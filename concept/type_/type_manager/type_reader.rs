/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::collections::{HashMap, HashSet};
use itertools::Itertools;

use bytes::Bytes;
use encoding::{
    error::EncodingError,
    graph::{
        definition::{definition_key::DefinitionKey, r#struct::StructDefinition, DefinitionValueEncoding},
        type_::{
            edge::{TypeEdge, TypeEdgeEncoding},
            index::{IdentifierIndex, LabelToTypeVertexIndex, NameToStructDefinitionIndex},
            property::{TypeEdgeProperty, TypeEdgePropertyEncoding, TypeVertexProperty, TypeVertexPropertyEncoding},
            vertex::{PrefixedTypeVertexEncoding, TypeVertex, TypeVertexEncoding},
        },
    },
    layout::infix::Infix,
    value::{label::Label, value_type::ValueType},
    Keyable,
};
use encoding::graph::type_::CapabilityKind;
use iterator::Collector;
use lending_iterator::LendingIterator;
use resource::constants::snapshot::{BUFFER_KEY_INLINE, BUFFER_VALUE_INLINE};
use storage::{key_range::KeyRange, snapshot::ReadableSnapshot};

use crate::{
    error::ConceptReadError,
    type_::{
        annotation::{
            Annotation, AnnotationAbstract, AnnotationCardinality, AnnotationCascade, AnnotationDistinct,
            AnnotationIndependent, AnnotationKey, AnnotationRange, AnnotationRegex, AnnotationUnique, AnnotationValues,
        },
        attribute_type::AttributeType,
        entity_type::EntityType,
        object_type::ObjectType,
        owns::Owns,
        relates::Relates,
        relation_type::RelationType,
        role_type::RoleType,
        sub::Sub,
        Capability, EdgeHidden, KindAPI, Ordering, TypeAPI,
    },
};
use crate::type_::constraint::{CapabilityConstraint, Constraint, ConstraintDescription, ConstraintValidationMode, get_cardinality_constraint_opt, get_distinct_constraints, TypeConstraint};
use crate::type_::plays::Plays;

pub struct TypeReader {}

impl TypeReader {
    pub(crate) fn get_labelled_type<T>(
        snapshot: &impl ReadableSnapshot,
        label: &Label<'_>,
    ) -> Result<Option<T>, ConceptReadError>
    where
        T: TypeAPI<'static>,
    {
        let key = LabelToTypeVertexIndex::build(label).into_storage_key();
        match snapshot.get::<BUFFER_KEY_INLINE>(key.as_reference()) {
            Err(error) => Err(ConceptReadError::SnapshotGet { source: error }),
            Ok(None) => Ok(None),
            Ok(Some(value)) => match T::from_bytes(Bytes::Array(value)) {
                Ok(type_) => Ok(Some(type_)),
                Err(err) => match err {
                    EncodingError::UnexpectedPrefix { .. } => Ok(None),
                    _ => Err(ConceptReadError::Encoding { source: err }),
                },
            },
        }
    }

    pub(crate) fn get_roles_by_name(
        snapshot: &impl ReadableSnapshot,
        name: String,
    ) -> Result<Vec<RoleType<'static>>, ConceptReadError> {
        let mut name_with_colon = name;
        name_with_colon.push(':');
        let key = LabelToTypeVertexIndex::build(&Label::build(name_with_colon.as_str())).into_storage_key();
        let vec = snapshot
            .iterate_range(KeyRange::new_within(key, IdentifierIndex::<TypeVertex<'static>>::FIXED_WIDTH_ENCODING))
            .collect_cloned_vec(|key, value| match RoleType::from_bytes(Bytes::copy(value.bytes())) {
                Err(_) => None,
                Ok(role_type) => Some(role_type),
            })
            .map_err(|source| ConceptReadError::SnapshotIterate { source })?;
        Ok(vec.into_iter().filter_map(|x| x).collect())
    }

    pub(crate) fn get_struct_definition_key(
        snapshot: &impl ReadableSnapshot,
        name: &str,
    ) -> Result<Option<DefinitionKey<'static>>, ConceptReadError> {
        let index_key = NameToStructDefinitionIndex::build(name);
        let bytes = snapshot
            .get(index_key.into_storage_key().as_reference())
            .map_err(|source| ConceptReadError::SnapshotGet { source })?;
        Ok(bytes.map(|value| DefinitionKey::new(Bytes::Array(value))))
    }

    pub(crate) fn get_struct_definition(
        snapshot: &impl ReadableSnapshot,
        definition_key: DefinitionKey<'_>,
    ) -> Result<StructDefinition, ConceptReadError> {
        let bytes = snapshot
            .get::<BUFFER_VALUE_INLINE>(definition_key.clone().into_storage_key().as_reference())
            .map_err(|source| ConceptReadError::SnapshotGet { source })?;
        Ok(StructDefinition::from_bytes(bytes.unwrap().as_ref()))
    }

    pub(crate) fn get_struct_definitions_all(
        snapshot: &impl ReadableSnapshot,
    ) -> Result<HashMap<DefinitionKey<'static>, StructDefinition>, ConceptReadError> {
        snapshot
            .iterate_range(KeyRange::new_within(
                DefinitionKey::build_prefix(StructDefinition::PREFIX),
                StructDefinition::PREFIX.fixed_width_keys(),
            ))
            .collect_cloned_hashmap(|key, value| {
                (DefinitionKey::new(Bytes::Array(key.byte_ref().into())), StructDefinition::from_bytes(value))
            })
            .map_err(|source| ConceptReadError::SnapshotIterate { source })
    }

    pub(crate) fn get_struct_definition_usages_in_attribute_types(
        snapshot: &impl ReadableSnapshot,
    ) -> Result<HashMap<DefinitionKey<'static>, HashSet<AttributeType<'static>>>, ConceptReadError> {
        let mut usages: HashMap<DefinitionKey<'static>, HashSet<AttributeType<'static>>> = HashMap::new();

        let attribute_types = TypeReader::get_attribute_types(snapshot)?;
        for attribute_type in attribute_types {
            if let Some(ValueType::Struct(definition_key)) =
                TypeReader::get_value_type_declared(snapshot, attribute_type.clone())?
            {
                if !usages.contains_key(&definition_key) {
                    usages.insert(definition_key.clone(), HashSet::new());
                }
                usages.get_mut(&definition_key).unwrap().insert(attribute_type);
            }
        }

        Ok(usages)
    }

    pub(crate) fn get_struct_definition_usages_in_struct_definitions(
        snapshot: &impl ReadableSnapshot,
    ) -> Result<HashMap<DefinitionKey<'static>, HashSet<DefinitionKey<'static>>>, ConceptReadError> {
        let mut usages: HashMap<DefinitionKey<'static>, HashSet<DefinitionKey<'static>>> = HashMap::new();

        let struct_definitions = TypeReader::get_struct_definitions_all(snapshot)?;
        for (owner_key, struct_definition) in struct_definitions {
            for value_type in struct_definition.fields.values().map(|field| field.value_type.clone()) {
                if let ValueType::Struct(definition_key) = value_type {
                    if !usages.contains_key(&definition_key) {
                        usages.insert(definition_key.clone(), HashSet::new());
                    }
                    usages.get_mut(&definition_key).unwrap().insert(owner_key.clone());
                }
            }
        }

        Ok(usages)
    }

    pub(crate) fn get_object_types(
        snapshot: &impl ReadableSnapshot,
    ) -> Result<Vec<ObjectType<'static>>, ConceptReadError> {
        let entity_types = Self::get_entity_types(snapshot)?;
        let relation_types = Self::get_relation_types(snapshot)?;
        Ok((entity_types.into_iter().map(ObjectType::Entity))
            .chain(relation_types.into_iter().map(ObjectType::Relation))
            .collect())
    }

    pub(crate) fn get_entity_types(
        snapshot: &impl ReadableSnapshot,
    ) -> Result<Vec<EntityType<'static>>, ConceptReadError> {
        snapshot
            .iterate_range(KeyRange::new_within(EntityType::prefix_for_kind(), EntityType::PREFIX.fixed_width_keys()))
            .collect_cloned_vec(|key, _| EntityType::new(TypeVertex::new(Bytes::copy(key.bytes()))))
            .map_err(|error| ConceptReadError::SnapshotIterate { source: error })
    }

    pub(crate) fn get_relation_types(
        snapshot: &impl ReadableSnapshot,
    ) -> Result<Vec<RelationType<'static>>, ConceptReadError> {
        snapshot
            .iterate_range(KeyRange::new_within(
                RelationType::prefix_for_kind(),
                RelationType::PREFIX.fixed_width_keys(),
            ))
            .collect_cloned_vec(|key, _| RelationType::new(TypeVertex::new(Bytes::copy(key.bytes()))))
            .map_err(|error| ConceptReadError::SnapshotIterate { source: error })
    }

    pub(crate) fn get_attribute_types(
        snapshot: &impl ReadableSnapshot,
    ) -> Result<Vec<AttributeType<'static>>, ConceptReadError> {
        snapshot
            .iterate_range(KeyRange::new_within(AttributeType::prefix_for_kind(), false))
            .collect_cloned_vec(|key, _| AttributeType::new(TypeVertex::new(Bytes::copy(key.bytes()))))
            .map_err(|error| ConceptReadError::SnapshotIterate { source: error })
    }

    pub(crate) fn get_role_types(snapshot: &impl ReadableSnapshot) -> Result<Vec<RoleType<'static>>, ConceptReadError> {
        snapshot
            .iterate_range(KeyRange::new_within(RoleType::prefix_for_kind(), RoleType::PREFIX.fixed_width_keys()))
            .collect_cloned_vec(|key, _| RoleType::new(TypeVertex::new(Bytes::copy(key.bytes()))))
            .map_err(|error| ConceptReadError::SnapshotIterate { source: error })
    }

    // TODO: Should get_{super/sub}type[s_transitive] return T or T::SelfStatic.
    // T::SelfStatic is the more consistent, more honest interface, but T is convenient.
    pub(crate) fn get_supertype<T>(snapshot: &impl ReadableSnapshot, subtype: T) -> Result<Option<T>, ConceptReadError>
    where
        T: TypeAPI<'static>,
    {
        Ok(snapshot
            .iterate_range(KeyRange::new_within(
                Sub::prefix_for_canonical_edges_from(subtype),
                TypeEdge::FIXED_WIDTH_ENCODING,
            ))
            .first_cloned()
            .map_err(|error| ConceptReadError::SnapshotIterate { source: error })?
            .map(|(key, _)| Sub::<T>::decode_canonical_edge(Bytes::Array(key.into_byte_array())).supertype()))
    }

    pub(crate) fn get_supertypes_transitive<T: TypeAPI<'static>>(
        snapshot: &impl ReadableSnapshot,
        subtype: T,
    ) -> Result<Vec<T>, ConceptReadError> {
        let mut supertypes: Vec<T> = Vec::new();
        let mut supertype_opt = TypeReader::get_supertype(snapshot, subtype.clone())?;
        while let Some(supertype) = supertype_opt {
            supertypes.push(supertype.clone());
            supertype_opt = TypeReader::get_supertype(snapshot, supertype.clone())?;
        }
        Ok(supertypes)
    }

    pub(crate) fn get_subtypes<T>(snapshot: &impl ReadableSnapshot, supertype: T) -> Result<HashSet<T>, ConceptReadError>
    where
        T: TypeAPI<'static>,
    {
        snapshot
            .iterate_range(KeyRange::new_within(
                Sub::prefix_for_reverse_edges_from(supertype),
                TypeEdge::FIXED_WIDTH_ENCODING,
            ))
            .collect_cloned_hashset(|key, _| {
                Sub::<T>::decode_reverse_edge(Bytes::Reference(key.byte_ref()).into_owned()).subtype()
            })
            .map_err(|error| ConceptReadError::SnapshotIterate { source: error })
    }

    pub fn get_subtypes_transitive<T>(snapshot: &impl ReadableSnapshot, type_: T) -> Result<Vec<T>, ConceptReadError>
    where
        T: TypeAPI<'static>,
    {
        let mut subtypes_transitive: Vec<T> = Vec::new();
        let mut types_to_check: Vec<T> = Vec::from([type_]);

        while let Some(type_) = types_to_check.pop() {
            let subtypes = Self::get_subtypes(snapshot, type_)?;
            types_to_check.extend(subtypes.iter());
            subtypes_transitive.extend(subtypes.into_iter());
        }

        Ok(subtypes_transitive)
    }

    pub(crate) fn get_label<'a>(
        snapshot: &impl ReadableSnapshot,
        type_: impl TypeAPI<'a>,
    ) -> Result<Option<Label<'static>>, ConceptReadError> {
        Self::get_type_property_declared::<Label<'static>>(snapshot, type_)
    }

    pub(crate) fn get_capabilities_declared<CAP: Capability<'static>>(
        snapshot: &impl ReadableSnapshot,
        owner: impl TypeVertexEncoding<'static>,
    ) -> Result<HashSet<CAP>, ConceptReadError> {
        let owns_prefix = CAP::prefix_for_canonical_edges_from(CAP::ObjectType::new(owner.into_vertex()));
        snapshot
            .iterate_range(KeyRange::new_within(owns_prefix, TypeEdge::FIXED_WIDTH_ENCODING))
            .collect_cloned_hashset(|key, _| CAP::decode_canonical_edge(Bytes::Reference(key.byte_ref()).into_owned()))
            .map_err(|error| ConceptReadError::SnapshotIterate { source: error })
    }

    pub(crate) fn get_capabilities<CAP: Capability<'static>>(
        snapshot: &impl ReadableSnapshot,
        object_type: CAP::ObjectType,
        allow_hidden: bool,
    ) -> Result<HashSet<CAP>, ConceptReadError> {
        let mut transitive_capabilities: HashSet<CAP> = HashSet::new();
        let mut hidden_interfaces: HashSet<CAP::InterfaceType> = HashSet::new();
        let mut current_type = Some(object_type);
        while current_type.is_some() {
            let declared_capabilities =
                Self::get_capabilities_declared::<CAP>(snapshot, current_type.as_ref().unwrap().clone())?;
            for capability in declared_capabilities.into_iter() {
                let interface = capability.interface();
                // TODO: Maybe need to check the whole capability, not interface. Revisit when hiding for plays and owns is implemented.
                if allow_hidden || !hidden_interfaces.contains(&interface) {
                    transitive_capabilities.insert(capability.clone());
                }
                if let Some(hidden) = Self::get_capability_hides(snapshot, capability.clone())? {
                    hidden_interfaces.add(hidden.interface());
                }
            }
            current_type = Self::get_supertype(snapshot, current_type.unwrap())?;
        }
        Ok(transitive_capabilities)
    }

    pub(crate) fn get_object_capabilities_hides_declared<CAP: Capability<'static>>(
        snapshot: &impl ReadableSnapshot,
        object_type: CAP::ObjectType,
    ) -> Result<HashMap<CAP, CAP>, ConceptReadError> {
        let mut capability_to_hidden: HashMap<CAP, CAP> = HashMap::new();
        let declared_capabilities = Self::get_capabilities_declared::<CAP>(snapshot, object_type)?;
        for capability in declared_capabilities.into_iter() {
            debug_assert!(!capability_to_hidden.contains_key(&capability));
            if let Some(hidden) = Self::get_capability_hides(snapshot, capability.clone())? {
                capability_to_hidden.insert(capability, hidden);
            }
        }
        Ok(capability_to_hidden)
    }

    pub(crate) fn get_object_capabilities_hides<CAP: Capability<'static>>(
        snapshot: &impl ReadableSnapshot,
        object_type: CAP::ObjectType,
    ) -> Result<HashMap<CAP, CAP>, ConceptReadError> {
        let mut capability_to_hidden: HashMap<CAP, CAP> = HashMap::new();
        let mut current_type = Some(object_type);
        while let Some(current_type_val) = &current_type {
            let current_type_capability_to_hidden =
                Self::get_object_capabilities_hides_declared(snapshot, current_type_val.clone())?;
            capability_to_hidden.extend(current_type_capability_to_hidden.into_iter());
            current_type = Self::get_supertype(snapshot, current_type_val.clone())?;
        }
        Ok(capability_to_hidden)
    }

    pub(crate) fn get_capability_hides<CAP: Capability<'static>>(
        snapshot: &impl ReadableSnapshot,
        capability: CAP,
    ) -> Result<Option<CAP>, ConceptReadError> {
        let hide_property_key = EdgeHidden::<CAP>::build_key(capability);
        snapshot
            .get_mapped(hide_property_key.into_storage_key().as_reference(), |hidden_edge_bytes| {
                EdgeHidden::<CAP>::from_value_bytes(hidden_edge_bytes).hidden
            })
            .map_err(|error| ConceptReadError::SnapshotGet { source: error })
    }

    pub(crate) fn get_capability_specializes<CAP: Capability<'static>>(
        snapshot: &impl ReadableSnapshot,
        capability: CAP,
    ) -> Result<Option<CAP>, ConceptReadError> {
        let (object_type, interface_type) = (capability.object(), capability.interface());
        let capabilities = Self::get_capabilities::<CAP>(snapshot, object_type.clone(), true)?;
        let mut current_interface_type_opt = Some(interface_type.clone());

        while let Some(current_interface_type) = current_interface_type_opt {
            let specialized = capabilities.iter().filter(|potential_specialized| {
                potential_specialized != capability
                    && &potential_specialized.interface() == &current_interface_type
            }).sorted_by(|lhs, rhs| lhs.interface().is_subtype_transitive_of(rhs.interface())).next();
            if specialized.is_some() {
                return Ok(specialized);
            }
            current_interface_type_opt = Self::get_supertype(snapshot, current_interface_type)?;
        }

        Ok(None)
    }

    pub(crate) fn get_capability_specializes_transitive<CAP: Capability<'static>>(
        snapshot: &impl ReadableSnapshot,
        capability: CAP,
    ) -> Result<Vec<CAP>, ConceptReadError> {
        let mut capability_specializes: Vec<CAP> = Vec::new();

        let mut specializes_opt = TypeReader::get_capability_specializes(snapshot, capability)?;
        while let Some(specializes) = specializes_opt {
            capability_specializes.push(specializes.clone());
            specializes_opt = TypeReader::get_supertype(snapshot, specializes)?;
        }

        Ok(capability_specializes)
    }

    pub(crate) fn get_specializing_capabilities<CAP: Capability<'static>>(
        snapshot: &impl ReadableSnapshot,
        capability: CAP,
    ) -> Result<HashSet<CAP>, ConceptReadError> {
        let mut specializing_capabilities: HashSet<CAP> = HashSet::new();
        let mut object_types_to_check: Vec<CAP::ObjectType> = Vec::from([capability.object()]);

        while let Some(current_object_type) = object_types_to_check.pop() {
            let object_type_capabilities = Self::get_capabilities_declared::<CAP>(snapshot, current_object_type.clone())?;
            let is_hidden = object_type_capabilities.get(&capability).is_none();
            for potential_specializing in object_type_capabilities.into_iter() {
                let specializes = Self::get_capability_specializes(snapshot, potential_specializing.clone())?;
                if specializes == capability {
                    specializing_capabilities.insert(potential_specializing);
                }
            }

            if !is_hidden {
                Self::get_subtypes(snapshot, current_object_type)?
                    .into_iter()
                    .for_each(|object_type| object_types_to_check.push(object_type));
            }
        }

        Ok(specializing_capabilities)
    }

    pub(crate) fn get_specializing_capabilities_transitive<CAP: Capability<'static>>(
        snapshot: &impl ReadableSnapshot,
        capability: CAP,
    ) -> Result<Vec<CAP>, ConceptReadError> {
        let mut specializing_capabilities: Vec<CAP> = Vec::new();
        let mut capabilities_to_check: Vec<CAP> = Vec::from([capability]);

        while let Some(capability) = capabilities_to_check.pop() {
            let specializings = Self::get_specializing_capabilities(snapshot, capability)?;
            capabilities_to_check.extend(specializings.iter());
            specializing_capabilities.extend(specializings.into_iter());
        }

        Ok(specializing_capabilities)
    }

    pub(crate) fn get_capabilities_for_interface<CAP>(
        snapshot: &impl ReadableSnapshot,
        interface_type: CAP::InterfaceType,
    ) -> Result<HashSet<CAP>, ConceptReadError>
    where
        CAP: Capability<'static>,
    {
        let owns_prefix = CAP::prefix_for_reverse_edges_from(interface_type);
        snapshot
            .iterate_range(KeyRange::new_within(owns_prefix, TypeEdge::FIXED_WIDTH_ENCODING))
            .collect_cloned_hashset(|key, _| CAP::decode_reverse_edge(Bytes::Array(key.byte_ref().into())))
            .map_err(|error| ConceptReadError::SnapshotIterate { source: error })
    }

    pub(crate) fn get_objects_with_capabilities_for_interface<CAP: Capability<'static>>(
        snapshot: &impl ReadableSnapshot,
        interface_type: CAP::InterfaceType,
    ) -> Result<HashMap<CAP::ObjectType, CAP>, ConceptReadError> {
        let mut capabilities: HashMap<CAP::ObjectType, CAP> = HashMap::new();
        let capabilities_declared: HashSet<CAP> =
            Self::get_capabilities_for_interface(snapshot, interface_type.clone())?;

        for declared_capability in capabilities_declared {
            let mut stack = Vec::new();
            stack.push(declared_capability.object());
            while let Some(sub_object) = stack.pop() {
                let mut is_declared_capability_hidden = false;
                for sub_object_cap in Self::get_capabilities_declared::<CAP>(snapshot, sub_object.clone())? {
                    if let Some(hidden_cap) = Self::get_capability_hides(snapshot, sub_object_cap.clone())? {
                        is_declared_capability_hidden =
                            is_declared_capability_hidden || hidden_cap.interface() == interface_type;
                    }
                }
                if !is_declared_capability_hidden {
                    debug_assert!(!capabilities.contains_key(&sub_object));
                    capabilities.insert(sub_object.clone(), declared_capability.clone());
                    Self::get_subtypes(snapshot, sub_object)?
                        .into_iter()
                        .for_each(|object_type| stack.push(object_type));
                }
            }
        }
        Ok(capabilities)
    }

    pub(crate) fn get_role_type_relates_declared(
        snapshot: &impl ReadableSnapshot,
        role_type: RoleType<'static>,
    ) -> Result<Relates<'static>, ConceptReadError> {
        let relates = Self::get_capabilities_for_interface::<Relates<'static>>(snapshot, role_type)?;
        debug_assert!(relates.len() == 1);
        relates.into_iter().next().ok_or(ConceptReadError::CorruptMissingMandatoryRelatesForRole)
    }

    pub(crate) fn get_value_type_declared(
        snapshot: &impl ReadableSnapshot,
        type_: AttributeType<'_>,
    ) -> Result<Option<ValueType>, ConceptReadError> {
        Self::get_type_property_declared::<ValueType>(snapshot, type_)
    }

    pub(crate) fn get_value_type(
        snapshot: &impl ReadableSnapshot,
        type_: AttributeType<'static>,
    ) -> Result<Option<(ValueType, AttributeType<'static>)>, ConceptReadError> {
        Self::get_type_property::<ValueType, AttributeType<'static>>(snapshot, type_)
    }

    pub(crate) fn get_value_type_without_source(
        snapshot: &impl ReadableSnapshot,
        type_: AttributeType<'static>,
    ) -> Result<Option<ValueType>, ConceptReadError> {
        Self::get_value_type(snapshot, type_).map(|result| result.map(|(value_type, _)| value_type))
    }

    pub(crate) fn get_type_property_declared<'a, PROPERTY>(
        snapshot: &impl ReadableSnapshot,
        type_: impl TypeVertexEncoding<'a>,
    ) -> Result<Option<PROPERTY>, ConceptReadError>
    where
        PROPERTY: TypeVertexPropertyEncoding<'static>,
    {
        let property = snapshot
            .get_mapped(PROPERTY::build_key(type_).into_storage_key().as_reference(), |value| {
                PROPERTY::from_value_bytes(value)
            })
            .map_err(|err| ConceptReadError::SnapshotGet { source: err })?;
        Ok(property)
    }

    pub(crate) fn get_type_property<PROPERTY, SOURCE>(
        snapshot: &impl ReadableSnapshot,
        type_: SOURCE,
    ) -> Result<Option<(PROPERTY, SOURCE)>, ConceptReadError>
    where
        PROPERTY: TypeVertexPropertyEncoding<'static>,
        SOURCE: TypeAPI<'static> + Clone,
    {
        let mut type_opt = Some(type_);
        while let Some(curr_type) = type_opt {
            if let Some(property) = Self::get_type_property_declared::<PROPERTY>(snapshot, curr_type.clone())? {
                return Ok(Some((property, curr_type.clone())));
            }
            type_opt = Self::get_supertype(snapshot, curr_type)?;
        }
        Ok(None)
    }

    pub(crate) fn get_type_edge_property<'a, PROPERTY>(
        snapshot: &impl ReadableSnapshot,
        edge: impl TypeEdgeEncoding<'a>,
    ) -> Result<Option<PROPERTY>, ConceptReadError>
        where
            PROPERTY: TypeEdgePropertyEncoding<'static>,
    {
        let property = snapshot
            .get_mapped(PROPERTY::build_key(edge).into_storage_key().as_reference(), |value| {
                PROPERTY::from_value_bytes(value)
            })
            .map_err(|err| ConceptReadError::SnapshotGet { source: err })?;
        Ok(property)
    }

    pub(crate) fn get_type_ordering(
        snapshot: &impl ReadableSnapshot,
        role_type: RoleType<'_>,
    ) -> Result<Ordering, ConceptReadError> {
        match Self::get_type_property_declared(snapshot, role_type)? {
            Some(ordering) => Ok(ordering),
            None => Err(ConceptReadError::CorruptMissingMandatoryOrdering),
        }
    }

    pub(crate) fn get_capability_ordering(
        snapshot: &impl ReadableSnapshot,
        owns: Owns<'_>,
    ) -> Result<Ordering, ConceptReadError> {
        match Self::get_type_edge_property::<Ordering>(snapshot, owns)? {
            Some(ordering) => Ok(ordering),
            None => Err(ConceptReadError::CorruptMissingMandatoryOrdering),
        }
    }

    pub(crate) fn get_type_annotations_declared<T: KindAPI<'static>>(
        snapshot: &impl ReadableSnapshot,
        type_: T,
    ) -> Result<HashSet<T::AnnotationType>, ConceptReadError> {
        snapshot
            .iterate_range(KeyRange::new_inclusive(
                TypeVertexProperty::build(type_.vertex(), Infix::ANNOTATION_MIN).into_storage_key(),
                TypeVertexProperty::build(type_.vertex(), Infix::ANNOTATION_MAX).into_storage_key(),
            ))
            .collect_cloned_hashset(|key, value| {
                let annotation_key = TypeVertexProperty::new(Bytes::Reference(key.byte_ref()));
                let annotation = match annotation_key.infix() {
                    Infix::PropertyAnnotationAbstract => Annotation::Abstract(AnnotationAbstract),
                    Infix::PropertyAnnotationDistinct => Annotation::Distinct(AnnotationDistinct),
                    Infix::PropertyAnnotationIndependent => Annotation::Independent(AnnotationIndependent),
                    Infix::PropertyAnnotationCardinality => Annotation::Cardinality(
                        <AnnotationCardinality as TypeVertexPropertyEncoding>::from_value_bytes(value),
                    ),
                    Infix::PropertyAnnotationRegex => {
                        Annotation::Regex(<AnnotationRegex as TypeVertexPropertyEncoding>::from_value_bytes(value))
                    }
                    Infix::PropertyAnnotationCascade => Annotation::Cascade(AnnotationCascade),
                    Infix::PropertyAnnotationRange => {
                        Annotation::Range(<AnnotationRange as TypeVertexPropertyEncoding>::from_value_bytes(value))
                    }
                    Infix::PropertyAnnotationValues => {
                        Annotation::Values(<AnnotationValues as TypeVertexPropertyEncoding>::from_value_bytes(value))
                    }
                    | Infix::_PropertyAnnotationLast
                    | Infix::PropertyAnnotationUnique
                    | Infix::PropertyAnnotationKey
                    | Infix::PropertyLabel
                    | Infix::PropertyValueType
                    | Infix::PropertyOrdering
                    | Infix::PropertyHide
                    | Infix::PropertyHasOrder
                    | Infix::PropertyLinksOrder => {
                        unreachable!("Retrieved unexpected infixes while reading annotations.")
                    }
                };
                T::AnnotationType::try_from(annotation).unwrap()
            })
            .map_err(|err| ConceptReadError::SnapshotIterate { source: err.clone() })
    }

    pub(crate) fn get_type_constraints<T: KindAPI<'static>>(
        snapshot: &impl ReadableSnapshot,
        type_: T,
    ) -> Result<HashMap<TypeConstraint<T>, HashSet<T>>, ConceptReadError> {
        let mut constraints: HashMap<TypeConstraint<T>, HashSet<T>> = HashMap::new();
        let mut type_opt = Some(type_);
        while let Some(curr_type) = type_opt {
            let declared_annotations = Self::get_type_annotations_declared(snapshot, curr_type.clone())?;
            for annotation in declared_annotations {
                for constraint in annotation.clone().into().into_type_constraints::<T>() {
                    let sources_of_duplicate_opt = constraints.get_mut(&constraint);
                    if let Some(sources_of_duplicate) = sources_of_duplicate_opt {
                        match constraint.description().validation_mode() {
                            ConstraintValidationMode::SingleInstanceOfTypeOrSubtype
                            | ConstraintValidationMode::AllInstancesOfTypeOrSubtypes => {
                                debug_assert!(sources_of_duplicate.len() == 1);
                                sources_of_duplicate.clear();
                            },

                            ConstraintValidationMode::SingleInstanceOfType
                            | ConstraintValidationMode::AllInstancesOfSiblingTypeOrSubtypes => {}
                        }
                    }
                    let constraint_sources = constraints.entry(constraint).or_insert(HashSet::new());
                    constraint_sources.insert(curr_type.clone());
                }
            }
            type_opt = Self::get_supertype(snapshot, curr_type.clone())?;
        }

        debug_assert!(constraints.iter().find(|(_, sources)| sources.is_empty()).is_none());
        Ok(constraints)
    }

    pub(crate) fn get_capability_annotations_declared<CAP: Capability<'static>>(
        snapshot: &impl ReadableSnapshot,
        capability: CAP,
    ) -> Result<HashSet<CAP::AnnotationType>, ConceptReadError> {
        let type_edge = capability.to_canonical_type_edge();
        snapshot
            .iterate_range(KeyRange::new_inclusive(
                TypeEdgeProperty::build(type_edge.clone(), Infix::ANNOTATION_MIN).into_storage_key(),
                TypeEdgeProperty::build(type_edge, Infix::ANNOTATION_MAX).into_storage_key(),
            ))
            .collect_cloned_hashset(|key, value| {
                let annotation_key = TypeEdgeProperty::new(Bytes::Reference(key.byte_ref()));
                let annotation = match annotation_key.infix() {
                    Infix::PropertyAnnotationDistinct => Annotation::Distinct(AnnotationDistinct),
                    Infix::PropertyAnnotationIndependent => Annotation::Independent(AnnotationIndependent),
                    Infix::PropertyAnnotationUnique => Annotation::Unique(AnnotationUnique),
                    Infix::PropertyAnnotationKey => Annotation::Key(AnnotationKey),
                    Infix::PropertyAnnotationCardinality => Annotation::Cardinality(
                        <AnnotationCardinality as TypeEdgePropertyEncoding>::from_value_bytes(value),
                    ),
                    Infix::PropertyAnnotationRegex => {
                        Annotation::Regex(<AnnotationRegex as TypeEdgePropertyEncoding>::from_value_bytes(value))
                    }
                    Infix::PropertyAnnotationRange => {
                        Annotation::Range(<AnnotationRange as TypeEdgePropertyEncoding>::from_value_bytes(value))
                    }
                    Infix::PropertyAnnotationValues => {
                        Annotation::Values(<AnnotationValues as TypeEdgePropertyEncoding>::from_value_bytes(value))
                    }
                    | Infix::_PropertyAnnotationLast
                    | Infix::PropertyAnnotationAbstract
                    | Infix::PropertyAnnotationCascade
                    | Infix::PropertyLabel
                    | Infix::PropertyValueType
                    | Infix::PropertyOrdering
                    | Infix::PropertyHide
                    | Infix::PropertyHasOrder
                    | Infix::PropertyLinksOrder => {
                        unreachable!("Retrieved unexpected infixes while reading annotations.")
                    }
                };
                CAP::AnnotationType::try_from(annotation).unwrap()
            })
            .map_err(|err| ConceptReadError::SnapshotIterate { source: err.clone() })
    }

    pub(crate) fn get_capability_constraints<CAP: Capability<'static>>(
        snapshot: &impl ReadableSnapshot,
        capability: CAP,
    ) -> Result<HashMap<CapabilityConstraint<CAP>, HashSet<CAP>>, ConceptReadError> {
        let mut constraints: HashMap<CapabilityConstraint<CAP>, HashSet<CAP>> = HashMap::new();
        let mut capability_opt = Some(capability);
        while let Some(curr_capability) = capability_opt {
            let declared_annotations = Self::get_capability_annotations_declared(snapshot, curr_capability.clone())?;

            for annotation in declared_annotations {
                for constraint in annotation.clone().into().into_capability_constraints::<CAP>() {
                    let sources_of_duplicate_opt = constraints.get_mut(&constraint);
                    if let Some(sources_of_duplicate) = sources_of_duplicate_opt {
                        match constraint.description().validation_mode() {
                            ConstraintValidationMode::SingleInstanceOfTypeOrSubtype
                            | ConstraintValidationMode::AllInstancesOfTypeOrSubtypes => {
                                debug_assert!(sources_of_duplicate.len() == 1);
                                sources_of_duplicate.clear();
                            },

                            ConstraintValidationMode::SingleInstanceOfType
                            | ConstraintValidationMode::AllInstancesOfSiblingTypeOrSubtypes => {}
                        }
                    }
                    let constraint_sources = constraints.entry(constraint).or_insert(HashSet::new());
                    constraint_sources.insert(curr_capability.clone());
                }
            }

            Self::add_capability_default_constraints_if_not_declared(snapshot, curr_capability.clone(), &mut constraints)?;
            capability_opt = Self::get_capability_specializes(snapshot, curr_capability.clone())?;
        }

        debug_assert!(constraints.iter().find(|(_, sources)| sources.is_empty()).is_none());
        Ok(constraints)
    }

    fn add_capability_default_constraints_if_not_declared<CAP: Capability<'static>>(
        snapshot: &impl ReadableSnapshot,
        capability: CAP,
        out_constraints: &mut HashMap<CapabilityConstraint<CAP>, HashSet<CAP>>,
    ) -> Result<(), ConceptReadError> {
        match CAP::KIND {
            CapabilityKind::Relates => {
                let relates = Relates::new(RelationType::new(capability.canonical_from().into_vertex()), RoleType::new(capability.canonical_to().into_vertex()));
                let role_ordering = Self::get_type_ordering(snapshot, relates.role())?;

                if get_cardinality_constraint_opt(capability.clone(), out_constraints)?.is_none() {
                    let cardinality_sources = out_constraints
                        .entry(CapabilityConstraint::new(ConstraintDescription::Cardinality(
                            Relates::get_default_cardinality(role_ordering)
                        )))
                        .or_insert(HashSet::new());
                    cardinality_sources.insert(capability.clone());
                }

                if let Some(default_distinct) = Relates::get_default_distinct(role_ordering)? {
                    if get_distinct_constraints(out_constraints)?.is_empty() {
                        let distinct_sources = out_constraints
                            .entry(CapabilityConstraint::new(ConstraintDescription::Distinct(
                                default_distinct
                            )))
                            .or_insert(HashSet::new());
                        distinct_sources.insert(capability.clone());
                    }
                }
            }
            CapabilityKind::Plays => {
                let plays = Plays::new(ObjectType::new(capability.canonical_from().into_vertex()), RoleType::new(capability.canonical_to().into_vertex()));
                if get_cardinality_constraint_opt(capability.clone(), out_constraints)?.is_none() {
                    let cardinality_sources = out_constraints
                        .entry(CapabilityConstraint::new(ConstraintDescription::Cardinality(
                            Plays::get_default_cardinality()
                        )))
                        .or_insert(HashSet::new());
                    cardinality_sources.insert(capability.clone());
                }
            }
            CapabilityKind::Owns => {
                let owns = Owns::new(ObjectType::new(capability.canonical_from().into_vertex()), AttributeType::new(capability.canonical_to().into_vertex()));
                let ordering = Self::get_capability_ordering(snapshot, owns.clone())?;

                if get_cardinality_constraint_opt(capability.clone(), out_constraints)?.is_none() {
                    let cardinality_sources = out_constraints
                        .entry(CapabilityConstraint::new(ConstraintDescription::Cardinality(
                            Owns::get_default_cardinality(ordering)
                        )))
                        .or_insert(HashSet::new());
                    cardinality_sources.insert(capability.clone());
                }

                if let Some(default_distinct) = Owns::get_default_distinct(ordering)? {
                    if get_distinct_constraints(out_constraints)?.is_empty() {
                        let distinct_sources = out_constraints
                            .entry(CapabilityConstraint::new(ConstraintDescription::Distinct(
                                default_distinct
                            )))
                            .or_insert(HashSet::new());
                        distinct_sources.insert(capability.clone());
                    }
                }
            }
        }
        Ok(())
    }
}
