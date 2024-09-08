/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::collections::{HashMap, HashSet};

use encoding::graph::{definition::r#struct::StructDefinition, type_::CapabilityKind};
use itertools::Itertools;
use storage::snapshot::ReadableSnapshot;

use crate::{
    error::ConceptReadError,
    type_::{
        attribute_type::AttributeType,
        entity_type::EntityType,
        owns::Owns,
        plays::Plays,
        relates::Relates,
        relation_type::RelationType,
        role_type::RoleType,
        type_manager::{
            type_reader::TypeReader,
            validation::{
                validation::{
                    get_label_or_concept_read_err,
                    is_overridden_interface_object_declared_supertype_or_self, is_type_transitive_supertype_or_same,
                    validate_role_name_uniqueness_non_transitive,
                    validate_role_type_supertype_ordering_match,
                    validate_type_declared_constraints_narrowing_of_supertype_constraints,
                },
                SchemaValidationError,
            },
            TypeManager,
        },
        Capability, KindAPI, ObjectTypeAPI, TypeAPI,
    },
};
use crate::type_::object_type::ObjectType;
use crate::type_::{Ordering, OwnerAPI};
use crate::type_::type_manager::validation::validation::{validate_sibling_owns_ordering_match_for_type, validate_type_supertype_abstractness};

pub struct CommitTimeValidation {}

macro_rules! validate_types {
    ($func_name:ident, $get_all_of_kind:ident, $type_:ident, $func:path) => {
        fn $func_name(
            snapshot: &impl ReadableSnapshot,
            type_manager: &TypeManager,
            validation_errors: &mut Vec<SchemaValidationError>,
        ) -> Result<(), ConceptReadError> {
            let roots = TypeReader::$get_all_of_kind(snapshot)?.into_iter().filter_map(|type_| {
                match type_.get_supertype(snapshot, type_manager) {
                    Ok(Some(_)) => None,
                    Ok(None) => Some(Ok(type_)),
                    Err(err) => Some(Err(err)),
                }
            });
            for root in roots {
                let root = root?;
                $func(snapshot, type_manager, root.clone(), validation_errors)?;
                for subtype in TypeReader::get_subtypes_transitive(snapshot, root)? {
                    $func(snapshot, type_manager, subtype, validation_errors)?;
                }
            }
            Ok(())
        }
    };
}

macro_rules! produced_errors {
    ($errors:ident, $expr:expr) => {{
        let len_before = $errors.len();
        $expr;
        $errors.len() > len_before
    }};
}

// Some of the checks from this file can duplicate already existing operation time validations
// and never fire up, but they are left here for better safety as the algorithms to check
// the updated schema with the finalised snapshot is much-much-much simpler and more robust
// than the operation time ones.
// It is still a goal to try call as much as possible validations on operation time.
impl CommitTimeValidation {
    pub(crate) fn validate(
        snapshot: &impl ReadableSnapshot,
        type_manager: &TypeManager,
    ) -> Result<Vec<SchemaValidationError>, ConceptReadError> {
        let mut errors = Vec::new();
        Self::validate_entity_types(snapshot, type_manager, &mut errors)?;
        Self::validate_relation_types(snapshot, type_manager, &mut errors)?;
        Self::validate_attribute_types(snapshot, type_manager, &mut errors)?;
        Self::validate_struct_definitions(snapshot, type_manager, &mut errors)?;
        Ok(errors)
    }

    validate_types!(validate_entity_types, get_entity_types, EntityType, Self::validate_entity_type);
    validate_types!(validate_relation_types, get_relation_types, RelationType, Self::validate_relation_type);
    validate_types!(validate_attribute_types, get_attribute_types, AttributeType, Self::validate_attribute_type);

    // TODO: redundancy check that there are no constraints on capabilities that are equal to type constraints (description() == description())

    fn validate_entity_type(
        snapshot: &impl ReadableSnapshot,
        type_manager: &TypeManager,
        type_: EntityType<'static>,
        validation_errors: &mut Vec<SchemaValidationError>,
    ) -> Result<(), ConceptReadError> {
        Self::validate_type_constraints(snapshot, type_manager, type_.clone(), validation_errors)?;
        Self::validate_object_type(snapshot, type_manager, type_.into_owned_object_type(), validation_errors)?;

        Ok(())
    }

    fn validate_relation_type(
        snapshot: &impl ReadableSnapshot,
        type_manager: &TypeManager,
        type_: RelationType<'static>,
        validation_errors: &mut Vec<SchemaValidationError>,
    ) -> Result<(), ConceptReadError> {
        Self::validate_type_constraints(snapshot, type_manager, type_.clone(), validation_errors)?;
        Self::validate_object_type(snapshot, type_manager, type_.into_owned_object_type(), validation_errors)?;

        Self::validate_relation_type_has_relates(snapshot, type_manager, type_.clone(), validation_errors)?;
        Self::validate_relation_type_role_types(snapshot, type_manager, type_.clone(), validation_errors)?;

        let invalid_relates = produced_errors!(
            validation_errors,
            Self::validate_relates(snapshot, type_manager, type_.clone(), validation_errors)?
        );
        if !invalid_relates {
            // TODO: Capabilities constraints narrowing checks are currently disabled
            // validate_capabilities_cardinalities_narrowing::<Relates<'static>>(
            //     snapshot,
            //     type_manager,
            //     type_.clone(),
            //     &HashMap::new(), // read everything from storage
            //     &HashMap::new(), // read everything from storage
            //     &HashMap::new(), // read everything from storage
            //     validation_errors,
            // )?;
        }

        Ok(())
    }

    fn validate_attribute_type(
        snapshot: &impl ReadableSnapshot,
        type_manager: &TypeManager,
        type_: AttributeType<'static>,
        validation_errors: &mut Vec<SchemaValidationError>,
    ) -> Result<(), ConceptReadError> {
        let invalid_value_type = produced_errors!(
            validation_errors,
            Self::validate_attribute_type_value_type(snapshot, type_manager, type_.clone(), validation_errors)?
        );

        if !invalid_value_type {
            Self::validate_type_constraints(snapshot, type_manager, type_.clone(), validation_errors)?;
        }

        Ok(())
    }

    fn validate_struct_definitions(
        snapshot: &impl ReadableSnapshot,
        type_manager: &TypeManager,
        validation_errors: &mut Vec<SchemaValidationError>,
    ) -> Result<(), ConceptReadError> {
        let definitions = TypeReader::get_struct_definitions_all(snapshot)?;

        for (_key, struct_definition) in definitions {
            Self::validate_struct_definition_fields(snapshot, type_manager, struct_definition, validation_errors)?;
        }

        Ok(())
    }

    fn validate_relation_type_role_types(
        snapshot: &impl ReadableSnapshot,
        type_manager: &TypeManager,
        relation_type: RelationType<'static>,
        validation_errors: &mut Vec<SchemaValidationError>,
    ) -> Result<(), ConceptReadError> {
        let relates_declared =
            TypeReader::get_capabilities_declared::<Relates<'static>>(snapshot, relation_type.clone())?;

        for relates in relates_declared {
            let role = relates.role();

            Self::validate_role_is_unique_for_relation_type_hierarchy(
                snapshot,
                type_manager,
                relation_type.clone(),
                role.clone(),
                validation_errors,
            )?;
            Self::validate_type_ordering(snapshot, type_manager, role.clone(), validation_errors)?;
            Self::validate_type_constraints(snapshot, type_manager, role.clone(), validation_errors)?;
        }

        Ok(())
    }

    fn validate_object_type(
        snapshot: &impl ReadableSnapshot,
        type_manager: &TypeManager,
        type_: ObjectType<'static>,
        validation_errors: &mut Vec<SchemaValidationError>,
    ) -> Result<(), ConceptReadError> {
        let invalid_owns = produced_errors!(
            validation_errors,
            Self::validate_owns(snapshot, type_manager, type_.clone(), validation_errors)?
        );
        if !invalid_owns {
            // TODO: Capabilities constraints narrowing checks are currently disabled
            // validate_capabilities_cardinalities_narrowing::<Owns<'static>>(
            //     snapshot,
            //     type_manager,
            //     type_.clone().into_owned_object_type(),
            //     &HashMap::new(), // read everything from storage
            //     &HashMap::new(), // read everything from storage
            //     &HashMap::new(), // read everything from storage
            //     validation_errors,
            // )?;
        }

        let invalid_plays = produced_errors!(
            validation_errors,
            Self::validate_plays(snapshot, type_manager, type_.clone(), validation_errors)?
        );
        if !invalid_plays {
            // TODO: Capabilities constraints narrowing checks are currently disabled
            // validate_capabilities_cardinalities_narrowing::<Plays<'static>>(
            //     snapshot,
            //     type_manager,
            //     type_.clone().into_owned_object_type(),
            //     &HashMap::new(), // read everything from storage
            //     &HashMap::new(), // read everything from storage
            //     &HashMap::new(), // read everything from storage
            //     validation_errors,
            // )?;
        }

        Ok(())
    }

    fn validate_owns(
        snapshot: &impl ReadableSnapshot,
        type_manager: &TypeManager,
        type_: ObjectType<'static>,
        validation_errors: &mut Vec<SchemaValidationError>,
    ) -> Result<(), ConceptReadError> {
        let owns_declared: HashSet<Owns<'static>> = TypeReader::get_capabilities_declared(snapshot, type_.clone())?;

        for owns in owns_declared {
            Self::validate_hidden_owns(snapshot, type_manager, owns.clone(), validation_errors)?;

            Self::validate_redundant_capabilities::<Owns<'static>>(
                snapshot,
                type_manager,
                owns.clone(),
                validation_errors,
            )?;

            Self::validate_capabilities_annotations::<Owns<'static>>(
                snapshot,
                type_manager,
                owns.clone(),
                validation_errors,
            )?;
        }

        Self::validate_capabilities_ordering(snapshot, type_manager, type_.clone(), validation_errors)?;

        Ok(())
    }

    fn validate_plays(
        snapshot: &impl ReadableSnapshot,
        type_manager: &TypeManager,
        type_: ObjectType<'static>,
        validation_errors: &mut Vec<SchemaValidationError>,
    ) -> Result<(), ConceptReadError>
    {
        let plays_declared: HashSet<Plays<'static>> = TypeReader::get_capabilities_declared(snapshot, type_.clone())?;

        for plays in plays_declared {
            let invalid_overrides = produced_errors!(
                validation_errors,
                Self::validate_hidden_plays(snapshot, type_manager, plays.clone(), validation_errors)?
            );

            if !invalid_overrides {
                Self::validate_redundant_capabilities::<Plays<'static>>(
                    snapshot,
                    type_manager,
                    plays.clone(),
                    validation_errors,
                )?;
                Self::validate_capabilities_annotations::<Plays<'static>>(
                    snapshot,
                    type_manager,
                    plays.clone(),
                    validation_errors,
                )?;
            }
        }

        Ok(())
    }

    fn validate_relates(
        snapshot: &impl ReadableSnapshot,
        type_manager: &TypeManager,
        relation_type: RelationType<'static>,
        validation_errors: &mut Vec<SchemaValidationError>,
    ) -> Result<(), ConceptReadError> {
        let relates_declared: HashSet<Relates<'static>> =
            TypeReader::get_capabilities_declared(snapshot, relation_type.clone())?;

        for relates in relates_declared {
            let invalid_overrides = produced_errors!(
                validation_errors,
                Self::validate_specialized_relates(snapshot, type_manager, relates.clone(), validation_errors)?
            );

            if !invalid_overrides {
                Self::validate_capabilities_annotations::<Relates<'static>>(
                    snapshot,
                    type_manager,
                    relates,
                    validation_errors,
                )?;
            }
        }

        Ok(())
    }

    // TODO: Change this method to check it correctly!
    fn validate_specialized_relates(
        snapshot: &impl ReadableSnapshot,
        type_manager: &TypeManager,
        relates: Relates<'static>,
        validation_errors: &mut Vec<SchemaValidationError>,
    ) -> Result<(), ConceptReadError> {
        let relation_type = relates.relation();
        let supertype = TypeReader::get_supertype(snapshot, relation_type.clone())?;

        if let Some(relates_override) = TypeReader::get_type_capability_specialises(snapshot, relates.clone())? {
            let role_type_overridden = relates_override.role();

            match &supertype {
                None => validation_errors.push(SchemaValidationError::HiddenRelatesIsNotInheritedByRelationType(
                    get_label_or_concept_read_err(snapshot, type_manager, relation_type.clone())?,
                    get_label_or_concept_read_err(snapshot, type_manager, role_type_overridden.clone())?,
                )),
                Some(supertype) => {
                    let contains = TypeReader::get_capabilities::<Relates<'static>>(snapshot, supertype.clone(), false)?
                        .into_iter()
                        .any(|relates| &relates.interface() == &role_type_overridden);

                    if !contains {
                        validation_errors.push(SchemaValidationError::HiddenRelatesIsNotInheritedByRelationType(
                            get_label_or_concept_read_err(snapshot, type_manager, relation_type.clone())?,
                            get_label_or_concept_read_err(snapshot, type_manager, role_type_overridden.clone())?,
                        ));
                    }
                }
            }

            let role_type = relates.role();
            // Only declared supertype (not transitive) fits as relates override == role subtype!
            // It is only a commit-time check as we verify that operation-time generation has been correct

            /*

            if needed:
                pub(crate) fn is_overridden_interface_object_declared_supertype_or_self<T: KindAPI<'static>>(
                    snapshot: &impl ReadableSnapshot,
                    type_manager: &TypeManager,
                    type_: T,
                    overridden: T,
                ) -> Result<bool, ConceptReadError> {
                    if type_ == overridden {
                        return Ok(true);
                    }

                    Ok(TypeReader::get_supertype(snapshot, type_.clone())? == Some(overridden.clone()))
                }

             */
            if !is_overridden_interface_object_declared_supertype_or_self(
                snapshot,
                role_type.clone(),
                role_type_overridden.clone(),
            )? {
                validation_errors.push(SchemaValidationError::HiddenCapabilityInterfaceIsNotSupertype(
                    CapabilityKind::Relates,
                    get_label_or_concept_read_err(snapshot, type_manager, relation_type.clone())?,
                    get_label_or_concept_read_err(snapshot, type_manager, role_type.clone())?,
                    get_label_or_concept_read_err(snapshot, type_manager, role_type_overridden.clone())?,
                ));
            }
        }

        Ok(())
    }

    fn validate_hidden_owns(
        snapshot: &impl ReadableSnapshot,
        type_manager: &TypeManager,
        owns: Owns<'static>,
        validation_errors: &mut Vec<SchemaValidationError>,
    ) -> Result<(), ConceptReadError> {
        let type_ = owns.owner();
        let supertype = TypeReader::get_supertype(snapshot, type_.clone())?;

        if let Some(owns_override) = TypeReader::get_type_capability_specialises(snapshot, owns.clone())? {
            let attribute_type_overridden = owns_override.attribute();

            match &supertype {
                None => validation_errors.push(SchemaValidationError::HiddenOwnsIsNotInheritedByObjectType(
                    get_label_or_concept_read_err(snapshot, type_manager, type_.clone())?,
                    get_label_or_concept_read_err(snapshot, type_manager, attribute_type_overridden.clone())?,
                )),
                Some(supertype) => {
                    let contains = TypeReader::get_capabilities::<Owns<'static>>(snapshot, supertype.clone(), false)?
                        .into_iter()
                        .any(|owns| &owns.attribute() == &attribute_type_overridden);

                    if !contains {
                        validation_errors.push(SchemaValidationError::HiddenOwnsIsNotInheritedByObjectType(
                            get_label_or_concept_read_err(snapshot, type_manager, type_.clone())?,
                            get_label_or_concept_read_err(snapshot, type_manager, attribute_type_overridden.clone())?,
                        ));
                    }
                }
            }

            let attribute_type = owns.attribute();
            if !is_type_transitive_supertype_or_same(
                // Any supertype (even transitive) fits
                snapshot,
                attribute_type.clone(),
                attribute_type_overridden.clone(),
            )? {
                validation_errors.push(SchemaValidationError::HiddenCapabilityInterfaceIsNotSupertype(
                    CapabilityKind::Owns,
                    get_label_or_concept_read_err(snapshot, type_manager, type_.clone())?,
                    get_label_or_concept_read_err(snapshot, type_manager, attribute_type.clone())?,
                    get_label_or_concept_read_err(snapshot, type_manager, attribute_type_overridden.clone())?,
                ));
            }
        }

        Ok(())
    }

    fn validate_hidden_plays(
        snapshot: &impl ReadableSnapshot,
        type_manager: &TypeManager,
        plays: Plays<'static>,
        validation_errors: &mut Vec<SchemaValidationError>,
    ) -> Result<(), ConceptReadError> {
        let type_ = plays.player();

        if let Some(plays_override) = TypeReader::get_type_capability_specialises(snapshot, plays.clone())? {
            let role_type_overridden = plays_override.role();
            let supertype = TypeReader::get_supertype(snapshot, type_.clone())?;
            match &supertype {
                None => validation_errors.push(SchemaValidationError::HiddenPlaysIsNotInheritedByObjectType(
                    get_label_or_concept_read_err(snapshot, type_manager, type_.clone())?,
                    get_label_or_concept_read_err(snapshot, type_manager, role_type_overridden.clone())?,
                )),
                Some(supertype) => {
                    let contains = TypeReader::get_capabilities::<Plays<'static>>(snapshot, supertype.clone(), false)?
                        .into_iter()
                        .any(|plays| &plays.role() == &role_type_overridden);

                    if !contains {
                        validation_errors.push(SchemaValidationError::HiddenPlaysIsNotInheritedByObjectType(
                            get_label_or_concept_read_err(snapshot, type_manager, type_.clone())?,
                            get_label_or_concept_read_err(snapshot, type_manager, role_type_overridden.clone())?,
                        ));
                    }
                }
            }

            let role_type = plays.role();
            if !is_type_transitive_supertype_or_same(
                // Any supertype (even transitive) fits
                snapshot,
                role_type.clone(),
                role_type_overridden.clone(),
            )? {
                validation_errors.push(SchemaValidationError::HiddenCapabilityInterfaceIsNotSupertype(
                    CapabilityKind::Plays,
                    get_label_or_concept_read_err(snapshot, type_manager, type_.clone())?,
                    get_label_or_concept_read_err(snapshot, type_manager, role_type.clone())?,
                    get_label_or_concept_read_err(snapshot, type_manager, role_type_overridden.clone())?,
                ));
            }
        }

        Ok(())
    }

    fn validate_redundant_capabilities<CAP: Capability<'static>>(
        snapshot: &impl ReadableSnapshot,
        type_manager: &TypeManager,
        capability: CAP,
        validation_errors: &mut Vec<SchemaValidationError>,
    ) -> Result<(), ConceptReadError> {
        if let Some(supertype) = TypeReader::get_supertype(snapshot, capability.object())? {
            let supertype_capabilities = TypeReader::get_capabilities::<CAP>(snapshot, supertype.clone(), false)?;

            let interface_type = capability.interface();
            if let Some(supertype_capability) =
                supertype_capabilities.iter().find(|cap| &cap.interface() == &interface_type)
            {
                let supertype_capability_object = supertype_capability.object();

                let capability_override = TypeReader::get_type_capability_specialises(snapshot, capability.clone())?;
                let correct_override = match capability_override {
                    None => false,
                    Some(capability_override) => &capability_override == supertype_capability,
                };
                if !correct_override {
                    validation_errors.push(
                        SchemaValidationError::CannotRedeclareInheritedCapabilityWithoutspecialisationWithOverride(
                            CAP::KIND,
                            get_label_or_concept_read_err(snapshot, type_manager, interface_type.clone())?,
                            get_label_or_concept_read_err(snapshot, type_manager, capability.object())?,
                            get_label_or_concept_read_err(snapshot, type_manager, supertype_capability_object.clone())?,
                        ),
                    );
                }

                let capability_annotations_declared =
                    TypeReader::get_capability_annotations_declared(snapshot, capability.clone())?;
                if capability_annotations_declared.is_empty() {
                    validation_errors.push(
                        SchemaValidationError::CannotRedeclareInheritedCapabilityWithoutspecialisationWithOverride(
                            CAP::KIND,
                            get_label_or_concept_read_err(snapshot, type_manager, interface_type.clone())?,
                            get_label_or_concept_read_err(snapshot, type_manager, capability.object())?,
                            get_label_or_concept_read_err(snapshot, type_manager, supertype_capability_object.clone())?,
                        ),
                    );
                }
            }
        }

        Ok(())
    }

    fn validate_redundant_type_constraints<T: KindAPI<'static>>(
        snapshot: &impl ReadableSnapshot,
        type_manager: &TypeManager,
        type_: T,
        annotation: &T::AnnotationType,
        validation_errors: &mut Vec<SchemaValidationError>,
    ) -> Result<(), ConceptReadError> {
        if !annotation.clone().into().category().inheritable() {
            return Ok(());
        }

        if let Some(supertype) = TypeReader::get_supertype(snapshot, type_.clone())? {
            let supertype_annotations = TypeReader::get_type_constraints(snapshot, supertype.clone())?;

            if supertype_annotations.keys().contains(&annotation) {
                validation_errors.push(
                    SchemaValidationError::CannotRedeclareInheritedAnnotationWithoutspecialisationForType(
                        T::ROOT_KIND,
                        get_label_or_concept_read_err(snapshot, type_manager, type_.clone())?,
                        get_label_or_concept_read_err(snapshot, type_manager, supertype.clone())?,
                        annotation.clone().into(),
                    ),
                );
            }
        }

        Ok(())
    }

    fn validate_redundant_edge_annotations<CAP: Capability<'static>>(
        snapshot: &impl ReadableSnapshot,
        type_manager: &TypeManager,
        edge: CAP,
        annotation: &CAP::AnnotationType,
        validation_errors: &mut Vec<SchemaValidationError>,
    ) -> Result<(), ConceptReadError> {
        if !annotation.clone().into().category().inheritable() {
            return Ok(());
        }

        if let Some(overridden_edge) = TypeReader::get_type_capability_specialises(snapshot, edge.clone())? {
            let overridden_edge_annotations = TypeReader::get_capability_constraints(snapshot, overridden_edge.clone())?;

            if overridden_edge_annotations.keys().contains(&annotation) {
                validation_errors.push(
                    SchemaValidationError::CannotRedeclareInheritedAnnotationWithoutspecialisationForCapability(
                        CAP::KIND,
                        get_label_or_concept_read_err(snapshot, type_manager, edge.object())?,
                        get_label_or_concept_read_err(snapshot, type_manager, overridden_edge.object())?,
                        get_label_or_concept_read_err(snapshot, type_manager, edge.interface())?,
                        annotation.clone().into(),
                    ),
                );
            }
        }

        Ok(())
    }

    fn validate_relation_type_has_relates(
        snapshot: &impl ReadableSnapshot,
        type_manager: &TypeManager,
        relation_type: RelationType<'static>,
        validation_errors: &mut Vec<SchemaValidationError>,
    ) -> Result<(), ConceptReadError> {
        let relates = TypeReader::get_capabilities::<Relates<'static>>(snapshot, relation_type.clone(), false)?;

        if relates.is_empty() {
            validation_errors.push(SchemaValidationError::RelationTypeMustRelateAtLeastOneRole(
                get_label_or_concept_read_err(snapshot, type_manager, relation_type)?,
            ));
        }

        Ok(())
    }

    fn validate_role_is_unique_for_relation_type_hierarchy(
        snapshot: &impl ReadableSnapshot,
        type_manager: &TypeManager,
        relation_type: RelationType<'static>,
        role_type: RoleType<'static>,
        validation_errors: &mut Vec<SchemaValidationError>,
    ) -> Result<(), ConceptReadError> {
        let role_label =
            TypeReader::get_label(snapshot, role_type)?.ok_or(ConceptReadError::CorruptMissingLabelOfType)?;
        let relation_supertypes = TypeReader::get_supertypes_transitive(snapshot, relation_type.clone())?;
        let relation_subtypes = TypeReader::get_subtypes_transitive(snapshot, relation_type.clone())?;

        for supertype in relation_supertypes {
            if let Err(err) = validate_role_name_uniqueness_non_transitive(snapshot, type_manager, supertype, &role_label) {
                validation_errors.push(err);
            }
        }
        for subtype in relation_subtypes {
            if let Err(err) = validate_role_name_uniqueness_non_transitive(snapshot, type_manager, subtype, &role_label) {
                validation_errors.push(err);
            }
        }

        Ok(())
    }

    fn validate_type_constraints(
        snapshot: &impl ReadableSnapshot,
        type_manager: &TypeManager,
        type_: impl KindAPI<'static>,
        validation_errors: &mut Vec<SchemaValidationError>,
    ) -> Result<(), ConceptReadError> {
        if let Some(supertype) = TypeReader::get_supertype(snapshot, type_.clone())? {
            if let Err(err) = validate_type_supertype_abstractness(
                snapshot: &impl ReadableSnapshot,
                type_manager: &TypeManager,
                type_,
                Some(supertype), // already found the supertype
                None,            // read abstractness from storage
                None,            // read abstractness from storage
            ) {
                validation_errors.push(err);
            }

            if let Err(err) = validate_type_declared_constraints_narrowing_of_supertype_constraints(
                snapshot,
                type_manager,
                type_.clone(),
                supertype.clone(),
            ) {
                validation_errors.push(err);
            }
        }

        // TODO: Just iterate over all constraints and count constraint descriptions without owners... If > 1, error!
        Self::validate_redundant_type_constraints(
            snapshot,
            type_manager,
            type_.clone(),
            &annotation,
            validation_errors,
        )?;

        Ok(())
    }

    fn validate_capabilities_annotations<CAP: Capability<'static>>(
        snapshot: &impl ReadableSnapshot,
        type_manager: &TypeManager,
        edge: CAP,
        validation_errors: &mut Vec<SchemaValidationError>,
    ) -> Result<(), ConceptReadError> {
        let declared_annotations = TypeReader::get_capability_annotations_declared(snapshot, edge.clone())?;

        for annotation in declared_annotations {
            Self::validate_redundant_edge_annotations(
                snapshot,
                type_manager,
                edge.clone(),
                &annotation,
                validation_errors,
            )?;
        }

        Ok(())
    }

    fn validate_type_ordering(
        snapshot: &impl ReadableSnapshot,
        type_manager: &TypeManager,
        type_: RoleType<'static>,
        validation_errors: &mut Vec<SchemaValidationError>,
    ) -> Result<(), ConceptReadError> {
        if let Some(supertype) = TypeReader::get_supertype(snapshot, type_.clone())? {
            if let Err(err) = validate_role_type_supertype_ordering_match(snapshot, type_manager, type_, supertype, None) {
                validation_errors.push(err);
            }
        }
        Ok(())
    }

    fn validate_capabilities_ordering(
        snapshot: &impl ReadableSnapshot,
        type_manager: &TypeManager,
        object_type: ObjectType<'static>,
        validation_errors: &mut Vec<SchemaValidationError>,
    ) -> Result<(), ConceptReadError> {
        if let Err(err) = validate_sibling_owns_ordering_match_for_type(snapshot, type_manager, object_type, &HashMap::new()) {
            validation_errors.push(err);
        }
        Ok(())
    }

    fn validate_attribute_type_value_type(
        snapshot: &impl ReadableSnapshot,
        type_manager: &TypeManager,
        attribute_type: AttributeType<'static>,
        validation_errors: &mut Vec<SchemaValidationError>,
    ) -> Result<(), ConceptReadError> {
        if let Some(supertype) = attribute_type.get_supertype(snapshot, type_manager)? {
            if let Some((supertype_value_type, _)) = supertype.get_value_type(snapshot, type_manager)? {
                if let Some(declared_value_type) =
                    TypeReader::get_value_type_declared(snapshot, attribute_type.clone())?
                {
                    let declared_value_type_annotations =
                        attribute_type.get_value_type_annotations_declared(snapshot, type_manager)?;
                    if declared_value_type_annotations.is_empty() {
                        validation_errors.push(
                            SchemaValidationError::CannotRedeclareInheritedValueTypeWithoutspecialisation(
                                get_label_or_concept_read_err(snapshot, type_manager, attribute_type.clone())?,
                                get_label_or_concept_read_err(snapshot, type_manager, supertype)?,
                                declared_value_type,
                                supertype_value_type,
                            ),
                        );
                    }
                }
            }
        }

        let value_type = attribute_type.get_value_type(snapshot, type_manager)?;
        if value_type.is_none() && !attribute_type.is_abstract(snapshot, type_manager)? {
            validation_errors.push(SchemaValidationError::AttributeTypeWithoutValueTypeShouldBeAbstract(
                get_label_or_concept_read_err(snapshot, type_manager, attribute_type)?,
            ));
        }

        Ok(())
    }

    fn validate_struct_definition_fields(
        _snapshot: &impl ReadableSnapshot,
        type_manager: &TypeManager,
        struct_definition: StructDefinition,
        validation_errors: &mut Vec<SchemaValidationError>,
    ) -> Result<(), ConceptReadError> {
        debug_assert_eq!(struct_definition.fields.len(), struct_definition.field_names.len());

        if struct_definition.fields.is_empty() {
            validation_errors.push(SchemaValidationError::StructShouldHaveAtLeastOneField(struct_definition.name));
        }

        Ok(())
    }
}
