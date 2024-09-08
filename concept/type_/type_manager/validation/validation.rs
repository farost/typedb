/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::collections::HashMap;

use encoding::value::label::Label;
use storage::snapshot::ReadableSnapshot;

use crate::{
    error::ConceptReadError,
    type_::{
        owns::Owns,
        relation_type::RelationType,
        role_type::RoleType,
        type_manager::{type_reader::TypeReader, validation::SchemaValidationError, TypeManager},
        Capability, KindAPI, Ordering, TypeAPI,
    },
};
use crate::type_::attribute_type::AttributeType;
use crate::type_::constraint::{Constraint, filter_by_source};
use crate::type_::object_type::ObjectType;
use crate::type_::OwnerAPI;

pub(crate) fn get_label_or_concept_read_err<'a>(
    snapshot: &impl ReadableSnapshot,
    type_manager: &TypeManager,
    type_: impl TypeAPI<'a>,
) -> Result<Label<'static>, ConceptReadError> {
    type_.get_label_cloned(snapshot, type_manager).map_err(|_| ConceptReadError::CorruptMissingLabelOfType)
}

pub(crate) fn get_label_or_schema_err<'a>(
    snapshot: &impl ReadableSnapshot,
    type_manager: &TypeManager,
    type_: impl TypeAPI<'a>,
) -> Result<Label<'static>, SchemaValidationError> {
    get_label_or_concept_read_err(snapshot, type_manager, type_).map_err(SchemaValidationError::ConceptRead)
}

pub(crate) fn get_opt_label_or_schema_err<'a>(
    snapshot: &impl ReadableSnapshot,
    type_manager: &TypeManager,
    type_: Option<impl TypeAPI<'a>>,
) -> Result<Option<Label<'static>>, SchemaValidationError> {
    Ok(match type_ {
        None => None,
        Some(type_) => Some(get_label_or_schema_err(snapshot, type_manager, type_)?),
    })
}

pub(crate) fn validate_role_name_uniqueness_non_transitive(
    snapshot: &impl ReadableSnapshot,
    type_manager: &TypeManager,
    relation_type: RelationType<'static>,
    new_label: &Label<'static>,
) -> Result<(), SchemaValidationError> {
    let scoped_label = Label::build_scoped(
        new_label.name.as_str(),
        relation_type.get_label(snapshot, type_manager).map_err(SchemaValidationError::ConceptRead)?.name().as_str(),
    );

    if TypeReader::get_labelled_type::<RoleType<'static>>(snapshot, &scoped_label)
        .map_err(SchemaValidationError::ConceptRead)?
        .is_some()
    {
        Err(SchemaValidationError::RoleNameShouldBeUniqueForRelationTypeHierarchy(new_label.clone(), scoped_label))
    } else {
        Ok(())
    }
}

pub(crate) fn validate_type_declared_constraints_narrowing_of_supertype_constraints<T: KindAPI<'static>>(
    snapshot: &impl ReadableSnapshot,
    type_manager: &TypeManager,
    subtype: T,
    supertype: T,
) -> Result<(), SchemaValidationError> {
    let supertype_constraints = supertype.get_constraints(snapshot, type_manager).map_err(SchemaValidationError::ConceptRead)?;
    let subtype_constraints = subtype.get_constraints(snapshot, type_manager).map_err(SchemaValidationError::ConceptRead)?.into_iter();

    for subtype_constraint in filter_by_source!(subtype_constraints, subtype) {
        for supertype_constraint in supertype_constraints.iter() {
            supertype_constraint.validate_narrowed_by_any_type(&subtype_constraint).map_err(|source| SchemaValidationError::SubtypeConstraintDoesNotNarrowSupertypeConstraint(
                get_label_or_schema_err(snapshot, type_manager, subtype.clone())?,
                get_label_or_schema_err(snapshot, type_manager, supertype.clone())?,
                source,
            ))?;
        }
    }

    Ok(())
}

pub(crate) fn validate_role_type_supertype_ordering_match(
    snapshot: &impl ReadableSnapshot,
    type_manager: &TypeManager,
    type_: RoleType<'static>,
    supertype: RoleType<'static>,
    set_subtype_role_ordering: Option<Ordering>,
) -> Result<(), SchemaValidationError> {
    let supertype_ordering =
        TypeReader::get_type_ordering(snapshot, supertype.clone()).map_err(SchemaValidationError::ConceptRead)?;
    let type_ordering = set_subtype_role_ordering
        .unwrap_or(TypeReader::get_type_ordering(snapshot, type_.clone()).map_err(SchemaValidationError::ConceptRead)?);

    if type_ordering == supertype_ordering {
        Ok(())
    } else {
        Err(SchemaValidationError::OrderingDoesNotMatchWithSupertype(
            get_label_or_schema_err(snapshot, type_manager, type_)?,
            get_label_or_schema_err(snapshot, type_manager, supertype)?,
            type_ordering,
            supertype_ordering,
        ))
    }
}

pub(crate) fn validate_sibling_owns_ordering_match_for_type(
    snapshot: &impl ReadableSnapshot,
    type_manager: &TypeManager,
    owner_type: ObjectType<'static>,
    new_set_owns_orderings: &HashMap<Owns<'static>, Ordering>,
) -> Result<(), SchemaValidationError> {
    let mut attribute_types_ordering: HashMap<AttributeType<'static>, (AttributeType<'static>, Ordering)> = HashMap::new();
    let existing_owns = owner_type
        .get_owns_with_specialised(snapshot, type_manager)
        .map_err(SchemaValidationError::ConceptRead)?
        .into_iter()
        .filter(|owns| !new_set_owns_orderings.contains_key(*owns))
        .map(|owns| (owns, None::<Ordering>));

    let all_updated_owns = new_set_owns_orderings
        .iter()
        .map(|(new_owns, new_ordering)| (new_owns, Some(new_ordering.clone())))
        .chain(existing_owns);

    for (owns, ordering_opt) in all_updated_owns {
        let ordering = ordering_opt.unwrap_or(owns.get_ordering(snapshot, type_manager)?);
        let attribute_type = owns.attribute();
        let root_attribute_type = if let Some(root) = attribute_type.get_supertypes_transitive(snapshot, type_manager)?.last() {
            root.clone()
        } else {
            attribute_type.clone()
        };

        if let Some((first_subtype, first_ordering)) = attribute_types_ordering.get(&root_attribute_type) {
            if first_ordering != &ordering {
                return Err(SchemaValidationError::OrderingDoesNotMatchWithCapabilityOfSubtypeInterface(
                    get_label_or_schema_err(snapshot, type_manager, owner_type)?,
                    get_label_or_schema_err(snapshot, type_manager, first_subtype)?,
                    get_label_or_schema_err(snapshot, type_manager, attribute_type)?,
                    first_ordering.clone(),
                    ordering,
                ));
            }
        } else {
            attribute_types_ordering.insert(root_attribute_type, (attribute_type, ordering));
        }
    }

    Ok(())
}

pub(crate) fn validate_type_supertype_abstractness<T: KindAPI<'static>>(
    snapshot: &impl ReadableSnapshot,
    type_manager: &TypeManager,
    subtype: T,
    supertype: Option<T>,
    set_subtype_abstract: Option<bool>,
    set_supertype_abstract: Option<bool>,
) -> Result<(), SchemaValidationError> {
    let supertype = match supertype {
        None => subtype.get_supertype(snapshot, type_manager).map_err(SchemaValidationError::ConceptRead)?,
        Some(_) => supertype,
    };

    if let Some(supertype) = supertype {
        let subtype_abstract = set_subtype_abstract
            .unwrap_or(subtype.is_abstract(snapshot, type_manager).map_err(SchemaValidationError::ConceptRead)?);
        let supertype_abstract = set_supertype_abstract
            .unwrap_or(supertype.is_abstract(snapshot, type_manager).map_err(SchemaValidationError::ConceptRead)?);

        match (subtype_abstract, supertype_abstract) {
            (false, false) | (false, true) | (true, true) => Ok(()),
            (true, false) => Err(SchemaValidationError::AbstractTypesSupertypeHasToBeAbstract(
                get_label_or_schema_err(snapshot, type_manager, supertype)?,
                get_label_or_schema_err(snapshot, type_manager, subtype)?,
            )),
        }
    } else {
        Ok(())
    }
}

// TODO: This validation can be resurrected (and all the other capabilities constraints validations as well)
// but it should be rewritten so all the constraints are queried for each separate CAP::ObjectType! (and they have to be validated separately)
// pub fn validate_capabilities_cardinalities_narrowing<CAP: Capability<'static>>(
//     snapshot: &impl ReadableSnapshot,
//     type_manager: &TypeManager,
//     type_: CAP::ObjectType,
//     not_stored_set_capabilities: &HashMap<CAP, bool>,
//     not_stored_set_cardinalities: &HashMap<CAP, AnnotationCardinality>,
//     not_stored_set_hidden: &HashMap<CAP, bool>,
//     validation_errors: &mut Vec<SchemaValidationError>,
// ) -> Result<(), ConceptReadError> {
//     let mut cardinality_connections: HashMap<CAP, HashSet<CAP>> = HashMap::new();
//     let mut cardinalities: HashMap<CAP, AnnotationCardinality> = not_stored_set_cardinalities.clone();
//
//     let capabilities: HashSet<CAP> = TypeReader::get_capabilities(snapshot, type_.clone(), true)?;
//
//     for capability in capabilities.into_iter().chain(not_stored_set_capabilities.iter().filter(|(_, is_set)| **is_set)).map(|(cap, _)| cap) {
//         // TODO: Looks like we need to ignore abstract capabilities? Think about it!
//
//         if !cardinalities.contains_key(&capability) {
//             cardinalities.insert(capability.clone(), capability.get_cardinality(snapshot, type_manager)?);
//         }
//
//         for capability_specialised in capability.get_specialises_transitive(snapshot, type_manager)? {
//             if !cardinalities.contains_key(&capability) {
//                 cardinalities.insert(capability.clone(), capability_specialised.get_cardinality(snapshot, type_manager)?);
//             }
//             let capability_connection = cardinality_connections.entry(capability_specialised.clone()).or_insert(HashSet::new());
//             capability_connection.insert(capability.clone());
//         }
//     }
//
//     for (root_capability, specialising_capabilities) in cardinality_connections {
//         let root_cardinality = cardinalities.get(&root_capability).unwrap();
//         let inheriting_cardinality =
//             specialising_capabilities.iter().filter_map(|capability| cardinalities.get(capability).copied()).sum();
//
//         if !root_cardinality.narrowed_correctly_by(&inheriting_cardinality) {
//             validation_errors.push(
//                 SchemaValidationError::SummarizedCardinalityOfCapabilitiesSpecialisingSingleCapabilityOverflowsConstraint(
//                     CAP::KIND,
//                     get_label_or_concept_read_err(snapshot, type_manager, root_capability.object())?,
//                     get_label_or_concept_read_err(snapshot, type_manager, root_capability.interface())?,
//                     get_opt_label_or_concept_read_err(
//                         snapshot,
//                         specialising_capabilities.iter().next().map(|cap| cap.object()),
//                     )?,
//                     *root_cardinality,
//                     inheriting_cardinality,
//                 ),
//             );
//         }
//     }
//
//     Ok(())
// }
