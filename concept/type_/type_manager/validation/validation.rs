/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::collections::{HashMap, HashSet};
use std::iter;

use encoding::value::label::Label;
use itertools::Itertools;
use storage::snapshot::ReadableSnapshot;

use crate::{
    error::ConceptReadError,
    thing::thing_manager::ThingManager,
    type_::{
        annotation::{
            Annotation, AnnotationCardinality, AnnotationCategory, AnnotationKey, AnnotationRange, AnnotationRegex,
            AnnotationValues,
        },
        owns::Owns,
        relation_type::RelationType,
        role_type::RoleType,
        type_manager::{type_reader::TypeReader, validation::SchemaValidationError, TypeManager},
        Capability, KindAPI, Ordering, TypeAPI,
    },
};

// TODO: Use get_label_cloned from TypeAPI instead of this function
pub(crate) fn get_label_or_concept_read_err<'a>(
    snapshot: &impl ReadableSnapshot,
    type_: impl TypeAPI<'a>,
) -> Result<Label<'static>, ConceptReadError> {
    TypeReader::get_label(snapshot, type_)?.ok_or(ConceptReadError::CorruptMissingLabelOfType)
}

pub(crate) fn get_opt_label_or_concept_read_err<'a>(
    snapshot: &impl ReadableSnapshot,
    type_: Option<impl TypeAPI<'a>>,
) -> Result<Option<Label<'static>>, ConceptReadError> {
    Ok(match type_ {
        None => None,
        Some(type_) => Some(get_label_or_concept_read_err(snapshot, type_)?),
    })
}

pub(crate) fn get_label_or_schema_err<'a>(
    snapshot: &impl ReadableSnapshot,
    type_: impl TypeAPI<'a>,
) -> Result<Label<'static>, SchemaValidationError> {
    get_label_or_concept_read_err(snapshot, type_).map_err(SchemaValidationError::ConceptRead)
}

pub(crate) fn get_opt_label_or_schema_err<'a>(
    snapshot: &impl ReadableSnapshot,
    type_: Option<impl TypeAPI<'a>>,
) -> Result<Option<Label<'static>>, SchemaValidationError> {
    Ok(match type_ {
        None => None,
        Some(type_) => Some(get_label_or_schema_err(snapshot, type_)?),
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

pub(crate) fn is_type_transitive_supertype_or_same<T: KindAPI<'static>>(
    snapshot: &impl ReadableSnapshot,
    type_: T,
    potential_supertype: T,
) -> Result<bool, ConceptReadError> {
    if type_ == potential_supertype {
        return Ok(true);
    }

    Ok(TypeReader::get_supertypes_transitive(snapshot, type_.clone())?.contains(&potential_supertype.clone()))
}

pub(crate) fn is_overridden_interface_object_declared_supertype_or_self<T: KindAPI<'static>>(
    snapshot: &impl ReadableSnapshot,
    type_: T,
    overridden: T,
) -> Result<bool, ConceptReadError> {
    if type_ == overridden {
        return Ok(true);
    }

    Ok(TypeReader::get_supertype(snapshot, type_.clone())? == Some(overridden.clone()))
}

pub(crate) fn is_interface_hidden<CAP: Capability<'static>>(
    snapshot: &impl ReadableSnapshot,
    object_type: CAP::ObjectType,
    interface_type: CAP::InterfaceType,
) -> Result<bool, ConceptReadError> {
    let capabilities_overrides = TypeReader::get_object_capabilities_hides::<CAP>(snapshot, object_type)?;
    Ok(capabilities_overrides
        .iter()
        .find(|(capability, overridden_capability)| {
            interface_type == overridden_capability.interface() && interface_type != capability.interface()
        })
        .is_some())
}

pub(crate) fn validate_declared_annotation_is_compatible_with_inherited_annotations(
    snapshot: &impl ReadableSnapshot,
    type_: impl KindAPI<'static>,
    annotation_category: AnnotationCategory,
) -> Result<(), SchemaValidationError> {
    let existing_annotations =
        TypeReader::get_type_constraints(snapshot, type_.clone()).map_err(SchemaValidationError::ConceptRead)?;

    for (existing_annotation, _) in existing_annotations {
        let existing_annotation_category = existing_annotation.clone().into().category();
        if !annotation_category.declarable_below(existing_annotation_category) {
            return Err(SchemaValidationError::DeclaredAnnotationIsNotCompatibleWithInheritedAnnotation(
                annotation_category,
                existing_annotation_category,
                get_label_or_schema_err(snapshot, type_)?,
            ));
        }
    }

    Ok(())
}

pub(crate) fn validate_declared_capability_annotation_is_compatible_with_inherited_annotations<
    CAP: Capability<'static>,
>(
    snapshot: &impl ReadableSnapshot,
    capability: CAP,
    annotation_category: AnnotationCategory,
) -> Result<(), SchemaValidationError> {
    let existing_annotations = TypeReader::get_capability_constraints(snapshot, capability.clone())
        .map_err(SchemaValidationError::ConceptRead)?;

    for (existing_annotation, _) in existing_annotations {
        let existing_annotation_category = existing_annotation.clone().into().category();
        if !annotation_category.declarable_below(existing_annotation_category) {
            return Err(SchemaValidationError::DeclaredCapabilityAnnotationIsNotCompatibleWithInheritedAnnotation(
                annotation_category,
                existing_annotation_category,
                get_label_or_schema_err(snapshot, capability.object())?,
                get_label_or_schema_err(snapshot, capability.interface())?,
            ));
        }
    }

    Ok(())
}

pub(crate) fn validate_cardinality_narrows_inherited_cardinality<CAP: Capability<'static>>(
    snapshot: &impl ReadableSnapshot,
    type_manager: &TypeManager,
    edge: CAP,
    overridden_edge: CAP,
    cardinality: AnnotationCardinality,
    is_key: bool,
) -> Result<(), SchemaValidationError> {
    let overridden_cardinality =
        overridden_edge.get_cardinality_constraints(snapshot, type_manager).map_err(SchemaValidationError::ConceptRead)?;

    if overridden_cardinality.narrowed_correctly_by(&cardinality) {
        Ok(())
    } else {
        if is_key {
            debug_assert!(cardinality == AnnotationKey::CARDINALITY, "Invalid use of key");
            Err(SchemaValidationError::KeyDoesNotNarrowInheritedCardinality(
                get_label_or_schema_err(snapshot, edge.object())?,
                get_label_or_schema_err(snapshot, edge.interface())?,
                get_label_or_schema_err(snapshot, overridden_edge.object())?,
                get_label_or_schema_err(snapshot, overridden_edge.interface())?,
                overridden_cardinality,
            ))
        } else {
            Err(SchemaValidationError::CardinalityDoesNotNarrowInheritedCardinality(
                CAP::KIND,
                get_label_or_schema_err(snapshot, edge.object())?,
                get_label_or_schema_err(snapshot, edge.interface())?,
                get_label_or_schema_err(snapshot, overridden_edge.object())?,
                get_label_or_schema_err(snapshot, overridden_edge.interface())?,
                cardinality,
                overridden_cardinality,
            ))
        }
    }
}

pub(crate) fn validate_type_regex_narrows_inherited_regex<T: KindAPI<'static>>(
    snapshot: &impl ReadableSnapshot,
    attribute_type: T,
    supertype: Option<T>,
    regex: AnnotationRegex,
) -> Result<(), SchemaValidationError> {
    let supertype = match supertype {
        None => {
            TypeReader::get_supertype(snapshot, attribute_type.clone()).map_err(SchemaValidationError::ConceptRead)?
        }
        Some(_) => supertype,
    };

    if let Some(supertype) = supertype {
        if let Some((supertype_annotation, _)) =
            type_get_annotation_with_source_by_category(snapshot, supertype.clone(), AnnotationCategory::Regex)
                .map_err(SchemaValidationError::ConceptRead)?
        {
            match supertype_annotation {
                Annotation::Regex(supertype_regex) => {
                    return if supertype_regex.regex() == regex.regex() {
                        Ok(())
                    } else {
                        Err(SchemaValidationError::OnlyOneRegexCanBeSetForTypeHierarchy(
                            get_label_or_schema_err(snapshot, attribute_type)?,
                            get_label_or_schema_err(snapshot, supertype)?,
                            regex.clone(),
                            supertype_regex.clone(),
                        ))
                    };
                }
                _ => unreachable!("Should not reach it for Regex-related function"),
            }
        }
    }

    Ok(())
}

pub(crate) fn validate_edge_regex_narrows_inherited_regex<CAP: Capability<'static>>(
    snapshot: &impl ReadableSnapshot,
    owns: CAP,
    overridden_owns: Option<CAP>,
    regex: AnnotationRegex,
) -> Result<(), SchemaValidationError> {
    let overridden_owns = match overridden_owns {
        None => {
            TypeReader::get_capability_specializes(snapshot, owns.clone()).map_err(SchemaValidationError::ConceptRead)?
        }
        Some(_) => overridden_owns,
    };

    if let Some(override_owns) = overridden_owns {
        if let Some((supertype_annotation, supertype)) =
            type_get_annotation_with_source_by_category(snapshot, override_owns.clone(), AnnotationCategory::Regex)
                .map_err(SchemaValidationError::ConceptRead)?
        {
            match supertype_annotation {
                Annotation::Regex(supertype_regex) => {
                    return if supertype_regex.regex() == regex.regex() {
                        Ok(())
                    } else {
                        Err(SchemaValidationError::OnlyOneRegexCanBeSetForCapabilitiesHierarchy(
                            get_label_or_schema_err(snapshot, owns.object())?,
                            get_label_or_schema_err(snapshot, owns.interface())?,
                            get_label_or_schema_err(snapshot, override_owns.object())?,
                            get_label_or_schema_err(snapshot, override_owns.interface())?,
                            regex.clone(),
                            supertype_regex.clone(),
                        ))
                    };
                }
                _ => unreachable!("Should not reach it for Regex-related function"),
            }
        }
    }

    Ok(())
}

pub(crate) fn validate_type_range_narrows_inherited_range<T: KindAPI<'static>>(
    snapshot: &impl ReadableSnapshot,
    attribute_type: T,
    supertype: Option<T>,
    range: AnnotationRange,
) -> Result<(), SchemaValidationError> {
    let supertype = match supertype {
        None => {
            TypeReader::get_supertype(snapshot, attribute_type.clone()).map_err(SchemaValidationError::ConceptRead)?
        }
        Some(_) => supertype,
    };

    if let Some(supertype) = supertype {
        if let Some((supertype_annotation, _)) =
            type_get_annotation_with_source_by_category(snapshot, supertype.clone(), AnnotationCategory::Range)
                .map_err(SchemaValidationError::ConceptRead)?
        {
            match supertype_annotation {
                Annotation::Range(supertype_range) => {
                    return if supertype_range.narrowed_correctly_by(&range) {
                        Ok(())
                    } else {
                        Err(SchemaValidationError::RangeShouldNarrowInheritedRange(
                            get_label_or_schema_err(snapshot, attribute_type)?,
                            get_label_or_schema_err(snapshot, supertype)?,
                            range.clone(),
                            supertype_range.clone(),
                        ))
                    };
                }
                _ => unreachable!("Should not reach it for Range-related function"),
            }
        }
    }

    Ok(())
}

// TODO: Wrap into macro all these similar checks?
pub(crate) fn validate_edge_range_narrows_inherited_range<CAP: Capability<'static>>(
    snapshot: &impl ReadableSnapshot,
    owns: CAP,
    overridden_owns: Option<CAP>,
    range: AnnotationRange,
) -> Result<(), SchemaValidationError> {
    let overridden_owns = match overridden_owns {
        None => {
            TypeReader::get_capability_specializes(snapshot, owns.clone()).map_err(SchemaValidationError::ConceptRead)?
        }
        Some(_) => overridden_owns,
    };

    if let Some(override_owns) = overridden_owns {
        if let Some((supertype_annotation, supertype)) =
            type_get_annotation_with_source_by_category(snapshot, override_owns.clone(), AnnotationCategory::Range)
                .map_err(SchemaValidationError::ConceptRead)?
        {
            match supertype_annotation {
                Annotation::Range(supertype_range) => {
                    return if supertype_range.narrowed_correctly_by(&range) {
                        Ok(())
                    } else {
                        Err(SchemaValidationError::RangeShouldNarrowInheritedCapabilityRange(
                            get_label_or_schema_err(snapshot, owns.object())?,
                            get_label_or_schema_err(snapshot, owns.interface())?,
                            get_label_or_schema_err(snapshot, override_owns.object())?,
                            get_label_or_schema_err(snapshot, override_owns.interface())?,
                            range.clone(),
                            supertype_range.clone(),
                        ))
                    };
                }
                _ => unreachable!("Should not reach it for Range-related function"),
            }
        }
    }

    Ok(())
}

pub(crate) fn validate_type_values_narrows_inherited_values<T: KindAPI<'static>>(
    snapshot: &impl ReadableSnapshot,
    attribute_type: T,
    supertype: Option<T>,
    values: AnnotationValues,
) -> Result<(), SchemaValidationError> {
    let supertype = match supertype {
        None => {
            TypeReader::get_supertype(snapshot, attribute_type.clone()).map_err(SchemaValidationError::ConceptRead)?
        }
        Some(_) => supertype,
    };

    if let Some(supertype) = supertype {
        if let Some((supertype_annotation, _)) =
            type_get_annotation_with_source_by_category(snapshot, supertype.clone(), AnnotationCategory::Values)
                .map_err(SchemaValidationError::ConceptRead)?
        {
            match supertype_annotation {
                Annotation::Values(supertype_values) => {
                    return if supertype_values.narrowed_correctly_by(&values) {
                        Ok(())
                    } else {
                        Err(SchemaValidationError::ValuesShouldNarrowInheritedValues(
                            get_label_or_schema_err(snapshot, attribute_type)?,
                            get_label_or_schema_err(snapshot, supertype)?,
                            values.clone(),
                            supertype_values.clone(),
                        ))
                    };
                }
                _ => unreachable!("Should not reach it for Values-related function"),
            }
        }
    }

    Ok(())
}

pub(crate) fn validate_edge_values_narrows_inherited_values<CAP: Capability<'static>>(
    snapshot: &impl ReadableSnapshot,
    owns: CAP,
    overridden_owns: Option<CAP>,
    values: AnnotationValues,
) -> Result<(), SchemaValidationError> {
    let overridden_owns = match overridden_owns {
        None => {
            TypeReader::get_capability_specializes(snapshot, owns.clone()).map_err(SchemaValidationError::ConceptRead)?
        }
        Some(_) => overridden_owns,
    };

    if let Some(override_owns) = overridden_owns {
        if let Some((supertype_annotation, supertype)) =
            type_get_annotation_with_source_by_category(snapshot, override_owns.clone(), AnnotationCategory::Values)
                .map_err(SchemaValidationError::ConceptRead)?
        {
            match supertype_annotation {
                Annotation::Values(supertype_values) => {
                    return if supertype_values.narrowed_correctly_by(&values) {
                        Ok(())
                    } else {
                        Err(SchemaValidationError::ValuesShouldNarrowInheritedCapabilityValues(
                            get_label_or_schema_err(snapshot, owns.object())?,
                            get_label_or_schema_err(snapshot, owns.interface())?,
                            get_label_or_schema_err(snapshot, override_owns.object())?,
                            get_label_or_schema_err(snapshot, override_owns.interface())?,
                            values.clone(),
                            supertype_values.clone(),
                        ))
                    };
                }
                _ => unreachable!("Should not reach it for Values-related function"),
            }
        }
    }

    Ok(())
}

pub(crate) fn validate_type_annotations_narrowing_of_inherited_annotations<T: KindAPI<'static>>(
    snapshot: &impl ReadableSnapshot,
    type_manager: &TypeManager,
    subtype: T,
    supertype: T,
    subtype_annotation: T::AnnotationType,
) -> Result<(), SchemaValidationError> {
    match subtype_annotation.into() {
        Annotation::Abstract(_) => validate_type_supertype_abstractness(
            snapshot,
            type_manager,
            subtype.clone(),
            Some(supertype.clone()),
            Some(true), // set_subtype_abstract
            None,       // set_supertype_abstract => read from storage
        )?,
        Annotation::Regex(regex) => {
            validate_type_regex_narrows_inherited_regex(snapshot, subtype.clone(), Some(supertype.clone()), regex)?
        }
        Annotation::Range(range) => {
            validate_type_range_narrows_inherited_range(snapshot, subtype.clone(), Some(supertype.clone()), range)?
        }
        Annotation::Values(values) => {
            validate_type_values_narrows_inherited_values(snapshot, subtype.clone(), Some(supertype.clone()), values)?
        }
        | Annotation::Distinct(_)
        | Annotation::Independent(_)
        | Annotation::Unique(_)
        | Annotation::Key(_)
        | Annotation::Cardinality(_)
        | Annotation::Cascade(_) => {}
    }
    Ok(())
}

pub(crate) fn validate_edge_annotations_narrowing_of_inherited_annotations<CAP: Capability<'static>>(
    snapshot: &impl ReadableSnapshot,
    type_manager: &TypeManager,
    edge: CAP,
    overridden_edge: CAP,
    edge_annotation: Annotation,
) -> Result<(), SchemaValidationError> {
    match edge_annotation {
        Annotation::Cardinality(cardinality) => validate_cardinality_narrows_inherited_cardinality(
            snapshot,
            type_manager,
            edge.clone(),
            overridden_edge.clone(),
            cardinality,
            false, // is_key
        )?,
        Annotation::Key(_) => validate_cardinality_narrows_inherited_cardinality(
            snapshot,
            type_manager,
            edge.clone(),
            overridden_edge.clone(),
            AnnotationKey::CARDINALITY,
            true,
        )?,
        Annotation::Regex(regex) => {
            validate_edge_regex_narrows_inherited_regex(snapshot, edge.clone(), Some(overridden_edge.clone()), regex)?
        }
        Annotation::Range(range) => {
            validate_edge_range_narrows_inherited_range(snapshot, edge.clone(), Some(overridden_edge.clone()), range)?
        }
        Annotation::Values(values) => validate_edge_values_narrows_inherited_values(
            snapshot,
            edge.clone(),
            Some(overridden_edge.clone()),
            values,
        )?,
        | Annotation::Abstract(_)
        | Annotation::Distinct(_)
        | Annotation::Independent(_)
        | Annotation::Unique(_)
        | Annotation::Cascade(_) => {}
    }
    Ok(())
}

pub(crate) fn validate_role_type_supertype_ordering_match(
    snapshot: &impl ReadableSnapshot,
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
            get_label_or_schema_err(snapshot, type_)?,
            get_label_or_schema_err(snapshot, supertype)?,
            type_ordering,
            supertype_ordering,
        ))
    }
}

pub(crate) fn validate_owns_override_ordering_match(
    snapshot: &impl ReadableSnapshot,
    owns: Owns<'static>,
    overridden_owns: Owns<'static>,
    set_subtype_owns_ordering: Option<Ordering>,
) -> Result<(), SchemaValidationError> {
    let edge_ordering = set_subtype_owns_ordering.unwrap_or(
        TypeReader::get_capability_ordering(snapshot, owns.clone()).map_err(SchemaValidationError::ConceptRead)?,
    );
    let overridden_edge_ordering = TypeReader::get_capability_ordering(snapshot, overridden_owns.clone())
        .map_err(SchemaValidationError::ConceptRead)?;

    if edge_ordering == overridden_edge_ordering {
        Ok(())
    } else {
        Err(SchemaValidationError::OrderingDoesNotMatchWithOverride(
            get_label_or_schema_err(snapshot, owns.owner())?,
            get_label_or_schema_err(snapshot, overridden_owns.owner())?,
            get_label_or_schema_err(snapshot, owns.attribute())?,
            edge_ordering,
            overridden_edge_ordering,
        ))
    }
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
        None => TypeReader::get_supertype(snapshot, subtype.clone()).map_err(SchemaValidationError::ConceptRead)?,
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
                get_label_or_schema_err(snapshot, supertype)?,
                get_label_or_schema_err(snapshot, subtype)?,
            )),
        }
    } else {
        Ok(())
    }
}

pub(crate) fn is_ordering_compatible_with_distinct_annotation(ordering: Ordering, distinct_set: bool) -> bool {
    if distinct_set {
        ordering == Ordering::Ordered
    } else {
        true
    }
}

// TODO: Use a type manager method instead
pub(crate) fn type_get_declared_annotation_by_category(
    snapshot: &impl ReadableSnapshot,
    type_: impl KindAPI<'static>,
    annotation_category: AnnotationCategory,
) -> Result<Option<Annotation>, ConceptReadError> {
    let annotation = TypeReader::get_type_annotations_declared(snapshot, type_.clone())?
        .into_iter()
        .find(|found_annotation| found_annotation.clone().into().category() == annotation_category);
    Ok(annotation.map(|val| val.clone().into()))
}

// TODO: Use a type manager method instead
pub(crate) fn capability_get_declared_annotation_by_category<CAP: Capability<'static>>(
    snapshot: &impl ReadableSnapshot,
    capability: CAP,
    annotation_category: AnnotationCategory,
) -> Result<Option<Annotation>, ConceptReadError> {
    let annotation = TypeReader::get_capability_annotations_declared(snapshot, capability.clone())?
        .into_iter()
        .find(|found_annotation| found_annotation.clone().into().category() == annotation_category);
    Ok(annotation.map(|val| val.clone().into()))
}

pub(crate) fn type_get_annotation_with_source_by_category<T: KindAPI<'static>>(
    snapshot: &impl ReadableSnapshot,
    type_manager: &TypeManager,
    type_: T,
    annotation_category: AnnotationCategory,
) -> Result<Option<(T::AnnotationType, T)>, ConceptReadError> {
    let type_and_supertypes = iter::once(type_).chain(type_.get_supertypes_transitive(snapshot, type_manager)?.into_iter());
    for current_type in type_and_supertypes {
        let annotations = current_type.get_annotations_declared(snapshot, type_manager)?;
        let found_annotation_opt = annotations
            .iter()
            .find(|annotation| annotation.clone().into().category() == annotation_category);
        if let Some(found_annotation) = found_annotation_opt {
            return Ok(Some((found_annotation, current_type)));
        }
    }
    Ok(None)
}

pub(crate) fn capability_get_annotation_with_source_by_category<CAP: Capability<'static>>(
    snapshot: &impl ReadableSnapshot,
    type_manager: &TypeManager,
    capability: CAP,
    annotation_category: AnnotationCategory,
) -> Result<Option<(CAP::AnnotationType, CAP)>, ConceptReadError> {
    let capability_and_specialized = iter::once(capability).chain(capability.get_specializes_transitive(snapshot, type_manager)?.into_iter());
    for current_capability in capability_and_specialized {
        let annotations = current_capability.get_annotations_declared(snapshot, type_manager)?;
        let found_annotation_opt = annotations
            .iter()
            .find(|annotation| annotation.clone().into().category() == annotation_category);
        if let Some(found_annotation) = found_annotation_opt {
            return Ok(Some((found_annotation, current_capability)));
        }
    }
    Ok(None)
}

pub fn validate_capabilities_cardinalities_narrowing<CAP: Capability<'static>>(
    type_manager: &TypeManager,
    snapshot: &impl ReadableSnapshot,
    type_: CAP::ObjectType,
    not_stored_set_capabilities: &HashMap<CAP, bool>,
    not_stored_set_cardinalities: &HashMap<CAP, AnnotationCardinality>,
    not_stored_set_hidden: &HashMap<CAP, bool>,
    validation_errors: &mut Vec<SchemaValidationError>,
) -> Result<(), ConceptReadError> {
    let mut cardinality_connections: HashMap<CAP, HashSet<CAP>> = HashMap::new();
    let mut cardinalities: HashMap<CAP, AnnotationCardinality> = not_stored_set_cardinalities.clone();

    let capabilities: HashSet<CAP> = TypeReader::get_capabilities(snapshot, type_.clone(), true)?;

    for capability in capabilities.into_iter().chain(not_stored_set_capabilities.iter().filter(|(_, is_set)| **is_set)).map(|(cap, _)| cap) {
        let is_hidden_in_storage = TypeReader::get_object_capabilities_hides(snapshot, type_.clone())?.into_iter().find(|(hider, hidden)| hidden == &capability);
        let updated_hide = not_stored_set_hidden.get(&capability);
        let updated_set_hidden = *updated_hide.unwrap_or(&false);
        let updated_unset_hidden = !*updated_hide.unwrap_or(&true);
        let updated_unset_capability = !not_stored_set_capabilities.get(&capability).unwrap_or(&true);
        if is_hidden_in_storage.is_some() && !updated_unset_hidden || updated_set_hidden || updated_unset_capability {
            continue;
        }

        if !cardinalities.contains_key(&capability) {
            cardinalities.insert(capability.clone(), capability.get_cardinality(snapshot, type_manager)?);
        }

        for capability_specialized in capability.get_specializes_transitive(snapshot, type_manager)? {
            if !cardinalities.contains_key(&capability) {
                cardinalities.insert(capability.clone(), capability_specialized.get_cardinality(snapshot, type_manager)?);
            }
            let capability_connection = cardinality_connections.entry(capability_specialized.clone()).or_insert(HashSet::new());
            capability_connection.insert(capability.clone());
        }
    }

    for (root_capability, specializing_capabilities) in cardinality_connections {
        let root_cardinality = cardinalities.get(&root_capability).unwrap();
        let inheriting_cardinality =
            specializing_capabilities.iter().filter_map(|capability| cardinalities.get(capability).copied()).sum();

        if !root_cardinality.narrowed_correctly_by(&inheriting_cardinality) {
            validation_errors.push(
                SchemaValidationError::SummarizedCardinalityOfCapabilitiesOverridingSingleCapabilityOverflowsConstraint(
                    CAP::KIND,
                    get_label_or_concept_read_err(snapshot, root_capability.object())?,
                    get_label_or_concept_read_err(snapshot, root_capability.interface())?,
                    get_opt_label_or_concept_read_err(
                        snapshot,
                        specializing_capabilities.iter().next().map(|cap| cap.object()),
                    )?,
                    *root_cardinality,
                    inheriting_cardinality,
                ),
            );
        }
    }

    Ok(())
}
