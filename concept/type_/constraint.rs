/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::fmt;
use std::marker::PhantomData;

use storage::snapshot::{ReadableSnapshot, WritableSnapshot};

use crate::{
    error::ConceptReadError,
    thing::thing_manager::ThingManager,
    type_::{
        annotation::{
            Annotation, AnnotationAbstract, AnnotationCardinality, AnnotationCategory,
            AnnotationDistinct, AnnotationError, AnnotationIndependent, AnnotationKey, AnnotationRange,
            AnnotationRegex, AnnotationUnique, AnnotationValues, DefaultFrom,
        },
        owns::Owns,
        type_manager::{type_reader::TypeReader, TypeManager},
        Capability,
    },
};
use crate::type_::{KindAPI, TypeAPI};
use crate::type_::annotation::AnnotationCascade;

macro_rules! compute_constraint_one_to_one_annotation {
    ($func_name:ident, $annotation_enum:path, $annotation_type:ident) => {
        pub fn $func_name<'a, A: Into<Annotation> + Clone + 'a>(
            annotations: impl IntoIterator<Item = &'a A>,
        ) -> Option<$annotation_type> {
            annotations
                .into_iter()
                .filter_map(|annotation| match annotation.clone().into() {
                    $annotation_enum(annotation) => Some(annotation),
                    _ => None,
                })
                .next()
        }
    };
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum ConstraintDescription {
    Abstract(AnnotationAbstract),
    Distinct(AnnotationDistinct),
    Independent(AnnotationIndependent),
    Unique(AnnotationUnique),
    Cardinality(AnnotationCardinality),
    Regex(AnnotationRegex),
    Range(AnnotationRange),
    Values(AnnotationValues),
}

impl ConstraintDescription {
    pub fn validation_mode(&self) -> ConstraintValidationMode {
        match self {
            ConstraintDescription::Abstract(_) => ConstraintValidationMode::SingleInstanceOfType,

            ConstraintDescription::Distinct(_)
            | ConstraintDescription::Independent(_)
            | ConstraintDescription::Regex(_)
            | ConstraintDescription::Range(_)
            | ConstraintDescription::Values(_) => ConstraintValidationMode::SingleInstanceOfTypeOrSubtype,

            ConstraintDescription::Cardinality(_) => ConstraintValidationMode::AllInstancesOfSiblingTypeOrSubtypes,

            ConstraintDescription::Unique(_) => ConstraintValidationMode::AllInstancesOfTypeOrSubtypes,
        }
    }

    pub fn inheritable(&self) -> bool { // TODO: find a better name. Infectious for subtypes?..
        match self {
            ConstraintDescription::Abstract(_) => true,

            | ConstraintDescription::Distinct(_)
            | ConstraintDescription::Independent(_)
            | ConstraintDescription::Unique(_)
            | ConstraintDescription::Cardinality(_)
            | ConstraintDescription::Regex(_)
            | ConstraintDescription::Range(_)
            | ConstraintDescription::Values(_) => false,
        }
    }
}

fn validate_cardinality_owns() {

}

fn validate_cardinality_plays() {

}

fn validate_cardinality_relates() {

}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct TypeConstraint<T: KindAPI<'static>> {
    description: ConstraintDescription,
    _phantom: PhantomData<T>
}

impl<T: KindAPI<'static>> TypeConstraint<T> {
    pub fn new(description: ConstraintDescription) -> Self {
        Self { description, _phantom: PhantomData }
    }

    pub fn description(&self) -> ConstraintDescription {
        self.description.clone()
    }
}

macro_rules! filter_by_constraint_description_match {
    ($constraints:ident, $pattern:pat) => {
        $constraints.iter().filter(|(constraint, sources)| {
            let description = constraint.description();
            matches!(description, $pattern)
        }).collect()
    };
}
pub use filter_by_constraint_description_match;

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct CapabilityConstraint<CAP: Capability<'static>> {
    description: ConstraintDescription,
    _phantom: PhantomData<CAP>
}

impl<CAP: Capability<'static>> CapabilityConstraint<CAP> {
    pub fn new(description: ConstraintDescription) -> Self {
        Self { description, _phantom: PhantomData }
    }

    pub fn description(&self) -> ConstraintDescription {
        self.description.clone()
    }
}

impl CapabilityConstraint<Owns<'static>> {

    pub fn validate_single(&self, owner: &Object<'_>, attribute: &Attribute<'_>) -> Result<(), ConstraintError> {
        match self.description() {
            ConstraintDescription::Abstract(_) => validate_cardinality_owns(),
            ConstraintDescription::Distinct(_) => validate_cardinality_owns(),
            ConstraintDescription::Independent(_) => {},
            ConstraintDescription::Unique(_) => validate_cardinality_owns(),
            ConstraintDescription::Cardinality(cardinality) => validate_cardinality_owns(),
            ConstraintDescription::Regex(regex) => validate_cardinality_owns(),
            ConstraintDescription::Range(range) => validate_cardinality_owns(),
            ConstraintDescription::Values(values) => validate_cardinality_owns(),
        }
        Ok(())
    }

    // pub fn validate_all(&self, ...) -> Result<(), ConstraintError> {
    //     match self.description() {
    //         ConstraintDescription::Abstract(_) => validate_cardinality_owns(),
    //         ConstraintDescription::Distinct(_) => validate_cardinality_owns(),
    //         ConstraintDescription::Independent(_) => {},
    //         ConstraintDescription::Unique(_) => validate_cardinality_owns(),
    //         ConstraintDescription::Cardinality(cardinality) => validate_cardinality_owns(),
    //         ConstraintDescription::Regex(regex) => validate_cardinality_owns(),
    //         ConstraintDescription::Range(range) => validate_cardinality_owns(),
    //         ConstraintDescription::Values(values) => validate_cardinality_owns(),
    //     }
    //     Ok(())
    // }
}

// Siblings = both interface types i1 and i2 are capabilities of the same capability type (owns/plays/relates)
// of the same object type (e.g. they are owned by the same type, they are played by the same type)
// with "i1 isa $x; i2 isa $x;"
#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum ConstraintValidationMode {
    SingleInstanceOfType,
    SingleInstanceOfTypeOrSubtype,
    AllInstancesOfSiblingTypeOrSubtypes,
    AllInstancesOfTypeOrSubtypes,
}

struct Constraint {}

impl Constraint {

    compute_constraint_one_to_one_annotation!(compute_abstract, Annotation::Abstract, AnnotationAbstract);
    compute_constraint_one_to_one_annotation!(compute_independent, Annotation::Independent, AnnotationIndependent);
    compute_constraint_one_to_one_annotation!(compute_key, Annotation::Key, AnnotationKey);

    pub fn compute_distinct<'a, A: Into<Annotation> + Clone + 'a>(
        annotations: impl IntoIterator<Item = &'a A>,
        default: Option<AnnotationDistinct>,
    ) -> Option<AnnotationDistinct> {
        let distinct = annotations
            .into_iter()
            .filter_map(|annotation| match annotation.clone().into() {
                Annotation::Distinct(distinct) => Some(distinct),
                _ => None,
            })
            .next();
        return if distinct.is_some() { distinct } else { default };
    }

    pub fn compute_unique<'a, A: Into<Annotation> + Clone + 'a>(
        annotations: impl IntoIterator<Item = &'a A>,
    ) -> Option<AnnotationUnique> {
        annotations
            .into_iter()
            .filter_map(|annotation| match annotation.clone().into() {
                // Unique and Key cannot be set together
                Annotation::Unique(_) | Annotation::Key(_) => Some(AnnotationUnique),
                _ => None,
            })
            .next()
    }

    // TODO: Remove
    pub fn compute_cardinalities<'a, TSource: Clone + PartialEq + 'a, A: Into<Annotation> + Clone + 'a>(
        annotations: HashMap<TSource, impl IntoIterator<Item = &'a A>>,
        default: Option<AnnotationCardinality>,
    ) -> HashMap<TSource, AnnotationCardinality> {
        let cardinality = annotations
            .into_iter()
            .filter_map(|(source, annotation)| match annotation.clone().into() {
                // Cardinality and Key cannot be set together
                Annotation::Cardinality(card) => Some(card),
                Annotation::Key(_) => Some(AnnotationKey::CARDINALITY),
                _ => None,
            })
            .collect();
        return if cardinality.is_some() { cardinality } else { default };
    }

    compute_constraint_one_to_one_annotation!(compute_regex, Annotation::Regex, AnnotationRegex);
    compute_constraint_one_to_one_annotation!(compute_cascade, Annotation::Cascade, AnnotationCascade);
    compute_constraint_one_to_one_annotation!(compute_range, Annotation::Range, AnnotationRange);
    compute_constraint_one_to_one_annotation!(compute_values, Annotation::Values, AnnotationValues);

    pub(crate) fn annotations_by_validation_modes<'a, A: Into<Annotation> + Clone + 'a>(
        annotations: impl IntoIterator<Item = A>,
    ) -> Result<HashMap<&'static ConstraintValidationMode, HashSet<Annotation>>, AnnotationError> {
        let mut map: HashMap<&ConstraintValidationMode, HashSet<Annotation>> = HashMap::new();

        for annotation in annotations.into_iter() {
            let annotation = annotation.clone().into();
            let modes = Self::constraint_validation_mode(annotation.category());

            for mode in modes {
                map.entry(mode).or_insert_with(HashSet::default).insert(annotation.clone());
            }
        }

        Ok(map)
    }

    pub(crate) fn constraint_validation_mode(
        annotation_category: AnnotationCategory,
    ) -> &'static [ConstraintValidationMode] {
        match annotation_category {
            AnnotationCategory::Abstract => &[ConstraintValidationMode::SingleInstanceOfType],
            AnnotationCategory::Distinct => &[ConstraintValidationMode::SingleInstanceOfTypeOrSubtype],
            AnnotationCategory::Unique => &[ConstraintValidationMode::AllInstancesOfTypeOrSubtypes],
            AnnotationCategory::Cardinality => &[ConstraintValidationMode::AllInstancesOfSiblingTypeOrSubtypes],
            AnnotationCategory::Key => { // TODO: use ConstraintCategory or something like that not to face Key...
                // WARNING: must match Unique + Cardinality checks!
                &[
                    ConstraintValidationMode::AllInstancesOfSiblingTypeOrSubtypes,
                    ConstraintValidationMode::AllInstancesOfTypeOrSubtypes,
                ]
            }
            AnnotationCategory::Regex => &[ConstraintValidationMode::SingleInstanceOfTypeOrSubtype],
            AnnotationCategory::Range => &[ConstraintValidationMode::SingleInstanceOfTypeOrSubtype],
            AnnotationCategory::Values => &[ConstraintValidationMode::SingleInstanceOfTypeOrSubtype],
            AnnotationCategory::Cascade => &[],
            AnnotationCategory::Independent => &[],
        }
    }
}

#[derive(Debug)]
pub enum ConstraintError {
    OwnsValidationError { constraint_description: ConstraintDescription, owns: Owns<'static> },
}

impl fmt::Display for ConstraintError {
    fn fmt(&self, _: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl Error for ConstraintError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            ConstraintError::OwnsValidationError { .. } => None,
        }
    }
}
