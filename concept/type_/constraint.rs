/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::collections::{HashMap, HashSet};
use std::collections::hash_map::Iter;
use std::error::Error;
use std::fmt;
use std::hash::Hash;
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

macro_rules! with_constraint_description {
    ($constraint_description:ident, $target_enum:ident, $default:expr, |$constraint:ident| $expr:expr) => {
        match &$constraint_description {
            ConstraintDescription::$target_enum($constraint) => $expr,
            _ => $default,
        }
    };
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum ConstraintCategory {
    Abstract,
    Distinct,
    Independent,
    Unique,
    Key,
    Cardinality,
    Regex,
    Range,
    Values,
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
    pub fn category(&self) -> ConstraintCategory {
        match self {
            ConstraintDescription::Abstract(_) => ConstraintCategory::Abstract,
            ConstraintDescription::Distinct(_) => ConstraintCategory::Distinct,
            ConstraintDescription::Independent(_) => ConstraintCategory::Independent,
            ConstraintDescription::Unique(_) => ConstraintCategory::Unique,
            ConstraintDescription::Cardinality(_) => ConstraintCategory::Cardinality,
            ConstraintDescription::Regex(_) => ConstraintCategory::Regex,
            ConstraintDescription::Range(_) => ConstraintCategory::Range,
            ConstraintDescription::Values(_) => ConstraintCategory::Values,
        }
    }

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

    pub fn inheritable(&self) -> bool {
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

    pub fn unchecked(&self) -> bool {
        match self {
            ConstraintDescription::Cardinality(cardinality) => cardinality == &AnnotationCardinality::unchecked(),
            _ => false,
        }
    }

    pub fn narrowed_correctly_by_same_type(&self, other: &ConstraintDescription) -> bool {
        self.narrowed_correctly_by(other, false)
    }

    pub fn narrowed_correctly_by_any_type(&self, other: &ConstraintDescription) -> bool {
        self.narrowed_correctly_by(other, true)
    }

    fn narrowed_correctly_by(&self, other: &ConstraintDescription, allow_different_description: bool) -> bool {
        let default = || if allow_different_description {
            true
        } else {
            unreachable!("Preceding filtering by ConstraintDescription is expected before this call")
        };
        match self {
            ConstraintDescription::Abstract(_) => true,
            ConstraintDescription::Distinct(_) => true,
            ConstraintDescription::Independent(_) => true,
            ConstraintDescription::Unique(_) => true,
            ConstraintDescription::Regex(regex) => with_constraint_description!(other, Regex, default(), |other_regex| regex.narrowed_correctly_by(other_regex)),
            ConstraintDescription::Cardinality(cardinality) => with_constraint_description!(other, Cardinality, default(), |other_cardinality| cardinality.narrowed_correctly_by(other_cardinality)),
            ConstraintDescription::Range(range) => with_constraint_description!(other, Range, default(), |other_range| range.narrowed_correctly_by(other_range)),
            ConstraintDescription::Values(values) => with_constraint_description!(other, Values, default(), |other_values| values.narrowed_correctly_by(other_values)),
        }
    }
}

pub trait Constraint<T>: Sized + Clone + Hash + PartialEq {
    fn description(&self) -> ConstraintDescription;

    fn source(&self) -> T;

    fn category(&self) -> ConstraintCategory {
        self.description().category()
    }

    fn validation_mode(&self) -> ConstraintValidationMode {
        self.description().validation_mode()
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct TypeConstraint<T: KindAPI<'static>> {
    description: ConstraintDescription,
    source: T,
}

impl<T: KindAPI<'static>> TypeConstraint<T> {
    pub fn new(description: ConstraintDescription, source: T) -> Self {
        Self { description, source }
    }
}

impl<T: KindAPI<'static>> Constraint<T> for TypeConstraint<T> {
    fn description(&self) -> ConstraintDescription {
        self.description.clone()
    }

    fn source(&self) -> T {
        self.source.clone()
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct CapabilityConstraint<CAP: Capability<'static>> {
    description: ConstraintDescription,
    source: CAP,
}

impl<CAP: Capability<'static>> CapabilityConstraint<CAP> {
    pub fn new(description: ConstraintDescription, source: CAP) -> Self {
        Self { description, source }
    }
}

impl<CAP: Capability<'static>> Constraint<CAP> for CapabilityConstraint<CAP> {
    fn description(&self) -> ConstraintDescription {
        self.description.clone()
    }

    fn source(&self) -> CAP {
        self.source.clone()
    }
}

// impl CapabilityConstraint<Owns<'static>> {
//
//     pub fn validate_single(&self, owner: &Object<'_>, attribute: &Attribute<'_>) -> Result<(), ConstraintError> {
//         match self.description() {
//             ConstraintDescription::Abstract(_) => validate_cardinality_owns(),
//             ConstraintDescription::Distinct(_) => validate_cardinality_owns(),
//             ConstraintDescription::Independent(_) => {},
//             ConstraintDescription::Unique(_) => validate_cardinality_owns(),
//             ConstraintDescription::Cardinality(cardinality) => validate_cardinality_owns(),
//             ConstraintDescription::Regex(regex) => validate_cardinality_owns(),
//             ConstraintDescription::Range(range) => validate_cardinality_owns(),
//             ConstraintDescription::Values(values) => validate_cardinality_owns(),
//         }
//         Ok(())
//     }
//
//     pub fn validate_all(&self, ...) -> Result<(), ConstraintError> {
//         match self.description() {
//             ConstraintDescription::Abstract(_) => validate_cardinality_owns(),
//             ConstraintDescription::Distinct(_) => validate_cardinality_owns(),
//             ConstraintDescription::Independent(_) => {},
//             ConstraintDescription::Unique(_) => validate_cardinality_owns(),
//             ConstraintDescription::Cardinality(cardinality) => validate_cardinality_owns(),
//             ConstraintDescription::Regex(regex) => validate_cardinality_owns(),
//             ConstraintDescription::Range(range) => validate_cardinality_owns(),
//             ConstraintDescription::Values(values) => validate_cardinality_owns(),
//         }
//         Ok(())
//     }
// }

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

macro_rules! filter_by_constraint_description_match {
    ($constraints_iter:expr, $pattern:pat) => {
        $constraints_iter.filter(|(constraint, sources)| {
            let description = constraint.description();
            matches!(description, $pattern)
        })
    };
}
pub use filter_by_constraint_description_match;

pub fn get_cardinality_constraints<'a, CAP: Capability<'a>>(
    constraints: impl IntoIterator<Item = (&CapabilityConstraint<CAP>, HashSet<CAP>)>,
) -> HashMap<CapabilityConstraint<CAP>, HashSet<CAP>> {
    filter_by_constraint_description_match!(constraints.into_iter(), ConstraintDescription::Cardinality(_)).collect()
}

pub(crate) fn get_cardinality_constraint_opt<'a, CAP: Capability<'a>>(
    capability: CAP,
    constraints: impl IntoIterator<Item = (&CapabilityConstraint<CAP>, HashSet<CAP>)>,
) -> Option<CapabilityConstraint<CAP>> {
    filter_by_constraint_description_match!(constraints.into_iter(), ConstraintDescription::Cardinality(_))
        .filter_map(|(constraint, sources)| match sources.get(&capability) {
            Some(_) => Some(constraint.clone()),
            None => None,
        })
        .next()
}

pub fn get_cardinality_constraint<'a, CAP: Capability<'a>>(
    capability: CAP,
    constraints: impl IntoIterator<Item = (&CapabilityConstraint<CAP>, HashSet<CAP>)>,
) -> CapabilityConstraint<CAP> {
    get_cardinality_constraint_opt(capability, constraints).expect("Expected a cardinality constraint for each capability")
}

pub fn get_abstract_constraint<'a, C: Constraint, T: Hash + PartialEq>(
    source: T,
    constraints: impl IntoIterator<Item = (&C, HashSet<T>)>,
) -> Option<C> {
    let abstracts =
        filter_by_constraint_description_match!(constraints.into_iter(), ConstraintDescription::Abstract(_));
    debug_assert!(abstracts.is_empty() || abstracts.len() == 1, "Cannot have Abstract constraints hashed in different buckets");
    abstracts
        .into_iter()
        .filter_map(|(constraint, sources)| {
            match sources.get(&source) {
                Some(_) => Some(constraint.clone()),
                None => None,
            }
        })
        .next()
}

pub fn get_unique_constraint<'a, C: Constraint, T: Hash + PartialEq>(
    constraints: impl IntoIterator<Item = (&C, HashSet<T>)>,
) -> Option<(C, T)> {
    let uniques =
        filter_by_constraint_description_match!(constraints.into_iter(), ConstraintDescription::Unique(_));
    debug_assert_eq!(uniques.is_empty() || uniques.len() == 1, "Cannot have Unique constraints hashed in different buckets");

    if let Some((constraint, sources)) = uniques.into_iter().next() {
        debug_assert_eq!(sources.len(), 1, "Expected to have only 1 uniqueness source");
        let source = sources.into_iter().next().unwrap();
        Some((constraint.clone(), source))
    } else {
        None
    }
}

pub fn get_distinct_constraints<'a, CAP: Capability<'a>>(
    constraints: impl IntoIterator<Item = (&CapabilityConstraint<CAP>, HashSet<CAP>)>,
) -> HashMap<CapabilityConstraint<CAP>, HashSet<CAP>> {
    filter_by_constraint_description_match!(constraints.into_iter(), ConstraintDescription::Distinct(_)).collect()
}

pub fn get_independent_constraints<'a, T: TypeAPI<'a>>(
    constraints: impl IntoIterator<Item = (TypeConstraint<T>, HashSet<T>)>,
) -> HashMap<TypeConstraint<T>, HashSet<T>> {
    filter_by_constraint_description_match!(constraints.into_iter(), ConstraintDescription::Independent(_)).collect()
}

pub fn get_regex_constraints<'a, C: Constraint, T: Hash + PartialEq>(
    constraints: impl IntoIterator<Item = (&C, HashSet<T>)>,
) -> HashMap<C, HashSet<T>> {
    filter_by_constraint_description_match!(constraints.into_iter(), ConstraintDescription::Regex(_)).collect()
}

pub fn get_range_constraints<'a, C: Constraint, T: Hash + PartialEq>(
    constraints: impl IntoIterator<Item = (&C, HashSet<T>)>,
) -> HashMap<C, HashSet<T>> {
    filter_by_constraint_description_match!(constraints.into_iter(), ConstraintDescription::Range(_)).collect()
}

pub fn get_values_constraints<'a, C: Constraint, T: Hash + PartialEq>(
    constraints: impl IntoIterator<Item = (&C, HashSet<T>)>,
) -> HashMap<C, HashSet<T>> {
    filter_by_constraint_description_match!(constraints.into_iter(), ConstraintDescription::Values(_)).collect()
}

pub(crate) fn annotations_by_validation_modes<'a, A: Into<Annotation> + Clone + 'a>(
    annotations: impl IntoIterator<Item = A>,
) -> Result<HashMap<&'static ConstraintValidationMode, HashSet<Annotation>>, AnnotationError> {
    let mut map: HashMap<&ConstraintValidationMode, HashSet<Annotation>> = HashMap::new();

    for annotation in annotations.into_iter() {
        let annotation = annotation.clone().into();
        let modes = constraint_validation_mode(annotation.category());

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
