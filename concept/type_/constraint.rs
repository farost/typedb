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
use encoding::value::value::Value;
use encoding::value::ValueEncodable;

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

macro_rules! unwrap_constraint_description_methods {
    ($(
        fn $method_name:ident() -> $return_type:ident = $target_enum:ident;
    )*) => {
        $(
            pub(crate) fn $method_name(self) -> Result<$return_type>, ConceptReadError> {
                with_constraint_description!(self, $target_enum, || Err(ConceptReadError::Constraint { source: ConstraintError::CannotUnwrapConstraint(stringify!($target_enum)) }), |constraint| Ok(constraint))
            }
        )*
    }
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
    pub(crate) fn from_annotation(annotation: Annotation) -> &'static [Self] {
        match annotation {
            Annotation::Abstract(annotation) => &[ConstraintDescription::Abstract(annotation)],
            Annotation::Distinct(annotation) => &[ConstraintDescription::Distinct(annotation)],
            Annotation::Independent(annotation) => &[ConstraintDescription::Independent(annotation)],
            Annotation::Unique(annotation) => &[ConstraintDescription::Unique(annotation)],
            Annotation::Cardinality(annotation) => &[ConstraintDescription::Cardinality(annotation)],
            Annotation::Regex(annotation) => &[ConstraintDescription::Regex(annotation)],
            Annotation::Range(annotation) => &[ConstraintDescription::Range(annotation)],
            Annotation::Values(annotation) => &[ConstraintDescription::Values(annotation)],

            Annotation::Key(_) => &[ConstraintDescription::Unique(AnnotationKey::UNIQUE), ConstraintDescription::Cardinality(AnnotationKey::CARDINALITY)],

            Annotation::Cascade(annotation) => &[],
        }
    }

    pub(crate) fn category(&self) -> ConstraintCategory {
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

    pub(crate) fn validation_mode(&self) -> ConstraintValidationMode {
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

    pub(crate) fn unchecked(&self) -> bool {
        match self {
            ConstraintDescription::Cardinality(cardinality) => cardinality == &AnnotationCardinality::unchecked(),
            _ => false,
        }
    }

    pub(crate) fn narrowed_correctly_by_same_type(&self, other: &ConstraintDescription) -> bool {
        self.narrowed_correctly_by(other, false)
    }

    pub(crate) fn narrowed_correctly_by_any_type(&self, other: &ConstraintDescription) -> bool {
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

    unwrap_constraint_description_methods! {
        fn unwrap_abstract() -> AnnotationAbstract = Abstract;
        fn unwrap_distinct() -> AnnotationDistinct = Distinct;
        fn unwrap_independent() -> AnnotationIndependent = Independent;
        fn unwrap_unique() -> AnnotationUnique = Unique;
        fn unwrap_regex() -> AnnotationRegex = Regex;
        fn unwrap_cardinality() -> AnnotationCardinality = Cardinality;
        fn unwrap_range() -> AnnotationRange = Range;
        fn unwrap_values() -> AnnotationValues = Values;
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

    fn validate_cardinality(&self, count: u64) -> Result<(), ConstraintError> {
        let cardinality = self.description().unwrap_cardinality()?;
        match cardinality.value_valid(count) {
            true => Ok(()),
            false => Err(ConstraintError::ViolatedCardinality { cardinality, count }),
        }
    }

    fn validate_regex(&self, value: Value<'_>) -> Result<(), ConstraintError> {
        match &value {
            Value::String(string_value) => {
                let regex = self.description().unwrap_regex()?;
                match regex.value_valid(string_value) {
                    true => Ok(()),
                    false => Err(ConstraintError::ViolatedRegex { regex, value: value.into_owned() }),
                }
            }
            _ => Err(ConstraintError::CorruptConstraintIsNotApplicableToValue {
                description: self.description(),
                value: value.into_owned(),
            })
        }
    }

    fn validate_range(&self, value: Value<'_>) -> Result<(), ConstraintError> {
        let range = self.description().unwrap_range()?;
        match range.value_valid(value.as_reference()) {
            true => Ok(()),
            false => Err(ConstraintError::ViolatedRange { range, value: value.into_owned() }),
        }
    }

    fn validate_values(&self, value: Value<'_>) -> Result<(), ConstraintError> {
        let values = self.description().unwrap_values()?;
        match values.value_valid(value.as_reference()) {
            true => Ok(()),
            false => Err(ConstraintError::ViolatedValues { values, value: value.into_owned() }),
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct TypeConstraint<T: KindAPI<'static>> {
    description: ConstraintDescription,
    source: T,
}

impl<T: KindAPI<'static>> TypeConstraint<T> {
    pub(crate) fn new(description: ConstraintDescription, source: T) -> Self {
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
    pub(crate) fn new(description: ConstraintDescription, source: CAP) -> Self {
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
        $constraints_iter.filter(|constraint| {
            let description = constraint.description();
            matches!(description, $pattern)
        })
    };
}
pub use filter_by_constraint_description_match;

macro_rules! filter_by_constraint_category {
    ($constraints_iter:expr, $constraint_category:ident) => {
        $constraints_iter.filter(|constraint| constraint.category() == ConstraintCategory::$constraint_category)
    };
}
pub use filter_by_constraint_category;
use crate::thing::thing_manager::validation::DataValidationError;
use crate::thing::thing_manager::validation::validation::get_label_or_data_err;

pub(crate) fn get_cardinality_constraints<'a, C: Constraint<T>, T: Hash + PartialEq>(
    constraints: impl IntoIterator<Item = &C>,
) -> HashSet<C> {
    filter_by_constraint_category!(constraints.into_iter(), Cardinality).collect()
}

pub(crate) fn get_cardinality_constraint_opt<'a, C: Constraint<T>, T: Hash + PartialEq>(
    source: T,
    constraints: impl IntoIterator<Item = &C>,
) -> Option<C> {
    filter_by_constraint_category!(constraints.into_iter(), Cardinality)
        .filter_map(|constraint| match &constraint.source() == &source {
            true => Some(constraint.clone()),
            false => None,
        })
        .next()
}

pub(crate) fn get_cardinality_constraint<'a, CAP: Capability<'a>>(
    capability: CAP,
    constraints: impl IntoIterator<Item = &CapabilityConstraint<CAP>>,
) -> CapabilityConstraint<CAP> {
    get_cardinality_constraint_opt(capability, constraints).expect("Expected a cardinality constraint for each capability")
}

pub(crate) fn get_abstract_constraints<'a, C: Constraint<T>, T: Hash + PartialEq>(
    constraints: impl IntoIterator<Item = &C>,
) -> HashSet<C> {
    filter_by_constraint_category!(constraints.into_iter(), Abstract).collect()
}

pub(crate) fn get_abstract_constraint<'a, C: Constraint<T>, T: Hash + PartialEq>(
    source: T,
    constraints: impl IntoIterator<Item = &C>,
) -> Option<C> {
    let abstracts = filter_by_constraint_category!(constraints.into_iter(), Abstract);
    debug_assert!(abstracts.is_empty() || abstracts.len() == 1, "Cannot have Abstract constraints hashed in different buckets");
    abstracts
        .filter(|constraint| {
            debug_assert_eq!(constraint.source(), source, "Expected not to inherit Abstract constraints");
            match &constraint.source() == &source {
                true => Some(constraint.clone()),
                false => None,
            }
        })
        .next()
}

pub(crate) fn get_unique_constraints<'a, C: Constraint<T>, T: Hash + PartialEq>(
    constraints: impl IntoIterator<Item = &C>,
) -> HashSet<C> {
    filter_by_constraint_category!(constraints.into_iter(), Unique).collect()
}

pub(crate) fn get_unique_constraint<'a, C: Constraint<T>, T: Hash + PartialEq>(
    constraints: impl IntoIterator<Item = &C>,
) -> Option<C> {
    let uniques = filter_by_constraint_category!(constraints.into_iter(), Unique);
    debug_assert_eq!(uniques.is_empty() || uniques.len() == 1, "Expected to inherit only one unique constraint from its root source");

    if let Some(constraint) = uniques.into_iter().next() {
        Some(constraint.clone())
    } else {
        None
    }
}

pub(crate) fn get_distinct_constraints<'a, C: Constraint<T>, T: Hash + PartialEq>(
    constraints: impl IntoIterator<Item = &C>,
) -> HashSet<C> {
    filter_by_constraint_category!(constraints.into_iter(), Distinct).collect()
}

pub(crate) fn get_independent_constraints<'a, C: Constraint<T>, T: Hash + PartialEq>(
    constraints: impl IntoIterator<Item = &C>,
) -> HashSet<C> {
    filter_by_constraint_category!(constraints.into_iter(), Independent).collect()
}

pub(crate) fn get_regex_constraints<'a, C: Constraint<T>, T: Hash + PartialEq>(
    constraints: impl IntoIterator<Item = &C>,
) -> HashSet<C> {
    filter_by_constraint_category!(constraints.into_iter(), Regex).collect()
}

pub(crate) fn get_range_constraints<'a, C: Constraint<T>, T: Hash + PartialEq>(
    constraints: impl IntoIterator<Item = &C>,
) -> HashSet<C> {
    filter_by_constraint_category!(constraints.into_iter(), Range).collect()
}

pub(crate) fn get_values_constraints<'a, C: Constraint<T>, T: Hash + PartialEq>(
    constraints: impl IntoIterator<Item = &C>,
) -> HashSet<C> {
    filter_by_constraint_category!(constraints.into_iter(), Values).collect()
}

// TODO: Use constraints!
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

// TODO: Use constraints!
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

#[derive(Debug, Clone)]
pub enum ConstraintError {
    CannotUnwrapConstraint(String),
    Violated(ConstraintDescription),
    CorruptConstraintIsNotApplicableToValue { description: ConstraintDescription, value: Value<'static>, },
    ViolatedCardinality { cardinality: AnnotationCardinality, count: u64 },
    ViolatedRegex { regex: AnnotationRegex, value: Value<'static> },
    ViolatedRange { range: AnnotationRange, value: Value<'static> },
    ViolatedValues { values: AnnotationValues, value: Value<'static> },
}

impl fmt::Display for ConstraintError {
    fn fmt(&self, _: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl Error for ConstraintError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::CannotUnwrapConstraint(_) => None,
            Self::Violated(_) => None,
            Self::CorruptConstraintIsNotApplicableToValue { .. } => None,
            Self::ViolatedCardinality { .. } => None,
            Self::ViolatedRegex { .. } => None,
            Self::ViolatedRange { .. } => None,
            Self::ViolatedValues { .. } => None,
        }
    }
}
