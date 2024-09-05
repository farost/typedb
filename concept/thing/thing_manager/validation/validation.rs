/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use encoding::value::label::Label;
use encoding::value::value::Value;
use storage::snapshot::ReadableSnapshot;

use crate::{
    thing::{object::ObjectAPI, thing_manager::validation::DataValidationError},
    type_::{type_manager::TypeManager, Capability, TypeAPI},
};
use crate::thing::object::Object;
use crate::thing::relation::Relation;
use crate::thing::thing_manager::ThingManager;
use crate::type_::annotation::AnnotationCardinality;
use crate::type_::attribute_type::AttributeType;
use crate::type_::constraint::{CapabilityConstraint, Constraint, ConstraintDescription, TypeConstraint};
use crate::type_::OwnerAPI;
use crate::type_::owns::Owns;
use crate::type_::plays::Plays;
use crate::type_::relates::Relates;

pub(crate) fn get_label_or_data_err<'a>(
    snapshot: &impl ReadableSnapshot,
    type_manager: &TypeManager,
    type_: impl TypeAPI<'a>,
) -> Result<Label<'static>, DataValidationError> {
    type_
        .get_label_cloned(snapshot, type_manager)
        .map(|label| label.into_owned())
        .map_err(DataValidationError::ConceptRead)
}

pub(crate) struct DataValidation {}

impl DataValidation {
    pub(crate) fn validate_owns_instances_cardinality_constraint<'a>(
        snapshot: &impl ReadableSnapshot,
        type_manager: &TypeManager,
        constraint: &CapabilityConstraint<Owns<'static>>,
        owner: &Object<'a>,
        owns: Owns<'static>,
        count: u64,
    ) -> Result<(), DataValidationError> {
        constraint.validate_cardinality(count).map_err(|source| {
            let is_key = match owns.is_key(snapshot, type_manager) {
                Ok(is_key) => is_key,
                Err(err) => return DataValidationError::ConceptRead(err),
            };
            let owner = owner.clone().into_owned();
            if is_key {
                DataValidationError::KeyConstraintViolated { owner, owns, source }
            } else {
                DataValidationError::OwnsConstraintViolated { owner, owns, source }
            }
        })
    }

    pub(crate) fn validate_plays_instances_cardinality_constraint<'a>(
        _snapshot: &impl ReadableSnapshot,
        _type_manager: &TypeManager,
        constraint: &CapabilityConstraint<Plays<'static>>,
        player: &Object<'a>,
        plays: Plays<'static>,
        count: u64,
    ) -> Result<(), DataValidationError> {
        constraint.validate_cardinality(count).map_err(|source| {
            let player = player.clone().into_owned();
            DataValidationError::PlaysConstraintViolated { player, plays, source }
        })
    }

    pub(crate) fn validate_relates_instances_cardinality_constraint<'a>(
        _snapshot: &impl ReadableSnapshot,
        _type_manager: &TypeManager,
        constraint: &CapabilityConstraint<Relates<'static>>,
        relation: &Relation<'a>,
        relates: Relates<'static>,
        count: u64,
    ) -> Result<(), DataValidationError> {
        constraint.validate_cardinality(count).map_err(|source| {
            let relation = relation.clone().into_owned();
            DataValidationError::RelatesConstraintViolated { relation, relates, source }
        })
    }

    pub(crate) fn validate_attribute_regex_constraint(
        constraint: &TypeConstraint<AttributeType<'static>>,
        attribute_type: AttributeType<'static>,
        value: Value<'_>,
    ) -> Result<(), DataValidationError> {
        constraint.validate_regex(value).map_err(|source| {
            DataValidationError::AttributeTypeConstraintViolated { attribute_type: attribute_type.clone(), source }
        })
    }

    pub(crate) fn validate_attribute_range_constraint(
        constraint: &TypeConstraint<AttributeType<'static>>,
        attribute_type: AttributeType<'static>,
        value: Value<'_>,
    ) -> Result<(), DataValidationError> {
        constraint.validate_range(value).map_err(|source| {
            DataValidationError::AttributeTypeConstraintViolated { attribute_type: attribute_type.clone(), source }
        })
    }

    pub(crate) fn validate_attribute_values_constraint(
        constraint: &TypeConstraint<AttributeType<'static>>,
        attribute_type: AttributeType<'static>,
        value: Value<'_>,
    ) -> Result<(), DataValidationError> {
        constraint.validate_values(value).map_err(|source| {
            DataValidationError::AttributeTypeConstraintViolated { attribute_type: attribute_type.clone(), source }
        })
    }

    pub(crate) fn validate_owns_regex_constraint<'a>(
        constraint: &CapabilityConstraint<Owns<'static>>,
        object: &Object<'a>,
        value: Value<'_>,
    ) -> Result<(), DataValidationError> {
        constraint.validate_regex(value).map_err(|source| {
            DataValidationError::OwnsConstraintViolated { owner: object.as_reference().into_owned(), owns: constraint.source(), source }
        })
    }

    pub(crate) fn validate_owns_range_constraint<'a>(
        constraint: &CapabilityConstraint<Owns<'static>>,
        object: &Object<'a>,
        value: Value<'_>,
    ) -> Result<(), DataValidationError> {
        constraint.validate_range(value).map_err(|source| {
            DataValidationError::OwnsConstraintViolated { owner: object.as_reference().into_owned(), owns: constraint.source(), source }
        })
    }

    pub(crate) fn validate_owns_values_constraint<'a>(
        constraint: &CapabilityConstraint<Owns<'static>>,
        object: &Object<'a>,
        value: Value<'_>,
    ) -> Result<(), DataValidationError> {
        constraint.validate_values(value).map_err(|source| {
            DataValidationError::OwnsConstraintViolated { owner: object.as_reference().into_owned(), owns: constraint.source(), source }
        })
    }
}
