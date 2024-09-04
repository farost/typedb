/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use encoding::value::label::Label;
use storage::snapshot::ReadableSnapshot;

use crate::{
    thing::{object::ObjectAPI, thing_manager::validation::DataValidationError},
    type_::{type_manager::TypeManager, Capability, TypeAPI},
};
use crate::thing::object::Object;
use crate::thing::relation::Relation;
use crate::thing::thing_manager::ThingManager;
use crate::type_::annotation::AnnotationCardinality;
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

pub(crate) fn check_owns_instances_cardinality<'a>(
    snapshot: &impl ReadableSnapshot,
    type_manager: &TypeManager,
    owner: &Object<'a>,
    owns: Owns<'static>,
    cardinality: AnnotationCardinality,
    count: u64,
) -> Result<(), DataValidationError> {
    if !cardinality.value_valid(count) {
        let is_key =
            owns.is_key(snapshot, type_manager).map_err(DataValidationError::ConceptRead)?;
        let owner = owner.clone().into_owned();
        if is_key {
            Err(DataValidationError::KeyCardinalityViolated { owner, owns, count })
        } else {
            Err(DataValidationError::OwnsCardinalityViolated { owner, owns, count, cardinality })
        }
    } else {
        Ok(())
    }
}

pub(crate) fn check_plays_instances_cardinality<'a>(
    _snapshot: &impl ReadableSnapshot,
    _type_manager: &TypeManager,
    player: &Object<'a>,
    plays: Plays<'static>,
    cardinality: AnnotationCardinality,
    count: u64,
) -> Result<(), DataValidationError> {
    if !cardinality.value_valid(count) {
        let player = player.clone().into_owned();
        Err(DataValidationError::PlaysCardinalityViolated { player, plays, count, cardinality })
    } else {
        Ok(())
    }
}

pub(crate) fn check_relates_instances_cardinality<'a>(
    _snapshot: &impl ReadableSnapshot,
    _type_manager: &TypeManager,
    relation: &Relation<'a>,
    relates: Relates<'static>,
    cardinality: AnnotationCardinality,
    count: u64,
) -> Result<(), DataValidationError> {
    if !cardinality.value_valid(count) {
        let relation = relation.clone().into_owned();
        Err(DataValidationError::RelatesCardinalityViolated { relation, relates, count, cardinality })
    } else {
        Ok(())
    }
}
