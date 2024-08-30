/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::collections::{HashMap, HashSet};

use itertools::Itertools;
use storage::snapshot::{ReadableSnapshot, WritableSnapshot};

use crate::{
    error::ConceptReadError,
    thing::{
        object::{Object, ObjectAPI},
        relation::Relation,
        thing_manager::{validation::DataValidationError, ThingManager},
    },
    type_::{
        annotation::AnnotationCardinality, attribute_type::AttributeType, owns::Owns, plays::Plays, relates::Relates,
        role_type::RoleType, Capability, OwnerAPI, PlayerAPI, TypeAPI,
    },
};

macro_rules! validate_capability_cardinality_constraint {
    ($func_name:ident, $capability_type:ident, $interface_type:ident, $object_instance:ident, $check_func:path) => {
        pub(crate) fn $func_name<'a>(
            snapshot: &impl ReadableSnapshot,
            thing_manager: &ThingManager,
            owner: &$object_instance<'a>,
            capabilities_to_check: HashSet<$capability_type<'static>>,
            counts: &HashMap<$interface_type<'static>, u64>,
        ) -> Result<(), DataValidationError> {
            let checked_capabilities: HashSet<$capability_type<'static>> = HashSet::new();

            for capability in capabilities_to_check {
                if checked_capabilities.contains(capability) {
                    continue;
                }

                let constraints = capability.get_constraints(snapshot, thing_manager.type_manager())
                let cardinality_constraints: HashMap<CapabilityConstraint<$capability_type<'static>>, HashSet<$capability_type<'static>::ObjectType>> =
                    filter_by_constraint_description_match!(constraints, ConstraintDescription::Cardinality(_));

                for (cardinality, sources) in cardinality_constraints {
                    for source in sources {
                        checked_capabilities.insert(source.clone());
                        if cardinality == AnnotationCardinality::unchecked() {
                            continue;
                        }

                        let count = source.get_specializing_transitive(snapshot, thing_manager.type_manager())?
                            .iter()
                            .chain(iter::once(source))
                            .map(|specializing| specializing.interface())
                            .unique()
                            .filter_map(|interface_type| counts.get(&interface_type))
                            .sum();
                        $check_func(snapshot, thing_manager, owner, capability.clone(), count)?; // TODO: Call for constraint check instead!
                    }
                }

                Ok(())
            }
        }
    };
}

macro_rules! collect_errors {
    ($vec:ident, $expr:expr, $wrap:expr) => {
        if let Err(e) = $expr {
            $vec.push($wrap(e));
        }
    };

    ($vec:ident, $expr:expr) => {
        if let Err(e) = $expr {
            $vec.push(e);
        }
    };
}

pub(crate) use collect_errors;

pub struct CommitTimeValidation {}

impl CommitTimeValidation {
    pub(crate) fn validate_object_has<'a>(
        snapshot: &impl WritableSnapshot,
        thing_manager: &ThingManager,
        object: Object<'a>,
        modified_owns: HashSet<Owns<'a>>,
        out_errors: &mut Vec<DataValidationError>,
    ) -> Result<(), ConceptReadError> {
        let has_counts = object.get_has_counts(snapshot, thing_manager)?;

        let cardinality_check = CommitTimeValidation::validate_owns_cardinality_constraint(
            snapshot,
            thing_manager,
            &object,
            modified_owns,
            &has_counts,
        );
        collect_errors!(out_errors, cardinality_check);

        Ok(())
    }

    pub(crate) fn validate_object_links<'a>(
        snapshot: &impl WritableSnapshot,
        thing_manager: &ThingManager,
        object: Object<'a>,
        modified_plays: HashSet<Plays<'a>>,
        out_errors: &mut Vec<DataValidationError>,
    ) -> Result<(), ConceptReadError> {
        let type_ = object.type_();
        let object_plays = type_.get_plays(snapshot, thing_manager.type_manager())?;
        let played_roles_counts = object.get_played_roles_counts(snapshot, thing_manager)?;

        for plays in object_plays.iter() {
            let cardinality_check = Self::validate_plays_cardinality_constraint(
                snapshot,
                thing_manager,
                &object,
                plays.clone().into_owned(),
                &played_roles_counts,
            );
            collect_errors!(out_errors, cardinality_check);
        }
        Ok(())
    }

    pub(crate) fn validate_relation_links<'a>(
        snapshot: &impl WritableSnapshot,
        thing_manager: &ThingManager,
        relation: Relation<'a>,
        modified_relates: HashSet<Relates<'a>>,
        out_errors: &mut Vec<DataValidationError>,
    ) -> Result<(), ConceptReadError> {
        let type_ = relation.type_();
        let relation_relates = type_.get_relates(snapshot, thing_manager.type_manager())?;
        let role_player_count = relation.get_player_counts(snapshot, thing_manager)?;

        for relates in relation_relates.iter() {
            let cardinality_check = Self::validate_relates_cardinality_constraint(
                snapshot,
                thing_manager,
                &relation,
                relates.clone().into_owned(),
                &role_player_count,
            );
            collect_errors!(out_errors, cardinality_check);
        }
        Ok(())
    }

    fn check_owns_cardinality<'a>(
        snapshot: &impl ReadableSnapshot,
        thing_manager: &ThingManager,
        owner: &Object<'a>,
        owns: Owns<'static>,
        count: u64,
    ) -> Result<(), DataValidationError> {
        let cardinality =
            owns.get_cardinalities(snapshot, thing_manager.type_manager()).map_err(DataValidationError::ConceptRead)?;
        let is_key: bool =
            owns.is_key(snapshot, thing_manager.type_manager()).map_err(DataValidationError::ConceptRead)?;
        if !cardinality.value_valid(count) {
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

    fn check_plays_cardinality<'a>(
        snapshot: &impl ReadableSnapshot,
        thing_manager: &ThingManager,
        player: &Object<'a>,
        plays: Plays<'static>,
        count: u64,
    ) -> Result<(), DataValidationError> {
        let cardinality =
            plays.get_cardinalities(snapshot, thing_manager.type_manager()).map_err(DataValidationError::ConceptRead)?;
        if !cardinality.value_valid(count) {
            let player = player.clone().into_owned();
            Err(DataValidationError::PlaysCardinalityViolated { player, plays, count, cardinality })
        } else {
            Ok(())
        }
    }

    fn check_relates_cardinality<'a>(
        snapshot: &impl ReadableSnapshot,
        thing_manager: &ThingManager,
        relation: &Relation<'a>,
        relates: Relates<'static>,
        count: u64,
    ) -> Result<(), DataValidationError> {
        let cardinality = relates
            .get_cardinalities(snapshot, thing_manager.type_manager())
            .map_err(DataValidationError::ConceptRead)?;
        if !cardinality.value_valid(count) {
            let relation = relation.clone().into_owned();
            Err(DataValidationError::RelatesCardinalityViolated { relation, relates, count, cardinality })
        } else {
            Ok(())
        }
    }

    validate_capability_cardinality_constraint!(
        validate_owns_cardinality_constraint,
        Owns,
        AttributeType,
        Object,
        Self::check_owns_cardinality
    );
    validate_capability_cardinality_constraint!(
        validate_plays_cardinality_constraint,
        Plays,
        RoleType,
        Object,
        Self::check_plays_cardinality
    );
    validate_capability_cardinality_constraint!(
        validate_relates_cardinality_constraint,
        Relates,
        RoleType,
        Relation,
        Self::check_relates_cardinality
    );
}
