/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::collections::HashSet;

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
    ($func_name:ident, $capability_type:ident, $object_instance:ident, $get_cardinality_constraints_func:ident, $get_interface_counts_func:ident, $check_func:path) => {
        pub(crate) fn $func_name<'a>(
            snapshot: &impl ReadableSnapshot,
            thing_manager: &ThingManager,
            object: $object_instance<'a>,
            interface_types_to_check: HashSet<$capability_type<'static>::InterfaceType>,
        ) -> Result<(), DataValidationError> {
            let mut cardinality_constraints: HashSet<CapabilityConstraint<$capability_type<'static>> = HashSet::new();
            let counts = object.$get_interface_counts_func(snapshot, thing_manager).map_err(DataValidationError::ConceptRead)?;

            for interface_type in interface_types_to_check {
                for constraint in object.type_().$get_cardinality_constraints_func(snapshot, thing_manager.type_manager(), interface_type.clone()).map_err(DataValidationError::ConceptRead)?.into_iter() {
                    cardinality_constraints.insert(constraint);
                }
            }

            for constraint in cardinality_constraints {
                let cardinality = constraint.description().unwrap_cardinality();
                if cardinality == AnnotationCardinality::unchecked() {
                    continue;
                }

                let source_interface_type = constraint.source().interface();
                let sub_interface_types = source_interface_type.get_subtypes_transitive(snapshot, thing_manager.type_manager())?;
                let count = TypeAPI::chain_types(source_interface_type, sub_interface_types)
                    .filter_map(|interface_type| counts.get(&interface_type))
                    .sum();
                $check_func(snapshot, thing_manager.type_manager(), &object, constraint.source(), cardinality, count)?;
            }

            Ok(())
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
use crate::thing::thing_manager::validation::validation::{check_owns_instances_cardinality, check_plays_instances_cardinality, check_relates_instances_cardinality};
use crate::type_::constraint::{CapabilityConstraint, ConstraintDescription};

pub struct CommitTimeValidation {}

impl CommitTimeValidation {
    pub(crate) fn validate_object_has<'a>(
        snapshot: &impl WritableSnapshot,
        thing_manager: &ThingManager,
        object: Object<'a>,
        modified_attribute_types: HashSet<AttributeType<'a>>,
        out_errors: &mut Vec<DataValidationError>,
    ) -> Result<(), ConceptReadError> {
        let cardinality_check = CommitTimeValidation::validate_owns_cardinality_constraint(
            snapshot,
            thing_manager,
            object,
            modified_attribute_types,
        );
        collect_errors!(out_errors, cardinality_check);
        Ok(())
    }

    pub(crate) fn validate_object_links<'a>(
        snapshot: &impl WritableSnapshot,
        thing_manager: &ThingManager,
        object: Object<'a>,
        modified_role_types: HashSet<RoleType<'a>>,
        out_errors: &mut Vec<DataValidationError>,
    ) -> Result<(), ConceptReadError> {
        let cardinality_check = Self::validate_plays_cardinality_constraint(
            snapshot,
            thing_manager,
            object,
            modified_role_types,
        );
        collect_errors!(out_errors, cardinality_check);
        Ok(())
    }

    pub(crate) fn validate_relation_links<'a>(
        snapshot: &impl WritableSnapshot,
        thing_manager: &ThingManager,
        relation: Relation<'a>,
        modified_role_types: HashSet<RoleType<'a>>,
        out_errors: &mut Vec<DataValidationError>,
    ) -> Result<(), ConceptReadError> {
        let cardinality_check = Self::validate_relates_cardinality_constraint(
            snapshot,
            thing_manager,
            relation,
            modified_role_types,
        );
        collect_errors!(out_errors, cardinality_check);
        Ok(())
    }

    validate_capability_cardinality_constraint!(
        validate_owns_cardinality_constraint,
        Owns,
        Object,
        get_type_owns_constraints_cardinality,
        get_has_counts,
        check_owns_instances_cardinality
    );
    validate_capability_cardinality_constraint!(
        validate_plays_cardinality_constraint,
        Plays,
        Object,
        get_type_plays_constraints_cardinality,
        get_played_roles_counts,
        check_plays_instances_cardinality
    );
    validate_capability_cardinality_constraint!(
        validate_relates_cardinality_constraint,
        Relates,
        Relation,
        get_type_relates_constraints_cardinality,
        get_player_counts,
        check_relates_instances_cardinality
    );
}
