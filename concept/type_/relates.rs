/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::collections::{HashMap, HashSet};

use encoding::{
    graph::type_::{edge::TypeEdgeEncoding, CapabilityKind},
    layout::prefix::Prefix,
};
use primitive::maybe_owns::MaybeOwns;
use storage::snapshot::{ReadableSnapshot, WritableSnapshot};

use crate::{
    error::{ConceptReadError, ConceptWriteError},
    thing::thing_manager::ThingManager,
    type_::{
        annotation::{
            Annotation, AnnotationCardinality, AnnotationCategory, AnnotationDistinct, AnnotationError, DefaultFrom,
        },
        plays::Plays,
        relation_type::RelationType,
        role_type::RoleType,
        type_manager::TypeManager,
        Capability, Ordering, TypeAPI,
    },
};
use crate::type_::constraint::CapabilityConstraint;
use crate::type_::owns::Owns;

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Relates<'a> {
    relation: RelationType<'a>,
    role: RoleType<'a>,
}

impl<'a> Relates<'a> {
    pub const DEFAULT_UNORDERED_CARDINALITY: AnnotationCardinality = AnnotationCardinality::new(0, Some(1));
    pub const DEFAULT_ORDERED_CARDINALITY: AnnotationCardinality = AnnotationCardinality::new(0, None);

    pub fn relation(&self) -> RelationType<'a> {
        self.relation.clone()
    }

    pub fn role(&self) -> RoleType<'a> {
        self.role.clone()
    }

    // TODO: It may be risky to use methods purely on constraints, so maybe we need to remove them and use only is_type_relates_distinct instead!
    pub fn is_distinct(
        &self,
        snapshot: &impl ReadableSnapshot,
        type_manager: &TypeManager,
    ) -> Result<bool, ConceptReadError> {
        type_manager.get_is_distinct(snapshot, self.clone().into_owned())
    }

    pub fn set_override(
        &self,
        snapshot: &mut impl WritableSnapshot,
        type_manager: &TypeManager,
        thing_manager: &ThingManager,
        overridden: Relates<'static>,
    ) -> Result<(), ConceptWriteError> {
        type_manager.set_relates_override(snapshot, thing_manager, self.clone().into_owned(), overridden)
    }

    pub fn unset_override(
        &self,
        snapshot: &mut impl WritableSnapshot,
        type_manager: &TypeManager,
        thing_manager: &ThingManager,
    ) -> Result<(), ConceptWriteError> {
        type_manager.unset_relates_override(snapshot, thing_manager, self.clone().into_owned())
    }

    pub fn set_annotation(
        &self,
        snapshot: &mut impl WritableSnapshot,
        type_manager: &TypeManager,
        thing_manager: &ThingManager,
        annotation: RelatesAnnotation,
    ) -> Result<(), ConceptWriteError> {
        match annotation {
            RelatesAnnotation::Distinct(_) => {
                type_manager.set_relates_annotation_distinct(snapshot, thing_manager, self.clone().into_owned())?
            }
            RelatesAnnotation::Cardinality(cardinality) => type_manager.set_relates_annotation_cardinality(
                snapshot,
                thing_manager,
                self.clone().into_owned(),
                cardinality,
            )?,
        };
        Ok(())
    }

    pub fn unset_annotation(
        &self,
        snapshot: &mut impl WritableSnapshot,
        type_manager: &TypeManager,
        thing_manager: &ThingManager,
        annotation_category: AnnotationCategory,
    ) -> Result<(), ConceptWriteError> {
        let relates_annotation = RelatesAnnotation::try_getting_default(annotation_category)
            .map_err(|source| ConceptWriteError::Annotation { source })?;
        match relates_annotation {
            RelatesAnnotation::Distinct(_) => {
                type_manager.unset_capability_annotation_distinct(snapshot, self.clone().into_owned())?
            }
            RelatesAnnotation::Cardinality(_) => {
                type_manager.unset_relates_annotation_cardinality(snapshot, thing_manager, self.clone().into_owned())?
            }
        }
        Ok(())
    }

    pub fn get_default_cardinality(role_ordering: Ordering) -> AnnotationCardinality {
        match role_ordering {
            Ordering::Unordered => Self::DEFAULT_UNORDERED_CARDINALITY,
            Ordering::Ordered => Self::DEFAULT_ORDERED_CARDINALITY,
        }
    }

    pub fn get_default_distinct(role_ordering: Ordering) -> Option<AnnotationDistinct> {
        match role_ordering {
            Ordering::Ordered => None,
            Ordering::Unordered => Some(AnnotationDistinct)
        }
    }

    pub(crate) fn into_owned(self) -> Relates<'static> {
        Relates { relation: self.relation.into_owned(), role: self.role.into_owned() }
    }
}

impl<'a> TypeEdgeEncoding<'a> for Relates<'a> {
    const CANONICAL_PREFIX: Prefix = Prefix::EdgeRelates;
    const REVERSE_PREFIX: Prefix = Prefix::EdgeRelatesReverse;
    type From = RelationType<'a>;
    type To = RoleType<'a>;

    fn from_vertices(from: RelationType<'a>, to: RoleType<'a>) -> Self {
        Self::new(from, to)
    }

    fn canonical_from(&self) -> Self::From {
        self.relation()
    }

    fn canonical_to(&self) -> Self::To {
        self.role()
    }
}

impl<'a> Capability<'a> for Relates<'a> {
    type AnnotationType = RelatesAnnotation;
    type ObjectType = RelationType<'a>;
    type InterfaceType = RoleType<'a>;
    const KIND: CapabilityKind = CapabilityKind::Relates;

    fn new(relation: RelationType<'a>, role: RoleType<'a>) -> Self {
        Relates { relation, role }
    }

    fn object(&self) -> RelationType<'a> {
        self.relation.clone()
    }

    fn interface(&self) -> RoleType<'a> {
        self.role.clone()
    }

    // fn get_specializes<'this>(
    //     &'this self,
    //     snapshot: &impl ReadableSnapshot,
    //     type_manager: &'this TypeManager,
    // ) -> Result<MaybeOwns<'this, Option<Relates<'static>>>, ConceptReadError> {
    //     type_manager.get_relates_specializes(snapshot, self.clone().into_owned())
    // }
    //
    // fn get_specializes_transitive<'this>(
    //     &'this self,
    //     snapshot: &impl ReadableSnapshot,
    //     type_manager: &'this TypeManager,
    // ) -> Result<MaybeOwns<'this, Vec<Relates<'static>>>, ConceptReadError> {
    //     type_manager.get_relates_specializes_transitive(snapshot, self.clone().into_owned())
    // }

    fn get_hides<'this>(
        &'this self,
        snapshot: &impl ReadableSnapshot,
        type_manager: &'this TypeManager,
    ) -> Result<MaybeOwns<'this, Option<Relates<'static>>>, ConceptReadError> {
        type_manager.get_relates_hides(snapshot, self.clone().into_owned())
    }

    // fn get_specializing<'this>(
    //     &'this self,
    //     snapshot: &impl ReadableSnapshot,
    //     type_manager: &'this TypeManager,
    // ) -> Result<MaybeOwns<'this, HashSet<Relates<'static>>>, ConceptReadError> {
    //     type_manager.get_relates_specializing(snapshot, self.clone().into_owned())
    // }
    //
    // fn get_specializing_transitive<'this>(
    //     &'this self,
    //     snapshot: &impl ReadableSnapshot,
    //     type_manager: &'this TypeManager,
    // ) -> Result<MaybeOwns<'this, Vec<Relates<'static>>>, ConceptReadError> {
    //     type_manager.get_relates_specializing_transitive(snapshot, self.clone().into_owned())
    // }

    fn get_annotations_declared<'m>(
        &self,
        snapshot: &impl ReadableSnapshot,
        type_manager: &'m TypeManager,
    ) -> Result<MaybeOwns<'m, HashSet<RelatesAnnotation>>, ConceptReadError> {
        type_manager.get_relates_annotations_declared(snapshot, self.clone().into_owned())
    }

    fn get_constraints<'m>(
        &self,
        snapshot: &impl ReadableSnapshot,
        type_manager: &'m TypeManager,
    ) -> Result<MaybeOwns<'m, HashSet<CapabilityConstraint<Relates<'static>>>>, ConceptReadError> {
        type_manager.get_relates_constraints(snapshot, self.clone().into_owned())
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq, Hash)]
pub enum RelatesAnnotation {
    Distinct(AnnotationDistinct),
    Cardinality(AnnotationCardinality),
}

impl TryFrom<Annotation> for RelatesAnnotation {
    type Error = AnnotationError;

    fn try_from(annotation: Annotation) -> Result<RelatesAnnotation, AnnotationError> {
        match annotation {
            Annotation::Distinct(annotation) => Ok(RelatesAnnotation::Distinct(annotation)),
            Annotation::Cardinality(annotation) => Ok(RelatesAnnotation::Cardinality(annotation)),

            | Annotation::Abstract(_)
            | Annotation::Independent(_)
            | Annotation::Unique(_)
            | Annotation::Key(_)
            | Annotation::Regex(_)
            | Annotation::Cascade(_)
            | Annotation::Range(_)
            | Annotation::Values(_) => Err(AnnotationError::UnsupportedAnnotationForRelates(annotation.category())),
        }
    }
}

impl Into<Annotation> for RelatesAnnotation {
    fn into(self) -> Annotation {
        match self {
            RelatesAnnotation::Distinct(annotation) => Annotation::Distinct(annotation),
            RelatesAnnotation::Cardinality(annotation) => Annotation::Cardinality(annotation),
        }
    }
}
