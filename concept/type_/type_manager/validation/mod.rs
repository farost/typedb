/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at https://mozilla.org/MPL/2.0/.
 */

use std::{error::Error, fmt};

use encoding::{
    graph::type_::{CapabilityKind, Kind},
    value::{label::Label, value_type::ValueType},
};

use crate::{
    error::ConceptReadError,
    type_::{
        annotation::{
            Annotation, AnnotationCardinality, AnnotationCategory, AnnotationRange, AnnotationRegex, AnnotationValues,
        },
        attribute_type::AttributeType,
        object_type::ObjectType,
        relation_type::RelationType,
        role_type::RoleType,
        Ordering,
    },
};
use crate::thing::thing_manager::validation::DataValidationError;
use crate::type_::constraint::ConstraintDescription;
use crate::type_::relates::Relates;

pub(crate) mod commit_time_validation;
pub(crate) mod operation_time_validation;
pub(crate) mod validation;

#[derive(Debug, Clone)]
pub enum SchemaValidationError {
    // TODO: Should probably send types themselves instead of labels here... Not sure how we are going to parse errors!
    ConceptRead(ConceptReadError),
    LabelShouldBeUnique {
        label: Label<'static>,
        existing_kind: Kind,
    },
    StructNameShouldBeUnique(String),
    StructShouldHaveAtLeastOneField(String),
    StructCannotBeDeletedAsItsUsedAsValueTypeForAttributeTypes(String, usize),
    StructCannotBeDeletedAsItsUsedAsValueTypeForStructs(String, usize),
    RoleNameShouldBeUniqueForRelationTypeHierarchy(Label<'static>, Label<'static>),
    CycleFoundInTypeHierarchy(Label<'static>, Label<'static>),
    ChangingAttributeTypeSupertypeWillLeadToConflictingValueTypes(Label<'static>, Option<ValueType>, ValueType),
    CannotUnsetAbstractnessOfAttributeTypeAsItHasSubtypes(Label<'static>),
    CannotDeleteTypeWithExistingSubtypes(Label<'static>),
    CannotUnsetCapabilityWithExistingOverridingCapabilities(
        CapabilityKind,
        Label<'static>,
        Label<'static>,
        Label<'static>,
        Label<'static>,
    ),
    RelatesNotInherited(RelationType<'static>, RoleType<'static>),
    OwnsNotInherited(ObjectType<'static>, AttributeType<'static>),
    PlaysNotInherited(ObjectType<'static>, RoleType<'static>),
    OverriddenCapabilityCannotBeRedeclared(CapabilityKind, Label<'static>, Label<'static>),
    HiddenCapabilityInterfaceIsNotSupertype(CapabilityKind, Label<'static>, Label<'static>, Label<'static>),
    AttributeTypeSupertypeIsNotAbstract(Label<'static>),
    AbstractTypesSupertypeHasToBeAbstract(Label<'static>, Label<'static>),
    CannotUnsetAbstractnessAsItHasDeclaredCapabilityOfAbstractInterface(CapabilityKind, Label<'static>, Label<'static>),
    CannotUnsetAbstractnessAsItHasInheritedCapabilityOfAbstractInterface(
        CapabilityKind,
        Label<'static>,
        Label<'static>,
    ),
    CannotUnsetRelatesAbstractnessAsItHasspecialisingRelates(Relates<'static>),
    OrderingDoesNotMatchWithSupertype(Label<'static>, Label<'static>, Ordering, Ordering),
    OrderingDoesNotMatchWithCapabilityOfSubtypeInterface(Label<'static>, Label<'static>, Label<'static>, Ordering, Ordering),
    CannotChangeSupertypeAsCapabilityOverrideIsImplicitlyLost(
        CapabilityKind,
        Label<'static>,
        Option<Label<'static>>,
        Label<'static>,
        Label<'static>,
        Label<'static>,
        Label<'static>,
    ),
    CannotChangeSupertypeAsOwnsOverrideIsImplicitlyLost(Label<'static>, Option<Label<'static>>, Label<'static>),
    CannotChangeSupertypeAsPlaysOverrideIsImplicitlyLost(Label<'static>, Option<Label<'static>>, Label<'static>),
    CannotChangeSupertypeAsCapabilityIsOverriddenInTheNewSupertype(
        CapabilityKind,
        Label<'static>,
        Label<'static>,
        Label<'static>,
    ),
    HiddenRelatesIsNotInheritedByRelationType(Label<'static>, Label<'static>),
    HiddenOwnsIsNotInheritedByObjectType(Label<'static>, Label<'static>),
    HiddenPlaysIsNotInheritedByObjectType(Label<'static>, Label<'static>),
    CannotSetOwnsBecauseItIsAlreadySetWithDifferentOrdering(Label<'static>, Label<'static>, Ordering),
    InvalidOrderingForDistinctConstraint(Label<'static>),
    AttributeTypeWithoutValueTypeShouldBeAbstract(Label<'static>),
    ValueTypeIsNotCompatibleWithRegexAnnotation(Label<'static>, Option<ValueType>),
    ValueTypeIsNotCompatibleWithRangeAnnotation(Label<'static>, Option<ValueType>),
    ValueTypeIsNotCompatibleWithValuesAnnotation(Label<'static>, Option<ValueType>),
    ValueTypeIsNotKeyableForKeyAnnotation(Label<'static>, Label<'static>, Option<ValueType>),
    ValueTypeIsNotKeyableForUniqueAnnotation(Label<'static>, Label<'static>, Option<ValueType>),
    CannotSetAnnotationToInterfaceBecauseItDoesNotNarrowItsCapabilityConstraint(Label<'static>, ConstraintDescription, ConstraintDescription),
    CannotSetAnnotationToCapabilityBecauseItDoesNotNarrowItsInterfaceConstraint(
        Label<'static>,
        Label<'static>,
        ConstraintDescription,
        ConstraintDescription,
    ),
    InvalidCardinalityArguments(AnnotationCardinality),
    InvalidRegexArguments(AnnotationRegex),
    InvalidRangeArgumentsForValueType(AnnotationRange, Option<ValueType>),
    InvalidValuesArgumentsForValueType(AnnotationValues, Option<ValueType>),
    KeyDoesNotNarrowInheritedCardinality(
        Label<'static>,
        Label<'static>,
        Label<'static>,
        Label<'static>,
        ConstraintDescription,
    ),
    CardinalityDoesNotNarrowInheritedCardinality(
        CapabilityKind,
        Label<'static>,
        Label<'static>,
        Label<'static>,
        Label<'static>,
        ConstraintDescription,
        ConstraintDescription,
    ),
    SummarizedCardinalityOfCapabilitiesOverridingSingleCapabilityOverflowsConstraint(
        CapabilityKind,
        Label<'static>,
        Label<'static>,
        Option<Label<'static>>,
        AnnotationCardinality,
        AnnotationCardinality,
    ),
    RegexShouldNarrowInheritedRegex(Label<'static>, Label<'static>, ConstraintDescription, ConstraintDescription),
    RangeShouldNarrowInheritedRange(Label<'static>, Label<'static>, ConstraintDescription, ConstraintDescription),
    ValuesShouldNarrowInheritedValues(Label<'static>, Label<'static>, ConstraintDescription, ConstraintDescription),
    RegexShouldNarrowInheritedCapabilityRegex(
        Label<'static>,
        Label<'static>,
        Label<'static>,
        Label<'static>,
        ConstraintDescription,
        ConstraintDescription,
    ),
    RangeShouldNarrowInheritedCapabilityRange(
        Label<'static>,
        Label<'static>,
        Label<'static>,
        Label<'static>,
        ConstraintDescription,
        ConstraintDescription,
    ),
    ValuesShouldNarrowInheritedCapabilityValues(
        Label<'static>,
        Label<'static>,
        Label<'static>,
        Label<'static>,
        ConstraintDescription,
        ConstraintDescription,
    ),
    CannotUnsetInheritedOwns(Label<'static>, Label<'static>),
    CannotUnsetInheritedPlays(Label<'static>, Label<'static>),
    CannotUnsetInheritedAnnotation(AnnotationCategory, Label<'static>),
    CannotUnsetInheritedEdgeAnnotation(AnnotationCategory, Label<'static>, Label<'static>),
    CannotUnsetInheritedValueType(ValueType, Label<'static>),
    ValueTypeNotCompatibleWithInheritedValueType(Label<'static>, Label<'static>, ValueType, ValueType),
    CannotRedeclareInheritedValueTypeWithoutspecialisation(Label<'static>, Label<'static>, ValueType, ValueType),
    DeclaredAnnotationIsNotCompatibleWithInheritedAnnotation(AnnotationCategory, AnnotationCategory, Label<'static>),
    DeclaredCapabilityAnnotationIsNotCompatibleWithInheritedAnnotation(
        AnnotationCategory,
        AnnotationCategory,
        Label<'static>,
        Label<'static>,
    ),
    AnnotationIsNotCompatibleWithDeclaredAnnotation(AnnotationCategory, AnnotationCategory, Label<'static>),
    RelationTypeMustRelateAtLeastOneRole(Label<'static>),
    CannotRedeclareInheritedCapabilityWithoutspecialisationWithOverride(
        CapabilityKind,
        Label<'static>,
        Label<'static>,
        Label<'static>,
    ),
    CannotRedeclareInheritedAnnotationWithoutspecialisationForType(Kind, Label<'static>, Label<'static>, Annotation),
    CannotRedeclareInheritedAnnotationWithoutspecialisationForCapability(
        CapabilityKind,
        Label<'static>,
        Label<'static>,
        Label<'static>,
        Annotation,
    ),
    ChangingRelationSupertypeLeadsToImplicitCascadeAnnotationAcquisitionAndUnexpectedDataLoss(
        Label<'static>,
        Label<'static>,
        Label<'static>,
    ),
    ChangingAttributeSupertypeLeadsToImplicitIndependentAnnotationLossAndUnexpectedDataLoss(
        Label<'static>,
        Option<Label<'static>>,
        Label<'static>,
    ),
    CannotDeleteTypeWithExistingInstances(Label<'static>),
    CannotSetRoleOrderingWithExistingInstances(Label<'static>),
    CannotSetOwnsOrderingWithExistingInstances(Label<'static>, Label<'static>),
    CannotUnsetValueTypeWithExistingInstances(Label<'static>),
    CannotChangeValueTypeWithExistingInstances(Label<'static>),
    CannotSetAbstractToTypeWithExistingInstances(Label<'static>),
    CannotUnsetCapabilityWithExistingInstances(CapabilityKind, Label<'static>, Label<'static>, Label<'static>),
    CannotSetAbstractToCapabilityWithExistingInstances(CapabilityKind, Label<'static>, Label<'static>, Label<'static>),
    CannotChangeSupertypeAsCapabilityIsLostWhileHavingHasInstances(
        CapabilityKind,
        Label<'static>,
        Option<Label<'static>>,
        Label<'static>,
        Label<'static>,
    ),
    CannotAcquireCapabilityAsExistingInstancesViolateItsConstraint(DataValidationError),
    CannotSetAnnotationForCapabilityAsExistingInstancesViolateItsConstraint(DataValidationError),
    CannotChangeSupertypeAsUpdatedCapabilityConstraintIsViolatedByExistingInstances(
        DataValidationError
    ),
    CannotChangeInterfaceTypeSupertypeAsUpdatedCapabilityConstraintIsViolatedByExistingInstances(
        DataValidationError
    ),
    CannotUnsetInterfaceTypeSupertypeAsUpdatedCapabilityConstraintIsViolatedByExistingInstances(
        DataValidationError
    ),
    CannotSetAnnotationAsExistingInstancesViolateItsConstraint(DataValidationError),
    CannotChangeSupertypeAsUpdatedConstraintIsViolatedByExistingInstances(DataValidationError),
}

impl fmt::Display for SchemaValidationError {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        todo!()
    }
}

impl Error for SchemaValidationError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::ConceptRead(source) => Some(source),
            Self::LabelShouldBeUnique { .. } => None,
            Self::StructNameShouldBeUnique(_) => None,
            Self::StructShouldHaveAtLeastOneField(_) => None,
            Self::StructCannotBeDeletedAsItsUsedAsValueTypeForAttributeTypes(_, _) => None,
            Self::StructCannotBeDeletedAsItsUsedAsValueTypeForStructs(_, _) => None,
            Self::RoleNameShouldBeUniqueForRelationTypeHierarchy(_, _) => None,
            Self::CycleFoundInTypeHierarchy(_, _) => None,
            Self::ChangingAttributeTypeSupertypeWillLeadToConflictingValueTypes(_, _, _) => None,
            Self::CannotUnsetAbstractnessOfAttributeTypeAsItHasSubtypes(_) => None,
            Self::CannotDeleteTypeWithExistingSubtypes(_) => None,
            Self::CannotUnsetCapabilityWithExistingOverridingCapabilities(_, _, _, _, _) => None,
            Self::RelatesNotInherited(_, _) => None,
            Self::OwnsNotInherited(_, _) => None,
            Self::PlaysNotInherited(_, _) => None,
            Self::OverriddenCapabilityCannotBeRedeclared(_, _, _) => None,
            Self::HiddenCapabilityInterfaceIsNotSupertype(_, _, _, _) => None,
            Self::OrderingDoesNotMatchWithSupertype(_, _, _, _) => None,
            Self::OrderingDoesNotMatchWithCapabilityOfSubtypeInterface(_, _, _, _, _) => None,
            Self::CannotChangeSupertypeAsCapabilityOverrideIsImplicitlyLost(_, _, _, _, _, _, _) => None,
            Self::CannotChangeSupertypeAsOwnsOverrideIsImplicitlyLost(_, _, _) => None,
            Self::CannotChangeSupertypeAsPlaysOverrideIsImplicitlyLost(_, _, _) => None,
            Self::CannotChangeSupertypeAsCapabilityIsOverriddenInTheNewSupertype(_, _, _, _) => None,
            Self::HiddenRelatesIsNotInheritedByRelationType(_, _) => None,
            Self::HiddenOwnsIsNotInheritedByObjectType(_, _) => None,
            Self::HiddenPlaysIsNotInheritedByObjectType(_, _) => None,
            Self::CannotSetOwnsBecauseItIsAlreadySetWithDifferentOrdering(_, _, _) => None,
            Self::InvalidOrderingForDistinctConstraint(_) => None,
            Self::AttributeTypeSupertypeIsNotAbstract(_) => None,
            Self::AbstractTypesSupertypeHasToBeAbstract(_, _) => None,
            Self::CannotUnsetAbstractnessAsItHasDeclaredCapabilityOfAbstractInterface(_, _, _) => None,
            Self::CannotUnsetAbstractnessAsItHasInheritedCapabilityOfAbstractInterface(_, _, _) => None,
            Self::CannotUnsetRelatesAbstractnessAsItHasspecialisingRelates(_) => None,
            Self::AttributeTypeWithoutValueTypeShouldBeAbstract(_) => None,
            Self::ValueTypeIsNotCompatibleWithRegexAnnotation(_, _) => None,
            Self::ValueTypeIsNotCompatibleWithRangeAnnotation(_, _) => None,
            Self::ValueTypeIsNotCompatibleWithValuesAnnotation(_, _) => None,
            Self::ValueTypeIsNotKeyableForKeyAnnotation(_, _, _) => None,
            Self::ValueTypeIsNotKeyableForUniqueAnnotation(_, _, _) => None,
            Self::CannotSetAnnotationToInterfaceBecauseItDoesNotNarrowItsCapabilityConstraint(_, _, _) => None,
            Self::CannotSetAnnotationToCapabilityBecauseItDoesNotNarrowItsInterfaceConstraint(_, _, _, _) => None,
            Self::InvalidCardinalityArguments(_) => None,
            Self::InvalidRegexArguments(_) => None,
            Self::InvalidRangeArgumentsForValueType(_, _) => None,
            Self::InvalidValuesArgumentsForValueType(_, _) => None,
            Self::KeyDoesNotNarrowInheritedCardinality(_, _, _, _, _) => None,
            Self::CardinalityDoesNotNarrowInheritedCardinality(_, _, _, _, _, _, _) => None,
            Self::SummarizedCardinalityOfCapabilitiesOverridingSingleCapabilityOverflowsConstraint(
                _,
                _,
                _,
                _,
                _,
                _,
            ) => None,
            Self::RegexShouldNarrowInheritedRegex(_, _, _, _) => None,
            Self::RangeShouldNarrowInheritedRange(_, _, _, _) => None,
            Self::ValuesShouldNarrowInheritedValues(_, _, _, _) => None,
            Self::RegexShouldNarrowInheritedCapabilityRegex(_, _, _, _, _, _) => None,
            Self::RangeShouldNarrowInheritedCapabilityRange(_, _, _, _, _, _) => None,
            Self::ValuesShouldNarrowInheritedCapabilityValues(_, _, _, _, _, _) => None,
            Self::CannotUnsetInheritedOwns(_, _) => None,
            Self::CannotUnsetInheritedPlays(_, _) => None,
            Self::CannotUnsetInheritedAnnotation(_, _) => None,
            Self::CannotUnsetInheritedEdgeAnnotation(_, _, _) => None,
            Self::CannotUnsetInheritedValueType(_, _) => None,
            Self::ValueTypeNotCompatibleWithInheritedValueType(_, _, _, _) => None,
            Self::CannotRedeclareInheritedValueTypeWithoutspecialisation(_, _, _, _) => None,
            Self::DeclaredAnnotationIsNotCompatibleWithInheritedAnnotation(_, _, _) => None,
            Self::DeclaredCapabilityAnnotationIsNotCompatibleWithInheritedAnnotation(_, _, _, _) => None,
            Self::AnnotationIsNotCompatibleWithDeclaredAnnotation(_, _, _) => None,
            Self::RelationTypeMustRelateAtLeastOneRole(_) => None,
            Self::CannotRedeclareInheritedCapabilityWithoutspecialisationWithOverride(_, _, _, _) => None,
            Self::CannotRedeclareInheritedAnnotationWithoutspecialisationForType(_, _, _, _) => None,
            Self::CannotRedeclareInheritedAnnotationWithoutspecialisationForCapability(_, _, _, _, _) => None,
            Self::ChangingRelationSupertypeLeadsToImplicitCascadeAnnotationAcquisitionAndUnexpectedDataLoss(
                _,
                _,
                _,
            ) => None,
            Self::ChangingAttributeSupertypeLeadsToImplicitIndependentAnnotationLossAndUnexpectedDataLoss(_, _, _) => {
                None
            }
            Self::CannotDeleteTypeWithExistingInstances(_) => None,
            Self::CannotSetRoleOrderingWithExistingInstances(_) => None,
            Self::CannotSetOwnsOrderingWithExistingInstances(_, _) => None,
            Self::CannotUnsetValueTypeWithExistingInstances(_) => None,
            Self::CannotChangeValueTypeWithExistingInstances(_) => None,
            Self::CannotSetAbstractToTypeWithExistingInstances(_) => None,
            Self::CannotUnsetCapabilityWithExistingInstances(_, _, _, _) => None,
            Self::CannotSetAbstractToCapabilityWithExistingInstances(_, _, _, _) => None,
            Self::CannotChangeSupertypeAsCapabilityIsLostWhileHavingHasInstances(_, _, _, _, _) => None,
            Self::CannotAcquireCapabilityAsExistingInstancesViolateItsConstraint(source) => Some(source),
            Self::CannotSetAnnotationForCapabilityAsExistingInstancesViolateItsConstraint(source) => Some(source),
            Self::CannotChangeSupertypeAsUpdatedCapabilityConstraintIsViolatedByExistingInstances(
                source,
            ) => Some(source),
            Self::CannotChangeInterfaceTypeSupertypeAsUpdatedCapabilityConstraintIsViolatedByExistingInstances(
                source,
            ) => Some(source),
            Self::CannotUnsetInterfaceTypeSupertypeAsUpdatedCapabilityConstraintIsViolatedByExistingInstances(
                source,
            ) => Some(source),
            Self::CannotSetAnnotationAsExistingInstancesViolateItsConstraint(source) => Some(source),
            Self::CannotChangeSupertypeAsUpdatedConstraintIsViolatedByExistingInstances(source) => Some(source),
        }
    }
}
