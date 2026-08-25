import Lean4Lean.Theory.Literals
import Lean4Lean.Theory.Projection
import Lean4Lean.Theory.Typing.ChurchRosser
import Lean4Lean.Theory.Typing.InductiveLemmas
import Lean4Lean.Theory.Typing.UniqueTyping

/-!
# Theory-only consumer surface

This module deliberately imports no `Lean4Lean.Verify` module.  Name
resolution here is the regression gate for the consumer-neutral declarations
migrated by L4L-15C; the deprecated Verify aliases can therefore be removed
without taking these APIs away from Theory consumers.
-/

namespace Lean4Lean.Tests.TheoryConsumerSurface

#check VEnv.reflectedPrimitiveNames
#check VEnv.HasPrimitives.of_avoids
#check VEnv.addConst_other
#check VEnv.HasPrimitives.addConst
#check VExpr.WF.boolLit_has_type
#check VExpr.hasConst_lift'
#check VEnv.HasType.hasConst_false_of_absent
#check VEnv.SpineWF.weak'
#check VEnv.SpineWF.weakN_inv
#check VEnv.SpineWF.weak'_inv
#check VExpr.instRev_liftN_bvarRevRange
#check VExpr.instRevAt_append_singleton
#check VExpr.instRevAt_liftN_one_append_singleton
#check VExpr.map_instRevAt_liftTelN_one_append_singleton
#check VEnv.OnTel.selfSpineWF
#check VEnv.OnTel.instRev_defeq_of_spines
#check VEnv.ConversionRegular
#check VEnv.WF.conversionRegular
#check VEnv.OnSortTel.prefix_getElem?
#check VEnv.ConstructorHead
#check VEnv.ConstructorHead.mono
#check VEnv.Params.PatternArgumentNonFunction
#check VEnv.Params.PatternArgumentNonFunction.not_forallE
#check VEnv.Params.StructurePatternCompatibility
#check VEnv.Params.StructurePatternCompatibility.structureArgument
#check VEnv.NormalEq.parRed_extra_structuralArg
#check VEnv.NormalEq.parRed
#check VInductDecl.ElimMode.ofBool
#check VStructureView.etaRebuild
#check VExpr.selectFieldMinor
#check VExpr.selectFieldMinor_liftN
#check VExpr.selectFieldMinor_instN
#check VStructureView.fieldProjectionMinorType
#check VStructureView.generatedProjectionMinorType
#check VStructureView.projectionMinorType
#check VStructureView.projectionIHTypes
#check VStructureView.WF.generatedProjectionMinorType_eq_field
#check VStructureView.MinorsWF
#check VStructureView.MinorsWFPrefix
#check VStructureView.ProgramsWFPrefix
#check VStructureView.ConstructorProjectorsExactPrefix
#check VStructureView.ConstructorRuleCapturesPrefix
#check VStructureView.RebuildWF
#check VStructureView.projectionArgsSpineAux_of_prefix
#check VStructureView.projector_hasType_field_of_type
#check VStructureView.WF.checkedParamsSpine
#check VStructureView.WF.constructorPrefix_hasType
#check VStructureView.WF.projectionCommonSpine
#check VStructureView.WF.projectionRuleCaptureSpine
#check VStructureView.WF.toMinorsWFPrefix_one
#check VStructureView.WF.toProgramsWFPrefix_of_minorsWFPrefix
#check VStructureView.WF.projectionTypeFn_hasType_of_programsPrefix
#check VStructureView.WF.toConstructorRuleCapturesPrefix_of_minorsWFPrefix
#check VStructureView.WF.toMinorsWFPrefix_succ_of_constructorProjectorsExactPrefix
#check VStructureView.WF.toConstructorProjectorsExactPrefix_of_ruleCaptures
#check VStructureView.WF.toMinorsWFPrefix_succ
#check VStructureView.WF.toMinorsWF
#check VStructureView.WF.toProgramsWF_of_minors
#check VStructureView.WF.toProgramsWF
#check VStructureView.WF.toRebuildWF_of_programs
#check VStructureView.WF.toRebuildWF
#check VStructureView.WF.toStructEtaWF_of_rebuilds
#check VStructureView.WF.toStructEtaWF
#check VStructureView.ProgramsWF.projectionArgsSpine
#check VStructureView.ProgramsWF.etaRebuild_hasType_of_constructorPrefix

/--
info: 'Lean4Lean.VEnv.reflectedPrimitiveNames' does not depend on any axioms
-/
#guard_msgs in
#print axioms VEnv.reflectedPrimitiveNames

/--
info: 'Lean4Lean.VEnv.HasPrimitives.of_avoids' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VEnv.HasPrimitives.of_avoids

/--
info: 'Lean4Lean.VEnv.addConst_other' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms VEnv.addConst_other

/--
info: 'Lean4Lean.VEnv.HasPrimitives.addConst' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VEnv.HasPrimitives.addConst

/--
info: 'Lean4Lean.VExpr.WF.boolLit_has_type' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms VExpr.WF.boolLit_has_type

/--
info: 'Lean4Lean.VExpr.hasConst_lift'' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms VExpr.hasConst_lift'

/--
info: 'Lean4Lean.VEnv.HasType.hasConst_false_of_absent' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms VEnv.HasType.hasConst_false_of_absent

/--
info: 'Lean4Lean.VEnv.SpineWF.weak'' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms VEnv.SpineWF.weak'

/--
info: 'Lean4Lean.VEnv.SpineWF.weakN_inv' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VEnv.SpineWF.weakN_inv

/--
info: 'Lean4Lean.VEnv.SpineWF.weak'_inv' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VEnv.SpineWF.weak'_inv

/--
info: 'Lean4Lean.VExpr.instRev_liftN_bvarRevRange' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms VExpr.instRev_liftN_bvarRevRange

/--
info: 'Lean4Lean.VExpr.instRevAt_append_singleton' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms VExpr.instRevAt_append_singleton

/--
info: 'Lean4Lean.VExpr.instRevAt_liftN_one_append_singleton' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms VExpr.instRevAt_liftN_one_append_singleton

/--
info: 'Lean4Lean.VExpr.map_instRevAt_liftTelN_one_append_singleton' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms VExpr.map_instRevAt_liftTelN_one_append_singleton

/--
info: 'Lean4Lean.VEnv.OnTel.selfSpineWF' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms VEnv.OnTel.selfSpineWF

/--
info: 'Lean4Lean.VEnv.OnTel.instRev_defeq_of_spines' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms VEnv.OnTel.instRev_defeq_of_spines

/--
info: 'Lean4Lean.VEnv.WF.conversionRegular' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VEnv.WF.conversionRegular

/--
info: 'Lean4Lean.VEnv.OnSortTel.prefix_getElem?' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms VEnv.OnSortTel.prefix_getElem?

/--
info: 'Lean4Lean.VInductDecl.ElimMode.ofBool' does not depend on any axioms
-/
#guard_msgs in
#print axioms VInductDecl.ElimMode.ofBool

/--
info: 'Lean4Lean.VStructureView.etaRebuild' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms VStructureView.etaRebuild

/--
info: 'Lean4Lean.VStructureView.projector_hasType_field_of_type' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VStructureView.projector_hasType_field_of_type

/--
info: 'Lean4Lean.VStructureView.WF.checkedParamsSpine' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VStructureView.WF.checkedParamsSpine

/--
info: 'Lean4Lean.VStructureView.WF.constructorPrefix_hasType' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VStructureView.WF.constructorPrefix_hasType

/--
info: 'Lean4Lean.VStructureView.WF.projectionCommonSpine' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VStructureView.WF.projectionCommonSpine

/--
info: 'Lean4Lean.VStructureView.WF.projectionRuleCaptureSpine' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VStructureView.WF.projectionRuleCaptureSpine

/--
info: 'Lean4Lean.VStructureView.projectionArgsSpineAux_of_prefix' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VStructureView.projectionArgsSpineAux_of_prefix

/--
info: 'Lean4Lean.VStructureView.WF.toMinorsWFPrefix_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VStructureView.WF.toMinorsWFPrefix_one

/--
info: 'Lean4Lean.VStructureView.WF.toProgramsWFPrefix_of_minorsWFPrefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms VStructureView.WF.toProgramsWFPrefix_of_minorsWFPrefix

/--
info: 'Lean4Lean.VStructureView.WF.projectionTypeFn_hasType_of_programsPrefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms VStructureView.WF.projectionTypeFn_hasType_of_programsPrefix

/--
info: 'Lean4Lean.VStructureView.WF.toConstructorRuleCapturesPrefix_of_minorsWFPrefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms VStructureView.WF.toConstructorRuleCapturesPrefix_of_minorsWFPrefix

/--
info: 'Lean4Lean.VStructureView.WF.toMinorsWFPrefix_succ_of_constructorProjectorsExactPrefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms VStructureView.WF.toMinorsWFPrefix_succ_of_constructorProjectorsExactPrefix

/--
info: 'Lean4Lean.VStructureView.WF.toConstructorProjectorsExactPrefix_of_ruleCaptures' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms VStructureView.WF.toConstructorProjectorsExactPrefix_of_ruleCaptures

/--
info: 'Lean4Lean.VStructureView.WF.toMinorsWFPrefix_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VStructureView.WF.toMinorsWFPrefix_succ

/--
info: 'Lean4Lean.VStructureView.WF.toMinorsWF' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VStructureView.WF.toMinorsWF

/--
info: 'Lean4Lean.VStructureView.WF.toProgramsWF_of_minors' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VStructureView.WF.toProgramsWF_of_minors

/--
info: 'Lean4Lean.VStructureView.WF.toProgramsWF' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VStructureView.WF.toProgramsWF

/--
info: 'Lean4Lean.VStructureView.WF.toRebuildWF_of_programs' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VStructureView.WF.toRebuildWF_of_programs

/--
info: 'Lean4Lean.VStructureView.WF.toRebuildWF' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VStructureView.WF.toRebuildWF

/--
info: 'Lean4Lean.VStructureView.WF.toStructEtaWF_of_rebuilds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VStructureView.WF.toStructEtaWF_of_rebuilds

/--
info: 'Lean4Lean.VStructureView.WF.toStructEtaWF' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VStructureView.WF.toStructEtaWF

/--
info: 'Lean4Lean.VStructureView.ProgramsWF.projectionArgsSpine' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VStructureView.ProgramsWF.projectionArgsSpine

/--
info: 'Lean4Lean.VStructureView.ProgramsWF.etaRebuild_hasType_of_constructorPrefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms VStructureView.ProgramsWF.etaRebuild_hasType_of_constructorPrefix

end Lean4Lean.Tests.TheoryConsumerSurface
