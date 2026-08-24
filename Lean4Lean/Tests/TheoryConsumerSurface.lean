import Lean4Lean.Theory.Literals
import Lean4Lean.Theory.Projection
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
#check VEnv.ConstructorHead
#check VEnv.ConstructorHead.mono
#check VInductDecl.ElimMode.ofBool
#check VStructureView.etaRebuild
#check VStructureView.MinorsWF
#check VStructureView.RebuildWF
#check VStructureView.projector_hasType_field_of_type
#check VStructureView.WF.checkedParamsSpine
#check VStructureView.WF.constructorPrefix_hasType
#check VStructureView.WF.toProgramsWF_of_minors
#check VStructureView.WF.toRebuildWF_of_programs
#check VStructureView.WF.toStructEtaWF_of_rebuilds
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
info: 'Lean4Lean.VStructureView.projector_hasType_field_of_type' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
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
info: 'Lean4Lean.VStructureView.WF.toProgramsWF_of_minors' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VStructureView.WF.toProgramsWF_of_minors

/--
info: 'Lean4Lean.VStructureView.WF.toRebuildWF_of_programs' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms VStructureView.WF.toRebuildWF_of_programs

/--
info: 'Lean4Lean.VStructureView.WF.toStructEtaWF_of_rebuilds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VStructureView.WF.toStructEtaWF_of_rebuilds

/--
info: 'Lean4Lean.VStructureView.ProgramsWF.projectionArgsSpine' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms VStructureView.ProgramsWF.projectionArgsSpine

/--
info: 'Lean4Lean.VStructureView.ProgramsWF.etaRebuild_hasType_of_constructorPrefix' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms VStructureView.ProgramsWF.etaRebuild_hasType_of_constructorPrefix

end Lean4Lean.Tests.TheoryConsumerSurface
