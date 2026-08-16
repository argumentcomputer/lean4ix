import Lean4Lean.Verify.TypeChecker.IsDefEq
import Lean4Lean.Theory.Typing.ChurchRosser

/-!
# Registered structure-eta checker surface

These guards pin the complete registered bridge. Host metadata resolves to
the exact checked-view descriptor, subject reduction comes from its ordered
registry certificate, and the primitive Theory rule closes both executable
checker roots.
-/

namespace Lean4Lean.Tests.StructureEtaCapability

open Lean4Lean.TypeChecker.Inner

/-! ## Kernel eligibility and conversion matrix -/

namespace Fixtures

open Lean Elab Command

elab "#guard_eta_eligible " n:ident : command => do
  let env ← getEnv
  unless Kernel.Environment.isNonRecStructure env.toKernelEnv n.getId do
    throwError "expected {n.getId} to be structure-eta eligible"

elab "#guard_eta_ineligible " n:ident : command => do
  let env ← getEnv
  if Kernel.Environment.isNonRecStructure env.toKernelEnv n.getId then
    throwError "expected {n.getId} not to be structure-eta eligible"

universe u v

/-- Parameterized, dependent fields exercise the ordered projector spine. -/
structure EtaDependent (α : Type u) (family : α → Type v) where
  key : α
  value : family key

/-- The unit-like path is the empty projector-spine specialization. -/
structure EtaEmpty (α : Type u) where

/-- A proof field in a Type-valued structure remains eta eligible. -/
structure EtaProofField (p : Prop) where
  witness : p

/-- Prop-valued structures share the same eligibility path. -/
structure EtaProp (p : Prop) : Prop where
  witness : p

inductive EtaRecursive : Type where
  | mk (tail : Option EtaRecursive)

inductive EtaMulti : Type where
  | left
  | right

inductive EtaIndexed : Bool → Type where
  | mk : EtaIndexed true

#guard_eta_eligible Lean4Lean.Tests.StructureEtaCapability.Fixtures.EtaDependent
#guard_eta_eligible Lean4Lean.Tests.StructureEtaCapability.Fixtures.EtaEmpty
#guard_eta_eligible Lean4Lean.Tests.StructureEtaCapability.Fixtures.EtaProofField
#guard_eta_eligible Lean4Lean.Tests.StructureEtaCapability.Fixtures.EtaProp
#guard_eta_ineligible Lean4Lean.Tests.StructureEtaCapability.Fixtures.EtaRecursive
#guard_eta_ineligible Lean4Lean.Tests.StructureEtaCapability.Fixtures.EtaMulti
#guard_eta_ineligible Lean4Lean.Tests.StructureEtaCapability.Fixtures.EtaIndexed

/-- Neutral-major reconstruction is kernel conversion, including dependence. -/
example (x : EtaDependent α family) :
    EtaDependent.mk x.key x.value = x := rfl

example (x : EtaEmpty α) : EtaEmpty.mk = x := rfl

example (x : EtaProofField p) : EtaProofField.mk x.witness = x := rfl

example (x : EtaProp p) : EtaProp.mk x.witness = x := rfl

end Fixtures

#check VEnv.HasStructureEta
#check VEnv.hasStructureEta_of_registry
#check VStructEta.WF.rebuild_hasType
#check VEnv.IsDefEq.structEta
#check VEnv.IsDefEq.church_rosser
#check StructureEtaArtifact
#check StructureEtaReady
#check tryEtaStructCore.WF_of_structureEta
#check isDefEqUnitLike.WF_of_structureEta
#check tryEtaStructCore.WF
#check isDefEqUnitLike.WF

/--
info: 'Lean4Lean.VEnv.HasStructureEta' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms VEnv.HasStructureEta

/--
info: 'Lean4Lean.VEnv.hasStructureEta_of_registry' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VEnv.hasStructureEta_of_registry

/--
info: 'Lean4Lean.VStructEta.WF.rebuild_hasType' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms VStructEta.WF.rebuild_hasType

/--
info: 'Lean4Lean.VEnv.IsDefEq.structEta' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms VEnv.IsDefEq.structEta

/--
info: 'Lean4Lean.VEnv.IsDefEq.church_rosser' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VEnv.IsDefEq.church_rosser

/--
info: 'Lean4Lean.TypeChecker.Inner.tryEtaStructCore.WF' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Lean.Expr.eqv_eq,
 Lean.Level.instLawfulBEqLevel,
 Lean.PersistentArray.toList'_push,
 Lean.Syntax.structEq_eq,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms tryEtaStructCore.WF

/--
info: 'Lean4Lean.TypeChecker.Inner.isDefEqUnitLike.WF' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Lean.PersistentArray.toList'_push,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms isDefEqUnitLike.WF

end Lean4Lean.Tests.StructureEtaCapability
