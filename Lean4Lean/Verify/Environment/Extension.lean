/-
This file is derived from lean4lean and has been modified by Argument Computer Corporation.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/

import Lean4Lean.Verify.Environment.Readiness

namespace Lean4Lean
open Lean4Lean
open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

theorem TrEnv.exists_addConst (H : TrEnv safety env venv) (hn : env.find? name = none)
    (ci' : VConstant) : ∃ venv', venv.addConst name ci' = some venv' := by
  unfold VEnv.addConst
  cases hfind : venv.constants name with
  | none => simp
  | some ci => obtain ⟨ci, hci, _⟩ := H.find?_iff.2 ⟨ci, hfind⟩; cases hn ▸ hci

theorem VEnv.addConst_mono {env₁ env₂ env₁' env₂' : VEnv} (H : env₁ ≤ env₂)
    (h₁ : env₁.addConst name ci = some env₁') (h₂ : env₂.addConst name ci = some env₂') :
    env₁' ≤ env₂' := by
  unfold VEnv.addConst at h₁ h₂
  split at h₁ <;> cases h₁
  split at h₂ <;> cases h₂
  refine { constants {n a} := ?_, defeqs := H.defeqs, structEtas := H.structEtas }
  dsimp; split <;> [exact id; exact H.constants]

theorem VEnv.addDefEq_mono {env₁ env₂ : VEnv} (H : env₁ ≤ env₂) :
    env₁.addDefEq df ≤ env₂.addDefEq df where
  constants := H.constants
  defeqs := by rintro d (rfl | hd) <;> [exact .inl rfl; exact .inr (H.defeqs hd)]
  structEtas := H.structEtas

/-- Registering the same structure-eta descriptor on two ordered models
preserves their extension relation. -/
theorem VEnv.addStructEta_mono {env₁ env₂ : VEnv} (H : env₁ ≤ env₂) :
    env₁.addStructEta rule ≤ env₂.addStructEta rule where
  constants := H.constants
  defeqs := H.defeqs
  structEtas := by
    rintro registered (rfl | hregistered)
    · exact .inl rfl
    · exact .inr (H.structEtas hregistered)

theorem VEnv.addConsts_mono {env₁ env₂ env₁' env₂' : VEnv} (H : env₁ ≤ env₂) :
    ∀ {cis}, env₁.addConsts cis = some env₁' → env₂.addConsts cis = some env₂' → env₁' ≤ env₂'
  | [], h₁, h₂ => by cases h₁; cases h₂; exact H
  | _ :: _, h₁, h₂ => by
    simp [VEnv.addConsts, Option.bind_eq_some_iff] at h₁ h₂
    obtain ⟨_, e₁, h₁⟩ := h₁; obtain ⟨_, e₂, h₂⟩ := h₂
    exact VEnv.addConsts_mono (VEnv.addConst_mono H e₁ e₂) h₁ h₂

theorem VEnv.addDefEqs_mono {env₁ env₂ : VEnv} (H : env₁ ≤ env₂) :
    ∀ {cis}, env₁.addDefEqs cis ≤ env₂.addDefEqs cis
  | [] => H
  | _ :: _ => VEnv.addDefEqs_mono (VEnv.addDefEq_mono H)

theorem VEnv.addConst_eq_of_ne
    {env env' : VEnv}
    (hadd : env.addConst name ci = some env') (hne : name ≠ n) :
    env'.constants n = env.constants n := by
  unfold VEnv.addConst at hadd
  split at hadd <;> cases hadd
  simp [hne]

/-- Transport a typed binary-Nat reflection across a model extension when the
reflected constant's lookup is known to come from the source model. -/
private theorem VEnv.ReflectsNatNatNat.mono_of_contains
    {env env' : VEnv} (H : env.ReflectsNatNatNat name f)
    (hle : env ≤ env') (hback : env'.contains name → env.contains name) :
    env'.ReflectsNatNatNat name f := by
  intro found
  obtain ⟨htype, heval⟩ := H (hback found)
  exact ⟨fun U Γ => (htype U Γ).mono hle,
    fun a b => (heval a b).mono hle⟩

/-- Transport a typed Boolean-valued binary-Nat reflection across a model
extension when the reflected lookup comes from the source model. -/
private theorem VEnv.ReflectsNatNatBool.mono_of_contains
    {env env' : VEnv} (H : env.ReflectsNatNatBool name f)
    (hle : env ≤ env') (hback : env'.contains name → env.contains name) :
    env'.ReflectsNatNatBool name f := by
  intro found
  obtain ⟨htype, heval⟩ := H (hback found)
  exact ⟨fun U Γ => (htype U Γ).mono hle,
    fun a b => (heval a b).mono hle⟩

theorem VEnv.HasPrimitives.addConst_of_not_primitive {env env' : VEnv} (H : env.HasPrimitives)
    (hname : Environment.primitives.contains name = false)
    (hadd : env.addConst name ci = some env') : env'.HasPrimitives := by
  have le := VEnv.addConst_le hadd
  have same {n} (hp : Environment.primitives.contains n = true) :
      env'.constants n = env.constants n :=
    VEnv.addConst_eq_of_ne hadd fun h => by subst h; simp_all
  have oldContains {n} (hp : Environment.primitives.contains n = true) :
      env'.contains n → env.contains n := fun ⟨ci, hci⟩ => ⟨ci, (same hp) ▸ hci⟩
  have newContains {n} : env.contains n → env'.contains n := fun ⟨ci, hci⟩ => ⟨ci, le.constants hci⟩
  refine let prims := _; have hprims : Environment.primitives = .ofList prims := rfl; ?_
  replace hprims {n} : n ∈ prims → Environment.primitives.contains n := by
    simp [hprims, NameSet.contains, NameSet.ofList]
  simp only [List.mem_cons, prims] at hprims
  constructor
  · intro h
    let ⟨h1, h2⟩ := H.bool (oldContains (hprims (by simp)) h)
    exact ⟨newContains h1, newContains h2⟩
  · intro ci h; apply H.boolFalse; rwa [← same (hprims (by simp))]
  · intro ci h; apply H.boolTrue; rwa [← same (hprims (by simp))]
  · intro h
    let ⟨h1, h2⟩ := H.nat (oldContains (hprims (by simp)) h)
    exact ⟨newContains h1, newContains h2⟩
  · intro ci h; apply H.natZero; rwa [← same (hprims (by simp))]
  · intro ci h; apply H.natSucc; rwa [← same (hprims (by simp))]
  · intro h
    obtain ⟨htype, heval⟩ := H.natPred
      (oldContains (hprims (by simp)) h)
    exact ⟨fun U Γ => (htype U Γ).mono le,
      fun a => (heval a).mono le⟩
  · exact H.natAdd.mono_of_contains le (oldContains (hprims (by simp)))
  · exact H.natSub.mono_of_contains le (oldContains (hprims (by simp)))
  · exact H.natMul.mono_of_contains le (oldContains (hprims (by simp)))
  · exact H.natPow.mono_of_contains le (oldContains (hprims (by simp)))
  · exact H.natGcd.mono_of_contains le (oldContains (hprims (by simp)))
  · exact H.natMod.mono_of_contains le (oldContains (hprims (by simp)))
  · exact H.natDiv.mono_of_contains le (oldContains (hprims (by simp)))
  · exact H.natBEq.mono_of_contains le (oldContains (hprims (by simp)))
  · exact H.natBLE.mono_of_contains le (oldContains (hprims (by simp)))
  · exact H.natLAnd.mono_of_contains le (oldContains (hprims (by simp)))
  · exact H.natLOr.mono_of_contains le (oldContains (hprims (by simp)))
  · exact H.natXor.mono_of_contains le (oldContains (hprims (by simp)))
  · exact H.natShiftLeft.mono_of_contains le
      (oldContains (hprims (by simp)))
  · exact H.natShiftRight.mono_of_contains le
      (oldContains (hprims (by simp)))
  · intro ci h
    obtain ⟨hu, hty⟩ := H.charOfNat (by
      rwa [← same (hprims (by simp))])
    exact ⟨hu, fun U Γ => (hty U Γ).mono le⟩
  · intro ci h
    obtain ⟨hu, hty, hnil, hcons⟩ := H.stringOfList
      (by rwa [← same (hprims (by simp))])
    exact ⟨hu, fun U Γ => (hty U Γ).mono le,
      hnil.mono le, hcons.mono le⟩

theorem VEnv.HasPrimitives.addDefEq {env : VEnv} (H : env.HasPrimitives) :
    (env.addDefEq df).HasPrimitives :=
  { H with
    natPred h :=
      let ⟨htype, heval⟩ := H.natPred h
      ⟨fun U Γ => (htype U Γ).mono VEnv.addDefEq_le,
        fun a => (heval a).mono VEnv.addDefEq_le⟩
    natAdd := H.natAdd.mono_of_contains VEnv.addDefEq_le (fun h => h)
    natSub := H.natSub.mono_of_contains VEnv.addDefEq_le (fun h => h)
    natMul := H.natMul.mono_of_contains VEnv.addDefEq_le (fun h => h)
    natPow := H.natPow.mono_of_contains VEnv.addDefEq_le (fun h => h)
    natGcd := H.natGcd.mono_of_contains VEnv.addDefEq_le (fun h => h)
    natMod := H.natMod.mono_of_contains VEnv.addDefEq_le (fun h => h)
    natDiv := H.natDiv.mono_of_contains VEnv.addDefEq_le (fun h => h)
    natBEq := H.natBEq.mono_of_contains VEnv.addDefEq_le (fun h => h)
    natBLE := H.natBLE.mono_of_contains VEnv.addDefEq_le (fun h => h)
    natLAnd := H.natLAnd.mono_of_contains VEnv.addDefEq_le (fun h => h)
    natLOr := H.natLOr.mono_of_contains VEnv.addDefEq_le (fun h => h)
    natXor := H.natXor.mono_of_contains VEnv.addDefEq_le (fun h => h)
    natShiftLeft := H.natShiftLeft.mono_of_contains VEnv.addDefEq_le
      (fun h => h)
    natShiftRight := H.natShiftRight.mono_of_contains VEnv.addDefEq_le
      (fun h => h)
    charOfNat h :=
      let ⟨hu, hty⟩ := H.charOfNat h
      ⟨hu, fun U Γ => (hty U Γ).mono VEnv.addDefEq_le⟩
    stringOfList h :=
      let ⟨hu, hty, hnil, hcons⟩ := H.stringOfList h
      ⟨hu, fun U Γ => (hty U Γ).mono VEnv.addDefEq_le,
        hnil.mono VEnv.addDefEq_le, hcons.mono VEnv.addDefEq_le⟩ }

/-- Theory-only structure-eta registration leaves primitive constants
unchanged and transports every reflected computation along the model
extension. -/
theorem VEnv.HasPrimitives.addStructEta {env : VEnv}
    (H : env.HasPrimitives) :
    (env.addStructEta rule).HasPrimitives :=
  { H with
    natPred h :=
      let ⟨htype, heval⟩ := H.natPred h
      ⟨fun U Γ => (htype U Γ).mono VEnv.addStructEta_le,
        fun a => (heval a).mono VEnv.addStructEta_le⟩
    natAdd := H.natAdd.mono_of_contains VEnv.addStructEta_le (fun h => h)
    natSub := H.natSub.mono_of_contains VEnv.addStructEta_le (fun h => h)
    natMul := H.natMul.mono_of_contains VEnv.addStructEta_le (fun h => h)
    natPow := H.natPow.mono_of_contains VEnv.addStructEta_le (fun h => h)
    natGcd := H.natGcd.mono_of_contains VEnv.addStructEta_le (fun h => h)
    natMod := H.natMod.mono_of_contains VEnv.addStructEta_le (fun h => h)
    natDiv := H.natDiv.mono_of_contains VEnv.addStructEta_le (fun h => h)
    natBEq := H.natBEq.mono_of_contains VEnv.addStructEta_le (fun h => h)
    natBLE := H.natBLE.mono_of_contains VEnv.addStructEta_le (fun h => h)
    natLAnd := H.natLAnd.mono_of_contains VEnv.addStructEta_le (fun h => h)
    natLOr := H.natLOr.mono_of_contains VEnv.addStructEta_le (fun h => h)
    natXor := H.natXor.mono_of_contains VEnv.addStructEta_le (fun h => h)
    natShiftLeft := H.natShiftLeft.mono_of_contains VEnv.addStructEta_le
      (fun h => h)
    natShiftRight := H.natShiftRight.mono_of_contains VEnv.addStructEta_le
      (fun h => h)
    charOfNat h :=
      let ⟨hu, hty⟩ := H.charOfNat h
      ⟨hu, fun U Γ => (hty U Γ).mono VEnv.addStructEta_le⟩
    stringOfList h :=
      let ⟨hu, hty, hnil, hcons⟩ := H.stringOfList h
      ⟨hu, fun U Γ => (hty U Γ).mono VEnv.addStructEta_le,
        hnil.mono VEnv.addStructEta_le,
        hcons.mono VEnv.addStructEta_le⟩ }

/-! ## Certified Theory-only readiness completion -/

/-- A source-ordered trace which registers a list of checked structure-eta
descriptors without changing the host constant map.  Each descriptor is
checked at the exact intermediate Theory environment in which it is added. -/
inductive VEnv.AddStructEtas : VEnv → List VStructEta → VEnv → Prop where
  | nil : VEnv.AddStructEtas env [] env
  | cons :
      rule.WF env →
      VEnv.AddStructEtas (env.addStructEta rule) rules env' →
      VEnv.AddStructEtas env (rule :: rules) env'

namespace VEnv.AddStructEtas

/-- A structure-eta registration trace is a monotone Theory extension. -/
theorem le : AddStructEtas env rules env' → env ≤ env'
  | .nil => VEnv.LE.rfl
  | .cons _ tail => VEnv.addStructEta_le.trans tail.le

/-- Registering a checked rule list preserves ordered-environment history. -/
theorem ordered (trace : AddStructEtas env rules env')
    (pre : env.Ordered) : env'.Ordered := by
  induction trace with
  | nil => exact pre
  | cons ruleWF _ ih => exact ih (.structEta pre ruleWF.toFoundationWF)

/-- Every descriptor named by the source list is registered in the trace's
final Theory environment. -/
theorem registered (trace : AddStructEtas env rules env')
    {rule : VStructEta} (member : rule ∈ rules) :
    env'.structEtas rule := by
  induction trace with
  | nil => simp at member
  | cons ruleWF tail ih =>
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact tail.le.structEtas VEnv.addStructEta_self
      · exact ih member

/-- Pointwise certificates in the input environment assemble into the exact
source-ordered registration fold.  Certificates for the unprocessed suffix
are transported across each preceding registration. -/
theorem of_forallWF
    (rulesWF : ∀ rule ∈ rules, rule.WF env) :
    AddStructEtas env rules (rules.foldl VEnv.addStructEta env) := by
  induction rules generalizing env with
  | nil => exact .nil
  | cons rule rules ih =>
    have ruleWF : rule.WF env := rulesWF rule (by simp)
    have tailWF : ∀ tailRule ∈ rules,
        tailRule.WF (env.addStructEta rule) := by
      intro tailRule member
      exact (rulesWF tailRule (by simp [member])).mono VEnv.addStructEta_le
    exact .cons ruleWF (ih tailWF)

/-- Existential form of `of_forallWF` retained for callers which do not need
the deterministic endpoint. -/
theorem exists_of_forallWF
    (rulesWF : ∀ rule ∈ rules, rule.WF env) :
    ∃ env', AddStructEtas env rules env' :=
  ⟨rules.foldl VEnv.addStructEta env, of_forallWF rulesWF⟩

/-- Registration does not alter the Theory constant lookup function. -/
theorem constants_eq : AddStructEtas env rules env' →
    env'.constants = env.constants
  | .nil => rfl
  | .cons _ tail => tail.constants_eq

/-- Registering checked descriptors extends an existing host/Theory
translation without changing its host map or quotient flag. -/
theorem trEnv {hostMap : ConstMap} {quotInit : Bool}
    (trace : AddStructEtas env rules env')
    (pre : TrEnv' safety hostMap quotInit env) :
    TrEnv' safety hostMap quotInit env' := by
  induction trace with
  | nil => exact pre
  | cons ruleWF _ ih => exact ih (.structEta ruleWF pre)

/-- Structure-eta registration preserves primitive reflection. -/
theorem hasPrimitives (trace : AddStructEtas env rules env')
    (pre : env.HasPrimitives) : env'.HasPrimitives := by
  induction trace with
  | nil => exact pre
  | cons _ _ ih => exact ih pre.addStructEta

/-- Replaying the same descriptor list over ordered input models preserves
their extension relation. -/
theorem mono :
    ∀ (_left : AddStructEtas env₁ rules env₁')
      (_right : AddStructEtas env₂ rules env₂'),
      env₁ ≤ env₂ → env₁' ≤ env₂'
  | .nil, .nil, pre => pre
  | .cons _ left, .cons _ right, pre =>
      left.mono right (VEnv.addStructEta_mono pre)

end VEnv.AddStructEtas

/--
info: 'Lean4Lean.VEnv.AddStructEtas.trEnv' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VEnv.AddStructEtas.trEnv

/--
info: 'Lean4Lean.VEnv.AddStructEtas.hasPrimitives' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms VEnv.AddStructEtas.hasPrimitives

/--
info: 'Lean4Lean.VEnv.AddStructEtas.mono' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms VEnv.AddStructEtas.mono

/-- A resolved projection artifact already contains enough checked generation
data to derive rule-independent reconstruction typing in its current
well-formed Theory model. -/
theorem ProjectionArtifact.rebuildWF
    (self : ProjectionArtifact env familyName familyInfo venv)
    (baseWF : venv.WF) : self.view.RebuildWF venv :=
  self.viewWF.toRebuildWF_of_programs baseWF.conversionRegular self.programsWF

/-- The exact semantic payload needed to register structure eta for one
newly generated projection artifact.  `ruleWF` is deliberately separate from
projection-program typing: it certifies the persistent subject-reduction
contract required by the Theory environment history. -/
structure StructureEtaRegistrationArtifact
    (env : Environment) (familyName : Name) (familyInfo : InductiveVal)
    (constructorName : Name) (constructorInfo : ConstructorVal)
    (venv : VEnv) where
  projection : ProjectionArtifact env familyName familyInfo venv
  constructor_name_eq : projection.view.constructorName = constructorName
  constructor_info_eq : projection.constructorInfo = constructorInfo
  baseWF : venv.WF
  ruleWF :
    (projection.viewWF.toStructEta baseWF.ordered).WF venv

namespace StructureEtaRegistrationArtifact

/-- Package the registry artifact from the smaller persistent reconstruction
contract.  The descriptor syntax, its closed family type, and its current
model proof are all reconstructed from the checked projection view. -/
noncomputable def ofRebuilds
    (projection : ProjectionArtifact env familyName familyInfo venv)
    (constructor_name_eq : projection.view.constructorName = constructorName)
    (constructor_info_eq : projection.constructorInfo = constructorInfo)
    (baseWF : venv.WF)
    (rebuilds : ∀ {venv' : VEnv}, venv ≤ venv' →
      venv'.ConversionRegular → projection.view.RebuildWF venv') :
    StructureEtaRegistrationArtifact env familyName familyInfo
      constructorName constructorInfo venv where
  projection := projection
  constructor_name_eq := constructor_name_eq
  constructor_info_eq := constructor_info_eq
  baseWF := baseWF
  ruleWF := projection.viewWF.toStructEtaWF_of_rebuilds
    baseWF.ordered rebuilds

/-- Checked projection generation closes the persistent registration
certificate without a caller-supplied future-model reconstruction oracle. -/
noncomputable def ofProjection
    (projection : ProjectionArtifact env familyName familyInfo venv)
    (constructor_name_eq : projection.view.constructorName = constructorName)
    (constructor_info_eq : projection.constructorInfo = constructorInfo)
    (baseWF : venv.WF) :
    StructureEtaRegistrationArtifact env familyName familyInfo
      constructorName constructorInfo venv where
  projection := projection
  constructor_name_eq := constructor_name_eq
  constructor_info_eq := constructor_info_eq
  baseWF := baseWF
  ruleWF := projection.viewWF.toStructEtaWF baseWF

/-- Projection readiness plus the exact host family, constructor, and
recursor observations construct the registration artifact selected by the
runtime structure test.  The singleton-family equation identifies the
projection view's constructor with the tested constructor; lookup uniqueness
then identifies its metadata record. -/
theorem ofProjectionReady
    (projectionReady : ProjectionReady env venv)
    (baseWF : venv.WF)
    (family_find : env.find? familyName = some (.inductInfo familyInfo))
    (constructor_find : env.find? constructorName =
      some (.ctorInfo constructorInfo))
    (structure_test : env.isNonRecStructureConstructor familyName constructorName =
      true)
    (recursor_find : env.find? (mkRecName familyName) =
      some (.recInfo recursorInfo)) :
    Nonempty (StructureEtaRegistrationArtifact env familyName familyInfo
      constructorName constructorInfo venv) := by
  obtain ⟨_isRec, constructors_eq, indices_eq, owner_eq⟩ :=
    Kernel.Environment.isNonRecStructureConstructor_info family_find
      constructor_find structure_test
  have projection_ready : env.isProjectionReadyStructure familyName = true :=
    Kernel.Environment.isProjectionReadyStructure_of_info family_find
      constructors_eq indices_eq constructor_find recursor_find owner_eq
  obtain ⟨projection⟩ := projectionReady.infer familyName familyInfo
    family_find projection_ready
  have constructor_name_eq :
      projection.view.constructorName = constructorName := by
    have singleton_eq : [projection.view.constructorName] =
        [constructorName] := projection.ctors_eq.symm.trans constructors_eq
    simpa using singleton_eq
  have constructor_info_eq :
      projection.constructorInfo = constructorInfo := by
    have projection_find := projection.constructor_find
    rw [constructor_name_eq] at projection_find
    have tagged_eq :
        (.ctorInfo projection.constructorInfo : ConstantInfo) =
          .ctorInfo constructorInfo :=
      Option.some.inj (projection_find.symm.trans constructor_find)
    cases tagged_eq
    rfl
  exact ⟨ofProjection projection constructor_name_eq constructor_info_eq
    baseWF⟩

/-- The deterministic Theory descriptor owned by a registration artifact. -/
noncomputable def rule
    (self : StructureEtaRegistrationArtifact env familyName familyInfo
      constructorName constructorInfo venv) : VStructEta :=
  self.projection.viewWF.toStructEta self.baseWF.ordered

/-- Rebuilding the descriptor after monotone transport changes only proof
fields, so every safety-indexed replay may share the same rule value. -/
theorem rule_mono_eq
    (self : StructureEtaRegistrationArtifact env familyName familyInfo
      constructorName constructorInfo venv)
    {venv' : VEnv} (hle : venv ≤ venv') (wf' : venv'.WF) :
    self.rule =
      (self.projection.mono hle).viewWF.toStructEta wf'.ordered :=
  self.projection.viewWF.toStructEta_mono_eq hle self.baseWF.ordered
    wf'.ordered

/-- A registration artifact is persistent along a well-formed Theory-model
extension, retaining the exact descriptor selected at its original base. -/
noncomputable def mono
    (self : StructureEtaRegistrationArtifact env familyName familyInfo
      constructorName constructorInfo venv)
    {venv' : VEnv} (hle : venv ≤ venv') (wf' : venv'.WF) :
    StructureEtaRegistrationArtifact env familyName familyInfo
      constructorName constructorInfo venv' where
  projection := self.projection.mono hle
  constructor_name_eq := self.constructor_name_eq
  constructor_info_eq := self.constructor_info_eq
  baseWF := wf'
  ruleWF := by
    rw [← self.rule_mono_eq hle wf']
    exact self.ruleWF.mono hle

/-- Register the artifact's descriptor as a singleton checked completion
trace. -/
theorem toAddStructEtas
    (self : StructureEtaRegistrationArtifact env familyName familyInfo
      constructorName constructorInfo venv) :
    VEnv.AddStructEtas venv [self.rule]
      (venv.addStructEta self.rule) :=
  .cons self.ruleWF .nil

/-- Projection readiness survives the Theory-only registration step. -/
noncomputable def projectionAfter
    (self : StructureEtaRegistrationArtifact env familyName familyInfo
      constructorName constructorInfo venv) :
    ProjectionArtifact env familyName familyInfo
      (venv.addStructEta self.rule) :=
  self.projection.mono VEnv.addStructEta_le

/-- The same singleton registration constructs the exact final
`StructureEtaArtifact`; equality of the rebuilt descriptor follows from
proof-irrelevance of the transported view and ordered-environment proofs. -/
noncomputable def toStructureEtaArtifact
    (self : StructureEtaRegistrationArtifact env familyName familyInfo
      constructorName constructorInfo venv) :
    StructureEtaArtifact env familyName familyInfo constructorName
      constructorInfo (venv.addStructEta self.rule) := by
  let finalOrd : (venv.addStructEta self.rule).Ordered :=
    .structEta self.baseWF.ordered self.ruleWF.toFoundationWF
  refine {
    projection := self.projectionAfter
    constructor_name_eq := self.constructor_name_eq
    constructor_info_eq := self.constructor_info_eq
    etaOrdered := finalOrd
    etaRegistered := ?_ }
  change (venv.addStructEta self.rule).structEtas
    ((self.projection.viewWF.mono VEnv.addStructEta_le).toStructEta finalOrd)
  rw [← self.projection.viewWF.toStructEta_mono_eq
    VEnv.addStructEta_le self.baseWF.ordered finalOrd]
  exact VEnv.addStructEta_self

/-- A registration artifact occurring anywhere in a checked shared rule list
constructs the exact final structure-eta artifact after the whole list has
been registered. -/
noncomputable def toStructureEtaArtifact_of_completion
    (self : StructureEtaRegistrationArtifact env familyName familyInfo
      constructorName constructorInfo venv)
    {rules : List VStructEta} {venv' : VEnv}
    (completion : VEnv.AddStructEtas venv rules venv')
    (member : self.rule ∈ rules) :
    StructureEtaArtifact env familyName familyInfo constructorName
      constructorInfo venv' := by
  let finalOrd : venv'.Ordered :=
    completion.ordered self.baseWF.ordered
  refine {
    projection := self.projection.mono completion.le
    constructor_name_eq := self.constructor_name_eq
    constructor_info_eq := self.constructor_info_eq
    etaOrdered := finalOrd
    etaRegistered := ?_ }
  change venv'.structEtas
    ((self.projection.viewWF.mono completion.le).toStructEta finalOrd)
  rw [← self.projection.viewWF.toStructEta_mono_eq completion.le
    self.baseWF.ordered finalOrd]
  exact completion.registered member

end StructureEtaRegistrationArtifact

/-- One existentially packaged registration artifact.  Erasing the dependent
host metadata indices this way lets a finite source-indexed inventory own the
shared Theory rule list without accepting that list independently. -/
structure StructureEtaRegistrationEntry
    (env : Environment) (venv : VEnv) where
  familyName : Name
  familyInfo : InductiveVal
  constructorName : Name
  constructorInfo : ConstructorVal
  artifact : StructureEtaRegistrationArtifact env familyName familyInfo
    constructorName constructorInfo venv

namespace StructureEtaRegistrationEntry

/-- The exact Theory descriptor contributed by one packaged artifact. -/
noncomputable def rule
    (entry : StructureEtaRegistrationEntry env venv) : VStructEta :=
  entry.artifact.rule

/-- Each packaged descriptor carries its persistent WF certificate. -/
theorem ruleWF (entry : StructureEtaRegistrationEntry env venv) :
    entry.rule.WF venv := by
  change (entry.artifact.projection.viewWF.toStructEta
    entry.artifact.baseWF.ordered).WF venv
  exact entry.artifact.ruleWF

end StructureEtaRegistrationEntry

/-- Complete host observations for one family selected by the nonrecursive
structure test.  The family name is the external index so a finite list of
names can be scanned without separately choosing metadata inventories. -/
structure StructureEtaRegistrationObservation
    (env : Environment) (familyName : Name) where
  familyInfo : InductiveVal
  constructorName : Name
  constructorInfo : ConstructorVal
  recursorInfo : RecursorVal
  family_find : env.find? familyName = some (.inductInfo familyInfo)
  constructor_find : env.find? constructorName =
    some (.ctorInfo constructorInfo)
  structure_test : env.isNonRecStructureConstructor familyName
    constructorName = true
  recursor_find : env.find? (mkRecName familyName) =
    some (.recInfo recursorInfo)

namespace StructureEtaRegistrationObservation

/-- Complete host observations and projection readiness synthesize the exact
entry contributed by this family. -/
noncomputable def toEntry
    (observation : StructureEtaRegistrationObservation env familyName)
    (projectionReady : ProjectionReady env venv) (baseWF : venv.WF) :
    StructureEtaRegistrationEntry env venv where
  familyName := familyName
  familyInfo := observation.familyInfo
  constructorName := observation.constructorName
  constructorInfo := observation.constructorInfo
  artifact := Classical.choice <|
    StructureEtaRegistrationArtifact.ofProjectionReady projectionReady baseWF
      observation.family_find observation.constructor_find
      observation.structure_test observation.recursor_find

/-- The family record selected by complete observations at a fixed name is
unique. -/
theorem familyInfo_eq
    (left right : StructureEtaRegistrationObservation env familyName) :
    left.familyInfo = right.familyInfo := by
  have tagged_eq :
      (.inductInfo left.familyInfo : ConstantInfo) =
        .inductInfo right.familyInfo :=
    Option.some.inj (left.family_find.symm.trans right.family_find)
  exact ConstantInfo.inductInfo.inj tagged_eq

/-- The singleton constructor selected by complete observations at a fixed
family name is unique. -/
theorem constructorName_eq
    (left right : StructureEtaRegistrationObservation env familyName) :
    left.constructorName = right.constructorName := by
  obtain ⟨_left_rec, left_ctors, _left_indices, _left_owner⟩ :=
    Kernel.Environment.isNonRecStructureConstructor_info left.family_find
      left.constructor_find left.structure_test
  obtain ⟨_right_rec, right_ctors, _right_indices, _right_owner⟩ :=
    Kernel.Environment.isNonRecStructureConstructor_info right.family_find
      right.constructor_find right.structure_test
  have family_info_eq := left.familyInfo_eq right
  rw [family_info_eq] at left_ctors
  have singleton_eq : [left.constructorName] = [right.constructorName] :=
    left_ctors.symm.trans right_ctors
  simpa using singleton_eq

/-- Constructor metadata selected by complete observations at a fixed family
name is unique. -/
theorem constructorInfo_eq
    (left right : StructureEtaRegistrationObservation env familyName) :
    left.constructorInfo = right.constructorInfo := by
  have constructor_name_eq := left.constructorName_eq right
  have left_constructor_find := left.constructor_find
  rw [constructor_name_eq] at left_constructor_find
  have tagged_eq :
      (.ctorInfo left.constructorInfo : ConstantInfo) =
        .ctorInfo right.constructorInfo :=
    Option.some.inj
      (left_constructor_find.symm.trans right.constructor_find)
  exact ConstantInfo.ctorInfo.inj tagged_eq

end StructureEtaRegistrationObservation

/-- Global classification of every host family accepted by the
nonrecursive-structure heuristic.  A family is either already ready in the
transaction model or is backed by an exact registration artifact whose rule
occurs in the shared completion list. -/
def StructureEtaRegistrationCoverage
    (env : Environment) (venv : VEnv) (rules : List VStructEta) : Prop :=
  ∀ familyName familyInfo constructorName constructorInfo,
    env.find? familyName = some (.inductInfo familyInfo) →
    env.find? constructorName = some (.ctorInfo constructorInfo) →
    env.isNonRecStructureConstructor familyName constructorName = true →
    Nonempty (StructureEtaArtifact env familyName familyInfo constructorName
      constructorInfo venv) ∨
      ∃ registration : StructureEtaRegistrationArtifact env familyName
          familyInfo constructorName constructorInfo venv,
        registration.rule ∈ rules

/-- A finite artifact inventory together with the exact classification that
every host nonrecursive structure is old or represented by one of its
entries.  The shared rule list is derived from this inventory. -/
structure StructureEtaRegistrationPlan
    (env : Environment) (venv : VEnv) where
  entries : List (StructureEtaRegistrationEntry env venv)
  coverage : ∀ familyName familyInfo constructorName constructorInfo,
    env.find? familyName = some (.inductInfo familyInfo) →
    env.find? constructorName = some (.ctorInfo constructorInfo) →
    env.isNonRecStructureConstructor familyName constructorName = true →
    Nonempty (StructureEtaArtifact env familyName familyInfo constructorName
      constructorInfo venv) ∨
      ∃ entry ∈ entries,
        entry.familyName = familyName ∧
        entry.familyInfo = familyInfo ∧
        entry.constructorName = constructorName ∧
        entry.constructorInfo = constructorInfo

namespace StructureEtaRegistrationPlan

/-- Select a registration entry exactly when a family name has complete host
structure and recursor observations. -/
noncomputable def entryForFamily?
    (projectionReady : ProjectionReady env venv) (baseWF : venv.WF)
    (familyName : Name) : Option (StructureEtaRegistrationEntry env venv) := by
  classical
  exact if observations : Nonempty
      (StructureEtaRegistrationObservation env familyName) then
    some ((Classical.choice observations).toEntry projectionReady baseWF)
  else
    none

/-- Deterministic artifact inventory selected from a finite family-name
inventory. -/
noncomputable def entriesForFamilies
    (projectionReady : ProjectionReady env venv) (baseWF : venv.WF)
    (familyNames : List Name) :
    List (StructureEtaRegistrationEntry env venv) :=
  familyNames.filterMap (entryForFamily? projectionReady baseWF)

/-- The deterministic common rule list owned by a registration plan. -/
noncomputable def rules
    (plan : StructureEtaRegistrationPlan env venv) : List VStructEta :=
  plan.entries.map StructureEtaRegistrationEntry.rule

/-- All rules derived from a registration plan are persistently well formed
in its base model. -/
theorem rulesWF (plan : StructureEtaRegistrationPlan env venv) :
    ∀ rule ∈ plan.rules, rule.WF venv := by
  intro rule member
  obtain ⟨entry, _entry_member, rfl⟩ := List.mem_map.mp member
  exact entry.ruleWF

/-- Forget the finite entry packaging to the coverage relation consumed by
the generic completion theorem. -/
theorem toCoverage (plan : StructureEtaRegistrationPlan env venv) :
    StructureEtaRegistrationCoverage env venv plan.rules := by
  intro familyName familyInfo constructorName constructorInfo family_find
    constructor_find structure_test
  rcases plan.coverage familyName familyInfo constructorName constructorInfo
      family_find constructor_find structure_test with
    existing |
      ⟨entry, entry_member, family_name_eq, family_info_eq,
        constructor_name_eq, constructor_info_eq⟩
  · exact .inl existing
  · subst familyName
    subst familyInfo
    subst constructorName
    subst constructorInfo
    exact .inr ⟨entry.artifact,
      List.mem_map.mpr ⟨entry, entry_member, rfl⟩⟩

/-- Build the finite registration plan by scanning a family-name inventory.
The only classification premise left to callers says that every accepted
host structure is either already ready or its family name occurs in the
inventory and its generated recursor is present. -/
noncomputable def ofFamilyNames
    (projectionReady : ProjectionReady env venv) (baseWF : venv.WF)
    (familyNames : List Name)
    (coverage : ∀ familyName familyInfo constructorName constructorInfo,
      env.find? familyName = some (.inductInfo familyInfo) →
      env.find? constructorName = some (.ctorInfo constructorInfo) →
      env.isNonRecStructureConstructor familyName constructorName = true →
      Nonempty (StructureEtaArtifact env familyName familyInfo constructorName
        constructorInfo venv) ∨
        familyName ∈ familyNames ∧
          ∃ recursorInfo, env.find? (mkRecName familyName) =
            some (.recInfo recursorInfo)) :
    StructureEtaRegistrationPlan env venv where
  entries := entriesForFamilies projectionReady baseWF familyNames
  coverage := by
    intro familyName familyInfo constructorName constructorInfo family_find
      constructor_find structure_test
    rcases coverage familyName familyInfo constructorName constructorInfo
        family_find constructor_find structure_test with
      existing | ⟨family_member, recursorInfo, recursor_find⟩
    · exact .inl existing
    · let observation : StructureEtaRegistrationObservation env familyName := {
        familyInfo := familyInfo
        constructorName := constructorName
        constructorInfo := constructorInfo
        recursorInfo := recursorInfo
        family_find := family_find
        constructor_find := constructor_find
        structure_test := structure_test
        recursor_find := recursor_find }
      have observations : Nonempty
          (StructureEtaRegistrationObservation env familyName) :=
        ⟨observation⟩
      let selected := Classical.choice observations
      let entry := selected.toEntry projectionReady baseWF
      have entry_member : entry ∈
          entriesForFamilies projectionReady baseWF familyNames := by
        apply List.mem_filterMap.mpr
        refine ⟨familyName, family_member, ?_⟩
        simp only [entryForFamily?, dif_pos observations, entry, selected]
      refine .inr ⟨entry, entry_member, rfl, ?_, ?_, ?_⟩
      · exact selected.familyInfo_eq observation
      · exact selected.constructorName_eq observation
      · exact selected.constructorInfo_eq observation

end StructureEtaRegistrationPlan

/-- Coverage by one fixed rule list persists through a well-formed Theory
model extension.  Existing final artifacts are transported directly; a
pending registration keeps the same proof-irrelevant rule value. -/
theorem StructureEtaRegistrationCoverage.mono
    (coverage : StructureEtaRegistrationCoverage env venv rules)
    (hle : venv ≤ venv') (wf' : venv'.WF) :
    StructureEtaRegistrationCoverage env venv' rules := by
  intro familyName familyInfo constructorName constructorInfo
    family_find constructor_find structure_test
  rcases coverage familyName familyInfo constructorName constructorInfo
      family_find constructor_find structure_test with
    existing | ⟨registration, member⟩
  · obtain ⟨artifact⟩ := existing
    exact .inl ⟨artifact.mono hle wf'.ordered⟩
  · let transported := registration.mono hle wf'
    refine .inr ⟨transported, ?_⟩
    have rule_eq : registration.rule = transported.rule := by
      simpa only [transported, StructureEtaRegistrationArtifact.rule,
        StructureEtaRegistrationArtifact.mono] using
        registration.rule_mono_eq hle wf'
    rwa [← rule_eq]

/-- Checked registration plus complete host-family classification constructs
the final global structure-eta readiness invariant. -/
theorem StructureEtaRegistrationCoverage.toStructureEtaReady
    (coverage : StructureEtaRegistrationCoverage env venv rules)
    (completion : VEnv.AddStructEtas venv rules venv') :
    StructureEtaReady env venv' where
  resolve familyName familyInfo constructorName constructorInfo
      hfamily hconstructor hnonrec := by
    rcases coverage familyName familyInfo constructorName constructorInfo
        hfamily hconstructor hnonrec with existing | ⟨registration, member⟩
    · obtain ⟨artifact⟩ := existing
      exact ⟨artifact.mono completion.le
        (completion.ordered artifact.etaOrdered)⟩
    · exact ⟨registration.toStructureEtaArtifact_of_completion
        completion member⟩

/--
info: 'Lean4Lean.StructureEtaRegistrationArtifact.toAddStructEtas' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms StructureEtaRegistrationArtifact.toAddStructEtas

/--
info: 'Lean4Lean.StructureEtaRegistrationArtifact.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms StructureEtaRegistrationArtifact.mono

/--
info: 'Lean4Lean.StructureEtaRegistrationArtifact.toStructureEtaArtifact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms StructureEtaRegistrationArtifact.toStructureEtaArtifact

/--
info: 'Lean4Lean.StructureEtaRegistrationArtifact.toStructureEtaArtifact_of_completion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms StructureEtaRegistrationArtifact.toStructureEtaArtifact_of_completion

/--
info: 'Lean4Lean.StructureEtaRegistrationCoverage.toStructureEtaReady' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms StructureEtaRegistrationCoverage.toStructureEtaReady

/--
info: 'Lean4Lean.ProjectionArtifact.rebuildWF' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ProjectionArtifact.rebuildWF

/--
info: 'Lean4Lean.StructureEtaRegistrationArtifact.ofRebuilds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms StructureEtaRegistrationArtifact.ofRebuilds

theorem safePrimitives_add' {env : Environment} (mapWF : env.constants.WF)
    (old : ∀ {n : Name} {ci}, env.find? n = some ci →
      Environment.primitives.contains n → ci.safety = .safe ∧ ci.levelParams = [])
    (ci : ConstantInfo) (hfresh : env.find? ci.name = none)
    (hok : Environment.primitives.contains ci.name → ci.safety = .safe ∧ ci.levelParams = [])
    (hfind : (env.add ci).find? (n : Name) = some ci')
    (hp : Environment.primitives.contains n) : ci'.safety = .safe ∧ ci'.levelParams = [] := by
  have hnone : env.constants.find? ci.name = none := by
    rw [← mapWF.find?'_eq_find?]; exact hfresh
  have mapWF' := mapWF.insert ci.name ci hnone
  change SMap.find?' (env.constants.insert ci.name ci) n = some ci' at hfind
  rw [mapWF'.find?'_eq_find?, mapWF.find?_insert] at hfind
  split at hfind
  · cases hfind; cases LawfulBEq.eq_of_beq ‹_›; exact hok hp
  · refine old ?_ hp; rwa [Kernel.Environment.find?, mapWF.find?'_eq_find?]

theorem VEnvs.WF.safePrimitives_add {ves : VEnvs} {env : Environment}
    (wf : ves.WF env) (ci : ConstantInfo)
    (hfresh : env.find? ci.name = none)
    (hok : Environment.primitives.contains ci.name →
      ci.safety = .safe ∧ ci.levelParams = [])
    (hfind : (env.add ci).find? (n : Name) = some ci')
    (hp : Environment.primitives.contains n) : ci'.safety = .safe ∧ ci'.levelParams = [] :=
  safePrimitives_add' (wf.tr (safety := .safe)).map_wf wf.safePrimitives ci hfresh hok hfind hp

theorem VEnvAt.safePrimitives_add {env : Environment} {venv : VEnv}
    (wf : VEnvAt env safety venv) (ci : ConstantInfo)
    (hfresh : env.find? ci.name = none)
    (hok : Environment.primitives.contains ci.name →
      ci.safety = .safe ∧ ci.levelParams = [])
    (hfind : (env.add ci).find? (n : Name) = some ci')
    (hp : Environment.primitives.contains n) : ci'.safety = .safe ∧ ci'.levelParams = [] :=
  safePrimitives_add' wf.tr.map_wf wf.safePrimitives ci hfresh hok hfind hp

theorem VEnv.HasPrimitives.addConsts {env env' : VEnv} : ∀ {cis : List VDefVal},
    env.HasPrimitives → (∀ ci ∈ cis, Environment.primitives.contains ci.name = false) →
    env.addConsts cis = some env' → env'.HasPrimitives
  | [], H, _, e => by cases e; exact H
  | _ :: _, H, hn, e => by
    simp [VEnv.addConsts, Option.bind_eq_some_iff] at e
    obtain ⟨_, h1, h2⟩ := e
    exact addConsts (H.addConst_of_not_primitive (hn _ (.head _)) h1) (fun c hc => hn c (.tail _ hc)) h2

theorem VEnv.HasPrimitives.addDefEqs {env : VEnv} : ∀ {cis : List VDefVal},
    env.HasPrimitives → (env.addDefEqs cis).HasPrimitives
  | [], H => H
  | _ :: cis, H => addDefEqs (cis := cis) H.addDefEq

/-! ## Primitive reflection across inductive transactions -/

/-- Kernel-side primitive safety stated directly on a constant map.  This
map form composes through the exact `AddInductConstant` folds and is converted
to/from `Environment.find?` only at the public boundary. -/
def ConstMapSafePrimitives (map : ConstMap) : Prop :=
  ∀ {n ci}, map.find? n = some ci →
    Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = []

/-- Re-express an environment's primitive-safety invariant on its lawful
constant map. -/
theorem ConstMapSafePrimitives.ofEnvironment
    {env : Environment} (mapWF : env.constants.WF)
    (safe : ∀ {n ci}, env.find? n = some ci →
      Environment.primitives.contains n →
        ci.safety = .safe ∧ ci.levelParams = []) :
    ConstMapSafePrimitives env.constants := by
  intro n ci found primitive
  apply safe (n := n) (ci := ci)
  · rwa [Kernel.Environment.find?, mapWF.find?'_eq_find?]
  · exact primitive

/-- Recover the public environment form from a lawful constant map. -/
theorem ConstMapSafePrimitives.toEnvironment
    {env : Environment} (safe : ConstMapSafePrimitives env.constants)
    (mapWF : env.constants.WF) :
    ∀ {n ci}, env.find? n = some ci →
      Environment.primitives.contains n →
        ci.safety = .safe ∧ ci.levelParams = [] := by
  intro n ci found primitive
  apply safe (n := n) (ci := ci)
  · rwa [Kernel.Environment.find?, mapWF.find?'_eq_find?] at found
  · exact primitive

/-- One exact metadata insertion preserves kernel primitive safety when its
new name is not a kernel primitive. -/
theorem AddInductConstant.safePrimitivesMap
    (H : AddInductConstant kind m₁ env₁ raw m₂ env₂)
    (mapWF : m₁.WF) (pre : ConstMapSafePrimitives m₁)
    (name : Environment.primitives.contains raw.name = false) :
    ConstMapSafePrimitives m₂ := by
  intro n ci found primitive
  rw [H.map_add, mapWF.find?_insert] at found
  split at found
  · rename_i equal
    have name_eq : raw.name = n := by simpa using equal
    subst n
    rw [name] at primitive
    contradiction
  · exact pre found primitive

/-- One exact metadata insertion preserves kernel primitive safety when the
inserted metadata itself satisfies the public primitive-safety contract. -/
theorem AddInductConstant.safePrimitivesMap_of
    (H : AddInductConstant kind m₁ env₁ raw m₂ env₂)
    (mapWF : m₁.WF) (pre : ConstMapSafePrimitives m₁)
    (inserted : Environment.primitives.contains raw.name →
      H.info.safety = .safe ∧ H.info.levelParams = []) :
    ConstMapSafePrimitives m₂ := by
  intro n ci found primitive
  rw [H.map_add, mapWF.find?_insert] at found
  split at found
  · rename_i equal
    have name_eq : raw.name = n := by simpa using equal
    subst n
    cases found
    exact inserted primitive
  · exact pre found primitive

/-- A complete source-ordered metadata fold preserves kernel primitive
safety when every inserted name is non-primitive. -/
theorem AddInductConstants.safePrimitivesMap :
    AddInductConstants kind m₁ env₁ cis m₂ env₂ →
      m₁.WF →
      ConstMapSafePrimitives m₁ →
      (∀ ci ∈ cis,
        Environment.primitives.contains ci.name = false) →
      ConstMapSafePrimitives m₂
  | .nil, _, pre, _ => pre
  | .cons step rest, mapWF, pre, names =>
      rest.safePrimitivesMap
        (by rw [step.map_add]; exact mapWF.insert _ _ step.map_fresh)
      (step.safePrimitivesMap mapWF pre (names _ (.head _)))
      (fun ci member => names ci (.tail _ member))

/-- A source-ordered inductive metadata fold may insert primitive names when
their Theory constants have no universe parameters.  Translation forces the
host metadata to be safe and to have the same zero parameter count. -/
theorem AddInductConstants.safePrimitivesMap_of_zero_uvars :
    AddInductConstants kind m₁ env₁ cis m₂ env₂ →
      m₁.WF →
      ConstMapSafePrimitives m₁ →
      (∀ ci ∈ cis, Environment.primitives.contains ci.name →
        ci.uvars = 0) →
      ConstMapSafePrimitives m₂
  | .nil, _, pre, _ => pre
  | .cons step rest, mapWF, pre, zeroUvars =>
      rest.safePrimitivesMap_of_zero_uvars
        (step.map_wf mapWF)
        (step.safePrimitivesMap_of mapWF pre fun primitive => by
          refine ⟨DefinitionSafety.le_antisymm DefinitionSafety.le_safe
            step.tr.1.1, ?_⟩
          apply List.length_eq_zero_iff.1
          rw [step.tr.1.2.1, zeroUvars _ (.head _) primitive])
        (fun ci member => zeroUvars ci (.tail _ member))

/-- Replaying the same constant list over ordered input models produces
ordered output models. -/
theorem AddInductConstants.mono :
    ∀ (_left : AddInductConstants kind m₁ env₁ cis m₂ env₂)
      (_right : AddInductConstants kind m₁' env₁' cis m₂' env₂'),
      env₁ ≤ env₁' → env₂ ≤ env₂'
  | .nil, .nil, pre => pre
  | .cons left leftRest, .cons right rightRest, pre =>
      leftRest.mono rightRest
        (VEnv.addConst_mono pre left.env_add right.env_add)

/-- Replaying the same rule list is monotone in its input model. -/
theorem AddDefEqs.mono
    (left : AddDefEqs env₁ dfs env₂)
    (right : AddDefEqs env₁' dfs env₂')
    (pre : env₁ ≤ env₁') : env₂ ≤ env₂' := by
  rw [← left.fold_eq, ← right.fold_eq]
  clear left right env₂ env₂'
  induction dfs generalizing env₁ env₁' with
  | nil => exact pre
  | cons rule rules ih =>
      exact ih (VEnv.addDefEq_mono pre)

/-- A source-ordered inductive constant fold preserves primitive reflection
when none of the newly inserted Theory names is one of the reflected
primitive names.  This is intentionally a non-primitive-declaration lemma;
primitive-recognized blocks require their dedicated semantic witnesses. -/
theorem AddInductConstants.hasPrimitives :
    AddInductConstants kind m₁ env₁ cis m₂ env₂ →
      env₁.HasPrimitives →
      (∀ ci ∈ cis, ci.name ∉ VEnv.reflectedPrimitiveNames) →
      env₂.HasPrimitives
  | .nil, pre, _ => pre
  | .cons step rest, pre, names =>
      rest.hasPrimitives
        (pre.addConst (names _ (.head _)) step.env_add)
        (fun ci member => names ci (.tail _ member))

/-- Adding only definitional equations preserves primitive reflection. -/
theorem AddDefEqs.hasPrimitives
    (H : AddDefEqs env₁ dfs env₂) (pre : env₁.HasPrimitives) :
    env₂.HasPrimitives := by
  have preserve : ∀ (rules : List VDefEq) (env : VEnv),
      env.HasPrimitives →
        (rules.foldl VEnv.addDefEq env).HasPrimitives := by
    intro rules
    induction rules with
    | nil => exact fun _ pre => pre
    | cons rule rules ih =>
        intro env pre
        exact ih (env.addDefEq rule) pre.addDefEq
  rw [← H.fold_eq]
  exact preserve dfs env₁ pre

/-- Adding definitional equations does not alter constant lookup. -/
theorem AddDefEqs.constants_eq
    (H : AddDefEqs env₁ dfs env₂) : env₂.constants = env₁.constants := by
  rw [← H.fold_eq]
  clear H env₂
  induction dfs generalizing env₁ with
  | nil => rfl
  | cons rule rules ih => exact ih

/-- A constant fold leaves an unrelated Theory lookup unchanged. -/
theorem AddInductConstants.constants_eq_of_not_mem
    (H : AddInductConstants kind m₁ env₁ cis m₂ env₂)
    (absent : ∀ ci ∈ cis, ci.name ≠ name) :
    env₂.constants name = env₁.constants name := by
  induction H with
  | nil => rfl
  | cons step rest ih =>
    rw [ih (fun ci member => absent ci (.tail _ member))]
    exact VEnv.addConst_other step.env_add
      (absent _ (.head _))

/-- Installing the canonical Boolean family and its two constructors preserves
all previously reflected primitives and establishes the new Boolean literal
contract.  `other` records that no unrelated primitive lookup changed. -/
theorem VEnv.HasPrimitives.of_addBool
    {input output : VEnv} (pre : input.HasPrimitives)
    (hle : input ≤ output)
    (falseLookup : output.constants ``Bool.false =
      some { uvars := 0, type := .bool })
    (trueLookup : output.constants ``Bool.true =
      some { uvars := 0, type := .bool })
    (other : ∀ n, n ∈ VEnv.reflectedPrimitiveNames →
      n ≠ ``Bool → n ≠ ``Bool.false →
      n ≠ ``Bool.true → output.constants n = input.constants n) :
    output.HasPrimitives := by
  have oldContains (n : Name) (member : n ∈ VEnv.reflectedPrimitiveNames)
      (hBool : n ≠ ``Bool)
      (hFalse : n ≠ ``Bool.false) (hTrue : n ≠ ``Bool.true) :
      output.contains n → input.contains n := by
    rintro ⟨ci, found⟩
    exact ⟨ci, by
      simpa only [other n member hBool hFalse hTrue] using found⟩
  have newContains (n : Name) : input.contains n → output.contains n := by
    rintro ⟨ci, found⟩
    exact ⟨ci, hle.constants found⟩
  have oldLookup (n : Name) (member : n ∈ VEnv.reflectedPrimitiveNames)
      (hBool : n ≠ ``Bool)
      (hFalse : n ≠ ``Bool.false) (hTrue : n ≠ ``Bool.true)
      {ci : VConstant} (found : output.constants n = some ci) :
      input.constants n = some ci := by
    simpa only [other n member hBool hFalse hTrue] using found
  exact {
    bool := fun _ => ⟨⟨_, falseLookup⟩, ⟨_, trueLookup⟩⟩
    boolFalse := fun found => Option.some.inj (found.symm.trans falseLookup)
    boolTrue := fun found => Option.some.inj (found.symm.trans trueLookup)
    nat := fun found => by
      obtain ⟨zero, succ⟩ := pre.nat
        (oldContains ``Nat (by simp [VEnv.reflectedPrimitiveNames])
          (by simp) (by simp) (by simp) found)
      exact ⟨newContains _ zero, newContains _ succ⟩
    natZero := fun found => pre.natZero
      (oldLookup ``Nat.zero (by simp [VEnv.reflectedPrimitiveNames])
        (by simp) (by simp) (by simp) found)
    natSucc := fun found => pre.natSucc
      (oldLookup ``Nat.succ (by simp [VEnv.reflectedPrimitiveNames])
        (by simp) (by simp) (by simp) found)
    natPred := fun found => by
      obtain ⟨htype, heval⟩ := pre.natPred
        (oldContains ``Nat.pred (by simp [VEnv.reflectedPrimitiveNames])
          (by simp) (by simp) (by simp) found)
      exact ⟨fun U Γ => (htype U Γ).mono hle,
        fun a => (heval a).mono hle⟩
    natAdd := pre.natAdd.mono_of_contains hle fun found =>
      oldContains ``Nat.add (by simp [VEnv.reflectedPrimitiveNames])
        (by simp) (by simp) (by simp) found
    natSub := pre.natSub.mono_of_contains hle fun found =>
      oldContains ``Nat.sub (by simp [VEnv.reflectedPrimitiveNames])
        (by simp) (by simp) (by simp) found
    natMul := pre.natMul.mono_of_contains hle fun found =>
      oldContains ``Nat.mul (by simp [VEnv.reflectedPrimitiveNames])
        (by simp) (by simp) (by simp) found
    natPow := pre.natPow.mono_of_contains hle fun found =>
      oldContains ``Nat.pow (by simp [VEnv.reflectedPrimitiveNames])
        (by simp) (by simp) (by simp) found
    natGcd := pre.natGcd.mono_of_contains hle fun found =>
      oldContains ``Nat.gcd (by simp [VEnv.reflectedPrimitiveNames])
        (by simp) (by simp) (by simp) found
    natMod := pre.natMod.mono_of_contains hle fun found =>
      oldContains ``Nat.mod (by simp [VEnv.reflectedPrimitiveNames])
        (by simp) (by simp) (by simp) found
    natDiv := pre.natDiv.mono_of_contains hle fun found =>
      oldContains ``Nat.div (by simp [VEnv.reflectedPrimitiveNames])
        (by simp) (by simp) (by simp) found
    natBEq := pre.natBEq.mono_of_contains hle fun found =>
      oldContains ``Nat.beq (by simp [VEnv.reflectedPrimitiveNames])
        (by simp) (by simp) (by simp) found
    natBLE := pre.natBLE.mono_of_contains hle fun found =>
      oldContains ``Nat.ble (by simp [VEnv.reflectedPrimitiveNames])
        (by simp) (by simp) (by simp) found
    natLAnd := pre.natLAnd.mono_of_contains hle fun found =>
      oldContains ``Nat.land (by simp [VEnv.reflectedPrimitiveNames])
        (by simp) (by simp) (by simp) found
    natLOr := pre.natLOr.mono_of_contains hle fun found =>
      oldContains ``Nat.lor (by simp [VEnv.reflectedPrimitiveNames])
        (by simp) (by simp) (by simp) found
    natXor := pre.natXor.mono_of_contains hle fun found =>
      oldContains ``Nat.xor (by simp [VEnv.reflectedPrimitiveNames])
        (by simp) (by simp) (by simp) found
    natShiftLeft := pre.natShiftLeft.mono_of_contains hle fun found =>
      oldContains ``Nat.shiftLeft (by simp [VEnv.reflectedPrimitiveNames])
        (by simp) (by simp) (by simp) found
    natShiftRight := pre.natShiftRight.mono_of_contains hle fun found =>
      oldContains ``Nat.shiftRight (by simp [VEnv.reflectedPrimitiveNames])
        (by simp) (by simp) (by simp) found
    charOfNat := fun found => by
      obtain ⟨hu, hty⟩ := pre.charOfNat
        (oldLookup ``Char.ofNat (by simp [VEnv.reflectedPrimitiveNames])
          (by simp) (by simp) (by simp) found)
      exact ⟨hu, fun U Γ => (hty U Γ).mono hle⟩
    stringOfList := fun found =>
      let ⟨hu, hty, nilType, consType⟩ := pre.stringOfList
        (oldLookup ``String.ofList
          (by simp [VEnv.reflectedPrimitiveNames])
          (by simp) (by simp) (by simp) found)
      ⟨hu, fun U Γ => (hty U Γ).mono hle,
        nilType.mono hle, consType.mono hle⟩ }

/-- Installing the canonical natural-number family and constructors preserves
all previously reflected primitives and establishes the new natural literal
contract. -/
theorem VEnv.HasPrimitives.of_addNat
    {input output : VEnv} (pre : input.HasPrimitives)
    (hle : input ≤ output)
    (zeroLookup : output.constants ``Nat.zero =
      some { uvars := 0, type := .nat })
    (succLookup : output.constants ``Nat.succ =
      some { uvars := 0, type := .forallE .nat .nat })
    (other : ∀ n, n ∈ VEnv.reflectedPrimitiveNames →
      n ≠ ``Nat → n ≠ ``Nat.zero →
      n ≠ ``Nat.succ → output.constants n = input.constants n) :
    output.HasPrimitives := by
  have oldContains (n : Name) (member : n ∈ VEnv.reflectedPrimitiveNames)
      (hNat : n ≠ ``Nat)
      (hZero : n ≠ ``Nat.zero) (hSucc : n ≠ ``Nat.succ) :
      output.contains n → input.contains n := by
    rintro ⟨ci, found⟩
    exact ⟨ci, by
      simpa only [other n member hNat hZero hSucc] using found⟩
  have newContains (n : Name) : input.contains n → output.contains n := by
    rintro ⟨ci, found⟩
    exact ⟨ci, hle.constants found⟩
  have oldLookup (n : Name) (member : n ∈ VEnv.reflectedPrimitiveNames)
      (hNat : n ≠ ``Nat)
      (hZero : n ≠ ``Nat.zero) (hSucc : n ≠ ``Nat.succ)
      {ci : VConstant} (found : output.constants n = some ci) :
      input.constants n = some ci := by
    simpa only [other n member hNat hZero hSucc] using found
  exact {
    bool := fun found => by
      obtain ⟨falsePresent, truePresent⟩ := pre.bool
        (oldContains ``Bool (by simp [VEnv.reflectedPrimitiveNames])
          (by simp) (by simp) (by simp) found)
      exact ⟨newContains _ falsePresent, newContains _ truePresent⟩
    boolFalse := fun found => pre.boolFalse
      (oldLookup ``Bool.false (by simp [VEnv.reflectedPrimitiveNames])
        (by simp) (by simp) (by simp) found)
    boolTrue := fun found => pre.boolTrue
      (oldLookup ``Bool.true (by simp [VEnv.reflectedPrimitiveNames])
        (by simp) (by simp) (by simp) found)
    nat := fun _ => ⟨⟨_, zeroLookup⟩, ⟨_, succLookup⟩⟩
    natZero := fun found => Option.some.inj (found.symm.trans zeroLookup)
    natSucc := fun found => Option.some.inj (found.symm.trans succLookup)
    natPred := fun found => by
      obtain ⟨htype, heval⟩ := pre.natPred
        (oldContains ``Nat.pred (by simp [VEnv.reflectedPrimitiveNames])
          (by simp) (by simp) (by simp) found)
      exact ⟨fun U Γ => (htype U Γ).mono hle,
        fun a => (heval a).mono hle⟩
    natAdd := pre.natAdd.mono_of_contains hle fun found =>
      oldContains ``Nat.add (by simp [VEnv.reflectedPrimitiveNames])
        (by simp) (by simp) (by simp) found
    natSub := pre.natSub.mono_of_contains hle fun found =>
      oldContains ``Nat.sub (by simp [VEnv.reflectedPrimitiveNames])
        (by simp) (by simp) (by simp) found
    natMul := pre.natMul.mono_of_contains hle fun found =>
      oldContains ``Nat.mul (by simp [VEnv.reflectedPrimitiveNames])
        (by simp) (by simp) (by simp) found
    natPow := pre.natPow.mono_of_contains hle fun found =>
      oldContains ``Nat.pow (by simp [VEnv.reflectedPrimitiveNames])
        (by simp) (by simp) (by simp) found
    natGcd := pre.natGcd.mono_of_contains hle fun found =>
      oldContains ``Nat.gcd (by simp [VEnv.reflectedPrimitiveNames])
        (by simp) (by simp) (by simp) found
    natMod := pre.natMod.mono_of_contains hle fun found =>
      oldContains ``Nat.mod (by simp [VEnv.reflectedPrimitiveNames])
        (by simp) (by simp) (by simp) found
    natDiv := pre.natDiv.mono_of_contains hle fun found =>
      oldContains ``Nat.div (by simp [VEnv.reflectedPrimitiveNames])
        (by simp) (by simp) (by simp) found
    natBEq := pre.natBEq.mono_of_contains hle fun found =>
      oldContains ``Nat.beq (by simp [VEnv.reflectedPrimitiveNames])
        (by simp) (by simp) (by simp) found
    natBLE := pre.natBLE.mono_of_contains hle fun found =>
      oldContains ``Nat.ble (by simp [VEnv.reflectedPrimitiveNames])
        (by simp) (by simp) (by simp) found
    natLAnd := pre.natLAnd.mono_of_contains hle fun found =>
      oldContains ``Nat.land (by simp [VEnv.reflectedPrimitiveNames])
        (by simp) (by simp) (by simp) found
    natLOr := pre.natLOr.mono_of_contains hle fun found =>
      oldContains ``Nat.lor (by simp [VEnv.reflectedPrimitiveNames])
        (by simp) (by simp) (by simp) found
    natXor := pre.natXor.mono_of_contains hle fun found =>
      oldContains ``Nat.xor (by simp [VEnv.reflectedPrimitiveNames])
        (by simp) (by simp) (by simp) found
    natShiftLeft := pre.natShiftLeft.mono_of_contains hle fun found =>
      oldContains ``Nat.shiftLeft (by simp [VEnv.reflectedPrimitiveNames])
        (by simp) (by simp) (by simp) found
    natShiftRight := pre.natShiftRight.mono_of_contains hle fun found =>
      oldContains ``Nat.shiftRight (by simp [VEnv.reflectedPrimitiveNames])
        (by simp) (by simp) (by simp) found
    charOfNat := fun found => by
      obtain ⟨hu, hty⟩ := pre.charOfNat
        (oldLookup ``Char.ofNat (by simp [VEnv.reflectedPrimitiveNames])
          (by simp) (by simp) (by simp) found)
      exact ⟨hu, fun U Γ => (hty U Γ).mono hle⟩
    stringOfList := fun found =>
      let ⟨hu, hty, nilType, consType⟩ := pre.stringOfList
        (oldLookup ``String.ofList
          (by simp [VEnv.reflectedPrimitiveNames])
          (by simp) (by simp) (by simp) found)
      ⟨hu, fun U Γ => (hty U Γ).mono hle,
        nilType.mono hle, consType.mono hle⟩ }

/-! ## Canonical primitive-inductive inventories -/

namespace VPrimitiveInductive

/-- The Theory constant emitted for the canonical Boolean family. -/
def boolFamily : VConstVal :=
  ⟨⟨0, .sort (.succ .zero)⟩, ``Bool⟩

/-- The Theory constants emitted for the canonical Boolean constructors. -/
def boolConstructors : List VConstVal := [
  ⟨⟨0, .bool⟩, ``Bool.false⟩,
  ⟨⟨0, .bool⟩, ``Bool.true⟩]

/-- The complete canonical Theory family selected for a recognized Boolean
inductive declaration. -/
def boolType : VInductiveType where
  name := ``Bool
  uvars := 0
  type := .sort (.succ .zero)
  ctors := boolConstructors

/-- The complete canonical Theory declaration for `Bool`. -/
def boolDecl : VInductDecl := ⟨0, 0, [boolType]⟩

/-- The Theory constant emitted for the canonical natural-number family. -/
def natFamily : VConstVal :=
  ⟨⟨0, .sort (.succ .zero)⟩, ``Nat⟩

/-- The Theory constants emitted for the canonical natural constructors. -/
def natConstructors : List VConstVal := [
  ⟨⟨0, .nat⟩, ``Nat.zero⟩,
  ⟨⟨0, .forallE .nat .nat⟩, ``Nat.succ⟩]

/-- The complete canonical Theory family selected for a recognized natural
number inductive declaration. -/
def natType : VInductiveType where
  name := ``Nat
  uvars := 0
  type := .sort (.succ .zero)
  ctors := natConstructors

/-- The complete canonical Theory declaration for `Nat`. -/
def natDecl : VInductDecl := ⟨0, 0, [natType]⟩

/-- Select the canonical Theory declaration represented by a primitive host
source.  Its semantic contract is stated separately under
`PrimitiveInductiveShape`; outside that recognized domain the fallback is
irrelevant. -/
def canonicalDecl (types : List Lean.InductiveType) : VInductDecl :=
  if types.any fun type => type.name == ``Bool then boolDecl else natDecl

/-- The unique identity block generation for the canonical Boolean source. -/
def boolGeneration : boolDecl.BlockGenerationChecked :=
  boolDecl.identityBlockGeneration?.get (by decide)

/-- The unique identity block generation for the canonical natural-number
source. -/
def natGeneration : natDecl.BlockGenerationChecked :=
  natDecl.identityBlockGeneration?.get (by decide)

/-- Select the fixed checked generation paired with `canonicalDecl`.  Primitive
replay producers choose neither the raw declaration nor its generated Theory
inventory. -/
def canonicalGeneration (types : List Lean.InductiveType) :
    (canonicalDecl types).BlockGenerationChecked := by
  unfold canonicalDecl
  split
  · exact boolGeneration
  · exact natGeneration

/--
info: 'Lean4Lean.VPrimitiveInductive.canonicalGeneration' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VPrimitiveInductive.canonicalGeneration

/-- The canonical Boolean generation is semantically well formed in any
input model where staging its sole family produces `blockEnv`. -/
theorem boolGeneration_wf {env blockEnv : VEnv}
    (hadd : env.addConst boolType.name boolType.toVConstant = some blockEnv) :
    boolGeneration.WF env blockEnv := by
  have families_eq : boolGeneration.families =
      [boolGeneration.families[0]] := by rfl
  have constructors_eq : boolGeneration.flatCtors =
      [boolGeneration.flatCtors[0], boolGeneration.flatCtors[1]] := by rfl
  refine {
    blockWF := ?_
    resultLevelWF := ?_
    paramsTel := ?_
    families := ?_
    constructors := ?_ }
  · refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · simpa [VEnv.stageInductiveTypes, boolDecl] using hadd
      · change List.Forall₂
            (fun raw view =>
              env.IsDefEqU 0 [] raw.type view.type ∧
                List.Forall₂
                  (fun rawCtor viewCtor =>
                    blockEnv.IsDefEqU 0 [] rawCtor.type viewCtor.type)
                  raw.ctors view.ctors)
            [boolType] [boolType]
        apply List.Forall₂.cons
        · constructor
          · exact ⟨_, .sortDF (by decide) (by decide) rfl⟩
          · apply List.Forall₂.cons
            · exact ⟨_, VEnv.HasType.const
                (VEnv.addConst_self hadd) (by simp) rfl⟩
            · apply List.Forall₂.cons
              · exact ⟨_, VEnv.HasType.const
                  (VEnv.addConst_self hadd) (by simp) rfl⟩
              · exact .nil
        · exact .nil
    · unfold VInductDecl.CheckedBlock.WF
      change VInductDecl.checkedFamilyListsWF boolDecl [] env
        (.succ .zero) [[]] [(.succ .zero)] [[]]
          [boolType.ctors.map
            (VInductDecl.CheckedCtor.ofBlock boolDecl)]
      simp only [VInductDecl.checkedFamilyListsWF]
      refine ⟨rfl, trivial, ?_, trivial⟩
      intro constructor member
      simp [boolType, boolConstructors] at member
      rcases member with rfl | rfl
      · exact ⟨trivial, .nil⟩
      · exact ⟨trivial, .nil⟩
  · decide
  · change True
    trivial
  · intro family member
    rw [families_eq] at member
    simp only [List.mem_singleton] at member
    subst family
    refine { familyTel := ?_, familyResult := ?_ }
    · change True
      trivial
    · change env.IsDefEq 0 [] (.sort (.succ .zero))
          (.sort (.succ .zero)) (.sort (.succ (.succ .zero)))
      exact .sortDF (by decide) (by decide) rfl
  · intro constructor member
    rw [constructors_eq] at member
    simp at member
    rcases member with rfl | rfl
    · refine {
        declaredTel := ?_
        declaredResult := ?_
        emittedTel := ?_
        emittedResult := ?_
        owner := ?_
        recursive := ?_
        resultSpine := ?_ }
      · change True
        trivial
      · change blockEnv.IsDefEq 0 [] .bool .bool (.sort (.succ .zero))
        exact VEnv.HasType.const (VEnv.addConst_self hadd) (by simp) rfl
      · change True
        trivial
      · change blockEnv.IsDefEq 0 [] .bool .bool (.sort (.succ .zero))
        exact VEnv.HasType.const (VEnv.addConst_self hadd) (by simp) rfl
      · refine ⟨boolGeneration.families[0], ?_, rfl, rfl, rfl⟩
        exact List.getElem_mem (l := boolGeneration.families)
          (n := 0) (by decide)
      · intro recursive member
        change recursive ∈ [] at member
        simp at member
      · change blockEnv.SpineWF 0 [] (.sort (.succ .zero)) []
          (.sort (.succ .zero))
        exact .nil
    · refine {
        declaredTel := ?_
        declaredResult := ?_
        emittedTel := ?_
        emittedResult := ?_
        owner := ?_
        recursive := ?_
        resultSpine := ?_ }
      · change True
        trivial
      · change blockEnv.IsDefEq 0 [] .bool .bool (.sort (.succ .zero))
        exact VEnv.HasType.const (VEnv.addConst_self hadd) (by simp) rfl
      · change True
        trivial
      · change blockEnv.IsDefEq 0 [] .bool .bool (.sort (.succ .zero))
        exact VEnv.HasType.const (VEnv.addConst_self hadd) (by simp) rfl
      · refine ⟨boolGeneration.families[0], ?_, rfl, rfl, rfl⟩
        exact List.getElem_mem (l := boolGeneration.families)
          (n := 0) (by decide)
      · intro recursive member
        change recursive ∈ [] at member
        simp at member
      · change blockEnv.SpineWF 0 [] (.sort (.succ .zero)) []
          (.sort (.succ .zero))
        exact .nil

/-- The canonical natural-number generation is semantically well formed in
any input model where staging its sole family produces `blockEnv`. -/
theorem natGeneration_wf {env blockEnv : VEnv}
    (hadd : env.addConst natType.name natType.toVConstant = some blockEnv) :
    natGeneration.WF env blockEnv := by
  have families_eq : natGeneration.families =
      [natGeneration.families[0]] := by rfl
  have constructors_eq : natGeneration.flatCtors =
      [natGeneration.flatCtors[0], natGeneration.flatCtors[1]] := by rfl
  have family_lookup : blockEnv.constants ``Nat =
      some natType.toVConstant := VEnv.addConst_self hadd
  have nat_isType (context : List VExpr) :
      blockEnv.IsType 0 context .nat :=
    ⟨.succ .zero, VEnv.HasType.const family_lookup (by simp) rfl⟩
  have nat_tel : blockEnv.TelDefEq 0 [] [.nat] [.nat] :=
    (show blockEnv.OnTel 0 [] [.nat] from
      ⟨nat_isType [], trivial⟩).telDefEq_refl
  refine {
    blockWF := ?_
    resultLevelWF := ?_
    paramsTel := ?_
    families := ?_
    constructors := ?_ }
  · refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · simpa [VEnv.stageInductiveTypes, natDecl] using hadd
      · change List.Forall₂
            (fun raw view =>
              env.IsDefEqU 0 [] raw.type view.type ∧
                List.Forall₂
                  (fun rawCtor viewCtor =>
                    blockEnv.IsDefEqU 0 [] rawCtor.type viewCtor.type)
                  raw.ctors view.ctors)
            [natType] [natType]
        apply List.Forall₂.cons
        · constructor
          · exact ⟨_, .sortDF (by decide) (by decide) rfl⟩
          · apply List.Forall₂.cons
            · exact ⟨_, VEnv.HasType.const family_lookup (by simp) rfl⟩
            · apply List.Forall₂.cons
              · refine ⟨_, VEnv.HasType.forallE
                  (u := .succ .zero) (v := .succ .zero) ?_ ?_⟩
                · exact VEnv.HasType.const family_lookup (by simp) rfl
                · exact VEnv.HasType.const family_lookup (by simp) rfl
              · exact .nil
        · exact .nil
    · unfold VInductDecl.CheckedBlock.WF
      change VInductDecl.checkedFamilyListsWF natDecl [] env
        (.succ .zero) [[]] [(.succ .zero)] [[]]
          [natType.ctors.map
            (VInductDecl.CheckedCtor.ofBlock natDecl)]
      simp only [VInductDecl.checkedFamilyListsWF]
      refine ⟨rfl, trivial, ?_, trivial⟩
      intro constructor member
      simp [natType, natConstructors] at member
      rcases member with rfl | rfl
      · exact ⟨trivial, .nil⟩
      · exact ⟨⟨⟨rfl, trivial, .nil⟩, trivial⟩, .nil⟩
  · decide
  · change True
    trivial
  · intro family member
    rw [families_eq] at member
    simp only [List.mem_singleton] at member
    subst family
    refine { familyTel := ?_, familyResult := ?_ }
    · change True
      trivial
    · change env.IsDefEq 0 [] (.sort (.succ .zero))
          (.sort (.succ .zero)) (.sort (.succ (.succ .zero)))
      exact .sortDF (by decide) (by decide) rfl
  · intro constructor member
    rw [constructors_eq] at member
    simp at member
    rcases member with rfl | rfl
    · refine {
        declaredTel := ?_
        declaredResult := ?_
        emittedTel := ?_
        emittedResult := ?_
        owner := ?_
        recursive := ?_
        resultSpine := ?_ }
      · change True
        trivial
      · change blockEnv.IsDefEq 0 [] .nat .nat (.sort (.succ .zero))
        exact VEnv.HasType.const family_lookup (by simp) rfl
      · change True
        trivial
      · change blockEnv.IsDefEq 0 [] .nat .nat (.sort (.succ .zero))
        exact VEnv.HasType.const family_lookup (by simp) rfl
      · refine ⟨natGeneration.families[0], ?_, rfl, rfl, rfl⟩
        exact List.getElem_mem (l := natGeneration.families)
          (n := 0) (by decide)
      · intro recursive member
        change recursive ∈ [] at member
        simp at member
      · change blockEnv.SpineWF 0 [] (.sort (.succ .zero)) []
          (.sort (.succ .zero))
        exact .nil
    · refine {
        declaredTel := ?_
        declaredResult := ?_
        emittedTel := ?_
        emittedResult := ?_
        owner := ?_
        recursive := ?_
        resultSpine := ?_ }
      · change blockEnv.TelDefEq 0 [] [.nat] [.nat]
        exact nat_tel
      · change blockEnv.IsDefEq 0 [.nat] .nat .nat (.sort (.succ .zero))
        exact VEnv.HasType.const family_lookup (by simp) rfl
      · change blockEnv.TelDefEq 0 [] [.nat] [.nat]
        exact nat_tel
      · change blockEnv.IsDefEq 0 [.nat] .nat .nat (.sort (.succ .zero))
        exact VEnv.HasType.const family_lookup (by simp) rfl
      · refine ⟨natGeneration.families[0], ?_, rfl, rfl, rfl⟩
        exact List.getElem_mem (l := natGeneration.families)
          (n := 0) (by decide)
      · intro recursive member
        change recursive ∈ [{
          fieldIndex := 0
          binders := []
          targetType := 0
          indices := [] }] at member
        simp only [List.mem_singleton] at member
        subst recursive
        refine ⟨natGeneration.families[0], ?_, rfl, ?_, ?_⟩
        · exact List.getElem_mem (l := natGeneration.families)
            (n := 0) (by decide)
        · exact ⟨.nat, rfl, rfl⟩
        · exact ⟨trivial, .nil⟩
      · change blockEnv.SpineWF 0 [.nat] (.sort (.succ .zero)) []
          (.sort (.succ .zero))
        exact .nil

/--
info: 'Lean4Lean.VPrimitiveInductive.boolGeneration_wf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VPrimitiveInductive.boolGeneration_wf

/--
info: 'Lean4Lean.VPrimitiveInductive.natGeneration_wf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VPrimitiveInductive.natGeneration_wf

end VPrimitiveInductive

/-- Exact Theory inventory associated with a primitive-recognized ordinary
block.  The family and constructor lists are canonical; generated recursors
must avoid every name whose computation is tracked by `HasPrimitives`. -/
inductive VInductDecl.CanonicalPrimitiveConstants
    (decl : VInductDecl) : Prop where
  | bool
      (types_eq : decl.blockTypeConstants =
        [VPrimitiveInductive.boolFamily])
      (constructors_eq : decl.blockConstructorConstants =
        VPrimitiveInductive.boolConstructors) :
      decl.CanonicalPrimitiveConstants
  | nat
      (types_eq : decl.blockTypeConstants =
        [VPrimitiveInductive.natFamily])
      (constructors_eq : decl.blockConstructorConstants =
        VPrimitiveInductive.natConstructors) :
      decl.CanonicalPrimitiveConstants

/-- Canonical primitive constants determine the complete generated inventory.
The only generated names are `Bool.rec` or `Nat.rec`, so their avoidance of
both Theory's reflected names and the host kernel-primitive set is derived
from the source-ordered family inventory rather than supplied separately. -/
inductive VInductDecl.CanonicalPrimitiveInventory
    (decl : VInductDecl) (generation : decl.BlockGenerationChecked) : Prop where
  | bool
      (types_eq : decl.blockTypeConstants =
        [VPrimitiveInductive.boolFamily])
      (constructors_eq : decl.blockConstructorConstants =
        VPrimitiveInductive.boolConstructors)
      (recursorNames : ∀ ci ∈ generation.recursors,
        ci.name ∉ VEnv.reflectedPrimitiveNames ∧
          Environment.primitives.contains ci.name = false) :
      decl.CanonicalPrimitiveInventory generation
  | nat
      (types_eq : decl.blockTypeConstants =
        [VPrimitiveInductive.natFamily])
      (constructors_eq : decl.blockConstructorConstants =
        VPrimitiveInductive.natConstructors)
      (recursorNames : ∀ ci ∈ generation.recursors,
        ci.name ∉ VEnv.reflectedPrimitiveNames ∧
          Environment.primitives.contains ci.name = false) :
      decl.CanonicalPrimitiveInventory generation

/-- Every exact ordinary block trace is a monotone Theory extension. -/
theorem AddInductBlockTrace.le
    (H : AddInductBlockTrace m₁ env₁ decl m₂ env₂) : env₁ ≤ env₂ :=
  H.addTypes.le.trans <| H.addCtors.le.trans <|
    H.addRecs.le.trans H.addRules.le

namespace VInductDecl.CanonicalPrimitiveConstants

/-- Recover the generated-recursors portion of the canonical primitive
inventory from the exact family constants. -/
theorem toInventory
    {decl : VInductDecl} (constants : decl.CanonicalPrimitiveConstants)
    (generation : decl.BlockGenerationChecked) :
    decl.CanonicalPrimitiveInventory generation := by
  have recursorNamesOf
      (familyConstant : VConstVal) (familyName : Name)
      (types_eq : decl.blockTypeConstants = [familyConstant])
      (family_name : familyConstant.name = familyName) :
      ∀ ci ∈ generation.recursors,
        ci.name = .str familyName "rec" := by
    intro ci member
    simp only [BlockGenerationChecked.recursors, List.mem_map] at member
    obtain ⟨family, family_mem, rfl⟩ := member
    have raw_mem : family.raw ∈ decl.types := by
      rw [← generation.families_map_raw]
      exact List.mem_map.2 ⟨family, family_mem, rfl⟩
    have constant_mem : family.raw.toVConstVal ∈ decl.blockTypeConstants := by
      exact List.mem_map.2 ⟨family.raw, raw_mem, rfl⟩
    rw [types_eq] at constant_mem
    have constant_eq : family.raw.toVConstVal = familyConstant :=
      List.mem_singleton.1 constant_mem
    have name_eq : family.raw.name = familyName := by
      exact (congrArg (fun constant : VConstVal => constant.name)
        constant_eq).trans family_name
    simp [name_eq]
  cases constants with
  | bool types_eq constructors_eq =>
      apply CanonicalPrimitiveInventory.bool types_eq constructors_eq
      intro ci member
      have name_eq := recursorNamesOf VPrimitiveInductive.boolFamily ``Bool
        types_eq (by rfl) ci member
      rw [name_eq]
      constructor
      · simp [VEnv.reflectedPrimitiveNames]
      · simp [Kernel.Environment.primitives, NameSet.ofList]
        simp +decide [NameSet.contains]
  | nat types_eq constructors_eq =>
      apply CanonicalPrimitiveInventory.nat types_eq constructors_eq
      intro ci member
      have name_eq := recursorNamesOf VPrimitiveInductive.natFamily ``Nat
        types_eq (by rfl) ci member
      rw [name_eq]
      constructor
      · simp [VEnv.reflectedPrimitiveNames]
      · simp [Kernel.Environment.primitives, NameSet.ofList]
        simp +decide [NameSet.contains]

end VInductDecl.CanonicalPrimitiveConstants

namespace VInductDecl.CanonicalPrimitiveInventory

/-- A canonical primitive inventory replayed by an exact ordinary trace
constructs the complete Theory primitive-reflection contract. -/
theorem hasPrimitives
    {decl : VInductDecl} {generation : decl.BlockGenerationChecked}
    (inventory : decl.CanonicalPrimitiveInventory generation)
    (trace : AddInductBlockTrace m₁ env₁ decl m₂ env₂)
    (generation_eq : trace.generation = generation)
    (pre : env₁.HasPrimitives) : env₂.HasPrimitives := by
  cases inventory with
  | bool types_eq constructors_eq recursorNames =>
    apply pre.of_addBool trace.le
    · have found := trace.addCtors.lookup
          (ci := VPrimitiveInductive.boolConstructors[0]) (by
            rw [constructors_eq]
            simp)
      exact trace.addRules.le.constants <| trace.addRecs.le.constants <| by
        simpa [VPrimitiveInductive.boolConstructors] using found
    · have found := trace.addCtors.lookup
          (ci := VPrimitiveInductive.boolConstructors[1]) (by
            rw [constructors_eq]
            simp)
      exact trace.addRules.le.constants <| trace.addRecs.le.constants <| by
        simpa [VPrimitiveInductive.boolConstructors] using found
    · intro n reflected hBool hFalse hTrue
      rw [trace.addRules.constants_eq]
      rw [trace.addRecs.constants_eq_of_not_mem (by
        intro ci member equality
        apply (recursorNames ci
          (by simpa only [← generation_eq] using member)).1
        simpa only [equality] using reflected)]
      rw [trace.addCtors.constants_eq_of_not_mem (by
        intro ci member
        rw [constructors_eq] at member
        simp [VPrimitiveInductive.boolConstructors] at member
        rcases member with rfl | rfl
        · exact Ne.symm hFalse
        · exact Ne.symm hTrue)]
      exact trace.addTypes.constants_eq_of_not_mem (by
        intro ci member
        rw [types_eq] at member
        have equality := List.mem_singleton.1 member
        subst ci
        exact Ne.symm hBool)
  | nat types_eq constructors_eq recursorNames =>
    apply pre.of_addNat trace.le
    · have found := trace.addCtors.lookup
          (ci := VPrimitiveInductive.natConstructors[0]) (by
            rw [constructors_eq]
            simp)
      exact trace.addRules.le.constants <| trace.addRecs.le.constants <| by
        simpa [VPrimitiveInductive.natConstructors] using found
    · have found := trace.addCtors.lookup
          (ci := VPrimitiveInductive.natConstructors[1]) (by
            rw [constructors_eq]
            simp)
      exact trace.addRules.le.constants <| trace.addRecs.le.constants <| by
        simpa [VPrimitiveInductive.natConstructors] using found
    · intro n reflected hNat hZero hSucc
      rw [trace.addRules.constants_eq]
      rw [trace.addRecs.constants_eq_of_not_mem (by
        intro ci member equality
        apply (recursorNames ci
          (by simpa only [← generation_eq] using member)).1
        simpa only [equality] using reflected)]
      rw [trace.addCtors.constants_eq_of_not_mem (by
        intro ci member
        rw [constructors_eq] at member
        simp [VPrimitiveInductive.natConstructors] at member
        rcases member with rfl | rfl
        · exact Ne.symm hZero
        · exact Ne.symm hSucc)]
      exact trace.addTypes.constants_eq_of_not_mem (by
        intro ci member
        rw [types_eq] at member
        have equality := List.mem_singleton.1 member
        subst ci
        exact Ne.symm hNat)

/-- The same canonical inventory discharges host primitive safety for the
exact metadata map.  All primitive family/constructor constants have zero
universe parameters; recursors avoid the reflected primitive inventory. -/
theorem safePrimitivesMap
    {decl : VInductDecl} {generation : decl.BlockGenerationChecked}
    (inventory : decl.CanonicalPrimitiveInventory generation)
    (trace : AddInductBlockTrace m₁ env₁ decl m₂ env₂)
    (generation_eq : trace.generation = generation)
    (mapWF : m₁.WF) (pre : ConstMapSafePrimitives m₁) :
    ConstMapSafePrimitives m₂ := by
  cases inventory with
  | bool types_eq constructors_eq recursorNames =>
    exact trace.addRecs.safePrimitivesMap_of_zero_uvars
      (trace.addCtors.map_wf (trace.addTypes.map_wf mapWF))
      (trace.addCtors.safePrimitivesMap_of_zero_uvars
        (trace.addTypes.map_wf mapWF)
        (trace.addTypes.safePrimitivesMap_of_zero_uvars mapWF pre (by
          intro ci member _
          rw [types_eq] at member
          have equality := List.mem_singleton.1 member
          subst ci
          rfl)) (by
            intro ci member _
            rw [constructors_eq] at member
            simp [VPrimitiveInductive.boolConstructors] at member
            rcases member with rfl | rfl <;> rfl)) (by
        intro ci member primitive
        rw [(recursorNames ci
          (by simpa only [← generation_eq] using member)).2] at primitive
        contradiction)
  | nat types_eq constructors_eq recursorNames =>
    exact trace.addRecs.safePrimitivesMap_of_zero_uvars
      (trace.addCtors.map_wf (trace.addTypes.map_wf mapWF))
      (trace.addCtors.safePrimitivesMap_of_zero_uvars
        (trace.addTypes.map_wf mapWF)
        (trace.addTypes.safePrimitivesMap_of_zero_uvars mapWF pre (by
          intro ci member _
          rw [types_eq] at member
          have equality := List.mem_singleton.1 member
          subst ci
          rfl)) (by
            intro ci member _
            rw [constructors_eq] at member
            simp [VPrimitiveInductive.natConstructors] at member
            rcases member with rfl | rfl <;> rfl)) (by
        intro ci member primitive
        rw [(recursorNames ci
          (by simpa only [← generation_eq] using member)).2] at primitive
        contradiction)

end VInductDecl.CanonicalPrimitiveInventory

/-!
The primitive-transaction helpers remain within Verify's existing logical and
persistent-map trust surface.  In particular, constructing Theory primitive
reflection from canonical lookup data introduces no checker axiom.
-/

/--
info: 'Lean4Lean.VInductDecl.CanonicalPrimitiveConstants.toInventory' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms VInductDecl.CanonicalPrimitiveConstants.toInventory

/--
info: 'Lean4Lean.AddInductConstants.safePrimitivesMap_of_zero_uvars' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms AddInductConstants.safePrimitivesMap_of_zero_uvars

/--
info: 'Lean4Lean.AddDefEqs.constants_eq' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms AddDefEqs.constants_eq

/--
info: 'Lean4Lean.AddInductConstants.constants_eq_of_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AddInductConstants.constants_eq_of_not_mem

/--
info: 'Lean4Lean.VEnv.HasPrimitives.of_addBool' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VEnv.HasPrimitives.of_addBool

/--
info: 'Lean4Lean.VEnv.HasPrimitives.of_addNat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VEnv.HasPrimitives.of_addNat

/--
info: 'Lean4Lean.VInductDecl.CanonicalPrimitiveInventory.hasPrimitives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms VInductDecl.CanonicalPrimitiveInventory.hasPrimitives

/--
info: 'Lean4Lean.VInductDecl.CanonicalPrimitiveInventory.safePrimitivesMap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms VInductDecl.CanonicalPrimitiveInventory.safePrimitivesMap

/-- Primitive reflection across all four phases of an ordinary mutual-block
transaction.  Name avoidance is exposed phase by phase so callers can derive
it from the exact source and generated-recursors inventories they own. -/
theorem AddInductBlockTrace.hasPrimitives
    (H : AddInductBlockTrace m₁ env₁ decl m₂ env₂)
    (pre : env₁.HasPrimitives)
    (typeNames : ∀ ci ∈ decl.blockTypeConstants,
      ci.name ∉ VEnv.reflectedPrimitiveNames)
    (ctorNames : ∀ ci ∈ decl.blockConstructorConstants,
      ci.name ∉ VEnv.reflectedPrimitiveNames)
    (recNames : ∀ ci ∈ H.generation.recursors,
      ci.name ∉ VEnv.reflectedPrimitiveNames) :
    env₂.HasPrimitives :=
  H.addRules.hasPrimitives <|
    H.addRecs.hasPrimitives
      (H.addCtors.hasPrimitives
        (H.addTypes.hasPrimitives pre typeNames) ctorNames)
      recNames

/-- Primitive reflection across all four phases of a restored nested
transaction.  Auxiliary recursor renamings are covered by the explicit
restored-recursor name premise. -/
theorem AddInductNestedTrace.hasPrimitives
    (H : AddInductNestedTrace m₁ env₁ decl m₂ env₂)
    (pre : env₁.HasPrimitives)
    (typeNames : ∀ ci ∈ decl.blockTypeConstants,
      ci.name ∉ VEnv.reflectedPrimitiveNames)
    (ctorNames : ∀ ci ∈ decl.blockConstructorConstants,
      ci.name ∉ VEnv.reflectedPrimitiveNames)
    (recNames : ∀ ci ∈ H.nested.recursors,
      ci.name ∉ VEnv.reflectedPrimitiveNames) :
    env₂.HasPrimitives :=
  H.addRules.hasPrimitives <|
    H.addRecs.hasPrimitives
      (H.addCtors.hasPrimitives
        (H.addTypes.hasPrimitives pre typeNames) ctorNames)
      recNames

/-- Kernel primitive safety after the metadata phases of an ordinary block.
The Theory rule phase does not alter the host constant map. -/
theorem AddInductBlockTrace.safePrimitivesMap
    (H : AddInductBlockTrace m₁ env₁ decl m₂ env₂)
    (mapWF : m₁.WF) (pre : ConstMapSafePrimitives m₁)
    (typeNames : ∀ ci ∈ decl.blockTypeConstants,
      Environment.primitives.contains ci.name = false)
    (ctorNames : ∀ ci ∈ decl.blockConstructorConstants,
      Environment.primitives.contains ci.name = false)
    (recNames : ∀ ci ∈ H.generation.recursors,
      Environment.primitives.contains ci.name = false) :
    ConstMapSafePrimitives m₂ :=
  H.addRecs.safePrimitivesMap
    (H.addCtors.map_wf (H.addTypes.map_wf mapWF))
    (H.addCtors.safePrimitivesMap
      (H.addTypes.map_wf mapWF)
      (H.addTypes.safePrimitivesMap mapWF pre typeNames) ctorNames)
    recNames

/-- Kernel primitive safety after the restored metadata phases of a nested
block. -/
theorem AddInductNestedTrace.safePrimitivesMap
    (H : AddInductNestedTrace m₁ env₁ decl m₂ env₂)
    (mapWF : m₁.WF) (pre : ConstMapSafePrimitives m₁)
    (typeNames : ∀ ci ∈ decl.blockTypeConstants,
      Environment.primitives.contains ci.name = false)
    (ctorNames : ∀ ci ∈ decl.blockConstructorConstants,
      Environment.primitives.contains ci.name = false)
    (recNames : ∀ ci ∈ H.nested.recursors,
      Environment.primitives.contains ci.name = false) :
    ConstMapSafePrimitives m₂ :=
  H.addRecs.safePrimitivesMap
    (H.addCtors.map_wf (H.addTypes.map_wf mapWF))
    (H.addCtors.safePrimitivesMap
      (H.addTypes.map_wf mapWF)
      (H.addTypes.safePrimitivesMap mapWF pre typeNames) ctorNames)
    recNames

/-- Two ordinary traces for the same generated artifact preserve an ordering
between their input Theory models. -/
theorem AddInductBlockTrace.mono
    (left : AddInductBlockTrace m₁ env₁ decl m₂ env₂)
    (right : AddInductBlockTrace m₁' env₁' decl m₂' env₂')
    (generation_eq : left.generation = right.generation)
    (pre : env₁ ≤ env₁') : env₂ ≤ env₂' := by
  have types := left.addTypes.mono right.addTypes pre
  have ctors := left.addCtors.mono right.addCtors types
  have rightRecs : AddInductConstants .recursor right.ctorMap right.ctorEnv
      left.generation.recursors m₂' right.recEnv := by
    simpa only [generation_eq] using right.addRecs
  have recs := left.addRecs.mono rightRecs ctors
  have rightRules : AddDefEqs right.recEnv
      left.generation.generatedRules env₂' := by
    simpa only [generation_eq] using right.addRules
  exact left.addRules.mono rightRules recs

/-- Two nested traces for the same restored artifact preserve an ordering
between their input Theory models. -/
theorem AddInductNestedTrace.mono
    (left : AddInductNestedTrace m₁ env₁ decl m₂ env₂)
    (right : AddInductNestedTrace m₁' env₁' decl m₂' env₂')
    (nested_eq : left.nested = right.nested)
    (pre : env₁ ≤ env₁') : env₂ ≤ env₂' := by
  have types := left.addTypes.mono right.addTypes pre
  have ctors := left.addCtors.mono right.addCtors types
  have rightRecs : AddInductConstants .recursor right.ctorMap right.ctorEnv
      left.nested.recursors m₂' right.recEnv := by
    simpa only [nested_eq] using right.addRecs
  have recs := left.addRecs.mono rightRecs ctors
  have rightRules : AddDefEqs right.recEnv left.nested.generatedRules env₂' := by
    simpa only [nested_eq] using right.addRules
  exact left.addRules.mono rightRules recs

theorem TrEnv.constants_eq_none (H : TrEnv safety env venv) (hn : env.find? name = none) :
    venv.constants name = none := by
  cases hfind : venv.constants name with
  | none => rfl
  | some ci => obtain ⟨ci, hci, _⟩ := H.find?_iff.2 ⟨ci, hfind⟩; cases hn ▸ hci

theorem TrEnv.exists_addConsts (H : TrEnv safety env venv) {cis : List VDefVal}
    (hfresh : ∀ ci ∈ cis, env.find? ci.name = none)
    (hnd : (cis.map (·.name)).Nodup) : ∃ venv', venv.addConsts cis = some venv' :=
  VEnv.exists_addConsts (fun ci hci => H.constants_eq_none (hfresh ci hci)) hnd

theorem insertDefs_wf : ∀ {cis : List DefinitionVal} {C : ConstMap}, C.WF →
    (∀ d ∈ cis, C.find? d.name = none) → (cis.map (·.name)).Nodup → (insertDefs C cis).WF
  | [], _, hC, _, _ => hC
  | d :: ds, C, hC, hfr, hnd => by
    rw [List.map_cons, List.nodup_cons] at hnd
    refine insertDefs_wf (cis := ds) (hC.insert _ _ (hfr _ (.head _))) (fun e he => ?_) hnd.2
    rw [hC.find?_insert, if_neg]; · exact hfr e (.tail _ he)
    simp only [beq_iff_eq]; intro hh
    exact hnd.1 (List.mem_map.2 ⟨e, he, hh.symm⟩)

theorem Environment.constants_addDefs : ∀ {vs : List DefinitionVal} {env : Environment},
    (vs.foldl (fun e v => Lean.Kernel.Environment.add e (.defnInfo v)) env).constants =
    insertDefs env.constants vs
  | [], _ => rfl
  | v :: vs, env => Environment.constants_addDefs (vs := vs) (env := env.add (.defnInfo v))

theorem VEnvs.WF.safePrimitives_addDefs {ves : VEnvs} {env : Environment}
    (wf : ves.WF env) {vs : List DefinitionVal}
    (hfresh : ∀ v ∈ vs, env.find? v.name = none)
    (hnd : (vs.map (·.name)).Nodup)
    (hnonprim : ∀ v ∈ vs, Environment.primitives.contains v.name = false)
    (hfind : (vs.foldl (fun e v => e.add (.defnInfo v)) env).find? n = some ci)
    (hp : Environment.primitives.contains n) : ci.safety = .safe ∧ ci.levelParams = [] := by
  have mapWF := (wf.tr (safety := .safe)).map_wf
  have hfr : ∀ d ∈ vs, env.constants.find? d.name = none := fun d hd => by
    rw [← mapWF.find?'_eq_find?]; exact hfresh d hd
  rw [Kernel.Environment.find?, Environment.constants_addDefs,
    (insertDefs_wf mapWF hfr hnd).find?'_eq_find?] at hfind
  rcases insertDefs_find? mapWF hfr hnd hfind with h | ⟨d, hd, rfl, rfl⟩
  · exact wf.safePrimitives (by rwa [Kernel.Environment.find?, mapWF.find?'_eq_find?]) hp
  · exact absurd hp (by simp [hnonprim d hd])

theorem Environment.quotInit_addDefs : ∀ {vs : List DefinitionVal} {env : Environment},
    (vs.foldl (fun e v => Lean.Kernel.Environment.add e (.defnInfo v)) env).quotInit =
    env.quotInit
  | [], _ => rfl
  | _ :: vs, _ => quotInit_addDefs (vs := vs)

/-- A block of definitions that is invisible at `safety` extends the constant map without
touching the model, one `TrEnv'.ignore` per member. -/
theorem TrEnv'.ignoreDefs : ∀ {vs : List DefinitionVal} {C : ConstMap},
    (∀ v ∈ vs, ¬ safety ≤ (ConstantInfo.defnInfo v).safety) →
    (∀ v ∈ vs, C.find? v.name = none) → (vs.map (·.name)).Nodup →
    TrEnv' safety C Q venv → TrEnv' safety (insertDefs C vs) Q venv
  | [], _, _, _, _, H => H
  | d :: ds, C, hvis, hfr, hnd, H => by
    rw [List.map_cons, List.nodup_cons] at hnd
    have H' := TrEnv'.ignore (ci := .defnInfo d) (hfr _ (.head _)) (hvis _ (.head _)) H
    show TrEnv' safety (insertDefs (SMap.insert C d.name (.defnInfo d)) ds) Q _
    refine TrEnv'.ignoreDefs (fun e he => hvis e (.tail _ he)) (fun e he => ?_) hnd.2 H'
    rw [H.map_wf.find?_insert, if_neg]; · exact hfr e (.tail _ he)
    simp only [beq_iff_eq]; intro hh
    exact hnd.1 (List.mem_map.2 ⟨e, he, hh.symm⟩)

theorem Environment.find?_add_of_ne {env : Environment} (mapWF : env.constants.WF)
    (ci : ConstantInfo) (hfresh : env.find? ci.name = none) {n : Name}
    (hne : ci.name ≠ n) (h : env.find? n = none) : (env.add ci).find? n = none := by
  have hnone : env.constants.find? ci.name = none := by rwa [← mapWF.find?'_eq_find?]
  have mapWF' := mapWF.insert ci.name ci hnone
  change SMap.find?' (env.constants.insert ci.name ci) n = none
  rw [mapWF'.find?'_eq_find?, mapWF.find?_insert, if_neg (by simpa using hne)]
  rwa [Kernel.Environment.find?, mapWF.find?'_eq_find?] at h

/-- Data produced by `addMutual`'s header loop for one block member. -/
def TrMutualHeader (bs : DefinitionSafety) (venv : VEnv) (env : Environment)
    (v : DefinitionVal) (ci : VDefVal) : Prop :=
  TrConstVal bs venv (.defnInfo v) ci.toVConstVal ∧
  ci.toVConstant.WF venv ∧ env.find? v.name = none ∧
  Environment.primitives.contains v.name = false

/-- A model of the temporary environment in which a mutual block's bodies are checked: every
member has been added as an axiom, so a body may refer to any member of the block (including
itself) but cannot delta-unfold it. -/
theorem VEnvAt.addAxioms {env : Environment} {venv : VEnv} {bs : DefinitionSafety}
    (hsf : bs ≤ (if bs == .unsafe then DefinitionSafety.unsafe else .safe)) :
    ∀ {vs : List DefinitionVal} {cis : List VDefVal} {venv' : VEnv},
      VEnvAt env bs venv →
      List.Forall₂ (TrMutualHeader bs venv env) vs cis →
      (vs.map (·.name)).Nodup →
      venv.addConsts cis = some venv' →
      VEnvAt (vs.foldl (fun e v => e.add (.axiomInfo { v with isUnsafe := bs == .unsafe })) env)
        bs venv'
  | [], _, _, wf, .nil, _, e => by cases e; exact wf
  | v :: vs, ci :: cis, venv', wf, .cons hd tl, hnd, e => by
    rw [List.map_cons, List.nodup_cons] at hnd
    simp [VEnv.addConsts, Option.bind_eq_some_iff] at e
    obtain ⟨venv₁, h₁, h₂⟩ := e
    have hn : v.name = ci.name := hd.1.2
    have h₁' : venv.addConst v.name ci.toVConstant = some venv₁ := by rw [hn]; exact h₁
    have hle := VEnv.addConst_le h₁'
    have hax : (ConstantInfo.axiomInfo { v with isUnsafe := bs == .unsafe }).name = v.name := rfl
    have tr₁ : TrEnv bs
        (env.add (.axiomInfo { v with isUnsafe := bs == .unsafe })) venv₁ :=
      TrEnv'.axiom (ci := { v with isUnsafe := bs == .unsafe })
        (ci' := ci.toVConstant) ⟨hsf, hd.1.1.2.1, hd.1.1.2.2⟩
        (by rw [← wf.tr.map_wf.find?'_eq_find?]; exact hd.2.2.1)
        hd.2.1 h₁' wf.tr
    have readiness :
        ProjectionReady (env.add (.axiomInfo { v with isUnsafe := bs == .unsafe })) venv₁ ∧
        StructureEtaReady (env.add (.axiomInfo { v with isUnsafe := bs == .unsafe })) venv₁ :=
      Readiness.add wf.tr.map_wf
        (by rw [hax]; exact hd.2.2.1)
        (by simp [Lean.ConstantInfo.ReadinessTransparent])
        hle tr₁.wf wf.projectionReady wf.structureEtaReady
    have wf₁ : VEnvAt (env.add (.axiomInfo { v with isUnsafe := bs == .unsafe })) bs venv₁ :=
      { tr := tr₁
        hasPrimitives := wf.hasPrimitives.addConst_of_not_primitive hd.2.2.2 h₁'
        safePrimitives := wf.safePrimitives_add _ (hax ▸ hd.2.2.1)
          (by rw [hax]; simp [hd.2.2.2])
        -- Tier V (L4L-19B): checker-readiness transport across the temporary
        -- axiom additions of a mutual-block body environment. Added at the
        -- v4.33 reconciliation, where upstream's proved front-end chains met
        -- this fork's projection-readiness obligation on `VContext`; the
        -- `infer` half needs `isProjectionReadyStructure` stability under
        -- `Environment.add`, which is new verification content, not merge
        -- resolution.
        projectionReady := readiness.1
        structureEtaReady := readiness.2 }
    show VEnvAt (vs.foldl (fun e v => e.add (.axiomInfo { v with isUnsafe := bs == .unsafe }))
      (env.add (.axiomInfo { v with isUnsafe := bs == .unsafe }))) bs venv'
    refine VEnvAt.addAxioms hsf wf₁ ?_ hnd.2 h₂
    refine tl.and_mem.imp fun w cj h => ?_
    obtain ⟨h, hw, -⟩ := h
    have hne : v.name ≠ w.name := fun hh => hnd.1 (List.mem_map.2 ⟨w, hw, hh.symm⟩)
    exact ⟨⟨⟨h.1.1.1, h.1.1.2.1, h.1.1.2.2.mono hle⟩, h.1.2⟩, h.2.1.mono hle,
      Environment.find?_add_of_ne wf.tr.map_wf _ (hax ▸ hd.2.2.1) (hax ▸ hne) h.2.2.1,
      h.2.2.2⟩

/-- Add a whole mutual block. The headers were checked in `env`, the bodies in the temporary
environment holding the entire block, which is `base` on the model side; `TrEnv'.mutualDef`
consumes exactly that split.

Like `addUnsafeDef.WF` this cannot conclude `VEnv.AddDef` for the members: the bodies may
refer to each other, so they do not translate before the block is added. -/
theorem addMutualBlock.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (bs : DefinitionSafety) (vs : List DefinitionVal) (cis : List VDefVal) (base : VEnv)
    (hbs : ∀ v ∈ vs, v.safety = bs)
    (hnd : (vs.map (·.name)).Nodup)
    (hfresh : ∀ v ∈ vs, env.find? v.name = none)
    (hnonprim : ∀ v ∈ vs, Environment.primitives.contains v.name = false)
    (hwfc : ∀ ci ∈ cis, ci.toVConstant.WF (ves.venv bs))
    (hbase : (ves.venv bs).addConsts cis = some base)
    (htr : TrDefBlock bs (ves.venv bs) base vs cis)
    (hci : ∀ ci ∈ cis, ci.WF base) :
    ∃ ves' : VEnvs, ves'.WF (vs.foldl (fun e v => e.add (.defnInfo v)) env) ∧
      ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  have hname := htr.imp (fun _ _ h => h.1.2)
  have hmapeq : vs.map (·.name) = cis.map (·.name) := by
    rwa [← List.forall₂_eq, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  have hndCis : (cis.map (·.name)).Nodup := hmapeq ▸ hnd
  have hpull {P : Name → Prop} (H : ∀ v ∈ vs, P v.name) : ∀ ci ∈ cis, P ci.name := by
    intro ci hc
    obtain ⟨v, hv, hn⟩ := hname.forall_exists_r ci hc
    exact hn ▸ H v hv
  have hfreshCis := hpull (P := fun n => env.find? n = none) hfresh
  have hnonprimCis := hpull (P := fun n => Environment.primitives.contains n = false) hnonprim
  have hfreshMap : ∀ v ∈ vs, env.constants.find? v.name = none := fun v hv => by
    rw [← (wf.tr (safety := .safe)).map_wf.find?'_eq_find?]; exact hfresh v hv
  have hvis_iff (sf) (hv : sf ≤ bs) (v) (hmem : v ∈ vs) :
      sf ≤ (ConstantInfo.defnInfo v).safety := by
    rw [ConstantInfo.defnInfo_safety, hbs v hmem]; exact hv
  -- the model at each visible safety level
  have hves' sf : ∃ venv',
      if sf ≤ bs then ∃ b, (ves.venv sf).addConsts cis = some b ∧ venv' = b.addDefEqs cis
      else venv' = ves.venv sf := by
    split <;> [skip; exact ⟨_, rfl⟩]
    obtain ⟨b, hb⟩ := (wf.tr (safety := sf)).exists_addConsts hfreshCis hndCis
    exact ⟨_, b, hb, rfl⟩
  obtain ⟨ves', hves'⟩ := VEnvs.axiom_of_choice hves'
  have hbaseSf (sf) (hv : sf ≤ bs) : ∃ b, (ves.venv sf).addConsts cis = some b ∧
      ves'.venv sf = b.addDefEqs cis := by
    have h := hves' sf; rw [if_pos hv] at h; exact h
  have hsame (sf) (hv : ¬ sf ≤ bs) : ves'.venv sf = ves.venv sf := by
    have h := hves' sf; rwa [if_neg hv] at h
  have leNew (sf) : ves.venv sf ≤ ves'.venv sf := by
    by_cases hv : sf ≤ bs
    · obtain ⟨b, hb, heq⟩ := hbaseSf sf hv
      exact heq ▸ (VEnv.addConsts_le hb).trans VEnv.addDefEqs_le
    · rw [hsame sf hv]
      exact VEnv.LE.rfl
  have trNew (sf) :
      TrEnv sf (vs.foldl (fun e v => e.add (.defnInfo v)) env) (ves'.venv sf) := by
    show TrEnv sf _ _
    unfold TrEnv
    rw [Environment.constants_addDefs, Environment.quotInit_addDefs]
    by_cases hv : sf ≤ bs
    · obtain ⟨b, hb, heq⟩ := hbaseSf sf hv
      have hmono : ves.venv bs ≤ ves.venv sf := wf.mono hv
      have hbmono : base ≤ b := VEnv.addConsts_mono hmono hbase hb
      refine heq ▸ TrEnv'.mutualDef (env := ves.venv sf) (env' := b) ?_ hnd hfreshMap
        (fun ci hc => (hwfc ci hc).mono hmono) hb
        (fun ci hc => (hci ci hc).mono hbmono) (wf.tr (safety := sf))
      exact htr.imp fun _ _ h => ⟨⟨(h.1.1.sf_mono hv).mono hmono, h.1.2⟩, h.2.mono hbmono⟩
    · rw [hsame sf hv]
      exact TrEnv'.ignoreDefs
        (fun v hmem => fun h => hv (by rwa [ConstantInfo.defnInfo_safety, hbs v hmem] at h))
        hfreshMap hnd (wf.tr (safety := sf))
  refine ⟨ves', ?_, leNew⟩
  have readiness : ∀ sf,
      ProjectionReady (vs.foldl (fun e v => e.add (.defnInfo v)) env) (ves'.venv sf) ∧
      StructureEtaReady (vs.foldl (fun e v => e.add (.defnInfo v)) env) (ves'.venv sf) :=
    fun sf => Readiness.addDefs (wf.tr (safety := sf)).map_wf hfresh hnd
      (leNew sf) (trNew sf).wf (wf.projectionReady (safety := sf))
      (wf.structureEtaReady (safety := sf))
  exact {
    tr {sf} := trNew sf
    hasPrimitives {sf} := by
      by_cases hv : sf ≤ bs
      · obtain ⟨b, hb, heq⟩ := hbaseSf sf hv
        exact heq ▸ ((wf.hasPrimitives (safety := sf)).addConsts hnonprimCis hb).addDefEqs
      · rw [hsame sf hv]; exact wf.hasPrimitives
    safePrimitives := wf.safePrimitives_addDefs hfresh hnd hnonprim
    mono {sf sf'} hle := by
      by_cases hv' : sf' ≤ bs
      · have hv : sf ≤ bs := DefinitionSafety.le_trans hle hv'
        obtain ⟨b', hb', heq'⟩ := hbaseSf sf' hv'
        obtain ⟨b, hb, heq⟩ := hbaseSf sf hv
        rw [heq', heq]
        exact VEnv.addDefEqs_mono (VEnv.addConsts_mono (wf.mono hle) hb' hb)
      · rw [hsame sf' hv']
        by_cases hv : sf ≤ bs
        · obtain ⟨b, hb, heq⟩ := hbaseSf sf hv
          rw [heq]
          exact (wf.mono hle).trans ((VEnv.addConsts_le hb).trans VEnv.addDefEqs_le)
        · rw [hsame sf hv]; exact wf.mono hle
    -- Tier V (L4L-19B): checker-readiness transport across this front-end
    -- extension; see `VEnvAt.addAxioms`.
    projectionReady {sf} := (readiness sf).1
    structureEtaReady {sf} := (readiness sf).2 }

theorem addConstCore.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (ci : ConstantInfo) (ci' : VConstVal) (checkSafety : DefinitionSafety)
    (visible_le : ∀ safety, safety ≤ ci.safety → safety ≤ checkSafety)
    (htr : TrConstVal checkSafety (ves.venv checkSafety) ci ci')
    (hci : ci'.toVConstant.WF (ves.venv checkSafety))
    (hn : env.find? ci.name = none)
    (htransparent : Lean.ConstantInfo.ReadinessTransparent ci)
    (hprim : Environment.primitives.contains ci.name →
      ci.safety = .safe ∧ ci.levelParams = [])
    (preserves : ∀ safety venv', safety ≤ ci.safety →
      (ves.venv safety).addConst ci.name ci'.toVConstant = some venv' →
      (ves.venv safety).HasPrimitives → venv'.HasPrimitives)
    (step : ∀ safety venv',
      TrConstant safety (ves.venv safety) ci ci'.toVConstant →
      ci'.toVConstant.WF (ves.venv safety) →
      (ves.venv safety).addConst ci.name ci'.toVConstant = some venv' →
      TrEnv' safety env.constants env.quotInit (ves.venv safety) →
      TrEnv' safety (env.constants.insert ci.name ci) env.quotInit venv') :
    ∃ ves' : VEnvs, ves'.WF (env.add ci) ∧
      ∀ safety, (ves.venv safety).AddConst safety ci ci'.toVConstant (ves'.venv safety) := by
  have hnMap : env.constants.find? ci.name = none := by
    rw [← (wf.tr (safety := .safe)).map_wf.find?'_eq_find?]
    exact hn
  have visible_tr (safety) (hvisible : safety ≤ ci.safety) :
      TrConstant safety (ves.venv safety) ci ci'.toVConstant :=
    (htr.1.sf_mono (visible_le safety hvisible)).mono (wf.mono (visible_le safety hvisible))
  have visible_wf (safety) (hvisible : safety ≤ ci.safety) :
      ci'.toVConstant.WF (ves.venv safety) :=
    hci.mono (wf.mono (visible_le safety hvisible))
  have hves' safety : ∃ venv', (ves.venv safety).AddConst safety ci ci'.toVConstant venv' := by
    unfold VEnv.AddConst; split <;> [rename_i hvisible; exact ⟨ves.venv safety, rfl⟩]
    have ⟨venv', hadd⟩ := (wf.tr (safety := safety)).exists_addConst hn ci'.toVConstant
    exact ⟨venv', visible_tr safety hvisible, visible_wf safety hvisible, hadd⟩
  obtain ⟨ves', hves'⟩ := VEnvs.axiom_of_choice hves'
  have hadd (safety) (hvisible : safety ≤ ci.safety) :
      (ves.venv safety).addConst ci.name ci'.toVConstant = some (ves'.venv safety) := by
    have h := hves' safety; unfold VEnv.AddConst at h; rw [if_pos hvisible] at h; exact h.2.2
  have hsame (safety) (hvisible : ¬ safety ≤ ci.safety) : ves'.venv safety = ves.venv safety := by
    have h := hves' safety; unfold VEnv.AddConst at h; rwa [if_neg hvisible] at h
  refine ⟨ves', ?_, hves'⟩
  have trNew (safety) : TrEnv safety (env.add ci) (ves'.venv safety) := by
    by_cases hvisible : safety ≤ ci.safety
    · exact step safety _ (visible_tr safety hvisible) (visible_wf safety hvisible)
        (hadd safety hvisible) (wf.tr (safety := safety))
    · rw [hsame safety hvisible]
      exact TrEnv'.ignore (ci := ci) hnMap hvisible (wf.tr (safety := safety))
  have leNew (safety) : ves.venv safety ≤ ves'.venv safety := by
    by_cases hvisible : safety ≤ ci.safety
    · exact VEnv.addConst_le (hadd safety hvisible)
    · rw [hsame safety hvisible]
      exact VEnv.LE.rfl
  have readiness : ∀ safety,
      ProjectionReady (env.add ci) (ves'.venv safety) ∧
      StructureEtaReady (env.add ci) (ves'.venv safety) :=
    fun safety => Readiness.add (wf.tr (safety := safety)).map_wf hn htransparent
      (leNew safety) (trNew safety).wf (wf.projectionReady (safety := safety))
      (wf.structureEtaReady (safety := safety))
  exact {
    tr {safety} := trNew safety
    hasPrimitives {safety} := by
      by_cases hvisible : safety ≤ ci.safety
      · exact preserves safety _ hvisible (hadd safety hvisible) (wf.hasPrimitives (safety := safety))
      · rw [hsame safety hvisible]; exact wf.hasPrimitives (safety := safety)
    safePrimitives := wf.safePrimitives_add ci hn hprim
    mono {safety safety'} hle := by
      by_cases hvisible' : safety' ≤ ci.safety
      · have hvisible := DefinitionSafety.le_trans hle hvisible'
        exact VEnv.addConst_mono (wf.mono hle) (hadd safety' hvisible') (hadd safety hvisible)
      rw [hsame safety' hvisible']
      by_cases hvisible : safety ≤ ci.safety
      · exact (wf.mono hle).trans (VEnv.addConst_le (hadd safety hvisible))
      · rw [hsame safety hvisible]; exact wf.mono hle
    -- Tier V (L4L-19B): checker-readiness transport across this front-end
    -- extension; see `VEnvAt.addAxioms`.
    projectionReady {safety} := (readiness safety).1
    structureEtaReady {safety} := (readiness safety).2 }

theorem addConst.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (ci : ConstantInfo) (ci' : VConstVal) (checkSafety : DefinitionSafety)
    (visible_le : ∀ safety, safety ≤ ci.safety → safety ≤ checkSafety)
    (htr : TrConstVal checkSafety (ves.venv checkSafety) ci ci')
    (hci : ci'.toVConstant.WF (ves.venv checkSafety))
    (hn : env.find? ci.name = none)
    (htransparent : Lean.ConstantInfo.ReadinessTransparent ci)
    (hnonprim : Environment.primitives.contains ci.name = false)
    (step : ∀ safety venv',
      TrConstant safety (ves.venv safety) ci ci'.toVConstant →
      ci'.toVConstant.WF (ves.venv safety) →
      (ves.venv safety).addConst ci.name ci'.toVConstant = some venv' →
      TrEnv' safety env.constants env.quotInit (ves.venv safety) →
      TrEnv' safety (env.constants.insert ci.name ci) env.quotInit venv') :
    ∃ ves' : VEnvs, ves'.WF (env.add ci) ∧
      ∀ safety, (ves.venv safety).AddConst safety ci ci'.toVConstant (ves'.venv safety) :=
  addConstCore.WF wf ci ci' checkSafety visible_le htr hci hn htransparent (by simp_all)
    (fun _ _ _ hadd hp => hp.addConst_of_not_primitive hnonprim hadd) step

theorem addDef.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (ci' : VDefVal) (checkSafety : DefinitionSafety)
    (visible_le : ∀ safety, safety ≤ (ConstantInfo.defnInfo v).safety → safety ≤ checkSafety)
    (htr : TrDefVal checkSafety (ves.venv checkSafety) (.defnInfo v) ci')
    (hci : ci'.WF (ves.venv checkSafety))
    (hn : env.find? v.name = none)
    (hprim : Environment.primitives.contains v.name →
      (ConstantInfo.defnInfo v).safety = .safe ∧ v.levelParams = [])
    (preserves : ∀ safety base,
      safety ≤ (ConstantInfo.defnInfo v).safety →
      (ves.venv safety).addConst v.name ci'.toVConstant = some base →
      (base.addDefEq ci'.toDefEq).HasPrimitives) :
    ∃ ves' : VEnvs, ves'.WF (env.add (.defnInfo v)) ∧
      ∀ safety, (ves.venv safety).AddDef safety (.defnInfo v) ci' (ves'.venv safety) := by
  have hnMap : env.constants.find? v.name = none := by
    rwa [← (wf.tr (safety := .safe)).map_wf.find?'_eq_find?]
  have visible_tr (safety) (hvisible : safety ≤ (ConstantInfo.defnInfo v).safety) :
      TrDefVal safety (ves.venv safety) (.defnInfo v) ci' :=
    .mono (wf.mono (visible_le safety hvisible)) <|
      ⟨⟨htr.1.1.sf_mono (visible_le safety hvisible), htr.1.2⟩, htr.2⟩
  have visible_wf safety hvisible := hci.mono (wf.mono (visible_le safety hvisible))
  have hves' safety : ∃ venv', (ves.venv safety).AddDef safety (.defnInfo v) ci' venv' := by
    unfold VEnv.AddDef; split <;> [rename_i hvisible; exact ⟨ves.venv safety, rfl⟩]
    have ⟨base, hadd⟩ := (wf.tr (safety := safety)).exists_addConst hn ci'.toVConstant
    exact ⟨base.addDefEq ci'.toDefEq,
      base, visible_tr safety hvisible, visible_wf safety hvisible, hadd, rfl⟩
  obtain ⟨ves', hves'⟩ := VEnvs.axiom_of_choice hves'
  have hbase (safety) (hvisible : safety ≤ (ConstantInfo.defnInfo v).safety) :
      ∃ base, (ves.venv safety).addConst v.name ci'.toVConstant = some base ∧
        ves'.venv safety = base.addDefEq ci'.toDefEq := by
    have h := hves' safety; unfold VEnv.AddDef at h; rw [if_pos hvisible] at h
    obtain ⟨base, _, _, hadd, heq⟩ := h; exact ⟨base, hadd, heq⟩
  have hsame (safety) (hvisible : ¬ safety ≤ (ConstantInfo.defnInfo v).safety) :
      ves'.venv safety = ves.venv safety := by
    have h := hves' safety; unfold VEnv.AddDef at h; rwa [if_neg hvisible] at h
  refine ⟨ves', ?_, hves'⟩
  have trNew (safety) : TrEnv safety (env.add (.defnInfo v)) (ves'.venv safety) := by
    change TrEnv' safety (env.constants.insert v.name (.defnInfo v)) env.quotInit _
    by_cases hvisible : safety ≤ (ConstantInfo.defnInfo v).safety
    · obtain ⟨base, hadd, heq⟩ := hbase safety hvisible
      exact heq ▸ TrEnv'.defn (visible_tr safety hvisible)
        (by rwa [← (wf.tr (safety := safety)).map_wf.find?'_eq_find?])
        (visible_wf safety hvisible) hadd (wf.tr (safety := safety))
    · rw [hsame safety hvisible]
      simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using
        TrEnv'.ignore (ci := .defnInfo v) hnMap hvisible (wf.tr (safety := safety))
  have leNew (safety) : ves.venv safety ≤ ves'.venv safety := by
    by_cases hvisible : safety ≤ (ConstantInfo.defnInfo v).safety
    · obtain ⟨base, hadd, heq⟩ := hbase safety hvisible
      rw [heq]
      exact (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
    · rw [hsame safety hvisible]
      exact VEnv.LE.rfl
  have readiness : ∀ safety,
      ProjectionReady (env.add (.defnInfo v)) (ves'.venv safety) ∧
      StructureEtaReady (env.add (.defnInfo v)) (ves'.venv safety) :=
    fun safety => Readiness.add (wf.tr (safety := safety)).map_wf
      (ci := .defnInfo v)
      (by simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using hn)
      (by simp [Lean.ConstantInfo.ReadinessTransparent])
      (leNew safety) (trNew safety).wf (wf.projectionReady (safety := safety))
      (wf.structureEtaReady (safety := safety))
  refine {
    tr {safety} := trNew safety
    hasPrimitives {safety} := by
      by_cases hvisible : safety ≤ (ConstantInfo.defnInfo v).safety
      · obtain ⟨base, hadd, heq⟩ := hbase safety hvisible
        rw [heq]; exact preserves safety base hvisible hadd
      · rw [hsame safety hvisible]; exact wf.hasPrimitives (safety := safety)
    safePrimitives := wf.safePrimitives_add (.defnInfo v) hn hprim
    mono {safety safety'} hle := by
      by_cases hvisible' : safety' ≤ (ConstantInfo.defnInfo v).safety
      · have hvisible := DefinitionSafety.le_trans hle hvisible'
        obtain ⟨base', hadd', heq'⟩ := hbase safety' hvisible'
        obtain ⟨base, hadd, heq⟩ := hbase safety hvisible
        rw [heq', heq]
        exact VEnv.addDefEq_mono <| VEnv.addConst_mono (wf.mono hle) hadd' hadd
      rw [hsame safety' hvisible']
      by_cases hvisible : safety ≤ (ConstantInfo.defnInfo v).safety
      · obtain ⟨base, hadd, heq⟩ := hbase safety hvisible
        rw [heq]
        exact (wf.mono hle).trans <| (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
      · rw [hsame safety hvisible]; exact wf.mono hle
    -- Tier V (L4L-19B): checker-readiness transport across this front-end
    -- extension; see `VEnvAt.addAxioms`.
    projectionReady {safety} := (readiness safety).1
    structureEtaReady {safety} := (readiness safety).2 }

/-- The unsafe branch of `addDefinition`. The constant is added to the environment as an axiom
*before* its body is checked, so the body is translated in the extended environment `base` and
the whole step is justified by `TrEnv'.mutualDef` with a one-element block.

Unlike `addDef.WF` this cannot conclude `VEnv.AddDef`: that would require the body to translate
in the environment *before* the addition, which is false for a recursive unsafe definition. -/
theorem addUnsafeDef.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (ci' : VDefVal) (base : VEnv)
    (hunsafe : v.safety = .unsafe)
    (htr : TrConstVal .unsafe (ves.venv .unsafe) (.defnInfo v) ci'.toVConstVal)
    (hwfc : ci'.toVConstant.WF (ves.venv .unsafe))
    (hadd : (ves.venv .unsafe).addConst v.name ci'.toVConstant = some base)
    (hvalue : TrExprS base v.levelParams [] v.value ci'.value)
    (hci : ci'.WF base)
    (hn : env.find? v.name = none)
    (hnonprim : Environment.primitives.contains v.name = false) :
    ∃ ves' : VEnvs, ves'.WF (env.add (.defnInfo v)) ∧
      ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  have hnMap : env.constants.find? v.name = none := by
    rwa [← (wf.tr (safety := .safe)).map_wf.find?'_eq_find?]
  have hle : ves.venv .unsafe ≤ base.addDefEq ci'.toDefEq :=
    (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
  have hname : (ConstantInfo.defnInfo v).name = ci'.name := htr.2
  have hadd' : (ves.venv .unsafe).addConsts [ci'] = some base := by
    simp [VEnv.addConsts, ← hname]; exact hadd
  let ves' : VEnvs := ⟨fun | .unsafe => base.addDefEq ci'.toDefEq | sf => ves.venv sf⟩
  have trNew (safety) : TrEnv safety (env.add (.defnInfo v)) (ves'.venv safety) := by
    change TrEnv' safety (env.constants.insert v.name (.defnInfo v)) env.quotInit _
    match safety with
    | .unsafe =>
      have := TrEnv'.mutualDef (safety := .unsafe) (cis := [v]) (cis' := [ci'])
        (C := env.constants) (Q := env.quotInit) (env := ves.venv .unsafe) (env' := base)
        (.cons ⟨htr, hvalue⟩ .nil) (by simp) (by simpa using hnMap) (by simpa using hwfc)
        hadd' (by simpa using hci) wf.tr
      simpa [ves', insertDefs, VEnv.addDefEqs] using this
    | .safe | .partial =>
      refine TrEnv'.ignore (ci := .defnInfo v) hnMap ?_ wf.tr
      rw [ConstantInfo.defnInfo_safety, hunsafe]
      decide
  have leNew : ∀ safety, ves.venv safety ≤ ves'.venv safety := by
    rintro ⟨⟩ <;> first | exact hle | exact VEnv.LE.rfl
  have readiness : ∀ safety,
      ProjectionReady (env.add (.defnInfo v)) (ves'.venv safety) ∧
      StructureEtaReady (env.add (.defnInfo v)) (ves'.venv safety) :=
    fun safety => Readiness.add (wf.tr (safety := safety)).map_wf
      (ci := .defnInfo v)
      (by simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using hn)
      (by simp [Lean.ConstantInfo.ReadinessTransparent])
      (leNew safety) (trNew safety).wf (wf.projectionReady (safety := safety))
      (wf.structureEtaReady (safety := safety))
  refine ⟨ves', ?_, leNew⟩
  exact {
    tr {safety} := trNew safety
    hasPrimitives {safety} :=
      match safety with
      | .unsafe => ((wf.hasPrimitives (safety := .unsafe)).addConst_of_not_primitive hnonprim hadd).addDefEq
      | .safe | .partial => wf.hasPrimitives
    safePrimitives := wf.safePrimitives_add (.defnInfo v) hn
      (by simp [ConstantInfo.name, ConstantInfo.toConstantVal, hnonprim])
    mono {safety safety'} hsf :=
      match safety, safety' with
      | .unsafe, .unsafe => .rfl
      | .unsafe, .safe | .unsafe, .partial => (wf.mono hsf).trans hle
      | .safe, .unsafe | .partial, .unsafe => absurd hsf (by decide)
      | .safe, .safe | .safe, .partial | .partial, .safe | .partial, .partial => wf.mono hsf
    -- Tier V (L4L-19B): checker-readiness transport across this front-end
    -- extension; see `VEnvAt.addAxioms`.
    projectionReady {safety} := (readiness safety).1
    structureEtaReady {safety} := (readiness safety).2 }
