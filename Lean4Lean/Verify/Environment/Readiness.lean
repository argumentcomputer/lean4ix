import Lean4Lean.Verify.Environment.Checker

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

/-!
# Readiness under ordinary environment extension

Projection and structure-eta readiness describe artifacts owned by existing
inductive declarations.  Adding an ordinary declaration preserves those
artifacts: the host lookup surface is unchanged at inductive, constructor,
and recursor entries, while the Theory artifact is transported along the
model extension.
-/

/-- Constant kinds which cannot create or replace any host metadata consumed
by projection or structure-eta readiness. -/
def _root_.Lean.ConstantInfo.ReadinessTransparent : ConstantInfo → Prop
  | .inductInfo _ | .ctorInfo _ | .recInfo _ => False
  | _ => True

/-- Lookup through one fresh kernel-environment insertion. -/
theorem Environment.find?_add_eq
    {env : Environment} (mapWF : env.constants.WF)
    (ci : ConstantInfo) (hfresh : env.find? ci.name = none) (name : Name) :
    (env.add ci).find? name =
      if ci.name = name then some ci else env.find? name := by
  have hnone : env.constants.find? ci.name = none := by
    rw [← mapWF.find?'_eq_find?]
    exact hfresh
  have mapWF' := mapWF.insert ci.name ci hnone
  change SMap.find?' (env.constants.insert ci.name ci) name =
    if ci.name = name then some ci else SMap.find?' env.constants name
  rw [mapWF'.find?'_eq_find?, mapWF.find?'_eq_find?, mapWF.find?_insert]
  simp only [beq_iff_eq]

/-- An old lookup can be recovered from a transparent fresh insertion when
the requested result is structural metadata. -/
theorem Environment.find?_of_add_structural
    {env : Environment} (mapWF : env.constants.WF)
    {ci : ConstantInfo} (hfresh : env.find? ci.name = none)
    (htransparent : Lean.ConstantInfo.ReadinessTransparent ci)
    {name : Name} {found : ConstantInfo}
    (hstructural : (∃ info, found = .inductInfo info) ∨
      (∃ info, found = .ctorInfo info) ∨
      (∃ info, found = .recInfo info))
    (hfind : (env.add ci).find? name = some found) :
    env.find? name = some found := by
  rw [Environment.find?_add_eq mapWF ci hfresh name] at hfind
  split at hfind
  · have heq : ci = found := Option.some.inj hfind
    rcases hstructural with ⟨info, rfl⟩ | ⟨info, rfl⟩ | ⟨info, rfl⟩ <;>
      subst ci <;> simp [Lean.ConstantInfo.ReadinessTransparent] at htransparent
  · exact hfind

/-- Absence after a fresh insertion implies absence before it. -/
theorem Environment.find?_eq_none_of_add
    {env : Environment} (mapWF : env.constants.WF)
    (ci : ConstantInfo) (hfresh : env.find? ci.name = none) {name : Name}
    (hfind : (env.add ci).find? name = none) : env.find? name = none := by
  rw [Environment.find?_add_eq mapWF ci hfresh name] at hfind
  split at hfind
  · contradiction
  · exact hfind

/-- A fresh ordinary insertion cannot create or alter recursor rules. -/
theorem Environment.RecursorRulesReductionConstFree.add
    {env : Environment} {name : Name}
    (self : env.RecursorRulesReductionConstFree name)
    (mapWF : env.constants.WF) {ci : ConstantInfo}
    (hfresh : env.find? ci.name = none)
    (htransparent : Lean.ConstantInfo.ReadinessTransparent ci) :
    (env.add ci).RecursorRulesReductionConstFree name := by
  intro recursorName recursor hfind rule hrule
  exact self recursorName recursor
    (Environment.find?_of_add_structural mapWF hfresh htransparent
      (.inr (.inr ⟨recursor, rfl⟩)) hfind)
    rule hrule

/-- Closing every old recursor payload over absent host names survives one
fresh ordinary insertion. -/
theorem Environment.recursorRulesClosed_add
    {env : Environment} (mapWF : env.constants.WF) {ci : ConstantInfo}
    (hfresh : env.find? ci.name = none)
    (htransparent : Lean.ConstantInfo.ReadinessTransparent ci)
    (self : ∀ {name}, env.find? name = none →
      env.RecursorRulesReductionConstFree name) :
    ∀ {name}, (env.add ci).find? name = none →
      (env.add ci).RecursorRulesReductionConstFree name := by
  intro name hfind
  exact Environment.RecursorRulesReductionConstFree.add
    (self (Environment.find?_eq_none_of_add mapWF ci hfresh hfind))
    mapWF hfresh htransparent

/-- Inserting fresh family metadata does not change projection readiness for
any other family.  At dependency names the new entry has inductive kind, so it
cannot masquerade as the constructor or recursor required by the test. -/
theorem Environment.isProjectionReadyStructure_add_inductInfo
    {env : Environment} (mapWF : env.constants.WF)
    (info : InductiveVal) (hfresh : env.find? info.name = none)
    {name : Name} (hne : info.name ≠ name) :
    (env.add (.inductInfo info)).isProjectionReadyStructure name =
      env.isProjectionReadyStructure name := by
  have infoName : (.inductInfo info : ConstantInfo).name = info.name := rfl
  have lookup (query : Name) :
      (env.add (.inductInfo info)).constants.find?' query =
        if info.name = query then some (.inductInfo info)
        else env.constants.find?' query := by
    change (env.add (.inductInfo info)).find? query =
      if info.name = query then some (.inductInfo info) else env.find? query
    simpa only [infoName] using
      Environment.find?_add_eq mapWF (.inductInfo info) hfresh query
  unfold Kernel.Environment.isProjectionReadyStructure
  rw [lookup name, if_neg hne]
  generalize hfamily : env.constants.find?' name = found
  cases found with
  | none => rfl
  | some found =>
    cases found <;> try rfl
    rename_i family
    cases family
    rename_i constant numParams numIndices all ctors numNested isRec
      isUnsafe isReflexive
    cases constant
    cases numIndices <;> try rfl
    cases ctors with
    | nil => rfl
    | cons ctor rest =>
      cases rest with
      | cons _ _ => rfl
      | nil =>
        simp only
        rw [lookup ctor, lookup (mkRecName name)]
        by_cases hc : info.name = ctor
        · have hnone : env.constants.find?' ctor = none := by
            change env.find? ctor = none
            rw [← hc]
            exact hfresh
          simp [hc, hnone]
        · by_cases hr : info.name = mkRecName name
          · have hnone : env.constants.find?' (mkRecName name) = none := by
              change env.find? (mkRecName name) = none
              rw [← hr]
              exact hfresh
            simp [hr, hnone]
          · simp [hc, hr]

/-- Fresh family-only staging preserves large-recursor structure-eta
eligibility at every other family name.  If the staged name collides with a
dependency query, its inductive kind makes both the old and new tests fail. -/
theorem Environment.isStructureEtaReadyConstructor_add_inductInfo
    {env : Environment} (mapWF : env.constants.WF)
    (info : InductiveVal) (hfresh : env.find? info.name = none)
    {family constructor : Name} (hne : info.name ≠ family) :
    (env.add (.inductInfo info)).isStructureEtaReadyConstructor
        family constructor =
      env.isStructureEtaReadyConstructor family constructor := by
  have infoName : (.inductInfo info : ConstantInfo).name = info.name := rfl
  have lookup (query : Name) :
      (env.add (.inductInfo info)).find? query =
        if info.name = query then some (.inductInfo info)
        else env.find? query := by
    simpa only [infoName] using
      Environment.find?_add_eq mapWF (.inductInfo info) hfresh query
  unfold Kernel.Environment.isStructureEtaReadyConstructor
  unfold Kernel.Environment.isNonRecStructureConstructor
  rw [lookup family, if_neg hne, lookup constructor,
    lookup (mkRecName family)]
  by_cases hc : info.name = constructor
  · have hnone : env.find? constructor = none := by
      rw [← hc]
      exact hfresh
    simp [hc, hnone]
  · by_cases hr : info.name = mkRecName family
    · have hnone : env.find? (mkRecName family) = none := by
        rw [← hr]
        exact hfresh
      simp [hc, hr, hnone]
    · simp [hc, hr]

/-- A fresh multi-constructor family is not projection-ready at its own name. -/
theorem Environment.isProjectionReadyStructure_add_inductInfo_self
    {env : Environment} (mapWF : env.constants.WF)
    (info : InductiveVal) (hfresh : env.find? info.name = none)
    (hctors : info.ctors.length ≠ 1) :
    (env.add (.inductInfo info)).isProjectionReadyStructure info.name =
      false := by
  have infoName : (.inductInfo info : ConstantInfo).name = info.name := rfl
  have lookup :
      (env.add (.inductInfo info)).constants.find?' info.name =
        some (.inductInfo info) := by
    change (env.add (.inductInfo info)).find? info.name = _
    rw [Environment.find?_add_eq mapWF (.inductInfo info) hfresh]
    simp only [infoName, if_pos]
  unfold Kernel.Environment.isProjectionReadyStructure
  rw [lookup]
  cases info
  rename_i constant numParams numIndices all ctors numNested isRec
    isUnsafe isReflexive
  cases constant
  cases numIndices <;> try rfl
  cases ctors with
  | nil => rfl
  | cons ctor rest =>
    cases rest with
    | nil => simp at hctors
    | cons _ _ => rfl

/-- A freshly staged one-constructor family is not projection-ready when its
constructor has not yet reached the host environment.  This is the ordinary
family-only staging case; unlike the multi-constructor shortcut above, it
also covers singleton families without pretending their constructor metadata
was declared early. -/
theorem Environment.isProjectionReadyStructure_add_inductInfo_self_of_ctor_absent
    {env : Environment} (mapWF : env.constants.WF)
    (info : InductiveVal) (hfresh : env.find? info.name = none)
    (ctor : Name) (hctors : info.ctors = [ctor])
    (hctor : env.find? ctor = none) :
    (env.add (.inductInfo info)).isProjectionReadyStructure info.name =
      false := by
  let added := env.add (.inductInfo info)
  change added.isProjectionReadyStructure info.name = false
  have infoName : (.inductInfo info : ConstantInfo).name = info.name := rfl
  have ctorNotInfo (ctorInfo : ConstructorVal) :
      added.constants.find?' ctor ≠ some (.ctorInfo ctorInfo) := by
    intro found
    change (env.add (.inductInfo info)).find? ctor =
      some (.ctorInfo ctorInfo) at found
    rw [Environment.find?_add_eq mapWF (.inductInfo info) hfresh] at found
    split at found
    · cases found
    · rw [hctor] at found
      cases found
  have familyLookup :
      added.constants.find?' info.name = some (.inductInfo info) := by
    change (env.add (.inductInfo info)).find? info.name = _
    rw [Environment.find?_add_eq mapWF (.inductInfo info) hfresh]
    simp only [infoName, if_pos]
  unfold Kernel.Environment.isProjectionReadyStructure
  rw [familyLookup]
  cases info
  rename_i constant numParams numIndices all ctors numNested isRec
    isUnsafe isReflexive
  cases constant
  cases numIndices with
  | succ _ => rfl
  | zero =>
    cases ctors with
    | nil => simp at hctors
    | cons head rest =>
      cases rest with
      | cons next tail => simp at hctors
      | nil =>
        have head_eq : head = ctor := by simpa using hctors
        subst head
        generalize found_eq : added.constants.find?' ctor = found
        cases found with
        | none => simp [found_eq]
        | some found =>
          cases found <;> simp_all

/-- Inserting fresh family metadata does not change the nonrecursive-structure
test at any other family name. -/
theorem Environment.isNonRecStructure_add_inductInfo
    {env : Environment} (mapWF : env.constants.WF)
    (info : InductiveVal) (hfresh : env.find? info.name = none)
    {name : Name} (hne : info.name ≠ name) :
    (env.add (.inductInfo info)).isNonRecStructure name =
      env.isNonRecStructure name := by
  have infoName : (.inductInfo info : ConstantInfo).name = info.name := rfl
  have lookup :
      (env.add (.inductInfo info)).find? name =
        if info.name = name then some (.inductInfo info)
        else env.find? name := by
    simpa only [infoName] using
      Environment.find?_add_eq mapWF (.inductInfo info) hfresh name
  unfold Kernel.Environment.isNonRecStructure
  rw [lookup]
  simp [hne]

/-- A fresh multi-constructor family is not a nonrecursive structure at its
own name. -/
theorem Environment.isNonRecStructure_add_inductInfo_self
    {env : Environment} (mapWF : env.constants.WF)
    (info : InductiveVal) (hfresh : env.find? info.name = none)
    (hctors : info.ctors.length ≠ 1) :
    (env.add (.inductInfo info)).isNonRecStructure info.name = false := by
  have infoName : (.inductInfo info : ConstantInfo).name = info.name := rfl
  have lookup :
      (env.add (.inductInfo info)).find? info.name =
        some (.inductInfo info) := by
    rw [Environment.find?_add_eq mapWF (.inductInfo info) hfresh]
    simp only [infoName, if_pos]
  unfold Kernel.Environment.isNonRecStructure
  rw [lookup]
  cases info
  rename_i constant numParams numIndices all ctors numNested isRec
    isUnsafe isReflexive
  cases constant
  cases isRec with
  | true => simp
  | false =>
    cases numIndices <;> try rfl
    cases ctors with
    | nil => rfl
    | cons ctor rest =>
      cases rest with
      | nil => simp at hctors
      | cons _ _ => rfl

/-- Recursive family metadata cannot trigger Lean's nonrecursive-structure
test, even when the family has exactly one constructor. -/
theorem Environment.isNonRecStructure_add_inductInfo_self_of_isRec
    {env : Environment} (mapWF : env.constants.WF)
    (info : InductiveVal) (hfresh : env.find? info.name = none)
    (hisRec : info.isRec = true) :
    (env.add (.inductInfo info)).isNonRecStructure info.name = false := by
  have infoName : (.inductInfo info : ConstantInfo).name = info.name := rfl
  have lookup :
      (env.add (.inductInfo info)).find? info.name =
        some (.inductInfo info) := by
    rw [Environment.find?_add_eq mapWF (.inductInfo info) hfresh]
    simp only [infoName, if_pos]
  unfold Kernel.Environment.isNonRecStructure
  rw [lookup]
  cases info
  simp_all

/-- A projection artifact persists along a Theory-environment extension and
an ordinary host declaration insertion. -/
def ProjectionArtifact.add
    {env : Environment} (mapWF : env.constants.WF)
    {ci : ConstantInfo} (hfresh : env.find? ci.name = none)
    (_htransparent : Lean.ConstantInfo.ReadinessTransparent ci)
    {venv venv' : VEnv} (hle : venv ≤ venv')
    (self : ProjectionArtifact env name info venv) :
    ProjectionArtifact (env.add ci) name info venv' where
  view := self.view
  name_eq := self.name_eq
  viewWF := self.viewWF.mono hle
  constructorInfo := self.constructorInfo
  constructor_find := by
    rw [Environment.find?_add_eq mapWF ci hfresh self.view.constructorName,
      if_neg]
    · exact self.constructor_find
    · intro heq
      have hold := self.constructor_find
      rw [← heq, hfresh] at hold
      contradiction
  recursorInfo := self.recursorInfo
  recursor_find := by
    rw [Environment.find?_add_eq mapWF ci hfresh self.view.recursorName,
      if_neg]
    · exact self.recursor_find
    · intro heq
      have hold := self.recursor_find
      rw [← heq, hfresh] at hold
      contradiction
  recursor_levelParams_length := self.recursor_levelParams_length
  constructor_numParams_eq := self.constructor_numParams_eq
  constructor_numFields_eq := self.constructor_numFields_eq
  levelParams_length := self.levelParams_length
  numParams_eq := self.numParams_eq
  numIndices_eq := self.numIndices_eq
  ctors_eq := self.ctors_eq
  programs := self.programs.mono hle

/-- A restored projection artifact persists along the same transparent host
insertion as an ordinary artifact.  Its operational payload is purely
Theory-side, so only the cached constructor and recursor lookups need to be
re-established. -/
def RestoredProjectionArtifact.add
    {env : Environment} (mapWF : env.constants.WF)
    {ci : ConstantInfo} (hfresh : env.find? ci.name = none)
    (_htransparent : Lean.ConstantInfo.ReadinessTransparent ci)
    {venv venv' : VEnv} (hle : venv ≤ venv')
    (self : RestoredProjectionArtifact env name info venv) :
    RestoredProjectionArtifact (env.add ci) name info venv' where
  view := self.view
  name_eq := self.name_eq
  viewWF := self.viewWF.mono hle
  constructorInfo := self.constructorInfo
  constructor_find := by
    rw [Environment.find?_add_eq mapWF ci hfresh self.view.constructorName,
      if_neg]
    · exact self.constructor_find
    · intro heq
      have hold := self.constructor_find
      rw [← heq, hfresh] at hold
      contradiction
  recursorInfo := self.recursorInfo
  recursor_find := by
    rw [Environment.find?_add_eq mapWF ci hfresh self.view.recursorName,
      if_neg]
    · exact self.recursor_find
    · intro heq
      have hold := self.recursor_find
      rw [← heq, hfresh] at hold
      contradiction
  recursor_levelParams_length := self.recursor_levelParams_length
  constructor_numParams_eq := self.constructor_numParams_eq
  constructor_numFields_eq := self.constructor_numFields_eq
  levelParams_length := self.levelParams_length
  numParams_eq := self.numParams_eq
  numIndices_eq := self.numIndices_eq
  ctors_eq := self.ctors_eq
  recEntriesClosed := self.recEntriesClosed
  codeNaturality := self.codeNaturality
  parameterLayout := self.parameterLayout.mono hle
  programs := self.programs.mono hle
  largeRebuilds large {_venv''} hle' hregular :=
    self.largeRebuilds large (hle.trans hle') hregular

/-- Backend-independent artifact transport across a transparent insertion. -/
def ProjectionArtifactResolution.add
    {env : Environment} (mapWF : env.constants.WF)
    {ci : ConstantInfo} (hfresh : env.find? ci.name = none)
    (htransparent : Lean.ConstantInfo.ReadinessTransparent ci)
    {venv venv' : VEnv} (hle : venv ≤ venv')
    (self : ProjectionArtifactResolution env name info venv) :
    ProjectionArtifactResolution (env.add ci) name info venv' := by
  cases self with
  | ordinary artifact =>
      exact .ordinary (artifact.add mapWF hfresh htransparent hle)
  | restored artifact =>
      exact .restored (artifact.add mapWF hfresh htransparent hle)

/-- A projection artifact persists when only the abstract model grows. -/
def ProjectionArtifact.mono
    {venv venv' : VEnv} (hle : venv ≤ venv')
    (self : ProjectionArtifact env name info venv) :
    ProjectionArtifact env name info venv' where
  view := self.view
  name_eq := self.name_eq
  viewWF := self.viewWF.mono hle
  constructorInfo := self.constructorInfo
  constructor_find := self.constructor_find
  recursorInfo := self.recursorInfo
  recursor_find := self.recursor_find
  recursor_levelParams_length := self.recursor_levelParams_length
  constructor_numParams_eq := self.constructor_numParams_eq
  constructor_numFields_eq := self.constructor_numFields_eq
  levelParams_length := self.levelParams_length
  numParams_eq := self.numParams_eq
  numIndices_eq := self.numIndices_eq
  ctors_eq := self.ctors_eq
  programs := self.programs.mono hle

/-- Resolution is monotone in the Theory environment, independently for the
ordinary and restored backends. -/
def ProjectionArtifactResolution.mono
    {env : Environment} {name : Name} {info : InductiveVal}
    {venv venv' : VEnv}
    (self : ProjectionArtifactResolution env name info venv)
    (hle : venv ≤ venv') :
    ProjectionArtifactResolution env name info venv' := by
  cases self with
  | ordinary artifact => exact .ordinary (artifact.mono hle)
  | restored artifact => exact .restored (artifact.mono hle)

/-- Resolution-aware readiness persists under Theory-environment growth. -/
theorem ProjectionResolutionReady.mono
    {env : Environment} {venv venv' : VEnv}
    (self : ProjectionResolutionReady env venv) (hle : venv ≤ venv') :
    ProjectionResolutionReady env venv' where
  infer name info found ready := by
    obtain ⟨artifact⟩ := self.infer name info found ready
    exact ⟨artifact.mono hle⟩
  constructorHead name info found :=
    (self.constructorHead name info found).mono hle

/-- An existing projection artifact fixes the host parameter count for every
later registered view with the same family and constructor names.  Family
arity rigidity supplies the Theory-side equality; exact host lookup supplies
the constructor-record equality.  No open-world quantification over
unrelated future views is used. -/
theorem ProjectionArtifact.constructorNumParams_of_alignedView
    {env : Environment} {name : Name} {familyInfo : InductiveVal}
    {venv venv' : VEnv}
    (self : ProjectionArtifact env name familyInfo venv)
    (hle : venv ≤ venv')
    (view : VProjectionView) (info : ConstructorVal)
    (hview : view.LayoutWF venv')
    (family_name_eq : view.name = self.view.name)
    (constructor_name_eq :
      view.constructorName = self.view.constructorName)
    (hfind : env.find? view.constructorName = some (.ctorInfo info)) :
    info.numParams = view.nparams := by
  have infoEq : info = self.constructorInfo := by
    rw [constructor_name_eq] at hfind
    exact ConstantInfo.ctorInfo.inj <|
      Option.some.inj (hfind.symm.trans self.constructor_find)
  calc
    info.numParams = self.constructorInfo.numParams := by rw [infoEq]
    _ = self.view.nparams := self.constructor_numParams_eq
    _ = view.nparams :=
      (self.viewWF.mono hle).nparams_eq_of_name_eq hview
        family_name_eq.symm

/-- A projection artifact may be retargeted to an arbitrary host environment
once its one host-dependent observation—the exact constructor lookup—is
re-established there.  The abstract model may grow at the same time. -/
def ProjectionArtifact.retarget
    (self : ProjectionArtifact env name info venv)
    {env' : Environment} {venv' : VEnv} (hle : venv ≤ venv')
    (constructor_find : env'.find? self.view.constructorName =
      some (.ctorInfo self.constructorInfo))
    (recursor_find : env'.find? self.view.recursorName =
      some (.recInfo self.recursorInfo)) :
    ProjectionArtifact env' name info venv' where
  view := self.view
  name_eq := self.name_eq
  viewWF := self.viewWF.mono hle
  constructorInfo := self.constructorInfo
  constructor_find := constructor_find
  recursorInfo := self.recursorInfo
  recursor_find := recursor_find
  recursor_levelParams_length := self.recursor_levelParams_length
  constructor_numParams_eq := self.constructor_numParams_eq
  constructor_numFields_eq := self.constructor_numFields_eq
  levelParams_length := self.levelParams_length
  numParams_eq := self.numParams_eq
  numIndices_eq := self.numIndices_eq
  ctors_eq := self.ctors_eq
  programs := self.programs.mono hle

/-- Retarget a restored artifact once its two exact host observations have
been replayed at the new endpoint. -/
def RestoredProjectionArtifact.retarget
    (self : RestoredProjectionArtifact env name info venv)
    {env' : Environment} {venv' : VEnv} (hle : venv ≤ venv')
    (constructor_find : env'.find? self.view.constructorName =
      some (.ctorInfo self.constructorInfo))
    (recursor_find : env'.find? self.view.recursorName =
      some (.recInfo self.recursorInfo)) :
    RestoredProjectionArtifact env' name info venv' where
  view := self.view
  name_eq := self.name_eq
  viewWF := self.viewWF.mono hle
  constructorInfo := self.constructorInfo
  constructor_find := constructor_find
  recursorInfo := self.recursorInfo
  recursor_find := recursor_find
  recursor_levelParams_length := self.recursor_levelParams_length
  constructor_numParams_eq := self.constructor_numParams_eq
  constructor_numFields_eq := self.constructor_numFields_eq
  levelParams_length := self.levelParams_length
  numParams_eq := self.numParams_eq
  numIndices_eq := self.numIndices_eq
  ctors_eq := self.ctors_eq
  recEntriesClosed := self.recEntriesClosed
  codeNaturality := self.codeNaturality
  parameterLayout := self.parameterLayout.mono hle
  programs := self.programs.mono hle
  largeRebuilds large {_venv''} hle' hregular :=
    self.largeRebuilds large (hle.trans hle') hregular

/-- Retarget either resolved backend whenever the surrounding host
transaction preserves every constructor and recursor observation. -/
def ProjectionArtifactResolution.retarget_of_preserved
    (self : ProjectionArtifactResolution env name info venv)
    {env' : Environment} {venv' : VEnv} (hle : venv ≤ venv')
    (constructorPreserved : ∀ {n constructorInfo},
      env.find? n = some (.ctorInfo constructorInfo) →
        env'.find? n = some (.ctorInfo constructorInfo))
    (recursorPreserved : ∀ {n recursorInfo},
      env.find? n = some (.recInfo recursorInfo) →
        env'.find? n = some (.recInfo recursorInfo)) :
    ProjectionArtifactResolution env' name info venv' := by
  cases self with
  | ordinary artifact =>
      exact .ordinary <| artifact.retarget hle
        (constructorPreserved artifact.constructor_find)
        (recursorPreserved artifact.recursor_find)
  | restored artifact =>
      exact .restored <| artifact.retarget hle
        (constructorPreserved artifact.constructor_find)
        (recursorPreserved artifact.recursor_find)

/-- A projection artifact depends only on the host constant map, not on the
module header or the other administrative fields of the kernel environment. -/
def ProjectionArtifact.of_constants_eq
    {env env' : Environment} (hconstants : env.constants = env'.constants)
    (self : ProjectionArtifact env name info venv) :
    ProjectionArtifact env' name info venv where
  view := self.view
  name_eq := self.name_eq
  viewWF := self.viewWF
  constructorInfo := self.constructorInfo
  constructor_find := by
    change env'.constants.find?' self.view.constructorName = _
    rw [← hconstants]
    exact self.constructor_find
  recursorInfo := self.recursorInfo
  recursor_find := by
    change env'.constants.find?' self.view.recursorName = _
    rw [← hconstants]
    exact self.recursor_find
  recursor_levelParams_length := self.recursor_levelParams_length
  constructor_numParams_eq := self.constructor_numParams_eq
  constructor_numFields_eq := self.constructor_numFields_eq
  levelParams_length := self.levelParams_length
  numParams_eq := self.numParams_eq
  numIndices_eq := self.numIndices_eq
  ctors_eq := self.ctors_eq
  programs := self.programs

/-- Restored artifacts, like ordinary artifacts, depend only on the host
constant map. -/
def RestoredProjectionArtifact.of_constants_eq
    {env env' : Environment} (hconstants : env.constants = env'.constants)
    (self : RestoredProjectionArtifact env name info venv) :
    RestoredProjectionArtifact env' name info venv where
  view := self.view
  name_eq := self.name_eq
  viewWF := self.viewWF
  constructorInfo := self.constructorInfo
  constructor_find := by
    change env'.constants.find?' self.view.constructorName = _
    rw [← hconstants]
    exact self.constructor_find
  recursorInfo := self.recursorInfo
  recursor_find := by
    change env'.constants.find?' self.view.recursorName = _
    rw [← hconstants]
    exact self.recursor_find
  recursor_levelParams_length := self.recursor_levelParams_length
  constructor_numParams_eq := self.constructor_numParams_eq
  constructor_numFields_eq := self.constructor_numFields_eq
  levelParams_length := self.levelParams_length
  numParams_eq := self.numParams_eq
  numIndices_eq := self.numIndices_eq
  ctors_eq := self.ctors_eq
  recEntriesClosed := self.recEntriesClosed
  codeNaturality := self.codeNaturality
  parameterLayout := self.parameterLayout
  programs := self.programs
  largeRebuilds := self.largeRebuilds

/-- Resolution artifacts are invariant under changes outside the host
constant map. -/
def ProjectionArtifactResolution.of_constants_eq
    {env env' : Environment} (hconstants : env.constants = env'.constants)
    (self : ProjectionArtifactResolution env name info venv) :
    ProjectionArtifactResolution env' name info venv := by
  cases self with
  | ordinary artifact => exact .ordinary (artifact.of_constants_eq hconstants)
  | restored artifact => exact .restored (artifact.of_constants_eq hconstants)

/-- Projection readiness is invariant under changes to host-environment fields
other than the constant map. -/
theorem ProjectionReady.of_constants_eq
    {env env' : Environment} (hconstants : env.constants = env'.constants)
    (self : ProjectionReady env venv) : ProjectionReady env' venv where
  infer name info hfind hready := by
    have hfind' : env.find? name = some (.inductInfo info) := by
      change env'.constants.find?' name = _ at hfind
      change env.constants.find?' name = _
      rwa [hconstants]
    have hready' : env.isProjectionReadyStructure name = true := by
      simpa only [Kernel.Environment.isProjectionReadyStructure, hconstants]
        using hready
    obtain ⟨artifact⟩ := self.infer name info hfind' hready'
    exact ⟨artifact.of_constants_eq hconstants⟩
  constructorHead name info hfind := by
    apply self.constructorHead name info
    change env'.constants.find?' name = _ at hfind
    change env.constants.find?' name = _
    rwa [hconstants]

/-- Resolution-aware readiness is likewise determined by the host constant
map alone. -/
theorem ProjectionResolutionReady.of_constants_eq
    {env env' : Environment} (hconstants : env.constants = env'.constants)
    (self : ProjectionResolutionReady env venv) :
    ProjectionResolutionReady env' venv where
  infer name info hfind hready := by
    have hfind' : env.find? name = some (.inductInfo info) := by
      change env'.constants.find?' name = _ at hfind
      change env.constants.find?' name = _
      rwa [hconstants]
    have hready' : env.isProjectionReadyStructure name = true := by
      simpa only [Kernel.Environment.isProjectionReadyStructure, hconstants]
        using hready
    obtain ⟨artifact⟩ := self.infer name info hfind' hready'
    exact ⟨artifact.of_constants_eq hconstants⟩
  constructorHead name info hfind := by
    apply self.constructorHead name info
    change env'.constants.find?' name = _ at hfind
    change env.constants.find?' name = _
    rwa [hconstants]

/-- A projection artifact for an existing family persists while fresh
family-only metadata is staged and the abstract model grows. -/
def ProjectionArtifact.addInductInfo
    {env : Environment} (mapWF : env.constants.WF)
    (info' : InductiveVal) (hfresh : env.find? info'.name = none)
    {venv venv' : VEnv} (hle : venv ≤ venv')
    (self : ProjectionArtifact env name info venv) :
    ProjectionArtifact (env.add (.inductInfo info')) name info venv' where
  view := self.view
  name_eq := self.name_eq
  viewWF := self.viewWF.mono hle
  constructorInfo := self.constructorInfo
  constructor_find := by
    have infoName : (.inductInfo info' : ConstantInfo).name = info'.name := rfl
    rw [Environment.find?_add_eq mapWF (.inductInfo info') hfresh]
    rw [if_neg]
    · exact self.constructor_find
    · intro heq
      have old := self.constructor_find
      change env.find? self.view.constructorName = _ at old
      have heq' : info'.name = self.view.constructorName :=
        infoName.symm.trans heq
      rw [← heq', hfresh] at old
      contradiction
  recursorInfo := self.recursorInfo
  recursor_find := by
    have infoName : (.inductInfo info' : ConstantInfo).name = info'.name := rfl
    rw [Environment.find?_add_eq mapWF (.inductInfo info') hfresh]
    rw [if_neg]
    · exact self.recursor_find
    · intro heq
      have old := self.recursor_find
      change env.find? self.view.recursorName = _ at old
      have heq' : info'.name = self.view.recursorName :=
        infoName.symm.trans heq
      rw [← heq', hfresh] at old
      contradiction
  recursor_levelParams_length := self.recursor_levelParams_length
  constructor_numParams_eq := self.constructor_numParams_eq
  constructor_numFields_eq := self.constructor_numFields_eq
  levelParams_length := self.levelParams_length
  numParams_eq := self.numParams_eq
  numIndices_eq := self.numIndices_eq
  ctors_eq := self.ctors_eq
  programs := self.programs.mono hle

/-- A restored artifact also persists through family-only staging. -/
def RestoredProjectionArtifact.addInductInfo
    {env : Environment} (mapWF : env.constants.WF)
    (info' : InductiveVal) (hfresh : env.find? info'.name = none)
    {venv venv' : VEnv} (hle : venv ≤ venv')
    (self : RestoredProjectionArtifact env name info venv) :
    RestoredProjectionArtifact (env.add (.inductInfo info')) name info venv' :=
  self.retarget hle (by
    have infoName : (.inductInfo info' : ConstantInfo).name = info'.name := rfl
    rw [Environment.find?_add_eq mapWF (.inductInfo info') hfresh]
    rw [if_neg]
    · exact self.constructor_find
    · intro heq
      have old := self.constructor_find
      change env.find? self.view.constructorName = _ at old
      have heq' : info'.name = self.view.constructorName :=
        infoName.symm.trans heq
      rw [← heq', hfresh] at old
      contradiction) (by
    have infoName : (.inductInfo info' : ConstantInfo).name = info'.name := rfl
    rw [Environment.find?_add_eq mapWF (.inductInfo info') hfresh]
    rw [if_neg]
    · exact self.recursor_find
    · intro heq
      have old := self.recursor_find
      change env.find? self.view.recursorName = _ at old
      have heq' : info'.name = self.view.recursorName :=
        infoName.symm.trans heq
      rw [← heq', hfresh] at old
      contradiction)

/-- Backend-independent artifact transport through family-only staging. -/
def ProjectionArtifactResolution.addInductInfo
    {env : Environment} (mapWF : env.constants.WF)
    (info' : InductiveVal) (hfresh : env.find? info'.name = none)
    {venv venv' : VEnv} (hle : venv ≤ venv')
    (self : ProjectionArtifactResolution env name info venv) :
    ProjectionArtifactResolution (env.add (.inductInfo info')) name info venv' := by
  cases self with
  | ordinary artifact =>
      exact .ordinary (artifact.addInductInfo mapWF info' hfresh hle)
  | restored artifact =>
      exact .restored (artifact.addInductInfo mapWF info' hfresh hle)

/-- Projection readiness survives staging one fresh multi-constructor family.
Such metadata cannot itself become projection-ready before constructor and
recursor declaration, while all existing artifacts are transported. -/
theorem ProjectionReady.addInductInfo
    {env : Environment} (mapWF : env.constants.WF)
    (info' : InductiveVal) (hfresh : env.find? info'.name = none)
    (hctors : info'.ctors.length ≠ 1)
    {venv venv' : VEnv} (hle : venv ≤ venv')
    (self : ProjectionReady env venv) :
    ProjectionReady (env.add (.inductInfo info')) venv' where
  infer name info hfind hready := by
    by_cases heq : info'.name = name
    · subst name
      rw [Environment.isProjectionReadyStructure_add_inductInfo_self
        mapWF info' hfresh hctors] at hready
      contradiction
    · have hfind' : env.find? name = some (.inductInfo info) := by
        rw [Environment.find?_add_eq mapWF (.inductInfo info') hfresh]
          at hfind
        have infoName : (.inductInfo info' : ConstantInfo).name =
            info'.name := rfl
        simpa only [infoName, if_neg heq] using hfind
      have hready' : env.isProjectionReadyStructure name = true := by
        rw [← Environment.isProjectionReadyStructure_add_inductInfo
          mapWF info' hfresh heq]
        exact hready
      obtain ⟨artifact⟩ := self.infer name info hfind' hready'
      exact ⟨artifact.addInductInfo mapWF info' hfresh hle⟩
  constructorHead name info hfind := by
    apply (self.constructorHead name info ?_).mono hle
    rw [Environment.find?_add_eq mapWF (.inductInfo info') hfresh] at hfind
    split at hfind
    · cases hfind
    · exact hfind

/-- Projection readiness also survives staging a fresh singleton family when
its sole constructor has not yet been declared.  This is the exact
family-only boundary used by the ordinary inductive producer. -/
theorem ProjectionReady.addInductInfo_of_ctor_absent
    {env : Environment} (mapWF : env.constants.WF)
    (info' : InductiveVal) (hfresh : env.find? info'.name = none)
    (ctor : Name) (hctors : info'.ctors = [ctor])
    (hctor : env.find? ctor = none)
    {venv venv' : VEnv} (hle : venv ≤ venv')
    (self : ProjectionReady env venv) :
    ProjectionReady (env.add (.inductInfo info')) venv' where
  infer name info hfind hready := by
    by_cases heq : info'.name = name
    · subst name
      rw [Environment.isProjectionReadyStructure_add_inductInfo_self_of_ctor_absent
        mapWF info' hfresh ctor hctors hctor] at hready
      contradiction
    · have hfind' : env.find? name = some (.inductInfo info) := by
        rw [Environment.find?_add_eq mapWF (.inductInfo info') hfresh]
          at hfind
        have infoName : (.inductInfo info' : ConstantInfo).name =
            info'.name := rfl
        simpa only [infoName, if_neg heq] using hfind
      have hready' : env.isProjectionReadyStructure name = true := by
        rw [← Environment.isProjectionReadyStructure_add_inductInfo
          mapWF info' hfresh heq]
        exact hready
      obtain ⟨artifact⟩ := self.infer name info hfind' hready'
      exact ⟨artifact.addInductInfo mapWF info' hfresh hle⟩
  constructorHead name info hfind := by
    apply (self.constructorHead name info ?_).mono hle
    rw [Environment.find?_add_eq mapWF (.inductInfo info') hfresh] at hfind
    split at hfind
    · cases hfind
    · exact hfind

/-- Resolution-aware readiness survives staging one fresh
multi-constructor family. -/
theorem ProjectionResolutionReady.addInductInfo
    {env : Environment} (mapWF : env.constants.WF)
    (info' : InductiveVal) (hfresh : env.find? info'.name = none)
    (hctors : info'.ctors.length ≠ 1)
    {venv venv' : VEnv} (hle : venv ≤ venv')
    (self : ProjectionResolutionReady env venv) :
    ProjectionResolutionReady (env.add (.inductInfo info')) venv' where
  infer name info hfind hready := by
    by_cases heq : info'.name = name
    · subst name
      rw [Environment.isProjectionReadyStructure_add_inductInfo_self
        mapWF info' hfresh hctors] at hready
      contradiction
    · have hfind' : env.find? name = some (.inductInfo info) := by
        rw [Environment.find?_add_eq mapWF (.inductInfo info') hfresh]
          at hfind
        have infoName : (.inductInfo info' : ConstantInfo).name =
            info'.name := rfl
        simpa only [infoName, if_neg heq] using hfind
      have hready' : env.isProjectionReadyStructure name = true := by
        rw [← Environment.isProjectionReadyStructure_add_inductInfo
          mapWF info' hfresh heq]
        exact hready
      obtain ⟨artifact⟩ := self.infer name info hfind' hready'
      exact ⟨artifact.addInductInfo mapWF info' hfresh hle⟩
  constructorHead name info hfind := by
    apply (self.constructorHead name info ?_).mono hle
    rw [Environment.find?_add_eq mapWF (.inductInfo info') hfresh] at hfind
    split at hfind
    · cases hfind
    · exact hfind

/-- Resolution-aware readiness also survives staging a fresh singleton
family while its sole constructor is absent. -/
theorem ProjectionResolutionReady.addInductInfo_of_ctor_absent
    {env : Environment} (mapWF : env.constants.WF)
    (info' : InductiveVal) (hfresh : env.find? info'.name = none)
    (ctor : Name) (hctors : info'.ctors = [ctor])
    (hctor : env.find? ctor = none)
    {venv venv' : VEnv} (hle : venv ≤ venv')
    (self : ProjectionResolutionReady env venv) :
    ProjectionResolutionReady (env.add (.inductInfo info')) venv' where
  infer name info hfind hready := by
    by_cases heq : info'.name = name
    · subst name
      rw [Environment.isProjectionReadyStructure_add_inductInfo_self_of_ctor_absent
        mapWF info' hfresh ctor hctors hctor] at hready
      contradiction
    · have hfind' : env.find? name = some (.inductInfo info) := by
        rw [Environment.find?_add_eq mapWF (.inductInfo info') hfresh]
          at hfind
        have infoName : (.inductInfo info' : ConstantInfo).name =
            info'.name := rfl
        simpa only [infoName, if_neg heq] using hfind
      have hready' : env.isProjectionReadyStructure name = true := by
        rw [← Environment.isProjectionReadyStructure_add_inductInfo
          mapWF info' hfresh heq]
        exact hready
      obtain ⟨artifact⟩ := self.infer name info hfind' hready'
      exact ⟨artifact.addInductInfo mapWF info' hfresh hle⟩
  constructorHead name info hfind := by
    apply (self.constructorHead name info ?_).mono hle
    rw [Environment.find?_add_eq mapWF (.inductInfo info') hfresh] at hfind
    split at hfind
    · cases hfind
    · exact hfind

/-- Projection readiness is monotone in the abstract model. -/
theorem ProjectionReady.mono
    {venv venv' : VEnv} (hle : venv ≤ venv')
    (self : ProjectionReady env venv) : ProjectionReady env venv' where
  infer name info hfind hready := by
    obtain ⟨artifact⟩ := self.infer name info hfind hready
    exact ⟨artifact.mono hle⟩
  constructorHead name info hfind :=
    (self.constructorHead name info hfind).mono hle

/-- Projection readiness survives one transparent, fresh host declaration
and a monotone extension of its abstract model. -/
theorem ProjectionReady.add
    {env : Environment} (mapWF : env.constants.WF)
    {ci : ConstantInfo} (hfresh : env.find? ci.name = none)
    (htransparent : Lean.ConstantInfo.ReadinessTransparent ci)
    {venv venv' : VEnv} (hle : venv ≤ venv')
    (self : ProjectionReady env venv) :
    ProjectionReady (env.add ci) venv' where
  infer name info hfind hready := by
    have hfindOld : env.find? name = some (.inductInfo info) :=
      Environment.find?_of_add_structural mapWF hfresh htransparent
        (.inl ⟨info, rfl⟩) hfind
    have hreadyOld : env.isProjectionReadyStructure name = true := by
      change (env.add ci).constants.find?' name =
        some (.inductInfo info) at hfind
      change env.constants.find?' name = some (.inductInfo info) at hfindOld
      cases info
      rename_i constant numParams numIndices all ctors numNested isRec
        isUnsafe isReflexive
      cases constant
      rename_i familyName levelParams type
      unfold Kernel.Environment.isProjectionReadyStructure at hready ⊢
      rw [hfind] at hready
      rw [hfindOld]
      cases numIndices with
      | succ n => simp at hready
      | zero =>
        cases ctors with
        | nil => simp at hready
        | cons ctor rest =>
          cases rest with
          | cons next tail => simp at hready
          | nil =>
            change (match (env.add ci).constants.find?' ctor,
                (env.add ci).constants.find?' (mkRecName name) with
              | some (.ctorInfo ctorInfo), some (.recInfo recInfo) =>
                  ctorInfo.induct == name && recInfo.all.contains name
              | _, _ => false) = true at hready
            change (match env.constants.find?' ctor,
                env.constants.find?' (mkRecName name) with
              | some (.ctorInfo ctorInfo), some (.recInfo recInfo) =>
                  ctorInfo.induct == name && recInfo.all.contains name
              | _, _ => false) = true
            generalize hc : (env.add ci).constants.find?' ctor =
              ctorFound at hready
            cases ctorFound with
            | none => simp at hready
            | some ctorFound =>
              cases ctorFound <;> try { simp at hready }
              case ctorInfo ctorInfo =>
                generalize hr : (env.add ci).constants.find?'
                  (mkRecName name) = recFound at hready
                cases recFound with
                | none => simp at hready
                | some recFound =>
                  cases recFound <;> try { simp at hready }
                  case recInfo recInfo =>
                    have hc' : (env.add ci).find? ctor =
                        some (.ctorInfo ctorInfo) := by
                      change (env.add ci).constants.find?' ctor = _
                      exact hc
                    have hr' : (env.add ci).find? (mkRecName name) =
                        some (.recInfo recInfo) := by
                      change (env.add ci).constants.find?' (mkRecName name) = _
                      exact hr
                    have hctor : env.find? ctor = some (.ctorInfo ctorInfo) :=
                      Environment.find?_of_add_structural mapWF hfresh htransparent
                        (.inr (.inl ⟨ctorInfo, rfl⟩)) hc'
                    have hrec : env.find? (mkRecName name) = some (.recInfo recInfo) :=
                      Environment.find?_of_add_structural mapWF hfresh htransparent
                        (.inr (.inr ⟨recInfo, rfl⟩)) hr'
                    change env.constants.find?' ctor =
                      some (.ctorInfo ctorInfo) at hctor
                    change env.constants.find?' (mkRecName name) =
                      some (.recInfo recInfo) at hrec
                    rw [hctor, hrec]
                    simpa only using hready
    obtain ⟨artifact⟩ := self.infer name info hfindOld hreadyOld
    exact ⟨artifact.add mapWF hfresh htransparent hle⟩
  constructorHead name info hfind := by
    have hfindOld : env.find? name = some (.ctorInfo info) :=
      Environment.find?_of_add_structural mapWF hfresh htransparent
        (.inr (.inl ⟨info, rfl⟩)) hfind
    exact (self.constructorHead name info hfindOld).mono hle

/-- Resolution-aware projection readiness survives one transparent, fresh
host declaration and a monotone Theory extension. -/
theorem ProjectionResolutionReady.add
    {env : Environment} (mapWF : env.constants.WF)
    {ci : ConstantInfo} (hfresh : env.find? ci.name = none)
    (htransparent : Lean.ConstantInfo.ReadinessTransparent ci)
    {venv venv' : VEnv} (hle : venv ≤ venv')
    (self : ProjectionResolutionReady env venv) :
    ProjectionResolutionReady (env.add ci) venv' where
  infer name info hfind hready := by
    have hfindOld : env.find? name = some (.inductInfo info) :=
      Environment.find?_of_add_structural mapWF hfresh htransparent
        (.inl ⟨info, rfl⟩) hfind
    have hreadyOld : env.isProjectionReadyStructure name = true := by
      change (env.add ci).constants.find?' name =
        some (.inductInfo info) at hfind
      change env.constants.find?' name = some (.inductInfo info) at hfindOld
      cases info
      rename_i constant numParams numIndices all ctors numNested isRec
        isUnsafe isReflexive
      cases constant
      rename_i familyName levelParams type
      unfold Kernel.Environment.isProjectionReadyStructure at hready ⊢
      rw [hfind] at hready
      rw [hfindOld]
      cases numIndices with
      | succ n => simp at hready
      | zero =>
        cases ctors with
        | nil => simp at hready
        | cons ctor rest =>
          cases rest with
          | cons next tail => simp at hready
          | nil =>
            change (match (env.add ci).constants.find?' ctor,
                (env.add ci).constants.find?' (mkRecName name) with
              | some (.ctorInfo ctorInfo), some (.recInfo recInfo) =>
                  ctorInfo.induct == name && recInfo.all.contains name
              | _, _ => false) = true at hready
            change (match env.constants.find?' ctor,
                env.constants.find?' (mkRecName name) with
              | some (.ctorInfo ctorInfo), some (.recInfo recInfo) =>
                  ctorInfo.induct == name && recInfo.all.contains name
              | _, _ => false) = true
            generalize hc : (env.add ci).constants.find?' ctor =
              ctorFound at hready
            cases ctorFound with
            | none => simp at hready
            | some ctorFound =>
              cases ctorFound <;> try { simp at hready }
              case ctorInfo ctorInfo =>
                generalize hr : (env.add ci).constants.find?'
                  (mkRecName name) = recFound at hready
                cases recFound with
                | none => simp at hready
                | some recFound =>
                  cases recFound <;> try { simp at hready }
                  case recInfo recInfo =>
                    have hc' : (env.add ci).find? ctor =
                        some (.ctorInfo ctorInfo) := by
                      change (env.add ci).constants.find?' ctor = _
                      exact hc
                    have hr' : (env.add ci).find? (mkRecName name) =
                        some (.recInfo recInfo) := by
                      change (env.add ci).constants.find?' (mkRecName name) = _
                      exact hr
                    have hctor : env.find? ctor = some (.ctorInfo ctorInfo) :=
                      Environment.find?_of_add_structural mapWF hfresh htransparent
                        (.inr (.inl ⟨ctorInfo, rfl⟩)) hc'
                    have hrec : env.find? (mkRecName name) = some (.recInfo recInfo) :=
                      Environment.find?_of_add_structural mapWF hfresh htransparent
                        (.inr (.inr ⟨recInfo, rfl⟩)) hr'
                    change env.constants.find?' ctor =
                      some (.ctorInfo ctorInfo) at hctor
                    change env.constants.find?' (mkRecName name) =
                      some (.recInfo recInfo) at hrec
                    rw [hctor, hrec]
                    simpa only using hready
    obtain ⟨artifact⟩ := self.infer name info hfindOld hreadyOld
    exact ⟨artifact.add mapWF hfresh htransparent hle⟩
  constructorHead name info hfind := by
    have hfindOld : env.find? name = some (.ctorInfo info) :=
      Environment.find?_of_add_structural mapWF hfresh htransparent
        (.inr (.inl ⟨info, rfl⟩)) hfind
    exact (self.constructorHead name info hfindOld).mono hle

/-- Rebuilding a checked view's eta descriptor after monotone transport
changes only proof fields, hence gives the same registered rule. -/
theorem VStructureView.WF.toStructEta_mono_eq
    {view : VStructureView} {env env' : VEnv}
    (self : view.WF env) (hle : env ≤ env')
    (ord : env.Ordered) (ord' : env'.Ordered) :
    self.toStructEta ord = (self.mono hle).toStructEta ord' := by
  rfl

/-- A structure-eta artifact persists across the same pair of extensions.
The registered descriptor is transported by `VEnv.LE.structEtas`; the new
ordered proof only rebuilds proposition-valued fields of the identical rule. -/
def StructureEtaArtifact.add
    {env : Environment} (mapWF : env.constants.WF)
    {ci : ConstantInfo} (hfresh : env.find? ci.name = none)
    (htransparent : Lean.ConstantInfo.ReadinessTransparent ci)
    {venv venv' : VEnv} (hle : venv ≤ venv')
    (ord' : venv'.Ordered)
    (self : StructureEtaArtifact env familyName familyInfo
      constructorName constructorInfo venv) :
    StructureEtaArtifact (env.add ci) familyName familyInfo
      constructorName constructorInfo venv' where
  projection := self.projection.add mapWF hfresh htransparent hle
  constructor_name_eq := self.constructor_name_eq
  constructor_info_eq := self.constructor_info_eq
  large := self.large
  etaOrdered := ord'
  etaRegistered := by
    change venv'.structEtas
      ((self.projection.viewWF.mono hle).toStructEta ord')
    rw [← self.projection.viewWF.toStructEta_mono_eq hle self.etaOrdered ord']
    exact hle.structEtas self.etaRegistered

/-- A structure-eta artifact persists when only the abstract model grows. -/
def StructureEtaArtifact.mono
    {venv venv' : VEnv} (hle : venv ≤ venv') (ord' : venv'.Ordered)
    (self : StructureEtaArtifact env familyName familyInfo
      constructorName constructorInfo venv) :
    StructureEtaArtifact env familyName familyInfo
      constructorName constructorInfo venv' where
  projection := self.projection.mono hle
  constructor_name_eq := self.constructor_name_eq
  constructor_info_eq := self.constructor_info_eq
  large := self.large
  etaOrdered := ord'
  etaRegistered := by
    change venv'.structEtas
      ((self.projection.viewWF.mono hle).toStructEta ord')
    rw [← self.projection.viewWF.toStructEta_mono_eq hle self.etaOrdered ord']
    exact hle.structEtas self.etaRegistered

/-- Retarget a structure-eta artifact together with its projection payload
after re-establishing the selected constructor lookup in a new host
environment. -/
def StructureEtaArtifact.retarget
    (self : StructureEtaArtifact env familyName familyInfo
      constructorName constructorInfo venv)
    {env' : Environment} {venv' : VEnv} (hle : venv ≤ venv')
    (ord' : venv'.Ordered)
    (constructor_find : env'.find? self.projection.view.constructorName =
      some (.ctorInfo self.projection.constructorInfo))
    (recursor_find : env'.find? self.projection.view.recursorName =
      some (.recInfo self.projection.recursorInfo)) :
    StructureEtaArtifact env' familyName familyInfo constructorName
      constructorInfo venv' where
  projection := self.projection.retarget hle constructor_find recursor_find
  constructor_name_eq := self.constructor_name_eq
  constructor_info_eq := self.constructor_info_eq
  large := self.large
  etaOrdered := ord'
  etaRegistered := by
    change venv'.structEtas
      ((self.projection.viewWF.mono hle).toStructEta ord')
    rw [← self.projection.viewWF.toStructEta_mono_eq hle self.etaOrdered ord']
    exact hle.structEtas self.etaRegistered

/-- A structure-eta artifact likewise depends only on the host constant map. -/
def StructureEtaArtifact.of_constants_eq
    {env env' : Environment} (hconstants : env.constants = env'.constants)
    (self : StructureEtaArtifact env familyName familyInfo
      constructorName constructorInfo venv) :
    StructureEtaArtifact env' familyName familyInfo
      constructorName constructorInfo venv where
  projection := self.projection.of_constants_eq hconstants
  constructor_name_eq := self.constructor_name_eq
  constructor_info_eq := self.constructor_info_eq
  large := self.large
  etaOrdered := self.etaOrdered
  etaRegistered := self.etaRegistered

/-- A restored structure-eta artifact persists across a transparent host
insertion and monotone Theory extension. -/
def RestoredStructureEtaArtifact.add
    {env : Environment} (mapWF : env.constants.WF)
    {ci : ConstantInfo} (hfresh : env.find? ci.name = none)
    (htransparent : Lean.ConstantInfo.ReadinessTransparent ci)
    {venv venv' : VEnv} (hle : venv ≤ venv')
    (ord' : venv'.Ordered)
    (self : RestoredStructureEtaArtifact env familyName familyInfo
      constructorName constructorInfo venv) :
    RestoredStructureEtaArtifact (env.add ci) familyName familyInfo
      constructorName constructorInfo venv' where
  projection := self.projection.add mapWF hfresh htransparent hle
  constructor_name_eq := self.constructor_name_eq
  constructor_info_eq := self.constructor_info_eq
  large := self.large
  etaOrdered := ord'
  etaRegistered := by
    change venv'.structEtas
      ((self.projection.parameterLayout.mono hle).toStructEta
        self.projection.codeNaturality self.projection.recEntriesClosed)
    rw [← self.projection.parameterLayout.toStructEta_mono_eq hle
      self.projection.codeNaturality self.projection.recEntriesClosed]
    exact hle.structEtas self.etaRegistered

/-- A restored structure-eta artifact is monotone in the Theory model. -/
def RestoredStructureEtaArtifact.mono
    {venv venv' : VEnv} (hle : venv ≤ venv') (ord' : venv'.Ordered)
    (self : RestoredStructureEtaArtifact env familyName familyInfo
      constructorName constructorInfo venv) :
    RestoredStructureEtaArtifact env familyName familyInfo
      constructorName constructorInfo venv' where
  projection := self.projection.mono hle
  constructor_name_eq := self.constructor_name_eq
  constructor_info_eq := self.constructor_info_eq
  large := self.large
  etaOrdered := ord'
  etaRegistered := by
    change venv'.structEtas
      ((self.projection.parameterLayout.mono hle).toStructEta
        self.projection.codeNaturality self.projection.recEntriesClosed)
    rw [← self.projection.parameterLayout.toStructEta_mono_eq hle
      self.projection.codeNaturality self.projection.recEntriesClosed]
    exact hle.structEtas self.etaRegistered

/-- Retarget a restored eta artifact after replaying its exact constructor
and recursor lookups at a new host endpoint. -/
def RestoredStructureEtaArtifact.retarget
    (self : RestoredStructureEtaArtifact env familyName familyInfo
      constructorName constructorInfo venv)
    {env' : Environment} {venv' : VEnv} (hle : venv ≤ venv')
    (ord' : venv'.Ordered)
    (constructor_find : env'.find? self.projection.view.constructorName =
      some (.ctorInfo self.projection.constructorInfo))
    (recursor_find : env'.find? self.projection.view.recursorName =
      some (.recInfo self.projection.recursorInfo)) :
    RestoredStructureEtaArtifact env' familyName familyInfo constructorName
      constructorInfo venv' where
  projection := self.projection.retarget hle constructor_find recursor_find
  constructor_name_eq := self.constructor_name_eq
  constructor_info_eq := self.constructor_info_eq
  large := self.large
  etaOrdered := ord'
  etaRegistered := by
    change venv'.structEtas
      ((self.projection.parameterLayout.mono hle).toStructEta
        self.projection.codeNaturality self.projection.recEntriesClosed)
    rw [← self.projection.parameterLayout.toStructEta_mono_eq hle
      self.projection.codeNaturality self.projection.recEntriesClosed]
    exact hle.structEtas self.etaRegistered

/-- Restored eta artifacts depend only on the host constant map. -/
def RestoredStructureEtaArtifact.of_constants_eq
    {env env' : Environment} (hconstants : env.constants = env'.constants)
    (self : RestoredStructureEtaArtifact env familyName familyInfo
      constructorName constructorInfo venv) :
    RestoredStructureEtaArtifact env' familyName familyInfo
      constructorName constructorInfo venv where
  projection := self.projection.of_constants_eq hconstants
  constructor_name_eq := self.constructor_name_eq
  constructor_info_eq := self.constructor_info_eq
  large := self.large
  etaOrdered := self.etaOrdered
  etaRegistered := self.etaRegistered

/-- Backend-preserving eta-artifact transport across a transparent host
insertion. -/
theorem StructureEtaArtifactResolution.add
    {env : Environment} (mapWF : env.constants.WF)
    {ci : ConstantInfo} (hfresh : env.find? ci.name = none)
    (htransparent : Lean.ConstantInfo.ReadinessTransparent ci)
    {venv venv' : VEnv} (hle : venv ≤ venv') (ord' : venv'.Ordered)
    (self : StructureEtaArtifactResolution env familyName familyInfo
      constructorName constructorInfo venv) :
    StructureEtaArtifactResolution (env.add ci) familyName familyInfo
      constructorName constructorInfo venv' := by
  cases self with
  | ordinary artifact =>
      exact .ordinary (artifact.add mapWF hfresh htransparent hle ord')
  | restored artifact =>
      exact .restored (artifact.add mapWF hfresh htransparent hle ord')

/-- Backend-preserving eta-artifact transport under Theory growth. -/
theorem StructureEtaArtifactResolution.mono
    {venv venv' : VEnv} (hle : venv ≤ venv') (ord' : venv'.Ordered)
    (self : StructureEtaArtifactResolution env familyName familyInfo
      constructorName constructorInfo venv) :
    StructureEtaArtifactResolution env familyName familyInfo constructorName
      constructorInfo venv' := by
  cases self with
  | ordinary artifact => exact .ordinary (artifact.mono hle ord')
  | restored artifact => exact .restored (artifact.mono hle ord')

/-- Retarget either eta backend when its host observations are preserved. -/
theorem StructureEtaArtifactResolution.retarget_of_preserved
    (self : StructureEtaArtifactResolution env familyName familyInfo
      constructorName constructorInfo venv)
    {env' : Environment} {venv' : VEnv} (hle : venv ≤ venv')
    (ord' : venv'.Ordered)
    (constructorPreserved : ∀ {n constructorInfo},
      env.find? n = some (.ctorInfo constructorInfo) →
        env'.find? n = some (.ctorInfo constructorInfo))
    (recursorPreserved : ∀ {n recursorInfo},
      env.find? n = some (.recInfo recursorInfo) →
        env'.find? n = some (.recInfo recursorInfo)) :
    StructureEtaArtifactResolution env' familyName familyInfo constructorName
      constructorInfo venv' := by
  cases self with
  | ordinary artifact =>
      exact .ordinary <| artifact.retarget hle ord'
        (constructorPreserved artifact.projection.constructor_find)
        (recursorPreserved artifact.projection.recursor_find)
  | restored artifact =>
      exact .restored <| artifact.retarget hle ord'
        (constructorPreserved artifact.projection.constructor_find)
        (recursorPreserved artifact.projection.recursor_find)

/-- Resolution artifacts are invariant under changes outside the host
constant map. -/
theorem StructureEtaArtifactResolution.of_constants_eq
    {env env' : Environment} (hconstants : env.constants = env'.constants)
    (self : StructureEtaArtifactResolution env familyName familyInfo
      constructorName constructorInfo venv) :
    StructureEtaArtifactResolution env' familyName familyInfo constructorName
      constructorInfo venv := by
  cases self with
  | ordinary artifact =>
      exact .ordinary (artifact.of_constants_eq hconstants)
  | restored artifact =>
      exact .restored (artifact.of_constants_eq hconstants)

/-- Structure-eta readiness is invariant under changes to host-environment
fields other than the constant map. -/
theorem StructureEtaReady.of_constants_eq
    {env env' : Environment} (hconstants : env.constants = env'.constants)
    (self : StructureEtaReady env venv) : StructureEtaReady env' venv where
  resolve familyName familyInfo constructorName constructorInfo
      hfamily hconstructor hnonrec := by
    have hfamily' : env.find? familyName = some (.inductInfo familyInfo) := by
      change env'.constants.find?' familyName = _ at hfamily
      change env.constants.find?' familyName = _
      rwa [hconstants]
    have hconstructor' : env.find? constructorName =
        some (.ctorInfo constructorInfo) := by
      change env'.constants.find?' constructorName = _ at hconstructor
      change env.constants.find?' constructorName = _
      rwa [hconstants]
    have hnonrec' :
        env.isStructureEtaReadyConstructor familyName constructorName = true := by
      have hfind (query : Name) : env.find? query = env'.find? query := by
        change env.constants.find?' query = env'.constants.find?' query
        rw [hconstants]
      unfold Kernel.Environment.isStructureEtaReadyConstructor
      unfold Kernel.Environment.isNonRecStructureConstructor
      rw [hfind familyName, hfind constructorName,
        hfind (mkRecName familyName)]
      exact hnonrec
    obtain ⟨artifact⟩ := self.resolve familyName familyInfo constructorName
      constructorInfo hfamily' hconstructor' hnonrec'
    exact ⟨artifact.of_constants_eq hconstants⟩

/-- A structure-eta artifact for an existing family persists across fresh
family-only staging and monotone Theory extension. -/
def StructureEtaArtifact.addInductInfo
    {env : Environment} (mapWF : env.constants.WF)
    (info' : InductiveVal) (hfresh : env.find? info'.name = none)
    {venv venv' : VEnv} (hle : venv ≤ venv') (ord' : venv'.Ordered)
    (self : StructureEtaArtifact env familyName familyInfo
      constructorName constructorInfo venv) :
    StructureEtaArtifact (env.add (.inductInfo info')) familyName familyInfo
      constructorName constructorInfo venv' where
  projection := self.projection.addInductInfo mapWF info' hfresh hle
  constructor_name_eq := self.constructor_name_eq
  constructor_info_eq := self.constructor_info_eq
  large := self.large
  etaOrdered := ord'
  etaRegistered := by
    change venv'.structEtas
      ((self.projection.viewWF.mono hle).toStructEta ord')
    rw [← self.projection.viewWF.toStructEta_mono_eq hle self.etaOrdered
      ord']
    exact hle.structEtas self.etaRegistered

/-- A restored eta artifact also persists through family-only staging. -/
def RestoredStructureEtaArtifact.addInductInfo
    {env : Environment} (mapWF : env.constants.WF)
    (info' : InductiveVal) (hfresh : env.find? info'.name = none)
    {venv venv' : VEnv} (hle : venv ≤ venv') (ord' : venv'.Ordered)
    (self : RestoredStructureEtaArtifact env familyName familyInfo
      constructorName constructorInfo venv) :
    RestoredStructureEtaArtifact (env.add (.inductInfo info')) familyName
      familyInfo constructorName constructorInfo venv' :=
  self.retarget hle ord' (by
    have infoName : (.inductInfo info' : ConstantInfo).name = info'.name := rfl
    rw [Environment.find?_add_eq mapWF (.inductInfo info') hfresh]
    rw [if_neg]
    · exact self.projection.constructor_find
    · intro heq
      have old := self.projection.constructor_find
      have heq' : info'.name = self.projection.view.constructorName :=
        infoName.symm.trans heq
      rw [← heq', hfresh] at old
      contradiction) (by
    have infoName : (.inductInfo info' : ConstantInfo).name = info'.name := rfl
    rw [Environment.find?_add_eq mapWF (.inductInfo info') hfresh]
    rw [if_neg]
    · exact self.projection.recursor_find
    · intro heq
      have old := self.projection.recursor_find
      have heq' : info'.name = self.projection.view.recursorName :=
        infoName.symm.trans heq
      rw [← heq', hfresh] at old
      contradiction)

/-- Backend-preserving eta transport through family-only staging. -/
theorem StructureEtaArtifactResolution.addInductInfo
    {env : Environment} (mapWF : env.constants.WF)
    (info' : InductiveVal) (hfresh : env.find? info'.name = none)
    {venv venv' : VEnv} (hle : venv ≤ venv') (ord' : venv'.Ordered)
    (self : StructureEtaArtifactResolution env familyName familyInfo
      constructorName constructorInfo venv) :
    StructureEtaArtifactResolution (env.add (.inductInfo info')) familyName
      familyInfo constructorName constructorInfo venv' := by
  cases self with
  | ordinary artifact =>
      exact .ordinary
        (artifact.addInductInfo mapWF info' hfresh hle ord')
  | restored artifact =>
      exact .restored
        (artifact.addInductInfo mapWF info' hfresh hle ord')

/-- Structure-eta readiness survives staging one fresh multi-constructor
family.  The inserted family cannot satisfy the host's one-constructor
structure test, and existing artifacts are transported unchanged. -/
theorem StructureEtaReady.addInductInfo
    {env : Environment} (mapWF : env.constants.WF)
    (info' : InductiveVal) (hfresh : env.find? info'.name = none)
    (hctors : info'.ctors.length ≠ 1)
    {venv venv' : VEnv} (hle : venv ≤ venv') (ord' : venv'.Ordered)
    (self : StructureEtaReady env venv) :
    StructureEtaReady (env.add (.inductInfo info')) venv' where
  resolve familyName familyInfo constructorName constructorInfo
      hfamily hconstructor hnonrec := by
    by_cases heq : info'.name = familyName
    · subst familyName
      have hnonrecOld :=
        Kernel.Environment.isStructureEtaReadyConstructor_isNonRec hnonrec
      have hshape :=
        Kernel.Environment.isNonRecStructureConstructor_isNonRecStructure
          hnonrecOld
      rw [Environment.isNonRecStructure_add_inductInfo_self
        mapWF info' hfresh hctors] at hshape
      contradiction
    · have hfamily' : env.find? familyName =
          some (.inductInfo familyInfo) := by
        rw [Environment.find?_add_eq mapWF (.inductInfo info') hfresh]
          at hfamily
        have infoName : (.inductInfo info' : ConstantInfo).name =
            info'.name := rfl
        simpa only [infoName, if_neg heq] using hfamily
      have hconstructor' : env.find? constructorName =
          some (.ctorInfo constructorInfo) := by
        rw [Environment.find?_add_eq mapWF (.inductInfo info') hfresh]
          at hconstructor
        split at hconstructor
        · cases hconstructor
        · exact hconstructor
      have hnonrec' :
          env.isStructureEtaReadyConstructor familyName constructorName = true := by
        rw [← Environment.isStructureEtaReadyConstructor_add_inductInfo
          mapWF info' hfresh heq]
        exact hnonrec
      obtain ⟨artifact⟩ := self.resolve familyName familyInfo
        constructorName constructorInfo hfamily' hconstructor' hnonrec'
      exact ⟨artifact.addInductInfo mapWF info' hfresh hle ord'⟩

/-- Structure-eta readiness survives the same singleton family-only stage.
The newly inserted family cannot activate the runtime structure test because
its sole constructor is absent, while all older artifacts are transported. -/
theorem StructureEtaReady.addInductInfo_of_ctor_absent
    {env : Environment} (mapWF : env.constants.WF)
    (info' : InductiveVal) (hfresh : env.find? info'.name = none)
    (ctor : Name) (hctors : info'.ctors = [ctor])
    (hctor : env.find? ctor = none)
    {venv venv' : VEnv} (hle : venv ≤ venv') (ord' : venv'.Ordered)
    (self : StructureEtaReady env venv) :
    StructureEtaReady (env.add (.inductInfo info')) venv' where
  resolve familyName familyInfo constructorName constructorInfo
      hfamily hconstructor hnonrec := by
    by_cases heq : info'.name = familyName
    · subst familyName
      have selfFind :
          (env.add (.inductInfo info')).find? info'.name =
            some (.inductInfo info') := by
        rw [Environment.find?_add_eq mapWF (.inductInfo info') hfresh]
        have infoName : (.inductInfo info' : ConstantInfo).name =
            info'.name := rfl
        simp only [infoName, if_pos]
      rw [selfFind] at hfamily
      cases hfamily
      have hnonrecOld :=
        Kernel.Environment.isStructureEtaReadyConstructor_isNonRec hnonrec
      have shape := Kernel.Environment.isNonRecStructureConstructor_info
        selfFind hconstructor hnonrecOld
      have constructorMember : constructorName ∈ info'.ctors := by
        rw [shape.2.1]
        simp
      rw [hctors] at constructorMember
      simp only [List.mem_singleton] at constructorMember
      subst constructorName
      rw [Environment.find?_add_eq mapWF (.inductInfo info') hfresh]
        at hconstructor
      split at hconstructor
      · cases hconstructor
      · rw [hctor] at hconstructor
        cases hconstructor
    · have hfamily' : env.find? familyName =
          some (.inductInfo familyInfo) := by
        rw [Environment.find?_add_eq mapWF (.inductInfo info') hfresh]
          at hfamily
        have infoName : (.inductInfo info' : ConstantInfo).name =
            info'.name := rfl
        simpa only [infoName, if_neg heq] using hfamily
      have hconstructor' : env.find? constructorName =
          some (.ctorInfo constructorInfo) := by
        rw [Environment.find?_add_eq mapWF (.inductInfo info') hfresh]
          at hconstructor
        split at hconstructor
        · cases hconstructor
        · exact hconstructor
      have hnonrec' :
          env.isStructureEtaReadyConstructor familyName constructorName = true := by
        rw [← Environment.isStructureEtaReadyConstructor_add_inductInfo
          mapWF info' hfresh heq]
        exact hnonrec
      obtain ⟨artifact⟩ := self.resolve familyName familyInfo
        constructorName constructorInfo hfamily' hconstructor' hnonrec'
      exact ⟨artifact.addInductInfo mapWF info' hfresh hle ord'⟩

/-- Structure-eta readiness is monotone in the abstract model. -/
theorem StructureEtaReady.mono
    {venv venv' : VEnv} (hle : venv ≤ venv') (wf' : venv'.WF)
    (self : StructureEtaReady env venv) : StructureEtaReady env venv' where
  resolve familyName familyInfo constructorName constructorInfo
      hfamily hconstructor hnonrec := by
    obtain ⟨artifact⟩ := self.resolve familyName familyInfo constructorName constructorInfo
      hfamily hconstructor hnonrec
    exact ⟨artifact.mono hle wf'.ordered⟩

/-- Structure-eta readiness survives one transparent host insertion and a
well-formed monotone abstract-model extension. -/
theorem StructureEtaReady.add
    {env : Environment} (mapWF : env.constants.WF)
    {ci : ConstantInfo} (hfresh : env.find? ci.name = none)
    (htransparent : Lean.ConstantInfo.ReadinessTransparent ci)
    {venv venv' : VEnv} (hle : venv ≤ venv') (wf' : venv'.WF)
    (self : StructureEtaReady env venv) :
    StructureEtaReady (env.add ci) venv' where
  resolve familyName familyInfo constructorName constructorInfo
      hfamily hconstructor hnonrec := by
    have hfamilyOld : env.find? familyName = some (.inductInfo familyInfo) :=
      Environment.find?_of_add_structural mapWF hfresh htransparent
        (.inl ⟨familyInfo, rfl⟩) hfamily
    have hconstructorOld : env.find? constructorName =
        some (.ctorInfo constructorInfo) :=
      Environment.find?_of_add_structural mapWF hfresh htransparent
        (.inr (.inl ⟨constructorInfo, rfl⟩)) hconstructor
    have hnonrecOld :
        env.isStructureEtaReadyConstructor familyName constructorName = true := by
      obtain ⟨recInfo, recursorNew, isRec, ctors, indices, owner, large,
        familyRecursor⟩ :=
        Kernel.Environment.isStructureEtaReadyConstructor_info hfamily
          hconstructor hnonrec
      have recursorOld : env.find? (mkRecName familyName) =
          some (.recInfo recInfo) :=
        Environment.find?_of_add_structural mapWF hfresh htransparent
          (.inr (.inr ⟨recInfo, rfl⟩)) recursorNew
      exact Kernel.Environment.isStructureEtaReadyConstructor_of_info
        hfamilyOld hconstructorOld recursorOld isRec ctors indices owner large
          familyRecursor
    obtain ⟨artifact⟩ := self.resolve familyName familyInfo constructorName constructorInfo
      hfamilyOld hconstructorOld hnonrecOld
    exact ⟨artifact.add mapWF hfresh htransparent hle wf'.ordered⟩

/-- The paired form used by all ordinary declaration-extension sites. -/
theorem Readiness.add
    {env : Environment} (mapWF : env.constants.WF)
    {ci : ConstantInfo} (hfresh : env.find? ci.name = none)
    (htransparent : Lean.ConstantInfo.ReadinessTransparent ci)
    {venv venv' : VEnv} (hle : venv ≤ venv') (wf' : venv'.WF)
    (projection : ProjectionResolutionReady env venv)
    (eta : StructureEtaReady env venv) :
    ProjectionResolutionReady (env.add ci) venv' ∧
      StructureEtaReady (env.add ci) venv' :=
  ⟨projection.add mapWF hfresh htransparent hle,
    eta.add mapWF hfresh htransparent hle wf'⟩

/-- Paired readiness is monotone in the abstract model. -/
theorem Readiness.mono
    {env : Environment} {venv venv' : VEnv}
    (hle : venv ≤ venv') (wf' : venv'.WF)
    (projection : ProjectionResolutionReady env venv)
    (eta : StructureEtaReady env venv) :
    ProjectionResolutionReady env venv' ∧ StructureEtaReady env venv' :=
  ⟨projection.mono hle, eta.mono hle wf'⟩

/-- Readiness survives a fresh block of ordinary definitions.  The final
model may already include the constants and their definition equations, so
only its monotone relation to the old model is needed here. -/
theorem Readiness.addDefs
    {env : Environment} {venv venv' : VEnv} {vs : List DefinitionVal}
    (mapWF : env.constants.WF)
    (hfresh : ∀ v ∈ vs, env.find? v.name = none)
    (hnd : (vs.map (·.name)).Nodup)
    (hle : venv ≤ venv') (wf' : venv'.WF)
    (projection : ProjectionResolutionReady env venv)
    (eta : StructureEtaReady env venv) :
    ProjectionResolutionReady
        (vs.foldl (fun e v => e.add (.defnInfo v)) env) venv' ∧
      StructureEtaReady (vs.foldl (fun e v => e.add (.defnInfo v)) env) venv' := by
  induction vs generalizing env venv with
  | nil =>
    simpa using Readiness.mono hle wf' projection eta
  | cons v vs ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    have hvFresh := hfresh v (.head _)
    have hnMap : env.constants.find? v.name = none := by
      rw [← mapWF.find?'_eq_find?]
      exact hvFresh
    have mapWF' : (env.add (.defnInfo v)).constants.WF := by
      change (env.constants.insert v.name (.defnInfo v)).WF
      exact mapWF.insert _ _ hnMap
    have hfresh' : ∀ w ∈ vs,
        (env.add (.defnInfo v)).find? w.name = none := by
      intro w hw
      rw [Environment.find?_add_eq mapWF (.defnInfo v)
        (by simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using hvFresh), if_neg]
      · exact hfresh w (.tail _ hw)
      · intro heq
        simp only [ConstantInfo.name, ConstantInfo.toConstantVal] at heq
        apply hnd.1
        rw [heq]
        exact List.mem_map.2 ⟨w, hw, rfl⟩
    have current := Readiness.add (ci := .defnInfo v) mapWF
      (by simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using hvFresh)
      (by simp [Lean.ConstantInfo.ReadinessTransparent]) hle wf' projection eta
    simpa only [List.foldl_cons] using
      ih mapWF' hfresh' hnd.2 VEnv.LE.rfl current.1 current.2

/-- Closing old recursor payloads over absent names survives a fresh block of
ordinary definitions. -/
theorem Environment.recursorRulesClosed_addDefs :
    ∀ {env : Environment} {vs : List DefinitionVal},
    env.constants.WF →
    (∀ v ∈ vs, env.find? v.name = none) →
    (vs.map (·.name)).Nodup →
    (∀ {name}, env.find? name = none →
      env.RecursorRulesReductionConstFree name) →
    ∀ {name},
      (vs.foldl (fun e v => e.add (.defnInfo v)) env).find? name = none →
      Environment.RecursorRulesReductionConstFree
        (vs.foldl (fun e v => e.add (.defnInfo v)) env) name
  | _, [], _, _, _, self => by simpa using self
  | env, v :: vs, mapWF, hfresh, hnd, self => by
    rw [List.map_cons, List.nodup_cons] at hnd
    have hvFresh := hfresh v (.head _)
    have hvFresh' : env.find? (ConstantInfo.defnInfo v).name = none := by
      simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using hvFresh
    have hnMap : env.constants.find? v.name = none := by
      rw [← mapWF.find?'_eq_find?]
      exact hvFresh
    have mapWF' : (env.add (.defnInfo v)).constants.WF := by
      change (env.constants.insert v.name (.defnInfo v)).WF
      exact mapWF.insert _ _ hnMap
    have hfresh' : ∀ w ∈ vs,
        (env.add (.defnInfo v)).find? w.name = none := by
      intro w hw
      rw [Environment.find?_add_eq mapWF (.defnInfo v) hvFresh', if_neg]
      · exact hfresh w (.tail _ hw)
      · intro heq
        simp only [ConstantInfo.name, ConstantInfo.toConstantVal] at heq
        apply hnd.1
        rw [heq]
        exact List.mem_map.2 ⟨w, hw, rfl⟩
    have current : ∀ {name},
        (env.add (.defnInfo v)).find? name = none →
        (env.add (.defnInfo v)).RecursorRulesReductionConstFree name :=
      Environment.recursorRulesClosed_add mapWF hvFresh'
        (by simp [Lean.ConstantInfo.ReadinessTransparent]) self
    simpa only [List.foldl_cons] using
      Environment.recursorRulesClosed_addDefs mapWF' hfresh' hnd.2 current

end Lean4Lean
