/-
This file is derived from lean4lean and has been modified by Argument Computer Corporation.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/

import Lean4Lean.Theory.Projection
import Lean4Lean.Theory.BlockProjection

namespace Lean4Lean

/-- A projection-capable family is backed either by the historical
single-family generator or by one retained family of a checked mutual block.
The cases stay explicit: in particular, no mutual recursor is re-presented as
a semantically different singleton recursor. -/
inductive VProjectionView where
  | singleton (view : VStructureView)
  | block (view : VBlockStructureView)

namespace VProjectionView

def source : VProjectionView → VInductDecl
  | .singleton view => view.source
  | .block view => view.source

def familyRaw : VProjectionView → VInductiveType
  | .singleton view => view.generation.block.sourceType
  | .block view => view.family.raw

def constructor : VProjectionView → VInductDecl.NormalizedCtor
  | .singleton view => view.constructor
  | .block view => view.constructor

def fieldSorts : VProjectionView → List VLevel
  | .singleton view => view.fieldSorts
  | .block view => view.fieldSorts

def name (view : VProjectionView) : Name := view.familyRaw.name

def constructorName (view : VProjectionView) : Name :=
  view.constructor.raw.name

def recursorName (view : VProjectionView) : Name := .str view.name "rec"

/-- Universe arity of the backend recursor retained by a projection view. -/
def recUvars : VProjectionView → Nat
  | .singleton view => view.generation.recUvars
  | .block view => view.generation.recUvars

/-- Elimination mode of the exact recursor backend retained by the view. -/
def elimination : VProjectionView → VInductDecl.ElimMode
  | .singleton view => view.generation.elimination
  | .block view => view.generation.elimination

def uvars (view : VProjectionView) : Nat := view.source.uvars

/-- A backend recursor with strictly more universe parameters than its source
block is necessarily the large-elimination recursor. -/
theorem elimination_eq_large_of_uvars_lt_recUvars
    (view : VProjectionView) (larger : view.uvars < view.recUvars) :
    view.elimination = .large := by
  cases view with
  | singleton selected =>
      cases mode : selected.generation.elimination with
      | large => simp [elimination, mode]
      | small =>
          simp [uvars, source, recUvars,
            VInductDecl.GenerationChecked.recUvars, mode] at larger
  | block selected =>
      cases mode : selected.generation.elimination with
      | large => simp [elimination, mode]
      | small =>
          simp [uvars, source, recUvars,
            VInductDecl.BlockGenerationChecked.recUvars, mode] at larger

def nparams (view : VProjectionView) : Nat := view.source.nparams

def rawFamilyType (view : VProjectionView) : VExpr := view.familyRaw.type

def resultLevel : VProjectionView → VLevel
  | .singleton selected => selected.generation.block.checked.resultLevel
  | .block selected => selected.resultLevel

/-- Projection-facing family type with the exact raw parameter telescope and
the producer-validated terminal sort. -/
def familyType : VProjectionView → VExpr
  | .singleton selected => selected.familyType
  | .block selected => selected.familyType

def constructorParams (view : VProjectionView) : List VExpr :=
  VExpr.telN view.nparams view.constructor.raw.type

def fields (view : VProjectionView) : List VExpr :=
  view.constructor.rawFields view.nparams

def rawParams : VProjectionView → List VExpr
  | .singleton selected => selected.generation.block.rawParams
  | .block selected => selected.family.rawParams selected.nparams

def rawIndices : VProjectionView → List VExpr
  | .singleton selected => selected.generation.block.rawIndices
  | .block selected => selected.family.rawIndices selected.nparams

def rawResult (view : VProjectionView) : VExpr :=
  match view with
  | .singleton selected => selected.generation.block.rawResult
  | .block selected => selected.family.rawResult selected.nparams

/-- The normalized constructor result reconstructed with the exact family
identity owned by the selected backend. -/
def constructorTarget : VProjectionView → VExpr
  | .singleton selected =>
      selected.constructor.resultTarget selected.generation.block
  | .block selected =>
      VInductDecl.NormalizedBlockCtor.resultTarget selected.generation
        selected.blockConstructor

theorem familyRaw_rawType_eq (view : VProjectionView) :
    view.familyRaw.type =
      VExpr.forallN (view.rawParams ++ view.rawIndices) view.rawResult := by
  cases view with
  | singleton selected =>
      simpa [familyRaw, rawParams, rawIndices, rawResult,
        VExpr.forallN_append] using
        VInductDecl.NormalizedChecked.rawType_eq selected.generation.block
  | block selected =>
      simpa [familyRaw, rawParams, rawIndices, rawResult,
        VExpr.forallN_append] using
        VInductDecl.NormalizedFamily.rawType_eq
          (source := selected.source) selected.family

theorem raw_indices_eq (view : VProjectionView) : view.rawIndices = [] := by
  cases view with
  | singleton selected => exact selected.raw_indices_eq
  | block selected => exact selected.raw_indices_eq

theorem rawFamilyType_eq_forallN (view : VProjectionView) :
    view.rawFamilyType = VExpr.forallN view.rawParams view.rawResult := by
  rw [rawFamilyType, view.familyRaw_rawType_eq, view.raw_indices_eq]
  simp

theorem familyType_eq_forallN (view : VProjectionView) :
    view.familyType =
      VExpr.forallN view.rawParams (.sort view.resultLevel) := by
  cases view <;> rfl

theorem rawParams_length (view : VProjectionView) :
    view.rawParams.length = view.nparams := by
  cases view with
  | singleton selected => exact selected.generation.shape.1
  | block selected => exact selected.raw_params_length

theorem constructorParams_length (view : VProjectionView) :
    view.constructorParams.length = view.nparams := by
  cases view with
  | singleton selected =>
      have hconstructorMem :
          selected.constructor ∈ selected.generation.block.ctorPairs := by
        simp [selected.constructor_eq]
      simpa [constructorParams, constructor, nparams, source] using
        (selected.generation.shape.2.2.2.2.2 selected.constructor
          hconstructorMem).2.2.1
  | block selected =>
      simpa [constructorParams, constructor, nparams, source] using
        ((selected.generation.shape.2.2.2.2 selected.family
          selected.family_mem).2.2.2.2.2.2 selected.constructor
            selected.constructor_mem).2.2.1

/-- Parameter and field binders exhaust the raw constructor telescope. -/
theorem constructorSpine_length (view : VProjectionView) :
    view.nparams + view.fields.length =
      (VInductDecl.ctorFields view.constructor.raw.type).length := by
  have split := VExpr.telN_length_add_ctorFields_dropN_length
    view.nparams view.constructor.raw.type
  change view.constructorParams.length + view.fields.length = _ at split
  rw [view.constructorParams_length] at split
  exact split

/-- The raw constructor telescope is its parameter prefix followed by fields. -/
theorem constructorFields_eq (view : VProjectionView) :
    VInductDecl.ctorFields view.constructor.raw.type =
      view.constructorParams ++ view.fields := by
  simpa [constructorParams, fields,
    VInductDecl.NormalizedCtor.rawFields] using
      VExpr.ctorFields_eq_telN_append view.nparams view.constructor.raw.type

theorem nparams_eq_familyArity (view : VProjectionView) :
    view.nparams = (VInductDecl.ctorFields view.familyType).length := by
  cases view with
  | singleton selected =>
      simpa [nparams, source, familyType, familyRaw] using
        selected.nparams_eq_familyArity
  | block selected =>
      simpa [nparams, source, familyType, familyRaw] using
        selected.nparams_eq_familyArity

theorem nparams_eq_rawFamilyArity (view : VProjectionView) :
    view.nparams =
      (VInductDecl.ctorFields view.rawFamilyType).length := by
  cases view with
  | singleton selected =>
      simpa [nparams, source, rawFamilyType, familyRaw] using
        selected.nparams_eq_rawFamilyArity
  | block selected =>
      simpa [nparams, source, rawFamilyType, familyRaw] using
        selected.nparams_eq_rawFamilyArity

theorem family_uvars_eq (view : VProjectionView) :
    view.familyRaw.uvars = view.uvars := by
  cases view with
  | singleton selected =>
      exact selected.generation.block.sourceType_uvars_eq
  | block selected => exact selected.family_uvars_eq

theorem constructor_uvars_eq (view : VProjectionView) :
    view.constructor.raw.uvars = view.uvars := by
  cases view with
  | singleton selected =>
      simpa [constructor, uvars, source] using
        selected.generation.ctor_uvars_eq
          (ctor := selected.constructor) (by simp [selected.constructor_eq])
  | block selected => exact selected.constructor_uvars_eq

def structureType (view : VProjectionView)
    (levels : List VLevel) (params : List VExpr) : VExpr :=
  VExpr.appN (.const view.name levels) params

@[simp] theorem structureType_liftN (view : VProjectionView)
    (levels : List VLevel) (params : List VExpr) (n k : Nat) :
    (view.structureType levels params).liftN n k =
      view.structureType levels
        (params.map fun param => param.liftN n k) := by
  simp [structureType, VExpr.liftN_appN, VExpr.liftN]

@[simp] theorem structureType_instN (view : VProjectionView)
    (levels : List VLevel) (params : List VExpr) (a : VExpr) (k : Nat) :
    (view.structureType levels params).inst a k =
      view.structureType levels
        (params.map fun param => param.inst a k) := by
  simp [structureType, VExpr.instN_appN, VExpr.inst]

@[simp] theorem structureType_instL (view : VProjectionView)
    (levels : List VLevel) (params : List VExpr) (ls : List VLevel) :
    (view.structureType levels params).instL ls =
      view.structureType (levels.map (VLevel.inst ls))
        (params.map (VExpr.instL ls)) := by
  simp [structureType, VExpr.instL_appN, VExpr.instL]

def specializedFields (view : VProjectionView)
    (levels : List VLevel) (params : List VExpr) : List VExpr :=
  match view with
  | .singleton selected => selected.specializedFields levels params
  | .block selected => selected.specializedFields levels params

@[simp] theorem specializedFields_eq (view : VProjectionView)
    (levels : List VLevel) (params : List VExpr) :
    view.specializedFields levels params =
      view.fields.zipIdx.map fun (field, i) =>
        VExpr.instRevAt (field.instL levels) params i := by
  cases view <;> rfl

def projectionCodes (view : VProjectionView)
    (levels : List VLevel) (params : List VExpr) :
    List VStructureView.ProjectionCode :=
  match view with
  | .singleton selected => selected.projectionCodes levels params
  | .block selected => selected.operationalProjectionCodes levels params

def projectionArgs (view : VProjectionView)
    (levels : List VLevel) (params : List VExpr)
    (count : Nat) (major : VExpr) : List VExpr :=
  (view.projectionCodes levels params).take count |>.map fun code =>
    .app code.projector major

def projectionType? (view : VProjectionView)
    (levels : List VLevel) (params : List VExpr)
    (idx : Nat) (major : VExpr) : Option VExpr := do
  let code ← (view.projectionCodes levels params)[idx]?
  return .app code.typeFn major

def project? (view : VProjectionView)
    (levels : List VLevel) (params : List VExpr)
    (idx : Nat) (major : VExpr) : Option VExpr := do
  let code ← (view.projectionCodes levels params)[idx]?
  return .app code.projector major

def etaRebuild (view : VProjectionView)
    (levels : List VLevel) (params : List VExpr) (major : VExpr) : VExpr :=
  VExpr.appN (.const view.constructorName levels)
    (params ++ view.projectionArgs levels params
      (view.specializedFields levels params).length major)

/-- The backend-specific checked-generation invariant, retained without
erasing which generator owns the recursor and iota rules. -/
inductive CheckedWF : (view : VProjectionView) → VEnv → Prop where
  | singleton (wf : view.WF env) : CheckedWF (.singleton view) env
  | block (wf : view.WF env) : CheckedWF (.block view) env

/-- Backend-specific producer layout, without claiming that all projection
programs are executable. -/
inductive CheckedLayoutWF : (view : VProjectionView) → VEnv → Prop where
  | singleton (wf : view.LayoutWF env) :
      CheckedLayoutWF (.singleton view) env
  | block (wf : view.LayoutWF env) : CheckedLayoutWF (.block view) env

/-- A projection view remains valid in every later environment.  We retain
the environment in which its backend certificate was checked because a
block-generation certificate can only be reconstructed at a later *ordered*
environment.  Lookup and typing consumers can still use the monotone fragment
without imposing that extra premise on every transport. -/
def WF (view : VProjectionView) (env : VEnv) : Prop :=
  ∃ base, base ≤ env ∧ CheckedWF view base

/-- Persistent producer-owned layout for either projection backend. -/
def LayoutWF (view : VProjectionView) (env : VEnv) : Prop :=
  ∃ base, base ≤ env ∧ CheckedLayoutWF view base

theorem CheckedWF.toCheckedLayoutWF
    {view : VProjectionView} {env : VEnv}
    (self : CheckedWF view env) : CheckedLayoutWF view env := by
  cases self with
  | singleton wf => exact .singleton wf.toLayoutWF
  | block wf => exact .block wf.toLayoutWF

theorem WF.toLayoutWF {view : VProjectionView} {env : VEnv}
    (self : view.WF env) : view.LayoutWF env := by
  obtain ⟨base, hbase, checked⟩ := self
  exact ⟨base, hbase, checked.toCheckedLayoutWF⟩

theorem LayoutWF.ofSingleton {view : VStructureView} {env : VEnv}
    (wf : view.LayoutWF env) : LayoutWF (.singleton view) env :=
  ⟨env, VEnv.LE.rfl, .singleton wf⟩

theorem LayoutWF.ofBlock {view : VBlockStructureView} {env : VEnv}
    (wf : view.LayoutWF env) : LayoutWF (.block view) env :=
  ⟨env, VEnv.LE.rfl, .block wf⟩

theorem WF.ofSingleton {view : VStructureView} {env : VEnv}
    (wf : view.WF env) : WF (.singleton view) env :=
  ⟨env, VEnv.LE.rfl, .singleton wf⟩

theorem WF.ofBlock {view : VBlockStructureView} {env : VEnv}
    (wf : view.WF env) : WF (.block view) env :=
  ⟨env, VEnv.LE.rfl, .block wf⟩

theorem WF.mono {view : VProjectionView} {env env' : VEnv}
    (hle : env ≤ env') (self : view.WF env) : view.WF env' := by
  obtain ⟨base, hbase, checked⟩ := self
  exact ⟨base, hbase.trans hle, checked⟩

theorem LayoutWF.mono {view : VProjectionView} {env env' : VEnv}
    (hle : env ≤ env') (self : view.LayoutWF env) :
    view.LayoutWF env' := by
  obtain ⟨base, hbase, checked⟩ := self
  exact ⟨base, hbase.trans hle, checked⟩

theorem WF.materialize {view : VProjectionView} {env : VEnv}
    (self : view.WF env) (henv : env.Ordered) : CheckedWF view env := by
  obtain ⟨base, hbase, checked⟩ := self
  cases checked with
  | singleton wf => exact .singleton (wf.mono hbase)
  | block wf => exact .block (wf.mono hbase henv)

theorem LayoutWF.materialize {view : VProjectionView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.Ordered) :
    CheckedLayoutWF view env := by
  obtain ⟨base, hbase, checked⟩ := self
  cases checked with
  | singleton wf => exact .singleton (wf.mono hbase)
  | block wf => exact .block (wf.mono hbase henv)

theorem LayoutWF.family {view : VProjectionView} {env : VEnv}
    (self : view.LayoutWF env) :
    env.constants view.name = some view.familyRaw.toVConstant := by
  obtain ⟨base, hbase, checked⟩ := self
  cases checked with
  | singleton wf => exact hbase.constants wf.family
  | block wf => exact hbase.constants wf.family

/-- The literal registered family type and the projection-facing validated
sort type are definitionally equal for either backend. -/
theorem LayoutWF.rawFamilyType_defeq_familyType
    {view : VProjectionView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.Ordered) :
    ∃ sortLevel, env.IsDefEq view.uvars []
      view.rawFamilyType view.familyType (.sort sortLevel) := by
  cases self.materialize henv with
  | singleton wf =>
      simpa [rawFamilyType, familyType, familyRaw, uvars, source] using
        wf.rawFamilyType_defeq_familyType
  | block wf =>
      simpa [rawFamilyType, familyType, familyRaw, uvars, source] using
        wf.rawFamilyType_defeq_familyType

/-- Type the registered family constant at the common projection-facing
family type. -/
theorem LayoutWF.familyConst_hasType
    {view : VProjectionView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars) :
    env.HasType U Γ (.const view.name levels)
      (view.familyType.instL levels) := by
  cases self.materialize henv with
  | singleton wf =>
      simpa [name, familyRaw, familyType, uvars, source] using
        wf.familyConst_hasType henv levels hlevels hlevelsLength
  | block wf =>
      simpa [name, familyRaw, familyType, uvars, source] using
        wf.familyConst_hasType henv levels hlevels hlevelsLength

theorem LayoutWF.familyType_closed
    {view : VProjectionView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.Ordered) :
    view.familyType.ClosedN := by
  cases self.materialize henv with
  | singleton wf =>
      simpa [familyType] using wf.familyType_closed henv
  | block wf =>
      simpa [familyType] using wf.familyType_closed henv

theorem LayoutWF.constructor_registered
    {view : VProjectionView} {env : VEnv}
    (self : view.LayoutWF env) :
    env.constants view.constructorName =
      some view.constructor.raw.toVConstant := by
  obtain ⟨base, hbase, checked⟩ := self
  cases checked with
  | singleton wf => exact hbase.constants wf.constructor
  | block wf => exact hbase.constants wf.constructor

/-- The registered backend recursor and its exact universe arity. -/
theorem LayoutWF.recursor_registered
    {view : VProjectionView} {env : VEnv}
    (self : view.LayoutWF env) :
    ∃ recursor : VConstant,
      env.constants view.recursorName = some recursor ∧
        recursor.uvars = view.recUvars := by
  cases view with
  | singleton selected =>
      obtain ⟨base, hbase, checked⟩ := self
      cases checked with
      | singleton wf =>
          exact ⟨selected.generation.recursor,
            hbase.constants wf.recursor, rfl⟩
  | block selected =>
      obtain ⟨base, hbase, checked⟩ := self
      cases checked with
      | block wf =>
          exact ⟨selected.generation.generatedRecursor selected.family,
            hbase.constants wf.recursor, rfl⟩

theorem WF.family {view : VProjectionView} {env : VEnv}
    (self : view.WF env) :
    env.constants view.name = some view.familyRaw.toVConstant := by
  obtain ⟨base, hbase, checked⟩ := self
  cases checked with
  | singleton wf => exact hbase.constants wf.family
  | block wf => exact hbase.constants wf.family

theorem WF.constructor_registered {view : VProjectionView} {env : VEnv}
    (self : view.WF env) :
    env.constants view.constructorName =
      some view.constructor.raw.toVConstant := by
  obtain ⟨base, hbase, checked⟩ := self
  cases checked with
  | singleton wf => exact hbase.constants wf.constructor
  | block wf => exact hbase.constants wf.constructor

/-- Registered projection views at the same family name have the same raw
family type and hence, because both are unindexed, the same parameter
arity. -/
theorem WF.nparams_eq_of_name_eq
    {left right : VProjectionView} {env : VEnv}
    (self : left.WF env) (other : right.WF env)
    (name_eq : left.name = right.name) :
    left.nparams = right.nparams := by
  have familyEq : left.familyRaw.toVConstant =
      right.familyRaw.toVConstant := by
    apply Option.some.inj
    exact self.family.symm.trans <|
      (congrArg env.constants name_eq).trans other.family
  have typeEq : left.rawFamilyType = right.rawFamilyType := by
    simpa [rawFamilyType] using congrArg VConstant.type familyEq
  calc
    left.nparams = (VInductDecl.ctorFields left.rawFamilyType).length :=
      left.nparams_eq_rawFamilyArity
    _ = (VInductDecl.ctorFields right.rawFamilyType).length := by rw [typeEq]
    _ = right.nparams := right.nparams_eq_rawFamilyArity.symm

/-- The same registered-family rigidity at the producer layout layer. -/
theorem LayoutWF.nparams_eq_of_name_eq
    {left right : VProjectionView} {env : VEnv}
    (self : left.LayoutWF env) (other : right.LayoutWF env)
    (name_eq : left.name = right.name) :
    left.nparams = right.nparams := by
  have familyEq : left.familyRaw.toVConstant =
      right.familyRaw.toVConstant := by
    apply Option.some.inj
    exact self.family.symm.trans <|
      (congrArg env.constants name_eq).trans other.family
  have typeEq : left.rawFamilyType = right.rawFamilyType := by
    simpa [rawFamilyType] using congrArg VConstant.type familyEq
  calc
    left.nparams = (VInductDecl.ctorFields left.rawFamilyType).length :=
      left.nparams_eq_rawFamilyArity
    _ = (VInductDecl.ctorFields right.rawFamilyType).length := by rw [typeEq]
    _ = right.nparams := right.nparams_eq_rawFamilyArity.symm

/-- A family parameter spine consumes the exact raw parameter prefix stored
in its selected constructor, independently of which checked generator owns
that constructor. -/
theorem LayoutWF.constructorParamsSpine
    {view : VProjectionView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (target : VExpr) :
    env.SpineWF U Γ
      (VExpr.forallN
        (view.constructorParams.map (VExpr.instL levels))
        target) params (VExpr.instRev target params) := by
  cases self.materialize henv with
  | singleton wf =>
      simpa [constructorParams, constructor, nparams, source, familyType,
        familyRaw, uvars, VStructureView.constructorParams] using
        wf.constructorParamsSpine henv levels hlevels hlevelsLength params
          hparamsLength paramsSpine target
  | block wf =>
      simpa [constructorParams, constructor, nparams, source, familyType,
        familyRaw, uvars, VBlockStructureView.constructorParams] using
        wf.constructorParamsSpine henv levels hlevels hlevelsLength params
          hparamsLength paramsSpine target

abbrev WF.constructorParamsSpine
    {view : VProjectionView} {env : VEnv} (self : view.WF env) :=
  self.toLayoutWF.constructorParamsSpine

/-- Recover a family parameter spine from the corresponding raw constructor
prefix for either checked projection backend. -/
theorem LayoutWF.familyParamsSpine_of_constructor
    {view : VProjectionView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    {target cursor : VExpr}
    (constructorSpine : env.SpineWF U Γ
      (VExpr.forallN
        (view.constructorParams.map (VExpr.instL levels)) target)
      params cursor) :
    env.SpineWF U Γ (view.familyType.instL levels) params
      (.sort (view.resultLevel.inst levels)) := by
  cases self.materialize henv with
  | singleton wf =>
      simpa [constructorParams, constructor, nparams, source, rawResult,
        familyType, familyRaw, resultLevel, uvars,
        VStructureView.constructorParams] using
        wf.familyParamsSpine_of_constructor henv levels hlevels
          hlevelsLength params hparamsLength constructorSpine
  | block wf =>
      simpa [constructorParams, constructor, nparams, source, rawResult,
        familyType, familyRaw, resultLevel, uvars,
        VBlockStructureView.constructorParams] using
        wf.familyParamsSpine_of_constructor henv levels hlevels
          hlevelsLength params hparamsLength constructorSpine

abbrev WF.familyParamsSpine_of_constructor
    {view : VProjectionView} {env : VEnv} (self : view.WF env) :=
  self.toLayoutWF.familyParamsSpine_of_constructor

/-- The raw constructor declaration telescope retained by either producer is
well formed in the current ordered environment. -/
theorem LayoutWF.constructorDeclared_onTel
    {view : VProjectionView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.Ordered) :
    env.OnTel view.uvars []
      (view.constructor.declaredBinders view.nparams) := by
  cases view with
  | singleton selected =>
      cases self.materialize henv with
      | singleton wf =>
          simpa [constructor, nparams, source, uvars] using
            wf.generationSemantics.constructor.declaredTel.raw_onTel
  | block selected =>
      cases self.materialize henv with
      | block wf =>
          simpa [constructor, nparams, source, uvars,
            VBlockStructureView.blockConstructor,
            VInductDecl.NormalizedBlockCtor.declaredBinders] using
            (wf.generationEnv.ctorWF selected.blockConstructor
              selected.blockConstructor_mem).declaredTel.raw_onTel

abbrev WF.constructorDeclared_onTel
    {view : VProjectionView} {env : VEnv} (self : view.WF env) :=
  self.toLayoutWF.constructorDeclared_onTel

/-- Backend-neutral declared-result semantics for the selected raw
constructor.  The result universe is existential because consumers only need
the exact definitional equality, not the backend's internal level name. -/
theorem LayoutWF.constructorDeclaredResult
    {view : VProjectionView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.Ordered) :
    ∃ resultLevel, env.IsDefEq view.uvars
      (view.constructor.declaredBinders view.nparams).reverse
      (view.constructor.rawResult view.nparams)
      view.constructorTarget (.sort resultLevel) := by
  cases view with
  | singleton selected =>
      cases self.materialize henv with
      | singleton wf =>
          refine ⟨selected.generation.block.checked.resultLevel, ?_⟩
          simpa [constructor, nparams, source, uvars, constructorTarget] using
            wf.generationSemantics.constructor.declaredResult
  | block selected =>
      cases self.materialize henv with
      | block wf =>
          refine ⟨selected.generation.validated.resultLevel, ?_⟩
          simpa [constructor, nparams, source, uvars, constructorTarget,
            VBlockStructureView.blockConstructor,
            VInductDecl.NormalizedBlockCtor.declaredBinders,
            VInductDecl.NormalizedBlockCtor.rawResult] using
            (wf.generationEnv.ctorWF selected.blockConstructor
              selected.blockConstructor_mem).declaredResult

abbrev WF.constructorDeclaredResult
    {view : VProjectionView} {env : VEnv} (self : view.WF env) :=
  self.toLayoutWF.constructorDeclaredResult

/-- Applying the selected constructor to a valid family parameter spine
exposes the canonical specialized field telescope and selected family
result. -/
theorem LayoutWF.constructorPrefix_hasType
    {view : VProjectionView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel)) :
    env.HasType U Γ
      (VExpr.appN (.const view.constructorName levels) params)
      (VExpr.forallN (view.specializedFields levels params)
        ((view.structureType levels params).liftN
          (view.specializedFields levels params).length)) := by
  cases self.materialize henv with
  | singleton wf =>
      simpa [constructorName, constructor, specializedFields, structureType,
        name, familyRaw, nparams, source, uvars, familyType,
        VStructureView.constructorName, VStructureView.structureType,
        VExpr.liftN_appN, VExpr.liftN] using
        wf.constructorPrefix_hasType henv levels hlevels hlevelsLength params
          hparamsLength paramsSpine
  | block wf =>
      simpa [constructorName, constructor, specializedFields, structureType,
        name, familyRaw, nparams, source, uvars, familyType,
        VBlockStructureView.constructorName,
        VBlockStructureView.structureType,
        VExpr.liftN_appN, VExpr.liftN] using
        wf.constructorPrefix_hasType henv levels hlevels hlevelsLength params
          hparamsLength paramsSpine

abbrev WF.constructorPrefix_hasType
    {view : VProjectionView} {env : VEnv} (self : view.WF env) :=
  self.toLayoutWF.constructorPrefix_hasType

theorem LayoutWF.specializedFields_onSortTel
    {view : VProjectionView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel)) :
    env.OnSortTel U Γ (view.specializedFields levels params)
      (view.fieldSorts.map (VLevel.inst levels)) := by
  cases self.materialize henv with
  | singleton wf =>
      simpa [specializedFields, fieldSorts, nparams, source, uvars,
        familyType, familyRaw] using
        wf.specializedFields_onSortTel henv levels hlevels hlevelsLength
          params hparamsLength paramsSpine
  | block wf =>
      simpa [specializedFields, fieldSorts, nparams, source, uvars,
        familyType, familyRaw] using
        wf.specializedFields_onSortTel henv levels hlevels hlevelsLength
          params hparamsLength paramsSpine

abbrev WF.specializedFields_onSortTel
    {view : VProjectionView} {env : VEnv} (self : view.WF env) :=
  self.toLayoutWF.specializedFields_onSortTel

/-- The reconstructed normalized constructor target specializes to the
selected family application when instantiated by an exact parameter/field
split. -/
theorem LayoutWF.constructorTarget_instRev
    {view : VProjectionView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.Ordered)
    (levels : List VLevel) (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (runtimeFields : List VExpr)
    (hfieldsLength : runtimeFields.length = view.fields.length) :
    (view.constructorTarget.instL levels).instRev
        (params ++ runtimeFields) =
      view.structureType levels params := by
  cases view with
  | singleton selected =>
      have hlevelsLength' : levels.length = selected.uvars := by
        simpa [uvars, source] using hlevelsLength
      have hparamsLength' : params.length = selected.nparams := by
        simpa [nparams, source] using hparamsLength
      have hfieldsLength' : runtimeFields.length = selected.fields.length := by
        simpa [fields, constructor, nparams, source,
          VStructureView.fields] using hfieldsLength
      cases self.materialize henv with
      | singleton wf =>
          let S := wf.toGenerationEnv henv
          have hconstructorMem :
              selected.constructor ∈ selected.generation.block.ctorPairs := by
            simp [selected.constructor_eq]
          have hresultIndices :
              selected.constructor.view.resultIndices = [] := by
            apply List.length_eq_zero_iff.1
            rw [S.viewResultIndices_length hconstructorMem]
            simp [selected.checked_indices_eq]
          have hargsLength : (params ++ runtimeFields).length =
              selected.nparams + selected.fields.length := by
            simp [hparamsLength', hfieldsLength']
          have hrange := VExpr.map_instRev_bvarRevRange_seg
            (params ++ runtimeFields) selected.nparams selected.fields.length
            (by rw [hargsLength]; omega)
          have hrange' :
              (VExpr.bvarRevRange selected.fields.length
                selected.nparams).map
                  (VExpr.instRev · (params ++ runtimeFields)) = params := by
            simpa [hargsLength, hparamsLength'] using hrange
          change
            ((selected.constructor.resultTarget selected.generation.block).instL
              levels).instRev (params ++ runtimeFields) =
              selected.structureType levels params
          simp only [VInductDecl.NormalizedCtor.resultTarget,
            VExpr.instL_appN, VExpr.instL, VExpr.instRev_appN,
            VExpr.bvarRevRange_map_instL, hresultIndices, List.append_nil]
          rw [VLevel.inst_map_id hlevelsLength']
          rw [VExpr.instRev_closedN (params ++ runtimeFields) (by trivial)]
          change
            (VExpr.const selected.name levels).appN
                ((VExpr.bvarRevRange selected.fields.length
                  selected.nparams).map
                    (VExpr.instRev · (params ++ runtimeFields))) =
              selected.structureType levels params
          rw [hrange']
          rfl
  | block selected =>
      have hlevelsLength' : levels.length = selected.uvars := by
        simpa [uvars, source] using hlevelsLength
      have hparamsLength' : params.length = selected.nparams := by
        simpa [nparams, source] using hparamsLength
      have hfieldsLength' : runtimeFields.length = selected.fields.length := by
        simpa [fields, constructor, nparams, source,
          VBlockStructureView.fields] using hfieldsLength
      cases self.materialize henv with
      | block wf =>
          have hresultIndices :
              selected.constructor.view.resultIndices = [] := by
            apply List.length_eq_zero_iff.1
            have hlength : selected.constructor.view.resultIndices.length =
                selected.family.view.indices.length := by
              simpa [VBlockStructureView.blockConstructor] using
                wf.generationEnv.viewResultIndices_length
                  selected.blockConstructor_mem
            rw [hlength, selected.checked_indices_eq]
            rfl
          have hargsLength : (params ++ runtimeFields).length =
              selected.nparams + selected.fields.length := by
            simp [hparamsLength', hfieldsLength']
          have hrange := VExpr.map_instRev_bvarRevRange_seg
            (params ++ runtimeFields) selected.nparams selected.fields.length
            (by rw [hargsLength]; omega)
          have hrange' :
              (VExpr.bvarRevRange selected.fields.length
                selected.nparams).map
                  (VExpr.instRev · (params ++ runtimeFields)) = params := by
            simpa [hargsLength, hparamsLength'] using hrange
          change
            ((VInductDecl.NormalizedBlockCtor.resultTarget
              selected.generation selected.blockConstructor).instL
                levels).instRev (params ++ runtimeFields) =
              selected.structureType levels params
          rw [VInductDecl.NormalizedBlockCtor.resultTarget,
            VExpr.instL_appN, VExpr.instRev_appN]
          dsimp only [VBlockStructureView.blockConstructor]
          simp only [List.map_append, hresultIndices, List.map_nil,
            List.append_nil, List.map_map, Function.comp_def,
            VExpr.bvarRevRange_map_instL]
          simp only [VExpr.instL]
          rw [VLevel.inst_map_id hlevelsLength']
          rw [VExpr.instRev_closedN (params ++ runtimeFields) (by trivial)]
          change
            (VExpr.const selected.name levels).appN
                ((VExpr.bvarRevRange selected.fields.length
                  selected.nparams).map
                    (VExpr.instRev · (params ++ runtimeFields))) =
              selected.structureType levels params
          rw [hrange']
          rfl

abbrev WF.constructorTarget_instRev
    {view : VProjectionView} {env : VEnv} (self : view.WF env) :=
  self.toLayoutWF.constructorTarget_instRev

/-- Uniform projector-program typing contract over the two honest backends. -/
def ProgramsWF (view : VProjectionView) (env : VEnv) : Prop :=
  ∀ {U : Nat} {Γ : List VExpr} {levels : List VLevel}
      {params : List VExpr} {idx : Nat}
      {code : VStructureView.ProjectionCode},
    OnCtx Γ (env.IsType U) →
    (∀ level ∈ levels, level.WF U) →
    levels.length = view.uvars →
    params.length = view.nparams →
    (∃ resultLevel, env.SpineWF U Γ (view.familyType.instL levels)
      params (.sort resultLevel)) →
    (view.projectionCodes levels params)[idx]? = some code →
    env.HasType U Γ code.projector
      (.forallE (view.structureType levels params)
        (.app code.typeFn.lift (.bvar 0)))

/-- Uniform rule-independent reconstruction contract. -/
def RebuildWF (view : VProjectionView) (env : VEnv) : Prop :=
  ∀ {U : Nat} {Γ : List VExpr} {levels : List VLevel}
      {params : List VExpr} {major : VExpr},
    OnCtx Γ (env.IsType U) →
    (∀ level ∈ levels, level.WF U) →
    levels.length = view.uvars →
    params.length = view.nparams →
    (∃ resultLevel, env.SpineWF U Γ (view.familyType.instL levels)
      params (.sort resultLevel)) →
    env.HasType U Γ major (view.structureType levels params) →
    env.HasType U Γ (view.etaRebuild levels params major)
      (view.structureType levels params)

/-- Producer layout plus a dense projector family is sufficient for the
rule-independent reconstruction contract; no stronger small-field witness is
needed at this consumer boundary. -/
theorem LayoutWF.toRebuildWF_of_programs
    {view : VProjectionView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.ConversionRegular)
    (programs : view.ProgramsWF env) : view.RebuildWF env := by
  have checked := self.materialize henv.ordered
  cases view with
  | singleton selected =>
      cases checked with
      | singleton wf =>
          intro U Γ levels params major hΓ hlevels hlevelsLength
            hparamsLength hparamsSpine hmajor
          have selectedPrograms : selected.ProgramsWF env := by
            change selected.ProgramsWF env at programs
            exact programs
          change env.HasType U Γ
            (selected.etaRebuild levels params major)
            (selected.structureType levels params)
          exact selectedPrograms.etaRebuild_hasType_of_constructorPrefix henv
            hΓ hlevels hlevelsLength hparamsLength hparamsSpine hmajor
            (wf.constructorPrefix_hasType henv.ordered levels hlevels
              hlevelsLength params hparamsLength hparamsSpine)
  | block selected =>
      cases checked with
      | block wf =>
          intro U Γ levels params major hΓ hlevels hlevelsLength
            hparamsLength hparamsSpine hmajor
          have selectedPrograms : selected.OperationalProgramsWF env := by
            change selected.OperationalProgramsWF env at programs
            exact programs
          have hconstructorPrefix :=
            wf.constructorPrefix_hasType henv.ordered levels hlevels
              hlevelsLength params hparamsLength hparamsSpine
          change env.HasType U Γ
            (selected.operationalEtaRebuild levels params major)
            (selected.structureType levels params)
          exact selectedPrograms.operationalEtaRebuild_hasType_of_constructorPrefix
            henv hΓ hlevels hlevelsLength hparamsLength hparamsSpine hmajor
              hconstructorPrefix

theorem WF.toProgramsWF {view : VProjectionView} {env : VEnv}
    (self : view.WF env) (henv : env.ConversionRegular) :
    view.ProgramsWF env := by
  have checked := self.materialize henv.ordered
  cases checked with
  | singleton wf =>
      intro U Γ levels params idx code hΓ hlevels hlevelsLength
        hparamsLength hparamsSpine hcode
      exact wf.toProgramsWF henv hΓ hlevels hlevelsLength hparamsLength
        hparamsSpine hcode
  | block wf =>
      intro U Γ levels params idx code hΓ hlevels hlevelsLength
        hparamsLength hparamsSpine hcode
      exact wf.toOperationalProgramsWF henv hΓ hlevels hlevelsLength
        hparamsLength hparamsSpine hcode

/-- A producer layout backed by a large recursor determines every projector
program without any small-field or prelude assumption.  The block backend
uses its prelude-free operational programs; the singleton backend's
small-elimination side condition is vacuous in this branch. -/
theorem LayoutWF.toProgramsWF_of_large
    {view : VProjectionView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.ConversionRegular)
    (large : view.elimination = .large) :
    view.ProgramsWF env := by
  have checked := self.materialize henv.ordered
  cases view with
  | singleton selected =>
      cases checked with
      | singleton layout =>
          have selectedLarge : selected.generation.elimination = .large :=
            large
          let wf : selected.WF env := {
            toLayoutWF := layout
            smallFields := by
              intro small
              rw [selectedLarge] at small
              contradiction }
          change selected.ProgramsWF env
          exact wf.toProgramsWF henv
  | block selected =>
      cases checked with
      | block layout =>
          have selectedLarge : selected.generation.elimination = .large :=
            large
          change selected.OperationalProgramsWF env
          apply layout.operationalProgramsWF_of_admissible henv
          intro levels params idx code hcode
          exact selected.motiveLevel_projectionLevels_of_large
            selectedLarge code.fieldSort levels

theorem WF.toRebuildWF {view : VProjectionView} {env : VEnv}
    (self : view.WF env) (henv : env.ConversionRegular) :
    view.RebuildWF env := by
  have checked := self.materialize henv.ordered
  cases view with
  | singleton selected =>
      cases checked with
      | singleton wf =>
          intro U Γ levels params major hΓ hlevels hlevelsLength
            hparamsLength hparamsSpine hmajor
          exact wf.toRebuildWF henv hΓ hlevels hlevelsLength hparamsLength
            hparamsSpine hmajor
  | block selected =>
      cases checked with
      | block wf =>
          intro U Γ levels params major hΓ hlevels hlevelsLength
            hparamsLength hparamsSpine hmajor
          have programs : selected.OperationalProgramsWF env :=
            wf.toOperationalProgramsWF henv
          have hconstructorPrefix :=
            wf.constructorPrefix_hasType henv.ordered levels hlevels
              hlevelsLength params hparamsLength hparamsSpine
          change env.HasType U Γ
            (selected.operationalEtaRebuild levels params major)
            (selected.structureType levels params)
          exact
            programs.operationalEtaRebuild_hasType_of_constructorPrefix henv
              hΓ hlevels hlevelsLength hparamsLength hparamsSpine hmajor
              hconstructorPrefix

@[simp] theorem projectionCodes_length (view : VProjectionView)
    (levels : List VLevel) (params : List VExpr) :
    (view.projectionCodes levels params).length =
      (view.specializedFields levels params).length := by
  cases view <;> simp [projectionCodes, specializedFields]

@[simp] theorem specializedFields_length (view : VProjectionView)
    (levels : List VLevel) (params : List VExpr) :
    (view.specializedFields levels params).length = view.fields.length := by
  cases view with
  | singleton selected =>
      change (selected.specializedFields levels params).length =
        selected.fields.length
      simp [VStructureView.specializedFields, VStructureView.fields]
  | block selected =>
      change (selected.specializedFields levels params).length =
        selected.fields.length
      simp [VBlockStructureView.specializedFields, VBlockStructureView.fields]

theorem projectionArgs_length (view : VProjectionView)
    (levels : List VLevel) (params : List VExpr)
    (count : Nat) (major : VExpr)
    (hcount : count ≤ (view.projectionCodes levels params).length) :
    (view.projectionArgs levels params count major).length = count := by
  unfold projectionArgs
  rw [List.length_map, List.length_take, Nat.min_eq_left hcount]

theorem projectionArgs_succ (view : VProjectionView)
    (levels : List VLevel) (params : List VExpr) (count : Nat)
    (major : VExpr) {code : VStructureView.ProjectionCode}
    (hcode : (view.projectionCodes levels params)[count]? = some code) :
    view.projectionArgs levels params (count + 1) major =
      view.projectionArgs levels params count major ++
        [.app code.projector major] := by
  simp only [projectionArgs, List.take_add_one, hcode, Option.toList_some,
    List.map_append, List.map_singleton]

@[simp] theorem projectionCodes_instL (view : VProjectionView)
    (levels : List VLevel) (params : List VExpr) (ls : List VLevel) :
    (view.projectionCodes levels params).map
        (fun code => code.instL ls) =
      view.projectionCodes (levels.map (VLevel.inst ls))
        (params.map (VExpr.instL ls)) := by
  cases view <;> simp [projectionCodes]

theorem LayoutWF.projectionCodes_liftN
    {view : VProjectionView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.Ordered)
    (levels : List VLevel) (params : List VExpr)
    (hparams : params.length = view.nparams) (n k : Nat) :
    (view.projectionCodes levels params).map
        (fun code => code.liftN n k) =
      view.projectionCodes levels
        (params.map fun param => param.liftN n k) := by
  cases self.materialize henv with
  | singleton wf =>
      simpa [projectionCodes, nparams, source] using
        wf.projectionCodes_liftN henv levels params hparams n k
  | block wf =>
      simpa [projectionCodes, nparams, source] using
        wf.operationalProjectionCodes_liftN levels params hparams n k

theorem LayoutWF.projectionCodes_instN
    {view : VProjectionView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.Ordered)
    (levels : List VLevel) (params : List VExpr)
    (hparams : params.length = view.nparams) (a : VExpr) (k : Nat) :
    (view.projectionCodes levels params).map
        (fun code => code.instN a k) =
      view.projectionCodes levels
        (params.map fun param => param.inst a k) := by
  cases self.materialize henv with
  | singleton wf =>
      simpa [projectionCodes, nparams, source] using
        wf.projectionCodes_instN henv levels params hparams a k
  | block wf =>
      simpa [projectionCodes, nparams, source] using
        wf.operationalProjectionCodes_instN levels params hparams a k

abbrev WF.projectionCodes_liftN
    {view : VProjectionView} {env : VEnv} (self : view.WF env) :=
  self.toLayoutWF.projectionCodes_liftN

abbrev WF.projectionCodes_instN
    {view : VProjectionView} {env : VEnv} (self : view.WF env) :=
  self.toLayoutWF.projectionCodes_instN

/-- The lower-layer structure-eta descriptor shared by both projection
backends.  Its data fields depend only on the explicit sum view; the retained
well-formedness witness supplies the naturality proofs. -/
def LayoutWF.toStructEta {view : VProjectionView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.Ordered) : VStructEta where
  uvars := view.uvars
  nparams := view.nparams
  nfields := view.fields.length
  familyName := view.name
  familyType := view.familyType
  constructorName := view.constructorName
  projectors := fun levels params =>
    (view.projectionCodes levels params).map (·.projector)
  projectors_length := by
    intro levels params _ _
    simp
  projectors_liftN := by
    intro levels params n k hparams
    have h := self.projectionCodes_liftN henv levels params hparams n k
    simpa [List.map_map, VStructureView.ProjectionCode.liftN,
      Function.comp_def] using
      congrArg (List.map (·.projector)) h

  projectors_instN := by
    intro levels params a k hparams
    have h := self.projectionCodes_instN henv levels params hparams a k
    simpa [List.map_map, VStructureView.ProjectionCode.instN,
      Function.comp_def] using
      congrArg (List.map (·.projector)) h
  projectors_instL := by
    intro levels params ls
    have h := projectionCodes_instL view levels params ls
    simpa [List.map_map, VStructureView.ProjectionCode.instL,
      Function.comp_def] using
      congrArg (List.map (·.projector)) h

abbrev WF.toStructEta {view : VProjectionView} {env : VEnv}
    (self : view.WF env) := self.toLayoutWF.toStructEta

/-- Monotone transport changes only proof fields of the generic eta
descriptor. -/
theorem LayoutWF.toStructEta_mono_eq
    {view : VProjectionView} {env env' : VEnv}
    (self : view.LayoutWF env) (hle : env ≤ env')
    (ord : env.Ordered) (ord' : env'.Ordered) :
    self.toStructEta ord = (self.mono hle).toStructEta ord' := by
  rfl

theorem WF.toStructEta_mono_eq
    {view : VProjectionView} {env env' : VEnv}
    (self : view.WF env) (hle : env ≤ env')
    (ord : env.Ordered) (ord' : env'.Ordered) :
    self.toStructEta ord = (self.mono hle).toStructEta ord' := by
  rfl

@[simp] theorem LayoutWF.toStructEta_structureType
    {view : VProjectionView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.Ordered)
    (levels : List VLevel) (params : List VExpr) :
    (self.toStructEta henv).structureType levels params =
      view.structureType levels params := rfl

@[simp] theorem LayoutWF.toStructEta_rebuild
    {view : VProjectionView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.Ordered)
    (levels : List VLevel) (params : List VExpr) (major : VExpr) :
    (self.toStructEta henv).rebuild levels params major =
      view.etaRebuild levels params major := by
  simp only [VStructEta.rebuild, VStructEta.projectionArgs,
    LayoutWF.toStructEta, etaRebuild, projectionArgs]
  rw [← view.projectionCodes_length levels params, List.take_length]
  simp [List.map_map, Function.comp_def]

abbrev WF.toStructEta_structureType
    {view : VProjectionView} {env : VEnv} (self : view.WF env) :=
  self.toLayoutWF.toStructEta_structureType

abbrev WF.toStructEta_rebuild
    {view : VProjectionView} {env : VEnv} (self : view.WF env) :=
  self.toLayoutWF.toStructEta_rebuild

/-- A persistent reconstruction family is precisely the semantic payload of
the generic registered eta descriptor. -/
theorem LayoutWF.toStructEtaWF_of_rebuilds
    {view : VProjectionView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.Ordered)
    (rebuilds : ∀ {env' : VEnv}, env ≤ env' →
      env'.ConversionRegular → view.RebuildWF env') :
    (self.toStructEta henv).WF env where
  familyType_closed := by
    change view.familyType.ClosedN
    exact self.familyType_closed henv
  rebuild_hasType := by
    intro env' hle hregular U Γ levels params major hΓ hlevels hlevelsLength
      hparamsLength hparamsSpine hmajor
    simpa using rebuilds hle hregular hΓ hlevels hlevelsLength
      hparamsLength hparamsSpine hmajor

theorem WF.toStructEtaWF
    {view : VProjectionView} {env : VEnv}
    (self : view.WF env) (henv : env.WF) :
    (self.toStructEta henv.ordered).WF env :=
  self.toLayoutWF.toStructEtaWF_of_rebuilds henv.ordered fun hle hregular =>
    (self.mono hle).toRebuildWF hregular

theorem ProgramsWF.projector_hasType_field
    {view : VProjectionView} {env : VEnv}
    (self : view.ProgramsWF env) (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} {levels : List VLevel}
    {params : List VExpr} {idx : Nat}
    {code : VStructureView.ProjectionCode}
    (hΓ : OnCtx Γ (env.IsType U))
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (hcode : (view.projectionCodes levels params)[idx]? = some code)
    {major : VExpr}
    (hmajor : env.HasType U Γ major (view.structureType levels params)) :
    ∃ field typeBody,
      (view.specializedFields levels params)[idx]? = some field ∧
      code.typeFn = .lam (view.structureType levels params) typeBody ∧
      env.HasType U Γ (.app code.projector major)
        (field.instRevAt (view.projectionArgs levels params idx major) 0) := by
  cases view with
  | singleton selected =>
      have programs : selected.ProgramsWF env := by
        exact self
      exact programs.projector_hasType_field henv hΓ hlevels hlevelsLength
        hparamsLength hparamsSpine hcode hmajor
  | block selected =>
      have programs : selected.OperationalProgramsWF env := by
        exact self
      exact VBlockStructureView.operationalProjector_hasType_field_of_type
        henv hΓ hcode
        (programs hΓ hlevels hlevelsLength hparamsLength hparamsSpine hcode)
        hmajor

/-- All generated projections form the dependent selected-constructor field
spine, with the backend kept explicit only inside this dispatch. -/
theorem ProgramsWF.projectionArgsSpine
    {view : VProjectionView} {env : VEnv}
    (self : view.ProgramsWF env) (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} {levels : List VLevel}
    {params : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U))
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    {major : VExpr}
    (hmajor : env.HasType U Γ major (view.structureType levels params))
    (tailResult : VExpr) :
    env.SpineWF U Γ
      (VExpr.forallN (view.specializedFields levels params) tailResult)
      (view.projectionArgs levels params
        (view.specializedFields levels params).length major)
      (VExpr.instRev tailResult
        (view.projectionArgs levels params
          (view.specializedFields levels params).length major)) := by
  cases view with
  | singleton selected =>
      have programs : selected.ProgramsWF env := self
      simpa [specializedFields, projectionArgs, projectionCodes, nparams,
        source, uvars, familyType, familyRaw, structureType, name,
        VStructureView.projectionArgs] using
        programs.projectionArgsSpine henv hΓ hlevels hlevelsLength
          hparamsLength hparamsSpine hmajor tailResult
  | block selected =>
      have programs : selected.OperationalProgramsWF env := self
      simpa [specializedFields, projectionArgs, projectionCodes, nparams,
        source, uvars, familyType, familyRaw, structureType, name,
        VBlockStructureView.operationalProjectionArgs] using
        programs.operationalProjectionArgsSpine henv hΓ hlevels hlevelsLength
          hparamsLength hparamsSpine hmajor tailResult

/-- Environment-indexed semantics for either honest projection backend. -/
structure TrProj (env : VEnv) (U : Nat) (Γ : List VExpr)
    (view : VProjectionView) (levels : List VLevel) (params : List VExpr)
    (idx : Nat) (major result : VExpr) : Prop where
  viewWF : view.LayoutWF env
  levelsWF : ∀ level ∈ levels, level.WF U
  levels_length : levels.length = view.uvars
  params_length : params.length = view.nparams
  paramsSpine : ∃ resultLevel,
    env.SpineWF U Γ (view.familyType.instL levels)
      params (.sort resultLevel)
  majorType : env.HasType U Γ major (view.structureType levels params)
  program : ∃ code : VStructureView.ProjectionCode,
    (view.projectionCodes levels params)[idx]? = some code ∧
      result = .app code.projector major ∧
      env.HasType U Γ code.projector
        (.forallE (view.structureType levels params)
          (.app code.typeFn.lift (.bvar 0)))

theorem TrProj.project_eq
    (self : TrProj env U Γ view levels params idx major result) :
    view.project? levels params idx major = some result := by
  obtain ⟨code, hcode, rfl, -⟩ := self.program
  simp [project?, hcode]

theorem TrProj.type_eq
    (self : TrProj env U Γ view levels params idx major result) :
    ∃ code : VStructureView.ProjectionCode,
      view.projectionType? levels params idx major =
        some (VExpr.app code.typeFn major) := by
  obtain ⟨code, hcode, _, -⟩ := self.program
  exact ⟨code, by simp [projectionType?, hcode]⟩

theorem TrProj.result_eq
    (self : TrProj env U Γ view levels params idx major result)
    (other : TrProj env U Γ view levels params idx major result') :
    result = result' :=
  Option.some.inj (self.project_eq.symm.trans other.project_eq)

theorem TrProj.mono {env env' : VEnv} (henv : env ≤ env')
    (self : TrProj env U Γ view levels params idx major result) :
    TrProj env' U Γ view levels params idx major result where
  viewWF := self.viewWF.mono henv
  levelsWF := self.levelsWF
  levels_length := self.levels_length
  params_length := self.params_length
  paramsSpine := self.paramsSpine.imp fun _ h => h.mono henv
  majorType := self.majorType.mono henv
  program := self.program.imp fun _ ⟨hcode, hresult, htype⟩ =>
    ⟨hcode, hresult, htype.mono henv⟩

theorem TrProj.weakN (henv : env.Ordered)
    (W : Ctx.LiftN n k Γ Γ')
    (self : TrProj env U Γ view levels params idx major result) :
    TrProj env U Γ' view levels
      (params.map fun param => param.liftN n k) idx
      (major.liftN n k) (result.liftN n k) := by
  refine {
    viewWF := self.viewWF
    levelsWF := self.levelsWF
    levels_length := self.levels_length
    params_length := by simpa using self.params_length
    paramsSpine := ?_
    majorType := by simpa using self.majorType.weakN henv W
    program := ?_ }
  · have hfamilyClosed : (view.familyType.instL levels).ClosedN 0 := by
      simpa using (self.viewWF.familyType_closed henv).instL
    obtain ⟨resultLevel, hspine⟩ := self.paramsSpine
    refine ⟨resultLevel, ?_⟩
    have hspine' := hspine.weakN henv W
    rw [hfamilyClosed.liftN_eq (Nat.zero_le _)] at hspine'
    simpa [VExpr.liftN] using hspine'
  · obtain ⟨code, hcode, rfl, htype⟩ := self.program
    refine ⟨code.liftN n k, ?_, rfl, ?_⟩
    rw [← self.viewWF.projectionCodes_liftN henv levels params
      self.params_length n k]
    simp only [List.getElem?_map, hcode, Option.map_some]
    simpa [VStructureView.ProjectionCode.liftN, VExpr.liftN,
      VExpr.liftN_lift_projection] using htype.weakN henv W

theorem TrProj.weak' (henv : env.Ordered)
    (W : Ctx.Lift' l Γ Γ')
    (self : TrProj env U Γ view levels params idx major result) :
    TrProj env U Γ' view levels
      (params.map fun param => param.lift' l) idx
      (major.lift' l) (result.lift' l) := by
  generalize hdepth : l.depth = depth
  induction depth generalizing l Γ' with
  | zero =>
      have hctx := W.depth_zero hdepth
      subst Γ'
      simpa [VExpr.lift'_depth_zero (l := l) hdepth] using self
  | succ depth ih =>
      obtain ⟨tail, k, rfl, rfl⟩ := Lift.depth_succ hdepth
      obtain ⟨Γ₁, W₁, W₂⟩ := W.of_cons_skip
      have h := (ih W₁ Lift.depth_consN).weakN henv W₂
      rw [Lift.consN_skip_eq]
      have hlift : ∀ e : VExpr,
          e.lift' ((tail.consN k).comp
              (Lift.refl.skip.consN k)) =
            (e.lift' (tail.consN k)).liftN 1 k := by
        intro e
        rw [VExpr.lift'_comp, ← Lift.skipN_one,
          VExpr.lift'_consN_skipN]
      have hparams :
          params.map (fun param => param.lift' ((tail.consN k).comp
              (Lift.refl.skip.consN k))) =
            (params.map fun param => param.lift' (tail.consN k)).map
              (fun param => param.liftN 1 k) := by
        rw [List.map_map]
        exact List.map_congr_left fun param _ => hlift param
      rw [hparams, hlift major, hlift result]
      exact h

theorem TrProj.instN (henv : env.Ordered)
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ)
    (h₀ : env.HasType U Γ₀ e₀ A₀)
    (self : TrProj env U Γ₁ view levels params idx major result) :
    TrProj env U Γ view levels
      (params.map fun param => param.inst e₀ k) idx
      (major.inst e₀ k) (result.inst e₀ k) := by
  refine {
    viewWF := self.viewWF
    levelsWF := self.levelsWF
    levels_length := self.levels_length
    params_length := by simpa using self.params_length
    paramsSpine := ?_
    majorType := by simpa using self.majorType.instN henv W h₀
    program := ?_ }
  · have hfamilyClosed : (view.familyType.instL levels).ClosedN 0 := by
      simpa using (self.viewWF.familyType_closed henv).instL
    obtain ⟨resultLevel, hspine⟩ := self.paramsSpine
    refine ⟨resultLevel, ?_⟩
    have hspine' := hspine.instNProjection henv W h₀
    rw [hfamilyClosed.instN_eq (Nat.zero_le _)] at hspine'
    simpa [VExpr.inst] using hspine'
  · obtain ⟨code, hcode, rfl, htype⟩ := self.program
    refine ⟨code.instN e₀ k, ?_, rfl, ?_⟩
    rw [← self.viewWF.projectionCodes_instN henv levels params
      self.params_length e₀ k]
    simp only [List.getElem?_map, hcode, Option.map_some]
    simpa [VStructureView.ProjectionCode.instN, VExpr.inst,
      ← VExpr.lift_instN_lo] using htype.instN henv W h₀

theorem TrProj.defeqDFC (henv : env.Ordered)
    (hΓ : env.IsDefEqCtx U Γ₀ Γ₁ Γ₂)
    (majorType' : env.HasType U Γ₂ major'
      (view.structureType levels params))
    (self : TrProj env U Γ₁ view levels params idx major result) :
    ∃ result', TrProj env U Γ₂ view levels params idx major' result' := by
  obtain ⟨code, hcode, -, htype⟩ := self.program
  refine ⟨.app code.projector major', {
    viewWF := self.viewWF
    levelsWF := self.levelsWF
    levels_length := self.levels_length
    params_length := self.params_length
    paramsSpine := self.paramsSpine.imp fun _ h => h.defeqDFC henv hΓ
    majorType := majorType'
    program := ⟨code, hcode, rfl, htype.defeqDFC henv hΓ⟩ }⟩

theorem TrProj.instL {ls : List VLevel}
    (hls : ∀ level ∈ ls, level.WF U')
    (self : TrProj env U Γ view levels params idx major result) :
    TrProj env U' (Γ.map (VExpr.instL ls)) view
      (levels.map (VLevel.inst ls))
      (params.map (VExpr.instL ls)) idx
      (major.instL ls) (result.instL ls) := by
  refine {
    viewWF := self.viewWF
    levelsWF := ?_
    levels_length := by simpa using self.levels_length
    params_length := by simpa using self.params_length
    paramsSpine := ?_
    majorType := by simpa using self.majorType.instL hls
    program := ?_ }
  · intro level hlevel
    obtain ⟨sourceLevel, hsourceLevel, rfl⟩ := List.mem_map.1 hlevel
    exact VLevel.WF.inst hls
  · obtain ⟨resultLevel, hspine⟩ := self.paramsSpine
    refine ⟨resultLevel.inst ls, ?_⟩
    simpa [VExpr.instL, VExpr.instL_instL] using hspine.instL hls
  · obtain ⟨code, hcode, rfl, htype⟩ := self.program
    refine ⟨code.instL ls, ?_, rfl, ?_⟩
    · rw [← projectionCodes_instL]
      simp only [List.getElem?_map, hcode, Option.map_some]
    · simpa [VStructureView.ProjectionCode.instL, VExpr.instL,
        VExpr.instL_liftN] using htype.instL hls

/-- Backend-owned generated-rule captures for a runtime constructor
application.  This package contains only the typed rule arguments; the iota
equation remains a separate theorem of the corresponding projection
backend. -/
def ConstructorRuleCapture (env : VEnv) (U : Nat) (Γ : List VExpr)
    (view : VProjectionView) (levels : List VLevel) (params : List VExpr)
    (idx : Nat) (code : VStructureView.ProjectionCode)
    (fields : List VExpr) : Prop :=
  match view with
  | .singleton selected =>
      ∃ B, env.SpineWF U Γ
        ((selected.generation.rule 0 selected.constructor).type.instL
          (selected.projectionLevels code.fieldSort levels))
        (params ++ [code.typeFn, code.minor] ++ fields) B
  | .block selected =>
      let motives := selected.projectionMotives levels params
        code.fieldSort code.typeFn
      let minors := selected.generation.flatCtors.map fun constructor =>
        selected.projectionMinor constructor code.fieldSort levels params
          (selected.specializedFields levels params) motives
          idx
      ∃ ruleIndex B,
        selected.generation.ruleEntry ruleIndex selected.blockConstructor ∧
        env.SpineWF U Γ
          ((selected.generation.rule ruleIndex selected.blockConstructor).type.instL
            (selected.projectionLevels code.fieldSort levels))
          (params ++ motives ++ minors ++ fields) B

/-- The projection-specific output of registered constructor-head inversion
for either honest backend.  It aligns syntax and typing but contains no final
projector equation. -/
structure ProjectionConstructorAlignment (env : VEnv) (U : Nat)
    (Γ : List VExpr) (view : VProjectionView) (levels : List VLevel)
    (params : List VExpr) (idx : Nat)
    (code : VStructureView.ProjectionCode)
    (runtimeConstructorName : Name) (runtimeMajor runtimeField : VExpr) where
  constructor_name_eq : runtimeConstructorName = view.constructorName
  fields : List VExpr
  field : VExpr
  fields_length :
    fields.length = (view.specializedFields levels params).length
  field_get : fields[idx]? = some field
  constructorType : env.HasType U Γ
    (VExpr.appN (.const view.constructorName levels) (params ++ fields))
    (view.structureType levels params)
  fieldsSpine : env.SpineWF U Γ
    (VExpr.forallN (view.specializedFields levels params) (.sort .zero))
    fields (.sort .zero)
  captures : ConstructorRuleCapture env U Γ view levels params idx code fields
  major_eq : env.IsDefEqU U Γ runtimeMajor
    (VExpr.appN (.const view.constructorName levels) (params ++ fields))
  field_eq : env.IsDefEqU U Γ runtimeField field

/-- Consume registered-head alignment with the backend-owned exact iota
theorem.  The inversion boundary supplies syntax and capture spines only;
singleton or mutual generation performs the computation here. -/
theorem TrProj.projector_constructor_aligned
    (self : TrProj env U Γ view levels params idx major result)
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    {code : VStructureView.ProjectionCode}
    (hcode : (view.projectionCodes levels params)[idx]? = some code)
    (hprojector : env.HasType U Γ code.projector
      (.forallE (view.structureType levels params)
        (.app code.typeFn.lift (.bvar 0))))
    {runtimeMajor runtimeField : VExpr}
    {runtimeConstructorName : Name}
    (alignment : ProjectionConstructorAlignment env U Γ view levels params
      idx code runtimeConstructorName runtimeMajor runtimeField) :
    env.IsDefEqU U Γ (.app code.projector runtimeMajor) runtimeField := by
  have hmajorEq := alignment.major_eq.of_r henv hΓ
    alignment.constructorType
  have hmajorCongr : env.IsDefEqU U Γ
      (.app code.projector runtimeMajor)
      (.app code.projector
        (VExpr.appN (.const view.constructorName levels)
          (params ++ alignment.fields))) :=
    ⟨_, hprojector.appDF hmajorEq⟩
  have checked := self.viewWF.materialize henv.ordered
  have hiota : env.IsDefEqU U Γ
      (.app code.projector
        (VExpr.appN (.const view.constructorName levels)
          (params ++ alignment.fields))) alignment.field := by
    cases checked with
    | singleton wf =>
        obtain ⟨captureType, hcaptures⟩ := alignment.captures
        exact wf.projector_constructor_exact henv hΓ self.levelsWF
          self.levels_length self.params_length self.paramsSpine hcode
          hprojector alignment.fields_length alignment.field_get
          alignment.constructorType alignment.fieldsSpine hcaptures
    | block wf =>
        exact wf.operationalProjector_constructor_exact henv hΓ self.levelsWF
          self.levels_length self.params_length self.paramsSpine hcode
          hprojector alignment.fields_length alignment.field_get
          alignment.constructorType alignment.fieldsSpine
  exact VEnv.IsDefEqU.trans henv hΓ hmajorCongr
    (VEnv.IsDefEqU.trans henv hΓ hiota alignment.field_eq.symm)

end VProjectionView

namespace VEnv

/-- The registered-projection constant-head inversion boundary.  Its view is
the explicit singleton-or-mutual sum, so every conclusion preserves the
recursor backend that owns the selected projector. -/
structure RegisteredStructureHeadInversion (env : VEnv) : Prop where
  weak'_inv :
    ∀ {U : Nat} {Γ Γ' : List VExpr} {view : VProjectionView}
      {levels : List VLevel} {params : List VExpr} {idx : Nat}
      {major result : VExpr} {lift : Lift},
      OnCtx Γ' (env.IsType U) →
      Ctx.Lift' lift Γ Γ' →
      VProjectionView.TrProj env U Γ' view levels params idx
        (major.lift' lift) result →
      ∃ params' result',
        VProjectionView.TrProj env U Γ view levels params' idx major result'
  unique :
    ∀ {U : Nat} {Γ₁ Γ₂ : List VExpr}
      {view₁ view₂ : VProjectionView}
      {levels₁ levels₂ : List VLevel} {params₁ params₂ : List VExpr}
      {idx : Nat} {major₁ major₂ result₁ result₂ : VExpr},
      env.IsDefEqCtx U [] Γ₁ Γ₂ →
      VProjectionView.TrProj env U Γ₁ view₁ levels₁ params₁ idx
        major₁ result₁ →
      VProjectionView.TrProj env U Γ₂ view₂ levels₂ params₂ idx
        major₂ result₂ →
      env.IsDefEqU U Γ₁ major₁ major₂ →
      env.IsDefEqU U Γ₁ result₁ result₂
  constructor_name_inv :
    ∀ {U : Nat} {Γ : List VExpr} {view : VProjectionView}
      {levels : List VLevel} {params : List VExpr} {idx : Nat}
      {major result runtimeMajor : VExpr}
      {constructorName : Name} {constructorLevels : List VLevel}
      {constructorArgs : List VExpr},
      OnCtx Γ (env.IsType U) →
      VProjectionView.TrProj env U Γ view levels params idx major result →
      env.ConstructorHead constructorName →
      runtimeMajor = VExpr.appN
        (.const constructorName constructorLevels) constructorArgs →
      env.IsDefEqU U Γ runtimeMajor major →
      constructorName = view.constructorName
  constructor_numParams_inv :
    ∀ {U : Nat} {Γ : List VExpr} {view : VProjectionView}
      {levels : List VLevel} {params : List VExpr} {idx : Nat}
      {major result runtimeMajor : VExpr}
      {constructorName : Name} {numParams : Nat}
      {constructorLevels : List VLevel}
      {constructorArgs : List VExpr},
      OnCtx Γ (env.IsType U) →
      VProjectionView.TrProj env U Γ view levels params idx major result →
      env.ConstructorHeadArity constructorName numParams →
      runtimeMajor = VExpr.appN
        (.const constructorName constructorLevels) constructorArgs →
      env.IsDefEqU U Γ runtimeMajor major →
      numParams = view.nparams
  constructor_inv :
    ∀ {U : Nat} {Γ : List VExpr} {view : VProjectionView}
      {levels : List VLevel} {params : List VExpr} {idx : Nat}
      {major result : VExpr} {code : VStructureView.ProjectionCode}
      {runtimeMajor runtimeField : VExpr}
      {constructorName : Name} {constructorLevels : List VLevel}
      {constructorArgs : List VExpr},
      OnCtx Γ (env.IsType U) →
      VProjectionView.TrProj env U Γ view levels params idx major result →
      env.ConstructorHead constructorName →
      (view.projectionCodes levels params)[idx]? = some code →
      runtimeMajor = VExpr.appN
        (.const constructorName constructorLevels) constructorArgs →
      constructorArgs[view.nparams + idx]? = some runtimeField →
      env.IsDefEqU U Γ runtimeMajor major →
      Nonempty (VProjectionView.ProjectionConstructorAlignment env U Γ view
        levels params idx code constructorName runtimeMajor runtimeField)

end VEnv

end Lean4Lean
