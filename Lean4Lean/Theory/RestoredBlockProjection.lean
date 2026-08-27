/-
This file is derived from lean4lean and has been modified by Argument Computer Corporation.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/

import Lean4Lean.Theory.BlockProjection
import Lean4Lean.Theory.Typing.InductiveCertificate
import Lean4Lean.Theory.Typing.NestedTransport

/-!
# Restored nested-block structure projections

A source family restored after nested elimination is not literally a family
of the flattened block: its constructor telescope has had auxiliary-family
applications collapsed back to the source syntax.  Nevertheless its
projection implementation is owned by one exact family position of the
flattened block and by that block's actual mutual recursor.

`VRestoredBlockStructureView` retains both sides without identifying them.
The source family and constructor are the metadata surface observed after
restoration; `flatView` is the exact checked block restriction which owns the
recursor layout.  Later semantic transport can therefore relate the two
endpoints without fabricating a singleton generation certificate or asking a
consumer to choose parallel family and constructor witnesses.
-/

namespace Lean4Lean

open VInductDecl

/-- One restored one-constructor, unindexed source family together with the
exact flattened block position which generated its recursor artifacts.  The
field-sort inventory is indexed by the restored constructor telescope; the
selection theorem proves that the same inventory also has the exact length
required by the flattened backend. -/
structure VRestoredBlockStructureView where
  source : VInductDecl
  nested : source.NestedBlockChecked
  familyIndex : Nat
  sourceFamily : VInductiveType
  sourceConstructor : VConstVal
  selection : NestedStructureSelection nested familyIndex sourceFamily
    sourceConstructor
  /-- The flattened constructor field telescope restores pointwise to the
  exact stored source telescope.  This is producer-owned syntax provenance;
  equal field counts alone are insufficient for dependent projection
  typing. -/
  flatFieldsRestored :
    (ctorFields
        (VExpr.dropN source.nparams selection.flatConstructor.type)).map
        (restoreExpr nested.declEntries nested.recMap) =
      ctorFields (VExpr.dropN source.nparams sourceConstructor.type)
  fieldSorts : List VLevel
  fieldSorts_length :
    fieldSorts.length =
      (ctorFields (VExpr.dropN source.nparams sourceConstructor.type)).length

namespace VRestoredBlockStructureView

/-- Fixed-offset substitution distributes through a lambda telescope with
the same progressive binder substitution used by the corresponding Pi
telescope. -/
theorem _root_.Lean4Lean.VExpr.instRevAt_lamN_projection
    (binders : List VExpr) (body : VExpr)
    (arguments : List VExpr) (offset : Nat) :
    (VExpr.lamN binders body).instRevAt arguments offset =
      VExpr.lamN
        (binders.zipIdx offset |>.map fun entry =>
          entry.1.instRevAt arguments entry.2)
        (body.instRevAt arguments (offset + binders.length)) := by
  induction binders generalizing offset with
  | nil => rfl
  | cons binder binders ih =>
      simp only [VExpr.lamN, VExpr.instRevAt_lam_projection,
        List.zipIdx, List.map_cons, List.length_cons]
      rw [ih]
      rw [show offset + 1 + binders.length =
        offset + (binders.length + 1) by omega]

/-- If an expression lifted above `cutoff` is closed after accounting for
the inserted variables, then the original expression was closed at the
corresponding shallower depth. -/
theorem _root_.Lean4Lean.VExpr.ClosedN.of_liftN
    {expression : VExpr} {count cutoff depth : Nat}
    (self : (expression.liftN count cutoff).ClosedN (depth + count))
    (hcutoff : cutoff ≤ depth) : expression.ClosedN depth := by
  induction expression generalizing cutoff depth with
  | bvar index =>
      simp only [VExpr.liftN, VExpr.ClosedN] at self ⊢
      unfold liftVar at self
      split at self
      · omega
      · omega
  | sort | const => trivial
  | app function argument functionIH argumentIH =>
      simp only [VExpr.liftN, VExpr.ClosedN] at self ⊢
      exact ⟨functionIH self.1 hcutoff, argumentIH self.2 hcutoff⟩
  | lam domain body domainIH bodyIH =>
      simp only [VExpr.liftN, VExpr.ClosedN] at self ⊢
      refine ⟨domainIH self.1 hcutoff,
        bodyIH ?_ (Nat.succ_le_succ hcutoff)⟩
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using self.2
  | forallE domain body domainIH bodyIH =>
      simp only [VExpr.liftN, VExpr.ClosedN] at self ⊢
      refine ⟨domainIH self.1 hcutoff,
        bodyIH ?_ (Nat.succ_le_succ hcutoff)⟩
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using self.2

/-- Closedness of a Pi telescope exposes the exact progressive closedness
boundary of any binder selected by index. -/
theorem _root_.Lean4Lean.VExpr.ClosedN.forallN_getElem?
    {binders : List VExpr} {body binder : VExpr}
    {depth index : Nat}
    (self : (VExpr.forallN binders body).ClosedN depth)
    (found : binders[index]? = some binder) :
    binder.ClosedN (depth + index) := by
  induction binders generalizing depth index with
  | nil => simp at found
  | cons head tail ih =>
      simp only [VExpr.forallN, VExpr.ClosedN] at self
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at found
          subst binder
          simpa using self.1
      | succ index =>
          simp only [List.getElem?_cons_succ] at found
          have tailClosed := ih self.2 found
          rw [show depth + (index + 1) = depth + 1 + index by omega]
          exact tailClosed

abbrev name (view : VRestoredBlockStructureView) : Name :=
  view.sourceFamily.name

abbrev constructorName (view : VRestoredBlockStructureView) : Name :=
  view.sourceConstructor.name

def recursorName (view : VRestoredBlockStructureView) : Name :=
  .str view.name "rec"

/-- The selected source family is an exact member of the declaration whose
metadata is restored. -/
theorem sourceFamily_mem (view : VRestoredBlockStructureView) :
    view.sourceFamily ∈ view.source.types :=
  List.mem_iff_getElem?.2 ⟨view.familyIndex, view.selection.source_at⟩

/-- The selected source constructor is the unique constructor retained by
the restored structure family. -/
theorem sourceConstructor_mem (view : VRestoredBlockStructureView) :
    view.sourceConstructor ∈ view.sourceFamily.ctors := by
  rw [view.selection.source_constructors_eq]
  simp

abbrev uvars (view : VRestoredBlockStructureView) : Nat :=
  view.source.uvars

abbrev nparams (view : VRestoredBlockStructureView) : Nat :=
  view.source.nparams

abbrev rawFamilyType (view : VRestoredBlockStructureView) : VExpr :=
  view.sourceFamily.type

abbrev resultLevel (view : VRestoredBlockStructureView) : VLevel :=
  view.nested.generation.validated.resultLevel

/-- Projection-facing family type on the restored metadata surface. -/
def familyType (view : VRestoredBlockStructureView) : VExpr :=
  VExpr.forallN (VExpr.telN view.nparams view.sourceFamily.type)
    (.sort view.resultLevel)

def constructorParams (view : VRestoredBlockStructureView) : List VExpr :=
  VExpr.telN view.nparams view.sourceConstructor.type

def fields (view : VRestoredBlockStructureView) : List VExpr :=
  ctorFields (VExpr.dropN view.nparams view.sourceConstructor.type)

def rawParams (view : VRestoredBlockStructureView) : List VExpr :=
  VExpr.telN view.nparams view.sourceFamily.type

theorem familyType_eq_forallN (view : VRestoredBlockStructureView) :
    view.familyType =
      VExpr.forallN view.rawParams (.sort view.resultLevel) := by
  rfl

def rawIndices (view : VRestoredBlockStructureView) : List VExpr :=
  ctorFields (VExpr.dropN view.nparams view.sourceFamily.type)

def rawResult (view : VRestoredBlockStructureView) : VExpr :=
  VExpr.resultOf (VExpr.dropN view.nparams view.sourceFamily.type)

def structureType (view : VRestoredBlockStructureView)
    (levels : List VLevel) (params : List VExpr) : VExpr :=
  VExpr.appN (.const view.name levels) params

def specializedFields (view : VRestoredBlockStructureView)
    (levels : List VLevel) (params : List VExpr) : List VExpr :=
  view.fields.zipIdx.map fun (field, i) =>
    VExpr.instRevAt (field.instL levels) params i

@[simp] theorem structureType_liftN (view : VRestoredBlockStructureView)
    (levels : List VLevel) (params : List VExpr) (count cutoff : Nat) :
    (view.structureType levels params).liftN count cutoff =
      view.structureType levels
        (params.map fun parameter => parameter.liftN count cutoff) := by
  simp [structureType, VExpr.liftN_appN, VExpr.liftN]

@[simp] theorem structureType_instN (view : VRestoredBlockStructureView)
    (levels : List VLevel) (params : List VExpr) (argument : VExpr)
    (cutoff : Nat) :
    (view.structureType levels params).inst argument cutoff =
      view.structureType levels
        (params.map fun parameter => parameter.inst argument cutoff) := by
  simp [structureType, VExpr.instN_appN, VExpr.inst]

@[simp] theorem structureType_instL (view : VRestoredBlockStructureView)
    (levels : List VLevel) (params : List VExpr) (extra : List VLevel) :
    (view.structureType levels params).instL extra =
      view.structureType (levels.map (VLevel.inst extra))
        (params.map (VExpr.instL extra)) := by
  simp [structureType, VExpr.instL_appN, VExpr.instL]

@[simp] theorem specializedFields_instL
    (view : VRestoredBlockStructureView)
    (levels : List VLevel) (params : List VExpr) (extra : List VLevel) :
    (view.specializedFields levels params).map (VExpr.instL extra) =
      view.specializedFields (levels.map (VLevel.inst extra))
        (params.map (VExpr.instL extra)) := by
  simp [specializedFields, VExpr.instL_instRevAt,
    VExpr.instL_instL, Function.comp_def]

/-- The source constructor paired with the checked recursive annotations of
the exact flattened producer.  This is a projection-facing descriptor only;
it is deliberately not claimed to be a member of the flattened generation. -/
def constructor (view : VRestoredBlockStructureView) : NormalizedCtor :=
  ⟨view.sourceConstructor, view.selection.constructor.view⟩

/-- The exact ordinary block restriction retained inside a restored view.
Its field-sort inventory is valid positionally because nested elimination
preserves the complete constructor Pi arity and the source parameter split. -/
def flatView (view : VRestoredBlockStructureView) : VBlockStructureView where
  source := view.nested.elim.flat
  generation := view.nested.generation
  family := view.selection.family
  family_mem := List.mem_iff_getElem?.2
    ⟨view.familyIndex, view.selection.family_at⟩
  constructor := view.selection.constructor
  constructor_eq := view.selection.constructors_eq
  raw_indices_eq := view.selection.flat_raw_indices_eq
  checked_indices_eq := view.selection.checked_indices_eq
  fieldSorts := view.fieldSorts
  fieldSorts_length := view.fieldSorts_length.trans
    view.selection.source_flat_fields_length_eq

/-- The restored backend uses the exact elimination mode and recursor
universe arity of its retained flattened generator. -/
abbrev elimination (view : VRestoredBlockStructureView) : ElimMode :=
  view.nested.generation.elimination

abbrev recUvars (view : VRestoredBlockStructureView) : Nat :=
  view.nested.generation.recUvars

/-- As for the ordinary block backend, an extra recursor universe parameter
forces the exact retained generator into its large-elimination branch. -/
theorem elimination_eq_large_of_uvars_lt_recUvars
    (view : VRestoredBlockStructureView)
    (larger : view.uvars < view.recUvars) :
    view.elimination = .large := by
  cases mode : view.nested.generation.elimination with
  | large => simp [elimination, mode]
  | small =>
      have flatUvars : view.nested.elim.flat.uvars = view.uvars := by
        simpa using congrArg VInductDecl.uvars view.nested.elim.flat_eq
      simp [elimination, recUvars,
        VInductDecl.BlockGenerationChecked.recUvars, mode,
        flatUvars] at larger

/-- Runtime projection levels are still selected by the exact flattened
recursor.  Only expression payloads are restored. -/
def projectionLevels (view : VRestoredBlockStructureView)
    (fieldSort : VLevel) (levels : List VLevel) : List VLevel :=
  view.flatView.projectionLevels fieldSort levels

/-- Large elimination preserves the selected restored field universe in the
projection motive.  Runtime inference uses this environment-free equality
before asking the restored backend to type the corresponding program. -/
theorem motiveLevel_projectionLevels_of_large
    (view : VRestoredBlockStructureView)
    (large : view.elimination = .large)
    (fieldSort : VLevel) (levels : List VLevel) :
    view.nested.generation.motiveLevel.inst
        (view.projectionLevels fieldSort levels) = fieldSort := by
  exact view.flatView.motiveLevel_projectionLevels_of_large large
    fieldSort levels

/-- The flattened and restored family names are literally identical. -/
theorem flatView_name (view : VRestoredBlockStructureView) :
    view.flatView.name = view.name := by
  have headerName := congrArg NestedFamilyHeader.name
    view.selection.family_header_eq
  change view.selection.family.raw.name = view.sourceFamily.name
  rw [view.selection.family_raw_eq]
  simpa [VInductiveType.nestedHeader] using headerName

/-- Consequently the selected flattened recursor and its restored source
surface use the same name; only its expression payload is restored. -/
theorem flatView_recursorName (view : VRestoredBlockStructureView) :
    view.flatView.recursorName = view.recursorName := by
  rw [VBlockStructureView.recursorName, recursorName, view.flatView_name]

/-- The flattened and restored constructor names are literally identical. -/
theorem flatView_constructorName (view : VRestoredBlockStructureView) :
    view.flatView.constructorName = view.constructorName := by
  have headerName := congrArg NestedCtorHeader.name
    view.selection.constructor_header_eq
  change view.selection.constructor.raw.name = view.sourceConstructor.name
  rw [view.selection.constructor_raw_eq]
  simpa [VConstVal.nestedHeader] using headerName

/-- Family types are restoration-stable, so the flattened block and restored
metadata surface expose the same raw family type. -/
theorem flatView_rawFamilyType (view : VRestoredBlockStructureView) :
    view.flatView.rawFamilyType = view.rawFamilyType := by
  have headerType := congrArg NestedFamilyHeader.type
    view.selection.family_header_eq
  change view.selection.family.raw.type = view.sourceFamily.type
  rw [view.selection.family_raw_eq]
  simpa [VInductiveType.nestedHeader] using headerType

/-- Flattening leaves the declaration universe and shared parameter counts
unchanged. -/
theorem flatView_uvars (view : VRestoredBlockStructureView) :
    view.flatView.uvars = view.uvars := by
  simpa [flatView] using congrArg VInductDecl.uvars
    view.nested.elim.flat_eq

theorem flatView_nparams (view : VRestoredBlockStructureView) :
    view.flatView.nparams = view.nparams :=
  view.nested.elim.nparams_eq

/-- Nested elimination leaves the selected constructor's shared-parameter
prefix literally unchanged.  The restored view can therefore reuse any
pre-family equality proved for the flattened raw prefix without transporting
that equality through the restoration substitution. -/
theorem flatView_constructorParams (view : VRestoredBlockStructureView) :
    view.flatView.constructorParams = view.constructorParams := by
  change VExpr.telN view.nested.elim.flat.nparams
      view.selection.constructor.raw.type =
    VExpr.telN view.source.nparams view.sourceConstructor.type
  rw [view.nested.elim.nparams_eq, view.selection.constructor_raw_eq]
  exact view.selection.flat_constructor_params_eq

/-- The recursor-world replacement inventory is exactly the
declaration-world inventory transported along the generated source-universe
spine.  This is the symbolic form of the producer's universe splice, before
any operational projection levels are supplied. -/
theorem recEntries_eq_declEntries_instL_sourceLevels
    (view : VRestoredBlockStructureView) :
    view.nested.recEntries =
      view.nested.declEntries.map
        (·.instL view.nested.generation.sourceLevels) := by
  have flatUvars : view.nested.elim.flat.uvars = view.source.uvars := by
    simpa using congrArg VInductDecl.uvars view.nested.elim.flat_eq
  have spliceLevels :
      VLevel.params' view.source.uvars
          (view.nested.generation.recUvars - view.source.uvars) =
        view.nested.generation.sourceLevels := by
    rw [← flatUvars]
    simp [BlockGenerationChecked.recUvars,
      BlockGenerationChecked.sourceLevels, ElimMode.recUvars]
  unfold NestedBlockChecked.recEntries NestedBlockChecked.declEntries
  simp only [List.map_map]
  apply List.map_congr_left
  intro spec _
  cases spec
  simp only [Function.comp_apply, RestoreEntry.instL]
  rw [spliceLevels]

/-- The recursor-world restoration inventory, instantiated at the exact
projection universe spine, is literally the declaration-world restoration
inventory instantiated at the caller's source universe levels.  Thus the
fresh large-elimination motive universe cannot leak into restored source
syntax. -/
theorem recEntries_instL_projectionLevels
    (view : VRestoredBlockStructureView) (fieldSort : VLevel)
    (levels : List VLevel) (hlevels : levels.length = view.uvars) :
    view.nested.recEntries.map
        (·.instL (view.flatView.projectionLevels fieldSort levels)) =
      view.nested.declEntries.map (·.instL levels) := by
  have sourceLevels := view.flatView.sourceLevels_projectionLevels
    fieldSort levels (by simpa only [view.flatView_uvars] using hlevels)
  have sourceLevels' :
      view.nested.generation.sourceLevels.map
          (VLevel.inst (view.flatView.projectionLevels fieldSort levels)) =
        levels := by
    simpa [flatView] using sourceLevels
  have flatUvars : view.nested.elim.flat.uvars = view.source.uvars := by
    simpa using congrArg VInductDecl.uvars view.nested.elim.flat_eq
  have spliceLevels :
      VLevel.params' view.source.uvars
          (view.nested.generation.recUvars - view.source.uvars) =
        view.nested.generation.sourceLevels := by
    rw [← flatUvars]
    simp [BlockGenerationChecked.recUvars,
      BlockGenerationChecked.sourceLevels, ElimMode.recUvars]
  unfold NestedBlockChecked.recEntries NestedBlockChecked.declEntries
  simp only [List.map_map]
  apply List.map_congr_left
  intro spec _
  cases spec with
  | mk aux target specLevels values =>
      simp only [Function.comp_apply, RestoreEntry.instL,
        VExpr.instL_instL]
      rw [spliceLevels, sourceLevels']

/-- At a valid source universe spine, the runtime restoration operator is
independent of the extra motive universe used by an individual projector.
Only the declaration universe prefix reaches the instantiated restoration
inventory. -/
theorem restoreRecAt_projectionLevels_eq
    (view : VRestoredBlockStructureView) (left right : VLevel)
    (levels : List VLevel) (hlevels : levels.length = view.uvars)
    (expression : VExpr) :
    view.nested.restoreRecAt
        (view.flatView.projectionLevels left levels) expression =
      view.nested.restoreRecAt
        (view.flatView.projectionLevels right levels) expression := by
  unfold NestedBlockChecked.restoreRecAt
  rw [view.recEntries_instL_projectionLevels left levels hlevels,
    view.recEntries_instL_projectionLevels right levels hlevels]

/-- Runtime restoration in the producer's recursor universe world agrees
exactly with declaration-world restoration followed by source-universe
instantiation. -/
theorem restoreRecAt_source_instL
    (view : VRestoredBlockStructureView) (fieldSort : VLevel)
    (levels : List VLevel) (hlevels : levels.length = view.uvars)
    (expression : VExpr) :
    view.nested.restoreRecAt
        (view.flatView.projectionLevels fieldSort levels)
        (expression.instL levels) =
      (restoreExpr view.nested.declEntries view.nested.recMap expression).instL
        levels := by
  rw [VInductDecl.restoreExpr_instL]
  unfold NestedBlockChecked.restoreRecAt
  rw [view.recEntries_instL_projectionLevels fieldSort levels hlevels]

/-- Declaration-world restoration sends the exact flattened field telescope
to the selected source constructor's field telescope. -/
theorem restoreFlatFields (view : VRestoredBlockStructureView) :
    view.flatView.fields.map
        (restoreExpr view.nested.declEntries view.nested.recMap) =
      view.fields := by
  change (view.selection.constructor.rawFields
      view.nested.elim.flat.nparams).map
        (restoreExpr view.nested.declEntries view.nested.recMap) =
    ctorFields (VExpr.dropN view.source.nparams
      view.sourceConstructor.type)
  rw [view.nested.elim.nparams_eq, NormalizedCtor.rawFields,
    view.selection.constructor_raw_eq]
  exact view.flatFieldsRestored

/-- The flattened constructor fields specialized into the generated
recursor universe restore exactly to the selected source fields specialized
along the same source-universe spine. -/
theorem restoreRuleRawFields (view : VRestoredBlockStructureView) :
    let gen := view.nested.generation
    let constructor := view.flatView.blockConstructor
    (constructor.ctor.fieldsR view.nested.elim.flat.uvars
        view.nested.elim.flat.nparams gen.elimination).map
        view.nested.restoreRec =
      view.fields.map (VExpr.instL gen.sourceLevels) := by
  let gen := view.nested.generation
  let constructor := view.flatView.blockConstructor
  dsimp only
  have entries := view.recEntries_eq_declEntries_instL_sourceLevels
  have fields := view.restoreFlatFields
  rw [NormalizedCtor.fieldsR]
  simp only [List.map_map, Function.comp_def]
  unfold NestedBlockChecked.restoreRec
  rw [entries]
  change view.flatView.fields.map (fun field =>
      restoreExpr
        (view.nested.declEntries.map (·.instL gen.sourceLevels))
        view.nested.recMap (field.instL gen.sourceLevels)) = _
  have commute :
      (fun field => restoreExpr
          (view.nested.declEntries.map (·.instL gen.sourceLevels))
          view.nested.recMap (field.instL gen.sourceLevels)) =
        (fun field =>
          (restoreExpr view.nested.declEntries view.nested.recMap field).instL
            gen.sourceLevels) := by
    funext field
    exact (VInductDecl.restoreExpr_instL view.nested.declEntries
      view.nested.recMap field gen.sourceLevels).symm
  rw [commute]
  rw [← fields]
  simp only [List.map_map, Function.comp_def]
  rfl

/-- The field suffix of the selected generated rule restores to the source
field telescope embedded beneath the rule's motive-and-minor prefix. -/
theorem restoreRuleFieldBinders (view : VRestoredBlockStructureView)
    (closed : RestoreEntriesClosed view.nested.recEntries) :
    let gen := view.nested.generation
    let constructor := view.flatView.blockConstructor
    let commonCount := gen.familyCount + gen.minorCount
    (gen.ruleFieldBinders constructor).map view.nested.restoreRec =
      VExpr.liftTelN commonCount
        (view.fields.map (VExpr.instL gen.sourceLevels)) 0 := by
  let gen := view.nested.generation
  let constructor := view.flatView.blockConstructor
  let commonCount := gen.familyCount + gen.minorCount
  dsimp only
  rw [BlockGenerationChecked.ruleFieldBinders]
  unfold NestedBlockChecked.restoreRec
  rw [VInductDecl.restoreExpr_liftTelN view.nested.recEntries closed
    view.nested.recMap]
  have raw := view.restoreRuleRawFields
  dsimp only at raw
  unfold NestedBlockChecked.restoreRec at raw
  rw [raw]

/-- Runtime restoration maps the exact flattened producer field inventory
to the source field inventory after declaration-universe instantiation.  The
view retains the pointwise telescope equation, so this statement no longer
depends on recovering the completed transaction which constructed it. -/
theorem restoreFlatFields_instL
    (view : VRestoredBlockStructureView)
    (fieldSort : VLevel) (levels : List VLevel)
    (hlevels : levels.length = view.uvars) :
    view.flatView.fields.map (fun field =>
        view.nested.restoreRecAt
          (view.flatView.projectionLevels fieldSort levels)
          (field.instL levels)) =
      view.fields.map (VExpr.instL levels) := by
  have flatFields : view.flatView.fields =
      ctorFields
        (VExpr.dropN view.source.nparams
          view.selection.flatConstructor.type) := by
    change ctorFields
      (VExpr.dropN view.flatView.nparams
        view.selection.constructor.raw.type) = _
    rw [view.flatView_nparams, view.selection.constructor_raw_eq]
  have sourceFields : view.fields =
      ctorFields
        (VExpr.dropN view.source.nparams view.sourceConstructor.type) := by
    rfl
  have fieldsRestored :
      view.flatView.fields.map
          (restoreExpr view.nested.declEntries view.nested.recMap) =
        view.fields := by
    rw [flatFields, sourceFields]
    exact view.flatFieldsRestored
  rw [← congrArg (List.map (VExpr.instL levels)) fieldsRestored]
  simp only [List.map_map]
  apply List.map_congr_left
  intro field _
  exact view.restoreRecAt_source_instL fieldSort levels hlevels field

/-- Restoration of the flattened specialized field inventory agrees
pointwise with the restored source inventory whenever runtime parameters are
outside the restoration domain.  Operational code templates instantiate
parameters only after this declaration-time restoration step. -/
theorem restoreFlatSpecializedFields
    (view : VRestoredBlockStructureView)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    (fieldSort : VLevel) (levels : List VLevel)
    (hlevels : levels.length = view.uvars) (params : List VExpr)
    (paramsInert : ∀ parameter ∈ params,
      RestoreInert
        (view.nested.recEntries.map
          (·.instL (view.flatView.projectionLevels fieldSort levels)))
        view.nested.recMap parameter) :
    (view.flatView.specializedFields levels params).map
        (view.nested.restoreRecAt
          (view.flatView.projectionLevels fieldSort levels)) =
      view.specializedFields levels params := by
  let projectionLevels := view.flatView.projectionLevels fieldSort levels
  have raw := view.restoreFlatFields_instL fieldSort levels hlevels
  change view.flatView.fields.map (fun field =>
      view.nested.restoreRecAt projectionLevels (field.instL levels)) =
    view.fields.map (VExpr.instL levels) at raw
  apply List.ext_getElem?
  intro index
  simp only [specializedFields,
    VBlockStructureView.specializedFields, List.getElem?_map,
    List.getElem?_zipIdx, Nat.zero_add]
  have rawAt := congrArg (fun fields : List VExpr => fields[index]?) raw
  simp only [List.getElem?_map] at rawAt
  cases flatFound : view.flatView.fields[index]? with
  | none =>
      cases sourceFound : view.fields[index]? <;>
        simp [flatFound, sourceFound] at rawAt ⊢
  | some flatField =>
      cases sourceFound : view.fields[index]? with
      | none => simp [flatFound, sourceFound] at rawAt
      | some sourceField =>
          simp only [flatFound, sourceFound, Option.map_some] at rawAt ⊢
          rw [← view.nested.restoreRecAt_instRevAt closed projectionLevels
            (flatField.instL levels) params index paramsInert]
          rw [Option.some.inj rawAt]

/-- Canonical formal parameter variables contain no restoration-domain
constant and are therefore inert for every nested restoration inventory. -/
theorem bvarRevRange_restoreInert
    (entries : List RestoreEntry) (recMap : List (Name × Name))
    (offset count : Nat) :
    ∀ parameter ∈ VExpr.bvarRevRange offset count,
      RestoreInert entries recMap parameter := by
  intro parameter member
  obtain ⟨index, rfl, _, _⟩ := VExpr.mem_bvarRevRange member
  intro name present
  simp [VExpr.hasConst] at present

/-- Restoring a canonical de Bruijn range is pointwise the identity. -/
theorem bvarRevRange_restoreExpr_map
    (entries : List RestoreEntry) (recMap : List (Name × Name))
    (offset count : Nat) :
    (VExpr.bvarRevRange offset count).map
        (restoreExpr entries recMap) =
      VExpr.bvarRevRange offset count := by
  have mapped :
      (VExpr.bvarRevRange offset count).map
          (restoreExpr entries recMap) =
        (VExpr.bvarRevRange offset count).map id := by
    apply List.map_congr_left
    intro expression member
    exact (bvarRevRange_restoreInert entries recMap offset count
      expression member).restoreExpr_eq
  simpa using mapped

/-- Recursor-world restoration leaves the selected source family application
literal when its arguments are canonical formal parameters. -/
theorem restoreRec_sourceFamilyApp
    (view : VRestoredBlockStructureView)
    (levels : List VLevel) (offset : Nat) :
    view.nested.restoreRec
        (VExpr.appN (.const view.name levels)
          (VExpr.bvarRevRange offset view.nparams)) =
      VExpr.appN (.const view.name levels)
        (VExpr.bvarRevRange offset view.nparams) := by
  have inert := view.nested.sourceFamilyName_restoreRecInert
    view.sourceFamily_mem levels
  obtain ⟨hrec, hentry, hctor⟩ := inert view.name (by
    simp [VExpr.hasConst])
  unfold NestedBlockChecked.restoreRec
  rw [VInductDecl.restoreExpr_appN_of_head_inert
    inert.restoreExpr_eq (by rfl) hrec hentry hctor]
  rw [bvarRevRange_restoreExpr_map]

/-- Runtime restoration at an instantiated recursor universe spine leaves
the selected source-family application on canonical formal parameters
literal.  This identifies the restored type-function binder with the public
source structure domain before caller parameters are substituted. -/
theorem restoreRecAt_flatStructureType_bvarRevRange
    (view : VRestoredBlockStructureView)
    (fieldSort : VLevel) (levels : List VLevel) :
    view.nested.restoreRecAt
        (view.flatView.projectionLevels fieldSort levels)
        (view.flatView.structureType levels
          (VExpr.bvarRevRange 0 view.nparams)) =
      view.structureType levels (VExpr.bvarRevRange 0 view.nparams) := by
  let projectionLevels := view.flatView.projectionLevels fieldSort levels
  have inert : RestoreInert
      (view.nested.recEntries.map (·.instL projectionLevels))
      view.nested.recMap (.const view.name levels) := by
    have base : RestoreInert view.nested.recEntries view.nested.recMap
        (.const view.name levels) :=
      view.nested.sourceFamilyName_restoreRecInert
        view.sourceFamily_mem levels
    exact base.instLEntries projectionLevels
  obtain ⟨recMapMiss, entryMiss, constructorMiss⟩ :=
    inert view.name (by simp [VExpr.hasConst])
  unfold NestedBlockChecked.restoreRecAt
  rw [show view.flatView.structureType levels
        (VExpr.bvarRevRange 0 view.nparams) =
      VExpr.appN (.const view.name levels)
        (VExpr.bvarRevRange 0 view.nparams) by
    simp [VBlockStructureView.structureType, view.flatView_name]]
  rw [VInductDecl.restoreExpr_appN_of_head_inert
    inert.restoreExpr_eq (by rfl) recMapMiss entryMiss constructorMiss]
  rw [bvarRevRange_restoreExpr_map]
  rfl

/-- Recursor-world restoration leaves the selected source constructor
application literal when its arguments are canonical parameters and fields. -/
theorem restoreRec_sourceConstructorApp
    (view : VRestoredBlockStructureView)
    (levels : List VLevel) (parameterOffset fieldCount : Nat) :
    view.nested.restoreRec
        (VExpr.appN (.const view.constructorName levels)
          (VExpr.bvarRevRange parameterOffset view.nparams ++
            VExpr.bvarRevRange 0 fieldCount)) =
      VExpr.appN (.const view.constructorName levels)
        (VExpr.bvarRevRange parameterOffset view.nparams ++
          VExpr.bvarRevRange 0 fieldCount) := by
  have inert := view.nested.sourceConstructorName_restoreRecInert
    view.sourceFamily_mem view.sourceConstructor_mem levels
  obtain ⟨hrec, hentry, hctor⟩ := inert view.constructorName (by
    simp [VExpr.hasConst])
  unfold NestedBlockChecked.restoreRec
  rw [VInductDecl.restoreExpr_appN_of_head_inert
    inert.restoreExpr_eq (by rfl) hrec hentry hctor]
  rw [List.map_append, bvarRevRange_restoreExpr_map,
    bvarRevRange_restoreExpr_map]

/-- The exact selected generated rule major restores to the literal source
constructor application with its canonical parameter and field variables. -/
theorem restoreRec_ruleCtorApp (view : VRestoredBlockStructureView) :
    let gen := view.nested.generation
    let constructor := view.flatView.blockConstructor
    view.nested.restoreRec (gen.ruleCtorApp constructor) =
      VExpr.appN (.const view.constructorName gen.sourceLevels)
        (VExpr.bvarRevRange
            (gen.ruleFieldCount constructor +
              (gen.familyCount + gen.minorCount))
            view.nparams ++
          VExpr.bvarRevRange 0 (gen.ruleFieldCount constructor)) := by
  let gen := view.nested.generation
  let constructor := view.flatView.blockConstructor
  dsimp only
  have constructorName : constructor.ctor.raw.name =
      view.constructorName := by
    exact view.flatView_constructorName
  rw [show gen.ruleCtorApp constructor =
      VExpr.appN (.const view.constructorName gen.sourceLevels)
        (VExpr.bvarRevRange
            (gen.ruleFieldCount constructor +
              (gen.familyCount + gen.minorCount))
            view.nparams ++
          VExpr.bvarRevRange 0 (gen.ruleFieldCount constructor)) by
    simp only [BlockGenerationChecked.ruleCtorApp, constructorName]
    rw [show view.nested.elim.flat.nparams = view.nparams from
      view.nested.elim.nparams_eq]]
  exact view.restoreRec_sourceConstructorApp gen.sourceLevels _ _

/-- Declaration-time restored projector templates use only canonical formal
parameters, so their flattened and source specialized field inventories
agree without a caller-side inertness premise. -/
theorem restoreFlatSpecializedFields_bvarRevRange
    (view : VRestoredBlockStructureView)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    (fieldSort : VLevel) (levels : List VLevel)
    (hlevels : levels.length = view.uvars) :
    (view.flatView.specializedFields levels
        (VExpr.bvarRevRange 0 view.nparams)).map
        (view.nested.restoreRecAt
          (view.flatView.projectionLevels fieldSort levels)) =
      view.specializedFields levels
        (VExpr.bvarRevRange 0 view.nparams) := by
  apply view.restoreFlatSpecializedFields closed fieldSort levels hlevels
  exact bvarRevRange_restoreInert _ _ _ _

/-- The sort-normalized family type is the same on the flattened and restored
surfaces because family types themselves are never rewritten. -/
theorem flatView_familyType (view : VRestoredBlockStructureView) :
    view.flatView.familyType = view.familyType := by
  change VExpr.forallN
      (VExpr.telN view.flatView.nparams view.flatView.rawFamilyType)
        (.sort view.flatView.resultLevel) =
    VExpr.forallN (VExpr.telN view.nparams view.rawFamilyType)
      (.sort view.resultLevel)
  rw [view.flatView_nparams, view.flatView_rawFamilyType]
  rfl

/-- The exact source family remains unindexed at the restored surface. -/
theorem raw_indices_eq (view : VRestoredBlockStructureView) :
    view.rawIndices = [] := by
  simpa [rawIndices] using view.selection.source_raw_indices_eq

theorem rawParams_length (view : VRestoredBlockStructureView) :
    view.rawParams.length = view.nparams := by
  have flat := view.flatView.raw_params_length
  change (VExpr.telN view.flatView.nparams
    view.flatView.rawFamilyType).length = view.flatView.nparams at flat
  rw [view.flatView_nparams, view.flatView_rawFamilyType] at flat
  simpa [rawParams] using flat

theorem constructorParams_length (view : VRestoredBlockStructureView) :
    view.constructorParams.length = view.nparams := by
  simpa [constructorParams] using
    view.selection.source_constructor_params_length

/-- The restored family and constructor constants retain the declaration's
universe arity. -/
theorem family_uvars_eq (view : VRestoredBlockStructureView) :
    view.sourceFamily.uvars = view.uvars := by
  have headerUvars := congrArg NestedFamilyHeader.uvars
    view.selection.family_header_eq
  have flatFamilyUvars : view.selection.flatFamily.uvars =
      view.nested.elim.flat.uvars := by
    rw [← view.selection.family_raw_eq]
    exact view.flatView.family_uvars_eq
  calc
    view.sourceFamily.uvars = view.selection.flatFamily.uvars := by
      simpa [VInductiveType.nestedHeader] using headerUvars.symm
    _ = view.nested.elim.flat.uvars := flatFamilyUvars
    _ = view.source.uvars := by
      simpa using congrArg VInductDecl.uvars view.nested.elim.flat_eq

theorem constructor_uvars_eq (view : VRestoredBlockStructureView) :
    view.sourceConstructor.uvars = view.uvars :=
  view.selection.source_constructor_uvars_eq

/-- The exact flattened recursor selected before restoration. -/
def flatRecursor (view : VRestoredBlockStructureView) : VConstVal :=
  ⟨view.nested.generation.generatedRecursor view.selection.family,
    view.flatView.recursorName⟩

/-- The exact final recursor selected after nested restoration.  Its type is
the producer's restored flattened recursor type, while source-name hygiene
proves that its name is not redirected through the auxiliary recursor map. -/
def recursor (view : VRestoredBlockStructureView) : VConstVal :=
  ⟨⟨view.flatRecursor.uvars,
      view.nested.restoreRec view.flatRecursor.type⟩,
    view.recursorName⟩

/-- The selected flattened recursor is present in the complete producer
inventory at the exact selected family position. -/
theorem flatRecursor_mem (view : VRestoredBlockStructureView) :
    view.flatRecursor ∈ view.nested.generation.recursors := by
  simp only [flatRecursor, BlockGenerationChecked.recursors, List.mem_map]
  exact ⟨view.selection.family, view.flatView.family_mem, rfl⟩

/-- Restoration retains the selected source-family recursor exactly in the
final nested recursor inventory. -/
theorem recursor_mem (view : VRestoredBlockStructureView) :
    view.recursor ∈ view.nested.recursors := by
  simp only [NestedBlockChecked.recursors, List.mem_map]
  refine ⟨view.flatRecursor, view.flatRecursor_mem, ?_⟩
  have unchanged :=
    view.nested.recMap_find?_source_recursor_eq_none view.sourceFamily_mem
  have flatName : view.flatRecursor.name = view.recursorName := by
    simp only [flatRecursor]
    exact view.flatView_recursorName
  have unchangedName :
      view.nested.recMap.find? (·.1 == view.recursorName) = none := by
    exact unchanged
  simp only [recursor, flatName, unchangedName, Option.map_none,
    Option.getD_none]

/-- Restore every expression payload of one flattened operational projection
code in the exact universe world selected by that code.  The field-sort key
is metadata, not an expression payload, and is therefore retained literally. -/
def restoreProjectionCodeAt (view : VRestoredBlockStructureView)
    (levels : List VLevel)
    (code : VStructureView.ProjectionCode) :
    VStructureView.ProjectionCode :=
  let recursorLevels :=
    view.flatView.projectionLevels code.fieldSort levels
  { fieldSort := code.fieldSort
    typeFn := view.nested.restoreRecAt recursorLevels code.typeFn
    minor := view.nested.restoreRecAt recursorLevels code.minor
    projector := view.nested.restoreRecAt recursorLevels code.projector }

@[simp] theorem restoreProjectionCodeAt_fieldSort
    (view : VRestoredBlockStructureView) (levels : List VLevel)
    (code : VStructureView.ProjectionCode) :
    (view.restoreProjectionCodeAt levels code).fieldSort = code.fieldSort :=
  rfl

/-- Restored operational codes remain natural under a further universe
instantiation. -/
@[simp] theorem restoreProjectionCodeAt_instL
    (view : VRestoredBlockStructureView) (levels : List VLevel)
    (code : VStructureView.ProjectionCode) (extra : List VLevel) :
    (view.restoreProjectionCodeAt levels code).instL extra =
      view.restoreProjectionCodeAt (levels.map (VLevel.inst extra))
        (code.instL extra) := by
  apply VStructureView.ProjectionCode.ext
  · rfl
  · simp [restoreProjectionCodeAt,
      VStructureView.ProjectionCode.instL]
  · simp [restoreProjectionCodeAt,
      VStructureView.ProjectionCode.instL]
  · simp [restoreProjectionCodeAt,
      VStructureView.ProjectionCode.instL]

/-- Restoring one operational code commutes with ambient lifting under the
producer's exact replacement-closure invariant. -/
theorem restoreProjectionCodeAt_liftN
    (view : VRestoredBlockStructureView)
    (closed : VInductDecl.RestoreEntriesClosed view.nested.recEntries)
    (levels : List VLevel) (code : VStructureView.ProjectionCode)
    (count cutoff : Nat) :
    (view.restoreProjectionCodeAt levels code).liftN count cutoff =
      view.restoreProjectionCodeAt levels (code.liftN count cutoff) := by
  apply VStructureView.ProjectionCode.ext
  · rfl
  · exact view.nested.restoreRecAt_liftN closed _ _ count cutoff
  · exact view.nested.restoreRecAt_liftN closed _ _ count cutoff
  · exact view.nested.restoreRecAt_liftN closed _ _ count cutoff

/-- Canonical flattened projection templates in the context of the source
parameter telescope.  Restoration happens at this declaration-time boundary,
before any caller expression is present. -/
def flatProjectionCodeTemplates (view : VRestoredBlockStructureView)
    (levels : List VLevel) : List VStructureView.ProjectionCode :=
  view.flatView.operationalProjectionCodes levels
    (VExpr.bvarRevRange 0 view.nparams)

/-- Declaration-time restoration of the exact flattened templates.  The
formal parameter variables are inert by construction. -/
def restoredProjectionCodeTemplates (view : VRestoredBlockStructureView)
    (levels : List VLevel) : List VStructureView.ProjectionCode :=
  (view.flatProjectionCodeTemplates levels).map
    (view.restoreProjectionCodeAt levels)

/-- Exact runtime projector inventory at the restored endpoint.  Runtime
parameters are substituted only after restoration and are consequently
opaque to the producer's auxiliary-name rewrite. -/
def operationalProjectionCodes (view : VRestoredBlockStructureView)
    (levels : List VLevel) (params : List VExpr) :
    List VStructureView.ProjectionCode :=
  (view.restoredProjectionCodeTemplates levels).map
    (fun code => code.instRevAt params 0)

/-- Per-family restored motive domains after recursor-universe and source
parameter specialization, before the progressive weakening imposed by the
mutual motive telescope. -/
def operationalProjectionMotiveTypes
    (view : VRestoredBlockStructureView)
    (fieldSort : VLevel) (levels : List VLevel)
    (params : List VExpr) : List VExpr :=
  let gen := view.nested.generation
  let projectionLevels := view.flatView.projectionLevels fieldSort levels
  gen.families.map fun family =>
    (view.nested.restoreRecAt projectionLevels
      ((gen.motiveType family).instL projectionLevels)).instRev params

/-- Per-constructor restored minor domains after universe, source-parameter,
and complete motive specialization, before the progressive weakening imposed
by the mutual minor telescope. -/
def operationalProjectionMinorTypes
    (view : VRestoredBlockStructureView)
    (fieldSort : VLevel) (levels : List VLevel)
    (params motives : List VExpr) : List VExpr :=
  let gen := view.nested.generation
  let projectionLevels := view.flatView.projectionLevels fieldSort levels
  gen.flatCtors.map fun constructor =>
    ((view.nested.restoreRecAt projectionLevels
      ((gen.minorType constructor).instL projectionLevels)).instRevAt
        params gen.familyCount).instRev motives

/-- The post-minor selected-family major cursor in the raw generated
recursor.  It is kept private; consumers use its restored and operational
specializations below. -/
private def projectionRecursorMajorTail
    (view : VRestoredBlockStructureView) : VExpr :=
  let gen := view.nested.generation
  VExpr.forallN
    (VExpr.liftTelN (gen.familyCount + gen.minorCount)
      (gen.idxTel view.selection.family) 0) <|
    .forallE
      (VExpr.appN
        (.const view.selection.family.raw.name gen.sourceLevels)
        (VExpr.bvarRevRange
            ((gen.idxTel view.selection.family).length +
              gen.familyCount + gen.minorCount)
            view.nested.elim.flat.nparams ++
          VExpr.bvarRevRange 0
            (gen.idxTel view.selection.family).length)) <|
      .app
        (VExpr.appN
          (.bvar
            (gen.familyCount - 1 - view.selection.family.view.ordinal +
              gen.minorCount +
              (gen.idxTel view.selection.family).length + 1))
          (VExpr.bvarRevRange 1
            (gen.idxTel view.selection.family).length))
        (.bvar 0)

/-- Restored selected-family major cursor before parameter, motive, or minor
specialization. -/
def restoredProjectionRecursorMajorTail
    (view : VRestoredBlockStructureView)
    (fieldSort : VLevel) (levels : List VLevel) : VExpr :=
  (view.nested.restoreRec view.projectionRecursorMajorTail).instL
    (view.flatView.projectionLevels fieldSort levels)

/-- Restored complete minor telescope immediately after the motive segment. -/
def restoredProjectionRecursorMinorTail
    (view : VRestoredBlockStructureView)
    (fieldSort : VLevel) (levels : List VLevel) : VExpr :=
  (view.nested.restoreRec
    (VExpr.forallN view.nested.generation.minorTypes
      view.projectionRecursorMajorTail)).instL
        (view.flatView.projectionLevels fieldSort levels)

/-- The selected-family major cursor after source parameters and all motives
have been specialized, but before the minor inventory is consumed. -/
def operationalProjectionRecursorMajorTail
    (view : VRestoredBlockStructureView)
    (fieldSort : VLevel) (levels : List VLevel)
    (params motives : List VExpr) : VExpr :=
  let gen := view.nested.generation
  ((view.restoredProjectionRecursorMajorTail fieldSort levels).instRevAt
    params (gen.familyCount + gen.minorCount)).instRevAt motives
      gen.minorCount

/-- Consuming the complete restored minor inventory exposes the literal
selected-family major binder and the selected operational motive. -/
theorem operationalProjectionRecursorMajorTail_instRev
    (view : VRestoredBlockStructureView)
    (fieldSort : VLevel) (levels : List VLevel)
    (hlevelsLength : levels.length = view.uvars)
    (params motives minors : List VExpr)
    (hparamsLength : params.length = view.nparams)
    (hmotivesLength : motives.length =
      view.nested.generation.familyCount)
    (hminorsLength : minors.length =
      view.nested.generation.minorCount)
    {typeFn : VExpr}
    (selectedMotive :
      motives[view.selection.family.view.ordinal]? = some typeFn) :
    (view.operationalProjectionRecursorMajorTail fieldSort levels
      params motives).instRev minors =
      .forallE (view.structureType levels params)
        (.app typeFn.lift (.bvar 0)) := by
  let gen := view.nested.generation
  let projectionLevels :=
    view.flatView.projectionLevels fieldSort levels
  unfold operationalProjectionRecursorMajorTail
  unfold restoredProjectionRecursorMajorTail
  dsimp only
  have hidxTel : gen.idxTel view.selection.family = [] := by
    unfold BlockGenerationChecked.idxTel
    have raw := view.flatView.raw_indices_eq
    change view.selection.family.rawIndices
      view.nested.elim.flat.nparams = [] at raw
    rw [raw]
    rfl
  dsimp only [projectionRecursorMajorTail]
  rw [hidxTel]
  simp only [VExpr.liftTelN, VExpr.forallN, VExpr.bvarRevRange,
    List.length_nil, Nat.zero_add, Nat.add_zero, List.append_nil,
    VExpr.appN]
  rw [show view.selection.family.raw.name = view.name by
    exact view.flatView_name]
  rw [show view.nested.elim.flat.nparams = view.nparams by
    exact view.nested.elim.nparams_eq]
  let commonCount := gen.familyCount + gen.minorCount
  let motiveIndex := gen.familyCount - 1 -
    view.selection.family.view.ordinal + gen.minorCount + 1
  have restoredTail : view.nested.restoreRec
      (.forallE
        (VExpr.appN (.const view.name gen.sourceLevels)
          (VExpr.bvarRevRange commonCount view.nparams))
        (.app (.bvar motiveIndex) (.bvar 0))) =
      .forallE
        (VExpr.appN (.const view.name gen.sourceLevels)
          (VExpr.bvarRevRange commonCount view.nparams))
        (.app (.bvar motiveIndex) (.bvar 0)) := by
    unfold NestedBlockChecked.restoreRec
    simp only [VInductDecl.restoreExpr]
    have familyRestored :=
      view.restoreRec_sourceFamilyApp gen.sourceLevels commonCount
    unfold NestedBlockChecked.restoreRec at familyRestored
    rw [familyRestored]
    congr 1
  rw [show gen.familyCount - 1 - view.selection.family.view.ordinal +
      gen.minorCount + 1 = motiveIndex by rfl]
  rw [show gen.familyCount + gen.minorCount = commonCount by rfl]
  rw [restoredTail]
  simp only [VExpr.instL]
  rw [VExpr.instL_appN]
  simp only [VExpr.instL, VExpr.bvarRevRange_map_instL]
  have sourceLevels := view.flatView.sourceLevels_projectionLevels
    fieldSort levels (by
      simpa only [view.flatView_uvars] using hlevelsLength)
  have sourceLevels' :
      gen.sourceLevels.map (VLevel.inst projectionLevels) = levels := by
    simpa only [gen, projectionLevels,
      VRestoredBlockStructureView.flatView] using sourceLevels
  rw [sourceLevels']
  rw [VExpr.instRevAt_forallE_projection,
    VExpr.instRevAt_forallE_projection,
    VExpr.instRev_forallE_projection]
  have combineAt (expression : VExpr) (offset : Nat) :
      ((expression.instRevAt params (offset + commonCount)).instRevAt
          motives (offset + gen.minorCount)).instRevAt minors offset =
        expression.instRevAt (params ++ motives ++ minors) offset := by
    rw [show offset + commonCount =
        offset + (motives ++ minors).length by
      simp [commonCount, gen, hmotivesLength, hminorsLength]]
    rw [show offset + gen.minorCount = offset + minors.length by
      rw [hminorsLength]]
    rw [← VExpr.instRevAt_append, ← VExpr.instRevAt_append,
      List.append_assoc]
  rw [← VExpr.instRevAt_zero]
  rw [show commonCount = 0 + commonCount by omega,
    show gen.minorCount = 0 + gen.minorCount by omega,
    combineAt]
  simp only [Nat.zero_add]
  rw [show commonCount + 1 = 1 + commonCount by omega,
    show gen.minorCount + 1 = 1 + gen.minorCount by omega,
    combineAt]
  rw [List.append_assoc]
  have suffixLength : (motives ++ minors).length = commonCount := by
    simp [commonCount, gen, hmotivesLength, hminorsLength]
  have paramsRange := VExpr.map_instRevAt_bvarRevRange_prefix
    params (motives ++ minors) 0
  rw [hparamsLength, suffixLength] at paramsRange
  simp only [Nat.zero_add] at paramsRange
  rw [VExpr.instRevAt_appN_projection,
    VExpr.instRevAt_closedN (params ++ (motives ++ minors)) (by trivial),
    paramsRange]
  simp only [VExpr.liftN_zero, List.map_id']
  change (view.structureType levels params).forallE _ = _
  have familyOrdinalLt : view.selection.family.view.ordinal <
      motives.length := by
    rw [hmotivesLength]
    simpa [gen, VRestoredBlockStructureView.flatView] using
      view.flatView.family_ordinal_lt
  have motiveAppend :
      (params ++ motives ++ minors)[params.length +
        view.selection.family.view.ordinal]? = some typeFn := by
    rw [getElem?_stack_mid params motives minors (by omega)
      (by simpa using familyOrdinalLt)]
    rw [Nat.add_sub_cancel_left, selectedMotive]
  have motiveAppend' :
      (params ++ (motives ++ minors))[params.length +
        view.selection.family.view.ordinal]? = some typeFn := by
    simpa only [List.append_assoc] using motiveAppend
  have commonLength : (params ++ (motives ++ minors)).length =
      params.length + gen.familyCount + gen.minorCount := by
    simp [gen, hmotivesLength, hminorsLength, Nat.add_assoc]
  have motivePosition : motiveIndex =
      1 + ((params ++ (motives ++ minors)).length - 1 -
        (params.length + view.selection.family.view.ordinal)) := by
    rw [commonLength]
    have ordinalLt : view.selection.family.view.ordinal <
        gen.familyCount := by
      simpa [gen, VRestoredBlockStructureView.flatView] using
        view.flatView.family_ordinal_lt
    dsimp only [motiveIndex]
    omega
  rw [VExpr.instRevAt_app_projection, motivePosition]
  rw [VExpr.instRevAt_bvar_rev_getElem?
    (params ++ (motives ++ minors)) motiveAppend' 1]
  rw [VExpr.instRevAt_closedN (params ++ (motives ++ minors))
    (C := .bvar 0) (k := 1) (by trivial)]

/-- The restored generated motive telescope specializes to the progressive
weakening of the exact per-family operational motive domains. -/
theorem restoredMotiveBinders_specialize
    (view : VRestoredBlockStructureView)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    (fieldSort : VLevel) (levels : List VLevel)
    (params : List VExpr) :
    let gen := view.nested.generation
    let projectionLevels := view.flatView.projectionLevels fieldSort levels
    ((((gen.motiveTypes.map view.nested.restoreRec).map
        (VExpr.instL projectionLevels)).zipIdx.map fun entry =>
          entry.1.instRevAt params entry.2)) =
      ((view.operationalProjectionMotiveTypes fieldSort levels params).zipIdx.map
        fun entry => entry.1.liftN entry.2) := by
  let gen := view.nested.generation
  let projectionLevels := view.flatView.projectionLevels fieldSort levels
  dsimp only
  apply List.ext_getElem?
  intro index
  simp only [List.getElem?_map, List.getElem?_zipIdx]
  rw [show gen.motiveTypes =
      gen.motiveTypesAux gen.families 0 from rfl,
    gen.motiveTypesAux_getElem?]
  simp only [operationalProjectionMotiveTypes, List.getElem?_map]
  cases familyFound : gen.families[index]? with
  | none => simp [familyFound]
  | some family =>
      simp only [familyFound, Option.map_some]
      congr 1
      simp only [Nat.zero_add]
      change
        ((view.nested.restoreRec
          ((gen.motiveType family).liftN index)).instL projectionLevels
            |>.instRevAt params index) =
          ((view.nested.restoreRecAt projectionLevels
            ((gen.motiveType family).instL projectionLevels)).instRev
              params).liftN index
      rw [view.nested.restoreRec_instL, VExpr.instL_liftN,
        ← view.nested.restoreRecAt_liftN closed,
        VExpr.liftN_instRevAt_same]

private theorem restoredGeneratedProjectionMinorType_lift_specialize
    (view : VRestoredBlockStructureView)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    (constructor : NormalizedBlockCtor)
    (fieldSort : VLevel) (levels : List VLevel)
    (params motives : List VExpr) (index : Nat) :
    (((view.nested.restoreRec
      ((view.nested.generation.minorType constructor).liftN index)).instL
        (view.flatView.projectionLevels fieldSort levels)).instRevAt params
          (view.nested.generation.familyCount + index)).instRevAt motives
            index =
      (((view.nested.restoreRecAt
        (view.flatView.projectionLevels fieldSort levels)
        ((view.nested.generation.minorType constructor).instL
          (view.flatView.projectionLevels fieldSort levels))).instRevAt params
            view.nested.generation.familyCount).instRev motives).liftN index := by
  rw [view.nested.restoreRec_instL, VExpr.instL_liftN,
    ← view.nested.restoreRecAt_liftN closed,
    VExpr.liftN_instRevAt_shift, VExpr.liftN_instRevAt_same]

/-- After parameters and every restored motive are consumed, the restored
generated minor telescope is the progressive weakening of the exact
per-constructor operational minor domains. -/
theorem restoredMinorBinders_specialize
    (view : VRestoredBlockStructureView)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    (fieldSort : VLevel) (levels : List VLevel)
    (params motives : List VExpr) :
    let gen := view.nested.generation
    let projectionLevels := view.flatView.projectionLevels fieldSort levels
    let restoredMinorBinders :=
      (gen.minorTypes.map view.nested.restoreRec).map
        (VExpr.instL projectionLevels)
    (((restoredMinorBinders.zipIdx gen.familyCount).map fun entry =>
        entry.1.instRevAt params entry.2).zipIdx.map fun entry =>
          entry.1.instRevAt motives entry.2) =
      ((view.operationalProjectionMinorTypes fieldSort levels
        params motives).zipIdx.map fun entry => entry.1.liftN entry.2) := by
  let gen := view.nested.generation
  let projectionLevels := view.flatView.projectionLevels fieldSort levels
  let restoredMinorBinders :=
    (gen.minorTypes.map view.nested.restoreRec).map
      (VExpr.instL projectionLevels)
  dsimp only
  apply List.ext_getElem?
  intro index
  simp only [List.getElem?_map, List.getElem?_zipIdx]
  rw [show gen.minorTypes =
      gen.minorTypesAux gen.flatCtors 0 from rfl,
    gen.minorTypesAux_getElem?]
  simp only [operationalProjectionMinorTypes, List.getElem?_map]
  cases constructorFound : gen.flatCtors[index]? with
  | none => simp [constructorFound]
  | some constructor =>
      simp only [constructorFound, Option.map_some]
      exact congrArg some <| by
        simpa using restoredGeneratedProjectionMinorType_lift_specialize
          view closed constructor fieldSort levels params motives index

/-- Every operational base motive domain retains the generated motive's
index-telescope/major-binder shape.  Restoration may change the concrete
index and major expressions, but cannot change the terminal motive sort. -/
theorem operationalProjectionMotiveTypes_getElem?_shape
    (view : VRestoredBlockStructureView)
    (fieldSort : VLevel) (levels : List VLevel)
    (params : List VExpr) (family : NormalizedFamily)
    (hfamily : family ∈ view.nested.generation.families)
    (hmotiveLevel : view.nested.generation.motiveLevel.inst
      (view.flatView.projectionLevels fieldSort levels) = fieldSort) :
    ∃ binders majorDomain,
      (view.operationalProjectionMotiveTypes fieldSort levels params
        )[family.view.ordinal]? =
        some (VExpr.forallN binders
          (.forallE majorDomain (.sort fieldSort))) := by
  let gen := view.nested.generation
  let projectionLevels := view.flatView.projectionLevels fieldSort levels
  let entries := view.nested.recEntries.map (·.instL projectionLevels)
  let indicesAt := (gen.idxTel family).map (VExpr.instL projectionLevels)
  let restoredIndices := indicesAt.map
    (VInductDecl.restoreExpr entries view.nested.recMap)
  let binders := restoredIndices.zipIdx.map fun entry =>
    entry.1.instRevAt params entry.2
  let familyApp := VExpr.appN
    (.const family.raw.name gen.sourceLevels)
    (VExpr.bvarRevRange (gen.idxTel family).length
        view.nested.elim.flat.nparams ++
      VExpr.bvarRevRange 0 (gen.idxTel family).length)
  let majorDomain :=
    (VInductDecl.restoreExpr entries view.nested.recMap
      (familyApp.instL projectionLevels)).instRevAt params
        restoredIndices.length
  have motiveShape :
      (view.nested.restoreRecAt projectionLevels
        ((gen.motiveType family).instL projectionLevels)).instRev params =
      VExpr.forallN binders
        (.forallE majorDomain (.sort fieldSort)) := by
    unfold BlockGenerationChecked.motiveType
    rw [VExpr.instL_forallN]
    unfold NestedBlockChecked.restoreRecAt
    rw [VInductDecl.restoreExpr_forallN,
      VExpr.instRev_forallN_projection]
    change VExpr.forallN binders _ = _
    congr 1
    simp only [VExpr.instL, VInductDecl.restoreExpr,
      VExpr.instRevAt_forallE_projection]
    rw [hmotiveLevel]
    change VExpr.forallE majorDomain
      ((VExpr.sort fieldSort).instRevAt params
        (restoredIndices.length + 1)) = _
    rw [VExpr.instRevAt_closedN params
      (C := VExpr.sort fieldSort) (by trivial)]
  rw [operationalProjectionMotiveTypes, List.getElem?_map,
    gen.family_getElem?_ordinal hfamily]
  exact ⟨binders, majorDomain, congrArg some motiveShape⟩

/-- Inserting the projector's fresh major binder before runtime parameter
specialization gives the same restored motive domain as specializing the
restored generated domain directly with lifted runtime parameters.  The
closedness premise is discharged from the registered recursor type by the
semantic spine construction. -/
theorem restoredProjectionMotiveType_eq
    (view : VRestoredBlockStructureView)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    (family : NormalizedFamily) (fieldSort : VLevel)
    (levels : List VLevel) (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (hmotiveLevel : view.nested.generation.motiveLevel.inst
      (view.flatView.projectionLevels fieldSort levels) = fieldSort)
    (baseClosed :
      (view.nested.restoreRecAt
        (view.flatView.projectionLevels fieldSort levels)
        ((view.nested.generation.motiveType family).instL
          (view.flatView.projectionLevels fieldSort levels))).ClosedN
        view.nparams) :
    let projectionLevels := view.flatView.projectionLevels fieldSort levels
    let formalParams := VExpr.bvarRevRange 0 view.nparams
    let flatParamsMajor := formalParams.map (VExpr.liftN 1)
    let paramsMajor := params.map (VExpr.liftN 1)
    (view.nested.restoreRecAt projectionLevels
        (view.flatView.projectionMotiveType family fieldSort levels
          flatParamsMajor)).instRevAt params 1 =
      (view.nested.restoreRecAt projectionLevels
        ((view.nested.generation.motiveType family).instL
          projectionLevels)).instRev paramsMajor := by
  let projectionLevels := view.flatView.projectionLevels fieldSort levels
  let formalParams := VExpr.bvarRevRange 0 view.nparams
  let flatParamsMajor := formalParams.map (VExpr.liftN 1)
  let paramsMajor := params.map (VExpr.liftN 1)
  let generatedDomain :=
    (view.nested.generation.motiveType family).instL projectionLevels
  let restoredDomain := view.nested.restoreRecAt projectionLevels
    generatedDomain
  dsimp only
  have restoredDomainClosedN : restoredDomain.ClosedN view.nparams := by
    simpa [restoredDomain, generatedDomain, projectionLevels] using baseClosed
  have flatParamsMajorEq : flatParamsMajor =
      VExpr.bvarRevRange 1 view.nparams := by
    unfold flatParamsMajor formalParams
    rw [VExpr.bvarRevRange_liftN_low]
  have flatDomainEq : generatedDomain.instRev flatParamsMajor =
      view.flatView.projectionMotiveType family fieldSort levels
        flatParamsMajor := by
    simpa [generatedDomain, projectionLevels,
      VRestoredBlockStructureView.flatView] using
      view.flatView.motiveType_specialize_exact family fieldSort levels
        (by simpa only [view.flatView_uvars] using hlevelsLength)
        flatParamsMajor (by
          simp [flatParamsMajor, formalParams, view.flatView_nparams])
        hmotiveLevel
  have formalInert : ∀ argument ∈ flatParamsMajor,
      RestoreInert
        (view.nested.recEntries.map (·.instL projectionLevels))
        view.nested.recMap argument := by
    intro argument member
    rw [flatParamsMajorEq] at member
    obtain ⟨offset, rfl, -, -⟩ := VExpr.mem_bvarRevRange member
    intro name present
    simp [VExpr.hasConst] at present
  have restoreFormal := view.nested.restoreRecAt_instRevAt closed
    projectionLevels generatedDomain flatParamsMajor 0 formalInert
  have restoredFlatDomain :
      view.nested.restoreRecAt projectionLevels
          (view.flatView.projectionMotiveType family fieldSort levels
            flatParamsMajor) = restoredDomain.lift := by
    have flatDomainEq' : generatedDomain.instRevAt flatParamsMajor 0 =
        view.flatView.projectionMotiveType family fieldSort levels
          flatParamsMajor := by
      simpa [VExpr.instRevAt_zero] using flatDomainEq
    rw [← flatDomainEq']
    rw [← restoreFormal]
    rw [flatParamsMajorEq]
    exact VExpr.instRevAt_bvarRevRange_eq_liftN restoredDomain 1
      view.nparams 0 (by simpa using restoredDomainClosedN)
  rw [restoredFlatDomain, VExpr.liftN_instRevAt_same]
  have restoredDomainClosed : restoredDomain.ClosedN params.length := by
    simpa [hparamsLength] using restoredDomainClosedN
  have directLift : restoredDomain.instRev paramsMajor =
      (restoredDomain.instRev params).lift := by
    have lifted := VExpr.liftN_instRevAt restoredDomain params 0 0 1
    simp only [Nat.zero_add] at lifted
    rw [restoredDomainClosed.liftN_eq (Nat.le_refl params.length)] at lifted
    simpa [paramsMajor, VExpr.instRevAt_zero, VExpr.liftN] using lifted.symm
  exact directLift.symm

/-- Restoring a flattened nonselected motive preserves the exact parallel
lambda/Pi telescope.  Its body is the restored major-local dummy carrier,
while its type is the corresponding operational generated motive domain. -/
theorem restoredIdentityMotiveWith_shape_exact
    (view : VRestoredBlockStructureView)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    (family : NormalizedFamily) (fieldSort : VLevel)
    (levels : List VLevel) (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (hmotiveLevel : view.nested.generation.motiveLevel.inst
      (view.flatView.projectionLevels fieldSort levels) = fieldSort)
    (flatDummyType dummyType : VExpr)
    (baseClosed :
      (view.nested.restoreRecAt
        (view.flatView.projectionLevels fieldSort levels)
        ((view.nested.generation.motiveType family).instL
          (view.flatView.projectionLevels fieldSort levels))).ClosedN
        view.nparams)
    (dummyEq :
      (view.nested.restoreRecAt
        (view.flatView.projectionLevels fieldSort levels)
        flatDummyType).instRevAt params 1 = dummyType) :
    let projectionLevels := view.flatView.projectionLevels fieldSort levels
    let formalParams := VExpr.bvarRevRange 0 view.nparams
    let flatParamsMajor := formalParams.map (VExpr.liftN 1)
    let paramsMajor := params.map (VExpr.liftN 1)
    ∃ binders majorDomain,
      binders.length = (family.rawIndices view.nparams).length ∧
      (view.nested.restoreRecAt projectionLevels
        (view.flatView.identityMotiveWith family levels flatParamsMajor
          flatDummyType)).instRevAt params 1 =
        VExpr.lamN binders
          (.lam majorDomain (dummyType.liftN (binders.length + 1))) ∧
      (view.nested.restoreRecAt projectionLevels
        ((view.nested.generation.motiveType family).instL
          projectionLevels)).instRev paramsMajor =
        VExpr.forallN binders
          (.forallE majorDomain (.sort fieldSort)) := by
  let projectionLevels := view.flatView.projectionLevels fieldSort levels
  let formalParams := VExpr.bvarRevRange 0 view.nparams
  let flatParamsMajor := formalParams.map (VExpr.liftN 1)
  let paramsMajor := params.map (VExpr.liftN 1)
  let flatIndices :=
    view.flatView.specializedIndices family levels flatParamsMajor
  let flatFamilyApp := VExpr.appN (.const family.raw.name levels)
    (flatParamsMajor.map (VExpr.liftN flatIndices.length) ++
      VExpr.bvarRevRange 0 flatIndices.length)
  let restoredIndices := flatIndices.map
    (view.nested.restoreRecAt projectionLevels)
  let binders := restoredIndices.zipIdx 1 |>.map fun entry =>
    entry.1.instRevAt params entry.2
  let majorDomain :=
    (view.nested.restoreRecAt projectionLevels flatFamilyApp).instRevAt
      params (1 + restoredIndices.length)
  dsimp only
  have domainBridge := view.restoredProjectionMotiveType_eq closed family
    fieldSort levels hlevelsLength params hparamsLength hmotiveLevel baseClosed
  dsimp only at domainBridge
  have flatDomainShape :
      (view.nested.restoreRecAt projectionLevels
        (view.flatView.projectionMotiveType family fieldSort levels
          flatParamsMajor)).instRevAt params 1 =
        VExpr.forallN binders
          (.forallE majorDomain (.sort fieldSort)) := by
    unfold VBlockStructureView.projectionMotiveType
    change (view.nested.restoreRecAt projectionLevels
      (VExpr.forallN flatIndices
        (.forallE flatFamilyApp (.sort fieldSort)))).instRevAt params 1 = _
    unfold NestedBlockChecked.restoreRecAt
    rw [VInductDecl.restoreExpr_forallN,
      VExpr.instRevAt_forallN_projection]
    change VExpr.forallN binders _ = _
    congr 1
    simp only [VInductDecl.restoreExpr]
    rw [VExpr.instRevAt_forallE_projection]
    change VExpr.forallE majorDomain
      ((VExpr.sort fieldSort).instRevAt params
        (1 + restoredIndices.length + 1)) = _
    rw [VExpr.instRevAt_closedN params
      (C := VExpr.sort fieldSort) (by trivial)]
  have operationalShape :
      (view.nested.restoreRecAt projectionLevels
        ((view.nested.generation.motiveType family).instL
          projectionLevels)).instRev paramsMajor =
        VExpr.forallN binders
          (.forallE majorDomain (.sort fieldSort)) :=
    domainBridge.symm.trans flatDomainShape
  have bindersLength :
      binders.length = (family.rawIndices view.nparams).length := by
    simp [binders, restoredIndices, flatIndices,
      VBlockStructureView.specializedIndices,
      VRestoredBlockStructureView.flatView_nparams]
  refine ⟨binders, majorDomain, bindersLength, ?_, operationalShape⟩
  unfold VBlockStructureView.identityMotiveWith
  change (view.nested.restoreRecAt projectionLevels
    (VExpr.lamN flatIndices
      (.lam flatFamilyApp
        (flatDummyType.liftN (flatIndices.length + 1))))).instRevAt
          params 1 = _
  unfold NestedBlockChecked.restoreRecAt
  rw [VInductDecl.restoreExpr_lamN,
    VExpr.instRevAt_lamN_projection]
  change VExpr.lamN binders _ = _
  congr 1
  simp only [VInductDecl.restoreExpr]
  rw [VExpr.instRevAt_lam_projection]
  congr 1
  rw [← VInductDecl.restoreExpr_liftN
    (view.nested.recEntries.map (·.instL projectionLevels))
    (closed.instL projectionLevels) view.nested.recMap flatDummyType
    (flatIndices.length + 1) 0]
  simp only [List.length_map]
  rw [show 1 + flatIndices.length + 1 =
    1 + (flatIndices.length + 1) by omega]
  rw [VExpr.liftN_instRevAt_shift]
  have dummyEq' :
      (VInductDecl.restoreExpr
        (view.nested.recEntries.map (·.instL projectionLevels))
        view.nested.recMap flatDummyType).instRevAt params 1 = dummyType := by
    simpa [projectionLevels, NestedBlockChecked.restoreRecAt] using dummyEq
  rw [dummyEq']
  congr 2
  simp [binders, restoredIndices]

/-- Compatibility projection of `restoredIdentityMotiveWith_shape_exact`
that exposes the parallel lambda/Pi syntax without its raw index count. -/
theorem restoredIdentityMotiveWith_shape
    (view : VRestoredBlockStructureView)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    (family : NormalizedFamily) (fieldSort : VLevel)
    (levels : List VLevel) (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (hmotiveLevel : view.nested.generation.motiveLevel.inst
      (view.flatView.projectionLevels fieldSort levels) = fieldSort)
    (flatDummyType dummyType : VExpr)
    (baseClosed :
      (view.nested.restoreRecAt
        (view.flatView.projectionLevels fieldSort levels)
        ((view.nested.generation.motiveType family).instL
          (view.flatView.projectionLevels fieldSort levels))).ClosedN
        view.nparams)
    (dummyEq :
      (view.nested.restoreRecAt
        (view.flatView.projectionLevels fieldSort levels)
        flatDummyType).instRevAt params 1 = dummyType) :
    let projectionLevels := view.flatView.projectionLevels fieldSort levels
    let formalParams := VExpr.bvarRevRange 0 view.nparams
    let flatParamsMajor := formalParams.map (VExpr.liftN 1)
    let paramsMajor := params.map (VExpr.liftN 1)
    ∃ binders majorDomain,
      (view.nested.restoreRecAt projectionLevels
        (view.flatView.identityMotiveWith family levels flatParamsMajor
          flatDummyType)).instRevAt params 1 =
        VExpr.lamN binders
          (.lam majorDomain (dummyType.liftN (binders.length + 1))) ∧
      (view.nested.restoreRecAt projectionLevels
        ((view.nested.generation.motiveType family).instL
          projectionLevels)).instRev paramsMajor =
        VExpr.forallN binders
          (.forallE majorDomain (.sort fieldSort)) := by
  obtain ⟨binders, majorDomain, _, motiveShape, domainShape⟩ :=
    view.restoredIdentityMotiveWith_shape_exact closed family fieldSort levels
      hlevelsLength params hparamsLength hmotiveLevel flatDummyType dummyType
        baseClosed dummyEq
  exact ⟨binders, majorDomain, motiveShape, domainShape⟩

/-- The selected family's restored operational motive domain is literally
the public source-structure domain under the fresh major binder. -/
theorem selectedRestoredMotiveType_eq
    (view : VRestoredBlockStructureView)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    (fieldSort : VLevel) (levels : List VLevel)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (hmotiveLevel : view.nested.generation.motiveLevel.inst
      (view.flatView.projectionLevels fieldSort levels) = fieldSort)
    (baseClosed :
      (view.nested.restoreRecAt
        (view.flatView.projectionLevels fieldSort levels)
        ((view.nested.generation.motiveType
          view.selection.family).instL
            (view.flatView.projectionLevels fieldSort levels))).ClosedN
        view.nparams) :
    let projectionLevels := view.flatView.projectionLevels fieldSort levels
    let paramsMajor := params.map (VExpr.liftN 1)
    (view.nested.restoreRecAt projectionLevels
      ((view.nested.generation.motiveType view.selection.family).instL
        projectionLevels)).instRev paramsMajor =
      .forallE (view.structureType levels paramsMajor) (.sort fieldSort) := by
  let projectionLevels := view.flatView.projectionLevels fieldSort levels
  let formalParams := VExpr.bvarRevRange 0 view.nparams
  let flatParamsMajor := formalParams.map (VExpr.liftN 1)
  let paramsMajor := params.map (VExpr.liftN 1)
  dsimp only
  have domainBridge := view.restoredProjectionMotiveType_eq closed
    view.selection.family fieldSort levels hlevelsLength params hparamsLength
      hmotiveLevel baseClosed
  dsimp only at domainBridge
  rw [← domainBridge]
  have flatParamsMajorEq : flatParamsMajor =
      VExpr.bvarRevRange 1 view.nparams := by
    unfold flatParamsMajor formalParams
    rw [VExpr.bvarRevRange_liftN_low]
  have restoredStructureMajor :
      view.nested.restoreRecAt projectionLevels
          (view.flatView.structureType levels flatParamsMajor) =
        view.structureType levels flatParamsMajor := by
    have flatStructureLift :
        view.flatView.structureType levels flatParamsMajor =
          (view.flatView.structureType levels formalParams).lift := by
      simpa [flatParamsMajor, VExpr.liftN] using
        (view.flatView.structureType_liftN levels formalParams 1 0).symm
    have structureLift :
        (view.structureType levels formalParams).lift =
          view.structureType levels flatParamsMajor := by
      simpa [flatParamsMajor, VExpr.liftN] using
        view.structureType_liftN levels formalParams 1 0
    calc
      view.nested.restoreRecAt projectionLevels
          (view.flatView.structureType levels flatParamsMajor) =
          view.nested.restoreRecAt projectionLevels
            ((view.flatView.structureType levels formalParams).lift) := by
        rw [flatStructureLift]
      _ = (view.nested.restoreRecAt projectionLevels
          (view.flatView.structureType levels formalParams)).lift := by
        exact (view.nested.restoreRecAt_liftN closed projectionLevels
          (view.flatView.structureType levels formalParams) 1 0).symm
      _ = (view.structureType levels formalParams).lift := by
        rw [view.restoreRecAt_flatStructureType_bvarRevRange fieldSort levels]
      _ = view.structureType levels flatParamsMajor := structureLift
  unfold VBlockStructureView.projectionMotiveType
  have flatIndicesEmpty :
      view.flatView.specializedIndices view.selection.family levels
        flatParamsMajor = [] := by
    simpa [VRestoredBlockStructureView.flatView] using
      view.flatView.specializedIndices_selected levels flatParamsMajor
  rw [flatIndicesEmpty]
  simp only [VExpr.forallN, List.length_nil, VExpr.liftN_zero,
    VExpr.bvarRevRange, List.append_nil]
  rw [List.map_id']
  rw [show VExpr.appN (.const view.selection.family.raw.name levels)
      flatParamsMajor = view.flatView.structureType levels flatParamsMajor by
    simp [VBlockStructureView.structureType,
      VRestoredBlockStructureView.flatView]]
  change (view.nested.restoreRecAt projectionLevels
    (.forallE (view.flatView.structureType levels flatParamsMajor)
      (.sort fieldSort))).instRevAt params 1 = _
  unfold NestedBlockChecked.restoreRecAt
  simp only [VInductDecl.restoreExpr]
  rw [VExpr.instRevAt_forallE_projection]
  change VExpr.forallE
      ((view.nested.restoreRecAt projectionLevels
        (view.flatView.structureType levels flatParamsMajor)).instRevAt
          params 1)
      ((VExpr.sort fieldSort).instRevAt params 2) = _
  rw [restoredStructureMajor]
  unfold structureType
  rw [VExpr.instRevAt_appN_projection]
  rw [VExpr.instRevAt_closedN params
    (C := VExpr.const view.name levels) (by trivial)]
  rw [VExpr.instRevAt_closedN params
    (C := VExpr.sort fieldSort) (by trivial)]
  rw [flatParamsMajorEq]
  have paramsMapped :
      (VExpr.bvarRevRange 1 view.nparams).map
          (fun expression => expression.instRevAt params 1) =
        paramsMajor := by
    rw [← hparamsLength]
    exact VExpr.map_instRevAt_bvarRevRange params 1
  rw [paramsMapped]

/-- Semantic arguments substituted while walking through a restored
dependent-field telescope.  These are built from the restored operational
programs, never from the flattened templates. -/
def operationalProjectionArgs (view : VRestoredBlockStructureView)
    (levels : List VLevel) (params : List VExpr) (count : Nat)
    (major : VExpr) : List VExpr :=
  (view.operationalProjectionCodes levels params).take count |>.map
    fun code => .app code.projector major

/-- The restored source constructor applied to the canonical parameter and
field variables in the complete restored field context. -/
def projectionConstructorApp (view : VRestoredBlockStructureView)
    (levels : List VLevel) (params fields : List VExpr) : VExpr :=
  VExpr.appN (.const view.constructorName levels)
    (params.map (VExpr.liftN fields.length) ++
      VExpr.bvarRevRange 0 fields.length)

/-- Rebuild the restored source structure from its operational projections. -/
def operationalEtaRebuild (view : VRestoredBlockStructureView)
    (levels : List VLevel) (params : List VExpr) (major : VExpr) : VExpr :=
  VExpr.appN (.const view.constructorName levels)
    (params ++ view.operationalProjectionArgs levels params
      (view.specializedFields levels params).length major)

theorem operationalProjectionArgs_length
    (view : VRestoredBlockStructureView)
    (levels : List VLevel) (params : List VExpr) (count : Nat)
    (major : VExpr)
    (bound : count ≤ (view.operationalProjectionCodes levels params).length) :
    (view.operationalProjectionArgs levels params count major).length =
      count := by
  simp only [operationalProjectionArgs, List.length_map, List.length_take,
    Nat.min_eq_left bound]

theorem operationalProjectionArgs_succ
    (view : VRestoredBlockStructureView)
    (levels : List VLevel) (params : List VExpr) (count : Nat)
    (major : VExpr) {code : VStructureView.ProjectionCode}
    (found : (view.operationalProjectionCodes levels params)[count]? =
      some code) :
    view.operationalProjectionArgs levels params (count + 1) major =
      view.operationalProjectionArgs levels params count major ++
        [.app code.projector major] := by
  simp only [operationalProjectionArgs, List.take_add_one, found,
    Option.toList_some, List.map_append, List.map_singleton]

/-- Specializing the canonical flattened template recovers the exact
runtime-parametric flattened inventory. -/
theorem flatProjectionCodeTemplates_instRevAt
    {env : VEnv} (view : VRestoredBlockStructureView)
    (flatLayout : view.flatView.LayoutWF env)
    (levels : List VLevel) (params : List VExpr)
    (paramsLength : params.length = view.nparams) :
    (view.flatProjectionCodeTemplates levels).map
        (fun code => code.instRevAt params 0) =
      view.flatView.operationalProjectionCodes levels params := by
  unfold flatProjectionCodeTemplates
  rw [← view.flatView_nparams]
  exact flatLayout.operationalProjectionCodes_bvarRevRange_instRevAt
    levels params (by simpa only [view.flatView_nparams] using paramsLength)

/-- A flattened declaration-time template at an exact source index maps to
the restored-and-specialized code at that same index. -/
theorem operationalProjectionCodes_get?_of_flat
    (view : VRestoredBlockStructureView)
    (levels : List VLevel) (params : List VExpr)
    {index : Nat} {code : VStructureView.ProjectionCode}
    (found : (view.flatProjectionCodeTemplates levels)[index]? =
      some code) :
    (view.operationalProjectionCodes levels params)[index]? =
      some ((view.restoreProjectionCodeAt levels code).instRevAt params 0) := by
  simp [operationalProjectionCodes, restoredProjectionCodeTemplates,
    List.getElem?_map, found]

/-- Every restored runtime code retains an exact flattened producer template
at the same source index. -/
theorem operationalProjectionCodes_get?_exists_flat
    (view : VRestoredBlockStructureView)
    (levels : List VLevel) (params : List VExpr)
    {index : Nat} {code : VStructureView.ProjectionCode}
    (found : (view.operationalProjectionCodes levels params)[index]? =
      some code) :
    ∃ flatTemplate,
      (view.flatProjectionCodeTemplates levels)[index]? =
        some flatTemplate ∧
      (view.restoreProjectionCodeAt levels flatTemplate).instRevAt params 0 =
        code := by
  unfold operationalProjectionCodes at found
  unfold restoredProjectionCodeTemplates at found
  simp only [List.getElem?_map] at found
  cases flatFound : (view.flatProjectionCodeTemplates levels)[index]? with
  | none => simp [flatFound] at found
  | some flatTemplate =>
      simp only [flatFound, Option.map_some] at found
      exact ⟨flatTemplate, rfl, Option.some.inj found⟩

/-- The selected motive carried by a restored projector is literally the
lifted runtime type function.  Restoration is performed on the formal
template before source parameters are specialized, so the only proof
obligation is commuting restoration with lifting and lifting with the exact
parameter substitution boundary. -/
theorem operationalProjectionCodes_get?_selectedMotive
    (view : VRestoredBlockStructureView)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    (levels : List VLevel) (params : List VExpr)
    {index : Nat} {code : VStructureView.ProjectionCode}
    (found : (view.operationalProjectionCodes levels params)[index]? =
      some code) :
    ∃ flatTemplate,
      (view.flatProjectionCodeTemplates levels)[index]? =
        some flatTemplate ∧
      (view.nested.restoreRecAt
          (view.flatView.projectionLevels flatTemplate.fieldSort levels)
          flatTemplate.typeFn.lift).instRevAt params 1 =
        code.typeFn.lift := by
  obtain ⟨flatTemplate, flatFound, rfl⟩ :=
    view.operationalProjectionCodes_get?_exists_flat levels params found
  refine ⟨flatTemplate, flatFound, ?_⟩
  change
    (view.nested.restoreRecAt
        (view.flatView.projectionLevels flatTemplate.fieldSort levels)
        flatTemplate.typeFn.lift).instRevAt params 1 =
      ((view.nested.restoreRecAt
        (view.flatView.projectionLevels flatTemplate.fieldSort levels)
        flatTemplate.typeFn).instRevAt params 0).lift
  rw [← view.nested.restoreRecAt_liftN closed]
  simpa only [VExpr.instRevAt_zero, VExpr.liftN] using
    VExpr.liftN_instRevAt_same
      (view.nested.restoreRecAt
        (view.flatView.projectionLevels flatTemplate.fieldSort levels)
        flatTemplate.typeFn) params 1

/-- At the selected family position of the mutual motive inventory, the
restored and parameter-specialized flattened motive is exactly the lifted
runtime type function.  This is the list-indexed form consumed by the
restored recursor spine. -/
theorem operationalProjectionCodes_get?_selectedMotiveAt
    (view : VRestoredBlockStructureView)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    (levels : List VLevel) (params : List VExpr)
    {index : Nat} {code : VStructureView.ProjectionCode}
    (found : (view.operationalProjectionCodes levels params)[index]? =
      some code) :
    ∃ flatTemplate,
      (view.flatProjectionCodeTemplates levels)[index]? =
        some flatTemplate ∧
      flatTemplate.fieldSort = code.fieldSort ∧
      let projectionLevels :=
        view.flatView.projectionLevels code.fieldSort levels
      let formalParams := VExpr.bvarRevRange 0 view.nparams
      let flatParamsMajor := formalParams.map (VExpr.liftN 1)
      let flatTypeFnMajor := flatTemplate.typeFn.lift
      let majorBinder := VExpr.bvar 0
      let flatDummyType := VBlockStructureView.majorDummyType
        flatTypeFnMajor majorBinder
      let flatMotives := view.flatView.projectionMotivesWith levels
        flatParamsMajor flatTypeFnMajor flatDummyType
      let restoreSpecialize := fun expression =>
        (view.nested.restoreRecAt projectionLevels expression).instRevAt
          params 1
      (flatMotives.map restoreSpecialize)[view.selection.family.view.ordinal]? =
        some code.typeFn.lift := by
  obtain ⟨flatTemplate, flatFound, codeEq⟩ :=
    view.operationalProjectionCodes_get?_exists_flat levels params found
  have fieldSortEq : flatTemplate.fieldSort = code.fieldSort := by
    rw [← codeEq]
    rfl
  refine ⟨flatTemplate, flatFound, fieldSortEq, ?_⟩
  let projectionLevels :=
    view.flatView.projectionLevels code.fieldSort levels
  let formalParams := VExpr.bvarRevRange 0 view.nparams
  let flatParamsMajor := formalParams.map (VExpr.liftN 1)
  let flatTypeFnMajor := flatTemplate.typeFn.lift
  let majorBinder := VExpr.bvar 0
  let flatDummyType := VBlockStructureView.majorDummyType
    flatTypeFnMajor majorBinder
  let flatMotives := view.flatView.projectionMotivesWith levels
    flatParamsMajor flatTypeFnMajor flatDummyType
  let restoreSpecialize := fun expression =>
    (view.nested.restoreRecAt projectionLevels expression).instRevAt params 1
  dsimp only
  have selectedFlat : flatMotives[view.selection.family.view.ordinal]? =
      some flatTypeFnMajor := by
    simpa [flatMotives, flatTypeFnMajor,
      VRestoredBlockStructureView.flatView] using
      view.flatView.projectionMotivesWith_getElem?_ordinal
        view.flatView.family view.flatView.family_mem levels flatParamsMajor
          flatTypeFnMajor flatDummyType
  rw [List.getElem?_map, selectedFlat]
  simp only [Option.map_some]
  congr 1
  obtain ⟨selectedTemplate, selectedFound, selectedEq⟩ :=
    view.operationalProjectionCodes_get?_selectedMotive closed levels params
      found
  have templateEq : selectedTemplate = flatTemplate :=
    Option.some.inj (selectedFound.symm.trans flatFound)
  subst selectedTemplate
  rw [← fieldSortEq]
  exact selectedEq

/-- The dummy carrier shared by all nonselected restored motives is exactly
the major-local carrier built from the runtime type function.  In particular,
runtime parameters are substituted only after restoration, while the fresh
major binder remains fixed. -/
theorem operationalProjectionCodes_get?_dummyType
    (view : VRestoredBlockStructureView)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    (levels : List VLevel) (params : List VExpr)
    {index : Nat} {code : VStructureView.ProjectionCode}
    (found : (view.operationalProjectionCodes levels params)[index]? =
      some code) :
    ∃ flatTemplate,
      (view.flatProjectionCodeTemplates levels)[index]? =
        some flatTemplate ∧
      flatTemplate.fieldSort = code.fieldSort ∧
      let projectionLevels :=
        view.flatView.projectionLevels code.fieldSort levels
      let flatDummyType := VBlockStructureView.majorDummyType
        flatTemplate.typeFn.lift (.bvar 0)
      (view.nested.restoreRecAt projectionLevels flatDummyType).instRevAt
          params 1 =
        VBlockStructureView.majorDummyType code.typeFn.lift (.bvar 0) := by
  obtain ⟨flatTemplate, flatFound, codeEq⟩ :=
    view.operationalProjectionCodes_get?_exists_flat levels params found
  have fieldSortEq : flatTemplate.fieldSort = code.fieldSort := by
    rw [← codeEq]
    rfl
  refine ⟨flatTemplate, flatFound, fieldSortEq, ?_⟩
  dsimp only
  rw [← fieldSortEq]
  obtain ⟨flatField, flatFieldFound, flatTypeFnEq⟩ :=
    view.flatView.operationalProjectionCodes_get?_typeFn levels
      (VExpr.bvarRevRange 0 view.nparams) flatFound
  obtain ⟨selectedTemplate, selectedFound, selectedEq⟩ :=
    view.operationalProjectionCodes_get?_selectedMotive closed levels params
      found
  have templateEq : selectedTemplate = flatTemplate :=
    Option.some.inj (selectedFound.symm.trans flatFound)
  subst selectedTemplate
  let projectionLevels :=
    view.flatView.projectionLevels flatTemplate.fieldSort levels
  let entries := view.nested.recEntries.map (·.instL projectionLevels)
  have carrierRestored :
      VInductDecl.restoreExpr entries view.nested.recMap
          (.app flatTemplate.typeFn.lift (.bvar 0)) =
        .app
          (VInductDecl.restoreExpr entries view.nested.recMap
            flatTemplate.typeFn.lift)
          (.bvar 0) := by
    rw [flatTypeFnEq]
    simp [entries, VExpr.liftN, VInductDecl.restoreExpr,
      VInductDecl.restoreExpr.restoreSpine, VExpr.appHead]
  unfold VBlockStructureView.majorDummyType
  unfold NestedBlockChecked.restoreRecAt
  change (VExpr.forallE
      (VInductDecl.restoreExpr entries view.nested.recMap
        (.app flatTemplate.typeFn.lift (.bvar 0)))
      (VInductDecl.restoreExpr entries view.nested.recMap
        ((VExpr.app flatTemplate.typeFn.lift (.bvar 0)).lift))).instRevAt
        params 1 = _
  rw [← VInductDecl.restoreExpr_liftN entries
      (closed.instL projectionLevels) view.nested.recMap
      (VExpr.app flatTemplate.typeFn.lift (.bvar 0)) 1 0,
    carrierRestored, VExpr.instRevAt_forallE_projection,
    VExpr.instRevAt_app_projection]
  have bvarFixed : (VExpr.bvar 0).instRevAt params 1 = .bvar 0 :=
    VExpr.instRevAt_closedN params (by trivial)
  have selectedEq' :
      (VInductDecl.restoreExpr entries view.nested.recMap
        flatTemplate.typeFn.lift).instRevAt params 1 =
        code.typeFn.lift := by
    simpa [entries, projectionLevels, NestedBlockChecked.restoreRecAt] using
      selectedEq
  rw [bvarFixed, selectedEq']
  rw [VExpr.liftN_instRevAt_shift]
  rw [VExpr.instRevAt_app_projection, bvarFixed, selectedEq']

/-- The identity inhabitant paired with the restored dummy carrier is the
runtime major-local identity function.  As for the carrier theorem above,
the fresh major binder remains fixed while source parameters are specialized
only after restoration. -/
theorem operationalProjectionCodes_get?_dummyValue
    (view : VRestoredBlockStructureView)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    (levels : List VLevel) (params : List VExpr)
    {index : Nat} {code : VStructureView.ProjectionCode}
    (found : (view.operationalProjectionCodes levels params)[index]? =
      some code) :
    ∃ flatTemplate,
      (view.flatProjectionCodeTemplates levels)[index]? =
        some flatTemplate ∧
      flatTemplate.fieldSort = code.fieldSort ∧
      let projectionLevels :=
        view.flatView.projectionLevels code.fieldSort levels
      let flatDummyValue := VBlockStructureView.majorDummyValue
        flatTemplate.typeFn.lift (.bvar 0)
      (view.nested.restoreRecAt projectionLevels flatDummyValue).instRevAt
          params 1 =
        VBlockStructureView.majorDummyValue code.typeFn.lift (.bvar 0) := by
  obtain ⟨flatTemplate, flatFound, codeEq⟩ :=
    view.operationalProjectionCodes_get?_exists_flat levels params found
  have fieldSortEq : flatTemplate.fieldSort = code.fieldSort := by
    rw [← codeEq]
    rfl
  refine ⟨flatTemplate, flatFound, fieldSortEq, ?_⟩
  dsimp only
  rw [← fieldSortEq]
  obtain ⟨flatField, flatFieldFound, flatTypeFnEq⟩ :=
    view.flatView.operationalProjectionCodes_get?_typeFn levels
      (VExpr.bvarRevRange 0 view.nparams) flatFound
  obtain ⟨selectedTemplate, selectedFound, selectedEq⟩ :=
    view.operationalProjectionCodes_get?_selectedMotive closed levels params
      found
  have templateEq : selectedTemplate = flatTemplate :=
    Option.some.inj (selectedFound.symm.trans flatFound)
  subst selectedTemplate
  let projectionLevels :=
    view.flatView.projectionLevels flatTemplate.fieldSort levels
  let entries := view.nested.recEntries.map (·.instL projectionLevels)
  have carrierRestored :
      VInductDecl.restoreExpr entries view.nested.recMap
          (.app flatTemplate.typeFn.lift (.bvar 0)) =
        .app
          (VInductDecl.restoreExpr entries view.nested.recMap
            flatTemplate.typeFn.lift)
          (.bvar 0) := by
    rw [flatTypeFnEq]
    simp [entries, VExpr.liftN, VInductDecl.restoreExpr,
      VInductDecl.restoreExpr.restoreSpine, VExpr.appHead]
  unfold VBlockStructureView.majorDummyValue
  unfold NestedBlockChecked.restoreRecAt
  change (VExpr.lam
      (VInductDecl.restoreExpr entries view.nested.recMap
        (.app flatTemplate.typeFn.lift (.bvar 0)))
      (VInductDecl.restoreExpr entries view.nested.recMap
        (.bvar 0))).instRevAt params 1 = _
  rw [carrierRestored, VExpr.instRevAt_lam_projection]
  have bvarFixed : (VExpr.bvar 0).instRevAt params 1 = .bvar 0 :=
    VExpr.instRevAt_closedN params (by trivial)
  have selectedEq' :
      (VInductDecl.restoreExpr entries view.nested.recMap
        flatTemplate.typeFn.lift).instRevAt params 1 =
        code.typeFn.lift := by
    simpa [entries, projectionLevels, NestedBlockChecked.restoreRecAt] using
      selectedEq
  rw [VExpr.instRevAt_app_projection, bvarFixed, selectedEq']
  simp only [VInductDecl.restoreExpr]
  have bodyFixed : (VExpr.bvar 0).instRevAt params 2 = .bvar 0 := by
    exact VExpr.instRevAt_closedN params (by trivial)
  rw [bodyFixed]

/-- The dependent type function of a restored runtime code is the
specialization of the exact declaration-time restoration image of the
flattened producer template. -/
theorem operationalProjectionCodes_get?_typeFn
    (view : VRestoredBlockStructureView)
    (levels : List VLevel) (params : List VExpr)
    {index : Nat} {code : VStructureView.ProjectionCode}
    (found : (view.operationalProjectionCodes levels params)[index]? =
      some code) :
    ∃ field,
      (view.flatView.specializedFields levels
        (VExpr.bvarRevRange 0 view.nparams))[index]? = some field ∧
      code.typeFn =
        VExpr.instRevAt
          (view.nested.restoreRecAt
            (view.flatView.projectionLevels code.fieldSort levels)
            (.lam (view.flatView.structureType levels
                (VExpr.bvarRevRange 0 view.nparams))
              ((field.liftN 1 index).instRevAt
                ((view.flatProjectionCodeTemplates levels).take index |>.map
                  fun prior => .app prior.projector.lift (.bvar 0)) 0)))
          params 0 := by
  obtain ⟨flatCode, flatFound, rfl⟩ :=
    view.operationalProjectionCodes_get?_exists_flat levels params found
  obtain ⟨field, fieldFound, typeFnEq⟩ :=
    view.flatView.operationalProjectionCodes_get?_typeFn levels
      (VExpr.bvarRevRange 0 view.nparams) flatFound
  refine ⟨field, fieldFound, ?_⟩
  change (view.nested.restoreRecAt
      (view.flatView.projectionLevels flatCode.fieldSort levels)
      flatCode.typeFn).instRevAt params 0 = _
  rw [typeFnEq]
  simp [flatProjectionCodeTemplates]

/-- The restored dependent type function retains the literal public source
structure as its lambda domain.  Only its body needs the nontrivial
flattened-to-restored field transport. -/
theorem operationalProjectionCodes_get?_typeFn_domain
    (view : VRestoredBlockStructureView)
    (levels : List VLevel) (params : List VExpr)
    (hparams : params.length = view.nparams)
    {index : Nat} {code : VStructureView.ProjectionCode}
    (found : (view.operationalProjectionCodes levels params)[index]? =
      some code) :
    ∃ body, code.typeFn =
      .lam (view.structureType levels params) body := by
  obtain ⟨field, fieldFound, typeFnEq⟩ :=
    view.operationalProjectionCodes_get?_typeFn levels params found
  let projectionLevels :=
    view.flatView.projectionLevels code.fieldSort levels
  let flatBody :=
    (field.liftN 1 index).instRevAt
      ((view.flatProjectionCodeTemplates levels).take index |>.map
        fun prior => .app prior.projector.lift (.bvar 0)) 0
  let restoredBody := view.nested.restoreRecAt projectionLevels flatBody
  refine ⟨restoredBody.instRevAt params 1, ?_⟩
  rw [typeFnEq]
  change
    (VExpr.lam
      (view.nested.restoreRecAt projectionLevels
        (view.flatView.structureType levels
          (VExpr.bvarRevRange 0 view.nparams)))
      restoredBody).instRevAt params 0 = _
  rw [VExpr.instRevAt_lam_projection]
  congr 1
  rw [view.restoreRecAt_flatStructureType_bvarRevRange
    code.fieldSort levels]
  unfold structureType
  rw [VExpr.instRevAt_appN_projection]
  rw [VExpr.instRevAt_closedN params (C := .const view.name levels)
    (by trivial)]
  rw [← hparams, VExpr.map_instRevAt_bvarRevRange]
  simp

/-- Every declaration-time flattened projector has a lambda application
head.  This producer-shape fact is what permits mapped argument substitution
through restoration without requiring the recursor-bearing argument itself
to be restoration-inert. -/
theorem flatProjectionCodeTemplates_get?_projector_lam
    (view : VRestoredBlockStructureView)
    (levels : List VLevel) {index : Nat}
    {code : VStructureView.ProjectionCode}
    (found : (view.flatProjectionCodeTemplates levels)[index]? =
      some code) :
    ∃ domain body, code.projector = .lam domain body := by
  obtain ⟨fieldSort, _, _, _, projectorEq⟩ :=
    view.flatView.operationalProjectionCodes_get?_program_shape levels
      (VExpr.bvarRevRange 0 view.nparams) (by
        simpa [flatProjectionCodeTemplates] using found)
  rw [projectorEq]
  unfold VBlockStructureView.operationalProjector
  exact ⟨_, _, rfl⟩

/-- Restoring one earlier flattened projector application in any projection
universe world yields the corresponding restored template application.
Cross-field motive universes disappear from the restoration inventory, and
the lambda head prevents a new outer restoration redex. -/
theorem restoreFlatProjectionArgumentAt
    (view : VRestoredBlockStructureView)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    (levels : List VLevel) (hlevels : levels.length = view.uvars)
    (fieldSort : VLevel) {index : Nat}
    {code : VStructureView.ProjectionCode}
    (found : (view.flatProjectionCodeTemplates levels)[index]? =
      some code) :
    view.nested.restoreRecAt
        (view.flatView.projectionLevels fieldSort levels)
        (.app code.projector.lift (.bvar 0)) =
      .app (view.restoreProjectionCodeAt levels code).projector.lift
        (.bvar 0) := by
  obtain ⟨domain, body, projectorEq⟩ :=
    view.flatProjectionCodeTemplates_get?_projector_lam levels found
  have cross := view.restoreRecAt_projectionLevels_eq fieldSort
    code.fieldSort levels hlevels code.projector
  have lifted := view.nested.restoreRecAt_liftN closed
    (view.flatView.projectionLevels fieldSort levels) code.projector 1 0
  calc
    view.nested.restoreRecAt
          (view.flatView.projectionLevels fieldSort levels)
          (.app code.projector.lift (.bvar 0)) =
        .app
          (view.nested.restoreRecAt
            (view.flatView.projectionLevels fieldSort levels)
            code.projector.lift) (.bvar 0) := by
      rw [projectorEq]
      rfl
    _ = .app
        (view.nested.restoreRecAt
          (view.flatView.projectionLevels fieldSort levels)
          code.projector).lift (.bvar 0) := by
      rw [← lifted]
    _ = .app
        (view.nested.restoreRecAt
          (view.flatView.projectionLevels code.fieldSort levels)
          code.projector).lift (.bvar 0) := by
      rw [cross]
    _ = .app (view.restoreProjectionCodeAt levels code).projector.lift
        (.bvar 0) := rfl

/-- The mapped earlier-projector argument has a lambda application head and
therefore satisfies the non-constant-head premise of mapped restoration
substitution. -/
theorem restoreFlatProjectionArgumentAt_nonConst
    (view : VRestoredBlockStructureView)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    (levels : List VLevel) (hlevels : levels.length = view.uvars)
    (fieldSort : VLevel) {index : Nat}
    {code : VStructureView.ProjectionCode}
    (found : (view.flatProjectionCodeTemplates levels)[index]? =
      some code) :
    ∀ name nameLevels,
      (view.nested.restoreRecAt
        (view.flatView.projectionLevels fieldSort levels)
        (.app code.projector.lift (.bvar 0))).appHead ≠
          .const name nameLevels := by
  obtain ⟨domain, body, projectorEq⟩ :=
    view.flatProjectionCodeTemplates_get?_projector_lam levels found
  rw [view.restoreFlatProjectionArgumentAt closed levels hlevels fieldSort
    found]
  change ∀ name nameLevels,
    ((view.nested.restoreRecAt
      (view.flatView.projectionLevels code.fieldSort levels)
      code.projector).lift.app (.bvar 0)).appHead ≠
        .const name nameLevels
  rw [projectorEq]
  intro name nameLevels
  simp [NestedBlockChecked.restoreRecAt,
    restoreExpr, VExpr.lift, VExpr.liftN, VExpr.appHead]

/-- Pointwise restoration of all declaration-time earlier-projector
arguments agrees with the arguments built from restored templates. -/
theorem restoreFlatProjectionArguments
    (view : VRestoredBlockStructureView)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    (levels : List VLevel) (hlevels : levels.length = view.uvars)
    (fieldSort : VLevel) :
    (view.flatProjectionCodeTemplates levels).map (fun code =>
        view.nested.restoreRecAt
          (view.flatView.projectionLevels fieldSort levels)
          (.app code.projector.lift (.bvar 0))) =
      (view.restoredProjectionCodeTemplates levels).map (fun code =>
        .app code.projector.lift (.bvar 0)) := by
  unfold restoredProjectionCodeTemplates
  rw [List.map_map]
  apply List.map_congr_left
  intro code member
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.1 member
  exact view.restoreFlatProjectionArgumentAt closed levels hlevels fieldSort
    found

/-- The pointwise argument correspondence restricts to every source prefix. -/
theorem restoreFlatProjectionArguments_take
    (view : VRestoredBlockStructureView)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    (levels : List VLevel) (hlevels : levels.length = view.uvars)
    (fieldSort : VLevel) (count : Nat) :
    ((view.flatProjectionCodeTemplates levels).take count).map (fun code =>
        view.nested.restoreRecAt
          (view.flatView.projectionLevels fieldSort levels)
          (.app code.projector.lift (.bvar 0))) =
      ((view.restoredProjectionCodeTemplates levels).take count).map
        (fun code => .app code.projector.lift (.bvar 0)) := by
  simpa only [List.map_take] using congrArg (List.take count)
    (view.restoreFlatProjectionArguments closed levels hlevels fieldSort)

/-- Before runtime parameters are supplied, the restored type-function
template is exactly the corresponding restored source field with the
restored earlier-projector prefix substituted.  Runtime parameters remain
outside the restoration boundary. -/
theorem operationalProjectionCodes_get?_restoredTypeFnTemplate
    (view : VRestoredBlockStructureView)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    (levels : List VLevel) (hlevels : levels.length = view.uvars)
    (params : List VExpr) {index : Nat}
    {code : VStructureView.ProjectionCode}
    (found : (view.operationalProjectionCodes levels params)[index]? =
      some code) :
    ∃ field domain body,
      (view.specializedFields levels
        (VExpr.bvarRevRange 0 view.nparams))[index]? = some field ∧
      code.typeFn = (VExpr.lam domain body).instRevAt params 0 ∧
      body = (field.liftN 1 index).instRevAt
        (((view.restoredProjectionCodeTemplates levels).take index).map
          fun prior => .app prior.projector.lift (.bvar 0)) 0 := by
  obtain ⟨flatField, flatFieldFound, typeFnEq⟩ :=
    view.operationalProjectionCodes_get?_typeFn levels params found
  let projectionLevels :=
    view.flatView.projectionLevels code.fieldSort levels
  let flatArgs :=
    ((view.flatProjectionCodeTemplates levels).take index).map
      fun prior => VExpr.app prior.projector.lift (.bvar 0)
  let restoredArgs :=
    ((view.restoredProjectionCodeTemplates levels).take index).map
      fun prior => VExpr.app prior.projector.lift (.bvar 0)
  let field := view.nested.restoreRecAt projectionLevels flatField
  let domain := view.nested.restoreRecAt projectionLevels
    (view.flatView.structureType levels
      (VExpr.bvarRevRange 0 view.nparams))
  let body := (field.liftN 1 index).instRevAt restoredArgs 0

  have fieldsEq := view.restoreFlatSpecializedFields_bvarRevRange closed
    code.fieldSort levels hlevels
  have fieldsAt := congrArg (fun fields : List VExpr => fields[index]?)
    fieldsEq
  simp only [List.getElem?_map, flatFieldFound, Option.map_some] at fieldsAt
  have fieldFound :
      (view.specializedFields levels
        (VExpr.bvarRevRange 0 view.nparams))[index]? = some field := by
    exact fieldsAt.symm

  have flatArgumentsNonConst :
      ∀ argument ∈ flatArgs, ∀ name nameLevels,
        (view.nested.restoreRecAt projectionLevels argument).appHead ≠
          .const name nameLevels := by
    intro argument member name nameLevels
    obtain ⟨prior, priorMember, rfl⟩ := List.mem_map.1 member
    have priorMemberFull :
        prior ∈ view.flatProjectionCodeTemplates levels :=
      List.mem_of_mem_take priorMember
    obtain ⟨priorIndex, priorFound⟩ :=
      List.mem_iff_getElem?.1 priorMemberFull
    exact view.restoreFlatProjectionArgumentAt_nonConst closed levels
      hlevels code.fieldSort priorFound name nameLevels

  have bodyMapped := view.nested.restoreRecAt_instRevAt_map closed
    projectionLevels (flatField.liftN 1 index) flatArgs 0
      flatArgumentsNonConst
  have fieldLift := view.nested.restoreRecAt_liftN closed projectionLevels
    flatField 1 index
  have argsMapped :
      flatArgs.map (view.nested.restoreRecAt projectionLevels) =
        restoredArgs := by
    dsimp [flatArgs, restoredArgs]
    rw [List.map_map]
    simpa [projectionLevels, Function.comp_def] using
      view.restoreFlatProjectionArguments_take closed levels hlevels
        code.fieldSort index
  have bodyRestored :
      view.nested.restoreRecAt projectionLevels
          ((flatField.liftN 1 index).instRevAt flatArgs 0) = body := by
    change view.nested.restoreRecAt projectionLevels
        ((flatField.liftN 1 index).instRevAt flatArgs 0) =
      (field.liftN 1 index).instRevAt restoredArgs 0
    calc
      _ = (view.nested.restoreRecAt projectionLevels
            (flatField.liftN 1 index)).instRevAt
            (flatArgs.map (view.nested.restoreRecAt projectionLevels)) 0 :=
        bodyMapped.symm
      _ = (field.liftN 1 index).instRevAt restoredArgs 0 := by
        rw [← fieldLift, argsMapped]

  refine ⟨field, domain, body, fieldFound, ?_, rfl⟩
  rw [typeFnEq]
  have templateEq :
      view.nested.restoreRecAt projectionLevels
          (VExpr.lam
            (view.flatView.structureType levels
              (VExpr.bvarRevRange 0 view.nparams))
            ((flatField.liftN 1 index).instRevAt flatArgs 0)) =
        VExpr.lam domain body := by
    change (VExpr.lam domain
        (view.nested.restoreRecAt projectionLevels
          ((flatField.liftN 1 index).instRevAt flatArgs 0))) =
      VExpr.lam domain body
    rw [bodyRestored]
  exact congrArg (fun expression : VExpr => expression.instRevAt params 0)
    templateEq

/-- Substitution above an already-instantiated inner segment can be moved
before that segment when every inner argument is transformed by the outer
substitution. -/
private theorem instRevAt_instRevAt_hi
    (expression : VExpr) (inner outer : List VExpr)
    (innerOffset outerOffset : Nat) :
    (expression.instRevAt inner innerOffset).instRevAt outer
        (outerOffset + innerOffset) =
      (expression.instRevAt outer
        (outerOffset + innerOffset + inner.length)).instRevAt
          (inner.map fun argument =>
            argument.instRevAt outer outerOffset) innerOffset := by
  induction outer generalizing expression inner with
  | nil => simp [VExpr.instRevAt]
  | cons argument outer ih =>
      simp only [VExpr.instRevAt]
      rw [show outerOffset + innerOffset + outer.length =
        (outerOffset + outer.length) + innerOffset by omega]
      rw [VExpr.instN_instRevAt]
      rw [ih]
      simp only [List.length_map]
      congr 1
      · congr 2 <;> omega
      · rw [List.map_map]
        rfl

/-- Exact telescopes commute with a substitution at the progressively
shifted cutoff used by `instRevAt`. -/
private theorem VExpr.telN_instRevAt
    (count : Nat) (expression : VExpr)
    (arguments : List VExpr) (offset : Nat)
    (lengthEq : (VExpr.telN count expression).length = count) :
    VExpr.telN count (expression.instRevAt arguments offset) =
      ((VExpr.telN count expression).zipIdx offset).map fun entry =>
        entry.1.instRevAt arguments entry.2 := by
  induction count generalizing expression offset with
  | zero => rfl
  | succ count ih =>
      cases expression with
      | forallE domain body =>
          have tailLength : (VExpr.telN count body).length = count := by
            simp only [VExpr.telN, List.length_cons] at lengthEq
            omega
          simp only [VExpr.instRevAt_forallE_projection, VExpr.telN,
            List.zipIdx, List.map_cons]
          rw [ih body (offset + 1) tailLength]
      | bvar | sort | const | app | lam =>
          simp only [VExpr.telN, List.length_nil] at lengthEq
          omega

/-- Dropping an exact telescope after substitution is substitution beneath
that telescope. -/
private theorem VExpr.dropN_instRevAt
    (count : Nat) (expression : VExpr)
    (arguments : List VExpr) (offset : Nat)
    (lengthEq : (VExpr.telN count expression).length = count) :
    VExpr.dropN count (expression.instRevAt arguments offset) =
      (VExpr.dropN count expression).instRevAt arguments (offset + count) := by
  induction count generalizing expression offset with
  | zero => rfl
  | succ count ih =>
      cases expression with
      | forallE domain body =>
          have tailLength : (VExpr.telN count body).length = count := by
            simp only [VExpr.telN, List.length_cons] at lengthEq
            omega
          simp only [VExpr.instRevAt_forallE_projection, VExpr.dropN]
          simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            ih body (offset + 1) tailLength
      | bvar | sort | const | app | lam =>
          simp only [VExpr.telN, List.length_nil] at lengthEq
          omega

/-- Recover a typing for the unapplied head of a typed iterated application.
This local inversion form is used to reconstruct a motive telescope directly
from the live minor result typing. -/
private theorem VEnv.HasType.appN_head_hasType_restored
    {env : VEnv} (henv : env.Ordered) {U : Nat} {context : List VExpr}
    (hcontext : OnCtx context (env.IsType U)) :
    ∀ {function : VExpr} {arguments : List VExpr} {result : VExpr},
      env.HasType U context (VExpr.appN function arguments) result →
        ∃ type, env.HasType U context function type
  | _, [], _, typed => ⟨_, typed⟩
  | function, argument :: arguments, _, typed => by
      obtain ⟨resultType, prefixTyped⟩ :=
        VEnv.HasType.appN_head_hasType_restored henv hcontext
          (function := .app function argument) (arguments := arguments) typed
      obtain ⟨domain, body, functionTyped, _⟩ :=
        prefixTyped.app_inv henv hcontext
      exact ⟨.forallE domain body, functionTyped⟩

/-- Instantiating ambient parameters above one freshly inserted binder
commutes with that binder insertion at an arbitrary cutoff. -/
private theorem liftAt_instRevAt_projection
    (expression : VExpr) (arguments : List VExpr) (offset : Nat) :
    (expression.liftN 1 offset).instRevAt arguments (offset + 1) =
      (expression.instRevAt arguments offset).liftN 1 offset := by
  induction arguments generalizing expression with
  | nil => rfl
  | cons argument arguments ih =>
      simp only [VExpr.instRevAt]
      rw [show offset + 1 + arguments.length =
        arguments.length + 1 + offset by omega]
      rw [VExpr.instN_liftAt_projection]
      simpa only [Nat.add_comm] using
        ih (expression := expression.inst argument
          (arguments.length + offset))

/-- Telescope form of commuting ambient parameter specialization beneath
one retained binder. -/
private theorem VExpr.liftTelN_instRevAt_projection
    (fields : List VExpr) (arguments : List VExpr) (start : Nat) :
    ((VExpr.liftTelN 1 fields start).zipIdx (start + 1)).map
        (fun entry => entry.1.instRevAt arguments entry.2) =
      VExpr.liftTelN 1
        ((fields.zipIdx start).map fun entry =>
          entry.1.instRevAt arguments entry.2) start := by
  induction fields generalizing start with
  | nil => rfl
  | cons field fields ih =>
      simp only [VExpr.liftTelN, List.zipIdx, List.map_cons]
      rw [liftAt_instRevAt_projection]
      congr 1
      simpa only [Nat.add_assoc] using ih (start + 1)

/-- Field-sort metadata, the dummy minor slot, and the projector body retain
their exact declaration-time flattened origin through restoration and later
runtime specialization. -/
theorem operationalProjectionCodes_get?_program_shape
    (view : VRestoredBlockStructureView)
    (levels : List VLevel) (params : List VExpr)
    {index : Nat} {code : VStructureView.ProjectionCode}
    (found : (view.operationalProjectionCodes levels params)[index]? =
      some code) :
    ∃ flatTemplate fieldSort,
      (view.flatProjectionCodeTemplates levels)[index]? =
        some flatTemplate ∧
      (view.flatView.fieldSorts.map (VLevel.inst levels))[index]? =
        some fieldSort ∧
      code.fieldSort = fieldSort ∧
      code.minor = code.typeFn ∧
      code.projector =
        VExpr.instRevAt
          (view.nested.restoreRecAt
            (view.flatView.projectionLevels fieldSort levels)
            (view.flatView.operationalProjector levels
              (VExpr.bvarRevRange 0 view.nparams)
              (view.flatView.specializedFields levels
                (VExpr.bvarRevRange 0 view.nparams))
              (view.flatView.structureType levels
                (VExpr.bvarRevRange 0 view.nparams))
              fieldSort index flatTemplate.typeFn))
          params 0 := by
  obtain ⟨flatTemplate, flatFound, rfl⟩ :=
    view.operationalProjectionCodes_get?_exists_flat levels params found
  obtain ⟨fieldSort, fieldSortFound, codeSort, minorEq, projectorEq⟩ :=
    view.flatView.operationalProjectionCodes_get?_program_shape levels
      (VExpr.bvarRevRange 0 view.nparams) flatFound
  refine ⟨flatTemplate, fieldSort, flatFound, fieldSortFound, ?_, ?_, ?_⟩
  · exact restoreProjectionCodeAt_fieldSort view levels flatTemplate |>.trans
      codeSort
  · change (view.nested.restoreRecAt _ flatTemplate.minor).instRevAt
      params 0 =
        (view.nested.restoreRecAt _ flatTemplate.typeFn).instRevAt params 0
    rw [minorEq]
  · change (view.nested.restoreRecAt
      (view.flatView.projectionLevels flatTemplate.fieldSort levels)
      flatTemplate.projector).instRevAt params 0 = _
    rw [codeSort, projectorEq]

/-- The restored recursor projector retains the literal public source
structure as its lambda domain.  This records the domain independently of
the detailed motive/minor body shape used by operational typing. -/
theorem operationalProjectionCodes_get?_projector_domain
    (view : VRestoredBlockStructureView)
    (levels : List VLevel) (params : List VExpr)
    (hparams : params.length = view.nparams)
    {index : Nat} {code : VStructureView.ProjectionCode}
    (found : (view.operationalProjectionCodes levels params)[index]? =
      some code) :
    ∃ body, code.projector =
      .lam (view.structureType levels params) body := by
  obtain ⟨flatTemplate, fieldSort, flatFound, fieldSortFound, codeSort,
      minorEq, projectorEq⟩ :=
    view.operationalProjectionCodes_get?_program_shape levels params found
  let projectionLevels :=
    view.flatView.projectionLevels fieldSort levels
  let formalParams := VExpr.bvarRevRange 0 view.nparams
  let flatFields := view.flatView.specializedFields levels formalParams
  let flatStructType := view.flatView.structureType levels formalParams
  let flatParamsMajor := formalParams.map (VExpr.liftN 1)
  let flatAllFieldsMajor := VExpr.liftTelN 1 flatFields 0
  let flatTypeFnMajor := flatTemplate.typeFn.lift
  let majorBinder := VExpr.bvar 0
  let flatDummyType := VBlockStructureView.majorDummyType
    flatTypeFnMajor majorBinder
  let flatDummyValue := VBlockStructureView.majorDummyValue
    flatTypeFnMajor majorBinder
  let flatMotives := view.flatView.projectionMotivesWith levels
    flatParamsMajor flatTypeFnMajor flatDummyType
  let flatMinors := view.nested.generation.flatCtors.map fun constructor =>
    view.flatView.projectionMinorWith constructor fieldSort levels
      flatParamsMajor flatAllFieldsMajor flatMotives index flatDummyValue
  let flatBody := VExpr.appN
    (.const view.flatView.recursorName
      (view.flatView.projectionLevels fieldSort levels))
    (flatParamsMajor ++ flatMotives ++ flatMinors ++ [majorBinder])
  let restoredBody := view.nested.restoreRecAt projectionLevels flatBody
  refine ⟨restoredBody.instRevAt params 1, ?_⟩
  rw [projectorEq]
  unfold VBlockStructureView.operationalProjector
  change (view.nested.restoreRecAt projectionLevels
      (.lam flatStructType flatBody)).instRevAt params 0 = _
  unfold NestedBlockChecked.restoreRecAt
  simp only [VInductDecl.restoreExpr, VExpr.instRevAt_lam_projection]
  congr 1
  change (view.nested.restoreRecAt projectionLevels flatStructType).instRevAt
      params 0 = view.structureType levels params
  rw [show view.nested.restoreRecAt projectionLevels flatStructType =
      view.structureType levels formalParams by
    simpa [projectionLevels, flatStructType, formalParams] using
      view.restoreRecAt_flatStructureType_bvarRevRange fieldSort levels]
  unfold structureType
  rw [VExpr.instRevAt_appN_projection]
  rw [VExpr.instRevAt_closedN params
    (C := .const view.name levels) (by trivial)]
  rw [show formalParams = VExpr.bvarRevRange 0 params.length by
    rw [hparams]]
  rw [VExpr.map_instRevAt_bvarRevRange]
  simp

@[simp] theorem operationalProjectionCodes_length
    (view : VRestoredBlockStructureView)
    (levels : List VLevel) (params : List VExpr) :
    (view.operationalProjectionCodes levels params).length =
      (view.specializedFields levels params).length := by
  calc
    (view.operationalProjectionCodes levels params).length =
        (view.flatProjectionCodeTemplates levels).length := by
      simp [operationalProjectionCodes, restoredProjectionCodeTemplates]
    _ = (view.flatView.specializedFields levels
        (VExpr.bvarRevRange 0 view.nparams)).length := by
      simp [flatProjectionCodeTemplates]
    _ = view.flatView.fields.length := by
      simp [VBlockStructureView.specializedFields]
    _ = view.fields.length := by
      simpa [fields, flatView, VBlockStructureView.fields] using
        view.selection.source_flat_fields_length_eq.symm
    _ = (view.specializedFields levels params).length := by
      simp [specializedFields]

@[simp] theorem flatProjectionCodeTemplates_instL
    (view : VRestoredBlockStructureView)
    (levels : List VLevel) (extra : List VLevel) :
    (view.flatProjectionCodeTemplates levels).map
        (fun code => code.instL extra) =
      view.flatProjectionCodeTemplates (levels.map (VLevel.inst extra)) := by
  simp [flatProjectionCodeTemplates,
    VBlockStructureView.operationalProjectionCodes_instL,
    VExpr.bvarRevRange_map_instL]

@[simp] theorem restoredProjectionCodeTemplates_instL
    (view : VRestoredBlockStructureView)
    (levels : List VLevel) (extra : List VLevel) :
    (view.restoredProjectionCodeTemplates levels).map
        (fun code => code.instL extra) =
      view.restoredProjectionCodeTemplates
        (levels.map (VLevel.inst extra)) := by
  unfold restoredProjectionCodeTemplates
  simp only [List.map_map, Function.comp_def,
    restoreProjectionCodeAt_instL]
  rw [← view.flatProjectionCodeTemplates_instL levels extra]
  rw [List.map_map]
  rfl

@[simp] theorem operationalProjectionCodes_instL
    (view : VRestoredBlockStructureView)
    (levels : List VLevel) (params : List VExpr)
    (extra : List VLevel) :
    (view.operationalProjectionCodes levels params).map
        (fun code => code.instL extra) =
      view.operationalProjectionCodes
        (levels.map (VLevel.inst extra))
        (params.map (VExpr.instL extra)) := by
  unfold operationalProjectionCodes
  simp only [List.map_map, Function.comp_def,
    VStructureView.ProjectionCode.instL_instRevAt]
  rw [← view.restoredProjectionCodeTemplates_instL levels extra]
  rw [List.map_map]
  rfl

/-- Above the complete formal parameter context, flattened templates are
invariant under ambient lifting. -/
theorem flatProjectionCodeTemplates_liftN_high
    (view : VRestoredBlockStructureView)
    (flatNaturality : view.flatView.OperationalCodeNaturality)
    (levels : List VLevel) (count cutoff : Nat)
    (above : view.nparams ≤ cutoff) :
    (view.flatProjectionCodeTemplates levels).map
        (fun code => code.liftN count cutoff) =
      view.flatProjectionCodeTemplates levels := by
  unfold flatProjectionCodeTemplates
  have formalLength :
      (VExpr.bvarRevRange 0 view.nparams).length =
        view.flatView.nparams := by
    simpa only [VExpr.bvarRevRange_length, view.flatView_nparams]
  rw [flatNaturality.liftN levels
    (VExpr.bvarRevRange 0 view.nparams) formalLength count cutoff]
  rw [VExpr.bvarRevRange_liftN_high]
  simpa using above

/-- Declaration-time restored templates inherit the same high-cutoff
invariance from the exact flattened layout and restoration closure. -/
theorem restoredProjectionCodeTemplates_liftN_high
    (view : VRestoredBlockStructureView)
    (flatNaturality : view.flatView.OperationalCodeNaturality)
    (closed : VInductDecl.RestoreEntriesClosed view.nested.recEntries)
    (levels : List VLevel) (count cutoff : Nat)
    (above : view.nparams ≤ cutoff) :
    (view.restoredProjectionCodeTemplates levels).map
        (fun code => code.liftN count cutoff) =
      view.restoredProjectionCodeTemplates levels := by
  unfold restoredProjectionCodeTemplates
  calc
    ((view.flatProjectionCodeTemplates levels).map
        (view.restoreProjectionCodeAt levels)).map
          (fun code => code.liftN count cutoff) =
      ((view.flatProjectionCodeTemplates levels).map
        (fun code => code.liftN count cutoff)).map
          (view.restoreProjectionCodeAt levels) := by
      simp only [List.map_map, Function.comp_def,
        restoreProjectionCodeAt_liftN view closed]
    _ = (view.flatProjectionCodeTemplates levels).map
          (view.restoreProjectionCodeAt levels) := by
      rw [view.flatProjectionCodeTemplates_liftN_high flatNaturality levels
        count cutoff above]

/-- Every restored declaration-time template is closed over exactly the
formal source-parameter context. -/
theorem restoredProjectionCodeTemplates_closedN
    (view : VRestoredBlockStructureView)
    (flatNaturality : view.flatView.OperationalCodeNaturality)
    (closed : VInductDecl.RestoreEntriesClosed view.nested.recEntries)
    (levels : List VLevel) {index : Nat}
    {code : VStructureView.ProjectionCode}
    (found : (view.restoredProjectionCodeTemplates levels)[index]? =
      some code) :
    code.ClosedN view.nparams := by
  have lifted := congrArg (fun codes :
      List VStructureView.ProjectionCode => codes[index]?)
    (view.restoredProjectionCodeTemplates_liftN_high flatNaturality closed
      levels 1 view.nparams (Nat.le_refl _))
  simp only [List.getElem?_map, found, Option.map_some,
    Option.some.injEq] at lifted
  exact code.closedN_of_liftN_one_eq view.nparams lifted

/-- Instantiation above the complete formal parameter context leaves every
restored template unchanged, with no condition on the substituted term. -/
theorem restoredProjectionCodeTemplates_instN_high
    (view : VRestoredBlockStructureView)
    (flatNaturality : view.flatView.OperationalCodeNaturality)
    (closed : VInductDecl.RestoreEntriesClosed view.nested.recEntries)
    (levels : List VLevel) (argument : VExpr) (cutoff : Nat)
    (above : view.nparams ≤ cutoff) :
    (view.restoredProjectionCodeTemplates levels).map
        (fun code => code.instN argument cutoff) =
      view.restoredProjectionCodeTemplates levels := by
  apply List.ext_getElem?
  intro index
  simp only [List.getElem?_map]
  cases found : (view.restoredProjectionCodeTemplates levels)[index]? with
  | none => rfl
  | some code =>
      simp only [Option.map_some]
      rw [(view.restoredProjectionCodeTemplates_closedN flatNaturality closed
        levels found).instN_eq argument cutoff above]

/-- The complete restored code inventory commutes with ambient lifting.
Restoration is performed only on formal templates; arbitrary caller
parameters are substituted afterward. -/
theorem operationalProjectionCodes_liftN
    (view : VRestoredBlockStructureView)
    (flatNaturality : view.flatView.OperationalCodeNaturality)
    (closed : VInductDecl.RestoreEntriesClosed view.nested.recEntries)
    (levels : List VLevel) (params : List VExpr)
    (paramsLength : params.length = view.nparams)
    (count cutoff : Nat) :
    (view.operationalProjectionCodes levels params).map
        (fun code => code.liftN count cutoff) =
      view.operationalProjectionCodes levels
        (params.map fun param => param.liftN count cutoff) := by
  unfold operationalProjectionCodes
  calc
    ((view.restoredProjectionCodeTemplates levels).map
        (fun code => code.instRevAt params 0)).map
          (fun code => code.liftN count cutoff) =
      ((view.restoredProjectionCodeTemplates levels).map
        (fun code => code.liftN count (cutoff + params.length))).map
          (fun code => code.instRevAt
            (params.map fun param => param.liftN count cutoff) 0) := by
      simp only [List.map_map, Function.comp_def]
      apply List.map_congr_left
      intro code _
      simpa using code.liftN_instRevAt params 0 cutoff count
    _ = (view.restoredProjectionCodeTemplates levels).map
          (fun code => code.instRevAt
            (params.map fun param => param.liftN count cutoff) 0) := by
      rw [view.restoredProjectionCodeTemplates_liftN_high flatNaturality closed
        levels count (cutoff + params.length) (by rw [paramsLength]; omega)]

/-- The complete restored code inventory commutes with arbitrary ambient
term instantiation.  Caller expressions remain opaque because substitution
occurs strictly after declaration-time restoration. -/
theorem operationalProjectionCodes_instN
    (view : VRestoredBlockStructureView)
    (flatNaturality : view.flatView.OperationalCodeNaturality)
    (closed : VInductDecl.RestoreEntriesClosed view.nested.recEntries)
    (levels : List VLevel) (params : List VExpr)
    (paramsLength : params.length = view.nparams)
    (argument : VExpr) (cutoff : Nat) :
    (view.operationalProjectionCodes levels params).map
        (fun code => code.instN argument cutoff) =
      view.operationalProjectionCodes levels
        (params.map fun param => param.inst argument cutoff) := by
  unfold operationalProjectionCodes
  calc
    ((view.restoredProjectionCodeTemplates levels).map
        (fun code => code.instRevAt params 0)).map
          (fun code => code.instN argument cutoff) =
      ((view.restoredProjectionCodeTemplates levels).map
        (fun code => code.instN argument (cutoff + params.length))).map
          (fun code => code.instRevAt
            (params.map fun param => param.inst argument cutoff) 0) := by
      simp only [List.map_map, Function.comp_def]
      apply List.map_congr_left
      intro code _
      simpa using code.instN_instRevAt params 0 cutoff argument
    _ = (view.restoredProjectionCodeTemplates levels).map
          (fun code => code.instRevAt
            (params.map fun param => param.inst argument cutoff) 0) := by
      rw [view.restoredProjectionCodeTemplates_instN_high flatNaturality closed
        levels argument (cutoff + params.length)
          (by rw [paramsLength]; omega)]

/-! ## Restored operational contracts

The contracts below intentionally mirror only the runtime-facing portion of
`VBlockStructureView`.  Their expressions are indexed by the restored source
telescope and the restored code inventory, so satisfying them can never be
mistaken for well-formedness of the flattened block at the public endpoint.
-/

/-- Typing of a source-order prefix of restored operational projectors. -/
def OperationalProgramsWFPrefix (view : VRestoredBlockStructureView)
    (env : VEnv) (limit : Nat) : Prop :=
  ∀ {U : Nat} {Γ : List VExpr} {levels : List VLevel}
      {params : List VExpr} {index : Nat}
      {code : VStructureView.ProjectionCode},
    index < limit →
    OnCtx Γ (env.IsType U) →
    (∀ level ∈ levels, level.WF U) →
    levels.length = view.uvars →
    params.length = view.nparams →
    (∃ resultLevel, env.SpineWF U Γ (view.familyType.instL levels)
      params (.sort resultLevel)) →
    (view.operationalProjectionCodes levels params)[index]? = some code →
    env.HasType U Γ code.projector
      (.forallE (view.structureType levels params)
        (.app code.typeFn.lift (.bvar 0)))

/-- Every restored operational projector is well typed at the restored
source surface. -/
def OperationalProgramsWF (view : VRestoredBlockStructureView)
    (env : VEnv) : Prop :=
  ∀ {U : Nat} {Γ : List VExpr} {levels : List VLevel}
      {params : List VExpr} {index : Nat}
      {code : VStructureView.ProjectionCode},
    OnCtx Γ (env.IsType U) →
    (∀ level ∈ levels, level.WF U) →
    levels.length = view.uvars →
    params.length = view.nparams →
    (∃ resultLevel, env.SpineWF U Γ (view.familyType.instL levels)
      params (.sort resultLevel)) →
    (view.operationalProjectionCodes levels params)[index]? = some code →
    env.HasType U Γ code.projector
      (.forallE (view.structureType levels params)
        (.app code.typeFn.lift (.bvar 0)))

/-- Elimination is admissible for every restored operational projector.
The statement is environment-free: restoration changes expression payloads
but preserves the flattened generator's field-universe key literally. -/
def OperationalMotiveAdmissible
    (view : VRestoredBlockStructureView) : Prop :=
  ∀ {levels : List VLevel} {params : List VExpr} {index : Nat}
      {code : VStructureView.ProjectionCode},
    (view.operationalProjectionCodes levels params)[index]? = some code →
    view.nested.generation.motiveLevel.inst
      (view.flatView.projectionLevels code.fieldSort levels) = code.fieldSort

/-- Full flattened generation well-formedness supplies the environment-free
elimination contract for the corresponding restored projector inventory.
Restoration and later parameter specialization preserve the field-sort key. -/
theorem operationalMotiveAdmissible_of_flatWF
    (view : VRestoredBlockStructureView) {env : VEnv}
    (flatWF : view.flatView.WF env) :
    view.OperationalMotiveAdmissible := by
  intro levels params index code found
  obtain ⟨flatCode, flatFound, rfl⟩ :=
    view.operationalProjectionCodes_get?_exists_flat levels params found
  have flatAdmissible := flatWF.operationalMotiveAdmissible
    (levels := levels) (params := VExpr.bvarRevRange 0 view.nparams)
      (idx := index) (code := flatCode) (by
        simpa [flatProjectionCodeTemplates] using flatFound)
  simpa [restoreProjectionCodeAt,
    VStructureView.ProjectionCode.instRevAt, flatView] using flatAdmissible

/-- Exact selected-constructor computation for a restored operational
prefix.  This is stated on the source constructor and source field telescope,
not on their flattened counterparts. -/
def OperationalConstructorProjectorsExactPrefix
    (view : VRestoredBlockStructureView) (env : VEnv)
    (limit : Nat) : Prop :=
  ∀ {U : Nat} {Γ : List VExpr} {levels : List VLevel}
      {params : List VExpr} {count : Nat},
    count ≤ limit →
    OnCtx Γ (env.IsType U) →
    (∀ level ∈ levels, level.WF U) →
    levels.length = view.uvars →
    params.length = view.nparams →
    (∃ resultLevel, env.SpineWF U Γ (view.familyType.instL levels)
      params (.sort resultLevel)) →
    count ≤ (view.operationalProjectionCodes levels params).length →
    let fields := view.specializedFields levels params
    List.Forall₂
      (fun projected selected => projected = selected ∨
        env.IsDefEqU U (fields.reverse ++ Γ) projected selected)
      (((view.operationalProjectionCodes levels params).take count).map
        fun prior =>
          .app (prior.projector.liftN fields.length)
            (view.projectionConstructorApp levels params fields))
      (VExpr.bvarRevRange (fields.length - count) count)

/-- Runtime constructor-prefix evidence with strengthening allowed at
dependency-irrelevant positions. -/
def OperationalSparseConstructorPrefix
    (view : VRestoredBlockStructureView) (env : VEnv) (U : Nat)
    (Γ : List VExpr) (levels : List VLevel) (params : List VExpr)
    (limit : Nat) : Prop :=
  let fields := view.specializedFields levels params
  let fieldCount := fields.length
  let source := VExpr.forallN (VExpr.liftTelN fieldCount fields 0)
    (.sort .zero)
  let leftArgs :=
    ((view.operationalProjectionCodes levels params).take limit).map
      fun prior =>
        VExpr.app (prior.projector.liftN fieldCount)
          (view.projectionConstructorApp levels params fields)
  let rightArgs := VExpr.bvarRevRange (fieldCount - limit) limit
  ∃ cursor, ∃ sparse : env.SparseSpineWF U (fields.reverse ++ Γ)
      source leftArgs cursor,
    sparse.PointwiseDefEq rightArgs

/-- The exact source-telescope fact needed by the selected restored minor:
substituting the restored operational prefix into the lifted current field
agrees with the canonical field variable context. -/
def OperationalConstructorFieldAligned
    (view : VRestoredBlockStructureView) (env : VEnv) (U : Nat)
    (Γ : List VExpr) (levels : List VLevel) (params : List VExpr)
    (limit : Nat) : Prop :=
  ∀ {field : VExpr},
    (view.specializedFields levels params)[limit]? = some field →
    let fields := view.specializedFields levels params
    let m := fields.length
    env.IsDefEqU U (fields.reverse ++ Γ)
      ((field.liftN m limit).instRev
        (((view.operationalProjectionCodes levels params).take limit).map
          fun prior =>
            .app (prior.projector.liftN m)
              (view.projectionConstructorApp levels params fields)))
      (field.liftN (m - limit))

/-- The two sparse traces consumed by restored projection inference. -/
def OperationalRuntimePrefix
    (view : VRestoredBlockStructureView) (env : VEnv) (U : Nat)
    (Γ : List VExpr) (levels : List VLevel) (params : List VExpr)
    (limit : Nat) : Prop :=
  (∃ cursor,
    env.SparseSpineWF U (view.structureType levels params :: Γ)
      (VExpr.forallN
        (view.specializedFields levels (params.map (VExpr.liftN 1)))
        (.sort .zero))
      (view.operationalProjectionArgs levels
        (params.map (VExpr.liftN 1)) limit (.bvar 0)) cursor) ∧
  view.OperationalSparseConstructorPrefix env U Γ levels params limit

/-- Exact final registrations owned by one restored nested structure.  The
family and constructor are source metadata, while the recursor and rules are
the producer's restored flattened artifacts. -/
structure Registered (view : VRestoredBlockStructureView)
    (env : VEnv) : Prop where
  family : env.constants view.name =
    some view.sourceFamily.toVConstant
  constructor : env.constants view.constructorName =
    some view.sourceConstructor.toVConstant
  recursor : env.constants view.recursorName =
    some view.recursor.toVConstant
  rules : ∀ rule ∈ view.nested.generatedRules, env.defeqs rule

theorem Registered.mono {view : VRestoredBlockStructureView}
    {env env' : VEnv} (hle : env ≤ env') (self : view.Registered env) :
    view.Registered env' where
  family := hle.constants self.family
  constructor := hle.constants self.constructor
  recursor := hle.constants self.recursor
  rules := fun rule member => hle.defeqs (self.rules rule member)

/-- The monotone restored metadata layout available at the final nested
endpoint.  Operational recursor-program transport is intentionally kept as
a separate backend contract instead of being conflated with this exact
registration and telescope layer. -/
structure LayoutWF (view : VRestoredBlockStructureView)
    (env : VEnv) : Prop extends view.Registered env where
  fieldTelescope : env.OnSortTel view.uvars
    view.constructorParams.reverse view.fields view.fieldSorts

/-- The selected flattened family semantics which remain valid at the
restored endpoint.  Family syntax is never rewritten by nested elimination,
so the paired staging certificate can transport this fragment monotonically
from the common dependency environment.  Constructor semantics are kept out
of this layer: their field bodies do undergo restoration and require a
separate operational transport argument. -/
structure FamilyLayoutWF (view : VRestoredBlockStructureView)
    (env : VEnv) : Prop extends view.LayoutWF env where
  familyWF : view.selection.family.WF view.nested.generation env

/-- The additional constructor-parameter alignment required by restored
projection execution.  It is intentionally separate from `FamilyLayoutWF`:
the paired flattened certificate proves the family side monotonically, while
transporting a flattened constructor comparison across restoration is the
remaining producer obligation. -/
structure ConstructorParameterLayoutWF
    (view : VRestoredBlockStructureView) (env : VEnv) : Prop
    extends view.FamilyLayoutWF env where
  constructorParamsDefEq : env.TelDefEq view.uvars []
    view.constructorParams view.nested.generation.block.checked.params
  /-- The registered recursor retains the exact generated binder surface,
  while the operational projector algebra is phrased over the legacy raw
  surface.  Nested restoration must preserve their definitional equality. -/
  recursorTypeDefEq : ∃ sortLevel, env.IsDefEq
    view.nested.generation.recUvars []
    (view.nested.restoreRec
      (view.nested.generation.recType view.selection.family))
    view.recursor.type (.sort sortLevel)

theorem LayoutWF.mono {view : VRestoredBlockStructureView}
    {env env' : VEnv} (hle : env ≤ env') (self : view.LayoutWF env) :
    view.LayoutWF env' where
  toRegistered := self.toRegistered.mono hle
  fieldTelescope := self.fieldTelescope.mono hle

/-- Well-formedness of the registered restored iota rule types the selected
constructor-headed major in the exact restored rule telescope.  This is the
first semantic bridge from the flattened producer's rule layout to the
restored source surface: it uses the rule type rather than assuming that the
source constructor result already has the canonical family shape. -/
theorem LayoutWF.restoredRuleCtorApp_hasType
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.ConversionRegular) :
    let gen := view.nested.generation
    let constructor := view.flatView.blockConstructor
    ∃ type, env.HasType gen.recUvars
      ((gen.ruleBinders constructor).map view.nested.restoreRec).reverse
      (view.nested.restoreRec (gen.ruleCtorApp constructor)) type := by
  let gen := view.nested.generation
  let constructor := view.flatView.blockConstructor
  obtain ⟨ruleIndex, hentry⟩ :=
    List.mem_iff_getElem?.1 view.flatView.blockConstructor_mem
  have registered : env.defeqs
      (view.nested.restoredRule ruleIndex constructor) :=
    self.rules _ (view.nested.restoredRule_mem hentry)
  have ruleWF := henv.ordered.defEqWF registered
  obtain ⟨_, ruleTypeWF⟩ := ruleWF.1.isType henv.ordered (by trivial)
  have ruleTypeShape :
      (view.nested.restoredRule ruleIndex constructor).type =
        VExpr.forallN
          ((gen.ruleBinders constructor).map view.nested.restoreRec)
          (view.nested.restoreRec (gen.ruleResult constructor)) := by
    change view.nested.restoreRec
      ((gen.rule ruleIndex constructor).type) = _
    rw [gen.rule_type]
    unfold NestedBlockChecked.restoreRec
    rw [VInductDecl.restoreExpr_forallN]
    rfl
  have ruleUvars :
      (view.nested.restoredRule ruleIndex constructor).uvars =
        gen.recUvars := by
    change (gen.rule ruleIndex constructor).uvars = gen.recUvars
    exact gen.rule_uvars ruleIndex constructor
  rw [ruleTypeShape] at ruleTypeWF
  obtain ⟨ruleTel, _, ruleBodyWF⟩ :=
    VEnv.HasType.forallN_wf henv.ordered ruleTypeWF
  rw [ruleUvars] at ruleTel ruleBodyWF
  simp only [List.append_nil] at ruleBodyWF
  have ruleCtx : OnCtx
      (((gen.ruleBinders constructor).map
        view.nested.restoreRec).reverse)
      (env.IsType gen.recUvars) := by
    simpa only [List.append_nil] using
      VEnv.OnTel.onCtx (by trivial) ruleTel
  have ruleBodyShape :
      view.nested.restoreRec (gen.ruleResult constructor) =
        VExpr.appN
          (.bvar (gen.familyCount - 1 - constructor.owner +
            gen.minorCount + gen.ruleFieldCount constructor))
          ((gen.ruleIdx constructor ++ [gen.ruleCtorApp constructor]).map
            view.nested.restoreRec) := by
    unfold NestedBlockChecked.restoreRec
    rw [BlockGenerationChecked.ruleResult,
      VInductDecl.restoreExpr_bvar_appN]
  rw [ruleBodyShape] at ruleBodyWF
  have argumentsWF := VEnv.HasType.appN_args_wf henv.ordered ruleCtx _ _ rfl
    ruleBodyWF
  exact argumentsWF
    (view.nested.restoreRec (gen.ruleCtorApp constructor)) (by simp)

/-- The selected restored recursor rule pins its formal constructor
application to the restored application of the selected family.  The target
deliberately retains `restoreRec` around the family application: proving that
this restoration is the identity requires a separate producer-owned
source-head safety fact, and is not implied by the rule registration alone. -/
theorem FamilyLayoutWF.restoredRuleCtorApp_hasFamilyType
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.FamilyLayoutWF env) (henv : env.ConversionRegular)
    (closed : RestoreEntriesClosed view.nested.recEntries) :
    let gen := view.nested.generation
    let constructor := view.flatView.blockConstructor
    let fieldCount := gen.ruleFieldCount constructor
    let commonCount := gen.familyCount + gen.minorCount
    env.HasType gen.recUvars
      ((gen.ruleBinders constructor).map view.nested.restoreRec).reverse
      (view.nested.restoreRec (gen.ruleCtorApp constructor))
      (view.nested.restoreRec
        (VExpr.appN (.const view.name gen.sourceLevels)
          (VExpr.bvarRevRange (fieldCount + commonCount) view.nparams))) := by
  let gen := view.nested.generation
  let constructor := view.flatView.blockConstructor
  let family := view.flatView.family
  let fieldCount := gen.ruleFieldCount constructor
  let familyCount := gen.familyCount
  let minorCount := gen.minorCount
  let commonCount := familyCount + minorCount
  let motiveIndex := familyCount - 1 - constructor.owner +
    minorCount + fieldCount
  obtain ⟨ruleIndex, hentry⟩ :=
    List.mem_iff_getElem?.1 view.flatView.blockConstructor_mem
  have registered : env.defeqs
      (view.nested.restoredRule ruleIndex constructor) :=
    self.rules _ (view.nested.restoredRule_mem hentry)
  have ruleWF := henv.ordered.defEqWF registered
  obtain ⟨_, ruleTypeWF⟩ := ruleWF.1.isType henv.ordered (by trivial)
  have ruleTypeShape :
      (view.nested.restoredRule ruleIndex constructor).type =
        VExpr.forallN
          ((gen.ruleBinders constructor).map view.nested.restoreRec)
          (view.nested.restoreRec (gen.ruleResult constructor)) := by
    change view.nested.restoreRec
      ((gen.rule ruleIndex constructor).type) = _
    rw [gen.rule_type]
    unfold NestedBlockChecked.restoreRec
    rw [VInductDecl.restoreExpr_forallN]
    rfl
  have ruleUvars :
      (view.nested.restoredRule ruleIndex constructor).uvars =
        gen.recUvars := by
    change (gen.rule ruleIndex constructor).uvars = gen.recUvars
    exact gen.rule_uvars ruleIndex constructor
  rw [ruleTypeShape] at ruleTypeWF
  obtain ⟨ruleTel, _, ruleBodyWF⟩ :=
    VEnv.HasType.forallN_wf henv.ordered ruleTypeWF
  rw [ruleUvars] at ruleTel ruleBodyWF
  simp only [List.append_nil] at ruleBodyWF
  let ruleContext :=
    ((gen.ruleBinders constructor).map view.nested.restoreRec).reverse
  have ruleCtx : OnCtx ruleContext (env.IsType gen.recUvars) := by
    simpa only [ruleContext, List.append_nil] using
      VEnv.OnTel.onCtx (by trivial) ruleTel
  have resultIndices : constructor.ctor.view.resultIndices = [] := by
    apply List.length_eq_zero_iff.1
    rw [gen.view_resultIndices_length view.flatView.blockConstructor_mem]
    simp [VBlockStructureView.blockConstructor,
      view.flatView.checked_indices_eq]
  have ruleIndices : gen.ruleIdx constructor = [] := by
    simp [BlockGenerationChecked.ruleIdx,
      NormalizedCtor.resultIndicesR, resultIndices]
  have ruleBodyShape :
      view.nested.restoreRec (gen.ruleResult constructor) =
        .app (.bvar motiveIndex)
          (view.nested.restoreRec (gen.ruleCtorApp constructor)) := by
    unfold NestedBlockChecked.restoreRec
    rw [BlockGenerationChecked.ruleResult,
      VInductDecl.restoreExpr_bvar_appN]
    simp [ruleIndices, motiveIndex, familyCount, minorCount,
      fieldCount, VExpr.appN]
  rw [ruleBodyShape] at ruleBodyWF
  obtain ⟨argumentType, motiveBody, motiveWF, constructorWF⟩ :=
    ruleBodyWF.app_inv henv ruleCtx

  have familyMember : family ∈ gen.families := view.flatView.family_mem
  have familyOrdinal : constructor.owner = family.view.ordinal := rfl
  have ownerLt : constructor.owner < familyCount := by
    simpa [familyCount, familyOrdinal] using
      gen.family_ordinal_lt familyMember
  let restoredFields :=
    (gen.ruleFieldBinders constructor).map view.nested.restoreRec
  let restoredMinors := gen.minorTypes.map view.nested.restoreRec
  let restoredMotives := gen.motiveTypes.map view.nested.restoreRec
  let restoredParams := gen.paramsTel.map view.nested.restoreRec
  have contextShape : ruleContext =
      restoredFields.reverse ++ restoredMinors.reverse ++
        restoredMotives.reverse ++ restoredParams.reverse := by
    simp [ruleContext, restoredFields, restoredMinors, restoredMotives,
      restoredParams, BlockGenerationChecked.ruleBinders,
      BlockGenerationChecked.ruleFieldBinders, List.reverse_append,
      List.append_assoc]
  have fieldsLength : restoredFields.length = fieldCount := by
    simp [restoredFields, fieldCount,
      BlockGenerationChecked.ruleFieldBinders,
      BlockGenerationChecked.ruleFieldCount, VExpr.liftTelN_length]
  have minorsLength : restoredMinors.length = minorCount := by
    simp [restoredMinors, minorCount, gen.minorTypes_length]
  have motivesLength : restoredMotives.length = familyCount := by
    simp [restoredMotives, familyCount, gen.motiveTypes_length]
  have motiveAt : ruleContext[motiveIndex]? = some
      (view.nested.restoreRec
        ((gen.motiveType family).liftN family.view.ordinal)) := by
    rw [contextShape]
    let motivePrefix := restoredFields.reverse ++ restoredMinors.reverse
    rw [getElem?_stack_mid motivePrefix restoredMotives.reverse
      restoredParams.reverse (i := motiveIndex) (by
        simp [motivePrefix, motiveIndex, fieldsLength, minorsLength]
        omega) (by
        simp [motivePrefix, motiveIndex, fieldsLength, minorsLength,
          motivesLength]
        omega)]
    have reversedIndex : motiveIndex - motivePrefix.length =
        familyCount - 1 - constructor.owner := by
      simp [motivePrefix, motiveIndex, fieldsLength, minorsLength]
      omega
    rw [reversedIndex]
    rw [List.getElem?_reverse (by
      rw [motivesLength]
      omega)]
    rw [show restoredMotives.length - 1 -
        (familyCount - 1 - constructor.owner) = constructor.owner by
      rw [motivesLength]
      omega]
    simp [restoredMotives, familyOrdinal,
      gen.motiveTypes_getElem?_ordinal familyMember]
  have motiveLookup := Lookup.of_getElem? motiveAt
  have motiveExplicitRaw : env.HasType gen.recUvars ruleContext
      (.bvar motiveIndex)
      ((view.nested.restoreRec
        ((gen.motiveType family).liftN family.view.ordinal)).liftN
          (motiveIndex + 1)) :=
    VEnv.HasType.bvar motiveLookup
  have totalShift : family.view.ordinal + (motiveIndex + 1) =
      fieldCount + commonCount := by
    simp [motiveIndex, commonCount, familyCount, minorCount, familyOrdinal]
    omega
  have motiveExplicit : env.HasType gen.recUvars ruleContext
      (.bvar motiveIndex)
      (view.nested.restoreRec
        ((gen.motiveType family).liftN (fieldCount + commonCount))) := by
    unfold NestedBlockChecked.restoreRec at motiveExplicitRaw ⊢
    rw [VInductDecl.restoreExpr_liftN _ closed] at motiveExplicitRaw
    simpa [VExpr.liftN_liftN, totalShift] using motiveExplicitRaw
  have indexTelEmpty : gen.idxTel family = [] := by
    unfold BlockGenerationChecked.idxTel
    change (view.flatView.family.rawIndices
      view.flatView.source.nparams).map (VExpr.instL gen.sourceLevels) = []
    rw [view.flatView.raw_indices_eq]
    rfl
  have familyName : family.raw.name = view.name := by
    exact view.flatView_name
  have motiveTypeShape :
      view.nested.restoreRec
          ((gen.motiveType family).liftN (fieldCount + commonCount)) =
        .forallE
          (view.nested.restoreRec
            (VExpr.appN (.const view.name gen.sourceLevels)
              (VExpr.bvarRevRange (fieldCount + commonCount)
                view.nparams)))
          (.sort gen.motiveLevel) := by
    rw [gen.motiveType_liftN family, indexTelEmpty]
    rw [show view.nested.elim.flat.nparams = view.nparams from
      view.nested.elim.nparams_eq]
    simp only [VExpr.liftTelN, VExpr.forallN, List.length_nil,
      Nat.add_zero, VExpr.bvarRevRange, List.append_nil, familyName,
      NestedBlockChecked.restoreRec, VInductDecl.restoreExpr]
  rw [motiveTypeShape] at motiveExplicit
  have motiveTypeEq := henv.hasType_uniqU ruleCtx
    motiveWF motiveExplicit
  obtain ⟨⟨_, domainEq⟩, _⟩ :=
    henv.forallE_inv ruleCtx motiveTypeEq
  exact henv.hasType_defeqU_r ruleCtx ⟨_, domainEq⟩
    constructorWF

/-- Head safety turns the restored rule theorem into a literal typing
judgment for the selected source constructor and source family applications.
This is the semantic constructor-spine bridge used by restored projector
programs; neither endpoint retains an opaque restoration wrapper. -/
theorem FamilyLayoutWF.sourceRuleCtorApp_hasFamilyType
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.FamilyLayoutWF env) (henv : env.ConversionRegular)
    (closed : RestoreEntriesClosed view.nested.recEntries) :
    let gen := view.nested.generation
    let constructor := view.flatView.blockConstructor
    let fieldCount := gen.ruleFieldCount constructor
    let commonCount := gen.familyCount + gen.minorCount
    env.HasType gen.recUvars
      ((gen.ruleBinders constructor).map view.nested.restoreRec).reverse
      (VExpr.appN (.const view.constructorName gen.sourceLevels)
        (VExpr.bvarRevRange (fieldCount + commonCount) view.nparams ++
          VExpr.bvarRevRange 0 fieldCount))
      (VExpr.appN (.const view.name gen.sourceLevels)
        (VExpr.bvarRevRange
          (fieldCount + commonCount) view.nparams)) := by
  let gen := view.nested.generation
  let constructor := view.flatView.blockConstructor
  let fieldCount := gen.ruleFieldCount constructor
  let commonCount := gen.familyCount + gen.minorCount
  dsimp only
  have typed := self.restoredRuleCtorApp_hasFamilyType henv closed
  dsimp only at typed
  rw [view.restoreRec_ruleCtorApp] at typed
  rw [view.restoreRec_sourceFamilyApp gen.sourceLevels
    (fieldCount + commonCount)] at typed
  exact typed

/-- Internal early form of the restored constructor telescope split.  The
public syntax lemma is stated with the other arity facts below. -/
private theorem constructorFields_eq_core
    (view : VRestoredBlockStructureView) :
    ctorFields view.sourceConstructor.type =
      view.constructorParams ++ view.fields := by
  simpa [constructorParams, fields] using
    VExpr.ctorFields_eq_telN_append view.nparams
      view.sourceConstructor.type

/-- Registration of a restored rule exposes its complete restored binder
telescope as a well-formed telescope at recursor universes. -/
theorem LayoutWF.restoredRuleBinders_onTel
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.ConversionRegular) :
    let gen := view.nested.generation
    let constructor := view.flatView.blockConstructor
    env.OnTel gen.recUvars []
      ((gen.ruleBinders constructor).map view.nested.restoreRec) := by
  let gen := view.nested.generation
  let constructor := view.flatView.blockConstructor
  obtain ⟨ruleIndex, hentry⟩ :=
    List.mem_iff_getElem?.1 view.flatView.blockConstructor_mem
  have registered : env.defeqs
      (view.nested.restoredRule ruleIndex constructor) :=
    self.rules _ (view.nested.restoredRule_mem hentry)
  have ruleWF := henv.ordered.defEqWF registered
  obtain ⟨_, ruleTypeWF⟩ := ruleWF.1.isType henv.ordered (by trivial)
  have ruleTypeShape :
      (view.nested.restoredRule ruleIndex constructor).type =
        VExpr.forallN
          ((gen.ruleBinders constructor).map view.nested.restoreRec)
          (view.nested.restoreRec (gen.ruleResult constructor)) := by
    change view.nested.restoreRec
      ((gen.rule ruleIndex constructor).type) = _
    rw [gen.rule_type]
    unfold NestedBlockChecked.restoreRec
    rw [VInductDecl.restoreExpr_forallN]
    rfl
  have ruleUvars :
      (view.nested.restoredRule ruleIndex constructor).uvars =
        gen.recUvars := by
    change (gen.rule ruleIndex constructor).uvars = gen.recUvars
    exact gen.rule_uvars ruleIndex constructor
  rw [ruleTypeShape] at ruleTypeWF
  obtain ⟨ruleTel, _, _⟩ :=
    VEnv.HasType.forallN_wf henv.ordered ruleTypeWF
  rw [ruleUvars] at ruleTel
  exact ruleTel

/-- The restored rule telescope splits at the exact producer common/field
boundary, with its field suffix identified with the lifted source fields. -/
theorem LayoutWF.restoredRuleCommonFields_onTel
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.ConversionRegular)
    (closed : RestoreEntriesClosed view.nested.recEntries) :
    let gen := view.nested.generation
    let commonCount := gen.familyCount + gen.minorCount
    let commonBinders :=
      gen.ruleCommonBinders.map view.nested.restoreRec
    let sourceFields := view.fields.map (VExpr.instL gen.sourceLevels)
    let ruleFields := VExpr.liftTelN commonCount sourceFields 0
    env.OnTel gen.recUvars [] commonBinders ∧
      env.OnTel gen.recUvars commonBinders.reverse ruleFields := by
  let gen := view.nested.generation
  let constructor := view.flatView.blockConstructor
  let commonCount := gen.familyCount + gen.minorCount
  let commonBinders := gen.ruleCommonBinders.map view.nested.restoreRec
  let sourceFields := view.fields.map (VExpr.instL gen.sourceLevels)
  let ruleFields := VExpr.liftTelN commonCount sourceFields 0
  dsimp only
  have ruleTel := self.restoredRuleBinders_onTel henv
  dsimp only at ruleTel
  have fieldsEq := view.restoreRuleFieldBinders closed
  dsimp only at fieldsEq
  have bindersEq :
      (gen.ruleBinders constructor).map view.nested.restoreRec =
        commonBinders ++ ruleFields := by
    have ruleSplit : gen.ruleBinders constructor =
        gen.ruleCommonBinders ++ gen.ruleFieldBinders constructor := by
      simp [BlockGenerationChecked.ruleBinders,
        BlockGenerationChecked.ruleCommonBinders,
        BlockGenerationChecked.ruleFieldBinders, List.append_assoc]
    rw [ruleSplit, List.map_append, fieldsEq]
  rw [bindersEq] at ruleTel
  simpa only [List.append_nil] using VEnv.OnTel.of_append ruleTel

/-- The semantic full rule application and the registered source constructor
recover the constructor prefix at the smaller rule-common context.  Its raw
tail is stated before the rule-field lift is normalized. -/
theorem FamilyLayoutWF.sourceConstructorPrefix_hasRawType
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.FamilyLayoutWF env) (henv : env.ConversionRegular)
    (closed : RestoreEntriesClosed view.nested.recEntries) :
    let gen := view.nested.generation
    let commonCount := gen.familyCount + gen.minorCount
    let commonBinders := gen.ruleCommonBinders.map view.nested.restoreRec
    let sourceFields := view.fields.map (VExpr.instL gen.sourceLevels)
    let parameters := VExpr.bvarRevRange commonCount view.nparams
    env.HasType gen.recUvars commonBinders.reverse
      (VExpr.appN (.const view.constructorName gen.sourceLevels) parameters)
      (VExpr.instRev
        (VExpr.forallN sourceFields
          (view.sourceConstructor.type.resultOf.instL gen.sourceLevels))
        parameters) := by
  let gen := view.nested.generation
  let constructor := view.flatView.blockConstructor
  let fieldCount := gen.ruleFieldCount constructor
  let commonCount := gen.familyCount + gen.minorCount
  let commonBinders := gen.ruleCommonBinders.map view.nested.restoreRec
  let sourceFields := view.fields.map (VExpr.instL gen.sourceLevels)
  let ruleFields := VExpr.liftTelN commonCount sourceFields 0
  let parameters := VExpr.bvarRevRange commonCount view.nparams
  let fullParameters :=
    VExpr.bvarRevRange (fieldCount + commonCount) view.nparams
  let fields := VExpr.bvarRevRange 0 fieldCount
  let ctorPrefix :=
    VExpr.appN (.const view.constructorName gen.sourceLevels) parameters
  dsimp only
  have sourceFieldsLength : sourceFields.length = fieldCount := by
    have restored := view.restoreRuleRawFields
    dsimp only at restored
    have lengths := congrArg List.length restored
    simpa [sourceFields, fieldCount,
      BlockGenerationChecked.ruleFieldCount] using lengths.symm
  have ruleFieldsLength : ruleFields.length = fieldCount := by
    simpa [ruleFields, VExpr.liftTelN_length] using sourceFieldsLength
  obtain ⟨commonTel, fieldTel⟩ :=
    self.toLayoutWF.restoredRuleCommonFields_onTel henv closed
  have commonCtx : OnCtx commonBinders.reverse
      (env.IsType gen.recUvars) := by
    simpa only [List.append_nil] using
      VEnv.OnTel.onCtx (by trivial) commonTel
  have fullCtx : OnCtx (ruleFields.reverse ++ commonBinders.reverse)
      (env.IsType gen.recUvars) :=
    VEnv.OnTel.onCtx commonCtx fieldTel
  have semantic := self.sourceRuleCtorApp_hasFamilyType henv closed
  dsimp only at semantic
  have bindersEq :
      (gen.ruleBinders constructor).map view.nested.restoreRec =
        commonBinders ++ ruleFields := by
    rw [gen.ruleBinders_eq_common_append_fields, List.map_append]
    exact congrArg (commonBinders ++ ·)
      (view.restoreRuleFieldBinders closed)
  have semantic' : env.HasType gen.recUvars
      (ruleFields.reverse ++ commonBinders.reverse)
      (VExpr.appN
        (VExpr.appN (.const view.constructorName gen.sourceLevels)
          fullParameters) fields)
      (VExpr.appN (.const view.name gen.sourceLevels) fullParameters) := by
    rw [bindersEq, List.reverse_append] at semantic
    simpa only [VExpr.appN_append] using semantic
  obtain ⟨observedType, observedPrefix⟩ :=
    VEnv.HasType.appN_head_wf henv.ordered fullCtx semantic'
  have prefixLift : ctorPrefix.liftN fieldCount =
      VExpr.appN (.const view.constructorName gen.sourceLevels)
        fullParameters := by
    simp only [ctorPrefix, VExpr.liftN_appN, VExpr.liftN]
    apply congrArg (VExpr.appN (.const view.constructorName gen.sourceLevels))
    simpa [parameters, fullParameters] using
      VExpr.bvarRevRange_liftN_low view.nparams commonCount fieldCount
  have prefixFullWF : VExpr.WF env gen.recUvars
      (ruleFields.reverse ++ commonBinders.reverse)
      (ctorPrefix.liftN fieldCount) := by
    refine ⟨observedType, ?_⟩
    change env.HasType gen.recUvars
      (ruleFields.reverse ++ commonBinders.reverse)
      (ctorPrefix.liftN fieldCount) observedType
    simpa only [prefixLift] using observedPrefix
  have contextLift : Ctx.LiftN fieldCount 0 commonBinders.reverse
      (ruleFields.reverse ++ commonBinders.reverse) := by
    exact Ctx.LiftN.zero (n := fieldCount) (Γ := commonBinders.reverse)
      ruleFields.reverse (by simpa using ruleFieldsLength)
  have prefixWF : VExpr.WF env gen.recUvars commonBinders.reverse
      ctorPrefix :=
    (VExpr.WF.weakN_iff henv fullCtx contextLift).1 prefixFullWF
  obtain ⟨observedPrefixType, prefixTyped⟩ := prefixWF
  have constructorConst : env.HasType gen.recUvars commonBinders.reverse
      (.const view.constructorName gen.sourceLevels)
      (view.sourceConstructor.type.instL gen.sourceLevels) := by
    apply VEnv.HasType.const self.constructor gen.sourceLevels_wf
    exact gen.sourceLevels_length.trans view.flatView_uvars |>.trans
      view.constructor_uvars_eq.symm
  have constructorTypeShape : view.sourceConstructor.type =
      VExpr.forallN (view.constructorParams ++ view.fields)
        view.sourceConstructor.type.resultOf := by
    rw [← constructorFields_eq_core view,
      VInductDecl.forallN_ctorFields_resultOf]
  have constructorTypeInstShape :
      view.sourceConstructor.type.instL gen.sourceLevels =
        VExpr.forallN
          (view.constructorParams.map (VExpr.instL gen.sourceLevels))
          (VExpr.forallN sourceFields
            (view.sourceConstructor.type.resultOf.instL
              gen.sourceLevels)) := by
    calc
      view.sourceConstructor.type.instL gen.sourceLevels =
          (VExpr.forallN (view.constructorParams ++ view.fields)
            view.sourceConstructor.type.resultOf).instL
              gen.sourceLevels :=
        congrArg (VExpr.instL gen.sourceLevels) constructorTypeShape
      _ = _ := by
        rw [VExpr.instL_forallN, List.map_append,
          VExpr.forallN_append]
  have constructorConst' : env.HasType gen.recUvars commonBinders.reverse
      (.const view.constructorName gen.sourceLevels)
      (VExpr.forallN
        (view.constructorParams.map (VExpr.instL gen.sourceLevels))
        (VExpr.forallN sourceFields
          (view.sourceConstructor.type.resultOf.instL gen.sourceLevels))) := by
    rw [constructorTypeInstShape] at constructorConst
    exact constructorConst
  apply VEnv.HasType.appN_canonical henv commonCtx
    (binders := view.constructorParams.map (VExpr.instL gen.sourceLevels))
    (result := observedPrefixType)
  · simpa [parameters] using view.constructorParams_length.symm
  · exact constructorConst'
  · exact prefixTyped

/-- The restored source constructor prefix has the exact rule-field
telescope and literal restored-family result needed by operational projector
typing.  The result is obtained semantically from the registered restored
rule, without identifying the restored constructor with the flattened one. -/
theorem FamilyLayoutWF.sourceConstructorPrefix_hasType
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.FamilyLayoutWF env) (henv : env.ConversionRegular)
    (closed : RestoreEntriesClosed view.nested.recEntries) :
    let gen := view.nested.generation
    let commonCount := gen.familyCount + gen.minorCount
    let commonBinders := gen.ruleCommonBinders.map view.nested.restoreRec
    let sourceFields := view.fields.map (VExpr.instL gen.sourceLevels)
    let ruleFields := VExpr.liftTelN commonCount sourceFields 0
    let parameters := VExpr.bvarRevRange commonCount view.nparams
    env.HasType gen.recUvars commonBinders.reverse
      (VExpr.appN (.const view.constructorName gen.sourceLevels) parameters)
      (VExpr.forallN ruleFields
        ((VExpr.appN (.const view.name gen.sourceLevels) parameters).liftN
          ruleFields.length)) := by
  let gen := view.nested.generation
  let constructor := view.flatView.blockConstructor
  let fieldCount := gen.ruleFieldCount constructor
  let commonCount := gen.familyCount + gen.minorCount
  let commonBinders := gen.ruleCommonBinders.map view.nested.restoreRec
  let sourceFields := view.fields.map (VExpr.instL gen.sourceLevels)
  let ruleFields := VExpr.liftTelN commonCount sourceFields 0
  let parameters := VExpr.bvarRevRange commonCount view.nparams
  let fullParameters :=
    VExpr.bvarRevRange (fieldCount + commonCount) view.nparams
  let fields := VExpr.bvarRevRange 0 fieldCount
  let ctorPrefix :=
    VExpr.appN (.const view.constructorName gen.sourceLevels) parameters
  let familyPrefix :=
    VExpr.appN (.const view.name gen.sourceLevels) parameters
  let rawResult :=
    view.sourceConstructor.type.resultOf.instL gen.sourceLevels
  let rawTail := VExpr.forallN sourceFields rawResult
  let rawBody := rawResult.liftN commonCount sourceFields.length
  dsimp only
  have sourceFieldsLength : sourceFields.length = fieldCount := by
    have restored := view.restoreRuleRawFields
    dsimp only at restored
    have lengths := congrArg List.length restored
    simpa [sourceFields, fieldCount,
      BlockGenerationChecked.ruleFieldCount] using lengths.symm
  have ruleFieldsLength : ruleFields.length = fieldCount := by
    simpa [ruleFields, VExpr.liftTelN_length] using sourceFieldsLength
  obtain ⟨commonTel, fieldTel⟩ :=
    self.toLayoutWF.restoredRuleCommonFields_onTel henv closed
  have commonCtx : OnCtx commonBinders.reverse
      (env.IsType gen.recUvars) := by
    simpa only [List.append_nil] using
      VEnv.OnTel.onCtx (by trivial) commonTel
  have fullCtx : OnCtx (ruleFields.reverse ++ commonBinders.reverse)
      (env.IsType gen.recUvars) :=
    VEnv.OnTel.onCtx commonCtx fieldTel
  have constructorTypeShape : view.sourceConstructor.type =
      VExpr.forallN view.constructorParams
        (VExpr.forallN view.fields
          view.sourceConstructor.type.resultOf) := by
    rw [← VExpr.forallN_append, ← constructorFields_eq_core view,
      VInductDecl.forallN_ctorFields_resultOf]
  have constructorClosed : view.sourceConstructor.type.ClosedN :=
    henv.ordered.closedC self.constructor
  rw [constructorTypeShape] at constructorClosed
  have rawTailSourceClosed :
      (VExpr.forallN view.fields
        view.sourceConstructor.type.resultOf).ClosedN view.nparams := by
    have tail := VExpr.ClosedN.forallN_body constructorClosed
    simpa [view.constructorParams_length] using tail
  have rawTailClosed : rawTail.ClosedN view.nparams := by
    have instantiated := rawTailSourceClosed.instL
      (ls := gen.sourceLevels)
    simpa [rawTail, rawResult, sourceFields,
      VExpr.instL_forallN] using instantiated
  have parameterInstantiation : rawTail.instRev parameters =
      VExpr.forallN ruleFields rawBody := by
    calc
      rawTail.instRev parameters = rawTail.instRevAt parameters 0 :=
        (VExpr.instRevAt_zero rawTail parameters).symm
      _ = rawTail.liftN commonCount := by
        exact VExpr.instRevAt_bvarRevRange_eq_liftN rawTail
          commonCount view.nparams 0 (by simpa [parameters] using rawTailClosed)
      _ = VExpr.forallN ruleFields rawBody := by
        rw [VExpr.liftN_forallN]
        simp only [Nat.zero_add, ruleFields, rawBody]
  have rawPrefix := self.sourceConstructorPrefix_hasRawType henv closed
  dsimp only at rawPrefix
  have rawPrefixCanonical : env.HasType gen.recUvars commonBinders.reverse
      ctorPrefix (VExpr.forallN ruleFields rawBody) := by
    rw [parameterInstantiation] at rawPrefix
    exact rawPrefix
  have contextLift : Ctx.LiftN fieldCount 0 commonBinders.reverse
      (ruleFields.reverse ++ commonBinders.reverse) := by
    exact Ctx.LiftN.zero (n := fieldCount) (Γ := commonBinders.reverse)
      ruleFields.reverse (by simpa using ruleFieldsLength)
  have rawPrefixFull := rawPrefixCanonical.weakN henv.ordered contextLift
  have rawApplication := VEnv.HasType.appN_selfSpine
    (As := ruleFields) (B := rawBody) (Δ := [])
    (Γ := commonBinders.reverse) (f := ctorPrefix.liftN fieldCount)
    (by simpa only [List.nil_append, List.length_nil, Nat.zero_add,
      ruleFieldsLength] using rawPrefixFull)
  have ctorPrefixLift : ctorPrefix.liftN fieldCount =
      VExpr.appN (.const view.constructorName gen.sourceLevels)
        fullParameters := by
    simp only [ctorPrefix, VExpr.liftN_appN, VExpr.liftN]
    apply congrArg (VExpr.appN (.const view.constructorName gen.sourceLevels))
    simpa [parameters, fullParameters] using
      VExpr.bvarRevRange_liftN_low view.nparams commonCount fieldCount
  have rawApplication' : env.HasType gen.recUvars
      (ruleFields.reverse ++ commonBinders.reverse)
      (VExpr.appN
        (VExpr.appN (.const view.constructorName gen.sourceLevels)
          fullParameters) fields)
      rawBody := by
    simpa only [List.nil_append, List.length_nil, VExpr.liftN_zero,
      ctorPrefixLift, fields, ruleFieldsLength] using rawApplication
  have semantic := self.sourceRuleCtorApp_hasFamilyType henv closed
  dsimp only at semantic
  have bindersEq :
      (gen.ruleBinders constructor).map view.nested.restoreRec =
        commonBinders ++ ruleFields := by
    rw [gen.ruleBinders_eq_common_append_fields, List.map_append]
    exact congrArg (commonBinders ++ ·)
      (view.restoreRuleFieldBinders closed)
  have semantic' : env.HasType gen.recUvars
      (ruleFields.reverse ++ commonBinders.reverse)
      (VExpr.appN
        (VExpr.appN (.const view.constructorName gen.sourceLevels)
          fullParameters) fields)
      (VExpr.appN (.const view.name gen.sourceLevels) fullParameters) := by
    rw [bindersEq, List.reverse_append] at semantic
    simpa only [VExpr.appN_append] using semantic
  have bodyEqU := henv.hasType_uniqU fullCtx
    rawApplication' semantic'
  obtain ⟨rawSort, rawBodyType⟩ :=
    rawApplication'.isType henv.ordered fullCtx
  have bodyEq : env.IsDefEq gen.recUvars
      (ruleFields.reverse ++ commonBinders.reverse)
      rawBody
      (VExpr.appN (.const view.name gen.sourceLevels) fullParameters)
      (.sort rawSort) :=
    henv.isDefEqU_of_l fullCtx bodyEqU rawBodyType
  obtain ⟨prefixSort, prefixTypeEq⟩ :=
    fieldTel.telDefEq_refl.forallN_defeq bodyEq
  have desiredPrefix := henv.hasType_defeqU_r commonCtx
    ⟨.sort prefixSort, prefixTypeEq⟩ rawPrefixCanonical
  have familyPrefixLift : familyPrefix.liftN fieldCount =
      VExpr.appN (.const view.name gen.sourceLevels) fullParameters := by
    simp only [familyPrefix, VExpr.liftN_appN, VExpr.liftN]
    apply congrArg (VExpr.appN (.const view.name gen.sourceLevels))
    simpa [parameters, fullParameters] using
      VExpr.bvarRevRange_liftN_low view.nparams commonCount fieldCount
  change env.HasType gen.recUvars commonBinders.reverse ctorPrefix
    (VExpr.forallN ruleFields
      (familyPrefix.liftN ruleFields.length))
  simpa only [ruleFieldsLength, familyPrefixLift] using desiredPrefix

/-- Removing the producer's motive and minor binders from the exact restored
rule context exposes the source constructor at the canonical generated
parameter boundary.  This is the universe-polymorphic seed used by the
operational projection backend; no flattened constructor result is assumed. -/
theorem FamilyLayoutWF.sourceConstructorCanonicalPrefix_hasType
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.FamilyLayoutWF env) (henv : env.ConversionRegular)
    (closed : RestoreEntriesClosed view.nested.recEntries) :
    let gen := view.nested.generation
    let paramsBinders := gen.paramsTel.map view.nested.restoreRec
    let sourceFields := view.fields.map (VExpr.instL gen.sourceLevels)
    let parameters := VExpr.bvarRevRange 0 view.nparams
    env.HasType gen.recUvars paramsBinders.reverse
      (VExpr.appN (.const view.constructorName gen.sourceLevels) parameters)
      (VExpr.forallN sourceFields
        ((VExpr.appN (.const view.name gen.sourceLevels) parameters).liftN
          sourceFields.length)) := by
  let gen := view.nested.generation
  let commonCount := gen.familyCount + gen.minorCount
  let paramsBinders := gen.paramsTel.map view.nested.restoreRec
  let motiveBinders := gen.motiveTypes.map view.nested.restoreRec
  let minorBinders := gen.minorTypes.map view.nested.restoreRec
  let extraBinders := motiveBinders ++ minorBinders
  let commonBinders := gen.ruleCommonBinders.map view.nested.restoreRec
  let sourceFields := view.fields.map (VExpr.instL gen.sourceLevels)
  let ruleFields := VExpr.liftTelN commonCount sourceFields 0
  let parameters := VExpr.bvarRevRange 0 view.nparams
  let liftedParameters := VExpr.bvarRevRange commonCount view.nparams
  let ctorPrefix :=
    VExpr.appN (.const view.constructorName gen.sourceLevels) parameters
  let familyPrefix :=
    VExpr.appN (.const view.name gen.sourceLevels) parameters
  let baseType := VExpr.forallN sourceFields
    (familyPrefix.liftN sourceFields.length)
  dsimp only
  have extraLength : extraBinders.length = commonCount := by
    simp [extraBinders, motiveBinders, minorBinders, commonCount,
      gen.motiveTypes_length, gen.minorTypes_length]
  have commonEq : commonBinders = paramsBinders ++ extraBinders := by
    simp [commonBinders, paramsBinders, extraBinders, motiveBinders,
      minorBinders, BlockGenerationChecked.ruleCommonBinders,
      List.map_append, List.append_assoc]
  obtain ⟨commonTel, _⟩ :=
    self.toLayoutWF.restoredRuleCommonFields_onTel henv closed
  have commonCtx : OnCtx commonBinders.reverse
      (env.IsType gen.recUvars) := by
    simpa only [List.append_nil] using
      VEnv.OnTel.onCtx (by trivial) commonTel
  have commonCtx' : OnCtx (extraBinders.reverse ++ paramsBinders.reverse)
      (env.IsType gen.recUvars) := by
    simpa [commonEq, List.reverse_append] using commonCtx
  have contextLift : Ctx.LiftN commonCount 0 paramsBinders.reverse
      (extraBinders.reverse ++ paramsBinders.reverse) := by
    exact Ctx.LiftN.zero (n := commonCount) (Γ := paramsBinders.reverse)
      extraBinders.reverse (by simpa using extraLength)
  have exactPrefix := self.sourceConstructorPrefix_hasType henv closed
  dsimp only at exactPrefix
  change env.HasType gen.recUvars commonBinders.reverse
      (VExpr.appN (.const view.constructorName gen.sourceLevels)
        liftedParameters)
      (VExpr.forallN ruleFields
        ((VExpr.appN (.const view.name gen.sourceLevels)
          liftedParameters).liftN ruleFields.length)) at exactPrefix
  rw [commonEq, List.reverse_append] at exactPrefix
  have ctorLift : ctorPrefix.liftN commonCount =
      VExpr.appN (.const view.constructorName gen.sourceLevels)
        liftedParameters := by
    simp only [ctorPrefix, VExpr.liftN_appN, VExpr.liftN]
    apply congrArg (VExpr.appN (.const view.constructorName gen.sourceLevels))
    simpa [parameters, liftedParameters] using
      VExpr.bvarRevRange_liftN_low view.nparams 0 commonCount
  have familyLift : familyPrefix.liftN commonCount =
      VExpr.appN (.const view.name gen.sourceLevels)
        liftedParameters := by
    simp only [familyPrefix, VExpr.liftN_appN, VExpr.liftN]
    apply congrArg (VExpr.appN (.const view.name gen.sourceLevels))
    simpa [parameters, liftedParameters] using
      VExpr.bvarRevRange_liftN_low view.nparams 0 commonCount
  have typeLift : baseType.liftN commonCount =
      VExpr.forallN ruleFields
        ((VExpr.appN (.const view.name gen.sourceLevels)
          liftedParameters).liftN ruleFields.length) := by
    rw [VExpr.liftN_forallN]
    simp only [ruleFields, VExpr.liftTelN_length]
    rw [← familyLift]
    congr 1
    simp only [Nat.zero_add]
    rw [VExpr.liftN'_liftN'
      (e := familyPrefix) (n1 := sourceFields.length)
      (n2 := commonCount) (k1 := 0) (k2 := sourceFields.length)
      (Nat.zero_le _) (Nat.le_refl _)]
    rw [VExpr.liftN_liftN]
    congr 1
    omega
  have lifted : env.HasType gen.recUvars
      (extraBinders.reverse ++ paramsBinders.reverse)
      (ctorPrefix.liftN commonCount) (baseType.liftN commonCount) := by
    simpa only [ctorLift, typeLift] using exactPrefix
  exact (VEnv.HasType.weakN_iff henv commonCtx' contextLift).1 lifted

/-- The exact generated parameter prefix restored from the registered rule is
a well-formed telescope in the recursor universe context. -/
theorem FamilyLayoutWF.restoredParams_onTel
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.FamilyLayoutWF env) (henv : env.ConversionRegular)
    (closed : RestoreEntriesClosed view.nested.recEntries) :
    env.OnTel view.nested.generation.recUvars []
      (view.nested.generation.paramsTel.map view.nested.restoreRec) := by
  let gen := view.nested.generation
  let paramsBinders := gen.paramsTel.map view.nested.restoreRec
  let motiveBinders := gen.motiveTypes.map view.nested.restoreRec
  let minorBinders := gen.minorTypes.map view.nested.restoreRec
  let commonBinders := gen.ruleCommonBinders.map view.nested.restoreRec
  obtain ⟨commonTel, _⟩ :=
    self.toLayoutWF.restoredRuleCommonFields_onTel henv closed
  have commonEq : commonBinders =
      paramsBinders ++ motiveBinders ++ minorBinders := by
    simp [commonBinders, paramsBinders, motiveBinders, minorBinders,
      BlockGenerationChecked.ruleCommonBinders, List.map_append,
      List.append_assoc]
  change env.OnTel gen.recUvars [] commonBinders at commonTel
  rw [commonEq] at commonTel
  exact (VEnv.OnTel.of_append (VEnv.OnTel.of_append commonTel).1).1

/-- The registered restored iota rule exposes the legacy common recursor
binder surface as a complete self-spine of the exact generated recursor.  For
the selected structure family both raw and generated index telescopes are
empty, so uniqueness of typing recovers the complete raw/exact telescope
comparison and hence the restored recursor-type equality. -/
theorem FamilyLayoutWF.restoredRecType_generated_defeq
    {view : VRestoredBlockStructureView} {env flatEnv : VEnv}
    (self : view.FamilyLayoutWF env) (henv : env.WF)
    (flatGeneration :
      VInductDecl.BlockGenerationEnv view.nested.generation flatEnv)
    (closed : RestoreEntriesClosed view.nested.recEntries) :
    ∃ sortLevel, env.IsDefEq view.nested.generation.recUvars []
      (view.nested.restoreRec
        (view.nested.generation.recType view.selection.family))
      view.recursor.type (.sort sortLevel) := by
  let gen := view.nested.generation
  let family := view.selection.family
  let constructor := view.flatView.blockConstructor
  let fieldCount := gen.ruleFieldCount constructor
  let rawCommon := gen.ruleCommonBinders.map view.nested.restoreRec
  let exactCommon :=
    (gen.paramsTel ++ gen.generatedMotiveTypes ++
      gen.generatedMinorTypes).map view.nested.restoreRec
  have familyMember : family ∈ gen.families :=
    view.flatView.family_mem
  have rawIndicesEmpty : gen.idxTel family = [] := by
    unfold BlockGenerationChecked.idxTel
    change (view.flatView.family.rawIndices
      view.flatView.source.nparams).map (VExpr.instL gen.sourceLevels) = []
    rw [view.flatView.raw_indices_eq]
    rfl
  have generatedIndicesEmpty : gen.generatedIdxTel family = [] := by
    apply List.length_eq_zero_iff.1
    rw [← flatGeneration.generatedIdxTel_length familyMember,
      rawIndicesEmpty]
    rfl
  let terminal : VExpr :=
    view.nested.restoreRec <|
      .forallE
        (VExpr.appN (.const family.raw.name gen.sourceLevels)
          (VExpr.bvarRevRange (gen.familyCount + gen.minorCount)
            view.nested.elim.flat.nparams))
        (.app
          (.bvar (gen.familyCount - 1 - family.view.ordinal +
            gen.minorCount + 1))
          (.bvar 0))
  have rawTypeShape :
      view.nested.restoreRec (gen.recType family) =
        VExpr.forallN rawCommon terminal := by
    simp [rawCommon, terminal, BlockGenerationChecked.recType,
      BlockGenerationChecked.ruleCommonBinders, rawIndicesEmpty,
      NestedBlockChecked.restoreRec, VInductDecl.restoreExpr_forallN,
      VExpr.forallN_append, VExpr.liftTelN, VExpr.bvarRevRange,
      VExpr.appN, VExpr.forallN, List.map_append]
    rfl
  have exactTypeShape : view.recursor.type =
      VExpr.forallN exactCommon terminal := by
    have generatedIndicesEmpty' :
        view.nested.generation.generatedIdxTel view.selection.family = [] := by
      simpa only [gen, family] using generatedIndicesEmpty
    rw [show view.recursor.type = view.nested.restoreRec
        (view.nested.generation.generatedRecType view.selection.family) by
      rfl,
      BlockGenerationChecked.generatedRecType, generatedIndicesEmpty']
    simp [VRestoredBlockStructureView.recursor,
      VRestoredBlockStructureView.flatRecursor,
      BlockGenerationChecked.generatedRecursor,
      exactCommon, terminal,
      NestedBlockChecked.restoreRec,
      VInductDecl.restoreExpr_forallN, VExpr.forallN_append,
      VExpr.liftTelN, VExpr.bvarRevRange, VExpr.appN, VExpr.forallN,
      List.map_append]
    rfl
  have rawCommonTel : env.OnTel gen.recUvars [] rawCommon := by
    obtain ⟨commonTel, _⟩ :=
      self.toLayoutWF.restoredRuleCommonFields_onTel henv closed
    exact commonTel
  have exactType : env.IsType gen.recUvars [] view.recursor.type := by
    obtain ⟨sortLevel, typed⟩ := henv.ordered.constWF self.recursor
    refine ⟨sortLevel, ?_⟩
    simpa [VRestoredBlockStructureView.recursor,
      VRestoredBlockStructureView.flatRecursor,
      BlockGenerationChecked.generatedRecursor] using typed
  have exactCommonTel : env.OnTel gen.recUvars [] exactCommon := by
    have exactType' := exactType
    rw [exactTypeShape] at exactType'
    exact (VEnv.IsType.forallN_inv henv.ordered exactType').1
  have commonLength : rawCommon.length = exactCommon.length := by
    simp [rawCommon, exactCommon, BlockGenerationChecked.ruleCommonBinders,
      gen.motiveTypes_length, gen.generatedMotiveTypes_length,
      gen.minorTypes_length, gen.generatedMinorTypes_length]
  obtain ⟨ruleIndex, ruleEntry⟩ :=
    List.mem_iff_getElem?.1 view.flatView.blockConstructor_mem
  have registered : env.defeqs
      (view.nested.restoredRule ruleIndex constructor) :=
    self.rules _ (view.nested.restoredRule_mem ruleEntry)
  have ruleWF := henv.ordered.defEqWF registered
  have lhsShape :
      (view.nested.restoredRule ruleIndex constructor).lhs =
        VExpr.lamN
          ((gen.ruleBinders constructor).map view.nested.restoreRec)
          (view.nested.restoreRec (gen.ruleLhsBody constructor)) := by
    change view.nested.restoreRec (gen.rule ruleIndex constructor).lhs = _
    rw [gen.rule_lhs]
    unfold NestedBlockChecked.restoreRec
    rw [VInductDecl.restoreExpr_lamN]
  have lhsWF := ruleWF.1
  rw [lhsShape] at lhsWF
  have ruleUvars :
      (view.nested.restoredRule ruleIndex constructor).uvars =
        gen.recUvars := by
    change (gen.rule ruleIndex constructor).uvars = gen.recUvars
    exact gen.rule_uvars ruleIndex constructor
  rw [ruleUvars] at lhsWF
  obtain ⟨_, observedType, lhsBodyType⟩ :=
    VEnv.HasType.lamN_wf henv.ordered (by trivial) lhsWF
  have ruleRecursorName : gen.ruleRecName constructor =
      view.recursorName := by
    rw [BlockGenerationChecked.ruleRecName]
    change (.str (gen.familyNameAt family.view.ordinal) "rec" : Name) =
      view.recursorName
    rw [show gen.familyNameAt family.view.ordinal = view.flatView.name by
      simpa only [gen, family, VRestoredBlockStructureView.flatView] using
        view.flatView.familyNameAt_ordinal]
    exact view.flatView_recursorName
  have resultIndices : constructor.ctor.view.resultIndices = [] := by
    apply List.length_eq_zero_iff.1
    rw [gen.view_resultIndices_length view.flatView.blockConstructor_mem]
    simp [VBlockStructureView.blockConstructor,
      view.flatView.checked_indices_eq]
  have ruleIndices : gen.ruleIdx constructor = [] := by
    simp [BlockGenerationChecked.ruleIdx,
      NormalizedCtor.resultIndicesR, resultIndices]
  have recursorInert : RestoreInert view.nested.recEntries
      view.nested.recMap (.const view.recursorName gen.recLevels) := by
    simpa [VRestoredBlockStructureView.recursorName] using
      view.nested.sourceRecursorName_restoreRecInert
        view.sourceFamily_mem gen.recLevels
  have constructorInert : RestoreInert view.nested.recEntries
      view.nested.recMap
      (.const view.constructorName gen.sourceLevels) := by
    exact view.nested.sourceConstructorName_restoreRecInert
      view.sourceFamily_mem view.sourceConstructor_mem gen.sourceLevels
  have lhsInert : RestoreInert view.nested.recEntries view.nested.recMap
      (gen.ruleLhsBody constructor) := by
    have recBaseInert : RestoreInert view.nested.recEntries
        view.nested.recMap
        (gen.recBase fieldCount constructor.owner) := by
      rw [BlockGenerationChecked.recBase,
        show (.str (gen.familyNameAt constructor.owner) "rec" : Name) =
            view.recursorName by
          simpa only [BlockGenerationChecked.ruleRecName] using
            ruleRecursorName]
      apply recursorInert.appN
      intro argument member
      exact bvarRevRange_restoreInert _ _ _ _ argument member
    have constructorAppInert : RestoreInert view.nested.recEntries
        view.nested.recMap (gen.ruleCtorApp constructor) := by
      rw [BlockGenerationChecked.ruleCtorApp,
        show constructor.ctor.raw.name = view.constructorName from
          view.flatView_constructorName]
      apply constructorInert.appN
      intro argument member
      rcases List.mem_append.mp member with parameter | field
      · exact bvarRevRange_restoreInert _ _ _ _ argument parameter
      · exact bvarRevRange_restoreInert _ _ _ _ argument field
    rw [BlockGenerationChecked.ruleLhsBody, ruleIndices]
    simp only [List.nil_append]
    apply recBaseInert.appN
    intro argument member
    simp only [List.mem_singleton] at member
    subst argument
    exact constructorAppInert
  have restoredLhs : view.nested.restoreRec (gen.ruleLhsBody constructor) =
      gen.ruleLhsBody constructor := lhsInert.restoreExpr_eq
  let commonArgs := VExpr.bvarRevRange fieldCount rawCommon.length
  have commonArgsEq : commonArgs =
      VExpr.bvarRevRange (gen.ruleFieldCount constructor)
        (view.nested.elim.flat.nparams + gen.familyCount +
          gen.minorCount) := by
    simp [commonArgs, fieldCount, rawCommon,
      gen.ruleCommonBinders_length]
  have lhsBodyShape :
      view.nested.restoreRec (gen.ruleLhsBody constructor) =
        .app
          (VExpr.appN (.const view.recursorName gen.recLevels) commonArgs)
          (gen.ruleCtorApp constructor) := by
    rw [restoredLhs, BlockGenerationChecked.ruleLhsBody, ruleIndices,
      List.nil_append, BlockGenerationChecked.recBase,
      show (.str (gen.familyNameAt constructor.owner) "rec" : Name) =
          view.recursorName by
        simpa only [BlockGenerationChecked.ruleRecName] using
          ruleRecursorName,
      ← commonArgsEq]
    simp [VExpr.appN]
  rw [lhsBodyShape] at lhsBodyType
  let ruleBinders :=
    (gen.ruleBinders constructor).map view.nested.restoreRec
  have ruleContext : OnCtx ruleBinders.reverse
      (env.IsType gen.recUvars) := by
    have ruleTel := self.toLayoutWF.restoredRuleBinders_onTel henv
    simpa [ruleBinders] using
      VEnv.OnTel.onCtx (Γ := []) (by trivial) ruleTel
  have lhsBodyType' : env.HasType gen.recUvars ruleBinders.reverse
      (.app
        (VExpr.appN (.const view.recursorName gen.recLevels) commonArgs)
        (gen.ruleCtorApp constructor)) observedType := by
    simpa [ruleBinders] using lhsBodyType
  obtain ⟨_, _, partialApplication, _⟩ :=
    lhsBodyType'.app_inv henv.ordered ruleContext
  have exactTypeLevelWF : view.recursor.type.LevelWF gen.recUvars := by
    obtain ⟨_, typed⟩ := exactType
    exact (typed.levelWF trivial).1
  have headType : env.HasType gen.recUvars ruleBinders.reverse
      (.const view.recursorName gen.recLevels) view.recursor.type := by
    have typed := VEnv.HasType.const (env := env) (U := gen.recUvars)
      (Γ := ruleBinders.reverse) self.recursor VLevel.params_wf
        VLevel.params_length
    rw [exactTypeLevelWF.instL_id] at typed
    simpa [VRestoredBlockStructureView.recursor,
      VRestoredBlockStructureView.flatRecursor,
      BlockGenerationChecked.generatedRecursor] using typed
  have exactSpineFull : env.SpineWF gen.recUvars ruleBinders.reverse
      (VExpr.forallN exactCommon terminal) commonArgs
      (VExpr.instRev terminal commonArgs) := by
    apply VEnv.HasType.appN_canonicalSpine henv ruleContext
      (binders := exactCommon) (arguments := commonArgs)
      (function := .const view.recursorName gen.recLevels)
    · simpa [commonArgs] using commonLength
    · simpa only [exactTypeShape] using headType
    · exact partialApplication
  have exactDummySpineFull : env.SpineWF gen.recUvars ruleBinders.reverse
      (VExpr.forallN exactCommon (.sort .zero)) commonArgs (.sort .zero) := by
    have retargeted := exactSpineFull.retarget
      (by simpa [commonArgs] using commonLength) (.sort .zero)
    have sortInst : (VExpr.sort .zero).instRev commonArgs = .sort .zero :=
      VExpr.instRev_closedN _ (by trivial)
    rw [sortInst] at retargeted
    exact retargeted
  let rawFields :=
    (gen.ruleFieldBinders constructor).map view.nested.restoreRec
  have ruleBindersEq : ruleBinders = rawCommon ++ rawFields := by
    simp [ruleBinders, rawCommon, rawFields,
      gen.ruleBinders_eq_common_append_fields, List.map_append]
  have rawFieldsLength : rawFields.length = fieldCount := by
    simp [rawFields, fieldCount, BlockGenerationChecked.ruleFieldBinders,
      BlockGenerationChecked.ruleFieldCount, VExpr.liftTelN_length]
  have fullContextShape : ruleBinders.reverse =
      rawFields.reverse ++ rawCommon.reverse := by
    rw [ruleBindersEq, List.reverse_append]
  have contextLift : Ctx.LiftN fieldCount 0 rawCommon.reverse
      ruleBinders.reverse := by
    rw [fullContextShape]
    exact Ctx.LiftN.zero (n := fieldCount) (Γ := rawCommon.reverse)
      rawFields.reverse (by simpa using rawFieldsLength)
  have exactDummyType : env.IsType gen.recUvars []
      (VExpr.forallN exactCommon (.sort .zero)) := by
    apply VEnv.IsType.forallN exactCommonTel
    exact ⟨_, VEnv.HasType.sort (by trivial)⟩
  have exactDummyClosed :
      (VExpr.forallN exactCommon (.sort .zero)).ClosedN 0 := by
    obtain ⟨sortLevel, typed⟩ := exactDummyType
    exact VExpr.WF.closedN henv.ordered ⟨.sort sortLevel, typed⟩ trivial
  have exactDummySpineLifted : env.SpineWF gen.recUvars
      ruleBinders.reverse
      ((VExpr.forallN exactCommon (.sort .zero)).liftN fieldCount)
      ((VExpr.bvarRevRange 0 rawCommon.length).map
        (fun argument => argument.liftN fieldCount))
      ((.sort .zero : VExpr).liftN fieldCount) := by
    simpa [commonArgs, exactDummyClosed.liftN_eq (Nat.zero_le _),
      VExpr.bvarRevRange_liftN_low, VExpr.liftN] using
        exactDummySpineFull
  have exactDummySpine : env.SpineWF gen.recUvars rawCommon.reverse
      (VExpr.forallN exactCommon (.sort .zero))
      (VExpr.bvarRevRange 0 rawCommon.length) (.sort .zero) :=
    VEnv.SpineWF.weakN_inv henv ruleContext contextLift
      exactDummySpineLifted
  have exactDummySpineForTelescope : env.SpineWF gen.recUvars
      (rawCommon.reverse ++ [])
      ((VExpr.forallN exactCommon (.sort .zero)).liftN rawCommon.length)
      (VExpr.bvarRevRange 0 rawCommon.length) (.sort .zero) := by
    simpa [exactDummyClosed.liftN_eq (Nat.zero_le _)] using
      exactDummySpine
  have telescope : env.TelDefEq gen.recUvars [] exactCommon rawCommon :=
    VEnv.TelDefEq.of_bvarRevRange_spine henv (by trivial)
      rawCommonTel exactCommonTel commonLength exactDummySpineForTelescope
  rw [rawTypeShape, exactTypeShape]
  obtain ⟨sortLevel, bridge⟩ :=
    telescope.forallN_defeq_self_right henv.ordered (by
      rw [← exactTypeShape]
      exact exactType)
  exact ⟨sortLevel, bridge.symm⟩

theorem FamilyLayoutWF.mono {view : VRestoredBlockStructureView}
    {env env' : VEnv} (hle : env ≤ env')
    (self : view.FamilyLayoutWF env) : view.FamilyLayoutWF env' where
  toLayoutWF := self.toLayoutWF.mono hle
  familyWF := self.familyWF.mono hle

theorem ConstructorParameterLayoutWF.mono
    {view : VRestoredBlockStructureView} {env env' : VEnv}
    (hle : env ≤ env') (self : view.ConstructorParameterLayoutWF env) :
    view.ConstructorParameterLayoutWF env' where
  toFamilyLayoutWF := self.toFamilyLayoutWF.mono hle
  constructorParamsDefEq := self.constructorParamsDefEq.mono hle
  recursorTypeDefEq := by
    obtain ⟨sortLevel, bridge⟩ := self.recursorTypeDefEq
    exact ⟨sortLevel, bridge.mono hle⟩

/-- Complete the restored constructor-parameter layer from a comparison
proved on the exact flattened raw prefix.  The flattener's literal-prefix
invariant performs the only reindexing; no semantic restoration transport is
used here. -/
theorem FamilyLayoutWF.withFlatConstructorParameters
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.FamilyLayoutWF env)
    (flat : env.TelDefEq view.uvars [] view.flatView.constructorParams
      view.nested.generation.block.checked.params)
    (recursorTypeDefEq : ∃ sortLevel, env.IsDefEq
      view.nested.generation.recUvars []
      (view.nested.restoreRec
        (view.nested.generation.recType view.selection.family))
      view.recursor.type (.sort sortLevel)) :
    view.ConstructorParameterLayoutWF env where
  toFamilyLayoutWF := self
  constructorParamsDefEq := by
    rw [← view.flatView_constructorParams]
    exact flat
  recursorTypeDefEq := recursorTypeDefEq

/-- The raw operational recursor type is closed because it is definitionally
equal to the exact registered restored recursor type. -/
theorem ConstructorParameterLayoutWF.restoredRawRecType_closedN
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.ConstructorParameterLayoutWF env) (henv : env.Ordered) :
    (view.nested.restoreRec
      (view.nested.generation.recType view.selection.family)).ClosedN 0 := by
  obtain ⟨sortLevel, bridge⟩ := self.recursorTypeDefEq
  exact VExpr.WF.closedN henv ⟨.sort sortLevel, bridge.hasType.1⟩ trivial

/-- A registered exact restored recursor may be consumed through the raw
operational type at any well-formed universe instantiation. -/
theorem ConstructorParameterLayoutWF.restoredRawRecursor_hasType
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.ConstructorParameterLayoutWF env) (henv : env.Ordered)
    {U : Nat} {context : List VExpr} {levels : List VLevel}
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.nested.generation.recUvars) :
    env.HasType U context (.const view.recursorName levels)
      ((view.nested.restoreRec
        (view.nested.generation.recType view.selection.family)).instL
          levels) := by
  have registered : env.HasType U context
      (.const view.recursorName levels) (view.recursor.type.instL levels) := by
    apply VEnv.HasType.const self.recursor hlevels
    simpa [VRestoredBlockStructureView.recursor,
      VRestoredBlockStructureView.flatRecursor,
      BlockGenerationChecked.generatedRecursor] using hlevelsLength
  obtain ⟨_, bridge⟩ := self.recursorTypeDefEq
  exact ((bridge.instL hlevels).weak0 henv).defeq' registered

/-- The registered restored family type is definitionally equal to the
projection-facing type at the validator-owned common result sort. -/
theorem FamilyLayoutWF.rawFamilyType_defeq_familyType
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.FamilyLayoutWF env) :
    ∃ sortLevel, env.IsDefEq view.uvars []
      view.rawFamilyType view.familyType (.sort sortLevel) := by
  have hfamilyWF : view.flatView.family.WF view.flatView.generation env :=
    self.familyWF
  have htel := hfamilyWF.familyTel.raw_onTel.telDefEq_refl
  have hresult : env.IsDefEq view.flatView.uvars
      ((view.flatView.family.rawParams view.flatView.nparams ++
        view.flatView.family.rawIndices view.flatView.nparams).reverse ++ [])
      (view.flatView.family.rawResult view.flatView.nparams)
      (.sort view.flatView.resultLevel)
      (.sort (.succ view.flatView.resultLevel)) := by
    simpa [VBlockStructureView.resultLevel] using hfamilyWF.familyResult
  obtain ⟨sortLevel, hforall⟩ := htel.forallN_defeq hresult
  have hflat : env.IsDefEq view.flatView.uvars []
      view.flatView.rawFamilyType view.flatView.familyType
      (.sort sortLevel) := by
    have hrawType := VInductDecl.NormalizedFamily.rawType_eq
      (source := view.flatView.source) view.flatView.family
    simpa [VBlockStructureView.rawFamilyType,
      VBlockStructureView.familyType, hrawType,
      view.flatView.raw_indices_eq, VExpr.forallN_append,
      VExpr.forallN] using hforall
  refine ⟨sortLevel, ?_⟩
  simpa only [view.flatView_uvars, view.flatView_rawFamilyType,
    view.flatView_familyType] using hflat

/-- Type the exact restored family constant at its projection-facing type. -/
theorem FamilyLayoutWF.familyConst_hasType
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.FamilyLayoutWF env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars) :
    env.HasType U Γ (.const view.name levels)
      (view.familyType.instL levels) := by
  obtain ⟨_, htype⟩ := self.rawFamilyType_defeq_familyType
  have htypeLevels := htype.instL hlevels
  have hraw : env.HasType U [] (.const view.name levels)
      (view.rawFamilyType.instL levels) := by
    apply VEnv.HasType.const self.family hlevels
    simpa using hlevelsLength.trans view.family_uvars_eq.symm
  exact (htypeLevels.defeq hraw).weak0 henv

/-- The restored projection-facing family type is syntactically closed. -/
theorem FamilyLayoutWF.familyType_closed
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.FamilyLayoutWF env) (henv : env.Ordered) :
    view.familyType.ClosedN := by
  obtain ⟨_, htype⟩ := self.rawFamilyType_defeq_familyType
  exact (htype.closedN' henv.closed trivial).2.1

/-- The selected family exposes the exact checked common parameter
telescope at the restored endpoint. -/
theorem FamilyLayoutWF.parameters
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.FamilyLayoutWF env) (henv : env.Ordered) :
    env.OnTel view.uvars [] view.nested.generation.block.checked.params := by
  have familyTel := self.familyWF.familyTel.view_onTel henv
  have flatParameters : env.OnTel view.nested.elim.flat.uvars []
      view.nested.generation.block.checked.params := by
    simpa [view.selection.checked_indices_eq] using familyTel
  have uvarsEq : view.nested.elim.flat.uvars = view.uvars := by
    simpa using congrArg VInductDecl.uvars view.nested.elim.flat_eq
  simpa only [uvarsEq] using flatParameters

/-- The restored raw family parameter telescope and the producer's checked
common parameter telescope are definitionally equal.  This is the precise
family-side semantic fragment retained from flattened staging. -/
theorem FamilyLayoutWF.rawParams_defeq_checkedParams
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.FamilyLayoutWF env) :
    env.TelDefEq view.nested.elim.flat.uvars []
      (view.selection.family.rawParams view.nested.elim.flat.nparams)
      view.nested.generation.block.checked.params := by
  simpa only [view.selection.flat_raw_indices_eq,
    view.selection.checked_indices_eq, List.append_nil] using
    self.familyWF.familyTel

/-- Parameters accepted by the restored family consume the exact checked
common-parameter prefix retained by the flattened producer. -/
theorem FamilyLayoutWF.checkedParamsSpine
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.FamilyLayoutWF env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (_hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (target : VExpr) :
    env.SpineWF U Γ
      (VExpr.forallN
        (view.nested.generation.block.checked.params.map
          (VExpr.instL levels)) target)
      params (VExpr.instRev target params) := by
  obtain ⟨resultLevel, hspine⟩ := paramsSpine
  rw [← view.flatView_familyType] at hspine
  have hrawLength :
      (view.selection.family.rawParams
        view.nested.elim.flat.nparams).length = view.nparams := by
    have flatLength := view.flatView.raw_params_length
    have exactLength :
        (view.selection.family.rawParams
          view.nested.elim.flat.nparams).length =
            view.nested.elim.flat.nparams := by
      simpa only [VRestoredBlockStructureView.flatView] using flatLength
    exact exactLength.trans view.nested.elim.nparams_eq
  have hparamsRawLength : params.length =
      (view.selection.family.rawParams
        view.nested.elim.flat.nparams).length :=
    hparamsLength.trans hrawLength.symm
  have hspineShape : env.SpineWF U Γ
      (VExpr.forallN
        ((view.selection.family.rawParams
          view.nested.elim.flat.nparams).map (VExpr.instL levels))
        (.sort (view.flatView.resultLevel.inst levels)))
      params (.sort resultLevel) := by
    simpa [VBlockStructureView.familyType,
      VRestoredBlockStructureView.flatView, VExpr.instL_forallN,
      VExpr.instL] using hspine
  have hparamsRaw : env.SpineWF U Γ
      (VExpr.forallN
        ((view.selection.family.rawParams
          view.nested.elim.flat.nparams).map (VExpr.instL levels))
        (.sort .zero))
      params (.sort .zero) := by
    have hout := hspineShape.retarget
      (by simpa only [List.length_map] using hparamsRawLength)
      (.sort .zero)
    rw [VExpr.instRev_closedN params (by trivial)] at hout
    exact hout
  have hfamilyDefEq := self.rawParams_defeq_checkedParams.instL hlevels
  have hrawLift : VExpr.liftTelN Γ.length
      ((view.selection.family.rawParams
        view.nested.elim.flat.nparams).map (VExpr.instL levels)) 0 =
      (view.selection.family.rawParams
        view.nested.elim.flat.nparams).map (VExpr.instL levels) := by
    simpa using VEnv.OnTel.liftTelN_eq henv
      hfamilyDefEq.raw_onTel (by trivial) Γ.length
  have hcheckedLift : VExpr.liftTelN Γ.length
      (view.nested.generation.block.checked.params.map
        (VExpr.instL levels)) 0 =
      view.nested.generation.block.checked.params.map
        (VExpr.instL levels) := by
    simpa using VEnv.OnTel.liftTelN_eq henv
      (hfamilyDefEq.view_onTel henv) (by trivial) Γ.length
  have hfamilyDefEqΓ := hfamilyDefEq.weakN henv
    (Ctx.LiftN.zero (n := Γ.length) (Γ := []) Γ)
  rw [hrawLift, hcheckedLift] at hfamilyDefEqΓ
  simp only [List.append_nil] at hfamilyDefEqΓ
  have hparamsChecked : env.SpineWF U Γ
      (VExpr.forallN
        (view.nested.generation.block.checked.params.map
          (VExpr.instL levels)) (.sort .zero))
      params (.sort .zero) :=
    VEnv.TelDefEq.spine_sort_view henv hfamilyDefEqΓ hparamsRaw
      (by simpa only [List.length_map] using hparamsRawLength)
  have hcheckedLength : params.length =
      (view.nested.generation.block.checked.params.map
        (VExpr.instL levels)).length := by
    have hcheckedParamsLength :
        view.nested.generation.block.checked.params.length = view.nparams :=
      view.flatView.checked_params_length.trans view.flatView_nparams
    simpa only [List.length_map] using
      hparamsLength.trans hcheckedParamsLength.symm
  exact hparamsChecked.retarget hcheckedLength target

/-- Family parameters accepted at the restored surface consume the stored
source constructor's parameter prefix once the producer supplies their exact
telescope alignment. -/
theorem ConstructorParameterLayoutWF.constructorParamsSpine
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.ConstructorParameterLayoutWF env) (henv : env.Ordered)
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
        (view.constructorParams.map (VExpr.instL levels)) target)
      params (VExpr.instRev target params) := by
  have hparamsChecked := self.toFamilyLayoutWF.checkedParamsSpine henv
    levels hlevels hlevelsLength params hparamsLength paramsSpine (.sort .zero)
  rw [VExpr.instRev_closedN params (by trivial)] at hparamsChecked
  have hconstructorDefEq := self.constructorParamsDefEq.instL hlevels
  have hconstructorRawLift : VExpr.liftTelN Γ.length
      (view.constructorParams.map (VExpr.instL levels)) 0 =
      view.constructorParams.map (VExpr.instL levels) := by
    simpa using VEnv.OnTel.liftTelN_eq henv
      hconstructorDefEq.raw_onTel (by trivial) Γ.length
  have hconstructorCheckedLift : VExpr.liftTelN Γ.length
      (view.nested.generation.block.checked.params.map
        (VExpr.instL levels)) 0 =
      view.nested.generation.block.checked.params.map
        (VExpr.instL levels) := by
    simpa using VEnv.OnTel.liftTelN_eq henv
      (hconstructorDefEq.view_onTel henv) (by trivial) Γ.length
  have hconstructorDefEqΓ := hconstructorDefEq.weakN henv
    (Ctx.LiftN.zero (n := Γ.length) (Γ := []) Γ)
  rw [hconstructorRawLift, hconstructorCheckedLift] at hconstructorDefEqΓ
  simp only [List.append_nil] at hconstructorDefEqΓ
  have hconstructorLength : params.length =
      (view.constructorParams.map (VExpr.instL levels)).length := by
    simpa only [List.length_map] using
      hparamsLength.trans view.constructorParams_length.symm
  have hout := VEnv.TelDefEq.spine_sort henv hconstructorDefEqΓ
    hparamsChecked hconstructorLength
  exact hout.retarget hconstructorLength target

/-- Recover the restored family parameter spine from a source-constructor
parameter prefix.  Both source prefixes are compared through the exact
checked common-parameter telescope retained by the flattened producer. -/
theorem ConstructorParameterLayoutWF.familyParamsSpine_of_constructor
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.ConstructorParameterLayoutWF env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (_hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    {target cursor : VExpr}
    (constructorSpine : env.SpineWF U Γ
      (VExpr.forallN
        (view.constructorParams.map (VExpr.instL levels)) target)
      params cursor) :
    env.SpineWF U Γ (view.familyType.instL levels) params
      (.sort (view.resultLevel.inst levels)) := by
  have hconstructorLength : params.length =
      (view.constructorParams.map (VExpr.instL levels)).length := by
    simpa only [List.length_map] using
      hparamsLength.trans view.constructorParams_length.symm
  have hparamsConstructor : env.SpineWF U Γ
      (VExpr.forallN
        (view.constructorParams.map (VExpr.instL levels)) (.sort .zero))
      params (.sort .zero) := by
    have hout := constructorSpine.retarget hconstructorLength (.sort .zero)
    rw [VExpr.instRev_closedN params (by trivial)] at hout
    exact hout
  have hfamilyDefEq :=
    self.toFamilyLayoutWF.rawParams_defeq_checkedParams.instL hlevels
  have hconstructorDefEq := self.constructorParamsDefEq.instL hlevels
  have hrawLift : VExpr.liftTelN Γ.length
      ((view.selection.family.rawParams
        view.nested.elim.flat.nparams).map (VExpr.instL levels)) 0 =
      (view.selection.family.rawParams
        view.nested.elim.flat.nparams).map (VExpr.instL levels) := by
    simpa using VEnv.OnTel.liftTelN_eq henv
      hfamilyDefEq.raw_onTel (by trivial) Γ.length
  have hcheckedLift : VExpr.liftTelN Γ.length
      (view.nested.generation.block.checked.params.map
        (VExpr.instL levels)) 0 =
      view.nested.generation.block.checked.params.map
        (VExpr.instL levels) := by
    simpa using VEnv.OnTel.liftTelN_eq henv
      (hfamilyDefEq.view_onTel henv) (by trivial) Γ.length
  have hconstructorRawLift : VExpr.liftTelN Γ.length
      (view.constructorParams.map (VExpr.instL levels)) 0 =
      view.constructorParams.map (VExpr.instL levels) := by
    simpa using VEnv.OnTel.liftTelN_eq henv
      hconstructorDefEq.raw_onTel (by trivial) Γ.length
  have hfamilyDefEqΓ := hfamilyDefEq.weakN henv
    (Ctx.LiftN.zero (n := Γ.length) (Γ := []) Γ)
  rw [hrawLift, hcheckedLift] at hfamilyDefEqΓ
  simp only [List.append_nil] at hfamilyDefEqΓ
  have hconstructorDefEqΓ := hconstructorDefEq.weakN henv
    (Ctx.LiftN.zero (n := Γ.length) (Γ := []) Γ)
  rw [hconstructorRawLift, hcheckedLift] at hconstructorDefEqΓ
  simp only [List.append_nil] at hconstructorDefEqΓ
  have hrawParamsEq :
      view.selection.family.rawParams view.nested.elim.flat.nparams =
        view.rawParams := by
    change VExpr.telN view.flatView.nparams view.flatView.rawFamilyType =
      VExpr.telN view.nparams view.rawFamilyType
    rw [view.flatView_nparams, view.flatView_rawFamilyType]
  have hparamsChecked : env.SpineWF U Γ
      (VExpr.forallN
        (view.nested.generation.block.checked.params.map
          (VExpr.instL levels)) (.sort .zero))
      params (.sort .zero) :=
    VEnv.TelDefEq.spine_sort_view henv hconstructorDefEqΓ
      hparamsConstructor hconstructorLength
  have hrawParamsLength : params.length =
      ((view.selection.family.rawParams
        view.nested.elim.flat.nparams).map (VExpr.instL levels)).length := by
    simpa only [List.length_map, hrawParamsEq] using
      hparamsLength.trans view.rawParams_length.symm
  have hparamsRaw : env.SpineWF U Γ
      (VExpr.forallN
        ((view.selection.family.rawParams
          view.nested.elim.flat.nparams).map (VExpr.instL levels))
        (.sort .zero))
      params (.sort .zero) :=
    VEnv.TelDefEq.spine_sort henv hfamilyDefEqΓ hparamsChecked
      hrawParamsLength
  have hout := hparamsRaw.retarget hrawParamsLength
    (.sort (view.resultLevel.inst levels))
  rw [VExpr.instRev_closedN params (by trivial)] at hout
  rw [hrawParamsEq] at hout
  simpa [VRestoredBlockStructureView.familyType_eq_forallN,
    VExpr.instL_forallN, VExpr.instL] using hout

/-- The registered restored family application at the canonical generated
parameter variables yields the exact family-parameter spine consumed by the
projection-facing family type. -/
theorem FamilyLayoutWF.canonicalFamilyParamsSpine
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.FamilyLayoutWF env) (henv : env.ConversionRegular)
    (closed : RestoreEntriesClosed view.nested.recEntries) :
    let gen := view.nested.generation
    let paramsBinders := gen.paramsTel.map view.nested.restoreRec
    let parameters := VExpr.bvarRevRange 0 view.nparams
    ∃ resultLevel, env.SpineWF gen.recUvars paramsBinders.reverse
      (view.familyType.instL gen.sourceLevels) parameters
      (.sort resultLevel) := by
  let gen := view.nested.generation
  let paramsBinders := gen.paramsTel.map view.nested.restoreRec
  let sourceFields := view.fields.map (VExpr.instL gen.sourceLevels)
  let parameters := VExpr.bvarRevRange 0 view.nparams
  let familyPrefix :=
    VExpr.appN (.const view.name gen.sourceLevels) parameters
  dsimp only
  have paramsTel := self.restoredParams_onTel henv closed
  have paramsCtx : OnCtx paramsBinders.reverse
      (env.IsType gen.recUvars) := by
    simpa only [List.append_nil] using
      VEnv.OnTel.onCtx (by trivial) paramsTel
  have hprefix := self.sourceConstructorCanonicalPrefix_hasType henv closed
  dsimp only at hprefix
  have prefixIsType := hprefix.isType henv.ordered paramsCtx
  obtain ⟨fieldTel, familyFull⟩ :=
    VEnv.IsType.forallN_inv henv.ordered prefixIsType
  have fieldsCtx : OnCtx (sourceFields.reverse ++ paramsBinders.reverse)
      (env.IsType gen.recUvars) :=
    VEnv.OnTel.onCtx paramsCtx fieldTel
  have contextLift : Ctx.LiftN sourceFields.length 0 paramsBinders.reverse
      (sourceFields.reverse ++ paramsBinders.reverse) :=
    Ctx.LiftN.zero sourceFields.reverse (by simp)
  change env.IsType gen.recUvars
    (sourceFields.reverse ++ paramsBinders.reverse)
    (familyPrefix.liftN sourceFields.length) at familyFull
  have familyIsType : env.IsType gen.recUvars paramsBinders.reverse
      familyPrefix :=
    (VEnv.IsType.weakN_iff henv fieldsCtx contextLift).1 familyFull
  obtain ⟨resultLevel, familyTyped⟩ := familyIsType
  have familyConst := self.familyConst_hasType (Γ := paramsBinders.reverse)
    henv.ordered gen.sourceLevels gen.sourceLevels_wf
    (gen.sourceLevels_length.trans view.flatView_uvars)
  have familyConst' : env.HasType gen.recUvars paramsBinders.reverse
      (.const view.name gen.sourceLevels)
      (VExpr.forallN
        (view.rawParams.map (VExpr.instL gen.sourceLevels))
        (.sort (view.resultLevel.inst gen.sourceLevels))) := by
    simpa [familyType_eq_forallN, VExpr.instL_forallN,
      VExpr.instL] using familyConst
  have spine := VEnv.HasType.appN_canonicalSpine henv paramsCtx
    (binders := view.rawParams.map (VExpr.instL gen.sourceLevels))
    (arguments := parameters)
    (function := .const view.name gen.sourceLevels)
    (body := .sort (view.resultLevel.inst gen.sourceLevels))
    (by simp [parameters, view.rawParams_length])
    familyConst' familyTyped
  rw [VExpr.instRev_closedN parameters (by trivial)] at spine
  exact ⟨view.resultLevel.inst gen.sourceLevels, by
    simpa [familyType_eq_forallN, VExpr.instL_forallN,
      VExpr.instL] using spine⟩

/-- Registration of the restored source constructor recovers its complete
parameter prefix as a well-formed telescope. -/
theorem LayoutWF.constructorParams_onTel
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.Ordered) :
    env.OnTel view.uvars [] view.constructorParams := by
  obtain ⟨sortLevel, constructorType⟩ := henv.constWF self.constructor
  have constructorTypeWF : env.IsType view.sourceConstructor.uvars []
      view.sourceConstructor.type := ⟨sortLevel, constructorType⟩
  rw [view.constructor_uvars_eq] at constructorTypeWF
  have telescope := VEnv.IsType.ctorFields_onTel henv constructorTypeWF
  rw [VExpr.ctorFields_eq_telN_append view.nparams
    view.sourceConstructor.type] at telescope
  simpa [constructorParams] using (VEnv.OnTel.of_append telescope).1

/-- The source constructor parameters and the generated parameter telescope
restored from the exact rule are structurally definitionally equal.  The
proof derives this bridge from the canonical family and constructor spines;
it does not assume restoration is syntactically inert on generated params. -/
theorem ConstructorParameterLayoutWF.restoredParamsDefEq
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.ConstructorParameterLayoutWF env) (henv : env.ConversionRegular)
    (closed : RestoreEntriesClosed view.nested.recEntries) :
    let gen := view.nested.generation
    env.TelDefEq gen.recUvars []
      (view.constructorParams.map (VExpr.instL gen.sourceLevels))
      (gen.paramsTel.map view.nested.restoreRec) := by
  let gen := view.nested.generation
  let restoredParams := gen.paramsTel.map view.nested.restoreRec
  let constructorParams :=
    view.constructorParams.map (VExpr.instL gen.sourceLevels)
  let parameters := VExpr.bvarRevRange 0 view.nparams
  dsimp only
  have restoredTel :=
    self.toFamilyLayoutWF.restoredParams_onTel henv closed
  obtain ⟨familySort, familySpine⟩ :=
    self.toFamilyLayoutWF.canonicalFamilyParamsSpine henv closed
  have hlevelsLength : gen.sourceLevels.length = view.uvars :=
    gen.sourceLevels_length.trans view.flatView_uvars
  have constructorSpine := self.constructorParamsSpine henv.ordered
    gen.sourceLevels gen.sourceLevels_wf hlevelsLength parameters
    (by simp [parameters]) ⟨familySort, familySpine⟩ (.sort .zero)
  rw [VExpr.instRev_closedN parameters (by trivial)] at constructorSpine
  have constructorTel : env.OnTel gen.recUvars [] constructorParams := by
    have sourceTel := self.toLayoutWF.constructorParams_onTel henv.ordered
    simpa [constructorParams] using sourceTel.instL gen.sourceLevels_wf
  have constructorTowerType : env.IsType gen.recUvars []
      (VExpr.forallN constructorParams (.sort .zero)) := by
    apply VEnv.IsType.forallN constructorTel
    exact ⟨.succ .zero, VEnv.HasType.sort trivial⟩
  have constructorTowerClosed :
      (VExpr.forallN constructorParams (.sort .zero)).ClosedN := by
    obtain ⟨_, typed⟩ := constructorTowerType
    exact typed.closedN henv.ordered trivial
  have constructorSpine' : env.SpineWF gen.recUvars restoredParams.reverse
      ((VExpr.forallN constructorParams (.sort .zero)).liftN
        restoredParams.length)
      parameters (.sort .zero) := by
    rw [constructorTowerClosed.liftN_eq (Nat.zero_le _)]
    exact constructorSpine
  apply VEnv.TelDefEq.of_bvarRevRange_spine henv
    (Γ := []) (As := restoredParams) (Bs := constructorParams)
    (by trivial) restoredTel constructorTel
  · have generationParamsLength : gen.paramsTel.length = view.nparams := by
      calc
        gen.paramsTel.length =
            gen.generatedParams.length := by
          simp [BlockGenerationChecked.paramsTel]
        _ = view.nested.elim.flat.nparams := gen.generatedParams_length
        _ = view.nparams := view.flatView_nparams
    simp [restoredParams, constructorParams, generationParamsLength,
      view.constructorParams_length]
  · have restoredLength : restoredParams.length = view.nparams := by
      have generationParamsLength : gen.paramsTel.length = view.nparams := by
        calc
          gen.paramsTel.length =
              gen.generatedParams.length := by
            simp [BlockGenerationChecked.paramsTel]
          _ = view.nested.elim.flat.nparams := gen.generatedParams_length
          _ = view.nparams := view.flatView_nparams
      simpa [restoredParams] using generationParamsLength
    simpa [parameters, restoredLength] using constructorSpine'

/-- Source parameters accepted by the public restored family consume the
exact restored parameter prefix of the flattened recursor at any operational
universe spine.  This is the parameter segment of the direct restored
recursor-typing path; later motive and minor proofs can start at the precise
generated cursor instead of reconstructing a singleton generation. -/
theorem ConstructorParameterLayoutWF.restoredParamsSpine
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.ConstructorParameterLayoutWF env) (henv : env.ConversionRegular)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    {U : Nat} {context : List VExpr}
    (fieldSort : VLevel) (hfieldSort : fieldSort.WF U)
    (levels : List VLevel) (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U context (view.familyType.instL levels)
        params (.sort resultLevel))
    (target : VExpr) :
    let gen := view.nested.generation
    let projectionLevels :=
      view.flatView.projectionLevels fieldSort levels
    let restoredParamsAt :=
      (gen.paramsTel.map view.nested.restoreRec).map
        (VExpr.instL projectionLevels)
    env.SpineWF U context (VExpr.forallN restoredParamsAt target)
      params (VExpr.instRev target params) := by
  let gen := view.nested.generation
  let projectionLevels :=
    view.flatView.projectionLevels fieldSort levels
  let restoredParams := gen.paramsTel.map view.nested.restoreRec
  let restoredParamsAt := restoredParams.map (VExpr.instL projectionLevels)
  let constructorParams := view.constructorParams.map (VExpr.instL levels)
  dsimp only
  have projectionLevelsWF : ∀ level ∈ projectionLevels, level.WF U := by
    change ∀ level ∈
      (match gen.elimination with
      | .large => fieldSort :: levels
      | .small => levels), level.WF U
    cases gen.elimination with
    | large =>
      intro level member
      have member' : level = fieldSort ∨ level ∈ levels := by
        simpa using member
      exact member'.elim (fun equal => equal ▸ hfieldSort)
        (hlevels level)
    | small =>
      intro level member
      exact hlevels level (by simpa using member)
  have sourceLevels :
      gen.sourceLevels.map (VLevel.inst projectionLevels) = levels := by
    simpa [gen, projectionLevels, VRestoredBlockStructureView.flatView] using
      view.flatView.sourceLevels_projectionLevels fieldSort levels
        (by simpa only [view.flatView_uvars] using hlevelsLength)
  have paramsDefEq₀ := self.restoredParamsDefEq henv closed
  dsimp only at paramsDefEq₀
  have paramsDefEqL := paramsDefEq₀.instL projectionLevelsWF
  have constructorParamsAt :
      (view.constructorParams.map (VExpr.instL gen.sourceLevels)).map
          (VExpr.instL projectionLevels) = constructorParams := by
    simp [constructorParams, List.map_map, Function.comp_def,
      VExpr.instL_instL, sourceLevels]
  have paramsDefEq : env.TelDefEq U [] constructorParams
      restoredParamsAt := by
    change env.TelDefEq U []
      ((view.constructorParams.map (VExpr.instL gen.sourceLevels)).map
        (VExpr.instL projectionLevels)) restoredParamsAt at paramsDefEqL
    rw [constructorParamsAt] at paramsDefEqL
    exact paramsDefEqL
  have constructorSpine := self.constructorParamsSpine henv.ordered
    levels hlevels hlevelsLength params hparamsLength paramsSpine (.sort .zero)
  rw [VExpr.instRev_closedN params (by trivial)] at constructorSpine
  have constructorLift : VExpr.liftTelN context.length
      constructorParams 0 = constructorParams := by
    simpa using VEnv.OnTel.liftTelN_eq henv.ordered
      paramsDefEq.raw_onTel (by trivial) context.length
  have restoredLift : VExpr.liftTelN context.length
      restoredParamsAt 0 = restoredParamsAt := by
    simpa using VEnv.OnTel.liftTelN_eq henv.ordered
      (paramsDefEq.view_onTel henv.ordered) (by trivial) context.length
  have paramsDefEqContext := paramsDefEq.weakN henv.ordered
    (Ctx.LiftN.zero (n := context.length) (Γ := []) context)
  rw [constructorLift, restoredLift] at paramsDefEqContext
  simp only [List.append_nil] at paramsDefEqContext
  have hlength : params.length = constructorParams.length := by
    simpa [constructorParams] using
      hparamsLength.trans view.constructorParams_length.symm
  have restoredLength : restoredParamsAt.length = constructorParams.length :=
    paramsDefEq.length_eq.symm
  have hrestoredLength : params.length = restoredParamsAt.length :=
    hlength.trans restoredLength.symm
  have restoredSpine : env.SpineWF U context
      (VExpr.forallN restoredParamsAt (.sort .zero)) params (.sort .zero) :=
    VEnv.TelDefEq.spine_sort_view henv paramsDefEqContext
      (by simpa [constructorParams] using constructorSpine)
      (by simpa using hlength)
  exact restoredSpine.retarget hrestoredLength target

/-- Every per-family restored motive domain is closed over exactly the
source parameter telescope.  This is recovered from the registered restored
recursor itself, so the operational motive bridge needs no separate producer
closedness assumption. -/
theorem ConstructorParameterLayoutWF.restoredMotiveType_closedN
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.ConstructorParameterLayoutWF env) (henv : env.ConversionRegular)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    (family : NormalizedFamily)
    (hfamily : family ∈ view.nested.generation.families)
    (levels : List VLevel) :
    (view.nested.restoreRecAt levels
      ((view.nested.generation.motiveType family).instL levels)).ClosedN
        view.nparams := by
  let gen := view.nested.generation
  let selected := view.selection.family
  let minorTail :=
    VExpr.forallN gen.minorTypes <|
      VExpr.forallN
        (VExpr.liftTelN (gen.familyCount + gen.minorCount)
          (gen.idxTel selected) 0) <|
        .forallE
          (VExpr.appN (.const selected.raw.name gen.sourceLevels)
            (VExpr.bvarRevRange
                ((gen.idxTel selected).length + gen.familyCount +
                  gen.minorCount) view.nested.elim.flat.nparams ++
              VExpr.bvarRevRange 0 (gen.idxTel selected).length)) <|
          .app
            (VExpr.appN
              (.bvar (gen.familyCount - 1 - selected.view.ordinal +
                gen.minorCount + (gen.idxTel selected).length + 1))
              (VExpr.bvarRevRange 1 (gen.idxTel selected).length))
            (.bvar 0)
  have recursorClosed' :
      (view.nested.restoreRec (gen.recType selected)).ClosedN 0 := by
    simpa [gen, selected] using
      self.restoredRawRecType_closedN henv.ordered
  have recShape : gen.recType selected =
      VExpr.forallN gen.paramsTel
        (VExpr.forallN gen.motiveTypes minorTail) := by
    rfl
  rw [recShape] at recursorClosed'
  unfold NestedBlockChecked.restoreRec at recursorClosed'
  rw [VInductDecl.restoreExpr_forallN,
    VInductDecl.restoreExpr_forallN] at recursorClosed'
  have motiveTelescopeClosed₀ :=
    VExpr.ClosedN.forallN_body recursorClosed'
  have genParamsLength : gen.paramsTel.length = view.nparams := by
    simp only [BlockGenerationChecked.paramsTel, List.length_map]
    exact gen.generatedParams_length.trans view.nested.elim.nparams_eq
  have motiveTelescopeClosed :
      (VExpr.forallN
        (gen.motiveTypes.map
          (VInductDecl.restoreExpr view.nested.recEntries
            view.nested.recMap))
        (VInductDecl.restoreExpr view.nested.recEntries
          view.nested.recMap minorTail)).ClosedN view.nparams := by
    simpa [List.length_map, genParamsLength] using
      motiveTelescopeClosed₀
  have motiveFound :
      (gen.motiveTypes.map
        (VInductDecl.restoreExpr view.nested.recEntries
          view.nested.recMap))[family.view.ordinal]? =
        some (VInductDecl.restoreExpr view.nested.recEntries
          view.nested.recMap
          ((gen.motiveType family).liftN family.view.ordinal)) := by
    rw [List.getElem?_map, gen.motiveTypes_getElem?_ordinal hfamily]
    rfl
  have liftedClosed :=
    motiveTelescopeClosed.forallN_getElem? motiveFound
  rw [← VInductDecl.restoreExpr_liftN view.nested.recEntries closed
    view.nested.recMap (gen.motiveType family) family.view.ordinal 0]
    at liftedClosed
  have baseClosed :
      (VInductDecl.restoreExpr view.nested.recEntries view.nested.recMap
        (gen.motiveType family)).ClosedN view.nparams := by
    exact VExpr.ClosedN.of_liftN liftedClosed (Nat.zero_le view.nparams)
  have instantiated := VExpr.ClosedN.instL (ls := levels) baseClosed
  rw [VInductDecl.restoreExpr_instL] at instantiated
  simpa [NestedBlockChecked.restoreRecAt] using instantiated

/-- Every restored minor domain is closed over exactly the source parameters
and family-motive inventory.  As for motives, this is recovered directly
from the registered restored recursor telescope. -/
theorem ConstructorParameterLayoutWF.restoredMinorType_closedN
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.ConstructorParameterLayoutWF env) (henv : env.ConversionRegular)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    (constructor : NormalizedBlockCtor)
    (hconstructor : constructor ∈ view.nested.generation.flatCtors)
    (levels : List VLevel) :
    (view.nested.restoreRecAt levels
      ((view.nested.generation.minorType constructor).instL levels)).ClosedN
        (view.nparams + view.nested.generation.familyCount) := by
  let gen := view.nested.generation
  let selected := view.selection.family
  let majorTail :=
    VExpr.forallN
      (VExpr.liftTelN (gen.familyCount + gen.minorCount)
        (gen.idxTel selected) 0) <|
      .forallE
        (VExpr.appN (.const selected.raw.name gen.sourceLevels)
          (VExpr.bvarRevRange
              ((gen.idxTel selected).length + gen.familyCount +
                gen.minorCount) view.nested.elim.flat.nparams ++
            VExpr.bvarRevRange 0 (gen.idxTel selected).length)) <|
        .app
          (VExpr.appN
            (.bvar (gen.familyCount - 1 - selected.view.ordinal +
              gen.minorCount + (gen.idxTel selected).length + 1))
            (VExpr.bvarRevRange 1 (gen.idxTel selected).length))
          (.bvar 0)
  have recursorClosed' :
      (view.nested.restoreRec (gen.recType selected)).ClosedN 0 := by
    simpa [gen, selected] using
      self.restoredRawRecType_closedN henv.ordered
  have recShape : gen.recType selected =
      VExpr.forallN gen.paramsTel
        (VExpr.forallN gen.motiveTypes
          (VExpr.forallN gen.minorTypes majorTail)) := by
    rfl
  rw [recShape] at recursorClosed'
  unfold NestedBlockChecked.restoreRec at recursorClosed'
  rw [VInductDecl.restoreExpr_forallN,
    VInductDecl.restoreExpr_forallN,
    VInductDecl.restoreExpr_forallN] at recursorClosed'
  have minorTelescopeClosed0 :=
    VExpr.ClosedN.forallN_body
      (VExpr.ClosedN.forallN_body recursorClosed')
  have genParamsLength : gen.paramsTel.length = view.nparams := by
    simp only [BlockGenerationChecked.paramsTel, List.length_map]
    exact gen.generatedParams_length.trans view.nested.elim.nparams_eq
  have minorTelescopeClosed :
      (VExpr.forallN
        (gen.minorTypes.map
          (VInductDecl.restoreExpr view.nested.recEntries
            view.nested.recMap))
        (VInductDecl.restoreExpr view.nested.recEntries
          view.nested.recMap majorTail)).ClosedN
          (view.nparams + gen.familyCount) := by
    simpa [List.length_map, genParamsLength, gen.motiveTypes_length,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        minorTelescopeClosed0
  obtain ⟨index, constructorAt⟩ := List.mem_iff_getElem?.1 hconstructor
  have minorFound :
      (gen.minorTypes.map
        (VInductDecl.restoreExpr view.nested.recEntries
          view.nested.recMap))[index]? =
        some (VInductDecl.restoreExpr view.nested.recEntries
          view.nested.recMap ((gen.minorType constructor).liftN index)) := by
    rw [List.getElem?_map,
      show gen.minorTypes = gen.minorTypesAux gen.flatCtors 0 from rfl,
      gen.minorTypesAux_getElem?, constructorAt]
    simp
  have liftedClosed := minorTelescopeClosed.forallN_getElem? minorFound
  rw [← VInductDecl.restoreExpr_liftN view.nested.recEntries closed
    view.nested.recMap (gen.minorType constructor) index 0] at liftedClosed
  have baseClosed :
      (VInductDecl.restoreExpr view.nested.recEntries view.nested.recMap
        (gen.minorType constructor)).ClosedN
          (view.nparams + gen.familyCount) := by
    exact VExpr.ClosedN.of_liftN liftedClosed
      (Nat.zero_le (view.nparams + gen.familyCount))
  have instantiated := VExpr.ClosedN.instL (ls := levels) baseClosed
  rw [VInductDecl.restoreExpr_instL] at instantiated
  simpa [NestedBlockChecked.restoreRecAt] using instantiated

/-- Applying the registered restored recursor through its source parameters
reaches the exact restored, universe-specialized, progressively
parameter-specialized motive telescope.  The post-motive tail remains
existential, while every motive domain is exposed at the cursor where it is
consumed. -/
theorem ConstructorParameterLayoutWF.restoredRecursorParamsSpine
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.ConstructorParameterLayoutWF env) (henv : env.ConversionRegular)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    {U : Nat} {context : List VExpr}
    (fieldSort : VLevel) (hfieldSort : fieldSort.WF U)
    (levels : List VLevel) (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U context (view.familyType.instL levels)
        params (.sort resultLevel)) :
    let gen := view.nested.generation
    let projectionLevels :=
      view.flatView.projectionLevels fieldSort levels
    let restoredMotiveBinders :=
      (gen.motiveTypes.map view.nested.restoreRec).map
        (VExpr.instL projectionLevels)
    ∃ tail, env.SpineWF U context
      ((view.nested.restoreRec
        (gen.recType view.selection.family)).instL projectionLevels)
      params
      (VExpr.forallN
        (restoredMotiveBinders.zipIdx.map fun entry =>
          entry.1.instRevAt params entry.2)
        tail) := by
  let gen := view.nested.generation
  let projectionLevels :=
    view.flatView.projectionLevels fieldSort levels
  let minorTail :=
    VExpr.forallN gen.minorTypes <|
      VExpr.forallN
        (VExpr.liftTelN (gen.familyCount + gen.minorCount)
          (gen.idxTel view.selection.family) 0) <|
        .forallE
          (VExpr.appN
            (.const view.selection.family.raw.name gen.sourceLevels)
            (VExpr.bvarRevRange
                ((gen.idxTel view.selection.family).length +
                  gen.familyCount + gen.minorCount)
                view.nested.elim.flat.nparams ++
              VExpr.bvarRevRange 0
                (gen.idxTel view.selection.family).length)) <|
          .app
            (VExpr.appN
              (.bvar
                (gen.familyCount - 1 -
                  view.selection.family.view.ordinal + gen.minorCount +
                  (gen.idxTel view.selection.family).length + 1))
              (VExpr.bvarRevRange 1
                (gen.idxTel view.selection.family).length))
            (.bvar 0)
  let recTail := VExpr.forallN gen.motiveTypes minorTail
  let restoredTail := (view.nested.restoreRec recTail).instL projectionLevels
  let restoredParamsAt :=
    (gen.paramsTel.map view.nested.restoreRec).map
      (VExpr.instL projectionLevels)
  let restoredMotiveBinders :=
    (gen.motiveTypes.map view.nested.restoreRec).map
      (VExpr.instL projectionLevels)
  let restoredMinorTail :=
    (view.nested.restoreRec minorTail).instL projectionLevels
  have recShape : gen.recType view.selection.family =
      VExpr.forallN gen.paramsTel recTail := by
    rfl
  have restoredShape :
      (view.nested.restoreRec
        (gen.recType view.selection.family)).instL projectionLevels =
      VExpr.forallN restoredParamsAt restoredTail := by
    rw [recShape]
    unfold NestedBlockChecked.restoreRec
    rw [VInductDecl.restoreExpr_forallN, VExpr.instL_forallN]
    rfl
  have paramsTyped := self.restoredParamsSpine henv closed fieldSort
    hfieldSort levels hlevels hlevelsLength params hparamsLength paramsSpine
      restoredTail
  have paramsFull : env.SpineWF U context
      ((view.nested.restoreRec
        (gen.recType view.selection.family)).instL projectionLevels)
      params (VExpr.instRev restoredTail params) := by
    rw [restoredShape]
    simpa [gen, projectionLevels, restoredParamsAt] using paramsTyped
  have restoredTailShape : restoredTail =
      VExpr.forallN restoredMotiveBinders restoredMinorTail := by
    unfold restoredTail recTail restoredMinorTail restoredMotiveBinders
    unfold NestedBlockChecked.restoreRec
    rw [VInductDecl.restoreExpr_forallN, VExpr.instL_forallN]
  rw [restoredTailShape, VExpr.instRev_forallN_projection] at paramsFull
  exact ⟨_, paramsFull⟩

/-- Operational form of `restoredRecursorParamsSpine`: the exposed cursor is
the progressive telescope over the per-family restored base motive domains.
This is the form consumed by pointwise motive typing. -/
theorem ConstructorParameterLayoutWF.restoredRecursorOperationalMotiveSpine
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.ConstructorParameterLayoutWF env) (henv : env.ConversionRegular)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    {U : Nat} {context : List VExpr}
    (fieldSort : VLevel) (hfieldSort : fieldSort.WF U)
    (levels : List VLevel) (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U context (view.familyType.instL levels)
        params (.sort resultLevel)) :
    let gen := view.nested.generation
    let projectionLevels :=
      view.flatView.projectionLevels fieldSort levels
    ∃ tail, env.SpineWF U context
      ((view.nested.restoreRec
        (gen.recType view.selection.family)).instL projectionLevels)
      params
      (VExpr.forallN
        ((view.operationalProjectionMotiveTypes fieldSort levels params).zipIdx.map
          fun entry => entry.1.liftN entry.2)
        tail) := by
  have cursor := self.restoredRecursorParamsSpine henv closed fieldSort
    hfieldSort levels hlevels hlevelsLength params hparamsLength paramsSpine
  dsimp only at cursor ⊢
  obtain ⟨tail, cursor⟩ := cursor
  rw [view.restoredMotiveBinders_specialize closed fieldSort levels params]
    at cursor
  exact ⟨tail, cursor⟩

/-- Exact operational form of the parameter cursor.  In addition to exposing
the progressive motive domains, it retains the concrete restored minor tail
which will be specialized by the motive arguments. -/
theorem ConstructorParameterLayoutWF.restoredRecursorOperationalMotiveSpineExact
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.ConstructorParameterLayoutWF env) (henv : env.ConversionRegular)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    {U : Nat} {context : List VExpr}
    (fieldSort : VLevel) (hfieldSort : fieldSort.WF U)
    (levels : List VLevel) (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U context (view.familyType.instL levels)
        params (.sort resultLevel)) :
    let gen := view.nested.generation
    let projectionLevels := view.flatView.projectionLevels fieldSort levels
    let majorTail :=
      VExpr.forallN
        (VExpr.liftTelN (gen.familyCount + gen.minorCount)
          (gen.idxTel view.selection.family) 0) <|
        .forallE
          (VExpr.appN
            (.const view.selection.family.raw.name gen.sourceLevels)
            (VExpr.bvarRevRange
                ((gen.idxTel view.selection.family).length +
                  gen.familyCount + gen.minorCount)
                view.nested.elim.flat.nparams ++
              VExpr.bvarRevRange 0
                (gen.idxTel view.selection.family).length)) <|
          .app
            (VExpr.appN
              (.bvar
                (gen.familyCount - 1 -
                  view.selection.family.view.ordinal + gen.minorCount +
                  (gen.idxTel view.selection.family).length + 1))
              (VExpr.bvarRevRange 1
                (gen.idxTel view.selection.family).length))
            (.bvar 0)
    let minorTail := VExpr.forallN gen.minorTypes majorTail
    let restoredMinorTail :=
      (view.nested.restoreRec minorTail).instL projectionLevels
    env.SpineWF U context
      ((view.nested.restoreRec
        (gen.recType view.selection.family)).instL projectionLevels)
      params
      (VExpr.forallN
        ((view.operationalProjectionMotiveTypes fieldSort levels params).zipIdx.map
          fun entry => entry.1.liftN entry.2)
        (restoredMinorTail.instRevAt params gen.familyCount)) := by
  let gen := view.nested.generation
  let projectionLevels := view.flatView.projectionLevels fieldSort levels
  let majorTail :=
    VExpr.forallN
      (VExpr.liftTelN (gen.familyCount + gen.minorCount)
        (gen.idxTel view.selection.family) 0) <|
      .forallE
        (VExpr.appN
          (.const view.selection.family.raw.name gen.sourceLevels)
          (VExpr.bvarRevRange
              ((gen.idxTel view.selection.family).length +
                gen.familyCount + gen.minorCount)
              view.nested.elim.flat.nparams ++
            VExpr.bvarRevRange 0
              (gen.idxTel view.selection.family).length)) <|
        .app
          (VExpr.appN
            (.bvar
              (gen.familyCount - 1 -
                view.selection.family.view.ordinal + gen.minorCount +
                (gen.idxTel view.selection.family).length + 1))
            (VExpr.bvarRevRange 1
              (gen.idxTel view.selection.family).length))
          (.bvar 0)
  let minorTail := VExpr.forallN gen.minorTypes majorTail
  let recTail := VExpr.forallN gen.motiveTypes minorTail
  let restoredTail := (view.nested.restoreRec recTail).instL projectionLevels
  let restoredParamsAt :=
    (gen.paramsTel.map view.nested.restoreRec).map
      (VExpr.instL projectionLevels)
  let restoredMotiveBinders :=
    (gen.motiveTypes.map view.nested.restoreRec).map
      (VExpr.instL projectionLevels)
  let restoredMinorTail :=
    (view.nested.restoreRec minorTail).instL projectionLevels
  have recShape : gen.recType view.selection.family =
      VExpr.forallN gen.paramsTel recTail := by
    rfl
  have restoredShape :
      (view.nested.restoreRec
        (gen.recType view.selection.family)).instL projectionLevels =
      VExpr.forallN restoredParamsAt restoredTail := by
    rw [recShape]
    unfold NestedBlockChecked.restoreRec
    rw [VInductDecl.restoreExpr_forallN, VExpr.instL_forallN]
    rfl
  have paramsTyped := self.restoredParamsSpine henv closed fieldSort
    hfieldSort levels hlevels hlevelsLength params hparamsLength paramsSpine
      restoredTail
  have paramsFull : env.SpineWF U context
      ((view.nested.restoreRec
        (gen.recType view.selection.family)).instL projectionLevels)
      params (VExpr.instRev restoredTail params) := by
    rw [restoredShape]
    simpa [gen, projectionLevels, restoredParamsAt] using paramsTyped
  have restoredTailShape : restoredTail =
      VExpr.forallN restoredMotiveBinders restoredMinorTail := by
    unfold restoredTail recTail restoredMinorTail restoredMotiveBinders
    unfold NestedBlockChecked.restoreRec
    rw [VInductDecl.restoreExpr_forallN, VExpr.instL_forallN]
  rw [restoredTailShape, VExpr.instRev_forallN_projection] at paramsFull
  rw [view.restoredMotiveBinders_specialize closed fieldSort levels params]
    at paramsFull
  have motiveCount : restoredMotiveBinders.length = gen.familyCount := by
    simp [restoredMotiveBinders, gen.motiveTypes_length]
  simpa [motiveCount] using paramsFull

/-- Named-tail presentation of the exact operational parameter cursor.  This
is the compositional interface for motive consumption: the raw generated
major syntax remains private while the residual minor telescope is exposed
through `restoredProjectionRecursorMinorTail`. -/
theorem ConstructorParameterLayoutWF.restoredRecursorOperationalMotiveCursor
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.ConstructorParameterLayoutWF env) (henv : env.ConversionRegular)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    {U : Nat} {context : List VExpr}
    (fieldSort : VLevel) (hfieldSort : fieldSort.WF U)
    (levels : List VLevel) (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U context (view.familyType.instL levels)
        params (.sort resultLevel)) :
    let gen := view.nested.generation
    let projectionLevels := view.flatView.projectionLevels fieldSort levels
    env.SpineWF U context
      ((view.nested.restoreRec
        (gen.recType view.selection.family)).instL projectionLevels)
      params
      (VExpr.forallN
        ((view.operationalProjectionMotiveTypes fieldSort levels params).zipIdx.map
          fun entry => entry.1.liftN entry.2)
        ((view.restoredProjectionRecursorMinorTail fieldSort levels).instRevAt
          params gen.familyCount)) := by
  have cursor := self.restoredRecursorOperationalMotiveSpineExact henv closed
    fieldSort hfieldSort levels hlevels hlevelsLength params hparamsLength
      paramsSpine
  simpa [restoredProjectionRecursorMinorTail,
    projectionRecursorMajorTail] using cursor

/-- Any well-formed motive domain admits the canonical constant motive once
an ambient result type at the motive universe is available.  This packages
the semantic part of every nonselected restored motive: the exact restored
recursor domain supplies the index and family-major telescope, so no
registration fact for the corresponding flattened family is needed. -/
theorem VEnv.IsType.constantMotive_hasType
    {env : VEnv} (henv : env.Ordered)
    {U : Nat} {context binders : List VExpr}
    {majorDomain dummyType : VExpr} {resultSort : VLevel}
    (self : env.IsType U context
      (VExpr.forallN binders
        (.forallE majorDomain (.sort resultSort))))
    (dummyTypeType : env.HasType U context dummyType (.sort resultSort)) :
    env.HasType U context
      (VExpr.lamN binders
        (.lam majorDomain (dummyType.liftN (binders.length + 1))))
      (VExpr.forallN binders
        (.forallE majorDomain (.sort resultSort))) := by
  obtain ⟨bindersTel, majorType⟩ :=
    VEnv.IsType.forallN_inv henv self
  obtain ⟨⟨majorSort, majorDomainType⟩, _⟩ :=
    majorType.forallE_inv henv
  have dummyTypeWeak : env.HasType U
      (majorDomain :: binders.reverse ++ context)
      (dummyType.liftN (binders.length + 1)) (.sort resultSort) := by
    have weakened := dummyTypeType.weakN henv
      (Ctx.LiftN.zero (n := binders.length + 1) (Γ := context)
        (majorDomain :: binders.reverse) (h := by simp))
    simpa [VExpr.liftN] using weakened
  exact VEnv.HasType.lamN bindersTel
    (majorDomainType.lam dummyTypeWeak)

/-- A declaration-time flattened motive, restored before runtime parameter
specialization, inhabits the exact current restored recursor domain.  The
selected family is the weakened runtime type function; every other family is
the canonical constant motive into the shared major-local dummy carrier.

`domainIsType` deliberately comes from the live recursor cursor.  This avoids
requiring registrations for auxiliary flattened families after their syntax
has been restored to the source surface. -/
theorem ConstructorParameterLayoutWF.restoredProjectionMotive_hasType
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.ConstructorParameterLayoutWF env) (henv : env.ConversionRegular)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    {U : Nat} {context : List VExpr}
    (family : NormalizedFamily)
    (hfamily : family ∈ view.nested.generation.families)
    (fieldSort : VLevel)
    (levels : List VLevel) (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (flatTemplate : VStructureView.ProjectionCode)
    (selectedMotiveEq :
      (view.nested.restoreRecAt
        (view.flatView.projectionLevels fieldSort levels)
        flatTemplate.typeFn.lift).instRevAt params 1 = typeFn.lift)
    (dummyEq :
      let flatDummyType := VBlockStructureView.majorDummyType
        flatTemplate.typeFn.lift (.bvar 0)
      (view.nested.restoreRecAt
        (view.flatView.projectionLevels fieldSort levels)
        flatDummyType).instRevAt params 1 = dummyType)
    (hmotiveLevel : view.nested.generation.motiveLevel.inst
      (view.flatView.projectionLevels fieldSort levels) = fieldSort)
    (typeFnType : env.HasType U context typeFn
      (.forallE (view.structureType levels params) (.sort fieldSort)))
    (dummyTypeType : env.HasType U
      (view.structureType levels params :: context) dummyType
      (.sort fieldSort))
    (domainIsType : env.IsType U
      (view.structureType levels params :: context)
      ((view.nested.restoreRecAt
        (view.flatView.projectionLevels fieldSort levels)
        ((view.nested.generation.motiveType family).instL
          (view.flatView.projectionLevels fieldSort levels))).instRev
            (params.map (VExpr.liftN 1)))) :
    let projectionLevels := view.flatView.projectionLevels fieldSort levels
    let formalParams := VExpr.bvarRevRange 0 view.nparams
    let flatParamsMajor := formalParams.map (VExpr.liftN 1)
    let flatDummyType := VBlockStructureView.majorDummyType
      flatTemplate.typeFn.lift (.bvar 0)
    env.HasType U (view.structureType levels params :: context)
      ((view.nested.restoreRecAt projectionLevels
        (if family.view.ordinal = view.selection.family.view.ordinal then
          flatTemplate.typeFn.lift
        else
          view.flatView.identityMotiveWith family levels flatParamsMajor
            flatDummyType)).instRevAt params 1)
      ((view.nested.restoreRecAt projectionLevels
        ((view.nested.generation.motiveType family).instL
          projectionLevels)).instRev (params.map (VExpr.liftN 1))) := by
  let projectionLevels := view.flatView.projectionLevels fieldSort levels
  let formalParams := VExpr.bvarRevRange 0 view.nparams
  let flatParamsMajor := formalParams.map (VExpr.liftN 1)
  let flatDummyType := VBlockStructureView.majorDummyType
    flatTemplate.typeFn.lift (.bvar 0)
  dsimp only
  have baseClosed := self.restoredMotiveType_closedN henv closed family
    hfamily projectionLevels
  by_cases selected : family.view.ordinal =
      view.selection.family.view.ordinal
  · have familyAt := view.nested.generation.family_getElem?_ordinal hfamily
    rw [selected] at familyAt
    have selectedAt := view.nested.generation.family_getElem?_ordinal
      view.flatView.family_mem
    have familyEq : family = view.selection.family :=
      Option.some.inj (familyAt.symm.trans selectedAt)
    subst family
    simp only [↓reduceIte]
    rw [selectedMotiveEq]
    have hstructureLift : view.structureType levels
        (params.map (VExpr.liftN 1)) =
        (view.structureType levels params).lift := by
      simpa [VExpr.liftN] using
        (view.structureType_liftN levels params 1 0).symm
    have typeFnLift : env.HasType U
        (view.structureType levels params :: context) typeFn.lift
        (.forallE (view.structureType levels params).lift
          (.sort fieldSort)) := by
      exact typeFnType.weakN henv.ordered
        (Ctx.LiftN.one (A := view.structureType levels params))
    rw [view.selectedRestoredMotiveType_eq closed fieldSort levels
      hlevelsLength params hparamsLength hmotiveLevel (by
        simpa [projectionLevels] using baseClosed)]
    rw [← hstructureLift] at typeFnLift
    exact typeFnLift
  · simp only [selected, ↓reduceIte]
    have dummyEq' :
        (view.nested.restoreRecAt projectionLevels flatDummyType).instRevAt
            params 1 = dummyType := by
      simpa [projectionLevels, flatDummyType] using dummyEq
    obtain ⟨binders, majorDomain, motiveShape, domainShape⟩ :=
      view.restoredIdentityMotiveWith_shape closed family fieldSort levels
        hlevelsLength params hparamsLength hmotiveLevel flatDummyType
          dummyType (by simpa [projectionLevels] using baseClosed) dummyEq'
    have canonicalType : env.HasType U
        (view.structureType levels params :: context)
        (VExpr.lamN binders
          (.lam majorDomain (dummyType.liftN (binders.length + 1))))
        (VExpr.forallN binders
          (.forallE majorDomain (.sort fieldSort))) := by
      apply VEnv.IsType.constantMotive_hasType henv.ordered
      · rw [← domainShape]
        simpa [projectionLevels] using domainIsType
      · exact dummyTypeType
    rw [motiveShape, domainShape]
    exact canonicalType

private def progressiveRestoredTypesAux : List VExpr → Nat → List VExpr
  | [], _ => []
  | type :: types, index =>
      type.liftN index :: progressiveRestoredTypesAux types (index + 1)

@[simp] private theorem progressiveRestoredTypesAux_length
    (types : List VExpr) (index : Nat) :
    (progressiveRestoredTypesAux types index).length = types.length := by
  induction types generalizing index with
  | nil => rfl
  | cons type types ih => simp [progressiveRestoredTypesAux, ih]

private theorem progressiveRestoredTypesAux_eq_zipIdx
    (types : List VExpr) (index : Nat) :
    progressiveRestoredTypesAux types index =
      (types.zipIdx index).map fun entry => entry.1.liftN entry.2 := by
  induction types generalizing index with
  | nil => rfl
  | cons type types ih =>
      simp only [progressiveRestoredTypesAux, List.zipIdx, List.map_cons]
      rw [ih]

private theorem progressiveRestoredTypesAux_instTelN
    (types : List VExpr) (argument : VExpr) (index : Nat) :
    VExpr.instTelN argument
      (progressiveRestoredTypesAux types (index + 1)) index =
        progressiveRestoredTypesAux types index := by
  induction types generalizing index with
  | nil => rfl
  | cons type types ih =>
      simp only [progressiveRestoredTypesAux, VExpr.instTelN]
      rw [VExpr.liftN_succ_inst_top, ih]

/-- The complete restored motive inventory consumes the live recursor's
progressively weakened motive telescope.  Regularity is queried at each
cursor before its argument is constructed, so later restored family domains
remain justified even though earlier motive arguments have already been
substituted. -/
theorem ConstructorParameterLayoutWF.restoredProjectionMotives_hasType
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.ConstructorParameterLayoutWF env) (henv : env.ConversionRegular)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    {U : Nat} {context : List VExpr}
    (fieldSort : VLevel)
    (levels : List VLevel) (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (hmajorContext : OnCtx
      (view.structureType levels params :: context) (env.IsType U))
    (flatTemplate : VStructureView.ProjectionCode)
    (selectedMotiveEq :
      (view.nested.restoreRecAt
        (view.flatView.projectionLevels fieldSort levels)
        flatTemplate.typeFn.lift).instRevAt params 1 = typeFn.lift)
    (dummyEq :
      let flatDummyType := VBlockStructureView.majorDummyType
        flatTemplate.typeFn.lift (.bvar 0)
      (view.nested.restoreRecAt
        (view.flatView.projectionLevels fieldSort levels)
        flatDummyType).instRevAt params 1 = dummyType)
    (hmotiveLevel : view.nested.generation.motiveLevel.inst
      (view.flatView.projectionLevels fieldSort levels) = fieldSort)
    (typeFnType : env.HasType U context typeFn
      (.forallE (view.structureType levels params) (.sort fieldSort)))
    (dummyTypeType : env.HasType U
      (view.structureType levels params :: context) dummyType
      (.sort fieldSort))
    (function tail : VExpr)
    (functionType : env.HasType U
      (view.structureType levels params :: context) function
      (VExpr.forallN
        ((view.operationalProjectionMotiveTypes fieldSort levels
          (params.map (VExpr.liftN 1))).zipIdx.map fun entry =>
            entry.1.liftN entry.2)
        tail)) :
    let projectionLevels := view.flatView.projectionLevels fieldSort levels
    let formalParams := VExpr.bvarRevRange 0 view.nparams
    let flatParamsMajor := formalParams.map (VExpr.liftN 1)
    let flatDummyType := VBlockStructureView.majorDummyType
      flatTemplate.typeFn.lift (.bvar 0)
    let flatMotives := view.flatView.projectionMotivesWith levels
      flatParamsMajor flatTemplate.typeFn.lift flatDummyType
    let motivesMajor := flatMotives.map fun expression =>
      (view.nested.restoreRecAt projectionLevels expression).instRevAt params 1
    env.HasType U (view.structureType levels params :: context)
      (VExpr.appN function motivesMajor) (tail.instRev motivesMajor) := by
  let gen := view.nested.generation
  let projectionLevels := view.flatView.projectionLevels fieldSort levels
  let formalParams := VExpr.bvarRevRange 0 view.nparams
  let flatParamsMajor := formalParams.map (VExpr.liftN 1)
  let flatDummyType := VBlockStructureView.majorDummyType
    flatTemplate.typeFn.lift (.bvar 0)
  let flatMotives := view.flatView.projectionMotivesWith levels
    flatParamsMajor flatTemplate.typeFn.lift flatDummyType
  let restoreSpecialize := fun expression =>
    (view.nested.restoreRecAt projectionLevels expression).instRevAt params 1
  let motivesMajor := flatMotives.map restoreSpecialize
  let baseType := fun family : NormalizedFamily =>
    (view.nested.restoreRecAt projectionLevels
      ((gen.motiveType family).instL projectionLevels)).instRev
        (params.map (VExpr.liftN 1))
  let motive := fun family : NormalizedFamily =>
    restoreSpecialize
      (if family.view.ordinal = view.selection.family.view.ordinal then
        flatTemplate.typeFn.lift
      else
        view.flatView.identityMotiveWith family levels flatParamsMajor
          flatDummyType)
  dsimp only
  have motiveTypesEq :
      view.operationalProjectionMotiveTypes fieldSort levels
          (params.map (VExpr.liftN 1)) =
        gen.families.map baseType := by
    rfl
  have flatMotivesEq : flatMotives = gen.families.map fun family =>
      if family.view.ordinal = view.selection.family.view.ordinal then
        flatTemplate.typeFn.lift
      else
        view.flatView.identityMotiveWith family levels flatParamsMajor
          flatDummyType := by
    rfl
  have motivesEq : motivesMajor = gen.families.map motive := by
    rw [show motivesMajor = flatMotives.map restoreSpecialize from rfl,
      flatMotivesEq, List.map_map]
    rfl
  rw [motiveTypesEq, ← progressiveRestoredTypesAux_eq_zipIdx]
    at functionType
  have aux : ∀ (families : List NormalizedFamily)
      (current tail : VExpr),
      (∀ family ∈ families, family ∈ gen.families) →
      env.HasType U (view.structureType levels params :: context) current
        (VExpr.forallN
          (progressiveRestoredTypesAux (families.map baseType) 0) tail) →
      env.HasType U (view.structureType levels params :: context)
        (VExpr.appN current (families.map motive))
        (tail.instRev (families.map motive)) := by
    intro families
    induction families with
    | nil =>
        intro current tail _ currentType
        change env.HasType U (view.structureType levels params :: context)
          current tail at currentType
        simpa [VExpr.appN, VExpr.instRev] using currentType
    | cons family families ih =>
        intro current tail hsub currentType
        have cursorIsType := currentType.isType henv hmajorContext
        have domainIsType : env.IsType U
            (view.structureType levels params :: context)
            (baseType family) := by
          have domain := (cursorIsType.forallE_inv henv.ordered).1
          simpa [progressiveRestoredTypesAux, baseType] using domain
        have motiveType := self.restoredProjectionMotive_hasType henv closed
          family (hsub family (.head _)) fieldSort levels hlevelsLength params
            hparamsLength flatTemplate selectedMotiveEq dummyEq hmotiveLevel
              typeFnType dummyTypeType (by simpa [baseType] using domainIsType)
        have motiveType' : env.HasType U
            (view.structureType levels params :: context) (motive family)
            ((baseType family).liftN 0) := by
          simpa [motive, baseType, restoreSpecialize, projectionLevels,
            flatParamsMajor, formalParams, flatDummyType, gen] using motiveType
        have nextType := currentType.app motiveType'
        simp only [List.map_cons, progressiveRestoredTypesAux,
          VExpr.instN_forallN] at nextType
        rw [progressiveRestoredTypesAux_instTelN] at nextType
        have restType := ih (.app current (motive family))
          (tail.inst (motive family) families.length)
          (fun candidate member => hsub candidate (.tail _ member)) (by
            simpa using nextType)
        simpa [VExpr.appN, VExpr.instRev] using restType
  change env.HasType U (view.structureType levels params :: context)
    (VExpr.appN function motivesMajor) (tail.instRev motivesMajor)
  rw [motivesEq]
  exact aux gen.families function tail (fun _ member => member) functionType

/-- Consuming the operational restored motives exposes the exact progressive
minor cursor of the same recursor transaction.  Both sides use named restored
tail contracts, keeping the raw generated major syntax private. -/
theorem ConstructorParameterLayoutWF.restoredProjectionMotives_minorCursor
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.ConstructorParameterLayoutWF env) (henv : env.ConversionRegular)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    {U : Nat} {context : List VExpr}
    (fieldSort : VLevel)
    (levels : List VLevel) (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (hmajorContext : OnCtx
      (view.structureType levels params :: context) (env.IsType U))
    (flatTemplate : VStructureView.ProjectionCode)
    (selectedMotiveEq :
      (view.nested.restoreRecAt
        (view.flatView.projectionLevels fieldSort levels)
        flatTemplate.typeFn.lift).instRevAt params 1 = typeFn.lift)
    (dummyEq :
      let flatDummyType := VBlockStructureView.majorDummyType
        flatTemplate.typeFn.lift (.bvar 0)
      (view.nested.restoreRecAt
        (view.flatView.projectionLevels fieldSort levels)
        flatDummyType).instRevAt params 1 = dummyType)
    (hmotiveLevel : view.nested.generation.motiveLevel.inst
      (view.flatView.projectionLevels fieldSort levels) = fieldSort)
    (typeFnType : env.HasType U context typeFn
      (.forallE (view.structureType levels params) (.sort fieldSort)))
    (dummyTypeType : env.HasType U
      (view.structureType levels params :: context) dummyType
      (.sort fieldSort))
    (function : VExpr)
    (functionType : env.HasType U
      (view.structureType levels params :: context) function
      (VExpr.forallN
        ((view.operationalProjectionMotiveTypes fieldSort levels
          (params.map (VExpr.liftN 1))).zipIdx.map fun entry =>
            entry.1.liftN entry.2)
        ((view.restoredProjectionRecursorMinorTail fieldSort levels).instRevAt
          (params.map (VExpr.liftN 1))
            view.nested.generation.familyCount))) :
    let projectionLevels := view.flatView.projectionLevels fieldSort levels
    let paramsMajor := params.map (VExpr.liftN 1)
    let formalParams := VExpr.bvarRevRange 0 view.nparams
    let flatParamsMajor := formalParams.map (VExpr.liftN 1)
    let flatDummyType := VBlockStructureView.majorDummyType
      flatTemplate.typeFn.lift (.bvar 0)
    let flatMotives := view.flatView.projectionMotivesWith levels
      flatParamsMajor flatTemplate.typeFn.lift flatDummyType
    let motivesMajor := flatMotives.map fun expression =>
      (view.nested.restoreRecAt projectionLevels expression).instRevAt params 1
    env.HasType U (view.structureType levels params :: context)
      (VExpr.appN function motivesMajor)
      (VExpr.forallN
        ((view.operationalProjectionMinorTypes fieldSort levels paramsMajor
          motivesMajor).zipIdx.map fun entry => entry.1.liftN entry.2)
        (view.operationalProjectionRecursorMajorTail fieldSort levels
          paramsMajor motivesMajor)) := by
  let gen := view.nested.generation
  let projectionLevels := view.flatView.projectionLevels fieldSort levels
  let paramsMajor := params.map (VExpr.liftN 1)
  let formalParams := VExpr.bvarRevRange 0 view.nparams
  let flatParamsMajor := formalParams.map (VExpr.liftN 1)
  let flatDummyType := VBlockStructureView.majorDummyType
    flatTemplate.typeFn.lift (.bvar 0)
  let flatMotives := view.flatView.projectionMotivesWith levels
    flatParamsMajor flatTemplate.typeFn.lift flatDummyType
  let motivesMajor := flatMotives.map fun expression =>
    (view.nested.restoreRecAt projectionLevels expression).instRevAt params 1
  let restoredMinorTail :=
    view.restoredProjectionRecursorMinorTail fieldSort levels
  let restoredMajorTail :=
    view.restoredProjectionRecursorMajorTail fieldSort levels
  let restoredMinorBinders :=
    (gen.minorTypes.map view.nested.restoreRec).map
      (VExpr.instL projectionLevels)
  dsimp only
  have afterMotives := self.restoredProjectionMotives_hasType henv closed
    fieldSort levels hlevelsLength params hparamsLength hmajorContext
      flatTemplate selectedMotiveEq dummyEq hmotiveLevel typeFnType
        dummyTypeType function (restoredMinorTail.instRevAt paramsMajor
          gen.familyCount) (by simpa [paramsMajor, restoredMinorTail, gen]
            using functionType)
  dsimp only at afterMotives
  have restoredMinorTailShape : restoredMinorTail =
      VExpr.forallN restoredMinorBinders restoredMajorTail := by
    unfold restoredMinorTail restoredMajorTail
    unfold restoredProjectionRecursorMinorTail
    unfold restoredProjectionRecursorMajorTail
    unfold NestedBlockChecked.restoreRec
    rw [VInductDecl.restoreExpr_forallN, VExpr.instL_forallN]
    rfl
  rw [restoredMinorTailShape,
    VExpr.instRevAt_forallN_projection,
    VExpr.instRev_forallN_projection] at afterMotives
  rw [view.restoredMinorBinders_specialize closed fieldSort levels
    paramsMajor motivesMajor] at afterMotives
  have minorCount : restoredMinorBinders.length = gen.minorCount := by
    simp [restoredMinorBinders, gen.minorTypes_length]
  have specializedMinorCount :
      ((restoredMinorBinders.zipIdx gen.familyCount).map fun entry =>
        entry.1.instRevAt paramsMajor entry.2).length = gen.minorCount := by
    simp [minorCount]
  rw [minorCount, specializedMinorCount] at afterMotives
  have motivesMajorEq : flatMotives.map (fun expression =>
      (view.nested.restoreRecAt projectionLevels expression).instRevAt
        params 1) = motivesMajor := rfl
  rw [motivesMajorEq] at afterMotives
  change env.HasType U (view.structureType levels params :: context)
    (VExpr.appN function motivesMajor)
    (VExpr.forallN
      ((view.operationalProjectionMinorTypes fieldSort levels paramsMajor
        motivesMajor).zipIdx.map fun entry => entry.1.liftN entry.2)
      (view.operationalProjectionRecursorMajorTail fieldSort levels
        paramsMajor motivesMajor)) at afterMotives
  exact afterMotives

/-- Restoring any generated projection motive produces a lambda-headed term,
never a source constant application.  This is the side condition needed to
map restoration through the raw minor's motive substitution. -/
private theorem restoredProjectionMotives_nonConst
    (view : VRestoredBlockStructureView)
    (fieldSort : VLevel) (levels : List VLevel)
    (flatTemplate : VStructureView.ProjectionCode)
    (flatTypeFnLam : ∃ domain body,
      flatTemplate.typeFn = .lam domain body) :
    let projectionLevels := view.flatView.projectionLevels fieldSort levels
    let formalParams := VExpr.bvarRevRange 0 view.nparams
    let flatParamsMajor := formalParams.map (VExpr.liftN 1)
    let flatDummyType := VBlockStructureView.majorDummyType
      flatTemplate.typeFn.lift (.bvar 0)
    let flatMotives := view.flatView.projectionMotivesWith levels
      flatParamsMajor flatTemplate.typeFn.lift flatDummyType
    ∀ motive ∈ flatMotives, ∀ name nameLevels,
      (view.nested.restoreRecAt projectionLevels motive).appHead ≠
        .const name nameLevels := by
  let projectionLevels := view.flatView.projectionLevels fieldSort levels
  let formalParams := VExpr.bvarRevRange 0 view.nparams
  let flatParamsMajor := formalParams.map (VExpr.liftN 1)
  let flatDummyType := VBlockStructureView.majorDummyType
    flatTemplate.typeFn.lift (.bvar 0)
  let flatMotives := view.flatView.projectionMotivesWith levels
    flatParamsMajor flatTemplate.typeFn.lift flatDummyType
  dsimp only
  intro motive motiveMem name nameLevels
  simp only [VBlockStructureView.projectionMotivesWith,
    List.mem_map] at motiveMem
  obtain ⟨family, _, rfl⟩ := motiveMem
  split
  · obtain ⟨domain, body, flatTypeFnEq⟩ := flatTypeFnLam
    rw [flatTypeFnEq]
    simp [NestedBlockChecked.restoreRecAt, VExpr.lift, VExpr.liftN,
      VExpr.appHead, VInductDecl.restoreExpr]
  · unfold VBlockStructureView.identityMotiveWith
    unfold NestedBlockChecked.restoreRecAt
    rw [VInductDecl.restoreExpr_lamN]
    generalize (view.flatView.specializedIndices family levels
      flatParamsMajor).map
        (VInductDecl.restoreExpr
          (view.nested.recEntries.map (·.instL projectionLevels))
          view.nested.recMap) = restoredIndices
    cases restoredIndices <;>
      simp [VExpr.lamN, VInductDecl.restoreExpr, VExpr.appHead]

/-- Restoring the flattened generated minor and then specializing its formal
parameters is exactly the live recursor minor domain after specializing the
same parameters and restored motive inventory. -/
theorem ConstructorParameterLayoutWF.restoredProjectionMinorType_eq
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.ConstructorParameterLayoutWF env) (henv : env.ConversionRegular)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    (constructor : NormalizedBlockCtor)
    (hconstructor : constructor ∈ view.nested.generation.flatCtors)
    (fieldSort : VLevel) (levels : List VLevel)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (flatTemplate : VStructureView.ProjectionCode)
    (flatTypeFnLam : ∃ domain body,
      flatTemplate.typeFn = .lam domain body) :
    let gen := view.nested.generation
    let projectionLevels := view.flatView.projectionLevels fieldSort levels
    let formalParams := VExpr.bvarRevRange 0 view.nparams
    let flatParamsMajor := formalParams.map (VExpr.liftN 1)
    let paramsMajor := params.map (VExpr.liftN 1)
    let flatDummyType := VBlockStructureView.majorDummyType
      flatTemplate.typeFn.lift (.bvar 0)
    let flatMotives := view.flatView.projectionMotivesWith levels
      flatParamsMajor flatTemplate.typeFn.lift flatDummyType
    let motivesMajor := flatMotives.map fun expression =>
      (view.nested.restoreRecAt projectionLevels expression).instRevAt params 1
    (view.nested.restoreRecAt projectionLevels
      (view.flatView.generatedProjectionMinorType constructor fieldSort levels
        flatParamsMajor flatMotives)).instRevAt params 1 =
      (((view.nested.restoreRecAt projectionLevels
        ((gen.minorType constructor).instL projectionLevels)).instRevAt
          paramsMajor gen.familyCount).instRev motivesMajor) := by
  let gen := view.nested.generation
  let projectionLevels := view.flatView.projectionLevels fieldSort levels
  let formalParams := VExpr.bvarRevRange 0 view.nparams
  let flatParamsMajor := formalParams.map (VExpr.liftN 1)
  let paramsMajor := params.map (VExpr.liftN 1)
  let flatDummyType := VBlockStructureView.majorDummyType
    flatTemplate.typeFn.lift (.bvar 0)
  let flatMotives := view.flatView.projectionMotivesWith levels
    flatParamsMajor flatTemplate.typeFn.lift flatDummyType
  let restoredFlatMotives := flatMotives.map
    (view.nested.restoreRecAt projectionLevels)
  let motivesMajor := flatMotives.map fun expression =>
    (view.nested.restoreRecAt projectionLevels expression).instRevAt params 1
  let rawMinor := (gen.minorType constructor).instL projectionLevels
  let restoredRawMinor := view.nested.restoreRecAt projectionLevels rawMinor
  dsimp only
  have flatParamsMajorEq : flatParamsMajor =
      VExpr.bvarRevRange 1 view.nparams := by
    unfold flatParamsMajor formalParams
    rw [VExpr.bvarRevRange_liftN_low]
  have formalInert : ∀ argument ∈ flatParamsMajor,
      RestoreInert
        (view.nested.recEntries.map (·.instL projectionLevels))
        view.nested.recMap argument := by
    intro argument member
    rw [flatParamsMajorEq] at member
    exact bvarRevRange_restoreInert _ _ _ _ argument member
  have restoreFormal := view.nested.restoreRecAt_instRevAt closed
    projectionLevels rawMinor flatParamsMajor gen.familyCount formalInert
  have flatMotivesNonConst : ∀ motive ∈ flatMotives,
      ∀ name nameLevels,
      (view.nested.restoreRecAt projectionLevels motive).appHead ≠
        .const name nameLevels := by
    simpa [projectionLevels, formalParams, flatParamsMajor, flatDummyType,
      flatMotives] using
        restoredProjectionMotives_nonConst view fieldSort levels
          flatTemplate flatTypeFnLam
  have restoreMotives := view.nested.restoreRecAt_instRevAt_map closed
    projectionLevels (rawMinor.instRevAt flatParamsMajor gen.familyCount)
      flatMotives 0 flatMotivesNonConst
  have restoreFlatExact :
      view.nested.restoreRecAt projectionLevels
          (view.flatView.generatedProjectionMinorType constructor fieldSort
            levels flatParamsMajor flatMotives) =
        (restoredRawMinor.instRevAt flatParamsMajor gen.familyCount).instRev
          restoredFlatMotives := by
    unfold VBlockStructureView.generatedProjectionMinorType
    simp only [← VExpr.instRevAt_zero]
    change view.nested.restoreRecAt projectionLevels
        ((rawMinor.instRevAt flatParamsMajor gen.familyCount).instRevAt
          flatMotives 0) =
      (restoredRawMinor.instRevAt flatParamsMajor gen.familyCount).instRevAt
        restoredFlatMotives 0
    rw [← restoreMotives, ← restoreFormal]
  rw [restoreFlatExact]
  have rawClosed := self.restoredMinorType_closedN henv closed
    constructor hconstructor projectionLevels
  have restoredRawClosed : restoredRawMinor.ClosedN
      (view.nparams + gen.familyCount) := by
    simpa [restoredRawMinor, rawMinor, gen, projectionLevels] using rawClosed
  simp only [← VExpr.instRevAt_zero]
  change
    ((restoredRawMinor.instRevAt flatParamsMajor gen.familyCount).instRevAt
        restoredFlatMotives 0).instRevAt params 1 =
      (restoredRawMinor.instRevAt paramsMajor gen.familyCount).instRevAt
        motivesMajor 0
  rw [instRevAt_instRevAt_hi
    (restoredRawMinor.instRevAt flatParamsMajor gen.familyCount)
    restoredFlatMotives params 0 1]
  have motivesLength : restoredFlatMotives.length = gen.familyCount := by
    simp [restoredFlatMotives, flatMotives,
      VRestoredBlockStructureView.flatView, gen]
  rw [motivesLength]
  rw [instRevAt_instRevAt_hi restoredRawMinor flatParamsMajor params
    gen.familyCount 1]
  have rawHighClosed : restoredRawMinor.ClosedN
      (1 + gen.familyCount + flatParamsMajor.length) := by
    apply restoredRawClosed.mono
    simp only [flatParamsMajor, formalParams, List.length_map,
      VExpr.bvarRevRange_length]
    omega
  rw [VExpr.instRevAt_closedN params rawHighClosed]
  have paramsMapped : flatParamsMajor.map
      (fun argument => argument.instRevAt params 1) = paramsMajor := by
    rw [flatParamsMajorEq]
    simpa [paramsMajor, hparamsLength] using
      VExpr.map_instRevAt_bvarRevRange params 1
  rw [paramsMapped]
  have restoredMotivesMapped : restoredFlatMotives.map
      (fun expression => expression.instRevAt params 1) = motivesMajor := by
    simp [restoredFlatMotives, motivesMajor, List.map_map,
      Function.comp_def]
  rw [restoredMotivesMapped]

/-- The exact live restored minor domain exposes all generated constructor
field and recursive-hypothesis binders. -/
theorem ConstructorParameterLayoutWF.restoredProjectionMinorBinders_length
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.ConstructorParameterLayoutWF env) (henv : env.ConversionRegular)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    (constructor : NormalizedBlockCtor)
    (hconstructor : constructor ∈ view.nested.generation.flatCtors)
    (fieldSort : VLevel) (levels : List VLevel)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (flatTemplate : VStructureView.ProjectionCode)
    (flatTypeFnLam : ∃ domain body,
      flatTemplate.typeFn = .lam domain body) :
    let gen := view.nested.generation
    let projectionLevels := view.flatView.projectionLevels fieldSort levels
    let formalParams := VExpr.bvarRevRange 0 view.nparams
    let flatParamsMajor := formalParams.map (VExpr.liftN 1)
    let paramsMajor := params.map (VExpr.liftN 1)
    let flatDummyType := VBlockStructureView.majorDummyType
      flatTemplate.typeFn.lift (.bvar 0)
    let flatMotives := view.flatView.projectionMotivesWith levels
      flatParamsMajor flatTemplate.typeFn.lift flatDummyType
    let motivesMajor := flatMotives.map fun expression =>
      (view.nested.restoreRecAt projectionLevels expression).instRevAt params 1
    let exactMinor :=
      (((view.nested.restoreRecAt projectionLevels
        ((gen.minorType constructor).instL projectionLevels)).instRevAt
          paramsMajor gen.familyCount).instRev motivesMajor)
    let count := (view.flatView.specializedCtorFields constructor levels
      flatParamsMajor).length + constructor.ctor.view.recursive.length
    (VExpr.telN count exactMinor).length = count := by
  let gen := view.nested.generation
  let projectionLevels := view.flatView.projectionLevels fieldSort levels
  let formalParams := VExpr.bvarRevRange 0 view.nparams
  let flatParamsMajor := formalParams.map (VExpr.liftN 1)
  let paramsMajor := params.map (VExpr.liftN 1)
  let flatDummyType := VBlockStructureView.majorDummyType
    flatTemplate.typeFn.lift (.bvar 0)
  let flatMotives := view.flatView.projectionMotivesWith levels
    flatParamsMajor flatTemplate.typeFn.lift flatDummyType
  let motivesMajor := flatMotives.map fun expression =>
    (view.nested.restoreRecAt projectionLevels expression).instRevAt params 1
  let flatExact := view.flatView.generatedProjectionMinorType constructor
    fieldSort levels flatParamsMajor flatMotives
  let exactMinor :=
    (((view.nested.restoreRecAt projectionLevels
      ((gen.minorType constructor).instL projectionLevels)).instRevAt
        paramsMajor gen.familyCount).instRev motivesMajor)
  let count := (view.flatView.specializedCtorFields constructor levels
    flatParamsMajor).length + constructor.ctor.view.recursive.length
  dsimp only
  have flatMotivesLength : flatMotives.length = gen.familyCount := by
    simp [flatMotives, VRestoredBlockStructureView.flatView, gen]
  have flatBindersLength :
      (VExpr.telN count flatExact).length = count := by
    simpa [count, flatExact, VRestoredBlockStructureView.flatView, gen] using
      view.flatView.generatedProjectionMinorBinders_length constructor
        fieldSort levels flatParamsMajor flatMotives flatMotivesLength
  let restore := view.nested.restoreRecAt projectionLevels
  have restoredBindersLength :
      (VExpr.telN count (restore flatExact)).length = count := by
    unfold restore NestedBlockChecked.restoreRecAt
    rw [← VInductDecl.restoreExpr_telN _ _ count flatExact
      flatBindersLength]
    simp [flatBindersLength]
  have specializedBinders := VExpr.telN_instRevAt count
    (restore flatExact) params 1 restoredBindersLength
  have specializedBindersLength :
      (VExpr.telN count ((restore flatExact).instRevAt params 1)).length =
        count := by
    rw [specializedBinders]
    simp [restoredBindersLength]
  have exactBridge := self.restoredProjectionMinorType_eq henv closed
    constructor hconstructor fieldSort levels params hparamsLength
      flatTemplate flatTypeFnLam
  dsimp only at exactBridge
  change (restore flatExact).instRevAt params 1 = exactMinor at exactBridge
  rw [exactBridge] at specializedBindersLength
  exact specializedBindersLength

/-- The restored selected flattened minor specializes to the canonical
field selector over the exact live recursor minor telescope. -/
theorem ConstructorParameterLayoutWF.restoredSelectedMinorWith_shape
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.ConstructorParameterLayoutWF env) (henv : env.ConversionRegular)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    (fieldSort : VLevel) (levels : List VLevel)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (flatTemplate : VStructureView.ProjectionCode)
    (flatTypeFnLam : ∃ domain body,
      flatTemplate.typeFn = .lam domain body)
    (index : Nat)
    (hindex : index < (view.specializedFields levels params).length) :
    let gen := view.nested.generation
    let constructor := view.flatView.blockConstructor
    let projectionLevels := view.flatView.projectionLevels fieldSort levels
    let formalParams := VExpr.bvarRevRange 0 view.nparams
    let flatParamsMajor := formalParams.map (VExpr.liftN 1)
    let paramsMajor := params.map (VExpr.liftN 1)
    let flatDummyType := VBlockStructureView.majorDummyType
      flatTemplate.typeFn.lift (.bvar 0)
    let flatDummyValue := VBlockStructureView.majorDummyValue
      flatTemplate.typeFn.lift (.bvar 0)
    let flatMotives := view.flatView.projectionMotivesWith levels
      flatParamsMajor flatTemplate.typeFn.lift flatDummyType
    let motivesMajor := flatMotives.map fun expression =>
      (view.nested.restoreRecAt projectionLevels expression).instRevAt params 1
    let flatSelectedMinor := view.flatView.projectionMinorWith constructor
      fieldSort levels flatParamsMajor
        (view.flatView.specializedFields levels flatParamsMajor)
        flatMotives index flatDummyValue
    let exactMinor :=
      (((view.nested.restoreRecAt projectionLevels
        ((gen.minorType constructor).instL projectionLevels)).instRevAt
          paramsMajor gen.familyCount).instRev motivesMajor)
    let count := (view.flatView.specializedCtorFields constructor levels
      flatParamsMajor).length + constructor.ctor.view.recursive.length
    (view.nested.restoreRecAt projectionLevels flatSelectedMinor).instRevAt
        params 1 =
      VExpr.lamN (VExpr.telN count exactMinor)
        (.bvar (constructor.ctor.view.recursive.length +
          (view.flatView.specializedCtorFields constructor levels
            flatParamsMajor).length - 1 - index)) := by
  let gen := view.nested.generation
  let constructor := view.flatView.blockConstructor
  let projectionLevels := view.flatView.projectionLevels fieldSort levels
  let formalParams := VExpr.bvarRevRange 0 view.nparams
  let flatParamsMajor := formalParams.map (VExpr.liftN 1)
  let paramsMajor := params.map (VExpr.liftN 1)
  let flatDummyType := VBlockStructureView.majorDummyType
    flatTemplate.typeFn.lift (.bvar 0)
  let flatDummyValue := VBlockStructureView.majorDummyValue
    flatTemplate.typeFn.lift (.bvar 0)
  let flatMotives := view.flatView.projectionMotivesWith levels
    flatParamsMajor flatTemplate.typeFn.lift flatDummyType
  let motivesMajor := flatMotives.map fun expression =>
    (view.nested.restoreRecAt projectionLevels expression).instRevAt params 1
  let flatExact := view.flatView.generatedProjectionMinorType constructor
    fieldSort levels flatParamsMajor flatMotives
  let flatSelectedMinor := view.flatView.projectionMinorWith constructor
    fieldSort levels flatParamsMajor
      (view.flatView.specializedFields levels flatParamsMajor)
      flatMotives index flatDummyValue
  let exactMinor :=
    (((view.nested.restoreRecAt projectionLevels
      ((gen.minorType constructor).instL projectionLevels)).instRevAt
        paramsMajor gen.familyCount).instRev motivesMajor)
  let count := (view.flatView.specializedCtorFields constructor levels
    flatParamsMajor).length + constructor.ctor.view.recursive.length
  let flatBinders := VExpr.telN count flatExact
  let selector := VExpr.bvar (constructor.ctor.view.recursive.length +
    (view.flatView.specializedCtorFields constructor levels
      flatParamsMajor).length - 1 - index)
  dsimp only
  have flatMotivesLength : flatMotives.length = gen.familyCount := by
    simp [flatMotives, VRestoredBlockStructureView.flatView, gen]
  have flatBindersLength : flatBinders.length = count := by
    simpa [flatBinders, count, flatExact,
      VRestoredBlockStructureView.flatView, gen] using
        view.flatView.generatedProjectionMinorBinders_length constructor
          fieldSort levels flatParamsMajor flatMotives flatMotivesLength
  have flatFieldsEq : view.flatView.specializedFields levels
      flatParamsMajor =
      view.flatView.specializedCtorFields constructor levels
        flatParamsMajor := by
    rfl
  have flatIhsLength :
      (view.flatView.projectionIHTypes fieldSort levels flatParamsMajor
        flatMotives).length = constructor.ctor.view.recursive.length := by
    simpa [constructor, VBlockStructureView.blockConstructor] using
      view.flatView.projectionIHTypes_length fieldSort levels
        (by simpa only [view.flatView_uvars] using hlevelsLength)
        flatParamsMajor flatMotives (by
          simpa [gen, VRestoredBlockStructureView.flatView] using
            flatMotivesLength)
  have flatBindersEq : flatBinders =
      view.flatView.specializedFields levels flatParamsMajor ++
        view.flatView.projectionIHTypes fieldSort levels flatParamsMajor
          flatMotives := by
    have decomposition : flatExact =
        VExpr.forallN
          (view.flatView.specializedFields levels flatParamsMajor)
          (VExpr.forallN
            (view.flatView.projectionIHTypes fieldSort levels flatParamsMajor
              flatMotives)
            (VExpr.dropN view.flatView.constructor.view.recursive.length
              (VExpr.dropN
                (view.flatView.specializedFields levels
                  flatParamsMajor).length flatExact))) := by
      simpa [flatExact, constructor] using
        view.flatView.projectionMinorType_decompose
          fieldSort levels (by
            simpa only [view.flatView_uvars] using hlevelsLength)
          flatParamsMajor flatMotives (by
            simpa [gen, VRestoredBlockStructureView.flatView] using
              flatMotivesLength)
    unfold flatBinders count
    rw [decomposition, flatFieldsEq]
    rw [show (view.flatView.specializedCtorFields constructor levels
          flatParamsMajor).length + constructor.ctor.view.recursive.length =
        (view.flatView.specializedFields levels flatParamsMajor ++
          view.flatView.projectionIHTypes fieldSort levels flatParamsMajor
            flatMotives).length by
      simp [flatFieldsEq, flatIhsLength]]
    rw [← VExpr.forallN_append]
    exact VExpr.telN_forallN_length _ _
  have flatSelectedShape : flatSelectedMinor =
      VExpr.lamN flatBinders selector := by
    unfold flatSelectedMinor
    have selectedOwner : constructor.owner =
        view.flatView.family.view.ordinal := by
      rfl
    unfold VBlockStructureView.projectionMinorWith
    rw [if_pos selectedOwner]
    unfold VExpr.selectFieldMinor
    rw [← VExpr.lamN_append, ← flatBindersEq]
    congr 2
    rw [flatIhsLength, flatFieldsEq]
  let restore := view.nested.restoreRecAt projectionLevels
  have restoredBinders : flatBinders.map restore =
      VExpr.telN count (restore flatExact) := by
    unfold restore NestedBlockChecked.restoreRecAt
    exact VInductDecl.restoreExpr_telN _ _ count flatExact
      flatBindersLength
  have restoredBindersLength :
      (VExpr.telN count (restore flatExact)).length = count := by
    rw [← restoredBinders]
    simp [flatBindersLength]
  have specializedBinders :
      ((flatBinders.map restore).zipIdx 1).map (fun entry =>
        entry.1.instRevAt params entry.2) =
      VExpr.telN count ((restore flatExact).instRevAt params 1) := by
    rw [restoredBinders]
    exact (VExpr.telN_instRevAt count (restore flatExact) params 1
      restoredBindersLength).symm
  have exactBridge := self.restoredProjectionMinorType_eq henv closed
    constructor view.flatView.blockConstructor_mem fieldSort levels params
      hparamsLength flatTemplate flatTypeFnLam
  dsimp only at exactBridge
  change (restore flatExact).instRevAt params 1 = exactMinor at exactBridge
  have specializedBinders' :
      ((flatBinders.map restore).zipIdx 1).map (fun entry =>
        entry.1.instRevAt params entry.2) = VExpr.telN count exactMinor := by
    rw [specializedBinders, exactBridge]
  have selectorClosed : selector.ClosedN flatBinders.length := by
    unfold selector VExpr.ClosedN
    rw [flatBindersLength]
    have flatFieldsLength :
        (view.flatView.specializedCtorFields constructor levels
          flatParamsMajor).length =
          (view.specializedFields levels params).length := by
      have fieldsLength : view.flatView.fields.length =
          view.fields.length := by
        simpa [fields, flatView, VBlockStructureView.fields] using
          view.selection.source_flat_fields_length_eq.symm
      calc
        (view.flatView.specializedCtorFields constructor levels
            flatParamsMajor).length = view.flatView.fields.length := by
          simp [VBlockStructureView.specializedCtorFields,
            VBlockStructureView.fields, constructor,
            VBlockStructureView.blockConstructor]
        _ = view.fields.length := fieldsLength
        _ = (view.specializedFields levels params).length := by
          simp [specializedFields]
    unfold count
    rw [flatFieldsLength]
    omega
  change (restore flatSelectedMinor).instRevAt params 1 =
    VExpr.lamN (VExpr.telN count exactMinor) selector
  have restoreSelector : restore selector = selector := by
    simp [restore, NestedBlockChecked.restoreRecAt, selector,
      VInductDecl.restoreExpr]
  rw [flatSelectedShape]
  unfold restore NestedBlockChecked.restoreRecAt
  rw [VInductDecl.restoreExpr_lamN,
    VExpr.instRevAt_lamN_projection]
  change VExpr.lamN
      (((flatBinders.map (view.nested.restoreRecAt projectionLevels)).zipIdx
        1).map fun entry => entry.1.instRevAt params entry.2) _ = _
  rw [specializedBinders']
  congr 1
  change (restore selector).instRevAt params
    (1 + (flatBinders.map restore).length) = selector
  rw [restoreSelector]
  apply VExpr.instRevAt_closedN
  apply selectorClosed.mono
  simp

/-- The selected flattened constructor supplies only its constructor major
to the selected motive, weakened beneath the exact generated IH suffix. -/
private theorem flatGeneratedProjectionMinorArguments_selected
    (view : VRestoredBlockStructureView) (fieldSort : VLevel)
    (levels : List VLevel) (hlevelsLength : levels.length = view.uvars)
    (params motives : List VExpr)
    (hparamsLength : params.length = view.nparams)
    (hmotives : motives.length = view.nested.generation.familyCount) :
    view.flatView.generatedProjectionMinorArguments
        view.flatView.blockConstructor fieldSort levels params motives =
      [(view.flatView.projectionConstructorApp levels params
          (view.flatView.specializedFields levels params)).liftN
        (view.flatView.projectionIHTypes fieldSort levels params
          motives).length] := by
  let gen := view.nested.generation
  let fields := view.flatView.specializedFields levels params
  let m := fields.length
  let r := view.flatView.constructor.view.recursive.length
  have hparamsLengthFlat : params.length = view.flatView.nparams := by
    simpa only [view.flatView_nparams] using hparamsLength
  have hmotivesFlat : motives.length =
      view.flatView.generation.familyCount := by
    simpa [VRestoredBlockStructureView.flatView] using hmotives
  have hrawFieldsLength :
      (view.flatView.blockConstructor.ctor.fieldsR view.flatView.uvars
        view.flatView.nparams
        view.flatView.generation.elimination).length = m := by
    simp [fields, m, VBlockStructureView.specializedFields,
      VBlockStructureView.fields, VBlockStructureView.blockConstructor,
      NormalizedCtor.fieldsR]
  have hrecArgsLength :
      (view.flatView.blockConstructor.ctor.recArgsR view.flatView.uvars
        view.flatView.generation.elimination).length = r := by
    simp [r, VBlockStructureView.blockConstructor,
      NormalizedCtor.recArgsR]
  have hihsLength :
      (view.flatView.projectionIHTypes fieldSort levels params motives).length =
        r := by
    simpa [r] using view.flatView.projectionIHTypes_length fieldSort levels
      (by simpa only [view.flatView_uvars] using hlevelsLength)
      params motives hmotivesFlat
  have hresultIndices : view.flatView.constructor.view.resultIndices = [] := by
    apply List.length_eq_zero_iff.1
    have hlength : view.flatView.constructor.view.resultIndices.length =
        view.flatView.family.view.indices.length := by
      simpa [VBlockStructureView.blockConstructor] using
        gen.view_resultIndices_length view.flatView.blockConstructor_mem
    rw [hlength, view.flatView.checked_indices_eq]
    rfl
  have hsource := view.flatView.sourceLevels_projectionLevels fieldSort levels
    (by simpa only [view.flatView_uvars] using hlevelsLength)
  have hparamsRange :
      (VExpr.bvarRevRange (r + m + view.flatView.generation.familyCount)
          view.flatView.nparams).map
        (fun expression => expression.instRevAt (params ++ motives) (m + r)) =
      params.map (VExpr.liftN (m + r)) := by
    have hout := VExpr.map_instRevAt_bvarRevRange_prefix
      params motives (m + r)
    rw [hparamsLengthFlat, hmotivesFlat] at hout
    rw [show r + m + view.flatView.generation.familyCount =
      m + r + view.flatView.generation.familyCount by omega]
    exact hout
  have hfieldsRange :
      (VExpr.bvarRevRange r m).map
        (fun expression => expression.instRevAt (params ++ motives) (m + r)) =
      VExpr.bvarRevRange r m := by
    calc
      _ = (VExpr.bvarRevRange r m).map id := by
        apply List.map_congr_left
        intro expression hexpression
        apply VExpr.instRevAt_closedN
        exact bvarRevRange_closedN m r (m + r) (by omega)
          expression hexpression
      _ = _ := by simp
  unfold VBlockStructureView.generatedProjectionMinorArguments
  dsimp only
  rw [hrawFieldsLength, hrecArgsLength]
  simp only [VBlockStructureView.blockConstructor,
    NormalizedCtor.resultIndicesR, hresultIndices, List.map_nil,
    List.nil_append, List.map_singleton, VExpr.instL_appN, VExpr.instL,
    List.map_append, VExpr.bvarRevRange_map_instL]
  rw [hsource, VExpr.instRevAt_appN_projection,
    VExpr.instRevAt_closedN (params ++ motives) (by trivial),
    List.map_append, hparamsRange, hfieldsRange]
  rw [hihsLength]
  simp only [VBlockStructureView.projectionConstructorApp, fields, m, r,
    VExpr.liftN, VExpr.liftN_appN, VExpr.bvarRevRange_liftN_low,
    List.map_append, List.map_map, Function.comp_def]
  rw [Nat.add_zero]
  congr 1
  apply congrArg (VExpr.appN
    (.const view.flatView.constructorName levels))
  congr 1
  apply List.map_congr_left
  intro param _
  rw [VExpr.liftN_liftN]

/-- Restoring the selected flattened constructor major and specializing its
formal parameters produces the literal source constructor major beneath the
same field and recursive-IH suffix. -/
private theorem restoredFlatProjectionConstructorApp_specialize
    (view : VRestoredBlockStructureView)
    (projectionLevels : List VLevel) (levels : List VLevel)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (flatFields fields : List VExpr)
    (hfieldsLength : flatFields.length = fields.length)
    (ihCount : Nat) :
    let formalParams := VExpr.bvarRevRange 0 view.nparams
    let flatParamsMajor := formalParams.map (VExpr.liftN 1)
    let paramsMajor := params.map (VExpr.liftN 1)
    ((view.nested.restoreRecAt projectionLevels
      ((view.flatView.projectionConstructorApp levels flatParamsMajor
        flatFields).liftN ihCount)).instRevAt params
          (1 + flatFields.length + ihCount)) =
      (view.projectionConstructorApp levels paramsMajor fields).liftN
        ihCount := by
  let formalParams := VExpr.bvarRevRange 0 view.nparams
  let flatParamsMajor := formalParams.map (VExpr.liftN 1)
  let paramsMajor := params.map (VExpr.liftN 1)
  let flatMajor := view.flatView.projectionConstructorApp levels
    flatParamsMajor flatFields
  let canonical := VExpr.appN (.const view.constructorName levels)
    (VExpr.bvarRevRange (1 + flatFields.length + ihCount) view.nparams ++
      VExpr.bvarRevRange ihCount flatFields.length)
  dsimp only
  have flatMajorLift : flatMajor.liftN ihCount = canonical := by
    unfold flatMajor canonical VBlockStructureView.projectionConstructorApp
    rw [view.flatView_constructorName]
    simp only [flatParamsMajor, formalParams, VExpr.liftN,
      VExpr.liftN_appN, List.map_append, List.map_map,
      Function.comp_def]
    have paramsLift :
        (VExpr.bvarRevRange 0 view.nparams).map
            (fun expression =>
              (expression.liftN 1).liftN flatFields.length
                |>.liftN ihCount) =
          VExpr.bvarRevRange
            (1 + flatFields.length + ihCount) view.nparams := by
      calc
        _ = (VExpr.bvarRevRange 0 view.nparams).map
            (VExpr.liftN (1 + flatFields.length + ihCount)) := by
              apply List.map_congr_left
              intro expression _
              rw [VExpr.liftN_liftN, VExpr.liftN_liftN]
              congr 1
              omega
        _ = VExpr.bvarRevRange
            (1 + flatFields.length + ihCount) view.nparams := by
              simpa using VExpr.bvarRevRange_liftN_low view.nparams 0
                (1 + flatFields.length + ihCount)
    have fieldsLift :
        (VExpr.bvarRevRange 0 flatFields.length).map
            (VExpr.liftN ihCount) =
          VExpr.bvarRevRange ihCount flatFields.length := by
      simpa using VExpr.bvarRevRange_liftN_low
        flatFields.length 0 ihCount
    apply congrArg (VExpr.appN (.const view.constructorName levels))
    calc
      _ = VExpr.bvarRevRange
          (1 + flatFields.length + ihCount) view.nparams ++
            (VExpr.bvarRevRange 0 flatFields.length).map
              (VExpr.liftN ihCount) := by
        exact congrArg
          (fun left => left ++
            (VExpr.bvarRevRange 0 flatFields.length).map
              (VExpr.liftN ihCount)) paramsLift
      _ = _ := by
        exact congrArg
          (fun right => VExpr.bvarRevRange
            (1 + flatFields.length + ihCount) view.nparams ++ right)
          fieldsLift
  have canonicalInert : RestoreInert
      (view.nested.recEntries.map (·.instL projectionLevels))
      view.nested.recMap canonical := by
    unfold canonical
    apply (view.nested.sourceConstructorName_restoreRecInert
      view.sourceFamily_mem view.sourceConstructor_mem levels
        |>.instLEntries projectionLevels).appN
    intro argument member
    rcases List.mem_append.mp member with parameter | field
    · exact bvarRevRange_restoreInert _ _ _ _ argument parameter
    · exact bvarRevRange_restoreInert _ _ _ _ argument field
  have restoredCanonical :
      view.nested.restoreRecAt projectionLevels canonical = canonical := by
    exact canonicalInert.restoreExpr_eq
  rw [flatMajorLift, restoredCanonical]
  unfold canonical VRestoredBlockStructureView.projectionConstructorApp
  rw [VExpr.instRevAt_appN_projection]
  rw [VExpr.instRevAt_closedN params
    (C := .const view.constructorName levels) (by trivial)]
  rw [List.map_append]
  have paramsRange :
      (VExpr.bvarRevRange (1 + flatFields.length + ihCount)
        view.nparams).map
          (fun expression => expression.instRevAt params
            (1 + flatFields.length + ihCount)) =
        params.map (VExpr.liftN (1 + flatFields.length + ihCount)) := by
    rw [← hparamsLength]
    exact VExpr.map_instRevAt_bvarRevRange params
      (1 + flatFields.length + ihCount)
  have fieldsRange :
      (VExpr.bvarRevRange ihCount flatFields.length).map
          (fun expression => expression.instRevAt params
            (1 + flatFields.length + ihCount)) =
        VExpr.bvarRevRange ihCount flatFields.length := by
    calc
      _ = (VExpr.bvarRevRange ihCount flatFields.length).map id := by
        apply List.map_congr_left
        intro expression member
        apply VExpr.instRevAt_closedN
        exact bvarRevRange_closedN flatFields.length ihCount
          (1 + flatFields.length + ihCount) (by omega) expression member
      _ = _ := by simp
  rw [paramsRange, fieldsRange]
  simp only [VExpr.liftN, VExpr.liftN_appN,
    List.map_append, List.map_map, Function.comp_def]
  rw [VExpr.bvarRevRange_liftN_low]
  rw [hfieldsLength]
  have paramsLift :
      params.map (VExpr.liftN (1 + fields.length + ihCount)) =
        params.map (fun parameter =>
          ((parameter.liftN 1).liftN fields.length).liftN ihCount) := by
    apply List.map_congr_left
    intro parameter _
    rw [VExpr.liftN_liftN]
    rw [VExpr.liftN_liftN]
    congr 1
    omega
  have fieldsLift : VExpr.bvarRevRange ihCount fields.length =
      VExpr.bvarRevRange (ihCount + 0) fields.length := by simp
  apply congrArg (VExpr.appN (.const view.constructorName levels))
  calc
    _ = params.map (fun parameter =>
        ((parameter.liftN 1).liftN fields.length).liftN ihCount) ++
          VExpr.bvarRevRange ihCount fields.length := by
      exact congrArg
        (fun left => left ++ VExpr.bvarRevRange ihCount fields.length)
        paramsLift
    _ = _ := by
      exact congrArg
        (fun right => params.map (fun parameter =>
          ((parameter.liftN 1).liftN fields.length).liftN ihCount) ++ right)
        fieldsLift

/-- The exact restored selected minor returns the live selected motive at the
canonical restored constructor major, weakened beneath its generated IH
suffix. -/
theorem ConstructorParameterLayoutWF.restoredSelectedMinorResult_shape
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.ConstructorParameterLayoutWF env) (henv : env.ConversionRegular)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    (fieldSort : VLevel) (levels : List VLevel)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (flatTemplate : VStructureView.ProjectionCode)
    (flatTypeFnLam : ∃ domain body,
      flatTemplate.typeFn = .lam domain body)
    {typeFn : VExpr}
    (selectedMotiveEq :
      (view.nested.restoreRecAt
        (view.flatView.projectionLevels fieldSort levels)
        flatTemplate.typeFn.lift).instRevAt params 1 = typeFn.lift) :
    let gen := view.nested.generation
    let constructor := view.flatView.blockConstructor
    let projectionLevels := view.flatView.projectionLevels fieldSort levels
    let formalParams := VExpr.bvarRevRange 0 view.nparams
    let flatParamsMajor := formalParams.map (VExpr.liftN 1)
    let paramsMajor := params.map (VExpr.liftN 1)
    let flatDummyType := VBlockStructureView.majorDummyType
      flatTemplate.typeFn.lift (.bvar 0)
    let flatMotives := view.flatView.projectionMotivesWith levels
      flatParamsMajor flatTemplate.typeFn.lift flatDummyType
    let motivesMajor := flatMotives.map fun expression =>
      (view.nested.restoreRecAt projectionLevels expression).instRevAt params 1
    let exactMinor :=
      (((view.nested.restoreRecAt projectionLevels
        ((gen.minorType constructor).instL projectionLevels)).instRevAt
          paramsMajor gen.familyCount).instRev motivesMajor)
    let fields := view.specializedFields levels paramsMajor
    let ihCount := constructor.ctor.view.recursive.length
    let count := fields.length + ihCount
    VExpr.dropN count exactMinor =
      (VExpr.app ((typeFn.lift).liftN fields.length)
        (view.projectionConstructorApp levels paramsMajor fields)).liftN
          ihCount := by
  let gen := view.nested.generation
  let constructor := view.flatView.blockConstructor
  let projectionLevels := view.flatView.projectionLevels fieldSort levels
  let formalParams := VExpr.bvarRevRange 0 view.nparams
  let flatParamsMajor := formalParams.map (VExpr.liftN 1)
  let paramsMajor := params.map (VExpr.liftN 1)
  let flatDummyType := VBlockStructureView.majorDummyType
    flatTemplate.typeFn.lift (.bvar 0)
  let flatMotives := view.flatView.projectionMotivesWith levels
    flatParamsMajor flatTemplate.typeFn.lift flatDummyType
  let motivesMajor := flatMotives.map fun expression =>
    (view.nested.restoreRecAt projectionLevels expression).instRevAt params 1
  let flatExact := view.flatView.generatedProjectionMinorType constructor
    fieldSort levels flatParamsMajor flatMotives
  let exactMinor :=
    (((view.nested.restoreRecAt projectionLevels
      ((gen.minorType constructor).instL projectionLevels)).instRevAt
        paramsMajor gen.familyCount).instRev motivesMajor)
  let flatFields := view.flatView.specializedFields levels flatParamsMajor
  let fields := view.specializedFields levels paramsMajor
  let flatIhs := view.flatView.projectionIHTypes fieldSort levels
    flatParamsMajor flatMotives
  let ihCount := constructor.ctor.view.recursive.length
  let count := fields.length + ihCount
  let flatCount := flatFields.length + ihCount
  let flatMotive := flatTemplate.typeFn.lift
  let flatArguments := view.flatView.generatedProjectionMinorArguments
    constructor fieldSort levels flatParamsMajor flatMotives
  let restore := view.nested.restoreRecAt projectionLevels
  dsimp only
  have flatMotivesLength : flatMotives.length = gen.familyCount := by
    simp [flatMotives, gen, VRestoredBlockStructureView.flatView]
  have flatFieldsLength : flatFields.length = fields.length := by
    calc
      flatFields.length = view.flatView.fields.length := by
        simp [flatFields, VBlockStructureView.specializedFields]
      _ = view.fields.length := by
        simpa [VRestoredBlockStructureView.fields,
          VRestoredBlockStructureView.flatView,
          VBlockStructureView.fields] using
            view.selection.source_flat_fields_length_eq.symm
      _ = fields.length := by
        simp [fields, VRestoredBlockStructureView.specializedFields]
  have countEq : flatCount = count := by
    simp [flatCount, count, flatFieldsLength]
  have flatIhsLength : flatIhs.length = ihCount := by
    simpa [flatIhs, ihCount, constructor,
      VBlockStructureView.blockConstructor] using
      view.flatView.projectionIHTypes_length fieldSort levels
        (by simpa only [view.flatView_uvars] using hlevelsLength)
        flatParamsMajor flatMotives (by
          simpa [gen, VRestoredBlockStructureView.flatView] using
            flatMotivesLength)
  have resultIndicesLength :
      constructor.ctor.view.resultIndices.length =
        view.flatView.family.view.indices.length := by
    calc
      constructor.ctor.view.resultIndices.length =
          constructor.familyIndices.length :=
        gen.view_resultIndices_length view.flatView.blockConstructor_mem
      _ = view.flatView.family.view.indices.length := by
        rfl
  have motiveAt :
      flatMotives[view.flatView.family.view.ordinal]? = some flatMotive := by
    simpa [flatMotives, flatMotive,
      VRestoredBlockStructureView.flatView] using
        view.flatView.projectionMotivesWith_getElem?_ordinal
          view.flatView.family view.flatView.family_mem levels flatParamsMajor
            flatMotive flatDummyType
  have flatResult :=
    (view.flatView.generatedProjectionMinorResult_motive constructor
      view.flatView.family rfl resultIndicesLength fieldSort levels
      flatParamsMajor flatMotives flatMotive flatMotivesLength motiveAt).2
  have flatSelectedArguments : flatArguments =
      [(view.flatView.projectionConstructorApp levels flatParamsMajor
        flatFields).liftN ihCount] := by
    have selected := flatGeneratedProjectionMinorArguments_selected view
      fieldSort levels hlevelsLength flatParamsMajor flatMotives
        (by simp [flatParamsMajor, formalParams]) flatMotivesLength
    change flatArguments =
      [(view.flatView.projectionConstructorApp levels flatParamsMajor
        flatFields).liftN flatIhs.length] at selected
    rw [flatIhsLength] at selected
    exact selected
  have flatCtorFieldsEq :
      view.flatView.specializedCtorFields constructor levels
        flatParamsMajor = flatFields := by
    rfl
  have recursiveCountEq :
      constructor.ctor.view.recursive.length = ihCount := by
    rfl
  have flatBindersLength :
      (VExpr.telN flatCount flatExact).length = flatCount := by
    have raw :=
      view.flatView.generatedProjectionMinorBinders_length constructor
        fieldSort levels flatParamsMajor flatMotives flatMotivesLength
    rw [flatCtorFieldsEq, recursiveCountEq] at raw
    simpa [flatCount, flatExact] using raw
  have restoreDrop : restore (VExpr.dropN flatCount flatExact) =
      VExpr.dropN flatCount (restore flatExact) := by
    unfold restore NestedBlockChecked.restoreRecAt
    exact VInductDecl.restoreExpr_dropN _ _ flatCount flatExact
      flatBindersLength
  let restoredMotive := restore flatMotive
  have restoreMotiveLift : restore (flatMotive.liftN flatCount) =
      restoredMotive.liftN flatCount := by
    unfold restore restoredMotive NestedBlockChecked.restoreRecAt
    exact (VInductDecl.restoreExpr_liftN _ (closed.instL projectionLevels)
      _ flatMotive flatCount 0).symm
  have restoredMotiveHead : ∀ name nameLevels,
      (restoredMotive.liftN flatCount).appHead ≠ .const name nameLevels := by
    obtain ⟨domain, body, typeFnShape⟩ := flatTypeFnLam
    unfold restoredMotive restore flatMotive NestedBlockChecked.restoreRecAt
    rw [typeFnShape]
    simp [VExpr.lift, VExpr.liftN, VInductDecl.restoreExpr,
      VExpr.appHead]
  let restoredArguments := flatArguments.map restore
  have restoreApp : restore
      (VExpr.appN (flatMotive.liftN flatCount) flatArguments) =
      VExpr.appN (restoredMotive.liftN flatCount) restoredArguments := by
    unfold restoredArguments
    exact VInductDecl.restoreExpr_appN_of_nonConst_head restoreMotiveLift
      restoredMotiveHead
  have flatResult' : VExpr.dropN flatCount flatExact =
      VExpr.appN (flatMotive.liftN flatCount) flatArguments := by
    rw [flatCtorFieldsEq, recursiveCountEq] at flatResult
    simpa [flatCount, flatExact, flatArguments] using flatResult
  have restoredResult := congrArg restore flatResult'
  rw [restoreDrop, restoreApp] at restoredResult
  have restoredBindersLength :
      (VExpr.telN flatCount (restore flatExact)).length = flatCount := by
    unfold restore NestedBlockChecked.restoreRecAt
    rw [← VInductDecl.restoreExpr_telN _ _ flatCount flatExact
      flatBindersLength]
    simp [flatBindersLength]
  have specializedResult := congrArg
    (fun expression : VExpr =>
      expression.instRevAt params (1 + flatCount)) restoredResult
  have dropSpecialize := VExpr.dropN_instRevAt flatCount
    (restore flatExact) params 1 restoredBindersLength
  rw [← dropSpecialize] at specializedResult
  have exactBridge := self.restoredProjectionMinorType_eq henv closed
    constructor view.flatView.blockConstructor_mem fieldSort levels params
      hparamsLength flatTemplate flatTypeFnLam
  dsimp only at exactBridge
  change (restore flatExact).instRevAt params 1 = exactMinor at exactBridge
  rw [exactBridge, VExpr.instRevAt_appN_projection] at specializedResult
  rw [show 1 + flatCount = 1 + 0 + flatCount by omega,
    VExpr.liftN_instRevAt_shift] at specializedResult
  have restoredSelectedMotive :
      restoredMotive.instRevAt params 1 = typeFn.lift := by
    simpa [restoredMotive, restore, flatMotive, projectionLevels] using
      selectedMotiveEq
  rw [restoredSelectedMotive] at specializedResult
  have specializedArguments :
      restoredArguments.map (fun expression =>
        expression.instRevAt params (1 + flatCount)) =
      [(view.projectionConstructorApp levels paramsMajor fields).liftN
        ihCount] := by
    unfold restoredArguments
    rw [flatSelectedArguments]
    simp only [List.map_singleton]
    congr 1
    simpa only [flatCount, flatParamsMajor, formalParams, paramsMajor,
      restore, Nat.add_assoc] using
      restoredFlatProjectionConstructorApp_specialize view
        projectionLevels levels params hparamsLength flatFields fields
          flatFieldsLength ihCount
  change VExpr.dropN flatCount exactMinor =
      VExpr.appN ((typeFn.lift).liftN flatCount)
        (restoredArguments.map fun expression =>
          expression.instRevAt params (1 + flatCount)) at specializedResult
  rw [specializedArguments] at specializedResult
  simp only [VExpr.appN] at specializedResult
  rw [countEq] at specializedResult
  change VExpr.dropN count exactMinor = _
  rw [specializedResult]
  change VExpr.app ((typeFn.lift).liftN count)
      ((view.projectionConstructorApp levels paramsMajor fields).liftN
        ihCount) =
    VExpr.app (((typeFn.lift).liftN fields.length).liftN ihCount)
      ((view.projectionConstructorApp levels paramsMajor fields).liftN
        ihCount)
  have functionLift : (typeFn.lift).liftN count =
      ((typeFn.lift).liftN fields.length).liftN ihCount := by
    simpa [count] using
      (VExpr.liftN_liftN (typeFn.lift) fields.length ihCount).symm
  rw [functionLift]

/-- A restored nonselected flattened minor specializes to the canonical
constant minor over the exact live recursor binder telescope. -/
theorem ConstructorParameterLayoutWF.restoredIdentityMinorWith_shape
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.ConstructorParameterLayoutWF env) (henv : env.ConversionRegular)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    (constructor : NormalizedBlockCtor)
    (hconstructor : constructor ∈ view.nested.generation.flatCtors)
    (fieldSort : VLevel) (levels : List VLevel)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (flatTemplate : VStructureView.ProjectionCode)
    (flatTypeFnLam : ∃ domain body,
      flatTemplate.typeFn = .lam domain body)
    (dummyValue : VExpr)
    (dummyValueEq :
      let projectionLevels := view.flatView.projectionLevels fieldSort levels
      let flatDummyValue := VBlockStructureView.majorDummyValue
        flatTemplate.typeFn.lift (.bvar 0)
      (view.nested.restoreRecAt projectionLevels flatDummyValue).instRevAt
        params 1 = dummyValue) :
    let gen := view.nested.generation
    let projectionLevels := view.flatView.projectionLevels fieldSort levels
    let formalParams := VExpr.bvarRevRange 0 view.nparams
    let flatParamsMajor := formalParams.map (VExpr.liftN 1)
    let paramsMajor := params.map (VExpr.liftN 1)
    let flatDummyType := VBlockStructureView.majorDummyType
      flatTemplate.typeFn.lift (.bvar 0)
    let flatDummyValue := VBlockStructureView.majorDummyValue
      flatTemplate.typeFn.lift (.bvar 0)
    let flatMotives := view.flatView.projectionMotivesWith levels
      flatParamsMajor flatTemplate.typeFn.lift flatDummyType
    let motivesMajor := flatMotives.map fun expression =>
      (view.nested.restoreRecAt projectionLevels expression).instRevAt params 1
    let exactMinor :=
      (((view.nested.restoreRecAt projectionLevels
        ((gen.minorType constructor).instL projectionLevels)).instRevAt
          paramsMajor gen.familyCount).instRev motivesMajor)
    let count := (view.flatView.specializedCtorFields constructor levels
      flatParamsMajor).length + constructor.ctor.view.recursive.length
    (view.nested.restoreRecAt projectionLevels
      (view.flatView.identityMinorWith constructor fieldSort levels
        flatParamsMajor flatMotives flatDummyValue)).instRevAt params 1 =
      VExpr.lamN (VExpr.telN count exactMinor)
        (dummyValue.liftN count) := by
  let gen := view.nested.generation
  let projectionLevels := view.flatView.projectionLevels fieldSort levels
  let formalParams := VExpr.bvarRevRange 0 view.nparams
  let flatParamsMajor := formalParams.map (VExpr.liftN 1)
  let paramsMajor := params.map (VExpr.liftN 1)
  let flatDummyType := VBlockStructureView.majorDummyType
    flatTemplate.typeFn.lift (.bvar 0)
  let flatDummyValue := VBlockStructureView.majorDummyValue
    flatTemplate.typeFn.lift (.bvar 0)
  let flatMotives := view.flatView.projectionMotivesWith levels
    flatParamsMajor flatTemplate.typeFn.lift flatDummyType
  let motivesMajor := flatMotives.map fun expression =>
    (view.nested.restoreRecAt projectionLevels expression).instRevAt params 1
  let flatExact := view.flatView.generatedProjectionMinorType constructor
    fieldSort levels flatParamsMajor flatMotives
  let exactMinor :=
    (((view.nested.restoreRecAt projectionLevels
      ((gen.minorType constructor).instL projectionLevels)).instRevAt
        paramsMajor gen.familyCount).instRev motivesMajor)
  let count := (view.flatView.specializedCtorFields constructor levels
    flatParamsMajor).length + constructor.ctor.view.recursive.length
  let flatBinders := VExpr.telN count flatExact
  dsimp only
  have flatMotivesLength : flatMotives.length = gen.familyCount := by
    simp [flatMotives, VRestoredBlockStructureView.flatView, gen]
  have flatBindersLength : flatBinders.length = count := by
    simpa [flatBinders, count, flatExact,
      VRestoredBlockStructureView.flatView, gen] using
        view.flatView.generatedProjectionMinorBinders_length constructor
          fieldSort levels flatParamsMajor flatMotives flatMotivesLength
  let restore := view.nested.restoreRecAt projectionLevels
  have restoredBinders : flatBinders.map restore =
      VExpr.telN count (restore flatExact) := by
    unfold restore NestedBlockChecked.restoreRecAt
    exact VInductDecl.restoreExpr_telN _ _ count flatExact
      flatBindersLength
  have restoredBindersLength :
      (VExpr.telN count (restore flatExact)).length = count := by
    rw [← restoredBinders]
    simp [flatBindersLength]
  have specializedBinders :
      ((flatBinders.map restore).zipIdx 1).map (fun entry =>
        entry.1.instRevAt params entry.2) =
      VExpr.telN count ((restore flatExact).instRevAt params 1) := by
    rw [restoredBinders]
    exact (VExpr.telN_instRevAt count (restore flatExact) params 1
      restoredBindersLength).symm
  have exactBridge := self.restoredProjectionMinorType_eq henv closed
    constructor hconstructor fieldSort levels params hparamsLength
      flatTemplate flatTypeFnLam
  dsimp only at exactBridge
  change (restore flatExact).instRevAt params 1 = exactMinor at exactBridge
  have specializedBinders' :
      ((flatBinders.map restore).zipIdx 1).map (fun entry =>
        entry.1.instRevAt params entry.2) =
      VExpr.telN count exactMinor := by
    rw [specializedBinders, exactBridge]
  have dummyEq : (restore flatDummyValue).instRevAt params 1 =
      dummyValue := by
    simpa [restore, flatDummyValue, projectionLevels] using dummyValueEq
  unfold VBlockStructureView.identityMinorWith
  change (restore (VExpr.lamN flatBinders
    (flatDummyValue.liftN flatBinders.length))).instRevAt params 1 = _
  unfold restore NestedBlockChecked.restoreRecAt
  rw [VInductDecl.restoreExpr_lamN,
    VExpr.instRevAt_lamN_projection]
  change VExpr.lamN
      (((flatBinders.map (view.nested.restoreRecAt projectionLevels)).zipIdx
        1).map fun entry => entry.1.instRevAt params entry.2) _ =
    VExpr.lamN (VExpr.telN count exactMinor) _
  rw [specializedBinders']
  congr 1
  rw [← VInductDecl.restoreExpr_liftN
    (view.nested.recEntries.map (·.instL projectionLevels))
    (closed.instL projectionLevels) view.nested.recMap flatDummyValue
      flatBinders.length 0]
  rw [flatBindersLength]
  simp only [List.length_map, flatBindersLength]
  change ((view.nested.restoreRecAt projectionLevels
    flatDummyValue).liftN count).instRevAt params (1 + count) =
      dummyValue.liftN count
  rw [show 1 + count = 1 + 0 + count by omega,
    VExpr.liftN_instRevAt_shift]
  change ((restore flatDummyValue).instRevAt params 1).liftN count = _
  rw [dummyEq]

/-- For a nonselected constructor, the exact restored minor's terminal
result applies the owning family's restored constant motive to precisely its
indices and constructed major. -/
theorem ConstructorParameterLayoutWF.restoredIdentityMinorResult_shape
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.ConstructorParameterLayoutWF env) (henv : env.ConversionRegular)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    (constructor : NormalizedBlockCtor)
    (hconstructor : constructor ∈ view.nested.generation.flatCtors)
    (hnotSelected : constructor.owner ≠
      view.selection.family.view.ordinal)
    (fieldSort : VLevel) (levels : List VLevel)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (flatTemplate : VStructureView.ProjectionCode)
    (flatTypeFnLam : ∃ domain body,
      flatTemplate.typeFn = .lam domain body) :
    let gen := view.nested.generation
    let projectionLevels := view.flatView.projectionLevels fieldSort levels
    let formalParams := VExpr.bvarRevRange 0 view.nparams
    let flatParamsMajor := formalParams.map (VExpr.liftN 1)
    let paramsMajor := params.map (VExpr.liftN 1)
    let flatDummyType := VBlockStructureView.majorDummyType
      flatTemplate.typeFn.lift (.bvar 0)
    let flatMotives := view.flatView.projectionMotivesWith levels
      flatParamsMajor flatTemplate.typeFn.lift flatDummyType
    let motivesMajor := flatMotives.map fun expression =>
      (view.nested.restoreRecAt projectionLevels expression).instRevAt params 1
    let exactMinor :=
      (((view.nested.restoreRecAt projectionLevels
        ((gen.minorType constructor).instL projectionLevels)).instRevAt
          paramsMajor gen.familyCount).instRev motivesMajor)
    let count := (view.flatView.specializedCtorFields constructor levels
      flatParamsMajor).length + constructor.ctor.view.recursive.length
    ∃ family ∈ gen.families,
      family.view.ordinal = constructor.owner ∧
      ∃ arguments,
        arguments.length = family.view.indices.length + 1 ∧
        VExpr.dropN count exactMinor =
          VExpr.appN
            (((view.nested.restoreRecAt projectionLevels
              (view.flatView.identityMotiveWith family levels
                flatParamsMajor flatDummyType)).instRevAt params 1).liftN
              count)
            arguments := by
  let gen := view.nested.generation
  let projectionLevels := view.flatView.projectionLevels fieldSort levels
  let formalParams := VExpr.bvarRevRange 0 view.nparams
  let flatParamsMajor := formalParams.map (VExpr.liftN 1)
  let paramsMajor := params.map (VExpr.liftN 1)
  let flatDummyType := VBlockStructureView.majorDummyType
    flatTemplate.typeFn.lift (.bvar 0)
  let flatMotives := view.flatView.projectionMotivesWith levels
    flatParamsMajor flatTemplate.typeFn.lift flatDummyType
  let motivesMajor := flatMotives.map fun expression =>
    (view.nested.restoreRecAt projectionLevels expression).instRevAt params 1
  let flatExact := view.flatView.generatedProjectionMinorType constructor
    fieldSort levels flatParamsMajor flatMotives
  let exactMinor :=
    (((view.nested.restoreRecAt projectionLevels
      ((gen.minorType constructor).instL projectionLevels)).instRevAt
        paramsMajor gen.familyCount).instRev motivesMajor)
  let count := (view.flatView.specializedCtorFields constructor levels
    flatParamsMajor).length + constructor.ctor.view.recursive.length
  dsimp only
  obtain ⟨family, familyMember, ownerEq, resultIndicesLength⟩ :=
    gen.flatCtor_owner_shape hconstructor
  have familyNotSelected : family.view.ordinal ≠
      view.selection.family.view.ordinal := by
    intro selected
    exact hnotSelected (ownerEq.symm.trans selected)
  let flatMotive := view.flatView.identityMotiveWith family levels
    flatParamsMajor flatDummyType
  have flatMotivesLength : flatMotives.length = gen.familyCount := by
    simp [flatMotives, VRestoredBlockStructureView.flatView, gen]
  have motiveAt : flatMotives[family.view.ordinal]? = some flatMotive := by
    simpa [flatMotives, flatMotive, familyNotSelected,
      VRestoredBlockStructureView.flatView] using
        view.flatView.projectionMotivesWith_getElem?_ordinal family
          familyMember levels flatParamsMajor flatTemplate.typeFn.lift
            flatDummyType
  let flatArguments := view.flatView.generatedProjectionMinorArguments
    constructor fieldSort levels flatParamsMajor flatMotives
  obtain ⟨flatArgumentsLength, flatResultShape⟩ :=
    view.flatView.generatedProjectionMinorResult_motive constructor family
      ownerEq resultIndicesLength fieldSort levels flatParamsMajor flatMotives
        flatMotive flatMotivesLength motiveAt
  have flatBindersLength : (VExpr.telN count flatExact).length = count := by
    simpa [count, flatExact, VRestoredBlockStructureView.flatView, gen] using
      view.flatView.generatedProjectionMinorBinders_length constructor
        fieldSort levels flatParamsMajor flatMotives flatMotivesLength
  let restore := view.nested.restoreRecAt projectionLevels
  let restoredMotive := restore flatMotive
  let restoredArguments := flatArguments.map restore
  let arguments := restoredArguments.map fun expression =>
    expression.instRevAt params (1 + count)
  have restoreDrop : restore (VExpr.dropN count flatExact) =
      VExpr.dropN count (restore flatExact) := by
    unfold restore NestedBlockChecked.restoreRecAt
    exact VInductDecl.restoreExpr_dropN _ _ count flatExact
      flatBindersLength
  have restoreMotiveLift : restore (flatMotive.liftN count) =
      restoredMotive.liftN count := by
    unfold restore restoredMotive NestedBlockChecked.restoreRecAt
    exact (VInductDecl.restoreExpr_liftN _ (closed.instL projectionLevels)
      _ flatMotive count 0).symm
  have restoredMotiveHead : ∀ name nameLevels,
      (restoredMotive.liftN count).appHead ≠ .const name nameLevels := by
    unfold restoredMotive restore flatMotive
    unfold VBlockStructureView.identityMotiveWith
    unfold NestedBlockChecked.restoreRecAt
    rw [VInductDecl.restoreExpr_lamN]
    generalize (view.flatView.specializedIndices family levels
      flatParamsMajor).map
        (VInductDecl.restoreExpr
          (view.nested.recEntries.map (·.instL projectionLevels))
          view.nested.recMap) = restoredIndices
    cases restoredIndices <;>
      simp [VExpr.lamN, VInductDecl.restoreExpr, VExpr.liftN,
        VExpr.appHead]
  have restoreApp : restore
      (VExpr.appN (flatMotive.liftN count) flatArguments) =
      VExpr.appN (restoredMotive.liftN count) restoredArguments := by
    unfold restore restoredArguments
    exact VInductDecl.restoreExpr_appN_of_nonConst_head restoreMotiveLift
      restoredMotiveHead
  have restoredResult := congrArg restore flatResultShape
  rw [restoreDrop, restoreApp] at restoredResult
  have restoredBindersLength :
      (VExpr.telN count (restore flatExact)).length = count := by
    unfold restore NestedBlockChecked.restoreRecAt
    rw [← VInductDecl.restoreExpr_telN _ _ count flatExact
      flatBindersLength]
    simp [flatBindersLength]
  have specializedResult := congrArg
    (fun expression : VExpr => expression.instRevAt params (1 + count))
    restoredResult
  have dropSpecialize := VExpr.dropN_instRevAt count
    (restore flatExact) params 1 restoredBindersLength
  rw [← dropSpecialize] at specializedResult
  have exactBridge := self.restoredProjectionMinorType_eq henv closed
    constructor hconstructor fieldSort levels params hparamsLength
      flatTemplate flatTypeFnLam
  dsimp only at exactBridge
  change (restore flatExact).instRevAt params 1 = exactMinor at exactBridge
  rw [exactBridge, VExpr.instRevAt_appN_projection] at specializedResult
  rw [show 1 + count = 1 + 0 + count by omega,
    VExpr.liftN_instRevAt_shift] at specializedResult
  change VExpr.dropN count exactMinor =
    VExpr.appN
      ((restoredMotive.instRevAt params 1).liftN count) arguments
    at specializedResult
  refine ⟨family, familyMember, ownerEq, arguments, ?_, ?_⟩
  · simpa [arguments, restoredArguments] using flatArgumentsLength
  · simpa [restoredMotive, restore, flatMotive] using specializedResult

/-- Once regularity exposes the exact restored domain for a nonselected
constructor, the restored canonical identity minor inhabits it.  The terminal
motive application itself supplies the motive-head typing by inversion, so
no parallel auxiliary-family typing traversal is required. -/
theorem ConstructorParameterLayoutWF.restoredIdentityMinorWith_hasType_of_isType
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.ConstructorParameterLayoutWF env) (henv : env.ConversionRegular)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    {U : Nat} {context : List VExpr}
    (constructor : NormalizedBlockCtor)
    (hconstructor : constructor ∈ view.nested.generation.flatCtors)
    (hnotSelected : constructor.owner ≠
      view.selection.family.view.ordinal)
    (fieldSort : VLevel) (levels : List VLevel)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (hmajorContext : OnCtx
      (view.structureType levels params :: context) (env.IsType U))
    (flatTemplate : VStructureView.ProjectionCode)
    (flatTypeFnLam : ∃ domain body,
      flatTemplate.typeFn = .lam domain body)
    (hmotiveLevel : view.nested.generation.motiveLevel.inst
      (view.flatView.projectionLevels fieldSort levels) = fieldSort)
    (dummyType dummyValue : VExpr)
    (dummyTypeEq :
      let projectionLevels := view.flatView.projectionLevels fieldSort levels
      let flatDummyType := VBlockStructureView.majorDummyType
        flatTemplate.typeFn.lift (.bvar 0)
      (view.nested.restoreRecAt projectionLevels flatDummyType).instRevAt
        params 1 = dummyType)
    (dummyValueEq :
      let projectionLevels := view.flatView.projectionLevels fieldSort levels
      let flatDummyValue := VBlockStructureView.majorDummyValue
        flatTemplate.typeFn.lift (.bvar 0)
      (view.nested.restoreRecAt projectionLevels flatDummyValue).instRevAt
        params 1 = dummyValue)
    (dummyValueType : env.HasType U
      (view.structureType levels params :: context) dummyValue dummyType)
    (minorIsType :
      let gen := view.nested.generation
      let projectionLevels := view.flatView.projectionLevels fieldSort levels
      let formalParams := VExpr.bvarRevRange 0 view.nparams
      let flatParamsMajor := formalParams.map (VExpr.liftN 1)
      let paramsMajor := params.map (VExpr.liftN 1)
      let flatDummyType := VBlockStructureView.majorDummyType
        flatTemplate.typeFn.lift (.bvar 0)
      let flatMotives := view.flatView.projectionMotivesWith levels
        flatParamsMajor flatTemplate.typeFn.lift flatDummyType
      let motivesMajor := flatMotives.map fun expression =>
        (view.nested.restoreRecAt projectionLevels expression).instRevAt
          params 1
      env.IsType U (view.structureType levels params :: context)
        (((view.nested.restoreRecAt projectionLevels
          ((gen.minorType constructor).instL projectionLevels)).instRevAt
            paramsMajor gen.familyCount).instRev motivesMajor)) :
    let gen := view.nested.generation
    let projectionLevels := view.flatView.projectionLevels fieldSort levels
    let formalParams := VExpr.bvarRevRange 0 view.nparams
    let flatParamsMajor := formalParams.map (VExpr.liftN 1)
    let paramsMajor := params.map (VExpr.liftN 1)
    let flatDummyType := VBlockStructureView.majorDummyType
      flatTemplate.typeFn.lift (.bvar 0)
    let flatDummyValue := VBlockStructureView.majorDummyValue
      flatTemplate.typeFn.lift (.bvar 0)
    let flatMotives := view.flatView.projectionMotivesWith levels
      flatParamsMajor flatTemplate.typeFn.lift flatDummyType
    let motivesMajor := flatMotives.map fun expression =>
      (view.nested.restoreRecAt projectionLevels expression).instRevAt params 1
    let exactMinor :=
      (((view.nested.restoreRecAt projectionLevels
        ((gen.minorType constructor).instL projectionLevels)).instRevAt
          paramsMajor gen.familyCount).instRev motivesMajor)
    env.HasType U (view.structureType levels params :: context)
      ((view.nested.restoreRecAt projectionLevels
        (view.flatView.identityMinorWith constructor fieldSort levels
          flatParamsMajor flatMotives flatDummyValue)).instRevAt params 1)
      exactMinor := by
  let gen := view.nested.generation
  let projectionLevels := view.flatView.projectionLevels fieldSort levels
  let formalParams := VExpr.bvarRevRange 0 view.nparams
  let flatParamsMajor := formalParams.map (VExpr.liftN 1)
  let paramsMajor := params.map (VExpr.liftN 1)
  let flatDummyType := VBlockStructureView.majorDummyType
    flatTemplate.typeFn.lift (.bvar 0)
  let flatDummyValue := VBlockStructureView.majorDummyValue
    flatTemplate.typeFn.lift (.bvar 0)
  let flatMotives := view.flatView.projectionMotivesWith levels
    flatParamsMajor flatTemplate.typeFn.lift flatDummyType
  let motivesMajor := flatMotives.map fun expression =>
    (view.nested.restoreRecAt projectionLevels expression).instRevAt params 1
  let exactMinor :=
    (((view.nested.restoreRecAt projectionLevels
      ((gen.minorType constructor).instL projectionLevels)).instRevAt
        paramsMajor gen.familyCount).instRev motivesMajor)
  let count := (view.flatView.specializedCtorFields constructor levels
    flatParamsMajor).length + constructor.ctor.view.recursive.length
  let binders := VExpr.telN count exactMinor
  let result := VExpr.dropN count exactMinor
  dsimp only
  have hbindersLength : binders.length = count := by
    simpa [binders, exactMinor, count, gen, projectionLevels, formalParams,
      flatParamsMajor, paramsMajor, flatDummyType, flatMotives,
      motivesMajor] using
      self.restoredProjectionMinorBinders_length henv closed constructor
        hconstructor fieldSort levels params hparamsLength flatTemplate
          flatTypeFnLam
  have hexactShape : exactMinor = VExpr.forallN binders result :=
    (VExpr.forallN_telN_dropN count exactMinor).symm
  obtain ⟨minorLevel, hminorType⟩ := minorIsType
  change env.HasType U (view.structureType levels params :: context)
    exactMinor (.sort minorLevel) at hminorType
  rw [hexactShape] at hminorType
  obtain ⟨hbinders, resultLevel, hresultType⟩ :=
    VEnv.HasType.forallN_wf henv.ordered hminorType
  have hterminalContext : OnCtx
      (binders.reverse ++ view.structureType levels params :: context)
      (env.IsType U) := by
    exact hbinders.toOnCtx hmajorContext
  obtain ⟨family, hfamily, _howner, arguments, hargumentsLength,
      hresultShape⟩ :=
    self.restoredIdentityMinorResult_shape henv closed constructor
      hconstructor hnotSelected fieldSort levels params hparamsLength
        flatTemplate flatTypeFnLam
  have baseClosed := self.restoredMotiveType_closedN henv closed family
    hfamily projectionLevels
  obtain ⟨motiveBinders, majorDomain, hmotiveBindersRawLength,
      hmotiveShape, _domainShape⟩ :=
    view.restoredIdentityMotiveWith_shape_exact closed family fieldSort levels
      hlevelsLength params hparamsLength hmotiveLevel flatDummyType dummyType
        (by simpa [projectionLevels] using baseClosed)
        (by simpa [projectionLevels, flatDummyType] using dummyTypeEq)
  have hmotiveBindersLength :
      motiveBinders.length = family.view.indices.length := by
    have rawLength :=
      (gen.shape.2.2.2.2 family hfamily).2.2.2.1
    rw [view.nested.elim.nparams_eq] at rawLength
    exact hmotiveBindersRawLength.trans rawLength
  let fullMotiveBinders := motiveBinders ++ [majorDomain]
  have hfullMotiveBindersLength :
      fullMotiveBinders.length = arguments.length := by
    rw [hargumentsLength]
    simp [fullMotiveBinders, hmotiveBindersLength]
  have hmotiveSyntax :
      (((view.nested.restoreRecAt projectionLevels
        (view.flatView.identityMotiveWith family levels flatParamsMajor
          flatDummyType)).instRevAt params 1).liftN count) =
        VExpr.lamN (VExpr.liftTelN count fullMotiveBinders 0)
          ((dummyType.liftN count).liftN fullMotiveBinders.length) := by
    rw [hmotiveShape]
    change (VExpr.lamN motiveBinders
      (VExpr.lamN [majorDomain]
        (dummyType.liftN (motiveBinders.length + 1)))).liftN count = _
    rw [← VExpr.lamN_append motiveBinders [majorDomain]
      (dummyType.liftN (motiveBinders.length + 1))]
    rw [VExpr.liftN_lamN_projection]
    have hfullLength : fullMotiveBinders.length =
        motiveBinders.length + 1 := by
      simp [fullMotiveBinders]
    rw [hfullLength]
    congr 1
    simpa only [Nat.zero_add] using
      (calc
        (dummyType.liftN (motiveBinders.length + 1)).liftN count
            (motiveBinders.length + 1) =
          dummyType.liftN (motiveBinders.length + 1 + count) := by
            exact VExpr.liftN'_liftN'
              (e := dummyType) (n1 := motiveBinders.length + 1)
              (n2 := count) (k1 := 0) (k2 := motiveBinders.length + 1)
              (Nat.zero_le _) (Nat.le_refl _)
        _ = dummyType.liftN (count + (motiveBinders.length + 1)) := by
          rw [Nat.add_comm]
        _ = (dummyType.liftN count).liftN
            (motiveBinders.length + 1) := by
          exact (VExpr.liftN_liftN dummyType count
            (motiveBinders.length + 1)).symm)
  have hresultType' : env.HasType U
      (binders.reverse ++ view.structureType levels params :: context)
      (VExpr.appN
        (((view.nested.restoreRecAt projectionLevels
          (view.flatView.identityMotiveWith family levels flatParamsMajor
            flatDummyType)).instRevAt params 1).liftN count)
        arguments) resultLevel := by
    rw [← hresultShape]
    simpa [result, count, exactMinor, hbindersLength] using hresultType
  rw [hmotiveSyntax] at hresultType'
  obtain ⟨_motiveType, hmotiveAny⟩ :=
    VEnv.HasType.appN_head_hasType_restored henv.ordered hterminalContext
      hresultType'
  obtain ⟨hmotiveBinders, motiveResultType, hmotiveBody⟩ :=
    VEnv.HasType.lamN_wf henv.ordered hterminalContext hmotiveAny
  have hmotiveExact : env.HasType U
      (binders.reverse ++ view.structureType levels params :: context)
      (VExpr.lamN (VExpr.liftTelN count fullMotiveBinders 0)
        ((dummyType.liftN count).liftN fullMotiveBinders.length))
      (VExpr.forallN (VExpr.liftTelN count fullMotiveBinders 0)
        motiveResultType) :=
    VEnv.HasType.lamN hmotiveBinders hmotiveBody
  have hargumentsExact : arguments.length =
      (VExpr.liftTelN count fullMotiveBinders 0).length := by
    rw [VExpr.liftTelN_length, hfullMotiveBindersLength]
  have hmotiveSpine := VEnv.HasType.spineWF_of_appN henv
    hterminalContext hmotiveExact hresultType' hargumentsExact
  have hcollapse := VEnv.IsDefEq.appN_lamN henv.ordered hmotiveBinders
    hmotiveBody hmotiveSpine hargumentsExact
  have hfullLengthArguments :
      fullMotiveBinders.length = arguments.length :=
    hfullMotiveBindersLength
  rw [hfullLengthArguments, VExpr.instRev_liftN_len] at hcollapse
  have hcollapseU : env.IsDefEqU U
      (binders.reverse ++ view.structureType levels params :: context)
      (VExpr.appN
        (((view.nested.restoreRecAt projectionLevels
          (view.flatView.identityMotiveWith family levels flatParamsMajor
            flatDummyType)).instRevAt params 1).liftN count)
        arguments)
      (dummyType.liftN count) := by
    refine ⟨motiveResultType.instRev arguments, ?_⟩
    rw [hmotiveSyntax, hfullLengthArguments]
    exact hcollapse
  have hdummyValue : env.HasType U
      (binders.reverse ++ view.structureType levels params :: context)
      (dummyValue.liftN count) (dummyType.liftN count) := by
    have weakened := dummyValueType.weakN henv.ordered
      (Ctx.LiftN.zero (n := count)
        (Γ := view.structureType levels params :: context) binders.reverse
        (h := by simp [hbindersLength]))
    simpa using weakened
  have hdummyResult : env.HasType U
      (binders.reverse ++ view.structureType levels params :: context)
      (dummyValue.liftN count) result := by
    change env.HasType U
      (binders.reverse ++ view.structureType levels params :: context)
      (dummyValue.liftN count) (VExpr.dropN count exactMinor)
    rw [hresultShape]
    have hregular : env.ConversionRegular := henv
    exact hregular.hasType_defeqU_r hterminalContext
      hcollapseU.symm hdummyValue
  have hout := VEnv.HasType.lamN hbinders hdummyResult
  rw [← hexactShape] at hout
  have hminorShape := self.restoredIdentityMinorWith_shape henv closed
    constructor hconstructor fieldSort levels params hparamsLength
      flatTemplate flatTypeFnLam dummyValue dummyValueEq
  dsimp only at hminorShape
  rw [hminorShape]
  exact hout

/-- The registered restored recursor can be applied through the source
parameters and the complete operational motive inventory.  The residual tail
is retained syntactically so the subsequent minor phase can continue from the
same checked recursor transaction. -/
theorem ConstructorParameterLayoutWF.restoredProjectionMotivesRecursor_hasType
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.ConstructorParameterLayoutWF env) (henv : env.ConversionRegular)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    {U : Nat} {context : List VExpr}
    (fieldSort : VLevel) (hfieldSort : fieldSort.WF U)
    (levels : List VLevel) (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (hmajorContext : OnCtx
      (view.structureType levels params :: context) (env.IsType U))
    (paramsMajorSpine : ∃ resultLevel,
      env.SpineWF U (view.structureType levels params :: context)
        (view.familyType.instL levels) (params.map (VExpr.liftN 1))
          (.sort resultLevel))
    (flatTemplate : VStructureView.ProjectionCode)
    (selectedMotiveEq :
      (view.nested.restoreRecAt
        (view.flatView.projectionLevels fieldSort levels)
        flatTemplate.typeFn.lift).instRevAt params 1 = typeFn.lift)
    (dummyEq :
      let flatDummyType := VBlockStructureView.majorDummyType
        flatTemplate.typeFn.lift (.bvar 0)
      (view.nested.restoreRecAt
        (view.flatView.projectionLevels fieldSort levels)
        flatDummyType).instRevAt params 1 = dummyType)
    (hmotiveLevel : view.nested.generation.motiveLevel.inst
      (view.flatView.projectionLevels fieldSort levels) = fieldSort)
    (typeFnType : env.HasType U context typeFn
      (.forallE (view.structureType levels params) (.sort fieldSort)))
    (dummyTypeType : env.HasType U
      (view.structureType levels params :: context) dummyType
      (.sort fieldSort)) :
    let projectionLevels := view.flatView.projectionLevels fieldSort levels
    let paramsMajor := params.map (VExpr.liftN 1)
    let formalParams := VExpr.bvarRevRange 0 view.nparams
    let flatParamsMajor := formalParams.map (VExpr.liftN 1)
    let flatDummyType := VBlockStructureView.majorDummyType
      flatTemplate.typeFn.lift (.bvar 0)
    let flatMotives := view.flatView.projectionMotivesWith levels
      flatParamsMajor flatTemplate.typeFn.lift flatDummyType
    let motivesMajor := flatMotives.map fun expression =>
      (view.nested.restoreRecAt projectionLevels expression).instRevAt params 1
    ∃ tail : VExpr, env.HasType U
      (view.structureType levels params :: context)
      (VExpr.appN (.const view.recursorName projectionLevels)
        (paramsMajor ++ motivesMajor))
      (tail.instRev motivesMajor) := by
  let gen := view.nested.generation
  let projectionLevels := view.flatView.projectionLevels fieldSort levels
  let paramsMajor := params.map (VExpr.liftN 1)
  let formalParams := VExpr.bvarRevRange 0 view.nparams
  let flatParamsMajor := formalParams.map (VExpr.liftN 1)
  let flatDummyType := VBlockStructureView.majorDummyType
    flatTemplate.typeFn.lift (.bvar 0)
  let flatMotives := view.flatView.projectionMotivesWith levels
    flatParamsMajor flatTemplate.typeFn.lift flatDummyType
  let motivesMajor := flatMotives.map fun expression =>
    (view.nested.restoreRecAt projectionLevels expression).instRevAt params 1
  have paramsMajorLength : paramsMajor.length = view.nparams := by
    simpa [paramsMajor] using hparamsLength
  obtain ⟨tail, paramsCursor⟩ :=
    self.restoredRecursorOperationalMotiveSpine henv closed fieldSort
      hfieldSort levels hlevels hlevelsLength paramsMajor paramsMajorLength
        paramsMajorSpine
  have projectionLevelsWF : ∀ level ∈ projectionLevels, level.WF U := by
    change ∀ level ∈
      (match gen.elimination with
      | .large => fieldSort :: levels
      | .small => levels), level.WF U
    cases gen.elimination with
    | large =>
      intro level member
      have member' : level = fieldSort ∨ level ∈ levels := by
        simpa using member
      exact member'.elim (fun equal => equal ▸ hfieldSort) (hlevels level)
    | small =>
      intro level member
      exact hlevels level (by simpa using member)
  have projectionLevelsLength : projectionLevels.length = gen.recUvars := by
    simpa [gen, projectionLevels, VRestoredBlockStructureView.flatView] using
      view.flatView.projectionLevels_length fieldSort levels
        (by simpa only [view.flatView_uvars] using hlevelsLength)
  have recursorTyped : env.HasType U
      (view.structureType levels params :: context)
      (.const view.recursorName projectionLevels)
      ((view.nested.restoreRec
        (gen.recType view.selection.family)).instL projectionLevels) := by
    exact self.restoredRawRecursor_hasType henv.ordered projectionLevelsWF
      projectionLevelsLength
  have afterParams := paramsCursor.hasType_appN recursorTyped
  have afterMotives := self.restoredProjectionMotives_hasType henv closed
    fieldSort levels hlevelsLength params hparamsLength hmajorContext
      flatTemplate selectedMotiveEq dummyEq hmotiveLevel typeFnType
        dummyTypeType _ tail afterParams
  refine ⟨tail, ?_⟩
  simpa [paramsMajor, motivesMajor, VExpr.appN_append] using afterMotives

/-- Every restored source field is closed at its exact
parameter-and-field position. -/
theorem LayoutWF.field_closed
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.Ordered)
    {index : Nat} {field : VExpr}
    (found : view.fields[index]? = some field) :
    field.ClosedN (view.nparams + index) := by
  have paramsContext : OnCtx view.constructorParams.reverse
      (env.IsType view.uvars) := by
    simpa using VEnv.OnTel.toOnCtx (self.constructorParams_onTel henv)
      (by trivial)
  have closed := VEnv.OnSortTel.closedAt henv self.fieldTelescope
    (VEnv.CtxWF.closed henv paramsContext) found
  simpa [view.constructorParams_length] using closed

/-- Canonical parameter variables leave every restored source field
literally at its declaration-universe instance. -/
theorem LayoutWF.specializedFields_bvarRevRange_eq
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.Ordered)
    (levels : List VLevel) :
    view.specializedFields levels (VExpr.bvarRevRange 0 view.nparams) =
      view.fields.map (VExpr.instL levels) := by
  apply List.ext_getElem?
  intro index
  simp only [specializedFields, List.getElem?_map,
    List.getElem?_zipIdx, Nat.zero_add]
  cases found : view.fields[index]? with
  | none => simp [found]
  | some field =>
      simp only [found, Option.map_some]
      rw [VExpr.instRevAt_bvarRevRange_eq_liftN
        (field.instL levels) 0 view.nparams index]
      · simp
      · have closed := (self.field_closed henv found).instL (ls := levels)
        simpa only [Nat.add_comm] using closed

/-- Specializing the canonical restored source-field template at runtime
parameters recovers the exact runtime source telescope, index by index. -/
theorem LayoutWF.specializedFields_bvarRevRange_instRevAt
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.Ordered)
    (levels : List VLevel) (params : List VExpr) :
    ((view.specializedFields levels
      (VExpr.bvarRevRange 0 view.nparams)).zipIdx.map
        fun (field, index) => field.instRevAt params index) =
      view.specializedFields levels params := by
  rw [self.specializedFields_bvarRevRange_eq henv levels]
  exact VExpr.instRevAt_map_instL_zipIdx view.fields levels params

/-- A restored operational type function has the same source-field body
shape as the ordinary block backend, with restored earlier projectors in its
dependent substitution spine. -/
theorem LayoutWF.operationalProjectionCodes_get?_typeFn_source_shape
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.Ordered)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    (levels : List VLevel) (hlevels : levels.length = view.uvars)
    (params : List VExpr) (hparams : params.length = view.nparams)
    {index : Nat} {code : VStructureView.ProjectionCode}
    (found : (view.operationalProjectionCodes levels params)[index]? =
      some code) :
    ∃ field,
      (view.specializedFields levels params)[index]? = some field ∧
      code.typeFn = .lam (view.structureType levels params)
        ((field.liftN 1 index).instRevAt
          (((view.operationalProjectionCodes levels params).take index).map
            fun prior => .app prior.projector.lift (.bvar 0)) 0) := by
  obtain ⟨formalField, domain, templateBody, formalFieldFound,
      typeFnEq, templateBodyEq⟩ :=
    view.operationalProjectionCodes_get?_restoredTypeFnTemplate closed
      levels hlevels params found
  let field := formalField.instRevAt params index
  have fieldsRuntime :=
    self.specializedFields_bvarRevRange_instRevAt henv levels params
  have fieldAt := congrArg (fun fields : List VExpr => fields[index]?)
    fieldsRuntime
  simp only [List.getElem?_map, List.getElem?_zipIdx, Nat.zero_add,
    formalFieldFound, Option.map_some] at fieldAt
  have fieldFound :
      (view.specializedFields levels params)[index]? = some field :=
    fieldAt.symm

  let templates := view.restoredProjectionCodeTemplates levels
  let templateArgs := (templates.take index).map fun prior =>
    VExpr.app prior.projector.lift (.bvar 0)
  let typeBody := templateBody.instRevAt params 1
  let runtimeDomain := domain.instRevAt params 0
  have typeFnShape : code.typeFn = .lam runtimeDomain typeBody := by
    rw [typeFnEq, VExpr.instRevAt_lam_projection]
  have indexBound : index < templates.length := by
    have runtimeBound := (List.getElem?_eq_some_iff.1 found).1
    simpa [templates, operationalProjectionCodes] using runtimeBound
  have templateArgsLength : templateArgs.length = index := by
    simp [templateArgs, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt indexBound)]
  have bodyOuter :
      typeBody =
        ((formalField.liftN 1 index).instRevAt params
          (index + 1)).instRevAt
            (templateArgs.map fun argument =>
              argument.instRevAt params 1) 0 := by
    change templateBody.instRevAt params 1 = _
    rw [templateBodyEq]
    change
      ((formalField.liftN 1 index).instRevAt templateArgs 0).instRevAt
          params 1 = _
    have moved := instRevAt_instRevAt_hi
      (formalField.liftN 1 index) templateArgs params 0 1
    rw [templateArgsLength] at moved
    simpa only [Nat.zero_add, Nat.add_comm] using moved
  have fieldOuter :
      (formalField.liftN 1 index).instRevAt params (index + 1) =
        field.liftN 1 index := by
    simpa [field] using
      liftAt_instRevAt_projection formalField params index
  have argsRuntime :
      templateArgs.map (fun argument => argument.instRevAt params 1) =
        ((view.operationalProjectionCodes levels params).take index).map
          fun prior => VExpr.app prior.projector.lift (.bvar 0) := by
    calc
      _ = (templates.take index).map (fun prior =>
          (VExpr.app prior.projector.lift (.bvar 0)).instRevAt
            params 1) := by
        simp [templateArgs, List.map_map, Function.comp_def]
      _ = (templates.take index).map (fun prior =>
          VExpr.app (prior.instRevAt params 0).projector.lift
            (.bvar 0)) := by
        apply List.map_congr_left
        intro prior _
        have bvarFixed :
            (VExpr.bvar 0).instRevAt params 1 = .bvar 0 :=
          VExpr.instRevAt_closedN params (by trivial)
        rw [VExpr.instRevAt_app_projection,
          VExpr.liftN_instRevAt_same, bvarFixed]
        simp only [VStructureView.ProjectionCode.instRevAt]
        rw [VExpr.instRevAt_zero]
      _ = ((view.operationalProjectionCodes levels params).take index).map
          fun prior => VExpr.app prior.projector.lift (.bvar 0) := by
        simp [templates, operationalProjectionCodes, List.map_take,
          List.map_map, Function.comp_def,
          VStructureView.ProjectionCode.instRevAt]
  have bodyShape : typeBody =
      (field.liftN 1 index).instRevAt
        (((view.operationalProjectionCodes levels params).take index).map
          fun prior => .app prior.projector.lift (.bvar 0)) 0 := by
    rw [bodyOuter, fieldOuter, argsRuntime]
  obtain ⟨domainBody, publicShape⟩ :=
    view.operationalProjectionCodes_get?_typeFn_domain levels params hparams
      found
  have lambdas : (.lam runtimeDomain typeBody : VExpr) =
      .lam (view.structureType levels params) domainBody :=
    typeFnShape.symm.trans publicShape
  have domainEq : runtimeDomain = view.structureType levels params := by
    injection lambdas
  refine ⟨field, fieldFound, ?_⟩
  rw [typeFnShape, domainEq, bodyShape]

/-- Applying a restored operational type function to its major computes the
exact restored source field type.  The syntactic lambda domain is retained
abstractly: projector typing later recovers its definitional equality with
the public source structure type. -/
theorem LayoutWF.operationalProjectionCodes_get?_typeFn_beta
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.Ordered)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    (levels : List VLevel) (hlevels : levels.length = view.uvars)
    (params : List VExpr) {index : Nat}
    {code : VStructureView.ProjectionCode}
    (found : (view.operationalProjectionCodes levels params)[index]? =
      some code) (major : VExpr) :
    ∃ field domain typeBody,
      (view.specializedFields levels params)[index]? = some field ∧
      code.typeFn = .lam domain typeBody ∧
      typeBody.inst major =
        field.instRevAt
          (view.operationalProjectionArgs levels params index major) 0 := by
  obtain ⟨formalField, domain, templateBody, formalFieldFound,
      typeFnEq, templateBodyEq⟩ :=
    view.operationalProjectionCodes_get?_restoredTypeFnTemplate closed
      levels hlevels params found
  let field := formalField.instRevAt params index
  have fieldsRuntime :=
    self.specializedFields_bvarRevRange_instRevAt henv levels params
  have fieldAt := congrArg (fun fields : List VExpr => fields[index]?)
    fieldsRuntime
  simp only [List.getElem?_map, List.getElem?_zipIdx, Nat.zero_add,
    formalFieldFound, Option.map_some] at fieldAt
  have fieldFound :
      (view.specializedFields levels params)[index]? = some field :=
    fieldAt.symm

  let templates := view.restoredProjectionCodeTemplates levels
  let templateArgs := (templates.take index).map fun prior =>
    VExpr.app prior.projector.lift (.bvar 0)
  let typeBody := templateBody.instRevAt params 1
  let runtimeDomain := domain.instRevAt params 0
  have typeFnShape : code.typeFn = .lam runtimeDomain typeBody := by
    rw [typeFnEq, VExpr.instRevAt_lam_projection]

  have indexBound : index < templates.length := by
    have runtimeBound := (List.getElem?_eq_some_iff.1 found).1
    simpa [templates, operationalProjectionCodes] using runtimeBound
  have templateArgsLength : templateArgs.length = index := by
    simp [templateArgs, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt indexBound)]
  have bodyOuter :
      templateBody.instRevAt params 1 =
        ((formalField.liftN 1 index).instRevAt params (index + 1)).instRevAt
            (templateArgs.map fun argument =>
              argument.instRevAt params 1) 0 := by
    rw [templateBodyEq]
    change
      ((formalField.liftN 1 index).instRevAt templateArgs 0).instRevAt
          params 1 = _
    have moved := instRevAt_instRevAt_hi
      (formalField.liftN 1 index) templateArgs params 0 1
    rw [templateArgsLength] at moved
    simpa only [Nat.zero_add, Nat.add_comm] using moved
  have fieldOuter :
      (formalField.liftN 1 index).instRevAt params (index + 1) =
        field.liftN 1 index := by
    simpa [field] using
      liftAt_instRevAt_projection formalField params index

  have argsRuntime :
      (templateArgs.map fun argument => argument.instRevAt params 1).map
          (fun argument => argument.inst major 0) =
        view.operationalProjectionArgs levels params index major := by
    unfold operationalProjectionArgs
    change _ = ((view.operationalProjectionCodes levels params).take index).map
      fun prior => VExpr.app prior.projector major
    calc
      _ = (templates.take index).map (fun prior =>
          ((VExpr.app prior.projector.lift (.bvar 0)).instRevAt
            params 1).inst major 0) := by
        simp [templateArgs, List.map_map, Function.comp_def]
      _ = (templates.take index).map (fun prior =>
          VExpr.app (prior.instRevAt params 0).projector major) := by
        apply List.map_congr_left
        intro prior _
        have bvarFixed :
            (VExpr.bvar 0).instRevAt params 1 = .bvar 0 :=
          VExpr.instRevAt_closedN params (by trivial)
        rw [VExpr.instRevAt_app_projection,
          VExpr.liftN_instRevAt_same, bvarFixed]
        simp only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero,
          VStructureView.ProjectionCode.instRevAt]
        rw [VExpr.instRevAt_zero]
      _ = ((view.operationalProjectionCodes levels params).take index).map
          fun prior => VExpr.app prior.projector major := by
        simp [templates, operationalProjectionCodes, List.map_take,
          List.map_map, Function.comp_def]

  have typeBodyBeta : typeBody.inst major =
      field.instRevAt
        (view.operationalProjectionArgs levels params index major) 0 := by
    change (templateBody.instRevAt params 1).inst major 0 = _
    rw [bodyOuter, fieldOuter]
    rw [VExpr.instN_instRevAt]
    rw [List.length_map, templateArgsLength]
    simp only [Nat.zero_add, VExpr.inst_liftN1]
    rw [argsRuntime]

  exact ⟨field, runtimeDomain, typeBody, fieldFound, typeFnShape,
    typeBodyBeta⟩

/-- One typed restored operational projector computes the exact dependent
source field type.  The projector contract supplies the public structure
domain; type uniqueness transports the restored template's syntactic lambda
domain to it. -/
theorem LayoutWF.operationalProjector_hasType_field_of_type
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.ConversionRegular)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    {U : Nat} {Γ : List VExpr} {levels : List VLevel}
    (hlevels : levels.length = view.uvars)
    {params : List VExpr} {index : Nat}
    {code : VStructureView.ProjectionCode}
    (hΓ : OnCtx Γ (env.IsType U))
    (found : (view.operationalProjectionCodes levels params)[index]? =
      some code)
    (hprojector : env.HasType U Γ code.projector
      (.forallE (view.structureType levels params)
        (.app code.typeFn.lift (.bvar 0))))
    {major : VExpr}
    (hmajor : env.HasType U Γ major
      (view.structureType levels params)) :
    ∃ field domain typeBody,
      (view.specializedFields levels params)[index]? = some field ∧
      code.typeFn = .lam domain typeBody ∧
      env.HasType U Γ (.app code.projector major)
        (field.instRevAt
          (view.operationalProjectionArgs levels params index major) 0) := by
  obtain ⟨field, domain, typeBody, fieldFound, typeFnEq, typeBodyEq⟩ :=
    self.operationalProjectionCodes_get?_typeFn_beta henv.ordered closed
      levels hlevels params found major
  have application : env.HasType U Γ (.app code.projector major)
      (.app code.typeFn major) := by
    simpa only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero] using
      hprojector.app hmajor
  rw [typeFnEq] at application
  obtain ⟨_, redexType⟩ := application.isType henv hΓ
  obtain ⟨_, _, lambdaType, argumentType⟩ :=
    redexType.app_inv henv hΓ
  obtain ⟨⟨_, domainType⟩, _, bodyType⟩ :=
    lambdaType.lam_inv henv hΓ
  have functionTypeEq := henv.hasType_uniqU hΓ lambdaType
    (domainType.lam bodyType)
  obtain ⟨⟨_, domainEq⟩, _⟩ :=
    henv.forallE_inv hΓ functionTypeEq
  have argumentType' := henv.hasType_defeqU_r hΓ ⟨_, domainEq⟩
    argumentType
  have beta : env.IsDefEqU U Γ
      (.app (.lam domain typeBody) major) (typeBody.inst major) :=
    ⟨_, VEnv.IsDefEq.beta bodyType argumentType'⟩
  have output := henv.hasType_defeqU_r hΓ beta application
  rw [typeBodyEq] at output
  exact ⟨field, domain, typeBody, fieldFound, typeFnEq, output⟩

/-- A typed prefix of restored operational projectors forms the matching
dependent source-field spine.  This is the restored analogue of the block
backend's operational-prefix lemma: the program inventory is restored, and
field typing is recovered through the exact restored layout. -/
private theorem operationalProjectionArgsSpineAux_of_prefix
    {view : VRestoredBlockStructureView} {env : VEnv}
    (layout : view.LayoutWF env)
    (henv : env.ConversionRegular)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    {U : Nat} {Γ : List VExpr} {levels : List VLevel}
    {params : List VExpr} {major : VExpr} {limit : Nat}
    (hΓ : OnCtx Γ (env.IsType U))
    (hlevelsLength : levels.length = view.uvars)
    (hmajor : env.HasType U Γ major
      (view.structureType levels params))
    (programs : ∀ {idx : Nat}
      {code : VStructureView.ProjectionCode}, idx < limit →
      (view.operationalProjectionCodes levels params)[idx]? = some code →
      env.HasType U Γ code.projector
        (.forallE (view.structureType levels params)
          (.app code.typeFn.lift (.bvar 0))))
    (tailResult : VExpr) :
    ∀ {count : Nat}, count ≤ limit →
      count ≤ (view.specializedFields levels params).length →
      ∃ cursor,
        VExpr.consumeForalls?
            (VExpr.forallN (view.specializedFields levels params) tailResult)
            (view.operationalProjectionArgs levels params count major) =
              some cursor ∧
          env.SpineWF U Γ
            (VExpr.forallN (view.specializedFields levels params) tailResult)
            (view.operationalProjectionArgs levels params count major)
            cursor := by
  intro count hlimit hcount
  induction count with
  | zero => exact ⟨_, rfl, .nil⟩
  | succ count ih =>
      have hcountLt : count <
          (view.specializedFields levels params).length := by omega
      have hcodeIdx : count <
          (view.operationalProjectionCodes levels params).length := by
        simpa using hcountLt
      let code := (view.operationalProjectionCodes levels params)[count]
      have hcode :
          (view.operationalProjectionCodes levels params)[count]? =
            some code := List.getElem?_eq_getElem hcodeIdx
      have hargsLength :
          (view.operationalProjectionArgs levels params count major).length =
            count :=
        view.operationalProjectionArgs_length levels params count major
          (Nat.le_of_lt hcodeIdx)
      obtain ⟨cursor, hconsume, hspine⟩ :=
        ih (Nat.le_of_lt (Nat.lt_of_succ_le hlimit))
          (Nat.le_of_lt hcountLt)
      obtain ⟨field, semanticBody, hfield, hconsumeDomain⟩ :=
        VExpr.consumeForalls?_forallN_domain
          (view.specializedFields levels params) tailResult
          (view.operationalProjectionArgs levels params count major)
          (by simpa [hargsLength] using hcountLt)
      have hcursorShape : cursor =
          .forallE
            (field.instRevAt
              (view.operationalProjectionArgs levels params count major) 0)
            semanticBody :=
        Option.some.inj (hconsume.symm.trans hconsumeDomain)
      subst cursor
      have hprojector := programs (Nat.lt_of_succ_le hlimit) hcode
      obtain ⟨field', _, _, hfield', _, hprojectorField⟩ :=
        layout.operationalProjector_hasType_field_of_type henv closed
          hlevelsLength hΓ hcode hprojector hmajor
      have hfieldEq : field' = field :=
        Option.some.inj
          (hfield'.symm.trans (by simpa [hargsLength] using hfield))
      subst field'
      refine ⟨semanticBody.inst (.app code.projector major), ?_, ?_⟩
      · rw [view.operationalProjectionArgs_succ levels params count major
          hcode]
        rw [VExpr.consumeForalls?_append, hconsumeDomain]
        rfl
      · rw [view.operationalProjectionArgs_succ levels params count major
          hcode]
        exact hspine.snoc hprojectorField

/-- All restored operational projections of a typed major form the complete
dependent source-field spine expected by the restored constructor. -/
theorem OperationalProgramsWF.operationalProjectionArgsSpine
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.OperationalProgramsWF env)
    (layout : view.LayoutWF env)
    (henv : env.ConversionRegular)
    (closed : RestoreEntriesClosed view.nested.recEntries)
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
      (view.operationalProjectionArgs levels params
        (view.specializedFields levels params).length major)
      (VExpr.instRev tailResult
        (view.operationalProjectionArgs levels params
          (view.specializedFields levels params).length major)) := by
  have programs : ∀ {idx : Nat}
      {code : VStructureView.ProjectionCode},
      idx < (view.specializedFields levels params).length →
      (view.operationalProjectionCodes levels params)[idx]? = some code →
      env.HasType U Γ code.projector
        (.forallE (view.structureType levels params)
          (.app code.typeFn.lift (.bvar 0))) := by
    intro idx code _hidx hcode
    exact self hΓ hlevels hlevelsLength hparamsLength hparamsSpine hcode
  obtain ⟨_, _, hspine⟩ := operationalProjectionArgsSpineAux_of_prefix
    layout henv closed hΓ hlevelsLength hmajor programs tailResult
      (Nat.le_refl _) (Nat.le_refl _)
  apply hspine.retarget
  exact view.operationalProjectionArgs_length levels params
    (view.specializedFields levels params).length major (by simp)

/-- Applying the complete restored projection spine to the typed public
constructor prefix rebuilds a value of the restored source family. -/
theorem OperationalProgramsWF.operationalEtaRebuild_hasType_of_constructorPrefix
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.OperationalProgramsWF env)
    (layout : view.LayoutWF env)
    (henv : env.ConversionRegular)
    (closed : RestoreEntriesClosed view.nested.recEntries)
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
    (hconstructorPrefix : env.HasType U Γ
      (VExpr.appN (.const view.constructorName levels) params)
      (VExpr.forallN (view.specializedFields levels params)
        ((view.structureType levels params).liftN
          (view.specializedFields levels params).length))) :
    env.HasType U Γ (view.operationalEtaRebuild levels params major)
      (view.structureType levels params) := by
  have hfields := self.operationalProjectionArgsSpine layout henv closed hΓ
    hlevels hlevelsLength hparamsLength hparamsSpine hmajor
    ((view.structureType levels params).liftN
      (view.specializedFields levels params).length)
  have hrebuild := hfields.hasType_appN hconstructorPrefix
  let args := view.operationalProjectionArgs levels params
    (view.specializedFields levels params).length major
  have hargsLength :
      args.length = (view.specializedFields levels params).length :=
    view.operationalProjectionArgs_length levels params
      (view.specializedFields levels params).length major (by simp)
  have hlift :
      (view.structureType levels params).liftN
          (view.specializedFields levels params).length =
        (view.structureType levels params).liftN args.length :=
    congrArg (view.structureType levels params).liftN hargsLength.symm
  have hresult :
      VExpr.instRev
        ((view.structureType levels params).liftN
          (view.specializedFields levels params).length) args =
        view.structureType levels params := by
    calc
      _ = VExpr.instRev
          ((view.structureType levels params).liftN args.length) args :=
        congrArg (VExpr.instRev · args) hlift
      _ = view.structureType levels params :=
        VExpr.instRev_liftN_len args _
  rw [hresult] at hrebuild
  simpa [operationalEtaRebuild, VExpr.appN_append] using hrebuild

/-- Rule-independent reconstruction typing for the restored projection
backend. -/
def OperationalRebuildWF (view : VRestoredBlockStructureView)
    (env : VEnv) : Prop :=
  ∀ {U : Nat} {Γ : List VExpr} {levels : List VLevel}
      {params : List VExpr} {major : VExpr},
    OnCtx Γ (env.IsType U) →
    (∀ level ∈ levels, level.WF U) →
    levels.length = view.uvars →
    params.length = view.nparams →
    (∃ resultLevel, env.SpineWF U Γ (view.familyType.instL levels)
      params (.sort resultLevel)) →
    env.HasType U Γ major (view.structureType levels params) →
    env.HasType U Γ (view.operationalEtaRebuild levels params major)
      (view.structureType levels params)

/-- The exact lower-layer structure-eta descriptor generated by a restored
nested family.  Its projector list contains the operational restored
programs, never the flattened templates. -/
def ConstructorParameterLayoutWF.toStructEta
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.ConstructorParameterLayoutWF env)
    (codeNaturality : view.flatView.OperationalCodeNaturality)
    (closed : RestoreEntriesClosed view.nested.recEntries) : VStructEta where
  uvars := view.uvars
  nparams := view.nparams
  nfields := view.fields.length
  familyName := view.name
  familyType := view.familyType
  constructorName := view.constructorName
  projectors := fun levels params =>
    (view.operationalProjectionCodes levels params).map (·.projector)
  projectors_length := by
    intro levels params _ _
    simp [specializedFields]
  projectors_liftN := by
    intro levels params n k hparams
    have h := view.operationalProjectionCodes_liftN codeNaturality closed
      levels params hparams n k
    simpa [List.map_map, VStructureView.ProjectionCode.liftN,
      Function.comp_def] using congrArg (List.map (·.projector)) h
  projectors_instN := by
    intro levels params a k hparams
    have h := view.operationalProjectionCodes_instN codeNaturality closed
      levels params hparams a k
    simpa [List.map_map, VStructureView.ProjectionCode.instN,
      Function.comp_def] using congrArg (List.map (·.projector)) h
  projectors_instL := by
    intro levels params ls
    have h := view.operationalProjectionCodes_instL levels params ls
    simpa [List.map_map, VStructureView.ProjectionCode.instL,
      Function.comp_def] using congrArg (List.map (·.projector)) h

/-- Monotone transport changes only proof fields of the restored eta
descriptor, so the registered rule value is stable. -/
theorem ConstructorParameterLayoutWF.toStructEta_mono_eq
    {view : VRestoredBlockStructureView} {env env' : VEnv}
    (self : view.ConstructorParameterLayoutWF env) (hle : env ≤ env')
    (codeNaturality : view.flatView.OperationalCodeNaturality)
    (closed : RestoreEntriesClosed view.nested.recEntries) :
    self.toStructEta codeNaturality closed =
      (self.mono hle).toStructEta codeNaturality closed := by
  rfl

@[simp] theorem ConstructorParameterLayoutWF.toStructEta_structureType
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.ConstructorParameterLayoutWF env)
    (codeNaturality : view.flatView.OperationalCodeNaturality)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    (levels : List VLevel) (params : List VExpr) :
    (self.toStructEta codeNaturality closed).structureType levels params =
      view.structureType levels params := rfl

@[simp] theorem ConstructorParameterLayoutWF.toStructEta_rebuild
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.ConstructorParameterLayoutWF env)
    (codeNaturality : view.flatView.OperationalCodeNaturality)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    (levels : List VLevel) (params : List VExpr) (major : VExpr) :
    (self.toStructEta codeNaturality closed).rebuild levels params major =
      view.operationalEtaRebuild levels params major := by
  simp only [VStructEta.rebuild, VStructEta.projectionArgs,
    ConstructorParameterLayoutWF.toStructEta, operationalEtaRebuild,
    operationalProjectionArgs]
  rw [← view.operationalProjectionCodes_length, List.take_length]
  simp [List.map_map, Function.comp_def]

/-- A persistent family of restored reconstruction proofs packages the
operational descriptor as a registry-valid `VStructEta.WF`. -/
theorem ConstructorParameterLayoutWF.toStructEtaWF_of_rebuilds
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.ConstructorParameterLayoutWF env)
    (codeNaturality : view.flatView.OperationalCodeNaturality)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    (henv : env.Ordered)
    (rebuilds : ∀ {env' : VEnv}, env ≤ env' →
      env'.ConversionRegular → view.OperationalRebuildWF env') :
    (self.toStructEta codeNaturality closed).WF env where
  familyType_closed := self.familyType_closed henv
  rebuild_hasType := by
    intro env' hle hregular U Γ levels params major hΓ hlevels
      hlevelsLength hparamsLength hparamsSpine hmajor
    simpa using rebuilds hle hregular hΓ hlevels hlevelsLength
      hparamsLength hparamsSpine hmajor

/-- Instantiating the restored left body of the selected unindexed rule with
a complete common/field capture produces the literal source recursor redex.
The source recursor and constructor heads are both inert under restoration,
so the ordinary producer computation theorem applies unchanged afterward. -/
theorem restoredRuleLhsBody_instL_instRev_common_fields
    (view : VRestoredBlockStructureView)
    (fieldSort : VLevel) (levels : List VLevel)
    (hlevelsLength : levels.length = view.uvars)
    (hidx : view.nested.generation.ruleIdx
      view.flatView.blockConstructor = [])
    (commonArgs fields : List VExpr)
    (hcommonLength : commonArgs.length =
      view.nested.elim.flat.nparams +
        view.nested.generation.familyCount +
        view.nested.generation.minorCount)
    (hfieldsLength : fields.length =
      view.nested.generation.ruleFieldCount
        view.flatView.blockConstructor) :
    VExpr.instRev
        ((view.nested.restoreRec
          (view.nested.generation.ruleLhsBody
            view.flatView.blockConstructor)).instL
          (view.flatView.projectionLevels fieldSort levels))
        (commonArgs ++ fields) =
      VExpr.appN
        (.const view.recursorName
          (view.flatView.projectionLevels fieldSort levels))
        (commonArgs ++
          [VExpr.appN (.const view.constructorName levels)
            (commonArgs.take view.nparams ++ fields)]) := by
  let gen := view.nested.generation
  let constructor := view.flatView.blockConstructor
  let projectionLevels :=
    view.flatView.projectionLevels fieldSort levels
  have projectionLevelsLength : projectionLevels.length = gen.recUvars := by
    simpa [gen, projectionLevels, VRestoredBlockStructureView.flatView] using
      view.flatView.projectionLevels_length fieldSort levels
        (by simpa only [view.flatView_uvars] using hlevelsLength)
  have ruleRecursorName : gen.ruleRecName constructor =
      view.recursorName := by
    have ordinary : gen.ruleRecName constructor =
        view.flatView.recursorName := by
      rw [BlockGenerationChecked.ruleRecName]
      change (.str
        (gen.familyNameAt view.flatView.family.view.ordinal) "rec" : Name) =
        view.flatView.recursorName
      rw [show gen.familyNameAt view.flatView.family.view.ordinal =
          view.flatView.name by
        simpa only [gen, VRestoredBlockStructureView.flatView] using
          view.flatView.familyNameAt_ordinal]
      rfl
    exact ordinary.trans view.flatView_recursorName
  have constructorName : constructor.ctor.raw.name =
      view.constructorName := by
    exact view.flatView_constructorName
  have recursorInert : RestoreInert view.nested.recEntries
      view.nested.recMap (.const view.recursorName gen.recLevels) := by
    simpa [VRestoredBlockStructureView.recursorName] using
      view.nested.sourceRecursorName_restoreRecInert
        view.sourceFamily_mem gen.recLevels
  have constructorInert : RestoreInert view.nested.recEntries
      view.nested.recMap (.const view.constructorName gen.sourceLevels) := by
    exact view.nested.sourceConstructorName_restoreRecInert
      view.sourceFamily_mem view.sourceConstructor_mem gen.sourceLevels
  have lhsInert : RestoreInert view.nested.recEntries view.nested.recMap
      (gen.ruleLhsBody constructor) := by
    have recBaseInert : RestoreInert view.nested.recEntries
        view.nested.recMap
        (gen.recBase (gen.ruleFieldCount constructor) constructor.owner) := by
      rw [BlockGenerationChecked.recBase,
        show (.str (gen.familyNameAt constructor.owner) "rec" : Name) =
            view.recursorName by
          simpa only [BlockGenerationChecked.ruleRecName] using
            ruleRecursorName]
      apply recursorInert.appN
      intro argument member
      exact bvarRevRange_restoreInert _ _ _ _ argument member
    have constructorAppInert : RestoreInert view.nested.recEntries
        view.nested.recMap (gen.ruleCtorApp constructor) := by
      rw [BlockGenerationChecked.ruleCtorApp, constructorName]
      apply constructorInert.appN
      intro argument member
      rcases List.mem_append.mp member with parameter | field
      · exact bvarRevRange_restoreInert _ _ _ _ argument parameter
      · exact bvarRevRange_restoreInert _ _ _ _ argument field
    rw [BlockGenerationChecked.ruleLhsBody, hidx]
    simp only [List.nil_append]
    apply recBaseInert.appN
    intro argument member
    simp only [List.mem_singleton] at member
    subst argument
    exact constructorAppInert
  have restored : view.nested.restoreRec (gen.ruleLhsBody constructor) =
      gen.ruleLhsBody constructor := lhsInert.restoreExpr_eq
  rw [show view.nested.restoreRec
      (view.nested.generation.ruleLhsBody
        view.flatView.blockConstructor) =
        gen.ruleLhsBody constructor by
    simpa [gen, constructor] using restored]
  have computed :=
    gen.ruleLhsBody_instL_instRev_common_fields_of_unindexed
      constructor projectionLevels projectionLevelsLength
      (by simpa [gen, constructor] using hidx)
      commonArgs fields hcommonLength hfieldsLength
  have sourceLevels := view.flatView.sourceLevels_projectionLevels
    fieldSort levels (by
      simpa only [view.flatView_uvars] using hlevelsLength)
  have sourceLevels' :
      gen.sourceLevels.map (VLevel.inst projectionLevels) = levels := by
    simpa only [gen, projectionLevels,
      VRestoredBlockStructureView.flatView] using sourceLevels
  rw [ruleRecursorName, constructorName, sourceLevels',
    view.nested.elim.nparams_eq] at computed
  simpa [projectionLevels] using computed

/-- Instantiating a restored right rule body selects the captured minor and
applies it to the captured source fields plus the restored recursive-call
payloads.  Restoration may change those payloads, but not their positions or
the selector minor's field prefix. -/
theorem restoredRuleRhsBody_instL_instRev_common_fields
    (view : VRestoredBlockStructureView)
    (ruleIndex : Nat) (constructor : NormalizedBlockCtor)
    (levels : List VLevel) (commonArgs fields : List VExpr)
    (hcommonLength : commonArgs.length =
      view.nested.elim.flat.nparams +
        view.nested.generation.familyCount +
        view.nested.generation.minorCount)
    (hfieldsLength : fields.length =
      view.nested.generation.ruleFieldCount constructor)
    {minor : VExpr}
    (hminor : commonArgs[view.nested.elim.flat.nparams +
      view.nested.generation.familyCount + ruleIndex]? = some minor)
    (hi : ruleIndex < view.nested.generation.minorCount) :
    let gen := view.nested.generation
    let recursiveArgs :=
      constructor.ctor.recArgsR view.nested.elim.flat.uvars gen.elimination
    let ihs := recursiveArgs.map fun recursive =>
      BlockGenerationChecked.blockRuleCall
        (gen.familyCount + gen.minorCount)
        (gen.ruleFieldCount constructor)
        (gen.recBase (gen.ruleFieldCount constructor)
          recursive.targetType) recursive
    let restoredIHs := ihs.map view.nested.restoreRec
    let capturedIHs := restoredIHs.map fun expression =>
      VExpr.instRev (expression.instL levels) (commonArgs ++ fields)
    VExpr.instRev
        ((view.nested.restoreRec
          (gen.ruleRhsBody ruleIndex constructor)).instL levels)
        (commonArgs ++ fields) =
      VExpr.appN minor (fields ++ capturedIHs) := by
  let gen := view.nested.generation
  let captures := commonArgs ++ fields
  let recursiveArgs :=
    constructor.ctor.recArgsR view.nested.elim.flat.uvars gen.elimination
  let ihs := recursiveArgs.map fun recursive =>
    BlockGenerationChecked.blockRuleCall
      (gen.familyCount + gen.minorCount)
      (gen.ruleFieldCount constructor)
      (gen.recBase (gen.ruleFieldCount constructor)
        recursive.targetType) recursive
  let restoredIHs := ihs.map view.nested.restoreRec
  let capturedIHs := restoredIHs.map fun expression =>
    VExpr.instRev (expression.instL levels) captures
  have commonLength : commonArgs.length =
      view.nested.elim.flat.nparams + gen.familyCount + gen.minorCount := by
    simpa only [gen] using hcommonLength
  have fieldsLength : fields.length =
      gen.ruleFieldCount constructor := by
    simpa only [gen] using hfieldsLength
  have minorAt : commonArgs[view.nested.elim.flat.nparams +
      gen.familyCount + ruleIndex]? = some minor := by
    simpa only [gen] using hminor
  have ruleIndexLt : ruleIndex < gen.minorCount := by
    simpa only [gen] using hi
  have capturesLength : captures.length =
      view.nested.elim.flat.nparams + gen.familyCount + gen.minorCount +
        gen.ruleFieldCount constructor := by
    simp only [captures, List.length_append]
    rw [commonLength, fieldsLength]
  have headLt : gen.minorCount - 1 - ruleIndex +
      gen.ruleFieldCount constructor < captures.length := by
    rw [capturesLength]
    omega
  obtain ⟨minorLt, minorGet⟩ := List.getElem?_eq_some_iff.1 minorAt
  have head : VExpr.instRev
      (.bvar (gen.minorCount - 1 - ruleIndex +
        gen.ruleFieldCount constructor)) captures = minor := by
    rw [VExpr.instRev_bvar_lt captures headLt]
    have position : captures.length - 1 -
        (gen.minorCount - 1 - ruleIndex +
          gen.ruleFieldCount constructor) =
        view.nested.elim.flat.nparams + gen.familyCount + ruleIndex := by
      rw [capturesLength]
      omega
    simpa only [position, captures,
      List.getElem_append_left minorLt] using minorGet
  have fieldSegment :
      (VExpr.bvarRevRange 0 (gen.ruleFieldCount constructor)).map
          (VExpr.instRev · captures) = fields := by
    rw [VExpr.map_instRev_bvarRevRange_seg _ _ _ (by omega)]
    rw [show captures.length - 0 - gen.ruleFieldCount constructor =
        commonArgs.length by
          rw [capturesLength, commonLength]
          omega]
    rw [List.drop_left]
    exact List.take_of_length_le (Nat.le_of_eq fieldsLength)
  change VExpr.instRev
      ((view.nested.restoreRec
        (VExpr.appN
          (.bvar (gen.minorCount - 1 - ruleIndex +
            gen.ruleFieldCount constructor))
          (VExpr.bvarRevRange 0 (gen.ruleFieldCount constructor) ++
            ihs))).instL levels) captures =
      VExpr.appN minor (fields ++ capturedIHs)
  unfold NestedBlockChecked.restoreRec
  rw [VInductDecl.restoreExpr_bvar_appN]
  rw [List.map_append, bvarRevRange_restoreExpr_map]
  rw [VExpr.instL_appN, VExpr.instRev_appN]
  simp only [List.map_append, VExpr.bvarRevRange_map_instL,
    VExpr.instL, List.map_map, Function.comp_def]
  rw [head, fieldSegment]
  simp [capturedIHs, restoredIHs, NestedBlockChecked.restoreRec,
    List.map_map, Function.comp_def]

/-- Restored specialized fields commute with ambient lifting once their
formal source-parameter boundary is fixed. -/
theorem LayoutWF.specializedFields_liftN
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.Ordered)
    (levels : List VLevel) (params : List VExpr)
    (paramsLength : params.length = view.nparams)
    (count cutoff : Nat) :
    view.specializedFields levels
        (params.map fun parameter => parameter.liftN count cutoff) =
      VExpr.liftTelN count (view.specializedFields levels params) cutoff := by
  simpa [specializedFields] using
    VStructureView.specializedFieldsAux_liftN view.fields levels params
      view.nparams 0 count cutoff paramsLength
      (fun index field found => by
        simpa using self.field_closed henv found)

/-- Restored specialized fields commute with ambient term instantiation at
the same exact source-parameter boundary. -/
theorem LayoutWF.specializedFields_instN
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.Ordered)
    (levels : List VLevel) (params : List VExpr)
    (paramsLength : params.length = view.nparams)
    (argument : VExpr) (cutoff : Nat) :
    view.specializedFields levels
        (params.map fun parameter => parameter.inst argument cutoff) =
      VExpr.instTelN argument (view.specializedFields levels params)
        cutoff := by
  simpa [specializedFields] using
    VStructureView.specializedFieldsAux_instN view.fields levels params
      view.nparams 0 cutoff argument paramsLength
      (fun index field found => by
        simpa using self.field_closed henv found)

/-- Current restored field alignment is stable when an ambient binder is
inserted beneath the complete source-field telescope. -/
theorem LayoutWF.operationalConstructorFieldAligned_weak
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.Ordered)
    (codeNaturality : view.flatView.OperationalCodeNaturality)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    {U : Nat} {Γ : List VExpr} {levels : List VLevel}
    {params : List VExpr} {limit : Nat}
    (hparamsLength : params.length = view.nparams)
    (aligned : view.OperationalConstructorFieldAligned env U Γ
      levels params limit) (A : VExpr) :
    view.OperationalConstructorFieldAligned env U (A :: Γ) levels
      (params.map (VExpr.liftN 1)) limit := by
  intro liftedField hliftedField
  let fields := view.specializedFields levels params
  let m := fields.length
  let paramsLift := params.map (VExpr.liftN 1)
  have hfieldsLift : view.specializedFields levels paramsLift =
      VExpr.liftTelN 1 fields 0 := by
    simpa [paramsLift, fields] using
      self.specializedFields_liftN henv levels params hparamsLength 1 0
  rw [hfieldsLift, VExpr.liftTelN_getElem?] at hliftedField
  obtain ⟨field, hfield, rfl⟩ := Option.map_eq_some_iff.1 hliftedField
  have hbase := aligned hfield
  have hweak := hbase.weakN henv
    (Ctx.LiftN.consTel fields (Ctx.LiftN.one (A := A)))
  have hcodesLift := view.operationalProjectionCodes_liftN
    codeNaturality closed levels params hparamsLength 1 0
  have hlimit : limit < fields.length := by
    simpa [fields] using (List.getElem?_eq_some_iff.1 hfield).1
  have hconstructorLift :
      view.projectionConstructorApp levels paramsLift
          (VExpr.liftTelN 1 fields 0) =
        (view.projectionConstructorApp levels params fields).liftN 1 m := by
    simp [VRestoredBlockStructureView.projectionConstructorApp, paramsLift,
      m, VExpr.liftN_appN, VExpr.liftN, VExpr.liftTelN_length,
      List.map_append, List.map_map, Function.comp_def,
      VExpr.liftN'_liftN', VExpr.bvarRevRange_liftN_high, Nat.add_comm]
  let args :=
    ((view.operationalProjectionCodes levels params).take limit).map
      fun prior => VExpr.app (prior.projector.liftN m)
        (view.projectionConstructorApp levels params fields)
  change env.IsDefEqU U ((VExpr.liftTelN 1 fields 0).reverse ++ A :: Γ)
    (((field.liftN m limit).instRev args).liftN 1 m)
    ((field.liftN (m - limit)).liftN 1 m) at hweak
  rw [hfieldsLift]
  dsimp only [m] at hweak ⊢
  rw [← hcodesLift]
  simp only [List.map_take, List.map_map,
    VStructureView.ProjectionCode.liftN, Function.comp_def]
  rw [hconstructorLift]
  have hargsLength : args.length = limit := by
    simp only [args, List.length_map, List.length_take,
      view.operationalProjectionCodes_length]
    apply Nat.min_eq_left
    simpa [fields] using Nat.le_of_lt hlimit
  rw [← VExpr.instRevAt_zero] at hweak
  have hliftInst := VExpr.liftN_instRevAt
    (field.liftN fields.length limit) args 0 fields.length 1
  simp only [Nat.add_zero] at hliftInst
  rw [hliftInst] at hweak
  rw [hargsLength] at hweak
  have hfieldCompose :
      (field.liftN fields.length limit).liftN 1
          (fields.length + limit) =
        (field.liftN 1 limit).liftN fields.length limit := by
    rw [VExpr.liftN'_liftN'
      (e := field) (n1 := fields.length) (n2 := 1)
      (k1 := limit) (k2 := fields.length + limit)
      (by omega) (by omega)]
    rw [VExpr.liftN'_liftN_hi]
    simp only [Nat.add_comm]
  have hargsLift :
      args.map (fun argument => argument.liftN 1 fields.length) =
        ((view.operationalProjectionCodes levels params).take limit).map
          fun prior =>
            VExpr.app ((prior.liftN 1 0).projector.liftN fields.length)
              ((view.projectionConstructorApp levels params fields).liftN
                1 fields.length) := by
    simp [args, m, VStructureView.ProjectionCode.liftN, VExpr.liftN,
      List.map_take, List.map_map, Function.comp_def,
      VExpr.liftN'_liftN', Nat.add_comm]
  have hrightCompose :
      (field.liftN (fields.length - limit)).liftN 1 fields.length =
        (field.liftN 1 limit).liftN (fields.length - limit) := by
    have h := VExpr.liftN_liftN_comm field
      (fields.length - limit) 1 0 limit (Nat.zero_le _)
    rw [Nat.add_sub_of_le (Nat.le_of_lt hlimit)] at h
    exact h.symm
  rw [hfieldCompose, hargsLift, hrightCompose,
    VExpr.instRevAt_zero] at hweak
  simpa only [VExpr.liftTelN_length, Nat.zero_add, List.map_take,
    VStructureView.ProjectionCode.liftN, m] using hweak

/-- The field prefix of the exact restored selected minor is the public
source field telescope beneath the retained major binder. -/
theorem ConstructorParameterLayoutWF.restoredSelectedMinorFields
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.ConstructorParameterLayoutWF env) (henv : env.ConversionRegular)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    (fieldSort : VLevel) (levels : List VLevel)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (flatTemplate : VStructureView.ProjectionCode)
    (flatTypeFnLam : ∃ domain body,
      flatTemplate.typeFn = .lam domain body) :
    let gen := view.nested.generation
    let constructor := view.flatView.blockConstructor
    let projectionLevels := view.flatView.projectionLevels fieldSort levels
    let formalParams := VExpr.bvarRevRange 0 view.nparams
    let flatParamsMajor := formalParams.map (VExpr.liftN 1)
    let paramsMajor := params.map (VExpr.liftN 1)
    let flatDummyType := VBlockStructureView.majorDummyType
      flatTemplate.typeFn.lift (.bvar 0)
    let flatMotives := view.flatView.projectionMotivesWith levels
      flatParamsMajor flatTemplate.typeFn.lift flatDummyType
    let motivesMajor := flatMotives.map fun expression =>
      (view.nested.restoreRecAt projectionLevels expression).instRevAt params 1
    let exactMinor :=
      (((view.nested.restoreRecAt projectionLevels
        ((gen.minorType constructor).instL projectionLevels)).instRevAt
          paramsMajor gen.familyCount).instRev motivesMajor)
    let fieldCount := (view.flatView.specializedCtorFields constructor levels
      flatParamsMajor).length
    VExpr.telN fieldCount exactMinor =
      view.specializedFields levels paramsMajor := by
  let gen := view.nested.generation
  let constructor := view.flatView.blockConstructor
  let projectionLevels := view.flatView.projectionLevels fieldSort levels
  let formalParams := VExpr.bvarRevRange 0 view.nparams
  let flatParamsMajor := formalParams.map (VExpr.liftN 1)
  let paramsMajor := params.map (VExpr.liftN 1)
  let flatDummyType := VBlockStructureView.majorDummyType
    flatTemplate.typeFn.lift (.bvar 0)
  let flatMotives := view.flatView.projectionMotivesWith levels
    flatParamsMajor flatTemplate.typeFn.lift flatDummyType
  let motivesMajor := flatMotives.map fun expression =>
    (view.nested.restoreRecAt projectionLevels expression).instRevAt params 1
  let flatExact := view.flatView.generatedProjectionMinorType constructor
    fieldSort levels flatParamsMajor flatMotives
  let exactMinor :=
    (((view.nested.restoreRecAt projectionLevels
      ((gen.minorType constructor).instL projectionLevels)).instRevAt
        paramsMajor gen.familyCount).instRev motivesMajor)
  let flatFields := view.flatView.specializedCtorFields constructor levels
    flatParamsMajor
  let fieldCount := flatFields.length
  let restore := view.nested.restoreRecAt projectionLevels
  dsimp only
  have flatMotivesLength : flatMotives.length = gen.familyCount := by
    simp [flatMotives, gen, VRestoredBlockStructureView.flatView]
  have flatPrefix : VExpr.telN fieldCount flatExact = flatFields := by
    simpa [fieldCount, flatFields, flatExact,
      VRestoredBlockStructureView.flatView, gen] using
        view.flatView.generatedProjectionMinorType_fields constructor
          fieldSort levels (by
            simpa only [view.flatView_uvars] using hlevelsLength)
          flatParamsMajor flatMotives (by
            simpa [gen, VRestoredBlockStructureView.flatView] using
              flatMotivesLength)
  have flatPrefixLength :
      (VExpr.telN fieldCount flatExact).length = fieldCount := by
    rw [flatPrefix]
  have restoredPrefix : VExpr.telN fieldCount (restore flatExact) =
      flatFields.map restore := by
    unfold restore NestedBlockChecked.restoreRecAt
    rw [← VInductDecl.restoreExpr_telN _ _ fieldCount flatExact
      flatPrefixLength, flatPrefix]
  have restoredPrefixLength :
      (VExpr.telN fieldCount (restore flatExact)).length = fieldCount := by
    rw [restoredPrefix]
    simp [fieldCount]
  have specializedPrefix := VExpr.telN_instRevAt fieldCount
    (restore flatExact) params 1 restoredPrefixLength
  rw [restoredPrefix] at specializedPrefix
  have flatFieldsEq : flatFields =
      view.flatView.specializedFields levels flatParamsMajor := by
    rfl
  have flatParamsMajorEq : flatParamsMajor =
      VExpr.bvarRevRange 1 view.nparams := by
    unfold flatParamsMajor formalParams
    rw [VExpr.bvarRevRange_liftN_low]
  have restoredFields : flatFields.map restore =
      view.specializedFields levels flatParamsMajor := by
    rw [flatFieldsEq]
    apply view.restoreFlatSpecializedFields closed fieldSort levels
      hlevelsLength flatParamsMajor
    intro parameter member
    rw [flatParamsMajorEq] at member
    exact bvarRevRange_restoreInert _ _ _ _ parameter member
  rw [restoredFields] at specializedPrefix
  have formalLength : formalParams.length = view.nparams := by
    simp [formalParams]
  have sourceFormalLift := self.toLayoutWF.specializedFields_liftN
    henv.ordered levels formalParams formalLength 1 0
  change view.specializedFields levels flatParamsMajor =
    VExpr.liftTelN 1 (view.specializedFields levels formalParams) 0
    at sourceFormalLift
  have sourceRuntimeLift := self.toLayoutWF.specializedFields_liftN
    henv.ordered levels params hparamsLength 1 0
  change view.specializedFields levels paramsMajor =
    VExpr.liftTelN 1 (view.specializedFields levels params) 0
    at sourceRuntimeLift
  have formalSpecialized :=
    self.toLayoutWF.specializedFields_bvarRevRange_instRevAt henv.ordered
      levels params
  change ((view.specializedFields levels formalParams).zipIdx.map
      fun entry => entry.1.instRevAt params entry.2) =
    view.specializedFields levels params at formalSpecialized
  have specializedFieldsEq :
      ((view.specializedFields levels flatParamsMajor).zipIdx 1).map
          (fun entry => entry.1.instRevAt params entry.2) =
        view.specializedFields levels paramsMajor := by
    rw [sourceFormalLift]
    rw [show (1 : Nat) = 0 + 1 by omega]
    rw [VExpr.liftTelN_instRevAt_projection]
    rw [formalSpecialized, sourceRuntimeLift]
  rw [specializedFieldsEq] at specializedPrefix
  have exactBridge := self.restoredProjectionMinorType_eq henv closed
    constructor view.flatView.blockConstructor_mem fieldSort levels params
      hparamsLength flatTemplate flatTypeFnLam
  dsimp only at exactBridge
  change (restore flatExact).instRevAt params 1 = exactMinor at exactBridge
  rw [exactBridge] at specializedPrefix
  exact specializedPrefix

/-- An explicit spine for the restored constructor's stored parameter
prefix specializes its exact source field telescope.  This lemma isolates
the sole constructor-side input still needed by the operational backend:
the family layer above supplies checked family parameters, but identifying
those parameters with the restored constructor prefix requires restoration
transport rather than metadata registration alone. -/
theorem LayoutWF.specializedFields_onSortTel_of_constructorParamsSpine
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    {target cursor : VExpr}
    (paramsSpine : env.SpineWF U Γ
      (VExpr.forallN
        (view.constructorParams.map (VExpr.instL levels)) target)
      params cursor) :
    env.OnSortTel U Γ (view.specializedFields levels params)
      (view.fieldSorts.map (VLevel.inst levels)) := by
  have hconstructorLength : params.length =
      (view.constructorParams.map (VExpr.instL levels)).length := by
    simpa only [List.length_map] using
      hparamsLength.trans view.constructorParams_length.symm
  have hparams : env.SpineWF U Γ
      (VExpr.forallN
        (view.constructorParams.map (VExpr.instL levels)) (.sort .zero))
      params (.sort .zero) := by
    have retargeted := paramsSpine.retarget hconstructorLength (.sort .zero)
    rw [VExpr.instRev_closedN params (by trivial)] at retargeted
    exact retargeted
  have hfields := self.fieldTelescope.instL hlevels
  have hconstructorParams := (self.constructorParams_onTel henv).instL hlevels
  have hconstructorLift : VExpr.liftTelN Γ.length
      (view.constructorParams.map (VExpr.instL levels)) 0 =
      view.constructorParams.map (VExpr.instL levels) := by
    simpa using VEnv.OnTel.liftTelN_eq henv hconstructorParams
      (by trivial) Γ.length
  have Wparams := Ctx.LiftN.consTel
    (view.constructorParams.map (VExpr.instL levels))
    (Ctx.LiftN.zero (n := Γ.length) (Γ := []) Γ)
  rw [hconstructorLift] at Wparams
  have hconstructorCtx : OnCtx
      (view.constructorParams.reverse.map (VExpr.instL levels))
      (env.IsType U) := by
    simpa [List.map_reverse] using
      VEnv.OnTel.toOnCtx hconstructorParams (by trivial)
  have hfieldLift := VEnv.OnSortTel.liftTelN_eq henv hfields
    (VEnv.CtxWF.closed henv hconstructorCtx) Γ.length
  have hfieldsΓ := VEnv.OnSortTel.weakN henv
    (by simpa [List.map_reverse] using Wparams) hfields
  simp only [List.length_reverse, List.length_map] at hfieldLift
  rw [hfieldLift] at hfieldsΓ
  have hspecialized := VEnv.OnSortTel.instRevParams henv hparams
    hconstructorLength
    (by simpa [List.map_reverse] using hfieldsΓ)
  rw [VExpr.instRevAt_map_instL_zipIdx] at hspecialized
  simpa [specializedFields] using hspecialized

/-- The producer-aligned constructor parameter layer discharges the explicit
spine premise and exposes the usual specialized restored field telescope. -/
theorem ConstructorParameterLayoutWF.specializedFields_onSortTel
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.ConstructorParameterLayoutWF env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel)) :
    env.OnSortTel U Γ (view.specializedFields levels params)
      (view.fieldSorts.map (VLevel.inst levels)) := by
  apply self.toLayoutWF
    |>.specializedFields_onSortTel_of_constructorParamsSpine henv levels
      hlevels params hparamsLength
  exact self.constructorParamsSpine henv levels hlevels hlevelsLength
    params hparamsLength paramsSpine (.sort .zero)

/-- The restored source constructor, at arbitrary caller universes and
well-typed family parameters, has the exact specialized restored field
telescope and returns the public restored structure type. -/
theorem ConstructorParameterLayoutWF.constructorPrefix_hasType
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.ConstructorParameterLayoutWF env) (henv : env.ConversionRegular)
    (closed : RestoreEntriesClosed view.nested.recEntries)
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
  let gen := view.nested.generation
  let pLevels := view.flatView.projectionLevels .zero levels
  let restoredParams := gen.paramsTel.map view.nested.restoreRec
  let restoredParamsAt := restoredParams.map (VExpr.instL pLevels)
  let constructorParams :=
    view.constructorParams.map (VExpr.instL levels)
  let sourceFields := view.fields.map (VExpr.instL levels)
  let parameters := VExpr.bvarRevRange 0 view.nparams
  let ctorPrefix :=
    VExpr.appN (.const view.constructorName levels) parameters
  let familyPrefix := VExpr.appN (.const view.name levels) parameters
  have hpLevelsWF : ∀ level ∈ pLevels, level.WF U := by
    change ∀ level ∈
      (match gen.elimination with
      | .large => VLevel.zero :: levels
      | .small => levels), level.WF U
    cases gen.elimination with
    | large =>
      intro level member
      have member' : level = VLevel.zero ∨ level ∈ levels := by
        simpa using member
      rcases member' with rfl | member
      · trivial
      · exact hlevels level member
    | small =>
      intro level member
      exact hlevels level (by simpa using member)
  have sourceLevels :
      gen.sourceLevels.map (VLevel.inst pLevels) = levels := by
    simpa [pLevels, gen, VRestoredBlockStructureView.flatView] using
      view.flatView.sourceLevels_projectionLevels .zero levels
        (by simpa only [view.flatView_uvars] using hlevelsLength)
  have sourceFieldsAt :
      (view.fields.map (VExpr.instL gen.sourceLevels)).map
          (VExpr.instL pLevels) = sourceFields := by
    simp [sourceFields, List.map_map, Function.comp_def,
      VExpr.instL_instL, sourceLevels]
  have constructorParamsAt :
      (view.constructorParams.map (VExpr.instL gen.sourceLevels)).map
          (VExpr.instL pLevels) = constructorParams := by
    simp [constructorParams, List.map_map, Function.comp_def,
      VExpr.instL_instL, sourceLevels]
  have parametersAt : parameters.map (VExpr.instL pLevels) = parameters := by
    exact VExpr.bvarRevRange_map_instL pLevels 0 view.nparams
  have sourceFieldsLength : sourceFields.length = view.fields.length := by
    simp [sourceFields]
  have ctorAt :
      (VExpr.appN (.const view.constructorName gen.sourceLevels)
        parameters).instL pLevels = ctorPrefix := by
    simp [ctorPrefix, VExpr.instL_appN, VExpr.instL,
      parametersAt, sourceLevels]
  have familyAt :
      (VExpr.appN (.const view.name gen.sourceLevels)
        parameters).instL pLevels = familyPrefix := by
    simp [familyPrefix, VExpr.instL_appN, VExpr.instL,
      parametersAt, sourceLevels]
  have canonical₀ :=
    self.toFamilyLayoutWF.sourceConstructorCanonicalPrefix_hasType
      henv closed
  dsimp only at canonical₀
  change env.HasType gen.recUvars restoredParams.reverse
      (VExpr.appN (.const view.constructorName gen.sourceLevels) parameters)
      (VExpr.forallN
        (view.fields.map (VExpr.instL gen.sourceLevels))
        ((VExpr.appN (.const view.name gen.sourceLevels) parameters).liftN
          (view.fields.map (VExpr.instL gen.sourceLevels)).length)) at canonical₀
  have canonicalL := canonical₀.instL hpLevelsWF
  have canonical : env.HasType U restoredParamsAt.reverse ctorPrefix
      (VExpr.forallN sourceFields
        (familyPrefix.liftN sourceFields.length)) := by
    rw [List.map_reverse, VExpr.instL_forallN,
      VExpr.instL_liftN, sourceFieldsAt, ctorAt, familyAt] at canonicalL
    simpa [restoredParamsAt, sourceFieldsLength] using canonicalL
  have paramsDefEq₀ := self.restoredParamsDefEq henv closed
  dsimp only at paramsDefEq₀
  have paramsDefEqL := paramsDefEq₀.instL hpLevelsWF
  have paramsDefEq : env.TelDefEq U [] constructorParams
      restoredParamsAt := by
    change env.TelDefEq U []
      ((view.constructorParams.map
        (VExpr.instL gen.sourceLevels)).map (VExpr.instL pLevels))
      restoredParamsAt at paramsDefEqL
    rw [constructorParamsAt] at paramsDefEqL
    exact paramsDefEqL
  have canonicalConstructorCtx : env.HasType U constructorParams.reverse
      ctorPrefix
      (VExpr.forallN sourceFields
        (familyPrefix.liftN sourceFields.length)) := by
    have contextEq : env.IsDefEqCtx U [] constructorParams.reverse
        restoredParamsAt.reverse := by
      simpa using paramsDefEq.ctx
    exact canonical.defeqDFC henv.ordered
      (contextEq.symm henv.ordered)
  have constructorCtx : OnCtx constructorParams.reverse
      (env.IsType U) := by
    simpa only [List.append_nil] using
      VEnv.OnTel.onCtx (by trivial) paramsDefEq.raw_onTel
  have canonicalΓ : env.HasType U (constructorParams.reverse ++ Γ)
      ctorPrefix
      (VExpr.forallN sourceFields
        (familyPrefix.liftN sourceFields.length)) :=
    canonicalConstructorCtx.weakR henv.ordered
      (VEnv.CtxWF.closed henv.ordered constructorCtx) Γ
  have constructorSpine := self.constructorParamsSpine henv.ordered
    levels hlevels hlevelsLength params hparamsLength paramsSpine (.sort .zero)
  rw [VExpr.instRev_closedN params (by trivial)] at constructorSpine
  have paramsLength : params.length = constructorParams.length := by
    simpa [constructorParams] using
      hparamsLength.trans view.constructorParams_length.symm
  have constructorTermSpine := constructorSpine.retarget paramsLength ctorPrefix
  have instantiated := constructorTermSpine.instRev_defeq henv.ordered
    paramsLength canonicalΓ
  have parametersInst : parameters.map (VExpr.instRev · params) = params := by
    change (VExpr.bvarRevRange 0 view.nparams).map
      (VExpr.instRev · params) = params
    rw [show view.nparams = params.length from hparamsLength.symm]
    exact VExpr.map_instRev_bvarRevRange params
  have ctorInst : ctorPrefix.instRev params =
      VExpr.appN (.const view.constructorName levels) params := by
    simp only [ctorPrefix, VExpr.instRev_appN, parametersInst]
    rw [VExpr.instRev_closedN params (by trivial)]
  have familyInst : familyPrefix.instRev params =
      view.structureType levels params := by
    simp only [familyPrefix, VExpr.instRev_appN, parametersInst]
    rw [VExpr.instRev_closedN params (by trivial)]
    rfl
  rw [ctorInst, VExpr.instRev_forallN_projection,
    VExpr.liftN_instRevAt_same, familyInst] at instantiated
  rw [VExpr.instRevAt_map_instL_zipIdx] at instantiated
  change env.IsDefEq U Γ
    (VExpr.appN (.const view.constructorName levels) params)
    (VExpr.appN (.const view.constructorName levels) params)
    (VExpr.forallN (view.specializedFields levels params)
      ((view.structureType levels params).liftN
        (view.specializedFields levels params).length))
  simpa [sourceFields, specializedFields] using instantiated

/-- The restored constructor layout and complete operational projector
typing discharge the rule-independent reconstruction contract. -/
theorem ConstructorParameterLayoutWF.toOperationalRebuildWF_of_programs
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.ConstructorParameterLayoutWF env)
    (henv : env.ConversionRegular)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    (programs : view.OperationalProgramsWF env) :
    view.OperationalRebuildWF env := by
  intro U Γ levels params major hΓ hlevels hlevelsLength hparamsLength
    hparamsSpine hmajor
  exact programs.operationalEtaRebuild_hasType_of_constructorPrefix
    self.toLayoutWF henv closed hΓ hlevels hlevelsLength
      hparamsLength hparamsSpine hmajor
      (self.constructorPrefix_hasType henv closed levels hlevels
        hlevelsLength params hparamsLength hparamsSpine)

/-- The restored constructor fully applied to its fields has the lifted
public structure type in the canonical field context. -/
theorem ConstructorParameterLayoutWF.projectionConstructorApp_hasType
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.ConstructorParameterLayoutWF env) (henv : env.ConversionRegular)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    {U : Nat} {context : List VExpr} (_hcontext :
      OnCtx context (env.IsType U))
    {levels : List VLevel} (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    {params : List VExpr} (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U context (view.familyType.instL levels)
        params (.sort resultLevel)) :
    let fields := view.specializedFields levels params
    env.HasType U (fields.reverse ++ context)
      (view.projectionConstructorApp levels params fields)
      ((view.structureType levels params).liftN fields.length) := by
  let fields := view.specializedFields levels params
  let count := fields.length
  have hconstructorPrefix := self.constructorPrefix_hasType henv closed
    levels hlevels hlevelsLength params hparamsLength hparamsSpine
  have hconstructorPrefixWeak := hconstructorPrefix.weakN henv.ordered
    (Ctx.LiftN.zero (n := count) (Γ := context) fields.reverse
      (h := by simp [count]))
  have hconstructorPrefixSelf : env.HasType U
      (([] : List VExpr) ++ fields.reverse ++ context)
      ((VExpr.appN (.const view.constructorName levels) params).liftN count)
      ((VExpr.forallN fields
        ((view.structureType levels params).liftN count)).liftN
          (([] : List VExpr).length + fields.length)) := by
    simpa [fields, count] using hconstructorPrefixWeak
  have hmajor := VEnv.HasType.appN_selfSpine
    (env := env) (U := U) (As := fields)
    (B := (view.structureType levels params).liftN count)
    (Δ := []) (Γ := context)
    (f := (VExpr.appN (.const view.constructorName levels) params).liftN count)
    hconstructorPrefixSelf
  simpa [fields, count, VRestoredBlockStructureView.projectionConstructorApp,
    VExpr.liftN, VExpr.liftN_appN, VExpr.appN_append, List.map_map,
    Function.comp_def] using hmajor

private theorem VExpr.telN_add_local (first second : Nat)
    (expression : VExpr) :
    VExpr.telN (first + second) expression =
      VExpr.telN first expression ++
        VExpr.telN second (VExpr.dropN first expression) := by
  induction first generalizing expression with
  | zero => simp [VExpr.telN, VExpr.dropN]
  | succ first ih =>
      cases expression with
      | forallE domain body =>
          simp only [Nat.succ_add, VExpr.telN, VExpr.dropN,
            List.cons_append]
          congr 1
          simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            ih body
      | bvar | sort | const | app | lam =>
          cases second <;> rfl

/-- The selected restored minor has its exact live cursor type.  The proof
recovers both the constructor-field and recursive-hypothesis telescopes from
that cursor, then transports the canonical selector across the restored
motive equation. -/
theorem ConstructorParameterLayoutWF.restoredSelectedMinorWith_hasType_of_isType
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.ConstructorParameterLayoutWF env) (henv : env.ConversionRegular)
    (codeNaturality : view.flatView.OperationalCodeNaturality)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    {U : Nat} {context : List VExpr}
    (levels : List VLevel) (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (hcontext : OnCtx context (env.IsType U))
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U context (view.familyType.instL levels)
        params (.sort resultLevel))
    {index : Nat} {code : VStructureView.ProjectionCode}
    {programSort : VLevel}
    (hcode : (view.operationalProjectionCodes levels params)[index]? =
      some code)
    (typeFnType : env.HasType U context code.typeFn
      (.forallE (view.structureType levels params) (.sort programSort)))
    (aligned : view.OperationalConstructorFieldAligned env U context
      levels params index)
    (flatTemplate : VStructureView.ProjectionCode)
    (flatTypeFnLam : ∃ domain body,
      flatTemplate.typeFn = .lam domain body)
    (selectedMotiveEq :
      (view.nested.restoreRecAt
        (view.flatView.projectionLevels programSort levels)
        flatTemplate.typeFn.lift).instRevAt params 1 = code.typeFn.lift)
    (minorIsType :
      let gen := view.nested.generation
      let constructor := view.flatView.blockConstructor
      let projectionLevels :=
        view.flatView.projectionLevels programSort levels
      let formalParams := VExpr.bvarRevRange 0 view.nparams
      let flatParamsMajor := formalParams.map (VExpr.liftN 1)
      let paramsMajor := params.map (VExpr.liftN 1)
      let flatDummyType := VBlockStructureView.majorDummyType
        flatTemplate.typeFn.lift (.bvar 0)
      let flatMotives := view.flatView.projectionMotivesWith levels
        flatParamsMajor flatTemplate.typeFn.lift flatDummyType
      let motivesMajor := flatMotives.map fun expression =>
        (view.nested.restoreRecAt projectionLevels expression).instRevAt
          params 1
      env.IsType U (view.structureType levels params :: context)
        (((view.nested.restoreRecAt projectionLevels
          ((gen.minorType constructor).instL projectionLevels)).instRevAt
            paramsMajor gen.familyCount).instRev motivesMajor)) :
    let gen := view.nested.generation
    let constructor := view.flatView.blockConstructor
    let projectionLevels :=
      view.flatView.projectionLevels programSort levels
    let formalParams := VExpr.bvarRevRange 0 view.nparams
    let flatParamsMajor := formalParams.map (VExpr.liftN 1)
    let paramsMajor := params.map (VExpr.liftN 1)
    let flatDummyType := VBlockStructureView.majorDummyType
      flatTemplate.typeFn.lift (.bvar 0)
    let flatDummyValue := VBlockStructureView.majorDummyValue
      flatTemplate.typeFn.lift (.bvar 0)
    let flatMotives := view.flatView.projectionMotivesWith levels
      flatParamsMajor flatTemplate.typeFn.lift flatDummyType
    let motivesMajor := flatMotives.map fun expression =>
      (view.nested.restoreRecAt projectionLevels expression).instRevAt params 1
    let exactMinor :=
      (((view.nested.restoreRecAt projectionLevels
        ((gen.minorType constructor).instL projectionLevels)).instRevAt
          paramsMajor gen.familyCount).instRev motivesMajor)
    let flatSelectedMinor := view.flatView.projectionMinorWith constructor
      programSort levels flatParamsMajor
        (view.flatView.specializedFields levels flatParamsMajor)
        flatMotives index flatDummyValue
    env.HasType U (view.structureType levels params :: context)
      ((view.nested.restoreRecAt projectionLevels flatSelectedMinor).instRevAt
        params 1)
      exactMinor := by
  let gen := view.nested.generation
  let constructor := view.flatView.blockConstructor
  let projectionLevels :=
    view.flatView.projectionLevels programSort levels
  let formalParams := VExpr.bvarRevRange 0 view.nparams
  let flatParamsMajor := formalParams.map (VExpr.liftN 1)
  let paramsMajor := params.map (VExpr.liftN 1)
  let flatDummyType := VBlockStructureView.majorDummyType
    flatTemplate.typeFn.lift (.bvar 0)
  let flatDummyValue := VBlockStructureView.majorDummyValue
    flatTemplate.typeFn.lift (.bvar 0)
  let flatMotives := view.flatView.projectionMotivesWith levels
    flatParamsMajor flatTemplate.typeFn.lift flatDummyType
  let motivesMajor := flatMotives.map fun expression =>
    (view.nested.restoreRecAt projectionLevels expression).instRevAt params 1
  let exactMinor :=
    (((view.nested.restoreRecAt projectionLevels
      ((gen.minorType constructor).instL projectionLevels)).instRevAt
        paramsMajor gen.familyCount).instRev motivesMajor)
  let flatSelectedMinor := view.flatView.projectionMinorWith constructor
    programSort levels flatParamsMajor
      (view.flatView.specializedFields levels flatParamsMajor)
      flatMotives index flatDummyValue
  let majorContext := view.structureType levels params :: context
  let fields := view.specializedFields levels paramsMajor
  let fieldCount := fields.length
  let ihCount := constructor.ctor.view.recursive.length
  let count := fieldCount + ihCount
  let ihs := VExpr.telN ihCount (VExpr.dropN fieldCount exactMinor)
  let result := VExpr.dropN count exactMinor
  dsimp only
  obtain ⟨resultLevel, hparamsSpine₀⟩ := hparamsSpine
  have familyTypeClosed : (view.familyType.instL levels).ClosedN 0 := by
    simpa using
      (self.toFamilyLayoutWF.familyType_closed henv.ordered).instL
  have familyType : env.HasType U context (.const view.name levels)
      (view.familyType.instL levels) :=
    self.toFamilyLayoutWF.familyConst_hasType henv.ordered levels hlevels
      hlevelsLength
  have structureType : env.HasType U context
      (view.structureType levels params) (.sort resultLevel) := by
    simpa [VRestoredBlockStructureView.structureType] using
      hparamsSpine₀.hasType_appN familyType
  have hmajorContext : OnCtx majorContext (env.IsType U) := by
    exact ⟨hcontext, resultLevel, structureType⟩
  have paramsMajorLength : paramsMajor.length = view.nparams := by
    simpa [paramsMajor] using hparamsLength
  have paramsMajorSpine : env.SpineWF U majorContext
      (view.familyType.instL levels) paramsMajor (.sort resultLevel) := by
    have weakened := hparamsSpine₀.weakN henv.ordered
      (Ctx.LiftN.one (A := view.structureType levels params))
    rw [familyTypeClosed.liftN_eq (Nat.zero_le _)] at weakened
    simpa [majorContext, paramsMajor, VExpr.liftN] using weakened
  have structureTypeMajor : view.structureType levels paramsMajor =
      (view.structureType levels params).lift := by
    change view.structureType levels
        (params.map fun parameter => parameter.liftN 1 0) =
      (view.structureType levels params).liftN 1 0
    exact (view.structureType_liftN levels params 1 0).symm
  let codeMajor := code.liftN 1 0
  have codesMajor := view.operationalProjectionCodes_liftN
    codeNaturality closed levels params hparamsLength 1 0
  have hcodeMajor :
      (view.operationalProjectionCodes levels paramsMajor)[index]? =
        some codeMajor := by
    rw [← codesMajor, List.getElem?_map, hcode]
    rfl
  have typeFnMajor : env.HasType U majorContext codeMajor.typeFn
      (.forallE (view.structureType levels paramsMajor)
        (.sort programSort)) := by
    have weakened := typeFnType.weakN henv.ordered
      (Ctx.LiftN.one (A := view.structureType levels params))
    simpa [codeMajor, VStructureView.ProjectionCode.liftN,
      structureTypeMajor, majorContext, VExpr.liftN] using weakened
  have alignedMajor : view.OperationalConstructorFieldAligned env U
      majorContext levels paramsMajor index := by
    change view.OperationalConstructorFieldAligned env U
      (view.structureType levels params :: context) levels
        (params.map (VExpr.liftN 1)) index
    exact self.toLayoutWF.operationalConstructorFieldAligned_weak
      henv.ordered codeNaturality closed hparamsLength aligned
        (view.structureType levels params)
  have hindex : index < fields.length := by
    have := (List.getElem?_eq_some_iff.1 hcodeMajor).1
    simpa [fields] using this
  have flatFieldCountEq :
      (view.flatView.specializedCtorFields constructor levels
        flatParamsMajor).length = fieldCount := by
    calc
      _ = view.flatView.fields.length := by
        simp [VBlockStructureView.specializedCtorFields,
          VBlockStructureView.fields, constructor,
          VBlockStructureView.blockConstructor]
      _ = view.fields.length := by
        simpa [VRestoredBlockStructureView.fields,
          VRestoredBlockStructureView.flatView,
          VBlockStructureView.fields] using
            view.selection.source_flat_fields_length_eq.symm
      _ = fieldCount := by
        simp [fieldCount, fields,
          VRestoredBlockStructureView.specializedFields]
  have fieldsPrefix : VExpr.telN fieldCount exactMinor = fields := by
    have fieldPrefixProof := self.restoredSelectedMinorFields henv closed
      programSort levels hlevelsLength params hparamsLength flatTemplate
        flatTypeFnLam
    dsimp only at fieldPrefixProof
    change VExpr.telN
      (view.flatView.specializedCtorFields constructor levels
        flatParamsMajor).length exactMinor = fields at fieldPrefixProof
    rwa [flatFieldCountEq] at fieldPrefixProof
  have fullBindersLength :
      (VExpr.telN count exactMinor).length = count := by
    have length := self.restoredProjectionMinorBinders_length henv closed
      constructor view.flatView.blockConstructor_mem programSort levels
        params hparamsLength flatTemplate flatTypeFnLam
    dsimp only at length
    change (VExpr.telN
      ((view.flatView.specializedCtorFields constructor levels
        flatParamsMajor).length + ihCount) exactMinor).length =
      (view.flatView.specializedCtorFields constructor levels
        flatParamsMajor).length + ihCount at length
    rwa [flatFieldCountEq] at length
  have splitBinders : VExpr.telN count exactMinor = fields ++ ihs := by
    rw [show count = fieldCount + ihCount by rfl,
      VExpr.telN_add_local, fieldsPrefix]
  have ihsLength : ihs.length = ihCount := by
    have lengths := congrArg List.length splitBinders
    rw [fullBindersLength] at lengths
    simp only [List.length_append] at lengths
    dsimp only [count, fieldCount] at lengths
    omega
  have exactShape : exactMinor =
      VExpr.forallN fields (VExpr.forallN ihs result) := by
    calc
      exactMinor = VExpr.forallN (VExpr.telN count exactMinor)
          (VExpr.dropN count exactMinor) :=
        (VExpr.forallN_telN_dropN count exactMinor).symm
      _ = VExpr.forallN (fields ++ ihs) result := by
        rw [splitBinders]
      _ = VExpr.forallN fields (VExpr.forallN ihs result) := by
        rw [VExpr.forallN_append]
  obtain ⟨minorLevel, minorType⟩ := minorIsType
  change env.HasType U majorContext exactMinor (.sort minorLevel) at minorType
  rw [exactShape] at minorType
  obtain ⟨hfields, afterFieldsLevel, afterFieldsType⟩ :=
    VEnv.HasType.forallN_wf henv.ordered minorType
  obtain ⟨hihs, resultSort, resultType⟩ :=
    VEnv.HasType.forallN_wf henv.ordered afterFieldsType
  have fieldsContext : OnCtx (fields.reverse ++ majorContext)
      (env.IsType U) := hfields.toOnCtx hmajorContext
  have constructorMajor : env.HasType U (fields.reverse ++ majorContext)
      (view.projectionConstructorApp levels paramsMajor fields)
      ((view.structureType levels paramsMajor).liftN fieldCount) := by
    simpa [fields, fieldCount, majorContext] using
      self.projectionConstructorApp_hasType henv closed hmajorContext
        hlevels hlevelsLength paramsMajorLength
          ⟨resultLevel, paramsMajorSpine⟩
  obtain ⟨field, hfield, -⟩ :=
    self.toLayoutWF.operationalProjectionCodes_get?_typeFn_source_shape
      henv.ordered closed levels hlevelsLength paramsMajor
        paramsMajorLength hcodeMajor
  let paramsFields := paramsMajor.map (VExpr.liftN fieldCount)
  have paramsFieldsLength : paramsFields.length = view.nparams := by
    simpa [paramsFields] using paramsMajorLength
  have codesFields := view.operationalProjectionCodes_liftN
    codeNaturality closed levels paramsMajor paramsMajorLength fieldCount 0
  let codeFields := codeMajor.liftN fieldCount 0
  have hcodeFields :
      (view.operationalProjectionCodes levels paramsFields)[index]? =
        some codeFields := by
    rw [← codesFields, List.getElem?_map, hcodeMajor]
    rfl
  have specializedFieldsLift :
      view.specializedFields levels paramsFields =
        VExpr.liftTelN fieldCount fields 0 := by
    simpa [paramsFields, fields] using
      self.toLayoutWF.specializedFields_liftN henv.ordered levels paramsMajor
        paramsMajorLength fieldCount 0
  have fieldLiftGet :
      (view.specializedFields levels paramsFields)[index]? =
        some (field.liftN fieldCount index) := by
    rw [specializedFieldsLift, VExpr.liftTelN_getElem?, hfield]
    simp
  have structureTypeFields : view.structureType levels paramsFields =
      (view.structureType levels paramsMajor).liftN fieldCount := by
    simpa [paramsFields] using
      (view.structureType_liftN levels paramsMajor fieldCount 0).symm
  have constructorMajorFields : env.HasType U
      (fields.reverse ++ majorContext)
      (view.projectionConstructorApp levels paramsMajor fields)
      (view.structureType levels paramsFields) := by
    rwa [structureTypeFields]
  have typeFnFieldsFull := typeFnMajor.weakN henv.ordered
    (Ctx.LiftN.zero (n := fieldCount) (Γ := majorContext) fields.reverse
      (h := by simp [fieldCount]))
  have typeFnFields : env.HasType U (fields.reverse ++ majorContext)
      codeFields.typeFn
      (.forallE (view.structureType levels paramsFields)
        (.sort programSort)) := by
    simpa [codeFields, codeMajor, VStructureView.ProjectionCode.liftN,
      structureTypeFields, VExpr.liftN] using typeFnFieldsFull
  have leftArgs :
      view.operationalProjectionArgs levels paramsFields index
          (view.projectionConstructorApp levels paramsMajor fields) =
        ((view.operationalProjectionCodes levels paramsMajor).take index).map
          fun prior =>
            .app (prior.projector.liftN fieldCount)
              (view.projectionConstructorApp levels paramsMajor fields) := by
    unfold operationalProjectionArgs
    rw [← codesFields]
    simp [List.map_take, List.map_map,
      VStructureView.ProjectionCode.liftN, Function.comp_def]
  have alignedField : env.IsDefEqU U (fields.reverse ++ majorContext)
      ((field.liftN fieldCount index).instRev
        (((view.operationalProjectionCodes levels paramsMajor).take index).map
          fun prior =>
            .app (prior.projector.liftN fieldCount)
              (view.projectionConstructorApp levels paramsMajor fields)))
      (field.liftN (fieldCount - index)) := by
    simpa [fields, fieldCount] using alignedMajor hfield
  obtain ⟨fieldLift, typeDomain, typeBody, hfieldLiftCode,
      typeFnFieldsShape, typeBodyContract⟩ :=
    self.toLayoutWF.operationalProjectionCodes_get?_typeFn_beta
      henv.ordered closed levels hlevelsLength paramsFields hcodeFields
        (view.projectionConstructorApp levels paramsMajor fields)
  have fieldLiftEq : fieldLift = field.liftN fieldCount index :=
    Option.some.inj (hfieldLiftCode.symm.trans fieldLiftGet)
  subst fieldLift
  rw [typeFnFieldsShape] at typeFnFields
  obtain ⟨⟨domainLevel, domainTyping⟩, ⟨bodyResult, typeBodyTyping⟩⟩ :=
    typeFnFields.lam_inv henv.ordered fieldsContext
  have hregular : env.ConversionRegular := henv
  have functionTypeEq := hregular.hasType_uniqU fieldsContext typeFnFields
    (domainTyping.lam typeBodyTyping)
  obtain ⟨⟨_, domainEq⟩, _⟩ :=
    hregular.forallE_inv fieldsContext functionTypeEq
  have constructorMajorDomain := hregular.hasType_defeqU_r fieldsContext
    ⟨_, domainEq⟩ constructorMajorFields
  have betaRaw := VEnv.IsDefEq.beta typeBodyTyping constructorMajorDomain
  rw [typeBodyContract, leftArgs] at betaRaw
  have beta : env.IsDefEqU U (fields.reverse ++ majorContext)
      (.app ((code.typeFn.lift).liftN fieldCount)
        (view.projectionConstructorApp levels paramsMajor fields))
      ((field.liftN fieldCount index).instRev
        (((view.operationalProjectionCodes levels paramsMajor).take index).map
          fun prior =>
            .app (prior.projector.liftN fieldCount)
              (view.projectionConstructorApp levels paramsMajor fields))) := by
    have typeFnHead : (code.typeFn.lift).liftN fieldCount =
        .lam typeDomain typeBody := by
      simpa [codeFields, codeMajor, VStructureView.ProjectionCode.liftN,
        VExpr.liftN] using typeFnFieldsShape
    refine ⟨bodyResult.inst
      (view.projectionConstructorApp levels paramsMajor fields), ?_⟩
    rw [typeFnHead]
    simpa only [VExpr.instRevAt_zero] using betaRaw
  have motiveEq : env.IsDefEqU U (fields.reverse ++ majorContext)
      (.app ((code.typeFn.lift).liftN fieldCount)
        (view.projectionConstructorApp levels paramsMajor fields))
      (field.liftN (fieldCount - index)) :=
    hregular.isDefEqU_trans fieldsContext beta alignedField
  let selectorIndex := fieldCount - 1 - index
  have selectorLt : selectorIndex < fields.length := by
    dsimp only [selectorIndex, fieldCount]
    omega
  have fieldReverse : fields.reverse[selectorIndex]? = some field := by
    rw [List.getElem?_reverse selectorLt,
      show fields.length - 1 - selectorIndex = index by
        dsimp only [selectorIndex, fieldCount]
        omega,
      hfield]
  have fieldContextLookup :
      (fields.reverse ++ majorContext)[selectorIndex]? = some field := by
    rw [List.getElem?_append_left (by simpa using selectorLt), fieldReverse]
  have selectorType : env.HasType U (fields.reverse ++ majorContext)
      (.bvar selectorIndex) (field.liftN (fieldCount - index)) := by
    have lookup := VEnv.HasType.bvar (env := env) (U := U)
      (Lookup.of_getElem? fieldContextLookup)
    have selectorSucc : selectorIndex + 1 = fieldCount - index := by
      dsimp only [selectorIndex, fieldCount]
      omega
    rwa [selectorSucc] at lookup
  have selectorExpected : env.HasType U (fields.reverse ++ majorContext)
      (.bvar selectorIndex)
      (.app ((code.typeFn.lift).liftN fieldCount)
        (view.projectionConstructorApp levels paramsMajor fields)) :=
    hregular.hasType_defeqU_r fieldsContext motiveEq.symm selectorType
  have selectedMinorType := VEnv.HasType.selectFieldMinor_of_weak
    henv.ordered hfields hihs hindex
      (by simpa [selectorIndex, fieldCount] using selectorExpected)
  have resultShape := self.restoredSelectedMinorResult_shape henv closed
    programSort levels hlevelsLength params hparamsLength flatTemplate
      flatTypeFnLam selectedMotiveEq
  dsimp only at resultShape
  change VExpr.dropN count exactMinor =
    (VExpr.app ((code.typeFn.lift).liftN fieldCount)
      (view.projectionConstructorApp levels paramsMajor fields)).liftN
        ihCount at resultShape
  have resultShape' : result =
      (VExpr.app ((code.typeFn.lift).liftN fieldCount)
        (view.projectionConstructorApp levels paramsMajor fields)).liftN
          ihs.length := by
    rw [ihsLength]
    exact resultShape
  have selectedExpected : env.HasType U majorContext
      (VExpr.selectFieldMinor fields ihs index) exactMinor := by
    rw [exactShape, resultShape']
    exact selectedMinorType
  have syntaxShape := self.restoredSelectedMinorWith_shape henv closed
    programSort levels hlevelsLength params hparamsLength flatTemplate
      flatTypeFnLam index (by
        have bound := (List.getElem?_eq_some_iff.1 hcode).1
        simpa using bound)
  dsimp only at syntaxShape
  rw [flatFieldCountEq] at syntaxShape
  change (view.nested.restoreRecAt projectionLevels
      flatSelectedMinor).instRevAt params 1 =
    VExpr.lamN (VExpr.telN count exactMinor)
      (.bvar (ihCount + fieldCount - 1 - index)) at syntaxShape
  rw [splitBinders] at syntaxShape
  have selectedSyntax :
      VExpr.lamN (fields ++ ihs)
          (.bvar (ihCount + fieldCount - 1 - index)) =
        VExpr.selectFieldMinor fields ihs index := by
    unfold VExpr.selectFieldMinor
    rw [← VExpr.lamN_append]
    rw [ihsLength]
  rw [selectedSyntax] at syntaxShape
  rw [syntaxShape]
  exact selectedExpected

/-- The complete restored minor inventory inhabits the exact live recursor
minor cursor.  Each cursor domain is inverted before its argument is built;
the selected constructor uses the dependent field selector, while every
other constructor uses the restored identity minor. -/
theorem ConstructorParameterLayoutWF.restoredProjectionMinors_forall₂_hasType
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.ConstructorParameterLayoutWF env) (henv : env.ConversionRegular)
    (codeNaturality : view.flatView.OperationalCodeNaturality)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    {U : Nat} {context : List VExpr}
    (levels : List VLevel) (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (hcontext : OnCtx context (env.IsType U))
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U context (view.familyType.instL levels)
        params (.sort resultLevel))
    (hmajorContext : OnCtx
      (view.structureType levels params :: context) (env.IsType U))
    {index : Nat} {code : VStructureView.ProjectionCode}
    {programSort : VLevel}
    (hcode : (view.operationalProjectionCodes levels params)[index]? =
      some code)
    (typeFnType : env.HasType U context code.typeFn
      (.forallE (view.structureType levels params) (.sort programSort)))
    (aligned : view.OperationalConstructorFieldAligned env U context
      levels params index)
    (flatTemplate : VStructureView.ProjectionCode)
    (flatTypeFnLam : ∃ domain body,
      flatTemplate.typeFn = .lam domain body)
    (selectedMotiveEq :
      (view.nested.restoreRecAt
        (view.flatView.projectionLevels programSort levels)
        flatTemplate.typeFn.lift).instRevAt params 1 = code.typeFn.lift)
    (hmotiveLevel : view.nested.generation.motiveLevel.inst
      (view.flatView.projectionLevels programSort levels) =
        programSort)
    (dummyType dummyValue : VExpr)
    (dummyTypeEq :
      let projectionLevels :=
        view.flatView.projectionLevels programSort levels
      let flatDummyType := VBlockStructureView.majorDummyType
        flatTemplate.typeFn.lift (.bvar 0)
      (view.nested.restoreRecAt projectionLevels flatDummyType).instRevAt
        params 1 = dummyType)
    (dummyValueEq :
      let projectionLevels :=
        view.flatView.projectionLevels programSort levels
      let flatDummyValue := VBlockStructureView.majorDummyValue
        flatTemplate.typeFn.lift (.bvar 0)
      (view.nested.restoreRecAt projectionLevels flatDummyValue).instRevAt
        params 1 = dummyValue)
    (dummyValueType : env.HasType U
      (view.structureType levels params :: context) dummyValue dummyType)
    (function tail : VExpr)
    (functionType :
      let projectionLevels :=
        view.flatView.projectionLevels programSort levels
      let formalParams := VExpr.bvarRevRange 0 view.nparams
      let flatParamsMajor := formalParams.map (VExpr.liftN 1)
      let paramsMajor := params.map (VExpr.liftN 1)
      let flatDummyType := VBlockStructureView.majorDummyType
        flatTemplate.typeFn.lift (.bvar 0)
      let flatMotives := view.flatView.projectionMotivesWith levels
        flatParamsMajor flatTemplate.typeFn.lift flatDummyType
      let motivesMajor := flatMotives.map fun expression =>
        (view.nested.restoreRecAt projectionLevels expression).instRevAt
          params 1
      env.HasType U (view.structureType levels params :: context) function
        (VExpr.forallN
          ((view.operationalProjectionMinorTypes programSort levels
            paramsMajor motivesMajor).zipIdx.map fun entry =>
              entry.1.liftN entry.2)
          tail)) :
    let gen := view.nested.generation
    let projectionLevels :=
      view.flatView.projectionLevels programSort levels
    let formalParams := VExpr.bvarRevRange 0 view.nparams
    let flatParamsMajor := formalParams.map (VExpr.liftN 1)
    let paramsMajor := params.map (VExpr.liftN 1)
    let flatDummyType := VBlockStructureView.majorDummyType
      flatTemplate.typeFn.lift (.bvar 0)
    let flatDummyValue := VBlockStructureView.majorDummyValue
      flatTemplate.typeFn.lift (.bvar 0)
    let flatMotives := view.flatView.projectionMotivesWith levels
      flatParamsMajor flatTemplate.typeFn.lift flatDummyType
    let motivesMajor := flatMotives.map fun expression =>
      (view.nested.restoreRecAt projectionLevels expression).instRevAt params 1
    let flatMinors := gen.flatCtors.map fun constructor =>
      view.flatView.projectionMinorWith constructor programSort levels
        flatParamsMajor
        (view.flatView.specializedFields levels flatParamsMajor)
        flatMotives index flatDummyValue
    let minorsMajor := flatMinors.map fun expression =>
      (view.nested.restoreRecAt projectionLevels expression).instRevAt params 1
    List.Forall₂ (fun argument type =>
      env.HasType U (view.structureType levels params :: context)
        argument type)
      minorsMajor
      (view.operationalProjectionMinorTypes programSort levels
        paramsMajor motivesMajor) := by
  let gen := view.nested.generation
  let projectionLevels :=
    view.flatView.projectionLevels programSort levels
  let formalParams := VExpr.bvarRevRange 0 view.nparams
  let flatParamsMajor := formalParams.map (VExpr.liftN 1)
  let paramsMajor := params.map (VExpr.liftN 1)
  let flatDummyType := VBlockStructureView.majorDummyType
    flatTemplate.typeFn.lift (.bvar 0)
  let flatDummyValue := VBlockStructureView.majorDummyValue
    flatTemplate.typeFn.lift (.bvar 0)
  let flatMotives := view.flatView.projectionMotivesWith levels
    flatParamsMajor flatTemplate.typeFn.lift flatDummyType
  let motivesMajor := flatMotives.map fun expression =>
    (view.nested.restoreRecAt projectionLevels expression).instRevAt params 1
  let flatMinor := fun constructor =>
    view.flatView.projectionMinorWith constructor programSort levels
      flatParamsMajor
      (view.flatView.specializedFields levels flatParamsMajor)
      flatMotives index flatDummyValue
  let argument := fun constructor =>
    (view.nested.restoreRecAt projectionLevels
      (flatMinor constructor)).instRevAt params 1
  let exactMinor := fun constructor =>
    (((view.nested.restoreRecAt projectionLevels
      ((gen.minorType constructor).instL projectionLevels)).instRevAt
        paramsMajor gen.familyCount).instRev motivesMajor)
  dsimp only
  have cursor : env.HasType U
      (view.structureType levels params :: context) function
      (VExpr.forallN
        (progressiveRestoredTypesAux (gen.flatCtors.map exactMinor) 0)
          tail) := by
    rw [progressiveRestoredTypesAux_eq_zipIdx]
    simpa [exactMinor,
      VRestoredBlockStructureView.operationalProjectionMinorTypes,
      gen, projectionLevels, paramsMajor, motivesMajor] using functionType
  have aux : ∀ (constructors : List NormalizedBlockCtor) (f rest : VExpr),
      (∀ constructor ∈ constructors, constructor ∈ gen.flatCtors) →
      env.HasType U (view.structureType levels params :: context) f
        (VExpr.forallN
          (progressiveRestoredTypesAux (constructors.map exactMinor) 0)
          rest) →
      List.Forall₂ (fun term type =>
        env.HasType U (view.structureType levels params :: context)
          term type)
        (constructors.map argument) (constructors.map exactMinor) := by
    intro constructors
    induction constructors with
    | nil =>
        intro f rest hsub hf
        exact .nil
    | cons constructor constructors ih =>
        intro f rest hsub hf
        have cursorIsType := hf.isType henv hmajorContext
        have minorIsType : env.IsType U
            (view.structureType levels params :: context)
            (exactMinor constructor) := by
          have domain := (cursorIsType.forallE_inv henv.ordered).1
          simpa [progressiveRestoredTypesAux, exactMinor] using domain
        have argumentType : env.HasType U
            (view.structureType levels params :: context)
            (argument constructor) (exactMinor constructor) := by
          by_cases selected : constructor.owner =
              view.selection.family.view.ordinal
          · have constructorEq := view.flatView.eq_blockConstructor_of_owner
              (hsub constructor (.head _)) selected
            subst constructor
            have selectedType :=
              self.restoredSelectedMinorWith_hasType_of_isType henv
                codeNaturality closed levels hlevels hlevelsLength params
                  hparamsLength hcontext hparamsSpine hcode typeFnType aligned
                    flatTemplate flatTypeFnLam selectedMotiveEq
                      (by simpa [exactMinor, gen, projectionLevels,
                        formalParams, flatParamsMajor, paramsMajor,
                        flatDummyType, flatMotives, motivesMajor] using
                          minorIsType)
            simpa [argument, flatMinor, exactMinor, gen, projectionLevels,
              formalParams, flatParamsMajor, paramsMajor, flatDummyType,
              flatDummyValue, flatMotives, motivesMajor] using selectedType
          · have identityType :=
              self.restoredIdentityMinorWith_hasType_of_isType henv closed
                constructor (hsub constructor (.head _)) selected
                  programSort levels hlevelsLength params hparamsLength
                    hmajorContext flatTemplate flatTypeFnLam hmotiveLevel
                      dummyType dummyValue dummyTypeEq dummyValueEq
                        dummyValueType (by
                          simpa [exactMinor, gen, projectionLevels,
                            formalParams, flatParamsMajor, paramsMajor,
                            flatDummyType, flatMotives, motivesMajor] using
                            minorIsType)
            have notFlatSelected : constructor.owner ≠
                view.flatView.family.view.ordinal := by
              simpa [VRestoredBlockStructureView.flatView] using selected
            simpa [argument, flatMinor, exactMinor, gen, projectionLevels,
              formalParams, flatParamsMajor, paramsMajor, flatDummyType,
              flatDummyValue, flatMotives, motivesMajor,
              VBlockStructureView.projectionMinorWith,
              notFlatSelected] using identityType
        have argumentType' : env.HasType U
            (view.structureType levels params :: context)
            (argument constructor) ((exactMinor constructor).liftN 0) := by
          simpa [exactMinor] using argumentType
        have next := hf.app argumentType'
        simp only [List.map_cons, progressiveRestoredTypesAux,
          VExpr.instN_forallN] at next
        rw [progressiveRestoredTypesAux_instTelN] at next
        have next' : env.HasType U
            (view.structureType levels params :: context)
            (.app f (argument constructor))
            (VExpr.forallN
              (progressiveRestoredTypesAux
                (constructors.map exactMinor) 0)
              (rest.inst (argument constructor) constructors.length)) := by
          simpa [argument, exactMinor] using next
        exact .cons argumentType
          (ih (.app f (argument constructor))
            (rest.inst (argument constructor) constructors.length)
            (fun candidate member => hsub candidate (.tail _ member)) next')
  have typed := aux gen.flatCtors function tail
    (fun _ member => member) cursor
  simpa [argument, flatMinor, exactMinor, gen, projectionLevels,
    formalParams, flatParamsMajor, paramsMajor, flatDummyType,
    flatDummyValue, flatMotives, motivesMajor,
    VRestoredBlockStructureView.operationalProjectionMinorTypes] using typed

/-- The restored and flattened constructor field inventories have the same
length at the exact common parameter boundary. -/
theorem fields_length_eq_flatView (view : VRestoredBlockStructureView) :
    view.fields.length = view.flatView.fields.length := by
  simpa [fields, flatView, VBlockStructureView.fields] using
    view.selection.source_flat_fields_length_eq

theorem fields_length (view : VRestoredBlockStructureView) :
    view.fields.length = view.constructor.view.fields.length := by
  calc
    view.fields.length = view.flatView.fields.length :=
      view.fields_length_eq_flatView
    _ = view.selection.constructor.view.fields.length :=
      view.flatView.fields_length
    _ = view.constructor.view.fields.length := rfl

/-- Parameter and field binders exhaust the restored constructor telescope. -/
theorem constructorSpine_length (view : VRestoredBlockStructureView) :
    view.nparams + view.fields.length =
      (ctorFields view.sourceConstructor.type).length := by
  have split := VExpr.telN_length_add_ctorFields_dropN_length
    view.nparams view.sourceConstructor.type
  change view.constructorParams.length + view.fields.length = _ at split
  rw [view.constructorParams_length] at split
  exact split

theorem constructorFields_eq (view : VRestoredBlockStructureView) :
    ctorFields view.sourceConstructor.type =
      view.constructorParams ++ view.fields := by
  exact constructorFields_eq_core view

theorem nparams_eq_rawFamilyArity (view : VRestoredBlockStructureView) :
    view.nparams = (ctorFields view.rawFamilyType).length := by
  have flat := view.flatView.nparams_eq_rawFamilyArity
  simpa [view.flatView_nparams, view.flatView_rawFamilyType] using flat

theorem nparams_eq_familyArity (view : VRestoredBlockStructureView) :
    view.nparams = (ctorFields view.familyType).length := by
  have flat := view.flatView.nparams_eq_familyArity
  simpa [view.flatView_nparams, view.flatView_familyType] using flat

@[simp] theorem specializedFields_length
    (view : VRestoredBlockStructureView)
    (levels : List VLevel) (params : List VExpr) :
    (view.specializedFields levels params).length = view.fields.length := by
  simp [specializedFields]

/-- A sparse restored runtime prefix types the next restored dependent
type function at the public source structure domain. -/
theorem ConstructorParameterLayoutWF.operationalProjectionTypeFn_hasType_of_sparse
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.ConstructorParameterLayoutWF env) (henv : env.ConversionRegular)
    (codeNaturality : view.flatView.OperationalCodeNaturality)
    (closed : RestoreEntriesClosed view.nested.recEntries)
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
    (hcode : (view.operationalProjectionCodes levels params)[idx]? =
      some code)
    (sparse : ∃ cursor,
      env.SparseSpineWF U (view.structureType levels params :: Γ)
        (VExpr.forallN
          (view.specializedFields levels
            (params.map (VExpr.liftN 1)))
          (.sort .zero))
        (view.operationalProjectionArgs levels
          (params.map (VExpr.liftN 1)) idx (.bvar 0)) cursor) :
    env.HasType U Γ code.typeFn
      (.forallE (view.structureType levels params)
        (.sort code.fieldSort)) := by
  obtain ⟨resultLevel, hparamsSpine₀⟩ := hparamsSpine
  have hfamily : env.HasType U Γ (.const view.name levels)
      (view.familyType.instL levels) := by
    exact self.toFamilyLayoutWF.familyConst_hasType henv.ordered levels
      hlevels hlevelsLength
  have hstruct : env.HasType U Γ
      (view.structureType levels params) (.sort resultLevel) := by
    simpa [structureType] using hparamsSpine₀.hasType_appN hfamily
  have hidx : idx <
      (view.operationalProjectionCodes levels params).length :=
    (List.getElem?_eq_some_iff.1 hcode).1
  obtain ⟨flatTemplate, fieldSort, flatFound, hfieldSort, hcodeSort,
      -, -⟩ :=
    view.operationalProjectionCodes_get?_program_shape levels params hcode
  have hfamilyClosed : (view.familyType.instL levels).ClosedN 0 := by
    simpa using
      (self.toFamilyLayoutWF.familyType_closed henv.ordered).instL
  let paramsLift := params.map (VExpr.liftN 1)
  have hparamsLengthLift : paramsLift.length = view.nparams := by
    simpa [paramsLift] using hparamsLength
  have hparamsSpineLift : env.SpineWF U
      (view.structureType levels params :: Γ)
      (view.familyType.instL levels) paramsLift (.sort resultLevel) := by
    have h := hparamsSpine₀.weakN henv.ordered
      (Ctx.LiftN.one (A := view.structureType levels params))
    rw [hfamilyClosed.liftN_eq (Nat.zero_le _)] at h
    simpa [paramsLift, VExpr.liftN] using h
  have hstructLift : view.structureType levels paramsLift =
      (view.structureType levels params).lift := by
    change view.structureType levels
        (params.map fun param => param.liftN 1 0) =
      (view.structureType levels params).liftN 1 0
    exact (view.structureType_liftN levels params 1 0).symm
  have hΓLift : OnCtx (view.structureType levels params :: Γ)
      (env.IsType U) := ⟨hΓ, resultLevel, hstruct⟩
  have hcodesLift := view.operationalProjectionCodes_liftN
    codeNaturality closed levels params hparamsLength 1 0
  have hidxLift : idx <
      (view.operationalProjectionCodes levels paramsLift).length := by
    rw [← hcodesLift]
    simpa using hidx
  have hargsLength :
      (view.operationalProjectionArgs levels paramsLift idx
        (.bvar 0)).length = idx :=
    view.operationalProjectionArgs_length levels paramsLift idx (.bvar 0)
      (Nat.le_of_lt hidxLift)
  have hsortBound :
      idx < (view.fieldSorts.map (VLevel.inst levels)).length := by
    rw [List.length_map, view.fieldSorts_length]
    change idx < view.fields.length
    simpa using hidxLift
  have hsortTelLift := self.specializedFields_onSortTel henv.ordered
    levels hlevels hlevelsLength paramsLift hparamsLengthLift
    ⟨resultLevel, hparamsSpineLift⟩
  obtain ⟨cursor, hsparse⟩ := sparse
  change env.SparseSpineWF U
    (view.structureType levels params :: Γ)
    (VExpr.forallN (view.specializedFields levels paramsLift) (.sort .zero))
    (view.operationalProjectionArgs levels paramsLift idx (.bvar 0)) cursor
    at hsparse
  have hconsume := hsparse.consumeForalls_eq
  have hsortCursor := hsortTelLift.toSortCursor (.sort .zero)
  obtain ⟨next, nextSort, cursorBody, hcursor, hnextType,
      hnextSort⟩ :=
    hsortCursor.next_of_sparse henv hΓLift hsparse
      (by simpa [hargsLength] using hsortBound)
  obtain ⟨field, hfield, htypeFnShape⟩ :=
    self.toLayoutWF.operationalProjectionCodes_get?_typeFn_source_shape
      henv.ordered closed levels hlevelsLength params hparamsLength hcode
  have hfieldLift :
      (view.specializedFields levels paramsLift)[idx]? =
        some (field.liftN 1 idx) := by
    rw [self.toLayoutWF.specializedFields_liftN henv.ordered levels params
      hparamsLength 1 0, VExpr.liftTelN_getElem?, hfield]
    simp
  have hargsLift :
      view.operationalProjectionArgs levels paramsLift idx (.bvar 0) =
        ((view.operationalProjectionCodes levels params).take idx).map
          fun prior => .app prior.projector.lift (.bvar 0) := by
    unfold operationalProjectionArgs
    rw [← hcodesLift]
    simp [List.map_take, List.map_map,
      VStructureView.ProjectionCode.liftN, Function.comp_def]
  obtain ⟨field', semanticBody, hfield', hconsumeDomain⟩ :=
    VExpr.consumeForalls?_forallN_domain
      (view.specializedFields levels paramsLift) (.sort .zero)
      (view.operationalProjectionArgs levels paramsLift idx (.bvar 0))
      (by simpa [hargsLength] using hidxLift)
  have hfieldEq : field' = field.liftN 1 idx :=
    Option.some.inj
      (hfield'.symm.trans (by simpa [hargsLength] using hfieldLift))
  subst field'
  have hcursorDomain : cursor =
      .forallE
        ((field.liftN 1 idx).instRevAt
          (view.operationalProjectionArgs levels paramsLift idx
            (.bvar 0)) 0)
        semanticBody :=
    Option.some.inj (hconsume.symm.trans hconsumeDomain)
  have hnextEq : next =
      (field.liftN 1 idx).instRevAt
        (view.operationalProjectionArgs levels paramsLift idx (.bvar 0)) 0 := by
    have hforall := hcursor.symm.trans hcursorDomain
    injection hforall
  have hsortEq : nextSort = code.fieldSort := by
    rw [hargsLength] at hnextSort
    have hfieldSort' :
        (view.fieldSorts.map (VLevel.inst levels))[idx]? =
          some fieldSort := by
      simpa [VRestoredBlockStructureView.flatView] using hfieldSort
    have hnextField : nextSort = fieldSort :=
      Option.some.inj (hnextSort.symm.trans hfieldSort')
    exact hnextField.trans hcodeSort.symm
  have htypeBody : env.HasType U
      (view.structureType levels params :: Γ)
      ((field.liftN 1 idx).instRevAt
        (((view.operationalProjectionCodes levels params).take idx).map
          fun prior => .app prior.projector.lift (.bvar 0)) 0)
      (.sort code.fieldSort) := by
    rw [← hargsLift, ← hnextEq, ← hsortEq]
    exact hnextType
  rw [htypeFnShape]
  exact hstruct.lam htypeBody


/-- A sparse canonical prefix determines the exact current-field substitution
needed by the selected minor. -/
theorem ConstructorParameterLayoutWF.operationalConstructorFieldAligned_of_sparse
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.ConstructorParameterLayoutWF env) (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} {levels : List VLevel}
    {params : List VExpr} {limit : Nat}
    (hΓ : OnCtx Γ (env.IsType U))
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (sparseExact : view.OperationalSparseConstructorPrefix env U Γ
      levels params limit) :
    view.OperationalConstructorFieldAligned env U Γ levels params limit := by
  intro field hfield
  let fields := view.specializedFields levels params
  let m := fields.length
  have hidx : limit < fields.length := by
    simpa [fields] using (List.getElem?_eq_some_iff.1 hfield).1
  have hsortTel := self.specializedFields_onSortTel henv.ordered
    levels hlevels hlevelsLength params hparamsLength hparamsSpine
  have hfieldsOnTel : env.OnTel U Γ fields := by
    simpa [fields] using hsortTel.toOnTel
  have hfieldsCtx : OnCtx (fields.reverse ++ Γ) (env.IsType U) :=
    hfieldsOnTel.toOnCtx hΓ
  have hsplit : env.OnTel U Γ (fields.take limit ++ fields.drop limit) := by
    simpa only [List.take_append_drop] using hfieldsOnTel
  obtain ⟨hprefixOriginal, -⟩ := hsplit.of_append
  have hsortTelFull := hsortTel.weakN henv.ordered
    (Ctx.LiftN.zero (n := m) (Γ := Γ) fields.reverse
      (h := by simp [m]))
  have hfullTel : env.OnTel U (fields.reverse ++ Γ)
      (VExpr.liftTelN m fields 0) := by
    simpa [fields] using hsortTelFull.toOnTel
  let source := VExpr.forallN (VExpr.liftTelN m fields 0) (.sort .zero)
  let leftArgs :=
    ((view.operationalProjectionCodes levels params).take limit).map
      fun prior =>
        VExpr.app (prior.projector.liftN m)
          (view.projectionConstructorApp levels params fields)
  let rightArgs := VExpr.bvarRevRange (m - limit) limit
  change ∃ cursor, ∃ sparse : env.SparseSpineWF U
      (fields.reverse ++ Γ) source leftArgs cursor,
    sparse.PointwiseDefEq rightArgs at sparseExact
  obtain ⟨leftCursor, hleftSparse, hpoint⟩ := sparseExact
  have htakeLength : (fields.take limit).length = limit := by
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hidx)]
  have hdropLength : (fields.drop limit).length = m - limit := by
    simp [m]
  have htotalLength :
      (fields.drop limit).length + (fields.take limit).length = m := by
    rw [hdropLength, htakeLength]
    dsimp only [m]
    omega
  let rightCursor :=
    (VExpr.forallN (fields.drop limit) (.sort .zero)).liftN (m - limit)
  have hrightRaw := hprefixOriginal.selfSpineWF
    (B := VExpr.forallN (fields.drop limit) (.sort .zero))
    (Δ := (fields.drop limit).reverse)
  have hright : env.SpineWF U (fields.reverse ++ Γ)
      source rightArgs rightCursor := by
    have hcontext : (fields.drop limit).reverse ++
        (fields.take limit).reverse ++ Γ = fields.reverse ++ Γ := by
      rw [← List.reverse_append, List.take_append_drop]
    rw [hcontext] at hrightRaw
    simp only [List.length_reverse] at hrightRaw
    rw [htotalLength, hdropLength, htakeLength] at hrightRaw
    have hsource :
        (VExpr.forallN (fields.take limit)
          (VExpr.forallN (fields.drop limit) (.sort .zero))).liftN m =
          source := by
      rw [← VExpr.forallN_append, List.take_append_drop,
        VExpr.liftN_forallN]
      rfl
    rw [hsource] at hrightRaw
    simpa [rightArgs, rightCursor] using hrightRaw
  have hsourceType : env.IsType U (fields.reverse ++ Γ) source := by
    apply VEnv.IsType.forallN hfullTel
    exact ⟨_, .sort (by trivial)⟩
  obtain ⟨sourceSort, hsourceHasType⟩ := hsourceType
  have hcursors := hpoint.cursor_defeq henv hfieldsCtx hright
    (show env.IsDefEqU U (fields.reverse ++ Γ) source source from
      ⟨.sort sourceSort, hsourceHasType⟩)
  have hfieldLift :
      (VExpr.liftTelN m fields 0)[limit]? =
        some (field.liftN m limit) := by
    rw [VExpr.liftTelN_getElem?]
    simp [fields, hfield]
  have hleftLength : leftArgs.length = limit := by
    simp [leftArgs, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt (by simpa [fields] using hidx))]
  have hrightLength : rightArgs.length = limit := by
    simp [rightArgs]
  obtain ⟨leftField, leftBody, hleftField, hleftConsume⟩ :=
    VExpr.consumeForalls?_forallN_domain
      (VExpr.liftTelN m fields 0) (.sort .zero) leftArgs
      (by rw [hleftLength, VExpr.liftTelN_length]; exact hidx)
  have hleftFieldEq : leftField = field.liftN m limit :=
    Option.some.inj (hleftField.symm.trans (by
      simpa [hleftLength] using hfieldLift))
  subst leftField
  have hleftCursor : leftCursor =
      .forallE ((field.liftN m limit).instRevAt leftArgs 0) leftBody :=
    Option.some.inj (hleftSparse.consumeForalls_eq.symm.trans hleftConsume)
  obtain ⟨rightField, rightBody, hrightField, hrightConsume⟩ :=
    VExpr.consumeForalls?_forallN_domain
      (VExpr.liftTelN m fields 0) (.sort .zero) rightArgs
      (by rw [hrightLength, VExpr.liftTelN_length]; exact hidx)
  have hrightFieldEq : rightField = field.liftN m limit :=
    Option.some.inj (hrightField.symm.trans (by
      simpa [hrightLength] using hfieldLift))
  subst rightField
  have hrightCursorShape : rightCursor =
      .forallE ((field.liftN m limit).instRevAt rightArgs 0) rightBody :=
    Option.some.inj (hright.toSparse.consumeForalls_eq.symm.trans hrightConsume)
  rw [hleftCursor, hrightCursorShape] at hcursors
  obtain ⟨domainSort, hdomains⟩ :=
    (henv.forallE_inv hfieldsCtx hcursors).1
  have hrightContract :
      (field.liftN m limit).instRev rightArgs =
        field.liftN (m - limit) := by
    simpa [rightArgs] using
      VExpr.instRev_liftN_bvarRevRange field m limit
        (Nat.le_of_lt hidx)
  change env.IsDefEqU U (fields.reverse ++ Γ)
    ((field.liftN m limit).instRev leftArgs)
    (field.liftN (m - limit))
  rw [← hrightContract]
  exact ⟨.sort domainSort, by
    simpa only [VExpr.instRevAt_zero] using hdomains⟩

private theorem LayoutWF.restoredRuleFieldBinders_specializeDirect
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    (fieldSort : VLevel)
    (levels : List VLevel) (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (motives minors : List VExpr)
    (hmotives : motives.length = view.nested.generation.familyCount)
    (hminors : minors.length = view.nested.generation.minorCount) :
    ((((view.nested.generation.ruleFieldBinders
        view.flatView.blockConstructor).map view.nested.restoreRec).map
          (VExpr.instL
            (view.flatView.projectionLevels fieldSort levels))).zipIdx.map
      fun entry => entry.1.instRevAt
        (params ++ motives ++ minors) entry.2) =
      view.specializedFields levels params := by
  let gen := view.nested.generation
  let commonCount := gen.familyCount + gen.minorCount
  let sourceFields := view.fields.map (VExpr.instL gen.sourceLevels)
  let pLevels := view.flatView.projectionLevels fieldSort levels
  let after := motives ++ minors
  have hsource := view.flatView.sourceLevels_projectionLevels fieldSort levels
    (by simpa only [view.flatView_uvars] using hlevelsLength)
  have hsource' : gen.sourceLevels.map (VLevel.inst pLevels) = levels := by
    change gen.sourceLevels.map (VLevel.inst pLevels) = levels at hsource
    exact hsource
  have hafterLength : after.length = commonCount := by
    simp [after, commonCount, gen, hmotives, hminors]
  have hfieldBinders := VExpr.map_liftTelN_instRevAt_append
    (view.fields.map (VExpr.instL levels)) params after 0
  rw [hafterLength] at hfieldBinders
  rw [VExpr.instRevAt_map_instL_zipIdx] at hfieldBinders
  have restored := view.restoreRuleFieldBinders closed
  dsimp only at restored
  rw [restored]
  rw [VExpr.liftTelN_instL]
  have sourceFieldsAt : sourceFields.map (VExpr.instL pLevels) =
      view.fields.map (VExpr.instL levels) := by
    simp only [sourceFields, List.map_map, Function.comp_def,
      VExpr.instL_instL]
    rw [hsource']
  rw [sourceFieldsAt]
  rw [show params ++ motives ++ minors = params ++ after by
    simp [after, List.append_assoc]]
  exact hfieldBinders

private theorem restoredRecType_instL_common
    (view : VRestoredBlockStructureView)
    (family : NormalizedFamily) (levels : List VLevel) :
    (view.nested.restoreRec
      (view.nested.generation.recType family)).instL levels =
      VExpr.forallN
        ((view.nested.generation.ruleCommonBinders.map
          view.nested.restoreRec).map (VExpr.instL levels))
        (VExpr.forallN
          (((view.nested.generation.recIndexBinders family).map
            view.nested.restoreRec).map (VExpr.instL levels))
          (.forallE
            ((view.nested.restoreRec
              (view.nested.generation.recMajorDomain family)).instL levels)
            ((view.nested.restoreRec
              (view.nested.generation.recMotiveResult family)).instL
                levels))) := by
  rw [view.nested.restoreRec_instL]
  rw [view.nested.generation.recType_instL_common]
  unfold NestedBlockChecked.restoreRecAt
  rw [VInductDecl.restoreExpr_forallN,
    VInductDecl.restoreExpr_forallN]
  simp only [VInductDecl.restoreExpr, List.map_map, Function.comp_def]
  congr 1
  · apply List.map_congr_left
    intro binder _
    exact (view.nested.restoreRec_instL binder levels).symm
  · congr 1
    · apply List.map_congr_left
      intro binder _
      exact (view.nested.restoreRec_instL binder levels).symm
    · rw [view.nested.restoreRec_instL,
        view.nested.restoreRec_instL]
      rfl

private theorem restoredRule_type_instL
    (view : VRestoredBlockStructureView) (ruleIndex : Nat)
    (constructor : NormalizedBlockCtor) (levels : List VLevel) :
    (view.nested.restoredRule ruleIndex constructor).type.instL levels =
      VExpr.forallN
        (((view.nested.generation.ruleBinders constructor).map
          view.nested.restoreRec).map (VExpr.instL levels))
        ((view.nested.restoreRec
          (view.nested.generation.ruleResult constructor)).instL levels) := by
  change (view.nested.restoreRec
    (view.nested.generation.rule ruleIndex constructor).type).instL levels = _
  rw [view.nested.generation.rule_type]
  unfold NestedBlockChecked.restoreRec
  rw [
    VInductDecl.restoreExpr_forallN, VExpr.instL_forallN]
  rfl

private theorem restoredRule_lhs_instL
    (view : VRestoredBlockStructureView) (ruleIndex : Nat)
    (constructor : NormalizedBlockCtor) (levels : List VLevel) :
    (view.nested.restoredRule ruleIndex constructor).lhs.instL levels =
      VExpr.lamN
        (((view.nested.generation.ruleBinders constructor).map
          view.nested.restoreRec).map (VExpr.instL levels))
        ((view.nested.restoreRec
          (view.nested.generation.ruleLhsBody constructor)).instL levels) := by
  change (view.nested.restoreRec
    (view.nested.generation.rule ruleIndex constructor).lhs).instL levels = _
  rw [view.nested.generation.rule_lhs]
  unfold NestedBlockChecked.restoreRec
  rw [
    VInductDecl.restoreExpr_lamN, VExpr.instL_lamN]

private theorem restoredRule_rhs_instL
    (view : VRestoredBlockStructureView) (ruleIndex : Nat)
    (constructor : NormalizedBlockCtor) (levels : List VLevel) :
    (view.nested.restoredRule ruleIndex constructor).rhs.instL levels =
      VExpr.lamN
        (((view.nested.generation.ruleBinders constructor).map
          view.nested.restoreRec).map (VExpr.instL levels))
        ((view.nested.restoreRec
          (view.nested.generation.ruleRhsBody ruleIndex constructor)).instL
            levels) := by
  change (view.nested.restoreRec
    (view.nested.generation.rule ruleIndex constructor).rhs).instL levels = _
  rw [view.nested.generation.rule_rhs]
  unfold NestedBlockChecked.restoreRec
  rw [
    VInductDecl.restoreExpr_lamN, VExpr.instL_lamN]

private theorem LayoutWF.restoredRuleBodies_defeq_of_capture
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    {ruleIndex : Nat} {constructor : NormalizedBlockCtor}
    (hentry : view.nested.generation.ruleEntry ruleIndex constructor)
    {levels : List VLevel}
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.nested.generation.recUvars)
    {captures : List VExpr} {B : VExpr}
    (hcaps : env.SpineWF U Γ
      ((view.nested.restoredRule ruleIndex constructor).type.instL levels)
      captures B)
    (hcapturesLength : captures.length =
      (view.nested.generation.ruleBinders constructor).length) :
    env.IsDefEqU U Γ
      (VExpr.instRev
        ((view.nested.restoreRec
          (view.nested.generation.ruleLhsBody constructor)).instL levels)
        captures)
      (VExpr.instRev
        ((view.nested.restoreRec
          (view.nested.generation.ruleRhsBody ruleIndex constructor)).instL
            levels)
        captures) := by
  let rule := view.nested.restoredRule ruleIndex constructor
  have hreg : env.defeqs rule :=
    self.rules _ (view.nested.restoredRule_mem hentry)
  have hruleWF := henv.ordered.defEqWF hreg
  have hlhs : env.HasType U Γ (rule.lhs.instL levels)
      (rule.type.instL levels) :=
    (hruleWF.1.instL hlevels).weak0 henv.ordered
  have hrhs : env.HasType U Γ (rule.rhs.instL levels)
      (rule.type.instL levels) :=
    (hruleWF.2.instL hlevels).weak0 henv.ordered
  rw [show rule.lhs.instL levels = _ from
    restoredRule_lhs_instL view ruleIndex constructor levels] at hlhs
  rw [show rule.rhs.instL levels = _ from
    restoredRule_rhs_instL view ruleIndex constructor levels] at hrhs
  obtain ⟨hlhsTel, lhsType, hlhsBody⟩ :=
    VEnv.HasType.lamN_wf henv.ordered hΓ hlhs
  obtain ⟨hrhsTel, rhsType, hrhsBody⟩ :=
    VEnv.HasType.lamN_wf henv.ordered hΓ hrhs
  have htype := restoredRule_type_instL view ruleIndex constructor levels
  have hcaps' := hcaps
  change env.SpineWF U Γ (rule.type.instL levels) captures B at hcaps'
  rw [htype] at hcaps'
  have hcapturesLength' : captures.length =
      (((view.nested.generation.ruleBinders constructor).map
        view.nested.restoreRec).map (VExpr.instL levels)).length := by
    simpa using hcapturesLength
  have hlhsSpine := hcaps'.retarget hcapturesLength' lhsType
  have hrhsSpine := hcaps'.retarget hcapturesLength' rhsType
  have hcollapseL := VEnv.IsDefEq.appN_lamN henv.ordered
    hlhsTel hlhsBody hlhsSpine hcapturesLength'
  have hcollapseR := VEnv.IsDefEq.appN_lamN henv.ordered
    hrhsTel hrhsBody hrhsSpine hcapturesLength'
  have hregisteredRule : env.IsDefEq U Γ
      (rule.lhs.instL levels) (rule.rhs.instL levels)
      (rule.type.instL levels) :=
    .extra hreg hlevels (by
      change levels.length =
        (view.nested.generation.rule ruleIndex constructor).uvars
      exact hlevelsLength.trans
        (view.nested.generation.rule_uvars ruleIndex constructor).symm)
  have happlied := VEnv.IsDefEq.appN_congr hregisteredRule hcaps
  rw [show rule.lhs.instL levels = _ from
      restoredRule_lhs_instL view ruleIndex constructor levels,
    show rule.rhs.instL levels = _ from
      restoredRule_rhs_instL view ruleIndex constructor levels] at happlied
  exact henv.isDefEqU_trans hΓ ⟨_, hcollapseL.symm⟩
    (henv.isDefEqU_trans hΓ ⟨_, happlied⟩
      ⟨_, hcollapseR⟩)

private theorem LayoutWF.restoredProjectionRuleCaptureSpineLocal
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    {U : Nat} {Γ : List VExpr}
    (fieldSort : VLevel) (levels : List VLevel)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (motives minors : List VExpr)
    (hmotives : motives.length = view.nested.generation.familyCount)
    (hminors : minors.length = view.nested.generation.minorCount)
    {fieldArgs suffix : List VExpr} (hfieldArgsLength :
      fieldArgs.length = (view.specializedFields levels params).length)
    {sourceResult : VExpr}
    (hsource : env.SpineWF U Γ
      ((view.nested.restoreRec
        (view.nested.generation.recType view.selection.family)).instL
          (view.flatView.projectionLevels fieldSort levels))
      ((params ++ motives ++ minors) ++ suffix) sourceResult)
    (hfields : env.SpineWF U Γ
      (VExpr.forallN (view.specializedFields levels params) (.sort .zero))
      fieldArgs (.sort .zero)) :
    ∃ ruleIndex B,
      view.nested.generation.ruleEntry ruleIndex
        view.flatView.blockConstructor ∧
      env.SpineWF U Γ
        ((view.nested.restoredRule ruleIndex
          view.flatView.blockConstructor).type.instL
            (view.flatView.projectionLevels fieldSort levels))
        ((params ++ motives ++ minors) ++ fieldArgs) B := by
  let gen := view.nested.generation
  let c := view.flatView.blockConstructor
  let pLevels := view.flatView.projectionLevels fieldSort levels
  let fields := view.specializedFields levels params
  let m := fields.length
  let commonArgs := params ++ motives ++ minors
  let restoredCommon :=
    (gen.ruleCommonBinders.map view.nested.restoreRec).map
      (VExpr.instL pLevels)
  let restoredRuleFields :=
    ((gen.ruleFieldBinders c).map view.nested.restoreRec).map
      (VExpr.instL pLevels)
  let restoredResult :=
    (view.nested.restoreRec (gen.ruleResult c)).instL pLevels
  let ruleContinuation := VExpr.instRev
    (VExpr.forallN restoredRuleFields restoredResult) commonArgs
  have hdomains := self.restoredRuleFieldBinders_specializeDirect
    closed fieldSort levels hlevelsLength params hparamsLength motives minors
      hmotives hminors
  have htel : VExpr.telN m ruleContinuation = fields := by
    unfold ruleContinuation
    rw [VExpr.instRev_forallN_projection]
    rw [show (restoredRuleFields.zipIdx.map fun entry =>
        entry.1.instRevAt commonArgs entry.2) = fields by
      simpa [restoredRuleFields, commonArgs, fields, gen, c, pLevels]
        using hdomains]
    simpa [m] using VExpr.telN_forallN_length fields
      (restoredResult.instRevAt commonArgs restoredRuleFields.length)
  let residual := VExpr.dropN m ruleContinuation
  have hcontinuation : ruleContinuation =
      VExpr.forallN fields residual := by
    calc
      ruleContinuation = VExpr.forallN (VExpr.telN m ruleContinuation)
          (VExpr.dropN m ruleContinuation) :=
        (VExpr.forallN_telN_dropN m ruleContinuation).symm
      _ = _ := by rw [htel]
  have hfieldsRule : env.SpineWF U Γ ruleContinuation fieldArgs
      (residual.instRev fieldArgs) := by
    have h := hfields.retarget
      (by simpa [fields, m] using hfieldArgsLength) residual
    rw [← hcontinuation] at h
    exact h
  obtain ⟨ruleIndex, hentry⟩ :=
    List.mem_iff_getElem?.1 view.flatView.blockConstructor_mem
  have hidxTel : gen.idxTel view.selection.family = [] := by
    unfold BlockGenerationChecked.idxTel
    have hraw := view.flatView.raw_indices_eq
    change view.selection.family.rawIndices
      view.nested.elim.flat.nparams = [] at hraw
    rw [hraw]
    rfl
  have hindices : gen.recIndexBinders view.selection.family = [] := by
    unfold BlockGenerationChecked.recIndexBinders
    rw [hidxTel]
    rfl
  have hsource' : env.SpineWF U Γ
      (VExpr.forallN restoredCommon
        (.forallE
          ((view.nested.restoreRec
            (gen.recMajorDomain view.selection.family)).instL pLevels)
          ((view.nested.restoreRec
            (gen.recMotiveResult view.selection.family)).instL pLevels)))
      (commonArgs ++ suffix) sourceResult := by
    have h := hsource
    rw [restoredRecType_instL_common] at h
    rw [hindices] at h
    simp only [List.map_nil, VExpr.forallN] at h
    simpa [restoredCommon, commonArgs, gen, pLevels] using h
  have hcommonLength : commonArgs.length = restoredCommon.length := by
    calc
      commonArgs.length =
          view.nparams + gen.familyCount + gen.minorCount := by
        simp [commonArgs, gen, hparamsLength, hmotives, hminors,
          Nat.add_assoc]
      _ = view.flatView.nparams + gen.familyCount + gen.minorCount := by
        rw [view.flatView_nparams]
      _ = gen.ruleCommonBinders.length :=
        gen.ruleCommonBinders_length.symm
      _ = restoredCommon.length := by simp [restoredCommon]
  have hcapture : env.SpineWF U Γ
      (VExpr.forallN (restoredCommon ++ restoredRuleFields) restoredResult)
      (commonArgs ++ fieldArgs) (residual.instRev fieldArgs) :=
    hsource'.prefixAppendForallN hcommonLength hfieldsRule
  have htype :
      (view.nested.restoredRule ruleIndex c).type.instL pLevels =
        VExpr.forallN (restoredCommon ++ restoredRuleFields)
          restoredResult := by
    rw [restoredRule_type_instL]
    rw [gen.ruleBinders_eq_common_append_fields,
      List.map_append, List.map_append]
  refine ⟨ruleIndex, residual.instRev fieldArgs, hentry, ?_⟩
  rw [htype]
  simpa [commonArgs, List.append_assoc] using hcapture


theorem operationalProjectionCodes_get?_projector_recursor_shape
    (view : VRestoredBlockStructureView)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    (levels : List VLevel) (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    {index : Nat} {code : VStructureView.ProjectionCode}
    (found : (view.operationalProjectionCodes levels params)[index]? =
      some code) :
    ∃ flatTemplate fieldSort domain,
      (view.flatProjectionCodeTemplates levels)[index]? =
        some flatTemplate ∧
      code.fieldSort = fieldSort ∧
      code.projector =
        let projectionLevels :=
          view.flatView.projectionLevels fieldSort levels
        let formalParams := VExpr.bvarRevRange 0 view.nparams
        let flatFields :=
          view.flatView.specializedFields levels formalParams
        let flatStructType :=
          view.flatView.structureType levels formalParams
        let paramsMajor := params.map (VExpr.liftN 1)
        let flatParamsMajor := formalParams.map (VExpr.liftN 1)
        let flatAllFieldsMajor := VExpr.liftTelN 1 flatFields 0
        let flatTypeFnMajor := flatTemplate.typeFn.lift
        let majorBinder := VExpr.bvar 0
        let flatDummyType := VBlockStructureView.majorDummyType
          flatTypeFnMajor majorBinder
        let flatDummyValue := VBlockStructureView.majorDummyValue
          flatTypeFnMajor majorBinder
        let flatMotives := view.flatView.projectionMotivesWith levels
          flatParamsMajor flatTypeFnMajor flatDummyType
        let flatMinors := view.nested.generation.flatCtors.map
          fun constructor => view.flatView.projectionMinorWith constructor
            fieldSort levels flatParamsMajor flatAllFieldsMajor flatMotives
              index flatDummyValue
        let restoreSpecialize := fun expression =>
          (view.nested.restoreRecAt projectionLevels expression).instRevAt
            params 1
        let motivesMajor := flatMotives.map restoreSpecialize
        let minorsMajor := flatMinors.map restoreSpecialize
        .lam domain <| VExpr.appN
          (.const view.recursorName projectionLevels)
          (paramsMajor ++ motivesMajor ++ minorsMajor ++ [majorBinder]) := by
  obtain ⟨flatTemplate, fieldSort, flatFound, _, codeSort, _, projectorEq⟩ :=
    view.operationalProjectionCodes_get?_program_shape levels params found
  let projectionLevels := view.flatView.projectionLevels fieldSort levels
  let formalParams := VExpr.bvarRevRange 0 view.nparams
  let flatFields := view.flatView.specializedFields levels formalParams
  let flatStructType := view.flatView.structureType levels formalParams
  let paramsMajor := params.map (VExpr.liftN 1)
  let flatParamsMajor := formalParams.map (VExpr.liftN 1)
  let flatAllFieldsMajor := VExpr.liftTelN 1 flatFields 0
  let flatTypeFnMajor := flatTemplate.typeFn.lift
  let majorBinder := VExpr.bvar 0
  let flatDummyType := VBlockStructureView.majorDummyType
    flatTypeFnMajor majorBinder
  let flatDummyValue := VBlockStructureView.majorDummyValue
    flatTypeFnMajor majorBinder
  let flatMotives := view.flatView.projectionMotivesWith levels
    flatParamsMajor flatTypeFnMajor flatDummyType
  let flatMinors := view.nested.generation.flatCtors.map
    fun constructor => view.flatView.projectionMinorWith constructor
      fieldSort levels flatParamsMajor flatAllFieldsMajor flatMotives index
        flatDummyValue
  let flatArguments := flatParamsMajor ++ flatMotives ++ flatMinors ++
    [majorBinder]
  let restoreSpecialize := fun expression =>
    (view.nested.restoreRecAt projectionLevels expression).instRevAt params 1
  let motivesMajor := flatMotives.map restoreSpecialize
  let minorsMajor := flatMinors.map restoreSpecialize
  let domain := (view.nested.restoreRecAt projectionLevels
    flatStructType).instRevAt params 0
  have recursorInert : RestoreInert
      (view.nested.recEntries.map (·.instL projectionLevels))
      view.nested.recMap (.const view.recursorName projectionLevels) := by
    have base : RestoreInert view.nested.recEntries view.nested.recMap
        (.const view.recursorName projectionLevels) := by
      simpa [VRestoredBlockStructureView.recursorName] using
        view.nested.sourceRecursorName_restoreRecInert
          view.sourceFamily_mem projectionLevels
    exact base.instLEntries projectionLevels
  obtain ⟨recMapMiss, entryMiss, constructorMiss⟩ :=
    recursorInert view.recursorName (by simp [VExpr.hasConst])
  have bodyRestored : view.nested.restoreRecAt projectionLevels
      (VExpr.appN (.const view.recursorName projectionLevels)
        flatArguments) =
      VExpr.appN (.const view.recursorName projectionLevels)
        (flatArguments.map (view.nested.restoreRecAt projectionLevels)) := by
    unfold NestedBlockChecked.restoreRecAt
    exact VInductDecl.restoreExpr_appN_of_head_inert
      recursorInert.restoreExpr_eq (by rfl) recMapMiss entryMiss
        constructorMiss
  have flatParamsRestored :
      flatParamsMajor.map (view.nested.restoreRecAt projectionLevels) =
        flatParamsMajor := by
    unfold flatParamsMajor formalParams
    rw [VExpr.bvarRevRange_liftN_low]
    exact bvarRevRange_restoreExpr_map _ _ _ _
  have paramsSpecialized : flatParamsMajor.map restoreSpecialize =
      paramsMajor := by
    calc
      flatParamsMajor.map restoreSpecialize =
          (flatParamsMajor.map
            (view.nested.restoreRecAt projectionLevels)).map
              (fun expression => expression.instRevAt params 1) := by
        simp [restoreSpecialize, List.map_map, Function.comp_def]
      _ = flatParamsMajor.map
          (fun expression => expression.instRevAt params 1) := by
        rw [flatParamsRestored]
      _ = paramsMajor := by
        rw [show flatParamsMajor = VExpr.bvarRevRange 1 params.length by
          unfold flatParamsMajor formalParams
          rw [VExpr.bvarRevRange_liftN_low, hparamsLength]]
        exact VExpr.map_instRevAt_bvarRevRange params 1
  have argumentsSpecialized :
      flatArguments.map (fun expression =>
        (view.nested.restoreRecAt projectionLevels expression).instRevAt
          params 1) =
        paramsMajor ++ motivesMajor ++ minorsMajor ++ [majorBinder] := by
    simp only [flatArguments, List.map_append, List.map_singleton]
    rw [show flatParamsMajor.map (fun expression =>
        (view.nested.restoreRecAt projectionLevels expression).instRevAt
          params 1) = paramsMajor by
      simpa only [restoreSpecialize] using paramsSpecialized]
    rw [show (view.nested.restoreRecAt projectionLevels majorBinder).instRevAt
        params 1 = majorBinder by
      unfold majorBinder NestedBlockChecked.restoreRecAt
      simp only [VInductDecl.restoreExpr]
      exact VExpr.instRevAt_closedN params (by simp [VExpr.ClosedN])]
  refine ⟨flatTemplate, fieldSort, domain, flatFound, codeSort, ?_⟩
  rw [projectorEq]
  unfold VBlockStructureView.operationalProjector
  change (view.nested.restoreRecAt projectionLevels
    (.lam flatStructType
      (VExpr.appN (.const view.flatView.recursorName projectionLevels)
        flatArguments))).instRevAt params 0 = _
  rw [view.flatView_recursorName]
  change (VExpr.lam
    (view.nested.restoreRecAt projectionLevels flatStructType)
    (view.nested.restoreRecAt projectionLevels
      (VExpr.appN (.const view.recursorName projectionLevels)
        flatArguments))).instRevAt params 0 = _
  rw [bodyRestored, VExpr.instRevAt_lam_projection,
    VExpr.instRevAt_appN_projection]
  have recursorSpecialized :
      (VExpr.const view.recursorName projectionLevels).instRevAt params 1 =
        .const view.recursorName projectionLevels :=
    VExpr.instRevAt_closedN params (by trivial)
  rw [recursorSpecialized]
  have argumentsSpecialized' :
      (flatArguments.map
        (view.nested.restoreRecAt projectionLevels)).map
          (fun expression => expression.instRevAt params 1) =
        paramsMajor ++ motivesMajor ++ minorsMajor ++ [majorBinder] := by
    rw [List.map_map]
    exact argumentsSpecialized
  rw [argumentsSpecialized']

/-- Core restored-projector typing at an explicitly selected recursor
universe.  The public field-sort and small-elimination entry points below
provide the exact restored syntax shape and show that restoration uses the
same recursor level vector retained by the runtime code. -/
private theorem ConstructorParameterLayoutWF.operationalProjector_hasType_of_typeFn_aligned_atSortCore
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.ConstructorParameterLayoutWF env) (henv : env.ConversionRegular)
    (codeNaturality : view.flatView.OperationalCodeNaturality)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    {U : Nat} {context : List VExpr}
    (levels : List VLevel) (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (hcontext : OnCtx context (env.IsType U))
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U context (view.familyType.instL levels)
        params (.sort resultLevel))
    {index : Nat} {code : VStructureView.ProjectionCode}
    {programSort : VLevel}
    (hcode : (view.operationalProjectionCodes levels params)[index]? =
      some code)
    (hprogramSort : programSort.WF U)
    (typeFnType : env.HasType U context code.typeFn
      (.forallE (view.structureType levels params) (.sort programSort)))
    (aligned : view.OperationalConstructorFieldAligned env U context
      levels params index)
    (hmotiveLevel : view.nested.generation.motiveLevel.inst
      (view.flatView.projectionLevels programSort levels) = programSort)
    {flatTemplate : VStructureView.ProjectionCode} {domain : VExpr}
    (flatFound : (view.flatProjectionCodeTemplates levels)[index]? =
      some flatTemplate)
    (projectionLevelsEq :
      view.flatView.projectionLevels programSort levels =
        view.flatView.projectionLevels code.fieldSort levels)
    (projectorShape : code.projector =
      let projectionLevels :=
        view.flatView.projectionLevels programSort levels
      let formalParams := VExpr.bvarRevRange 0 view.nparams
      let flatFields := view.flatView.specializedFields levels formalParams
      let flatStructType := view.flatView.structureType levels formalParams
      let paramsMajor := params.map (VExpr.liftN 1)
      let flatParamsMajor := formalParams.map (VExpr.liftN 1)
      let flatAllFieldsMajor := VExpr.liftTelN 1 flatFields 0
      let flatTypeFnMajor := flatTemplate.typeFn.lift
      let majorBinder := VExpr.bvar 0
      let flatDummyType := VBlockStructureView.majorDummyType
        flatTypeFnMajor majorBinder
      let flatDummyValue := VBlockStructureView.majorDummyValue
        flatTypeFnMajor majorBinder
      let flatMotives := view.flatView.projectionMotivesWith levels
        flatParamsMajor flatTypeFnMajor flatDummyType
      let flatMinors := view.nested.generation.flatCtors.map
        fun constructor => view.flatView.projectionMinorWith constructor
          programSort levels flatParamsMajor flatAllFieldsMajor flatMotives
            index flatDummyValue
      let restoreSpecialize := fun expression =>
        (view.nested.restoreRecAt projectionLevels expression).instRevAt
          params 1
      let motivesMajor := flatMotives.map restoreSpecialize
      let minorsMajor := flatMinors.map restoreSpecialize
      .lam domain <| VExpr.appN
        (.const view.recursorName projectionLevels)
        (paramsMajor ++ motivesMajor ++ minorsMajor ++ [majorBinder])) :
    env.HasType U context code.projector
      (.forallE (view.structureType levels params)
        (.app code.typeFn.lift (.bvar 0))) := by
  obtain ⟨resultLevel, hparamsSpine₀⟩ := hparamsSpine
  have hfamily : env.HasType U context (.const view.name levels)
      (view.familyType.instL levels) := by
    exact self.toFamilyLayoutWF.familyConst_hasType henv.ordered levels
      hlevels hlevelsLength
  have hstructure : env.HasType U context
      (view.structureType levels params) (.sort resultLevel) := by
    simpa [structureType] using hparamsSpine₀.hasType_appN hfamily
  have hmajorContext : OnCtx
      (view.structureType levels params :: context) (env.IsType U) :=
    ⟨hcontext, resultLevel, hstructure⟩
  have hfamilyClosed : (view.familyType.instL levels).ClosedN 0 := by
    simpa using
      (self.toFamilyLayoutWF.familyType_closed henv.ordered).instL

  obtain ⟨flatField, flatFieldFound, flatTypeFnEq⟩ :=
    view.flatView.operationalProjectionCodes_get?_typeFn levels
      (VExpr.bvarRevRange 0 view.nparams) flatFound
  have flatTypeFnLam : ∃ flatDomain flatBody,
      flatTemplate.typeFn = .lam flatDomain flatBody := by
    exact ⟨_, _, flatTypeFnEq⟩
  obtain ⟨selectedTemplate, selectedFound, selectedMotiveEq⟩ :=
    view.operationalProjectionCodes_get?_selectedMotive closed levels params
      hcode
  have selectedTemplateEq : selectedTemplate = flatTemplate :=
    Option.some.inj (selectedFound.symm.trans flatFound)
  subst selectedTemplate
  obtain ⟨dummyTypeTemplate, dummyTypeFound, dummyTypeSort,
      dummyTypeEq⟩ :=
    view.operationalProjectionCodes_get?_dummyType closed levels params hcode
  have dummyTypeTemplateEq : dummyTypeTemplate = flatTemplate :=
    Option.some.inj (dummyTypeFound.symm.trans flatFound)
  subst dummyTypeTemplate
  obtain ⟨dummyValueTemplate, dummyValueFound, dummyValueSort,
      dummyValueEq⟩ :=
    view.operationalProjectionCodes_get?_dummyValue closed levels params hcode
  have dummyValueTemplateEq : dummyValueTemplate = flatTemplate :=
    Option.some.inj (dummyValueFound.symm.trans flatFound)
  subst dummyValueTemplate
  obtain ⟨motiveTemplate, motiveFound, motiveSort,
      selectedMotiveAt⟩ :=
    view.operationalProjectionCodes_get?_selectedMotiveAt closed levels params
      hcode
  have motiveTemplateEq : motiveTemplate = flatTemplate :=
    Option.some.inj (motiveFound.symm.trans flatFound)
  subst motiveTemplate
  rw [dummyTypeSort] at selectedMotiveEq

  let gen := view.nested.generation
  let projectionLevels :=
    view.flatView.projectionLevels programSort levels
  let formalParams := VExpr.bvarRevRange 0 view.nparams
  let flatFields := view.flatView.specializedFields levels formalParams
  let flatStructType := view.flatView.structureType levels formalParams
  let paramsMajor := params.map (VExpr.liftN 1)
  let flatParamsMajor := formalParams.map (VExpr.liftN 1)
  let flatAllFieldsMajor := VExpr.liftTelN 1 flatFields 0
  let flatTypeFnMajor := flatTemplate.typeFn.lift
  let majorBinder := VExpr.bvar 0
  let flatDummyType := VBlockStructureView.majorDummyType
    flatTypeFnMajor majorBinder
  let flatDummyValue := VBlockStructureView.majorDummyValue
    flatTypeFnMajor majorBinder
  let flatMotives := view.flatView.projectionMotivesWith levels
    flatParamsMajor flatTypeFnMajor flatDummyType
  let restoreSpecialize := fun expression =>
    (view.nested.restoreRecAt projectionLevels expression).instRevAt params 1
  let motivesMajor := flatMotives.map restoreSpecialize
  let canonicalFlatMinors := gen.flatCtors.map fun constructor =>
    view.flatView.projectionMinorWith constructor programSort levels
      flatParamsMajor
      (view.flatView.specializedFields levels flatParamsMajor)
      flatMotives index flatDummyValue
  let canonicalMinorsMajor := canonicalFlatMinors.map restoreSpecialize
  let actualFlatMinors := gen.flatCtors.map fun constructor =>
    view.flatView.projectionMinorWith constructor programSort levels
      flatParamsMajor flatAllFieldsMajor flatMotives index flatDummyValue
  let actualMinorsMajor := actualFlatMinors.map restoreSpecialize
  let dummyType := VBlockStructureView.majorDummyType
    code.typeFn.lift majorBinder
  let dummyValue := VBlockStructureView.majorDummyValue
    code.typeFn.lift majorBinder

  have paramsMajorLength : paramsMajor.length = view.nparams := by
    simpa [paramsMajor] using hparamsLength
  have hparamsMajorSpine : env.SpineWF U
      (view.structureType levels params :: context)
      (view.familyType.instL levels) paramsMajor (.sort resultLevel) := by
    have weakened := hparamsSpine₀.weakN henv.ordered
      (Ctx.LiftN.one (A := view.structureType levels params))
    rw [hfamilyClosed.liftN_eq (Nat.zero_le _)] at weakened
    simpa [paramsMajor, VExpr.liftN] using weakened
  have hstructureLift : view.structureType levels paramsMajor =
      (view.structureType levels params).lift := by
    change view.structureType levels
        (params.map fun parameter => parameter.liftN 1 0) =
      (view.structureType levels params).liftN 1 0
    exact (view.structureType_liftN levels params 1 0).symm
  have hmajor : env.HasType U
      (view.structureType levels params :: context) majorBinder
      (view.structureType levels paramsMajor) := by
    rw [hstructureLift]
    exact .bvar .zero
  have htypeFnLift : env.HasType U
      (view.structureType levels params :: context) code.typeFn.lift
      (.forallE (view.structureType levels paramsMajor)
        (.sort programSort)) := by
    have weakened := typeFnType.weakN henv.ordered
      (Ctx.LiftN.one (A := view.structureType levels params))
    simpa [hstructureLift, VExpr.liftN] using weakened
  have hcarrier : env.HasType U
      (view.structureType levels params :: context)
      (.app code.typeFn.lift majorBinder) (.sort programSort) := by
    simpa only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero] using
      htypeFnLift.app hmajor
  have hdummyType : env.HasType U
      (view.structureType levels params :: context) dummyType
      (.sort programSort) := by
    exact VBlockStructureView.majorDummyType_hasType henv.ordered
      hprogramSort hcarrier
  have hdummyValue : env.HasType U
      (view.structureType levels params :: context) dummyValue dummyType := by
    exact VBlockStructureView.majorDummyValue_hasType henv.ordered hcarrier

  have projectionLevelsWF : ∀ level ∈ projectionLevels, level.WF U := by
    change ∀ level ∈
      (match gen.elimination with
      | .large => programSort :: levels
      | .small => levels), level.WF U
    cases gen.elimination with
    | large =>
      intro level member
      have member' : level = programSort ∨ level ∈ levels := by
        simpa using member
      exact member'.elim (fun equal => equal ▸ hprogramSort) (hlevels level)
    | small =>
      intro level member
      exact hlevels level (by simpa using member)
  have projectionLevelsLength : projectionLevels.length = gen.recUvars := by
    simpa [gen, projectionLevels, VRestoredBlockStructureView.flatView] using
      view.flatView.projectionLevels_length programSort levels
        (by simpa only [view.flatView_uvars] using hlevelsLength)
  have recursorTyped : env.HasType U
      (view.structureType levels params :: context)
      (.const view.recursorName projectionLevels)
      ((view.nested.restoreRec
        (gen.recType view.selection.family)).instL projectionLevels) := by
    exact self.restoredRawRecursor_hasType henv.ordered projectionLevelsWF
      projectionLevelsLength
  have paramsCursor := self.restoredRecursorOperationalMotiveCursor
    henv closed programSort hprogramSort levels hlevels hlevelsLength
      paramsMajor paramsMajorLength ⟨resultLevel, hparamsMajorSpine⟩
  dsimp only at paramsCursor
  have afterParams := paramsCursor.hasType_appN recursorTyped
  have afterMotives := self.restoredProjectionMotives_minorCursor henv closed
    programSort levels hlevelsLength params hparamsLength hmajorContext
      flatTemplate (by
        simpa [projectionLevels, projectionLevelsEq] using selectedMotiveEq)
        (by simpa [flatDummyType, flatTypeFnMajor, majorBinder,
          projectionLevels, projectionLevelsEq, dummyType] using dummyTypeEq)
        hmotiveLevel typeFnType
        (by simpa [dummyType] using hdummyType)
        (VExpr.appN (.const view.recursorName projectionLevels) paramsMajor)
        (by simpa [projectionLevels, paramsMajor, gen] using afterParams)
  dsimp only at afterMotives
  have minorTypes := self.restoredProjectionMinors_forall₂_hasType henv
    codeNaturality closed levels hlevels hlevelsLength params hparamsLength
      hcontext ⟨resultLevel, hparamsSpine₀⟩ hmajorContext hcode typeFnType
        aligned flatTemplate flatTypeFnLam
        (by
          simpa [projectionLevels, projectionLevelsEq] using selectedMotiveEq)
        hmotiveLevel dummyType dummyValue
        (by simpa [flatDummyType, flatTypeFnMajor, majorBinder,
          projectionLevels, projectionLevelsEq, dummyType] using dummyTypeEq)
        (by simpa [flatDummyValue, flatTypeFnMajor, majorBinder,
          projectionLevels, projectionLevelsEq, dummyValue] using dummyValueEq)
        (by simpa [dummyType, dummyValue] using hdummyValue)
        (VExpr.appN
          (VExpr.appN (.const view.recursorName projectionLevels) paramsMajor)
          motivesMajor)
        (view.operationalProjectionRecursorMajorTail programSort levels
          paramsMajor motivesMajor)
        (by simpa [projectionLevels, paramsMajor, motivesMajor,
          flatMotives, flatDummyType, flatTypeFnMajor, formalParams,
          flatParamsMajor] using afterMotives)
  dsimp only at minorTypes
  have minorSpine := VEnv.SpineWF.of_forall₂_progressive
    (tail := view.operationalProjectionRecursorMajorTail programSort levels
      paramsMajor motivesMajor) minorTypes
  have afterMinors := minorSpine.hasType_appN afterMotives
  have motivesMajorLength : motivesMajor.length = gen.familyCount := by
    simp [motivesMajor, flatMotives, gen,
      VRestoredBlockStructureView.flatView,
      VBlockStructureView.projectionMotivesWith,
      BlockGenerationChecked.familyCount]
  have canonicalMinorsMajorLength : canonicalMinorsMajor.length =
      gen.minorCount := by
    simp [canonicalMinorsMajor, canonicalFlatMinors, gen,
      BlockGenerationChecked.minorCount]
  have selectedMotiveAt' :
      motivesMajor[view.selection.family.view.ordinal]? =
        some code.typeFn.lift := by
    simpa [motivesMajor, flatMotives, restoreSpecialize, flatDummyType,
      flatTypeFnMajor, majorBinder, flatParamsMajor, formalParams,
      projectionLevels, projectionLevelsEq] using selectedMotiveAt
  have majorTailEq := view.operationalProjectionRecursorMajorTail_instRev
    programSort levels hlevelsLength paramsMajor motivesMajor
      canonicalMinorsMajor paramsMajorLength motivesMajorLength
        canonicalMinorsMajorLength selectedMotiveAt'
  rw [majorTailEq] at afterMinors
  have bodyCanonical := afterMinors.app hmajor
  have bodyCanonical' : env.HasType U
      (view.structureType levels params :: context)
      (VExpr.appN (.const view.recursorName projectionLevels)
        (paramsMajor ++ motivesMajor ++ canonicalMinorsMajor ++
          [majorBinder]))
      (.app code.typeFn.lift majorBinder) := by
    simpa [VExpr.appN_append, VExpr.appN, VExpr.inst, VExpr.inst_lift,
      VExpr.instVar_zero, List.append_assoc, motivesMajor,
      canonicalMinorsMajor, canonicalFlatMinors, restoreSpecialize,
      flatMotives, flatDummyType, flatTypeFnMajor, flatParamsMajor,
      formalParams, gen] using bodyCanonical

  have formalParamsLength : formalParams.length = view.flatView.nparams := by
    simp [formalParams, view.flatView_nparams]
  have flatFieldsLift :
      view.flatView.specializedFields levels flatParamsMajor =
        flatAllFieldsMajor := by
    simpa [flatParamsMajor, flatAllFieldsMajor, flatFields] using
      codeNaturality.fieldsLiftN levels formalParams
        formalParamsLength 1 0
  have actualFlatMinorsEq : actualFlatMinors = canonicalFlatMinors := by
    simp [actualFlatMinors, canonicalFlatMinors, flatFieldsLift]
  have actualMinorsMajorEq : actualMinorsMajor = canonicalMinorsMajor := by
    simp [actualMinorsMajor, canonicalMinorsMajor, actualFlatMinorsEq]
  have bodyActual : env.HasType U
      (view.structureType levels params :: context)
      (VExpr.appN (.const view.recursorName projectionLevels)
        (paramsMajor ++ motivesMajor ++ actualMinorsMajor ++ [majorBinder]))
      (.app code.typeFn.lift majorBinder) := by
    rwa [actualMinorsMajorEq]

  have domainEq : domain = view.structureType levels params := by
    obtain ⟨projectorBody, projectorDomainShape⟩ :=
      view.operationalProjectionCodes_get?_projector_domain levels params
        hparamsLength hcode
    have lambdaEq := projectorShape.symm.trans projectorDomainShape
    injection lambdaEq
  have projectorTyped := hstructure.lam bodyActual
  rw [projectorShape, domainEq]
  simpa [projectionLevels, paramsMajor, motivesMajor, actualMinorsMajor,
    actualFlatMinors, flatAllFieldsMajor, flatFields, flatParamsMajor,
    formalParams, flatTypeFnMajor, majorBinder, flatDummyType,
    flatDummyValue, flatMotives, restoreSpecialize, gen] using projectorTyped

/-- The exact restored mutual-recursor program implements one selected
source projection once the current dependent type function and constructor
field alignment are available.  Motives and minors are consumed from the
live registered recursor cursor, and the flattened declaration-time field
inventory is related to its major-local syntax through the retained producer
closure contract. -/
theorem ConstructorParameterLayoutWF.operationalProjector_hasType_of_typeFn_aligned_atSort
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.ConstructorParameterLayoutWF env) (henv : env.ConversionRegular)
    (codeNaturality : view.flatView.OperationalCodeNaturality)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    {U : Nat} {context : List VExpr}
    (levels : List VLevel) (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (hcontext : OnCtx context (env.IsType U))
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U context (view.familyType.instL levels)
        params (.sort resultLevel))
    {index : Nat} {code : VStructureView.ProjectionCode}
    (hcode : (view.operationalProjectionCodes levels params)[index]? =
      some code)
    (hfieldSort : code.fieldSort.WF U)
    (typeFnType : env.HasType U context code.typeFn
      (.forallE (view.structureType levels params) (.sort code.fieldSort)))
    (aligned : view.OperationalConstructorFieldAligned env U context
      levels params index)
    (hmotiveLevel : view.nested.generation.motiveLevel.inst
      (view.flatView.projectionLevels code.fieldSort levels) =
        code.fieldSort) :
    env.HasType U context code.projector
      (.forallE (view.structureType levels params)
        (.app code.typeFn.lift (.bvar 0))) := by
  obtain ⟨flatTemplate, fieldSort, domain, flatFound, codeSort,
      projectorShape⟩ :=
    view.operationalProjectionCodes_get?_projector_recursor_shape closed
      levels hlevelsLength params hparamsLength hcode
  subst fieldSort
  exact self.operationalProjector_hasType_of_typeFn_aligned_atSortCore henv
    codeNaturality closed levels hlevels hlevelsLength params hparamsLength
      hcontext hparamsSpine hcode hfieldSort typeFnType aligned hmotiveLevel
        flatFound rfl projectorShape

/-- The runtime's two restored sparse traces are sufficient to type the next
operational projector.  The flattened field-telescope algebra is supplied by
the producer-retained naturality contract, so this theorem applies directly
at the public restored endpoint. -/
theorem ConstructorParameterLayoutWF.operationalProjector_hasType_of_runtimePrefix
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.ConstructorParameterLayoutWF env) (henv : env.ConversionRegular)
    (codeNaturality : view.flatView.OperationalCodeNaturality)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    {U : Nat} {context : List VExpr} {levels : List VLevel}
    {params : List VExpr} {index : Nat}
    {code : VStructureView.ProjectionCode}
    (runtime : view.OperationalRuntimePrefix env U context levels params index)
    (hcontext : OnCtx context (env.IsType U))
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U context (view.familyType.instL levels)
        params (.sort resultLevel))
    (hcode : (view.operationalProjectionCodes levels params)[index]? =
      some code)
    (hmotiveLevel : view.nested.generation.motiveLevel.inst
      (view.flatView.projectionLevels code.fieldSort levels) =
        code.fieldSort) :
    env.HasType U context code.projector
      (.forallE (view.structureType levels params)
        (.app code.typeFn.lift (.bvar 0))) := by
  obtain ⟨typePrefix, constructorPrefix⟩ := runtime
  have typeFnType := self.operationalProjectionTypeFn_hasType_of_sparse henv
    codeNaturality closed hcontext hlevels hlevelsLength hparamsLength
      hparamsSpine hcode typePrefix
  have aligned : view.OperationalConstructorFieldAligned env U context
      levels params index :=
    self.operationalConstructorFieldAligned_of_sparse henv hcontext hlevels
      hlevelsLength hparamsLength hparamsSpine constructorPrefix
  obtain ⟨_, fieldSort, _, fieldSortFound, codeSort, _, _⟩ :=
    view.operationalProjectionCodes_get?_program_shape levels params hcode
  have sortTel := self.specializedFields_onSortTel henv.ordered levels hlevels
    hlevelsLength params hparamsLength hparamsSpine
  have fieldSortFound' :
      (view.fieldSorts.map (VLevel.inst levels))[index]? = some fieldSort := by
    simpa [VRestoredBlockStructureView.flatView] using fieldSortFound
  have fieldSortWF : code.fieldSort.WF U := by
    rw [codeSort]
    exact sortTel.sortWF hcontext fieldSortFound'
  exact self.operationalProjector_hasType_of_typeFn_aligned_atSort henv
    codeNaturality closed levels hlevels hlevelsLength params hparamsLength
      hcontext hparamsSpine hcode fieldSortWF typeFnType aligned hmotiveLevel

/-- A runtime-proven restored Prop field is admissible for small elimination
even when its normalized universe is only semantically zero.  The retained
flattened recursor erases that universe from both its level vector and minor
syntax, so the same restored program can be typed at literal level zero. -/
theorem ConstructorParameterLayoutWF.operationalProjector_hasType_of_runtimePrefix_small
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.ConstructorParameterLayoutWF env) (henv : env.ConversionRegular)
    (codeNaturality : view.flatView.OperationalCodeNaturality)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    {U : Nat} {context : List VExpr} {levels : List VLevel}
    {params : List VExpr} {index : Nat}
    {code : VStructureView.ProjectionCode}
    (runtime : view.OperationalRuntimePrefix env U context levels params index)
    (hsmall : view.elimination = .small)
    (hfieldSortZero : code.fieldSort ≈ .zero)
    (hcontext : OnCtx context (env.IsType U))
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U context (view.familyType.instL levels)
        params (.sort resultLevel))
    (hcode : (view.operationalProjectionCodes levels params)[index]? =
      some code) :
    env.HasType U context code.projector
      (.forallE (view.structureType levels params)
        (.app code.typeFn.lift (.bvar 0))) := by
  obtain ⟨resultLevel, hparamsSpine₀⟩ := hparamsSpine
  obtain ⟨typePrefix, constructorPrefix⟩ := runtime
  have typeFnType := self.operationalProjectionTypeFn_hasType_of_sparse henv
    codeNaturality closed hcontext hlevels hlevelsLength hparamsLength
      ⟨resultLevel, hparamsSpine₀⟩ hcode typePrefix
  obtain ⟨_, fieldSort, _, fieldSortFound, codeSort, _, _⟩ :=
    view.operationalProjectionCodes_get?_program_shape levels params hcode
  have sortTel := self.specializedFields_onSortTel henv.ordered levels hlevels
    hlevelsLength params hparamsLength ⟨resultLevel, hparamsSpine₀⟩
  have fieldSortFound' :
      (view.fieldSorts.map (VLevel.inst levels))[index]? = some fieldSort := by
    simpa [VRestoredBlockStructureView.flatView] using fieldSortFound
  have fieldSortWF : code.fieldSort.WF U := by
    rw [codeSort]
    exact sortTel.sortWF hcontext fieldSortFound'
  have familyType : env.HasType U context (.const view.name levels)
      (view.familyType.instL levels) :=
    self.toFamilyLayoutWF.familyConst_hasType henv.ordered levels hlevels
      hlevelsLength
  have structureType : env.HasType U context
      (view.structureType levels params) (.sort resultLevel) := by
    simpa [VRestoredBlockStructureView.structureType] using
      hparamsSpine₀.hasType_appN familyType
  have sortEq : env.IsDefEq U
      (view.structureType levels params :: context)
      (.sort code.fieldSort) (.sort .zero) (.sort (.succ code.fieldSort)) :=
    .sortDF fieldSortWF (by trivial) hfieldSortZero
  have typeEq : env.IsDefEqU U context
      (.forallE (view.structureType levels params) (.sort code.fieldSort))
      (.forallE (view.structureType levels params) (.sort .zero)) :=
    ⟨_, .forallEDF structureType sortEq⟩
  have typeFnZero : env.HasType U context code.typeFn
      (.forallE (view.structureType levels params) (.sort .zero)) :=
    henv.hasType_defeqU_r hcontext typeEq typeFnType
  have aligned : view.OperationalConstructorFieldAligned env U context
      levels params index :=
    self.operationalConstructorFieldAligned_of_sparse henv hcontext hlevels
      hlevelsLength hparamsLength ⟨resultLevel, hparamsSpine₀⟩
        constructorPrefix
  have flatSmall : view.flatView.generation.elimination = .small := hsmall
  have generationSmall : view.nested.generation.elimination = .small := hsmall
  have motiveLevel : view.nested.generation.motiveLevel.inst
      (view.flatView.projectionLevels .zero levels) = .zero := by
    unfold BlockGenerationChecked.motiveLevel ElimMode.motiveLevel
    unfold VBlockStructureView.projectionLevels
    rw [flatSmall, generationSmall]
    rfl
  obtain ⟨flatTemplate, retainedSort, domain, flatFound, retainedSortEq,
      retainedShape⟩ :=
    view.operationalProjectionCodes_get?_projector_recursor_shape closed
      levels hlevelsLength params hparamsLength hcode
  subst retainedSort
  have projectionLevelsEq :
      view.flatView.projectionLevels .zero levels =
        view.flatView.projectionLevels code.fieldSort levels := by
    simp [VBlockStructureView.projectionLevels, flatSmall]
  have projectorShape : code.projector =
      let projectionLevels := view.flatView.projectionLevels .zero levels
      let formalParams := VExpr.bvarRevRange 0 view.nparams
      let flatFields := view.flatView.specializedFields levels formalParams
      let flatStructType := view.flatView.structureType levels formalParams
      let paramsMajor := params.map (VExpr.liftN 1)
      let flatParamsMajor := formalParams.map (VExpr.liftN 1)
      let flatAllFieldsMajor := VExpr.liftTelN 1 flatFields 0
      let flatTypeFnMajor := flatTemplate.typeFn.lift
      let majorBinder := VExpr.bvar 0
      let flatDummyType := VBlockStructureView.majorDummyType
        flatTypeFnMajor majorBinder
      let flatDummyValue := VBlockStructureView.majorDummyValue
        flatTypeFnMajor majorBinder
      let flatMotives := view.flatView.projectionMotivesWith levels
        flatParamsMajor flatTypeFnMajor flatDummyType
      let flatMinors := view.nested.generation.flatCtors.map
        fun constructor => view.flatView.projectionMinorWith constructor
          .zero levels flatParamsMajor flatAllFieldsMajor flatMotives index
            flatDummyValue
      let restoreSpecialize := fun expression =>
        (view.nested.restoreRecAt projectionLevels expression).instRevAt
          params 1
      let motivesMajor := flatMotives.map restoreSpecialize
      let minorsMajor := flatMinors.map restoreSpecialize
      .lam domain <| VExpr.appN
        (.const view.recursorName projectionLevels)
        (paramsMajor ++ motivesMajor ++ minorsMajor ++ [majorBinder]) := by
    simpa [VBlockStructureView.projectionMinorWith,
      VBlockStructureView.identityMinorWith,
      VBlockStructureView.projectionIHTypes,
      VBlockStructureView.generatedProjectionMinorType,
      VBlockStructureView.projectionLevels, flatSmall] using retainedShape
  exact self.operationalProjector_hasType_of_typeFn_aligned_atSortCore henv
    codeNaturality closed levels hlevels hlevelsLength params hparamsLength
      hcontext ⟨resultLevel, hparamsSpine₀⟩ hcode (by trivial) typeFnZero
        aligned motiveLevel flatFound projectionLevelsEq projectorShape


private theorem VExpr.instRevAt_lamN_exists
    (binders : List VExpr) (body : VExpr)
    (arguments : List VExpr) (offset : Nat) :
    ∃ specializedBinders,
      specializedBinders.length = binders.length ∧
      (VExpr.lamN binders body).instRevAt arguments offset =
        VExpr.lamN specializedBinders
          (body.instRevAt arguments (offset + binders.length)) := by
  induction arguments generalizing binders body with
  | nil => exact ⟨binders, rfl, rfl⟩
  | cons argument arguments ih =>
      simp only [VExpr.instRevAt]
      rw [VExpr.instN_lamN_projection]
      obtain ⟨specializedBinders, lengthEq, specialized⟩ :=
        ih (VExpr.instTelN argument binders (offset + arguments.length))
          (body.inst argument
            (offset + arguments.length + binders.length))
      refine ⟨specializedBinders, ?_, ?_⟩
      · exact lengthEq.trans (VExpr.instTelN_length ..)
      · rw [VExpr.instTelN_length] at specialized
        rw [specialized]
        congr 1
        rw [show offset + arguments.length + binders.length =
          offset + binders.length + arguments.length by omega]

private theorem restoredSelectedProjectionMinor_shape
    (view : VRestoredBlockStructureView)
    (levels : List VLevel) (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (fieldSort : VLevel) (index : Nat)
    (hindex : index < (view.specializedFields levels params).length)
    (flatTemplate : VStructureView.ProjectionCode) (major : VExpr) :
    let gen := view.nested.generation
    let constructor := view.flatView.blockConstructor
    let projectionLevels := view.flatView.projectionLevels fieldSort levels
    let formalParams := VExpr.bvarRevRange 0 view.nparams
    let flatFields := view.flatView.specializedFields levels formalParams
    let flatParamsMajor := formalParams.map (VExpr.liftN 1)
    let flatAllFieldsMajor := VExpr.liftTelN 1 flatFields 0
    let flatTypeFnMajor := flatTemplate.typeFn.lift
    let majorBinder := VExpr.bvar 0
    let flatDummyType := VBlockStructureView.majorDummyType
      flatTypeFnMajor majorBinder
    let flatDummyValue := VBlockStructureView.majorDummyValue
      flatTypeFnMajor majorBinder
    let flatMotives := view.flatView.projectionMotivesWith levels
      flatParamsMajor flatTypeFnMajor flatDummyType
    let flatIHs := view.flatView.projectionIHTypes fieldSort levels
      flatParamsMajor flatMotives
    let flatSelectedMinor := view.flatView.projectionMinorWith constructor
      fieldSort levels flatParamsMajor flatAllFieldsMajor flatMotives index
        flatDummyValue
    let selectedMinor := ((view.nested.restoreRecAt projectionLevels
      flatSelectedMinor).instRevAt params 1).inst major 0
    ∃ binders,
      binders.length = (view.specializedFields levels params).length +
        constructor.ctor.view.recursive.length ∧
      selectedMinor = VExpr.lamN binders
        (.bvar (constructor.ctor.view.recursive.length +
          (view.specializedFields levels params).length - 1 - index)) := by
  let gen := view.nested.generation
  let constructor := view.flatView.blockConstructor
  let projectionLevels := view.flatView.projectionLevels fieldSort levels
  let formalParams := VExpr.bvarRevRange 0 view.nparams
  let flatFields := view.flatView.specializedFields levels formalParams
  let flatParamsMajor := formalParams.map (VExpr.liftN 1)
  let flatAllFieldsMajor := VExpr.liftTelN 1 flatFields 0
  let flatTypeFnMajor := flatTemplate.typeFn.lift
  let majorBinder := VExpr.bvar 0
  let flatDummyType := VBlockStructureView.majorDummyType
    flatTypeFnMajor majorBinder
  let flatDummyValue := VBlockStructureView.majorDummyValue
    flatTypeFnMajor majorBinder
  let flatMotives := view.flatView.projectionMotivesWith levels
    flatParamsMajor flatTypeFnMajor flatDummyType
  let flatIHs := view.flatView.projectionIHTypes fieldSort levels
    flatParamsMajor flatMotives
  let flatBinders := flatAllFieldsMajor ++ flatIHs
  let selectorBody := VExpr.bvar
    (flatIHs.length + flatAllFieldsMajor.length - 1 - index)
  let flatSelectedMinor := view.flatView.projectionMinorWith constructor
    fieldSort levels flatParamsMajor flatAllFieldsMajor flatMotives index
      flatDummyValue
  let restoredBinders := flatBinders.map
    (view.nested.restoreRecAt projectionLevels)
  let selectedMinor := ((view.nested.restoreRecAt projectionLevels
    flatSelectedMinor).instRevAt params 1).inst major 0
  have flatMotivesLength : flatMotives.length = gen.familyCount := by
    simpa [flatMotives, gen, VRestoredBlockStructureView.flatView] using
      view.flatView.projectionMotivesWith_length levels flatParamsMajor
        flatTypeFnMajor flatDummyType
  have flatIHsLength : flatIHs.length =
      constructor.ctor.view.recursive.length := by
    have length := view.flatView.projectionIHTypes_length fieldSort levels
      (by simpa only [view.flatView_uvars] using hlevelsLength)
      flatParamsMajor flatMotives (by
        simpa [gen, VRestoredBlockStructureView.flatView] using
          flatMotivesLength)
    simpa [flatIHs, constructor, VBlockStructureView.blockConstructor] using
      length
  have flatFieldsLength : flatAllFieldsMajor.length =
      (view.specializedFields levels params).length := by
    simp [flatAllFieldsMajor, VExpr.liftTelN_length, flatFields,
      VBlockStructureView.specializedFields,
      VRestoredBlockStructureView.specializedFields,
      view.fields_length_eq_flatView]
  have flatBindersLength : flatBinders.length =
      (view.specializedFields levels params).length +
        constructor.ctor.view.recursive.length := by
    simp [flatBinders, flatFieldsLength, flatIHsLength]
  have selectorLt : flatIHs.length + flatAllFieldsMajor.length - 1 -
      index < flatBinders.length := by
    simp only [flatBinders, List.length_append]
    rw [flatFieldsLength]
    omega
  have flatMinorShape : flatSelectedMinor =
      VExpr.lamN flatBinders selectorBody := by
    unfold flatSelectedMinor
    simp only [VBlockStructureView.projectionMinorWith, constructor,
      VBlockStructureView.blockConstructor, ↓reduceIte]
    unfold VExpr.selectFieldMinor selectorBody flatBinders flatIHs
      flatAllFieldsMajor
    exact (VExpr.lamN_append _ _ _).symm
  have restoredMinorShape : view.nested.restoreRecAt projectionLevels
      flatSelectedMinor = VExpr.lamN restoredBinders selectorBody := by
    rw [flatMinorShape]
    unfold NestedBlockChecked.restoreRecAt restoredBinders selectorBody
    rw [VInductDecl.restoreExpr_lamN]
    rfl
  obtain ⟨parameterBinders, parameterBindersLength,
      parameterShape⟩ :=
    VExpr.instRevAt_lamN_exists restoredBinders selectorBody params 1
  have restoredBindersLength : restoredBinders.length =
      flatBinders.length := by simp [restoredBinders]
  have selectorParams : selectorBody.instRevAt params
      (1 + restoredBinders.length) = selectorBody := by
    apply VExpr.instRevAt_closedN
    unfold selectorBody VExpr.ClosedN
    rw [restoredBindersLength]
    omega
  have parameterShape' :
      (VExpr.lamN restoredBinders selectorBody).instRevAt params 1 =
        VExpr.lamN parameterBinders selectorBody := by
    rw [parameterShape, selectorParams]
  let binders := VExpr.instTelN major parameterBinders 0
  have bindersLength : binders.length =
      (view.specializedFields levels params).length +
        constructor.ctor.view.recursive.length := by
    rw [show binders.length = parameterBinders.length by
      simp [binders, VExpr.instTelN_length], parameterBindersLength,
      restoredBindersLength, flatBindersLength]
  refine ⟨binders, bindersLength, ?_⟩
  change ((view.nested.restoreRecAt projectionLevels
    flatSelectedMinor).instRevAt params 1).inst major 0 = _
  rw [restoredMinorShape, parameterShape',
    VExpr.instN_lamN_projection]
  have selectorMajor : selectorBody.inst major parameterBinders.length =
      selectorBody := by
    have selectorClosed : selectorBody.ClosedN parameterBinders.length := by
      unfold selectorBody VExpr.ClosedN
      rw [parameterBindersLength, restoredBindersLength]
      exact selectorLt
    exact selectorClosed.instN_eq (Nat.le_refl _)
  simp only [Nat.zero_add, selectorMajor]
  unfold binders
  congr 2
  unfold selectorBody
  rw [flatIHsLength, flatFieldsLength]

/-- A typed restored operational projector reduces on the selected source
constructor to the exact source field, while executing the flattened recursor
program and its restored registered iota rule. -/
theorem ConstructorParameterLayoutWF.operationalProjector_constructor_exact
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.ConstructorParameterLayoutWF env) (henv : env.ConversionRegular)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    {U : Nat} {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    {levels : List VLevel} (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    {params : List VExpr} (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    {idx : Nat} {code : VStructureView.ProjectionCode}
    (hcode : (view.operationalProjectionCodes levels params)[idx]? =
      some code)
    (hprojector : env.HasType U Γ code.projector
      (.forallE (view.structureType levels params)
        (.app code.typeFn.lift (.bvar 0))))
    {fields : List VExpr} (hfieldsLength :
      fields.length = (view.specializedFields levels params).length)
    {field : VExpr} (hfield : fields[idx]? = some field)
    (hctorType : env.HasType U Γ
      (VExpr.appN (.const view.constructorName levels) (params ++ fields))
      (view.structureType levels params))
    (hfieldsSpine : env.SpineWF U Γ
      (VExpr.forallN (view.specializedFields levels params) (.sort .zero))
      fields (.sort .zero)) :
    env.IsDefEqU U Γ
      (.app code.projector
        (VExpr.appN (.const view.constructorName levels) (params ++ fields)))
      field := by
  obtain ⟨resultLevel, hparamsSpine₀⟩ := hparamsSpine
  obtain ⟨flatTemplate, fieldSort, domain, flatFound, codeSort,
      projectorShape⟩ :=
    operationalProjectionCodes_get?_projector_recursor_shape view
      closed levels hlevelsLength params hparamsLength hcode
  obtain ⟨_, observedFieldSort, _, fieldSortFound, observedCodeSort,
      _, _⟩ :=
    view.operationalProjectionCodes_get?_program_shape levels params hcode
  have observedFieldSortEq : observedFieldSort = fieldSort :=
    observedCodeSort.symm.trans codeSort
  subst observedFieldSort
  have fieldsSortTel := self.specializedFields_onSortTel henv.ordered
    levels hlevels hlevelsLength params hparamsLength
      ⟨resultLevel, hparamsSpine₀⟩
  have fieldSortFound' :
      (view.fieldSorts.map (VLevel.inst levels))[idx]? = some fieldSort := by
    simpa [VRestoredBlockStructureView.flatView, codeSort] using
      fieldSortFound
  have fieldSortWF : fieldSort.WF U :=
    fieldsSortTel.sortWF hΓ fieldSortFound'
  let gen := view.nested.generation
  let constructor := view.flatView.blockConstructor
  let projectionLevels := view.flatView.projectionLevels fieldSort levels
  let formalParams := VExpr.bvarRevRange 0 view.nparams
  let flatFields := view.flatView.specializedFields levels formalParams
  let flatStructType := view.flatView.structureType levels formalParams
  let paramsMajor := params.map (VExpr.liftN 1)
  let flatParamsMajor := formalParams.map (VExpr.liftN 1)
  let flatAllFieldsMajor := VExpr.liftTelN 1 flatFields 0
  let flatTypeFnMajor := flatTemplate.typeFn.lift
  let majorBinder := VExpr.bvar 0
  let flatDummyType := VBlockStructureView.majorDummyType
    flatTypeFnMajor majorBinder
  let flatDummyValue := VBlockStructureView.majorDummyValue
    flatTypeFnMajor majorBinder
  let flatMotives := view.flatView.projectionMotivesWith levels
    flatParamsMajor flatTypeFnMajor flatDummyType
  let flatMinors := gen.flatCtors.map fun candidate =>
    view.flatView.projectionMinorWith candidate fieldSort levels
      flatParamsMajor flatAllFieldsMajor flatMotives idx flatDummyValue
  let restoreSpecialize := fun expression =>
    (view.nested.restoreRecAt projectionLevels expression).instRevAt params 1
  let motivesMajor := flatMotives.map restoreSpecialize
  let minorsMajor := flatMinors.map restoreSpecialize
  let major := VExpr.appN (.const view.constructorName levels)
    (params ++ fields)
  let motives := motivesMajor.map fun expression => expression.inst major 0
  let minors := minorsMajor.map fun expression => expression.inst major 0
  let commonArgs := params ++ motives ++ minors
  have projectionLevelsWF : ∀ level ∈ projectionLevels, level.WF U := by
    change ∀ level ∈
      (match gen.elimination with
      | .large => fieldSort :: levels
      | .small => levels), level.WF U
    cases gen.elimination with
    | large =>
      intro level member
      have member' : level = fieldSort ∨ level ∈ levels := by
        simpa using member
      exact member'.elim (fun equal => equal ▸ fieldSortWF)
        (hlevels level)
    | small =>
      intro level member
      exact hlevels level (by simpa using member)
  have projectionLevelsLength : projectionLevels.length = gen.recUvars := by
    simpa [gen, projectionLevels, VRestoredBlockStructureView.flatView] using
      view.flatView.projectionLevels_length fieldSort levels
        (by simpa only [view.flatView_uvars] using hlevelsLength)
  have flatMotivesLength : flatMotives.length = gen.familyCount := by
    simpa [flatMotives, gen, VRestoredBlockStructureView.flatView] using
      view.flatView.projectionMotivesWith_length levels flatParamsMajor
        flatTypeFnMajor flatDummyType
  have motivesLength : motives.length = gen.familyCount := by
    simp [motives, motivesMajor, flatMotivesLength]
  have minorsLength : minors.length = gen.minorCount := by
    simp [minors, minorsMajor, flatMinors,
      BlockGenerationChecked.minorCount]
  have paramsBeta : paramsMajor.map
      (fun expression => expression.inst major 0) = params := by
    simp [paramsMajor, List.map_map, Function.comp_def, VExpr.inst_liftN]
  rw [projectorShape] at hprojector
  obtain ⟨projectorDomainType, ⟨projectorBodyType, projectorBody⟩⟩ :=
    hprojector.lam_inv henv.ordered hΓ
  obtain ⟨_, projectorDomainTyped⟩ := projectorDomainType
  have inferredLambda := projectorDomainTyped.lam projectorBody
  have functionTypeEq := henv.hasType_uniqU hΓ
    hprojector inferredLambda
  obtain ⟨⟨_, domainEq⟩, _⟩ :=
    henv.forallE_inv hΓ functionTypeEq
  have hctorType' := henv.hasType_defeqU_r hΓ
    ⟨_, domainEq⟩ hctorType
  have projectorBeta := VEnv.IsDefEq.beta projectorBody hctorType'
  have bodyBetaShape :
      (VExpr.appN (.const view.recursorName projectionLevels)
        (paramsMajor ++ motivesMajor ++ minorsMajor ++ [majorBinder])).inst
          major 0 =
        VExpr.appN (.const view.recursorName projectionLevels)
          (commonArgs ++ [major]) := by
    rw [VExpr.instN_appN]
    simp only [VExpr.inst, List.map_append, List.map_singleton,
      VExpr.instVar_zero]
    rw [paramsBeta]
    rw [show majorBinder.inst major 0 = major by
      simp [majorBinder, VExpr.inst, VExpr.instVar]]
  have projectorToRule : env.IsDefEqU U Γ
      (.app code.projector major)
      (VExpr.appN (.const view.recursorName projectionLevels)
      (commonArgs ++ [major])) := by
    refine ⟨projectorBodyType.inst major, ?_⟩
    rw [projectorShape]
    rw [bodyBetaShape] at projectorBeta
    exact projectorBeta
  have commonLength : commonArgs.length =
      view.nested.elim.flat.nparams + gen.familyCount + gen.minorCount := by
    simp only [commonArgs, List.length_append]
    rw [show params.length = view.nested.elim.flat.nparams by
        simpa [view.nested.elim.nparams_eq] using hparamsLength,
      motivesLength, minorsLength]
  let fullArgs := commonArgs ++ [major]
  let recType :=
    (view.nested.restoreRec (gen.recType view.selection.family)).instL
      projectionLevels
  have recursorTyped : env.HasType U Γ
      (.const view.recursorName projectionLevels) recType := by
    exact self.restoredRawRecursor_hasType henv.ordered projectionLevelsWF
      projectionLevelsLength
  have indexTel : gen.idxTel view.selection.family = [] := by
    unfold BlockGenerationChecked.idxTel
    have raw := view.flatView.raw_indices_eq
    change view.selection.family.rawIndices
      view.nested.elim.flat.nparams = [] at raw
    rw [raw]
    rfl
  have indexBinders : gen.recIndexBinders view.selection.family = [] := by
    unfold BlockGenerationChecked.recIndexBinders
    rw [indexTel]
    rfl
  let recCommon := (gen.ruleCommonBinders.map
    view.nested.restoreRec).map (VExpr.instL projectionLevels)
  let recMajor := (view.nested.restoreRec
    (gen.recMajorDomain view.selection.family)).instL projectionLevels
  let recResult := (view.nested.restoreRec
    (gen.recMotiveResult view.selection.family)).instL projectionLevels
  let recBinders := recCommon ++ [recMajor]
  have recTypeShape : recType =
      VExpr.forallN recBinders recResult := by
    unfold recType recBinders recCommon recMajor recResult
    rw [restoredRecType_instL_common, indexBinders]
    simp only [List.map_nil, VExpr.forallN]
    rw [VExpr.forallN_append]
    rfl
  have fullArgsLength : fullArgs.length = recBinders.length := by
    simp [fullArgs, recBinders, recCommon, commonLength,
      gen.ruleCommonBinders_length]
  have recursorTyped' : env.HasType U Γ
      (.const view.recursorName projectionLevels)
      (VExpr.forallN recBinders recResult) := by
    rw [← recTypeShape]
    exact recursorTyped
  obtain ⟨ruleAppType, projectorToRuleRaw⟩ := projectorToRule
  have ruleAppTyped : env.HasType U Γ
      (VExpr.appN (.const view.recursorName projectionLevels) fullArgs)
      ruleAppType := by
    simpa [fullArgs] using projectorToRuleRaw.hasType.2
  have fullSpineRaw := VEnv.HasType.spineWF_of_appN henv
    hΓ recursorTyped' ruleAppTyped fullArgsLength
  have fullSpine : env.SpineWF U Γ recType fullArgs
      (recResult.instRev fullArgs) := by
    rw [recTypeShape]
    exact fullSpineRaw
  obtain ⟨ruleIndex, captureType, ruleEntry, captures⟩ :=
    self.toLayoutWF.restoredProjectionRuleCaptureSpineLocal closed
      fieldSort levels hlevelsLength params hparamsLength motives minors
      motivesLength minorsLength hfieldsLength
      (by simpa [fullArgs, commonArgs, List.append_assoc] using fullSpine)
      hfieldsSpine
  have fieldRuleLength : fields.length = gen.ruleFieldCount constructor := by
    have restoredLengths := congrArg List.length view.restoreRuleRawFields
    have count : gen.ruleFieldCount constructor = view.fields.length := by
      simpa [gen, constructor, BlockGenerationChecked.ruleFieldCount,
        VBlockStructureView.blockConstructor, NormalizedCtor.fieldsR,
        view.fields_length_eq_flatView] using restoredLengths
    rw [hfieldsLength]
    simpa [VRestoredBlockStructureView.specializedFields] using count.symm
  have capturesLength : (commonArgs ++ fields).length =
      (gen.ruleBinders constructor).length := by
    rw [List.length_append, commonLength, fieldRuleLength,
      gen.ruleBinders_length]
  have iotaBodies := self.toLayoutWF.restoredRuleBodies_defeq_of_capture
    henv hΓ ruleEntry projectionLevelsWF projectionLevelsLength captures
      capturesLength
  have resultIndices : constructor.ctor.view.resultIndices = [] := by
    apply List.eq_nil_of_length_eq_zero
    calc
      constructor.ctor.view.resultIndices.length =
          view.flatView.family.view.indices.length := by
        simpa [constructor, VBlockStructureView.blockConstructor] using
          gen.view_resultIndices_length view.flatView.blockConstructor_mem
      _ = 0 := by simp [view.flatView.checked_indices_eq]
  have ruleIndices : gen.ruleIdx constructor = [] := by
    simp [BlockGenerationChecked.ruleIdx,
      NormalizedCtor.resultIndicesR, resultIndices]
  have commonParams : commonArgs.take view.nparams = params := by
    rw [show view.nparams = params.length by exact hparamsLength.symm]
    simp [commonArgs]
  have leftShape :
      VExpr.instRev
        ((view.nested.restoreRec
          (gen.ruleLhsBody constructor)).instL projectionLevels)
        (commonArgs ++ fields) =
      VExpr.appN (.const view.recursorName projectionLevels)
        (commonArgs ++ [major]) := by
    have computed := restoredRuleLhsBody_instL_instRev_common_fields view
      fieldSort levels hlevelsLength ruleIndices commonArgs fields
        commonLength fieldRuleLength
    rw [commonParams] at computed
    simpa [major, projectionLevels] using computed
  have ruleIndexLt : ruleIndex < gen.minorCount := by
    rw [BlockGenerationChecked.minorCount]
    exact (List.getElem?_eq_some_iff.1 ruleEntry).1
  let flatSelectedMinor := view.flatView.projectionMinorWith constructor
    fieldSort levels flatParamsMajor flatAllFieldsMajor flatMotives idx
      flatDummyValue
  let selectedMinor := ((view.nested.restoreRecAt projectionLevels
    flatSelectedMinor).instRevAt params 1).inst major 0
  have selectedMinorAt : minors[ruleIndex]? = some selectedMinor := by
    simp [minors, minorsMajor, flatMinors, restoreSpecialize,
      flatSelectedMinor, selectedMinor, ruleEntry, gen, constructor]
  have commonMinor : commonArgs[view.nested.elim.flat.nparams +
      gen.familyCount + ruleIndex]? = some selectedMinor := by
    have commonShape : commonArgs = (params ++ motives) ++ minors := by
      simp [commonArgs, List.append_assoc]
    rw [commonShape, List.getElem?_append_right (by
      simp only [List.length_append]
      rw [show params.length = view.nested.elim.flat.nparams by
          simpa [view.nested.elim.nparams_eq] using hparamsLength,
        motivesLength]
      omega)]
    have offset : view.nested.elim.flat.nparams + gen.familyCount +
        ruleIndex - (params ++ motives).length = ruleIndex := by
      simp only [List.length_append]
      rw [show params.length = view.nested.elim.flat.nparams by
          simpa [view.nested.elim.nparams_eq] using hparamsLength,
        motivesLength]
      omega
    rw [offset]
    exact selectedMinorAt
  let recursiveArgs := constructor.ctor.recArgsR
    view.nested.elim.flat.uvars gen.elimination
  let ihs := recursiveArgs.map fun recursive =>
    BlockGenerationChecked.blockRuleCall
      (gen.familyCount + gen.minorCount) (gen.ruleFieldCount constructor)
      (gen.recBase (gen.ruleFieldCount constructor) recursive.targetType)
        recursive
  let restoredIHs := ihs.map view.nested.restoreRec
  let capturedIHs := restoredIHs.map fun expression =>
    VExpr.instRev (expression.instL projectionLevels)
      (commonArgs ++ fields)
  have rightShape :
      VExpr.instRev
        ((view.nested.restoreRec
          (gen.ruleRhsBody ruleIndex constructor)).instL projectionLevels)
        (commonArgs ++ fields) =
      VExpr.appN selectedMinor (fields ++ capturedIHs) := by
    simpa [recursiveArgs, ihs, restoredIHs, capturedIHs,
      Function.comp_def] using
      restoredRuleRhsBody_instL_instRev_common_fields view ruleIndex
        constructor projectionLevels commonArgs fields commonLength
          fieldRuleLength commonMinor ruleIndexLt
  rw [leftShape, rightShape] at iotaBodies
  have fieldIndexLt : idx <
      (view.specializedFields levels params).length := by
    rw [← hfieldsLength]
    exact (List.getElem?_eq_some_iff.1 hfield).1
  let selectorBody := VExpr.bvar
    (constructor.ctor.view.recursive.length +
      (view.specializedFields levels params).length - 1 - idx)
  obtain ⟨selectorBinders, selectorBindersLength,
      selectedMinorShapeRaw⟩ :=
    restoredSelectedProjectionMinor_shape view levels hlevelsLength
      params hparamsLength fieldSort idx fieldIndexLt flatTemplate major
  have selectedMinorShape : selectedMinor =
      VExpr.lamN selectorBinders selectorBody := by
    simpa [gen, constructor, projectionLevels, formalParams, flatFields,
      flatParamsMajor, flatAllFieldsMajor, flatTypeFnMajor, majorBinder,
      flatDummyType, flatDummyValue, flatMotives, flatSelectedMinor,
      selectedMinor, selectorBody] using selectedMinorShapeRaw
  have selectedMinorMem : selectedMinor ∈ commonArgs ++ fields :=
    List.mem_append_left fields (List.mem_of_getElem? commonMinor)
  have selectedMinorMem' : selectedMinor ∈
      params ++ motives ++ minors ++ fields := by
    simpa [commonArgs, List.append_assoc] using selectedMinorMem
  obtain ⟨_, selectedMinorType⟩ :=
    VEnv.SpineWF.arg_hasType captures selectedMinorMem'
  rw [selectedMinorShape] at selectedMinorType
  obtain ⟨selectorTel, selectorResultType, selectorBodyTyped⟩ :=
    VEnv.HasType.lamN_wf henv.ordered hΓ selectedMinorType
  have iotaBodies' := iotaBodies
  obtain ⟨_, iotaTyped⟩ := iotaBodies'
  have selectedAppType := iotaTyped.hasType.2
  rw [selectedMinorShape] at selectedAppType
  let allArgs := fields ++ capturedIHs
  change env.HasType U Γ
      (VExpr.appN (VExpr.lamN selectorBinders selectorBody) allArgs) _
      at selectedAppType
  have capturedIHsLength : capturedIHs.length =
      constructor.ctor.view.recursive.length := by
    calc
      capturedIHs.length = restoredIHs.length := by simp [capturedIHs]
      _ = ihs.length := by simp [restoredIHs]
      _ = recursiveArgs.length := by simp [ihs]
      _ = constructor.ctor.view.recursive.length := by
        simp [recursiveArgs, NormalizedCtor.recArgsR]
  have allArgsLength : allArgs.length = selectorBinders.length := by
    simp only [allArgs, List.length_append]
    rw [hfieldsLength, capturedIHsLength, selectorBindersLength]
  have selectedMinorSpine := VEnv.HasType.spineWF_of_appN
    henv hΓ
      (VEnv.HasType.lamN selectorTel selectorBodyTyped)
      selectedAppType allArgsLength
  have selectedMinorBetaRaw := VEnv.IsDefEq.appN_lamN henv.ordered
    selectorTel selectorBodyTyped selectedMinorSpine allArgsLength
  have fieldInAllArgs : allArgs[idx]? = some field := by
    rw [show allArgs = fields ++ capturedIHs by rfl,
      List.getElem?_append_left
        ((List.getElem?_eq_some_iff.1 hfield).1), hfield]
  obtain ⟨_, fieldGetAllArgs⟩ :=
    List.getElem?_eq_some_iff.1 fieldInAllArgs
  have selectorBodyLt :
      constructor.ctor.view.recursive.length +
        (view.specializedFields levels params).length - 1 - idx <
          allArgs.length := by
    simp only [allArgs, List.length_append]
    rw [hfieldsLength, capturedIHsLength]
    omega
  have fieldInst : VExpr.instRev selectorBody allArgs = field := by
    unfold selectorBody
    rw [VExpr.instRev_bvar_lt allArgs selectorBodyLt]
    have position : allArgs.length - 1 -
        (constructor.ctor.view.recursive.length +
          (view.specializedFields levels params).length - 1 - idx) =
        idx := by
      simp only [allArgs, List.length_append]
      rw [hfieldsLength, capturedIHsLength]
      omega
    simpa only [position] using fieldGetAllArgs
  change VExpr.instRev selectorBody (fields ++ capturedIHs) = field
    at fieldInst
  have selectedMinorBeta : env.IsDefEqU U Γ
      (VExpr.appN selectedMinor (fields ++ capturedIHs)) field := by
    refine ⟨VExpr.instRev selectorResultType allArgs, ?_⟩
    rw [selectedMinorShape]
    simpa only [allArgs, fieldInst] using selectedMinorBetaRaw
  exact henv.isDefEqU_trans hΓ
    ⟨ruleAppType, projectorToRuleRaw⟩
    (henv.isDefEqU_trans hΓ iotaBodies
      selectedMinorBeta)


private theorem VExpr.bvarRevRange_getElem?_restored
    (offset count index : Nat) (hindex : index < count) :
    (VExpr.bvarRevRange offset count)[index]? =
      some (.bvar (offset + (count - 1 - index))) := by
  induction count generalizing index with
  | zero => omega
  | succ count ih =>
      cases index with
      | zero => simp [VExpr.bvarRevRange]
      | succ index =>
          simp only [VExpr.bvarRevRange, List.getElem?_cons_succ]
          rw [ih index (by omega)]
          congr 3
          omega

/-- A currently typed operational projector computes exactly on the
canonical selected constructor.  Earlier-prefix construction is deliberately
absent from this statement so runtime sparse-prefix consumers can supply the
program they have just justified. -/
theorem ConstructorParameterLayoutWF.operationalProjector_constructor_exact_of_program
    {view : VRestoredBlockStructureView} {env : VEnv}
    (self : view.ConstructorParameterLayoutWF env) (henv : env.ConversionRegular)
    (closed : RestoreEntriesClosed view.nested.recEntries)
    (codeNaturality : view.flatView.OperationalCodeNaturality)
    {idx : Nat}
    {U : Nat} {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    {levels : List VLevel} (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    {params : List VExpr} (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    {code : VStructureView.ProjectionCode}
    (hcode : (view.operationalProjectionCodes levels params)[idx]? =
      some code)
    (hprojector : env.HasType U Γ code.projector
      (.forallE (view.structureType levels params)
        (.app code.typeFn.lift (.bvar 0)))) :
    let fields := view.specializedFields levels params
    env.IsDefEqU U (fields.reverse ++ Γ)
      (.app (code.projector.liftN fields.length)
        (view.projectionConstructorApp levels params fields))
      (.bvar (fields.length - 1 - idx)) := by
  obtain ⟨resultLevel, hparamsSpine₀⟩ := hparamsSpine
  let fields := view.specializedFields levels params
  let m := fields.length
  let fieldArgs := VExpr.bvarRevRange 0 m
  have hidx : idx < m := by
    have h := (List.getElem?_eq_some_iff.1 hcode).1
    simpa [m, fields] using h
  have hsortTel := self.specializedFields_onSortTel henv.ordered
    levels hlevels hlevelsLength params hparamsLength
      ⟨resultLevel, hparamsSpine₀⟩
  have hfieldsOnTel : env.OnTel U Γ fields := by
    simpa [fields] using hsortTel.toOnTel
  have hfieldsCtx : OnCtx (fields.reverse ++ Γ) (env.IsType U) :=
    hfieldsOnTel.toOnCtx hΓ
  have hconstructorPrefix := self.constructorPrefix_hasType henv closed
    levels hlevels hlevelsLength params hparamsLength
      ⟨resultLevel, hparamsSpine₀⟩
  have hconstructorPrefixWeak := hconstructorPrefix.weakN henv.ordered
    (Ctx.LiftN.zero (n := m) (Γ := Γ) fields.reverse
      (h := by simp [m]))
  have hconstructorPrefixSelf : env.HasType U
      (([] : List VExpr) ++ fields.reverse ++ Γ)
      ((VExpr.appN (.const view.constructorName levels) params).liftN m)
      ((VExpr.forallN fields
        ((view.structureType levels params).liftN m)).liftN
          (([] : List VExpr).length + fields.length)) := by
    simpa [fields, m] using hconstructorPrefixWeak
  have hmajor₀ := VEnv.HasType.appN_selfSpine
    (env := env) (U := U) (As := fields)
    (B := (view.structureType levels params).liftN m)
    (Δ := []) (Γ := Γ)
    (f := (VExpr.appN (.const view.constructorName levels) params).liftN m)
    hconstructorPrefixSelf
  have hmajor : env.HasType U (fields.reverse ++ Γ)
      (view.projectionConstructorApp levels params fields)
      ((view.structureType levels params).liftN m) := by
    simpa [fields, m, projectionConstructorApp,
      VExpr.liftN, VExpr.liftN_appN, VExpr.appN_append, List.map_map,
      Function.comp_def] using hmajor₀
  let paramsLift := params.map (VExpr.liftN m)
  have hparamsLengthLift : paramsLift.length = view.nparams := by
    simpa [paramsLift] using hparamsLength
  have hfamilyClosed : (view.familyType.instL levels).ClosedN 0 := by
    simpa using (self.familyType_closed henv.ordered).instL
  have hparamsSpineLift : env.SpineWF U (fields.reverse ++ Γ)
      (view.familyType.instL levels) paramsLift (.sort resultLevel) := by
    have h := hparamsSpine₀.weakN henv.ordered
      (Ctx.LiftN.zero (n := m) (Γ := Γ) fields.reverse
        (h := by simp [m]))
    rw [hfamilyClosed.liftN_eq (Nat.zero_le _)] at h
    simpa [paramsLift, m, VExpr.liftN] using h
  have hstructLift : view.structureType levels paramsLift =
      (view.structureType levels params).liftN m := by
    simp [paramsLift]
  have hmajorLift : env.HasType U (fields.reverse ++ Γ)
      (view.projectionConstructorApp levels params fields)
      (view.structureType levels paramsLift) := by
    rwa [hstructLift]
  have hcodesLift := view.operationalProjectionCodes_liftN codeNaturality closed
    levels params hparamsLength m 0
  have hcodeLift :
      (view.operationalProjectionCodes levels paramsLift)[idx]? =
        some (code.liftN m 0) := by
    rw [← hcodesLift, List.getElem?_map, hcode]
    rfl
  have hspecializedLift : view.specializedFields levels paramsLift =
      VExpr.liftTelN m fields 0 := by
    simpa [paramsLift, fields] using
      self.toLayoutWF.specializedFields_liftN henv.ordered levels params
        hparamsLength m 0
  have hfieldBase := hfieldsOnTel.selfSpineWF
    (B := .sort .zero) (Δ := ([] : List VExpr))
  have hfieldsSpine : env.SpineWF U (fields.reverse ++ Γ)
      (VExpr.forallN (view.specializedFields levels paramsLift)
        (.sort .zero)) fieldArgs (.sort .zero) := by
    rw [hspecializedLift]
    simpa [m, fieldArgs, VExpr.liftN_forallN, VExpr.liftN]
      using hfieldBase
  have hfieldArg : fieldArgs[idx]? =
      some (.bvar (m - 1 - idx)) := by
    simpa [fieldArgs] using
      VExpr.bvarRevRange_getElem?_restored 0 m idx hidx
  have hctorLift : env.HasType U (fields.reverse ++ Γ)
      (VExpr.appN (.const view.constructorName levels)
        (paramsLift ++ fieldArgs))
      (view.structureType levels paramsLift) := by
    simpa [projectionConstructorApp, paramsLift, fieldArgs, m]
      using hmajorLift
  have hprojectorWeak := hprojector.weakN henv.ordered
    (Ctx.LiftN.zero (n := m) (Γ := Γ) fields.reverse
      (h := by simp [m]))
  have hprojectorLift : env.HasType U (fields.reverse ++ Γ)
      (code.liftN m 0).projector
      (.forallE (view.structureType levels paramsLift)
        (.app (code.liftN m 0).typeFn.lift (.bvar 0))) := by
    simpa [VStructureView.ProjectionCode.liftN, hstructLift,
      VExpr.liftN, VExpr.liftN_lift_projection] using hprojectorWeak
  have hiota := self.operationalProjector_constructor_exact henv closed hfieldsCtx
    hlevels hlevelsLength hparamsLengthLift
    ⟨resultLevel, hparamsSpineLift⟩ hcodeLift hprojectorLift
    (by rw [hspecializedLift, VExpr.liftTelN_length]
        simp [fieldArgs, m])
    hfieldArg hctorLift hfieldsSpine
  simpa [fields, m, fieldArgs, paramsLift,
    VStructureView.ProjectionCode.liftN, projectionConstructorApp]
    using hiota


/-! ## Restored projection semantics -/

/-- Environment-indexed semantics for a projector whose public constructor
is restored source syntax while its code inventory comes from the paired
flattened generation.  The two producer-owned syntactic facts are retained
explicitly because neither can be reconstructed from final registrations. -/
structure TrProj (env : VEnv) (U : Nat) (Γ : List VExpr)
    (view : VRestoredBlockStructureView) (levels : List VLevel)
    (params : List VExpr) (idx : Nat) (major result : VExpr) : Prop where
  viewWF : view.FamilyLayoutWF env
  parameterLayout : view.ConstructorParameterLayoutWF env
  codeNaturality : view.flatView.OperationalCodeNaturality
  recEntriesClosed :
    VInductDecl.RestoreEntriesClosed view.nested.recEntries
  levelsWF : ∀ level ∈ levels, level.WF U
  levels_length : levels.length = view.uvars
  params_length : params.length = view.nparams
  paramsSpine : ∃ resultLevel,
    env.SpineWF U Γ (view.familyType.instL levels)
      params (.sort resultLevel)
  majorType : env.HasType U Γ major (view.structureType levels params)
  program : ∃ code : VStructureView.ProjectionCode,
    (view.operationalProjectionCodes levels params)[idx]? = some code ∧
      result = .app code.projector major ∧
      env.HasType U Γ code.projector
        (.forallE (view.structureType levels params)
          (.app code.typeFn.lift (.bvar 0)))

/-- The restored-backend output of registered constructor-head inversion.
It contains only the canonical constructor spine and its typing; the actual
iota equation is still proved by the restored operational projector. -/
structure ProjectionConstructorAlignment (env : VEnv) (U : Nat)
    (Γ : List VExpr) (view : VRestoredBlockStructureView)
    (levels : List VLevel) (params : List VExpr) (idx : Nat)
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
  major_eq : env.IsDefEqU U Γ runtimeMajor
    (VExpr.appN (.const view.constructorName levels) (params ++ fields))
  field_eq : env.IsDefEqU U Γ runtimeField field

/-- Consume restored registered-head alignment with the operational iota
theorem.  Inversion supplies syntax and typing only; the restored generated
recursor remains the owner of the computation equation. -/
theorem TrProj.projector_constructor_aligned
    (self : TrProj env U Γ view levels params idx major result)
    (henv : env.ConversionRegular) (hΓ : OnCtx Γ (env.IsType U))
    {code : VStructureView.ProjectionCode}
    (hcode : (view.operationalProjectionCodes levels params)[idx]? =
      some code)
    (hprojector : env.HasType U Γ code.projector
      (.forallE (view.structureType levels params)
        (.app code.typeFn.lift (.bvar 0))))
    {runtimeMajor runtimeField : VExpr}
    {runtimeConstructorName : Name}
    (alignment : ProjectionConstructorAlignment env U Γ view levels params
      idx code runtimeConstructorName runtimeMajor runtimeField) :
    env.IsDefEqU U Γ (.app code.projector runtimeMajor) runtimeField := by
  have hmajorEq :=
    (henv.isDefEqU_of_l hΓ alignment.major_eq.symm
      alignment.constructorType).symm
  have hmajorCongr : env.IsDefEqU U Γ
      (.app code.projector runtimeMajor)
      (.app code.projector
        (VExpr.appN (.const view.constructorName levels)
          (params ++ alignment.fields))) :=
    ⟨_, hprojector.appDF hmajorEq⟩
  have hiota := self.parameterLayout.operationalProjector_constructor_exact
    henv self.recEntriesClosed hΓ self.levelsWF self.levels_length
    self.params_length self.paramsSpine hcode hprojector
    alignment.fields_length alignment.field_get alignment.constructorType
    alignment.fieldsSpine
  exact henv.isDefEqU_trans hΓ hmajorCongr
    (henv.isDefEqU_trans hΓ hiota alignment.field_eq.symm)

theorem TrProj.result_eq
    (self : TrProj env U Γ view levels params idx major result)
    (other : TrProj env U Γ view levels params idx major result') :
    result = result' := by
  obtain ⟨code, hcode, hresult, _⟩ := self.program
  obtain ⟨otherCode, hotherCode, hotherResult, _⟩ := other.program
  have codeEq : code = otherCode :=
    Option.some.inj (hcode.symm.trans hotherCode)
  subst otherCode
  exact hresult.trans hotherResult.symm

theorem TrProj.mono {env env' : VEnv} (henv : env ≤ env')
    (self : TrProj env U Γ view levels params idx major result) :
    TrProj env' U Γ view levels params idx major result where
  viewWF := self.viewWF.mono henv
  parameterLayout := self.parameterLayout.mono henv
  codeNaturality := self.codeNaturality
  recEntriesClosed := self.recEntriesClosed
  levelsWF := self.levelsWF
  levels_length := self.levels_length
  params_length := self.params_length
  paramsSpine := self.paramsSpine.imp fun _ spine => spine.mono henv
  majorType := self.majorType.mono henv
  program := self.program.imp fun _ ⟨found, resultEq, typed⟩ =>
    ⟨found, resultEq, typed.mono henv⟩

theorem TrProj.weakN (henv : env.Ordered)
    (W : Ctx.LiftN count cutoff Γ Γ')
    (self : TrProj env U Γ view levels params idx major result) :
    TrProj env U Γ' view levels
      (params.map fun param => param.liftN count cutoff) idx
      (major.liftN count cutoff) (result.liftN count cutoff) := by
  refine {
    viewWF := self.viewWF
    parameterLayout := self.parameterLayout
    codeNaturality := self.codeNaturality
    recEntriesClosed := self.recEntriesClosed
    levelsWF := self.levelsWF
    levels_length := self.levels_length
    params_length := by simpa using self.params_length
    paramsSpine := ?_
    majorType := by simpa using self.majorType.weakN henv W
    program := ?_ }
  · have familyClosed : (view.familyType.instL levels).ClosedN 0 := by
      simpa using (self.viewWF.familyType_closed henv).instL
    obtain ⟨resultLevel, spine⟩ := self.paramsSpine
    refine ⟨resultLevel, ?_⟩
    have lifted := spine.weakN henv W
    rw [familyClosed.liftN_eq (Nat.zero_le _)] at lifted
    simpa [VExpr.liftN] using lifted
  · obtain ⟨code, found, rfl, typed⟩ := self.program
    refine ⟨code.liftN count cutoff, ?_, rfl, ?_⟩
    rw [← view.operationalProjectionCodes_liftN self.codeNaturality
      self.recEntriesClosed levels params self.params_length count cutoff]
    simp only [List.getElem?_map, found, Option.map_some]
    simpa [VStructureView.ProjectionCode.liftN, VExpr.liftN,
      VExpr.liftN_lift_projection] using typed.weakN henv W

theorem TrProj.weak' (henv : env.Ordered)
    (W : Ctx.Lift' lift Γ Γ')
    (self : TrProj env U Γ view levels params idx major result) :
    TrProj env U Γ' view levels
      (params.map fun param => param.lift' lift) idx
      (major.lift' lift) (result.lift' lift) := by
  generalize depthEq : lift.depth = depth
  induction depth generalizing lift Γ' with
  | zero =>
      have contextEq := W.depth_zero depthEq
      subst Γ'
      simpa [VExpr.lift'_depth_zero (l := lift) depthEq] using self
  | succ depth ih =>
      obtain ⟨tail, cutoff, rfl, rfl⟩ := Lift.depth_succ depthEq
      obtain ⟨Γ₁, W₁, W₂⟩ := W.of_cons_skip
      have lifted := (ih W₁ Lift.depth_consN).weakN henv W₂
      rw [Lift.consN_skip_eq]
      have liftEq : ∀ expression : VExpr,
          expression.lift' ((tail.consN cutoff).comp
              (Lift.refl.skip.consN cutoff)) =
            (expression.lift' (tail.consN cutoff)).liftN 1 cutoff := by
        intro expression
        rw [VExpr.lift'_comp, ← Lift.skipN_one,
          VExpr.lift'_consN_skipN]
      have paramsEq :
          params.map (fun param => param.lift' ((tail.consN cutoff).comp
              (Lift.refl.skip.consN cutoff))) =
            (params.map fun param => param.lift' (tail.consN cutoff)).map
              (fun param => param.liftN 1 cutoff) := by
        rw [List.map_map]
        exact List.map_congr_left fun param _ => liftEq param
      rw [paramsEq, liftEq major, liftEq result]
      exact lifted

theorem TrProj.instN (henv : env.Ordered)
    (W : Ctx.InstN Γ₀ argument domain cutoff Γ₁ Γ)
    (argumentType : env.HasType U Γ₀ argument domain)
    (self : TrProj env U Γ₁ view levels params idx major result) :
    TrProj env U Γ view levels
      (params.map fun param => param.inst argument cutoff) idx
      (major.inst argument cutoff) (result.inst argument cutoff) := by
  refine {
    viewWF := self.viewWF
    parameterLayout := self.parameterLayout
    codeNaturality := self.codeNaturality
    recEntriesClosed := self.recEntriesClosed
    levelsWF := self.levelsWF
    levels_length := self.levels_length
    params_length := by simpa using self.params_length
    paramsSpine := ?_
    majorType := by simpa using self.majorType.instN henv W argumentType
    program := ?_ }
  · have familyClosed : (view.familyType.instL levels).ClosedN 0 := by
      simpa using (self.viewWF.familyType_closed henv).instL
    obtain ⟨resultLevel, spine⟩ := self.paramsSpine
    refine ⟨resultLevel, ?_⟩
    have instantiated := spine.instNProjection henv W argumentType
    rw [familyClosed.instN_eq (Nat.zero_le _)] at instantiated
    simpa [VExpr.inst] using instantiated
  · obtain ⟨code, found, rfl, typed⟩ := self.program
    refine ⟨code.instN argument cutoff, ?_, rfl, ?_⟩
    rw [← view.operationalProjectionCodes_instN self.codeNaturality
      self.recEntriesClosed levels params self.params_length argument cutoff]
    simp only [List.getElem?_map, found, Option.map_some]
    simpa [VStructureView.ProjectionCode.instN, VExpr.inst,
      ← VExpr.lift_instN_lo] using typed.instN henv W argumentType

theorem TrProj.defeqDFC (henv : env.Ordered)
    (contexts : env.IsDefEqCtx U Γ₀ Γ₁ Γ₂)
    (majorType' : env.HasType U Γ₂ major'
      (view.structureType levels params))
    (self : TrProj env U Γ₁ view levels params idx major result) :
    ∃ result', TrProj env U Γ₂ view levels params idx major' result' := by
  obtain ⟨code, found, _, typed⟩ := self.program
  refine ⟨.app code.projector major', {
    viewWF := self.viewWF
    parameterLayout := self.parameterLayout
    codeNaturality := self.codeNaturality
    recEntriesClosed := self.recEntriesClosed
    levelsWF := self.levelsWF
    levels_length := self.levels_length
    params_length := self.params_length
    paramsSpine := self.paramsSpine.imp fun _ spine =>
      spine.defeqDFC henv contexts
    majorType := majorType'
    program := ⟨code, found, rfl, typed.defeqDFC henv contexts⟩ }⟩

theorem TrProj.instL {extra : List VLevel}
    (extraWF : ∀ level ∈ extra, level.WF U')
    (self : TrProj env U Γ view levels params idx major result) :
    TrProj env U' (Γ.map (VExpr.instL extra)) view
      (levels.map (VLevel.inst extra))
      (params.map (VExpr.instL extra)) idx
      (major.instL extra) (result.instL extra) := by
  refine {
    viewWF := self.viewWF
    parameterLayout := self.parameterLayout
    codeNaturality := self.codeNaturality
    recEntriesClosed := self.recEntriesClosed
    levelsWF := ?_
    levels_length := by simpa using self.levels_length
    params_length := by simpa using self.params_length
    paramsSpine := ?_
    majorType := by simpa using self.majorType.instL extraWF
    program := ?_ }
  · intro level member
    obtain ⟨sourceLevel, sourceMember, rfl⟩ := List.mem_map.1 member
    exact VLevel.WF.inst extraWF
  · obtain ⟨resultLevel, spine⟩ := self.paramsSpine
    refine ⟨resultLevel.inst extra, ?_⟩
    simpa [VExpr.instL, VExpr.instL_instL] using spine.instL extraWF
  · obtain ⟨code, found, rfl, typed⟩ := self.program
    refine ⟨code.instL extra, ?_, rfl, ?_⟩
    · rw [← operationalProjectionCodes_instL]
      simp only [List.getElem?_map, found, Option.map_some]
    · simpa [VStructureView.ProjectionCode.instL, VExpr.instL,
        VExpr.instL_liftN] using typed.instL extraWF

end VRestoredBlockStructureView

namespace VInductDecl.NestedBlockCertificate

variable {source : VInductDecl} {before after : VEnv}

/-- The completed nested transaction also closes the declaration-universe
restoration inventory used by source family and constructor syntax. -/
theorem declEntriesClosed
    (certificate : NestedBlockCertificate source before after)
    (targetsWF : NestedTargetsWF before
      certificate.nested.elim.targets) :
    RestoreEntriesClosed certificate.nested.declEntries := by
  have sourceClosed : ∀ family ∈ source.types,
      family.NestedMetadataClosed := by
    intro family familyMember
    refine ⟨?_, ?_⟩
    · simpa using certificate.afterWF.ordered.closedC
        (certificate.familyLookup familyMember)
    · intro constructor constructorMember
      simpa using certificate.afterWF.ordered.closedC
        (certificate.constructorLookup familyMember constructorMember)
  exact certificate.nested.declEntriesClosed sourceClosed
    (targetsWF.metadataClosed certificate.beforeWF.ordered)

/-- A completed nested transaction plus well-formedness of the exact target
copies consulted by its retained elimination run supplies the closure
invariant required by operational restoration.  Source metadata closure is
recovered from the transaction's exact final registrations. -/
theorem recEntriesClosed
    (certificate : NestedBlockCertificate source before after)
    (targetsWF : NestedTargetsWF before
      certificate.nested.elim.targets) :
    RestoreEntriesClosed certificate.nested.recEntries := by
  have sourceClosed : ∀ family ∈ source.types,
      family.NestedMetadataClosed := by
    intro family familyMember
    refine ⟨?_, ?_⟩
    · simpa using certificate.afterWF.ordered.closedC
        (certificate.familyLookup familyMember)
    · intro constructor constructorMember
      simpa using certificate.afterWF.ordered.closedC
        (certificate.constructorLookup familyMember constructorMember)
  exact certificate.nested.recEntriesClosed sourceClosed
    (targetsWF.metadataClosed certificate.beforeWF.ordered)

/-- The same producer-owned closure bundle closes every value of the
canonical declaration/recursor interpretation.  This is the closure field
used by semantic transport from the common dependency boundary; no restored
value typing is assumed here. -/
theorem restoreInterp_closed
    (certificate : NestedBlockCertificate source before after)
    (targetsWF : NestedTargetsWF before
      certificate.nested.elim.targets) :
    InterpClosed certificate.nested.restoreInterp := by
  have sourceClosed : ∀ family ∈ source.types,
      family.NestedMetadataClosed := by
    intro family familyMember
    refine ⟨?_, ?_⟩
    · simpa using certificate.afterWF.ordered.closedC
        (certificate.familyLookup familyMember)
    · intro constructor constructorMember
      simpa using certificate.afterWF.ordered.closedC
        (certificate.constructorLookup familyMember constructorMember)
  exact certificate.nested.restoreInterp_closed sourceClosed
    (targetsWF.metadataClosed certificate.beforeWF.ordered)

/-- Declaration-world restoration of the exact flattened constructor chosen
by a source-family selection recovers the literal stored source constructor.
Closure comes from its final registration, while the checked artifact's
restoration-domain gate supplies source-syntax inertness. -/
theorem restoreSelectedConstructor
    (certificate : NestedBlockCertificate source before after)
    {familyIndex : Nat} {sourceFamily : VInductiveType}
    {sourceConstructor : VConstVal}
    (selection : NestedStructureSelection certificate.nested familyIndex
      sourceFamily sourceConstructor) :
    certificate.nested.restoreDeclConstructor selection.flatConstructor =
      sourceConstructor := by
  have familyMember : sourceFamily ∈ source.types :=
    List.mem_iff_getElem?.2 ⟨familyIndex, selection.source_at⟩
  have closed : ∀ constructor ∈ sourceFamily.ctors,
      constructor.type.ClosedN := by
    intro constructor constructorMember
    simpa using certificate.afterWF.ordered.closedC
      (certificate.constructorLookup familyMember constructorMember)
  have inert : ∀ constructor ∈ sourceFamily.ctors,
      RestoreInert certificate.nested.declEntries
        certificate.nested.recMap constructor.type := by
    intro constructor constructorMember
    exact certificate.nested.sourceConstructor_restoreInert
      familyMember constructorMember
  have restored := certificate.nested.restoreDeclConstructorsAt
    selection.source_at selection.flat_at closed inert
  rw [selection.flat_constructors_eq,
    selection.source_constructors_eq] at restored
  have selected :
      certificate.nested.restoreDeclConstructor selection.flatConstructor =
        sourceConstructor ∧ True := by
    simpa only [List.map_cons, List.map_nil, List.cons.injEq] using restored
  exact selected.1

/-- Expression-level form of `restoreSelectedConstructor`: the exact
flattened constructor telescope restores literally to the selected source
telescope. -/
theorem restoreSelectedConstructorType
    (certificate : NestedBlockCertificate source before after)
    {familyIndex : Nat} {sourceFamily : VInductiveType}
    {sourceConstructor : VConstVal}
    (selection : NestedStructureSelection certificate.nested familyIndex
      sourceFamily sourceConstructor) :
    restoreExpr certificate.nested.declEntries certificate.nested.recMap
        selection.flatConstructor.type = sourceConstructor.type := by
  have restored := congrArg (fun value : VConstVal => value.type)
    (certificate.restoreSelectedConstructor selection)
  simpa only [NestedBlockChecked.restoreDeclConstructor] using restored

/-- Restoration commutes past the exact shared-parameter prefix of the
selected flattened constructor. -/
theorem restoreSelectedConstructorBody
    (certificate : NestedBlockCertificate source before after)
    {familyIndex : Nat} {sourceFamily : VInductiveType}
    {sourceConstructor : VConstVal}
    (selection : NestedStructureSelection certificate.nested familyIndex
      sourceFamily sourceConstructor) :
    restoreExpr certificate.nested.declEntries certificate.nested.recMap
        (VExpr.dropN source.nparams selection.flatConstructor.type) =
      VExpr.dropN source.nparams sourceConstructor.type := by
  have familyMember : selection.family ∈
      certificate.nested.generation.families :=
    List.mem_iff_getElem?.2 ⟨familyIndex, selection.family_at⟩
  have constructorMember : selection.constructor ∈
      selection.family.ctorPairs := by
    rw [selection.constructors_eq]
    simp
  have flatParamsLength :
      (VExpr.telN source.nparams selection.flatConstructor.type).length =
        source.nparams := by
    have checked :=
      (certificate.nested.generation.shape.2.2.2.2 selection.family
        familyMember).2.2.2.2.2.2 selection.constructor
          constructorMember |>.2.2.1
    rw [selection.constructor_raw_eq,
      certificate.nested.elim.nparams_eq] at checked
    exact checked
  rw [VInductDecl.restoreExpr_dropN _ _ _ _ flatParamsLength,
    certificate.restoreSelectedConstructorType selection]

/-- The exact flattened field telescope restores pointwise, in source order,
to the selected stored source field telescope. -/
theorem restoreSelectedConstructorFields
    (certificate : NestedBlockCertificate source before after)
    {familyIndex : Nat} {sourceFamily : VInductiveType}
    {sourceConstructor : VConstVal}
    (selection : NestedStructureSelection certificate.nested familyIndex
      sourceFamily sourceConstructor) :
    (ctorFields
        (VExpr.dropN source.nparams selection.flatConstructor.type)).map
        (restoreExpr certificate.nested.declEntries
          certificate.nested.recMap) =
      ctorFields (VExpr.dropN source.nparams sourceConstructor.type) := by
  have fieldsLength :
      (ctorFields
          (VExpr.dropN source.nparams selection.flatConstructor.type)).length =
        (ctorFields
          (VExpr.dropN source.nparams sourceConstructor.type)).length := by
    calc
      (ctorFields
          (VExpr.dropN source.nparams selection.flatConstructor.type)).length =
          (selection.constructor.rawFields
            certificate.nested.elim.flat.nparams).length := by
        simp only [NormalizedCtor.rawFields, selection.constructor_raw_eq,
          certificate.nested.elim.nparams_eq]
      _ = (ctorFields
          (VExpr.dropN source.nparams sourceConstructor.type)).length :=
        selection.source_flat_fields_length_eq.symm
  exact VInductDecl.restoreExpr_ctorFields _ _
    (certificate.restoreSelectedConstructorBody selection) fieldsLength

/-- Canonical finite choice of one sort for every restored source field.  The
completed nested transaction already checks the exact source constructor
telescope, so this definition adds no semantic premise. -/
noncomputable def restoredFieldSorts
    (certificate : NestedBlockCertificate source before after)
    {familyIndex : Nat} {sourceFamily : VInductiveType}
    {sourceConstructor : VConstVal}
    (selection : NestedStructureSelection certificate.nested familyIndex
      sourceFamily sourceConstructor) : List VLevel :=
  Classical.choose <|
    (certificate.selectedSourceConstructorFieldsTelescope selection)
      |>.exists_onSortTel

/-- The chosen restored field-sort inventory labels the exact source field
telescope in the completed nested environment. -/
theorem restoredFieldTelescope
    (certificate : NestedBlockCertificate source before after)
    {familyIndex : Nat} {sourceFamily : VInductiveType}
    {sourceConstructor : VConstVal}
    (selection : NestedStructureSelection certificate.nested familyIndex
      sourceFamily sourceConstructor) :
    after.OnSortTel source.uvars
      (VExpr.telN source.nparams sourceConstructor.type).reverse
      (ctorFields (VExpr.dropN source.nparams sourceConstructor.type))
      (certificate.restoredFieldSorts selection) :=
  Classical.choose_spec <|
    (certificate.selectedSourceConstructorFieldsTelescope selection)
      |>.exists_onSortTel

/-- Construct the restored projection-facing view selected by one completed
nested transaction.  Its flattened backend is definitionally the exact
`NestedBlockChecked` generation already retained by the certificate. -/
noncomputable def restoredStructureView
    (certificate : NestedBlockCertificate source before after)
    {familyIndex : Nat} {sourceFamily : VInductiveType}
    {sourceConstructor : VConstVal}
    (selection : NestedStructureSelection certificate.nested familyIndex
      sourceFamily sourceConstructor) : VRestoredBlockStructureView where
  source := source
  nested := certificate.nested
  familyIndex := familyIndex
  sourceFamily := sourceFamily
  sourceConstructor := sourceConstructor
  selection := selection
  flatFieldsRestored :=
    certificate.restoreSelectedConstructorFields selection
  fieldSorts := certificate.restoredFieldSorts selection
  fieldSorts_length :=
    (certificate.restoredFieldTelescope selection).length_eq.symm

/-- At every operational field universe, runtime restoration maps the exact
flattened producer field inventory to the source field inventory after
declaration-universe instantiation.  This is the universe-specialized form
of the literal constructor restoration theorem. -/
theorem restoredStructureView_restoreFlatFields_instL
    (certificate : NestedBlockCertificate source before after)
    {familyIndex : Nat} {sourceFamily : VInductiveType}
    {sourceConstructor : VConstVal}
    (selection : NestedStructureSelection certificate.nested familyIndex
      sourceFamily sourceConstructor)
    (fieldSort : VLevel) (levels : List VLevel)
    (hlevels : levels.length = source.uvars) :
    let view := certificate.restoredStructureView selection
    view.flatView.fields.map (fun field =>
        view.nested.restoreRecAt
          (view.flatView.projectionLevels fieldSort levels)
          (field.instL levels)) =
      view.fields.map (VExpr.instL levels) := by
  let view := certificate.restoredStructureView selection
  change view.flatView.fields.map (fun field =>
      view.nested.restoreRecAt
        (view.flatView.projectionLevels fieldSort levels)
        (field.instL levels)) =
    view.fields.map (VExpr.instL levels)
  have flatFields : view.flatView.fields =
      ctorFields
        (VExpr.dropN source.nparams selection.flatConstructor.type) := by
    change ctorFields
      (VExpr.dropN view.flatView.nparams
        view.selection.constructor.raw.type) = _
    rw [view.flatView_nparams, view.selection.constructor_raw_eq]
    rfl
  have sourceFields : view.fields =
      ctorFields
        (VExpr.dropN source.nparams sourceConstructor.type) := by
    rfl
  have fieldsRestored :
      view.flatView.fields.map
          (restoreExpr view.nested.declEntries view.nested.recMap) =
        view.fields := by
    rw [flatFields, sourceFields]
    exact certificate.restoreSelectedConstructorFields selection
  rw [← congrArg (List.map (VExpr.instL levels)) fieldsRestored]
  simp only [List.map_map]
  apply List.map_congr_left
  intro field _
  exact view.restoreRecAt_source_instL fieldSort levels (by
    simpa [view, restoredStructureView] using hlevels) field

/-- After supplying an inert runtime parameter spine, restoration maps the
exact flattened specialized field inventory to the source specialized field
inventory at the same field indices.  This is the operational strengthening
of `restoredStructureView_restoreFlatFields_instL`. -/
theorem restoredStructureView_restoreFlatSpecializedFields
    (certificate : NestedBlockCertificate source before after)
    (targetsWF : NestedTargetsWF before certificate.nested.elim.targets)
    {familyIndex : Nat} {sourceFamily : VInductiveType}
    {sourceConstructor : VConstVal}
    (selection : NestedStructureSelection certificate.nested familyIndex
      sourceFamily sourceConstructor)
    (fieldSort : VLevel) (levels : List VLevel)
    (hlevels : levels.length = source.uvars) (params : List VExpr) :
    let view := certificate.restoredStructureView selection
    (∀ parameter ∈ params,
      RestoreInert
        (view.nested.recEntries.map
          (·.instL (view.flatView.projectionLevels fieldSort levels)))
        view.nested.recMap parameter) →
    (view.flatView.specializedFields levels params).map
        (view.nested.restoreRecAt
          (view.flatView.projectionLevels fieldSort levels)) =
      view.specializedFields levels params := by
  let view := certificate.restoredStructureView selection
  change (∀ parameter ∈ params,
      RestoreInert
        (view.nested.recEntries.map
          (·.instL (view.flatView.projectionLevels fieldSort levels)))
        view.nested.recMap parameter) →
    (view.flatView.specializedFields levels params).map
        (view.nested.restoreRecAt
          (view.flatView.projectionLevels fieldSort levels)) =
      view.specializedFields levels params
  intro paramsInert
  let projectionLevels := view.flatView.projectionLevels fieldSort levels
  have raw := certificate.restoredStructureView_restoreFlatFields_instL
    selection fieldSort levels hlevels
  change view.flatView.fields.map (fun field =>
      view.nested.restoreRecAt projectionLevels (field.instL levels)) =
    view.fields.map (VExpr.instL levels) at raw
  have closed : RestoreEntriesClosed view.nested.recEntries := by
    change RestoreEntriesClosed certificate.nested.recEntries
    exact certificate.recEntriesClosed targetsWF
  change (view.flatView.specializedFields levels params).map
      (view.nested.restoreRecAt projectionLevels) =
    view.specializedFields levels params
  apply List.ext_getElem?
  intro index
  simp only [VRestoredBlockStructureView.specializedFields,
    VBlockStructureView.specializedFields, List.getElem?_map,
    List.getElem?_zipIdx, Nat.zero_add]
  have rawAt := congrArg (fun fields : List VExpr => fields[index]?) raw
  simp only [List.getElem?_map] at rawAt
  cases flatFound : view.flatView.fields[index]? with
  | none =>
      cases sourceFound : view.fields[index]? <;>
        simp [flatFound, sourceFound] at rawAt ⊢
  | some flatField =>
      cases sourceFound : view.fields[index]? with
      | none => simp [flatFound, sourceFound] at rawAt
      | some sourceField =>
          simp only [flatFound, sourceFound, Option.map_some] at rawAt ⊢
          rw [← view.nested.restoreRecAt_instRevAt closed projectionLevels
            (flatField.instL levels) params index paramsInert]
          rw [Option.some.inj rawAt]

/-- The constructed view retains the exact checked source field telescope at
its final restored endpoint. -/
theorem restoredStructureView_fieldTelescope
    (certificate : NestedBlockCertificate source before after)
    {familyIndex : Nat} {sourceFamily : VInductiveType}
    {sourceConstructor : VConstVal}
    (selection : NestedStructureSelection certificate.nested familyIndex
      sourceFamily sourceConstructor) :
    after.OnSortTel source.uvars
      (certificate.restoredStructureView selection).constructorParams.reverse
      (certificate.restoredStructureView selection).fields
      (certificate.restoredStructureView selection).fieldSorts := by
  simpa [restoredStructureView,
    VRestoredBlockStructureView.constructorParams,
    VRestoredBlockStructureView.fields] using
      certificate.restoredFieldTelescope selection

/-- A completed nested transaction constructs the complete exact restored
metadata layout at its final environment.  No lookup or typing premise is
left to a projection consumer. -/
theorem restoredStructureView_layoutWF
    (certificate : NestedBlockCertificate source before after)
    {familyIndex : Nat} {sourceFamily : VInductiveType}
    {sourceConstructor : VConstVal}
    (selection : NestedStructureSelection certificate.nested familyIndex
      sourceFamily sourceConstructor) :
    (certificate.restoredStructureView selection).LayoutWF after := by
  let view := certificate.restoredStructureView selection
  have familyMember : sourceFamily ∈ source.types :=
    List.mem_iff_getElem?.2 ⟨familyIndex, selection.source_at⟩
  have constructorMember : sourceConstructor ∈ sourceFamily.ctors := by
    rw [selection.source_constructors_eq]
    simp
  refine {
    family := ?_
    constructor := ?_
    recursor := ?_
    rules := ?_
    fieldTelescope := certificate.restoredStructureView_fieldTelescope
      selection }
  · simpa [view, restoredStructureView,
      VRestoredBlockStructureView.name] using
      certificate.familyLookup familyMember
  · simpa [view, restoredStructureView,
      VRestoredBlockStructureView.constructorName] using
      certificate.constructorLookup familyMember constructorMember
  · change after.constants view.recursor.name =
      some view.recursor.toVConstant
    exact certificate.recursorLookup view.recursor_mem
  · intro rule member
    exact certificate.ruleRegistered member

end VInductDecl.NestedBlockCertificate

namespace VInductDecl.NestedStagedCertificate

variable {source : VInductDecl} {before flatAfter after : VEnv}

/-- Paired staging retains exactly the family semantics erased by the
smaller restored transaction certificate.  Together with the restored
transaction's final metadata layout, this constructs the family-facing
projection invariant without asking a consumer to reproduce normalization
evidence. -/
theorem restoredStructureView_familyLayoutWF
    (certificate : NestedStagedCertificate source before flatAfter after)
    {familyIndex : Nat} {sourceFamily : VInductiveType}
    {sourceConstructor : VConstVal}
    (selection : NestedStructureSelection certificate.restored.nested
      familyIndex sourceFamily sourceConstructor) :
    (certificate.restored.restoredStructureView selection).FamilyLayoutWF
      after := by
  refine {
    toLayoutWF :=
      certificate.restored.restoredStructureView_layoutWF selection
    familyWF := ?_ }
  have familyMember : selection.family ∈
      certificate.restored.nested.generation.families :=
    List.mem_iff_getElem?.2
      ⟨familyIndex, selection.family_at⟩
  have familyWF := certificate.flatWF.families
    selection.family familyMember
  simpa [VInductDecl.NestedBlockCertificate.restoredStructureView] using
    familyWF.mono certificate.restored.envLE

/-- Exact constant inventory of the flattened side of a paired nested
transaction.  Every final lookup is owned by precisely one of the three
producer phases, or is inherited from the common dependency boundary.  The
statement deliberately retains the generated payload rather than merely its
name, so later interpretation proofs can recover its stored type and universe
arity without a caller-selected witness. -/
theorem flatAfter_constants_cases
    (certificate : NestedStagedCertificate source before flatAfter after)
    {name : Name} {constant : VConstant}
    (lookup : flatAfter.constants name = some constant) :
    (∃ recursor ∈ certificate.restored.nested.generation.recursors,
        name = recursor.name ∧ constant = recursor.toVConstant) ∨
      (∃ constructor ∈
          certificate.restored.nested.elim.flat.blockConstructorConstants,
        name = constructor.name ∧ constant = constructor.toVConstant) ∨
      (∃ family ∈
          certificate.restored.nested.elim.flat.blockTypeConstants,
        name = family.name ∧ constant = family.toVConstant) ∨
      before.constants name = some constant := by
  obtain ⟨trace⟩ := certificate.flatCertificate.trace
  have recLookup : trace.recEnv.constants name = some constant := by
    rw [← trace.addRules,
      VEnv.foldl_addDefEq_constants_eq] at lookup
    exact lookup
  rcases VEnv.foldlM_addConst_constants_cases
      (fun recursor : VConstVal => recursor.name)
      (fun recursor => recursor.toVConstant)
      certificate.restored.nested.generation.recursors trace.addRecs
      recLookup with recursor | beforeRecursors
  · exact .inl recursor
  rcases VEnv.foldlM_addConst_constants_cases
      (fun constructor : VConstVal => constructor.name)
      (fun constructor => constructor.toVConstant)
      certificate.restored.nested.elim.flat.blockConstructorConstants
      trace.addCtors beforeRecursors with constructor | beforeConstructors
  · exact .inr (.inl constructor)
  rcases VEnv.foldlM_addConst_constants_cases
      (fun family : VConstVal => family.name)
      (fun family => family.toVConstant)
      certificate.restored.nested.elim.flat.blockTypeConstants trace.addTypes
      beforeConstructors with family | inherited
  · exact .inr (.inr (.inl family))
  · exact .inr (.inr (.inr inherited))

/-- The flattened transaction's registered equations are exactly its
producer-owned generated rules together with the equations inherited from
the common dependency boundary. -/
theorem flatAfter_defeqs_iff_before
    (certificate : NestedStagedCertificate source before flatAfter after)
    (rule : VDefEq) :
    flatAfter.defeqs rule ↔
      rule ∈ certificate.flatCertificate.generation.generatedRules ∨
        before.defeqs rule := by
  obtain ⟨trace⟩ := certificate.flatCertificate.trace
  have rules : flatAfter.defeqs rule ↔
      rule ∈ certificate.flatCertificate.generation.generatedRules ∨
        trace.recEnv.defeqs rule := by
    simpa only [trace.addRules] using
      VEnv.foldl_addDefEq_defeqs_iff
        certificate.flatCertificate.generation.generatedRules
        trace.recEnv rule
  have recursors : trace.recEnv.defeqs rule ↔
      trace.ctorEnv.defeqs rule :=
    VEnv.foldlM_addConst_defeqs_iff
      (fun recursor : VConstVal => recursor.name)
      (fun recursor => recursor.toVConstant)
      certificate.restored.nested.generation.recursors trace.addRecs rule
  have constructors : trace.ctorEnv.defeqs rule ↔
      trace.typeEnv.defeqs rule :=
    VEnv.foldlM_addConst_defeqs_iff
      (fun constructor : VConstVal => constructor.name)
      (fun constructor => constructor.toVConstant)
      certificate.restored.nested.elim.flat.blockConstructorConstants
      trace.addCtors rule
  have families : trace.typeEnv.defeqs rule ↔ before.defeqs rule :=
    VEnv.foldlM_addConst_defeqs_iff
      (fun family : VConstVal => family.name)
      (fun family => family.toVConstant)
      certificate.restored.nested.elim.flat.blockTypeConstants
      trace.addTypes rule
  exact rules.trans <| or_congr Iff.rfl <|
    recursors.trans (constructors.trans families)

/-- The flattened transaction inherits its complete structure-eta registry
from the common dependency boundary: its three constant phases and final
equation fold do not register eta descriptors. -/
theorem flatAfter_structEtas_iff_before
    (certificate : NestedStagedCertificate source before flatAfter after)
    (rule : VStructEta) :
    flatAfter.structEtas rule ↔ before.structEtas rule := by
  obtain ⟨trace⟩ := certificate.flatCertificate.trace
  have rules : flatAfter.structEtas rule ↔ trace.recEnv.structEtas rule := by
    simpa only [trace.addRules] using
      VEnv.foldl_addDefEq_structEtas_iff
        certificate.flatCertificate.generation.generatedRules
        trace.recEnv rule
  have recursors : trace.recEnv.structEtas rule ↔
      trace.ctorEnv.structEtas rule :=
    VEnv.foldlM_addConst_structEtas_iff
      (fun recursor : VConstVal => recursor.name)
      (fun recursor => recursor.toVConstant)
      certificate.restored.nested.generation.recursors trace.addRecs rule
  have constructors : trace.ctorEnv.structEtas rule ↔
      trace.typeEnv.structEtas rule :=
    VEnv.foldlM_addConst_structEtas_iff
      (fun constructor : VConstVal => constructor.name)
      (fun constructor => constructor.toVConstant)
      certificate.restored.nested.elim.flat.blockConstructorConstants
      trace.addCtors rule
  have families : trace.typeEnv.structEtas rule ↔
      before.structEtas rule :=
    VEnv.foldlM_addConst_structEtas_iff
      (fun family : VConstVal => family.name)
      (fun family => family.toVConstant)
      certificate.restored.nested.elim.flat.blockTypeConstants
      trace.addTypes rule
  exact rules.trans (recursors.trans (constructors.trans families))

/-- Every name on which the canonical restoration interpretation acts was
fresh at the common dependency boundary of the paired transactions. -/
theorem restoreInterp_fresh
    (certificate : NestedStagedCertificate source before flatAfter after)
    {name : Name} {value : VExpr}
    (interpreted : certificate.restored.nested.restoreInterp name =
      some value) :
    before.constants name = none := by
  unfold NestedBlockChecked.restoreInterp at interpreted
  split at interpreted
  next recursor recursorFound =>
    have recursorMember := List.mem_of_find?_eq_some recursorFound
    have recursorName : recursor.name = name := by
      simpa using List.find?_some recursorFound
    rw [← recursorName]
    exact certificate.flatCertificate.recursorFresh recursorMember
  next recursorAbsent =>
    split at interpreted
    next constant constantFound =>
      have constantMember := List.mem_of_find?_eq_some constantFound
      have constantName : constant.name = name := by
        simpa using List.find?_some constantFound
      rw [← constantName]
      simp only [NestedBlockChecked.flatDeclarationConstants,
        List.mem_append] at constantMember
      rcases constantMember with familyMember | constructorMember
      · simp only [VInductDecl.blockTypeConstants,
          List.mem_map] at familyMember
        obtain ⟨family, familyMember, rfl⟩ := familyMember
        exact certificate.flatCertificate.familyFresh familyMember
      · exact certificate.flatCertificate.constructorFresh constructorMember
    next declarationAbsent => contradiction

/-- Typed syntax inherited from the dependency environment is disjoint from
the canonical restoration interpretation. -/
theorem restoreInterp_inert_of_hasType
    (certificate : NestedStagedCertificate source before flatAfter after)
    {U : Nat} {Γ : List VExpr} {expression type : VExpr}
    (contextWF : OnCtx Γ (before.IsType U))
    (typed : before.HasType U Γ expression type) :
    InterpInert certificate.restored.nested.restoreInterp expression := by
  intro name value interpreted
  exact typed.hasConst_false_of_absent certificate.restored.beforeWF.ordered
    contextWF (certificate.restoreInterp_fresh interpreted)

/-- Canonical restoration is literally inert on every well-formed inherited
context.  Each binder is typed in its preceding context, exactly matching the
dependent shape of `OnCtx`; this is the context equation needed by semantic
transport of inherited eta uses. -/
theorem restoreInterp_oldContext
    (certificate : NestedStagedCertificate source before flatAfter after)
    {U : Nat} {Γ : List VExpr} (contextWF : OnCtx Γ (before.IsType U)) :
    Γ.map (VExpr.substConst certificate.restored.nested.restoreInterp) =
      Γ := by
  induction Γ with
  | nil => rfl
  | cons type context ih =>
    change OnCtx context (before.IsType U) ∧
      before.IsType U context type at contextWF
    obtain ⟨contextWF, typeWF⟩ := contextWF
    obtain ⟨sortLevel, typeHasType⟩ := typeWF
    have typeInert := certificate.restoreInterp_inert_of_hasType
      contextWF typeHasType
    have typeEq :
        type.substConst certificate.restored.nested.restoreInterp = type :=
      VExpr.substConst_eq_of_interpInert typeInert
    simp only [List.map_cons, typeEq, ih contextWF]

/-- In particular, the stored type of every inherited constant is literally
unchanged by canonical restoration substitution. -/
theorem restoreInterp_oldConstantType
    (certificate : NestedStagedCertificate source before flatAfter after)
    {name : Name} {constant : VConstant}
    (lookup : before.constants name = some constant) :
    constant.type.substConst certificate.restored.nested.restoreInterp =
      constant.type := by
  apply VExpr.substConst_eq_of_interpInert
  obtain ⟨_, typed⟩ := certificate.restored.beforeWF.ordered.constWF lookup
  exact certificate.restoreInterp_inert_of_hasType (by trivial) typed

/-- Each expression in an inherited registered definitional equation is
literally unchanged by canonical restoration substitution. -/
theorem restoreInterp_oldDefEq
    (certificate : NestedStagedCertificate source before flatAfter after)
    {rule : VDefEq} (registered : before.defeqs rule) :
    rule.lhs.substConst certificate.restored.nested.restoreInterp =
        rule.lhs ∧
      rule.rhs.substConst certificate.restored.nested.restoreInterp =
        rule.rhs ∧
      rule.type.substConst certificate.restored.nested.restoreInterp =
        rule.type := by
  have wf := certificate.restored.beforeWF.ordered.defEqWF registered
  refine ⟨?_, ?_, ?_⟩
  · apply VExpr.substConst_eq_of_interpInert
    exact certificate.restoreInterp_inert_of_hasType (by trivial) wf.1
  · apply VExpr.substConst_eq_of_interpInert
    exact certificate.restoreInterp_inert_of_hasType (by trivial) wf.2
  · apply VExpr.substConst_eq_of_interpInert
    obtain ⟨_, typed⟩ := wf.1.isType
      certificate.restored.beforeWF.ordered (by trivial)
    exact certificate.restoreInterp_inert_of_hasType (by trivial) typed

/-- An inherited constant supplies the semantic `keep` branch of the
canonical restoration interpretation.  Environment growth retains its exact
lookup, while the preceding inertness theorem identifies its interpreted
type with the stored one. -/
theorem restoreInterp_keep_of_before
    (certificate : NestedStagedCertificate source before flatAfter after)
    {name : Name} {constant : VConstant}
    (lookup : before.constants name = some constant) :
    ∃ constant' sortLevel,
      after.constants name = some constant' ∧
        constant'.uvars = constant.uvars ∧
        after.IsDefEq constant.uvars [] constant'.type
          (constant.type.substConst
            certificate.restored.nested.restoreInterp)
          (.sort sortLevel) := by
  obtain ⟨sortLevel, typed⟩ :=
    certificate.restored.beforeWF.ordered.constWF lookup
  refine ⟨constant, sortLevel,
    certificate.restored.envLE.constants lookup, rfl, ?_⟩
  rw [certificate.restoreInterp_oldConstantType lookup]
  exact typed.mono certificate.restored.envLE

/-- The complete semantic `keep` branch for the flattened-to-restored
interpretation.  Exact phase inversion rules out every generated constant
because all three generated inventories lie in the interpreter's domain;
the sole surviving case is therefore the inherited lookup above. -/
theorem restoreInterp_keep
    (certificate : NestedStagedCertificate source before flatAfter after)
    {name : Name} {constant : VConstant}
    (lookup : flatAfter.constants name = some constant)
    (uninterpreted : certificate.restored.nested.restoreInterp name = none) :
    ∃ constant' sortLevel,
      after.constants name = some constant' ∧
        constant'.uvars = constant.uvars ∧
        after.IsDefEq constant.uvars [] constant'.type
          (constant.type.substConst
            certificate.restored.nested.restoreInterp)
          (.sort sortLevel) := by
  rcases certificate.flatAfter_constants_cases lookup with
    recursor | constructor | family | inherited
  · obtain ⟨recursor, member, nameEq, _⟩ := recursor
    rw [nameEq] at uninterpreted
    exact (certificate.restored.nested
      |>.restoreInterp_ne_none_of_recursor_mem member uninterpreted).elim
  · obtain ⟨constructor, member, nameEq, _⟩ := constructor
    have declarationMember : constructor ∈
        certificate.restored.nested.flatDeclarationConstants := by
      exact List.mem_append_right _ member
    rw [nameEq] at uninterpreted
    exact (certificate.restored.nested
      |>.restoreInterp_ne_none_of_declaration_mem declarationMember
        uninterpreted).elim
  · obtain ⟨family, member, nameEq, _⟩ := family
    have declarationMember : family ∈
        certificate.restored.nested.flatDeclarationConstants := by
      exact List.mem_append_left _ member
    rw [nameEq] at uninterpreted
    exact (certificate.restored.nested
      |>.restoreInterp_ne_none_of_declaration_mem declarationMember
        uninterpreted).elim
  · exact certificate.restoreInterp_keep_of_before inherited

/-- An inherited registered equation supplies the semantic equation branch
of the canonical restoration interpretation. -/
theorem restoreInterp_defeq_of_before
    (certificate : NestedStagedCertificate source before flatAfter after)
    {rule : VDefEq} (registered : before.defeqs rule) :
    after.IsDefEq rule.uvars []
      (rule.lhs.substConst certificate.restored.nested.restoreInterp)
      (rule.rhs.substConst certificate.restored.nested.restoreInterp)
      (rule.type.substConst certificate.restored.nested.restoreInterp) := by
  have registered' := certificate.restored.envLE.defeqs registered
  have transported := VEnv.IsDefEq.extra0 registered'
    (certificate.restored.afterWF.ordered.defEqWF registered')
  obtain ⟨lhs, rhs, type⟩ := certificate.restoreInterp_oldDefEq registered
  simpa only [lhs, rhs, type] using transported

/-- A structure-eta step which was already usable at the dependency boundary
is stable under canonical restoration.  Source context well-formedness makes
the actual major, reconstruction, result type, and context inert; the
registered equality can therefore be transported monotonically to the final
restored environment.  Recursively transported target premises are accepted
to match `ConstInterp.structEta`, but are not needed for this inherited case. -/
theorem restoreInterp_structEta_of_before
    (certificate : NestedStagedCertificate source before flatAfter after)
    {rule : VStructEta} {U : Nat} {Γ : List VExpr}
    {levels : List VLevel} {params : List VExpr}
    {resultLevel : VLevel} {major : VExpr}
    (registered : before.structEtas rule)
    (contextWF : OnCtx Γ (before.IsType U))
    (levelsWF : ∀ level ∈ levels, level.WF U)
    (levelsLength : levels.length = rule.uvars)
    (paramsLength : params.length = rule.nparams)
    (paramsSpine : before.SpineWF U Γ
      (rule.familyType.instL levels) params (.sort resultLevel))
    (majorType : before.HasType U Γ major
      (rule.structureType levels params))
    (rebuildType : before.HasType U Γ
      (rule.rebuild levels params major)
      (rule.structureType levels params))
    (_paramsSpine' : after.SpineWF U
      (Γ.map (VExpr.substConst
        certificate.restored.nested.restoreInterp))
      ((rule.familyType.instL levels).substConst
        certificate.restored.nested.restoreInterp)
      (params.map (VExpr.substConst
        certificate.restored.nested.restoreInterp)) (.sort resultLevel))
    (_majorType' : after.HasType U
      (Γ.map (VExpr.substConst
        certificate.restored.nested.restoreInterp))
      (major.substConst certificate.restored.nested.restoreInterp)
      ((rule.structureType levels params).substConst
        certificate.restored.nested.restoreInterp))
    (_rebuildType' : after.HasType U
      (Γ.map (VExpr.substConst
        certificate.restored.nested.restoreInterp))
      ((rule.rebuild levels params major).substConst
        certificate.restored.nested.restoreInterp)
      ((rule.structureType levels params).substConst
        certificate.restored.nested.restoreInterp)) :
    after.IsDefEq U
      (Γ.map (VExpr.substConst
        certificate.restored.nested.restoreInterp))
      ((rule.rebuild levels params major).substConst
        certificate.restored.nested.restoreInterp)
      (major.substConst certificate.restored.nested.restoreInterp)
      ((rule.structureType levels params).substConst
        certificate.restored.nested.restoreInterp) := by
  have sourceEquality : before.IsDefEq U Γ
      (rule.rebuild levels params major) major
      (rule.structureType levels params) :=
    .structEta registered levelsWF levelsLength paramsLength paramsSpine
      majorType rebuildType
  have targetEquality := sourceEquality.mono certificate.restored.envLE
  have contextEq := certificate.restoreInterp_oldContext contextWF
  have majorEq :
      major.substConst certificate.restored.nested.restoreInterp = major :=
    VExpr.substConst_eq_of_interpInert
      (certificate.restoreInterp_inert_of_hasType contextWF majorType)
  have rebuildEq :
      (rule.rebuild levels params major).substConst
          certificate.restored.nested.restoreInterp =
        rule.rebuild levels params major :=
    VExpr.substConst_eq_of_interpInert
      (certificate.restoreInterp_inert_of_hasType contextWF rebuildType)
  obtain ⟨sortLevel, structureType⟩ :=
    majorType.isType certificate.restored.beforeWF.ordered contextWF
  have structureTypeEq :
      (rule.structureType levels params).substConst
          certificate.restored.nested.restoreInterp =
        rule.structureType levels params :=
    VExpr.substConst_eq_of_interpInert
      (certificate.restoreInterp_inert_of_hasType contextWF structureType)
  simpa only [contextEq, majorEq, rebuildEq, structureTypeEq] using
    targetEquality

/-- Canonical restoration is a complete constant interpretation from the
common dependency environment into the completed restored transaction.
Interpreted names are fresh at the source, so the value branch is impossible;
all surviving constants, equations, and usable eta steps are inherited
semantically. -/
theorem restoreInterp_beforeConstInterp
    (certificate : NestedStagedCertificate source before flatAfter after)
    (targetsWF : NestedTargetsWF before
      certificate.restored.nested.elim.targets) :
    VEnv.ConstInterp before after
      certificate.restored.nested.restoreInterp where
  ordered := certificate.restored.beforeWF.ordered
  ordered' := certificate.restored.afterWF.ordered
  closed := certificate.restored.restoreInterp_closed targetsWF
  value := by
    intro name constant value lookup interpreted
    have fresh := certificate.restoreInterp_fresh interpreted
    rw [lookup] at fresh
    contradiction
  keep := by
    intro _ _ lookup _
    exact certificate.restoreInterp_keep_of_before lookup
  defeq := certificate.restoreInterp_defeq_of_before
  structEta := certificate.restoreInterp_structEta_of_before

end VInductDecl.NestedStagedCertificate

end Lean4Lean
