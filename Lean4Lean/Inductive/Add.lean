/-
This file is derived from lean4lean and has been modified by Argument Computer Corporation.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/

import Batteries.Data.List.Basic
import Lean4Lean.Environment.Basic
import Lean4Lean.TypeChecker

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

namespace AddInductive
open TypeChecker

structure RecInfo where
  motive : Expr
  minors : Array Expr
  indices : Array Expr
  major : Expr
  deriving Inhabited

structure InductiveStats where
  lctx : LocalContext := {}
  levels : List Level
  resultLevel : Level
  nindices : Array Nat := #[]
  indConsts : Array Expr
  params : Array Expr
  isNotZero : Bool
  deriving Inhabited

/-- Explicit initial state for family validation. Naming this value keeps the
executable producer and its exact-result lemmas independent of the opaque
compiler-generated `Inhabited` instance. -/
def InductiveStats.initial (levels : List Level) : InductiveStats where
  levels := levels
  resultLevel := .zero
  indConsts := #[]
  params := #[]
  isNotZero := false

structure Context where
  env : Environment
  lctx : LocalContext := {}
  lparams : List Name
  ngen : NameGenerator := { namePrefix := `_ind_fresh }
  safety : DefinitionSafety
  allowPrimitive : Bool
  fuel : FuelConfig := {}

/-- Checker context represented by an inductive-add context. Candidate traces
retain the latter so Verify can recover this exact former value. -/
def Context.toTypeChecker (context : Context) : TypeChecker.Context where
  env := context.env
  lctx := context.lctx
  safety := context.safety
  lparams := context.lparams
  fuel := context.fuel

/-- The exact free variable allocated by the next `withLocalDecl` in an
inductive-add context. -/
def Context.freshFVarId (context : Context) : FVarId :=
  ⟨context.ngen.curr⟩

def Context.freshExpr (context : Context) : Expr :=
  .fvar context.freshFVarId

/-- Context seen by the body of the next `withLocalDecl`.  Naming this update
lets candidate traces index a Pi body by the actual reader context used by the
producer, rather than retaining an unrelated context as unchecked data. -/
def Context.pushLocalDecl (context : Context)
    (name : Name) (binderInfo : BinderInfo) (type : Expr) : Context :=
  { context with
    lctx := context.lctx.mkLocalDecl context.freshFVarId name type binderInfo
    ngen := context.ngen.next }

/-- A reader context reached from another solely by the scoped local
declarations used by inductive synthesis.  The relation deliberately ignores
the values returned by the synthesis loops: it records the one operational
fact needed by verification, namely that an eventual callback context is the
root context followed by zero or more `withLocalDecl` pushes. -/
inductive Context.LocalExtension (root : Context) : Context → Prop where
  | refl : LocalExtension root root
  | push {current : Context} (extension : LocalExtension root current)
      (name : Name) (binderInfo : BinderInfo) (type : Expr) :
      LocalExtension root (current.pushLocalDecl name binderInfo type)

abbrev M := ReaderT Context <| Except Exception

instance : MonadLocalNameGenerator M where
  withFreshId f c := f c.ngen.curr { c with ngen := c.ngen.next }

instance (priority := low) : MonadLift TypeChecker.M M where
  monadLift x c := x.run c.env c.safety c.lctx c.lparams (fuel := c.fuel)

@[simp] theorem liftTypeChecker_apply (x : TypeChecker.M α) (c : Context) :
    (liftM x : M α) c =
      x.run c.env c.safety c.lctx c.lparams (fuel := c.fuel) :=
  rfl

@[simp] theorem liftExcept_apply (x : Except Exception α) (c : Context) :
    (liftM x : M α) c = x :=
  rfl

instance (priority := low+1) : MonadWithReaderOf LocalContext M where
  withReader f x := withReader (fun c => { c with lctx := f c.lctx }) x

instance : MonadLCtx M where
  getLCtx := return (← read).lctx

@[simp] theorem getLCtx_apply (context : Context) :
    (getLCtx : M LocalContext) context = .ok context.lctx := by
  rfl

@[simp] theorem withLocalDecl_apply
    (name : Name) (binderInfo : BinderInfo) (type : Expr)
    (k : Expr → M α) (context : Context) :
    withLocalDecl name binderInfo type k context =
      k context.freshExpr
        (context.pushLocalDecl name binderInfo type) := by
  rfl

@[inline] def withEnv (env : Environment) (x : M α) : M α :=
  withReader (fun c => { c with env }) x

/-- Run a closed-metadata action without inheriting validation-local
declarations.  All other reader fields, including the staged environment and
fuel, are preserved exactly. -/
@[inline] def withEmptyLocalContext (x : M α) : M α :=
  withReader (fun c : Context => { c with lctx := {} }) x

@[simp] theorem withEmptyLocalContext_apply (x : M α) (context : Context) :
    withEmptyLocalContext x context = x { context with lctx := {} } := by
  rfl

def getType (fvar : Expr) : M Expr :=
  return ((← getLCtx).get! fvar.fvarId!).type

/-- Transparent binder-annotation peeling used by inductive checking.

Lean's `Expr.consumeTypeAnnotations` is an opaque partial implementation.  A
kernel proof of an exact successful inductive pass cannot reduce through that
helper, so using it directly would require a separate contract axiom for every
annotated binder.  This structural mirror covers the same four top-level
annotations and is regression-checked against Lean's helper below at the
candidate boundary. -/
def consumeTypeAnnotations : (source : Expr) → Expr
  | .app (.app (.const name levels) type) default =>
    if name = ``_root_.optParam then
      consumeTypeAnnotations type
    else if name = ``_root_.autoParam then
      consumeTypeAnnotations type
    else
      .app (.app (.const name levels) type) default
  | .app (.const name levels) type =>
    if name = ``_root_.outParam then
      consumeTypeAnnotations type
    else if name = ``_root_.semiOutParam then
      consumeTypeAnnotations type
    else
      .app (.const name levels) type
  | source => source
termination_by source => sizeOf source

/-- Transparent structural equality used only as a fast path before the
normalization-based universe comparison. -/
def levelStructEq : Level → Level → Bool
  | .zero, .zero => true
  | .succ u, .succ v => levelStructEq u v
  | .max u₁ u₂, .max v₁ v₂ | .imax u₁ u₂, .imax v₁ v₂ =>
    levelStructEq u₁ v₁ && levelStructEq u₂ v₂
  | .param u, .param v => u == v
  | .mvar u, .mvar v => u == v
  | _, _ => false

/-- Transparent sufficient comparison for the common structural universe
cases used by constructor fields.  Every universe is at least zero, successor
is monotone, and otherwise exact structural equality is sufficient.  Cases
outside this deliberately small relation continue to the standard
normalization-based `Level.geq` comparison below. -/
def levelStructGe : Level → Level → Bool
  | _, .zero => true
  | .succ u, .succ v => levelStructGe u v
  | u, v => levelStructEq u v

def checkInductiveTypes
    (nparams : Nat) (indTypes : Array InductiveType)
    (k : InductiveStats → M α) : M α := do
  let rec loopInd dIdx stats : M α := do
    if _h : dIdx < indTypes.size then
      let indType := indTypes[dIdx]
      let env := (← read).env
      let type := indType.type
      env.checkNoMVarNoFVar indType.name type
      _ ← checkType type
      let rec loop stats type i nindices fuel k : M α := match fuel with
      | 0 => throw .deepRecursion
      | fuel+1 => do
        if let .forallE name dom body bi := type then
          if i < nparams then
            if stats.indConsts.isEmpty then
              withLocalDecl name bi (consumeTypeAnnotations dom) fun param => do
                let stats := { stats with params := stats.params.push param }
                let type := body.instantiate1 param
                loop stats (← whnf type) (i + 1) nindices fuel k
            else
              let param := stats.params[i]!
              unless ← isDefEq dom (← getType param) do
                throw <| .other "parameters of all inductive datatypes must match"
              let type := body.instantiate1 param
              loop stats (← whnf type) (i + 1) nindices fuel k
          else
            withLocalDecl name bi (consumeTypeAnnotations dom) fun arg => do
              let type := body.instantiate1 arg
              loop stats (← whnf type) i (nindices + 1) fuel k
        else
          if i != nparams then
            throw <| .other "number of parameters mismatch in inductive datatype declaration"
          k type stats nindices
      let fuel := (← readThe Context).fuel.inductiveFuel
      loop stats (← whnf type) 0 0 fuel fun type stats nindices => show M α from do
      let type ← ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indType.name stats.levels) }
      loopInd (dIdx + 1) stats
    else
      k <|
        assert! stats.levels.length == (← read).lparams.length
        assert! stats.nindices.size == indTypes.size
        assert! stats.indConsts.size == indTypes.size
        assert! stats.params.size == nparams
        stats
  termination_by indTypes.size - dIdx
  loopInd 0 (InductiveStats.initial ((← read).lparams.map .param))

/-- Exact singleton result of the family-validation pass when the family type
normalizes directly to a sort. This is the non-telescope producer seam used by
end-to-end candidate certificates: the executable pass selects every retained
statistic, while callers supply only the ordinary checker runs it consumed. -/
def singletonInductiveStats (context : Context)
    (indType : InductiveType) (resultLevel : Level) : InductiveStats where
  lctx := context.lctx
  levels := context.lparams.map .param
  resultLevel := resultLevel
  nindices := #[0]
  indConsts := #[.const indType.name (context.lparams.map .param)]
  params := #[]
  isNotZero := resultLevel.isNeverZero

theorem checkInductiveTypes_singleton_zero_of_whnf_sort
    (context : Context) (indType : InductiveType)
    (inferred : Expr) (resultLevel : Level)
    (k : InductiveStats → M α)
    (hfuel : 0 < context.fuel.inductiveFuel)
    (hclosed :
      context.env.checkNoMVarNoFVar indType.name indType.type = .ok ())
    (hcheck :
      TypeChecker.M.run context.env context.safety context.lctx
          context.lparams context.fuel (TypeChecker.checkType indType.type) =
        .ok inferred)
    (hwhnf :
      TypeChecker.M.run context.env context.safety context.lctx
          context.lparams context.fuel (TypeChecker.whnf indType.type) =
        .ok (.sort resultLevel))
    (hensure :
      TypeChecker.M.run context.env context.safety context.lctx
          context.lparams context.fuel
          (TypeChecker.ensureSort (.sort resultLevel)) =
        .ok (.sort resultLevel)) :
    checkInductiveTypes 0 #[indType] k context =
      k (singletonInductiveStats context indType resultLevel) context := by
  cases hfuel_eq : context.fuel.inductiveFuel with
  | zero => omega
  | succ fuel =>
    simp [checkInductiveTypes, checkInductiveTypes.loopInd, checkInductiveTypes.loopInd.loop,
      singletonInductiveStats, readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
      ReaderT.bind, Bind.bind, Pure.pure, Except.bind, Except.pure, liftTypeChecker_apply, hclosed,
      hcheck, hwhnf, hensure, hfuel_eq, InductiveStats.initial, Expr.sortLevel!]

/-- Transparent occurrence test for constants in the inductive block.

Lean's `Expr.find?` is an opaque native traversal.  Using it here makes the
kernel's recursive-family and positivity decisions impossible to reduce in an
exact producer theorem without postulating a separate contract for that
traversal.  This structural version follows the same expression children and
keeps those decisions computational in the logic as well as at runtime. -/
def hasIndOcc (indConsts : Array Expr) : Expr → Bool
  | .const name _ => indConsts.any fun I => I.constName! == name
  | .app fn arg => hasIndOcc indConsts fn || hasIndOcc indConsts arg
  | .lam _ domain body _ | .forallE _ domain body _ =>
    hasIndOcc indConsts domain || hasIndOcc indConsts body
  | .letE _ type value body _ =>
    hasIndOcc indConsts type || hasIndOcc indConsts value ||
      hasIndOcc indConsts body
  | .mdata _ body | .proj _ _ body => hasIndOcc indConsts body
  | _ => false

/-- Return true if declaration is recursive -/
def isRec (indTypes : Array InductiveType) (indConsts : Array Expr) : Bool :=
  let rec loop
    | .forallE _ dom body _ => hasIndOcc indConsts dom || loop body
    | _ => false
  indTypes.any fun indType => indType.ctors.any fun ctor => loop ctor.type

/-- Return true if the given declaration is reflexive.

Remark: We say an inductive type `T` is reflexive if it
contains at least one constructor that takes as an argument a
function returning `T'` where `T'` is another inductive datatype (possibly equal to `T`)
in the same mutual declaration. -/
def isReflexive (indTypes : Array InductiveType) (indConsts : Array Expr) : Bool :=
  let rec loop
    | .forallE _ dom body _ => dom.isForall && hasIndOcc indConsts dom || loop body
    | _ => false
  indTypes.any fun indType => indType.ctors.any fun ctor => loop ctor.type

/-- One kernel family record assembled before the source-ordered declaration
fold.  Its full-block arguments retain the mutual names and recursion flags
computed by the executable producer. -/
def declaredInductiveInfo (stats : InductiveStats) (numParams : Nat)
    (indTypes : Array InductiveType) (indType : InductiveType)
    (numIndices numNested : Nat) (isUnsafe : Bool)
    (context : Context) : InductiveVal :=
  let all := indTypes.map (·.name) |>.toList
  { indType with
    numParams, numIndices, all, numNested, isUnsafe
    levelParams := context.lparams
    ctors := indType.ctors.map (·.name)
    isRec := isRec indTypes stats.indConsts
    isReflexive := isReflexive indTypes stats.indConsts }

/-- Kernel family records assembled before their source-ordered declaration
fold.  Naming this arbitrary-block payload makes the retained execution usable
without reconstructing the metadata list in Verify. -/
def declaredInductiveInfos (stats : InductiveStats) (numParams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (context : Context) : Array InductiveVal :=
  indTypes.zipWith (bs := stats.nindices) fun indType numIndices =>
    declaredInductiveInfo stats numParams indTypes indType numIndices
      numNested isUnsafe context

private theorem forall₂_zipWith_exists_right
    (f : α → β → γ) : ∀ (xs : List α) (ys : List β),
    xs.length = ys.length →
      List.Forall₂ (fun x z => ∃ y, z = f x y) xs
        (List.zipWith f xs ys)
  | [], [], _ => .nil
  | x :: xs, y :: ys, length_eq => by
      simp only [List.length_cons, Nat.succ.injEq] at length_eq
      exact .cons ⟨y, rfl⟩
        (forall₂_zipWith_exists_right f xs ys length_eq)

private theorem map_eq_map_of_forall₂
    {R : α → β → Prop} {f : α → γ} {g : β → γ}
    {xs : List α} {ys : List β}
    (relation : List.Forall₂ R xs ys)
    (aligned : ∀ x y, R x y → f x = g y) :
    xs.map f = ys.map g := by
  induction relation with
  | nil => rfl
  | cons head _ ih => simp only [List.map_cons, aligned _ _ head, ih]

/-- The executable metadata array has one exact full-block record for every
source family whenever validation has established the index-count invariant.
The dependent relation preserves source order and exposes the selected index
count without a partial lookup. -/
theorem declaredInductiveInfos_matches
    (stats : InductiveStats) (numParams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (context : Context)
    (size_eq : stats.nindices.size = indTypes.size) :
    List.Forall₂
      (fun indType info => ∃ numIndices,
        info = declaredInductiveInfo stats numParams indTypes indType
          numIndices numNested isUnsafe context)
      indTypes.toList
      (declaredInductiveInfos stats numParams indTypes numNested isUnsafe
        context).toList := by
  unfold declaredInductiveInfos
  rw [Array.toList_zipWith]
  apply forall₂_zipWith_exists_right
  simpa using size_eq.symm

/-- Select the exact family metadata record synthesized from a source family
and validator index count at one common array position. -/
theorem declaredInductiveInfos_getElem?
    (stats : InductiveStats) (numParams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (context : Context) {offset : Nat} {indType : InductiveType}
    {numIndices : Nat}
    (sourceAt : indTypes.toList[offset]? = some indType)
    (countAt : stats.nindices[offset]? = some numIndices) :
    (declaredInductiveInfos stats numParams indTypes numNested isUnsafe
      context).toList[offset]? =
        some (declaredInductiveInfo stats numParams indTypes indType
          numIndices numNested isUnsafe context) := by
  simp only [declaredInductiveInfos, Array.toList_zipWith,
    List.getElem?_zipWith, sourceAt, Array.getElem?_toList, countAt]

/-- Once family validation has fixed one index count per source family, the
metadata declaration inventory preserves the complete source name order. -/
theorem declaredInductiveInfos_names
    (stats : InductiveStats) (numParams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (context : Context)
    (size_eq : stats.nindices.size = indTypes.size) :
    (declaredInductiveInfos stats numParams indTypes numNested isUnsafe
      context).toList.map (·.name) = indTypes.toList.map (·.name) := by
  have relation := declaredInductiveInfos_matches stats numParams indTypes
    numNested isUnsafe context size_eq
  apply Eq.symm
  apply map_eq_map_of_forall₂ relation
  intro source info alignment
  show source.name = info.name
  obtain ⟨numIndices, rfl⟩ := alignment
  rfl

/-- Every emitted family record retains the name of a source family.  This
direction does not require the validation-size invariant: membership in the
truncated `zipWith` already supplies a valid source index. -/
theorem declaredInductiveInfos_name
    (stats : InductiveStats) (numParams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (context : Context) {info : InductiveVal}
    (member : info ∈
      (declaredInductiveInfos stats numParams indTypes numNested isUnsafe
        context).toList) :
    ∃ indType ∈ indTypes.toList, info.name = indType.name := by
  rw [Array.mem_toList_iff, Array.mem_iff_getElem] at member
  obtain ⟨i, outputUpper, getEq⟩ := member
  have sourceUpper : i < indTypes.size := by
    have zippedUpper : i < min indTypes.size stats.nindices.size := by
      simpa [declaredInductiveInfos] using outputUpper
    exact Nat.lt_of_lt_of_le zippedUpper (Nat.min_le_left _ _)
  refine ⟨indTypes[i], Array.mem_toList_iff.mpr
    (Array.getElem_mem sourceUpper), ?_⟩
  change (indTypes.zipWith (bs := stats.nindices) fun indType numIndices =>
    declaredInductiveInfo stats numParams indTypes indType numIndices
      numNested isUnsafe context)[i] = info at getEq
  rw [Array.getElem_zipWith outputUpper] at getEq
  rw [← getEq]
  rfl

/-- Transparent list form of the family-declaration fold. -/
def declareInductiveInfoList (allowPrimitive : Bool) :
    List InductiveVal → Environment → Except Exception Environment
  | [], env => .ok env
  | info :: infos, env => do
      env.checkName info.name allowPrimitive
      declareInductiveInfoList allowPrimitive infos
        (env.add (.inductInfo info))

/-- Exact source-ordered operational trace of the family-declaration fold. -/
inductive DeclareInductiveInfoListRun (allowPrimitive : Bool) :
    Environment → List InductiveVal → Environment → Prop where
  | nil : DeclareInductiveInfoListRun allowPrimitive env [] env
  | cons
      (checkName : env.checkName info.name allowPrimitive = .ok ())
      (tail : DeclareInductiveInfoListRun allowPrimitive
        (env.add (.inductInfo info)) infos finalEnv) :
      DeclareInductiveInfoListRun allowPrimitive env (info :: infos) finalEnv

/-- Interpret one exact successful declaration fold as its dependent trace. -/
theorem DeclareInductiveInfoListRun.of_run
    (run : declareInductiveInfoList allowPrimitive infos env = .ok finalEnv) :
    DeclareInductiveInfoListRun allowPrimitive env infos finalEnv := by
  induction infos generalizing env with
  | nil =>
      simp only [declareInductiveInfoList, Except.ok.injEq] at run
      subst finalEnv
      exact .nil
  | cons info infos ih =>
      simp only [declareInductiveInfoList] at run
      cases hcheck : env.checkName info.name allowPrimitive with
      | error error =>
          rw [hcheck] at run
          contradiction
      | ok value =>
          have value_eq : value = () := Subsingleton.elim _ _
          subst value
          simp only [hcheck] at run
          exact .cons hcheck (ih run)

/-- Forget the name-check evidence in a successful declaration trace. -/
theorem DeclareInductiveInfoListRun.environment
    (run : DeclareInductiveInfoListRun allowPrimitive env infos finalEnv) :
    finalEnv = infos.foldl
      (fun env info => env.add (.inductInfo info)) env := by
  induction run with
  | nil => rfl
  | cons _ _ ih => simpa only [List.foldl_cons] using ih

private theorem declaredInductiveInfoList_constants : ∀
    (infos : List InductiveVal) (env : Environment),
    (infos.foldl (fun env info => env.add (.inductInfo info)) env).constants =
      infos.foldl (fun constants info =>
        constants.insert info.name (.inductInfo info)) env.constants
  | [], _ => rfl
  | info :: infos, env =>
      declaredInductiveInfoList_constants infos (env.add (.inductInfo info))

private theorem declaredInductiveInfoList_quotInit : ∀
    (infos : List InductiveVal) (env : Environment),
    (infos.foldl (fun env info => env.add (.inductInfo info)) env).quotInit =
      env.quotInit
  | [], _ => rfl
  | info :: infos, env =>
      declaredInductiveInfoList_quotInit infos (env.add (.inductInfo info))

/-- The declaration trace exposes the exact final constant map. -/
theorem DeclareInductiveInfoListRun.constants
    (run : DeclareInductiveInfoListRun allowPrimitive env infos finalEnv) :
    finalEnv.constants = infos.foldl
      (fun constants info =>
        constants.insert info.name (.inductInfo info)) env.constants := by
  rw [run.environment]
  exact declaredInductiveInfoList_constants infos env

/-- Declaring family metadata does not change quotient initialization. -/
theorem DeclareInductiveInfoListRun.quotInit
    (run : DeclareInductiveInfoListRun allowPrimitive env infos finalEnv) :
    finalEnv.quotInit = env.quotInit := by
  rw [run.environment]
  exact declaredInductiveInfoList_quotInit infos env

def declareInductiveTypes (stats : InductiveStats) (numParams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat) (isUnsafe : Bool) : M Environment :=
  fun context =>
  declareInductiveInfoList context.allowPrimitive
    (declaredInductiveInfos stats numParams indTypes numNested isUnsafe
      context).toList context.env

/-- The exact kernel family record assembled for a singleton inductive block.
Naming it exposes the value installed by `declareInductiveTypes` without
asking a replay proof to duplicate the producer's record construction. -/
def singletonDeclaredInfo (stats : InductiveStats) (numParams numIndices : Nat)
    (indType : InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (context : Context) : InductiveVal :=
  { indType with
    numParams, numIndices, all := [indType.name], numNested, isUnsafe
    levelParams := context.lparams
    ctors := indType.ctors.map (·.name)
    isRec := isRec #[indType] stats.indConsts
    isReflexive := isReflexive #[indType] stats.indConsts }

/-- The arbitrary-block metadata inventory specializes to the named singleton
record when the retained index-count array has one exact entry. -/
theorem declaredInductiveInfos_singleton
    (stats : InductiveStats) (numParams numIndices : Nat)
    (indType : InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (context : Context) (hnindices : stats.nindices = #[numIndices]) :
    (declaredInductiveInfos stats numParams #[indType] numNested isUnsafe
      context).toList =
      [singletonDeclaredInfo stats numParams numIndices indType numNested
        isUnsafe context] := by
  simp [declaredInductiveInfos, singletonDeclaredInfo,
    declaredInductiveInfo, hnindices]

/-- A successful singleton family declaration installs exactly the family
record assembled by the executable producer.  The result equation supplies
the name-check evidence; replay callers provide only the validator's exact
singleton index count. -/
theorem declareInductiveTypes_singleton_constants
    (stats : InductiveStats) (numParams numIndices : Nat)
    (indType : InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (context : Context) (familyEnv : Environment)
    (hnindices : stats.nindices = #[numIndices])
    (hdeclare :
      declareInductiveTypes stats numParams #[indType] numNested isUnsafe context =
        .ok familyEnv) :
    familyEnv.constants =
      context.env.constants.insert indType.name
        (.inductInfo <| singletonDeclaredInfo stats numParams numIndices
          indType numNested isUnsafe context) := by
  have run := DeclareInductiveInfoListRun.of_run (by
    simpa only [declareInductiveTypes] using hdeclare)
  simpa [declaredInductiveInfos, declaredInductiveInfo, hnindices,
    singletonDeclaredInfo] using run.constants

/-- A successful singleton family declaration changes only the constant map;
in particular it preserves the kernel's quotient-initialization flag. -/
theorem declareInductiveTypes_singleton_quotInit
    (stats : InductiveStats) (numParams numIndices : Nat)
    (indType : InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (context : Context) (familyEnv : Environment)
    (_hnindices : stats.nindices = #[numIndices])
    (hdeclare :
      declareInductiveTypes stats numParams #[indType] numNested isUnsafe context =
        .ok familyEnv) :
    familyEnv.quotInit = context.env.quotInit := by
  have run := DeclareInductiveInfoListRun.of_run (by
    simpa only [declareInductiveTypes] using hdeclare)
  exact run.quotInit

/-- Family declaration observes only the environment, universe parameters,
and primitive-name policy of its reader context.  In particular, the local
telescope and fresh-name generator retained by family validation do not alter
the staged environment it produces. -/
theorem declareInductiveTypes_context_eq
    (stats : InductiveStats) (numParams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat)
    (isUnsafe : Bool) (left right : Context)
    (henv : left.env = right.env)
    (hlparams : left.lparams = right.lparams)
    (hallow : left.allowPrimitive = right.allowPrimitive) :
    declareInductiveTypes stats numParams indTypes numNested isUnsafe left =
      declareInductiveTypes stats numParams indTypes numNested isUnsafe right := by
  unfold declareInductiveTypes declaredInductiveInfos declaredInductiveInfo
  rw [henv, hlparams, hallow]

def isValidIndAppIdx (stats : InductiveStats) (t : Expr) (i : Nat) : Bool :=
  t.withApp fun I args => Id.run do
  unless I == stats.indConsts[i]! && args.size == stats.params.size + stats.nindices[i]! do
    return false
  for i in [:stats.params.size] do
    if stats.params[i]! != args[i]! then return false
  for i in [stats.params.size:args.size] do
    if hasIndOcc stats.indConsts args[i]! then return false
  true

def isValidIndApp? (stats : InductiveStats) (t : Expr) : Option Nat := do
  for i in [:stats.indConsts.size] do
    if isValidIndAppIdx stats t i then
      return i
  none

theorem isValidIndApp?_singleton_zero
    (stats : InductiveStats) (t : Expr)
    (hsize : stats.indConsts.size = 1)
    (hvalid : isValidIndAppIdx stats t 0 = true) :
    isValidIndApp? stats t = some 0 := by
  unfold isValidIndApp?
  simp [hsize, hvalid]

def isRecArg (stats : InductiveStats) (t : Expr) : M (Option Nat) := do
  loop t (← readThe Context).fuel.inductiveFuel
where
  loop t
  | 0 => throw .deepRecursion
  | fuel+1 => do
    let t ← whnf t
    let .forallE name dom body bi := t | return isValidIndApp? stats t
    withLocalDecl name bi (consumeTypeAnnotations dom) fun arg => do
    loop (body.instantiate1 arg) fuel

def checkPositivity (stats : InductiveStats) (t : Expr) (ctor : Name) (idx : Nat) :
    M Unit := do loop t (← readThe Context).fuel.inductiveFuel where
  loop t
  | 0 => throw .deepRecursion
  | fuel+1 => do
    let t ← whnf t
    if !hasIndOcc stats.indConsts t then return
    if let .forallE name dom body bi := t then
      if hasIndOcc stats.indConsts dom then
        throw <| .other s!"arg #{idx + 1} of '{ctor}' \
          has a non positive occurrence of the datatypes being declared"
      withLocalDecl name bi (consumeTypeAnnotations dom) fun arg => do
      loop (body.instantiate1 arg) fuel
    else if let none := isValidIndApp? stats t then
      throw <| .other s!"arg #{idx + 1} of '{ctor}' \
        has a non valid occurrence of the datatypes being declared"

/-- Validate the parameter/field telescope and terminal family application of
one constructor. This is factored from the outer traversal so successful
executions can be retained without reproducing compiler-expanded `for` loops. -/
def checkConstructorType (stats : InductiveStats) (isUnsafe : Bool)
    (idx : Nat) (n : Name) (t : Expr) : M Unit := do
  loop t 0 (← readThe Context).fuel.inductiveFuel
where
  loop t i
  | 0 => throw .deepRecursion
  | fuel+1 => do
    if let .forallE name dom body bi := t then
      if let some param := stats.params[i]? then
        unless ← isDefEq dom (← getType param) do
          throw <| .other
            s!"arg #{i + 1} of '{n}' does not match inductive datatype parameters"
        loop (body.instantiate1 param) (i + 1) fuel
      else
        let s ← ensureType dom
        -- Equal levels are reflexively admissible, so discharge that common
        -- case before consulting the full normalization comparison.
        if levelStructGe stats.resultLevel s.sortLevel! then
          pure ()
        else
          unless stats.resultLevel.isAlwaysZero || stats.resultLevel.geq' s.sortLevel! do
            throw <| .other s!"universe level of type_of(arg #{i + 1}) of '{n}' \
              is too big for the corresponding inductive datatype"
        if !isUnsafe then
          checkPositivity stats dom n i
        withLocalDecl name bi (consumeTypeAnnotations dom) fun arg => do
          loop (body.instantiate1 arg) (i + 1) fuel
    else if !isValidIndAppIdx stats t idx then
      throw <| .other s!"invalid return type for '{n}'"

/-- Validate constructors in source order while retaining the duplicate-name
accumulator as the fold result. -/
def checkConstructorFold (env : Environment) (stats : InductiveStats)
    (isUnsafe : Bool) (idx : Nat) (seen : NameSet)
    (ctors : List Constructor) : M NameSet := match ctors with
  | [] => pure seen
  | ctor :: ctors => do
    let n := ctor.name
    if seen.contains n then
      throw <| .other s!"duplicate constructor name '{n}'"
    let seen := seen.insert n
    let t := ctor.type
    env.checkNoMVarNoFVar n t
    -- Constructor metadata has just been established to contain no free
    -- variables. Its full closed-type check does not inherit family locals;
    -- parameter matching in `checkConstructorType` deliberately does.
    _ ← withEmptyLocalContext do checkType t
    checkConstructorType stats isUnsafe idx n t
    checkConstructorFold env stats isUnsafe idx seen ctors

/-- The named family recursion of `checkConstructors`.  Naming the loop keeps
the executable shell and its validation-trace mirror aligned without depending
on proof terms synthesized by `for` notation. -/
def checkConstructorsLoop (env : Environment) (stats : InductiveStats)
    (isUnsafe : Bool) : Nat → List InductiveType → M Unit
  | _, [] => pure ()
  | idx, indType :: rest => do
    _ ← checkConstructorFold env stats isUnsafe idx {} indType.ctors
    checkConstructorsLoop env stats isUnsafe (idx + 1) rest

def checkConstructors (indTypes : Array InductiveType)
    (stats : InductiveStats) (isUnsafe : Bool) : M Unit := do
  let env ← getEnv
  checkConstructorsLoop env stats isUnsafe 0 indTypes.toList

/-- One observed WHNF node in the executable normalization-candidate pass.
The complete `AddInductive.Context` is retained because Verify must replay the
same environment, safety mode, local context, level parameters, transparency,
and checker fuel before the observation acquires semantic authority. -/
structure CandidateWhnfStep where
  context : Context
  source : Expr
  result : Expr

/-- Exact ordinary-checker execution represented by one retained step. -/
def CandidateWhnfStep.Valid (step : CandidateWhnfStep) : Prop :=
  TypeChecker.M.run step.context.env step.context.safety
      step.context.lctx step.context.lparams step.context.fuel
      (TypeChecker.whnf step.source) =
    .ok step.result

/-- The result of evaluating one WHNF step together with the equality that
certifies the observation. -/
structure CandidateWhnfObservation (context : Context) (source : Expr) where
  result : Expr
  valid : CandidateWhnfStep.Valid ⟨context, source, result⟩

def observeCandidateWhnf (context : Context) (source : Expr) :
    Except Exception (CandidateWhnfObservation context source) :=
  match hrun :
      TypeChecker.M.run context.env context.safety context.lctx
        context.lparams context.fuel (TypeChecker.whnf source) with
  | .error err => .error err
  | .ok result => .ok ⟨result, hrun⟩

theorem observeCandidateWhnf_of_run
    (context : Context) (source result : Expr)
    (hrun : CandidateWhnfStep.Valid ⟨context, source, result⟩) :
    observeCandidateWhnf context source = .ok ⟨result, hrun⟩ := by
  change
    TypeChecker.M.run context.env context.safety context.lctx
        context.lparams context.fuel (TypeChecker.whnf source) =
      .ok result at hrun
  unfold observeCandidateWhnf
  split
  · simp_all
  · rename_i observed hobserved
    have : observed = result := by simp_all
    subst observed
    rfl

/-- Recover the state-bearing recursive checker execution erased by
`TypeChecker.M.run`. This is the exact `WhnfRun.run_eq` boundary used by
Verify; no final state is guessed or chosen. -/
theorem CandidateWhnfStep.innerRun
    (step : CandidateWhnfStep) (recursionFuel : Nat)
    (hdepth : step.context.fuel.recDepth = recursionFuel + 1)
    (hvalid : step.Valid) :
    ∃ state : TypeChecker.State,
      TypeChecker.Inner.whnf' step.source
          (TypeChecker.Methods.withFuel recursionFuel)
          step.context.toTypeChecker
          ({} : TypeChecker.State) =
        .ok (step.result, state) := by
  unfold CandidateWhnfStep.Valid at hvalid
  unfold TypeChecker.M.run TypeChecker.whnf TypeChecker.RecM.run at hvalid
  simp [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, StateT.bind, Except.bind, Bind.bind,
    StateT.pure, Except.pure, Pure.pure,
    StateT.run', Functor.map, Except.map] at hvalid
  rw [hdepth] at hvalid
  simp only [TypeChecker.Methods.withFuel,
    TypeChecker.Inner.whnf] at hvalid
  cases hinner :
      TypeChecker.Inner.whnf' step.source
        (TypeChecker.Methods.withFuel recursionFuel)
        { env := step.context.env
          lctx := step.context.lctx
          safety := step.context.safety
          lparams := step.context.lparams
          fuel := step.context.fuel }
        ({} : TypeChecker.State) with
  | error err => simp [hinner] at hvalid
  | ok pair =>
    rcases pair with ⟨observed, state⟩
    have : observed = step.result := by
      simpa [hinner] using hvalid
    subst observed
    exact ⟨state, by
      simpa [Context.toTypeChecker] using hinner⟩

/-- One full, non-inference-only type-check observation retained by the
candidate producer. -/
structure CandidateCheckTypeStep where
  context : Context
  source : Expr
  inferred : Expr

def CandidateCheckTypeStep.Valid
    (step : CandidateCheckTypeStep) : Prop :=
  TypeChecker.M.run step.context.env step.context.safety
      step.context.lctx step.context.lparams step.context.fuel
      (TypeChecker.checkType step.source) =
    .ok step.inferred

structure CandidateCheckTypeObservation
    (context : Context) (source : Expr) where
  inferred : Expr
  valid : CandidateCheckTypeStep.Valid ⟨context, source, inferred⟩

def observeCandidateCheckType (context : Context) (source : Expr) :
    Except Exception (CandidateCheckTypeObservation context source) :=
  match hrun :
      TypeChecker.M.run context.env context.safety context.lctx
        context.lparams context.fuel (TypeChecker.checkType source) with
  | .error err => .error err
  | .ok inferred => .ok ⟨inferred, hrun⟩

theorem observeCandidateCheckType_of_run
    (context : Context) (source inferred : Expr)
    (hrun : CandidateCheckTypeStep.Valid
      ⟨context, source, inferred⟩) :
    observeCandidateCheckType context source =
      .ok ⟨inferred, hrun⟩ := by
  change
    TypeChecker.M.run context.env context.safety context.lctx
        context.lparams context.fuel (TypeChecker.checkType source) =
      .ok inferred at hrun
  unfold observeCandidateCheckType
  split
  · simp_all
  · rename_i observed hobserved
    have : observed = inferred := by simp_all
    subst observed
    rfl

/-- Recover the state-bearing full-check execution erased by `M.run`. -/
theorem CandidateCheckTypeStep.innerRun
    (step : CandidateCheckTypeStep) (recursionFuel : Nat)
    (hdepth : step.context.fuel.recDepth = recursionFuel)
    (hvalid : step.Valid) :
    ∃ state : TypeChecker.State,
      TypeChecker.Inner.inferType step.source false
          (TypeChecker.Methods.withFuel recursionFuel)
          step.context.toTypeChecker
          ({} : TypeChecker.State) =
        .ok (step.inferred, state) := by
  unfold CandidateCheckTypeStep.Valid at hvalid
  unfold TypeChecker.M.run TypeChecker.checkType
    TypeChecker.RecM.run at hvalid
  simp [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, StateT.bind, Except.bind, Bind.bind,
    StateT.pure, Except.pure, Pure.pure,
    StateT.run', Functor.map, Except.map] at hvalid
  rw [hdepth] at hvalid
  cases hinner :
      TypeChecker.Inner.inferType step.source false
        (TypeChecker.Methods.withFuel recursionFuel)
        { env := step.context.env
          lctx := step.context.lctx
          safety := step.context.safety
          lparams := step.context.lparams
          fuel := step.context.fuel }
        ({} : TypeChecker.State) with
  | error err => simp [hinner] at hvalid
  | ok pair =>
    rcases pair with ⟨observed, state⟩
    have : observed = step.inferred := by
      simpa [hinner] using hvalid
    subst observed
    exact ⟨state, by
      simpa [Context.toTypeChecker] using hinner⟩

/-- One exact successful definitional-equality observation retained by the
candidate producer. The result is fixed to `true`; a negative checker result
is not evidence and aborts candidate construction. -/
structure CandidateIsDefEqStep where
  context : Context
  lhs : Expr
  rhs : Expr

def CandidateIsDefEqStep.Valid
    (step : CandidateIsDefEqStep) : Prop :=
  TypeChecker.M.run step.context.env step.context.safety
      step.context.lctx step.context.lparams step.context.fuel
      (TypeChecker.isDefEq step.lhs step.rhs) =
    .ok true

structure CandidateIsDefEqObservation
    (context : Context) (lhs rhs : Expr) : Type where
  valid : CandidateIsDefEqStep.Valid ⟨context, lhs, rhs⟩

def observeCandidateIsDefEq
    (context : Context) (lhs rhs : Expr) :
    Except Exception (CandidateIsDefEqObservation context lhs rhs) :=
  match hrun :
      TypeChecker.M.run context.env context.safety context.lctx
        context.lparams context.fuel (TypeChecker.isDefEq lhs rhs) with
  | .error err => .error err
  | .ok false =>
    .error (.other "normalization candidate changed a binder domain")
  | .ok true => .ok ⟨hrun⟩

theorem observeCandidateIsDefEq_of_run
    (context : Context) (lhs rhs : Expr)
    (hrun : CandidateIsDefEqStep.Valid ⟨context, lhs, rhs⟩) :
    observeCandidateIsDefEq context lhs rhs = .ok ⟨hrun⟩ := by
  change
    TypeChecker.M.run context.env context.safety context.lctx
        context.lparams context.fuel (TypeChecker.isDefEq lhs rhs) =
      .ok true at hrun
  unfold observeCandidateIsDefEq
  split
  · simp_all
  · simp_all
  · rfl

/-- Recover the state-bearing equality execution erased by `M.run`. -/
theorem CandidateIsDefEqStep.innerRun
    (step : CandidateIsDefEqStep) (recursionFuel : Nat)
    (hdepth : step.context.fuel.recDepth = recursionFuel)
    (hvalid : step.Valid) :
    ∃ state : TypeChecker.State,
      TypeChecker.Inner.isDefEq step.lhs step.rhs
          (TypeChecker.Methods.withFuel recursionFuel)
          step.context.toTypeChecker
          ({} : TypeChecker.State) =
        .ok (true, state) := by
  unfold CandidateIsDefEqStep.Valid at hvalid
  unfold TypeChecker.M.run TypeChecker.isDefEq
    TypeChecker.RecM.run at hvalid
  simp [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, StateT.bind, Except.bind, Bind.bind,
    StateT.pure, Except.pure, Pure.pure,
    StateT.run', Functor.map, Except.map] at hvalid
  rw [hdepth] at hvalid
  cases hinner :
      TypeChecker.Inner.isDefEq step.lhs step.rhs
        (TypeChecker.Methods.withFuel recursionFuel)
        { env := step.context.env
          lctx := step.context.lctx
          safety := step.context.safety
          lparams := step.context.lparams
          fuel := step.context.fuel }
        ({} : TypeChecker.State) with
  | error err => simp [hinner] at hvalid
  | ok pair =>
    rcases pair with ⟨observed, state⟩
    have : observed = true := by
      simpa [hinner] using hvalid
    subst observed
    exact ⟨state, by
      simpa [Context.toTypeChecker] using hinner⟩

/-- Source-indexed retained full-check execution. -/
structure CandidateCheckTypeRun (source : Expr) where
  step : CandidateCheckTypeStep
  source_eq : step.source = source
  valid : step.Valid

def buildCandidateCheckType
    (source : Expr) : M (CandidateCheckTypeRun source) := do
  let context ← readThe Context
  match observeCandidateCheckType context source with
  | .error err => throw err
  | .ok ⟨inferred, valid⟩ =>
    return ⟨⟨context, source, inferred⟩, rfl, valid⟩

/-- Structural certificate for the four top-level binder-domain annotations
peeled by `Expr.consumeTypeAnnotations`.

The certificate exposes which application argument survives. Verify can
therefore recover a strict translation and free-variable facts for the
consumed domain from the translated raw domain, without assigning semantic
authority to Lean's opaque helper. -/
inductive CandidateTypeAnnotationTrace : Expr → Expr → Type where
  | identity (source : Expr) :
      CandidateTypeAnnotationTrace source source
  | outParam (levels : List Level) (type : Expr)
      (inner : CandidateTypeAnnotationTrace type consumed) :
      CandidateTypeAnnotationTrace
        (.app (.const ``outParam levels) type) consumed
  | semiOutParam (levels : List Level) (type : Expr)
      (inner : CandidateTypeAnnotationTrace type consumed) :
      CandidateTypeAnnotationTrace
        (.app (.const ``semiOutParam levels) type) consumed
  | optParam (levels : List Level) (type default : Expr)
      (inner : CandidateTypeAnnotationTrace type consumed) :
      CandidateTypeAnnotationTrace
        (.app (.app (.const ``optParam levels) type) default) consumed
  | autoParam (levels : List Level) (type tactic : Expr)
      (inner : CandidateTypeAnnotationTrace type consumed) :
      CandidateTypeAnnotationTrace
        (.app (.app (.const ``autoParam levels) type) tactic) consumed

namespace CandidateTypeAnnotationTrace

/-- Transparent structural mirror of the top-level peeling algorithm. -/
def build : (source : Expr) → Sigma (CandidateTypeAnnotationTrace source)
  | .app (.app (.const name levels) type) default =>
    if hopt : name = ``_root_.optParam then by
      subst name
      let ⟨consumed, inner⟩ := build type
      exact ⟨consumed, .optParam levels type default inner⟩
    else if hauto : name = ``_root_.autoParam then by
      subst name
      let ⟨consumed, inner⟩ := build type
      exact ⟨consumed, .autoParam levels type default inner⟩
    else
      ⟨.app (.app (.const name levels) type) default, .identity _⟩
  | .app (.const name levels) type =>
    if hout : name = ``_root_.outParam then by
      subst name
      let ⟨consumed, inner⟩ := build type
      exact ⟨consumed, .outParam levels type inner⟩
    else if hsemi : name = ``_root_.semiOutParam then by
      subst name
      let ⟨consumed, inner⟩ := build type
      exact ⟨consumed, .semiOutParam levels type inner⟩
    else
      ⟨.app (.const name levels) type, .identity _⟩
  | source => ⟨source, .identity source⟩
termination_by source => sizeOf source

/-- The structural annotation builder computes the same transparent peeling
used by inductive validation.  This deliberately relates two definitions in
this module, not Lean's opaque `Expr.consumeTypeAnnotations`. -/
theorem build_consumed (source : Expr) :
    (build source).1 = consumeTypeAnnotations source := by
  fun_induction build source <;> simp_all [consumeTypeAnnotations]

end CandidateTypeAnnotationTrace

/-- A structural peeling certificate. Verify assigns semantic authority only
to the trace; compatibility with Lean's opaque helper is retained as a
differential executable check rather than a proof axiom. -/
structure CandidateTypeAnnotations (source : Expr) where
  consumed : Expr
  trace : CandidateTypeAnnotationTrace source consumed

def buildCandidateTypeAnnotations
    (source : Expr) : Except Exception (CandidateTypeAnnotations source) :=
  let ⟨consumed, trace⟩ := CandidateTypeAnnotationTrace.build source
  .ok ⟨consumed, trace⟩

namespace CandidateTypeAnnotations

/-- Operational compatibility with this module's transparent annotation
peeling.  Semantic consumers still rely on `trace` plus the retained
definitional-equality execution; `Matches` is used to replay the executable
family-validation path exactly. -/
def Matches (annotations : CandidateTypeAnnotations source) : Prop :=
  annotations.consumed = consumeTypeAnnotations source

theorem matches_of_build
    (annotations : CandidateTypeAnnotations source)
    (hbuild : buildCandidateTypeAnnotations source = .ok annotations) :
    annotations.Matches := by
  unfold buildCandidateTypeAnnotations at hbuild
  cases htrace : CandidateTypeAnnotationTrace.build source with
  | mk consumed trace =>
    simp only [Except.ok.injEq] at hbuild
    subst annotations
    simpa [Matches, htrace] using
      CandidateTypeAnnotationTrace.build_consumed source

end CandidateTypeAnnotations

/-- Differential check pinning the transparent implementation to Lean's
opaque helper. This is executable regression evidence, not a logical premise
of the candidate producer. -/
def candidateTypeAnnotationsAgree (source : Expr) : Bool :=
  let ⟨consumed, _⟩ := CandidateTypeAnnotationTrace.build source
  consumed.equal source.consumeTypeAnnotations

/-- Context- and source-indexed tree underlying one candidate expression.
The recursive indices are important: a Pi-domain trace uses the exact parent
context, while its body trace uses precisely `Context.pushLocalDecl` with the
structurally certified annotation-consumed domain and the corresponding fresh
free variable. The retained equality run relates that local declaration back
to the raw binder syntax. Thus expression position, annotation handling, and
checker-context provenance are enforced by the type rather than being
invariants of the producer alone. -/
inductive CandidateExprTrace : Context → Expr → Type where
  | terminal (context : Context) (source inferred result : Expr)
      (checked : CandidateCheckTypeStep.Valid
        ⟨context, source, inferred⟩)
      (valid : CandidateWhnfStep.Valid ⟨context, source, result⟩) :
      CandidateExprTrace context source
  | forallE (context : Context) (source : Expr)
      (inferred : Expr)
      (name : Name) (domain body : Expr)
      (binderInfo : BinderInfo)
      (fresh : context.lctx.find? context.freshFVarId = none)
      (annotations : CandidateTypeAnnotations domain)
      (annotationsEq : CandidateIsDefEqStep.Valid
        ⟨context, domain, annotations.consumed⟩)
      (checked : CandidateCheckTypeStep.Valid
        ⟨context, source, inferred⟩)
      (valid : CandidateWhnfStep.Valid
        ⟨context, source, .forallE name domain body binderInfo⟩)
      (domainCandidate : CandidateExprTrace context domain)
      (bodyCandidate : CandidateExprTrace
        (context.pushLocalDecl name binderInfo annotations.consumed)
        (body.instantiate1 context.freshExpr)) :
      CandidateExprTrace context source

namespace CandidateExprTrace

/-- The main Pi spine exposed by candidate WHNF was already present in the
stored source syntax at every traversed body position.

This is the structural precondition needed by mixed generation: it permits
normalization inside binder domains and at the terminal result, but it does
not let WHNF invent or remove the raw binders that generation must emit. -/
def storedSpine :
    {context : Context} → {source : Expr} →
      CandidateExprTrace context source → Bool
  | _, _, .terminal .. => true
  | _, _, .forallE _ source _ name domain body binderInfo _ _ _ _ _ _
      bodyCandidate =>
    Expr.structuralEq source (.forallE name domain body binderInfo) &&
      storedSpine bodyCandidate

/-- Kernel expressions whose strict Theory translation cannot have a Pi at
the root.  Let and metadata wrappers are transparent to strict translation;
free-variable and projection roots are deliberately excluded because their
Theory shape is selected by contextual evidence rather than syntax alone. -/
def generationTerminalSource : Expr → Bool
  | .sort _ | .const _ _ | .app _ _ | .lam _ _ _ _ => true
  | .letE _ _ _ body _ => generationTerminalSource body
  | .mdata _ body => generationTerminalSource body
  | _ => false

/-- Complete stored-spine gate used by mixed Theory generation.

Every Pi visited by candidate WHNF must occur in the stored kernel syntax,
and the final stored source must belong to the syntax fragment whose strict
Theory translation is known not to expose another Pi.  This strengthens
`storedSpine` only at its terminal node and still permits normalization inside
binder domains and at non-Pi terminal results. -/
def generationSpine :
    {context : Context} → {source : Expr} →
      CandidateExprTrace context source → Bool
  | _, _, .terminal _ source _ _ _ _ => generationTerminalSource source
  | _, _, .forallE _ source _ name domain body binderInfo _ _ _ _ _ _
      bodyCandidate =>
    Expr.structuralEq source (.forallE name domain body binderInfo) &&
      generationSpine bodyCandidate

/-- The complete generation gate in particular preserves every visited Pi. -/
theorem generationSpine_storedSpine
    (trace : CandidateExprTrace context source)
    (generation : trace.generationSpine = true) :
    trace.storedSpine = true := by
  induction trace with
  | terminal => rfl
  | forallE context source inferred name domain body binderInfo fresh
      annotations annotationsEq checked valid domainCandidate bodyCandidate
      domainIH bodyIH =>
    simp only [generationSpine, Bool.and_eq_true] at generation
    simp [storedSpine, generation.1, bodyIH generation.2]

/--
info: 'Lean4Lean.AddInductive.CandidateExprTrace.generationSpine_storedSpine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CandidateExprTrace.generationSpine_storedSpine

/-- Number of stored Pi binders on the main (body) path of a candidate. -/
def spineLength :
    {context : Context} → {source : Expr} →
      CandidateExprTrace context source → Nat
  | _, _, .terminal .. => 0
  | _, _, .forallE _ _ _ _ _ _ _ _ _ _ _ _ _ bodyCandidate =>
    bodyCandidate.spineLength + 1

/-- The exact full-check observation at the root of a candidate trace. -/
def rootCheck :
    CandidateExprTrace context source →
      CandidateCheckTypeObservation context source
  | .terminal _ _ inferred _ checked _ => ⟨inferred, checked⟩
  | .forallE _ _ inferred _ _ _ _ _ _ _ checked _ _ _ =>
    ⟨inferred, checked⟩

/-- The exact WHNF result at the root, before recursively normalized domains
and bodies are reassembled into `view`. -/
def rootWhnf : CandidateExprTrace context source → Expr
  | .terminal _ _ _ result _ _ => result
  | .forallE _ _ _ name domain body binderInfo _ _ _ _ _ _ _ =>
    .forallE name domain body binderInfo

theorem rootWhnf_valid (candidate : CandidateExprTrace context source) :
    CandidateWhnfStep.Valid ⟨context, source, candidate.rootWhnf⟩ := by
  cases candidate <;> assumption

/-- Reader context reached after following the complete main Π spine. -/
def terminalContext : CandidateExprTrace context source → Context
  | .terminal context _ _ _ _ _ => context
  | .forallE _ _ _ _ _ _ _ _ _ _ _ _ _ bodyCandidate =>
    bodyCandidate.terminalContext

theorem terminalContext_lparams
    (candidate : CandidateExprTrace context source) :
    candidate.terminalContext.lparams = context.lparams := by
  induction candidate with
  | terminal => rfl
  | forallE context source inferred name domain body binderInfo fresh
      annotations annotationsEq checked valid domainCandidate bodyCandidate
      domain_ih body_ih =>
    simpa [terminalContext, Context.pushLocalDecl] using body_ih

/-- Following the main candidate Π spine preserves the kernel environment. -/
theorem terminalContext_env
    (candidate : CandidateExprTrace context source) :
    candidate.terminalContext.env = context.env := by
  induction candidate with
  | terminal => rfl
  | forallE context source inferred name domain body binderInfo fresh
      annotations annotationsEq checked valid domainCandidate bodyCandidate
      domain_ih body_ih =>
    simpa [terminalContext, Context.pushLocalDecl] using body_ih

/-- Following the main candidate Π spine preserves the primitive-name
policy used by family declaration. -/
theorem terminalContext_allowPrimitive
    (candidate : CandidateExprTrace context source) :
    candidate.terminalContext.allowPrimitive = context.allowPrimitive := by
  induction candidate with
  | terminal => rfl
  | forallE context source inferred name domain body binderInfo fresh
      annotations annotationsEq checked valid domainCandidate bodyCandidate
      domain_ih body_ih =>
    simpa [terminalContext, Context.pushLocalDecl] using body_ih

/-- Following the main candidate Π spine changes only the local context and
name generator; it preserves the checker safety mode. -/
theorem terminalContext_safety
    (candidate : CandidateExprTrace context source) :
    candidate.terminalContext.safety = context.safety := by
  induction candidate with
  | terminal => rfl
  | forallE context source inferred name domain body binderInfo fresh
      annotations annotationsEq checked valid domainCandidate bodyCandidate
      domain_ih body_ih =>
    simpa [terminalContext, Context.pushLocalDecl] using body_ih

/-- Following the main candidate Π spine preserves the checker fuel
configuration. -/
theorem terminalContext_fuel
    (candidate : CandidateExprTrace context source) :
    candidate.terminalContext.fuel = context.fuel := by
  induction candidate with
  | terminal => rfl
  | forallE context source inferred name domain body binderInfo fresh
      annotations annotationsEq checked valid domainCandidate bodyCandidate
      domain_ih body_ih =>
    simpa [terminalContext, Context.pushLocalDecl] using body_ih

/-- Non-Π result reached after following the complete main Π spine. -/
def terminalResult : CandidateExprTrace context source → Expr
  | .terminal _ _ _ result _ _ => result
  | .forallE _ _ _ _ _ _ _ _ _ _ _ _ _ bodyCandidate =>
    bodyCandidate.terminalResult

/-- The first `count` local expressions allocated along the main Π spine.
These are exactly the expressions accumulated as inductive parameters when
`count` is the declaration's `nparams`. -/
def parameterList :
    (count : Nat) → CandidateExprTrace context source → List Expr
  | 0, _ => []
  | _ + 1, .terminal .. => []
  | count + 1,
      .forallE context _ _ _ _ _ _ _ _ _ _ _ _ bodyCandidate =>
    context.freshExpr :: bodyCandidate.parameterList count

theorem parameterList_length
    (candidate : CandidateExprTrace context source)
    (hcount : count ≤ candidate.spineLength) :
    (candidate.parameterList count).length = count := by
  induction candidate generalizing count with
  | terminal =>
    simp [spineLength] at hcount
    subst count
    rfl
  | forallE context source inferred name domain body binderInfo fresh
      annotations annotationsEq checked valid domainCandidate bodyCandidate
      domain_ih body_ih =>
    cases count with
    | zero => rfl
    | succ count =>
      simp only [parameterList, List.length_cons]
      rw [body_ih]
      simpa [spineLength] using hcount

/-- Candidate traversals started from the same name generator allocate the
same free variables at every common main-spine position.

The binder names, domains, and semantic observations may differ.  Only the
reader's name-generator state selects `parameterList`, and every Pi step
advances that state in the same way. -/
theorem parameterList_eq_of_ngen_eq
    {leftContext rightContext : Context}
    {leftSource rightSource : Expr}
    (left : CandidateExprTrace leftContext leftSource)
    (right : CandidateExprTrace rightContext rightSource)
    (ngen_eq : leftContext.ngen = rightContext.ngen)
    (leftCount : count ≤ left.spineLength)
    (rightCount : count ≤ right.spineLength) :
    left.parameterList count = right.parameterList count := by
  induction count generalizing leftContext rightContext leftSource rightSource with
  | zero => rfl
  | succ count ih =>
    cases left with
    | terminal => simp [CandidateExprTrace.spineLength] at leftCount
    | @forallE leftContext leftSource leftInferred leftName leftDomain
        leftBody leftBinderInfo leftFresh leftAnnotations leftAnnotationsEq
        leftChecked leftValid leftDomainCandidate leftBodyCandidate =>
      cases right with
      | terminal => simp [CandidateExprTrace.spineLength] at rightCount
      | @forallE rightContext rightSource rightInferred rightName rightDomain
          rightBody rightBinderInfo rightFresh rightAnnotations
          rightAnnotationsEq rightChecked rightValid rightDomainCandidate
          rightBodyCandidate =>
        simp only [CandidateExprTrace.parameterList]
        have fresh_eq : leftContext.freshExpr = rightContext.freshExpr := by
          simp [Context.freshExpr, Context.freshFVarId, ngen_eq]
        have tail_eq := ih leftBodyCandidate rightBodyCandidate
          (by simp [Context.pushLocalDecl, ngen_eq])
          (by simpa [CandidateExprTrace.spineLength] using leftCount)
          (by simpa [CandidateExprTrace.spineLength] using rightCount)
        exact (congrArg (fun head => head ::
          leftBodyCandidate.parameterList count) fresh_eq).trans
            (congrArg (fun tail => rightContext.freshExpr :: tail) tail_eq)

/-- Every annotation choice on the main Π spine matches the transparent
peeling operation used by `checkInductiveTypes`.  This is operational
provenance, separate from the semantic raw/consumed equality stored at each
candidate node. -/
def validationAnnotations :
    CandidateExprTrace context source → Prop
  | .terminal .. => True
  | .forallE _ _ _ _ _ _ _ _ annotations _ _ _ _ bodyCandidate =>
    annotations.Matches ∧ bodyCandidate.validationAnnotations

/-- Replay the inner family-telescope validator from a candidate's exact main
Π spine. The first `remaining` binders extend `stats.params`; every later
binder contributes an index. The theorem is independent of any fixture and
preserves the exact terminal reader context reached by the executable loop. -/
theorem checkInductiveTypes_loop_of_candidate
    (candidate : CandidateExprTrace context source)
    (stats : InductiveStats) (nparams i nindices fuel : Nat)
    (remaining : Nat) (k : Expr → InductiveStats → Nat → M α)
    (hi : i + remaining = nparams)
    (hcount : remaining ≤ candidate.spineLength)
    (hfuel : candidate.spineLength < fuel)
    (hempty : stats.indConsts.isEmpty = true)
    (hannotations : candidate.validationAnnotations)
    (hterminal : candidate.terminalResult.isForall = false) :
    checkInductiveTypes.loopInd.loop nparams stats candidate.rootWhnf
        i nindices fuel k context =
      k candidate.terminalResult
        { stats with
          params := stats.params ++
            (candidate.parameterList remaining).toArray }
        (nindices + (candidate.spineLength - remaining))
        candidate.terminalContext := by
  induction candidate generalizing i nindices fuel remaining stats with
  | terminal context source inferred result checked valid =>
    simp only [spineLength] at hcount hfuel
    have hremaining : remaining = 0 := by omega
    subst remaining
    have hi' : i = nparams := by omega
    subst i
    cases stats
    cases fuel with
    | zero => omega
    | succ fuel =>
      cases result <;>
        simp_all [rootWhnf, terminalResult, terminalContext, parameterList,
          spineLength, checkInductiveTypes.loopInd.loop, Expr.isForall]
  | forallE context source inferred name domain body binderInfo fresh
      annotations annotationsEq checked valid domainCandidate bodyCandidate
      domain_ih body_ih =>
    rcases hannotations with ⟨hmatch, hbodyAnnotations⟩
    cases remaining with
    | zero =>
      have hi' : i = nparams := by omega
      subst i
      have hbodyFuel : bodyCandidate.spineLength < fuel - 1 := by
        simp only [spineLength] at hfuel
        omega
      have hbodyCount : 0 ≤ bodyCandidate.spineLength := Nat.zero_le _
      have hvalid := bodyCandidate.rootWhnf_valid
      change TypeChecker.M.run _ _ _ _ _
          (TypeChecker.whnf (body.instantiate1 context.freshExpr)) =
        .ok bodyCandidate.rootWhnf at hvalid
      rw [show fuel = (fuel - 1) + 1 by omega]
      simp only [rootWhnf, checkInductiveTypes.loopInd.loop,
        Nat.lt_irrefl, if_false, withLocalDecl_apply]
      rw [← hmatch]
      simp only [ReaderT.bind, Bind.bind, liftTypeChecker_apply]
      rw [hvalid]
      simp only [Except.bind]
      rw [body_ih stats nparams (nindices + 1) (fuel - 1) 0 rfl
        hbodyCount hbodyFuel hempty hbodyAnnotations hterminal]
      simp [terminalResult, terminalContext, parameterList, spineLength,
        Nat.add_comm, Nat.add_assoc]
    | succ remaining =>
      have hil : i < nparams := by omega
      have hbodyCount : remaining ≤ bodyCandidate.spineLength := by
        simp only [spineLength] at hcount
        omega
      have hbodyFuel : bodyCandidate.spineLength < fuel - 1 := by
        simp only [spineLength] at hfuel
        omega
      have hvalid := bodyCandidate.rootWhnf_valid
      change TypeChecker.M.run _ _ _ _ _
          (TypeChecker.whnf (body.instantiate1 context.freshExpr)) =
        .ok bodyCandidate.rootWhnf at hvalid
      rw [show fuel = (fuel - 1) + 1 by omega]
      simp only [rootWhnf, checkInductiveTypes.loopInd.loop, hil, if_true,
        hempty, withLocalDecl_apply]
      rw [← hmatch]
      simp only [ReaderT.bind, Bind.bind, liftTypeChecker_apply]
      rw [hvalid]
      simp only [Except.bind]
      rw [body_ih { stats with
          params := stats.params.push context.freshExpr }
        (i + 1) nindices (fuel - 1) remaining (by omega)
        hbodyCount hbodyFuel (by simpa using hempty) hbodyAnnotations
        hterminal]
      simp [terminalResult, terminalContext, parameterList, spineLength]

/-- A candidate main spine which ends before the declared parameter boundary
cannot be the first-family telescope of a successful validator run.  This is
the converse failure seam to `checkInductiveTypes_loop_of_candidate`: it does
not assume enough inductive fuel, because exhausting that fuel is itself a
failure. -/
theorem checkInductiveTypes_loop_not_ok_of_candidate_tooFew
    (candidate : CandidateExprTrace context source)
    (stats : InductiveStats) (nparams i nindices fuel : Nat)
    (k : Expr → InductiveStats → Nat → M α)
    (hi : i + candidate.spineLength < nparams)
    (hempty : stats.indConsts.isEmpty = true)
    (hannotations : candidate.validationAnnotations)
    (hterminal : candidate.terminalResult.isForall = false) :
    ∀ result,
      checkInductiveTypes.loopInd.loop nparams stats candidate.rootWhnf
          i nindices fuel k context ≠ .ok result := by
  induction candidate generalizing i nindices fuel stats with
  | terminal context source inferred terminal checked valid =>
      intro output success
      cases fuel with
      | zero =>
          simp [checkInductiveTypes.loopInd.loop, throw, throwThe,
            MonadExceptOf.throw] at success
      | succ fuel =>
          have hne : i ≠ nparams := by omega
          cases terminal <;>
            simp_all [rootWhnf, terminalResult, spineLength,
              checkInductiveTypes.loopInd.loop, Expr.isForall, ReaderT.bind,
              Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  | forallE context source inferred name domain body binderInfo fresh
      annotations annotationsEq checked valid domainCandidate bodyCandidate
      domain_ih body_ih =>
      rcases hannotations with ⟨hmatch, hbodyAnnotations⟩
      intro output success
      cases fuel with
      | zero =>
          simp [checkInductiveTypes.loopInd.loop, throw, throwThe,
            MonadExceptOf.throw] at success
      | succ fuel =>
          have hil : i < nparams := by
            simp only [spineLength] at hi
            omega
          have hbodyTooFew :
              i + 1 + bodyCandidate.spineLength < nparams := by
            simp only [spineLength] at hi
            omega
          have hvalid := bodyCandidate.rootWhnf_valid
          change TypeChecker.M.run _ _ _ _ _
              (TypeChecker.whnf (body.instantiate1 context.freshExpr)) =
            .ok bodyCandidate.rootWhnf at hvalid
          simp only [rootWhnf, checkInductiveTypes.loopInd.loop, hil,
            if_true, hempty, withLocalDecl_apply] at success
          rw [← hmatch] at success
          simp only [ReaderT.bind, Bind.bind, liftTypeChecker_apply] at success
          rw [hvalid] at success
          simp only [Except.bind] at success
          exact body_ih
            (stats :=
              { stats with params := stats.params.push context.freshExpr })
            (i := i + 1) (nindices := nindices) (fuel := fuel)
            hbodyTooFew (by simpa using hempty) hbodyAnnotations hterminal
            output success

/-- Exhausting the family validator's telescope fuel before the retained
candidate reaches its terminal node cannot produce a successful continuation.
This is the fuel counterpart of
`checkInductiveTypes_loop_not_ok_of_candidate_tooFew`; it is restricted to
the first family, whose shared-parameter accumulator is still empty. -/
theorem checkInductiveTypes_loop_not_ok_of_candidate_fuel
    (candidate : CandidateExprTrace context source)
    (stats : InductiveStats) (nparams i nindices fuel : Nat)
    (k : Expr → InductiveStats → Nat → M α)
    (hfuel : fuel ≤ candidate.spineLength)
    (hempty : stats.indConsts.isEmpty = true)
    (hannotations : candidate.validationAnnotations) :
    ∀ result,
      checkInductiveTypes.loopInd.loop nparams stats candidate.rootWhnf
          i nindices fuel k context ≠ .ok result := by
  induction candidate generalizing i nindices fuel stats with
  | terminal context source inferred terminal checked valid =>
      intro output success
      simp only [spineLength] at hfuel
      have hfuel_zero : fuel = 0 := by omega
      subst fuel
      simp [checkInductiveTypes.loopInd.loop, throw, throwThe,
        MonadExceptOf.throw] at success
  | forallE context source inferred name domain body binderInfo fresh
      annotations annotationsEq checked valid domainCandidate bodyCandidate
      domain_ih body_ih =>
      rcases hannotations with ⟨hmatch, hbodyAnnotations⟩
      intro output success
      cases fuel with
      | zero =>
          simp [checkInductiveTypes.loopInd.loop, throw, throwThe,
            MonadExceptOf.throw] at success
      | succ fuel =>
          have hbodyFuel : fuel ≤ bodyCandidate.spineLength := by
            simp only [spineLength] at hfuel
            omega
          have hvalid := bodyCandidate.rootWhnf_valid
          change TypeChecker.M.run _ _ _ _ _
              (TypeChecker.whnf (body.instantiate1 context.freshExpr)) =
            .ok bodyCandidate.rootWhnf at hvalid
          by_cases hil : i < nparams
          · simp only [rootWhnf, checkInductiveTypes.loopInd.loop, hil,
              if_true, hempty, withLocalDecl_apply] at success
            rw [← hmatch] at success
            simp only [ReaderT.bind, Bind.bind, liftTypeChecker_apply]
              at success
            rw [hvalid] at success
            simp only [Except.bind] at success
            exact body_ih
              (stats := { stats with
                params := stats.params.push context.freshExpr })
              (i := i + 1) (nindices := nindices) (fuel := fuel)
              hbodyFuel (by simpa using hempty) hbodyAnnotations output
              success
          · simp only [rootWhnf, checkInductiveTypes.loopInd.loop, hil,
              if_false, withLocalDecl_apply] at success
            rw [← hmatch] at success
            simp only [ReaderT.bind, Bind.bind, liftTypeChecker_apply]
              at success
            rw [hvalid] at success
            simp only [Except.bind] at success
            exact body_ih (stats := stats) (i := i)
              (nindices := nindices + 1) (fuel := fuel) hbodyFuel hempty
              hbodyAnnotations output success

/-- A successful nonempty family-validation block contains at least the
declared number of parameter binders in its first exact candidate spine.  The
proof uses the validator's real first-family call and the candidate builder's
annotation provenance; no terminal counter assertion is read backwards. -/
theorem nparams_le_spineLength_of_firstFamilyValidation
    (indType : InductiveType) (indTypes : List InductiveType)
    (candidate : CandidateExprTrace context indType.type)
    (nparams : Nat) (k : InductiveStats → M α) (output : α)
    (hannotations : candidate.validationAnnotations)
    (hterminal : candidate.terminalResult = .sort resultLevel)
    (success : checkInductiveTypes nparams (indType :: indTypes).toArray
      k context = .ok output) :
    nparams ≤ candidate.spineLength := by
  apply Classical.byContradiction
  intro hcount
  have tooFew : candidate.spineLength < nparams := by omega
  have hterminalForall : candidate.terminalResult.isForall = false := by
    rw [hterminal]
    rfl
  have hcheck := candidate.rootCheck.valid
  have hwhnf := candidate.rootWhnf_valid
  change TypeChecker.M.run context.env context.safety context.lctx
      context.lparams context.fuel (TypeChecker.checkType indType.type) =
    .ok candidate.rootCheck.inferred at hcheck
  change TypeChecker.M.run context.env context.safety context.lctx
      context.lparams context.fuel (TypeChecker.whnf indType.type) =
    .ok candidate.rootWhnf at hwhnf
  unfold checkInductiveTypes at success
  simp only [readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, Pure.pure, Except.pure, Except.bind] at success
  rw [checkInductiveTypes.loopInd.eq_1] at success
  have hsize : 0 < (indType :: indTypes).toArray.size := by simp
  rw [dif_pos hsize] at success
  rw [show (indType :: indTypes).toArray[0] = indType by rfl] at success
  simp only [readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, Pure.pure, Except.pure, Except.bind,
    liftExcept_apply, liftTypeChecker_apply]
    at success
  cases hclosed : context.env.checkNoMVarNoFVar indType.name indType.type with
  | error error =>
      rw [hclosed] at success
      contradiction
  | ok _ =>
      rw [hclosed, hcheck, hwhnf] at success
      exact candidate.checkInductiveTypes_loop_not_ok_of_candidate_tooFew
        (stats := InductiveStats.initial (context.lparams.map .param))
        (nparams := nparams) (i := 0) (nindices := 0)
        (fuel := context.fuel.inductiveFuel) _ (by simpa using tooFew) rfl
        hannotations hterminalForall output success

/-- Exact singleton statistics selected by a candidate family spine with an
arbitrary parameter/index split. -/
def singletonCandidateInductiveStats
    (indType : InductiveType)
    (candidate : CandidateExprTrace context indType.type)
    (nparams : Nat) (resultLevel : Level) : InductiveStats where
  lctx := candidate.terminalContext.lctx
  levels := context.lparams.map .param
  resultLevel := resultLevel
  nindices := #[candidate.spineLength - nparams]
  indConsts := #[.const indType.name (context.lparams.map .param)]
  params := (candidate.parameterList nparams).toArray
  isNotZero := resultLevel.isNeverZero

/-- A source-indexed candidate family spine discharges the complete singleton
family-validation pass for any number of parameters and indices.  The result
records the same local expressions, terminal context, index count, universe,
and family constant selected by the executable validator. -/
theorem checkInductiveTypes_singleton_of_candidate
    (indType : InductiveType)
    (candidate : CandidateExprTrace context indType.type)
    (nparams : Nat) (resultLevel : Level)
    (k : InductiveStats → M α)
    (hclosed :
      context.env.checkNoMVarNoFVar indType.name indType.type = .ok ())
    (hcount : nparams ≤ candidate.spineLength)
    (hfuel : candidate.spineLength < context.fuel.inductiveFuel)
    (hannotations : candidate.validationAnnotations)
    (hterminal : candidate.terminalResult = .sort resultLevel)
    (hensure :
      TypeChecker.M.run candidate.terminalContext.env
          candidate.terminalContext.safety candidate.terminalContext.lctx
          candidate.terminalContext.lparams candidate.terminalContext.fuel
          (TypeChecker.ensureSort (.sort resultLevel)) =
        .ok (.sort resultLevel)) :
    checkInductiveTypes nparams #[indType] k context =
      k (candidate.singletonCandidateInductiveStats
        indType nparams resultLevel) candidate.terminalContext := by
  have hcheck := candidate.rootCheck.valid
  have hwhnf := candidate.rootWhnf_valid
  change TypeChecker.M.run context.env context.safety context.lctx
      context.lparams context.fuel (TypeChecker.checkType indType.type) =
    .ok candidate.rootCheck.inferred at hcheck
  change TypeChecker.M.run context.env context.safety context.lctx
      context.lparams context.fuel (TypeChecker.whnf indType.type) =
    .ok candidate.rootWhnf at hwhnf
  have hterminalForall : candidate.terminalResult.isForall = false := by
    rw [hterminal]
    rfl
  have hterminalLparams :
      candidate.terminalContext.lparams = context.lparams :=
    candidate.terminalContext_lparams
  have hparameterLength := candidate.parameterList_length hcount
  unfold checkInductiveTypes
  simp only [readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, Pure.pure, Except.pure, Except.bind]
  rw [checkInductiveTypes.loopInd.eq_1]
  have hsize : 0 < #[indType].size := by simp
  rw [dif_pos hsize]
  rw [show #[indType][0] = indType by rfl]
  simp only [readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, Pure.pure, Except.pure, Except.bind,
    liftTypeChecker_apply, hclosed, hcheck, hwhnf]
  rw [candidate.checkInductiveTypes_loop_of_candidate
    (stats := InductiveStats.initial (context.lparams.map .param))
    (nparams := nparams) (i := 0) (nindices := 0)
    (fuel := context.fuel.inductiveFuel) (remaining := nparams)
    (hi := Nat.zero_add nparams) (hcount := hcount) (hfuel := hfuel)
    (hempty := rfl) (hannotations := hannotations)
    (hterminal := hterminalForall)]
  rw [hterminal]
  simp only [ReaderT.bind, Bind.bind, liftTypeChecker_apply]
  rw [hensure]
  simp only [Except.bind]
  rw [if_pos (show ((InductiveStats.initial
      (List.map Level.param context.lparams)).indConsts).isEmpty = true from
    rfl)]
  simp only [Expr.sortLevel!, InductiveStats.initial, Nat.zero_add]
  simp only [ReaderT.bind, Bind.bind, Except.pure, Except.bind]
  rw [checkInductiveTypes.loopInd.eq_1]
  have hdone : ¬1 < #[indType].size := by simp
  rw [dif_neg hdone]
  simp only [readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, Pure.pure, Except.pure, Except.bind]
  simp [singletonCandidateInductiveStats, hterminalLparams,
    hparameterLength]

/-- Exact successful singleton family-validation execution retained at the
candidate selected by `buildNormalizationCandidate`.

The executable validator owns the parameter/index split, result universe,
statistics, and terminal reader context. Keeping the universally quantified
continuation equation makes this a decomposition of the real
`checkInductiveTypes` call rather than a fixture-specific success flag. The
semantic interpretation of the retained candidate remains in Verify. -/
structure FamilyValidationRun
    (indType : InductiveType)
    {context : Context}
    (candidate : CandidateExprTrace context indType.type) where
  nparams : Nat
  resultLevel : Level
  stats : InductiveStats
  stats_eq : stats = candidate.singletonCandidateInductiveStats
    indType nparams resultLevel
  terminal_eq : candidate.terminalResult = Expr.sort resultLevel
  run : ∀ {α} (k : InductiveStats → M α),
    checkInductiveTypes nparams #[indType] k context =
      k stats candidate.terminalContext

/-- The retained singleton validation run exposes exactly the candidate view
parameter expressions selected by the executable family pass. -/
def FamilyValidationRun.parameters
    (run : FamilyValidationRun indType candidate) : List Expr :=
  candidate.parameterList run.nparams

/-- The retained singleton validation run exposes the number of candidate
view indices following the selected parameter prefix. -/
def FamilyValidationRun.numIndices
    (run : FamilyValidationRun indType candidate) : Nat :=
  candidate.spineLength - run.nparams

/-- Candidate expression reconstructed from the traced WHNF/Pi tree. -/
def view : CandidateExprTrace context source → Expr
  | .terminal _ _ _ result _ _ => result
  | .forallE context _ _ name _ _ binderInfo _ _ _ _ _ domain body =>
    .forallE name domain.view
      (body.view.abstract #[context.freshExpr]) binderInfo

/-- Preorder list of all retained checker observations. -/
def steps : CandidateExprTrace context source → List CandidateWhnfStep
  | .terminal context source _ result _ _ => [{ context, source, result }]
  | .forallE context source _ name domain body binderInfo _ _ _ _ _
      domainCandidate bodyCandidate =>
    { context, source,
      result := .forallE name domain body binderInfo } ::
      domainCandidate.steps ++ bodyCandidate.steps

/-- Preorder list of all retained full-check observations. -/
def checkSteps : CandidateExprTrace context source → List CandidateCheckTypeStep
  | .terminal context source inferred _ _ _ =>
    [{ context, source, inferred }]
  | .forallE context source inferred _ _ _ _ _ _ _ _ _
      domainCandidate bodyCandidate =>
    { context, source, inferred } ::
      domainCandidate.checkSteps ++ bodyCandidate.checkSteps

/-- Preorder list of all retained binder-domain equality observations. -/
def isDefEqSteps :
    CandidateExprTrace context source → List CandidateIsDefEqStep
  | .terminal .. => []
  | .forallE context _ _ _ domain _ _ _ annotations _ _ _
      domainCandidate bodyCandidate =>
    { context, lhs := domain, rhs := annotations.consumed } ::
      domainCandidate.isDefEqSteps ++ bodyCandidate.isDefEqSteps

/-- Every retained WHNF observation is an exact checker execution. -/
theorem allValid : (candidate : CandidateExprTrace context source) →
    ∀ step ∈ candidate.steps, step.Valid
  | .terminal context source _ result _ valid, step, h => by
    simp only [steps, List.mem_singleton] at h
    subst step
    exact valid
  | .forallE _ _ _ _ _ _ _ _ _ _ _ valid domain body, step, h => by
    simp only [steps, List.mem_cons, List.mem_append] at h
    rcases h with (rfl | h) | h
    · exact valid
    · exact domain.allValid step h
    · exact body.allValid step h

/-- Every retained full-check observation is an exact checker execution. -/
theorem allChecksValid : (candidate : CandidateExprTrace context source) →
    ∀ step ∈ candidate.checkSteps, step.Valid
  | .terminal context source inferred _ checked _, step, h => by
    simp only [checkSteps, List.mem_singleton] at h
    subst step
    exact checked
  | .forallE _ _ _ _ _ _ _ _ _ _ checked _ domain body, step, h => by
    simp only [checkSteps, List.mem_cons, List.mem_append] at h
    rcases h with (rfl | h) | h
    · exact checked
    · exact domain.allChecksValid step h
    · exact body.allChecksValid step h

/-- Every retained binder-domain equality is an exact successful checker
execution. -/
theorem allIsDefEqValid : (candidate : CandidateExprTrace context source) →
    ∀ step ∈ candidate.isDefEqSteps, step.Valid
  | .terminal .., step, h => by simp [isDefEqSteps] at h
  | .forallE _ _ _ _ _ _ _ _ _ annotationsEq _ _ domain body,
      step, h => by
    simp only [isDefEqSteps, List.mem_cons, List.mem_append] at h
    rcases h with (rfl | h) | h
    · exact annotationsEq
    · exact domain.allIsDefEqValid step h
    · exact body.allIsDefEqValid step h

end CandidateExprTrace

/-- Source-indexed trace for one candidate expression. The tree records the
full-check and WHNF observations at every inspected node and retains the exact
positional split through Pi domains and instantiated bodies. Every node
carries the exact checker-run equalities produced by
`observeCandidateCheckType` and `observeCandidateWhnf`; Theory translation and
semantic refinement are intentionally separate. -/
structure CandidateExpr (source : Expr) where
  context : Context
  trace : CandidateExprTrace context source

def CandidateExpr.view (candidate : CandidateExpr source) : Expr :=
  candidate.trace.view

def CandidateExpr.steps
    (candidate : CandidateExpr source) : List CandidateWhnfStep :=
  candidate.trace.steps

def CandidateExpr.checkSteps
    (candidate : CandidateExpr source) :
    List CandidateCheckTypeStep :=
  candidate.trace.checkSteps

def CandidateExpr.isDefEqSteps
    (candidate : CandidateExpr source) :
    List CandidateIsDefEqStep :=
  candidate.trace.isDefEqSteps

theorem CandidateExpr.step_valid
    (candidate : CandidateExpr source)
    (hstep : step ∈ candidate.steps) :
    step.Valid :=
  candidate.trace.allValid step hstep

theorem CandidateExpr.checkStep_valid
    (candidate : CandidateExpr source)
    (hstep : step ∈ candidate.checkSteps) :
    step.Valid :=
  candidate.trace.allChecksValid step hstep

theorem CandidateExpr.isDefEqStep_valid
    (candidate : CandidateExpr source)
    (hstep : step ∈ candidate.isDefEqSteps) :
    step.Valid :=
  candidate.trace.allIsDefEqValid step hstep

/-- Normalize exactly the expression positions inspected by inductive
analysis. Each node is fully checked and then exposed with the ordinary
checker `whnf`; Pi domains retain their raw syntax, while bodies are traversed
under the structurally certified annotation-consumed local declarations used
by kernel checking. Every raw/consumed domain pair is also checked by an exact
successful ordinary-checker `isDefEq` run. The traversal uses the checker's
configured recursion depth so that candidate observation does not impose a
stricter hidden depth bound than the checker runs it records.

The returned trace is only a candidate analysis view and operational
provenance. It is not stored in the kernel environment and acquires semantic
authority only after Verify reconstructs and refines every retained checker
run. -/
def buildCandidateExpr (e : Expr) : M (CandidateExpr e) := do
  let context ← readThe Context
  return ⟨context, ← loop context e context.fuel.recDepth⟩
where
  loop (context : Context) (e : Expr) :
      Nat → Except Exception (CandidateExprTrace context e)
    | 0 => throw .deepRecursion
    | fuel + 1 => do
      match observeCandidateCheckType context e with
      | .error err => throw err
      | .ok ⟨inferred, checked⟩ =>
        match observeCandidateWhnf context e with
        | .error err => throw err
        | .ok ⟨view, valid⟩ =>
          match view, valid with
          | .forallE name domain body binderInfo, valid =>
            match hfresh : context.lctx.find? context.freshFVarId with
            | some _ =>
              throw (Exception.other
                "normalization candidate generated a duplicate free variable")
            | none =>
              let annotations ← buildCandidateTypeAnnotations domain
              let ⟨annotationsEq⟩ ← observeCandidateIsDefEq
                context domain annotations.consumed
              let domainCandidate ← loop context domain fuel
              let bodyContext :=
                context.pushLocalDecl name binderInfo
                  annotations.consumed
              let bodyCandidate ← loop bodyContext
                (body.instantiate1 context.freshExpr) fuel
              return .forallE context e inferred name domain body
                binderInfo hfresh annotations annotationsEq checked valid
                domainCandidate bodyCandidate
          | result, valid =>
            return .terminal context e inferred result checked valid

/-- The additional recursive checker observations needed to normalize one
expression are executable in the exact reader context where the candidate
pass will inspect it.  This is deliberately narrower than successful
inductive validation: the ordinary validator does not recursively inspect Pi
domains with `buildCandidateExpr`. -/
def CandidateExpr.Observable (context : Context) (source : Expr) : Prop :=
  ∃ candidate : CandidateExpr source,
    buildCandidateExpr source context = .ok candidate

/-- One terminal recursive step of `buildCandidateExpr`, with its traversal
budget made explicit. This is the reusable reduction seam for exact producer
fixtures; all semantic evidence remains the ordinary checker executions
stored in the resulting trace. -/
theorem buildCandidateExpr_loop_of_whnf_nonForall
    (context : Context) (e inferred view : Expr) (fuel : Nat)
    (hcheck : CandidateCheckTypeStep.Valid
      ⟨context, e, inferred⟩)
    (hrun : CandidateWhnfStep.Valid ⟨context, e, view⟩)
    (hview : view.isForall = false) :
    buildCandidateExpr.loop context e (fuel + 1) =
      .ok (.terminal context e inferred view hcheck hrun) := by
  unfold buildCandidateExpr.loop
  rw [observeCandidateCheckType_of_run context e inferred hcheck]
  rw [observeCandidateWhnf_of_run context e view hrun]
  cases view <;>
    simp_all [Expr.isForall, Pure.pure, Except.pure]

/-- One forall recursive step of `buildCandidateExpr`, exposing the exact
child executions used at the decremented traversal budget. -/
theorem buildCandidateExpr_loop_of_whnf_forall
    (context : Context) (e inferred : Expr) (fuel : Nat)
    (name : Name) (domain body : Expr) (binderInfo : BinderInfo)
    (hfresh : context.lctx.find? context.freshFVarId = none)
    (annotations : CandidateTypeAnnotations domain)
    (hannotations :
      buildCandidateTypeAnnotations domain = .ok annotations)
    (hannotationsEq : CandidateIsDefEqStep.Valid
      ⟨context, domain, annotations.consumed⟩)
    (hcheck : CandidateCheckTypeStep.Valid
      ⟨context, e, inferred⟩)
    (hrun : CandidateWhnfStep.Valid
      ⟨context, e, .forallE name domain body binderInfo⟩)
    (domainCandidate : CandidateExprTrace context domain)
    (bodyCandidate : CandidateExprTrace
      (context.pushLocalDecl name binderInfo annotations.consumed)
      (body.instantiate1 context.freshExpr))
    (hdomain :
      buildCandidateExpr.loop context domain fuel =
        .ok domainCandidate)
    (hbody :
      buildCandidateExpr.loop
          (context.pushLocalDecl name binderInfo annotations.consumed)
          (body.instantiate1 context.freshExpr) fuel =
        .ok bodyCandidate) :
    buildCandidateExpr.loop context e (fuel + 1) =
      .ok (.forallE context e inferred name domain body binderInfo
        hfresh annotations hannotationsEq hcheck hrun
        domainCandidate bodyCandidate) := by
  unfold buildCandidateExpr.loop
  simp only [observeCandidateCheckType_of_run context e inferred hcheck,
    observeCandidateWhnf_of_run context e
      (.forallE name domain body binderInfo) hrun]
  split
  · simp_all
  · simp [Bind.bind, Except.bind, hannotations,
      observeCandidateIsDefEq_of_run context domain
        annotations.consumed hannotationsEq,
      hdomain, hbody, Pure.pure, Except.pure]

/-- Every annotation choice on a successfully built candidate main spine
comes from the transparent annotation builder used by the ordinary producer.
This recovers validator-replay provenance from the executable traversal
itself; callers do not supply an independent annotation premise. -/
theorem CandidateExprTrace.validationAnnotations_of_loop
    {context : Context} {source : Expr} {fuel : Nat}
    {candidate : CandidateExprTrace context source}
    (h : buildCandidateExpr.loop context source fuel = .ok candidate) :
    candidate.validationAnnotations := by
  fun_induction buildCandidateExpr.loop context source fuel <;>
    simp_all
  case case5 =>
    simp only [Bind.bind, Except.bind] at h
    repeat' split at h
    all_goals try simp_all [Functor.map, Except.map]
    repeat' split at h
    all_goals try simp_all
    subst candidate
    constructor
    · apply CandidateTypeAnnotations.matches_of_build
      assumption
    · apply_assumption
      assumption
  case case6 =>
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at h
    subst candidate
    trivial

/-- A successful ordinary candidate-expression call carries the complete
annotation provenance needed to replay family validation. -/
theorem CandidateExpr.validationAnnotations_of_build
    {context : Context} {source : Expr}
    {candidate : CandidateExpr source}
    (h : buildCandidateExpr source context = .ok candidate) :
    candidate.trace.validationAnnotations := by
  unfold buildCandidateExpr at h
  simp [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, Pure.pure, Except.bind, Except.pure] at h
  split at h <;> try simp_all
  simp [ReaderT.pure, Pure.pure, Except.pure] at h
  subst candidate
  apply CandidateExprTrace.validationAnnotations_of_loop
  assumption

/-- The context stored at the root of a successful expression candidate is
the exact reader context in which the ordinary builder was executed. -/
theorem CandidateExpr.context_eq_of_build
    {context : Context} {source : Expr}
    {candidate : CandidateExpr source}
    (h : buildCandidateExpr source context = .ok candidate) :
    candidate.context = context := by
  unfold buildCandidateExpr at h
  simp [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, Pure.pure, Except.bind, Except.pure] at h
  split at h <;> try simp_all
  simp [ReaderT.pure, Pure.pure, Except.pure] at h
  subst candidate
  rfl

/-- Erase the operational trace and retain only the analysis expression. -/
def normalizeCandidateExpr (e : Expr) : M Expr := do
  return (← buildCandidateExpr e).view

/-- A successful ordinary WHNF run to a non-Pi expression is exactly one
terminal step of the candidate traversal. This exposes the operational seam
used by Verify without duplicating the `ReaderT`/checker lift plumbing in
every certificate. -/
theorem buildCandidateExpr_of_whnf_nonForall
    (context : Context) (e inferred view : Expr)
    (hfuel : 0 < context.fuel.recDepth)
    (hcheck :
      TypeChecker.M.run context.env context.safety context.lctx
          context.lparams context.fuel (TypeChecker.checkType e) =
        .ok inferred)
    (hrun :
      TypeChecker.M.run context.env context.safety context.lctx
          context.lparams context.fuel (TypeChecker.whnf e) =
        .ok view)
    (hview : view.isForall = false) :
    buildCandidateExpr e context =
      .ok ⟨context, .terminal context e inferred view hcheck hrun⟩ := by
  cases hf : context.fuel.recDepth with
  | zero => omega
  | succ fuel =>
    cases hresult :
        TypeChecker.M.run context.env context.safety context.lctx
          context.lparams context.fuel (TypeChecker.whnf e) with
    | error err => simp [hresult] at hrun
    | ok result =>
      have : result = view := by simpa [hresult] using hrun
      subst result
      unfold buildCandidateExpr
      unfold buildCandidateExpr.loop
      simp [readThe, MonadReaderOf.read, ReaderT.read,
        ReaderT.bind, Bind.bind, Pure.pure, Except.bind, Except.pure,
        hf, observeCandidateCheckType_of_run context e inferred hcheck,
        observeCandidateWhnf_of_run context e view hrun]
      cases view <;>
        simp_all [ReaderT.pure, Pure.pure, Except.pure, Expr.isForall]

theorem normalizeCandidateExpr_of_whnf_nonForall
    (context : Context) (e inferred view : Expr)
    (hfuel : 0 < context.fuel.recDepth)
    (hcheck :
      TypeChecker.M.run context.env context.safety context.lctx
          context.lparams context.fuel (TypeChecker.checkType e) =
        .ok inferred)
    (hrun :
      TypeChecker.M.run context.env context.safety context.lctx
          context.lparams context.fuel (TypeChecker.whnf e) =
        .ok view)
    (hview : view.isForall = false) :
    normalizeCandidateExpr e context = .ok view := by
  simp [normalizeCandidateExpr, ReaderT.bind, Bind.bind,
    ReaderT.pure, Pure.pure, Except.bind, Except.pure,
    CandidateExpr.view, CandidateExprTrace.view,
    buildCandidateExpr_of_whnf_nonForall context e inferred view
      hfuel hcheck hrun hview]

/-- A dependent list retains the exact source position of each candidate. -/
inductive CandidateList {α : Type} (F : α → Type) : List α → Type
  | nil : CandidateList F []
  | cons : F a → CandidateList F as → CandidateList F (a :: as)

namespace CandidateList

def toList (f : (a : α) → F a → β) :
    CandidateList F source → List β
  | .nil => []
  | .cons head tail => f _ head :: tail.toList f

/-- Total first-position projection for a source-indexed nonempty candidate
list. -/
def head : CandidateList F (source :: sources) → F source
  | .cons head _ => head

/-- Eliminate a source-indexed singleton without a partial list operation. -/
def singleton : CandidateList F [source] → F source
  | .cons head .nil => head

/-- A source-indexed singleton list is completely determined by its total
singleton projection.  This eta law lets retained producer witnesses be
reindexed at staged singleton APIs without inspecting or replacing their
candidate payload. -/
theorem singleton_eta (candidates : CandidateList F [source]) :
    candidates = .cons candidates.singleton .nil := by
  cases candidates with
  | cons head tail =>
      cases tail
      rfl

end CandidateList

/-- Candidate for one constructor; its header is always taken from `source`. -/
structure CandidateConstructor (source : Constructor) where
  type : CandidateExpr source.type

def CandidateConstructor.view
    (candidate : CandidateConstructor source) : Constructor :=
  { source with type := candidate.type.view }

/-- Candidate for one family type, computed before raw family insertion. -/
structure CandidateFamilyType (source : InductiveType) where
  type : CandidateExpr source.type

/-- Source-ordered syntactic closure retained for the flattened family types
accepted by the detailed normalization prefix.  The two cached-expression
equations are exactly the data later needed to reconstruct `FVarsIn False`
without reasoning about how nested elimination produced the source list. -/
inductive FamilySourceClosedList : List InductiveType → Prop where
  | nil : FamilySourceClosedList []
  | cons
      (noMVar : source.type.hasMVar = false)
      (noFVar : source.type.hasFVar = false)
      (tail : FamilySourceClosedList sources) :
      FamilySourceClosedList (source :: sources)

/-- Executable syntactic-closure gate for every flattened family source. -/
def FamilySourceClosedList.check : List InductiveType → Bool
  | [] => true
  | source :: sources =>
      !source.type.hasMVar && !source.type.hasFVar &&
        FamilySourceClosedList.check sources

/-- A successful source-closure gate reconstructs its source-indexed proof. -/
theorem FamilySourceClosedList.of_check :
    (sources : List InductiveType) →
      FamilySourceClosedList.check sources = true →
        FamilySourceClosedList sources
  | [], _ => .nil
  | source :: sources, checked => by
      simp only [FamilySourceClosedList.check, Bool.and_eq_true,
        Bool.not_eq_true'] at checked
      exact .cons checked.1.1 checked.1.2
        (FamilySourceClosedList.of_check sources checked.2)

/-- Proof-carrying source closure evaluates back to the successful gate. -/
theorem FamilySourceClosedList.check_eq_true
    (closed : FamilySourceClosedList sources) :
    FamilySourceClosedList.check sources = true := by
  induction closed with
  | nil => rfl
  | cons noMVar noFVar tail ih =>
      simp [FamilySourceClosedList.check, noMVar, noFVar, ih]

/-- Source-indexed evidence that every retained family-type candidate reaches
a sort at the end of its main telescope.  The detailed normalization prefix
checks this exact payload before accepting a candidate block, so downstream
semantic staging does not need to reconstruct the validator's terminal
observer. -/
inductive CandidateFamilyTypeTerminalSortList :
    {sources : List InductiveType} →
      CandidateList CandidateFamilyType sources → Prop where
  | nil : CandidateFamilyTypeTerminalSortList .nil
  | cons
      (terminal : candidate.type.trace.terminalResult = .sort resultLevel)
      (tail : CandidateFamilyTypeTerminalSortList candidates) :
      CandidateFamilyTypeTerminalSortList (.cons candidate candidates)

/-- Executable terminal-sort gate for an exact dependent family-type list. -/
def CandidateFamilyTypeTerminalSortList.check :
    {sources : List InductiveType} →
      (candidates : CandidateList CandidateFamilyType sources) → Bool
  | [], .nil => true
  | _ :: _, .cons candidate candidates =>
      match candidate.type.trace.terminalResult with
      | .sort _ => CandidateFamilyTypeTerminalSortList.check candidates
      | _ => false

/-- A successful terminal gate reconstructs its exact source-indexed proof. -/
theorem CandidateFamilyTypeTerminalSortList.of_check :
    (candidates : CandidateList CandidateFamilyType sources) →
      CandidateFamilyTypeTerminalSortList.check candidates = true →
        CandidateFamilyTypeTerminalSortList candidates
  | .nil, _ => .nil
  | .cons candidate candidates, checked => by
      cases terminal_eq : candidate.type.trace.terminalResult <;>
        simp [CandidateFamilyTypeTerminalSortList.check, terminal_eq]
          at checked
      case sort resultLevel =>
        exact .cons terminal_eq
          (CandidateFamilyTypeTerminalSortList.of_check candidates checked)

/-- Proof-carrying terminal evidence evaluates back to the successful gate. -/
theorem CandidateFamilyTypeTerminalSortList.check_eq_true
    (terminals : CandidateFamilyTypeTerminalSortList candidates) :
    CandidateFamilyTypeTerminalSortList.check candidates = true := by
  induction terminals with
  | nil => rfl
  | cons terminal tail ih =>
      simp [CandidateFamilyTypeTerminalSortList.check, terminal, ih]

/-- Complete candidate for one family, with constructor traces computed only
after raw family insertion. -/
structure CandidateFamily (source : InductiveType) where
  familyType : CandidateFamilyType source
  constructors :
    CandidateList CandidateConstructor source.ctors

/-- Source-indexed evidence that every retained constructor candidate keeps
its complete Pi spine in the stored source syntax and ends in a terminal
whose strict Theory translation is syntactically non-Pi.  Mixed Theory
generation may normalize binder domains and terminal results, but it cannot
accept binders invented only by WHNF. -/
inductive CandidateConstructorGenerationSpineList :
    {sources : List Constructor} →
      CandidateList CandidateConstructor sources → Prop where
  | nil : CandidateConstructorGenerationSpineList .nil
  | cons
      (head : candidate.type.trace.generationSpine = true)
      (tail : CandidateConstructorGenerationSpineList candidates) :
      CandidateConstructorGenerationSpineList (.cons candidate candidates)

/-- Executable generation-spine gate for an exact dependent constructor
list. -/
def CandidateConstructorGenerationSpineList.check :
    {sources : List Constructor} →
      CandidateList CandidateConstructor sources → Bool
  | [], .nil => true
  | _ :: _, .cons candidate candidates =>
      candidate.type.trace.generationSpine &&
        CandidateConstructorGenerationSpineList.check candidates

/-- A successful constructor gate reconstructs its source-indexed proof. -/
theorem CandidateConstructorGenerationSpineList.of_check :
    (candidates : CandidateList CandidateConstructor sources) →
      CandidateConstructorGenerationSpineList.check candidates = true →
        CandidateConstructorGenerationSpineList candidates
  | .nil, _ => .nil
  | .cons candidate candidates, checked => by
      simp only [CandidateConstructorGenerationSpineList.check,
        Bool.and_eq_true] at checked
      exact .cons checked.1
        (CandidateConstructorGenerationSpineList.of_check candidates checked.2)

/-- Proof-carrying constructor spine evidence evaluates back to its gate. -/
theorem CandidateConstructorGenerationSpineList.check_eq_true
    (spines : CandidateConstructorGenerationSpineList candidates) :
    CandidateConstructorGenerationSpineList.check candidates = true := by
  induction spines with
  | nil => rfl
  | cons head tail ih =>
      simp [CandidateConstructorGenerationSpineList.check, head, ih]

/-- Source-indexed complete generation-spine evidence for every family type
and every one of its constructors in an accepted normalization candidate
block. -/
inductive CandidateFamilyGenerationSpineList :
    {sources : List InductiveType} →
      CandidateList CandidateFamily sources → Prop where
  | nil : CandidateFamilyGenerationSpineList .nil
  | cons
      (family : candidate.familyType.type.trace.generationSpine = true)
      (constructors : CandidateConstructorGenerationSpineList
        candidate.constructors)
      (tail : CandidateFamilyGenerationSpineList candidates) :
      CandidateFamilyGenerationSpineList (.cons candidate candidates)

/-- Executable generation-spine gate for an exact dependent family block. -/
def CandidateFamilyGenerationSpineList.check :
    {sources : List InductiveType} →
      CandidateList CandidateFamily sources → Bool
  | [], .nil => true
  | _ :: _, .cons candidate candidates =>
      (candidate.familyType.type.trace.generationSpine &&
        CandidateConstructorGenerationSpineList.check
          candidate.constructors) &&
          CandidateFamilyGenerationSpineList.check candidates

/-- A successful family-block gate reconstructs its source-indexed proof. -/
theorem CandidateFamilyGenerationSpineList.of_check :
    (candidates : CandidateList CandidateFamily sources) →
      CandidateFamilyGenerationSpineList.check candidates = true →
        CandidateFamilyGenerationSpineList candidates
  | .nil, _ => .nil
  | .cons candidate candidates, checked => by
      simp only [CandidateFamilyGenerationSpineList.check, Bool.and_eq_true]
        at checked
      exact .cons checked.1.1
        (CandidateConstructorGenerationSpineList.of_check
          candidate.constructors checked.1.2)
        (CandidateFamilyGenerationSpineList.of_check candidates checked.2)

/-- Proof-carrying family-block spine evidence evaluates back to its gate. -/
theorem CandidateFamilyGenerationSpineList.check_eq_true
    (spines : CandidateFamilyGenerationSpineList candidates) :
    CandidateFamilyGenerationSpineList.check candidates = true := by
  induction spines with
  | nil => rfl
  | cons family constructors tail ih =>
      simp [CandidateFamilyGenerationSpineList.check, family,
        constructors.check_eq_true, ih]

/-- Source-indexed evidence that every retained family candidate exposes the
complete declared parameter prefix.  This is kept separate from
`CandidateFamilyGenerationSpineList`: the latter certifies that WHNF did not
invent the stored generation telescope, while this list pins the minimum split
accepted by the earlier family validator. -/
inductive CandidateFamilyParameterSpineList (nparams : Nat) :
    {sources : List InductiveType} →
      CandidateList CandidateFamily sources → Prop where
  | nil : CandidateFamilyParameterSpineList nparams .nil
  | cons
      (family : nparams ≤ candidate.familyType.type.trace.spineLength)
      (tail : CandidateFamilyParameterSpineList nparams candidates) :
      CandidateFamilyParameterSpineList nparams (.cons candidate candidates)

/-- Executable parameter-prefix gate for an exact dependent family block. -/
def CandidateFamilyParameterSpineList.check (nparams : Nat) :
    {sources : List InductiveType} →
      CandidateList CandidateFamily sources → Bool
  | [], .nil => true
  | _ :: _, .cons candidate candidates =>
      decide (nparams ≤ candidate.familyType.type.trace.spineLength) &&
        CandidateFamilyParameterSpineList.check nparams candidates

/-- A successful parameter-prefix gate reconstructs its source-indexed proof. -/
theorem CandidateFamilyParameterSpineList.of_check (nparams : Nat) :
    (candidates : CandidateList CandidateFamily sources) →
      CandidateFamilyParameterSpineList.check nparams candidates = true →
        CandidateFamilyParameterSpineList nparams candidates
  | .nil, _ => .nil
  | .cons candidate candidates, checked => by
      simp only [CandidateFamilyParameterSpineList.check, Bool.and_eq_true,
        decide_eq_true_eq] at checked
      exact .cons checked.1
        (CandidateFamilyParameterSpineList.of_check nparams candidates checked.2)

/-- Proof-carrying family parameter-prefix evidence evaluates back to its
executable gate. -/
theorem CandidateFamilyParameterSpineList.check_eq_true
    (bounds : CandidateFamilyParameterSpineList nparams candidates) :
    CandidateFamilyParameterSpineList.check nparams candidates = true := by
  induction bounds with
  | nil => rfl
  | cons family tail ih =>
      simp [CandidateFamilyParameterSpineList.check, family, ih]

/--
info: 'Lean4Lean.AddInductive.CandidateFamilyParameterSpineList.of_check' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CandidateFamilyParameterSpineList.of_check

/--
info: 'Lean4Lean.AddInductive.CandidateFamilyParameterSpineList.check_eq_true' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CandidateFamilyParameterSpineList.check_eq_true

/-- Source-ordered agreement between the validator's completed index-count
array and the exact family candidates retained by normalization.  The
ordinal is explicit so recursive suffixes remain tied to their positions in
the whole declaration block. -/
inductive CandidateFamilyIndexCountList (stats : InductiveStats)
    (nparams : Nat) :
    (ordinal : Nat) → {sources : List InductiveType} →
      CandidateList CandidateFamily sources → Prop where
  | nil (ordinal : Nat) :
      CandidateFamilyIndexCountList stats nparams ordinal .nil
  | cons
      {ordinal : Nat} {source : InductiveType}
      {sources : List InductiveType}
      {candidate : CandidateFamily source}
      {candidates : CandidateList CandidateFamily sources}
      (head : stats.nindices[ordinal]? =
        some (candidate.familyType.type.trace.spineLength - nparams))
      (tail : CandidateFamilyIndexCountList stats nparams (ordinal + 1)
        candidates) :
      CandidateFamilyIndexCountList stats nparams ordinal
        (.cons candidate candidates)

/-- Executable audit for the exact positional family-index inventory. -/
def CandidateFamilyIndexCountList.check (stats : InductiveStats)
    (nparams : Nat) :
    (ordinal : Nat) → {sources : List InductiveType} →
      CandidateList CandidateFamily sources → Bool
  | _, _, .nil => true
  | ordinal, _, .cons candidate candidates =>
      stats.nindices[ordinal]? ==
          some (candidate.familyType.type.trace.spineLength - nparams) &&
        CandidateFamilyIndexCountList.check stats nparams (ordinal + 1)
          candidates

/-- A successful positional index audit reconstructs its proof-carrying
source-indexed inventory. -/
theorem CandidateFamilyIndexCountList.of_check (stats : InductiveStats)
    (nparams ordinal : Nat) :
    (candidates : CandidateList CandidateFamily sources) →
      CandidateFamilyIndexCountList.check stats nparams ordinal candidates =
          true →
        CandidateFamilyIndexCountList stats nparams ordinal candidates
  | .nil, _ => .nil ordinal
  | .cons candidate candidates, checked => by
      simp only [CandidateFamilyIndexCountList.check, Bool.and_eq_true,
        beq_iff_eq] at checked
      exact .cons checked.1
        (CandidateFamilyIndexCountList.of_check stats nparams (ordinal + 1)
          candidates checked.2)

/-- Proof-carrying positional index evidence evaluates back to the exact
audit performed by the strengthened normalization producer. -/
theorem CandidateFamilyIndexCountList.check_eq_true
    (counts : CandidateFamilyIndexCountList stats nparams ordinal
      candidates) :
    CandidateFamilyIndexCountList.check stats nparams ordinal candidates =
      true := by
  induction counts with
  | nil => rfl
  | cons head tail ih =>
      simp [CandidateFamilyIndexCountList.check, head, ih]

/-- The exact positional family-index inventory retained by a detailed
normalization execution. -/
theorem CandidateFamilyIndexCountList.head
    {source : InductiveType} {sources : List InductiveType}
    {candidate : CandidateFamily source}
    {candidates : CandidateList CandidateFamily sources}
    (counts : CandidateFamilyIndexCountList stats nparams ordinal
      (.cons candidate candidates)) :
    stats.nindices[ordinal]? =
      some (candidate.familyType.type.trace.spineLength - nparams) := by
  cases counts with
  | cons head tail => exact head

/-- Positional family-index evidence after the exact dependent head. -/
theorem CandidateFamilyIndexCountList.tail
    {source : InductiveType} {sources : List InductiveType}
    {candidate : CandidateFamily source}
    {candidates : CandidateList CandidateFamily sources}
    (counts : CandidateFamilyIndexCountList stats nparams ordinal
      (.cons candidate candidates)) :
    CandidateFamilyIndexCountList stats nparams (ordinal + 1) candidates := by
  cases counts with
  | cons head tail => exact tail

/-- Project the pre-family candidate spine from a complete dependent family
candidate list without erasing source indices or using a parallel list. -/
def CandidateList.familyTypes :
    {sources : List InductiveType} →
      CandidateList CandidateFamily sources →
      CandidateList CandidateFamilyType sources
  | [], .nil => .nil
  | _ :: _, .cons family families =>
    .cons family.familyType families.familyTypes

def CandidateFamily.view (candidate : CandidateFamily source) : InductiveType :=
  { source with
    type := candidate.familyType.type.view
    ctors := candidate.constructors.toList fun _ ctor => ctor.view }

def normalizeCandidateConstructor
    (ctor : Constructor) : M (CandidateConstructor ctor) := do
  return ⟨← buildCandidateExpr ctor.type⟩

/-- The root context stored by a successful constructor normalization is the
exact post-family reader context used for that traversal. -/
theorem CandidateConstructor.context_eq_of_normalize
    {context : Context} {source : Constructor}
    {candidate : CandidateConstructor source}
    (h : normalizeCandidateConstructor source context = .ok candidate) :
    candidate.type.context = context := by
  unfold normalizeCandidateConstructor at h
  simp only [ReaderT.bind, Bind.bind] at h
  cases hbuild : buildCandidateExpr source.type context with
  | error error =>
      simp [Except.bind, hbuild] at h
  | ok type =>
      simp [Except.bind, ReaderT.pure, Pure.pure, Except.pure, hbuild] at h
      subst candidate
      exact CandidateExpr.context_eq_of_build hbuild

/-- A successful constructor normalization carries the annotation provenance
of its underlying executable expression traversal. -/
theorem CandidateConstructor.validationAnnotations_of_normalize
    {context : Context} {source : Constructor}
    {candidate : CandidateConstructor source}
    (h : normalizeCandidateConstructor source context = .ok candidate) :
    candidate.type.trace.validationAnnotations := by
  unfold normalizeCandidateConstructor at h
  simp only [ReaderT.bind, Bind.bind] at h
  cases hbuild : buildCandidateExpr source.type context with
  | error error =>
      simp [Except.bind, hbuild] at h
  | ok type =>
      simp [Except.bind, ReaderT.pure, Pure.pure, Except.pure, hbuild] at h
      subst candidate
      exact type.validationAnnotations_of_build hbuild

def normalizeCandidateFamilyType
    (indType : InductiveType) : M (CandidateFamilyType indType) := do
  return ⟨← buildCandidateExpr indType.type⟩

/-- A successful family-type normalization carries the annotation provenance
of its underlying executable expression traversal. -/
theorem CandidateFamilyType.validationAnnotations_of_normalize
    {context : Context} {source : InductiveType}
    {candidate : CandidateFamilyType source}
    (h : normalizeCandidateFamilyType source context = .ok candidate) :
    candidate.type.trace.validationAnnotations := by
  unfold normalizeCandidateFamilyType at h
  simp only [ReaderT.bind, Bind.bind] at h
  cases hbuild : buildCandidateExpr source.type context with
  | error error =>
      simp [Except.bind, hbuild] at h
  | ok type =>
      simp [Except.bind, ReaderT.pure, Pure.pure, Except.pure, hbuild] at h
      subst candidate
      exact type.validationAnnotations_of_build hbuild

/-- The root context stored by a successful family-type normalization is the
exact pre-family reader context used for that traversal. -/
theorem CandidateFamilyType.context_eq_of_normalize
    {context : Context} {source : Lean.InductiveType}
    {candidate : CandidateFamilyType source}
    (h : normalizeCandidateFamilyType source context = .ok candidate) :
    candidate.type.context = context := by
  unfold normalizeCandidateFamilyType at h
  simp only [ReaderT.bind, Bind.bind] at h
  cases hbuild : buildCandidateExpr source.type context with
  | error error =>
      simp [Except.bind, hbuild] at h
  | ok type =>
      simp [Except.bind, ReaderT.pure, Pure.pure, Except.pure, hbuild] at h
      subst candidate
      exact CandidateExpr.context_eq_of_build hbuild

/-- The exact first-family candidate produced in the validator's reader
context contains at least the parameter prefix accepted by that validator.
The candidate's executable build equation supplies both its root-context
identity and annotation provenance. -/
theorem CandidateFamilyType.nparams_le_spineLength_of_firstFamilyValidation
    {context : Context} {indType : InductiveType}
    {candidate : CandidateFamilyType indType}
    (candidateRun : normalizeCandidateFamilyType indType context =
      .ok candidate)
    (terminal : candidate.type.trace.terminalResult = .sort resultLevel)
    (validation : checkInductiveTypes nparams
      (indType :: indTypes).toArray k context = .ok output) :
    nparams ≤ candidate.type.trace.spineLength := by
  have contextEq : candidate.type.context = context :=
    CandidateFamilyType.context_eq_of_normalize candidateRun
  have annotations : candidate.type.trace.validationAnnotations :=
    CandidateFamilyType.validationAnnotations_of_normalize candidateRun
  cases candidate with
  | mk candidateType =>
      cases candidateType with
      | mk candidateContext trace =>
          change candidateContext = context at contextEq
          subst candidateContext
          exact trace.nparams_le_spineLength_of_firstFamilyValidation
            indType indTypes nparams k output annotations terminal validation

def normalizeCandidateConstructorList :
    (ctors : List Constructor) →
      M (CandidateList CandidateConstructor ctors)
  | [] => return .nil
  | ctor :: ctors => do
    return .cons (← normalizeCandidateConstructor ctor)
      (← normalizeCandidateConstructorList ctors)

def normalizeCandidateFamilyTypeList :
    (types : List InductiveType) →
      M (CandidateList CandidateFamilyType types)
  | [] => return .nil
  | indType :: types => do
    return .cons (← normalizeCandidateFamilyType indType)
      (← normalizeCandidateFamilyTypeList types)

def normalizeCandidateFamilyList :
    {types : List InductiveType} →
      CandidateList CandidateFamilyType types →
      M (CandidateList CandidateFamily types)
  | [], .nil => return .nil
  | indType :: _, .cons familyType tail => do
    return .cons
      { familyType,
        constructors := ←
          normalizeCandidateConstructorList indType.ctors }
      (← normalizeCandidateFamilyList tail)

/-- Exact successful traversal of an arbitrary source-indexed family-type
list. The dependent indices prevent a proof for one metadata position from
being reused at another position or from silently truncating the source. -/
inductive CandidateFamilyTypeListProduced (context : Context) :
    {sources : List InductiveType} →
      CandidateList CandidateFamilyType sources → Prop where
  | nil : CandidateFamilyTypeListProduced context .nil
  | cons
      (head : normalizeCandidateFamilyType source context = .ok candidate)
      (tail : CandidateFamilyTypeListProduced context candidates) :
      CandidateFamilyTypeListProduced context (.cons candidate candidates)

/-- The first exact traversal equation retained by a nonempty family-type
producer trace. -/
theorem CandidateFamilyTypeListProduced.head
    {context : Context} {source : InductiveType}
    {sources : List InductiveType}
    {candidate : CandidateFamilyType source}
    {candidates : CandidateList CandidateFamilyType sources}
    (run : CandidateFamilyTypeListProduced context
      (.cons candidate candidates)) :
    normalizeCandidateFamilyType source context = .ok candidate := by
  cases run with
  | cons head _ => exact head

/-- The exact tail traversal retained by a nonempty family-type producer
trace. -/
theorem CandidateFamilyTypeListProduced.tail
    {context : Context} {source : InductiveType}
    {sources : List InductiveType}
    {candidate : CandidateFamilyType source}
    {candidates : CandidateList CandidateFamilyType sources}
    (run : CandidateFamilyTypeListProduced context
      (.cons candidate candidates)) :
    CandidateFamilyTypeListProduced context candidates := by
  cases run with
  | cons _ tail => exact tail

/-- A source-indexed family-type traversal determines the complete executable
list result for any length, without a fixture-specific list reduction. -/
theorem CandidateFamilyTypeListProduced.normalize
    {sources : List InductiveType}
    {candidates : CandidateList CandidateFamilyType sources}
    (run : CandidateFamilyTypeListProduced context candidates) :
    normalizeCandidateFamilyTypeList sources context = .ok candidates := by
  induction run with
  | nil => rfl
  | cons head tail ih =>
    unfold normalizeCandidateFamilyTypeList
    simp only [ReaderT.bind, Bind.bind]
    rw [head, ih]
    rfl

/-- A successful singleton family-type traversal retains the annotation
provenance of the exact candidate selected at its sole source position. -/
theorem CandidateFamilyTypeListProduced.singleton_validationAnnotations
    {context : Context} {source : Lean.InductiveType}
    {candidates : CandidateList CandidateFamilyType [source]}
    (run : CandidateFamilyTypeListProduced context candidates) :
    candidates.singleton.type.trace.validationAnnotations := by
  cases run with
  | cons head tail =>
      cases tail
      exact CandidateFamilyType.validationAnnotations_of_normalize head

/-- A successful singleton family-type traversal stores its exact traversal
context at the candidate root. -/
theorem CandidateFamilyTypeListProduced.singleton_context_eq
    {context : Context} {source : Lean.InductiveType}
    {candidates : CandidateList CandidateFamilyType [source]}
    (run : CandidateFamilyTypeListProduced context candidates) :
    candidates.singleton.type.context = context := by
  cases run with
  | cons head tail =>
      cases tail
      exact CandidateFamilyType.context_eq_of_normalize head

/-- Exact successful traversal of an arbitrary source-indexed constructor
list in one post-family context. Every candidate remains indexed by its source
constructor, so ordering, length, and header provenance are preserved by the
type rather than recovered from an erased list equality. -/
inductive CandidateConstructorListProduced (context : Context) :
    {sources : List Constructor} →
      CandidateList CandidateConstructor sources → Prop where
  | nil : CandidateConstructorListProduced context .nil
  | cons
      (head : normalizeCandidateConstructor source context = .ok candidate)
      (tail : CandidateConstructorListProduced context candidates) :
      CandidateConstructorListProduced context (.cons candidate candidates)

/-- The first exact traversal equation retained by a nonempty constructor
producer trace. -/
theorem CandidateConstructorListProduced.head
    {context : Context} {source : Constructor}
    {sources : List Constructor}
    {candidate : CandidateConstructor source}
    {candidates : CandidateList CandidateConstructor sources}
    (run : CandidateConstructorListProduced context
      (.cons candidate candidates)) :
    normalizeCandidateConstructor source context = .ok candidate := by
  cases run with
  | cons head _ => exact head

/-- The exact tail traversal retained by a nonempty constructor producer
trace. -/
theorem CandidateConstructorListProduced.tail
    {context : Context} {source : Constructor}
    {sources : List Constructor}
    {candidate : CandidateConstructor source}
    {candidates : CandidateList CandidateConstructor sources}
    (run : CandidateConstructorListProduced context
      (.cons candidate candidates)) :
    CandidateConstructorListProduced context candidates := by
  cases run with
  | cons _ tail => exact tail

/-- Annotation provenance at the exact head of a successful constructor-list
traversal. -/
theorem CandidateConstructorListProduced.head_validationAnnotations
    {context : Context} {source : Constructor}
    {sources : List Constructor}
    {candidate : CandidateConstructor source}
    {candidates : CandidateList CandidateConstructor sources}
    (run : CandidateConstructorListProduced context
      (.cons candidate candidates)) :
    candidate.type.trace.validationAnnotations :=
  CandidateConstructor.validationAnnotations_of_normalize run.head

/-- A source-indexed constructor traversal determines the complete executable
list result for any length, with no `zip`, partial lookup, or fixture-specific
cons-chain reduction. -/
theorem CandidateConstructorListProduced.normalize
    {sources : List Constructor}
    {candidates : CandidateList CandidateConstructor sources}
    (run : CandidateConstructorListProduced context candidates) :
    normalizeCandidateConstructorList sources context = .ok candidates := by
  induction run with
  | nil => rfl
  | cons head tail ih =>
    unfold normalizeCandidateConstructorList
    simp only [ReaderT.bind, Bind.bind]
    rw [head, ih]
    rfl

/-- A successful singleton constructor traversal stores its exact traversal
context at the candidate root. -/
theorem CandidateConstructorListProduced.singleton_context_eq
    {context : Context} {source : Constructor}
    {candidates : CandidateList CandidateConstructor [source]}
    (run : CandidateConstructorListProduced context candidates) :
    candidates.singleton.type.context = context := by
  cases run with
  | cons head tail =>
      cases tail
      exact CandidateConstructor.context_eq_of_normalize head

/-- Exact successful assembly of complete family candidates from an already
source-indexed family-type list. Each constructor traversal is tied to the
corresponding family source, and the tail remains tied to the remaining family
sources. This is the reusable ordered-list boundary needed before mutual-block
staging. -/
inductive CandidateFamilyListProduced (context : Context) :
    {sources : List InductiveType} →
      CandidateList CandidateFamilyType sources →
      CandidateList CandidateFamily sources → Prop where
  | nil : CandidateFamilyListProduced context .nil .nil
  | cons
      (constructors : CandidateConstructorListProduced
        context family.constructors)
      (tail : CandidateFamilyListProduced context familyTypes families) :
      CandidateFamilyListProduced context
        (.cons family.familyType familyTypes) (.cons family families)

/-- Constructor traversals retained for every exact family candidate, with
the family-type assembly index erased but family and constructor positions
preserved dependently. -/
inductive CandidateBlockConstructorListProduced (context : Context) :
    {sources : List InductiveType} →
      CandidateList CandidateFamily sources → Prop where
  | nil : CandidateBlockConstructorListProduced context .nil
  | cons
      (head : CandidateConstructorListProduced context family.constructors)
      (tail : CandidateBlockConstructorListProduced context families) :
      CandidateBlockConstructorListProduced context (.cons family families)

/-- Erase only the family-type assembly index from an exact family producer
trace, retaining every source-indexed constructor traversal. -/
theorem CandidateFamilyListProduced.constructorLists
    (run : CandidateFamilyListProduced context familyTypes families) :
    CandidateBlockConstructorListProduced context families := by
  induction run with
  | nil => exact .nil
  | cons constructors _ ih => exact .cons constructors ih

/-- The exact first-family constructor traversal in a nonempty block trace. -/
theorem CandidateBlockConstructorListProduced.head
    (run : CandidateBlockConstructorListProduced context
      (.cons family families)) :
    CandidateConstructorListProduced context family.constructors := by
  cases run with
  | cons head _ => exact head

/-- The exact remaining family traversals in a nonempty block trace. -/
theorem CandidateBlockConstructorListProduced.tail
    (run : CandidateBlockConstructorListProduced context
      (.cons family families)) :
    CandidateBlockConstructorListProduced context families := by
  cases run with
  | cons _ tail => exact tail

/-- Source-indexed family assembly determines the exact executable family-list
result for arbitrary list lengths. -/
theorem CandidateFamilyListProduced.normalize
    {sources : List InductiveType}
    {familyTypes : CandidateList CandidateFamilyType sources}
    {families : CandidateList CandidateFamily sources}
    (run : CandidateFamilyListProduced context familyTypes families) :
    normalizeCandidateFamilyList familyTypes context = .ok families := by
  induction run with
  | nil => rfl
  | cons constructors tail ih =>
    unfold normalizeCandidateFamilyList
    simp only [ReaderT.bind, Bind.bind]
    rw [constructors.normalize, ih]
    rfl

/-- Erasing an assembled family list back to its family-type payload recovers
the exact source-indexed input list used by the traversal. -/
theorem CandidateFamilyListProduced.familyTypes_eq
    {sources : List InductiveType}
    {familyTypes : CandidateList CandidateFamilyType sources}
    {families : CandidateList CandidateFamily sources}
    (run : CandidateFamilyListProduced context familyTypes families) :
    families.familyTypes = familyTypes := by
  induction run with
  | nil => rfl
  | cons _ _ ih => simp only [CandidateList.familyTypes, ih]

/-- The head family assembled for a nonempty block retains the exact
pre-family type candidate selected by the source-indexed traversal. -/
theorem CandidateFamilyListProduced.head_familyType
    {source : InductiveType} {sources : List InductiveType}
    {familyTypes : CandidateList CandidateFamilyType (source :: sources)}
    {families : CandidateList CandidateFamily (source :: sources)}
    (run : CandidateFamilyListProduced context familyTypes families) :
    families.head.familyType = familyTypes.head := by
  cases run
  rfl

/-- Reindex an arbitrary-length family-production witness by the family-type
payload stored in its own assembled result. -/
theorem CandidateFamilyListProduced.reindex
    {sources : List InductiveType}
    {familyTypes : CandidateList CandidateFamilyType sources}
    {families : CandidateList CandidateFamily sources}
    (run : CandidateFamilyListProduced context familyTypes families) :
    CandidateFamilyListProduced context families.familyTypes families := by
  rw [run.familyTypes_eq]
  exact run

/-- Singleton family assembly reuses, without replacement, the family-type
candidate produced in the pre-family environment. -/
theorem CandidateFamilyListProduced.singleton_familyType
    {context : Context} {source : Lean.InductiveType}
    {familyTypes : CandidateList CandidateFamilyType [source]}
    {families : CandidateList CandidateFamily [source]}
    (run : CandidateFamilyListProduced context familyTypes families) :
    families.singleton.familyType = familyTypes.singleton := by
  cases run with
  | cons constructors tail =>
      cases tail
      rfl

/-- Singleton family assembly exposes the exact source-indexed constructor
traversal retained for its sole family. -/
theorem CandidateFamilyListProduced.singleton_constructors
    {context : Context} {source : Lean.InductiveType}
    {familyTypes : CandidateList CandidateFamilyType [source]}
    {families : CandidateList CandidateFamily [source]}
    (run : CandidateFamilyListProduced context familyTypes families) :
    CandidateConstructorListProduced context
      families.singleton.constructors := by
  cases run with
  | cons constructors tail =>
      cases tail
      exact constructors

/-- A successful singleton family assembly can be reindexed directly by the
family-type payload retained in its assembled result.  This dependent eta law
avoids rewriting the input list underneath the execution witness. -/
theorem CandidateFamilyListProduced.singleton_reindex
    {context : Context} {source : Lean.InductiveType}
    {familyTypes : CandidateList CandidateFamilyType [source]}
    {families : CandidateList CandidateFamily [source]}
    (run : CandidateFamilyListProduced context familyTypes families) :
    CandidateFamilyListProduced context
      (.cons families.singleton.familyType .nil) families := by
  cases run with
  | cons constructors tail =>
      cases tail
      exact .cons constructors .nil

/-- Shape-preserving output of the executable normalization-candidate pass.
The dependent family/constructor lists prevent positional provenance from
being silently reused for a different inductive request. Names, ordering, and
record headers come from the indexed source; only expression payloads are
reconstructed from candidate traces. -/
structure NormalizationCandidate (source : List InductiveType) where
  families : CandidateList CandidateFamily source

def NormalizationCandidate.view
    (candidate : NormalizationCandidate source) : List InductiveType :=
  candidate.families.toList fun _ family => family.view

/-- One exact family-type traversal result together with the source-indexed
operational witness that produced it.  The witness is provenance for later
Verify staging; it carries no Theory semantics. -/
structure CandidateFamilyTypeListExecution (context : Context)
    (sources : List InductiveType) where
  candidates : CandidateList CandidateFamilyType sources
  produced : CandidateFamilyTypeListProduced context candidates

/-- Run the existing family-type normalizer while retaining its exact
source-ordered traversal equations.  Errors and candidate data are unchanged. -/
def executeCandidateFamilyTypeList (context : Context) :
    (sources : List InductiveType) →
      Except Exception (CandidateFamilyTypeListExecution context sources)
  | [] => .ok ⟨.nil, .nil⟩
  | source :: sources =>
      match hhead : normalizeCandidateFamilyType source context with
      | .error error => .error error
      | .ok head =>
          match executeCandidateFamilyTypeList context sources with
          | .error error => .error error
          | .ok tail => .ok {
              candidates := .cons head tail.candidates
              produced := .cons (by simpa using hhead) tail.produced }

/-- One exact constructor traversal result together with its source-indexed
operational witness. -/
structure CandidateConstructorListExecution (context : Context)
    (sources : List Constructor) where
  candidates : CandidateList CandidateConstructor sources
  produced : CandidateConstructorListProduced context candidates

/-- Run the existing constructor normalizer while retaining its exact
source-ordered traversal equations. -/
def executeCandidateConstructorList (context : Context) :
    (sources : List Constructor) →
      Except Exception (CandidateConstructorListExecution context sources)
  | [] => .ok ⟨.nil, .nil⟩
  | source :: sources =>
      match hhead : normalizeCandidateConstructor source context with
      | .error error => .error error
      | .ok head =>
          match executeCandidateConstructorList context sources with
          | .error error => .error error
          | .ok tail => .ok {
              candidates := .cons head tail.candidates
              produced := .cons (by simpa using hhead) tail.produced }

/-- One exact family/constructor assembly result together with both dependent
source lists retained by the ordinary traversal. -/
structure CandidateFamilyListExecution (context : Context)
    {sources : List InductiveType}
    (familyTypes : CandidateList CandidateFamilyType sources) where
  candidates : CandidateList CandidateFamily sources
  produced : CandidateFamilyListProduced context familyTypes candidates

/-- Run the existing family assembler while retaining each constructor-list
execution.  This is an operational refinement of
`normalizeCandidateFamilyList`, not an additional acceptance premise. -/
def executeCandidateFamilyList (context : Context) :
    {sources : List InductiveType} →
    (familyTypes : CandidateList CandidateFamilyType sources) →
      Except Exception (CandidateFamilyListExecution context familyTypes)
  | [], .nil => .ok ⟨.nil, .nil⟩
  | source :: _, .cons familyType familyTypes =>
      match executeCandidateConstructorList context source.ctors with
      | .error error => .error error
      | .ok constructors =>
          match executeCandidateFamilyList context familyTypes with
          | .error error => .error error
          | .ok tail =>
            let family : CandidateFamily source := {
              familyType
              constructors := constructors.candidates }
            .ok {
              candidates := .cons family tail.candidates
              produced := by
                change CandidateFamilyListProduced context
                  (.cons family.familyType familyTypes)
                  (.cons family tail.candidates)
                exact .cons constructors.produced tail.produced }

/-! ## Exact normalization-observer boundary -/

/-- The recursive family-type observer succeeds in its exact pre-family
reader context. -/
def CandidateFamilyType.Observable
    (context : Context) (source : InductiveType) : Prop :=
  ∃ (candidate : CandidateFamilyType source) (resultLevel : Level),
    normalizeCandidateFamilyType source context = .ok candidate ∧
      candidate.type.trace.terminalResult = .sort resultLevel

/-- The recursive constructor-type observer succeeds in its exact post-family
reader context. -/
def CandidateConstructor.Observable
    (context : Context) (source : Constructor) : Prop :=
  ∃ candidate : CandidateConstructor source,
    normalizeCandidateConstructor source context = .ok candidate

/-- Pointwise candidate-expression observations for every family type, in
source order. -/
inductive CandidateFamilyTypeListObservable (context : Context) :
    List InductiveType → Prop where
  | nil : CandidateFamilyTypeListObservable context []
  | cons
      (head : CandidateFamilyType.Observable context source)
      (tail : CandidateFamilyTypeListObservable context sources) :
      CandidateFamilyTypeListObservable context (source :: sources)

/-- Pointwise candidate-expression observations for one source-ordered
constructor list. -/
inductive CandidateConstructorListObservable (context : Context) :
    List Constructor → Prop where
  | nil : CandidateConstructorListObservable context []
  | cons
      (head : CandidateConstructor.Observable context source)
      (tail : CandidateConstructorListObservable context sources) :
      CandidateConstructorListObservable context (source :: sources)

/-- Pointwise constructor observations for every family in a source-ordered
inductive block.  All constructor types are inspected after the same raw
family environment has been installed. -/
inductive CandidateFamilyConstructorListsObservable (context : Context) :
    List InductiveType → Prop where
  | nil : CandidateFamilyConstructorListsObservable context []
  | cons
      (head : CandidateConstructorListObservable context source.ctors)
      (tail : CandidateFamilyConstructorListsObservable context sources) :
      CandidateFamilyConstructorListsObservable context (source :: sources)

/-- Ordered family observation constructs the exact traversal together with
the terminal-sort evidence now required by the retained normalization
prefix. -/
theorem executeCandidateFamilyTypeList_ok_with_terminals_of_observable
    (observable : CandidateFamilyTypeListObservable context sources) :
    ∃ execution,
      executeCandidateFamilyTypeList context sources = .ok execution ∧
        CandidateFamilyTypeTerminalSortList execution.candidates := by
  induction sources with
  | nil => exact ⟨_, rfl, .nil⟩
  | cons source sources ih =>
      cases observable with
      | cons head tail =>
          change (∃ (candidate : CandidateFamilyType source)
              (resultLevel : Level),
            normalizeCandidateFamilyType source context = .ok candidate ∧
              candidate.type.trace.terminalResult =
                .sort resultLevel) at head
          obtain ⟨headCandidate, resultLevel, headRun, terminal⟩ := head
          obtain ⟨tailExecution, tailRun, terminals⟩ := ih tail
          unfold executeCandidateFamilyTypeList
          split
          next error actual =>
            rw [headRun] at actual
            contradiction
          next actualHead actual =>
            rw [headRun] at actual
            cases actual
            split
            next error actualTail =>
              rw [tailRun] at actualTail
              contradiction
            next actualTail actualTailRun =>
              rw [tailRun] at actualTailRun
              cases actualTailRun
              exact ⟨_, rfl, .cons terminal terminals⟩

/-- Ordered family-type observation succeeds when each underlying recursive
expression observer succeeds. -/
theorem executeCandidateFamilyTypeList_ok_of_observable
    (observable : CandidateFamilyTypeListObservable context sources) :
    ∃ execution,
      executeCandidateFamilyTypeList context sources = .ok execution := by
  obtain ⟨execution, run, _⟩ :=
    executeCandidateFamilyTypeList_ok_with_terminals_of_observable observable
  exact ⟨execution, run⟩

/-- Ordered constructor observation succeeds when each underlying recursive
expression observer succeeds. -/
theorem executeCandidateConstructorList_ok_of_observable
    (observable : CandidateConstructorListObservable context sources) :
    ∃ execution,
      executeCandidateConstructorList context sources = .ok execution := by
  induction sources with
  | nil => exact ⟨_, rfl⟩
  | cons source sources ih =>
      cases observable with
      | cons head tail =>
          change (∃ candidate : CandidateConstructor source,
            normalizeCandidateConstructor source context = .ok candidate) at head
          obtain ⟨headCandidate, headRun⟩ := head
          obtain ⟨tailExecution, tailRun⟩ := ih tail
          unfold executeCandidateConstructorList
          split
          next error actual =>
            rw [headRun] at actual
            contradiction
          next actualHead actual =>
            split
            next error actualTail =>
              rw [tailRun] at actualTail
              contradiction
            next actualTail actualTailRun => exact ⟨_, rfl⟩

/-- Ordered family assembly succeeds when every source family owns the exact
constructor observations used by its candidate traversal. -/
theorem executeCandidateFamilyList_ok_of_observable
    (familyTypes : CandidateList CandidateFamilyType sources)
    (observable :
      CandidateFamilyConstructorListsObservable context sources) :
    ∃ execution,
      executeCandidateFamilyList context familyTypes = .ok execution := by
  induction observable with
  | nil =>
      cases familyTypes
      exact ⟨_, rfl⟩
  | @cons sources source head tail ih =>
      cases familyTypes with
      | cons familyType familyTypes =>
          obtain ⟨constructors, constructorsRun⟩ :=
            executeCandidateConstructorList_ok_of_observable head
          obtain ⟨tailExecution, tailRun⟩ := ih familyTypes
          simp only [executeCandidateFamilyList, constructorsRun, tailRun]
          exact ⟨_, rfl⟩

/-- Detailed operational result of `buildNormalizationCandidate`.

The ordinary result erases to `candidate`.  The remaining fields retain the
validator-selected statistics, intermediate environment, and exact list
traversals already executed by the same call.  Verify uses these equations as
staging provenance; all semantic authority still comes from the D1--D4
interpreters. -/
structure NormalizationCandidateExecution
    (nparams : Nat) (types : List InductiveType)
    (numNested : Nat) (isUnsafe : Bool) (candidateContext : Context) where
  validationContext : Context
  stats : InductiveStats
  familySourcesClosed : FamilySourceClosedList types
  familyTypes : CandidateFamilyTypeListExecution
    { candidateContext with lctx := {} } types
  familyTerminals : CandidateFamilyTypeTerminalSortList
    familyTypes.candidates
  familyEnv : Environment
  declareRun : declareInductiveTypes stats nparams types.toArray
    numNested isUnsafe validationContext = .ok familyEnv
  declareTrace : DeclareInductiveInfoListRun
    validationContext.allowPrimitive validationContext.env
    (declaredInductiveInfos stats nparams types.toArray numNested isUnsafe
      validationContext).toList familyEnv
  constructorRun : checkConstructors types.toArray stats isUnsafe
    { validationContext with env := familyEnv } = .ok ()
  families : CandidateFamilyListExecution
    { candidateContext with env := familyEnv, lctx := {} }
    familyTypes.candidates
  generationSpines : CandidateFamilyGenerationSpineList families.candidates
  familyParameterSpines :
    CandidateFamilyParameterSpineList nparams families.candidates
  familyIndexCounts :
    CandidateFamilyIndexCountList stats nparams 0 families.candidates

def NormalizationCandidateExecution.candidate
    (execution : NormalizationCandidateExecution nparams types numNested
      isUnsafe candidateContext) : NormalizationCandidate types :=
  ⟨execution.families.candidates⟩

/-- Exact source-ordered family metadata installed by a retained execution. -/
def NormalizationCandidateExecution.declaredInfos
    (execution : NormalizationCandidateExecution nparams types numNested
      isUnsafe candidateContext) : List InductiveVal :=
  (declaredInductiveInfos execution.stats nparams types.toArray numNested
    isUnsafe execution.validationContext).toList

/-- The retained declaration trace determines the complete post-family
constant map, including the empty-block case. -/
theorem NormalizationCandidateExecution.familyEnv_constants
    (execution : NormalizationCandidateExecution nparams types numNested
      isUnsafe candidateContext) :
    execution.familyEnv.constants = execution.declaredInfos.foldl
      (fun constants info =>
        constants.insert info.name (.inductInfo info))
      execution.validationContext.env.constants := by
  exact execution.declareTrace.constants

/-- Family metadata declaration preserves the quotient-initialization flag. -/
theorem NormalizationCandidateExecution.familyEnv_quotInit
    (execution : NormalizationCandidateExecution nparams types numNested
      isUnsafe candidateContext) :
    execution.familyEnv.quotInit =
      execution.validationContext.env.quotInit :=
  execution.declareTrace.quotInit

/-- The post-family half of the detailed ordinary execution. -/
def buildNormalizationCandidateExecutionAfterValidation
    (nparams : Nat) (types : List InductiveType)
    (numNested : Nat) (isUnsafe : Bool) (candidateContext : Context)
    (stats : InductiveStats) :
    M (NormalizationCandidateExecution nparams types numNested isUnsafe
      candidateContext) :=
  fun validationContext =>
    match hdeclare : declareInductiveTypes stats nparams types.toArray
        numNested isUnsafe validationContext with
    | .error error => .error error
    | .ok familyEnv =>
      match hconstructors : checkConstructors types.toArray stats isUnsafe
          { validationContext with env := familyEnv } with
      | .error error => .error error
      | .ok () =>
        match executeCandidateFamilyTypeList
            { candidateContext with lctx := {} } types with
        | .error error => .error error
        | .ok familyTypes =>
          if hsources : FamilySourceClosedList.check types then
            if hterminals : CandidateFamilyTypeTerminalSortList.check
                familyTypes.candidates then
              match executeCandidateFamilyList
                  { candidateContext with env := familyEnv, lctx := {} }
                  familyTypes.candidates with
              | .error error => .error error
              | .ok families =>
                if hspines : CandidateFamilyGenerationSpineList.check
                    families.candidates then
                  if hparameters : CandidateFamilyParameterSpineList.check
                      nparams families.candidates then
                    if hcounts : CandidateFamilyIndexCountList.check stats
                        nparams 0 families.candidates then
                      .ok {
                        validationContext
                        stats
                        familySourcesClosed :=
                          FamilySourceClosedList.of_check _ hsources
                        familyTypes
                        familyTerminals :=
                          CandidateFamilyTypeTerminalSortList.of_check _ hterminals
                        familyEnv
                        declareRun := by simpa using hdeclare
                        declareTrace := DeclareInductiveInfoListRun.of_run (by
                          simpa only [declareInductiveTypes] using hdeclare)
                        constructorRun := by simpa using hconstructors
                        families
                        generationSpines :=
                          CandidateFamilyGenerationSpineList.of_check _ hspines
                        familyParameterSpines :=
                          CandidateFamilyParameterSpineList.of_check nparams _
                            hparameters
                        familyIndexCounts :=
                          CandidateFamilyIndexCountList.of_check stats nparams
                            0 _ hcounts }
                    else
                      .error (.other
                        "normalization candidate index counts disagree with family validation")
                  else
                    .error (.other
                      "normalization candidate family parameter spine is incomplete")
                else
                  .error (.other
                    "normalization candidate generation spine is not complete")
            else
              .error (.other
                "normalization candidate family terminal is not a sort")
          else
            .error (.other
              "normalization candidate family source is not closed")

/-- A retained successful post-validation execution exposes exactly the
statistics and reader context supplied by the family validator. -/
theorem NormalizationCandidateExecution.fields_of_afterValidation
    (execution : NormalizationCandidateExecution nparams types numNested
      isUnsafe candidateContext)
    (stats : InductiveStats) (validationContext : Context)
    (h : buildNormalizationCandidateExecutionAfterValidation nparams types
        numNested isUnsafe candidateContext stats validationContext =
      .ok execution) :
    execution.stats = stats ∧
      execution.validationContext = validationContext := by
  unfold buildNormalizationCandidateExecutionAfterValidation at h
  repeat' split at h
  all_goals try simp_all
  subst execution
  exact ⟨rfl, rfl⟩

/-- Execute the ordinary singleton/mutual candidate pass while retaining the
exact operational provenance erased by the public candidate result. -/
def buildNormalizationCandidateExecution
    (nparams : Nat) (types : List InductiveType)
    (numNested : Nat) (isUnsafe : Bool) (candidateContext : Context) :
    Except Exception (NormalizationCandidateExecution nparams types
      numNested isUnsafe candidateContext) :=
  checkInductiveTypes nparams types.toArray (fun stats =>
    buildNormalizationCandidateExecutionAfterValidation nparams types
      numNested isUnsafe candidateContext stats) candidateContext

/-- Run the generic one-pass candidate producer at the same two environments
as kernel inductive checking: family types in the input environment, then
constructor types after insertion of every raw family constant.

This repeats the ordinary family/constructor validity checks so a candidate
cannot be obtained from metadata already rejected at those stages. The Theory
analyzer and Verify semantic certificate remain separate downstream gates. -/
def buildNormalizationCandidate
    (nparams : Nat) (types : List InductiveType)
    (numNested : Nat) (isUnsafe : Bool) :
    M (NormalizationCandidate types) :=
  -- Family validation retains its parameter/index telescope while invoking
  -- the continuation.  That context is required by `checkConstructors`, whose
  -- parameter checks refer to the free variables recorded in `stats`, but it
  -- is not part of the closed metadata being normalized.  Snapshot the entry
  -- context so both candidate traversals use one stable fresh-name provenance
  -- and an empty local context; only the staged kernel environment changes.
  fun candidateContext =>
  let indTypes := types.toArray
  checkInductiveTypes nparams indTypes (fun stats => do
    let familyEnv ←
      declareInductiveTypes stats nparams indTypes numNested isUnsafe
    withEnv familyEnv do
      checkConstructors indTypes stats isUnsafe
      let familyTypes ←
        withReader (fun _ : Context => { candidateContext with lctx := {} }) do
          normalizeCandidateFamilyTypeList types
      let families ←
        withReader (fun _ : Context =>
          { candidateContext with env := familyEnv, lctx := {} }) do
          normalizeCandidateFamilyList familyTypes
      return ⟨families⟩) candidateContext

/-- Erase a retained successful execution back to the unchanged public
candidate producer.  The family-validation equation supplies the continuation
boundary selected by `checkInductiveTypes`; every later rewrite comes from an
operation already stored in `execution`. -/
theorem NormalizationCandidateExecution.produces
    (execution : NormalizationCandidateExecution nparams types numNested
      isUnsafe candidateContext)
    (validationRun : ∀ {α} (k : InductiveStats → M α),
      checkInductiveTypes nparams types.toArray k candidateContext =
        k execution.stats execution.validationContext) :
    buildNormalizationCandidate nparams types numNested isUnsafe
        candidateContext = .ok execution.candidate := by
  unfold buildNormalizationCandidate
  rw [validationRun]
  simp only [ReaderT.bind, Bind.bind]
  rw [execution.declareRun]
  unfold withEnv
  change (ReaderT.bind
      (checkConstructors types.toArray execution.stats isUnsafe)
      (fun _ => ReaderT.bind
        (withReader (fun _ : Context =>
          { candidateContext with lctx := {} })
          (normalizeCandidateFamilyTypeList types))
        (fun familyTypes => ReaderT.bind
        (withReader (fun _ : Context =>
          { candidateContext with
            env := execution.familyEnv, lctx := {} })
          (normalizeCandidateFamilyList familyTypes))
        (fun families => pure
          (⟨families⟩ : NormalizationCandidate types)))))
      ({ execution.validationContext with
        env := execution.familyEnv } : Context) = _
  simp only [ReaderT.bind, Bind.bind]
  rw [execution.constructorRun]
  simp only [Except.bind]
  rw [show
    (withReader (fun _ : Context =>
        { candidateContext with lctx := {} })
      (normalizeCandidateFamilyTypeList types))
      { execution.validationContext with env := execution.familyEnv } =
        .ok execution.familyTypes.candidates by
      change normalizeCandidateFamilyTypeList types
        { candidateContext with lctx := {} } = _
      exact execution.familyTypes.produced.normalize]
  simp only
  rw [show
    (withReader (fun _ : Context =>
        { candidateContext with
          env := execution.familyEnv, lctx := {} })
      (normalizeCandidateFamilyList execution.familyTypes.candidates))
      { execution.validationContext with env := execution.familyEnv } =
        .ok execution.families.candidates by
      change normalizeCandidateFamilyList execution.familyTypes.candidates
        { candidateContext with env := execution.familyEnv, lctx := {} } = _
      exact execution.families.produced.normalize]
  rfl

/--
info: 'Lean4Lean.AddInductive.buildCandidateExpr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms buildCandidateExpr

/--
info: 'Lean4Lean.AddInductive.observeCandidateIsDefEq_of_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms observeCandidateIsDefEq_of_run

/--
info: 'Lean4Lean.AddInductive.buildCandidateExpr_loop_of_whnf_nonForall' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms buildCandidateExpr_loop_of_whnf_nonForall

/--
info: 'Lean4Lean.AddInductive.buildCandidateExpr_loop_of_whnf_forall' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms buildCandidateExpr_loop_of_whnf_forall

/--
info: 'Lean4Lean.AddInductive.CandidateTypeAnnotationTrace.build' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms CandidateTypeAnnotationTrace.build

/--
info: 'Lean4Lean.AddInductive.CandidateTypeAnnotationTrace.build_consumed' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms CandidateTypeAnnotationTrace.build_consumed

/--
info: 'Lean4Lean.AddInductive.buildCandidateTypeAnnotations' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms buildCandidateTypeAnnotations

/--
info: 'Lean4Lean.AddInductive.CandidateTypeAnnotations.matches_of_build' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CandidateTypeAnnotations.matches_of_build

/--
info: 'Lean4Lean.AddInductive.buildCandidateCheckType' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms buildCandidateCheckType

/--
info: 'Lean4Lean.AddInductive.buildNormalizationCandidate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms buildNormalizationCandidate

/--
info: 'Lean4Lean.AddInductive.CandidateFamilyTypeListProduced.normalize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CandidateFamilyTypeListProduced.normalize

/--
info: 'Lean4Lean.AddInductive.CandidateConstructorListProduced.normalize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CandidateConstructorListProduced.normalize

/--
info: 'Lean4Lean.AddInductive.CandidateFamilyListProduced.normalize' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CandidateFamilyListProduced.normalize

/--
info: 'Lean4Lean.AddInductive.executeCandidateFamilyTypeList_ok_of_observable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms executeCandidateFamilyTypeList_ok_of_observable

/--
info: 'Lean4Lean.AddInductive.executeCandidateConstructorList_ok_of_observable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms executeCandidateConstructorList_ok_of_observable

/--
info: 'Lean4Lean.AddInductive.executeCandidateFamilyList_ok_of_observable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms executeCandidateFamilyList_ok_of_observable

/--
info: 'Lean4Lean.AddInductive.CandidateList.singleton' does not depend on any axioms
-/
#guard_msgs in
#print axioms CandidateList.singleton

/--
info: 'Lean4Lean.AddInductive.CandidateExprTrace.storedSpine' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CandidateExprTrace.storedSpine

/--
info: 'Lean4Lean.AddInductive.CandidateExprTrace.spineLength' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CandidateExprTrace.spineLength

/--
info: 'Lean4Lean.AddInductive.CandidateExprTrace.rootWhnf_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CandidateExprTrace.rootWhnf_valid

/--
info: 'Lean4Lean.AddInductive.CandidateExprTrace.terminalContext_lparams' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CandidateExprTrace.terminalContext_lparams

/--
info: 'Lean4Lean.AddInductive.CandidateExprTrace.parameterList_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CandidateExprTrace.parameterList_length

/--
info: 'Lean4Lean.AddInductive.CandidateExprTrace.parameterList_eq_of_ngen_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CandidateExprTrace.parameterList_eq_of_ngen_eq

/--
info: 'Lean4Lean.AddInductive.CandidateExprTrace.checkInductiveTypes_loop_of_candidate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CandidateExprTrace.checkInductiveTypes_loop_of_candidate

/--
info: 'Lean4Lean.AddInductive.CandidateExprTrace.checkInductiveTypes_loop_not_ok_of_candidate_tooFew' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CandidateExprTrace.checkInductiveTypes_loop_not_ok_of_candidate_tooFew

/--
info: 'Lean4Lean.AddInductive.CandidateExprTrace.checkInductiveTypes_loop_not_ok_of_candidate_fuel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CandidateExprTrace.checkInductiveTypes_loop_not_ok_of_candidate_fuel

/--
info: 'Lean4Lean.AddInductive.CandidateExprTrace.nparams_le_spineLength_of_firstFamilyValidation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CandidateExprTrace.nparams_le_spineLength_of_firstFamilyValidation

/--
info: 'Lean4Lean.AddInductive.CandidateFamilyType.nparams_le_spineLength_of_firstFamilyValidation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CandidateFamilyType.nparams_le_spineLength_of_firstFamilyValidation

/--
info: 'Lean4Lean.AddInductive.CandidateFamilyListProduced.head_familyType' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CandidateFamilyListProduced.head_familyType

/--
info: 'Lean4Lean.AddInductive.CandidateExprTrace.checkInductiveTypes_singleton_of_candidate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CandidateExprTrace.checkInductiveTypes_singleton_of_candidate

/--
info: 'Lean4Lean.AddInductive.CandidateExprTrace.FamilyValidationRun' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CandidateExprTrace.FamilyValidationRun

/--
info: 'Lean4Lean.AddInductive.CandidateExprTrace.FamilyValidationRun.parameters' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CandidateExprTrace.FamilyValidationRun.parameters

/--
info: 'Lean4Lean.AddInductive.CandidateExprTrace.FamilyValidationRun.numIndices' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CandidateExprTrace.FamilyValidationRun.numIndices

/--
info: 'Lean4Lean.AddInductive.CandidateExpr.step_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CandidateExpr.step_valid

/--
info: 'Lean4Lean.AddInductive.CandidateExpr.checkStep_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CandidateExpr.checkStep_valid

/--
info: 'Lean4Lean.AddInductive.CandidateExpr.isDefEqStep_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CandidateExpr.isDefEqStep_valid

/--
info: 'Lean4Lean.AddInductive.CandidateWhnfStep.innerRun' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CandidateWhnfStep.innerRun

/--
info: 'Lean4Lean.AddInductive.CandidateCheckTypeStep.innerRun' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CandidateCheckTypeStep.innerRun

/--
info: 'Lean4Lean.AddInductive.CandidateIsDefEqStep.innerRun' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CandidateIsDefEqStep.innerRun

/-- Number of leading binders stored in a constructor type. -/
def constructorArity : Expr → Nat → Nat
  | .forallE _ _ body _, arity => constructorArity body (arity + 1)
  | _, arity => arity

/-- Adding to the accumulator commutes with counting the literal leading Pi
spine. -/
theorem constructorArity_add (source : Expr) (left right : Nat) :
    constructorArity source (left + right) =
      constructorArity source left + right := by
  induction source generalizing left right <;>
    simp only [constructorArity]
  rw [show left + right + 1 = left + 1 + right by omega]
  apply_assumption

/-- The accumulator contributes additively to the literal leading Pi count. -/
theorem constructorArity_eq_zero_add (source : Expr) (arity : Nat) :
    constructorArity source arity = constructorArity source 0 + arity := by
  simpa only [Nat.zero_add] using constructorArity_add source 0 arity

/-- Structural expression equality preserves the literal leading Pi count
used by ordinary constructor metadata. -/
theorem constructorArity_eq_of_structuralEq
    {source target : Expr}
    (equal : Expr.structuralEq source target = true) (arity : Nat) :
    constructorArity source arity = constructorArity target arity := by
  induction source generalizing target arity <;> cases target <;>
    simp_all [Expr.structuralEq, constructorArity]
  apply_assumption
  exact equal.2

/-- Exact constructor record assembled by the ordinary declaration phase. -/
def declaredConstructorInfo (stats : InductiveStats)
    (induct : Name) (ctor : Constructor) (cidx : Nat)
    (isUnsafe : Bool) (context : Context) : ConstructorVal :=
  let arity := constructorArity ctor.type 0
  { type := ctor.type, cidx, isUnsafe
    levelParams := context.lparams
    name := ctor.name
    induct := induct
    numParams := stats.params.size
    numFields := assert! arity ≥ stats.params.size
      arity - stats.params.size }

/-- Constructor metadata for one family, retaining its zero-based constructor
ordinal in source order. -/
def declaredConstructorInfosFor (stats : InductiveStats)
    (induct : Name) (isUnsafe : Bool) (context : Context) :
    Nat → List Constructor → List ConstructorVal
  | _, [] => []
  | cidx, ctor :: ctors =>
      declaredConstructorInfo stats induct ctor cidx isUnsafe context ::
        declaredConstructorInfosFor stats induct isUnsafe context
          (cidx + 1) ctors

/-- Family-major constructor metadata in the exact order installed by the
kernel: source families first, then each family's constructor order. -/
def declaredConstructorInfos (stats : InductiveStats)
    (indTypes : Array InductiveType) (isUnsafe : Bool)
    (context : Context) : List ConstructorVal :=
  indTypes.toList.flatMap fun indType =>
    declaredConstructorInfosFor stats indType.name isUnsafe context 0
      indType.ctors

theorem declaredConstructorInfos_toArray
    (stats : InductiveStats) (indTypes : List InductiveType)
    (isUnsafe : Bool) (context : Context) :
    declaredConstructorInfos stats indTypes.toArray isUnsafe context =
      indTypes.flatMap fun indType =>
        declaredConstructorInfosFor stats indType.name isUnsafe context 0
          indType.ctors := by
  simp [declaredConstructorInfos]

/-- Constructor metadata for one family preserves every source constructor
name and its declaration order. -/
theorem declaredConstructorInfosFor_names
    (stats : InductiveStats) (induct : Name) (isUnsafe : Bool)
    (context : Context) (cidx : Nat) (ctors : List Constructor) :
    (declaredConstructorInfosFor stats induct isUnsafe context cidx ctors).map
      (·.name) = ctors.map (·.name) := by
  induction ctors generalizing cidx with
  | nil => rfl
  | cons ctor ctors ih =>
      simp only [declaredConstructorInfosFor, List.map_cons,
        declaredConstructorInfo, ih]

/-- The family-major constructor metadata inventory preserves the flattened
source constructor-name order. -/
theorem declaredConstructorInfos_names
    (stats : InductiveStats) (indTypes : Array InductiveType)
    (isUnsafe : Bool) (context : Context) :
    (declaredConstructorInfos stats indTypes isUnsafe context).map (·.name) =
      indTypes.toList.flatMap (fun indType =>
        indType.ctors.map (·.name)) := by
  simp only [declaredConstructorInfos, List.map_flatMap,
    declaredConstructorInfosFor_names]

/-- Every source constructor occurs by name in the exact metadata list
synthesized for its family. -/
theorem declaredConstructorInfosFor_name
    (stats : InductiveStats) (induct : Name) (isUnsafe : Bool)
    (context : Context) (cidx : Nat) (ctors : List Constructor)
    {ctor : Constructor} (member : ctor ∈ ctors) :
    ∃ info ∈ declaredConstructorInfosFor stats induct isUnsafe context cidx
        ctors,
      info.name = ctor.name := by
  induction ctors generalizing cidx with
  | nil => contradiction
  | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨declaredConstructorInfo stats induct ctor cidx isUnsafe
          context, .head _, rfl⟩
      · obtain ⟨info, infoMember, nameEq⟩ := ih (cidx + 1) member
        exact ⟨info, .tail _ infoMember, nameEq⟩

/-- Every constructor metadata record synthesized by one family fold carries
the validator's common parameter count. -/
theorem declaredConstructorInfosFor_numParams
    (stats : InductiveStats) (induct : Name) (isUnsafe : Bool)
    (context : Context) (cidx : Nat) (ctors : List Constructor)
    {info : ConstructorVal}
    (member : info ∈ declaredConstructorInfosFor stats induct isUnsafe
      context cidx ctors) :
    info.numParams = stats.params.size := by
  induction ctors generalizing cidx with
  | nil => contradiction
  | cons ctor ctors ih =>
      simp only [declaredConstructorInfosFor, List.mem_cons] at member
      rcases member with rfl | member
      · rfl
      · exact ih (cidx + 1) member

/-- The flattened constructor inventory preserves the same common parameter
count for every synthesized metadata record. -/
theorem declaredConstructorInfos_numParams
    (stats : InductiveStats) (indTypes : Array InductiveType)
    (isUnsafe : Bool) (context : Context) {info : ConstructorVal}
    (member : info ∈ declaredConstructorInfos stats indTypes isUnsafe
      context) :
    info.numParams = stats.params.size := by
  simp only [declaredConstructorInfos, List.mem_flatMap] at member
  obtain ⟨indType, _member, member⟩ := member
  exact declaredConstructorInfosFor_numParams stats indType.name isUnsafe
    context 0 indType.ctors member

/-- Every constructor record synthesized by one family fold retains that
family as its owner. -/
theorem declaredConstructorInfosFor_induct
    (stats : InductiveStats) (induct : Name) (isUnsafe : Bool)
    (context : Context) (cidx : Nat) (ctors : List Constructor)
    {info : ConstructorVal}
    (member : info ∈ declaredConstructorInfosFor stats induct isUnsafe
      context cidx ctors) :
    info.induct = induct := by
  induction ctors generalizing cidx with
  | nil => contradiction
  | cons ctor ctors ih =>
      simp only [declaredConstructorInfosFor, List.mem_cons] at member
      rcases member with rfl | member
      · rfl
      · exact ih (cidx + 1) member

/-- Every record in the flattened constructor inventory retains the name of
one source family as its owner. -/
theorem declaredConstructorInfos_induct
    (stats : InductiveStats) (indTypes : Array InductiveType)
    (isUnsafe : Bool) (context : Context) {info : ConstructorVal}
    (member : info ∈ declaredConstructorInfos stats indTypes isUnsafe
      context) :
    ∃ indType ∈ indTypes.toList, info.induct = indType.name := by
  simp only [declaredConstructorInfos, List.mem_flatMap] at member
  obtain ⟨indType, sourceMember, member⟩ := member
  exact ⟨indType, sourceMember,
    declaredConstructorInfosFor_induct stats indType.name isUnsafe context
      0 indType.ctors member⟩

/--
info: 'Lean4Lean.AddInductive.declaredConstructorInfosFor_numParams' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms AddInductive.declaredConstructorInfosFor_numParams

/-- info: 'Lean4Lean.AddInductive.declaredConstructorInfosFor_induct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AddInductive.declaredConstructorInfosFor_induct

/-- info: 'Lean4Lean.AddInductive.declaredConstructorInfos_induct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AddInductive.declaredConstructorInfos_induct

/-- info: 'Lean4Lean.AddInductive.declaredConstructorInfos_numParams' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms AddInductive.declaredConstructorInfos_numParams

/-- Transparent source-ordered constructor declaration fold. -/
def declareConstructorInfoList (allowPrimitive : Bool) :
    List ConstructorVal → Environment → Except Exception Environment
  | [], env => .ok env
  | info :: infos, env => do
      env.checkName info.name allowPrimitive
      declareConstructorInfoList allowPrimitive infos
        (env.add (.ctorInfo info))

/-- Exact operational trace of every constructor metadata insertion. -/
inductive DeclareConstructorInfoListRun (allowPrimitive : Bool) :
    Environment → List ConstructorVal → Environment → Prop where
  | nil : DeclareConstructorInfoListRun allowPrimitive env [] env
  | cons
      (checkName : env.checkName info.name allowPrimitive = .ok ())
      (tail : DeclareConstructorInfoListRun allowPrimitive
        (env.add (.ctorInfo info)) infos finalEnv) :
      DeclareConstructorInfoListRun allowPrimitive env (info :: infos)
        finalEnv

theorem DeclareConstructorInfoListRun.of_run
    (run : declareConstructorInfoList allowPrimitive infos env =
      .ok finalEnv) :
    DeclareConstructorInfoListRun allowPrimitive env infos finalEnv := by
  induction infos generalizing env with
  | nil =>
      simp only [declareConstructorInfoList, Except.ok.injEq] at run
      subst finalEnv
      exact .nil
  | cons info infos ih =>
      simp only [declareConstructorInfoList] at run
      cases hcheck : env.checkName info.name allowPrimitive with
      | error error =>
          rw [hcheck] at run
          contradiction
      | ok value =>
          have value_eq : value = () := Subsingleton.elim _ _
          subst value
          simp only [hcheck] at run
          exact .cons hcheck (ih run)

theorem DeclareConstructorInfoListRun.environment
    (run : DeclareConstructorInfoListRun allowPrimitive env infos finalEnv) :
    finalEnv = infos.foldl
      (fun env info => env.add (.ctorInfo info)) env := by
  induction run with
  | nil => rfl
  | cons _ _ ih => simpa only [List.foldl_cons] using ih

private theorem declaredConstructorInfoList_constants : ∀
    (infos : List ConstructorVal) (env : Environment),
    (infos.foldl (fun env info => env.add (.ctorInfo info)) env).constants =
      infos.foldl (fun constants info =>
        constants.insert info.name (.ctorInfo info)) env.constants
  | [], _ => rfl
  | info :: infos, env =>
      declaredConstructorInfoList_constants infos
        (env.add (.ctorInfo info))

private theorem declaredConstructorInfoList_quotInit : ∀
    (infos : List ConstructorVal) (env : Environment),
    (infos.foldl (fun env info => env.add (.ctorInfo info)) env).quotInit =
      env.quotInit
  | [], _ => rfl
  | info :: infos, env =>
      declaredConstructorInfoList_quotInit infos
        (env.add (.ctorInfo info))

theorem DeclareConstructorInfoListRun.constants
    (run : DeclareConstructorInfoListRun allowPrimitive env infos finalEnv) :
    finalEnv.constants = infos.foldl
      (fun constants info => constants.insert info.name (.ctorInfo info))
      env.constants := by
  rw [run.environment]
  exact declaredConstructorInfoList_constants infos env

theorem DeclareConstructorInfoListRun.quotInit
    (run : DeclareConstructorInfoListRun allowPrimitive env infos finalEnv) :
    finalEnv.quotInit = env.quotInit := by
  rw [run.environment]
  exact declaredConstructorInfoList_quotInit infos env

def declareConstructors (stats : InductiveStats)
    (indTypes : Array InductiveType) (isUnsafe : Bool) : M Environment :=
  fun context =>
    declareConstructorInfoList context.allowPrimitive
      (declaredConstructorInfos stats indTypes isUnsafe context) context.env

/-- Return true if recursor can map into any universe -/
def isLargeEliminator (stats : InductiveStats) (indTypes : Array InductiveType) : M Bool := do
  if stats.isNotZero then return true
  let #[indType] := indTypes | return false
  match indType.ctors with
  | [] => return true
  | [ctor] =>
    let rec loop type i toCheck
    | 0 => throw .deepRecursion
    | fuel+1 => do
      if let .forallE name dom body bi := type then
        withLocalDecl name bi (consumeTypeAnnotations dom) fun arg => do
          let mut toCheck := toCheck
          if i ≥ stats.params.size then
            if !(← ensureType dom).sortLevel!.isAlwaysZero then
              toCheck := toCheck.push arg
          loop (body.instantiate1 arg) (i + 1) toCheck fuel
      else
        return toCheck.all type.getAppArgs.contains
    loop ctor.type 0 #[] (← readThe Context).fuel.inductiveFuel
  | _ => return false

/-- The kernel's indexed elimination-universe spelling.  Constructing this
name through public `String.append` is extensionally identical to
``(`u).appendIndexAfter i`` while keeping the distinct-index property
available to verification (the latter uses an opaque internal append). -/
def getElimParamName (i : Nat) : Name :=
  .str .anonymous ("u_" ++ Nat.repr i)

/-- Search the kernel's elimination-universe name sequence (`u`, `u_1`, …)
for its first entry not already used by the inductive declaration.  Among
`lparams.length + 1` distinct candidates at least one is available; the
zero-fuel branch is therefore only a totality fallback. -/
def getFreshElimParam.loop (lparams : List Name) (u : Name) (i : Nat) :
    Nat → Name
  | 0 => u
  | fuel + 1 =>
      if lparams.contains u then
        loop lparams (getElimParamName i) (i + 1) fuel
      else
        u

def getFreshElimParam (lparams : List Name) : Name :=
  getFreshElimParam.loop lparams `u 1 (lparams.length + 1)

def getElimLevel (stats : InductiveStats) (indTypes : Array InductiveType) :
    M Level := do
  unless ← isLargeEliminator stats indTypes do return .zero
  let {lparams, ..} ← read
  return .param (getFreshElimParam lparams)

/-- The constructor-shape fragment of the kernel's K-target test. A visible
Pi is accepted only while it belongs to the shared parameter prefix; the
first visible field makes the target ineligible. -/
def isKTargetCtor (nparams : Nat) : Nat → Expr → Bool
  | i, .forallE _ _ body _ => i < nparams && isKTargetCtor nparams (i + 1) body
  | _, _ => true

def isKTarget (stats : InductiveStats) (indTypes : Array InductiveType) : M Bool := do
  let #[indType] := indTypes | return false
  unless stats.resultLevel.isAlwaysZero do return false
  let [ctor] := indType.ctors | return false
  return isKTargetCtor stats.params.size 0 ctor.type

@[inline] def getIIndices (stats : InductiveStats) (t : Expr) : Nat × Array Expr :=
  ((isValidIndApp? stats t).get!, t.getAppArgs[stats.params.size:])

-- FIXME: The function below has been exploded into nested loops as standalone functions
-- because I couldn't get them all to compile together as `let rec`s.
namespace mkRecInfos

def loopArgs1 (stats : InductiveStats) (type : Expr) (i : Nat) (indices : Array Expr)
    (fuel : Nat) (k : Array Expr → M α) : M α := match fuel with
  | 0 => throw .deepRecursion
  | fuel+1 => do
    if let .forallE name dom body bi := type then
      if i < stats.params.size then
        loopArgs1 stats (← whnf <| body.instantiate1 stats.params[i]!) (i + 1) indices fuel k
      else
        withLocalDecl name bi (consumeTypeAnnotations dom) fun arg => do
        loopArgs1 stats (← whnf <| body.instantiate1 arg) i (indices.push arg) fuel k
    else
      k indices

/-- A successful first-phase argument traversal reaches its continuation in
a local extension of the context in which the traversal started. -/
theorem loopArgs1_localExtension
    {root current : Context} (extension : root.LocalExtension current)
    {stats : InductiveStats} {type : Expr} {i : Nat}
    {indices : Array Expr} {fuel : Nat} {k : Array Expr → M α}
    {result : α} {P : Prop}
    (run : loopArgs1 stats type i indices fuel k current = .ok result)
    (done : ∀ nextIndices nextContext,
      root.LocalExtension nextContext →
      k nextIndices nextContext = .ok result → P) : P := by
  induction fuel generalizing type i indices current with
  | zero =>
      simp [loopArgs1, throw, throwThe, MonadExceptOf.throw] at run
  | succ fuel ih =>
      cases type <;> simp only [loopArgs1] at run
      case forallE name dom body bi =>
        split at run
        · simp only [ReaderT.bind, Bind.bind] at run
          cases whnfRun :
              (liftM (TypeChecker.whnf <| body.instantiate1 stats.params[i]!) :
                M Expr) current with
          | error error =>
              rw [whnfRun] at run
              contradiction
          | ok nextType =>
              rw [whnfRun] at run
              simp only [Except.bind] at run
              exact ih extension run
        · rw [withLocalDecl_apply] at run
          simp only [ReaderT.bind, Bind.bind] at run
          cases whnfRun :
              (liftM (TypeChecker.whnf <|
                body.instantiate1 current.freshExpr) : M Expr)
                (current.pushLocalDecl name bi
                  (consumeTypeAnnotations dom)) with
          | error error =>
              rw [whnfRun] at run
              contradiction
          | ok nextType =>
              rw [whnfRun] at run
              simp only [Except.bind] at run
              exact ih
                (extension.push name bi (consumeTypeAnnotations dom)) run
      all_goals exact done indices current extension run

/-- Expose the terminal index array and reader context of `loopArgs1`
independently of its continuation.  This is a proof-only reassociation of
the existing continuation-passing worker; it does not rerun the traversal or
change the executable recursor synthesis path. -/
theorem loopArgs1_eq_capture
    {stats : InductiveStats} {type : Expr} {i : Nat}
    {indices : Array Expr} {fuel : Nat} {k : Array Expr → M α}
    (current : Context) :
    loopArgs1 stats type i indices fuel k current =
      (loopArgs1 stats type i indices fuel
        (fun nextIndices nextContext => .ok (nextIndices, nextContext))
        current).bind fun result => k result.1 result.2 := by
  induction fuel generalizing type i indices current k with
  | zero => rfl
  | succ fuel ih =>
      cases type <;> simp only [loopArgs1]
      case forallE name dom body bi =>
        split
        · simp only [ReaderT.bind, Bind.bind]
          cases run :
              (liftM (TypeChecker.whnf <| body.instantiate1 stats.params[i]!) :
                M Expr) current with
          | error error => simp only [run, Except.bind]
          | ok nextType =>
              simp only [run, Except.bind]
              exact ih (k := k) current
        · simp only [withLocalDecl_apply, ReaderT.bind, Bind.bind]
          cases run :
              (liftM (TypeChecker.whnf <|
                body.instantiate1 current.freshExpr) : M Expr)
                (current.pushLocalDecl name bi
                  (consumeTypeAnnotations dom)) with
          | error error => simp only [run, Except.bind]
          | ok nextType =>
              simp only [run, Except.bind]
              exact ih (k := k)
                (current.pushLocalDecl name bi
                  (consumeTypeAnnotations dom))
      all_goals rfl

/-- Exact parameter/index decomposition of one successful `loopArgs1` run.

The aggregate capture equation records only the final index array and reader
context.  Semantic recursor assembly additionally needs to know which visible
Pi binders were consumed by the shared parameter prefix and which ones were
retained as family indices.  This trace exposes precisely those executable
branches while keeping every WHNF observation tied to the original run. -/
inductive LoopArgs1Trace (stats : InductiveStats) :
    (type : Expr) → (i : Nat) → (indices : Array Expr) → (fuel : Nat) →
      (current : Context) → (finalIndices : Array Expr) →
      (finalContext : Context) → Type where
  | done
      (notForall : type.isForall = false) :
      LoopArgs1Trace stats type i indices fuel current indices current
  | parameter
      (isParameter : i < stats.params.size)
      (nextType : Expr)
      (whnfRun :
        (liftM (TypeChecker.whnf <|
          body.instantiate1 stats.params[i]!) : M Expr) current =
            .ok nextType)
      (tail : LoopArgs1Trace stats nextType (i + 1) indices fuel current
        finalIndices finalContext) :
      LoopArgs1Trace stats (.forallE name domain body binderInfo) i indices
        (fuel + 1) current finalIndices finalContext
  | index
      (notParameter : ¬ i < stats.params.size)
      (nextType : Expr)
      (whnfRun :
        (liftM (TypeChecker.whnf <|
          body.instantiate1 current.freshExpr) : M Expr)
            (current.pushLocalDecl name binderInfo
              (consumeTypeAnnotations domain)) = .ok nextType)
      (tail : LoopArgs1Trace stats nextType i
        (indices.push current.freshExpr) fuel
        (current.pushLocalDecl name binderInfo
          (consumeTypeAnnotations domain)) finalIndices finalContext) :
      LoopArgs1Trace stats (.forallE name domain body binderInfo) i indices
        (fuel + 1) current finalIndices finalContext

/-- Recover the complete parameter/index decomposition from the
continuation-free capture used by recursor synthesis. -/
theorem LoopArgs1Trace.of_run
    {stats : InductiveStats} {type : Expr} {i : Nat}
    {indices finalIndices : Array Expr} {fuel : Nat}
    {current finalContext : Context}
    (run : loopArgs1 stats type i indices fuel
      (fun nextIndices nextContext => .ok (nextIndices, nextContext))
      current = .ok (finalIndices, finalContext)) :
    Nonempty (LoopArgs1Trace stats type i indices fuel current finalIndices
      finalContext) := by
  induction fuel generalizing type i indices current with
  | zero =>
      simp [loopArgs1, throw, throwThe, MonadExceptOf.throw] at run
  | succ fuel ih =>
      cases type <;> simp only [loopArgs1] at run
      case forallE name domain body binderInfo =>
        split at run
        · simp only [ReaderT.bind, Bind.bind] at run
          cases whnfRun :
            (liftM (TypeChecker.whnf <|
              body.instantiate1 stats.params[i]!) : M Expr) current with
          | error error =>
              rw [whnfRun] at run
              contradiction
          | ok nextType =>
              rw [whnfRun] at run
              simp only [ReaderT.bind, Bind.bind, Except.bind] at run
              obtain ⟨tail⟩ := ih run
              exact ⟨.parameter (by assumption) nextType whnfRun tail⟩
        · rw [withLocalDecl_apply] at run
          simp only [ReaderT.bind, Bind.bind] at run
          cases whnfRun :
              (liftM (TypeChecker.whnf <|
                body.instantiate1 current.freshExpr) : M Expr)
                (current.pushLocalDecl name binderInfo
                  (consumeTypeAnnotations domain)) with
          | error error =>
              rw [whnfRun] at run
              contradiction
          | ok nextType =>
              rw [whnfRun] at run
              simp only [Except.bind] at run
              obtain ⟨tail⟩ := ih run
              exact ⟨.index (by assumption) nextType whnfRun tail⟩
      all_goals
        have pairEq : (indices, current) =
            (finalIndices, finalContext) := Except.ok.inj run
        cases pairEq
        exact ⟨.done rfl⟩

variable (stats : InductiveStats) (indTypes : Array InductiveType) (elimLevel : Level) in
def loopInd1 (dIdx : Nat) (recInfos : Array RecInfo) (k : Array RecInfo → M α) : M α := do
  if _h : dIdx < indTypes.size then
    let ctx ← readThe Context
    loopArgs1 stats (← whnf indTypes[dIdx].type) 0 #[] ctx.fuel.inductiveFuel fun indices =>
    let tTy := mkAppN (mkAppN stats.indConsts[dIdx]! stats.params) indices
    withLocalDecl `t .default (consumeTypeAnnotations tTy) fun major => do
    let lctx ← getLCtx
    let motiveTy := lctx.mkForall indices <| lctx.mkForall #[major] <| .sort elimLevel
    let name := if indTypes.size > 1 then (`motive).appendIndexAfter (dIdx+1) else `motive
    withLocalDecl name .default (consumeTypeAnnotations motiveTy) fun motive => do
    loopInd1 (dIdx + 1) (recInfos.push { motive, minors := #[], indices, major }) k
  else
    k recInfos
termination_by indTypes.size - dIdx

/-- The whole first recursor-synthesis phase preserves the same local-
extension invariant as its argument traversal. -/
theorem loopInd1_localExtension
    {root current : Context} (extension : root.LocalExtension current)
    {stats : InductiveStats} {indTypes : Array InductiveType}
    {elimLevel : Level} {dIdx : Nat} {recInfos : Array RecInfo}
    {k : Array RecInfo → M α} {result : α} {P : Prop}
    (run : loopInd1 stats indTypes elimLevel dIdx recInfos k current =
      .ok result)
    (done : ∀ nextInfos nextContext,
      root.LocalExtension nextContext →
      k nextInfos nextContext = .ok result → P) : P := by
  rw [loopInd1.eq_1] at run
  split at run
  · simp only [readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
      ReaderT.bind, Bind.bind, Pure.pure, ReaderT.pure, Except.pure,
      Except.bind] at run
    cases whnfRun :
        (liftM (TypeChecker.whnf indTypes[dIdx].type) : M Expr) current with
    | error error =>
        rw [whnfRun] at run
        contradiction
    | ok normalizedType =>
        rw [whnfRun] at run
        simp only [Except.bind] at run
        exact loopArgs1_localExtension extension run fun indices
          indexContext indexExtension continuationRun => by
            rw [withLocalDecl_apply] at continuationRun
            simp only [getLCtx_apply, ReaderT.bind, Bind.bind, Except.bind,
              Pure.pure, ReaderT.pure, Except.pure] at continuationRun
            rw [withLocalDecl_apply] at continuationRun
            exact loopInd1_localExtension
              ((indexExtension.push `t .default
                (consumeTypeAnnotations
                  (mkAppN (mkAppN stats.indConsts[dIdx]! stats.params)
                    indices))).push
                (if indTypes.size > 1 then
                  (`motive).appendIndexAfter (dIdx + 1)
                else `motive)
                .default
                (consumeTypeAnnotations
                  ((indexContext.pushLocalDecl `t .default
                    (consumeTypeAnnotations
                      (mkAppN (mkAppN stats.indConsts[dIdx]! stats.params)
                        indices))).lctx.mkForall indices <|
                    (indexContext.pushLocalDecl `t .default
                      (consumeTypeAnnotations
                        (mkAppN (mkAppN stats.indConsts[dIdx]! stats.params)
                          indices))).lctx.mkForall
                      #[indexContext.freshExpr] <| .sort elimLevel)))
              continuationRun done
  · exact done recInfos current extension run
termination_by indTypes.size - dIdx

/-- Capture the complete phase-one `RecInfo` array and its final motive
context independently of the callback that consumes them. -/
theorem loopInd1_eq_capture
    {stats : InductiveStats} {indTypes : Array InductiveType}
    {elimLevel : Level} {dIdx : Nat} {recInfos : Array RecInfo}
    {k : Array RecInfo → M α} (current : Context) :
    loopInd1 stats indTypes elimLevel dIdx recInfos k current =
      (loopInd1 stats indTypes elimLevel dIdx recInfos
        (fun nextInfos nextContext => .ok (nextInfos, nextContext))
        current).bind fun result => k result.1 result.2 := by
  conv => rhs; rw [loopInd1.eq_1]
  rw [loopInd1.eq_1]
  split
  · simp only [readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
      ReaderT.bind, Bind.bind, Pure.pure, ReaderT.pure, Except.pure,
      Except.bind]
    cases whnfRun :
        (liftM (TypeChecker.whnf indTypes[dIdx].type) : M Expr) current with
    | error error => simp only [whnfRun, Except.bind]
    | ok normalizedType =>
        simp only [whnfRun, Except.bind]
        conv => lhs; rw [loopArgs1_eq_capture current]
        conv => rhs; rw [loopArgs1_eq_capture current]
        cases indicesRun :
            loopArgs1 stats normalizedType 0 #[]
              current.fuel.inductiveFuel
              (fun nextIndices nextContext =>
                .ok (nextIndices, nextContext)) current with
        | error error => simp only [indicesRun, Except.bind]
        | ok indicesResult =>
            rcases indicesResult with ⟨indices, indexContext⟩
            simp only [indicesRun, Except.bind, withLocalDecl_apply,
              getLCtx_apply, Pure.pure, ReaderT.pure, Except.pure]
            exact loopInd1_eq_capture
              ((indexContext.pushLocalDecl `t .default
                (consumeTypeAnnotations
                  (mkAppN (mkAppN stats.indConsts[dIdx]! stats.params)
                    indices))).pushLocalDecl
                (if indTypes.size > 1 then
                  (`motive).appendIndexAfter (dIdx + 1)
                else `motive)
                .default
                (consumeTypeAnnotations
                  ((indexContext.pushLocalDecl `t .default
                    (consumeTypeAnnotations
                      (mkAppN (mkAppN stats.indConsts[dIdx]! stats.params)
                        indices))).lctx.mkForall indices <|
                    (indexContext.pushLocalDecl `t .default
                      (consumeTypeAnnotations
                        (mkAppN (mkAppN stats.indConsts[dIdx]! stats.params)
                          indices))).lctx.mkForall
                      #[indexContext.freshExpr] <| .sort elimLevel)))
  · rfl
termination_by indTypes.size - dIdx

variable (stats : InductiveStats) in
def loopCtorArgs (t : Expr) (k : Expr → Array Expr → Array Expr → M α) : M α := do
  loop t 0 #[] #[] (← readThe Context).fuel.inductiveFuel
where
  loop t i bu u
  | 0 => throw .deepRecursion
  | fuel+1 => do
    if let .forallE name dom body bi := t then
      if let some param := stats.params[i]? then
        loop (body.instantiate1 param) (i + 1) bu u fuel
      else
        withLocalDecl name bi (consumeTypeAnnotations dom) fun arg => do
        let bu := bu.push arg
        let u := if (← isRecArg stats dom).isSome then u.push arg else u
        loop (body.instantiate1 arg) (i + 1) bu u fuel
    else k t bu u

/-- The inner constructor-argument traversal invokes its continuation only
under local-declaration pushes from its input context. -/
theorem loopCtorArgs_loop_localExtension
    {root current : Context} (extension : root.LocalExtension current)
    {stats : InductiveStats} {t : Expr} {i : Nat}
    {bu u : Array Expr} {fuel : Nat}
    {k : Expr → Array Expr → Array Expr → M α}
    {result : α} {P : Prop}
    (run : loopCtorArgs.loop stats k t i bu u fuel current = .ok result)
    (done : ∀ terminal nextBu nextU nextContext,
      root.LocalExtension nextContext →
      k terminal nextBu nextU nextContext = .ok result → P) : P := by
  induction fuel generalizing t i bu u current with
  | zero =>
      simp [loopCtorArgs.loop, throw, throwThe, MonadExceptOf.throw] at run
  | succ fuel ih =>
      cases t <;> simp only [loopCtorArgs.loop] at run
      case forallE name dom body bi =>
        cases parameterEq : stats.params[i]? with
        | some parameter =>
          simp only [parameterEq] at run
          exact ih extension run
        | none =>
          simp only [parameterEq] at run
          rw [withLocalDecl_apply] at run
          simp only [ReaderT.bind, Bind.bind] at run
          cases recursiveRun :
              isRecArg stats dom
                (current.pushLocalDecl name bi
                  (consumeTypeAnnotations dom)) with
          | error error =>
              rw [recursiveRun] at run
              contradiction
          | ok recursive =>
              rw [recursiveRun] at run
              simp only [Except.bind] at run
              exact ih
                (extension.push name bi (consumeTypeAnnotations dom)) run
      all_goals exact done _ bu u current extension run

/-- Wrapper form of `loopCtorArgs_loop_localExtension`. -/
theorem loopCtorArgs_localExtension
    {root current : Context} (extension : root.LocalExtension current)
    {stats : InductiveStats} {t : Expr}
    {k : Expr → Array Expr → Array Expr → M α}
    {result : α} {P : Prop}
    (run : loopCtorArgs stats t k current = .ok result)
    (done : ∀ terminal nextBu nextU nextContext,
      root.LocalExtension nextContext →
      k terminal nextBu nextU nextContext = .ok result → P) : P := by
  unfold loopCtorArgs at run
  simp only [readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, Pure.pure, ReaderT.pure, Except.pure,
    Except.bind] at run
  exact loopCtorArgs_loop_localExtension extension run done

/-- Continuation-independent capture form of the constructor-argument
worker.  It exposes the terminal result, all constructor arguments, the
recursive-argument subarray, and the exact reader context at which the
continuation is entered. -/
theorem loopCtorArgs_loop_eq_capture
    {stats : InductiveStats} {t : Expr} {i : Nat}
    {bu u : Array Expr} {fuel : Nat}
    {k : Expr → Array Expr → Array Expr → M α}
    (current : Context) :
    loopCtorArgs.loop stats k t i bu u fuel current =
      (loopCtorArgs.loop stats
        (fun terminal nextBu nextU nextContext =>
          .ok (terminal, nextBu, nextU, nextContext))
        t i bu u fuel current).bind fun result =>
          k result.1 result.2.1 result.2.2.1 result.2.2.2 := by
  induction fuel generalizing t i bu u current k with
  | zero => rfl
  | succ fuel ih =>
      cases t <;> simp only [loopCtorArgs.loop]
      case forallE name dom body bi =>
        cases parameterEq : stats.params[i]? with
        | some parameter =>
            simp only [parameterEq]
            exact ih (k := k) current
        | none =>
            simp only [parameterEq, withLocalDecl_apply, ReaderT.bind,
              Bind.bind]
            cases recursiveRun :
                isRecArg stats dom
                  (current.pushLocalDecl name bi
                    (consumeTypeAnnotations dom)) with
            | error error => simp only [recursiveRun, Except.bind]
            | ok recursive =>
                simp only [recursiveRun, Except.bind]
                exact ih (k := k)
                  (current.pushLocalDecl name bi
                    (consumeTypeAnnotations dom))
      all_goals rfl

/-- Wrapper capture equation for `loopCtorArgs`. -/
theorem loopCtorArgs_eq_capture
    {stats : InductiveStats} {t : Expr}
    {k : Expr → Array Expr → Array Expr → M α}
    (current : Context) :
    loopCtorArgs stats t k current =
      (loopCtorArgs stats t
        (fun terminal nextBu nextU nextContext =>
          .ok (terminal, nextBu, nextU, nextContext)) current).bind fun result =>
            k result.1 result.2.1 result.2.2.1 result.2.2.2 := by
  unfold loopCtorArgs
  simp only [readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, Pure.pure, ReaderT.pure, Except.pure,
    Except.bind]
  exact loopCtorArgs_loop_eq_capture current

/-- Complete source-ordered decomposition of a retained `loopCtorArgs`
traversal.  Parameter branches instantiate the shared parameter array and
leave both argument inventories unchanged; field branches push the
annotation-consumed domain, retain the exact recursive-argument
classification run, and extend the inventories accordingly.  The traversal
itself never normalizes the constructor spine. -/
inductive LoopCtorArgsTrace (stats : InductiveStats) :
    (type : Expr) → (i : Nat) → (bu u : Array Expr) → (fuel : Nat) →
      (current : Context) → (terminal : Expr) →
      (finalBu finalU : Array Expr) → (finalContext : Context) → Type where
  | done
      (notForall : type.isForall = false) :
      LoopCtorArgsTrace stats type i bu u fuel current type bu u current
  | parameter
      (parameter : Expr)
      (isParameter : stats.params[i]? = some parameter)
      (tail : LoopCtorArgsTrace stats (body.instantiate1 parameter) (i + 1)
        bu u fuel current terminal finalBu finalU finalContext) :
      LoopCtorArgsTrace stats (.forallE name domain body binderInfo) i bu u
        (fuel + 1) current terminal finalBu finalU finalContext
  | field
      (noParameter : stats.params[i]? = none)
      (recursive : Option Nat)
      (recursiveRun :
        isRecArg stats domain
          (current.pushLocalDecl name binderInfo
            (consumeTypeAnnotations domain)) = .ok recursive)
      (tail : LoopCtorArgsTrace stats
        (body.instantiate1 current.freshExpr) (i + 1)
        (bu.push current.freshExpr)
        (if recursive.isSome then u.push current.freshExpr else u) fuel
        (current.pushLocalDecl name binderInfo
          (consumeTypeAnnotations domain)) terminal finalBu finalU
        finalContext) :
      LoopCtorArgsTrace stats (.forallE name domain body binderInfo) i bu u
        (fuel + 1) current terminal finalBu finalU finalContext

/-- Recover the complete constructor-argument decomposition from the
continuation-free capture used by recursor synthesis. -/
theorem LoopCtorArgsTrace.of_run
    {stats : InductiveStats} {t : Expr} {i : Nat} {bu u : Array Expr}
    {fuel : Nat} {current : Context} {terminal : Expr}
    {finalBu finalU : Array Expr} {finalContext : Context}
    (run : loopCtorArgs.loop stats
      (fun nextTerminal nextBu nextU nextContext =>
        .ok (nextTerminal, nextBu, nextU, nextContext)) t i bu u fuel
      current = .ok (terminal, finalBu, finalU, finalContext)) :
    Nonempty (LoopCtorArgsTrace stats t i bu u fuel current terminal
      finalBu finalU finalContext) := by
  induction fuel generalizing t i bu u current with
  | zero =>
      simp [loopCtorArgs.loop, throw, throwThe, MonadExceptOf.throw] at run
  | succ fuel ih =>
      cases t <;> simp only [loopCtorArgs.loop] at run
      case forallE name dom body bi =>
        cases parameterEq : stats.params[i]? with
        | some parameter =>
            simp only [parameterEq] at run
            obtain ⟨tail⟩ := ih run
            exact ⟨.parameter parameter parameterEq tail⟩
        | none =>
            simp only [parameterEq] at run
            rw [withLocalDecl_apply] at run
            simp only [ReaderT.bind, Bind.bind] at run
            cases recursiveRun :
                isRecArg stats dom
                  (current.pushLocalDecl name bi
                    (consumeTypeAnnotations dom)) with
            | error error =>
                rw [recursiveRun] at run
                contradiction
            | ok recursive =>
                rw [recursiveRun] at run
                simp only [Except.bind] at run
                obtain ⟨tail⟩ := ih run
                exact ⟨.field parameterEq recursive recursiveRun tail⟩
      all_goals
        have quadEq := Except.ok.inj run
        cases quadEq
        exact ⟨.done rfl⟩

/-- Wrapper form of `LoopCtorArgsTrace.of_run` at the exact traversal
entry. -/
theorem LoopCtorArgsTrace.of_capture
    {stats : InductiveStats} {t : Expr} {current : Context}
    {terminal : Expr} {finalBu finalU : Array Expr}
    {finalContext : Context}
    (run : loopCtorArgs stats t
      (fun nextTerminal nextBu nextU nextContext =>
        .ok (nextTerminal, nextBu, nextU, nextContext)) current =
      .ok (terminal, finalBu, finalU, finalContext)) :
    Nonempty (LoopCtorArgsTrace stats t 0 #[] #[]
      current.fuel.inductiveFuel current terminal finalBu finalU
      finalContext) := by
  unfold loopCtorArgs at run
  simp only [readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, Pure.pure, ReaderT.pure, Except.pure,
    Except.bind] at run
  exact LoopCtorArgsTrace.of_run run

def loopUArgs (ui : Expr) (k : Expr → Array Expr → M α) : M α := do
  loop (← whnf (← inferType ui)) #[] (← readThe Context).fuel.inductiveFuel
where
  loop uiTy xs
  | 0 => throw .deepRecursion
  | fuel+1 => do
    if let .forallE name dom body bi := uiTy then
      withLocalDecl name bi (consumeTypeAnnotations dom) fun arg => do
      loop (← whnf <| body.instantiate1 arg) (xs.push arg) fuel
    else
      k uiTy xs

/-- Recursive-argument index synthesis likewise reaches its continuation
only through scoped local-declaration pushes. -/
theorem loopUArgs_loop_localExtension
    {root current : Context} (extension : root.LocalExtension current)
    {uiType : Expr} {xs : Array Expr} {fuel : Nat}
    {k : Expr → Array Expr → M α} {result : α} {P : Prop}
    (run : loopUArgs.loop k uiType xs fuel current = .ok result)
    (done : ∀ terminal nextXs nextContext,
      root.LocalExtension nextContext →
      k terminal nextXs nextContext = .ok result → P) : P := by
  induction fuel generalizing uiType xs current with
  | zero =>
      simp [loopUArgs.loop, throw, throwThe, MonadExceptOf.throw] at run
  | succ fuel ih =>
      cases uiType <;> simp only [loopUArgs.loop] at run
      case forallE name dom body bi =>
        rw [withLocalDecl_apply] at run
        simp only [ReaderT.bind, Bind.bind] at run
        cases whnfRun :
            (liftM (TypeChecker.whnf <|
              body.instantiate1 current.freshExpr) : M Expr)
              (current.pushLocalDecl name bi
                (consumeTypeAnnotations dom)) with
        | error error =>
            rw [whnfRun] at run
            contradiction
        | ok nextType =>
            rw [whnfRun] at run
            simp only [Except.bind] at run
            exact ih (extension.push name bi (consumeTypeAnnotations dom))
              run
      all_goals exact done _ xs current extension run

/-- Wrapper form of `loopUArgs_loop_localExtension`. -/
theorem loopUArgs_localExtension
    {root current : Context} (extension : root.LocalExtension current)
    {ui : Expr} {k : Expr → Array Expr → M α}
    {result : α} {P : Prop}
    (run : loopUArgs ui k current = .ok result)
    (done : ∀ terminal nextXs nextContext,
      root.LocalExtension nextContext →
      k terminal nextXs nextContext = .ok result → P) : P := by
  unfold loopUArgs at run
  simp only [readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, Pure.pure, ReaderT.pure, Except.pure,
    Except.bind] at run
  cases inferRun : (liftM (TypeChecker.inferType ui) : M Expr) current with
  | error error =>
      rw [inferRun] at run
      contradiction
  | ok inferredType =>
      rw [inferRun] at run
      simp only [Except.bind] at run
      cases whnfRun :
          (liftM (TypeChecker.whnf inferredType) : M Expr) current with
      | error error =>
          rw [whnfRun] at run
          contradiction
      | ok normalizedType =>
          rw [whnfRun] at run
          simp only [Except.bind] at run
          exact loopUArgs_loop_localExtension extension run done

/-- Capture the terminal recursive-argument type, its introduced argument
array, and the exact continuation context independently of the consumer. -/
theorem loopUArgs_loop_eq_capture
    {uiType : Expr} {xs : Array Expr} {fuel : Nat}
    {k : Expr → Array Expr → M α} (current : Context) :
    loopUArgs.loop k uiType xs fuel current =
      (loopUArgs.loop
        (fun terminal nextXs nextContext =>
          .ok (terminal, nextXs, nextContext))
        uiType xs fuel current).bind fun result =>
          k result.1 result.2.1 result.2.2 := by
  induction fuel generalizing uiType xs current k with
  | zero => rfl
  | succ fuel ih =>
      cases uiType <;> simp only [loopUArgs.loop]
      case forallE name dom body bi =>
        simp only [withLocalDecl_apply, ReaderT.bind, Bind.bind]
        cases run :
            (liftM (TypeChecker.whnf <|
              body.instantiate1 current.freshExpr) : M Expr)
              (current.pushLocalDecl name bi
                (consumeTypeAnnotations dom)) with
        | error error => simp only [run, Except.bind]
        | ok nextType =>
            simp only [run, Except.bind]
            exact ih (k := k)
              (current.pushLocalDecl name bi
                (consumeTypeAnnotations dom))
      all_goals rfl

/-- Wrapper capture equation for `loopUArgs`, including its initial
`inferType` and WHNF observations. -/
theorem loopUArgs_eq_capture
    {ui : Expr} {k : Expr → Array Expr → M α}
    (current : Context) :
    loopUArgs ui k current =
      (loopUArgs ui
        (fun terminal nextXs nextContext =>
          .ok (terminal, nextXs, nextContext)) current).bind fun result =>
            k result.1 result.2.1 result.2.2 := by
  unfold loopUArgs
  simp only [readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, Pure.pure, ReaderT.pure, Except.pure,
    Except.bind]
  cases inferRun : (liftM (TypeChecker.inferType ui) : M Expr) current with
  | error error => simp only [inferRun, Except.bind]
  | ok inferredType =>
      simp only [inferRun, Except.bind]
      cases whnfRun :
          (liftM (TypeChecker.whnf inferredType) : M Expr) current with
      | error error => simp only [whnfRun, Except.bind]
      | ok normalizedType =>
          simp only [whnfRun, Except.bind]
          exact loopUArgs_loop_eq_capture current

/-- Complete decomposition of the inner recursive-argument index loop.
Every step retains the exact WHNF observation that produced the next
traversal source. -/
inductive LoopUArgsInnerTrace :
    (type : Expr) → (xs : Array Expr) → (fuel : Nat) →
      (current : Context) → (terminal : Expr) → (finalXs : Array Expr) →
      (finalContext : Context) → Type where
  | done
      (notForall : type.isForall = false) :
      LoopUArgsInnerTrace type xs fuel current type xs current
  | step
      (nextType : Expr)
      (whnfRun :
        (liftM (TypeChecker.whnf <|
          body.instantiate1 current.freshExpr) : M Expr)
            (current.pushLocalDecl name binderInfo
              (consumeTypeAnnotations domain)) = .ok nextType)
      (tail : LoopUArgsInnerTrace nextType (xs.push current.freshExpr) fuel
        (current.pushLocalDecl name binderInfo
          (consumeTypeAnnotations domain)) terminal finalXs finalContext) :
      LoopUArgsInnerTrace (.forallE name domain body binderInfo) xs
        (fuel + 1) current terminal finalXs finalContext

/-- Recover the inner index-loop decomposition from its continuation-free
capture. -/
theorem LoopUArgsInnerTrace.of_run
    {uiType : Expr} {xs : Array Expr} {fuel : Nat} {current : Context}
    {terminal : Expr} {finalXs : Array Expr} {finalContext : Context}
    (run : loopUArgs.loop
      (fun nextTerminal nextXs nextContext =>
        .ok (nextTerminal, nextXs, nextContext)) uiType xs fuel current =
      .ok (terminal, finalXs, finalContext)) :
    Nonempty (LoopUArgsInnerTrace uiType xs fuel current terminal finalXs
      finalContext) := by
  induction fuel generalizing uiType xs current with
  | zero =>
      simp [loopUArgs.loop, throw, throwThe, MonadExceptOf.throw] at run
  | succ fuel ih =>
      cases uiType <;> simp only [loopUArgs.loop] at run
      case forallE name dom body bi =>
        rw [withLocalDecl_apply] at run
        simp only [ReaderT.bind, Bind.bind] at run
        cases whnfRun :
            (liftM (TypeChecker.whnf <|
              body.instantiate1 current.freshExpr) : M Expr)
              (current.pushLocalDecl name bi
                (consumeTypeAnnotations dom)) with
        | error error =>
            rw [whnfRun] at run
            contradiction
        | ok nextType =>
            rw [whnfRun] at run
            simp only [Except.bind] at run
            obtain ⟨tail⟩ := ih run
            exact ⟨.step nextType whnfRun tail⟩
      all_goals
        have tripleEq := Except.ok.inj run
        cases tripleEq
        exact ⟨.done rfl⟩

/-- One retained recursive-argument index synthesis: the initial type
inference and normalization observations, followed by the complete inner
index loop. -/
structure LoopUArgsTrace
    (ui : Expr) (current : Context) (terminal : Expr)
    (finalXs : Array Expr) (finalContext : Context) where
  inferred : Expr
  inferRun : (liftM (TypeChecker.inferType ui) : M Expr) current =
    .ok inferred
  normalized : Expr
  whnfRun : (liftM (TypeChecker.whnf inferred) : M Expr) current =
    .ok normalized
  inner : LoopUArgsInnerTrace normalized #[] current.fuel.inductiveFuel
    current terminal finalXs finalContext

/-- Recover the complete recursive-argument index synthesis from its
continuation-free capture. -/
theorem LoopUArgsTrace.of_run
    {ui : Expr} {current : Context} {terminal : Expr}
    {finalXs : Array Expr} {finalContext : Context}
    (run : loopUArgs ui
      (fun nextTerminal nextXs nextContext =>
        .ok (nextTerminal, nextXs, nextContext)) current =
      .ok (terminal, finalXs, finalContext)) :
    Nonempty (LoopUArgsTrace ui current terminal finalXs finalContext) := by
  unfold loopUArgs at run
  simp only [readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, Pure.pure, ReaderT.pure, Except.pure,
    Except.bind] at run
  cases inferRun : (liftM (TypeChecker.inferType ui) : M Expr) current with
  | error error =>
      rw [inferRun] at run
      contradiction
  | ok inferred =>
      rw [inferRun] at run
      simp only [Except.bind] at run
      cases whnfRun :
          (liftM (TypeChecker.whnf inferred) : M Expr) current with
      | error error =>
          rw [whnfRun] at run
          contradiction
      | ok normalized =>
          rw [whnfRun] at run
          simp only [Except.bind] at run
          obtain ⟨inner⟩ := LoopUArgsInnerTrace.of_run run
          exact ⟨⟨inferred, inferRun, normalized, whnfRun, inner⟩⟩

variable (stats : InductiveStats) (u : Array Expr) (recInfos : Array RecInfo) in
def loopU (i : Nat) (v : Array Expr) (k : Array Expr → M α) : M α := do
  if _h : i < u.size then
    let ui := u[i]
    let viTy ← loopUArgs ui fun uiTy xs => do
      let (itIdx, itIndices) := getIIndices stats uiTy
      return (← getLCtx).mkForall xs <|
        .app (mkAppN recInfos[itIdx]!.motive itIndices) (mkAppN ui xs)
    let vName := ((← getLCtx).get! ui.fvarId!).userName.appendAfter "_ih"
    withLocalDecl vName .default (consumeTypeAnnotations viTy) fun vi => do
    loopU (i + 1) (v.push vi) k
  else
    k v
termination_by u.size - i

/-- Recursive hypotheses retained by phase two are added by one local push
per hypothesis; temporary index binders created by `loopUArgs` are abstracted
back into the hypothesis type and therefore do not escape that subcall. -/
theorem loopU_localExtension
    {root current : Context} (extension : root.LocalExtension current)
    {stats : InductiveStats} {u : Array Expr}
    {recInfos : Array RecInfo} {i : Nat} {v : Array Expr}
    {k : Array Expr → M α} {result : α} {P : Prop}
    (run : loopU stats u recInfos i v k current = .ok result)
    (done : ∀ nextV nextContext,
      root.LocalExtension nextContext →
      k nextV nextContext = .ok result → P) : P := by
  rw [loopU.eq_1] at run
  split at run
  · simp only [ReaderT.bind, Bind.bind] at run
    cases argsRun :
        loopUArgs u[i] (fun uiType xs =>
          ReaderT.bind getLCtx fun implementationLCtx =>
            pure (implementationLCtx.mkForall xs <|
              .app
                (mkAppN recInfos[(getIIndices stats uiType).fst]!.motive
                  (getIIndices stats uiType).snd)
                (mkAppN u[i] xs))) current with
    | error error =>
        rw [argsRun] at run
        contradiction
    | ok hypothesisType =>
        rw [argsRun] at run
        simp only [Except.bind, getLCtx_apply, Pure.pure, ReaderT.pure,
          Except.pure] at run
        rw [withLocalDecl_apply] at run
        exact loopU_localExtension
          (extension.push
            ((current.lctx.get! u[i].fvarId!).userName.appendAfter "_ih")
            .default (consumeTypeAnnotations hypothesisType)) run done
  · exact done v current extension run
termination_by u.size - i

/-- Capture the complete recursive-hypothesis array and the exact context at
which `loopU` reaches its continuation. -/
theorem loopU_eq_capture
    {stats : InductiveStats} {u : Array Expr}
    {recInfos : Array RecInfo} {i : Nat} {v : Array Expr}
    {k : Array Expr → M α} (current : Context) :
    loopU stats u recInfos i v k current =
      (loopU stats u recInfos i v
        (fun nextV nextContext => .ok (nextV, nextContext)) current).bind
          fun result => k result.1 result.2 := by
  conv => rhs; rw [loopU.eq_1]
  rw [loopU.eq_1]
  split
  · simp only [ReaderT.bind, Bind.bind]
    cases argsRun :
        loopUArgs u[i] (fun uiType xs =>
          ReaderT.bind getLCtx fun implementationLCtx =>
            pure (implementationLCtx.mkForall xs <|
              .app
                (mkAppN recInfos[(getIIndices stats uiType).fst]!.motive
                  (getIIndices stats uiType).snd)
                (mkAppN u[i] xs))) current with
    | error error =>
        rfl
    | ok hypothesisType =>
        simp only [Except.bind, getLCtx_apply, Pure.pure, ReaderT.pure,
          Except.pure, withLocalDecl_apply]
        exact loopU_eq_capture
          (current.pushLocalDecl
            ((current.lctx.get! u[i].fvarId!).userName.appendAfter "_ih")
            .default (consumeTypeAnnotations hypothesisType))
  · rfl
termination_by u.size - i

/-- Complete source-ordered decomposition of a retained `loopU` run.  Each
step retains the exact captured hypothesis-type synthesis for one recursive
argument and the local push that stores it. -/
inductive LoopUTrace (stats : InductiveStats) (u : Array Expr)
    (recInfos : Array RecInfo) :
    (i : Nat) → (v : Array Expr) → (current : Context) →
      (finalV : Array Expr) → (finalContext : Context) → Type where
  | done
      (finished : ¬ i < u.size) :
      LoopUTrace stats u recInfos i v current v current
  | step
      (inBounds : i < u.size)
      (hypothesisType : Expr)
      (hypothesisRun :
        loopUArgs u[i] (fun uiType xs =>
          ReaderT.bind getLCtx fun implementationLCtx =>
            pure (implementationLCtx.mkForall xs <|
              .app
                (mkAppN recInfos[(getIIndices stats uiType).fst]!.motive
                  (getIIndices stats uiType).snd)
                (mkAppN u[i] xs))) current = .ok hypothesisType)
      (tail : LoopUTrace stats u recInfos (i + 1)
        (v.push current.freshExpr)
        (current.pushLocalDecl
          ((current.lctx.get! u[i].fvarId!).userName.appendAfter "_ih")
          .default (consumeTypeAnnotations hypothesisType))
        finalV finalContext) :
      LoopUTrace stats u recInfos i v current finalV finalContext

/-- Recover the complete recursive-hypothesis decomposition from the
continuation-free capture used by recursor synthesis. -/
theorem LoopUTrace.of_run
    {stats : InductiveStats} {u : Array Expr} {recInfos : Array RecInfo}
    {i : Nat} {v : Array Expr} {current : Context}
    {finalV : Array Expr} {finalContext : Context}
    (run : loopU stats u recInfos i v
      (fun nextV nextContext => .ok (nextV, nextContext)) current =
      .ok (finalV, finalContext)) :
    Nonempty (LoopUTrace stats u recInfos i v current finalV
      finalContext) := by
  rw [loopU.eq_1] at run
  split at run
  · simp only [ReaderT.bind, Bind.bind] at run
    cases argsRun :
        loopUArgs u[i] (fun uiType xs =>
          ReaderT.bind getLCtx fun implementationLCtx =>
            pure (implementationLCtx.mkForall xs <|
              .app
                (mkAppN recInfos[(getIIndices stats uiType).fst]!.motive
                  (getIIndices stats uiType).snd)
                (mkAppN u[i] xs))) current with
    | error error =>
        rw [argsRun] at run
        contradiction
    | ok hypothesisType =>
        rw [argsRun] at run
        simp only [Except.bind, getLCtx_apply, Pure.pure, ReaderT.pure,
          Except.pure] at run
        rw [withLocalDecl_apply] at run
        obtain ⟨tail⟩ := LoopUTrace.of_run run
        exact ⟨.step ‹_› hypothesisType argsRun tail⟩
  · have pairEq := Except.ok.inj run
    cases pairEq
    exact ⟨.done ‹_›⟩
termination_by u.size - i

variable (stats : InductiveStats) (indTypeName : Name) (dIdx : Nat) in
def loopCtors (recInfos : Array RecInfo)
    (ctors : List Constructor) (k : Array RecInfo → M α) : M α := match ctors with
  | ctor::ctors =>
    loopCtorArgs stats ctor.type fun t bu u => do
    let (itIdx, itIndices) := getIIndices stats t
    let introApp := mkAppN (mkAppN (.const ctor.name stats.levels) stats.params) bu
    let motiveApp := Expr.app (mkAppN recInfos[itIdx]!.motive itIndices) introApp
    loopU stats u recInfos 0 #[] fun v => do
    let lctx ← getLCtx
    let minorTy := lctx.mkForall bu <| lctx.mkForall v motiveApp
    let minorName := ctor.name.replacePrefix indTypeName .anonymous
    withLocalDecl minorName .default (consumeTypeAnnotations minorTy) fun minor => do
    let recInfos := recInfos.modify dIdx fun s => { s with minors := s.minors.push minor }
    loopCtors recInfos ctors k
  | [] => k recInfos

/-- Constructor traversal composes the argument, recursive-hypothesis, and
minor-declaration pushes without losing the local-extension invariant. -/
theorem loopCtors_localExtension
    {root current : Context} (extension : root.LocalExtension current)
    {stats : InductiveStats} {indTypeName : Name} {dIdx : Nat}
    {recInfos : Array RecInfo} {ctors : List Constructor}
    {k : Array RecInfo → M α} {result : α} {P : Prop}
    (run : loopCtors stats indTypeName dIdx recInfos ctors k current =
      .ok result)
    (done : ∀ nextInfos nextContext,
      root.LocalExtension nextContext →
      k nextInfos nextContext = .ok result → P) : P := by
  induction ctors generalizing recInfos current with
  | nil => exact done recInfos current extension run
  | cons ctor ctors ih =>
      rw [loopCtors] at run
      exact loopCtorArgs_localExtension extension run fun terminal
        constructorArgs recursiveArgs argumentContext argumentExtension
        continuationRun => by
          exact loopU_localExtension argumentExtension continuationRun
            fun hypotheses hypothesisContext hypothesisExtension minorRun => by
              simp only [getLCtx_apply, ReaderT.bind, Bind.bind, Except.bind,
                Pure.pure, ReaderT.pure, Except.pure] at minorRun
              rw [withLocalDecl_apply] at minorRun
              exact ih
                (hypothesisExtension.push
                  (ctor.name.replacePrefix indTypeName .anonymous) .default
                  (consumeTypeAnnotations
                    (hypothesisContext.lctx.mkForall constructorArgs <|
                      hypothesisContext.lctx.mkForall hypotheses <|
                        .app
                          (mkAppN
                            recInfos[(getIIndices stats terminal).fst]!.motive
                            (getIIndices stats terminal).snd)
                          (mkAppN
                            (mkAppN (.const ctor.name stats.levels)
                              stats.params)
                            constructorArgs))))
                minorRun

/-- Capture the final `RecInfo` array and context of one constructor-list
traversal independently of the continuation that consumes them. -/
theorem loopCtors_eq_capture
    {stats : InductiveStats} {indTypeName : Name} {dIdx : Nat}
    {recInfos : Array RecInfo} {ctors : List Constructor}
    {k : Array RecInfo → M α} (current : Context) :
    loopCtors stats indTypeName dIdx recInfos ctors k current =
      (loopCtors stats indTypeName dIdx recInfos ctors
        (fun nextInfos nextContext => .ok (nextInfos, nextContext))
        current).bind fun result => k result.1 result.2 := by
  induction ctors generalizing recInfos current k with
  | nil => rfl
  | cons ctor ctors ih =>
      simp only [loopCtors]
      conv => lhs; rw [loopCtorArgs_eq_capture current]
      conv => rhs; rw [loopCtorArgs_eq_capture current]
      cases argsRun :
          loopCtorArgs stats ctor.type
            (fun terminal nextBu nextU nextContext =>
              .ok (terminal, nextBu, nextU, nextContext)) current with
      | error error => simp only [argsRun, Except.bind]
      | ok argsResult =>
          rcases argsResult with
            ⟨terminal, constructorArgs, recursiveArgs, argumentContext⟩
          simp only [argsRun, Except.bind]
          conv => lhs; rw [loopU_eq_capture argumentContext]
          conv => rhs; rw [loopU_eq_capture argumentContext]
          cases hypothesesRun :
              loopU stats recursiveArgs recInfos 0 #[]
                (fun nextHypotheses nextContext =>
                  .ok (nextHypotheses, nextContext)) argumentContext with
          | error error => simp only [hypothesesRun, Except.bind]
          | ok hypothesesResult =>
              rcases hypothesesResult with
                ⟨hypotheses, hypothesisContext⟩
              simp only [hypothesesRun, Except.bind, getLCtx_apply,
                Pure.pure, ReaderT.pure, Except.pure, withLocalDecl_apply]
              exact ih (k := k)
                (hypothesisContext.pushLocalDecl
                  (ctor.name.replacePrefix indTypeName .anonymous) .default
                  (consumeTypeAnnotations
                    (hypothesisContext.lctx.mkForall constructorArgs <|
                      hypothesisContext.lctx.mkForall hypotheses <|
                        .app
                          (mkAppN
                            recInfos[(getIIndices stats terminal).fst]!.motive
                            (getIIndices stats terminal).snd)
                          (mkAppN
                            (mkAppN (.const ctor.name stats.levels)
                              stats.params)
                            constructorArgs))))

variable (stats : InductiveStats) (indTypes : Array InductiveType) in
def loopInd2 (dIdx : Nat) (recInfos : Array RecInfo) (k : Array RecInfo → M α) : M α := do
  if _h : dIdx < indTypes.size then
    let indType := indTypes[dIdx]
    let indTypeName := indType.name
    loopCtors stats indTypeName dIdx recInfos indType.ctors fun recInfos =>
    loopInd2 (dIdx + 1) recInfos k
  else
    k recInfos
termination_by indTypes.size - dIdx

/-- The complete second synthesis phase reaches its final callback in a
local extension of the phase-one context. -/
theorem loopInd2_localExtension
    {root current : Context} (extension : root.LocalExtension current)
    {stats : InductiveStats} {indTypes : Array InductiveType}
    {dIdx : Nat} {recInfos : Array RecInfo} {k : Array RecInfo → M α}
    {result : α} {P : Prop}
    (run : loopInd2 stats indTypes dIdx recInfos k current = .ok result)
    (done : ∀ nextInfos nextContext,
      root.LocalExtension nextContext →
      k nextInfos nextContext = .ok result → P) : P := by
  rw [loopInd2.eq_1] at run
  split at run
  · exact loopCtors_localExtension extension run fun nextInfos nextContext
      nextExtension continuationRun =>
        loopInd2_localExtension nextExtension continuationRun done
  · exact done recInfos current extension run
termination_by indTypes.size - dIdx

/-- Capture the complete phase-two `RecInfo` array and its final synthesis
context independently of the callback that consumes them. -/
theorem loopInd2_eq_capture
    {stats : InductiveStats} {indTypes : Array InductiveType}
    {dIdx : Nat} {recInfos : Array RecInfo} {k : Array RecInfo → M α}
    (current : Context) :
    loopInd2 stats indTypes dIdx recInfos k current =
      (loopInd2 stats indTypes dIdx recInfos
        (fun nextInfos nextContext => .ok (nextInfos, nextContext))
        current).bind fun result => k result.1 result.2 := by
  conv => rhs; rw [loopInd2.eq_1]
  rw [loopInd2.eq_1]
  split
  · conv => lhs; rw [loopCtors_eq_capture current]
    conv => rhs; rw [loopCtors_eq_capture current]
    cases constructorsRun :
        loopCtors stats indTypes[dIdx].name dIdx recInfos
          indTypes[dIdx].ctors
          (fun nextInfos nextContext => .ok (nextInfos, nextContext))
          current with
    | error error => simp only [constructorsRun, Except.bind]
    | ok constructorsResult =>
        rcases constructorsResult with ⟨nextInfos, nextContext⟩
        simp only [constructorsRun, Except.bind]
        exact loopInd2_eq_capture nextContext
  · rfl
termination_by indTypes.size - dIdx

end mkRecInfos

def mkRecInfos (stats : InductiveStats) (indTypes : Array InductiveType)
    (elimLevel : Level) (k : Array RecInfo → M α) : M α := fun context =>
  match mkRecInfos.loopInd1 stats indTypes elimLevel 0 #[]
      (fun recInfos phase1Context => .ok (recInfos, phase1Context))
      context with
  | .error error => .error error
  | .ok (phase1Infos, phase1Context) =>
      mkRecInfos.loopInd2 stats indTypes 0 phase1Infos k phase1Context

def getRecLevels (elimLevel : Level) (levels : List Level) : List Level :=
  if elimLevel.isParam then elimLevel :: levels else levels

def getRecLevelParams (elimLevel : Level) (lparams : List Name) : List Name :=
  if let .param u := elimLevel then u :: lparams else lparams

def mkRecRules (indTypes : Array InductiveType) (elimLevel : Level) (stats : InductiveStats)
    (dIdx : Nat) (motives : Array Expr) (minors : Array Expr) :
    StateT Nat M (List RecursorRule) := do
  let d := indTypes[dIdx]!
  let lvls := getRecLevels elimLevel stats.levels
  let mut rules := #[]
  for ctor in d.ctors do
    let rule ← fun minorIdx => mkRecInfos.loopCtorArgs stats ctor.type fun _ bu u =>
      let rec loopU i (v : Array Expr) k := do
        if _h : i < u.size then
          let ui := u[i]
          let val ← mkRecInfos.loopUArgs ui fun uiTy xs => do
            let (itIdx, itIndices) := getIIndices stats uiTy
            let val := .const (mkRecName indTypes[itIdx]!.name) lvls
            let val := mkAppN (mkAppN (mkAppN (mkAppN val stats.params) motives) minors) itIndices
            return (← getLCtx).mkLambda xs <| val.app (mkAppN ui xs)
          loopU (i + 1) (v.push val) k
        else
          k v
      termination_by u.size - i
      loopU 0 #[] fun v => do
      let lctx ← getLCtx
      let rule := {
        ctor := ctor.name
        nfields := bu.size
        rhs := lctx.mkLambda stats.params <| lctx.mkLambda motives <|
          lctx.mkLambda minors <| lctx.mkLambda bu <|
          mkAppN (mkAppN minors[minorIdx]! bu) v
      }
      return (rule, minorIdx + 1)
    rules := rules.push rule
  return rules.toList

/-- Transparent source-ordered recursor declaration fold. -/
def declareRecursorInfoList (allowPrimitive : Bool) :
    List RecursorVal → Environment → Except Exception Environment
  | [], env => .ok env
  | info :: infos, env => do
      env.checkName info.name allowPrimitive
      declareRecursorInfoList allowPrimitive infos
        (env.add (.recInfo info))

/-- Exact operational trace of every generated recursor insertion. -/
inductive DeclareRecursorInfoListRun (allowPrimitive : Bool) :
    Environment → List RecursorVal → Environment → Prop where
  | nil : DeclareRecursorInfoListRun allowPrimitive env [] env
  | cons
      (checkName : env.checkName info.name allowPrimitive = .ok ())
      (tail : DeclareRecursorInfoListRun allowPrimitive
        (env.add (.recInfo info)) infos finalEnv) :
      DeclareRecursorInfoListRun allowPrimitive env (info :: infos) finalEnv

theorem DeclareRecursorInfoListRun.run
    (trace : DeclareRecursorInfoListRun allowPrimitive env infos finalEnv) :
    declareRecursorInfoList allowPrimitive infos env = .ok finalEnv := by
  induction trace with
  | nil => rfl
  | cons checkName _ ih =>
      simp only [declareRecursorInfoList, checkName, Bind.bind, Except.bind]
      exact ih

theorem DeclareRecursorInfoListRun.environment
    (trace : DeclareRecursorInfoListRun allowPrimitive env infos finalEnv) :
    finalEnv = infos.foldl
      (fun env info => env.add (.recInfo info)) env := by
  induction trace with
  | nil => rfl
  | cons _ _ ih => simpa only [List.foldl_cons] using ih

private theorem declaredRecursorInfoList_constants : ∀
    (infos : List RecursorVal) (env : Environment),
    (infos.foldl (fun env info => env.add (.recInfo info)) env).constants =
      infos.foldl (fun constants info =>
        constants.insert info.name (.recInfo info)) env.constants
  | [], _ => rfl
  | info :: infos, env =>
      declaredRecursorInfoList_constants infos (env.add (.recInfo info))

private theorem declaredRecursorInfoList_quotInit : ∀
    (infos : List RecursorVal) (env : Environment),
    (infos.foldl (fun env info => env.add (.recInfo info)) env).quotInit =
      env.quotInit
  | [], _ => rfl
  | info :: infos, env =>
      declaredRecursorInfoList_quotInit infos (env.add (.recInfo info))

theorem DeclareRecursorInfoListRun.constants
    (trace : DeclareRecursorInfoListRun allowPrimitive env infos finalEnv) :
    finalEnv.constants = infos.foldl
      (fun constants info => constants.insert info.name (.recInfo info))
      env.constants := by
  rw [trace.environment]
  exact declaredRecursorInfoList_constants infos env

theorem DeclareRecursorInfoListRun.quotInit
    (trace : DeclareRecursorInfoListRun allowPrimitive env infos finalEnv) :
    finalEnv.quotInit = env.quotInit := by
  rw [trace.environment]
  exact declaredRecursorInfoList_quotInit infos env

/-- The exact source-ordered recursor metadata produced by `run`, paired with
the kernel environment after those records have been installed. -/
structure RecursorDeclarationResult where
  initialEnv : Environment
  allowPrimitive : Bool
  kTarget : Bool
  sourceTypes : Array InductiveType
  levelParams : List Name
  isUnsafe : Bool
  infos : List RecursorVal
  infos_names : infos.map (·.name) =
    sourceTypes.toList.map (fun indType => mkRecName indType.name)
  infos_kTarget : ∀ info ∈ infos, info.k = kTarget
  infos_levelParams : ∀ info ∈ infos, info.levelParams = levelParams
  infos_isUnsafe : ∀ info ∈ infos, info.isUnsafe = isUnsafe
  info_of_source_index : ∀ (i : Nat) (_upper : i < sourceTypes.size),
    ∃ info ∈ infos, info.name = mkRecName sourceTypes[i].name
  env : Environment
  trace : DeclareRecursorInfoListRun allowPrimitive initialEnv infos env

/-- The source-ordered result of the transparent recursor worker before it is
repackaged with its reader-context provenance.  This is public so downstream
verification can reason from the retained producer equation without
reimplementing recursor synthesis. -/
structure RecursorDeclarationTail
    (allowPrimitive : Bool) (initialEnv : Environment) (kTarget : Bool)
    (sourceTypes : Array InductiveType) (startIndex : Nat)
    (levelParams : List Name) (isUnsafe : Bool) where
  infos : List RecursorVal
  infos_names : infos.map (·.name) =
    (sourceTypes.toList.drop startIndex).map
      (fun indType => mkRecName indType.name)
  infos_kTarget : ∀ info ∈ infos, info.k = kTarget
  infos_levelParams : ∀ info ∈ infos, info.levelParams = levelParams
  infos_isUnsafe : ∀ info ∈ infos, info.isUnsafe = isUnsafe
  info_of_source_index : ∀ (i : Nat) (_lower : startIndex ≤ i)
    (_upper : i < sourceTypes.size),
    ∃ info ∈ infos, info.name = mkRecName sourceTypes[i].name
  env : Environment
  trace : DeclareRecursorInfoListRun allowPrimitive initialEnv infos env

namespace declareRecursors

/-- The inferred-implicit recursor type assembled from the local declarations
created by `mkRecInfos`. -/
def generatedRecursorType (stats : InductiveStats)
    (motives minors : Array Expr) (lctx : LocalContext) (info : RecInfo) : Expr :=
  (lctx.mkForall stats.params <|
    lctx.mkForall motives <|
    lctx.mkForall minors <|
    lctx.mkForall info.indices <|
    lctx.mkForall #[info.major] <|
    .app (mkAppN info.motive info.indices) info.major).inferImplicit 1000 false

/-- Source-indexed list of the recursor types assembled by `loop`.  This
definition mirrors only the family traversal; rule generation and environment
insertion do not affect these headers. -/
def generatedRecursorTypes (stats : InductiveStats)
    (indTypes : Array InductiveType) (recInfos : Array RecInfo)
    (motives minors : Array Expr) (lctx : LocalContext) : Nat → List Expr
  | dIdx =>
      if h : dIdx < indTypes.size then
        generatedRecursorType stats motives minors lctx recInfos[dIdx]! ::
          generatedRecursorTypes stats indTypes recInfos motives minors lctx
            (dIdx + 1)
      else
        []
termination_by dIdx => indTypes.size - dIdx

/-- Pure assembly of one generated recursor record once its rules have been
synthesized.  Its translation-visible header does not depend on `rules`. -/
def generatedRecursorVal (stats : InductiveStats)
    (indTypes : Array InductiveType) (elimLevel : Level) (k : Bool)
    (motives minors : Array Expr) (lctx : LocalContext)
    (lparams : List Name) (isUnsafe : Bool) (dIdx : Nat)
    (indType : InductiveType) (info : RecInfo)
    (rules : List RecursorRule) : RecursorVal := {
  name := mkRecName indType.name
  levelParams := getRecLevelParams elimLevel lparams
  type := generatedRecursorType stats motives minors lctx info
  all := indTypes.map (·.name) |>.toList
  numParams := stats.params.size
  numIndices := stats.nindices[dIdx]!
  numMotives := motives.size
  numMinors := minors.size
  rules, k, isUnsafe }

/-- Data-level wrapper for the successful name-check equation retained by the
recursor declaration worker. -/
structure NameCheckCertificate (env : Environment) (name : Name)
    (allowPrimitive : Bool) : Type where
  run : env.checkName name allowPrimitive = .ok ()

/-- Check one generated recursor name while retaining the successful kernel
equation needed by the declaration trace.  Keeping the certificate in an
ordinary `Except` result avoids making the remainder of recursor synthesis
depend on the equation compiler's match proof. -/
def checkNameCertificate (env : Environment) (name : Name)
    (allowPrimitive : Bool) :
    Except Exception (NameCheckCertificate env name allowPrimitive) :=
  match hcheck : env.checkName name allowPrimitive with
  | .error error => .error error
  | .ok value =>
      have value_eq : value = () := Subsingleton.elim _ _
      .ok { run := hcheck.trans (congrArg Except.ok value_eq) }

/-- Generate and install one recursor per family.  The rule-state counter is
threaded across the whole block, and each name is checked immediately after
that family's rules are generated, preserving the operational order of the
original loop in `run`. -/
def loop (stats : InductiveStats) (indTypes : Array InductiveType)
    (elimLevel : Level) (k : Bool) (recInfos : Array RecInfo)
    (motives minors : Array Expr) (lctx : LocalContext)
    (lparams : List Name) (isUnsafe allowPrimitive : Bool) :
    (dIdx : Nat) → (env : Environment) →
      StateT Nat M
        (RecursorDeclarationTail allowPrimitive env k indTypes dIdx
          (getRecLevelParams elimLevel lparams) isUnsafe)
  | dIdx, env => do
      if h : dIdx < indTypes.size then
        let indType := indTypes[dIdx]
        let info := recInfos[dIdx]!
        let rules ← mkRecRules indTypes elimLevel stats dIdx motives minors
        let name := mkRecName indType.name
        let recursor := generatedRecursorVal stats indTypes elimLevel k motives
          minors lctx lparams isUnsafe dIdx indType info rules
        let hcheck ← checkNameCertificate env name allowPrimitive
        let tail ← loop stats indTypes elimLevel k recInfos motives minors lctx
          lparams isUnsafe allowPrimitive (dIdx + 1)
            (env.add (.recInfo recursor))
        pure {
          infos := recursor :: tail.infos
          infos_names := by
            have dropped : indTypes.toList.drop dIdx =
                indTypes[dIdx] :: indTypes.toList.drop (dIdx + 1) := by
              rw [List.drop_eq_getElem_cons (by simpa using h)]
              simp
            simp only [List.map_cons]
            rw [tail.infos_names, dropped]
            rfl
          infos_kTarget := by
            intro other member
            rcases List.mem_cons.mp member with rfl | member
            · rfl
            · exact tail.infos_kTarget other member
          infos_levelParams := by
            intro other member
            rcases List.mem_cons.mp member with rfl | member
            · rfl
            · exact tail.infos_levelParams other member
          infos_isUnsafe := by
            intro other member
            rcases List.mem_cons.mp member with rfl | member
            · rfl
            · exact tail.infos_isUnsafe other member
          info_of_source_index := by
            intro i lower upper
            by_cases equal : i = dIdx
            · subst i
              exact ⟨recursor, List.mem_cons_self, rfl⟩
            · obtain ⟨other, member, name_eq⟩ :=
                tail.info_of_source_index i (by omega) upper
              exact ⟨other, List.mem_cons_of_mem recursor member, name_eq⟩
          env := tail.env
          trace := .cons hcheck.run tail.trace }
      else
        pure {
          infos := []
          infos_names := by
            simp only [List.map_nil]
            have dropped : indTypes.toList.drop dIdx = [] := by
              apply List.drop_eq_nil_iff.mpr
              simpa only [Array.length_toList] using Nat.le_of_not_gt h
            rw [dropped]
            rfl
          infos_kTarget := by simp
          infos_levelParams := by simp
          infos_isUnsafe := by simp
          info_of_source_index := by
            intro i lower upper
            exact (h (by omega)).elim
          env
          trace := .nil }
termination_by dIdx _ => indTypes.size - dIdx

/-- A successful worker run exposes the exact source-ordered generated type
headers.  Rule synthesis remains existentially internal, but cannot change
the `generatedRecursorType` stored in each emitted record. -/
theorem loop_infos_types
    {stats : InductiveStats} {indTypes : Array InductiveType}
    {elimLevel : Level} {k : Bool} {recInfos : Array RecInfo}
    {motives minors : Array Expr} {lctx : LocalContext}
    {lparams : List Name} {isUnsafe allowPrimitive : Bool}
    {dIdx : Nat} {env : Environment} {state : Nat} {context : Context}
    {tail : RecursorDeclarationTail allowPrimitive env k indTypes dIdx
      (getRecLevelParams elimLevel lparams) isUnsafe}
    (run : StateT.run'
      (loop stats indTypes elimLevel k recInfos motives minors lctx lparams
        isUnsafe allowPrimitive dIdx env) state context = .ok tail) :
    tail.infos.map (fun info => info.type) =
      generatedRecursorTypes stats indTypes recInfos motives minors lctx
        dIdx := by
  rw [loop.eq_1] at run
  by_cases hindex : dIdx < indTypes.size
  · rw [dif_pos hindex] at run
    dsimp only at run
    simp only [StateT.run', StateT.bind, ReaderT.bind, Bind.bind,
      Functor.map, Except.map] at run
    cases hrules : mkRecRules indTypes elimLevel stats dIdx motives minors state
        context with
    | error error =>
        rw [hrules] at run
        contradiction
    | ok rulesState =>
        rw [hrules] at run
        simp only [Except.bind] at run
        cases hcheck : checkNameCertificate env
            (mkRecName indTypes[dIdx].name) allowPrimitive with
        | error error =>
            rw [hcheck] at run
            contradiction
        | ok certificate =>
            rw [hcheck] at run
            dsimp [liftM, monadLift, MonadLift.monadLift, StateT.lift] at run
            simp only [Bind.bind, ReaderT.bind, Except.bind, Pure.pure,
              ReaderT.pure, StateT.pure, Except.pure] at run
            let recursor := generatedRecursorVal stats indTypes elimLevel k
              motives minors lctx lparams isUnsafe dIdx indTypes[dIdx]
                recInfos[dIdx]! rulesState.fst
            cases htailState :
                loop stats indTypes elimLevel k recInfos motives minors lctx
                  lparams isUnsafe allowPrimitive (dIdx + 1)
                    (env.add (.recInfo recursor)) rulesState.snd context with
            | error error =>
                rw [htailState] at run
                contradiction
            | ok nextTailState =>
                rw [htailState] at run
                simp only [Pure.pure, ReaderT.pure, StateT.pure,
                  Except.pure] at run
                have tail_eq := Except.ok.inj run
                subst tail
                have htail : StateT.run'
                    (loop stats indTypes elimLevel k recInfos motives minors
                      lctx lparams isUnsafe allowPrimitive (dIdx + 1)
                        (env.add (.recInfo recursor))) rulesState.snd context =
                      .ok nextTailState.fst := by
                  simp [StateT.run', htailState, Functor.map, Except.map]
                simp only [List.map_cons]
                rw [loop_infos_types htail]
                have types_eq :
                    generatedRecursorTypes stats indTypes recInfos motives
                        minors lctx dIdx =
                      generatedRecursorType stats motives minors lctx
                          recInfos[dIdx]! ::
                        generatedRecursorTypes stats indTypes recInfos motives
                          minors lctx (dIdx + 1) := by
                  rw [generatedRecursorTypes.eq_1, dif_pos hindex]
                rw [types_eq]
                rfl
  · rw [dif_neg hindex] at run
    simp only [Pure.pure, ReaderT.pure, StateT.pure, StateT.run',
      Functor.map, Except.map, Except.pure] at run
    have tail_eq := Except.ok.inj run
    subst tail
    have types_eq :
        generatedRecursorTypes stats indTypes recInfos motives minors lctx
            dIdx = [] := by
      rw [generatedRecursorTypes.eq_1, dif_neg hindex]
    exact types_eq.symm
termination_by indTypes.size - dIdx

/-- A successful singleton-family worker emits exactly the recursor assembled
from its first family and `RecInfo`.  Only the generated rule payload remains
existential, so consumers of the translation-visible header need not evaluate
`mkRecRules`. -/
theorem loop_singleton_infos_eq
    {stats : InductiveStats} {indTypes : Array InductiveType}
    {elimLevel : Level} {k : Bool} {recInfos : Array RecInfo}
    {motives minors : Array Expr} {lctx : LocalContext}
    {lparams : List Name} {isUnsafe allowPrimitive : Bool}
    {env : Environment} {state : Nat} {context : Context}
    {tail : RecursorDeclarationTail allowPrimitive env k indTypes 0
      (getRecLevelParams elimLevel lparams) isUnsafe}
    (hindex : 0 < indTypes.size)
    (size_eq : indTypes.size = 1)
    (run : StateT.run'
      (loop stats indTypes elimLevel k recInfos motives minors lctx lparams
        isUnsafe allowPrimitive 0 env) state context = .ok tail) :
    ∃ rules, tail.infos =
      [generatedRecursorVal stats indTypes elimLevel k motives minors lctx
        lparams isUnsafe 0 indTypes[0] recInfos[0]! rules] := by
  rw [loop.eq_1] at run
  rw [dif_pos hindex] at run
  dsimp only at run
  simp only [StateT.run', StateT.bind, ReaderT.bind, Bind.bind,
    Functor.map, Except.map] at run
  cases hrules : mkRecRules indTypes elimLevel stats 0 motives minors state
      context with
  | error error =>
      rw [hrules] at run
      contradiction
  | ok rulesState =>
      rw [hrules] at run
      simp only [Except.bind] at run
      cases hcheck : checkNameCertificate env
          (mkRecName indTypes[0].name) allowPrimitive with
      | error error =>
          rw [hcheck] at run
          contradiction
      | ok certificate =>
          rw [hcheck] at run
          dsimp [liftM, monadLift, MonadLift.monadLift, StateT.lift] at run
          rw [loop.eq_1] at run
          have hdone : ¬ 0 + 1 < indTypes.size := by omega
          rw [dif_neg hdone] at run
          simp only [Pure.pure, ReaderT.pure, StateT.pure, Except.pure] at run
          have tail_eq := Except.ok.inj run
          refine ⟨rulesState.fst, ?_⟩
          rw [← tail_eq]

end declareRecursors

/-- One family step retained by the first half of recursor-info synthesis.
It records the two normalization observations and the exact index context;
the major, motive, next context, and appended `RecInfo` are deterministic
projections of those observations. -/
structure RecInfoPhaseOneStep
    (stats : InductiveStats) (indTypes : Array InductiveType)
    (elimLevel : Level) (dIdx : Nat) (current : Context) where
  active : dIdx < indTypes.size
  normalizedType : Expr
  whnfRun :
    (liftM (TypeChecker.whnf (indTypes[dIdx]'active).type) : M Expr) current =
      .ok normalizedType
  indices : Array Expr
  indexContext : Context
  indicesRun :
    mkRecInfos.loopArgs1 stats normalizedType 0 #[]
      current.fuel.inductiveFuel
      (fun nextIndices nextContext => .ok (nextIndices, nextContext))
      current = .ok (indices, indexContext)

namespace RecInfoPhaseOneStep

/-- Expand the retained aggregate index run into its exact parameter/index
branch trace. -/
theorem indicesTrace
    (step : RecInfoPhaseOneStep stats indTypes elimLevel dIdx current) :
    Nonempty (mkRecInfos.LoopArgs1Trace stats step.normalizedType 0 #[]
      current.fuel.inductiveFuel current step.indices step.indexContext) :=
  mkRecInfos.LoopArgs1Trace.of_run step.indicesRun

def majorType
    (step : RecInfoPhaseOneStep stats indTypes elimLevel dIdx current) : Expr :=
  mkAppN (mkAppN stats.indConsts[dIdx]! stats.params) step.indices

def majorContext
    (step : RecInfoPhaseOneStep stats indTypes elimLevel dIdx current) :
    Context :=
  step.indexContext.pushLocalDecl `t .default
    (consumeTypeAnnotations step.majorType)

def major
    (step : RecInfoPhaseOneStep stats indTypes elimLevel dIdx current) : Expr :=
  step.indexContext.freshExpr

def motiveType
    (step : RecInfoPhaseOneStep stats indTypes elimLevel dIdx current) : Expr :=
  step.majorContext.lctx.mkForall step.indices <|
    step.majorContext.lctx.mkForall #[step.major] <| .sort elimLevel

def motiveName
    (step : RecInfoPhaseOneStep stats indTypes elimLevel dIdx current) : Name :=
  if indTypes.size > 1 then
    (`motive).appendIndexAfter (dIdx + 1)
  else
    `motive

def motive
    (step : RecInfoPhaseOneStep stats indTypes elimLevel dIdx current) : Expr :=
  step.majorContext.freshExpr

def motiveContext
    (step : RecInfoPhaseOneStep stats indTypes elimLevel dIdx current) :
    Context :=
  step.majorContext.pushLocalDecl step.motiveName .default
    (consumeTypeAnnotations step.motiveType)

def info
    (step : RecInfoPhaseOneStep stats indTypes elimLevel dIdx current) :
    RecInfo :=
  { motive := step.motive
    minors := #[]
    indices := step.indices
    major := step.major }

end RecInfoPhaseOneStep

/-- Complete source-ordered decomposition of a captured `loopInd1` run. -/
inductive RecInfoPhaseOneTrace
    (stats : InductiveStats) (indTypes : Array InductiveType)
    (elimLevel : Level) :
    Nat → Array RecInfo → Context → Array RecInfo → Context → Type where
  | done
      (finished : ¬ dIdx < indTypes.size) :
      RecInfoPhaseOneTrace stats indTypes elimLevel dIdx recInfos current
        recInfos current
  | next
      (step : RecInfoPhaseOneStep stats indTypes elimLevel dIdx current)
      (tail : RecInfoPhaseOneTrace stats indTypes elimLevel (dIdx + 1)
        (recInfos.push step.info) step.motiveContext finalInfos finalContext) :
      RecInfoPhaseOneTrace stats indTypes elimLevel dIdx recInfos current
        finalInfos finalContext

/-- Extract the complete phase-one decomposition from its retained capture
equation. -/
theorem RecInfoPhaseOneTrace.of_run
    {stats : InductiveStats} {indTypes : Array InductiveType}
    {elimLevel : Level} {dIdx : Nat} {recInfos finalInfos : Array RecInfo}
    {current finalContext : Context}
    (run : mkRecInfos.loopInd1 stats indTypes elimLevel dIdx recInfos
      (fun nextInfos nextContext => .ok (nextInfos, nextContext)) current =
        .ok (finalInfos, finalContext)) :
    Nonempty (RecInfoPhaseOneTrace stats indTypes elimLevel dIdx recInfos
      current finalInfos finalContext) := by
  rw [mkRecInfos.loopInd1.eq_1] at run
  split at run
  · simp only [readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
      ReaderT.bind, Bind.bind, Pure.pure, ReaderT.pure, Except.pure,
      Except.bind] at run
    cases whnfRun :
        (liftM (TypeChecker.whnf indTypes[dIdx].type) : M Expr) current with
    | error error =>
        simp only [whnfRun, Except.bind] at run
        contradiction
    | ok normalizedType =>
        simp only [whnfRun, Except.bind] at run
        rw [mkRecInfos.loopArgs1_eq_capture current] at run
        cases indicesRun :
            mkRecInfos.loopArgs1 stats normalizedType 0 #[]
              current.fuel.inductiveFuel
              (fun nextIndices nextContext =>
                .ok (nextIndices, nextContext)) current with
        | error error =>
            simp only [indicesRun, Except.bind] at run
            contradiction
        | ok indicesResult =>
            rcases indicesResult with ⟨indices, indexContext⟩
            simp only [indicesRun, Except.bind, withLocalDecl_apply,
              ReaderT.bind, Bind.bind, getLCtx_apply, Pure.pure,
              ReaderT.pure, Except.pure] at run
            let step : RecInfoPhaseOneStep stats indTypes elimLevel dIdx
                current := {
              active := by assumption
              normalizedType
              whnfRun
              indices
              indexContext
              indicesRun }
            have tailRun :
                mkRecInfos.loopInd1 stats indTypes elimLevel (dIdx + 1)
                  (recInfos.push step.info)
                  (fun nextInfos nextContext =>
                    .ok (nextInfos, nextContext)) step.motiveContext =
                    .ok (finalInfos, finalContext) := by
              simpa only [step, RecInfoPhaseOneStep.info,
                RecInfoPhaseOneStep.motive, RecInfoPhaseOneStep.motiveContext,
                RecInfoPhaseOneStep.motiveName,
                RecInfoPhaseOneStep.motiveType,
                RecInfoPhaseOneStep.major,
                RecInfoPhaseOneStep.majorContext,
                RecInfoPhaseOneStep.majorType] using run
            obtain ⟨tail⟩ := RecInfoPhaseOneTrace.of_run tailRun
            exact ⟨.next step tail⟩
  · have pairEq : (recInfos, current) = (finalInfos, finalContext) :=
      Except.ok.inj run
    cases pairEq
    exact ⟨.done (by assumption)⟩
termination_by indTypes.size - dIdx

/-- Information records appended by a retained phase-one trace, in the same
source order as the traversed kernel families. -/
def RecInfoPhaseOneTrace.addedInfos :
    RecInfoPhaseOneTrace stats indTypes elimLevel dIdx recInfos current
      finalInfos finalContext → List RecInfo
  | .done _ => []
  | .next step tail => step.info :: tail.addedInfos

/-- Phase one changes its incoming information array only by appending the
source-ordered records exposed by `addedInfos`. -/
theorem RecInfoPhaseOneTrace.finalInfos_toList
    (trace : RecInfoPhaseOneTrace stats indTypes elimLevel dIdx recInfos
      current finalInfos finalContext) :
    finalInfos.toList = recInfos.toList ++ trace.addedInfos := by
  induction trace with
  | done => simp [RecInfoPhaseOneTrace.addedInfos]
  | next step tail ih =>
      rw [ih, Array.toList_push, List.append_assoc]
      rfl

/-- Exact boundary between the two operational halves of `mkRecInfos`.

`loopInd1` creates every family index, major premise, and motive.  Only after
that whole array exists does `loopInd2` traverse constructors and add the
minor premises.  Retaining both equations gives verification a natural
family-wise induction boundary without rerunning recursor synthesis or
placing semantic data in the kernel producer. -/
structure RecInfoSynthesisTrace
    (stats : InductiveStats) (indTypes : Array InductiveType)
    (elimLevel : Level) (rootContext : Context)
    (recInfos : Array RecInfo) (synthesisContext : Context) where
  phase1Infos : Array RecInfo
  phase1Context : Context
  phase1Run :
    mkRecInfos.loopInd1 stats indTypes elimLevel 0 #[]
      (fun infos context => .ok (infos, context)) rootContext =
        .ok (phase1Infos, phase1Context)
  phase2Run :
    mkRecInfos.loopInd2 stats indTypes 0 phase1Infos
      (fun infos context => .ok (infos, context)) phase1Context =
        .ok (recInfos, synthesisContext)

/-- Source-ordered family decomposition of the retained first-phase run. -/
theorem RecInfoSynthesisTrace.phase1_trace
    (trace : RecInfoSynthesisTrace stats indTypes elimLevel rootContext
      recInfos synthesisContext) :
    Nonempty (RecInfoPhaseOneTrace stats indTypes elimLevel 0 #[] rootContext
      trace.phase1Infos trace.phase1Context) :=
  RecInfoPhaseOneTrace.of_run trace.phase1Run

/-- One constructor step retained by the second half of recursor-info
synthesis.  The two nested workers expose the exact constructor arguments,
recursive arguments, induction hypotheses, and callback contexts.  The
minor premise and updated `RecInfo` array are deterministic projections of
those observations. -/
structure RecInfoConstructorStep
    (stats : InductiveStats) (indTypeName : Name) (dIdx : Nat)
    (ctor : Constructor) (recInfos : Array RecInfo) (current : Context) where
  terminal : Expr
  constructorArgs : Array Expr
  recursiveArgs : Array Expr
  argumentContext : Context
  argumentsRun :
    mkRecInfos.loopCtorArgs stats ctor.type
      (fun nextTerminal nextConstructorArgs nextRecursiveArgs nextContext =>
        .ok (nextTerminal, nextConstructorArgs, nextRecursiveArgs,
          nextContext)) current =
      .ok (terminal, constructorArgs, recursiveArgs, argumentContext)
  hypotheses : Array Expr
  hypothesisContext : Context
  hypothesesRun :
    mkRecInfos.loopU stats recursiveArgs recInfos 0 #[]
      (fun nextHypotheses nextContext =>
        .ok (nextHypotheses, nextContext)) argumentContext =
      .ok (hypotheses, hypothesisContext)

namespace RecInfoConstructorStep

def targetIndex
    (step : RecInfoConstructorStep stats indTypeName dIdx ctor recInfos
      current) : Nat :=
  (getIIndices stats step.terminal).fst

def targetIndices
    (step : RecInfoConstructorStep stats indTypeName dIdx ctor recInfos
      current) : Array Expr :=
  (getIIndices stats step.terminal).snd

def constructorApplication
    (step : RecInfoConstructorStep stats indTypeName dIdx ctor recInfos
      current) : Expr :=
  mkAppN (mkAppN (.const ctor.name stats.levels) stats.params)
    step.constructorArgs

def motiveApplication
    (step : RecInfoConstructorStep stats indTypeName dIdx ctor recInfos
      current) : Expr :=
  .app (mkAppN recInfos[step.targetIndex]!.motive step.targetIndices)
    step.constructorApplication

def minorType
    (step : RecInfoConstructorStep stats indTypeName dIdx ctor recInfos
      current) : Expr :=
  step.hypothesisContext.lctx.mkForall step.constructorArgs <|
    step.hypothesisContext.lctx.mkForall step.hypotheses <|
      step.motiveApplication

def minorName
    (step : RecInfoConstructorStep stats indTypeName dIdx ctor recInfos
      current) : Name :=
  ctor.name.replacePrefix indTypeName .anonymous

def minor
    (step : RecInfoConstructorStep stats indTypeName dIdx ctor recInfos
      current) : Expr :=
  step.hypothesisContext.freshExpr

def minorContext
    (step : RecInfoConstructorStep stats indTypeName dIdx ctor recInfos
      current) : Context :=
  step.hypothesisContext.pushLocalDecl step.minorName .default
    (consumeTypeAnnotations step.minorType)

def nextInfos
    (step : RecInfoConstructorStep stats indTypeName dIdx ctor recInfos
      current) : Array RecInfo :=
  recInfos.modify dIdx fun info =>
    { info with minors := info.minors.push step.minor }

/-- Expand the retained aggregate constructor-argument run into its exact
parameter/field branch trace. -/
theorem argumentsTrace
    (step : RecInfoConstructorStep stats indTypeName dIdx ctor recInfos
      current) :
    Nonempty (mkRecInfos.LoopCtorArgsTrace stats ctor.type 0 #[] #[]
      current.fuel.inductiveFuel current step.terminal
      step.constructorArgs step.recursiveArgs step.argumentContext) :=
  mkRecInfos.LoopCtorArgsTrace.of_capture step.argumentsRun

/-- Expand the retained aggregate hypothesis run into its exact
per-recursive-argument trace. -/
theorem hypothesesTrace
    (step : RecInfoConstructorStep stats indTypeName dIdx ctor recInfos
      current) :
    Nonempty (mkRecInfos.LoopUTrace stats step.recursiveArgs recInfos 0 #[]
      step.argumentContext step.hypotheses step.hypothesisContext) :=
  mkRecInfos.LoopUTrace.of_run step.hypothesesRun

private theorem map_modify_of_project_eq
    (values : Array α) (index : Nat) (update : α → α)
    (project : α → β) (preserved : ∀ value,
      project (update value) = project value) :
    (values.modify index update).map project = values.map project := by
  rw [← Array.toList_inj]
  simp only [Array.toList_map, Array.toList_modify]
  apply List.ext_getElem?
  intro current
  simp only [List.getElem?_map, List.getElem?_modify]
  by_cases selected : index = current
  · simp only [selected, if_true]
    cases valueAt : values.toList[current]? with
    | none => rfl
    | some value =>
        change some (project (update value)) = some (project value)
        exact congrArg some (preserved value)
  · simp only [selected, if_false]
    cases values.toList[current]? <;> rfl

/-- Adding a constructor minor leaves the family motive inventory unchanged.
This is the field-level invariant used to carry the phase-one motive
telescope through the complete constructor traversal. -/
theorem nextInfos_map_motive
    (step : RecInfoConstructorStep stats indTypeName dIdx ctor recInfos
      current) :
    step.nextInfos.map (·.motive) = recInfos.map (·.motive) := by
  apply map_modify_of_project_eq
  intro info
  rfl

/-- Constructor traversal also preserves every family index inventory
selected by phase one. -/
theorem nextInfos_map_indices
    (step : RecInfoConstructorStep stats indTypeName dIdx ctor recInfos
      current) :
    step.nextInfos.map (·.indices) = recInfos.map (·.indices) := by
  apply map_modify_of_project_eq
  intro info
  rfl

/-- Constructor traversal also preserves every family major premise selected
by phase one. -/
theorem nextInfos_map_major
    (step : RecInfoConstructorStep stats indTypeName dIdx ctor recInfos
      current) :
    step.nextInfos.map (·.major) = recInfos.map (·.major) := by
  apply map_modify_of_project_eq
  intro info
  rfl

end RecInfoConstructorStep

/-- Complete source-ordered decomposition of one captured constructor-list
worker. -/
inductive RecInfoConstructorTrace
    (stats : InductiveStats) (indTypeName : Name) (dIdx : Nat) :
    List Constructor → Array RecInfo → Context →
      Array RecInfo → Context → Type where
  | done :
      RecInfoConstructorTrace stats indTypeName dIdx [] recInfos current
        recInfos current
  | next
      (step : RecInfoConstructorStep stats indTypeName dIdx ctor recInfos
        current)
      (tail : RecInfoConstructorTrace stats indTypeName dIdx ctors
        step.nextInfos step.minorContext finalInfos finalContext) :
      RecInfoConstructorTrace stats indTypeName dIdx (ctor :: ctors)
        recInfos current finalInfos finalContext

/-- Extract a constructor-list decomposition from its continuation-free
capture equation. -/
theorem RecInfoConstructorTrace.of_run
    {stats : InductiveStats} {indTypeName : Name} {dIdx : Nat}
    {ctors : List Constructor} {recInfos finalInfos : Array RecInfo}
    {current finalContext : Context}
    (run : mkRecInfos.loopCtors stats indTypeName dIdx recInfos ctors
      (fun nextInfos nextContext => .ok (nextInfos, nextContext)) current =
        .ok (finalInfos, finalContext)) :
    Nonempty (RecInfoConstructorTrace stats indTypeName dIdx ctors recInfos
      current finalInfos finalContext) := by
  induction ctors generalizing recInfos current with
  | nil =>
      have pairEq : (recInfos, current) = (finalInfos, finalContext) :=
        Except.ok.inj run
      cases pairEq
      exact ⟨.done⟩
  | cons ctor ctors ih =>
      rw [mkRecInfos.loopCtors] at run
      rw [mkRecInfos.loopCtorArgs_eq_capture current] at run
      cases argumentsRun :
          mkRecInfos.loopCtorArgs stats ctor.type
            (fun nextTerminal nextConstructorArgs nextRecursiveArgs
                nextContext =>
              .ok (nextTerminal, nextConstructorArgs, nextRecursiveArgs,
                nextContext)) current with
      | error error =>
          simp only [argumentsRun, Except.bind] at run
          contradiction
      | ok argumentsResult =>
          rcases argumentsResult with
            ⟨terminal, constructorArgs, recursiveArgs, argumentContext⟩
          simp only [argumentsRun, Except.bind] at run
          rw [mkRecInfos.loopU_eq_capture argumentContext] at run
          cases hypothesesRun :
              mkRecInfos.loopU stats recursiveArgs recInfos 0 #[]
                (fun nextHypotheses nextContext =>
                  .ok (nextHypotheses, nextContext)) argumentContext with
          | error error =>
              simp only [hypothesesRun, Except.bind] at run
              contradiction
          | ok hypothesesResult =>
              rcases hypothesesResult with ⟨hypotheses, hypothesisContext⟩
              simp only [hypothesesRun, Except.bind, getLCtx_apply,
                ReaderT.bind, Bind.bind, Pure.pure, ReaderT.pure, Except.pure,
                withLocalDecl_apply] at run
              let step : RecInfoConstructorStep stats indTypeName dIdx ctor
                  recInfos current := {
                terminal
                constructorArgs
                recursiveArgs
                argumentContext
                argumentsRun
                hypotheses
                hypothesisContext
                hypothesesRun }
              have tailRun :
                  mkRecInfos.loopCtors stats indTypeName dIdx step.nextInfos
                    ctors
                    (fun nextInfos nextContext =>
                      .ok (nextInfos, nextContext)) step.minorContext =
                    .ok (finalInfos, finalContext) := by
                simpa only [step, RecInfoConstructorStep.nextInfos,
                  RecInfoConstructorStep.minor,
                  RecInfoConstructorStep.minorContext,
                  RecInfoConstructorStep.minorName,
                  RecInfoConstructorStep.minorType,
                  RecInfoConstructorStep.motiveApplication,
                  RecInfoConstructorStep.constructorApplication,
                  RecInfoConstructorStep.targetIndices,
                  RecInfoConstructorStep.targetIndex] using run
              obtain ⟨tail⟩ := ih tailRun
              exact ⟨.next step tail⟩

/-- Traversing all constructors of one family changes only that family's
minor array; the motive selected during phase one is preserved pointwise. -/
theorem RecInfoConstructorTrace.map_motive_eq
    (trace : RecInfoConstructorTrace stats indTypeName dIdx ctors recInfos
      current finalInfos finalContext) :
    finalInfos.map (·.motive) = recInfos.map (·.motive) := by
  induction trace with
  | done => rfl
  | next step tail ih => exact ih.trans step.nextInfos_map_motive

/-- The family index arrays selected during phase one are stable throughout
one family's constructor traversal. -/
theorem RecInfoConstructorTrace.map_indices_eq
    (trace : RecInfoConstructorTrace stats indTypeName dIdx ctors recInfos
      current finalInfos finalContext) :
    finalInfos.map (·.indices) = recInfos.map (·.indices) := by
  induction trace with
  | done => rfl
  | next step tail ih => exact ih.trans step.nextInfos_map_indices

/-- The family major premises selected during phase one are stable throughout
one family's constructor traversal. -/
theorem RecInfoConstructorTrace.map_major_eq
    (trace : RecInfoConstructorTrace stats indTypeName dIdx ctors recInfos
      current finalInfos finalContext) :
    finalInfos.map (·.major) = recInfos.map (·.major) := by
  induction trace with
  | done => rfl
  | next step tail ih => exact ih.trans step.nextInfos_map_major

/-- One family step retained by the second half of recursor-info synthesis. -/
structure RecInfoPhaseTwoStep
    (stats : InductiveStats) (indTypes : Array InductiveType)
    (dIdx : Nat) (recInfos : Array RecInfo) (current : Context) where
  active : dIdx < indTypes.size
  finalInfos : Array RecInfo
  finalContext : Context
  constructors : RecInfoConstructorTrace stats
    (indTypes[dIdx]'active).name dIdx (indTypes[dIdx]'active).ctors recInfos
      current finalInfos finalContext

/-- Complete source-ordered decomposition of a captured `loopInd2` run. -/
inductive RecInfoPhaseTwoTrace
    (stats : InductiveStats) (indTypes : Array InductiveType) :
    Nat → Array RecInfo → Context → Array RecInfo → Context → Type where
  | done
      (finished : ¬ dIdx < indTypes.size) :
      RecInfoPhaseTwoTrace stats indTypes dIdx recInfos current recInfos
        current
  | next
      (step : RecInfoPhaseTwoStep stats indTypes dIdx recInfos current)
      (tail : RecInfoPhaseTwoTrace stats indTypes (dIdx + 1)
        step.finalInfos step.finalContext finalInfos finalContext) :
      RecInfoPhaseTwoTrace stats indTypes dIdx recInfos current finalInfos
        finalContext

/-- Extract the complete phase-two decomposition from its retained capture
equation. -/
theorem RecInfoPhaseTwoTrace.of_run
    {stats : InductiveStats} {indTypes : Array InductiveType}
    {dIdx : Nat} {recInfos finalInfos : Array RecInfo}
    {current finalContext : Context}
    (run : mkRecInfos.loopInd2 stats indTypes dIdx recInfos
      (fun nextInfos nextContext => .ok (nextInfos, nextContext)) current =
        .ok (finalInfos, finalContext)) :
    Nonempty (RecInfoPhaseTwoTrace stats indTypes dIdx recInfos current
      finalInfos finalContext) := by
  rw [mkRecInfos.loopInd2.eq_1] at run
  split at run
  · rw [mkRecInfos.loopCtors_eq_capture current] at run
    cases constructorsRun :
        mkRecInfos.loopCtors stats indTypes[dIdx].name dIdx recInfos
          indTypes[dIdx].ctors
          (fun nextInfos nextContext => .ok (nextInfos, nextContext))
          current with
    | error error =>
        simp only [constructorsRun, Except.bind] at run
        contradiction
    | ok constructorsResult =>
        rcases constructorsResult with ⟨nextInfos, nextContext⟩
        simp only [constructorsRun, Except.bind] at run
        obtain ⟨constructors⟩ := RecInfoConstructorTrace.of_run
          constructorsRun
        obtain ⟨tail⟩ := RecInfoPhaseTwoTrace.of_run run
        let step : RecInfoPhaseTwoStep stats indTypes dIdx recInfos current := {
          active := by assumption
          finalInfos := nextInfos
          finalContext := nextContext
          constructors := by simpa using constructors }
        exact ⟨.next step (by simpa only [step] using tail)⟩
  · have pairEq : (recInfos, current) = (finalInfos, finalContext) :=
      Except.ok.inj run
    cases pairEq
    exact ⟨.done (by assumption)⟩
termination_by indTypes.size - dIdx

/-- The complete second phase preserves the source-ordered motive array.
Only the `minors` field of each `RecInfo` is extended. -/
theorem RecInfoPhaseTwoTrace.map_motive_eq
    (trace : RecInfoPhaseTwoTrace stats indTypes dIdx recInfos current
      finalInfos finalContext) :
    finalInfos.map (·.motive) = recInfos.map (·.motive) := by
  induction trace with
  | done => rfl
  | next step tail ih => exact ih.trans step.constructors.map_motive_eq

/-- The complete second phase preserves the family index arrays. -/
theorem RecInfoPhaseTwoTrace.map_indices_eq
    (trace : RecInfoPhaseTwoTrace stats indTypes dIdx recInfos current
      finalInfos finalContext) :
    finalInfos.map (·.indices) = recInfos.map (·.indices) := by
  induction trace with
  | done => rfl
  | next step tail ih => exact ih.trans step.constructors.map_indices_eq

/-- The complete second phase preserves the family major premises. -/
theorem RecInfoPhaseTwoTrace.map_major_eq
    (trace : RecInfoPhaseTwoTrace stats indTypes dIdx recInfos current
      finalInfos finalContext) :
    finalInfos.map (·.major) = recInfos.map (·.major) := by
  induction trace with
  | done => rfl
  | next step tail ih => exact ih.trans step.constructors.map_major_eq

/-- Source-ordered family/constructor decomposition of the retained second
phase. -/
theorem RecInfoSynthesisTrace.phase2_trace
    (trace : RecInfoSynthesisTrace stats indTypes elimLevel rootContext
      recInfos synthesisContext) :
    Nonempty (RecInfoPhaseTwoTrace stats indTypes 0 trace.phase1Infos
      trace.phase1Context recInfos synthesisContext) :=
  RecInfoPhaseTwoTrace.of_run trace.phase2Run

/-- The motive array used to assemble every emitted recursor is exactly the
array allocated by the retained phase-one family traversal. -/
theorem RecInfoSynthesisTrace.motives_eq_phase1
    (trace : RecInfoSynthesisTrace stats indTypes elimLevel rootContext
      recInfos synthesisContext) :
    recInfos.map (·.motive) = trace.phase1Infos.map (·.motive) := by
  obtain ⟨phase2⟩ := trace.phase2_trace
  exact phase2.map_motive_eq

/-- The final recursor inventory uses exactly the phase-one family indices. -/
theorem RecInfoSynthesisTrace.indices_eq_phase1
    (trace : RecInfoSynthesisTrace stats indTypes elimLevel rootContext
      recInfos synthesisContext) :
    recInfos.map (·.indices) = trace.phase1Infos.map (·.indices) := by
  obtain ⟨phase2⟩ := trace.phase2_trace
  exact phase2.map_indices_eq

/-- The final recursor inventory uses exactly the phase-one major premises. -/
theorem RecInfoSynthesisTrace.majors_eq_phase1
    (trace : RecInfoSynthesisTrace stats indTypes elimLevel rootContext
      recInfos synthesisContext) :
    recInfos.map (·.major) = trace.phase1Infos.map (·.major) := by
  obtain ⟨phase2⟩ := trace.phase2_trace
  exact phase2.map_major_eq

/-- One source-ordered phase-one trace simultaneously owns the motive,
index, and major arrays consumed by every final generated recursor.  This is
the operational handoff used by the family-wise semantic telescope loop. -/
theorem RecInfoSynthesisTrace.phase1_inventory
    (trace : RecInfoSynthesisTrace stats indTypes elimLevel rootContext
      recInfos synthesisContext) :
    ∃ phase1 : RecInfoPhaseOneTrace stats indTypes elimLevel 0 #[] rootContext
        trace.phase1Infos trace.phase1Context,
      (recInfos.map (·.motive)).toList =
          phase1.addedInfos.map (·.motive) ∧
        (recInfos.map (·.indices)).toList =
          phase1.addedInfos.map (·.indices) ∧
        (recInfos.map (·.major)).toList =
          phase1.addedInfos.map (·.major) := by
  obtain ⟨phase1⟩ := trace.phase1_trace
  have infosEq : trace.phase1Infos.toList = phase1.addedInfos := by
    simpa using phase1.finalInfos_toList
  refine ⟨phase1, ?_, ?_, ?_⟩
  · calc
      (recInfos.map (·.motive)).toList =
          (trace.phase1Infos.map (·.motive)).toList :=
        congrArg Array.toList trace.motives_eq_phase1
      _ = trace.phase1Infos.toList.map (·.motive) := Array.toList_map
      _ = phase1.addedInfos.map (·.motive) := congrArg _ infosEq
  · calc
      (recInfos.map (·.indices)).toList =
          (trace.phase1Infos.map (·.indices)).toList :=
        congrArg Array.toList trace.indices_eq_phase1
      _ = trace.phase1Infos.toList.map (·.indices) := Array.toList_map
      _ = phase1.addedInfos.map (·.indices) := congrArg _ infosEq
  · calc
      (recInfos.map (·.major)).toList =
          (trace.phase1Infos.map (·.major)).toList :=
        congrArg Array.toList trace.majors_eq_phase1
      _ = trace.phase1Infos.toList.map (·.major) := Array.toList_map
      _ = phase1.addedInfos.map (·.major) := congrArg _ infosEq

/-- The phase-one callback context is reached solely by local-declaration
pushes from the recursor root. -/
theorem RecInfoSynthesisTrace.phase1_localExtension
    (trace : RecInfoSynthesisTrace stats indTypes elimLevel rootContext
      recInfos synthesisContext) :
    rootContext.LocalExtension trace.phase1Context := by
  exact mkRecInfos.loopInd1_localExtension .refl trace.phase1Run
    fun nextInfos nextContext extension callbackRun => by
      have pairEq : (nextInfos, nextContext) =
          (trace.phase1Infos, trace.phase1Context) :=
        Except.ok.inj callbackRun
      have contextEq : nextContext = trace.phase1Context :=
        congrArg Prod.snd pairEq
      exact contextEq ▸ extension

/-- Composing both synthesis phases shows that the final context used to
assemble generated recursor types still contains the root local context as an
exact push-only prefix. -/
theorem RecInfoSynthesisTrace.synthesis_localExtension
    (trace : RecInfoSynthesisTrace stats indTypes elimLevel rootContext
      recInfos synthesisContext) :
    rootContext.LocalExtension synthesisContext := by
  exact mkRecInfos.loopInd2_localExtension trace.phase1_localExtension
    trace.phase2Run fun nextInfos nextContext extension callbackRun => by
      have pairEq : (nextInfos, nextContext) = (recInfos, synthesisContext) :=
        Except.ok.inj callbackRun
      have contextEq : nextContext = synthesisContext :=
        congrArg Prod.snd pairEq
      exact contextEq ▸ extension

/-- Producer-owned provenance for the successful `mkRecInfos` callback and
the exact recursor declaration worker it launches.  Retaining the callback
context makes the generated motive/minor telescope available to verification
without rerunning synthesis or inspecting a parallel executable checker. -/
structure RecursorDeclarationSynthesis
    (stats : InductiveStats) (indTypes : Array InductiveType)
    (elimLevel : Level) (k : Bool) (rootContext : Context) where
  recInfos : Array RecInfo
  synthesisContext : Context
  synthesisTrace : RecInfoSynthesisTrace stats indTypes elimLevel rootContext
    recInfos synthesisContext
  tail : RecursorDeclarationTail rootContext.allowPrimitive rootContext.env k
    indTypes 0 (getRecLevelParams elimLevel rootContext.lparams)
      (rootContext.safety != .safe)
  run : StateT.run'
    (declareRecursors.loop stats indTypes elimLevel k recInfos
      (recInfos.map (·.motive)) (recInfos.flatMap (·.minors))
      synthesisContext.lctx rootContext.lparams
      (rootContext.safety != .safe) rootContext.allowPrimitive 0
      rootContext.env) 0 synthesisContext = .ok tail

/-- Transparent synthesis/declaration worker retaining the exact callback
context and `RecInfo` array that determine every generated recursor type. -/
def declareRecursorsDetailedAt (stats : InductiveStats)
    (indTypes : Array InductiveType) (elimLevel : Level) (k : Bool)
    (context : Context) :
    Except Exception
      (RecursorDeclarationSynthesis stats indTypes elimLevel k context) :=
  match hphase1 : mkRecInfos.loopInd1 stats indTypes elimLevel 0 #[]
      (fun recInfos phase1Context => .ok (recInfos, phase1Context))
      context with
  | .error error => .error error
  | .ok (phase1Infos, phase1Context) =>
      match hphase2 : mkRecInfos.loopInd2 stats indTypes 0 phase1Infos
          (fun recInfos synthesisContext => .ok (recInfos, synthesisContext))
          phase1Context with
      | .error error => .error error
      | .ok (recInfos, synthesisContext) =>
          match hloop : StateT.run'
              (declareRecursors.loop stats indTypes elimLevel k recInfos
                (recInfos.map (·.motive)) (recInfos.flatMap (·.minors))
                synthesisContext.lctx context.lparams
                (context.safety != .safe) context.allowPrimitive 0 context.env)
              0 synthesisContext with
          | .error error => .error error
          | .ok tail => .ok {
              recInfos
              synthesisContext
              synthesisTrace := {
                phase1Infos
                phase1Context
                phase1Run := hphase1
                phase2Run := hphase2 }
              tail
              run := hloop }

/-- Recover the exact successful `mkRecInfos` capture from a successful
detailed declaration worker.  The equation is derived at the consumer
boundary instead of being stored dependently in the result, keeping concrete
replay reductions proof-irrelevant. -/
theorem RecursorDeclarationSynthesis.synthesisRun
    (synthesis : RecursorDeclarationSynthesis stats indTypes elimLevel k
      context)
    (run : declareRecursorsDetailedAt stats indTypes elimLevel k context =
      .ok synthesis) :
    mkRecInfos stats indTypes elimLevel
      (fun recInfos synthesisContext => .ok (recInfos, synthesisContext))
      context = .ok (synthesis.recInfos, synthesis.synthesisContext) := by
  unfold mkRecInfos
  rw [synthesis.synthesisTrace.phase1Run]
  exact synthesis.synthesisTrace.phase2Run

/-- Transparent recursor synthesis/declaration worker at an explicit reader
context.  Exposing this worker lets verification recover generated metadata
from a successful `declareRecursors` equation while keeping the public result
record focused on replay data. -/
def declareRecursorsAt (stats : InductiveStats)
    (indTypes : Array InductiveType) (elimLevel : Level) (k : Bool)
    (context : Context) :
    Except Exception
      (RecursorDeclarationTail context.allowPrimitive context.env k
        indTypes 0 (getRecLevelParams elimLevel context.lparams)
        (context.safety != .safe)) :=
  (declareRecursorsDetailedAt stats indTypes elimLevel k context).map
    (·.tail)

/-- Run the complete ordinary recursor synthesis/declaration phase while
retaining the generated metadata inventory. -/
def declareRecursors (stats : InductiveStats)
    (indTypes : Array InductiveType) (elimLevel : Level) (k : Bool) :
    M RecursorDeclarationResult := fun context => do
  let result ← declareRecursorsAt stats indTypes elimLevel k context
  pure {
    initialEnv := context.env
    allowPrimitive := context.allowPrimitive
    kTarget := k
    sourceTypes := indTypes
    levelParams := getRecLevelParams elimLevel context.lparams
    isUnsafe := context.safety != .safe
    infos := result.infos
    infos_names := by simpa using result.infos_names
    infos_kTarget := result.infos_kTarget
    infos_levelParams := result.infos_levelParams
    infos_isUnsafe := result.infos_isUnsafe
    info_of_source_index := by
      intro i upper
      exact result.info_of_source_index i (Nat.zero_le i) upper
    env := result.env
    trace := result.trace }

/-- Recover the exact successful `mkRecInfos` callback owned by a public
recursor result.  The equality on `infos` is intentionally retained even
though the detailed worker is definitionally projected by
`declareRecursorsAt`; it is the stable transport boundary for verification. -/
theorem declareRecursors_synthesis
    (run : declareRecursors stats indTypes elimLevel k context = .ok result) :
    ∃ synthesis : RecursorDeclarationSynthesis stats indTypes elimLevel k
        context,
      declareRecursorsDetailedAt stats indTypes elimLevel k context =
          .ok synthesis ∧
        result.infos = synthesis.tail.infos := by
  unfold declareRecursors at run
  unfold declareRecursorsAt at run
  cases hsynthesis :
      declareRecursorsDetailedAt stats indTypes elimLevel k context with
  | error error =>
      simp_all [Functor.map, Except.map, Bind.bind, Except.bind]
  | ok synthesis =>
      simp only [hsynthesis, Functor.map, Except.map, Bind.bind, Except.bind,
        Pure.pure, Except.pure] at run
      cases run
      exact ⟨synthesis, rfl, rfl⟩

/-- Every public recursor header is exactly the source-ordered type assembled
from the retained `mkRecInfos` callback. -/
theorem declareRecursors_infos_types
    (run : declareRecursors stats indTypes elimLevel k context = .ok result) :
    ∃ synthesis : RecursorDeclarationSynthesis stats indTypes elimLevel k
        context,
      declareRecursorsDetailedAt stats indTypes elimLevel k context =
          .ok synthesis ∧
        result.infos.map (fun info => info.type) =
          declareRecursors.generatedRecursorTypes stats indTypes
            synthesis.recInfos (synthesis.recInfos.map (·.motive))
            (synthesis.recInfos.flatMap (·.minors))
            synthesis.synthesisContext.lctx 0 := by
  obtain ⟨synthesis, synthesisRun, infos_eq⟩ :=
    declareRecursors_synthesis run
  refine ⟨synthesis, synthesisRun, ?_⟩
  rw [infos_eq]
  exact declareRecursors.loop_infos_types synthesis.run

/-- A successful recursor phase records the exact input environment and name-
checking mode of its reader context. -/
theorem declareRecursors_input_eq
    (run : declareRecursors stats indTypes elimLevel k context = .ok result) :
    result.initialEnv = context.env ∧
      result.allowPrimitive = context.allowPrimitive := by
  unfold declareRecursors at run
  cases hrun : declareRecursorsAt stats indTypes elimLevel k context with
  | error error => simp_all [Bind.bind, Except.bind]
  | ok tail =>
      simp only [hrun, Bind.bind, Except.bind, Pure.pure, Except.pure] at run
      cases run
      exact ⟨rfl, rfl⟩

/-- A successful recursor phase retains the exact K-like flag supplied to
the producer. -/
theorem declareRecursors_kTarget_eq
    (run : declareRecursors stats indTypes elimLevel k context = .ok result) :
    result.kTarget = k := by
  unfold declareRecursors at run
  cases hrun : declareRecursorsAt stats indTypes elimLevel k context with
  | error error => simp_all [Bind.bind, Except.bind]
  | ok tail =>
      simp only [hrun, Bind.bind, Except.bind, Pure.pure, Except.pure] at run
      cases run
      rfl

/-- A successful recursor phase retains the exact source-family array supplied
to the producer. -/
theorem declareRecursors_sourceTypes_eq
    (run : declareRecursors stats indTypes elimLevel k context = .ok result) :
    result.sourceTypes = indTypes := by
  unfold declareRecursors at run
  cases hrun : declareRecursorsAt stats indTypes elimLevel k context with
  | error error => simp_all [Bind.bind, Except.bind]
  | ok tail =>
      simp only [hrun, Bind.bind, Except.bind, Pure.pure, Except.pure] at run
      cases run
      rfl

/-- A successful recursor phase records the exact universe-parameter list
used by every generated recursor header. -/
theorem declareRecursors_levelParams_eq
    (run : declareRecursors stats indTypes elimLevel k context = .ok result) :
    result.levelParams = getRecLevelParams elimLevel context.lparams := by
  unfold declareRecursors at run
  cases hrun : declareRecursorsAt stats indTypes elimLevel k context with
  | error error => simp_all [Bind.bind, Except.bind]
  | ok tail =>
      simp only [hrun, Bind.bind, Except.bind, Pure.pure, Except.pure] at run
      cases run
      rfl

/-- A successful recursor phase records the reader-context safety decision
used by every generated recursor header. -/
theorem declareRecursors_isUnsafe_eq
    (run : declareRecursors stats indTypes elimLevel k context = .ok result) :
    result.isUnsafe = (context.safety != .safe) := by
  unfold declareRecursors at run
  cases hrun : declareRecursorsAt stats indTypes elimLevel k context with
  | error error => simp_all [Bind.bind, Except.bind]
  | ok tail =>
      simp only [hrun, Bind.bind, Except.bind, Pure.pure, Except.pure] at run
      cases run
      rfl

/-- A successful recursor phase emits exactly one canonical recursor name per
source family, in source order. -/
theorem declareRecursors_infos_names
    (run : declareRecursors stats indTypes elimLevel k context = .ok result) :
    result.infos.map (·.name) =
      indTypes.toList.map (fun indType => mkRecName indType.name) := by
  rw [← declareRecursors_sourceTypes_eq run]
  exact result.infos_names

/-- Every source-family index contributes a generated recursor with the
kernel's canonical recursor name. -/
theorem declareRecursors_info_of_index
    (run : declareRecursors stats indTypes elimLevel k context = .ok result)
    {i : Nat} (upper : i < indTypes.size) :
    ∃ info ∈ result.infos,
      info.name = mkRecName indTypes[i].name := by
  have sourceTypesEq := declareRecursors_sourceTypes_eq run
  have resultUpper : i < result.sourceTypes.size := by
    simpa only [sourceTypesEq] using upper
  obtain ⟨info, member, nameEq⟩ :=
    result.info_of_source_index i resultUpper
  refine ⟨info, member, ?_⟩
  simpa only [sourceTypesEq] using nameEq

/-- Every source family contributes a generated recursor with the kernel's
canonical recursor name. -/
theorem declareRecursors_info_of_family
    (run : declareRecursors stats indTypes elimLevel k context = .ok result)
    {indType : InductiveType} (member : indType ∈ indTypes.toList) :
    ∃ info ∈ result.infos,
      info.name = mkRecName indType.name := by
  obtain ⟨i, upper, getEq⟩ := List.mem_iff_getElem.mp member
  have arrayUpper : i < indTypes.size := by simpa using upper
  obtain ⟨info, infoMember, nameEq⟩ :=
    declareRecursors_info_of_index run arrayUpper
  refine ⟨info, infoMember, ?_⟩
  have arrayGetEq : indTypes[i] = indType := by simpa using getEq
  simpa only [arrayGetEq] using nameEq

/-- Every recursor emitted by one successful phase carries the exact K-like
flag computed for that phase. -/
theorem declareRecursors_infos_kTarget
    (run : declareRecursors stats indTypes elimLevel k context = .ok result)
    {info : RecursorVal} (member : info ∈ result.infos) :
    info.k = k := by
  rw [← declareRecursors_kTarget_eq run]
  exact result.infos_kTarget info member

/-- Every emitted recursor uses the exact universe-parameter list computed
for the successful phase. -/
theorem declareRecursors_infos_levelParams
    (run : declareRecursors stats indTypes elimLevel k context = .ok result)
    {info : RecursorVal} (member : info ∈ result.infos) :
    info.levelParams = getRecLevelParams elimLevel context.lparams := by
  rw [← declareRecursors_levelParams_eq run]
  exact result.infos_levelParams info member

/-- Every emitted recursor carries the exact safety bit of the reader
context used by the successful phase. -/
theorem declareRecursors_infos_isUnsafe
    (run : declareRecursors stats indTypes elimLevel k context = .ok result)
    {info : RecursorVal} (member : info ∈ result.infos) :
    info.isUnsafe = (context.safety != .safe) := by
  rw [← declareRecursors_isUnsafe_eq run]
  exact result.infos_isUnsafe info member

/-- Repackage the exact detailed worker result as the public recursor
declaration result without rerunning synthesis. -/
def RecursorDeclarationSynthesis.toDeclarationResult
    (synthesis : RecursorDeclarationSynthesis stats indTypes elimLevel k
      context) : RecursorDeclarationResult := {
  initialEnv := context.env
  allowPrimitive := context.allowPrimitive
  kTarget := k
  sourceTypes := indTypes
  levelParams := getRecLevelParams elimLevel context.lparams
  isUnsafe := context.safety != .safe
  infos := synthesis.tail.infos
  infos_names := by simpa using synthesis.tail.infos_names
  infos_kTarget := synthesis.tail.infos_kTarget
  infos_levelParams := synthesis.tail.infos_levelParams
  infos_isUnsafe := synthesis.tail.infos_isUnsafe
  info_of_source_index := by
    intro i upper
    exact synthesis.tail.info_of_source_index i (Nat.zero_le i) upper
  env := synthesis.tail.env
  trace := synthesis.tail.trace }

/-- The public declaration equation projected from one successful detailed
worker.  This is a proof-only projection of the same run, not a second
execution of recursor synthesis. -/
theorem RecursorDeclarationSynthesis.declareRecursorsRun
    (synthesis : RecursorDeclarationSynthesis stats indTypes elimLevel k
      context)
    (run : declareRecursorsDetailedAt stats indTypes elimLevel k context =
      .ok synthesis) :
    declareRecursors stats indTypes elimLevel k context =
      .ok synthesis.toDeclarationResult := by
  unfold declareRecursors declareRecursorsAt
  rw [run]
  rfl

/-- The recursor prefix applied before a constructor in the generated-rule
check: parameters, all motives, and all minor premises have already been
supplied. -/
def generatedRecursorCheckPrefix (stats : InductiveStats)
    (elimLevel : Level) (motives minors : Array Expr)
    (indType : InductiveType) : Expr :=
  mkAppN (mkAppN (mkAppN
    (.const (mkRecName indType.name)
      (getRecLevels elimLevel stats.levels)) stats.params) motives) minors

/-- The constructor application used as the major premise in one generated
recursor type-preservation check. -/
def generatedRecursorConstructorApplication (stats : InductiveStats)
    (constructor : Constructor) (fields : Array Expr) : Expr :=
  mkAppN (mkAppN (.const constructor.name stats.levels) stats.params) fields

/-- Exact left-hand side inferred, reduced, and inferred again by Lean
4.33.1's generated-rule guard. -/
def generatedRecursorRuleLhs (stats : InductiveStats)
    (elimLevel : Level) (motives minors : Array Expr)
    (indType : InductiveType) (constructor : Constructor)
    (terminal : Expr) (fields : Array Expr) : Expr :=
  let indices := (getIIndices stats terminal).2
  .app (mkAppN
      (generatedRecursorCheckPrefix stats elimLevel motives minors indType)
      indices)
    (generatedRecursorConstructorApplication stats constructor fields)

/-- One constructor-specific generated-rule verification.  Besides the four
checker equations it retains the exact constructor traversal, terminal
indices, field locals, constructor application, and recursor left-hand side. -/
structure GeneratedRecursorRuleCheck
    (stats : InductiveStats) (elimLevel : Level)
    (motives minors : Array Expr) (indType : InductiveType)
    (recursor : RecursorVal) (constructor : Constructor)
    (initialContext finalContext : Context) where
  terminal : Expr
  fields : Array Expr
  recursiveFields : Array Expr
  argumentsRun :
    mkRecInfos.loopCtorArgs stats constructor.type
      (fun terminal fields recursiveFields context =>
        .ok (terminal, fields, recursiveFields, context)) initialContext =
      .ok (terminal, fields, recursiveFields, finalContext)
  constructorApplication : Expr
  constructorApplication_eq : constructorApplication =
    generatedRecursorConstructorApplication stats constructor fields
  lhs : Expr
  lhs_eq : lhs = generatedRecursorRuleLhs stats elimLevel motives minors
    indType constructor terminal fields
  expected : Expr
  expectedRun :
    TypeChecker.M.run finalContext.env (safety := finalContext.safety)
      (lctx := finalContext.lctx) (lparams := recursor.levelParams)
      (fuel := finalContext.fuel) (TypeChecker.inferType lhs) = .ok expected
  reduct : Expr
  reductRun :
    TypeChecker.M.run finalContext.env (safety := finalContext.safety)
      (lctx := finalContext.lctx) (lparams := recursor.levelParams)
      (fuel := finalContext.fuel) (TypeChecker.whnf lhs) = .ok reduct
  actual : Expr
  actualRun :
    TypeChecker.M.run finalContext.env (safety := finalContext.safety)
      (lctx := finalContext.lctx) (lparams := recursor.levelParams)
      (fuel := finalContext.fuel) (TypeChecker.inferType reduct) = .ok actual
  typePreservingRun :
    TypeChecker.M.run finalContext.env (safety := finalContext.safety)
      (lctx := finalContext.lctx) (lparams := recursor.levelParams)
      (fuel := finalContext.fuel)
      (TypeChecker.isDefEq actual expected) = .ok true

/-- Run one constructor-specific generated-rule guard at an explicit
name-generator/local-context boundary. -/
def checkGeneratedRecursorRuleAt
    (stats : InductiveStats) (elimLevel : Level)
    (motives minors : Array Expr) (indType : InductiveType)
    (recursor : RecursorVal) (constructor : Constructor)
    (initialContext : Context) :
    Except Exception (Σ finalContext,
      GeneratedRecursorRuleCheck stats elimLevel motives minors indType
        recursor constructor initialContext finalContext) :=
  match hargs : mkRecInfos.loopCtorArgs stats constructor.type
      (fun terminal fields recursiveFields context =>
        .ok (terminal, fields, recursiveFields, context)) initialContext with
  | .error error => .error error
  | .ok (terminal, fields, recursiveFields, finalContext) =>
      let constructorApplication :=
        generatedRecursorConstructorApplication stats constructor fields
      let lhs := generatedRecursorRuleLhs stats elimLevel motives minors
        indType constructor terminal fields
      match hexpected : TypeChecker.M.run finalContext.env
          (safety := finalContext.safety) (lctx := finalContext.lctx)
          (lparams := recursor.levelParams) (fuel := finalContext.fuel)
          (TypeChecker.inferType lhs) with
      | .error error => .error error
      | .ok expected =>
          match hreduct : TypeChecker.M.run finalContext.env
              (safety := finalContext.safety) (lctx := finalContext.lctx)
              (lparams := recursor.levelParams) (fuel := finalContext.fuel)
              (TypeChecker.whnf lhs) with
          | .error error => .error error
          | .ok reduct =>
              match hactual : TypeChecker.M.run finalContext.env
                  (safety := finalContext.safety)
                  (lctx := finalContext.lctx)
                  (lparams := recursor.levelParams)
                  (fuel := finalContext.fuel)
                  (TypeChecker.inferType reduct) with
              | .error error => .error error
              | .ok actual =>
                  match hequal : TypeChecker.M.run finalContext.env
                      (safety := finalContext.safety)
                      (lctx := finalContext.lctx)
                      (lparams := recursor.levelParams)
                      (fuel := finalContext.fuel)
                      (TypeChecker.isDefEq actual expected) with
                  | .error error => .error error
                  | .ok false => .error (.other
                      s!"generated recursor computation rule for '{
                        constructor.name}' is not type-preserving")
                  | .ok true => .ok ⟨finalContext, {
                      terminal
                      fields
                      recursiveFields
                      argumentsRun := hargs
                      constructorApplication
                      constructorApplication_eq := rfl
                      lhs
                      lhs_eq := rfl
                      expected
                      expectedRun := hexpected
                      reduct
                      reductRun := hreduct
                      actual
                      actualRun := hactual
                      typePreservingRun := hequal }⟩

/-- Source-ordered generated-rule checks for all constructors of one family,
threading the persistent local/name-generator context exactly as the kernel
does. -/
inductive GeneratedRecursorRuleCheckTrace
    (stats : InductiveStats) (elimLevel : Level)
    (motives minors : Array Expr) (indType : InductiveType)
    (recursor : RecursorVal) :
    List Constructor → Context → Context → Type where
  | nil : GeneratedRecursorRuleCheckTrace stats elimLevel motives minors
      indType recursor [] context context
  | cons
      (head : GeneratedRecursorRuleCheck stats elimLevel motives minors
        indType recursor constructor initialContext nextContext)
      (tail : GeneratedRecursorRuleCheckTrace stats elimLevel motives minors
        indType recursor constructors nextContext finalContext) :
      GeneratedRecursorRuleCheckTrace stats elimLevel motives minors indType
        recursor (constructor :: constructors) initialContext finalContext

/-- Execute all constructor checks for one generated recursor in source
order. -/
def checkGeneratedRecursorRulesAt
    (stats : InductiveStats) (elimLevel : Level)
    (motives minors : Array Expr) (indType : InductiveType)
    (recursor : RecursorVal) :
    (constructors : List Constructor) → (initialContext : Context) →
      Except Exception (Σ finalContext,
        GeneratedRecursorRuleCheckTrace stats elimLevel motives minors
          indType recursor constructors initialContext finalContext)
  | [], context => .ok ⟨context, .nil⟩
  | constructor :: constructors, context => do
      let ⟨nextContext, head⟩ ← checkGeneratedRecursorRuleAt stats elimLevel
        motives minors indType recursor constructor context
      let ⟨finalContext, tail⟩ ← checkGeneratedRecursorRulesAt stats elimLevel
        motives minors indType recursor constructors nextContext
      return ⟨finalContext, .cons head tail⟩

/-- One family-specific generated-recursor verification: the exact final-env
lookup, a full check of the stored recursor type, and every source constructor
rule check. -/
structure GeneratedRecursorFamilyCheck
    (stats : InductiveStats) (indTypes : Array InductiveType)
    (elimLevel : Level) (motives minors : Array Expr) (dIdx : Nat)
    (initialContext finalContext : Context) where
  active : dIdx < indTypes.size
  recursor : RecursorVal
  recursorLookup : initialContext.env.find?
    (mkRecName indTypes[dIdx].name) = some (.recInfo recursor)
  recursorType : Expr
  recursorType_eq : recursorType = recursor.type
  recursorTypeInferred : Expr
  recursorTypeRun :
    TypeChecker.M.run initialContext.env (safety := initialContext.safety)
      (lctx := initialContext.lctx) (lparams := recursor.levelParams)
      (fuel := initialContext.fuel) (TypeChecker.checkType recursorType) =
      .ok recursorTypeInferred
  rules : GeneratedRecursorRuleCheckTrace stats elimLevel motives minors
    indTypes[dIdx] recursor indTypes[dIdx].ctors initialContext finalContext

/-- Complete family-ordered generated-recursor guard. -/
inductive GeneratedRecursorCheckTrace
    (stats : InductiveStats) (indTypes : Array InductiveType)
    (elimLevel : Level) (motives minors : Array Expr) :
    Nat → Context → Context → Type where
  | done
      (finished : ¬ dIdx < indTypes.size) :
      GeneratedRecursorCheckTrace stats indTypes elimLevel motives minors
        dIdx context context
  | next
      (family : GeneratedRecursorFamilyCheck stats indTypes elimLevel
        motives minors dIdx initialContext nextContext)
      (tail : GeneratedRecursorCheckTrace stats indTypes elimLevel motives
        minors (dIdx + 1) nextContext finalContext) :
      GeneratedRecursorCheckTrace stats indTypes elimLevel motives minors
        dIdx initialContext finalContext

/-- Execute Lean 4.33.1's generated-recursor guard over every family. -/
def checkGeneratedRecursorsAt
    (stats : InductiveStats) (indTypes : Array InductiveType)
    (elimLevel : Level) (motives minors : Array Expr) :
    (dIdx : Nat) → (initialContext : Context) →
      Except Exception (Σ finalContext,
        GeneratedRecursorCheckTrace stats indTypes elimLevel motives minors
          dIdx initialContext finalContext)
  | dIdx, context =>
      if active : dIdx < indTypes.size then
        let indType := indTypes[dIdx]
        let recName := mkRecName indType.name
        match hlookup : context.env.find? recName with
        | none => .error (.other
            s!"generated recursor '{recName}' is missing")
        | some (.recInfo recursor) =>
            let recursorType := recursor.type
            match htype : TypeChecker.M.run context.env
                (safety := context.safety) (lctx := context.lctx)
                (lparams := recursor.levelParams) (fuel := context.fuel)
                (TypeChecker.checkType recursorType) with
            | .error error => .error error
            | .ok recursorTypeInferred => do
                let ⟨nextContext, rules⟩ ←
                  checkGeneratedRecursorRulesAt stats elimLevel motives minors
                    indType recursor indType.ctors context
                let ⟨finalContext, tail⟩ ←
                  checkGeneratedRecursorsAt stats indTypes elimLevel motives
                    minors (dIdx + 1) nextContext
                return ⟨finalContext, .next {
                  active
                  recursor
                  recursorLookup := hlookup
                  recursorType
                  recursorType_eq := rfl
                  recursorTypeInferred
                  recursorTypeRun := htype
                  rules } tail⟩
        | some _ => .error (.other
            s!"generated declaration '{recName}' is not a recursor")
      else
        .ok ⟨context, .done active⟩
termination_by dIdx context => indTypes.size - dIdx

/-- A one-pass recursor declaration plus the exact 4.33.1 generated-recursors
verification.  `synthesisRun` owns the only execution of the detailed
producer; `recursorsRun` is its proof-level public projection. -/
structure CheckedRecursorDeclaration
    (stats : InductiveStats) (indTypes : Array InductiveType)
    (elimLevel : Level) (k : Bool) (context : Context) where
  synthesis : RecursorDeclarationSynthesis stats indTypes elimLevel k context
  synthesisRun :
    declareRecursorsDetailedAt stats indTypes elimLevel k context =
      .ok synthesis
  recursors : RecursorDeclarationResult
  recursors_eq : recursors = synthesis.toDeclarationResult
  recursorsRun :
    declareRecursors stats indTypes elimLevel k context = .ok recursors
  finalContext : Context
  verification : GeneratedRecursorCheckTrace stats indTypes elimLevel
    (synthesis.recInfos.map (·.motive))
    (synthesis.recInfos.flatMap (·.minors)) 0
    { synthesis.synthesisContext with env := synthesis.tail.env }
    finalContext

/-- Run recursor synthesis, declaration, and the generated-artifact guard
without repeating the producer. -/
def declareRecursorsCheckedAt (stats : InductiveStats)
    (indTypes : Array InductiveType) (elimLevel : Level) (k : Bool)
    (context : Context) : Except Exception
      (CheckedRecursorDeclaration stats indTypes elimLevel k context) :=
  match hsynthesis : declareRecursorsDetailedAt stats indTypes elimLevel k
      context with
  | .error error => .error error
  | .ok synthesis =>
      let motives := synthesis.recInfos.map (·.motive)
      let minors := synthesis.recInfos.flatMap (·.minors)
      let verificationContext : Context :=
        { synthesis.synthesisContext with env := synthesis.tail.env }
      match checkGeneratedRecursorsAt stats indTypes elimLevel motives minors
          0 verificationContext with
      | .error error => .error error
      | .ok ⟨finalContext, verification⟩ =>
          let recursors := synthesis.toDeclarationResult
          .ok {
            synthesis
            synthesisRun := hsynthesis
            recursors
            recursors_eq := rfl
            recursorsRun := synthesis.declareRecursorsRun hsynthesis
            finalContext
            verification := by
              simpa only [motives, minors, verificationContext] using
                verification }

/-- Reader-independent package for the checked recursor result returned by
the ordinary `AddInductive.M` pipeline. -/
structure CheckedRecursorDeclarationResult
    (stats : InductiveStats) (indTypes : Array InductiveType)
    (elimLevel : Level) (k : Bool) where
  context : Context
  checked : CheckedRecursorDeclaration stats indTypes elimLevel k context

/-- Reader-form checked recursor phase used by the public ordinary runner. -/
def declareRecursorsChecked (stats : InductiveStats)
    (indTypes : Array InductiveType) (elimLevel : Level) (k : Bool) :
    M (CheckedRecursorDeclarationResult stats indTypes elimLevel k) :=
  fun context =>
    (declareRecursorsCheckedAt stats indTypes elimLevel k context).map fun
      checked => { context, checked }

/-- Run an ordinary flattened inductive transaction through the retained
normalization prefix consumed by Theory/Verify.  The prefix keeps the kernel's
family-validation, raw-declaration, and constructor-validation order, then
executes the exact pre-family and post-family candidate traversals before any
generated constructor or recursor metadata is committed. -/
def run (nparams : Nat) (types : List InductiveType) (numNested : Nat) : M Environment := do
  let candidateContext ← read
  let isUnsafe := candidateContext.safety != .safe
  let indTypes := types.toArray
  let {lparams, ..} := candidateContext
  Environment.checkDuplicatedUnivParams lparams
  let normalization ← liftM <| buildNormalizationCandidateExecution
    nparams types numNested isUnsafe candidateContext
  withReader (fun _ : Context =>
    { normalization.validationContext with env := normalization.familyEnv }) do
  withEnv (← declareConstructors normalization.stats indTypes isUnsafe) do
  let elimLevel ← getElimLevel normalization.stats indTypes
  let k ← isKTarget normalization.stats indTypes
  let checked ← declareRecursorsChecked normalization.stats indTypes
    elimLevel k
  pure checked.checked.recursors.env

end AddInductive

namespace ElimNestedInductive

structure Result where
  ngen : NameGenerator
  nparams : Nat
  lctx : LocalContext
  params : Array Expr -- the fvars declared in `lctx`
  aux2nested : NameMap Expr -- exprs are open over `params`, like the C++ `m_aux2nested`
  /-- Exact owner of every auxiliary constructor emitted by nested
  elimination.  Retaining this map makes restoration classification a
  producer-owned fact instead of a lookup reconstructed from the temporary
  flattened environment. -/
  auxCtor2Induct : NameMap Name
  types : List InductiveType
  types_nonempty : types.isEmpty = false

instance [MonadStateOf NameGenerator m] : MonadNameGenerator m where
  getNGen := get
  setNGen := set

namespace Result

/-- Structural abstraction of the fresh parameter FVar introduced by nested
restoration.  Unlike the opaque array abstraction primitive, this one-variable
form exposes the binder-depth shift needed by the prefix invariant. -/
def abstractNestedFVar (id : FVarId) : Expr → (depth : Nat := 0) → Expr
  | .bvar index, depth =>
      .bvar (if index < depth then index else index + 1)
  | expression@(.fvar other), depth =>
      if id == other then .bvar depth else expression
  | .mdata data expression, depth =>
      .mdata data (abstractNestedFVar id expression depth)
  | .proj typeName index expression, depth =>
      .proj typeName index (abstractNestedFVar id expression depth)
  | .app function argument, depth =>
      .app (abstractNestedFVar id function depth)
        (abstractNestedFVar id argument depth)
  | .lam name domain body binderInfo, depth =>
      .lam name (abstractNestedFVar id domain depth)
        (abstractNestedFVar id body (depth + 1)) binderInfo
  | .forallE name domain body binderInfo, depth =>
      .forallE name (abstractNestedFVar id domain depth)
        (abstractNestedFVar id body (depth + 1)) binderInfo
  | .letE name type value body nondep, depth =>
      .letE name (abstractNestedFVar id type depth)
        (abstractNestedFVar id value depth)
        (abstractNestedFVar id body (depth + 1)) nondep
  | expression@(.const ..), _
  | expression@(.sort _), _
  | expression@(.mvar _), _
  | expression@(.lit _), _ => expression

def getNestedIfAuxCtor (r : Result) (_env' : Environment) (c : Name) : Option (Expr × Name) := do
  let induct ← r.auxCtor2Induct.find? c
  return (← r.aux2nested.find? induct, induct)

def restoreCtorName (r : Result) (env' : Environment) (c : Name) : Name := Id.run do
  let (e, name) := (r.getNestedIfAuxCtor env' c).get!
  let .const I _ := e.getAppFn | unreachable!
  c.replacePrefix name I

/-- One top-down rewrite step used by `restoreNestedBody`.  Naming the
callback separately exposes the exact replacement boundary to verification:
recursive traversal stops precisely when this operation returns `some`. -/
def restoreNestedBodyRewrite? (r : Result) (env' : Environment)
    (As : Array Expr) (auxRec : NameMap Name) (t : Expr) : Option Expr := do
    if let .const c ls := t then
      if let some recName := auxRec.find? c then
        return .const recName ls
    let .const c _ := t.getAppFn | none
    if let some nested := r.aux2nested.find? c then
      let args := t.getAppArgs
      assert! args.size ≥ r.nparams
      return mkAppRange ((nested.abstract r.params).instantiateRev As) r.nparams args.size args
    let (nested, auxI_name) ← r.getNestedIfAuxCtor env' c
    let args := t.getAppArgs
    assert! args.size ≥ r.nparams
    let nested' := (nested.abstract r.params).instantiateRev As
    nested'.withApp fun I I_args => do
    let .const I_c I_ls := I | unreachable!
    let c' := .const (c.replacePrefix auxI_name I_c) I_ls
    return mkAppRange (mkAppN c' I_args) r.nparams args.size args

private def restoreNestedBodyImpl (r : Result) (env' : Environment) (e : Expr)
    (As : Array Expr) (auxRec : NameMap Name) : Expr :=
  e.replace (r.restoreNestedBodyRewrite? env' As auxRec)

/-- Restore the body opened over the exact shared-parameter FVars selected by
`restoreNestedAux`.  Keeping this rewrite separate from the prefix traversal
makes the fact that restoration never visits a parameter domain structural.
The logical definition uses the transparent no-cache traversal so proofs can
follow every visited child; compiled code retains the kernel's pointer-cached
implementation. -/
@[implemented_by restoreNestedBodyImpl]
def restoreNestedBody (r : Result) (env' : Environment) (e : Expr)
    (As : Array Expr) (auxRec : NameMap Name) : Expr :=
  e.replaceNoCache (r.restoreNestedBodyRewrite? env' As auxRec)

/-- Open and rebuild the shared-parameter prefix one binder at a time.  The
fresh FVars passed to `restoreNestedBody` are abstracted immediately on the
way back out, so each parameter domain is retained verbatim and only the
terminal body is rewritten.  `pi` preserves the kernel's historical choice
to rebuild the whole prefix using the outer binder kind. -/
def restoreNestedAux (r : Result) (env' : Environment)
    (auxRec : NameMap Name) (pi : Bool) :
    (remaining : Nat) → (e : Expr) → (As : Array Expr) →
      StateM NameGenerator Expr
  | 0, e, As => pure (r.restoreNestedBody env' e As auxRec)
  | remaining + 1, e, As => do
      match e with
      | .forallE name dom body bi | .lam name dom body bi =>
        let id := ⟨← mkFreshId⟩
        let arg := .fvar id
        let restored ← r.restoreNestedAux env' auxRec pi remaining
          (body.instantiate1 arg) (As.push arg)
        let restoredBody := abstractNestedFVar id restored
        return if pi then .forallE name dom restoredBody bi
          else .lam name dom restoredBody bi
      | _ => unreachable!

def restoreNested (r : Result) (env' : Environment) (e : Expr)
    (auxRec : NameMap Name := {}) : Expr :=
  Id.run <| StateT.run' (s :=
      { namePrefix := `_nested_fresh : NameGenerator }) <|
    r.restoreNestedAux env' auxRec e.isForall r.nparams e #[]

/-- Transparent loose-bound-variable range used by the nested producer's
restoration certificate.  Unlike the packed expression cache, this traversal
can be used as proof evidence for arbitrary syntax. -/
def restorationLooseBVarRange : Expr → Nat
  | .bvar index => index + 1
  | .mdata _ expression
  | .proj _ _ expression => restorationLooseBVarRange expression
  | .app function argument =>
      max (restorationLooseBVarRange function)
        (restorationLooseBVarRange argument)
  | .lam _ domain body _
  | .forallE _ domain body _ =>
      max (restorationLooseBVarRange domain)
        (restorationLooseBVarRange body - 1)
  | .letE _ type value body _ =>
      max (max (restorationLooseBVarRange type)
        (restorationLooseBVarRange value))
        (restorationLooseBVarRange body - 1)
  | .const ..
  | .sort _
  | .fvar _
  | .mvar _
  | .lit _ => 0

/-- The arguments erased by one auxiliary-family or auxiliary-constructor
restoration step contain no loose bound variables. -/
def restoreNestedBodyNodeDependencyCheck (r : Result) (source : Expr) : Bool :=
  match source.getAppFn with
  | .const name _ =>
      if (r.aux2nested.find? name).isSome ||
          (r.auxCtor2Induct.find? name).isSome then
        (source.getAppArgs.extract 0 r.nparams).all fun argument =>
          restorationLooseBVarRange argument == 0
      else
        true
  | _ => true

/-- Structural certificate checked at every node visited by the public
top-down nested-restoration callback. -/
def restoreNestedBodyDependencyCheck (r : Result) : Expr → Bool
  | source@(.app function argument) =>
      r.restoreNestedBodyNodeDependencyCheck source &&
        r.restoreNestedBodyDependencyCheck function &&
        r.restoreNestedBodyDependencyCheck argument
  | source@(.lam _ domain body _)
  | source@(.forallE _ domain body _) =>
      r.restoreNestedBodyNodeDependencyCheck source &&
        r.restoreNestedBodyDependencyCheck domain &&
        r.restoreNestedBodyDependencyCheck body
  | source@(.letE _ type value body _) =>
      r.restoreNestedBodyNodeDependencyCheck source &&
        r.restoreNestedBodyDependencyCheck type &&
        r.restoreNestedBodyDependencyCheck value &&
        r.restoreNestedBodyDependencyCheck body
  | source@(.mdata _ expression)
  | source@(.proj _ _ expression) =>
      r.restoreNestedBodyNodeDependencyCheck source &&
        r.restoreNestedBodyDependencyCheck expression
  | source => r.restoreNestedBodyNodeDependencyCheck source

/-- Execute the same shared-parameter opening loop as `restoreNestedAux`,
then check the terminal body on which restoration actually runs. -/
def restoreNestedAuxDependencyCheck (r : Result) :
    Nat → Expr → Array Expr → NameGenerator → Bool
  | 0, source, _, _ => r.restoreNestedBodyDependencyCheck source
  | remaining + 1, .forallE _ _ body _, parameters, ngen
  | remaining + 1, .lam _ _ body _, parameters, ngen =>
      let id : FVarId := ⟨ngen.curr⟩
      let argument : Expr := .fvar id
      r.restoreNestedAuxDependencyCheck remaining
        (body.instantiate1 argument) (parameters.push argument) ngen.next
  | _ + 1, _, _, _ => false

/-- Public constructor-level restoration certificate. -/
def restoreNestedDependencyCheck (r : Result) (source : Expr) : Bool :=
  let initial : NameGenerator := { namePrefix := `_nested_fresh }
  r.restoreNestedAuxDependencyCheck r.nparams source #[] initial

/-- Every constructor emitted by this nested-elimination result is safe for
the exact subsequent public restoration pass. -/
def restorationDependencyCheck (r : Result) : Bool :=
  r.types.all fun type =>
    type.ctors.all fun constructor =>
      r.restoreNestedDependencyCheck constructor.type

end Result

structure State where
  ngen : NameGenerator := { namePrefix := `_nested_fresh }
  nestedAux : Array (Expr × Name) := {}
  auxCtor2Induct : NameMap Name := {}
  lvls : List Level
  newTypes : Array InductiveType
  newTypes_nonempty : newTypes.isEmpty = false
  nextIdx : Nat := 1

instance : Inhabited State where
  default := {
    lvls := []
    newTypes := #[default]
    newTypes_nonempty := rfl }

namespace State

/-- Appending an auxiliary family preserves the nonempty flattened block. -/
@[simp] def pushNewType (state : State) (newType : InductiveType) : State := {
  state with
  newTypes := state.newTypes.push newType
  newTypes_nonempty := by
    simp [Array.isEmpty] }

/-- Replacing one processed family preserves the nonempty flattened block. -/
@[simp] def setNewType (state : State) (index : Nat)
    (newType : InductiveType) : State := {
  state with
  newTypes := state.newTypes.set! index newType
  newTypes_nonempty := by
    rw [Array.isEmpty]
    simpa using state.newTypes_nonempty }

/-- The state's flattened family list is nonempty. -/
theorem newTypes_toList_nonempty (state : State) :
    state.newTypes.toList.isEmpty = false := by
  apply List.isEmpty_eq_false_iff.mpr
  intro empty
  have sizeZero : state.newTypes.size = 0 := by
    rw [← Array.length_toList, empty]
    rfl
  have emptyArray : state.newTypes.isEmpty = true := by
    simp [Array.isEmpty, sizeZero]
  rw [state.newTypes_nonempty] at emptyArray
  contradiction

end State

/--
info: 'Lean4Lean.ElimNestedInductive.State.newTypes_toList_nonempty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms State.newTypes_toList_nonempty

abbrev M := ReaderT Environment <| StateT State <| Except Exception

instance : MonadNameGenerator M where
  getNGen := return (← get).ngen
  setNGen ngen := modify fun s => { s with ngen }

-- TODO: remove partial
partial def mkUniqueName (n : Name) : M Name := fun env s =>
  let rec loop i :=
    let r := n.appendIndexAfter i
    if env.contains r then
      loop (i + 1)
    else
      pure (r, { s with nextIdx := i + 1 })
  loop s.nextIdx

def illFormed : Exception :=
  .other "invalid nested inductive datatype, ill-formed declaration"

def replaceParams (params : Array Expr) (e : Expr) (As : Array Expr) : M Expr := do
  assert! As.size == params.size
  return (e.abstract As).instantiateRev params

/-- IF `e` is of the form `I Ds is` where
  1) `I` is a nested inductive datatype (i.e., a previously declared inductive datatype),
  2) the parametric arguments `Ds` do not contain loose bound variables, and do contain inductive datatypes in `m_new_types`
THEN return the `inductive_val` in the `constant_info` associated with `I`.
Otherwise, return none. -/
def isNestedInductiveApp? (e : Expr) : M (Option InductiveVal) := do
  if !e.isApp then return none
  let .const fn _ := e.getAppFn | return none
  let env ← read
  let some (.inductInfo ci) := env.find? fn | return none
  let args := e.getAppArgs
  if ci.numParams > args.size then return none
  let mut isNested := false
  let mut looseBVars := false
  for i in [0:ci.numParams] do
    if args[i]!.hasLooseBVars then
      looseBVars := true
    let newTypes := (← get).newTypes
    if let some _ := args[i]!.find? fun
      | .const t _ => newTypes.any fun ty => t == ty.name
      | _ => false
    then
      isNested := true
  if !isNested then return none
  if looseBVars then
    throw <| .other s!"invalid nested inductive datatype '{fn}', \
      nested inductive datatypes parameters cannot contain local variables."
  return some ci

def instantiateForallParams (e : Expr) (hi : Nat) (params : Array Expr) :
    Except Exception Expr := do
  let mut e := e
  for _ in [:hi] do
    let .forallE _ _ body _ := e | throw illFormed
    e := body
  return e.instantiateRevRange 0 hi params

/-- If `e` is a nested occurrence `I Ds is`, return `Iaux As is` -/
def replaceIfNested (lctx : LocalContext) (params : Array Expr) (As : Array Expr) (e : Expr) :
    M (Option Expr) := do
  let some I_val ← isNestedInductiveApp? e | return none
  e.withApp fun fn args => do
  let .const I_name I_lvls := fn | unreachable!
  let I_nparams := I_val.numParams
  assert! I_nparams ≤ args.size
  let IAs := mkAppRange fn 0 I_nparams args -- `I As`
  let Iparams ← replaceParams params IAs As
  let st ← get
  if let some auxI_name := st.nestedAux.findSome? fun (e, n) =>
    if e == Iparams then some n else none
  then
    return mkAppRange (mkAppN (.const auxI_name st.lvls) As) I_nparams args.size args
  let mut result := none
  let env ← read
  for J_name in I_val.all do
    let .inductInfo J_info ← env.get J_name | unreachable!
    let J := .const J_name I_lvls
    let JAs := mkAppRange J 0 I_nparams args
    let auxJ_name ← mkUniqueName (`_nested ++ J_name)
    let auxJ_type := J_info.type.instantiateLevelParams J_info.levelParams I_lvls
    let auxJ_type := lctx.mkForall As <| ← instantiateForallParams auxJ_type I_nparams args
    let JAs' ← replaceParams params JAs As
    modify fun st => { st with nestedAux := st.nestedAux.push (JAs', auxJ_name) }
    if J_name == I_name then
      result := some <|
        mkAppRange (mkAppN (.const auxJ_name (← get).lvls) As) I_nparams args.size args
    let auxJ_ctors ← J_info.ctors.mapM fun J_ctor_name => do
      let J_ctor_info ← env.get J_ctor_name
      -- auxJ_cnstr_type still has references to `J`, this will be fixed later when we process it.
      let auxJ_ctor_name := J_ctor_name.replacePrefix J_name auxJ_name
      modify fun st => { st with
        auxCtor2Induct := st.auxCtor2Induct.insert auxJ_ctor_name auxJ_name }
      let auxJ_ctor_type := J_ctor_info.type.instantiateLevelParams J_ctor_info.levelParams I_lvls
      let auxJ_ctor_type ← instantiateForallParams auxJ_ctor_type I_nparams args
      return { name := auxJ_ctor_name, type := lctx.mkForall As auxJ_ctor_type }
    let newType := { name := auxJ_name, type := auxJ_type, ctors := auxJ_ctors }
    modify fun st => st.pushNewType newType
  assert! result.isSome
  return result

def replaceAllNested (lctx : LocalContext) (params : Array Expr) (As : Array Expr) (e : Expr) :
    M Expr := e.replaceM (replaceIfNested lctx params As)

def withParams (type : Expr) (nparams : Nat)
    (k : LocalContext → Expr → Array Expr → M α) : M α := loop {} type #[] nparams where
  loop lctx type params
  | 0 => k lctx type params
  | i+1 => do
    let .forallE name dom body bi := type
      | throw <| .other "invalid inductive datatype declaration, incorrect number of parameters"
    let id := ⟨← mkFreshId⟩
    let lctx := lctx.mkLocalDecl id name dom bi
    let arg := .fvar id
    loop lctx (body.instantiate1 arg) (params.push arg) i

def run (fuel nparams : Nat) (types : List InductiveType) : M Result := do
  let I :: _ := types
    | throw <| .other s!"invalid empty (mutual) inductive datatype declaration, \
        it must contain at least one inductive type."
  withParams I.type nparams fun lctx _ params => do
  let rec loop i
  | 0 => throw <| .other "deep recursion: ElimNestedInductive.run.loop"
  | fuel+1 => do
    let s ← get
    if _h : i < s.newTypes.size then
      let indType := s.newTypes[i]
      let ctors ← indType.ctors.mapM fun ctor => do
        withParams ctor.type nparams fun lctx ctorType As => do
        assert! As.size == nparams
        return { ctor with type := lctx.mkForall As (← replaceAllNested lctx params As ctorType) }
      modify fun s => s.setNewType i { indType with ctors }
      loop (i+1) fuel
    else
      let aux2nested := s.nestedAux.foldl (fun m (e, n) => m.insert n e) {}
      return {
        ngen := s.ngen
        nparams := params.size
        lctx := lctx
        params := params
        aux2nested := aux2nested
        auxCtor2Induct := s.auxCtor2Induct
        types := s.newTypes.toList
        types_nonempty := s.newTypes_toList_nonempty }
  loop 0 fuel
end ElimNestedInductive

def mkAuxRecNameMap (env' : Environment) (types : List InductiveType) :
    List Name × NameMap Name := Id.run do
  let mainType :: _ := types | unreachable!
  let ntypes := types.length
  let mainName := mainType.name
  let some (.inductInfo mainInfo) := env'.find? mainName | unreachable!
  let allNames := mainInfo.all
  assert! allNames.length > ntypes
  let mut oldRecNames := #[]
  let mut recMap : NameMap Name := {}
  let mut nextIdx := 1
  for indName in allNames.drop ntypes do
    let oldRecName := mkRecName indName
    let newRecName := (mkRecName mainName).appendIndexAfter nextIdx
    nextIdx := nextIdx + 1
    recMap := recMap.insert oldRecName newRecName
    oldRecNames := oldRecNames.push oldRecName
  return (oldRecNames.toList, recMap)

/-- Transparent reserved-prefix occurrence test used by the public inductive
precheck.  This follows the same expression children as `Expr.find?`, but its
structural definition lets a retained successful execution expose the exact
absence fact to later verification phases. -/
def hasNestedAux : Expr → Bool
  | .const name _ => (`_nested).isPrefixOf name
  | .app function argument =>
      hasNestedAux function || hasNestedAux argument
  | .lam _ domain body _ | .forallE _ domain body _ =>
      hasNestedAux domain || hasNestedAux body
  | .letE _ type value body _ =>
      hasNestedAux type || hasNestedAux value || hasNestedAux body
  | .mdata _ body => hasNestedAux body
  | .proj structureName _ body =>
      (`_nested).isPrefixOf structureName || hasNestedAux body
  | _ => false

def checkNoNestedAux (n : Name) (e : Expr) : Except Exception Unit := do
  if hasNestedAux e then
    throw <| .other s!"invalid declaration '{n}', it uses the reserved prefix '_nested'"

/-- Closedness and reserved-prefix checks performed before nested
elimination.  Naming this phase lets a retained outer execution own the exact
successful precheck equation. -/
def Environment.checkInductiveInput (env : Environment)
    (types : List InductiveType) : Except Exception Unit := do
  for indType in types do
    checkNoNestedAux indType.name (.const indType.name [])
    env.checkNoMVarNoFVar indType.name indType.type
    for ctor in indType.ctors do
      checkNoNestedAux ctor.name (.const ctor.name [])
      env.checkNoMVarNoFVar ctor.name ctor.type
      checkNoNestedAux ctor.name ctor.type

/-- Check one expression for the Lean 4.33.1 uniform-occurrence invariant.
An occurrence of a family currently being declared must use the declaration's
exact universe levels and the surrounding shared binders.  Over-applied
occurrences are traversed so their parameter prefix and indices are checked
separately, matching the kernel's `for_each` pass. -/
def checkUniformInductiveOccurrence (familyNames : List Name)
    (levels : List Level) (nparams : Nat) : Expr → Nat → Except Exception Unit
  | expression, offset => do
      let function := expression.getAppFn
      let arguments := expression.getAppArgs
      if let .const name actualLevels := function then
        if familyNames.contains name then
          if arguments.size ≤ nparams then
            let uniform := arguments.size == nparams &&
              offset ≥ nparams &&
              arguments.toList.zipIdx.all fun (argument, index) =>
                Expr.structuralEq argument (.bvar (offset - 1 - index))
            unless actualLevels == levels && uniform do
              throw <| .other s!"invalid occurrence of datatype '{name
                }' being declared: it must be applied to the parameters and universe levels of the mutual declaration"
            return
      match expression with
      | .app function argument =>
          checkUniformInductiveOccurrence familyNames levels nparams function
            offset
          checkUniformInductiveOccurrence familyNames levels nparams argument
            offset
      | .lam _ domain body _ | .forallE _ domain body _ =>
          checkUniformInductiveOccurrence familyNames levels nparams domain
            offset
          checkUniformInductiveOccurrence familyNames levels nparams body
            (offset + 1)
      | .letE _ type value body _ =>
          checkUniformInductiveOccurrence familyNames levels nparams type
            offset
          checkUniformInductiveOccurrence familyNames levels nparams value
            offset
          checkUniformInductiveOccurrence familyNames levels nparams body
            (offset + 1)
      | .mdata _ body | .proj _ _ body =>
          checkUniformInductiveOccurrence familyNames levels nparams body
            offset
      | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const _ _ | .lit _ =>
          pure ()
termination_by expression => expression

/-- Lean 4.33.1's up-front uniform-occurrence scan over the original
constructor declarations.  It intentionally runs before nested elimination
or WHNF can erase an invalid syntactic occurrence. -/
def Environment.checkUniformInductiveOccurrences (lparams : List Name)
    (nparams : Nat) (types : List InductiveType) : Except Exception Unit := do
  let familyNames := types.map (·.name)
  let levels := lparams.map Level.param
  for indType in types do
    for ctor in indType.ctors do
      checkUniformInductiveOccurrence familyNames levels nparams ctor.type 0

/-- Exact initial state used by nested elimination. -/
def ElimNestedInductive.initialState (lparams : List Name)
    (head : InductiveType) (tail : List InductiveType) :
    ElimNestedInductive.State where
  lvls := lparams.map .param
  newTypes := (head :: tail).toArray
  newTypes_nonempty := rfl

/-- Run nested elimination at the exact reader/state boundary used by
`Environment.addInductive`. -/
def ElimNestedInductive.runAt (env : Environment) (fuel nparams : Nat)
    (lparams : List Name) (types : List InductiveType) :
    Except Exception ElimNestedInductive.Result :=
  match types with
  | [] =>
      .error <| .other s!"invalid empty (mutual) inductive datatype declaration, \
        it must contain at least one inductive type."
  | head :: tail =>
      do
        let result ← ElimNestedInductive.run fuel nparams (head :: tail) env
          |>.run' (ElimNestedInductive.initialState lparams head tail)
        -- `run` obtains the same count as `params.size` after consuming the
        -- requested telescope.  Retain the public input directly so later
        -- restoration does not need to rediscover that operational invariant.
        let result' : ElimNestedInductive.Result :=
          { result with nparams := nparams }
        if result'.restorationDependencyCheck then
          return result'
        else
          throw <| .other "internal nested restoration dependency check failed"

/-- A successful nested-elimination run retains the exact shared parameter
count supplied at its public boundary. -/
theorem ElimNestedInductive.runAt_nparams_eq
    (run : ElimNestedInductive.runAt env fuel nparams lparams types =
      .ok result) :
    result.nparams = nparams := by
  cases types with
  | nil => simp [ElimNestedInductive.runAt] at run
  | cons head tail =>
      unfold ElimNestedInductive.runAt at run
      generalize hraw :
        ElimNestedInductive.run fuel nparams (head :: tail) env
          (ElimNestedInductive.initialState lparams head tail) = raw at run
      cases raw with
      | error error =>
          simp [StateT.run', Functor.map, Except.map, hraw, Bind.bind,
            Except.bind] at run
      | ok pair =>
          let checked : ElimNestedInductive.Result :=
            { pair.1 with nparams := nparams }
          by_cases check : checked.restorationDependencyCheck = true
          · simp [StateT.run', Functor.map, Except.map, hraw, Bind.bind,
              Except.bind, Pure.pure, Except.pure, checked, check] at run
            rw [← run]
          · simp [StateT.run', Functor.map, Except.map, hraw, Bind.bind,
              Except.bind, Pure.pure, Except.pure, throw, throwThe,
              MonadExceptOf.throw, checked, check] at run

/-- Every successful public nested-elimination execution owns the exact
constructor restoration certificate checked before flattened insertion. -/
theorem ElimNestedInductive.runAt_restorationDependencyCheck
    (run : ElimNestedInductive.runAt env fuel nparams lparams types =
      .ok result) :
    result.restorationDependencyCheck = true := by
  cases types with
  | nil => simp [ElimNestedInductive.runAt] at run
  | cons head tail =>
      unfold ElimNestedInductive.runAt at run
      generalize hraw :
        ElimNestedInductive.run fuel nparams (head :: tail) env
          (ElimNestedInductive.initialState lparams head tail) = raw at run
      cases raw with
      | error error =>
          simp [StateT.run', Functor.map, Except.map, hraw, Bind.bind,
            Except.bind] at run
      | ok pair =>
          let checked : ElimNestedInductive.Result :=
            { pair.1 with nparams := nparams }
          by_cases check : checked.restorationDependencyCheck = true
          · simp [StateT.run', Functor.map, Except.map, hraw, Bind.bind,
              Except.bind, Pure.pure, Except.pure, checked, check] at run
            rw [← run]
            exact check
          · simp [StateT.run', Functor.map, Except.map, hraw, Bind.bind,
              Except.bind, Pure.pure, Except.pure, throw, throwThe,
              MonadExceptOf.throw, checked, check] at run

/-- Reader context passed to the ordinary flattened-block checker. -/
def AddInductive.Context.forInductive (env : Environment)
    (lparams : List Name) (isUnsafe allowPrimitive : Bool)
    (fuel : FuelConfig) : AddInductive.Context where
  env
  allowPrimitive
  lparams
  fuel
  safety := if isUnsafe then .unsafe else .safe

/-- Restore one recursor record emitted for the flattened block.  Auxiliary
recursors are renamed into the source block's public recursor namespace;
types, rule constructors, and rule right-hand sides are restored exactly as
in the nested branch of `Environment.addInductive`. -/
def ElimNestedInductive.Result.restoreRecursorInfo
    (res : ElimNestedInductive.Result) (flatEnv : Environment)
    (allIndNames : List Name) (recNameMap : NameMap Name)
    (recName : Name) : RecursorVal := Id.run do
  let newRecName := recNameMap.getD recName recName
  let recInfo :=
    match flatEnv.find? recName with
    | some (.recInfo recInfo) => recInfo
    | _ => default
  let newRecType := res.restoreNested flatEnv recInfo.type recNameMap
  let newRules := recInfo.rules.map fun rule =>
    let newRhs := res.restoreNested flatEnv rule.rhs recNameMap
    let newCtorName := if newRecName == recName then rule.ctor else
      res.restoreCtorName flatEnv rule.ctor
    { rule with ctor := newCtorName, rhs := newRhs }
  return {
    recInfo with
    name := newRecName
    type := newRecType
    all := allIndNames
    rules := newRules }

/-- Restore the stored source-family record copied from the flattened block. -/
def ElimNestedInductive.Result.restoreInductiveInfo
    (_res : ElimNestedInductive.Result) (flatEnv : Environment)
    (allIndNames : List Name) (indType : InductiveType) : InductiveVal :=
  match flatEnv.find? indType.name with
  | some (.inductInfo ind) => { ind with all := allIndNames }
  | _ => unreachable!

/-- Restore one source constructor record copied from the flattened block. -/
def ElimNestedInductive.Result.restoreConstructorInfo
    (res : ElimNestedInductive.Result) (flatEnv : Environment)
    (ctorName : Name) : ConstructorVal :=
  match flatEnv.find? ctorName with
  | some (.ctorInfo ctor) =>
      { ctor with type := res.restoreNested flatEnv ctor.type }
  | _ => unreachable!

/-- Restore a source-family record while retaining its lookup key as the
public family name.  Successful flattened declarations already store this
same name; spelling the identity field explicitly makes restoration
provenance structural even outside that ambient map invariant. -/
def ElimNestedInductive.Result.restoreSourceInductiveInfo
    (res : ElimNestedInductive.Result) (flatEnv : Environment)
    (allIndNames : List Name) (indType : InductiveType) : InductiveVal :=
  { res.restoreInductiveInfo flatEnv allIndNames indType with
    name := indType.name }

/-- A nonempty restored constructor inventory can only come from a genuine
flattened family lookup (the defensive `unreachable!` fallback has the empty
default inventory).  The returned equation exposes the exact record copied
by restoration. -/
theorem ElimNestedInductive.Result.restoreSourceInductiveInfo_of_ctors_ne_nil
    (res : ElimNestedInductive.Result) (flatEnv : Environment)
    (allIndNames : List Name) (indType : InductiveType)
    (nonempty :
      (res.restoreSourceInductiveInfo flatEnv allIndNames indType).ctors ≠ []) :
    ∃ flatInfo,
      flatEnv.find? indType.name = some (.inductInfo flatInfo) ∧
      res.restoreSourceInductiveInfo flatEnv allIndNames indType =
        { flatInfo with name := indType.name, all := allIndNames } := by
  have defaultCtors : (default : InductiveVal).ctors = [] := rfl
  cases found : flatEnv.find? indType.name with
  | none =>
      have impossible : False := by
        apply nonempty
        simp [ElimNestedInductive.Result.restoreSourceInductiveInfo,
          ElimNestedInductive.Result.restoreInductiveInfo, found,
          defaultCtors]
      exact impossible.elim
  | some info =>
      cases info <;>
        simp_all [ElimNestedInductive.Result.restoreSourceInductiveInfo,
          ElimNestedInductive.Result.restoreInductiveInfo]

/-- Restore a source constructor while retaining the family chunk's public
owner and the constructor lookup key.  The flattened producer already emits
these exact fields; the explicit updates expose that fact to inventory
consumers while restoration still changes only the constructor type. -/
def ElimNestedInductive.Result.restoreSourceConstructorInfo
    (res : ElimNestedInductive.Result) (flatEnv : Environment)
    (induct ctorName : Name) : ConstructorVal :=
  { res.restoreConstructorInfo flatEnv ctorName with
    name := ctorName
    induct := induct
    numParams := res.nparams }

/-- Restore a source family's main recursor at its canonical public name.
Auxiliary recursors continue to use `mkAuxRecNameMap`; source recursors are
the unrenamed prefix of the restored inventory. -/
def ElimNestedInductive.Result.restoreSourceRecursorInfo
    (res : ElimNestedInductive.Result) (flatEnv : Environment)
    (allIndNames : List Name) (recNameMap : NameMap Name)
    (indType : InductiveType) : RecursorVal :=
  { res.restoreRecursorInfo flatEnv allIndNames recNameMap
      (mkRecName indType.name) with
    name := mkRecName indType.name }

/-- Restored metadata contributed by one source family: the family itself,
its constructors, and its canonical main recursor. -/
def restoredNestedFamilyInfos (res : ElimNestedInductive.Result)
    (flatEnv : Environment) (allIndNames : List Name)
    (recNameMap : NameMap Name) (indType : InductiveType) :
    List ConstantInfo :=
  let ind := res.restoreSourceInductiveInfo flatEnv allIndNames indType
  [ConstantInfo.inductInfo ind] ++
    (ind.ctors.map fun ctorName => ConstantInfo.ctorInfo <|
      res.restoreSourceConstructorInfo flatEnv indType.name ctorName) ++
    [ConstantInfo.recInfo <|
      res.restoreSourceRecursorInfo flatEnv allIndNames recNameMap indType]

/-- Restored auxiliary-recursor suffix, in the order selected by
`mkAuxRecNameMap`. -/
def restoredNestedAuxRecursorInfos (res : ElimNestedInductive.Result)
    (flatEnv : Environment) (allIndNames auxRecNames : List Name)
    (recNameMap : NameMap Name) : List ConstantInfo :=
  auxRecNames.map fun recName => .recInfo <|
    res.restoreRecursorInfo flatEnv allIndNames recNameMap recName

/-- Complete source-ordered metadata inventory installed by nested
restoration.  Each source family is followed by its source constructors and
main recursor; renamed auxiliary recursors form the final suffix. -/
def restoredNestedInfos (res : ElimNestedInductive.Result)
    (flatEnv : Environment) (types : List InductiveType) : List ConstantInfo :=
  let allIndNames := types.map (·.name)
  let (auxRecNames, recNameMap) := mkAuxRecNameMap flatEnv types
  types.flatMap
      (restoredNestedFamilyInfos res flatEnv allIndNames recNameMap) ++
    restoredNestedAuxRecursorInfos res flatEnv allIndNames auxRecNames
      recNameMap

/-- A restored family record in one source chunk retains that source
family's exact name. -/
theorem restoredNestedFamilyInfos_family_cases
    (member : (.inductInfo info : ConstantInfo) ∈
      restoredNestedFamilyInfos res flatEnv allIndNames recNameMap indType) :
    info.name = indType.name := by
  simp [restoredNestedFamilyInfos] at member
  obtain rfl := member
  rfl

/-- The family entry of one restored source chunk is not merely named by its
source family: it is definitionally the exact record assembled by the
restoration producer. -/
theorem restoredNestedFamilyInfos_family_exact
    (member : (.inductInfo info : ConstantInfo) ∈
      restoredNestedFamilyInfos res flatEnv allIndNames recNameMap indType) :
    info = res.restoreSourceInductiveInfo flatEnv allIndNames indType := by
  simp [restoredNestedFamilyInfos] at member
  obtain rfl := member
  rfl

/-- A restored constructor record in one source chunk retains that source
family as its exact owner. -/
theorem restoredNestedFamilyInfos_constructor_cases
    (member : (.ctorInfo info : ConstantInfo) ∈
      restoredNestedFamilyInfos res flatEnv allIndNames recNameMap indType) :
    info.induct = indType.name := by
  simp [restoredNestedFamilyInfos] at member
  obtain ⟨ctorName, _member, rfl⟩ := member
  rfl

/-- Every source-family chunk contains its canonical restored main
recursor. -/
theorem restoredNestedFamilyInfos_recursor
    (indType : InductiveType) :
    ∃ info,
      (.recInfo info : ConstantInfo) ∈
        restoredNestedFamilyInfos res flatEnv allIndNames recNameMap indType ∧
      info.name = mkRecName indType.name := by
  refine ⟨res.restoreSourceRecursorInfo flatEnv allIndNames recNameMap
    indType, ?_, rfl⟩
  simp [restoredNestedFamilyInfos]

/-- Every family record in the complete restored inventory is indexed by an
exact source family. -/
theorem restoredNestedInfos_family_cases
    (member : (.inductInfo info : ConstantInfo) ∈
      restoredNestedInfos res flatEnv types) :
    ∃ indType ∈ types, info.name = indType.name := by
  simp only [restoredNestedInfos, List.mem_append, List.mem_flatMap] at member
  rcases member with member | member
  · obtain ⟨indType, sourceMember, familyMember⟩ := member
    exact ⟨indType, sourceMember,
      restoredNestedFamilyInfos_family_cases familyMember⟩
  · simp [restoredNestedAuxRecursorInfos] at member

/-- Every family in the complete restored inventory is the exact producer
record belonging to one original source family. -/
theorem restoredNestedInfos_family_exact
    (member : (.inductInfo info : ConstantInfo) ∈
      restoredNestedInfos res flatEnv types) :
    ∃ indType ∈ types,
      info = res.restoreSourceInductiveInfo flatEnv
        (types.map (·.name)) indType := by
  simp only [restoredNestedInfos, List.mem_append, List.mem_flatMap] at member
  rcases member with member | member
  · obtain ⟨indType, sourceMember, familyMember⟩ := member
    exact ⟨indType, sourceMember,
      restoredNestedFamilyInfos_family_exact familyMember⟩
  · simp [restoredNestedAuxRecursorInfos] at member

/-- Every constructor record in the complete restored inventory retains the
exact source family that owns its chunk. -/
theorem restoredNestedInfos_constructor_cases
    (member : (.ctorInfo info : ConstantInfo) ∈
      restoredNestedInfos res flatEnv types) :
    ∃ indType ∈ types, info.induct = indType.name := by
  simp only [restoredNestedInfos, List.mem_append, List.mem_flatMap] at member
  rcases member with member | member
  · obtain ⟨indType, sourceMember, constructorMember⟩ := member
    exact ⟨indType, sourceMember,
      restoredNestedFamilyInfos_constructor_cases constructorMember⟩
  · simp [restoredNestedAuxRecursorInfos] at member

/-- Every restored source constructor retains the shared parameter count
owned by the nested-elimination result.  The auxiliary suffix contains only
recursors, so no other constructor case exists. -/
theorem restoredNestedInfos_constructor_numParams
    (member : (.ctorInfo info : ConstantInfo) ∈
      restoredNestedInfos res flatEnv types) :
    info.numParams = res.nparams := by
  simp only [restoredNestedInfos, List.mem_append, List.mem_flatMap] at member
  rcases member with member | member
  · obtain ⟨indType, _sourceMember, constructorMember⟩ := member
    simp [restoredNestedFamilyInfos,
      ElimNestedInductive.Result.restoreSourceConstructorInfo] at constructorMember
    obtain ⟨_ctorName, _ctorMember, rfl⟩ := constructorMember
    rfl
  · have : False := by
      simp [restoredNestedAuxRecursorInfos] at member
    exact this.elim

/-- Restoration changes a source constructor's type and public ownership,
but retains the flattened producer's cached field count.  The exact flat
lookup keeps this fact tied to the constructor record selected by the
restored inventory rather than to a parallel name lookup. -/
theorem restoredNestedInfos_constructor_numFields_of_flat_lookup
    (member : (.ctorInfo info : ConstantInfo) ∈
      restoredNestedInfos res flatEnv types)
    (found : flatEnv.find? info.name = some (.ctorInfo flatInfo)) :
    info.numFields = flatInfo.numFields := by
  simp only [restoredNestedInfos, List.mem_append, List.mem_flatMap] at member
  rcases member with member | member
  · obtain ⟨indType, _sourceMember, constructorMember⟩ := member
    simp [restoredNestedFamilyInfos] at constructorMember
    obtain ⟨ctorName, _ctorMember, rfl⟩ := constructorMember
    simp [ElimNestedInductive.Result.restoreSourceConstructorInfo,
      ElimNestedInductive.Result.restoreConstructorInfo] at found ⊢
    rw [found]
  · simp [restoredNestedAuxRecursorInfos] at member

/-- The public restored constructor type is exactly the nested-restoration
rewrite of the flattened constructor record selected by the same lookup. -/
theorem restoredNestedInfos_constructor_type_of_flat_lookup
    (member : (.ctorInfo info : ConstantInfo) ∈
      restoredNestedInfos res flatEnv types)
    (found : flatEnv.find? info.name = some (.ctorInfo flatInfo)) :
    info.type = res.restoreNested flatEnv flatInfo.type := by
  simp only [restoredNestedInfos, List.mem_append, List.mem_flatMap] at member
  rcases member with member | member
  · obtain ⟨indType, _sourceMember, constructorMember⟩ := member
    simp [restoredNestedFamilyInfos] at constructorMember
    obtain ⟨ctorName, _ctorMember, rfl⟩ := constructorMember
    simp [ElimNestedInductive.Result.restoreSourceConstructorInfo,
      ElimNestedInductive.Result.restoreConstructorInfo] at found ⊢
    rw [found]
  · simp [restoredNestedAuxRecursorInfos] at member

/-- Constructor restoration rewrites only the stored type; its universe
parameter names remain those of the exact flattened constructor record
selected by the same lookup. -/
theorem restoredNestedInfos_constructor_levelParams_of_flat_lookup
    (member : (.ctorInfo info : ConstantInfo) ∈
      restoredNestedInfos res flatEnv types)
    (found : flatEnv.find? info.name = some (.ctorInfo flatInfo)) :
    info.levelParams = flatInfo.levelParams := by
  simp only [restoredNestedInfos, List.mem_append, List.mem_flatMap] at member
  rcases member with member | member
  · obtain ⟨indType, _sourceMember, constructorMember⟩ := member
    simp [restoredNestedFamilyInfos] at constructorMember
    obtain ⟨ctorName, _ctorMember, rfl⟩ := constructorMember
    simp [ElimNestedInductive.Result.restoreSourceConstructorInfo,
      ElimNestedInductive.Result.restoreConstructorInfo] at found ⊢
    rw [found]
  · simp [restoredNestedAuxRecursorInfos] at member

/-- Every recursor in the restored inventory records the complete public
source-family list.  This includes both canonical source recursors and the
renamed auxiliary suffix; restoration deliberately gives both groups the
same `all` inventory. -/
theorem restoredNestedInfos_recursor_all
    (member : (.recInfo info : ConstantInfo) ∈
      restoredNestedInfos res flatEnv types) :
    info.all = types.map (·.name) := by
  simp only [restoredNestedInfos, List.mem_append, List.mem_flatMap] at member
  rcases member with member | member
  · obtain ⟨indType, _sourceMember, recursorMember⟩ := member
    simp [restoredNestedFamilyInfos] at recursorMember
    obtain rfl := recursorMember
    simp [ElimNestedInductive.Result.restoreSourceRecursorInfo,
      ElimNestedInductive.Result.restoreRecursorInfo]
  · simp [restoredNestedAuxRecursorInfos] at member
    obtain ⟨_recName, _recursorMember, rfl⟩ := member
    simp [ElimNestedInductive.Result.restoreRecursorInfo]

/-- Every source family contributes its exact public family record to the
complete restored inventory.  This is the family-side counterpart of
`restoredNestedInfos_recursor_of_family`; retaining the record explicitly is
useful when freshness must be transported back across the restoration fold. -/
theorem restoredNestedInfos_family_of_source
    (sourceMember : indType ∈ types) :
    ∃ info,
      (.inductInfo info : ConstantInfo) ∈
        restoredNestedInfos res flatEnv types ∧
      info.name = indType.name := by
  let info := res.restoreSourceInductiveInfo flatEnv
    (types.map (·.name)) indType
  refine ⟨info, ?_, rfl⟩
  simp only [restoredNestedInfos, List.mem_append, List.mem_flatMap]
  refine .inl ⟨indType, sourceMember, ?_⟩
  simp [restoredNestedFamilyInfos, info]

/-- Every source family owns a canonical main recursor in the complete
restored inventory. -/
theorem restoredNestedInfos_recursor_of_family
    (sourceMember : indType ∈ types) :
    ∃ info,
      (.recInfo info : ConstantInfo) ∈ restoredNestedInfos res flatEnv types ∧
      info.name = mkRecName indType.name := by
  obtain ⟨info, familyMember, nameEq⟩ :=
    restoredNestedFamilyInfos_recursor
      (res := res) (flatEnv := flatEnv)
      (allIndNames := types.map (·.name))
      (recNameMap := (mkAuxRecNameMap flatEnv types).2) indType
  refine ⟨info, ?_, nameEq⟩
  simp only [restoredNestedInfos, List.mem_append, List.mem_flatMap]
  exact .inl ⟨indType, sourceMember, familyMember⟩

/-- Transparent declaration fold used by nested restoration. -/
def declareRestoredInfoList (allowPrimitive : Bool) :
    List ConstantInfo → Environment → Except Exception Environment
  | [], env => .ok env
  | info :: infos, env => do
      env.checkName info.name allowPrimitive
      declareRestoredInfoList allowPrimitive infos (env.add info)

/-- Exact operational trace of the restored metadata fold. -/
inductive DeclareRestoredInfoListRun (allowPrimitive : Bool) :
    Environment → List ConstantInfo → Environment → Prop where
  | nil : DeclareRestoredInfoListRun allowPrimitive env [] env
  | cons
      (checkName : env.checkName info.name allowPrimitive = .ok ())
      (tail : DeclareRestoredInfoListRun allowPrimitive
        (env.add info) infos finalEnv) :
      DeclareRestoredInfoListRun allowPrimitive env (info :: infos) finalEnv

theorem DeclareRestoredInfoListRun.of_run
    (run : declareRestoredInfoList allowPrimitive infos env = .ok finalEnv) :
    DeclareRestoredInfoListRun allowPrimitive env infos finalEnv := by
  induction infos generalizing env with
  | nil =>
      simp only [declareRestoredInfoList, Except.ok.injEq] at run
      subst finalEnv
      exact .nil
  | cons info infos ih =>
      simp only [declareRestoredInfoList] at run
      cases hcheck : env.checkName info.name allowPrimitive with
      | error error =>
          rw [hcheck] at run
          contradiction
      | ok value =>
          have value_eq : value = () := Subsingleton.elim _ _
          subst value
          simp only [hcheck] at run
          exact .cons hcheck (ih run)

theorem DeclareRestoredInfoListRun.run
    (trace : DeclareRestoredInfoListRun allowPrimitive env infos finalEnv) :
    declareRestoredInfoList allowPrimitive infos env = .ok finalEnv := by
  induction trace with
  | nil => rfl
  | cons checkName _ ih =>
      simp only [declareRestoredInfoList, checkName, Bind.bind, Except.bind]
      exact ih

theorem DeclareRestoredInfoListRun.environment
    (trace : DeclareRestoredInfoListRun allowPrimitive env infos finalEnv) :
    finalEnv = infos.foldl (fun env info => env.add info) env := by
  induction trace with
  | nil => rfl
  | cons _ _ ih => simpa only [List.foldl_cons] using ih

private theorem declaredRestoredInfoList_constants : ∀
    (infos : List ConstantInfo) (env : Environment),
    (infos.foldl (fun env info => env.add info) env).constants =
      infos.foldl (fun constants info =>
        constants.insert info.name info) env.constants
  | [], _ => rfl
  | info :: infos, env =>
      declaredRestoredInfoList_constants infos (env.add info)

private theorem declaredRestoredInfoList_quotInit : ∀
    (infos : List ConstantInfo) (env : Environment),
    (infos.foldl (fun env info => env.add info) env).quotInit = env.quotInit
  | [], _ => rfl
  | info :: infos, env =>
      declaredRestoredInfoList_quotInit infos (env.add info)

/-- The restoration trace exposes the exact final persistent constant map. -/
theorem DeclareRestoredInfoListRun.constants
    (trace : DeclareRestoredInfoListRun allowPrimitive env infos finalEnv) :
    finalEnv.constants = infos.foldl
      (fun constants info => constants.insert info.name info)
      env.constants := by
  rw [trace.environment]
  exact declaredRestoredInfoList_constants infos env

/-- Restored metadata insertion does not modify quotient initialization. -/
theorem DeclareRestoredInfoListRun.quotInit
    (trace : DeclareRestoredInfoListRun allowPrimitive env infos finalEnv) :
    finalEnv.quotInit = env.quotInit := by
  rw [trace.environment]
  exact declaredRestoredInfoList_quotInit infos env

/-- The lean4#14577 escape-hatch check, isolated from metadata restoration so
its successful equation can be retained by the outer execution. -/
def checkNestedAuxValues (res : ElimNestedInductive.Result)
    (env : Environment) (safety : DefinitionSafety) (lparams : List Name)
    (fuel : FuelConfig) : Except Exception Unit :=
  TypeChecker.M.run env (safety := safety) (lctx := res.lctx)
      (lparams := lparams) (fuel := fuel) do
    res.aux2nested.forM fun _ e => do
      _ ← TypeChecker.checkType e

/-- Which restored artifact is being rechecked by Lean 4.33.1's final
defense-in-depth pass.  Rule origins retain both the recursor and constructor
names so later semantic consumers do not have to rediscover their ownership
from an unindexed expression list. -/
inductive RestoredArtifactCheckOrigin where
  | constructorType (constructor : Name)
  | recursorType (recursor : Name)
  | ruleRhs (recursor constructor : Name)

/-- One source expression, with the universe-parameter context in which the
kernel rechecks it after nested restoration. -/
structure RestoredArtifactCheckSource where
  origin : RestoredArtifactCheckOrigin
  lparams : List Name
  expression : Expr

/-- Restored constructor types in source order.  The restored inventory is
assembled family-by-family, so filtering it preserves the original family and
constructor ordering used by Lean's final pass. -/
def restoredConstructorCheckSources (lparams : List Name) :
    List ConstantInfo → List RestoredArtifactCheckSource
  | [] => []
  | .ctorInfo constructor :: infos =>
      { origin := .constructorType constructor.name
        lparams
        expression := constructor.type } ::
        restoredConstructorCheckSources lparams infos
  | _ :: infos => restoredConstructorCheckSources lparams infos

/-- Restored recursors in inventory order, with each recursor type immediately
followed by its computation-rule right-hand sides. -/
def restoredRecursorCheckSources :
    List ConstantInfo → List RestoredArtifactCheckSource
  | [] => []
  | .recInfo recursor :: infos =>
      { origin := .recursorType recursor.name
        lparams := recursor.levelParams
        expression := recursor.type } ::
        (recursor.rules.map fun rule =>
          { origin := .ruleRhs recursor.name rule.ctor
            lparams := recursor.levelParams
            expression := rule.rhs }) ++
        restoredRecursorCheckSources infos
  | _ :: infos => restoredRecursorCheckSources infos

/-- The exact source order of Lean 4.33.1's post-restoration recheck. -/
def restoredArtifactCheckSources (lparams : List Name)
    (infos : List ConstantInfo) : List RestoredArtifactCheckSource :=
  restoredConstructorCheckSources lparams infos ++
    restoredRecursorCheckSources infos

/-- Data-bearing successful checks for a source-ordered restored-artifact
inventory.  Every node retains the exact full-check equation in the final
restored environment. -/
inductive RestoredArtifactCheckTrace (env : Environment)
    (safety : DefinitionSafety) (fuel : FuelConfig) :
    List RestoredArtifactCheckSource → Type where
  | nil : RestoredArtifactCheckTrace env safety fuel []
  | cons {source sources} (inferred : Expr)
      (check : TypeChecker.M.run env (safety := safety) (lctx := {})
        (lparams := source.lparams) (fuel := fuel)
        (TypeChecker.checkType source.expression) = .ok inferred)
      (tail : RestoredArtifactCheckTrace env safety fuel sources) :
      RestoredArtifactCheckTrace env safety fuel (source :: sources)

/-- Execute and retain every full typecheck in the post-restoration pass. -/
def checkRestoredArtifactSources (env : Environment)
    (safety : DefinitionSafety) (fuel : FuelConfig) :
    (sources : List RestoredArtifactCheckSource) →
      Except Exception (RestoredArtifactCheckTrace env safety fuel sources)
  | [] => .ok .nil
  | source :: sources =>
      match hcheck : TypeChecker.M.run env (safety := safety) (lctx := {})
          (lparams := source.lparams) (fuel := fuel)
          (TypeChecker.checkType source.expression) with
      | .error error => .error error
      | .ok inferred =>
          match checkRestoredArtifactSources env safety fuel sources with
          | .error error => .error error
          | .ok tail => .ok (.cons inferred hcheck tail)

/-- Complete Lean 4.33.1 restored-artifact recheck over one exact restored
inventory. -/
def checkRestoredArtifacts (infos : List ConstantInfo) (env : Environment)
    (safety : DefinitionSafety) (lparams : List Name) (fuel : FuelConfig) :
    Except Exception (RestoredArtifactCheckTrace env safety fuel
      (restoredArtifactCheckSources lparams infos)) :=
  checkRestoredArtifactSources env safety fuel
    (restoredArtifactCheckSources lparams infos)

/-- Successful nested restoration retains the exact restored inventory, all
name checks and insertions, the auxiliary-value typecheck, and every final
restored-artifact recheck. -/
structure NestedRestorationResult
    (res : ElimNestedInductive.Result) (flatEnv initialEnv : Environment)
    (types : List InductiveType) (allowPrimitive : Bool)
    (safety : DefinitionSafety) (lparams : List Name) (fuel : FuelConfig) where
  infos : List ConstantInfo
  infos_eq : infos = restoredNestedInfos res flatEnv types
  env : Environment
  trace : DeclareRestoredInfoListRun allowPrimitive initialEnv infos env
  auxCheck : checkNestedAuxValues res env safety lparams fuel = .ok ()
  artifactChecks : RestoredArtifactCheckTrace env safety fuel
    (restoredArtifactCheckSources lparams infos)
  artifactChecksRun :
    checkRestoredArtifacts infos env safety lparams fuel = .ok artifactChecks

theorem NestedRestorationResult.constants
    (result : NestedRestorationResult res flatEnv initialEnv types
      allowPrimitive safety lparams fuel) :
    result.env.constants =
      (restoredNestedInfos res flatEnv types).foldl
        (fun constants info => constants.insert info.name info)
        initialEnv.constants := by
  rw [result.trace.constants, result.infos_eq]

/-- Execute the complete nested restoration phase while retaining its
data-bearing metadata and auxiliary-check trace. -/
def restoreNestedEnvironment (res : ElimNestedInductive.Result)
    (flatEnv initialEnv : Environment) (types : List InductiveType)
    (allowPrimitive : Bool) (safety : DefinitionSafety)
    (lparams : List Name) (fuel : FuelConfig) :
    Except Exception (NestedRestorationResult res flatEnv initialEnv types
      allowPrimitive safety lparams fuel) :=
  let infos := restoredNestedInfos res flatEnv types
  match hdeclare : declareRestoredInfoList allowPrimitive infos initialEnv with
  | .error error => .error error
  | .ok restoredEnv =>
    match hcheck : checkNestedAuxValues res restoredEnv safety lparams fuel with
    | .error error => .error error
    | .ok () =>
      match hartifacts : checkRestoredArtifacts infos restoredEnv safety
          lparams fuel with
      | .error error => .error error
      | .ok artifactChecks => .ok {
          infos
          infos_eq := rfl
          env := restoredEnv
          trace := DeclareRestoredInfoListRun.of_run hdeclare
          auxCheck := hcheck
          artifactChecks
          artifactChecksRun := hartifacts }

def Environment.addInductive (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe allowPrimitive : Bool) (fuel : FuelConfig := {}) :
    Except Exception Environment := do
  Environment.checkInductiveInput env types
  Environment.checkUniformInductiveOccurrences lparams nparams types
  let res ← ElimNestedInductive.runAt env fuel.inductiveFuel nparams
    lparams types
  let numNested := res.aux2nested.size
  let env' ← AddInductive.run nparams res.types numNested
    (AddInductive.Context.forInductive env lparams isUnsafe allowPrimitive fuel)
  if numNested = 0 then return env'
  return (← restoreNestedEnvironment res env' env types allowPrimitive
    (if isUnsafe then .unsafe else .safe) lparams fuel).env
