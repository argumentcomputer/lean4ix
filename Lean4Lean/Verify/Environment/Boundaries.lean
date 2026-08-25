/-
This file is derived from lean4lean and has been modified by Argument Computer Corporation.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/

import Lean4Lean.Verify.TypeChecker
import Lean4Lean.Environment

/-!
This module contains the front-end-specific trust boundary for declaration verification.
The checker, extension, and declaration modules introduce no additional `sorry`-backed
assumptions. The imported type-checker and theory layers retain their own explicit
verification gaps.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

/-- What the primitive-definition recognizer must establish beyond ordinary type checking.
This is kept separate from declaration checking so that the remaining metatheory does not
depend on the recognizer's syntactic implementation. Primitive semantics are claimed only
in well-formed extensions of the environment in which recognition ran. -/
structure PrimitiveResult (checked : VEnv) (v : DefinitionVal) (allow : Bool) : Prop where
  safe : allow = true → v.safety = .safe
  no_level_params : allow = true → v.levelParams = []
  preserves : allow = true → ∀ {safety : DefinitionSafety} {venv env' : VEnv} {ci' : VDefVal},
    checked ≤ venv → venv.WF →
    venv.HasPrimitives →
    TrDefVal safety venv (.defnInfo v) ci' → ci'.WF venv →
    venv.addConst v.name ci'.toVConstant = some env' →
    (env'.addDefEq ci'.toDefEq).HasPrimitives

/-- Exact host syntax accepted by the primitive-inductive recognizer.  Binder
names and binder information on `Nat.succ` are retained existentially because
Lean expression equivalence deliberately ignores those annotations. -/
def PrimitiveInductiveShape (types : List InductiveType) : Prop :=
  ∃ type, types = [type] ∧ type.type = .sort (.succ .zero) ∧
    ((type.name = ``Bool ∧ type.ctors = [
        ⟨``Bool.false, .const ``Bool []⟩,
        ⟨``Bool.true, .const ``Bool []⟩]) ∨
      (type.name = ``Nat ∧ ∃ binderName binderInfo, type.ctors = [
        ⟨``Nat.zero, .const ``Nat []⟩,
        ⟨``Nat.succ, .forallE binderName (.const ``Nat [])
          (.const ``Nat []) binderInfo⟩]))

/-- Proof-carrying result of primitive-inductive recognition.  The false
branch claims nothing; the true branch records every outer guard and the
complete canonical `Bool`/`Nat` shape needed by primitive reflection. -/
structure PrimitiveInductiveResult (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe allow : Bool) : Prop where
  recognized : allow = true →
    isUnsafe = false ∧ lparams = [] ∧ nparams = 0 ∧
      PrimitiveInductiveShape types

/-- The executable primitive-inductive recognizer returns `true` only for
the two canonical primitive families. -/
theorem checkPrimitiveInductive.WF (env : Environment)
    (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (isUnsafe : Bool) :
    (Environment.checkPrimitiveInductive env lparams nparams types
      isUnsafe).WF fun allow =>
        PrimitiveInductiveResult lparams nparams types isUnsafe allow := by
  intro allow run
  constructor
  intro hallow
  subst allow
  unfold Environment.checkPrimitiveInductive at run
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff,
    beq_iff_eq] at run
  split at run
  · rename_i guard
    obtain ⟨⟨hunsafe, hlevels⟩, hparams⟩ := guard
    refine ⟨hunsafe, hlevels, hparams, ?_⟩
    cases types with
    | nil => simp [Pure.pure, Except.pure] at run
    | cons type rest =>
      cases rest with
      | cons next tail => simp [Pure.pure, Except.pure] at run
      | nil =>
        refine ⟨type, rfl, ?_⟩
        repeat' split at run
        all_goals simp_all [Expr.eqv_sort, Pure.pure, Except.pure,
          Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
  · simp [Pure.pure, Except.pure] at run

/--
info: 'Lean4Lean.checkPrimitiveInductive.WF' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.eqv_eq,
 Level.instLawfulBEqLevel]
-/
#guard_msgs in
#print axioms checkPrimitiveInductive.WF

private theorem arrayFoldl_empty' {α β} (f : β → α → β) (init : β) :
    Array.foldl f init ({} : Array α) = init := by
  exact Array.foldl_empty

private theorem exprAbstract_empty (e : Expr) : e.abstract #[] = e := by
  simpa using (Expr.abstract_eq e [])

private theorem localContextMkForall_empty (lctx : LocalContext) (e : Expr) :
    lctx.mkForall #[] e = e := by
  unfold LocalContext.mkForall LocalContext.mkBinding
  rw [exprAbstract_empty]
  rfl

private def canonicalBoolTypes : List InductiveType :=
  [{ name := ``Bool
     type := .sort (.succ .zero)
     ctors := [
       ⟨``Bool.false, .const ``Bool []⟩,
       ⟨``Bool.true, .const ``Bool []⟩] }]

private def canonicalBoolNestedResult : ElimNestedInductive.Result where
  ngen := { namePrefix := `_nested_fresh }
  nparams := 0
  lctx := {}
  params := #[]
  aux2nested := {}
  types := canonicalBoolTypes

private theorem canonicalBoolNestedRun_succSucc (env : Environment)
    (fuel : Nat) :
    ElimNestedInductive.runAt env (fuel + 2) 0 [] canonicalBoolTypes =
      .ok canonicalBoolNestedResult := by
  simp (config := { maxSteps := 100000 }) [
    ElimNestedInductive.runAt, ElimNestedInductive.initialState,
    ElimNestedInductive.run, ElimNestedInductive.run.loop,
    ElimNestedInductive.withParams, ElimNestedInductive.withParams.loop,
    ElimNestedInductive.replaceAllNested,
    ElimNestedInductive.replaceIfNested,
    ElimNestedInductive.isNestedInductiveApp?,
    Expr.replaceM, Expr.replaceNoCacheT, Expr.isApp,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind,
    Pure.pure, ReaderT.pure, StateT.pure, Except.pure,
    StateT.run', Functor.map, Except.map,
    get, getThe, MonadStateOf.get, StateT.get,
    liftM, monadLift, MonadLift.monadLift,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    canonicalBoolTypes, canonicalBoolNestedResult,
    localContextMkForall_empty]
  exact arrayFoldl_empty' _ _

private theorem canonicalBoolNested_of_run {env : Environment} {fuel : Nat}
    {result : ElimNestedInductive.Result}
    (run : ElimNestedInductive.runAt env fuel 0 [] canonicalBoolTypes =
      .ok result) :
    result = canonicalBoolNestedResult := by
  cases fuel with
  | zero =>
      simp [ElimNestedInductive.runAt, ElimNestedInductive.initialState,
        ElimNestedInductive.run, ElimNestedInductive.run.loop,
        ElimNestedInductive.withParams, ElimNestedInductive.withParams.loop,
        Bind.bind, Except.bind,
        StateT.run', Functor.map, Except.map,
        liftM, monadLift, MonadLift.monadLift, StateT.lift,
        throw, throwThe, MonadExceptOf.throw, canonicalBoolTypes] at run
  | succ fuel =>
      cases fuel with
      | zero =>
          simp (config := { maxSteps := 100000 }) [
            ElimNestedInductive.runAt, ElimNestedInductive.initialState,
            ElimNestedInductive.run, ElimNestedInductive.run.loop,
            ElimNestedInductive.withParams,
            ElimNestedInductive.withParams.loop,
            ElimNestedInductive.replaceAllNested,
            ElimNestedInductive.replaceIfNested,
            ElimNestedInductive.isNestedInductiveApp?,
            Expr.replaceM, Expr.replaceNoCacheT, Expr.isApp,
            Bind.bind, ReaderT.bind, StateT.bind, Except.bind,
            Pure.pure, ReaderT.pure, StateT.pure, Except.pure,
            StateT.run', Functor.map, Except.map,
            get, getThe, MonadStateOf.get, StateT.get,
            liftM, monadLift, MonadLift.monadLift, StateT.lift,
            modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
            throw, throwThe, MonadExceptOf.throw, canonicalBoolTypes,
            localContextMkForall_empty] at run
      | succ fuel =>
          have expected := canonicalBoolNestedRun_succSucc env fuel
          exact (Except.ok.inj (expected.symm.trans run)).symm

private def canonicalNatTypes (binderName : Name) (binderInfo : BinderInfo) :
    List InductiveType :=
  [{ name := ``Nat
     type := .sort (.succ .zero)
     ctors := [
       ⟨``Nat.zero, .const ``Nat []⟩,
       ⟨``Nat.succ, .forallE binderName (.const ``Nat [])
         (.const ``Nat []) binderInfo⟩] }]

private def canonicalNatNestedResult (binderName : Name)
    (binderInfo : BinderInfo) : ElimNestedInductive.Result where
  ngen := { namePrefix := `_nested_fresh }
  nparams := 0
  lctx := {}
  params := #[]
  aux2nested := {}
  types := canonicalNatTypes binderName binderInfo

private theorem canonicalNatNestedRun_succSucc (env : Environment)
    (fuel : Nat) (binderName : Name) (binderInfo : BinderInfo) :
    ElimNestedInductive.runAt env (fuel + 2) 0 []
        (canonicalNatTypes binderName binderInfo) =
      .ok (canonicalNatNestedResult binderName binderInfo) := by
  simp (config := { maxSteps := 100000 }) [
    ElimNestedInductive.runAt, ElimNestedInductive.initialState,
    ElimNestedInductive.run, ElimNestedInductive.run.loop,
    ElimNestedInductive.withParams, ElimNestedInductive.withParams.loop,
    ElimNestedInductive.replaceAllNested,
    ElimNestedInductive.replaceIfNested,
    ElimNestedInductive.isNestedInductiveApp?,
    Expr.replaceM, Expr.replaceNoCacheT, Expr.isApp,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind,
    Pure.pure, ReaderT.pure, StateT.pure, Except.pure,
    StateT.run', Functor.map, Except.map,
    get, getThe, MonadStateOf.get, StateT.get,
    liftM, monadLift, MonadLift.monadLift,
    modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
    canonicalNatTypes, canonicalNatNestedResult,
    localContextMkForall_empty]
  exact arrayFoldl_empty' _ _

private theorem canonicalNatNested_of_run {env : Environment} {fuel : Nat}
    {binderName : Name} {binderInfo : BinderInfo}
    {result : ElimNestedInductive.Result}
    (run : ElimNestedInductive.runAt env fuel 0 []
        (canonicalNatTypes binderName binderInfo) = .ok result) :
    result = canonicalNatNestedResult binderName binderInfo := by
  cases fuel with
  | zero =>
      simp [ElimNestedInductive.runAt, ElimNestedInductive.initialState,
        ElimNestedInductive.run, ElimNestedInductive.run.loop,
        ElimNestedInductive.withParams, ElimNestedInductive.withParams.loop,
        Bind.bind, Except.bind,
        StateT.run', Functor.map, Except.map,
        liftM, monadLift, MonadLift.monadLift, StateT.lift,
        throw, throwThe, MonadExceptOf.throw, canonicalNatTypes] at run
  | succ fuel =>
      cases fuel with
      | zero =>
          simp (config := { maxSteps := 100000 }) [
            ElimNestedInductive.runAt, ElimNestedInductive.initialState,
            ElimNestedInductive.run, ElimNestedInductive.run.loop,
            ElimNestedInductive.withParams,
            ElimNestedInductive.withParams.loop,
            ElimNestedInductive.replaceAllNested,
            ElimNestedInductive.replaceIfNested,
            ElimNestedInductive.isNestedInductiveApp?,
            Expr.replaceM, Expr.replaceNoCacheT, Expr.isApp,
            Bind.bind, ReaderT.bind, StateT.bind, Except.bind,
            Pure.pure, ReaderT.pure, StateT.pure, Except.pure,
            StateT.run', Functor.map, Except.map,
            get, getThe, MonadStateOf.get, StateT.get,
            liftM, monadLift, MonadLift.monadLift, StateT.lift,
            modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
            throw, throwThe, MonadExceptOf.throw, canonicalNatTypes,
            localContextMkForall_empty] at run
      | succ fuel =>
          have expected := canonicalNatNestedRun_succSucc env fuel
            binderName binderInfo
          exact (Except.ok.inj (expected.symm.trans run)).symm

/-- Canonical primitive syntax cannot contain a nested inductive occurrence.
Consequently, every successful public nested-elimination run preserves the
source list exactly and emits no auxiliary families. -/
theorem ElimNestedInductive.Result.canonicalPrimitive_noop
    {env : Environment} {fuel : Nat} {types : List InductiveType}
    {result : ElimNestedInductive.Result}
    (shape : PrimitiveInductiveShape types)
    (run : ElimNestedInductive.runAt env fuel 0 [] types = .ok result) :
    result.types = types ∧ result.aux2nested.size = 0 := by
  obtain ⟨type, rfl, typeType, shape⟩ := shape
  rcases shape with boolShape | natShape
  · obtain ⟨typeName, constructorsEq⟩ := boolShape
    cases type
    subst typeName
    subst typeType
    subst constructorsEq
    have resultEq := canonicalBoolNested_of_run (by
      simpa only [canonicalBoolTypes] using run)
    subst result
    simp [canonicalBoolNestedResult, canonicalBoolTypes]
    rfl
  · obtain ⟨typeName, binderName, binderInfo, constructorsEq⟩ := natShape
    cases type
    subst typeName
    subst typeType
    subst constructorsEq
    have resultEq := canonicalNatNested_of_run (by
      simpa only [canonicalNatTypes] using run)
    subst result
    simp [canonicalNatNestedResult, canonicalNatTypes]
    rfl

/--
info: 'Lean4Lean.ElimNestedInductive.Result.canonicalPrimitive_noop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.abstract_eq]
-/
#guard_msgs in
#print axioms ElimNestedInductive.Result.canonicalPrimitive_noop

set_option warn.sorry false in
/-- Verification boundary for Lean4Lean's syntactic primitive-definition recognizer. -/
theorem checkPrimitiveDef.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) :
    (Environment.checkPrimitiveDef v).WF (.mk' wf .safe v.levelParams) {} fun allow _ =>
      PrimitiveResult (ves.venv .safe) v allow := by
  sorry
