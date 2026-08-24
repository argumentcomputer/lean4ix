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

set_option warn.sorry false in
/-- Verification boundary for Lean4Lean's syntactic primitive-definition recognizer. -/
theorem checkPrimitiveDef.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) :
    (Environment.checkPrimitiveDef v).WF (.mk' wf .safe v.levelParams) {} fun allow _ =>
      PrimitiveResult (ves.venv .safe) v allow := by
  sorry
