/-
This file is derived from lean4lean and has been modified by Argument Computer Corporation.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/

import Lean4Lean.Verify.Environment.RecursorReduction
import Lean4Lean.Verify.TypeChecker.Basic

namespace Lean4Lean.TypeChecker.Inner
open Lean hiding Environment Exception
open Kernel

/-- The pure tail of `inductiveReduceRec` applies exactly the recursor prefix,
the selected constructor fields, and the arguments trailing the major
premise. -/
theorem applyRecursorRule_eq_slices
    (hfirst : info.getFirstIndexIdx ≤ recArgs.size) :
    applyRecursorRule info rule levels recArgs majorArgs =
      Expr.mkAppList
        (rule.rhs.instantiateLevelParams info.levelParams levels)
        (recArgs.toList.take info.getFirstIndexIdx ++
          majorArgs.toList.drop (majorArgs.size - rule.nfields) ++
          recArgs.toList.drop (info.getMajorIdx + 1)) := by
  simp only [applyRecursorRule]
  rw [Expr.mkAppRange_zero_eq_take hfirst]
  rw [Expr.mkAppRange_suffix_eq_drop (Nat.sub_le ..)]
  split
  · rename_i htrail
    rw [Expr.mkAppRange_suffix_eq_drop (Nat.le_of_lt htrail)]
    simp only [← Expr.mkAppList_append, List.append_assoc]
  · rename_i htrail
    have hdrop : recArgs.toList.drop (info.getMajorIdx + 1) = [] := by
      apply List.length_eq_zero_iff.1
      rw [List.length_drop]
      simp only [Array.length_toList]
      omega
    rw [hdrop, List.append_nil]
    simp only [← Expr.mkAppList_append]

/-- Applying a selected recursor rule cannot introduce new free variables:
the recursor arguments come from the original expression, the constructor
fields come from its WHNF major, and the registered rule RHS is free-variable
closed.  This discharges the `FVarsBelow` half of the live verifier contract
independently of the semantic rule equation. -/
theorem applyRecursorRule_fvarsBelow
    {Δ : VLCtx} {info : RecursorVal} {rule : RecursorRule}
    {levels : List Level} {e major : Expr}
    (hfirst : info.getFirstIndexIdx ≤ e.getAppArgs.size)
    (hrhs : FVarsIn (fun _ => False)
      (rule.rhs.instantiateLevelParams info.levelParams levels))
    (hmajor : FVarsBelow Δ e major) :
    FVarsBelow Δ e
      (applyRecursorRule info rule levels e.getAppArgs major.getAppArgs) := by
  rw [applyRecursorRule_eq_slices hfirst]
  intro P hP he
  refine FVarsIn.mkAppList.2 ⟨hrhs.mono ?_, ?_⟩
  · simp
  · intro a ha
    simp only [List.mem_append] at ha
    rcases ha with (ha | ha) | ha
    · apply FVarsIn.getAppArgsList he
      simpa only [Expr.getAppArgs_toList] using List.mem_of_mem_take ha
    · apply FVarsIn.getAppArgsList (hmajor P hP he)
      simpa only [Expr.getAppArgs_toList] using List.mem_of_mem_drop ha
    · apply FVarsIn.getAppArgsList he
      simpa only [Expr.getAppArgs_toList] using List.mem_of_mem_drop ha

/-- A strict translation of a registered rule RHS in the empty local
context supplies the free-variable closure needed above after any
well-formed universe instantiation. -/
theorem instantiateLevelParams_fvarsIn_of_trExprS_empty
    {env : VEnv} {ps Us : List Name} {levels : List Level}
    {levelVals : List VLevel} {e : Expr} {e' : VExpr}
    (H : TrExprS env ps [] e e')
    (Hlevels : levels.mapM (VLevel.ofLevel Us) = some levelVals) :
    FVarsIn (fun _ => False) (e.instantiateLevelParams ps levels) := by
  simpa using H.fvarsIn.instantiateLevelParams Hlevels

/-- Strict translation of a constant-headed application fixes the host
universe-list length to the registered kernel constant's universe arity. -/
theorem getAppFn_const_levels_length_of_trExprS
    {c : VContext} {e : Expr} {e' : VExpr}
    {name : Name} {levels : List Level} {ci : ConstantInfo}
    (H : c.TrExprS e e')
    (hfn : e.getAppFn = .const name levels)
    (hfind : c.env.find? name = some ci) :
    levels.length = ci.levelParams.length := by
  obtain ⟨_, hhead⟩ := H.getAppFn
  rw [hfn] at hhead
  let .const hvenv _ hlen := hhead
  have ⟨_, htr⟩ := c.trenv.find?_uniq hfind hvenv
  exact hlen.trans htr.2.1.symm

/-- Structure-eta conversion is inert once the WHNF is already recognized as
a constructor application.  This isolates the first, callback-free exit of
`toCtorWhenStruct` for use by recursor-reduction execution proofs. -/
theorem toCtorWhenStruct_eq_pure_of_isConstructorApp
    {m : Type → Type} [Monad m]
    (env : Environment) (whnf inferType : Expr → m Expr)
    {inductName : Name} {e : Expr}
    (hctor : (e.isConstructorApp?' env).isSome = true) :
    toCtorWhenStruct env whnf inferType inductName e = pure e := by
  simp [toCtorWhenStruct, hctor]

/-- Structure conversion is also inert for an inductive that is not recorded
as a nonrecursive structure.  This is the common path for ordinary recursive
inductives, including the main and auxiliary Rose recursors. -/
theorem toCtorWhenStruct_eq_pure_of_not_nonRecStructure
    {m : Type → Type} [Monad m]
    (env : Environment) (whnf inferType : Expr → m Expr)
    {inductName : Name} {e : Expr}
    (hstruct : env.isNonRecStructure inductName = false) :
    toCtorWhenStruct env whnf inferType inductName e = pure e := by
  simp [toCtorWhenStruct, hstruct]

/-- The application head of a completed spine is the head of its seed. -/
theorem getAppFn_mkAppList (head : Expr) (args : List Expr) :
    (Expr.mkAppList head args).getAppFn = head.getAppFn := by
  induction args generalizing head with
  | nil => rfl
  | cons arg args ih =>
    rw [Expr.mkAppList, ih]
    rfl

/-- `getAppArgsList` exposes its accumulator as a suffix. -/
theorem getAppArgsList_append (e : Expr) (r : List Expr) :
    e.getAppArgsList r = e.getAppArgsList ++ r := by
  induction e generalizing r <;> try rfl
  rename_i f a ihf iha
  simp only [Expr.getAppArgsList]
  rw [ihf]
  rw [ihf (r := [a])]
  simp

/-- Completing a host application spine appends exactly the supplied
arguments to the seed's existing application arguments. -/
theorem getAppArgsList_mkAppList (e : Expr) (args : List Expr) :
    (Expr.mkAppList e args).getAppArgsList = e.getAppArgsList ++ args := by
  induction args generalizing e with
  | nil => simp
  | cons arg args ih =>
    rw [Expr.mkAppList, ih]
    rw [show (Expr.app e arg).getAppArgsList =
      e.getAppArgsList ++ [arg] by
        simp only [Expr.getAppArgsList]
        rw [getAppArgsList_append]]
    simp

/-- A constant seed has no pre-existing application arguments, so the
runtime array of a completed constructor spine is exactly its supplied
argument list. -/
theorem getAppArgs_mkAppList_const (ctor : Name) (levels : List Level)
    (args : List Expr) :
    (Expr.mkAppList (.const ctor levels) args).getAppArgs.toList = args := by
  rw [Expr.getAppArgs_toList, getAppArgsList_mkAppList]
  rfl

/-- An exact constructor lookup recognizes every completion of that
constructor's application spine. -/
theorem isConstructorApp?_mkAppList_of_find_ctor
    (env : Environment) {ctor : Name} {info : ConstructorVal}
    (levels : List Level) (args : List Expr)
    (hfind : env.find? ctor = some (.ctorInfo info)) :
    (Expr.mkAppList (.const ctor levels) args).isConstructorApp?' env =
      some ctor := by
  rw [Expr.isConstructorApp?', getAppFn_mkAppList]
  change (env.find? ctor).bind (fun
    | .ctorInfo _ => some ctor
    | _ => none) = some ctor
  rw [hfind]
  rfl

/-- A constant-headed application spine cannot enter either literal branch
of `inductiveReduceRec`. -/
theorem mkAppList_const_ne_lit (ctor : Name) (levels : List Level)
    (args : List Expr) (lit : Literal) :
    Expr.mkAppList (.const ctor levels) args ≠ .lit lit := by
  intro h
  have hfn := congrArg Expr.getAppFn h
  rw [getAppFn_mkAppList] at hfn
  cases hfn

/-- Execute the ordinary application-headed constructor branch of
`inductiveReduceRec` exactly.  This boundary retains the real environment
lookup, major selection, WHNF, structure conversion, rule lookup, arity
checks, and universe check, while exposing the already verified pure tail.
K conversion and literal branches remain separate control-flow cases. -/
theorem inductiveReduceRec_eq_some_applyRecursorRule_of_apps
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (env : Environment) (whnf inferType : Expr → m Expr)
    (isDefEq : Expr → Expr → m Bool)
    {e major whnfFn whnfArg ctorFn ctorArg : Expr} {recFn : Name}
    {levels : List Level} {info : RecursorVal} {rule : RecursorRule}
    (hfn : e.getAppFn = .const recFn levels)
    (hinfo : env.find? recFn = some (.recInfo info))
    (hmajor : e.getAppArgs[info.getMajorIdx]? = some major)
    (hk : info.k = false)
    (hwhnf : whnf major = pure (.app whnfFn whnfArg))
    (hstruct : toCtorWhenStruct env whnf inferType info.getMajorInduct
      (.app whnfFn whnfArg) = pure (.app ctorFn ctorArg))
    (hrule : getRecRuleFor info (.app ctorFn ctorArg) = some rule)
    (hfields : rule.nfields ≤ (Expr.app ctorFn ctorArg).getAppArgs.size)
    (hlevels : levels.length = info.levelParams.length) :
    inductiveReduceRec env e whnf inferType isDefEq =
      pure (some (applyRecursorRule info rule levels e.getAppArgs
        (Expr.app ctorFn ctorArg).getAppArgs)) := by
  have hnfields : ¬(Expr.app ctorFn ctorArg).getAppArgs.size <
      rule.nfields := Nat.not_lt_of_ge hfields
  simp [inductiveReduceRec, hfn, hinfo, hmajor, hk, hwhnf, hstruct,
    hrule, hnfields, hlevels]

/-- Pair the exact ordinary-constructor execution with any semantic proof of
its pure reduct.  In particular, the nested generated-body consumers below
can now describe the result returned by the actual `inductiveReduceRec`
program rather than only the isolated `applyRecursorRule` expression. -/
theorem inductiveReduceRec_result_trExpr_of_apps
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (env : Environment) (whnf inferType : Expr → m Expr)
    (isDefEq : Expr → Expr → m Bool)
    {e major whnfFn whnfArg ctorFn ctorArg : Expr} {recFn : Name}
    {levels : List Level} {info : RecursorVal} {rule : RecursorRule}
    (hfn : e.getAppFn = .const recFn levels)
    (hinfo : env.find? recFn = some (.recInfo info))
    (hmajor : e.getAppArgs[info.getMajorIdx]? = some major)
    (hk : info.k = false)
    (hwhnf : whnf major = pure (.app whnfFn whnfArg))
    (hstruct : toCtorWhenStruct env whnf inferType info.getMajorInduct
      (.app whnfFn whnfArg) = pure (.app ctorFn ctorArg))
    (hrule : getRecRuleFor info (.app ctorFn ctorArg) = some rule)
    (hfields : rule.nfields ≤ (Expr.app ctorFn ctorArg).getAppArgs.size)
    (hlevels : levels.length = info.levelParams.length)
    {venv : VEnv} {Us : List Name} {Δ : VLCtx} {target : VExpr}
    (hout : TrExpr venv Us Δ
      (applyRecursorRule info rule levels e.getAppArgs
        (Expr.app ctorFn ctorArg).getAppArgs) target) :
    ∃ result,
      inductiveReduceRec env e whnf inferType isDefEq = pure (some result) ∧
      TrExpr venv Us Δ result target := by
  refine ⟨_, ?_, hout⟩
  exact inductiveReduceRec_eq_some_applyRecursorRule_of_apps env whnf
    inferType isDefEq hfn hinfo hmajor hk hwhnf hstruct hrule hfields hlevels

/-- Execute the complete nonliteral WHNF branch without constraining the
constructor to one syntactic application node.  This covers arbitrary
completed constructor spines (including a bare nullary constructor), while
still keeping the Nat and String literal branches explicit and separate. -/
theorem inductiveReduceRec_eq_some_applyRecursorRule_of_nonliteral
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (env : Environment) (whnf inferType : Expr → m Expr)
    (isDefEq : Expr → Expr → m Bool)
    {e major whnfMajor ctorMajor : Expr} {recFn : Name}
    {levels : List Level} {info : RecursorVal} {rule : RecursorRule}
    (hfn : e.getAppFn = .const recFn levels)
    (hinfo : env.find? recFn = some (.recInfo info))
    (hmajor : e.getAppArgs[info.getMajorIdx]? = some major)
    (hk : info.k = false)
    (hwhnf : whnf major = pure whnfMajor)
    (hnotLit : ∀ lit, whnfMajor ≠ .lit lit)
    (hstruct : toCtorWhenStruct env whnf inferType info.getMajorInduct
      whnfMajor = pure ctorMajor)
    (hrule : getRecRuleFor info ctorMajor = some rule)
    (hfields : rule.nfields ≤ ctorMajor.getAppArgs.size)
    (hlevels : levels.length = info.levelParams.length) :
    inductiveReduceRec env e whnf inferType isDefEq =
      pure (some (applyRecursorRule info rule levels e.getAppArgs
        ctorMajor.getAppArgs)) := by
  have hnfields : ¬ctorMajor.getAppArgs.size < rule.nfields :=
    Nat.not_lt_of_ge hfields
  cases hwm : whnfMajor
  case lit lit => exact (hnotLit lit hwm).elim
  all_goals
    rw [hwm] at hwhnf hstruct
    simp [inductiveReduceRec, hfn, hinfo, hmajor, hk, hwhnf, hstruct,
      hrule, hnfields, hlevels]

/-- Semantic result wrapper for the general nonliteral constructor branch. -/
theorem inductiveReduceRec_result_trExpr_of_nonliteral
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (env : Environment) (whnf inferType : Expr → m Expr)
    (isDefEq : Expr → Expr → m Bool)
    {e major whnfMajor ctorMajor : Expr} {recFn : Name}
    {levels : List Level} {info : RecursorVal} {rule : RecursorRule}
    (hfn : e.getAppFn = .const recFn levels)
    (hinfo : env.find? recFn = some (.recInfo info))
    (hmajor : e.getAppArgs[info.getMajorIdx]? = some major)
    (hk : info.k = false)
    (hwhnf : whnf major = pure whnfMajor)
    (hnotLit : ∀ lit, whnfMajor ≠ .lit lit)
    (hstruct : toCtorWhenStruct env whnf inferType info.getMajorInduct
      whnfMajor = pure ctorMajor)
    (hrule : getRecRuleFor info ctorMajor = some rule)
    (hfields : rule.nfields ≤ ctorMajor.getAppArgs.size)
    (hlevels : levels.length = info.levelParams.length)
    {venv : VEnv} {Us : List Name} {Δ : VLCtx} {target : VExpr}
    (hout : TrExpr venv Us Δ
      (applyRecursorRule info rule levels e.getAppArgs
        ctorMajor.getAppArgs) target) :
    ∃ result,
      inductiveReduceRec env e whnf inferType isDefEq = pure (some result) ∧
      TrExpr venv Us Δ result target := by
  refine ⟨_, ?_, hout⟩
  exact inductiveReduceRec_eq_some_applyRecursorRule_of_nonliteral env whnf
    inferType isDefEq hfn hinfo hmajor hk hwhnf hnotLit hstruct hrule
    hfields hlevels

/-- Execute the nonliteral branch when K conversion is enabled.  The exact
result of `toCtorWhenK` is retained as a separate callback boundary before
the ordinary WHNF/structure/rule path. -/
theorem inductiveReduceRec_eq_some_applyRecursorRule_of_k_nonliteral
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (env : Environment) (whnf inferType : Expr → m Expr)
    (isDefEq : Expr → Expr → m Bool)
    {e major preparedMajor whnfMajor ctorMajor : Expr} {recFn : Name}
    {levels : List Level} {info : RecursorVal} {rule : RecursorRule}
    (hfn : e.getAppFn = .const recFn levels)
    (hinfo : env.find? recFn = some (.recInfo info))
    (hmajor : e.getAppArgs[info.getMajorIdx]? = some major)
    (hk : info.k = true)
    (hkmajor : toCtorWhenK env whnf inferType isDefEq info major =
      pure preparedMajor)
    (hwhnf : whnf preparedMajor = pure whnfMajor)
    (hnotLit : ∀ lit, whnfMajor ≠ .lit lit)
    (hstruct : toCtorWhenStruct env whnf inferType info.getMajorInduct
      whnfMajor = pure ctorMajor)
    (hrule : getRecRuleFor info ctorMajor = some rule)
    (hfields : rule.nfields ≤ ctorMajor.getAppArgs.size)
    (hlevels : levels.length = info.levelParams.length) :
    inductiveReduceRec env e whnf inferType isDefEq =
      pure (some (applyRecursorRule info rule levels e.getAppArgs
        ctorMajor.getAppArgs)) := by
  have hnfields : ¬ctorMajor.getAppArgs.size < rule.nfields :=
    Nat.not_lt_of_ge hfields
  cases hwm : whnfMajor
  case lit lit => exact (hnotLit lit hwm).elim
  all_goals
    rw [hwm] at hwhnf hstruct
    simp [inductiveReduceRec, hfn, hinfo, hmajor, hk, hkmajor, hwhnf,
      hstruct, hrule, hnfields, hlevels]

/-- K conversion followed by an already completed constructor spine avoids
the literal and structure-expansion callbacks just like the ordinary
constructor specialization. -/
theorem inductiveReduceRec_eq_some_applyRecursorRule_of_k_constructor
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (env : Environment) (whnf inferType : Expr → m Expr)
    (isDefEq : Expr → Expr → m Bool)
    {e major : Expr} {recFn ctor : Name}
    {levels ctorLevels : List Level} {ctorArgs : List Expr}
    {info : RecursorVal} {ctorInfo : ConstructorVal}
    {rule : RecursorRule}
    (hfn : e.getAppFn = .const recFn levels)
    (hinfo : env.find? recFn = some (.recInfo info))
    (hmajor : e.getAppArgs[info.getMajorIdx]? = some major)
    (hk : info.k = true)
    (hkmajor : toCtorWhenK env whnf inferType isDefEq info major =
      pure (Expr.mkAppList (.const ctor ctorLevels) ctorArgs))
    (hwhnf : whnf (Expr.mkAppList (.const ctor ctorLevels) ctorArgs) =
      pure (Expr.mkAppList (.const ctor ctorLevels) ctorArgs))
    (hctor : env.find? ctor = some (.ctorInfo ctorInfo))
    (hrule : getRecRuleFor info
      (Expr.mkAppList (.const ctor ctorLevels) ctorArgs) = some rule)
    (hfields : rule.nfields ≤ ctorArgs.length)
    (hlevels : levels.length = info.levelParams.length) :
    inductiveReduceRec env e whnf inferType isDefEq =
      pure (some (applyRecursorRule info rule levels e.getAppArgs
        (Expr.mkAppList (.const ctor ctorLevels) ctorArgs).getAppArgs)) := by
  apply inductiveReduceRec_eq_some_applyRecursorRule_of_k_nonliteral env whnf
    inferType isDefEq hfn hinfo hmajor hk hkmajor hwhnf
  · exact mkAppList_const_ne_lit ctor ctorLevels ctorArgs
  · apply toCtorWhenStruct_eq_pure_of_isConstructorApp
    rw [isConstructorApp?_mkAppList_of_find_ctor env ctorLevels ctorArgs
      hctor]
    rfl
  · exact hrule
  · rw [← Array.length_toList, getAppArgs_mkAppList_const]
    exact hfields
  · exact hlevels

/-- Execute the Nat-literal branch after its built-in conversion to the
canonical constructor spine. -/
theorem inductiveReduceRec_eq_some_applyRecursorRule_of_natLit
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (env : Environment) (whnf inferType : Expr → m Expr)
    (isDefEq : Expr → Expr → m Bool)
    {e major : Expr} {recFn : Name} {levels : List Level}
    {info : RecursorVal} {rule : RecursorRule} {n : Nat}
    (hfn : e.getAppFn = .const recFn levels)
    (hinfo : env.find? recFn = some (.recInfo info))
    (hmajor : e.getAppArgs[info.getMajorIdx]? = some major)
    (hk : info.k = false)
    (hwhnf : whnf major = pure (.lit (.natVal n)))
    (hrule : getRecRuleFor info (.natLitToConstructor n) = some rule)
    (hfields : rule.nfields ≤ (Expr.natLitToConstructor n).getAppArgs.size)
    (hlevels : levels.length = info.levelParams.length) :
    inductiveReduceRec env e whnf inferType isDefEq =
      pure (some (applyRecursorRule info rule levels e.getAppArgs
        (Expr.natLitToConstructor n).getAppArgs)) := by
  have hnfields : ¬(Expr.natLitToConstructor n).getAppArgs.size <
      rule.nfields := Nat.not_lt_of_ge hfields
  simp [inductiveReduceRec, hfn, hinfo, hmajor, hk, hwhnf, hrule,
    hnfields, hlevels]

/-- Execute the String-literal branch, retaining its second WHNF callback on
the expanded constructor representation. -/
theorem inductiveReduceRec_eq_some_applyRecursorRule_of_strLit
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (env : Environment) (whnf inferType : Expr → m Expr)
    (isDefEq : Expr → Expr → m Bool)
    {e major ctorMajor : Expr} {recFn : Name} {levels : List Level}
    {info : RecursorVal} {rule : RecursorRule} {str : String}
    (hfn : e.getAppFn = .const recFn levels)
    (hinfo : env.find? recFn = some (.recInfo info))
    (hmajor : e.getAppArgs[info.getMajorIdx]? = some major)
    (hk : info.k = false)
    (hwhnf : whnf major = pure (.lit (.strVal str)))
    (hstr : whnf (.strLitToConstructor str) = pure ctorMajor)
    (hrule : getRecRuleFor info ctorMajor = some rule)
    (hfields : rule.nfields ≤ ctorMajor.getAppArgs.size)
    (hlevels : levels.length = info.levelParams.length) :
    inductiveReduceRec env e whnf inferType isDefEq =
      pure (some (applyRecursorRule info rule levels e.getAppArgs
        ctorMajor.getAppArgs)) := by
  have hnfields : ¬ctorMajor.getAppArgs.size < rule.nfields :=
    Nat.not_lt_of_ge hfields
  simp [inductiveReduceRec, hfn, hinfo, hmajor, hk, hwhnf, hstr, hrule,
    hnfields, hlevels]

/-- Execute the ordinary constructor branch from an exact constructor
lookup.  Constructor recognition discharges both the literal split and the
structure-eta callback path for arbitrary completed spines, including bare
nullary constructors. -/
theorem inductiveReduceRec_eq_some_applyRecursorRule_of_constructor
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (env : Environment) (whnf inferType : Expr → m Expr)
    (isDefEq : Expr → Expr → m Bool)
    {e major : Expr} {recFn ctor : Name}
    {levels ctorLevels : List Level} {ctorArgs : List Expr}
    {info : RecursorVal} {ctorInfo : ConstructorVal}
    {rule : RecursorRule}
    (hfn : e.getAppFn = .const recFn levels)
    (hinfo : env.find? recFn = some (.recInfo info))
    (hmajor : e.getAppArgs[info.getMajorIdx]? = some major)
    (hk : info.k = false)
    (hwhnf : whnf major =
      pure (Expr.mkAppList (.const ctor ctorLevels) ctorArgs))
    (hctor : env.find? ctor = some (.ctorInfo ctorInfo))
    (hrule : getRecRuleFor info
      (Expr.mkAppList (.const ctor ctorLevels) ctorArgs) = some rule)
    (hfields : rule.nfields ≤ ctorArgs.length)
    (hlevels : levels.length = info.levelParams.length) :
    inductiveReduceRec env e whnf inferType isDefEq =
      pure (some (applyRecursorRule info rule levels e.getAppArgs
        (Expr.mkAppList (.const ctor ctorLevels) ctorArgs).getAppArgs)) := by
  exact inductiveReduceRec_eq_some_applyRecursorRule_of_nonliteral env whnf
    inferType isDefEq hfn hinfo hmajor hk hwhnf
      (mkAppList_const_ne_lit ctor ctorLevels ctorArgs)
      (toCtorWhenStruct_eq_pure_of_isConstructorApp env whnf inferType
        (by rw [isConstructorApp?_mkAppList_of_find_ctor env ctorLevels
          ctorArgs hctor]; rfl))
      hrule (by
        rw [← Array.length_toList, getAppArgs_mkAppList_const]
        exact hfields) hlevels

/-- Semantic result wrapper for the exact constructor-lookup branch. -/
theorem inductiveReduceRec_result_trExpr_of_constructor
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (env : Environment) (whnf inferType : Expr → m Expr)
    (isDefEq : Expr → Expr → m Bool)
    {e major : Expr} {recFn ctor : Name}
    {levels ctorLevels : List Level} {ctorArgs : List Expr}
    {info : RecursorVal} {ctorInfo : ConstructorVal}
    {rule : RecursorRule}
    (hfn : e.getAppFn = .const recFn levels)
    (hinfo : env.find? recFn = some (.recInfo info))
    (hmajor : e.getAppArgs[info.getMajorIdx]? = some major)
    (hk : info.k = false)
    (hwhnf : whnf major =
      pure (Expr.mkAppList (.const ctor ctorLevels) ctorArgs))
    (hctor : env.find? ctor = some (.ctorInfo ctorInfo))
    (hrule : getRecRuleFor info
      (Expr.mkAppList (.const ctor ctorLevels) ctorArgs) = some rule)
    (hfields : rule.nfields ≤ ctorArgs.length)
    (hlevels : levels.length = info.levelParams.length)
    {venv : VEnv} {Us : List Name} {Δ : VLCtx} {target : VExpr}
    (hout : TrExpr venv Us Δ
      (applyRecursorRule info rule levels e.getAppArgs
        (Expr.mkAppList (.const ctor ctorLevels) ctorArgs).getAppArgs)
      target) :
    ∃ result,
      inductiveReduceRec env e whnf inferType isDefEq = pure (some result) ∧
      TrExpr venv Us Δ result target := by
  refine ⟨_, ?_, hout⟩
  exact inductiveReduceRec_eq_some_applyRecursorRule_of_constructor env whnf
    inferType isDefEq hfn hinfo hmajor hk hwhnf hctor hrule hfields hlevels

/-! ### Exact ordinary failure branches -/

/-- A non-constant application head cannot be a recursor. -/
theorem inductiveReduceRec_eq_none_of_nonconst
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (env : Environment) (whnf inferType : Expr → m Expr)
    (isDefEq : Expr → Expr → m Bool) {e : Expr}
    (hfn : ∀ name levels, e.getAppFn ≠ .const name levels) :
    inductiveReduceRec env e whnf inferType isDefEq = pure none := by
  cases heq : e.getAppFn <;> simp [inductiveReduceRec, heq]
  rename_i name levels
  exact (hfn name levels heq).elim

/-- A constant head absent from the environment cannot reduce as a
recursor. -/
theorem inductiveReduceRec_eq_none_of_missing_recursor
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (env : Environment) (whnf inferType : Expr → m Expr)
    (isDefEq : Expr → Expr → m Bool)
    {e : Expr} {recFn : Name} {levels : List Level}
    (hfn : e.getAppFn = .const recFn levels)
    (hinfo : env.find? recFn = none) :
    inductiveReduceRec env e whnf inferType isDefEq = pure none := by
  simp [inductiveReduceRec, hfn, hinfo]

/-- More generally, a constant whose environment entry is not a recursor
takes the same early exit, regardless of which other declaration kind is
stored under that name. -/
theorem inductiveReduceRec_eq_none_of_not_recursor
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (env : Environment) (whnf inferType : Expr → m Expr)
    (isDefEq : Expr → Expr → m Bool)
    {e : Expr} {recFn : Name} {levels : List Level}
    (hfn : e.getAppFn = .const recFn levels)
    (hinfo : ∀ info, env.find? recFn ≠ some (.recInfo info)) :
    inductiveReduceRec env e whnf inferType isDefEq = pure none := by
  cases heq : env.find? recFn with
  | none => simp [inductiveReduceRec, hfn, heq]
  | some ci =>
    cases ci <;> simp [inductiveReduceRec, hfn, heq]
    rename_i info
    exact (hinfo info heq).elim

/-- A known recursor with no argument at its major index takes the early
`none` exit before invoking any callback. -/
theorem inductiveReduceRec_eq_none_of_missing_major
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (env : Environment) (whnf inferType : Expr → m Expr)
    (isDefEq : Expr → Expr → m Bool)
    {e : Expr} {recFn : Name} {levels : List Level} {info : RecursorVal}
    (hfn : e.getAppFn = .const recFn levels)
    (hinfo : env.find? recFn = some (.recInfo info))
    (hmajor : e.getAppArgs[info.getMajorIdx]? = none) :
    inductiveReduceRec env e whnf inferType isDefEq = pure none := by
  simp [inductiveReduceRec, hfn, hinfo, hmajor]

/-- The ordinary nonliteral branch returns `none` when the normalized major
has no rule in the selected recursor. -/
theorem inductiveReduceRec_eq_none_of_nonliteral_no_rule
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (env : Environment) (whnf inferType : Expr → m Expr)
    (isDefEq : Expr → Expr → m Bool)
    {e major whnfMajor ctorMajor : Expr} {recFn : Name}
    {levels : List Level} {info : RecursorVal}
    (hfn : e.getAppFn = .const recFn levels)
    (hinfo : env.find? recFn = some (.recInfo info))
    (hmajor : e.getAppArgs[info.getMajorIdx]? = some major)
    (hk : info.k = false)
    (hwhnf : whnf major = pure whnfMajor)
    (hnotLit : ∀ lit, whnfMajor ≠ .lit lit)
    (hstruct : toCtorWhenStruct env whnf inferType info.getMajorInduct
      whnfMajor = pure ctorMajor)
    (hrule : getRecRuleFor info ctorMajor = none) :
    inductiveReduceRec env e whnf inferType isDefEq = pure none := by
  cases hwm : whnfMajor
  case lit lit => exact (hnotLit lit hwm).elim
  all_goals
    rw [hwm] at hwhnf hstruct
    simp [inductiveReduceRec, hfn, hinfo, hmajor, hk, hwhnf, hstruct,
      hrule]

/-- A selected ordinary rule with more fields than the constructor spine
takes the field-underflow exit. -/
theorem inductiveReduceRec_eq_none_of_nonliteral_field_underflow
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (env : Environment) (whnf inferType : Expr → m Expr)
    (isDefEq : Expr → Expr → m Bool)
    {e major whnfMajor ctorMajor : Expr} {recFn : Name}
    {levels : List Level} {info : RecursorVal} {rule : RecursorRule}
    (hfn : e.getAppFn = .const recFn levels)
    (hinfo : env.find? recFn = some (.recInfo info))
    (hmajor : e.getAppArgs[info.getMajorIdx]? = some major)
    (hk : info.k = false)
    (hwhnf : whnf major = pure whnfMajor)
    (hnotLit : ∀ lit, whnfMajor ≠ .lit lit)
    (hstruct : toCtorWhenStruct env whnf inferType info.getMajorInduct
      whnfMajor = pure ctorMajor)
    (hrule : getRecRuleFor info ctorMajor = some rule)
    (hfields : ctorMajor.getAppArgs.size < rule.nfields) :
    inductiveReduceRec env e whnf inferType isDefEq = pure none := by
  cases hwm : whnfMajor
  case lit lit => exact (hnotLit lit hwm).elim
  all_goals
    rw [hwm] at hwhnf hstruct
    simp [inductiveReduceRec, hfn, hinfo, hmajor, hk, hwhnf, hstruct,
      hrule, hfields]

/-- Once an ordinary rule has been selected, a universe-argument count
mismatch returns `none` whether or not the earlier field guard also fails. -/
theorem inductiveReduceRec_eq_none_of_nonliteral_level_mismatch
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (env : Environment) (whnf inferType : Expr → m Expr)
    (isDefEq : Expr → Expr → m Bool)
    {e major whnfMajor ctorMajor : Expr} {recFn : Name}
    {levels : List Level} {info : RecursorVal} {rule : RecursorRule}
    (hfn : e.getAppFn = .const recFn levels)
    (hinfo : env.find? recFn = some (.recInfo info))
    (hmajor : e.getAppArgs[info.getMajorIdx]? = some major)
    (hk : info.k = false)
    (hwhnf : whnf major = pure whnfMajor)
    (hnotLit : ∀ lit, whnfMajor ≠ .lit lit)
    (hstruct : toCtorWhenStruct env whnf inferType info.getMajorInduct
      whnfMajor = pure ctorMajor)
    (hrule : getRecRuleFor info ctorMajor = some rule)
    (hlevels : levels.length ≠ info.levelParams.length) :
    inductiveReduceRec env e whnf inferType isDefEq = pure none := by
  cases hwm : whnfMajor
  case lit lit => exact (hnotLit lit hwm).elim
  all_goals
    rw [hwm] at hwhnf hstruct
    simp [inductiveReduceRec, hfn, hinfo, hmajor, hk, hwhnf, hstruct,
      hrule, hlevels]

/-- The sole successful-branch obligation left by exhaustive ordinary
recursor analysis.  It is deliberately phrased at the actual selected rule:
failure branches require no semantic evidence, while a successful branch
retains both the strict original-major translation and the weak normalized
major translation needed by head injectivity. -/
structure inductiveReduceRec.SelectedBranchWF
    (c : VContext) (s : VState) (e : Expr) (e' : VExpr)
    (major : Expr) (levels : List Level) (info : RecursorVal) : Prop where
  apply : ∀ {state major' majorV rule},
    s ≤ state →
    c.TrExprS major majorV →
    c.FVarsBelow e major' →
    c.TrExpr major' majorV →
    getRecRuleFor info major' = some rule →
    rule.nfields ≤ major'.getAppArgs.size →
    levels.length = info.levelParams.length →
    c.FVarsBelow e
        (applyRecursorRule info rule levels e.getAppArgs
          major'.getAppArgs) ∧
      c.TrExpr
        (applyRecursorRule info rule levels e.getAppArgs
          major'.getAppArgs) e'

/-- Exhaust the live callback and all ordinary reducer guards when K and
structure conversion are statically inactive.  The caller is responsible
only for a branch that actually selects a sufficiently saturated rule with
the correct universe arity; all WHNF shapes, both literal conversions, and
every `none` exit are discharged here.

The selected-branch premise receives both the strict translation of the
original major and the weak translation produced by `whnf.WF`.  This is the
precise boundary at which an inductive-head injectivity result can align the
runtime constructor parameters with the recursor parameters. -/
theorem inductiveReduceRec.WF_of_k_false_of_not_structure
    {c : VContext} {s : VState} {e : Expr} {e' : VExpr}
    {recFn : Name} {levels : List Level} {info : RecursorVal}
    {major : Expr}
    (he : c.TrExprS e e')
    (hfn : e.getAppFn = .const recFn levels)
    (hinfo : c.env.find? recFn = some (.recInfo info))
    (hmajor : e.getAppArgs[info.getMajorIdx]? = some major)
    (hk : info.k = false)
    (hstruct : c.env.isNonRecStructure info.getMajorInduct = false)
    (happly : inductiveReduceRec.SelectedBranchWF
      c s e e' major levels info) :
    RecM.WF c s
      (inductiveReduceRec c.env e whnf inferType isDefEq) fun oe _ =>
        ∀ result, oe = some result →
          c.FVarsBelow e result ∧ c.TrExpr result e' := by
  obtain ⟨majorV, hmajorTr⟩ := he.getAppArg hmajor
  have finish {state : VState} {major' : Expr}
      (hle : s ≤ state)
      (hbelow : c.FVarsBelow e major')
      (htr : c.TrExpr major' majorV) :
      RecM.WF c state
        (do
          let some rule := getRecRuleFor info major' | return none
          let majorArgs := major'.getAppArgs
          if rule.nfields > majorArgs.size then return none
          if levels.length != info.levelParams.length then return none
          return some (applyRecursorRule info rule levels e.getAppArgs
            majorArgs)) fun oe _ =>
              ∀ result, oe = some result →
                c.FVarsBelow e result ∧ c.TrExpr result e' := by
    cases hrule : getRecRuleFor info major' with
    | none =>
      exact .pure nofun
    | some rule =>
      simp only
      split
      · exact .pure nofun
      · rename_i hfields
        split
        · exact .pure nofun
        · rename_i hlevels
          apply RecM.WF.pure
          intro result hresult
          cases hresult
          exact happly.apply hle hmajorTr hbelow htr hrule
            (Nat.le_of_not_gt hfields) (by simpa using hlevels)
  have nonlit {state : VState} {normalized : Expr}
      (hle : s ≤ state)
      (hbelow : c.FVarsBelow e normalized)
      (htr : c.TrExpr normalized majorV) :
      RecM.WF c state
        (do
          let major ← toCtorWhenStruct c.env whnf inferType
            info.getMajorInduct normalized
          let some rule := getRecRuleFor info major | return none
          let majorArgs := major.getAppArgs
          if rule.nfields > majorArgs.size then return none
          if levels.length != info.levelParams.length then return none
          return some (applyRecursorRule info rule levels e.getAppArgs
            majorArgs)) fun oe _ =>
              ∀ result, oe = some result →
                c.FVarsBelow e result ∧ c.TrExpr result e' := by
    rw [toCtorWhenStruct_eq_pure_of_not_nonRecStructure
      c.env whnf inferType hstruct]
    exact finish hle hbelow htr
  unfold inductiveReduceRec
  simp only [hfn, hinfo, hmajor, hk, Bool.false_eq_true, ↓reduceIte]
  refine (whnf.WF hmajorTr).bind fun normalized state hle hnormalized => ?_
  cases normalized <;> try simp only
  all_goals first
    | exact nonlit hle
        ((FVarsBelow.getAppArg hmajor).trans hnormalized.1) hnormalized.2
    | skip
  rename_i lit
  cases lit with
  | natVal n =>
    obtain ⟨literalV, hlitS, hlitEq⟩ := hnormalized.2
    let .lit _ hctorS := hlitS
    apply finish hle
    · intro P hP heP
      exact FVarsIn.natLitToConstructor
    · exact ⟨literalV, hctorS, hlitEq⟩
  | strVal str =>
    obtain ⟨literalV, hlitS, hlitEq⟩ := hnormalized.2
    let .lit _ hctorS := hlitS
    refine (whnf.WF hctorS).bind fun expanded state' hle' hexpanded => ?_
    apply finish (hle.trans hle')
    · exact FVarsBelow.trans
        (fun _ _ _ => FVarsIn.strLitToConstructor) hexpanded.1
    · exact hexpanded.2.defeq c.Ewf c.Δwf hlitEq

/--
info: 'Lean4Lean.TypeChecker.Inner.inductiveReduceRec.WF_of_k_false_of_not_structure' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.inductiveReduceRec.WF_of_k_false_of_not_structure

/-! ### `reduceRecursor` quotient gate -/

/-- When quotient support is not initialized, the actual `RecM`
`reduceRecursor` wrapper returns exactly the pointwise result and state of
`inductiveReduceRec`. -/
theorem reduceRecursor_run_eq_of_quotInit_false
    (methods : TypeChecker.Methods) (context : TypeChecker.Context)
    (state : TypeChecker.State) {e : Expr} {result : Option Expr}
    {state' : TypeChecker.State}
    (hquot : context.env.quotInit = false)
    (hind :
      inductiveReduceRec context.env e whnf inferType isDefEq
          methods context state =
        .ok (result, state')) :
    reduceRecursor e methods context state = .ok (result, state') := by
  unfold reduceRecursor
  simp only [ReaderT.bind, StateT.bind, Except.bind, Bind.bind]
  rw [show (liftM TypeChecker.getEnv :
      TypeChecker.RecM Environment) methods context state =
        .ok (context.env, state) by rfl]
  simp only []
  rw [hquot]
  simp only [Bool.false_eq_true, ↓reduceIte, ReaderT.bind, StateT.bind,
    Except.bind, Bind.bind]
  rw [hind]
  cases result <;> rfl

/-- With quotient support enabled, a successful quotient reduction wins and
the inductive reducer is not evaluated. -/
theorem reduceRecursor_run_eq_of_quot_some
    (methods : TypeChecker.Methods) (context : TypeChecker.Context)
    (state : TypeChecker.State) {e result : Expr}
    {state' : TypeChecker.State}
    (hquot : context.env.quotInit = true)
    (hquotRun : quotReduceRec e whnf methods context state =
      .ok (some result, state')) :
    reduceRecursor e methods context state = .ok (some result, state') := by
  unfold reduceRecursor
  simp only [ReaderT.bind, StateT.bind, Except.bind, Bind.bind]
  rw [show (liftM TypeChecker.getEnv :
      TypeChecker.RecM Environment) methods context state =
        .ok (context.env, state) by rfl]
  simp only []
  rw [hquot]
  simp only [↓reduceIte, ReaderT.bind, StateT.bind,
    Except.bind, Bind.bind]
  rw [hquotRun]
  rfl

/-- If quotient reduction declines, its output state is threaded into the
inductive reducer and the wrapper returns that second phase's exact result. -/
theorem reduceRecursor_run_eq_of_quot_none
    (methods : TypeChecker.Methods) (context : TypeChecker.Context)
    (state : TypeChecker.State) {e : Expr} {result : Option Expr}
    {quotState state' : TypeChecker.State}
    (hquot : context.env.quotInit = true)
    (hquotRun : quotReduceRec e whnf methods context state =
      .ok (none, quotState))
    (hind :
      inductiveReduceRec context.env e whnf inferType isDefEq
          methods context quotState =
        .ok (result, state')) :
    reduceRecursor e methods context state = .ok (result, state') := by
  unfold reduceRecursor
  simp only [ReaderT.bind, StateT.bind, Except.bind, Bind.bind]
  rw [show (liftM TypeChecker.getEnv :
      TypeChecker.RecM Environment) methods context state =
        .ok (context.env, state) by rfl]
  simp only []
  rw [hquot]
  simp only [↓reduceIte, ReaderT.bind, StateT.bind,
    Except.bind, Bind.bind]
  rw [hquotRun]
  simp only []
  simp only [ReaderT.bind, StateT.bind, Except.bind, Bind.bind]
  rw [hind]
  cases result <;> rfl

/-! ### Live soundness adapters for the recursor wrapper -/

/-- Replay one successful `Quot.lift` reduction in the translated Theory.
The proof recovers the exact eliminator and constructor spines from strict
translation, derives their quotient-type equality by unique typing, invokes
the registered quotient equation through `quotLift_mk_reduction`, and then
reattaches every host argument trailing the major premise. -/
theorem quotLift_result_trExpr
    {c : VContext} {e mk : Expr} {e' major' : VExpr}
    {hostLevels : List Level}
    (hquot : c.env.quotInit = true)
    (hinj : c.venv.QuotAppInj)
    (he : c.TrExprS e e')
    (hfn : e.getAppFn = .const ``Quot.lift hostLevels)
    (hmajorBound : 5 < e.getAppArgs.size)
    (hmajorTr : c.TrExprS e.getAppArgs[5] major')
    (hmkTr : c.TrExpr mk major')
    (hmkShape : mk.isAppOfArity ``Quot.mk 3 = true) :
    c.TrExpr
      (mkAppRange
        (.app e.getAppArgs[3]! mk.appArg!) 6
        e.getAppArgs.size e.getAppArgs) e' := by
  have hobjects := c.trenv.quotObjects hquot
  have hargsSix : 6 ≤ e.getAppArgs.size := by omega
  have hargsListSix : 6 ≤ e.getAppArgsList.length := by
    simpa [← Expr.getAppArgs_toList] using hargsSix
  obtain ⟨_, hstack⟩ := AppStack.build
    (e.mkAppList_getAppArgsList ▸ he)
  rw [hfn] at hstack
  obtain ⟨_, _, hprefixStack, _⟩ := hstack.splitAt 6
  have hheadTr := hprefixStack.tr
  let .const (ci := ci) (us' := theoryLevels)
      hlookup hlevelsMap hhostLevelsLen := hheadTr
  rw [hobjects.2.2.1] at hlookup
  cases hlookup
  have htheoryLevelsLen : theoryLevels.length = 2 := by
    have hmapLen := Lean4Lean.List.Forall₂.length_eq
      (List.mapM_eq_some.1 hlevelsMap)
    simpa [quotLiftConst] using hmapLen.symm.trans hhostLevelsLen
  have lengthTwo : ∀ {xs : List VLevel}, xs.length = 2 →
      ∃ u v, xs = [u, v] := by
    intro xs hlen
    cases xs with
    | nil => simp at hlen
    | cons u xs =>
      cases xs with
      | nil => simp at hlen
      | cons v xs =>
        cases xs with
        | nil => exact ⟨u, v, rfl⟩
        | cons _ _ => simp at hlen
  obtain ⟨u, v, hlevels⟩ := lengthTwo htheoryLevelsLen
  subst theoryLevels
  have hlevelsWF : ∀ level ∈ [u, v], level.WF c.lparams.length :=
    VLevel.WF.of_mapM_ofLevel hlevelsMap
  have hu : u.WF c.lparams.length := hlevelsWF u (by simp)
  have hv : v.WF c.lparams.length := hlevelsWF v (by simp)
  have hliftHead : c.HasType (.const ``Quot.lift [u, v])
      (quotLiftConst.type.instL [u, v]) :=
    VEnv.HasType.const hobjects.2.2.1 hlevelsWF
      (by simp [quotLiftConst])
  let As := (VExpr.telN 6 quotLiftConst.type).map
    (VExpr.instL [u, v])
  let C := (VExpr.dropN 6 quotLiftConst.type).instL [u, v]
  have hliftTypeShape : quotLiftConst.type.instL [u, v] =
      VExpr.forallN As C := by
    dsimp [As, C]
    rw [← VExpr.instL_forallN, VExpr.forallN_telN_dropN]
  rw [hliftTypeShape] at hliftHead
  have hprefixLength : (e.getAppArgsList.take 6).length = As.length := by
    simp [As, quotLiftConst, VExpr.telN, List.length_take, hargsListSix]
  obtain ⟨front, hfrontTr, hliftSpine, hprefixFull⟩ :=
    hprefixStack.toSpineWF c.Ewf c.Δwf hliftHead hprefixLength
  have hfrontTheoryLen : front.length = 6 := by
    rw [← Lean4Lean.List.Forall₂.length_eq hfrontTr]
    simp [List.length_take, hargsListSix]
  have lengthSix : ∀ {xs : List VExpr}, xs.length = 6 →
      ∃ α r β f coh q, xs = [α, r, β, f, coh, q] := by
    intro xs hlen
    cases xs with
    | nil => simp at hlen
    | cons α xs =>
      cases xs with
      | nil => simp at hlen
      | cons r xs =>
        cases xs with
        | nil => simp at hlen
        | cons β xs =>
          cases xs with
          | nil => simp at hlen
          | cons f xs =>
            cases xs with
            | nil => simp at hlen
            | cons coh xs =>
              cases xs with
              | nil => simp at hlen
              | cons q xs =>
                cases xs with
                | nil => exact ⟨α, r, β, f, coh, q, rfl⟩
                | cons _ _ => simp at hlen
  obtain ⟨α, r, β, f, coh, q, hfrontTheory⟩ :=
    lengthSix hfrontTheoryLen
  subst front
  rw [← hliftTypeShape] at hliftSpine
  have hfunGet : (e.getAppArgsList.take 6)[3]? =
      some e.getAppArgs[3]! := by
    rw [List.getElem?_take_of_lt (by omega)]
    rw [← Expr.getAppArgs_toList, Array.getElem?_toList]
    rw [getElem!_pos e.getAppArgs 3 (by omega)]
    exact Array.getElem?_eq_getElem (by omega)
  obtain ⟨f', hfGet, hfunTr⟩ :=
    Lean4Lean.List.Forall₂.getElem?_left hfrontTr hfunGet
  simp at hfGet
  subst f'
  have hmajorGet : (e.getAppArgsList.take 6)[5]? =
      some e.getAppArgs[5] := by
    rw [List.getElem?_take_of_lt (by omega)]
    rw [← Expr.getAppArgs_toList, Array.getElem?_toList]
    exact Array.getElem?_eq_getElem hmajorBound
  obtain ⟨q', hqGet, hmajorTr'⟩ :=
    Lean4Lean.List.Forall₂.getElem?_left hfrontTr hmajorGet
  simp at hqGet
  subst q'
  have hmajorEq : c.IsDefEqU major' q :=
    hmajorTr.uniq c.Ewf (.refl c.Ewf c.Δwf) hmajorTr'
  obtain ⟨mkTheory, hmkStrict, hmkEq⟩ := hmkTr
  have hmkqTheory : c.IsDefEqU mkTheory q :=
    hmkEq.trans c.Ewf c.Δwf hmajorEq
  obtain ⟨mkHostLevels, mkAlpha, mkRel, rep, hmkHost⟩ :=
    Expr.eq_app3_of_isAppOfArity hmkShape
  subst mk
  obtain ⟨_, hmkStack⟩ := AppStack.build
    (as := [mkAlpha, mkRel, rep]) (by
      simpa [Expr.mkAppList] using hmkStrict)
  have hmkHeadTr := hmkStack.tr
  let .const (ci := mkCi) (us' := mkTheoryLevels)
      hmkLookup hmkLevelsMap hmkHostLevelsLen := hmkHeadTr
  rw [hobjects.2.2.2.1] at hmkLookup
  cases hmkLookup
  have hmkTheoryLevelsLen : mkTheoryLevels.length = 1 := by
    have hmapLen := Lean4Lean.List.Forall₂.length_eq
      (List.mapM_eq_some.1 hmkLevelsMap)
    simpa [quotMkConst] using hmapLen.symm.trans hmkHostLevelsLen
  have lengthOne : ∀ {xs : List VLevel}, xs.length = 1 →
      ∃ u, xs = [u] := by
    intro xs hlen
    cases xs with
    | nil => simp at hlen
    | cons u xs =>
      cases xs with
      | nil => exact ⟨u, rfl⟩
      | cons _ _ => simp at hlen
  obtain ⟨u', hmkLevels⟩ := lengthOne hmkTheoryLevelsLen
  subst mkTheoryLevels
  have hmkLevelsWF : ∀ level ∈ [u'],
      level.WF c.lparams.length :=
    VLevel.WF.of_mapM_ofLevel hmkLevelsMap
  have hu' : u'.WF c.lparams.length := hmkLevelsWF u' (by simp)
  have hmkHead : c.HasType (.const ``Quot.mk [u'])
      (quotMkConst.type.instL [u']) :=
    VEnv.HasType.const hobjects.2.2.2.1 hmkLevelsWF
      (by simp [quotMkConst])
  let MkAs := (VExpr.telN 3 quotMkConst.type).map
    (VExpr.instL [u'])
  let MkC := (VExpr.dropN 3 quotMkConst.type).instL [u']
  have hmkTypeShape : quotMkConst.type.instL [u'] =
      VExpr.forallN MkAs MkC := by
    dsimp [MkAs, MkC]
    rw [← VExpr.instL_forallN, VExpr.forallN_telN_dropN]
  rw [hmkTypeShape] at hmkHead
  have hmkArgsLength : ([mkAlpha, mkRel, rep] : List Expr).length =
      MkAs.length := by
    simp [MkAs, quotMkConst, VExpr.telN]
  obtain ⟨mkArgs, hmkArgsTr, hmkSpine, hmkFull⟩ :=
    hmkStack.toSpineWF c.Ewf c.Δwf hmkHead hmkArgsLength
  have hmkTheoryArgsLen : mkArgs.length = 3 := by
    rw [← Lean4Lean.List.Forall₂.length_eq hmkArgsTr]
    rfl
  have lengthThree : ∀ {xs : List VExpr}, xs.length = 3 →
      ∃ α r a, xs = [α, r, a] := by
    intro xs hlen
    cases xs with
    | nil => simp at hlen
    | cons α xs =>
      cases xs with
      | nil => simp at hlen
      | cons r xs =>
        cases xs with
        | nil => simp at hlen
        | cons a xs =>
          cases xs with
          | nil => exact ⟨α, r, a, rfl⟩
          | cons _ _ => simp at hlen
  obtain ⟨α', r', a, hmkTheoryArgs⟩ := lengthThree hmkTheoryArgsLen
  subst mkArgs
  rw [← hmkTypeShape] at hmkSpine
  have hmkExact := hmkSpine.quotMk_exact
  have hrepGet : ([mkAlpha, mkRel, rep] : List Expr)[2]? = some rep := rfl
  obtain ⟨a', haGet, hrepTr⟩ :=
    Lean4Lean.List.Forall₂.getElem?_left hmkArgsTr hrepGet
  simp at haGet
  subst a'
  rw [← hmkTypeShape] at hmkHead
  have hmkFullEq : c.IsDefEqU
      (VExpr.appN (.const ``Quot.mk [u']) [α', r', a]) mkTheory :=
    hmkFull.uniq c.Ewf (.refl c.Ewf c.Δwf) hmkStrict
  have hmkqExact : c.IsDefEqU
      (VExpr.appN (.const ``Quot.mk [u']) [α', r', a]) q :=
    hmkFullEq.trans c.Ewf c.Δwf hmkqTheory
  have hmkTerm : c.HasType
      (VExpr.appN (.const ``Quot.mk [u']) [α', r', a])
      (VExpr.appN (.const ``Quot [u']) [α', r']) :=
    hmkExact.hasType_appN hmkHead
  have hqLift : c.HasType q
      (VExpr.appN (.const ``Quot [u]) [α, r]) :=
    hliftSpine.quotLift_major
  have hmkAtLift := hmkqExact.of_r c.Ewf c.Δwf hqLift
  have hqtype : c.IsDefEqU
      (VExpr.appN (.const ``Quot [u']) [α', r'])
      (VExpr.appN (.const ``Quot [u]) [α, r]) :=
    hmkTerm.uniqU c.Ewf c.Δwf hmkAtLift.hasType.1
  have hred := VEnv.quotLift_mk_reduction c.Ewf c.Δwf
    hinj hobjects hu hv hu' hliftSpine hmkExact hqtype hmkqExact
  obtain ⟨_, hredTyped⟩ := hred
  obtain ⟨_, _, hfTyped, haTyped⟩ :=
    hredTyped.hasType.2.app_inv c.Ewf c.Δwf
  have hbaseStrict : c.TrExprS
      (.app e.getAppArgs[3]! rep) (.app f a) :=
    .app hfTyped haTyped hfunTr hrepTr
  have hbaseWeak : c.TrExpr
      (.app e.getAppArgs[3]! rep)
      (VExpr.appN (.const ``Quot.lift [u, v])
        [α, r, β, f, coh, q]) :=
    ⟨_, hbaseStrict, ⟨_, hredTyped.symm⟩⟩
  have hfull : c.TrExprS
      (((Expr.const ``Quot.lift hostLevels).mkAppList
          (e.getAppArgsList.take 6)).mkAppList
        (e.getAppArgsList.drop 6)) e' := by
    rw [← Expr.mkAppList_append, List.take_append_drop]
    rw [← hfn, e.mkAppList_getAppArgsList]
    exact he
  have hrebuilt := TrExpr.rebuild_mkAppList c.Ewf c.Δwf
    hprefixFull hfull hbaseWeak
  change c.TrExpr
    (mkAppRange (.app e.getAppArgs[3]! rep) 6
      e.getAppArgs.size e.getAppArgs) e'
  rw [Expr.mkAppRange_suffix_eq_drop hargsSix,
    Expr.getAppArgs_toList]
  simpa using hrebuilt

/--
info: 'Lean4Lean.TypeChecker.Inner.quotLift_result_trExpr' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.quotLift_result_trExpr

/-- Replay one successful `Quot.ind` reduction in the translated Theory.
The constructor parameter alignment is recovered exactly as for
`Quot.lift`; the semantic endpoint is supplied by proof irrelevance through
`quotInd_mk_reduction`, then all trailing host arguments are reattached. -/
theorem quotInd_result_trExpr
    {c : VContext} {e mk : Expr} {e' major' : VExpr}
    {hostLevels : List Level}
    (hquot : c.env.quotInit = true)
    (hinj : c.venv.QuotAppInj)
    (he : c.TrExprS e e')
    (hfn : e.getAppFn = .const ``Quot.ind hostLevels)
    (hmajorBound : 4 < e.getAppArgs.size)
    (hmajorTr : c.TrExprS e.getAppArgs[4] major')
    (hmkTr : c.TrExpr mk major')
    (hmkShape : mk.isAppOfArity ``Quot.mk 3 = true) :
    c.TrExpr
      (mkAppRange
        (.app e.getAppArgs[3]! mk.appArg!) 5
        e.getAppArgs.size e.getAppArgs) e' := by
  have hobjects := c.trenv.quotObjects hquot
  have hargsFive : 5 ≤ e.getAppArgs.size := by omega
  have hargsListFive : 5 ≤ e.getAppArgsList.length := by
    simpa [← Expr.getAppArgs_toList] using hargsFive
  obtain ⟨_, hstack⟩ := AppStack.build
    (e.mkAppList_getAppArgsList ▸ he)
  rw [hfn] at hstack
  obtain ⟨_, _, hprefixStack, _⟩ := hstack.splitAt 5
  have hheadTr := hprefixStack.tr
  let .const (ci := ci) (us' := theoryLevels)
      hlookup hlevelsMap hhostLevelsLen := hheadTr
  rw [hobjects.2.1] at hlookup
  cases hlookup
  have htheoryLevelsLen : theoryLevels.length = 1 := by
    have hmapLen := Lean4Lean.List.Forall₂.length_eq
      (List.mapM_eq_some.1 hlevelsMap)
    simpa [quotIndConst] using hmapLen.symm.trans hhostLevelsLen
  have lengthOneLevel : ∀ {xs : List VLevel}, xs.length = 1 →
      ∃ u, xs = [u] := by
    intro xs hlen
    cases xs with
    | nil => simp at hlen
    | cons u xs =>
      cases xs with
      | nil => exact ⟨u, rfl⟩
      | cons _ _ => simp at hlen
  obtain ⟨u, hlevels⟩ := lengthOneLevel htheoryLevelsLen
  subst theoryLevels
  have hlevelsWF : ∀ level ∈ [u], level.WF c.lparams.length :=
    VLevel.WF.of_mapM_ofLevel hlevelsMap
  have hu : u.WF c.lparams.length := hlevelsWF u (by simp)
  have hindHead : c.HasType (.const ``Quot.ind [u])
      (quotIndConst.type.instL [u]) :=
    VEnv.HasType.const hobjects.2.1 hlevelsWF
      (by simp [quotIndConst])
  let As := (VExpr.telN 5 quotIndConst.type).map
    (VExpr.instL [u])
  let C := (VExpr.dropN 5 quotIndConst.type).instL [u]
  have hindTypeShape : quotIndConst.type.instL [u] =
      VExpr.forallN As C := by
    dsimp [As, C]
    rw [← VExpr.instL_forallN, VExpr.forallN_telN_dropN]
  rw [hindTypeShape] at hindHead
  have hprefixLength : (e.getAppArgsList.take 5).length = As.length := by
    simp [As, quotIndConst, VExpr.telN, List.length_take, hargsListFive]
  obtain ⟨front, hfrontTr, hindSpine, hprefixFull⟩ :=
    hprefixStack.toSpineWF c.Ewf c.Δwf hindHead hprefixLength
  have hfrontTheoryLen : front.length = 5 := by
    rw [← Lean4Lean.List.Forall₂.length_eq hfrontTr]
    simp [List.length_take, hargsListFive]
  have lengthFive : ∀ {xs : List VExpr}, xs.length = 5 →
      ∃ α r β p q, xs = [α, r, β, p, q] := by
    intro xs hlen
    cases xs with
    | nil => simp at hlen
    | cons α xs =>
      cases xs with
      | nil => simp at hlen
      | cons r xs =>
        cases xs with
        | nil => simp at hlen
        | cons β xs =>
          cases xs with
          | nil => simp at hlen
          | cons p xs =>
            cases xs with
            | nil => simp at hlen
            | cons q xs =>
              cases xs with
              | nil => exact ⟨α, r, β, p, q, rfl⟩
              | cons _ _ => simp at hlen
  obtain ⟨α, r, β, p, q, hfrontTheory⟩ :=
    lengthFive hfrontTheoryLen
  subst front
  rw [← hindTypeShape] at hindSpine
  have hfunGet : (e.getAppArgsList.take 5)[3]? =
      some e.getAppArgs[3]! := by
    rw [List.getElem?_take_of_lt (by omega)]
    rw [← Expr.getAppArgs_toList, Array.getElem?_toList]
    rw [getElem!_pos e.getAppArgs 3 (by omega)]
    exact Array.getElem?_eq_getElem (by omega)
  obtain ⟨p', hpGet, hfunTr⟩ :=
    Lean4Lean.List.Forall₂.getElem?_left hfrontTr hfunGet
  simp at hpGet
  subst p'
  have hmajorGet : (e.getAppArgsList.take 5)[4]? =
      some e.getAppArgs[4] := by
    rw [List.getElem?_take_of_lt (by omega)]
    rw [← Expr.getAppArgs_toList, Array.getElem?_toList]
    exact Array.getElem?_eq_getElem hmajorBound
  obtain ⟨q', hqGet, hmajorTr'⟩ :=
    Lean4Lean.List.Forall₂.getElem?_left hfrontTr hmajorGet
  simp at hqGet
  subst q'
  have hmajorEq : c.IsDefEqU major' q :=
    hmajorTr.uniq c.Ewf (.refl c.Ewf c.Δwf) hmajorTr'
  obtain ⟨mkTheory, hmkStrict, hmkEq⟩ := hmkTr
  have hmkqTheory : c.IsDefEqU mkTheory q :=
    hmkEq.trans c.Ewf c.Δwf hmajorEq
  obtain ⟨mkHostLevels, mkAlpha, mkRel, rep, hmkHost⟩ :=
    Expr.eq_app3_of_isAppOfArity hmkShape
  subst mk
  obtain ⟨_, hmkStack⟩ := AppStack.build
    (as := [mkAlpha, mkRel, rep]) (by
      simpa [Expr.mkAppList] using hmkStrict)
  have hmkHeadTr := hmkStack.tr
  let .const (ci := mkCi) (us' := mkTheoryLevels)
      hmkLookup hmkLevelsMap hmkHostLevelsLen := hmkHeadTr
  rw [hobjects.2.2.2.1] at hmkLookup
  cases hmkLookup
  have hmkTheoryLevelsLen : mkTheoryLevels.length = 1 := by
    have hmapLen := Lean4Lean.List.Forall₂.length_eq
      (List.mapM_eq_some.1 hmkLevelsMap)
    simpa [quotMkConst] using hmapLen.symm.trans hmkHostLevelsLen
  obtain ⟨u', hmkLevels⟩ := lengthOneLevel hmkTheoryLevelsLen
  subst mkTheoryLevels
  have hmkLevelsWF : ∀ level ∈ [u'],
      level.WF c.lparams.length :=
    VLevel.WF.of_mapM_ofLevel hmkLevelsMap
  have hu' : u'.WF c.lparams.length := hmkLevelsWF u' (by simp)
  have hmkHead : c.HasType (.const ``Quot.mk [u'])
      (quotMkConst.type.instL [u']) :=
    VEnv.HasType.const hobjects.2.2.2.1 hmkLevelsWF
      (by simp [quotMkConst])
  let MkAs := (VExpr.telN 3 quotMkConst.type).map
    (VExpr.instL [u'])
  let MkC := (VExpr.dropN 3 quotMkConst.type).instL [u']
  have hmkTypeShape : quotMkConst.type.instL [u'] =
      VExpr.forallN MkAs MkC := by
    dsimp [MkAs, MkC]
    rw [← VExpr.instL_forallN, VExpr.forallN_telN_dropN]
  rw [hmkTypeShape] at hmkHead
  have hmkArgsLength : ([mkAlpha, mkRel, rep] : List Expr).length =
      MkAs.length := by
    simp [MkAs, quotMkConst, VExpr.telN]
  obtain ⟨mkArgs, hmkArgsTr, hmkSpine, hmkFull⟩ :=
    hmkStack.toSpineWF c.Ewf c.Δwf hmkHead hmkArgsLength
  have hmkTheoryArgsLen : mkArgs.length = 3 := by
    rw [← Lean4Lean.List.Forall₂.length_eq hmkArgsTr]
    rfl
  have lengthThree : ∀ {xs : List VExpr}, xs.length = 3 →
      ∃ α r a, xs = [α, r, a] := by
    intro xs hlen
    cases xs with
    | nil => simp at hlen
    | cons α xs =>
      cases xs with
      | nil => simp at hlen
      | cons r xs =>
        cases xs with
        | nil => simp at hlen
        | cons a xs =>
          cases xs with
          | nil => exact ⟨α, r, a, rfl⟩
          | cons _ _ => simp at hlen
  obtain ⟨α', r', a, hmkTheoryArgs⟩ := lengthThree hmkTheoryArgsLen
  subst mkArgs
  rw [← hmkTypeShape] at hmkSpine
  have hmkExact := hmkSpine.quotMk_exact
  have hrepGet : ([mkAlpha, mkRel, rep] : List Expr)[2]? = some rep := rfl
  obtain ⟨a', haGet, hrepTr⟩ :=
    Lean4Lean.List.Forall₂.getElem?_left hmkArgsTr hrepGet
  simp at haGet
  subst a'
  rw [← hmkTypeShape] at hmkHead
  have hmkFullEq : c.IsDefEqU
      (VExpr.appN (.const ``Quot.mk [u']) [α', r', a]) mkTheory :=
    hmkFull.uniq c.Ewf (.refl c.Ewf c.Δwf) hmkStrict
  have hmkqExact : c.IsDefEqU
      (VExpr.appN (.const ``Quot.mk [u']) [α', r', a]) q :=
    hmkFullEq.trans c.Ewf c.Δwf hmkqTheory
  have hmkTerm : c.HasType
      (VExpr.appN (.const ``Quot.mk [u']) [α', r', a])
      (VExpr.appN (.const ``Quot [u']) [α', r']) :=
    hmkExact.hasType_appN hmkHead
  have hqInd : c.HasType q
      (VExpr.appN (.const ``Quot [u]) [α, r]) :=
    hindSpine.quotInd_components.2.2
  have hmkAtInd := hmkqExact.of_r c.Ewf c.Δwf hqInd
  have hqtype : c.IsDefEqU
      (VExpr.appN (.const ``Quot [u']) [α', r'])
      (VExpr.appN (.const ``Quot [u]) [α, r]) :=
    hmkTerm.uniqU c.Ewf c.Δwf hmkAtInd.hasType.1
  have hred := VEnv.quotInd_mk_reduction c.Ewf c.Δwf
    hinj hobjects hu hu' hindSpine hmkExact hqtype hmkqExact
  obtain ⟨_, hredTyped⟩ := hred
  obtain ⟨_, _, hpTyped, haTyped⟩ :=
    hredTyped.hasType.2.app_inv c.Ewf c.Δwf
  have hbaseStrict : c.TrExprS
      (.app e.getAppArgs[3]! rep) (.app p a) :=
    .app hpTyped haTyped hfunTr hrepTr
  have hbaseWeak : c.TrExpr
      (.app e.getAppArgs[3]! rep)
      (VExpr.appN (.const ``Quot.ind [u]) [α, r, β, p, q]) :=
    ⟨_, hbaseStrict, ⟨_, hredTyped.symm⟩⟩
  have hfull : c.TrExprS
      (((Expr.const ``Quot.ind hostLevels).mkAppList
          (e.getAppArgsList.take 5)).mkAppList
        (e.getAppArgsList.drop 5)) e' := by
    rw [← Expr.mkAppList_append, List.take_append_drop]
    rw [← hfn, e.mkAppList_getAppArgsList]
    exact he
  have hrebuilt := TrExpr.rebuild_mkAppList c.Ewf c.Δwf
    hprefixFull hfull hbaseWeak
  change c.TrExpr
    (mkAppRange (.app e.getAppArgs[3]! rep) 5
      e.getAppArgs.size e.getAppArgs) e'
  rw [Expr.mkAppRange_suffix_eq_drop hargsFive,
    Expr.getAppArgs_toList]
  simpa using hrebuilt

/--
info: 'Lean4Lean.TypeChecker.Inner.quotInd_result_trExpr' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.quotInd_result_trExpr

/-- Full live verifier contract for the `Quot.lift` branch.  A successful
runtime recognition of `Quot.mk` is replayed by `quotLift_result_trExpr`;
the same WHNF witness supplies the independent free-variable bound. -/
theorem quotReduceRec.WF_of_quotLift
    {c : VContext} {s : VState} {e : Expr} {e' : VExpr}
    {hostLevels : List Level}
    (hquot : c.env.quotInit = true)
    (hinj : c.venv.QuotAppInj)
    (he : c.TrExprS e e')
    (hfn : e.getAppFn = .const ``Quot.lift hostLevels) :
    RecM.WF c s (quotReduceRec e whnf) fun oe _ =>
      ∀ e₁, oe = some e₁ →
        c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  unfold quotReduceRec
  rw [hfn]
  simp only [beq_self_eq_true, ↓reduceIte]
  dsimp
  split
  · rename_i hmajorBound
    have hmajorGet : e.getAppArgs[5]? = some e.getAppArgs[5] :=
      Array.getElem?_eq_getElem hmajorBound
    obtain ⟨major', hmajorTr⟩ := he.getAppArg hmajorGet
    refine (whnf.WF hmajorTr).bind fun mk _ _ ⟨hmkBelow, hmkTr⟩ => ?_
    have hmkBelowE : c.FVarsBelow e mk :=
      (FVarsBelow.getAppArg hmajorGet).trans hmkBelow
    split
    · exact .pure nofun
    · rename_i hnotApp
      have hmkShape : mk.isAppOfArity ``Quot.mk 3 = true := by
        cases h : mk.isAppOfArity ``Quot.mk 3 <;> simp_all
      have happ : ∃ fn arg, mk = .app fn arg := by
        obtain ⟨levels, α, r, a, hshape⟩ :=
          Expr.eq_app3_of_isAppOfArity hmkShape
        exact ⟨_, _, hshape⟩
      have hbase : c.FVarsBelow e
          (Expr.app e.getAppArgs[3]! mk.appArg!) := by
        intro P hP heP
        exact ⟨FVarsBelow.getAppArg! (by omega) P hP heP,
          (hmkBelowE.appArg! happ) P hP heP⟩
      have hsem := quotLift_result_trExpr hquot hinj he hfn
        hmajorBound hmajorTr hmkTr hmkShape
      split
      · rename_i htrail
        exact .pure fun e₁ he₁ => by
          cases he₁
          exact ⟨hbase.mkAppRange_getAppArgs_suffix
            (by omega), hsem⟩
      · rename_i htrail
        have hargsSix : 6 ≤ e.getAppArgs.size := by omega
        have hsize : e.getAppArgs.size = 6 := by omega
        have hdrop : e.getAppArgs.toList.drop 6 = [] := by
          apply List.length_eq_zero_iff.1
          rw [List.length_drop]
          simp [hsize]
        have hrange :
            mkAppRange (Expr.app e.getAppArgs[3]! mk.appArg!) 6
              e.getAppArgs.size e.getAppArgs =
              Expr.app e.getAppArgs[3]! mk.appArg! := by
          rw [Expr.mkAppRange_suffix_eq_drop hargsSix, hdrop]
          rfl
        rw [hrange] at hsem
        exact .pure fun e₁ he₁ => by
          cases he₁
          exact ⟨hbase, hsem⟩
  · exact .pure nofun

/--
info: 'Lean4Lean.TypeChecker.Inner.quotReduceRec.WF_of_quotLift' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.quotReduceRec.WF_of_quotLift

/-- Full live verifier contract for the `Quot.ind` branch.  Its semantic
half is proof-irrelevant, while its free-variable half is the same selected
representative argument analysis used by `Quot.lift`. -/
theorem quotReduceRec.WF_of_quotInd
    {c : VContext} {s : VState} {e : Expr} {e' : VExpr}
    {hostLevels : List Level}
    (hquot : c.env.quotInit = true)
    (hinj : c.venv.QuotAppInj)
    (he : c.TrExprS e e')
    (hfn : e.getAppFn = .const ``Quot.ind hostLevels) :
    RecM.WF c s (quotReduceRec e whnf) fun oe _ =>
      ∀ e₁, oe = some e₁ →
        c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  unfold quotReduceRec
  rw [hfn]
  simp only [beq_self_eq_true, ↓reduceIte]
  dsimp
  split
  · rename_i hmajorBound
    have hmajorGet : e.getAppArgs[4]? = some e.getAppArgs[4] :=
      Array.getElem?_eq_getElem hmajorBound
    obtain ⟨major', hmajorTr⟩ := he.getAppArg hmajorGet
    refine (whnf.WF hmajorTr).bind fun mk _ _ ⟨hmkBelow, hmkTr⟩ => ?_
    have hmkBelowE : c.FVarsBelow e mk :=
      (FVarsBelow.getAppArg hmajorGet).trans hmkBelow
    split
    · exact .pure nofun
    · rename_i hnotApp
      have hmkShape : mk.isAppOfArity ``Quot.mk 3 = true := by
        cases h : mk.isAppOfArity ``Quot.mk 3 <;> simp_all
      have happ : ∃ fn arg, mk = .app fn arg := by
        obtain ⟨levels, α, r, a, hshape⟩ :=
          Expr.eq_app3_of_isAppOfArity hmkShape
        exact ⟨_, _, hshape⟩
      have hbase : c.FVarsBelow e
          (Expr.app e.getAppArgs[3]! mk.appArg!) := by
        intro P hP heP
        exact ⟨FVarsBelow.getAppArg! (by omega) P hP heP,
          (hmkBelowE.appArg! happ) P hP heP⟩
      have hsem := quotInd_result_trExpr hquot hinj he hfn
        hmajorBound hmajorTr hmkTr hmkShape
      split
      · rename_i htrail
        exact .pure fun e₁ he₁ => by
          cases he₁
          exact ⟨hbase.mkAppRange_getAppArgs_suffix
            (by omega), hsem⟩
      · rename_i htrail
        have hargsFive : 5 ≤ e.getAppArgs.size := by omega
        have hsize : e.getAppArgs.size = 5 := by omega
        have hdrop : e.getAppArgs.toList.drop 5 = [] := by
          apply List.length_eq_zero_iff.1
          rw [List.length_drop]
          simp [hsize]
        have hrange :
            mkAppRange (Expr.app e.getAppArgs[3]! mk.appArg!) 5
              e.getAppArgs.size e.getAppArgs =
              Expr.app e.getAppArgs[3]! mk.appArg! := by
          rw [Expr.mkAppRange_suffix_eq_drop hargsFive, hdrop]
          rfl
        rw [hrange] at hsem
        exact .pure fun e₁ he₁ => by
          cases he₁
          exact ⟨hbase, hsem⟩
  · exact .pure nofun

/--
info: 'Lean4Lean.TypeChecker.Inner.quotReduceRec.WF_of_quotInd' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.quotReduceRec.WF_of_quotInd

/-- Exhaustive live quotient-reducer contract.  The two recognized heads use
their semantic proofs above; every other expression head returns `none` and
therefore satisfies the successful-result postcondition vacuously. -/
theorem quotReduceRec.WF
    {c : VContext} {s : VState} {e : Expr} {e' : VExpr}
    (hquot : c.env.quotInit = true)
    (hinj : c.venv.QuotAppInj)
    (he : c.TrExprS e e') :
    RecM.WF c s (quotReduceRec e whnf) fun oe _ =>
      ∀ e₁, oe = some e₁ →
        c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  cases hhead : e.getAppFn with
  | const name levels =>
    by_cases hlift : name = ``Quot.lift
    · subst name
      exact quotReduceRec.WF_of_quotLift hquot hinj he hhead
    · by_cases hind : name = ``Quot.ind
      · subst name
        exact quotReduceRec.WF_of_quotInd hquot hinj he hhead
      · unfold quotReduceRec
        rw [hhead]
        simp [hlift, hind]
        exact .pure nofun
  | _ =>
    unfold quotReduceRec
    rw [hhead]
    exact .pure nofun

/--
info: 'Lean4Lean.TypeChecker.Inner.quotReduceRec.WF' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.quotReduceRec.WF

/-- Quotient reduction cannot introduce free variables.  Its function and
trailing arguments are selected from the original redex, while the quotient
representative is selected from the WHNF of the major argument; `whnf.WF`
supplies exactly the latter monotonicity step.  This closes the syntactic half
of quotient-reducer soundness independently of its Theory equation. -/
theorem quotReduceRec.WF_fvarsBelow
    {c : VContext} {s : VState} {e : Expr} {e' : VExpr}
    (he : c.TrExprS e e') :
    RecM.WF c s (quotReduceRec e whnf) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.FVarsBelow e e₁ := by
  have contWF (mkPos argPos : Nat) (hargPos : argPos < mkPos) :
      RecM.WF c s
        (do
          let args := e.getAppArgs
          if h : mkPos < args.size then
            let mk ← whnf args[mkPos]
            if !mk.isAppOfArity ``Quot.mk 3 then return none
            let mut r := Expr.app args[argPos]! mk.appArg!
            let elimArity := mkPos + 1
            if elimArity < args.size then
              r := mkAppRange r elimArity args.size args
            return some r
          else
            return none) fun oe _ =>
              ∀ e₁, oe = some e₁ → c.FVarsBelow e e₁ := by
    dsimp
    split
    · rename_i hmkPos
      have hmajorGet : e.getAppArgs[mkPos]? =
          some e.getAppArgs[mkPos] :=
        Array.getElem?_eq_getElem hmkPos
      obtain ⟨major', hmajorTr⟩ := he.getAppArg hmajorGet
      refine (whnf.WF hmajorTr).bind fun mk _ _ ⟨hmkBelow, _⟩ => ?_
      have hmkBelowE : c.FVarsBelow e mk :=
        (FVarsBelow.getAppArg hmajorGet).trans hmkBelow
      split
      · exact .pure nofun
      · rename_i hnotApp
        have hmkShape : mk.isAppOfArity ``Quot.mk 3 = true := by
          cases h : mk.isAppOfArity ``Quot.mk 3 <;> simp_all
        have happ : ∃ fn arg, mk = .app fn arg := by
          cases mk <;> simp_all [Expr.isAppOfArity]
        have hbase : c.FVarsBelow e
            (Expr.app e.getAppArgs[argPos]! mk.appArg!) := by
          intro P hP heP
          exact ⟨FVarsBelow.getAppArg!
              (Nat.lt_trans hargPos hmkPos) P hP heP,
            (hmkBelowE.appArg! happ) P hP heP⟩
        split
        · rename_i htrail
          exact .pure fun e₁ he₁ => by
            cases he₁
            exact hbase.mkAppRange_getAppArgs_suffix
              (Nat.le_of_lt htrail)
        · exact .pure fun e₁ he₁ => by
            cases he₁
            exact hbase
    · exact .pure nofun
  unfold quotReduceRec
  split
  · dsimp
    split
    · exact contWF 5 3 (by omega)
    · split
      · exact contWF 4 3 (by omega)
      · exact .pure nofun
  · exact .pure nofun

/-- info: 'Lean4Lean.TypeChecker.Inner.quotReduceRec.WF_fvarsBelow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.quotReduceRec.WF_fvarsBelow

/-- When quotient reduction is disabled, a live verifier contract for the
inductive reducer lifts directly through `reduceRecursor`.  The wrapper's
`if let` preserves both the returned option and the state, so this join is
polymorphic in the desired postcondition. -/
theorem reduceRecursor.WF_of_quotInit_false
    {c : VContext} {s : VState} {e : Expr}
    {Q : Option Expr → VState → Prop}
    (hquot : c.env.quotInit = false)
    (hind : RecM.WF c s
      (inductiveReduceRec c.env e whnf inferType isDefEq) Q) :
    RecM.WF c s (reduceRecursor e) Q := by
  unfold reduceRecursor
  refine .getEnv ?_
  rw [hquot]
  refine hind.bind fun result _ _ hresult => ?_
  cases result <;> exact .pure hresult

/--
info: 'Lean4Lean.TypeChecker.Inner.reduceRecursor.WF_of_quotInit_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.reduceRecursor.WF_of_quotInit_false

/-- Compose the exhaustive ordinary callback analysis through a disabled
quotient gate.  Unlike the earlier exact-result adapters, this theorem does
not assume an equation for `whnf`; it invokes `whnf.WF` and analyzes every
runtime result internally. -/
theorem reduceRecursor.WF_of_quotInit_false_of_k_false_of_not_structure
    {c : VContext} {s : VState} {e : Expr} {e' : VExpr}
    {recFn : Name} {levels : List Level} {info : RecursorVal}
    {major : Expr}
    (hquot : c.env.quotInit = false)
    (he : c.TrExprS e e')
    (hfn : e.getAppFn = .const recFn levels)
    (hinfo : c.env.find? recFn = some (.recInfo info))
    (hmajor : e.getAppArgs[info.getMajorIdx]? = some major)
    (hk : info.k = false)
    (hstruct : c.env.isNonRecStructure info.getMajorInduct = false)
    (happly : inductiveReduceRec.SelectedBranchWF
      c s e e' major levels info) :
    RecM.WF c s (reduceRecursor e) fun oe _ =>
      ∀ result, oe = some result →
        c.FVarsBelow e result ∧ c.TrExpr result e' := by
  apply reduceRecursor.WF_of_quotInit_false hquot
  exact inductiveReduceRec.WF_of_k_false_of_not_structure
    he hfn hinfo hmajor hk hstruct happly

/--
info: 'Lean4Lean.TypeChecker.Inner.reduceRecursor.WF_of_quotInit_false_of_k_false_of_not_structure' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.reduceRecursor.WF_of_quotInit_false_of_k_false_of_not_structure

/-- When quotient reduction is enabled, compose its live verifier contract
with the inductive fallback.  A successful quotient result discharges `Q`
immediately; a `none` result may advance the verifier state and therefore
selects an inductive proof valid at every state extending the input state. -/
theorem reduceRecursor.WF_of_quotInit_true
    {c : VContext} {s : VState} {e : Expr}
    {Q : Option Expr → VState → Prop}
    (hquot : c.env.quotInit = true)
    (hquotWF : RecM.WF c s (quotReduceRec e whnf) fun oe s' =>
      ∀ result, oe = some result → Q (some result) s')
    (hind : ∀ {s'}, s ≤ s' → RecM.WF c s'
      (inductiveReduceRec c.env e whnf inferType isDefEq) Q) :
    RecM.WF c s (reduceRecursor e) Q := by
  unfold reduceRecursor
  refine .getEnv ?_
  rw [hquot]
  refine hquotWF.bind fun quotResult state hle hquotPost => ?_
  cases quotResult with
  | some result => exact .pure (hquotPost result rfl)
  | none =>
    refine (hind hle).bind fun result _ _ hresult => ?_
    cases result <;> exact .pure hresult

/--
info: 'Lean4Lean.TypeChecker.Inner.reduceRecursor.WF_of_quotInit_true' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.reduceRecursor.WF_of_quotInit_true

/-- The complete quotient-enabled join: both quotient eliminators are
handled by `quotReduceRec.WF`, and a declined quotient reduction falls
through to the caller's live inductive-reducer contract. -/
theorem reduceRecursor.WF_of_quotInit_true_of_inductive
    {c : VContext} {s : VState} {e : Expr} {e' : VExpr}
    (hquot : c.env.quotInit = true)
    (hinj : c.venv.QuotAppInj)
    (he : c.TrExprS e e')
    (hind : ∀ {s'}, s ≤ s' → RecM.WF c s'
      (inductiveReduceRec c.env e whnf inferType isDefEq) fun oe _ =>
        ∀ e₁, oe = some e₁ →
          c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e') :
    RecM.WF c s (reduceRecursor e) fun oe _ =>
      ∀ e₁, oe = some e₁ →
        c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  apply reduceRecursor.WF_of_quotInit_true hquot
  · exact (quotReduceRec.WF hquot hinj he).mono fun oe _ _ hpost => by
      intro result hresult e₁ he₁
      exact hpost e₁ (hresult.trans he₁)
  · exact hind

/--
info: 'Lean4Lean.TypeChecker.Inner.reduceRecursor.WF_of_quotInit_true_of_inductive' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.reduceRecursor.WF_of_quotInit_true_of_inductive

/-- Compose the proved live `Quot.lift` contract through the quotient gate of
`reduceRecursor`.  If quotient reduction declines, the ordinary inductive
fallback remains explicit and is required at every advanced verifier state. -/
theorem reduceRecursor.WF_of_quotLift
    {c : VContext} {s : VState} {e : Expr} {e' : VExpr}
    {hostLevels : List Level}
    (hquot : c.env.quotInit = true)
    (hinj : c.venv.QuotAppInj)
    (he : c.TrExprS e e')
    (hfn : e.getAppFn = .const ``Quot.lift hostLevels)
    (hind : ∀ {s'}, s ≤ s' → RecM.WF c s'
      (inductiveReduceRec c.env e whnf inferType isDefEq) fun oe _ =>
        ∀ e₁, oe = some e₁ →
          c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e') :
    RecM.WF c s (reduceRecursor e) fun oe _ =>
      ∀ e₁, oe = some e₁ →
        c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  apply reduceRecursor.WF_of_quotInit_true hquot
  · exact (quotReduceRec.WF_of_quotLift hquot hinj he hfn).mono
      fun oe _ _ hpost => by
        intro result hresult e₁ he₁
        exact hpost e₁ (hresult.trans he₁)
  · exact hind

/--
info: 'Lean4Lean.TypeChecker.Inner.reduceRecursor.WF_of_quotLift' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.reduceRecursor.WF_of_quotLift

/-- The quotient gate is completely transparent to the free-variable half
of `reduceRecursor.WF`.  Quotient reduction is handled above; a `none` result
falls through to an inductive proof that is polymorphic in the current
verifier state. -/
theorem reduceRecursor.WF_fvarsBelow_of_inductive
    {c : VContext} {s : VState} {e : Expr} {e' : VExpr}
    (he : c.TrExprS e e')
    (hind : ∀ {s'}, RecM.WF c s'
      (inductiveReduceRec c.env e whnf inferType isDefEq) fun oe _ =>
        ∀ e₁, oe = some e₁ → c.FVarsBelow e e₁) :
    RecM.WF c s (reduceRecursor e) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.FVarsBelow e e₁ := by
  cases hquot : c.env.quotInit with
  | false => exact reduceRecursor.WF_of_quotInit_false hquot hind
  | true =>
    apply reduceRecursor.WF_of_quotInit_true hquot
      ((quotReduceRec.WF_fvarsBelow he).mono fun oe _ _ hbelow => by
        intro result hresult e₁ he₁
        exact hbelow e₁ (hresult.trans he₁))
    intro state _
    exact hind (s' := state)

/--
info: 'Lean4Lean.TypeChecker.Inner.reduceRecursor.WF_fvarsBelow_of_inductive' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.reduceRecursor.WF_fvarsBelow_of_inductive

/-- Lift an exact pure `inductiveReduceRec` equation into the verifier's
`RecM.WF` contract when quotient reduction is disabled.  This is the semantic
join between the operational branch equations above and `reduceRecursor.WF`:
only a property of an actually returned expression remains. -/
theorem reduceRecursor.WF_of_quotInit_false_of_inductive_pure
    {c : VContext} {s : VState} {e : Expr} {e' : VExpr}
    {result : Option Expr}
    (hquot : c.env.quotInit = false)
    (hind : inductiveReduceRec c.env e whnf inferType isDefEq = pure result)
    (hresult : ∀ e₁, result = some e₁ →
      c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e') :
    RecM.WF c s (reduceRecursor e) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  apply reduceRecursor.WF_of_quotInit_false hquot
  rw [hind]
  cases result with
  | none => exact .pure nofun
  | some result =>
    exact .pure fun e₁ h => by
      cases h
      exact hresult result rfl

/-- Every exact `none` equation closes the verifier contract immediately. -/
theorem reduceRecursor.WF_of_quotInit_false_of_inductive_none
    {c : VContext} {s : VState} {e : Expr} {e' : VExpr}
    (hquot : c.env.quotInit = false)
    (hind : inductiveReduceRec c.env e whnf inferType isDefEq = pure none) :
    RecM.WF c s (reduceRecursor e) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  apply reduceRecursor.WF_of_quotInit_false_of_inductive_pure hquot hind
  exact nofun

/-- The nonconstant-head early exit is therefore already semantically
complete and needs no typing or normalization premise. -/
theorem reduceRecursor.WF_of_quotInit_false_of_nonconst
    {c : VContext} {s : VState} {e : Expr} {e' : VExpr}
    (hquot : c.env.quotInit = false)
    (hfn : ∀ name levels, e.getAppFn ≠ .const name levels) :
    RecM.WF c s (reduceRecursor e) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  apply reduceRecursor.WF_of_quotInit_false_of_inductive_none hquot
  exact inductiveReduceRec_eq_none_of_nonconst c.env whnf inferType isDefEq
    hfn

/-- A constant whose environment entry is not a recursor is another closed
early-failure branch of the live verifier. -/
theorem reduceRecursor.WF_of_quotInit_false_of_not_recursor
    {c : VContext} {s : VState} {e : Expr} {e' : VExpr}
    {recFn : Name} {levels : List Level}
    (hquot : c.env.quotInit = false)
    (hfn : e.getAppFn = .const recFn levels)
    (hinfo : ∀ info, c.env.find? recFn ≠ some (.recInfo info)) :
    RecM.WF c s (reduceRecursor e) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  apply reduceRecursor.WF_of_quotInit_false_of_inductive_none hquot
  exact inductiveReduceRec_eq_none_of_not_recursor c.env whnf inferType
    isDefEq hfn hinfo

/-- A known recursor missing its major argument also closes before any
callback is invoked. -/
theorem reduceRecursor.WF_of_quotInit_false_of_missing_major
    {c : VContext} {s : VState} {e : Expr} {e' : VExpr}
    {recFn : Name} {levels : List Level} {info : RecursorVal}
    (hquot : c.env.quotInit = false)
    (hfn : e.getAppFn = .const recFn levels)
    (hinfo : c.env.find? recFn = some (.recInfo info))
    (hmajor : e.getAppArgs[info.getMajorIdx]? = none) :
    RecM.WF c s (reduceRecursor e) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  apply reduceRecursor.WF_of_quotInit_false_of_inductive_none hquot
  exact inductiveReduceRec_eq_none_of_missing_major c.env whnf inferType
    isDefEq hfn hinfo hmajor

/-- Join a successful pure rule application to the exact live
`reduceRecursor.WF` contract.  The WHNF proof supplies free-variable
monotonicity for the exposed major, while the only output-specific premise
left here is its semantic translation. -/
theorem reduceRecursor.WF_of_quotInit_false_of_applyRecursorRule
    {c : VContext} {s : VState} {e : Expr} {e' : VExpr}
    {info : RecursorVal} {rule : RecursorRule}
    {levels : List Level} {major : Expr}
    (hquot : c.env.quotInit = false)
    (hind : inductiveReduceRec c.env e whnf inferType isDefEq =
      pure (some (applyRecursorRule info rule levels e.getAppArgs
        major.getAppArgs)))
    (hfirst : info.getFirstIndexIdx ≤ e.getAppArgs.size)
    (hrhs : FVarsIn (fun _ => False)
      (rule.rhs.instantiateLevelParams info.levelParams levels))
    (hmajor : c.FVarsBelow e major)
    (hout : c.TrExpr
      (applyRecursorRule info rule levels e.getAppArgs major.getAppArgs) e') :
    RecM.WF c s (reduceRecursor e) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  apply reduceRecursor.WF_of_quotInit_false_of_inductive_pure hquot hind
  intro e₁ he₁
  cases he₁
  exact ⟨applyRecursorRule_fvarsBelow hfirst hrhs hmajor, hout⟩

/-- Join a successful pure rule application to the live verifier contract
using the actual WHNF callback contract.  Strict translation of the complete
application supplies a strict translation of its selected major argument;
running `whnf.WF` against the exact pure callback equation then derives the
free-variable premise consumed by `applyRecursorRule_fvarsBelow`. -/
theorem reduceRecursor.WF_of_quotInit_false_of_applyRecursorRule_of_whnf
    {c : VContext} {s : VState} {e : Expr} {e' : VExpr}
    {info : RecursorVal} {rule : RecursorRule}
    {levels : List Level} {major whnfMajor : Expr}
    (hquot : c.env.quotInit = false)
    (hind : inductiveReduceRec c.env e whnf inferType isDefEq =
      pure (some (applyRecursorRule info rule levels e.getAppArgs
        whnfMajor.getAppArgs)))
    (hmajorArg : e.getAppArgs[info.getMajorIdx]? = some major)
    (hwhnf : whnf major = pure whnfMajor)
    (he : c.TrExprS e e')
    (hfirst : info.getFirstIndexIdx ≤ e.getAppArgs.size)
    (hrhs : FVarsIn (fun _ => False)
      (rule.rhs.instantiateLevelParams info.levelParams levels))
    (hout : c.TrExpr
      (applyRecursorRule info rule levels e.getAppArgs
        whnfMajor.getAppArgs) e') :
    RecM.WF c s (reduceRecursor e) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  obtain ⟨major', hmajorTr⟩ := he.getAppArg hmajorArg
  intro methods hmethods
  intro hs out state' hrun
  have hwhnfRun :
      whnf major methods c.toContext s.toState =
        .ok (whnfMajor, s.toState) := by
    rw [hwhnf]
    rfl
  obtain ⟨_, _, _, _, hwhnfPost⟩ :=
    (whnf.WF (s := s) hmajorTr methods hmethods)
      hs whnfMajor s.toState hwhnfRun
  have hbelow : c.FVarsBelow e whnfMajor :=
    (FVarsBelow.getAppArg hmajorArg).trans hwhnfPost.1
  exact
    (reduceRecursor.WF_of_quotInit_false_of_applyRecursorRule
      hquot hind hfirst hrhs hbelow hout methods hmethods)
      hs out state' hrun

/--
info: 'Lean4Lean.TypeChecker.Inner.reduceRecursor.WF_of_quotInit_false_of_applyRecursorRule_of_whnf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.reduceRecursor.WF_of_quotInit_false_of_applyRecursorRule_of_whnf

/-- Translate the pure recursor-rule tail once the selected RHS, canonical
capture slices, and arguments trailing the major premise have been typed.
This is the output-side boundary for recursor verification: runtime array
slicing is normalized by `applyRecursorRule_eq_slices`, while the two Theory
spines are concatenated and rebuilt as one host application. -/
theorem applyRecursorRule_trExpr
    {venv : VEnv} {Us : List Name} {Δ : VLCtx}
    {info : RecursorVal} {rule : RecursorRule}
    {levels : List Level} {recArgs majorArgs : Array Expr}
    {rhs' A B C : VExpr} {captures' trailing' : List VExpr}
    (hfirst : info.getFirstIndexIdx ≤ recArgs.size)
    (henv : venv.WF) (hΔ : Δ.WF venv Us.length)
    (hrhs : TrExpr venv Us Δ
      (rule.rhs.instantiateLevelParams info.levelParams levels) rhs')
    (hhead : venv.HasType Us.length Δ.toCtx rhs' A)
    (hcaptures : List.Forall₂ (TrExprS venv Us Δ)
      (recArgs.toList.take info.getFirstIndexIdx ++
        majorArgs.toList.drop (majorArgs.size - rule.nfields)) captures')
    (hcapspine : venv.SpineWF Us.length Δ.toCtx A captures' B)
    (htrailing : List.Forall₂ (TrExprS venv Us Δ)
      (recArgs.toList.drop (info.getMajorIdx + 1)) trailing')
    (htrailspine : venv.SpineWF Us.length Δ.toCtx B trailing' C) :
    TrExpr venv Us Δ
      (applyRecursorRule info rule levels recArgs majorArgs)
      (VExpr.appN (VExpr.appN rhs' captures') trailing') := by
  rw [applyRecursorRule_eq_slices hfirst]
  have hargs := Lean4Lean.List.Forall₂.append hcaptures htrailing
  have hspine := VEnv.SpineWF.append hcapspine htrailspine
  simpa [VExpr.appN_append] using
    TrExpr.mkAppList_of_spine henv hΔ hrhs hhead hargs hspine

/-- Generator-aligned form of `applyRecursorRule_trExpr`.  Pointwise
translation of the complete runtime recursor and constructor argument arrays
is sliced into the generator's canonical captures and the post-major suffix;
the host metadata equalities are the only positional inputs. -/
theorem applyRecursorRule_trExpr_of_generation
    {source : VInductDecl} (gen : source.BlockGenerationChecked)
    (constructor : VInductDecl.NormalizedBlockCtor)
    {venv : VEnv} {Us : List Name} {Δ : VLCtx}
    {info : RecursorVal} {rule : RecursorRule}
    {levels : List Level} {recArgs majorArgs : Array Expr}
    {fArgs aArgs : List VExpr}
    {rhs' A B C : VExpr}
    (henv : venv.WF) (hΔ : Δ.WF venv Us.length)
    (hfirst : info.getFirstIndexIdx =
      source.nparams + gen.familyCount + gen.minorCount)
    (hmajor : info.getMajorIdx = gen.ruleMajorArity constructor)
    (hfields : rule.nfields = gen.ruleFieldCount constructor)
    (hmajorBound : gen.ruleMajorArity constructor < fArgs.length)
    (hNlen : aArgs.length = gen.ruleArgArity constructor)
    (hrec : List.Forall₂ (TrExprS venv Us Δ) recArgs.toList fArgs)
    (hctor : List.Forall₂ (TrExprS venv Us Δ) majorArgs.toList aArgs)
    (hrhs : TrExpr venv Us Δ
      (rule.rhs.instantiateLevelParams info.levelParams levels) rhs')
    (hhead : venv.HasType Us.length Δ.toCtx rhs' A)
    (hcapspine : venv.SpineWF Us.length Δ.toCtx A
      (gen.ruleCaptureValues constructor fArgs aArgs) B)
    (htrailspine : venv.SpineWF Us.length Δ.toCtx B
      (fArgs.drop (gen.ruleMajorArity constructor + 1)) C) :
    TrExpr venv Us Δ
      (applyRecursorRule info rule levels recArgs majorArgs)
      (VExpr.appN
        (VExpr.appN rhs' (gen.ruleCaptureValues constructor fArgs aArgs))
        (fArgs.drop (gen.ruleMajorArity constructor + 1))) := by
  have hfirstBound : info.getFirstIndexIdx ≤ recArgs.size := by
    rw [hfirst]
    have hcommon : source.nparams + gen.familyCount + gen.minorCount ≤
        gen.ruleMajorArity constructor := Nat.le_add_right _ _
    have hcommonBound := Nat.lt_of_le_of_lt hcommon hmajorBound
    rw [← Lean4Lean.List.Forall₂.length_eq hrec] at hcommonBound
    simpa using Nat.le_of_lt hcommonBound
  have hcaptures := gen.ruleCaptureValues_translation constructor
    info.getFirstIndexIdx rule.nfields hrec hctor hfirst hfields hNlen
  simp only [Array.length_toList] at hcaptures
  have htrailing := Lean4Lean.List.Forall₂.drop hrec
    (info.getMajorIdx + 1)
  have htrailspine' : venv.SpineWF Us.length Δ.toCtx B
      (fArgs.drop (info.getMajorIdx + 1)) C := by
    simpa [hmajor] using htrailspine
  have hout := applyRecursorRule_trExpr hfirstBound henv hΔ hrhs hhead
    hcaptures hcapspine htrailing htrailspine'
  simpa [hmajor] using hout

/-- Translate the pure reducer tail and discharge its semantic target with
the final registered restoration of one staged rule.  The runtime slice
translations build the concrete output, while the restored rule equation is
applied to the same typed captures and then extended across the post-major
suffix. -/
theorem applyRecursorRule_trExpr_of_nestedRegistered
    {source : VInductDecl} {before flatAfter after : VEnv}
    (certificate : VInductDecl.NestedStagedCertificate source before
      flatAfter after)
    {i : Nat} {constructor : VInductDecl.NormalizedBlockCtor}
    (facts : certificate.RecursorRuleFacts i constructor)
    {Us : List Name} {Δ : VLCtx}
    {info : RecursorVal} {rule : RecursorRule}
    {levels : List Level} {recArgs majorArgs : Array Expr}
    {m1 : List VLevel} {captures trailing : List VExpr}
    {B C target : VExpr}
    (hfirst : info.getFirstIndexIdx ≤ recArgs.size)
    (hΔ : Δ.WF after Us.length)
    (hm1 : ∀ l ∈ m1, l.WF Us.length)
    (hlen1 : m1.length =
      certificate.restored.nested.generation.recUvars)
    (hrhs : TrExpr after Us Δ
      (rule.rhs.instantiateLevelParams info.levelParams levels)
      ((certificate.restored.nested.restoredRule i constructor).rhs.instL m1))
    (hcaptures : List.Forall₂ (TrExprS after Us Δ)
      (recArgs.toList.take info.getFirstIndexIdx ++
        majorArgs.toList.drop (majorArgs.size - rule.nfields)) captures)
    (hcapspine : after.SpineWF Us.length Δ.toCtx
      ((certificate.restored.nested.restoredRule i constructor).type.instL m1)
      captures B)
    (htrailing : List.Forall₂ (TrExprS after Us Δ)
      (recArgs.toList.drop (info.getMajorIdx + 1)) trailing)
    (htrailspine : after.SpineWF Us.length Δ.toCtx B trailing C)
    (hinput : after.IsDefEqU Us.length Δ.toCtx
      (VExpr.appN
        (VExpr.appN
          ((certificate.restored.nested.restoredRule i constructor).lhs.instL
            m1) captures) trailing)
      target) :
    TrExpr after Us Δ
      (applyRecursorRule info rule levels recArgs majorArgs) target := by
  have hhead : after.HasType Us.length Δ.toCtx
      ((certificate.restored.nested.restoredRule i constructor).rhs.instL m1)
      ((certificate.restored.nested.restoredRule i constructor).type.instL m1) :=
    (facts.restoredWF.2.instL hm1).weak0 certificate.restored.afterWF.ordered
  have hout := applyRecursorRule_trExpr hfirst certificate.restored.afterWF hΔ
    hrhs hhead hcaptures hcapspine htrailing htrailspine
  have hregistered := certificate.restoredRuleReductionApplied facts hm1
    hlen1 hcapspine
  have hregisteredTrailing := hregistered.appN_congr htrailspine
  exact hout.defeq certificate.restored.afterWF hΔ.toCtx
    (VEnv.IsDefEqU.trans certificate.restored.afterWF hΔ.toCtx
      ⟨_, hregisteredTrailing.symm⟩ hinput)

/-- Generator-aligned form of the staged restored-rule consumer.  Complete
runtime argument translations determine the canonical capture and trailing
slices, leaving only the restored capture spine and the alignment of the
restored lhs application with the translated input redex. -/
theorem applyRecursorRule_trExpr_of_nestedGeneration
    {source : VInductDecl} {before flatAfter after : VEnv}
    (certificate : VInductDecl.NestedStagedCertificate source before
      flatAfter after)
    {i : Nat} {constructor : VInductDecl.NormalizedBlockCtor}
    (facts : certificate.RecursorRuleFacts i constructor)
    {Us : List Name} {Δ : VLCtx}
    {info : RecursorVal} {rule : RecursorRule}
    {levels : List Level} {recArgs majorArgs : Array Expr}
    {m1 : List VLevel} {fArgs aArgs : List VExpr}
    {B C target : VExpr}
    (hΔ : Δ.WF after Us.length)
    (hm1 : ∀ l ∈ m1, l.WF Us.length)
    (hlen1 : m1.length =
      certificate.restored.nested.generation.recUvars)
    (hfirst : info.getFirstIndexIdx =
      certificate.restored.nested.elim.flat.nparams +
        certificate.restored.nested.generation.familyCount +
        certificate.restored.nested.generation.minorCount)
    (hmajor : info.getMajorIdx =
      certificate.restored.nested.generation.ruleMajorArity constructor)
    (hfields : rule.nfields =
      certificate.restored.nested.generation.ruleFieldCount constructor)
    (hmajorBound :
      certificate.restored.nested.generation.ruleMajorArity constructor <
        fArgs.length)
    (hNlen : aArgs.length =
      certificate.restored.nested.generation.ruleArgArity constructor)
    (hrec : List.Forall₂ (TrExprS after Us Δ) recArgs.toList fArgs)
    (hctor : List.Forall₂ (TrExprS after Us Δ) majorArgs.toList aArgs)
    (hrhs : TrExpr after Us Δ
      (rule.rhs.instantiateLevelParams info.levelParams levels)
      ((certificate.restored.nested.restoredRule i constructor).rhs.instL m1))
    (hcapspine : after.SpineWF Us.length Δ.toCtx
      ((certificate.restored.nested.restoredRule i constructor).type.instL m1)
      (certificate.restored.nested.generation.ruleCaptureValues constructor
        fArgs aArgs) B)
    (htrailspine : after.SpineWF Us.length Δ.toCtx B
      (fArgs.drop
        (certificate.restored.nested.generation.ruleMajorArity constructor + 1)) C)
    (hinput : after.IsDefEqU Us.length Δ.toCtx
      (VExpr.appN
        (VExpr.appN
          ((certificate.restored.nested.restoredRule i constructor).lhs.instL
            m1)
          (certificate.restored.nested.generation.ruleCaptureValues constructor
            fArgs aArgs))
        (fArgs.drop
          (certificate.restored.nested.generation.ruleMajorArity constructor + 1)))
      target) :
    TrExpr after Us Δ
      (applyRecursorRule info rule levels recArgs majorArgs) target := by
  have hhead : after.HasType Us.length Δ.toCtx
      ((certificate.restored.nested.restoredRule i constructor).rhs.instL m1)
      ((certificate.restored.nested.restoredRule i constructor).type.instL m1) :=
    (facts.restoredWF.2.instL hm1).weak0 certificate.restored.afterWF.ordered
  have hout := applyRecursorRule_trExpr_of_generation
    certificate.restored.nested.generation constructor
    certificate.restored.afterWF hΔ hfirst hmajor hfields hmajorBound hNlen
    hrec hctor hrhs hhead hcapspine htrailspine
  have hregistered := certificate.restoredRuleReductionApplied facts hm1
    hlen1 hcapspine
  have hregisteredTrailing := hregistered.appN_congr htrailspine
  exact hout.defeq certificate.restored.afterWF hΔ.toCtx
    (VEnv.IsDefEqU.trans certificate.restored.afterWF hΔ.toCtx
      ⟨_, hregisteredTrailing.symm⟩ hinput)

/-- Restored-body form of the generator-aligned reducer theorem.  The
certificate β-collapses the restored left tower, including post-major
arguments, so consumers only align the instantiated restored generated body
with the translated runtime redex. -/
theorem applyRecursorRule_trExpr_of_nestedGenerationBody
    {source : VInductDecl} {before flatAfter after : VEnv}
    (certificate : VInductDecl.NestedStagedCertificate source before
      flatAfter after)
    {i : Nat} {constructor : VInductDecl.NormalizedBlockCtor}
    (facts : certificate.RecursorRuleFacts i constructor)
    {Us : List Name} {Δ : VLCtx}
    {info : RecursorVal} {rule : RecursorRule}
    {levels : List Level} {recArgs majorArgs : Array Expr}
    {m1 : List VLevel} {fArgs aArgs : List VExpr}
    {B C target : VExpr}
    (hΔ : Δ.WF after Us.length)
    (hm1 : ∀ l ∈ m1, l.WF Us.length)
    (hlen1 : m1.length =
      certificate.restored.nested.generation.recUvars)
    (hfirst : info.getFirstIndexIdx =
      certificate.restored.nested.elim.flat.nparams +
        certificate.restored.nested.generation.familyCount +
        certificate.restored.nested.generation.minorCount)
    (hmajor : info.getMajorIdx =
      certificate.restored.nested.generation.ruleMajorArity constructor)
    (hfields : rule.nfields =
      certificate.restored.nested.generation.ruleFieldCount constructor)
    (hmajorBound :
      certificate.restored.nested.generation.ruleMajorArity constructor <
        fArgs.length)
    (hNlen : aArgs.length =
      certificate.restored.nested.generation.ruleArgArity constructor)
    (hrec : List.Forall₂ (TrExprS after Us Δ) recArgs.toList fArgs)
    (hctor : List.Forall₂ (TrExprS after Us Δ) majorArgs.toList aArgs)
    (hrhs : TrExpr after Us Δ
      (rule.rhs.instantiateLevelParams info.levelParams levels)
      ((certificate.restored.nested.restoredRule i constructor).rhs.instL m1))
    (hcapspine : after.SpineWF Us.length Δ.toCtx
      ((certificate.restored.nested.restoredRule i constructor).type.instL m1)
      (certificate.restored.nested.generation.ruleCaptureValues constructor
        fArgs aArgs) B)
    (htrailspine : after.SpineWF Us.length Δ.toCtx B
      (fArgs.drop
        (certificate.restored.nested.generation.ruleMajorArity constructor + 1)) C)
    (hbodyInput : after.IsDefEqU Us.length Δ.toCtx
      (VExpr.appN
        (VExpr.instRev
          ((certificate.restored.nested.restoreRec
            (certificate.restored.nested.generation.ruleLhsBody
              constructor)).instL m1)
          (certificate.restored.nested.generation.ruleCaptureValues constructor
            fArgs aArgs))
        (fArgs.drop
          (certificate.restored.nested.generation.ruleMajorArity constructor + 1)))
      target) :
    TrExpr after Us Δ
      (applyRecursorRule info rule levels recArgs majorArgs) target := by
  apply applyRecursorRule_trExpr_of_nestedGeneration certificate facts hΔ hm1
    hlen1 hfirst hmajor hfields hmajorBound hNlen hrec hctor hrhs hcapspine
    htrailspine
  exact VEnv.IsDefEqU.trans certificate.restored.afterWF hΔ.toCtx
    (certificate.restoredRuleCanonicalLhsAppliedTrailing facts hΔ.toCtx hm1
      hmajorBound hNlen hcapspine htrailspine)
    hbodyInput

/-- Feed a saturated restored-body/runtime-redex match directly to the pure
reducer tail.  The certified restored LHS collapse types that body at the
capture-spine result, so ordinary application congruence appends every
post-major argument and chooses `target.appN trailing` automatically. -/
theorem applyRecursorRule_trExpr_of_nestedGenerationBodyMatched
    {source : VInductDecl} {before flatAfter after : VEnv}
    (certificate : VInductDecl.NestedStagedCertificate source before
      flatAfter after)
    {i : Nat} {constructor : VInductDecl.NormalizedBlockCtor}
    (facts : certificate.RecursorRuleFacts i constructor)
    {Us : List Name} {Δ : VLCtx}
    {info : RecursorVal} {rule : RecursorRule}
    {levels : List Level} {recArgs majorArgs : Array Expr}
    {m1 : List VLevel} {fArgs aArgs : List VExpr}
    {B C target : VExpr}
    (hΔ : Δ.WF after Us.length)
    (hm1 : ∀ l ∈ m1, l.WF Us.length)
    (hlen1 : m1.length =
      certificate.restored.nested.generation.recUvars)
    (hfirst : info.getFirstIndexIdx =
      certificate.restored.nested.elim.flat.nparams +
        certificate.restored.nested.generation.familyCount +
        certificate.restored.nested.generation.minorCount)
    (hmajor : info.getMajorIdx =
      certificate.restored.nested.generation.ruleMajorArity constructor)
    (hfields : rule.nfields =
      certificate.restored.nested.generation.ruleFieldCount constructor)
    (hmajorBound :
      certificate.restored.nested.generation.ruleMajorArity constructor <
        fArgs.length)
    (hNlen : aArgs.length =
      certificate.restored.nested.generation.ruleArgArity constructor)
    (hrec : List.Forall₂ (TrExprS after Us Δ) recArgs.toList fArgs)
    (hctor : List.Forall₂ (TrExprS after Us Δ) majorArgs.toList aArgs)
    (hrhs : TrExpr after Us Δ
      (rule.rhs.instantiateLevelParams info.levelParams levels)
      ((certificate.restored.nested.restoredRule i constructor).rhs.instL m1))
    (hcapspine : after.SpineWF Us.length Δ.toCtx
      ((certificate.restored.nested.restoredRule i constructor).type.instL m1)
      (certificate.restored.nested.generation.ruleCaptureValues constructor
        fArgs aArgs) B)
    (htrailspine : after.SpineWF Us.length Δ.toCtx B
      (fArgs.drop
        (certificate.restored.nested.generation.ruleMajorArity constructor + 1)) C)
    (hbody : after.IsDefEqU Us.length Δ.toCtx
      (VExpr.instRev
        ((certificate.restored.nested.restoreRec
          (certificate.restored.nested.generation.ruleLhsBody
            constructor)).instL m1)
        (certificate.restored.nested.generation.ruleCaptureValues constructor
          fArgs aArgs))
      target) :
    TrExpr after Us Δ
      (applyRecursorRule info rule levels recArgs majorArgs)
      (VExpr.appN target
        (fArgs.drop
          (certificate.restored.nested.generation.ruleMajorArity constructor + 1))) := by
  let gen := certificate.restored.nested.generation
  have hmajorLE : gen.ruleMajorArity constructor ≤ fArgs.length := by
    dsimp [gen]
    omega
  have htakeLen : (fArgs.take (gen.ruleMajorArity constructor)).length =
      gen.ruleMajorArity constructor := by
    rw [List.length_take, Nat.min_eq_left hmajorLE]
  have hcapsLen := gen.ruleCaptureValues_length constructor htakeLen hNlen
  rw [gen.ruleCaptureValues_take_major] at hcapsLen
  have hcollapse := certificate.restoredRuleLhsApplied facts hΔ.toCtx hm1
    hcapspine hcapsLen
  have hhead : after.HasType Us.length Δ.toCtx
      ((certificate.restored.nested.restoredRule i constructor).lhs.instL m1)
      ((certificate.restored.nested.restoredRule i constructor).type.instL m1) :=
    (facts.restoredWF.1.instL hm1).weak0
      certificate.restored.afterWF.ordered
  have happ := hcapspine.hasType_appN hhead
  have hbodyT :=
    (hcollapse.of_l certificate.restored.afterWF hΔ.toCtx happ).hasType.2
  have hbody' := hbody.of_l certificate.restored.afterWF hΔ.toCtx hbodyT
  have hbodyInput : after.IsDefEqU Us.length Δ.toCtx
      (VExpr.appN
        (VExpr.instRev
          ((certificate.restored.nested.restoreRec
            (certificate.restored.nested.generation.ruleLhsBody
              constructor)).instL m1)
          (certificate.restored.nested.generation.ruleCaptureValues constructor
            fArgs aArgs))
        (fArgs.drop
          (certificate.restored.nested.generation.ruleMajorArity constructor + 1)))
      (VExpr.appN target
        (fArgs.drop
          (certificate.restored.nested.generation.ruleMajorArity constructor + 1))) :=
    ⟨C, hbody'.appN_congr htrailspine⟩
  exact applyRecursorRule_trExpr_of_nestedGenerationBody certificate facts hΔ
    hm1 hlen1 hfirst hmajor hfields hmajorBound hNlen hrec hctor hrhs
    hcapspine htrailspine hbodyInput

/-- Thread a saturated nested generated-body match through the actual
nonliteral `inductiveReduceRec` execution.  This is the
selected-site composition point: the real reducer control flow identifies
the pure tail, and the staged certificate proves the returned reduct has the
restored runtime target, including every argument after the major premise. -/
theorem inductiveReduceRec_result_trExpr_of_nestedGenerationBodyMatched
    {source : VInductDecl} {before flatAfter after : VEnv}
    (certificate : VInductDecl.NestedStagedCertificate source before
      flatAfter after)
    {i : Nat} {constructor : VInductDecl.NormalizedBlockCtor}
    (facts : certificate.RecursorRuleFacts i constructor)
    {m : Type → Type} [Monad m] [LawfulMonad m]
    (env : Environment) (whnf inferType : Expr → m Expr)
    (isDefEq : Expr → Expr → m Bool)
    {e major whnfMajor ctorMajor : Expr} {recFn : Name}
    {levels : List Level} {info : RecursorVal} {rule : RecursorRule}
    (hfn : e.getAppFn = .const recFn levels)
    (hinfo : env.find? recFn = some (.recInfo info))
    (hmajor : e.getAppArgs[info.getMajorIdx]? = some major)
    (hk : info.k = false)
    (hwhnf : whnf major = pure whnfMajor)
    (hnotLit : ∀ lit, whnfMajor ≠ .lit lit)
    (hstruct : toCtorWhenStruct env whnf inferType info.getMajorInduct
      whnfMajor = pure ctorMajor)
    (hrule : getRecRuleFor info ctorMajor = some rule)
    (hfieldsBound : rule.nfields ≤ ctorMajor.getAppArgs.size)
    (hlevels : levels.length = info.levelParams.length)
    {Us : List Name} {Δ : VLCtx}
    {m1 : List VLevel} {fArgs aArgs : List VExpr}
    {B C target : VExpr}
    (hΔ : Δ.WF after Us.length)
    (hm1 : ∀ l ∈ m1, l.WF Us.length)
    (hlen1 : m1.length =
      certificate.restored.nested.generation.recUvars)
    (hfirst : info.getFirstIndexIdx =
      certificate.restored.nested.elim.flat.nparams +
        certificate.restored.nested.generation.familyCount +
        certificate.restored.nested.generation.minorCount)
    (hmajorIdx : info.getMajorIdx =
      certificate.restored.nested.generation.ruleMajorArity constructor)
    (hfields : rule.nfields =
      certificate.restored.nested.generation.ruleFieldCount constructor)
    (hmajorBound :
      certificate.restored.nested.generation.ruleMajorArity constructor <
        fArgs.length)
    (hNlen : aArgs.length =
      certificate.restored.nested.generation.ruleArgArity constructor)
    (hrec : List.Forall₂ (TrExprS after Us Δ)
      e.getAppArgs.toList fArgs)
    (hctor : List.Forall₂ (TrExprS after Us Δ)
      ctorMajor.getAppArgs.toList aArgs)
    (hrhs : TrExpr after Us Δ
      (rule.rhs.instantiateLevelParams info.levelParams levels)
      ((certificate.restored.nested.restoredRule i constructor).rhs.instL m1))
    (hcapspine : after.SpineWF Us.length Δ.toCtx
      ((certificate.restored.nested.restoredRule i constructor).type.instL m1)
      (certificate.restored.nested.generation.ruleCaptureValues constructor
        fArgs aArgs) B)
    (htrailspine : after.SpineWF Us.length Δ.toCtx B
      (fArgs.drop
        (certificate.restored.nested.generation.ruleMajorArity constructor + 1)) C)
    (hbody : after.IsDefEqU Us.length Δ.toCtx
      (VExpr.instRev
        ((certificate.restored.nested.restoreRec
          (certificate.restored.nested.generation.ruleLhsBody
            constructor)).instL m1)
        (certificate.restored.nested.generation.ruleCaptureValues constructor
          fArgs aArgs))
      target) :
    ∃ result,
      inductiveReduceRec env e whnf inferType isDefEq = pure (some result) ∧
      TrExpr after Us Δ result
        (VExpr.appN target
          (fArgs.drop
            (certificate.restored.nested.generation.ruleMajorArity
              constructor + 1))) := by
  have hout := applyRecursorRule_trExpr_of_nestedGenerationBodyMatched
    certificate facts hΔ hm1 hlen1 hfirst hmajorIdx hfields hmajorBound
    hNlen hrec hctor hrhs hcapspine htrailspine hbody
  exact inductiveReduceRec_result_trExpr_of_nonliteral env whnf inferType
    isDefEq hfn hinfo hmajor hk hwhnf hnotLit hstruct hrule hfieldsBound
    hlevels hout

/-- info: 'Lean4Lean.TypeChecker.Inner.applyRecursorRule_eq_slices' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.applyRecursorRule_eq_slices

/-- info: 'Lean4Lean.TypeChecker.Inner.applyRecursorRule_fvarsBelow' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.applyRecursorRule_fvarsBelow

/--
info: 'Lean4Lean.TypeChecker.Inner.instantiateLevelParams_fvarsIn_of_trExprS_empty' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.instantiateLevelParams_fvarsIn_of_trExprS_empty

/--
info: 'Lean4Lean.TypeChecker.Inner.getAppFn_const_levels_length_of_trExprS' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.getAppFn_const_levels_length_of_trExprS

/-- info: 'Lean4Lean.TypeChecker.Inner.toCtorWhenStruct_eq_pure_of_isConstructorApp' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.toCtorWhenStruct_eq_pure_of_isConstructorApp

/-- info: 'Lean4Lean.TypeChecker.Inner.isConstructorApp?_mkAppList_of_find_ctor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.isConstructorApp?_mkAppList_of_find_ctor

/-- info: 'Lean4Lean.TypeChecker.Inner.mkAppList_const_ne_lit' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.mkAppList_const_ne_lit

/--
info: 'Lean4Lean.TypeChecker.Inner.inductiveReduceRec_eq_some_applyRecursorRule_of_apps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.inductiveReduceRec_eq_some_applyRecursorRule_of_apps

/--
info: 'Lean4Lean.TypeChecker.Inner.inductiveReduceRec_result_trExpr_of_apps' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.inductiveReduceRec_result_trExpr_of_apps

/--
info: 'Lean4Lean.TypeChecker.Inner.inductiveReduceRec_eq_some_applyRecursorRule_of_nonliteral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.inductiveReduceRec_eq_some_applyRecursorRule_of_nonliteral

/--
info: 'Lean4Lean.TypeChecker.Inner.inductiveReduceRec_result_trExpr_of_nonliteral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.inductiveReduceRec_result_trExpr_of_nonliteral

/--
info: 'Lean4Lean.TypeChecker.Inner.inductiveReduceRec_eq_some_applyRecursorRule_of_k_nonliteral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.inductiveReduceRec_eq_some_applyRecursorRule_of_k_nonliteral

/--
info: 'Lean4Lean.TypeChecker.Inner.inductiveReduceRec_eq_some_applyRecursorRule_of_k_constructor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.inductiveReduceRec_eq_some_applyRecursorRule_of_k_constructor

/--
info: 'Lean4Lean.TypeChecker.Inner.inductiveReduceRec_eq_some_applyRecursorRule_of_natLit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.inductiveReduceRec_eq_some_applyRecursorRule_of_natLit

/--
info: 'Lean4Lean.TypeChecker.Inner.inductiveReduceRec_eq_some_applyRecursorRule_of_strLit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.inductiveReduceRec_eq_some_applyRecursorRule_of_strLit

/--
info: 'Lean4Lean.TypeChecker.Inner.inductiveReduceRec_eq_some_applyRecursorRule_of_constructor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.inductiveReduceRec_eq_some_applyRecursorRule_of_constructor

/--
info: 'Lean4Lean.TypeChecker.Inner.inductiveReduceRec_result_trExpr_of_constructor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.inductiveReduceRec_result_trExpr_of_constructor

/--
info: 'Lean4Lean.TypeChecker.Inner.inductiveReduceRec_eq_none_of_nonconst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.inductiveReduceRec_eq_none_of_nonconst

/--
info: 'Lean4Lean.TypeChecker.Inner.inductiveReduceRec_eq_none_of_missing_recursor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.inductiveReduceRec_eq_none_of_missing_recursor

/--
info: 'Lean4Lean.TypeChecker.Inner.inductiveReduceRec_eq_none_of_not_recursor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.inductiveReduceRec_eq_none_of_not_recursor

/--
info: 'Lean4Lean.TypeChecker.Inner.inductiveReduceRec_eq_none_of_missing_major' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.inductiveReduceRec_eq_none_of_missing_major

/--
info: 'Lean4Lean.TypeChecker.Inner.inductiveReduceRec_eq_none_of_nonliteral_no_rule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.inductiveReduceRec_eq_none_of_nonliteral_no_rule

/--
info: 'Lean4Lean.TypeChecker.Inner.inductiveReduceRec_eq_none_of_nonliteral_field_underflow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.inductiveReduceRec_eq_none_of_nonliteral_field_underflow

/--
info: 'Lean4Lean.TypeChecker.Inner.inductiveReduceRec_eq_none_of_nonliteral_level_mismatch' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.inductiveReduceRec_eq_none_of_nonliteral_level_mismatch

/--
info: 'Lean4Lean.TypeChecker.Inner.reduceRecursor_run_eq_of_quotInit_false' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.reduceRecursor_run_eq_of_quotInit_false

/--
info: 'Lean4Lean.TypeChecker.Inner.reduceRecursor_run_eq_of_quot_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.reduceRecursor_run_eq_of_quot_some

/--
info: 'Lean4Lean.TypeChecker.Inner.reduceRecursor_run_eq_of_quot_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.reduceRecursor_run_eq_of_quot_none

/--
info: 'Lean4Lean.TypeChecker.Inner.reduceRecursor.WF_of_quotInit_false_of_inductive_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.reduceRecursor.WF_of_quotInit_false_of_inductive_pure

/--
info: 'Lean4Lean.TypeChecker.Inner.reduceRecursor.WF_of_quotInit_false_of_inductive_none' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.reduceRecursor.WF_of_quotInit_false_of_inductive_none

/--
info: 'Lean4Lean.TypeChecker.Inner.reduceRecursor.WF_of_quotInit_false_of_nonconst' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.reduceRecursor.WF_of_quotInit_false_of_nonconst

/--
info: 'Lean4Lean.TypeChecker.Inner.reduceRecursor.WF_of_quotInit_false_of_not_recursor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.reduceRecursor.WF_of_quotInit_false_of_not_recursor

/--
info: 'Lean4Lean.TypeChecker.Inner.reduceRecursor.WF_of_quotInit_false_of_missing_major' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.reduceRecursor.WF_of_quotInit_false_of_missing_major

/--
info: 'Lean4Lean.TypeChecker.Inner.reduceRecursor.WF_of_quotInit_false_of_applyRecursorRule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.reduceRecursor.WF_of_quotInit_false_of_applyRecursorRule

/--
info: 'Lean4Lean.TypeChecker.Inner.applyRecursorRule_trExpr' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.applyRecursorRule_trExpr

/--
info: 'Lean4Lean.TypeChecker.Inner.applyRecursorRule_trExpr_of_generation' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.applyRecursorRule_trExpr_of_generation

/--
info: 'Lean4Lean.TypeChecker.Inner.applyRecursorRule_trExpr_of_nestedRegistered' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.applyRecursorRule_trExpr_of_nestedRegistered

/--
info: 'Lean4Lean.TypeChecker.Inner.applyRecursorRule_trExpr_of_nestedGeneration' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.applyRecursorRule_trExpr_of_nestedGeneration

/--
info: 'Lean4Lean.TypeChecker.Inner.applyRecursorRule_trExpr_of_nestedGenerationBody' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.applyRecursorRule_trExpr_of_nestedGenerationBody

/--
info: 'Lean4Lean.TypeChecker.Inner.applyRecursorRule_trExpr_of_nestedGenerationBodyMatched' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.applyRecursorRule_trExpr_of_nestedGenerationBodyMatched

/--
info: 'Lean4Lean.TypeChecker.Inner.inductiveReduceRec_result_trExpr_of_nestedGenerationBodyMatched' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.TypeChecker.Inner.inductiveReduceRec_result_trExpr_of_nestedGenerationBodyMatched

theorem reduceNative.WF :
    (reduceNative env e).WF fun oe => ∀ e₁, oe = some e₁ → False := by
  unfold reduceNative; split <;> [skip; exact .pure nofun]
  split <;> [exact .throw; skip]; split <;> [exact .throw; exact .pure nofun]

theorem rawNatLitExt?.WF {c : VContext} (H : rawNatLitExt? e = some n) (he : c.TrExprS e e') :
    c.venv.contains ``Nat ∧ e' = .natLit n := by
  have : c.TrExprS (.lit (.natVal n)) e' := by
    unfold rawNatLitExt? at H; split at H <;> rename_i h
    · cases H; have := he.eqv h; exact .lit (this.nat_of_natZero c.Ewf c.hasPrimitives) this
    · unfold Expr.rawNatLit? at H; split at H <;> cases H; exact he
  have hn := this.lit_has_type
  exact ⟨hn, this.unique (by trivial) (TrExprS.natLit c.hasPrimitives hn n).1⟩

def reduceBinNatOpG (guard : Nat → Nat → Prop) [DecidableRel guard]
    (f : Nat → Nat → Nat) (a b : Expr) : RecM (Option Expr) := do
  let some v1 := rawNatLitExt? (← whnf a) | return none
  let some v2 := rawNatLitExt? (← whnf b) | return none
  if guard v1 v2 then return none
  return some <| .lit <| .natVal <| f v1 v2

theorem reduceBinNatOpG.WF {guard} [DecidableRel guard] {c : VContext}
    (he : c.TrExprS (.app (.app (.const fc ls) a) b) e')
    (hprim : Environment.primitives.contains fc)
    (heval : c.venv.ReflectsNatNatNat fc f) :
    RecM.WF c s (reduceBinNatOpG guard f a b) fun oe _ => ∀ e₁, oe = some e₁ →
      c.FVarsBelow (.app (.app (.const fc ls) a) b) e₁ ∧ c.TrExpr e₁ e' := by
  let .app hb1 hb2 hf hb := he
  let .app ha1 ha2 hf ha := hf
  let .const h1 h2 h3 := hf
  unfold reduceBinNatOpG
  refine (whnf.WF ha).bind fun a₁ _ _ ⟨a1, _, a2, a3⟩ => ?_
  split <;> [rename_i v1 h; exact .pure nofun]
  obtain ⟨hn, rfl⟩ := rawNatLitExt?.WF h a2
  refine (whnf.WF hb).bind fun b₁ _ _ ⟨b1, _, b2, b3⟩ => ?_
  split <;> [rename_i v2 h; exact .pure nofun]
  cases (rawNatLitExt?.WF h b2).2
  split <;> [exact .pure nofun; rename_i h]
  refine .pure ?_; rintro _ ⟨⟩; refine ⟨fun _ _ _ => trivial, ?_⟩
  have ⟨ci, c1, _⟩ := c.trenv.find?_iff.2 ⟨_, h1⟩
  have ⟨_, c3⟩ := c.safePrimitives c1 hprim
  have ⟨_, d1, d2, d3⟩ := c.trenv.find?_uniq c1 h1
  simp [c3] at d2; simp [← d2] at h3; simp [h3] at h2; subst h2
  refine ⟨_, (TrExprS.natLit c.hasPrimitives hn _).1, ?_⟩
  have := heval ⟨_, h1⟩ v1 v2 |>.instL (U' := c.lparams.length) (ls := []) nofun
  simp [VExpr.instL] at this
  refine this.weak0 c.Ewf (Γ := c.vlctx.toCtx) |>.symm.trans c.Ewf c.Δwf ?_
  have a3 := a3.of_r c.Ewf c.Δwf ha2
  have b3 := b3.of_r c.Ewf c.Δwf hb2
  have := ha1.appDF a3 |>.toU.of_r c.Ewf c.Δwf hb1
  exact ⟨_, .appDF this b3⟩

theorem reduceBinNatPred.WF {c : VContext}
    (he : c.TrExprS (.app (.app (.const fc ls) a) b) e')
    (hprim : Environment.primitives.contains fc)
    (heval : c.venv.ReflectsNatNatBool fc f) :
    RecM.WF c s (reduceBinNatPred f a b) fun oe _ => ∀ e₁, oe = some e₁ →
      c.FVarsBelow (.app (.app (.const fc ls) a) b) e₁ ∧ c.TrExpr e₁ e' := by
  let .app hb1 hb2 hf hb := he
  let .app ha1 ha2 hf ha := hf
  let .const h1 h2 h3 := hf
  unfold reduceBinNatPred
  refine (whnf.WF ha).bind fun a₁ _ _ ⟨a1, _, a2, a3⟩ => ?_
  split <;> [rename_i v1 h; exact .pure nofun]; cases (rawNatLitExt?.WF h a2).2
  refine (whnf.WF hb).bind fun b₁ _ _ ⟨b1, _, b2, b3⟩ => ?_
  split <;> [rename_i v2 h; exact .pure nofun]; cases (rawNatLitExt?.WF h b2).2
  refine .pure ?_; rintro _ ⟨⟩; refine ⟨fun _ _ _ => .boolLit, ?_⟩
  have ⟨ci, c1, _⟩ := c.trenv.find?_iff.2 ⟨_, h1⟩
  have ⟨_, c3⟩ := c.safePrimitives c1 hprim
  have ⟨_, d1, d2, d3⟩ := c.trenv.find?_uniq c1 h1
  simp [c3] at d2; simp [← d2] at h3; simp [h3] at h2; subst h2
  have := heval ⟨_, h1⟩ v1 v2 |>.instL (U' := c.lparams.length) (ls := []) nofun
  simp [VExpr.instL] at this
  refine ⟨_, (TrExprS.boolLit c.hasPrimitives ?_ _).1, ?_⟩
  · let ⟨_, H⟩ := this
    exact VExpr.WF.boolLit_has_type c.Ewf c.hasPrimitives (Γ := []) trivial ⟨_, H.hasType.2⟩
  refine this.weak0 c.Ewf (Γ := c.vlctx.toCtx) |>.symm.trans c.Ewf c.Δwf ?_
  have a3 := a3.of_r c.Ewf c.Δwf ha2
  have b3 := b3.of_r c.Ewf c.Δwf hb2
  have := ha1.appDF a3 |>.toU.of_r c.Ewf c.Δwf hb1
  exact  ⟨_, .appDF this b3⟩

theorem reduceNat.WF {c : VContext} (he : c.TrExprS e e') :
    RecM.WF c s (reduceNat e) fun oe _ => ∀ e₁, oe = some e₁ →
      c.FVarsBelow e e₁ ∧ c.TrExpr e₁ e' := by
  generalize hP : (fun oe => _) = P
  refine let prims := _; have hprims : Environment.primitives = .ofList prims := rfl; ?_
  replace hprims {a} : Environment.primitives.contains a ↔ a ∈ prims := by
    simp [hprims, NameSet.contains, NameSet.ofList]
  unfold reduceNat; extract_lets nargs F1 fn
  cases h1 : nargs == 1 <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · cases nargs == 2 <;> [exact hP ▸ .pure nofun; simp only [↓reduceIte]]
    split <;> [rename_i f ls a b; exact hP ▸ .pure nofun]
    have hfun guard {g fc G} [DecidableRel guard] (hprim : fc ∈ prims)
        (heval : c.venv.ReflectsNatNatNat fc g) (hG : RecM.WF c s G P) :
        RecM.WF c s (do if f == fc then {return ← reduceBinNatOpG guard g a b}; G) P := by
      split <;> [rename_i h; exact hG]
      simp at h ⊢; subst h
      exact hP ▸ reduceBinNatOpG.WF he (hprims.2 hprim) heval
    have hpred {g fc G} (hprim : fc ∈ prims)
        (heval : c.venv.ReflectsNatNatBool fc g) (hG : RecM.WF c s G P) :
        RecM.WF c s (do if f == fc then {return ← reduceBinNatPred g a b}; G) P := by
      split <;> [rename_i h; exact hG]
      simp at h ⊢; subst h
      exact hP ▸ reduceBinNatPred.WF he (hprims.2 hprim) heval
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natAdd
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natSub
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natMul
    apply hfun _ (by simp [prims]) c.hasPrimitives.natPow
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natGcd
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natMod
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natDiv
    apply hpred (by simp [prims]) c.hasPrimitives.natBEq
    apply hpred (by simp [prims]) c.hasPrimitives.natBLE
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natLAnd
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natLOr
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natXor
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natShiftLeft
    apply hfun (fun _ _ => False) (by simp [prims]) c.hasPrimitives.natShiftRight
    exact hP ▸ .pure nofun
  · split <;> [rename_i h2; exact hP ▸ .pure nofun]
    simp [nargs, Expr.getAppNumArgs_eq] at h1; subst fn
    let .app f a := e; simp [Expr.appFn!, Expr.structuralEq_const] at h2 ⊢; subst h2
    let .app ha1 ha2 hf ha := he
    let .const h1 h2 h3 := hf
    refine (whnf.WF ha).bind fun a₁ _ _ ⟨a1, _, a2, a3⟩ => ?_
    split <;> [rename_i n h; exact hP ▸ .pure nofun]
    obtain ⟨hn, rfl⟩ := rawNatLitExt?.WF h a2
    refine hP ▸ .pure ?_; rintro _ ⟨⟩; refine ⟨fun _ _ _ => trivial, ?_⟩
    have ⟨ci, c1, _⟩ := c.trenv.find?_iff.2 ⟨_, h1⟩
    have ⟨c2, c3⟩ := c.safePrimitives c1 <| hprims.2 (by simp [prims])
    have ⟨d1, d2, d3⟩ := c.trenv.find?_uniq c1 h1; cases h2
    refine have ⟨p1, p2⟩ := TrExprS.natLit c.hasPrimitives hn _; ⟨_, p1, ?_⟩
    refine p2.toU.symm.trans c.Ewf c.Δwf ?_
    exact ⟨_, ha1.appDF <| a3.of_r c.Ewf c.Δwf ha2⟩

theorem reduceProjCore.WF {c : VContext} {s : VState} (he : c.TrExprS (.proj n i e) e') :
    RecM.WF c s (reduceProjCore i e) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.FVarsBelow (.proj n i e) e₁ ∧ c.TrExpr e₁ e' := by
  let .proj (e' := major) heMajor hproj := he
  obtain ⟨view, levels, params, _hviewName, hsemantic⟩ := hproj
  obtain ⟨code, hcode, hresult, hprojector⟩ := hsemantic.program
  have finish {normal : Expr} {state : VState}
      (hbelow : c.FVarsBelow e normal)
      (htr : c.TrExpr normal major) :
      RecM.WF c state
        (normal.withApp fun mk args => do
          let .const mkC _ := mk | return none
          let env ← getEnv
          let .ctorInfo mkInfo ← env.get mkC | return none
          return args[mkInfo.numParams + i]?) (fun oe _ =>
            ∀ e₁, oe = some e₁ →
              c.FVarsBelow (.proj n i e) e₁ ∧ c.TrExpr e₁ e') := by
    rw [Expr.withApp_eq]
    split
    · rename_i mkC hostLevels hheadShape
      obtain ⟨runtimeMajor, hnormalS, hnormalEq⟩ := htr
      have ⟨runtimeHead, hstack⟩ := AppStack.build
        (normal.mkAppList_getAppArgsList ▸ hnormalS)
      have hhead := hstack.tr
      rw [hheadShape] at hhead
      let .const (us' := runtimeLevels) _hconst _hlevelsMap
          _hlevelsLength := hhead
      obtain ⟨runtimeArgs, hargsTr, hfull⟩ := hstack.argsTranslation
      rw [normal.mkAppList_getAppArgsList] at hfull
      have hfullEq := hfull.uniq c.Ewf (.refl c.Ewf c.Δwf) hnormalS
      have hmajorEq := hfullEq.trans c.Ewf c.Δwf hnormalEq
      refine .getEnv ?_
      refine (M.WF.liftExcept envGet.WF).lift.bind fun _ci _ _ hfind => ?_
      split
      · rename_i mkInfo
        refine .pure ?_
        intro selected hselected
        have hconstructorHead : c.venv.ConstructorHead mkC :=
          c.projectionReady.constructorHead mkC mkInfo hfind
        have hconstructorName : mkC = view.constructorName :=
          c.Ewf.registeredStructureHeadInversion.constructor_name_inv
            c.Δwf hsemantic hconstructorHead rfl hmajorEq
        have hnumParams : mkInfo.numParams = view.nparams :=
          c.projectionReady.constructorNumParams view mkInfo
            hsemantic.viewWF (by
              intro hfields
              have hspecialized :
                  view.specializedFields levels params = [] := by
                simp [VStructureView.specializedFields, hfields]
              have hcodesLength :
                  (view.projectionCodes levels params).length = 0 := by
                rw [view.projectionCodes_length levels params, hspecialized]
                rfl
              have hcodesNil : view.projectionCodes levels params = [] :=
                List.length_eq_zero_iff.mp hcodesLength
              rw [hcodesNil] at hcode
              contradiction) (by
              rw [← hconstructorName]
              exact hfind)
        have hselectedList :
            normal.getAppArgsList[mkInfo.numParams + i]? = some selected := by
          rw [← Expr.getAppArgs_toList, Array.getElem?_toList]
          exact hselected
        obtain ⟨runtimeField, hfieldGet, hfieldTr⟩ :=
          Lean4Lean.List.Forall₂.getElem?_left hargsTr hselectedList
        have hfieldGetCanonical :
            runtimeArgs[view.nparams + i]? = some runtimeField := by
          rw [← hnumParams]
          exact hfieldGet
        obtain ⟨alignment⟩ :=
          c.Ewf.registeredStructureHeadInversion.constructor_inv
            c.Δwf hsemantic hconstructorHead hcode rfl
              hfieldGetCanonical hmajorEq
        have hiota := hsemantic.projector_constructor_aligned
          c.Ewf c.Δwf hcode hprojector alignment
        have hmajorTyped := hmajorEq.of_r c.Ewf c.Δwf hsemantic.majorType
        have hprojectorCongr : c.IsDefEqU
            (.app code.projector
              (VExpr.appN (.const mkC runtimeLevels) runtimeArgs))
            (.app code.projector major) :=
          ⟨_, hprojector.appDF hmajorTyped⟩
        have hfieldTarget : c.IsDefEqU runtimeField e' := by
          rw [hresult]
          exact hiota.symm.trans c.Ewf c.Δwf hprojectorCongr
        refine ⟨?_, ⟨runtimeField, hfieldTr, hfieldTarget⟩⟩
        intro P hP hprojFv
        exact FVarsIn.getAppArgsList (hbelow P hP hprojFv)
          (List.mem_of_getElem? hselectedList)
      · exact .pure nofun
    · exact .pure nofun
  unfold reduceProjCore
  extract_lets c₀ jp
  suffices hjp : ∀ {normal : Expr} {state : VState}, c.FVarsBelow e normal →
      c.TrExpr normal major → RecM.WF c state (jp () normal) (fun oe _ =>
        ∀ e₁, oe = some e₁ → c.FVarsBelow (.proj n i e) e₁ ∧ c.TrExpr e₁ e') by
    unfold c₀
    split
    · let .lit _ hconstructorS := heMajor
      refine (whnf.WF hconstructorS).bind fun expanded _ _ hexpanded => ?_
      refine hjp ?_ hexpanded.2
      exact FVarsBelow.trans (fun _ _ _ => FVarsIn.strLitToConstructor) hexpanded.1
    · exact hjp .rfl (heMajor.trExpr c.Ewf c.Δwf)
  intro normal state hbelow htr
  exact finish hbelow htr

theorem reduceProj.WF {c : VContext} {s : VState} (he : c.TrExprS (.proj n i e) e') :
    RecM.WF c s (reduceProj i e cheapProj) fun oe _ =>
      ∀ e₁, oe = some e₁ → c.FVarsBelow (.proj n i e) e₁ ∧ c.TrExpr e₁ e' := by
  unfold reduceProj
  have .proj (e' := s) a1 a2 := he
  refine .bind (Q := fun e₁ _ => c.FVarsBelow e e₁ ∧ c.TrExpr e₁ s) ?_ fun _ _ _ ⟨h1, h2⟩ => ?_
  · split <;> [exact whnfCore.WF a1; exact whnf.WF a1]
  have ⟨_, b1, b2⟩ := h2.proj c.Ewf c.Δwf a2
  refine (reduceProjCore.WF b1).mono fun _ _ _ H _ eq => ?_
  have ⟨c1, c2⟩ := H _ eq; exact ⟨h1.trans c1, c2.defeq c.Ewf c.Δwf b2⟩
