/-
This file is derived from lean4lean and has been modified by Argument Computer Corporation.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/

import Lean4Lean.Instantiate
import Lean4Lean.TypeChecker
import Lean4Lean.Verify.Expr

/-!
# Trust-repair regressions

These probes retain the concrete inputs that falsified the former unconditional
runtime contracts.  They test the mismatches directly, then prove that the
repaired contracts' hypotheses exclude them.  No probe invokes an operation
outside its runtime domain.
-/

namespace Lean4Lean.Tests.TrustRepair

open Lean

private def simultaneousSource : Expr := .bvar 0

private def simultaneousSubst : Array Expr :=
  #[.bvar 0, .sort .zero]

/- Simultaneous runtime substitution and the sequential list model disagree
on this open substituend. -/
run_meta do
  unless simultaneousSource.instantiate simultaneousSubst == .bvar 0 do
    throwError "unexpected simultaneous-substitution result"
  unless simultaneousSource.instantiateList simultaneousSubst.toList == .sort .zero do
    throwError "unexpected sequential-substitution result"

/-- The repaired bridge cannot be applied to the simultaneous/sequential
counterexample: neither the source nor every substituend is closed. -/
example :
    ¬ (simultaneousSource.looseBVarRange' = 0 ∨
      ∀ a ∈ simultaneousSubst, a.looseBVarRange' = 0) := by
  simp [simultaneousSource, simultaneousSubst, Expr.looseBVarRange']

private def abstractionId : FVarId := ⟨`trustRepairX⟩

/- Runtime abstraction preserves an existing loose bvar, while the old
sequential model shifts it. -/
run_meta do
  let targets : Array Expr := #[.fvar abstractionId]
  unless (Expr.bvar 0).abstract targets == .bvar 0 do
    throwError "runtime abstraction unexpectedly changed a loose bvar"
  unless (Expr.bvar 0).abstractList [abstractionId] == .bvar 1 do
    throwError "unexpected sequential abstraction of a loose bvar"

/- Runtime abstraction chooses the final duplicate target, whereas sequential
abstraction shifts the result of the first match. -/
run_meta do
  let targets : Array Expr := #[.fvar abstractionId, .fvar abstractionId]
  unless (Expr.fvar abstractionId).abstract targets == .bvar 0 do
    throwError "unexpected runtime duplicate-abstraction result"
  unless (Expr.fvar abstractionId).abstractList [abstractionId, abstractionId] == .bvar 1 do
    throwError "unexpected sequential duplicate-abstraction result"

example :
    ¬ ([abstractionId] = [] ∨ (Expr.bvar 0).looseBVarRange' = 0) := by
  simp [Expr.looseBVarRange']

example : ¬ [abstractionId, abstractionId].Nodup := by
  simp

/-- The old loose-bvar contradiction used the first index outside the packed
20-bit range.  It is outside the hereditary domain of the repaired bridge. -/
private def overflowBVar : Expr := .bvar (2 ^ 20 - 1)

example : overflowBVar.looseBVarRange' = 2 ^ 20 := by
  simp [overflowBVar, Expr.looseBVarRange']

example : ¬ overflowBVar.BVarBounded := by
  simp [overflowBVar, Expr.BVarBounded]

/-- The partial range operations' former out-of-domain examples cannot supply
the repaired bounds. -/
example : ¬ (2 : Nat) ≤ 1 := by omega

example : ¬ (2 : Nat) ≤ (#[Expr.sort .zero]).size := by decide

/-- Arbitrary `PersistentArray` records are not assumed to have the list/push
semantics of arrays constructed from `empty` and `push`. -/
private def malformedPersistentArray : PersistentArray Nat where
  root := .leaf #[0]
  tail := #[]
  size := 0
  shift := PersistentArray.initShift
  tailOff := 0

example : ¬ PersistentArray.WF malformedPersistentArray := by
  intro h
  have hlen := h.toList'_length
  simp [malformedPersistentArray, PersistentArray.toList',
    PersistentArrayNode.toList'] at hlen

/- The simple checker path still accepts an ordinary closed sort and rejects
a loose bound variable explicitly. -/
run_meta do
  let env := (← getEnv).toKernelEnv
  match TypeChecker.M.run env (x := TypeChecker.checkType (.sort .zero)) with
  | .ok (.sort (.succ .zero)) => pure ()
  | .ok type => throwError "closed sort inferred unexpected type {repr type}"
  | .error error =>
    throwError "closed sort was rejected: {← (error.toMessageData {}).toString}"
  match TypeChecker.M.run env (x := TypeChecker.checkType (.bvar 0)) with
  | .error _ => pure ()
  | .ok type => throwError "loose bvar was accepted with type {repr type}"

/- Both the substituting and no-op beta paths retain their ordinary results
after removing cached loose-bvar metadata as semantic authority. -/
run_meta do
  let substituting : Expr :=
    .app (.lam `x (.sort .zero) (.bvar 0) .default) (.sort .zero)
  unless substituting.cheapBetaReduce == .sort .zero do
    throwError "substituting cheap beta regression"
  let constant : Expr :=
    .app (.lam `x (.sort .zero) (.sort .zero) .default) (.const ``Nat [])
  unless constant.cheapBetaReduce == .sort .zero do
    throwError "constant-body cheap beta regression"

end Lean4Lean.Tests.TrustRepair
