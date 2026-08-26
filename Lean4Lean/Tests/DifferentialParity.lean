/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Lean4Lean.TypeChecker

/-!
# Differential-parity regressions

These tests make execution-order differences observable when the final return
value alone cannot distinguish Lean4Lean from the Lean kernel.
-/

namespace Lean4Lean.Tests.DifferentialParity

open Lean

private def leftHead : Expr := .const `up5LeftHead []
private def rightHead : Expr := .const `up5RightHead []

private def shorterApp : Expr :=
  .app leftHead (.sort .zero)

private def longerApp : Expr :=
  .app (.app rightHead (.sort .zero)) (.sort .zero)

/- `isDefEqApp` must compare the distinct heads before rejecting the unequal
argument counts. The controlled comparison records its invocation in the
failure set, making the otherwise return-value-invisible order observable. -/
run_meta do
  let context : TypeChecker.Context := { env := (← getEnv).toKernelEnv }
  let methods : TypeChecker.Methods :=
    { TypeChecker.Methods.withFuel 0 with
      isDefEqCore := fun t s => do
        modify fun state => { state with failure := state.failure.insert (t, s) }
        return true }
  match (TypeChecker.Inner.isDefEqApp shorterApp longerApp methods context).run {} with
  | .ok (false, state) =>
    unless state.failure.contains (leftHead, rightHead) do
      throwError "isDefEqApp rejected unequal argument counts before comparing heads"
  | .ok (true, _) =>
    throwError "isDefEqApp accepted applications with unequal argument counts"
  | .error _ =>
    throwError "isDefEqApp order probe raised an unexpected kernel exception"

end Lean4Lean.Tests.DifferentialParity
