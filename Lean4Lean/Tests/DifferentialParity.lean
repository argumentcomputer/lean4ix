/-
Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: MIT OR Apache-2.0
-/

import Lean4Lean.TypeChecker

/-!
# Differential-parity regressions

These tests make execution-order differences observable when the final return
value alone cannot distinguish Lean4Lean from the Lean kernel. They also pin
the exact expression structure and hashes produced by cache-sensitive universe
substitution.
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

private def levelParam : Name := `p
private def replacementParam : Name := `q
private def replacementLevel : Level := .param replacementParam
private def levelOne : Level := .succ .zero

private def rawMaxLevel : Level :=
  .max (.succ (.param levelParam)) levelOne

private def rawIMaxLevel : Level :=
  .imax levelOne (.param levelParam)

private def addUnchecked (env : Environment) (decl : Declaration) :
    Except Kernel.Exception Environment :=
  env.addDeclCore 0 0 decl none (doCheck := false)

private def levelAxiom (name : Name) (level : Level) : Declaration :=
  .axiomDecl {
    name
    levelParams := [levelParam]
    type := .sort level
    isUnsafe := false
  }

private def levelDefinition (name : Name) (level : Level) : Declaration :=
  .defnDecl {
    name
    levelParams := [levelParam]
    type := .sort (.succ level)
    value := .sort level
    hints := .regular 0
    safety := .safe
  }

private def expectStructure (label : String) (actual expected : Expr) : MetaM Unit := do
  unless Expr.structuralEq actual expected do
    throwError "{label}: expected {repr expected}, got {repr actual}"

private def expectHash (label : String) (actual expected : Expr) : MetaM Unit := do
  unless actual.hash == expected.hash do
    throwError "{label}: expected hash {expected.hash}, got {actual.hash}"

/- The declarations below are added only to a local environment and bypass
checking so their raw, deliberately unnormalized level syntax reaches both
kernel implementations unchanged. They are never installed in the module's
global environment. -/
run_meta do
  let maxName := `Lean4Lean.Tests.DifferentialParity.maxLevelProbe
  let imaxName := `Lean4Lean.Tests.DifferentialParity.imaxLevelProbe
  let cacheName := `Lean4Lean.Tests.DifferentialParity.levelCacheProbe
  let .ok env₁ := addUnchecked (← getEnv) (levelAxiom maxName rawMaxLevel)
    | throwError "could not add the max-level parity probe"
  let .ok env₂ := addUnchecked env₁ (levelAxiom imaxName rawIMaxLevel)
    | throwError "could not add the imax-level parity probe"
  let .ok env := addUnchecked env₂ (levelDefinition cacheName rawMaxLevel)
    | throwError "could not add the unfold-cache parity probe"

  let maxExpr := Expr.const maxName [replacementLevel]
  let imaxExpr := Expr.const imaxName [replacementLevel]
  let cacheExpr := Expr.const cacheName [replacementLevel]
  let expectedMax := Expr.sort (.max (.succ replacementLevel) levelOne)
  let expectedIMax := Expr.sort replacementLevel

  -- Keep both examples discriminating until Lean's public constructors match
  -- the C++ kernel and the compatibility wrappers can be removed.
  let stdMax := (Expr.sort rawMaxLevel).instantiateLevelParams
    [levelParam] [replacementLevel]
  let stdIMax := (Expr.sort rawIMaxLevel).instantiateLevelParams
    [levelParam] [replacementLevel]
  if Expr.structuralEq stdMax expectedMax then
    throwError "the stdlib max substitution now matches the kernel; remove the C++ compatibility path"
  if Expr.structuralEq stdIMax expectedIMax then
    throwError "the stdlib imax substitution now matches the kernel; remove the C++ compatibility path"

  let .ok kernelMax := Kernel.check env {} maxExpr
    | throwError "the Lean kernel rejected the max-level parity probe"
  let .ok kernelIMax := Kernel.check env {} imaxExpr
    | throwError "the Lean kernel rejected the imax-level parity probe"
  let .ok modelMax := TypeChecker.M.run env.toKernelEnv
      (lparams := [replacementParam]) (x := TypeChecker.checkType maxExpr)
    | throwError "Lean4Lean rejected the max-level parity probe"
  let .ok modelIMax := TypeChecker.M.run env.toKernelEnv
      (lparams := [replacementParam]) (x := TypeChecker.checkType imaxExpr)
    | throwError "Lean4Lean rejected the imax-level parity probe"

  expectStructure "Lean kernel max substitution" kernelMax expectedMax
  expectStructure "Lean4Lean max substitution" modelMax kernelMax
  expectHash "Lean4Lean max substitution" modelMax kernelMax
  expectStructure "Lean kernel imax substitution" kernelIMax expectedIMax
  expectStructure "Lean4Lean imax substitution" modelIMax kernelIMax
  expectHash "Lean4Lean imax substitution" modelIMax kernelIMax

  let .ok kernelWhnf := Kernel.whnf env {} cacheExpr
    | throwError "the Lean kernel rejected the unfold-cache parity probe"
  expectStructure "Lean kernel unfolded value" kernelWhnf expectedMax
  let context : TypeChecker.Context := {
    env := env.toKernelEnv
    lparams := [replacementParam]
  }
  match (TypeChecker.whnf cacheExpr context).run {} with
  | .error _ =>
    throwError "Lean4Lean rejected the unfold-cache parity probe"
  | .ok (modelWhnf, state) =>
    expectStructure "Lean4Lean unfolded value" modelWhnf kernelWhnf
    expectHash "Lean4Lean unfolded value" modelWhnf kernelWhnf
    let some unfolded := state.unfold[cacheExpr]?
      | throwError "Lean4Lean did not cache the instantiated definition value"
    expectStructure "Lean4Lean unfold cache" unfolded kernelWhnf
    expectHash "Lean4Lean unfold cache" unfolded kernelWhnf
    let some cachedWhnf := state.whnfCache[cacheExpr]?
      | throwError "Lean4Lean did not cache the weak-head normal form"
    expectStructure "Lean4Lean WHNF cache" cachedWhnf kernelWhnf
    expectHash "Lean4Lean WHNF cache" cachedWhnf kernelWhnf

end Lean4Lean.Tests.DifferentialParity
