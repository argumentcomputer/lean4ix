/-
This file is derived from lean4lean and has been modified by Argument Computer Corporation.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/

import Lean4Lean.Verify.Environment

/-!
# Primitive verification regression pins

The `Nat.add` declaration path is the first UP6 primitive slice that must stay
independent of the generic admitted primitive-recognizer boundary.
-/

open Lean Lean.Elab.Command

private def directConstants : Lean.ConstantInfo → Array Lean.Name
  | .axiomInfo v => v.type.getUsedConstants
  | .defnInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .thmInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .quotInfo _ => #[]
  | .ctorInfo v => v.type.getUsedConstants
  | .recInfo v => v.type.getUsedConstants
  | .inductInfo v => v.type.getUsedConstants ++ v.ctors

private partial def dependencyClosure (env : Lean.Environment) :
    List Lean.Name → Lean.NameSet → Lean.NameSet
  | [], seen => seen
  | name :: rest, seen =>
    if seen.contains name then
      dependencyClosure env rest seen
    else
      let seen := seen.insert name
      match env.find? name with
      | none => dependencyClosure env rest seen
      | some info =>
        dependencyClosure env ((directConstants info).toList ++ rest) seen

run_cmd do
  let env ← getEnv
  let root := ``Lean4Lean.addDefinition.WF_safe_natAdd
  let genericBoundary := ``Lean4Lean.checkPrimitiveDef.WF
  let closure := dependencyClosure env [root] {}
  if closure.contains genericBoundary then
    throwError "the direct Nat.add declaration certificate regressed through checkPrimitiveDef.WF"
  let some liveInfo := env.find? ``Lean4Lean.addDefinition.WF
    | throwError "addDefinition.WF is missing"
  unless (directConstants liveInfo).contains root do
    throwError "addDefinition.WF no longer dispatches directly to the Nat.add certificate"
  let sorryCarriers := env.constants.toList.foldl (init := #[]) fun found (name, info) =>
    if closure.contains name && (directConstants info).contains ``sorryAx then
      found.push name
    else
      found
  let expectedSorryCarriers : Array Lean.Name := #[
    ``Lean4Lean.VEnv.IsDefEqU.sort_inv,
    ``Lean4Lean.VEnv.IsDefEqU.sort_forallE_inv,
    ``Lean4Lean.VEnv.WF.registeredStructureHeadInversion,
    ``Lean4Lean.VEnv.IsDefEqU.weakN_iff,
    ``Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified,
    ``Lean4Lean.TypeChecker.Inner.reduceRecursor.WF]
  let observedSet : Lean.NameSet := sorryCarriers.foldl (·.insert ·) {}
  let expectedSet : Lean.NameSet := expectedSorryCarriers.foldl (·.insert ·) {}
  let added := sorryCarriers.filter (!expectedSet.contains ·)
  let removed := expectedSorryCarriers.filter (!observedSet.contains ·)
  unless added.isEmpty && removed.isEmpty do
    throwError m!"Nat.add direct-certificate sorry closure changed; added: {added}; removed: {removed}"
  logInfo "Nat.add direct certificate excludes checkPrimitiveDef.WF and retains exactly six known upstream proof dependencies"
