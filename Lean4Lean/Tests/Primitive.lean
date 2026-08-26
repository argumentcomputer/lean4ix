/-
This file is derived from lean4lean and has been modified by Argument Computer Corporation.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/

import Lean4Lean.Verify.Environment

/-!
# Primitive verification regression pins

The direct elementary-Nat declaration paths must stay independent of the
generic admitted primitive-recognizer boundary.
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
  let predRoot := ``Lean4Lean.addDefinition.WF_safe_natPred
  let subRoot := ``Lean4Lean.addDefinition.WF_safe_natSub
  let mulRoot := ``Lean4Lean.addDefinition.WF_safe_natMul
  let powRoot := ``Lean4Lean.addDefinition.WF_safe_natPow
  let genericBoundary := ``Lean4Lean.checkPrimitiveDef.WF
  let closure := dependencyClosure env [root] {}
  let predClosure := dependencyClosure env [predRoot] {}
  let subClosure := dependencyClosure env [subRoot] {}
  let mulClosure := dependencyClosure env [mulRoot] {}
  let powClosure := dependencyClosure env [powRoot] {}
  if closure.contains genericBoundary then
    throwError "the direct Nat.add declaration certificate regressed through checkPrimitiveDef.WF"
  if predClosure.contains genericBoundary then
    throwError "the direct Nat.pred declaration certificate regressed through checkPrimitiveDef.WF"
  if subClosure.contains genericBoundary then
    throwError "the direct Nat.sub declaration certificate regressed through checkPrimitiveDef.WF"
  if mulClosure.contains genericBoundary then
    throwError "the direct Nat.mul declaration certificate regressed through checkPrimitiveDef.WF"
  if powClosure.contains genericBoundary then
    throwError "the direct Nat.pow declaration certificate regressed through checkPrimitiveDef.WF"
  let some liveInfo := env.find? ``Lean4Lean.addDefinition.WF
    | throwError "addDefinition.WF is missing"
  unless (directConstants liveInfo).contains root do
    throwError "addDefinition.WF no longer dispatches directly to the Nat.add certificate"
  unless (directConstants liveInfo).contains predRoot do
    throwError "addDefinition.WF no longer dispatches directly to the Nat.pred certificate"
  unless (directConstants liveInfo).contains subRoot do
    throwError "addDefinition.WF no longer dispatches directly to the Nat.sub certificate"
  unless (directConstants liveInfo).contains mulRoot do
    throwError "addDefinition.WF no longer dispatches directly to the Nat.mul certificate"
  unless (directConstants liveInfo).contains powRoot do
    throwError "addDefinition.WF no longer dispatches directly to the Nat.pow certificate"
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
  let predSorryCarriers := env.constants.toList.foldl (init := #[])
      fun found (name, info) =>
    if predClosure.contains name && (directConstants info).contains ``sorryAx then
      found.push name
    else
      found
  let predObservedSet : Lean.NameSet :=
    predSorryCarriers.foldl (·.insert ·) {}
  let predAdded := predSorryCarriers.filter (!expectedSet.contains ·)
  let predRemoved := expectedSorryCarriers.filter (!predObservedSet.contains ·)
  unless predAdded.isEmpty && predRemoved.isEmpty do
    throwError m!"Nat.pred direct-certificate sorry closure changed; added: {predAdded}; removed: {predRemoved}"
  let subSorryCarriers := env.constants.toList.foldl (init := #[])
      fun found (name, info) =>
    if subClosure.contains name && (directConstants info).contains ``sorryAx then
      found.push name
    else
      found
  let subObservedSet : Lean.NameSet :=
    subSorryCarriers.foldl (·.insert ·) {}
  let subAdded := subSorryCarriers.filter (!expectedSet.contains ·)
  let subRemoved := expectedSorryCarriers.filter (!subObservedSet.contains ·)
  unless subAdded.isEmpty && subRemoved.isEmpty do
    throwError m!"Nat.sub direct-certificate sorry closure changed; added: {subAdded}; removed: {subRemoved}"
  let mulSorryCarriers := env.constants.toList.foldl (init := #[])
      fun found (name, info) =>
    if mulClosure.contains name && (directConstants info).contains ``sorryAx then
      found.push name
    else
      found
  let mulObservedSet : Lean.NameSet :=
    mulSorryCarriers.foldl (·.insert ·) {}
  let mulAdded := mulSorryCarriers.filter (!expectedSet.contains ·)
  let mulRemoved := expectedSorryCarriers.filter (!mulObservedSet.contains ·)
  unless mulAdded.isEmpty && mulRemoved.isEmpty do
    throwError m!"Nat.mul direct-certificate sorry closure changed; added: {mulAdded}; removed: {mulRemoved}"
  let powSorryCarriers := env.constants.toList.foldl (init := #[])
      fun found (name, info) =>
    if powClosure.contains name && (directConstants info).contains ``sorryAx then
      found.push name
    else
      found
  let powObservedSet : Lean.NameSet :=
    powSorryCarriers.foldl (·.insert ·) {}
  let powAdded := powSorryCarriers.filter (!expectedSet.contains ·)
  let powRemoved := expectedSorryCarriers.filter (!powObservedSet.contains ·)
  unless powAdded.isEmpty && powRemoved.isEmpty do
    throwError m!"Nat.pow direct-certificate sorry closure changed; added: {powAdded}; removed: {powRemoved}"
  logInfo "Nat.add, Nat.pred, Nat.sub, Nat.mul, and Nat.pow direct certificates exclude checkPrimitiveDef.WF and each retain exactly six known upstream proof dependencies"
