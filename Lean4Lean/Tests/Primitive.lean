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
  let shiftLeftRoot := ``Lean4Lean.addDefinition.WF_safe_natShiftLeft
  let shiftRightRoot := ``Lean4Lean.addDefinition.WF_safe_natShiftRight
  let charOfNatRoot := ``Lean4Lean.addDefinition.WF_safe_charOfNat
  let stringOfListRoot := ``Lean4Lean.addDefinition.WF_safe_stringOfList
  let beqRoot := ``Lean4Lean.addDefinition.WF_safe_natBEq
  let bleRoot := ``Lean4Lean.addDefinition.WF_safe_natBLE
  let modRoot := ``Lean4Lean.addDefinition.WF_safe_natMod
  let divRoot := ``Lean4Lean.addDefinition.WF_safe_natDiv
  let gcdRoot := ``Lean4Lean.addDefinition.WF_safe_natGcd
  let genericBoundary := ``Lean4Lean.checkPrimitiveDef.WF
  let closure := dependencyClosure env [root] {}
  let predClosure := dependencyClosure env [predRoot] {}
  let subClosure := dependencyClosure env [subRoot] {}
  let mulClosure := dependencyClosure env [mulRoot] {}
  let powClosure := dependencyClosure env [powRoot] {}
  let shiftLeftClosure := dependencyClosure env [shiftLeftRoot] {}
  let shiftRightClosure := dependencyClosure env [shiftRightRoot] {}
  let charOfNatClosure := dependencyClosure env [charOfNatRoot] {}
  let stringOfListClosure := dependencyClosure env [stringOfListRoot] {}
  let beqClosure := dependencyClosure env [beqRoot] {}
  let bleClosure := dependencyClosure env [bleRoot] {}
  let modClosure := dependencyClosure env [modRoot] {}
  let divClosure := dependencyClosure env [divRoot] {}
  let gcdClosure := dependencyClosure env [gcdRoot] {}
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
  if shiftLeftClosure.contains genericBoundary then
    throwError "the direct Nat.shiftLeft declaration certificate regressed through checkPrimitiveDef.WF"
  if shiftRightClosure.contains genericBoundary then
    throwError "the direct Nat.shiftRight declaration certificate regressed through checkPrimitiveDef.WF"
  if charOfNatClosure.contains genericBoundary then
    throwError "the direct Char.ofNat declaration certificate regressed through checkPrimitiveDef.WF"
  if stringOfListClosure.contains genericBoundary then
    throwError "the direct String.ofList declaration certificate regressed through checkPrimitiveDef.WF"
  if beqClosure.contains genericBoundary then
    throwError "the direct Nat.beq declaration certificate regressed through checkPrimitiveDef.WF"
  if bleClosure.contains genericBoundary then
    throwError "the direct Nat.ble declaration certificate regressed through checkPrimitiveDef.WF"
  if modClosure.contains genericBoundary then
    throwError "the direct Nat.mod declaration certificate regressed through checkPrimitiveDef.WF"
  if divClosure.contains genericBoundary then
    throwError "the direct Nat.div declaration certificate regressed through checkPrimitiveDef.WF"
  if gcdClosure.contains genericBoundary then
    throwError "the direct Nat.gcd declaration certificate regressed through checkPrimitiveDef.WF"
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
  unless (directConstants liveInfo).contains shiftLeftRoot do
    throwError "addDefinition.WF no longer dispatches directly to the Nat.shiftLeft certificate"
  unless (directConstants liveInfo).contains shiftRightRoot do
    throwError "addDefinition.WF no longer dispatches directly to the Nat.shiftRight certificate"
  unless (directConstants liveInfo).contains charOfNatRoot do
    throwError "addDefinition.WF no longer dispatches directly to the Char.ofNat certificate"
  unless (directConstants liveInfo).contains stringOfListRoot do
    throwError "addDefinition.WF no longer dispatches directly to the String.ofList certificate"
  unless (directConstants liveInfo).contains beqRoot do
    throwError "addDefinition.WF no longer dispatches directly to the Nat.beq certificate"
  unless (directConstants liveInfo).contains bleRoot do
    throwError "addDefinition.WF no longer dispatches directly to the Nat.ble certificate"
  unless (directConstants liveInfo).contains modRoot do
    throwError "addDefinition.WF no longer dispatches directly to the Nat.mod certificate"
  unless (directConstants liveInfo).contains divRoot do
    throwError "addDefinition.WF no longer dispatches directly to the Nat.div certificate"
  unless (directConstants liveInfo).contains gcdRoot do
    throwError "addDefinition.WF no longer dispatches directly to the Nat.gcd certificate"
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
  let shiftLeftSorryCarriers := env.constants.toList.foldl (init := #[])
      fun found (name, info) =>
    if shiftLeftClosure.contains name && (directConstants info).contains ``sorryAx then
      found.push name
    else
      found
  let shiftLeftObservedSet : Lean.NameSet :=
    shiftLeftSorryCarriers.foldl (·.insert ·) {}
  let shiftLeftAdded := shiftLeftSorryCarriers.filter (!expectedSet.contains ·)
  let shiftLeftRemoved :=
    expectedSorryCarriers.filter (!shiftLeftObservedSet.contains ·)
  unless shiftLeftAdded.isEmpty && shiftLeftRemoved.isEmpty do
    throwError m!"Nat.shiftLeft direct-certificate sorry closure changed; added: {shiftLeftAdded}; removed: {shiftLeftRemoved}"
  let shiftRightSorryCarriers := env.constants.toList.foldl (init := #[])
      fun found (name, info) =>
    if shiftRightClosure.contains name &&
        (directConstants info).contains ``sorryAx then
      found.push name
    else
      found
  let shiftRightObservedSet : Lean.NameSet :=
    shiftRightSorryCarriers.foldl (·.insert ·) {}
  let shiftRightAdded :=
    shiftRightSorryCarriers.filter (!expectedSet.contains ·)
  let shiftRightRemoved :=
    expectedSorryCarriers.filter (!shiftRightObservedSet.contains ·)
  unless shiftRightAdded.isEmpty && shiftRightRemoved.isEmpty do
    throwError m!"Nat.shiftRight direct-certificate sorry closure changed; added: {shiftRightAdded}; removed: {shiftRightRemoved}"
  let charOfNatSorryCarriers := env.constants.toList.foldl (init := #[])
      fun found (name, info) =>
    if charOfNatClosure.contains name &&
        (directConstants info).contains ``sorryAx then
      found.push name
    else
      found
  let charOfNatObservedSet : Lean.NameSet :=
    charOfNatSorryCarriers.foldl (·.insert ·) {}
  let charOfNatAdded :=
    charOfNatSorryCarriers.filter (!expectedSet.contains ·)
  let charOfNatRemoved :=
    expectedSorryCarriers.filter (!charOfNatObservedSet.contains ·)
  unless charOfNatAdded.isEmpty && charOfNatRemoved.isEmpty do
    throwError m!"Char.ofNat direct-certificate sorry closure changed; added: {charOfNatAdded}; removed: {charOfNatRemoved}"
  let stringOfListSorryCarriers := env.constants.toList.foldl (init := #[])
      fun found (name, info) =>
    if stringOfListClosure.contains name &&
        (directConstants info).contains ``sorryAx then
      found.push name
    else
      found
  let stringOfListObservedSet : Lean.NameSet :=
    stringOfListSorryCarriers.foldl (·.insert ·) {}
  let stringOfListAdded :=
    stringOfListSorryCarriers.filter (!expectedSet.contains ·)
  let stringOfListRemoved :=
    expectedSorryCarriers.filter (!stringOfListObservedSet.contains ·)
  unless stringOfListAdded.isEmpty && stringOfListRemoved.isEmpty do
    throwError m!"String.ofList direct-certificate sorry closure changed; added: {stringOfListAdded}; removed: {stringOfListRemoved}"
  let beqSorryCarriers := env.constants.toList.foldl (init := #[])
      fun found (name, info) =>
    if beqClosure.contains name && (directConstants info).contains ``sorryAx then
      found.push name
    else
      found
  let beqObservedSet : Lean.NameSet :=
    beqSorryCarriers.foldl (·.insert ·) {}
  let beqAdded := beqSorryCarriers.filter (!expectedSet.contains ·)
  let beqRemoved := expectedSorryCarriers.filter (!beqObservedSet.contains ·)
  unless beqAdded.isEmpty && beqRemoved.isEmpty do
    throwError m!"Nat.beq direct-certificate sorry closure changed; added: {beqAdded}; removed: {beqRemoved}"
  let bleSorryCarriers := env.constants.toList.foldl (init := #[])
      fun found (name, info) =>
    if bleClosure.contains name && (directConstants info).contains ``sorryAx then
      found.push name
    else
      found
  let bleObservedSet : Lean.NameSet :=
    bleSorryCarriers.foldl (·.insert ·) {}
  let bleAdded := bleSorryCarriers.filter (!expectedSet.contains ·)
  let bleRemoved := expectedSorryCarriers.filter (!bleObservedSet.contains ·)
  unless bleAdded.isEmpty && bleRemoved.isEmpty do
    throwError m!"Nat.ble direct-certificate sorry closure changed; added: {bleAdded}; removed: {bleRemoved}"
  let modSorryCarriers := env.constants.toList.foldl (init := #[])
      fun found (name, info) =>
    if modClosure.contains name && (directConstants info).contains ``sorryAx then
      found.push name
    else
      found
  let modObservedSet : Lean.NameSet :=
    modSorryCarriers.foldl (·.insert ·) {}
  let modAdded := modSorryCarriers.filter (!expectedSet.contains ·)
  let modRemoved := expectedSorryCarriers.filter (!modObservedSet.contains ·)
  unless modAdded.isEmpty && modRemoved.isEmpty do
    throwError m!"Nat.mod direct-certificate sorry closure changed; added: {modAdded}; removed: {modRemoved}"
  let divSorryCarriers := env.constants.toList.foldl (init := #[])
      fun found (name, info) =>
    if divClosure.contains name && (directConstants info).contains ``sorryAx then
      found.push name
    else
      found
  let divObservedSet : Lean.NameSet :=
    divSorryCarriers.foldl (·.insert ·) {}
  let divAdded := divSorryCarriers.filter (!expectedSet.contains ·)
  let divRemoved := expectedSorryCarriers.filter (!divObservedSet.contains ·)
  unless divAdded.isEmpty && divRemoved.isEmpty do
    throwError m!"Nat.div direct-certificate sorry closure changed; added: {divAdded}; removed: {divRemoved}"
  let gcdSorryCarriers := env.constants.toList.foldl (init := #[])
      fun found (name, info) =>
    if gcdClosure.contains name && (directConstants info).contains ``sorryAx then
      found.push name
    else
      found
  let gcdObservedSet : Lean.NameSet :=
    gcdSorryCarriers.foldl (·.insert ·) {}
  let gcdAdded := gcdSorryCarriers.filter (!expectedSet.contains ·)
  let gcdRemoved := expectedSorryCarriers.filter (!gcdObservedSet.contains ·)
  unless gcdAdded.isEmpty && gcdRemoved.isEmpty do
    throwError m!"Nat.gcd direct-certificate sorry closure changed; added: {gcdAdded}; removed: {gcdRemoved}"
  logInfo "Nat.add, Nat.pred, Nat.sub, Nat.mul, Nat.pow, Nat.shiftLeft, Nat.shiftRight, Char.ofNat, String.ofList, Nat.beq, Nat.ble, Nat.mod, Nat.div, and Nat.gcd direct certificates exclude checkPrimitiveDef.WF and each retain exactly six known upstream proof dependencies"
