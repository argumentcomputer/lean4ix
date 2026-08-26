/-
This file is derived from lean4lean and has been modified by Argument Computer Corporation.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/

import Lean4Lean.Verify.Environment.Checker

/-!
# Nat.bitwise specialization regression pins

These checks pin the typed `Nat.land`, `Nat.lor`, and `Nat.xor` recognizers,
their Boolean and bitwise semantic bridges, their primitive-contract
conservation theorems, and their direct safe-checker endpoints.
-/

#print axioms Lean4Lean.VEnv.ReflectsBoolBin.of_table
#print axioms Lean4Lean.VEnv.ReflectsBoolBin.of_and_equations
#print axioms Lean4Lean.VEnv.ReflectsBoolBin.of_or_equations
#print axioms Lean4Lean.VEnv.ReflectsNatNatNat.of_bitwise_specialization
#print axioms Lean4Lean.Environment.checkPrimitiveDef.natLand.WF_typed
#print axioms Lean4Lean.Environment.checkPrimitiveDef.natLor.WF_typed
#print axioms Lean4Lean.Environment.checkPrimitiveDef.natXor.WF_typed
#print axioms Lean4Lean.VEnv.HasPrimitives.addNatLandDef
#print axioms Lean4Lean.VEnv.HasPrimitives.addNatLorDef
#print axioms Lean4Lean.VEnv.HasPrimitives.addNatXorDef
#print axioms Lean4Lean.checkSafeNatLandDefinition.WF
#print axioms Lean4Lean.checkSafeNatLorDefinition.WF
#print axioms Lean4Lean.checkSafeNatXorDefinition.WF

open Lean Lean.Elab Command

private def bitwiseSpecializationRoots : Array Lean.Name := #[
  ``Lean4Lean.VEnv.ReflectsBoolBin.of_table,
  ``Lean4Lean.VEnv.ReflectsBoolBin.of_and_equations,
  ``Lean4Lean.VEnv.ReflectsBoolBin.of_or_equations,
  ``Lean4Lean.VEnv.ReflectsNatNatNat.of_bitwise_specialization,
  ``Lean4Lean.Environment.checkPrimitiveDef.natLand.WF_typed,
  ``Lean4Lean.Environment.checkPrimitiveDef.natLor.WF_typed,
  ``Lean4Lean.Environment.checkPrimitiveDef.natXor.WF_typed,
  ``Lean4Lean.VEnv.HasPrimitives.addNatLandDef,
  ``Lean4Lean.VEnv.HasPrimitives.addNatLorDef,
  ``Lean4Lean.VEnv.HasPrimitives.addNatXorDef,
  ``Lean4Lean.checkSafeNatLandDefinition.WF,
  ``Lean4Lean.checkSafeNatLorDefinition.WF,
  ``Lean4Lean.checkSafeNatXorDefinition.WF]

private def allowedBitwiseSpecializationAxioms : Lean.NameSet :=
  (#[`propext, `sorryAx, `Classical.choice, `Quot.sound,
    `Lean4Lean.ptrEqConstantInfo_eq, `Lean4Lean.ptrEqExpr_eq,
    `Lean.Expr.abstractRange_eq, `Lean.Expr.abstract_eq,
    `Lean.Expr.eqv_eq, `Lean.Expr.hasLooseBVar_eq,
    `Lean.Expr.instantiate1_eq, `Lean.Expr.instantiateRange_eq,
    `Lean.Expr.instantiateRevRange_eq, `Lean.Expr.instantiateRev_eq,
    `Lean.Expr.instantiate_eq, `Lean.Expr.lowerLooseBVars_eq,
    `Lean.Expr.mkAppData_eq, `Lean.Expr.mkData_eq, `Lean.Expr.replace_eq,
    `Lean.Level.hasMVar_eq, `Lean.Level.hasParam_eq,
    `Lean.Level.instLawfulBEqLevel, `Lean.Level.isExplicitSubsumedAux_eq,
    `Lean.Level.normalize_eq, `Lean.PersistentHashMap.findAux_isSome,
    `Lean.Syntax.structEq_eq, `Lean.PersistentArray.WF.toList'_push,
    `Lean.PersistentHashMap.WF.find?_eq,
    `Lean.PersistentHashMap.WF.toList'_insert] : Array Lean.Name).foldl
      (init := {}) fun found name => found.insert name

run_meta
  let env ← Lean.getEnv
  for name in #[``Nat.land, ``Nat.lor, ``Nat.xor] do
    let some (.defnInfo value) := env.toKernelEnv.find? name
      | throwError m!"{name} is not a definition"
    match (Lean4Lean.Environment.checkPrimitiveDef value).run env.toKernelEnv
        (lparams := value.levelParams) with
    | .ok true => pure ()
    | .ok false =>
      throwError m!"the executable primitive checker rejected {name}"
    | .error _ =>
      throwError m!"the executable primitive checker failed while checking {name}"

run_cmd do
  for root in bitwiseSpecializationRoots do
    let axioms ← Lean.collectAxioms root
    let unexpected :=
      axioms.filter (!allowedBitwiseSpecializationAxioms.contains ·)
    unless unexpected.isEmpty do
      throwError m!"bitwise specialization trust closure for {root} gained unexpected axioms: {unexpected}"
