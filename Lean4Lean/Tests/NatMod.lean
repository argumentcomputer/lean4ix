/-
This file is derived from lean4lean and has been modified by Argument Computer Corporation.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/

import Lean4Lean.Verify.Environment.Checker

/-!
# Nat.mod checker and semantics trust pins

These probes keep the typed checker, fuel adequacy, semantic reflection, and
safe-definition checker endpoints visible while the live environment path is
tested with the other primitive declarations.
-/

#print axioms Lean4Lean.Environment.checkNatModPrimitive.WF_typed
#print axioms Lean4Lean.VEnv.natLit_defeq_of_fuel_relation
#print axioms Lean4Lean.VEnv.ReflectsNatNatNat.of_modCore_equations
#print axioms Lean4Lean.Environment.VEnv.natModTop_semantics
#print axioms Lean4Lean.Environment.VEnv.natModGo_semantics
#print axioms Lean4Lean.Environment.NatModPrimitiveEvidence.conservesHasPrimitives
#print axioms Lean4Lean.Environment.checkPrimitiveDef.natMod.WF_typed
#print axioms Lean4Lean.checkSafeNatModDefinition.WF

open Lean Lean.Elab.Command

private def natModRoots : Array Lean.Name := #[
  ``Lean4Lean.Environment.checkNatModPrimitive.WF_typed,
  ``Lean4Lean.VEnv.natLit_defeq_of_fuel_relation,
  ``Lean4Lean.VEnv.ReflectsNatNatNat.of_modCore_equations,
  ``Lean4Lean.Environment.VEnv.natModTop_semantics,
  ``Lean4Lean.Environment.VEnv.natModGo_semantics,
  ``Lean4Lean.Environment.NatModPrimitiveEvidence.conservesHasPrimitives,
  ``Lean4Lean.Environment.checkPrimitiveDef.natMod.WF_typed,
  ``Lean4Lean.checkSafeNatModDefinition.WF]

private def allowedNatModAxioms : Lean.NameSet :=
  (#[
    `propext, `sorryAx, `Classical.choice, `Quot.sound,
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

run_cmd do
  for root in natModRoots do
    let axioms ← Lean.collectAxioms root
    let unexpected := axioms.filter (!allowedNatModAxioms.contains ·)
    unless unexpected.isEmpty do
      throwError m!"Nat.mod trust closure for {root} gained unexpected axioms: {unexpected}"
