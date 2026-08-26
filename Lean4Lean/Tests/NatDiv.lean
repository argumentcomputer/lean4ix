/-
This file is derived from lean4lean and has been modified by Argument Computer Corporation.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/

import Lean4Lean.Verify.Environment.Checker

/-!
# Nat.div checker and semantics trust pins

These probes keep the structural loose-bvar bridge, typed checker, fuel
adequacy, semantic reflection, and safe-definition checker endpoints visible
while the live environment path is tested with the other primitive
declarations.
-/

#print axioms Lean4Lean.Environment.primitiveLiftLooseBVars_eq
#print axioms Lean4Lean.Environment.checkNatDivPrimitive.WF_typed
#print axioms Lean4Lean.VEnv.ReflectsNatNatNat.of_divCore_equations
#print axioms Lean4Lean.Environment.VEnv.natDivTop_semantics
#print axioms Lean4Lean.Environment.VEnv.natDivGo_semantics
#print axioms Lean4Lean.Environment.NatDivPrimitiveEvidence.conservesHasPrimitives
#print axioms Lean4Lean.Environment.checkPrimitiveDef.natDiv.WF_typed
#print axioms Lean4Lean.checkSafeNatDivDefinition.WF

open Lean Lean.Elab.Command

private def natDivRoots : Array Lean.Name := #[
  ``Lean4Lean.Environment.primitiveLiftLooseBVars_eq,
  ``Lean4Lean.Environment.checkNatDivPrimitive.WF_typed,
  ``Lean4Lean.VEnv.ReflectsNatNatNat.of_divCore_equations,
  ``Lean4Lean.Environment.VEnv.natDivTop_semantics,
  ``Lean4Lean.Environment.VEnv.natDivGo_semantics,
  ``Lean4Lean.Environment.NatDivPrimitiveEvidence.conservesHasPrimitives,
  ``Lean4Lean.Environment.checkPrimitiveDef.natDiv.WF_typed,
  ``Lean4Lean.checkSafeNatDivDefinition.WF]

private def allowedNatDivAxioms : Lean.NameSet :=
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
  let forbiddenLiftAxiom := `Lean.Expr.liftLooseBVars_eq
  for root in natDivRoots do
    let axioms ← Lean.collectAxioms root
    if axioms.contains forbiddenLiftAxiom then
      throwError m!"Nat.div trust closure for {root} reached the forbidden opaque loose-bvar lift axiom"
    let unexpected := axioms.filter (!allowedNatDivAxioms.contains ·)
    unless unexpected.isEmpty do
      throwError m!"Nat.div trust closure for {root} gained unexpected axioms: {unexpected}"
