/-
This file is derived from lean4lean and has been modified by Argument Computer Corporation.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/

import Lean4Lean.Verify.Environment.Checker

/-!
# Nat.bitwise generic-state certificate regression pins

These checks pin the executable well-founded certificate, the Boolean and
Nat-equality condition semantics, the Kripke bitwise reflection theorem, and
the typed safe-definition endpoint.  The integrated primitive regression
separately verifies that the top-level environment dispatcher reaches this
path without using the generic `checkPrimitiveDef.WF` boundary.
-/

#print axioms Lean4Lean.Environment.reduceNatWellFoundedLam2.WF
#print axioms Lean4Lean.Environment.checkNatBitwiseZero.WF
#print axioms Lean4Lean.Environment.checkNatBitwiseFixCertificate.WF
#print axioms Lean4Lean.VEnv.evalNatBitwise_of_fix_relation
#print axioms Lean4Lean.Environment.Condition.bool.check.WF.semantic
#print axioms Lean4Lean.Environment.Condition.natEq.check.WF.semantic
#print axioms Lean4Lean.Environment.NatBitwiseFixCertificate.NormalizedValid.reflects
#print axioms Lean4Lean.Environment.checkNatBitwisePrimitive.WF_typed
#print axioms Lean4Lean.Environment.NatBitwisePrimitiveEvidence.conservesHasPrimitives
#print axioms Lean4Lean.Environment.checkPrimitiveDef.natBitwise.WF_typed
#print axioms Lean4Lean.checkSafeNatBitwiseDefinition.WF

open Lean Lean.Elab Command

private def natBitwiseRoots : Array Lean.Name := #[
  ``Lean4Lean.Environment.reduceNatWellFoundedLam2.WF,
  ``Lean4Lean.Environment.checkNatBitwiseZero.WF,
  ``Lean4Lean.Environment.checkNatBitwiseFixCertificate.WF,
  ``Lean4Lean.VEnv.evalNatBitwise_of_fix_relation,
  ``Lean4Lean.Environment.Condition.bool.check.WF.semantic,
  ``Lean4Lean.Environment.Condition.natEq.check.WF.semantic,
  ``Lean4Lean.Environment.NatBitwiseFixCertificate.NormalizedValid.reflects,
  ``Lean4Lean.Environment.checkNatBitwisePrimitive.WF_typed,
  ``Lean4Lean.Environment.NatBitwisePrimitiveEvidence.conservesHasPrimitives,
  ``Lean4Lean.Environment.checkPrimitiveDef.natBitwise.WF_typed,
  ``Lean4Lean.checkSafeNatBitwiseDefinition.WF]

private def allowedNatBitwiseAxioms : Lean.NameSet :=
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

run_cmd do
  for root in natBitwiseRoots do
    let axioms ← Lean.collectAxioms root
    let unexpected := axioms.filter (!allowedNatBitwiseAxioms.contains ·)
    unless unexpected.isEmpty do
      throwError m!"Nat.bitwise trust closure for {root} gained unexpected axioms: {unexpected}"
