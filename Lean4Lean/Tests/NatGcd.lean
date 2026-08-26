/-
This file is derived from lean4lean and has been modified by Argument Computer Corporation.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/

import Lean4Lean.Verify.Environment.Checker

/-!
# Nat.gcd generic-state certificate regression pins

These checks pin the executable certificate, its Euclidean semantics, and
the typed safe-definition endpoint. The executable regression uses a
`Prod (Nat × Nat)` recursive state so a future refactor cannot silently
reintroduce the upstream PR's `PSigma`-only acceptance boundary.
-/

#print axioms Lean4Lean.Environment.exprLooseBVarRange_eq
#print axioms Lean4Lean.Environment.checkNatWellFoundedCertificate.WF
#print axioms Lean4Lean.Environment.VEnv.ReflectsNatNatNat.of_gcd_fix_relation
#print axioms Lean4Lean.Environment.NatGcdFixCertificate.NormalizedValid.reflects
#print axioms Lean4Lean.Environment.checkNatGcdPrimitive.WF_typed
#print axioms Lean4Lean.Environment.NatGcdPrimitiveEvidence.conservesHasPrimitives
#print axioms Lean4Lean.Environment.checkPrimitiveDef.natGcd.WF_typed
#print axioms Lean4Lean.checkSafeNatGcdDefinition.WF

open Lean Lean.Elab Command

private def natGcdRoots : Array Lean.Name := #[
  ``Lean4Lean.Environment.exprLooseBVarRange_eq,
  ``Lean4Lean.Environment.checkNatWellFoundedCertificate.WF,
  ``Lean4Lean.Environment.VEnv.ReflectsNatNatNat.of_gcd_fix_relation,
  ``Lean4Lean.Environment.NatGcdFixCertificate.NormalizedValid.reflects,
  ``Lean4Lean.Environment.checkNatGcdPrimitive.WF_typed,
  ``Lean4Lean.Environment.NatGcdPrimitiveEvidence.conservesHasPrimitives,
  ``Lean4Lean.Environment.checkPrimitiveDef.natGcd.WF_typed,
  ``Lean4Lean.checkSafeNatGcdDefinition.WF]

private def allowedNatGcdAxioms : Lean.NameSet :=
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
  for root in natGcdRoots do
    let axioms ← Lean.collectAxioms root
    let unexpected := axioms.filter (!allowedNatGcdAxioms.contains ·)
    unless unexpected.isEmpty do
      throwError m!"Nat.gcd trust closure for {root} gained unexpected axioms: {unexpected}"
