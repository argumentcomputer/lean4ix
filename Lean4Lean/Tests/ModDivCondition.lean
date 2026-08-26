/-
This file is derived from lean4lean and has been modified by Argument Computer Corporation.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/

import Lean4Lean.Verify.ModDivCondition

/-!
# Nat.mod/div condition-selector trust pins

The executable checker evidence and the semantic branch-selection adapters
are pinned independently before the recursive Nat.mod/div certificate lands.
-/

/--
info: 'Lean4Lean.Environment.Condition.natLE.check.WF' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Lean4Lean.ptrEqConstantInfo_eq,
 Lean4Lean.ptrEqExpr_eq,
 Quot.sound,
 Lean.Expr.abstractRange_eq,
 Lean.Expr.abstract_eq,
 Lean.Expr.eqv_eq,
 Lean.Expr.hasLooseBVar_eq,
 Lean.Expr.instantiate1_eq,
 Lean.Expr.instantiateRange_eq,
 Lean.Expr.instantiateRevRange_eq,
 Lean.Expr.instantiateRev_eq,
 Lean.Expr.instantiate_eq,
 Lean.Expr.lowerLooseBVars_eq,
 Lean.Expr.mkAppData_eq,
 Lean.Expr.mkData_eq,
 Lean.Expr.replace_eq,
 Lean.Level.hasParam_eq,
 Lean.Level.instLawfulBEqLevel,
 Lean.Level.isExplicitSubsumedAux_eq,
 Lean.Level.normalize_eq,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.Syntax.structEq_eq,
 Lean.PersistentArray.WF.toList'_push,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms Lean4Lean.Environment.Condition.natLE.check.WF

/--
info: 'Lean4Lean.Environment.Condition.natLE.checkForPrimitive.WF.selector' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Lean4Lean.ptrEqConstantInfo_eq,
 Lean4Lean.ptrEqExpr_eq,
 Quot.sound,
 Lean.Expr.abstractRange_eq,
 Lean.Expr.abstract_eq,
 Lean.Expr.eqv_eq,
 Lean.Expr.hasLooseBVar_eq,
 Lean.Expr.instantiate1_eq,
 Lean.Expr.instantiateRange_eq,
 Lean.Expr.instantiateRevRange_eq,
 Lean.Expr.instantiateRev_eq,
 Lean.Expr.instantiate_eq,
 Lean.Expr.lowerLooseBVars_eq,
 Lean.Expr.mkAppData_eq,
 Lean.Expr.mkData_eq,
 Lean.Expr.replace_eq,
 Lean.Level.hasParam_eq,
 Lean.Level.instLawfulBEqLevel,
 Lean.Level.isExplicitSubsumedAux_eq,
 Lean.Level.normalize_eq,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.Syntax.structEq_eq,
 Lean.PersistentArray.WF.toList'_push,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms Lean4Lean.Environment.Condition.natLE.checkForPrimitive.WF.selector

/--
info: 'Lean4Lean.Environment.VEnv.NatLESelectorCertificate.selectITETrue' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.Environment.VEnv.NatLESelectorCertificate.selectITETrue

/--
info: 'Lean4Lean.Environment.VEnv.NatLESelectorCertificate.selectDITEFalseConstructor' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.Environment.VEnv.NatLESelectorCertificate.selectDITEFalseConstructor
