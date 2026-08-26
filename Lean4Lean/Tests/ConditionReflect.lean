/-
This file is derived from lean4lean and has been modified by Argument Computer Corporation.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/

import Lean4Lean.Verify.ConditionReflect

/-!
# Reflected-condition trust pins

The shared nondependent and dependent selector certificates are compiled and
their exact axiom closures are pinned before Nat.mod/div or bitwise consume
them.
-/

/--
info: 'Lean4Lean.Environment.VEnv.ReflectionITECertificate.canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.Environment.VEnv.ReflectionITECertificate.canonical

/--
info: 'Lean4Lean.Environment.VEnv.reflectionITE_true_of_condition' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.Environment.VEnv.reflectionITE_true_of_condition

/--
info: 'Lean4Lean.Environment.VEnv.ReflectionNatDITEChecked.canonical' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.Environment.VEnv.ReflectionNatDITEChecked.canonical

/--
info: 'Lean4Lean.Environment.VEnv.reflectionNatDITE_true_of_condition' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.Environment.VEnv.reflectionNatDITE_true_of_condition
