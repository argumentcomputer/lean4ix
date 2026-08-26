/-
This file is derived from lean4lean and has been modified by Argument Computer Corporation.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/

import Lean4Lean.Primitive

/-!
# Nat.gcd generic-state executable regression

The production toolchain currently compiles `Nat.gcd` through a `PSigma`
state. This fixture uses `Prod (Nat × Nat)` instead, pinning the certificate
checker to the recursive-state interface rather than one compiler-selected
representation.
-/

namespace Lean4Lean.Environment

open Lean hiding Environment Exception
open Kernel TypeChecker

private def gcdProdAux (p : Nat × Nat) : Nat :=
  if _h : p.1 = 0 then
    p.2
  else
    gcdProdAux (p.2 % p.1, p.1)
  termination_by p.1
  decreasing_by
    simp_wf
    exact Nat.mod_lt _ (Nat.zero_lt_of_ne_zero _h)

private def gcdProd (m n : Nat) : Nat :=
  gcdProdAux (m, n)

run_meta
  let env ← Lean.getEnv
  let some (.defnInfo gcd) := env.toKernelEnv.find? ``gcdProd
    | throwError "Prod-state gcd regression is not a definition"
  let candidate := { gcd with name := ``Nat.gcd }
  let fail {α} : TypeChecker.M α :=
    throw <| .other "generic-state Nat.gcd certificate rejected Prod state"
  match (checkNatGcdPrimitive env.toKernelEnv candidate fail).run
      env.toKernelEnv (lparams := candidate.levelParams) with
  | .ok _ => pure ()
  | .error err =>
    throwError "generic-state Nat.gcd certificate rejected Prod state: {← (err.toMessageData {}).toString}"

end Lean4Lean.Environment
