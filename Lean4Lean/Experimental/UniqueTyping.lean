/-
This file is derived from lean4lean and has been modified by Argument Computer Corporation.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/

import Lean4Lean.Experimental.ShapeLogRelAdequacy

/-! # Strong sort uniqueness

The former contents of this module attempted to recover an
`IsDefEqStrong` derivation from weak `SExpr.IsDefEq`.  That direction loses
the typing and extension certificates carried by the strong judgment and is
not valid for the current proof-carrying interface.

L4L-16 needs the converse architecture: translate the live Theory strong
judgment directly, then run semantic adequacy on that evidence.  The
resulting sort-injectivity theorem is re-exported here under the old
`uniq_sort` spelling.  General type uniqueness and elimination of weak
heterogeneous transitivity remain L4L-17 work.
-/

namespace Lean4Lean
namespace SExpr

variable [Params] [Params.Semantic]

/-- Compatibility spelling for semantic sort injectivity on the strong
judgment.  Unlike the retired weak theorem, its premise retains every typing
and local-extension certificate required by adequacy.  Conditional on the
two L4L-16C′w leaf inputs, like everything downstream of `LR.adequacy`. -/
theorem IsDefEqStrong.uniq_sort
    (hΓ : Ctx.WF Γ)
    (piInv : LRS.PiPathInv) (linkRect : LR.MajorLinkRect Γ)
    (h : IsDefEqStrong Γ (.sort u) (.sort v) V) : u = v :=
  SExpr.sort_inv hΓ piInv linkRect h

end SExpr
end Lean4Lean
