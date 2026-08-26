/-
This file is derived from lean4lean and has been modified by Argument Computer Corporation.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/

import Lean4Lean.Verify.ConditionChecker

/-!
# Verified Nat.div primitive checker

This module proves the typed checker certificate for the executable `Nat.div`
primitive definition check. It is adapted from upstream lean4lean PR #32 at
`6cfd43a48d17be85c76414638655c12ef9a7ee23`.
-/

namespace Lean4Lean.Environment

open Lean hiding Environment Exception
open Kernel TypeChecker

set_option maxHeartbeats 800000 in
theorem checkPrimitiveDef.natDiv_eq (hname : v.name = ``Nat.div) :
    checkPrimitiveDefCore v = (do
      let env ← getEnv
      let fail {α} : M α :=
        throw <| .other s!"invalid form for primitive def {v.name}"
      checkNatDivPrimitive env v fail
      pure true) := by
  simp only [checkPrimitiveDefCore, hname]

set_option maxHeartbeats 800000 in
theorem checkNatDivPrimitive.WF_typed {c : VContext} {s : VState}
    (hcparams : c.lparams = v.levelParams)
    (hty : c.TrExprS v.type ty')
    (hvlctx : c.vlctx = [])
    (hvalue : c.TrExprS v.value value')
    (hnatLECheck : ∀ {fail : ∀ {α}, M α} {s'},
      c.lparams = [] →
      (∀ {α} {s''}, M.WF c s'' (fail : M α) fun _ _ => False) →
      M.WF c s' (Condition.natLE.checkForPrimitive fail)
        fun _ _ => Rcond) :
    M.WF c s
      (checkNatDivPrimitive c.env v
        (throw <| .other s!"invalid form for primitive def {v.name}")) fun _ _ =>
      ∃ go goTy topL topR goL goR,
        c.TrExprS q(Nat.div.go) go ∧
        c.TrExprS q(∀ y, Nat.succ Nat.zero ≤ y →
          ∀ fuel x : Nat, Nat.succ x ≤ fuel → Nat) goTy ∧
        c.TrExprS (natDivTopEquation v.value).1 topL ∧
        c.TrExprS (natDivTopEquation v.value).2 topR ∧
        c.TrExprS natDivGoEquation.1 goL ∧
        c.TrExprS natDivGoEquation.2 goR ∧
        v.levelParams = [] ∧
        c.venv.contains ``Nat ∧ c.venv.contains ``Bool ∧
        c.venv.contains ``Nat.ble ∧ c.venv.contains ``Nat.sub ∧
        c.IsDefEqU ty' (.forallE .nat <| .forallE .nat .nat) ∧
        Rcond ∧ c.HasType go goTy ∧
        c.IsDefEqU topL topR ∧ c.IsDefEqU goL goR := by
  unfold checkNatDivPrimitive
  dsimp only
  by_cases hdeps : (c.env.contains ``Nat && c.env.contains ``Nat.sub &&
      c.env.contains ``Bool && c.env.contains ``Nat.ble &&
      v.levelParams.isEmpty) = true
  · rw [if_pos hdeps]
    simp only [Bool.and_eq_true] at hdeps
    rcases hdeps with
      ⟨⟨⟨⟨hnatSrc, hsubSrc⟩, hboolSrc⟩, hbleSrc⟩, hempty⟩
    have hlparams : v.levelParams = [] := by simpa using hempty
    have hclparams : c.lparams = [] := hcparams.trans hlparams
    have hnat : c.venv.contains ``Nat :=
      Environment.VContext.contains_safe_primitive c hnatSrc (by
        simp [Lean.Kernel.Environment.primitives,
          NameSet.contains, NameSet.ofList])
    have hsub : c.venv.contains ``Nat.sub :=
      Environment.VContext.contains_safe_primitive c hsubSrc (by
        simp [Lean.Kernel.Environment.primitives,
          NameSet.contains, NameSet.ofList])
    have hbool : c.venv.contains ``Bool :=
      Environment.VContext.contains_safe_primitive c hboolSrc (by
        simp [Lean.Kernel.Environment.primitives,
          NameSet.contains, NameSet.ofList])
    have hble : c.venv.contains ``Nat.ble :=
      Environment.VContext.contains_safe_primitive c hbleSrc (by
        simp [Lean.Kernel.Environment.primitives,
          NameSet.contains, NameSet.ofList])
    have hcanon : c.TrExprS q(Nat → Nat → Nat)
        (.forallE .nat <| .forallE .nat .nat) := by
      change TrExprS c.venv c.lparams c.vlctx _ _
      rw [hvlctx]
      exact TrExprS.natBinaryType_of_contains c.Ewf c.hasPrimitives hnat
        c.lparams []
    exact checkTypeDiscard.bind_WF hcanon.fvarsIn fun _ =>
      (isDefEq.WF hty hcanon).bind fun b _ _ htyEq => by
      by_cases hb : b = true
      · rw [if_pos hb]
        have htyEq := htyEq hb
        exact (hnatLECheck hclparams (fun {_} {_} => .throw)).bind
          fun _ _ _ hcond =>
          checkTypeDiscard.capture.bind_WF
            (by fvars_closed)
            fun _ _ _ hleTy _ =>
          checkTypeIsDefEqGuard.fvarsIn.bind_WF
            (by fvars_closed)
            hleTy (fun {_} {_} => .throw) fun _ _ _ _ =>
          checkTypeDiscard.capture.bind_WF
            (by fvars_closed)
            fun _ goTy _ hgoTy _ =>
          checkTypeIsDefEqGuard.fvarsIn.bind_WF
            (by fvars_closed)
            hgoTy (fun {_} {_} => .throw) fun _ go hgoS hgoHas =>
          checkTypeDiscard.capture.bind_WF
            (by simpa [natDivTopEquation, Expr.lam0, mkAppB, mkApp2,
              mkApp, FVarsIn] using hvalue.fvarsIn)
            fun _ topL _ htopL _ =>
          checkTypeDiscard.capture.bind_WF
            (by fvars_closed [natDivTopEquation, natDivTopRhs,
              primitiveLiftLooseBVars])
            fun _ topR _ htopR _ =>
          isDefEqGuard.bind_WF htopL htopR (fun {_} {_} => .throw)
            fun _ htopEq =>
            checkTypeDiscard.capture.bind_WF
              (by fvars_closed [natDivGoEquation, natDivGoLhsBody,
                natDivGoRhsBody, primitiveLiftLooseBVars])
              fun _ goL _ hgoL _ =>
            checkTypeDiscard.capture.bind_WF
              (by fvars_closed [natDivGoEquation, natDivGoLhsBody,
                natDivGoRhsBody, primitiveLiftLooseBVars])
              fun _ goR _ hgoR _ =>
            (isDefEq.WF hgoL hgoR).bind fun b _ _ hgoEq => by
              by_cases hb : b = true
              · rw [if_pos hb]
                exact .pure ⟨go, goTy, topL, topR, goL, goR,
                  hgoS, hgoTy, htopL, htopR, hgoL, hgoR,
                  hlparams, hnat, hbool, hble, hsub, htyEq,
                  hcond, hgoHas, htopEq, hgoEq hb⟩
              · rw [if_neg hb]
                exact .throw
      · rw [if_neg hb]
        exact .throw
  · rw [if_neg hdeps]
    exact .throw

end Lean4Lean.Environment
