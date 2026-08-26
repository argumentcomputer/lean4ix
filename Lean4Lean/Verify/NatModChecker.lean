/-
This file is derived from lean4lean and has been modified by Argument Computer Corporation.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/

import Lean4Lean.Verify.ConditionChecker

/-!
# Verified Nat.mod primitive checker

This module proves the typed checker certificate for the executable `Nat.mod`
primitive definition check. It is adapted from upstream lean4lean PR #32 at
`6cfd43a48d17be85c76414638655c12ef9a7ee23`.
-/

namespace Lean4Lean.Environment

open Lean hiding Environment Exception
open Kernel TypeChecker

set_option maxHeartbeats 800000 in
theorem checkPrimitiveDef.natMod_eq (hname : v.name = ``Nat.mod) :
    checkPrimitiveDefCore v = (do
      let env ← getEnv
      let fail {α} : M α :=
        throw <| .other s!"invalid form for primitive def {v.name}"
      checkNatModPrimitive env v fail
      pure true) := by
  simp only [checkPrimitiveDefCore, hname]

set_option maxHeartbeats 800000 in
theorem checkNatModPrimitive.WF_typed {c : VContext} {s : VState}
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
      (checkNatModPrimitive c.env v
        (throw <| .other s!"invalid form for primitive def {v.name}")) fun _ _ =>
      ∃ zL zR go goTy topL topR goL goR,
        c.TrExprS
          (.lam0 q(Nat) <| mkApp2 v.value q(Nat.zero) (.bvar 0)) zL ∧
        c.TrExprS (.lam0 q(Nat) q(Nat.zero)) zR ∧
        c.TrExprS q(Nat.modCore.go) go ∧
        c.TrExprS q(∀ y, Nat.succ Nat.zero ≤ y →
          ∀ fuel x : Nat, Nat.succ x ≤ fuel → Nat) goTy ∧
        c.TrExprS (natModTopEquation v.value).1 topL ∧
        c.TrExprS (natModTopEquation v.value).2 topR ∧
        c.TrExprS natModGoEquation.1 goL ∧
        c.TrExprS natModGoEquation.2 goR ∧
        v.levelParams = [] ∧
        c.venv.contains ``Nat ∧ c.venv.contains ``Bool ∧
        c.venv.contains ``Nat.ble ∧ c.venv.contains ``Nat.sub ∧
        c.IsDefEqU ty' (.forallE .nat <| .forallE .nat .nat) ∧
        c.IsDefEqU zL zR ∧ Rcond ∧ c.HasType go goTy ∧
        c.IsDefEqU topL topR ∧ c.IsDefEqU goL goR := by
  unfold checkNatModPrimitive
  dsimp only
  by_cases hdeps : (c.env.contains ``Nat && c.env.contains ``Nat.sub &&
      c.env.contains ``Bool && c.env.contains ``Nat.ble &&
      v.levelParams.isEmpty) = true
  · rw [if_pos hdeps]
    simp only [Bool.and_eq_true] at hdeps
    rcases hdeps with
      ⟨⟨⟨⟨hnatSrc, hsubSrc⟩, hboolSrc⟩, hbleSrc⟩, hempty⟩
    have hlparams : v.levelParams = [] := by
      simpa using hempty
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
        have hzLF :
            ((Expr.lam0 q(Nat) <|
              mkApp2 v.value q(Nat.zero) (.bvar 0)) : Expr).FVarsIn
              (· ∈ c.vlctx.fvars) := by
          simpa [Expr.lam0, mkApp2, mkApp, FVarsIn] using hvalue.fvarsIn
        refine checkTypeDiscard.capture.bind_WF hzLF fun _ zL _ hzL _ => ?_
        refine checkTypeDiscard.capture.bind_WF
          (by fvars_closed)
          fun _ zR _ hzR _ => ?_
        exact (isDefEq.WF hzL hzR).bind fun b _ _ hzEq => by
          by_cases hb : b = true
          · rw [if_pos hb]
            have hzEq := hzEq hb
            refine checkTypeDiscard.capture.bind_WF
              (by fvars_closed)
              fun _ _ _ hleTy _ => ?_
            refine checkTypeIsDefEqGuard.fvarsIn.bind_WF
              (by fvars_closed)
              hleTy (fun {_} {_} => .throw) fun _ _ _ _ => ?_
            refine checkTypeDiscard.capture.bind_WF
              (by fvars_closed)
              fun _ goTy _ hgoTy _ => ?_
            refine checkTypeIsDefEqGuard.fvarsIn.bind_WF
              (by fvars_closed)
              hgoTy (fun {_} {_} => .throw) fun _ go hgoS hgoHas => ?_
            exact (hnatLECheck hclparams (fun {_} {_} => .throw)).bind
              fun _ _ _ hcond =>
              checkTypeDiscard.capture.bind_WF
                (by simpa [natModTopEquation, Expr.lam0, mkAppB, mkApp2,
                  mkApp, FVarsIn]
                  using hvalue.fvarsIn)
                fun _ topL _ htopL _ =>
              checkTypeDiscard.capture.bind_WF
                (by fvars_closed [natModTopEquation, Condition.reflectedITE,
                  Condition.reflectedDITE, Condition.natLE])
                fun _ topR _ htopR _ =>
              isDefEqGuard.bind_WF htopL htopR (fun {_} {_} => .throw)
                fun _ htopEq =>
                checkTypeDiscard.capture.bind_WF
                  (by fvars_closed [natModGoEquation])
                  fun _ goL _ hgoL _ =>
                checkTypeDiscard.capture.bind_WF
                  (by fvars_closed [natModGoEquation])
                  fun _ goR _ hgoR _ =>
                (isDefEq.WF hgoL hgoR).bind fun b _ _ hgoEq => by
                  by_cases hb : b = true
                  · rw [if_pos hb]
                    exact .pure ⟨zL, zR, go, goTy, topL, topR, goL, goR,
                      hzL, hzR, hgoS, hgoTy, htopL, htopR, hgoL, hgoR,
                      hlparams, hnat, hbool, hble, hsub,
                      htyEq, hzEq, hcond, hgoHas, htopEq,
                      hgoEq hb⟩
                  · rw [if_neg hb]
                    exact .throw
          · rw [if_neg hb]
            exact .throw
      · rw [if_neg hb]
        exact .throw
  · rw [if_neg hdeps]
    exact .throw

end Lean4Lean.Environment
