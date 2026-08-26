/-
This file is derived from lean4lean and has been modified by Argument Computer Corporation.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/

import Lean4Lean.Primitive
import Lean4Lean.Verify.TypeChecker

/-!
# Verified primitive-definition certificates

This module manually adapts bounded pieces of upstream lean4lean PR #32 at
`6cfd43a48d17be85c76414638655c12ef9a7ee23`. The current bounded surface
covers the body-first foundation and direct `Nat.add`, `Nat.pred`, `Nat.sub`,
`Nat.mul`, `Nat.pow`, `Nat.shiftLeft`, `Nat.beq`, and `Nat.ble` certificates;
later primitive families remain separate slices.
-/

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel TypeChecker

@[simp] private theorem mkApp2_eq_app (f a b : Expr) :
    mkApp2 f a b = (f.app a).app b := rfl

@[simp] private theorem Expr.lam0_eq_lam (ty body : Expr) :
    Expr.lam0 ty body = .lam `_ ty body .default := rfl

@[simp] private theorem VEnv.hasType_eq_isDefEq (env : VEnv) (U : Nat)
    (Γ : List VExpr) (e A : VExpr) :
    env.HasType U Γ e A = env.IsDefEq U Γ e e A := rfl

namespace Environment

/-- Transfer a successful source lookup of a reserved primitive into the
safe Theory model used by the type checker. -/
theorem VContext.contains_safe_primitive
    (c : VContext) (hsrc : c.env.contains n)
    (hprimitive : Lean.Kernel.Environment.primitives.contains n) :
    c.venv.contains n := by
  have hsome : (c.env.find? n).isSome := by
    change (c.env.constants.find?' n).isSome = true
    rw [c.trenv.map_wf.find?'_eq_find?]
    rw [← SMap.find?_isSome]
    exact hsrc
  obtain ⟨ci, hfind⟩ := Option.isSome_iff_exists.mp hsome
  have hsafety := (c.safePrimitives hfind hprimitive).1
  obtain ⟨ci', hci', _⟩ := c.trenv.find? hfind (by
    rw [hsafety]
    exact DefinitionSafety.le_safe)
  exact ⟨ci', hci'⟩

/-- Lift a proof about the recognizer's substantive core through its public
safety guard. -/
theorem checkPrimitiveDef.WF_of_core {c : VContext} {s : VState}
    {post : Bool → VState → Prop} (hfalse : post false s)
    (hcore : M.WF c s (checkPrimitiveDefCore v) post) :
    M.WF c s (checkPrimitiveDef v) post := by
  simp only [checkPrimitiveDef]
  split
  · exact hcore
  · exact .pure hfalse

/-- A globally closed translation can be reused under freshly introduced
bound variables without changing its target expression. -/
private theorem TrExprS.closed_weak
    {env : VEnv} (wf : env.WF)
    {e : Expr} {eV : VExpr} {Δ : VLCtx} {dn n : Nat}
    (hglobal : TrExprS env Us [] e eV)
    (W : VLCtx.BVLift [] Δ dn 0 n 0) :
    TrExprS env Us Δ e eV := by
  obtain ⟨_, hglobalWF⟩ := hglobal.wf wf.ordered
    (Δ := []) trivial
  have heVClosed :=
    (hglobalWF.hasType.1.closedN' wf.ordered.closed trivial).1
  have hsourceClosed := hglobal.closed.looseBVarRange_zero
  have hsourceLift : e.liftLooseBVars' 0 dn = e :=
    Expr.liftLooseBVars_eq_self (by rw [hsourceClosed]; omega)
  have htargetLift : eV.liftN n 0 = eV :=
    heVClosed.liftN_eq (Nat.zero_le _)
  have hweak := hglobal.weakBV wf.ordered W
  rwa [hsourceLift, htargetLift] at hweak

/-- Translate the canonical `Bool` type and recover its sort from the stored
`Bool.false` declaration. The local `HasPrimitives` contract intentionally
does not duplicate a separate `boolType` field. -/
theorem TrExprS.boolType_of_contains
    {env : VEnv} (wf : env.WF) (hprim : env.HasPrimitives)
    (hbool : env.contains ``Bool) (Us : List Name) (Δ : VLCtx) :
    TrExprS env Us Δ q(Bool) .bool ∧
      env.IsType Us.length Δ.toCtx .bool := by
  obtain ⟨boolCi, hboolLookup⟩ := hbool
  obtain ⟨⟨falseCi, hfalseLookup⟩, _⟩ :=
    hprim.bool ⟨boolCi, hboolLookup⟩
  have hfalseShape := hprim.boolFalse hfalseLookup
  subst falseCi
  obtain ⟨u, hboolSort0⟩ := wf.ordered.constWF hfalseLookup
  obtain ⟨boolCi', hboolLookup', _, hboolUvars⟩ :=
    hboolSort0.const_inv wf.ordered trivial
  rw [hboolLookup] at hboolLookup'
  cases hboolLookup'
  have hboolSortU := hboolSort0.instL (U' := Us.length) (ls := []) nofun
  have hboolSortU' : env.HasType Us.length [] .bool (.sort (u.inst [])) := by
    simpa [VExpr.bool, VExpr.instL] using hboolSortU
  exact ⟨.const hboolLookup rfl hboolUvars,
    ⟨u.inst [], hboolSortU'.weak0 wf (Γ := Δ.toCtx)⟩⟩

/-- Translate the canonical `Nat` type and recover its sort from the stored
`Nat.zero` declaration. The local `HasPrimitives` contract intentionally does
not duplicate a separate `natType` field. -/
theorem TrExprS.natType_of_contains
    {env : VEnv} (wf : env.WF) (hprim : env.HasPrimitives)
    (hnat : env.contains ``Nat) (Us : List Name) (Δ : VLCtx) :
    TrExprS env Us Δ q(Nat) .nat ∧
      env.IsType Us.length Δ.toCtx .nat := by
  obtain ⟨natCi, hnatLookup⟩ := hnat
  obtain ⟨⟨zeroCi, hzeroLookup⟩, _⟩ := hprim.nat ⟨natCi, hnatLookup⟩
  have hzeroShape := hprim.natZero hzeroLookup
  subst zeroCi
  obtain ⟨u, hnatSort0⟩ := wf.ordered.constWF hzeroLookup
  obtain ⟨natCi', hnatLookup', _, hnatUvars⟩ :=
    hnatSort0.const_inv wf.ordered trivial
  rw [hnatLookup] at hnatLookup'
  cases hnatLookup'
  have hnatSortU := hnatSort0.instL (U' := Us.length) (ls := []) nofun
  have hnatSortU' : env.HasType Us.length [] .nat (.sort (u.inst [])) := by
    simpa [VExpr.nat, VExpr.instL] using hnatSortU
  exact ⟨.const hnatLookup rfl hnatUvars,
    ⟨u.inst [], hnatSortU'.weak0 wf (Γ := Δ.toCtx)⟩⟩

/-- Translate a reflected unary Nat primitive in an arbitrary verified local
context. -/
private theorem TrExprS.reflectedNatUnary
    {env : VEnv} (wf : env.WF) {name : Name} {f : Nat → Nat}
    (hreflect : env.ReflectsNatNat name f)
    (hcontains : env.contains name) (Us : List Name) (Δ : VLCtx)
    (hΔ : Δ.WF env Us.length) :
    TrExprS env Us Δ (.const name []) (.const name []) ∧
      env.HasType Us.length Δ.toCtx (.const name [])
        (.forallE .nat .nat) := by
  have hcontains' := hcontains
  obtain ⟨ci, hci⟩ := hcontains
  have htype := (hreflect hcontains').1 Us.length Δ.toCtx
  obtain ⟨ci', hci', _, hlen⟩ := htype.const_inv wf hΔ.toCtx
  have hc : ci' = ci := by rw [hci] at hci'; cases hci'; rfl
  subst ci'
  exact ⟨.const hci rfl hlen, htype⟩

/-- Translate a reflected binary Nat primitive in an arbitrary verified local
context. -/
private theorem TrExprS.reflectedNatBinary
    {env : VEnv} (wf : env.WF) {name : Name} {f : Nat → Nat → Nat}
    (hreflect : env.ReflectsNatNatNat name f)
    (hcontains : env.contains name) (Us : List Name) (Δ : VLCtx)
    (hΔ : Δ.WF env Us.length) :
    TrExprS env Us Δ (.const name []) (.const name []) ∧
      env.HasType Us.length Δ.toCtx (.const name [])
        (.forallE .nat <| .forallE .nat .nat) := by
  have hcontains' := hcontains
  obtain ⟨ci, hci⟩ := hcontains
  have htype := (hreflect hcontains').1 Us.length Δ.toCtx
  obtain ⟨ci', hci', _, hlen⟩ := htype.const_inv wf hΔ.toCtx
  have hc : ci' = ci := by rw [hci] at hci'; cases hci'; rfl
  subst ci'
  exact ⟨.const hci rfl hlen, htype⟩

/-- Presence of a certified Nat.pred constant entails presence of the Nat
type named by its reflected domain. -/
private theorem VEnv.HasPrimitives.nat_of_pred_contains
    {env : VEnv} (h : env.HasPrimitives) (wf : env.WF)
    (hpred : env.contains ``Nat.pred) : env.contains ``Nat := by
  have hfun := (h.natPred hpred).1 0 []
  have ⟨_, hfunType⟩ := hfun.isType wf trivial
  obtain ⟨⟨_, hnatType⟩, _⟩ := hfunType.forallE_inv wf
  obtain ⟨_, hnat, _⟩ := hnatType.const_inv wf trivial
  exact ⟨_, hnat⟩

/-- Presence of a reflected binary Nat primitive entails presence of the Nat
type named by its first domain. -/
private theorem VEnv.nat_of_reflected_binary_contains
    {env : VEnv} (wf : env.WF) {name : Name} {f : Nat → Nat → Nat}
    (hreflect : env.ReflectsNatNatNat name f)
    (hcontains : env.contains name) : env.contains ``Nat := by
  have hfun := (hreflect hcontains).1 0 []
  have ⟨_, hfunType⟩ := hfun.isType wf trivial
  obtain ⟨⟨_, hnatType⟩, _⟩ := hfunType.forallE_inv wf
  obtain ⟨_, hnat, _⟩ := hnatType.const_inv wf trivial
  exact ⟨_, hnat⟩

/-- Typed translations shared by the elementary binary `Nat` primitive
branches. -/
structure NatBinaryEvidence (c : VContext) (value : Expr) (value' : VExpr) :
    Prop where
  hnat : c.venv.contains ``Nat
  hΔ1 : VLCtx.WF c.venv c.lparams.length [(none, .vlam .nat)]
  hΔ2 : VLCtx.WF c.venv c.lparams.length
    [(none, .vlam .nat), (none, .vlam .nat)]
  hx1S : TrExprS c.venv c.lparams [(none, .vlam .nat)] (.bvar 0) (.bvar 0)
  hx1T : c.venv.HasType c.lparams.length [.nat] (.bvar 0) .nat
  hx2S : TrExprS c.venv c.lparams [(none, .vlam .nat), (none, .vlam .nat)]
    (.bvar 0) (.bvar 0)
  hy2S : TrExprS c.venv c.lparams [(none, .vlam .nat), (none, .vlam .nat)]
    (.bvar 1) (.bvar 1)
  hx2T : c.venv.HasType c.lparams.length [.nat, .nat] (.bvar 0) .nat
  hy2T : c.venv.HasType c.lparams.length [.nat, .nat] (.bvar 1) .nat
  hv1 : TrExprS c.venv c.lparams [(none, .vlam .nat)] value value'
  hv2 : TrExprS c.venv c.lparams [(none, .vlam .nat), (none, .vlam .nat)]
    value value'
  hv1T : c.venv.HasType c.lparams.length [.nat] value'
    (.forallE .nat <| .forallE .nat .nat)
  hv2T : c.venv.HasType c.lparams.length [.nat, .nat] value'
    (.forallE .nat <| .forallE .nat .nat)
  hrecS : TrExprS c.venv c.lparams [(none, .vlam .nat), (none, .vlam .nat)]
    (mkApp2 value (.bvar 1) (.bvar 0))
    (.app (.app value' (.bvar 1)) (.bvar 0))
  hrecT : c.venv.HasType c.lparams.length [.nat, .nat]
    (.app (.app value' (.bvar 1)) (.bvar 0)) .nat

theorem NatBinaryEvidence.mk' {c : VContext} {value : Expr} {value' : VExpr}
    (hnat : c.venv.contains ``Nat)
    (hvalue0 : TrExprS c.venv c.lparams [] value value')
    (hvalueCanonT : c.venv.HasType c.lparams.length [] value'
      (.forallE .nat <| .forallE .nat .nat)) :
    NatBinaryEvidence c value value' := by
  let Δ1 : VLCtx := [(none, .vlam .nat)]
  let Δ2 : VLCtx := [(none, .vlam .nat), (none, .vlam .nat)]
  have hnat0 := TrExprS.natType_of_contains c.Ewf c.hasPrimitives hnat c.lparams []
  have hnat1 := TrExprS.natType_of_contains c.Ewf c.hasPrimitives hnat c.lparams Δ1
  have hΔ1 : Δ1.WF c.venv c.lparams.length :=
    ⟨trivial, nofun, hnat0.2⟩
  have hΔ2 : Δ2.WF c.venv c.lparams.length :=
    ⟨hΔ1, nofun, hnat1.2⟩
  have hv1 : TrExprS c.venv c.lparams Δ1 value value' :=
    TrExprS.closed_weak c.Ewf hvalue0 (.skip (.vlam .nat) .refl)
  have hv2 : TrExprS c.venv c.lparams Δ2 value value' :=
    TrExprS.closed_weak c.Ewf hvalue0
      (.skip (.vlam .nat) (.skip (.vlam .nat) .refl))
  have hx1S : TrExprS c.venv c.lparams Δ1 (.bvar 0) (.bvar 0) :=
    .bvar (A := .nat) (by simp [Δ1, VLCtx.find?, VLCtx.next,
      VLocalDecl.value, VLocalDecl.type,
      VExpr.liftN, VExpr.lift, VExpr.nat])
  have hx1T : c.venv.HasType c.lparams.length [.nat] (.bvar 0) .nat := by
    simpa [VExpr.lift] using
      (VEnv.IsDefEq.bvar (env := c.venv) (uvars := c.lparams.length)
        (A := .nat) (i := 0) Lookup.zero)
  have hx2S : TrExprS c.venv c.lparams Δ2 (.bvar 0) (.bvar 0) :=
    .bvar (A := .nat) (by simp [Δ2, VLCtx.find?, VLCtx.next,
      VLocalDecl.value, VLocalDecl.type,
      VExpr.liftN, VExpr.lift, VExpr.nat])
  have hy2S : TrExprS c.venv c.lparams Δ2 (.bvar 1) (.bvar 1) :=
    .bvar (A := .nat) (by simp [Δ2, VLCtx.find?, VLCtx.next,
      VLocalDecl.value, VLocalDecl.type, VLocalDecl.depth,
      VExpr.liftN, VExpr.lift, VExpr.nat, liftVar])
  have hx2T : c.venv.HasType c.lparams.length [.nat, .nat]
      (.bvar 0) .nat := by
    simpa [VExpr.lift] using
      (VEnv.IsDefEq.bvar (env := c.venv) (uvars := c.lparams.length)
        (A := .nat) (i := 0) Lookup.zero)
  have hy2T : c.venv.HasType c.lparams.length [.nat, .nat]
      (.bvar 1) .nat := by
    simpa [VExpr.lift] using
      (VEnv.IsDefEq.bvar (env := c.venv) (uvars := c.lparams.length)
        (A := .nat) (i := 1) (Lookup.succ Lookup.zero))
  have hv1T := hvalueCanonT.weak0 c.Ewf (Γ := [.nat])
  have hv2T := hvalueCanonT.weak0 c.Ewf (Γ := [.nat, .nat])
  have hrecS : TrExprS c.venv c.lparams Δ2
      (mkApp2 value (.bvar 1) (.bvar 0))
      (.app (.app value' (.bvar 1)) (.bvar 0)) :=
    .app (.app hv2T hy2T) hx2T
      (.app hv2T hy2T hv2 hy2S) hx2S
  have hrecT : c.venv.HasType c.lparams.length [.nat, .nat]
      (.app (.app value' (.bvar 1)) (.bvar 0)) .nat :=
    .app (.app hv2T hy2T) hx2T
  exact ⟨hnat, hΔ1, hΔ2, hx1S, hx1T, hx2S, hy2S, hx2T, hy2T,
    hv1, hv2, hv1T, hv2T, hrecS, hrecT⟩

/-- Verify the common type, zero equation, and successor equation sequence for
an elementary binary-`Nat` primitive. -/
theorem checkNatBinaryTyped.WF {c : VContext} {s : VState}
    {P₁ P₂ : Prop} {ty value zR sR : Expr} {ty' value' zR' sR' : VExpr}
    {err : Exception}
    (h₁ : P₁) (h₂ : P₂)
    (hnat : c.venv.contains ``Nat)
    (hvlctx : c.vlctx = [])
    (hty : c.TrExprS ty ty')
    (hvalue0 : TrExprS c.venv c.lparams [] value value')
    (hvalueT0 : c.venv.HasType c.lparams.length [] value' ty')
    (hzR : NatBinaryEvidence c value value' →
      TrExprS c.venv c.lparams [(none, .vlam .nat)] zR zR')
    (hsR : NatBinaryEvidence c value value' →
      TrExprS c.venv c.lparams [(none, .vlam .nat), (none, .vlam .nat)]
        sR sR') :
    M.WF c s (do
      unless ← isDefEq ty q(Nat → Nat → Nat) do throw err
      unless ← isDefEq (.lam0 q(Nat) <| mkApp2 value (.bvar 0) q(Nat.zero))
        (.lam0 q(Nat) zR) do throw err
      unless ← isDefEq
        (.lam0 q(Nat) <| .lam0 q(Nat) <|
          mkApp2 value (.bvar 1) (mkApp q(Nat.succ) (.bvar 0)))
        (.lam0 q(Nat) <| .lam0 q(Nat) <| sR) do throw err) fun _ _ =>
        P₁ ∧ P₂ ∧
        c.venv.IsDefEqU c.lparams.length [] ty'
          (.forallE .nat <| .forallE .nat .nat) ∧
        c.venv.IsDefEqU c.lparams.length []
          (.lam .nat <| .app (.app value' (.bvar 0)) .natZero)
          (.lam .nat zR') ∧
        c.venv.IsDefEqU c.lparams.length []
          (.lam .nat <| .lam .nat <|
            .app (.app value' (.bvar 1)) (.app .natSucc (.bvar 0)))
          (.lam .nat <| .lam .nat <| sR') := by
  have hnat0 := TrExprS.natType_of_contains c.Ewf c.hasPrimitives hnat c.lparams []
  have hnat1 := TrExprS.natType_of_contains c.Ewf c.hasPrimitives hnat c.lparams
    [(none, .vlam .nat)]
  have hnat2 := TrExprS.natType_of_contains c.Ewf c.hasPrimitives hnat c.lparams
    [(none, .vlam .nat), (none, .vlam .nat)]
  have hinnerType : c.venv.IsType c.lparams.length [.nat]
      (.forallE .nat .nat) := by
    obtain ⟨u, hA⟩ := hnat1.2
    obtain ⟨w, hB⟩ := hnat2.2
    exact ⟨.imax u w, .forallEDF hA hB⟩
  have hcanon : c.TrExprS q(Nat → Nat → Nat)
      (.forallE .nat <| .forallE .nat .nat) := by
    change TrExprS c.venv c.lparams c.vlctx _ _
    rw [hvlctx]
    exact .forallE hnat0.2 hinnerType hnat0.1
      (.forallE hnat1.2 hnat2.2 hnat1.1 hnat2.1)
  exact (isDefEq.WF hty hcanon).bind fun b _ _ htyEq => by
    by_cases hb : b = true
    · rw [if_pos hb]
      have htyEq0 := htyEq hb
      change c.venv.IsDefEqU c.lparams.length c.vlctx.toCtx ty'
        (.forallE .nat <| .forallE .nat .nat) at htyEq0
      rw [hvlctx] at htyEq0
      have hvalueCanonT : c.venv.HasType c.lparams.length [] value'
          (.forallE .nat <| .forallE .nat .nat) :=
        hvalueT0.defeqU_r c.Ewf trivial htyEq0
      have ev : NatBinaryEvidence c value value' :=
        .mk' hnat hvalue0 hvalueCanonT
      have hzS := TrExprS.natZero c.hasPrimitives hnat
        (Us := c.lparams) (Δ := [(none, .vlam .nat)])
      have hsS := TrExprS.natSucc c.hasPrimitives hnat
        (Us := c.lparams) (Δ := [(none, .vlam .nat), (none, .vlam .nat)])
      have hz₁ : c.TrExprS
          (.lam0 q(Nat) <| mkApp2 value (.bvar 0) q(Nat.zero))
          (.lam .nat <| .app (.app value' (.bvar 0)) .natZero) := by
        change TrExprS c.venv c.lparams c.vlctx _ _
        rw [hvlctx]
        exact .lam hnat0.2 hnat0.1
          (.app (.app ev.hv1T ev.hx1T) hzS.2
            (.app ev.hv1T ev.hx1T ev.hv1 ev.hx1S) hzS.1)
      have hz₂ : c.TrExprS (.lam0 q(Nat) zR) (.lam .nat zR') := by
        change TrExprS c.venv c.lparams c.vlctx _ _
        rw [hvlctx]
        exact .lam hnat0.2 hnat0.1 (hzR ev)
      have hs₁ : c.TrExprS
          (.lam0 q(Nat) <| .lam0 q(Nat) <|
            mkApp2 value (.bvar 1) (mkApp q(Nat.succ) (.bvar 0)))
          (.lam .nat <| .lam .nat <|
            .app (.app value' (.bvar 1)) (.app .natSucc (.bvar 0))) := by
        change TrExprS c.venv c.lparams c.vlctx _ _
        rw [hvlctx]
        exact .lam hnat0.2 hnat0.1 (.lam hnat1.2 hnat1.1
          (.app (.app ev.hv2T ev.hy2T) (.app hsS.2 ev.hx2T)
            (.app ev.hv2T ev.hy2T ev.hv2 ev.hy2S)
            (.app hsS.2 ev.hx2T hsS.1 ev.hx2S)))
      have hs₂ : c.TrExprS (.lam0 q(Nat) <| .lam0 q(Nat) <| sR)
          (.lam .nat <| .lam .nat <| sR') := by
        change TrExprS c.venv c.lparams c.vlctx _ _
        rw [hvlctx]
        exact .lam hnat0.2 hnat0.1 (.lam hnat1.2 hnat1.1 (hsR ev))
      exact (isDefEq.WF hz₁ hz₂).bind fun z _ _ hzEq => by
        by_cases hzb : z = true
        · rw [if_pos hzb]
          have hzEq0 := hzEq hzb
          change c.venv.IsDefEqU c.lparams.length c.vlctx.toCtx _ _ at hzEq0
          rw [hvlctx] at hzEq0
          exact (isDefEq.WF hs₁ hs₂).bind fun p _ _ hsEq => by
            by_cases hsb : p = true
            · rw [if_pos hsb]
              have hsEq0 := hsEq hsb
              change c.venv.IsDefEqU c.lparams.length c.vlctx.toCtx _ _ at hsEq0
              rw [hvlctx] at hsEq0
              exact .pure ⟨h₁, h₂, htyEq0, hzEq0, hsEq0⟩
            · rw [if_neg hsb]
              exact .throw
        · rw [if_neg hzb]
          exact .throw
    · rw [if_neg hb]
      exact .throw

/-- Verify the common type and four constructor equations for a binary
`Nat → Nat → Bool` primitive. The three closed Boolean right-hand sides are
parameters so this checker is shared by `Nat.beq` and `Nat.ble`. -/
theorem checkNatBinaryBoolTyped.WF {c : VContext} {s : VState}
    {P₁ : Prop} {ty value r00 r0s rs0 : Expr}
    {ty' value' r00' r0s' rs0' : VExpr} {err : Exception}
    (h₁ : P₁)
    (hnat : c.venv.contains ``Nat) (hbool : c.venv.contains ``Bool)
    (hvlctx : c.vlctx = [])
    (hty : c.TrExprS ty ty')
    (hvalue0 : TrExprS c.venv c.lparams [] value value')
    (hvalueT0 : c.venv.HasType c.lparams.length [] value' ty')
    (hr00 : TrExprS c.venv c.lparams [] r00 r00')
    (hr0s : TrExprS c.venv c.lparams [(none, .vlam .nat)] r0s r0s')
    (hrs0 : TrExprS c.venv c.lparams [(none, .vlam .nat)] rs0 rs0') :
    M.WF c s (do
      unless ← isDefEq ty q(Nat → Nat → Bool) do throw err
      unless ← isDefEq (mkApp2 value q(Nat.zero) q(Nat.zero)) r00 do
        throw err
      unless ← isDefEq
        (.lam0 q(Nat) <| mkApp2 value q(Nat.zero)
          (mkApp q(Nat.succ) (.bvar 0)))
        (.lam0 q(Nat) r0s) do throw err
      unless ← isDefEq
        (.lam0 q(Nat) <| mkApp2 value
          (mkApp q(Nat.succ) (.bvar 0)) q(Nat.zero))
        (.lam0 q(Nat) rs0) do throw err
      unless ← isDefEq
        (.lam0 q(Nat) <| .lam0 q(Nat) <|
          mkApp2 value (mkApp q(Nat.succ) (.bvar 1))
            (mkApp q(Nat.succ) (.bvar 0)))
        (.lam0 q(Nat) <| .lam0 q(Nat) <|
          mkApp2 value (.bvar 1) (.bvar 0)) do throw err) fun _ _ =>
        P₁ ∧
        c.venv.contains ``Nat ∧ c.venv.contains ``Bool ∧
        c.venv.IsDefEqU c.lparams.length [] ty'
          (.forallE .nat <| .forallE .nat .bool) ∧
        c.venv.IsDefEqU c.lparams.length []
          (.app (.app value' .natZero) .natZero) r00' ∧
        c.venv.IsDefEqU c.lparams.length []
          (.lam .nat <| .app (.app value' .natZero)
            (.app .natSucc (.bvar 0))) (.lam .nat r0s') ∧
        c.venv.IsDefEqU c.lparams.length []
          (.lam .nat <| .app (.app value' (.app .natSucc (.bvar 0)))
            .natZero) (.lam .nat rs0') ∧
        c.venv.IsDefEqU c.lparams.length []
          (.lam .nat <| .lam .nat <|
            .app (.app value' (.app .natSucc (.bvar 1)))
              (.app .natSucc (.bvar 0)))
          (.lam .nat <| .lam .nat <|
            .app (.app value' (.bvar 1)) (.bvar 0)) := by
  let Δ1 : VLCtx := [(none, .vlam .nat)]
  let Δ2 : VLCtx := [(none, .vlam .nat), (none, .vlam .nat)]
  have hnat0 := TrExprS.natType_of_contains c.Ewf c.hasPrimitives hnat
    c.lparams []
  have hnat1 := TrExprS.natType_of_contains c.Ewf c.hasPrimitives hnat
    c.lparams Δ1
  have hbool2 := TrExprS.boolType_of_contains c.Ewf c.hasPrimitives hbool
    c.lparams Δ2
  have hinnerType : c.venv.IsType c.lparams.length [.nat]
      (.forallE .nat .bool) := by
    obtain ⟨u, hA⟩ := hnat1.2
    obtain ⟨w, hB⟩ := hbool2.2
    exact ⟨.imax u w, .forallEDF hA hB⟩
  have hcanon : c.TrExprS q(Nat → Nat → Bool)
      (.forallE .nat <| .forallE .nat .bool) := by
    change TrExprS c.venv c.lparams c.vlctx _ _
    rw [hvlctx]
    have hbool1 := TrExprS.boolType_of_contains c.Ewf c.hasPrimitives hbool
      c.lparams Δ2
    exact .forallE hnat0.2 hinnerType hnat0.1
      (.forallE hnat1.2 hbool1.2 hnat1.1 hbool1.1)
  exact (isDefEq.WF hty hcanon).bind fun b _ _ htyEq => by
    by_cases hb : b = true
    · rw [if_pos hb]
      have htyEq0 := htyEq hb
      change c.venv.IsDefEqU c.lparams.length c.vlctx.toCtx ty'
        (.forallE .nat <| .forallE .nat .bool) at htyEq0
      rw [hvlctx] at htyEq0
      have hvalueCanonT : c.venv.HasType c.lparams.length [] value'
          (.forallE .nat <| .forallE .nat .bool) :=
        hvalueT0.defeqU_r c.Ewf trivial htyEq0
      have hv1 : TrExprS c.venv c.lparams Δ1 value value' :=
        TrExprS.closed_weak c.Ewf hvalue0 (.skip (.vlam .nat) .refl)
      have hv2 : TrExprS c.venv c.lparams Δ2 value value' :=
        TrExprS.closed_weak c.Ewf hvalue0
          (.skip (.vlam .nat) (.skip (.vlam .nat) .refl))
      have hv1T := hvalueCanonT.weak0 c.Ewf (Γ := [.nat])
      have hv2T := hvalueCanonT.weak0 c.Ewf (Γ := [.nat, .nat])
      have hz0 := TrExprS.natZero c.hasPrimitives hnat
        (Us := c.lparams) (Δ := [])
      have hz1 := TrExprS.natZero c.hasPrimitives hnat
        (Us := c.lparams) (Δ := Δ1)
      have hs1 := TrExprS.natSucc c.hasPrimitives hnat
        (Us := c.lparams) (Δ := Δ1)
      have hs2 := TrExprS.natSucc c.hasPrimitives hnat
        (Us := c.lparams) (Δ := Δ2)
      have hx1S : TrExprS c.venv c.lparams Δ1 (.bvar 0) (.bvar 0) :=
        .bvar (A := .nat) (by simp [Δ1, VLCtx.find?, VLCtx.next,
          VLocalDecl.value, VLocalDecl.type,
          VExpr.liftN, VExpr.lift, VExpr.nat])
      have hx1T : c.venv.HasType c.lparams.length [.nat]
          (.bvar 0) .nat := by
        simpa [VExpr.lift] using
          (VEnv.IsDefEq.bvar (env := c.venv) (uvars := c.lparams.length)
            (A := .nat) (i := 0) Lookup.zero)
      have hx2S : TrExprS c.venv c.lparams Δ2 (.bvar 0) (.bvar 0) :=
        .bvar (A := .nat) (by simp [Δ2, VLCtx.find?, VLCtx.next,
          VLocalDecl.value, VLocalDecl.type,
          VExpr.liftN, VExpr.lift, VExpr.nat])
      have hy2S : TrExprS c.venv c.lparams Δ2 (.bvar 1) (.bvar 1) :=
        .bvar (A := .nat) (by simp [Δ2, VLCtx.find?, VLCtx.next,
          VLocalDecl.value, VLocalDecl.type, VLocalDecl.depth,
          VExpr.liftN, VExpr.lift, VExpr.nat, liftVar])
      have hx2T : c.venv.HasType c.lparams.length [.nat, .nat]
          (.bvar 0) .nat := by
        simpa [VExpr.lift] using
          (VEnv.IsDefEq.bvar (env := c.venv) (uvars := c.lparams.length)
            (A := .nat) (i := 0) Lookup.zero)
      have hy2T : c.venv.HasType c.lparams.length [.nat, .nat]
          (.bvar 1) .nat := by
        simpa [VExpr.lift] using
          (VEnv.IsDefEq.bvar (env := c.venv) (uvars := c.lparams.length)
            (A := .nat) (i := 1) (Lookup.succ Lookup.zero))
      have h00₁ : c.TrExprS
          (mkApp2 value q(Nat.zero) q(Nat.zero))
          (.app (.app value' .natZero) .natZero) := by
        change TrExprS c.venv c.lparams c.vlctx _ _
        rw [hvlctx]
        exact .app (.app hvalueCanonT hz0.2) hz0.2
          (.app hvalueCanonT hz0.2 hvalue0 hz0.1) hz0.1
      have h00₂ : c.TrExprS r00 r00' := by
        change TrExprS c.venv c.lparams c.vlctx _ _
        rw [hvlctx]
        exact hr00
      have hsx1S : TrExprS c.venv c.lparams Δ1
          (mkApp q(Nat.succ) (.bvar 0)) (.app .natSucc (.bvar 0)) :=
        .app hs1.2 hx1T hs1.1 hx1S
      have hsx1T : c.venv.HasType c.lparams.length [.nat]
          (.app .natSucc (.bvar 0)) .nat := .app hs1.2 hx1T
      have h0s₁ : c.TrExprS
          (.lam0 q(Nat) <| mkApp2 value q(Nat.zero)
            (mkApp q(Nat.succ) (.bvar 0)))
          (.lam .nat <| .app (.app value' .natZero)
            (.app .natSucc (.bvar 0))) := by
        change TrExprS c.venv c.lparams c.vlctx _ _
        rw [hvlctx]
        exact .lam hnat0.2 hnat0.1
          (.app (.app hv1T hz1.2) hsx1T
            (.app hv1T hz1.2 hv1 hz1.1) hsx1S)
      have hs0₁ : c.TrExprS
          (.lam0 q(Nat) <| mkApp2 value
            (mkApp q(Nat.succ) (.bvar 0)) q(Nat.zero))
          (.lam .nat <| .app (.app value' (.app .natSucc (.bvar 0)))
            .natZero) := by
        change TrExprS c.venv c.lparams c.vlctx _ _
        rw [hvlctx]
        exact .lam hnat0.2 hnat0.1
          (.app (.app hv1T hsx1T) hz1.2
            (.app hv1T hsx1T hv1 hsx1S) hz1.1)
      have h0s₂ : c.TrExprS (.lam0 q(Nat) r0s) (.lam .nat r0s') := by
        change TrExprS c.venv c.lparams c.vlctx _ _
        rw [hvlctx]
        exact .lam hnat0.2 hnat0.1 hr0s
      have hs0₂ : c.TrExprS (.lam0 q(Nat) rs0) (.lam .nat rs0') := by
        change TrExprS c.venv c.lparams c.vlctx _ _
        rw [hvlctx]
        exact .lam hnat0.2 hnat0.1 hrs0
      have hsx2S : TrExprS c.venv c.lparams Δ2
          (mkApp q(Nat.succ) (.bvar 0)) (.app .natSucc (.bvar 0)) :=
        .app hs2.2 hx2T hs2.1 hx2S
      have hsy2S : TrExprS c.venv c.lparams Δ2
          (mkApp q(Nat.succ) (.bvar 1)) (.app .natSucc (.bvar 1)) :=
        .app hs2.2 hy2T hs2.1 hy2S
      have hsx2T : c.venv.HasType c.lparams.length [.nat, .nat]
          (.app .natSucc (.bvar 0)) .nat := .app hs2.2 hx2T
      have hsy2T : c.venv.HasType c.lparams.length [.nat, .nat]
          (.app .natSucc (.bvar 1)) .nat := .app hs2.2 hy2T
      have hss₁ : c.TrExprS
          (.lam0 q(Nat) <| .lam0 q(Nat) <|
            mkApp2 value (mkApp q(Nat.succ) (.bvar 1))
              (mkApp q(Nat.succ) (.bvar 0)))
          (.lam .nat <| .lam .nat <|
            .app (.app value' (.app .natSucc (.bvar 1)))
              (.app .natSucc (.bvar 0))) := by
        change TrExprS c.venv c.lparams c.vlctx _ _
        rw [hvlctx]
        exact .lam hnat0.2 hnat0.1 (.lam hnat1.2 hnat1.1
          (.app (.app hv2T hsy2T) hsx2T
            (.app hv2T hsy2T hv2 hsy2S) hsx2S))
      have hss₂ : c.TrExprS
          (.lam0 q(Nat) <| .lam0 q(Nat) <|
            mkApp2 value (.bvar 1) (.bvar 0))
          (.lam .nat <| .lam .nat <|
            .app (.app value' (.bvar 1)) (.bvar 0)) := by
        change TrExprS c.venv c.lparams c.vlctx _ _
        rw [hvlctx]
        exact .lam hnat0.2 hnat0.1 (.lam hnat1.2 hnat1.1
          (.app (.app hv2T hy2T) hx2T
            (.app hv2T hy2T hv2 hy2S) hx2S))
      exact (isDefEq.WF h00₁ h00₂).bind fun b00 _ _ h00Eq => by
        by_cases hb00 : b00 = true
        · rw [if_pos hb00]
          have h00 := h00Eq hb00
          exact (isDefEq.WF h0s₁ h0s₂).bind fun b0s _ _ h0sEq => by
            by_cases hb0s : b0s = true
            · rw [if_pos hb0s]
              have h0s := h0sEq hb0s
              exact (isDefEq.WF hs0₁ hs0₂).bind fun bs0 _ _ hs0Eq => by
                by_cases hbs0 : bs0 = true
                · rw [if_pos hbs0]
                  have hs0 := hs0Eq hbs0
                  exact (isDefEq.WF hss₁ hss₂).bind fun bss _ _ hssEq => by
                    by_cases hbss : bss = true
                    · rw [if_pos hbss]
                      have hss := hssEq hbss
                      change c.venv.IsDefEqU c.lparams.length
                        c.vlctx.toCtx _ _ at h00 h0s hs0 hss
                      rw [hvlctx] at h00 h0s hs0 hss
                      exact .pure
                        ⟨h₁, hnat, hbool, htyEq0, h00, h0s, hs0, hss⟩
                    · rw [if_neg hbss]
                      exact .throw
                · rw [if_neg hbs0]
                  exact .throw
            · rw [if_neg hb0s]
              exact .throw
        · rw [if_neg hb00]
          exact .throw
    · rw [if_neg hb]
      exact .throw

/-- Verify the common type and two recursive equations for the binary Nat
shift primitives. The successor right-hand side is supplied by each concrete
primitive together with the translated literal `2`. -/
theorem checkNatShiftTyped.WF {c : VContext} {s : VState}
    {P₁ P₂ : Prop} {ty value sR : Expr} {ty' value' sR' : VExpr}
    {err : Exception}
    (h₁ : P₁) (h₂ : P₂)
    (hnat : c.venv.contains ``Nat)
    (hvlctx : c.vlctx = [])
    (hty : c.TrExprS ty ty')
    (hvalue0 : TrExprS c.venv c.lparams [] value value')
    (hvalueT0 : c.venv.HasType c.lparams.length [] value' ty')
    (hsR : NatBinaryEvidence c value value' →
      TrExprS c.venv c.lparams [(none, .vlam .nat), (none, .vlam .nat)]
        q(Nat.succ (Nat.succ Nat.zero)) (.natLit 2) →
      c.venv.HasType c.lparams.length [.nat, .nat] (.natLit 2) .nat →
      TrExprS c.venv c.lparams [(none, .vlam .nat), (none, .vlam .nat)]
        sR sR') :
    M.WF c s (do
      unless ← isDefEq ty q(Nat → Nat → Nat) do throw err
      unless ← isDefEq (.lam0 q(Nat) <| mkApp2 value (.bvar 0) q(Nat.zero))
        (.lam0 q(Nat) <| .bvar 0) do throw err
      unless ← isDefEq
        (.lam0 q(Nat) <| .lam0 q(Nat) <|
          mkApp2 value (.bvar 0) (mkApp q(Nat.succ) (.bvar 1)))
        (.lam0 q(Nat) <| .lam0 q(Nat) <| sR) do throw err) fun _ _ =>
        P₁ ∧ P₂ ∧
        c.venv.IsDefEqU c.lparams.length [] ty'
          (.forallE .nat <| .forallE .nat .nat) ∧
        c.venv.IsDefEqU c.lparams.length []
          (.lam .nat <| .app (.app value' (.bvar 0)) .natZero)
          (.lam .nat <| .bvar 0) ∧
        c.venv.IsDefEqU c.lparams.length []
          (.lam .nat <| .lam .nat <|
            .app (.app value' (.bvar 0)) (.app .natSucc (.bvar 1)))
          (.lam .nat <| .lam .nat <| sR') := by
  have hnat0 := TrExprS.natType_of_contains c.Ewf c.hasPrimitives hnat
    c.lparams []
  have hnat1 := TrExprS.natType_of_contains c.Ewf c.hasPrimitives hnat
    c.lparams [(none, .vlam .nat)]
  have hnat2 := TrExprS.natType_of_contains c.Ewf c.hasPrimitives hnat
    c.lparams [(none, .vlam .nat), (none, .vlam .nat)]
  have hinnerType : c.venv.IsType c.lparams.length [.nat]
      (.forallE .nat .nat) := by
    obtain ⟨u, hA⟩ := hnat1.2
    obtain ⟨w, hB⟩ := hnat2.2
    exact ⟨.imax u w, .forallEDF hA hB⟩
  have hcanon : c.TrExprS q(Nat → Nat → Nat)
      (.forallE .nat <| .forallE .nat .nat) := by
    change TrExprS c.venv c.lparams c.vlctx _ _
    rw [hvlctx]
    exact .forallE hnat0.2 hinnerType hnat0.1
      (.forallE hnat1.2 hnat2.2 hnat1.1 hnat2.1)
  exact (isDefEq.WF hty hcanon).bind fun b _ _ htyEq => by
    by_cases hb : b = true
    · rw [if_pos hb]
      have htyEq0 := htyEq hb
      change c.venv.IsDefEqU c.lparams.length c.vlctx.toCtx ty'
        (.forallE .nat <| .forallE .nat .nat) at htyEq0
      rw [hvlctx] at htyEq0
      have hvalueCanonT : c.venv.HasType c.lparams.length [] value'
          (.forallE .nat <| .forallE .nat .nat) :=
        hvalueT0.defeqU_r c.Ewf trivial htyEq0
      have ev : NatBinaryEvidence c value value' :=
        .mk' hnat hvalue0 hvalueCanonT
      have hzS1 := TrExprS.natZero c.hasPrimitives hnat
        (Us := c.lparams) (Δ := [(none, .vlam .nat)])
      have hsS := TrExprS.natSucc c.hasPrimitives hnat
        (Us := c.lparams) (Δ := [(none, .vlam .nat), (none, .vlam .nat)])
      have hz₁ : c.TrExprS
          (.lam0 q(Nat) <| mkApp2 value (.bvar 0) q(Nat.zero))
          (.lam .nat <| .app (.app value' (.bvar 0)) .natZero) := by
        change TrExprS c.venv c.lparams c.vlctx _ _
        rw [hvlctx]
        exact .lam hnat0.2 hnat0.1
          (.app (.app ev.hv1T ev.hx1T) hzS1.2
            (.app ev.hv1T ev.hx1T ev.hv1 ev.hx1S) hzS1.1)
      have hz₂ : c.TrExprS (.lam0 q(Nat) <| .bvar 0)
          (.lam .nat <| .bvar 0) := by
        change TrExprS c.venv c.lparams c.vlctx _ _
        rw [hvlctx]
        exact .lam hnat0.2 hnat0.1 ev.hx1S
      have hsyS : TrExprS c.venv c.lparams
          [(none, .vlam .nat), (none, .vlam .nat)]
          (mkApp q(Nat.succ) (.bvar 1))
          (.app .natSucc (.bvar 1)) := .app hsS.2 ev.hy2T hsS.1 ev.hy2S
      have hsyT : c.venv.HasType c.lparams.length [.nat, .nat]
          (.app .natSucc (.bvar 1)) .nat := .app hsS.2 ev.hy2T
      have hs₁ : c.TrExprS
          (.lam0 q(Nat) <| .lam0 q(Nat) <|
            mkApp2 value (.bvar 0) (mkApp q(Nat.succ) (.bvar 1)))
          (.lam .nat <| .lam .nat <|
            .app (.app value' (.bvar 0)) (.app .natSucc (.bvar 1))) := by
        change TrExprS c.venv c.lparams c.vlctx _ _
        rw [hvlctx]
        exact .lam hnat0.2 hnat0.1 (.lam hnat1.2 hnat1.1
          (.app (.app ev.hv2T ev.hx2T) hsyT
            (.app ev.hv2T ev.hx2T ev.hv2 ev.hx2S) hsyS))
      have hzeroS2 := TrExprS.natZero c.hasPrimitives hnat
        (Us := c.lparams) (Δ := [(none, .vlam .nat), (none, .vlam .nat)])
      have honeS : TrExprS c.venv c.lparams
          [(none, .vlam .nat), (none, .vlam .nat)] q(Nat.succ Nat.zero)
          (.natLit 1) := .app hsS.2 hzeroS2.2 hsS.1 hzeroS2.1
      have honeT : c.venv.HasType c.lparams.length [.nat, .nat]
          (.natLit 1) .nat := .app hsS.2 hzeroS2.2
      have htwoS : TrExprS c.venv c.lparams
          [(none, .vlam .nat), (none, .vlam .nat)]
          q(Nat.succ (Nat.succ Nat.zero)) (.natLit 2) :=
        .app hsS.2 honeT hsS.1 honeS
      have htwoT : c.venv.HasType c.lparams.length [.nat, .nat]
          (.natLit 2) .nat := .app hsS.2 honeT
      have hs₂ : c.TrExprS (.lam0 q(Nat) <| .lam0 q(Nat) <| sR)
          (.lam .nat <| .lam .nat <| sR') := by
        change TrExprS c.venv c.lparams c.vlctx _ _
        rw [hvlctx]
        exact .lam hnat0.2 hnat0.1 (.lam hnat1.2 hnat1.1
          (hsR ev htwoS htwoT))
      exact (isDefEq.WF hz₁ hz₂).bind fun z _ _ hzEq => by
        by_cases hzb : z = true
        · rw [if_pos hzb]
          have hzEq0 := hzEq hzb
          change c.venv.IsDefEqU c.lparams.length c.vlctx.toCtx _ _ at hzEq0
          rw [hvlctx] at hzEq0
          exact (isDefEq.WF hs₁ hs₂).bind fun p _ _ hsEq => by
            by_cases hsb : p = true
            · rw [if_pos hsb]
              have hsEq0 := hsEq hsb
              change c.venv.IsDefEqU c.lparams.length c.vlctx.toCtx _ _
                at hsEq0
              rw [hvlctx] at hsEq0
              exact .pure ⟨h₁, h₂, htyEq0, hzEq0, hsEq0⟩
            · rw [if_neg hsb]
              exact .throw
        · rw [if_neg hzb]
          exact .throw
    · rw [if_neg hb]
      exact .throw

/-- Exact typed certificate for the public `Nat.add` recognizer branch. -/
theorem checkPrimitiveDef.natAdd.WF_typed {c : VContext} {s : VState}
    (hname : v.name = ``Nat.add)
    (hvlctx : c.vlctx = [])
    (hty : c.TrExprS v.type ty')
    (hvalue : c.TrExprS v.value value')
    (hvalueT : c.HasType value' ty') :
    M.WF c s (checkPrimitiveDef v) fun b _ => b →
      v.levelParams = [] ∧
      c.venv.contains ``Nat ∧
      c.venv.IsDefEqU c.lparams.length [] ty'
        (.forallE .nat <| .forallE .nat .nat) ∧
      c.venv.IsDefEqU c.lparams.length []
        (.lam .nat <| .app (.app value' (.bvar 0)) .natZero)
        (.lam .nat <| .bvar 0) ∧
      c.venv.IsDefEqU c.lparams.length []
        (.lam .nat <| .lam .nat <|
          .app (.app value' (.bvar 1)) (.app .natSucc (.bvar 0)))
        (.lam .nat <| .lam .nat <|
          .app .natSucc (.app (.app value' (.bvar 1)) (.bvar 0))) := by
  apply checkPrimitiveDef.WF_of_core (by simp)
  simp only [checkPrimitiveDefCore, hname, checkNatAddPrimitive]
  refine getEnv.WF.bind ?_
  intro _ _ _ ⟨rfl, rfl⟩
  split
  · rename_i hdeps
    have hdeps' : c.env.contains ``Nat = true ∧
        v.levelParams.isEmpty = true := by simpa using hdeps
    have hlevels : v.levelParams = [] := by simpa using hdeps'.2
    have hnat : c.venv.contains ``Nat :=
      VContext.contains_safe_primitive c hdeps'.1 (by
        simp [Lean.Kernel.Environment.primitives,
          NameSet.contains, NameSet.ofList])
    have hvalue0 := hvalue
    change TrExprS c.venv c.lparams c.vlctx v.value value' at hvalue0
    rw [hvlctx] at hvalue0
    have hvalueT0 := hvalueT
    change c.venv.HasType c.lparams.length c.vlctx.toCtx value' ty' at hvalueT0
    rw [hvlctx] at hvalueT0
    exact (checkNatBinaryTyped.WF hlevels hnat hnat hvlctx hty hvalue0 hvalueT0
        (fun ev => ev.hx1S)
        (fun ev =>
          have hsS := TrExprS.natSucc c.hasPrimitives ev.hnat
            (Us := c.lparams) (Δ := [(none, .vlam .nat), (none, .vlam .nat)])
          .app hsS.2 ev.hrecT hsS.1 ev.hrecS)).bind
      fun _ _ _ h => .pure fun _ => h
  · exact .throw

/-- Exact typed certificate for the public `Nat.pred` recognizer branch. -/
theorem checkPrimitiveDef.natPred.WF_typed {c : VContext} {s : VState}
    (hname : v.name = ``Nat.pred)
    (hvlctx : c.vlctx = [])
    (hty : c.TrExprS v.type ty')
    (hvalue : c.TrExprS v.value value')
    (hvalueT : c.HasType value' ty') :
    M.WF c s (checkPrimitiveDef v) fun b _ => b →
      v.levelParams = [] ∧
      c.venv.contains ``Nat ∧
      c.venv.IsDefEqU c.lparams.length [] ty' (.forallE .nat .nat) ∧
      c.venv.IsDefEqU c.lparams.length []
        (.app value' .natZero) .natZero ∧
      c.venv.IsDefEqU c.lparams.length []
        (.lam .nat <| .app value' (.app .natSucc (.bvar 0)))
        (.lam .nat <| .bvar 0) := by
  apply checkPrimitiveDef.WF_of_core (by simp)
  simp only [checkPrimitiveDefCore, hname, checkNatPredPrimitive]
  refine getEnv.WF.bind ?_
  intro _ _ _ ⟨rfl, rfl⟩
  split
  · rename_i hdeps
    have hdeps' : c.env.contains ``Nat = true ∧
        v.levelParams.isEmpty = true := by simpa using hdeps
    have hlevels : v.levelParams = [] := by simpa using hdeps'.2
    have hnat : c.venv.contains ``Nat :=
      VContext.contains_safe_primitive c hdeps'.1 (by
        simp [Lean.Kernel.Environment.primitives,
          NameSet.contains, NameSet.ofList])
    have hvalue0 := hvalue
    change TrExprS c.venv c.lparams c.vlctx v.value value' at hvalue0
    rw [hvlctx] at hvalue0
    have hvalueT0 := hvalueT
    change c.venv.HasType c.lparams.length c.vlctx.toCtx value' ty' at hvalueT0
    rw [hvlctx] at hvalueT0
    let Δ1 : VLCtx := [(none, .vlam .nat)]
    have hnat0 := TrExprS.natType_of_contains c.Ewf c.hasPrimitives hnat
      c.lparams []
    have hnat1 := TrExprS.natType_of_contains c.Ewf c.hasPrimitives hnat
      c.lparams Δ1
    have hcanon0 : TrExprS c.venv c.lparams [] q(Nat → Nat)
        (.forallE .nat .nat) :=
      .forallE hnat0.2 hnat1.2 hnat0.1 hnat1.1
    have hcanon : c.TrExprS q(Nat → Nat) (.forallE .nat .nat) := by
      change TrExprS c.venv c.lparams c.vlctx _ _
      rw [hvlctx]
      exact hcanon0
    exact ((isDefEq.WF hty hcanon).bind fun b _ _ htyEq => by
      by_cases hb : b = true
      · rw [if_pos hb]
        have htyEq0 := htyEq hb
        change c.venv.IsDefEqU c.lparams.length c.vlctx.toCtx ty'
          (.forallE .nat .nat) at htyEq0
        rw [hvlctx] at htyEq0
        have hvalueCanonT : c.venv.HasType c.lparams.length [] value'
            (.forallE .nat .nat) :=
          hvalueT0.defeqU_r c.Ewf trivial htyEq0
        have hzS := TrExprS.natZero c.hasPrimitives hnat
          (Us := c.lparams) (Δ := [])
        have hsS := TrExprS.natSucc c.hasPrimitives hnat
          (Us := c.lparams) (Δ := Δ1)
        have hz₁0 : TrExprS c.venv c.lparams []
            (mkApp v.value q(Nat.zero)) (.app value' .natZero) :=
          .app hvalueCanonT hzS.2 hvalue0 hzS.1
        have hz₁ : c.TrExprS (mkApp v.value q(Nat.zero))
            (.app value' .natZero) := by
          change TrExprS c.venv c.lparams c.vlctx _ _
          rw [hvlctx]
          exact hz₁0
        have hz₂ : c.TrExprS q(Nat.zero) .natZero := by
          change TrExprS c.venv c.lparams c.vlctx _ _
          rw [hvlctx]
          exact hzS.1
        have hv1 : TrExprS c.venv c.lparams Δ1 v.value value' :=
          TrExprS.closed_weak c.Ewf hvalue0 (.skip (.vlam .nat) .refl)
        have hv1T := hvalueCanonT.weak0 c.Ewf (Γ := [.nat])
        have hx1S : TrExprS c.venv c.lparams Δ1 (.bvar 0) (.bvar 0) :=
          .bvar (A := .nat) (by simp [Δ1, VLCtx.find?, VLCtx.next,
            VLocalDecl.value, VLocalDecl.type,
            VExpr.liftN, VExpr.lift, VExpr.nat])
        have hx1T : c.venv.HasType c.lparams.length [.nat]
            (.bvar 0) .nat := by
          simpa [VExpr.lift] using
            (VEnv.IsDefEq.bvar (env := c.venv) (uvars := c.lparams.length)
              (A := .nat) (i := 0) Lookup.zero)
        have hsxS : TrExprS c.venv c.lparams Δ1
            (mkApp q(Nat.succ) (.bvar 0))
            (.app .natSucc (.bvar 0)) :=
          .app hsS.2 hx1T hsS.1 hx1S
        have hsxT : c.venv.HasType c.lparams.length [.nat]
            (.app .natSucc (.bvar 0)) .nat := .app hsS.2 hx1T
        have hsBodyS : TrExprS c.venv c.lparams Δ1
            (mkApp v.value (mkApp q(Nat.succ) (.bvar 0)))
            (.app value' (.app .natSucc (.bvar 0))) :=
          .app hv1T hsxT hv1 hsxS
        have hs₁0 : TrExprS c.venv c.lparams []
            (.lam0 q(Nat) <| mkApp v.value
              (mkApp q(Nat.succ) (.bvar 0)))
            (.lam .nat <| .app value' (.app .natSucc (.bvar 0))) :=
          .lam hnat0.2 hnat0.1 hsBodyS
        have hs₁ : c.TrExprS
            (.lam0 q(Nat) <| mkApp v.value
              (mkApp q(Nat.succ) (.bvar 0)))
            (.lam .nat <| .app value' (.app .natSucc (.bvar 0))) := by
          change TrExprS c.venv c.lparams c.vlctx _ _
          rw [hvlctx]
          exact hs₁0
        have hs₂0 : TrExprS c.venv c.lparams []
            (.lam0 q(Nat) <| .bvar 0) (.lam .nat <| .bvar 0) :=
          .lam hnat0.2 hnat0.1 hx1S
        have hs₂ : c.TrExprS (.lam0 q(Nat) <| .bvar 0)
            (.lam .nat <| .bvar 0) := by
          change TrExprS c.venv c.lparams c.vlctx _ _
          rw [hvlctx]
          exact hs₂0
        exact (isDefEq.WF hz₁ hz₂).bind fun z _ _ hzEq => by
          by_cases hzb : z = true
          · rw [if_pos hzb]
            have hzEq0 := hzEq hzb
            change c.venv.IsDefEqU c.lparams.length c.vlctx.toCtx _ _ at hzEq0
            rw [hvlctx] at hzEq0
            exact (isDefEq.WF hs₁ hs₂).bind fun q _ _ hsEq => by
              by_cases hsb : q = true
              · rw [if_pos hsb]
                have hsEq0 := hsEq hsb
                change c.venv.IsDefEqU c.lparams.length c.vlctx.toCtx _ _ at hsEq0
                rw [hvlctx] at hsEq0
                exact .pure ⟨hlevels, hnat, htyEq0, hzEq0, hsEq0⟩
              · rw [if_neg hsb]
                exact .throw
          · rw [if_neg hzb]
            exact .throw
      · rw [if_neg hb]
        exact .throw
    ).bind fun _ _ _ h => .pure fun _ => h
  · exact .throw

/-- Exact typed certificate for the public `Nat.sub` recognizer branch. -/
theorem checkPrimitiveDef.natSub.WF_typed {c : VContext} {s : VState}
    (hname : v.name = ``Nat.sub)
    (hvlctx : c.vlctx = [])
    (hty : c.TrExprS v.type ty')
    (hvalue : c.TrExprS v.value value')
    (hvalueT : c.HasType value' ty') :
    M.WF c s (checkPrimitiveDef v) fun b _ => b →
      v.levelParams = [] ∧
      c.venv.contains ``Nat.pred ∧
      c.venv.IsDefEqU c.lparams.length [] ty'
        (.forallE .nat <| .forallE .nat .nat) ∧
      c.venv.IsDefEqU c.lparams.length []
        (.lam .nat <| .app (.app value' (.bvar 0)) .natZero)
        (.lam .nat <| .bvar 0) ∧
      c.venv.IsDefEqU c.lparams.length []
        (.lam .nat <| .lam .nat <|
          .app (.app value' (.bvar 1)) (.app .natSucc (.bvar 0)))
        (.lam .nat <| .lam .nat <|
          .app (.const ``Nat.pred [])
            (.app (.app value' (.bvar 1)) (.bvar 0))) := by
  apply checkPrimitiveDef.WF_of_core (by simp)
  simp only [checkPrimitiveDefCore, hname, checkNatSubPrimitive]
  refine getEnv.WF.bind ?_
  intro _ _ _ ⟨rfl, rfl⟩
  split
  · rename_i hdeps
    have hdeps' : c.env.contains ``Nat.pred = true ∧
        v.levelParams.isEmpty = true := by simpa using hdeps
    have hlevels : v.levelParams = [] := by simpa using hdeps'.2
    have hpred : c.venv.contains ``Nat.pred :=
      VContext.contains_safe_primitive c hdeps'.1 (by
        simp [Lean.Kernel.Environment.primitives,
          NameSet.contains, NameSet.ofList])
    have hnat := VEnv.HasPrimitives.nat_of_pred_contains
      c.hasPrimitives c.Ewf hpred
    have hvalue0 := hvalue
    change TrExprS c.venv c.lparams c.vlctx v.value value' at hvalue0
    rw [hvlctx] at hvalue0
    have hvalueT0 := hvalueT
    change c.venv.HasType c.lparams.length c.vlctx.toCtx value' ty' at hvalueT0
    rw [hvlctx] at hvalueT0
    exact (checkNatBinaryTyped.WF hlevels hpred hnat hvlctx hty hvalue0
        hvalueT0 (fun ev => ev.hx1S)
        (fun ev =>
          have hpredS := TrExprS.reflectedNatUnary c.Ewf
            c.hasPrimitives.natPred hpred c.lparams _ ev.hΔ2
          .app hpredS.2 ev.hrecT hpredS.1 ev.hrecS)).bind
      fun _ _ _ h => .pure fun _ => h
  · exact .throw

/-- Exact typed certificate for the public `Nat.mul` recognizer branch. -/
theorem checkPrimitiveDef.natMul.WF_typed {c : VContext} {s : VState}
    (hname : v.name = ``Nat.mul)
    (hvlctx : c.vlctx = [])
    (hty : c.TrExprS v.type ty')
    (hvalue : c.TrExprS v.value value')
    (hvalueT : c.HasType value' ty') :
    M.WF c s (checkPrimitiveDef v) fun b _ => b →
      v.levelParams = [] ∧
      c.venv.contains ``Nat.add ∧
      c.venv.IsDefEqU c.lparams.length [] ty'
        (.forallE .nat <| .forallE .nat .nat) ∧
      c.venv.IsDefEqU c.lparams.length []
        (.lam .nat <| .app (.app value' (.bvar 0)) .natZero)
        (.lam .nat .natZero) ∧
      c.venv.IsDefEqU c.lparams.length []
        (.lam .nat <| .lam .nat <|
          .app (.app value' (.bvar 1)) (.app .natSucc (.bvar 0)))
        (.lam .nat <| .lam .nat <|
          .app (.app (.const ``Nat.add [])
            (.app (.app value' (.bvar 1)) (.bvar 0))) (.bvar 1)) := by
  apply checkPrimitiveDef.WF_of_core (by simp)
  simp only [checkPrimitiveDefCore, hname, checkNatMulPrimitive]
  refine getEnv.WF.bind ?_
  intro _ _ _ ⟨rfl, rfl⟩
  split
  · rename_i hdeps
    have hdeps' : c.env.contains ``Nat.add = true ∧
        v.levelParams.isEmpty = true := by simpa using hdeps
    have hlevels : v.levelParams = [] := by simpa using hdeps'.2
    have haddC : c.venv.contains ``Nat.add :=
      VContext.contains_safe_primitive c hdeps'.1 (by
        simp [Lean.Kernel.Environment.primitives,
          NameSet.contains, NameSet.ofList])
    have hnat := VEnv.nat_of_reflected_binary_contains c.Ewf
      c.hasPrimitives.natAdd haddC
    have hvalue0 := hvalue
    change TrExprS c.venv c.lparams c.vlctx v.value value' at hvalue0
    rw [hvlctx] at hvalue0
    have hvalueT0 := hvalueT
    change c.venv.HasType c.lparams.length c.vlctx.toCtx value' ty' at hvalueT0
    rw [hvlctx] at hvalueT0
    exact (checkNatBinaryTyped.WF hlevels haddC hnat hvlctx hty hvalue0
        hvalueT0
        (fun ev => (TrExprS.natZero c.hasPrimitives ev.hnat
          (Us := c.lparams) (Δ := [(none, .vlam .nat)])).1)
        (fun ev =>
          have hopS := TrExprS.reflectedNatBinary c.Ewf
            c.hasPrimitives.natAdd haddC c.lparams _ ev.hΔ2
          .app (.app hopS.2 ev.hrecT) ev.hy2T
            (.app hopS.2 ev.hrecT hopS.1 ev.hrecS) ev.hy2S)).bind
      fun _ _ _ h => .pure fun _ => h
  · exact .throw

/-- Exact typed certificate for the public `Nat.pow` recognizer branch. -/
theorem checkPrimitiveDef.natPow.WF_typed {c : VContext} {s : VState}
    (hname : v.name = ``Nat.pow)
    (hvlctx : c.vlctx = [])
    (hty : c.TrExprS v.type ty')
    (hvalue : c.TrExprS v.value value')
    (hvalueT : c.HasType value' ty') :
    M.WF c s (checkPrimitiveDef v) fun b _ => b →
      v.levelParams = [] ∧
      c.venv.contains ``Nat.mul ∧
      c.venv.IsDefEqU c.lparams.length [] ty'
        (.forallE .nat <| .forallE .nat .nat) ∧
      c.venv.IsDefEqU c.lparams.length []
        (.lam .nat <| .app (.app value' (.bvar 0)) .natZero)
        (.lam .nat <| .app .natSucc .natZero) ∧
      c.venv.IsDefEqU c.lparams.length []
        (.lam .nat <| .lam .nat <|
          .app (.app value' (.bvar 1)) (.app .natSucc (.bvar 0)))
        (.lam .nat <| .lam .nat <|
          .app (.app (.const ``Nat.mul [])
            (.app (.app value' (.bvar 1)) (.bvar 0))) (.bvar 1)) := by
  apply checkPrimitiveDef.WF_of_core (by simp)
  simp only [checkPrimitiveDefCore, hname, checkNatPowPrimitive]
  refine getEnv.WF.bind ?_
  intro _ _ _ ⟨rfl, rfl⟩
  split
  · rename_i hdeps
    have hdeps' : c.env.contains ``Nat.mul = true ∧
        v.levelParams.isEmpty = true := by simpa using hdeps
    have hlevels : v.levelParams = [] := by simpa using hdeps'.2
    have hmulC : c.venv.contains ``Nat.mul :=
      VContext.contains_safe_primitive c hdeps'.1 (by
        simp [Lean.Kernel.Environment.primitives,
          NameSet.contains, NameSet.ofList])
    have hnat := VEnv.nat_of_reflected_binary_contains c.Ewf
      c.hasPrimitives.natMul hmulC
    have hvalue0 := hvalue
    change TrExprS c.venv c.lparams c.vlctx v.value value' at hvalue0
    rw [hvlctx] at hvalue0
    have hvalueT0 := hvalueT
    change c.venv.HasType c.lparams.length c.vlctx.toCtx value' ty' at hvalueT0
    rw [hvlctx] at hvalueT0
    exact (checkNatBinaryTyped.WF hlevels hmulC hnat hvlctx hty hvalue0
        hvalueT0
        (fun ev =>
          have hzS := TrExprS.natZero c.hasPrimitives ev.hnat
            (Us := c.lparams) (Δ := [(none, .vlam .nat)])
          have hsS := TrExprS.natSucc c.hasPrimitives ev.hnat
            (Us := c.lparams) (Δ := [(none, .vlam .nat)])
          .app hsS.2 hzS.2 hsS.1 hzS.1)
        (fun ev =>
          have hopS := TrExprS.reflectedNatBinary c.Ewf
            c.hasPrimitives.natMul hmulC c.lparams _ ev.hΔ2
          .app (.app hopS.2 ev.hrecT) ev.hy2T
            (.app hopS.2 ev.hrecT hopS.1 ev.hrecS) ev.hy2S)).bind
      fun _ _ _ h => .pure fun _ => h
  · exact .throw

/-- Exact typed certificate for the public `Nat.shiftLeft` recognizer branch. -/
theorem checkPrimitiveDef.natShiftLeft.WF_typed {c : VContext} {s : VState}
    (hname : v.name = ``Nat.shiftLeft)
    (hvlctx : c.vlctx = [])
    (hty : c.TrExprS v.type ty')
    (hvalue : c.TrExprS v.value value')
    (hvalueT : c.HasType value' ty') :
    M.WF c s (checkPrimitiveDef v) fun b _ => b →
      v.levelParams = [] ∧
      c.venv.contains ``Nat.mul ∧
      c.venv.IsDefEqU c.lparams.length [] ty'
        (.forallE .nat <| .forallE .nat .nat) ∧
      c.venv.IsDefEqU c.lparams.length []
        (.lam .nat <| .app (.app value' (.bvar 0)) .natZero)
        (.lam .nat <| .bvar 0) ∧
      c.venv.IsDefEqU c.lparams.length []
        (.lam .nat <| .lam .nat <|
          .app (.app value' (.bvar 0)) (.app .natSucc (.bvar 1)))
        (.lam .nat <| .lam .nat <|
          .app (.app value'
            (.app (.app (.const ``Nat.mul []) (.natLit 2)) (.bvar 0)))
            (.bvar 1)) := by
  apply checkPrimitiveDef.WF_of_core (by simp)
  simp only [checkPrimitiveDefCore, hname, checkNatShiftLeftPrimitive]
  refine getEnv.WF.bind ?_
  intro _ _ _ ⟨rfl, rfl⟩
  split
  · rename_i hdeps
    have hdeps' : c.env.contains ``Nat.mul = true ∧
        v.levelParams.isEmpty = true := by simpa using hdeps
    have hlevels : v.levelParams = [] := by simpa using hdeps'.2
    have hmulC : c.venv.contains ``Nat.mul :=
      VContext.contains_safe_primitive c hdeps'.1 (by
        simp [Lean.Kernel.Environment.primitives,
          NameSet.contains, NameSet.ofList])
    have hnat := VEnv.nat_of_reflected_binary_contains c.Ewf
      c.hasPrimitives.natMul hmulC
    have hvalue0 := hvalue
    change TrExprS c.venv c.lparams c.vlctx v.value value' at hvalue0
    rw [hvlctx] at hvalue0
    have hvalueT0 := hvalueT
    change c.venv.HasType c.lparams.length c.vlctx.toCtx value' ty' at hvalueT0
    rw [hvlctx] at hvalueT0
    exact (checkNatShiftTyped.WF hlevels hmulC hnat hvlctx hty
        hvalue0 hvalueT0
        (fun ev htwoS htwoT =>
          have hmulS := TrExprS.reflectedNatBinary c.Ewf
            c.hasPrimitives.natMul hmulC c.lparams _ ev.hΔ2
          have hmulTwoS : TrExprS c.venv c.lparams
              [(none, .vlam .nat), (none, .vlam .nat)]
              (mkApp q(Nat.mul) q(Nat.succ (Nat.succ Nat.zero)))
              (.app (.const ``Nat.mul []) (.natLit 2)) :=
            .app hmulS.2 htwoT hmulS.1 htwoS
          have hmulTwoT : c.venv.HasType c.lparams.length [.nat, .nat]
              (.app (.const ``Nat.mul []) (.natLit 2))
              (.forallE .nat .nat) := .app hmulS.2 htwoT
          have hmulTwoXS : TrExprS c.venv c.lparams
              [(none, .vlam .nat), (none, .vlam .nat)]
              (mkApp2 q(Nat.mul) q(Nat.succ (Nat.succ Nat.zero)) (.bvar 0))
              (.app (.app (.const ``Nat.mul []) (.natLit 2)) (.bvar 0)) :=
            .app hmulTwoT ev.hx2T hmulTwoS ev.hx2S
          have hmulTwoXT : c.venv.HasType c.lparams.length [.nat, .nat]
              (.app (.app (.const ``Nat.mul []) (.natLit 2)) (.bvar 0)) .nat :=
            .app hmulTwoT ev.hx2T
          have hvMulS : TrExprS c.venv c.lparams
              [(none, .vlam .nat), (none, .vlam .nat)]
              (mkApp v.value
                (mkApp2 q(Nat.mul) q(Nat.succ (Nat.succ Nat.zero)) (.bvar 0)))
              (.app value'
                (.app (.app (.const ``Nat.mul []) (.natLit 2)) (.bvar 0))) :=
            .app ev.hv2T hmulTwoXT ev.hv2 hmulTwoXS
          have hvMulT : c.venv.HasType c.lparams.length [.nat, .nat]
              (.app value'
                (.app (.app (.const ``Nat.mul []) (.natLit 2)) (.bvar 0)))
              (.forallE .nat .nat) := .app ev.hv2T hmulTwoXT
          .app hvMulT ev.hy2T hvMulS ev.hy2S)).bind
      fun _ _ _ h => .pure fun _ => h
  · exact .throw

/-- Exact typed certificate for the public `Nat.beq` recognizer branch. -/
theorem checkPrimitiveDef.natBEq.WF_typed {c : VContext} {s : VState}
    (hname : v.name = ``Nat.beq)
    (hvlctx : c.vlctx = [])
    (hty : c.TrExprS v.type ty')
    (hvalue : c.TrExprS v.value value')
    (hvalueT : c.HasType value' ty') :
    M.WF c s (checkPrimitiveDef v) fun b _ => b →
      v.levelParams = [] ∧
      c.venv.contains ``Nat ∧ c.venv.contains ``Bool ∧
      c.venv.IsDefEqU c.lparams.length [] ty'
        (.forallE .nat <| .forallE .nat .bool) ∧
      c.venv.IsDefEqU c.lparams.length []
        (.app (.app value' .natZero) .natZero) .boolTrue ∧
      c.venv.IsDefEqU c.lparams.length []
        (.lam .nat <| .app (.app value' .natZero)
          (.app .natSucc (.bvar 0))) (.lam .nat .boolFalse) ∧
      c.venv.IsDefEqU c.lparams.length []
        (.lam .nat <| .app (.app value' (.app .natSucc (.bvar 0)))
          .natZero) (.lam .nat .boolFalse) ∧
      c.venv.IsDefEqU c.lparams.length []
        (.lam .nat <| .lam .nat <|
          .app (.app value' (.app .natSucc (.bvar 1)))
            (.app .natSucc (.bvar 0)))
        (.lam .nat <| .lam .nat <|
          .app (.app value' (.bvar 1)) (.bvar 0)) := by
  apply checkPrimitiveDef.WF_of_core (by simp)
  simp only [checkPrimitiveDefCore, hname, checkNatBEqPrimitive]
  refine getEnv.WF.bind ?_
  intro _ _ _ ⟨rfl, rfl⟩
  by_cases hdeps : (c.env.contains ``Nat && c.env.contains ``Bool &&
      v.levelParams.isEmpty) = true
  · rw [if_pos hdeps]
    have hdeps' : (c.env.contains ``Nat = true ∧
        c.env.contains ``Bool = true) ∧ v.levelParams = [] := by
      simpa using hdeps
    have hlevels : v.levelParams = [] := hdeps'.2
    have hnat : c.venv.contains ``Nat :=
      VContext.contains_safe_primitive c hdeps'.1.1 (by
        simp [Lean.Kernel.Environment.primitives,
          NameSet.contains, NameSet.ofList])
    have hbool : c.venv.contains ``Bool :=
      VContext.contains_safe_primitive c hdeps'.1.2 (by
        simp [Lean.Kernel.Environment.primitives,
          NameSet.contains, NameSet.ofList])
    have hvalue0 := hvalue
    change TrExprS c.venv c.lparams c.vlctx v.value value' at hvalue0
    rw [hvlctx] at hvalue0
    have hvalueT0 := hvalueT
    change c.venv.HasType c.lparams.length c.vlctx.toCtx value' ty' at hvalueT0
    rw [hvlctx] at hvalueT0
    exact (checkNatBinaryBoolTyped.WF hlevels hnat hbool hvlctx hty
        hvalue0 hvalueT0
        (TrExprS.boolTrue c.hasPrimitives hbool).1
        (TrExprS.boolFalse c.hasPrimitives hbool).1
        (TrExprS.boolFalse c.hasPrimitives hbool).1).bind
      fun _ _ _ h => .pure fun _ => h
  · rw [if_neg hdeps]
    exact .throw

/-- Exact typed certificate for the public `Nat.ble` recognizer branch. -/
theorem checkPrimitiveDef.natBLE.WF_typed {c : VContext} {s : VState}
    (hname : v.name = ``Nat.ble)
    (hvlctx : c.vlctx = [])
    (hty : c.TrExprS v.type ty')
    (hvalue : c.TrExprS v.value value')
    (hvalueT : c.HasType value' ty') :
    M.WF c s (checkPrimitiveDef v) fun b _ => b →
      v.levelParams = [] ∧
      c.venv.contains ``Nat ∧ c.venv.contains ``Bool ∧
      c.venv.IsDefEqU c.lparams.length [] ty'
        (.forallE .nat <| .forallE .nat .bool) ∧
      c.venv.IsDefEqU c.lparams.length []
        (.app (.app value' .natZero) .natZero) .boolTrue ∧
      c.venv.IsDefEqU c.lparams.length []
        (.lam .nat <| .app (.app value' .natZero)
          (.app .natSucc (.bvar 0))) (.lam .nat .boolTrue) ∧
      c.venv.IsDefEqU c.lparams.length []
        (.lam .nat <| .app (.app value' (.app .natSucc (.bvar 0)))
          .natZero) (.lam .nat .boolFalse) ∧
      c.venv.IsDefEqU c.lparams.length []
        (.lam .nat <| .lam .nat <|
          .app (.app value' (.app .natSucc (.bvar 1)))
            (.app .natSucc (.bvar 0)))
        (.lam .nat <| .lam .nat <|
          .app (.app value' (.bvar 1)) (.bvar 0)) := by
  apply checkPrimitiveDef.WF_of_core (by simp)
  simp only [checkPrimitiveDefCore, hname, checkNatBLEPrimitive]
  refine getEnv.WF.bind ?_
  intro _ _ _ ⟨rfl, rfl⟩
  by_cases hdeps : (c.env.contains ``Nat && c.env.contains ``Bool &&
      v.levelParams.isEmpty) = true
  · rw [if_pos hdeps]
    have hdeps' : (c.env.contains ``Nat = true ∧
        c.env.contains ``Bool = true) ∧ v.levelParams = [] := by
      simpa using hdeps
    have hlevels : v.levelParams = [] := hdeps'.2
    have hnat : c.venv.contains ``Nat :=
      VContext.contains_safe_primitive c hdeps'.1.1 (by
        simp [Lean.Kernel.Environment.primitives,
          NameSet.contains, NameSet.ofList])
    have hbool : c.venv.contains ``Bool :=
      VContext.contains_safe_primitive c hdeps'.1.2 (by
        simp [Lean.Kernel.Environment.primitives,
          NameSet.contains, NameSet.ofList])
    have hvalue0 := hvalue
    change TrExprS c.venv c.lparams c.vlctx v.value value' at hvalue0
    rw [hvlctx] at hvalue0
    have hvalueT0 := hvalueT
    change c.venv.HasType c.lparams.length c.vlctx.toCtx value' ty' at hvalueT0
    rw [hvlctx] at hvalueT0
    exact (checkNatBinaryBoolTyped.WF hlevels hnat hbool hvlctx hty
        hvalue0 hvalueT0
        (TrExprS.boolTrue c.hasPrimitives hbool).1
        (TrExprS.boolTrue c.hasPrimitives hbool).1
        (TrExprS.boolFalse c.hasPrimitives hbool).1).bind
      fun _ _ _ h => .pure fun _ => h
  · rw [if_neg hdeps]
    exact .throw

end Environment

/-! ## Semantic conservation for elementary Nat primitives -/

/-- Adding a definitional equality preserves an existing unary Nat
reflection. -/
theorem VEnv.ReflectsNatNat.addDefEq {env : VEnv} {df : VDefEq}
    (h : env.ReflectsNatNat fc f) :
    (env.addDefEq df).ReflectsNatNat fc f := by
  intro hfc
  obtain ⟨htype, heval⟩ := h hfc
  exact ⟨fun U Γ => (htype U Γ).mono VEnv.addDefEq_le,
    fun a => (heval a).mono VEnv.addDefEq_le⟩

/-- Adding an unrelated definitional equality preserves an existing binary
Nat reflection. -/
theorem VEnv.ReflectsNatNatNat.addDefEq {env : VEnv} {df : VDefEq}
    (h : env.ReflectsNatNatNat fc f) :
    (env.addDefEq df).ReflectsNatNatNat fc f := by
  intro hfc
  obtain ⟨htype, heval⟩ := h hfc
  exact ⟨fun U Γ => (htype U Γ).mono VEnv.addDefEq_le,
    fun a b => (heval a b).mono VEnv.addDefEq_le⟩

/-- Adding an unrelated definitional equality preserves an existing
Nat-to-Bool reflection. -/
theorem VEnv.ReflectsNatNatBool.addDefEq {env : VEnv} {df : VDefEq}
    (h : env.ReflectsNatNatBool fc f) :
    (env.addDefEq df).ReflectsNatNatBool fc f := by
  intro hfc
  obtain ⟨htype, heval⟩ := h hfc
  exact ⟨fun U Γ => (htype U Γ).mono VEnv.addDefEq_le,
    fun a b => (heval a b).mono VEnv.addDefEq_le⟩

/-- Adding a fresh, differently named constant preserves an existing binary
Nat reflection. -/
theorem VEnv.ReflectsNatNatNat.addConst {env env' : VEnv}
    (h : env.ReflectsNatNatNat fc f)
    (hadd : env.addConst n ci = some env') (hne : n ≠ fc) :
    env'.ReflectsNatNatNat fc f := by
  intro hfc
  obtain ⟨fcCi, hfcLookup⟩ := hfc
  have hold : env.contains fc := ⟨fcCi, by
    rwa [VEnv.addConst_other hadd hne] at hfcLookup⟩
  obtain ⟨htype, heval⟩ := h hold
  have hle := VEnv.addConst_le hadd
  exact ⟨fun U Γ => (htype U Γ).mono hle,
    fun a b => (heval a b).mono hle⟩

/-- Adding a fresh, differently named constant preserves an existing
Nat-to-Bool reflection. -/
theorem VEnv.ReflectsNatNatBool.addConst {env env' : VEnv}
    (h : env.ReflectsNatNatBool fc f)
    (hadd : env.addConst n ci = some env') (hne : n ≠ fc) :
    env'.ReflectsNatNatBool fc f := by
  intro hfc
  obtain ⟨fcCi, hfcLookup⟩ := hfc
  have hold : env.contains fc := ⟨fcCi, by
    rwa [VEnv.addConst_other hadd hne] at hfcLookup⟩
  obtain ⟨htype, heval⟩ := h hold
  have hle := VEnv.addConst_le hadd
  exact ⟨fun U Γ => (htype U Γ).mono hle,
    fun a b => (heval a b).mono hle⟩

/-- Adding a fresh, differently named constant preserves an existing unary
Nat reflection. -/
theorem VEnv.ReflectsNatNat.addConst {env env' : VEnv}
    (h : env.ReflectsNatNat fc f)
    (hadd : env.addConst n ci = some env') (hne : n ≠ fc) :
    env'.ReflectsNatNat fc f := by
  intro hfc
  obtain ⟨fcCi, hfcLookup⟩ := hfc
  have hold : env.contains fc := ⟨fcCi, by
    rwa [VEnv.addConst_other hadd hne] at hfcLookup⟩
  obtain ⟨htype, heval⟩ := h hold
  have hle := VEnv.addConst_le hadd
  exact ⟨fun U Γ => (htype U Γ).mono hle,
    fun a => (heval a).mono hle⟩

/-- A closed, level-free constant whose declared type is definitionally equal
to `A` can be used at type `A` in every universe and local context. -/
theorem VEnv.HasType.const_of_type_defeq (henv : VEnv.WF env)
    (hci : env.constants n = some ci) (hu : ci.uvars = 0)
    (hty : env.IsDefEqU 0 [] ci.type A) :
    ∀ U Γ, env.HasType U Γ (.const n []) A := by
  intro U Γ
  obtain ⟨B, hty⟩ := hty
  have htyU := (show env.IsDefEqU 0 [] ci.type A from ⟨B, hty⟩).instL
    (ls := []) (U' := U) nofun
  have hlevels := hty.levelWF trivial
  rw [show [] = VLevel.params 0 by rfl, hlevels.1.instL_id,
    hlevels.2.1.instL_id] at htyU
  have hc := HasType.const (U := U) (Γ := []) (ls := []) hci (by simp)
    (by simpa using hu.symm)
  rw [show [] = VLevel.params 0 by rfl, hlevels.1.instL_id] at hc
  exact (HasType.defeqU_r henv trivial htyU hc).weak0 henv

/-- Congruence in the function position, packaged without exposing the result
type witness. -/
theorem VEnv.IsDefEqU.app_same (henv : VEnv.WF env)
    (hΓ : OnCtx Γ (env.IsType U))
    (hf : env.IsDefEqU U Γ f g)
    (hft : env.HasType U Γ f (.forallE A B))
    (ha : env.HasType U Γ a A) :
    env.IsDefEqU U Γ (.app f a) (.app g a) :=
  ⟨_, .appDF (hf.of_l henv hΓ hft) ha⟩

/-- Congruence in the argument position, packaged without exposing the result
type witness. -/
theorem VEnv.IsDefEqU.app_arg (henv : VEnv.WF env)
    (hΓ : OnCtx Γ (env.IsType U))
    (ha : env.IsDefEqU U Γ a b)
    (hf : env.HasType U Γ f (.forallE A B))
    (hat : env.HasType U Γ a A) :
    env.IsDefEqU U Γ (.app f a) (.app f b) :=
  ⟨_, .appDF hf (ha.of_l henv hΓ hat)⟩

/-- Instantiate a definitional equality between lambdas at a typed argument. -/
theorem VEnv.IsDefEqU.lam_inst (henv : VEnv.WF env)
    (hΓ : OnCtx Γ (env.IsType U))
    (h : env.IsDefEqU U Γ (.lam A e₁) (.lam A e₂))
    (hA : env.HasType U Γ A (.sort u))
    (h₁ : env.HasType U (A :: Γ) e₁ B)
    (h₂ : env.HasType U (A :: Γ) e₂ B)
    (ha : env.HasType U Γ a A) :
    env.IsDefEqU U Γ (e₁.inst a) (e₂.inst a) := by
  have happ : env.IsDefEq U Γ (.app (.lam A e₁) a)
      (.app (.lam A e₂) a) (B.inst a) :=
    .appDF (h.of_l henv hΓ (.lam hA h₁)) ha
  exact ⟨_, (VEnv.IsDefEq.beta h₁ ha).symm.trans
    (happ.trans (VEnv.IsDefEq.beta h₂ ha))⟩

/-- The newly registered definition equation relates a level-free constant to
its checked body. -/
theorem VDefVal.const_defeq_value {env : VEnv} {v : VDefVal}
    (henv : (env.addDefEq v.toDefEq).WF) (hu : v.uvars = 0) :
    (env.addDefEq v.toDefEq).IsDefEqU 0 [] (.const v.name []) v.value := by
  have hwf := henv.ordered.defEqWF VEnv.addDefEq_self
  have h := VEnv.IsDefEq.extra0 VEnv.addDefEq_self hwf
  simpa [VDefVal.toDefEq, hu, VLevel.params] using h.toU

private theorem VEnv.natLit_hasType {env : VEnv}
    (hzeroT : ∀ Γ, env.HasType 0 Γ .natZero .nat)
    (hsuccT : ∀ Γ, env.HasType 0 Γ .natSucc (.forallE .nat .nat))
    (n : Nat) (Γ : List VExpr) : env.HasType 0 Γ (.natLit n) .nat := by
  induction n with
  | zero => exact hzeroT Γ
  | succ n ih => exact .app (hsuccT Γ) ih

/-- Turn the checked zero and successor equations for `Nat.pred` into unary
literal reflection. -/
theorem VEnv.ReflectsNatNat.of_pred_equations (henv : VEnv.WF env)
    (hzeroT : ∀ Γ, env.HasType 0 Γ .natZero .nat)
    (hsuccT : ∀ Γ, env.HasType 0 Γ .natSucc (.forallE .nat .nat))
    (hf : ∀ U Γ, env.HasType U Γ (.const ``Nat.pred [])
      (.forallE .nat .nat))
    (hcf : env.IsDefEqU 0 [] (.const ``Nat.pred []) f)
    (hz : env.IsDefEqU 0 [] (.app f .natZero) .natZero)
    (hs : env.IsDefEqU 0 []
      (.lam .nat <| .app f (.app .natSucc (.bvar 0)))
      (.lam .nat <| .bvar 0)) :
    env.ReflectsNatNat ``Nat.pred Nat.pred := by
  intro _
  refine ⟨hf, fun a => ?_⟩
  have ⟨_, hNatSort⟩ := (hzeroT []).isType henv trivial
  have hlit := VEnv.natLit_hasType hzeroT hsuccT
  have hfClosed : f.ClosedN := by
    let ⟨_, hcf⟩ := hcf
    exact (hcf.closedN' henv.ordered.closed trivial).2.1
  have hfv₁ : env.HasType 0 [.nat] f (.forallE .nat .nat) :=
    (hf 0 [.nat]).defeqU_l henv ⟨trivial, ⟨_, hNatSort⟩⟩
      (hcf.weak0 henv)
  have hbody₁ : env.HasType 0 [.nat]
      (.app f (.app .natSucc (.bvar 0))) .nat :=
    .app hfv₁ (.app (hsuccT _) (.bvar .zero))
  have hbody₂ : env.HasType 0 [.nat] (.bvar 0) .nat := .bvar .zero
  cases a with
  | zero =>
    have hcf0 := hcf.app_same henv trivial (hf 0 []) (hzeroT [])
    exact hcf0.trans henv trivial hz
  | succ a =>
    have hcfSucc := hcf.app_same henv trivial (hf 0 [])
      (.app (hsuccT []) (hlit a []))
    have hs' := hs.lam_inst henv trivial hNatSort hbody₁ hbody₂ (hlit a [])
    simp [VExpr.inst, VExpr.natSucc, hfClosed.instN_eq] at hs'
    exact hcfSucc.trans henv trivial hs'

/-- Replace the vacuous/old `Nat.pred` reflection field after inserting a
checked `Nat.pred` definition, while transporting every unrelated primitive
fact through the extension. -/
theorem VEnv.HasPrimitives.addNatPred {env env' : VEnv}
    (h : env.HasPrimitives)
    (hadd : env.addConst ``Nat.pred ci = some env')
    (href : (env'.addDefEq df).ReflectsNatNat ``Nat.pred Nat.pred) :
    (env'.addDefEq df).HasPrimitives := by
  let env'' := env'.addDefEq df
  have le : env ≤ env'' := (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
  have same (p : Name) (hne : ``Nat.pred ≠ p) :
      env''.constants p = env.constants p := by
    change env'.constants p = env.constants p
    exact VEnv.addConst_other hadd hne
  have oldContains {p : Name} (hne : ``Nat.pred ≠ p)
      (H : env''.contains p) : env.contains p := by
    obtain ⟨pci, hpci⟩ := H
    exact ⟨pci, by rwa [same p hne] at hpci⟩
  have newContains {p : Name} (H : env.contains p) : env''.contains p := by
    obtain ⟨pci, hpci⟩ := H
    exact ⟨pci, le.constants hpci⟩
  exact {
    bool := fun H => by
      obtain ⟨hfalse, htrue⟩ := h.bool (oldContains (by decide) H)
      exact ⟨newContains hfalse, newContains htrue⟩
    boolFalse := fun H => h.boolFalse (by
      change env''.constants ``Bool.false = some _ at H
      rwa [same ``Bool.false (by decide)] at H)
    boolTrue := fun H => h.boolTrue (by
      change env''.constants ``Bool.true = some _ at H
      rwa [same ``Bool.true (by decide)] at H)
    nat := fun H => by
      obtain ⟨hzero, hsucc⟩ := h.nat (oldContains (by decide) H)
      exact ⟨newContains hzero, newContains hsucc⟩
    natZero := fun H => h.natZero (by
      change env''.constants ``Nat.zero = some _ at H
      rwa [same ``Nat.zero (by decide)] at H)
    natSucc := fun H => h.natSucc (by
      change env''.constants ``Nat.succ = some _ at H
      rwa [same ``Nat.succ (by decide)] at H)
    natPred := href
    natAdd := (h.natAdd.addConst hadd (by decide)).addDefEq
    natSub := (h.natSub.addConst hadd (by decide)).addDefEq
    natMul := (h.natMul.addConst hadd (by decide)).addDefEq
    natPow := (h.natPow.addConst hadd (by decide)).addDefEq
    natGcd := (h.natGcd.addConst hadd (by decide)).addDefEq
    natMod := (h.natMod.addConst hadd (by decide)).addDefEq
    natDiv := (h.natDiv.addConst hadd (by decide)).addDefEq
    natBEq := (h.natBEq.addConst hadd (by decide)).addDefEq
    natBLE := (h.natBLE.addConst hadd (by decide)).addDefEq
    natLAnd := (h.natLAnd.addConst hadd (by decide)).addDefEq
    natLOr := (h.natLOr.addConst hadd (by decide)).addDefEq
    natXor := (h.natXor.addConst hadd (by decide)).addDefEq
    natShiftLeft := (h.natShiftLeft.addConst hadd (by decide)).addDefEq
    natShiftRight := (h.natShiftRight.addConst hadd (by decide)).addDefEq
    charOfNat := fun H => h.charOfNat (by
      change env''.constants ``Char.ofNat = some _ at H
      rwa [same ``Char.ofNat (by decide)] at H)
    stringOfList := fun H => by
      change env''.constants ``String.ofList = some _ at H
      rw [same ``String.ofList (by decide)] at H
      obtain ⟨hshape, hnil, hcons⟩ := h.stringOfList H
      exact ⟨hshape, hnil.mono le, hcons.mono le⟩ }

/-- Common bookkeeping needed to turn the checked Nat.pred equations for a
fresh definition into an updated primitive-reflection contract. -/
theorem VEnv.HasPrimitives.natPredDefKit {env env' : VEnv} {v : VDefVal}
    (h : env.HasPrimitives) (hnat : env.contains ``Nat)
    (hname : v.name = ``Nat.pred)
    (hadd : env.addConst ``Nat.pred v.toVConstant = some env')
    (hwf : (env'.addDefEq v.toDefEq).WF)
    (hu : v.uvars = 0)
    (hty : env.IsDefEqU 0 [] v.type (.forallE .nat .nat))
    (hnext :
      env ≤ env'.addDefEq v.toDefEq →
      (∀ U Γ, (env'.addDefEq v.toDefEq).HasType U Γ
        (.const ``Nat.pred []) (.forallE .nat .nat)) →
      (env'.addDefEq v.toDefEq).IsDefEqU 0 []
        (.const ``Nat.pred []) v.value →
      (∀ Γ, (env'.addDefEq v.toDefEq).HasType 0 Γ .natZero .nat) →
      (∀ Γ, (env'.addDefEq v.toDefEq).HasType 0 Γ .natSucc
        (.forallE .nat .nat)) →
      (env'.addDefEq v.toDefEq).HasPrimitives) :
    (env'.addDefEq v.toDefEq).HasPrimitives := by
  let env'' := env'.addDefEq v.toDefEq
  have le : env ≤ env'' := (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
  have hf (U Γ) : env''.HasType U Γ (.const ``Nat.pred [])
      (.forallE .nat .nat) :=
    VEnv.HasType.const_of_type_defeq hwf (by
      change env'.constants ``Nat.pred = some v.toVConstant
      exact VEnv.addConst_self hadd) hu (hty.mono le) U Γ
  have hcf := VDefVal.const_defeq_value hwf hu
  rw [hname] at hcf
  have hzero (Γ) : env''.HasType 0 Γ .natZero .nat :=
    (TrExprS.natZero h hnat (Us := []) (Δ := [])).2.mono le |>.weak0 hwf
  have hsucc (Γ) : env''.HasType 0 Γ .natSucc (.forallE .nat .nat) :=
    (TrExprS.natSucc h hnat (Us := []) (Δ := [])).2.mono le |>.weak0 hwf
  exact hnext le hf hcf hzero hsucc

/-- A checked, well-typed Nat.pred definition with the two canonical
equations preserves `HasPrimitives` after installing its declaration equation. -/
theorem VEnv.HasPrimitives.addNatPredDef {env env' : VEnv} {v : VDefVal}
    (h : env.HasPrimitives) (hnat : env.contains ``Nat)
    (hname : v.name = ``Nat.pred)
    (hadd : env.addConst ``Nat.pred v.toVConstant = some env')
    (hwf : (env'.addDefEq v.toDefEq).WF)
    (hu : v.uvars = 0)
    (hty : env.IsDefEqU 0 [] v.type (.forallE .nat .nat))
    (hz : env.IsDefEqU 0 [] (.app v.value .natZero) .natZero)
    (hs : env.IsDefEqU 0 []
      (.lam .nat <| .app v.value (.app .natSucc (.bvar 0)))
      (.lam .nat <| .bvar 0)) :
    (env'.addDefEq v.toDefEq).HasPrimitives := by
  refine h.natPredDefKit hnat hname hadd hwf hu hty ?_
  intro le hf hcf hzero hsucc
  have href := VEnv.ReflectsNatNat.of_pred_equations hwf hzero hsucc hf hcf
    (hz.mono le) (hs.mono le)
  exact h.addNatPred hadd href

/-- Turn the checked zero and successor equations for a binary Nat function
into literal reflection when the successor step applies a typed unary
operation. -/
theorem VEnv.ReflectsNatNatNat.of_unary_step_equations (henv : VEnv.WF env)
    {n : Name} {F : Nat → Nat → Nat} {u : VExpr} (U : Nat → Nat)
    (hzeroT : ∀ Γ, env.HasType 0 Γ .natZero .nat)
    (hsuccT : ∀ Γ, env.HasType 0 Γ .natSucc (.forallE .nat .nat))
    (huT : ∀ Γ, env.HasType 0 Γ u (.forallE .nat .nat))
    (huClosed : u.ClosedN)
    (huEval : ∀ k, env.IsDefEqU 0 [] (.app u (.natLit k)) (.natLit (U k)))
    (hF0 : ∀ a, F a 0 = a)
    (hFs : ∀ a b, F a (b + 1) = U (F a b))
    (hf : ∀ k Γ, env.HasType k Γ (.const n [])
      (.forallE .nat <| .forallE .nat .nat))
    (hcf : env.IsDefEqU 0 [] (.const n []) f)
    (hz : env.IsDefEqU 0 []
      (.lam .nat <| .app (.app f (.bvar 0)) .natZero)
      (.lam .nat <| .bvar 0))
    (hs : env.IsDefEqU 0 []
      (.lam .nat <| .lam .nat <|
        .app (.app f (.bvar 1)) (.app .natSucc (.bvar 0)))
      (.lam .nat <| .lam .nat <|
        .app u (.app (.app f (.bvar 1)) (.bvar 0)))) :
    env.ReflectsNatNatNat n F := by
  intro _
  refine ⟨hf, fun a b => ?_⟩
  have ⟨_, hNatSort⟩ := (hzeroT []).isType henv trivial
  have hctx₁ : OnCtx [.nat] (env.IsType 0) :=
    ⟨trivial, ⟨_, hNatSort⟩⟩
  have hctx₂ : OnCtx [.nat, .nat] (env.IsType 0) :=
    ⟨hctx₁, ⟨_, hNatSort.weak0 henv⟩⟩
  have hlit := VEnv.natLit_hasType hzeroT hsuccT
  have hfv (Γ) (hΓ : OnCtx Γ (env.IsType 0)) :
      env.HasType 0 Γ f (.forallE .nat <| .forallE .nat .nat) :=
    (hf 0 Γ).defeqU_l henv hΓ (hcf.weak0 henv)
  have hfClosed : f.ClosedN := by
    let ⟨_, hcf⟩ := hcf
    exact (hcf.closedN' henv.ordered.closed trivial).2.1
  have hcfApp (a b) : env.IsDefEqU 0 []
      (.app (.app (.const n []) (.natLit a)) (.natLit b))
      (.app (.app f (.natLit a)) (.natLit b)) := by
    have h₁ := hcf.app_same henv trivial (hf 0 []) (hlit a [])
    exact h₁.app_same henv trivial (.app (hf 0 []) (hlit a [])) (hlit b [])
  induction b with
  | zero =>
    rw [hF0]
    have hbody₁ : env.HasType 0 [.nat]
        (.app (.app f (.bvar 0)) .natZero) .nat :=
      .app (.app (hfv _ hctx₁) (.bvar .zero)) (hzeroT _)
    have hbody₂ : env.HasType 0 [.nat] (.bvar 0) .nat := .bvar .zero
    have hz' := hz.lam_inst henv trivial hNatSort hbody₁ hbody₂ (hlit a [])
    simp [VExpr.inst, hfClosed.instN_eq] at hz'
    simpa [VExpr.inst, VExpr.natLit] using
      (hcfApp a 0).trans henv trivial hz'
  | succ b ih =>
    rw [hFs]
    have hbvar0 : env.HasType 0 [.nat, .nat] (.bvar 0) .nat := .bvar .zero
    have hbvar1 : env.HasType 0 [.nat, .nat] (.bvar 1) .nat :=
      .bvar (.succ .zero)
    have hleft : env.HasType 0 [.nat, .nat]
        (.app (.app f (.bvar 1)) (.app .natSucc (.bvar 0))) .nat :=
      .app (.app (hfv _ hctx₂) hbvar1) (.app (hsuccT _) hbvar0)
    have hright : env.HasType 0 [.nat, .nat]
        (.app u (.app (.app f (.bvar 1)) (.bvar 0))) .nat :=
      .app (huT _) (.app (.app (hfv _ hctx₂) hbvar1) hbvar0)
    have hinner₁ : env.HasType 0 [.nat]
        (.lam .nat <| .app (.app f (.bvar 1)) (.app .natSucc (.bvar 0)))
        (.forallE .nat .nat) := .lam (hNatSort.weak0 henv) hleft
    have hinner₂ : env.HasType 0 [.nat]
        (.lam .nat <| .app u (.app (.app f (.bvar 1)) (.bvar 0)))
        (.forallE .nat .nat) := .lam (hNatSort.weak0 henv) hright
    have houter := hs.lam_inst henv trivial hNatSort hinner₁ hinner₂
      (hlit a [])
    have hstep := houter.lam_inst henv trivial hNatSort
      (by simpa [VExpr.inst] using hleft.instN henv (.succ .zero) (hlit a []))
      (by simpa [VExpr.inst] using hright.instN henv (.succ .zero) (hlit a []))
      (hlit b [])
    simp [VExpr.inst, VExpr.natSucc, hfClosed.instN_eq,
      huClosed.instN_eq] at hstep
    have hback := (hcfApp a b).symm.app_arg henv trivial (huT [])
      (.app (.app (hfv [] trivial) (hlit a [])) (hlit b []))
    have hcongr := ih.app_arg henv trivial (huT [])
      (.app (.app (hf 0 []) (hlit a [])) (hlit b []))
    exact (hcfApp a (b + 1)).trans henv trivial <| hstep.trans henv trivial <|
      hback.trans henv trivial <| hcongr.trans henv trivial (huEval (F a b))

/-- Turn checked binary recurrence equations into literal reflection when the
successor step applies another reflected binary Nat operation to the recursive
call and the first argument. This is shared by `Nat.mul` and `Nat.pow`. -/
theorem VEnv.ReflectsNatNatNat.of_binop_step_equations (henv : VEnv.WF env)
    {n : Name} {F : Nat → Nat → Nat} {g : Name} {G : Nat → Nat → Nat}
    (z : Nat)
    (hzeroT : ∀ Γ, env.HasType 0 Γ .natZero .nat)
    (hsuccT : ∀ Γ, env.HasType 0 Γ .natSucc (.forallE .nat .nat))
    (hg : env.ReflectsNatNatNat g G) (hgC : env.contains g)
    (hF0 : ∀ a, F a 0 = z)
    (hFs : ∀ a b, F a (b + 1) = G (F a b) a)
    (hf : ∀ k Γ, env.HasType k Γ (.const n [])
      (.forallE .nat <| .forallE .nat .nat))
    (hcf : env.IsDefEqU 0 [] (.const n []) f)
    (hz : env.IsDefEqU 0 []
      (.lam .nat <| .app (.app f (.bvar 0)) .natZero)
      (.lam .nat <| .natLit z))
    (hs : env.IsDefEqU 0 []
      (.lam .nat <| .lam .nat <|
        .app (.app f (.bvar 1)) (.app .natSucc (.bvar 0)))
      (.lam .nat <| .lam .nat <|
        .app (.app (.const g [])
          (.app (.app f (.bvar 1)) (.bvar 0))) (.bvar 1))) :
    env.ReflectsNatNatNat n F := by
  intro _
  refine ⟨hf, fun a b => ?_⟩
  obtain ⟨hgT, hgEval⟩ := hg hgC
  have ⟨_, hNatSort⟩ := (hzeroT []).isType henv trivial
  have hctx₁ : OnCtx [.nat] (env.IsType 0) :=
    ⟨trivial, ⟨_, hNatSort⟩⟩
  have hctx₂ : OnCtx [.nat, .nat] (env.IsType 0) :=
    ⟨hctx₁, ⟨_, hNatSort.weak0 henv⟩⟩
  have hlit := VEnv.natLit_hasType hzeroT hsuccT
  have hfv (Γ) (hΓ : OnCtx Γ (env.IsType 0)) :
      env.HasType 0 Γ f (.forallE .nat <| .forallE .nat .nat) :=
    (hf 0 Γ).defeqU_l henv hΓ (hcf.weak0 henv)
  have hfClosed : f.ClosedN := by
    let ⟨_, hcf⟩ := hcf
    exact (hcf.closedN' henv.ordered.closed trivial).2.1
  have hcfApp (a b) : env.IsDefEqU 0 []
      (.app (.app (.const n []) (.natLit a)) (.natLit b))
      (.app (.app f (.natLit a)) (.natLit b)) := by
    have h₁ := hcf.app_same henv trivial (hf 0 []) (hlit a [])
    exact h₁.app_same henv trivial (.app (hf 0 []) (hlit a [])) (hlit b [])
  induction b with
  | zero =>
    rw [hF0]
    have hbody₁ : env.HasType 0 [.nat]
        (.app (.app f (.bvar 0)) .natZero) .nat :=
      .app (.app (hfv _ hctx₁) (.bvar .zero)) (hzeroT _)
    have hz' := hz.lam_inst henv trivial hNatSort hbody₁ (hlit z _)
      (hlit a [])
    simp [VExpr.inst, hfClosed.instN_eq] at hz'
    exact (hcfApp a 0).trans henv trivial hz'
  | succ b ih =>
    rw [hFs]
    have hbvar0 : env.HasType 0 [.nat, .nat] (.bvar 0) .nat := .bvar .zero
    have hbvar1 : env.HasType 0 [.nat, .nat] (.bvar 1) .nat :=
      .bvar (.succ .zero)
    have hfbody : env.HasType 0 [.nat, .nat]
        (.app (.app f (.bvar 1)) (.bvar 0)) .nat :=
      .app (.app (hfv _ hctx₂) hbvar1) hbvar0
    have hleft : env.HasType 0 [.nat, .nat]
        (.app (.app f (.bvar 1)) (.app .natSucc (.bvar 0))) .nat :=
      .app (.app (hfv _ hctx₂) hbvar1) (.app (hsuccT _) hbvar0)
    have hright : env.HasType 0 [.nat, .nat]
        (.app (.app (.const g [])
          (.app (.app f (.bvar 1)) (.bvar 0))) (.bvar 1)) .nat :=
      .app (.app (hgT 0 _) hfbody) hbvar1
    have hinner₁ : env.HasType 0 [.nat]
        (.lam .nat <| .app (.app f (.bvar 1)) (.app .natSucc (.bvar 0)))
        (.forallE .nat .nat) := .lam (hNatSort.weak0 henv) hleft
    have hinner₂ : env.HasType 0 [.nat]
        (.lam .nat <| .app (.app (.const g [])
          (.app (.app f (.bvar 1)) (.bvar 0))) (.bvar 1))
        (.forallE .nat .nat) := .lam (hNatSort.weak0 henv) hright
    have houter := hs.lam_inst henv trivial hNatSort hinner₁ hinner₂
      (hlit a [])
    have hstep := houter.lam_inst henv trivial hNatSort
      (by simpa [VExpr.inst] using hleft.instN henv (.succ .zero) (hlit a []))
      (by simpa [VExpr.inst] using hright.instN henv (.succ .zero) (hlit a []))
      (hlit b [])
    simp [VExpr.inst, VExpr.natSucc, hfClosed.instN_eq]
      at hstep
    have hback₁ := (hcfApp a b).symm.app_arg henv trivial (hgT 0 [])
      (.app (.app (hfv [] trivial) (hlit a [])) (hlit b []))
    have hback := hback₁.app_same henv trivial
      (.app (hgT 0 []) (.app (.app (hfv [] trivial) (hlit a []))
        (hlit b [])))
      (hlit a [])
    have hcongr₁ := ih.app_arg henv trivial (hgT 0 [])
      (.app (.app (hf 0 []) (hlit a [])) (hlit b []))
    have hcongr := hcongr₁.app_same henv trivial
      (.app (hgT 0 []) (.app (.app (hf 0 []) (hlit a [])) (hlit b [])))
      (hlit a [])
    exact (hcfApp a (b + 1)).trans henv trivial <|
      hstep.trans henv trivial <| hback.trans henv trivial <|
      hcongr.trans henv trivial (hgEval (F a b) a)

/-- The concrete recurrence certificate used for `Nat.add`. -/
theorem VEnv.ReflectsNatNatNat.of_add_equations (henv : VEnv.WF env)
    (hzeroT : ∀ Γ, env.HasType 0 Γ .natZero .nat)
    (hsuccT : ∀ Γ, env.HasType 0 Γ .natSucc (.forallE .nat .nat))
    (hf : ∀ U Γ, env.HasType U Γ (.const ``Nat.add [])
      (.forallE .nat <| .forallE .nat .nat))
    (hcf : env.IsDefEqU 0 [] (.const ``Nat.add []) f)
    (hz : env.IsDefEqU 0 []
      (.lam .nat <| .app (.app f (.bvar 0)) .natZero)
      (.lam .nat <| .bvar 0))
    (hs : env.IsDefEqU 0 []
      (.lam .nat <| .lam .nat <|
        .app (.app f (.bvar 1)) (.app .natSucc (.bvar 0)))
      (.lam .nat <| .lam .nat <|
        .app .natSucc (.app (.app f (.bvar 1)) (.bvar 0)))) :
    env.ReflectsNatNatNat ``Nat.add Nat.add := by
  refine VEnv.ReflectsNatNatNat.of_unary_step_equations henv Nat.succ
    hzeroT hsuccT hsuccT trivial ?_ (fun _ => rfl) (fun _ _ => rfl)
    hf hcf hz hs
  intro k
  exact ⟨_, VEnv.natLit_hasType hzeroT hsuccT (k + 1) []⟩

/-- The concrete recurrence certificate used for `Nat.sub`, consuming the
retained unary reflection for `Nat.pred`. -/
theorem VEnv.ReflectsNatNatNat.of_sub_equations (henv : VEnv.WF env)
    (hzeroT : ∀ Γ, env.HasType 0 Γ .natZero .nat)
    (hsuccT : ∀ Γ, env.HasType 0 Γ .natSucc (.forallE .nat .nat))
    (hpred : env.ReflectsNatNat ``Nat.pred Nat.pred)
    (hpredC : env.contains ``Nat.pred)
    (hf : ∀ U Γ, env.HasType U Γ (.const ``Nat.sub [])
      (.forallE .nat <| .forallE .nat .nat))
    (hcf : env.IsDefEqU 0 [] (.const ``Nat.sub []) f)
    (hz : env.IsDefEqU 0 []
      (.lam .nat <| .app (.app f (.bvar 0)) .natZero)
      (.lam .nat <| .bvar 0))
    (hs : env.IsDefEqU 0 []
      (.lam .nat <| .lam .nat <|
        .app (.app f (.bvar 1)) (.app .natSucc (.bvar 0)))
      (.lam .nat <| .lam .nat <|
        .app (.const ``Nat.pred [])
          (.app (.app f (.bvar 1)) (.bvar 0)))) :
    env.ReflectsNatNatNat ``Nat.sub Nat.sub := by
  obtain ⟨hpredT, hpredEval⟩ := hpred hpredC
  exact VEnv.ReflectsNatNatNat.of_unary_step_equations henv Nat.pred
    hzeroT hsuccT (hpredT 0) trivial hpredEval
    (fun _ => rfl) (fun _ _ => rfl) hf hcf hz hs

/-- The concrete recurrence certificate used for `Nat.mul`, consuming the
retained binary reflection for `Nat.add`. -/
theorem VEnv.ReflectsNatNatNat.of_mul_equations (henv : VEnv.WF env)
    (hzeroT : ∀ Γ, env.HasType 0 Γ .natZero .nat)
    (hsuccT : ∀ Γ, env.HasType 0 Γ .natSucc (.forallE .nat .nat))
    (hadd : env.ReflectsNatNatNat ``Nat.add Nat.add)
    (haddC : env.contains ``Nat.add)
    (hf : ∀ U Γ, env.HasType U Γ (.const ``Nat.mul [])
      (.forallE .nat <| .forallE .nat .nat))
    (hcf : env.IsDefEqU 0 [] (.const ``Nat.mul []) f)
    (hz : env.IsDefEqU 0 []
      (.lam .nat <| .app (.app f (.bvar 0)) .natZero)
      (.lam .nat .natZero))
    (hs : env.IsDefEqU 0 []
      (.lam .nat <| .lam .nat <|
        .app (.app f (.bvar 1)) (.app .natSucc (.bvar 0)))
      (.lam .nat <| .lam .nat <|
        .app (.app (.const ``Nat.add [])
          (.app (.app f (.bvar 1)) (.bvar 0))) (.bvar 1))) :
    env.ReflectsNatNatNat ``Nat.mul Nat.mul := by
  exact VEnv.ReflectsNatNatNat.of_binop_step_equations henv 0
    hzeroT hsuccT hadd haddC (fun _ => rfl) (fun _ _ => rfl)
    hf hcf hz hs

/-- The concrete recurrence certificate used for `Nat.pow`, consuming the
retained binary reflection for `Nat.mul`. -/
theorem VEnv.ReflectsNatNatNat.of_pow_equations (henv : VEnv.WF env)
    (hzeroT : ∀ Γ, env.HasType 0 Γ .natZero .nat)
    (hsuccT : ∀ Γ, env.HasType 0 Γ .natSucc (.forallE .nat .nat))
    (hmul : env.ReflectsNatNatNat ``Nat.mul Nat.mul)
    (hmulC : env.contains ``Nat.mul)
    (hf : ∀ U Γ, env.HasType U Γ (.const ``Nat.pow [])
      (.forallE .nat <| .forallE .nat .nat))
    (hcf : env.IsDefEqU 0 [] (.const ``Nat.pow []) f)
    (hz : env.IsDefEqU 0 []
      (.lam .nat <| .app (.app f (.bvar 0)) .natZero)
      (.lam .nat <| .app .natSucc .natZero))
    (hs : env.IsDefEqU 0 []
      (.lam .nat <| .lam .nat <|
        .app (.app f (.bvar 1)) (.app .natSucc (.bvar 0)))
      (.lam .nat <| .lam .nat <|
        .app (.app (.const ``Nat.mul [])
          (.app (.app f (.bvar 1)) (.bvar 0))) (.bvar 1))) :
    env.ReflectsNatNatNat ``Nat.pow Nat.pow := by
  exact VEnv.ReflectsNatNatNat.of_binop_step_equations henv 1
    hzeroT hsuccT hmul hmulC (fun _ => rfl) (fun _ _ => rfl)
    hf hcf hz hs

/-- The recursive input-transform certificate used for `Nat.shiftLeft`,
consuming the retained typed reflection for `Nat.mul`. -/
theorem VEnv.ReflectsNatNatNat.of_shiftLeft_equations (henv : VEnv.WF env)
    (hzeroT : ∀ Γ, env.HasType 0 Γ .natZero .nat)
    (hsuccT : ∀ Γ, env.HasType 0 Γ .natSucc (.forallE .nat .nat))
    (hmul : env.ReflectsNatNatNat ``Nat.mul Nat.mul)
    (hmulC : env.contains ``Nat.mul)
    (hf : ∀ U Γ, env.HasType U Γ (.const ``Nat.shiftLeft [])
      (.forallE .nat <| .forallE .nat .nat))
    (hcf : env.IsDefEqU 0 [] (.const ``Nat.shiftLeft []) f)
    (hz : env.IsDefEqU 0 []
      (.lam .nat <| .app (.app f (.bvar 0)) .natZero)
      (.lam .nat <| .bvar 0))
    (hs : env.IsDefEqU 0 []
      (.lam .nat <| .lam .nat <|
        .app (.app f (.bvar 0)) (.app .natSucc (.bvar 1)))
      (.lam .nat <| .lam .nat <|
        .app (.app f
          (.app (.app (.const ``Nat.mul []) (.natLit 2)) (.bvar 0)))
          (.bvar 1))) :
    env.ReflectsNatNatNat ``Nat.shiftLeft Nat.shiftLeft := by
  intro _
  refine ⟨hf, fun a b => ?_⟩
  obtain ⟨hmulT, hmulEval⟩ := hmul hmulC
  have ⟨_, hNatSort⟩ := (hzeroT []).isType henv trivial
  have hctx₁ : OnCtx [.nat] (env.IsType 0) :=
    ⟨trivial, ⟨_, hNatSort⟩⟩
  have hctx₂ : OnCtx [.nat, .nat] (env.IsType 0) :=
    ⟨hctx₁, ⟨_, hNatSort.weak0 henv⟩⟩
  have hlit := VEnv.natLit_hasType hzeroT hsuccT
  have hfv (Γ) (hΓ : OnCtx Γ (env.IsType 0)) :
      env.HasType 0 Γ f (.forallE .nat <| .forallE .nat .nat) :=
    (hf 0 Γ).defeqU_l henv hΓ (hcf.weak0 henv)
  have hfClosed : f.ClosedN := by
    let ⟨_, hcf⟩ := hcf
    exact (hcf.closedN' henv.ordered.closed trivial).2.1
  have hcfApp (a b) : env.IsDefEqU 0 []
      (.app (.app (.const ``Nat.shiftLeft []) (.natLit a)) (.natLit b))
      (.app (.app f (.natLit a)) (.natLit b)) := by
    have h₁ := hcf.app_same henv trivial (hf 0 []) (hlit a [])
    exact h₁.app_same henv trivial (.app (hf 0 []) (hlit a [])) (hlit b [])
  induction b generalizing a with
  | zero =>
    have hbody : env.HasType 0 [.nat]
        (.app (.app f (.bvar 0)) .natZero) .nat :=
      .app (.app (hfv _ hctx₁) (.bvar .zero)) (hzeroT _)
    have heq := hz.lam_inst henv trivial hNatSort hbody (.bvar .zero)
      (hlit a [])
    simp [VExpr.inst, hfClosed.instN_eq] at heq
    exact (hcfApp a 0).trans henv trivial heq
  | succ b ih =>
    have hbvar0 : env.HasType 0 [.nat, .nat] (.bvar 0) .nat := .bvar .zero
    have hbvar1 : env.HasType 0 [.nat, .nat] (.bvar 1) .nat :=
      .bvar (.succ .zero)
    have hleft : env.HasType 0 [.nat, .nat]
        (.app (.app f (.bvar 0)) (.app .natSucc (.bvar 1))) .nat :=
      .app (.app (hfv _ hctx₂) hbvar0) (.app (hsuccT _) hbvar1)
    have hmulBody : env.HasType 0 [.nat, .nat]
        (.app (.app (.const ``Nat.mul []) (.natLit 2)) (.bvar 0)) .nat :=
      .app (.app (hmulT 0 _) (hlit 2 _)) hbvar0
    have hright : env.HasType 0 [.nat, .nat]
        (.app (.app f
          (.app (.app (.const ``Nat.mul []) (.natLit 2)) (.bvar 0)))
          (.bvar 1)) .nat :=
      .app (.app (hfv _ hctx₂) hmulBody) hbvar1
    have hinner₁ : env.HasType 0 [.nat]
        (.lam .nat <| .app (.app f (.bvar 0)) (.app .natSucc (.bvar 1)))
        (.forallE .nat .nat) := .lam (hNatSort.weak0 henv) hleft
    have hinner₂ : env.HasType 0 [.nat]
        (.lam .nat <| .app (.app f
          (.app (.app (.const ``Nat.mul []) (.natLit 2)) (.bvar 0)))
          (.bvar 1))
        (.forallE .nat .nat) := .lam (hNatSort.weak0 henv) hright
    have houter := hs.lam_inst henv trivial hNatSort hinner₁ hinner₂
      (hlit b [])
    have hstep := houter.lam_inst henv trivial hNatSort
      (by simpa [VExpr.inst] using hleft.instN henv (.succ .zero) (hlit b []))
      (by simpa [VExpr.inst] using hright.instN henv (.succ .zero) (hlit b []))
      (hlit a [])
    simp [VExpr.inst, VExpr.natSucc, hfClosed.instN_eq]
      at hstep
    have hmulEq := hmulEval 2 a
    have harg := hmulEq.app_arg henv trivial (hfv [] trivial)
      (.app (.app (hmulT 0 []) (hlit 2 [])) (hlit a []))
    have hfa : env.HasType 0 []
        (.app f (.app (.app (.const ``Nat.mul []) (.natLit 2)) (.natLit a)))
        (.forallE .nat .nat) :=
      .app (hfv [] trivial)
        (.app (.app (hmulT 0 []) (hlit 2 [])) (hlit a []))
    have hargs := harg.app_same henv trivial hfa (hlit b [])
    exact (hcfApp a (b + 1)).trans henv trivial <| hstep.trans henv trivial <|
      hargs.trans henv trivial <|
        (hcfApp (2 * a) b).symm.trans henv trivial (ih (a := 2 * a))

/-- The four constructor equations checked for `Nat.beq` and `Nat.ble`
determine a Boolean-valued operation on natural literals. -/
theorem VEnv.ReflectsNatNatBool.of_rec_equations (henv : VEnv.WF env)
    (hzeroT : ∀ Γ, env.HasType 0 Γ .natZero .nat)
    (hsuccT : ∀ Γ, env.HasType 0 Γ .natSucc (.forallE .nat .nat))
    (hboolT : ∀ b Γ, env.HasType 0 Γ (.boolLit b) .bool)
    (hf : ∀ U Γ, env.HasType U Γ (.const fc [])
      (.forallE .nat <| .forallE .nat .bool))
    (hcf : env.IsDefEqU 0 [] (.const fc []) f)
    (h00 : env.IsDefEqU 0 []
      (.app (.app f .natZero) .natZero) (.boolLit r00))
    (h0s : env.IsDefEqU 0 []
      (.lam .nat <| .app (.app f .natZero) (.app .natSucc (.bvar 0)))
      (.lam .nat <| .boolLit r0s))
    (hs0 : env.IsDefEqU 0 []
      (.lam .nat <| .app (.app f (.app .natSucc (.bvar 0))) .natZero)
      (.lam .nat <| .boolLit rs0))
    (hss : env.IsDefEqU 0 []
      (.lam .nat <| .lam .nat <|
        .app (.app f (.app .natSucc (.bvar 1))) (.app .natSucc (.bvar 0)))
      (.lam .nat <| .lam .nat <| .app (.app f (.bvar 1)) (.bvar 0)))
    (hg00 : g 0 0 = r00) (hg0s : ∀ b, g 0 (b + 1) = r0s)
    (hgs0 : ∀ a, g (a + 1) 0 = rs0)
    (hgss : ∀ a b, g (a + 1) (b + 1) = g a b) :
    env.ReflectsNatNatBool fc g := by
  intro _
  refine ⟨hf, fun a b => ?_⟩
  have ⟨_, hNatSort⟩ := (hzeroT []).isType henv trivial
  have hctx₁ : OnCtx [.nat] (env.IsType 0) :=
    ⟨trivial, ⟨_, hNatSort⟩⟩
  have hctx₂ : OnCtx [.nat, .nat] (env.IsType 0) :=
    ⟨hctx₁, ⟨_, hNatSort.weak0 henv⟩⟩
  have hlit := VEnv.natLit_hasType hzeroT hsuccT
  have hfv (Γ) (hΓ : OnCtx Γ (env.IsType 0)) :
      env.HasType 0 Γ f (.forallE .nat <| .forallE .nat .bool) :=
    (hf 0 Γ).defeqU_l henv hΓ (hcf.weak0 henv)
  have hfClosed : f.ClosedN := by
    let ⟨_, hcf⟩ := hcf
    exact (hcf.closedN' henv.ordered.closed trivial).2.1
  have hcfApp (a b) : env.IsDefEqU 0 []
      (.app (.app (.const fc []) (.natLit a)) (.natLit b))
      (.app (.app f (.natLit a)) (.natLit b)) := by
    have h₁ := hcf.app_same henv trivial (hf 0 []) (hlit a [])
    exact h₁.app_same henv trivial (.app (hf 0 []) (hlit a [])) (hlit b [])
  induction a generalizing b with
  | zero =>
    cases b with
    | zero =>
      simpa [hg00] using (hcfApp 0 0).trans henv trivial h00
    | succ b =>
      have hbody : env.HasType 0 [.nat]
          (.app (.app f .natZero) (.app .natSucc (.bvar 0))) .bool :=
        .app (.app (hfv _ hctx₁) (hzeroT _))
          (.app (hsuccT _) (.bvar .zero))
      have heq := h0s.lam_inst henv trivial hNatSort hbody
        (hboolT r0s _) (hlit b [])
      cases r0s <;>
        simp [VExpr.inst, VExpr.natLit, VExpr.natZero, VExpr.natSucc,
          VExpr.boolLit, VExpr.boolFalse, VExpr.boolTrue,
          hfClosed.instN_eq, hg0s] at heq ⊢ <;>
        exact (hcfApp 0 (b + 1)).trans henv trivial heq
  | succ a ih =>
    cases b with
    | zero =>
      have hbody : env.HasType 0 [.nat]
          (.app (.app f (.app .natSucc (.bvar 0))) .natZero) .bool :=
        .app (.app (hfv _ hctx₁) (.app (hsuccT _) (.bvar .zero)))
          (hzeroT _)
      have heq := hs0.lam_inst henv trivial hNatSort hbody
        (hboolT rs0 _) (hlit a [])
      cases rs0 <;>
        simp [VExpr.inst, VExpr.natLit, VExpr.natZero, VExpr.natSucc,
          VExpr.boolLit, VExpr.boolFalse, VExpr.boolTrue,
          hfClosed.instN_eq, hgs0] at heq ⊢ <;>
        exact (hcfApp (a + 1) 0).trans henv trivial heq
    | succ b =>
      have hbvar0 : env.HasType 0 [.nat, .nat] (.bvar 0) .nat := .bvar .zero
      have hbvar1 : env.HasType 0 [.nat, .nat] (.bvar 1) .nat :=
        .bvar (.succ .zero)
      have hleft : env.HasType 0 [.nat, .nat]
          (.app (.app f (.app .natSucc (.bvar 1)))
            (.app .natSucc (.bvar 0))) .bool :=
        .app (.app (hfv _ hctx₂) (.app (hsuccT _) hbvar1))
          (.app (hsuccT _) hbvar0)
      have hright : env.HasType 0 [.nat, .nat]
          (.app (.app f (.bvar 1)) (.bvar 0)) .bool :=
        .app (.app (hfv _ hctx₂) hbvar1) hbvar0
      have hinner₁ : env.HasType 0 [.nat]
          (.lam .nat <| .app (.app f (.app .natSucc (.bvar 1)))
            (.app .natSucc (.bvar 0))) (.forallE .nat .bool) :=
        .lam (hNatSort.weak0 henv) hleft
      have hinner₂ : env.HasType 0 [.nat]
          (.lam .nat <| .app (.app f (.bvar 1)) (.bvar 0))
          (.forallE .nat .bool) := .lam (hNatSort.weak0 henv) hright
      have houter := hss.lam_inst henv trivial hNatSort hinner₁ hinner₂
        (hlit a [])
      have heq := houter.lam_inst henv trivial hNatSort
        (by simpa [VExpr.inst] using
          hleft.instN henv (.succ .zero) (hlit a []))
        (by simpa [VExpr.inst] using
          hright.instN henv (.succ .zero) (hlit a []))
        (hlit b [])
      simp [VExpr.inst, VExpr.natSucc, hfClosed.instN_eq] at heq
      rw [hgss]
      exact (hcfApp (a + 1) (b + 1)).trans henv trivial <|
        heq.trans henv trivial <|
        (hcfApp a b).symm.trans henv trivial (ih b)

/-- Replace the vacuous/old `Nat.add` reflection field after inserting a
checked `Nat.add` definition, while transporting every unrelated primitive
fact through the extension. -/
theorem VEnv.HasPrimitives.addNatAdd {env env' : VEnv}
    (h : env.HasPrimitives)
    (hadd : env.addConst ``Nat.add ci = some env')
    (href : (env'.addDefEq df).ReflectsNatNatNat ``Nat.add Nat.add) :
    (env'.addDefEq df).HasPrimitives := by
  let env'' := env'.addDefEq df
  have le : env ≤ env'' := (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
  have same (p : Name) (hne : ``Nat.add ≠ p) :
      env''.constants p = env.constants p := by
    change env'.constants p = env.constants p
    exact VEnv.addConst_other hadd hne
  have oldContains {p : Name} (hne : ``Nat.add ≠ p)
      (H : env''.contains p) : env.contains p := by
    obtain ⟨pci, hpci⟩ := H
    exact ⟨pci, by rwa [same p hne] at hpci⟩
  have newContains {p : Name} (H : env.contains p) : env''.contains p := by
    obtain ⟨pci, hpci⟩ := H
    exact ⟨pci, le.constants hpci⟩
  exact {
    bool := fun H => by
      obtain ⟨hfalse, htrue⟩ := h.bool (oldContains (by decide) H)
      exact ⟨newContains hfalse, newContains htrue⟩
    boolFalse := fun H => h.boolFalse (by
      change env''.constants ``Bool.false = some _ at H
      rwa [same ``Bool.false (by decide)] at H)
    boolTrue := fun H => h.boolTrue (by
      change env''.constants ``Bool.true = some _ at H
      rwa [same ``Bool.true (by decide)] at H)
    nat := fun H => by
      obtain ⟨hzero, hsucc⟩ := h.nat (oldContains (by decide) H)
      exact ⟨newContains hzero, newContains hsucc⟩
    natZero := fun H => h.natZero (by
      change env''.constants ``Nat.zero = some _ at H
      rwa [same ``Nat.zero (by decide)] at H)
    natSucc := fun H => h.natSucc (by
      change env''.constants ``Nat.succ = some _ at H
      rwa [same ``Nat.succ (by decide)] at H)
    natPred := (h.natPred.addConst hadd (by decide)).addDefEq
    natAdd := href
    natSub := (h.natSub.addConst hadd (by decide)).addDefEq
    natMul := (h.natMul.addConst hadd (by decide)).addDefEq
    natPow := (h.natPow.addConst hadd (by decide)).addDefEq
    natGcd := (h.natGcd.addConst hadd (by decide)).addDefEq
    natMod := (h.natMod.addConst hadd (by decide)).addDefEq
    natDiv := (h.natDiv.addConst hadd (by decide)).addDefEq
    natBEq := (h.natBEq.addConst hadd (by decide)).addDefEq
    natBLE := (h.natBLE.addConst hadd (by decide)).addDefEq
    natLAnd := (h.natLAnd.addConst hadd (by decide)).addDefEq
    natLOr := (h.natLOr.addConst hadd (by decide)).addDefEq
    natXor := (h.natXor.addConst hadd (by decide)).addDefEq
    natShiftLeft := (h.natShiftLeft.addConst hadd (by decide)).addDefEq
    natShiftRight := (h.natShiftRight.addConst hadd (by decide)).addDefEq
    charOfNat := fun H => h.charOfNat (by
      change env''.constants ``Char.ofNat = some _ at H
      rwa [same ``Char.ofNat (by decide)] at H)
    stringOfList := fun H => by
      change env''.constants ``String.ofList = some _ at H
      rw [same ``String.ofList (by decide)] at H
      obtain ⟨hshape, hnil, hcons⟩ := h.stringOfList H
      exact ⟨hshape, hnil.mono le, hcons.mono le⟩ }

/-- Replace the vacuous/old `Nat.sub` reflection field after inserting a
checked definition, while transporting all unrelated primitive facts. -/
theorem VEnv.HasPrimitives.addNatSub {env env' : VEnv}
    (h : env.HasPrimitives)
    (hadd : env.addConst ``Nat.sub ci = some env')
    (href : (env'.addDefEq df).ReflectsNatNatNat ``Nat.sub Nat.sub) :
    (env'.addDefEq df).HasPrimitives := by
  let env'' := env'.addDefEq df
  have le : env ≤ env'' := (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
  have same (p : Name) (hne : ``Nat.sub ≠ p) :
      env''.constants p = env.constants p := by
    change env'.constants p = env.constants p
    exact VEnv.addConst_other hadd hne
  have oldContains {p : Name} (hne : ``Nat.sub ≠ p)
      (H : env''.contains p) : env.contains p := by
    obtain ⟨pci, hpci⟩ := H
    exact ⟨pci, by rwa [same p hne] at hpci⟩
  have newContains {p : Name} (H : env.contains p) : env''.contains p := by
    obtain ⟨pci, hpci⟩ := H
    exact ⟨pci, le.constants hpci⟩
  exact {
    bool := fun H => by
      obtain ⟨hfalse, htrue⟩ := h.bool (oldContains (by decide) H)
      exact ⟨newContains hfalse, newContains htrue⟩
    boolFalse := fun H => h.boolFalse (by
      change env''.constants ``Bool.false = some _ at H
      rwa [same ``Bool.false (by decide)] at H)
    boolTrue := fun H => h.boolTrue (by
      change env''.constants ``Bool.true = some _ at H
      rwa [same ``Bool.true (by decide)] at H)
    nat := fun H => by
      obtain ⟨hzero, hsucc⟩ := h.nat (oldContains (by decide) H)
      exact ⟨newContains hzero, newContains hsucc⟩
    natZero := fun H => h.natZero (by
      change env''.constants ``Nat.zero = some _ at H
      rwa [same ``Nat.zero (by decide)] at H)
    natSucc := fun H => h.natSucc (by
      change env''.constants ``Nat.succ = some _ at H
      rwa [same ``Nat.succ (by decide)] at H)
    natPred := (h.natPred.addConst hadd (by decide)).addDefEq
    natAdd := (h.natAdd.addConst hadd (by decide)).addDefEq
    natSub := href
    natMul := (h.natMul.addConst hadd (by decide)).addDefEq
    natPow := (h.natPow.addConst hadd (by decide)).addDefEq
    natGcd := (h.natGcd.addConst hadd (by decide)).addDefEq
    natMod := (h.natMod.addConst hadd (by decide)).addDefEq
    natDiv := (h.natDiv.addConst hadd (by decide)).addDefEq
    natBEq := (h.natBEq.addConst hadd (by decide)).addDefEq
    natBLE := (h.natBLE.addConst hadd (by decide)).addDefEq
    natLAnd := (h.natLAnd.addConst hadd (by decide)).addDefEq
    natLOr := (h.natLOr.addConst hadd (by decide)).addDefEq
    natXor := (h.natXor.addConst hadd (by decide)).addDefEq
    natShiftLeft := (h.natShiftLeft.addConst hadd (by decide)).addDefEq
    natShiftRight := (h.natShiftRight.addConst hadd (by decide)).addDefEq
    charOfNat := fun H => h.charOfNat (by
      change env''.constants ``Char.ofNat = some _ at H
      rwa [same ``Char.ofNat (by decide)] at H)
    stringOfList := fun H => by
      change env''.constants ``String.ofList = some _ at H
      rw [same ``String.ofList (by decide)] at H
      obtain ⟨hshape, hnil, hcons⟩ := h.stringOfList H
      exact ⟨hshape, hnil.mono le, hcons.mono le⟩ }

/-- Replace the vacuous/old `Nat.mod` reflection field after inserting a
checked definition, while transporting all unrelated primitive facts. -/
theorem VEnv.HasPrimitives.addNatMod {env env' : VEnv}
    (h : env.HasPrimitives)
    (hadd : env.addConst ``Nat.mod ci = some env')
    (href : (env'.addDefEq df).ReflectsNatNatNat ``Nat.mod Nat.mod) :
    (env'.addDefEq df).HasPrimitives := by
  let env'' := env'.addDefEq df
  have le : env ≤ env'' := (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
  have same (p : Name) (hne : ``Nat.mod ≠ p) :
      env''.constants p = env.constants p := by
    change env'.constants p = env.constants p
    exact VEnv.addConst_other hadd hne
  have oldContains {p : Name} (hne : ``Nat.mod ≠ p)
      (H : env''.contains p) : env.contains p := by
    obtain ⟨pci, hpci⟩ := H
    exact ⟨pci, by rwa [same p hne] at hpci⟩
  have newContains {p : Name} (H : env.contains p) : env''.contains p := by
    obtain ⟨pci, hpci⟩ := H
    exact ⟨pci, le.constants hpci⟩
  exact {
    bool := fun H => by
      obtain ⟨hfalse, htrue⟩ := h.bool (oldContains (by decide) H)
      exact ⟨newContains hfalse, newContains htrue⟩
    boolFalse := fun H => h.boolFalse (by
      change env''.constants ``Bool.false = some _ at H
      rwa [same ``Bool.false (by decide)] at H)
    boolTrue := fun H => h.boolTrue (by
      change env''.constants ``Bool.true = some _ at H
      rwa [same ``Bool.true (by decide)] at H)
    nat := fun H => by
      obtain ⟨hzero, hsucc⟩ := h.nat (oldContains (by decide) H)
      exact ⟨newContains hzero, newContains hsucc⟩
    natZero := fun H => h.natZero (by
      change env''.constants ``Nat.zero = some _ at H
      rwa [same ``Nat.zero (by decide)] at H)
    natSucc := fun H => h.natSucc (by
      change env''.constants ``Nat.succ = some _ at H
      rwa [same ``Nat.succ (by decide)] at H)
    natPred := (h.natPred.addConst hadd (by decide)).addDefEq
    natAdd := (h.natAdd.addConst hadd (by decide)).addDefEq
    natMod := href
    natMul := (h.natMul.addConst hadd (by decide)).addDefEq
    natPow := (h.natPow.addConst hadd (by decide)).addDefEq
    natGcd := (h.natGcd.addConst hadd (by decide)).addDefEq
    natSub := (h.natSub.addConst hadd (by decide)).addDefEq
    natDiv := (h.natDiv.addConst hadd (by decide)).addDefEq
    natBEq := (h.natBEq.addConst hadd (by decide)).addDefEq
    natBLE := (h.natBLE.addConst hadd (by decide)).addDefEq
    natLAnd := (h.natLAnd.addConst hadd (by decide)).addDefEq
    natLOr := (h.natLOr.addConst hadd (by decide)).addDefEq
    natXor := (h.natXor.addConst hadd (by decide)).addDefEq
    natShiftLeft := (h.natShiftLeft.addConst hadd (by decide)).addDefEq
    natShiftRight := (h.natShiftRight.addConst hadd (by decide)).addDefEq
    charOfNat := fun H => h.charOfNat (by
      change env''.constants ``Char.ofNat = some _ at H
      rwa [same ``Char.ofNat (by decide)] at H)
    stringOfList := fun H => by
      change env''.constants ``String.ofList = some _ at H
      rw [same ``String.ofList (by decide)] at H
      obtain ⟨hshape, hnil, hcons⟩ := h.stringOfList H
      exact ⟨hshape, hnil.mono le, hcons.mono le⟩ }

/-- Replace the vacuous/old `Nat.mul` reflection field after inserting a
checked definition, while transporting all unrelated primitive facts. -/
theorem VEnv.HasPrimitives.addNatMul {env env' : VEnv}
    (h : env.HasPrimitives)
    (hadd : env.addConst ``Nat.mul ci = some env')
    (href : (env'.addDefEq df).ReflectsNatNatNat ``Nat.mul Nat.mul) :
    (env'.addDefEq df).HasPrimitives := by
  let env'' := env'.addDefEq df
  have le : env ≤ env'' := (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
  have same (p : Name) (hne : ``Nat.mul ≠ p) :
      env''.constants p = env.constants p := by
    change env'.constants p = env.constants p
    exact VEnv.addConst_other hadd hne
  have oldContains {p : Name} (hne : ``Nat.mul ≠ p)
      (H : env''.contains p) : env.contains p := by
    obtain ⟨pci, hpci⟩ := H
    exact ⟨pci, by rwa [same p hne] at hpci⟩
  have newContains {p : Name} (H : env.contains p) : env''.contains p := by
    obtain ⟨pci, hpci⟩ := H
    exact ⟨pci, le.constants hpci⟩
  exact {
    bool := fun H => by
      obtain ⟨hfalse, htrue⟩ := h.bool (oldContains (by decide) H)
      exact ⟨newContains hfalse, newContains htrue⟩
    boolFalse := fun H => h.boolFalse (by
      change env''.constants ``Bool.false = some _ at H
      rwa [same ``Bool.false (by decide)] at H)
    boolTrue := fun H => h.boolTrue (by
      change env''.constants ``Bool.true = some _ at H
      rwa [same ``Bool.true (by decide)] at H)
    nat := fun H => by
      obtain ⟨hzero, hsucc⟩ := h.nat (oldContains (by decide) H)
      exact ⟨newContains hzero, newContains hsucc⟩
    natZero := fun H => h.natZero (by
      change env''.constants ``Nat.zero = some _ at H
      rwa [same ``Nat.zero (by decide)] at H)
    natSucc := fun H => h.natSucc (by
      change env''.constants ``Nat.succ = some _ at H
      rwa [same ``Nat.succ (by decide)] at H)
    natPred := (h.natPred.addConst hadd (by decide)).addDefEq
    natAdd := (h.natAdd.addConst hadd (by decide)).addDefEq
    natSub := (h.natSub.addConst hadd (by decide)).addDefEq
    natMul := href
    natPow := (h.natPow.addConst hadd (by decide)).addDefEq
    natGcd := (h.natGcd.addConst hadd (by decide)).addDefEq
    natMod := (h.natMod.addConst hadd (by decide)).addDefEq
    natDiv := (h.natDiv.addConst hadd (by decide)).addDefEq
    natBEq := (h.natBEq.addConst hadd (by decide)).addDefEq
    natBLE := (h.natBLE.addConst hadd (by decide)).addDefEq
    natLAnd := (h.natLAnd.addConst hadd (by decide)).addDefEq
    natLOr := (h.natLOr.addConst hadd (by decide)).addDefEq
    natXor := (h.natXor.addConst hadd (by decide)).addDefEq
    natShiftLeft := (h.natShiftLeft.addConst hadd (by decide)).addDefEq
    natShiftRight := (h.natShiftRight.addConst hadd (by decide)).addDefEq
    charOfNat := fun H => h.charOfNat (by
      change env''.constants ``Char.ofNat = some _ at H
      rwa [same ``Char.ofNat (by decide)] at H)
    stringOfList := fun H => by
      change env''.constants ``String.ofList = some _ at H
      rw [same ``String.ofList (by decide)] at H
      obtain ⟨hshape, hnil, hcons⟩ := h.stringOfList H
      exact ⟨hshape, hnil.mono le, hcons.mono le⟩ }

/-- Replace the vacuous/old `Nat.pow` reflection field after inserting a
checked definition, while transporting all unrelated primitive facts. -/
theorem VEnv.HasPrimitives.addNatPow {env env' : VEnv}
    (h : env.HasPrimitives)
    (hadd : env.addConst ``Nat.pow ci = some env')
    (href : (env'.addDefEq df).ReflectsNatNatNat ``Nat.pow Nat.pow) :
    (env'.addDefEq df).HasPrimitives := by
  let env'' := env'.addDefEq df
  have le : env ≤ env'' := (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
  have same (p : Name) (hne : ``Nat.pow ≠ p) :
      env''.constants p = env.constants p := by
    change env'.constants p = env.constants p
    exact VEnv.addConst_other hadd hne
  have oldContains {p : Name} (hne : ``Nat.pow ≠ p)
      (H : env''.contains p) : env.contains p := by
    obtain ⟨pci, hpci⟩ := H
    exact ⟨pci, by rwa [same p hne] at hpci⟩
  have newContains {p : Name} (H : env.contains p) : env''.contains p := by
    obtain ⟨pci, hpci⟩ := H
    exact ⟨pci, le.constants hpci⟩
  exact {
    bool := fun H => by
      obtain ⟨hfalse, htrue⟩ := h.bool (oldContains (by decide) H)
      exact ⟨newContains hfalse, newContains htrue⟩
    boolFalse := fun H => h.boolFalse (by
      change env''.constants ``Bool.false = some _ at H
      rwa [same ``Bool.false (by decide)] at H)
    boolTrue := fun H => h.boolTrue (by
      change env''.constants ``Bool.true = some _ at H
      rwa [same ``Bool.true (by decide)] at H)
    nat := fun H => by
      obtain ⟨hzero, hsucc⟩ := h.nat (oldContains (by decide) H)
      exact ⟨newContains hzero, newContains hsucc⟩
    natZero := fun H => h.natZero (by
      change env''.constants ``Nat.zero = some _ at H
      rwa [same ``Nat.zero (by decide)] at H)
    natSucc := fun H => h.natSucc (by
      change env''.constants ``Nat.succ = some _ at H
      rwa [same ``Nat.succ (by decide)] at H)
    natPred := (h.natPred.addConst hadd (by decide)).addDefEq
    natAdd := (h.natAdd.addConst hadd (by decide)).addDefEq
    natSub := (h.natSub.addConst hadd (by decide)).addDefEq
    natMul := (h.natMul.addConst hadd (by decide)).addDefEq
    natPow := href
    natGcd := (h.natGcd.addConst hadd (by decide)).addDefEq
    natMod := (h.natMod.addConst hadd (by decide)).addDefEq
    natDiv := (h.natDiv.addConst hadd (by decide)).addDefEq
    natBEq := (h.natBEq.addConst hadd (by decide)).addDefEq
    natBLE := (h.natBLE.addConst hadd (by decide)).addDefEq
    natLAnd := (h.natLAnd.addConst hadd (by decide)).addDefEq
    natLOr := (h.natLOr.addConst hadd (by decide)).addDefEq
    natXor := (h.natXor.addConst hadd (by decide)).addDefEq
    natShiftLeft := (h.natShiftLeft.addConst hadd (by decide)).addDefEq
    natShiftRight := (h.natShiftRight.addConst hadd (by decide)).addDefEq
    charOfNat := fun H => h.charOfNat (by
      change env''.constants ``Char.ofNat = some _ at H
      rwa [same ``Char.ofNat (by decide)] at H)
    stringOfList := fun H => by
      change env''.constants ``String.ofList = some _ at H
      rw [same ``String.ofList (by decide)] at H
      obtain ⟨hshape, hnil, hcons⟩ := h.stringOfList H
      exact ⟨hshape, hnil.mono le, hcons.mono le⟩ }

/-- Replace the vacuous/old `Nat.beq` reflection field after inserting a
checked definition, while transporting all unrelated primitive facts. -/
theorem VEnv.HasPrimitives.addNatBEq {env env' : VEnv}
    (h : env.HasPrimitives)
    (hadd : env.addConst ``Nat.beq ci = some env')
    (href : (env'.addDefEq df).ReflectsNatNatBool ``Nat.beq Nat.beq) :
    (env'.addDefEq df).HasPrimitives := by
  let env'' := env'.addDefEq df
  have le : env ≤ env'' := (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
  have same (p : Name) (hne : ``Nat.beq ≠ p) :
      env''.constants p = env.constants p := by
    change env'.constants p = env.constants p
    exact VEnv.addConst_other hadd hne
  have oldContains {p : Name} (hne : ``Nat.beq ≠ p)
      (H : env''.contains p) : env.contains p := by
    obtain ⟨pci, hpci⟩ := H
    exact ⟨pci, by rwa [same p hne] at hpci⟩
  have newContains {p : Name} (H : env.contains p) : env''.contains p := by
    obtain ⟨pci, hpci⟩ := H
    exact ⟨pci, le.constants hpci⟩
  exact {
    bool := fun H => by
      obtain ⟨hfalse, htrue⟩ := h.bool (oldContains (by decide) H)
      exact ⟨newContains hfalse, newContains htrue⟩
    boolFalse := fun H => h.boolFalse (by
      change env''.constants ``Bool.false = some _ at H
      rwa [same ``Bool.false (by decide)] at H)
    boolTrue := fun H => h.boolTrue (by
      change env''.constants ``Bool.true = some _ at H
      rwa [same ``Bool.true (by decide)] at H)
    nat := fun H => by
      obtain ⟨hzero, hsucc⟩ := h.nat (oldContains (by decide) H)
      exact ⟨newContains hzero, newContains hsucc⟩
    natZero := fun H => h.natZero (by
      change env''.constants ``Nat.zero = some _ at H
      rwa [same ``Nat.zero (by decide)] at H)
    natSucc := fun H => h.natSucc (by
      change env''.constants ``Nat.succ = some _ at H
      rwa [same ``Nat.succ (by decide)] at H)
    natPred := (h.natPred.addConst hadd (by decide)).addDefEq
    natAdd := (h.natAdd.addConst hadd (by decide)).addDefEq
    natSub := (h.natSub.addConst hadd (by decide)).addDefEq
    natMul := (h.natMul.addConst hadd (by decide)).addDefEq
    natPow := (h.natPow.addConst hadd (by decide)).addDefEq
    natGcd := (h.natGcd.addConst hadd (by decide)).addDefEq
    natMod := (h.natMod.addConst hadd (by decide)).addDefEq
    natDiv := (h.natDiv.addConst hadd (by decide)).addDefEq
    natBEq := href
    natBLE := (h.natBLE.addConst hadd (by decide)).addDefEq
    natLAnd := (h.natLAnd.addConst hadd (by decide)).addDefEq
    natLOr := (h.natLOr.addConst hadd (by decide)).addDefEq
    natXor := (h.natXor.addConst hadd (by decide)).addDefEq
    natShiftLeft := (h.natShiftLeft.addConst hadd (by decide)).addDefEq
    natShiftRight := (h.natShiftRight.addConst hadd (by decide)).addDefEq
    charOfNat := fun H => h.charOfNat (by
      change env''.constants ``Char.ofNat = some _ at H
      rwa [same ``Char.ofNat (by decide)] at H)
    stringOfList := fun H => by
      change env''.constants ``String.ofList = some _ at H
      rw [same ``String.ofList (by decide)] at H
      obtain ⟨hshape, hnil, hcons⟩ := h.stringOfList H
      exact ⟨hshape, hnil.mono le, hcons.mono le⟩ }

/-- Replace the vacuous/old `Nat.ble` reflection field after inserting a
checked definition, while transporting all unrelated primitive facts. -/
theorem VEnv.HasPrimitives.addNatBLE {env env' : VEnv}
    (h : env.HasPrimitives)
    (hadd : env.addConst ``Nat.ble ci = some env')
    (href : (env'.addDefEq df).ReflectsNatNatBool ``Nat.ble Nat.ble) :
    (env'.addDefEq df).HasPrimitives := by
  let env'' := env'.addDefEq df
  have le : env ≤ env'' := (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
  have same (p : Name) (hne : ``Nat.ble ≠ p) :
      env''.constants p = env.constants p := by
    change env'.constants p = env.constants p
    exact VEnv.addConst_other hadd hne
  have oldContains {p : Name} (hne : ``Nat.ble ≠ p)
      (H : env''.contains p) : env.contains p := by
    obtain ⟨pci, hpci⟩ := H
    exact ⟨pci, by rwa [same p hne] at hpci⟩
  have newContains {p : Name} (H : env.contains p) : env''.contains p := by
    obtain ⟨pci, hpci⟩ := H
    exact ⟨pci, le.constants hpci⟩
  exact {
    bool := fun H => by
      obtain ⟨hfalse, htrue⟩ := h.bool (oldContains (by decide) H)
      exact ⟨newContains hfalse, newContains htrue⟩
    boolFalse := fun H => h.boolFalse (by
      change env''.constants ``Bool.false = some _ at H
      rwa [same ``Bool.false (by decide)] at H)
    boolTrue := fun H => h.boolTrue (by
      change env''.constants ``Bool.true = some _ at H
      rwa [same ``Bool.true (by decide)] at H)
    nat := fun H => by
      obtain ⟨hzero, hsucc⟩ := h.nat (oldContains (by decide) H)
      exact ⟨newContains hzero, newContains hsucc⟩
    natZero := fun H => h.natZero (by
      change env''.constants ``Nat.zero = some _ at H
      rwa [same ``Nat.zero (by decide)] at H)
    natSucc := fun H => h.natSucc (by
      change env''.constants ``Nat.succ = some _ at H
      rwa [same ``Nat.succ (by decide)] at H)
    natPred := (h.natPred.addConst hadd (by decide)).addDefEq
    natAdd := (h.natAdd.addConst hadd (by decide)).addDefEq
    natSub := (h.natSub.addConst hadd (by decide)).addDefEq
    natMul := (h.natMul.addConst hadd (by decide)).addDefEq
    natPow := (h.natPow.addConst hadd (by decide)).addDefEq
    natGcd := (h.natGcd.addConst hadd (by decide)).addDefEq
    natMod := (h.natMod.addConst hadd (by decide)).addDefEq
    natDiv := (h.natDiv.addConst hadd (by decide)).addDefEq
    natBEq := (h.natBEq.addConst hadd (by decide)).addDefEq
    natBLE := href
    natLAnd := (h.natLAnd.addConst hadd (by decide)).addDefEq
    natLOr := (h.natLOr.addConst hadd (by decide)).addDefEq
    natXor := (h.natXor.addConst hadd (by decide)).addDefEq
    natShiftLeft := (h.natShiftLeft.addConst hadd (by decide)).addDefEq
    natShiftRight := (h.natShiftRight.addConst hadd (by decide)).addDefEq
    charOfNat := fun H => h.charOfNat (by
      change env''.constants ``Char.ofNat = some _ at H
      rwa [same ``Char.ofNat (by decide)] at H)
    stringOfList := fun H => by
      change env''.constants ``String.ofList = some _ at H
      rw [same ``String.ofList (by decide)] at H
      obtain ⟨hshape, hnil, hcons⟩ := h.stringOfList H
      exact ⟨hshape, hnil.mono le, hcons.mono le⟩ }

/-- Replace the vacuous/old `Nat.shiftLeft` reflection field after inserting
a checked definition, while transporting all unrelated primitive facts. -/
theorem VEnv.HasPrimitives.addNatShiftLeft {env env' : VEnv}
    (h : env.HasPrimitives)
    (hadd : env.addConst ``Nat.shiftLeft ci = some env')
    (href : (env'.addDefEq df).ReflectsNatNatNat
      ``Nat.shiftLeft Nat.shiftLeft) :
    (env'.addDefEq df).HasPrimitives := by
  let env'' := env'.addDefEq df
  have le : env ≤ env'' := (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
  have same (p : Name) (hne : ``Nat.shiftLeft ≠ p) :
      env''.constants p = env.constants p := by
    change env'.constants p = env.constants p
    exact VEnv.addConst_other hadd hne
  have oldContains {p : Name} (hne : ``Nat.shiftLeft ≠ p)
      (H : env''.contains p) : env.contains p := by
    obtain ⟨pci, hpci⟩ := H
    exact ⟨pci, by rwa [same p hne] at hpci⟩
  have newContains {p : Name} (H : env.contains p) : env''.contains p := by
    obtain ⟨pci, hpci⟩ := H
    exact ⟨pci, le.constants hpci⟩
  exact {
    bool := fun H => by
      obtain ⟨hfalse, htrue⟩ := h.bool (oldContains (by decide) H)
      exact ⟨newContains hfalse, newContains htrue⟩
    boolFalse := fun H => h.boolFalse (by
      change env''.constants ``Bool.false = some _ at H
      rwa [same ``Bool.false (by decide)] at H)
    boolTrue := fun H => h.boolTrue (by
      change env''.constants ``Bool.true = some _ at H
      rwa [same ``Bool.true (by decide)] at H)
    nat := fun H => by
      obtain ⟨hzero, hsucc⟩ := h.nat (oldContains (by decide) H)
      exact ⟨newContains hzero, newContains hsucc⟩
    natZero := fun H => h.natZero (by
      change env''.constants ``Nat.zero = some _ at H
      rwa [same ``Nat.zero (by decide)] at H)
    natSucc := fun H => h.natSucc (by
      change env''.constants ``Nat.succ = some _ at H
      rwa [same ``Nat.succ (by decide)] at H)
    natPred := (h.natPred.addConst hadd (by decide)).addDefEq
    natAdd := (h.natAdd.addConst hadd (by decide)).addDefEq
    natSub := (h.natSub.addConst hadd (by decide)).addDefEq
    natMul := (h.natMul.addConst hadd (by decide)).addDefEq
    natPow := (h.natPow.addConst hadd (by decide)).addDefEq
    natGcd := (h.natGcd.addConst hadd (by decide)).addDefEq
    natMod := (h.natMod.addConst hadd (by decide)).addDefEq
    natDiv := (h.natDiv.addConst hadd (by decide)).addDefEq
    natBEq := (h.natBEq.addConst hadd (by decide)).addDefEq
    natBLE := (h.natBLE.addConst hadd (by decide)).addDefEq
    natLAnd := (h.natLAnd.addConst hadd (by decide)).addDefEq
    natLOr := (h.natLOr.addConst hadd (by decide)).addDefEq
    natXor := (h.natXor.addConst hadd (by decide)).addDefEq
    natShiftLeft := href
    natShiftRight := (h.natShiftRight.addConst hadd (by decide)).addDefEq
    charOfNat := fun H => h.charOfNat (by
      change env''.constants ``Char.ofNat = some _ at H
      rwa [same ``Char.ofNat (by decide)] at H)
    stringOfList := fun H => by
      change env''.constants ``String.ofList = some _ at H
      rw [same ``String.ofList (by decide)] at H
      obtain ⟨hshape, hnil, hcons⟩ := h.stringOfList H
      exact ⟨hshape, hnil.mono le, hcons.mono le⟩ }

/-- Shared bookkeeping for a checked Nat primitive definition: recover the
new constant typing, its definition equation, and the constructor typings in
the extended environment. -/
theorem VEnv.HasPrimitives.natDefKit {env env' : VEnv} {v : VDefVal}
    {n : Name} {ty : VExpr}
    (h : env.HasPrimitives) (hnat : env.contains ``Nat)
    (hname : v.name = n)
    (hadd : env.addConst n v.toVConstant = some env')
    (hwf : (env'.addDefEq v.toDefEq).WF)
    (hu : v.uvars = 0)
    (hty : env.IsDefEqU 0 [] v.type ty)
    (hnext :
      env ≤ env'.addDefEq v.toDefEq →
      (∀ U Γ, (env'.addDefEq v.toDefEq).HasType U Γ
        (.const n []) ty) →
      (env'.addDefEq v.toDefEq).IsDefEqU 0 []
        (.const n []) v.value →
      (∀ Γ, (env'.addDefEq v.toDefEq).HasType 0 Γ .natZero .nat) →
      (∀ Γ, (env'.addDefEq v.toDefEq).HasType 0 Γ .natSucc
        (.forallE .nat .nat)) →
      (env'.addDefEq v.toDefEq).HasPrimitives) :
    (env'.addDefEq v.toDefEq).HasPrimitives := by
  let env'' := env'.addDefEq v.toDefEq
  have le : env ≤ env'' := (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
  have hf (U Γ) : env''.HasType U Γ (.const n []) ty :=
    VEnv.HasType.const_of_type_defeq hwf (by
      change env'.constants n = some v.toVConstant
      exact VEnv.addConst_self hadd) hu (hty.mono le) U Γ
  have hcf := VDefVal.const_defeq_value hwf hu
  rw [hname] at hcf
  have hzero (Γ) : env''.HasType 0 Γ .natZero .nat :=
    (TrExprS.natZero h hnat (Us := []) (Δ := [])).2.mono le |>.weak0 hwf
  have hsucc (Γ) : env''.HasType 0 Γ .natSucc (.forallE .nat .nat) :=
    (TrExprS.natSucc h hnat (Us := []) (Δ := [])).2.mono le |>.weak0 hwf
  exact hnext le hf hcf hzero hsucc

/-- Nat.add-specialized compatibility wrapper around `natDefKit`. -/
theorem VEnv.HasPrimitives.natAddDefKit {env env' : VEnv} {v : VDefVal}
    (h : env.HasPrimitives) (hnat : env.contains ``Nat)
    (hname : v.name = ``Nat.add)
    (hadd : env.addConst ``Nat.add v.toVConstant = some env')
    (hwf : (env'.addDefEq v.toDefEq).WF)
    (hu : v.uvars = 0)
    (hty : env.IsDefEqU 0 [] v.type
      (.forallE .nat <| .forallE .nat .nat))
    (hnext :
      env ≤ env'.addDefEq v.toDefEq →
      (∀ U Γ, (env'.addDefEq v.toDefEq).HasType U Γ
        (.const ``Nat.add []) (.forallE .nat <| .forallE .nat .nat)) →
      (env'.addDefEq v.toDefEq).IsDefEqU 0 []
        (.const ``Nat.add []) v.value →
      (∀ Γ, (env'.addDefEq v.toDefEq).HasType 0 Γ .natZero .nat) →
      (∀ Γ, (env'.addDefEq v.toDefEq).HasType 0 Γ .natSucc
        (.forallE .nat .nat)) →
      (env'.addDefEq v.toDefEq).HasPrimitives) :
    (env'.addDefEq v.toDefEq).HasPrimitives :=
  h.natDefKit hnat hname hadd hwf hu hty hnext

/-- A checked, well-typed Nat.add definition with the two canonical recurrence
equations preserves `HasPrimitives` after installing its declaration equation. -/
theorem VEnv.HasPrimitives.addNatAddDef {env env' : VEnv} {v : VDefVal}
    (h : env.HasPrimitives) (hnat : env.contains ``Nat)
    (hname : v.name = ``Nat.add)
    (hadd : env.addConst ``Nat.add v.toVConstant = some env')
    (hwf : (env'.addDefEq v.toDefEq).WF)
    (hu : v.uvars = 0)
    (hty : env.IsDefEqU 0 [] v.type
      (.forallE .nat <| .forallE .nat .nat))
    (hz : env.IsDefEqU 0 []
      (.lam .nat <| .app (.app v.value (.bvar 0)) .natZero)
      (.lam .nat <| .bvar 0))
    (hs : env.IsDefEqU 0 []
      (.lam .nat <| .lam .nat <|
        .app (.app v.value (.bvar 1)) (.app .natSucc (.bvar 0)))
      (.lam .nat <| .lam .nat <|
        .app .natSucc (.app (.app v.value (.bvar 1)) (.bvar 0)))) :
    (env'.addDefEq v.toDefEq).HasPrimitives := by
  refine h.natAddDefKit hnat hname hadd hwf hu hty ?_
  intro le hf hcf hzero hsucc
  have href := VEnv.ReflectsNatNatNat.of_add_equations hwf hzero hsucc hf hcf
    (hz.mono le) (hs.mono le)
  exact h.addNatAdd hadd href

/-- A checked, well-typed Nat.sub definition with the canonical recurrence
equations preserves `HasPrimitives`. -/
theorem VEnv.HasPrimitives.addNatSubDef {env env' : VEnv} {v : VDefVal}
    (h : env.HasPrimitives) (henv : env.WF)
    (hpredC : env.contains ``Nat.pred)
    (hname : v.name = ``Nat.sub)
    (hadd : env.addConst ``Nat.sub v.toVConstant = some env')
    (hwf : (env'.addDefEq v.toDefEq).WF)
    (hu : v.uvars = 0)
    (hty : env.IsDefEqU 0 [] v.type
      (.forallE .nat <| .forallE .nat .nat))
    (hz : env.IsDefEqU 0 []
      (.lam .nat <| .app (.app v.value (.bvar 0)) .natZero)
      (.lam .nat <| .bvar 0))
    (hs : env.IsDefEqU 0 []
      (.lam .nat <| .lam .nat <|
        .app (.app v.value (.bvar 1)) (.app .natSucc (.bvar 0)))
      (.lam .nat <| .lam .nat <|
        .app (.const ``Nat.pred [])
          (.app (.app v.value (.bvar 1)) (.bvar 0)))) :
    (env'.addDefEq v.toDefEq).HasPrimitives := by
  have hnat : env.contains ``Nat := by
    have hfun := (h.natPred hpredC).1 0 []
    have ⟨_, hfunType⟩ := hfun.isType henv trivial
    obtain ⟨⟨_, hnatType⟩, _⟩ := hfunType.forallE_inv henv
    obtain ⟨_, hnat, _⟩ := hnatType.const_inv henv trivial
    exact ⟨_, hnat⟩
  refine h.natDefKit hnat hname hadd hwf hu hty ?_
  intro le hf hcf hzero hsucc
  have hpred : (env'.addDefEq v.toDefEq).ReflectsNatNat
      ``Nat.pred Nat.pred :=
    (h.natPred.addConst hadd (by decide)).addDefEq
  have hpredC' : (env'.addDefEq v.toDefEq).contains ``Nat.pred := by
    obtain ⟨predCi, hpredLookup⟩ := hpredC
    exact ⟨predCi, le.constants hpredLookup⟩
  have href := VEnv.ReflectsNatNatNat.of_sub_equations hwf hzero hsucc
    hpred hpredC' hf hcf (hz.mono le) (hs.mono le)
  exact h.addNatSub hadd href

/-- A checked, well-typed Nat.mul definition with the canonical recurrence
equations preserves `HasPrimitives`. -/
theorem VEnv.HasPrimitives.addNatMulDef {env env' : VEnv} {v : VDefVal}
    (h : env.HasPrimitives) (henv : env.WF)
    (haddC : env.contains ``Nat.add)
    (hname : v.name = ``Nat.mul)
    (hadd : env.addConst ``Nat.mul v.toVConstant = some env')
    (hwf : (env'.addDefEq v.toDefEq).WF)
    (hu : v.uvars = 0)
    (hty : env.IsDefEqU 0 [] v.type
      (.forallE .nat <| .forallE .nat .nat))
    (hz : env.IsDefEqU 0 []
      (.lam .nat <| .app (.app v.value (.bvar 0)) .natZero)
      (.lam .nat .natZero))
    (hs : env.IsDefEqU 0 []
      (.lam .nat <| .lam .nat <|
        .app (.app v.value (.bvar 1)) (.app .natSucc (.bvar 0)))
      (.lam .nat <| .lam .nat <|
        .app (.app (.const ``Nat.add [])
          (.app (.app v.value (.bvar 1)) (.bvar 0))) (.bvar 1))) :
    (env'.addDefEq v.toDefEq).HasPrimitives := by
  have hnat : env.contains ``Nat := by
    have hfun := (h.natAdd haddC).1 0 []
    have ⟨_, hfunType⟩ := hfun.isType henv trivial
    obtain ⟨⟨_, hnatType⟩, _⟩ := hfunType.forallE_inv henv
    obtain ⟨_, hnat, _⟩ := hnatType.const_inv henv trivial
    exact ⟨_, hnat⟩
  refine h.natDefKit hnat hname hadd hwf hu hty ?_
  intro le hf hcf hzero hsucc
  have haddR : (env'.addDefEq v.toDefEq).ReflectsNatNatNat
      ``Nat.add Nat.add :=
    (h.natAdd.addConst hadd (by decide)).addDefEq
  have haddC' : (env'.addDefEq v.toDefEq).contains ``Nat.add := by
    obtain ⟨addCi, haddLookup⟩ := haddC
    exact ⟨addCi, le.constants haddLookup⟩
  have href := VEnv.ReflectsNatNatNat.of_mul_equations hwf hzero hsucc
    haddR haddC' hf hcf (hz.mono le) (hs.mono le)
  exact h.addNatMul hadd href

/-- A checked, well-typed Nat.pow definition with the canonical recurrence
equations preserves `HasPrimitives`. -/
theorem VEnv.HasPrimitives.addNatPowDef {env env' : VEnv} {v : VDefVal}
    (h : env.HasPrimitives) (henv : env.WF)
    (hmulC : env.contains ``Nat.mul)
    (hname : v.name = ``Nat.pow)
    (hadd : env.addConst ``Nat.pow v.toVConstant = some env')
    (hwf : (env'.addDefEq v.toDefEq).WF)
    (hu : v.uvars = 0)
    (hty : env.IsDefEqU 0 [] v.type
      (.forallE .nat <| .forallE .nat .nat))
    (hz : env.IsDefEqU 0 []
      (.lam .nat <| .app (.app v.value (.bvar 0)) .natZero)
      (.lam .nat <| .app .natSucc .natZero))
    (hs : env.IsDefEqU 0 []
      (.lam .nat <| .lam .nat <|
        .app (.app v.value (.bvar 1)) (.app .natSucc (.bvar 0)))
      (.lam .nat <| .lam .nat <|
        .app (.app (.const ``Nat.mul [])
          (.app (.app v.value (.bvar 1)) (.bvar 0))) (.bvar 1))) :
    (env'.addDefEq v.toDefEq).HasPrimitives := by
  have hnat : env.contains ``Nat := by
    have hfun := (h.natMul hmulC).1 0 []
    have ⟨_, hfunType⟩ := hfun.isType henv trivial
    obtain ⟨⟨_, hnatType⟩, _⟩ := hfunType.forallE_inv henv
    obtain ⟨_, hnat, _⟩ := hnatType.const_inv henv trivial
    exact ⟨_, hnat⟩
  refine h.natDefKit hnat hname hadd hwf hu hty ?_
  intro le hf hcf hzero hsucc
  have hmulR : (env'.addDefEq v.toDefEq).ReflectsNatNatNat
      ``Nat.mul Nat.mul :=
    (h.natMul.addConst hadd (by decide)).addDefEq
  have hmulC' : (env'.addDefEq v.toDefEq).contains ``Nat.mul := by
    obtain ⟨mulCi, hmulLookup⟩ := hmulC
    exact ⟨mulCi, le.constants hmulLookup⟩
  have href := VEnv.ReflectsNatNatNat.of_pow_equations hwf hzero hsucc
    hmulR hmulC' hf hcf (hz.mono le) (hs.mono le)
  exact h.addNatPow hadd href

/-- A checked, well-typed Nat.shiftLeft definition with its two recursive
equations preserves `HasPrimitives`. -/
theorem VEnv.HasPrimitives.addNatShiftLeftDef
    {env env' : VEnv} {v : VDefVal}
    (h : env.HasPrimitives) (henv : env.WF)
    (hmulC : env.contains ``Nat.mul)
    (hname : v.name = ``Nat.shiftLeft)
    (hadd : env.addConst ``Nat.shiftLeft v.toVConstant = some env')
    (hwf : (env'.addDefEq v.toDefEq).WF)
    (hu : v.uvars = 0)
    (hty : env.IsDefEqU 0 [] v.type
      (.forallE .nat <| .forallE .nat .nat))
    (hz : env.IsDefEqU 0 []
      (.lam .nat <| .app (.app v.value (.bvar 0)) .natZero)
      (.lam .nat <| .bvar 0))
    (hs : env.IsDefEqU 0 []
      (.lam .nat <| .lam .nat <|
        .app (.app v.value (.bvar 0)) (.app .natSucc (.bvar 1)))
      (.lam .nat <| .lam .nat <|
        .app (.app v.value
          (.app (.app (.const ``Nat.mul []) (.natLit 2)) (.bvar 0)))
          (.bvar 1))) :
    (env'.addDefEq v.toDefEq).HasPrimitives := by
  have hnat : env.contains ``Nat := by
    have hfun := (h.natMul hmulC).1 0 []
    have ⟨_, hfunType⟩ := hfun.isType henv trivial
    obtain ⟨⟨_, hnatType⟩, _⟩ := hfunType.forallE_inv henv
    obtain ⟨_, hnat, _⟩ := hnatType.const_inv henv trivial
    exact ⟨_, hnat⟩
  refine h.natDefKit hnat hname hadd hwf hu hty ?_
  intro le hf hcf hzero hsucc
  have hmulR : (env'.addDefEq v.toDefEq).ReflectsNatNatNat
      ``Nat.mul Nat.mul :=
    (h.natMul.addConst hadd (by decide)).addDefEq
  have hmulC' : (env'.addDefEq v.toDefEq).contains ``Nat.mul := by
    obtain ⟨mulCi, hmulLookup⟩ := hmulC
    exact ⟨mulCi, le.constants hmulLookup⟩
  have href := VEnv.ReflectsNatNatNat.of_shiftLeft_equations hwf hzero hsucc
    hmulR hmulC' hf hcf (hz.mono le) (hs.mono le)
  exact h.addNatShiftLeft hadd href

/-- A checked, well-typed Nat.beq definition with its four constructor
equations preserves `HasPrimitives`. -/
theorem VEnv.HasPrimitives.addNatBEqDef {env env' : VEnv} {v : VDefVal}
    (h : env.HasPrimitives) (hnat : env.contains ``Nat)
    (hbool : env.contains ``Bool)
    (hname : v.name = ``Nat.beq)
    (hadd : env.addConst ``Nat.beq v.toVConstant = some env')
    (hwf : (env'.addDefEq v.toDefEq).WF)
    (hu : v.uvars = 0)
    (hty : env.IsDefEqU 0 [] v.type
      (.forallE .nat <| .forallE .nat .bool))
    (h00 : env.IsDefEqU 0 []
      (.app (.app v.value .natZero) .natZero) .boolTrue)
    (h0s : env.IsDefEqU 0 []
      (.lam .nat <| .app (.app v.value .natZero)
        (.app .natSucc (.bvar 0))) (.lam .nat .boolFalse))
    (hs0 : env.IsDefEqU 0 []
      (.lam .nat <| .app (.app v.value (.app .natSucc (.bvar 0)))
        .natZero) (.lam .nat .boolFalse))
    (hss : env.IsDefEqU 0 []
      (.lam .nat <| .lam .nat <|
        .app (.app v.value (.app .natSucc (.bvar 1)))
          (.app .natSucc (.bvar 0)))
      (.lam .nat <| .lam .nat <|
        .app (.app v.value (.bvar 1)) (.bvar 0))) :
    (env'.addDefEq v.toDefEq).HasPrimitives := by
  refine h.natDefKit hnat hname hadd hwf hu hty ?_
  intro le hf hcf hzero hsucc
  have hboolLit (b) (Γ) :
      (env'.addDefEq v.toDefEq).HasType 0 Γ (.boolLit b) .bool :=
    (TrExprS.boolLit h hbool b (Us := []) (Δ := [])).2.mono le
      |>.weak0 hwf
  have href := VEnv.ReflectsNatNatBool.of_rec_equations hwf hzero hsucc
    hboolLit hf hcf (h00.mono le) (h0s.mono le) (hs0.mono le)
    (hss.mono le) (g := Nat.beq) (r00 := true) (r0s := false)
    (rs0 := false) (by rfl) (by intro b; rfl) (by intro a; rfl)
    (by intro a b; rfl)
  exact h.addNatBEq hadd href

/-- A checked, well-typed Nat.ble definition with its four constructor
equations preserves `HasPrimitives`. -/
theorem VEnv.HasPrimitives.addNatBLEDef {env env' : VEnv} {v : VDefVal}
    (h : env.HasPrimitives) (hnat : env.contains ``Nat)
    (hbool : env.contains ``Bool)
    (hname : v.name = ``Nat.ble)
    (hadd : env.addConst ``Nat.ble v.toVConstant = some env')
    (hwf : (env'.addDefEq v.toDefEq).WF)
    (hu : v.uvars = 0)
    (hty : env.IsDefEqU 0 [] v.type
      (.forallE .nat <| .forallE .nat .bool))
    (h00 : env.IsDefEqU 0 []
      (.app (.app v.value .natZero) .natZero) .boolTrue)
    (h0s : env.IsDefEqU 0 []
      (.lam .nat <| .app (.app v.value .natZero)
        (.app .natSucc (.bvar 0))) (.lam .nat .boolTrue))
    (hs0 : env.IsDefEqU 0 []
      (.lam .nat <| .app (.app v.value (.app .natSucc (.bvar 0)))
        .natZero) (.lam .nat .boolFalse))
    (hss : env.IsDefEqU 0 []
      (.lam .nat <| .lam .nat <|
        .app (.app v.value (.app .natSucc (.bvar 1)))
          (.app .natSucc (.bvar 0)))
      (.lam .nat <| .lam .nat <|
        .app (.app v.value (.bvar 1)) (.bvar 0))) :
    (env'.addDefEq v.toDefEq).HasPrimitives := by
  refine h.natDefKit hnat hname hadd hwf hu hty ?_
  intro le hf hcf hzero hsucc
  have hboolLit (b) (Γ) :
      (env'.addDefEq v.toDefEq).HasType 0 Γ (.boolLit b) .bool :=
    (TrExprS.boolLit h hbool b (Us := []) (Δ := [])).2.mono le
      |>.weak0 hwf
  have href := VEnv.ReflectsNatNatBool.of_rec_equations hwf hzero hsucc
    hboolLit hf hcf (h00.mono le) (h0s.mono le) (hs0.mono le)
    (hss.mono le) (g := Nat.ble) (r00 := true) (r0s := true)
    (rs0 := false) (by rfl) (by intro b; rfl) (by intro a; rfl)
    (by intro a b; rfl)
  exact h.addNatBLE hadd href

end Lean4Lean
