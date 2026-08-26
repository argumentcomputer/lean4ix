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
`6cfd43a48d17be85c76414638655c12ef9a7ee23`. The first slice covers only the
shared typed evidence needed by the elementary binary-Nat checkers and the
exact `Nat.add` recognizer branch.
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

end Environment

/-! ## Semantic conservation for `Nat.add` -/

/-- Adding an unrelated definitional equality preserves an existing binary
Nat reflection. -/
theorem VEnv.ReflectsNatNatNat.addDefEq {env : VEnv} {df : VDefEq}
    (h : env.ReflectsNatNatNat fc f) :
    (env.addDefEq df).ReflectsNatNatNat fc f := by
  intro hfc a b
  exact (h hfc a b).mono VEnv.addDefEq_le

/-- Adding an unrelated definitional equality preserves an existing
Nat-to-Bool reflection. -/
theorem VEnv.ReflectsNatNatBool.addDefEq {env : VEnv} {df : VDefEq}
    (h : env.ReflectsNatNatBool fc f) :
    (env.addDefEq df).ReflectsNatNatBool fc f := by
  intro hfc a b
  exact (h hfc a b).mono VEnv.addDefEq_le

/-- Adding a fresh, differently named constant preserves an existing binary
Nat reflection. -/
theorem VEnv.ReflectsNatNatNat.addConst {env env' : VEnv}
    (h : env.ReflectsNatNatNat fc f)
    (hadd : env.addConst n ci = some env') (hne : n ≠ fc) :
    env'.ReflectsNatNatNat fc f := by
  intro hfc a b
  obtain ⟨fcCi, hfcLookup⟩ := hfc
  have hold : env.contains fc := ⟨fcCi, by
    rwa [VEnv.addConst_other hadd hne] at hfcLookup⟩
  exact (h hold a b).mono (VEnv.addConst_le hadd)

/-- Adding a fresh, differently named constant preserves an existing
Nat-to-Bool reflection. -/
theorem VEnv.ReflectsNatNatBool.addConst {env env' : VEnv}
    (h : env.ReflectsNatNatBool fc f)
    (hadd : env.addConst n ci = some env') (hne : n ≠ fc) :
    env'.ReflectsNatNatBool fc f := by
  intro hfc a b
  obtain ⟨fcCi, hfcLookup⟩ := hfc
  have hold : env.contains fc := ⟨fcCi, by
    rwa [VEnv.addConst_other hadd hne] at hfcLookup⟩
  exact (h hold a b).mono (VEnv.addConst_le hadd)

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
  intro _ a b
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

/-- Common bookkeeping needed to turn the checked Nat.add equations for a
fresh definition into an updated primitive-reflection contract. -/
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
    (env'.addDefEq v.toDefEq).HasPrimitives := by
  let env'' := env'.addDefEq v.toDefEq
  have le : env ≤ env'' := (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
  have hf (U Γ) : env''.HasType U Γ (.const ``Nat.add [])
      (.forallE .nat <| .forallE .nat .nat) :=
    VEnv.HasType.const_of_type_defeq hwf (by
      change env'.constants ``Nat.add = some v.toVConstant
      exact VEnv.addConst_self hadd) hu (hty.mono le) U Γ
  have hcf := VDefVal.const_defeq_value hwf hu
  rw [hname] at hcf
  have hzero (Γ) : env''.HasType 0 Γ .natZero .nat :=
    (TrExprS.natZero h hnat (Us := []) (Δ := [])).2.mono le |>.weak0 hwf
  have hsucc (Γ) : env''.HasType 0 Γ .natSucc (.forallE .nat .nat) :=
    (TrExprS.natSucc h hnat (Us := []) (Δ := [])).2.mono le |>.weak0 hwf
  exact hnext le hf hcf hzero hsucc

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

end Lean4Lean
