import Lean4Lean.Theory.Typing.InductiveCertificate
import Lean4Lean.Theory.Typing.InductivePatternWF
import Lean4Lean.Theory.Typing.NestedTransport
import Lean4Lean.Verify.Typing.Lemmas

/-!
# Certified recursor-reduction consumers

The completed block certificates already own the environment WF,
`RuleClosure`, exact rule position, registration, and rule WF premises of
`BlockGenerationChecked.pat_wf`.  These wrappers discharge that stable half
once and leave only the reduction site's universe, match, check, and typed
spine evidence explicit.

This is intentionally a Verify-side module.  `pat_wf` currently carries the
transitional unique-typing `sorryAx`; these consumers expose that dependency
without importing it into the stable Theory certificate root.  They must not
be used as the semantic source for the normalization/inversion construction.
-/

namespace Lean4Lean

namespace VEnv

/-- The terminal type of a spine is determined syntactically by its start
type and argument list.  This small projection is useful when `SpineWF.split`
hides the cursor behind an existential. -/
theorem SpineWF.result_eq
    {env : VEnv} {U : Nat} {Γ : List VExpr} :
    ∀ {es A B₁}, env.SpineWF U Γ A es B₁ →
      ∀ {B₂}, env.SpineWF U Γ A es B₂ → B₁ = B₂
  | [], _, _, .nil, _, .nil => rfl
  | _ :: _, _, _, .cons _ h₁, _, .cons _ h₂ =>
    SpineWF.result_eq h₁ h₂

/-- The sixth argument of a typed `Quot.lift` spine has the quotient type
determined by the first two arguments. -/
theorem SpineWF.quotLift_major
    {env : VEnv} {U : Nat} {Γ : List VExpr}
    {u v : VLevel} {α r β f c q B : VExpr}
    (hlift : env.SpineWF U Γ (quotLiftConst.type.instL [u, v])
      [α, r, β, f, c, q] B) :
    env.HasType U Γ q
      (VExpr.appN (.const ``Quot [u]) [α, r]) := by
  have hsplit : env.SpineWF U Γ (quotLiftConst.type.instL [u, v])
      ([α, r, β, f, c] ++ [q]) B := by simpa using hlift
  obtain ⟨cursor, hprefix, htail⟩ := hsplit.split
  let As := (VExpr.telN 5 quotLiftConst.type).map
    (VExpr.instL [u, v])
  have htypeShape : quotLiftConst.type.instL [u, v] =
      VExpr.forallN As
        ((VExpr.dropN 5 quotLiftConst.type).instL [u, v]) := by
    dsimp [As]
    rw [← VExpr.instL_forallN, VExpr.forallN_telN_dropN]
  rw [htypeShape] at hprefix
  have hprefix0 := hprefix.retarget
    (by simp [As, quotLiftConst, VExpr.telN])
    ((VExpr.dropN 5 quotLiftConst.type).instL [u, v])
  rw [← htypeShape] at hprefix0
  have hresult :
      ((VExpr.dropN 5 quotLiftConst.type).instL [u, v]).instRev
        [α, r, β, f, c] =
        .forallE (VExpr.appN (.const ``Quot [u]) [α, r]) β.lift := by
    change
      VExpr.forallE
        (VExpr.appN (.const ``Quot [u])
          [(α.liftN 4).instRev [r, β, f, c],
            (r.liftN 3).instRev [β, f, c]])
        ((β.liftN 3).instRevAt [f, c] 1) = _
    have hα : (α.liftN 4).instRev [r, β, f, c] = α := by
      simpa using VExpr.instRev_liftN_len [r, β, f, c] α
    have hr : (r.liftN 3).instRev [β, f, c] = r := by
      simpa using VExpr.instRev_liftN_len [β, f, c] r
    have hβc : β.liftN 3 = (β.lift).liftN 2 1 := by
      symm
      simpa using VExpr.liftN'_liftN'
        (e := β) (n1 := 1) (n2 := 2) (k1 := 0) (k2 := 1)
        (by omega) (by omega)
    have hβ : (β.liftN 3).instRevAt [f, c] 1 = β.lift := by
      rw [hβc]
      exact VExpr.instRevAt_liftN_gap [f, c] β.lift 1
    rw [hα, hr, hβ]
  rw [hresult] at hprefix0
  have hcursor : cursor =
      .forallE (VExpr.appN (.const ``Quot [u]) [α, r]) β.lift :=
    hprefix.result_eq hprefix0
  rw [hcursor] at htail
  cases htail with
  | cons hq _ => exact hq

/-- Retarget a complete `Quot.mk` spine to its canonical quotient result.
This removes the raw iterated-substitution endpoint produced by generic
application-spine reconstruction. -/
theorem SpineWF.quotMk_exact
    {env : VEnv} {U : Nat} {Γ : List VExpr}
    {u : VLevel} {α r a B : VExpr}
    (hmk : env.SpineWF U Γ (quotMkConst.type.instL [u])
      [α, r, a] B) :
    env.SpineWF U Γ (quotMkConst.type.instL [u])
      [α, r, a] (VExpr.appN (.const ``Quot [u]) [α, r]) := by
  let As := (VExpr.telN 3 quotMkConst.type).map (VExpr.instL [u])
  have htypeShape : quotMkConst.type.instL [u] =
      VExpr.forallN As ((VExpr.dropN 3 quotMkConst.type).instL [u]) := by
    dsimp [As]
    rw [← VExpr.instL_forallN, VExpr.forallN_telN_dropN]
  rw [htypeShape] at hmk
  have hmk0 := hmk.retarget
    (by simp [As, quotMkConst, VExpr.telN])
    ((VExpr.dropN 3 quotMkConst.type).instL [u])
  rw [← htypeShape] at hmk0
  have hresult :
      ((VExpr.dropN 3 quotMkConst.type).instL [u]).instRev
        [α, r, a] = VExpr.appN (.const ``Quot [u]) [α, r] := by
    change VExpr.appN (.const ``Quot [u])
      [(α.liftN 2).instRev [r, a], (r.lift).instRev [a]] = _
    have hα : (α.liftN 2).instRev [r, a] = α := by
      simpa using VExpr.instRev_liftN_len [r, a] α
    have hr : (r.lift).instRev [a] = r := by
      simpa using VExpr.instRev_liftN_len [a] r
    rw [hα, hr]
  rw [hresult] at hmk0
  exact hmk0

/-- A complete `Quot.ind` spine exposes the exact motive, minor premise, and
major-premise typings needed by proof-irrelevant reduction. -/
theorem SpineWF.quotInd_components
    {env : VEnv} {U : Nat} {Γ : List VExpr} {u : VLevel}
    {α r β p q B : VExpr}
    (hind : env.SpineWF U Γ (quotIndConst.type.instL [u])
      [α, r, β, p, q] B) :
    env.HasType U Γ β
        (.forallE (VExpr.appN (.const ``Quot [u]) [α, r]) (.sort .zero)) ∧
      env.HasType U Γ p
        (.forallE α
          (.app β.lift
            (VExpr.appN (.const ``Quot.mk [u])
              [α.lift, r.lift, .bvar 0]))) ∧
        env.HasType U Γ q
          (VExpr.appN (.const ``Quot [u]) [α, r]) := by
  generalize hB : B = B' at hind
  cases hind with
  | cons _ hrest =>
    cases hrest with
    | cons _ hrest =>
      cases hrest with
      | cons hβ hrest =>
        cases hrest with
        | cons hp hrest =>
          cases hrest with
          | cons hq _ =>
            constructor
            · change env.IsDefEq U Γ β β
                (.forallE
                  (VExpr.appN (.const ``Quot [u]) [α, r]) (.sort .zero))
              simpa [quotIndConst, VExpr.instL, VExpr.inst,
                VExpr.instVar, VExpr.liftN, VExpr.inst_lift,
                VLevel.inst, VExpr.appN] using hβ
            · constructor
              · change env.IsDefEq U Γ p p
                  (.forallE α
                    (.app β.lift
                      (VExpr.appN (.const ``Quot.mk [u])
                        [α.lift, r.lift, .bvar 0])))
                have hα : (α.liftN 2).instRev [r, β] = α := by
                  simpa using VExpr.instRev_liftN_len [r, β] α
                have hαc : α.liftN 3 = (α.lift).liftN 2 1 := by
                  symm
                  simpa using VExpr.liftN'_liftN'
                    (e := α) (n1 := 1) (n2 := 2)
                    (k1 := 0) (k2 := 1) (by omega) (by omega)
                have hαLift :
                    (α.liftN 3).instRevAt [r, β] 1 = α.lift := by
                  rw [hαc]
                  exact VExpr.instRevAt_liftN_gap [r, β] α.lift 1
                have hrc : r.liftN 2 = (r.lift).liftN 1 1 := by
                  symm
                  simpa using VExpr.liftN'_liftN'
                    (e := r) (n1 := 1) (n2 := 1)
                    (k1 := 0) (k2 := 1) (by omega) (by omega)
                have hrLift :
                    (r.liftN 2).instRevAt [β] 1 = r.lift := by
                  rw [hrc]
                  exact VExpr.instRevAt_liftN_gap [β] r.lift 1
                change env.IsDefEq U Γ p p
                  (.forallE ((α.liftN 2).instRev [r, β])
                    (.app β.lift
                      (VExpr.appN (.const ``Quot.mk [u])
                        [(α.liftN 3).instRevAt [r, β] 1,
                          (r.liftN 2).instRevAt [β] 1, .bvar 0]))) at hp
                rw [hα, hαLift, hrLift] at hp
                exact hp
              · change env.IsDefEq U Γ q q
                  (VExpr.appN (.const ``Quot [u]) [α, r])
                have hα : (α.liftN 3).instRev [r, β, p] = α := by
                  simpa using VExpr.instRev_liftN_len [r, β, p] α
                have hr : (r.liftN 2).instRev [β, p] = r := by
                  simpa using VExpr.instRev_liftN_len [β, p] r
                change env.IsDefEq U Γ q q
                  (VExpr.appN (.const ``Quot [u])
                    [(α.liftN 3).instRev [r, β, p],
                      (r.liftN 2).instRev [β, p]]) at hq
                rw [hα, hr] at hq
                exact hq

/-- Retarget a complete `Quot.ind` spine to the motive applied to its major
premise. -/
theorem SpineWF.quotInd_exact
    {env : VEnv} {U : Nat} {Γ : List VExpr} {u : VLevel}
    {α r β p q B : VExpr}
    (hind : env.SpineWF U Γ (quotIndConst.type.instL [u])
      [α, r, β, p, q] B) :
    env.SpineWF U Γ (quotIndConst.type.instL [u])
      [α, r, β, p, q] (.app β q) := by
  let As := (VExpr.telN 5 quotIndConst.type).map (VExpr.instL [u])
  have htypeShape : quotIndConst.type.instL [u] =
      VExpr.forallN As ((VExpr.dropN 5 quotIndConst.type).instL [u]) := by
    dsimp [As]
    rw [← VExpr.instL_forallN, VExpr.forallN_telN_dropN]
  rw [htypeShape] at hind
  have hind0 := hind.retarget
    (by simp [As, quotIndConst, VExpr.telN])
    ((VExpr.dropN 5 quotIndConst.type).instL [u])
  rw [← htypeShape] at hind0
  have hresult :
      ((VExpr.dropN 5 quotIndConst.type).instL [u]).instRev
        [α, r, β, p, q] = .app β q := by
    simp [quotIndConst, VExpr.dropN, VExpr.instL, VExpr.instRev,
      VExpr.inst, VExpr.instVar]
    simpa [VExpr.instRev] using VExpr.instRev_liftN_len [p, q] β
  rw [hresult] at hind0
  exact hind0

/-- The final argument of a typed `Quot.mk` spine is a representative of its
carrier. -/
theorem SpineWF.quotMk_representative
    {env : VEnv} {U : Nat} {Γ : List VExpr} {u : VLevel}
    {α r a B : VExpr}
    (hmk : env.SpineWF U Γ (quotMkConst.type.instL [u])
      [α, r, a] B) : env.HasType U Γ a α := by
  generalize hB : B = B' at hmk
  cases hmk with
  | cons _ hrest =>
    cases hrest with
    | cons _ hrest =>
      cases hrest with
      | cons ha _ =>
        change env.IsDefEq U Γ a a α
        simpa [quotMkConst, VExpr.instL, VExpr.inst,
          VExpr.instRev, VExpr.inst_lift] using ha

/-- Quotient-head injectivity transports a well-typed representative across
the exposed carrier/relation parameters and therefore makes the two
corresponding `Quot.mk` applications definitionally equal.  This is a
consumer of `QuotAppInj`, not its producer: all typing comes from the exact
constructor spine and the canonical quotient inventory. -/
theorem QuotAppInj.quotMk
    {env : VEnv} (henv : env.WF)
    {U : Nat} {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    (hinj : env.QuotAppInj)
    (hmk : env.constants ``Quot.mk = some quotMkConst)
    {u₁ u₂ : VLevel} {α₁ r₁ α₂ r₂ a B : VExpr}
    (hu₁ : u₁.WF U) (hu₂ : u₂.WF U)
    (hspine : env.SpineWF U Γ (quotMkConst.type.instL [u₁])
      [α₁, r₁, a] B)
    (hqeq : env.IsDefEqU U Γ
      (VExpr.appN (.const ``Quot [u₁]) [α₁, r₁])
      (VExpr.appN (.const ``Quot [u₂]) [α₂, r₂])) :
    env.IsDefEqU U Γ
      (VExpr.appN (.const ``Quot.mk [u₁]) [α₁, r₁, a])
      (VExpr.appN (.const ``Quot.mk [u₂]) [α₂, r₂, a]) := by
  obtain ⟨hu, hα, hr⟩ := hinj hqeq
  cases hspine with
  | cons hα₁ hrest =>
    cases hrest with
    | cons hr₁ hrest =>
      cases hrest with
      | cons ha hnil =>
        cases hnil
        have hhead : env.IsDefEq U Γ
            (.const ``Quot.mk [u₁]) (.const ``Quot.mk [u₂])
            (quotMkConst.type.instL [u₁]) := by
          exact .constDF hmk (by simp [hu₁]) (by simp [hu₂])
            (by simp [quotMkConst]) (.cons hu .nil)
        have hα' := hα.of_l henv hΓ hα₁
        have hr' := hr.of_l henv hΓ hr₁
        exact ⟨_, hhead.appDF hα' |>.appDF hr' |>.appDF ha⟩

private def quotDefEqLhsBody : VExpr :=
  VExpr.appN (.const ``Quot.lift [.param 0, .param 1])
    [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 1,
      VExpr.appN (.const ``Quot.mk [.param 0])
        [.bvar 5, .bvar 4, .bvar 0]]

private def quotDefEqRhsBody : VExpr :=
  VExpr.appN (.bvar 2) [.bvar 0]

/-- Apply the registered `Quot.lift` equation to its six typed captures and
beta-collapse both lambda towers.  Registration is the only reduction fact;
the capture spine remains an explicit consumer obligation. -/
theorem quotDefEq_reduction
    {env : VEnv} (henv : env.WF)
    {U : Nat} {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    (hreg : env.defeqs quotDefEq)
    {u v : VLevel} (hu : u.WF U) (hv : v.WF U)
    {α r β f c a B : VExpr}
    (hcaps : env.SpineWF U Γ (quotDefEq.type.instL [u, v])
      [α, r, β, f, c, a] B) :
    env.IsDefEqU U Γ
      (.app (VExpr.appN (.const ``Quot.lift [u, v]) [α, r, β, f, c])
        (VExpr.appN (.const ``Quot.mk [u]) [α, r, a]))
      (.app f a) := by
  let As := (VExpr.telN 6 quotDefEq.type).map (VExpr.instL [u, v])
  let lhsBody := quotDefEqLhsBody.instL [u, v]
  let rhsBody := quotDefEqRhsBody.instL [u, v]
  have htypeShape : quotDefEq.type.instL [u, v] =
      VExpr.forallN As ((VExpr.dropN 6 quotDefEq.type).instL [u, v]) := by
    dsimp [As]
    rw [← VExpr.instL_forallN, VExpr.forallN_telN_dropN]
  have hlhsShape : quotDefEq.lhs.instL [u, v] =
      VExpr.lamN As lhsBody := by
    dsimp [As, lhsBody]
    unfold quotDefEq quotDefEqLhsBody
    rfl
  have hrhsShape : quotDefEq.rhs.instL [u, v] =
      VExpr.lamN As rhsBody := by
    dsimp [As, rhsBody]
    unfold quotDefEq quotDefEqRhsBody
    rfl
  have hlen : ([α, r, β, f, c, a] : List VExpr).length = As.length := by
    simp [As, quotDefEq, VExpr.telN]
  have hlevels : ∀ l ∈ [u, v], l.WF U := by
    simp [hu, hv]
  have hwf := henv.ordered.defEqWF hreg
  have hlhsT := (hwf.1.instL hlevels).weak0 henv.ordered (Γ := Γ)
  have hrhsT := (hwf.2.instL hlevels).weak0 henv.ordered (Γ := Γ)
  have hcaps0 := hcaps
  rw [hlhsShape, htypeShape] at hlhsT
  rw [hrhsShape, htypeShape] at hrhsT
  rw [htypeShape] at hcaps
  obtain ⟨hTelL, TL, hbodyL⟩ :=
    VEnv.HasType.lamN_wf henv.ordered hΓ hlhsT
  obtain ⟨hTelR, TR, hbodyR⟩ :=
    VEnv.HasType.lamN_wf henv.ordered hΓ hrhsT
  have hcollapseL := VEnv.IsDefEq.appN_lamN henv.ordered hTelL hbodyL
    (hcaps.retarget hlen TL) hlen
  have hcollapseR := VEnv.IsDefEq.appN_lamN henv.ordered hTelR hbodyR
    (hcaps.retarget hlen TR) hlen
  have hregistered : env.IsDefEqU U Γ
      ((VExpr.lamN As lhsBody).appN [α, r, β, f, c, a])
      ((VExpr.lamN As rhsBody).appN [α, r, β, f, c, a]) := by
    have hregistered0 :=
      (VEnv.IsDefEq.extra hreg hlevels (by simp [quotDefEq])).appN_congr hcaps0
    rw [hlhsShape, hrhsShape] at hregistered0
    exact hregistered0.toU
  have hresult := VEnv.IsDefEqU.trans henv hΓ ⟨_, hcollapseL.symm⟩
    (VEnv.IsDefEqU.trans henv hΓ hregistered ⟨_, hcollapseR⟩)
  have hliftClosed :
      (VExpr.const ``Quot.lift [u, v]).instRev [α, r, β, f, c, a] =
        .const ``Quot.lift [u, v] :=
    VExpr.instRev_closedN _ (by trivial)
  have hmkClosed :
      (VExpr.const ``Quot.mk [u]).instRev [α, r, β, f, c, a] =
        .const ``Quot.mk [u] :=
    VExpr.instRev_closedN _ (by trivial)
  have hresult' : env.IsDefEqU U Γ
      (VExpr.appN (.const ``Quot.lift [u, v])
        [α, r, β, f, c, VExpr.appN (.const ``Quot.mk [u]) [α, r, a]])
      (VExpr.appN f [a]) := by
    simpa [lhsBody, rhsBody, quotDefEqLhsBody,
      quotDefEqRhsBody, VExpr.instL_appN, VExpr.instL,
      VExpr.instRev_appN, VExpr.instRev_bvar_lt,
      hliftClosed, hmkClosed, VLevel.inst] using hresult
  simpa [VExpr.appN] using hresult'

/-- A typed `Quot.lift` application whose major premise is definitionally
equal to a translated `Quot.mk` reduces to the function applied to the
representative.  The only head-inversion input is `QuotAppInj`; the actual
reduction equality is derived from the registered `quotDefEq` object.

The eliminator and constructor may initially carry different universe,
carrier, and relation parameters.  Quotient-head injectivity transports the
representative and canonicalizes the constructor before the registered
equation is applied. -/
theorem quotLift_mk_reduction
    {env : VEnv} (henv : env.WF)
    {U : Nat} {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    (hinj : env.QuotAppInj)
    (hobjects : env.HasObjects [.defeq quotDefEq,
      .const ``Quot.ind quotIndConst,
      .const ``Quot.lift quotLiftConst,
      .const ``Quot.mk quotMkConst, .const ``Quot quotConst])
    {u v u' : VLevel} (hu : u.WF U) (hv : v.WF U) (hu' : u'.WF U)
    {α r β f c q α' r' a Bl : VExpr}
    (hlift : env.SpineWF U Γ (quotLiftConst.type.instL [u, v])
      [α, r, β, f, c, q] Bl)
    (hmk : env.SpineWF U Γ (quotMkConst.type.instL [u'])
      [α', r', a]
      (VExpr.appN (.const ``Quot [u']) [α', r']))
    (hqtype : env.IsDefEqU U Γ
      (VExpr.appN (.const ``Quot [u']) [α', r'])
      (VExpr.appN (.const ``Quot [u]) [α, r]))
    (hmkq : env.IsDefEqU U Γ
      (VExpr.appN (.const ``Quot.mk [u']) [α', r', a]) q) :
    env.IsDefEqU U Γ
      (VExpr.appN (.const ``Quot.lift [u, v]) [α, r, β, f, c, q])
      (.app f a) := by
  have hmk0 := hmk
  obtain ⟨_, hαeq, _⟩ := hinj hqtype
  generalize hBm :
    VExpr.appN (.const ``Quot [u']) [α', r'] = Bm at hmk
  cases hmk with
  | cons _ hrest =>
    cases hrest with
    | cons _ hrest =>
      cases hrest with
      | cons ha hnil =>
        cases hnil
        have haAlpha : env.HasType U Γ a α' := by
          change env.IsDefEq U Γ a a α'
          simpa [quotMkConst, VExpr.instL, VExpr.inst,
            VExpr.instRev, VExpr.inst_lift] using ha
        have ha' := VEnv.HasType.defeqU_r henv hΓ hαeq haAlpha
        have hliftSplit : env.SpineWF U Γ
            (quotLiftConst.type.instL [u, v])
            ([α, r, β, f, c] ++ [q]) Bl := by simpa using hlift
        obtain ⟨_, hliftPrefix, _⟩ := hliftSplit.split
        let As := (VExpr.telN 5 quotLiftConst.type).map
          (VExpr.instL [u, v])
        have hliftTypeShape : quotLiftConst.type.instL [u, v] =
            VExpr.forallN As
              ((VExpr.dropN 5 quotLiftConst.type).instL [u, v]) := by
          dsimp [As]
          rw [← VExpr.instL_forallN, VExpr.forallN_telN_dropN]
        rw [hliftTypeShape] at hliftPrefix
        have hprefixDef0 := hliftPrefix.retarget
          (by simp [As, quotLiftConst, VExpr.telN])
          ((VExpr.dropN 5 quotDefEq.type).instL [u, v])
        have hdefTypeShape : quotDefEq.type.instL [u, v] =
            VExpr.forallN As
              ((VExpr.dropN 5 quotDefEq.type).instL [u, v]) := by
          dsimp [As]
          unfold quotLiftConst quotDefEq
          rfl
        rw [← hdefTypeShape] at hprefixDef0
        have hdefResult :
            ((VExpr.dropN 5 quotDefEq.type).instL [u, v]).instRev
              [α, r, β, f, c] = .forallE α β.lift := by
          change
            VExpr.forallE ((α.liftN 4).instRev [r, β, f, c])
              ((β.liftN 3).instRevAt [f, c] 1) =
                VExpr.forallE α β.lift
          have hαConsume :
              (α.liftN 4).instRev [r, β, f, c] = α := by
            simpa using VExpr.instRev_liftN_len [r, β, f, c] α
          have hβCompose : β.liftN 3 = (β.lift).liftN 2 1 := by
            symm
            simpa using VExpr.liftN'_liftN'
              (e := β) (n1 := 1) (n2 := 2) (k1 := 0) (k2 := 1)
              (by omega) (by omega)
          have hβConsume :
              (β.liftN 3).instRevAt [f, c] 1 = β.lift := by
            rw [hβCompose]
            exact VExpr.instRevAt_liftN_gap [f, c] β.lift 1
          rw [hαConsume, hβConsume]
        have hprefixDef : env.SpineWF U Γ
            (quotDefEq.type.instL [u, v]) [α, r, β, f, c]
            (.forallE α β.lift) := by
          rw [hdefResult] at hprefixDef0
          exact hprefixDef0
        have hcaps := hprefixDef.snoc ha'
        have hred := quotDefEq_reduction henv hΓ hobjects.1 hu hv hcaps
        have hmkCanonical := hinj.quotMk henv hΓ hobjects.2.2.2.1
          hu' hu hmk0 hqtype
        have hcanonicalQ := hmkCanonical.symm.trans henv hΓ hmkq
        have hmkHead : env.HasType U Γ (.const ``Quot.mk [u'])
            (quotMkConst.type.instL [u']) :=
          VEnv.HasType.const hobjects.2.2.2.1 (by simp [hu'])
            (by simp [quotMkConst])
        have hmkTerm : env.HasType U Γ
            (VExpr.appN (.const ``Quot.mk [u']) [α', r', a])
            (VExpr.appN (.const ``Quot [u']) [α', r']) :=
          hmk0.hasType_appN hmkHead
        have hcanonicalType0 := hmkCanonical.of_l henv hΓ hmkTerm
        have hcanonicalType : env.HasType U Γ
            (VExpr.appN (.const ``Quot.mk [u]) [α, r, a])
            (VExpr.appN (.const ``Quot [u]) [α, r]) :=
          VEnv.HasType.defeqU_r henv hΓ hqtype
            hcanonicalType0.hasType.2
        have hliftHead : env.HasType U Γ (.const ``Quot.lift [u, v])
            (quotLiftConst.type.instL [u, v]) :=
          VEnv.HasType.const hobjects.2.2.1 (by simp [hu, hv])
            (by simp [quotLiftConst])
        have hlift5 : env.HasType U Γ
            (VExpr.appN (.const ``Quot.lift [u, v]) [α, r, β, f, c])
            (.forallE
              (VExpr.appN (.const ``Quot [u]) [α, r]) β.lift) := by
          have hprefixLift0 := hliftPrefix.retarget
            (by simp [As, quotLiftConst, VExpr.telN])
            ((VExpr.dropN 5 quotLiftConst.type).instL [u, v])
          rw [← hliftTypeShape] at hprefixLift0
          have hliftResult :
              ((VExpr.dropN 5 quotLiftConst.type).instL [u, v]).instRev
                [α, r, β, f, c] =
                .forallE
                  (VExpr.appN (.const ``Quot [u]) [α, r]) β.lift := by
            change
              VExpr.forallE
                (VExpr.appN (.const ``Quot [u])
                  [(α.liftN 4).instRev [r, β, f, c],
                    (r.liftN 3).instRev [β, f, c]])
                ((β.liftN 3).instRevAt [f, c] 1) = _
            have hαConsume :
                (α.liftN 4).instRev [r, β, f, c] = α := by
              simpa using VExpr.instRev_liftN_len [r, β, f, c] α
            have hrConsume :
                (r.liftN 3).instRev [β, f, c] = r := by
              simpa using VExpr.instRev_liftN_len [β, f, c] r
            have hβCompose : β.liftN 3 = (β.lift).liftN 2 1 := by
              symm
              simpa using VExpr.liftN'_liftN'
                (e := β) (n1 := 1) (n2 := 2) (k1 := 0) (k2 := 1)
                (by omega) (by omega)
            have hβConsume :
                (β.liftN 3).instRevAt [f, c] 1 = β.lift := by
              rw [hβCompose]
              exact VExpr.instRevAt_liftN_gap [f, c] β.lift 1
            rw [hαConsume, hrConsume, hβConsume]
          have hprefixLift : env.SpineWF U Γ
              (quotLiftConst.type.instL [u, v]) [α, r, β, f, c]
              (.forallE
                (VExpr.appN (.const ``Quot [u]) [α, r]) β.lift) := by
            rw [hliftResult] at hprefixLift0
            exact hprefixLift0
          exact hprefixLift.hasType_appN hliftHead
        have hmajorEq := hcanonicalQ.of_l henv hΓ hcanonicalType
        have hcongr : env.IsDefEqU U Γ
            (.app (VExpr.appN (.const ``Quot.lift [u, v])
              [α, r, β, f, c])
              (VExpr.appN (.const ``Quot.mk [u]) [α, r, a]))
            (.app (VExpr.appN (.const ``Quot.lift [u, v])
              [α, r, β, f, c]) q) :=
          ⟨_, hlift5.appDF hmajorEq⟩
        exact hcongr.symm.trans henv hΓ hred

/-- `Quot.ind` reduces on a translated quotient constructor by proof
irrelevance.  Unlike `Quot.lift`, this needs no registered reduction object:
the eliminator result and the minor premise applied to the representative
are transported to the same proposition and then identified by the core
proof-irrelevance rule. -/
theorem quotInd_mk_reduction
    {env : VEnv} (henv : env.WF)
    {U : Nat} {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    (hinj : env.QuotAppInj)
    (hobjects : env.HasObjects [.defeq quotDefEq,
      .const ``Quot.ind quotIndConst,
      .const ``Quot.lift quotLiftConst,
      .const ``Quot.mk quotMkConst, .const ``Quot quotConst])
    {u u' : VLevel} (hu : u.WF U) (hu' : u'.WF U)
    {α r β p q α' r' a Bi : VExpr}
    (hind : env.SpineWF U Γ (quotIndConst.type.instL [u])
      [α, r, β, p, q] Bi)
    (hmk : env.SpineWF U Γ (quotMkConst.type.instL [u'])
      [α', r', a]
      (VExpr.appN (.const ``Quot [u']) [α', r']))
    (hqtype : env.IsDefEqU U Γ
      (VExpr.appN (.const ``Quot [u']) [α', r'])
      (VExpr.appN (.const ``Quot [u]) [α, r]))
    (hmkq : env.IsDefEqU U Γ
      (VExpr.appN (.const ``Quot.mk [u']) [α', r', a]) q) :
    env.IsDefEqU U Γ
      (VExpr.appN (.const ``Quot.ind [u]) [α, r, β, p, q])
      (.app p a) := by
  obtain ⟨hβ, hp, hq⟩ := hind.quotInd_components
  have ha' := hmk.quotMk_representative
  obtain ⟨_, hαeq, _⟩ := hinj hqtype
  have ha := VEnv.HasType.defeqU_r henv hΓ hαeq ha'
  have hmkCanonical := hinj.quotMk henv hΓ hobjects.2.2.2.1
    hu' hu hmk hqtype
  have hcanonicalQ := hmkCanonical.symm.trans henv hΓ hmkq
  have hmajorEq := hcanonicalQ.of_r henv hΓ hq
  have hpropEq : env.IsDefEqU U Γ
      (.app β (VExpr.appN (.const ``Quot.mk [u]) [α, r, a]))
      (.app β q) := ⟨_, hβ.appDF hmajorEq⟩
  have hpropQ : env.HasType U Γ (.app β q) (.sort .zero) :=
    hβ.app hq
  have hrhsCanonical : env.HasType U Γ (.app p a)
      (.app β (VExpr.appN (.const ``Quot.mk [u]) [α, r, a])) := by
    simpa [VExpr.inst, VExpr.inst_lift, VExpr.appN] using hp.app ha
  have hrhs := VEnv.HasType.defeqU_r henv hΓ hpropEq hrhsCanonical
  have hindHead : env.HasType U Γ (.const ``Quot.ind [u])
      (quotIndConst.type.instL [u]) :=
    VEnv.HasType.const hobjects.2.1 (by simp [hu])
      (by simp [quotIndConst])
  have hlhs : env.HasType U Γ
      (VExpr.appN (.const ``Quot.ind [u]) [α, r, β, p, q])
      (.app β q) :=
    hind.quotInd_exact.hasType_appN hindHead
  exact ⟨_, .proofIrrel hpropQ hlhs hrhs⟩

end VEnv

/-- info: 'Lean4Lean.VEnv.SpineWF.result_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Lean4Lean.VEnv.SpineWF.result_eq

/-- info: 'Lean4Lean.VEnv.SpineWF.quotLift_major' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VEnv.SpineWF.quotLift_major

/-- info: 'Lean4Lean.VEnv.SpineWF.quotMk_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VEnv.SpineWF.quotMk_exact

/-- info: 'Lean4Lean.VEnv.SpineWF.quotInd_components' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VEnv.SpineWF.quotInd_components

/-- info: 'Lean4Lean.VEnv.SpineWF.quotInd_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VEnv.SpineWF.quotInd_exact

/-- info: 'Lean4Lean.VEnv.SpineWF.quotMk_representative' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Lean4Lean.VEnv.SpineWF.quotMk_representative

/-- info: 'Lean4Lean.VEnv.QuotAppInj.quotMk' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VEnv.QuotAppInj.quotMk

/-- info: 'Lean4Lean.VEnv.quotDefEq_reduction' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VEnv.quotDefEq_reduction

/-- info: 'Lean4Lean.VEnv.quotLift_mk_reduction' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VEnv.quotLift_mk_reduction

/-- info: 'Lean4Lean.VEnv.quotInd_mk_reduction' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VEnv.quotInd_mk_reduction

namespace VInductDecl

namespace BlockGenerationChecked

variable {source : VInductDecl} (gen : source.BlockGenerationChecked)

/-- Pointwise translation commutes with the exact capture slices used by the
host reducer.  Reducer metadata alignment turns the translated slice into the
generator's canonical capture list. -/
theorem ruleCaptureValues_translation
    {α : Type _} {R : α → VExpr → Prop}
    {recArgs ctorArgs : List α} {fArgs aArgs : List VExpr}
    (constructor : NormalizedBlockCtor) (firstIndex nfields : Nat)
    (hrec : List.Forall₂ R recArgs fArgs)
    (hctor : List.Forall₂ R ctorArgs aArgs)
    (hfirst : firstIndex =
      source.nparams + gen.familyCount + gen.minorCount)
    (hfields : nfields = gen.ruleFieldCount constructor)
    (hctorLength : aArgs.length = gen.ruleArgArity constructor) :
    List.Forall₂ R
      (recArgs.take firstIndex ++
        ctorArgs.drop (ctorArgs.length - nfields))
      (gen.ruleCaptureValues constructor fArgs aArgs) := by
  have hstart : ctorArgs.length - nfields = aArgs.length - nfields := by
    rw [Lean4Lean.List.Forall₂.length_eq hctor]
  have hctorDrop : List.Forall₂ R
      (ctorArgs.drop (ctorArgs.length - nfields))
      (aArgs.drop (aArgs.length - nfields)) := by
    rw [← hstart]
    exact Lean4Lean.List.Forall₂.drop hctor (ctorArgs.length - nfields)
  have hcaptures := Lean4Lean.List.Forall₂.append
    (Lean4Lean.List.Forall₂.take hrec firstIndex) hctorDrop
  rw [← gen.ruleCaptureValues_eq_reducerSlices constructor fArgs aArgs
    firstIndex nfields hfirst hfields hctorLength] at hcaptures
  exact hcaptures

end BlockGenerationChecked

namespace BlockCertificate

variable {source : VInductDecl} {before after : VEnv}

/-- The certified family that owns one selected generated constructor.  The
facts retain the ordinal and normalized source-shape equalities needed to
rewrite the generated recursor and constructor types to the same head. -/
structure RuleOwnerFacts
    (certificate : BlockCertificate source before after)
    (constructor : NormalizedBlockCtor)
    (family : NormalizedFamily) : Prop where
  member : family ∈ certificate.generation.families
  ordinal : family.view.ordinal = constructor.owner
  name : family.raw.name = constructor.familyName
  indices : family.view.indices = constructor.familyIndices

/-- Recover the certified owner family of the constructor at an exact rule
position. -/
theorem ruleOwnerFacts
    (certificate : BlockCertificate source before after)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (facts : certificate.RecursorRuleFacts i constructor) :
    ∃ family, certificate.RuleOwnerFacts constructor family := by
  have hconstructor := List.mem_of_getElem? facts.entry
  obtain ⟨family, hfamily, hordinal, hname, hindices⟩ :=
    (certificate.generationEnv.ctorWF constructor hconstructor).owner
  exact ⟨family, hfamily, hordinal, hname, hindices⟩

/-- The completed transaction supplies the exact generated recursor-head
typing at runtime universe levels and in any well-formed local context. -/
theorem ruleRecursorHeadHasType
    (certificate : BlockCertificate source before after)
    {constructor : NormalizedBlockCtor} {family : NormalizedFamily}
    (owner : certificate.RuleOwnerFacts constructor family)
    {univs : Nat} {Γ : List VExpr} {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs)
    (hlen1 : m1.length = certificate.generation.recUvars) :
    after.HasType univs Γ
      (.const (certificate.generation.ruleRecName constructor) m1)
      ((certificate.generation.recType family).instL m1) := by
  let gen := certificate.generation
  have hrecursor :
      (⟨gen.generatedRecursor family, .str family.raw.name "rec"⟩ :
        VConstVal) ∈
        gen.recursors := by
    apply List.mem_map.2
    exact ⟨family, owner.member, rfl⟩
  have hlookup : after.constants (.str family.raw.name "rec") =
      some (gen.generatedRecursor family) := by
    simpa using certificate.recursorLookup hrecursor
  have hhead := certificate.generationEnv.recursor_hasType_instL
    owner.member hlookup m1 hm1 hlen1 (Γ := Γ)
  have hname : gen.ruleRecName constructor =
      (.str family.raw.name "rec" : Name) := by
    rw [BlockGenerationChecked.ruleRecName, ← owner.ordinal,
      gen.familyNameAt_ordinal owner.member]
  rwa [hname]

/-- The completed transaction likewise supplies the exact normalized
constructor-head typing used by the generated rule. -/
theorem ruleConstructorHeadHasType
    (certificate : BlockCertificate source before after)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (facts : certificate.RecursorRuleFacts i constructor)
    {family : NormalizedFamily}
    (owner : certificate.RuleOwnerFacts constructor family)
    {univs : Nat} {Γ : List VExpr} {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs) :
    after.HasType univs Γ
      (.const constructor.ctor.raw.name
        (certificate.generation.sourceLevels.map (VLevel.inst m1)))
      (VExpr.forallN
        ((certificate.generation.paramsTel ++
          constructor.ctor.fieldsR source.uvars source.nparams
            certificate.generation.elimination).map (VExpr.instL m1))
        ((certificate.generation.ruleCtorType constructor).instL m1)) := by
  exact certificate.generationEnv.ctorConst_emitted_instL
    (List.mem_of_getElem? facts.entry) owner.name m1 hm1

/-- At an unindexed generated iota site, the major premise has two explicit
types headed by its certified owner family: one obtained from the saturated
constructor spine and one from the saturated recursor spine.  Unique typing
makes those applications definitionally equal.  Turning this equality into
pointwise parameter agreement is precisely the separate inductive-head
injectivity obligation. -/
theorem ruleMajorTypesDefEqUnindexed
    (certificate : BlockCertificate source before after)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (facts : certificate.RecursorRuleFacts i constructor)
    {family : NormalizedFamily}
    (owner : certificate.RuleOwnerFacts constructor family)
    (hidx : certificate.generation.ruleIdx constructor = [])
    {univs : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (after.IsType univs))
    {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs)
    {fArgs aArgs : List VExpr}
    (hMlen : fArgs.length =
      certificate.generation.ruleMajorArity constructor)
    (hNlen : aArgs.length =
      certificate.generation.ruleArgArity constructor)
    {Ae Actor : VExpr}
    (hrecspine : after.SpineWF univs Γ
      ((certificate.generation.recType family).instL m1)
      (fArgs ++ [VExpr.appN (.const constructor.ctor.raw.name
        (certificate.generation.sourceLevels.map (VLevel.inst m1)))
        aArgs]) Ae)
    (hctorspine : after.SpineWF univs Γ
      (VExpr.forallN
        ((certificate.generation.paramsTel ++
          constructor.ctor.fieldsR source.uvars source.nparams
            certificate.generation.elimination).map (VExpr.instL m1))
        ((certificate.generation.ruleCtorType constructor).instL m1))
      aArgs Actor) :
    after.IsDefEqU univs Γ
      (VExpr.appN (.const family.raw.name
        (certificate.generation.sourceLevels.map (VLevel.inst m1)))
        (aArgs.take source.nparams))
      (VExpr.appN (.const family.raw.name
        (certificate.generation.sourceLevels.map (VLevel.inst m1)))
        (fArgs.take source.nparams)) := by
  let gen := certificate.generation
  have hconstructor : constructor ∈ gen.flatCtors :=
    List.mem_of_getElem? facts.entry
  have hidxArity := certificate.generationEnv
    |>.ruleIdx_length_eq_recIndexBinders hconstructor owner.member
      owner.indices
  have hidxRaw :
      constructor.ctor.resultIndicesR source.uvars gen.elimination = [] := by
    simpa only [BlockGenerationChecked.ruleIdx, List.map_eq_nil_iff]
      using hidx
  have hindexCount :
      (constructor.ctor.resultIndicesR source.uvars gen.elimination).length =
        (gen.idxTel family).length := by
    simpa only [BlockGenerationChecked.ruleIdx, List.length_map,
      BlockGenerationChecked.recIndexBinders,
      VExpr.liftTelN_length] using hidxArity
  have hrecIndicesNil : gen.recIndexBinders family = [] := by
    apply List.length_eq_zero_iff.1
    rw [← hidxArity, hidx]
    rfl
  have hrecspine' := hrecspine
  rw [gen.recType_instL_common family m1, hrecIndicesNil] at hrecspine'
  simp only [List.map_nil, VExpr.forallN] at hrecspine'
  have hcommonLen : fArgs.length =
      (gen.ruleCommonBinders.map (VExpr.instL m1)).length := by
    rw [List.length_map, gen.ruleCommonBinders_length, hMlen]
    simp [BlockGenerationChecked.ruleMajorArity, gen, hidxRaw]
  have hmajorRec := hrecspine'.lastForallN hcommonLen
  have hrecArgsLen : fArgs.length = source.nparams + gen.familyCount +
      gen.minorCount + (gen.idxTel family).length := by
    rw [hMlen]
    simp only [BlockGenerationChecked.ruleMajorArity]
    rw [hindexCount]
  rw [gen.recMajorDomain_instL_instRev family m1 fArgs hrecArgsLen]
    at hmajorRec
  have hrecDrop : fArgs.drop
      (source.nparams + gen.familyCount + gen.minorCount) = [] := by
    apply List.length_eq_zero_iff.1
    rw [List.length_drop, hMlen]
    simp [BlockGenerationChecked.ruleMajorArity, gen, hidxRaw]
  rw [hrecDrop, List.append_nil] at hmajorRec
  have hctorHead := certificate.generationEnv
    |>.ctorConst_emitted_instL hconstructor owner.name m1 hm1
      (Γ := Γ)
  have hctorBindersLen : aArgs.length =
      ((gen.paramsTel ++
        constructor.ctor.fieldsR source.uvars source.nparams
          gen.elimination).map (VExpr.instL m1)).length := by
    rw [hNlen]
    simp only [List.length_map, List.length_append,
      gen.paramsTel_length, BlockGenerationChecked.ruleArgArity,
      BlockGenerationChecked.ruleFieldCount]
    rfl
  have hctorExact := hctorspine.retarget hctorBindersLen
    ((gen.ruleCtorType constructor).instL m1)
  have hmajorCtor := hctorExact.hasType_appN hctorHead
  rw [gen.ruleCtorType_instL_instRev_of_unindexed constructor m1 aArgs
    hidx hNlen] at hmajorCtor
  rw [← owner.name] at hmajorCtor
  exact hmajorCtor.uniqU certificate.afterWF hΓ hmajorRec

/-- Consume the exact same-head equality above through an external
inductive-head injectivity theorem.  This formulation deliberately names the
remaining NORM boundary instead of baking an unproved injectivity principle
into the reduction certificate. -/
theorem ruleParameterAgreementUnindexedOfMajorInjectivity
    (certificate : BlockCertificate source before after)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (facts : certificate.RecursorRuleFacts i constructor)
    {family : NormalizedFamily}
    (owner : certificate.RuleOwnerFacts constructor family)
    (hidx : certificate.generation.ruleIdx constructor = [])
    {univs : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (after.IsType univs))
    {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs)
    {fArgs aArgs : List VExpr}
    (hMlen : fArgs.length =
      certificate.generation.ruleMajorArity constructor)
    (hNlen : aArgs.length =
      certificate.generation.ruleArgArity constructor)
    {Ae Actor : VExpr}
    (hrecspine : after.SpineWF univs Γ
      ((certificate.generation.recType family).instL m1)
      (fArgs ++ [VExpr.appN (.const constructor.ctor.raw.name
        (certificate.generation.sourceLevels.map (VLevel.inst m1)))
        aArgs]) Ae)
    (hctorspine : after.SpineWF univs Γ
      (VExpr.forallN
        ((certificate.generation.paramsTel ++
          constructor.ctor.fieldsR source.uvars source.nparams
            certificate.generation.elimination).map (VExpr.instL m1))
        ((certificate.generation.ruleCtorType constructor).instL m1))
      aArgs Actor)
    (hmajorInjective :
      after.IsDefEqU univs Γ
        (VExpr.appN (.const family.raw.name
          (certificate.generation.sourceLevels.map (VLevel.inst m1)))
          (aArgs.take source.nparams))
        (VExpr.appN (.const family.raw.name
          (certificate.generation.sourceLevels.map (VLevel.inst m1)))
          (fArgs.take source.nparams)) →
      List.Forall₂ (after.IsDefEqU univs Γ)
        (aArgs.take source.nparams) (fArgs.take source.nparams)) :
    List.Forall₂ (after.IsDefEqU univs Γ)
      (aArgs.take source.nparams) (fArgs.take source.nparams) :=
  hmajorInjective <| certificate.ruleMajorTypesDefEqUnindexed facts owner
    hidx hΓ hm1 hMlen hNlen hrecspine hctorspine

/-- For a one-parameter unindexed block, parameter agreement transports the
entire dependent constructor-field spine to the generated rule-field
telescope.  The generated lift by the motive/minor suffix cancels exactly,
so recursive and non-recursive fields use the same structural proof. -/
theorem ruleFieldSpineOneParam
    (certificate : BlockCertificate source before after)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (facts : certificate.RecursorRuleFacts i constructor)
    (hone : source.nparams = 1)
    (hidx : certificate.generation.ruleIdx constructor = [])
    {univs : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (after.IsType univs))
    {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs)
    {fArgs aArgs : List VExpr}
    (hMlen : fArgs.length =
      certificate.generation.ruleMajorArity constructor)
    (hNlen : aArgs.length =
      certificate.generation.ruleArgArity constructor)
    (hparams : List.Forall₂ (after.IsDefEqU univs Γ)
      (aArgs.take source.nparams) (fArgs.take source.nparams))
    {Actor : VExpr}
    (hctorspine : after.SpineWF univs Γ
      (VExpr.forallN
        ((certificate.generation.paramsTel ++
          constructor.ctor.fieldsR source.uvars source.nparams
            certificate.generation.elimination).map (VExpr.instL m1))
        ((certificate.generation.ruleCtorType constructor).instL m1))
      aArgs Actor) :
    ∃ B, after.SpineWF univs Γ
      (VExpr.instRev
        (VExpr.forallN
          ((certificate.generation.ruleFieldBinders constructor).map
            (VExpr.instL m1))
          ((certificate.generation.ruleResult constructor).instL m1))
        (fArgs.take (source.nparams +
          certificate.generation.familyCount +
          certificate.generation.minorCount)))
      (aArgs.drop source.nparams) B := by
  let gen := certificate.generation
  let fields :=
    (constructor.ctor.fieldsR source.uvars source.nparams
      gen.elimination).map (VExpr.instL m1)
  have hidxRaw :
      constructor.ctor.resultIndicesR source.uvars gen.elimination = [] := by
    simpa only [BlockGenerationChecked.ruleIdx, List.map_eq_nil_iff]
      using hidx
  have hMlenOne : fArgs.length =
      1 + (gen.familyCount + gen.minorCount) := by
    rw [hMlen]
    simp [BlockGenerationChecked.ruleMajorArity, hidxRaw, hone, gen]
    omega
  have hNlenOne : aArgs.length = 1 + fields.length := by
    rw [hNlen]
    simp [BlockGenerationChecked.ruleArgArity,
      BlockGenerationChecked.ruleFieldCount, fields, hone, gen]
  cases fArgs with
  | nil =>
    simp only [List.length_nil] at hMlenOne
    omega
  | cons f fTail =>
    cases aArgs with
    | nil =>
      simp only [List.length_nil] at hNlenOne
      omega
    | cons a aTail =>
      simp only [List.length_cons] at hMlenOne hNlenOne
      have hfTailLen : fTail.length =
          gen.familyCount + gen.minorCount := by
        omega
      have haTailLen : aTail.length = fields.length := by
        omega
      have hparamU : after.IsDefEqU univs Γ a f := by
        simpa [hone] using hparams
      have hparamTelLen :
          (gen.paramsTel.map (VExpr.instL m1)).length = 1 := by
        simp [gen.paramsTel_length, hone]
      obtain ⟨A, hparamTel⟩ := List.length_eq_one_iff.mp hparamTelLen
      have hparamsOnTel := certificate.generationEnv.paramsTel_onTel
      have hparamsOnTelL := hparamsOnTel.instL hm1
      have hparamsRuntime : after.OnTel univs [] [A] := by
        simpa [hparamTel, gen] using hparamsOnTelL
      have hfieldsOnTel := certificate.generationEnv
        |>.generationFields_onTel_rec
          (List.mem_of_getElem? facts.entry)
      have hfieldsOnTelL := hfieldsOnTel.instL hm1
      have hfieldsRuntime : after.OnTel univs [A] fields := by
        simpa [fields, List.map_reverse, hparamTel, gen] using hfieldsOnTelL
      have hparamCtx : OnCtx [A] (after.IsType univs) :=
        ⟨trivial, hparamsRuntime.1⟩
      have hfieldsΓ : after.OnTel univs (A :: Γ) fields := by
        simpa using VEnv.OnTel.weakR certificate.afterWF.ordered
          (Γ := [A]) (Γ' := Γ) hparamCtx hfieldsRuntime
      have hctorspineHead := hctorspine
      rw [List.map_append, hparamTel] at hctorspineHead
      simp only [VExpr.forallN, List.cons_append] at hctorspineHead
      cases hctorspineHead with
      | cons ha _ =>
        have haf : after.IsDefEq univs Γ a f A :=
          hparamU.of_l certificate.afterWF hΓ ha
        have hfieldTel : after.TelDefEq univs Γ
            (VExpr.instTelN f fields 0)
            (VExpr.instTelN a fields 0) :=
          hfieldsΓ.telDefEq_instDF certificate.afterWF hΓ haf.symm
        have hctorFields := gen.ruleConstructorFieldSpine constructor
          hNlen hctorspine
        have htakeA : (a :: aTail).take source.nparams = [a] := by
          simp [hone]
        have hdropA : (a :: aTail).drop source.nparams = aTail := by
          simp [hone]
        rw [htakeA, hdropA] at hctorFields
        change after.SpineWF univs Γ
          (VExpr.instRev
            (VExpr.forallN fields
              ((gen.ruleCtorType constructor).instL m1)) [a])
          aTail Actor at hctorFields
        have hctorCursor :=
          VExpr.instRev_forallN_liftTelN_suffix_one fields
            ((gen.ruleCtorType constructor).instL m1) a []
        have hctorCursor' :
            VExpr.instRev
                (VExpr.forallN fields
                  ((gen.ruleCtorType constructor).instL m1)) [a] =
              VExpr.forallN (VExpr.instTelN a fields 0)
                (((gen.ruleCtorType constructor).instL m1).instRevAt
                  [a] fields.length) := by
          simpa using hctorCursor
        rw [hctorCursor'] at hctorFields
        have haInstLen : aTail.length =
            (VExpr.instTelN a fields 0).length := by
          rw [VExpr.instTelN_length]
          exact haTailLen
        have hfInstLen : aTail.length =
            (VExpr.instTelN f fields 0).length := by
          rw [VExpr.instTelN_length]
          exact haTailLen
        have hctorSort := hctorFields.retarget haInstLen (.sort .zero)
        rw [VExpr.instRev_closedN aTail (by trivial)] at hctorSort
        have hfieldSort := VEnv.TelDefEq.spine_sort
          certificate.afterWF.ordered hfieldTel hctorSort hfInstLen
        let result := (gen.ruleResult constructor).instL m1
        let result' := result.instRevAt (f :: fTail) fields.length
        have hfieldResult := hfieldSort.retarget hfInstLen result'
        have htake :
            (f :: fTail).take
                (source.nparams + gen.familyCount + gen.minorCount) =
              f :: fTail := by
          apply List.take_of_length_le
          simp only [List.length_cons, hone, hfTailLen]
          omega
        refine ⟨VExpr.instRev result' aTail, ?_⟩
        rw [htake, hdropA]
        change after.SpineWF univs Γ
          (VExpr.instRev
            (VExpr.forallN
              ((gen.ruleFieldBinders constructor).map (VExpr.instL m1))
              result)
            (f :: fTail)) aTail _
        rw [BlockGenerationChecked.ruleFieldBinders,
          VExpr.liftTelN_instL, ← hfTailLen,
          VExpr.instRev_forallN_liftTelN_suffix_one]
        exact hfieldResult

/-- A completed ordinary block reduces at one exact certified rule once the
runtime match, checks, and typed spines are supplied. -/
theorem ruleReduction
    (certificate : BlockCertificate source before after)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (facts : certificate.RecursorRuleFacts i constructor)
    {univs : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (after.IsType univs))
    {m1 : List VLevel} {m2}
    (hm1 : ∀ l ∈ m1, l.WF univs)
    (hlen1 : m1.length = certificate.generation.recUvars)
    {fArgs aArgs : List VExpr}
    (hMlen : fArgs.length =
      certificate.generation.ruleMajorArity constructor)
    (hNlen : aArgs.length =
      certificate.generation.ruleArgArity constructor)
    (hm : ((certificate.generation.rulePattern constructor).toPattern).Matches
      (.app
        (VExpr.appN (.const
          (certificate.generation.ruleRecName constructor) m1) fArgs)
        (VExpr.appN (.const constructor.ctor.raw.name
          (certificate.generation.sourceLevels.map (VLevel.inst m1)))
          aArgs)) m1 m2)
    (hck : (certificate.generation.ruleCheck certificate.ruleClosure
      (List.mem_of_getElem? facts.entry)).OK
        (after.IsDefEqU univs Γ) m1 m2)
    {Frec Ae : VExpr}
    (hehead : after.HasType univs Γ
      (.const (certificate.generation.ruleRecName constructor) m1) Frec)
    (hespine : after.SpineWF univs Γ Frec
      (fArgs ++ [VExpr.appN (.const constructor.ctor.raw.name
        (certificate.generation.sourceLevels.map (VLevel.inst m1)))
        aArgs]) Ae)
    {Fctor Actor : VExpr}
    (hctorhead : after.HasType univs Γ
      (.const constructor.ctor.raw.name
        (certificate.generation.sourceLevels.map (VLevel.inst m1))) Fctor)
    (hctorspine : after.SpineWF univs Γ Fctor aArgs Actor)
    {B : VExpr}
    (hcaps : after.SpineWF univs Γ
      ((certificate.generation.rule i constructor).type.instL m1)
      (fArgs.take (source.nparams + certificate.generation.familyCount +
          certificate.generation.minorCount) ++
        aArgs.drop source.nparams) B) :
    after.IsDefEqU univs Γ
      (.app
        (VExpr.appN (.const
          (certificate.generation.ruleRecName constructor) m1) fArgs)
        (VExpr.appN (.const constructor.ctor.raw.name
          (certificate.generation.sourceLevels.map (VLevel.inst m1)))
          aArgs))
      ((certificate.generation.ruleRHS certificate.ruleClosure
        facts.entry).apply m1 m2) := by
  exact certificate.generation.pat_wf certificate.afterWF hΓ
    certificate.ruleClosure facts.entry facts.registered facts.wf hm1
    hlen1 hMlen hNlen hm hck hehead hespine hctorhead hctorspine hcaps

/-- Construct the generated iota match from the two completed runtime spines
and reduce through the certified rule.  The generated checks are discharged
from the two visible semantic alignments—constructor/recursor parameters and
explicit recursor indices/computed constructor indices—and the result is
normalized to the registered RHS applied to the canonical capture list. -/
theorem ruleReductionMatched
    (certificate : BlockCertificate source before after)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (facts : certificate.RecursorRuleFacts i constructor)
    {univs : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (after.IsType univs))
    {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs)
    (hlen1 : m1.length = certificate.generation.recUvars)
    {fArgs aArgs : List VExpr}
    (hMlen : fArgs.length =
      certificate.generation.ruleMajorArity constructor)
    (hNlen : aArgs.length =
      certificate.generation.ruleArgArity constructor)
    (hparams : List.Forall₂ (after.IsDefEqU univs Γ)
      (aArgs.take source.nparams) (fArgs.take source.nparams))
    (hindices : List.Forall₂ (after.IsDefEqU univs Γ)
      (fArgs.drop (source.nparams + certificate.generation.familyCount +
        certificate.generation.minorCount))
      (certificate.generation.ruleIndexTargets constructor m1 fArgs aArgs))
    {Frec Ae : VExpr}
    (hehead : after.HasType univs Γ
      (.const (certificate.generation.ruleRecName constructor) m1) Frec)
    (hespine : after.SpineWF univs Γ Frec
      (fArgs ++ [VExpr.appN (.const constructor.ctor.raw.name
        (certificate.generation.sourceLevels.map (VLevel.inst m1)))
        aArgs]) Ae)
    {Fctor Actor : VExpr}
    (hctorhead : after.HasType univs Γ
      (.const constructor.ctor.raw.name
        (certificate.generation.sourceLevels.map (VLevel.inst m1))) Fctor)
    (hctorspine : after.SpineWF univs Γ Fctor aArgs Actor)
    {B : VExpr}
    (hcaps : after.SpineWF univs Γ
      ((certificate.generation.rule i constructor).type.instL m1)
      (fArgs.take (source.nparams + certificate.generation.familyCount +
          certificate.generation.minorCount) ++
        aArgs.drop source.nparams) B) :
    after.IsDefEqU univs Γ
      (.app
        (VExpr.appN (.const
          (certificate.generation.ruleRecName constructor) m1) fArgs)
        (VExpr.appN (.const constructor.ctor.raw.name
          (certificate.generation.sourceLevels.map (VLevel.inst m1)))
          aArgs))
      (VExpr.appN
        ((certificate.generation.rule i constructor).rhs.instL m1)
        (certificate.generation.ruleCaptureValues constructor fArgs
          aArgs)) := by
  obtain ⟨m2, hm⟩ :=
    certificate.generation.rulePattern_matches_spines constructor m1
      (certificate.generation.sourceLevels.map (VLevel.inst m1))
      fArgs aArgs hMlen hNlen
  have hck := certificate.generation.ruleCheck_ok_of_spines hMlen hNlen hm
    hparams hindices certificate.ruleClosure
    (List.mem_of_getElem? facts.entry)
  have hred := certificate.ruleReduction facts hΓ hm1 hlen1
    hMlen hNlen hm hck hehead hespine hctorhead hctorspine hcaps
  rw [certificate.generation.ruleRHS_apply_eq_of_match hMlen hNlen hm
    certificate.ruleClosure facts.entry] at hred
  exact hred

/-- Unindexed specialization of `ruleReductionMatched`.  Once generation
shows that the selected constructor has no result indices, parameter
agreement is the complete semantic check at the runtime iota site. -/
theorem ruleReductionMatchedUnindexed
    (certificate : BlockCertificate source before after)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (facts : certificate.RecursorRuleFacts i constructor)
    (hidx : certificate.generation.ruleIdx constructor = [])
    {univs : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (after.IsType univs))
    {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs)
    (hlen1 : m1.length = certificate.generation.recUvars)
    {fArgs aArgs : List VExpr}
    (hMlen : fArgs.length =
      certificate.generation.ruleMajorArity constructor)
    (hNlen : aArgs.length =
      certificate.generation.ruleArgArity constructor)
    (hparams : List.Forall₂ (after.IsDefEqU univs Γ)
      (aArgs.take source.nparams) (fArgs.take source.nparams))
    {Frec Ae : VExpr}
    (hehead : after.HasType univs Γ
      (.const (certificate.generation.ruleRecName constructor) m1) Frec)
    (hespine : after.SpineWF univs Γ Frec
      (fArgs ++ [VExpr.appN (.const constructor.ctor.raw.name
        (certificate.generation.sourceLevels.map (VLevel.inst m1)))
        aArgs]) Ae)
    {Fctor Actor : VExpr}
    (hctorhead : after.HasType univs Γ
      (.const constructor.ctor.raw.name
        (certificate.generation.sourceLevels.map (VLevel.inst m1))) Fctor)
    (hctorspine : after.SpineWF univs Γ Fctor aArgs Actor)
    {B : VExpr}
    (hcaps : after.SpineWF univs Γ
      ((certificate.generation.rule i constructor).type.instL m1)
      (fArgs.take (source.nparams + certificate.generation.familyCount +
          certificate.generation.minorCount) ++
        aArgs.drop source.nparams) B) :
    after.IsDefEq univs Γ
      (.app
        (VExpr.appN (.const
          (certificate.generation.ruleRecName constructor) m1) fArgs)
        (VExpr.appN (.const constructor.ctor.raw.name
          (certificate.generation.sourceLevels.map (VLevel.inst m1)))
          aArgs))
      (VExpr.appN
        ((certificate.generation.rule i constructor).rhs.instL m1)
        (certificate.generation.ruleCaptureValues constructor fArgs
          aArgs)) B := by
  have hred := certificate.ruleReductionMatched facts hΓ hm1 hlen1 hMlen hNlen
    hparams
    (certificate.generation.ruleIndexTargets_aligned_of_unindexed hidx hMlen)
    hehead hespine hctorhead hctorspine hcaps
  have hrhsHead : after.HasType univs Γ
      ((certificate.generation.rule i constructor).rhs.instL m1)
      ((certificate.generation.rule i constructor).type.instL m1) :=
    (facts.wf.2.instL hm1).weak0 certificate.afterWF.ordered
  exact hred.of_r certificate.afterWF hΓ
    (hcaps.hasType_appN hrhsHead)

/-- Field-continuation form of `ruleReductionMatchedUnindexed`.  Once the
recursor head exposes the generated common telescope, the generic capture
assembler replays that prefix and appends the selected constructor fields;
callers no longer need to manufacture the complete rule spine themselves. -/
theorem ruleReductionMatchedUnindexedOfFieldContinuation
    (certificate : BlockCertificate source before after)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (facts : certificate.RecursorRuleFacts i constructor)
    (hidx : certificate.generation.ruleIdx constructor = [])
    {univs : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (after.IsType univs))
    {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs)
    (hlen1 : m1.length = certificate.generation.recUvars)
    {fArgs aArgs : List VExpr}
    (hMlen : fArgs.length =
      certificate.generation.ruleMajorArity constructor)
    (hNlen : aArgs.length =
      certificate.generation.ruleArgArity constructor)
    (hparams : List.Forall₂ (after.IsDefEqU univs Γ)
      (aArgs.take source.nparams) (fArgs.take source.nparams))
    {recResult Ae : VExpr}
    (hehead : after.HasType univs Γ
      (.const (certificate.generation.ruleRecName constructor) m1)
      (VExpr.forallN
        (certificate.generation.ruleCommonBinders.map (VExpr.instL m1))
        recResult))
    (hespine : after.SpineWF univs Γ
      (VExpr.forallN
        (certificate.generation.ruleCommonBinders.map (VExpr.instL m1))
        recResult)
      (fArgs ++ [VExpr.appN (.const constructor.ctor.raw.name
        (certificate.generation.sourceLevels.map (VLevel.inst m1)))
        aArgs]) Ae)
    {Fctor Actor : VExpr}
    (hctorhead : after.HasType univs Γ
      (.const constructor.ctor.raw.name
        (certificate.generation.sourceLevels.map (VLevel.inst m1))) Fctor)
    (hctorspine : after.SpineWF univs Γ Fctor aArgs Actor)
    {B : VExpr}
    (hfields : after.SpineWF univs Γ
      (VExpr.instRev
        (VExpr.forallN
          ((certificate.generation.ruleFieldBinders constructor).map
            (VExpr.instL m1))
          ((certificate.generation.ruleResult constructor).instL m1))
        (fArgs.take (source.nparams +
          certificate.generation.familyCount +
          certificate.generation.minorCount)))
      (aArgs.drop source.nparams) B) :
    after.IsDefEq univs Γ
      (.app
        (VExpr.appN (.const
          (certificate.generation.ruleRecName constructor) m1) fArgs)
        (VExpr.appN (.const constructor.ctor.raw.name
          (certificate.generation.sourceLevels.map (VLevel.inst m1)))
          aArgs))
      (VExpr.appN
        ((certificate.generation.rule i constructor).rhs.instL m1)
        (certificate.generation.ruleCaptureValues constructor fArgs
          aArgs)) B := by
  have hcaps := certificate.generation.ruleCaptureSpine_of_prefix_fields
    i constructor m1 hMlen hespine hfields
  exact certificate.ruleReductionMatchedUnindexed facts hidx hΓ hm1 hlen1
    hMlen hNlen hparams hehead hespine hctorhead hctorspine hcaps

/-- Fully generated-head form of the unindexed field-continuation consumer.
The completed certificate supplies both constant typings, the two exact
spines expose the major's same-head family types, and the caller supplies the
inductive-head injectivity consequence that turns that equality into
parameter agreement. -/
theorem ruleReductionMatchedUnindexedOfMajorInjectivityAndFieldContinuation
    (certificate : BlockCertificate source before after)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (facts : certificate.RecursorRuleFacts i constructor)
    {family : NormalizedFamily}
    (owner : certificate.RuleOwnerFacts constructor family)
    (hidx : certificate.generation.ruleIdx constructor = [])
    {univs : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (after.IsType univs))
    {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs)
    (hlen1 : m1.length = certificate.generation.recUvars)
    {fArgs aArgs : List VExpr}
    (hMlen : fArgs.length =
      certificate.generation.ruleMajorArity constructor)
    (hNlen : aArgs.length =
      certificate.generation.ruleArgArity constructor)
    (hmajorInjective :
      after.IsDefEqU univs Γ
        (VExpr.appN (.const family.raw.name
          (certificate.generation.sourceLevels.map (VLevel.inst m1)))
          (aArgs.take source.nparams))
        (VExpr.appN (.const family.raw.name
          (certificate.generation.sourceLevels.map (VLevel.inst m1)))
          (fArgs.take source.nparams)) →
      List.Forall₂ (after.IsDefEqU univs Γ)
        (aArgs.take source.nparams) (fArgs.take source.nparams))
    {Ae Actor : VExpr}
    (hrecspine : after.SpineWF univs Γ
      ((certificate.generation.recType family).instL m1)
      (fArgs ++ [VExpr.appN (.const constructor.ctor.raw.name
        (certificate.generation.sourceLevels.map (VLevel.inst m1)))
        aArgs]) Ae)
    (hctorspine : after.SpineWF univs Γ
      (VExpr.forallN
        ((certificate.generation.paramsTel ++
          constructor.ctor.fieldsR source.uvars source.nparams
            certificate.generation.elimination).map (VExpr.instL m1))
        ((certificate.generation.ruleCtorType constructor).instL m1))
      aArgs Actor)
    {B : VExpr}
    (hfields : after.SpineWF univs Γ
      (VExpr.instRev
        (VExpr.forallN
          ((certificate.generation.ruleFieldBinders constructor).map
            (VExpr.instL m1))
          ((certificate.generation.ruleResult constructor).instL m1))
        (fArgs.take (source.nparams +
          certificate.generation.familyCount +
          certificate.generation.minorCount)))
      (aArgs.drop source.nparams) B) :
    after.IsDefEq univs Γ
      (.app
        (VExpr.appN (.const
          (certificate.generation.ruleRecName constructor) m1) fArgs)
        (VExpr.appN (.const constructor.ctor.raw.name
          (certificate.generation.sourceLevels.map (VLevel.inst m1)))
          aArgs))
      (VExpr.appN
        ((certificate.generation.rule i constructor).rhs.instL m1)
        (certificate.generation.ruleCaptureValues constructor fArgs
          aArgs)) B := by
  have hparams :=
    certificate.ruleParameterAgreementUnindexedOfMajorInjectivity facts
      owner hidx hΓ hm1 hMlen hNlen hrecspine hctorspine hmajorInjective
  have hehead := certificate.ruleRecursorHeadHasType owner hm1 hlen1
    (Γ := Γ)
  have hctorhead := certificate.ruleConstructorHeadHasType facts owner hm1
    (Γ := Γ)
  rw [certificate.generation.recType_instL_common family m1] at hehead hrecspine
  exact certificate.ruleReductionMatchedUnindexedOfFieldContinuation facts
    hidx hΓ hm1 hlen1 hMlen hNlen hparams hehead hrecspine hctorhead
    hctorspine hfields

/-- A saturated generated rule left-hand side β-collapses to its instantiated
generated body.  This exposes the flat body/redex equality that can be
transported through a nested constant interpretation independently of the
registered RHS. -/
theorem ruleLhsApplied
    (certificate : BlockCertificate source before after)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (facts : certificate.RecursorRuleFacts i constructor)
    {univs : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (after.IsType univs))
    {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs)
    {captures : List VExpr} {B : VExpr}
    (hcaps : after.SpineWF univs Γ
      ((certificate.generation.rule i constructor).type.instL m1)
      captures B)
    (hcapsLen : captures.length =
      (certificate.generation.ruleBinders constructor).length) :
    after.IsDefEqU univs Γ
      (VExpr.appN
        ((certificate.generation.rule i constructor).lhs.instL m1)
        captures)
      (VExpr.instRev
        ((certificate.generation.ruleLhsBody constructor).instL m1)
        captures) := by
  let gen := certificate.generation
  let binders := (gen.ruleBinders constructor).map (VExpr.instL m1)
  let lhsBody := (gen.ruleLhsBody constructor).instL m1
  let typeBody := (gen.ruleResult constructor).instL m1
  have hlhsShape : (gen.rule i constructor).lhs.instL m1 =
      VExpr.lamN binders lhsBody := by
    rw [gen.rule_lhs, VExpr.instL_lamN]
  have htypeShape : (gen.rule i constructor).type.instL m1 =
      VExpr.forallN binders typeBody := by
    rw [gen.rule_type, VExpr.instL_forallN]
    rfl
  have hlhsT : after.HasType univs Γ (VExpr.lamN binders lhsBody)
      ((gen.rule i constructor).type.instL m1) := by
    rw [← hlhsShape]
    exact (facts.wf.1.instL hm1).weak0 certificate.afterWF.ordered
  obtain ⟨hTel, T₀, hbody⟩ := VEnv.HasType.lamN_wf
    certificate.afterWF.ordered hΓ hlhsT
  rw [htypeShape] at hcaps
  have hlen : captures.length = binders.length := by
    simpa [binders] using hcapsLen
  have hretT₀ := hcaps.retarget hlen T₀
  have hcollapse := VEnv.IsDefEq.appN_lamN certificate.afterWF.ordered
    hTel hbody hretT₀ hlen
  rw [hlhsShape]
  change after.IsDefEqU univs Γ
    (VExpr.appN (VExpr.lamN binders lhsBody) captures)
    (VExpr.instRev lhsBody captures)
  exact ⟨_, hcollapse⟩

/-- Recover the generated body's equality to a matched redex from an exact
certificate reduction.  The registered rule joins the β-collapsed LHS to the
same RHS application, exposing a transportable body/redex equality without
replaying the internal pattern-check calculation. -/
theorem ruleLhsBodyMatchedOfReduction
    (certificate : BlockCertificate source before after)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (facts : certificate.RecursorRuleFacts i constructor)
    {univs : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (after.IsType univs))
    {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs)
    (hlen1 : m1.length = certificate.generation.recUvars)
    {captures : List VExpr} {B redex : VExpr}
    (hcaps : after.SpineWF univs Γ
      ((certificate.generation.rule i constructor).type.instL m1)
      captures B)
    (hcapsLen : captures.length =
      (certificate.generation.ruleBinders constructor).length)
    (hreduction : after.IsDefEq univs Γ redex
      (VExpr.appN ((certificate.generation.rule i constructor).rhs.instL m1)
        captures) B) :
    after.IsDefEq univs Γ
      (VExpr.instRev
        ((certificate.generation.ruleLhsBody constructor).instL m1)
        captures)
      redex B := by
  have hlhs := certificate.ruleLhsApplied facts hΓ hm1 hcaps hcapsLen
  have hlhsHead : after.HasType univs Γ
      ((certificate.generation.rule i constructor).lhs.instL m1)
      ((certificate.generation.rule i constructor).type.instL m1) :=
    (facts.wf.1.instL hm1).weak0 certificate.afterWF.ordered
  have hlhsApp := hcaps.hasType_appN hlhsHead
  have hlhsB := hlhs.of_l certificate.afterWF hΓ hlhsApp
  have hlenRule : m1.length =
      (certificate.generation.rule i constructor).uvars := by
    simpa using hlen1.trans
      (certificate.generation.rule_uvars i constructor).symm
  have hregistered := VEnv.IsDefEq.appN_congr
    (.extra facts.registered hm1 hlenRule) hcaps
  exact hlhsB.symm.trans (hregistered.trans hreduction.symm)

/-- One-parameter generated-head typing also retains the complete canonical
capture spine.  This is the transport-facing half of the reduction consumer:
the same parameter injectivity and runtime spines that justify iota
reduction type every captured argument against the generated rule tower. -/
theorem ruleCaptureSpineUnindexedOfMajorInjectivityOneParam
    (certificate : BlockCertificate source before after)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (facts : certificate.RecursorRuleFacts i constructor)
    {family : NormalizedFamily}
    (owner : certificate.RuleOwnerFacts constructor family)
    (hidx : certificate.generation.ruleIdx constructor = [])
    (hone : source.nparams = 1)
    {univs : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (after.IsType univs))
    {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs)
    {fArgs aArgs : List VExpr}
    (hMlen : fArgs.length =
      certificate.generation.ruleMajorArity constructor)
    (hNlen : aArgs.length =
      certificate.generation.ruleArgArity constructor)
    (hmajorInjective :
      after.IsDefEqU univs Γ
        (VExpr.appN (.const family.raw.name
          (certificate.generation.sourceLevels.map (VLevel.inst m1)))
          (aArgs.take source.nparams))
        (VExpr.appN (.const family.raw.name
          (certificate.generation.sourceLevels.map (VLevel.inst m1)))
          (fArgs.take source.nparams)) →
      List.Forall₂ (after.IsDefEqU univs Γ)
        (aArgs.take source.nparams) (fArgs.take source.nparams))
    {Ae Actor : VExpr}
    (hrecspine : after.SpineWF univs Γ
      ((certificate.generation.recType family).instL m1)
      (fArgs ++ [VExpr.appN (.const constructor.ctor.raw.name
        (certificate.generation.sourceLevels.map (VLevel.inst m1)))
        aArgs]) Ae)
    (hctorspine : after.SpineWF univs Γ
      (VExpr.forallN
        ((certificate.generation.paramsTel ++
          constructor.ctor.fieldsR source.uvars source.nparams
            certificate.generation.elimination).map (VExpr.instL m1))
        ((certificate.generation.ruleCtorType constructor).instL m1))
      aArgs Actor) :
    ∃ B, after.SpineWF univs Γ
      ((certificate.generation.rule i constructor).type.instL m1)
      (certificate.generation.ruleCaptureValues constructor fArgs aArgs) B := by
  have hparams :=
    certificate.ruleParameterAgreementUnindexedOfMajorInjectivity facts
      owner hidx hΓ hm1 hMlen hNlen hrecspine hctorspine hmajorInjective
  obtain ⟨B, hfields⟩ := certificate.ruleFieldSpineOneParam facts hone hidx
    hΓ hm1 hMlen hNlen hparams hctorspine
  have hrecspine' := hrecspine
  rw [certificate.generation.recType_instL_common family m1] at hrecspine'
  exact ⟨B, certificate.generation.ruleCaptureSpine_of_prefix_fields
    i constructor m1 hMlen hrecspine' hfields⟩

/-- One-parameter specialization of the generated-head consumer.  Parameter
agreement obtained from inductive-head injectivity now transports the whole
dependent field telescope, eliminating the separate field-continuation
premise. -/
theorem ruleReductionMatchedUnindexedOfMajorInjectivityOneParam
    (certificate : BlockCertificate source before after)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (facts : certificate.RecursorRuleFacts i constructor)
    {family : NormalizedFamily}
    (owner : certificate.RuleOwnerFacts constructor family)
    (hidx : certificate.generation.ruleIdx constructor = [])
    (hone : source.nparams = 1)
    {univs : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (after.IsType univs))
    {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs)
    (hlen1 : m1.length = certificate.generation.recUvars)
    {fArgs aArgs : List VExpr}
    (hMlen : fArgs.length =
      certificate.generation.ruleMajorArity constructor)
    (hNlen : aArgs.length =
      certificate.generation.ruleArgArity constructor)
    (hmajorInjective :
      after.IsDefEqU univs Γ
        (VExpr.appN (.const family.raw.name
          (certificate.generation.sourceLevels.map (VLevel.inst m1)))
          (aArgs.take source.nparams))
        (VExpr.appN (.const family.raw.name
          (certificate.generation.sourceLevels.map (VLevel.inst m1)))
          (fArgs.take source.nparams)) →
      List.Forall₂ (after.IsDefEqU univs Γ)
        (aArgs.take source.nparams) (fArgs.take source.nparams))
    {Ae Actor : VExpr}
    (hrecspine : after.SpineWF univs Γ
      ((certificate.generation.recType family).instL m1)
      (fArgs ++ [VExpr.appN (.const constructor.ctor.raw.name
        (certificate.generation.sourceLevels.map (VLevel.inst m1)))
        aArgs]) Ae)
    (hctorspine : after.SpineWF univs Γ
      (VExpr.forallN
        ((certificate.generation.paramsTel ++
          constructor.ctor.fieldsR source.uvars source.nparams
            certificate.generation.elimination).map (VExpr.instL m1))
        ((certificate.generation.ruleCtorType constructor).instL m1))
      aArgs Actor) :
    ∃ B, after.IsDefEq univs Γ
      (.app
        (VExpr.appN (.const
          (certificate.generation.ruleRecName constructor) m1) fArgs)
        (VExpr.appN (.const constructor.ctor.raw.name
          (certificate.generation.sourceLevels.map (VLevel.inst m1)))
          aArgs))
      (VExpr.appN
        ((certificate.generation.rule i constructor).rhs.instL m1)
        (certificate.generation.ruleCaptureValues constructor fArgs
          aArgs)) B := by
  have hparams :=
    certificate.ruleParameterAgreementUnindexedOfMajorInjectivity facts
      owner hidx hΓ hm1 hMlen hNlen hrecspine hctorspine hmajorInjective
  obtain ⟨B, hfields⟩ := certificate.ruleFieldSpineOneParam facts hone hidx
    hΓ hm1 hMlen hNlen hparams hctorspine
  exact ⟨B,
    certificate
      |>.ruleReductionMatchedUnindexedOfMajorInjectivityAndFieldContinuation
        facts owner hidx hΓ hm1 hlen1 hMlen hNlen hmajorInjective
        hrecspine hctorspine hfields⟩

/-- Zero-field specialization of the generated-head consumer.  For such a
constructor the field continuation is reflexive, so inductive-head
injectivity is the only remaining semantic premise at the iota site. -/
theorem ruleReductionMatchedUnindexedOfMajorInjectivityNoFields
    (certificate : BlockCertificate source before after)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (facts : certificate.RecursorRuleFacts i constructor)
    {family : NormalizedFamily}
    (owner : certificate.RuleOwnerFacts constructor family)
    (hidx : certificate.generation.ruleIdx constructor = [])
    (hzero : certificate.generation.ruleFieldCount constructor = 0)
    {univs : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (after.IsType univs))
    {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs)
    (hlen1 : m1.length = certificate.generation.recUvars)
    {fArgs aArgs : List VExpr}
    (hMlen : fArgs.length =
      certificate.generation.ruleMajorArity constructor)
    (hNlen : aArgs.length =
      certificate.generation.ruleArgArity constructor)
    (hmajorInjective :
      after.IsDefEqU univs Γ
        (VExpr.appN (.const family.raw.name
          (certificate.generation.sourceLevels.map (VLevel.inst m1)))
          (aArgs.take source.nparams))
        (VExpr.appN (.const family.raw.name
          (certificate.generation.sourceLevels.map (VLevel.inst m1)))
          (fArgs.take source.nparams)) →
      List.Forall₂ (after.IsDefEqU univs Γ)
        (aArgs.take source.nparams) (fArgs.take source.nparams))
    {Ae Actor : VExpr}
    (hrecspine : after.SpineWF univs Γ
      ((certificate.generation.recType family).instL m1)
      (fArgs ++ [VExpr.appN (.const constructor.ctor.raw.name
        (certificate.generation.sourceLevels.map (VLevel.inst m1)))
        aArgs]) Ae)
    (hctorspine : after.SpineWF univs Γ
      (VExpr.forallN
        ((certificate.generation.paramsTel ++
          constructor.ctor.fieldsR source.uvars source.nparams
            certificate.generation.elimination).map (VExpr.instL m1))
        ((certificate.generation.ruleCtorType constructor).instL m1))
      aArgs Actor) :
    after.IsDefEq univs Γ
      (.app
        (VExpr.appN (.const
          (certificate.generation.ruleRecName constructor) m1) fArgs)
        (VExpr.appN (.const constructor.ctor.raw.name
          (certificate.generation.sourceLevels.map (VLevel.inst m1)))
          aArgs))
      (VExpr.appN
        ((certificate.generation.rule i constructor).rhs.instL m1)
        (certificate.generation.ruleCaptureValues constructor fArgs
          aArgs))
      (VExpr.instRev
        (VExpr.forallN
          ((certificate.generation.ruleFieldBinders constructor).map
            (VExpr.instL m1))
          ((certificate.generation.ruleResult constructor).instL m1))
        (fArgs.take (source.nparams +
          certificate.generation.familyCount +
          certificate.generation.minorCount))) := by
  exact certificate
    |>.ruleReductionMatchedUnindexedOfMajorInjectivityAndFieldContinuation
      facts owner hidx hΓ hm1 hlen1 hMlen hNlen hmajorInjective
      hrecspine hctorspine
      (certificate.generation.ruleFieldSpine_of_no_fields constructor hzero
        hNlen)

end BlockCertificate

namespace NestedStagedCertificate

variable {source : VInductDecl} {before flatAfter after : VEnv}

/-- The exact flattened half of a nested certificate inherits the ordinary
rule-reduction consumer.  The original and flattened declarations can have
different dependent types, so the capture spine names the flattened source's
parameter count explicitly. -/
theorem flatRuleReduction
    (certificate : NestedStagedCertificate source before flatAfter after)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (facts : certificate.RecursorRuleFacts i constructor)
    {univs : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (flatAfter.IsType univs))
    {m1 : List VLevel} {m2}
    (hm1 : ∀ l ∈ m1, l.WF univs)
    (hlen1 : m1.length =
      certificate.restored.nested.generation.recUvars)
    {fArgs aArgs : List VExpr}
    (hMlen : fArgs.length =
      certificate.restored.nested.generation.ruleMajorArity constructor)
    (hNlen : aArgs.length =
      certificate.restored.nested.generation.ruleArgArity constructor)
    (hm :
      ((certificate.restored.nested.generation.rulePattern
        constructor).toPattern).Matches
      (.app
        (VExpr.appN (.const
          (certificate.restored.nested.generation.ruleRecName constructor) m1)
          fArgs)
        (VExpr.appN (.const constructor.ctor.raw.name
          (certificate.restored.nested.generation.sourceLevels.map
            (VLevel.inst m1))) aArgs)) m1 m2)
    (hck : (certificate.restored.nested.generation.ruleCheck
      certificate.flatRuleClosure
      (List.mem_of_getElem? facts.flat.entry)).OK
        (flatAfter.IsDefEqU univs Γ) m1 m2)
    {Frec Ae : VExpr}
    (hehead : flatAfter.HasType univs Γ
      (.const
        (certificate.restored.nested.generation.ruleRecName constructor) m1)
      Frec)
    (hespine : flatAfter.SpineWF univs Γ Frec
      (fArgs ++ [VExpr.appN (.const constructor.ctor.raw.name
        (certificate.restored.nested.generation.sourceLevels.map
          (VLevel.inst m1))) aArgs]) Ae)
    {Fctor Actor : VExpr}
    (hctorhead : flatAfter.HasType univs Γ
      (.const constructor.ctor.raw.name
        (certificate.restored.nested.generation.sourceLevels.map
          (VLevel.inst m1))) Fctor)
    (hctorspine : flatAfter.SpineWF univs Γ Fctor aArgs Actor)
    {B : VExpr}
    (hcaps : flatAfter.SpineWF univs Γ
      ((certificate.restored.nested.generation.rule i constructor).type.instL
        m1)
      (fArgs.take (certificate.restored.nested.elim.flat.nparams +
          certificate.restored.nested.generation.familyCount +
          certificate.restored.nested.generation.minorCount) ++
        aArgs.drop certificate.restored.nested.elim.flat.nparams) B) :
    flatAfter.IsDefEqU univs Γ
      (.app
        (VExpr.appN (.const
          (certificate.restored.nested.generation.ruleRecName constructor) m1)
          fArgs)
        (VExpr.appN (.const constructor.ctor.raw.name
          (certificate.restored.nested.generation.sourceLevels.map
            (VLevel.inst m1))) aArgs))
      ((certificate.restored.nested.generation.ruleRHS
        certificate.flatRuleClosure facts.flat.entry).apply m1 m2) := by
  exact certificate.flatCertificate.ruleReduction facts.flat hΓ hm1 hlen1
    hMlen hNlen hm hck hehead hespine hctorhead hctorspine hcaps

/-- The nested staging analogue of `ruleReductionMatched`: structural
matching and folded checks are generated from the flattened runtime spines,
while the two semantic alignments and typing evidence remain explicit. -/
theorem flatRuleReductionMatched
    (certificate : NestedStagedCertificate source before flatAfter after)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (facts : certificate.RecursorRuleFacts i constructor)
    {univs : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (flatAfter.IsType univs))
    {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs)
    (hlen1 : m1.length =
      certificate.restored.nested.generation.recUvars)
    {fArgs aArgs : List VExpr}
    (hMlen : fArgs.length =
      certificate.restored.nested.generation.ruleMajorArity constructor)
    (hNlen : aArgs.length =
      certificate.restored.nested.generation.ruleArgArity constructor)
    (hparams : List.Forall₂ (flatAfter.IsDefEqU univs Γ)
      (aArgs.take certificate.restored.nested.elim.flat.nparams)
      (fArgs.take certificate.restored.nested.elim.flat.nparams))
    (hindices : List.Forall₂ (flatAfter.IsDefEqU univs Γ)
      (fArgs.drop (certificate.restored.nested.elim.flat.nparams +
        certificate.restored.nested.generation.familyCount +
        certificate.restored.nested.generation.minorCount))
      (certificate.restored.nested.generation.ruleIndexTargets constructor m1
        fArgs aArgs))
    {Frec Ae : VExpr}
    (hehead : flatAfter.HasType univs Γ
      (.const
        (certificate.restored.nested.generation.ruleRecName constructor) m1)
      Frec)
    (hespine : flatAfter.SpineWF univs Γ Frec
      (fArgs ++ [VExpr.appN (.const constructor.ctor.raw.name
        (certificate.restored.nested.generation.sourceLevels.map
          (VLevel.inst m1))) aArgs]) Ae)
    {Fctor Actor : VExpr}
    (hctorhead : flatAfter.HasType univs Γ
      (.const constructor.ctor.raw.name
        (certificate.restored.nested.generation.sourceLevels.map
          (VLevel.inst m1))) Fctor)
    (hctorspine : flatAfter.SpineWF univs Γ Fctor aArgs Actor)
    {B : VExpr}
    (hcaps : flatAfter.SpineWF univs Γ
      ((certificate.restored.nested.generation.rule i constructor).type.instL
        m1)
      (fArgs.take (certificate.restored.nested.elim.flat.nparams +
          certificate.restored.nested.generation.familyCount +
          certificate.restored.nested.generation.minorCount) ++
        aArgs.drop certificate.restored.nested.elim.flat.nparams) B) :
    flatAfter.IsDefEqU univs Γ
      (.app
        (VExpr.appN (.const
          (certificate.restored.nested.generation.ruleRecName constructor) m1)
          fArgs)
        (VExpr.appN (.const constructor.ctor.raw.name
          (certificate.restored.nested.generation.sourceLevels.map
            (VLevel.inst m1))) aArgs))
      (VExpr.appN
        ((certificate.restored.nested.generation.rule i constructor).rhs.instL
          m1)
        (certificate.restored.nested.generation.ruleCaptureValues constructor
          fArgs aArgs)) := by
  exact certificate.flatCertificate.ruleReductionMatched facts.flat hΓ hm1
    hlen1 hMlen hNlen hparams hindices hehead hespine hctorhead hctorspine
    hcaps

/-- The flattened nested specialization for unindexed rules.  This is the
exact consumer shape used by each selected RoseTree restoration rule: the
only remaining generated check is constructor/recursor parameter agreement. -/
theorem flatRuleReductionMatchedUnindexed
    (certificate : NestedStagedCertificate source before flatAfter after)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (facts : certificate.RecursorRuleFacts i constructor)
    (hidx : certificate.restored.nested.generation.ruleIdx constructor = [])
    {univs : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (flatAfter.IsType univs))
    {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs)
    (hlen1 : m1.length =
      certificate.restored.nested.generation.recUvars)
    {fArgs aArgs : List VExpr}
    (hMlen : fArgs.length =
      certificate.restored.nested.generation.ruleMajorArity constructor)
    (hNlen : aArgs.length =
      certificate.restored.nested.generation.ruleArgArity constructor)
    (hparams : List.Forall₂ (flatAfter.IsDefEqU univs Γ)
      (aArgs.take certificate.restored.nested.elim.flat.nparams)
      (fArgs.take certificate.restored.nested.elim.flat.nparams))
    {Frec Ae : VExpr}
    (hehead : flatAfter.HasType univs Γ
      (.const
        (certificate.restored.nested.generation.ruleRecName constructor) m1)
      Frec)
    (hespine : flatAfter.SpineWF univs Γ Frec
      (fArgs ++ [VExpr.appN (.const constructor.ctor.raw.name
        (certificate.restored.nested.generation.sourceLevels.map
          (VLevel.inst m1))) aArgs]) Ae)
    {Fctor Actor : VExpr}
    (hctorhead : flatAfter.HasType univs Γ
      (.const constructor.ctor.raw.name
        (certificate.restored.nested.generation.sourceLevels.map
          (VLevel.inst m1))) Fctor)
    (hctorspine : flatAfter.SpineWF univs Γ Fctor aArgs Actor)
    {B : VExpr}
    (hcaps : flatAfter.SpineWF univs Γ
      ((certificate.restored.nested.generation.rule i constructor).type.instL
        m1)
      (fArgs.take (certificate.restored.nested.elim.flat.nparams +
          certificate.restored.nested.generation.familyCount +
          certificate.restored.nested.generation.minorCount) ++
        aArgs.drop certificate.restored.nested.elim.flat.nparams) B) :
    flatAfter.IsDefEq univs Γ
      (.app
        (VExpr.appN (.const
          (certificate.restored.nested.generation.ruleRecName constructor) m1)
          fArgs)
        (VExpr.appN (.const constructor.ctor.raw.name
          (certificate.restored.nested.generation.sourceLevels.map
            (VLevel.inst m1))) aArgs))
      (VExpr.appN
        ((certificate.restored.nested.generation.rule i constructor).rhs.instL
          m1)
        (certificate.restored.nested.generation.ruleCaptureValues constructor
          fArgs aArgs)) B := by
  exact certificate.flatCertificate.ruleReductionMatchedUnindexed facts.flat
    hidx hΓ hm1 hlen1 hMlen hNlen hparams hehead hespine hctorhead
    hctorspine hcaps

/-- Nested-staging field-continuation form of the unindexed reduction
consumer.  The flattened certificate supplies the registered rule, while the
generic common/field assembler supplies its canonical capture spine. -/
theorem flatRuleReductionMatchedUnindexedOfFieldContinuation
    (certificate : NestedStagedCertificate source before flatAfter after)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (facts : certificate.RecursorRuleFacts i constructor)
    (hidx : certificate.restored.nested.generation.ruleIdx constructor = [])
    {univs : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (flatAfter.IsType univs))
    {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs)
    (hlen1 : m1.length =
      certificate.restored.nested.generation.recUvars)
    {fArgs aArgs : List VExpr}
    (hMlen : fArgs.length =
      certificate.restored.nested.generation.ruleMajorArity constructor)
    (hNlen : aArgs.length =
      certificate.restored.nested.generation.ruleArgArity constructor)
    (hparams : List.Forall₂ (flatAfter.IsDefEqU univs Γ)
      (aArgs.take certificate.restored.nested.elim.flat.nparams)
      (fArgs.take certificate.restored.nested.elim.flat.nparams))
    {recResult Ae : VExpr}
    (hehead : flatAfter.HasType univs Γ
      (.const
        (certificate.restored.nested.generation.ruleRecName constructor) m1)
      (VExpr.forallN
        (certificate.restored.nested.generation.ruleCommonBinders.map
          (VExpr.instL m1)) recResult))
    (hespine : flatAfter.SpineWF univs Γ
      (VExpr.forallN
        (certificate.restored.nested.generation.ruleCommonBinders.map
          (VExpr.instL m1)) recResult)
      (fArgs ++ [VExpr.appN (.const constructor.ctor.raw.name
        (certificate.restored.nested.generation.sourceLevels.map
          (VLevel.inst m1))) aArgs]) Ae)
    {Fctor Actor : VExpr}
    (hctorhead : flatAfter.HasType univs Γ
      (.const constructor.ctor.raw.name
        (certificate.restored.nested.generation.sourceLevels.map
          (VLevel.inst m1))) Fctor)
    (hctorspine : flatAfter.SpineWF univs Γ Fctor aArgs Actor)
    {B : VExpr}
    (hfields : flatAfter.SpineWF univs Γ
      (VExpr.instRev
        (VExpr.forallN
          ((certificate.restored.nested.generation.ruleFieldBinders
            constructor).map (VExpr.instL m1))
          ((certificate.restored.nested.generation.ruleResult
            constructor).instL m1))
        (fArgs.take
          (certificate.restored.nested.elim.flat.nparams +
            certificate.restored.nested.generation.familyCount +
            certificate.restored.nested.generation.minorCount)))
      (aArgs.drop certificate.restored.nested.elim.flat.nparams) B) :
    flatAfter.IsDefEq univs Γ
      (.app
        (VExpr.appN (.const
          (certificate.restored.nested.generation.ruleRecName constructor) m1)
          fArgs)
        (VExpr.appN (.const constructor.ctor.raw.name
          (certificate.restored.nested.generation.sourceLevels.map
            (VLevel.inst m1))) aArgs))
      (VExpr.appN
        ((certificate.restored.nested.generation.rule i constructor).rhs.instL
          m1)
        (certificate.restored.nested.generation.ruleCaptureValues constructor
          fArgs aArgs)) B := by
  exact certificate.flatCertificate
    |>.ruleReductionMatchedUnindexedOfFieldContinuation facts.flat hidx hΓ
      hm1 hlen1 hMlen hNlen hparams hehead hespine hctorhead hctorspine
      hfields

/-- Nested-staging specialization of the generated-head/injectivity
consumer.  It exposes exactly the flattened family-head injectivity and field
continuation premises needed before restored-rule transport. -/
theorem
    flatRuleReductionMatchedUnindexedOfMajorInjectivityAndFieldContinuation
    (certificate : NestedStagedCertificate source before flatAfter after)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (facts : certificate.RecursorRuleFacts i constructor)
    {family : NormalizedFamily}
    (owner : certificate.flatCertificate.RuleOwnerFacts constructor family)
    (hidx : certificate.restored.nested.generation.ruleIdx constructor = [])
    {univs : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (flatAfter.IsType univs))
    {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs)
    (hlen1 : m1.length =
      certificate.restored.nested.generation.recUvars)
    {fArgs aArgs : List VExpr}
    (hMlen : fArgs.length =
      certificate.restored.nested.generation.ruleMajorArity constructor)
    (hNlen : aArgs.length =
      certificate.restored.nested.generation.ruleArgArity constructor)
    (hmajorInjective :
      flatAfter.IsDefEqU univs Γ
        (VExpr.appN (.const family.raw.name
          (certificate.restored.nested.generation.sourceLevels.map
            (VLevel.inst m1)))
          (aArgs.take certificate.restored.nested.elim.flat.nparams))
        (VExpr.appN (.const family.raw.name
          (certificate.restored.nested.generation.sourceLevels.map
            (VLevel.inst m1)))
          (fArgs.take certificate.restored.nested.elim.flat.nparams)) →
      List.Forall₂ (flatAfter.IsDefEqU univs Γ)
        (aArgs.take certificate.restored.nested.elim.flat.nparams)
        (fArgs.take certificate.restored.nested.elim.flat.nparams))
    {Ae Actor : VExpr}
    (hrecspine : flatAfter.SpineWF univs Γ
      ((certificate.restored.nested.generation.recType family).instL m1)
      (fArgs ++ [VExpr.appN (.const constructor.ctor.raw.name
        (certificate.restored.nested.generation.sourceLevels.map
          (VLevel.inst m1))) aArgs]) Ae)
    (hctorspine : flatAfter.SpineWF univs Γ
      (VExpr.forallN
        ((certificate.restored.nested.generation.paramsTel ++
          constructor.ctor.fieldsR
            certificate.restored.nested.elim.flat.uvars
            certificate.restored.nested.elim.flat.nparams
            certificate.restored.nested.generation.elimination).map
              (VExpr.instL m1))
        ((certificate.restored.nested.generation.ruleCtorType
          constructor).instL m1))
      aArgs Actor)
    {B : VExpr}
    (hfields : flatAfter.SpineWF univs Γ
      (VExpr.instRev
        (VExpr.forallN
          ((certificate.restored.nested.generation.ruleFieldBinders
            constructor).map (VExpr.instL m1))
          ((certificate.restored.nested.generation.ruleResult
            constructor).instL m1))
        (fArgs.take
          (certificate.restored.nested.elim.flat.nparams +
            certificate.restored.nested.generation.familyCount +
            certificate.restored.nested.generation.minorCount)))
      (aArgs.drop certificate.restored.nested.elim.flat.nparams) B) :
    flatAfter.IsDefEq univs Γ
      (.app
        (VExpr.appN (.const
          (certificate.restored.nested.generation.ruleRecName constructor) m1)
          fArgs)
        (VExpr.appN (.const constructor.ctor.raw.name
          (certificate.restored.nested.generation.sourceLevels.map
            (VLevel.inst m1))) aArgs))
      (VExpr.appN
        ((certificate.restored.nested.generation.rule i constructor).rhs.instL
          m1)
        (certificate.restored.nested.generation.ruleCaptureValues constructor
          fArgs aArgs)) B := by
  exact certificate.flatCertificate
    |>.ruleReductionMatchedUnindexedOfMajorInjectivityAndFieldContinuation
      facts.flat owner hidx hΓ hm1 hlen1 hMlen hNlen hmajorInjective
      hrecspine hctorspine hfields

/-- The staged nested wrapper retains the flattened canonical capture spine
needed by σ̂/restoration transport. -/
theorem flatRuleCaptureSpineUnindexedOfMajorInjectivityOneParam
    (certificate : NestedStagedCertificate source before flatAfter after)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (facts : certificate.RecursorRuleFacts i constructor)
    {family : NormalizedFamily}
    (owner : certificate.flatCertificate.RuleOwnerFacts constructor family)
    (hidx : certificate.restored.nested.generation.ruleIdx constructor = [])
    (hone : certificate.restored.nested.elim.flat.nparams = 1)
    {univs : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (flatAfter.IsType univs))
    {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs)
    {fArgs aArgs : List VExpr}
    (hMlen : fArgs.length =
      certificate.restored.nested.generation.ruleMajorArity constructor)
    (hNlen : aArgs.length =
      certificate.restored.nested.generation.ruleArgArity constructor)
    (hmajorInjective :
      flatAfter.IsDefEqU univs Γ
        (VExpr.appN (.const family.raw.name
          (certificate.restored.nested.generation.sourceLevels.map
            (VLevel.inst m1)))
          (aArgs.take certificate.restored.nested.elim.flat.nparams))
        (VExpr.appN (.const family.raw.name
          (certificate.restored.nested.generation.sourceLevels.map
            (VLevel.inst m1)))
          (fArgs.take certificate.restored.nested.elim.flat.nparams)) →
      List.Forall₂ (flatAfter.IsDefEqU univs Γ)
        (aArgs.take certificate.restored.nested.elim.flat.nparams)
        (fArgs.take certificate.restored.nested.elim.flat.nparams))
    {Ae Actor : VExpr}
    (hrecspine : flatAfter.SpineWF univs Γ
      ((certificate.restored.nested.generation.recType family).instL m1)
      (fArgs ++ [VExpr.appN (.const constructor.ctor.raw.name
        (certificate.restored.nested.generation.sourceLevels.map
          (VLevel.inst m1))) aArgs]) Ae)
    (hctorspine : flatAfter.SpineWF univs Γ
      (VExpr.forallN
        ((certificate.restored.nested.generation.paramsTel ++
          constructor.ctor.fieldsR
            certificate.restored.nested.elim.flat.uvars
            certificate.restored.nested.elim.flat.nparams
            certificate.restored.nested.generation.elimination).map
              (VExpr.instL m1))
        ((certificate.restored.nested.generation.ruleCtorType
          constructor).instL m1))
      aArgs Actor) :
    ∃ B, flatAfter.SpineWF univs Γ
      ((certificate.restored.nested.generation.rule i constructor).type.instL
        m1)
      (certificate.restored.nested.generation.ruleCaptureValues constructor
        fArgs aArgs) B := by
  exact certificate.flatCertificate
    |>.ruleCaptureSpineUnindexedOfMajorInjectivityOneParam facts.flat owner
      hidx hone hΓ hm1 hMlen hNlen hmajorInjective hrecspine hctorspine

/-- Nested-staging one-parameter specialization.  For flattened declarations
such as RoseTree/List, the certificate-derived parameter agreement transports
every dependent constructor field and leaves only inductive-head injectivity
plus the exact runtime spines. -/
theorem flatRuleReductionMatchedUnindexedOfMajorInjectivityOneParam
    (certificate : NestedStagedCertificate source before flatAfter after)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (facts : certificate.RecursorRuleFacts i constructor)
    {family : NormalizedFamily}
    (owner : certificate.flatCertificate.RuleOwnerFacts constructor family)
    (hidx : certificate.restored.nested.generation.ruleIdx constructor = [])
    (hone : certificate.restored.nested.elim.flat.nparams = 1)
    {univs : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (flatAfter.IsType univs))
    {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs)
    (hlen1 : m1.length =
      certificate.restored.nested.generation.recUvars)
    {fArgs aArgs : List VExpr}
    (hMlen : fArgs.length =
      certificate.restored.nested.generation.ruleMajorArity constructor)
    (hNlen : aArgs.length =
      certificate.restored.nested.generation.ruleArgArity constructor)
    (hmajorInjective :
      flatAfter.IsDefEqU univs Γ
        (VExpr.appN (.const family.raw.name
          (certificate.restored.nested.generation.sourceLevels.map
            (VLevel.inst m1)))
          (aArgs.take certificate.restored.nested.elim.flat.nparams))
        (VExpr.appN (.const family.raw.name
          (certificate.restored.nested.generation.sourceLevels.map
            (VLevel.inst m1)))
          (fArgs.take certificate.restored.nested.elim.flat.nparams)) →
      List.Forall₂ (flatAfter.IsDefEqU univs Γ)
        (aArgs.take certificate.restored.nested.elim.flat.nparams)
        (fArgs.take certificate.restored.nested.elim.flat.nparams))
    {Ae Actor : VExpr}
    (hrecspine : flatAfter.SpineWF univs Γ
      ((certificate.restored.nested.generation.recType family).instL m1)
      (fArgs ++ [VExpr.appN (.const constructor.ctor.raw.name
        (certificate.restored.nested.generation.sourceLevels.map
          (VLevel.inst m1))) aArgs]) Ae)
    (hctorspine : flatAfter.SpineWF univs Γ
      (VExpr.forallN
        ((certificate.restored.nested.generation.paramsTel ++
          constructor.ctor.fieldsR
            certificate.restored.nested.elim.flat.uvars
            certificate.restored.nested.elim.flat.nparams
            certificate.restored.nested.generation.elimination).map
              (VExpr.instL m1))
        ((certificate.restored.nested.generation.ruleCtorType
          constructor).instL m1))
      aArgs Actor) :
    ∃ B, flatAfter.IsDefEq univs Γ
      (.app
        (VExpr.appN (.const
          (certificate.restored.nested.generation.ruleRecName constructor) m1)
          fArgs)
        (VExpr.appN (.const constructor.ctor.raw.name
          (certificate.restored.nested.generation.sourceLevels.map
            (VLevel.inst m1))) aArgs))
      (VExpr.appN
        ((certificate.restored.nested.generation.rule i constructor).rhs.instL
          m1)
        (certificate.restored.nested.generation.ruleCaptureValues constructor
          fArgs aArgs)) B := by
  exact certificate.flatCertificate
    |>.ruleReductionMatchedUnindexedOfMajorInjectivityOneParam facts.flat
      owner hidx hone hΓ hm1 hlen1 hMlen hNlen hmajorInjective
      hrecspine hctorspine

/-- Transport-facing body form of the selected one-parameter flattened
reduction.  It joins the certificate-produced reduction with the registered
generated rule and β-collapsed LHS, yielding the exact generated body/redex
equality that `ConstInterp` can map into the final environment. -/
theorem flatRuleCaptureAndLhsBodyMatchedUnindexedOfMajorInjectivityOneParam
    (certificate : NestedStagedCertificate source before flatAfter after)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (facts : certificate.RecursorRuleFacts i constructor)
    {family : NormalizedFamily}
    (owner : certificate.flatCertificate.RuleOwnerFacts constructor family)
    (hidx : certificate.restored.nested.generation.ruleIdx constructor = [])
    (hone : certificate.restored.nested.elim.flat.nparams = 1)
    {univs : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (flatAfter.IsType univs))
    {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs)
    (hlen1 : m1.length =
      certificate.restored.nested.generation.recUvars)
    {fArgs aArgs : List VExpr}
    (hMlen : fArgs.length =
      certificate.restored.nested.generation.ruleMajorArity constructor)
    (hNlen : aArgs.length =
      certificate.restored.nested.generation.ruleArgArity constructor)
    (hmajorInjective :
      flatAfter.IsDefEqU univs Γ
        (VExpr.appN (.const family.raw.name
          (certificate.restored.nested.generation.sourceLevels.map
            (VLevel.inst m1)))
          (aArgs.take certificate.restored.nested.elim.flat.nparams))
        (VExpr.appN (.const family.raw.name
          (certificate.restored.nested.generation.sourceLevels.map
            (VLevel.inst m1)))
          (fArgs.take certificate.restored.nested.elim.flat.nparams)) →
      List.Forall₂ (flatAfter.IsDefEqU univs Γ)
        (aArgs.take certificate.restored.nested.elim.flat.nparams)
        (fArgs.take certificate.restored.nested.elim.flat.nparams))
    {Ae Actor : VExpr}
    (hrecspine : flatAfter.SpineWF univs Γ
      ((certificate.restored.nested.generation.recType family).instL m1)
      (fArgs ++ [VExpr.appN (.const constructor.ctor.raw.name
        (certificate.restored.nested.generation.sourceLevels.map
          (VLevel.inst m1))) aArgs]) Ae)
    (hctorspine : flatAfter.SpineWF univs Γ
      (VExpr.forallN
        ((certificate.restored.nested.generation.paramsTel ++
          constructor.ctor.fieldsR
            certificate.restored.nested.elim.flat.uvars
            certificate.restored.nested.elim.flat.nparams
            certificate.restored.nested.generation.elimination).map
              (VExpr.instL m1))
        ((certificate.restored.nested.generation.ruleCtorType
          constructor).instL m1))
      aArgs Actor) :
    ∃ B, flatAfter.SpineWF univs Γ
        ((certificate.restored.nested.generation.rule i constructor).type.instL
          m1)
        (certificate.restored.nested.generation.ruleCaptureValues constructor
          fArgs aArgs) B ∧
      flatAfter.IsDefEq univs Γ
      (VExpr.instRev
        ((certificate.restored.nested.generation.ruleLhsBody
          constructor).instL m1)
        (certificate.restored.nested.generation.ruleCaptureValues constructor
          fArgs aArgs))
      (.app
        (VExpr.appN (.const
          (certificate.restored.nested.generation.ruleRecName constructor) m1)
          fArgs)
        (VExpr.appN (.const constructor.ctor.raw.name
          (certificate.restored.nested.generation.sourceLevels.map
            (VLevel.inst m1))) aArgs)) B := by
  let gen := certificate.restored.nested.generation
  obtain ⟨B, hcaps⟩ :=
    certificate.flatRuleCaptureSpineUnindexedOfMajorInjectivityOneParam
      facts owner hidx hone hΓ hm1 hMlen hNlen hmajorInjective
      hrecspine hctorspine
  obtain ⟨B', hred⟩ :=
    certificate.flatRuleReductionMatchedUnindexedOfMajorInjectivityOneParam
      facts owner hidx hone hΓ hm1 hlen1 hMlen hNlen hmajorInjective
      hrecspine hctorspine
  have hrhsHead : flatAfter.HasType univs Γ
      ((gen.rule i constructor).rhs.instL m1)
      ((gen.rule i constructor).type.instL m1) :=
    (facts.flat.wf.2.instL hm1).weak0 certificate.flatAfterWF.ordered
  have hredB : flatAfter.IsDefEq univs Γ
      (.app
        (VExpr.appN (.const (gen.ruleRecName constructor) m1) fArgs)
        (VExpr.appN (.const constructor.ctor.raw.name
          (gen.sourceLevels.map (VLevel.inst m1))) aArgs))
      (VExpr.appN ((gen.rule i constructor).rhs.instL m1)
        (gen.ruleCaptureValues constructor fArgs aArgs)) B :=
    (show flatAfter.IsDefEqU univs Γ _ _ from ⟨B', hred⟩).of_r
      certificate.flatAfterWF hΓ (hcaps.hasType_appN hrhsHead)
  refine ⟨B, hcaps, ?_⟩
  exact certificate.flatCertificate.ruleLhsBodyMatchedOfReduction facts.flat
    hΓ hm1 hlen1 hcaps
    (gen.ruleCaptureValues_length constructor hMlen hNlen) hredB

/-- Compatibility projection of the joint capture/body certificate.  The
stronger theorem above keeps the capture spine available for subsequent
constant-interpretation transport; callers needing only the body match retain
the former interface. -/
theorem flatRuleLhsBodyMatchedUnindexedOfMajorInjectivityOneParam
    (certificate : NestedStagedCertificate source before flatAfter after)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (facts : certificate.RecursorRuleFacts i constructor)
    {family : NormalizedFamily}
    (owner : certificate.flatCertificate.RuleOwnerFacts constructor family)
    (hidx : certificate.restored.nested.generation.ruleIdx constructor = [])
    (hone : certificate.restored.nested.elim.flat.nparams = 1)
    {univs : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (flatAfter.IsType univs))
    {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs)
    (hlen1 : m1.length =
      certificate.restored.nested.generation.recUvars)
    {fArgs aArgs : List VExpr}
    (hMlen : fArgs.length =
      certificate.restored.nested.generation.ruleMajorArity constructor)
    (hNlen : aArgs.length =
      certificate.restored.nested.generation.ruleArgArity constructor)
    (hmajorInjective :
      flatAfter.IsDefEqU univs Γ
        (VExpr.appN (.const family.raw.name
          (certificate.restored.nested.generation.sourceLevels.map
            (VLevel.inst m1)))
          (aArgs.take certificate.restored.nested.elim.flat.nparams))
        (VExpr.appN (.const family.raw.name
          (certificate.restored.nested.generation.sourceLevels.map
            (VLevel.inst m1)))
          (fArgs.take certificate.restored.nested.elim.flat.nparams)) →
      List.Forall₂ (flatAfter.IsDefEqU univs Γ)
        (aArgs.take certificate.restored.nested.elim.flat.nparams)
        (fArgs.take certificate.restored.nested.elim.flat.nparams))
    {Ae Actor : VExpr}
    (hrecspine : flatAfter.SpineWF univs Γ
      ((certificate.restored.nested.generation.recType family).instL m1)
      (fArgs ++ [VExpr.appN (.const constructor.ctor.raw.name
        (certificate.restored.nested.generation.sourceLevels.map
          (VLevel.inst m1))) aArgs]) Ae)
    (hctorspine : flatAfter.SpineWF univs Γ
      (VExpr.forallN
        ((certificate.restored.nested.generation.paramsTel ++
          constructor.ctor.fieldsR
            certificate.restored.nested.elim.flat.uvars
            certificate.restored.nested.elim.flat.nparams
            certificate.restored.nested.generation.elimination).map
              (VExpr.instL m1))
        ((certificate.restored.nested.generation.ruleCtorType
          constructor).instL m1))
      aArgs Actor) :
    ∃ B, flatAfter.IsDefEq univs Γ
      (VExpr.instRev
        ((certificate.restored.nested.generation.ruleLhsBody
          constructor).instL m1)
        (certificate.restored.nested.generation.ruleCaptureValues constructor
          fArgs aArgs))
      (.app
        (VExpr.appN (.const
          (certificate.restored.nested.generation.ruleRecName constructor) m1)
          fArgs)
        (VExpr.appN (.const constructor.ctor.raw.name
          (certificate.restored.nested.generation.sourceLevels.map
            (VLevel.inst m1))) aArgs)) B := by
  obtain ⟨B, _, hbody⟩ :=
    certificate
      |>.flatRuleCaptureAndLhsBodyMatchedUnindexedOfMajorInjectivityOneParam
        facts owner hidx hone hΓ hm1 hlen1 hMlen hNlen hmajorInjective
        hrecspine hctorspine
  exact ⟨B, hbody⟩

/-- Nested-staging zero-field specialization.  This is the exact flattened
consumer shape for constructors such as the selected `List.nil` rule. -/
theorem flatRuleReductionMatchedUnindexedOfMajorInjectivityNoFields
    (certificate : NestedStagedCertificate source before flatAfter after)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (facts : certificate.RecursorRuleFacts i constructor)
    {family : NormalizedFamily}
    (owner : certificate.flatCertificate.RuleOwnerFacts constructor family)
    (hidx : certificate.restored.nested.generation.ruleIdx constructor = [])
    (hzero : certificate.restored.nested.generation.ruleFieldCount
      constructor = 0)
    {univs : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (flatAfter.IsType univs))
    {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs)
    (hlen1 : m1.length =
      certificate.restored.nested.generation.recUvars)
    {fArgs aArgs : List VExpr}
    (hMlen : fArgs.length =
      certificate.restored.nested.generation.ruleMajorArity constructor)
    (hNlen : aArgs.length =
      certificate.restored.nested.generation.ruleArgArity constructor)
    (hmajorInjective :
      flatAfter.IsDefEqU univs Γ
        (VExpr.appN (.const family.raw.name
          (certificate.restored.nested.generation.sourceLevels.map
            (VLevel.inst m1)))
          (aArgs.take certificate.restored.nested.elim.flat.nparams))
        (VExpr.appN (.const family.raw.name
          (certificate.restored.nested.generation.sourceLevels.map
            (VLevel.inst m1)))
          (fArgs.take certificate.restored.nested.elim.flat.nparams)) →
      List.Forall₂ (flatAfter.IsDefEqU univs Γ)
        (aArgs.take certificate.restored.nested.elim.flat.nparams)
        (fArgs.take certificate.restored.nested.elim.flat.nparams))
    {Ae Actor : VExpr}
    (hrecspine : flatAfter.SpineWF univs Γ
      ((certificate.restored.nested.generation.recType family).instL m1)
      (fArgs ++ [VExpr.appN (.const constructor.ctor.raw.name
        (certificate.restored.nested.generation.sourceLevels.map
          (VLevel.inst m1))) aArgs]) Ae)
    (hctorspine : flatAfter.SpineWF univs Γ
      (VExpr.forallN
        ((certificate.restored.nested.generation.paramsTel ++
          constructor.ctor.fieldsR
            certificate.restored.nested.elim.flat.uvars
            certificate.restored.nested.elim.flat.nparams
            certificate.restored.nested.generation.elimination).map
              (VExpr.instL m1))
        ((certificate.restored.nested.generation.ruleCtorType
          constructor).instL m1))
      aArgs Actor) :
    flatAfter.IsDefEq univs Γ
      (.app
        (VExpr.appN (.const
          (certificate.restored.nested.generation.ruleRecName constructor) m1)
          fArgs)
        (VExpr.appN (.const constructor.ctor.raw.name
          (certificate.restored.nested.generation.sourceLevels.map
            (VLevel.inst m1))) aArgs))
      (VExpr.appN
        ((certificate.restored.nested.generation.rule i constructor).rhs.instL
          m1)
        (certificate.restored.nested.generation.ruleCaptureValues constructor
          fArgs aArgs))
      (VExpr.instRev
        (VExpr.forallN
          ((certificate.restored.nested.generation.ruleFieldBinders
            constructor).map (VExpr.instL m1))
          ((certificate.restored.nested.generation.ruleResult
            constructor).instL m1))
        (fArgs.take
          (certificate.restored.nested.elim.flat.nparams +
            certificate.restored.nested.generation.familyCount +
            certificate.restored.nested.generation.minorCount))) := by
  exact certificate.flatCertificate
    |>.ruleReductionMatchedUnindexedOfMajorInjectivityNoFields facts.flat
      owner hidx hzero hΓ hm1 hlen1 hMlen hNlen hmajorInjective
      hrecspine hctorspine

/-- Transport a complete flattened rule capture spine through an explicit
constant interpretation and retarget it to the paired restored rule type.
All structural rule/telescope shapes come from the staged certificate; the
remaining restoration-specific premise is the whole-type alignment between
the restored rule and the σ̂ image. -/
theorem restoredRuleCaptureSpineOfConstInterp
    (certificate : NestedStagedCertificate source before flatAfter after)
    {i : Nat} {constructor : NormalizedBlockCtor}
    {interp : Name → Option VExpr}
    (hi : VEnv.ConstInterp flatAfter after interp)
    {univs : Nat} {Γ : List VExpr}
    (hΓflat : OnCtx Γ (flatAfter.IsType univs))
    (hΓ : OnCtx (Γ.map (VExpr.substConst interp)) (after.IsType univs))
    {m1 : List VLevel} {captures : List VExpr} {B : VExpr}
    (hcaps : flatAfter.SpineWF univs Γ
      ((certificate.restored.nested.generation.rule i constructor).type.instL
        m1) captures B)
    (hcapsLen : captures.length =
      (certificate.restored.nested.generation.ruleBinders constructor).length)
    (htype : after.IsDefEqU univs (Γ.map (VExpr.substConst interp))
      ((certificate.restored.nested.restoredRule i constructor).type.instL m1)
      (((certificate.restored.nested.generation.rule i constructor).type.instL
        m1).substConst interp)) :
    ∃ B', after.SpineWF univs (Γ.map (VExpr.substConst interp))
      ((certificate.restored.nested.restoredRule i constructor).type.instL m1)
      (captures.map (VExpr.substConst interp)) B' := by
  let gen := certificate.restored.nested.generation
  let body := VExpr.appN
    (.bvar (gen.familyCount - 1 - constructor.owner + gen.minorCount +
      gen.ruleFieldCount constructor))
    (gen.ruleIdx constructor ++ [gen.ruleCtorApp constructor])
  have hflatShape : (gen.rule i constructor).type.instL m1 =
      VExpr.forallN ((gen.ruleBinders constructor).map (VExpr.instL m1))
        (body.instL m1) := by
    rw [gen.rule_type, VExpr.instL_forallN]
  have hrestShape :
      (certificate.restored.nested.restoredRule i constructor).type.instL m1 =
        VExpr.forallN
          (((gen.ruleBinders constructor).map
            certificate.restored.nested.restoreRec).map (VExpr.instL m1))
          ((certificate.restored.nested.restoreRec body).instL m1) := by
    change (certificate.restored.nested.restoreRec
      (gen.rule i constructor).type).instL m1 = _
    rw [gen.rule_type]
    unfold NestedBlockChecked.restoreRec
    rw [VInductDecl.restoreExpr_forallN]
    rw [VExpr.instL_forallN]
  rw [hflatShape] at hcaps
  rw [hrestShape] at htype ⊢
  rw [hflatShape] at htype
  refine ⟨_, VEnv.SpineWF.substConst_forallN_of_defeq hi
    certificate.restored.afterWF hΓflat hΓ hcaps
    (by simpa using hcapsLen)
    (by simp) htype⟩

/-- Canonical-capture specialization of the σ̂ transport boundary.  Exact
runtime recursor/constructor arities discharge the rule-telescope length
premise automatically. -/
theorem restoredRuleCanonicalCaptureSpineOfConstInterp
    (certificate : NestedStagedCertificate source before flatAfter after)
    {i : Nat} {constructor : NormalizedBlockCtor}
    {interp : Name → Option VExpr}
    (hi : VEnv.ConstInterp flatAfter after interp)
    {univs : Nat} {Γ : List VExpr}
    (hΓflat : OnCtx Γ (flatAfter.IsType univs))
    (hΓ : OnCtx (Γ.map (VExpr.substConst interp)) (after.IsType univs))
    {m1 : List VLevel} {fArgs aArgs : List VExpr} {B : VExpr}
    (hMlen : fArgs.length =
      certificate.restored.nested.generation.ruleMajorArity constructor)
    (hNlen : aArgs.length =
      certificate.restored.nested.generation.ruleArgArity constructor)
    (hcaps : flatAfter.SpineWF univs Γ
      ((certificate.restored.nested.generation.rule i constructor).type.instL
        m1)
      (certificate.restored.nested.generation.ruleCaptureValues constructor
        fArgs aArgs) B)
    (htype : after.IsDefEqU univs (Γ.map (VExpr.substConst interp))
      ((certificate.restored.nested.restoredRule i constructor).type.instL m1)
      (((certificate.restored.nested.generation.rule i constructor).type.instL
        m1).substConst interp)) :
    ∃ B', after.SpineWF univs (Γ.map (VExpr.substConst interp))
      ((certificate.restored.nested.restoredRule i constructor).type.instL m1)
      (certificate.restored.nested.generation.ruleCaptureValues constructor
        (fArgs.map (VExpr.substConst interp))
        (aArgs.map (VExpr.substConst interp))) B' := by
  have hout := certificate.restoredRuleCaptureSpineOfConstInterp hi hΓflat
    hΓ hcaps (certificate.restored.nested.generation.ruleCaptureValues_length
      constructor hMlen hNlen) htype
  rw [certificate.restored.nested.generation.ruleCaptureValues_map] at hout
  exact hout

/-- End-to-end capture typing for a one-parameter staged nested rule.  The
flattened certificate constructs the canonical capture spine from the two
runtime spines and the NORM-owned head-injectivity consequence; σ̂ then
transports it to the paired restored rule. -/
theorem restoredRuleCanonicalCaptureSpineUnindexedOfMajorInjectivityOneParam
    (certificate : NestedStagedCertificate source before flatAfter after)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (facts : certificate.RecursorRuleFacts i constructor)
    {family : NormalizedFamily}
    (owner : certificate.flatCertificate.RuleOwnerFacts constructor family)
    (hidx : certificate.restored.nested.generation.ruleIdx constructor = [])
    (hone : certificate.restored.nested.elim.flat.nparams = 1)
    {interp : Name → Option VExpr}
    (hi : VEnv.ConstInterp flatAfter after interp)
    {univs : Nat} {Γ : List VExpr}
    (hΓflat : OnCtx Γ (flatAfter.IsType univs))
    (hΓrestored : OnCtx
      (Γ.map (VExpr.substConst interp)) (after.IsType univs))
    {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs)
    {fArgs aArgs : List VExpr}
    (hMlen : fArgs.length =
      certificate.restored.nested.generation.ruleMajorArity constructor)
    (hNlen : aArgs.length =
      certificate.restored.nested.generation.ruleArgArity constructor)
    (hmajorInjective :
      flatAfter.IsDefEqU univs Γ
        (VExpr.appN (.const family.raw.name
          (certificate.restored.nested.generation.sourceLevels.map
            (VLevel.inst m1)))
          (aArgs.take certificate.restored.nested.elim.flat.nparams))
        (VExpr.appN (.const family.raw.name
          (certificate.restored.nested.generation.sourceLevels.map
            (VLevel.inst m1)))
          (fArgs.take certificate.restored.nested.elim.flat.nparams)) →
      List.Forall₂ (flatAfter.IsDefEqU univs Γ)
        (aArgs.take certificate.restored.nested.elim.flat.nparams)
        (fArgs.take certificate.restored.nested.elim.flat.nparams))
    {Ae Actor : VExpr}
    (hrecspine : flatAfter.SpineWF univs Γ
      ((certificate.restored.nested.generation.recType family).instL m1)
      (fArgs ++ [VExpr.appN (.const constructor.ctor.raw.name
        (certificate.restored.nested.generation.sourceLevels.map
          (VLevel.inst m1))) aArgs]) Ae)
    (hctorspine : flatAfter.SpineWF univs Γ
      (VExpr.forallN
        ((certificate.restored.nested.generation.paramsTel ++
          constructor.ctor.fieldsR
            certificate.restored.nested.elim.flat.uvars
            certificate.restored.nested.elim.flat.nparams
            certificate.restored.nested.generation.elimination).map
              (VExpr.instL m1))
        ((certificate.restored.nested.generation.ruleCtorType
          constructor).instL m1))
      aArgs Actor)
    (htype : after.IsDefEqU univs
      (Γ.map (VExpr.substConst interp))
      ((certificate.restored.nested.restoredRule i constructor).type.instL m1)
      (((certificate.restored.nested.generation.rule i constructor).type.instL
        m1).substConst interp)) :
    ∃ B', after.SpineWF univs (Γ.map (VExpr.substConst interp))
      ((certificate.restored.nested.restoredRule i constructor).type.instL m1)
      (certificate.restored.nested.generation.ruleCaptureValues constructor
        (fArgs.map (VExpr.substConst interp))
        (aArgs.map (VExpr.substConst interp))) B' := by
  obtain ⟨B, hcaps⟩ :=
    certificate.flatRuleCaptureSpineUnindexedOfMajorInjectivityOneParam
      facts owner hidx hone hΓflat hm1 hMlen hNlen hmajorInjective
      hrecspine hctorspine
  exact certificate.restoredRuleCanonicalCaptureSpineOfConstInterp hi
    hΓflat hΓrestored hMlen hNlen hcaps htype

/-- Transport a certified flattened body/redex equality through σ̂ and join
it to the two local restoration alignments.  This makes the remaining nested
work explicit and orthogonal: align the restored generated body with its σ̂
image, and align the σ̂-image flat redex with the final runtime redex. -/
theorem restoredRuleBodyMatchedOfFlat
    (certificate : NestedStagedCertificate source before flatAfter after)
    {constructor : NormalizedBlockCtor}
    {interp : Name → Option VExpr}
    (hi : VEnv.ConstInterp flatAfter after interp)
    {univs : Nat} {Γ : List VExpr} {m1 : List VLevel}
    (hΓflat : OnCtx Γ (flatAfter.IsType univs))
    (hΓ : OnCtx
      (Γ.map (VExpr.substConst interp)) (after.IsType univs))
    {captures : List VExpr} {redex B target : VExpr}
    (hflat : flatAfter.IsDefEq univs Γ
      (VExpr.instRev
        ((certificate.restored.nested.generation.ruleLhsBody
          constructor).instL m1) captures)
      redex B)
    (hbody : after.IsDefEqU univs
      (Γ.map (VExpr.substConst interp))
      (VExpr.instRev
        ((certificate.restored.nested.restoreRec
          (certificate.restored.nested.generation.ruleLhsBody
            constructor)).instL m1)
        (captures.map (VExpr.substConst interp)))
      (VExpr.instRev
        (((certificate.restored.nested.generation.ruleLhsBody
          constructor).substConst interp).instL m1)
        (captures.map (VExpr.substConst interp))))
    (hredex : after.IsDefEqU univs
      (Γ.map (VExpr.substConst interp))
      (redex.substConst interp) target) :
    after.IsDefEqU univs (Γ.map (VExpr.substConst interp))
      (VExpr.instRev
        ((certificate.restored.nested.restoreRec
          (certificate.restored.nested.generation.ruleLhsBody
            constructor)).instL m1)
        (captures.map (VExpr.substConst interp)))
      target := by
  have hσ := VEnv.IsDefEq.substConst_instRev hi hΓflat hflat
  exact VEnv.IsDefEqU.trans certificate.restored.afterWF hΓ hbody
    (VEnv.IsDefEqU.trans certificate.restored.afterWF hΓ ⟨_, hσ⟩ hredex)

/-- A saturated restored rule left-hand side β-collapses to the iterated
instantiation of its restored generated body.  The rule's final-environment
WF proof supplies the restored lambda telescope; no restoration-specific
typing premise is needed beyond the exact restored capture spine. -/
theorem restoredRuleLhsApplied
    (certificate : NestedStagedCertificate source before flatAfter after)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (facts : certificate.RecursorRuleFacts i constructor)
    {univs : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (after.IsType univs))
    {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs)
    {captures : List VExpr} {B : VExpr}
    (hcaps : after.SpineWF univs Γ
      ((certificate.restored.nested.restoredRule i constructor).type.instL m1)
      captures B)
    (hcapsLen : captures.length =
      (certificate.restored.nested.generation.ruleBinders constructor).length) :
    after.IsDefEqU univs Γ
      (VExpr.appN
        ((certificate.restored.nested.restoredRule i constructor).lhs.instL m1)
        captures)
      (VExpr.instRev
        ((certificate.restored.nested.restoreRec
          (certificate.restored.nested.generation.ruleLhsBody
            constructor)).instL m1)
        captures) := by
  let nested := certificate.restored.nested
  let gen := nested.generation
  let binders := (gen.ruleBinders constructor).map
    (VInductDecl.restoreExpr nested.recEntries nested.recMap)
  let lhsBody := VInductDecl.restoreExpr nested.recEntries nested.recMap
    (gen.ruleLhsBody constructor)
  let typeBody := VInductDecl.restoreExpr nested.recEntries nested.recMap
    (gen.ruleResult constructor)
  have hlhsShape :
      (nested.restoredRule i constructor).lhs.instL m1 =
        VExpr.lamN (binders.map (VExpr.instL m1)) (lhsBody.instL m1) := by
    change (nested.restoreRec (gen.rule i constructor).lhs).instL m1 = _
    rw [gen.rule_lhs]
    unfold NestedBlockChecked.restoreRec
    rw [VInductDecl.restoreExpr_lamN, VExpr.instL_lamN]
  have htypeShape :
      (nested.restoredRule i constructor).type.instL m1 =
        VExpr.forallN (binders.map (VExpr.instL m1))
          (typeBody.instL m1) := by
    change (nested.restoreRec (gen.rule i constructor).type).instL m1 = _
    rw [gen.rule_type]
    unfold NestedBlockChecked.restoreRec
    rw [VInductDecl.restoreExpr_forallN, VExpr.instL_forallN]
    simp only [binders, typeBody, BlockGenerationChecked.ruleResult]
  have hlhsT : after.HasType univs Γ
      (VExpr.lamN (binders.map (VExpr.instL m1)) (lhsBody.instL m1))
      ((nested.restoredRule i constructor).type.instL m1) := by
    rw [← hlhsShape]
    exact (facts.restoredWF.1.instL hm1).weak0
      certificate.restored.afterWF.ordered
  obtain ⟨hTel, T₀, hbody⟩ := VEnv.HasType.lamN_wf
    certificate.restored.afterWF.ordered hΓ hlhsT
  rw [htypeShape] at hcaps
  have hlen : captures.length =
      (binders.map (VExpr.instL m1)).length := by
    simpa [binders] using hcapsLen
  have hretT₀ := hcaps.retarget hlen T₀
  have hcollapse := VEnv.IsDefEq.appN_lamN
    certificate.restored.afterWF.ordered hTel hbody hretT₀ hlen
  rw [hlhsShape]
  change after.IsDefEqU univs Γ
    (VExpr.appN
      (VExpr.lamN (binders.map (VExpr.instL m1)) (lhsBody.instL m1))
      captures)
    (VExpr.instRev (lhsBody.instL m1) captures)
  exact ⟨_, hcollapse⟩

/-- Once the complete restored rule LHS is aligned with the σ̂-image of
the flattened LHS, their saturated bodies are aligned automatically.  The
flattened capture spine is transported to the restored telescope, both lambda
towers are β-collapsed, and the interpreted flattened collapse supplies the
right endpoint.  Thus a nested fixture need not replay `restoreRec` through
the generated body binder-by-binder. -/
theorem restoredRuleBodyAlignmentOfLhs
    (certificate : NestedStagedCertificate source before flatAfter after)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (facts : certificate.RecursorRuleFacts i constructor)
    {interp : Name → Option VExpr}
    (hi : VEnv.ConstInterp flatAfter after interp)
    {univs : Nat} {Γ : List VExpr}
    (hΓflat : OnCtx Γ (flatAfter.IsType univs))
    (hΓrestored : OnCtx
      (Γ.map (VExpr.substConst interp)) (after.IsType univs))
    {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs)
    {captures : List VExpr} {B : VExpr}
    (hcaps : flatAfter.SpineWF univs Γ
      ((certificate.restored.nested.generation.rule i constructor).type.instL
        m1) captures B)
    (hcapsLen : captures.length =
      (certificate.restored.nested.generation.ruleBinders constructor).length)
    (htype : after.IsDefEqU univs
      (Γ.map (VExpr.substConst interp))
      ((certificate.restored.nested.restoredRule i constructor).type.instL m1)
      (((certificate.restored.nested.generation.rule i constructor).type.instL
        m1).substConst interp))
    (hlhs : after.IsDefEqU univs
      (Γ.map (VExpr.substConst interp))
      ((certificate.restored.nested.restoredRule i constructor).lhs.instL m1)
      (((certificate.restored.nested.generation.rule i constructor).lhs.instL
        m1).substConst interp)) :
    after.IsDefEqU univs (Γ.map (VExpr.substConst interp))
      (VExpr.instRev
        ((certificate.restored.nested.restoreRec
          (certificate.restored.nested.generation.ruleLhsBody
            constructor)).instL m1)
        (captures.map (VExpr.substConst interp)))
      (VExpr.instRev
        (((certificate.restored.nested.generation.ruleLhsBody
          constructor).substConst interp).instL m1)
        (captures.map (VExpr.substConst interp))) := by
  obtain ⟨B', hcapsRestored⟩ :=
    certificate.restoredRuleCaptureSpineOfConstInterp hi hΓflat
      hΓrestored hcaps hcapsLen htype
  have hrestoredCollapse := certificate.restoredRuleLhsApplied facts
    hΓrestored hm1 hcapsRestored (by simpa using hcapsLen)
  have hrestoredHead : after.HasType univs
      (Γ.map (VExpr.substConst interp))
      ((certificate.restored.nested.restoredRule i constructor).lhs.instL m1)
      ((certificate.restored.nested.restoredRule i constructor).type.instL m1) :=
    (facts.restoredWF.1.instL hm1).weak0
      certificate.restored.afterWF.ordered
  have hlhs' := hlhs.of_l certificate.restored.afterWF hΓrestored
    hrestoredHead
  have hlhsApplied : after.IsDefEqU univs
      (Γ.map (VExpr.substConst interp))
      (VExpr.appN
        ((certificate.restored.nested.restoredRule i constructor).lhs.instL m1)
        (captures.map (VExpr.substConst interp)))
      (VExpr.appN
        (((certificate.restored.nested.generation.rule i constructor).lhs.instL
          m1).substConst interp)
        (captures.map (VExpr.substConst interp))) :=
    ⟨B', hlhs'.appN_congr hcapsRestored⟩
  obtain ⟨_, hflatCollapse⟩ :=
    certificate.flatCertificate.ruleLhsApplied facts.flat hΓflat hm1 hcaps
      hcapsLen
  have hflatCollapseσ := hflatCollapse.substConst hi hΓflat
  simp only [NestedStagedCertificate.flatCertificate,
    VExpr.substConst_appN,
    VExpr.substConst_instRev hi.closed,
    VExpr.substConst_instL] at hflatCollapseσ
  simp only [VExpr.substConst_instL] at hlhsApplied
  exact VEnv.IsDefEqU.trans certificate.restored.afterWF hΓrestored
    hrestoredCollapse.symm
    (VEnv.IsDefEqU.trans certificate.restored.afterWF hΓrestored
      hlhsApplied ⟨_, hflatCollapseσ⟩)

/-- Transport a flattened body/redex match all the way to a final runtime
redex when whole restored rule type/LHS alignment is available.  Compared to
`restoredRuleBodyMatchedOfFlat`, this derived interface removes the local
restored-body premise; only the endpoint redex alignment remains specific to
the restoration representation. -/
theorem restoredRuleBodyMatchedOfFlatOfLhs
    (certificate : NestedStagedCertificate source before flatAfter after)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (facts : certificate.RecursorRuleFacts i constructor)
    {interp : Name → Option VExpr}
    (hi : VEnv.ConstInterp flatAfter after interp)
    {univs : Nat} {Γ : List VExpr}
    (hΓflat : OnCtx Γ (flatAfter.IsType univs))
    (hΓrestored : OnCtx
      (Γ.map (VExpr.substConst interp)) (after.IsType univs))
    {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs)
    {captures : List VExpr} {redex B target : VExpr}
    (hcaps : flatAfter.SpineWF univs Γ
      ((certificate.restored.nested.generation.rule i constructor).type.instL
        m1) captures B)
    (hcapsLen : captures.length =
      (certificate.restored.nested.generation.ruleBinders constructor).length)
    (htype : after.IsDefEqU univs
      (Γ.map (VExpr.substConst interp))
      ((certificate.restored.nested.restoredRule i constructor).type.instL m1)
      (((certificate.restored.nested.generation.rule i constructor).type.instL
        m1).substConst interp))
    (hlhs : after.IsDefEqU univs
      (Γ.map (VExpr.substConst interp))
      ((certificate.restored.nested.restoredRule i constructor).lhs.instL m1)
      (((certificate.restored.nested.generation.rule i constructor).lhs.instL
        m1).substConst interp))
    (hflat : flatAfter.IsDefEq univs Γ
      (VExpr.instRev
        ((certificate.restored.nested.generation.ruleLhsBody
          constructor).instL m1) captures)
      redex B)
    (hredex : after.IsDefEqU univs
      (Γ.map (VExpr.substConst interp))
      (redex.substConst interp) target) :
    after.IsDefEqU univs (Γ.map (VExpr.substConst interp))
      (VExpr.instRev
        ((certificate.restored.nested.restoreRec
          (certificate.restored.nested.generation.ruleLhsBody
            constructor)).instL m1)
        (captures.map (VExpr.substConst interp)))
      target := by
  have hbody := certificate.restoredRuleBodyAlignmentOfLhs facts hi hΓflat
    hΓrestored hm1 hcaps hcapsLen htype hlhs
  exact certificate.restoredRuleBodyMatchedOfFlat hi hΓflat hΓrestored
    hflat hbody hredex

/-- Extend the complete restored-body/runtime-redex match through the
arguments following the reducer's major premise.  The caller supplies the
same restored capture spine used by the output theorem, which fixes the
intermediate type without another uniqueness choice. -/
theorem restoredRuleBodyMatchedOfFlatOfLhsTrailing
    (certificate : NestedStagedCertificate source before flatAfter after)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (facts : certificate.RecursorRuleFacts i constructor)
    {interp : Name → Option VExpr}
    (hi : VEnv.ConstInterp flatAfter after interp)
    {univs : Nat} {Γ : List VExpr}
    (hΓflat : OnCtx Γ (flatAfter.IsType univs))
    (hΓrestored : OnCtx
      (Γ.map (VExpr.substConst interp)) (after.IsType univs))
    {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs)
    {captures : List VExpr} {redex B target B' : VExpr}
    (hcaps : flatAfter.SpineWF univs Γ
      ((certificate.restored.nested.generation.rule i constructor).type.instL
        m1) captures B)
    (hcapsLen : captures.length =
      (certificate.restored.nested.generation.ruleBinders constructor).length)
    (hcapsRestored : after.SpineWF univs
      (Γ.map (VExpr.substConst interp))
      ((certificate.restored.nested.restoredRule i constructor).type.instL m1)
      (captures.map (VExpr.substConst interp)) B')
    {trailing : List VExpr} {C : VExpr}
    (htrailing : after.SpineWF univs
      (Γ.map (VExpr.substConst interp)) B' trailing C)
    (htype : after.IsDefEqU univs
      (Γ.map (VExpr.substConst interp))
      ((certificate.restored.nested.restoredRule i constructor).type.instL m1)
      (((certificate.restored.nested.generation.rule i constructor).type.instL
        m1).substConst interp))
    (hlhs : after.IsDefEqU univs
      (Γ.map (VExpr.substConst interp))
      ((certificate.restored.nested.restoredRule i constructor).lhs.instL m1)
      (((certificate.restored.nested.generation.rule i constructor).lhs.instL
        m1).substConst interp))
    (hflat : flatAfter.IsDefEq univs Γ
      (VExpr.instRev
        ((certificate.restored.nested.generation.ruleLhsBody
          constructor).instL m1) captures)
      redex B)
    (hredex : after.IsDefEqU univs
      (Γ.map (VExpr.substConst interp))
      (redex.substConst interp) target) :
    after.IsDefEqU univs (Γ.map (VExpr.substConst interp))
      (VExpr.appN
        (VExpr.instRev
          ((certificate.restored.nested.restoreRec
            (certificate.restored.nested.generation.ruleLhsBody
              constructor)).instL m1)
          (captures.map (VExpr.substConst interp))) trailing)
      (VExpr.appN target trailing) := by
  have hbody := certificate.restoredRuleBodyMatchedOfFlatOfLhs facts hi
    hΓflat hΓrestored hm1 hcaps hcapsLen htype hlhs hflat hredex
  have hcollapse := certificate.restoredRuleLhsApplied facts hΓrestored hm1
    hcapsRestored (by simpa using hcapsLen)
  have hhead : after.HasType univs
      (Γ.map (VExpr.substConst interp))
      ((certificate.restored.nested.restoredRule i constructor).lhs.instL m1)
      ((certificate.restored.nested.restoredRule i constructor).type.instL m1) :=
    (facts.restoredWF.1.instL hm1).weak0
      certificate.restored.afterWF.ordered
  have happ := hcapsRestored.hasType_appN hhead
  have hbodyT :=
    (hcollapse.of_l certificate.restored.afterWF hΓrestored happ).hasType.2
  have hbody' := hbody.of_l certificate.restored.afterWF hΓrestored hbodyT
  exact ⟨C, hbody'.appN_congr htrailing⟩

/-- Extend the restored-left β-collapse through the reducer arguments after
the major premise.  The original restored capture spine fixes the exact
intermediate type used by that trailing spine. -/
theorem restoredRuleLhsAppliedTrailing
    (certificate : NestedStagedCertificate source before flatAfter after)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (facts : certificate.RecursorRuleFacts i constructor)
    {univs : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (after.IsType univs))
    {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs)
    {captures trailing : List VExpr} {B C : VExpr}
    (hcaps : after.SpineWF univs Γ
      ((certificate.restored.nested.restoredRule i constructor).type.instL m1)
      captures B)
    (hcapsLen : captures.length =
      (certificate.restored.nested.generation.ruleBinders constructor).length)
    (htrailing : after.SpineWF univs Γ B trailing C) :
    after.IsDefEqU univs Γ
      (VExpr.appN
        (VExpr.appN
          ((certificate.restored.nested.restoredRule i constructor).lhs.instL
            m1) captures) trailing)
      (VExpr.appN
        (VExpr.instRev
          ((certificate.restored.nested.restoreRec
            (certificate.restored.nested.generation.ruleLhsBody
              constructor)).instL m1)
          captures) trailing) := by
  have hlhs := certificate.restoredRuleLhsApplied facts hΓ hm1 hcaps hcapsLen
  have hlhsHead : after.HasType univs Γ
      ((certificate.restored.nested.restoredRule i constructor).lhs.instL m1)
      ((certificate.restored.nested.restoredRule i constructor).type.instL m1) :=
    (facts.restoredWF.1.instL hm1).weak0
      certificate.restored.afterWF.ordered
  have hlhsApp := hcaps.hasType_appN hlhsHead
  have hlhsB := hlhs.of_l certificate.restored.afterWF hΓ hlhsApp
  exact ⟨_, hlhsB.appN_congr htrailing⟩

/-- Canonical reducer-slice specialization of the restored-left collapse.
The full translated recursor array contains the major premise (and possibly
post-major arguments), so the strict major bound recovers the saturated
pre-major prefix used by the generated capture algebra. -/
theorem restoredRuleCanonicalLhsAppliedTrailing
    (certificate : NestedStagedCertificate source before flatAfter after)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (facts : certificate.RecursorRuleFacts i constructor)
    {univs : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (after.IsType univs))
    {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs)
    {fArgs aArgs : List VExpr}
    (hmajorBound :
      certificate.restored.nested.generation.ruleMajorArity constructor <
        fArgs.length)
    (hNlen : aArgs.length =
      certificate.restored.nested.generation.ruleArgArity constructor)
    {B C : VExpr}
    (hcaps : after.SpineWF univs Γ
      ((certificate.restored.nested.restoredRule i constructor).type.instL m1)
      (certificate.restored.nested.generation.ruleCaptureValues constructor
        fArgs aArgs) B)
    (htrailing : after.SpineWF univs Γ B
      (fArgs.drop
        (certificate.restored.nested.generation.ruleMajorArity constructor + 1))
      C) :
    after.IsDefEqU univs Γ
      (VExpr.appN
        (VExpr.appN
          ((certificate.restored.nested.restoredRule i constructor).lhs.instL
            m1)
          (certificate.restored.nested.generation.ruleCaptureValues constructor
            fArgs aArgs))
        (fArgs.drop
          (certificate.restored.nested.generation.ruleMajorArity constructor + 1)))
      (VExpr.appN
        (VExpr.instRev
          ((certificate.restored.nested.restoreRec
            (certificate.restored.nested.generation.ruleLhsBody
              constructor)).instL m1)
          (certificate.restored.nested.generation.ruleCaptureValues constructor
            fArgs aArgs))
        (fArgs.drop
          (certificate.restored.nested.generation.ruleMajorArity constructor + 1))) := by
  let gen := certificate.restored.nested.generation
  have hmajorLE : gen.ruleMajorArity constructor ≤ fArgs.length := by
    dsimp [gen]
    omega
  have htakeLen : (fArgs.take (gen.ruleMajorArity constructor)).length =
      gen.ruleMajorArity constructor := by
    rw [List.length_take, Nat.min_eq_left hmajorLE]
  have hcapsLen := gen.ruleCaptureValues_length constructor htakeLen hNlen
  rw [gen.ruleCaptureValues_take_major] at hcapsLen
  exact certificate.restoredRuleLhsAppliedTrailing facts hΓ hm1 hcaps
    hcapsLen htrailing

/-- Apply the final registered restoration of one staged rule to an exact
typed capture spine.  This is the final-environment counterpart of the
flattened generated-pattern consumer: restoration itself is already owned by
the nested transaction, so the only remaining dynamic premise is typing the
restored captures against the restored rule telescope. -/
theorem restoredRuleReductionApplied
    (certificate : NestedStagedCertificate source before flatAfter after)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (facts : certificate.RecursorRuleFacts i constructor)
    {univs : Nat} {Γ : List VExpr} {m1 : List VLevel}
    (hm1 : ∀ l ∈ m1, l.WF univs)
    (hlen1 : m1.length =
      certificate.restored.nested.generation.recUvars)
    {captures : List VExpr} {B : VExpr}
    (hcaps : after.SpineWF univs Γ
      ((certificate.restored.nested.restoredRule i constructor).type.instL m1)
      captures B) :
    after.IsDefEq univs Γ
      (VExpr.appN
        ((certificate.restored.nested.restoredRule i constructor).lhs.instL m1)
        captures)
      (VExpr.appN
        ((certificate.restored.nested.restoredRule i constructor).rhs.instL m1)
        captures) B := by
  have hlenRule : m1.length =
      (certificate.restored.nested.restoredRule i constructor).uvars := by
    simpa [NestedBlockChecked.restoredRule, NestedBlockChecked.restoreRule]
      using hlen1.trans
        (certificate.restored.nested.generation.rule_uvars i constructor).symm
  exact (VEnv.IsDefEq.appN_congr
    (.extra facts.restoredRegistered hm1 hlenRule) hcaps)

end NestedStagedCertificate

end VInductDecl

end Lean4Lean

/-! ## Transitional trust guards -/

/-- info: 'Lean4Lean.VInductDecl.BlockGenerationChecked.ruleCaptureValues_translation' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockGenerationChecked.ruleCaptureValues_translation

/-- info: 'Lean4Lean.VInductDecl.BlockCertificate.ruleOwnerFacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockCertificate.ruleOwnerFacts

/--
info: 'Lean4Lean.VInductDecl.BlockCertificate.ruleRecursorHeadHasType' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockCertificate.ruleRecursorHeadHasType

/--
info: 'Lean4Lean.VInductDecl.BlockCertificate.ruleConstructorHeadHasType' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockCertificate.ruleConstructorHeadHasType

/--
info: 'Lean4Lean.VInductDecl.BlockCertificate.ruleMajorTypesDefEqUnindexed' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockCertificate.ruleMajorTypesDefEqUnindexed

/--
info: 'Lean4Lean.VInductDecl.BlockCertificate.ruleParameterAgreementUnindexedOfMajorInjectivity' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockCertificate.ruleParameterAgreementUnindexedOfMajorInjectivity

/--
info: 'Lean4Lean.VInductDecl.BlockCertificate.ruleFieldSpineOneParam' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockCertificate.ruleFieldSpineOneParam

/--
info: 'Lean4Lean.VInductDecl.BlockCertificate.ruleReduction' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockCertificate.ruleReduction

/--
info: 'Lean4Lean.VInductDecl.NestedStagedCertificate.flatRuleReduction' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.NestedStagedCertificate.flatRuleReduction

/--
info: 'Lean4Lean.VInductDecl.BlockCertificate.ruleReductionMatched' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockCertificate.ruleReductionMatched

/--
info: 'Lean4Lean.VInductDecl.NestedStagedCertificate.flatRuleReductionMatched' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.NestedStagedCertificate.flatRuleReductionMatched

/--
info: 'Lean4Lean.VInductDecl.BlockCertificate.ruleReductionMatchedUnindexed' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockCertificate.ruleReductionMatchedUnindexed

/--
info: 'Lean4Lean.VInductDecl.NestedStagedCertificate.flatRuleReductionMatchedUnindexed' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.NestedStagedCertificate.flatRuleReductionMatchedUnindexed

/--
info: 'Lean4Lean.VInductDecl.BlockCertificate.ruleReductionMatchedUnindexedOfFieldContinuation' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockCertificate.ruleReductionMatchedUnindexedOfFieldContinuation

/--
info: 'Lean4Lean.VInductDecl.BlockCertificate.ruleReductionMatchedUnindexedOfMajorInjectivityAndFieldContinuation' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockCertificate.ruleReductionMatchedUnindexedOfMajorInjectivityAndFieldContinuation

/-- info: 'Lean4Lean.VInductDecl.BlockCertificate.ruleLhsApplied' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockCertificate.ruleLhsApplied

/--
info: 'Lean4Lean.VInductDecl.BlockCertificate.ruleLhsBodyMatchedOfReduction' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockCertificate.ruleLhsBodyMatchedOfReduction

/--
info: 'Lean4Lean.VInductDecl.BlockCertificate.ruleCaptureSpineUnindexedOfMajorInjectivityOneParam' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockCertificate.ruleCaptureSpineUnindexedOfMajorInjectivityOneParam

/--
info: 'Lean4Lean.VInductDecl.BlockCertificate.ruleReductionMatchedUnindexedOfMajorInjectivityOneParam' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockCertificate.ruleReductionMatchedUnindexedOfMajorInjectivityOneParam

/--
info: 'Lean4Lean.VInductDecl.BlockCertificate.ruleReductionMatchedUnindexedOfMajorInjectivityNoFields' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockCertificate.ruleReductionMatchedUnindexedOfMajorInjectivityNoFields

/--
info: 'Lean4Lean.VInductDecl.NestedStagedCertificate.flatRuleReductionMatchedUnindexedOfFieldContinuation' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.NestedStagedCertificate.flatRuleReductionMatchedUnindexedOfFieldContinuation

/--
info: 'Lean4Lean.VInductDecl.NestedStagedCertificate.flatRuleReductionMatchedUnindexedOfMajorInjectivityAndFieldContinuation' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.NestedStagedCertificate.flatRuleReductionMatchedUnindexedOfMajorInjectivityAndFieldContinuation

/--
info: 'Lean4Lean.VInductDecl.NestedStagedCertificate.flatRuleCaptureSpineUnindexedOfMajorInjectivityOneParam' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.NestedStagedCertificate.flatRuleCaptureSpineUnindexedOfMajorInjectivityOneParam

/--
info: 'Lean4Lean.VInductDecl.NestedStagedCertificate.flatRuleReductionMatchedUnindexedOfMajorInjectivityOneParam' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.NestedStagedCertificate.flatRuleReductionMatchedUnindexedOfMajorInjectivityOneParam

/--
info: 'Lean4Lean.VInductDecl.NestedStagedCertificate.flatRuleCaptureAndLhsBodyMatchedUnindexedOfMajorInjectivityOneParam' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.NestedStagedCertificate.flatRuleCaptureAndLhsBodyMatchedUnindexedOfMajorInjectivityOneParam

/--
info: 'Lean4Lean.VInductDecl.NestedStagedCertificate.flatRuleLhsBodyMatchedUnindexedOfMajorInjectivityOneParam' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.NestedStagedCertificate.flatRuleLhsBodyMatchedUnindexedOfMajorInjectivityOneParam

/--
info: 'Lean4Lean.VInductDecl.NestedStagedCertificate.flatRuleReductionMatchedUnindexedOfMajorInjectivityNoFields' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.NestedStagedCertificate.flatRuleReductionMatchedUnindexedOfMajorInjectivityNoFields

/--
info: 'Lean4Lean.VInductDecl.NestedStagedCertificate.restoredRuleCaptureSpineOfConstInterp' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.NestedStagedCertificate.restoredRuleCaptureSpineOfConstInterp

/--
info: 'Lean4Lean.VInductDecl.NestedStagedCertificate.restoredRuleCanonicalCaptureSpineOfConstInterp' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.NestedStagedCertificate.restoredRuleCanonicalCaptureSpineOfConstInterp

/--
info: 'Lean4Lean.VInductDecl.NestedStagedCertificate.restoredRuleCanonicalCaptureSpineUnindexedOfMajorInjectivityOneParam' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.NestedStagedCertificate.restoredRuleCanonicalCaptureSpineUnindexedOfMajorInjectivityOneParam

/--
info: 'Lean4Lean.VInductDecl.NestedStagedCertificate.restoredRuleBodyMatchedOfFlat' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.NestedStagedCertificate.restoredRuleBodyMatchedOfFlat

/--
info: 'Lean4Lean.VInductDecl.NestedStagedCertificate.restoredRuleLhsApplied' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.NestedStagedCertificate.restoredRuleLhsApplied

/--
info: 'Lean4Lean.VInductDecl.NestedStagedCertificate.restoredRuleBodyAlignmentOfLhs' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.NestedStagedCertificate.restoredRuleBodyAlignmentOfLhs

/--
info: 'Lean4Lean.VInductDecl.NestedStagedCertificate.restoredRuleBodyMatchedOfFlatOfLhs' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.NestedStagedCertificate.restoredRuleBodyMatchedOfFlatOfLhs

/--
info: 'Lean4Lean.VInductDecl.NestedStagedCertificate.restoredRuleBodyMatchedOfFlatOfLhsTrailing' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.NestedStagedCertificate.restoredRuleBodyMatchedOfFlatOfLhsTrailing

/--
info: 'Lean4Lean.VInductDecl.NestedStagedCertificate.restoredRuleLhsAppliedTrailing' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.NestedStagedCertificate.restoredRuleLhsAppliedTrailing

/--
info: 'Lean4Lean.VInductDecl.NestedStagedCertificate.restoredRuleCanonicalLhsAppliedTrailing' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.NestedStagedCertificate.restoredRuleCanonicalLhsAppliedTrailing

/--
info: 'Lean4Lean.VInductDecl.NestedStagedCertificate.restoredRuleReductionApplied' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.NestedStagedCertificate.restoredRuleReductionApplied
