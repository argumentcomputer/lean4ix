import Lean4Lean.Experimental.SExpr
import Lean4Lean.Theory.Typing.InductivePatternWF

/-!
# L4L-16 R2: the generic per-rule replay engine

D0 and D1 each replay their generated iota rules *by hand*, once per rule:
roughly 640 lines for `SExprParamsD0.lean`'s two `Nat` rules and 340 for
`SExprParamsD1.lean`'s re-basing of them.  Almost none of that volume is
rule-specific.  This module extracts the rule-independent part as a single
engine, parameterized only by

* an ambient `[Params]` with `env.WF` and a `Params.StructureEtaSound`
  certificate (the two facts a fixture instance establishes once), and
* the *structural* shape of one registered rule — `df.lhs = lamN binders
  body`, `df.type = forallN binders result` — which for a certified block is
  `BlockGenerationChecked.rule_lhs`/`rule_type`, i.e. `rfl`.

What is left for a rule's own glue is exactly the two things that genuinely
vary: naming its recursor/constructor and levels, and supplying the
per-argument typings that build the canonical spine.

Contents:

* §1 the ambient certificate `Replay` and the type-uniqueness tower
  (`typeUniq`, `typesTrans`, `typesInst`, `forallEInv`), generic versions of
  `d1TypeUniq` … `d1ForallEInv`;
* §2 the spine views (`SpineConsView`, `pathSpineOfSpineWF`), generic
  versions of `d1SpineConsView` and `d1PathSpineOfSpineWF`;
* §3 the β-collapse engine `ruleCollapse` — the reify → `instL_lamN` →
  `lamN_wf` → `SpineWF.retarget` → `appN_lamN` → `IsDefEq.mkS` chain that
  every rule replay runs verbatim;
* §4 the site assembler `iotaSiteOf`, which turns the collapse plus a
  rule's own capture data into a `Pattern.IotaReductionSite`, taking the
  `Pattern.Check` discharge as an explicit hypothesis (see the D2 record:
  that discharge is `L4L-18A′`-gated at a general matched redex).
-/

namespace Lean4Lean
namespace SExpr

/-! ## §1 The ambient replay certificate -/

/-- The two ambient facts a fixture instance supplies once, after which
every per-rule replay is generic.  `wf` powers type uniqueness through
Theory's inversion lemmas; `structEta` powers the `IsDefEq.mkS` transfer
back from Theory into the quotiented syntax. -/
structure Replay [Params] : Prop where
  wf : Params.env.WF
  structEta : Params.StructureEtaSound

variable [Params] (R : Replay)

/-- Reified validity of a working context. -/
def CtxValid (Γ : List SExpr) : Prop :=
  OnCtx (Γ.map SExpr.reify) (Params.env.IsType Params.univs)

/-- Two types of one term are definitionally equal at some sort. -/
def TypesDefEq (Γ : List SExpr) (A B : SExpr) : Prop :=
  ∃ u, IsDefEq Γ A B (.sort u)

theorem ctx_mk_reify (Γ : List SExpr) :
    (Γ.map SExpr.reify).map SExpr.mk = Γ := by
  rw [List.map_map]
  exact List.map_id''' Γ fun term _ => SExpr.mk_reify term

include R in
theorem typeUniq {Γ : List SExpr} {x A B : SExpr}
    (hΓ : CtxValid Γ) (hxA : IsDefEq Γ x x A) (hxB : IsDefEq Γ x x B) :
    TypesDefEq Γ A B := by
  have hxA' := hxA.reify hΓ
  have hxB' := hxB.reify hΓ
  obtain ⟨u, hAB⟩ := hxA'.uniq R.wf hΓ hxB'
  have hlevels := (VEnv.CtxStrong.strong Params.henv hΓ).levelWF
  have hAB' := SExpr.IsDefEq.mkS R.structEta hAB hlevels
  rw [ctx_mk_reify] at hAB'
  exact ⟨SLevel.mk u, by simpa only [SExpr.mk_reify, SExpr.mk] using hAB'⟩

include R in
theorem typesTrans {Γ : List SExpr} {A B C : SExpr}
    (hΓ : CtxValid Γ) (hAB : TypesDefEq Γ A B) (hBC : TypesDefEq Γ B C) :
    TypesDefEq Γ A C := by
  obtain ⟨u, hAB⟩ := hAB
  obtain ⟨v, hBC⟩ := hBC
  obtain ⟨w, huv⟩ := typeUniq R hΓ hAB.hasType.2 hBC.hasType.1
  exact ⟨u, hAB.trans (huv.symm.defeqDF hBC)⟩

theorem typesInst {Γ : List SExpr} {D B B' e : SExpr}
    (hBB' : TypesDefEq (D :: Γ) B B') (he : IsDefEq Γ e e D) :
    TypesDefEq Γ (B.inst e) (B'.inst e) := by
  obtain ⟨u, hBB'⟩ := hBB'
  exact ⟨u, hBB'.subst (Ctx.Subst.one IsDefEq.weak' IsDefEq.bvar he)⟩

include R in
theorem forallEInv {Γ : List SExpr} {A B A' B' : SExpr}
    (hΓ : CtxValid Γ)
    (hPi : TypesDefEq Γ (.forallE A B) (.forallE A' B')) :
    TypesDefEq Γ A A' ∧ TypesDefEq (A :: Γ) B B' := by
  obtain ⟨_, hPi⟩ := hPi
  have hPi' := hPi.reify hΓ
  have hPiU : Params.env.IsDefEqU Params.univs (Γ.map SExpr.reify)
      (.forallE A.reify B.reify) (.forallE A'.reify B'.reify) := ⟨_, hPi'⟩
  obtain ⟨⟨u, hA⟩, v, hB⟩ := hPiU.forallE_inv R.wf hΓ
  have hlevels := (VEnv.CtxStrong.strong Params.henv hΓ).levelWF
  have hA' := SExpr.IsDefEq.mkS R.structEta hA hlevels
  rw [ctx_mk_reify] at hA'
  have hAwf : (A.reify).LevelWF Params.univs := SExpr.reify_levelWF A
  have hB' := SExpr.IsDefEq.mkS R.structEta hB ⟨hlevels, hAwf⟩
  have hBctx : ((A.reify :: Γ.map SExpr.reify).map SExpr.mk) = A :: Γ := by
    rw [List.map_cons, ctx_mk_reify, SExpr.mk_reify]
  rw [hBctx] at hB'
  exact ⟨⟨SLevel.mk u, by simpa only [SExpr.mk_reify, SExpr.mk] using hA'⟩,
    ⟨SLevel.mk v, by simpa only [SExpr.mk_reify, SExpr.mk] using hB'⟩⟩

/-! ## §2 Spine views -/

/-- One peeled application of a conversion-aware spine: the exact domain and
codomain the spine used, with the argument's typing and the tail. -/
structure SpineConsView (Γ : List SExpr) (D B e : SExpr) (es : List SExpr)
    (Res : SExpr) where
  domain : SExpr
  codomain : SExpr
  domainEq : TypesDefEq Γ D domain
  codomainEq : TypesDefEq (D :: Γ) B codomain
  argument : IsDefEq Γ e e domain
  tail : SpineWF Γ (codomain.inst e) es Res

include R in
theorem spineConsView_nonempty {Γ : List SExpr} {D B Head e Res : SExpr}
    {es : List SExpr}
    (hΓ : CtxValid Γ) (hHead : TypesDefEq Γ (.forallE D B) Head)
    (H : SpineWF Γ Head (e :: es) Res) :
    Nonempty (SpineConsView Γ D B e es Res) := by
  generalize hargsEq : e :: es = args at H
  induction H generalizing D B e es with
  | nil => cases hargsEq
  | @cons _ domain _ _ codomain harg htail ih =>
    cases hargsEq
    obtain ⟨hdom, hbody⟩ := forallEInv R hΓ hHead
    exact ⟨{ domain := domain, codomain := codomain, domainEq := hdom
             codomainEq := hbody, argument := harg, tail := htail }⟩
  | @conv _ Head' u _ _ hconv htail ih =>
    exact ih (typesTrans R hΓ hHead ⟨u, hconv⟩) hargsEq
  | @ret _ _ R' _ _ htail hret ih =>
    let ⟨view⟩ := ih hHead hargsEq
    exact ⟨{ view with tail := .ret view.tail hret }⟩

noncomputable def spineConsView {Γ : List SExpr} {D B Head e Res : SExpr}
    {es : List SExpr}
    (hΓ : CtxValid Γ) (hHead : TypesDefEq Γ (.forallE D B) Head)
    (H : SpineWF Γ Head (e :: es) Res) : SpineConsView Γ D B e es Res :=
  Classical.choice (spineConsView_nonempty R hΓ hHead H)

theorem SpineConsView.argumentExpected {Γ : List SExpr} {D B e Res : SExpr}
    {es : List SExpr} (view : SpineConsView Γ D B e es Res) :
    IsDefEq Γ e e D := by
  obtain ⟨_, hdom⟩ := view.domainEq
  exact hdom.symm.defeqDF view.argument

theorem SpineConsView.restEq {Γ : List SExpr} {D B e Res : SExpr}
    {es : List SExpr} (view : SpineConsView Γ D B e es Res) :
    TypesDefEq Γ (B.inst e) (view.codomain.inst e) :=
  typesInst view.codomainEq view.argumentExpected

include R in
/-- Replace the final argument of a well-typed spine by a definitionally
equal term.  Earlier arguments remain reflexive; the final equality is
retargeted to the exact dependent domain recovered from the spine. -/
theorem SpineWF.replaceLast {Γ : List SExpr} {Head Res x y T : SExpr}
    {pre : List SExpr}
    (hΓ : CtxValid Γ) (H : SpineWF Γ Head (pre ++ [x]) Res)
    (hxy : IsDefEq Γ x y T) :
    SpineDefEq Γ Head (pre ++ [x]) (pre ++ [y]) Res := by
  generalize hargs : pre ++ [x] = args at H
  induction H generalizing pre with
  | nil => simp at hargs
  | @cons e domain es result codomain harg htail ih =>
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hargs
      obtain ⟨rfl, rfl⟩ := hargs
      obtain ⟨_, hdomain⟩ := typeUniq R hΓ harg hxy.hasType.1
      exact .cons (hdomain.symm.defeqDF hxy) htail.toSpineDefEq
    | cons p pre =>
      simp only [List.cons_append, List.cons.injEq] at hargs
      obtain ⟨rfl, hrest⟩ := hargs
      exact .cons harg (ih hrest)
  | conv hty _ ih => exact .conv hty (ih hargs)
  | ret _ hty ih => exact .ret (ih hargs) hty

include R in
/-- The typed-redex package already proves that the concrete recursor/
constructor application is self-typed at the site's result.  The recursor
spine is stored using `majorTerm`; `majorEq` replaces only that final
argument by the matched constructor application. -/
theorem _root_.Lean4Lean.Pattern.IotaTyping.redexSelf
    {Γ : List SExpr} {rec ctor : Name}
    {recLs ctorLs : List SLevel} {recArgs ctorArgs : List SExpr}
    {majorTerm A : SExpr}
    (hΓ : CtxValid Γ)
    (typing : Pattern.IotaTyping Γ rec ctor recLs ctorLs
      recArgs ctorArgs majorTerm A) :
    IsDefEq Γ
      ((recArgs.foldr (fun (a f : SExpr) => f.app a)
        (SExpr.const rec recLs)).app
        (ctorArgs.foldr (fun (a f : SExpr) => f.app a)
          (SExpr.const ctor ctorLs)))
      ((recArgs.foldr (fun (a f : SExpr) => f.app a)
        (SExpr.const rec recLs)).app
        (ctorArgs.foldr (fun (a f : SExpr) => f.app a)
          (SExpr.const ctor ctorLs))) A := by
  have hargs := SpineWF.replaceLast R hΓ typing.recSpine typing.majorEq
  have hredex := (hargs.congr typing.recHead).hasType.2
  simpa [List.foldl_append, List.foldl_reverse] using hredex

omit [Params] in
private theorem forall₂EquivSymm {xs ys : List VLevel}
    (H : List.Forall₂ (· ≈ ·) xs ys) : List.Forall₂ (· ≈ ·) ys xs := by
  induction H with
  | nil => exact .nil
  | cons h _ ih => exact .cons h.symm ih

omit [Params] in
private theorem eqUpToLevelsSymm {U : Nat} {e e' : VExpr}
    (H : VEnv.EqUpToLevels U e e') : VEnv.EqUpToLevels U e' e := by
  induction H with
  | bvar => exact .bvar
  | const hls hls' heq =>
    exact .const hls' hls (forall₂EquivSymm heq)
  | sort hu hv heq => exact .sort hv hu heq.symm
  | app _ _ ihf iha => exact .app ihf iha
  | lam _ _ ihA ihBody => exact .lam ihA ihBody
  | forallE _ _ ihA ihBody => exact .forallE ihA ihBody

include R in
/-- Replay a conversion-aware S-expression spine against its exact Theory
telescope.  `SpineWF` on the S-expression side permits head and result
conversions, while Theory's spine judgment deliberately does not; repeatedly
peeling the canonical Pi tower with `spineConsView` recovers each argument at
the exact domain and therefore reconstructs the strict Theory spine.

The result is the canonical iterated instantiation of the supplied Theory
codomain.  In particular, a caller can feed this spine directly to
`ruleCollapse` without duplicating the conversion bookkeeping performed by
the D0/D1 rule replays. -/
theorem vSpineOfSpineWF_forallN {Γ : List SExpr} {Head Res : SExpr}
    (hΓ : CtxValid Γ) :
    ∀ {n : Nat} {binders : List VExpr} {result : VExpr}
      {args : List SExpr},
      binders.length = n → args.length = n →
      (VExpr.forallN binders result).LevelWF Params.univs →
      TypesDefEq Γ (SExpr.mk (VExpr.forallN binders result)) Head →
      SpineWF Γ Head args Res →
      Params.env.SpineWF Params.univs (Γ.map SExpr.reify)
        (VExpr.forallN binders result) (args.map SExpr.reify)
        (VExpr.instRev result (args.map SExpr.reify)) := by
  intro n
  induction n generalizing Head with
  | zero =>
    intro binders result args hbinders hargs _ _ _
    obtain rfl : binders = [] := List.length_eq_zero_iff.mp hbinders
    obtain rfl : args = [] := List.length_eq_zero_iff.mp hargs
    exact .nil
  | succ n ih =>
    intro binders result args hbinders hargs hlevel hHead hspine
    cases binders with
    | nil => simp at hbinders
    | cons D binders =>
      cases args with
      | nil => simp at hargs
      | cons e args =>
        have hbinders' : binders.length = n := by simpa using hbinders
        have hargs' : args.length = n := by simpa using hargs
        change D.LevelWF Params.univs ∧
          (VExpr.forallN binders result).LevelWF Params.univs at hlevel
        change TypesDefEq Γ
          (.forallE (SExpr.mk D) (SExpr.mk (VExpr.forallN binders result)))
          Head at hHead
        let view := spineConsView R hΓ hHead hspine
        have he := view.argumentExpected
        have heV := he.reify hΓ
        have heV' : Params.env.IsDefEq Params.univs
            (Γ.map SExpr.reify) e.reify e.reify D :=
          VEnv.IsDefEq.alignEqUpToLevels hΓ heV
            (VEnv.EqUpToLevels.reify_refl e)
            (VEnv.EqUpToLevels.reify_refl e)
            (eqUpToLevelsSymm (VEnv.EqUpToLevels.reify_mk hlevel.1))
        have hcanon :
            (SExpr.mk (VExpr.forallN binders result)).inst e =
              SExpr.mk (VExpr.forallN
                (VExpr.instTelN e.reify binders 0)
                (result.inst e.reify binders.length)) := by
          calc
            _ = (SExpr.mk (VExpr.forallN binders result)).inst
                (SExpr.mk e.reify) := by rw [SExpr.mk_reify]
            _ = SExpr.mk ((VExpr.forallN binders result).inst e.reify) :=
              (SExpr.mk_instExpr).symm
            _ = _ := by rw [VExpr.instN_forallN, Nat.zero_add]
        have hnext : TypesDefEq Γ
            (SExpr.mk (VExpr.forallN
              (VExpr.instTelN e.reify binders 0)
              (result.inst e.reify binders.length)))
            (view.codomain.inst e) := hcanon ▸ view.restEq
        have hlevel' : (VExpr.forallN
            (VExpr.instTelN e.reify binders 0)
            (result.inst e.reify binders.length)).LevelWF Params.univs := by
          have hinst := hlevel.2.inst (k := 0) (SExpr.reify_levelWF e)
          rw [VExpr.instN_forallN, Nat.zero_add] at hinst
          exact hinst
        have htail := ih
          (binders := VExpr.instTelN e.reify binders 0)
          (result := result.inst e.reify binders.length)
          (args := args)
          (by simpa [VExpr.instTelN_length] using hbinders') hargs'
          hlevel' hnext view.tail
        refine .cons ?_ ?_
        · exact heV'
        · simpa only [VExpr.instN_forallN, Nat.zero_add, VExpr.instRev,
            List.map_cons, List.length_map, hargs', hbinders'] using htail

include R in
/-- Replay just a leading Pi telescope from a longer conversion-aware spine,
while replacing the old tail by an arbitrary new result.  This is the common
prefix operation needed by generated iota rules: the recursor typing spine
contains the final major argument, whereas the registered rule reuses the
same parameter/motive/minor prefix and continues with constructor fields.

The returned result is the canonical instantiation of `newResult`; callers
may append the field spine and use one final `SpineWF.ret` conversion. -/
theorem spinePrefixForallN {Γ : List SExpr} {Head Res : SExpr}
    (hΓ : CtxValid Γ) :
    ∀ {n : Nat} {binders : List VExpr} {oldResult newResult : VExpr}
      {args suffix : List SExpr},
      binders.length = n → args.length = n →
      (VExpr.forallN binders oldResult).LevelWF Params.univs →
      TypesDefEq Γ (SExpr.mk (VExpr.forallN binders oldResult)) Head →
      SpineWF Γ Head (args ++ suffix) Res →
      SpineWF Γ (SExpr.mk (VExpr.forallN binders newResult)) args
        (SExpr.mk (VExpr.instRev newResult (args.map SExpr.reify))) := by
  intro n
  induction n generalizing Head with
  | zero =>
    intro binders oldResult newResult args suffix hbinders hargs _ _ _
    obtain rfl : binders = [] := List.length_eq_zero_iff.mp hbinders
    obtain rfl : args = [] := List.length_eq_zero_iff.mp hargs
    exact .nil
  | succ n ih =>
    intro binders oldResult newResult args suffix hbinders hargs hlevel
      hHead hspine
    cases binders with
    | nil => simp at hbinders
    | cons D binders =>
      cases args with
      | nil => simp at hargs
      | cons e args =>
        have hbinders' : binders.length = n := by simpa using hbinders
        have hargs' : args.length = n := by simpa using hargs
        change D.LevelWF Params.univs ∧
          (VExpr.forallN binders oldResult).LevelWF Params.univs at hlevel
        change TypesDefEq Γ
          (.forallE (SExpr.mk D)
            (SExpr.mk (VExpr.forallN binders oldResult))) Head at hHead
        let view := spineConsView R hΓ hHead hspine
        have holdCanon :
            (SExpr.mk (VExpr.forallN binders oldResult)).inst e =
              SExpr.mk (VExpr.forallN
                (VExpr.instTelN e.reify binders 0)
                (oldResult.inst e.reify binders.length)) := by
          calc
            _ = (SExpr.mk (VExpr.forallN binders oldResult)).inst
                (SExpr.mk e.reify) := by rw [SExpr.mk_reify]
            _ = SExpr.mk ((VExpr.forallN binders oldResult).inst e.reify) :=
              (SExpr.mk_instExpr).symm
            _ = _ := by rw [VExpr.instN_forallN, Nat.zero_add]
        have hnext : TypesDefEq Γ
            (SExpr.mk (VExpr.forallN
              (VExpr.instTelN e.reify binders 0)
              (oldResult.inst e.reify binders.length)))
            (view.codomain.inst e) := holdCanon ▸ view.restEq
        have hlevel' : (VExpr.forallN
            (VExpr.instTelN e.reify binders 0)
            (oldResult.inst e.reify binders.length)).LevelWF
              Params.univs := by
          have hinst := hlevel.2.inst (k := 0) (SExpr.reify_levelWF e)
          rw [VExpr.instN_forallN, Nat.zero_add] at hinst
          exact hinst
        have htail := ih
          (binders := VExpr.instTelN e.reify binders 0)
          (oldResult := oldResult.inst e.reify binders.length)
          (newResult := newResult.inst e.reify binders.length)
          (args := args) (suffix := suffix)
          (by simpa [VExpr.instTelN_length] using hbinders') hargs'
          hlevel' hnext view.tail
        have hnewCanon :
            (SExpr.mk (VExpr.forallN binders newResult)).inst e =
              SExpr.mk (VExpr.forallN
                (VExpr.instTelN e.reify binders 0)
                (newResult.inst e.reify binders.length)) := by
          calc
            _ = (SExpr.mk (VExpr.forallN binders newResult)).inst
                (SExpr.mk e.reify) := by rw [SExpr.mk_reify]
            _ = SExpr.mk ((VExpr.forallN binders newResult).inst e.reify) :=
              (SExpr.mk_instExpr).symm
            _ = _ := by rw [VExpr.instN_forallN, Nat.zero_add]
        refine .cons view.argumentExpected ?_
        rw [hnewCanon]
        simpa only [VExpr.instRev, List.map_cons, List.length_map,
          hargs', hbinders'] using htail

include R in
/-- Re-index a spine by the paths that selected its arguments. -/
theorem pathSpineOfSpineWF {Γ : List SExpr} {alpha : Type}
    {value type : alpha → SExpr} {A B : SExpr} {paths : List alpha}
    (hΓ : CtxValid Γ)
    (htyped : ∀ path, IsDefEq Γ (value path) (value path) (type path))
    (H : SpineWF Γ A (paths.map value) B) :
    PathSpineWF Γ value type A paths B := by
  generalize hargs : paths.map value = args at H
  induction H generalizing paths with
  | nil =>
    have hpaths : paths = [] := by simpa using hargs
    subst paths
    exact .nil
  | @cons e domain es result codomain harg htail ih =>
    cases paths with
    | nil => simp at hargs
    | cons path paths =>
      simp only [List.map_cons, List.cons.injEq] at hargs
      obtain ⟨hvalue, hrest⟩ := hargs
      subst e
      obtain ⟨_, hdomain⟩ := typeUniq R hΓ (htyped path) harg
      exact .cons hdomain (ih hrest)
  | @conv Head Head' u es result hHead htail ih => exact .conv hHead (ih hargs)
  | @ret Head es result result' u htail hresult ih => exact .ret (ih hargs) hresult

/-! ## §2.5 Strong lambda-tower closure

`Params.Semantic.registered` is proved from an equality at the fully opened
rule body followed by one eta contraction per rule binder.  The D0 proof
spelled out every prefix application separately.  The helpers below factor
that traversal independently of any environment: callers supply only the
strong-weakening operation available while their semantic instance is still
being assembled. -/

/-- Apply a term successively to the newest variables introduced by a
dependent telescope. -/
def applyTelVars : List SExpr → SExpr → SExpr
  | [], f => f
  | _ :: As, f => applyTelVars As (f.lift.app (.bvar 0))

/-- `applyTelVars` inspects only the number of telescope entries; their
types are carried separately by the typing theorem below. -/
theorem applyTelVars_eq_of_length {As Bs : List SExpr}
    (h : As.length = Bs.length) (f : SExpr) :
    applyTelVars As f = applyTelVars Bs f := by
  induction As generalizing Bs f with
  | nil =>
    have : Bs = [] := List.length_eq_zero_iff.mp h.symm
    subst Bs
    rfl
  | cons A As ih =>
    cases Bs with
    | nil => simp at h
    | cons B Bs =>
      simp only [List.length_cons, Nat.succ.injEq] at h
      simpa only [applyTelVars] using ih h (f.lift.app (.bvar 0))

/-- Canonical variables for a fully opened telescope, from oldest to newest
in application order. -/
def telBvars [Params] : Nat → List SExpr
  | 0 => []
  | n + 1 => .bvar n :: telBvars n

theorem Lift.comp_skip_skipN_refl (n : Nat) :
    Lift.comp (Lift.skip Lift.refl) (Lift.skipN Lift.refl n) =
      Lift.skip (Lift.skipN Lift.refl n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Lift.skipN, Lift.comp, ih]

/-- Pure syntax formula for `applyTelVars`: lift the head past the whole
telescope and apply the descending canonical variables. -/
theorem applyTelVars_eq_foldl : ∀ (As : List SExpr) (f : SExpr),
    applyTelVars As f =
      (telBvars As.length).foldl (fun g a => g.app a)
        (f.lift' (.skipN .refl As.length)) := by
  intro As
  induction As with
  | nil => intro f; simp [applyTelVars, telBvars]
  | cons A As ih =>
    intro f
    rw [applyTelVars, ih]
    change (telBvars As.length).foldl (fun g a => g.app a)
        ((f.lift.app (.bvar 0)).lift' (.skipN .refl As.length)) = _
    have hhead : (f.lift.app (.bvar 0)).lift' (.skipN .refl As.length) =
        (f.lift' (.skipN .refl (As.length + 1))).app (.bvar As.length) := by
      simp [SExpr.lift, ← SExpr.lift'_comp,
        Lift.comp_skip_skipN_refl, Lift.liftVar_skipN]
    rw [hhead]
    simp only [List.length_cons, telBvars, List.foldl_cons]

/-- Abstract a body over a dependent telescope. -/
def lamTel : List SExpr → SExpr → SExpr
  | [], e => e
  | A :: As, e => .lam A (lamTel As e)

/-- `mkInst` maps a Theory lambda telescope to the corresponding semantic
lambda telescope. -/
theorem mkInst_lamN (ls : List SLevel) :
    ∀ (Ts : List VExpr) (body : VExpr),
      SExpr.mkInst ls (VExpr.lamN Ts body) =
        lamTel (Ts.map (SExpr.mkInst ls)) (SExpr.mkInst ls body) := by
  intro Ts
  induction Ts with
  | nil => intro body; rfl
  | cons T Ts ih =>
    intro body
    simp only [VExpr.lamN, SExpr.mkInst, List.map_cons, lamTel, ih]

/-- `mkInst` maps a Theory Pi telescope to the corresponding semantic Pi
telescope. -/
theorem mkInst_forallN (ls : List SLevel) :
    ∀ (Ts : List VExpr) (body : VExpr),
      SExpr.mkInst ls (VExpr.forallN Ts body) =
        (Ts.map (SExpr.mkInst ls)).foldr .forallE
          (SExpr.mkInst ls body) := by
  intro Ts
  induction Ts with
  | nil => intro body; rfl
  | cons T Ts ih =>
    intro body
    simp only [VExpr.forallN, SExpr.mkInst, List.map_cons,
      List.foldr_cons, ih]

/-- `mkInst` commutes with a flattened application spine. -/
theorem mkInst_appN (ls : List SLevel) : ∀ (as : List VExpr) (f : VExpr),
    SExpr.mkInst ls (VExpr.appN f as) =
      (as.map (SExpr.mkInst ls)).foldl
        (fun (g a : SExpr) => g.app a) (SExpr.mkInst ls f)
  | [], _ => rfl
  | a :: as, f => by
    rw [VExpr.appN]
    exact mkInst_appN ls as (f.app a)

/-- The callback shape needed to use strong weakening before the ambient
`Params.Semantic` instance exists. -/
def StrongWeakening : Prop :=
  ∀ {rho : Lift} {Γ Γ' : List SExpr} {e₁ e₂ A : SExpr},
    Ctx.Lift' rho Γ Γ' → IsDefEqStrong Γ e₁ e₂ A →
      IsDefEqStrong Γ' (e₁.lift' rho) (e₂.lift' rho) (A.lift' rho)

/-- Evidence-rich validity of the binders in a dependent telescope.  Each
binder is checked in the context formed by the preceding binders, exactly
the orientation used by `List.foldr SExpr.forallE`. -/
inductive StrongTelescope : List SExpr → List SExpr → Prop where
  | nil : StrongTelescope Γ []
  | cons : (∃ u, IsDefEqStrong Γ A A (.sort u)) →
      StrongTelescope (A :: Γ) As → StrongTelescope Γ (A :: As)

/-- Recover binder validity from validity of a Pi tower. -/
theorem StrongTelescope.of_forall :
    ∀ {As : List SExpr} {Γ : List SExpr} {B : SExpr},
      (∃ u, IsDefEqStrong Γ (As.foldr .forallE B)
        (As.foldr .forallE B) (.sort u)) →
      StrongTelescope Γ As := by
  intro As
  induction As with
  | nil => intro Γ B _; exact .nil
  | cons A As ih =>
    intro Γ B h
    obtain ⟨_, hTower⟩ := h
    obtain ⟨hA, v, hRest⟩ := hTower.forallE_inv' (.inl rfl)
    exact .cons hA (ih ⟨v, hRest⟩)

/-- Forget a suffix of a valid telescope. -/
theorem StrongTelescope.prefix :
    ∀ {As Bs : List SExpr} {Γ : List SExpr},
      StrongTelescope Γ (As ++ Bs) → StrongTelescope Γ As := by
  intro As
  induction As with
  | nil => intro Bs Γ _; exact .nil
  | cons A As ih =>
    intro Bs Γ h
    cases h with
    | cons hA hAs => exact .cons hA (ih hAs)

/-- Enter a valid telescope prefix and retain the validity of its suffix in
the fully extended prefix context. -/
theorem StrongTelescope.suffix :
    ∀ {As Bs : List SExpr} {Γ : List SExpr},
      StrongTelescope Γ (As ++ Bs) →
      StrongTelescope (As.reverse ++ Γ) Bs := by
  intro As
  induction As with
  | nil =>
    intro Bs Γ h
    simpa using h
  | cons A As ih =>
    intro Bs Γ h
    cases h with
    | cons _ hRest =>
      simpa [List.append_assoc] using ih hRest

/-- Rebuild a valid Pi tower from valid binders and a valid result in the
fully extended context. -/
theorem StrongTelescope.close :
    ∀ {As : List SExpr} {Γ : List SExpr} {B : SExpr},
      StrongTelescope Γ As →
      (∃ u, IsDefEqStrong (As.reverse ++ Γ) B B (.sort u)) →
      ∃ u, IsDefEqStrong Γ (As.foldr .forallE B)
        (As.foldr .forallE B) (.sort u) := by
  intro As Γ B h
  induction h with
  | nil => simp
  | @cons Γ A As hA _ ih =>
    intro hB
    obtain ⟨u, hA⟩ := hA
    obtain ⟨v, hRest⟩ := ih (by
      simpa [List.append_assoc] using hB)
    exact ⟨.imax u v, .forallEDF hA hRest hRest⟩

/-- Insert an arbitrary list of newer binders in front of a context. -/
theorem Ctx.Lift'.skipAppend (Delta : List SExpr) :
    Ctx.Lift' (.skipN .refl Delta.length) Gamma (Delta ++ Gamma) := by
  induction Delta with
  | nil => exact .refl
  | cons A Delta ih => simpa using ih.skip

/-- The outermost binder of a valid telescope is a strongly typed canonical
variable in the fully opened telescope. -/
theorem StrongTelescope.head_bvar (weak : StrongWeakening)
    (h : StrongTelescope Gamma (A :: As)) :
    IsDefEqStrong ((A :: As).reverse ++ Gamma)
      (.bvar As.length) (.bvar As.length)
      (A.lift.lift' (.skipN .refl As.length)) := by
  cases h with
  | cons hA _ =>
    obtain ⟨u, hA⟩ := hA
    let W0 : Ctx.Lift' (.skip .refl) Gamma (A :: Gamma) := .skip .refl
    have hA0 := weak W0 hA
    have hb0 : IsDefEqStrong (A :: Gamma) (.bvar 0) (.bvar 0) A.lift :=
      .bvar .zero hA0
    let W : Ctx.Lift' (.skipN .refl As.reverse.length)
        (A :: Gamma) (As.reverse ++ (A :: Gamma)) :=
      Ctx.Lift'.skipAppend As.reverse
    have hb := weak W hb0
    simpa [List.append_assoc, Lift.liftVar_skipN] using hb

/-- Preserving an existing newest binder while inserting an outer one, then
instantiating the preserved binder by the new variable, cancels exactly. -/
theorem lift_cons_skip_inst_bvar0 (e : SExpr) :
    (e.lift' (.cons (.skip .refl))).inst (.bvar 0) = e := by
  rw [SExpr.inst, subst_lift']
  have hsubst :
      Subst.lift_l (.cons (.skip .refl)) (Subst.one (.bvar 0)) =
        Subst.id := by
    funext i
    cases i <;> rfl
  rw [hsubst, subst_id]

/-- A strongly typed function tower remains strongly typed after applying it
to the canonical variables of its telescope. -/
theorem applyTelVars_strong (weak : StrongWeakening) :
    ∀ {As : List SExpr} {Γ : List SExpr} {f B : SExpr},
      IsDefEqStrong Γ f f (As.foldr .forallE B) →
      IsDefEqStrong (As.reverse ++ Γ)
        (applyTelVars As f) (applyTelVars As f) B := by
  intro As
  induction As with
  | nil =>
    intro Γ f B H
    simpa [applyTelVars] using H
  | cons A As ih =>
    intro Γ f B H
    obtain ⟨_, hPiType⟩ := H.isType
    obtain ⟨⟨_, hA⟩, v, hRest⟩ :=
      hPiType.forallE_inv' (.inl rfl)
    let rho : Lift := .skip .refl
    let W : Ctx.Lift' rho Γ (A :: Γ) := .skip .refl
    have hFw := weak W H
    have hAw := weak W hA
    have hRestW := weak W.cons hRest
    have hb : IsDefEqStrong (A :: Γ) (.bvar 0) (.bvar 0) A.lift :=
      .bvar .zero hAw
    have hResult : IsDefEqStrong (A :: Γ)
        ((As.foldr .forallE B).lift' rho.cons |>.inst (.bvar 0))
        ((As.foldr .forallE B).lift' rho.cons |>.inst (.bvar 0))
        (.sort v) := by
      simpa [rho, lift_cons_skip_inst_bvar0] using hRest
    have hApp : IsDefEqStrong (A :: Γ)
        (f.lift.app (.bvar 0)) (f.lift.app (.bvar 0))
        (As.foldr .forallE B) := by
      simpa [rho, SExpr.lift, lift_cons_skip_inst_bvar0] using
        IsDefEqStrong.appDF hAw hRestW hFw hb hResult
    simpa [applyTelVars, List.append_assoc] using ih hApp

/-- Evidence-rich equality is preserved while a dependent function tower is
applied to the canonical variables of its telescope.  This is the congruence
form of `applyTelVars_strong`; unlike rebuilding the applications from two
self-typings, it retains the equality between the endpoints at every
prefix. -/
theorem applyTelVars_congr_strong (weak : StrongWeakening) :
    ∀ {As : List SExpr} {Γ : List SExpr} {f g B : SExpr},
      IsDefEqStrong Γ f g (As.foldr .forallE B) →
      IsDefEqStrong (As.reverse ++ Γ)
        (applyTelVars As f) (applyTelVars As g) B := by
  intro As
  induction As with
  | nil =>
    intro Γ f g B H
    simpa [applyTelVars] using H
  | cons A As ih =>
    intro Γ f g B H
    obtain ⟨_, hPiType⟩ := H.isType
    obtain ⟨⟨_, hA⟩, v, hRest⟩ :=
      hPiType.forallE_inv' (.inl rfl)
    let rho : Lift := .skip .refl
    let W : Ctx.Lift' rho Γ (A :: Γ) := .skip .refl
    have hHw := weak W H
    have hAw := weak W hA
    have hRestW := weak W.cons hRest
    have hb : IsDefEqStrong (A :: Γ) (.bvar 0) (.bvar 0) A.lift :=
      .bvar .zero hAw
    have hResult : IsDefEqStrong (A :: Γ)
        ((As.foldr .forallE B).lift' rho.cons |>.inst (.bvar 0))
        ((As.foldr .forallE B).lift' rho.cons |>.inst (.bvar 0))
        (.sort v) := by
      simpa [rho, lift_cons_skip_inst_bvar0] using hRest
    have hApp : IsDefEqStrong (A :: Γ)
        (f.lift.app (.bvar 0)) (g.lift.app (.bvar 0))
        (As.foldr .forallE B) := by
      simpa [rho, SExpr.lift, lift_cons_skip_inst_bvar0] using
        IsDefEqStrong.appDF hAw hRestW hHw hb hResult
    simpa [applyTelVars, List.append_assoc] using ih hApp

/-- An ordinary equality between two dependent towers can likewise be
applied to their canonical telescope variables when the left tower carries
the evidence-rich self-typing needed to type every prefix. -/
theorem applyTelVars_defeq (weak : StrongWeakening) :
    ∀ {As : List SExpr} {Γ : List SExpr} {f g B : SExpr},
      IsDefEqStrong Γ f f (As.foldr .forallE B) →
      IsDefEq Γ f g (As.foldr .forallE B) →
      IsDefEq (As.reverse ++ Γ)
        (applyTelVars As f) (applyTelVars As g) B := by
  intro As
  induction As with
  | nil =>
    intro Γ f g B _ H
    simpa [applyTelVars] using H
  | cons A As ih =>
    intro Γ f g B hF H
    obtain ⟨_, hPiType⟩ := hF.isType
    obtain ⟨⟨_, hA⟩, v, hRest⟩ :=
      hPiType.forallE_inv' (.inl rfl)
    let rho : Lift := .skip .refl
    let W : Ctx.Lift' rho Γ (A :: Γ) := .skip .refl
    have hHw := H.weak' W
    have hAw := weak W hA
    have hRestW := weak W.cons hRest
    have hb : IsDefEqStrong (A :: Γ) (.bvar 0) (.bvar 0) A.lift :=
      .bvar .zero hAw
    have hResult : IsDefEqStrong (A :: Γ)
        ((As.foldr .forallE B).lift' rho.cons |>.inst (.bvar 0))
        ((As.foldr .forallE B).lift' rho.cons |>.inst (.bvar 0))
        (.sort v) := by
      simpa [rho, lift_cons_skip_inst_bvar0] using hRest
    have hFApp : IsDefEqStrong (A :: Γ)
        (f.lift.app (.bvar 0)) (f.lift.app (.bvar 0))
        (As.foldr .forallE B) := by
      simpa [rho, SExpr.lift, lift_cons_skip_inst_bvar0] using
        IsDefEqStrong.appDF hAw hRestW (weak W hF) hb hResult
    have hApp : IsDefEq (A :: Γ)
        (f.lift.app (.bvar 0)) (g.lift.app (.bvar 0))
        (As.foldr .forallE B) := by
      simpa [rho, SExpr.lift, lift_cons_skip_inst_bvar0] using
        IsDefEq.appDF hHw hb.defeq
    simpa [applyTelVars, List.append_assoc] using ih hFApp hApp

/-- Abstract a strongly typed body over a valid dependent telescope. -/
theorem StrongTelescope.lamTel_strong :
    ∀ {As : List SExpr} {Γ : List SExpr} {e B : SExpr},
      StrongTelescope Γ As →
      IsDefEqStrong (As.reverse ++ Γ) e e B →
      IsDefEqStrong Γ (lamTel As e) (lamTel As e)
        (As.foldr .forallE B) := by
  intro As Γ e B h
  induction h with
  | nil =>
    intro hBody
    simpa [lamTel] using hBody
  | @cons Γ A As hA _ ih =>
    intro hBody
    obtain ⟨_, hA⟩ := hA
    have hInner := ih (by
      simpa [List.append_assoc] using hBody)
    obtain ⟨_, hRest⟩ := hInner.isType
    exact .lamDF hA hRest hRest hInner hInner

/-- Applying a freshly abstracted dependent telescope to its canonical
variables beta-reduces back to the original body, with evidence-rich typing
retained throughout. -/
theorem StrongTelescope.applyTelVars_lamTel (weak : StrongWeakening) :
    ∀ {As : List SExpr} {Γ : List SExpr} {e B : SExpr}
      (h : StrongTelescope Γ As),
      IsDefEqStrong (As.reverse ++ Γ) e e B →
      IsDefEqStrong (As.reverse ++ Γ)
        (applyTelVars As (lamTel As e)) e B := by
  intro As Γ e B h
  induction h with
  | nil =>
    intro hBody
    simpa [applyTelVars, lamTel] using hBody
  | @cons Γ A As hA hAs ih =>
    intro hBody
    obtain ⟨_, hA⟩ := hA
    have hInner := hAs.lamTel_strong (by
      simpa [List.append_assoc] using hBody)
    have hLam := (StrongTelescope.cons ⟨_, hA⟩ hAs).lamTel_strong
      (by simpa [List.append_assoc] using hBody)
    let rho : Lift := .skip .refl
    let W : Ctx.Lift' rho Γ (A :: Γ) := .skip .refl
    have hInnerW := weak W.cons hInner
    have hAw := weak W hA
    have hb : IsDefEqStrong (A :: Γ) (.bvar 0) (.bvar 0) A.lift :=
      .bvar .zero hAw
    have hApp : IsDefEqStrong (A :: Γ)
        ((SExpr.lam A (lamTel As e)).lift.app (.bvar 0))
        ((SExpr.lam A (lamTel As e)).lift.app (.bvar 0))
        (As.foldr .forallE B) := by
      have H := applyTelVars_congr_strong weak
        (As := [A]) (Γ := Γ) (f := SExpr.lam A (lamTel As e))
        (g := SExpr.lam A (lamTel As e))
        (B := As.foldr .forallE B) hLam
      simpa [applyTelVars] using H
    have hApp' : IsDefEqStrong (A :: Γ)
        ((SExpr.lam (A.lift' rho) ((lamTel As e).lift' rho.cons)).app
          (.bvar 0))
        ((SExpr.lam (A.lift' rho) ((lamTel As e).lift' rho.cons)).app
          (.bvar 0))
        (((As.foldr .forallE B).lift' rho.cons).inst (.bvar 0)) := by
      simpa [rho, SExpr.lift, lift_cons_skip_inst_bvar0] using hApp
    have hInst : IsDefEqStrong (A :: Γ)
        (((lamTel As e).lift' rho.cons).inst (.bvar 0))
        (((lamTel As e).lift' rho.cons).inst (.bvar 0))
        (((As.foldr .forallE B).lift' rho.cons).inst (.bvar 0)) := by
      simpa [rho, lift_cons_skip_inst_bvar0] using hInner
    have hBeta : IsDefEqStrong (A :: Γ)
        ((SExpr.lam A (lamTel As e)).lift.app (.bvar 0))
        (lamTel As e) (As.foldr .forallE B) := by
      simpa [rho, SExpr.lift, lift_cons_skip_inst_bvar0] using
        IsDefEqStrong.beta hInnerW hb hApp' hInst
    have hApplied := applyTelVars_congr_strong weak (As := As) hBeta
    have hRest := ih (by simpa [List.append_assoc] using hBody)
    simpa [applyTelVars, lamTel, SExpr.lift, rho,
      List.append_assoc] using hApplied.trans hRest

/-- Package a canonical beta-opened registered equation as one local strong
action.  Registration supplies only the ordinary tower equality; the
caller still provides the concrete pattern match, its finite checks, and
the strong typing of the exposed left body. -/
theorem registeredBody_strong (weak : StrongWeakening)
    {df : VDefEq} {ls : List SLevel} {Γ As : List SExpr}
    {e B : SExpr} {p : Pattern} {r : p.RHS × p.Check}
    {mcap : p.Path → SExpr}
    (hreg : Params.env.defeqs df) (hlen : ls.length = df.uvars)
    (hlhs : SExpr.mkInst ls df.lhs = lamTel As e)
    (htype : SExpr.mkInst ls df.type = As.foldr .forallE B)
    (hRhs : IsDefEqStrong Γ (SExpr.mkInst ls df.rhs)
      (SExpr.mkInst ls df.rhs) (SExpr.mkInst ls df.type))
    (hLeft : IsDefEqStrong (As.reverse ++ Γ) e e B)
    (hpat : Params.Pat p r) (hmatch : p.MatchesS e ls mcap)
    (happly : r.1.applyS ls mcap =
      applyTelVars As (SExpr.mkInst ls df.rhs))
    (dfs : List (SExpr × SExpr × SExpr))
    (hdefeqs : dfs.map (·.2) = r.2.defeqsS ls mcap)
    (hchecked : ∀ a b T, (T, a, b) ∈ dfs → IsDefEq (As.reverse ++ Γ) a b T) :
    IsDefEqStrong (As.reverse ++ Γ) e
      (applyTelVars As (SExpr.mkInst ls df.rhs)) B := by
  have hRhs' : IsDefEqStrong Γ (SExpr.mkInst ls df.rhs)
      (SExpr.mkInst ls df.rhs) (As.foldr .forallE B) := by
    simpa only [htype] using hRhs
  have hTel : StrongTelescope Γ As :=
    StrongTelescope.of_forall hRhs'.isType
  have hLhsTower : IsDefEqStrong Γ (lamTel As e) (lamTel As e)
      (As.foldr .forallE B) := hTel.lamTel_strong hLeft
  have hRaw : IsDefEq Γ (lamTel As e) (SExpr.mkInst ls df.rhs)
      (As.foldr .forallE B) := by
    rw [← hlhs, ← htype]
    exact .extra hreg hlen
  have hRawApplied := applyTelVars_defeq weak hLhsTower hRaw
  have hBeta := hTel.applyTelVars_lamTel weak hLeft
  have hsound0 : IsDefEq (As.reverse ++ Γ) e
      (applyTelVars As (SExpr.mkInst ls df.rhs)) B :=
    hBeta.symm.defeq.trans hRawApplied
  have hsound : IsDefEq (As.reverse ++ Γ) e (r.1.applyS ls mcap) B := by
    rw [happly]
    exact hsound0
  let action : Pattern.Action (As.reverse ++ Γ) r e ls mcap B := {
    pat := hpat
    matched := hmatch
    dfs := dfs
    defeqs := hdefeqs
    checked := hchecked
    sound := hsound }
  have hRight0 := applyTelVars_strong weak hRhs'
  have hRight : IsDefEqStrong (As.reverse ++ Γ)
      (r.1.applyS ls mcap) (r.1.applyS ls mcap) B := by
    rw [happly]
    exact hRight0
  have H := IsDefEqStrong.extra action hLeft hRight
  rw [happly] at H
  exact H

/-- Close a strongly typed local rule-body equality back into its registered
lambda tower.  All proper RHS prefixes and eta contractions are generated by
the recursion; rule-specific code need only build the fully opened leaf. -/
theorem closeTel_strong (weak : StrongWeakening) :
    ∀ {As : List SExpr} {Γ : List SExpr} {f e B : SExpr},
      IsDefEqStrong Γ f f (As.foldr .forallE B) →
      IsDefEqStrong (As.reverse ++ Γ) e (applyTelVars As f) B →
      IsDefEqStrong Γ (lamTel As e) f (As.foldr .forallE B) := by
  intro As
  induction As with
  | nil =>
    intro Γ f e B _ hLocal
    simpa [lamTel, applyTelVars] using hLocal
  | cons A As ih =>
    intro Γ f e B hHead hLocal
    obtain ⟨_, hPiType⟩ := hHead.isType
    obtain ⟨⟨_, hA⟩, _, hRest⟩ :=
      hPiType.forallE_inv' (.inl rfl)
    have hHeadApplied : IsDefEqStrong (A :: Γ)
        (f.lift.app (.bvar 0)) (f.lift.app (.bvar 0))
        (As.foldr .forallE B) := by
      have hSpecialized := applyTelVars_strong weak
        (As := [A]) (Γ := Γ) (f := f)
        (B := As.foldr .forallE B) hHead
      simpa [applyTelVars] using hSpecialized
    have hInner : IsDefEqStrong (A :: Γ)
        (lamTel As e) (f.lift.app (.bvar 0))
        (As.foldr .forallE B) := by
      apply ih hHeadApplied
      simpa [applyTelVars, List.append_assoc] using hLocal
    have hLam : IsDefEqStrong Γ
        (.lam A (lamTel As e)) (.lam A (f.lift.app (.bvar 0)))
        (.forallE A (As.foldr .forallE B)) := by
      exact .lamDF hA hRest hRest hInner hInner
    exact hLam.trans (.eta hHead hLam.hasType.2)

/-! ## §3 The β-collapse engine

`ruleCollapse` is the rule-independent heart of every generated-iota
replay.  D0 and D1 inline it once per rule; here it is proved once. -/

/-- Semantic translation of an iterated application. -/
theorem mk_appN : ∀ (as : List VExpr) (f : VExpr),
    SExpr.mk (VExpr.appN f as) =
      (as.map SExpr.mk).foldl (fun (g a : SExpr) => g.app a) (SExpr.mk f)
  | [], _ => rfl
  | a :: as, f => by
    show SExpr.mk (VExpr.appN (f.app a) as) = _
    rw [mk_appN as (f.app a)]
    rfl

@[simp] theorem map_mk_map_reify (as : List SExpr) :
    (as.map SExpr.reify).map SExpr.mk = as := by
  rw [List.map_map]
  exact List.map_id''' as fun e _ => SExpr.mk_reify e

include R in
/-- **The generic replay lemma.**  A registered rule whose left tower is a
lambda telescope over `body`, applied to a full well-typed argument spine,
β-collapses to the iterated instantiation of `body` — with no reference
whatever to which rule, which block, or which constructor is involved.

The spine premise is stated on the Theory side because Theory's `SpineWF`
has no conversion constructor; a rule's own glue builds it with `.cons`
from the per-argument typings it has just extracted, which is exactly the
form in which those typings arrive. -/
theorem ruleCollapse {Γ : List SExpr} {df : VDefEq}
    {binders : List VExpr} {body result : VExpr}
    {ls : List SLevel} {args : List SExpr}
    (hΓ : CtxValid Γ)
    (hreg : Params.env.defeqs df)
    (hlhs : df.lhs = VExpr.lamN binders body)
    (_htype : df.type = VExpr.forallN binders result)
    (_hls : ls.length = df.uvars)
    (hlen : args.length = binders.length)
    (hspine : Params.env.SpineWF Params.univs (Γ.map SExpr.reify)
      (VExpr.forallN (binders.map (VExpr.instL (ls.map SLevel.reify)))
        (result.instL (ls.map SLevel.reify)))
      (args.map SExpr.reify)
      (VExpr.instRev (result.instL (ls.map SLevel.reify))
        (args.map SExpr.reify))) :
    ∃ B, IsDefEq Γ
      (args.foldl (fun (f a : SExpr) => f.app a) (SExpr.mkInst ls df.lhs))
      (SExpr.mk ((body.instL (ls.map SLevel.reify)).instRev
        (args.map SExpr.reify))) B := by
  have hvls : ∀ l ∈ ls.map SLevel.reify, l.WF Params.univs := by
    intro l hl
    simp only [List.mem_map] at hl
    obtain ⟨sl, -, rfl⟩ := hl
    exact SLevel.reify_wf sl
  have hlenV : (args.map SExpr.reify).length =
      (binders.map (VExpr.instL (ls.map SLevel.reify))).length := by
    simp only [List.length_map]
    exact hlen
  -- the rule's left tower, typed at the working context
  have hlhsClosed :=
    (Params.henv.defEqWF hreg).1.instL (ls := ls.map SLevel.reify) hvls
  have hlhsGamma : Params.env.HasType Params.univs (Γ.map SExpr.reify)
      (df.lhs.instL (ls.map SLevel.reify))
      (df.type.instL (ls.map SLevel.reify)) :=
    hlhsClosed.weak0 Params.henv
  rw [hlhs, VExpr.instL_lamN] at hlhsGamma
  obtain ⟨hTel, bodyType, hbody⟩ :=
    VEnv.HasType.lamN_wf Params.henv hΓ hlhsGamma
  -- retarget the canonical spine at the recovered body type
  have hspineBody := VEnv.SpineWF.retarget hspine hlenV bodyType
  have hcollapseV :=
    VEnv.IsDefEq.appN_lamN Params.henv hTel hbody hspineBody hlenV
  -- transfer back into the quotiented syntax
  have hlevels := (VEnv.CtxStrong.strong Params.henv hΓ).levelWF
  have hcollapseS := SExpr.IsDefEq.mkS R.structEta hcollapseV hlevels
  rw [ctx_mk_reify] at hcollapseS
  rw [mk_appN, map_mk_map_reify] at hcollapseS
  have hhead : SExpr.mk (VExpr.lamN
        (binders.map (VExpr.instL (ls.map SLevel.reify)))
        (body.instL (ls.map SLevel.reify))) = SExpr.mkInst ls df.lhs := by
    rw [← VExpr.instL_lamN, ← hlhs]
    exact SExpr.mk_instL_map_reify df.lhs ls
  rw [hhead] at hcollapseS
  exact ⟨_, hcollapseS⟩

include R in
/-- S-expression-facing form of `ruleCollapse`.  A caller that has already
built the capture `SpineWF` need not separately reconstruct its strict
Theory counterpart: `vSpineOfSpineWF_forallN` peels all conversions against
the registered rule's exact Pi telescope, after which the generic
beta-collapse engine applies unchanged. -/
theorem ruleCollapseOfSpineWF {Γ : List SExpr} {df : VDefEq}
    {binders : List VExpr} {body result : VExpr}
    {ls : List SLevel} {args : List SExpr} {A : SExpr}
    (hΓ : CtxValid Γ)
    (hreg : Params.env.defeqs df)
    (hlhs : df.lhs = VExpr.lamN binders body)
    (htype : df.type = VExpr.forallN binders result)
    (hls : ls.length = df.uvars)
    (hlen : args.length = binders.length)
    (hspine : SpineWF Γ (SExpr.mkInst ls df.type) args A) :
    ∃ B, IsDefEq Γ
      (args.foldl (fun (f a : SExpr) => f.app a)
        (SExpr.mkInst ls df.lhs))
      (SExpr.mk ((body.instL (ls.map SLevel.reify)).instRev
        (args.map SExpr.reify))) B := by
  let vls := ls.map SLevel.reify
  have hvls : ∀ l ∈ vls, l.WF Params.univs := by
    intro l hl
    simp only [vls, List.mem_map] at hl
    obtain ⟨sl, -, rfl⟩ := hl
    exact SLevel.reify_wf sl
  have hlhsClosed :=
    (Params.henv.defEqWF hreg).1.instL (ls := vls) hvls
  have hlhsGamma : Params.env.HasType Params.univs
      (Γ.map SExpr.reify) (df.lhs.instL vls) (df.type.instL vls) :=
    hlhsClosed.weak0 Params.henv
  have hctxLevels := (VEnv.CtxStrong.strong Params.henv hΓ).levelWF
  obtain ⟨u, htypeV⟩ := hlhsGamma.isType Params.henv hΓ
  have htypeS := SExpr.IsDefEq.mkS R.structEta htypeV hctxLevels
  rw [ctx_mk_reify] at htypeS
  have hcanonV : df.type.instL vls =
      VExpr.forallN (binders.map (VExpr.instL vls))
        (result.instL vls) := by
    rw [htype, VExpr.instL_forallN]
  rw [hcanonV] at htypeS
  have hhead : SExpr.mk
      (VExpr.forallN (binders.map (VExpr.instL vls))
        (result.instL vls)) = SExpr.mkInst ls df.type := by
    calc
      _ = SExpr.mk (df.type.instL vls) := congrArg SExpr.mk hcanonV.symm
      _ = SExpr.mkInst ls df.type := by
        simpa only [vls] using SExpr.mk_instL_map_reify df.type ls
  have hheadEq : TypesDefEq Γ
      (SExpr.mk (VExpr.forallN (binders.map (VExpr.instL vls))
        (result.instL vls))) (SExpr.mkInst ls df.type) := by
    refine ⟨SLevel.mk u, ?_⟩
    rw [← hhead]
    simpa only [SExpr.mk] using htypeS
  have hlevel : (VExpr.forallN (binders.map (VExpr.instL vls))
      (result.instL vls)).LevelWF Params.univs := by
    have h := (hlhsGamma.levelWF hctxLevels).2.2
    rwa [hcanonV] at h
  have hspineV := vSpineOfSpineWF_forallN R hΓ
    (n := binders.length)
    (binders := binders.map (VExpr.instL vls))
    (result := result.instL vls) (args := args)
    (by simp) hlen hlevel hheadEq hspine
  exact ruleCollapse R hΓ hreg hlhs htype hls hlen hspineV

include R in
/-- Retarget `ruleCollapseOfSpineWF` directly to a concrete reduction site.
The only rule-specific input left is the finite syntax computation identifying
the instantiated generated left body with the matched redex.  The capture
spine both supplies the strict Theory spine used by beta collapse and types
the applied registered left tower at the site's result `A`; type uniqueness
then removes the existential result type exposed by the raw collapse. -/
theorem ruleCollapseOfSpineWF_at {Γ : List SExpr} {df : VDefEq}
    {binders : List VExpr} {body result : VExpr}
    {ls : List SLevel} {args : List SExpr} {A redex : SExpr}
    (hΓ : CtxValid Γ)
    (hreg : Params.env.defeqs df)
    (hlhs : df.lhs = VExpr.lamN binders body)
    (htype : df.type = VExpr.forallN binders result)
    (hls : ls.length = df.uvars)
    (hlen : args.length = binders.length)
    (hspine : SpineWF Γ (SExpr.mkInst ls df.type) args A)
    (hbody : SExpr.mk ((body.instL (ls.map SLevel.reify)).instRev
      (args.map SExpr.reify)) = redex) :
    IsDefEq Γ redex
      (args.foldl (fun (f a : SExpr) => f.app a)
        (SExpr.mkInst ls df.lhs)) A := by
  obtain ⟨B, hcollapse⟩ := ruleCollapseOfSpineWF R hΓ hreg hlhs htype
    hls hlen hspine
  rw [hbody] at hcollapse
  have hhead : IsDefEq Γ (SExpr.mkInst ls df.lhs)
      (SExpr.mkInst ls df.lhs) (SExpr.mkInst ls df.type) :=
    (IsDefEq.extra hreg hls).hasType.1
  have happlied := hspine.hasType hhead
  obtain ⟨_, hBA⟩ := typeUniq R hΓ hcollapse.hasType.1 happlied
  exact hBA.defeqDF hcollapse.symm

include R in
/-- Definitional-equality variant of `ruleCollapseOfSpineWF_at`.  This is
the form needed by parameterized constructors: after substitution the
generated body rebuilds the constructor with the recursor-side parameter,
so the finite site proof relates that body to the matched constructor using
the rule's checked parameter equality rather than by syntactic equality. -/
theorem ruleCollapseOfSpineWF_at_defeq {Γ : List SExpr} {df : VDefEq}
    {binders : List VExpr} {body result : VExpr}
    {ls : List SLevel} {args : List SExpr} {A redex : SExpr}
    (hΓ : CtxValid Γ)
    (hreg : Params.env.defeqs df)
    (hlhs : df.lhs = VExpr.lamN binders body)
    (htype : df.type = VExpr.forallN binders result)
    (hls : ls.length = df.uvars)
    (hlen : args.length = binders.length)
    (hspine : SpineWF Γ (SExpr.mkInst ls df.type) args A)
    (hbody : IsDefEq Γ
      (SExpr.mk ((body.instL (ls.map SLevel.reify)).instRev
        (args.map SExpr.reify))) redex A) :
    IsDefEq Γ redex
      (args.foldl (fun (f a : SExpr) => f.app a)
        (SExpr.mkInst ls df.lhs)) A := by
  obtain ⟨_, hcollapse⟩ := ruleCollapseOfSpineWF R hΓ hreg hlhs htype
    hls hlen hspine
  obtain ⟨_, hBA⟩ := typeUniq R hΓ hcollapse.hasType.2 hbody.hasType.1
  exact (hBA.defeqDF hcollapse |>.trans hbody).symm

include R in
/-- Finish both site obligations from a raw capture spine.  Prefix replay
naturally ends at the rule's canonical instantiated result `B`; the concrete
typed redex may be indexed by a converted result `A`.  Beta collapse first
types the redex at `B`, after which type uniqueness supplies the single
`SpineWF.ret` conversion and retargets the collapse in lockstep. -/
theorem ruleReplayOfRawSpine {Γ : List SExpr} {df : VDefEq}
    {binders : List VExpr} {body result : VExpr}
    {ls : List SLevel} {args : List SExpr} {A B redex : SExpr}
    (hΓ : CtxValid Γ)
    (hreg : Params.env.defeqs df)
    (hlhs : df.lhs = VExpr.lamN binders body)
    (htype : df.type = VExpr.forallN binders result)
    (hls : ls.length = df.uvars)
    (hlen : args.length = binders.length)
    (hraw : SpineWF Γ (SExpr.mkInst ls df.type) args B)
    (hbody : SExpr.mk ((body.instL (ls.map SLevel.reify)).instRev
      (args.map SExpr.reify)) = redex)
    (hredex : IsDefEq Γ redex redex A) :
    SpineWF Γ (SExpr.mkInst ls df.type) args A ∧
      IsDefEq Γ redex
        (args.foldl (fun (f a : SExpr) => f.app a)
          (SExpr.mkInst ls df.lhs)) A := by
  have hsiteB := ruleCollapseOfSpineWF_at R hΓ hreg hlhs htype hls hlen
    hraw hbody
  obtain ⟨_, hBA⟩ := typeUniq R hΓ hsiteB.hasType.1 hredex
  exact ⟨.ret hraw hBA, hBA.defeqDF hsiteB⟩

include R in
/-- Checked-parameter form of `ruleReplayOfRawSpine`.  Here the finite body
calculation is a typed definitional equality at the raw canonical result,
which is exactly what parameterized generated constructors provide after
their `Pattern.Check` equality is consumed. -/
theorem ruleReplayOfRawSpine_defeq {Γ : List SExpr} {df : VDefEq}
    {binders : List VExpr} {body result : VExpr}
    {ls : List SLevel} {args : List SExpr} {A B redex : SExpr}
    (hΓ : CtxValid Γ)
    (hreg : Params.env.defeqs df)
    (hlhs : df.lhs = VExpr.lamN binders body)
    (htype : df.type = VExpr.forallN binders result)
    (hls : ls.length = df.uvars)
    (hlen : args.length = binders.length)
    (hraw : SpineWF Γ (SExpr.mkInst ls df.type) args B)
    (hbody : IsDefEq Γ
      (SExpr.mk ((body.instL (ls.map SLevel.reify)).instRev
        (args.map SExpr.reify))) redex B)
    (hredex : IsDefEq Γ redex redex A) :
    SpineWF Γ (SExpr.mkInst ls df.type) args A ∧
      IsDefEq Γ redex
        (args.foldl (fun (f a : SExpr) => f.app a)
          (SExpr.mkInst ls df.lhs)) A := by
  have hsiteB := ruleCollapseOfSpineWF_at_defeq R hΓ hreg hlhs htype
    hls hlen hraw hbody
  obtain ⟨_, hBA⟩ := typeUniq R hΓ hsiteB.hasType.1 hredex
  exact ⟨.ret hraw hBA, hBA.defeqDF hsiteB⟩

/-! ## §4 The site assembler

Given the collapse and a rule's own capture data, the reduction site is
assembled generically.  The `Pattern.Check` obligations are an explicit
hypothesis: at a *general* matched redex the parameter checks are not
derivable from the site's typing inputs (they need injectivity of a stuck
inductive-type application, `L4L-18A′` strength), so an instance either
proves them for its block or parks them, and this engine stays neutral. -/

include R in
/-- **The generic site assembler.**  Every field of `IotaReductionSite`
except `typing`/`matched` (inputs) and `checked` (the parked obligation) is
produced here from the collapse and the capture inventory. -/
noncomputable def iotaSiteOf
    {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {Γ : List SExpr} {A majorTerm : SExpr} {recLs ctorLs : List SLevel}
    {recArgs ctorArgs : List SExpr}
    {mcap : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
    {captureType : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
    (rule : Pattern.IotaRule r)
    (captureTyping : Pattern.CaptureTyping Γ mcap captureType)
    (hΓ : CtxValid Γ)
    (typing : Pattern.IotaTyping Γ rec ctor recLs ctorLs
      recArgs ctorArgs majorTerm A)
    (matched : (RecursorIotaPattern rec major ctor arity).MatchesS
      ((recArgs.foldr (fun (a f : SExpr) => f.app a) (SExpr.const rec recLs)).app
        (ctorArgs.foldr (fun (a f : SExpr) => f.app a)
          (SExpr.const ctor ctorLs))) recLs mcap)
    (levelsLength : recLs.length = rule.df.uvars)
    /- the rule's own capture spine, at the instantiated rule type -/
    (hspine : SpineWF Γ (SExpr.mkInst recLs rule.df.type)
      (rule.capturePaths.map mcap) A)
    /- the β-collapse of the applied left tower back to the matched redex -/
    (lhsCollapse : IsDefEq Γ
      ((recArgs.foldr (fun (a f : SExpr) => f.app a) (SExpr.const rec recLs)).app
        (ctorArgs.foldr (fun (a f : SExpr) => f.app a)
          (SExpr.const ctor ctorLs)))
      ((rule.capturePaths.map mcap).foldl
        (fun (f a : SExpr) => f.app a) (SExpr.mkInst recLs rule.df.lhs)) A)
    /- the parked `Pattern.Check` discharge -/
    (dfs : List (SExpr × SExpr × SExpr))
    (hdefeqs : dfs.map (·.2) = r.2.defeqsS recLs mcap)
    (hchecked : ∀ a b B, (B, a, b) ∈ dfs → IsDefEq Γ a b B) :
    Pattern.IotaReductionSite Γ r rule recLs ctorLs recArgs ctorArgs
      majorTerm A mcap captureType captureTyping where
  typing := typing
  matched := matched
  levelsLength := levelsLength
  captureSpine := pathSpineOfSpineWF R hΓ captureTyping.typed hspine
  lhsCollapse := lhsCollapse
  dfs := dfs
  defeqs := hdefeqs
  checked := hchecked


/-! ## §5 Level extraction and the reified-spine bridge (R3)

Two further generic pieces consumed by block instances whose constructors
carry universe parameters (the first being D2's `Tree`/`TreeList`).

* `sortInj` — the quotiented-level form of sort injectivity: two
  definitionally equal sorts have *equal* `SLevel`s.  It rides on
  `VEnv.IsDefEqU.sort_inv`, one of the sorried 16C′-cluster leaves in
  `Theory/Typing/Injectivity.lean` that `typeUniq` (via
  `VEnv.IsDefEq.uniq`) already consumes, so it adds no admission beyond the
  engine's existing closure.
* `spineOfVSpineReify` — the working-context instance of
  `VEnv.SpineWF.mkS`: a Theory-side spine at the reified context transfers
  to a quotiented-syntax spine at the working context itself.  A rule's
  glue builds the Theory-side spine once (the form `ruleCollapse` consumes)
  and obtains its `iotaSiteOf` capture spine from this bridge instead of
  rebuilding it by hand. -/

/-- `SLevel.succ` is injective: the quotient is by pointwise evaluation and
successor is pointwise `+1`. -/
theorem _root_.Lean4Lean.SLevel.succ_inj {u v : SLevel}
    (h : SLevel.succ u = SLevel.succ v) : u = v := by
  apply Subtype.ext
  funext ns
  have h' := congrArg (·.1 ns) h
  change u.1 ns + 1 = v.1 ns + 1 at h'
  omega

include R in
/-- Sort injectivity at the quotiented level: definitionally equal sorts
have equal `SLevel`s.  Inherits the 16C′ `sort_inv` leaf already inside the
engine's closure. -/
theorem sortInj {Γ : List SExpr} {u v : SLevel}
    (hΓ : CtxValid Γ) (h : TypesDefEq Γ (.sort u) (.sort v)) : u = v := by
  obtain ⟨w, h⟩ := h
  have hV := h.reify hΓ
  have hU : Params.env.IsDefEqU Params.univs (Γ.map SExpr.reify)
      (.sort u.reify) (.sort v.reify) := ⟨_, hV⟩
  have hequiv := hU.sort_inv R.wf hΓ
  calc u = SLevel.mk u.reify := (SLevel.mk_reify u).symm
    _ = SLevel.mk v.reify :=
        SLevel.mk_eq (SLevel.reify_wf u) (SLevel.reify_wf v) hequiv
    _ = v := SLevel.mk_reify v

/-- Transfer a Theory-side spine over the reified working context back into
the quotiented syntax at the working context itself. -/
theorem spineOfVSpineReify (hstruct : Params.StructureEtaSound)
    {Γ : List SExpr} {T Res : VExpr} {args : List SExpr}
    (hΓ : CtxValid Γ)
    (H : Params.env.SpineWF Params.univs (Γ.map SExpr.reify) T
      (args.map SExpr.reify) Res) :
    SpineWF Γ (SExpr.mk T) args (SExpr.mk Res) := by
  have hlevels : OnCtx (Γ.map SExpr.reify)
      (fun _ A => A.LevelWF Params.univs) :=
    (VEnv.CtxStrong.strong Params.henv hΓ).levelWF
  have hS := VEnv.SpineWF.mkS hstruct H hlevels
  rw [ctx_mk_reify, map_mk_map_reify] at hS
  exact hS

/-! ## Axiom closures

`ruleCollapse` — the entire reify/`instL_lamN`/`lamN_wf`/`retarget`/
`appN_lamN`/`mkS` chain that D0 and D1 inline once per rule — is
`sorryAx`-free: the generic engine adds no admission of its own.

`ruleCollapseOfSpineWF` adds conversion-aware spine peeling to that engine;
the peeling uses `typeUniq`, so this convenience wrapper inherits the
ladder's existing `sorryAx` even though `ruleCollapse` itself does not.
`spinePrefixForallN` uses the same conversion-aware peeling and has the same
closure.

`typeUniq` (and everything downstream of it, including `iotaSiteOf`)
inherits the ladder's existing `sorryAx` through `VEnv.IsDefEq.uniq`, the
16C′ leaf that `SExprParamsD1.lean`'s `d1SortInvS` already carries.  Nothing
here consumes `VInductDecl.BlockGenerationChecked.pat_wf`, whose own
`sorryAx` would close a circle back through the sorried `sort_inv`. -/

/-- info: 'Lean4Lean.SExpr.ruleCollapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ruleCollapse

/-- info: 'Lean4Lean.SExpr.spinePrefixForallN' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms spinePrefixForallN

/-- info: 'Lean4Lean.Pattern.IotaTyping.redexSelf' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Pattern.IotaTyping.redexSelf

/-- info: 'Lean4Lean.SExpr.ruleCollapseOfSpineWF' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ruleCollapseOfSpineWF

/-- info: 'Lean4Lean.SExpr.ruleCollapseOfSpineWF_at' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ruleCollapseOfSpineWF_at

/-- info: 'Lean4Lean.SExpr.ruleCollapseOfSpineWF_at_defeq' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ruleCollapseOfSpineWF_at_defeq

/-- info: 'Lean4Lean.SExpr.ruleReplayOfRawSpine' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ruleReplayOfRawSpine

/-- info: 'Lean4Lean.SExpr.ruleReplayOfRawSpine_defeq' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ruleReplayOfRawSpine_defeq

/-- info: 'Lean4Lean.SExpr.mk_appN' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms mk_appN

/-- info: 'Lean4Lean.SExpr.typeUniq' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms typeUniq

/-- info: 'Lean4Lean.SExpr.iotaSiteOf' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms iotaSiteOf

/-- info: 'Lean4Lean.SExpr.sortInj' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sortInj

/-- info: 'Lean4Lean.SExpr.spineOfVSpineReify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms spineOfVSpineReify

end SExpr
end Lean4Lean
