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

`typeUniq` (and everything downstream of it, including `iotaSiteOf`)
inherits the ladder's existing `sorryAx` through `VEnv.IsDefEq.uniq`, the
16C′ leaf that `SExprParamsD1.lean`'s `d1SortInvS` already carries.  Nothing
here consumes `VInductDecl.BlockGenerationChecked.pat_wf`, whose own
`sorryAx` would close a circle back through the sorried `sort_inv`. -/

/-- info: 'Lean4Lean.SExpr.ruleCollapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ruleCollapse

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
