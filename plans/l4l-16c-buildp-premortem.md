# L4L-16C buildP pre-mortem: gap map for the final adequacy-leaf step

## Worker resolution (2026-08-14, after review integration)

The signature audit was correct to stop the leaf-local draft.  The moving
working tree now resolves the mapped gaps as follows:

- **G1 is closed.** `FixedHeadResult` and
  `iotaDefEq_of_ctorExactAt_fixedHead` no longer require `Ctx.WF`; the
  target-context well-formedness dependency belongs only at the joint
  uniqueness/root-reduction boundary.
- **The old G2 obligation is obsolete.** The retained consumer uses
  `RDeepChildren (fun _ => True)`, whose laws are already complete; it does
  not require a `Laws FixedHeadResult` instance.
- **G3 exposed an additional depth mismatch, now repaired.**
  `FixedHeadResultAt hX depth` is retained at the same Nat index as
  `SelfAdequateAt`; `FixedHeadStep` receives that freshly constructed
  same-depth self-adequacy result.  Only after the Nat-first recursion has
  produced every depth does `FixedHeadResult.of_forall_at` recover the old
  depth-polymorphic contract.  The adequacy module builds after this change.
- **G4 chooses route 2.** Route 1 cannot instantiate the existing
  `CtorChain.NativeAlgebra` safely: a native exact link is stated in an
  arbitrary relation `J`, while
  `iotaDefEq_of_ctorExactAt_fixedHead` is stated in canonical `LR` at both
  the recursor prefix and generated RHS.  An `unlift` frame does not permit
  projecting arbitrary high-level fields or the canonical prefix into `J`.
  Thus a uniqueness-free leaf-local fold would recreate the already rejected
  native/root projection.  The main adequacy construction must expose the
  predecessor limited-uniqueness/lower-adequacy package through the existing
  level-indexed joint boundary; it must not manufacture a completed
  `JointBuilder` inside the current direct induction.
- **G5 remains live** and is part of the fixed-head application-chain proof,
  not an admissible raw-to-semantic conversion shortcut.

This resolution supersedes the alternatives in G4 below; the rest of the
document remains as the snapshot evidence that motivated it.

Purpose: before the worker writes the "consumer-specific fixed-head `buildP`
application-chain algebra" (the last named obligation per
`plans/l4l-16c-adequacy-log.md` final entry and
`plans/l4l-16-completion-plan.md` §3 line 649), map exactly what that step
must consume, whether each input is actually available at the sorry site,
and where erasure-failure-mode #7 could hide. All claims carry file:line
references to the snapshot below. Uncertainty is flagged inline; nothing
below was elaborated through Lean (read-only analysis).

## Snapshot (MOVING TARGET — verify before relying on line numbers)

Read window: 2026-08-14 ~03:35–03:55 EDT. A worker session is actively
editing these files; mtimes were checked at the start and end of the read
session and did not change in between, so all line numbers are consistent
with this exact state:

| file | mtime | size |
|---|---|---|
| `Lean4Lean/Experimental/ShapeLogRel.lean` | 2026-08-14 01:21:27 | 583544 B |
| `Lean4Lean/Experimental/ShapeLogRelAdequacy.lean` | 2026-08-14 03:31:07 | 181248 B |
| `Lean4Lean/Experimental/SExpr.lean` | 2026-08-13 13:07:35 | 182986 B |

Sole adequacy-file sorry: `ShapeLogRelAdequacy.lean:3058`. (SExpr.lean has
four separate sorries at 3516/3739/3842/3908 — L4L-16B′ scope, not this
leaf.) Re-locate after any edit with
`grep -n "sorry" Lean4Lean/Experimental/ShapeLogRelAdequacy.lean`.

Abbreviations: SLR = ShapeLogRel.lean, ADQ = ShapeLogRelAdequacy.lean,
SE = SExpr.lean. All Lean names live under `Lean4Lean.SExpr` unless noted.

## The sorry site

### Enclosing structure (outermost → innermost)

1. `LR.adequacy` (ADQ:2856-2858): `(H : IsDefEqStrong Γ M N A) (hM :
   LE_Interp ρ m.T M) (hA : LE_Interp ρ a.T A) (hmem : m.HasType a) :
   Adequate Γ₀ Γ ρ M N A m a`, by `induction H generalizing ρ n m a`.
   **No `Ctx.WF` premise anywhere in the statement.** `Adequate`
   (ADQ:9-13) quantifies over `LR.SubstWF Γ₀ σ σ' Γ ρ`.
2. `| @const c ci Γ ls u h1 h2 hTy F hF hDef ihTy ihF ihDef` (ADQ:2886).
3. `cases hM.witness`, const branch (ADQ:2891):
   `| @const _ _ ci' _ m' _ a' _ R hreg _ hle hm'ty hA' hConst hR`.
   This binds the proof-relevant callback
   **`hR : ∀ m e, R m e → LE_Interp.Witness ρ m e`** and
   `hA' : LE_Interp.Witness ρ a' (mkInst ls ci.type)` (the registered
   type's witness tree).
4. `suffices`-block per substitution; `intro σ σ' W` with
   `W : LR.SubstWF Γ₀ σ σ' Γ ρ` (ADQ:2893-2896).
5. `hC : LE_Interp.Const c ls (LE_Interp.Lower R) [] m.T` (ADQ:2898-2899);
   `cases hC with | lam hrec hlam` + `rename_i nsem hlen_sem fsem`
   (ADQ:2902-2903). Per `LE_Interp.Const.lam` (SLR:3542-3543):
   `hrec : ∀ x y : WShape nsem, (x, y) ∈ fsem →
   LE_Interp.Const c ls (LE_Interp.Lower R) [x] y.T`.
6. `hmem.unfold` lam branch `| @lam k f a₁ a₂ htm` (ADQ:2908); soundness
   unpack of the constant's type (ADQ:2909-2915, the `toValTy` pattern);
   `split <;> rename_i hf`, Pi-observation unpack
   `⟨A₁, A₂, _, _, u₁, u₂, hred, _, hA₁, hA₂, hvalA₁, hpi⟩` (ADQ:2919).
7. `have eval : ∀ {k'} (hn : k ≤ k') (hnsem hnArgs : nsem ≤ k') {x y p x₀
   y₀}, p.HasType (a₁.lift k') → Γ₀ ⊢ x ≡ y : A₁ → (LR Γ₀).DefEq x y A₁ p
   (a₁.lift k') → (x₀,y₀) ∈ fsem → x₀.lift k' ≤ p → (f.lift k').app p ≤
   y₀.lift k' → (LR Γ₀).DefEq ((const c ls).app x) ((const c ls).app y)
   (A₂.inst x) ((f.lift k').app p) ((a₂.lift k').app p)` (ADQ:2928-2937).
   Inside: `hPiK hAK hout hchildLe hType₀ hTypePi hConstPi hAppTerm
   hAppType hAppSpineX hAppCodomain hAppSpineY hA₁K hAppPair hAppAligned
   hAppLeaf` (ADQ:2939-3020); `hAppLeaf : LR.PatternLeafSpine Γ₀ (LR Γ₀)
   (mkInst ls ci.type) [x] [y] [p] (A₂.inst x) ((f.lift k').app p)
   ((a₂.lift k').app p)` (ADQ:2997-3020).
8. `evalPat : LR.PatternLeafDefEq Γ₀ c ls (LE_Interp.Lower R) :=
   LR.PatternLeafDefEq.of_iota (by …)` (ADQ:3021-3059) — the sorry is the
   tail of this by-block. After it, `eval` is consumed by `LR.constDefEq`
   (ADQ:3060-3065) and wrapped into `LogRel.DefEqRect.diagonal` for
   `LR.constLamDefEq` (ADQ:3066-3069) — diagonal suffices here because
   both heads are the same `const c ls`.

### Hypotheses introduced inside the `of_iota` block (ADQ:3027-3057)

`of_iota` (ADQ:2178-2185) reduces `PatternLeafDefEq` to `IotaLeafDefEq`
(ADQ:1302-1326) instantiated at `R := LE_Interp.Lower R`. The intro at
ADQ:3027-3029 binds (types per ADQ:1304-1323):

- `nI : Nat`, `rargsI : List (WShape nI)`, `rec major ctor arity`,
  `rI : (RecursorIotaPattern rec major ctor arity).RHS × ….Check`,
  `mcapI : ….Path → TShape`, `xsI ysI CHeadI AI : SExpr`,
  `outI outTyI : WShape nI`
- `hpatI : Params.Pat (RecursorIotaPattern rec major ctor arity) rI`
- `hmatchI : LE_Interp.Matches (RecursorIotaPattern …) c rargsI mcapI`
- `hrhsI : LE_Interp.RHS ls mcapI (LE_Interp.Lower R) outI.T rI.1`
- `hleafI : LR.PatternLeafSpine Γ₀ (LR Γ₀) CHeadI xsI ysI rargsI AI outI
  outTyI`
- `htermI : Γ₀ ⊢ xsI.foldr app-fold (const c ls) ≡ ysI.foldr … : AI`
- `hAIType : ∃ u, Γ₀ ⊢ AI : .sort u`;
  `hheadI : Γ₀ ⊢ const c ls : CHeadI`
- `hspineXI hspineYI : SExpr.SpineWF Γ₀ CHeadI xsI.reverse AI` (resp. ysI)
- `houtI : outI.HasType outTyI`; `hAI : (LR Γ₀).TyDefEq AI AI outTyI`

Then `cases hmatchI | @app fPat nCtor head recShapes mrec aPat ctorHead
ctorShapes mctor hmfI hmaI` (ADQ:3030-3032) yields
- `hmfI : LE_Interp.Matches (Pattern.varN (.const rec) major) rec
  recShapes mrec` (recursor prefix, successor depth) and
- `hmaI : LE_Interp.Matches (Pattern.varN (.const ctor) arity) ctor
  ctorShapes mctor` (constructor, one depth lower);

`rcases hleafI` (ADQ:3033-3037) destructures the `PatternLeafSpine`
fields (ADQ:1144-1168): `majorX recXs majorY recYs majorShape recShapesI
majorTypeShape resultShape resultTypeShape hxs hys hrargs houtEq houtTyEq
hlastPair hpMajor hresultType htyMajor hvMajor halignedI hPiI`; substs
collapse `xsI = majorX :: recXs`, `ysI = majorY :: recYs`, `rargsI =
majorShape :: recShapes`, `outI = resultShape.app majorShape`, `outTyI =
resultTypeShape.app majorShape`, and identify `ctorHead = ctor`
(ADQ:3038-3048). Then:
- `hctorClass : Params.classify ctor = some (.ctor
  ctorShapes.reverse.length)` (ADQ:3049-3052)
- `hmajorCtor := LR.DefEq.ctor'_inv hctorClass hpMajor hvMajor`
  (ADQ:3053-3054): by SLR:11040-11047 this is
  `LRS.IndTyHead Γ₀ D ∧ LRS.CtorDefEq Γ₀ (LR Γ₀) majorX majorY
  (WShape.ctor ctor ctorShapes.reverse hwf)` where `D` is the last-Pi
  domain (`hvMajor : (LR Γ₀).DefEq majorX majorY hlastPair.domain
  majorShape majorTypeShape`, per field `majorRel` ADQ:1165). Note: the
  free-closure `CtorDefEq`, **not** a native `CtorExact` leaf.
- `hrecargsI : LRS.CtorArgsDefEq (LR Γ₀) recXs recYs recShapes :=
  halignedI.args.tail` (ADQ:3055-3057).

### Target of the sorry

The `IotaLeafDefEq` conclusion (ADQ:1324-1326) after the substs. Modulo
exact post-`subst` normal form (inferred, not elaborated — verify in
goal view):

```
(LR Γ₀).DefEq
  ((majorX :: recXs).foldr (fun a f => f.app a) (.const c ls))
  ((majorY :: recYs).foldr (fun a f => f.app a) (.const c ls))
  AI (resultShape.app majorShape) (resultTypeShape.app majorShape)
```

with `c = rec` derivable from `hmfI` (the analogous
`iotaDefEq_of_ctorExactAt` consumers all state the head as
`.const rec recLs`, e.g. ADQ:1983-1986). This matches the conclusion
shape of `LRS.iotaDefEq_of_ctorExactAt_fixedHead` (ADQ:2072-2077) at
`recLs := ls`.

## buildP status

**`buildP` exists as a named hypothesis slot, not a definition.** It is
the main callback of `LE_Interp.Witness.recNatRDeepSound`
(SLR:8521-8548, binder at SLR:8523-8532):

```
buildP : ∀ (d : Nat) {ρ m M} (hM : LE_Interp.Witness ρ m M),
  hM.RDeepChildren (fun hM' => P hM' ∧ hM'.RDeepChildren P ∧
    LE_Interp.Witness.SoundRDeepAt P Γ₀ hM' d) →
  (∀ d' < d, ∀ {ρ m M} (hM' : Witness ρ m M),
    P hM' ∧ hM'.RDeepChildren P ∧ SoundRDeepAt P Γ₀ hM' d') →
  P hM
```

Sibling slots: `buildC` in `recNatRDeepConsumer` (SLR:8553) and
`recNatRDeepConsumerAt` (SLR:8592). The plans' phrase "the buildP
algebra" (log line 295, completion plan line 649, roadmap line 776) means:
*write the concrete instantiation of this slot* — i.e. choose the
predicate `P` and prove the per-constructor cases.

The evident candidate for `P` is **`LR.FixedHeadResult`** (ADQ:1331-1367):
a Prop on one witness `hX : Witness ρ root X`, universally quantified
inside over level `n`, context `Γ` (with a `Ctx.WF Γ` input, ADQ:1346),
iota rule, and spine data; conclusion
`(LR (n+1) Γ).DefEq (r.1.applyS recLs mx) (r.1.applyS recLs my) A out
outTy` (ADQ:1366-1367). Already proved cases/transports:
`mono` (ADQ:1369), `mono_l` (ADQ:1380), `bot` (ADQ:1391), `bvar`
(ADQ:1408), `sort` (ADQ:1424). Its consumer chain is fully in place:
`LRS.iotaDefEq_of_ctorExactAt_fixedHead` (ADQ:2040-2088) takes
`hP : ∀ (hr : R m M), LR.FixedHeadResult (hR hr)` and feeds
`LRS.IotaRHSDefEq.of_nonbotWitnessResult` (ADQ:1635-1699, applied at
ADQ:2081-2088), which selects the fixed-head witness *together with* its
retained `P` via `LE_Interp.RHS.fixedLowerWitnessResult` (SLR:4507-4517),
so lowering cannot reselect a different evaluator (the instance-#6
repair).

So the missing work is exactly: (i) `RDeepChildren.Laws FixedHeadResult`
(two of five fields unproved — see gap G2), (ii) the `buildP` cases for
witness constructors `app`, `lam`, `forallE`, `const` (the
application-chain algebra proper, plus the "conversion/type-relation
handoff and constant case" named at completion plan lines 653-656), and
(iii) the assembly at the sorry (gaps G1, G4).

## Machinery signatures (statement-level)

Witness layer (SLR):
- `LE_Interp.Witness` (3584-3605), **Type**-valued mirror of `LE_Interp`
  (3550-3567). `const` case (3599-3605) stores `Params.env.constants c =
  some ci`, `ls.length = ci.uvars`, root bound `m ≤ m'`, `m'.HasType a`,
  the registered type's witness `Witness ρ a (mkInst ls ci.type)`, the
  Prop evaluator `LE_Interp.Const c ls R [] m'`, and the proof-relevant
  callback `∀ m e, R m e → Witness ρ m e`.
- `Witness.mono` (3657) / `mono_l` (3672): lower root / grow valuation,
  preserving the tree. `Witness.closed` (4957): change valuation entries
  irrelevant to a `ClosedN M k` term. `Witness.recR` (3693): follow
  exactly the stored R-edges.
- `Witness.recDeep` (3748) / `recDeep₂` (3769): full structural recursion
  (deep children); recDeep₂ keeps the first tree's IH polymorphic in the
  second (term/type role swap).
- `Witness.RDeepChildren P` (3799-3816): retained tree granting `P` (and
  recursively `RDeepChildren P`) **only at abstract constant R-edges**
  (const case, 3813-3816); ordinary children get only the recursive
  structure. Closure lemmas: `map` 3838, `mono` 3858, `mono_l` 3898,
  `closed` 5003, `lift'` 5114, `weak` 5172, `subst` 5215, `inst` 5277,
  `forallE_inv'`/`lam_inv'` 6448/6490, `forallE_inst`/`lam_inst`
  6552/6572.
- `RDeepChildren.JoinLaws P` (3822-3834): `bot`, `mono`, `mono_l`,
  `join` (join of two witnesses at `m₁.join m₂`). `RDeepChildren.Laws P`
  (6814-6820) **extends JoinLaws with `closed`** — five fields total.
- `RDeepChildren.compat_join` (5686+): from `JoinLaws P`, `ρ'.LE ρ`, and
  two retained trees on the same `M`, produces `m₁.Compat m₂` and a
  joined witness with a retained tree.
- `recRDeep` (3942) / `recNatRDeep` (4020) / `recRDeep₂` (4044) /
  `recNatRDeep₂` (4129): R-edge recursions; the `Nat` variants make
  stratification depth the primary decrease, so conversion restarts on an
  arbitrary witness only after `d' < d`.
- `TypedRDeep P ρ m M A` (6614-6621): ∃ enlarged root `m'`, type shape
  `a`, witnesses for `M` and `A`, `m ≤ m'`, `m'.HasType a`, both retained
  trees. `TypeRDeep` (6624), `toType` (6632), `bot` (6640).
- `TypedRDeep.app` (6654-6670): from `mono_l`+`closed` laws and two
  callbacks (function typed at `.forallE A B`; instantiated result
  `B.inst X` as a type), applies — "application itself introduces no new
  semantic R edge".
- `TypedRDeep.lam` (6895): laws + body callback (under `ρ.push x`) →
  typed at `A.forallE B`. `TypedRDeep.forallE` (7169): laws + domain +
  codomain callbacks → typed at `.sort (.imax u v)`.
- `FitsRDeep P base Γ ρ` (8359-8366): valuation whose entries carry
  witnesses + retained trees; `lookup` 8368, `push` 8386,
  `Valuation.Fits.toFitsRDeepTrue` 8396.
- `SoundRDeepAt P Γ₀ hM d` (8408-8415): ∀ `{Γ A core}`,
  `HasTypeStratifiedS Γ M A core d → FitsRDeep P Γ₀ Γ ρ →
  Valuation.Fits Γ₀ Γ ρ → TypedRDeep P ρ m M A`. (`Γ₀` here is an
  auto-bound variable of each statement, chosen by the consumer.)
- `soundRDeepRestart` (8421-8433): proves `SoundRDeepAt` below a depth
  bound from `Laws P` + strictly-smaller restarts; syntax-directed cases
  compiled through `TypedRDeep.app/lam/forallE`; the `defeq` case
  (8503-8515) converts via `LE_Interp.sound` on the stratified equation.
- `recNatRDeepSound` (8521-8548): `Laws P` + `buildP` ⊢ ∀ hM d,
  `P hM ∧ hM.RDeepChildren P ∧ SoundRDeepAt P Γ₀ hM d`.
- Fixed-head selection: `Lower R` (4447), `Lower.realizeWitness` (4466),
  `RHS.fixedWitness` (4432), `RHS.fixedLowerWitness` (4476),
  `RHS.fixedLowerWitnessResult(P, hR, hP, hmono)` (4490-4517) — selects
  witness **and** its `P` from the same R-edge.
- `LogRel.DefEqRect R M₁ M₂ N₁ N₂ A m a` (8666-8670): `left`, `right`,
  `cross` edges at one relation/type/shapes. Ops: `diagonal` 8674,
  `trans` 8680, `conv` 8689 (needs semantic `TyDefEq`), `mono_l` 8696,
  `mono_r_1/2` 8705/8715, `whr` 8724 (all four endpoints in lockstep),
  `LRS.DefEqRect.app` 10988 / `LR.DefEqRect.app` 11020.
- `LRS.DefEq.app` (10962-10972): function edge at `LRS IH` level n+1 with
  shape `.lam mf hmf : WShape (n+1)`, argument `IH.DefEq x y A₁ p b` at
  level n, `p.HasType b`, raw `Γ ⊢ x ≡ y : A₁` ⊢ result `IH.DefEq (M.app
  x) (N.app y) (A₂.inst x) (mf.app p) (tf.app p)` at level n. **Each app
  step descends one level.**
- `LR.DefEq.ctor'_inv` (11040-11047): classification + `HasType` +
  `(LR Γ).DefEq M N A (.ctor' c fields) a` ⊢ `IndTyHead Γ A ∧
  LRS.CtorDefEq Γ (LR Γ) M N (.ctor c fields hwf)` (free closure).
- `LRS.CtorExact` (9561-9579): the native leaf — classification, level
  lists equal (`ls = ls'`), head typings, two `SpineWF`s, `CtorArgsDefEq`
  and both `CtorSpineDefEq`s.
- `LRS.CaptureDefEqAligned IH m x y typeExpr` (11481-11487): ∃ shapes,
  `m ≤ elemShape.T`, `elemShape.HasType typeShape`, `IH.TyDefEq typeExpr
  typeExpr typeShape`, raw `Γ ⊢ x ≡ y : typeExpr`, `IH.DefEq x y typeExpr
  elemShape typeShape`. `mono` 11504, `lift` 11511, `rebase` 11527.
- `LE_Interp.RHS.ShapeSpine m2 head paths out` (3375-3383): per-path cons
  `{n} {f : WShape (n+1)} {a : WShape n}`: `a.T ≤ m2 path → m ≤ (f.app
  a).T → ShapeSpine m2 m paths out → ShapeSpine m2 f.T (path::paths) out`.
  **The level `n` is existential and independent per step.**
  `typedLowerHead` (3417): from per-path typed lower bounds + typed out,
  a typed lower approximation of the head.
- `LE_Interp.sound` (8353-8355): `IsDefEqStrong Γ M N A → Fits Γ₀ Γ ρ →
  (LE_Interp ρ m M ↔ … N) ∧ (… → InterpTyped ρ m M A)`.

SExpr layer:
- `PathSpineWF Γ value type A paths B` (SE:1537-1550): dependent spine
  over paths; `cons` consumes `.forallE (type path) A₂` and instantiates
  at `value path`; **`conv` and `ret` embed raw `IsDefEq … (.sort u)`
  edges** with no semantic counterpart.

Adequacy layer (ADQ):
- `LR.PatternLeafDefEq` (1276) / `LR.IotaLeafDefEq` (1302) — the leaf
  contracts; `of_iota` (2178) bridges them.
- `LR.FixedHeadResult` (1331-1367) — see above. Inputs at use-site: `Ctx.WF
  Γ`, `X = mkInst recLs rule.df.rhs`, `head ≤ root`, strong self-typing
  `IsDefEqStrong Γ X X (mkInst recLs rule.df.type)` (supplied by
  `rule.rhsStrong`, used at ADQ:1575), `ShapeSpine`, typed lower head,
  two `PathSpineWF`s at one shared `captureType`, per-path
  `CaptureDefEqAligned` (rec at `LR (n+1) Γ`, ctor at `LR n Γ`,
  ADQ:1358-1363), `out.HasType outTy`, `(LR (n+1) Γ).TyDefEq A A outTy`.
- `LRS.IotaRHSDefEq` (1480-1508); `of_nonbot` (1519, discharges the bot
  RHS and extracts head + `ShapeSpine` via `rule.rhsShapeSpine`,
  supplies `rule.rhsStrong recLs`); `of_nonbotWitness` (1582);
  `of_nonbotWitnessResult` (1635) — the P-preserving form; its capture
  input shape (1669-1674) **matches FixedHeadResult's exactly** (levels
  `LRS IH`/`IH` vs `LR (n+1)`/`LR n`).
- `LRS.iotaDefEq_of_ctorExactAt` (1951-2031): pattern + matches + RHS +
  **`CtorExact Γ₀ IH …`** + `PatternLeafSpine` + rec-head typing + out/A +
  `rhsDefEq : ∀ rule, IotaRHSDefEq …` ⊢ the goal-shaped `DefEq`.
- `LRS.iotaDefEq_of_ctorExactAt_fixedHead` (2040-2088): same but
  discharges `rhsDefEq` from `hR` + `hP : ∀ hr, FixedHeadResult (hR hr)`;
  demands **`hΓ : Ctx.WF Γ₀`** (2054) and `leaf : CtorExact Γ₀ (LR Γ₀) …`
  (2064) — everything at the canonical relation.
- `LR.iotaActions_of_exactEqAt` (used 1929, 2153) / `iotaDefEq_of_exactEqAt`
  wrapper ending 1926-1939: the root-pair form taking `CtorArgsDefEq` for
  both spines + weak-head reductions of both majors to their ctor spines.
- `LR.constDefEq` (2193-2217): the structural constant evaluator; caller
  supplies only `evalPat : PatternLeafDefEq`.
- `LR.adequateApp` (2452-2471): the Adequate-level dependent-application
  core (three lower callbacks: function, argument, instantiated result);
  the template the buildP `app` case is meant to mirror
  (completion plan 650-653).
- `LR.Adequate.rect` (~935-945): packages adequacy output as a
  `DefEqRect`; `LR.constLamDefEq` (1076-1137) consumes a rect-valued
  `eval`.
- `LR.JointBuilder` (717+), `foldRaw_of_jointBuilder` (751-756): the
  typed chain-fold consumer — needs `B : JointBuilder` and `Ctx.WF Γ`,
  where `B.rawTypeUniq`/`B.stratifiedInversion` (729-739) are derived
  from **`LR.ContextualAdequacyAt 1`** (`B.first B.zero`) — i.e. from the
  full adequacy theorem at levels 0/1.

## Gap map

Notation: (a) = directly in scope at the sorry, (b) = constructible via a
named kernel-checked lemma, (c) = gap.

Assembly route assumed (the only one whose consumers exist today): apply
`LRS.iotaDefEq_of_ctorExactAt_fixedHead` (or its `exactEqAt` sibling)
after decomposing `hmajorCtor.2`.

| input | status |
|---|---|
| `hpat` | (a) `hpatI` ADQ:3028 |
| `hmf`/`hma` | (a) `hmfI`/`hmaI` ADQ:3031-3032 |
| `hrhs` at `Lower R` | (a) `hrhsI` ADQ:3028 — relation matches: the leaf is stated at `LE_Interp.Lower R` (ADQ:3021) and `of_nonbotWitnessResult` concludes at `Lower R` (ADQ:1679-1680) |
| `hR : R → Witness` | (a) from the witness destructuring, ADQ:2891 (explicit-binder form; the consumer wants implicit — trivial eta wrapper) |
| `hmono` for P | (b) `FixedHeadResult.mono` ADQ:1369; wired at ADQ:2083-2084 |
| `hP : ∀ hr, FixedHeadResult (hR hr)` | (c) **G3** — this is buildP itself: `(recNatRDeepSound laws buildP (hR _ _ hr) 0).1` once laws+buildP exist |
| `laws : RDeepChildren.Laws FixedHeadResult` | (c) **G2** — `join` and `closed` unproved (only `bot`/`mono`/`mono_l` exist, ADQ:1391/1369/1380; Laws needs five fields, SLR:6814+3822) |
| `hΓ : Ctx.WF Γ₀` | (c) **G1** — see below |
| `leaf : CtorExact Γ₀ (LR Γ₀) …` (or `exactEqAt`'s reductions + `CtorArgsDefEq` for the ctor spines) | (c) **G4** — `hmajorCtor.2` is the free-closure `CtorDefEq`; decomposition machinery is conditional on `JointBuilder` |
| `hleaf : PatternLeafSpine` | (a) re-assemble the rcased fields of `hleafI` (all bound at ADQ:3033-3037) |
| `hrecHead` | (a) `hheadI` after `c = rec` identification (via `hmfI`, cf. `varN_const_head` used at ADQ:3046-3048) |
| `hout`, `hA` | (a) `houtI`, `hAI` |
| capture relations for `IotaRHSDefEq` | produced internally by `iotaActions_of_exactEqAt` (ADQ:1927-1935) — needs G4's inputs first |

### G1 — `Ctx.WF Γ₀` is not in scope (availability gap, low design risk)

Required by `iotaDefEq_of_ctorExactAt_fixedHead` (ADQ:2054) and by
`FixedHeadResult` itself (ADQ:1346). Not available: `LR.adequacy`
(ADQ:2856-2858) has no WF premise; `LR.SubstWF` (SLR:11797-11805) does
not record target-context well-formedness; nothing in the const case
introduces it. Downstream churn if threaded: `LR.adequacyAt` (ADQ:3547),
`forallE_whRed_l` (ADQ:3573-3577), `sort_forallE_inv` (ADQ:3631), and
`sort_inv` (ADQ:3696) all instantiate adequacy at an **arbitrary** Γ with
no WF; `sort_invS` (ADQ:3698-3708) does have `hΓ : OnCtx …` to feed a WF
premise, but the `forallE_inv` co-deliverables (ADQ:3605, 3631) would
need new hypotheses or a move to their `_of_adequacy_collapsed` variants
(ADQ:3583). Alternative: audit whether `FixedHeadResult` actually needs
`Ctx.WF Γ` (it plausibly does, for stratified-typing restarts /
weakening the closed head's typing into Γ) — if not, drop the field
instead of threading it. Decide explicitly; do not discover this at
`exact`-time.

### G2 — `Laws FixedHeadResult`: `join` and `closed` unproved

`recNatRDeepSound` needs all five fields (SLR:8521-8522, 6814-6820,
3822-3834). `closed` should follow the `mono_l` pattern (FixedHeadResult
never inspects ρ except through the witness; cf. ADQ:1380-1389 where the
proof is transparent pass-through). `join` is the suspicious one: given
`P H₁`, `P H₂` at `m₁.join m₂` on the same `M`, the ShapeSpine input
arrives at `head ≤ m₁.join m₂` — the proof must route `head` through one
of the joined bounds. Check whether `TShape.join`'s LE lemmas suffice
(`head ≤ m₁.join m₂` does NOT give `head ≤ m₁` or `head ≤ m₂` in a join
semilattice — it gives the reverse). If not directly provable, the
`compat_join` machinery (SLR:5686) exists precisely because joins were
needed at application nodes; `FixedHeadResult.join` may need the same
`Compat`-based split of the ShapeSpine head. Budget real time here.

### G3 — the buildP cases themselves (the planned work)

Missing witness cases: `app`, `lam`, `forallE`, `const` (plus using
`bot`/`bvar`/`sort` already proved). Per completion plan 649-656 the
remaining content is "the conversion/type-relation handoff and constant
case, then consuming the rectangle along the generated `ShapeSpine`".
Available cores: `TypedRDeep.app/lam/forallE` (SLR:6654/6895/7169),
`soundRDeepRestart` (8421), `LRS.DefEq.app` (10962), `DefEqRect` ops
(8666-8737), `LR.adequateApp` as the shape template (ADQ:2452).
Known sub-gap inside: converting TShape-level witness facts into
level-indexed `(LR n Γ)` facts at the *consumer-demanded* `n` — the
`toValTy` pattern (ADQ:2909-2915) handles existential levels via
`le_n`/`le_a` + lift; the algebra must do this at every chain node whose
`ShapeSpine` cons level is existential (SLR:3378-3380).

### G4 — the major-side decomposition (highest #7 risk)

`hmajorCtor.2` is a **free-closure** `LRS.CtorDefEq` at the canonical
relation. Both existing leaf consumers need more: `…_of_ctorExactAt*`
need a native `CtorExact` (ADQ:1972/2064); `…of_exactEqAt` needs
weak-head reductions of both majors onto ctor spines plus root-to-root
`CtorArgsDefEq` for the ctor fields (ADQ:2109-2114 in the `of_exact`
wrapper). The chain-normalization layer (`CtorExact/CtorFrame/CtorLink/
CtorChain/NativeAlgebra`, `CtorDefEq.toChain`, per completion plan
430-446) exists, but the only typed fold consumer visible is
`foldRaw_of_jointBuilder` (ADQ:751), which requires `B : LR.JointBuilder`
— and `JointBuilder` is powered by `ContextualAdequacyAt 0/1`
(ADQ:729-739), i.e. by the very theorem whose proof contains this sorry.
**Inside `LR.adequacy`'s single derivation-induction there is no
level-indexed fixpoint from which lower-level full adequacy (hence
uniqueness, hence the typed chain fold) can be consumed.** The decided
joint route (completion plan 403-412, 414-428) prescribes exactly that
offset bootstrap ("uniqueness at n consumed by adequacy at n+2"), but
`LR.adequacy` as written (2856) has not been restructured into it. So one
of the following must be true before the leaf closes, and the worker
should decide which *in the plan file first*:
  1. The buildP/fixedHead route makes the typed chain fold unnecessary at
     this site: a uniqueness-free *semantic* fold (per-link iota results
     glued by `(LRS IH).trans` at the package-fixed type, midpoints via
     `WHRedS.ctorSpine_determ`, frames folding completed results — plan
     259-276, 440-446, 488-491) is written as a new `CtorChain` algebra
     instance whose leaf handler is `iotaDefEq_of_ctorExactAt_fixedHead`.
     Watch item: that handler is stated at `(LR Γ₀)` throughout; a link's
     native relation must reach it only through the frame-transport of
     the *completed* result, never by projecting the root prefix into the
     native relation (the instance-#5 trap, plan 532-544).
  2. Or `LR.adequacy` is restructured into the level fixpoint so a
     `JointBuilder` (or `LimitedUniq` at the ctor-field level) is in
     scope. That is a statement-level change to the main induction, not
     leaf-local work — if the worker finds themselves needing
     `ContextualAdequacyAt` inside the sorry, STOP (this is the two-strikes
     rule's tripwire).
  Note the composition-impossibility map (plan 342-356): lam-shaped
  constructor fields cannot compose without uniqueness; `ctorShapes` here
  come from a live `Matches` and are arbitrary. Route 1 works only if
  the per-link/fold design genuinely avoids root-to-root *field*
  composition (it composes link *conclusions*, not fields — that is the
  design's whole point; verify this property survives contact with the
  actual `CtorChain.Algebra` interface before writing Lean).

### G5 — PathSpineWF's raw-only conv edges (latent)

`PathSpineWF.conv`/`ret` (SE:1543-1550) inject raw `IsDefEq … (.sort u)`
steps into the capture telescope with no semantic counterpart, while the
chain algebra's `LRS.DefEq.app` needs semantic Pi data per step and
`DefEqRect.conv` (SLR:8689) needs semantic `TyDefEq`. The intended
source of the semantic telescope is the head's own type witness
(`Witness.const` stores `hA : Witness ρ a (mkInst ls ci.type)`,
SLR:3602) — i.e. the algebra derives its own telescope semantically and
uses the supplied final `(LRS IH).TyDefEq A A outTy` (ADQ:1506) to land,
never converting *along* a raw edge mid-chain. If a draft finds itself
needing "raw defeq ⇒ semantic TyDefEq" mid-spine, that is adequacy-shaped
and circular — same tripwire as G4.2.

## Pre-mortem checklist (the six historical erasures, re-asked for buildP)

1. **Erased midpoint/capture types (iotaSite/SpineDefEq era).** Q: does
   any buildP-facing interface erase the types of intermediate chain
   nodes? A: mostly repaired — both `PathSpineWF`s share **one**
   `captureType` map (ADQ:1492-1498) and `CaptureDefEqAligned`
   (SLR:11481) is stated *at* that map, so variable leaves are related at
   the exact telescope domain ("the very domain used by both dependent
   application spines", ADQ:1476-1477). Residual: the raw-only
   `conv`/`ret` edges inside `PathSpineWF` (G5) are the one place a
   midpoint typing is only raw. File:SE:1543-1550.

2. **False assumption-free Retype (lambda observations).** Q: does the
   buildP conversion handoff anywhere retype a lam-shaped observation
   without the term-indexed callback? A: the new layer does not assume
   `Retype`: `DefEqRect.conv` (SLR:8689) demands semantic `TyDefEq`;
   `soundRDeepRestart`'s defeq case (SLR:8503-8515) converts via
   `LE_Interp.sound` on the stratified equation itself; the lambda
   boundary remains `LimitedUniq.LamRetype` (plan 509-519) and is NOT
   consumed by the Witness layer. Risk shifts to G4's fold, not buildP.

3. **Shallow children lost under symm/trans (RChildren era).** Q: does
   `RDeepChildren` survive every transport buildP will perform? A: YES —
   the closure family is comprehensive: `mono` SLR:3858, `mono_l` 3898,
   `closed` 5003, `lift'` 5114, `weak` 5172, `subst` 5215, `inst` 5277,
   binder inversions 6448/6490, instantiations 6552/6572, join via
   `compat_join` 5686, plus `TypedRDeep.{mono,weak,out}` 6855/6862/6873.
   This instance looks genuinely repaired.

4. **Unary recursion couldn't cover two semantic inputs (recRDeep →
   recRDeep₂ era).** Q: does the unary `recNatRDeepSound` reach the
   type-side tree, and "does the hypothesis at an abstract constant edge
   arrive at the level the root chain consumer folds at"? A: the
   type-side tree is a *structural child* of `Witness.const` (SLR:3602)
   retained by `RDeepChildren.const` (3813), and `TypedRDeep` carries
   both trees (6617-6621) — so unary suffices structurally;
   `recDeep₂`/`recNatRDeep₂` (3769/4129) remain available for role
   swaps. Levels: the Witness layer is TShape-valued (level-free), and
   `FixedHeadResult` is level-polymorphic *inside* the predicate
   (ADQ:1333), so there is no fixed-level mismatch at R-edges **by
   construction**; the level obligation moves entirely into the
   TShape→`WShape n` conversion inside each buildP case (G3 sub-gap).
   One verify-item: `FixedHeadResult` receives `IsDefEqStrong` self-typing
   (ADQ:1349) but `SoundRDeepAt` consumes `HasTypeStratifiedS`
   (SLR:8412); confirm the strong→stratified adapter exists at the depth
   accounting `recNatRDeepSound` provides (`∀ d` is unbounded, so any
   finite stratification depth is reachable — the question is only which
   lemma produces the stratified derivation for `mkInst recLs
   rule.df.rhs` in context Γ).

5. **Native vs root relation (lift/unlift zigzag era).** Q: "does
   DefEqRect's cross edge survive recursion into spine tails, or is it
   rebuilt per node?" A: it survives compositionally —
   `LRS.DefEqRect.app` (SLR:10988-11003) produces all three result edges
   from the same argument observation and left-oriented codomain, and
   `trans`/`whr`/`mono_*` (8680-8737) never mix endpoint witnesses; no
   per-node rebuild. The eval site currently needs only `diagonal`
   (ADQ:3067-3069) because both heads are the same constant. The
   instance-#5 trap re-enters ONLY through G4's chain fold (a native
   link's relation vs the canonical `(LR Γ₀)` of
   `iotaDefEq_of_ctorExactAt_fixedHead`'s statement, ADQ:2064-2071) —
   this is the single most likely home of failure mode #7.

6. **Prop-valued provenance (LE_Interp proof irrelevance era).** Q: "is
   anything in the chain Prop-valued where the consumer needs to case on
   which branch produced it?" A: the fixed-head selection is clean —
   `hR` is data in the witness (SLR:3604) and
   `fixedLowerWitnessResult` (SLR:4490-4517) selects witness + retained
   `P` from the *same* R-edge, with `hmono` covering the `Lower` root
   drop (the instance-#6 repair, correctly threaded at ADQ:2081-2088).
   Residual Prop-boundaries checked: `LE_Interp.Const`/`RHS`/`Matches`
   are Props, but their consumers only *universally quantify* over rules
   (`rhsDefEq : ∀ rule, …`, ADQ:1921-1922, 1980-1981) or destruct them
   inside Prop goals — no consumer needs to remember *which* rule/pattern
   fired across a proof-irrelevant boundary. One watch item: inside
   buildP's `const` case, the witness's `hC : LE_Interp.Const c ls R []
   m'` (SLR:3603) is Prop; if the app-chain algebra ever needs to case on
   `hC`'s `.pat` vs `.lam` branch AND retain the choice into a
   Type-valued construction, that is #6 all over again — the design says
   it should not (the chain consumes only `hR`-selected witnesses and the
   Prop-level `RHS`), but check the first draft for exactly this.

## Probe file

Ready-to-run axiom-closure probe. Place at repo root (e.g.
`AxiomProbe.lean`) and run `lake env lean AxiomProbe.lean` (the flake dev
shell provides lake; the Experimental import convention is confirmed by
ADQ:1 and `Lean4Lean/Experimental/UniqueTyping.lean:1`).

```lean
import Lean4Lean.Experimental.ShapeLogRelAdequacy

/-! Axiom-closure waypoints for the L4L-16 gate path.
Expected clean baseline: [propext, Classical.choice, Quot.sound].
`LR.adequacy` and everything through it (incl. `sort_invS`,
`forallE_inv`, `sort_forallE_inv`) will show `sorryAx` until the
iota leaf closes; the Witness-layer roots must NOT. -/

#print axioms Lean4Lean.VEnv.IsDefEqU.sort_invS
#print axioms Lean4Lean.SExpr.LR.adequacy
#print axioms Lean4Lean.SExpr.LE_Interp.sound
#print axioms Lean4Lean.SExpr.forallE_inv
#print axioms Lean4Lean.SExpr.sort_forallE_inv
-- Witness-layer roots the buildP step will lean on:
#print axioms Lean4Lean.SExpr.LE_Interp.Witness.recNatRDeepSound
#print axioms Lean4Lean.SExpr.LE_Interp.Witness.RDeepChildren.compat_join
#print axioms Lean4Lean.SExpr.LE_Interp.Witness.TypedRDeep.lam
#print axioms Lean4Lean.SExpr.LRS.IotaRHSDefEq.of_nonbotWitnessResult
#print axioms Lean4Lean.SExpr.LRS.iotaDefEq_of_ctorExactAt_fixedHead
```

Caveat: `LE_Interp.sound` / `TypedRDeep.lam` etc. are `Lean4Lean.SExpr.*`
because SLR/ADQ open `namespace Lean4Lean … namespace SExpr` (ADQ:4-6);
`sort_invS` is declared `_root_.Lean4Lean.VEnv.IsDefEqU.sort_invS`
(ADQ:3698). If a name fails to resolve after worker edits, re-grep — the
declarations may have been renamed since this snapshot.

### Measured (2026-08-14 ~07:15 EDT, all four Experimental files green)

First live run (extended with `IsDefEqStrong.mkS` and three D0 fixture
waypoints; run against the freshly built oleans):

- `sort_invS`, `LR.adequacy`, `forallE_inv`, `sort_forallE_inv`:
  `[propext, sorryAx, Classical.choice, Quot.sound]` — expected while the
  leaf is open.
- CLEAN at `[propext, Classical.choice, Quot.sound]`: `LE_Interp.sound`,
  `IsDefEqStrong.mkS`, all five Witness-layer roots listed above, and the
  D0 waypoints `ParamsD0.natParams` / `natTypeStrong` / `natIotaRule` —
  the fixture inherits no admission so far.
- `LR.iotaActions_of_exactEqAt` is CLEAN. The sorry-bearing
  `LR.iotaActions_of_exact` (ADQ:2212 at probe time) has **zero
  consumers**, and literal `WHRedS.defeq` no longer occurs in the
  adequacy file. Modulo transitive consumption of the other three SExpr
  admissions (all measured off-path at the 16B′ audit), the gate's sole
  `sorryAx` source is now the leaf's own `sorry`: closing it cleans
  `sort_invS` and both inversion co-deliverables simultaneously. The
  orphaned `of_exact` wrapper is deletable at the next touch.

## Review response: the shape-order mismatch (2026-08-14, sibling session)

Re the reported gap — recursive fixed-head adequacy needs a typed lower
observation (`headElem ≤ head`, supplied by `ShapeSpine.typedLowerHead`)
*together with* a semantic interpretation of its type, while soundness
types only an upper extension, and the two directions do not compose.

1. **The rejection of the downward pullback is consistent with two
   recorded corrections**, not just prudence: the `Shape.WF.plift`
   refutation (no lift-shaped Pi below an arbitrary function shape) and
   the `Retype` correction (lambda observations pin codomain validity to
   the original Pi typing). Contravariant domains are the same wall in
   both. Do not revisit it under stronger-sounding hypotheses; the
   established principle is CARRY the evidence, never project it down.
2. **The type's semantic witness may already exist in the retained tree
   — check before constructing anything new.** `Witness.const` stores
   `hA : Witness ρ a (mkInst ls ci.type)` (SLR:3602 at snapshot time):
   the fixed head's *type* witness is a field of the very node the
   fixed-head selection destructs. The synchronized package then needs
   only to THREAD `hA` through the retained invariant and peel it per
   application via the already-kernel-checked exact Pi inversion of the
   retained-tree transport layer, feeding `TypedRDeep`'s dependent
   application. If that holds, the repair is plumbing an existing field
   through `FitsRDeep`'s motive, not new mathematics.
3. **Two pre-flight checks on the widened invariant, per the
   signature-first rule** (write the package as a Lean statement and
   check every recursion case has its transport before proving):
   (a) *binder cases* — the type-witness component must weaken through
   `TypedRDeep.lam`/`forallE`; the transport layer's lift/weakening
   coverage should supply this, verify it applies at the package's
   indexing; (b) *depth/restart indexing* — the type's interpretation
   recurses independently of the term's (this is WHY `Witness.recDeep₂`
   is binary); the package must put the type witness in the second,
   polymorphic slot of the binary principle rather than forcing it
   through the unary `recNatRDeepSound` axis, and its restarts must obey
   the same strict stratification-depth decrease.
4. **Anchor at the lower observation from construction**, per the
   NativeAlgebra order: build the package where `typedLowerHead` is
   produced and transport completed results root-ward; never build at
   `head` and project down.
5. This is invariant-widening #8, but the first caught pre-proof; each
   revision since the re-cut has strictly narrowed. If the widened
   package hits a second wall (the likely spot: the compat-join case
   failing to synchronize the type witness), the two-strikes rule
   applies — state the obligation here before more Lean.

### Frontier re-map after the pause (2026-08-14 ~16:30)

Codex session PAUSED; tree stable. Snapshot for this section (verified
unchanged across the analysis window): SLR mtime 2026-08-14 13:58:42,
597560 B; ADQ mtime 2026-08-14 14:43:33, 214542 B. Sole sorry:
**ADQ:4285**. Everything in the original body above refers to the old
(2026-08-14 03:31) state; line numbers in THIS section are current.

#### 1. The sorry site now

The leaf was **extracted into a standalone theorem**:
`LR.iotaWitnessStep : LR.IotaWitnessStep Γ₀` (ADQ:4255-4285), where
`LR.IotaWitnessStep Γ₀` (ADQ:1505-1510) is
`Ctx.WF Γ₀ → ∀ {ρ c ls R}, (∀ {m M}, R m M → Witness ρ m M) →
LR.IotaLeafDefEq Γ₀ c ls (LE_Interp.Lower R)`. The proof intros
`hΓ₀ ρ c ls R hR` (4256) and then replays the exact prelude of the old
in-line block (intro 4257-4259 = old 3027-3029; `cases hmatchI` app case
4260-4262; `rcases hleafI` 4263-4267; substs 4268-4277; `hctorClass`
4278-4280; `hmajorCtor := LR.DefEq.ctor'_inv …` 4281; `hrecargsI` 4282-
4284; sorry 4285). Target: unchanged from the original "Target of the
sorry" section above (the `IotaLeafDefEq` conclusion, ADQ:1422-1424).

Scope changes vs the old site: **`hΓ₀ : Ctx.WF Γ₀` is now bound**
(4256) — old gap G1 is resolved at the leaf, and globally: `LR.adequacy`
(4288-4293) and `LR.adequacyAt` (4298-4300) now take `hΓ₀`. But the
scope is also LEANER: the old outer const-case data (`W : SubstWF`, the
constant's type witness `hA'`, `hConst`, `hrec`, the `eval` app package)
is gone — the step receives ONLY `hΓ₀` and the bare callback `hR`.

**Is a lower-level adequacy hypothesis / JointBuilder bound at the
sorry? NO.** The intended discipline is stated in the docstring
(ADQ:4251-4254): the body "may consume only the well-founded fixed-head
and predecessor-uniqueness packages, never the final polymorphic
adequacy theorem" — but no such package appears in the theorem's
hypotheses. The fixpoint restructure reached the *boundary*, not the
sorry: `LR.adequacy_of_iotaWitnessStep` (ADQ:3572, ~680 lines) is the
old induction parameterized by `iotaStep`, and it consumes the leaf
**level-pinned** — `evalPat : LR.PatternLeafDefEqAt Γ₀ k c ls (Lower R)
:= LR.PatternLeafDefEqAt.of_iota (iotaStep hΓ₀ hRI)` (ADQ:3743-3745),
with `LR.constDefEq` restated to take the At-form (ADQ:2521). The
level-indexed step interfaces exist but are **parked with zero
consumers**: `IotaWitnessStepAt` (ADQ:1493), `IotaLeafDefEqAt`
(ADQ:1427), `PatternLeafDefEqAt` (ADQ:1456). No level-indexed
`adequacy_of_iotaWitnessStepAt` exists yet.

#### 2. What codex built (the synchronized-package layer)

The proposed "synchronized package" repair **largely exists**:

- `LR.SelfAdequateAt Γ₀ hX depth` (ADQ:3145-3154): for all `n`, `mx bx :
  WShape n`, `Δ`, `mx.T ≤ root` (**typed lower observation**),
  `HasTypeStratifiedS Δ X B core depth`, `mx.HasType bx`, and
  **`Witness ρ bx.T B` (semantic type witness) as an input** —
  concludes `LR.Adequate Γ₀ Δ ρ X X B mx bx`. Private exact-root worker
  `SelfAdequateExactAt` (3157); public downward closure is by
  `hX.mono hroot` on the witness (ADQ:3467-3469), never by pulling
  `HasType` back — consistent with the review response's point 1.
- `LR.RetainedResultAt Γ₀ hX depth` (ADQ:3169-3175) =
  `(SelfAdequateAt ∧ FixedHeadResultAt) ∧ RDeepChildren (True) ∧
  SoundRDeepAt (True)` — the full retained invariant.
- **Proved**: `selfAdequateExactAtStep` (ADQ:3200-3455) — every
  `HasTypeStratifiedS` case of self-adequacy EXCEPT const (delegated to
  a contract), given `inv : JointStratifiedInversion` + `hΓ₀`; its app
  case (3247+) uses `lower`-restarts as the three adequateApp callbacks.
  `selfAdequateAtStep` (3456-3469). `retainedResultAt_of_steps`
  (ADQ:3488-3523): the complete well-founded plumbing via
  `recNatRDeepConsumerAt` (SLR:8811) with retained-tree predicate
  `T := fun _ => True` and `Laws.true` (ADQ:3519-3521) — **this
  resolves old gap G2**: no `join`/`closed` laws for `FixedHeadResult`
  are needed; the consumer/tree separation eliminates them.
  `fixedHeadResult_of_steps` (ADQ:3527-3536). The conversion algebra
  `LR.adequateDefeqSelf_of_stratifiedInversion` (ADQ:3071+, given inv)
  and `LR.TyDefEq.of_defeq_of_stratifiedInversion` (ADQ:813) — the
  "conversion/type-relation handoff" named in the old plan is proved,
  conditional on `inv`.
- `LR.FixedHeadResult` **restated** (ADQ:1515-1560): now `Γ₀`-explicit
  and quantified over `LR.SubstWF Γ₀ σ σ' Δ ρ` (1517-1518) instead of
  taking `Ctx.WF Γ`; `PathSpineWF`s at Γ₀ (1539-1542). Depth-indexed
  `LR.FixedHeadResultAt` (ADQ:1562-1600) adds the input
  **`HasTypeStratifiedS Δ X (mkInst recLs rule.df.type) true depth`**
  (1582) — the stratified certificate the chain algebra needs to invoke
  `SelfAdequateAt`; adapters `FixedHeadResult.at` (1604),
  `of_forall_at` (1615, uses `IsDefEqStrong.stratify` 1621),
  `FixedHeadResultAt.mono` (1625). Surviving case lemmas: `mono` 1636,
  `bot` 1647, `bvar` 1664, `sort` 1680 (old `mono_l` dropped — no
  longer needed by the new plumbing).
- Leaf consumers restated: `iotaDefEq_of_ctorExactAt` (ADQ:2211, now
  takes `hΓ`), `iotaDefEq_of_ctorExactAt_fixedHead` (ADQ:2358-2408, now
  takes `W : SubstWF Γ₀ σ σ' Δ ρ` (2373) + `hΓ : Ctx.WF Γ₀` (2374) +
  `hP` at the new `FixedHeadResult Γ₀` (2383); still `leaf : CtorExact
  Γ₀ (LR Γ₀) …` (2384)); `of_nonbotWitnessResult` at ADQ:1891.
- New SLR plumbing (+~14KB): `WShapeFun.AppLEData`/`appLEData`
  (SLR:6516/6526) and `WShape.HasDomData`/`HasDom.data`
  (SLR:6559/6565) — noncomputable Type-valued extractors of lower-shape
  application/domain data (the peeling plumbing for the chain);
  `LE_Interp.RHS.realizeWitness*` (SLR:4384-4408).
- **Unchanged**: `LE_Interp.Witness` (SLR:3584) — the `const`
  constructor (3599-3605) still has exactly seven fields (hreg, hlen,
  hle, hty, hA, hC, hR); the `ihA/ihR` seen at SLR:3640 are induction-
  hypothesis names inside `witnessNonempty`'s proof, not constructor
  fields. `FitsRDeep` (now SLR:8578) is the same inductive; its `cons`
  carries a per-BINDING type witness (8583-8584) as before. The
  head-type witness of the synchronized package lives in
  `SelfAdequateAt`'s `hB` input, not in `FitsRDeep`.

#### 3. Gap map at ADQ:4285 (current)

(a) in scope: `hΓ₀` (new), `hR`, `hpatI hmatchI hrhsI`, all
`PatternLeafSpine` fields, `hctorClass`, `hmajorCtor` (IndTyHead ∧
free-closure `CtorDefEq`), `hrecargsI` — as before.

(b) constructible via named lemmas GIVEN the three missing inputs
below: `hP hr := (fixedHeadResult_of_steps inv hΓ₀ constStep fixedStep
(hR hr))` (ADQ:3527); the RHS discharge is fully wired inside
`iotaDefEq_of_ctorExactAt_fixedHead` (ADQ:2398-2408).

(c) gaps, ordered by depth:

- **C1 — `inv : JointStratifiedInversion`, non-circularly.** Gates
  everything: `retainedResultAt_of_steps`, `fixedHeadResult_of_steps`,
  `adequateDefeqSelf…`, and any `foldRaw_of_jointBuilder` use. The only
  constructors are `JointStratifiedInversion.of_adequacy`
  (ADQ:435, needs `ContextualAdequacyAt 1`) and
  `of_adequacy_and_typeUniq` (ADQ:4417) — both need the theorem being
  proved. No prover of `JointBuilder.zero`/`first` (ADQ:718-719)
  exists. The designed escape (JointBuilder docstring ADQ:700-716:
  "level-zero adequacy is built first; a specialized base argument
  builds level-one adequacy without predecessor uniqueness") requires
  the level ladder: a level-indexed `adequacy_of_iotaWitnessStepAt`
  consuming `IotaWitnessStepAt` (the consumption at ADQ:3743-3745 is
  already level-pinned, so this refactor is prepared), plus direct
  proofs of the level-0/1 leaf instances. None of this is wired yet.
  **If the worker tries to prove `LR.iotaWitnessStep` as stated
  (polymorphic, no package hypotheses), C1 is unreachable — the
  statement must gain hypotheses or the ladder must land first.**
- **C2 — `constStep : LR.SelfAdequateConstStep Γ₀`** (ADQ:3178-3195),
  unproven, no prover theorem exists. Content: constant self-adequacy
  from the evaluator semantics + `RetainedResultAt` restarts; the
  template is the main induction's const case (ADQ:~3600-3757).
- **C3 — `fixedStep : LR.FixedHeadStep Γ₀`** (ADQ:3474-3483), unproven
  — the application-chain algebra proper, and the home of the
  **residual shape-order blocker**. Status of the blocker: NARROWED but
  live. To invoke `SelfAdequateAt` at the fixed head, the algebra must
  supply (i) `mx.T ≤ root` — available via `typedLowerHead` (SLR:3417)
  ✓; (ii) the stratified typing — now an input of `FixedHeadResultAt`
  (ADQ:1582) ✓ (added in the final pre-pause hours); (iii)
  `mx.HasType bx` — from `typedLowerHead`'s TShape pair, plumbing ✓;
  (iv) **`Witness ρ bx.T B` — the registered type interpreted at the
  LOWER type observation — still has no visible producer.** Soundness
  (`LE_Interp.sound`, `TypedRDeep`) types only upper extensions;
  downward pullback stays invalid at function shapes. The intended
  construction (per review-response point 4 and the new
  `AppLEData`/`HasDomData` extractors) is to BUILD the lower Pi-shaped
  type witness along the registered telescope from capture-type
  witnesses + the out-type witness — that constructor does not exist
  yet. This is the one place the blocker's mathematics remains.
- **C4 — major decomposition** (old G4, unchanged): `hmajorCtor.2` is
  the free-closure `CtorDefEq`; consumers need `CtorExact` (ADQ:2384)
  or exactEq reductions + ctor-field `CtorArgsDefEq`. The typed fold
  `foldRaw_of_jointBuilder` (ADQ:751) needs a full `JointBuilder` —
  same circularity family as C1. A uniqueness-free semantic fold
  instance for THIS consumer is still unwritten.
- **C5 — SubstWF availability at the leaf (wiring check, flagged
  uncertain).** The restated consumers demand `W : SubstWF Γ₀ σ σ' Δ ρ`
  at the leaf's *arbitrary* ρ, but `SubstWF` (SLR:12143-12151) only
  constructs `.id` at `ρ = .nil` plus pushes — no instance for
  arbitrary ρ. Plausible intended resolution: the fixed head is CLOSED
  (`rule.rhsClosed`), so `Witness.closedAt` (SLR:5168) transports its
  witness to `.nil` and `W := SubstWF.id` suffices; but then the
  capture relations (at the ambient ρ) and the head relations (at
  `.nil`) must be recombined. Verify this valuation split *on paper*
  before writing the fixedStep — it smells like erasure-instance
  material if done implicitly.

#### 4. Bottom line

The pause state is a genuine narrowing: G1 resolved (hΓ₀ threaded), G2
dissolved (consumer/tree separation — no Laws needed), the synchronized
package designed, stated, and proved for every non-const structural
case, and the well-founded plumbing finished. What remains is exactly
three unproven inputs (C1 ladder/base-levels, C2 const producer, C3
chain algebra with the narrowed type-witness-at-lower-shape
construction) plus the unchanged major-decomposition assembly (C4) and
one valuation-wiring check (C5). The sorry itself is now a pure
assembly point: nothing in its local scope blocks it except the absence
of those inputs.

## Decision synthesis — the resumption work order (2026-08-14 ~16:45)

Product of three parallel design investigations against the paused
tree (frontier re-map above; a construction-probe pass; a ladder/
alternative adversarial pass). All referenced probe files elaborate
green under `lake env lean` and are preserved in `plans/probes/`
(gitignored). Statements marked PROVED are fully term-proved there and
can be lifted into the codebase directly.

**Architectural decision (supersedes the level-ladder reading of route
2): index the joint fixpoint by stratified typing DEPTH, not shape
level.** The shape-level `JointBuilder` tower (`zero`/`first`/succ) is
structurally unrealizable: `LE_Interp.app` stores function shapes at a
free constructor level and `adequateApp` runs at interpretation-derived
max-levels, so full adequacy at any fixed level requires leaf instances
at unboundedly many levels — every rung is same-index circular
(unbounded-ascent argument; cruxes in `probeC-ladder-crux.lean`, all
seven elaborate). `LiftEquiv` cannot rescue it (iff only at
literally-lifted observations). The predecessor-package alternative is
also dead: the lower head's type lives at a level ≥ the leaf's own, and
adequacy consumes interpretations rather than manufacturing `Witness`es.
Depth, by contrast, genuinely decreases (`HasTypeStratifiedS.forallE_inv`)
and is already the machinery's measure (Nat-first restarts,
`lower : ∀ d' < depth+1`). The level tower may survive only as a final
public assembly facade.

**Work order, in dependency order:**

1. **Depth-indexed bootstrap** (unblocks everything inv-shaped: C1, the
   conversion cases, C4's callbacks). Retire the level-polymorphic
   `iotaWitnessStep` obligation in favor of the depth-indexed form
   (`IotaWitnessStepAt`, parked at ADQ:1493); restate the ~400-line
   bootstrap (ADQ:59-440) depth-bounded (`AdequacyAtDepth` +
   `JointStratifiedInversionAt D` from depth-≤D adequacy — statements
   elaborate in probeC). Mechanical but the largest single chunk.
   STANDING TRIPWIRE: audit every leaf-internal inversion consumption
   for strictly-smaller depth; one same-depth consumption re-imports
   the G4 circularity.
2. **N1 — `typedLowerHeadLE`** (the C3(iv) shape half). Strengthen
   `typedLowerHead` so `elemTy ≤ a` by the spine recursion over the
   single-layer peel, which is PROVED (`peelLayerProved`,
   probeB-2). The witness half is `Witness.mono` (root-lowering is
   legitimate — no pullback). Remaining content: the induction's
   level-lifting bookkeeping and re-anchoring the tail at
   `tyFun.app argCap`. C5's type-witness half is dissolved: registered
   types are closed (`closedAt` + `henv.closedC`), so the witness
   component is valuation-free.
3. **N2 — the capture-domain link. The ONE surviving design decision;
   state it in this file before writing Lean (two-strikes rule).** Each
   capture shape needs a typed upper bound in the *peeled registered
   domain*; element-side singletons need fire points ≥ the spine arg
   while `HasDom.data` supplies typed args ≤ it, so the bound must come
   from peeling the OUTER recursor-constant's `hA` along the pattern
   `Matches` — i.e. an invariant-widening of `FixedHeadResultAt`'s
   `hcap` input (or a joint two-telescope recursion). The context-free
   form (probeB-1 S6) is stated but likely unprovable as written; do
   not attempt it.
4. **C2 `SelfAdequateConstStep`** — assembles from 1-3's outputs
   (probeB-1 S2 confirms the exact `SelfAdequateAt` invocation fits).
5. **C4** — one `RawAlgebra` consumer instance; its `RawTypeUniq` and
   two root callbacks all derive from step 1's inversion package
   (`foldRaw_of_jointBuilder` body pattern, ADQ:756-762). Needs no
   `JointBuilder`.
6. `FixedHeadStep`, the leaf fold, then the endpoint measurement
   (probe: `plans/probes/AxiomProbe.lean`; expect `sort_invS` clean and
   record `forallE_inv`/`sort_forallE_inv` clean simultaneously).

**Verified non-risks** (do not re-litigate): unary recursion axis
suffices (widened component threads through `recNatRDeepConsumerAt` —
`widenedThreading` PROVED; `recDeep₂` has zero adequacy-file
consumers); compat-join demands nothing of the widened consumer
(`Laws.true` separation, and `compat_join` would synchronize anyway);
restarts cover fresh-depth type witnesses (`soundRDeepRestart`).

**Risk ranking:** (1) N2's design — the shape-order wall's surviving
kernel, now one input of one structure; (2) step 1's rung audit; (3)
N1's literal-Pi requirement across `PathSpineWF`'s raw conv/ret edges
(G5) — the peel needs `mkInst recLs rule.df.type` to stay a literal Pi
telescope along capture paths.

## N2 decision — retain one ordered term/type telescope (2026-08-14)

**Decision: take the joint two-telescope route, not a pointwise widening of
`CaptureDefEqAligned`.**  A standalone field for each path cannot certify
that its alleged domain is the domain selected by the *same* registered-type
observation after all earlier dependent applications.  It would also leave
`PathSpineWF.conv`/`.ret` free to switch the syntax telescope without moving
the semantic type witness.  Both are erasure #7 in a new wrapper.

The producer will therefore recurse in `rule.capturePaths` order while the
outer recursor evaluator and its registered-type evidence are still in
scope.  One layer retains, at a common shape level:

- the RHS-spine argument `aSp` and a capture cap `argCap` with
  `aSp ≤ argCap`;
- `argCap.HasType tyDom`, where `tyDom` is the domain of the current peeled
  registered-type observation;
- the recursive result below `g.app aSp`, re-anchored at
  `tyFun.app argCap` on the type side.

The consumer for exactly this layer is now kernel-checked as
`LE_Interp.RHS.ShapeSpine.peelTypedLayer` in `ShapeLogRel.lean`.  Its proof
needs no ambient upper function or downward typing transport: the three
fields above plus the recursive term/type bounds construct the singleton
lambda/Pi layer and prove both lower inequalities.

The completed ordered certificate must expose the fixed-head consumer's
actual endpoint, not merely another synthetic typing pair:

```text
∃ headElem headTy,
  headElem ≤ head ∧ headElem.HasType headTy ∧
  Nonempty (LE_Interp.Witness ρ headTy
    (SExpr.mkInst recLs rule.df.type))
```

`FixedHeadResultAt` will consume that synchronized endpoint.  The current
context-free `typedLowerHead` input remains useful only as the shape fallback
and must not be used to manufacture the final witness.  The ordered producer
belongs at the outer `constDefEq`/`Matches` materialization boundary, where
the recursor's type evidence and the accumulated semantic-to-logical
argument caps coexist; the leaf-local `hcap` map is already too late.

Two invariants are part of this decision:

1. A raw `PathSpineWF.conv`/`.ret` edge may be crossed only by the strictly
   smaller typing-depth inversion package.  A same-depth conversion call is
   the standing circularity tripwire.
2. Valuation changes are explicit.  Closed registered roots may use
   `Witness.closedAt`, but an ambient-`ρ` capture certificate is never
   silently combined with a `.nil` head witness; the joint producer performs
   and records the transport before the leaf boundary.

## Post-resumption rung audit (2026-08-14)

The first implementation pass validated the shape half of the review and
found two additional interface mismatches in the proposed depth bootstrap.
They must be resolved before C2/C4 are implemented against that bootstrap.

1. **The bounded semantic result is path-valued, not ordinary inversion.**
   `AdequacyAtDepth` directly proves bounded sort observation and Pi
   observation with `TypeDefEqPath` domain/codomain outputs.  It does *not*
   directly prove `JointStratifiedInversionAt`: a `TypeDefEqPath` erases the
   stratification depths of its intermediate endpoints, so the existing
   global path-collapse proof cannot be reused inside one bounded rung.
   Probe C only established that the stronger statement elaborated; its body
   was `sorry`.  The kernel-checked result is now named
   `JointStratifiedPathInversionAt.of_adequacyAtDepth`.  Ordinary inversion is
   recovered only after the final, depth-polymorphic adequacy theorem exists.

2. **`IotaWitnessStepAt` is shape-level indexed.**  Its parameter pins the
   `WShape` level of `IotaLeafDefEqAt`; it carries no typing-depth certificate.
   It therefore cannot be the depth rung named in work-order item 1 without a
   new contract.

There is also a statement-level tripwire on the current
`AdequacyAtDepth`: a stratification of only the left endpoint does not bound
the strong equality derivation paired with it.  In `symm` the recursive
derivation needs the opposite endpoint; in `trans` it needs the intermediate
endpoint; and in `const` the registered RHS premise can have a deeper typing
derivation than the constant's declared type.  Consequently the current
definition is a valid observation interface but is too broad, by itself, to
be the induction unit for the main adequacy proof.  The repaired rung must
retain a coherent depth certificate for the strong derivation (or an
equivalent proof-relevant transport invariant), not merely an arbitrary
`HasTypeStratifiedS` proof for its left term.

One dependency previously routed through ordinary bounded inversion has
already been removed safely.  The `HasTypeStratifiedS.defeq` branch of
retained self-adequacy now consumes a `SelfAdequateDefeqStepAt` callback.
Its well-founded implementation calls `LR.adequateDefeq` with heterogeneous
adequacy at the strictly smaller certificate depth; the compatibility
implementation still accepts completed global stratified inversion.  Both
paths are kernel-checked.  This isolates the remaining rung decision to the
constant/fixed-head producers instead of letting it leak through the whole
syntax-directed algebra.

The next bootstrap edit must therefore choose and state the coherent
derivation-depth certificate first.  Until then, do not implement C2/C4 by
assuming either `JointStratifiedInversionAt.of_adequacyAtDepth` or a
depth-indexed meaning for the existing `IotaWitnessStepAt`; neither theorem
exists.

## Ordered-telescope implementation status (2026-08-14)

The consumer half of the N2 decision is now complete and kernel-checked in
`ShapeLogRel.lean`:

- `ShapeSpine.TypedTelescope` retains the exact capture order and threads the
  same `argCap` through both the term spine and the dependent codomain
  `tyFun.app argCap`;
- `TypedTelescope.lowerHead` folds that certificate through
  `peelTypedLayer` into `TypedLowerHead`; and
- `TypedLowerHead.withWitness` exposes the fixed-head endpoint selected
  above:

  ```text
  ∃ headElem headTy,
    headElem ≤ head ∧ headElem.HasType headTy ∧
    Nonempty (LE_Interp.Witness ρ headTy A)
  ```

This closes the ordered *consumer/certificate* problem, not its producer.
The remaining architecture gate is the recursion contract.  The current
Nat-first `R`-deep recursor supplies semantic-child consumer results only at
the parent term's exact typing depth.  That contract is not evaluator
coherent: a shallow constant typing derivation can unfold to a registered RHS
whose syntax-directed typing proof is deeper.  Conversely, restarting only
from the semantic witness loses the retained provenance needed after
conversion.  C2/C4 must therefore wait for a recursion certificate that
supports evaluator unfolding and retained conversion together; the new
ordered telescope must not be wired to the known-invalid same-depth callback.

### Recursion-contract probe

A focused elaboration probe of `selfAdequateExactAtStep` confirms exactly
where the information is lost.  The `HasTypeStratifiedS` induction
hypotheses are generalized over the semantic witnesses, but invoking one at
a selected function/argument/result witness requires
`RDeepChildren (RetainedResultAt ... d)` for that witness.  The parent
package retains consumer results only at abstract `R` edges, and semantic
typing was intentionally separated with tree predicate `T := fun _ => True`.
Consequently the `TypedRDeep` enlargement/join can retain an exact evaluator
tree, but not the consumer result needed when the enlarged witness becomes a
syntax-induction subject.

The two tempting interface changes are both invalid in isolation:

1. Keeping Nat first and asking an `R` child only at the parent's depth fails
   when the reached registered RHS has a deeper syntax-directed typing.
2. Keeping semantic descent first and asking every `R` child at all depths
   still cannot restart on an unrelated converted/enlarged witness: supplying
   both freedoms abstractly admits the cycle “raise depth along `R`, then
   lower depth and restart at the parent witness.”

The repaired certificate must therefore be *provenance-sensitive*.  It must
show that each witness selected by application/conversion is obtained from
the retained subject/type trees by the existing root, valuation, closed,
instantiation, or compatible-join transports, and it must carry the consumer
result across exactly those transports.  Equivalently, a replacement may
use a genuinely derived environment/evaluator bound, but a bare global Nat
assumption would be a new oracle and is not admissible.  This is now the sole
architecture decision before C2/C4; more wrappers around
`recNatRDeepConsumerAt` do not address it.

### Provenance-closure checkpoint

The first half of that replacement is now kernel-checked.  The semantic
module has a free `Witness.TransportClosure P` containing only the transports
that preserve an already-selected evaluator tree (`bot`, root lowering,
valuation growth, compatible join, and closed-term valuation change), with
an automatic `RDeepChildren.Laws` instance.  `Witness.recRDeepTransport`
therefore follows genuine `R` edges before inserting `.base`; it does not
grant a consumer result to a witness merely because that witness has the
same public indices.

On the adequacy side, `LR.CoherentRetainedResult` packages self-adequacy and
the fixed-head result at every stratification depth, and
`coherentRetainedResult_of_step` closes that package from one semantic-first
algebra.  A direct induction,
`Witness.typedRDeep_of_stratified`, also kernel-checks all syntax-directed
typing constructors without a Nat restart.  Binder enlargement is discharged
by semantic typing of the domain; the only abstract input left by this
theorem is proof-relevant transport across the displayed-type equality in a
`HasTypeStratifiedS.defeq` node (`DefeqRDeepTransport`).

The mixed eliminator is now explicit as
`Witness.recRDeepNatTransport`.  It performs structural `R` descent before
the Nat induction, gives genuine `R` children every Nat index, and permits a
strictly-smaller Nat restart only after the caller supplies the restarted
witness's complete `RDeepChildren (TransportClosure ...)` certificate.  The
adequacy specialization is `LR.CoherentRetainedNatStep`, closed by
`coherentRetainedResult_of_natStep`; its two consumer obligations are split
as `CoherentSelfStep` and `CoherentFixedHeadStep` and reassembled by
`CoherentRetainedNatStep.of_steps`.  All of these declarations and the full
adequacy module build with the sole pre-existing iota admission unchanged.

That callback is an *isolation boundary*, not yet an admissible assumption.
In particular, its fully generic statement for an arbitrary tree predicate
`P` is stronger than the final construction may use.  The reverse direction
of a registered definition/action can build a constant witness whose selected
`R` edge is the current RHS witness.  To prove `RDeepChildren P` for that new
constant, a generic transport would need `P` of the current witness, exactly
the result under construction.  Adding such a case to `TransportClosure`
would reintroduce the cycle in proof-relevant form.

Consequently the next interface must retain the *actual strong equality (or
endpoint stratification) derivation* at conversion.  Congruence, beta/eta,
root/valuation transport, instantiation, and compatible join can preserve the
tree structurally; a reverse registered step must instead consume its genuine
smaller RHS-typing/equality hypothesis.  Do not implement
`DefeqRDeepTransport (TransportClosure CoherentRetainedResult)` as a global
oracle, and do not add an unconstrained “conversion” constructor to
`TransportClosure`.

### Depth-local endpoint-rebuild refinement

The next implementation probe found a smaller sufficient interface than a
constructor-by-constructor interpreter for `IsDefEqStrong`, while preserving
the checkpoint's prohibition on a global conversion oracle.

The recursive-edge evidence is now split into two layers:

```text
NatSeed Q d h       := (∀ k, Q h k) ∨ Q h d
NatProvenance Q d h := TransportClosure (NatSeed Q d) h
```

`Witness.recRDeepNatProvenance` exposes `RDeepChildren (NatSeed Q d)` to the
consumer algebra and injects genuine outer-recursion children on the left.
A tree rebuilt after a strict Nat decrease may inject an edge only on the
right, at that exact smaller depth.  `NatProvenance` is introduced later,
inside retained semantic typing, where root/valuation/closed/join transports
must be recorded.  The adequacy specializations are respectively
`LR.CoherentSeedAt` and `LR.CoherentProvenanceAt`; the outer self/fixed-head
consumers see only the inspectable seed, never the free transport closure.

The key new operation is `Witness.RDeepChildren.of_step`.  Given an exact
converted endpoint witness, it rebuilds that witness's evaluator tree
structurally.  Only after a real `R` child's own tree has been rebuilt may a
caller attach a result for that child.  Therefore, inside an outer rung at
depth `D`, the already-complete callback for `d < D` can safely attach
`CoherentRetainedAt ... d` local seeds throughout a freshly selected endpoint
tree.  Reverse definition folding is then harmless: if the new constant's
`R` edge points back to the old RHS witness, that edge receives only the
already-complete result at `d`, never the all-depth result at `D` currently
under construction.

The following bridge is kernel-checked:

- `LR.CoherentSeedAt.rebuild` constructs the inspectable exact evaluator
  tree used at the consumer boundary;
- `LR.CoherentProvenanceAt.rebuild` performs the guarded tree rebuild;
- `LR.CoherentRetainedAt.restart` packages the strictly-smaller-depth
  restart;
- `LR.coherentDefeqRDeepTransportAt` selects the converted endpoint by
  semantic soundness and rebuilds its tree from the local seed constructor;
  and
- `Witness.typedRDeep_of_stratifiedLocal` instantiates the retained semantic
  typing proof with that conversion bridge.

This supersedes only the claim that the equality derivation itself must be
interpreted constructor by constructor.  The safety conclusion above is
unchanged: generic `DefeqRDeepTransport P` remains only an isolation boundary,
and no unconstrained conversion constructor belongs in `TransportClosure`.

### Exact iota-consumer revalidation

The first direct consumer of the refined seed interface is now
kernel-checked as `LRS.iotaDefEq_of_ctorExactAt_coherent`.  It preserves the
`NatSeed` injection through root lowering and splits at the selected fixed
RHS head:

- an `.inl` genuine evaluator child chooses the native depth returned by
  `rule.rhsStrong recLs |>.stratify` and consumes its all-depth fixed-head
  result there;
- an `.inr` rebuilt child consumes only its exact local result and therefore
  requires the registered RHS typing raised to that same local depth.

This confirms that the provenance repair is sufficient on the consumer side
and makes the remaining producer obligation exact.  The direct coherent
constant/fixed-head algebra must justify the local RHS depth budget at the
actual rebuilt endpoint.

The follow-up implementation now packages that obligation as
`LR.CoherentRhsSeedAt Γ₀ Δ depth hRhs rhsType`.  Its two constructors are
deliberately asymmetric:

- a genuine evaluator child carries `CoherentRetainedResult` and therefore
  needs no selected depth certificate; and
- a rebuilt child carries both `CoherentRetainedAt ... depth` and the exact
  `HasTypeStratifiedS Δ rhs rhsType true depth` certificate.

`LRS.iotaDefEq_of_ctorExactAt_coherent` consumes this coupled package at the
*same proof-relevant `R` edge*.  The generic lower-witness eliminator hides
the endpoint index, so the implementation guards its predicate by the
explicit equality to `mkInst recLs rule.df.rhs` and discharges that equality
before opening the package.  This prevents a proof-irrelevant re-selection
from pairing one edge's retained result with another edge's typing budget.
The focused adequacy target builds with this interface.

The stale proof-independent route has also been removed: `RetainedResultAt`,
`FixedHeadStep`, `CoherentFixedHeadStep.of_step`,
`retainedResultAt_of_steps`, and `fixedHeadResult_of_steps` no longer exist.
The syntax-directed self algebra now receives `CoherentSeedAt` trees and
returns coherent retained results directly.

What remains is therefore a producer theorem, not another consumer adapter:
at the actual constant evaluator edge it must construct
`CoherentRhsSeedAt`.  A bare local `CoherentSeedAt` is insufficient in the
constant case, because a shallow constant typing may expose a registered RHS
whose native stratification is deeper.  No all-depth result, generic
conversion transport, proof-independent pairing, or same-depth assumption
may be manufactured to discharge that local branch.  The next producer
contract must retain the derivation that justifies the local RHS certificate
(or retain an equivalent exact ordered type-telescope witness) at the point
where that edge is created.

### Focused-edge correction and producer boundary

Rechecking the exact iota consumer against the live conversion code found one
stale conclusion in the depth-local endpoint-rebuild checkpoint above.
`LR.coherentDefeqRDeepTransportAt` does rebuild a selected endpoint tree, but
it ignores the endpoint stratifications supplied by the equality derivation
and reselects the public endpoint witness through semantic soundness.  It
therefore does **not** preserve the proof-relevant evaluator edge required by
`CoherentRhsSeedAt`, and it must not be used as the final conversion producer.
The checkpoint remains useful for the guarded rebuild operation itself; its
claim that the conversion bridge is complete is superseded here.

The proof-relevant RHS half of the replacement is now kernel-checked:

- `LE_Interp.Witness.appNVarsFocused` peels the exact application witness,
  joins repeated capture occurrences, and retains the literal fixed-head
  sub-witness;
- `Pattern.IotaRule.focusedShapeSpine` specializes that extraction to the
  registered iota tower; and
- `Pattern.IotaRule.focusedRHS` reconstructs the registered RHS using only
  root lowerings of that retained head witness.

Thus the next producer contract is deliberately narrower than another
conversion oracle.  While the reverse registered action still has both the
exact endpoint derivation and the exact RHS witness in scope, it must produce
one package containing:

1. the retained fixed-head sub-witness and its ordered semantic capture
   spine;
2. the ordered registered-type telescope for the same capture caps; and
3. either the genuine evaluator-child result or the exact local
   `HasTypeStratifiedS` derivation for the focused RHS edge.

Only after constructing that package may the reverse action rebuild the
constant with `appsRealizeFocused`.  Extending `LR.constDefEq` alone cannot
repair the loss: the current reverse action uses proof-independent
`RHS.of_applyS` followed by ordinary `apps_realize`, so it can discard the
selected edge before `constDefEq` is entered.  The implementation order is
therefore fixed: retain the ordered type derivation at action materialization,
rebuild the focused constant witness, then thread the resulting
`CoherentRhsSeedAt` through the constant/fixed-head algebra.

### Packed-telescope consumer checkpoint (2026-08-15)

The consumer side of that order is now stronger than the earlier
`TypedTelescope`/`Captures` sketch.  The active tree contains
`ShapeSpine.TypedTelescope.WithCaptures`, a single inductive certificate that
owns the semantic spine, the registered-type telescope, and the exact aligned
capture payload at every layer.  Its fold
`TypedTelescope.fixedHeadShapeChain` returns the lower term, its lower
registered-type observation, the type bound, and the logical application
chain from the same constructor choices.

On the adequacy side, `LR.FixedHeadTelescope.withWitnessAndChain` lowers the
registered-type witness and returns it together with that same chain.
`LR.FixedHeadTelescope.toApplicationWith` then zips the chain with the
concrete `PathSpineWF`, invoking semantic conversion only for actual
`conv`/`ret`/domain edges and invoking head self-validity only for the literal
lower endpoint just selected.  Both experimental semantic modules build with
these declarations, and no new admission was introduced.

This closes the downstream erasure risk: once a producer supplies
`WithCaptures`, no later theorem can independently reselect the lower head,
its registered type, or its capture chain.  It does **not** yet construct that
certificate.  The live `StrongSoundEq.ofAction` reverse direction still calls
proof-independent `RHS.of_applyS`, `build_spine`, and `apps_realize`; by then
the exact RHS witness used by the endpoint derivation may already have been
replaced.  The next producer edit must therefore live at (or immediately
inside) that reverse-action/conversion boundary and return the packed
telescope before rebuilding through `appsRealizeFocused`.

### Producer-placement correction and first depth peel (2026-08-15)

The last sentence above is too literal about what can be returned at the
reverse-action boundary.  `LR.FixedHeadTelescope` is instantiated with
`CaptureDefEqAligned.AtShapes`; it depends on the later adequacy-side
`mx`/`my` endpoints, shared `captureType`, substitution, and logical relation.
None of those values exists inside `StrongSoundEq.ofAction`.  Constructing
that exact package there is therefore not merely inconvenient but
ill-typed.  The semantic conversion boundary must instead retain the exact
focused RHS witness and its derivation-aware registered-head typing.  The
final `WithCaptures` fusion belongs at the fixed-head adequacy boundary,
where that semantic certificate and the logical capture payload first
coexist.

The first producer-side depth fact is now kernel-checked in `SExpr.lean`:

- `HasTypeStratifiedS.app_inv` removes outer displayed-type conversions and
  exposes all five premises of the literal application derivation at
  `depth - 1`;
- `foldl_app_head` iterates that inversion through a concrete left-associated
  application tower;
- `foldl_app_head_of_ne_nil` proves that a nonempty tower's literal head is
  typed at a strictly smaller depth; and
- `Pattern.IotaRule.rhsHeadStratified{,_of_nonempty}` specializes the result
  to the exact fixed RHS selected by `rule.rhsApply`.

This removes the former uncertainty about whether focused application
inversion supplies a genuine well-founded decrease.  The remaining type
alignment is now explicit: the native head derivation returned by the peel
has an existential `HeadType`, while `CoherentRhsSeedAt` requires the
registered `mkInst recLs rule.df.type`.  The next producer theorem must align
those two at the same smaller derivation depth using the concrete registered
capture spine (and only its actual conversion edges).  Once that alignment
is retained, `appsRealizeFocused` can rebuild the outer constant with edges
generated from the exact head witness; the adequacy-side fold can then fuse
the aligned captures into `FixedHeadTelescope` without reselecting the head
or its type.

### Exact head handoff correction (2026-08-15)

The final paragraph above overstates the need to identify the peeled native
`HeadType` with the registered rule type.  The head-term half is
heterogeneous: `AdequacyAtDepth` is indexed by the exact registered
`HasTypeStratifiedS` derivation but accepts the semantic witness for the
displayed registered type independently.  Consequently the proof does not
need raw type uniqueness, an equality cast, or a general conversion oracle
to obtain the head term relation.

The consumer now makes the two genuinely distinct obligations explicit.
`LR.AdequacyAtDepth.closedHeadSelf` returns both the head term relation and
semantic validity of the exact registered head type at the same lower type
observation.  The former comes from heterogeneous term adequacy.  The latter
uses `hstrat.isType` and adequacy at the preceding type rung.  Moreover,
`LR.FixedHeadApplication` retains the exact head term relation instead of
discarding it and asking a later consumer to run self-adequacy again.  The
focused adequacy module kernel-checks with this term-and-type handoff and no
new admission.

The remaining producer obligation is therefore narrower and more concrete:
construct `ShapeSpine.TypedTelescope.WithCaptures` (or an equivalent single
proof-relevant package) whose lower head type, ordered capture layers, and
output observation are all selected from one recursion.  An independently
chosen lower type witness is insufficient, even when it is propositionally
compatible, because downward projection through a function observation is
not generally available.  This ordered packed producer--not equality of the
native and registered syntax types--is now the live architecture gate.

### Focused reverse-action certificate (2026-08-15)

The first producer-side handoff at the corrected boundary is now
kernel-checked.  `Pattern.IotaRule.FocusedActionPreimage` is a data-bearing
certificate selected from the exact interpreted RHS witness.  It retains:

- the literal fixed-head sub-witness and ordered semantic capture spine;
- the matched constant/argument prefix reconstructed by `build_spine`; and
- the exact `Const` derivation whose abstract evaluator relation is
  `headWitness.LowerEdge`.

`Pattern.IotaRule.focusedActionPreimage` constructs the certificate without
calling `RHS.of_applyS`, and `FocusedActionPreimage.witness` realizes the
matched redex with `Witness.appsRealizeFocused` at a caller-supplied typed
observation.  Thus reverse action no longer needs to erase and then reselect
the fixed RHS edge.

This checkpoint intentionally stops before claiming the complete producer.
The caller must still obtain that typed RHS observation from the retained
endpoint stratification without losing its evaluator tree, and the
adequacy-side boundary must still fuse the retained semantic spine with the
ordered logical captures into `WithCaptures`.  Those are now separate,
explicit obligations; neither can be replaced by public semantic soundness
or an independently selected type witness.

### Derivation-aware reverse-action transport (2026-08-15)

The focused certificate is now wired into retained semantic conversion.
`LR.focusedExtraReverseRDeepAt` dispatches the pattern carried by an
`IsDefEqStrong.extra` node: zero-arity definition patterns keep the guarded
local endpoint rebuild, while generated iota patterns use the exact
`FocusedActionPreimage` path.  The internal focused evaluator is generalized
over the action's declared type; the public displayed-type conversion remains
the `Sort u` specialization.

`LR.coherentDefeqRDeepPairAt` interprets the strong equality
bidirectionally.  It swaps continuations under `symm`, composes them under
`trans`, and focuses precisely the reverse branch of `extra`.  Consequently
an iota action nested under equality symmetry or composition can no longer be
hidden by one proof-independent soundness call.  The live
`coherentDefeqRDeepTransportAt` now consumes this derivation-aware path, and
the focused adequacy module kernel-checks with the sole pre-existing iota
admission unchanged.

This closes evaluator-edge preservation through conversion, but not the
coupled producer required by the coherent iota consumer.  The rebuilt
constant's `LowerEdge` still receives `CoherentProvenanceAt`; it does not yet
receive the exact registered-head `HasTypeStratifiedS` certificate needed to
form `CoherentRhsSeedAt` in the local branch.  That certificate must be
constructed where the retained semantic spine and the concrete ordered
`PathSpineWF`/capture relations coexist, then packed with `WithCaptures`.

### Producer split after live-signature audit (2026-08-15)

The last sentence above places one half of the remaining producer too late.
The logical `WithCaptures` package still belongs at the fixed-head adequacy
boundary: its `mx`/`my`, substitution, logical relation, and aligned capture
payload do not exist during semantic conversion.  The exact local registered
RHS typing certificate cannot wait for that boundary, however.

The live signatures make the loss explicit:

- `StratifiedDefeqRDeepTransport` supplies both endpoint
  `HasTypeStratifiedS` derivations at the conversion node;
- `coherentDefeqRDeepTransportAt` currently binds them as `_hA`/`_hB` and
  returns only `RDeepChildren (CoherentProvenanceAt ...)`;
- the focused `extra` branch preserves `headWitness.LowerEdge`, but
  `CoherentProvenanceAt.local` stores only `CoherentRetainedAt`; and
- `CoherentFixedHeadStep` later receives neither the discarded endpoint
  derivation nor an action-indexed replacement for it.

Consequently generic provenance plus the later ordered capture telescope is
not by itself an implementable producer for `CoherentRhsSeedAt`.  Public
semantic soundness would merely reselect the endpoint, and
`rule.rhsStrong.stratify` chooses an unrelated native depth that need not fit
the local guarded-restart depth.

The producer must be split across the two boundaries:

1. **At focused reverse conversion**, retain a semantic-only certificate
   tied to the literal `LowerEdge`: the exact fixed-head witness and semantic
   spine already carried by `FocusedActionPreimage`, plus the derivation/depth
   evidence needed to justify the local registered RHS typing.  This package
   must survive the result type of derivation-aware conversion; constructing
   it transiently and returning plain `CoherentProvenanceAt` still erases it.
2. **At the fixed-head adequacy boundary**, combine that retained semantic
   and typing certificate with the concrete `PathSpineWF` and aligned logical
   captures to construct `TypedTelescope.WithCaptures`, then consume it via
   `FixedHeadTelescope.toApplicationWithAdequacyAtDepth`.

This correction does not reopen the rejected raw type-equality route and does
not move logical captures into conversion.  It only identifies the minimum
action-indexed fact that must cross conversion before the later synchronized
fusion can be sound.

### Post-implementation preservation audit (2026-08-15)

The first enriched-provenance implementation kernel-checks, but auditing its
actual flow through `coherentDefeqRDeepPairAt` found a second erasure point.
The recursive interpreter does visit an `extra` nested below `symm` or
`trans`, and `rebuildFocused` tags the literal lower edges of the reconstructed
constant.  That is not yet sufficient to say the certificate survives the
whole equality:

- each non-`extra` leg is implemented by
  `coherentDefeqRDeepFallbackPairAt`;
- that fallback deliberately ignores the incoming `RDeepChildren` tree,
  selects a fresh endpoint through public semantic soundness, and rebuilds a
  new local tree; and
- consequently, in a composite equality, any fallback leg *after* the
  focused leg erases the focused seed before the final endpoint is returned.

Thus the earlier statement that a nested action “can no longer be hidden” is
only a traversal claim.  It is not yet an end-to-end preservation theorem.
The next contract must make the suffix explicit: either interpret the
remaining equality constructors proof-relevantly while retaining the same
focused evaluator relation, or return a conversion-path certificate whose
consumer can replay those exact endpoint choices.  Adding more data solely
to `FocusedRhsOriginAt`, while leaving the suffix fallback proof-independent,
cannot close the producer.

This also sharpens the role of the retained typing fields already added to
`FocusedActionPreimage`.  They are necessary at the action boundary, but they
must travel with the proof-relevant evaluator edge through the *entire*
conversion path.  A transient focused node followed by a plain local rebuild
is observationally indistinguishable from the erasing implementation that
the producer split was meant to replace.

### Closed-valuation leaf consumer and consumption-tower survey (2026-08-15, session-C subagent)

Baseline at resumption: green, zero errors, exactly one `declaration uses
sorry` at the `LR.iotaWitnessStep` leaf (statement now ADQ:6406, sorry
ADQ:6436 after this session's insertions).  Source and olean were
consistent at 06:24; a fresh full elaboration reconfirmed the state before
any edit.

**The preservation question of the previous section is already answered in
the tree.**  Between writing "Post-implementation preservation audit" and
pausing, the previous writer landed the replayable conversion-path
certificate (candidate 2): `LR.FocusedRhsTraceAt` (ADQ:3882),
`LR.FocusedRhsTraceBundleAt` (ADQ:3896), the `carried`/`replayed`
constructors of `LR.CoherentSemanticSeedAt` (ADQ:3907), and
`LR.CoherentProvenanceAt.rebuildTracingFocused` (ADQ:4220), which is now
wired into both legs of `LR.coherentDefeqRDeepFallbackPairAt` (ADQ:4845).
The fallback no longer discards the incoming tree's focused history: every
rebuilt recursive edge carries the complete source trace bundle, replayable
at matching registered-head syntax.  I did not re-litigate that design;
this session's work is downstream of it.

**Two consumption walls found between the conversion layer and the sorry,
one repaired, one mapped:**

1. *SubstWF/valuation coupling (repaired this session).*
   `LR.FixedHeadResult`/`FixedHeadResultAt` are consumed through
   `LR.SubstWF Γ₀ σ σ' Δ ρ` at the witness's own valuation, and the only
   closed `SubstWF` constructor is `.id` at `Valuation.nil`
   (SLR:14222).  The `IotaWitnessStep` leaf receives an arbitrary caller
   valuation with no fits certificate, so the existing consumers
   `iotaDefEq_of_ctorExactAt_fixedHead` and `_coherent` are unusable at
   that leaf as stated — their `W` pins ρ.  Repair, kernel-checked and
   landed: the registered RHS is closed, so the selected head witness is
   transported to `Valuation.nil` at the same root shape by
   `Witness.closedAt` (whole-tree transport, not endpoint reselection)
   and consumed at `SubstWF.id` with `Γ := Γ₀` instances of
   `rule.rhsStrong`.  This is the C5-dissolution argument
   ("registered types are closed") applied to the witness side, and it
   retains everything: spine, typed lower head, raw telescopes, and
   aligned captures were already valuation-free.

2. *The chain wall (mapped; NOT repaired; do not attempt leaf-locally).*
   At the sorry, the major arrives as `hmajorCtor.2 :
   LRS.CtorDefEq Γ₀ (LR Γ₀) majorX majorY (ctor' ...)` via
   `LR.DefEq.ctor'_inv` — the free closure, not a single `CtorExact`.
   Consuming it requires the normalized chain fold
   (`CtorDefEq.toChain` + rectangles; the exact-link rectangle
   `LRS.iotaDefEqRect_of_ctorExactAt` ADQ:2748 was prepared for exactly
   this and `LogRel.DefEqRect.trans` composes shared-middle rectangles).
   The blocker: interior chain vertices must be retyped at the recursor
   domain, and every chain consumer that does this
   (`CtorChain.rawDefEqAt`, `foldRaw`, `foldRaw_of_stratifiedInversion`)
   takes raw type uniqueness / `JointStratifiedInversion` — which is only
   constructible FROM adequacy (`of_adequacy` needs
   `ContextualAdequacyAt 1`, ADQ:582), i.e., not at the bare leaf (G4).
   A uniq-free fold was examined and fails structurally: `NativeAlgebra.trans`
   threads no typing for the shared middle vertex, and deriving it from
   link raw equalities reintroduces pairwise type uniqueness.  Conclusion:
   the leaf sorry is discharge-LAST.  It needs inversion at strictly
   smaller stratified depth, i.e., the depth-indexed adequacy rungs
   (`LR.AdequacyAtDepth` producers) of work-order step 1, which remain
   unlanded — nothing in the file yet produces `AdequacyAtDepth`, it is
   only consumed (ADQ:31/1834/1946/5355).

**Landed this session (kernel-checked, elaboration green, zero errors, the
sole sorry unchanged at ADQ:6436):**

- `LRS.iotaDefEq_of_ctorExactAt_closedFixedHead` (ADQ:2871).  The
  ρ-decoupled exact-link consumer: same interface as `_fixedHead` but the
  fixed-head oracle is `∀ hX : Witness Valuation.nil root X,
  FixedHeadResult Γ₀ hX`, consumed after `closedAt` transport at
  `SubstWF.id`.  Proof goes through `IotaRHSDefEq.of_nonbotWitness` (no
  P-threading needed — the oracle is global, so no `mono`-commutation
  obligation arises).
- `LRS.iotaDefEq_of_ctorExactAt_natStep` (ADQ:4561).  The formal residual-
  gap statement: the exact iota link follows from
  `LR.CoherentRetainedNatStep Γ₀` alone, via
  `coherentRetainedResult_of_natStep` + `CoherentRetainedResult.fixedHead`
  + the closed consumer above.

**The remaining tower, in dependency order (all names live in the file):**

1. Depth bootstrap (work-order step 1, still the critical path): produce
   `LR.AdequacyAtDepth Γ₀ d` / `ContextualAdequacyAtDepth d` by strong Nat
   induction.  Both walls above point here: it feeds
   `SelfAdequateDefeqStepAt.of_lowerAdequacy` (ADQ:5355) and depth-bounded
   inversion (`JointStratifiedPathInversionAt.of_adequacyAtDepth`,
   ADQ:563) for the chain fold's vertex retyping.
2. `LR.SelfAdequateConstStep Γ₀` (ADQ:5298, unproved): the constant case
   remake consuming `children`/`lower` instead of derivation induction; its
   internal iota leaf should use the coherent consumer with seeds drawn
   from the const witness's own `RDeepChildren` tree — NOT the global
   `iotaWitnessStep`.
3. `LR.CoherentFixedHeadStep Γ₀` (ADQ:4503, unproved): the
   `WithCaptures` fusion.  Its missing ingredient is the ordered
   spine→`FixedHeadTelescope` producer (N1/N2 peel); only the `nil`/`cons`
   constructors exist today (ADQ:1700/1715).  `SelfAdequateAt` (not global
   `AdequacyAtDepth`) supplies the head validity inside the algebra via
   `of_fixedHeadTelescope`/`toApplicationWith`.
4. Assembly: `CoherentRetainedNatStep.of_steps` (ADQ:4516) then the chain
   fold at the leaf feeding `iotaDefEq_of_ctorExactAt_natStep` per exact
   link, with vertex retyping through the depth-bounded inversion of 1.

**Design note recorded for the depth-local variant:** a depth-local closed
consumer (analogue of `_coherent` at `Valuation.nil`) would need either a
witness-term commutation lemma `closedAt`-vs-`mono` (to thread a
per-witness seed through `of_nonbotWitnessResult`'s `hmono`), or seeds
stated directly at `Valuation.nil` witnesses.  Deliberately not attempted
this session (two-strikes discipline; the global-oracle form needed no such
commutation).  Whoever writes `SelfAdequateConstStep` should prefer stating
its rule-indexed seeds at nil witnesses from the start.

### Depth bootstrap landed conditionally; N1 peel core ported (2026-08-15, session-C subagent 2)

Baseline at resumption: green, zero errors, exactly one `declaration uses
sorry` at the `LR.iotaWitnessStep` leaf.  Reconfirmed by full elaboration
before edits; the identical inventory holds after every edit below (final
log `elab2`: sole sorry warning at ADQ:6540:8, the same leaf statement,
moved only by insertions).

**Landed (all kernel-checked; no new sorries):**

- `LR.IotaWitnessStepAtDepth Γ₀ depth` (ADQ:1701) and
  `LR.ContextualIotaWitnessStepAtDepth depth` (ADQ:1709): the
  depth-indexed joint-leaf obligation.  At rung `depth` the leaf
  producer receives `∀ d' < depth, LR.ContextualAdequacyAtDepth d'` —
  the raw strict-predecessor family, deliberately unprocessed — and
  returns the ordinary level-polymorphic `IotaWitnessStep Γ₀`.
- `JointStratifiedPathInversionAt.of_predecessorAdequacy` (ADQ:584):
  the `<`-shaped bridge — a successor rung's strict family below
  `depth + 1` is exactly the `≤ depth` family `of_adequacyAtDepth`
  (ADQ:563) consumes, so a leaf producer at rung `d + 1` can assemble
  bounded path inversion at depth `d` with no same-depth adequacy
  consumption.
- `LR.contextualAdequacyAtDepth_of_iotaSteps` (ADQ:6503): THE
  BOOTSTRAP.  `(∀ d, ContextualIotaWitnessStepAtDepth d) → ∀ d,
  ContextualAdequacyAtDepth d` by `Nat.strongRecOn`.  The step case
  hands the untouched strong-induction hypothesis to `steps d` and runs
  `adequacy_of_iotaWitnessStep` (ADQ:5808) with the resulting leaf.  No
  separate base case: at `d = 0` the family quantifier is vacuous and
  the step receives an empty package (honesty note below).
- `LR.contextualAdequacyAt_of_adequacyAtDepth` (ADQ:6519) and the
  composition `LR.contextualAdequacyAt_of_iotaSteps` (ADQ:6530): the
  full depth tower subsumes every level-indexed contextual package via
  `IsDefEqStrong.stratify`.  The level tower is now formally a facade
  over the depth fixpoint, closing that architectural decision of the
  2026-08-14 synthesis.
- `WShape.HasTypeLam.peelLayer` (ADQ:1743): verbatim port of the PROVED
  probe `probeB.peelLayerProved` (plans/probes/probeB-2.lean), placed
  with the `FixedHeadTelescope` producers it will feed.  `hgle`/`hty`
  stay in the signature (unused by the layer algebra, two lint warnings
  accepted) to pin the spine recursion's interface.  `widenedThreading`
  was NOT ported: it commits the `LowerSyncAt` widened-component
  interface, which belongs to the N2 capture-domain decision this file
  requires stating in prose before Lean.

**Why the design respects the standing constraints.**  Depth-indexed,
never level-indexed: the fixpoint index is stratified typing depth; the
leaf stays level-polymorphic exactly as `IotaWitnessStep` is today.
G4: the bootstrap constructs no predecessor package — no inversion, no
uniqueness, nothing derived from the IH inside the induction — it
forwards the raw rung family through the step interface, whose
docstring names the two sanctioned consumers
(`of_predecessorAdequacy`, `SelfAdequateDefeqStepAt.of_lowerAdequacy`,
ADQ:5440).  The global sorried `iotaWitnessStep` is never referenced.
Erasure: the step receives the full contextual family, not a
projection.

**Honesty note — where the remaining depth content lives.**  Producing
`AdequacyAtDepth Γ₀ d` cannot use the rung's own certificate: the
derivation induction is depth-blind (the ADQ:25 docstring caveat is
real — `trans`/`symm`/evaluator descent reach subderivations the
left-endpoint certificate does not bound, and depth-0 certificates
exist via `sort'`, so even the base rung covers arbitrary derivations
with sort-left endpoints).  The bootstrap therefore ignores `hstrat`
(it is a hypothesis of the PRODUCED statement, for consumers), and
`IotaWitnessStepAtDepth 0` degenerates to the bare global leaf.  The
depth restriction that will make the step family dischargeable must
come from the leaf's OWN certificates — the registered-rule stratified
typings (`rhsStratified`/`headStratified`, SLR:9280-9283) that bound
the chain fold's vertex retyping — not from the adequacy root.  That is
the rung audit of the 2026-08-14 synthesis (risk #2), now localized to
one named obligation instead of an amorphous circularity.

**Remaining tower (updated difficulty against the previous survey):**

1. `LR.SelfAdequateConstStep Γ₀` (ADQ:5383, unproved; hard, design
   partly pre-committed): state its rule-indexed seeds at
   `Valuation.nil` witnesses from the start (previous section's design
   note).  Its conversion callback is now one hypothesis away:
   `of_lowerAdequacy` consumes exactly the bootstrap's rungs.
2. `LR.CoherentFixedHeadStep Γ₀` (ADQ:4588, unproved; medium once N2 is
   stated): ordered spine→`FixedHeadTelescope` producer.  Per-layer
   core is now in-file (`peelLayer`); N2 (capture-domain link) remains
   the one open design decision and must be stated in this document
   before Lean.
3. Assembly `CoherentRetainedNatStep.of_steps` (ADQ:4601), then the
   chain fold at the leaf feeding `iotaDefEq_of_ctorExactAt_natStep`
   (ADQ:4646) per exact link, vertex retyping through
   `of_predecessorAdequacy` at the rule certificates' depths.  If those
   depths stay strictly below the rung index, the step family
   discharges per-rung and the bootstrap closes unconditionally; if a
   same-rung consumption appears, that is the G4 tripwire firing — stop
   and escalate to a design session, do not patch.

Consumers already prepared (`closedHeadSelf` ADQ:1919,
`toApplicationWithAdequacyAtDepth` ADQ:2009, `of_lowerAdequacy`
ADQ:5440, bounded inversion ADQ:563/584) are all reachable from the
single hypothesis family `∀ d, LR.ContextualIotaWitnessStepAtDepth d`.

— session-C subagent 2

### SelfAdequateConstStep interface decision — seeds pinned by the ambient SubstWF, not restated at nil (2026-08-15, session-C subagent 3)

Written before the Lean, per the two-strikes prose-first rule, because it
deviates in letter (not in force) from the standing note "state the
rule-indexed seeds at `Valuation.nil` witnesses from the start."

**Where the seeds live.**  Inside `SelfAdequateConstStep`'s proof the
constant witness is destructured together with its
`RDeepChildren (CoherentSeedAt Γ₀ (depth+1))` tree.  The `const` branch
of that tree (SLR:4170-4173) yields, per abstract `R` edge, the exact
seed `pR : ∀ m e hr, CoherentSeedAt Γ₀ (depth+1) (hR m e hr)` and the
child's own tree `cR`.  These seeds are attached to witnesses at the
constant's ambient valuation ρ — and, crucially, the const case proves an
`LR.Adequate` conclusion, so it works under an introduced
`W : LR.SubstWF Γ₀ σ σ' Γ ρ` that pins that same ρ end to end.

**Why the nil restatement is not available here.**  Transporting a seed's
result to the `closedAt`-transported witness needs
`CoherentRetainedAt Γ₀ hV d → CoherentRetainedAt Γ₀ (hV.closedAt cl) d`.
Its `SelfAdequateAt` half quantifies over demands
`LE_Interp.Witness Valuation.nil bx.T B → Adequate Γ₀ Δ Valuation.nil …`
whose `Adequate` components quantify over `SubstWF … Δ Valuation.nil`;
the only closed constructor is `.id` at `Δ = Γ₀`, `σ = σ' = .id`, and the
ρ-stated result can never be instantiated there (no
`SubstWF Γ₀ .id .id Γ₀ ρ` exists for a non-nil ρ).  The same wall blocks
`RDeepChildren.closed` (SLR:5598): its `hP` premise is exactly this
underivable stability.  So per-rule seeds *stated at nil witnesses* are
not producible from the tree; a `SelfAdequateConstStep` conditional on
them would be a hypothesis no producer can ever discharge.

**What the standing note was actually protecting.**  The predecessor's
rationale was "no `closedAt`-vs-`mono` commutation."  The commutation
only arises when a per-witness seed must be threaded through
`of_nonbotWitnessResult`'s `hmono` *and then* moved across a valuation
change.  The kernel-checked `_coherent` consumer (ADQ:4697) already
threads per-witness seeds through `hmono` via `CoherentRhsSeedAt.mono`
with zero valuation transport, consuming the seed's `FixedHeadResultAt`
at the caller's own `W`.  The const case has that `W`.  Decision:

- The internal-leaf obligation is factored as
  `LR.CoherentIotaLeafStep Γ₀`, stated at the ambient valuation with an
  explicit `SubstWF Γ₀ σ σ' Δ ρ` input plus the per-edge seed family,
  the per-edge child trees, and the strict-predecessor restart family —
  the exact inventory `_coherent` + the chain fold will want.  No
  `closedAt` appears anywhere in the const step, which satisfies the
  note's operative content (no commutation obligation is ever created).
- The nil-witness form remains the right interface where no caller
  SubstWF exists — the bare global leaf — and is already served there by
  the global-oracle consumer `_closedFixedHead` (ADQ:2956).  Nothing in
  this decision forecloses it.

**Second interface introduced.**  The stratified `const` rule carries
only the constant's *type* certificate (SExpr:2383-2387); unlike the
strong constructor it carries no definitional-unfold premise.  The
unfold must therefore come from the witness's own `R` edge seed.  A
genuine child's all-depth result covers the value's native stratified
depth; a *local* (guarded-restart) seed is pinned to `depth+1` while the
registered value's certificate depth is unrelated — the exact
"registered premise deeper than the declared type" tripwire from the
2026-08-14 rung audit, now localized.  That branch is factored as
`LR.ConstDefnLocalStep Γ₀` (local seed on a registered definitional
value extends to every certificate depth), keeping the provable branch
proved and naming the budget question instead of patching it.

— session-C subagent 3

### SelfAdequateConstStep landed conditionally on two named leaf obligations (2026-08-15, session-C subagent 3)

Baseline at resumption: green, zero errors, exactly one `declaration uses
sorry` at the `LR.iotaWitnessStep` leaf (6540:8 before this session's
insertions).  Reconfirmed by full elaboration before any edit; the same
sole-sorry inventory holds after the landing (final log `main1`, exit 0:
the one warning at the leaf statement, moved only by insertions to
ADQ:6866, sorry token ADQ:6896; warning profile otherwise byte-identical
to the baseline modulo line shifts).

**Landed (kernel-checked; no new sorries; probe-verified first in
`plans/probes/probeC2-conststep.lean` against the fresh olean, then ported
verbatim):**

- `LR.CoherentIotaLeafStep Γ₀` (ADQ:5820): the internal iota-leaf
  obligation of the constant producer.  Inputs: the depth index, the
  per-`R`-edge seed family `∀ m M hr, CoherentSeedAt Γ₀ depth (hR m M hr)`
  and exact child trees (both drawn from the const witness's own
  `RDeepChildren` const branch), `Ctx.WF Γ₀`, the ambient
  `SubstWF Γ₀ σ σ' Δ ρ`, and the strict-predecessor coherent restart
  family.  Output: level-polymorphic `IotaLeafDefEqAt Γ₀ level c ls
  (Lower R)`.
- `LR.ConstDefnLocalStep Γ₀` (ADQ:5848): the definitional-unfold budget
  obligation — a local (guarded-restart) coherent seed on a registered
  definitional value extends to the value's own certificate depths.
- `LR.SelfAdequateConstStep.of_steps` (ADQ:5871, ~250 lines):
  `Ctx.WF Γ₀ → CoherentIotaLeafStep Γ₀ → ConstDefnLocalStep Γ₀ →
  SelfAdequateConstStep Γ₀`.  Everything else in the constant case is
  proved outright — see the case inventory below.
- `LR.CoherentSelfStep.of_leafSteps` (ADQ:6122): composition through
  `coherentSelfStep_of_steps`, so the full self-adequacy half of the
  coherent Nat algebra is now conditional on exactly
  `defeqStep`-family + the two new Props (and `defeqStep` is itself one
  hypothesis away via `SelfAdequateDefeqStepAt.of_lowerAdequacy` from the
  bootstrap rungs).

**Case inventory of the remake** (mirrors the old derivation-induction
const case at `adequacy_of_iotaWitnessStep`, with every induction
hypothesis replaced by witness-tree data):

- Witness `bot` / `Const.bot`: unchanged bottom collapses.
- `Const.lam` (the recursion): the constant-type observation that the old
  proof took from `ihTy` is now
  `(CoherentRetainedAt.restart lower (Nat.lt_succ_self depth)).1` at the
  sound-transported witness of the type — legitimate because the
  stratified `const` rule carries the type certificate at the strictly
  smaller `depth`.  The reached leaf callback `evalPat` is
  `PatternLeafDefEqAt.of_iota (leafStep (depth+1) hR hΓ₀ W pR cR lower k)`
  — the witness's own seeds, never the global sorried `iotaWitnessStep`.
- `Const.ctor` / `Const.indTy`: the `IndTyHead` fact the old proof took
  from `ihF` is recovered with no `F`-bundle at all: the same `lower`
  restart at the type witness, `toValTy` landing at the unfold-forced
  `.indTy` type shape, and the definitional `TyDefEq`-at-`.indTy`
  conjunction (the `indTy_m` simp lemma is `rfl`; the projection form
  needs the definitional bridge, not the simp set).
- `Const.pat` (nullary = definitional unfold): the old `ihDef` is
  replaced by the seed on the witness's own `R` edge (`Lower R` at the
  registered value).  Genuine child (`inl`): the all-depth result is
  consumed at the value's native stratified depth from
  `defn_whRed (Γ := Γ)` + `stratify`, then the goal closes by
  `(LR Γ₀).whr` along `defn_whRed (Γ := Γ₀)`'s one-step reduction.
  Local child (`inr`): `ConstDefnLocalStep` — the one branch with a real
  depth-budget gap (below).

**The seed-interface decision** is recorded in full in the preceding
section ("SelfAdequateConstStep interface decision", same date): seeds
stay at the ambient valuation pinned by the caller's `SubstWF`; the
`Valuation.nil` restatement demanded by the earlier design note is not
producible from the tree (per-edge retained results quantify over
`SubstWF` at their own valuation and do not transport across `closedAt`;
`RDeepChildren.closed`'s `hP` premise is that same underivable
stability), while the ambient-`W` interface is exactly what the
kernel-checked `_coherent` consumer threads with zero valuation
transport, so the note's operative content — never create a
`closedAt`-vs-`mono` commutation obligation — is satisfied by
construction.

**What discharging each hypothesis takes:**

1. `CoherentIotaLeafStep` is the chain wall, scoped: split the joint
   `RecursorIotaPattern` match (the `Matches.app` inversion already used
   by the bare leaf at ADQ:6866), normalize the major's free-closure
   `CtorDefEq` through `CtorDefEq.toChain` + rectangles, retype interior
   vertices with strictly-smaller bounded inversion
   (`JointStratifiedPathInversionAt.of_predecessorAdequacy`, ADQ:584),
   and per exact link run `iotaDefEq_of_ctorExactAt_coherent` (ADQ:4697)
   with `hP := CoherentRhsSeedAt.of_seed` applied to the received seeds —
   the right-injection branch needs the RHS typing raised to the seed's
   index, which is the same rung-audit question as item 2's.  Note the
   Prop hands over the raw `NatSeed` family untruncated plus the child
   trees, so the discharger keeps every option (including per-edge
   sub-restarts).  If the discharge turns out to need the constant's own
   type certificate as well, extend the Prop — it has exactly one call
   site (ADQ:6017, the `evalPat` construction).
2. `ConstDefnLocalStep` is the localized "registered premise deeper than
   the declared type" tripwire from the 2026-08-14 rung audit.  Two known
   discharge routes, to be decided at assembly time: (a) prove that the
   coherent tower only ever attaches local seeds to definitional-value
   edges together with a budget covering the value's certificate (then
   this Prop follows from the producer invariant — likely requires
   enriching `CoherentSeedAt`'s right injection with the coupled typing,
   the same enrichment `CoherentRhsSeedAt` models one level up); or
   (b) show closed registered values admit depth-extension of local
   coherent results directly.  Route (a) is an ADQ-file interface change
   with wide transport-lemma ripple; deliberately not attempted this
   session (two-strikes discipline).

**Opportunistic extension not attempted.**  The gate condition (short
hypothesis list) was met, but `CoherentFixedHeadStep`'s missing N2 piece
is the one OPEN interface decision the predecessor explicitly declined to
commit (`LowerSyncAt` / widened `hcap`), and it must be a prose decision
first.  With the session budget spent on the const landing and the
elaboration cycle, writing that decision well was not affordable; wiring
a skeleton conditional on an uncommitted N2 shape would be exactly the
premature commitment the pause was protecting against.

**Remaining tower (updated):**

1. `LR.CoherentIotaLeafStep Γ₀` (new, hard): the chain fold against the
   received seeds — this is where the G4 rung audit resolves (interior
   retyping depths vs the rung index).
2. `LR.ConstDefnLocalStep Γ₀` (new, medium): the local-seed budget for
   definitional values, routes (a)/(b) above.
3. `LR.CoherentFixedHeadStep Γ₀` (ADQ:4588, unchanged; medium once N2 is
   stated in prose): ordered spine→`FixedHeadTelescope` producer over the
   in-file `peelLayer`.
4. Assembly: `CoherentRetainedNatStep.of_steps` (ADQ:4601) from
   `CoherentSelfStep.of_leafSteps` (ADQ:6122) + item 3, then the bare
   leaf per rung via `iotaDefEq_of_ctorExactAt_natStep` (ADQ:4646) and
   the bootstrap (`contextualAdequacyAtDepth_of_iotaSteps`, ADQ:6829).

— session-C subagent 3

### The chain wall resolves as a G4 tripwire; the residual is named and wired (2026-08-15, session-C subagent 4)

Baseline at resumption: green, exit 0, zero errors, exactly one
`declaration uses sorry` at `LR.iotaWitnessStep` (6866:8 before this
session's insertions).  Reconfirmed by a full elaboration before any edit
(log `baseline`).  Final state after the landings below (log `edit1`, exit
0): zero errors, the same sole sorry warning at the same leaf statement,
moved only by insertions to ADQ:6985 (sorry token ADQ:7015).  The warning
profile is otherwise identical modulo line shifts, plus two new instances
of the file's already-accepted `unusedSectionVars` lint (56 → 58) for the
two new theorems that do not use `[Params.Semantic]`.

**Primary target `LR.CoherentIotaLeafStep Γ₀` (ADQ:5884): obstruction, not
a landing.  The rung audit fires the G4 tripwire.**  Per the standing
instruction the discharge line was stopped rather than patched, and the
residual was factored, named, and given both a producer and a consumer so
that it is a checkable object rather than a narrative.

#### The rung audit — the depth arithmetic, spelled out

The journaled recipe survives its first three steps and dies at the fourth.
Splitting the joint `RecursorIotaPattern` match and normalizing the major's
free closure through `LRS.CtorDefEq.toChain` (SLR:11390) are available.
More importantly, **every per-link consumer is inversion-free**: neither
`LRS.iotaDefEq_of_ctorExactAt_coherent` (ADQ:4751) nor the synchronized
rectangle `LRS.iotaDefEqRect_of_ctorExactAt` (ADQ:2887) takes a uniqueness,
inversion, or subject-reduction premise, and `LogRel.DefEqRect.trans`
(SLR:9960) composes shared-middle rectangles with pure logical-relation
transitivity.  So the *entire* residual is the fold that carries the
rectangle along the normalized chain.

That fold spends exactly two facts, and both are unbounded:

1. **Interior-vertex retyping.**  `LRS.CtorPath.foldRaw` (SLR:11072) calls
   `uniq hXY.hasType.1 hX` once per link, where `hXY : IsDefEq Γ₀ X Y
   A_link` is the link's own result type from `CtorExact.rawDefEq`
   (SLR:10937) and `hX : IsDefEq Γ₀ X X D` anchors the vertex at the
   recursor's major domain `D = pair.domain`.  `uniq : LogRel.RawTypeUniq
   Γ₀` (SLR:10446) has exactly one producer in the tree,
   `IsDefEq.uniq_of_stratified_inversion` (ADQ:646), whose induction is on
   `max n₁ n₂` for the two *existentially obtained* stratification depths
   of the vertex (`(h.strong hΓ).stratify`, ADQ:276-277, inside `uniqPath_of_stratified_inversion`) and which consumes
   the **unbounded** `JointStratifiedInversion`.  That package's only
   producer is `JointStratifiedInversion.of_adequacy` (ADQ:594) from
   `LR.ContextualAdequacyAt 1` — full level-one adequacy at *every* depth.
   At rung `d` the leaf holds only `∀ d' < d, ContextualAdequacyAtDepth d'`.
2. **Root subject reduction.**  `LRS.CtorChain.foldRaw`'s two root
   callbacks (SLR:11185) must move each major to its classified constructor
   spine at `D`; the only producer is
   `WHRedS.defeq_of_stratified_inversion` (ADQ:841), which internally
   spends `uniq_of_stratified_inversion` again at the reducing term's own
   depth.  Same unbounded package.

**Why no certificate reachable at the leaf bounds the depth in (1).**  Three
candidate bounds were checked and all fail, for three different reasons:

- *The rung index `d`.*  The bootstrap deliberately does not hand the
  produced rung's own certificate to the leaf (`_hstrat` at ADQ:6955; the
  docstring at ADQ:6943-6947 states why: the derivation induction is
  depth-blind, so a left-endpoint certificate cannot bound the leaf
  instances reached through `trans` or evaluator descent).  This is
  subagent 2's honesty note and it is load-bearing here.
- *The registered-rule certificates `rhsStratified` / `headStratified`
  (SLR:9280-9285).*  These are the ones the 2026-08-14 audit nominated, and
  they are the wrong side of the redex.  They bound the *contractum* — the
  applied RHS and its peeled fixed head, the latter exactly
  `capturePaths.length` shallower.  The chain lives on the **major**, i.e.
  the redex's inspected argument.  No arithmetic connects them.
- *The redex's own stratification, hypothetically granted.*  This is the
  decisive one.  Even if the leaf were handed
  `HasTypeStratifiedS Δ (rec … major) B core D`, `HasTypeStratifiedS.app`
  (SExpr:2388) would bound only the two **endpoint** majors at `D - 1`.  The
  chain's *interior* vertices are the middle terms of `LRS.CtorDefEq.trans`
  (SLR:10712), which relates `M ≡ N` and `N ≡ P` while retaining nothing
  whatsoever about `N` — no typing, no shape, no certificate.  An interior
  vertex is an arbitrary term of the ambient theory whose stratified depth
  is not a function of the endpoints' depths at all.  **This is the exact
  failing vertex.**

So the demand is not "inversion at some depth `< d`" that we failed to
arrange; it is "inversion at a depth that no premise in scope names".  There
is no depth arithmetic that makes it strictly-predecessor, and manufacturing
the package inside the proof would be precisely the same-rung
self-consumption G4 forbids.  Extending `CoherentIotaLeafStep`'s inputs with
the strict-predecessor contextual family therefore does **not** help, which
is why the sanctioned "extend the Prop, there is one call site" escape hatch
was not taken.

**The repair that would close it is not local, and it is not in this
session's territory.**  The erasure-north-star fix is to stop erasing the
middle vertex: index `LRS.CtorDefEq`/`CtorLink`/`CtorPath`/`CtorChain` by
the raw domain and have `trans` retain `IsDefEq Γ N N D`, after which
`CtorPath.foldRaw` needs no `uniq` at all.  That is a ShapeLogRel.lean
change and it was **not** attempted; more importantly it does not stay
local: `LRS.CtorDefEq` is consumed through `LRS.IndDefEq` (SLR:11544), whose
`trans` (SLR:11560) is the `trans` field of the `LogRel` record (SLR:9927),
and `LogRel` carries **no** raw-typing projection at all — `DefEq M N A m a`
does not imply `IsDefEq Γ M N A`.  So a strengthened `CtorDefEq.trans` would
make `IndDefEq.trans` underivable unless the logical relation itself is
given a soundness field, and that field's own `whr`/`unwhr` closure
conditions (SLR:9937) are subject reduction, i.e. the inversion package
again.  **Exact needed change, for the record:** either (i) `LRS.CtorDefEq`
gains a raw domain index with `trans` retaining the middle vertex's
self-typing *and* `LogRel` gains a raw-soundness field discharging
`IndDefEq.trans`'s new premise, or (ii) an environment-level discipline on
constructor result types (each constructor's instantiated result type is
determined by the constructor and its arguments) replaces general raw
uniqueness at exactly these vertices.  Route (ii) is the cheaper-looking one
and is untouched research.

**A second, independent blocker in the same fold, for whoever resumes.**  It
is mechanical, not circular, and it was not visible in the journaled recipe.
`CtorChain.RawAlgebra.exact` hands over a *framed* native leaf: `CtorFrame
Γ₀ (LR Γ₀) m J p` plus `CtorExact Γ₀ J X Y p` at the leaf's own level `k`
and shape `p`.  `iotaDefEqRect_of_ctorExactAt` pins the leaf's level to the
ambient recursor level (`out`/`outTy : WShape (nI+1)` are fixed by the
goal), and `CtorExact` has **no** level transport by design — its only
lemmas are `toCtorDefEq`, `symm`, `rawDefEq` (SLR:10912-10945), because
frames exist precisely to keep transports outside the native leaf
(SLR:10858-10861).  So the fold must run the iota *natively* at level `k`
and transport the finished rectangle back through the frame.  The parts for
that exist: `LE_Interp.Matches.lift`/`.unlift` (SLR:5287/5416) move the
match, `LE_Interp.RHS` is level-erased (`TShape`-valued) and needs no
transport at all, and `LogRel.LiftEquiv.rect` (SLR:10783) is exactly the
rectangle's transport iff.  Budget this as a real second layer.

#### Landed (kernel-checked; no new sorries)

- `LR.MajorChainFoldStep Γ₀` (ADQ:960): the named residual of the
  normalized-chain fold, as a two-field structure — `uniq :
  LogRel.RawTypeUniq Γ₀` and `subjectRed : WHRedS Γ₀ e₁ e₂ → IsDefEq Γ₀ e₁
  e₁ A → IsDefEq Γ₀ e₁ e₂ A`.  Stated as two separate fields rather than
  bundled as `JointStratifiedInversion` on purpose: a future producer may
  reach either half by other means (route (ii) above reaches the first
  without the second), and the fold consumes nothing else.
- `LR.MajorChainFoldStep.of_stratifiedInversion` (ADQ:972): the completed
  inversion package supplies both fields.  This certifies that the two
  named facts are *precisely* what the existing
  `foldRaw_of_stratifiedInversion` consumer spends — nothing else is hidden
  in the package, so the factorization is faithful rather than convenient.
- `LRS.CtorDefEq.foldRaw_of_majorChainFoldStep` (ADQ:981): the consumer.
  The free constructor-observation closure folds from the named residual
  alone, with no well-formedness hypothesis and no inversion package in
  sight.  The Prop is therefore both produced and consumed in-file, not a
  dangling definition.
- `LR.ConstDefnDeepStep Γ₀` (ADQ:5941) and
  `LR.ConstDefnLocalStep.of_deepStep` (ADQ:5957): the secondary target's
  reduction (below).
- `LR.CoherentSelfStep.of_leafStepsDeep` (ADQ:6241): the same assembly as
  `of_leafSteps` (ADQ:6229) against the strictly smaller definitional
  obligation, so the new Prop reaches the top-level composition.
- Docstring on `LR.CoherentIotaLeafStep` (ADQ:5884) now records the audit
  status inline, so the next reader of the Prop does not re-derive it.

#### Secondary target `LR.ConstDefnLocalStep` (ADQ:5912): route (b) refuted, obligation strictly reduced

Route (b) — "closed registered values admit depth-extension of local
coherent results directly" — is **not** provable from closedness, and the
reason is structural rather than a missing lemma.  `LR.SelfAdequateAt`
(ADQ:3796) mentions its depth index in exactly one place, the stratified
certificate it *consumes*; its conclusion `LR.Adequate …` is depth-free.
Since `HasTypeStratifiedS.mono` (SExpr:2414) raises a certificate to any
larger index, `SelfAdequateAt` is *stronger* at larger depth, and a local
seed at index `depth` already discharges every `depth' ≤ depth` with no
hypothesis at all.  All residual content is the strictly deeper case — and
closedness of the value says nothing about it: `value.Closed` constrains
substitution (`closed.mkInstS.subst_eq`), not stratification depth.

The real content of that residual is worth stating plainly, because it is
the same family of finding as the chain wall: **the stratified-depth measure
does not decrease along δ-unfolding.**  The stratified `const` rule
(SExpr:2383-2387) certifies only `SExpr.mkInst ls ci.type`; a definitional
value is routinely far deeper than its declared type (`def foo : Nat := ⟨big
term⟩`), so no environment-independent inequality can bound the value's
depth by the constant's.  The old derivation induction handled this because
`Params.Semantic.defn`'s equality is a *subderivation*; the witness-tree
remake replaced derivation induction with a Nat recursion whose index simply
does not travel across δ.  Note the call site is not rescued by the easy
half either: it obtains `nV` from `hdefΓ.stratify` (ADQ:6212), and
`.mono` lets that be taken arbitrarily large, so the `≤` half never applies
there.  Route (a) — couple the budget to the seed at its creation point, as
`CoherentRhsSeedAt` (ADQ:3976) already models one level up, with the budget
derived from the *value's* certificate rather than the constant's — remains
the only route, and it must be a producer-side change.  Deliberately not
implemented (two-strikes; wide transport ripple), exactly as the predecessor
scoped it.

What landed is the honest reduction: `ConstDefnLocalStep.of_deepStep`
(ADQ:5957) proves the whole `depth' ≤ depth` half unconditionally by
`HasTypeStratifiedS.mono`, spending **no** adequacy content — it is pure
depth arithmetic — leaving `ConstDefnDeepStep` (ADQ:5941) as a strictly
smaller obligation stated only for `depth < depth'`.

#### N2 capture-domain interface decision (prose, per the two-strikes rule)

The one open design decision, stated before any Lean, as required.  The
2026-08-14 N2 entry already ruled out pointwise widening of
`CaptureDefEqAligned` and adopted the joint two-telescope route, which is
landed as `LR.FixedHeadTelescope` (ADQ:1775) with `nil`/`cons`
(ADQ:1839/1854) and the N1 layer core `WShape.HasTypeLam.peelLayer`
(ADQ:1797).  What was left open is narrower and is the actual N2 question:
the telescope *synthesizes* its head-type observation from the captures
(`cons` builds `forallE tyDom tyFun` with `tyDom := capture`'s own
`typeShape`), while `LR.FixedHeadResultAt` (ADQ:2148) must consume a head
that observes the **registered** type `SExpr.mkInst recLs rule.df.type`.
Something must link the two.  The alternatives:

- **(i) Widened threading.**  Add the probe's `probeB.LowerSyncAt`
  (plans/probes/probeB-2.lean:63) to the tower's per-witness invariant: on
  demand from `head ≤ root`, a stratified certificate and `Fits`, it yields
  `∃ headElem headTy, headElem ≤ head ∧ headElem.HasType headTy ∧ Nonempty
  (Witness ρ headTy B)`, instantiated at `B :=` the registered type.  Its
  threading through the unary recursor is PROVED
  (`probeB.widenedThreading`).
- **(ii) State the link on the consumer's premise.**  Replace
  `FixedHeadResultAt`'s third premise — today the context-free fallback
  `(∃ headElem headTy, headElem ≤ head ∧ headElem.HasType headTy)`,
  ADQ:2171-2172 — by the ordered telescope itself together with
  `Nonempty (Witness ρ headTy (SExpr.mkInst recLs rule.df.type))` stated at
  the **telescope's own** `headTy` index.

**Decision: (ii).**  The argument is the eight-failure erasure pattern, and
it is decisive.  Option (i)'s conclusion is a *fresh* existential: the
invariant chooses some `headElem`/`headTy` pair, while the telescope has
already chosen the pair that every layer's `AtShapes` is indexed by.  Two
independently chosen shape pairs for the same head, with a reconciliation
obligation between them, is erasure #7 recurring one level up — the very
shape the 2026-08-14 entry rejected when it refused a standalone per-path
field ("a standalone field for each path cannot certify that its alleged
domain is the domain selected by the *same* registered-type observation").
Wrapping the semantic component in `Nonempty` makes it worse, not better:
the consumer receives a witness it provably cannot align with its own
telescope indices.  Option (ii) creates no reconciliation obligation at all,
because there is only ever one pair per layer, chosen once, and the
registered-type witness is attached to that same index.  This is also
verbatim what the 2026-08-14 decision already prescribed for the completed
certificate ("`FixedHeadResultAt` will consume that synchronized endpoint …
the current context-free `typedLowerHead` input remains useful only as the
shape fallback and must not be used to manufacture the final witness"), so
(ii) is continuation rather than a new commitment.

Note also that `widenedThreading` being PROVED argues only that the widening
is *possible*; it was recorded in the 2026-08-14 synthesis under "verified
non-risks", i.e. as evidence that adopting it would not break the recursion —
not as evidence that it should be adopted.

**Consequence, and why `CoherentFixedHeadStep` (ADQ:4642) was not attempted
after the decision.**  Decision (ii) is an interface change to
`FixedHeadResultAt`/`FixedHeadResult` (ADQ:2101/2148) with an enumerable but
real ripple — `iotaDefEq_of_ctorExactAt_fixedHead`, `_closedFixedHead`,
`_coherent`, `FixedHeadResult.mono`, `FixedHeadResult.of_forall_at`, and the
`CoherentRetainedResult.fixedHead` projection.  Landing the premise change
and the ordered producer in one session, after the audit and its elaboration
cycles, would have put the green state at risk for a partial result; wiring
a skeleton against an unchanged premise would bake in the fallback the
decision just rejected.  The next session should land the premise change
first, as its own green step, and only then build the producer at the
`constDefEq`/`Matches` materialization boundary where the registered-type
evidence is still in scope.

#### Remaining tower (updated)

1. `LR.MajorChainFoldStep Γ₀` (ADQ:960, NEW, blocked): the chain wall,
   reduced to two named raw facts.  Not reachable from any adequacy rung;
   see the audit above.  Next moves are the two repairs named there, both
   outside `ShapeLogRelAdequacy.lean` — (i) retain the middle vertex in
   `LRS.CtorDefEq` plus a `LogRel` soundness field, or (ii) an
   environment-level constructor-result-type discipline.  Recommend
   scoping (ii) first: it is local to the vertices that actually occur.
2. `LR.CoherentIotaLeafStep Γ₀` (ADQ:5884, still unproved): now known to
   reduce to item 1 plus the mechanical multi-level frame layer.  Do not
   re-attempt before item 1 has an answer.
3. `LR.ConstDefnDeepStep Γ₀` (ADQ:5941, NEW, strictly smaller than the
   retired-in-half `ConstDefnLocalStep`): the δ-unfold depth budget.  Route
   (a), producer-side, with the budget taken from the value's own
   certificate.
4. `LR.CoherentFixedHeadStep Γ₀` (ADQ:4642, unchanged): N2 is now decided
   (option (ii) above).  Land the `FixedHeadResultAt` premise change first,
   then the ordered producer over `peelLayer` (ADQ:1797).
5. Assembly: `CoherentRetainedNatStep.of_steps` (ADQ:4655) from
   `CoherentSelfStep.of_leafStepsDeep` (ADQ:6241) + item 4, then the bare
   leaf per rung via `iotaDefEq_of_ctorExactAt_natStep` and the bootstrap
   `contextualAdequacyAtDepth_of_iotaSteps` (ADQ:6948).

One structural observation worth carrying forward, since items 1 and 3 are
the same finding twice: the stratified-depth measure decreases along
syntax-directed typing but **not** along the two moves the joint leaf
actually needs — δ-unfolding (item 3) and free-closure transitivity on
constructor observations (item 1).  A depth-indexed fixpoint cannot by
itself reach either.  Both residuals are now named, so the next design pass
can be about those two moves specifically rather than about the fixpoint.

— session-C subagent 4

### Chain-wall repair: the reconciliation moves to the constructor observation (2026-08-15, session-C subagent 5)

Written before any Lean, as the prose-first rule requires.  The task was to
discharge `LR.MajorChainFoldStep` (ADQ:960) by a structural change.  Below is
the route comparison, the choice, and — because it is the part that decides —
what the choice does *not* buy.

#### What the fold actually spends, restated exactly

`LRS.CtorPath.foldRaw` (SLR:11072) does not use `uniq` to type the middle
term of a `trans`.  It uses it, once per link, to reconcile **two independent
type observations of the link's left vertex**: the link's own natural result
type `A` (from `CtorExact`'s retained `hspine : SpineWF Γ CHead args.reverse
A`, surfaced by `CtorExact.rawDefEq`, SLR:10937) against the running anchor
`D` threaded from the root.  For the first link the anchor is the recursor's
major domain; for every later link it is `hXYD.hasType.2`, i.e. the anchor
*transported by the previous link*.  So the residual is not "type the middle
vertex" — the middle vertex is already typed at `D` by construction once the
previous link has been retyped.  The residual is: **the link's own result
type and the inherited anchor are two derivations that must be identified.**

This restatement is what separates the two candidate routes, and it kills one
of them outright.

#### (R1) Retain the middle vertex — refuted, twice, and for a new reason

The predecessor's R1 was "index `CtorDefEq` by the raw domain and have `trans`
retain `IsDefEq Γ N N D`".  Two findings:

- *The blocker the predecessor named is not fatal.*  The audit said a raw
  component on `CtorDefEq`/`IndDefEq` cannot survive `whr`/`unwhr`, because
  those closure conditions would become subject reduction.  That is true for a
  component stated about `M` and `N` — but **not** for one stated about their
  classified spines.  `LRS.CtorView.whr`/`.unwhr` (SLR:10955/10963) move a
  view across a weak-head reduction in *both* directions using only
  `WHRedS.determ_l … .ctorSpine`, i.e. weak-head determinism at classified
  constructor spines.  A component of the form `∀ X, CtorView Γ M X → P X` is
  therefore exactly whr-invariant with no subject reduction at all.  Recorded
  because it is a reusable fact: the whr regress the audit feared is avoidable,
  and any future raw component on the ctor branch of the relation should be
  stated on views rather than on roots.
- *R1 nevertheless fails, one level down.*  Even with whr survived, a
  D-indexed `CtorDefEq` must produce `IsDefEq Γ X Y D` at its `exact`
  constructor for the externally chosen `D`, and there the leaf has only its
  own `A`.  The reconciliation is not removed; it is relocated to the leaf
  **and simultaneously made harder**, because `LogRel.conv` (SLR:9930) changes
  the raw type index `A` of `IndDefEq` using only `LRS.TyDefEq`, which at
  `.indTy` is `IndTyHead Γ A ∧ IndTyHead Γ B` (SLR:11629) and carries *no* raw
  type equality.  A raw component pinned to `IndDefEq`'s own `A` is destroyed
  by `conv`.  So R1 must in any case be stated anchor-*polymorphically*, at
  which point it is R2 with extra indices.  Two strikes; R1 abandoned.

#### (R2) Constructor-result-type discipline — chosen, in the form below

The chosen shape, and the reason it is the right one, is that it makes the
reconciliation *anchor-polymorphic and leaf-local*:

- `LRS.CtorRetype Γ X Y`: a two-field **transport**, `∀ D, IsDefEq Γ X X D →
  IsDefEq Γ X Y D` and its right-hand mirror.  Not an existential, not a sort
  equality: it is the retyping *action* the fold performs, retained as data.
- `LRS.CtorAnchorDisciplineAt Γ IH m`: that transport is available for every
  framed native leaf of the root observation, with the frame and the leaf both
  in hand — exactly the signature `CtorPath.RawAlgebra.exact` (SLR:11064)
  already receives, so the discipline is scoped to the leaves that actually
  occur under the root shape rather than to the whole environment.
- `LRS.CtorSpineTypeUniqPath Γ`: the environment-level statement the
  discipline reduces to — *the declared result type of a registered
  constructor determines the type of its applications*, path-valued.

Every closure operation of the chain machinery is then free of new premises:
`foldRaw`'s per-link `uniq` call is replaced by the leaf's own transport, and
`trans` needs nothing, because after the first link the anchor travels with the
term.

**Why this survives the eight-failure erasure pattern.**  The north star is
retain more; proof-relevant, positional, replayable; never truncate to
Prop/existence what a consumer needs.  Judged against it:

1. *Proof-relevant rather than existential.*  `RawTypeUniq`'s conclusion is
   `∃ u, IsDefEq Γ A B (.sort u)` — the consumer must then pick `u` and
   `defeqDF` by hand, and every call site re-chooses.  `CtorRetype` hands over
   the transport itself, already applied to the right endpoint.  Nothing is
   existentially quantified that a consumer must re-align.
2. *Positional.*  The discipline is indexed by the *frame and leaf* of the
   observation it serves, so a consumer cannot accidentally satisfy it with a
   retyping of some other constructor spine.  This is the same discipline the
   2026-08-14 N2 entry enforced when it refused a standalone per-path field:
   one pair per position, chosen once.
3. *Path-valued, so no premature collapse.*  `CtorSpineTypeUniqPath` returns
   `TypeDefEqPath` (SLR:10121), not a single conversion.  `TypeDefEqPath`
   exists precisely because adjacent type equalities may assign different
   universes, and `TypeDefEqPath.collapse` (SLR:10460) charges *the whole of
   raw type uniqueness* for the collapse.  Since the fold only ever transports
   term equalities (`TypeDefEqPath.defeqDF`, SLR:10157), collapsing first
   would be erasure #2 — throwing away the sequence a consumer never needed
   flattened.  The reduction therefore never asks for it.
4. *Additive.*  `CtorDefEq`, `CtorExact`, `IndDefEq` and `LogRel` are not
   touched; the anchored fold lands beside the existing one.  No consumer of
   the free relation loses anything it has today, and the old
   `foldRaw_of_majorChainFoldStep` stays green as the reference consumer.

**What the choice does not buy, stated plainly so the next session does not
rediscover it.**  It does **not** make the residual reachable from a strict
predecessor adequacy rung.  Interior vertices are still classified constructor
spines of unbounded stratified depth, and *any* identification of two type
observations of the same term must invert at least one of the two derivations:
`HasTypeStratifiedS.app_inv` (SExpr:2613) walks a spine, but reconciling the
two codomains at each application step is Pi inversion at that vertex's own
depth.  There is no reformulation of the fold that escapes this — the two
types genuinely originate in two independent derivations, so the repair must
remove the *independence*, and the only place independence can be removed is
the producer of constructor observations, where the constructor's declared
type is available and there is exactly one of it.

That is the whole content of the choice: the obligation is moved **out of the
depth-indexed fixpoint** and onto the environment, where it has no depth index
to be blocked on.  `MajorChainFoldStep` demanded `LogRel.RawTypeUniq Γ₀` for
arbitrary terms plus subject reduction for arbitrary reductions; what replaces
it demands a retyping only for terms carrying a native `CtorExact` certificate,
plus subject reduction only for reductions **to a classified constructor
spine** — and the latter, per the 2026-08-15 audit's own third bullet, is the
one half a redex certificate does bound (`HasTypeStratifiedS.app`, SExpr:2388,
bounds the two endpoint majors at `D - 1`).  Removing the interior demand is
therefore what makes the endpoint bound worth having.

— session-C subagent 5 (design decision; landing recorded below)

#### Landed (kernel-checked; no new sorries; additive, zero ripple)

Baseline at resumption, reconfirmed by a full elaboration before any edit (log
`baseline-adq`, exit 0): zero errors, exactly one `declaration uses sorry` at
the `LR.iotaWitnessStep` leaf, ADQ:6985:8.  Final state after everything below:
zero errors in both edited files, `ShapeLogRel.lean` with zero sorries, the
same sole sorry warning in `ShapeLogRelAdequacy.lean` at the same leaf
statement, moved only by insertion to ADQ:7062:8.  Warning profile otherwise
identical modulo line shifts, plus two further instances of the file's already
accepted `unusedSectionVars` lint (81 → 83 file-anchored warnings) for the two
new theorems that do not use `[Params.Semantic]`.  `ShapeLogRel.lean` gained
no warnings beyond its existing profile.

In `Lean4Lean/Experimental/ShapeLogRel.lean`:

- `LRS.CtorRetype` (SLR:11112) and `.symm` (SLR:11119): the two-field retyping
  transport of one native link.
- `LRS.CtorSpineTypeUniqPath` (SLR:11135): the environment-level constructor
  result-type discipline, path-valued.
- `LRS.CtorSpineTypeUniqPath.of_rawTypeUniq` (SLR:11147): raw type uniqueness
  supplies it by a single-edge path — the faithfulness certificate that the
  new obligation is *implied by* the one it replaces.
- `LRS.CtorExact.retype_of_ctorSpineTypeUniqPath` (SLR:11161): the discipline
  retypes any native exact link.  The right-endpoint field is the interesting
  one: it applies the discipline twice at that endpoint's own spine
  certificate — once against the link's type, once against the requested
  domain — and composes the two paths.  No sort index is ever identified, so
  `TypeDefEqPath.collapse` (and with it the whole of raw type uniqueness) is
  never charged.
- `LRS.CtorAnchorDisciplineAt` (SLR:11188) with `.of_ctorSpineTypeUniqPath`
  (SLR:11194) and `.of_rawTypeUniq` (SLR:11200): the frame-scoped form the
  folds consume.
- `LRS.CtorPath.foldRaw_of_anchorDiscipline` (SLR:11210),
  `LRS.CtorPath.rawDefEqAt_of_anchorDiscipline` (SLR:11229),
  `LRS.CtorChain.foldRaw_of_anchorDiscipline` (SLR:11356),
  `LRS.CtorChain.rawDefEqAt_of_anchorDiscipline` (SLR:11374),
  `LRS.CtorDefEq.foldRaw_of_anchorDiscipline` (SLR:11625),
  `LRS.CtorDefEq.rawDefEqAt_of_anchorDiscipline` (SLR:11636): the complete
  raw-consumer surface of the chain machinery, re-landed without
  `LogRel.RawTypeUniq`.  All six have the same statements as their `uniq`-taking
  originals (SLR:11041/11072/11155/11185/11416/11428), which are untouched.

In `Lean4Lean/Experimental/ShapeLogRelAdequacy.lean`:

- `LR.MajorChainAnchorStep Γ₀` (ADQ:1015): the repaired residual, two fields —
  `ctorRetype` (per-framed-leaf transport) and `rootRed` (subject reduction *to
  a classified constructor spine*, i.e. the two root views only).
- `LR.MajorChainAnchorStep.of_ctorSpineTypeUniqPath` (ADQ:1030): the intended
  producer, taking the environment-level discipline directly.
- `LR.MajorChainAnchorStep.of_majorChainFoldStep` (ADQ:1040): the old residual
  implies the new one, so this is a weakening and not a restatement.
- `LRS.CtorDefEq.foldRaw_of_majorChainAnchorStep` (ADQ:1053): the consumer.
  Identical statement to `foldRaw_of_majorChainFoldStep` (ADQ:981), which stays
  green beside it as the reference consumer.
- The status paragraph of `LR.CoherentIotaLeafStep` (ADQ:5961) now records the
  repair and the surviving mechanical multi-level frame layer inline.

**Ripple: none, by construction.**  `LRS.CtorDefEq`, `LRS.CtorExact`,
`LRS.CtorLink`, `LRS.CtorPath`, `LRS.CtorChain`, `LRS.IndDefEq` and `LogRel`
are untouched — no constructor gained a premise, no structure gained a field,
so not one existing consumer changed.  Enumerated before editing: the free
relation is reached through `IndDefEq` (SLR:11544 pre-edit) which is the ctor
branch of `LR`, hence through `LogRel`'s `trans`/`whr`/`conv`; every one of
those would have been a breaking site under R1.  Landing beside the existing
fold instead of inside it avoids all of them, as the additive-first rule
prefers.  `LogRel.RawTypeUniq` still has its original consumers; nothing was
removed.

#### What `MajorChainFoldStep` now reduces to

Precisely, and with the honest limits stated:

1. **Interior of the chain: discharged outright.**  `CtorPath.foldRaw` used to
   call `uniq` once per link.  `CtorPath.foldRaw_of_anchorDiscipline` calls
   nothing: the link retypes itself and its retyped right endpoint anchors the
   tail.  The unbounded family of interior obligations is gone from the
   consumer, not renamed.
2. **Per native leaf: `LRS.CtorSpineTypeUniqPath Γ₀`.**  This is where the
   payment now sits, and it has *no depth index at all* — it has left the
   depth-indexed fixpoint.  Its subject is a registered constructor
   application with its head typing and spine certificate retained; its
   content is that a registered constructor's declared result type is the type
   of its applications.
3. **At the two roots: `rootRed`.**  Weak-head subject reduction restricted to
   reductions that land on a classified constructor spine.

**A correction to the 2026-08-15 audit's endpoint claim, since it matters for
whoever discharges item 3.**  The audit observed that a redex certificate
bounds the two endpoint majors at `D - 1` (`HasTypeStratifiedS.app`,
SExpr:2388), and that reads as though `rootRed` is therefore reachable.  It is
not, quite: `WHRedS` is the reflexive-transitive closure, and
`WHRedS.defeq_of_stratified_inversion` (ADQ:841) inducts along the sequence
taking each next step's typing from `ih.hasType.2` — an `IsDefEq` whose own
stratified depth is existential.  The redex certificate bounds the *first*
step only.  So item 3 is a well-posed *local* target — one reduction sequence
from one bounded term — but it needs a subject-reduction lemma that
re-certifies each reduct, which does not exist yet.  Worth noting that the
single-step producer's one uniqueness use in the registered-action case
(`uniq hcore.hasType action.sound.hasType.1`, ADQ:836) is on the *contractum*,
which is exactly the side `rhsStratified`/`headStratified` (SLR:9280-9285) do
bound — so for the root callbacks, unlike for the interior, the registered-rule
certificates are on the right side of the redex after all.

#### Secondary: `LR.ConstDefnDeepStep` (ADQ:6018) — not landed, and deliberately not faked

The instruction was to look for whether the primary repair also serves the
δ-unfold budget.  It does, as a *principle*, and not as a lemma; both halves
are worth recording.

The principle transfers exactly.  The call site (ADQ:6284) obtains the value's
stratification depth by `obtain ⟨nV, -, hstratV⟩ := hdefΓ.stratify` — an
existential index re-chosen at consumption time — and then needs
`SelfAdequateAt Γ₀ hV nV` while the local seed offers only `depth + 1`.  That
is the same erasure as the chain wall: an index the producer already knew is
discarded and re-chosen downstream.  The repair is the same shape too — retain
it at creation, i.e. give the local (`NatSeed` right-injection) branch on a
registered definitional edge the value's own certificate at the seed's index,
exactly as `CoherentRhsSeedAt` (ADQ:4048) already does one level up — after
which the call site consumes the retained certificate and the deep case
disappears entirely rather than being discharged.

The lemma does not transfer.  For the chain, the obligation's *subject* could
be narrowed (from arbitrary terms to certified constructor spines) and that
was enough.  Here the obligation is a universally quantified *index*
(`∀ depth', depth < depth' → SelfAdequateAt Γ₀ hV depth'`), and no leaf-local
retention weakens a quantified index — only bounding the demand does, which is
a producer-side change to the seed interface with the transport ripple the
predecessor already scoped.  Two strikes on route (b) (refuted), route (a) not
attempted.

One thing was deliberately *not* done, and the next session should not do it
either: factoring `ConstDefnDeepStep` through a "certificate lowering" Prop of
the form `HasTypeStratifiedS Δ X B core depth' → HasTypeStratifiedS Δ X B core
depth`.  That reads like the analogous narrowing but is underivable, and worse,
false in spirit: `HasTypeStratifiedS.defeq` (SExpr:2405) lets a certificate
reach an arbitrary type `B` at an arbitrary larger index, so no lowering to a
seed index chosen by an unrelated guarded restart can hold.  It would be a
hypothesis no producer could ever discharge — the exact failure mode the
2026-08-15 interface-decision section rejected for nil-restated seeds.

#### Tertiary: not attempted

Gated on the secondary being resolved, which it is not.  The N2 decision
(option (ii)) and its ~five-consumer ripple stand exactly as the previous
session left them.

#### Remaining tower (updated)

1. `LRS.CtorSpineTypeUniqPath Γ₀` (SLR:11135, NEW): the environment-level
   constructor result-type discipline.  This is the interior half of the chain
   wall, now outside the depth fixpoint.  It is the first residual in this
   development that a *generation-side* argument can attack, because its
   subject is a registered declaration rather than an arbitrary derivation.
2. `LR.MajorChainAnchorStep.rootRed` (ADQ:1015): root subject reduction to a
   classified spine.  Needs a re-certifying multi-step subject-reduction
   lemma; see the correction above for why the redex certificate alone is not
   enough and where the rule certificates *do* apply.
3. `LR.CoherentIotaLeafStep Γ₀` (ADQ:5961, unproved): items 1 + 2 plus the
   mechanical multi-level frame layer (run the rectangle natively at the
   leaf's level `k`, transport back through `LogRel.LiftEquiv.rect`,
   SLR:10783).
4. `LR.ConstDefnDeepStep Γ₀` (ADQ:6018, unproved): route (a) only, as a
   producer-side retention of the value's certificate at seed creation.
5. `LR.CoherentFixedHeadStep Γ₀` (unchanged): N2 decided; land the
   `FixedHeadResultAt` premise change first, then the ordered producer over
   `peelLayer`.
6. Assembly: `CoherentRetainedNatStep.of_steps` from
   `CoherentSelfStep.of_leafStepsDeep` + item 5, then the bare leaf per rung
   and the depth bootstrap.

`LR.MajorChainFoldStep` (ADQ:960) and its two lemmas are kept, unused by the
new path, as the reference statement of what the repair removed.

**Build note for the fixture slice:** this session changed `ShapeLogRel.lean`
and rebuilt only `Lean4Lean.Experimental.ShapeLogRel` and
`Lean4Lean.Experimental.ShapeLogRelAdequacy`.  The D0/D1/D2 fixture oleans
(`SExprParamsD0/D1/D2`) are stale by design and need a rebuild before they are
trusted again.  The change is purely additive, so no fixture source edit is
expected.

— session-C subagent 5

### The chain-wall residual collapses to Pi injectivity; both fields of `MajorChainAnchorStep` land (2026-08-15, session-C subagent 6)

Baseline at resumption, reconfirmed by a full elaboration before any edit
(log `baseline-adq`, exit 0): zero errors, exactly one `declaration uses
sorry` at the `LR.iotaWitnessStep` leaf (ADQ:7062:8), plus `SExpr.lean`'s four
off-path sorries.  Final state: zero errors in both edited files;
`ShapeLogRel.lean` with **zero** sorries; `ShapeLogRelAdequacy.lean` with the
same sole sorry at the same leaf, moved only by insertion to ADQ:7115:8 (token
ADQ:7145).  Both warning profiles are **identical to baseline, not merely
comparable**: `diff` of the two sorted, line-number-stripped warning sets is
empty on both files (23 → 23 in `ShapeLogRel.lean`, 83 → 83 in
`ShapeLogRelAdequacy.lean`).  Every landed declaration depends on nothing but
`propext` / `Classical.choice` / `Quot.sound` — checked by `#print axioms` in
`plans/probes/probeA6-spine.lean` — so no `sorryAx` is reachable and none of
`SExpr.lean`'s off-path sorries is touched.

Both remaining items of the previous session's tower are discharged.  They
turned out to be the *same* obligation, and the obligation is smaller than
either half was thought to be.

#### The move: stop erasing the conversions a stratified typing already carries

The predecessor's route comparison was right about where the payment sits and
wrong about how much of it there is.  The decisive observation is an erasure
repair one level below anything the previous four sessions inspected.

`HasTypeStratifiedS.to_core` (SExpr:2580) strips the outer conversions of a
stratified typing and returns only `∃ A', Γ ⊢ e :! A' !! n`.  It *throws the
conversions away*.  That single discard is the entire reason
`HasTypeStratifiedS.core_aligned_of_typeUniq` (ADQ:794) has to buy the
alignment back with `LogRel.RawTypeUniq`, and therefore the reason every case
of `WHRed.defeq_of_stratified_inversion` (ADQ:821) opens by spending the full
`JointStratifiedInversion` package.  But the discarded conversions are
`IsDefEqStrong … (.sort u)` edges — they already *are* a `TypeDefEqPath`.
Retaining them costs nothing: `HasTypeStratifiedS.to_core_path` (SLR:11194) is
the same induction as `to_core` with the path threaded, and its base case
closes from `HasTypeStratifiedS.isType` (SExpr:2716), which every
syntax-directed core derivation already carries.

This is the north star applied to a lemma nobody had looked at: the producer
knew the conversions, the consumer needed them, and the interface in between
truncated them to an existential.  Everything below is what falls out.

#### Target 1 — `LRS.CtorSpineTypeUniqPath` (SLR:11135): the generation-side argument

With the path retained, the discipline reduces in three steps, of which the
first two are *free* — no adequacy, no uniqueness, no inversion, nothing.

1. **Any typing of an application spine already is a `SpineWF`.**
   `HasTypeStratifiedS.spineWF_of_foldl` (SLR:11278): from
   `Γ ⊢ es.foldl (·.app ·) hd : V !! n` one recovers a typing of `hd` together
   with `SExpr.SpineWF Γ HdTy es V`.  The recursion is on the *argument list*,
   not on a depth; each `app` node is exposed by `to_core_path`; and the
   conversions that node discards are absorbed by `SpineWF.conv_path`
   (SLR:11223), because `SpineWF` is already closed under conversion at both
   ends (`conv`/`ret`, SExpr:1398-1405).  Nothing is identified anywhere.
   Contrast `HasTypeStratifiedS.foldl_app_head` (SExpr:2629), which walks the
   same spine and retains only the head — erasure of exactly the layer
   structure this needs.
2. **The head is a registered constant, and a registered constant has one
   type.**  `LRS.constTypeUniqPath` (SLR:11304): two typings of `.const c ls`
   are path-equal.  Both core derivations must be the stratified `const` rule,
   whose displayed type is literally `SExpr.mkInst ls ci.type`; the
   environment is a function, so `env.constants c = some ci₁` and
   `= some ci₂` give `ci₁ = ci₂` and the two types are *syntactically
   identical*.  The retained paths then compose.  **This step consumes
   nothing at all.**  It is the generation-side content of the whole repair,
   and it is why the residual has no depth index: its subject is a registered
   declaration, and the fact used about it is settled at declaration time, not
   at derivation time.
3. **The two spine runs are compared layer by layer.**
   `SExpr.SpineWF.result_path` (SLR:11345): two `SpineWF`s over the *same*
   argument list from path-equal head types reach path-equal results.  Each
   layer inverts the Pi that `SpineWF.cons_path` (SLR:11250) exposes as the
   running path's right endpoint, then substitutes the shared argument into
   the codomain path (`TypeDefEqPath.subst`, SLR:10184).

Only step 3 has content, and its content is exactly **Pi injectivity for type
paths**.  That is the single named residual, `LRS.PiPathInv` (SLR:11332):

    ∀ {Γ A B A' B' s}, Ctx.WF Γ →
      TypeDefEqPath Γ (.forallE A B) (.forallE A' B') s →
      ∃ u v, TypeDefEqPath Γ A A' u ∧ TypeDefEqPath (A :: Γ) B B' v

Three absences in that statement are load-bearing and were each a separate
failure mode in earlier sessions.  *No stratification index* — unlike
`JointStratifiedPathInversion.forallEInv` (ADQ:234) it demands no endpoint
certificates, so no consumer must name a depth, and the G4 tripwire has
nothing to fire on.  *No universe alignment* — `sortPathInv` is never used by
any consumer below.  *No collapse* — the conclusion is again path-valued, so
`TypeDefEqPath.collapse` (SLR:10460), which is the whole of raw type
uniqueness, is never charged.  `LRS.PiPathInv.of_adequacy` (ADQ:267) is the
producer, and it is `TypeDefEqPath.forallE_inv_of_adequacy` (ADQ:177)
repackaged with nothing added — that theorem already requests no certificate.

The general statement is `LRS.constSpineTypeUniqPath` (SLR:11373): *any* two
typings of one fully-applied registered-constant spine are path-equal.
`LRS.CtorSpineTypeUniqPath.of_piPathInv` (SLR:11393) is the instance.  Worth
recording explicitly: **the proof never uses `Params.classify c = some (.ctor
_)`.**  The result-type discipline is not special to constructors — it is the
discipline of registered declarations, and the constructor classification only
selects which spines the fold happens to meet.  That is the honest scope of
route (ii) of the 2026-08-15 audit, and it is wider than the audit guessed.

#### Target 2 — `rootRed` (ADQ:1040): the re-certifying lemma is not needed

The brief for this session was to build a *re-certifying* multi-step subject
reduction: one that carries the stratification certificate along the whole
`WHRedS` rather than losing it after the first step, since
`WHRedS.defeq_of_stratified_inversion` (ADQ:866) takes each next step's typing
from `ih.hasType.2`, whose depth is existential.

That design is correct as a diagnosis and unnecessary as a construction.  The
obstruction is dissolved rather than answered: once the per-step lemma names
no depth, the induction has nothing left to lose.  Re-proving the single step
against the retained path, `WHRed.defeq_of_piPathInv` (SLR:11422):

* `app` and `major` become **free** — their only cost was
  `core_aligned_of_stratified_inversion`, and `IsDefEq.core_aligned_path`
  (SLR:11212) supplies the same alignment with no premise;
* `beta` spends **only `LRS.PiPathInv`**, in place of the collapsed
  `inv.forallEInv`;
* `extra` (a registered contraction) spends **only the spine discipline of
  Target 1**.  `Pattern.MatchesS.head_spine` (SExpr:899) says a matched redex
  *is* a constant-headed application spine, so its core type and the type
  carried by `Pattern.Action.sound` are two typings of one registered spine —
  reconciled by exactly the environment-level fact the constructor leaves use.

`WHRedS.defeq_of_piPathInv` (SLR:11464) is then the three-line induction, with
no certificate threaded and none needed.  The predecessor's correction about
which side of the redex the rule certificates bound is therefore moot for this
route: no side of the redex needs a certificate.  Note also that the general
form is proved — the restriction of `rootRed` to reductions landing on a
*classified* spine is never used, so that narrowing can be dropped from any
future interface without cost.

#### What this does and does not buy

`LR.MajorChainAnchorStep.of_piPathInv` (ADQ:1092) discharges **both** fields
from `LRS.PiPathInv` plus `Ctx.WF Γ₀`.  Measured against what
`MajorChainAnchorStep.of_majorChainFoldStep` (ADQ:1065) needs — the collapsed
`JointStratifiedInversion`, i.e. `IsDefEq.uniq_of_stratified_inversion`
(ADQ:671, a well-founded induction on `max n₁ n₂`) *plus*
`TypeDefEqPath.collapse_of_stratified_inversion` (ADQ:422) *plus* the sort
inversion — this is a strict and large weakening.  `LRS.PiPathInv` is *implied
by* the package it replaces: `LRS.PiPathInv.of_jointStratifiedPathInversion`
(ADQ:276) is the faithfulness certificate, recovering the endpoint
certificates `forallEInv` demands from the path's own two self-typings.

What it does **not** buy, stated plainly so the next session does not
rediscover it.  `LRS.PiPathInv` is still produced only from
`LR.ContextualAdequacyAt 1`, so at a leaf inside the depth bootstrap it is not
yet available.  The depth-*bounded* rung that does exist —
`IsDefEqStrong.forallE_invPath_of_adequacyAtDepth` (ADQ:555), reachable from a
strict predecessor family via `JointStratifiedPathInversionAt.of_predecessorAdequacy`
(ADQ:609) — does **not** discharge `PiPathInv`, for a reason that is now
precise rather than atmospheric: the Pis inverted by `SpineWF.result_path` are
the types occurring along the spine of a *native chain leaf*, and those leaves
are the chain's interior vertices, whose stratified depth the 2026-08-15 audit
already showed is not a function of the endpoints'.  A bounded rung needs the
Pi's own depth `≤ depth`; nothing names that depth.  So the residual is
genuinely one proposition now, but it is still a proposition about the whole
theory rather than about a predecessor rung.

Two further consequences worth carrying, both free:

* `IsDefEq.core_aligned_path` (SLR:11212) is a drop-in strengthening of
  `IsDefEq.core_aligned_of_stratified_inversion` (ADQ:805) for every consumer
  that only transports a term equality.  Any remaining call site of the latter
  that does not then collapse is spending the full package for nothing.
* `HasTypeStratifiedS.spineWF_of_foldl` (SLR:11278) turns any spine typing
  into the retained layer certificate the generated-iota machinery already
  speaks in.  It is the premise-free converse of `SpineWF.hasType`
  (SExpr:1524) and should be reached for before any new spine inversion is
  written.

#### Item 3 (`LR.CoherentIotaLeafStep`, ADQ:6014): assessed, deliberately not started

Per the brief this was to be attempted opportunistically if both targets
landed.  It was assessed and not started, and the reason is a concrete
specification rather than a budget excuse.

The audit's second blocker — run the iota natively at the framed leaf's own
level `k` and transport the finished rectangle back through
`LogRel.LiftEquiv.rect` (SLR:10783) — is *not* mechanical, because of a shape
mismatch that is easy to miss.  `LogRel.DefEqRect R M₁ M₂ N₁ N₂ A m a`
(SLR:9946) is indexed by an **element** shape and a **type** shape, both
`WShape n`.  `LRS.CtorFrame Γ IH m J p` (SLR:10862) is indexed by the two
**constructor-observation** shapes, `WShape (n+1)` and `WShape (k+1)`, and
carries no element or type shape at all.  So a standalone
`CtorFrame`-indexed rectangle transport would have to *quantify* the element
and type shapes and their `HasType`/`≤` side conditions (`DefEqRect.mono_l`
SLR:9976, `.mono_r_1/2` SLR:9985/9995, and `LiftEquiv.rect`'s own `hma`).
That is a second, independently chosen shape pair for one position — erasure
#7, exactly the failure the N2 decision refused in the 2026-08-15 entry.

The right construction therefore threads the element shape **positionally**
from the leaf that already owns it, which makes it a producer-side step inside
item 3's own leaf assembly, not a reusable lemma that can be landed first.
Recorded so the next session builds it in the right place rather than
manufacturing a plausible-looking transport lemma its consumer cannot align
with.

#### Remaining tower (updated, renumbered)

1. `LRS.PiPathInv` (SLR:11332, NEW): path-valued Pi injectivity.  **The sole
   residual of the chain wall**, replacing former items 1 and 2 in their
   entirety.  Depth-free, universe-free, collapse-free; produced by
   `LRS.PiPathInv.of_adequacy` (ADQ:267) from `LR.ContextualAdequacyAt 1`, and
   implied by the existing path package (ADQ:276).  Not reachable from a
   depth-bounded rung; see above for why.
2. `LR.CoherentIotaLeafStep Γ₀` (ADQ:6014, unproved): item 1 plus the
   multi-level frame layer, whose shape-threading specification is recorded
   above.
3. `LR.ConstDefnDeepStep Γ₀` (ADQ:6071, unproved): unchanged — route (a) only,
   as a producer-side retention of the value's certificate at seed creation.
4. `LR.CoherentFixedHeadStep Γ₀` (ADQ:4767, unchanged): N2 decided; land the
   `FixedHeadResultAt` premise change first, then the ordered producer over
   `peelLayer`.
5. Assembly: `CoherentRetainedNatStep.of_steps` (ADQ:4743) from
   `CoherentSelfStep.of_leafStepsDeep` (ADQ:6371) + item 4, then the bare leaf
   per rung and the depth bootstrap.

`LR.MajorChainFoldStep` (ADQ:985) and `LR.MajorChainAnchorStep` (ADQ:1040) are
both kept with all their producers, the former unused, as the reference
statements of what two successive repairs removed.

**Build note for the fixture slice:** this session changed `ShapeLogRel.lean`
and `ShapeLogRelAdequacy.lean` and rebuilt only
`Lean4Lean.Experimental.ShapeLogRel` and
`Lean4Lean.Experimental.ShapeLogRelAdequacy`.  The D0/D1/D2 fixture oleans
(`SExprParamsD0/D1/D2`) are stale by design and need the central rebuild
before they are trusted again.  The change is purely additive — no existing
structure gained a field, no existing theorem gained a premise, no existing
statement changed — so no fixture source edit is expected.

— session-C subagent 6

### Two probe-verified ports land; the N2 premise change is in the file (2026-08-15, session-C subagent 7)

Mechanical application of `plans/l4l-16c-port-queue.md` items 4 and 5(i)–(iii),
from the green probes `plans/probes/probeH-constdefn.lean` and
`plans/probes/probeF-telescope.lean`.  Three separate green builds of
`Lean4Lean.Experimental.ShapeLogRelAdequacy`, one per port, in the queue doc's
prescribed landing order.  Nothing outside `ShapeLogRelAdequacy.lean` was
touched: `ShapeLogRel.lean` and `SExpr.lean` are byte-identical.

#### Port 1 — retention + demand narrowing for the δ-definition budget (item 4)

`LR.ConstDefnLocalStep` (ADQ:6232), `LR.ConstDefnDeepStep` (ADQ:6261) and
`LR.ConstDefnLocalStep.of_deepStep` (ADQ:6277) are KEPT verbatim as reference
statements, the same treatment `MajorChainFoldStep` received.  Landed beside
them, verbatim from probeH modulo the `probeH.` → `LR.` rename:

- `LR.ConstDefnLocalStepR` (ADQ:6311) and `LR.ConstDefnDeepStepR` (ADQ:6329) —
  the retentive forms.  They keep the strictly smaller restart family `lower`
  and `Ctx.WF Γ₀`, both of which were in scope at the sole call site and were
  being erased on the way in.
- `LR.ConstDefnDeepStepR.toLocal` (ADQ:6349) — the depth-arithmetic reduction,
  threaded through the retained family.
- `LR.ConstDefnDeepStepR.of_constDefnDeepStep` (ADQ:6359) and
  `LR.ConstDefnLocalStepR.of_constDefnLocalStep` (ADQ:6366) — faithfulness:
  the new Props are weakenings, so whatever discharges the old ones discharges
  these.
- `LR.ConstDefnDeepInstStep` (ADQ:6378) — the demand narrowing.  The call site
  consumes exactly one instance of `LR.SelfAdequateAt`, pinned by
  `Params.Semantic.defn_whRed` to `B := SExpr.mkInst ls ci.type`,
  `core := true`; the certificate depth `nV` is now bound where the
  certificate is supplied rather than universally ahead of it.
- `LR.ConstDefnDeepInstStep.of_deepStepR` (ADQ:6405) — faithfulness for the
  narrowed form, hence (composing) from the current `ConstDefnDeepStep`.

Three consumers moved: `LR.SelfAdequateConstStep.of_steps` (ADQ:6426) now takes
`LR.ConstDefnDeepInstStep Γ₀`, and its defn-local branch (ADQ:6661) is
probeH's `callSiteInst` body — the `have hself : SelfAdequateAt … ` is replaced
by a directly ascribed `have adV : LR.Adequate …`, so no index-polymorphic
intermediate is manufactured; `LR.CoherentSelfStep.of_leafSteps` (ADQ:6678)
takes the same; `LR.CoherentSelfStep.of_leafStepsDeep` (ADQ:6690) now takes
`LR.ConstDefnDeepStepR Γ₀` and goes through
`LR.ConstDefnDeepInstStep.of_deepStepR`.

No discrepancy against the probe.  `CoherentSeedAt`, `RDeepChildren` and every
seed transport law are untouched, as probeH's §3 demanded.  **This narrows the
residual; it does not discharge it.**  What remains still needs the δ-rank
third well-founded component.

#### Port 2 — the N2 premise change and the four supplying call sites (item 5(i)+(ii))

**Naming, for the record:** the premise replaced is NOT `hcap` (the per-path
aligned-capture family, unchanged) but the third one — the context-free
typed-lower-head existential intro'd as `htyped`.  The premortem's own N2
section names it correctly as the `typedLowerHead` fallback; the tower summary
above does not.

(i) `LR.FixedHeadResult` (ADQ:2226) and `LR.FixedHeadResultAt` (ADQ:2274):
binder block `{head : TShape}` → `{head headTy : TShape}`, and

```
    LE_Interp.RHS.ShapeSpine … head rule.capturePaths out.T →
    (∃ headElem headTy : TShape, headElem ≤ head ∧ headElem.HasType headTy) →
```
became
```
    ∀ hshape : LE_Interp.RHS.ShapeSpine … head rule.capturePaths out.T,
    LR.FixedHeadTelescope (headTy := headTy) (outTy := outTy.T)
      Γ₀ mx my captureType hshape →
    LE_Interp.Witness ρ headTy (SExpr.mkInst recLs rule.df.type) →
```

`headTy` is universally quantified (an existential would need `Nonempty` over
a `Type`-valued `Witness` — exactly what N2 rejected); the spine premise is
NAMED so the telescope can be indexed by it, which costs nothing at consumers
because `FixedHeadTelescope` ignores its `spine` argument definitionally; the
terminal index is the caller's own `outTy.T`.

The eight Group-B adapters took the predicted two-token edit — insert `headTy`
after `head` in the `intro`, replace `htyped` by `htel hTyReg`:
`LR.FixedHeadResult.at` (ADQ:2317), `.of_forall_at` (ADQ:2328),
`LR.FixedHeadResultAt.mono` (ADQ:2338), `LR.FixedHeadResult.mono` (ADQ:2349),
`.bot` (ADQ:2360), `.bvar` (ADQ:2377), `.sort` (ADQ:2393),
`LR.FixedHeadResultAt.of_le` (ADQ:4759).  `.sort` was the one the probe had
NOT re-proved (verified by inspection only); it elaborated unchanged, so the
inspection was right.

A single-file `lake env lean` check after (i) alone produced EXACTLY four
errors, all "argument `htyped` has type `∃ headElem headTy, …` but is expected
to have type `LR.FixedHeadTelescope …`", at the four Group-C sites and nowhere
else.  That is the machine confirmation of the queue doc's "10 declarations,
zero new obligations" claim, and of the claim that the
`IotaRHSDefEq.of_nonbot` / `of_nonbotWitness` / `of_nonbotWitnessResult`
family (ADQ:2638 / 2701 / 2754) needs no edit at all: those keep the old
existential in their own callback contract, and the new evidence enters from
the enclosing theorem.  That is what bounds the ripple.

(ii) The producer interface landed as `LR.FixedHeadProducer` (ADQ:2574),
verbatim from probeF — continuation-passing, delivering the telescope and the
registered-type witness at ONE index at `outTy.T`.  The four Group-C sites each
gained a `producer` hypothesis and thread it through:

- `LRS.iotaDefEq_of_ctorExactAt_fixedHead` (ADQ:3221), producer at `ρ`;
- `LRS.iotaDefEq_of_ctorExactAt_closedFixedHead` (ADQ:3297), producer at
  `Valuation.nil`;
- `LRS.iotaDefEq_of_ctorExactAt_natStep` (ADQ:4997), inherits the nil-valuation
  producer and passes it straight down;
- `LRS.iotaDefEq_of_ctorExactAt_coherent` (ADQ:5056), producer at `ρ`.

Body shape at each: `refine producer rule mx my captureType hshape
(outTyP := outTy) ?_; intro headTy htel hTyReg; <old application with
htyped ↦ htel hTyReg>`.  At `_coherent` the single `refine` is placed before
`cases hseed`, so both the all-depth and the local branch share one
elimination.  The now-unused callback binder is renamed `_htyped` at all four
sites; no linter warning was added or removed anywhere in the file.

**Two deviations from the probe, both forced and both small.**

1. probeF states `FixedHeadProducer` at ONE instantiation (`leaf_call`).  A
   call site needs it quantified, so the landed hypothesis is
   `∀ (rule : Pattern.IotaRule r) {head} (mx my captureType) {outTyP}
   (hshape …), LR.FixedHeadProducer Γ₀ ρ rule mx my captureType hshape
   (recLs := recLs) (outTy := outTyP)`.  `recLs` and `outTy` MUST be passed by
   name: neither is determined by `hshape` — `recLs` occurs only under
   `SExpr.mkInst recLs rule.df.type` in the body, and `outTy` only in the
   telescope's terminal index.  `mx my captureType` are explicit for the same
   reason (they are explicit in `FixedHeadProducer` itself).
2. The predicted `_closedFixedHead` side condition arrived exactly as
   diagnosed: the consumer is pinned to `Valuation.nil`, `Witness.closedAt`
   needs `(mkInst recLs rule.df.type).ClosedN`, and `Pattern.IotaRule` carries
   `rhsClosed` but no `typeClosed`.  Resolved the cheap way — that site's
   producer is stated at `Valuation.nil` directly.  **No field was added to
   `Pattern.IotaRule`**; `SExpr.lean` is untouched and no fixture source needs
   an edit.  The cost is recorded, not paid: whoever discharges the
   nil-valuation producer will have to obtain the registered type's closedness
   from somewhere, and `rhsClosed` will not give it to them.

#### Port 3 — the ordered producer (item 5(iii))

Ported verbatim from probeF §2 under the queue doc's suggested names:

- `LR.FixedHeadOrderedLink` (ADQ:2467) — the per-layer input, in
  continuation-passing form so `argCap` and the argument witness stay
  proof-relevant.  The equation `headTy = (WShape.forallE tyDom tyFun).T` IS
  the capture-domain link.  `B = .forallE Bdom Bbody` is a layer datum, not
  derived (O3: `PathSpineWF` reaches the syntactic Pi form only through
  `conv`/`ret` edges carrying bare `IsDefEq`).
- `LR.FixedHeadTerminalLink` (ADQ:2492) — the terminal input, carrying O1 in
  its docstring.
- `LR.FixedHeadTelescope.consPeel` (ADQ:2503, probeF's `consPeel`) — the layer
  step, returning the telescope layer AND the peeled witness from one
  declaration so a caller cannot pair a layer with a witness peeled at another
  domain.  This is the file's first `noncomputable def`.
- `LR.FixedHeadTelescope.ofOrderedLink` (ADQ:2538, probeF's
  `telescope_ofOrderedLink`) — the ordered recursion, 12 lines.  The producer
  is the coincidence that `FixedHeadTelescope.cons` demands its tail at
  `(tyFun.app argCap).T` and `LE_Interp.Witness.forallE_inst` delivers the next
  registered-type witness at exactly that observation.

No bridge from `ofOrderedLink` to `FixedHeadProducer` was attempted, and none
should be: by O1, `WithCaptures.nil` forces `headTy = outTy` as an index
equality, so the telescope's terminal index is the codomain observation the
peel actually reaches, while the premise pins it to the caller's `outTy.T`.
A leaf-local `TerminalLink` is therefore stronger than any leaf can discharge;
the repair is producer-side, at the `constDefEq`/`Matches` materialization
boundary, where `hout`/`hA` must be produced BY the ordered peel rather than
supplied beside it.  O2 (no level-reconciliation constructor on
`WithCaptures`; the caller-side `ShapeSpine` head-lift is the clean repair, and
is a non-empty-spine lemma only) is likewise untouched.

#### State of the tower after this session

`LR.iotaWitnessStep` (ADQ:7434, `sorry` at ADQ:7464) remains the file's ONLY
`sorry`; the warning profile is byte-identical modulo line shifts.  Remaining
named obligations, in the order the assembly needs them:

1. `LRS.CtorSpineTypeUniqPath` — unchanged, environment-level, not reachable
   from a depth-bounded rung.
2. `LR.CoherentIotaLeafStep Γ₀` — unchanged.
3. The δ-definition residual — now `LR.ConstDefnDeepStepR` /
   `LR.ConstDefnDeepInstStep` rather than `LR.ConstDefnDeepStep`.  Both
   erasures are repaired; what is left is genuinely the δ-rank component.
4. `LR.CoherentFixedHeadStep Γ₀` (ADQ:4939) — step (iv), NOT attempted, per the
   queue doc's landing order.  It is now materially closer: its conclusion is
   `LR.FixedHeadResultAt Γ₀ hX depth`, whose changed premise hands it the
   telescope and the registered-type witness at one index, and it already
   receives `LR.SelfAdequateAt Γ₀ hX depth` at the same witness and depth — so
   the head-validity half is a direct application of
   `LR.SelfAdequateAt.of_fixedHeadTelescope` (ADQ:4165) with no global
   `AdequacyAtDepth`.  The application-fold half still routes through
   `LR.FixedHeadTelescope.toApplicationWithAdequacyAtDepth` (ADQ:2188), which
   takes `LR.AdequacyAtDepth Γ₀ depth` plus the `convert` callback and the two
   closedness facts.  That input, not the premise, is now the wall.
5. Assembly: `LR.CoherentRetainedNatStep.of_steps` (ADQ:4952) from
   `CoherentSelfStep.of_leafStepsDeep` (ADQ:6690) + item 4.

The four Group-C `producer` hypotheses are the new explicit obligations
introduced by this session.  They are leaf-local statements of a producer-side
fact (O1), so the next design pass on them should start at the
materialization boundary, not at the leaf.

**Build note for the fixture slice:** this session changed only
`ShapeLogRelAdequacy.lean` and rebuilt only
`Lean4Lean.Experimental.ShapeLogRelAdequacy`.  The D0/D1/D2 fixture oleans
(`SExprParamsD0/D1/D2`) are stale by design and need the central rebuild before
they are trusted again.  Unlike the previous session's change this one is NOT
purely additive — `FixedHeadResult`/`FixedHeadResultAt` changed a premise and
four `iotaDefEq_of_ctorExactAt_*` theorems gained a hypothesis — but every
affected declaration lives in `ShapeLogRelAdequacy.lean` and every in-file
consumer was updated, so no fixture source edit is expected either.

— session-C subagent 7

### `CoherentFixedHeadStep` lands; the application fold's adequacy demand is at `depth - 1`, not at the rung (2026-08-15, session-C subagent 8)

Item 4 of the tower is proved.  `LR.CoherentFixedHeadStep.of_steps`
(ADQ:5227) is green, conditional on two named Props and on nothing else — in
particular on no global `LR.AdequacyAtDepth` at the rung, which is what the
previous session recorded as "the wall".  Final state of
`ShapeLogRelAdequacy.lean`: **zero errors**, the same sole `sorry` at
`LR.iotaWitnessStep` (now ADQ:7718:8, token ADQ:7748), and 87 → 90 warnings,
the three new ones being the `unusedSectionVars` linter firing on the three
new declarations that do not use `[Params.Semantic]`.  Every other warning is
byte-identical modulo line shifts (`diff` of the sorted, line-stripped sets is
empty apart from those three additions).  `ShapeLogRel.lean` and `SExpr.lean`
were not touched.

#### THE DEPTH ANSWER (the paragraph that matters)

**The application fold does not need same-rung adequacy.  Its demand splits
into one call the step already holds and one call at `depth - 1`.**

`LR.FixedHeadTelescope.toApplicationWithAdequacyAtDepth` (now ADQ:2281)
takes `LR.AdequacyAtDepth Γ₀ depth` at literally the same `depth` as
its `hstrat : HasTypeStratifiedS Δ X headType core depth`, and
`LR.FixedHeadResultAt Γ₀ hX depth` supplies `hstrat` at exactly the rung's
depth — so read off the signatures, the answer is "same rung, G4 fires".  That
reading is wrong, and the reason is visible only one level down, inside
`LR.AdequacyAtDepth.closedHeadSelf` (ADQ:2098), which is where the single
`adequacy` hypothesis is actually spent.  It is spent **twice, at two
different subjects and two different depths**:

1. `adequacy hstrong hstrat hX.toInterp hTy.toInterp htyped` — subject `X`,
   displayed type `headType`, certificate at `depth`.  This instance is
   *pointwise identical* to an instance of `LR.SelfAdequateAt Γ₀ hX depth`:
   both conclude `LR.Adequate Γ₀ Δ ρ X X headType headElem headElemTy`, and
   `SelfAdequateAt`'s only extra premise is `headElem.T ≤ root`, which the
   `headSelf` callback supplies as `headElem.T ≤ head` composed with the
   fold's own `hhead : head ≤ root`.  `LR.CoherentRetainedNatStep.of_steps`
   (ADQ:5199) hands `CoherentFixedHeadStep` exactly that package at exactly
   that witness and depth.  **Cost: zero.**
2. `adequacy hTypeStrong (hTypeStrat.mono (Nat.sub_le depth 1)) …` — subject
   `headType`, displayed type `.sort u`.  `HasTypeStratifiedS.isType`
   (SExpr:2716) returns `∃ u, Γ ⊢ A : .sort u !! n - 1`, so this certificate
   lives at `depth - 1`; the `mono` exists **only** so that one hypothesis can
   serve both calls.  Drop the `mono` and the honest demand is
   `LR.AdequacyAtDepth Γ₀ (depth - 1)`.

So the arithmetic is: rung `depth`, term call at `depth`, type call at
`depth - 1`.  `depth - 1 < depth` iff `0 < depth`; at `depth = 0` truncated
subtraction collapses the two, which is why
`LR.FixedHeadTypeValidStep.of_lowerAdequacy` (ADQ:2200) carries an explicit
`0 < depth` and `of_predecessorAdequacy` (ADQ:2169) does not.  The depth-zero
rung is the only place the demand stops being a predecessor demand.

Two consequences must be stated together, or the result will be over-read.

*The G4 tripwire does not fire on the step.*  Nothing is manufactured inside
the induction: the term half arrives through the step interface, and the type
half is an interface hypothesis of `of_steps`.  Neither `children` nor the
strict predecessor family `lower` is consumed at all — the fixed-head half
turns out to need **no recursion whatsoever** once the N2 premise change hands
it the telescope.  That is the strongest evidence yet that the N2 decision was
the right one.

*But the predecessor family that would discharge the type half is not the one
the step carries.*  `CoherentFixedHeadStep`'s `lower` is a family of
`LR.CoherentRetainedAt Γ₀ hX' d'`, not of `LR.AdequacyAtDepth Γ₀ d'`; and its
`depth` is the **inner** Nat index of the coherent witness recursion,
universally quantified, with no relation to the **outer** adequacy rung `d` of
`LR.IotaWitnessStepAtDepth` (ADQ:1880) whose family
`contextualAdequacyAtDepth_of_iotaSteps` (ADQ:7681) forwards.  Worse,
the inner `depth` here is the stratification depth of a *registered
declaration's own typing* (`Pattern.IotaRule.rhsStrong`, SExpr:2242) — an
environment-level quantity, exactly like `LRS.CtorSpineTypeUniqPath` — so it
is not bounded by the outer rung and `∀ depth, FixedHeadTypeValidStep Γ₀
depth` is not reachable from `∀ d' < d, ContextualAdequacyAtDepth d'`.  That
is why the obligation is landed as a named Prop quantified over all inner
depths, in the same idiom `LR.CoherentSelfStep.of_leafSteps` already uses for
`defeqStep : ∀ depth, LR.SelfAdequateDefeqStepAt Γ₀ depth`, rather than
discharged.  The honest summary: **the wall moved from "adequacy at the rung"
to "type-level adequacy at the predecessor of an environment-fixed depth",
which is strictly smaller, structurally the same shape as the self-adequacy
half's existing obligation, and no longer blocks item 4.**

#### What landed

Producers and named obligations, in file order:

- `LR.AdequacyAtDepth.of_le` (ADQ:2132) — contravariance in the depth index;
  larger index = strictly stronger package.
- `LR.FixedHeadTypeValidStep Γ₀ depth` (ADQ:2155, NEW OBLIGATION) — the
  isolated type rung of `closedHeadSelf`.  Discharged by
  `of_predecessorAdequacy` (ADQ:2169) from `LR.AdequacyAtDepth Γ₀ (depth - 1)`
  with **no `mono` anywhere**; by `of_adequacyAtDepth` (ADQ:2190) from the old
  same-rung package (faithfulness); and by `of_lowerAdequacy` (ADQ:2200) from
  `∀ d < depth, ContextualAdequacyAtDepth d` given `0 < depth`.
- `LR.FixedHeadConvertStep Γ₀` (ADQ:2215, NEW OBLIGATION, pre-existing in
  substance) — the conversion transport
  `IsDefEq Γ₀ A B (.sort u) → TyDefEq A A a → TyDefEq A B a`.  This was always
  a hypothesis of `LR.FixedHeadTelescope.toApplicationWith`; it is only now
  named.  It is **not** an instance of
  `LR.TyDefEq.of_defeq_of_stratifiedInversion` (ADQ:1168): that lemma also
  demands `TyDefEq B B a`, and the chain zip has no producer for it.  Its
  shape is fixed by `LR.FixedHeadShapeChain.pathSemantics` (SLR:14322), which
  is outside this session's territory.
- `Pattern.IotaRule.typeClosed` (ADQ:2693) — **the recorded
  `_closedFixedHead` side condition is discharged.**  `Pattern.IotaRule` still
  has no `typeClosed` field and needs none: `VEnv.Ordered.closed`
  (Theory/Typing/Lemmas.lean:412) closes all three components of every
  registered `VDefEq`, so `(Params.henv.closed.2 rule.registered).2.2.mkInstS`
  is the whole proof.  No `SExpr.lean` edit, no fixture source edit.
- `LR.FixedHeadTerminalRetarget` (ADQ:2721, NEW OBLIGATION) and
  `LR.FixedHeadProducer.of_orderedLink` (ADQ:2741) — see the O1 section below.
- `LR.SelfAdequateAt.closedHeadSelf` (ADQ:4370) — the depth-refined
  `headSelf` callback: `SelfAdequateAt` at the same witness and depth for the
  term half, `FixedHeadTypeValidStep` for the type half, both closedness facts
  free.  Endpoints are the literal ones the packed telescope selected; nothing
  is re-existentialized (contrast `SelfAdequateAt.of_fixedHeadTelescope`
  (ADQ:4341), which republishes an existential and is therefore *not*
  what the fold should call).
- `LR.FixedHeadTelescope.toApplicationWithSelfAdequacy` (ADQ:4400) — drop-in
  strengthening of `toApplicationWithAdequacyAtDepth`: same conclusion, same
  `convert`/`raw`/`resultRel`/closedness inputs, but `AdequacyAtDepth Γ₀
  depth` replaced by the two weaker inputs above.  The original is kept
  unused as the reference statement, the same treatment `MajorChainFoldStep`
  and `ConstDefnLocalStep` received.
- `LR.CoherentFixedHeadStep.of_steps` (ADQ:5227) — **item 4**.  Twelve lines.
  `by_cases` on `out.T ≤ TShape.bot` (bottom branch is `FixedHeadResult.bot`'s
  ending verbatim), then `FixedHeadApplication.applyRule` on
  `toApplicationWithSelfAdequacy`.  `hX` must be passed by name at both calls:
  `LR.FixedHeadApplication`'s `depth` and `hX` are phantom indices — neither
  occurs in its body — so unification cannot recover them.

Three premises of `FixedHeadResultAt` are **not used** by the proof and were
renamed with a leading underscore: `hstrong` (subsumed by `hstrat`), `hspineY`
(the fold zips one raw spine), and — the interesting one — `hcap`, the
existential per-path capture family.  The telescope already carries every
capture at its own shapes, so the shape-existential form is now dead weight at
this consumer.  That is the N2 retention paying out exactly as designed.

#### O1 re-diagnosed: the prescribed repair is not available below `LR.Adequate`

The port queue's O1 says the fix is producer-side, "at the `constDefEq`/
`Matches` materialization boundary, where `hout`/`hA` must be produced BY the
ordered peel rather than supplied beside it".  **That repair does not exist
there**, and the reason is a one-line signature fact worth recording so nobody
spends a session looking for it: `hout`/`hA` are *inputs* of `LR.constDefEq`
(ADQ:3638).  The fold recomputes them only when it crosses an application
layer; in its `pat` branch it passes them to the pattern leaf unchanged, and
`LR.PatternLeafDefEq.of_iota`, `LR.IotaLeafDefEq` and `LRS.IotaRHSDefEq`
thread them verbatim to `LRS.iotaDefEq_of_ctorExactAt_*`.  So `outTy` is fixed
by the caller of the constant-evaluation fold — ultimately by the shape
argument of `LR.Adequate` — before any pattern is matched.  Nothing at or
below the matched leaf can produce it.

Two further checks, both negative, both recorded so they are not re-derived:

* `Shape.HasType` is **not** functional, so `out` does not determine `outTy`:
  `Shape.HasTypeU.bot` (SLR:2548) types `.bot` at every `x` with
  `HasType x .type`, and `.lam`/`.forallE` do not pin their type index either.
  O1 cannot be dissolved by uniqueness of the observation.
* Building the telescope bottom-up instead of peeling top-down does not help.
  `WithCaptures.cons` (SLR:3661) demands its tail at `(tyFun.app argCap).T`
  and threads `outTy` unchanged, so the same equation reappears at the base:
  the fully-peeled registered-type observation must *equal* the caller's
  `outTy`.  There is no `≤` anywhere on that index.

What this leaves is one equation, and it is now named:
`LR.FixedHeadTerminalRetarget Γ₀ mx my captureType spine outTy` (ADQ:2721)
reads a finished telescope at the caller's result observation instead of the
peel's.  With it, `LR.FixedHeadProducer.of_orderedLink` (ADQ:2741) discharges
the whole `FixedHeadProducer` interface from four inputs: the registered
type's own observation `hTyReg`, `FixedHeadOrderedLink`,
`FixedHeadTerminalLink`, and the retarget.  So the four leaf-local `producer`
hypotheses introduced by the previous session are no longer opaque: they are
one reusable producer plus three named per-shape Props.  The retarget's
natural producer is a *uniqueness* statement rather than a construction — the
peel's terminal witness observes the syntactic spine result `A` (the right
endpoint of `SExpr.PathSpineWF`), and the caller's
`hA : (LR Γ₀).TyDefEq A A outTy` observes that same `A` at `outTy`.  A
terminal-index monotonicity for `WithCaptures` would also do it, but that is a
`ShapeLogRel.lean` change and was therefore not attempted.

#### Remaining tower (updated)

1. `LRS.CtorSpineTypeUniqPath` — unchanged; environment-level, not reachable
   from a depth-bounded rung.
2. `LR.CoherentIotaLeafStep Γ₀` — unchanged; item 1 plus the multi-level frame
   layer whose shape-threading specification is in subagent 6's entry.
3. The δ-definition residual (`LR.ConstDefnDeepStepR` /
   `LR.ConstDefnDeepInstStep`) — unchanged; genuinely the δ-rank component.
4. **`LR.CoherentFixedHeadStep Γ₀` — DONE** (ADQ:5227), conditional on
   `LR.FixedHeadConvertStep Γ₀` and `∀ depth, LR.FixedHeadTypeValidStep Γ₀
   depth`.
5. `LR.FixedHeadConvertStep Γ₀` (NEW, ADQ:2215) — one-sided conversion
   transport for `TyDefEq`; needs the right endpoint's validity, which the
   chain zip does not carry.  Not new work created by this session: it has
   been a hypothesis of `toApplicationWith` since that lemma existed.
6. `∀ depth, LR.FixedHeadTypeValidStep Γ₀ depth` (NEW, ADQ:2155) —
   type-level adequacy at `depth - 1`; same interface idiom as
   `∀ depth, LR.SelfAdequateDefeqStepAt Γ₀ depth`, which
   `CoherentSelfStep.of_leafSteps` already takes, so these two should be
   discharged together by whatever eventually supplies the depth family.
7. `LR.FixedHeadTerminalRetarget` (NEW, ADQ:2721) — the isolated O1 equation;
   with `FixedHeadOrderedLink` and `FixedHeadTerminalLink` it discharges all
   four `producer` hypotheses via `FixedHeadProducer.of_orderedLink`.
8. Assembly: `LR.CoherentRetainedNatStep.of_steps` (ADQ:5199) now needs only
   `CoherentSelfStep.of_leafStepsDeep` plus item 4 — i.e. the fixed-head half
   is no longer what blocks it.

**Build note for the fixture slice:** this session changed only
`ShapeLogRelAdequacy.lean` and rebuilt only
`Lean4Lean.Experimental.ShapeLogRelAdequacy` (`lake build`, exit 0, "Build
completed successfully (34 jobs)").  The change is **purely additive** — no
existing declaration changed its statement, gained a premise, or was removed;
`toApplicationWithAdequacyAtDepth` and `AdequacyAtDepth.closedHeadSelf` are
kept verbatim as reference statements.  The D0/D1/D2 fixture oleans
(`SExprParamsD0/D1/D2`) remain stale by design from the previous two sessions
and still need the central rebuild; no fixture source edit is expected from
this session either.

— session-C subagent 8

### The `∀ depth` type rung is discharged from `lower`; O1 is refuted (2026-08-15, session-C subagent 9)

`ShapeLogRelAdequacy.lean`: **zero errors**, `Build completed successfully
(34 jobs)`, the same sole `sorry` at `LR.iotaWitnessStep` (now ADQ:7936:8,
token ADQ:7968), and the warning set is **byte-identical to the baseline** —
90 before, 90 after, `comm` empty in both directions after stripping line
numbers.  Not "changed only by `unusedSectionVars`": *unchanged*.  The eight
new declarations all forward `[Params.Semantic]` into an existing lemma that
carries it, so the linter does not fire on any of them.  `ShapeLogRel.lean`
and `SExpr.lean` were not touched.

#### THE DEPTH AUDIT (lead with this; it decided the session)

**At which depths is `∀ depth, LR.FixedHeadTypeValidStep Γ₀ depth`
instantiated on the leaf path, and are those depths bounded by the rung?**

*Instantiated at every `depth : Nat`.  Not bounded by the rung.  Neither
branch of the audit's dichotomy applies, because the dichotomy's premise —
that the only producer is adequacy at `depth - 1` — is false.*

The two indices, kept apart:

* the **outer rung** `d` of `LR.IotaWitnessStepAtDepth Γ₀ d` (ADQ:1880),
  which forwards `∀ d' < d, ContextualAdequacyAtDepth d'`.  Note that its
  product `LR.IotaWitnessStep` (ADQ:1860) is itself **depth-free**;
* the **inner Nat index** `depth` of the coherent witness recursion.
  `LR.CoherentRetainedResult` (ADQ:4500) is *literally* `∀ depth,
  CoherentRetainedAt Γ₀ hX depth`, so `recRDeepNatProvenance` fires the step
  at every Nat.  `LR.CoherentFixedHeadStep` therefore quantifies `depth`
  universally and `of_steps` consumed `typeValid depth` at that same index.

Not bounded, for two independent reasons, both now confirmed against the
source rather than inferred:

1. The bootstrap withholds the bound *by design*.
   `contextualAdequacyAtDepth_of_iotaSteps`'s docstring (ADQ:7676-7680):
   "the derivation induction is depth-blind, so a root certificate cannot
   bound the leaf instances reached through `trans` or evaluator descent.
   Whatever depth bound a leaf producer needs must come from its own
   registered-rule certificates."
2. The registered-rule certificates do **not** supply it here, and this is
   where the `rootRed` pattern fails to transfer.  The candidate was
   `Pattern.IotaRule.FocusedActionPreimage` (SLR:9278-9290), whose
   `rhsStratified` sits at `rhsDepth` and whose `headStratified` sits at
   `rhsDepth - rule.capturePaths.length` — a genuine bound, but on a
   *different* certificate than the one the fixed-head consumer reads.  The
   two live instantiations are `LRS.iotaDefEq_of_ctorExactAt_coherent`
   (ADQ:5416), which takes its depth from
   `obtain ⟨rhsDepth, hstrat, _⟩ := hstrong.stratify` on `rule.rhsStrong` —
   an unbounded existential on an environment-level derivation — and
   ADQ:5420, which takes the ambient `CoherentRhsSeedAt` depth.  Neither
   reads `headStratified`.

**So both audit branches fail, and it is still not a G4 tripwire.**  The
third producer is inside the step's own interface:

> `∀ depth` never needed to be bounded.  The obligation at each `depth` is
> dischargeable from `lower` — `LR.CoherentFixedHeadStep`'s own strict
> predecessor family — at that same `depth`.

The arithmetic, spelled out:

| piece | index | source |
|---|---|---|
| term half | `depth` | `hself : SelfAdequateAt Γ₀ hX depth`, an interface input (subagent 8) |
| type half | `depth - 1` | `HasTypeStratifiedS.isType` (SExpr:2716) |
| decrease | `depth - 1 < depth ⟺ 0 < depth` | `Nat.sub_lt` |
| `0 < depth` | — | `LR.CoherentRetainedAt.restart lower (Nat.sub_lt hdepth Nat.one_pos)` at `hTypeInterp.witness` |
| `depth = 0` | — | no adequacy at all; see below |

Two facts make the restart legal here, and both are specific to this
obligation:

* **The witness is unrelated to `hX`.**  The type half needs self-adequacy at
  the *registered type's own* interpretation witness, which is not a child of
  the fixed head's witness — `children` could never have supplied it.
  `LR.CoherentRetainedAt.restart` (ADQ:5030) admits an arbitrary witness
  precisely because it rebuilds the evaluator tree itself via
  `LR.CoherentSeedAt.rebuild`.  This is the same move
  `LR.selfAdequateExactAtStep` already makes at ADQ:6299-6304 (`restartSelf`).
* **The conclusion is homogeneous.**  `CoherentRetainedAt` carries
  `SelfAdequateAt Γ₀ hX' d'`, i.e. `Adequate Γ₀ Δ ρ X X B mx bx` with *one*
  subject; `FixedHeadTypeValidStep`'s conclusion is
  `TyDefEq headType headType headElemTy`, also homogeneous, so it fits
  exactly.

`depth = 0` is free, not residual.  Every `HasTypeStratifiedS` constructor
except `sort'` and `base` carries the index `n + 1` (SExpr:2380-2409), so a
depth-`0` certificate forces `X = .sort l` and `headType = .sort l.succ`;
the conclusion is then the `sort_iff` / `bot` split already used by the
`sort'` case of `selfAdequateExactAtStep`.  Machine-checked as
`LR.FixedHeadTypeValidStep.zero`.

#### The previous session's "discharge both together" recommendation is REFUTED

`∀ depth, LR.SelfAdequateDefeqStepAt Γ₀ depth` has the same `∀ depth` shape
but **cannot** take this route, and the reason is one word: heterogeneity.
`SelfAdequateDefeqStepAt.of_lowerAdequacy` (ADQ:6231-6241) feeds
`LR.adequateDefeq`'s first callback, whose type (ADQ:4343-4355, `ihTy`) is
`Adequate Γ₀ Γ ρ A B (.sort u) ma sa` — **two different endpoints**, carrying
the `A ≡ B` link.  `SelfAdequateAt` produces only `X X`, so the coherent
predecessor family is strictly too weak.  Whatever eventually supplies that
family must either be genuinely heterogeneous adequacy at unbounded inner
depths, or `LR.CoherentRetainedAt` must be widened to carry a heterogeneous
rung — and the second is not free, since `selfAdequateExactAtStep` inducts on
the stratified typing of the *witness's own* subject and has no second
subject to offer.

#### What landed

- `LR.FixedHeadTypeValidStep.of_lowerCoherent` (ADQ:4987) — the discharge at
  `0 < depth`, from `lower` alone.  No `LR.AdequacyAtDepth` at any rung.
- `LR.FixedHeadTypeValidStep.zero` (ADQ:5021) — the depth-zero rung.
- `LR.FixedHeadTypeValidStep.of_coherentLower` (ADQ:5054) — the two combined;
  this is what removes the obligation.
- `LR.CoherentFixedHeadStep.of_convertStep` (ADQ:5445) — **item 4 with the
  type family gone**.  Identical to `of_steps` (ADQ:5412, kept unchanged as
  the reference statement) except that `typeValid` is no longer a hypothesis:
  the instance is built from `lower`, which `of_steps` left unused.  Its only
  remaining input is `LR.FixedHeadConvertStep Γ₀`.
- `LR.FixedHeadConvertRightValid` (ADQ:2240) + `LR.FixedHeadConvertStep.of_rightValid`
  (ADQ:2249) — target 2 narrowed.  The recorded dead end
  (`LR.TyDefEq.of_defeq_of_stratifiedInversion` "also demands
  `TyDefEq B B a`") is turned into a producer by *naming* that demand.  The
  residual is then readable by unfolding: at `a = .sort r`, `sort_iff_ty`
  makes it "`B` has a weak-head normal form and it is a sort"; at
  `a = .forallE b f` the same with Pi.  That is `PiHeadNorm` =
  `TypeWHNFEx` + `PiHeadStable`, the single irreducible factor probeP
  isolated inside `PiPathInv`.  Nothing weaker is available at the consumer:
  `SExpr.PathSpineWF`'s `conv`/`ret` edges (SExpr:1650-1658) carry a bare
  `IsDefEq` and no shape, witness, or endpoint validity — G5 in its exact
  position.  (Also checked and rejected: `SExpr.IsDefEq.strong`
  (SExpr:3013) is a real proved bridge, but it only upgrades the raw edge;
  it produces no interpretation of `B` at `a`, so it does not help.)
- `LR.FixedHeadTerminalRetarget.hasType_functional` (ADQ:2777) and
  `LR.FixedHeadTerminalRetarget.not_general` (ADQ:2804) — see below.

Probes (untracked, both green, exit 0, no `sorryAx`):
`plans/probes/probeT-typevalid.lean` (3 results, axioms
`propext, Classical.choice, Quot.sound` only) and
`plans/probes/probeU-convert-retarget.lean` (3 results).

#### O1 RESOLVED IN THE NEGATIVE: `LR.FixedHeadTerminalRetarget` is FALSE

Not "hard", not "needs a producer" — **refutable**, and now machine-checked.

`WithCaptures.nil` (SLR:3661) identifies the telescope's two type indices, so
at a nil-terminated spine the retarget says exactly: every type of `head`
equals the caller's `outTy`.  `LR.FixedHeadTerminalRetarget.hasType_functional`
proves that implication; `TShape.HasType.bot` (SLR:3135) types `.bot` at every
sort, so `not_general` derives `False` from the Prop at
`head := TShape.bot`.  `WithCaptures.cons` threads `outTy` unchanged, so on a
longer spine the same demand simply reappears at the base — the refutation is
not an artefact of the empty spine, it is the base case of every spine.

Consequences, so the next session does not re-plan around a false statement:

* the previous session's suggested producer — "a *uniqueness* statement rather
  than a construction", using the caller's `hA : TyDefEq A A outTy` — is
  refuted along with the Prop.  There is nothing to produce.
* `LR.FixedHeadProducer.of_orderedLink` (ADQ:2874) is therefore conditional on
  a false hypothesis.  It is left in place (it is not *wrong*, just vacuous),
  but it must not be counted as progress toward the four leaf `producer`
  hypotheses.
* the repair cannot be leaf-side or producer-side at all.  Two routes remain,
  both requiring `ShapeLogRel.lean`, i.e. outside this session's territory:
  (i) give `TypedTelescope.WithCaptures` a terminal-index monotonicity — the
  same absence O2 records for its level index; or (ii) let
  `LR.FixedHeadShapeChain.pathSemantics` (SLR:14322) consume a chain at the
  observation the peel actually reached plus a semantic bridge to `outTy`, so
  the caller's `hout`/`hA` are used where they are in fact available.  Route
  (ii) is the one consistent with subagent 8's signature finding that
  `hout`/`hA` are *inputs* of `LR.constDefEq`.

#### Remaining tower (updated)

1. `LRS.CtorSpineTypeUniqPath` — unchanged; environment-level.
2. `LR.CoherentIotaLeafStep Γ₀` — unchanged.
3. δ-definition residual (`LR.ConstDefnDeepStepR` / `LR.ConstDefnDeepInstStep`)
   — unchanged; the δ-rank component (probeK).
4. `LR.CoherentFixedHeadStep Γ₀` — **DONE, and now conditional on
   `LR.FixedHeadConvertStep Γ₀` ALONE** (ADQ:5445).
5. `LR.FixedHeadConvertStep Γ₀` — narrowed to `JointStratifiedInversion` +
   `LR.FixedHeadConvertRightValid`; the residual is `PiHeadNorm`.  **Blocked
   on the same irreducible factor as `PiPathInv`.**
6. ~~`∀ depth, LR.FixedHeadTypeValidStep Γ₀ depth`~~ — **REMOVED, discharged.**
7. ~~`LR.FixedHeadTerminalRetarget`~~ — **REMOVED, refuted.**  Replaced by a
   `ShapeLogRel.lean`-side repair request (routes (i)/(ii) above).
8. `∀ depth, LR.SelfAdequateDefeqStepAt Γ₀ depth` — unchanged, and now known
   *not* to be dischargeable alongside item 6.  Blocked on `PiPathInv` via
   `of_stratifiedInversion`, or on the inner/outer depth mismatch via
   `of_lowerAdequacy`.
9. Assembly: `LR.CoherentRetainedNatStep.of_steps` (ADQ:5384) now needs only
   `CoherentSelfStep.of_leafStepsDeep` plus item 4.

**Build note for the fixture slice:** only `ShapeLogRelAdequacy.lean` changed,
and only `Lean4Lean.Experimental.ShapeLogRelAdequacy` was built.  The change is
purely additive — no existing declaration changed its statement, gained or lost
a premise, or was removed; `of_steps`, `toApplicationWithAdequacyAtDepth`,
`AdequacyAtDepth.closedHeadSelf`, `of_predecessorAdequacy`, `of_lowerAdequacy`
and `FixedHeadTerminalRetarget` itself are all kept verbatim.  The D0/D1/D2
fixture oleans (`SExprParamsD0/D1/D2`) remain stale by design from the previous
three sessions and still need the central rebuild; no fixture source edit is
expected from this session either.

— session-C subagent 9

### O1 repaired by terminal-index monotonicity; a SECOND vacuity found and machine-checked (2026-08-15, session-C subagent 10)

`ShapeLogRel.lean`: **zero errors, zero sorries**, warning set **byte-identical**
to baseline (23 → 23, `diff` empty).  `ShapeLogRelAdequacy.lean`: **zero
errors**, the same sole `sorry` at `LR.iotaWitnessStep` (ADQ:8348, token
ADQ:8378), 90 → 100 warnings — nine new `unusedSectionVars` on nine new
theorems, plus one new `unusedVariables` on `spine`, which is the exact mirror
of the pre-existing warning on `LR.FixedHeadTelescope` (ADQ:1904) and has the
same cause: the `spine` argument is ignored definitionally, by design.  No
warning disappeared.  `SExpr.lean` untouched.  No new `sorryAx`: every new
declaration checks with `propext, Classical.choice, Quot.sound` only (the two
`SpineWF` ports need only `propext, Quot.sound`).

#### LEAD WITH THIS: `LR.FixedHeadTerminalLink` IS ALSO FALSE

`LR.FixedHeadProducer.of_orderedLink` was vacuous for **two** independent
reasons, not one.  Beside the refuted retarget, its `term` input

```
LR.FixedHeadTerminalLink ρ out := ∀ headTy B, Witness ρ headTy B → out.HasType headTy
```

is refutable at every non-bottom `out`.  `LE_Interp.Witness.bot` (SLR:3928) is
`Witness ρ (WShape.T .bot) M` for **arbitrary** `ρ`, `M`, `n`, so instantiating
at `TShape.bot` gives `out.HasType TShape.bot`, and `TShape.HasType.bot_r`
(SLR:3120) turns that into `out ≤ TShape.bot`.  Every consumer of the
fixed-head fold carries `houtNonbot : ¬out.T ≤ TShape.bot` — the bottom result
shape is split off before the telescope is ever read — so the Prop is false
exactly where it would be used.  Machine-checked as
`LR.FixedHeadTerminalLink.le_bot` (ADQ:2844) and `.not_nonbot` (ADQ:2855).

**The pattern behind both refutations, stated so it is not repeated.**  The
observation lattice has a bottom that *every* syntax is witnessed at and that
*every* type of type-kind types.  Therefore **no terminal fact about the peel
may be stated as a law quantified over observations.**  `TerminalRetarget`
quantified over the reached index; `TerminalLink` quantified over the
witnessed index; both die to the same instance.  A terminal fact must be a
*datum at the observation actually reached*, i.e. existential /
continuation-passing in that index.  That single criterion is what selected
the route below, and it is the cheap vacuity test to run on the next such
Prop: instantiate at `TShape.bot` and see whether the statement survives.

#### ROUTE DECISION: (R-A), and (R-B) is not available

**(R-B) is refuted by a signature fact.**  `LR.FixedHeadShapeChain`'s terminal
index is not free to be the reached observation: it is a `WShape outLevel` that
flows *verbatim* into `LR.FixedHeadApplication` (ADQ:2075) and thence into the
conclusion of `LR.FixedHeadResult`, `(LR Γ₀).DefEq … A out outTy`.  Moreover
`pathSemantics`'s `resultRel : TyDefEq resultType resultType outTy` **is** the
caller's `hA`, already consumed at the caller's own `outTy`.  So the chain
must end at `outTy`, the semantic bridge is already there, and there is nothing
for a second bridge to do.  Recorded as a dead end in
`FixedHeadTerminalRetarget.not_general`'s docstring.

**(R-A) landed, additive, as a parallel structure.**  The audit that decided
it: the telescope's terminal index is read in exactly **two** places downstream,
and both are monotone.

| read | who | direction |
|---|---|---|
| `out.HasType outTy` | `WithCaptures.outHasType`, the fold's `nil` case | the caller already holds this (`hout`) |
| `headElemTy.T ≤ headTy` | the fold's return, spent by `hTy.mono` in `withWitnessAndChain` | head index is an **upper bound** only |

Nothing anywhere uses the head index as a lower bound or as an exact value.
Hence weakening the base from an index *equality* to `outTy ≤ headTy` is sound
for every consumer, and it is the unique place the equality was doing work:
`cons` is verbatim in the new structure, so every layer is the same layer.

#### The new named Prop, and its vacuity check

`LR.FixedHeadTerminalDominance Γ₀ mx my captureType spine headTy outTy`
(ADQ:3160) — continuation-passing: *some* run of the ordered peel terminates at
a `reachedTy` with `outTy ≤ reachedTy`, delivering the telescope there.

* **Not refutable by the bot argument**, because the reached observation is
  chosen by the producer rather than quantified over.  (Contrast: both refuted
  Props are ∀-over-observations.)
* **Strictly weaker than what it replaces** — `.of_exact` (ADQ:3174) builds it
  from the old exact demand at `TShape.LE.rfl`, so nothing that used to
  discharge the producer stops discharging it.
* **Inhabited, at the very instance where the retarget is FALSE** — `.nil`
  (ADQ:3189) builds it at the empty capture spine from `head.HasType outTy`
  alone, including at `head = .bot`, which is exactly where
  `FixedHeadTerminalRetarget.not_general` derives `False`.

#### What landed

`ShapeLogRel.lean` (all additive; every pre-existing statement byte-identical):

- `…TypedTelescope.WithCapturesLE` (SLR:3871) — the packed telescope with a
  monotone terminal index.  Only `nil` differs: `(htyped : head.HasType outTy)`
  `(hle : outTy ≤ headTy)` in place of the two-index identification.
- `WithCaptures.toLE` (SLR:3892) — faithfulness.
- `WithCaptures.retarget` (SLR:3914) — **THE TERMINAL-INDEX MONOTONICITY.**
  Rebuilds an exact telescope at any lower result observation the caller can
  type.  This is the lemma `WithCaptures` cannot have on its own.
- `WithCapturesLE.spine` / `.outHasType` / `.lowerHead` (SLR:3929/3942/3956) —
  the eliminations, proved directly rather than through `TypedTelescope`, so
  `TypedTelescope` and `Captures` are untouched.
- `WithCapturesLE.fixedHeadShapeChain` (SLR:13904) — the fold, differing from
  the old proof **only in its `nil` case**;
  `TypedTelescope.fixedHeadShapeChain` (SLR:14110) is kept with its statement
  byte-identical and is now a one-line corollary via `toLE`, so its sole
  consumer is unaffected.
- Secondary ports from `plans/probes/probeS-spinedepth.lean`:
  `SpineWF.ret_path` (SLR:11360, the missing `ret` dual of `conv_path`) and
  `HasTypeStratifiedS.spineWF_of_foldl_bound` (SLR:11416), which sharpens the
  walk to `m + es.length ≤ n`; the old `spineWF_of_foldl` (SLR:11437) keeps its
  statement and is now a corollary, so its two consumers are unaffected.

`ShapeLogRelAdequacy.lean`:

- `LR.FixedHeadTelescopeLE` (ADQ:2085) + `.toLE` (ADQ:2108) + **`.retarget`**
  (ADQ:2122) + `.nil` / `.cons` / `.outHasType` / `.lowerHead` / `.withWitness`
  / `.withWitnessAndChain` (ADQ:2136-2213) + `.toApplicationWith` (ADQ:2480) +
  `.toApplicationWithSelfAdequacy` (ADQ:4896).
- **Premise swap, three sites, one token each**: `FixedHeadResult` (ADQ:2590),
  `FixedHeadResultAt` (ADQ:2639), `FixedHeadProducer` (ADQ:2931) now take
  `LR.FixedHeadTelescopeLE`.  This is the interesting engineering datum: a
  single-file `lake env lean` after the swap produced **exactly one error**, in
  `of_orderedLink`.  The eight Group-B adapters, the four Group-C leaf sites
  and both `CoherentFixedHeadStep` producers elaborated **unchanged** — dot
  notation (`htel.toApplicationWithSelfAdequacy`) dispatched to the LE lemmas
  by itself.  Naming the LE lemmas identically inside the `FixedHeadTelescopeLE`
  namespace is what bought the zero-ripple landing.
- `LR.FixedHeadTerminalLink.le_bot` / `.not_nonbot` (ADQ:2844/2855) — the
  second refutation.
- `LR.FixedHeadTelescopeLE.ofOrderedLink` (ADQ:2947) — **the repaired ordered
  peel.**  It takes *no* terminal law: it returns the reached observation with
  its witness, plus a *factory* `∀ outTy, out.HasType outTy → outTy ≤ reachedTy
  → telescope`.  The base typing the old `term` supplied is just the caller's
  own `hout`, and the comparison is handed to the caller — which is the only
  place `hout`/`hA` exist, since they are inputs of `LR.constDefEq` fixed before
  any pattern is matched.
- `LR.FixedHeadTerminalDominance` (ADQ:3160) + `.of_exact` + `.nil` +
  **`LR.FixedHeadProducer.of_dominance`** (ADQ:3206).
- `LR.FixedHeadProducer.of_orderedLink` (ADQ:3114) is KEPT as the reference
  statement with a `.toLE` inserted and a docstring that now says it is vacuous
  twice over and must not be counted as progress.

#### What `FixedHeadProducer` now rests on

`hTyReg` (the registered type's own observation, an input — the peel transports
an observation, it does not manufacture one) + `hout` (**already a hypothesis
of every leaf**, `out.HasType outTy` in `LRS.IotaRHSDefEq`) +
`LR.FixedHeadTerminalDominance`.  The ordered layer machinery — `link`,
`consPeel`, `forallE_inst` lockstep, capture alignment — is fully proved and
enters through `LR.FixedHeadTelescopeLE.ofOrderedLink`.  Net: the four leaf
`producer` hypotheses are, for the first time, reducible to a statement that is
not refutable, and the irreducible content is **one comparison**: the caller's
result-type observation lies below the observation the ordered peel reaches.

Where that comparison must eventually come from, recorded so it is not
re-derived: it relates a logical-relation observation of the syntactic result
type `A` (the caller's `outTy`, carried by `hA`) to a semantic-interpretation
observation of the peeled registered type.  `LE_Interp.Witness` is downward
closed under `≤` (`.mono`) and the observation sets are directed
(`LE_Interp.…join'`), so the two have a common upper bound — but the peel's
terminal is a function of the *initial* `headTy` and the layer `argCap`s, so
using the join would mean choosing `hTyReg` at a large enough observation.
That is a join/maximality theory for `Witness`, not a leaf-local fact, and it
is the honest next design pass on this obligation.

#### Remaining tower (updated)

1. `LRS.CtorSpineTypeUniqPath` — unchanged; environment-level.
2. `LR.CoherentIotaLeafStep Γ₀` — unchanged.
3. δ-definition residual (`LR.ConstDefnDeepStepR` / `LR.ConstDefnDeepInstStep`)
   — unchanged; the δ-rank component (probeK).  *Independently attackable.*
4. `LR.CoherentFixedHeadStep Γ₀` — **DONE**, still conditional on
   `LR.FixedHeadConvertStep Γ₀` alone; unaffected by this session's premise
   swap (its proof did not change a character).
5. `LR.FixedHeadConvertStep Γ₀` — residual `PiHeadNorm`.  **Blocked on the same
   irreducible factor as `PiPathInv`.**
6. `LR.FixedHeadTerminalDominance` (NEW, replaces the refuted
   `FixedHeadTerminalRetarget` and `FixedHeadTerminalLink`) — the four leaf
   `producer` hypotheses.  *Independently attackable*: it is adequacy-free and
   `PiPathInv`-free, living entirely in the shape/witness layer.
7. `∀ depth, LR.SelfAdequateDefeqStepAt Γ₀ depth` — unchanged.  Blocked on
   `PiPathInv`, or on the inner/outer depth mismatch.
8. Assembly: `LR.CoherentRetainedNatStep.of_steps` needs only
   `CoherentSelfStep.of_leafStepsDeep` plus item 4.

**Build note for the fixture slice:** only `ShapeLogRel.lean` and
`ShapeLogRelAdequacy.lean` changed, and only
`Lean4Lean.Experimental.ShapeLogRel` then
`Lean4Lean.Experimental.ShapeLogRelAdequacy` were built (both exit 0).  The
`ShapeLogRel.lean` change is purely additive apart from two proofs whose
*statements* are byte-identical (`TypedTelescope.fixedHeadShapeChain`,
`HasTypeStratifiedS.spineWF_of_foldl`).  The `ShapeLogRelAdequacy.lean` change
is additive apart from the three-site premise swap described above.  The D0/D1/D2
fixture oleans (`SExprParamsD0/D1/D2`) remain stale by design from the previous
four sessions and still need the central rebuild; no fixture source edit is
expected from this session either.  **Note for that rebuild:** `ShapeLogRel.lean`
changed this session for the first time in four sessions, so anything downstream
of it — not only the Adequacy module — must be rebuilt.

— session-C subagent 10

### probeW lands: three §4.4 facts cost no rung, the fourth costs rung 0, and the `FixedHeadConvertStep` docstrings were wrong (2026-08-15, session-C subagent 11)

`ShapeLogRel.lean`: **zero errors, zero sorries**, warning set **identical** to
baseline (23 → 23, `diff` empty).  `ShapeLogRelAdequacy.lean`: **zero errors**,
the same sole `sorry` at `LR.iotaWitnessStep` (ADQ:8631, token ADQ:8661 — it
moved from 8348/8378 only because ~283 lines landed above it), warning set
**identical** to baseline (100 → 100, `diff` empty; the eight new
`unusedSectionVars` the additions would have raised are suppressed with
`omit [Params.Semantic] in`, the linter's own prescribed fix, applied to the
eight declarations that genuinely do not use the instance).  `SExpr.lean`
untouched, and **no change to it is needed** — every lemma the port wanted was
already available there or in `ShapeLogRel.lean`.

**No new `sorryAx`.**  All 48 landed results check with
`[propext, Classical.choice, Quot.sound]`, several with only
`[propext, Quot.sound]`.  Negative control run in the same file:
`LR.iotaWitnessStep`, `LR.adequacy` and `LR.adequacyAt` all report
`[propext, sorryAx, Classical.choice, Quot.sound]`, so the check discriminates
and nothing landed here consumes unconditional adequacy.

#### LEAD WITH THIS: the suspected 16C′ ⇄ 18A′ cycle does not exist

`LRS.PiPathInv` — the single residual of the chain wall — now has a producer
that takes **no adequacy input whatsoever**:

```
LRS.PiPathInv.of_crLadder_noAdequacy (SLR:15381)
  (srp : LRS.ParRedSDefeq) (cr : LRS.CRComplete)
  (std : LRS.PiStandard)   (inv : LRS.PiEdgeInv) : LRS.PiPathInv
```

Every hypothesis is an L4L-18A′ transport of a Church–Rosser /
standardization / subject-reduction fact.  The two semantic side conditions
probeCR had left open — `LRS.PiNotFunTyped` and `LRS.PiNotProof` — are
discharged here **from soundness alone**, with no rung.  So 18A′ can be
scheduled independently of the ADQ fixpoint, and item 1
(`LRS.CtorSpineTypeUniqPath`, which goes through `.of_piPathInv`) inherits the
same clean dependency.

#### Why the four §4.4 facts split the way they do

*Disjointness* is a statement about **head shapes**, and `LE_Interp` already
records one: `WShape.sort r` and `WShape.forallE b f` are incomparable, and
`LE_Interp.sound` transports a shape across a strong equality, so a sort
equated to a Pi would carry both shapes at once.  No fixpoint rung is involved
— hence `LRS.SortForallEDisj.of_soundness` (SLR:15113),
`LRS.PiNotFunTyped.of_soundness` (SLR:15124),
`LRS.PiNotProof.of_soundness` (SLR:15135) take no adequacy hypothesis.

*Injectivity* is a statement about the **level**, and `WShape.sort` records
only `decide (u ≠ .zero)`.  The sharp boundary is machine-checked as
`LRS.sortInv_bit_only` (SLR:15469): soundness recovers that bit and **nothing
more**.  This is also the strongest available non-vacuity evidence for the
whole pass — if `[Params] [Params.Semantic]` were inconsistent, or if the
soundness machinery proved too much, `LRS.SortInv` would fall out of the same
two lines.  It does not.

`LRS.SortInv` therefore needs a rung, and the rung is **0**:
`HasTypeStratifiedS.sort'` is a *nullary* constructor whose depth index is a
free variable (`HasTypeStratifiedS.sort_zero`, SLR:15160), so the observation's
subject never consumes depth.  Neither probeS wall is reachable: bounded output
does not apply (the conclusion is `False` or a bare level equation, so nothing
is re-decorated), and the leaf supplies no anchor (the only certificate demanded
is for a syntactic sort).

#### The two wrong docstrings, corrected

**`LR.FixedHeadConvertRightValid` (now ADQ:2515).**  The old text said the
residual is `PiHeadNorm` = `TypeWHNFEx` + `PiHeadStable`.  That is wrong in
**both** directions, and `LRS.TypeWHNFEx` never arises at all — the Prop
carries `TyDefEq A A a` as a *hypothesis*, so the left endpoint's weak-head
normal form is **given**, not manufactured.  What the observations really are:

* `a = .sort r`: *exactly* a transport, namely `LRS.SortHeadNorm` (SLR:15405,
  the SExpr transport of `VEnv.IsDefEq.reduce_sort`, HeadReduction:493, which
  Theory proves).  Machine-checked **both ways**:
  `LR.fixedHeadConvertRightValid_sort_of_transport` (ADQ:2555) and
  `LRS.SortHeadNorm.of_fixedHeadConvertRightValid` (ADQ:2570).  Nothing weaker
  suffices, nothing stronger is demanded.
* `a = .forallE b f`: `LR.tyDefEq_forallE_unfold` (SLR:15425) is `.rfl`, and
  the first two conjuncts of the unfolded `LRS.ValTyPi2` *are* the two
  weak-head reductions — that half is `LRS.PiHeadNorm`, CR-covered.  The
  remaining four (`TypeDefEqPath` ×2, `TyDefEq B₁ B₂ b`, `LRS.PiDefEq`) are
  semantic **component** data the CR ladder does not produce, isolated as
  `LR.PiComponentTransport` (SLR:15436); see
  `LR.fixedHeadConvertRightValid_forallE_of_parts` (ADQ:2582).

**`LR.FixedHeadConvertStep` (now ADQ:2470).**  Its conclusion is
`TyDefEq A B a`, not `TyDefEq B B a`, so the sort case additionally demands
that `A` and `B` reach the **same** sort.  Discharged from three inputs, none
of them `TypeWHNFEx`: `LRS.SortHeadNorm`, `LRS.SubjectRedS` (a CR-ladder item)
and `LRS.SortInv` (the rung-0 item) — `LR.fixedHeadConvertStep_sort_of_parts`
(ADQ:2602).

**`LR.FixedHeadConvertStep.of_rightValid` (now ADQ:2536).**  The old "one line
away" framing understates the price.  The *line* is one line; the *input* is
the full uncollapsed `JointStratifiedInversion`: unbounded-depth `sortInv`, and
an `IsDefEq`-valued — i.e. already collapsed — `forallEInv` with endpoint
stratification bookkeeping at `n - 1`, strictly stronger than the path-valued
`LRS.PiPathInv` the rest of the development charges.  Corrected in place.

#### G4: the rung-0 consumption is real, and is mitigated, not papered over

`LR.FixedHeadConvertStep` is depth-free, so it has to hold at rung `0` — and
there its sort observation would consume a `LRS.SortInv` produced *at rung 0*
by `LRS.SortInv.of_adequacyAtDepth_zero`.  That is same-rung consumption at
exactly that rung.  The probe's `of_parts` route is sufficient but not
necessary, so the mitigation taken is the one `LR.SelfAdequateDefeqStepAt`
(ADQ:6974, with `.of_lowerAdequacy` at ADQ:7006) already uses:

```
LR.FixedHeadConvertStepAt Γ₀ outerDepth (ADQ:2635)
  -- adds: depth < outerDepth → HasTypeStratifiedS Γ₀ A (.sort u) core depth →
```

* `LR.FixedHeadConvertStep.at` (ADQ:2647) — the indexed form is a **weakening**
  of the depth-free one, so demanding it never demands more.
* `LR.FixedHeadConvertStepAt.zero` (ADQ:2655) — **the mitigation.**  At rung 0
  the indexed step is unconditional, so the rung that *produces* `LRS.SortInv`
  consumes nothing from itself.  The same-rung consumption exists only for the
  depth-free Prop.
* `LR.fixedHeadConvertStepAt_sort_of_lowerAdequacy` (ADQ:2664) — at every
  positive rung the sort observation takes its `LRS.SortInv` from the strictly
  lower family.  The index has exactly one job and the arithmetic is explicit:
  `depth < outerDepth` forces `0 < outerDepth`, which is what puts rung `0`
  inside `lower`.

**Landed BESIDE the depth-free Prop, not replacing it, and here is the
migration.**  `convert` is spent inside
`LR.FixedHeadShapeChain.pathSemantics` (SLR:14506) while zipping a
`SExpr.PathSpineWF`, whose `conv`/`ret` edges carry a bare `IsDefEq` and no
shape, witness or endpoint validity — so there is no certificate at the
consumption site to index on.  Supplying one there is the G5 gap, a different
obligation; migrating `LR.CoherentFixedHeadStep.of_convertStep` (ADQ:6140) and
`LR.FixedHeadTelescope(LE).toApplicationWith` (ADQ:2756, 2801) to the indexed
form is blocked behind it and is not a one-step change.  Nothing was weakened
to hide the consumption.

#### Vacuity discipline

Standing policy after the two false Props earlier today.  Every new `Prop` this
session is checked:

* The three proved disjointness facts are *refutations*, so the risk is that
  the judgment they refute is empty.  It is not: `LRS.nonvacuous_sort`
  (SLR:15457) and `LRS.nonvacuous_pi` (SLR:15483) inhabit `IsDefEq` at both
  shapes involved.
* `LRS.sortInv_bit_only` (SLR:15469) is the **negative control** described
  above — the sharp boundary showing the machinery does not prove too much.
* `LRS.SortHeadNorm` — inhabited on the diagonal
  (`LRS.sortHeadNorm_diagonal`, SLR:15488); it is the transport of a theorem
  Theory proves.  No derivation of `False` found.
* `LR.PiComponentTransport` — inhabited on the diagonal
  (`LR.piComponentTransport_diagonal_witness`, SLR:15491).  No `False` found.
* `LR.FixedHeadConvertStepAt` — vacuous at rung 0 by construction, so the check
  is done at a *positive* rung: `LR.fixedHeadConvertStepAt_nonvacuous`
  (ADQ:2697) exhibits a syntactic sort meeting all four hypotheses at
  `outerDepth = 1` **and** the conclusion simultaneously.  Not empty-hypothesis
  vacuous, not refutable at the one instance computable outright, and implied
  by the depth-free Prop.  No `False` found.
* `LRS.SortForallEDisjAt` / `LRS.SortInvAt` are faithful at `d = 0`
  (`LRS.SortForallEDisj.of_at_zero` SLR:15179, `LRS.SortInv.of_at_zero`
  SLR:15184), because the certificate they demand holds unconditionally.
  `LRS.PiNotFunTyped` and `LRS.PiNotProof` are deliberately **not** indexed:
  their subject is an arbitrary Pi, so recovering a bare form from a depth-`d`
  form would need `LRS.PathRestratifyAt`-strength uniform depth bound (probeS
  Part 7), which collapses the depth hierarchy.  Preserved from the probe.

#### Placement rule used

Dependencies decided the file, with one deliberate exception.  Everything whose
*statement* mentions only `LE_Interp` / `LR` / `LogRel` / `SExpr` went to
`ShapeLogRel.lean` (the shape layer, the three disjointness facts, the whole CR
ladder, `LRS.SortHeadNorm`, the `tyDefEq_*` unfoldings,
`LR.PiComponentTransport`, the vacuity witnesses).  Everything whose statement
mentions an ADQ Prop (`LR.ContextualAdequacyAtDepth`,
`LR.FixedHeadConvertRightValid`, `LR.FixedHeadConvertStep`) went to
`ShapeLogRelAdequacy.lean`.  **The exception:** the four per-observation
`fixedHeadConvert*` theorems have SLR-only dependencies but were placed in ADQ
anyway, immediately beside the docstrings they correct — a corrected docstring
whose evidence sits 6 000 lines away in another file is a docstring that will
go wrong again.

#### Remaining tower (updated — items 1, 5 and 7 restated)

1. `LRS.CtorSpineTypeUniqPath` — unchanged as an obligation, but its route
   through `LRS.PiPathInv` is now **adequacy-free**: `.of_piPathInv` composed
   with `LRS.PiPathInv.of_crLadder_noAdequacy` reduces it to L4L-18A′ alone.
2. `LR.CoherentIotaLeafStep Γ₀` — unchanged.
3. δ-definition residual (`LR.ConstDefnDeepStepR` / `LR.ConstDefnDeepInstStep`)
   — unchanged; the δ-rank component (probeK).  *Independently attackable.*
4. `LR.CoherentFixedHeadStep Γ₀` — **DONE**, still conditional on
   `LR.FixedHeadConvertStep Γ₀` alone; its proof did not change a character.
5. `LR.FixedHeadConvertStep Γ₀` — **re-diagnosed.**  It is *not* "residual
   `PiHeadNorm`".  At the sort observation it is
   `LRS.SortHeadNorm` + `LRS.SubjectRedS` + `LRS.SortInv`, all three of which
   are now producible (the first two from 18A′, the third at rung 0).  At the
   Pi observation it is `LRS.PiHeadNorm` (18A′-covered) **plus**
   `LR.PiComponentTransport`, which the CR ladder does **not** cover — that is
   the honest residual.  Shapes other than `sort` and `forallE` are outside
   this analysis.  Carries the G4 tripwire; indexed variant landed beside it.
6. `LR.FixedHeadTerminalDominance` — unchanged.  *Independently attackable*:
   adequacy-free and `PiPathInv`-free.
7. `∀ depth, LR.SelfAdequateDefeqStepAt Γ₀ depth` — unchanged as an obligation,
   but its "blocked on `PiPathInv`" premise is now milder: `PiPathInv` no
   longer waits on the ADQ fixpoint, only on 18A′.
8. Assembly: `LR.CoherentRetainedNatStep.of_steps` needs only
   `CoherentSelfStep.of_leafStepsDeep` plus item 4.

#### The exact remaining inputs to the 16C′ leaf

* **From L4L-18A′ (Theory transports, no adequacy):** `LRS.ParRedSDefeq`,
  `LRS.CRComplete`, `LRS.PiStandard`, `LRS.PiEdgeInv`.  These four give
  `LRS.PiPathInv`, hence `LRS.PiHeadNorm` and `LRS.SubjectRedS` as well.
  `LRS.SortHeadNorm` is a fifth, of the same kind
  (`VEnv.IsDefEq.reduce_sort`, HeadReduction:493).
* **From the ADQ fixpoint, at rung 0 only:** `LRS.SortInv`, via
  `LR.ContextualAdequacyAtDepth 0`.
* **Not covered by either:** `LR.PiComponentTransport Γ₀` — the component half
  of the Pi observation of `LR.FixedHeadConvert{Step,RightValid}`.  This is the
  one genuinely new named residual this session produced.

**Build note for the fixture slice:** only `ShapeLogRel.lean` and
`ShapeLogRelAdequacy.lean` changed, and only
`Lean4Lean.Experimental.ShapeLogRel` then
`Lean4Lean.Experimental.ShapeLogRelAdequacy` were built (both exit 0).  The
`ShapeLogRel.lean` change is **purely additive** — one appended block, every
pre-existing byte unchanged.  The `ShapeLogRelAdequacy.lean` change is additive
apart from three docstrings rewritten in place (no statement, proof or name
touched).  The D0/D1/D2 fixture oleans (`SExprParamsD0/D1/D2`) remain stale by
design and still need the central rebuild; no fixture source edit is expected
from this session.  `ShapeLogRel.lean` changed again, so everything downstream
of it must be rebuilt.

— session-C subagent 11

### R11 ports, `PiComponentTransport` dissolves into a shape-level induction, and the "last input" docstring is retracted (2026-08-15, session-C subagent 12)

Three landings, one retraction, one probe-only finding.  The headline is the
second item: the residual the previous session recorded as *"the one genuinely
new named residual"* is not a residual at all.

#### 1. Rung R11 ported (`ShapeLogRel.lean`)

`plans/probes/probeR11-piedgeinv.lean` ported verbatim, plus its supporting
lemmas: `LRS.PiTypeInv` (:15267, the one new `Prop`) and
`LRS.PiTypeInv.of_strong` (:15466, proved outright from `IsDefEq.strong` +
`IsDefEqStrong.forallE_inv'` — no CR, no adequacy), `LRS.parRedS_forallE_path`
(:15493), `LRS.normalEqPiInv` (:15529), `LRS.PiEdgeInv.of_crLadder` (:15572),
`LRS.PiEdgeInv.of_crLadder_noAdequacy` (:15594), the composites
`LRS.PiPathInv.of_crLadder_R11` (:15609) and
`LRS.crComplete_is_the_last_input` (:15660), and non-vacuity witnesses
`LRS.piTypeInv_nonvacuous` / `LRS.piEdgeInv_nonvacuous` (:16018/:16027).

Two facts worth keeping, both about R11's price:

* **R11 sits strictly BELOW the `PiHeadNorm` rung, not beside it.**  Not one
  step performs a weak-head reduction: no `LRS.PiStandard`, no
  `LRS.PiHeadNorm`, no `LRS.ReduceForallE`, no `LRS.TypeWHNFEx`.  The `≫*`
  chains from `LRS.CRComplete` are consumed *as chains*.
* **R11 costs `LRS.PiNotProof` but not `LRS.PiNotFunTyped`** — one of the two
  sort facts, not both.  Knowing *both* `NormalEq` endpoints are Pis makes
  `etaL`/`etaR` structural (a `.lam` is not a `.forallE`), so they die by
  `cases`.  `LRS.NormalEqPiInvL`, which knows only the right endpoint's shape,
  must refute `etaL` semantically and therefore does need the second fact.
  Six of eight `NormalEq` constructors are structural in `normalEqPiInv`.

Why the conclusion stays path-valued, recorded in the `parRedS_forallE_path`
docstring: `ParRed.forallE_inv` cannot be iterated along a chain because the
codomain components live in the *shifting* contexts `A₀::Γ`, `A₁::Γ`, … and
SExpr's `ParRed` has no context-conversion lemma (it is ported only at `rfl`
and `weak'`).  The fix is to convert each step to a typed equality immediately
via `LRS.ParRedSDefeq` and walk the codomain one edge at a time with
`TypeDefEqPath.defeqDF_l`.  Collapsing the accumulated path would charge
`TypeDefEqPath.collapse`, i.e. raw type uniqueness.

#### 2. RETRACTION — `LRS.CRComplete` is **not** the last input; the CR ladder is circular

Received mid-session from the coordinator (probe
`plans/probes/probeR12-parredS-clean.lean`, green, no `sorryAx`), and it
invalidates the gloss the previous session landed on
`LRS.crComplete_is_the_last_input`.  `VEnv.ParRedS.defeq` / `.standard` do NOT
depend on `weakN_iff`; their `sorry` roots are `IsDefEqU.sort_inv` and
`IsDefEqU.forallE_inv_stratified` — the 16C′ deliverables themselves:

    LRS.PiPathInv = SExpr.forallE_inv ⇒ forallE_inv_stratified
      ⇒ IsDefEqU.forallE_inv ⇒ ParRed.defeq ⇒ ParRedS.defeq
      ⇒ LRS.ParRedSDefeq ⇒ (R11) LRS.PiPathInv

The β case is where the dependency is essential, for a reason worth stating
rather than citing: firing β requires reconciling an application's domain with
its abstraction's own domain, which *is* Pi injectivity.  The two essential
uses are `ParRed.defeq` (ChurchRosser, β case) and `StRed.triangle`
(HeadReduction, β case) — anchor on the **names**, both files are moving.

Docstrings corrected in place (no statement, proof or name touched):

* `LRS.crComplete_is_the_last_input` (:15660) — full circularity note; the
  theorem is retained verbatim because it is a *true implication*, and keeping
  the mis-named target visible is how the ledger records that the arrow does
  not point where it was thought to.
* `LRS.PiPathInv.of_crLadder_noAdequacy` (:15403) — the claim "the
  suspected 16C′ ⇄ 18A′ cycle does not exist" is narrowed to what is actually
  proved: no cycle with the **ADQ fixpoint**.
* the R11 subsection header, `LRS.PiEdgeInv.of_crLadder`,
  `LRS.PiPathInv.of_crLadder_R11`, `LRS.CtorSpineTypeUniqPath.of_crLadder`,
  and ADQ's `LR.MajorChainAnchorStep.of_crLadder` /
  `LR.FixedHeadConvertStep.of_crLadder`.

**R11 is an interderivability result, not a reduction.**
`LRS.PiEdgeInv.of_piPathInv` runs the other way in one line.  What R11 buys is
real but narrower than advertised: single-edge Pi injectivity suffices, so the
path-valued form is not independently needed.

Not ported for budget: the coordinator's sort-typed narrowing
(`LRS.ParRedSDefeqSort` / `CRCompleteSort` / `PiStandardSort` and
`LRS.PiPathInv.of_crLadder_R12`).  It is the natural next port and is
orthogonal to everything below.

#### 3. HEADLINE — `LR.PiComponentTransport` is the inductive step of an induction on the SHAPE LEVEL

Probe `plans/probes/probeR13-…` aside, the work is
`plans/probes/probeR12-picomponent.lean`, landed at `ShapeLogRel.lean`
:15733-:15963.  The previous session's account —
"`LRS.ValTyPi2`'s first two conjuncts are `LRS.PiHeadNorm`; the remaining four
are semantic component data the CR ladder does not produce" — reads one
unfolding correctly and the obligation wrongly.

**The component data at the Pi observation is the same statement one shape
level down.**  Unfolding `TyDefEq A B (.forallE b f)` at level `n+1` exposes
`TyDefEq B₁ B₂ b` and, inside `LRS.PiDefEq`,
`TyDefEq (F.inst a) (F.inst b') (f.app p)` — all at level `n`.  So the convert
step at `n+1` consumes the convert step at `n`, and `PiComponentTransport` is
not new data: it is the inductive step.

Also: **the two-reduct form is illusory.**  Both weak-head reductions in
`LR.PiComponentTransport` reduce the *same* `B`, so `WHRedS.determ` collapses
them (`LR.PiComponentTransport.of_diag` :15785, converse `.diag` :15791).
There was never anything to reconcile.

Landed: `LR.PiComponentTransportDiag` (:15776), `LR.ConvertStepAt` (:15797),
`LR.ConvertStepAt.path` (:15806) and `.path_right` (:15818),
`LRS.IndTyHeadNorm` (:15835), `LR.convertStep_forallE` (:15851),
`LR.convertStep_sort` (:15899), `LR.convertStepAt_all` (:15920),
`LR.PiComponentTransport.of_crLadder` (:15944).  In ADQ:
`LR.FixedHeadConvertStep.of_crLadder` (:2672),
`LR.FixedHeadConvertRightValid.of_crLadder` (:2679),
`LR.FixedHeadConvertStep.of_crLadder_R11` (:2691).

Cost per shape constructor of `WShape (n+1)`, which is the whole content:

| shape          | obligation |
| -------------- | ---------- |
| `bot`          | `True` |
| `lam`, `ctor`  | `True` |
| `sort r`       | `LRS.SortHeadNorm` + `LRS.SubjectRedS` + `LRS.SortInv` (level-uniform; a `LogRel` *field*, no recursion) |
| `forallE b f`  | `LRS.PiHeadNorm` + `LRS.SubjectRedS` + `LRS.PiEdgeInv` + the step at level `n` |
| `indTy`        | `LRS.IndTyHeadNorm` — **the one new obligation** |

Three of six are `True`.  Two implementation notes worth keeping:

* The Pi rung concludes the **heterogeneous** `TyDefEq A B`, not the
  right-endpoint form.  That is strictly more convenient: `LRS.PiEdgeInv`
  hands back paths `A₁ ⇝ B₁` and `G₁ ⇝ F₁` that slot directly into
  `LRS.ValTyPi2`'s two `TypeDefEqPath` fields, so no path is reversed,
  composed, or collapsed.
* `LR.ConvertStepAt.path` is what lets a *single-edge* convert step consume
  `LRS.PiEdgeInv`'s *path*-valued output — induction on the path, `trans_ty` at
  each join.  Path collapse is never charged anywhere in the layer.
* `LRS.PiInstDefEq`'s raw fields (`leftDefEq`/`rightDefEq`) come from
  `IsDefEqStrong.subst` at the equality substitution `a ≡ b' : A₁`
  (`Ctx.SubstEq.cons`), charging no semantics at all.

**`LRS.IndTyHeadNorm` has no upstream analogue.**  Theory's `reduce_*` family
stops at `IsDefEq.reduce_sort` (HeadReduction:493) and `.reduce_forallE`
(:512); there is no `reduce_const`.  It is CR-ladder *shaped* (a head-form
transport, no semantic component data), not adequacy-shaped, and it is the only
such residual the induction exposes.

**G4 is unaffected.**  The induction is on the *shape level*, orthogonal to the
adequacy rung.  `LRS.SortInv` is consumed exactly where it was — at the sort
observation, at every level — so `LR.FixedHeadConvertStepAt` remains the right
mitigation and nothing about the rung-0 same-rung consumption changes.

Read honestly against the retraction in §2: this does **not** make the convert
step free, because `LRS.PiEdgeInv`/`LRS.PiHeadNorm` are inside the loop.  What
it does say is sharper and still worth the session: **`LR.FixedHeadConvertStep`
demands nothing beyond the 16C′ leaf itself**, plus `LRS.SortInv` at rung 0 and
`LRS.IndTyHeadNorm`.  It was recorded as a separate obligation; it is not one.

#### 4. `LRS.CtorSpineTypeUniqPath` closes end-to-end

`LRS.CtorSpineTypeUniqPath.of_crLadder` (SLR :15676) and
`LR.MajorChainAnchorStep.of_crLadder` (ADQ :1180).  `of_piPathInv` already
existed; R11 supplies its input.  Same honest reading as §3: the residual costs
exactly `LRS.PiPathInv` and adds nothing on top of it — in particular no
adequacy rung and no raw type uniqueness.

#### 5. Probe-only — the `CoherentIotaLeafStep` frame layer is mechanical once the type shape rides along

`plans/probes/probeR13-rectframe.lean` (green, no `sorryAx`; **not landed**).
The previous session established that the frame layer is *not* mechanical
because `LogRel.DefEqRect` is indexed by an element shape **and** a type shape
`(m, a)` while `LRS.CtorFrame` is indexed by the element shape alone.  The
probe localizes that failure exactly: **it is entirely in the frame's index,
not in the transport.**

`LRS.RectFrame` is `LRS.CtorFrame` with the type shape threaded alongside the
element shape and `HasType` coherence recorded wherever the element shape
moves — same four constructors, same level arithmetic.  With it,
`LRS.RectFrame.rect` is four one-liners: `LogRel.DefEqRect.mono_l` for `mono`,
`LogRel.LiftEquiv.rect` in each direction for `lift`/`unlift`.  The frame also
composes (`LRS.RectFrame.trans`).

The blocking case is `mono` and the reason is precise: `DefEqRect.mono_l` needs
`m.HasType a` **and** `m'.HasType a` for one common `a`, and a frame recording
only `m ≤ m'` can supply neither.  Choosing `a` inside the transport is exactly
the independent re-selection of the type observation that the N2 decision
exists to prevent.  So the honest statement of the residual is not "prove a
transport lemma" but **"produce `RectFrame`, not `CtorFrame`"** — the shape must
be threaded positionally from the leaf that owns it, in the frame's
*producers*.  `LRS.CtorFrame.TyWitness` names that demand and
`LRS.CtorFrame.rect_of_tyWitness` shows there is nothing left to prove once it
is met.  Left as a probe because upgrading the index touches the frame
producers, which is not an additive change.

#### Vacuity discipline

Six new `Prop`s this session, all checked.  `LRS.PiTypeInv` and
`LRS.RectFrame` are **proved/inhabited outright**, so they cannot be false.
The other four carry explicit non-degenerate witnesses:

* `LRS.piTypeInv_nonvacuous` / `LRS.piEdgeInv_nonvacuous` — the hypothesis is
  satisfiable with *no* environment assumptions, in the empty context: a Pi
  over two sorts (`LRS.nonvacuous_pi .sort .sort`).
* `LR.piComponentTransportDiag_nonvacuous` (:16054) — sharper than the
  pre-existing diagonal witness: the *reduct* is chosen by the caller and
  determinism forces agreement.  So the diagonal form can only fail off the
  diagonal, which is precisely where the level induction supplies it.
* `LR.convertStepAt_nonvacuous` (:16070) — at the **sort** observation, a
  non-degenerate shape at every level and every relevance bit, with a
  content-carrying conclusion (it forces `B` to reach the *same* sort).
* `LRS.indTyHead_nonvacuous` (:16080) — honestly environment-*conditional*:
  inhabited as soon as any nullary inductive type is declared.  There is no
  `Params`-free inductive type, and recording that is the correct statement of
  the residual's scope.

No new `Prop` was left unwitnessed and no derivation of `False` succeeded.

#### Build note

Only `ShapeLogRel.lean` and `ShapeLogRelAdequacy.lean` changed, plus two new
probes (`probeR12-picomponent.lean`, `probeR13-rectframe.lean`).  Both targets
built in order, both exit 0.  `ShapeLogRel.lean`: **zero warning delta**,
verified by sorted diff against a pre-change baseline; **zero sorries**.
`ShapeLogRelAdequacy.lean`: **exactly one** sorry, `LR.iotaWitnessStep`
(declaration :8716, token :8746); no warning falls in any inserted range and no
warning names any inserted declaration.  Both files' changes are additive apart
from the docstring corrections listed in §2, none of which touched a statement,
proof, or name.  Everything downstream of `ShapeLogRel.lean` needs rebuilding.

— session-C subagent 12

### The CR ladder banks as a *consumer* of the leaf; `TypeDefEqPath` moves to `SExpr.lean` (2026-08-15, session-C subagent 13)

Source: `plans/probes/probeR13-loop.lean` (740 lines, green, all 22
`#print axioms` `sorryAx`-free).  R13 proved the ladder rung
`LRS.ParRedSDefeq` and the L4L-16C′ leaf `LRS.PiPathInv` **interderivable**.
That closes the ladder as a way to *discharge* the leaf — any proof of the
rung is a proof of the leaf — but the very same fact makes the ladder a
valuable downstream **consumer**.  This session banks the consumer direction.

#### 1. The `TypeDefEqPath` relocation (the one non-additive change)

`TypeDefEqPath` and its whole conversion API — `single`, `trans`, `leftType`,
`rightType`, `left`, `right`, `symm`, `defeqDF`, `defeqDF_l`,
`defeqDF_l_path`, `subst` — moved out of `ShapeLogRel.lean` (old :10244–:10317)
and into `Lean4Lean/Experimental/SExpr.lean:3613`, immediately after
`IsDefEq.defeqDF_l` (:3588) and `HasType.defeq_l` (:3592).

* **It is clean.**  The API's only inputs are `IsDefEq.defeqDF`,
  `IsDefEq.defeqDF_l` (:3588), `IsDefEq.subst` (:3255) and `Ctx.Subst` (:3025)
  — every one SExpr-level.  Nothing about it was logical-relation-flavoured.
* **Zero consumer fixups.**  `ShapeLogRel.lean` re-elaborated with every
  existing consumer *unchanged*, and `ShapeLogRelAdequacy.lean` likewise: the
  name `Lean4Lean.SExpr.TypeDefEqPath` is unchanged, and both files see it
  through the same namespace.  The signal the brief asked for — a consumer
  breaking — did not appear.  75 lines left SLR, replaced by a 9-line pointer
  note: net −66.
* **`TypeDefEqPath.collapse` deliberately stayed** in `ShapeLogRel.lean`
  (now :10521).  It did not sit in the moved block and it has one extra input,
  `LogRel.RawTypeUniq` (:10514), which is declared there.  Moving it would
  have dragged raw type uniqueness into `SExpr.lean` for no gain.
* **Placement deviation, recorded.**  The brief asked for the inversion suite
  "beside `IsDefEqStrong.forallE_inv'` (:2284)".  That is not reachable:
  `IsDefEq.hasType` is at :2370 and `Ctx.Subst` at :3025, both *after* :2284,
  so no formulation of the path API can precede `forallE_inv'`.  The suite
  therefore sits with the path API at :3705–:3844, with docstrings pointing
  back to `forallE_inv'`, whose proof style it mirrors exactly.

#### 2. S1 — the inversion suite (SExpr.lean)

`IsDefEqStrong.app_inv'` (:3705), `.lam_inv'` (:3753), `.forallE_inv_path`
(:3804).  Each also returns the `TypeDefEqPath` from the subject's **own**
type to the declared type `V`; that is the whole novelty over Theory's
`VEnv.HasType.app_inv` / `.lam_inv`, and it is what removes every
`IsDefEq.trans_l` / `uniqU` fixup the Theory proofs spend.  Recorded in the
docstrings.

Each measures `[propext, Quot.sound]`, each is `#sorryRoots`-CLEAN, and the
dependency walker confirms **none of them reaches `IsDefEq.strong`** — nor
`LRS.PiPathInv`.  They are pure structural case analysis on `IsDefEqStrong`.

#### 3. S2 — the loop as a downstream consumer (ShapeLogRel.lean, at EOF)

`LRS.PatStep`, `.of_typeUniq`, `.of_piPathInv`, `applyS_congr`,
`ParRed.defeq_of_piPathInv`, `ParRedS.defeq_of_piPathInv`,
`LRS.parRedSDefeq_of_piPathInv`, `LRS.piPathInv_iff_parRedSDefeq` (headline),
`LRS.PiEdgeInv.of_piPathInv`, `LRS.PiPathInv.of_piEdgeInv_collapse`,
`LRS.patStep_nonvacuous`.

**The payoff, docstringed prominently at the section head.**  The moment 16C′
lands, the ladder is free: `LRS.ParRedSDefeq` outright, `LRS.SubjectRedS`
(already landed as `WHRedS.defeq_of_piPathInv`), and the single-edge
`LRS.PiEdgeInv`.  It also retires the `sorryAx` that Theory's
`VEnv.ParRed.defeq` and `VEnv.StRed.triangle` carry — probeR12 measured their
roots as `IsDefEqU.sort_inv` / `IsDefEqU.forallE_inv_stratified`, i.e. the
16C′ deliverables themselves.  The walker confirms the route reaches
`LRS.PiPathInv` and **not** `LRS.CRComplete`, `LRS.PiStandard`,
`LRS.SubjectRedS`, `LRS.PiEdgeInv`, `LogRel.RawTypeUniq` or `LR.adequacy`.

**One correction to the brief's framing, machine-checked.**  `LRS.PatStep` was
to be banked as "the second, independent uniqueness site", and in *content* it
is: `.of_typeUniq` proves it from raw type uniqueness and from nothing about
Pi shapes.  But it is **not an extra residual on top of the leaf**.  Every
redex a `Pattern.Action` can match is a constant-headed spine, and spine type
uniqueness is already reduced to the leaf in this file
(`LRS.constSpineTypeUniqPath`, :11458), so `LRS.PatStep.of_piPathInv` — five
lines, mirroring the `extra` case of the landed `WHRed.defeq_of_piPathInv`
(:11507) — discharges it from `LRS.PiPathInv` as well.  Hence
`LRS.parRedSDefeq_of_piPathInv`: the rung from the leaf with **no side
conditions**.  This strengthens rather than weakens the banked claim, and both
docstrings say so.  `LRS.PiEdgeInv.of_piPathInv` was landed for the same
reason: two existing docstrings (:15361, :15579) already referred to it as
"a one-liner in the other direction"; it is now checked rather than asserted.

`LRS.PiPathInv.of_piEdgeInv_collapse` carries the trade explicitly: collapsing
a path to a single edge costs `LogRel.ContextualRawTypeUniq`, so the
`PiEdgeInv` framing **trades the 16C′ leaf for the L4L-17 co-deliverable**
rather than avoiding it.

#### 4. S3 — the closure records

`beta_congr_no_piInv` (the β *congruence* needs no Π-inversion at all),
`LRS.BetaFire` + `.of_piPathInv` (the *contraction* is where the leaf is
charged), `betaSort_domain_unconstrained` (sort-typedness constrains the
result type, never the domain — the sort restriction is not an escape), and
`LRS.ChainAnchorAt` + `.uniformDepthBound` / `.of_uniformDepthBound` (the
stratification escape's consumer-side obstruction, *provably equivalent* to a
uniform stratification bound — the same fatal proposition probeS identified).
Banked so nobody re-attempts the dead routes.

#### 5. Vacuity discipline

Three new `Prop`s (`LRS.PatStep`, `LRS.BetaFire`, `LRS.ChainAnchorAt`), all
witnessed:

* `LRS.patStep_nonvacuous` — environment-conditional, like
  `LRS.indTyHead_nonvacuous`: inhabited wherever `Pattern.Action` is, and at
  the action's own type the conclusion *is* `action.sound`, so no derivation
  of `False` is available that does not refute `Pattern.Action.sound`.  Two
  independent derivations (`.of_typeUniq`, `.of_piPathInv`) rule out
  underivability.
* `LRS.betaFire_nonvacuous` — at a **non-degenerate** instance: the witness of
  `betaSort_domain_unconstrained`, whose application domain is syntactically
  different from the abstraction's own.  Empty context, no environment
  assumptions.
* `LRS.chainAnchorAt_nonvacuous` — hypothesis inhabited in the empty context
  with no environment assumptions, which is what makes the
  `.uniformDepthBound` equivalence a real obstruction rather than a vacuous
  one.

No new `Prop` was left unwitnessed and no derivation of `False` succeeded.

#### 6. Build note

Three targets, built in the prescribed order, all exit 0:
`Lean4Lean.Experimental.SExpr`, then `...ShapeLogRel` (31s), then
`...ShapeLogRelAdequacy` (12s).  Every block compiled **first try**.

*Warning-profile delta: zero.*  SExpr 6, ShapeLogRel 23, Adequacy 100 — the
same counts as the pre-change baseline, and verified by diff to be the same
warnings (SLR modulo the line shift from the relocation; ADQ byte-identical).
No `omit [Params.Semantic] in` was needed: every new declaration genuinely
uses its section variables.

*Sorry inventory, exact:*

* `SExpr.lean` — **4**, the known off-path ones, unchanged in identity and
  shifted +254 lines by the insertion: :4051, :4287, :4390, :4456 (was :3797,
  :4033, :4136, :4202).
* `ShapeLogRel.lean` — **0**.
* `ShapeLogRelAdequacy.lean` — **exactly 1**, `LR.iotaWitnessStep`
  (declaration :8716, token :8746), untouched.

Everything downstream of `SExpr.lean` needs rebuilding; `SExprParams*` was
deliberately not built here.

— session-C subagent 13
