# L4L-16E design pass: `IsDefEqU.weakN_iff`, forward direction

2026-08-15. Companion probe: `plans/probes/probeE-weakn.lean` (type-checked
statements for every staged obligation; two clean proofs; one tainted
assembly certificate). Target:
`Lean4Lean/Theory/Typing/UniqueTyping.lean:171-174` — the sole sorry gating
the entire strengthening suite (`weakN_iff'`, `OnCtx.weakN_inv`,
`IsDefEq/HasType/IsType.weakN_iff`, `skips`, `weak'_iff`, the SpineWF
inversions, ~20 ChurchRosser sites, projection/TrProj consumers).
Allowlisted at `Audit/SorryFrontier.lean:173`.

## 1. Decision

**Route: de-circularized stratified standardization on the Theory side
("SST"), executed as an L4L-18A′-coupled slice — NOT as a 16E leaf.**
The forward direction is real mathematics: it is the strengthening
corollary of typed standardization (Church–Rosser + normal-comparison
strengthening), and every elementary route is provably blocked (§3, §4).
The repo already contains ~2,600 lines of exactly the needed machinery
(`ChurchRosser.lean`, `HeadReduction.lean`) — but built *downstream* of
this sorry, consuming it in the core. The work is therefore a
dependency-inversion refactor plus two genuinely new proof cores, not a
from-scratch development. Verdict: **research-grade** (3–6 focused weeks
after its inputs land), and it cannot close within 16E as scheduled.
Recommendation for sequencing in §7.

The probe machine-checks the decisive positive fact: given the staged
lemmas (S1, S-PR, S-NE below), the forward direction assembles in ~15
lines (`IsDefEqU.weakN_inv_staged`). Everything reduces to making those
stages weakN_iff-free.

## 2. Corrections and additions to the recorded route analysis

Verified against source; differences from the 2026-08-15 recon:

1. **`Theory/Typing/HeadReduction.lean` was missing from the map** and is
   the single most important file for this problem: Theory-side `WHRed`
   with proved `weakU_inv` (:94), `WHRedS.weakU_inv` (:292), whnf
   determinism, standardization `StRed` + `ParRedS.standard` (:489),
   head-normalization of defeq at observation heads
   (`IsDefEq.reduce_sort` :493, `reduce_forallE` :512), and a
   syntax-directed `InferType` with `determ`, `weakU_inv` (:586) and
   completeness `InferType.exists` (:658, `[Params.Extension]`). It has
   **no sorries** — but is tainted: its four `weak'_iff` uses
   (:110, :112, :599, :603) ride on the target sorry.
2. The recon's "`WHRed.weakU_inv` `.extra` is sorried and a prerequisite"
   refers to the **SExpr mirror** (SExpr.lean:3810). The Theory-side
   `.extra` case is *proved* — by consuming `IsDefEqU.weak'_iff`
   (HeadReduction.lean:110-112), i.e. it is tainted, not missing. Same
   pattern at `ParRed.weakN_inv` (ChurchRosser.lean:1173/1175): the
   structural cases are strengthening-free; only the pattern-action
   certificates need the theorem.
3. The Theory-CR circularity is deeper than "ChurchRosser consumes
   weakN_iff": it is definitional and interface-level. `NormalEq` and
   `StructEq` embed full typing/defeq judgments in their constructors
   (ChurchRosser.lean:137-218), so *their* strengthening is judgment
   strengthening; the CR core consumes it inside `NormalEq.trans`'s
   eta-eta case (:896), `hasType_app_bvar0` (:1537), `NormalEq.parRed`
   (:1634, :1699), and the DFC family (:609-812). Moreover the `Params`
   class itself carries `forallE_weakN_inv` and `structEta_weakN_inv` as
   *assumed oracle fields* (ChurchRosser.lean:32-76) which the roadmap
   plans to discharge FROM the 16E co-deliverables at L4L-18A instance
   time — i.e. the plan's dependency direction is weakN_iff → CR, and
   using CR for weakN_iff inverts a planned edge (cf. the 16C′ precedent
   commit "first joint-induction design pass inverts the dependency
   order").
4. The brief's candidate repair for the strong route — use
   `HasType.skips`/`weakN_inv` on the trans midpoint's TYPE — is
   circular: `IsDefEq.skips`/`HasType.skips` are corollaries of
   `weakN_iff` itself (UniqueTyping.lean:180-187, 225-228). And even
   granted, it does not help (§3).
5. `IsDefEq.uniq` and everything before UniqueTyping:171 is
   weakN_iff-free, but consumes the sorried Injectivity endpoints
   (`forallE_inv_stratified` at :43; Injectivity.lean:12/21/34 are all
   sorried 16C′ co-deliverables). "The suite is proved modulo this one
   sorry" is accurate only modulo those three as well; SST likewise
   treats them as available inputs.
6. **No VExpr-side gaps**: `liftN_inj`, `skips_iff_exists`,
   `inst_lift/inst_liftN`, `liftN_inst_hi`, `lift'_inj`,
   `Pattern.RHS.apply_liftN`, `Pattern.matches_lift'` all exist. No O0
   stage is needed.
7. Truth check (statement-repair scan à la
   `registeredStructureHeadInversion`): WF environments acquire defeqs
   only through `VDefVal.toDefEq` (lhs a bare constant; Env.lean:19-57)
   plus registered ι/structEta — no arbitrary defeq axioms — so the
   CR-strength inputs are plausible for every genuinely WF env and no
   falsity landmine was found. The forward direction is believed true as
   stated.
8. Semantic-route wall, sharpened: the shape relation is *observationally
   poor by construction* — `LogRel.bot` and `LR0.DefEq` relate ALL terms
   at bot shape (ShapeLogRel.lean:9921, 10046-10056) — so relatedness can
   never imply `IsDefEqU` for an arbitrary pair. `LE_Interp.weak'_iff`
   (:5893) and `LogRel.LiftEquiv` (:10751) descend the *relation*
   perfectly; the loss is at reflection, which does not exist and cannot
   exist for this relation design. Adequacy extracts judgments only at
   sort/Pi/ctor observation heads (ShapeLogRelAdequacy.lean).

## 3. The wall, precisely

**Obstruction: trans-midpoint re-lift gluing.** Machine-checked witness
(`probe_wall_witness`, clean): for any `Γ ⊢ e : B` and any inserted type
`A₀`,

```
A₀::Γ  ⊢  (fun x : A₀↑ => e↑↑) (bvar 0)  ≡  e↑  :  B↑
```

The midpoint mentions the inserted variable essentially (it is applied via
the `bvar` rule inside `beta`), is not a lift of anything, yet is defeq to
a lift. Consequences, route by route:

- *Induction on the weak derivation*: at `trans`, neither subderivation
  has two lift endpoints. Strengthening the statement to "one lift
  endpoint ⇒ other endpoint defeq to a lift + strengthened equation"
  makes each IH produce a *different* strengthening of the shared
  midpoint (`em`, `em'` with `Γ' ⊢ em↑ ≡ m ≡ em'↑`); gluing them into
  `Γ ⊢ em ≡ em'` is the target theorem applied to `em↑ ≡ em'↑` — a
  derivation that is NOT a subderivation. No structural or size measure
  decreases (`meas` is lift-invariant). Two formalization attempts of
  this shape are pointless; the failure is structural.
- *Induction on `IsDefEqStrong`*: identical. Strong `trans` is
  homogeneous (midpoint typed at the same `A` in the same `Γ'`,
  Strong.lean:21), but typedness does not remove the `bvar 0` occurrence
  from the midpoint TERM: the witness's typed variant has liftable type
  `B↑` and an unliftable term. Substituting the midpoint away needs
  `IsDefEqStrong.instN`'s typed witness `h₀` (Strong.lean:410) — i.e.
  inhabitance of the inserted types, which fails in general (`False`).
  `HasType.skips` on the type is circular per §2.4.
- *Underlying reason there is no elementary proof*: strengthening is
  equivalent to finding a section of the weakening context morphism,
  which exists only when the inserted types are inhabited; every known
  non-elementary proof replaces the section by normalization-strength
  machinery (standardization or a neutral-terms/Kripke model). This
  matches upstream: Injectivity.lean's header ("structural theorems
  which we can't prove :(") and this sorry are the same class of fact.

## 4. Route verdicts

| Route | Verdict | Killing obstruction |
|---|---|---|
| A. Induction on weak `IsDefEq` | dead | trans-midpoint re-lift gluing (§3, witness proved) |
| B. Induction on `IsDefEqStrong` (entry `IsDefEq.strong`, exit `.defeq`) | dead | same wall; typed midpoint still unliftable; `instN` needs inhabitants; `HasType.skips` circular |
| C. Semantic descent (`LE_Interp.weak'_iff` → unlift → reflect) | dead | observation poverty: bot shape relates everything (ShapeLogRel.lean:10046); no reflection for arbitrary pairs, by relation design |
| D. Theory-CR as currently structured | dead (circular) | CR core consumes the suite (ChurchRosser.lean:896, 1537, 1634, 1699, 1173-1175, 609-812); `Params` oracle fields owed BY weakN_iff; module order (`ChurchRosser` imports `UniqueTyping`) |
| E. Witness substitution | partial only | sound and cheap when insertions are inhabited (`IsDefEqU.strengthen_of_witness`, proved); not the theorem |
| F. **SST — de-circularized stratified standardization** | **chosen** | none structural; cost is research-grade re-founding (§5, §6) |
| G. Oracle field (`defeq_weakN_inv` in `Params`) | rejected | violates the 16E exit criterion "no environment oracle on any path" (roadmap); relocates the sorry without closing it |
| H. SExpr-side counterpart first (`SExpr.IsDefEq.weakU_inv`) | rejected | same wall, and SExpr has NO CR core (the `CRDefEq` mirror was deleted at 16B′ precisely because it required one); would duplicate 2,600 Theory lines. Keep `SExprCounterpartDrafts.lean` statement-only |

## 5. The chosen route in one page

Forward proof dataflow (machine-checked as `IsDefEqU.weakN_inv_staged`,
probe Part 3):

```
IsDefEqU Γ' e1↑ e2↑
  → church_rosser:            Γ' ⊢ e1↑ ≫* x,  Γ' ⊢ e2↑ ≫* y,  Γ' ⊢ x ≡ₚ y
  → S-PR (ParRedS.weakN_inv): x = x₀↑, y = y₀↑,  Γ ⊢ e1 ≫* x₀,  Γ ⊢ e2 ≫* y₀
  → S-NE (NormalEq.weakN_inv): Γ ⊢ x₀ ≡ₚ y₀
  → S1 (HasType.weakN_inv_ex): Γ-typings of e1, e2
  → glue by soundness + IsDefEqU.trans.
```

Today every arrow except the last exists but rides on the target sorry.
SST makes the tower weakN_iff-free by proving it as ONE mutual
development, well-founded on **stratified typing depth**
(`HasTypeStratified`, Strong.lean:926 — the exact pattern of
`IsDefEq.uniq` and of the 16C′ `JointStratifiedInversion` bootstrap):

- Strengthening at depth `d` may consume the re-founded CR core at depth
  `d`, which may consume strengthening only at depth `< d` (types live
  one stratification level below their terms: `proofIrrel`'s proposition,
  binder domains, `defeqDF` sort equations).
- The four `Params` oracle fields (`forallE_weakN_inv`,
  `structEta_weakN_inv`, and the two disjointness fields) become
  per-depth *lemmas* of the development instead of instance obligations —
  simplifying the planned L4L-18A live-instance work.
- Existing proof scripts survive nearly verbatim; what changes is the
  induction scaffolding and module order (a new
  `Theory/Typing/Strengthening.lean` layer between `Strong.lean` and a
  slimmed `UniqueTyping.lean`, with `ChurchRosser`/`HeadReduction`
  re-founded above it).

Two genuinely new proof cores (the research content):

1. **S-NE core** — `NormalEq`/`StructEq` strengthening at lift endpoints
   without `weakN_iff`, mutual with `NormalEq.trans` (whose eta-eta case
   :896 consumes it on the same terms — `meas` is lift-invariant, so a
   lexicographic (depth, meas, derivation) measure is the candidate).
   Case analysis is fully mapped: `refl`/`appDF`/`etaL/R` need S1;
   `lamDF`/`forallEDF`/`proofIrrel` need S2 one depth down; `structural`
   needs the structEta-family lemma (the erstwhile oracle field).
2. **Depth-bounded subject reduction** — the CR core at depth `d` must
   keep reducts/normal forms inside a controlled depth. This is the same
   frontier the 16C′ SExpr leaf is currently closing ("vertex retyping
   bounded by the registered-rule stratification certificates"); the
   Theory mirror will need its analogue. Treat 16C′'s resolution as the
   template before attempting.

One open design decision inside SST — **`.extra` certificates**
(S-PR/`WHRed.weakU_inv` residual): the pattern-action equality
certificates are lift-pairs after `apply_liftN` rewriting, but the match
pieces are not structurally smaller than the original endpoints, so
re-strengthening them lacks an obvious measure. Two candidate repairs,
decide before proof text (two-strikes): (a) thread base-context
certificates through the standardization as data (the Theory analogue of
the SExpr note at SExpr.lean:3790-3796, "restate `Action.checked`/`sound`
at `:↑`"); (b) justify a measure through the reduction sequence. (a) is
recommended: it is a rule-packaging change, not a proof search.

## 6. Staged obligations (Lean statements in `plans/probes/probeE-weakn.lean`)

> **2026-08-20 correction (machine-checked; folded from the completion
> plan):** this table's original W2→W3 dependency arrow was INVERTED —
> **W3 uses W2**, not the reverse — and W2's only non-elementary input is
> `InferType.exists`.  W2 and W3 are both now **PROVED**, and strengthened:
> probe E's `hA`/`hF` hypotheses are shown redundant.  Evidence:
> `plans/probes/probeE2-weakn-w2w3.lean`.  The W2/W3 rows below are
> updated accordingly; the SST route, the obstruction records, and the
> W5+W6 residual-risk assessment are unchanged.

| # | Statement (probe name) | Difficulty | Discharged by | Probe status |
|---|---|---|---|---|
| W0 | `probe_wall_witness` | short proof | `IsDefEq.beta` + `inst_lift` | **proved, clean** |
| W1 | `IsDefEqU.strengthen_of_witness` (forward under inhabited insertion) | short proof | `IsDefEq.instN` + `inst_lift` | **proved, clean** |
| W2 | `HasType.weakN_inv_ex` (S1: typing strengthening, existential type) | **PROVED** (2026-08-20) | `InferType.exists` — its only non-elementary input (arrow corrected: W2 does **not** use W3) | proved + strengthened (`probeE2-weakn-w2w3.lean`) |
| W3 | `IsDefEqU.weakN_inv_sort` / `weakN_inv_forallE` (S2-obs at heads) | **PROVED** (2026-08-20) | W2 (dependency arrow corrected — W3 uses W2, not the reverse) | proved + strengthened (`probeE2-weakn-w2w3.lean`) |
| W4 | `ParRedS.weakN_inv` (S-PR) | real work → research-grade pending the `.extra` decision (§5) | existing `ParRed.weakN_inv` structural cases + certificate re-packaging | tainted-proved (iteration); `.extra` residual open |
| W5 | `NormalEq.weakN_inv` (S-NE) | **research-grade core** | new mutual induction (§5.1) | tainted-proved via `weakN_inv_DFC` (stand-in); clean re-proof owed |
| W6 | CR-core re-founding per depth (`NormalEq.trans`, `church_rosser`, `ParRedS.standard`; no new statements) | **research-grade core** | existing scripts + depth scaffolding + §5.2 | n/a (refactor) |
| W7 | `IsDefEqU.weakN_inv_staged` (assembly) | consumption | W2+W4+W5 + `church_rosser` | **tainted-proved** (dataflow certificate) |
| W8 | `IsDefEqU.weakN_inv_probe` (= O1, bare `VEnv.WF` form) | outside this leaf | W7 at `[Params][Params.Extension]` + generic instance construction (shared debt with `sort_inv`, roadmap L4L-16E "closes from the instances") | type-checked, sorry |

Measured closures (probe run 2026-08-15, `lake env lean`, exit 0, first
attempt): `probe_wall_witness` and `IsDefEqU.strengthen_of_witness` at
`[propext, Quot.sound]` — no `sorryAx`; `IsDefEqU.weakN_inv_staged` at
`[propext, sorryAx, Classical.choice, Quot.sound]`; the only sorry
warnings are the four intended heads (W2, W3a, W3b, W8). `ParRedS.weakN_inv`
and `NormalEq.weakN_inv` elaborate fully (tainted through their inputs as
documented).

Inputs assumed available (not counted above): Injectivity.lean's three
sorried endpoints (16C′ co-deliverables), the two `NormalEq.parRed`
`.extra` holes (ChurchRosser.lean:1759/1778, L4L-18A), and the generic
`Params`/`Params.Extension` instance (L4L-18A′/D-series).

## 7. Execution order and sequencing recommendation

**Can start now, before the 16C′ leaf closes** (all against stable
sorried inputs):
1. The `.extra` certificate design decision (§5, option (a) recommended) —
   it also unblocks the SExpr mirror's :3810 sorry, a 16E pre-promotion
   item.
2. The SST module-order plan: name the new layer, enumerate the exact
   theorem moves out of `ChurchRosser`/`HeadReduction`, and the
   depth-indexed statements of `NormalEq.trans`/`church_rosser`.
   (Pure planning; no proof text.)
3. W5's case skeleton against the sorried W2/W3 heads (they are frozen
   in the probe).

**Waits for 16C′ leaf:** taint removal on Injectivity endpoints; the
depth-bounded subject-reduction template (§5.2).

**Waits for / merges with L4L-18A:** the two parRed `.extra` holes; the
live and generic instances; W8.

**Roadmap consequence (the actionable verdict):** `weakN_iff` forward
should move off the 16E gate. 16E lands: this design, the probe (W0/W1
proved, all heads pinned), and the re-scoped promise that the four
`Params` inversion fields will be *proved* by SST rather than supplied at
instance time. The sorry stays allowlisted through 16E and closes in an
"18A′-SST" slice. The alternative — holding 16E open for 3–6 weeks of
research-grade work whose prerequisites (18A extra holes, generic
instances) are themselves later milestones — inverts the ladder's
dependency order twice.

## 8. Effort estimate

- W0/W1: done (this pass).
- W2+W3: ~3–5 days inside SST once the scaffolding stands.
- W4: 2–4 days if design (a) is taken; unknown under (b).
- W5+W6: the cores — 2–4 weeks combined, high variance; the two named
  risks are the (depth, meas, derivation) termination argument for
  S-NE×trans and the Theory analogue of 16C′'s depth-bounded retyping.
- W7: hours (already written).
- W8: not this leaf's budget (shared instance-generalization debt).

Total for the forward proof proper: **3–6 focused weeks**, research-grade,
after its 16C′/18A inputs; plus the shared instance debt for the bare-WF
form. If a cheaper proof exists, it is not visible from the current
codebase's vocabulary — every elementary route has a machine-checked or
line-cited obstruction above.
