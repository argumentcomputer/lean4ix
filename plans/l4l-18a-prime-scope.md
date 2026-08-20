# L4L-18A′ scope — Church–Rosser, standardization, and the normalization question

> **2026-08-20:** the ladder (§5/§6) as a *route to the 16C′ leaf* is
> closed: `plans/probes/probeR13-loop.lean` proved `LRS.ParRedSDefeq` ⟺
> `LRS.PiPathInv` — interderivable, so the CR ladder cannot discharge the
> leaf; it is a downstream **consumer** of it. The rungs remain the plan of
> record for L4L-18A′'s own deliverables (the CR `.extra` cases,
> standardization transport), and the sort-restriction narrowing
> (R12′/`PiPathInv.of_crLadder_R12`) provably does not dodge the hard case.

Date: 2026-08-15

Commissioned by the 2026-08-15 16C′ verdict, `plans/roadmap.md:735-741`:

> The irreducible factor is `PiHeadNorm` = `TypeWHNFEx` (a well-typed type
> HAS a weak-head normal form) + `PiHeadStable`. That is an existence claim,
> so **L4L-18A′ is now a hard dependency of 16C′ and must be scoped to
> include normalization, not merely Church–Rosser** — CR alone buys only
> `PiEdgeInv`, one of the two factors already recoverable. Scoping pass:
> `plans/l4l-18a-prime-scope.md`.

Status: analysis complete; recommendation in §9. Companion probe
`plans/probes/probeCR-scope.lean` — green, **16 banked results, all at
`[propext, Quot.sound]`**, no `sorryAx`, no `Classical.choice`. The probe
imports `Lean4Lean.Experimental.ShapeLogRel` only, so its independence from
adequacy is structural rather than audited. No `Experimental/` or `Theory/`
file was edited by this pass.

---

## 0. TL;DR

1. **Strike normalization from L4L-18A′.** `TypeWHNFEx` is not needed. The
   recorded decomposition `PiHeadNorm = TypeWHNFEx ∧ PiHeadStable`
   (probeP:216) is *sufficient*, not necessary, and it is the expensive
   branch. `PiHeadNorm` follows instead from Church–Rosser plus the
   **standardization theorem**, and Theory already proves standardization in
   full — `VEnv.ParRedS.standard`, `HeadReduction.lean:489`, after Kashima
   (2000). Machine-checked: `LRS.PiHeadNorm.of_crLadder`.
2. **Theory already has the target statement.**
   `VEnv.IsDefEq.reduce_forallE` (`HeadReduction.lean:512`) *is*
   `LRS.PiHeadNorm`, transposed to `VExpr`, and it is proved by exactly the
   route in (1). Nobody in `plans/` had connected these; §3 does.
3. **The real wall is sort inversion, not normalization.** `reduce_forallE`
   consumes `IsDefEqU.sort_forallE_inv` and `IsDefEqU.sort_inv`
   (`HeadReduction.lean:523`, `:527`; both `sorry` at `Injectivity.lean:34`,
   `:11`). The probe localises this exactly: `LRS.NormalEqPiInvL` is
   structural in six of `NormalEq`'s eight constructors, and the two
   survivors, `etaL` and `proofIrrel`, cost precisely two sort facts
   (`LRS.PiNotFunTyped`, `LRS.PiNotProof`).
4. **That cost is unavoidable, by any route.** `LRS.PiHeadNorm` entails
   `LRS.SortForallEDisj` in four lines, with no `PiHeadStable` detour
   (`LRS.SortForallEDisj.of_piHeadNorm`). So **L4L-18A′ can never close the
   16C′ leaf on its own**, whatever it is scoped to include.
5. **`TypeWHNFEx` on its own unblocks nothing.** Its only consumer is
   `PiHeadNorm.of_parts`, which also demands `PiHeadStable` — and
   `PiHeadStable` already entails `SortForallEDisj`
   (`LRS.SortForallEDisj.of_piHeadStable`). The recorded split therefore
   divides the leaf's cost into a normalization half that is **avoidable**
   and a sort half that is **not**.
6. **Net re-scope.** 18A′ = confluence + standardization + the two `.extra`
   overlaps + the live `Params`/`Params.Extension` instances, delivering
   `SubjectRedS`, `PiEdgeInv` and `PiHeadNorm` *conditional on a named
   four-field shape-disjointness interface*. A new micro-milestone (§9,
   "16C″") owns that interface. **Estimated 8–14 serial developer-weeks, or
   20–34 staged agent-sessions across four independent tracks.**

---

## 1. The `TypeWHNFEx` recommendation

**Recommendation: do not prove `TypeWHNFEx`. Remove it from the critical
path.** None of the three routes the commission offered is the answer; the
answer is a fourth, (d) *avoid the decomposition that introduces it*.

### 1.1 Why it is avoidable

`LRS.PiHeadNorm` asks: given `Γ ⊢ X ≡ Y : .sort s` and `Γ ⊢ X ⤳* Πab`,
show `Y ⤳*` some Pi. `PiHeadNorm.of_parts` reaches this by first
manufacturing *some* weak-head normal form of `Y` (`TypeWHNFEx`) and then
constraining its shape (`PiHeadStable`). But the Pi that `Y` must reach can
be *transported* rather than manufactured:

| step | instrument |
|---|---|
| `X ⤳* Πab` ⟹ `X ≫* Πab` | `WHRedS.parRedS`, SExpr:4252 (proved) |
| `X ≡ Y` ⟹ `X ≫* X′`, `Y ≫* Y′`, `X′ ≡ₚ Y′` | Church–Rosser |
| a `≫`-reduct of a Pi is a Pi | `ParRedS.forallE_inv` — **proved in probe** |
| a `NormalEq` opposite a Pi has a Pi on the other side | `LRS.NormalEqPiInvL` (§4) |
| `Y ≫* ` a Pi ⟹ `Y ⤳* ` a Pi | **standardization** |

No step asserts that a normal form *exists*; the last step converts a
normal form that has already been produced by transport into a weak-head
one. Machine-checked as `LRS.ReduceForallE.of_ladder` and
`LRS.PiHeadNorm.of_crLadder`, both `[propext, Quot.sound]`.

This is not a new idea — it is precisely how Theory discharges the same
statement at `HeadReduction.lean:511-530`. The probe's proof is that proof,
with the two sort appeals factored out instead of spent inline.

### 1.2 Verdicts on the three offered routes

| route | verdict | reason |
|---|---|---|
| (a) an independent, smaller logical relation (a reducibility predicate not carrying adequacy) | **rejected** | This is a normalization proof for the full theory — universes, eta, proof irrelevance, *and* an abstract class of registered rewrite rules. `Params` (SExpr:26, ChurchRosser:18) imposes no termination, well-foundedness or orthogonality condition on `Pat`; `Params.Extension.join` requires only typed *joinability*. So the statement is not even determined by the interface: it would first need a new `Params` field constraining the rewrite system, and then a research-grade formalization on top. |
| (b) full CR/standardization machinery | **does not deliver it** | Confluence and standardization are both *conditional* — they relate reduction sequences that exist. Neither produces one. Theory's `ParRedS.standard` needs a `≫*` sequence as input. |
| (c) cheaper for types specifically | **no** | The claim is about `X` with `Γ ⊢ X : .sort s`, but nothing restricts the *shape* of such an `X`: it can be any application whose head is a type-valued constant. Deciding whether it has a weak-head normal form is deciding whether that application's iota/registered chain terminates. Types are not a syntactically simpler class here. |
| (d) **do not prove it** | **recommended** | §1.1. |

### 1.3 The reason the existing logical relation cannot be reused

The commission notes that using `LogRel`/`LR` for `TypeWHNFEx` is circular.
That is right, and the mechanism is worth recording. `LRS.ValTyPi2`
(SLR:10221) *does* carry a weak-head-normal-form existence conjunct —
`Γ ⊢ M₁ ⤳* .forallE B₁ F₁` — but only for a type already known to inhabit
a `forallE` `WShape`. Getting an arbitrary well-typed type into the
relation is exactly adequacy, which is what the leaf is trying to prove. So
the relation supplies the existence claim only *after* the thing it is
being used to establish.

### 1.4 Consequence for the three obligations flagged mid-pass

The coordinator reports that `LR.FixedHeadConvertStep` unfolds to
`PiHeadNorm`, and that `∀ depth, LR.SelfAdequateDefeqStepAt` is also blocked
on `PiPathInv`. Both are covered by §1.1 **provided** they unfold to
`PiHeadNorm` and not to the strictly stronger conjunction
`TypeWHNFEx ∧ PiHeadStable`. Those are different propositions: the
conjunction implies `PiHeadNorm`, not conversely, and this pass supplies a
proof of the former only. **Action for the ADQ owner:** check which of the
two `FixedHeadConvertStep` actually needs. If it needs the conjunction, ask
whether its consumer can be weakened to `PiHeadNorm` — every use this pass
inspected can be.

---

## 2. Corrections to the recorded analysis

| record | correction |
|---|---|
| `SExpr.lean:4371` — "nothing on the L4L-16 gate path consumes it" (`CRDefEq.trans`) | **False.** `LRS.PiPathInv.of_crLadder` (probe, Part 4) consumes `LRS.CRComplete`, whose Theory witness `IsDefEq.church_rosser` is proved from `CRDefEq.trans`; and `LRS.PiPathInv` is the sole residual of the 16C′ leaf. Recorded as the type-checked `LRS.crDefEq_is_on_the_gate_path`. |
| `roadmap.md:735-741`, `:828` — 18A′ "must be scoped to include normalization" | **Withdraw.** §1. Normalization is neither necessary nor obtainable; standardization is necessary and is already proved. |
| `roadmap.md:735` — "CR alone buys only `PiEdgeInv`, one of the two factors already recoverable" | **Understated.** CR + standardization buys `PiHeadNorm` as well, i.e. all three factors — modulo shape disjointness (§4). |
| `plans/l4l-16-weakn-design.md:36-45` — HeadReduction.lean "has **no sorries** — but is tainted: its four `weak'_iff` uses ride on the target sorry" | **Correct but incomplete.** It is tainted a second, independent way: `reduce_sort` (:497, :502, :506) and `reduce_forallE` (:523, :527) consume `Injectivity.lean`'s `sort_inv` and `sort_forallE_inv`, and everything downstream of `church_rosser` inherits ChurchRosser's two `sorry`s. |
| probeP:41 — `LRS.PiHeadNorm` "contains `IsDefEqU.sort_forallE_inv` … via `LRS.SortForallEDisj.of_piHeadStable`" | **Strengthened.** It contains it *directly*, with no `PiHeadStable` in between: `LRS.SortForallEDisj.of_piHeadNorm`. The obligation is on the leaf, not on the decomposition. |

---

## 3. Existing-machinery inventory

### 3.1 `Lean4Lean/Theory/Typing/ChurchRosser.lean` — 1999 lines, **2 `sorry`**

The complete Church–Rosser development on `VExpr`, and it is nearly done.

Proved: `StructEq` (:137) and its full lemma set; `NormalEq` (:184) with
`defeq`/`symm`/`weakN`/`instN`/`defeqDFC`/`weakN_inv_DFC`/`trans` (:860);
`ParRed` (:943), `CParRed` (:964), `ParRed.instN` (:1002), `ParRed.defeq`
(:1031), `ParRed.hasType` (:1058), `ParRed.weakN_inv` (:1129),
`CParRed.exists` (:1204), **`ParRed.triangle` (:1253)** — 160 lines, the
complete-development diamond, `.extra` case included — `ParRed.church_rosser`
(:1413), `ParRedS` + congruence/substitution lemmas (:1421-1493),
`ParRedExt` and `parRed_beta` (:1495-1717), `NormalEq.parRedS` (:1854),
`ParRedS.church_rosser` (:1870), `CRDefEq.trans` (:1907),
`IsDefEq.church_rosser` (:1952).

**Sorried:** exactly two, both inside `VEnv.NormalEq.parRed` (:1747):

* `:1759` — `constDF` meets `ParRed.extra`;
* `:1778` — `appDF` meets `ParRed.extra`.

These are the historical L4L-18A obligations, and they are the only `sorry`
tokens in the file (single allowlist row, `Audit/SorryFrontier.lean:175`).
The template for both already exists in the same file: `ParRed.triangle`'s
own `.extra` case (:1253-1412), and `StRed.triangle`'s (`HeadReduction.lean:441-479`).

**Assumed, not sorried** — and this matters for scoping:

* `class Params` (:18) carries four *oracle* fields beyond the pattern
  combinatorics: `structEta_weakN_inv` (:34), **`structEta_sort_disjoint`
  (:54)**, **`structEta_forallE_disjoint` (:61)**, `forallE_weakN_inv`
  (:71). The two bolded ones are shape-disjointness facts of exactly the
  kind §4 identifies as the wall.
* `class Params.Extension` (:1930) — the registered-equation join oracle,
  consumed by `IsDefEq.church_rosser`. The roadmap already assigns its live
  instance to 18A′ (`roadmap.md:859-863`); L4L-18B (complete, 2026-08-12)
  built its proof-carrying interface.
* `Params.henv : env.WF`, strictly stronger than SExpr's
  `Params.henv : env.Ordered` (`VEnv.WF.ordered`, `EnvLemmas.lean:88`, is
  one-way). An instantiation gap — see §7.

### 3.2 `Lean4Lean/Theory/Typing/HeadReduction.lean` — 721 lines, **0 `sorry`**, tainted

The single most under-used file in the repository for this problem.

* `WHRed` (:59), `WHNF` (:141), `WHRedS` (:225) — the same relations SExpr
  re-declares at SExpr:3762/3811/4030.
* **`StRed` (:302)** — standard reduction, and its inversion lemmas
  `sort_l` (:322), `lam_l` (:326), **`forallE_l` (:332)**.
* **`StRed.triangle` (:418)** — 62 lines including the full `.extra` case.
* **`ParRedS.standard` (:489)** — *the standardization theorem*, three lines
  from `triangleS`. Header (:7-9) cites Kashima (2000). **This is the rung
  that replaces normalization**, and it is already done.
* **`IsDefEq.reduce_sort` (:493)** and **`IsDefEq.reduce_forallE` (:512)** —
  head normalization of a definitional equality at the two rigid type heads.
  `reduce_forallE` *is* `LRS.PiHeadNorm`.

Taint, three independent sources:

1. via `IsDefEq.church_rosser` — ChurchRosser's two `sorry`s;
2. **`sort_forallE_inv` at :502 and :523, `sort_inv` at :506 and :527** —
   `Injectivity.lean:34` and `:11`, both `sorry`. This is §4's wall and was
   not previously recorded;
3. four `weak'_iff` uses (:110, :112, :599, :603) riding on
   `UniqueTyping.lean:174` (`sorry`), per `l4l-16-weakn-design.md:36-45`.

### 3.3 `Lean4Lean/Theory/Typing/Injectivity.lean` — 34 lines, **3 `sorry`**

Module docstring: "A bunch of important structural theorems which we can't
prove :(". `IsDefEqU.sort_inv` (:11), `IsDefEqU.forallE_inv_stratified`
(:16), `IsDefEqU.sort_forallE_inv` (:34). `IsDefEqU.forallE_inv` (:23) is
*proved* from `forallE_inv_stratified`. `sort_inv` is the declared L4L-16
gate theorem (`plans/l4l-16-sort-inversion-decision.md:15-22`).

### 3.4 `Lean4Lean/Experimental/SExpr.lean` — the partial port

| declaration | line | ported | missing |
|---|---|---|---|
| `ParRed` | 4079 | `rfl`, `weak'` | `instN`, `defeq`, `hasType`, `defeqDFC`, `apply_pat`, `weakN_inv`, `CParRed`, `triangle`, `church_rosser` |
| `ParRedS` | 4111 | `weak'` | `hasType`, `defeq`, `app`/`lam`/`forallE`, `inst`, `church_rosser`, `standard` |
| `NormalEq` | 4274 | `defeqDFC`, `defeq`, `symm`, `weak'` | `instN`, `trans`, `parRed`, `parRedS`, and the whole `structural`/`StructEq` constructor, which SExpr's `NormalEq` **does not have** |
| `CRDefEq` | 4352 | `normalEq`, `refl`, `defeq`, `symm`, `defeqDF`, `weak'` | **`trans`** (deliberately absent, :4371) |
| `StRed` | — | — | **entirely absent** |

SExpr's own four `sorry`s: `WHRed.weakU_inv`'s `.extra` case (:3810),
**`WHRedS.defeq` (:4033)**, `InferType.hasType` (:4136),
`InferTypeS.hasType` (:4202). The probe shows the second is not separate
work: `LRS.SubjectRedS.of_parRedSDefeq` derives it from `ParRedS.defeq`.

### 3.5 The parked Experimental modules — both dead

* `Lean4Lean/Experimental/NormalEq.lean` — 512 lines, **0 `sorry`**, header
  line 4: "TODO: remove, this is now part of ChurchRosser.lean". Superseded.
* `Lean4Lean/Experimental/ParallelReduction.lean` — 11 lines, **0 `sorry`**,
  an import-compatible stub; its docstring says the maintained CR
  development supersedes it and it has no consumers.

Neither contains anything 18A′ needs. **Recommend deleting both** at the
next cleanup boundary; they cost audit surface and mislead the map.

---

## 4. The wall, precisely

Not normalization. **Head-shape disjointness**, of which sort inversion is
the headline instance.

### 4.1 Where it bites

`LRS.NormalEqPiInvL` — invert a `NormalEq` whose right endpoint is a Pi —
is structural in six of `NormalEq`'s eight constructors: `appDF`, `lamDF`
and `etaR` put a non-Pi node on the right and die by `cases`; `refl` and
`forallEDF` put a Pi on the left and succeed; `defeqDF` recurses. Machine-
checked as `LRS.NormalEqPiInvL.of_parts`. The two survivors are:

* **`etaL`**, whose right endpoint is an arbitrary `e'` carrying
  `Γ ⊢ e' : .forallE A B`. Refuted exactly by "a Pi is not typed at a Pi" —
  `LRS.PiNotFunTyped`.
* **`proofIrrel`**, whose right endpoint is an arbitrary `h'` carrying
  `Γ ⊢ h' : p` with `Γ ⊢ p : .sort .zero`. Refuted exactly by "a Pi is not
  a proof of a proposition" — `LRS.PiNotProof`.

Theory spends `sort_forallE_inv` and `sort_inv` on precisely these two
(`HeadReduction.lean:523`, `:527`).

### 4.2 Why confluence cannot supply it

Confluence sees through everything that is a *reduction*. `proofIrrel` is
not one: it is a congruence with no operational content, present in both
`IsDefEq` (SExpr:1276) and `NormalEq` (SExpr:4288). Chasing the residue
does not descend. Unfolding the obligation "no sort is a proof of a
proposition" via unique typing produces `Γ ⊢ .sort v : .sort .zero` for a
successor level `v`; unfolding *that* the same way reproduces a statement of
the same form at a level determined by the previous one, with no decreasing
measure — the regress has a fixpoint, not a base case. Refuting it requires
a model in which `Prop` is not a universe containing `Type 0`. That is what
`plans/l4l-16-sort-inversion-decision.md` already decided (route: shape
logical relation), and it is L4L-16's gate theorem, not 18A′'s.

### 4.3 Why it is unavoidable, not an artifact of this route

`LRS.SortForallEDisj.of_piHeadNorm`, four lines, machine-checked: apply
`PiHeadNorm` to the edge `Γ ⊢ .forallE A B ≡ .sort u : .sort s` with the
reflexive reduction on the left; `.sort u` is already a weak-head normal
form (`WHNF.sort`), so its only `⤳*`-reduct is itself, and the conclusion
demands it be a Pi.

So **any** proof of `LRS.PiHeadNorm`, by any route, proves sort/Pi
disjointness on the way. `PiHeadNorm` is a factor of `LRS.PiPathInv`
(probeP:303), which is the 16C′ leaf. Therefore **L4L-18A′ can never close
the 16C′ leaf on its own.** That verdict is independent of how 18A′ is
scoped and is the single most sequencing-relevant fact in this pass.

### 4.4 The four shape facts 18A′ consumes and does not produce

| fact | where consumed | current status |
|---|---|---|
| `IsDefEqU.sort_inv` | HeadReduction:506, :527 | `Injectivity.lean:11`, `sorry`; L4L-16 gate theorem |
| `IsDefEqU.sort_forallE_inv` | HeadReduction:502, :523 | `Injectivity.lean:34`, `sorry` |
| `Params.structEta_sort_disjoint` | ChurchRosser:54, used at HeadReduction:503 | oracle field of `Params` |
| `Params.structEta_forallE_disjoint` | ChurchRosser:61, used at HeadReduction:524 | oracle field of `Params` |

All four say the same kind of thing: two rigid head shapes are not
definitionally equal. All four are what a shape logical relation delivers.
Collecting them into one named class is the interface 18A′ should be built
against — see §9.

---

## 5. The staged ladder

Every rung is a Lean statement. Probe-verified rungs give their probe name;
the rest are stated here for the implementer and are **not** machine-checked
by this pass. "Serial after" gives the dependency.

| # | rung | statement / probe name | difficulty | discharged by | serial after | parallel? |
|---|---|---|---|---|---|---|
| R0 | `ParRed`/`ParRedS` inversion at Pi and sort | `ParRed.forallE_inv`, `ParRed.sort_shape_inv`, `ParRedS.forallE_inv`, `ParRedS.sort_shape_inv` | **done** | this probe, `[propext, Quot.sound]` | — | ✔ |
| R1 | Theory `Params` instance from SExpr `Params` | needs `env.WF` (SExpr has `Ordered` only) + the four oracle fields | **real work**; two fields are §4.4 semantics | partly `Params.Semantic` (SExpr:1964); disjointness fields → 16C″ | — | ✔ NOW |
| R2 | weak-head reduction reflection, `mk`-ward | `VEnv.WHRedS (Γ.map reify) e.reify P → ∃ P', P = P'.reify ∧ WHRedS Γ e P'` | **real work**, mechanical | pattern bridges exist: `Pattern.MatchesS.reify` (SExpr:965), `Pattern.RHS.mk_apply_reify` (SExpr:1028), `mk_reify` (SExpr:299) | — | ✔ NOW |
| R3 | the two `.extra` overlap cases | `VEnv.NormalEq.parRed`, ChurchRosser:1759, :1778 | **real work** (the historical 18A) | template: `ParRed.triangle`'s `.extra` case (ChurchRosser:1253-1412), `StRed.triangle`'s (HeadReduction:441-479) | — | ✔ NOW |
| R4 | live `Params.Extension.join` | ChurchRosser:1930 | **real work**, overlaps L4L-16F "live instance" | L4L-18B interface (complete) | — | ✔ NOW |
| R5 | `LRS.CRComplete` | `IsDefEq.church_rosser` transported | **consumption** | R1+R2+R3+R4 | R1–R4 | serial |
| R6 | `LRS.PiStandard` | `ParRedS.standard` ∘ `StRed.forallE_l`, transported | **consumption** — already proved upstream | R1+R2 | R1,R2 | serial |
| R7 | `LRS.ParRedSDefeq`, hence `LRS.SubjectRedS` | `ParRedS.defeq` (ChurchRosser:1431) transported; `LRS.SubjectRedS.of_parRedSDefeq` **proved in probe** | **consumption** | R1+R2 | R1,R2 | serial |
| R8 | `LRS.PiNotFunTyped`, `LRS.PiNotProof` | §4.4 | **research-grade — NOT 18A′** | 16C″ (§9) | — | ✔ separate track |
| R9 | `LRS.NormalEqPiInvL` | `LRS.NormalEqPiInvL.of_parts` — **proved in probe** | **consumption** | R8 | R8 | serial |
| R10 | `LRS.ReduceForallE`, `LRS.PiHeadNorm` | `LRS.ReduceForallE.of_ladder`, `LRS.PiHeadNorm.of_crLadder` — **both proved in probe** | **consumption** | R5+R6+R7+R9 | R5,R6,R7,R9 | serial |
| R11 | `LRS.PiEdgeInv` from CR | `NormalEq` Pi/Pi component extraction (the `forallEDF` case yields component `NormalEq`s) + `ParRedS.defeq` on components + path composition | **short proof** — *sketch only, not machine-checked* | R5+R7+R9 | R5,R7,R9 | serial |
| R12 | `LRS.PiPathInv` — the 16C′ leaf | `LRS.PiPathInv.of_crLadder` — **proved in probe** from R7+R5+R6+R8+R11 | **consumption** | R10+R11 | R10,R11 | serial |

**Attackable now, in parallel: R1, R2, R3, R4** — four independent tracks
with no dependency on each other or on the sort facts. **R8 is a fifth
track and belongs to a different milestone.** Everything from R5 down is
consumption or short glue: once R1–R4 land, R5–R7 and R9–R12 are days, not
weeks, and eight of the twelve rungs are already machine-checked here.

**What `TypeWHNFEx` alone would unblock: nothing on this ladder.** It
appears in no rung. Its only route to a consumer is `PiHeadNorm.of_parts`,
which also demands `PiHeadStable` — R8-strength semantics. See
`LRS.typeWHNFEx_not_needed` in the probe.

---

## 6. Implementation route: transport, do not port

Two ways to get the Theory development onto the SExpr statement language.

**Route B — port.** Re-prove ChurchRosser + HeadReduction on `SExpr`.
Roughly 1600 lines to port (ChurchRosser:943-1912 ≈ 970; the `NormalEq`
lemma block ≈ 430; HeadReduction's `StRed`+`triangle`+`standard` ≈ 230),
*plus* adding the `structural`/`StructEq` constructor that SExpr's
`NormalEq` lacks entirely (≈ 300). **Not recommended.**

**Route A — transport via `reify`.** SExpr already has the bridge:
`IsDefEq.reify` (SExpr:2876), `Ctx.WF.reify` (:2986), `mk_reify` (:299),
`Pattern.MatchesS.reify` (:965), `Pattern.RHS.mk_apply_reify` (:1028), and
`IsDefEqStrong.mkS` (:2091) in the other direction. What is missing is only
R1 (the `Params` instance) and R2 (reflecting `WHRedS` back through `mk`,
using `mk ∘ reify = id`). **Recommended**; it is what makes R5–R7 pure
consumption and is why the ladder is as short as it is.

Note that SExpr does *not* currently import `ChurchRosser`/`HeadReduction`
(it stops at `Lemmas`, `Pattern`, `Strong`), so Route A implies a new import
edge `SExpr.lean → HeadReduction.lean`. **Verified acyclic**: no file under
`Lean4Lean/Theory/` imports anything under `Lean4Lean/Experimental/`, and
`ChurchRosser` imports only `Pattern`, `Strong`, `UniqueTyping`. The edge
does, however, pull ChurchRosser's two `sorry`s and `Injectivity`'s three
into SExpr's transitive closure — so the audit frontier must be re-measured
when it lands, and `Audit/SorryFrontier.lean` will need the SExpr-side rows
re-checked.

---

## 7. Effort estimate

### 7.1 Serial developer-weeks: **8–14**

| rung | weeks | driver |
|---|---|---|
| R1 `Params` instance | 1–2 | the `Ordered`→`WF` upgrade, plus wiring the four oracle fields to their producers |
| R2 `WHRedS` reflection | 1–2 | four constructors; only `extra` is non-trivial, and its bridges exist |
| R3 the two `.extra` overlaps | 2–4 | the genuine unknown; two working templates exist in-repo |
| R4 live `Params.Extension.join` | 2–4 | the generated-environment bridge; overlaps L4L-16F |
| R5–R7, R9–R12 | 1.5–2 | consumption and glue; 8 of 12 rungs already checked |

Assumptions driving this number: one developer, no parallel tracks; R3
behaves like the already-finished `ParRed.triangle`/`StRed.triangle`
`.extra` cases, i.e. the existing pattern non-overlap interface suffices and
**no new `Params` field is required**. If R3 needs a new field, add 2–4
weeks — and check whether the new field is another §4.4 semantic oracle, in
which case it belongs to 16C″ and this estimate is the wrong shape.
**Excludes R8 entirely.**

### 7.2 Staged parallel agent-sessions: **20–34**

Calibrated against the repository's one published pair — `weakN_iff`, 2.5–5
serial weeks ↔ 8–11 staged sessions (`l4l-16-weakn-design.md:268-282`) —
which is 2.2–3.2 sessions per serial week.

Assumptions driving this number, and they differ from §7.1's: R1/R2/R3/R4
run as four concurrent tracks from day one (they share no file and no
lemma); each session is scoped to one named Lean statement with its own
probe; and the repeated observation that a probe-first session lands
200–400 lines. Wall-clock is then set by the longest track, R3 or R4, at
roughly 6–13 sessions each — so **the 5–10× advantage here is in wall-clock
and re-work, not in total session count**, and it is realised only if R1–R4
are genuinely dispatched in parallel. Dispatching them serially forfeits it
and reproduces §7.1.

---

## 8. Sequencing recommendation

### 8.3 Re-cut 16C′ to close conditionally — **yes, do it**

The commission asks honestly whether closing 16C′ with the leaf conditional
on a named CR-supplied Prop is worth doing when the sorry moves rather than
disappears. It is, for four reasons, and the cost is nearly zero:

1. **It is nearly free.** `LRS.PiPathInv` is *already* threaded as an
   explicit hypothesis, not embedded in an induction —
   `SpineWF.result_path (piInv : LRS.PiPathInv)` (SLR:11348),
   `WHRedS.defeq_of_piPathInv` (SLR:11464),
   `LRS.constSpineTypeUniqPath` (SLR:11373). Closing conditionally is
   plumbing, not restructuring.
2. **It collapses three obligations into one import.** `PiPathInv` now
   gates `MajorChainAnchorStep`, `LR.FixedHeadConvertStep` and
   `∀ depth, LR.SelfAdequateDefeqStepAt`. One named interface serves all
   three.
3. **It makes the residual auditable.** A single named `Prop` in
   `SorryFrontier` beats a structural gap inside an induction.
4. **It unblocks the rest of the ladder.** 16D/16E can proceed to green
   against the interface.

The one thing to get right: make the named Prop the **shape-disjointness
class of §4.4**, not `PiPathInv` itself. `PiPathInv` is 18A′'s *output*;
the disjointness class is the genuine leaf, it is what 16C″ owes, and
conditioning on it keeps the two milestones' interfaces honest.

> **2026-08-20:** §8.3 was adopted as roadmap Decision (A) on 2026-08-15 —
> but with the conditional Prop named `LRS.PiPathInv`, not the
> shape-disjointness class this section insists on. Recorded deviation,
> defensible: the disjointness facts landed independently (three from
> `LE_Interp.sound`, `sortInv` at rung 0) before the cut, leaving
> `PiPathInv` the genuine leaf.

### 8.4 What 16C′ banks meanwhile

Everything already landed stays banked and is unaffected by this pass: the
depth tower (`contextualAdequacyAtDepth_of_iotaSteps`),
`SelfAdequateConstStep`, `CoherentFixedHeadStep`, the chain-wall repair
(`to_core_path`, `CtorRetype`, `CtorSpineTypeUniqPath`, SLR:11112-11147),
and `MajorChainAnchorStep`. Still bankable without any 18A′ input:
`CoherentIotaLeafStep`, `ConstDefnLocalStep`, the δ-definition residual
(`ConstDefnDeepStepR`/`ConstDefnDeepInstStep`),
`∀ depth, FixedHeadTypeValidStep`, and `FixedHeadTerminalRetarget`.

### 8.5 Roadmap edits this implies

> **2026-08-20:** the roadmap-edit bullets below were executed — the
> roadmap rewrite of this date handles them.

* Retitle the ladder entry `L4L-18A` → `L4L-18A′` and rewrite `:824-836`
  per §0 and §2 (strike normalization; add standardization as *already
  proved*; correct the "CR alone buys only `PiEdgeInv`" clause).
* Add `L4L-16C″` before 16C′ in the ladder.
* `plans/roadmap.md:741` and `:833` cite this file; both now resolve.
* Tracked-file bookkeeping: `.gitignore` ignores `/plans/*` with per-file
  `!` negations, and `roadmap.md:9-17` lists the tracked set by name. If
  this doc is meant to travel with checkpoints, both need an entry. **Not
  done by this pass** — outside the assigned territory.

---

## 9. Appendix — probe evidence

Command (run from the repository root):

```
lake env lean plans/probes/probeCR-scope.lean
```

Full output, exit 0:

```
'Lean4Lean.SExpr.LRS.SortForallEDisj.of_piHeadNorm' depends on axioms: [propext, Quot.sound]
'Lean4Lean.SExpr.LRS.SortForallEDisj.of_piHeadStable' depends on axioms: [propext, Quot.sound]
'Lean4Lean.SExpr.LRS.typeWHNFEx_not_needed' depends on axioms: [propext, Quot.sound]
'Lean4Lean.SExpr.ParRed.forallE_inv' depends on axioms: [propext, Quot.sound]
'Lean4Lean.SExpr.ParRed.sort_shape_inv' depends on axioms: [propext, Quot.sound]
'Lean4Lean.SExpr.ParRedS.forallE_inv' depends on axioms: [propext, Quot.sound]
'Lean4Lean.SExpr.ParRedS.sort_shape_inv' depends on axioms: [propext, Quot.sound]
'Lean4Lean.SExpr.LRS.ReduceForallE.of_ladder' depends on axioms: [propext, Quot.sound]
'Lean4Lean.SExpr.LRS.PiHeadNorm.of_reduceForallE' depends on axioms: [propext, Quot.sound]
'Lean4Lean.SExpr.LRS.PiHeadNorm.of_crLadder' depends on axioms: [propext, Quot.sound]
'Lean4Lean.SExpr.LRS.SubjectRedS.of_parRedSDefeq' depends on axioms: [propext, Quot.sound]
'Lean4Lean.SExpr.LRS.NormalEqPiInvL.of_parts' depends on axioms: [propext, Quot.sound]
'Lean4Lean.SExpr.LRS.PiPathInv.of_piEdgeObs' depends on axioms: [propext, Quot.sound]
'Lean4Lean.SExpr.LRS.PiEdgeObs.of_parts' depends on axioms: [propext, Quot.sound]
'Lean4Lean.SExpr.LRS.PiEdgeInvObs.of_parts' depends on axioms: [propext, Quot.sound]
'Lean4Lean.SExpr.LRS.PiPathInv.of_crLadder' depends on axioms: [propext, Quot.sound]
'Lean4Lean.SExpr.LRS.crDefEq_is_on_the_gate_path' depends on axioms: [propext, Quot.sound]
```

No `sorryAx`; no `Classical.choice`. Nothing in the probe is `sorry`ed. The
three rungs stated but *not* machine-checked by this pass are R1, R2 and
R11; R11 is a sketch in §5 and should be treated as unverified until a
successor probe lands it.
