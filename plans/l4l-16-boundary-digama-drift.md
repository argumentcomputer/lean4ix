# L4L-16 boundary decision: digama upstream drift (prepared 2026-08-14; superseded recommendation — see 2026-08-20 addendum)

The drift recorded in `plans/roadmap.md:82` ("two commits past `b292275c`,
at `3f6e8f92`") is stale: digama master is now **four** commits past the
merge base, tip `4b60e53d1531` (committed 2026-08-14, today). Evidence
caveat: none of the four is in the local object store — local
`upstream/master` still points at `b292275c`; the 2026-08-12 audit was
network-only, and this analysis read the commits via the GitHub API
(read-only, no fetch, no repo mutation). **Any reconcile must start with a
`jj git fetch` this checkout has not had** — do it only at a clean boundary.

## The two commits (what they actually do)

1. `aaeeb156bf37` — perf: replay into a stage-2 environment. Adds
   `stage₁ := false` to `Environment.empty`
   (`Lean4Lean/Environment/Basic.lean`, `constants := { stage₁ }`), passed in
   `replayFromFresh` (`Lean4Lean/Replay.lean`). Pure perf (stage-1 SMap
   copying made fresh replay quadratic; 37s → 0.14s on Init); lookup
   semantics unchanged.
2. `3f6e8f927a42` — chore: enable the new level algorithm. Two real wires:
   `isEquivList := List.all2 isEquiv'` (`Lean4Lean/Level.lean`; `isEquiv'` =
   stdlib `isEquiv` fast path, then complete `Normalize.normalize` fallback)
   and `checkConstructors` universe check `geq → geq'`
   (`Lean4Lean/Inductive/Add.lean`). Behavior change: the checker now
   *accepts more* (complete level algebra; per upstream `divergences.md`,
   never fewer). Riders: upstream `Verify/Level.lean` `isEquivList_wf`
   updated to `isEquiv'_wf`; cosmetic `def → theorem` in
   `Experimental/{LogRel,SExpr,ShapeLogRel}.lean`; lakefile/CI moves
   `Lean4Lean.Tests` out of default targets.

Two newer commits past the audited tip:

3. `624414182cfb` — perf: add lazyDeltaProjReduction. Rewrites
   `ReductionStatus` (`| bool b` → `| true` / `| false tn sn`), splits
   `reduceProj` into `reduceProjCore` + explicit `>>=` wrapper, adds
   `lazyDeltaProjReduction`, and changes the `isDefEqCore'` proj case from
   `isDefEq te se` to `lazyDeltaProjReduction te se ti` — a defeq-path
   behavior change. Verify side: restructures `ReductionStatus.WF`,
   `lazyDeltaReduction*.WF`, `isDefEqCore'.WF`; moves `reduceProj.WF` from
   `WHNF.lean` (sorry) to `Reduce.lean`, proved atop a *new sorry*
   `reduceProjCore.WF`; proves `lazyDeltaProjReduction.{finish,loop}.WF`.
4. `4b60e53d1531` (2026-08-14) — fix: compute `isKTarget` before
   `mkRecInfos` in `AddInductive.run` (kernel step alignment; "nothing
   observable"); rewrites the `divergences.md` Level entry.

## Overlap with the fork

Fork HEAD (`931c686`, merge-base to `b292275c` confirmed) has modified 14 of
the 16 touched files; per-commit classification:

- `aaeeb15`: **clean-apply**. Fork regions are exact pre-images
  (`Environment/Basic.lean:121`, `Replay.lean:324`); no proof contact.
- `3f6e8f92`: **half-absorbed / textual-clean, semantic residue**. The fork
  made the identical `isEquivList := all2 isEquiv'` change in merge `99a7f8a`
  (`Lean4Lean/Level.lean:371`), with `isEquivList_wf` already on `isEquiv'_wf`
  (`Verify/Level.lean:3865-3871`; proved, sorry-free at `:3836`) — that half
  merges as a no-op. Residue: the `geq → geq'` flip — fork's `Add.lean:477`
  still has the pre-image inside a +2333-line rewritten file. The
  `def → theorem` hunks hit `Experimental/SExpr.lean:1057` and
  `Experimental/ShapeLogRel.lean:2304,2685,2848,2857,2877` — still `def` in
  the fork, and **both files carry uncommitted 16C′ edits right now**.
- `624414`: **semantic-conflict-likely** (the expensive one). Fork's
  `TypeChecker.lean:72-75` still has `| bool (b : Bool)` and the unsplit
  `reduceProj` (`:358`); fork's `Verify/TypeChecker/IsDefEq.lean` diverges by
  698 lines exactly where upstream rewrites `ReductionStatus.WF` (`:841`),
  `lazyDeltaReductionStep.WF` (`:857`), `loop.WF` (`:950`), and
  `isDefEqCore'.WF` (`:1177` region). The fork **already proved
  `reduceProj.WF` sorry-free in place** (`Verify/TypeChecker/WHNF.lean:25-100`)
  against the unsplit implementation, while upstream's parallel version rests
  on a new `reduceProjCore.WF` sorry — two proof architectures for the same
  theorem, reconcilable only by hand (fork's proof likely discharges
  upstream's sorry after reshaping).
- `4b60e53`: **textual-clean, cheap semantic tail**. Fork's `run` matches the
  pre-image ordering (`Add.lean:2668-2676`, `isKTarget` after `mkRecInfos`);
  `divergences.md` (fork: 2 changed lines) will conflict trivially.

## Proof-surface exposure

- Level/inductive: fork fixture proofs `unfold AddInductive.checkConstructors`
  directly (`Verify/Environment/IndexedVecOuterReplay.lean:1659-1724`,
  `MutualInductiveFixtures.lean:516`) — the `geq'` flip lands inside a
  function they unfold, forcing re-discharge (concrete goals should survive:
  `geq' = geq || _` short-circuits). Owner: L4L-19B (`roadmap.md:773-782`,
  "`addDecl.WF` — now only its `inductDecl` case … full `TrEnv` over fixture
  environments").
- TypeChecker: `624414` rewrites the code under L4L-19A
  (`roadmap.md:761-771`, "enclosing WHNF roots have exact guards") and the
  fork's largest-diverged proof file. Roadmap already places the drift here:
  `roadmap.md:755-759` — "two unabsorbed checker-side commits … land in
  exactly this territory. The reconcile-or-defer decision made at the L4L-16
  boundary precedes detailed L4L-19 scoping; if deferred, repeat the check
  here."
- No Verify surface touches `Replay.lean` or `Environment.empty` (grep:
  only `SMap.WF.empty`/`ConstMap {}` fixture literals, e.g.
  `Verify/Environment/NormalizationMatrix.lean:48`).

## Recommendation

**Defer to the L4L-19 entry boundary, and make the reconcile merge L4L-19's
first action** (per `roadmap.md:758-759`). Not now; not L4L-20C.

Strongest reasons: (1) the drift has zero contact with L4L-16's subject
matter — its only L4L-16-adjacent hunks are keyword swaps in the two
Experimental files that hold uncommitted 16C′ edits, so merging now maximizes
interruption (fetch + merge + fixture re-discharge + the `624414` proof-
architecture reconcile, session-scale) for zero milestone benefit; (2) one
merge instead of two — upstream committed again *today*, the fork's
Verify/TypeChecker and Inductive surfaces are quiet until L4L-19, so waiting
accrues no fork-side conflict growth, while reconciling now still forces a
repeat at L4L-19.

Strongest counter-argument: `3f6e8f92`+`624414` change checker behavior
(`geq'` widens acceptance; proj defeq now runs `lazyDeltaProjReduction`)
that L4L-19A/B proofs must target, and upstream is visibly active — the
delta compounds while we wait. But that argues only against deferring *past*
L4L-19 (why L4L-20C loses: 19A/B would write new proofs against stale
checker text, guaranteeing rework), and the live residue is small and
enumerated — half of `3f6e8f92` is already convergently absorbed.

## Evidence

- Refs: base `b292275cecebb70ae65fabe7ef7c57dc3aafaf4e` (= local
  `upstream/master`), fork HEAD `931c686`, fork merge `99a7f8a` (L4L-15R);
  drift commits `aaeeb156bf37`, `3f6e8f927a42`, `624414182cfb`, `4b60e53d1531`
  read 2026-08-14 via `api.github.com/repos/digama0/lean4lean/compare/…` and
  `…/commits/<sha>` (read-only; not fetched).
- Local: `git for-each-ref refs/remotes`; `git cat-file -t 3f6e8f92` (absent);
  `git merge-base HEAD b292275c` (= b292275c); `git diff --stat
  b292275c..HEAD -- <16 files>`; `git show HEAD:<file>` + `grep -n` for each
  file:line above; `git status --porcelain` for the mid-16C′ dirty set.

## Addendum (2026-08-20): five commits, two large in-flight PRs — recommendation flips to reconcile at the next checkpoint boundary

Re-scanned via `gh api` + `git fetch upstream` (remote-tracking refs only;
working copy untouched). Both legs of the 2026-08-14 defer rationale are now
stale: the 16C′ working-copy edits are committed (clean tree at `06f13e02`),
and upstream's in-flight PR queue makes "one merge instead of two" point the
other way.

**Drift is now five commits** past `b292275c`, tip `e0e3f6bc` — the four
analyzed above plus:

5. `e0e3f6bc` (2026-08-14) — feat(theory): coNP-hardness of level
   equivalence. New self-contained `Lean4Lean/Theory/LevelSat.lean`
   (~450 lines): SAT reduction for `isEquiv`/`geq`
   (`equiv_iff_unsat`, `le_iff_unsat`). No name collisions, no checker
   contact, **clean-apply**.

Upstream `lean-toolchain` is still `v4.33.0-rc2` (fork remains slightly
ahead on v4.33.0 final; ledger D018 stands).

**In-flight signals that change the calculus:**

- **PR #43 (barabbs, "Iota Reduction", open, updated 2026-08-18, base =
  exactly `b292275c`, +1256/−35 over 20 files).** Third-party ι-reduction
  formalization: `VEnv.pats` registry, `IsDefEq.pat` constructor, real
  `addInduct`, `VRecursor`/`VRecRule`, 12 `IOTA-TODO` sorries (including
  the Church–Rosser `.pat` case — it hits the same wall our L4L-18B
  `Params` interface addresses). **16 of its 20 files are files this fork
  has modified since the merge** (Theory/Inductive, Typing/Basic,
  ChurchRosser, Lemmas, Pattern, Strong, VEnv, VExpr, Verify/Environment,
  Extension, four Experimental files). Mario has not reviewed it yet; his
  verdict decides whether the next reconciliation collides head-on with a
  competing iota design. Read it for design comparison regardless.
- **PR #32 (kim-em, "Verify HasPrimitives conservation", open, updated
  2026-08-12, 33 files, +24k/−1.3k).** Verifies the primitive-definition
  recognizer and `HasPrimitives` preservation — direct overlap with the
  fork's D017 Tier-V debt (`checkPrimitiveDef.WF`, `addQuot.WF`,
  `Extension.lean` transports). If merged it may discharge or reshape
  several fork sorries — check before investing in those proofs.
- **PR #27 (kim-em).** Proves `Level.hasParam_eq`/`hasMVar_eq` (+71/−50),
  turning two of the fork's three forbidden cached-field axioms into
  theorems — L4L-20A pre-work landing upstream for free.
- **Branch `differential`** (C++-kernel parity harness; source of
  `624414`) and **branch `arena`** (`--import file.ndjson` lean4export
  replay) signal continued upstream checker activity; expect more parity
  fixes to trickle into master.

**Revised recommendation: reconcile all five master commits at the next
checkpoint boundary (the 16C′ conditional-closure checkpoint), as an
explicit integration-only checkpoint — do not wait for L4L-19.**

Reasons: (1) the tree is clean and the drift is small — four of five are
trivial/clean-apply, so the merge is one session dominated by the `624414`
proj-restructure, where the fork's already-proved `reduceProj.WF` must be
reshaped onto the `reduceProjCore` split — and that reshaping is an
**upstream-contribution opportunity** (the fork's TrProj machinery can
likely discharge upstream's new `reduceProjCore.WF` sorry outright);
(2) either of PR #43/#32 merging would stack a large, colliding delta on
top of the current five — reconciling now means the next heavy
reconciliation starts from a shared recent base instead of compounding;
(3) the `3f6e8f92` residue (`geq → geq'` in `checkConstructors`) sits
inside files L4L-19B fixtures unfold, so absorbing it early keeps 19B
proofs targeting current checker text. The counter-argument that waiting
avoids interrupting 16C′ no longer applies: the reconcile slots between
checkpoints, and 16C′'s conditional wrap is the next one.
