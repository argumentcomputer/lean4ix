# L4L-16D0 slice map — concrete execution plan

## Worker update (2026-08-14)

The two interface blockers found by this review are now closed in the active
working tree:

- **G1:** `IsDefEqStrong.defn` is a finite, definition-specific constructor.
  It combines registered constant metadata, independently strong-typed RHS
  evidence, and the local proof-carrying `Pattern.Action`; it does not add an
  environment oracle or a recursive premise to ordinary `const`.  The new
  case is threaded through weakening/substitution/stratification and semantic
  soundness, and the Experimental SExpr, logical-relation, and adequacy
  modules build.
- **G2:** weak constant-endpoint inversion is implemented by
  `HeadConstLevelsWF`, `IsDefEq.headConstLevelsWF`, and the left/right
  `const_*_levelsLength` corollaries.  The proof covers beta exposure and raw
  registered equations through `Params.henv.defEqWF`; no new semantic field
  is required.

Consequently D0b is no longer blocked on the definition knot, and the
concrete `iotaSite.levelsLength` field has a generic source.  The remaining
D0 work begins at the concrete Nat `Params`/`Params.Semantic` construction
and the union/non-overlap/site derivations listed below.

## Implementation update (2026-08-14)

**D0a and D0b are complete in the active working tree.**
`Lean4Lean/Experimental/SExprParamsD0.lean` now preserves the Nat-only D0a
certificate and layers D0b over it with the checked declaration
`d0def : Nat := Nat.zero`.  The extended `d0Env`/`D0Pat` inventory, all six
`Params.Semantic` fields, the definition-specific strong contraction, both
generated Nat iota sites, and the endpoint `d0SortInvS` are kernel-checked.
In particular, the iota-site proof is replayed against `d0Env` itself, so it
remains valid for contexts that mention `d0def`; it is not obtained by
casting such contexts back into the smaller Nat environment.

`nix develop --command lake build Lean4Lean.Experimental.SExprParamsD0`
is green (122 jobs), the D0 file has no `sorry`/`admit`, and an exact
`#guard_msgs`/`#print axioms` pin records the endpoint closure.  The pin
contains the inherited 16C′ `sorryAx`, the fixture's persistent-map
contracts, and named concrete `native_decide` observations; closing 16C′ is
expected to remove the inherited `sorryAx` without changing the D0 instance.
The gap/status tables below remain as the pre-implementation audit record.

Audience: the L4L-16D worker session and John. Produced read-only on
2026-08-14 by an analysis session; no `.lean` file was touched.

## Snapshot

All file:line references below were read against this state and **will
drift**: the 16C′ session is actively editing `Experimental/` (one write
observed hours before this read). Re-verify line numbers before acting.

| File | Size | mtime at read |
|---|---|---|
| `Lean4Lean/Experimental/SExpr.lean` | 182,986 B | 2026-08-13 13:07 |
| `Lean4Lean/Experimental/ShapeLogRel.lean` | 583,544 B | 2026-08-14 01:21 |
| `Lean4Lean/Experimental/ShapeLogRelAdequacy.lean` | 181,248 B | 2026-08-14 03:31 |

- git HEAD `931c686` (detached), working copy dirty in exactly the three
  files above plus plans docs. jj: `.jj/` present, `jj workspace list` =
  `default: muqzvzmw 6c45e8a9` only.
- Open admissions on the D0-relevant path at read time:
  `SExpr.lean:3516` (`WHRed.weakU_inv`, `extra` case), `SExpr.lean:3739`
  (`WHRedS.defeq`), `SExpr.lean:3842`/`3908` (`InferType(S).hasType`),
  and the sole adequacy admission `ShapeLogRelAdequacy.lean:3058` inside
  `LR.adequacy` (declared at `ShapeLogRelAdequacy.lean:2856`).
  `ShapeLogRel.lean` is sorry-free. D0's endpoint inherits these until
  16C′ closes them; that is expected and does not block D0.

## Params/Semantic field inventory

### `class Params` — `SExpr.lean:24-45` (11 fields)

| Field | Signature (exact) | Line |
|---|---|---|
| `env` | `VEnv` | 25 |
| `henv` | `env.Ordered` | 26 |
| `univs` | `Nat` | 27 |
| `Pat` | `(p : Pattern) → p.RHS × p.Check → Prop` | 28 |
| `classify` | `Name → Option Classification` | 29 |
| `pat_simple` | `Pat p r → ∃ sp : SimplePattern, p = sp.toPattern` | 30 |
| `pat_wf` | `Pat p r → p.WF classify` | 31 |
| `pat_uniq` | `Pat p₁ r → Pat p₂ r' → Subpattern p₃ p₁ → p₂.inter p₃ = some p₄ → p₁ = p₂ ∧ p₂ = p₃ ∧ r ≍ r'` | 32-33 |
| `pat_app_l` | `Pat p r → Subpattern (.app p₁ p₂) p → ¬Subpattern (.app p₃ p₄) p₁` | 36 |
| `pat_app_l_uniq` | `Pat p r → Pat p' r' → Subpattern (.app p₁ p₂) p → Subpattern (.app p₁' p₂') p' → Subpattern (.var p₃) p₁ → p₁'.inter p₃ = none` | 37-38 |
| `pat_app_uniq` | `Pat p r → Pat p' r' → Subpattern (.app p₁ p₂) p → Subpattern (.app p₁' p₂') p' → Subpattern p₃ p₁ → Subpattern p₃' p₂' → p₃.inter p₃' = none` | 39-40 |

`pat_app_r_arity` (41-42) and `extra_pat` (43-45) are **commented out** —
no coverage law is currently demanded of the instance.
`Classification` (`ctor`/`etaCtor`/`symb`/`indTy`) is at 8-16;
`Pattern.WF classify` at 18-22 (note: `.app` adds 1 to the extra-arity
accumulator and each `.var` adds 1, so a recursor head's `symb` arity is
major-arity + 1, counting the major itself).

### `class Params.Semantic [Params]` — `SExpr.lean:1844-1924` (6 fields)

| Field | Shape | Line |
|---|---|---|
| `structureEta` | `env.structEtas rule → strong self-typing of rebuild → strong self-typing of major → IsDefEqStrong … rebuild ≡ major` | 1845-1856 |
| `ctor` | `env.constants c = some ci → ls.length = ci.uvars → ∀ cl : CtorBundle.IsCtor c, {F : CtorBundle c cl // IsDefEqStrong Γ (mkInst ls ci.type) (F.rhs ls) (.sort F.u)}` — **data** (Subtype), quantified over all `ls`, `Γ` | 1857-1862 |
| `defn` | `Pat (.const c) r → ∃ value closed, r = (.fixed value closed, .true) ∧ ∀ ci ls Γ, … → IsDefEqStrong Γ (.const c ls) (mkInst ls value) (mkInst ls ci.type)` — **unconditional** equations (no typing inputs) | 1867-1875 |
| `iotaRule` | `Pat (RecursorIotaPattern rec major ctor arity) r → Pattern.IotaRule r` | 1879-1884 |
| `iotaSite` | rule + `captureType` + `CaptureTyping` + `IotaTyping` + `MatchesS` + weak redex self-`IsDefEq` + `∃ u, IsDefEq Γ A A (.sort u)` → `Pattern.IotaReductionSite …` | 1891-1914 |
| `registered` | `env.defeqs df → ls.length = df.uvars → strong lhs self-typing → strong rhs self-typing → IsDefEqStrong Γ (mkInst ls df.lhs) (mkInst ls df.rhs) (mkInst ls df.type)` — receives endpoint typings as **inputs** | 1919-1924 |

Recent-additions audit requested by the plan:

- `iotaRule`, `iotaSite`, `registered` — landed as fields (above).
- `closedHasTypeStrong` — **not a field**: a derived theorem at
  `SExpr.lean:2074-2101`; the comment at 2073 says explicitly "derived
  from `Params.henv`, not added to `Params.Semantic` as an oracle".
  Likewise `registeredRhsStrong` (2105) and `IotaRule.rhsStrong` (2116).
- lemma (C) / coherence field (registered-equation lhs heads classify as
  symbols) — **not landed**. Sole mention is
  `plans/l4l-16-completion-plan.md:485`: "(e) lemma (C) and the coherence
  field only if the first-order composition still needs raw telescope
  alignment (it may not …)" — conditional, deferred. No such field exists
  in either class.

Key supporting definitions (same file): weak `IsDefEq` 1260-1280 with
**raw** `extra` (1279-1280: `env.defeqs df → ls.length = df.uvars → …`);
`SpineWF` 1286-1299; `Pattern.CaptureTyping` 1585-1588;
`Pattern.IotaTyping` 1593-1607; `Pattern.IotaRule` 1613-1623 (fields
`pat`, `df`, `registered`, `rhsClosed`, `capturePaths`, `rhsTower`);
`Pattern.IotaReductionSite` 1643-1667 (fields `typing`, `matched`,
`levelsLength`, `captureSpine`, `lhsCollapse`, `dfs`, `defeqs`,
`checked`); `Pattern.Action` 1676-1684; `IotaReductionSite.action`
1930-1960 (derives the `Action` generically — the instance never builds
one for iota directly); `CtorBundle.IsCtor` 1774, `CtorBundle` 1783-1790
(note `hu0 : u ≠ .zero`), `CtorBundle.rhs` 1792.

`IsDefEqStrong` 1798-1839. Two rules matter enormously for D0:

- `const` (1803-1813) carries the premise
  `∀ {r}, Pat (.const c) r → Γ ⊢ r.1.applyS ls Empty.elim ≡ .const c ls : mkInst ls ci.type`
  (1811-1812) — the definition-unfolding equation is a **prerequisite**
  of typing any constant that has a defn pattern (comment 1807-1810: the
  direction serves `LE_Interp.Const.pat` semantic recursion).
- `extra` (1836-1838) needs a full `Pattern.Action` (hence a `Pat`
  member) **plus strong typings of both endpoints**.

Consumption sites (fixing the contracts): `IsDefEqStrong.mkS`
(1965-2068) uses `ctor` at 1992/1998, `defn` at 2006, `structureEta` at
2060, `registered` at 2067. Endpoint:
`VEnv.IsDefEqU.sort_invS` at `ShapeLogRelAdequacy.lean:3698-3708` —
signature `[Params.Semantic] → OnCtx Γ (Params.env.IsType Params.univs)
→ IsDefEqU … (.sort u) (.sort v) → u ≈ v`. Nothing beyond the two
instances is required.

## Certificate sources

| Artifact | Location | Certifies | Feeds |
|---|---|---|---|
| `CertifiedExtension` | `Theory/Typing/InductivePatternEnv.lean:59-66` | one extension rule: `df`, `SimplePattern`, RHS/Check payload, `covers` at `stripLams (df.lhs.instL ls)` | `Pat` union half (D1/D2); `quot` instance at 113-146 (D1) |
| `iotaExtension` | `InductivePatternEnv.lean:157-184` | every generated rule fits the beta-collapsed extension shape | D2 |
| `assembleEnv` / `_defeqs` / `_defeq_cases` / `_WF` | `InductivePatternEnv.lean:189/247/289/305` | assembled env, exact defeq inversion, Ordered | alternative `env`/`henv` route (D2) |
| `AssembledPat` | `InductivePatternEnv.lean:330-336` | union pattern set; **only** `pat_simple` (339) and `ext_covers` (349) proved | `Pat` at D2; the four non-overlap laws are missing at this level (gap G3) |
| `BlockGenerationChecked` (+ `.WF`) | `Theory/Inductive.lean:2141` / `2812`; `identityBlockGeneration?` 2161 | checked block generation | rule data via accessors below |
| `IotaPat` + block-local laws | `Theory/Typing/InductivePattern.lean:607-612`; `pat_simple` 617, `recover` 624, `pat_uniq` 640, `pat_app_l` 668, `pat_app_l_uniq` 679, `pat_app_uniq` 707 | the four non-overlap laws, block-locally | proof **templates** for D0's bespoke laws |
| `RuleClosure` / `captureArgs` / `ruleRHS` / `ruleCheck` | `InductivePattern.lean:531/541/553/563` | closedness; RHS template `= RHS.appN (.fixed rule.rhs closed) captureArgs` — exactly `IotaRule.rhsTower`'s shape (`SExpr.lean:1622-1623`) | `Pat` payloads, `iotaRule` |
| `pat_wf` (typed match soundness) | `Theory/Typing/InductivePatternWF.lean:543` (axioms pinned 943-949) | successful match ⇒ typed defeq | not directly a field; background for D2 |
| L4L-10B match-inversion library | `Theory/Typing/Pattern.lean`: `RecursorIotaPattern` 304, `subpattern_inv` 346, `inter_some` 407, `inter_varN_const_some` 419, `inj` 439, `app_subpattern` 449; `Pattern.inter` 54-60; `SimplePattern` 242-248 (has `.defn`) | pattern combinatorics | the four non-overlap laws |
| SExpr match layer | `SExpr.lean:802-807` (`MatchesS`), 848 (`MatchesS.varN_const_inv`) | SExpr-side spine decomposition | `iotaSite` |
| Declaration history | `Theory/VDecl.lean:11-12` (`VDefVal.toDefEq`: lhs `= .const name (VLevel.params uvars)`); `Theory/Typing/Env.lean:19-55` (`VDecl.WF`, `.def` at 24-27), 57-67 (`WF'`/`WF`); `Theory/Typing/EnvLemmas.lean:112` (`WF → Ordered`) | how a definition's defeq is registered; Ordered | `env`/`henv` for D0b; `defn` |
| Theory strong system | `Theory/Typing/Strong.lean:18` (`IsDefEqStrong`), 91-99 (`extra`: raw + typings, **no** action), 116-123 (`const`: **no** unfolding premise), 786 (`IsDefEq.strong`) | Theory-side strengthening | contrast for gap G1 — Theory has no knot, SExpr does |
| Eta registry (L4L-15B) | `Theory/VEnv.lean:173/193-194` (`structEtas`, `addStructEta`); `VEnv.hasStructureEta_of_registry` pinned at `Tests/StructureEtaCapability.lean:82,100-103` | registered structure eta | `structureEta` at D4 only; vacuous in D0 |
| Nat fixtures | `Lean4Lean/Theory/InductiveFixtures.lean:34` (`natDecl`), 51-52 (`natBlockGenerationChecked`), 88-93 (both rules, literal `vdefeq`), 72 (`kTarget = false`); `Lean4Lean/Verify/Environment/InductiveFixtures.lean:143` (`natDecl_wf`), 348-350 (`nat_final_matches_addInduct`, by `rfl`), 354-362 (`natFinalEnv_ordered`, axioms `[propext, Classical.choice, Quot.sound]`, `#guard_msgs`-pinned), **364 (`nat_env_wf : natFinalEnv.WF`)** — namespace `Lean4Lean.InductiveReplayFixtures` | the D0 environment, Ordered and WF, exists today | `env`, `henv` |
| Other blocks | punit `Theory/InductiveFixtures.lean:136-201` (1 rule, `punitDecl_wf` 174, `punitEnv_ordered` 199); patBlock/patVec `Theory/Typing/InductivePatternFixtures.lean:25/53` (+ closures 102/105, assemble guards 168-169, **no Ordered**); tree/indexedTree `Theory/MutualInductiveFixtures.lean:51-58/122-129`; Bool `Theory/InductiveFixtures.lean:110-126` | candidate ladder | D2 fixtures; see disqualification below |

## D0 fixture candidate

**Chosen: the Nat block (`natFinalEnv`) + one new definition
`d0def : Nat := Nat.zero`, staged as D0a (iota-only) then D0b (add the
definition).**

- Iota rules (from `Theory/InductiveFixtures.lean:88-93`):
  `motive z s => Nat.rec motive z s .zero ≡ z` and
  `motive z s n => Nat.rec motive z s (.succ n) ≡ s n (Nat.rec motive z s n)`.
  Patterns: `.iota Nat.rec 3 Nat.zero 0` and `.iota Nat.rec 3 Nat.succ 1`
  (major arity 3 = 1 motive + 2 minors; `nparams = 0`). Rule uvars = 1
  (the motive's `Sort u`). `ruleCheck` degenerates to `.true` for Nat
  (no params, no indices — `InductivePattern.lean:563` folds over empty
  lists), so every `Action.dfs = []`.
- classify table (5 literal names): `Nat ↦ .indTy 0`,
  `Nat.zero ↦ .ctor 0`, `Nat.succ ↦ .ctor 1`, `Nat.rec ↦ .symb 4`
  (extra-accumulation: the app contributes 1, three `varN` vars 3),
  `d0def ↦ .symb 0` (D0b).
- Environment: D0a = `natFinalEnv` as-is (`henv` = `natFinalEnv_ordered`).
  D0b = `natFinalEnv.addConst d0def … |>.addDefEq (toDefEq …)` with
  `VDecl.WF.def` (`Theory/Typing/Env.lean:24-27`) consed onto
  `nat_env_wf`'s history (Verify `InductiveFixtures.lean:364`), Ordered
  via `EnvLemmas.lean:112`.

**Deviation from the plan's "one iota rule": Nat has two.** No
Ordered-certified single-rule Type-valued block exists, and the only
single-rule block with an Ordered proof is disqualified:

- **punit is disqualified by `CtorBundle.hu0`.** `punitDecl` has
  `uvars = 1`, `resultLevel = .param 0`
  (`Theory/InductiveFixtures.lean:142,153`). `pat_wf` of its iota pattern
  forces `classify PUnit.unit = some (.ctor 0)` (`Pattern.WF`,
  `SExpr.lean:18-22`), so `CtorBundle.IsCtor PUnit.unit` holds and
  `Semantic.ctor` (1857-1862) must produce a bundle at **every** `ls`,
  including `ls = [SLevel.zero]` — where `mkInst ls ci.type =
  .const PUnit [zero]` types only in `.sort zero`, forcing `F.u = zero`
  against `hu0 : u ≠ .zero` (`SExpr.lean:1790`). This matches the
  completion plan's first-order/non-Prop staging
  (`l4l-16-completion-plan.md:465-480`; "Acc is the known exception").
  *(Uncertainty flag: verified by signature analysis only, not by an
  attempted build.)*

Ranking: 1. **Nat** (Ordered+WF exist, literal kernel names, checks
`.true`, always `u = 1 ≠ 0`); 2. patBlock (universes always `succ` but 3
rules, mutual, no Ordered proof); 3. patVec (external `Nat` constants;
no Ordered); 4. Bool (like Nat but no prebuilt block descriptor or WF);
punit disqualified. Recommendation: do the zero rule first, succ second
(the succ rule adds a recursive minor application on the RHS — the honest
smoke test).

## Sourcing table

Status legend: READY (source exists, plumbing only), WORK (concrete
construction, known shape), GAP (missing lemma/decision).

| Field | Status | Source / adaptation |
|---|---|---|
| `Params.env` | READY | `natFinalEnv` (Verify `InductiveFixtures.lean:348-350`); D0b appends one const+defeq |
| `Params.henv` | READY | `natFinalEnv_ordered` (354-356); D0b: `VDecl.WF.def` + `nat_env_wf` (364) + `EnvLemmas.lean:112`; needs the `addConst` freshness computation (G5b) |
| `Params.univs` | READY | leave parametric: build the instance as a `def` over any `univs : Nat` |
| `Params.Pat` | READY | bespoke inductive, 2 members (D0a) / 3 (D0b); payloads = `ruleRHS`/`ruleCheck` (`InductivePattern.lean:553/563`) over `natBlockGenerationChecked` (`InductiveFixtures.lean:51-52`) + a new `natRuleClosure` by `decide` (template `patTreeClosure`, `InductivePatternFixtures.lean:102-103`) (G5d) |
| `Params.classify` | READY | 5-name literal table above |
| `pat_simple` | READY | per-member `⟨.iota …, rfl⟩` / `⟨.defn _, rfl⟩` (`Pattern.lean:242-248`) |
| `pat_wf` | READY | `decide`/`simp [Pattern.WF]` against the literal table |
| `pat_uniq` | WORK | clone `IotaPat.pat_uniq` (`InductivePattern.lean:640-666`) for the 2-3 member set; zero-vs-succ cross cases via `RecursorIotaPattern.inter_some` (`Pattern.lean:407`) + ctor-name disequality; defn cases trivial (`.const` vs `.app` inter = `none`, `Pattern.lean:54-60`; only subpattern of `.const` is itself) |
| `pat_app_l` / `pat_app_l_uniq` / `pat_app_uniq` | WORK | clone `InductivePattern.lean:668/679/707` with `app_subpattern` (`Pattern.lean:449`) + `inter_varN_const_some` (419); defn cases vacuous |
| `Semantic.structureEta` | READY | vacuous: `d0Env.structEtas = fun _ => False` (empty at `Theory/VEnv.lean:178`; only `addStructEta` 193-194 extends it) — needs the small emptiness lemma (G5a) |
| `Semantic.ctor` | WORK | two concrete bundles: zero `⟨Nat, [], [], 1, …⟩` with rhs `.const Nat []`; succ `⟨Nat, [.const Nat []], [], imax 1 1, …⟩` with rhs `= mkInst [] ci.type` syntactically; `hu0` via `SLevel.succ_ne_zero` (**lives at `ShapeLogRel.lean:20`, not `SExpr.lean`** — import or reprove, G5c); strong self-typings direct (`const`'s `F`/hpat premises vacuous for `Nat`: `IsCtor Nat` false, no `Pat` at `.const Nat`) |
| `Semantic.defn` | D0a: READY (vacuous — no `Pat (.const c)` member). D0b: **GAP G1** | see Gaps |
| `Semantic.iotaRule` | WORK | two descriptors: `df` = the registered rules (membership `.inl rfl`-style, cf. `InductiveFixtures.lean:104-106`), `rhsClosed` by `decide`, `capturePaths` from `captureArgs`'s paths (`InductivePattern.lean:541-549`: `.inl` of first 3 rec paths ++ `.inr` of ctor field paths), `rhsTower` = a `List.map` equation against `ruleRHS` (553-558) — mechanical |
| `Semantic.iotaSite` | WORK + **GAP G2** | `typing`/`matched` from inputs; `dfs = []`, `defeqs` by `rfl` (checks `.true`); `levelsLength` **not derivable from the stated inputs** (G2); `captureSpine` (`PathSpineWF` against `df.type`'s telescope) and `lhsCollapse` (weak beta collapse of the applied tower, 3-4 `.beta` steps + congruence) built concretely per rule (G4) |
| `Semantic.registered` (iota defeqs) | WORK (largest) | `lamDF` descent under the 3-4 binders to the bodies; at the body, `.extra` with the iota `Action` (weak `sound` = raw weak `extra` 1279-1280 + beta chain); strong redex typing built from scratch — dominated by one reusable derivation: strong self-typing of `mkInst ls (Nat.rec's type)` (a concrete Pi-tower derivation) |
| `Semantic.registered` (defn defeq, D0b) | **GAP G1** | see Gaps |

Endpoint: `sort_invS` (`ShapeLogRelAdequacy.lean:3698`) instantiates
with nothing further; supply `OnCtx [] …` trivially and pin
`#print axioms` (expect `sorryAx` from the five known admissions until
16C′ lands).

## Gaps

- **G1 — the defn/strong-const circularity (interface-level; blocks the
  definition half, D0b).** `Semantic.defn` (`SExpr.lean:1867-1875`) must
  supply *unconditional* strong unfolding equations. The only
  cross-constant rule in `IsDefEqStrong` is `.extra` (1836-1838), which
  needs a `Pattern.Action` (hence a `Pat` member at `.const c`) **and** a
  strong typing of `.const c ls`; the only constant-introduction rule
  `const` (1803-1813) demands the unfolding equation as its premise
  (1811-1812) at the *same* `(ls, Γ)`. So any derivation of the equation
  strictly contains a derivation of itself — no finite derivation
  exists. Omitting the defn pattern from `Pat` instead makes
  `registered` (1919-1924) unsatisfiable for the registered defn defeq
  (no `Action` without a `Pat` member). Either way, an env containing a
  definition defeq admits no instance under the current interface.
  Theory's system has no knot: its `const` has no unfolding premise and
  its `extra` is raw (`Strong.lean:116-123`, `91-99`). Candidate
  repairs, **16C′-owner decision required** (one-writer rule,
  `l4l-16-completion-plan.md:748-751`): (a) weaken the `const` premise's
  equation to weak `IsDefEq` — then it comes free from raw weak `extra`,
  if `LE_Interp.Const.pat` (comment 1807-1810) tolerates weak; (b) add a
  dedicated defn-unfolding constructor to `IsDefEqStrong` that types
  only the rhs value. *(Confidence: high on the signature analysis, but
  it is untested — task 2 below is a ≤30-line probe before escalating.)*
- **G2 — `iotaSite.levelsLength` unsourceable.**
  `IotaReductionSite.levelsLength : recLs.length = rule.df.uvars`
  (`SExpr.lean:1657`) is not derivable from `iotaSite`'s inputs
  (1891-1914). Fix: a new weak inversion lemma
  `IsDefEq Γ (.const c ls) e T → env.constants c = some ci → ls.length = ci.uvars`
  — provable by structural induction on the weak judgment (every rule
  preserving a const endpoint carries the length or an IH); no such
  lemma exists (grep negative). Small, generic, no interface change.
- **G3 — union-level non-overlap still missing (D2, confirmed).**
  `AssembledPat` carries only `pat_simple`
  (`InductivePatternEnv.lean:339`) and `ext_covers` (349); the four
  laws exist only block-locally (`InductivePattern.lean:640-740`), and
  no cross-term (block-rule vs extension-rule) lemma exists anywhere.
  Unchanged since the plan was written. D0 dodges it via the bespoke
  `Pat`; D2 must pay it.
- **G4 — no SExpr-side generic site builders.** `captureSpine`
  (`PathSpineWF`) and `lhsCollapse` (beta collapse) have no generic
  constructors; D0 builds them concretely per rule. Genericizing is
  D1/D2 work, not D0.
- **G5 — small missing pieces:** (a) structEtas-emptiness lemma for the
  concrete env; (b) `addConst` freshness discharge over the concrete
  constants function (see the memory note on decidability-discharge
  hazards); (c) `SLevel.succ_ne_zero` is in `ShapeLogRel.lean:20`, not
  `SExpr.lean` (import path or 3-line reproof); (d) `natRuleClosure`
  not yet defined (one `decide` following
  `InductivePatternFixtures.lean:102-103`).

## Ordered task list

Each item is one committed checkpoint; the working tree builds at every
pause. All new code goes in **one new file**
(suggest `Lean4Lean/Experimental/SExprParamsD0.lean`), importing
`Lean4Lean.Experimental.ShapeLogRelAdequacy` and
`Lean4Lean.Verify.Environment.InductiveFixtures`. No existing `.lean`
file is edited.

1. Workspace + skeleton: second jj workspace, new file with imports,
   cold build. (Flagged: first build compiles the 583KB/181KB modules —
   budget hours, not minutes.)
2. **[RISK — do early, non-blocking]** G1 probe (≤30 lines): attempt a
   strong self-typing of a defn constant whose pattern is in `Pat`;
   confirm or refute the circularity; send the finding plus repair
   options (a)/(b) to the 16C′ session. Do **not** change the interface
   unilaterally.
3. D0a environment layer: `natRuleClosure` (`decide`), the defeq
   inventory lemma (`d0Env.defeqs df ↔ df = zeroRule ∨ df = succRule`),
   the structEtas-emptiness lemma (G5a).
4. `classify` + the `D0Pat` inductive + `pat_simple` + `pat_wf`.
5. The four non-overlap laws for `D0Pat` (clone
   `InductivePattern.lean:640-740`); assemble the `Params` instance
   (parametric over `univs`).
6. `Semantic.ctor` bundles + vacuous `structureEta` + the two `iotaRule`
   descriptors (the `rhsTower` map equation).
7. **[RISK — largest]** Derivation layer: strong self-typing of
   `Nat.rec`'s instantiated type (reusable core); the G2 inversion
   lemma; `registered` for the zero rule (lamDF descent + `.extra`
   action + weak beta collapse), then the succ rule as a separate
   checkpoint; `iotaSite` for both (captureSpine, lhsCollapse).
8. Endpoint: close `Params.Semantic`; instantiate `sort_invS`
   (`ShapeLogRelAdequacy.lean:3698`) at the instance; `#print axioms`
   pin recording exactly the inherited 16C′ admissions. **This is the
   D0a exit.**
9. **[BLOCKED on G1]** D0b: add `d0def` (WF extension + freshness),
   extend `Pat`/`classify`, populate `defn` and `registered`-for-defn
   under the repaired interface. This completes D0 as specified in
   `l4l-16-completion-plan.md:668-671`.

## Parallel-start recommendation

**Yes — start D0a now in a second jj workspace; do not wait for 16C′.**

- Build isolation verified: `/.lake` is the first line of `.gitignore`,
  so a second workspace materializes its own untracked `.lake`; the
  worker's builds and D0's builds cannot touch each other. (`result`,
  `.direnv` likewise ignored.) jj repo confirmed (`.jj/` present; one
  workspace `default` today).
- File isolation: D0 adds one new file and edits nothing the worker
  owns, so the eventual merge is import-level only. This respects the
  one-writer-per-`Experimental/` rule because the writer set is disjoint
  by file and by workspace.
- Known frictions: (i) cold first build; (ii) `SExpr.lean` /
  `ShapeLogRelAdequacy.lean` are moving targets (mtimes within hours of
  this read) and the contact surface — `Params`, `Params.Semantic`,
  `IsDefEqStrong` — is exactly what 16C′ may still reshape; expect one
  rebase-adapt pass when 16C′ lands; (iii) the D0a endpoint will carry
  `sorryAx` from the five known admissions until then — gate D0a on
  "instance fields sorry-free + endpoint compiles + axiom set exactly
  the known list", not on a clean closure.
- Sequencing dependency: only task 9 (D0b) waits — on the G1 decision,
  which task 2 requests early. Everything else is decision-free.
- Housekeeping: `.gitignore` ignores `plans/*` except an allowlist; add
  `!/plans/l4l-16d0-slice-map.md` if this document should be versioned,
  otherwise it stays local to this workspace.

## Verification note (sibling session, 2026-08-14 ~12:25 EDT)

The current `SExprParamsD0.lean` (mtime 11:20) elaborates **clean**: exit
0, zero errors, zero sorry-bearing declarations; both `natSortInvS` and
`d0SortInvS` compile with their guard-pinned axiom sets. Residue is 40
lint warnings (30 unused-simp-arg, 6 semireducible class defs, 2 naming,
2 simpa→simp) — 16E polish.

Process note to the D0 worker: your 11:14 verification command
(`lake env lean … --json | rg -m 10 'error'`) deadlocked for ~67 min —
`rg -m 10` exits after ten matches, closing the pipe, and `lean` then
blocks forever on write. It was killed at ~12:21 by the sibling session
to unblock your shell; the ten error lines it finally returned describe
the STALE 11:14 snapshot, already fixed by your 11:20 save. Do not
re-fix them. For future checks, redirect to a file instead of piping
through `rg -m N`.

## D1 executed (2026-08-15) — outcome and D2-builder template

D1 landed as `Lean4Lean/Experimental/SExprParamsD1.lean` (187 decls, no
local admission; endpoint `d1SortInvS` and the sorryAx-free
`d1qEnv_wf` pin in-source). Mutual-definitions half complete end to
end; the quot semantic instance is blocked on the `CtorBundle.hu0`
interface decision recorded at `SExprParamsD1.lean:2703-2755` (see the
completion plan's D1 bullet for the decision framing).

Extension template proven by the build (clone for D2+): env layer →
Pat layer (laws by delegation + fresh-name intersection lemmas) →
structural `Params` → transport functor `d(n)→d(n+1)` (clone
`d0StrongToD1`; the `const`/`defn` cases use a
`d1Pat_at_old_const`-style inversion plus the `ihDef` hypothesis; a
`funext fun path => nomatch path` aligns the const-pattern capture
map) → context/spine/PathSpine clones → strong-const chain (transfer
old; `defn` constructor for new) → `Defn`/`Registered` (old defeqs via
the previous level's `Semantic.closedHasTypeStrong` + transfer; new
direct) → `Ctor` via bundle transfer → `IotaRule`
destructure/rebuild → iota-site replay clone (swap env-lookup lemmas;
the `defeqs_iff` cascade grows one `natRule_rhs_ne_*` native pair per
new defeq) → assembly, endpoint, pin.

Gotchas that cost cycles: term-mode `.trans`/`.symm` on
`IsDefEqStrong` needs `by letI : Params := ...`; `Lookup` inside SExpr
namespaces shadows Theory's (use `_root_.Lean4Lean.Lookup`);
`VEnv.HasType.const` in a bare `have` needs `(U := ...)`;
`addConsts`/`addQuot` compute via simp with per-step
`addConst ... = some ...` lemmas over `native_decide` freshness;
existential witnesses by `exact ⟨_, ...⟩` not `refine ⟨_, ?_⟩`.

## Theory-side pattern API after D2 (2026-08-15)

D2's build fed three reusable pieces back into
`Theory/Typing/InductivePatternEnv.lean` (all `#guard_msgs`-pinned at
`[propext, Quot.sound]`; pins verified load-bearing by a negative
control):

- `SimplePattern.HeadSep.app_l_uniq` (:245) and `HeadSep.app_uniq`
  (:266) — the cross-block `(rule, ext)` engine cases, previously
  inlined. The two landed union laws now call them (proof bodies
  −21/−24 lines, statements and axiom closures unchanged).
- `AssembledPat.recover` (:592) — the inversion principle
  (`cases` cannot destructure `AssembledPat` at a concrete iota
  pattern: stuck `varN` tower). Generalizes the fixture-local version;
  the rule branch uses `gen.ruleEntry i constructor` and the ext
  branch additionally yields `r ≍ (ext.rhs, ext.check)`.
- Scope doc block (:639-666) — one `AssembledPat` covers exactly ONE
  block (`ext_sep`'s pairwise `HeadSep` is unsatisfiable for two rules
  sharing a recursor), so an N-block `Params` takes the N-way sum plus
  N(N-1) hand-written ordered cross-block pairs per obligation.

Migration for D3 (mechanical): drop any local `simple_app_l_uniq` /
`simple_app_uniq` and call `(…headSep…).app_l_uniq h h' h₃` /
`.app_uniq h h' h₃ h₃'` (`.symm` variants unchanged); replace
`assembledPat_cases H` with `AssembledPat.recover Gen H`, and widen
the ext-branch rcases pattern by one component
(`⟨ext, hmem, hpattern⟩` → `⟨ext, hmem, hpattern, -⟩`). The per-block
constructor *inventory* lemma remains per-fixture work — it depends on
the concrete constructor list and cannot come from Theory.
