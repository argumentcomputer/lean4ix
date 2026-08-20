# L4L-16 generic `Params`/`Params.Semantic` instance — design pass

Date: 2026-08-15
Author: design-pass session (agent G), commissioned by the L4L-16E
"DECISION REQUIRED" line in `plans/l4l-16-completion-plan.md:781-785`:

> **Instance generalization is implicit and unstaged:** `sort_invS` holds at
> `[Params.Semantic]`; public `sort_inv` quantifies over arbitrary
> `VEnv.WF env`. "Closes from the instances" needs the generic
> `Params`/`Params.Semantic` construction from any WF history — decide at D4
> exit whether that is D4's endpoint or a named 16E step.

Status: analysis complete; recommendation below. Companion probe:
`plans/probes/probeG-generic-instance.lean` (green, six banked results at
`[propext, Quot.sound]`). No `Experimental/` or `Theory/` file was edited.

---

## 0. TL;DR

**The pending decision is posed on a false trichotomy.** The generic
construction is neither D4's endpoint nor a 16E step nor usefully
conditional. It is a milestone-sized development containing **three
independent walls**, two of which are owned by other milestones:

1. **`CtorBundle.hu0` vs. Prop-typed constructors** — strictly worse than the
   D1 record says. D1 found it for `Quot.mk` at `ls = [.zero]`; in fact
   *every* constructor of a `Prop`-sorted inductive (`Eq.refl`, `And.intro`,
   `Exists.intro`, `Acc.intro`, …) violates `hu0` at *every* instantiation,
   because a constructor's type ends in its inductive type and `imax _ 0 = 0`.
   No environment containing `Eq` can carry the instance. **Banked**
   (`hu0_impossible_at_prop`): under type uniqueness, *no* choice of
   `CtorBundle` can repair this — the failure is intrinsic, not a bad-bundle
   artifact.
   **2026-08-20 note:** the repair this document recommends for this wall
   (§5.1: delete `hu0` outright) was REFUTED 2026-08-15 by executed probe
   `plans/probes/probeA1-hu0.lean` — the ADQ consumption site is free, but
   `build_spine`'s post-deletion statement is FALSE for Prop-sorted
   ctor-classified pattern-argument heads; `hu0` is the syntactic mirror of
   `WShape.HasType.proofIrrel`'s `.indTy` non-Prop-sortedness requirement.
   Resolving the Prop wall needs a Matches/classification-level design (a
   Prop branch, or excluding Prop-recursor iota patterns from `Pat`).
2. **Iota check discharge for parameters/indices** — `Semantic.iotaSite` must
   supply `IotaReductionSite.checked`; `gen.ruleCheck` emits one check per
   parameter and per result index; discharging them at a matched redex needs
   injectivity of a stuck inductive-type application, which is L4L-18A′
   strength. **This wall is recorded nowhere in the plan and bites D2 before
   it bites the generic construction** — D0/D1 pass only because Nat has no
   parameters and no indices (`dfs := []; checked := by simp`).
3. **`Semantic.structureEta` for a nonempty eta registry** — Theory takes
   `IsDefEqStrong.structEta` as a *primitive rule*; SExpr's judgment has no
   such constructor, so the field asks the SExpr layer to *prove* what Theory
   *assumes*. Structure eta does not follow from iota at a stuck major. All
   three existing instances discharge this field vacuously. `VEnv.WF'`
   admits eta rules, so an arbitrary WF environment can have them.

**Conditional instances do not rescue the target.** The restriction cannot be
pushed onto the goal: `sort_invS` consumes `LR.adequacyAt`, a theorem about
*all* derivations, and `IsDefEqStrong.mkS` demands `Semantic.ctor` at *every*
`constDF` node of the *input* derivation. A "non-Prop fragment" instance
therefore yields `sort_inv` only for environments with no Prop-sorted
inductive, no parameterised inductive, and no eta registry — i.e. the D0–D2
fixture ladder, not a public theorem.

**Recommendation:** re-scope the public `IsDefEqU.sort_inv` promotion **off
the 16E gate** into a named successor milestone (§8), exactly as
`plans/l4l-16-weakn-design.md` recommends for `weakN_iff`. 16E then exits on
the SExpr-side statements plus fixture-instantiated endpoints. Four of the
seven staged rungs (§7) are attackable *today* with no interface decision,
and one of them — the generic syntax transport — is already banked in the
probe and deletes ~1200 lines of D-ladder boilerplate.

**One trap worth naming up front:** the generic construction must **not**
consume Theory's `VInductDecl.BlockGenerationChecked.pat_wf`
(`Theory/Typing/InductivePatternWF.lean:543`). It measures at
`[propext, sorryAx, Classical.choice, Quot.sound]` (`:942-949`) because it
composes typed defeqs through `IsDefEqU.trans`
(`Theory/Typing/UniqueTyping.lean:167`) → `uniq` → the sorried `sort_inv`.
It is the natural-looking source for "the rule fires soundly", and using it
would make the promoted theorem circular.

---

## 1. What exactly is missing (and what is not)

`VEnv.IsDefEqU.sort_invS` (`Experimental/ShapeLogRelAdequacy.lean:7064`):

```lean
theorem _root_.Lean4Lean.VEnv.IsDefEqU.sort_invS [Params.Semantic]
    (hΓ : OnCtx Γ (Params.env.IsType Params.univs))
    (h : Params.env.IsDefEqU Params.univs Γ (.sort u) (.sort v)) : u ≈ v
```

Public target (`Theory/Typing/Injectivity.lean:11`):

```lean
theorem IsDefEqU.sort_inv (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (h1 : env.IsDefEqU U Γ (.sort u) (.sort v)) : u ≈ v := sorry
```

`Params` is a *class whose `env` and `univs` are fields*, so "an instance for
`env` at `U`" is a Σ-type, not a typeclass search. Probe §G0 pins that the
whole remaining gap is that Σ-type:

```lean
structure GenericInstance (env : VEnv) (U : Nat) where
  params : Params
  env_eq : @Params.env params = env
  univs_eq : @Params.univs params = U
  semantic : @Params.Semantic params
```

**Banked** (`sort_inv_of_generic`, probe): given the bundle, the public
statement follows in five lines with no further semantic work — the promotion
step really is exactly one instance wide. Its measured closure is
`[propext, sorryAx, Classical.choice, Quot.sound]`, the `sorryAx` inherited
from `sort_invS`'s 16C′ leaf, not from the probe.

So the gap is exactly:

```lean
noncomputable def genericInstance (env : VEnv) (hwf : env.WF) (U : Nat) :
    GenericInstance env U
```

---

## 2. Field-by-field generalization table

Discharge classes, per the commission's taxonomy:
**(a)** literal-name computation (`decide`/`native_decide` freshness,
classify tables, rule inventories); **(b)** structural transport (the
d(n)→d(n+1) functor); **(c)** genuinely semantic content (iota-site replay,
`IsDefEqStrong` chains, eta registry).

### 2.1 `Params` (11 fields, `Experimental/SExpr.lean:24-45`)

| Field | Fixture discharge | Class | Generic source | Verdict |
|---|---|---|---|---|
| `env` | literal `d0Env`/`d1Env` | — | the given `env` | trivial |
| `henv : env.Ordered` | `d0Env_wf.ordered` (D0:87) | (b) | `VEnv.WF.ordered`, `Theory/Typing/EnvLemmas.lean:88` | **exists** |
| `univs` | parameter | — | the given `U` | trivial |
| `classify` | literal `match` tables: `natClassify` D0:114, `d0Classify` D0:122, `d1Classify` D1:248; freshness by `native_decide` (D0:57-63, D1:68-92) | (a) | per-rung `blockClassify` from the certificate inventory (`gen.families`, `gen.flatCtors`, `gen.recursors`), `.symb 0` per def rung, unioned along the history | **needs new lemma** (G4a): inventory exists, packaging as `Name → Option Classification` does not |
| `Pat` | inductive, one constructor per rule: `D1Pat` = `old`/`defnA`/`defnB` (D1:245-270) | (a)+(b) | `AssembledPat`-shaped union: `gen.IotaPat` per block rung, `.const c` per def rung | mechanical induction |
| `pat_simple` | case split → `IotaPat.pat_simple` / `⟨.defn c, rfl⟩` (D0:272) | (b) | `AssembledPat.pat_simple`, `InductivePatternEnv.lean:529` | **exists** |
| `pat_wf` | `natPat_wf` D0:256 by `decide` on the literal table; D1 lifts via `d0Classify_agrees` D1:279 | (a) | pattern heads are `gen.ruleRecName c` / `c.ctor.raw.name` **by construction** | **needs new lemma** (G4b): true by definition; *no lemma states it* |
| `pat_uniq` | `d0Pat_uniq` D0:313 / `d1Pat_uniq` D1:374, via literal-name `*_inter_*_none` lemmas | (a) | `AssembledPat.pat_uniq` under `ExtSeparation`, `InductivePatternEnv.lean:570` | **needs new lemma** (G5): union law exists (landed today); `ExtSeparation`-from-history does not |
| `pat_app_l` | `d0Pat_app_l` D0:340 → `toPattern_app_l` | (b) | `AssembledPat.pat_app_l` (side-condition free) | **exists** |
| `pat_app_l_uniq` | as `pat_uniq` | (a) | `AssembledPat.pat_app_l_uniq` under `ExtSeparation` | **needs G5** |
| `pat_app_uniq` | as `pat_uniq` | (a) | `AssembledPat.pat_app_uniq` under `ExtSeparation` | **needs G5** |

Note the generality limit of today's engine: `AssembledPat` is parameterized
by **one** `gen : source.BlockGenerationChecked` plus a list of
`CertifiedExtension`s (`InductivePatternEnv.lean:520-526`). An arbitrary
history has many blocks. Two routes: (i) encode every non-distinguished block
as `CertifiedExtension`s via `gen.iotaExtension` (`:347`) — available, but
then those rungs lose the `IotaPat` payload structure the `Semantic` fields
want; (ii) generalize `AssembledPat` to a list of blocks. (ii) is cleaner and
is the same proof: the cross-term engine
`HeadSep.inter_subpattern_none` (`:160`) is already fully generic in both
patterns.

### 2.2 `Params.Semantic` (6 fields, `Experimental/SExpr.lean:1964-2050`)

| Field | Fixture discharge | Class | Generic source | Verdict |
|---|---|---|---|---|
| `structureEta` | **VACUOUS in all three instances** — `natSemantic` D0:5570, `d0Semantic` D0:6880, `d1Semantic` D1:2621, each `(*_no_structEta rule hreg).elim` | never exercised | Theory's primitive `IsDefEqStrong.structEta` (`Theory/Typing/Strong.lean:74-87`) has **no SExpr counterpart** | **BLOCKED on interface repair** (§5.3, G8) |
| `ctor` | `natCtor` D0:1597 (hand-built bundle + strong Pi-tower typing for `Nat.zero`/`Nat.succ`, ~110 lines of support at D0:1485-1605); `d0Ctor` D0:6033 and `d1Ctor` D1:1885 are pure transports | (c) then (b) | per-block: the constructor's type IS a Pi telescope ending in `I args`, pinned by the generation certificate | mechanical-ish, **but `hu0` is BLOCKED** (§5.1, G6) |
| `defn` | `d0Defn` D0:6116, `d1Defn` D1:1758 — case split on the registry, each case a hand-built `IsDefEqStrong.defn` (`d1MutADefStrong` D1:1709, `d1MutBDefStrong` :1651) | (b)+(c), fully templated | per-def rung: `.const c` pattern → `IsDefEqStrong.defn` with `action` from `IsDefEq.extra` at the closed constant | **mechanical induction**; one genuinely new sub-case: `uvars > 0` (every fixture ran `uvars = 0`, cf. `List.length_eq_zero_iff.mp hlen` at D1:1785) |
| `iotaRule` | `natIotaRule` D0:1943 / `d1IotaRule` D1:1466 — `Classical.choice` of a nonemptiness proof recovering the descriptor from the pattern | (a)+(b) | `IotaPat.recover` (`InductivePattern.lean:624`) + `gen.rule` / `gen.rule_uvars` | **mechanical** |
| `iotaSite` | `natIotaSite_nonempty` D0:1954-2578 (624 lines), `d0IotaSite_nonempty` D0:6199-6829 (630), `d1IotaSite_nonempty` D1:1930-2569 (639) — hand-built typed telescopes; **all three end `dfs := []; checked := by simp`** (D0:2569-2572, D0:6825-6828) | (c) | per-block site construction from `gen`'s rule shape | **partially BLOCKED**: `captureSpine` needs a new generic telescope lemma (hard but plausible); `checked` is BLOCKED for parameters/indices (§5.2, G7) |
| `registered` | `natRegistered` D0:5497 → `natZeroRuleRegistered` D0:3930 / `natSuccRuleRegistered` D0:5325, each on top of ~700 lines of `*RuleBodyStrong` / `*RuleAppliedStrong` / `*RuleActionSound` / `*RuleLocalStrong` / `*RulePrefixesStrong` (D0:2898-5497). `d1Registered` D1:1821 transports old rules and hand-builds the two new ones | (c) | per-rung: def/mutualDef rungs reduce to `defn`; block rungs need a generic `lamN`-tower descent + `IotaReductionSite.action` | **needs new lemma** (substantial); inherits G7 |

**Reading of the table.** Only two `Semantic` fields (`iotaRule`, `defn`) are
mechanical. `ctor` and `registered` are per-block semantic content with a
uniform shape that a generation-certificate-parameterized lemma can capture.
`iotaSite` and `structureEta` are the walls. The ~2000 fixture lines behind
`registered` are *not* irreducible: they are the concrete instance of a
uniform recipe — descend the registered rule's `lamN` binder tower with
`lamDF`, expose the redex, build the local `Pattern.Action` by applying the
closed registered equation to the binder spine and beta-collapsing. The
generic engine for the last step already exists and is kernel-checked:
`Pattern.IotaReductionSite.action` (`Experimental/SExpr.lean:2056-2086`).

**Why `registered` cannot be shortcut.** The tempting route — get the
equality from Theory by `.extra` + `IsDefEq.strong` + `mkS` — is circular:
`IsDefEqStrong.mkS`'s `extra` case *is* `Params.Semantic.registered`
(`Experimental/SExpr.lean:2188-2194`). Likewise its `constDF` case *is*
`Semantic.ctor` (`:2117-2125`) and its constant-unfolding case *is*
`Semantic.defn` (`:2132`). The `Semantic` class is precisely the set of
Theory rules the SExpr judgment has no constructor for.

---

## 3. Construction shape

### 3.1 The induction

`VEnv.WF env := ∃ ds, VEnv.WF' ds env` (`Theory/Typing/Env.lean:67`), and
`VEnv.WF'` (`:57-65`) is an inductive with three constructors: `empty`,
`decl` (one `VDecl.WF env d env'` step), `structEta` (an eta-registry
insertion, *not* a `VDecl`). So the construction is an induction on `WF'`,
producing a `GenericInstance` at each prefix.

Caveat measured during this pass: **the only consumer of `VEnv.WF'` in the
entire tree is `VEnv.WF.ordered`** (`EnvLemmas.lean:88`). There is no
inversion lemma, no `VDecl.names` function, and no "the history's declared
names are pairwise distinct". Every history-level fact this construction
wants is new (§6).

### 3.2 The per-step extension theorem — the D-ladder transport, abstracted

**The D-ladder's transport pattern literally is the induction step.** The
correspondence, checked against `SExprParamsD1.lean`:

| D1 artifact | Abstracted role |
|---|---|
| `d0ToD1Level` (D1:484) / `d0ToD1Expr` (D1:514) | the syntax functor — `Step.univs_eq` + `transportExpr` |
| `d0Env_le_d1Env` (D1:134) | `Step.le` |
| `D1Pat.old` (D1:245ff) | `Step.pat_mono` |
| `d1Pat_at_old_const` (D1:988) | `Step.pat_old` — a *new* rule never fires at an *old* constant |
| `d0StrongToD1` (D1:1004-1107) | `Step.strong` — the judgment transport, one case per `IsDefEqStrong` constructor |
| `d1Ctor` / `d1Defn` / `d1Registered` old cases | the transport half of each `Semantic` field |
| `d1MutADefStrong` / `d1MutBDefStrong` / `d1IotaSite_nonempty` | the **new** half — this is what varies per rung |

Probe §G2 types this as `Step P₀ P₁` + `StepObligations P₀ P₁ st` +
`Semantic.step`.

**What varies, precisely:** only `StepObligations` — the five new-content
fields (`newCtor`, `newDefn`, `newRegistered`, `newIota`, `newStructEta`).
Everything else in a rung is boilerplate that is currently rewritten by hand.

### 3.3 Two structural findings that shrink the work

**(i) The syntax functor is generic and is now banked.** `SExpr` is
`[Params]`-indexed (`Experimental/SExpr.lean:217`), so a history induction
cannot keep one syntax type across rungs — hence the four hand-rolled
functors in D0/D1 (`natToD0Expr`/`d0ToNatExpr` D0:583/596,
`d0ToD1Expr`/`d1ToD0Expr` D1:514/527) plus their roundtrip and commutation
lemmas: D0:547-1140 and D1:475-1120, ≈1200 lines total. All of it depends
only on `univs` agreeing. The probe defines `transportLevel` /
`transportExpr` / `transportLevel_transportLevel` generically, all at
`[propext, Quot.sound]`. **This is a strict, immediate win for D2/D3/D4
regardless of the milestone decision.**

**(ii) The pattern registry needs no transport at all.** `Pattern.RHS` and
`Pattern.Check` (`Theory/Typing/Pattern.lean:96,101`) are `Params`-*independent*
— `.fixed` carries a `VExpr`, not an `SExpr`. So `Step.pat_mono` keeps `r`
fixed. (Checked while elaborating the probe; the first draft wrongly assumed
a `transportRHS` was needed.)

### 3.4 Per-declaration-kind content

| `VDecl` kind | New content | Difficulty |
|---|---|---|
| `.axiom`, `.opaque` | none: adds a constant, no defeq, no pattern; `classify` extends by `none`, so `CtorBundle.IsCtor` stays uninhabited and `Semantic.ctor` is vacuous at it | trivial (G3-axiom) |
| `.example` | environment unchanged | trivial |
| `.def` | one `.const c` pattern (`classify c = some (.symb 0)`, so **not** a ctor and no `hu0` exposure), one defeq; `defn` + `registered` both from `IsDefEqStrong.defn` | mechanical; new sub-case `uvars > 0` (G3-def) |
| `.mutualDef` | as `.def`, per block element, with the forward references D1 already exercised | mechanical (D1 is the template) |
| `.quot` | four constants + `quotDefEq` | **BLOCKED** ×2: `hu0` (§5.1) and stuck-`Quot` injectivity for `quotCheck` (§5.2) |
| `.induct` (3 variants) | block inventory into `classify`; `gen.IotaPat` into `Pat`; `Semantic.ctor` for the new constructors; `iotaRule`/`iotaSite`/`registered` for the new rules | the substantial rung; **BLOCKED** by §5.1 (Prop-sorted blocks) and §5.2 (parameterised/indexed blocks) |
| `WF'.structEta` | `Semantic.structureEta` becomes non-vacuous | **BLOCKED** (§5.3) |

---

## 4. Freshness and decidability

The fixtures discharge every name obligation by computation on literal names:
`native_decide` freshness (D0:57-63, D1:68-92, D1:2767-2812), `decide`
classify-table lookups (D0:256-290), literal rule inventories
(`natRulePattern_inventory` D0:167). An arbitrary history has no literals, so
each of these must come from a WF invariant instead.

**What exists.**

* Freshness is a *consequence of a successful step*: `VEnv.addConst`
  (`Theory/VEnv.lean:184-187`) returns `none` when the name is taken, and
  `VEnv.addConst_fresh` (`Theory/Typing/Lemmas.lean:197`) extracts it.
* Transaction traces carry the block form:
  `ctorFold_spec` (`Theory/Typing/InductiveLemmas.lean:13828`) gives
  `env₀ ≤ env₁ ∧ (∀ c ∈ cs, env₁.constants c.name = some _) ∧
  (∀ c ∈ cs, env₀.constants c.name = none)`;
  `AddInductBlockGenerationTrace.{family,ctor,rec}_fresh` (`:14091, 14123,
  14153`) and their `_lookup` siblings (`:14103, 14137, 14167`).
* Backward monotonicity: `VEnv.LE.constants_none` (`Lemmas.lean:220`).
* Intra-block distinctness: `blockGeneratedNames_nodup`
  (`Theory/Typing/InductivePattern.lean:222`), `recName_ne_ctorName` (`:478`),
  `flatCtors_name_inj` (`:456`), `families_name_inj` (`:443`),
  `ruleRecName_inj` (`:502`), `rulePattern_inj` (`:519`).

**What does not exist** (each is a named obligation in §7):

1. Any inversion of `VEnv.WF'` / `VDecl.WF`; no `VDecl.names`; no "the
   history's declared names are pairwise distinct".
2. `addConsts_fresh` / `addConsts_nodup` — freshness extracted from a
   *successful* `addConsts` (only the converse `exists_addConsts`,
   `EnvLemmas.lean:27`, exists).
3. `addQuot_fresh`.
4. **"A rule pattern's head names are names this block introduces."** True by
   construction (`rulePattern` = `.iota (gen.ruleRecName c) _ c.ctor.raw.name _`,
   `InductivePattern.lean:287`) but stated nowhere. This is the bridge from
   transaction freshness to `ExtSeparation`.
5. `nodup_parts` (`InductivePattern.lean:430`) is `private`, so the three
   component distinctness facts are unavailable outside that file.
6. `(gen.recursors).map (·.name) ⊆ blockGeneratedNames`.

**And the hypothesis genuinely is necessary.** `separation_is_necessary`
(`InductivePatternEnv.lean:760`) proves the certificate-free union law false
— a `defn` extension named after a rule's recursor breaks `pat_uniq`. So
`ExtSeparation` must be *derived* from freshness, not dropped. The only
discharge in the tree today is `decide`-based on a literal fixture
inventory (`patTree_quot_separation`, `InductivePatternFixtures.lean:216`).

**Verdict:** the freshness half is *mechanical but not small* — six new
lemmas plus one visibility change, all pure bookkeeping over existing
traces, no semantics. It is attackable today.

---

## 5. The three walls

### 5.1 `hu0` and Prop-typed constructors — the interface repair (recommended)

**What `hu0` does.** `CtorBundle.hu0 : u ≠ .zero`
(`Experimental/SExpr.lean:1897`) has exactly two consumption sites:

* `LE_Interp.build_spine`, constructor case (`ShapeLogRel.lean:9208-9251`).
  `hu0` is threaded down the constructor's Pi telescope (`:9230-9242`) so
  that the inductive-type-headed result can be realized at a **non-bot**
  sort shape (`:9246`, `.sort (decide_eq_true hu0 ▸ TShape.sort_eqv.1)`),
  which is what makes the `.ctor'`/`.indTy` observation available.
* the nullary-constructor case of adequacy's constant case
  (`ShapeLogRelAdequacy.lean:6339`), same role, to obtain `LRS.IndTyHead`.

(`Params.ctor_ty`, `SExpr.lean:2353-2368`, only re-exports the field.)

**How bad it is.** `SLevel` is semantic (`SExpr.lean:50`), so `u ≠ .zero`
means "nonzero at *some* valuation". The violation is therefore exactly the
*identically*-Prop instantiations. That is still fatal:

* A constructor's type ends in its inductive type. If the inductive is
  `Prop`-sorted, the whole Pi type has sort `imax _ 0 = 0` — **at every level
  instantiation**. So every constructor of `Eq`, `And`, `Or`, `Exists`,
  `False`, `Acc`, … violates `hu0` unconditionally.
* Universe-polymorphic constructors (`Quot.mk`, `PUnit.unit`, `PProd.mk`)
  violate it at their Prop instantiations — the D1 record's case.

**Banked** (`hu0_impossible_at_prop`, probe §G6): under type uniqueness — the
`LogRel.ContextualRawTypeUniq` the joint L4L-16/17 route already delivers —
*no* choice of `CtorBundle` satisfies `hu0` for a Prop-typed constructor, because
the bundle's own equality `Γ ⊢ mkInst ls ci.type ≡ F.rhs ls : .sort F.u`
pins `F.u` against the type's Prop typing. The wall is intrinsic.

**Can the classifier dodge it?** No. `Params.pat_wf` forces
`classify ctor = some (.ctor arity)` for any pattern in `Pat`
(`quotPattern_forces_ctor_classification`, D1:2755, is the kernel-checked
instance of this). Keeping a Prop inductive's iota patterns *out* of `Pat`
then leaves `Semantic.registered` with no route for its rules: `.extra`
needs a `Pattern.Action`, hence membership; `defn` is constant-patterns only;
and `proofIrrel` closes only rules whose *type* is a Prop, which fails for
every large-eliminating Prop inductive (`Eq.rec`, `Acc.rec`, `False.rec`
have Type-valued motives).

> **2026-08-20:** the repair below is **REFUTED** — 2026-08-15, executed
> probe `plans/probes/probeA1-hu0.lean`. The ADQ consumption site is indeed
> free, but `build_spine`'s post-deletion statement is FALSE for Prop-sorted
> ctor-classified pattern-argument heads: `hu0` is the syntactic mirror of
> `WShape.HasType.proofIrrel`'s `.indTy` non-Prop-sortedness requirement.
> Resolving the Prop wall needs a Matches/classification-level design (a
> Prop branch, or excluding Prop-recursor iota patterns from `Pat`).

**Recommended repair — and it is cheaper than both candidates in the D1 note.**
The D1 record offers "typing-conditional `hu0`" or "restrict `Semantic.ctor`'s
level quantification". Both add interface surface. **Simply delete `hu0`.**
Justification, **banked** (`propWitness_of_ctor_zero`, probe §G6): in the
`F.u = .zero` branch the Prop typing of the constructor's type is *free* from
the bundle's own equality (`hF.hasType.1` after rewriting). So no new field
and no new premise is needed — the two consumption sites simply case-split on
`F.u = .zero`, and the zero branch has all the evidence it needs.

The residual obligation is confined to those two sites, and it has two
possible resolutions. A cheap discriminating probe settles which
(`propCtor_membership`, probe §G6a):

* **(i) absorption** — in the Prop branch the observation degenerates to
  `.bot` and the goal closes by the relation's bot law. The machinery is
  adjacent: the same match at `ShapeLogRelAdequacy.lean:6325` already has a
  `| bot hm => exact (LR Γ₀).bot hm` arm.
* **(ii) contradiction** — a Prop-typed constant cannot carry a ctor-shaped
  `LE_Interp` membership at all, in which case `hu0` was never load-bearing
  and the deletion is free.

(ii) is the ideal outcome and should be probed first. **This repair is
16C′-owner territory and is the single highest-leverage unblock in this
document** — it is also what unblocks D1's parked quotient half.

### 5.2 Iota check discharge — the unrecorded wall

`Semantic.iotaSite` must produce `Pattern.IotaReductionSite`, whose `dfs` /
`defeqs` / `checked` fields (`Experimental/SExpr.lean:1772-1774`) assert that
the rule's `Check` obligations hold **at the matched redex**.

`gen.ruleCheck` (`Theory/Typing/InductivePattern.lean:563-582`) emits:
* one `.defeq` per `source.nparams`, comparing the constructor-side parameter
  argument with the recursor-side parameter argument; and
* one `.defeq` per result index, comparing the recursor-side index argument
  with the computed index tower applied to the captures.

At an arbitrary matched redex these are **not syntactic identities** — they
are forced only semantically, by the major premise's type. `IotaTyping`
(`SExpr.lean:1700-1714`) supplies two typings of the constructor application:
at `ctorResultType` (from `ctorSpine`) and at the recursor's major-premise
domain (from `recSpine`). Reconciling them gives `I recParams recIdx ≡
I ctorParams ctorIdx`; extracting the argument equalities from that needs
**injectivity of a stuck inductive-type application** — Church–Rosser /
L4L-18A′ strength, exactly the strength the D1 record cites as obstruction 3
for `quotCheck`.

**The semantic side cannot help.** The logical relation realizes `indTy`
arguments at `.bot` (`ShapeLogRel.lean:9244`,
`rargs := .replicate args.length .bot`), so it tracks no argument information
at all by design.

**This is unrecorded and it is a D2 risk, not just a generic-construction
risk.** All three fixture sites end `dfs := []; checked := by simp` because
Nat has neither parameters nor indices. D2's remaining work is List and the
PatTree/PatForest blocks — List has one parameter, so D2 hits this the moment
its `Semantic` plumbing is attempted. **Recommendation: raise this into the
D2 line of the completion plan now**, before D2 spends effort discovering it.

Staged as `iotaCheck_param` in probe §G7.

### 5.3 `Semantic.structureEta` — the SExpr layer is asked to prove a primitive

Established facts (verified this pass):

* `VStructEta.WF` (`Theory/Typing/Basic.lean:115-133`) has exactly two
  fields, `familyType_closed` and `rebuild_hasType`. It is a **subject-
  reduction certificate only**; it contains no equality.
* The eta equation enters *exclusively* through the primitive constructors
  `VEnv.IsDefEq.structEta` (`Theory/Typing/Basic.lean:59-69`) and
  `IsDefEqStrong.structEta` (`Theory/Typing/Strong.lean:74-87`), both gated
  on `env.structEtas rule`.
* SExpr's `IsDefEq` (`SExpr.lean:1260-1281`) and `IsDefEqStrong` (`:1905`)
  have **no** `structEta` constructor — which is exactly why
  `Params.Semantic.structureEta` and `Params.StructureEtaSound` (`:1796`)
  exist as fields.
* Every discharge in the tree is vacuous (`natStructureEtaSound` D0:1141,
  `d0StructureEtaSound` D0:5594, `d1StructureEtaSound` D1:1123, and the three
  `Semantic.structureEta` fields).
* `VEnv.hasStructureEta_of_registry` (`Theory/Projection.lean:2076`) is
  registry *consumption*, not derivation; its own doc comment
  (`Projection.lean:1790-1802`) says the equality is what the certificates do
  not derive.
* No concrete `VStructEta.WF` value is constructed anywhere in the repo.

So the field asks the SExpr judgment to *prove* an equation that Theory
*postulates*. Structure eta does not follow from iota at a stuck major (that
is the whole point of the rule), so it is not derivable as stated.

**Encouraging counterweight:** the semantic ingredient is already built.
`Shape.ctor'` (`ShapeLogRel.lean:817`) collapses an all-bot
structure-constructor shape to `.bot` **exactly when `IsStruct c`**, i.e.
when `classify c = some (.etaCtor ..)` (`:815`), and `WShape` carries the
`IsStruct n → ListNonZero l` side condition (`:856`, `:974`). The
`.etaCtor` classification (`SExpr.lean:10`) is otherwise unused in the entire
tree. The design clearly anticipated eta support and stopped one layer short.

**Recommended route:** mirror Theory's primitive on the SExpr side (add
`structEta` to `IsDefEq`/`IsDefEqStrong`), prove the adequacy case from the
`Shape.ctor'` bot-collapse, and `Semantic.structureEta` then becomes a
transport like every other field. This is a scoped sub-development with
existing semantic support — but it is an interface change to a module the
16C′ owner is actively editing, so it is a decision, not a task.

---

## 6. Why conditional instances do not reach the target

The commission asks whether a partial instance (non-Prop fragment) could
suffice, "checking what `sort_invS`'s proof actually consumes from
`Semantic.ctor`". Measured answer: **it consumes it everywhere, and the
restriction cannot be moved onto the goal.**

* `sort_invS` (`ShapeLogRelAdequacy.lean:7064-7076`) calls
  `SExpr.sort_inv` → `sort_inv_of_adequacy` with `LR.adequacyAt Γ hΓ 1`.
  `adequacyAt` is a theorem about **all** derivations at that level, so its
  proof needs the constant case — hence `Semantic.ctor` and `hu0` — for
  every ctor-classified constant in the environment, whatever the goal.
* `sort_invS` also calls `(h.strong Params.henv hΓ).mkS`, and
  `IsDefEqStrong.mkS`'s `constDF` case (`SExpr.lean:2117-2125`) instantiates
  `Semantic.ctor` at **every** constant node of the *input* derivation, which
  is arbitrary — a derivation of `sort u ≡ sort v` may route through any
  constant in the environment.

So a conditional instance yields exactly: *for any WF environment with no
Prop-sorted inductive, no Prop-instantiable constructor, no parameterised or
indexed inductive, and an empty eta registry, `sort_inv` holds.* That is the
D0–D2 fixture ladder restated, not a public theorem. It is worth having as a
**staging artifact** (it is what D2/D3 actually deliver), but it must not be
sold as closing `IsDefEqU.sort_inv`.

Probe §G9 (`NoPropCtor`, `conditionalInstance`) types this so the claim is
stated rather than implied.

---

## 7. Staged obligations, as Lean statements

All are typed in `plans/probes/probeG-generic-instance.lean` (green).
"Banked" = proved there at `[propext, Quot.sound]`.

| # | Obligation | Probe name | Difficulty | Depends on |
|---|---|---|---|---|
| **R0** | promotion is one instance wide | `sort_inv_of_generic` | **BANKED** | — |
| **R1** | generic syntax transport (replaces ~1200 lines of D-ladder boilerplate) | `transportLevel`, `transportExpr`, `transportLevel_transportLevel` | **LANDED 2026-08-15** (`Experimental/SExprTransport.lean`) | — |
| **R2** | the per-step extension theorem | `Step`, `StepObligations`, `Semantic.step` | **LANDED 2026-08-15** (`Experimental/SExprGenericReplay.lean`, the generic iota replay engine) | R1 |
| **R3** | `classify` + `pat_wf` from block certificates | `blockClassify`, `blockClassify_pat_wf` | needs new lemma (combinatorial) | — |
| **R4** | `ExtSeparation` from the history | `extSeparation_intra`, `extSeparation_inter` | needs 6 new lemmas + `nodup_parts` visibility; pure bookkeeping | §4 gaps |
| **R5** | `defn` rung at `uvars > 0` | `step_def` | small, mechanical | R2 |
| **R6** | `hu0` deletion + Prop branch at 2 sites | `propWitness_of_ctor_zero` (**BANKED**), `hu0_impossible_at_prop` (**BANKED**), `propCtor_membership` (open) | **interface decision** — 16C′ owner | — |
| **R7** | iota check discharge for parameters/indices | `iotaCheck_param` | **BLOCKED — L4L-18A′ strength** | stuck-application injectivity |
| **R8** | SExpr `structEta` primitive + adequacy case | `structureEta_underivable` | **interface decision**, then a scoped development | — |
| **R9** | generic `registered` tower descent + generic `iotaSite` | `genericInstance_of_WF'`, `step_induct` | the bulk (weeks) | R2–R6, R7, R8 |

**Attackable today, with no interface decision and no other milestone:**
R3, R4, R5. (R1 and R2 LANDED 2026-08-15 —
`Experimental/SExprTransport.lean`, `Experimental/SExprGenericReplay.lean`,
commit "experimental: land generic syntax transport and the generic iota
replay engine".) Together with the landed R1+R2 these are the whole
non-semantic half of the construction.

**Blocked on a decision the 16C′ owner must take:** R6, R8.
**Blocked on another milestone:** R7 (18A′).

---

## 8. Recommendation for the pending plan decision

**Neither option in the plan's question is right; take the third door.**

1. **Not D4's endpoint.** D4 is currently written as "registered structure
   eta from the L4L-15B registry" — but §5.3 shows that line is itself an
   interface change plus a scoped semantic development, not plumbing. Loading
   the generic construction (which contains two further walls, one of them
   18A′-strength) onto D4's exit makes D4 unschedulable.

2. **Not a named 16E step.** 16E is measured in days
   (`plans/l4l-16e-promotion-map.md`). This is months, and two of its
   obligations are interface decisions in modules 16E does not own.

3. **Not "conditional".** §6: a conditional instance cannot reach
   `IsDefEqU.sort_inv`, only the fixture-shaped restatement.

**Do this instead** — the same move already recommended for `weakN_iff` in
`plans/l4l-16-weakn-design.md`:

* **Re-scope the arbitrary-environment `IsDefEqU.sort_inv` promotion off the
  16E gate** into a new named milestone (suggested: **L4L-16F "live
  instance"**, or fold into the L4L-19 slot). 16E then exits on: the SExpr
  statements going clean, the module moves, the guard re-pins, and the
  *fixture-instantiated* endpoints (`d0SortInvS`, `d1SortInvS`, D2…).
* **16E's allowlist exit count does not shrink by the `sort_inv` row.**
  Combined with the `weakN_iff` re-scope already recommended (which lands 16E
  at 19 rather than 17), the `sort_inv` row stays on the list too. The
  promotion map's gate table needs that correction before execution.
* **Add R1+R2 to the D-ladder now, ahead of D2.** They are banked/mechanical
  and they delete a repeated ~600-line-per-rung cost that D2, D3 and D4 would
  otherwise each pay again. *(Executed — LANDED 2026-08-15.)*
* **Raise §5.2 (iota check discharge) into the D2 line immediately.** D2's
  remaining work is "registry consumption along D1's template"; that template
  never exercised `checked`, and List's parameter check will stop it. Better
  to know before the effort starts.
* **Put R6 (`hu0` deletion) in front of the 16C′ owner as a one-line
  decision** with the banked evidence: the Prop witness is free, so the
  repair costs a case split at two sites and no new interface surface; and it
  simultaneously unblocks D1's parked quotient half. *(2026-08-20: REFUTED
  by executed probe `plans/probes/probeA1-hu0.lean` — see the §5.1 note.)*

**Two-strikes note.** No formalization attempt in this pass hit a second
strike: R0, R1 and the two `hu0` facts went through on the first attempt; the
one draft error (assuming `Pattern.RHS` needed transport) was corrected by
the elaborator on the first re-run, and the correction *reduced* the staged
work. Everything else in §7 is stated, not attempted, by design.

---

## 9. Appendix — measured citations

Interfaces: `Experimental/SExpr.lean:24-45` (`Params`), `:1890-1897`
(`CtorBundle`, `hu0`), `:1964-2050` (`Params.Semantic`), `:2056-2086`
(`IotaReductionSite.action`), `:2091-2194` (`IsDefEqStrong.mkS`),
`:2200-2235` (`closedHasTypeStrong`), `:1700-1774` (`IotaTyping`,
`IotaRule`, `IotaReductionSite`), `:1783-1791` (`Pattern.Action`),
`:1796-1807` (`StructureEtaSound`), `:217` (`SExpr` is `[Params]`-indexed).

Gate: `Experimental/ShapeLogRelAdequacy.lean:7001-7076`.

`hu0` consumers: `Experimental/ShapeLogRel.lean:9208-9251`,
`Experimental/ShapeLogRelAdequacy.lean:6325-6345`.

Fixtures: `SExprParamsD0.lean:514-546` (`natParams`/`d0Params`),
`:1141-1145`, `:1597`, `:1954-2578`, `:2898-5497`, `:5497-5591`
(`natSemantic`), `:6033`, `:6116`, `:6146`, `:6199-6829`, `:6875-6903`
(`d0Semantic`), `:6904-6952`. `SExprParamsD1.lean:245-474` (pattern layer),
`:475-1120` (transport), `:1121-2651` (semantic certificates),
`:2703-2755` (quot obstruction record), `:2755` (forcing lemma).

Union engine: `Theory/Typing/InductivePatternEnv.lean:109-236` (head
separation), `:249-336` (`CertifiedExtension`, `quot`), `:347` (`iotaExtension`),
`:520-546` (`AssembledPat`), `:558-567` (`ExtSeparation`), `:570-748` (four
laws), `:760` (`separation_is_necessary`).

Block certificates: `Theory/Typing/InductivePattern.lean:222` (`blockGeneratedNames_nodup`),
`:287-289` (`rulePattern`), `:430` (private `nodup_parts`), `:443-524`
(injectivity family), `:541-582` (`captureArgs`, `ruleRHS`, `ruleCheck`),
`:607-726` (`IotaPat` + four laws).

Circularity trap: `Theory/Typing/InductivePatternWF.lean:543` and its axiom
pin at `:942-949`; `Theory/Typing/UniqueTyping.lean:167` (`IsDefEqU.trans`),
`:13` (`uniq`), `Theory/Typing/Injectivity.lean:11` (`sort_inv`, sorried).

History: `Theory/Typing/Env.lean:19-67`, `Theory/VDecl.lean:22-29`,
`Theory/Typing/EnvLemmas.lean:88` (`WF.ordered`).

Structure eta: `Theory/VEnv.lean:21-64, 170-199`,
`Theory/Typing/Basic.lean:59-69, 115-133`, `Theory/Typing/Strong.lean:74-87`,
`Theory/Projection.lean:1790-1802, 2076-2091`,
`Experimental/ShapeLogRel.lean:815-856, 974`.

Freshness: `Theory/VEnv.lean:184-187`, `Theory/Typing/Lemmas.lean:197, 220`,
`Theory/Typing/EnvLemmas.lean:27`, `Theory/Typing/InductiveLemmas.lean:13828,
14091-14180`, `Theory/Typing/InductivePatternFixtures.lean:216-234`.
