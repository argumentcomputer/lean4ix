# L4L-16D extension template and D3 migration (formerly the D0 slice map)

D0a/D0b, D1, and D2 landed (`SExprParamsD0.lean` / `SExprParamsD1.lean` /
`SExprParamsD2.lean`); the pre-implementation D0 planning (snapshot,
inventory, sourcing table, gaps, task list) was removed 2026-08-20 — git
history has it.

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
