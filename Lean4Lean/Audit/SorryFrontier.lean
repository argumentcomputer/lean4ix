import Lean4Lean.Theory
import Lean4Lean.Theory.ConstructorValidityFixtures
import Lean4Lean.Theory.Inductive
import Lean4Lean.Theory.InductiveFixtures
import Lean4Lean.Theory.Literals
import Lean4Lean.Theory.LocalContext
import Lean4Lean.Theory.Meta
import Lean4Lean.Theory.MutualInductiveFixtures
import Lean4Lean.Theory.Projection
import Lean4Lean.Theory.Quot
import Lean4Lean.Theory.SingletonParity
import Lean4Lean.Theory.Typing.Basic
import Lean4Lean.Theory.Typing.ChurchRosser
import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Typing.HeadReduction
import Lean4Lean.Theory.Typing.InductiveCertificate
import Lean4Lean.Theory.Typing.InductiveLemmas
import Lean4Lean.Theory.Typing.Injectivity
import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.Meta
import Lean4Lean.Theory.Typing.Pattern
import Lean4Lean.Theory.Typing.QuotLemmas
import Lean4Lean.Theory.Typing.Strong
import Lean4Lean.Theory.Typing.UniqueTyping
import Lean4Lean.Theory.VDecl
import Lean4Lean.Theory.VEnv
import Lean4Lean.Theory.VExpr
import Lean4Lean.Theory.VLevel
import Lean4Lean.Verify
import Lean4Lean.Verify.Axioms
import Lean4Lean.Verify.Environment
import Lean4Lean.Verify.Environment.Basic
import Lean4Lean.Verify.Environment.CandidateIdentityReplay
import Lean4Lean.Verify.Environment.ConstructorValidation
import Lean4Lean.Verify.Environment.ConstructorValidityMatrix
import Lean4Lean.Verify.Environment.ConstructorValidityReplay
import Lean4Lean.Verify.Environment.DeepNestedReplay
import Lean4Lean.Verify.Environment.Elimination
import Lean4Lean.Verify.Environment.EliminationFixtures
import Lean4Lean.Verify.Environment.EliminationFixturesCommon
import Lean4Lean.Verify.Environment.EliminationFixturesEdges
import Lean4Lean.Verify.Environment.EliminationFixturesEq
import Lean4Lean.Verify.Environment.EliminationFixturesEqNat
import Lean4Lean.Verify.Environment.EliminationFixturesNat
import Lean4Lean.Verify.Environment.EliminationFixturesOrAnd
import Lean4Lean.Verify.Environment.EliminationFixturesSmall
import Lean4Lean.Verify.Environment.IndexedVecCandidate
import Lean4Lean.Verify.Environment.IndexedVecConsReplay
import Lean4Lean.Verify.Environment.IndexedVecConstructors
import Lean4Lean.Verify.Environment.IndexedVecOuterReplay
import Lean4Lean.Verify.Environment.IndexedVecSemanticReplay
import Lean4Lean.Verify.Environment.InductiveFixtures
import Lean4Lean.Verify.Environment.InductiveReplayMatrix
import Lean4Lean.Verify.Environment.Lemmas
import Lean4Lean.Verify.Environment.MutualInductiveFixtures
import Lean4Lean.Verify.Environment.Normalization
import Lean4Lean.Verify.Environment.NormalizationMatrix
import Lean4Lean.Verify.Environment.SingletonParityMatrix
import Lean4Lean.Verify.Environment.SingletonParityReplay
import Lean4Lean.Verify.EquivManager
import Lean4Lean.Verify.Expr
import Lean4Lean.Verify.Level
import Lean4Lean.Verify.LocalContext
import Lean4Lean.Verify.NameGenerator
import Lean4Lean.Verify.TypeChecker
import Lean4Lean.Verify.TypeChecker.Basic
import Lean4Lean.Verify.TypeChecker.InferType
import Lean4Lean.Verify.TypeChecker.IsDefEq
import Lean4Lean.Verify.TypeChecker.Reduce
import Lean4Lean.Verify.TypeChecker.WHNF
import Lean4Lean.Verify.Typing.ConditionallyTyped
import Lean4Lean.Verify.Typing.Expr
import Lean4Lean.Verify.Typing.Lemmas
import Lean4Lean.Verify.VLCtx

/-!
# Lean4Lean sorry frontier

Guards the trusted verification frontier: the exact set of `Lean4Lean.Theory.*`
and `Lean4Lean.Verify.*` declarations that are allowed to depend on `sorry`.
Progress shrinks the allowlist; a new, moved, or renamed sorry fails the build.

Unlike a source-token grep, this asks the compiled environment which
declarations directly reference `sorryAx` (the elaborated form of a `sorry`
token), so it can never drift from Lean's lexer over comments, string/char
literals, or nested block comments. Attribution is by SOURCE MODULE via
`getModuleIdxFor?`, so a declaration is charged to the file that defines it even
when it sits in a foreign namespace (e.g. `Lean.Level.isEquiv_wf` lives in
`Lean4Lean.Verify.LevelStd`).

The audited surface is exactly the modules reachable from this file's imports:
importing a `Theory`/`Verify` module here is what brings it into scope. A sorry
in a proof module not (transitively) imported here is not seen, so the import
block above lists the complete `Theory`/`Verify` file tree explicitly (imports
already reachable transitively are harmless). When files are added or renamed,
regenerate it with

  { printf 'import %s\n' Lean4Lean.Theory Lean4Lean.Verify; \
    find Lean4Lean/Theory Lean4Lean/Verify -name '*.lean' \
      | sed 's/\.lean$//; s#/#.#g; s/^/import /'; } | LC_ALL=C sort -u

`Lean4Lean.Experimental.*` is parked proof work outside the trusted surface and
is intentionally not imported.

Runs as a build-time `run_cmd`, not an executable: `lake build` of this module
is the whole check.

Because this audit is what guards the frontier, every allowlisted declaration
that would log Lean's "declaration uses `sorry`" warning carries `set_option
warn.sorry false in` at its definition, which keeps `lake build --wfail` clean
for downstream consumers. (The `#guard_msgs`-pinned fixtures below need no
annotation: their warning is captured by the pinned message.) Suppressing the
warning costs no safety here, since the check reads `sorryAx` out of the
environment: a sorry that is new, moved, or renamed still fails this build, and
one added without the annotation also still fails `--wfail`.
-/

open Lean Lean.Elab.Command

namespace Lean4Lean.Audit

/-- Constants referenced directly by a declaration's type or value, following
the cases of `Lean.collectAxioms`. The `Lean.` qualifiers are load-bearing:
this file imports lean4lean's kernel, which defines its own `Name`/
`ConstantInfo` that would otherwise shadow Lean's inside this namespace. -/
private def directConstants : Lean.ConstantInfo → Array Lean.Name
  | .axiomInfo v => v.type.getUsedConstants
  | .defnInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .thmInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .opaqueInfo v => v.type.getUsedConstants ++ v.value.getUsedConstants
  | .quotInfo _ => #[]
  | .ctorInfo v => v.type.getUsedConstants
  | .recInfo v => v.type.getUsedConstants
  | .inductInfo v => v.type.getUsedConstants ++ v.ctors

/-- Prefixes whose modules make up the audited verification surface. -/
private def surfacePrefixes : Array Lean.Name := #[`Lean4Lean.Theory, `Lean4Lean.Verify]

/-- The checked-in sorry frontier, tiered as in the fork's upstream-gaps plan:
S (missing specification), P (stated but sorried, blocked on S), V (checker
verification, blocked on S/P), R (research-grade metatheory, upstream-driven). -/
private def allowlist : Array Lean.Name := #[
  -- Tier V — checker verification, blocked on Tier P
  -- (NormLevel.subsumption_eval and the primed-comparator soundness were
  -- proved on the formalization line, 2026-08-05/07, and left the frontier;
  -- the v4.33 reconciliation then absorbed upstream's stronger level
  -- verification.)
  -- After upstream #28 (v4.33 reconciliation), `addDecl.WF` is proved for
  -- every declaration kind except `inductDecl`, whose case is the remaining
  -- sorry (L4L-19B territory).
  `Lean4Lean.addDecl.WF,
  -- Upstream's front-end trust boundary for the syntactic primitive-definition
  -- recognizer (Verify/Environment/Boundaries.lean), added by #28 at the
  -- v4.33 reconciliation.
  `Lean4Lean.checkPrimitiveDef.WF,
  -- `ProjectionReady`/registered `StructureEtaReady` transport across the
  -- front-end environment extensions (Verify/Environment/Extension.lean):
  -- upstream's proved v4.33 declaration chains do not establish these fork
  -- obligations on `VContext`; the transport proofs are L4L-19B content. The
  -- mutual-block entry is the compiled recursive functional of
  -- `VEnvAt.addAxioms`.
  `Lean4Lean.VEnvAt.addAxioms._f,
  `Lean4Lean.addConstCore.WF,
  `Lean4Lean.addDef.WF,
  `Lean4Lean.addMutualBlock.WF,
  `Lean4Lean.addUnsafeDef.WF,
  -- Quotient initialization (Verify/Environment.lean): upstream's v4.33
  -- proof was vacuous via the fork-refutable `TrEnv'.no_inductInfo`; the
  -- constructive connection to the Theory quotient transaction is L4L-19B
  -- content.
  `Lean4Lean.addQuot.WF,
  -- v4.33 reconciliation repair debt: the exact alignment-run fixture's
  -- `build.eq_def` stepping no longer elaborates; the closed checker-run
  -- statement is unchanged (Verify/Environment/InductiveFixtures.lean).
  `Lean4Lean.InductiveReplayFixtures.aliasFormerAlignmentRun,
  `Lean4Lean.TypeChecker.Inner.reduceRecursor.WF,
  -- Tier R — research-grade metatheory (upstream-driven, not scheduled)
  `Lean4Lean.VEnv.IsDefEqU.sort_inv,
  `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified,
  `Lean4Lean.VEnv.IsDefEqU.sort_forallE_inv,
  `Lean4Lean.VEnv.IsDefEqU.weakN_iff,
  `Lean4Lean.VEnv.WF.registeredStructureHeadInversion,
  `Lean4Lean.VEnv.NormalEq.parRed,
  -- Tier F — deliberately kernel-rejected inductive fixtures. Elaborator error
  -- recovery admits the invalid `inductive` with `sorryAx`, so the constant
  -- carries a sorry dependency even though the source has no `sorry` token
  -- (which is why the old source-token scan never saw these). Not proof debt.
  `Lean4Lean.InductiveFixtures.KernelDifferential.KernelRejectRecDomain,
  `Lean4Lean.InductiveFixtures.KernelDifferential.KernelRejectRecIndex,
  -- The L4L-05 nearest-kernel negatives (Theory/ConstructorValidityFixtures.lean)
  -- are the same pattern: `#guard_msgs`-pinned rejections whose recovered
  -- constants carry `sorryAx`. Not proof debt.
  `Lean4Lean.InductiveFixtures.KernelDifferential.L4L05FamilyNonrecursive,
  `Lean4Lean.InductiveFixtures.KernelDifferential.L4L05FamilyProof,
  `Lean4Lean.InductiveFixtures.KernelDifferential.L4L05NestedNegative,
  `Lean4Lean.InductiveFixtures.KernelDifferential.L4L05RecursiveDependency]

/-- Declarations in the audited surface that directly reference `sorryAx`. -/
private def observedFrontier (env : Lean.Environment) : Array Lean.Name := Id.run do
  let moduleNames := env.allImportedModuleNames
  let mut observed := #[]
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let mod := moduleNames[idx.toNat]!
      if surfacePrefixes.any (·.isPrefixOf mod) && (directConstants info).contains ``sorryAx then
        observed := observed.push name
  return observed

run_cmd do
  let env ← getEnv
  let observed := observedFrontier env
  let expected : Std.HashSet Lean.Name := allowlist.foldl (·.insert ·) {}
  let observedSet : Std.HashSet Lean.Name := observed.foldl (·.insert ·) {}
  let added := observed.filter (!expected.contains ·) |>.qsort Name.lt
  let removed := allowlist.filter (!observedSet.contains ·) |>.qsort Name.lt
  if added.isEmpty && removed.isEmpty then
    logInfo m!"Lean4Lean sorry frontier OK ({observed.size} known sorries)"
  else
    let fmt (hdr : String) (ns : Array Name) : String :=
      if ns.isEmpty then "" else
        s!"\n{hdr}\n" ++ String.intercalate "\n" (ns.toList.map (s!"  {·}"))
    throwError m!"Lean4Lean sorry frontier changed.\
      {fmt "New sorries (not in allowlist):" added}\
      {fmt "Expected sorries now absent (update the allowlist):" removed}\n\
      Edit the allowlist in Lean4Lean/Audit/SorryFrontier.lean only when the \
      trusted frontier intentionally changes."

end Lean4Lean.Audit
