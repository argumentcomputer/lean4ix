import Lean4Lean
-- Keep the two deprecated proof-helper import paths compiling in clean proof builds.
import Lean4Lean.Std.PersistentHashMap
import Lean4Lean.Std.SMap
import Lean4Lean.Theory
import Lean4Lean.Theory.ConstructorValidityFixtures
import Lean4Lean.Theory.Inductive
import Lean4Lean.Theory.InductiveFixtures
import Lean4Lean.Theory.LevelSat
import Lean4Lean.Theory.Literals
import Lean4Lean.Theory.LocalContext
import Lean4Lean.Theory.Meta
import Lean4Lean.Theory.MutualInductiveFixtures
import Lean4Lean.Theory.NestedInductive
import Lean4Lean.Theory.NestedInductiveFixtures
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
import Lean4Lean.Theory.Typing.InductivePattern
import Lean4Lean.Theory.Typing.InductivePatternEnv
import Lean4Lean.Theory.Typing.InductivePatternFixtures
import Lean4Lean.Theory.Typing.InductivePatternWF
import Lean4Lean.Theory.Typing.Injectivity
import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.Meta
import Lean4Lean.Theory.Typing.NestedInductiveLemmas
import Lean4Lean.Theory.Typing.NestedTransport
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
import Lean4Lean.Verify.Environment.Boundaries
import Lean4Lean.Verify.Environment.CandidateIdentityReplay
import Lean4Lean.Verify.Environment.Checker
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
import Lean4Lean.Verify.Environment.Extension
import Lean4Lean.Verify.Environment.IndexedVecCandidate
import Lean4Lean.Verify.Environment.IndexedVecConsReplay
import Lean4Lean.Verify.Environment.IndexedVecConstructors
import Lean4Lean.Verify.Environment.IndexedVecOuterReplay
import Lean4Lean.Verify.Environment.IndexedVecSemanticReplay
import Lean4Lean.Verify.Environment.InductiveFixtures
import Lean4Lean.Verify.Environment.InductiveReplayMatrix
import Lean4Lean.Verify.Environment.Lemmas
import Lean4Lean.Verify.Environment.MutualInductiveFixtures
import Lean4Lean.Verify.Environment.NestedReplay
import Lean4Lean.Verify.Environment.NestedRepresentation
import Lean4Lean.Verify.Environment.NestedTransformation
import Lean4Lean.Verify.Environment.Normalization
import Lean4Lean.Verify.Environment.NormalizationMatrix
import Lean4Lean.Verify.Environment.Quotient
import Lean4Lean.Verify.Environment.Readiness
import Lean4Lean.Verify.Environment.SingletonParityMatrix
import Lean4Lean.Verify.Environment.SingletonParityReplay
import Lean4Lean.Verify.EquivManager
import Lean4Lean.Verify.Expr
import Lean4Lean.Verify.Level
import Lean4Lean.Verify.LevelStd
import Lean4Lean.Verify.LocalContext
import Lean4Lean.Verify.Name
import Lean4Lean.Verify.NameGenerator
import Lean4Lean.Verify.NormLt
import Lean4Lean.Verify.QSort
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
import Main

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
  -- every declaration kind except safe `inductDecl`, whose case is the
  -- remaining sorry (L4L-19B territory). Unsafe inductives are explicitly
  -- outside the supported declaration class.
  `Lean4Lean.addDecl.WF,
  -- Upstream's front-end trust boundary for the syntactic primitive-definition
  -- recognizer (Verify/Environment/Boundaries.lean), added by #28 at the
  -- v4.33 reconciliation.
  `Lean4Lean.checkPrimitiveDef.WF,
  -- The five readiness transports and constructive quotient initialization
  -- closed together on 2026-08-21 (Lane V1/V2); the v4.33 alignment-run
  -- fixture repair (V6) closed later that day.
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

/-! ## Custom project-axiom reachability

The sorry allowlist above handles admitted proof bodies.  The audits below pin
the explicit contracts declared by `Verify/Axioms.lean` and `PtrEq.lean`, then
compute complete transitive axiom closures for the supported Theory and Verify
surfaces, the shipped library, and the CLI.  They fail on an inventory change,
duplicate stable ID, any change to an individual root's exact closure,
forbidden root dependency, reachable forbidden contract, or a dead
custom/compiler axiom that should be deleted.  Manifest axioms are also
forbidden from the global simp set: each consumer must name the exact bridge it
uses.
-/

/-- Release-policy classification for a transitive axiom dependency. -/
inductive AxiomDisposition where
  | logicalBaseline
  | admittedProof
  | rejectedFixture
  | compilerDecision
  | narrowPlatformContract
  | transitionalBridge
  | forbidden
  deriving BEq, Repr

def AxiomDisposition.label : AxiomDisposition → String
  | .logicalBaseline => "logical-baseline"
  | .admittedProof => "admitted-proof"
  | .rejectedFixture => "rejected-fixture"
  | .compilerDecision => "compiler-decision"
  | .narrowPlatformContract => "platform-contract"
  | .transitionalBridge => "transitional-bridge"
  | .forbidden => "forbidden"

/-- Stable metadata for one custom project axiom. -/
structure ProjectAxiom where
  stableId : String
  declaration : Lean.Name
  disposition : AxiomDisposition
  reason : String
  owner : String
  deriving Repr

private def ProjectAxiom.platform (stableId : String)
    (declaration : Lean.Name) (reason : String) : ProjectAxiom where
  stableId := stableId
  declaration := declaration
  disposition := .narrowPlatformContract
  reason := reason
  owner := "TRUST/platform"

private def ProjectAxiom.bridge (stableId : String)
    (declaration : Lean.Name) (reason : String) : ProjectAxiom where
  stableId := stableId
  declaration := declaration
  disposition := .transitionalBridge
  reason := reason
  owner := "TRUST/retire"

private def opaqueOperation :=
  "Bridge from an opaque kernel operation to its total model."

private def cachedMetadata :=
  "Bridge from cached metadata to structural recursion."

private def persistentContract :=
  "Opaque persistent-container implementation equation."

/-- Exact custom-axiom inventory.  IDs survive declaration moves: a rename
updates only `declaration`, rather than allocating a new identity. -/
def projectAxiomManifest : Array ProjectAxiom := #[
  .platform "L4L-PTR-001" `Lean4Lean.ptrEqConstantInfo_eq
    "Pointer-equality implication for kernel constant metadata.",
  .platform "L4L-PTR-002" `Lean4Lean.ptrEqExpr_eq
    "Pointer-equality implication for kernel expressions.",

  .bridge "L4L-EXPR-001" `Lean.Expr.abstractRange_eq opaqueOperation,
  .bridge "L4L-EXPR-002" `Lean.Expr.abstract_eq opaqueOperation,
  .bridge "L4L-EXPR-003" `Lean.Expr.eqv_eq
    "Bridge from cached expression equality to its structural model.",
  .bridge "L4L-EXPR-004" `Lean.Expr.hasLooseBVar_eq cachedMetadata,
  .bridge "L4L-EXPR-005" `Lean.Expr.instantiate1_eq opaqueOperation,
  .bridge "L4L-EXPR-006" `Lean.Expr.instantiateRange_eq opaqueOperation,
  .bridge "L4L-EXPR-007" `Lean.Expr.instantiateRevRange_eq opaqueOperation,
  .bridge "L4L-EXPR-008" `Lean.Expr.instantiateRev_eq opaqueOperation,
  .bridge "L4L-EXPR-009" `Lean.Expr.instantiate_eq opaqueOperation,
  .bridge "L4L-EXPR-010" `Lean.Expr.looseBVarRange_eq cachedMetadata,
  .bridge "L4L-EXPR-011" `Lean.Expr.lowerLooseBVars_eq opaqueOperation,
  .platform "L4L-EXPR-012" `Lean.Expr.mkAppData_eq
    "Pinned expression-cache bit layout used by metadata proofs.",
  .platform "L4L-EXPR-013" `Lean.Expr.mkData_eq
    "Pinned expression-cache bit layout used by metadata proofs.",
  .bridge "L4L-EXPR-014" `Lean.Expr.replace_eq opaqueOperation,
  .bridge "L4L-EXPR-015" `Lean.Expr.abstract_fvars_shape
    "Opaque free-variable abstraction preserves the recursive expression skeleton.",

  .bridge "L4L-LEVEL-001" `Lean.Level.hasMVar_eq cachedMetadata,
  .bridge "L4L-LEVEL-002" `Lean.Level.hasParam_eq cachedMetadata,
  .platform "L4L-LEVEL-003" `Lean.Level.instLawfulBEqLevel
    "Lawfulness contract for the C++ level equality implementation.",
  .bridge "L4L-LEVEL-004" `Lean.Level.isExplicitSubsumedAux_eq
    "Bridge from the partial kernel helper to its total model.",
  .platform "L4L-LEVEL-005" `Lean.Level.mkData_eq
    "Pinned level-cache bit layout used by metadata proofs.",
  .bridge "L4L-LEVEL-006" `Lean.Level.normalize_eq
    "Bridge from partial level normalization to its total copy.",

  .bridge "L4L-PARRAY-001" `Lean.PersistentArray.WF.toList'_push
    persistentContract,
  .bridge "L4L-PHMAP-001" `Lean.PersistentHashMap.findAux_isSome persistentContract,
  .bridge "L4L-PHMAP-002" `Lean.PersistentHashMap.WF.find?_eq persistentContract,
  .bridge "L4L-PHMAP-003" `Lean.PersistentHashMap.WF.toList'_insert
    persistentContract,
  .bridge "L4L-SYNTAX-001" `Lean.Syntax.structEq_eq
    "Bridge from partial syntax equality to structural recursion."]

/-! ## Repaired contract signatures

These guards pin the exact domains of every contract implicated by the
upstream trust audit.  The name-based manifest would not notice a same-name
axiom being widened again; these checks do.  The new shape-only abstraction
bridge is pinned alongside the ten repaired assumptions because it is the
replacement used by callers outside `abstract_eq`'s honest equality domain.
-/

/--
info: @PersistentArray.WF.toList'_push : ∀ {α : Type u_1} {arr : PersistentArray α},
  arr.WF → ∀ (x : α), (arr.push x).toList' = arr.toList' ++ [x]
-/
#guard_msgs in
#check @Lean.PersistentArray.WF.toList'_push

/--
info: @Level.mkData_eq : ∀ {h : UInt64} {d : Nat} {mv hp : Bool},
  d < 2 ^ 24 → Level.mkData h d mv hp = Level.mkData' h d mv hp
-/
#guard_msgs in
#check @Lean.Level.mkData_eq

/--
info: Level.hasParam_eq : ∀ (l : Level), l.hasParam = l.hasParam'
-/
#guard_msgs in
#check @Lean.Level.hasParam_eq

/--
info: Level.hasMVar_eq : ∀ (l : Level), l.hasMVar = l.hasMVar'
-/
#guard_msgs in
#check @Lean.Level.hasMVar_eq

/--
info: @Expr.mkData_eq : ∀ {h : UInt64} {br : Nat} {d : UInt32} {fv ev lv lp : Bool},
  br ≤ 2 ^ 20 - 1 → Expr.mkData h br d fv ev lv lp = Expr.mkData' h br d fv ev lv lp
-/
#guard_msgs in
#check @Lean.Expr.mkData_eq

/--
info: Expr.looseBVarRange_eq : ∀ (e : Expr), e.BVarBounded → e.looseBVarRange = e.looseBVarRange'
-/
#guard_msgs in
#check @Lean.Expr.looseBVarRange_eq

/--
info: Expr.instantiate_eq : ∀ (e : Expr) (subst : Array Expr),
  (e.looseBVarRange' = 0 ∨ ∀ (a : Expr), a ∈ subst → a.looseBVarRange' = 0) →
    e.instantiate subst = e.instantiateList subst.toList
-/
#guard_msgs in
#check @Lean.Expr.instantiate_eq

/--
info: @Expr.instantiateRange_eq : ∀ {start stop : Nat} (e : Expr) (subst : Array Expr),
  start ≤ stop → stop ≤ subst.size → e.instantiateRange start stop subst = e.instantiate (subst.extract start stop)
-/
#guard_msgs in
#check @Lean.Expr.instantiateRange_eq

/--
info: @Expr.instantiateRevRange_eq : ∀ {start stop : Nat} (e : Expr) (subst : Array Expr),
  start ≤ stop →
    stop ≤ subst.size → e.instantiateRevRange start stop subst = e.instantiateRev (subst.extract start stop)
-/
#guard_msgs in
#check @Lean.Expr.instantiateRevRange_eq

/--
info: Expr.abstract_eq : ∀ (e : Expr) (xs : List FVarId),
  xs = [] ∨ e.looseBVarRange' = 0 → xs.Nodup → e.abstract { toList := List.map Expr.fvar xs } = e.abstractList xs
-/
#guard_msgs in
#check @Lean.Expr.abstract_eq

/--
info: Expr.abstract_fvars_shape : ∀ (e : Expr) (xs : List FVarId),
  (e.abstract { toList := List.map Expr.fvar xs }).AbstractFVarShape e
-/
#guard_msgs in
#check @Lean.Expr.abstract_fvars_shape

/-! ## Exact release-root axiom policy

These are the non-project leaves in the current transitive release closure.
The logical baseline is accepted at every root.  `sorryAx` is accepted only on
the proof surfaces and is pinned more precisely by the direct-reference
allowlist above.  Six axiom declarations created by error recovery are accepted
only as the pinned negative Theory fixtures.  Compiler-generated decision
certificates are accepted only in Verify; their opaque generated names are
intentionally exact so adding, removing, or renumbering a
`native_decide`/`bv_decide` use forces review.
-/

private def logicalBaselineAxioms : Array Lean.Name := #[
  `propext,
  `Classical.choice,
  `Quot.sound]

private def admittedProofAxioms : Array Lean.Name := #[`sorryAx]

/-- Error recovery represents these six `#guard_msgs`-pinned, deliberately
kernel-rejected inductives as axiom declarations.  They are negative fixtures,
not usable Theory assumptions. -/
private def rejectedFixtureAxioms : Array Lean.Name := #[
  `Lean4Lean.InductiveFixtures.KernelDifferential.KernelRejectRecDomain,
  `Lean4Lean.InductiveFixtures.KernelDifferential.KernelRejectRecIndex,
  `Lean4Lean.InductiveFixtures.KernelDifferential.L4L05FamilyNonrecursive,
  `Lean4Lean.InductiveFixtures.KernelDifferential.L4L05FamilyProof,
  `Lean4Lean.InductiveFixtures.KernelDifferential.L4L05NestedNegative,
  `Lean4Lean.InductiveFixtures.KernelDifferential.L4L05RecursiveDependency]

private def quotientPrivateName (suffix : Lean.Name) : Lean.Name :=
  Lean.Name.appendCore
    (.num `_private.Lean4Lean.Verify.Environment.Quotient 0) suffix

private def nestedReplayPrivateName (suffix : Lean.Name) : Lean.Name :=
  Lean.Name.appendCore
    (.num `_private.Lean4Lean.Verify.Environment.NestedReplay 0) suffix

private def compilerDecisionAxioms : Array Lean.Name := #[
  `Lean.Expr.mkAppData_looseBVarRange._native.bv_decide.ax_1_8,
  `Lean.Expr.mkData_looseBVarRange._native.bv_decide.ax_1_9,
  `Lean.Level.mkData_depth._native.bv_decide.ax_1_9,
  `Lean.Level.mkData_hasMVar._native.bv_decide.ax_1_8,
  `Lean.Level.mkData_hasParam._native.bv_decide.ax_1_8,
  `Lean4Lean.CompleteInductiveReplay.singletonCandidateReplayMatrix._native.native_decide.ax_1,
  `Lean4Lean.DeepNestedReplayFixtures.biBoxObservedShape._native.native_decide.ax_1_1,
  `Lean4Lean.DeepNestedReplayFixtures.deepKTarget._native.native_decide.ax_1_1,
  `Lean4Lean.DeepNestedReplayFixtures.deepNestedC_some._native.native_decide.ax_1_1,
  `Lean4Lean.DeepNestedReplayFixtures.deepRecursors_eq._native.native_decide.ax_1_1,
  `Lean4Lean.DeepNestedReplayFixtures.deepRules_eq._native.native_decide.ax_1_1,
  `Lean4Lean.InductiveReplayFixtures.andAlignment06._native.native_decide.ax_1,
  `Lean4Lean.InductiveReplayFixtures.andEliminationResult06_isOk._native.native_decide.ax_1_1,
  `Lean4Lean.InductiveReplayFixtures.andKTargetSingleton06._native.native_decide.ax_1,
  `Lean4Lean.InductiveReplayFixtures.andSingletonExecution06._native.native_decide.ax_1,
  `Lean4Lean.InductiveReplayFixtures.cvmExecutionResult_isOk._native.native_decide.ax_1_1,
  `Lean4Lean.InductiveReplayFixtures.emptyAlignment06C._native.native_decide.ax_1,
  `Lean4Lean.InductiveReplayFixtures.emptyEliminationResult06C_isOk._native.native_decide.ax_1_1,
  `Lean4Lean.InductiveReplayFixtures.eqAlignment06._native.native_decide.ax_1,
  `Lean4Lean.InductiveReplayFixtures.eqEliminationResult06_isOk._native.native_decide.ax_1_1,
  `Lean4Lean.InductiveReplayFixtures.eqKTargetSingleton06._native.native_decide.ax_1,
  `Lean4Lean.InductiveReplayFixtures.natElimAlignmentResult06_isSome._native.native_decide.ax_1_1,
  `Lean4Lean.InductiveReplayFixtures.natElimLevelResult06_isOk._native.native_decide.ax_1_1,
  `Lean4Lean.InductiveReplayFixtures.natKTargetAlignmentResult06_isSome._native.native_decide.ax_1_1,
  `Lean4Lean.InductiveReplayFixtures.natKTargetResult06_isOk._native.native_decide.ax_1_1,
  `Lean4Lean.InductiveReplayFixtures.orAlignment06._native.native_decide.ax_1,
  `Lean4Lean.InductiveReplayFixtures.orEliminationResult06_isOk._native.native_decide.ax_1_1,
  `Lean4Lean.InductiveReplayFixtures.prbExecutionResult_isOk._native.native_decide.ax_1_1,
  `Lean4Lean.InductiveReplayFixtures.punitAlignment06C._native.native_decide.ax_1,
  `Lean4Lean.InductiveReplayFixtures.punitEliminationResult06C_isOk._native.native_decide.ax_1_1,
  `Lean4Lean.InductiveReplayFixtures.punitLargeSingleton06C._native.native_decide.ax_1,
  `Lean4Lean.InductiveReplayFixtures.smallSourceAlignment06._native.native_decide.ax_1,
  `Lean4Lean.InductiveReplayFixtures.smallSourceEliminationResult06_isOk._native.native_decide.ax_1_1,
  `Lean4Lean.MutualInductiveReplayFixtures.indexedTreeBlockEliminationAlignment._native.native_decide.ax_1,
  `Lean4Lean.MutualInductiveReplayFixtures.indexedTreeBlockEliminationShapeResult_isOk._native.native_decide.ax_1_1,
  `Lean4Lean.MutualInductiveReplayFixtures.indexedTreeBlockGenerationShapeResult_isOk._native.native_decide.ax_1_1,
  `Lean4Lean.MutualInductiveReplayFixtures.indexedTreeBlockRecursorShapeResult_isOk._native.native_decide.ax_1_1,
  `Lean4Lean.MutualInductiveReplayFixtures.indexedTreeCandidateDeclaredInfosMulti._native.native_decide.ax_1_1,
  `Lean4Lean.MutualInductiveReplayFixtures.indexedTreeCandidateIdentityNormalization._native.native_decide.ax_1_3,
  `Lean4Lean.MutualInductiveReplayFixtures.indexedTreeCandidateIdentitySemantic._native.native_decide.ax_1,
  `Lean4Lean.MutualInductiveReplayFixtures.indexedTreeCandidatePostReadiness._native.native_decide.ax_1_1,
  `Lean4Lean.MutualInductiveReplayFixtures.indexedTreeCandidateStaging._native.native_decide.ax_1,
  `Lean4Lean.MutualInductiveReplayFixtures.indexedTreeCandidateTerminals._native.native_decide.ax_1_1,
  `Lean4Lean.MutualInductiveReplayFixtures.indexedTreeConstructorTargets_exact._native.native_decide.ax_1_1,
  `Lean4Lean.MutualInductiveReplayFixtures.indexedTreeConstructorValidationResult_isOk._native.native_decide.ax_1_1,
  `Lean4Lean.MutualInductiveReplayFixtures.indexedTreeFamilyValidationResult_isOk._native.native_decide.ax_1_1,
  `Lean4Lean.MutualInductiveReplayFixtures.indexedTreeGeneratedRecursorInfos_match._native.native_decide.ax_1_1,
  `Lean4Lean.MutualInductiveReplayFixtures.indexedTreeKernelLevelParams._native.native_decide.ax_1_1,
  `Lean4Lean.MutualInductiveReplayFixtures.indexedTreeLeafKernelLevelParams._native.native_decide.ax_1_1,
  `Lean4Lean.MutualInductiveReplayFixtures.indexedTreeListConsKernelLevelParams._native.native_decide.ax_1_1,
  `Lean4Lean.MutualInductiveReplayFixtures.indexedTreeListKernelLevelParams._native.native_decide.ax_1_1,
  `Lean4Lean.MutualInductiveReplayFixtures.indexedTreeListNilKernelLevelParams._native.native_decide.ax_1_1,
  `Lean4Lean.MutualInductiveReplayFixtures.indexedTreeNodeKernelLevelParams._native.native_decide.ax_1_1,
  `Lean4Lean.MutualInductiveReplayFixtures.treeBlockEliminationAlignment._native.native_decide.ax_1,
  `Lean4Lean.MutualInductiveReplayFixtures.treeBlockEliminationShapeResult_isOk._native.native_decide.ax_1_1,
  `Lean4Lean.MutualInductiveReplayFixtures.treeBlockGenerationShapeResult_isOk._native.native_decide.ax_1_1,
  `Lean4Lean.MutualInductiveReplayFixtures.treeBlockRecursorShapeResult_isOk._native.native_decide.ax_1_1,
  `Lean4Lean.MutualInductiveReplayFixtures.treeBranchKernelLevelParams._native.native_decide.ax_1_1,
  `Lean4Lean.MutualInductiveReplayFixtures.treeCandidateIdentityNormalization._native.native_decide.ax_1_3,
  `Lean4Lean.MutualInductiveReplayFixtures.treeCandidateIdentitySemantic._native.native_decide.ax_1,
  `Lean4Lean.MutualInductiveReplayFixtures.treeCandidateStaging._native.native_decide.ax_1,
  `Lean4Lean.MutualInductiveReplayFixtures.treeCandidateStaging._native.native_decide.ax_2,
  `Lean4Lean.MutualInductiveReplayFixtures.treeConstructorTargets_exact._native.native_decide.ax_1_1,
  `Lean4Lean.MutualInductiveReplayFixtures.treeConstructorValidationResult_isOk._native.native_decide.ax_1_1,
  `Lean4Lean.MutualInductiveReplayFixtures.treeExecution_shortGenerationShape_rejected._native.native_decide.ax_1_1,
  `Lean4Lean.MutualInductiveReplayFixtures.treeFamilyValidationResult_isOk._native.native_decide.ax_1_1,
  `Lean4Lean.MutualInductiveReplayFixtures.treeGeneratedRecursorInfos_match._native.native_decide.ax_1_1,
  `Lean4Lean.MutualInductiveReplayFixtures.treeKernelLevelParams._native.native_decide.ax_1_1,
  `Lean4Lean.MutualInductiveReplayFixtures.treeLeafKernelLevelParams._native.native_decide.ax_1_1,
  `Lean4Lean.MutualInductiveReplayFixtures.treeListConsKernelLevelParams._native.native_decide.ax_1_1,
  `Lean4Lean.MutualInductiveReplayFixtures.treeListKernelLevelParams._native.native_decide.ax_1_1,
  `Lean4Lean.MutualInductiveReplayFixtures.treeListNilKernelLevelParams._native.native_decide.ax_1_1,
  `Lean4Lean.MutualInductiveReplayFixtures.treeNodeKernelLevelParams._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.nvKTarget09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.nvNestedC._native.native_decide.ax_1,
  `Lean4Lean.NestedReplayFixtures.nvRecursors_eq._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.nvRules_eq._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseEnvironmentInductiveExecutionResult_isOk._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseEnvironmentInductiveExecution_numNested._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseKTarget09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseNestedC._native.native_decide.ax_1,
  `Lean4Lean.NestedReplayFixtures.roseProducedAuxRecInfo_match09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseProducedCtorInfo_match09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseProducedCtorTranslationHeader09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseProducedFamilyPins09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseProducedFamilyTranslationHeader09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseProducedRecInfo_match09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseProducedRecK09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseProducedRestoredInfoRun_isSome._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseRecursors_eq._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseRules_eq._native.native_decide.ax_1_1,
  -- Exact compiler certificates introduced by the flattened RoseTree
  -- generation/certificate/reduction replay.
  `Lean4Lean.NestedReplayFixtures.roseFlatAddFirstRec09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatAddSecondRec09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatAuxConstructorSources09._native.native_decide.ax_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatAuxConstructorSources09._native.native_decide.ax_2,
  `Lean4Lean.NestedReplayFixtures.roseFlatAuxInfoName09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatAuxInfoShape09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatAuxRecType09_eq._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatCandidateFamilySources09._native.native_decide.ax_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatCandidateFamilySources09._native.native_decide.ax_2,
  `Lean4Lean.NestedReplayFixtures.roseFlatCandidateIdentityAnalysis09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatCandidateIdentityCheck09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatCandidateStaging09._native.native_decide.ax_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatCandidateStaging09._native.native_decide.ax_2,
  `Lean4Lean.NestedReplayFixtures.roseFlatCandidateStaging09._native.native_decide.ax_3,
  `Lean4Lean.NestedReplayFixtures.roseFlatCheckedBlockWF09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatCheckedBlockWF09._native.native_decide.ax_1_2,
  `Lean4Lean.NestedReplayFixtures.roseFlatCheckedBlockWF09._native.native_decide.ax_1_3,
  `Lean4Lean.NestedReplayFixtures.roseFlatCheckedBlockWF09._native.native_decide.ax_1_4,
  `Lean4Lean.NestedReplayFixtures.roseFlatCheckedBlockWF09._native.native_decide.ax_1_5,
  `Lean4Lean.NestedReplayFixtures.roseFlatCheckedBlockWF09._native.native_decide.ax_1_6,
  `Lean4Lean.NestedReplayFixtures.roseFlatDecl09_eq._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatDeclaredInfos09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatEliminationAlignment._native.native_decide.ax_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatFamilyConstructorSources09._native.native_decide.ax_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatFirstRecEnv09._native.native_decide.ax_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatGeneratedRecursorEvidence09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatGeneratedRecursorEvidence09._native.native_decide.ax_1_2,
  `Lean4Lean.NestedReplayFixtures.roseFlatGenerationShape._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatKernelAuxFamilyCtors09_eq._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatKernelAuxFamilyType09_eq._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatKernelConsType09_eq._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatKernelFamilyCtors09_eq._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatKernelFamilyType09_eq._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatKernelNilType09_eq._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatKernelNodeType09_eq._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatKernelTypes09_eq._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatMainInfoIsRec09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatMainInfoName09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatMainInfoShape09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatNparams._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatProducedAuxRecTr09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatProducedAuxRecTr09._native.native_decide.ax_1_2,
  `Lean4Lean.NestedReplayFixtures.roseFlatProducedAuxRecTr09._native.native_decide.ax_1_23,
  `Lean4Lean.NestedReplayFixtures.roseFlatProducedAuxRecTr09._native.native_decide.ax_1_25,
  `Lean4Lean.NestedReplayFixtures.roseFlatProducedAuxRecTr09._native.native_decide.ax_1_26,
  `Lean4Lean.NestedReplayFixtures.roseFlatProducedAuxRecTr09._native.native_decide.ax_1_3,
  `Lean4Lean.NestedReplayFixtures.roseFlatProducedAuxRecTr09._native.native_decide.ax_1_4,
  `Lean4Lean.NestedReplayFixtures.roseFlatProducedAuxRecTr09._native.native_decide.ax_1_5,
  `Lean4Lean.NestedReplayFixtures.roseFlatProducedAuxRecTr09._native.native_decide.ax_1_6,
  `Lean4Lean.NestedReplayFixtures.roseFlatProducedAuxRecTr09._native.native_decide.ax_1_7,
  `Lean4Lean.NestedReplayFixtures.roseFlatProducedRecTr09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatProducedRecTr09._native.native_decide.ax_1_2,
  `Lean4Lean.NestedReplayFixtures.roseFlatProducedRecTr09._native.native_decide.ax_1_23,
  `Lean4Lean.NestedReplayFixtures.roseFlatProducedRecTr09._native.native_decide.ax_1_25,
  `Lean4Lean.NestedReplayFixtures.roseFlatProducedRecTr09._native.native_decide.ax_1_26,
  `Lean4Lean.NestedReplayFixtures.roseFlatProducedRecTr09._native.native_decide.ax_1_3,
  `Lean4Lean.NestedReplayFixtures.roseFlatProducedRecTr09._native.native_decide.ax_1_4,
  `Lean4Lean.NestedReplayFixtures.roseFlatProducedRecTr09._native.native_decide.ax_1_5,
  `Lean4Lean.NestedReplayFixtures.roseFlatProducedRecTr09._native.native_decide.ax_1_6,
  `Lean4Lean.NestedReplayFixtures.roseFlatProducedRecTr09._native.native_decide.ax_1_7,
  `Lean4Lean.NestedReplayFixtures.roseFlatRecEnv09._native.native_decide.ax_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatRecType09_eq._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatRecursorFold09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatResultLevelWF._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatRuleBound0_09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatRuleBound1_09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatRuleBound2_09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatRuleCount09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatValidationEnv09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatValidationLparams._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseNestedRecMap09_eq._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseProducedConsReducerAlignment09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseProducedConsSelectedRule09._native.native_decide.ax_1,
  `Lean4Lean.NestedReplayFixtures.roseProducedConsSelectedRuleLookup09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseProducedConsSelectedRuleRhs09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseProducedConsSelectedRuleShape09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseProducedConsSelectedRuleTr09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseProducedConsSelectedRuleTr09._native.native_decide.ax_1_2,
  `Lean4Lean.NestedReplayFixtures.roseProducedMainReducerAlignment09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseProducedMainSelectedRule09._native.native_decide.ax_1,
  `Lean4Lean.NestedReplayFixtures.roseProducedMainSelectedRuleLookup09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseProducedMainSelectedRuleRhs09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseProducedMainSelectedRuleShape09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseProducedMainSelectedRuleTr09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseProducedMainSelectedRuleTr09._native.native_decide.ax_1_2,
  `Lean4Lean.NestedReplayFixtures.roseProducedNilReducerAlignment09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseProducedNilSelectedRule09._native.native_decide.ax_1,
  `Lean4Lean.NestedReplayFixtures.roseProducedNilSelectedRuleLookup09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseProducedNilSelectedRuleRhs09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseProducedNilSelectedRuleShape09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseProducedNilSelectedRuleTr09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseProducedNilSelectedRuleTr09._native.native_decide.ax_1_2,
  -- Exact compiler certificates newly exposed by the live Rose recursor
  -- control-flow and selected-branch semantic surface.
  `Lean4Lean.NestedReplayFixtures.roseEnvironmentInductiveExecution_consReduceRec09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseEnvironmentInductiveExecution_consReduceRecursorWF09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseEnvironmentInductiveExecution_consReduceRecursorWF09._native.native_decide.ax_1_2,
  `Lean4Lean.NestedReplayFixtures.roseEnvironmentInductiveExecution_mainReduceRec09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseEnvironmentInductiveExecution_mainReduceRecursorWF09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseEnvironmentInductiveExecution_mainReduceRecursorWF09._native.native_decide.ax_1_2,
  `Lean4Lean.NestedReplayFixtures.roseEnvironmentInductiveExecution_nilReduceRec09._native.native_decide.ax_1_2,
  `Lean4Lean.NestedReplayFixtures.roseEnvironmentInductiveExecution_nilReduceRecursorWF09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseEnvironmentInductiveExecution_nilReduceRecursorWF09._native.native_decide.ax_1_2,
  `Lean4Lean.NestedReplayFixtures.roseEnvironmentInductiveExecution_notNonRecStructure09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatGeneratedRulesLiteral09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatRule0LhsReflatten09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatRule0RhsReflatten09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatRule0TypeReflatten09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatRule1LhsReflatten09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatRule1RhsReflatten09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatRule1TypeReflatten09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatRule2LhsReflatten09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatRule2RhsReflatten09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseFlatRule2TypeReflatten09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseListGeneratedRulesLiteral09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseListRuleBound0_09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseListRuleBound1_09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseProducedConsApplyRecursorRuleFVarsBelow09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseProducedMainApplyRecursorRuleFVarsBelow09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseProducedNilApplyRecursorRuleFVarsBelow09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseProducedRuleCtorInventories09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseRestoreInterpDefEq09._native.native_decide.ax_1_4,
  `Lean4Lean.NestedReplayFixtures.roseRestoreInterpDefEq09._native.native_decide.ax_1_5,
  `Lean4Lean.NestedReplayFixtures.roseRestoreInterpDefEq09._native.native_decide.ax_1_6,
  `Lean4Lean.NestedReplayFixtures.roseRestoreInterpKeep09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseRestoreInterpKeep09._native.native_decide.ax_1_2,
  `Lean4Lean.NestedReplayFixtures.roseRestoreInterpKeep09._native.native_decide.ax_1_4,
  `Lean4Lean.NestedReplayFixtures.roseRestoreInterpKeep09._native.native_decide.ax_1_6,
  `Lean4Lean.NestedReplayFixtures.roseRestoreInterpKeep09._native.native_decide.ax_1_7,
  `Lean4Lean.NestedReplayFixtures.roseRestoreInterpKeep09._native.native_decide.ax_1_8,
  `Lean4Lean.NestedReplayFixtures.roseRestoreInterpKeep09._native.native_decide.ax_1_9,
  `Lean4Lean.NestedReplayFixtures.roseRestoreInterpListRule0DefEq09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseRestoreInterpListRule0Fixed09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseRestoreInterpListRule1DefEq09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseRestoreInterpListRule1Fixed09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseRestoreInterpRule0BodyMatchedRuntimeOfMajorInjectivity09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseRestoreInterpRule0BodyMatchedRuntimeOfMajorInjectivity09._native.native_decide.ax_1_2,
  `Lean4Lean.NestedReplayFixtures.roseRestoreInterpRule0BodyMatchedRuntimeOfMajorInjectivity09._native.native_decide.ax_1_3,
  `Lean4Lean.NestedReplayFixtures.roseRestoreInterpRule0BodyMatchedRuntimeOfMajorInjectivity09._native.native_decide.ax_1_4,
  `Lean4Lean.NestedReplayFixtures.roseRestoreInterpRule1BodyMatchedRuntimeOfMajorInjectivity09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseRestoreInterpRule1BodyMatchedRuntimeOfMajorInjectivity09._native.native_decide.ax_1_2,
  `Lean4Lean.NestedReplayFixtures.roseRestoreInterpRule1BodyMatchedRuntimeOfMajorInjectivity09._native.native_decide.ax_1_3,
  `Lean4Lean.NestedReplayFixtures.roseRestoreInterpRule2BodyMatchedRuntimeOfMajorInjectivity09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseRestoreInterpRule2BodyMatchedRuntimeOfMajorInjectivity09._native.native_decide.ax_1_2,
  `Lean4Lean.NestedReplayFixtures.roseRestoreInterpRule2BodyMatchedRuntimeOfMajorInjectivity09._native.native_decide.ax_1_3,
  `Lean4Lean.NestedReplayFixtures.roseRestoreInterpValueOfRecursors09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseRestoreInterpValueOfRecursors09._native.native_decide.ax_1_2,
  `Lean4Lean.NestedReplayFixtures.roseRestoreInterpValueOfRecursors09._native.native_decide.ax_1_3,
  `Lean4Lean.NestedReplayFixtures.roseRestoreInterpValueOfRecursors09._native.native_decide.ax_1_4,
  `Lean4Lean.NestedReplayFixtures.roseRestoreInterpValueOfRecursors09._native.native_decide.ax_1_5,
  `Lean4Lean.NestedReplayFixtures.roseRestoreInterpValueOfRecursors09._native.native_decide.ax_1_6,
  `Lean4Lean.NestedReplayFixtures.roseRestoreInterpValueOfRecursors09._native.native_decide.ax_1_7,
  `Lean4Lean.NestedReplayFixtures.roseRestoreInterpValueOfRecursors09._native.native_decide.ax_1_8,
  `Lean4Lean.NestedReplayFixtures.roseRestoreInterp_auxCons09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseRestoreInterp_auxFamily09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseRestoreInterp_auxNil09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseRestoreInterp_auxRec09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseRestoreInterp_listCons09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseRestoreInterp_listFamily09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseRestoreInterp_listNil09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseRestoreInterp_listRec09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseRestoreInterp_mainCtor09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseRestoreInterp_mainFamily09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseRestoreInterp_mainRec09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseRestoredRule0Literal09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseRestoredRule1Literal09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseRestoredRule2Literal09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.roseRecEntries09_eq._native.native_decide.ax_1_1,
  nestedReplayPrivateName
    `Lean4Lean.NestedReplayFixtures.roseProducedConsSelectedRuleFVars09._native.native_decide.ax_1_1,
  nestedReplayPrivateName
    `Lean4Lean.NestedReplayFixtures.roseProducedConsSelectedRuleFVars09._native.native_decide.ax_1_2,
  nestedReplayPrivateName
    `Lean4Lean.NestedReplayFixtures.roseProducedMainSelectedRuleFVars09._native.native_decide.ax_1_1,
  nestedReplayPrivateName
    `Lean4Lean.NestedReplayFixtures.roseProducedMainSelectedRuleFVars09._native.native_decide.ax_1_2,
  nestedReplayPrivateName
    `Lean4Lean.NestedReplayFixtures.roseProducedNilSelectedRuleFVars09._native.native_decide.ax_1_1,
  nestedReplayPrivateName
    `Lean4Lean.NestedReplayFixtures.roseProducedNilSelectedRuleFVars09._native.native_decide.ax_1_2,
  nestedReplayPrivateName
    `Lean4Lean.NestedReplayFixtures.roseRestoredRule0Rhs09._native.native_decide.ax_1_1,
  nestedReplayPrivateName
    `Lean4Lean.NestedReplayFixtures.roseRestoredRule1Rhs09._native.native_decide.ax_1_1,
  nestedReplayPrivateName
    `Lean4Lean.NestedReplayFixtures.roseRestoredRule2Rhs09._native.native_decide.ax_1_1,
  nestedReplayPrivateName
    `Lean4Lean.NestedReplayFixtures.roseStoredConsSelectedRule09._native.native_decide.ax_1,
  nestedReplayPrivateName
    `Lean4Lean.NestedReplayFixtures.roseStoredConsSelectedRuleEqv09._native.native_decide.ax_1_1,
  nestedReplayPrivateName
    `Lean4Lean.NestedReplayFixtures.roseStoredMainSelectedRule09._native.native_decide.ax_1,
  nestedReplayPrivateName
    `Lean4Lean.NestedReplayFixtures.roseStoredMainSelectedRuleEqv09._native.native_decide.ax_1_1,
  nestedReplayPrivateName
    `Lean4Lean.NestedReplayFixtures.roseStoredNilSelectedRule09._native.native_decide.ax_1,
  nestedReplayPrivateName
    `Lean4Lean.NestedReplayFixtures.roseStoredNilSelectedRuleEqv09._native.native_decide.ax_1_1,
  `Lean4Lean.NestedReplayFixtures.RoseFlatCandidateReadiness09.preFamily._native.native_decide.ax_1,
  quotientPrivateName `Lean4Lean.AddQuot.hasPrimitives._native.native_decide.ax_1_1,
  quotientPrivateName `Lean4Lean.AddQuot.hasPrimitives._native.native_decide.ax_1_2,
  quotientPrivateName `Lean4Lean.AddQuot.hasPrimitives._native.native_decide.ax_1_3,
  quotientPrivateName `Lean4Lean.AddQuot.hasPrimitives._native.native_decide.ax_1_4,
  quotientPrivateName `Lean4Lean.VEnvs.WF.addQuot._native.native_decide.ax_1_1,
  quotientPrivateName `Lean4Lean.VEnvs.WF.addQuot._native.native_decide.ax_1_10,
  quotientPrivateName `Lean4Lean.VEnvs.WF.addQuot._native.native_decide.ax_1_2,
  quotientPrivateName `Lean4Lean.VEnvs.WF.addQuot._native.native_decide.ax_1_3,
  quotientPrivateName `Lean4Lean.VEnvs.WF.addQuot._native.native_decide.ax_1_4,
  quotientPrivateName `Lean4Lean.VEnvs.WF.addQuot._native.native_decide.ax_1_5,
  quotientPrivateName `Lean4Lean.VEnvs.WF.addQuot._native.native_decide.ax_1_6,
  quotientPrivateName `Lean4Lean.VEnvs.WF.addQuot._native.native_decide.ax_1_7,
  quotientPrivateName `Lean4Lean.VEnvs.WF.addQuot._native.native_decide.ax_1_8,
  quotientPrivateName `Lean4Lean.VEnvs.WF.addQuot._native.native_decide.ax_1_9]

private def projectAxiomModules : Array Lean.Name :=
  #[`Lean4Lean.Verify.Axioms, `Lean4Lean.PtrEq]

private def observedProjectAxioms (env : Lean.Environment) : Array Lean.Name := Id.run do
  let modules := env.allImportedModuleNames
  let mut observed := #[]
  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let mod := modules[idx.toNat]!
      if projectAxiomModules.contains mod then
        if let .axiomInfo _ := info then
          observed := observed.push name
  return observed

private def formatNames (title : String) (names : Array Lean.Name) : String :=
  if names.isEmpty then ""
  else s!"\n{title}\n" ++
    String.intercalate "\n" (names.toList.map (s!"  {·}"))

run_cmd do
  let env ← getEnv
  let manifestNames := projectAxiomManifest.map (·.declaration)
  let manifestSet : Lean.NameSet := manifestNames.foldl (·.insert ·) {}

  let mut idsSeen : Std.HashSet String := {}
  let mut namesSeen : Lean.NameSet := {}
  let mut duplicateIds := #[]
  let mut duplicateNames := #[]
  for entry in projectAxiomManifest do
    if idsSeen.contains entry.stableId then
      duplicateIds := duplicateIds.push entry.stableId
    idsSeen := idsSeen.insert entry.stableId
    if namesSeen.contains entry.declaration then
      duplicateNames := duplicateNames.push entry.declaration
    namesSeen := namesSeen.insert entry.declaration
  unless duplicateIds.isEmpty do
    throwError m!"Duplicate stable project-axiom IDs: {duplicateIds}"
  unless duplicateNames.isEmpty do
    throwError m!"Duplicate project-axiom declarations: {duplicateNames}"

  let observed := observedProjectAxioms env
  let observedSet : Lean.NameSet := observed.foldl (·.insert ·) {}
  let added := observed.filter (!manifestSet.contains ·) |>.qsort Lean.Name.lt
  let removed := manifestNames.filter (!observedSet.contains ·) |>.qsort Lean.Name.lt
  unless added.isEmpty && removed.isEmpty do
    throwError m!"Lean4Lean custom project-axiom inventory changed.\
      {formatNames "New unclassified project axioms:" added}\
      {formatNames "Manifest entries now absent:" removed}\n\
      Update projectAxiomManifest only for an intentional trust-boundary change."

  let simpTheorems ← liftCoreM Lean.Meta.getSimpTheorems
  let simpAxioms := manifestNames.filter fun name =>
    simpTheorems.lemmaNames.contains (.decl name)
  unless simpAxioms.isEmpty do
    throwError m!"Custom project axioms must not be registered globally as simp lemmas:\
      {formatNames "Globally registered project axioms:" simpAxioms}"

  let modules := env.allImportedModuleNames
  let forbiddenSet : Lean.NameSet := projectAxiomManifest.foldl (init := {}) fun set entry =>
    if entry.disposition == .forbidden then set.insert entry.declaration else set
  let mut allUsed : Lean.NameSet := {}
  let mut theoryUsed : Lean.NameSet := {}
  let mut verifyUsed : Lean.NameSet := {}
  let mut theoryEdges : Array (Lean.Name × Lean.Name) := #[]
  let mut forbiddenEdges : Array (Lean.Name × Lean.Name) := #[]
  let mut theoryDecls : Nat := 0
  let mut verifyDecls : Nat := 0

  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let mod := modules[idx.toNat]!
      let isTheory := `Lean4Lean.Theory |>.isPrefixOf mod
      let isVerify := `Lean4Lean.Verify |>.isPrefixOf mod
      if isTheory || isVerify then
        if isTheory then theoryDecls := theoryDecls + 1
        if isVerify then verifyDecls := verifyDecls + 1
        -- An axiom trivially reaches itself; that does not make it live.
        unless manifestSet.contains name do
          let axioms ← Lean.collectAxioms name
          for axName in axioms do
            if manifestSet.contains axName then
              allUsed := allUsed.insert axName
              if isTheory then
                theoryUsed := theoryUsed.insert axName
                theoryEdges := theoryEdges.push (name, axName)
              if isVerify then
                verifyUsed := verifyUsed.insert axName
              if forbiddenSet.contains axName then
                forbiddenEdges := forbiddenEdges.push (name, axName)

  unless theoryEdges.isEmpty do
    let rows := theoryEdges.map fun (decl, axName) => s!"  {decl} -> {axName}"
    throwError m!"Theory reaches custom project axioms:\n{String.intercalate "\n" rows.toList}"
  unless forbiddenEdges.isEmpty do
    let rows := forbiddenEdges.map fun (decl, axName) => s!"  {decl} -> {axName}"
    throwError m!"A forbidden custom axiom is reachable:\n{String.intercalate "\n" rows.toList}"

  let unreachable := manifestNames.filter (!allUsed.contains ·) |>.qsort Lean.Name.lt
  unless unreachable.isEmpty do
    throwError m!"Custom project axioms are unreachable and must be deleted:\
      {formatNames "Dead project axioms:" unreachable}"

  let reportRows := projectAxiomManifest
    |>.filter (verifyUsed.contains ·.declaration)
    |>.map fun entry =>
      s!"  {entry.stableId} [{entry.disposition.label}] {entry.declaration} \
        ({entry.owner}) — {entry.reason}"
  logInfo m!"Lean4Lean project-axiom reachability OK.\n\
    Theory: {theoryDecls} declarations, {theoryUsed.size} custom axioms.\n\
    Verify: {verifyDecls} declarations, {verifyUsed.size} classified custom axioms.\n\
    {String.intercalate "\n" reportRows.toList}"

private inductive ReleaseSurface where
  | theory
  | verify
  | library
  | cli
  deriving BEq, Repr

private def ReleaseSurface.label : ReleaseSurface → String
  | .theory => "Theory"
  | .verify => "Verify"
  | .library => "Library"
  | .cli => "CLI"

private def releaseSurface? (mod : Lean.Name) : Option ReleaseSurface :=
  if (`Lean4Lean.Theory).isPrefixOf mod then some .theory
  else if (`Lean4Lean.Verify).isPrefixOf mod then some .verify
  else if mod == `Main then some .cli
  else if (`Lean4Lean.Audit).isPrefixOf mod then none
  else if (`Lean4Lean.Experimental).isPrefixOf mod then none
  else if (`Lean4Lean.Tests).isPrefixOf mod then none
  else if (`Lean4Lean).isPrefixOf mod then some .library
  else none

private def axiomDisposition? (name : Lean.Name) : Option AxiomDisposition :=
  if logicalBaselineAxioms.contains name then some .logicalBaseline
  else if admittedProofAxioms.contains name then some .admittedProof
  else if rejectedFixtureAxioms.contains name then some .rejectedFixture
  else if compilerDecisionAxioms.contains name then some .compilerDecision
  else
    (projectAxiomManifest.find? fun entry => entry.declaration == name).map (·.disposition)

private def ReleaseSurface.allows : ReleaseSurface → AxiomDisposition → Bool
  | .theory, .logicalBaseline
  | .theory, .admittedProof
  | .theory, .rejectedFixture => true
  | .verify, .forbidden => false
  | .verify, _ => true
  | .library, .logicalBaseline
  | .library, .narrowPlatformContract
  | .cli, .logicalBaseline => true
  | _, _ => false

/-- The exact transitive axiom closure expected at each release surface.

Most memberships are derived from the classified inventories above, so an
intentional declaration rename has one source of truth.  The library's two
pointer contracts are listed explicitly because the other platform contracts
are Verify-only. -/
private def expectedRootAxioms : ReleaseSurface → Array Lean.Name
  | .theory =>
    logicalBaselineAxioms ++ admittedProofAxioms ++ rejectedFixtureAxioms
  | .verify =>
    logicalBaselineAxioms ++ admittedProofAxioms ++
      projectAxiomManifest.map (·.declaration) ++
      compilerDecisionAxioms
  | .library => #[
    `propext,
    `Classical.choice,
    `Quot.sound,
    `Lean4Lean.ptrEqConstantInfo_eq,
    `Lean4Lean.ptrEqExpr_eq]
  | .cli => logicalBaselineAxioms

private def rootClosureDrift (surface : ReleaseSurface)
    (observed : Lean.NameSet) : Array String := Id.run do
  let expectedNames := expectedRootAxioms surface
  let expectedSet : Lean.NameSet := expectedNames.foldl (·.insert ·) {}
  let unexpected := observed.toArray.filter (!expectedSet.contains ·)
    |>.qsort Lean.Name.lt
  let missing := expectedNames.filter (!observed.contains ·)
    |>.qsort Lean.Name.lt
  let mut rows := #[]
  for name in unexpected do
    rows := rows.push s!"  {surface.label}: unexpected {name}"
  for name in missing do
    rows := rows.push s!"  {surface.label}: missing {name}"
  return rows

private def policyViolations (surface : ReleaseSurface)
    (axioms : Lean.NameSet) : Array String := Id.run do
  let mut rows := #[]
  for name in axioms.toArray.qsort Lean.Name.lt do
    if let some disposition := axiomDisposition? name then
      unless surface.allows disposition do
        rows := rows.push
          s!"  {surface.label}: [{disposition.label}] {name}"
  return rows

private def formatRootReport (surface : ReleaseSurface) (declarations : Nat)
    (axioms : Lean.NameSet) : String :=
  let rows := axioms.toArray.qsort Lean.Name.lt |>.map fun name =>
    let disposition := (axiomDisposition? name).map (·.label) |>.getD "unclassified"
    s!"    [{disposition}] {name}"
  s!"  {surface.label}: {declarations} declarations, {axioms.size} axiom leaves\n" ++
    String.intercalate "\n" rows.toList

run_cmd do
  let env ← getEnv
  let modules := env.allImportedModuleNames
  let mut theoryAxioms : Lean.NameSet := {}
  let mut verifyAxioms : Lean.NameSet := {}
  let mut libraryAxioms : Lean.NameSet := {}
  let mut cliAxioms : Lean.NameSet := {}
  let mut usedAxioms : Lean.NameSet := {}
  let mut theoryDecls := 0
  let mut verifyDecls := 0
  let mut libraryDecls := 0
  let mut cliDecls := 0

  for (name, info) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let mod := modules[idx.toNat]!
      if let some surface := releaseSurface? mod then
        match surface with
        | .theory => theoryDecls := theoryDecls + 1
        | .verify => verifyDecls := verifyDecls + 1
        | .library => libraryDecls := libraryDecls + 1
        | .cli => cliDecls := cliDecls + 1
        let isSourceAxiom := info matches .axiomInfo _
        let axioms ← Lean.collectAxioms name
        for axiomName in axioms do
          match surface with
          | .theory => theoryAxioms := theoryAxioms.insert axiomName
          | .verify => verifyAxioms := verifyAxioms.insert axiomName
          | .library => libraryAxioms := libraryAxioms.insert axiomName
          | .cli => cliAxioms := cliAxioms.insert axiomName
          -- Keep declaration inventory and consumer liveness separate: an
          -- axiom's self-edge makes it part of the shipped surface, but does
          -- not prove that any other declaration uses it.
          if !isSourceAxiom || axiomName != name then
            usedAxioms := usedAxioms.insert axiomName

  let observedSet : Lean.NameSet :=
    (theoryAxioms.toArray ++ verifyAxioms.toArray ++ libraryAxioms.toArray ++
      cliAxioms.toArray).foldl (·.insert ·) {}
  let accepted := logicalBaselineAxioms ++ admittedProofAxioms ++
    rejectedFixtureAxioms ++ compilerDecisionAxioms ++
    projectAxiomManifest.map (·.declaration)
  let acceptedSet : Lean.NameSet := accepted.foldl (·.insert ·) {}

  let mut acceptedSeen : Lean.NameSet := {}
  let mut duplicateAccepted := #[]
  for name in accepted do
    if acceptedSeen.contains name then
      duplicateAccepted := duplicateAccepted.push name
    acceptedSeen := acceptedSeen.insert name
  unless duplicateAccepted.isEmpty do
    throwError m!"Axiom classifications overlap:\
      {formatNames "Multiply classified axioms:" duplicateAccepted}"

  let unclassified := observedSet.toArray.filter (!acceptedSet.contains ·)
    |>.qsort Lean.Name.lt
  let stale := accepted.filter (!observedSet.contains ·) |>.qsort Lean.Name.lt
  unless unclassified.isEmpty && stale.isEmpty do
    throwError m!"Lean4Lean release-root axiom closure changed.\
      {formatNames "New unclassified transitive leaves:" unclassified}\
      {formatNames "Classified leaves no longer reachable:" stale}\n\
      Update the exact release policy only for an intentional trust-boundary change."

  let deadCompiler := compilerDecisionAxioms.filter (!usedAxioms.contains ·)
    |>.qsort Lean.Name.lt
  unless deadCompiler.isEmpty do
    throwError m!"Compiler-generated axiom declarations are no longer used and must be deleted:\
      {formatNames "Dead compiler decision axioms:" deadCompiler}"

  let violations :=
    policyViolations .theory theoryAxioms ++
    policyViolations .verify verifyAxioms ++
    policyViolations .library libraryAxioms ++
    policyViolations .cli cliAxioms
  unless violations.isEmpty do
    throwError m!"A classified axiom reached a forbidden release root:\n\
      {String.intercalate "\n" violations.toList}"

  -- The union and disposition checks above cannot detect an otherwise allowed
  -- leaf moving between roots.  Pin each root separately as well.
  let rootDrift :=
    rootClosureDrift .theory theoryAxioms ++
    rootClosureDrift .verify verifyAxioms ++
    rootClosureDrift .library libraryAxioms ++
    rootClosureDrift .cli cliAxioms
  unless rootDrift.isEmpty do
    throwError m!"A release root's exact axiom closure changed:\n\
      {String.intercalate "\n" rootDrift.toList}\n\n\
      Update expectedRootAxioms only for an intentional root-boundary change."

  let reports := #[
    formatRootReport .theory theoryDecls theoryAxioms,
    formatRootReport .verify verifyDecls verifyAxioms,
    formatRootReport .library libraryDecls libraryAxioms,
    formatRootReport .cli cliDecls cliAxioms]
  logInfo m!"Lean4Lean release-root axiom closure OK ({observedSet.size} exactly classified leaves).\n\
    {String.intercalate "\n" reports.toList}"

end Lean4Lean.Audit
