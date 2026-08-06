import Lean4Lean.Theory
import Lean4Lean.Theory.InductiveFixtures
import Lean4Lean.Theory.Typing.Injectivity
import Lean4Lean.Verify
import Lean4Lean.Verify.Level
import Lean4Lean.Verify.Environment
import Lean4Lean.Verify.Environment.IndexedVecCandidate
import Lean4Lean.Verify.Environment.IndexedVecConsReplay
import Lean4Lean.Verify.Environment.IndexedVecConstructors
import Lean4Lean.Verify.Environment.IndexedVecOuterReplay
import Lean4Lean.Verify.Environment.IndexedVecSemanticReplay
import Lean4Lean.Verify.Environment.InductiveFixtures
import Lean4Lean.Verify.Environment.Normalization
import Lean4Lean.Verify.TypeChecker.InferType
import Lean4Lean.Verify.TypeChecker.WHNF
import Lean4Lean.Verify.TypeChecker.IsDefEq

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
`Lean4Lean.Verify.Level`).

The audited surface is exactly the modules reachable from this file's imports:
importing a `Theory`/`Verify` module here is what brings it into scope. A sorry
in a proof module not (transitively) imported here is not seen, so when a new
`Theory`/`Verify` file joins the trusted build, add its import below.
`Lean4Lean.Experimental.*` is parked proof work outside the trusted surface and
is intentionally not imported.

Runs as a build-time `run_cmd`, not an executable: `lake build` of this module
is the whole check.
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
  -- Tier S — missing specification
  `Lean4Lean.TrProj,
  -- Tier P — blocked only on Tier S
  `Lean4Lean.TrProj.weak',
  `Lean4Lean.TrProj.weak'_inv,
  `Lean4Lean.TrProj.defeqDFC,
  `Lean4Lean.TrProj.wf,
  `Lean4Lean.TrProj.uniq,
  `Lean4Lean.TrProj.instN,
  `Lean4Lean.TrProj.instL,
  -- Tier V — checker verification, blocked on Tiers S/P
  `Lean.Level.Normalize.NormLevel.subsumption_eval,
  `Lean.Level.isEquiv_wf,
  `Lean4Lean.addDecl.WF,
  `Lean4Lean.TypeChecker.Inner.inferProj.WF,
  `Lean4Lean.TypeChecker.Inner.reduceRecursor.WF,
  `Lean4Lean.TypeChecker.Inner.reduceProj.WF,
  `Lean4Lean.TypeChecker.Inner.tryEtaStructCore.WF,
  `Lean4Lean.TypeChecker.Inner.isDefEqUnitLike.WF,
  -- Tier R — research-grade metatheory (upstream-driven, not scheduled)
  `Lean4Lean.VEnv.IsDefEqU.sort_inv,
  `Lean4Lean.VEnv.IsDefEqU.forallE_inv_stratified,
  `Lean4Lean.VEnv.IsDefEqU.sort_forallE_inv,
  `Lean4Lean.VEnv.IsDefEqU.weakN_iff,
  `Lean4Lean.VEnv.NormalEq.parRed,
  -- Tier F — deliberately kernel-rejected inductive fixtures. Elaborator error
  -- recovery admits the invalid `inductive` with `sorryAx`, so the constant
  -- carries a sorry dependency even though the source has no `sorry` token
  -- (which is why the old source-token scan never saw these). Not proof debt.
  `Lean4Lean.InductiveFixtures.KernelDifferential.KernelRejectRecDomain,
  `Lean4Lean.InductiveFixtures.KernelDifferential.KernelRejectRecIndex]

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
