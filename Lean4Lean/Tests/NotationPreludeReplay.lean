import Lean4Lean.Replay
import Lean4Lean.Tests.NotationPreludeFixture

/-!
# Fresh notation-prelude replay

This is an executable replay from an empty kernel environment over the real
compiled dependency closure of `bundled`.  In particular, no hand-built
Theory environment or abstract existence witness stands in for the prelude
prefix selected by the stored metadata.
-/

namespace Lean4Lean.Tests.NotationPreludeReplay

open Lean

private def fixtureModule : Name :=
  `Lean4Lean.Tests.NotationPreludeFixture

private def fixtureRoot : Name :=
  ``Lean4Lean.Tests.NotationPreludeFixture.bundled

/-- Return the actual fresh kernel environment as well as the count so the
test can check that the notation-selected prelude prefix was really installed.
This is the same operation as `Replay.replayFromFresh` specialized to one
dependency root. -/
private unsafe def replayNotationPrefix :
    IO (Nat × Lean.Kernel.Environment) := do
  Lean.withImportModules #[fixtureModule] {} (trustLevel := 0) fun env => do
    let context : Lean4Lean.Replay.Context := {
      newConstants := env.constants.map₁
      checkQuot := false }
    Lean4Lean.Replay.replay context (.empty fixtureModule) (some fixtureRoot)

run_cmd do
  let (count, replayed) ← replayNotationPrefix
  unless count = 296 do
    throwError "notation-heavy fresh replay added {count} declarations; expected 296"
  let required := #[
    ``OfNat.ofNat,
    ``HAdd.hAdd,
    ``String.ofList,
    ``Char.ofNat,
    ``Lean4Lean.Tests.NotationPreludeFixture.NotationVec,
    ``Lean4Lean.Tests.NotationPreludeFixture.NotationVec.nil,
    ``Lean4Lean.Tests.NotationPreludeFixture.NotationVec.cons,
    ``Lean4Lean.Tests.NotationPreludeFixture.NotationVec.rec,
    fixtureRoot]
  for name in required do
    unless (replayed.constants.find? name).isSome do
      throwError "notation-heavy fresh replay omitted {name}"
  logInfo m!"notation-heavy fresh replay OK ({count} declarations)"

end Lean4Lean.Tests.NotationPreludeReplay
