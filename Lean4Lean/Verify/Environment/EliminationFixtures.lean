import Lean4Lean.Verify.Environment.SingletonParityReplay
import Lean4Lean.Verify.Environment.EliminationFixturesSmall

/-!
Public singleton-inductive verification umbrella.

`SingletonParityReplay` is the sole L4L-07 path for the fixed positive,
normalization, rejection, kernel-metadata, and environment-replay matrices.
The small synthetic elimination boundary cases remain alongside it because
they are not standard-library singleton declarations.
-/
