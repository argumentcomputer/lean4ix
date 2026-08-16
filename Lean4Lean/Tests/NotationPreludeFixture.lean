/-!
# Notation-heavy prelude fixture

Unlike the older `IndexedVec` fixture, these declarations deliberately keep
ordinary numeral, arithmetic, list, array, product, conditional, comparison,
and string notation in the source.  Their compiled metadata therefore pulls
the real `OfNat`/`HAdd` and literal dependency prefix into fresh replay.
-/

namespace Lean4Lean.Tests.NotationPreludeFixture

inductive NotationVec (α : Type u) : Nat → Type u where
  | nil : NotationVec α 0
  | cons {n : Nat} : α → NotationVec α n → NotationVec α (n + 1)

def sample : NotationVec Nat (1 + 1) :=
  .cons 37 (.cons 5 .nil)

def notationList : List (Nat × String) :=
  [(0, "zero"), (1 + 1, "two"), (if 2 < 3 then 3 else 4, "three")]

def notationArray : Array (Nat × String) :=
  #[(5, "five"), (2 + 4, "six")]

/-- One root whose type and value retain the complete fixture dependency
closure for replay. -/
def bundled :
    NotationVec Nat (1 + 1) ×
      (List (Nat × String) × Array (Nat × String)) :=
  (sample, notationList, notationArray)

end Lean4Lean.Tests.NotationPreludeFixture
