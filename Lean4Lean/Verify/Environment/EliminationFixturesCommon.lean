import Lean4Lean.Verify.Environment.Elimination
import Lean4Lean.Verify.Environment.InductiveFixtures

namespace Lean4Lean.InductiveReplayFixtures
open Lean Meta Elab Term
open Lean4Lean.InductiveFixtures

universe u

/-- A source-universe-bearing small eliminator. Or has no source universes,
so this fixture distinguishes "no fresh level" from "no levels at all". -/
inductive L4L06SmallSource (α : Sort u) : Prop where
  | left : L4L06SmallSource α
  | right : L4L06SmallSource α

def recursorShape06 (info : ConstantInfo) :
    List Name × Nat × Nat × Nat × Nat × Bool × List (Name × Nat) :=
  match info with
  | .recInfo rec =>
      (rec.levelParams, rec.numParams, rec.numIndices, rec.numMotives,
        rec.numMinors, rec.k,
        rec.rules.map fun rule => (rule.ctor, rule.nfields))
  | _ => ([], 0, 0, 0, 0, false, [])

def l4l06KernelEnv : Kernel.Environment :=
  Kernel.Environment.ofConstants `_l4l06 {}

def l4l06Context (lparams : List Name) : AddInductive.Context where
  env := l4l06KernelEnv
  lparams := lparams
  safety := .safe
  allowPrimitive := false

example : AddInductive.getFreshElimParam [] = `u := by native_decide
example : AddInductive.getFreshElimParam [`u] = `u_1 := by native_decide
example : AddInductive.getFreshElimParam [`u, `u_1] = `u_2 := by native_decide

/-- Decidable structural equality for the exact kernel level lists retained by
the fixtures. `Lean.Level` intentionally has no `DecidableEq` instance. -/
def levelListStructEq06 : List Level → List Level → Bool
  | [], [] => true
  | u :: us, v :: vs =>
      Level.isStructEq u v && levelListStructEq06 us vs
  | _, _ => false

theorem levelListStructEq06_eq {us vs : List Level}
    (h : levelListStructEq06 us vs) : us = vs := by
  induction us generalizing vs with
  | nil => cases vs <;> simp_all [levelListStructEq06]
  | cons u us ih =>
      cases vs with
      | nil => simp [levelListStructEq06] at h
      | cons v vs =>
          simp only [levelListStructEq06, Bool.and_eq_true] at h
          cases Level.isStructEq_eq h.1
          cases ih h.2
          rfl

end Lean4Lean.InductiveReplayFixtures
