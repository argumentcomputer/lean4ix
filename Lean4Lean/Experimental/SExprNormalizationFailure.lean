import Lean4Lean.Experimental.SExprReducibility
import Lean4Lean.Theory.MutualInductiveFixtures

/-!
# L4L-16N2: machine-checked termination-measure failure

This file records the kill criterion reached by the classified
normalization experiment.  It does **not** refute weak-head normalization.
It refutes the two termination measures authorized by the L4L-16N roadmap:

* the primary `(definition rank, syntax size, typing depth)` order increases
  on the production `Tree.branch` iota rewrite (123 LHS nodes to 127 RHS
  nodes); the generated recursive major explains the increase by applying a
  captured field to a fresh variable; and
* repairing that step with a leading block-family rank is impossible for the
  checked `Tree`/`TreeList` block.  The under-Pi `Tree -> TreeList` edge needs
  a strict rank drop, while the reverse `TreeList -> Tree` edge requires the
  rank to be non-increasing in the opposite direction.

The second statement is deliberately stronger than checking the stored
source ordinals `[0, 1]`: it rules out every reassignment of natural-number
family ranks satisfying the lexicographic obligations.  The roadmap permits
no third fallback after this point.
-/

namespace Lean4Lean
namespace L4L16NFailure

open VInductDecl
open MutualInductiveFixtures

/-! ## The primary syntax-size component -/

/-- A transparent syntax-node count used to state the proposed size
component without depending on compiler-generated `SizeOf` code. -/
def exprNodes : VExpr -> Nat
  | .bvar _ | .sort _ | .const _ _ => 1
  | .app f a | .lam f a | .forallE f a =>
      exprNodes f + exprNodes a + 1

/-- Boolean syntactic containment, used only to tie the isolated major below
back to the production `blockRuleCall` implementation. -/
def containsExpr (needle : VExpr) : VExpr -> Bool
  | expression@(.bvar _) | expression@(.sort _) | expression@(.const _ _) =>
      expression == needle
  | expression@(.app f a) | expression@(.lam f a) |
      expression@(.forallE f a) =>
      expression == needle || containsExpr needle f || containsExpr needle a

/-- The major argument emitted inside `blockRuleCall`.  This is the exact
subexpression from `Theory/Inductive.lean`: a recursive field is applied to
every fresh binder before it is passed to the target recursor. -/
def generatedMajor (m : Nat) (recursive : RecArg) : VExpr :=
  let n := recursive.binders.length
  VExpr.appN (.bvar (m - 1 - recursive.fieldIndex + n))
    (VExpr.bvarRevRange 0 n)

/-- The checked descriptor for `Tree.branch : (alpha -> TreeList alpha) ->
Tree alpha`. -/
def treeBranchRecursive : RecArg :=
  treeChecked.families.constructors[0][2].recursive[0]

/-- The owner ordinal of the generated `Tree.branch` rule. -/
def treeBranchOwner : Nat :=
  treeChecked.families.ordinals[0]

/-- The production iota equation for `Tree.branch` (the third constructor in
the checked source order). -/
def treeBranchRule : VDefEq :=
  treeGeneration.generatedRules[2]

theorem treeBranch_owner : treeBranchOwner = 0 := rfl

theorem treeBranch_target : treeBranchRecursive.targetType = 1 := rfl

theorem treeBranch_underPi : treeBranchRecursive.binders.length = 1 := rfl

theorem treeBranch_rule_constructor :
    treeGeneration.flatCtors[2].ctor.raw.name = ``Tree.branch := rfl

/-- The generated recursive major is literally the captured function field
applied to the fresh Pi-bound variable. -/
theorem treeBranch_generatedMajor :
    generatedMajor 1 treeBranchRecursive =
      VExpr.app (.bvar 1) (.bvar 0) := rfl

/-- The isolated term above really occurs in the production mutual-rule
generator; it is not a restatement detached from `blockRuleCall`. -/
theorem treeBranch_generatedMajor_in_blockRuleCall :
    containsExpr (generatedMajor 1 treeBranchRecursive)
      (VInductDecl.BlockGenerationChecked.blockRuleCall
        7 1 (.bvar 0) treeBranchRecursive) = true := by
  decide

/-- Moving from the captured field to the generated recursive major grows
the syntax measure from one node to three. -/
theorem treeBranch_generatedMajor_grows :
    exprNodes (.bvar 0) < exprNodes (generatedMajor 1 treeBranchRecursive) := by
  rw [treeBranch_generatedMajor]
  decide

/-- The complete production iota rewrite grows as syntax: its LHS contains
123 nodes and its RHS 127.  This is the actual reduction transition on which
the N2 normalizer would recurse. -/
theorem treeBranch_rule_lhs_nodes : exprNodes treeBranchRule.lhs = 123 := by
  decide

theorem treeBranch_rule_rhs_nodes : exprNodes treeBranchRule.rhs = 127 := by
  decide

theorem treeBranch_rule_grows :
    exprNodes treeBranchRule.lhs < exprNodes treeBranchRule.rhs := by
  decide

/-- The lexicographic measure proposed for N2. -/
structure PrimaryMeasure where
  rank : Nat
  size : Nat
  depth : Nat

/-- Strict lexicographic order with the roadmap's component priority. -/
def PrimaryMeasure.LT (target source : PrimaryMeasure) : Prop :=
  Or (target.rank < source.rank)
    (And (target.rank = source.rank)
      (Or (target.size < source.size)
        (And (target.size = source.size) (target.depth < source.depth))))

/-- An iota contraction is not a delta step, so the definition-rank component
is unchanged.  Since the production Tree-branch RHS is larger than its LHS,
no choice of typing depths can make the primary lexicographic measure
decrease. -/
theorem treeBranch_primaryMeasure_fails
    (rank sourceDepth targetDepth : Nat) :
    Not (PrimaryMeasure.LT
      { rank := rank
        size := exprNodes treeBranchRule.rhs
        depth := targetDepth }
      { rank := rank
        size := exprNodes treeBranchRule.lhs
        depth := sourceDepth }) := by
  rw [treeBranch_rule_lhs_nodes, treeBranch_rule_rhs_nodes]
  simp [PrimaryMeasure.LT]

/-! ## The block-family ordinal fallback -/

/-- Boolean edge lookup in the exact `recursiveTargets` artifact retained by
checked mutual-block analysis. -/
def recursiveTargetEdge (targets : List (List (List Nat)))
    (owner target : Nat) : Bool :=
  match targets[owner]? with
  | none => false
  | some constructors => constructors.any fun constructorTargets =>
      constructorTargets.contains target

/-- A leading family rank may stay equal when a later measure component
decreases, but it may never increase along a recursive edge. -/
def FamilyRankNonincreasing (targets : List (List (List Nat)))
    (rank : Nat -> Nat) : Prop :=
  forall {owner target}, recursiveTargetEdge targets owner target = true ->
    rank target <= rank owner

theorem tree_targetEdge_tree_treeList :
    recursiveTargetEdge treeChecked.families.recursiveTargets 0 1 = true := by
  decide

theorem tree_targetEdge_treeList_tree :
    recursiveTargetEdge treeChecked.families.recursiveTargets 1 0 = true := by
  decide

theorem tree_targetEdge_treeList_treeList :
    recursiveTargetEdge treeChecked.families.recursiveTargets 1 1 = true := by
  decide

/-- The exact ordinal fallback obligations: family rank is non-increasing on
all recursive edges and strictly decreases on the under-Pi branch whose
syntax-size transition failed above. -/
def FamilyOrdinalFallback (rank : Nat -> Nat) : Prop :=
  And (FamilyRankNonincreasing treeChecked.families.recursiveTargets rank)
    (rank treeBranchRecursive.targetType < rank treeBranchOwner)

/-- No reassignment of family ordinals can meet the fallback obligations.
The reverse `TreeList -> Tree` edge yields `rank Tree <= rank TreeList`,
contradicting the strict `Tree -> TreeList` drop required by `Tree.branch`. -/
theorem tree_familyOrdinalFallback_false :
    Not (Exists FamilyOrdinalFallback) := by
  rintro ⟨rank, nonincreasing, strict⟩
  have reverse : rank 0 <= rank 1 :=
    nonincreasing tree_targetEdge_treeList_tree
  rw [treeBranch_target, treeBranch_owner] at strict
  omega

/-- A fortiori, the recursive-target graph admits no rank that strictly
decreases on every edge (the `TreeList` self-edge alone rules it out). -/
def StrictFamilyRanking (rank : Nat -> Nat) : Prop :=
  forall {owner target},
    recursiveTargetEdge treeChecked.families.recursiveTargets owner target = true ->
      rank target < rank owner

theorem tree_strictFamilyRanking_false :
    Not (Exists StrictFamilyRanking) := by
  rintro ⟨rank, ranks⟩
  have impossible : rank 1 < rank 1 :=
    ranks tree_targetEdge_treeList_treeList
  omega

/-! The failure record stays within the accepted Theory logical baseline. -/

/-- info: 'Lean4Lean.L4L16NFailure.treeBranch_primaryMeasure_fails' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms treeBranch_primaryMeasure_fails

/-- info: 'Lean4Lean.L4L16NFailure.tree_familyOrdinalFallback_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tree_familyOrdinalFallback_false

/-- info: 'Lean4Lean.L4L16NFailure.tree_strictFamilyRanking_false' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tree_strictFamilyRanking_false

end L4L16NFailure
end Lean4Lean
