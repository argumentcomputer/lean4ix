import Lean4Lean.Theory.Typing.InductivePatternEnv

/-! # Pattern facts for concrete certified blocks

Two self-contained certified blocks pin the L4L-10A pattern layer by
evaluation: a mutual tree/forest pair (two families, three flattened
constructors, recursion in both directions) and an indexed vector (one
family, a `Nat` index, indices spelled with `Nat.zero`/`Nat.succ`). Both
use literal names throughout, keeping every closedness and inventory bit
kernel-decidable. The expected `SimplePattern` inventories are written by
hand: the major arity counts shared parameters, all motives, all minors, and
the constructor's result indices; the argument arity counts the
constructor's parameters and fields. -/

namespace Lean4Lean.InductivePatternFixtures

open Lean4Lean.VInductDecl
open Lean4Lean.VInductDecl.BlockGenerationChecked

/-- `mutual inductive PatTree (α : Type u) | node : α → PatForest α → PatTree α
inductive PatForest (α : Type u) | nil | cons : PatTree α → PatForest α →
PatForest α end` -/
def patBlock : VInductDecl where
  uvars := 1
  nparams := 1
  types :=
    [{ name := `PatTree
       uvars := 1
       type := .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))
       ctors :=
         [⟨⟨1, .forallE (.sort (.succ (.param 0)))
             (.forallE (.bvar 0)
               (.forallE (.app (.const `PatForest [.param 0]) (.bvar 1))
                 (.app (.const `PatTree [.param 0]) (.bvar 2))))⟩,
           `PatTree.node⟩] },
     { name := `PatForest
       uvars := 1
       type := .forallE (.sort (.succ (.param 0))) (.sort (.succ (.param 0)))
       ctors :=
         [⟨⟨1, .forallE (.sort (.succ (.param 0)))
             (.app (.const `PatForest [.param 0]) (.bvar 0))⟩,
           `PatForest.nil⟩,
          ⟨⟨1, .forallE (.sort (.succ (.param 0)))
             (.forallE (.app (.const `PatTree [.param 0]) (.bvar 0))
               (.forallE (.app (.const `PatForest [.param 0]) (.bvar 1))
                 (.app (.const `PatForest [.param 0]) (.bvar 2))))⟩,
           `PatForest.cons⟩] }]

/-- `inductive PatVec (α : Type) : Nat → Type | nil : PatVec α Nat.zero
| cons : α → (n : Nat) → PatVec α n → PatVec α (Nat.succ n)` -/
def patVec : VInductDecl where
  uvars := 0
  nparams := 1
  types :=
    [{ name := `PatVec
       uvars := 0
       type := .forallE (.sort (.succ .zero))
         (.forallE (.const `Nat []) (.sort (.succ .zero)))
       ctors :=
         [⟨⟨0, .forallE (.sort (.succ .zero))
             (.app (.app (.const `PatVec []) (.bvar 0))
               (.const `Nat.zero []))⟩,
           `PatVec.nil⟩,
          ⟨⟨0, .forallE (.sort (.succ .zero))
             (.forallE (.bvar 0)
               (.forallE (.const `Nat [])
                 (.forallE (.app (.app (.const `PatVec []) (.bvar 2)) (.bvar 0))
                   (.app (.app (.const `PatVec []) (.bvar 3))
                     (.app (.const `Nat.succ []) (.bvar 1))))))⟩,
           `PatVec.cons⟩] }]

#guard patBlock.stage3
#guard patVec.stage3

/-- The certified mutual block. -/
def patTreeGen : patBlock.BlockGenerationChecked :=
  (identityBlockGeneration? patBlock).get (by decide)

/-- The certified indexed block. -/
def patVecGen : patVec.BlockGenerationChecked :=
  (identityBlockGeneration? patVec).get (by decide)

/-! ## Pattern inventories

Majors: `PatTree`/`PatForest` share one parameter, two motives, and three
minors with no indices (major arity 6); `PatVec` has one parameter, one
motive, two minors, and one index (major arity 5). -/

#guard patTreeGen.flatCtors.map (fun c => patTreeGen.rulePattern c) ==
  [.iota (.str `PatTree "rec") 6 `PatTree.node 3,
   .iota (.str `PatForest "rec") 6 `PatForest.nil 1,
   .iota (.str `PatForest "rec") 6 `PatForest.cons 3]

#guard patVecGen.flatCtors.map (fun c => patVecGen.rulePattern c) ==
  [.iota (.str `PatVec "rec") 5 `PatVec.nil 1,
   .iota (.str `PatVec "rec") 5 `PatVec.cons 4]

/-! ## Payload closedness by evaluation -/

theorem patTreeClosure : patTreeGen.RuleClosure :=
  RuleClosure.of_all _ (by decide) (by decide)

theorem patVecClosure : patVecGen.RuleClosure :=
  RuleClosure.of_all _ (by decide) (by decide)

/-! ## Beta-collapsed tower certificates

The concrete generated block and the built-in quotient equation both expose
their first-order match only after stripping the registered lambda tower.
These examples pin that contract without constructing a `Params` instance or
assuming an equality from pattern membership. -/

/-- Every registered iota rule of the concrete mutual block has a
beta-collapsed pattern witness. -/
theorem patTreeIotaExtension_covers {i : Nat}
    {constructor : NormalizedBlockCtor} (hentry : patTreeGen.ruleEntry i constructor)
    (ls : List VLevel) (hlen : ls.length = (patTreeGen.rule i constructor).uvars) :
    ∃ m1 m2, (patTreeGen.rulePattern constructor).toPattern.Matches
      (VExpr.stripLams ((patTreeGen.rule i constructor).lhs.instL ls)) m1 m2 :=
  (patTreeGen.iotaExtension patTreeClosure hentry).covers ls hlen

/-- `quotDefEq` satisfies the same beta-collapsed coverage contract. -/
theorem quotDefEq_covers (ls : List VLevel)
    (hlen : ls.length = quotDefEq.uvars) :
    ∃ m1 m2, CertifiedExtension.quotPattern.toPattern.Matches
      (VExpr.stripLams (quotDefEq.lhs.instL ls)) m1 m2 :=
  CertifiedExtension.quot.covers ls hlen

/-!
The tower witnesses stay on the standard logical baseline. In particular,
neither closure contains a project axiom or `sorryAx`.
-/

/--
info: 'Lean4Lean.InductivePatternFixtures.patTreeIotaExtension_covers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms patTreeIotaExtension_covers

/-- info: 'Lean4Lean.InductivePatternFixtures.quotDefEq_covers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms quotDefEq_covers

/-! ## The instantiated pattern sets

Both blocks now carry complete pattern payloads: `patTreeGen.IotaPat
patTreeClosure` and `patVecGen.IotaPat patVecClosure` satisfy every generic
obligation proved in `Theory/Typing/InductivePattern.lean`, at the standard
axiom closure recorded below. -/

/-- info: 'Lean4Lean.InductivePatternFixtures.patTreeClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms patTreeClosure

/-- info: 'Lean4Lean.InductivePatternFixtures.patVecClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms patVecClosure

/-! ## The assembled block-local environments

Both blocks assemble over the empty base with no extensions; their defeq
sets are exactly their generated rules. -/

#guard (patTreeGen.assembleEnv .empty []).isSome
#guard (patVecGen.assembleEnv .empty []).isSome

/-- Every defeq of the assembled tree/forest environment is a generated
rule: the base is defeq-free and no extensions are registered. -/
example {env' : VEnv} (h : patTreeGen.assembleEnv .empty [] = some env')
    {df : VDefEq} (hdf : env'.defeqs df) :
    df ∈ patTreeGen.generatedRules := by
  rcases patTreeGen.assembleEnv_defeq_cases h (fun _ hd => hd) hdf with
    hrule | ⟨ext, hm, -⟩
  · exact hrule
  · cases hm

/-! ## Union-level non-overlap: the mutual block plus the quotient extension

The union-level laws of `Theory/Typing/InductivePatternEnv.lean` require an
`ExtSeparation` certificate for the extension list.  For the concrete
mutual tree/forest block extended with `CertifiedExtension.quot` the
certificate is kernel-decidable: the rule inventory is pinned by `decide`
and every required head disequality is a literal name comparison.  All four
union laws instantiate below. -/

/-- The three-rule inventory of the mutual tree/forest block,
kernel-checked (the `Prop` form of the `#guard` inventory above). -/
theorem patTree_rulePattern_inventory :
    patTreeGen.flatCtors.map (fun c => patTreeGen.rulePattern c) =
      [.iota (.str `PatTree "rec") 6 `PatTree.node 3,
       .iota (.str `PatForest "rec") 6 `PatForest.nil 1,
       .iota (.str `PatForest "rec") 6 `PatForest.cons 3] := by decide

/-- Head separation of the quotient extension from every rule of the
mutual block. -/
theorem quot_headSep_patTree {constructor : NormalizedBlockCtor}
    (hc : constructor ∈ patTreeGen.flatCtors) :
    (CertifiedExtension.quot.pat).HeadSep
      (patTreeGen.rulePattern constructor) := by
  have hp : patTreeGen.rulePattern constructor ∈
      patTreeGen.flatCtors.map (fun c => patTreeGen.rulePattern c) :=
    List.mem_map_of_mem hc
  rw [patTree_rulePattern_inventory] at hp
  have hq : CertifiedExtension.quot.pat =
      .iota ``Quot.lift 5 ``Quot.mk 3 := rfl
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with hp | hp | hp <;> rw [hq, hp] <;>
    exact SimplePattern.HeadSep.iota_iota (by decide) (by decide) (by decide)

/-- The complete separation certificate for the mutual block unioned with
the quotient extension, discharged by kernel `decide`. -/
theorem patTree_quot_separation :
    patTreeGen.ExtSeparation [CertifiedExtension.quot] := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ext hm
    rw [List.mem_singleton] at hm
    subst hm
    show (``Quot.lift : Name) ≠ ``Quot.mk
    decide
  · rintro ext hm c hc
    rw [List.mem_singleton] at hm
    subst hm
    exact quot_headSep_patTree hc
  · rintro e1 h1 e2 h2 -
    rw [List.mem_singleton] at h1 h2
    subst h1; subst h2; rfl
  · rintro e1 h1 e2 h2 hne
    rw [List.mem_singleton] at h1 h2
    subst h1; subst h2
    exact absurd rfl hne

/-- All four union laws instantiate for the two-inductive mutual block with
the quotient extension. -/
example {p₁ p₂ p₃ p₄ : Pattern} {r : p₁.RHS × p₁.Check}
    {r' : p₂.RHS × p₂.Check}
    (H1 : patTreeGen.AssembledPat patTreeClosure [CertifiedExtension.quot]
      p₁ r)
    (H2 : patTreeGen.AssembledPat patTreeClosure [CertifiedExtension.quot]
      p₂ r')
    (H3 : Subpattern p₃ p₁) (H4 : p₂.inter p₃ = some p₄) :
    p₁ = p₂ ∧ p₂ = p₃ ∧ r ≍ r' :=
  AssembledPat.pat_uniq patTreeGen patTree_quot_separation H1 H2 H3 H4

example {p : Pattern} {r : p.RHS × p.Check} {p₁ p₂ p₃ p₄ : Pattern}
    (H : patTreeGen.AssembledPat patTreeClosure [CertifiedExtension.quot]
      p r)
    (h : Subpattern (.app p₁ p₂) p) : ¬Subpattern (.app p₃ p₄) p₁ :=
  AssembledPat.pat_app_l patTreeGen H h

example {p p' : Pattern} {r : p.RHS × p.Check} {r' : p'.RHS × p'.Check}
    {p₁ p₂ p₁' p₂' p₃ : Pattern}
    (H : patTreeGen.AssembledPat patTreeClosure [CertifiedExtension.quot]
      p r)
    (H' : patTreeGen.AssembledPat patTreeClosure [CertifiedExtension.quot]
      p' r')
    (h : Subpattern (.app p₁ p₂) p) (h' : Subpattern (.app p₁' p₂') p')
    (h₃ : Subpattern (.var p₃) p₁) : p₁'.inter p₃ = none :=
  AssembledPat.pat_app_l_uniq patTreeGen patTree_quot_separation
    H H' h h' h₃

example {p p' : Pattern} {r : p.RHS × p.Check} {r' : p'.RHS × p'.Check}
    {p₁ p₂ p₁' p₂' p₃ p₃' : Pattern}
    (H : patTreeGen.AssembledPat patTreeClosure [CertifiedExtension.quot]
      p r)
    (H' : patTreeGen.AssembledPat patTreeClosure [CertifiedExtension.quot]
      p' r')
    (h : Subpattern (.app p₁ p₂) p) (h' : Subpattern (.app p₁' p₂') p')
    (h₃ : Subpattern p₃ p₁) (h₃' : Subpattern p₃' p₂') :
    p₃.inter p₃' = none :=
  AssembledPat.pat_app_uniq patTreeGen patTree_quot_separation
    H H' h h' h₃ h₃'

/-!
The separation certificate stays on the standard logical baseline; in
particular it contains no project axiom and no `sorryAx`, and its `decide`
steps are kernel-checked.
-/

/-- info: 'Lean4Lean.InductivePatternFixtures.patTree_quot_separation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms patTree_quot_separation

end Lean4Lean.InductivePatternFixtures
