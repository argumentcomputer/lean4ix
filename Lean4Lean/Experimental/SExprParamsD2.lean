import Lean4Lean.Experimental.SExprParamsD1
import Lean4Lean.Experimental.SExprTransport
import Lean4Lean.Experimental.SExprGenericReplay
import Lean4Lean.Verify.Environment.MutualInductiveFixtures
import Lean4Lean.Theory.Typing.InductivePatternFixtures

/-!
# L4L-16D2: a live block-inductive environment over the D1 fixture

This module extends the kernel-checked D1 instance
(`Lean4Lean/Experimental/SExprParamsD1.lean`) with the next staged slice of
live-environment coverage: a genuine *mutual inductive block* declaration
step.  The block is the real `Tree`/`TreeList` pair of
`Lean4Lean/Theory/MutualInductiveFixtures.lean` — two families, five
flattened constructors, two recursors, five generated iota rules — added to
`d1Env` by a checked `VDecl.WF.inductBlock` history step.

The pattern layer is the first live consumer of the union-level non-overlap
laws landed in `Theory/Typing/InductivePatternEnv.lean`: the block's five
generated rules and the three D1 *definition* rules are packaged as one
`AssembledPat` whose `ExtSeparation` certificate is discharged by kernel
`decide` through the block's rule-pattern inventory.

Scope note.  The `Params.Semantic` bridge is *not* completed here.  Four of
its six fields are delivered (see `d2StructureEtaSound`, `d2IotaRule`, and
the transport-free observations below); `iotaSite` and `registered` for the
five *new* block rules require the full evidence-rich reduction-site replay
that D0/D1 performed per Nat rule, which is a bounded but large piece of
work.  The obstruction is recorded precisely at the end of this file, in the
same style as D1's quotient record.
-/

namespace Lean4Lean
namespace SExpr
namespace ParamsD2

open InductiveFixtures InductiveReplayFixtures VInductDecl
open MutualInductiveFixtures MutualInductiveReplayFixtures
open ParamsD0 ParamsD1

/-! ## D2 block data

`treeGeneration` is the certified block-wide generation descriptor of the
real `Tree`/`TreeList` declaration, together with the semantic package
`treeBlockGenerationWF` proved over the empty environment in
`Verify/Environment/MutualInductiveFixtures.lean`.  Nothing about the block
is re-derived here; the D2 work is re-basing that package onto `d1Env` and
consuming it. -/

/-- The certified mutual block used by D2. -/
abbrev TreeGen := MutualInductiveFixtures.treeGeneration

/-- The five generated iota RHS towers and index towers are closed. -/
theorem treeRuleClosure : TreeGen.RuleClosure :=
  VInductDecl.BlockGenerationChecked.RuleClosure.of_all _
    (by decide) (by decide)

/-- The block's rule-pattern inventory, kernel-checked.  Majors count the
shared parameter, both motives, all five minors, and the (empty) result
indices; argument arities count parameters plus constructor fields. -/
theorem treeRulePattern_inventory :
    TreeGen.flatCtors.map (fun c => TreeGen.rulePattern c) =
      [.iota (.str ``Tree "rec") 8 ``Tree.leaf 2,
       .iota (.str ``Tree "rec") 8 ``Tree.node 2,
       .iota (.str ``Tree "rec") 8 ``Tree.branch 2,
       .iota (.str ``TreeList "rec") 8 ``TreeList.nil 1,
       .iota (.str ``TreeList "rec") 8 ``TreeList.cons 3] := by decide

/-! ## D2 environment layer

The block is added to `d1Env` by the four-phase block transaction.  Its
semantic package is the empty-environment package re-based by monotonicity:
`BlockGenerationChecked.WF` is monotone in every field except the staging
equation, which is re-established over `d1Env` directly. -/

local instance : Inhabited VEnv := ⟨VEnv.empty⟩

theorem tree_fresh : d1Env.constants ``Tree = none := by native_decide

theorem treeList_fresh : d1Env.constants ``TreeList = none := by native_decide

theorem tree_name_ne_treeList : (``Tree : Name) ≠ ``TreeList := by decide

/-- The environment after the block's family constants, before any
constructor. -/
def d2StageT := (d1Env.addConst ``Tree treeType.toVConstant).get!

def d2BlockEnv := (d2StageT.addConst ``TreeList treeListType.toVConstant).get!

theorem d1Env_add_tree :
    d1Env.addConst ``Tree treeType.toVConstant = some d2StageT := by
  simp [VEnv.addConst, tree_fresh, d2StageT]

theorem treeList_fresh_T : d2StageT.constants ``TreeList = none := by
  have hne := tree_name_ne_treeList
  simp [d2StageT, VEnv.addConst, tree_fresh, hne, treeList_fresh]

theorem d2StageT_add_treeList :
    d2StageT.addConst ``TreeList treeListType.toVConstant =
      some d2BlockEnv := by
  simp [VEnv.addConst, treeList_fresh_T, d2BlockEnv]

theorem d1Env_stage :
    d1Env.stageInductiveTypes treeDecl.types = some d2BlockEnv := by
  simp [VEnv.stageInductiveTypes, treeDecl, List.foldlM]
  exact ⟨_, d1Env_add_tree, d2StageT_add_treeList⟩

theorem d1Env_le_d2BlockEnv : d1Env ≤ d2BlockEnv :=
  (VEnv.addConst_le d1Env_add_tree).trans
    (VEnv.addConst_le d2StageT_add_treeList)

/-! ### Re-basing the block's semantic package

`treeBlockGenerationWF` lives over `VEnv.empty`/`treeBlockEnv`.  Every field
except the staging equation is monotone, so the D2 package follows from two
environment inclusions. -/

theorem empty_le_d1Env : VEnv.empty ≤ d1Env where
  constants h := by simp [VEnv.empty] at h
  defeqs h := h.elim
  structEtas h := h.elim

/-- Adding the same constant to a larger environment stays larger. -/
theorem addConst_le_of_le {e₁ e₂ s₁ s₂ : VEnv} {n : Name} {ci : VConstant}
    (h₁ : e₁.addConst n ci = some s₁) (h₂ : e₂.addConst n ci = some s₂)
    (hle : e₁ ≤ e₂) : s₁ ≤ s₂ := by
  unfold VEnv.addConst at h₁ h₂
  split at h₁
  · cases h₁
  split at h₂
  · cases h₂
  cases h₁
  cases h₂
  constructor
  · intro n' a h
    have h' : (if n = n' then some ci else e₁.constants n') = some a := h
    show (if n = n' then some ci else e₂.constants n') = some a
    by_cases hn : n = n'
    · rw [if_pos hn] at h' ⊢
      exact h'
    · rw [if_neg hn] at h' ⊢
      exact hle.constants h'
  · exact fun h => hle.defeqs h
  · exact fun h => hle.structEtas h

/-- Staging the same family list over a larger environment stays larger. -/
theorem stageInductiveTypes_le_of_le :
    ∀ (types : List VInductiveType) {e₁ e₂ s₁ s₂ : VEnv},
      e₁.stageInductiveTypes types = some s₁ →
      e₂.stageInductiveTypes types = some s₂ →
      e₁ ≤ e₂ → s₁ ≤ s₂
  | [], _, _, _, _, h₁, h₂, hle => by
    cases h₁; cases h₂; exact hle
  | ty :: types, e₁, e₂, s₁, s₂, h₁, h₂, hle => by
    rw [VEnv.stageInductiveTypes, List.foldlM_cons] at h₁ h₂
    rcases Option.bind_eq_some_iff.1 h₁ with ⟨t₁, ht₁, hrest₁⟩
    rcases Option.bind_eq_some_iff.1 h₂ with ⟨t₂, ht₂, hrest₂⟩
    exact stageInductiveTypes_le_of_le types hrest₁ hrest₂
      (addConst_le_of_le ht₁ ht₂ hle)

/-- Pointwise strengthening of a `Forall₂` witness. -/
theorem forall₂_imp {α β : Type _} {R S : α → β → Prop}
    (H : ∀ a b, R a b → S a b) :
    ∀ {l₁ : List α} {l₂ : List β},
      List.Forall₂ R l₁ l₂ → List.Forall₂ S l₁ l₂
  | _, _, .nil => .nil
  | _, _, .cons h t => .cons (H _ _ h) (forall₂_imp H t)

theorem treeBlockEnv_le_d2BlockEnv : treeBlockEnv ≤ d2BlockEnv :=
  stageInductiveTypes_le_of_le treeDecl.types treeStage d1Env_stage
    empty_le_d1Env

/-- The block's semantic package, re-based from the empty environment onto
`d1Env`.  Only the staging equation is genuinely new; every other field is
the empty-environment field transported by monotonicity. -/
theorem d2BlockGenerationWF : TreeGen.WF d1Env d2BlockEnv where
  blockWF :=
    ⟨⟨d1Env_stage,
      forall₂_imp
        (fun _ _ h =>
          ⟨VEnv.IsDefEqU.mono empty_le_d1Env h.1,
            forall₂_imp
              (fun _ _ hc => VEnv.IsDefEqU.mono treeBlockEnv_le_d2BlockEnv hc)
              h.2⟩)
        treeNormalizationBlockWF.2⟩,
      VInductDecl.CheckedBlock.WF.mono empty_le_d1Env
        treeBlockGenerationWF.blockWF.2⟩
  resultLevelWF := treeBlockGenerationWF.resultLevelWF
  paramsTel := VEnv.TelDefEq.mono empty_le_d1Env treeBlockGenerationWF.paramsTel
  families := fun family hfamily =>
    VInductDecl.NormalizedFamily.WF.mono empty_le_d1Env
      (treeBlockGenerationWF.families family hfamily)
  constructors := fun constructor hconstructor =>
    VInductDecl.NormalizedBlockCtor.WF.mono treeBlockEnv_le_d2BlockEnv
      (treeBlockGenerationWF.constructors constructor hconstructor)

/-! ### The completed block transaction -/

theorem d2Env_isSome : (d1Env.addInductBlockGeneration TreeGen).isSome := by
  native_decide

/-- The complete D2 environment: the D1 environment followed by one checked
mutual inductive block declaration. -/
def d2Env : VEnv := (d1Env.addInductBlockGeneration TreeGen).get d2Env_isSome

theorem d1Env_addBlock :
    d1Env.addInductBlockGeneration TreeGen = some d2Env :=
  (Option.some_get d2Env_isSome).symm

theorem d2Env_ordered : d2Env.Ordered :=
  VEnv.addInductBlockGeneration_WF d1Env_ordered d2BlockGenerationWF
    d1Env_addBlock

/-- The block is a genuine declaration history step. -/
theorem d2Env_step : VDecl.WF d1Env (.induct treeDecl) d2Env :=
  .inductBlock d2BlockGenerationWF d1Env_addBlock

theorem d2Env_wf : d2Env.WF := by
  obtain ⟨ds, hds⟩ := d1Env_wf
  exact ⟨.induct treeDecl :: ds, .decl d2Env_step hds⟩

theorem d2Trace :
    Nonempty (VEnv.AddInductBlockGenerationTrace d1Env d2Env TreeGen) :=
  VEnv.addInductBlockGeneration_trace d1Env_addBlock

theorem d1Env_le_d2Env : d1Env ≤ d2Env := by
  obtain ⟨trace⟩ := d2Trace
  exact trace.le

theorem d2Env_family_lookup {type : VInductiveType}
    (htype : type ∈ treeDecl.types) :
    d2Env.constants type.name = some type.toVConstant := by
  obtain ⟨trace⟩ := d2Trace
  exact trace.family_lookup htype

theorem d2Env_ctor_lookup {constructor : VConstVal}
    (hconstructor : constructor ∈ treeDecl.blockConstructorConstants) :
    d2Env.constants constructor.name = some constructor.toVConstant := by
  obtain ⟨trace⟩ := d2Trace
  exact trace.ctor_lookup hconstructor

theorem d2Env_rec_lookup {recursor : VConstVal}
    (hrecursor : recursor ∈ TreeGen.recursors) :
    d2Env.constants recursor.name = some recursor.toVConstant := by
  obtain ⟨trace⟩ := d2Trace
  exact trace.rec_lookup hrecursor

theorem d2Env_rule_mem {rule : VDefEq}
    (hrule : rule ∈ TreeGen.generatedRules) : d2Env.defeqs rule := by
  obtain ⟨trace⟩ := d2Trace
  exact trace.rule_mem hrule

/-- The registered defeqs of the block-extended environment, inverted
exactly: a generated block rule or an inherited D1 rule.  This is the landed
`addInductBlockGeneration_defeqs` instantiated at the live fixture. -/
theorem d2Env_defeqs_iff (df : VDefEq) :
    d2Env.defeqs df ↔ df ∈ TreeGen.generatedRules ∨ d1Env.defeqs df :=
  TreeGen.addInductBlockGeneration_defeqs d1Env_addBlock df

/-! ### Structure-eta transparency of the transaction

Neither phase of the block transaction touches the structure-eta registry. -/

theorem addConst_structEtas {env env' : VEnv} {n : Name} {ci : VConstant}
    (h : env.addConst n ci = some env') {rule : VStructEta} :
    env'.structEtas rule ↔ env.structEtas rule := by
  unfold VEnv.addConst at h
  split at h
  · cases h
  · cases h
    exact Iff.rfl

theorem foldlM_addConst_structEtas {α : Type _} (name : α → Name)
    (ci : α → VConstant) :
    ∀ (xs : List α) {env env' : VEnv},
      xs.foldlM (fun env x => env.addConst (name x) (ci x)) env = some env' →
      ∀ {rule : VStructEta}, (env'.structEtas rule ↔ env.structEtas rule)
  | [], _, _, h, _ => by cases h; exact Iff.rfl
  | x :: xs, _, _, h, _ => by
    rw [List.foldlM_cons] at h
    rcases Option.bind_eq_some_iff.1 h with ⟨envx, hx, hrest⟩
    exact (foldlM_addConst_structEtas name ci xs hrest).trans
      (addConst_structEtas hx)

theorem foldl_addDefEq_structEtas :
    ∀ (dfs : List VDefEq) (env : VEnv) (rule : VStructEta),
      ((dfs.foldl VEnv.addDefEq env).structEtas rule ↔ env.structEtas rule)
  | [], _, _ => Iff.rfl
  | d :: dfs, env, rule =>
    (foldl_addDefEq_structEtas dfs (env.addDefEq d) rule).trans Iff.rfl

theorem d2Env_no_structEta (rule : VStructEta) : ¬d2Env.structEtas rule := by
  obtain ⟨trace⟩ := d2Trace
  intro h
  rw [← trace.addRules, foldl_addDefEq_structEtas] at h
  rw [foldlM_addConst_structEtas _ _ _ trace.addRecs,
    foldlM_addConst_structEtas _ _ _ trace.addCtors,
    foldlM_addConst_structEtas _ _ _ trace.addTypes] at h
  exact d1Env_no_structEta rule h

/-! ## D2 pattern layer

The block's own five iota rules are the `.rule` half of `AssembledPat`; they
must *not* appear in the `exts` list, whose members are required to be head
separated from every block rule.  The genuinely external extensions are the
three zero-universe definition rules inherited from D1. -/

/-- The `d0def` unfolding rule as a certified extension.  Its registered
tower is a bare constant, so the beta-collapsed match is the constant
pattern itself. -/
def d0DefExt : CertifiedExtension where
  df := d0DefVal.toDefEq
  pat := .defn d0DefVal.name
  rhs := .fixed d0DefVal.value d0DefClosed
  check := .true
  covers := fun _ _ => ⟨_, _, .const⟩

def d1MutAExt : CertifiedExtension where
  df := d1MutAVal.toDefEq
  pat := .defn d1MutAVal.name
  rhs := .fixed d1MutAVal.value d1MutAClosed
  check := .true
  covers := fun _ _ => ⟨_, _, .const⟩

def d1MutBExt : CertifiedExtension where
  df := d1MutBVal.toDefEq
  pat := .defn d1MutBVal.name
  rhs := .fixed d1MutBVal.value d1MutBClosed
  check := .true
  covers := fun _ _ => ⟨_, _, .const⟩

/-- The external extension list of the D2 assembly: exactly the D1
definition rules. -/
def d2Exts : List CertifiedExtension := [d0DefExt, d1MutAExt, d1MutBExt]

/-- Head separation of a definition extension from a generated iota rule.
The constructor-side obligation is vacuous: a `defn` pattern has no
constructor head. -/
theorem headSep_defn_iota {n R C : Name} {m k : Nat}
    (h1 : n ≠ R) (h2 : n ≠ C) :
    (SimplePattern.defn n).HeadSep (.iota R m C k) where
  symb_ne_symb := h1
  symb_ne_ctor := fun c hc => by cases hc; exact h2
  ctor_ne_symb := fun c hc => by simp at hc

/-- Head separation of two distinct definition extensions. -/
theorem headSep_defn_defn {n n' : Name} (h : n ≠ n') :
    (SimplePattern.defn n).HeadSep (.defn n') where
  symb_ne_symb := h
  symb_ne_ctor := fun c hc => by simp at hc
  ctor_ne_symb := fun c hc => by simp at hc

/-- Every D1 definition head is head separated from every rule of the
block. -/
theorem d2Ext_headSep_tree {n : Name}
    (h1 : n ≠ .str ``Tree "rec") (h2 : n ≠ .str ``TreeList "rec")
    (h3 : n ≠ ``Tree.leaf) (h4 : n ≠ ``Tree.node) (h5 : n ≠ ``Tree.branch)
    (h6 : n ≠ ``TreeList.nil) (h7 : n ≠ ``TreeList.cons)
    {constructor : NormalizedBlockCtor} (hc : constructor ∈ TreeGen.flatCtors) :
    (SimplePattern.defn n).HeadSep (TreeGen.rulePattern constructor) := by
  have hp : TreeGen.rulePattern constructor ∈
      TreeGen.flatCtors.map (fun c => TreeGen.rulePattern c) :=
    List.mem_map_of_mem hc
  rw [treeRulePattern_inventory] at hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with hp | hp | hp | hp | hp <;> rw [hp]
  · exact headSep_defn_iota h1 h3
  · exact headSep_defn_iota h1 h4
  · exact headSep_defn_iota h1 h5
  · exact headSep_defn_iota h2 h6
  · exact headSep_defn_iota h2 h7

/-- The complete separation certificate for the D2 assembly: the block's
five generated rules unioned with the three inherited definition rules.
Every obligation is a literal name comparison, discharged by kernel
`decide`. -/
theorem d2ExtSeparation : TreeGen.ExtSeparation d2Exts := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ext hm
    simp only [d2Exts, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;> exact trivial
  · rintro ext hm c hc
    simp only [d2Exts, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl <;>
      exact d2Ext_headSep_tree (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) hc
  · rintro e1 h1 e2 h2 hpat
    simp only [d2Exts, List.mem_cons, List.not_mem_nil, or_false] at h1 h2
    rcases h1 with rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl <;>
      first
        | rfl
        | exact absurd hpat (by decide)
  · rintro e1 h1 e2 h2 hne
    simp only [d2Exts, List.mem_cons, List.not_mem_nil, or_false] at h1 h2
    rcases h1 with rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl <;>
      first
        | exact absurd rfl hne
        | exact headSep_defn_defn (by decide)

/-- The complete D2 pattern inventory: the generated `Nat` rules inherited
from D0, and the assembled union of the new block's five generated rules
with the three inherited definition rules. -/
inductive D2Pat : (p : Pattern) → p.RHS × p.Check → Prop where
  | nat {p : Pattern} {r : p.RHS × p.Check} : NatPat p r → D2Pat p r
  | assembled {p : Pattern} {r : p.RHS × p.Check} :
      TreeGen.AssembledPat treeRuleClosure d2Exts p r → D2Pat p r

/-- Transport the complete D1 inventory into D2: the `Nat` rules stay
`IotaPat` members, and the three definition rules become extension members
of the assembly.  The payloads are literally the same terms. -/
theorem d1Pat_to_d2 {p : Pattern} {r : p.RHS × p.Check}
    (H : D1Pat p r) : D2Pat p r := by
  cases H with
  | old H =>
    cases H with
    | iota H => exact .nat H
    | defn =>
      exact .assembled (.ext d0DefExt (by simp [d2Exts]))
  | defnA => exact .assembled (.ext d1MutAExt (by simp [d2Exts]))
  | defnB => exact .assembled (.ext d1MutBExt (by simp [d2Exts]))

/-! ### Simple-pattern inventories and cross-block separation -/

def d2NatPatterns : List SimplePattern :=
  [.iota ``Nat.rec 3 ``Nat.zero 0, .iota ``Nat.rec 3 ``Nat.succ 1]

def d2AssembledPatterns : List SimplePattern :=
  [.iota (.str ``Tree "rec") 8 ``Tree.leaf 2,
   .iota (.str ``Tree "rec") 8 ``Tree.node 2,
   .iota (.str ``Tree "rec") 8 ``Tree.branch 2,
   .iota (.str ``TreeList "rec") 8 ``TreeList.nil 1,
   .iota (.str ``TreeList "rec") 8 ``TreeList.cons 3,
   .defn d0DefVal.name, .defn d1MutAVal.name, .defn d1MutBVal.name]

theorem natPat_inventory {p : Pattern} {r : p.RHS × p.Check} (H : NatPat p r) :
    ∃ sp ∈ d2NatPatterns, p = sp.toPattern := by
  rcases natPat_pattern H with hp | hp
  · exact ⟨_, by simp [d2NatPatterns], hp⟩
  · exact ⟨_, by simp [d2NatPatterns], hp⟩

theorem assembledPat_inventory {p : Pattern} {r : p.RHS × p.Check}
    (H : TreeGen.AssembledPat treeRuleClosure d2Exts p r) :
    ∃ sp ∈ d2AssembledPatterns, p = sp.toPattern := by
  cases H with
  | rule h =>
    cases h with
    | @mk i c hentry =>
      have hp : TreeGen.rulePattern c ∈
          TreeGen.flatCtors.map (fun c => TreeGen.rulePattern c) :=
        List.mem_map_of_mem (List.mem_of_getElem? hentry)
      rw [treeRulePattern_inventory] at hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      refine ⟨TreeGen.rulePattern c, ?_, rfl⟩
      rcases hp with hp | hp | hp | hp | hp <;> rw [hp] <;>
        simp [d2AssembledPatterns]
  | ext ext hmem =>
    refine ⟨ext.pat, ?_, rfl⟩
    simp only [d2Exts, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl <;> simp [d2AssembledPatterns,
      d0DefExt, d1MutAExt, d1MutBExt]

/-- Cross-block head separation: every `Nat` rule pattern is head separated
from every member of the assembly. -/
theorem d2Nat_headSep_assembled {spn spa : SimplePattern}
    (hn : spn ∈ d2NatPatterns) (ha : spa ∈ d2AssembledPatterns) :
    spn.HeadSep spa := by
  simp only [d2NatPatterns, d2AssembledPatterns, List.mem_cons,
    List.not_mem_nil, or_false] at hn ha
  rcases hn with rfl | rfl <;>
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | exact SimplePattern.HeadSep.iota_iota (by decide) (by decide)
          (by decide)
      | exact (headSep_defn_iota (by decide) (by decide)).symm

/-! ### The four `Params` non-overlap obligations

The same-block cases delegate to the landed laws: `IotaPat.pat_uniq` for the
`Nat` block and `AssembledPat.pat_uniq` (etc.) for the assembly.  Only the
*cross-block* cases are proved here, from the landed cross-term engine
`SimplePattern.HeadSep.inter_subpattern_none` and the two shape lemmas
below, which mirror the corresponding inlined cases of the landed union
proofs. -/

/-- Cross-block `pat_app_l_uniq`, for two head-separated simple patterns.
This is the inlined `(rule, ext)` case of `AssembledPat.pat_app_l_uniq`,
restated for two arbitrary head-separated simple patterns. -/
theorem simple_app_l_uniq {sp sp' : SimplePattern} {p₁ p₂ p₁' p₂' p₃ : Pattern}
    (hsep : sp.HeadSep sp')
    (h : Subpattern (.app p₁ p₂) sp.toPattern)
    (h' : Subpattern (.app p₁' p₂') sp'.toPattern)
    (h₃ : Subpattern (.var p₃) p₁) : p₁'.inter p₃ = none := by
  cases sp with
  | defn n => exact absurd (Subpattern.const_inv h) (by simp)
  | iota R m C k =>
    obtain ⟨rfl, -⟩ := RecursorIotaPattern.app_subpattern h
    obtain ⟨j, -, rfl⟩ := Subpattern.var_varN_const_le h₃
    cases sp' with
    | defn n' => exact absurd (Subpattern.const_inv h') (by simp)
    | iota R' m' C' k' =>
      obtain ⟨rfl, -⟩ := RecursorIotaPattern.app_subpattern h'
      exact Pattern.varN_const_inter_of_ne_name
        hsep.symb_ne_symb.symm _ _

/-- Cross-block `pat_app_uniq`, for two head-separated simple patterns. -/
theorem simple_app_uniq {sp sp' : SimplePattern}
    {p₁ p₂ p₁' p₂' p₃ p₃' : Pattern}
    (hsep : sp.HeadSep sp')
    (h : Subpattern (.app p₁ p₂) sp.toPattern)
    (h' : Subpattern (.app p₁' p₂') sp'.toPattern)
    (h₃ : Subpattern p₃ p₁) (h₃' : Subpattern p₃' p₂') :
    p₃.inter p₃' = none := by
  cases sp with
  | defn n => exact absurd (Subpattern.const_inv h) (by simp)
  | iota R m C k =>
    obtain ⟨rfl, -⟩ := RecursorIotaPattern.app_subpattern h
    obtain ⟨j, -, rfl⟩ := h₃.varN_const_le
    cases sp' with
    | defn n' => exact absurd (Subpattern.const_inv h') (by simp)
    | iota R' m' C' k' =>
      obtain ⟨-, rfl⟩ := RecursorIotaPattern.app_subpattern h'
      obtain ⟨j', -, rfl⟩ := h₃'.varN_const_le
      exact Pattern.varN_const_inter_of_ne_name
        (hsep.symb_ne_ctor C' rfl) _ _

theorem d2Pat_simple {p : Pattern} {r : p.RHS × p.Check}
    (H : D2Pat p r) : ∃ sp : SimplePattern, p = sp.toPattern := by
  cases H with
  | nat H =>
    exact VInductDecl.BlockGenerationChecked.IotaPat.pat_simple NatGeneration H
  | assembled H =>
    exact VInductDecl.BlockGenerationChecked.AssembledPat.pat_simple TreeGen H

theorem d2Pat_uniq {p₁ p₂ p₃ p₄ : Pattern}
    {r : p₁.RHS × p₁.Check} {r' : p₂.RHS × p₂.Check}
    (H1 : D2Pat p₁ r) (H2 : D2Pat p₂ r')
    (H3 : Subpattern p₃ p₁) (H4 : p₂.inter p₃ = some p₄) :
    p₁ = p₂ ∧ p₂ = p₃ ∧ r ≍ r' := by
  cases H1 with
  | nat H1 =>
    cases H2 with
    | nat H2 =>
      exact VInductDecl.BlockGenerationChecked.IotaPat.pat_uniq NatGeneration
        H1 H2 H3 H4
    | assembled H2 =>
      obtain ⟨spn, hn, rfl⟩ := natPat_inventory H1
      obtain ⟨spa, ha, rfl⟩ := assembledPat_inventory H2
      rw [(d2Nat_headSep_assembled hn ha).inter_subpattern_none H3] at H4
      cases H4
  | assembled H1 =>
    cases H2 with
    | nat H2 =>
      obtain ⟨spa, ha, rfl⟩ := assembledPat_inventory H1
      obtain ⟨spn, hn, rfl⟩ := natPat_inventory H2
      rw [((d2Nat_headSep_assembled hn ha).symm).inter_subpattern_none H3]
        at H4
      cases H4
    | assembled H2 =>
      exact VInductDecl.BlockGenerationChecked.AssembledPat.pat_uniq TreeGen
        d2ExtSeparation H1 H2 H3 H4

theorem d2Pat_app_l {p : Pattern} {r : p.RHS × p.Check}
    {p₁ p₂ p₃ p₄ : Pattern}
    (H : D2Pat p r) (h : Subpattern (.app p₁ p₂) p) :
    ¬Subpattern (.app p₃ p₄) p₁ := by
  obtain ⟨sp, rfl⟩ := d2Pat_simple H
  exact SimplePattern.toPattern_app_l h

theorem d2Pat_app_l_uniq {p p' : Pattern}
    {r : p.RHS × p.Check} {r' : p'.RHS × p'.Check}
    {p₁ p₂ p₁' p₂' p₃ : Pattern}
    (H : D2Pat p r) (H' : D2Pat p' r')
    (h : Subpattern (.app p₁ p₂) p)
    (h' : Subpattern (.app p₁' p₂') p')
    (h₃ : Subpattern (.var p₃) p₁) : p₁'.inter p₃ = none := by
  cases H with
  | nat H =>
    cases H' with
    | nat H' =>
      exact VInductDecl.BlockGenerationChecked.IotaPat.pat_app_l_uniq
        NatGeneration H H' h h' h₃
    | assembled H' =>
      obtain ⟨spn, hn, rfl⟩ := natPat_inventory H
      obtain ⟨spa, ha, rfl⟩ := assembledPat_inventory H'
      exact simple_app_l_uniq (d2Nat_headSep_assembled hn ha) h h' h₃
  | assembled H =>
    cases H' with
    | nat H' =>
      obtain ⟨spa, ha, rfl⟩ := assembledPat_inventory H
      obtain ⟨spn, hn, rfl⟩ := natPat_inventory H'
      exact simple_app_l_uniq ((d2Nat_headSep_assembled hn ha).symm) h h' h₃
    | assembled H' =>
      exact VInductDecl.BlockGenerationChecked.AssembledPat.pat_app_l_uniq
        TreeGen d2ExtSeparation H H' h h' h₃

theorem d2Pat_app_uniq {p p' : Pattern}
    {r : p.RHS × p.Check} {r' : p'.RHS × p'.Check}
    {p₁ p₂ p₁' p₂' p₃ p₃' : Pattern}
    (H : D2Pat p r) (H' : D2Pat p' r')
    (h : Subpattern (.app p₁ p₂) p)
    (h' : Subpattern (.app p₁' p₂') p')
    (h₃ : Subpattern p₃ p₁) (h₃' : Subpattern p₃' p₂') :
    p₃.inter p₃' = none := by
  cases H with
  | nat H =>
    cases H' with
    | nat H' =>
      exact VInductDecl.BlockGenerationChecked.IotaPat.pat_app_uniq
        NatGeneration H H' h h' h₃ h₃'
    | assembled H' =>
      obtain ⟨spn, hn, rfl⟩ := natPat_inventory H
      obtain ⟨spa, ha, rfl⟩ := assembledPat_inventory H'
      exact simple_app_uniq (d2Nat_headSep_assembled hn ha) h h' h₃ h₃'
  | assembled H =>
    cases H' with
    | nat H' =>
      obtain ⟨spa, ha, rfl⟩ := assembledPat_inventory H
      obtain ⟨spn, hn, rfl⟩ := natPat_inventory H'
      exact simple_app_uniq ((d2Nat_headSep_assembled hn ha).symm) h h' h₃ h₃'
    | assembled H' =>
      exact VInductDecl.BlockGenerationChecked.AssembledPat.pat_app_uniq
        TreeGen d2ExtSeparation H H' h h' h₃ h₃'

/-! ### The classification table

The block contributes two family heads, five constructor heads, and two
recursor heads.  Major arity 8 (one parameter, two motives, five minors, no
indices) gives each recursor the symbol arity 9 demanded by `Pattern.WF` at
the top of an iota pattern. -/

def d2Classify (n : Name) : Option Classification :=
  if n = ``Tree then some (.indTy 1)
  else if n = ``TreeList then some (.indTy 1)
  else if n = ``Tree.leaf then some (.ctor 2)
  else if n = ``Tree.node then some (.ctor 2)
  else if n = ``Tree.branch then some (.ctor 2)
  else if n = ``TreeList.nil then some (.ctor 1)
  else if n = ``TreeList.cons then some (.ctor 3)
  else if n = .str ``Tree "rec" then some (.symb 9)
  else if n = .str ``TreeList "rec" then some (.symb 9)
  else d1Classify n

/-- The D1 table is the restriction of the D2 table: every name it
classifies is distinct from all nine block heads. -/
theorem d1Classify_agrees {c : Name} {cl : Classification}
    (H : d1Classify c = some cl) : d2Classify c = some cl := by
  have hcases : c = d1MutAVal.name ∨ c = d1MutBVal.name ∨
      c = d0DefVal.name ∨ c = ``Nat ∨ c = ``Nat.zero ∨ c = ``Nat.succ ∨
      c = ``Nat.rec := by
    by_cases h1 : c = d1MutAVal.name
    · exact .inl h1
    by_cases h2 : c = d1MutBVal.name
    · exact .inr (.inl h2)
    by_cases h3 : c = d0DefVal.name
    · exact .inr (.inr (.inl h3))
    by_cases h4 : c = ``Nat
    · exact .inr (.inr (.inr (.inl h4)))
    by_cases h5 : c = ``Nat.zero
    · exact .inr (.inr (.inr (.inr (.inl h5))))
    by_cases h6 : c = ``Nat.succ
    · exact .inr (.inr (.inr (.inr (.inr (.inl h6)))))
    by_cases h7 : c = ``Nat.rec
    · exact .inr (.inr (.inr (.inr (.inr (.inr h7)))))
    simp [d1Classify, d0Classify, natClassify, h1, h2, h3, h4, h5, h6,
      h7] at H
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simpa [d2Classify, d0DefVal, d1MutAVal, d1MutBVal] using H

theorem d1PatWF_lift {p : Pattern} {top : Bool} {extra : Nat}
    (H : p.WF d1Classify top extra) : p.WF d2Classify top extra := by
  induction p generalizing top extra with
  | const c => exact d1Classify_agrees H
  | var f ih => exact ih H
  | app f a ihf iha => exact ⟨ihf H.1, iha H.2⟩

theorem d2Pat_wf {p : Pattern} {r : p.RHS × p.Check}
    (H : D2Pat p r) : p.WF d2Classify := by
  cases H with
  | nat H => exact d1PatWF_lift (d1Pat_wf (.old (.iota H)))
  | assembled H =>
    cases H with
    | rule h =>
      cases h with
      | @mk i c hentry =>
        have hp : TreeGen.rulePattern c ∈
            TreeGen.flatCtors.map (fun c => TreeGen.rulePattern c) :=
          List.mem_map_of_mem (List.mem_of_getElem? hentry)
        rw [treeRulePattern_inventory] at hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        show ((TreeGen.rulePattern c).toPattern).WF d2Classify
        rcases hp with hp | hp | hp | hp | hp <;> rw [hp] <;>
          simp [SimplePattern.toPattern, Pattern.varN, Pattern.WF, d2Classify]
    | ext ext hmem =>
      simp only [d2Exts, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl
      · exact d1PatWF_lift (d1Pat_wf (.old .defn))
      · exact d1PatWF_lift (d1Pat_wf .defnA)
      · exact d1PatWF_lift (d1Pat_wf .defnB)

/-- The complete D2 structural instance: the D1 inventory extended by a live
mutual inductive block, over the block-extended environment. -/
def d2Params (univs : Nat) : Params where
  env := d2Env
  henv := d2Env_ordered
  univs := univs
  Pat := D2Pat
  classify := d2Classify
  pat_simple := d2Pat_simple
  pat_wf := d2Pat_wf
  pat_uniq := d2Pat_uniq
  pat_app_l := d2Pat_app_l
  pat_app_l_uniq := d2Pat_app_l_uniq
  pat_app_uniq := d2Pat_app_uniq

/-! ## Semantic-layer fragments

`Params.StructureEtaSound` and `Params.Semantic.iotaRule` are the two
semantic obligations that are purely registry-level: neither needs a typed
reduction site.  They are delivered here for the complete inventory. -/

theorem d2StructureEtaSound (univs : Nat) :
    @Params.StructureEtaSound (d2Params univs) := by
  letI : Params := d2Params univs
  intro rule levels Gamma params major hreg
  exact (d2Env_no_structEta rule hreg).elim

/-- Every generated rule of the block is registered in `d2Env`. -/
theorem treeRule_registered {i : Nat} {constructor : NormalizedBlockCtor}
    (hentry : TreeGen.flatCtors[i]? = some constructor) :
    d2Env.defeqs (TreeGen.rule i constructor) := by
  refine d2Env_rule_mem ?_
  have : (constructor, i) ∈ TreeGen.flatCtors.zipIdx := by
    apply List.mem_of_getElem? (i := i)
    rw [List.getElem?_zipIdx, hentry, Option.map_some, Nat.zero_add]
  simpa only [VInductDecl.BlockGenerationChecked.generatedRules,
    List.mem_map] using ⟨_, this, rfl⟩

/-- Each recursive call in a Tree/TreeList rule is attached to a strict
constructor-field position.  Unlike the concrete Nat proof, this is derived
uniformly from the block generation certificate: constructor semantics gives
the retained field lookup and generation shape aligns the normalized and raw
field telescope lengths. -/
theorem treeRule_recursive_lt {i : Nat} {constructor : NormalizedBlockCtor}
    (hentry : TreeGen.flatCtors[i]? = some constructor) :
    ∀ recursive ∈ constructor.ctor.view.recursive,
      recursive.fieldIndex <
        (constructor.ctor.rawFields treeDecl.nparams).length := by
  intro recursive hrecursive
  have hmem : constructor ∈ TreeGen.flatCtors := List.mem_of_getElem? hentry
  obtain ⟨_, _, _, ⟨_, hfield, _⟩, _⟩ :=
    (d2BlockGenerationWF.constructors constructor hmem).recursive
      recursive hrecursive
  have hlt : recursive.fieldIndex < constructor.ctor.view.fields.length :=
    (List.getElem?_eq_some_iff.mp hfield).1
  rw [TreeGen.flatCtor_fields_length hmem]
  exact hlt

/-- The RHS template of a block rule is the registered right tower applied
to the ordered capture list. -/
theorem treeRuleRHS_tower {i : Nat} {constructor : NormalizedBlockCtor}
    (hentry : TreeGen.flatCtors[i]? = some constructor) :
    TreeGen.ruleRHS treeRuleClosure hentry =
      Pattern.RHS.appN
        (.fixed (TreeGen.rule i constructor).rhs
          (treeRuleClosure.rhs_closed hentry))
        (TreeGen.captureArgs constructor) := rfl

/-- The ordered capture inventory of one block rule: the recursor side's
parameter, motives, and minors, then the constructor's fields. -/
def treeCapturePaths (constructor : NormalizedBlockCtor) :
    List (((TreeGen.rulePattern constructor).toPattern).Path) :=
  ((Pattern.varNPaths (.const (TreeGen.ruleRecName constructor))
      (TreeGen.ruleMajorArity constructor)).take
    (treeDecl.nparams + TreeGen.familyCount + TreeGen.minorCount)).map Sum.inl ++
  ((Pattern.varNPaths (.const constructor.ctor.raw.name)
      (TreeGen.ruleArgArity constructor)).drop treeDecl.nparams).map Sum.inr

theorem treeCapturePaths_map_var (constructor : NormalizedBlockCtor) :
    (treeCapturePaths constructor).map (fun path => .var path) =
      TreeGen.captureArgs constructor := by
  simp [treeCapturePaths, VInductDecl.BlockGenerationChecked.captureArgs,
    List.map_map, Function.comp_def]

/-- The `Pattern.IotaRule.rhsTower` shape for a block rule: the registered
right tower applied to the ordered capture path list. -/
theorem treeRuleRHS_capture_tower {i : Nat} {constructor : NormalizedBlockCtor}
    (hentry : TreeGen.flatCtors[i]? = some constructor) :
    TreeGen.ruleRHS treeRuleClosure hentry =
      Pattern.RHS.appN
        (.fixed (TreeGen.rule i constructor).rhs
          (treeRuleClosure.rhs_closed hentry))
        ((treeCapturePaths constructor).map fun path => .var path) :=
  (treeRuleRHS_tower hentry).trans (by rw [treeCapturePaths_map_var])

/-- Inversion for the assembly at a *variable* pattern.  `cases` cannot be
used at a concrete iota pattern — the block half's index
`(rulePattern c).toPattern` is a stuck `varN` tower — so this is the
`AssembledPat` counterpart of `IotaPat.recover`. -/
theorem assembledPat_cases {p : Pattern} {r : p.RHS × p.Check}
    (H : TreeGen.AssembledPat treeRuleClosure d2Exts p r) :
    (∃ (i : Nat) (c : NormalizedBlockCtor)
        (h : TreeGen.flatCtors[i]? = some c),
        p = (TreeGen.rulePattern c).toPattern ∧
          r ≍ (TreeGen.ruleRHS treeRuleClosure h,
            TreeGen.ruleCheck treeRuleClosure (List.mem_of_getElem? h))) ∨
      (∃ ext ∈ d2Exts, p = ext.pat.toPattern) := by
  cases H with
  | rule h =>
    cases h with
    | @mk i c hentry => exact .inl ⟨i, c, hentry, rfl, HEq.rfl⟩
  | ext ext hmem => exact .inr ⟨ext, hmem, rfl⟩

/-- `Params.Semantic.iotaRule` for the complete D2 inventory: every iota
pattern in `Pat` recovers its unique registered tower and ordered capture
inventory.  This field is purely registry-level — it needs no typed
reduction site — and is therefore delivered for both blocks. -/
theorem d2IotaRule_nonempty (univs : Nat)
    {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (H : (d2Params univs).Pat
      (RecursorIotaPattern rec major ctor arity) r) :
    Nonempty (@Pattern.IotaRule (d2Params univs) rec major ctor arity r) := by
  letI : Params := d2Params univs
  change D2Pat _ _ at H
  cases H with
  | nat H =>
    let oldRule := d1IotaRule univs (D1Pat.old (D0Pat.iota H))
    rcases oldRule with
      ⟨oldPat, df, registered, rhsClosed, capturePaths, rhsTower⟩
    exact ⟨{
      pat := D2Pat.nat H
      df := df
      registered := d1Env_le_d2Env.defeqs registered
      rhsClosed := rhsClosed
      capturePaths := capturePaths
      rhsTower := rhsTower }⟩
  | assembled H =>
    rcases assembledPat_cases H with
      ⟨i, c, hentry, hpattern, hr⟩ | ⟨ext, hmem, hpattern⟩
    · change RecursorIotaPattern rec major ctor arity =
        RecursorIotaPattern (TreeGen.ruleRecName c)
          (TreeGen.ruleMajorArity c) c.ctor.raw.name
          (TreeGen.ruleArgArity c) at hpattern
      obtain ⟨rfl, rfl, rfl, rfl⟩ := RecursorIotaPattern.inj hpattern
      obtain rfl : r = _ := eq_of_heq hr
      exact ⟨{
        pat := D2Pat.assembled (.rule (.mk hentry))
        df := TreeGen.rule i c
        registered := treeRule_registered hentry
        rhsClosed := treeRuleClosure.rhs_closed hentry
        capturePaths := treeCapturePaths c
        rhsTower := treeRuleRHS_capture_tower hentry }⟩
    · exfalso
      simp only [d2Exts, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl <;>
        exact absurd hpattern
          (by simp [RecursorIotaPattern, d0DefExt, d1MutAExt, d1MutBExt])

noncomputable def d2IotaRule (univs : Nat)
    {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (H : (d2Params univs).Pat
      (RecursorIotaPattern rec major ctor arity) r) :
    @Pattern.IotaRule (d2Params univs) rec major ctor arity r :=
  Classical.choice (d2IotaRule_nonempty univs H)

/-- Transport an inherited D1 iota descriptor into D2.  The syntax and
payload indices are unchanged; only pattern membership and registration are
weakened along the live environment extension. -/
def d1IotaRuleToD2 (univs : Nat)
    {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (rule : @Pattern.IotaRule (d1Params univs) rec major ctor arity r) :
    @Pattern.IotaRule (d2Params univs) rec major ctor arity r := by
  letI : Params := d1Params univs
  rcases rule with
    ⟨pat, df, registered, rhsClosed, capturePaths, rhsTower⟩
  letI : Params := d2Params univs
  exact {
    pat := d1Pat_to_d2 pat
    df := df
    registered := d1Env_le_d2Env.defeqs registered
    rhsClosed := rhsClosed
    capturePaths := capturePaths
    rhsTower := rhsTower }

/-- The canonical D2 descriptor of an inherited Nat rule. -/
noncomputable def d2NatIotaRule (univs : Nat)
    {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (H : NatPat (RecursorIotaPattern rec major ctor arity) r) :
    @Pattern.IotaRule (d2Params univs) rec major ctor arity r :=
  d1IotaRuleToD2 univs
    (d1IotaRule univs (D1Pat.old (D0Pat.iota H)))

/-- The fully explicit D2 descriptor of one Nat rule entry.  This variant
is indexed by the generated-rule lookup rather than an abstract `NatPat`
proof, so its registered equation and capture inventory compute directly. -/
def d2NatEntryIotaRule (univs : Nat) {i : Nat}
    {constructor : NormalizedBlockCtor}
    (hentry : NatGeneration.flatCtors[i]? = some constructor) :
    @Pattern.IotaRule (d2Params univs)
      (NatGeneration.ruleRecName constructor)
      (NatGeneration.ruleMajorArity constructor) constructor.ctor.raw.name
      (NatGeneration.ruleArgArity constructor)
      (NatGeneration.ruleRHS natRuleClosure hentry,
        NatGeneration.ruleCheck natRuleClosure
          (List.mem_of_getElem? hentry)) := by
  letI : Params := d2Params univs
  exact {
    pat := D2Pat.nat (.mk hentry)
    df := NatGeneration.rule i constructor
    registered := d1Env_le_d2Env.defeqs <|
      d0Env_le_d1Env.defeqs <|
        natFinalEnv_le_d0Env.defeqs (natRule_registered hentry)
    rhsClosed := natRuleClosure.rhs_closed hentry
    capturePaths := natCapturePaths constructor
    rhsTower := natRuleRHS_tower hentry }

/-- The canonical D2 descriptor of one generated Tree/TreeList rule. -/
def d2TreeIotaRule (univs : Nat) {i : Nat}
    {constructor : NormalizedBlockCtor}
    (hentry : TreeGen.flatCtors[i]? = some constructor) :
    @Pattern.IotaRule (d2Params univs)
      (TreeGen.ruleRecName constructor)
      (TreeGen.ruleMajorArity constructor) constructor.ctor.raw.name
      (TreeGen.ruleArgArity constructor)
      (TreeGen.ruleRHS treeRuleClosure hentry,
        TreeGen.ruleCheck treeRuleClosure (List.mem_of_getElem? hentry)) := by
  letI : Params := d2Params univs
  exact {
    pat := D2Pat.assembled (.rule (.mk hentry))
    df := TreeGen.rule i constructor
    registered := treeRule_registered hentry
    rhsClosed := treeRuleClosure.rhs_closed hentry
    capturePaths := treeCapturePaths constructor
    rhsTower := treeRuleRHS_capture_tower hentry }

/-! ## D1-to-D2 proof transport

`SExpr` retains its complete `Params` value as an inductive parameter, so
crossing from the D1 instance into the block-extended D2 instance is an
explicit syntax map.  Unlike D0/D1, the syntax layer is not hand-rolled: it
is the generic univs-agreement transport of
`Lean4Lean/Experimental/SExprTransport.lean` (R1), instantiated at the two
instances.  Only the judgment transport below (`d1StrongToD2`) is
rung-specific, because its `const`/`defn` cases consume the D2 pattern and
classifier extensions. -/

/-- The two instances agree on `univs` definitionally. -/
abbrev d1d2 (univs : Nat) :
    @Params.univs (d1Params univs) = @Params.univs (d2Params univs) := rfl

/-! ### Freshness of the nine block heads over `d1Env` -/

theorem treeLeaf_fresh : d1Env.constants ``Tree.leaf = none := by native_decide

theorem treeNode_fresh : d1Env.constants ``Tree.node = none := by native_decide

theorem treeBranch_fresh : d1Env.constants ``Tree.branch = none := by
  native_decide

theorem treeListNil_fresh : d1Env.constants ``TreeList.nil = none := by
  native_decide

theorem treeListCons_fresh : d1Env.constants ``TreeList.cons = none := by
  native_decide

theorem treeRec_fresh : d1Env.constants (.str ``Tree "rec") = none := by
  native_decide

theorem treeListRec_fresh : d1Env.constants (.str ``TreeList "rec") = none := by
  native_decide

/-! ### The nine block heads are unclassified by the D1 table -/

theorem d1Classify_tree : d1Classify ``Tree = none := by native_decide

theorem d1Classify_treeList : d1Classify ``TreeList = none := by native_decide

theorem d1Classify_treeLeaf : d1Classify ``Tree.leaf = none := by native_decide

theorem d1Classify_treeNode : d1Classify ``Tree.node = none := by native_decide

theorem d1Classify_treeBranch : d1Classify ``Tree.branch = none := by
  native_decide

theorem d1Classify_treeListNil : d1Classify ``TreeList.nil = none := by
  native_decide

theorem d1Classify_treeListCons : d1Classify ``TreeList.cons = none := by
  native_decide

theorem d1Classify_treeRec : d1Classify (.str ``Tree "rec") = none := by
  native_decide

theorem d1Classify_treeListRec : d1Classify (.str ``TreeList "rec") = none := by
  native_decide

/-- A constant of the D1 environment is none of the nine block heads, so the
D2 classifier restricts to the D1 classifier at it. -/
theorem d2Classify_of_d1Const {c : Name} {ci : VConstant}
    (hreg : d1Env.constants c = some ci) :
    d2Classify c = d1Classify c := by
  have h1 : c ≠ ``Tree := fun h => by rw [h, tree_fresh] at hreg; cases hreg
  have h2 : c ≠ ``TreeList := fun h => by
    rw [h, treeList_fresh] at hreg; cases hreg
  have h3 : c ≠ ``Tree.leaf := fun h => by
    rw [h, treeLeaf_fresh] at hreg; cases hreg
  have h4 : c ≠ ``Tree.node := fun h => by
    rw [h, treeNode_fresh] at hreg; cases hreg
  have h5 : c ≠ ``Tree.branch := fun h => by
    rw [h, treeBranch_fresh] at hreg; cases hreg
  have h6 : c ≠ ``TreeList.nil := fun h => by
    rw [h, treeListNil_fresh] at hreg; cases hreg
  have h7 : c ≠ ``TreeList.cons := fun h => by
    rw [h, treeListCons_fresh] at hreg; cases hreg
  have h8 : c ≠ .str ``Tree "rec" := fun h => by
    rw [h, treeRec_fresh] at hreg; cases hreg
  have h9 : c ≠ .str ``TreeList "rec" := fun h => by
    rw [h, treeListRec_fresh] at hreg; cases hreg
  simp [d2Classify, h1, h2, h3, h4, h5, h6, h7, h8, h9]

/-! ### Constant lookups of the block-extended environment restrict -/

theorem foldlM_addConst_constants_old {α : Type _} (name : α → Name)
    (ci : α → VConstant) {c : Name} :
    ∀ (xs : List α) {env env' : VEnv},
      xs.foldlM (fun env x => env.addConst (name x) (ci x)) env = some env' →
      (∀ x ∈ xs, name x ≠ c) →
      env'.constants c = env.constants c
  | [], _, _, h, _ => by cases h; rfl
  | x :: xs, _, _, h, hne => by
    rw [List.foldlM_cons] at h
    rcases Option.bind_eq_some_iff.1 h with ⟨envx, hx, hrest⟩
    rw [foldlM_addConst_constants_old name ci xs hrest
      (fun y hy => hne y (.tail _ hy))]
    unfold VEnv.addConst at hx
    split at hx
    · cases hx
    · cases hx
      show (if name x = c then some (ci x) else _) = _
      rw [if_neg (hne x (.head _))]

theorem foldl_addDefEq_constants :
    ∀ (dfs : List VDefEq) (env : VEnv) (c : Name),
      (dfs.foldl VEnv.addDefEq env).constants c = env.constants c
  | [], _, _ => rfl
  | d :: dfs, env, c => foldl_addDefEq_constants dfs (env.addDefEq d) c

theorem treeTypeConstants_names :
    treeDecl.blockTypeConstants.map (·.name) = [``Tree, ``TreeList] := rfl

theorem treeCtorConstants_names :
    treeDecl.blockConstructorConstants.map (·.name) =
      [``Tree.leaf, ``Tree.node, ``Tree.branch,
        ``TreeList.nil, ``TreeList.cons] := rfl

theorem treeRecursors_names :
    TreeGen.recursors.map (·.name) =
      [.str ``Tree "rec", .str ``TreeList "rec"] := rfl

/-- A D2 constant that is none of the nine block heads was already a D1
constant. -/
theorem d2Env_constants_old {c : Name} {ci : VConstant}
    (h1 : c ≠ ``Tree) (h2 : c ≠ ``TreeList)
    (h3 : c ≠ ``Tree.leaf) (h4 : c ≠ ``Tree.node) (h5 : c ≠ ``Tree.branch)
    (h6 : c ≠ ``TreeList.nil) (h7 : c ≠ ``TreeList.cons)
    (h8 : c ≠ .str ``Tree "rec") (h9 : c ≠ .str ``TreeList "rec")
    (hci : d2Env.constants c = some ci) : d1Env.constants c = some ci := by
  obtain ⟨trace⟩ := d2Trace
  rw [← trace.addRules, foldl_addDefEq_constants] at hci
  rw [foldlM_addConst_constants_old _ _ _ trace.addRecs (by
      intro x hx
      have : x.name ∈ TreeGen.recursors.map (·.name) := List.mem_map_of_mem hx
      rw [treeRecursors_names] at this
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with h | h <;> rw [h]
      · exact fun hc => h8 hc.symm
      · exact fun hc => h9 hc.symm),
    foldlM_addConst_constants_old _ _ _ trace.addCtors (by
      intro x hx
      have : x.name ∈ treeDecl.blockConstructorConstants.map (·.name) :=
        List.mem_map_of_mem hx
      rw [treeCtorConstants_names] at this
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with h | h | h | h | h <;> rw [h]
      · exact fun hc => h3 hc.symm
      · exact fun hc => h4 hc.symm
      · exact fun hc => h5 hc.symm
      · exact fun hc => h6 hc.symm
      · exact fun hc => h7 hc.symm),
    foldlM_addConst_constants_old _ _ _ trace.addTypes (by
      intro x hx
      have : x.name ∈ treeDecl.blockTypeConstants.map (·.name) :=
        List.mem_map_of_mem hx
      rw [treeTypeConstants_names] at this
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with h | h <;> rw [h]
      · exact fun hc => h1 hc.symm
      · exact fun hc => h2 hc.symm)] at hci
  exact hci

/-! ### Constant patterns of the D2 registry are inherited -/

/-- Every constant pattern of the D2 inventory is a D1 pattern: the block
contributes only iota patterns, and the extension patterns are literally the
D1 definition patterns.  Stated with an explicit pattern equation so the
dependent index of `AssembledPat` can be eliminated. -/
theorem d2Pat_at_const_aux {p : Pattern} {r : p.RHS × p.Check}
    (H : D2Pat p r) :
    ∀ {c : Name} (hp : p = .const c), D1Pat (.const c) (hp ▸ r) := by
  intro c hp
  cases H with
  | nat H =>
    exfalso
    rcases natPat_pattern H with h | h <;> rw [hp] at h <;> cases h
  | assembled H =>
    cases H with
    | rule h =>
      exfalso
      obtain ⟨i, cc, hentry, hpat, -⟩ :=
        VInductDecl.BlockGenerationChecked.IotaPat.recover TreeGen h
      rw [hp] at hpat
      cases hpat
    | ext ext hmem =>
      simp only [d2Exts, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl
      · cases hp
        exact .old .defn
      · cases hp
        exact .defnA
      · cases hp
        exact .defnB

theorem d2Pat_at_const {c : Name}
    {r : (Pattern.const c).RHS × (Pattern.const c).Check}
    (H : D2Pat (.const c) r) : D1Pat (.const c) r :=
  d2Pat_at_const_aux H rfl

/-! ### Constructor-classification transport at old constants -/

/-- A constructor-shaped D2 classification at a D1 constant restricts to the
same constructor classification in D1. -/
theorem d2CtorToD1 (univs : Nat) {c : Name} {ci : VConstant}
    (hreg : d1Env.constants c = some ci)
    (H : @CtorBundle.IsCtor (d2Params univs) c) :
    @CtorBundle.IsCtor (d1Params univs) c := by
  change ∃ cl, d2Classify c = some cl ∧
    (match cl with | .ctor _ | .etaCtor _ _ => true | _ => false) = true at H
  change ∃ cl, d1Classify c = some cl ∧
    (match cl with | .ctor _ | .etaCtor _ _ => true | _ => false) = true
  rwa [d2Classify_of_d1Const hreg] at H

theorem d2CtorToD1_cl_eq (univs : Nat) {c : Name} {ci : VConstant}
    (hreg : d1Env.constants c = some ci)
    (cl : @CtorBundle.IsCtor (d2Params univs) c) :
    (@CtorBundle.IsCtor.cl (d1Params univs) c
        (d2CtorToD1 univs hreg cl)).1 =
      (@CtorBundle.IsCtor.cl (d2Params univs) c cl).1 := by
  let oldCl := @CtorBundle.IsCtor.cl (d1Params univs) c
    (d2CtorToD1 univs hreg cl)
  let newCl := @CtorBundle.IsCtor.cl (d2Params univs) c cl
  have hnewD1 : d1Classify c = some newCl.1 := by
    have hnew := newCl.2.1
    change d2Classify c = some newCl.1 at hnew
    rwa [d2Classify_of_d1Const hreg] at hnew
  have hold : d1Classify c = some oldCl.1 := oldCl.2.1
  exact Option.some.inj (hold.symm.trans hnewD1)

/-- Reindex a D1 constructor bundle through the generic syntax transport and
the classifier restriction. -/
noncomputable def d1CtorBundleToD2 (univs : Nat) {c : Name} {ci : VConstant}
    (hreg : d1Env.constants c = some ci)
    (cl : @CtorBundle.IsCtor (d2Params univs) c)
    (F : @CtorBundle (d1Params univs) c (d2CtorToD1 univs hreg cl)) :
    @CtorBundle (d2Params univs) c cl := by
  rcases F with ⟨I, Ts, args, u, hlen, hclI, hu0⟩
  refine @CtorBundle.mk (d2Params univs) c cl I
    (Ts.map (transportExpr (d1d2 univs)))
    (args.map (transportExpr (d1d2 univs)))
    (transportLevel (d1d2 univs) u) ?_ ?_ ?_
  · rw [List.length_map, hlen, d2CtorToD1_cl_eq univs hreg cl]
  · change d1Classify I = some (.indTy args.length) at hclI
    letI : Params := d2Params univs
    change d2Classify I =
      some (.indTy (args.map (transportExpr (d1d2 univs))).length)
    simpa using d1Classify_agrees hclI
  · intro hzero
    have hback := congrArg (transportLevel (d1d2 univs).symm) hzero
    apply hu0
    apply Subtype.ext
    exact congrArg Subtype.val hback

@[simp] theorem d1CtorBundleToD2_rhs (univs : Nat) {c : Name} {ci : VConstant}
    (hreg : d1Env.constants c = some ci)
    (cl : @CtorBundle.IsCtor (d2Params univs) c)
    (F : @CtorBundle (d1Params univs) c (d2CtorToD1 univs hreg cl))
    (ls : List (@SLevel (d1Params univs))) :
    transportExpr (d1d2 univs)
        (@CtorBundle.rhs (d1Params univs) c (d2CtorToD1 univs hreg cl) F ls) =
      @CtorBundle.rhs (d2Params univs) c cl
        (d1CtorBundleToD2 univs hreg cl F)
        (ls.map (transportLevel (d1d2 univs))) := by
  rcases F with ⟨I, Ts, args, u, hlen, hclI, hu0⟩
  simp [CtorBundle.rhs, d1CtorBundleToD2,
    transportExpr_foldr_forallE, transportExpr_foldr_app]

@[simp] theorem d1CtorBundleToD2_u (univs : Nat) {c : Name} {ci : VConstant}
    (hreg : d1Env.constants c = some ci)
    (cl : @CtorBundle.IsCtor (d2Params univs) c)
    (F : @CtorBundle (d1Params univs) c (d2CtorToD1 univs hreg cl)) :
    @CtorBundle.u (d2Params univs) c cl (d1CtorBundleToD2 univs hreg cl F) =
      transportLevel (d1d2 univs)
        (@CtorBundle.u (d1Params univs) c (d2CtorToD1 univs hreg cl) F) := by
  cases F
  rfl

/-! ### Judgment transport -/

theorem d1IsDefEq_to_d2 (univs : Nat)
    {Gamma : List (@SExpr (d1Params univs))}
    {e₁ e₂ A : @SExpr (d1Params univs)}
    (H : @IsDefEq (d1Params univs) Gamma e₁ e₂ A) :
    @IsDefEq (d2Params univs) (Gamma.map (transportExpr (d1d2 univs)))
      (transportExpr (d1d2 univs) e₁) (transportExpr (d1d2 univs) e₂)
      (transportExpr (d1d2 univs) A) := by
  letI : Params := d2Params univs
  induction H with
  | bvar h => exact .bvar (transportLookup (d1d2 univs) h)
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | @sort Gamma l =>
    simpa only [transportExpr_sort, transportLevel_succ] using
      (IsDefEq.sort : IsDefEq (Gamma.map (transportExpr (d1d2 univs)))
        (.sort (transportLevel (d1d2 univs) l))
        (.sort (transportLevel (d1d2 univs) l))
        (.sort (.succ (transportLevel (d1d2 univs) l))))
  | @const c ci Gamma ls hreg hlen =>
    simpa only [transportExpr_const, transportExpr_mkInst] using
      (IsDefEq.const (Γ := Gamma.map (transportExpr (d1d2 univs)))
        (ls := ls.map (transportLevel (d1d2 univs)))
        (d1Env_le_d2Env.constants hreg) (by simpa using hlen))
  | appDF _ _ ihf iha =>
    rw [transportExpr_app, transportExpr_app, transportExpr_inst]
    exact IsDefEq.appDF ihf iha
  | lamDF _ _ ihA ihBody =>
    simpa only [List.map_cons, transportExpr_lam, transportExpr_forallE] using
      IsDefEq.lamDF ihA ihBody
  | forallEDF _ _ ihA ihBody =>
    simpa only [List.map_cons, transportExpr_forallE, transportExpr_sort,
      transportLevel_imax] using IsDefEq.forallEDF ihA ihBody
  | defeqDF _ _ ihA ihe => exact .defeqDF ihA ihe
  | beta _ _ ihBody ihArg =>
    simpa only [List.map_cons, transportExpr_app, transportExpr_lam,
      transportExpr_inst] using IsDefEq.beta ihBody ihArg
  | eta _ ih =>
    rw [transportExpr_lam, transportExpr_app, transportExpr_bvar,
      transportExpr_forallE, transportExpr_lift']
    exact IsDefEq.eta ih
  | proofIrrel _ _ _ ihp ihh ihh' => exact .proofIrrel ihp ihh ihh'
  | @extra df Gamma ls hreg hlen =>
    simpa only [transportExpr_mkInst] using
      (IsDefEq.extra (Γ := Gamma.map (transportExpr (d1d2 univs)))
        (ls := ls.map (transportLevel (d1d2 univs)))
        (d1Env_le_d2Env.defeqs hreg) (by simpa using hlen))

noncomputable def d1Action_to_d2 (univs : Nat)
    {Gamma : List (@SExpr (d1Params univs))} {p : Pattern}
    {r : p.RHS × p.Check} {e A : @SExpr (d1Params univs)}
    {m₁ : List (@SLevel (d1Params univs))}
    {m₂ : p.Path → @SExpr (d1Params univs)}
    (H : @Pattern.Action (d1Params univs) Gamma p r e m₁ m₂ A) :
    @Pattern.Action (d2Params univs)
      (Gamma.map (transportExpr (d1d2 univs))) p r
      (transportExpr (d1d2 univs) e) (m₁.map (transportLevel (d1d2 univs)))
      (fun path => transportExpr (d1d2 univs) (m₂ path))
      (transportExpr (d1d2 univs) A) := by
  rcases H with ⟨hpat, hmatched, dfs, hdefeqs, hchecked, hsound⟩
  change D1Pat p r at hpat
  refine @Pattern.Action.mk (d2Params univs)
    (Gamma := Gamma.map (transportExpr (d1d2 univs))) (p := p) (r := r)
    (e := transportExpr (d1d2 univs) e)
    (m1 := m₁.map (transportLevel (d1d2 univs)))
    (m2 := fun path => transportExpr (d1d2 univs) (m₂ path))
    (A := transportExpr (d1d2 univs) A) (d1Pat_to_d2 hpat)
    (transportMatchesS (d1d2 univs) hmatched)
    (transportDfs (d1d2 univs) dfs) ?_ ?_ ?_
  · rw [transportDfs_map_snd, hdefeqs]
    exact transport_defeqsS (d1d2 univs) r.2 m₁ m₂
  · intro a b B hmem
    simp only [transportDfs, List.mem_map] at hmem
    obtain ⟨⟨B₀, a₀, b₀⟩, hmem₀, heq⟩ := hmem
    cases heq
    exact d1IsDefEq_to_d2 univs (hchecked a₀ b₀ B₀ hmem₀)
  · simpa only [transportExpr_rhs_applyS] using d1IsDefEq_to_d2 univs hsound

/-- Transport a D1 evidence-rich derivation into the block-extended D2
syntax and registry.  The `const` and `defn` cases carry the inherited
definition patterns across the `d1Pat_to_d2` inclusion, and reindex
constructor bundles through the D2 classifier restriction at old
constants. -/
noncomputable def d1StrongToD2 (univs : Nat)
    {Gamma : List (@SExpr (d1Params univs))}
    {e₁ e₂ A : @SExpr (d1Params univs)}
    (H : @IsDefEqStrong (d1Params univs) Gamma e₁ e₂ A) :
    @IsDefEqStrong (d2Params univs) (Gamma.map (transportExpr (d1d2 univs)))
      (transportExpr (d1d2 univs) e₁) (transportExpr (d1d2 univs) e₂)
      (transportExpr (d1d2 univs) A) := by
  letI : Params := d2Params univs
  induction H with
  | bvar h _ ihA => exact .bvar (transportLookup (d1d2 univs) h) ihA
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | @sort Gamma l =>
    simpa only [transportExpr_sort, transportLevel_succ] using
      (IsDefEqStrong.sort : IsDefEqStrong
        (Gamma.map (transportExpr (d1d2 univs)))
        (.sort (transportLevel (d1d2 univs) l))
        (.sort (transportLevel (d1d2 univs) l))
        (.sort (.succ (transportLevel (d1d2 univs) l))))
  | @const c ci Gamma ls u hreg hlen hTy F hF hDef ihTy ihF ihDef =>
    let F' : ∀ cl : CtorBundle.IsCtor c, CtorBundle c cl := fun cl =>
      d1CtorBundleToD2 univs hreg cl (F (d2CtorToD1 univs hreg cl))
    simpa only [transportExpr_const, transportExpr_mkInst] using
      (@IsDefEqStrong.const (d2Params univs) c ci
      (Gamma.map (transportExpr (d1d2 univs)))
      (ls.map (transportLevel (d1d2 univs))) (transportLevel (d1d2 univs) u)
      (d1Env_le_d2Env.constants hreg)
      (by simpa only [List.length_map] using hlen) (by
        simpa only [transportExpr_mkInst, transportExpr_sort] using ihTy)
      F' (by
        intro cl
        dsimp only [F']
        rw [← d1CtorBundleToD2_rhs univs hreg cl
            (F (d2CtorToD1 univs hreg cl)) ls,
          d1CtorBundleToD2_u univs hreg cl (F (d2CtorToD1 univs hreg cl))]
        have H := ihF (d2CtorToD1 univs hreg cl)
        simp only [transportExpr_mkInst, transportExpr_sort] at H
        exact H) (by
        intro r hpat
        have hold : D1Pat (.const c) r := d2Pat_at_const hpat
        have H := ihDef hold
        rw [transportExpr_rhs_applyS] at H
        have hm2 : (fun path => transportExpr (d1d2 univs) (Empty.elim path)) =
            (Empty.elim :
              (Pattern.const c).Path → @SExpr (d2Params univs)) :=
          funext fun path => nomatch path
        rw [hm2] at H
        simpa only [transportExpr_const, transportExpr_mkInst] using H))
  | appDF _ _ _ _ _ ihA ihCod ihf iha ihResult =>
    rw [transportExpr_inst, transportExpr_inst, transportExpr_sort] at ihResult
    simpa only [List.map_cons, transportExpr_app, transportExpr_forallE,
      transportExpr_inst] using
      IsDefEqStrong.appDF ihA ihCod ihf iha ihResult
  | lamDF _ _ _ _ _ ihA ihB ihB' ihBody ihBody' =>
    simpa only [List.map_cons, transportExpr_lam, transportExpr_forallE] using
      IsDefEqStrong.lamDF ihA ihB ihB' ihBody ihBody'
  | forallEDF _ _ _ ihA ihBody ihBody' =>
    simpa only [List.map_cons, transportExpr_forallE, transportExpr_sort,
      transportLevel_imax] using
      IsDefEqStrong.forallEDF ihA ihBody ihBody'
  | defeqDF _ _ ihA ihe => exact .defeqDF ihA ihe
  | beta _ _ _ _ ihBody ihArg ihApp ihInst =>
    simp only [transportExpr_app, transportExpr_lam,
      transportExpr_inst] at ihApp
    simp only [transportExpr_inst] at ihInst
    simpa only [List.map_cons, transportExpr_app, transportExpr_lam,
      transportExpr_inst] using
      IsDefEqStrong.beta ihBody ihArg ihApp ihInst
  | @eta Gamma e A B _ _ ihTerm ihLam =>
    rw [transportExpr_lam, transportExpr_app, transportExpr_lift',
      transportExpr_bvar, transportExpr_forallE] at ihLam ⊢
    exact IsDefEqStrong.eta ihTerm ihLam
  | proofIrrel _ _ _ ihp ihh ihh' => exact .proofIrrel ihp ihh ihh'
  | @defn c ci Gamma ls u r hreg hlen hTy F hF action hRhs ihTy ihF ihRhs =>
    have hm2 : (fun path => transportExpr (d1d2 univs) (Empty.elim path)) =
        (Empty.elim :
          (Pattern.const c).Path → @SExpr (d2Params univs)) :=
      funext fun path => nomatch path
    let F' : ∀ cl : CtorBundle.IsCtor c, CtorBundle c cl := fun cl =>
      d1CtorBundleToD2 univs hreg cl (F (d2CtorToD1 univs hreg cl))
    have action' := d1Action_to_d2 univs action
    rw [transportExpr_const, transportExpr_mkInst, hm2] at action'
    have hRhs' := ihRhs
    rw [transportExpr_rhs_applyS, hm2, transportExpr_mkInst] at hRhs'
    have hTy' := ihTy
    rw [transportExpr_mkInst, transportExpr_sort] at hTy'
    have hF' : ∀ cl, IsDefEqStrong (Gamma.map (transportExpr (d1d2 univs)))
        (SExpr.mkInst (ls.map (transportLevel (d1d2 univs))) ci.type)
        ((F' cl).rhs (ls.map (transportLevel (d1d2 univs))))
        (.sort (F' cl).u) := by
      intro cl
      dsimp only [F']
      rw [← d1CtorBundleToD2_rhs univs hreg cl
          (F (d2CtorToD1 univs hreg cl)) ls,
        d1CtorBundleToD2_u univs hreg cl (F (d2CtorToD1 univs hreg cl))]
      have H := ihF (d2CtorToD1 univs hreg cl)
      simp only [transportExpr_mkInst, transportExpr_sort] at H
      exact H
    simpa only [transportExpr_const, transportExpr_mkInst,
      transportExpr_rhs_applyS, hm2] using
      IsDefEqStrong.defn (d1Env_le_d2Env.constants hreg)
        (by simpa only [List.length_map] using hlen)
        hTy' F' hF' action' hRhs'
  | extra action _ _ ihLeft ihRight =>
    rw [transportExpr_rhs_applyS] at ihRight
    simpa only [transportExpr_rhs_applyS] using
      IsDefEqStrong.extra (d1Action_to_d2 univs action) ihLeft ihRight

/-! ## D2 semantic machinery

The type-uniqueness, spine-view, and path-spine tools the semantic layer
needs are *not* re-proved here: they are the generic engine of
`Lean4Lean/Experimental/SExprGenericReplay.lean` (R2), instantiated at the
block-extended instance through one `SExpr.Replay` certificate.  This is the
first consumer of that module; D0/D1's hand-rolled copies are a recorded
deletion follow-up. -/

/-- The ambient replay certificate of the D2 instance: the block-extended
environment is well formed, and its (empty) structure-eta registry is
sound. -/
theorem d2Replay (univs : Nat) : @SExpr.Replay (d2Params univs) :=
  @SExpr.Replay.mk (d2Params univs) d2Env_wf (d2StructureEtaSound univs)



abbrev D2ContextValid (univs : Nat)
    (Gamma : List (@SExpr (d2Params univs))) : Prop :=
  @SExpr.CtxValid (d2Params univs) Gamma

abbrev D2TypesDefEq (univs : Nat) {Gamma : List (@SExpr (d2Params univs))}
    (A B : @SExpr (d2Params univs)) : Prop :=
  @SExpr.TypesDefEq (d2Params univs) Gamma A B

theorem d2TypeUniq (univs : Nat)
    {Gamma : List (@SExpr (d2Params univs))}
    {x A B : @SExpr (d2Params univs)}
    (hGamma : D2ContextValid univs Gamma)
    (hxA : @IsDefEq (d2Params univs) Gamma x x A)
    (hxB : @IsDefEq (d2Params univs) Gamma x x B) :
    D2TypesDefEq (Gamma := Gamma) univs A B :=
  @SExpr.typeUniq (d2Params univs) (d2Replay univs) _ _ _ _ hGamma hxA hxB

theorem d2TypesTrans (univs : Nat)
    {Gamma : List (@SExpr (d2Params univs))}
    {A B C : @SExpr (d2Params univs)}
    (hGamma : D2ContextValid univs Gamma)
    (hAB : D2TypesDefEq (Gamma := Gamma) univs A B)
    (hBC : D2TypesDefEq (Gamma := Gamma) univs B C) :
    D2TypesDefEq (Gamma := Gamma) univs A C :=
  @SExpr.typesTrans (d2Params univs) (d2Replay univs) _ _ _ _ hGamma hAB hBC

theorem d2TypesInst (univs : Nat)
    {Gamma : List (@SExpr (d2Params univs))}
    {D B B' e : @SExpr (d2Params univs)}
    (hBB' : D2TypesDefEq (Gamma := D :: Gamma) univs B B')
    (he : @IsDefEq (d2Params univs) Gamma e e D) :
    D2TypesDefEq (Gamma := Gamma) univs
      (@SExpr.inst (d2Params univs) B e)
      (@SExpr.inst (d2Params univs) B' e) :=
  @SExpr.typesInst (d2Params univs) _ _ _ _ _ hBB' he

theorem d2ForallEInv (univs : Nat)
    {Gamma : List (@SExpr (d2Params univs))}
    {A B A' B' : @SExpr (d2Params univs)}
    (hGamma : D2ContextValid univs Gamma)
    (hPi : D2TypesDefEq (Gamma := Gamma) univs
      (@SExpr.forallE (d2Params univs) A B)
      (@SExpr.forallE (d2Params univs) A' B')) :
    D2TypesDefEq (Gamma := Gamma) univs A A' ∧
      D2TypesDefEq (Gamma := A :: Gamma) univs B B' :=
  @SExpr.forallEInv (d2Params univs) (d2Replay univs) _ _ _ _ _ hGamma hPi

noncomputable def d2SpineConsView (univs : Nat)
    {Gamma : List (@SExpr (d2Params univs))}
    {D B Head e R : @SExpr (d2Params univs)}
    {es : List (@SExpr (d2Params univs))}
    (hGamma : D2ContextValid univs Gamma)
    (hHead : D2TypesDefEq (Gamma := Gamma) univs
      (@SExpr.forallE (d2Params univs) D B) Head)
    (H : @SpineWF (d2Params univs) Gamma Head (e :: es) R) :
    @SExpr.SpineConsView (d2Params univs) Gamma D B e es R :=
  @SExpr.spineConsView (d2Params univs) (d2Replay univs) _ _ _ _ _ _ _ hGamma hHead H

theorem d2PathSpineOfSpineWF (univs : Nat)
    {Gamma : List (@SExpr (d2Params univs))}
    {alpha : Type}
    {value type : alpha → @SExpr (d2Params univs)}
    {A B : @SExpr (d2Params univs)} {paths : List alpha}
    (hGamma : D2ContextValid univs Gamma)
    (htyped : ∀ path, @IsDefEq (d2Params univs) Gamma
      (value path) (value path) (type path))
    (H : @SpineWF (d2Params univs) Gamma A (paths.map value) B) :
    @PathSpineWF (d2Params univs) Gamma alpha value type A paths B :=
  @SExpr.pathSpineOfSpineWF (d2Params univs) (d2Replay univs) _ _ _ _ _ _ _ hGamma htyped H

/-! ## The block heads: lookups, classifications, and strong typings -/

theorem d2Env_tree_lookup :
    d2Env.constants ``Tree = some treeType.toVConstant :=
  d2Env_family_lookup (List.mem_of_getElem? (i := 0) rfl)

theorem d2Env_treeList_lookup :
    d2Env.constants ``TreeList = some treeListType.toVConstant :=
  d2Env_family_lookup (List.mem_of_getElem? (i := 1) rfl)

theorem d2Env_treeLeaf_lookup :
    d2Env.constants ``Tree.leaf = some treeType.ctors[0].toVConstant :=
  d2Env_ctor_lookup (List.mem_of_getElem? (i := 0) rfl)

theorem d2Env_treeNode_lookup :
    d2Env.constants ``Tree.node = some treeType.ctors[1].toVConstant :=
  d2Env_ctor_lookup (List.mem_of_getElem? (i := 1) rfl)

theorem d2Env_treeBranch_lookup :
    d2Env.constants ``Tree.branch = some treeType.ctors[2].toVConstant :=
  d2Env_ctor_lookup (List.mem_of_getElem? (i := 2) rfl)

theorem d2Env_treeListNil_lookup :
    d2Env.constants ``TreeList.nil = some treeListType.ctors[0].toVConstant :=
  d2Env_ctor_lookup (List.mem_of_getElem? (i := 3) rfl)

theorem d2Env_treeListCons_lookup :
    d2Env.constants ``TreeList.cons = some treeListType.ctors[1].toVConstant :=
  d2Env_ctor_lookup (List.mem_of_getElem? (i := 4) rfl)

theorem d2Env_treeRec_lookup :
    d2Env.constants (.str ``Tree "rec") =
      some TreeGen.recursors[0].toVConstant :=
  d2Env_rec_lookup (List.mem_of_getElem? (i := 0) rfl)

theorem d2Env_treeListRec_lookup :
    d2Env.constants (.str ``TreeList "rec") =
      some TreeGen.recursors[1].toVConstant :=
  d2Env_rec_lookup (List.mem_of_getElem? (i := 1) rfl)

/-- Constructor-shaped classifications of the D2 table: the five block
constructors, or an inherited D1 classification. -/
theorem d2Classify_ctor_cases {c : Name} {cl : Classification}
    (hc : d2Classify c = some cl) (hshape : ctorLike cl = true) :
    (c = ``Tree.leaf ∧ cl = .ctor 2) ∨ (c = ``Tree.node ∧ cl = .ctor 2) ∨
      (c = ``Tree.branch ∧ cl = .ctor 2) ∨
      (c = ``TreeList.nil ∧ cl = .ctor 1) ∨
      (c = ``TreeList.cons ∧ cl = .ctor 3) ∨ d1Classify c = some cl := by
  by_cases h1 : c = ``Tree
  · subst c
    simp [d2Classify] at hc
    subst cl
    simp [ctorLike] at hshape
  by_cases h2 : c = ``TreeList
  · subst c
    simp [d2Classify, h1] at hc
    subst cl
    simp [ctorLike] at hshape
  by_cases h3 : c = ``Tree.leaf
  · subst c
    simp [d2Classify, h1, h2] at hc
    exact .inl ⟨rfl, hc.symm⟩
  by_cases h4 : c = ``Tree.node
  · subst c
    simp [d2Classify, h1, h2, h3] at hc
    exact .inr (.inl ⟨rfl, hc.symm⟩)
  by_cases h5 : c = ``Tree.branch
  · subst c
    simp [d2Classify, h1, h2, h3, h4] at hc
    exact .inr (.inr (.inl ⟨rfl, hc.symm⟩))
  by_cases h6 : c = ``TreeList.nil
  · subst c
    simp [d2Classify, h1, h2, h3, h4, h5] at hc
    exact .inr (.inr (.inr (.inl ⟨rfl, hc.symm⟩)))
  by_cases h7 : c = ``TreeList.cons
  · subst c
    simp [d2Classify, h1, h2, h3, h4, h5, h6] at hc
    exact .inr (.inr (.inr (.inr (.inl ⟨rfl, hc.symm⟩))))
  by_cases h8 : c = .str ``Tree "rec"
  · subst c
    simp [d2Classify, h1, h2, h3, h4, h5, h6, h7] at hc
    subst cl
    simp [ctorLike] at hshape
  by_cases h9 : c = .str ``TreeList "rec"
  · subst c
    simp [d2Classify, h1, h2, h3, h4, h5, h6, h7, h8] at hc
    subst cl
    simp [ctorLike] at hshape
  refine .inr (.inr (.inr (.inr (.inr ?_))))
  simpa [d2Classify, h1, h2, h3, h4, h5, h6, h7, h8, h9] using hc

theorem treeType_not_ctor (univs : Nat)
    (cl : @CtorBundle.IsCtor (d2Params univs) ``Tree) : False := by
  letI : Params := d2Params univs
  have hshape : ctorLike cl.cl.1 = true := by
    have hs := cl.cl.2.2
    cases hc : cl.cl.1 <;> simp [ctorLike, hc] at hs ⊢
  have hc := cl.cl.2.1
  change d2Classify ``Tree = some cl.cl.1 at hc
  simp [d2Classify] at hc
  rw [← hc] at hshape
  simp [ctorLike] at hshape

theorem treeListType_not_ctor (univs : Nat)
    (cl : @CtorBundle.IsCtor (d2Params univs) ``TreeList) : False := by
  letI : Params := d2Params univs
  have hshape : ctorLike cl.cl.1 = true := by
    have hs := cl.cl.2.2
    cases hc : cl.cl.1 <;> simp [ctorLike, hc] at hs ⊢
  have hc := cl.cl.2.1
  change d2Classify ``TreeList = some cl.cl.1 at hc
  simp [d2Classify] at hc
  rw [← hc] at hshape
  simp [ctorLike] at hshape

/-- No D2 constant pattern lives at a name fresh over `d1Env`: the three
definition patterns name D1 constants. -/
theorem d2Pat_no_const_fresh {c : Name}
    {r : (Pattern.const c).RHS × (Pattern.const c).Check}
    (hfresh : d1Env.constants c = none) (H : D2Pat (.const c) r) : False := by
  have H1 := d2Pat_at_const H
  cases H1 with
  | old H0 =>
    cases H0 with
    | iota H' => rcases natPat_pattern H' with h | h <;> cases h
    | defn =>
      rw [d0Env_le_d1Env.constants d0Env_d0Def_lookup] at hfresh
      cases hfresh
  | defnA =>
    rw [d1Env_d1MutA_lookup] at hfresh
    cases hfresh
  | defnB =>
    rw [d1Env_d1MutB_lookup] at hfresh
    cases hfresh

/-! ### Strong typings of the family heads and constructor types -/

theorem d2TreeStrong (univs : Nat) (Gamma : List (@SExpr (d2Params univs)))
    (l : @SLevel (d2Params univs)) :
    @IsDefEqStrong (d2Params univs) Gamma
      (@SExpr.const (d2Params univs) ``Tree [l])
      (@SExpr.const (d2Params univs) ``Tree [l])
      (@SExpr.forallE (d2Params univs)
        (@SExpr.sort (d2Params univs) (@SLevel.succ (d2Params univs) l))
        (@SExpr.sort (d2Params univs) (@SLevel.succ (d2Params univs) l))) := by
  letI : Params := d2Params univs
  let F : ∀ cl : CtorBundle.IsCtor ``Tree, CtorBundle ``Tree cl := fun cl =>
    (treeType_not_ctor univs cl).elim
  have H : IsDefEqStrong Gamma (.const ``Tree [l]) (.const ``Tree [l])
      (SExpr.mkInst [l] treeType.toVConstant.type) := by
    refine .const (u := SLevel.imax l.succ.succ l.succ.succ)
      d2Env_tree_lookup rfl ?_ F ?_ ?_
    · change IsDefEqStrong Gamma
        (.forallE (.sort l.succ) (.sort l.succ))
        (.forallE (.sort l.succ) (.sort l.succ))
        (.sort (SLevel.imax l.succ.succ l.succ.succ))
      exact .forallEDF .sort .sort .sort
    · intro cl
      exact (treeType_not_ctor univs cl).elim
    · intro r hpat
      exact (d2Pat_no_const_fresh tree_fresh hpat).elim
  exact H

theorem d2TreeListStrong (univs : Nat)
    (Gamma : List (@SExpr (d2Params univs)))
    (l : @SLevel (d2Params univs)) :
    @IsDefEqStrong (d2Params univs) Gamma
      (@SExpr.const (d2Params univs) ``TreeList [l])
      (@SExpr.const (d2Params univs) ``TreeList [l])
      (@SExpr.forallE (d2Params univs)
        (@SExpr.sort (d2Params univs) (@SLevel.succ (d2Params univs) l))
        (@SExpr.sort (d2Params univs) (@SLevel.succ (d2Params univs) l))) := by
  letI : Params := d2Params univs
  let F : ∀ cl : CtorBundle.IsCtor ``TreeList, CtorBundle ``TreeList cl :=
    fun cl => (treeListType_not_ctor univs cl).elim
  have H : IsDefEqStrong Gamma
      (.const ``TreeList [l]) (.const ``TreeList [l])
      (SExpr.mkInst [l] treeListType.toVConstant.type) := by
    refine .const (u := SLevel.imax l.succ.succ l.succ.succ)
      d2Env_treeList_lookup rfl ?_ F ?_ ?_
    · change IsDefEqStrong Gamma
        (.forallE (.sort l.succ) (.sort l.succ))
        (.forallE (.sort l.succ) (.sort l.succ))
        (.sort (SLevel.imax l.succ.succ l.succ.succ))
      exact .forallEDF .sort .sort .sort
    · intro cl
      exact (treeListType_not_ctor univs cl).elim
    · intro r hpat
      exact (d2Pat_no_const_fresh treeList_fresh hpat).elim
  exact H

/-- Application of the `Tree` head to a type argument. -/
theorem d2TreeAppStrong (univs : Nat)
    {Gamma : List (@SExpr (d2Params univs))} {x : @SExpr (d2Params univs)}
    (l : @SLevel (d2Params univs))
    (hx : @IsDefEqStrong (d2Params univs) Gamma x x
      (@SExpr.sort (d2Params univs) (@SLevel.succ (d2Params univs) l))) :
    @IsDefEqStrong (d2Params univs) Gamma
      (@SExpr.app (d2Params univs)
        (@SExpr.const (d2Params univs) ``Tree [l]) x)
      (@SExpr.app (d2Params univs)
        (@SExpr.const (d2Params univs) ``Tree [l]) x)
      (@SExpr.sort (d2Params univs) (@SLevel.succ (d2Params univs) l)) := by
  letI : Params := d2Params univs
  have h := IsDefEqStrong.appDF (.sort : IsDefEqStrong Gamma
      (.sort l.succ) (.sort l.succ) (.sort l.succ.succ))
    (.sort : IsDefEqStrong (.sort l.succ :: Gamma)
      (.sort l.succ) (.sort l.succ) (.sort l.succ.succ))
    (d2TreeStrong univs Gamma l) hx
    (.sort : IsDefEqStrong Gamma
      (.sort l.succ) (.sort l.succ) (.sort l.succ.succ))
  exact h

theorem d2TreeListAppStrong (univs : Nat)
    {Gamma : List (@SExpr (d2Params univs))} {x : @SExpr (d2Params univs)}
    (l : @SLevel (d2Params univs))
    (hx : @IsDefEqStrong (d2Params univs) Gamma x x
      (@SExpr.sort (d2Params univs) (@SLevel.succ (d2Params univs) l))) :
    @IsDefEqStrong (d2Params univs) Gamma
      (@SExpr.app (d2Params univs)
        (@SExpr.const (d2Params univs) ``TreeList [l]) x)
      (@SExpr.app (d2Params univs)
        (@SExpr.const (d2Params univs) ``TreeList [l]) x)
      (@SExpr.sort (d2Params univs) (@SLevel.succ (d2Params univs) l)) := by
  letI : Params := d2Params univs
  have h := IsDefEqStrong.appDF (.sort : IsDefEqStrong Gamma
      (.sort l.succ) (.sort l.succ) (.sort l.succ.succ))
    (.sort : IsDefEqStrong (.sort l.succ :: Gamma)
      (.sort l.succ) (.sort l.succ) (.sort l.succ.succ))
    (d2TreeListStrong univs Gamma l) hx
    (.sort : IsDefEqStrong Gamma
      (.sort l.succ) (.sort l.succ) (.sort l.succ.succ))
  exact h

/-! ## `Params.Semantic.ctor` for the block-extended inventory

The five block constructors are Type-sorted, so their bundles are
unproblematic: each constructor's instantiated type is *literally* the
bundle's `rhs` (the field telescope over the family head applied to the
parameter), so the bundle obligation reduces to a self-typing of that Pi
tower.  Old constants transport through `d1Ctor`. -/

/-- The bundle level of a two-field Type-sorted constructor is nonzero. -/
theorem d2CtorLevel_ne_zero (univs : Nat)
    (u : @SLevel (d2Params univs)) (hu : ∀ v, 0 < u.1 v) :
    u ≠ @SLevel.zero (d2Params univs) := by
  intro h
  have hv := congrArg (fun l : @SLevel (d2Params univs) => l.1 []) h
  have hpos := hu []
  have hz : (@SLevel.zero (d2Params univs)).1 [] = 0 := rfl
  have hv' : u.1 [] = (@SLevel.zero (d2Params univs)).1 [] := hv
  rw [hv', hz] at hpos
  exact absurd hpos (Nat.lt_irrefl 0)

theorem d2Imax_pos (univs : Nat) (u v : @SLevel (d2Params univs))
    (hv : ∀ w, 0 < v.1 w) : ∀ w, 0 < (@SLevel.imax (d2Params univs) u v).1 w := by
  intro w
  have hw := hv w
  show 0 < Lean.Nat.imax (u.1 w) (v.1 w)
  simp only [Lean.Nat.imax]
  rw [if_neg (by omega)]
  exact Nat.lt_of_lt_of_le hw (Nat.le_max_right _ _)

theorem d2Succ_pos (univs : Nat) (u : @SLevel (d2Params univs)) :
    ∀ w, 0 < (@SLevel.succ (d2Params univs) u).1 w := fun _ => Nat.succ_pos _

/-- Self-typing of the `α` binder variable at the head of every block
constructor's telescope. -/
theorem d2AlphaStrong (univs : Nat) (Gamma : List (@SExpr (d2Params univs)))
    (l : @SLevel (d2Params univs)) :
    @IsDefEqStrong (d2Params univs)
      (@SExpr.sort (d2Params univs) (@SLevel.succ (d2Params univs) l) :: Gamma)
      (@SExpr.bvar (d2Params univs) 0) (@SExpr.bvar (d2Params univs) 0)
      (@SExpr.sort (d2Params univs) (@SLevel.succ (d2Params univs) l)) := by
  letI : Params := d2Params univs
  exact .bvar .zero (by exact IsDefEqStrong.sort)

theorem d2BvarStrong (univs : Nat) {Gamma : List (@SExpr (d2Params univs))}
    {i : Nat} {A : @SExpr (d2Params univs)}
    {u : @SLevel (d2Params univs)}
    (h : @Lookup (d2Params univs) Gamma i A)
    (hA : @IsDefEqStrong (d2Params univs) Gamma A A
      (@SExpr.sort (d2Params univs) u)) :
    @IsDefEqStrong (d2Params univs) Gamma
      (@SExpr.bvar (d2Params univs) i) (@SExpr.bvar (d2Params univs) i) A :=
  @IsDefEqStrong.bvar (d2Params univs) Gamma i A u h hA

/-- The result type of the D2 constructor bridge. -/
def D2CtorResult (univs : Nat) {c : Name} {ci : VConstant}
    (ls : List (@SLevel (d2Params univs)))
    (Gamma : List (@SExpr (d2Params univs)))
    (cl : @CtorBundle.IsCtor (d2Params univs) c) : Type :=
  letI : Params := d2Params univs
  {F : CtorBundle c cl //
    IsDefEqStrong Gamma (SExpr.mkInst ls ci.type) (F.rhs ls) (.sort F.u)}

section BlockBundles

variable (univs : Nat)

/-- `Tree.leaf`: one type parameter and one `α` field. -/
theorem d2TreeLeafBundle {ls : List (@SLevel (d2Params univs))}
    {Gamma : List (@SExpr (d2Params univs))}
    (hlen : ls.length = 1)
    (cl : @CtorBundle.IsCtor (d2Params univs) ``Tree.leaf) :
    Nonempty (D2CtorResult (ci := treeType.ctors[0].toVConstant)
      univs ls Gamma cl) := by
  letI : Params := d2Params univs
  obtain ⟨l, rfl⟩ := List.length_eq_one_iff.mp hlen
  have hcl : cl.cl.1 = .ctor 2 := by
    have hc := cl.cl.2.1
    change d2Classify ``Tree.leaf = some cl.cl.1 at hc
    simpa [d2Classify] using hc.symm
  let u : SLevel := .imax l.succ.succ (.imax l.succ l.succ)
  let F : CtorBundle ``Tree.leaf cl := {
    I := ``Tree
    Ts := [.sort l.succ, .bvar 0]
    args := [.bvar 1]
    u := u
    hlen := by simp [hcl, Classification.arity]
    hclI := by
      change d2Classify ``Tree = some (.indTy 1)
      simp [d2Classify]
    hu0 := d2CtorLevel_ne_zero univs u
      (d2Imax_pos univs _ _ (d2Imax_pos univs _ _ (d2Succ_pos univs _))) }
  refine ⟨⟨F, ?_⟩⟩
  change IsDefEqStrong Gamma
    (.forallE (.sort l.succ)
      (.forallE (.bvar 0) ((SExpr.const ``Tree [l]).app (.bvar 1))))
    (.forallE (.sort l.succ)
      (.forallE (.bvar 0) ((SExpr.const ``Tree [l]).app (.bvar 1))))
    (.sort u)
  refine .forallEDF (.sort) ?_ ?_ <;>
    exact .forallEDF (d2AlphaStrong univs Gamma l)
      (d2TreeAppStrong univs l (d2BvarStrong univs (.succ .zero)
        (by exact IsDefEqStrong.sort)))
      (d2TreeAppStrong univs l (d2BvarStrong univs (.succ .zero)
        (by exact IsDefEqStrong.sort)))

/-- `Tree.node`: one type parameter and one `TreeList α` field. -/
theorem d2TreeNodeBundle {ls : List (@SLevel (d2Params univs))}
    {Gamma : List (@SExpr (d2Params univs))}
    (hlen : ls.length = 1)
    (cl : @CtorBundle.IsCtor (d2Params univs) ``Tree.node) :
    Nonempty (D2CtorResult (ci := treeType.ctors[1].toVConstant)
      univs ls Gamma cl) := by
  letI : Params := d2Params univs
  obtain ⟨l, rfl⟩ := List.length_eq_one_iff.mp hlen
  have hcl : cl.cl.1 = .ctor 2 := by
    have hc := cl.cl.2.1
    change d2Classify ``Tree.node = some cl.cl.1 at hc
    simpa [d2Classify] using hc.symm
  let u : SLevel := .imax l.succ.succ (.imax l.succ l.succ)
  let F : CtorBundle ``Tree.node cl := {
    I := ``Tree
    Ts := [.sort l.succ, (SExpr.const ``TreeList [l]).app (.bvar 0)]
    args := [.bvar 1]
    u := u
    hlen := by simp [hcl, Classification.arity]
    hclI := by
      change d2Classify ``Tree = some (.indTy 1)
      simp [d2Classify]
    hu0 := d2CtorLevel_ne_zero univs u
      (d2Imax_pos univs _ _ (d2Imax_pos univs _ _ (d2Succ_pos univs _))) }
  refine ⟨⟨F, ?_⟩⟩
  change IsDefEqStrong Gamma
    (.forallE (.sort l.succ)
      (.forallE ((SExpr.const ``TreeList [l]).app (.bvar 0))
        ((SExpr.const ``Tree [l]).app (.bvar 1))))
    (.forallE (.sort l.succ)
      (.forallE ((SExpr.const ``TreeList [l]).app (.bvar 0))
        ((SExpr.const ``Tree [l]).app (.bvar 1))))
    (.sort u)
  refine .forallEDF (.sort) ?_ ?_ <;>
    exact .forallEDF
      (d2TreeListAppStrong univs l (d2AlphaStrong univs Gamma l))
      (d2TreeAppStrong univs l (d2BvarStrong univs (.succ .zero)
        (by exact IsDefEqStrong.sort)))
      (d2TreeAppStrong univs l (d2BvarStrong univs (.succ .zero)
        (by exact IsDefEqStrong.sort)))

/-- `Tree.branch`: one type parameter and one higher-order
`α → TreeList α` field. -/
theorem d2TreeBranchBundle {ls : List (@SLevel (d2Params univs))}
    {Gamma : List (@SExpr (d2Params univs))}
    (hlen : ls.length = 1)
    (cl : @CtorBundle.IsCtor (d2Params univs) ``Tree.branch) :
    Nonempty (D2CtorResult (ci := treeType.ctors[2].toVConstant)
      univs ls Gamma cl) := by
  letI : Params := d2Params univs
  obtain ⟨l, rfl⟩ := List.length_eq_one_iff.mp hlen
  have hcl : cl.cl.1 = .ctor 2 := by
    have hc := cl.cl.2.1
    change d2Classify ``Tree.branch = some cl.cl.1 at hc
    simpa [d2Classify] using hc.symm
  let u : SLevel := .imax l.succ.succ (.imax (.imax l.succ l.succ) l.succ)
  let F : CtorBundle ``Tree.branch cl := {
    I := ``Tree
    Ts := [.sort l.succ,
      .forallE (.bvar 0) ((SExpr.const ``TreeList [l]).app (.bvar 1))]
    args := [.bvar 1]
    u := u
    hlen := by simp [hcl, Classification.arity]
    hclI := by
      change d2Classify ``Tree = some (.indTy 1)
      simp [d2Classify]
    hu0 := d2CtorLevel_ne_zero univs u
      (d2Imax_pos univs _ _ (d2Imax_pos univs _ _ (d2Succ_pos univs _))) }
  refine ⟨⟨F, ?_⟩⟩
  change IsDefEqStrong Gamma
    (.forallE (.sort l.succ)
      (.forallE (.forallE (.bvar 0) ((SExpr.const ``TreeList [l]).app (.bvar 1)))
        ((SExpr.const ``Tree [l]).app (.bvar 1))))
    (.forallE (.sort l.succ)
      (.forallE (.forallE (.bvar 0) ((SExpr.const ``TreeList [l]).app (.bvar 1)))
        ((SExpr.const ``Tree [l]).app (.bvar 1))))
    (.sort u)
  have hfield : ∀ Delta : List SExpr,
      IsDefEqStrong (SExpr.sort l.succ :: Delta)
        (.forallE (.bvar 0) ((SExpr.const ``TreeList [l]).app (.bvar 1)))
        (.forallE (.bvar 0) ((SExpr.const ``TreeList [l]).app (.bvar 1)))
        (.sort (.imax l.succ l.succ)) := by
    intro Delta
    exact .forallEDF (d2AlphaStrong univs Delta l)
      (d2TreeListAppStrong univs l (d2BvarStrong univs (.succ .zero)
        (by exact IsDefEqStrong.sort)))
      (d2TreeListAppStrong univs l (d2BvarStrong univs (.succ .zero)
        (by exact IsDefEqStrong.sort)))
  refine .forallEDF (.sort) ?_ ?_ <;>
    exact .forallEDF (hfield Gamma)
      (d2TreeAppStrong univs l (d2BvarStrong univs (.succ .zero)
        (by exact IsDefEqStrong.sort)))
      (d2TreeAppStrong univs l (d2BvarStrong univs (.succ .zero)
        (by exact IsDefEqStrong.sort)))

/-- `TreeList.nil`: one type parameter and no fields. -/
theorem d2TreeListNilBundle {ls : List (@SLevel (d2Params univs))}
    {Gamma : List (@SExpr (d2Params univs))}
    (hlen : ls.length = 1)
    (cl : @CtorBundle.IsCtor (d2Params univs) ``TreeList.nil) :
    Nonempty (D2CtorResult (ci := treeListType.ctors[0].toVConstant)
      univs ls Gamma cl) := by
  letI : Params := d2Params univs
  obtain ⟨l, rfl⟩ := List.length_eq_one_iff.mp hlen
  have hcl : cl.cl.1 = .ctor 1 := by
    have hc := cl.cl.2.1
    change d2Classify ``TreeList.nil = some cl.cl.1 at hc
    simpa [d2Classify] using hc.symm
  let u : SLevel := .imax l.succ.succ l.succ
  let F : CtorBundle ``TreeList.nil cl := {
    I := ``TreeList
    Ts := [.sort l.succ]
    args := [.bvar 0]
    u := u
    hlen := by simp [hcl, Classification.arity]
    hclI := by
      change d2Classify ``TreeList = some (.indTy 1)
      simp [d2Classify]
    hu0 := d2CtorLevel_ne_zero univs u
      (d2Imax_pos univs _ _ (d2Succ_pos univs _)) }
  refine ⟨⟨F, ?_⟩⟩
  change IsDefEqStrong Gamma
    (.forallE (.sort l.succ) ((SExpr.const ``TreeList [l]).app (.bvar 0)))
    (.forallE (.sort l.succ) ((SExpr.const ``TreeList [l]).app (.bvar 0)))
    (.sort u)
  exact .forallEDF (.sort)
    (d2TreeListAppStrong univs l (d2AlphaStrong univs Gamma l))
    (d2TreeListAppStrong univs l (d2AlphaStrong univs Gamma l))

/-- `TreeList.cons`: one type parameter, a `Tree α` head and a
`TreeList α` tail. -/
theorem d2TreeListConsBundle {ls : List (@SLevel (d2Params univs))}
    {Gamma : List (@SExpr (d2Params univs))}
    (hlen : ls.length = 1)
    (cl : @CtorBundle.IsCtor (d2Params univs) ``TreeList.cons) :
    Nonempty (D2CtorResult (ci := treeListType.ctors[1].toVConstant)
      univs ls Gamma cl) := by
  letI : Params := d2Params univs
  obtain ⟨l, rfl⟩ := List.length_eq_one_iff.mp hlen
  have hcl : cl.cl.1 = .ctor 3 := by
    have hc := cl.cl.2.1
    change d2Classify ``TreeList.cons = some cl.cl.1 at hc
    simpa [d2Classify] using hc.symm
  let u : SLevel := .imax l.succ.succ (.imax l.succ (.imax l.succ l.succ))
  let F : CtorBundle ``TreeList.cons cl := {
    I := ``TreeList
    Ts := [.sort l.succ, (SExpr.const ``Tree [l]).app (.bvar 0),
      (SExpr.const ``TreeList [l]).app (.bvar 1)]
    args := [.bvar 2]
    u := u
    hlen := by simp [hcl, Classification.arity]
    hclI := by
      change d2Classify ``TreeList = some (.indTy 1)
      simp [d2Classify]
    hu0 := d2CtorLevel_ne_zero univs u
      (d2Imax_pos univs _ _ (d2Imax_pos univs _ _
        (d2Imax_pos univs _ _ (d2Succ_pos univs _)))) }
  refine ⟨⟨F, ?_⟩⟩
  change IsDefEqStrong Gamma
    (.forallE (.sort l.succ)
      (.forallE ((SExpr.const ``Tree [l]).app (.bvar 0))
        (.forallE ((SExpr.const ``TreeList [l]).app (.bvar 1))
          ((SExpr.const ``TreeList [l]).app (.bvar 2)))))
    (.forallE (.sort l.succ)
      (.forallE ((SExpr.const ``Tree [l]).app (.bvar 0))
        (.forallE ((SExpr.const ``TreeList [l]).app (.bvar 1))
          ((SExpr.const ``TreeList [l]).app (.bvar 2)))))
    (.sort u)
  have hinner : ∀ Delta : List SExpr,
      IsDefEqStrong ((SExpr.const ``Tree [l]).app (.bvar 0) ::
          SExpr.sort l.succ :: Delta)
        (.forallE ((SExpr.const ``TreeList [l]).app (.bvar 1))
          ((SExpr.const ``TreeList [l]).app (.bvar 2)))
        (.forallE ((SExpr.const ``TreeList [l]).app (.bvar 1))
          ((SExpr.const ``TreeList [l]).app (.bvar 2)))
        (.sort (.imax l.succ l.succ)) := by
    intro Delta
    exact .forallEDF
      (d2TreeListAppStrong univs l (d2BvarStrong univs (.succ .zero)
        (by exact IsDefEqStrong.sort)))
      (d2TreeListAppStrong univs l (d2BvarStrong univs
        (.succ (.succ .zero)) (by exact IsDefEqStrong.sort)))
      (d2TreeListAppStrong univs l (d2BvarStrong univs
        (.succ (.succ .zero)) (by exact IsDefEqStrong.sort)))
  refine .forallEDF (.sort) ?_ ?_ <;>
    exact .forallEDF
      (d2TreeAppStrong univs l (d2AlphaStrong univs Gamma l))
      (hinner Gamma) (hinner Gamma)

end BlockBundles

/-- `Params.Semantic.ctor` for the complete D2 inventory. -/
theorem d2Ctor_nonempty (univs : Nat) {c : Name} {ci : VConstant}
    {ls : List (@SLevel (d2Params univs))}
    {Gamma : List (@SExpr (d2Params univs))}
    (hci : d2Env.constants c = some ci)
    (hlen : ls.length = ci.uvars)
    (cl : @CtorBundle.IsCtor (d2Params univs) c) :
    Nonempty (D2CtorResult (ci := ci) univs ls Gamma cl) := by
  letI : Params := d2Params univs
  have hshape : ctorLike cl.cl.1 = true := by
    have hs := cl.cl.2.2
    cases hc : cl.cl.1 <;> simp [ctorLike, hc] at hs ⊢
  have hcases := d2Classify_ctor_cases cl.cl.2.1 hshape
  rcases hcases with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ | hold
  · obtain rfl : ci = treeType.ctors[0].toVConstant :=
      Option.some.inj (hci.symm.trans d2Env_treeLeaf_lookup)
    exact d2TreeLeafBundle univs hlen cl
  · obtain rfl : ci = treeType.ctors[1].toVConstant :=
      Option.some.inj (hci.symm.trans d2Env_treeNode_lookup)
    exact d2TreeNodeBundle univs hlen cl
  · obtain rfl : ci = treeType.ctors[2].toVConstant :=
      Option.some.inj (hci.symm.trans d2Env_treeBranch_lookup)
    exact d2TreeBranchBundle univs hlen cl
  · obtain rfl : ci = treeListType.ctors[0].toVConstant :=
      Option.some.inj (hci.symm.trans d2Env_treeListNil_lookup)
    exact d2TreeListNilBundle univs hlen cl
  · obtain rfl : ci = treeListType.ctors[1].toVConstant :=
      Option.some.inj (hci.symm.trans d2Env_treeListCons_lookup)
    exact d2TreeListConsBundle univs hlen cl
  · -- an inherited constant: restrict, apply `d1Ctor`, and transport back.
    -- `hold` classifies `c` in D1, and the nine block heads are unclassified
    -- there, so `c` is none of them and its D2 constant is a D1 constant.
    have hci' : d1Env.constants c = some ci :=
      d2Env_constants_old
        (by rintro rfl; rw [d1Classify_tree] at hold; cases hold)
        (by rintro rfl; rw [d1Classify_treeList] at hold; cases hold)
        (by rintro rfl; rw [d1Classify_treeLeaf] at hold; cases hold)
        (by rintro rfl; rw [d1Classify_treeNode] at hold; cases hold)
        (by rintro rfl; rw [d1Classify_treeBranch] at hold; cases hold)
        (by rintro rfl; rw [d1Classify_treeListNil] at hold; cases hold)
        (by rintro rfl; rw [d1Classify_treeListCons] at hold; cases hold)
        (by rintro rfl; rw [d1Classify_treeRec] at hold; cases hold)
        (by rintro rfl; rw [d1Classify_treeListRec] at hold; cases hold)
        hci
    let oldGamma := Gamma.map (transportExpr (d1d2 univs).symm)
    let oldLs := ls.map (transportLevel (d1d2 univs).symm)
    have oldLen : oldLs.length = ci.uvars := by simpa [oldLs] using hlen
    let oldCl := d2CtorToD1 univs hci' cl
    let oldF : @CtorBundle (d1Params univs) c oldCl :=
      (d1Ctor univs (Gamma := oldGamma) (ls := oldLs) hci' oldLen oldCl).1
    have oldProof : @IsDefEqStrong (d1Params univs) oldGamma
        (@SExpr.mkInst (d1Params univs) oldLs ci.type)
        (@CtorBundle.rhs (d1Params univs) c oldCl oldF oldLs)
        (@SExpr.sort (d1Params univs)
          (@CtorBundle.u (d1Params univs) c oldCl oldF)) :=
      (d1Ctor univs (Gamma := oldGamma) (ls := oldLs) hci' oldLen oldCl).2
    refine ⟨⟨d1CtorBundleToD2 univs hci' cl oldF, ?_⟩⟩
    have H := d1StrongToD2 univs oldProof
    dsimp only [oldGamma, oldLs] at H
    simp only [transport_context_roundtrip, transportExpr_mkInst,
      transportExpr_sort] at H
    rw [d1CtorBundleToD2_rhs univs hci' cl oldF
      (ls.map (transportLevel (d1d2 univs).symm))] at H
    simpa only [transport_level_list_roundtrip,
      d1CtorBundleToD2_u] using H

noncomputable def d2Ctor (univs : Nat) {c : Name} {ci : VConstant}
    {ls : List (@SLevel (d2Params univs))}
    {Gamma : List (@SExpr (d2Params univs))}
    (hci : d2Env.constants c = some ci)
    (hlen : ls.length = ci.uvars)
    (cl : @CtorBundle.IsCtor (d2Params univs) c) :
    D2CtorResult (ci := ci) univs ls Gamma cl :=
  Classical.choice (d2Ctor_nonempty univs hci hlen cl)

/-! ## `Params.Semantic.defn` for the block-extended inventory

The block contributes no constant pattern, so every `defn` obligation is an
inherited D1 one, transported. -/

theorem d2Defn (univs : Nat) {c : Name}
    {r : (Pattern.const c).RHS × (Pattern.const c).Check}
    (H : (d2Params univs).Pat (.const c) r) :
    ∃ (value : VExpr) (closed : value.Closed),
      r = (.fixed value closed, .true) ∧
      ∀ {ci : VConstant} {ls : List (@SLevel (d2Params univs))}
        {Gamma : List (@SExpr (d2Params univs))},
        d2Env.constants c = some ci → ls.length = ci.uvars →
        @IsDefEqStrong (d2Params univs) Gamma
          (@SExpr.const (d2Params univs) c ls)
          (@SExpr.mkInst (d2Params univs) ls value)
          (@SExpr.mkInst (d2Params univs) ls ci.type) := by
  letI : Params := d2Params univs
  change D2Pat (.const c) r at H
  obtain ⟨value, closed, rfl, hunfold⟩ := d1Defn univs (d2Pat_at_const H)
  refine ⟨value, closed, rfl, ?_⟩
  intro ci ls Gamma hci hlen
  have hd1 : d1Env.constants c = some ci := by
    have H1 := d2Pat_at_const H
    cases H1 with
    | old H0 =>
      cases H0 with
      | iota H' => exact (natPat_no_const univs (by exact H')).elim
      | defn =>
        have hlook := d0Env_le_d1Env.constants d0Env_d0Def_lookup
        rw [hlook]
        rw [d1Env_le_d2Env.constants hlook] at hci
        exact hci.symm ▸ rfl
    | defnA =>
      rw [d1Env_d1MutA_lookup]
      rw [d1Env_le_d2Env.constants d1Env_d1MutA_lookup] at hci
      exact hci.symm ▸ rfl
    | defnB =>
      rw [d1Env_d1MutB_lookup]
      rw [d1Env_le_d2Env.constants d1Env_d1MutB_lookup] at hci
      exact hci.symm ▸ rfl
  let oldGamma := Gamma.map (transportExpr (d1d2 univs).symm)
  let oldLs := ls.map (transportLevel (d1d2 univs).symm)
  have oldLen : oldLs.length = ci.uvars := by simpa [oldLs] using hlen
  have H1 := d1StrongToD2 univs
    (hunfold (ci := ci) (ls := oldLs) (Gamma := oldGamma) hd1 oldLen)
  dsimp only [oldGamma, oldLs] at H1
  simpa only [transport_context_roundtrip, transportExpr_const,
    transportExpr_mkInst, transport_level_list_roundtrip] using H1

/-- Weakening specialized to the partially assembled D2 semantic bridge.

The generic `IsDefEqStrong.weak'` is stated under a complete
`Params.Semantic` instance, which is exactly what the registered-tower proof
is constructing.  D2 already has every fragment weakening actually needs:
`d2Ctor` rebuilds constructor bundles at the target context, `d2Defn`
rebuilds constant-pattern contractions there, and local iota actions carry
their own pointwise weakening.  Keeping this lemma outside the eventual
semantic instance breaks the otherwise artificial registered/weakening
cycle. -/
theorem d2StrongWeak (univs : Nat)
    {rho : Lift} {Gamma Gamma' : List (@SExpr (d2Params univs))}
    {e1 e2 A : @SExpr (d2Params univs)}
    (W : @Ctx.Lift' (d2Params univs) rho Gamma Gamma')
    (H : @IsDefEqStrong (d2Params univs) Gamma e1 e2 A) :
    @IsDefEqStrong (d2Params univs) Gamma'
      (@SExpr.lift' (d2Params univs) e1 rho)
      (@SExpr.lift' (d2Params univs) e2 rho)
      (@SExpr.lift' (d2Params univs) A rho) := by
  letI : Params := d2Params univs
  induction H generalizing rho Gamma' with
  | bvar h _ ihA => exact .bvar (h.weak' W) (ihA W)
  | symm _ ih => exact (ih W).symm
  | trans _ _ ih1 ih2 => exact (ih1 W).trans (ih2 W)
  | sort => exact .sort
  | @const c ci Gamma ls u hreg hlen hTy F hF hDef ihTy ihF ihDef =>
    rw [((Params.henv.closedC hreg).mkInstS).lift'_eq .zero]
    have hTy' := ihTy W
    rw [((Params.henv.closedC hreg).mkInstS).lift'_eq .zero] at hTy'
    let F' : ∀ cl, CtorBundle c cl := fun cl =>
      (d2Ctor univs (Gamma := Gamma') hreg hlen cl).1
    have hF' : ∀ cl, IsDefEqStrong Gamma'
        (SExpr.mkInst ls ci.type) ((F' cl).rhs ls) (.sort (F' cl).u) := by
      intro cl
      exact (d2Ctor univs (Gamma := Gamma') hreg hlen cl).2
    have hDef' : ∀ {r : (Pattern.const c).RHS × (Pattern.const c).Check},
        Params.Pat (.const c) r →
        IsDefEqStrong Gamma' (r.1.applyS ls Empty.elim) (.const c ls)
          (SExpr.mkInst ls ci.type) := by
      intro r hpat
      obtain ⟨value, closed, hr, hdef⟩ := d2Defn univs hpat
      subst r
      simpa only [Pattern.RHS.applyS] using
        (hdef hreg hlen : IsDefEqStrong Gamma'
          (.const c ls) (SExpr.mkInst ls value)
          (SExpr.mkInst ls ci.type)).symm
    exact .const hreg hlen hTy' F' hF' hDef'
  | appDF _ _ _ _ _ ihA ihCod ihf iha ihResult =>
    have hResult := ihResult W
    rw [SExpr.lift'_inst_hi, SExpr.lift'_inst_hi] at hResult
    exact SExpr.lift'_inst_hi .. ▸
      .appDF (ihA W) (ihCod W.cons) (ihf W) (iha W) hResult
  | lamDF _ _ _ _ _ ihA ihB ihB' ihBody ihBody' =>
    exact .lamDF (ihA W) (ihB W.cons) (ihB' W.cons)
      (ihBody W.cons) (ihBody' W.cons)
  | forallEDF _ _ _ ihA ihBody ihBody' =>
    exact .forallEDF (ihA W) (ihBody W.cons) (ihBody' W.cons)
  | defeqDF _ _ ihA ihe => exact .defeqDF (ihA W) (ihe W)
  | beta _ _ _ _ ihBody ihArg ihApp ihInst =>
    have hApp := ihApp W
    have hInst := ihInst W
    simp only [SExpr.lift'_inst_hi] at hApp hInst
    rw [SExpr.lift'_inst_hi, SExpr.lift'_inst_hi]
    exact .beta (ihBody W.cons) (ihArg W) hApp hInst
  | @eta Gamma e A B hTerm hLam ihTerm ihLam =>
    have hLam' : IsDefEqStrong Gamma'
        (.lam (A.lift' rho) ((e.lift' rho).lift.app (.bvar 0)))
        (.lam (A.lift' rho) ((e.lift' rho).lift.app (.bvar 0)))
        (.forallE (A.lift' rho) (B.lift' rho.cons)) := by
      simpa [SExpr.lift, ← SExpr.lift'_comp] using ihLam W
    simpa [SExpr.lift, ← SExpr.lift'_comp] using
      IsDefEqStrong.eta (ihTerm W) hLam'
  | proofIrrel _ _ _ ihProp ihLeft ihRight =>
    exact .proofIrrel (ihProp W) (ihLeft W) (ihRight W)
  | @defn c ci Gamma ls u r hreg hlen hTy F hF action hRhs
      ihTy ihF ihRhs =>
    rw [((Params.henv.closedC hreg).mkInstS).lift'_eq .zero]
    have hTy' := ihTy W
    rw [((Params.henv.closedC hreg).mkInstS).lift'_eq .zero] at hTy'
    let F' : ∀ cl, CtorBundle c cl := fun cl =>
      (d2Ctor univs (Gamma := Gamma') hreg hlen cl).1
    have hF' : ∀ cl, IsDefEqStrong Gamma'
        (SExpr.mkInst ls ci.type) ((F' cl).rhs ls) (.sort (F' cl).u) := by
      intro cl
      exact (d2Ctor univs (Gamma := Gamma') hreg hlen cl).2
    have hempty :
        (fun path : Empty => (Empty.elim path : SExpr).lift' rho) = Empty.elim := by
      funext path
      exact nomatch path
    have hAction := action.weak' W
    simp only [SExpr.lift'] at hAction
    rw [hempty, ((Params.henv.closedC hreg).mkInstS).lift'_eq .zero] at hAction
    have hRhs' := ihRhs W
    rw [Pattern.RHS.lift'_applyS] at hRhs'
    rw [hempty, ((Params.henv.closedC hreg).mkInstS).lift'_eq .zero] at hRhs'
    rw [Pattern.RHS.lift'_applyS, hempty]
    exact IsDefEqStrong.defn hreg hlen hTy' F' hF' hAction hRhs'
  | extra action _ _ ihLeft ihRight =>
    have hRight := ihRight W
    rw [Pattern.RHS.lift'_applyS] at hRight
    simpa only [Pattern.RHS.lift'_applyS] using
      IsDefEqStrong.extra (action.weak' W) (ihLeft W) hRight

/-- Strong self-typing of a registered D2 constant once its declared type is
strongly known.  Constructor bundles and constant-pattern equations are
supplied by the already-closed `ctor`/`defn` fragments, so callers proving a
generated rule body only have to establish the declaration's type. -/
theorem d2ConstStrong (univs : Nat)
    {c : Name} {ci : VConstant}
    {ls : List (@SLevel (d2Params univs))}
    {Gamma : List (@SExpr (d2Params univs))}
    {u : @SLevel (d2Params univs)}
    (hreg : d2Env.constants c = some ci) (hlen : ls.length = ci.uvars)
    (hTy : @IsDefEqStrong (d2Params univs) Gamma
      (@SExpr.mkInst (d2Params univs) ls ci.type)
      (@SExpr.mkInst (d2Params univs) ls ci.type)
      (@SExpr.sort (d2Params univs) u)) :
    @IsDefEqStrong (d2Params univs) Gamma
      (@SExpr.const (d2Params univs) c ls)
      (@SExpr.const (d2Params univs) c ls)
      (@SExpr.mkInst (d2Params univs) ls ci.type) := by
  letI : Params := d2Params univs
  let F : ∀ cl : CtorBundle.IsCtor c, CtorBundle c cl := fun cl =>
    (d2Ctor univs (Gamma := Gamma) hreg hlen cl).1
  refine .const hreg hlen hTy F ?_ ?_
  · intro cl
    exact (d2Ctor univs (Gamma := Gamma) hreg hlen cl).2
  · intro r hpat
    obtain ⟨value, closed, hr, hdef⟩ := d2Defn univs hpat
    subst r
    simpa only [Pattern.RHS.applyS] using
      (hdef hreg hlen : IsDefEqStrong Gamma
        (.const c ls) (SExpr.mkInst ls value)
        (SExpr.mkInst ls ci.type)).symm

/-! ## `Params.Semantic.registered`: inherited rules

A registered defeq of `d2Env` is either one of the block's five generated
rules or an inherited D1 rule.  The inherited half transports; the block
half is one of the two parked obligations below. -/

/-- The inherited half of `Params.Semantic.registered`, transported from
D1's own certificate through the generic syntax transport. -/
theorem d2Registered_old (univs : Nat)
    {df : VDefEq} {ls : List (@SLevel (d2Params univs))}
    {Gamma : List (@SExpr (d2Params univs))}
    (hreg : d1Env.defeqs df) (hlen : ls.length = df.uvars) :
    @IsDefEqStrong (d2Params univs) Gamma
      (@SExpr.mkInst (d2Params univs) ls df.lhs)
      (@SExpr.mkInst (d2Params univs) ls df.rhs)
      (@SExpr.mkInst (d2Params univs) ls df.type) := by
  let oldGamma := Gamma.map (transportExpr (d1d2 univs).symm)
  let oldLs := ls.map (transportLevel (d1d2 univs).symm)
  have oldLen : oldLs.length = df.uvars := by simpa [oldLs] using hlen
  have oldLhs : @IsDefEqStrong (d1Params univs) oldGamma
      (@SExpr.mkInst (d1Params univs) oldLs df.lhs)
      (@SExpr.mkInst (d1Params univs) oldLs df.lhs)
      (@SExpr.mkInst (d1Params univs) oldLs df.type) := by
    letI : Params := d1Params univs
    letI : Params.Semantic := d1Semantic univs
    exact Params.Semantic.closedHasTypeStrong (d1Env_ordered.defEqWF hreg).1
  have oldRhs : @IsDefEqStrong (d1Params univs) oldGamma
      (@SExpr.mkInst (d1Params univs) oldLs df.rhs)
      (@SExpr.mkInst (d1Params univs) oldLs df.rhs)
      (@SExpr.mkInst (d1Params univs) oldLs df.type) := by
    letI : Params := d1Params univs
    letI : Params.Semantic := d1Semantic univs
    exact Params.Semantic.closedHasTypeStrong (d1Env_ordered.defEqWF hreg).2
  have oldEq := d1Registered univs hreg oldLen oldLhs oldRhs
  have H := d1StrongToD2 univs oldEq
  dsimp only [oldGamma, oldLs] at H
  simpa only [transport_context_roundtrip, transportExpr_mkInst,
    transport_level_list_roundtrip] using H

/-! ## Concrete δ-rank certificate

The inductive block adds iota rules but no new constant-headed definition
rules.  Consequently D2 inherits D1's dependency order unchanged:
`d1mutA > d1mutB > d0def`; every block head remains at rank zero. -/

def d2DeltaRankFn : Name → Nat := fun n =>
  if n = ``ParamsD1.d1mutA then 3
  else if n = ``ParamsD1.d1mutB then 2
  else if n = ``ParamsD0.d0def then 1
  else 0

theorem d2NatTypeLookup :
    d2Env.constants ``Nat = some InductiveFixtures.natType.toVConstant :=
  d1Env_le_d2Env.constants d1NatTypeLookup

theorem d2D0DefLookup :
    d2Env.constants ``ParamsD0.d0def = some d0DefVal.toVConstant :=
  d1Env_le_d2Env.constants d1D0DefLookup

theorem d2DeltaRankFn_nat : d2DeltaRankFn ``Nat ≤ 0 := by decide

theorem d2DeltaRankFn_natZero : d2DeltaRankFn ``Nat.zero ≤ 0 := by
  decide

theorem d2DeltaRankFn_natSucc : d2DeltaRankFn ``Nat.succ ≤ 0 := by
  decide

theorem d2DeltaRankFn_d0def :
    d2DeltaRankFn ``ParamsD0.d0def ≤ 1 := by
  decide

theorem d2DeltaRankFn_d1mutB :
    d2DeltaRankFn ``ParamsD1.d1mutB ≤ 2 := by
  decide

theorem d2NatCertR (univs : Nat) :
    letI : Params := d2Params univs
    ∀ (Gamma : List SExpr) (n : Nat),
      HasTypeStratifiedR d2DeltaRankFn Gamma
        (.const ``Nat []) (.sort (.instV [] (.succ .zero))) true (n + 1) 0 := by
  letI : Params := d2Params univs
  intro Gamma n
  exact .base (.const d2NatTypeLookup rfl d2DeltaRankFn_nat
    (.base .sort'))

theorem d2NatPiCertR (univs : Nat) :
    letI : Params := d2Params univs
    ∀ (Gamma : List SExpr) (n : Nat),
      HasTypeStratifiedR d2DeltaRankFn Gamma
        (.forallE (.const ``Nat []) (.const ``Nat []))
        (.sort (.imax (.instV [] (.succ .zero))
          (.instV [] (.succ .zero)))) true (n + 2) 0 := by
  letI : Params := d2Params univs
  intro Gamma n
  exact .base (.forallE (d2NatCertR univs Gamma n)
    (d2NatCertR univs (_ :: Gamma) n))

theorem d2SuccCertR (univs : Nat) :
    letI : Params := d2Params univs
    ∀ (Gamma : List SExpr) (n : Nat),
      HasTypeStratifiedR d2DeltaRankFn Gamma
        (.const ``Nat.succ [])
        (.forallE (.const ``Nat []) (.const ``Nat [])) true (n + 3) 0 := by
  letI : Params := d2Params univs
  intro Gamma n
  exact .base (.const (d1Env_le_d2Env.constants d1NatSuccEnvLookup) rfl
    d2DeltaRankFn_natSucc (d2NatPiCertR univs Gamma n))

theorem d2ZeroCertR (univs : Nat) :
    letI : Params := d2Params univs
    ∀ (Gamma : List SExpr),
      HasTypeStratifiedR d2DeltaRankFn Gamma
        (.const ``Nat.zero []) (.const ``Nat []) true 2 0 := by
  letI : Params := d2Params univs
  intro Gamma
  exact .base (.const (d1Env_le_d2Env.constants d1NatZeroEnvLookup) rfl
    d2DeltaRankFn_natZero (d2NatCertR univs Gamma 0))

theorem d2D0DefConstCertR (univs : Nat) :
    letI : Params := d2Params univs
    ∀ (Gamma : List SExpr) (n : Nat),
      HasTypeStratifiedR d2DeltaRankFn Gamma
        (.const ``ParamsD0.d0def []) (.const ``Nat []) true (n + 2) 1 := by
  letI : Params := d2Params univs
  intro Gamma n
  exact .base (.const d2D0DefLookup rfl d2DeltaRankFn_d0def
    ((d2NatCertR univs Gamma n).mono_rank (Nat.zero_le 1)))

theorem d2MutBValueCertR (univs : Nat) :
    letI : Params := d2Params univs
    ∀ (Gamma : List SExpr),
      HasTypeStratifiedR d2DeltaRankFn Gamma
        (.app (.const ``Nat.succ []) (.const ``ParamsD0.d0def []))
        (.const ``Nat []) true 4 1 := by
  letI : Params := d2Params univs
  intro Gamma
  refine .base (.app (u := .instV [] (.succ .zero))
    (v := .instV [] (.succ .zero))
    ((d2NatCertR univs Gamma 2).mono_rank (Nat.zero_le 1))
    ((d2NatCertR univs (_ :: Gamma) 2).mono_rank (Nat.zero_le 1))
    ((d2SuccCertR univs Gamma 0).mono_rank (Nat.zero_le 1))
    (d2D0DefConstCertR univs Gamma 1)
    ((d2NatCertR univs Gamma 2).mono_rank (Nat.zero_le 1)))

theorem d2MutBConstCertR (univs : Nat) :
    letI : Params := d2Params univs
    ∀ (Gamma : List SExpr),
      HasTypeStratifiedR d2DeltaRankFn Gamma
        (.const ``ParamsD1.d1mutB []) (.const ``Nat []) true 2 2 := by
  letI : Params := d2Params univs
  intro Gamma
  exact .base (.const (d1Env_le_d2Env.constants d1Env_d1MutB_lookup) rfl
    d2DeltaRankFn_d1mutB
    ((d2NatCertR univs Gamma 0).mono_rank (Nat.zero_le 2)))

/-- The D2 fixture's checked δ-rank certificate.  The generated block rules
are eliminated structurally because none has a constant pattern. -/
def d2DeltaRank (univs : Nat) :
    letI : Params := d2Params univs
    Params.DeltaRank := by
  letI : Params := d2Params univs
  refine ⟨d2DeltaRankFn, ?_⟩
  intro c ci value closed ls Gamma hpat hreg hlen
  change D2Pat _ _ at hpat
  have h1 := d2Pat_at_const hpat
  cases h1 with
  | old h0 =>
    cases h0 with
    | iota h => exact (natPat_no_const univs h).elim
    | defn =>
      obtain rfl := Option.some.inj (d2D0DefLookup.symm.trans hreg)
      obtain rfl := List.length_eq_zero_iff.mp hlen
      exact ⟨2, 0, by decide, d2ZeroCertR univs Gamma⟩
  | defnA =>
    obtain rfl := Option.some.inj
      ((d1Env_le_d2Env.constants d1Env_d1MutA_lookup).symm.trans hreg)
    obtain rfl := List.length_eq_zero_iff.mp hlen
    exact ⟨2, 2, by decide, d2MutBConstCertR univs Gamma⟩
  | defnB =>
    obtain rfl := Option.some.inj
      ((d1Env_le_d2Env.constants d1Env_d1MutB_lookup).symm.trans hreg)
    obtain rfl := List.length_eq_zero_iff.mp hlen
    exact ⟨4, 1, by decide, d2MutBValueCertR univs Gamma⟩

/-! ## The parked block obligations

The legacy internal assembler names four obligations of the *block* half of
`Params.Semantic`.  The preferred `D2BlockStepExact` removes discharged
bookkeeping and inherited Nat replay, leaving three fields: the Tree check,
one paired Tree replay, and the generated registered bodies.  The earlier
pair-shaped `D2BlockStep` remains as the internal assembler input;
`D2BlockStepExact.toBlockStep` reconstructs it.

The first obligation is directly `L4L-18A′`-blocked.  The Tree/TreeList
parts of the next two share that boundary: after the common recursor prefix
is replayed, their field telescope and rebuilt constructor use the
recursor-derived parameter and source levels, while the concrete constructor
spine is typed at its own parameter and levels.  Relating those two
instantiations needs both the checked parameter equality and canonical source-
level alignment.  The finite telescope/body calculations after alignment
and the registered bodies are mechanical; the inherited Nat cases are now
proved below.

**Scope note.**  The legacy capture-spine and β-collapse contracts quantify
over *every* iota rule of the D2 inventory, i.e. the block's five plus the two
inherited `Nat` rules — not only the five new ones.  That is forced, not sloppy: a
reduction-site certificate cannot be transported *downwards* along
`d1Env ≤ d2Env`, because its inputs (`typing`, `matched`) are D2-instance
derivations whose contexts and captures may mention the block's constants,
and `d1StrongToD2` only runs in the growing direction.  D1 met exactly this
and re-replayed D0's two `Nat` rules rather than transporting them
(`SExprParamsD1.lean:1925-1929`).  D2 now performs that third replay through
the generic engine (`d2NatZeroRuleReplay`, `d2NatSuccRuleReplay`), so the
preferred residual quantifies only over the five block rules.  Their checks
are likewise discharged by `d2NatChecked`, and
`D2CheckedStep.of_tree` lifts the five-entry `D2TreeCheckedStep` to the full
inventory.  The genuinely 18A′-gated premise therefore quantifies over the
five block rules only. -/

/-- (i) The `Pattern.Check` discharge of a generated rule at a matched
redex.  `TreeGen.ruleCheck` folds one `.defeq` per `treeDecl.nparams`; Tree
has exactly one parameter and no indices, so this says: the
constructor-side type parameter and the recursor-side type parameter of a
matched redex are definitionally equal.  That is injectivity of a stuck
inductive-type application, `L4L-18A′` strength — see
`plans/probes/probeG-generic-instance.lean:320` (`iotaCheck_param`).  The
semantic side cannot help: the logical relation realizes `indTy` arguments
at `.bot` (`ShapeLogRel.lean:9244`), so it retains no argument information.
This is one of the two explicit alignment facts needed by the Tree replay. -/
def D2CheckedStep (univs : Nat) : Prop :=
  letI : Params := d2Params univs
  ∀ {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {Gamma : List SExpr} {A majorTerm : SExpr}
    {recLs ctorLs : List SLevel} {recArgs ctorArgs : List SExpr}
    {mcap : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
    {captureType : (RecursorIotaPattern rec major ctor arity).Path → SExpr},
    Params.Pat (RecursorIotaPattern rec major ctor arity) r →
    Pattern.CaptureTyping Gamma mcap captureType →
    D2ContextValid univs Gamma →
    Pattern.IotaTyping Gamma rec ctor recLs ctorLs
      recArgs ctorArgs majorTerm A →
    (RecursorIotaPattern rec major ctor arity).MatchesS
      ((recArgs.foldr (fun (a f : SExpr) => f.app a) (SExpr.const rec recLs)).app
        (ctorArgs.foldr (fun (a f : SExpr) => f.app a)
          (SExpr.const ctor ctorLs))) recLs mcap →
    ∃ dfs : List (SExpr × SExpr × SExpr),
      dfs.map (·.2) = r.2.defeqsS recLs mcap ∧
      ∀ a b B, (B, a, b) ∈ dfs → IsDefEq Gamma a b B

/-- The inherited Nat rules contribute no check obligations: Nat has no
parameters and no indices, so every generated `ruleCheck` is `.true`.
This is independent of the surrounding D2 context and match. -/
theorem d2NatChecked (univs : Nat)
    {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (H : NatPat (RecursorIotaPattern rec major ctor arity) r)
    {Gamma : List (@SExpr (d2Params univs))}
    {recLs : List (@SLevel (d2Params univs))}
    {mcap : (RecursorIotaPattern rec major ctor arity).Path →
      @SExpr (d2Params univs)} :
    letI : Params := d2Params univs
    ∃ dfs : List (SExpr × SExpr × SExpr),
      dfs.map (·.2) = r.2.defeqsS recLs mcap ∧
      ∀ a b B, (B, a, b) ∈ dfs → IsDefEq Gamma a b B := by
  letI : Params := d2Params univs
  obtain ⟨i, constructor, hentry, hpattern, -⟩ :=
    VInductDecl.BlockGenerationChecked.IotaPat.recover NatGeneration H
  change RecursorIotaPattern rec major ctor arity =
    RecursorIotaPattern (NatGeneration.ruleRecName constructor)
      (NatGeneration.ruleMajorArity constructor) constructor.ctor.raw.name
      (NatGeneration.ruleArgArity constructor) at hpattern
  obtain ⟨rfl, rfl, rfl, rfl⟩ := RecursorIotaPattern.inj hpattern
  let rgen :=
    (NatGeneration.ruleRHS natRuleClosure hentry,
      NatGeneration.ruleCheck natRuleClosure (List.mem_of_getElem? hentry))
  have Hgen : NatPat
      (RecursorIotaPattern (NatGeneration.ruleRecName constructor)
        (NatGeneration.ruleMajorArity constructor) constructor.ctor.raw.name
        (NatGeneration.ruleArgArity constructor)) rgen := .mk hentry
  have hr : r ≍ rgen :=
    (VInductDecl.BlockGenerationChecked.IotaPat.pat_uniq NatGeneration
      H Hgen .refl (Pattern.inter_self _)).2.2
  obtain rfl : r = rgen := eq_of_heq hr
  have hi : i = 0 ∨ i = 1 := by
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hentry
    have : NatGeneration.flatCtors.length = 2 := rfl
    omega
  rcases hi with rfl | rfl
  · have hc := Option.some.inj
      (probeNatFlatCtorZero_lookup.symm.trans hentry)
    subst constructor
    exact ⟨[], by rfl, by simp⟩
  · have hc := Option.some.inj
      (probeNatFlatCtorSucc_lookup.symm.trans hentry)
    subst constructor
    exact ⟨[], by rfl, by simp⟩

/-- The genuinely blocked check contract, restricted to the five generated
rules of the new block.  Unlike the earlier over-strong draft, the contract
retains the concrete capture typing, valid context, typed recursor and
constructor spines, and successful match from the reduction site. -/
def D2TreeCheckedStep (univs : Nat) : Prop :=
  letI : Params := d2Params univs
  ∀ {i : Nat} {constructor : NormalizedBlockCtor}
    (hentry : TreeGen.flatCtors[i]? = some constructor)
    {Gamma : List SExpr} {A majorTerm : SExpr}
    {recLs ctorLs : List SLevel} {recArgs ctorArgs : List SExpr}
    {mcap : ((TreeGen.rulePattern constructor).toPattern).Path → SExpr}
    {captureType : ((TreeGen.rulePattern constructor).toPattern).Path → SExpr},
    Pattern.CaptureTyping Gamma mcap captureType →
    D2ContextValid univs Gamma →
    Pattern.IotaTyping Gamma (TreeGen.ruleRecName constructor)
      constructor.ctor.raw.name recLs ctorLs recArgs ctorArgs majorTerm A →
    ((TreeGen.rulePattern constructor).toPattern).MatchesS
      ((recArgs.foldr (fun (a f : SExpr) => f.app a)
          (SExpr.const (TreeGen.ruleRecName constructor) recLs)).app
        (ctorArgs.foldr (fun (a f : SExpr) => f.app a)
          (SExpr.const constructor.ctor.raw.name ctorLs))) recLs mcap →
    ∃ dfs : List (SExpr × SExpr × SExpr),
      dfs.map (·.2) =
        (TreeGen.ruleCheck treeRuleClosure
          (List.mem_of_getElem? hentry)).defeqsS recLs mcap ∧
      ∀ a b B, (B, a, b) ∈ dfs → IsDefEq Gamma a b B

/-- Canonical source-level alignment needed by the generated Tree/TreeList
capture and collapse replay.  Theory's block theorem states its constructor
spine directly at `sourceLevels.map (VLevel.inst recLs)`; an SExpr reduction
site instead permits an independently typed `ctorLs`.  Showing that the two
lists agree is a head-injectivity/normalization consequence, not a finite
rule computation.  This contract names that shared research boundary; it is
currently subsumed by the paired `D2TreeReplayStep` premise below rather than
added as a redundant field of `D2BlockStepExact`. -/
def D2TreeLevelAlignmentStep (univs : Nat) : Prop :=
  letI : Params := d2Params univs
  ∀ {i : Nat} {constructor : NormalizedBlockCtor},
    TreeGen.flatCtors[i]? = some constructor →
    ∀ {Gamma : List SExpr} {A majorTerm : SExpr}
      {recLs ctorLs : List SLevel} {recArgs ctorArgs : List SExpr},
      D2ContextValid univs Gamma →
      Pattern.IotaTyping Gamma (TreeGen.ruleRecName constructor)
        constructor.ctor.raw.name recLs ctorLs recArgs ctorArgs majorTerm A →
      ctorLs = TreeGen.sourceLevels.map (SLevel.instV recLs)

/-- Lift the five-rule block check to the complete D2 inventory.  The two
Nat cases are discharged by `d2NatChecked`; definition extensions cannot
inhabit a recursor-iota pattern. -/
theorem D2CheckedStep.of_tree (univs : Nat)
    (h : D2TreeCheckedStep univs) : D2CheckedStep univs := by
  letI : Params := d2Params univs
  intro rec major ctor arity r Gamma A majorTerm recLs ctorLs recArgs ctorArgs
    mcap captureType hpat captureTyping hGamma typing matched
  change D2Pat (RecursorIotaPattern rec major ctor arity) r at hpat
  cases hpat with
  | nat H =>
    exact d2NatChecked univs H
  | assembled H =>
    rcases assembledPat_cases H with
      ⟨i, c, hentry, hpattern, hr⟩ | ⟨ext, hmem, hpattern⟩
    · change RecursorIotaPattern rec major ctor arity =
        RecursorIotaPattern (TreeGen.ruleRecName c)
          (TreeGen.ruleMajorArity c) c.ctor.raw.name
          (TreeGen.ruleArgArity c) at hpattern
      obtain ⟨rfl, rfl, rfl, rfl⟩ := RecursorIotaPattern.inj hpattern
      obtain rfl : r = _ := eq_of_heq hr
      exact h hentry captureTyping hGamma typing matched
    · exfalso
      simp only [d2Exts, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl <;>
        exact absurd hpattern
          (by simp [RecursorIotaPattern, d0DefExt, d1MutAExt, d1MutBExt])

/-- (ii) The rule's capture inventory re-indexed onto its own binder
telescope, with the rule's level arity.  The generic engine
(`SExpr.iotaSiteOf`) consumes this and supplies every other site field;
Theory's own generic block-rule soundness theorem takes the same spine as a
hypothesis (`InductivePatternWF.lean`, the `hcaps` argument), so this is the
engine's interface boundary rather than an omission.  The inherited Nat
cases and the eight common Tree recursor arguments are mechanical.  The
remaining Tree field suffix is typed at the constructor-side parameter and
levels, so replaying it at the generated rule's canonical recursor-side
telescope also consumes `D2TreeCheckedStep` and
`D2TreeLevelAlignmentStep`-strength facts.  The level-arity conjunct in this
legacy form is proved unconditionally later by `d2IotaRule_levelsLength`;
`D2CaptureSpineCoreStep` is the current, deliberately unfactored residual. -/
def D2CaptureSpineStep (univs : Nat) : Prop :=
  letI : Params := d2Params univs
  ∀ {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {Gamma : List SExpr} {A majorTerm : SExpr}
    {recLs ctorLs : List SLevel} {recArgs ctorArgs : List SExpr}
    {mcap : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
    (rule : Pattern.IotaRule r),
    D2ContextValid univs Gamma →
    Pattern.IotaTyping Gamma rec ctor recLs ctorLs
      recArgs ctorArgs majorTerm A →
    (RecursorIotaPattern rec major ctor arity).MatchesS
      ((recArgs.foldr (fun (a f : SExpr) => f.app a) (SExpr.const rec recLs)).app
        (ctorArgs.foldr (fun (a f : SExpr) => f.app a)
          (SExpr.const ctor ctorLs))) recLs mcap →
    recLs.length = rule.df.uvars ∧
      SpineWF Gamma (SExpr.mkInst recLs rule.df.type)
        (rule.capturePaths.map mcap) A

/-- (iii) The β-collapse of the rule's applied left tower back onto the
matched redex.  Once the raw capture spine and constructor alignment are
available, this is `SExpr.ruleCollapse` plus a finite `instRev` computation
and one type conversion.  For the parameterized Tree rules, however, that
body comparison rebuilds the constructor at the recursor-derived parameter
and source levels, so the same two alignment facts as (ii) are genuine
inputs to the straightforward proof route. -/
def D2CollapseStep (univs : Nat) : Prop :=
  letI : Params := d2Params univs
  ∀ {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {Gamma : List SExpr} {A majorTerm : SExpr}
    {recLs ctorLs : List SLevel} {recArgs ctorArgs : List SExpr}
    {mcap : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
    (rule : Pattern.IotaRule r),
    D2ContextValid univs Gamma →
    Pattern.IotaTyping Gamma rec ctor recLs ctorLs
      recArgs ctorArgs majorTerm A →
    (RecursorIotaPattern rec major ctor arity).MatchesS
      ((recArgs.foldr (fun (a f : SExpr) => f.app a) (SExpr.const rec recLs)).app
        (ctorArgs.foldr (fun (a f : SExpr) => f.app a)
          (SExpr.const ctor ctorLs))) recLs mcap →
    IsDefEq Gamma
      ((recArgs.foldr (fun (a f : SExpr) => f.app a)
        (SExpr.const rec recLs)).app
        (ctorArgs.foldr (fun (a f : SExpr) => f.app a)
          (SExpr.const ctor ctorLs)))
      ((rule.capturePaths.map mcap).foldl
        (fun (f a : SExpr) => f.app a) (SExpr.mkInst recLs rule.df.lhs)) A

/-- (iv) `Params.Semantic.registered` at the five block rules: the D0-style
lambda-tower descent re-run for this block.

The endpoint self-typings are retained here exactly as they are in
`Params.Semantic.registered`.  The previous parked contract accidentally
dropped them and therefore asked for a strictly stronger theorem than the
semantic bridge consumes; D0's `natRegistered` correctly keeps both inputs.
They provide the native tower typing used by the structural lambda/eta
descent, without assuming the semantic instance being assembled. -/
def D2RegisteredTowerStep (univs : Nat) : Prop :=
  letI : Params := d2Params univs
  ∀ {df : VDefEq} {ls : List SLevel} {Gamma : List SExpr},
    df ∈ TreeGen.generatedRules → ls.length = df.uvars →
    IsDefEqStrong Gamma (SExpr.mkInst ls df.lhs) (SExpr.mkInst ls df.lhs)
      (SExpr.mkInst ls df.type) →
    IsDefEqStrong Gamma (SExpr.mkInst ls df.rhs) (SExpr.mkInst ls df.rhs)
      (SExpr.mkInst ls df.type) →
    IsDefEqStrong Gamma (SExpr.mkInst ls df.lhs) (SExpr.mkInst ls df.rhs)
      (SExpr.mkInst ls df.type)

/-- The result at the bottom of a generated Tree/TreeList rule telescope. -/
def d2RuleResult (constructor : NormalizedBlockCtor) : VExpr :=
  VExpr.appN
    (.bvar (TreeGen.familyCount - 1 - constructor.owner +
      TreeGen.minorCount + TreeGen.ruleFieldCount constructor))
    (TreeGen.ruleIdx constructor ++ [TreeGen.ruleCtorApp constructor])

/-- The genuinely rule-specific leaf of registered-tower closure.

The generic `SExpr.closeTel_strong` theorem now supplies every prefix
application, lambda congruence, and eta contraction.  What remains per rule
is exactly the strongly typed equality at the fully opened generated body:
the recursor/constructor redex versus the registered RHS tower applied to
the canonical binder variables. -/
def D2RegisteredBodyStep (univs : Nat) : Prop :=
  letI : Params := d2Params univs
  ∀ {i : Nat} {constructor : NormalizedBlockCtor}
    (_hentry : TreeGen.flatCtors[i]? = some constructor)
    {ls : List SLevel} {Gamma : List SExpr},
    ls.length = (TreeGen.rule i constructor).uvars →
    IsDefEqStrong Gamma
      (SExpr.mkInst ls (TreeGen.rule i constructor).rhs)
      (SExpr.mkInst ls (TreeGen.rule i constructor).rhs)
      (SExpr.mkInst ls (TreeGen.rule i constructor).type) →
    let As := (TreeGen.ruleBinders constructor).map (SExpr.mkInst ls)
    IsDefEqStrong (As.reverse ++ Gamma)
      (SExpr.mkInst ls (TreeGen.ruleLhsBody constructor))
      (SExpr.applyTelVars As
        (SExpr.mkInst ls (TreeGen.rule i constructor).rhs))
      (SExpr.mkInst ls (d2RuleResult constructor))

/-- Close the five local generated-body leaves into the complete semantic
registered contract.  This is the rule-independent part formerly repeated
by hand in D0. -/
theorem D2RegisteredTowerStep.of_body (univs : Nat)
    (h : D2RegisteredBodyStep univs) : D2RegisteredTowerStep univs := by
  letI : Params := d2Params univs
  intro df ls Gamma hmem hlen _hLhs hRhs
  change df ∈ TreeGen.flatCtors.zipIdx.map
    (fun ic => TreeGen.rule ic.2 ic.1) at hmem
  obtain ⟨⟨constructor, i⟩, hpair, rfl⟩ := List.mem_map.1 hmem
  obtain ⟨-, hentry⟩ := List.mem_zipIdx_getElem? hpair
  rw [Nat.sub_zero] at hentry
  let As : List SExpr :=
    (TreeGen.ruleBinders constructor).map (SExpr.mkInst ls)
  let B : SExpr := SExpr.mkInst ls (d2RuleResult constructor)
  have htype : SExpr.mkInst ls (TreeGen.rule i constructor).type =
      As.foldr .forallE B := by
    rw [TreeGen.rule_type, SExpr.mkInst_forallN]
    rfl
  have hlhs : SExpr.mkInst ls (TreeGen.rule i constructor).lhs =
      SExpr.lamTel As
        (SExpr.mkInst ls (TreeGen.ruleLhsBody constructor)) := by
    rw [TreeGen.rule_lhs, SExpr.mkInst_lamN]
  have hRhs' : IsDefEqStrong Gamma
      (SExpr.mkInst ls (TreeGen.rule i constructor).rhs)
      (SExpr.mkInst ls (TreeGen.rule i constructor).rhs)
      (As.foldr .forallE B) := htype ▸ hRhs
  have hLocal := h hentry hlen hRhs
  have hClosed := SExpr.closeTel_strong
    (fun W H => d2StrongWeak univs W H) hRhs' hLocal
  rw [hlhs, htype]
  exact hClosed

/-- The block half of the D2 semantic bridge, as one named premise.  The
`checked` field is directly `L4L-18A′`-blocked.  The Tree portions of
`captureSpine` and `lhsCollapse` additionally hide canonical constructor
level alignment of the same normalization/injectivity strength; their
remaining finite replay, the Nat cases, and `registeredTower` are
engineering.  The preferred exact bundle supplies those Nat cases
internally. -/
structure D2BlockStep (univs : Nat) : Prop where
  checked : D2TreeCheckedStep univs
  captureSpine : D2CaptureSpineStep univs
  lhsCollapse : D2CollapseStep univs
  registeredTower : D2RegisteredTowerStep univs

/-- The complete `Params.Semantic.iotaSite` for the D2 inventory, assembled
by the generic engine `SExpr.iotaSiteOf` from the parked block data. -/
noncomputable def d2IotaSite (univs : Nat) (h : D2BlockStep univs)
    {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {Gamma : List (@SExpr (d2Params univs))}
    {A majorTerm : @SExpr (d2Params univs)}
    {recLs ctorLs : List (@SLevel (d2Params univs))}
    {recArgs ctorArgs : List (@SExpr (d2Params univs))}
    {mcap : (RecursorIotaPattern rec major ctor arity).Path →
      @SExpr (d2Params univs)}
    (rule : @Pattern.IotaRule (d2Params univs) rec major ctor arity r)
    (captureType : (RecursorIotaPattern rec major ctor arity).Path →
      @SExpr (d2Params univs))
    (captureTyping : @Pattern.CaptureTyping (d2Params univs) Gamma
      (RecursorIotaPattern rec major ctor arity) mcap captureType)
    (hGamma : D2ContextValid univs Gamma)
    (typing : @Pattern.IotaTyping (d2Params univs) Gamma rec ctor recLs ctorLs
      recArgs ctorArgs majorTerm A)
    (matched : @Pattern.MatchesS (d2Params univs)
      (RecursorIotaPattern rec major ctor arity)
      (@SExpr.app (d2Params univs)
        (recArgs.foldr (fun a f => @SExpr.app (d2Params univs) f a)
          (@SExpr.const (d2Params univs) rec recLs))
        (ctorArgs.foldr (fun a f => @SExpr.app (d2Params univs) f a)
          (@SExpr.const (d2Params univs) ctor ctorLs))) recLs mcap) :
    @Pattern.IotaReductionSite (d2Params univs) Gamma rec major ctor
      arity r rule recLs ctorLs recArgs ctorArgs majorTerm A mcap captureType
      captureTyping := by
  letI : Params := d2Params univs
  have hcap := h.captureSpine rule hGamma typing matched
  have hchecked : D2CheckedStep univs :=
    D2CheckedStep.of_tree univs h.checked
  have hck := hchecked rule.pat captureTyping hGamma typing matched
  exact SExpr.iotaSiteOf (d2Replay univs) rule captureTyping hGamma typing
    matched hcap.1 hcap.2 (h.lhsCollapse rule hGamma typing matched)
    hck.choose hck.choose_spec.1 hck.choose_spec.2

/-- `Params.Semantic.registered` for the complete D2 inventory. -/
theorem d2Registered (univs : Nat) (h : D2BlockStep univs)
    {df : VDefEq} {ls : List (@SLevel (d2Params univs))}
    {Gamma : List (@SExpr (d2Params univs))}
    (hreg : d2Env.defeqs df) (hlen : ls.length = df.uvars)
    (hLhs : @IsDefEqStrong (d2Params univs) Gamma
      (@SExpr.mkInst (d2Params univs) ls df.lhs)
      (@SExpr.mkInst (d2Params univs) ls df.lhs)
      (@SExpr.mkInst (d2Params univs) ls df.type))
    (hRhs : @IsDefEqStrong (d2Params univs) Gamma
      (@SExpr.mkInst (d2Params univs) ls df.rhs)
      (@SExpr.mkInst (d2Params univs) ls df.rhs)
      (@SExpr.mkInst (d2Params univs) ls df.type)) :
    @IsDefEqStrong (d2Params univs) Gamma
      (@SExpr.mkInst (d2Params univs) ls df.lhs)
      (@SExpr.mkInst (d2Params univs) ls df.rhs)
      (@SExpr.mkInst (d2Params univs) ls df.type) := by
  rw [d2Env_defeqs_iff] at hreg
  rcases hreg with hnew | hold
  · exact h.registeredTower hnew hlen hLhs hRhs
  · exact d2Registered_old univs hold hlen

/-- The complete D2 bridge, conditional on the block step: the inherited
Nat iota rules, the three inherited definition rules, the block's five
constructor bundles, and the block's five generated iota rules. -/
noncomputable def d2Semantic (univs : Nat) (h : D2BlockStep univs) :
    letI : Params := d2Params univs
    Params.Semantic := by
  letI : Params := d2Params univs
  exact {
  structureEta := by
    intro rule levels Gamma params major hreg
    exact (d2Env_no_structEta rule hreg).elim
  ctor := by
    intro c ci ls Gamma hci hlen cl
    exact d2Ctor univs hci hlen cl
  defn := by
    intro c r hpat
    exact d2Defn univs hpat
  iotaRule := by
    intro rec major ctor arity r hpat
    exact d2IotaRule univs hpat
  iotaSite := by
    intro rec major ctor arity r Gamma A majorTerm recLs ctorLs
      recArgs ctorArgs mcap rule captureType captureTyping hGamma typing
      matched _redexSelf _AType
    exact d2IotaSite univs h rule captureType captureTyping hGamma typing
      matched
  registered := by
    intro df ls Gamma hreg hlen hLhs hRhs
    exact d2Registered univs h hreg hlen hLhs hRhs }

/-- End-to-end D2 endpoint, conditional on the block step and the two
L4L-16C′w leaf inputs: the block-inductive environment supplies every
semantic certificate required by the experimental sort-injectivity
bridge. -/
theorem d2SortInvS (univs : Nat) (h : D2BlockStep univs)
    (piInv : @LRS.PiPathInv (d2Params univs))
    (linkRect : ∀ Γ, @LR.MajorLinkRect (d2Params univs) Γ)
    {Gamma : List VExpr} {u v : VLevel}
    (hGamma : OnCtx Gamma (d2Env.IsType univs))
    (hde : d2Env.IsDefEqU univs Gamma (.sort u) (.sort v)) : u ≈ v := by
  letI : Params := d2Params univs
  letI : Params.Semantic := d2Semantic univs h
  exact VEnv.IsDefEqU.sort_invS piInv linkRect hGamma hde

/-! ## The complete rule registry, disambiguated by right towers

Every site-level case analysis below must recover *which* registered rule a
matched descriptor names.  D1 did this with per-pair `rhs`-inequality
probes; the D2 inventory has ten registered rules, so the pairwise style
would need dozens of probes.  Instead the registry is pinned once: the ten
rules' right towers are pairwise distinct, so a registered defeq is
recovered from its `rhs` alone. -/

/-- The complete defeq inventory of `d2Env`, in registration order: the
block's five generated rules, the three definition rules, and the two
inherited `Nat` rules. -/
def d2AllRules : List VDefEq :=
  TreeGen.generatedRules ++
    [d1MutBVal.toDefEq, d1MutAVal.toDefEq, d0DefVal.toDefEq] ++
    NatGeneration.generatedRules

theorem d2Env_defeqs_mem {df : VDefEq} :
    d2Env.defeqs df ↔ df ∈ d2AllRules := by
  rw [d2Env_defeqs_iff, d1Env_defeqs_iff, d0Env_defeqs_iff,
    natFinalEnv_defeqs_iff]
  simp only [d2AllRules, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, or_assoc]

/-- The ten registered right towers are pairwise distinct. -/
theorem d2AllRules_rhs_nodup : (d2AllRules.map (·.rhs)).Nodup := by
  native_decide

private theorem map_nodup_inj {α β : Type _} {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {a b : α}, a ∈ l → b ∈ l →
      f a = f b → a = b
  | [], _, _, _, ha, _, _ => (List.not_mem_nil ha).elim
  | x :: l, hnodup, a, b, ha, hb, hf => by
    rw [List.map_cons, List.nodup_cons] at hnodup
    cases List.mem_cons.mp ha with
    | inl haeq =>
      cases List.mem_cons.mp hb with
      | inl hbeq => rw [haeq, hbeq]
      | inr hbmem =>
        have hmem : f b ∈ l.map f := List.mem_map_of_mem hbmem
        rw [← hf, haeq] at hmem
        exact absurd hmem hnodup.1
    | inr hamem =>
      cases List.mem_cons.mp hb with
      | inl hbeq =>
        have hmem : f a ∈ l.map f := List.mem_map_of_mem hamem
        rw [hf, hbeq] at hmem
        exact absurd hmem hnodup.1
      | inr hbmem => exact map_nodup_inj hnodup.2 hamem hbmem hf

/-- A registered defeq of `d2Env` is recovered from its right tower. -/
theorem d2Registered_eq_of_rhs {df target : VDefEq}
    (hreg : d2Env.defeqs df) (htarget : target ∈ d2AllRules)
    (hrhs : df.rhs = target.rhs) : df = target :=
  map_nodup_inj d2AllRules_rhs_nodup (d2Env_defeqs_mem.mp hreg) htarget hrhs

/-- A D2 iota descriptor is uniquely determined by its pattern payload.

The payload fixes the registered right tower.  Pairwise distinct right
towers then identify the registered equation, and injectivity of a
fixed-headed `RHS.appN` identifies the ordered capture paths.  This removes
the proof-relevant descriptor choice from every subsequent replay: a caller
may replace an arbitrary `Pattern.IotaRule r` by the canonical descriptor
returned by `d2IotaRule`. -/
theorem d2IotaRule_ext (univs : Nat)
    {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (x y : @Pattern.IotaRule (d2Params univs) rec major ctor arity r) :
    x = y := by
  letI : Params := d2Params univs
  rcases x with ⟨xpat, xdf, xreg, xclosed, xpaths, xtower⟩
  rcases y with ⟨ypat, ydf, yreg, yclosed, ypaths, ytower⟩
  obtain ⟨hrhs, hpaths⟩ := rhsFixedAppN_inj (xtower.symm.trans ytower)
  have hdf : xdf = ydf :=
    d2Registered_eq_of_rhs xreg (d2Env_defeqs_mem.mp yreg) hrhs
  subst ydf
  subst ypaths
  rfl

instance d2IotaRule_subsingleton (univs : Nat)
    {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check} :
    Subsingleton (@Pattern.IotaRule (d2Params univs)
      rec major ctor arity r) :=
  ⟨d2IotaRule_ext univs⟩

/-- Replace an arbitrary descriptor by the public canonical choice for its
own pattern proof. -/
theorem d2IotaRule_eq_canonical (univs : Nat)
    {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (rule : @Pattern.IotaRule (d2Params univs) rec major ctor arity r) :
    rule = d2IotaRule univs (by
      letI : Params := d2Params univs
      exact rule.pat) :=
  d2IotaRule_ext univs _ _

/-- Recover the canonical origin of any D2 iota descriptor.

The result has seven concrete leaves: the left disjunct contains the two
inherited Nat rules, while the right disjunct contains the five entries of
`TreeGen.flatCtors`.  `HEq` in the block branch carries the recovered
recursor, major arity, constructor, argument arity, and payload indices in
one equation, so downstream replay can eliminate it without a registry
cross-product. -/
theorem d2IotaRule_origin (univs : Nat)
    {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (rule : @Pattern.IotaRule (d2Params univs) rec major ctor arity r) :
    (∃ H : NatPat (RecursorIotaPattern rec major ctor arity) r,
      rule = d2NatIotaRule univs H) ∨
    (∃ (i : Nat) (constructor : NormalizedBlockCtor)
        (hentry : TreeGen.flatCtors[i]? = some constructor),
      HEq rule (d2TreeIotaRule univs hentry)) := by
  letI : Params := d2Params univs
  have hpat := rule.pat
  change D2Pat (RecursorIotaPattern rec major ctor arity) r at hpat
  cases hpat with
  | nat H =>
    exact .inl ⟨H, d2IotaRule_ext univs _ _⟩
  | assembled H =>
    rcases assembledPat_cases H with
      ⟨i, c, hentry, hpattern, hr⟩ | ⟨ext, hmem, hpattern⟩
    · change RecursorIotaPattern rec major ctor arity =
        RecursorIotaPattern (TreeGen.ruleRecName c)
          (TreeGen.ruleMajorArity c) c.ctor.raw.name
          (TreeGen.ruleArgArity c) at hpattern
      obtain ⟨rfl, rfl, rfl, rfl⟩ := RecursorIotaPattern.inj hpattern
      obtain rfl : r = _ := eq_of_heq hr
      exact .inr ⟨i, c, hentry,
        heq_of_eq (d2IotaRule_ext univs _ _)⟩
    · exfalso
      simp only [d2Exts, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl <;>
        exact absurd hpattern
          (by simp [RecursorIotaPattern, d0DefExt, d1MutAExt, d1MutBExt])

/-- Seven-case elimination for D2 iota descriptors.  All proof-relevant
descriptor fields have already been canonicalized by
`d2IotaRule_origin`; callers prove only the Nat-family and block-entry
cases. -/
theorem d2IotaRule_elim (univs : Nat)
    (P : ∀ {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
      {r : (RecursorIotaPattern rec major ctor arity).RHS ×
        (RecursorIotaPattern rec major ctor arity).Check},
      @Pattern.IotaRule (d2Params univs) rec major ctor arity r → Prop)
    (hnat : ∀ {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
      {r : (RecursorIotaPattern rec major ctor arity).RHS ×
        (RecursorIotaPattern rec major ctor arity).Check}
      (H : NatPat (RecursorIotaPattern rec major ctor arity) r),
      P (d2NatIotaRule univs H))
    (htree : ∀ {i : Nat} {constructor : NormalizedBlockCtor}
      (hentry : TreeGen.flatCtors[i]? = some constructor),
      P (d2TreeIotaRule univs hentry))
    {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (rule : @Pattern.IotaRule (d2Params univs) rec major ctor arity r) :
    P rule := by
  letI : Params := d2Params univs
  have hpat := rule.pat
  change D2Pat (RecursorIotaPattern rec major ctor arity) r at hpat
  cases hpat with
  | nat H =>
    rw [d2IotaRule_ext univs rule (d2NatIotaRule univs H)]
    exact hnat H
  | assembled H =>
    rcases assembledPat_cases H with
      ⟨i, c, hentry, hpattern, hr⟩ | ⟨ext, hmem, hpattern⟩
    · change RecursorIotaPattern rec major ctor arity =
        RecursorIotaPattern (TreeGen.ruleRecName c)
          (TreeGen.ruleMajorArity c) c.ctor.raw.name
          (TreeGen.ruleArgArity c) at hpattern
      obtain ⟨rfl, rfl, rfl, rfl⟩ := RecursorIotaPattern.inj hpattern
      obtain rfl : r = _ := eq_of_heq hr
      rw [d2IotaRule_ext univs rule (d2TreeIotaRule univs hentry)]
      exact htree hentry
    · exfalso
      simp only [d2Exts, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl <;>
        exact absurd hpattern
          (by simp [RecursorIotaPattern, d0DefExt, d1MutAExt, d1MutBExt])

/-- Fully concrete seven-entry elimination.  Unlike `d2IotaRule_elim`, the
Nat branch is indexed by its generated-rule lookup too, so every descriptor
field reduces to literal `NatGeneration`/`TreeGen` data. -/
theorem d2IotaRule_entry_elim (univs : Nat)
    (P : ∀ {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
      {r : (RecursorIotaPattern rec major ctor arity).RHS ×
        (RecursorIotaPattern rec major ctor arity).Check},
      @Pattern.IotaRule (d2Params univs) rec major ctor arity r → Prop)
    (hnat : ∀ {i : Nat} {constructor : NormalizedBlockCtor}
      (hentry : NatGeneration.flatCtors[i]? = some constructor),
      P (d2NatEntryIotaRule univs hentry))
    (htree : ∀ {i : Nat} {constructor : NormalizedBlockCtor}
      (hentry : TreeGen.flatCtors[i]? = some constructor),
      P (d2TreeIotaRule univs hentry))
    {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (rule : @Pattern.IotaRule (d2Params univs) rec major ctor arity r) :
    P rule := by
  letI : Params := d2Params univs
  have hpat := rule.pat
  change D2Pat (RecursorIotaPattern rec major ctor arity) r at hpat
  cases hpat with
  | nat H =>
    obtain ⟨i, c, hentry, hpattern, -⟩ :=
      VInductDecl.BlockGenerationChecked.IotaPat.recover NatGeneration H
    change RecursorIotaPattern rec major ctor arity =
        RecursorIotaPattern (NatGeneration.ruleRecName c)
          (NatGeneration.ruleMajorArity c) c.ctor.raw.name
          (NatGeneration.ruleArgArity c) at hpattern
    obtain ⟨rfl, rfl, rfl, rfl⟩ := RecursorIotaPattern.inj hpattern
    let rgen :=
      (NatGeneration.ruleRHS natRuleClosure hentry,
        NatGeneration.ruleCheck natRuleClosure
          (List.mem_of_getElem? hentry))
    have Hgen : NatPat
        (RecursorIotaPattern (NatGeneration.ruleRecName c)
          (NatGeneration.ruleMajorArity c) c.ctor.raw.name
          (NatGeneration.ruleArgArity c)) rgen := .mk hentry
    have hr : r ≍ rgen :=
      (VInductDecl.BlockGenerationChecked.IotaPat.pat_uniq NatGeneration
        H Hgen .refl (Pattern.inter_self _)).2.2
    obtain rfl : r = rgen := eq_of_heq hr
    rw [d2IotaRule_ext univs rule (d2NatEntryIotaRule univs hentry)]
    exact hnat hentry
  | assembled H =>
    rcases assembledPat_cases H with
      ⟨i, c, hentry, hpattern, hr⟩ | ⟨ext, hmem, hpattern⟩
    · change RecursorIotaPattern rec major ctor arity =
        RecursorIotaPattern (TreeGen.ruleRecName c)
          (TreeGen.ruleMajorArity c) c.ctor.raw.name
          (TreeGen.ruleArgArity c) at hpattern
      obtain ⟨rfl, rfl, rfl, rfl⟩ := RecursorIotaPattern.inj hpattern
      obtain rfl : r = _ := eq_of_heq hr
      rw [d2IotaRule_ext univs rule (d2TreeIotaRule univs hentry)]
      exact htree hentry
    · exfalso
      simp only [d2Exts, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl | rfl <;>
        exact absurd hpattern
          (by simp [RecursorIotaPattern, d0DefExt, d1MutAExt, d1MutBExt])

/-- A concrete inherited Nat entry retains the generated declaration and its
strict recursive-field certificate after transport into D2. -/
theorem d2NatEntryIotaStructuralDescent (univs : Nat) {i : Nat}
    {constructor : NormalizedBlockCtor}
    (hentry : NatGeneration.flatCtors[i]? = some constructor) :
    @Pattern.IotaRule.StructuralDescent (d2Params univs)
      (NatGeneration.ruleRecName constructor)
      (NatGeneration.ruleMajorArity constructor) constructor.ctor.raw.name
      (NatGeneration.ruleArgArity constructor)
      (NatGeneration.ruleRHS natRuleClosure hentry,
        NatGeneration.ruleCheck natRuleClosure
          (List.mem_of_getElem? hentry))
      (d2NatEntryIotaRule univs hentry) := by
  letI : Params := d2Params univs
  exact ⟨{
    source := InductiveFixtures.natDecl
    generation := NatGeneration
    ruleIndex := i
    constructor := constructor
    entry := hentry
    rule_eq := rfl
    recursive_lt := natRule_recursive_lt hentry }⟩

/-- A concrete Tree/TreeList entry is certified directly by the block
generation proof used to register its equation. -/
theorem d2TreeIotaStructuralDescent (univs : Nat) {i : Nat}
    {constructor : NormalizedBlockCtor}
    (hentry : TreeGen.flatCtors[i]? = some constructor) :
    @Pattern.IotaRule.StructuralDescent (d2Params univs)
      (TreeGen.ruleRecName constructor)
      (TreeGen.ruleMajorArity constructor) constructor.ctor.raw.name
      (TreeGen.ruleArgArity constructor)
      (TreeGen.ruleRHS treeRuleClosure hentry,
        TreeGen.ruleCheck treeRuleClosure (List.mem_of_getElem? hentry))
      (d2TreeIotaRule univs hentry) := by
  letI : Params := d2Params univs
  exact ⟨{
    source := treeDecl
    generation := TreeGen
    ruleIndex := i
    constructor := constructor
    entry := hentry
    rule_eq := rfl
    recursive_lt := treeRule_recursive_lt hentry }⟩

/-- Every D2 iota rule can be selected with a generated origin whose recursive
calls point to strict constructor-field positions.  The concrete-entry
eliminator covers both inherited Nat rules and the live mutual block. -/
theorem d2IotaStructuralDescent (univs : Nat)
    {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (H : (d2Params univs).Pat
      (RecursorIotaPattern rec major ctor arity) r) :
    ∃ rule : @Pattern.IotaRule (d2Params univs) rec major ctor arity r,
      @Pattern.IotaRule.StructuralDescent (d2Params univs)
        rec major ctor arity r rule := by
  let rule := d2IotaRule univs H
  let P : ∀ {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
      {r : (RecursorIotaPattern rec major ctor arity).RHS ×
        (RecursorIotaPattern rec major ctor arity).Check},
      @Pattern.IotaRule (d2Params univs) rec major ctor arity r → Prop :=
    fun {rec} {major} {ctor} {arity} {r} selected =>
      @Pattern.IotaRule.StructuralDescent (d2Params univs)
        rec major ctor arity r selected
  refine ⟨rule, d2IotaRule_entry_elim univs P ?_ ?_ rule⟩
  · intro i constructor hentry
    exact d2NatEntryIotaStructuralDescent univs hentry
  · intro i constructor hentry
    exact d2TreeIotaStructuralDescent univs hentry

/-- The full Nat + mutual Tree/TreeList fixture inhabits the classified
normalization fragment.  `d2IotaStructuralDescent` covers all seven generated
entries, including recursion under a Pi, while `d2DeltaRank` covers the
inherited zero-arity definitions. -/
theorem d2Classified (univs : Nat)
    [semantic : @Params.Semantic (d2Params univs)] :
    letI : Params := d2Params univs
    letI : Params.DeltaRank := d2DeltaRank univs
    Params.Classified := by
  letI : Params := d2Params univs
  letI : Params.Semantic := semantic
  letI : Params.DeltaRank := d2DeltaRank univs
  exact {
    iotaDescent := d2IotaStructuralDescent univs
    argumentNonProp := Params.patternArgumentNonProp }

/-- The recursor levels at every D2 iota site have the arity stored by the
selected generated equation.  This field is not per-rule replay volume: it
comes from the typed recursor head and the generated rule's `rule_uvars`
identity. -/
theorem d2IotaRule_levelsLength (univs : Nat)
    {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {Gamma : List (@SExpr (d2Params univs))} {A majorTerm : @SExpr (d2Params univs)}
    {recLs ctorLs : List (@SLevel (d2Params univs))}
    {recArgs ctorArgs : List (@SExpr (d2Params univs))}
    (rule : @Pattern.IotaRule (d2Params univs) rec major ctor arity r)
    (typing : @Pattern.IotaTyping (d2Params univs) Gamma rec ctor recLs
      ctorLs recArgs ctorArgs majorTerm A) :
    letI : Params := d2Params univs
    recLs.length = rule.df.uvars := by
  letI : Params := d2Params univs
  let P : ∀ {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
      {r : (RecursorIotaPattern rec major ctor arity).RHS ×
        (RecursorIotaPattern rec major ctor arity).Check},
      @Pattern.IotaRule (d2Params univs) rec major ctor arity r → Prop :=
    fun {rec} {_major} {ctor} {_arity} {_r} selected =>
      ∀ {Gamma : List SExpr} {A majorTerm : SExpr}
        {recLs ctorLs : List SLevel} {recArgs ctorArgs : List SExpr},
        Pattern.IotaTyping Gamma rec ctor recLs ctorLs
          recArgs ctorArgs majorTerm A →
        recLs.length = selected.df.uvars
  have hP : P rule := by
    apply d2IotaRule_entry_elim univs P
    · intro i constructor hentry Gamma A majorTerm recLs ctorLs recArgs
        ctorArgs typing
      have hi : i = 0 ∨ i = 1 := by
        obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hentry
        have : NatGeneration.flatCtors.length = 2 := rfl
        omega
      rcases hi with rfl | rfl
      all_goals
        first
        | have hc := Option.some.inj
            (probeNatFlatCtorZero_lookup.symm.trans hentry)
        | have hc := Option.some.inj
            (probeNatFlatCtorSucc_lookup.symm.trans hentry)
        subst constructor
        have hlen := typing.recHead.const_left_levelsLength
          (d1Env_le_d2Env.constants d1NatRecEnvLookup)
        change recLs.length = 1 at hlen
        change recLs.length = (NatGeneration.rule _ _).uvars
        change recLs.length = 1
        exact hlen
    · intro i constructor hentry Gamma A majorTerm recLs ctorLs recArgs
        ctorArgs typing
      have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
        obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hentry
        have : TreeGen.flatCtors.length = 5 := rfl
        omega
      rcases hi with rfl | rfl | rfl | rfl | rfl
      all_goals
        first
        | have hc := Option.some.inj
            ((show TreeGen.flatCtors[0]? = some TreeGen.flatCtors[0] from rfl).symm.trans
              hentry)
        | have hc := Option.some.inj
            ((show TreeGen.flatCtors[1]? = some TreeGen.flatCtors[1] from rfl).symm.trans
              hentry)
        | have hc := Option.some.inj
            ((show TreeGen.flatCtors[2]? = some TreeGen.flatCtors[2] from rfl).symm.trans
              hentry)
        | have hc := Option.some.inj
            ((show TreeGen.flatCtors[3]? = some TreeGen.flatCtors[3] from rfl).symm.trans
              hentry)
        | have hc := Option.some.inj
            ((show TreeGen.flatCtors[4]? = some TreeGen.flatCtors[4] from rfl).symm.trans
              hentry)
        subst constructor
      case inl | inr.inl | inr.inr.inl =>
        have hlen :=
          typing.recHead.const_left_levelsLength d2Env_treeRec_lookup
        change recLs.length = 2 at hlen
        change recLs.length = (TreeGen.rule _ _).uvars
        change recLs.length = 2
        exact hlen
      case inr.inr.inr.inl | inr.inr.inr.inr =>
        have hlen :=
          typing.recHead.const_left_levelsLength d2Env_treeListRec_lookup
        change recLs.length = 2 at hlen
        change recLs.length = (TreeGen.rule _ _).uvars
        change recLs.length = 2
        exact hlen
  exact hP typing

/-! ### Inherited Nat replay

The two Nat rules have no parameter or source-level alignment problem.  Their
three common recursor arguments can therefore be replayed in any D2 context
directly from `Pattern.IotaTyping`; the zero rule stops there and the
successor rule appends its one constructor field. -/

/-- The major-premise tail after the motive and two Nat minors. -/
def d2NatRecTailV : VExpr :=
  VExpr.forallE (VExpr.const ``Nat [])
    ((VExpr.bvar 3).app (VExpr.bvar 0))

theorem d2NatRecTypePrefixV_eq :
    probeNatRecTypeV =
      VExpr.forallN probeNatRuleBindersV d2NatRecTailV := by
  rfl

theorem d2NatZeroRuleTypePrefixV_eq :
    (NatGeneration.rule 0 NatGeneration.flatCtors[0]).type =
      VExpr.forallN probeNatRuleBindersV probeNatZeroRuleResultV := by
  rw [probeNatZeroRuleTypeV_eq]
  rfl

theorem d2NatSuccRuleTypePrefixV_eq :
    (NatGeneration.rule 1 NatGeneration.flatCtors[1]).type =
      VExpr.forallN probeNatRuleBindersV
        (VExpr.forallE (VExpr.const ``Nat []) probeNatSuccRuleResultV) := by
  rw [probeNatSuccRuleTypeV_eq]
  rfl

/-- Replay the motive and two minor premises from a typed `Nat.rec` spine as
the common prefix of a rule whose remaining result is `newResult`. -/
theorem d2NatRuleCommonRawSpine (univs : Nat)
    (level : @SLevel (d2Params univs)) (newResult : VExpr)
    {Gamma : List (@SExpr (d2Params univs))}
    {A majorTerm : @SExpr (d2Params univs)}
    {ctor : Name} {ctorLs : List (@SLevel (d2Params univs))}
    {recArgs ctorArgs : List (@SExpr (d2Params univs))}
    (hGamma : D2ContextValid univs Gamma)
    (typing : @Pattern.IotaTyping (d2Params univs) Gamma ``Nat.rec
      ctor [level] ctorLs recArgs ctorArgs majorTerm A)
    (hlen : recArgs.length = 3) :
    letI : Params := d2Params univs
    SpineWF Gamma
      (SExpr.mkInst [level]
        (VExpr.forallN probeNatRuleBindersV newResult))
      recArgs.reverse
      (SExpr.mk
        ((newResult.instL [level.reify]).instRev
          (recArgs.reverse.map SExpr.reify))) := by
  letI : Params := d2Params univs
  let vls : List VLevel := [level.reify]
  have hvls : ∀ l ∈ vls, l.WF univs := by
    intro l hl
    have : l = level.reify := List.mem_singleton.mp hl
    subst l
    exact SLevel.reify_wf level
  have hrec : IsDefEq Gamma (.const ``Nat.rec [level])
      (.const ``Nat.rec [level])
      (SExpr.mkInst [level]
        (VInductDecl.recConst 0 ``Nat 0 InductiveFixtures.natType).type) :=
    .const (d1Env_le_d2Env.constants d1NatRecEnvLookup) rfl
  rw [probeNatRecTypeV_eq, d2NatRecTypePrefixV_eq] at hrec
  have hHead := typeUniq (d2Replay univs) hGamma hrec typing.recHead
  have hlevel : (VExpr.forallN
      (probeNatRuleBindersV.map (VExpr.instL vls))
      (d2NatRecTailV.instL vls)).LevelWF univs := by
    have H : ((VExpr.forallN probeNatRuleBindersV d2NatRecTailV).instL vls).LevelWF
        univs := VExpr.LevelWF.instL hvls
    rwa [VExpr.instL_forallN] at H
  have holdShape : SExpr.mk
      (VExpr.forallN (probeNatRuleBindersV.map (VExpr.instL vls))
        (d2NatRecTailV.instL vls)) =
      SExpr.mkInst [level]
        (VExpr.forallN probeNatRuleBindersV d2NatRecTailV) := by
    calc
      _ = SExpr.mk ((VExpr.forallN probeNatRuleBindersV
          d2NatRecTailV).instL vls) := by
        rw [VExpr.instL_forallN]
      _ = _ := by
        simpa only [vls, List.map_cons, List.map_nil] using
          (@SExpr.mk_instL_map_reify (d2Params univs)
            (VExpr.forallN probeNatRuleBindersV d2NatRecTailV) [level])
  have hprefix := spinePrefixForallN (d2Replay univs) hGamma
    (n := 3)
    (binders := probeNatRuleBindersV.map (VExpr.instL vls))
    (oldResult := d2NatRecTailV.instL vls)
    (newResult := newResult.instL vls)
    (args := recArgs.reverse) (suffix := [majorTerm])
    (by simp [probeNatRuleBindersV]) (by simp [hlen]) hlevel
      (holdShape ▸ hHead)
      typing.recSpine
  have hnewShape : SExpr.mk
      (VExpr.forallN (probeNatRuleBindersV.map (VExpr.instL vls))
        (newResult.instL vls)) =
      SExpr.mkInst [level]
        (VExpr.forallN probeNatRuleBindersV newResult) := by
    calc
      _ = SExpr.mk ((VExpr.forallN probeNatRuleBindersV
          newResult).instL vls) := by
        rw [VExpr.instL_forallN]
      _ = _ := by
        simpa only [vls, List.map_cons, List.map_nil] using
          (@SExpr.mk_instL_map_reify (d2Params univs)
            (VExpr.forallN probeNatRuleBindersV newResult) [level])
  rw [hnewShape] at hprefix
  simpa only [vls] using hprefix

/-- The inherited zero-rule match exposes exactly its three recursor
captures, now in the ambient D2 syntax. -/
theorem d2NatZeroCaptureValues (univs : Nat)
    {recLs ctorLs : List (@SLevel (d2Params univs))}
    {recArgs ctorArgs : List (@SExpr (d2Params univs))}
    {mcap : (RecursorIotaPattern ``Nat.rec 3 ``Nat.zero 0).Path →
      @SExpr (d2Params univs)}
    (H : @Pattern.MatchesS (d2Params univs)
      (RecursorIotaPattern ``Nat.rec 3 ``Nat.zero 0)
      (@SExpr.app (d2Params univs)
        (recArgs.foldr (fun a f => @SExpr.app (d2Params univs) f a)
          (@SExpr.const (d2Params univs) ``Nat.rec recLs))
        (ctorArgs.foldr (fun a f => @SExpr.app (d2Params univs) f a)
          (@SExpr.const (d2Params univs) ``Nat.zero ctorLs))) recLs mcap) :
    recArgs.length = 3 ∧ ctorArgs = [] ∧
      (natCapturePaths NatGeneration.flatCtors[0]).map mcap =
        recArgs.reverse := by
  letI : Params := d2Params univs
  cases H with
  | @app _ _ _ recCap _ _ _ ctorCap hrec hctor =>
    obtain ⟨-, hrecLen, hrecValues⟩ := ParamsD0.matchesS_varN_foldr hrec
    obtain ⟨-, hctorLen, -⟩ := ParamsD0.matchesS_varN_foldr hctor
    have hctorArgs : ctorArgs = [] := List.length_eq_zero_iff.mp hctorLen
    subst ctorArgs
    refine ⟨hrecLen, rfl, ?_⟩
    rw [natZeroCapturePaths]
    change
      ((Pattern.varNPaths (.const ``Nat.rec) 3).map Sum.inl).map
          (Sum.elim recCap ctorCap) = recArgs.reverse
    simpa [List.map_map, Function.comp_def] using hrecValues

/-- The inherited successor-rule match exposes the same three recursor
captures followed by its predecessor field. -/
theorem d2NatSuccCaptureValues (univs : Nat)
    {recLs ctorLs : List (@SLevel (d2Params univs))}
    {recArgs ctorArgs : List (@SExpr (d2Params univs))}
    {mcap : (RecursorIotaPattern ``Nat.rec 3 ``Nat.succ 1).Path →
      @SExpr (d2Params univs)}
    (H : @Pattern.MatchesS (d2Params univs)
      (RecursorIotaPattern ``Nat.rec 3 ``Nat.succ 1)
      (@SExpr.app (d2Params univs)
        (recArgs.foldr (fun a f => @SExpr.app (d2Params univs) f a)
          (@SExpr.const (d2Params univs) ``Nat.rec recLs))
        (ctorArgs.foldr (fun a f => @SExpr.app (d2Params univs) f a)
          (@SExpr.const (d2Params univs) ``Nat.succ ctorLs))) recLs mcap) :
    recArgs.length = 3 ∧ ctorArgs.length = 1 ∧
      (natCapturePaths NatGeneration.flatCtors[1]).map mcap =
        recArgs.reverse ++ ctorArgs.reverse := by
  letI : Params := d2Params univs
  cases H with
  | @app _ _ _ recCap _ _ _ ctorCap hrec hctor =>
    obtain ⟨-, hrecLen, hrecValues⟩ := ParamsD0.matchesS_varN_foldr hrec
    obtain ⟨-, hctorLen, hctorValues⟩ :=
      ParamsD0.matchesS_varN_foldr hctor
    refine ⟨hrecLen, hctorLen, ?_⟩
    rw [natSuccCapturePaths]
    change
      (((Pattern.varNPaths (.const ``Nat.rec) 3).map Sum.inl ++
          (Pattern.varNPaths (.const ``Nat.succ) 1).map Sum.inr).map
        (Sum.elim recCap ctorCap)) = recArgs.reverse ++ ctorArgs.reverse
    simp [List.map_append, List.map_map, Function.comp_def,
      hrecValues, hctorValues]

/-- Both site obligations for the inherited Nat zero rule, replayed in the
actual D2 context. -/
theorem d2NatZeroRuleReplay (univs : Nat)
    {Gamma : List (@SExpr (d2Params univs))}
    {A majorTerm : @SExpr (d2Params univs)}
    {recLs ctorLs : List (@SLevel (d2Params univs))}
    {recArgs ctorArgs : List (@SExpr (d2Params univs))}
    {mcap : (RecursorIotaPattern ``Nat.rec 3 ``Nat.zero 0).Path →
      @SExpr (d2Params univs)}
    (hGamma : D2ContextValid univs Gamma)
    (typing : @Pattern.IotaTyping (d2Params univs) Gamma ``Nat.rec
      ``Nat.zero recLs ctorLs recArgs ctorArgs majorTerm A)
    (matched : @Pattern.MatchesS (d2Params univs)
      (RecursorIotaPattern ``Nat.rec 3 ``Nat.zero 0)
      (@SExpr.app (d2Params univs)
        (recArgs.foldr (fun a f => @SExpr.app (d2Params univs) f a)
          (@SExpr.const (d2Params univs) ``Nat.rec recLs))
        (ctorArgs.foldr (fun a f => @SExpr.app (d2Params univs) f a)
          (@SExpr.const (d2Params univs) ``Nat.zero ctorLs))) recLs mcap) :
    letI : Params := d2Params univs
    SpineWF Gamma
      (SExpr.mkInst recLs
        (NatGeneration.rule 0 NatGeneration.flatCtors[0]).type)
      ((natCapturePaths NatGeneration.flatCtors[0]).map mcap) A ∧
    IsDefEq Gamma
      ((recArgs.foldr (fun (a f : SExpr) => f.app a)
        (SExpr.const ``Nat.rec recLs)).app
        (ctorArgs.foldr (fun (a f : SExpr) => f.app a)
          (SExpr.const ``Nat.zero ctorLs)))
      (((natCapturePaths NatGeneration.flatCtors[0]).map mcap).foldl
        (fun (f a : SExpr) => f.app a)
        (SExpr.mkInst recLs
          (NatGeneration.rule 0 NatGeneration.flatCtors[0]).lhs)) A := by
  letI : Params := d2Params univs
  have hrecLen := typing.recHead.const_left_levelsLength
    (d1Env_le_d2Env.constants d1NatRecEnvLookup)
  change recLs.length = 1 at hrecLen
  obtain ⟨level, rfl⟩ := List.length_eq_one_iff.mp hrecLen
  have hctorLen := typing.ctorHead.const_left_levelsLength
    (d1Env_le_d2Env.constants d1NatZeroEnvLookup)
  change ctorLs.length = 0 at hctorLen
  have hctorLs : ctorLs = [] := List.length_eq_zero_iff.mp hctorLen
  subst ctorLs
  obtain ⟨hrecArgsLen, hctorArgs, hcaptures⟩ :=
    d2NatZeroCaptureValues univs matched
  subst ctorArgs
  have hrecArgs : ∃ x y z, recArgs = [x, y, z] :=
    ⟨recArgs[0], recArgs[1], recArgs[2],
      List.eq_getElem_of_length_eq_three recArgs hrecArgsLen⟩
  obtain ⟨minorSucc, minorZero, motive, rfl⟩ := hrecArgs
  have hraw := d2NatRuleCommonRawSpine univs level
    probeNatZeroRuleResultV hGamma typing rfl
  rw [← d2NatZeroRuleTypePrefixV_eq] at hraw
  let vls : List VLevel := [level.reify]
  have hbodyV :
      (probeNatZeroRuleLhsBodyV.instL vls).instRev
          [motive.reify, minorZero.reify, minorSucc.reify] =
        ((((VExpr.const ``Nat.rec [level.reify]).app motive.reify).app
          minorZero.reify).app minorSucc.reify).app
          (VExpr.const ``Nat.zero []) := by
    simp [probeNatZeroRuleLhsBodyV, vls, VExpr.instRev, VExpr.instL,
      VExpr.inst, VExpr.instVar,
      VExpr.liftN_succ, VExpr.liftN_zero, probeReifyInstVParamZero,
      VExpr.inst_lift]
    simpa only [VExpr.liftN_zero] using
      probeVCancelTwoLifts motive.reify minorZero.reify minorSucc.reify
  have hbody : SExpr.mk
      ((probeNatZeroRuleLhsBodyV.instL vls).instRev
        ([motive, minorZero, minorSucc].map SExpr.reify)) =
      (((((SExpr.const ``Nat.rec [level]).app motive).app minorZero).app
        minorSucc).app (SExpr.const ``Nat.zero [])) := by
    simpa only [vls, SExpr.mk, List.map_cons, List.map_nil,
      SLevel.mk_reify, SExpr.mk_reify] using congrArg SExpr.mk hbodyV
  have hredex := Pattern.IotaTyping.redexSelf
    (d2Replay univs) hGamma typing
  have hreg : d2Env.defeqs
      (NatGeneration.rule 0 NatGeneration.flatCtors[0]) :=
    d1Env_le_d2Env.defeqs <| d0Env_le_d1Env.defeqs <|
      natFinalEnv_le_d0Env.defeqs <|
        natRule_registered
          (show NatGeneration.flatCtors[0]? =
            some NatGeneration.flatCtors[0] from rfl)
  have hreplay := ruleReplayOfRawSpine (d2Replay univs) hGamma
    hreg
    (by simpa [probeNatZeroRuleLhsV] using probeNatZeroRuleLhsV_eq)
    d2NatZeroRuleTypePrefixV_eq rfl
    (by simp [probeNatRuleBindersV]) hraw hbody hredex
  simpa only [List.reverse_cons, List.reverse_nil, List.append_nil,
    List.foldr, hcaptures] using hreplay

/-- Both site obligations for the inherited Nat successor rule, including
the one constructor-field suffix. -/
theorem d2NatSuccRuleReplay (univs : Nat)
    {Gamma : List (@SExpr (d2Params univs))}
    {A majorTerm : @SExpr (d2Params univs)}
    {recLs ctorLs : List (@SLevel (d2Params univs))}
    {recArgs ctorArgs : List (@SExpr (d2Params univs))}
    {mcap : (RecursorIotaPattern ``Nat.rec 3 ``Nat.succ 1).Path →
      @SExpr (d2Params univs)}
    (hGamma : D2ContextValid univs Gamma)
    (typing : @Pattern.IotaTyping (d2Params univs) Gamma ``Nat.rec
      ``Nat.succ recLs ctorLs recArgs ctorArgs majorTerm A)
    (matched : @Pattern.MatchesS (d2Params univs)
      (RecursorIotaPattern ``Nat.rec 3 ``Nat.succ 1)
      (@SExpr.app (d2Params univs)
        (recArgs.foldr (fun a f => @SExpr.app (d2Params univs) f a)
          (@SExpr.const (d2Params univs) ``Nat.rec recLs))
        (ctorArgs.foldr (fun a f => @SExpr.app (d2Params univs) f a)
          (@SExpr.const (d2Params univs) ``Nat.succ ctorLs))) recLs mcap) :
    letI : Params := d2Params univs
    SpineWF Gamma
      (SExpr.mkInst recLs
        (NatGeneration.rule 1 NatGeneration.flatCtors[1]).type)
      ((natCapturePaths NatGeneration.flatCtors[1]).map mcap) A ∧
    IsDefEq Gamma
      ((recArgs.foldr (fun (a f : SExpr) => f.app a)
        (SExpr.const ``Nat.rec recLs)).app
        (ctorArgs.foldr (fun (a f : SExpr) => f.app a)
          (SExpr.const ``Nat.succ ctorLs)))
      (((natCapturePaths NatGeneration.flatCtors[1]).map mcap).foldl
        (fun (f a : SExpr) => f.app a)
        (SExpr.mkInst recLs
          (NatGeneration.rule 1 NatGeneration.flatCtors[1]).lhs)) A := by
  letI : Params := d2Params univs
  have hrecLen := typing.recHead.const_left_levelsLength
    (d1Env_le_d2Env.constants d1NatRecEnvLookup)
  change recLs.length = 1 at hrecLen
  obtain ⟨level, rfl⟩ := List.length_eq_one_iff.mp hrecLen
  have hctorLen := typing.ctorHead.const_left_levelsLength
    (d1Env_le_d2Env.constants d1NatSuccEnvLookup)
  change ctorLs.length = 0 at hctorLen
  have hctorLs : ctorLs = [] := List.length_eq_zero_iff.mp hctorLen
  subst ctorLs
  obtain ⟨hrecArgsLen, hctorArgsLen, hcaptures⟩ :=
    d2NatSuccCaptureValues univs matched
  obtain ⟨pred, rfl⟩ := List.length_eq_one_iff.mp hctorArgsLen
  have hrecArgs : ∃ x y z, recArgs = [x, y, z] :=
    ⟨recArgs[0], recArgs[1], recArgs[2],
      List.eq_getElem_of_length_eq_three recArgs hrecArgsLen⟩
  obtain ⟨minorSucc, minorZero, motive, rfl⟩ := hrecArgs
  have hcommon := d2NatRuleCommonRawSpine univs level
    (VExpr.forallE (VExpr.const ``Nat []) probeNatSuccRuleResultV)
    hGamma typing rfl
  rw [← d2NatSuccRuleTypePrefixV_eq] at hcommon
  have hctorCanonical : IsDefEq Gamma
      (.const ``Nat.succ []) (.const ``Nat.succ [])
      (SExpr.mkInst [] InductiveFixtures.natType.ctors[1].type) :=
    .const (d1Env_le_d2Env.constants d1NatSuccEnvLookup) rfl
  rw [probeNatSuccCtorTypeV_eq] at hctorCanonical
  have hctorCanonical' : IsDefEq Gamma
      (.const ``Nat.succ []) (.const ``Nat.succ [])
      (.forallE (.const ``Nat []) (.const ``Nat [])) := by
    simpa [SExpr.mkInst] using hctorCanonical
  have hctorType := typeUniq (d2Replay univs) hGamma
    hctorCanonical' typing.ctorHead
  let predView := spineConsView (d2Replay univs) hGamma
    hctorType typing.ctorSpine
  have hpred : IsDefEq Gamma pred pred (.const ``Nat []) := by
    simpa using predView.argumentExpected
  have hraw := hcommon.append (.cons hpred .nil)
  let vls : List VLevel := [level.reify]
  have hbodyV :
      (probeNatSuccRuleLhsBodyV.instL vls).instRev
          [motive.reify, minorZero.reify, minorSucc.reify, pred.reify] =
        ((((VExpr.const ``Nat.rec [level.reify]).app motive.reify).app
          minorZero.reify).app minorSucc.reify).app
          ((VExpr.const ``Nat.succ []).app pred.reify) := by
    simp [probeNatSuccRuleLhsBodyV, vls, VExpr.instRev, VExpr.instL,
      VExpr.inst, VExpr.instVar,
      VExpr.liftN_succ, VExpr.liftN_zero, probeReifyInstVParamZero,
      VExpr.inst_lift]
    constructor
    · simpa only [VExpr.liftN_zero] using
        probeVCancelThreeLifts motive.reify minorZero.reify
          minorSucc.reify pred.reify
    · simpa only [VExpr.liftN_zero] using
        probeVCancelTwoLifts minorZero.reify minorSucc.reify pred.reify
  have hbody : SExpr.mk
      ((probeNatSuccRuleLhsBodyV.instL vls).instRev
        ([motive, minorZero, minorSucc, pred].map SExpr.reify)) =
      (((((SExpr.const ``Nat.rec [level]).app motive).app minorZero).app
        minorSucc).app ((SExpr.const ``Nat.succ []).app pred)) := by
    simpa only [vls, SExpr.mk, List.map_cons, List.map_nil,
      SLevel.mk_reify, SExpr.mk_reify] using congrArg SExpr.mk hbodyV
  have hredex := Pattern.IotaTyping.redexSelf
    (d2Replay univs) hGamma typing
  have hreg : d2Env.defeqs
      (NatGeneration.rule 1 NatGeneration.flatCtors[1]) :=
    d1Env_le_d2Env.defeqs <| d0Env_le_d1Env.defeqs <|
      natFinalEnv_le_d0Env.defeqs <|
        natRule_registered
          (show NatGeneration.flatCtors[1]? =
            some NatGeneration.flatCtors[1] from rfl)
  have hreplay := ruleReplayOfRawSpine (d2Replay univs) hGamma hreg
    (by simpa [probeNatSuccRuleLhsV] using probeNatSuccRuleLhsV_eq)
    (by simpa [probeNatSuccRuleTypeV] using probeNatSuccRuleTypeV_eq)
    rfl (by simp [probeNatSuccRuleBindersV, probeNatRuleBindersV])
    hraw hbody hredex
  simpa [hcaptures] using hreplay

/-- The actual per-rule capture obligation after removing the universe-arity
field proved by `d2IotaRule_levelsLength`. -/
def D2CaptureSpineCoreStep (univs : Nat) : Prop :=
  letI : Params := d2Params univs
  ∀ {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {Gamma : List SExpr} {A majorTerm : SExpr}
    {recLs ctorLs : List SLevel} {recArgs ctorArgs : List SExpr}
    {mcap : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
    (rule : Pattern.IotaRule r),
    D2ContextValid univs Gamma →
    Pattern.IotaTyping Gamma rec ctor recLs ctorLs
      recArgs ctorArgs majorTerm A →
    (RecursorIotaPattern rec major ctor arity).MatchesS
      ((recArgs.foldr (fun (a f : SExpr) => f.app a) (SExpr.const rec recLs)).app
        (ctorArgs.foldr (fun (a f : SExpr) => f.app a)
          (SExpr.const ctor ctorLs))) recLs mcap →
    SpineWF Gamma (SExpr.mkInst recLs rule.df.type)
      (rule.capturePaths.map mcap) A

/-- Restore the legacy pair-shaped capture contract from its genuine spine
content and the unconditional level-arity theorem. -/
theorem D2CaptureSpineStep.of_core (univs : Nat)
    (h : D2CaptureSpineCoreStep univs) : D2CaptureSpineStep univs := by
  letI : Params := d2Params univs
  intro rec major ctor arity r Gamma A majorTerm recLs ctorLs recArgs ctorArgs
    mcap rule hGamma typing matched
  exact ⟨d2IotaRule_levelsLength univs rule typing,
    h rule hGamma typing matched⟩

/-- The genuinely remaining site replay, restricted to the five new
Tree/TreeList entries.  Both outputs share one concrete site because the
field telescope and collapsed body consume the same parameter/source-level
alignment. -/
def D2TreeReplayStep (univs : Nat) : Prop :=
  letI : Params := d2Params univs
  ∀ {i : Nat} {constructor : NormalizedBlockCtor}
    (_hentry : TreeGen.flatCtors[i]? = some constructor)
    {Gamma : List SExpr} {A majorTerm : SExpr}
    {recLs ctorLs : List SLevel} {recArgs ctorArgs : List SExpr}
    {mcap : ((TreeGen.rulePattern constructor).toPattern).Path → SExpr},
    D2ContextValid univs Gamma →
    Pattern.IotaTyping Gamma (TreeGen.ruleRecName constructor)
      constructor.ctor.raw.name recLs ctorLs recArgs ctorArgs majorTerm A →
    ((TreeGen.rulePattern constructor).toPattern).MatchesS
      ((recArgs.foldr (fun (a f : SExpr) => f.app a)
        (SExpr.const (TreeGen.ruleRecName constructor) recLs)).app
        (ctorArgs.foldr (fun (a f : SExpr) => f.app a)
          (SExpr.const constructor.ctor.raw.name ctorLs))) recLs mcap →
    SpineWF Gamma
        (SExpr.mkInst recLs (TreeGen.rule i constructor).type)
        ((treeCapturePaths constructor).map mcap) A ∧
      IsDefEq Gamma
        ((recArgs.foldr (fun (a f : SExpr) => f.app a)
          (SExpr.const (TreeGen.ruleRecName constructor) recLs)).app
          (ctorArgs.foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const constructor.ctor.raw.name ctorLs)))
        (((treeCapturePaths constructor).map mcap).foldl
          (fun (f a : SExpr) => f.app a)
          (SExpr.mkInst recLs (TreeGen.rule i constructor).lhs)) A

/-- Fill the complete seven-rule capture contract from the two proved Nat
replays and a five-rule Tree replay premise. -/
theorem D2CaptureSpineCoreStep.of_treeReplay (univs : Nat)
    (h : D2TreeReplayStep univs) : D2CaptureSpineCoreStep univs := by
  letI : Params := d2Params univs
  let P : ∀ {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
      {r : (RecursorIotaPattern rec major ctor arity).RHS ×
        (RecursorIotaPattern rec major ctor arity).Check},
      @Pattern.IotaRule (d2Params univs) rec major ctor arity r → Prop :=
    fun {rec} {major} {ctor} {arity} {_r} selected =>
      ∀ {Gamma : List SExpr} {A majorTerm : SExpr}
        {recLs ctorLs : List SLevel} {recArgs ctorArgs : List SExpr}
        {mcap : (RecursorIotaPattern rec major ctor arity).Path → SExpr},
        D2ContextValid univs Gamma →
        Pattern.IotaTyping Gamma rec ctor recLs ctorLs
          recArgs ctorArgs majorTerm A →
        (RecursorIotaPattern rec major ctor arity).MatchesS
          ((recArgs.foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const rec recLs)).app
            (ctorArgs.foldr (fun (a f : SExpr) => f.app a)
              (SExpr.const ctor ctorLs))) recLs mcap →
        SpineWF Gamma (SExpr.mkInst recLs selected.df.type)
          (selected.capturePaths.map mcap) A
  intro rec major ctor arity r Gamma A majorTerm recLs ctorLs recArgs ctorArgs
    mcap rule
  have hP : P rule := by
    apply d2IotaRule_entry_elim univs P
    · intro i constructor hentry Gamma A majorTerm recLs ctorLs recArgs
        ctorArgs mcap hGamma typing matched
      have hi : i = 0 ∨ i = 1 := by
        obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hentry
        have : NatGeneration.flatCtors.length = 2 := rfl
        omega
      rcases hi with rfl | rfl
      · have hc := Option.some.inj
          (probeNatFlatCtorZero_lookup.symm.trans hentry)
        subst constructor
        change @SpineWF (d2Params univs) Gamma
          (@SExpr.mkInst (d2Params univs) recLs
            (NatGeneration.rule 0 NatGeneration.flatCtors[0]).type)
          ((natCapturePaths NatGeneration.flatCtors[0]).map mcap) A
        exact (d2NatZeroRuleReplay univs hGamma typing matched).1
      · have hc := Option.some.inj
          (probeNatFlatCtorSucc_lookup.symm.trans hentry)
        subst constructor
        change @SpineWF (d2Params univs) Gamma
          (@SExpr.mkInst (d2Params univs) recLs
            (NatGeneration.rule 1 NatGeneration.flatCtors[1]).type)
          ((natCapturePaths NatGeneration.flatCtors[1]).map mcap) A
        exact (d2NatSuccRuleReplay univs hGamma typing matched).1
    · intro i constructor hentry Gamma A majorTerm recLs ctorLs recArgs
        ctorArgs mcap hGamma typing matched
      change @SpineWF (d2Params univs) Gamma
        (@SExpr.mkInst (d2Params univs) recLs
          (TreeGen.rule i constructor).type)
        ((treeCapturePaths constructor).map mcap) A
      exact (h hentry hGamma typing matched).1
  exact hP

/-- Fill the complete seven-rule collapse contract from the same Tree replay
premise and the two proved Nat replays. -/
theorem D2CollapseStep.of_treeReplay (univs : Nat)
    (h : D2TreeReplayStep univs) : D2CollapseStep univs := by
  letI : Params := d2Params univs
  let P : ∀ {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
      {r : (RecursorIotaPattern rec major ctor arity).RHS ×
        (RecursorIotaPattern rec major ctor arity).Check},
      @Pattern.IotaRule (d2Params univs) rec major ctor arity r → Prop :=
    fun {rec} {major} {ctor} {arity} {_r} selected =>
      ∀ {Gamma : List SExpr} {A majorTerm : SExpr}
        {recLs ctorLs : List SLevel} {recArgs ctorArgs : List SExpr}
        {mcap : (RecursorIotaPattern rec major ctor arity).Path → SExpr},
        D2ContextValid univs Gamma →
        Pattern.IotaTyping Gamma rec ctor recLs ctorLs
          recArgs ctorArgs majorTerm A →
        (RecursorIotaPattern rec major ctor arity).MatchesS
          ((recArgs.foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const rec recLs)).app
            (ctorArgs.foldr (fun (a f : SExpr) => f.app a)
              (SExpr.const ctor ctorLs))) recLs mcap →
        IsDefEq Gamma
          ((recArgs.foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const rec recLs)).app
            (ctorArgs.foldr (fun (a f : SExpr) => f.app a)
              (SExpr.const ctor ctorLs)))
          ((selected.capturePaths.map mcap).foldl
            (fun (f a : SExpr) => f.app a)
            (SExpr.mkInst recLs selected.df.lhs)) A
  intro rec major ctor arity r Gamma A majorTerm recLs ctorLs recArgs ctorArgs
    mcap rule
  have hP : P rule := by
    apply d2IotaRule_entry_elim univs P
    · intro i constructor hentry Gamma A majorTerm recLs ctorLs recArgs
        ctorArgs mcap hGamma typing matched
      have hi : i = 0 ∨ i = 1 := by
        obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hentry
        have : NatGeneration.flatCtors.length = 2 := rfl
        omega
      rcases hi with rfl | rfl
      · have hc := Option.some.inj
          (probeNatFlatCtorZero_lookup.symm.trans hentry)
        subst constructor
        change @IsDefEq (d2Params univs) Gamma
          ((recArgs.foldr (fun (a f : @SExpr (d2Params univs)) => f.app a)
            (@SExpr.const (d2Params univs) ``Nat.rec recLs)).app
            (ctorArgs.foldr
              (fun (a f : @SExpr (d2Params univs)) => f.app a)
              (@SExpr.const (d2Params univs) ``Nat.zero ctorLs)))
          (((natCapturePaths NatGeneration.flatCtors[0]).map mcap).foldl
            (fun (f a : @SExpr (d2Params univs)) => f.app a)
            (@SExpr.mkInst (d2Params univs) recLs
              (NatGeneration.rule 0 NatGeneration.flatCtors[0]).lhs)) A
        exact (d2NatZeroRuleReplay univs hGamma typing matched).2
      · have hc := Option.some.inj
          (probeNatFlatCtorSucc_lookup.symm.trans hentry)
        subst constructor
        change @IsDefEq (d2Params univs) Gamma
          ((recArgs.foldr (fun (a f : @SExpr (d2Params univs)) => f.app a)
            (@SExpr.const (d2Params univs) ``Nat.rec recLs)).app
            (ctorArgs.foldr
              (fun (a f : @SExpr (d2Params univs)) => f.app a)
              (@SExpr.const (d2Params univs) ``Nat.succ ctorLs)))
          (((natCapturePaths NatGeneration.flatCtors[1]).map mcap).foldl
            (fun (f a : @SExpr (d2Params univs)) => f.app a)
            (@SExpr.mkInst (d2Params univs) recLs
              (NatGeneration.rule 1 NatGeneration.flatCtors[1]).lhs)) A
        exact (d2NatSuccRuleReplay univs hGamma typing matched).2
    · intro i constructor hentry Gamma A majorTerm recLs ctorLs recArgs
        ctorArgs mcap hGamma typing matched
      change @IsDefEq (d2Params univs) Gamma
        ((recArgs.foldr (fun (a f : @SExpr (d2Params univs)) => f.app a)
          (@SExpr.const (d2Params univs)
            (TreeGen.ruleRecName constructor) recLs)).app
          (ctorArgs.foldr
            (fun (a f : @SExpr (d2Params univs)) => f.app a)
            (@SExpr.const (d2Params univs)
              constructor.ctor.raw.name ctorLs)))
        (((treeCapturePaths constructor).map mcap).foldl
          (fun (f a : @SExpr (d2Params univs)) => f.app a)
          (@SExpr.mkInst (d2Params univs) recLs
            (TreeGen.rule i constructor).lhs)) A
      exact (h hentry hGamma typing matched).2
  exact hP

/-- The exact remaining D2 bridge contract.

Compared with the internal `D2BlockStep`, this removes the obligations now
proved by the fixture itself: inherited Nat checks, recursor level arity, and
both inherited Nat site replays.  Its three fields are therefore the
five-rule 18A′ check, one paired five-rule Tree replay, and the five generated
strong body leaves.  The latter is pure finite work and
`D2RegisteredTowerStep.of_body` closes it into the registered lambda towers
generically.  The paired Tree replay still subsumes the shared
parameter/source-level alignment boundary named by
`D2TreeLevelAlignmentStep`; they are not pure volume as currently packaged. -/
structure D2BlockStepExact (univs : Nat) : Prop where
  checked : D2TreeCheckedStep univs
  replay : D2TreeReplayStep univs
  registeredBody : D2RegisteredBodyStep univs

/-- Recover the old full-inventory capture contract from the smaller exact
bundle.  Kept as a named projection-compatible theorem for downstream code. -/
theorem D2BlockStepExact.captureSpine (h : D2BlockStepExact univs) :
    D2CaptureSpineCoreStep univs :=
  D2CaptureSpineCoreStep.of_treeReplay univs h.replay

/-- Recover the old full-inventory collapse contract from the smaller exact
bundle. -/
theorem D2BlockStepExact.lhsCollapse (h : D2BlockStepExact univs) :
    D2CollapseStep univs :=
  D2CollapseStep.of_treeReplay univs h.replay

theorem D2BlockStepExact.toBlockStep (h : D2BlockStepExact univs) :
    D2BlockStep univs where
  checked := h.checked
  captureSpine := D2CaptureSpineStep.of_core univs h.captureSpine
  lhsCollapse := h.lhsCollapse
  registeredTower := D2RegisteredTowerStep.of_body univs h.registeredBody

/-- Preferred complete semantic bridge, conditional only on the exact
residual contract. -/
noncomputable def d2SemanticExact (univs : Nat) (h : D2BlockStepExact univs) :
    letI : Params := d2Params univs
    Params.Semantic :=
  d2Semantic univs h.toBlockStep

/-- Preferred D2 endpoint with inherited Nat checks and all level-arity
bookkeeping discharged internally.  Conditional on the exact residual
contract and the two L4L-16C′w leaf inputs. -/
theorem d2SortInvSExact (univs : Nat) (h : D2BlockStepExact univs)
    (piInv : @LRS.PiPathInv (d2Params univs))
    (linkRect : ∀ Γ, @LR.MajorLinkRect (d2Params univs) Γ)
    {Gamma : List VExpr} {u v : VLevel}
    (hGamma : OnCtx Gamma (d2Env.IsType univs))
    (hde : d2Env.IsDefEqU univs Gamma (.sort u) (.sort v)) : u ≈ v :=
  d2SortInvS univs h.toBlockStep piInv linkRect hGamma hde

/-! ## Endpoints and pins -/

/-- The block-extended environment is well formed, ordered, and registers
exactly the block's generated rules over D1's. -/
theorem d2Env_live :
    d2Env.WF ∧ d2Env.Ordered ∧
      ∀ df, d2Env.defeqs df ↔
        df ∈ TreeGen.generatedRules ∨ d1Env.defeqs df :=
  ⟨d2Env_wf, d2Env_ordered, d2Env_defeqs_iff⟩

/-! ## What remains for the D2 `Params.Semantic` bridge

**Corrected record.**  Four of the six `Params.Semantic` fields are now
delivered unconditionally: `structureEta` (`d2StructureEtaSound`),
`iotaRule` (`d2IotaRule`), `ctor` (`d2Ctor`, including all five block
constructor bundles) and `defn` (`d2Defn`).  `registered` is delivered for
every inherited rule (`d2Registered_old`).  What remains is the *block*
half of `iotaSite` and `registered`, packaged by the single preferred premise
`D2BlockStepExact`; `d2SemanticExact`/`d2SortInvSExact` are conditional on
exactly that premise and nothing else.  Descriptor uniqueness and
`d2IotaRule_entry_elim` reduce arbitrary proof-relevant descriptors to the
seven literal generated entries.  The inherited Nat check branches, both Nat
site replays, and the recursor level-arity field are proved outright and do
not appear in the preferred premise.

The earlier record here called the residual "pure volume".  That is
**wrong** for both non-registered fields of the current exact bundle:

* `D2TreeCheckedStep` is *not* volume.  `TreeGen.ruleCheck` folds one `.defeq`
  per `treeDecl.nparams`, and Tree has one parameter, so discharging it at
  a matched redex means deriving `p ≡ a` from a stuck `I p ≡ I a`.  That is
  injectivity of a stuck inductive-type application — `L4L-18A′` strength,
  the same wall recorded for the quotient rule at
  `SExprParamsD1.lean:2735`.  The semantic side cannot supply it either:
  the logical relation realizes `indTy` arguments at `.bot`
  (`ShapeLogRel.lean:9244`), so it retains no argument information at all.
  D0/D1 never met this wall because `Nat` has no parameters and no indices,
  which is why both discharge `checked` by `simp`.

* `D2TreeReplayStep` pairs the remaining capture and collapse results and
  still mixes finite replay with the same research boundary.  The generated
  field telescope and collapsed lhs
  rebuild constructors using the recursor-derived parameter and canonical
  `TreeGen.sourceLevels`; `Pattern.IotaTyping` types the concrete constructor
  at independent `ctorLs` and its own parameter.  The checked parameter
  equality plus `D2TreeLevelAlignmentStep` are therefore required before the
  Tree suffix/body can be connected.  Theory's `pat_wf` makes this explicit
  by requiring constructor heads at
  `sourceLevels.map (VLevel.inst recLs)`.

* The finite remainder is now much smaller because the eight common recursor
  arguments, conversion-aware collapse, and redex self-typing have been
  factored into the generic engine
  `Lean4Lean/Experimental/SExprGenericReplay.lean`
  (`SExpr.spinePrefixForallN`, `SExpr.ruleReplayOfRawSpine_defeq`,
  `Pattern.IotaTyping.redexSelf`, `SExpr.iotaSiteOf`) and the
  syntax transport into
  `Lean4Lean/Experimental/SExprTransport.lean`.  Notably `ruleCollapse` —
  the whole reify/`instL_lamN`/`lamN_wf`/`retarget`/`appN_lamN`/`mkS`
  chain that D0 and D1 inline once per rule — is proved once, generically,
  and `closeTel_strong` supplies every registered-rule prefix,
  lambda congruence, and eta contraction from one fully opened body equality.
  The concrete five registered bodies are discharged separately.  The raw
  `ruleCollapse` and `closeTel_strong` kernels are `sorryAx`-free; the
  conversion-aware wrappers inherit the ladder's existing 16C′ `sorryAx`.
  The two inherited Nat rules are fully replayed in D2 and are no longer
  premises of `D2BlockStepExact`.

The old note also claimed the D1→D2 transport functor was missing; it is
now landed (`d1StrongToD2` and the generic transport it rests on), which is
what unblocked `ctor`/`defn`.

The two forcing observations below are unchanged in content: every
generated rule of the live block is simultaneously a `Pat` member and a
registered defeq of `d2Env`, which is what obliges `iotaSite`/`registered`
at it, hence what `D2BlockStepExact` must cover. -/

/-- Forcing observation 1: every generated rule of the live block is a
pattern member of the D2 registry.  This is what makes `D2TreeCheckedStep`
unavoidable: the pattern's `Check` payload is `TreeGen.ruleCheck`, whose
parameter obligation is 18A′-gated. -/
theorem d2Pat_block_rule {i : Nat} {c : NormalizedBlockCtor}
    (hentry : TreeGen.flatCtors[i]? = some c) :
    D2Pat ((TreeGen.rulePattern c).toPattern)
      (TreeGen.ruleRHS treeRuleClosure hentry,
        TreeGen.ruleCheck treeRuleClosure (List.mem_of_getElem? hentry)) :=
  .assembled (.rule (.mk hentry))

/-- Forcing observation 2: the same rule is a registered defeq of the live
environment, so `Params.Semantic.registered` is obliged at it. -/
theorem d2Registered_obligation {i : Nat} {c : NormalizedBlockCtor}
    (hentry : TreeGen.flatCtors[i]? = some c) :
    d2Env.defeqs (TreeGen.rule i c) ∧
      D2Pat ((TreeGen.rulePattern c).toPattern)
        (TreeGen.ruleRHS treeRuleClosure hentry,
          TreeGen.ruleCheck treeRuleClosure (List.mem_of_getElem? hentry)) :=
  ⟨treeRule_registered hentry, d2Pat_block_rule hentry⟩

/-! ## Axiom closures

The pattern layer — including all four union-level non-overlap laws, this
file's first live consumption of `Theory/Typing/InductivePatternEnv.lean` —
stays on the standard logical baseline with kernel `decide` only.  The
environment layer inherits D1's named concrete `native_decide` freshness
observations and adds three of its own; it carries no `sorryAx`, so the live
block-inductive environment is admission-free. -/

/-- info: 'Lean4Lean.SExpr.ParamsD2.d2ExtSeparation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms d2ExtSeparation

/-- info: 'Lean4Lean.SExpr.ParamsD2.d2Pat_uniq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms d2Pat_uniq

/-- info: 'Lean4Lean.SExpr.ParamsD2.d2Pat_app_l_uniq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms d2Pat_app_l_uniq

/-- info: 'Lean4Lean.SExpr.ParamsD2.d2Pat_app_uniq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms d2Pat_app_uniq

/--
info: 'Lean4Lean.SExpr.ParamsD2.d2Env_wf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 d0Def_fresh._native.native_decide.ax_1_1,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 d1MutA_fresh._native.native_decide.ax_1_1,
 d1MutA_name_ne_mutB._native.native_decide.ax_1_1,
 d1MutB_fresh._native.native_decide.ax_1_1,
 d2Env_isSome._native.native_decide.ax_1_1,
 treeList_fresh._native.native_decide.ax_1_1,
 tree_fresh._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d2Env_wf

/--
info: 'Lean4Lean.SExpr.ParamsD2.d2Params' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 d0Def_fresh._native.native_decide.ax_1_1,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 d0Classify_d1MutA_none._native.native_decide.ax_1_1,
 d0Classify_d1MutB_none._native.native_decide.ax_1_1,
 d1MutA_fresh._native.native_decide.ax_1_1,
 d1MutA_name_ne_mutB._native.native_decide.ax_1_1,
 d1MutB_fresh._native.native_decide.ax_1_1,
 d2Env_isSome._native.native_decide.ax_1_1,
 treeList_fresh._native.native_decide.ax_1_1,
 tree_fresh._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d2Params

/--
info: 'Lean4Lean.SExpr.ParamsD2.d2StructureEtaSound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 d0Def_fresh._native.native_decide.ax_1_1,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 d0Classify_d1MutA_none._native.native_decide.ax_1_1,
 d0Classify_d1MutB_none._native.native_decide.ax_1_1,
 d1MutA_fresh._native.native_decide.ax_1_1,
 d1MutA_name_ne_mutB._native.native_decide.ax_1_1,
 d1MutB_fresh._native.native_decide.ax_1_1,
 d2Env_isSome._native.native_decide.ax_1_1,
 treeList_fresh._native.native_decide.ax_1_1,
 tree_fresh._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d2StructureEtaSound

/--
info: 'Lean4Lean.SExpr.ParamsD2.d2IotaRule' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 d0Def_fresh._native.native_decide.ax_1_1,
 d0Def_name_ne_natRec._native.native_decide.ax_1_1,
 d0Def_name_ne_natSucc._native.native_decide.ax_1_1,
 d0Def_name_ne_natZero._native.native_decide.ax_1_1,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 d0Classify_d1MutA_none._native.native_decide.ax_1_1,
 d0Classify_d1MutB_none._native.native_decide.ax_1_1,
 d1MutA_fresh._native.native_decide.ax_1_1,
 d1MutA_name_ne_d0Def._native.native_decide.ax_1_1,
 d1MutA_name_ne_mutB._native.native_decide.ax_1_1,
 d1MutA_name_ne_natRec._native.native_decide.ax_1_1,
 d1MutA_name_ne_natSucc._native.native_decide.ax_1_1,
 d1MutA_name_ne_natZero._native.native_decide.ax_1_1,
 d1MutB_fresh._native.native_decide.ax_1_1,
 d1MutB_name_ne_d0Def._native.native_decide.ax_1_1,
 d1MutB_name_ne_natRec._native.native_decide.ax_1_1,
 d1MutB_name_ne_natSucc._native.native_decide.ax_1_1,
 d1MutB_name_ne_natZero._native.native_decide.ax_1_1,
 d2Env_isSome._native.native_decide.ax_1_1,
 treeList_fresh._native.native_decide.ax_1_1,
 tree_fresh._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d2IotaRule

/--
info: 'Lean4Lean.SExpr.ParamsD2.d2Registered_obligation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 d2Env_isSome._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d2Registered_obligation

/-! ### New pins: the semantic layer landed by this slice

`d2Ctor` and `d2Defn` are unconditional.  `d2Semantic`/`d2SortInvS` and
their preferred exact-contract wrappers are conditional on the corresponding
D2 block premise and inherit the ladder's existing `sorryAx` through
`VEnv.IsDefEq.uniq` (the 16C′ leaf that `SExprParamsD1.lean:2654` already
carries); they introduce no new admission of their own.  The descriptor
uniqueness and level-arity mechanics added with the exact contract are
`sorryAx`-free. -/

/--
info: 'Lean4Lean.SExpr.ParamsD2.d2Ctor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 d0Def_fresh._native.native_decide.ax_1_1,
 d0Def_name_ne_natRec._native.native_decide.ax_1_1,
 d0Def_name_ne_natSucc._native.native_decide.ax_1_1,
 d0Def_name_ne_natZero._native.native_decide.ax_1_1,
 natClassify_d0Def_none._native.native_decide.ax_1_1,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 d0Classify_d1MutA_none._native.native_decide.ax_1_1,
 d0Classify_d1MutB_none._native.native_decide.ax_1_1,
 d1MutA_fresh._native.native_decide.ax_1_1,
 d1MutA_name_ne_d0Def._native.native_decide.ax_1_1,
 d1MutA_name_ne_mutB._native.native_decide.ax_1_1,
 d1MutA_name_ne_natRec._native.native_decide.ax_1_1,
 d1MutA_name_ne_natSucc._native.native_decide.ax_1_1,
 d1MutA_name_ne_natZero._native.native_decide.ax_1_1,
 d1MutB_fresh._native.native_decide.ax_1_1,
 d1MutB_name_ne_d0Def._native.native_decide.ax_1_1,
 d1MutB_name_ne_natRec._native.native_decide.ax_1_1,
 d1MutB_name_ne_natSucc._native.native_decide.ax_1_1,
 d1MutB_name_ne_natZero._native.native_decide.ax_1_1,
 d1Classify_tree._native.native_decide.ax_1_1,
 d1Classify_treeBranch._native.native_decide.ax_1_1,
 d1Classify_treeLeaf._native.native_decide.ax_1_1,
 d1Classify_treeList._native.native_decide.ax_1_1,
 d1Classify_treeListCons._native.native_decide.ax_1_1,
 d1Classify_treeListNil._native.native_decide.ax_1_1,
 d1Classify_treeListRec._native.native_decide.ax_1_1,
 d1Classify_treeNode._native.native_decide.ax_1_1,
 d1Classify_treeRec._native.native_decide.ax_1_1,
 d2Env_isSome._native.native_decide.ax_1_1,
 treeBranch_fresh._native.native_decide.ax_1_1,
 treeLeaf_fresh._native.native_decide.ax_1_1,
 treeListCons_fresh._native.native_decide.ax_1_1,
 treeListNil_fresh._native.native_decide.ax_1_1,
 treeListRec_fresh._native.native_decide.ax_1_1,
 treeList_fresh._native.native_decide.ax_1_1,
 treeNode_fresh._native.native_decide.ax_1_1,
 treeRec_fresh._native.native_decide.ax_1_1,
 tree_fresh._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d2Ctor

/--
info: 'Lean4Lean.SExpr.ParamsD2.d2Defn' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 d0Def_fresh._native.native_decide.ax_1_1,
 d0Def_name_ne_natRec._native.native_decide.ax_1_1,
 d0Def_name_ne_natSucc._native.native_decide.ax_1_1,
 d0Def_name_ne_natZero._native.native_decide.ax_1_1,
 natClassify_d0Def_none._native.native_decide.ax_1_1,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 d0Classify_d1MutA_none._native.native_decide.ax_1_1,
 d0Classify_d1MutB_none._native.native_decide.ax_1_1,
 d1MutA_fresh._native.native_decide.ax_1_1,
 d1MutA_name_ne_d0Def._native.native_decide.ax_1_1,
 d1MutA_name_ne_mutB._native.native_decide.ax_1_1,
 d1MutA_name_ne_natRec._native.native_decide.ax_1_1,
 d1MutA_name_ne_natSucc._native.native_decide.ax_1_1,
 d1MutA_name_ne_natZero._native.native_decide.ax_1_1,
 d1MutB_fresh._native.native_decide.ax_1_1,
 d1MutB_name_ne_d0Def._native.native_decide.ax_1_1,
 d1MutB_name_ne_natRec._native.native_decide.ax_1_1,
 d1MutB_name_ne_natSucc._native.native_decide.ax_1_1,
 d1MutB_name_ne_natZero._native.native_decide.ax_1_1,
 d2Env_isSome._native.native_decide.ax_1_1,
 treeBranch_fresh._native.native_decide.ax_1_1,
 treeLeaf_fresh._native.native_decide.ax_1_1,
 treeListCons_fresh._native.native_decide.ax_1_1,
 treeListNil_fresh._native.native_decide.ax_1_1,
 treeListRec_fresh._native.native_decide.ax_1_1,
 treeList_fresh._native.native_decide.ax_1_1,
 treeNode_fresh._native.native_decide.ax_1_1,
 treeRec_fresh._native.native_decide.ax_1_1,
 tree_fresh._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d2Defn

/--
info: 'Lean4Lean.SExpr.ParamsD2.d2Semantic' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 d0Def_fresh._native.native_decide.ax_1_1,
 d0Def_name_ne_natRec._native.native_decide.ax_1_1,
 d0Def_name_ne_natSucc._native.native_decide.ax_1_1,
 d0Def_name_ne_natZero._native.native_decide.ax_1_1,
 natClassify_d0Def_none._native.native_decide.ax_1_1,
 natRule_rhs_ne_d0Def._native.native_decide.ax_1_2,
 natRule_rhs_ne_d0Def._native.native_decide.ax_1_3,
 probeNatGeneratedRuleSucc_lookup._native.native_decide.ax_1_1,
 probeNatGeneratedRuleZero_lookup._native.native_decide.ax_1_1,
 probeNatRecTypeV_eq._native.native_decide.ax_1_1,
 probeNatRuleRhs_ne._native.native_decide.ax_1_1,
 probeNatSuccCtorName._native.native_decide.ax_1_1,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatSuccRuleLhsV_eq._native.native_decide.ax_1_1,
 probeNatSuccRuleRecName._native.native_decide.ax_1_1,
 probeNatSuccRuleTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 probeNatZeroCtorName._native.native_decide.ax_1_1,
 probeNatZeroRuleLhsV_eq._native.native_decide.ax_1_1,
 probeNatZeroRuleRecName._native.native_decide.ax_1_1,
 probeNatZeroRuleTypeV_eq._native.native_decide.ax_1_1,
 d0Classify_d1MutA_none._native.native_decide.ax_1_1,
 d0Classify_d1MutB_none._native.native_decide.ax_1_1,
 d1MutA_fresh._native.native_decide.ax_1_1,
 d1MutA_name_ne_d0Def._native.native_decide.ax_1_1,
 d1MutA_name_ne_mutB._native.native_decide.ax_1_1,
 d1MutA_name_ne_natRec._native.native_decide.ax_1_1,
 d1MutA_name_ne_natSucc._native.native_decide.ax_1_1,
 d1MutA_name_ne_natZero._native.native_decide.ax_1_1,
 d1MutB_fresh._native.native_decide.ax_1_1,
 d1MutB_name_ne_d0Def._native.native_decide.ax_1_1,
 d1MutB_name_ne_natRec._native.native_decide.ax_1_1,
 d1MutB_name_ne_natSucc._native.native_decide.ax_1_1,
 d1MutB_name_ne_natZero._native.native_decide.ax_1_1,
 natRule_rhs_ne_d1MutA._native.native_decide.ax_1_2,
 natRule_rhs_ne_d1MutA._native.native_decide.ax_1_3,
 natRule_rhs_ne_d1MutB._native.native_decide.ax_1_2,
 natRule_rhs_ne_d1MutB._native.native_decide.ax_1_3,
 d1Classify_tree._native.native_decide.ax_1_1,
 d1Classify_treeBranch._native.native_decide.ax_1_1,
 d1Classify_treeLeaf._native.native_decide.ax_1_1,
 d1Classify_treeList._native.native_decide.ax_1_1,
 d1Classify_treeListCons._native.native_decide.ax_1_1,
 d1Classify_treeListNil._native.native_decide.ax_1_1,
 d1Classify_treeListRec._native.native_decide.ax_1_1,
 d1Classify_treeNode._native.native_decide.ax_1_1,
 d1Classify_treeRec._native.native_decide.ax_1_1,
 d2Env_isSome._native.native_decide.ax_1_1,
 treeBranch_fresh._native.native_decide.ax_1_1,
 treeLeaf_fresh._native.native_decide.ax_1_1,
 treeListCons_fresh._native.native_decide.ax_1_1,
 treeListNil_fresh._native.native_decide.ax_1_1,
 treeListRec_fresh._native.native_decide.ax_1_1,
 treeList_fresh._native.native_decide.ax_1_1,
 treeNode_fresh._native.native_decide.ax_1_1,
 treeRec_fresh._native.native_decide.ax_1_1,
 tree_fresh._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d2Semantic

/--
info: 'Lean4Lean.SExpr.ParamsD2.d2SortInvS' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 d0Def_fresh._native.native_decide.ax_1_1,
 d0Def_name_ne_natRec._native.native_decide.ax_1_1,
 d0Def_name_ne_natSucc._native.native_decide.ax_1_1,
 d0Def_name_ne_natZero._native.native_decide.ax_1_1,
 natClassify_d0Def_none._native.native_decide.ax_1_1,
 natRule_rhs_ne_d0Def._native.native_decide.ax_1_2,
 natRule_rhs_ne_d0Def._native.native_decide.ax_1_3,
 probeNatGeneratedRuleSucc_lookup._native.native_decide.ax_1_1,
 probeNatGeneratedRuleZero_lookup._native.native_decide.ax_1_1,
 probeNatRecTypeV_eq._native.native_decide.ax_1_1,
 probeNatRuleRhs_ne._native.native_decide.ax_1_1,
 probeNatSuccCtorName._native.native_decide.ax_1_1,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatSuccRuleLhsV_eq._native.native_decide.ax_1_1,
 probeNatSuccRuleRecName._native.native_decide.ax_1_1,
 probeNatSuccRuleTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 probeNatZeroCtorName._native.native_decide.ax_1_1,
 probeNatZeroRuleLhsV_eq._native.native_decide.ax_1_1,
 probeNatZeroRuleRecName._native.native_decide.ax_1_1,
 probeNatZeroRuleTypeV_eq._native.native_decide.ax_1_1,
 d0Classify_d1MutA_none._native.native_decide.ax_1_1,
 d0Classify_d1MutB_none._native.native_decide.ax_1_1,
 d1MutA_fresh._native.native_decide.ax_1_1,
 d1MutA_name_ne_d0Def._native.native_decide.ax_1_1,
 d1MutA_name_ne_mutB._native.native_decide.ax_1_1,
 d1MutA_name_ne_natRec._native.native_decide.ax_1_1,
 d1MutA_name_ne_natSucc._native.native_decide.ax_1_1,
 d1MutA_name_ne_natZero._native.native_decide.ax_1_1,
 d1MutB_fresh._native.native_decide.ax_1_1,
 d1MutB_name_ne_d0Def._native.native_decide.ax_1_1,
 d1MutB_name_ne_natRec._native.native_decide.ax_1_1,
 d1MutB_name_ne_natSucc._native.native_decide.ax_1_1,
 d1MutB_name_ne_natZero._native.native_decide.ax_1_1,
 natRule_rhs_ne_d1MutA._native.native_decide.ax_1_2,
 natRule_rhs_ne_d1MutA._native.native_decide.ax_1_3,
 natRule_rhs_ne_d1MutB._native.native_decide.ax_1_2,
 natRule_rhs_ne_d1MutB._native.native_decide.ax_1_3,
 d1Classify_tree._native.native_decide.ax_1_1,
 d1Classify_treeBranch._native.native_decide.ax_1_1,
 d1Classify_treeLeaf._native.native_decide.ax_1_1,
 d1Classify_treeList._native.native_decide.ax_1_1,
 d1Classify_treeListCons._native.native_decide.ax_1_1,
 d1Classify_treeListNil._native.native_decide.ax_1_1,
 d1Classify_treeListRec._native.native_decide.ax_1_1,
 d1Classify_treeNode._native.native_decide.ax_1_1,
 d1Classify_treeRec._native.native_decide.ax_1_1,
 d2Env_isSome._native.native_decide.ax_1_1,
 treeBranch_fresh._native.native_decide.ax_1_1,
 treeLeaf_fresh._native.native_decide.ax_1_1,
 treeListCons_fresh._native.native_decide.ax_1_1,
 treeListNil_fresh._native.native_decide.ax_1_1,
 treeListRec_fresh._native.native_decide.ax_1_1,
 treeList_fresh._native.native_decide.ax_1_1,
 treeNode_fresh._native.native_decide.ax_1_1,
 treeRec_fresh._native.native_decide.ax_1_1,
 tree_fresh._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d2SortInvS

/--
info: 'Lean4Lean.SExpr.ParamsD2.d2IotaRule_ext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 d0Def_fresh._native.native_decide.ax_1_1,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 d0Classify_d1MutA_none._native.native_decide.ax_1_1,
 d0Classify_d1MutB_none._native.native_decide.ax_1_1,
 d1MutA_fresh._native.native_decide.ax_1_1,
 d1MutA_name_ne_mutB._native.native_decide.ax_1_1,
 d1MutB_fresh._native.native_decide.ax_1_1,
 d2AllRules_rhs_nodup._native.native_decide.ax_1_1,
 d2Env_isSome._native.native_decide.ax_1_1,
 treeList_fresh._native.native_decide.ax_1_1,
 tree_fresh._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d2IotaRule_ext

/--
info: 'Lean4Lean.SExpr.ParamsD2.d2IotaRule_levelsLength' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 d0Def_fresh._native.native_decide.ax_1_1,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 d0Classify_d1MutA_none._native.native_decide.ax_1_1,
 d0Classify_d1MutB_none._native.native_decide.ax_1_1,
 d1MutA_fresh._native.native_decide.ax_1_1,
 d1MutA_name_ne_mutB._native.native_decide.ax_1_1,
 d1MutB_fresh._native.native_decide.ax_1_1,
 d2AllRules_rhs_nodup._native.native_decide.ax_1_1,
 d2Env_isSome._native.native_decide.ax_1_1,
 treeList_fresh._native.native_decide.ax_1_1,
 tree_fresh._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d2IotaRule_levelsLength

/--
info: 'Lean4Lean.SExpr.ParamsD2.d2IotaStructuralDescent' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 d0Def_fresh._native.native_decide.ax_1_1,
 d0Def_name_ne_natRec._native.native_decide.ax_1_1,
 d0Def_name_ne_natSucc._native.native_decide.ax_1_1,
 d0Def_name_ne_natZero._native.native_decide.ax_1_1,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 d0Classify_d1MutA_none._native.native_decide.ax_1_1,
 d0Classify_d1MutB_none._native.native_decide.ax_1_1,
 d1MutA_fresh._native.native_decide.ax_1_1,
 d1MutA_name_ne_d0Def._native.native_decide.ax_1_1,
 d1MutA_name_ne_mutB._native.native_decide.ax_1_1,
 d1MutA_name_ne_natRec._native.native_decide.ax_1_1,
 d1MutA_name_ne_natSucc._native.native_decide.ax_1_1,
 d1MutA_name_ne_natZero._native.native_decide.ax_1_1,
 d1MutB_fresh._native.native_decide.ax_1_1,
 d1MutB_name_ne_d0Def._native.native_decide.ax_1_1,
 d1MutB_name_ne_natRec._native.native_decide.ax_1_1,
 d1MutB_name_ne_natSucc._native.native_decide.ax_1_1,
 d1MutB_name_ne_natZero._native.native_decide.ax_1_1,
 d2AllRules_rhs_nodup._native.native_decide.ax_1_1,
 d2Env_isSome._native.native_decide.ax_1_1,
 treeList_fresh._native.native_decide.ax_1_1,
 tree_fresh._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d2IotaStructuralDescent

/--
info: 'Lean4Lean.SExpr.ParamsD2.d2Classified' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 d0Def_fresh._native.native_decide.ax_1_1,
 d0Def_name_ne_natRec._native.native_decide.ax_1_1,
 d0Def_name_ne_natSucc._native.native_decide.ax_1_1,
 d0Def_name_ne_natZero._native.native_decide.ax_1_1,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 d0Classify_d1MutA_none._native.native_decide.ax_1_1,
 d0Classify_d1MutB_none._native.native_decide.ax_1_1,
 d1MutA_fresh._native.native_decide.ax_1_1,
 d1MutA_name_ne_d0Def._native.native_decide.ax_1_1,
 d1MutA_name_ne_mutB._native.native_decide.ax_1_1,
 d1MutA_name_ne_natRec._native.native_decide.ax_1_1,
 d1MutA_name_ne_natSucc._native.native_decide.ax_1_1,
 d1MutA_name_ne_natZero._native.native_decide.ax_1_1,
 d1MutB_fresh._native.native_decide.ax_1_1,
 d1MutB_name_ne_d0Def._native.native_decide.ax_1_1,
 d1MutB_name_ne_natRec._native.native_decide.ax_1_1,
 d1MutB_name_ne_natSucc._native.native_decide.ax_1_1,
 d1MutB_name_ne_natZero._native.native_decide.ax_1_1,
 d2AllRules_rhs_nodup._native.native_decide.ax_1_1,
 d2Env_isSome._native.native_decide.ax_1_1,
 treeList_fresh._native.native_decide.ax_1_1,
 tree_fresh._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d2Classified

/--
info: 'Lean4Lean.SExpr.ParamsD2.d2SortInvSExact' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Lean.PersistentHashMap.findAux_isSome,
 Lean.PersistentHashMap.WF.find?_eq,
 Lean.PersistentHashMap.WF.toList'_insert,
 d0Def_fresh._native.native_decide.ax_1_1,
 d0Def_name_ne_natRec._native.native_decide.ax_1_1,
 d0Def_name_ne_natSucc._native.native_decide.ax_1_1,
 d0Def_name_ne_natZero._native.native_decide.ax_1_1,
 natClassify_d0Def_none._native.native_decide.ax_1_1,
 natRule_rhs_ne_d0Def._native.native_decide.ax_1_2,
 natRule_rhs_ne_d0Def._native.native_decide.ax_1_3,
 probeNatGeneratedRuleSucc_lookup._native.native_decide.ax_1_1,
 probeNatGeneratedRuleZero_lookup._native.native_decide.ax_1_1,
 probeNatRecTypeV_eq._native.native_decide.ax_1_1,
 probeNatRuleRhs_ne._native.native_decide.ax_1_1,
 probeNatSuccCtorName._native.native_decide.ax_1_1,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatSuccRuleLhsV_eq._native.native_decide.ax_1_1,
 probeNatSuccRuleRecName._native.native_decide.ax_1_1,
 probeNatSuccRuleTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 probeNatZeroCtorName._native.native_decide.ax_1_1,
 probeNatZeroRuleLhsV_eq._native.native_decide.ax_1_1,
 probeNatZeroRuleRecName._native.native_decide.ax_1_1,
 probeNatZeroRuleTypeV_eq._native.native_decide.ax_1_1,
 d0Classify_d1MutA_none._native.native_decide.ax_1_1,
 d0Classify_d1MutB_none._native.native_decide.ax_1_1,
 d1MutA_fresh._native.native_decide.ax_1_1,
 d1MutA_name_ne_d0Def._native.native_decide.ax_1_1,
 d1MutA_name_ne_mutB._native.native_decide.ax_1_1,
 d1MutA_name_ne_natRec._native.native_decide.ax_1_1,
 d1MutA_name_ne_natSucc._native.native_decide.ax_1_1,
 d1MutA_name_ne_natZero._native.native_decide.ax_1_1,
 d1MutB_fresh._native.native_decide.ax_1_1,
 d1MutB_name_ne_d0Def._native.native_decide.ax_1_1,
 d1MutB_name_ne_natRec._native.native_decide.ax_1_1,
 d1MutB_name_ne_natSucc._native.native_decide.ax_1_1,
 d1MutB_name_ne_natZero._native.native_decide.ax_1_1,
 natRule_rhs_ne_d1MutA._native.native_decide.ax_1_2,
 natRule_rhs_ne_d1MutA._native.native_decide.ax_1_3,
 natRule_rhs_ne_d1MutB._native.native_decide.ax_1_2,
 natRule_rhs_ne_d1MutB._native.native_decide.ax_1_3,
 d1Classify_tree._native.native_decide.ax_1_1,
 d1Classify_treeBranch._native.native_decide.ax_1_1,
 d1Classify_treeLeaf._native.native_decide.ax_1_1,
 d1Classify_treeList._native.native_decide.ax_1_1,
 d1Classify_treeListCons._native.native_decide.ax_1_1,
 d1Classify_treeListNil._native.native_decide.ax_1_1,
 d1Classify_treeListRec._native.native_decide.ax_1_1,
 d1Classify_treeNode._native.native_decide.ax_1_1,
 d1Classify_treeRec._native.native_decide.ax_1_1,
 d2AllRules_rhs_nodup._native.native_decide.ax_1_1,
 d2Env_isSome._native.native_decide.ax_1_1,
 treeBranch_fresh._native.native_decide.ax_1_1,
 treeLeaf_fresh._native.native_decide.ax_1_1,
 treeListCons_fresh._native.native_decide.ax_1_1,
 treeListNil_fresh._native.native_decide.ax_1_1,
 treeListRec_fresh._native.native_decide.ax_1_1,
 treeList_fresh._native.native_decide.ax_1_1,
 treeNode_fresh._native.native_decide.ax_1_1,
 treeRec_fresh._native.native_decide.ax_1_1,
 tree_fresh._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d2SortInvSExact

end ParamsD2
end SExpr
end Lean4Lean
