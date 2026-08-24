import Lean4Lean.Experimental.ShapeLogRelAdequacy
import Lean4Lean.Experimental.SExprClassified
import Lean4Lean.Theory.Typing.InductivePatternEnv
import Lean4Lean.Verify.Environment.InductiveFixtures

/-!
# L4L-16D0: a concrete `SExpr.Params` fixture

This module instantiates the experimental semantic interface with the
generated `Nat` block.  It is intentionally kept separate from the generic
adequacy development: the fixture is an executable integration test for the
pattern and environment certificates, not another assumption of the generic
theory.
-/

namespace Lean4Lean
namespace SExpr
namespace ParamsD0

open InductiveFixtures InductiveReplayFixtures VInductDecl

abbrev NatGeneration := InductiveFixtures.natBlockGenerationChecked

/-- The two generated Nat iota RHS towers and their (empty) check payloads
are closed. -/
def natRuleClosure : NatGeneration.RuleClosure :=
  VInductDecl.BlockGenerationChecked.RuleClosure.of_all _
    (by decide) (by decide)

/-- The concrete reduction-pattern inventory for the Nat block. -/
abbrev NatPat := NatGeneration.IotaPat natRuleClosure

/-! ## D0b declaration layer

The iota-only `natParams` fixture below is intentionally retained as the
small D0a regression.  D0b extends its Theory environment with one ordinary
definition whose value is a constructor constant; the semantic instance is
layered over D0a later in this file. -/

/-- The host declaration supplies a stable kernel name for the object-level
definition fixture.  Its Theory payload is spelled out explicitly below. -/
def d0def : Nat := Nat.zero

/-- Object-level metadata for `d0def : Nat := Nat.zero`. -/
def d0DefVal : VDefVal where
  name := ``d0def
  uvars := 0
  type := InductiveFixtures.natType.ctors[0].type
  value := .const ``Nat.zero []

theorem d0DefVal_wf : d0DefVal.WF natFinalEnv := by
  have hzero :
      natFinalEnv.constants ``Nat.zero =
        some InductiveFixtures.natType.ctors[0].toVConstant := by
    rfl
  exact VEnv.HasType.const (Γ := []) (ls := []) hzero (by simp) rfl

theorem d0Def_fresh : natFinalEnv.constants d0DefVal.name = none := by
  native_decide

theorem d0Def_name_ne_nat : d0DefVal.name ≠ ``Nat := by native_decide
theorem d0Def_name_ne_natZero : d0DefVal.name ≠ ``Nat.zero := by native_decide
theorem d0Def_name_ne_natSucc : d0DefVal.name ≠ ``Nat.succ := by native_decide
theorem d0Def_name_ne_natRec : d0DefVal.name ≠ ``Nat.rec := by native_decide

local instance : Inhabited VEnv := ⟨VEnv.empty⟩

def d0ConstEnv :=
  (natFinalEnv.addConst d0DefVal.name d0DefVal.toVConstant).get!

/-- The complete D0 environment: generated Nat constants/rules followed by
one checked ordinary definition. -/
def d0Env := d0ConstEnv.addDefEq d0DefVal.toDefEq

theorem natFinalEnv_add_d0Def :
    natFinalEnv.addConst d0DefVal.name d0DefVal.toVConstant =
      some d0ConstEnv := by
  simp [VEnv.addConst, d0Def_fresh, d0ConstEnv]

theorem natFinalEnv_le_d0Env : natFinalEnv ≤ d0Env :=
  (VEnv.addConst_le natFinalEnv_add_d0Def).trans VEnv.addDefEq_le

theorem d0Env_wf : d0Env.WF := by
  obtain ⟨ds, hds⟩ := InductiveReplayFixtures.nat_env_wf
  exact ⟨.def d0DefVal :: ds,
    .decl (.def d0DefVal_wf natFinalEnv_add_d0Def) hds⟩

theorem d0Env_ordered : d0Env.Ordered := d0Env_wf.ordered

theorem d0Env_d0Def_lookup :
    d0Env.constants d0DefVal.name = some d0DefVal.toVConstant :=
  VEnv.addDefEq_le.constants
    (VEnv.addConst_self natFinalEnv_add_d0Def)

theorem d0Env_constants_old {c : Name} {ci : VConstant}
    (hne : c ≠ d0DefVal.name)
    (H : d0Env.constants c = some ci) :
    natFinalEnv.constants c = some ci := by
  simpa [d0Env, d0ConstEnv, VEnv.addConst, d0Def_fresh,
    VEnv.addDefEq, Ne.symm hne] using H

theorem d0Env_defeqs_iff (df : VDefEq) :
    d0Env.defeqs df ↔
      df = d0DefVal.toDefEq ∨ natFinalEnv.defeqs df := by
  simp [d0Env, d0ConstEnv, VEnv.addConst, d0Def_fresh,
    VEnv.addDefEq]

theorem d0Env_no_structEta (rule : VStructEta) :
    ¬d0Env.structEtas rule := by
  change ¬False
  intro h
  exact h

/-- The exact head classification used by the generated Nat rules. -/
def natClassify (n : Name) : Option Classification :=
  if n = ``Nat then some (.indTy 0)
  else if n = ``Nat.zero then some (.ctor 0)
  else if n = ``Nat.succ then some (.ctor 1)
  else if n = ``Nat.rec then some (.symb 4)
  else none

/-- D0b adds exactly one zero-arity definition head to the D0a table. -/
def d0Classify (n : Name) : Option Classification :=
  if n = d0DefVal.name then some (.symb 0) else natClassify n

theorem d0DefClosed : d0DefVal.value.Closed := by
  decide

/-- The complete D0 pattern inventory: both generated Nat iota rules and
the single ordinary definition rule. -/
inductive D0Pat : (p : Pattern) → p.RHS × p.Check → Prop where
  | iota {p : Pattern} {r : p.RHS × p.Check} : NatPat p r → D0Pat p r
  | defn : D0Pat (.const d0DefVal.name)
      (.fixed d0DefVal.value d0DefClosed, .true)

/-- A proof-independent view of the constructor-shaped classifications.
Unlike the `matches` syntax, this predicate does not retain the proof of the
preceding classifier equality in its elaborated motive. -/
def ctorLike : Classification → Bool
  | .ctor _ | .etaCtor _ _ => true
  | .symb _ | .indTy _ => false

theorem natClassify_ctor_cases {c : Name} {cl : Classification}
    (hc : natClassify c = some cl)
    (hshape : ctorLike cl = true) :
    (c = ``Nat.zero ∧ cl = .ctor 0) ∨
      (c = ``Nat.succ ∧ cl = .ctor 1) := by
  by_cases hNat : c = ``Nat
  · subst c
    simp [natClassify] at hc
    subst cl
    simp [ctorLike] at hshape
  by_cases hzero : c = ``Nat.zero
  · subst c
    simp [natClassify] at hc
    exact .inl ⟨rfl, hc.symm⟩
  by_cases hsucc : c = ``Nat.succ
  · subst c
    simp [natClassify] at hc
    exact .inr ⟨rfl, hc.symm⟩
  by_cases hrec : c = ``Nat.rec
  · subst c
    simp [natClassify] at hc
    subst cl
    simp [ctorLike] at hshape
  · simp [natClassify, hNat, hzero, hsucc, hrec] at hc

theorem natRulePattern_inventory :
    NatGeneration.flatCtors.map NatGeneration.rulePattern =
      [.iota ``Nat.rec 3 ``Nat.zero 0,
       .iota ``Nat.rec 3 ``Nat.succ 1] :=
  rfl

theorem natFinalEnv_defeqs_iff (df : VDefEq) :
    natFinalEnv.defeqs df ↔ df ∈ NatGeneration.generatedRules := by
  simpa [VEnv.empty] using
    (VInductDecl.BlockGenerationChecked.addInductBlockGeneration_defeqs
      NatGeneration (base := VEnv.empty) (env₁ := natFinalEnv) (by rfl) df)

theorem natFinalEnv_no_structEta (rule : VStructEta) :
    ¬natFinalEnv.structEtas rule := by
  change ¬False
  intro h
  exact h

theorem natRule_registered {i : Nat} {constructor : NormalizedBlockCtor}
    (hentry : NatGeneration.flatCtors[i]? = some constructor) :
    natFinalEnv.defeqs (NatGeneration.rule i constructor) := by
  rw [natFinalEnv_defeqs_iff]
  unfold VInductDecl.BlockGenerationChecked.generatedRules
  have hmem : (constructor, i) ∈ NatGeneration.flatCtors.zipIdx := by
    apply List.mem_of_getElem? (i := i)
    rw [List.getElem?_zipIdx, hentry, Option.map_some, Nat.zero_add]
  simpa using (List.mem_map_of_mem
    (f := fun ic => NatGeneration.rule ic.2 ic.1) hmem)

/-- Capture paths before they are embedded as `.var` nodes in `ruleRHS`. -/
def natCapturePaths (constructor : NormalizedBlockCtor) :
    List ((NatGeneration.rulePattern constructor).toPattern.Path) :=
  ((Pattern.varNPaths (.const (NatGeneration.ruleRecName constructor))
      (NatGeneration.ruleMajorArity constructor)).take
    (InductiveFixtures.natDecl.nparams + NatGeneration.familyCount +
      NatGeneration.minorCount)).map Sum.inl ++
  ((Pattern.varNPaths (.const constructor.ctor.raw.name)
      (NatGeneration.ruleArgArity constructor)).drop
    InductiveFixtures.natDecl.nparams).map Sum.inr

/-- The zero descriptor keeps all three recursor captures and has no
constructor-field captures. -/
theorem natZeroCapturePaths :
    natCapturePaths NatGeneration.flatCtors[0] =
      (Pattern.varNPaths (.const ``Nat.rec) 3).map Sum.inl := by
  rfl

/-- The successor descriptor keeps all three recursor captures followed by
its single constructor-field capture. -/
theorem natSuccCapturePaths :
    natCapturePaths NatGeneration.flatCtors[1] =
      (Pattern.varNPaths (.const ``Nat.rec) 3).map Sum.inl ++
        (Pattern.varNPaths (.const ``Nat.succ) 1).map Sum.inr := by
  rfl

theorem natCapturePaths_map_var (constructor : NormalizedBlockCtor) :
    (natCapturePaths constructor).map (fun path => Pattern.RHS.var path) =
      NatGeneration.captureArgs constructor := by
  simp [natCapturePaths,
    VInductDecl.BlockGenerationChecked.captureArgs, List.map_map,
    Function.comp_def]

theorem natRuleRHS_tower {i : Nat} {constructor : NormalizedBlockCtor}
    (hentry : NatGeneration.flatCtors[i]? = some constructor) :
    NatGeneration.ruleRHS natRuleClosure hentry =
      Pattern.RHS.appN
        (.fixed (NatGeneration.rule i constructor).rhs
          (natRuleClosure.rhs_closed hentry))
        ((natCapturePaths constructor).map fun path => .var path) := by
  unfold VInductDecl.BlockGenerationChecked.ruleRHS
  rw [natCapturePaths_map_var]

/-! Named paths and exact generated RHS normal forms for the Nat spike. -/

def natZeroMotivePath :
    (RecursorIotaPattern ``Nat.rec 3 ``Nat.zero 0).Path :=
  .inl (some (some none))

def natZeroMinorPath :
    (RecursorIotaPattern ``Nat.rec 3 ``Nat.zero 0).Path :=
  .inl (some none)

def natZeroSuccMinorPath :
    (RecursorIotaPattern ``Nat.rec 3 ``Nat.zero 0).Path :=
  .inl none

/-- Read a canonical three-argument `Nat.rec` capture map pointwise.

The evaluator stores recursor arguments newest first, while `varNPaths`
enumerates them in generated application order.  This small inversion keeps
that reversal in one place and is polymorphic in the captured payload. -/
theorem natRecThreeReadback [Params]
    {α : Type}
    {f : (Pattern.varN (.const ``Nat.rec) 3).Path → α}
    {succ zero motive : α}
    (H : (Pattern.varNPaths (.const ``Nat.rec) 3).map f =
      [succ, zero, motive].reverse) :
    f (some (some none)) = motive ∧ f (some none) = zero ∧
      f none = succ := by
  simpa [Pattern.varNPaths] using H

/-- Read the sole capture of a unary `Nat.succ` match. -/
theorem natSuccOneReadback [Params]
    {α : Type}
    {f : (Pattern.varN (.const ``Nat.succ) 1).Path → α}
    {pred : α}
    (H : (Pattern.varNPaths (.const ``Nat.succ) 1).map f =
      [pred].reverse) :
    f none = pred := by
  simpa [Pattern.varNPaths] using H

/--
info: 'Lean4Lean.SExpr.ParamsD0.natRecThreeReadback' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms natRecThreeReadback

/--
info: 'Lean4Lean.SExpr.ParamsD0.natSuccOneReadback' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms natSuccOneReadback

/-- The singleton Pi tower generated by the three Nat recursor-prefix
captures.  Its arguments are all represented at one base shape level; the
motive and zero-minor layers are lifted by the two enclosing binders. -/
def natZeroCaptureTower [Params] {n : Nat}
    (succElem zeroElem motiveElem succType zeroType motiveType outTy :
      WShape n) : WShape (n + 3) :=
  .forallE (motiveType.lift (n + 2))
    (.single (motiveElem.lift (n + 2)) <|
      .forallE (zeroType.lift (n + 1))
        (.single (zeroElem.lift (n + 1)) <|
          .forallE succType (.single succElem outTy)))

/-- The singleton Pi tower generated by the three Nat recursor-prefix
captures and the strictly smaller predecessor field of a successor major.
The predecessor is represented at the common base level selected by the
rule consumer; its source constructor-field observation lives one level
lower and is lifted exactly once before entering this tower. -/
def natSuccCaptureTower [Params] {n : Nat}
    (predElem succElem zeroElem motiveElem
      predType succType zeroType motiveType outTy : WShape n) :
    WShape (n + 4) :=
  .forallE (motiveType.lift (n + 3))
    (.single (motiveElem.lift (n + 3)) <|
      .forallE (zeroType.lift (n + 2))
        (.single (zeroElem.lift (n + 2)) <|
          .forallE (succType.lift (n + 1))
            (.single (succElem.lift (n + 1)) <|
              .forallE predType (.single predElem outTy))))

def natSuccMotivePath :
    (RecursorIotaPattern ``Nat.rec 3 ``Nat.succ 1).Path :=
  .inl (some (some none))

def natSuccZeroMinorPath :
    (RecursorIotaPattern ``Nat.rec 3 ``Nat.succ 1).Path :=
  .inl (some none)

def natSuccMinorPath :
    (RecursorIotaPattern ``Nat.rec 3 ``Nat.succ 1).Path :=
  .inl none

def natSuccPredPath :
    (RecursorIotaPattern ``Nat.rec 3 ``Nat.succ 1).Path :=
  .inr none

theorem natPat_pattern {p : Pattern} {r : p.RHS × p.Check}
    (H : NatPat p r) :
    p = (SimplePattern.iota ``Nat.rec 3 ``Nat.zero 0).toPattern ∨
      p = (SimplePattern.iota ``Nat.rec 3 ``Nat.succ 1).toPattern := by
  cases H with
  | @mk i constructor hentry =>
    have hmem : constructor ∈ NatGeneration.flatCtors :=
      List.mem_of_getElem? hentry
    have hpattern : NatGeneration.rulePattern constructor ∈
        [.iota ``Nat.rec 3 ``Nat.zero 0,
         .iota ``Nat.rec 3 ``Nat.succ 1] := by
      rw [← natRulePattern_inventory]
      exact List.mem_map_of_mem hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
    exact hpattern.imp (congrArg SimplePattern.toPattern)
      (congrArg SimplePattern.toPattern)

theorem natPat_wf {p : Pattern} {r : p.RHS × p.Check}
    (H : NatPat p r) : p.WF natClassify := by
  cases H with
  | @mk i constructor hentry =>
    have hmem : constructor ∈ NatGeneration.flatCtors :=
      List.mem_of_getElem? hentry
    have hpattern : NatGeneration.rulePattern constructor ∈
        [.iota ``Nat.rec 3 ``Nat.zero 0,
         .iota ``Nat.rec 3 ``Nat.succ 1] := by
      rw [← natRulePattern_inventory]
      exact List.mem_map_of_mem hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpattern
    rcases hpattern with hpattern | hpattern <;> rw [hpattern]
    · simp [SimplePattern.toPattern, Pattern.varN, Pattern.WF, natClassify]
    · simp [SimplePattern.toPattern, Pattern.varN, Pattern.WF, natClassify]

theorem d0Pat_simple {p : Pattern} {r : p.RHS × p.Check}
    (H : D0Pat p r) : ∃ sp : SimplePattern, p = sp.toPattern := by
  cases H with
  | iota H =>
    exact VInductDecl.BlockGenerationChecked.IotaPat.pat_simple
      NatGeneration H
  | defn => exact ⟨.defn d0DefVal.name, rfl⟩

theorem d0Pat_wf {p : Pattern} {r : p.RHS × p.Check}
    (H : D0Pat p r) : p.WF d0Classify := by
  cases H with
  | iota H =>
    rcases natPat_pattern H with hp | hp <;> subst p <;>
      simp [SimplePattern.toPattern, Pattern.WF, d0Classify, natClassify,
        d0DefVal]
  | defn => simp [Pattern.WF, d0Classify]

/-- The fresh D0 definition head cannot intersect any subpattern of either
generated Nat iota rule. -/
theorem d0Def_inter_natSubpattern_none {p p' : Pattern}
    {r : p.RHS × p.Check} (H : NatPat p r)
    (hsub : Subpattern p' p) :
    (Pattern.const d0DefVal.name).inter p' = none := by
  rcases natPat_pattern H with hp | hp
  · subst p
    rcases RecursorIotaPattern.subpattern_inv hsub with
      rfl | ⟨j, -, rfl⟩ | ⟨j, -, rfl⟩
    · rfl
    · simpa only [Pattern.varN] using
        Pattern.varN_const_inter_of_ne_name d0Def_name_ne_natRec 0 j
    · simpa only [Pattern.varN] using
        Pattern.varN_const_inter_of_ne_name d0Def_name_ne_natZero 0 j
  · subst p
    rcases RecursorIotaPattern.subpattern_inv hsub with
      rfl | ⟨j, -, rfl⟩ | ⟨j, -, rfl⟩
    · rfl
    · simpa only [Pattern.varN] using
        Pattern.varN_const_inter_of_ne_name d0Def_name_ne_natRec 0 j
    · simpa only [Pattern.varN] using
        Pattern.varN_const_inter_of_ne_name d0Def_name_ne_natSucc 0 j

theorem d0Pat_uniq {p₁ p₂ p₃ p₄ : Pattern}
    {r : p₁.RHS × p₁.Check} {r' : p₂.RHS × p₂.Check}
    (H1 : D0Pat p₁ r) (H2 : D0Pat p₂ r')
    (H3 : Subpattern p₃ p₁) (H4 : p₂.inter p₃ = some p₄) :
    p₁ = p₂ ∧ p₂ = p₃ ∧ r ≍ r' := by
  cases H1 with
  | iota H1 =>
    cases H2 with
    | iota H2 =>
      exact VInductDecl.BlockGenerationChecked.IotaPat.pat_uniq
        NatGeneration H1 H2 H3 H4
    | defn =>
      rw [d0Def_inter_natSubpattern_none H1 H3] at H4
      cases H4
  | defn =>
    cases H2 with
    | iota H2 =>
      cases H3
      rw [Pattern.inter_comm,
        d0Def_inter_natSubpattern_none H2 (Subpattern.refl)] at H4
      cases H4
    | defn =>
      cases H3
      simp [Pattern.inter] at H4
      subst p₄
      exact ⟨rfl, rfl, HEq.rfl⟩

theorem d0Pat_app_l {p : Pattern} {r : p.RHS × p.Check}
    {p₁ p₂ p₃ p₄ : Pattern}
    (H : D0Pat p r) (h : Subpattern (.app p₁ p₂) p) :
    ¬Subpattern (.app p₃ p₄) p₁ := by
  cases H with
  | iota H =>
    exact VInductDecl.BlockGenerationChecked.IotaPat.pat_app_l
      NatGeneration H h
  | defn => cases h

theorem d0Pat_app_l_uniq {p p' : Pattern}
    {r : p.RHS × p.Check} {r' : p'.RHS × p'.Check}
    {p₁ p₂ p₁' p₂' p₃ : Pattern}
    (H : D0Pat p r) (H' : D0Pat p' r')
    (h : Subpattern (.app p₁ p₂) p)
    (h' : Subpattern (.app p₁' p₂') p')
    (h₃ : Subpattern (.var p₃) p₁) : p₁'.inter p₃ = none := by
  cases H with
  | iota H =>
    cases H' with
    | iota H' =>
      exact VInductDecl.BlockGenerationChecked.IotaPat.pat_app_l_uniq
        NatGeneration H H' h h' h₃
    | defn => cases h'
  | defn => cases h

theorem d0Pat_app_uniq {p p' : Pattern}
    {r : p.RHS × p.Check} {r' : p'.RHS × p'.Check}
    {p₁ p₂ p₁' p₂' p₃ p₃' : Pattern}
    (H : D0Pat p r) (H' : D0Pat p' r')
    (h : Subpattern (.app p₁ p₂) p)
    (h' : Subpattern (.app p₁' p₂') p')
    (h₃ : Subpattern p₃ p₁) (h₃' : Subpattern p₃' p₂') :
    p₃.inter p₃' = none := by
  cases H with
  | iota H =>
    cases H' with
    | iota H' =>
      exact VInductDecl.BlockGenerationChecked.IotaPat.pat_app_uniq
        NatGeneration H H' h h' h₃ h₃'
    | defn => cases h'
  | defn => cases h

/-- Reading the canonical paths of an SExpr `varN` match returns its
application arguments in application order. -/
theorem matchesS_varN_paths [Params] {c : Name} {ls : List SLevel} :
    ∀ (n : Nat) (args : List SExpr)
      {mcap : (Pattern.varN (.const c) n).Path → SExpr},
      (Pattern.varN (.const c) n).MatchesS
        (args.foldl (fun f a => f.app a) (.const c ls)) ls mcap →
      args.length = n →
      (Pattern.varNPaths (.const c) n).map mcap = args := by
  intro n
  induction n with
  | zero =>
    intro args mcap H hlen
    obtain rfl : args = [] := List.length_eq_zero_iff.mp hlen
    rfl
  | succ n ih =>
    intro args mcap H hlen
    have hne : args ≠ [] := by rintro rfl; simp at hlen
    obtain ⟨args', arg, rfl⟩ : ∃ args' arg, args = args' ++ [arg] :=
      ⟨args.dropLast, args.getLast hne,
        (List.dropLast_concat_getLast hne).symm⟩
    have hlen' : args'.length = n := by simpa using hlen
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil] at H
    cases H with
    | var H =>
      show ((Pattern.varNPaths (.const c) n).map some ++ [none]).map _ =
        args' ++ [arg]
      rw [List.map_append, List.map_map]
      exact congrArg (fun xs => xs ++ [arg]) (ih args' H hlen')

/-- Split an SExpr into its non-application head and application-order
spine. -/
def sexprSpine [Params] : SExpr → SExpr × List SExpr
  | .app f a =>
    let (head, args) := sexprSpine f
    (head, args ++ [a])
  | e => (e, [])

theorem sexprSpine_foldl [Params] (f : SExpr) (args : List SExpr) :
    sexprSpine (args.foldl (fun f a => f.app a) f) =
      (match sexprSpine f with
      | (head, pre) => (head, pre ++ args)) := by
  induction args generalizing f with
  | nil => simp
  | cons arg args ih =>
    rw [List.foldl_cons, ih]
    simp [sexprSpine, List.append_assoc]

theorem constFoldl_inj [Params] {c : Name} {ls ls' : List SLevel}
    {xs ys : List SExpr}
    (h : xs.foldl (fun (f a : SExpr) => f.app a) (SExpr.const c ls) =
      ys.foldl (fun (f a : SExpr) => f.app a) (SExpr.const c ls')) :
    ls = ls' ∧ xs = ys := by
  have hs := congrArg sexprSpine h
  rw [sexprSpine_foldl, sexprSpine_foldl] at hs
  have hhead := congrArg (fun pair => pair.1) hs
  have hargs := congrArg (fun pair => pair.2) hs
  constructor
  · injection hhead
  · simpa [sexprSpine] using hargs

/-- A concrete constant-headed `varN` match both fixes the spine length and
reads its captures back in application order. -/
theorem matchesS_varN_foldr [Params] {c : Name}
    {exprLs matchLs : List SLevel}
    {n : Nat} {args : List SExpr}
    {mcap : (Pattern.varN (.const c) n).Path → SExpr}
    (H : (Pattern.varN (.const c) n).MatchesS
      (args.foldr (fun a f => f.app a) (.const c exprLs)) matchLs mcap) :
    exprLs = matchLs ∧ args.length = n ∧
      (Pattern.varNPaths (.const c) n).map mcap = args.reverse := by
  obtain ⟨args', hlen, heq, H'⟩ := H.varN_const_inv
  have heq' :
      args.reverse.foldl (fun (f a : SExpr) => f.app a)
          (SExpr.const c exprLs) =
        args'.reverse.foldl (fun (f a : SExpr) => f.app a)
          (SExpr.const c matchLs) := by
    rw [List.foldl_reverse, List.foldl_reverse]
    exact heq
  obtain ⟨hlevels, hargs⟩ := constFoldl_inj heq'
  refine ⟨hlevels, ?_, ?_⟩
  · calc
      args.length = args.reverse.length := by simp
      _ = args'.reverse.length := congrArg List.length hargs
      _ = args'.length := by simp
      _ = n := hlen
  · have H'' : (Pattern.varN (.const c) n).MatchesS
        (args'.reverse.foldl (fun f a => f.app a) (.const c matchLs)) matchLs mcap := by
      simpa only [List.foldl_reverse] using H'
    rw [matchesS_varN_paths n args'.reverse H'' (by simpa using hlen)]
    exact hargs.symm

/-- Split an RHS syntax tree into its non-application head and left-to-right
application spine. -/
def rhsSpine {p : Pattern} : p.RHS → p.RHS × List p.RHS
  | r@(.fixed ..) | r@(.var ..) => (r, [])
  | .app f a =>
    let (head, args) := rhsSpine f
    (head, args ++ [a])

theorem rhsSpine_appN {p : Pattern} (f : p.RHS) (args : List p.RHS) :
    rhsSpine (Pattern.RHS.appN f args) =
      (match rhsSpine f with
      | (head, pre) => (head, pre ++ args)) := by
  induction args generalizing f with
  | nil => simp [Pattern.RHS.appN]
  | cons arg args ih =>
    rw [Pattern.RHS.appN]
    rw [ih]
    simp [rhsSpine, List.append_assoc]

/-- A fixed-headed RHS application tower is injective in both its fixed
VExpr head and its ordered path arguments. -/
theorem rhsFixedAppN_inj {p : Pattern} {f g : VExpr}
    {hf : f.Closed} {hg : g.Closed} {xs ys : List p.Path}
    (h : Pattern.RHS.appN (.fixed f hf) (xs.map .var) =
      Pattern.RHS.appN (.fixed g hg) (ys.map .var)) :
    f = g ∧ xs = ys := by
  have hs := congrArg rhsSpine h
  rw [rhsSpine_appN, rhsSpine_appN] at hs
  simp only [rhsSpine, List.nil_append] at hs
  have hhead := congrArg (fun pair => pair.1) hs
  have hargs := congrArg (fun pair => pair.2) hs
  constructor
  · injection hhead
  · exact (List.map_inj_right
      (fun _ _ hvar => Pattern.RHS.var.inj hvar)).mp hargs

/-- The structural half of the D0 integration fixture.  `univs` remains a
parameter because the Nat environment itself is closed and the experimental
judgment deliberately supports arbitrary ambient universe valuations. -/
def natParams (univs : Nat) : Params where
  env := natFinalEnv
  henv := natFinalEnv_ordered
  univs := univs
  Pat := NatPat
  classify := natClassify
  pat_simple :=
    VInductDecl.BlockGenerationChecked.IotaPat.pat_simple NatGeneration
  pat_wf := natPat_wf
  pat_uniq :=
    VInductDecl.BlockGenerationChecked.IotaPat.pat_uniq NatGeneration
  pat_app_l :=
    VInductDecl.BlockGenerationChecked.IotaPat.pat_app_l NatGeneration
  pat_app_l_uniq :=
    VInductDecl.BlockGenerationChecked.IotaPat.pat_app_l_uniq NatGeneration
  pat_app_uniq :=
    VInductDecl.BlockGenerationChecked.IotaPat.pat_app_uniq NatGeneration

/-- The complete D0b structural instance.  It preserves the generated Nat
inventory and adds the one fresh definition pattern. -/
def d0Params (univs : Nat) : Params where
  env := d0Env
  henv := d0Env_ordered
  univs := univs
  Pat := D0Pat
  classify := d0Classify
  pat_simple := d0Pat_simple
  pat_wf := d0Pat_wf
  pat_uniq := d0Pat_uniq
  pat_app_l := d0Pat_app_l
  pat_app_l_uniq := d0Pat_app_l_uniq
  pat_app_uniq := d0Pat_app_uniq

/-! ## D0a-to-D0b proof transport

`SExpr` retains its complete `Params` value as an inductive parameter.  D0
transport is therefore an explicit syntax map (developed below), not a cast
based only on the shared universe count. -/

def natToD0Level (univs : Nat)
    (u : @SLevel (natParams univs)) : @SLevel (d0Params univs) := by
  refine ⟨u.1, ?_⟩
  obtain ⟨l, hl, heval⟩ := u.2
  refine ⟨l, ?_, heval⟩
  change l.WF univs
  change l.WF univs at hl
  exact hl

def d0ToNatLevel (univs : Nat)
    (u : @SLevel (d0Params univs)) : @SLevel (natParams univs) := by
  refine ⟨u.1, ?_⟩
  obtain ⟨l, hl, heval⟩ := u.2
  refine ⟨l, ?_, heval⟩
  change l.WF univs
  change l.WF univs at hl
  exact hl

@[simp] theorem d0ToNatLevel_natToD0Level (univs : Nat)
    (u : @SLevel (natParams univs)) :
    d0ToNatLevel univs (natToD0Level univs u) = u := by
  apply Subtype.ext
  rfl

@[simp] theorem natToD0Level_d0ToNatLevel (univs : Nat)
    (u : @SLevel (d0Params univs)) :
    natToD0Level univs (d0ToNatLevel univs u) = u := by
  apply Subtype.ext
  rfl

noncomputable def natToD0Expr (univs : Nat) (e : @SExpr (natParams univs)) :
    @SExpr (d0Params univs) :=
  @SExpr.rec (natParams univs)
    (motive := fun _ => @SExpr (d0Params univs))
    (fun i => @SExpr.bvar (d0Params univs) i)
    (fun u => @SExpr.sort (d0Params univs) (natToD0Level univs u))
    (fun c ls => @SExpr.const (d0Params univs) c
      (ls.map (natToD0Level univs)))
    (fun _ _ f a => @SExpr.app (d0Params univs) f a)
    (fun _ _ A body => @SExpr.lam (d0Params univs) A body)
    (fun _ _ A B => @SExpr.forallE (d0Params univs) A B)
    e

noncomputable def d0ToNatExpr (univs : Nat) (e : @SExpr (d0Params univs)) :
    @SExpr (natParams univs) :=
  @SExpr.rec (d0Params univs)
    (motive := fun _ => @SExpr (natParams univs))
    (fun i => @SExpr.bvar (natParams univs) i)
    (fun u => @SExpr.sort (natParams univs) (d0ToNatLevel univs u))
    (fun c ls => @SExpr.const (natParams univs) c
      (ls.map (d0ToNatLevel univs)))
    (fun _ _ f a => @SExpr.app (natParams univs) f a)
    (fun _ _ A body => @SExpr.lam (natParams univs) A body)
    (fun _ _ A B => @SExpr.forallE (natParams univs) A B)
    e

@[simp] theorem natToD0Expr_bvar (univs i) :
    natToD0Expr univs (@SExpr.bvar (natParams univs) i) =
      @SExpr.bvar (d0Params univs) i := rfl

@[simp] theorem natToD0Expr_sort (univs) (u : @SLevel (natParams univs)) :
    natToD0Expr univs (@SExpr.sort (natParams univs) u) =
      @SExpr.sort (d0Params univs) (natToD0Level univs u) := rfl

@[simp] theorem natToD0Expr_const (univs c)
    (ls : List (@SLevel (natParams univs))) :
    natToD0Expr univs (@SExpr.const (natParams univs) c ls) =
      @SExpr.const (d0Params univs) c (ls.map (natToD0Level univs)) := rfl

@[simp] theorem natToD0Expr_app (univs)
    (f a : @SExpr (natParams univs)) :
    natToD0Expr univs (@SExpr.app (natParams univs) f a) =
      @SExpr.app (d0Params univs) (natToD0Expr univs f)
        (natToD0Expr univs a) := rfl

@[simp] theorem natToD0Expr_lam (univs)
    (A e : @SExpr (natParams univs)) :
    natToD0Expr univs (@SExpr.lam (natParams univs) A e) =
      @SExpr.lam (d0Params univs) (natToD0Expr univs A)
        (natToD0Expr univs e) := rfl

@[simp] theorem natToD0Expr_forallE (univs)
    (A B : @SExpr (natParams univs)) :
    natToD0Expr univs (@SExpr.forallE (natParams univs) A B) =
      @SExpr.forallE (d0Params univs) (natToD0Expr univs A)
        (natToD0Expr univs B) := rfl

@[simp] theorem d0ToNatExpr_bvar (univs i) :
    d0ToNatExpr univs (@SExpr.bvar (d0Params univs) i) =
      @SExpr.bvar (natParams univs) i := rfl

@[simp] theorem d0ToNatExpr_sort (univs) (u : @SLevel (d0Params univs)) :
    d0ToNatExpr univs (@SExpr.sort (d0Params univs) u) =
      @SExpr.sort (natParams univs) (d0ToNatLevel univs u) := rfl

@[simp] theorem d0ToNatExpr_const (univs c)
    (ls : List (@SLevel (d0Params univs))) :
    d0ToNatExpr univs (@SExpr.const (d0Params univs) c ls) =
      @SExpr.const (natParams univs) c (ls.map (d0ToNatLevel univs)) := rfl

@[simp] theorem d0ToNatExpr_app (univs)
    (f a : @SExpr (d0Params univs)) :
    d0ToNatExpr univs (@SExpr.app (d0Params univs) f a) =
      @SExpr.app (natParams univs) (d0ToNatExpr univs f)
        (d0ToNatExpr univs a) := rfl

@[simp] theorem d0ToNatExpr_lam (univs)
    (A e : @SExpr (d0Params univs)) :
    d0ToNatExpr univs (@SExpr.lam (d0Params univs) A e) =
      @SExpr.lam (natParams univs) (d0ToNatExpr univs A)
        (d0ToNatExpr univs e) := rfl

@[simp] theorem d0ToNatExpr_forallE (univs)
    (A B : @SExpr (d0Params univs)) :
    d0ToNatExpr univs (@SExpr.forallE (d0Params univs) A B) =
      @SExpr.forallE (natParams univs) (d0ToNatExpr univs A)
        (d0ToNatExpr univs B) := rfl


@[simp] theorem d0ToNatExpr_natToD0Expr (univs : Nat)
    (e : @SExpr (natParams univs)) :
    d0ToNatExpr univs (natToD0Expr univs e) = e := by
  induction e <;> simp [List.map_map, Function.comp_def, *]

@[simp] theorem natToD0Expr_d0ToNatExpr (univs : Nat)
    (e : @SExpr (d0Params univs)) :
    natToD0Expr univs (d0ToNatExpr univs e) = e := by
  induction e <;> simp [List.map_map, Function.comp_def, *]

noncomputable def natToD0Subst (univs : Nat) (sigma : @Subst (natParams univs)) :
    @Subst (d0Params univs) := fun i => natToD0Expr univs (sigma i)

@[simp] theorem natToD0Expr_lift' (univs : Nat)
    (e : @SExpr (natParams univs)) (rho : Lift) :
    natToD0Expr univs (@SExpr.lift' (natParams univs) e rho) =
      @SExpr.lift' (d0Params univs) (natToD0Expr univs e) rho := by
  induction e generalizing rho <;> simp [SExpr.lift', *]

@[simp] theorem natToD0Subst_lift (univs : Nat)
    (sigma : @Subst (natParams univs)) :
    natToD0Subst univs (@Subst.lift (natParams univs) sigma) =
      @Subst.lift (d0Params univs) (natToD0Subst univs sigma) := by
  funext i
  cases i <;> simp [natToD0Subst, Subst.lift,
    natToD0Expr_lift']

@[simp] theorem natToD0Expr_subst (univs : Nat)
    (e : @SExpr (natParams univs)) (sigma : @Subst (natParams univs)) :
    natToD0Expr univs (@SExpr.subst (natParams univs) e sigma) =
      @SExpr.subst (d0Params univs) (natToD0Expr univs e)
        (natToD0Subst univs sigma) := by
  induction e generalizing sigma <;>
    simp [SExpr.subst, natToD0Subst, *]

@[simp] theorem natToD0Expr_inst (univs : Nat)
    (e a : @SExpr (natParams univs)) :
    natToD0Expr univs (@SExpr.inst (natParams univs) e a) =
      @SExpr.inst (d0Params univs) (natToD0Expr univs e)
        (natToD0Expr univs a) := by
  change natToD0Expr univs
      (@SExpr.subst (natParams univs) e (@Subst.one (natParams univs) a)) =
    @SExpr.subst (d0Params univs) (natToD0Expr univs e)
      (@Subst.one (d0Params univs) (natToD0Expr univs a))
  rw [natToD0Expr_subst]
  congr 1
  funext i
  cases i <;> rfl

@[simp] theorem natToD0Level_instV (univs : Nat)
    (ls : List (@SLevel (natParams univs))) (u : VLevel) :
    natToD0Level univs (@SLevel.instV (natParams univs) ls u) =
      @SLevel.instV (d0Params univs) (ls.map (natToD0Level univs)) u := by
  apply Subtype.ext
  funext v
  change u.eval (ls.map fun l => l.1 v) =
    u.eval ((ls.map (natToD0Level univs)).map fun l => l.1 v)
  congr 1
  simp [List.map_map, Function.comp_def, natToD0Level]

@[simp] theorem natToD0Level_succ (univs : Nat)
    (u : @SLevel (natParams univs)) :
    natToD0Level univs (@SLevel.succ (natParams univs) u) =
      @SLevel.succ (d0Params univs) (natToD0Level univs u) := by
  apply Subtype.ext
  rfl

@[simp] theorem natToD0Level_imax (univs : Nat)
    (u v : @SLevel (natParams univs)) :
    natToD0Level univs (@SLevel.imax (natParams univs) u v) =
      @SLevel.imax (d0Params univs)
        (natToD0Level univs u) (natToD0Level univs v) := by
  apply Subtype.ext
  rfl

@[simp] theorem natToD0Expr_mkInst (univs : Nat)
    (ls : List (@SLevel (natParams univs))) (e : VExpr) :
    natToD0Expr univs (@SExpr.mkInst (natParams univs) ls e) =
      @SExpr.mkInst (d0Params univs) (ls.map (natToD0Level univs)) e := by
  induction e <;> simp [SExpr.mkInst, List.map_map, Function.comp_def, *]

theorem natLookup_to_d0 (univs : Nat)
    {Gamma : List (@SExpr (natParams univs))} {i : Nat}
    {A : @SExpr (natParams univs)}
    (H : @Lookup (natParams univs) Gamma i A) :
    @Lookup (d0Params univs) (Gamma.map (natToD0Expr univs)) i
      (natToD0Expr univs A) := by
  letI : Params := d0Params univs
  induction H with
  | zero =>
    rw [natToD0Expr_lift']
    exact .zero
  | succ _ ih =>
    rw [natToD0Expr_lift']
    exact .succ ih

theorem natIsDefEq_to_d0 (univs : Nat)
    {Gamma : List (@SExpr (natParams univs))}
    {e₁ e₂ A : @SExpr (natParams univs)}
    (H : @IsDefEq (natParams univs) Gamma e₁ e₂ A) :
    @IsDefEq (d0Params univs) (Gamma.map (natToD0Expr univs))
      (natToD0Expr univs e₁) (natToD0Expr univs e₂)
      (natToD0Expr univs A) := by
  letI : Params := d0Params univs
  induction H with
  | bvar h => exact .bvar (natLookup_to_d0 univs h)
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | @sort Gamma l =>
    simpa only [natToD0Expr_sort, natToD0Level_succ] using
      (IsDefEq.sort : IsDefEq (Gamma.map (natToD0Expr univs))
        (.sort (natToD0Level univs l)) (.sort (natToD0Level univs l))
        (.sort (.succ (natToD0Level univs l))))
  | @const c ci Gamma ls hreg hlen =>
    simpa only [natToD0Expr_const, natToD0Expr_mkInst] using
      (IsDefEq.const (Γ := Gamma.map (natToD0Expr univs))
        (ls := ls.map (natToD0Level univs))
        (natFinalEnv_le_d0Env.constants hreg) (by simpa using hlen))
  | appDF _ _ ihf iha =>
    rw [natToD0Expr_app, natToD0Expr_app, natToD0Expr_inst]
    exact IsDefEq.appDF ihf iha
  | lamDF _ _ ihA ihBody =>
    simpa only [List.map_cons, natToD0Expr_lam, natToD0Expr_forallE] using
      IsDefEq.lamDF ihA ihBody
  | forallEDF _ _ ihA ihBody =>
    simpa only [List.map_cons, natToD0Expr_forallE, natToD0Expr_sort,
      natToD0Level_imax] using IsDefEq.forallEDF ihA ihBody
  | defeqDF _ _ ihA ihe => exact .defeqDF ihA ihe
  | beta _ _ ihBody ihArg =>
    simpa only [List.map_cons, natToD0Expr_app, natToD0Expr_lam,
      natToD0Expr_inst] using
      IsDefEq.beta ihBody ihArg
  | eta _ ih =>
    rw [natToD0Expr_lam, natToD0Expr_app, natToD0Expr_bvar,
      natToD0Expr_forallE, natToD0Expr_lift']
    exact IsDefEq.eta ih
  | proofIrrel _ _ _ ihp ihh ihh' => exact .proofIrrel ihp ihh ihh'
  | @extra df Gamma ls hreg hlen =>
    simpa only [natToD0Expr_mkInst] using
      (IsDefEq.extra (Γ := Gamma.map (natToD0Expr univs))
        (ls := ls.map (natToD0Level univs))
        (natFinalEnv_le_d0Env.defeqs hreg) (by simpa using hlen))

theorem natClassify_d0Def_none : natClassify d0DefVal.name = none := by
  native_decide

/-- A constructor-shaped D0b classification cannot be the new definition,
and therefore determines the same constructor classification in D0a. -/
theorem d0CtorToNat (univs : Nat) {c : Name}
    (H : @CtorBundle.IsCtor (d0Params univs) c) :
    @CtorBundle.IsCtor (natParams univs) c := by
  change ∃ cl, d0Classify c = some cl ∧
    (match cl with | .ctor _ | .etaCtor _ _ => true | _ => false) = true at H
  change ∃ cl, natClassify c = some cl ∧
    (match cl with | .ctor _ | .etaCtor _ _ => true | _ => false) = true
  obtain ⟨cl, hclass, hshape⟩ := H
  have hne : c ≠ d0DefVal.name := by
    intro hc
    subst c
    simp [d0Classify] at hclass
    subst cl
    simp at hshape
  exact ⟨cl, by simpa [d0Classify, hne] using hclass, hshape⟩

theorem natIndTyClassify_to_d0 {c : Name} {arity : Nat}
    (H : natClassify c = some (.indTy arity)) :
    d0Classify c = some (.indTy arity) := by
  have hne : c ≠ d0DefVal.name := by
    intro hc
    subst c
    rw [natClassify_d0Def_none] at H
    cases H
  simpa [d0Classify, hne] using H

theorem d0CtorToNat_cl_eq (univs : Nat) {c : Name}
    (cl : @CtorBundle.IsCtor (d0Params univs) c) :
    (@CtorBundle.IsCtor.cl (natParams univs) c (d0CtorToNat univs cl)).1 =
      (@CtorBundle.IsCtor.cl (d0Params univs) c cl).1 := by
  let oldCl := @CtorBundle.IsCtor.cl (natParams univs) c
    (d0CtorToNat univs cl)
  let newCl := @CtorBundle.IsCtor.cl (d0Params univs) c cl
  have hne : c ≠ d0DefVal.name := by
    intro hc
    subst c
    have hold := oldCl.2.1
    change natClassify d0DefVal.name = some oldCl.1 at hold
    rw [natClassify_d0Def_none] at hold
    cases hold
  have hnewNat : natClassify c = some newCl.1 := by
    have hnew := newCl.2.1
    change d0Classify c = some newCl.1 at hnew
    simpa [d0Classify, hne] using hnew
  have hold := oldCl.2.1
  change natClassify c = some oldCl.1 at hold
  exact Option.some.inj (hold.symm.trans hnewNat)

/-- Reindex a D0a constructor bundle through the syntax and classifier
maps. -/
noncomputable def natCtorBundleToD0 (univs : Nat) {c : Name}
    (cl : @CtorBundle.IsCtor (d0Params univs) c)
    (F : @CtorBundle (natParams univs) c (d0CtorToNat univs cl)) :
    @CtorBundle (d0Params univs) c cl := by
  rcases F with ⟨I, Ts, args, u, hlen, hclI, hu0⟩
  refine @CtorBundle.mk (d0Params univs) c cl I
    (Ts.map (natToD0Expr univs)) (args.map (natToD0Expr univs))
    (natToD0Level univs u) ?_ ?_ ?_
  · rw [List.length_map, hlen, d0CtorToNat_cl_eq univs cl]
  · change natClassify I = some (.indTy args.length) at hclI
    letI : Params := d0Params univs
    change d0Classify I = some (.indTy (args.map (natToD0Expr univs)).length)
    simpa using natIndTyClassify_to_d0 hclI
  · intro hzero
    have hback := congrArg (d0ToNatLevel univs) hzero
    apply hu0
    apply Subtype.ext
    exact congrArg Subtype.val hback

theorem natToD0Expr_foldr_forallE (univs : Nat)
    (Ts : List (@SExpr (natParams univs))) (e : @SExpr (natParams univs)) :
    natToD0Expr univs
        (Ts.foldr (fun A B => @SExpr.forallE (natParams univs) A B) e) =
      (Ts.map (natToD0Expr univs)).foldr
        (fun A B => @SExpr.forallE (d0Params univs) A B)
        (natToD0Expr univs e) := by
  induction Ts <;> simp [*]

theorem natToD0Expr_foldr_app (univs : Nat)
    (args : List (@SExpr (natParams univs)))
    (e : @SExpr (natParams univs)) :
    natToD0Expr univs
        (args.foldr (fun A acc => @SExpr.app (natParams univs) acc A) e) =
      (args.map (natToD0Expr univs)).foldr
        (fun A acc => @SExpr.app (d0Params univs) acc A)
        (natToD0Expr univs e) := by
  induction args <;> simp [*]

@[simp] theorem natCtorBundleToD0_rhs (univs : Nat) {c : Name}
    (cl : @CtorBundle.IsCtor (d0Params univs) c)
    (F : @CtorBundle (natParams univs) c (d0CtorToNat univs cl))
    (ls : List (@SLevel (natParams univs))) :
    natToD0Expr univs (@CtorBundle.rhs (natParams univs) c
      (d0CtorToNat univs cl) F ls) =
      @CtorBundle.rhs (d0Params univs) c cl
        (natCtorBundleToD0 univs cl F)
        (ls.map (natToD0Level univs)) := by
  rcases F with ⟨I, Ts, args, u, hlen, hclI, hu0⟩
  simp [CtorBundle.rhs, natCtorBundleToD0,
    natToD0Expr_foldr_forallE, natToD0Expr_foldr_app]

@[simp] theorem natCtorBundleToD0_u (univs : Nat) {c : Name}
    (cl : @CtorBundle.IsCtor (d0Params univs) c)
    (F : @CtorBundle (natParams univs) c (d0CtorToNat univs cl)) :
    @CtorBundle.u (d0Params univs) c cl
        (natCtorBundleToD0 univs cl F) =
      natToD0Level univs
        (@CtorBundle.u (natParams univs) c (d0CtorToNat univs cl) F) := by
  cases F
  rfl

@[simp] theorem natToD0Expr_rhs_applyS (univs : Nat) {p : Pattern}
    (r : p.RHS) (m₁ : List (@SLevel (natParams univs)))
    (m₂ : p.Path → @SExpr (natParams univs)) :
    natToD0Expr univs
        (@Pattern.RHS.applyS (natParams univs) p m₁ m₂ r) =
      @Pattern.RHS.applyS (d0Params univs) p
        (m₁.map (natToD0Level univs))
        (fun path => natToD0Expr univs (m₂ path)) r := by
  induction r with
  | fixed e closed => exact natToD0Expr_mkInst univs m₁ e
  | var path => rfl
  | app f a ihf iha =>
    simp only [Pattern.RHS.applyS, natToD0Expr_app, ihf, iha]

theorem natMatchesS_to_d0 (univs : Nat) {p : Pattern}
    {e : @SExpr (natParams univs)}
    {m₁ : List (@SLevel (natParams univs))}
    {m₂ : p.Path → @SExpr (natParams univs)}
    (H : @Pattern.MatchesS (natParams univs) p e m₁ m₂) :
    @Pattern.MatchesS (d0Params univs) p (natToD0Expr univs e)
      (m₁.map (natToD0Level univs))
      (fun path => natToD0Expr univs (m₂ path)) := by
  letI : Params := d0Params univs
  induction H with
  | @const c ls =>
    rw [natToD0Expr_const]
    refine cast ?_ (@Pattern.MatchesS.const (d0Params univs) c
      (ls.map (natToD0Level univs)))
    congr 1
    funext path
    exact Empty.elim path
  | @var f f' f₁ g₁ a' _ ih =>
    change @Pattern.MatchesS (d0Params univs) (.var f)
      (.app (natToD0Expr univs f') (natToD0Expr univs a'))
      (f₁.map (natToD0Level univs))
      (fun path => natToD0Expr univs (Option.elim path a' g₁))
    have heq : (fun path => natToD0Expr univs (Option.elim path a' g₁)) =
        (fun path => Option.elim path (natToD0Expr univs a')
          (fun path => natToD0Expr univs (g₁ path))) := by
      funext path
      cases path <;> rfl
    rw [heq]
    exact ih.var
  | @app f f' f₁ g₁ a a' f₂ g₂ _ _ ihf iha =>
    change @Pattern.MatchesS (d0Params univs) (.app f a)
      (@SExpr.app (d0Params univs)
        (natToD0Expr univs f') (natToD0Expr univs a'))
      (f₁.map (natToD0Level univs))
      (fun path => natToD0Expr univs (Sum.elim g₁ g₂ path))
    have heq : (fun path => natToD0Expr univs (Sum.elim g₁ g₂ path)) =
        Sum.elim (fun path => natToD0Expr univs (g₁ path))
          (fun path => natToD0Expr univs (g₂ path)) := by
      funext path
      cases path <;> rfl
    rw [heq]
    exact ihf.app iha

theorem natToD0_defeqsS (univs : Nat) {p : Pattern}
    (ck : p.Check) (m₁ : List (@SLevel (natParams univs)))
    (m₂ : p.Path → @SExpr (natParams univs)) :
    (@Pattern.Check.defeqsS (natParams univs) p m₁ m₂ ck).map
        (fun ab => (natToD0Expr univs ab.1, natToD0Expr univs ab.2)) =
      @Pattern.Check.defeqsS (d0Params univs) p
        (m₁.map (natToD0Level univs))
        (fun path => natToD0Expr univs (m₂ path)) ck := by
  induction ck with
  | true => rfl
  | defeq a b rest ih =>
    simp only [Pattern.Check.defeqsS, List.map_cons, ih,
      natToD0Expr_rhs_applyS]

noncomputable def natToD0Dfs (univs : Nat)
    (dfs : List (@SExpr (natParams univs) × @SExpr (natParams univs) ×
      @SExpr (natParams univs))) :
    List (@SExpr (d0Params univs) × @SExpr (d0Params univs) ×
      @SExpr (d0Params univs)) :=
  dfs.map fun (B, a, b) =>
    (natToD0Expr univs B, natToD0Expr univs a, natToD0Expr univs b)

theorem natToD0Dfs_map_snd (univs : Nat)
    (dfs : List (@SExpr (natParams univs) × @SExpr (natParams univs) ×
      @SExpr (natParams univs))) :
    (natToD0Dfs univs dfs).map (fun x => x.2) =
      (dfs.map fun x => x.2).map fun ab =>
        (natToD0Expr univs ab.1, natToD0Expr univs ab.2) := by
  simp [natToD0Dfs, List.map_map, Function.comp_def]

noncomputable def natAction_to_d0 (univs : Nat)
    {Gamma : List (@SExpr (natParams univs))} {p : Pattern}
    {r : p.RHS × p.Check} {e A : @SExpr (natParams univs)}
    {m₁ : List (@SLevel (natParams univs))}
    {m₂ : p.Path → @SExpr (natParams univs)}
    (H : @Pattern.Action (natParams univs) Gamma p r e m₁ m₂ A) :
    @Pattern.Action (d0Params univs)
      (Gamma.map (natToD0Expr univs)) p r
      (natToD0Expr univs e) (m₁.map (natToD0Level univs))
      (fun path => natToD0Expr univs (m₂ path))
      (natToD0Expr univs A) := by
  rcases H with ⟨hpat, hmatched, dfs, hdefeqs, hchecked, hsound⟩
  change NatPat p r at hpat
  refine @Pattern.Action.mk (d0Params univs)
    (Gamma := Gamma.map (natToD0Expr univs)) (p := p) (r := r)
    (e := natToD0Expr univs e)
    (m1 := m₁.map (natToD0Level univs))
    (m2 := fun path => natToD0Expr univs (m₂ path))
    (A := natToD0Expr univs A) (.iota hpat)
    (natMatchesS_to_d0 univs hmatched) (natToD0Dfs univs dfs) ?_ ?_ ?_
  · rw [natToD0Dfs_map_snd, hdefeqs]
    exact natToD0_defeqsS univs r.2 m₁ m₂
  · intro a b B hmem
    simp only [natToD0Dfs, List.mem_map] at hmem
    obtain ⟨⟨B₀, a₀, b₀⟩, hmem₀, heq⟩ := hmem
    cases heq
    exact natIsDefEq_to_d0 univs (hchecked a₀ b₀ B₀ hmem₀)
  · simpa only [natToD0Expr_rhs_applyS] using
      natIsDefEq_to_d0 univs hsound

theorem d0Pat_at_old_const_false {c : Name} {ci : VConstant}
    (hreg : natFinalEnv.constants c = some ci)
    {r : (Pattern.const c).RHS × (Pattern.const c).Check}
    (H : D0Pat (.const c) r) : False := by
  cases H with
  | iota H =>
    rcases natPat_pattern H with h | h <;> cases h
  | defn =>
    rw [d0Def_fresh] at hreg
    cases hreg

/-- Transport a D0a evidence-rich derivation into the definition-extended
D0b syntax and registry. -/
noncomputable def natStrongToD0 (univs : Nat)
    {Gamma : List (@SExpr (natParams univs))}
    {e₁ e₂ A : @SExpr (natParams univs)}
    (H : @IsDefEqStrong (natParams univs) Gamma e₁ e₂ A) :
    @IsDefEqStrong (d0Params univs) (Gamma.map (natToD0Expr univs))
      (natToD0Expr univs e₁) (natToD0Expr univs e₂)
      (natToD0Expr univs A) := by
  letI : Params := d0Params univs
  induction H with
  | bvar h _ ihA => exact .bvar (natLookup_to_d0 univs h) ihA
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | @sort Gamma l =>
    simpa only [natToD0Expr_sort, natToD0Level_succ] using
      (IsDefEqStrong.sort : IsDefEqStrong
        (Gamma.map (natToD0Expr univs))
        (.sort (natToD0Level univs l)) (.sort (natToD0Level univs l))
        (.sort (.succ (natToD0Level univs l))))
  | @const c ci Gamma ls u hreg hlen hTy F hF hDef
      ihTy ihF ihDef =>
    let F' : ∀ cl : CtorBundle.IsCtor c, CtorBundle c cl := fun cl =>
      natCtorBundleToD0 univs cl (F (d0CtorToNat univs cl))
    simpa only [natToD0Expr_const, natToD0Expr_mkInst] using
      (@IsDefEqStrong.const (d0Params univs) c ci
      (Gamma.map (natToD0Expr univs))
      (ls.map (natToD0Level univs)) (natToD0Level univs u)
      (natFinalEnv_le_d0Env.constants hreg)
      (by simpa only [List.length_map] using hlen) (by
        simpa only [natToD0Expr_mkInst, natToD0Expr_sort] using ihTy)
      F' (by
        intro cl
        dsimp only [F']
        rw [← natCtorBundleToD0_rhs, natCtorBundleToD0_u]
        have H := ihF (d0CtorToNat univs cl)
        simp only [natToD0Expr_mkInst, natToD0Expr_sort] at H
        exact H) (by
        intro r hpat
        exact (d0Pat_at_old_const_false hreg hpat).elim))
  | appDF _ _ _ _ _ ihA ihCod ihf iha ihResult =>
    rw [natToD0Expr_inst, natToD0Expr_inst, natToD0Expr_sort] at ihResult
    simpa only [List.map_cons, natToD0Expr_app, natToD0Expr_forallE,
      natToD0Expr_inst] using
      IsDefEqStrong.appDF ihA ihCod ihf iha ihResult
  | lamDF _ _ _ _ _ ihA ihB ihB' ihBody ihBody' =>
    simpa only [List.map_cons, natToD0Expr_lam, natToD0Expr_forallE] using
      IsDefEqStrong.lamDF ihA ihB ihB' ihBody ihBody'
  | forallEDF _ _ _ ihA ihBody ihBody' =>
    simpa only [List.map_cons, natToD0Expr_forallE, natToD0Expr_sort,
      natToD0Level_imax] using
      IsDefEqStrong.forallEDF ihA ihBody ihBody'
  | defeqDF _ _ ihA ihe => exact .defeqDF ihA ihe
  | beta _ _ _ _ ihBody ihArg ihApp ihInst =>
    simp only [natToD0Expr_app, natToD0Expr_lam,
      natToD0Expr_inst] at ihApp
    simp only [natToD0Expr_inst] at ihInst
    simpa only [List.map_cons, natToD0Expr_app, natToD0Expr_lam,
      natToD0Expr_inst] using
      IsDefEqStrong.beta ihBody ihArg ihApp ihInst
  | @eta Gamma e A B _ _ ihTerm ihLam =>
    rw [natToD0Expr_lam, natToD0Expr_app, natToD0Expr_lift',
      natToD0Expr_bvar, natToD0Expr_forallE] at ihLam ⊢
    exact IsDefEqStrong.eta ihTerm ihLam
  | proofIrrel _ _ _ ihp ihh ihh' => exact .proofIrrel ihp ihh ihh'
  | @defn c ci Gamma ls u r hreg hlen hTy F hF action hRhs
      ihTy ihF ihRhs =>
    have hpat : NatPat (.const c) r := by
      change (natParams univs).Pat (.const c) r
      exact @Pattern.Action.pat (natParams univs) Gamma (.const c) r
        (@SExpr.const (natParams univs) c ls) ls Empty.elim
        (@SExpr.mkInst (natParams univs) ls ci.type) action
    rcases natPat_pattern hpat with h | h <;> cases h
  | extra action _ _ ihLeft ihRight =>
    rw [natToD0Expr_rhs_applyS] at ihRight
    simpa only [natToD0Expr_rhs_applyS] using
      IsDefEqStrong.extra (natAction_to_d0 univs action) ihLeft ihRight

section SemanticCertificates

/-- The Nat environment has no structure-eta registry entries, so its weak
reflection bridge is vacuous. -/
theorem natStructureEtaSound (univs : Nat) :
    @Params.StructureEtaSound (natParams univs) := by
  letI : Params := natParams univs
  intro rule levels Gamma params major hreg
  exact (natFinalEnv_no_structEta rule hreg).elim

/-- Raw type uniqueness for the concrete Nat bridge.  The semantic syntax
is reflected into the checked Theory environment, where uniqueness follows
from `nat_env_wf`, then translated back through the level quotient. -/
def NatContextValid (univs : Nat)
    (Gamma : List (@SExpr (natParams univs))) : Prop :=
  letI : Params := natParams univs
  OnCtx (Gamma.map SExpr.reify) (natFinalEnv.IsType univs)

def NatTypesDefEq (univs : Nat) {Gamma : List (@SExpr (natParams univs))}
    (A B : @SExpr (natParams univs)) : Prop :=
  letI : Params := natParams univs
  ∃ u, IsDefEq Gamma A B (.sort u)

theorem natTypeUniq (univs : Nat)
    {Gamma : List (@SExpr (natParams univs))} {x A B : @SExpr (natParams univs)}
    (hGamma : NatContextValid univs Gamma)
    (hxA : @IsDefEq (natParams univs) Gamma x x A)
    (hxB : @IsDefEq (natParams univs) Gamma x x B) :
    NatTypesDefEq (Gamma := Gamma) univs A B := by
  letI : Params := natParams univs
  change OnCtx (Gamma.map SExpr.reify) (natFinalEnv.IsType univs) at hGamma
  change ∃ u, IsDefEq Gamma A B (.sort u)
  have hxA' := hxA.reify hGamma
  have hxB' := hxB.reify hGamma
  obtain ⟨u, hAB⟩ := hxA'.uniq InductiveReplayFixtures.nat_env_wf hGamma hxB'
  have hlevels := (VEnv.CtxStrong.strong natFinalEnv_ordered hGamma).levelWF
  have hAB' := SExpr.IsDefEq.mkS (natStructureEtaSound univs) hAB hlevels
  have hctx : (Gamma.map SExpr.reify).map SExpr.mk = Gamma := by
    rw [List.map_map]
    exact List.map_id''' Gamma fun term _ => SExpr.mk_reify term
  rw [hctx] at hAB'
  refine ⟨SLevel.mk u, ?_⟩
  simpa only [SExpr.mk_reify, SExpr.mk] using hAB'

/-- Type equality in the concrete bridge composes even when its two raw
derivations choose different sort representatives.  The middle type's two
self-typings are aligned by `natTypeUniq` before ordinary homogeneous
transitivity is used. -/
theorem natTypesTrans (univs : Nat)
    {Gamma : List (@SExpr (natParams univs))}
    {A B C : @SExpr (natParams univs)}
    (hGamma : NatContextValid univs Gamma)
    (hAB : NatTypesDefEq (Gamma := Gamma) univs A B)
    (hBC : NatTypesDefEq (Gamma := Gamma) univs B C) :
    NatTypesDefEq (Gamma := Gamma) univs A C := by
  letI : Params := natParams univs
  obtain ⟨u, hAB⟩ := hAB
  obtain ⟨v, hBC⟩ := hBC
  obtain ⟨w, huv⟩ := natTypeUniq univs hGamma hAB.hasType.2 hBC.hasType.1
  exact ⟨u, hAB.trans (huv.symm.defeqDF hBC)⟩

/-- Instantiate a type equality under one binder with a well-typed semantic
argument. -/
theorem natTypesInst (univs : Nat)
    {Gamma : List (@SExpr (natParams univs))}
    {D B B' e : @SExpr (natParams univs)}
    (hBB' : NatTypesDefEq (Gamma := D :: Gamma) univs B B')
    (he : @IsDefEq (natParams univs) Gamma e e D) :
    NatTypesDefEq (Gamma := Gamma) univs
      (@SExpr.inst (natParams univs) B e)
      (@SExpr.inst (natParams univs) B' e) := by
  letI : Params := natParams univs
  obtain ⟨u, hBB'⟩ := hBB'
  have hsubst := hBB'.subst
    (Ctx.Subst.one IsDefEq.weak' IsDefEq.bvar he)
  change IsDefEq Gamma (B.inst e) (B'.inst e) (.sort u) at hsubst
  exact ⟨u, hsubst⟩

/-- Pi injectivity for the concrete semantic syntax.  The raw SExpr
equality is reflected into the checked Nat environment, decomposed there,
and translated back. -/
theorem natForallEInv (univs : Nat)
    {Gamma : List (@SExpr (natParams univs))}
    {A B A' B' : @SExpr (natParams univs)}
    (hGamma : NatContextValid univs Gamma)
    (hPi : NatTypesDefEq (Gamma := Gamma) univs
      (@SExpr.forallE (natParams univs) A B)
      (@SExpr.forallE (natParams univs) A' B')) :
    NatTypesDefEq (Gamma := Gamma) univs A A' ∧
      NatTypesDefEq (Gamma := A :: Gamma) univs B B' := by
  letI : Params := natParams univs
  change OnCtx (Gamma.map SExpr.reify) (natFinalEnv.IsType univs) at hGamma
  obtain ⟨_, hPi⟩ := hPi
  have hPi' := hPi.reify hGamma
  have hPiU : natFinalEnv.IsDefEqU univs (Gamma.map SExpr.reify)
      (.forallE A.reify B.reify) (.forallE A'.reify B'.reify) := by
    exact ⟨_, hPi'⟩
  obtain ⟨⟨u, hA⟩, v, hB⟩ :=
    VEnv.IsDefEqU.forallE_inv InductiveReplayFixtures.nat_env_wf hGamma hPiU
  have hlevels :=
    (VEnv.CtxStrong.strong natFinalEnv_ordered hGamma).levelWF
  have hA' := SExpr.IsDefEq.mkS (natStructureEtaSound univs) hA hlevels
  have hAlevels := (hA.levelWF hlevels).1
  have hB' := SExpr.IsDefEq.mkS (natStructureEtaSound univs) hB
    ⟨hlevels, hAlevels⟩
  have hctx : (Gamma.map SExpr.reify).map SExpr.mk = Gamma := by
    rw [List.map_map]
    exact List.map_id''' Gamma fun term _ => SExpr.mk_reify term
  constructor
  · refine ⟨SLevel.mk u, ?_⟩
    simpa only [hctx, SExpr.mk_reify, SExpr.mk] using hA'
  · refine ⟨SLevel.mk v, ?_⟩
    simpa only [List.map_cons, hctx, SExpr.mk_reify, SExpr.mk] using hB'

/-- One exposed application layer of a conversion-aware spine, aligned with
a concrete Pi type. -/
structure NatSpineConsView (univs : Nat)
    {Gamma : List (@SExpr (natParams univs))}
    (D B e : @SExpr (natParams univs))
    (es : List (@SExpr (natParams univs)))
    (R : @SExpr (natParams univs)) where
  domain : @SExpr (natParams univs)
  codomain : @SExpr (natParams univs)
  domainEq : NatTypesDefEq (Gamma := Gamma) univs D domain
  codomainEq : NatTypesDefEq (Gamma := D :: Gamma) univs B codomain
  argument : @IsDefEq (natParams univs) Gamma e e domain
  tail : @SpineWF (natParams univs) Gamma
    (@SExpr.inst (natParams univs) codomain e) es R

/-- Peel the first argument of a `SpineWF`, commuting past its head and
result conversions.  Pi injectivity supplies the dependent equality needed
to keep the concrete generated telescope aligned with the exposed spine. -/
theorem natSpineConsView_nonempty (univs : Nat)
    {Gamma : List (@SExpr (natParams univs))}
    {D B Head e R : @SExpr (natParams univs)}
    {es : List (@SExpr (natParams univs))}
    (hGamma : NatContextValid univs Gamma)
    (hHead : NatTypesDefEq (Gamma := Gamma) univs
      (@SExpr.forallE (natParams univs) D B) Head)
    (H : @SpineWF (natParams univs) Gamma Head (e :: es) R) :
    Nonempty (NatSpineConsView (Gamma := Gamma) univs D B e es R) := by
  letI : Params := natParams univs
  generalize hargsEq : e :: es = args at H
  induction H generalizing D B e es with
  | nil => cases hargsEq
  | @cons _ domain _ _ codomain harg htail ih =>
    cases hargsEq
    obtain ⟨hdom, hbody⟩ := natForallEInv univs hGamma hHead
    exact ⟨{
      domain := domain
      codomain := codomain
      domainEq := hdom
      codomainEq := hbody
      argument := harg
      tail := htail }⟩
  | @conv _ Head' u _ _ hconv htail ih =>
    exact ih (natTypesTrans univs hGamma hHead ⟨u, hconv⟩) hargsEq
  | @ret _ _ R' _ _ htail hret ih =>
    let ⟨view⟩ := ih hHead hargsEq
    exact ⟨{ view with tail := .ret view.tail hret }⟩

/-- Data-valued first-layer view selected at the proposition-elimination
boundary above. -/
noncomputable def natSpineConsView (univs : Nat)
    {Gamma : List (@SExpr (natParams univs))}
    {D B Head e R : @SExpr (natParams univs)}
    {es : List (@SExpr (natParams univs))}
    (hGamma : NatContextValid univs Gamma)
    (hHead : NatTypesDefEq (Gamma := Gamma) univs
      (@SExpr.forallE (natParams univs) D B) Head)
    (H : @SpineWF (natParams univs) Gamma Head (e :: es) R) :
    NatSpineConsView (Gamma := Gamma) univs D B e es R :=
  Classical.choice (natSpineConsView_nonempty univs hGamma hHead H)

/-- The exposed argument also has the concrete generated domain. -/
theorem NatSpineConsView.argumentExpected (univs : Nat)
    {Gamma : List (@SExpr (natParams univs))}
    {D B e R : @SExpr (natParams univs)}
    {es : List (@SExpr (natParams univs))}
    (view : NatSpineConsView (Gamma := Gamma) univs D B e es R) :
    @IsDefEq (natParams univs) Gamma e e D := by
  letI : Params := natParams univs
  obtain ⟨_, hdom⟩ := view.domainEq
  exact hdom.symm.defeqDF view.argument

/-- Equality between the concrete next telescope layer and the next head
exposed by the caller's spine. -/
theorem NatSpineConsView.restEq (univs : Nat)
    {Gamma : List (@SExpr (natParams univs))}
    {D B e R : @SExpr (natParams univs)}
    {es : List (@SExpr (natParams univs))}
    (view : NatSpineConsView (Gamma := Gamma) univs D B e es R) :
    NatTypesDefEq (Gamma := Gamma) univs
      (@SExpr.inst (natParams univs) B e)
      (@SExpr.inst (natParams univs) view.codomain e) :=
  natTypesInst univs view.codomainEq (view.argumentExpected univs)

/-- Add one capture to a concrete path-indexed spine.  Type uniqueness
aligns the exposed generated domain with the caller-selected shared capture
type, and `PathSpineWF.cons` retains that local domain conversion. -/
theorem natPathSpineCons (univs : Nat)
    {Gamma : List (@SExpr (natParams univs))}
    {D B e R : @SExpr (natParams univs)}
    {es : List (@SExpr (natParams univs))}
    {alpha : Type}
    {value type : alpha → @SExpr (natParams univs)}
    {path : alpha} {paths : List alpha}
    (hGamma : NatContextValid univs Gamma)
    (view : NatSpineConsView (Gamma := Gamma) univs D B e es R)
    (he : e = value path)
    (htyped : @IsDefEq (natParams univs) Gamma
      (value path) (value path) (type path))
    (htail : @PathSpineWF (natParams univs) Gamma alpha value type
      (@SExpr.inst (natParams univs) B e) paths R) :
    @PathSpineWF (natParams univs) Gamma alpha value type
      (@SExpr.forallE (natParams univs) D B) (path :: paths) R := by
  letI : Params := natParams univs
  subst e
  obtain ⟨_, hdom⟩ := view.domainEq
  obtain ⟨_, hshared⟩ :=
    natTypeUniq univs hGamma view.argument htyped
  obtain ⟨_, hconcrete⟩ :=
    natTypesTrans univs hGamma ⟨_, hdom⟩ ⟨_, hshared⟩
  exact .cons hconcrete.symm htail

/-- Recover the path-indexed form of an already typed concrete spine.  The
ordinary spine fixes each generated domain; concrete type uniqueness then
aligns that domain with the independently selected shared capture type.
Head and result conversions are retained verbatim. -/
theorem natPathSpineOfSpineWF (univs : Nat)
    {Gamma : List (@SExpr (natParams univs))}
    {alpha : Type}
    {value type : alpha → @SExpr (natParams univs)}
    {A B : @SExpr (natParams univs)} {paths : List alpha}
    (hGamma : NatContextValid univs Gamma)
    (htyped : ∀ path, @IsDefEq (natParams univs) Gamma
      (value path) (value path) (type path))
    (H : @SpineWF (natParams univs) Gamma A (paths.map value) B) :
    @PathSpineWF (natParams univs) Gamma alpha value type A paths B := by
  letI : Params := natParams univs
  generalize hargs : paths.map value = args at H
  induction H generalizing paths with
  | nil =>
    have hpaths : paths = [] := by simpa using hargs
    subst paths
    exact .nil
  | @cons e domain es result codomain harg htail ih =>
    cases paths with
    | nil => simp at hargs
    | cons path paths =>
      simp only [List.map_cons, List.cons.injEq] at hargs
      obtain ⟨hvalue, hrest⟩ := hargs
      subst e
      obtain ⟨_, hdomain⟩ :=
        natTypeUniq univs hGamma (htyped path) harg
      exact .cons hdomain (ih hrest)
  | @conv Head Head' u es result hHead htail ih =>
    exact .conv hHead (ih hargs)
  | @ret Head es result result' u htail hresult ih =>
    exact .ret (ih hargs) hresult

/-- The zero-rule match exposes exactly the three recursor captures. -/
theorem natZeroCaptureValues (univs : Nat)
    {recLs ctorLs : List (@SLevel (natParams univs))}
    {recArgs ctorArgs : List (@SExpr (natParams univs))}
    {mcap : (RecursorIotaPattern ``Nat.rec 3 ``Nat.zero 0).Path →
      @SExpr (natParams univs)}
    (H : @Pattern.MatchesS (natParams univs)
      (RecursorIotaPattern ``Nat.rec 3 ``Nat.zero 0)
      (@SExpr.app (natParams univs)
        (recArgs.foldr
          (fun a f => @SExpr.app (natParams univs) f a)
          (@SExpr.const (natParams univs) ``Nat.rec recLs))
        (ctorArgs.foldr
          (fun a f => @SExpr.app (natParams univs) f a)
          (@SExpr.const (natParams univs) ``Nat.zero ctorLs))) recLs mcap) :
    recArgs.length = 3 ∧ ctorArgs = [] ∧
      (natCapturePaths NatGeneration.flatCtors[0]).map mcap =
        recArgs.reverse := by
  letI : Params := natParams univs
  cases H with
  | @app fPat recHead recLevels recCap ctorPat ctorHead ctorLevels ctorCap
      hrec hctor =>
    obtain ⟨-, hrecLen, hrecValues⟩ := matchesS_varN_foldr hrec
    obtain ⟨-, hctorLen, -⟩ := matchesS_varN_foldr hctor
    have hctorArgs : ctorArgs = [] := List.length_eq_zero_iff.mp hctorLen
    subst ctorArgs
    refine ⟨hrecLen, rfl, ?_⟩
    rw [natZeroCapturePaths]
    change
      ((Pattern.varNPaths (.const ``Nat.rec) 3).map Sum.inl).map
          (Sum.elim recCap ctorCap) = recArgs.reverse
    simpa [List.map_map, Function.comp_def] using hrecValues

/-- The successor-rule match exposes the three recursor captures followed
by its one constructor field. -/
theorem natSuccCaptureValues (univs : Nat)
    {recLs ctorLs : List (@SLevel (natParams univs))}
    {recArgs ctorArgs : List (@SExpr (natParams univs))}
    {mcap : (RecursorIotaPattern ``Nat.rec 3 ``Nat.succ 1).Path →
      @SExpr (natParams univs)}
    (H : @Pattern.MatchesS (natParams univs)
      (RecursorIotaPattern ``Nat.rec 3 ``Nat.succ 1)
      (@SExpr.app (natParams univs)
        (recArgs.foldr
          (fun a f => @SExpr.app (natParams univs) f a)
          (@SExpr.const (natParams univs) ``Nat.rec recLs))
        (ctorArgs.foldr
          (fun a f => @SExpr.app (natParams univs) f a)
          (@SExpr.const (natParams univs) ``Nat.succ ctorLs))) recLs mcap) :
    recArgs.length = 3 ∧ ctorArgs.length = 1 ∧
      (natCapturePaths NatGeneration.flatCtors[1]).map mcap =
        recArgs.reverse ++ ctorArgs.reverse := by
  letI : Params := natParams univs
  cases H with
  | @app fPat recHead recLevels recCap ctorPat ctorHead ctorLevels ctorCap
      hrec hctor =>
    obtain ⟨-, hrecLen, hrecValues⟩ := matchesS_varN_foldr hrec
    obtain ⟨-, hctorLen, hctorValues⟩ := matchesS_varN_foldr hctor
    refine ⟨hrecLen, hctorLen, ?_⟩
    rw [natSuccCapturePaths]
    change
      (((Pattern.varNPaths (.const ``Nat.rec) 3).map Sum.inl ++
          (Pattern.varNPaths (.const ``Nat.succ) 1).map Sum.inr).map
        (Sum.elim recCap ctorCap)) = recArgs.reverse ++ ctorArgs.reverse
    simpa [List.map_append, List.map_map, Function.comp_def,
      hrecValues, hctorValues]

theorem natPat_no_const (univs : Nat) {c : Name}
    {r : (Pattern.const c).RHS × (Pattern.const c).Check}
    (H : (natParams univs).Pat (.const c) r) : False := by
  change NatPat (.const c) r at H
  rcases natPat_pattern H with h | h <;> cases h

theorem natType_not_ctor (univs : Nat)
    (cl : @CtorBundle.IsCtor (natParams univs) ``Nat) : False := by
  letI : Params := natParams univs
  have hshape : ctorLike cl.cl.1 = true := by
    have hs := cl.cl.2.2
    cases hc : cl.cl.1 <;> simp [ctorLike, hc] at hs ⊢
  rcases natClassify_ctor_cases cl.cl.2.1 hshape with h | h
  · simp at h
  · simp at h

/-- The instance-scoped proposition asserting strong self-typing of the Nat
family head.  Packaging the proposition behind a `letI` keeps the ambient
universe valuation explicit without leaking an unresolved `Params` argument
through `SExpr` and `SLevel` in the theorem signature. -/
def NatTypeStrong (univs : Nat) (Gamma : List (@SExpr (natParams univs))) : Prop :=
  letI : Params := natParams univs
  IsDefEqStrong Gamma (.const ``Nat []) (.const ``Nat [])
    (SExpr.mkInst [] InductiveFixtures.natType.type)

/-- Strong self-typing of the inductive family head, shared by both Nat
constructor bundles. -/
theorem natTypeStrong (univs : Nat)
    (Gamma : List (@SExpr (natParams univs))) : NatTypeStrong univs Gamma := by
  letI : Params := natParams univs
  change IsDefEqStrong Gamma (.const ``Nat []) (.const ``Nat [])
    (SExpr.mkInst [] InductiveFixtures.natType.type)
  refine IsDefEqStrong.const
    (ci := InductiveFixtures.natType.toVConstant) (ls := [])
    (u := SLevel.succ (SLevel.succ SLevel.zero))
    InductiveReplayFixtures.nat_type_env_lookup rfl ?_ ?_ ?_ ?_
  · change IsDefEqStrong Gamma
      (.sort (SLevel.succ SLevel.zero))
      (.sort (SLevel.succ SLevel.zero))
      (.sort (SLevel.succ (SLevel.succ SLevel.zero)))
    exact .sort
  · intro cl
    exact (natType_not_ctor univs cl).elim
  · intro cl
    exact (natType_not_ctor univs cl).elim
  · intro r hpat
    exact (natPat_no_const univs hpat).elim

/-- The result type of the constructor half of the semantic bridge, with the
`Params` instance scoped inside the definition for stable elaboration. -/
def NatCtorResult (univs : Nat) {c : Name} {ci : VConstant}
    (ls : List (@SLevel (natParams univs)))
    (Gamma : List (@SExpr (natParams univs)))
    (cl : @CtorBundle.IsCtor (natParams univs) c) : Type :=
  letI : Params := natParams univs
  {F : CtorBundle c cl //
    IsDefEqStrong Gamma (SExpr.mkInst ls ci.type) (F.rhs ls) (.sort F.u)}

/-- The Nat classifier exposes exactly the zero and successor constructor
bundles.  This proposition-valued existence theorem is the safe elimination
boundary for the classifier proof. -/
theorem natCtor_nonempty (univs : Nat) {c : Name} {ci : VConstant}
    {ls : List (@SLevel (natParams univs))}
    {Gamma : List (@SExpr (natParams univs))}
    (hci : natFinalEnv.constants c = some ci)
    (hlen : ls.length = ci.uvars)
    (cl : @CtorBundle.IsCtor (natParams univs) c) :
    Nonempty (NatCtorResult (ci := ci) univs ls Gamma cl) := by
  letI : Params := natParams univs
  have hshape : ctorLike cl.cl.1 = true := by
    have hs := cl.cl.2.2
    cases hc : cl.cl.1 <;> simp [ctorLike, hc] at hs ⊢
  have hcases := natClassify_ctor_cases cl.cl.2.1 hshape
  unfold NatCtorResult
  rcases hcases with hzero | hsucc
  · obtain ⟨rfl, hcl⟩ := hzero
    change some InductiveFixtures.natType.ctors[0].toVConstant = some ci at hci
    have hci' : ci = InductiveFixtures.natType.ctors[0].toVConstant :=
      Option.some.inj hci.symm
    subst ci
    have hls : ls = [] := List.length_eq_zero_iff.mp hlen
    subst ls
    let F : CtorBundle ``Nat.zero cl := {
      I := ``Nat
      Ts := []
      args := []
      u := SLevel.succ SLevel.zero
      hlen := by simp [hcl, Classification.arity]
      hclI := by
        change natClassify ``Nat = some (.indTy 0)
        simp [natClassify]
      hu0 := by
        intro h
        have hv := congrArg (fun l : SLevel => l.1 []) h
        simp [SLevel.succ, SLevel.zero] at hv }
    refine ⟨⟨F, ?_⟩⟩
    change IsDefEqStrong Gamma (.const ``Nat []) (.const ``Nat [])
      (SExpr.mkInst [] InductiveFixtures.natType.type)
    exact natTypeStrong univs Gamma
  · obtain ⟨rfl, hcl⟩ := hsucc
    change some InductiveFixtures.natType.ctors[1].toVConstant = some ci at hci
    have hci' : ci = InductiveFixtures.natType.ctors[1].toVConstant :=
      Option.some.inj hci.symm
    subst ci
    have hls : ls = [] := List.length_eq_zero_iff.mp hlen
    subst ls
    let one : SLevel := SLevel.succ SLevel.zero
    let F : CtorBundle ``Nat.succ cl := {
      I := ``Nat
      Ts := [.const ``Nat []]
      args := []
      u := SLevel.imax one one
      hlen := by simp [hcl, Classification.arity]
      hclI := by
        change natClassify ``Nat = some (.indTy 0)
        simp [natClassify]
      hu0 := by
        intro h
        have hv := congrArg (fun l : SLevel => l.1 []) h
        simp [SLevel.imax, one, SLevel.succ, SLevel.zero,
          Lean.Nat.imax] at hv }
    refine ⟨⟨F, ?_⟩⟩
    change IsDefEqStrong Gamma
      (.forallE (.const ``Nat []) (.const ``Nat []))
      (.forallE (.const ``Nat []) (.const ``Nat []))
      (.sort (SLevel.imax one one))
    exact IsDefEqStrong.forallEDF
      (natTypeStrong univs Gamma)
      (natTypeStrong univs (.const ``Nat [] :: Gamma))
      (natTypeStrong univs (.const ``Nat [] :: Gamma))

/-- The data-valued constructor bridge selected from `natCtor_nonempty`. -/
noncomputable def natCtor (univs : Nat) {c : Name} {ci : VConstant}
    {ls : List (@SLevel (natParams univs))}
    {Gamma : List (@SExpr (natParams univs))}
    (hci : natFinalEnv.constants c = some ci)
    (hlen : ls.length = ci.uvars)
    (cl : @CtorBundle.IsCtor (natParams univs) c) :
    NatCtorResult (ci := ci) univs ls Gamma cl :=
  Classical.choice (natCtor_nonempty univs hci hlen cl)

/-! ### Concrete normal forms used by the Nat iota-site certificate -/

def probeNatZeroRuleTypeV : VExpr :=
  VExpr.forallE
    (VExpr.forallE (VExpr.const ``Nat []) (VExpr.sort (VLevel.param 0)))
    (VExpr.forallE
      ((VExpr.bvar 0).app (VExpr.const ``Nat.zero []))
      (VExpr.forallE
        (VExpr.forallE (VExpr.const ``Nat [])
          (VExpr.forallE
            ((VExpr.bvar 2).app (VExpr.bvar 0))
            ((VExpr.bvar 3).app
              ((VExpr.const ``Nat.succ []).app (VExpr.bvar 1)))))
        ((VExpr.bvar 2).app (VExpr.const ``Nat.zero []))))

def probeNatRecTypeV : VExpr :=
  VExpr.forallE
    (VExpr.forallE (VExpr.const ``Nat []) (VExpr.sort (VLevel.param 0)))
    (VExpr.forallE
      ((VExpr.bvar 0).app (VExpr.const ``Nat.zero []))
      (VExpr.forallE
        (VExpr.forallE (VExpr.const ``Nat [])
          (VExpr.forallE
            ((VExpr.bvar 2).app (VExpr.bvar 0))
            ((VExpr.bvar 3).app
              ((VExpr.const ``Nat.succ []).app (VExpr.bvar 1)))))
        (VExpr.forallE (VExpr.const ``Nat [])
          ((VExpr.bvar 3).app (VExpr.bvar 0)))))

def probeNatRuleBindersV : List VExpr :=
  [VExpr.forallE (VExpr.const ``Nat []) (VExpr.sort (VLevel.param 0)),
   (VExpr.bvar 0).app (VExpr.const ``Nat.zero []),
   VExpr.forallE (VExpr.const ``Nat [])
     (VExpr.forallE
       ((VExpr.bvar 2).app (VExpr.bvar 0))
       ((VExpr.bvar 3).app
         ((VExpr.const ``Nat.succ []).app (VExpr.bvar 1))))]

def probeNatZeroRuleResultV : VExpr :=
  (VExpr.bvar 2).app (VExpr.const ``Nat.zero [])

def probeNatZeroRuleLhsBodyV : VExpr :=
  ((((VExpr.const ``Nat.rec [VLevel.param 0]).app (VExpr.bvar 2)).app
    (VExpr.bvar 1)).app (VExpr.bvar 0)).app (VExpr.const ``Nat.zero [])

def probeNatZeroRuleLhsV : VExpr :=
  VExpr.lamN probeNatRuleBindersV probeNatZeroRuleLhsBodyV

def probeNatSuccRuleBindersV : List VExpr :=
  probeNatRuleBindersV ++ [VExpr.const ``Nat []]

def probeNatSuccRuleResultV : VExpr :=
  (VExpr.bvar 3).app
    ((VExpr.const ``Nat.succ []).app (VExpr.bvar 0))

def probeNatSuccRuleTypeV : VExpr :=
  VExpr.forallN probeNatSuccRuleBindersV probeNatSuccRuleResultV

def probeNatSuccRuleLhsBodyV : VExpr :=
  ((((VExpr.const ``Nat.rec [VLevel.param 0]).app (VExpr.bvar 3)).app
    (VExpr.bvar 2)).app (VExpr.bvar 1)).app
      ((VExpr.const ``Nat.succ []).app (VExpr.bvar 0))

def probeNatSuccRuleLhsV : VExpr :=
  VExpr.lamN probeNatSuccRuleBindersV probeNatSuccRuleLhsBodyV

/-- The generated zero body selects the zero minor after the three common
recursor binders. -/
def probeNatZeroRuleRhsV : VExpr :=
  VExpr.lamN probeNatRuleBindersV (VExpr.bvar 1)

/-- The generated successor body applies its minor to the predecessor and
the recursive recursor call. -/
def probeNatSuccRuleRhsV : VExpr :=
  VExpr.lamN probeNatSuccRuleBindersV <|
    ((VExpr.bvar 1).app (VExpr.bvar 0)).app <|
      ((((VExpr.const ``Nat.rec [VLevel.param 0]).app
        (VExpr.bvar 3)).app (VExpr.bvar 2)).app
        (VExpr.bvar 1)).app (VExpr.bvar 0)

theorem probeNatZeroRuleTypeV_eq :
    (NatGeneration.rule 0 NatGeneration.flatCtors[0]).type =
      probeNatZeroRuleTypeV := by
  native_decide

theorem probeNatRecTypeV_eq :
    (VInductDecl.recConst 0 ``Nat 0 InductiveFixtures.natType).type =
      probeNatRecTypeV := by
  native_decide

theorem probeNatZeroRuleLhsV_eq :
    (NatGeneration.rule 0 NatGeneration.flatCtors[0]).lhs =
      probeNatZeroRuleLhsV := by
  native_decide

theorem probeNatSuccRuleTypeV_eq :
    (NatGeneration.rule 1 NatGeneration.flatCtors[1]).type =
      probeNatSuccRuleTypeV := by
  native_decide

theorem probeNatSuccRuleLhsV_eq :
    (NatGeneration.rule 1 NatGeneration.flatCtors[1]).lhs =
      probeNatSuccRuleLhsV := by
  native_decide

theorem probeNatZeroRuleRhsV_eq :
    (NatGeneration.rule 0 NatGeneration.flatCtors[0]).rhs =
      probeNatZeroRuleRhsV := by
  native_decide

theorem probeNatSuccRuleRhsV_eq :
    (NatGeneration.rule 1 NatGeneration.flatCtors[1]).rhs =
      probeNatSuccRuleRhsV := by
  native_decide

theorem probeNatSuccCtorTypeV_eq :
    InductiveFixtures.natType.ctors[1].type =
      VExpr.forallE (VExpr.const ``Nat []) (VExpr.const ``Nat []) := by
  native_decide

theorem probeNatRuleRhs_ne :
    (NatGeneration.rule 0 NatGeneration.flatCtors[0]).rhs ≠
      (NatGeneration.rule 1 NatGeneration.flatCtors[1]).rhs := by
  native_decide

theorem probeNatFlatCtorZero_lookup :
    NatGeneration.flatCtors[0]? =
      some NatGeneration.flatCtors[0] :=
  List.getElem?_eq_getElem (by decide)

theorem probeNatFlatCtorSucc_lookup :
    NatGeneration.flatCtors[1]? =
      some NatGeneration.flatCtors[1] :=
  List.getElem?_eq_getElem (by decide)

/-- The literal generated zero descriptor used by the guarded RHS spike.
Unlike `natIotaRule`, this value is not selected through pattern uniqueness:
its rule entry, registered equation, closed fixed body, and ordered captures
are definitionally the zero entry of `NatGeneration`. -/
def natZeroDirectIotaRule (univs : Nat) :
    letI : Params := natParams univs
    @Pattern.IotaRule (natParams univs) ``Nat.rec 3 ``Nat.zero 0
      (NatGeneration.ruleRHS natRuleClosure
          probeNatFlatCtorZero_lookup,
        NatGeneration.ruleCheck natRuleClosure
          (List.mem_of_getElem? probeNatFlatCtorZero_lookup)) := by
  letI : Params := natParams univs
  exact {
    pat := .mk probeNatFlatCtorZero_lookup
    df := NatGeneration.rule 0 NatGeneration.flatCtors[0]
    registered := natRule_registered probeNatFlatCtorZero_lookup
    rhsClosed := natRuleClosure.rhs_closed probeNatFlatCtorZero_lookup
    capturePaths := natCapturePaths NatGeneration.flatCtors[0]
    rhsTower := natRuleRHS_tower probeNatFlatCtorZero_lookup }

/-- The literal zero descriptor exposes exactly the three recursor-prefix
captures, in generated application order. -/
theorem natZeroDirectIotaRule_capturePaths (univs : Nat) :
    letI : Params := natParams univs
    (natZeroDirectIotaRule univs).capturePaths =
      [natZeroMotivePath, natZeroMinorPath, natZeroSuccMinorPath] := by
  letI : Params := natParams univs
  rfl

/-- The literal generated successor descriptor, retaining the fourth
constructor-field capture after the three common recursor captures. -/
def natSuccDirectIotaRule (univs : Nat) :
    letI : Params := natParams univs
    @Pattern.IotaRule (natParams univs) ``Nat.rec 3 ``Nat.succ 1
      (NatGeneration.ruleRHS natRuleClosure
          probeNatFlatCtorSucc_lookup,
        NatGeneration.ruleCheck natRuleClosure
          (List.mem_of_getElem? probeNatFlatCtorSucc_lookup)) := by
  letI : Params := natParams univs
  exact {
    pat := .mk probeNatFlatCtorSucc_lookup
    df := NatGeneration.rule 1 NatGeneration.flatCtors[1]
    registered := natRule_registered probeNatFlatCtorSucc_lookup
    rhsClosed := natRuleClosure.rhs_closed probeNatFlatCtorSucc_lookup
    capturePaths := natCapturePaths NatGeneration.flatCtors[1]
    rhsTower := natRuleRHS_tower probeNatFlatCtorSucc_lookup }

/-- The literal successor descriptor exposes the common recursor prefix and
then its unique predecessor field. -/
theorem natSuccDirectIotaRule_capturePaths (univs : Nat) :
    letI : Params := natParams univs
    (natSuccDirectIotaRule univs).capturePaths =
      [natSuccMotivePath, natSuccZeroMinorPath,
        natSuccMinorPath, natSuccPredPath] := by
  letI : Params := natParams univs
  rfl

/-- Proof-relevant exhaustive view of the generated Nat iota inventory.

Eliminating this view substitutes the recursor name, major arity,
constructor name, constructor arity, and registered RHS/check pair together.
It is the dependency-safe case split used by the guarded native leaf: no
later consumer has to repeat the generated-entry recovery or manipulate a
heterogeneous equality between rule indices. -/
inductive NatDirectIotaView (univs : Nat) :
    {rec : Name} → {major : Nat} → {ctor : Name} → {arity : Nat} →
    letI : Params := natParams univs
    (r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check) → Prop where
  | zero : NatDirectIotaView univs
      (rec := ``Nat.rec) (major := 3) (ctor := ``Nat.zero) (arity := 0)
      (NatGeneration.ruleRHS natRuleClosure probeNatFlatCtorZero_lookup,
        NatGeneration.ruleCheck natRuleClosure
          (List.mem_of_getElem? probeNatFlatCtorZero_lookup))
  | succ : NatDirectIotaView univs
      (rec := ``Nat.rec) (major := 3) (ctor := ``Nat.succ) (arity := 1)
      (NatGeneration.ruleRHS natRuleClosure probeNatFlatCtorSucc_lookup,
        NatGeneration.ruleCheck natRuleClosure
          (List.mem_of_getElem? probeNatFlatCtorSucc_lookup))

/-- Recover the exact zero/successor entry selected by any Nat iota pattern.
The result is an indexed inductive rather than a disjunction, so an ordinary
case split performs every dependent substitution needed by the leaf. -/
theorem NatDirectIotaView.of_pat (univs : Nat)
    {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : letI : Params := natParams univs
      (RecursorIotaPattern rec major ctor arity).RHS ×
        (RecursorIotaPattern rec major ctor arity).Check}
    (H : letI : Params := natParams univs
      Params.Pat (RecursorIotaPattern rec major ctor arity) r) :
    NatDirectIotaView univs r := by
  letI : Params := natParams univs
  change NatPat (RecursorIotaPattern rec major ctor arity) r at H
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
  have hr' : r = rgen := eq_of_heq hr
  subst r
  have hi : i = 0 ∨ i = 1 := by
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hentry
    have : NatGeneration.flatCtors.length = 2 := rfl
    omega
  rcases hi with rfl | rfl
  · have hc := Option.some.inj
      (probeNatFlatCtorZero_lookup.symm.trans hentry)
    subst constructor
    exact .zero
  · have hc := Option.some.inj
      (probeNatFlatCtorSucc_lookup.symm.trans hentry)
    subst constructor
    exact .succ

/--
info: 'Lean4Lean.SExpr.ParamsD0.NatDirectIotaView.of_pat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms NatDirectIotaView.of_pat

/-- Expose the registered `Nat.rec` application trace in the literal order
used by the evaluator.  The semantic `varN` match fixes the recursor prefix
at three arguments, while the trace itself synchronizes both syntax rows
with those three shapes.  The continuation consequently receives, newest
first, the constructor major, successor minor, zero minor, and motive layers
from one registered Pi decomposition. -/
theorem natRegisteredRecursorTrace_fourViewElim
    (univs : Nat) [semantic : @Params.Semantic (natParams univs)] :
    letI : Params := natParams univs
    ∀ {n outLevel : Nat} {Γ : List SExpr} {ρ : Valuation}
      {headType : SExpr} {ctor : Name} {ctorShapes : List (WShape n)}
      {recShapes : List (WShape (n + 1))}
      {mrec : (Pattern.varN (.const ``Nat.rec) 3).Path → TShape}
      {majorX majorY : SExpr} {recXs recYs : List SExpr}
      {A : SExpr} {outTy : WShape outLevel},
    LE_Interp.Matches (n := n + 1)
      (Pattern.varN (.const ``Nat.rec) 3) ``Nat.rec recShapes mrec →
    (H : LR.DirectRegisteredTypeTrace Γ ρ headType
      (majorX :: recXs) (majorY :: recYs)
      ((.ctor' ctor ctorShapes.reverse) :: recShapes) A outTy) →
    ∀ {C : Prop},
      (∀ (succX zeroX motiveX succY zeroY motiveY : SExpr)
          (succShape zeroShape motiveShape : WShape (n + 1)),
        ∀ H' : LR.DirectRegisteredTypeTrace Γ ρ headType
          [majorX, succX, zeroX, motiveX]
          [majorY, succY, zeroY, motiveY]
          [(.ctor' ctor ctorShapes.reverse),
            succShape, zeroShape, motiveShape] A outTy,
          ∀ view : LR.DirectRegisteredTypeTrace.FourView H',
          LR.DirectCaptureDefEqAligned.AtShapes (LRD Γ)
            (mrec none) succX succY view.third.domainExpr
            succShape (view.third.domain.lift (n + 1)) →
          LR.DirectCaptureDefEqAligned.AtShapes (LRD Γ)
            (mrec (some none)) zeroX zeroY view.second.domainExpr
            zeroShape (view.second.domain.lift (n + 1)) →
          LR.DirectCaptureDefEqAligned.AtShapes (LRD Γ)
            (mrec (some (some none))) motiveX motiveY
            view.first.domainExpr motiveShape
            (view.first.domain.lift (n + 1)) → C) → C := by
  letI : Params := natParams univs
  letI : Params.Semantic := semantic
  intro n outLevel Γ ρ headType ctor ctorShapes recShapes mrec
    majorX majorY recXs recYs A outTy hmatch H C K
  have hrecShapes : recShapes.length = 3 := hmatch.varN_length
  obtain ⟨succShape, zeroShape, motiveShape, rfl⟩ :
      ∃ succShape zeroShape motiveShape,
        recShapes = [succShape, zeroShape, motiveShape] :=
    ⟨recShapes[0], recShapes[1], recShapes[2],
      List.eq_getElem_of_length_eq_three recShapes hrecShapes⟩
  have hlens := H.directArgs.lengths
  have hrecXs : recXs.length = 3 := Nat.succ.inj hlens.1
  have hrecYs : recYs.length = 3 := Nat.succ.inj hlens.2
  obtain ⟨succX, zeroX, motiveX, rfl⟩ :
      ∃ succX zeroX motiveX, recXs = [succX, zeroX, motiveX] :=
    ⟨recXs[0], recXs[1], recXs[2],
      List.eq_getElem_of_length_eq_three recXs hrecXs⟩
  obtain ⟨succY, zeroY, motiveY, rfl⟩ :
      ∃ succY zeroY motiveY, recYs = [succY, zeroY, motiveY] :=
    ⟨recYs[0], recYs[1], recYs[2],
      List.eq_getElem_of_length_eq_three recYs hrecYs⟩
  have hsucc : mrec none = succShape.T := by
    cases hmatch with
    | var _ => rfl
  have hzero : mrec (some none) = zeroShape.T := by
    cases hmatch with
    | var hmatch =>
      cases hmatch with
      | var _ => rfl
  have hmotive : mrec (some (some none)) = motiveShape.T := by
    cases hmatch with
    | var hmatch =>
      cases hmatch with
      | var hmatch =>
        cases hmatch with
        | var _ => rfl
  let view := H.fourView
  exact K succX zeroX motiveX succY zeroY motiveY
    succShape zeroShape motiveShape H view
    (view.third.captureAtShapes (hsucc ▸ TShape.LE.rfl))
    (view.second.captureAtShapes (hzero ▸ TShape.LE.rfl))
    (view.first.captureAtShapes (hmotive ▸ TShape.LE.rfl))

/--
info: 'Lean4Lean.SExpr.ParamsD0.natRegisteredRecursorTrace_fourViewElim' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms natRegisteredRecursorTrace_fourViewElim

/-- Exact registered major-link obligation for the generated zero entry.
All heterogeneous registry indices have already been substituted; the branch
retains only its semantic matches, direct leaf, and registered application
trace. -/
def NatZeroRegisteredIotaMajorLinkStepAt
    (univs : Nat) (Γ : List (@SExpr (natParams univs)))
    (ρ : @Valuation (natParams univs))
    (headType : @SExpr (natParams univs)) (siteLevel : Nat)
    (level : @SLevel (natParams univs))
    (R : @TShape (natParams univs) → @SExpr (natParams univs) → Prop) :
    Prop := by
  letI : Params := natParams univs
  exact ∀ {n : Nat}
      {recShapes : List (WShape (n + 1))}
      {ctorShapes : List (WShape n)}
      {mrec : (Pattern.varN (.const ``Nat.rec) 3).Path → TShape}
      {mctor : (Pattern.varN (.const ``Nat.zero) 0).Path → TShape}
      {majorX majorY : SExpr} {recXs recYs : List SExpr}
      {A : SExpr} {out outTy : WShape (n + 1)},
    siteLevel = n + 1 →
    Ctx.WF Γ →
    LE_Interp.Matches (n := n + 1)
      (Pattern.varN (.const ``Nat.rec) 3) ``Nat.rec recShapes mrec →
    LE_Interp.Matches (n := n)
      (Pattern.varN (.const ``Nat.zero) 0) ``Nat.zero ctorShapes mctor →
    LE_Interp.RHS [level] (Sum.elim mrec mctor) R out.T
      (NatGeneration.ruleRHS natRuleClosure
        probeNatFlatCtorZero_lookup) →
    (hleaf : LR.DirectPatternLeafSpine Γ (LRD Γ) headType
      (majorX :: recXs) (majorY :: recYs)
      ((.ctor' ``Nat.zero ctorShapes.reverse) :: recShapes)
      A out outTy) →
    LR.DirectRegisteredTypeTrace Γ ρ headType
      (majorX :: recXs) (majorY :: recYs)
      ((.ctor' ``Nat.zero ctorShapes.reverse) :: recShapes)
      A outTy →
    (pair : SExpr.SpineWF.LastPair Γ headType
      recXs recYs majorX majorY A) →
    IsDefEq Γ (.const ``Nat.rec [level]) (.const ``Nat.rec [level])
      headType →
    out.HasType outTy →
    (LRD Γ).TyDefEq A A outTy →
    LR.DirectMajorLinkRectAt Γ
      (.ctor' ``Nat.zero ctorShapes.reverse) pair.domain
      ``Nat.rec [level] recXs recYs majorX A out outTy

/-- Exact registered major-link obligation for the generated successor
entry.  Its constructor match retains the sole predecessor field; no branch
consumer needs to recover the generated descriptor again. -/
def NatSuccRegisteredIotaMajorLinkStepAt
    (univs : Nat) (Γ : List (@SExpr (natParams univs)))
    (ρ : @Valuation (natParams univs))
    (headType : @SExpr (natParams univs)) (siteLevel : Nat)
    (level : @SLevel (natParams univs))
    (R : @TShape (natParams univs) → @SExpr (natParams univs) → Prop) :
    Prop := by
  letI : Params := natParams univs
  exact ∀ {n : Nat}
      {recShapes : List (WShape (n + 1))}
      {ctorShapes : List (WShape n)}
      {mrec : (Pattern.varN (.const ``Nat.rec) 3).Path → TShape}
      {mctor : (Pattern.varN (.const ``Nat.succ) 1).Path → TShape}
      {majorX majorY : SExpr} {recXs recYs : List SExpr}
      {A : SExpr} {out outTy : WShape (n + 1)},
    siteLevel = n + 1 →
    Ctx.WF Γ →
    LE_Interp.Matches (n := n + 1)
      (Pattern.varN (.const ``Nat.rec) 3) ``Nat.rec recShapes mrec →
    LE_Interp.Matches (n := n)
      (Pattern.varN (.const ``Nat.succ) 1) ``Nat.succ ctorShapes mctor →
    LE_Interp.RHS [level] (Sum.elim mrec mctor) R out.T
      (NatGeneration.ruleRHS natRuleClosure
        probeNatFlatCtorSucc_lookup) →
    (hleaf : LR.DirectPatternLeafSpine Γ (LRD Γ) headType
      (majorX :: recXs) (majorY :: recYs)
      ((.ctor' ``Nat.succ ctorShapes.reverse) :: recShapes)
      A out outTy) →
    LR.DirectRegisteredTypeTrace Γ ρ headType
      (majorX :: recXs) (majorY :: recYs)
      ((.ctor' ``Nat.succ ctorShapes.reverse) :: recShapes)
      A outTy →
    (pair : SExpr.SpineWF.LastPair Γ headType
      recXs recYs majorX majorY A) →
    IsDefEq Γ (.const ``Nat.rec [level]) (.const ``Nat.rec [level])
      headType →
    out.HasType outTy →
    (LRD Γ).TyDefEq A A outTy →
    LR.DirectMajorLinkRectAt Γ
      (.ctor' ``Nat.succ ctorShapes.reverse) pair.domain
      ``Nat.rec [level] recXs recYs majorX A out outTy

/-- Canonicalize the registered Nat iota inventory once and delegate the
reached site to its exact zero or successor major-link producer. -/
theorem natRegisteredIotaMajorLinkStepAt_of_branches
    (univs : Nat) [semantic : @Params.Semantic (natParams univs)]
    {Γ : List (@SExpr (natParams univs))}
    {ρ : @Valuation (natParams univs)}
    {headType : @SExpr (natParams univs)} {siteLevel : Nat}
    (level : @SLevel (natParams univs))
    {R : @TShape (natParams univs) → @SExpr (natParams univs) → Prop}
    (zero : NatZeroRegisteredIotaMajorLinkStepAt univs Γ ρ
      headType siteLevel level R)
    (succ : NatSuccRegisteredIotaMajorLinkStepAt univs Γ ρ
      headType siteLevel level R) :
    letI : Params := natParams univs
    LRD.RegisteredIotaMajorLinkStepAt Γ ρ headType siteLevel
      ``Nat.rec [level] R := by
  letI : Params := natParams univs
  letI : Params.Semantic := semantic
  intro n rec ctor major arity recShapes ctorShapes mrec mctor r
    majorX majorY recXs recYs A out outTy hsite hrec hΓ hpat hmf hma
    hrhs hleaf trace pair hhead hout hA
  have view := NatDirectIotaView.of_pat univs hpat
  cases view with
  | zero =>
    intro k J p X Y frame leafExact hXY hbridge
    exact zero hsite hΓ hmf hma hrhs hleaf trace pair hhead hout hA
      frame leafExact hXY hbridge
  | succ =>
    intro k J p X Y frame leafExact hXY hbridge
    exact succ hsite hΓ hmf hma hrhs hleaf trace pair hhead hout hA
      frame leafExact hXY hbridge

/--
info: 'Lean4Lean.SExpr.ParamsD0.natRegisteredIotaMajorLinkStepAt_of_branches' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms natRegisteredIotaMajorLinkStepAt_of_branches

/-- Applying the actual generated zero RHS is its closed fixed body followed
by the motive, zero-minor, and successor-minor captures in that order. -/
theorem natZeroRuleRHS_applyS (univs : Nat)
    (ls : List (@SLevel (natParams univs)))
    (mcap : (RecursorIotaPattern ``Nat.rec 3 ``Nat.zero 0).Path →
      @SExpr (natParams univs)) :
    letI : Params := natParams univs
    (NatGeneration.ruleRHS natRuleClosure
        probeNatFlatCtorZero_lookup).applyS ls mcap =
      (((SExpr.mkInst ls
            (NatGeneration.rule 0 NatGeneration.flatCtors[0]).rhs).app
          (mcap natZeroMotivePath)).app
          (mcap natZeroMinorPath)).app
          (mcap natZeroSuccMinorPath) := by
  letI : Params := natParams univs
  rw [natRuleRHS_tower probeNatFlatCtorZero_lookup]
  rfl

/-- Applying the actual generated successor RHS appends the predecessor
capture after the same three recursor captures. -/
theorem natSuccRuleRHS_applyS (univs : Nat)
    (ls : List (@SLevel (natParams univs)))
    (mcap : (RecursorIotaPattern ``Nat.rec 3 ``Nat.succ 1).Path →
      @SExpr (natParams univs)) :
    letI : Params := natParams univs
    (NatGeneration.ruleRHS natRuleClosure
        probeNatFlatCtorSucc_lookup).applyS ls mcap =
      ((((SExpr.mkInst ls
              (NatGeneration.rule 1 NatGeneration.flatCtors[1]).rhs).app
            (mcap natSuccMotivePath)).app
          (mcap natSuccZeroMinorPath)).app
        (mcap natSuccMinorPath)).app
        (mcap natSuccPredPath) := by
  letI : Params := natParams univs
  rw [natRuleRHS_tower probeNatFlatCtorSucc_lookup]
  rfl

/-- Every recursive descriptor retained by either generated Nat rule points
strictly inside that constructor's emitted field telescope.  This is the
concrete N0 structural-decrease fact; `Nat.succ` contributes the sole
recursive field and `Nat.zero` contributes none. -/
theorem natRule_recursive_lt {i : Nat} {constructor : NormalizedBlockCtor}
    (hentry : NatGeneration.flatCtors[i]? = some constructor) :
    ∀ recursive ∈ constructor.ctor.view.recursive,
      recursive.fieldIndex <
        (constructor.ctor.rawFields InductiveFixtures.natDecl.nparams).length := by
  have hi : i = 0 ∨ i = 1 := by
    obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hentry
    have : NatGeneration.flatCtors.length = 2 := rfl
    omega
  rcases hi with rfl | rfl
  · have hc := Option.some.inj
      (probeNatFlatCtorZero_lookup.symm.trans hentry)
    subst constructor
    decide
  · have hc := Option.some.inj
      (probeNatFlatCtorSucc_lookup.symm.trans hentry)
    subst constructor
    decide

theorem probeNatGeneratedRuleZero_lookup :
    NatGeneration.generatedRules[0]? =
      some (NatGeneration.rule 0 NatGeneration.flatCtors[0]) := by
  native_decide

theorem probeNatGeneratedRuleSucc_lookup :
    NatGeneration.generatedRules[1]? =
      some (NatGeneration.rule 1 NatGeneration.flatCtors[1]) := by
  native_decide

/-- Nat iota descriptors are uniquely determined by their indexed pattern
payload.  Equality of their fixed-headed RHS towers identifies both the
registered RHS and its ordered capture paths; the concrete two-entry
registry then identifies the complete registered equation. -/
theorem natIotaRule_ext (univs : Nat)
    {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : letI : Params := natParams univs
      (RecursorIotaPattern rec major ctor arity).RHS ×
        (RecursorIotaPattern rec major ctor arity).Check}
    (x y : @Pattern.IotaRule (natParams univs)
      rec major ctor arity r) : x = y := by
  letI : Params := natParams univs
  rcases x with ⟨xpat, xdf, xreg, xclosed, xpaths, xtower⟩
  rcases y with ⟨ypat, ydf, yreg, yclosed, ypaths, ytower⟩
  obtain ⟨hrhs, hpaths⟩ := rhsFixedAppN_inj (xtower.symm.trans ytower)
  change natFinalEnv.defeqs xdf at xreg
  change natFinalEnv.defeqs ydf at yreg
  rw [natFinalEnv_defeqs_iff] at xreg yreg
  obtain ⟨ix, hix⟩ := List.mem_iff_getElem?.mp xreg
  obtain ⟨iy, hiy⟩ := List.mem_iff_getElem?.mp yreg
  have hix' : ix = 0 ∨ ix = 1 := by
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hix
    have : NatGeneration.generatedRules.length = 2 := rfl
    omega
  have hiy' : iy = 0 ∨ iy = 1 := by
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hiy
    have : NatGeneration.generatedRules.length = 2 := rfl
    omega
  rcases hix' with rfl | rfl <;> rcases hiy' with rfl | rfl
  all_goals
    first
    | have hxdf := Option.some.inj
        (probeNatGeneratedRuleZero_lookup.symm.trans hix)
    | have hxdf := Option.some.inj
        (probeNatGeneratedRuleSucc_lookup.symm.trans hix)
    first
    | have hydf := Option.some.inj
        (probeNatGeneratedRuleZero_lookup.symm.trans hiy)
    | have hydf := Option.some.inj
        (probeNatGeneratedRuleSucc_lookup.symm.trans hiy)
    subst xdf
    subst ydf
  · subst ypaths
    rfl
  · exact (probeNatRuleRhs_ne hrhs).elim
  · exact (probeNatRuleRhs_ne hrhs.symm).elim
  · subst ypaths
    rfl

instance natIotaRule_subsingleton (univs : Nat)
    {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : letI : Params := natParams univs
      (RecursorIotaPattern rec major ctor arity).RHS ×
        (RecursorIotaPattern rec major ctor arity).Check} :
    Subsingleton (@Pattern.IotaRule (natParams univs)
      rec major ctor arity r) :=
  ⟨natIotaRule_ext univs⟩

/--
info: 'Lean4Lean.SExpr.ParamsD0.natIotaRule_ext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 probeNatGeneratedRuleSucc_lookup._native.native_decide.ax_1_1,
 probeNatGeneratedRuleZero_lookup._native.native_decide.ax_1_1,
 probeNatRuleRhs_ne._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms natIotaRule_ext

/-- Exhaustive eliminator for proof-relevant Nat iota descriptors.  Consumers
provide literal zero and successor cases; descriptor uniqueness transports
those cases to whichever semantic descriptor was selected. -/
theorem natDirectIotaRule_elim (univs : Nat)
    (P : ∀ {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
      {r : letI : Params := natParams univs
        (RecursorIotaPattern rec major ctor arity).RHS ×
          (RecursorIotaPattern rec major ctor arity).Check},
      @Pattern.IotaRule (natParams univs) rec major ctor arity r → Prop)
    (hzero : P (natZeroDirectIotaRule univs))
    (hsucc : P (natSuccDirectIotaRule univs))
    {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : letI : Params := natParams univs
      (RecursorIotaPattern rec major ctor arity).RHS ×
        (RecursorIotaPattern rec major ctor arity).Check}
    (rule : @Pattern.IotaRule (natParams univs)
      rec major ctor arity r) : P rule := by
  letI : Params := natParams univs
  have view := NatDirectIotaView.of_pat univs rule.pat
  cases view with
  | zero =>
    rw [natIotaRule_ext univs rule (natZeroDirectIotaRule univs)]
    exact hzero
  | succ =>
    rw [natIotaRule_ext univs rule (natSuccDirectIotaRule univs)]
    exact hsucc

/--
info: 'Lean4Lean.SExpr.ParamsD0.natDirectIotaRule_elim' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 probeNatGeneratedRuleSucc_lookup._native.native_decide.ax_1_1,
 probeNatGeneratedRuleZero_lookup._native.native_decide.ax_1_1,
 probeNatRuleRhs_ne._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms natDirectIotaRule_elim

theorem probeCancelThreeLifts [Params] (e a b c : SExpr) :
    (((e.lift.lift.lift.subst (Subst.one a).lift.lift).subst
      (Subst.one b).lift).subst (Subst.one c)) = e := by
  rw [SExpr.subst_subst, SExpr.subst_subst]
  rw [SExpr.lift_subst, SExpr.lift_subst, SExpr.lift_subst]
  rw [show ((Subst.one a).lift.lift.comp
      ((Subst.one b).lift.comp (Subst.one c))).tail.tail.tail = Subst.id by
    funext i
    simp [Subst.comp, Subst.tail, Subst.lift, Subst.one,
      Subst.cons, Subst.id, SExpr.subst]]
  exact SExpr.subst_id

theorem probeCancelTwoLifts [Params] (e a b : SExpr) :
    ((e.lift.lift.subst (Subst.one a).lift).subst (Subst.one b)) = e := by
  rw [SExpr.subst_subst]
  rw [SExpr.lift_subst, SExpr.lift_subst]
  rw [show ((Subst.one a).lift.comp (Subst.one b)).tail.tail =
      Subst.id by
    funext i
    simp [Subst.comp, Subst.tail, Subst.lift, Subst.one,
      Subst.cons, Subst.id, SExpr.subst]]
  exact SExpr.subst_id

theorem probeVCancelTwoLifts (e a b : VExpr) :
    ((e.lift.lift.inst a 1).inst b) = e := by
  rw [← VExpr.lift_instN_lo]
  rw [VExpr.inst_lift, VExpr.inst_lift]

theorem probeVCancelThreeLifts (e a b c : VExpr) :
    ((((e.lift.lift.lift).inst a 2).inst b 1).inst c) = e := by
  rw [← VExpr.lift_instN_lo]
  rw [← VExpr.lift_instN_lo]
  rw [probeVCancelTwoLifts, VExpr.inst_lift]

theorem probeInstVParamZero [Params] (level : SLevel) :
    SLevel.instV [level] (VLevel.param 0) = level := by
  apply Subtype.ext
  rfl

theorem probeReifyInstVParamZero [Params] (level : SLevel) :
    VLevel.inst [level.reify] (VLevel.param 0) = level.reify := by
  rfl

theorem probeReifySubstOne [Params] (a : SExpr) :
    (fun i => (Subst.one a i).reify) = VExpr.Subst.one a.reify := by
  funext i
  cases i <;> rfl

theorem probeReifySubstLift [Params] (sigma : Subst) :
    (fun i => (sigma.lift i).reify) =
      VExpr.Subst.lift (fun i => (sigma i).reify) := by
  funext i
  cases i with
  | zero => rfl
  | succ i =>
    simpa only [Subst.lift, VExpr.Subst.lift, VExpr.lift_eq_lift'] using
      SExpr.reify_lift' (sigma i)

def probeSubstLiftN [Params] (sigma : Subst) : Nat → Subst
  | 0 => sigma
  | n + 1 => (probeSubstLiftN sigma n).lift

theorem probeCancelInsertedBinder [Params] (e a : SExpr) : ∀ k,
    (e.lift' (Lift.consN (.skip .refl) k)).subst
      (probeSubstLiftN (Subst.one a) k) = e := by
  induction e with
  | bvar i =>
    intro k
    induction k generalizing i with
    | zero =>
      simp only [Lift.consN, probeSubstLiftN, SExpr.lift', Lift.liftVar,
        SExpr.subst, Subst.one, Subst.cons]
      rfl
    | succ k ih =>
      cases i with
      | zero =>
        simp [probeSubstLiftN, SExpr.subst, Subst.one, Subst.cons,
          Subst.lift]
      | succ i =>
        simpa [probeSubstLiftN, Subst.lift, SExpr.subst, SExpr.lift] using
          congrArg SExpr.lift (ih i)
  | sort | const => intro k; rfl
  | app f a ihf iha =>
    intro k
    simp [SExpr.subst, ihf k, iha k]
  | lam A body ihA ihBody | forallE A body ihA ihBody =>
    intro k
    simp only [SExpr.lift', SExpr.subst]
    rw [ihA k]
    have hbody := ihBody (k + 1)
    change (body.lift' (Lift.consN (.skip .refl) k).cons).subst
      (probeSubstLiftN (Subst.one a) k).lift = body at hbody
    rw [hbody]

theorem probeCancelUnderOne [Params] (e a : SExpr) :
    e.lift.lift.subst (Subst.one a).lift = e.lift := by
  simpa [SExpr.lift, probeSubstLiftN, ← SExpr.lift'_comp] using
    probeCancelInsertedBinder (e := e.lift) a 1

theorem probeCancelUnderTwo [Params] (e a : SExpr) :
    e.lift.lift.lift.subst (Subst.one a).lift.lift = e.lift.lift := by
  simpa [SExpr.lift, probeSubstLiftN, ← SExpr.lift'_comp] using
    probeCancelInsertedBinder (e := e.lift.lift) a 2

theorem probeNatZeroRuleRecName :
    NatGeneration.ruleRecName NatGeneration.flatCtors[0] = ``Nat.rec := by
  native_decide

theorem probeNatZeroCtorName :
    NatGeneration.flatCtors[0].ctor.raw.name = ``Nat.zero := by
  native_decide

theorem probeNatSuccRuleRecName :
    NatGeneration.ruleRecName NatGeneration.flatCtors[1] = ``Nat.rec := by
  native_decide

theorem probeNatSuccCtorName :
    NatGeneration.flatCtors[1].ctor.raw.name = ``Nat.succ := by
  native_decide

def probeNatZeroRuleType (univs : Nat) (level : @SLevel (natParams univs)) :
    @SExpr (natParams univs) :=
  letI : Params := natParams univs
  SExpr.forallE
    (SExpr.forallE (SExpr.const ``Nat []) (SExpr.sort level))
    (SExpr.forallE
      ((SExpr.bvar 0).app (SExpr.const ``Nat.zero []))
      (SExpr.forallE
        (SExpr.forallE (SExpr.const ``Nat [])
          (SExpr.forallE
            ((SExpr.bvar 2).app (SExpr.bvar 0))
            ((SExpr.bvar 3).app
              ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1)))))
        ((SExpr.bvar 2).app (SExpr.const ``Nat.zero []))))

theorem probeNatZeroRuleTypeS_eq (univs : Nat)
    (level : @SLevel (natParams univs)) :
    @SExpr.mkInst (natParams univs) [level]
        (NatGeneration.rule 0 NatGeneration.flatCtors[0]).type =
      probeNatZeroRuleType univs level := by
  rw [probeNatZeroRuleTypeV_eq]
  rfl

def probeNatSuccRuleType (univs : Nat)
    (level : @SLevel (natParams univs)) : @SExpr (natParams univs) :=
  letI : Params := natParams univs
  SExpr.forallE
    (SExpr.forallE (SExpr.const ``Nat []) (SExpr.sort level))
    (SExpr.forallE
      ((SExpr.bvar 0).app (SExpr.const ``Nat.zero []))
      (SExpr.forallE
        (SExpr.forallE (SExpr.const ``Nat [])
          (SExpr.forallE
            ((SExpr.bvar 2).app (SExpr.bvar 0))
            ((SExpr.bvar 3).app
              ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1)))))
        (SExpr.forallE (SExpr.const ``Nat [])
          ((SExpr.bvar 3).app
            ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0))))))

theorem probeNatSuccRuleTypeS_eq (univs : Nat)
    (level : @SLevel (natParams univs)) :
    @SExpr.mkInst (natParams univs) [level]
        (NatGeneration.rule 1 NatGeneration.flatCtors[1]).type =
      probeNatSuccRuleType univs level := by
  rw [probeNatSuccRuleTypeV_eq]
  rfl

def probeNatZeroRuleRhs (univs : Nat)
    (level : @SLevel (natParams univs)) : @SExpr (natParams univs) :=
  letI : Params := natParams univs
  let NatS : SExpr := SExpr.const ``Nat []
  let Motive : SExpr := SExpr.forallE NatS (SExpr.sort level)
  let MinorZero : SExpr :=
    (SExpr.bvar 0).app (SExpr.const ``Nat.zero [])
  let MinorSucc : SExpr :=
    SExpr.forallE NatS <|
      SExpr.forallE ((SExpr.bvar 2).app (SExpr.bvar 0)) <|
        (SExpr.bvar 3).app
          ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))
  SExpr.lam Motive <| SExpr.lam MinorZero <|
    SExpr.lam MinorSucc (SExpr.bvar 1)

def probeNatSuccRuleRhs (univs : Nat)
    (level : @SLevel (natParams univs)) : @SExpr (natParams univs) :=
  letI : Params := natParams univs
  let NatS : SExpr := SExpr.const ``Nat []
  let Motive : SExpr := SExpr.forallE NatS (SExpr.sort level)
  let MinorZero : SExpr :=
    (SExpr.bvar 0).app (SExpr.const ``Nat.zero [])
  let MinorSucc : SExpr :=
    SExpr.forallE NatS <|
      SExpr.forallE ((SExpr.bvar 2).app (SExpr.bvar 0)) <|
        (SExpr.bvar 3).app
          ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))
  SExpr.lam Motive <| SExpr.lam MinorZero <|
    SExpr.lam MinorSucc <| SExpr.lam NatS <|
      ((SExpr.bvar 1).app (SExpr.bvar 0)).app <|
        ((((SExpr.const ``Nat.rec [level]).app
          (SExpr.bvar 3)).app (SExpr.bvar 2)).app
          (SExpr.bvar 1)).app (SExpr.bvar 0)

theorem probeNatZeroRuleRhsS_eq (univs : Nat)
    (level : @SLevel (natParams univs)) :
    @SExpr.mkInst (natParams univs) [level]
        (NatGeneration.rule 0 NatGeneration.flatCtors[0]).rhs =
      probeNatZeroRuleRhs univs level := by
  rw [probeNatZeroRuleRhsV_eq]
  rfl

theorem probeNatSuccRuleRhsS_eq (univs : Nat)
    (level : @SLevel (natParams univs)) :
    @SExpr.mkInst (natParams univs) [level]
        (NatGeneration.rule 1 NatGeneration.flatCtors[1]).rhs =
      probeNatSuccRuleRhs univs level := by
  rw [probeNatSuccRuleRhsV_eq]
  rfl

/-- Every stratified typing of the literal successor RHS spends at least
four lambda layers, the outer minor application, four recursive-recursor
applications, the constant layer, and the four outer Pi layers of the
registered recursor type.

In particular, a local coherent seed at a minimal enclosing constant rung
cannot be treated as though it carried a same-rung successor-RHS typing
certificate; that branch must preserve genuinely all-depth provenance or use
a different structural consumer. -/
theorem probeNatSuccRuleRhs_depth_lower_bound
    (univs : Nat) (level : @SLevel (natParams univs))
    {Γ : List (@SExpr (natParams univs))} {V : @SExpr (natParams univs)}
    {depth : Nat}
    (H : @HasTypeStratifiedS (natParams univs) Γ
      (probeNatSuccRuleRhs univs level) V true depth) :
    14 ≤ depth := by
  letI : Params := natParams univs
  let NatS : SExpr := SExpr.const ``Nat []
  let Motive : SExpr := SExpr.forallE NatS (SExpr.sort level)
  let MinorZero : SExpr :=
    (SExpr.bvar 0).app (SExpr.const ``Nat.zero [])
  let MinorSucc : SExpr :=
    SExpr.forallE NatS <|
      SExpr.forallE ((SExpr.bvar 2).app (SExpr.bvar 0)) <|
        (SExpr.bvar 3).app
          ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))
  change HasTypeStratifiedS Γ
    (.lam Motive (.lam MinorZero (.lam MinorSucc (.lam NatS
      (((SExpr.bvar 1).app (SExpr.bvar 0)).app
        (((((SExpr.const ``Nat.rec [level]).app
          (SExpr.bvar 3)).app (SExpr.bvar 2)).app
          (SExpr.bvar 1)).app (SExpr.bvar 0))))))) V true depth at H
  have p0 := H.lam_depth_pos
  obtain ⟨_, _, _, _, _, H1, _⟩ := H.lam_inv
  have p1 := H1.lam_depth_pos
  obtain ⟨_, _, _, _, _, H2, _⟩ := H1.lam_inv
  have p2 := H2.lam_depth_pos
  obtain ⟨_, _, _, _, _, H3, _⟩ := H2.lam_inv
  have p3 := H3.lam_depth_pos
  obtain ⟨_, _, _, _, _, H4, _⟩ := H3.lam_inv
  have p4 := H4.app_depth_pos
  obtain ⟨_, _, _, _, _, _, _, Hrec, _⟩ := H4.app_inv
  have p5 := Hrec.app_depth_pos
  obtain ⟨_, _, _, _, _, _, Hrec3, _, _⟩ := Hrec.app_inv
  have p6 := Hrec3.app_depth_pos
  obtain ⟨_, _, _, _, _, _, Hrec2, _, _⟩ := Hrec3.app_inv
  have p7 := Hrec2.app_depth_pos
  obtain ⟨_, _, _, _, _, _, Hrec1, _, _⟩ := Hrec2.app_inv
  have p8 := Hrec1.app_depth_pos
  obtain ⟨_, _, _, _, _, _, Hconst, _, _⟩ := Hrec1.app_inv
  have p9 := Hconst.const_depth_pos
  obtain ⟨ci, _, hreg, _, hTy⟩ := Hconst.const_inv
  have hci : ci =
      VInductDecl.recConst 0 ``Nat 0 InductiveFixtures.natType := by
    exact Option.some.inj
      (hreg.symm.trans InductiveReplayFixtures.nat_rec_env_lookup)
  subst ci
  rw [probeNatRecTypeV_eq] at hTy
  change HasTypeStratifiedS _
    (.forallE _ (.forallE _ (.forallE _ (.forallE _ _))))
    _ true _ at hTy
  have p10 := hTy.forallE_depth_pos
  obtain ⟨_, _, _, hTy1⟩ := hTy.forallE_inv
  have p11 := hTy1.forallE_depth_pos
  obtain ⟨_, _, _, hTy2⟩ := hTy1.forallE_inv
  have p12 := hTy2.forallE_depth_pos
  obtain ⟨_, _, _, hTy3⟩ := hTy2.forallE_inv
  have p13 := hTy3.forallE_depth_pos
  omega

/--
info: 'Lean4Lean.SExpr.ParamsD0.probeNatSuccRuleRhs_depth_lower_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 probeNatRecTypeV_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms probeNatSuccRuleRhs_depth_lower_bound

/-- The same lower bound, stated at the literal generated successor
descriptor consumed by the guarded iota leaf.  This keeps the obstruction at
the descriptor boundary: any same-rung certificate for the selected fixed
successor RHS must already have a rung of at least fourteen. -/
theorem natSuccDirectIotaRule_rhs_depth_lower_bound
    (univs : Nat) (level : @SLevel (natParams univs))
    {Γ : List (@SExpr (natParams univs))} {V : @SExpr (natParams univs)}
    {depth : Nat} :
    letI : Params := natParams univs
    @HasTypeStratifiedS (natParams univs) Γ
      (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.rhs)
      V true depth →
    14 ≤ depth := by
  letI : Params := natParams univs
  intro H
  change HasTypeStratifiedS Γ
    (SExpr.mkInst [level]
      (NatGeneration.rule 1 NatGeneration.flatCtors[1]).rhs)
    V true depth at H
  rw [probeNatSuccRuleRhsS_eq] at H
  exact probeNatSuccRuleRhs_depth_lower_bound univs level H

/--
info: 'Lean4Lean.SExpr.ParamsD0.natSuccDirectIotaRule_rhs_depth_lower_bound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 probeNatRecTypeV_eq._native.native_decide.ax_1_1,
 probeNatSuccRuleRhsV_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms natSuccDirectIotaRule_rhs_depth_lower_bound

/-- The exact generated zero body multi-beta-reduces to its selected minor.
The three steps are supplied by the syntax-level tower reducer, so dependent
binder annotations are transported by accumulated substitution rather than
discarded by an endpoint equality. -/
theorem probeNatZeroRuleRhs_beta (univs : Nat)
    (level : @SLevel (natParams univs))
    (Γ : List (@SExpr (natParams univs)))
    (motive zeroMinor succMinor : @SExpr (natParams univs)) :
    letI : Params := natParams univs
    WHRedS Γ
      (((probeNatZeroRuleRhs univs level).app motive).app zeroMinor |>.app
        succMinor)
      zeroMinor := by
  letI : Params := natParams univs
  let NatS : SExpr := SExpr.const ``Nat []
  let Motive : SExpr := SExpr.forallE NatS (SExpr.sort level)
  let MinorZero : SExpr :=
    (SExpr.bvar 0).app (SExpr.const ``Nat.zero [])
  let MinorSucc : SExpr :=
    SExpr.forallE NatS <|
      SExpr.forallE ((SExpr.bvar 2).app (SExpr.bvar 0)) <|
        (SExpr.bvar 3).app
          ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))
  simpa [probeNatZeroRuleRhs, NatS, Motive, MinorZero, MinorSucc,
    SExpr.subst, Subst.cons, Subst.id] using
    (WHRedS.lamTower (Γ := Γ)
      [Motive, MinorZero, MinorSucc] (SExpr.bvar 1)
      [motive, zeroMinor, succMinor] rfl)

/-- The exact generated successor body multi-beta-reduces to the successor
minor applied to the predecessor and its recursive `Nat.rec` call. -/
theorem probeNatSuccRuleRhs_beta (univs : Nat)
    (level : @SLevel (natParams univs))
    (Γ : List (@SExpr (natParams univs)))
    (motive zeroMinor succMinor pred : @SExpr (natParams univs)) :
    letI : Params := natParams univs
    WHRedS Γ
      ((((probeNatSuccRuleRhs univs level).app motive).app zeroMinor |>.app
        succMinor).app pred)
      ((succMinor.app pred).app
        (((((SExpr.const ``Nat.rec [level]).app motive).app zeroMinor).app
          succMinor).app pred)) := by
  letI : Params := natParams univs
  let NatS : SExpr := SExpr.const ``Nat []
  let Motive : SExpr := SExpr.forallE NatS (SExpr.sort level)
  let MinorZero : SExpr :=
    (SExpr.bvar 0).app (SExpr.const ``Nat.zero [])
  let MinorSucc : SExpr :=
    SExpr.forallE NatS <|
      SExpr.forallE ((SExpr.bvar 2).app (SExpr.bvar 0)) <|
        (SExpr.bvar 3).app
          ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))
  let Body : SExpr :=
    ((SExpr.bvar 1).app (SExpr.bvar 0)).app <|
      ((((SExpr.const ``Nat.rec [level]).app
        (SExpr.bvar 3)).app (SExpr.bvar 2)).app
        (SExpr.bvar 1)).app (SExpr.bvar 0)
  simpa [probeNatSuccRuleRhs, NatS, Motive, MinorZero, MinorSucc, Body,
    SExpr.subst, Subst.cons, Subst.id] using
    (WHRedS.lamTower (Γ := Γ)
      [Motive, MinorZero, MinorSucc, NatS] Body
      [motive, zeroMinor, succMinor, pred] rfl)

/-- The left endpoint is the actual registered zero RHS applied to its named
capture function, rather than a separately postulated tower. -/
theorem natZeroRuleRHS_beta (univs : Nat)
    (level : @SLevel (natParams univs))
    (Γ : List (@SExpr (natParams univs)))
    (mcap : (RecursorIotaPattern ``Nat.rec 3 ``Nat.zero 0).Path →
      @SExpr (natParams univs)) :
    letI : Params := natParams univs
    WHRedS Γ
      ((NatGeneration.ruleRHS natRuleClosure
        probeNatFlatCtorZero_lookup).applyS [level] mcap)
      (mcap natZeroMinorPath) := by
  letI : Params := natParams univs
  rw [natZeroRuleRHS_applyS, probeNatZeroRuleRhsS_eq]
  exact probeNatZeroRuleRhs_beta univs level Γ
    (mcap natZeroMotivePath) (mcap natZeroMinorPath)
    (mcap natZeroSuccMinorPath)

/-- The actual registered successor RHS reduces to the generated recursive
minor application at its four named captures. -/
theorem natSuccRuleRHS_beta (univs : Nat)
    (level : @SLevel (natParams univs))
    (Γ : List (@SExpr (natParams univs)))
    (mcap : (RecursorIotaPattern ``Nat.rec 3 ``Nat.succ 1).Path →
      @SExpr (natParams univs)) :
    letI : Params := natParams univs
    WHRedS Γ
      ((NatGeneration.ruleRHS natRuleClosure
        probeNatFlatCtorSucc_lookup).applyS [level] mcap)
      (((mcap natSuccMinorPath).app (mcap natSuccPredPath)).app
        (((((SExpr.const ``Nat.rec [level]).app
          (mcap natSuccMotivePath)).app
          (mcap natSuccZeroMinorPath)).app
          (mcap natSuccMinorPath)).app (mcap natSuccPredPath))) := by
  letI : Params := natParams univs
  rw [natSuccRuleRHS_applyS, probeNatSuccRuleRhsS_eq]
  exact probeNatSuccRuleRhs_beta univs level Γ
    (mcap natSuccMotivePath) (mcap natSuccZeroMinorPath)
    (mcap natSuccMinorPath) (mcap natSuccPredPath)

/-- The descriptor half of `Params.Semantic.iotaRule`, recovered directly
from the certified generated-rule membership proof.  The intermediate
statement is proposition-valued so it can eliminate `IotaPat`; the public
descriptor below selects the uniquely indexed witness. -/
theorem natIotaRule_nonempty (univs : Nat)
    {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (H : (natParams univs).Pat
      (RecursorIotaPattern rec major ctor arity) r) :
    Nonempty (@Pattern.IotaRule (natParams univs)
      rec major ctor arity r) := by
  letI : Params := natParams univs
  change NatPat (RecursorIotaPattern rec major ctor arity) r at H
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
        (NatGeneration.ruleArgArity constructor)) rgen :=
    .mk hentry
  have hr : r ≍ rgen :=
    (VInductDecl.BlockGenerationChecked.IotaPat.pat_uniq NatGeneration
      H Hgen .refl (Pattern.inter_self _)).2.2
  have hr' : r = rgen := eq_of_heq hr
  subst r
  refine ⟨{
    pat := ?_
    df := NatGeneration.rule i constructor
    registered := natRule_registered hentry
    rhsClosed := natRuleClosure.rhs_closed hentry
    capturePaths := natCapturePaths constructor
    rhsTower := ?_ }⟩
  · change NatPat _ _
    exact Hgen
  · simpa only [rgen,
      VInductDecl.BlockGenerationChecked.rulePattern,
      SimplePattern.toPattern, RecursorIotaPattern] using
      natRuleRHS_tower hentry

noncomputable def natIotaRule (univs : Nat)
    {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (H : (natParams univs).Pat
      (RecursorIotaPattern rec major ctor arity) r) :
    @Pattern.IotaRule (natParams univs) rec major ctor arity r :=
  Classical.choice (natIotaRule_nonempty univs H)

/-- Every iota pattern in the base Nat fixture has a semantic descriptor
whose registered equation carries certified structural descent.  The witness
is selected from the generation entry itself rather than from the weaker
`Params.Semantic.iotaRule` result, whose public type intentionally remembers
only registration. -/
theorem natIotaStructuralDescent (univs : Nat)
    {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (H : (natParams univs).Pat
      (RecursorIotaPattern rec major ctor arity) r) :
    ∃ rule : @Pattern.IotaRule (natParams univs) rec major ctor arity r,
      @Pattern.IotaRule.StructuralDescent (natParams univs)
        rec major ctor arity r rule := by
  letI : Params := natParams univs
  change NatPat (RecursorIotaPattern rec major ctor arity) r at H
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
        (NatGeneration.ruleArgArity constructor)) rgen :=
    .mk hentry
  have hr : r ≍ rgen :=
    (VInductDecl.BlockGenerationChecked.IotaPat.pat_uniq NatGeneration
      H Hgen .refl (Pattern.inter_self _)).2.2
  have hr' : r = rgen := eq_of_heq hr
  subst r
  let rule : @Pattern.IotaRule (natParams univs)
      (NatGeneration.ruleRecName constructor)
      (NatGeneration.ruleMajorArity constructor) constructor.ctor.raw.name
      (NatGeneration.ruleArgArity constructor) rgen := {
    pat := Hgen
    df := NatGeneration.rule i constructor
    registered := natRule_registered hentry
    rhsClosed := natRuleClosure.rhs_closed hentry
    capturePaths := natCapturePaths constructor
    rhsTower := by
      simpa only [rgen, VInductDecl.BlockGenerationChecked.rulePattern,
        SimplePattern.toPattern, RecursorIotaPattern] using
        natRuleRHS_tower hentry }
  refine ⟨rule, ⟨?_⟩⟩
  exact {
    source := InductiveFixtures.natDecl
    generation := NatGeneration
    ruleIndex := i
    constructor := constructor
    entry := hentry
    rule_eq := rfl
    recursive_lt := natRule_recursive_lt hentry }

/-- Every concrete Nat pattern match selects its canonical registered rule
and carries a checked, conversion-aware capture spine and beta collapse. -/
theorem natIotaSite_nonempty (univs : Nat)
    {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {Gamma : List (@SExpr (natParams univs))}
    {A majorTerm : @SExpr (natParams univs)}
    {recLs ctorLs : List (@SLevel (natParams univs))}
    {recArgs ctorArgs : List (@SExpr (natParams univs))}
    {mcap : (RecursorIotaPattern rec major ctor arity).Path →
      @SExpr (natParams univs)}
    (rule : @Pattern.IotaRule (natParams univs) rec major ctor arity r)
    (captureType : (RecursorIotaPattern rec major ctor arity).Path →
      @SExpr (natParams univs))
    (captureTyping : @Pattern.CaptureTyping (natParams univs) Gamma
      (RecursorIotaPattern rec major ctor arity) mcap captureType)
    (hGamma : NatContextValid univs Gamma)
    (typing : @Pattern.IotaTyping (natParams univs) Gamma rec ctor recLs ctorLs
      recArgs ctorArgs majorTerm A)
    (matched : @Pattern.MatchesS (natParams univs)
      (RecursorIotaPattern rec major ctor arity)
      (@SExpr.app (natParams univs)
        (recArgs.foldr (fun a f => @SExpr.app (natParams univs) f a)
          (@SExpr.const (natParams univs) rec recLs))
        (ctorArgs.foldr (fun a f => @SExpr.app (natParams univs) f a)
          (@SExpr.const (natParams univs) ctor ctorLs))) recLs mcap)
    (redexSelf : @IsDefEq (natParams univs) Gamma
      (@SExpr.app (natParams univs)
        (recArgs.foldr (fun a f => @SExpr.app (natParams univs) f a)
          (@SExpr.const (natParams univs) rec recLs))
        (ctorArgs.foldr (fun a f => @SExpr.app (natParams univs) f a)
          (@SExpr.const (natParams univs) ctor ctorLs)))
      (@SExpr.app (natParams univs)
        (recArgs.foldr (fun a f => @SExpr.app (natParams univs) f a)
          (@SExpr.const (natParams univs) rec recLs))
        (ctorArgs.foldr (fun a f => @SExpr.app (natParams univs) f a)
          (@SExpr.const (natParams univs) ctor ctorLs))) A)
    (AType : ∃ u, @IsDefEq (natParams univs) Gamma A A
      (@SExpr.sort (natParams univs) u)) :
    Nonempty (@Pattern.IotaReductionSite (natParams univs) Gamma rec major ctor
      arity r rule recLs ctorLs recArgs ctorArgs majorTerm A mcap captureType
      captureTyping) := by
  letI : Params := natParams univs
  have hpat := rule.pat
  change NatPat _ _ at hpat
  obtain ⟨i, constructor, hentry, hpattern, -⟩ :=
    VInductDecl.BlockGenerationChecked.IotaPat.recover NatGeneration hpat
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
      hpat Hgen .refl (Pattern.inter_self _)).2.2
  have hr' : r = rgen := eq_of_heq hr
  subst r
  rcases rule with
    ⟨rulePat, df, ruleRegistered, rhsClosed, capturePaths, rhsTower⟩
  change NatGeneration.ruleRHS natRuleClosure hentry =
    Pattern.RHS.appN (.fixed df.rhs rhsClosed)
      (capturePaths.map fun path => .var path) at rhsTower
  rw [natRuleRHS_tower hentry] at rhsTower
  obtain ⟨hrhs, hpaths⟩ := rhsFixedAppN_inj rhsTower
  subst capturePaths
  have hi : i = 0 ∨ i = 1 := by
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hentry
    have : NatGeneration.flatCtors.length = 2 := rfl
    omega
  have hreg := ruleRegistered
  change natFinalEnv.defeqs df at hreg
  rw [natFinalEnv_defeqs_iff] at hreg
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hreg
  have hj' : j = 0 ∨ j = 1 := by
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hj
    have : NatGeneration.generatedRules.length = 2 := rfl
    omega
  rcases hi with rfl | rfl <;> rcases hj' with rfl | rfl
  all_goals
    first
    | have hc := Option.some.inj
        (probeNatFlatCtorZero_lookup.symm.trans hentry)
    | have hc := Option.some.inj
        (probeNatFlatCtorSucc_lookup.symm.trans hentry)
    first
    | have hdf := Option.some.inj
        (probeNatGeneratedRuleZero_lookup.symm.trans hj)
    | have hdf := Option.some.inj
        (probeNatGeneratedRuleSucc_lookup.symm.trans hj)
    subst df
  all_goals (try simp at hrhs ⊢)
  case inl.inl =>
    have hrecName : NatGeneration.ruleRecName constructor = ``Nat.rec := by
      rw [← hc]
      exact probeNatZeroRuleRecName
    have hctorName : constructor.ctor.raw.name = ``Nat.zero := by
      rw [← hc]
      exact probeNatZeroCtorName
    simp only [hrecName, hctorName] at typing matched redexSelf
    subst constructor
    have hrecLen := typing.recHead.const_left_levelsLength
      InductiveReplayFixtures.nat_rec_env_lookup
    change recLs.length = 1 at hrecLen
    obtain ⟨level, rfl⟩ := List.length_eq_one_iff.mp hrecLen
    have hctorLen := typing.ctorHead.const_left_levelsLength
      (ci := InductiveFixtures.natType.ctors[0].toVConstant) (by rfl)
    change ctorLs.length = 0 at hctorLen
    have hctorLs : ctorLs = [] := List.length_eq_zero_iff.mp hctorLen
    subst ctorLs
    obtain ⟨hrecArgsLen, hctorArgs, hcaptures⟩ :=
      natZeroCaptureValues univs matched
    rw [hctorArgs] at typing matched redexSelf ⊢
    have hrecArgs : ∃ x y z, recArgs = [x, y, z] :=
      ⟨recArgs[0], recArgs[1], recArgs[2],
        List.eq_getElem_of_length_eq_three recArgs hrecArgsLen⟩
    obtain ⟨minorSucc, minorZero, motive, rfl⟩ := hrecArgs
    have hrecCanonical : IsDefEq Gamma
        (.const ``Nat.rec [level]) (.const ``Nat.rec [level])
        (SExpr.mkInst [level]
          (VInductDecl.recConst 0 ``Nat 0 InductiveFixtures.natType).type) :=
      .const InductiveReplayFixtures.nat_rec_env_lookup rfl
    rw [probeNatRecTypeV_eq] at hrecCanonical
    have hheadEq := natTypeUniq univs hGamma hrecCanonical typing.recHead
    let motiveView := natSpineConsView univs hGamma hheadEq typing.recSpine
    have hmotive := motiveView.argumentExpected univs
    have hrestMotive := motiveView.restEq univs
    let zeroView := natSpineConsView univs hGamma hrestMotive motiveView.tail
    have hzero := zeroView.argumentExpected univs
    have hrestZero := zeroView.restEq univs
    let succView := natSpineConsView univs hGamma hrestZero zeroView.tail
    have hsucc := succView.argumentExpected univs
    have hrestSucc := succView.restEq univs
    let majorView := natSpineConsView univs hGamma hrestSucc succView.tail
    have hmajor := majorView.argumentExpected univs
    have hprefixMotive := IsDefEq.appDF hrecCanonical hmotive
    have hprefixZero := IsDefEq.appDF hprefixMotive hzero
    have hprefixSucc := IsDefEq.appDF hprefixZero hsucc
    obtain ⟨_, hmajorType⟩ := natTypeUniq univs hGamma
      typing.majorEq.hasType.1 hmajor
    have hmajorEq := hmajorType.defeqDF typing.majorEq
    have hredexAtGenerated := IsDefEq.appDF hprefixSucc hmajorEq
    have hctorAtRuleResult :=
      IsDefEq.appDF hprefixSucc hmajorEq.hasType.2
    have redexSelf' : IsDefEq Gamma
        (((((SExpr.const ``Nat.rec [level]).app motive).app minorZero).app
          minorSucc).app (SExpr.const ``Nat.zero []))
        (((((SExpr.const ``Nat.rec [level]).app motive).app minorZero).app
          minorSucc).app (SExpr.const ``Nat.zero [])) A := by
      simpa using redexSelf
    obtain ⟨_, hruleMajor⟩ := natTypeUniq univs hGamma
      hctorAtRuleResult hredexAtGenerated.hasType.2
    obtain ⟨_, hmajorA⟩ := natTypeUniq univs hGamma
      hredexAtGenerated.hasType.2 redexSelf'
    have hruleA := natTypesTrans univs hGamma
      ⟨_, hruleMajor⟩ ⟨_, hmajorA⟩
    obtain ⟨ruleSort, hruleA⟩ := hruleA
    have hruleA' : IsDefEq Gamma
        (motive.app (SExpr.const ``Nat.zero [])) A (.sort ruleSort) := by
      simpa [SExpr.mkInst, SExpr.inst, SExpr.subst, Subst.lift,
        Subst.cons, Subst.id, probeCancelThreeLifts] using hruleA
    have hmotive' : IsDefEq Gamma motive motive
        (.forallE (.const ``Nat []) (.sort level)) := by
      simpa [probeNatRecTypeV, SExpr.mkInst, probeInstVParamZero] using hmotive
    have hzero' : IsDefEq Gamma minorZero minorZero
        (motive.app (.const ``Nat.zero [])) := by
      simpa [probeNatRecTypeV, SExpr.mkInst, SExpr.inst, SExpr.subst,
        Subst.lift, Subst.cons, Subst.id] using hzero
    have hsucc' : IsDefEq Gamma minorSucc minorSucc
        (.forallE (SExpr.const ``Nat [])
          (.forallE
            (motive.lift.app (SExpr.bvar 0))
            (motive.lift.lift.app
              ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))))) := by
      simpa [probeNatRecTypeV, SExpr.mkInst, SExpr.inst, SExpr.subst,
        Subst.lift, Subst.cons, Subst.id, probeCancelTwoLifts,
        probeCancelUnderOne, probeCancelUnderTwo,
        probeInstVParamZero] using hsucc
    have hruleAForTelescope : IsDefEq Gamma
        (((((SExpr.bvar 2).app (SExpr.const ``Nat.zero [])).subst
          (Subst.one motive).lift.lift).subst
          (Subst.one minorZero).lift).inst minorSucc)
        A (.sort ruleSort) := by
      simpa [SExpr.inst, SExpr.subst, Subst.lift, Subst.cons,
        Subst.id, probeCancelTwoLifts] using hruleA'
    have hzeroForTelescope : IsDefEq Gamma minorZero minorZero
        (((SExpr.bvar 0).app (SExpr.const ``Nat.zero [])).subst
          (Subst.one motive)) := by
      simpa [SExpr.inst, SExpr.subst, Subst.lift, Subst.cons,
        Subst.id] using hzero'
    have hsuccForTelescope : IsDefEq Gamma minorSucc minorSucc
        (((SExpr.forallE (SExpr.const ``Nat [])
          (SExpr.forallE
            ((SExpr.bvar 2).app (SExpr.bvar 0))
            ((SExpr.bvar 3).app
              ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))))).subst
          (Subst.one motive).lift).subst (Subst.one minorZero)) := by
      simpa [SExpr.inst, SExpr.subst, Subst.lift, Subst.cons,
        Subst.id, probeCancelUnderOne, probeCancelUnderTwo] using hsucc'
    have hcoreExplicit : SpineWF Gamma (probeNatZeroRuleType univs level)
        [motive, minorZero, minorSucc]
        (((((SExpr.bvar 2).app (SExpr.const ``Nat.zero [])).subst
          (Subst.one motive).lift.lift).subst
          (Subst.one minorZero).lift).inst minorSucc) := by
      exact .cons hmotive' (.cons hzeroForTelescope
        (.cons hsuccForTelescope .nil))
    have hplainExplicit : SpineWF Gamma (probeNatZeroRuleType univs level)
        [motive, minorZero, minorSucc] A :=
      .ret hcoreExplicit hruleAForTelescope
    have hplain : SpineWF Gamma
        (SExpr.mkInst [level]
          (NatGeneration.rule 0 NatGeneration.flatCtors[0]).type)
        [motive, minorZero, minorSucc] A := by
      rw [probeNatZeroRuleTypeS_eq]
      exact hplainExplicit
    have hplainPaths : SpineWF Gamma
        (SExpr.mkInst [level]
          (NatGeneration.rule 0 NatGeneration.flatCtors[0]).type)
        ((natCapturePaths NatGeneration.flatCtors[0]).map mcap) A := by
      exact hcaptures.symm ▸ hplain
    have captureSpine := natPathSpineOfSpineWF univs hGamma
      captureTyping.typed hplainPaths
    let vls : List VLevel := [level.reify]
    have hvls : ∀ l ∈ vls, l.WF univs := by
      intro l hl
      simp only [vls, List.mem_singleton] at hl
      subst l
      exact SLevel.reify_wf level
    have hlhs :=
      (natFinalEnv_ordered.defEqWF ruleRegistered).1.instL hvls
    have hlhsGamma : natFinalEnv.HasType univs (Gamma.map SExpr.reify)
        (probeNatZeroRuleLhsV.instL vls)
        ((NatGeneration.rule 0 NatGeneration.flatCtors[0]).type.instL vls) := by
      rw [← probeNatZeroRuleLhsV_eq]
      exact hlhs.weak0 natFinalEnv_ordered
    unfold probeNatZeroRuleLhsV at hlhsGamma
    rw [VExpr.instL_lamN] at hlhsGamma
    obtain ⟨hTel, bodyType, hbody⟩ :=
      VEnv.HasType.lamN_wf natFinalEnv_ordered hGamma hlhsGamma
    have hmotiveV := hmotive'.reify hGamma
    change natFinalEnv.IsDefEq univs (Gamma.map SExpr.reify)
      motive.reify motive.reify _ at hmotiveV
    have hzeroV := hzeroForTelescope.reify hGamma
    change natFinalEnv.IsDefEq univs (Gamma.map SExpr.reify)
      minorZero.reify minorZero.reify _ at hzeroV
    have hsuccV := hsuccForTelescope.reify hGamma
    change natFinalEnv.IsDefEq univs (Gamma.map SExpr.reify)
      minorSucc.reify minorSucc.reify _ at hsuccV
    have hcoreV : natFinalEnv.SpineWF univs (Gamma.map SExpr.reify)
        (VExpr.forallN (probeNatRuleBindersV.map (VExpr.instL vls))
          (probeNatZeroRuleResultV.instL vls))
        [motive.reify, minorZero.reify, minorSucc.reify]
        (VExpr.instRev (probeNatZeroRuleResultV.instL vls)
          [motive.reify, minorZero.reify, minorSucc.reify]) := by
      refine .cons hmotiveV ?_
      refine .cons ?_ ?_
      · simpa [natParams, vls, VExpr.instL, SExpr.reify,
          SExpr.reify_subst,
          VExpr.inst_eq, probeReifySubstOne] using
          hzeroV
      refine .cons ?_ .nil
      simpa [natParams, vls, VExpr.instL, SExpr.reify,
        SExpr.reify_subst,
        SExpr.reify_inst, VExpr.inst_eq, VExpr.instN_eq,
        VExpr.Subst.liftN,
        probeReifySubstOne, probeReifySubstLift] using
        hsuccV
    have hspineV := hcoreV
    have hspineBody := VEnv.SpineWF.retarget hspineV
      (by simp [probeNatRuleBindersV])
      bodyType
    have hcollapseV := VEnv.IsDefEq.appN_lamN natFinalEnv_ordered
      hTel hbody hspineBody (by simp [probeNatRuleBindersV])
    have hlevels :=
      (VEnv.CtxStrong.strong natFinalEnv_ordered hGamma).levelWF
    have hcollapseS := SExpr.IsDefEq.mkS (natStructureEtaSound univs)
      hcollapseV hlevels
    have hctx : (Gamma.map SExpr.reify).map SExpr.mk = Gamma := by
      rw [List.map_map]
      exact List.map_id''' Gamma fun term _ => SExpr.mk_reify term
    rw [hctx] at hcollapseS
    have hmkInst (e : VExpr) :
        SExpr.mk (e.instL vls) = SExpr.mkInst [level] e := by
      unfold vls
      exact @SExpr.mk_instL_map_reify (natParams univs) e [level]
    have hlevelMk :
        SLevel.mk (VLevel.inst vls (VLevel.param 0)) = level := by
      simp [vls, probeReifyInstVParamZero, SLevel.mk_reify]
    have hbodyCollapseV :
        (probeNatZeroRuleLhsBodyV.instL vls).instRev
          [motive.reify, minorZero.reify, minorSucc.reify] =
        (((((VExpr.const ``Nat.rec [level.reify]).app motive.reify).app
          minorZero.reify).app minorSucc.reify).app
          (VExpr.const ``Nat.zero [])) := by
      simp [probeNatZeroRuleLhsBodyV, vls, VExpr.instRev, VExpr.instL,
        VExpr.inst, VExpr.instVar, VExpr.liftN, liftVar,
        VExpr.liftN_succ, VExpr.liftN_zero, probeReifyInstVParamZero,
        probeVCancelTwoLifts, VExpr.inst_lift]
      simpa only [VExpr.liftN_zero] using
        probeVCancelTwoLifts motive.reify minorZero.reify minorSucc.reify
    rw [hbodyCollapseV] at hcollapseS
    have hcollapseCanonical : IsDefEq Gamma
        ([motive, minorZero, minorSucc].foldl
          (fun (f a : SExpr) => f.app a)
          (SExpr.mkInst [level]
            (NatGeneration.rule 0 NatGeneration.flatCtors[0]).lhs))
        (((((SExpr.const ``Nat.rec [level]).app motive).app minorZero).app
          minorSucc).app (SExpr.const ``Nat.zero []))
        (SExpr.mk (bodyType.instRev
          [motive.reify, minorZero.reify, minorSucc.reify])) := by
      rw [probeNatZeroRuleLhsV_eq]
      simpa [vls, hmkInst, hlevelMk, probeNatZeroRuleLhsV,
        probeNatRuleBindersV, probeNatZeroRuleLhsBodyV,
        VExpr.lamN, VExpr.appN,
        probeVCancelTwoLifts, VExpr.inst_lift, SExpr.mk,
        SExpr.mkInst] using
        hcollapseS
    obtain ⟨_, hcollapseType⟩ := natTypeUniq univs hGamma
      hcollapseCanonical.hasType.2 redexSelf'
    have lhsCollapseCanonical : IsDefEq Gamma
        (((((SExpr.const ``Nat.rec [level]).app motive).app minorZero).app
          minorSucc).app (SExpr.const ``Nat.zero []))
        ([motive, minorZero, minorSucc].foldl
          (fun (f a : SExpr) => f.app a)
          (SExpr.mkInst [level]
            (NatGeneration.rule 0 NatGeneration.flatCtors[0]).lhs)) A :=
      hcollapseType.defeqDF hcollapseCanonical.symm
    refine ⟨{
      typing := typing
      matched := matched
      levelsLength := by rfl
      captureSpine := captureSpine
      lhsCollapse := ?_
      dfs := []
      defeqs := by rfl
      checked := by simp }⟩
    simpa [probeNatZeroRuleRecName] using
      (hcaptures.symm ▸ lhsCollapseCanonical)
  case inl.inr =>
    subst constructor
    exact (probeNatRuleRhs_ne (by simpa using hrhs)).elim
  case inr.inl =>
    subst constructor
    exact (probeNatRuleRhs_ne (by simpa using hrhs.symm)).elim
  case inr.inr =>
    have hrecName : NatGeneration.ruleRecName constructor = ``Nat.rec := by
      rw [← hc]
      exact probeNatSuccRuleRecName
    have hctorName : constructor.ctor.raw.name = ``Nat.succ := by
      rw [← hc]
      exact probeNatSuccCtorName
    simp only [hrecName, hctorName] at typing matched redexSelf
    subst constructor
    have hrecLen := typing.recHead.const_left_levelsLength
      InductiveReplayFixtures.nat_rec_env_lookup
    change recLs.length = 1 at hrecLen
    obtain ⟨level, rfl⟩ := List.length_eq_one_iff.mp hrecLen
    have hctorLen := typing.ctorHead.const_left_levelsLength
      InductiveReplayFixtures.nat_succ_env_lookup
    change ctorLs.length = 0 at hctorLen
    have hctorLs : ctorLs = [] := List.length_eq_zero_iff.mp hctorLen
    subst ctorLs
    obtain ⟨hrecArgsLen, hctorArgsLen, hcaptures⟩ :=
      natSuccCaptureValues univs matched
    obtain ⟨pred, rfl⟩ := List.length_eq_one_iff.mp hctorArgsLen
    have hrecArgs : ∃ x y z, recArgs = [x, y, z] :=
      ⟨recArgs[0], recArgs[1], recArgs[2],
        List.eq_getElem_of_length_eq_three recArgs hrecArgsLen⟩
    obtain ⟨minorSucc, minorZero, motive, rfl⟩ := hrecArgs
    have hrecCanonical : IsDefEq Gamma
        (.const ``Nat.rec [level]) (.const ``Nat.rec [level])
        (SExpr.mkInst [level]
          (VInductDecl.recConst 0 ``Nat 0 InductiveFixtures.natType).type) :=
      .const InductiveReplayFixtures.nat_rec_env_lookup rfl
    rw [probeNatRecTypeV_eq] at hrecCanonical
    have hheadEq := natTypeUniq univs hGamma hrecCanonical typing.recHead
    let motiveView := natSpineConsView univs hGamma hheadEq typing.recSpine
    have hmotive := motiveView.argumentExpected univs
    have hrestMotive := motiveView.restEq univs
    let zeroView := natSpineConsView univs hGamma hrestMotive motiveView.tail
    have hzero := zeroView.argumentExpected univs
    have hrestZero := zeroView.restEq univs
    let succView := natSpineConsView univs hGamma hrestZero zeroView.tail
    have hsucc := succView.argumentExpected univs
    have hrestSucc := succView.restEq univs
    let majorView := natSpineConsView univs hGamma hrestSucc succView.tail
    have hmajor := majorView.argumentExpected univs
    have hctorCanonical : IsDefEq Gamma
        (.const ``Nat.succ []) (.const ``Nat.succ [])
        (SExpr.mkInst [] InductiveFixtures.natType.ctors[1].type) :=
      .const InductiveReplayFixtures.nat_succ_env_lookup rfl
    rw [probeNatSuccCtorTypeV_eq] at hctorCanonical
    have hctorCanonical' : IsDefEq Gamma
        (.const ``Nat.succ []) (.const ``Nat.succ [])
        (.forallE (.const ``Nat []) (.const ``Nat [])) := by
      simpa [SExpr.mkInst] using hctorCanonical
    have hctorType := natTypeUniq univs hGamma
      hctorCanonical' typing.ctorHead
    let predView := natSpineConsView univs hGamma hctorType typing.ctorSpine
    have hpred := predView.argumentExpected univs
    have hpred' : IsDefEq Gamma pred pred (.const ``Nat []) := by
      simpa using hpred
    have hprefixMotive := IsDefEq.appDF hrecCanonical hmotive
    have hprefixZero := IsDefEq.appDF hprefixMotive hzero
    have hprefixSucc := IsDefEq.appDF hprefixZero hsucc
    obtain ⟨_, hmajorType⟩ := natTypeUniq univs hGamma
      typing.majorEq.hasType.1 hmajor
    have hmajorEq := hmajorType.defeqDF typing.majorEq
    have hredexAtGenerated := IsDefEq.appDF hprefixSucc hmajorEq
    have hctorAtRuleResult :=
      IsDefEq.appDF hprefixSucc hmajorEq.hasType.2
    have redexSelf' : IsDefEq Gamma
        (((((SExpr.const ``Nat.rec [level]).app motive).app minorZero).app
          minorSucc).app
            ((SExpr.const ``Nat.succ []).app pred))
        (((((SExpr.const ``Nat.rec [level]).app motive).app minorZero).app
          minorSucc).app
            ((SExpr.const ``Nat.succ []).app pred)) A := by
      simpa using redexSelf
    obtain ⟨_, hruleMajor⟩ := natTypeUniq univs hGamma
      hctorAtRuleResult hredexAtGenerated.hasType.2
    obtain ⟨_, hmajorA⟩ := natTypeUniq univs hGamma
      hredexAtGenerated.hasType.2 redexSelf'
    have hruleA := natTypesTrans univs hGamma
      ⟨_, hruleMajor⟩ ⟨_, hmajorA⟩
    obtain ⟨ruleSort, hruleA⟩ := hruleA
    have hruleA' : IsDefEq Gamma
        (motive.app ((SExpr.const ``Nat.succ []).app pred)) A
        (.sort ruleSort) := by
      simpa [SExpr.mkInst, SExpr.inst, SExpr.subst, Subst.lift,
        Subst.cons, Subst.id, probeCancelThreeLifts] using hruleA
    have hmotive' : IsDefEq Gamma motive motive
        (.forallE (.const ``Nat []) (.sort level)) := by
      simpa [probeNatRecTypeV, SExpr.mkInst, probeInstVParamZero] using hmotive
    have hzero' : IsDefEq Gamma minorZero minorZero
        (motive.app (.const ``Nat.zero [])) := by
      simpa [probeNatRecTypeV, SExpr.mkInst, SExpr.inst, SExpr.subst,
        Subst.lift, Subst.cons, Subst.id] using hzero
    have hsucc' : IsDefEq Gamma minorSucc minorSucc
        (.forallE (SExpr.const ``Nat [])
          (.forallE
            (motive.lift.app (SExpr.bvar 0))
            (motive.lift.lift.app
              ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))))) := by
      simpa [probeNatRecTypeV, SExpr.mkInst, SExpr.inst, SExpr.subst,
        Subst.lift, Subst.cons, Subst.id, probeCancelTwoLifts,
        probeCancelUnderOne, probeCancelUnderTwo,
        probeInstVParamZero] using hsucc
    have hruleAForTelescope : IsDefEq Gamma
        ((((((SExpr.bvar 3).app
          ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0))).subst
            (Subst.one motive).lift.lift.lift).subst
            (Subst.one minorZero).lift.lift).subst
            (Subst.one minorSucc).lift).inst pred)
        A (.sort ruleSort) := by
      simpa [SExpr.inst, SExpr.subst, Subst.lift, Subst.cons,
        Subst.id, probeCancelThreeLifts] using hruleA'
    have hzeroForTelescope : IsDefEq Gamma minorZero minorZero
        (((SExpr.bvar 0).app (SExpr.const ``Nat.zero [])).subst
          (Subst.one motive)) := by
      simpa [SExpr.inst, SExpr.subst, Subst.lift, Subst.cons,
        Subst.id] using hzero'
    have hsuccForTelescope : IsDefEq Gamma minorSucc minorSucc
        (((SExpr.forallE (SExpr.const ``Nat [])
          (SExpr.forallE
            ((SExpr.bvar 2).app (SExpr.bvar 0))
            ((SExpr.bvar 3).app
              ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))))).subst
          (Subst.one motive).lift).subst (Subst.one minorZero)) := by
      simpa [SExpr.inst, SExpr.subst, Subst.lift, Subst.cons,
        Subst.id, probeCancelUnderOne, probeCancelUnderTwo] using hsucc'
    have hcoreExplicit : SpineWF Gamma (probeNatSuccRuleType univs level)
        [motive, minorZero, minorSucc, pred]
        ((((((SExpr.bvar 3).app
          ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0))).subst
            (Subst.one motive).lift.lift.lift).subst
            (Subst.one minorZero).lift.lift).subst
            (Subst.one minorSucc).lift).inst pred) := by
      exact .cons hmotive' (.cons hzeroForTelescope
        (.cons hsuccForTelescope (.cons hpred' .nil)))
    have hplainExplicit : SpineWF Gamma (probeNatSuccRuleType univs level)
        [motive, minorZero, minorSucc, pred] A :=
      .ret hcoreExplicit hruleAForTelescope
    have hplain : SpineWF Gamma
        (SExpr.mkInst [level]
          (NatGeneration.rule 1 NatGeneration.flatCtors[1]).type)
        [motive, minorZero, minorSucc, pred] A := by
      rw [probeNatSuccRuleTypeS_eq]
      exact hplainExplicit
    have hplainPaths : SpineWF Gamma
        (SExpr.mkInst [level]
          (NatGeneration.rule 1 NatGeneration.flatCtors[1]).type)
        ((natCapturePaths NatGeneration.flatCtors[1]).map mcap) A := by
      exact hcaptures.symm ▸ hplain
    have captureSpine := natPathSpineOfSpineWF univs hGamma
      captureTyping.typed hplainPaths
    let vls : List VLevel := [level.reify]
    have hvls : ∀ l ∈ vls, l.WF univs := by
      intro l hl
      simp only [vls, List.mem_singleton] at hl
      subst l
      exact SLevel.reify_wf level
    have hlhs :=
      (natFinalEnv_ordered.defEqWF ruleRegistered).1.instL hvls
    have hlhsGamma : natFinalEnv.HasType univs (Gamma.map SExpr.reify)
        (probeNatSuccRuleLhsV.instL vls)
        ((NatGeneration.rule 1 NatGeneration.flatCtors[1]).type.instL vls) := by
      rw [← probeNatSuccRuleLhsV_eq]
      exact hlhs.weak0 natFinalEnv_ordered
    unfold probeNatSuccRuleLhsV at hlhsGamma
    rw [VExpr.instL_lamN] at hlhsGamma
    obtain ⟨hTel, bodyType, hbody⟩ :=
      VEnv.HasType.lamN_wf natFinalEnv_ordered hGamma hlhsGamma
    have hmotiveV := hmotive'.reify hGamma
    change natFinalEnv.IsDefEq univs (Gamma.map SExpr.reify)
      motive.reify motive.reify _ at hmotiveV
    have hzeroV := hzeroForTelescope.reify hGamma
    change natFinalEnv.IsDefEq univs (Gamma.map SExpr.reify)
      minorZero.reify minorZero.reify _ at hzeroV
    have hsuccV := hsuccForTelescope.reify hGamma
    change natFinalEnv.IsDefEq univs (Gamma.map SExpr.reify)
      minorSucc.reify minorSucc.reify _ at hsuccV
    have hpredV := hpred'.reify hGamma
    change natFinalEnv.IsDefEq univs (Gamma.map SExpr.reify)
      pred.reify pred.reify _ at hpredV
    have hcoreV : natFinalEnv.SpineWF univs (Gamma.map SExpr.reify)
        (VExpr.forallN
          (probeNatSuccRuleBindersV.map (VExpr.instL vls))
          (probeNatSuccRuleResultV.instL vls))
        [motive.reify, minorZero.reify, minorSucc.reify, pred.reify]
        (VExpr.instRev (probeNatSuccRuleResultV.instL vls)
          [motive.reify, minorZero.reify, minorSucc.reify, pred.reify]) := by
      refine .cons hmotiveV ?_
      refine .cons ?_ ?_
      · simpa [natParams, vls, VExpr.instL, SExpr.reify,
          SExpr.reify_subst, VExpr.inst_eq, probeReifySubstOne] using hzeroV
      refine .cons ?_ ?_
      · simpa [natParams, vls, VExpr.instL, SExpr.reify,
          SExpr.reify_subst, SExpr.reify_inst, VExpr.inst_eq,
          VExpr.instN_eq, VExpr.Subst.liftN, probeReifySubstOne,
          probeReifySubstLift] using hsuccV
      refine .cons ?_ .nil
      simpa [natParams, vls, VExpr.instL, VExpr.inst, SExpr.reify] using hpredV
    have hspineBody := VEnv.SpineWF.retarget hcoreV
      (by simp [probeNatSuccRuleBindersV, probeNatRuleBindersV]) bodyType
    have hcollapseV := VEnv.IsDefEq.appN_lamN natFinalEnv_ordered
      hTel hbody hspineBody
      (by simp [probeNatSuccRuleBindersV, probeNatRuleBindersV])
    have hlevels :=
      (VEnv.CtxStrong.strong natFinalEnv_ordered hGamma).levelWF
    have hcollapseS := SExpr.IsDefEq.mkS (natStructureEtaSound univs)
      hcollapseV hlevels
    have hctx : (Gamma.map SExpr.reify).map SExpr.mk = Gamma := by
      rw [List.map_map]
      exact List.map_id''' Gamma fun term _ => SExpr.mk_reify term
    rw [hctx] at hcollapseS
    have hmkInst (e : VExpr) :
        SExpr.mk (e.instL vls) = SExpr.mkInst [level] e := by
      unfold vls
      exact @SExpr.mk_instL_map_reify (natParams univs) e [level]
    have hlevelMk :
        SLevel.mk (VLevel.inst vls (VLevel.param 0)) = level := by
      simp [vls, probeReifyInstVParamZero, SLevel.mk_reify]
    have hbodyCollapseV :
        (probeNatSuccRuleLhsBodyV.instL vls).instRev
          [motive.reify, minorZero.reify, minorSucc.reify, pred.reify] =
        (((((VExpr.const ``Nat.rec [level.reify]).app motive.reify).app
          minorZero.reify).app minorSucc.reify).app
          ((VExpr.const ``Nat.succ []).app pred.reify)) := by
      simp [probeNatSuccRuleLhsBodyV, vls, VExpr.instRev, VExpr.instL,
        VExpr.inst, VExpr.instVar, VExpr.liftN, liftVar,
        VExpr.liftN_succ, VExpr.liftN_zero, probeReifyInstVParamZero,
        probeVCancelThreeLifts, probeVCancelTwoLifts, VExpr.inst_lift]
      constructor
      · simpa only [VExpr.liftN_zero] using
          probeVCancelThreeLifts motive.reify minorZero.reify
            minorSucc.reify pred.reify
      · simpa only [VExpr.liftN_zero] using
          probeVCancelTwoLifts minorZero.reify minorSucc.reify pred.reify
    rw [hbodyCollapseV] at hcollapseS
    have hcollapseCanonical : IsDefEq Gamma
        ([motive, minorZero, minorSucc, pred].foldl
          (fun (f a : SExpr) => f.app a)
          (SExpr.mkInst [level]
            (NatGeneration.rule 1 NatGeneration.flatCtors[1]).lhs))
        (((((SExpr.const ``Nat.rec [level]).app motive).app minorZero).app
          minorSucc).app ((SExpr.const ``Nat.succ []).app pred))
        (SExpr.mk (bodyType.instRev
          [motive.reify, minorZero.reify, minorSucc.reify, pred.reify])) := by
      rw [probeNatSuccRuleLhsV_eq]
      simpa [vls, hmkInst, hlevelMk, probeNatSuccRuleLhsV,
        probeNatSuccRuleBindersV, probeNatRuleBindersV,
        probeNatSuccRuleLhsBodyV, VExpr.lamN, VExpr.appN,
        probeVCancelThreeLifts, probeVCancelTwoLifts, VExpr.inst_lift,
        SExpr.mk, SExpr.mkInst] using hcollapseS
    obtain ⟨_, hcollapseType⟩ := natTypeUniq univs hGamma
      hcollapseCanonical.hasType.2 redexSelf'
    have lhsCollapseCanonical : IsDefEq Gamma
        (((((SExpr.const ``Nat.rec [level]).app motive).app minorZero).app
          minorSucc).app ((SExpr.const ``Nat.succ []).app pred))
        ([motive, minorZero, minorSucc, pred].foldl
          (fun (f a : SExpr) => f.app a)
          (SExpr.mkInst [level]
            (NatGeneration.rule 1 NatGeneration.flatCtors[1]).lhs)) A :=
      hcollapseType.defeqDF hcollapseCanonical.symm
    refine ⟨{
      typing := typing
      matched := matched
      levelsLength := by rfl
      captureSpine := captureSpine
      lhsCollapse := ?_
      dfs := []
      defeqs := by rfl
      checked := by simp }⟩
    simpa [probeNatSuccRuleRecName] using
      (hcaptures.symm ▸ lhsCollapseCanonical)

/-- Data-valued Nat iota-site bridge selected from the proposition-valued
certificate above. -/
noncomputable def natIotaSite (univs : Nat)
    {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {Gamma : List (@SExpr (natParams univs))}
    {A majorTerm : @SExpr (natParams univs)}
    {recLs ctorLs : List (@SLevel (natParams univs))}
    {recArgs ctorArgs : List (@SExpr (natParams univs))}
    {mcap : (RecursorIotaPattern rec major ctor arity).Path →
      @SExpr (natParams univs)}
    (rule : @Pattern.IotaRule (natParams univs) rec major ctor arity r)
    (captureType : (RecursorIotaPattern rec major ctor arity).Path →
      @SExpr (natParams univs))
    (captureTyping : @Pattern.CaptureTyping (natParams univs) Gamma
      (RecursorIotaPattern rec major ctor arity) mcap captureType)
    (hGamma : NatContextValid univs Gamma)
    (typing : @Pattern.IotaTyping (natParams univs) Gamma rec ctor recLs ctorLs
      recArgs ctorArgs majorTerm A)
    (matched : @Pattern.MatchesS (natParams univs)
      (RecursorIotaPattern rec major ctor arity)
      (@SExpr.app (natParams univs)
        (recArgs.foldr (fun a f => @SExpr.app (natParams univs) f a)
          (@SExpr.const (natParams univs) rec recLs))
        (ctorArgs.foldr (fun a f => @SExpr.app (natParams univs) f a)
          (@SExpr.const (natParams univs) ctor ctorLs))) recLs mcap)
    (redexSelf : @IsDefEq (natParams univs) Gamma
      (@SExpr.app (natParams univs)
        (recArgs.foldr (fun a f => @SExpr.app (natParams univs) f a)
          (@SExpr.const (natParams univs) rec recLs))
        (ctorArgs.foldr (fun a f => @SExpr.app (natParams univs) f a)
          (@SExpr.const (natParams univs) ctor ctorLs)))
      (@SExpr.app (natParams univs)
        (recArgs.foldr (fun a f => @SExpr.app (natParams univs) f a)
          (@SExpr.const (natParams univs) rec recLs))
        (ctorArgs.foldr (fun a f => @SExpr.app (natParams univs) f a)
          (@SExpr.const (natParams univs) ctor ctorLs))) A)
    (AType : ∃ u, @IsDefEq (natParams univs) Gamma A A
      (@SExpr.sort (natParams univs) u)) :
    @Pattern.IotaReductionSite (natParams univs) Gamma rec major ctor arity r
      rule recLs ctorLs recArgs ctorArgs majorTerm A mcap captureType
      captureTyping :=
  Classical.choice (natIotaSite_nonempty univs rule captureType captureTyping
    hGamma typing matched redexSelf AType)

theorem natOnTelWeakR {env : VEnv} {univs : Nat}
    (henv : env.Ordered) :
    ∀ {Base As : List VExpr}, CtxClosed Base →
      env.OnTel univs Base As → ∀ Tail,
        env.OnTel univs (Base ++ Tail) As
  | _, [], _, _, _ => trivial
  | Base, A :: As, hBase, ⟨⟨u, hA⟩, hAs⟩, Tail => by
      refine ⟨⟨u, VEnv.IsDefEq.weakR henv hBase hA Tail⟩, ?_⟩
      have hAClosed : A.ClosedN Base.length := hA.closedN henv hBase
      have hBase' : CtxClosed (A :: Base) := ⟨hBase, hAClosed⟩
      simpa [List.append_assoc] using
        natOnTelWeakR henv hBase' hAs Tail

theorem natSelfSpine {env : VEnv} {univs : Nat} :
    ∀ (As : List VExpr) (B : VExpr) (Gamma : List VExpr),
      env.SpineWF univs (As.reverse ++ Gamma)
        ((VExpr.forallN As B).liftN As.length)
        (VExpr.bvarRevRange 0 As.length) B
  | [], B, Gamma => by
      simpa [VExpr.forallN, VExpr.bvarRevRange] using
        (VEnv.SpineWF.nil : env.SpineWF univs Gamma B [] B)
  | A :: As, B, Gamma => by
      have harg : env.HasType univs
          ((A :: As).reverse ++ Gamma)
          (.bvar As.length) (A.liftN (As.length + 1)) := by
        exact .bvar (by
          have hlookup := Lean4Lean.Lookup.append
            (A := A) As.reverse (Γ := Gamma)
          simpa [List.append_assoc] using hlookup)
      have htail := natSelfSpine (env := env) (univs := univs)
        As B (A :: Gamma)
      have htail' : env.SpineWF univs ((A :: As).reverse ++ Gamma)
          ((VExpr.forallN As B).liftN (As.length + 1) 1 |>.inst
            (.bvar As.length))
          (VExpr.bvarRevRange 0 As.length) B := by
        rw [VExpr.liftN_succ_inst_bvar]
        simpa [List.append_assoc] using htail
      have hout := VEnv.SpineWF.cons harg htail'
      simpa [VExpr.forallN, VExpr.bvarRevRange, VExpr.liftN,
        List.append_assoc] using hout

theorem natReifyLevelWFContext [Params] (Gamma : List SExpr) :
    OnCtx (Gamma.map SExpr.reify) (fun _ A => A.LevelWF Params.univs) := by
  induction Gamma with
  | nil => trivial
  | cons A Gamma ih => exact ⟨ih, SExpr.reify_levelWF A⟩

/-- Weakening specialized to the Nat fixture.  Unlike the generic theorem,
this needs only the already-built constructor half of the prospective
semantic instance; constant patterns are impossible in `NatPat`. -/
theorem natStrongWeak (univs : Nat)
    {rho : Lift} {Gamma Gamma' : List (@SExpr (natParams univs))}
    {e1 e2 A : @SExpr (natParams univs)}
    (W : @Ctx.Lift' (natParams univs) rho Gamma Gamma')
    (H : @IsDefEqStrong (natParams univs) Gamma e1 e2 A) :
    @IsDefEqStrong (natParams univs) Gamma'
      (@SExpr.lift' (natParams univs) e1 rho)
      (@SExpr.lift' (natParams univs) e2 rho)
      (@SExpr.lift' (natParams univs) A rho) := by
  letI : Params := natParams univs
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
      (natCtor univs (Gamma := Gamma') hreg hlen cl).1
    have hF' : ∀ cl, IsDefEqStrong Gamma'
        (SExpr.mkInst ls ci.type) ((F' cl).rhs ls) (.sort (F' cl).u) := by
      intro cl
      exact (natCtor univs (Gamma := Gamma') hreg hlen cl).2
    have hDef' : ∀ {r : (Pattern.const c).RHS × (Pattern.const c).Check},
        Params.Pat (.const c) r →
        IsDefEqStrong Gamma' (r.1.applyS ls Empty.elim) (.const c ls)
          (SExpr.mkInst ls ci.type) := by
      intro r hpat
      exact (natPat_no_const univs hpat).elim
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
    exact (natPat_no_const univs action.pat).elim
  | extra action _ _ ihLeft ihRight =>
    have hRight := ihRight W
    rw [Pattern.RHS.lift'_applyS] at hRight
    simpa only [Pattern.RHS.lift'_applyS] using
      IsDefEqStrong.extra (action.weak' W) (ihLeft W) hRight

theorem natZeroStrong (univs : Nat)
    (Gamma : List (@SExpr (natParams univs))) :
    @IsDefEqStrong (natParams univs) Gamma
      (@SExpr.const (natParams univs) ``Nat.zero [])
      (@SExpr.const (natParams univs) ``Nat.zero [])
      (@SExpr.const (natParams univs) ``Nat []) := by
  letI : Params := natParams univs
  let F : ∀ cl : CtorBundle.IsCtor ``Nat.zero,
      CtorBundle ``Nat.zero cl := fun cl =>
    (natCtor univs (Gamma := Gamma) (ls := []) (by rfl) rfl cl).1
  refine .const (ci := InductiveFixtures.natType.ctors[0].toVConstant)
    (u := SLevel.succ SLevel.zero) (by rfl) rfl
    (natTypeStrong univs Gamma) F ?_ ?_
  · intro cl
    exact (natCtor univs (Gamma := Gamma) (ls := []) (by rfl) rfl cl).2
  · intro r hpat
    exact (natPat_no_const univs hpat).elim

theorem natSuccStrong (univs : Nat)
    (Gamma : List (@SExpr (natParams univs))) :
    @IsDefEqStrong (natParams univs) Gamma
      (@SExpr.const (natParams univs) ``Nat.succ [])
      (@SExpr.const (natParams univs) ``Nat.succ [])
      (@SExpr.forallE (natParams univs)
        (@SExpr.const (natParams univs) ``Nat [])
        (@SExpr.const (natParams univs) ``Nat [])) := by
  letI : Params := natParams univs
  let one := SLevel.succ SLevel.zero
  let F : ∀ cl : CtorBundle.IsCtor ``Nat.succ,
      CtorBundle ``Nat.succ cl := fun cl =>
    (natCtor univs (Gamma := Gamma) (ls := [])
      InductiveReplayFixtures.nat_succ_env_lookup rfl cl).1
  refine .const (ci := InductiveFixtures.natType.ctors[1].toVConstant)
    (u := SLevel.imax one one)
    InductiveReplayFixtures.nat_succ_env_lookup rfl ?_ F ?_ ?_
  · rw [probeNatSuccCtorTypeV_eq]
    change IsDefEqStrong Gamma
      (.forallE (.const ``Nat []) (.const ``Nat []))
      (.forallE (.const ``Nat []) (.const ``Nat []))
      (.sort (SLevel.imax one one))
    exact .forallEDF (natTypeStrong univs Gamma)
      (natTypeStrong univs (.const ``Nat [] :: Gamma))
      (natTypeStrong univs (.const ``Nat [] :: Gamma))
  · intro cl
    exact (natCtor univs (Gamma := Gamma) (ls := [])
      InductiveReplayFixtures.nat_succ_env_lookup rfl cl).2
  · intro r hpat
    exact (natPat_no_const univs hpat).elim

theorem natRec_not_ctor (univs : Nat)
    (cl : @CtorBundle.IsCtor (natParams univs) ``Nat.rec) : False := by
  letI : Params := natParams univs
  have hshape : ctorLike cl.cl.1 = true := by
    have hs := cl.cl.2.2
    cases hc : cl.cl.1 <;> simp [ctorLike, hc] at hs ⊢
  rcases natClassify_ctor_cases cl.cl.2.1 hshape with h | h
  · simp at h
  · simp at h

theorem probeNatTypeTypeV_eq :
    InductiveFixtures.natType.type =
      VExpr.sort (VLevel.succ VLevel.zero) := by
  native_decide

/-- Canonical informative semantic observation of the closed Nat type at
any positive shape level.  This is the domain witness used when a registered
recursor telescope is specialized to an actual constructor. -/
noncomputable def natTypeSemanticWitness (univs : Nat)
    (ρ : @Valuation (natParams univs)) (n : Nat) :
    letI : Params := natParams univs
    LE_Interp.Witness ρ (WShape.indTy : WShape (n + 1)).T
      (.const ``Nat []) := by
  letI : Params := natParams univs
  have hsort : LE_Interp.Witness ρ
      (WShape.type : WShape (n + 1)).T
      (SExpr.mkInst [] InductiveFixtures.natType.type) := by
    rw [probeNatTypeTypeV_eq]
    exact .sort (by
      change TShape.sort true ≤ TShape.sort
        (SLevel.succ SLevel.zero ≠ SLevel.zero)
      simpa using TShape.LE.rfl)
  exact .const InductiveReplayFixtures.nat_type_env_lookup rfl
    TShape.LE.rfl (WShape.HasType.T_iff.2 WShape.HasType.indTy) hsort
    (LE_Interp.Const.indTy (R := fun _ _ => False)
      (by change natClassify ``Nat = some (.indTy 0); rfl)
      TShape.LE.rfl)
    nofun

/-- Canonical informative witness for the closed zero constructor at any
positive shape level. -/
noncomputable def natZeroSemanticWitness (univs : Nat)
    (ρ : @Valuation (natParams univs)) (n : Nat) :
    letI : Params := natParams univs
    LE_Interp.Witness ρ
      (WShape.ctor' ``Nat.zero [] : WShape (n + 1)).T
      (.const ``Nat.zero []) := by
  letI : Params := natParams univs
  have hreg : natFinalEnv.constants ``Nat.zero =
      some InductiveFixtures.natType.ctors[0].toVConstant := by
    rfl
  exact .const hreg rfl TShape.LE.rfl
    (WShape.HasType.T_iff.2 WShape.HasType.ctor')
    (natTypeSemanticWitness univs ρ n)
    (LE_Interp.Const.ctor (R := fun _ _ => False)
      (by change natClassify ``Nat.zero = some (.ctor 0); rfl)
      TShape.LE.rfl)
    nofun

/-- Interpret `Nat.succ` applied to the newest bound variable at the
constructor shape generated from one strictly lower field observation.

The binder carries the lifted field shape.  A larger semantic binder value
is also accepted, which is the monotone branch needed by a singleton Pi
telescope.  The constructor evaluator still records the original lower
field in its result, making the source-depth drop explicit. -/
noncomputable def natSuccBvarSemanticWitness (univs : Nat)
    [_semantic : @Params.Semantic (natParams univs)] :
    letI : Params := natParams univs
    ∀ {n : Nat} {ρ : Valuation} (field : WShape n)
      (value : WShape (n + 1))
      (_hfield : (field.lift (n + 1)).HasType
        (.indTy : WShape (n + 1)))
      (_hvalue : field.lift (n + 1) ≤ value),
    LE_Interp.Witness (ρ.push value.T)
      (WShape.ctor' ``Nat.succ [field]).T
      ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0)) := by
  letI : Params := natParams univs
  letI : Params.Semantic := _semantic
  intro n ρ field value hfield hvalue
  let arg : WShape (n + 1) := field.lift (n + 1)
  let result : WShape (n + 1) := WShape.ctor' ``Nat.succ [field]
  let termFun : WShapeFun (n + 1) := .single arg result
  let typeFun : WShapeFun (n + 1) := .single arg .indTy
  have hresult : result.HasType (.indTy : WShape (n + 1)) := by
    exact WShape.HasType.ctor'
  have htermFun : termFun.NonZero := by
    apply WShapeFun.NonZero.iff.2
    refine ⟨(arg, result), WShapeFun.mem_single.2 (.inl rfl), ?_⟩
    intro hbot
    have : result = .bot := WShape.le_bot.1 hbot
    have hnotStruct : IsStruct ``Nat.succ = false := by
      change (natClassify ``Nat.succ matches some (.etaCtor ..)) = false
      rfl
    simp only [result, WShape.ctor', hnotStruct, Bool.false_eq_true,
      false_implies, dif_pos] at this
    cases congrArg (·.1) this
  have htermTyped : (WShape.lam termFun htermFun).HasType
      (.forallE (.indTy : WShape (n + 1)) typeFun) := by
    rw [WShape.lam_eq_lam']
    apply WShape.HasType.lam
    refine WShape.HasTypeLam.iff'.2 ⟨?_, ?_, fun x => ?_⟩
    · refine WShape.HasTypePi.def.2
        ⟨WShape.HasDom.single.2 (.inl hfield), ?_⟩
      intro x y hxy
      obtain ⟨rfl, rfl⟩ | ⟨_, rfl, rfl⟩ :=
        WShapeFun.mem_single.1 hxy
      · exact WShape.HasType.indTy
      · exact .bot' .sort
    · exact WShape.HasDom.single.2 (.inl hfield)
    · simp only [termFun, typeFun, WShapeFun.single_app]
      split
      · exact hresult
      · exact .bot' (.bot' .sort)
  have htype : LE_Interp.Witness (ρ.push value.T)
      (WShape.forallE (.indTy : WShape (n + 1)) typeFun).T
      (SExpr.forallE (SExpr.const ``Nat []) (SExpr.const ``Nat [])) := by
    refine .forallE
      (natTypeSemanticWitness univs (ρ.push value.T) n)
      (natTypeSemanticWitness univs (ρ.push value.T) n)
      (WShape.HasDom.single.2 (.inl hfield)) (fun x _ => ?_)
      TShape.LE.rfl
    simp only [WShapeFun.single_app]
    split
    · exact natTypeSemanticWitness univs ((ρ.push value.T).push x.T) n
    · exact .bot
  have hconst : LE_Interp.Const ``Nat.succ [] (fun _ _ => False)
      ([] : List (WShape (n + 1)))
      (WShape.lam termFun htermFun).T := by
    refine LE_Interp.Const.lam (R := fun _ _ => False) (f := termFun)
        (fun x y hmem => ?_) ?_
    · obtain ⟨rfl, rfl⟩ | ⟨_, rfl, rfl⟩ :=
        WShapeFun.mem_single.1 hmem
      · refine LE_Interp.Const.ctor
          (by change natClassify ``Nat.succ = some (.ctor 1); rfl) ?_
        have hlift : result.lift (n + 2) =
            WShape.ctor' ``Nat.succ [arg] := by
          simp only [result, arg, WShape.lift_ctor' (Nat.le_succ n),
            List.map_cons, List.map_nil]
        exact (TShape.lift_eqv (Nat.le_succ (n + 1))).2.trans
          (by rw [hlift]; exact TShape.LE.rfl)
      · exact LE_Interp.Const.bot
    · rw [WShape.lam_eq_lam']
      exact TShape.LE.rfl
  have hfun : LE_Interp.Witness (ρ.push value.T)
      (WShape.lam termFun htermFun).T (SExpr.const ``Nat.succ []) := by
    refine .const InductiveReplayFixtures.nat_succ_env_lookup rfl
      TShape.LE.rfl htermTyped.T ?_ hconst (fun _ _ h => h.elim)
    simpa [probeNatSuccCtorTypeV_eq, SExpr.mkInst] using htype
  have harg : LE_Interp.Witness (ρ.push value.T) arg.T (SExpr.bvar 0) :=
    .bvar hvalue.T
  have happ := LE_Interp.Witness.app hfun harg TShape.LE.rfl
  simpa only [WShape.lam_eq_lam', WShape.lam'_app, termFun,
    WShapeFun.single_app, WShape.LE.rfl, ↓reduceIte, arg, result] using happ

/--
info: 'Lean4Lean.SExpr.ParamsD0.natSuccBvarSemanticWitness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms natSuccBvarSemanticWitness

/-- Interpret `Nat.succ (bvar 0)` at the exact predecessor element/type
shapes selected by a recursive capture.  The constructor result retains the
literal lower field observation; only the binder value may dominate the
selected predecessor element. -/
noncomputable def natSuccBvarSemanticWitnessAligned (univs : Nat)
    [semantic : @Params.Semantic (natParams univs)] :
    letI : Params := natParams univs
    ∀ {n : Nat} {ρ : Valuation} (field : WShape n)
      (predElem predType value : WShape (n + 1)),
    (field.lift (n + 1)) ≤ predElem →
    predElem.HasType predType →
    predElem ≤ value →
    LE_Interp.Witness ρ predType.T (.const ``Nat []) →
    LE_Interp.Witness (ρ.push value.T)
      (WShape.ctor' ``Nat.succ [field]).T
      ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0)) := by
  letI : Params := natParams univs
  letI : Params.Semantic := semantic
  intro n ρ field predElem predType value hfield hpred hvalue hNat
  let result : WShape (n + 1) := WShape.ctor' ``Nat.succ [field]
  let termFun : WShapeFun (n + 1) := .single predElem result
  let typeFun : WShapeFun (n + 1) := .single predElem .indTy
  have hresult : result.HasType (.indTy : WShape (n + 1)) := by
    exact WShape.HasType.ctor'
  have htermFun : termFun.NonZero := by
    apply WShapeFun.NonZero.iff.2
    refine ⟨(predElem, result), WShapeFun.mem_single.2 (.inl rfl), ?_⟩
    intro hbot
    have : result = .bot := WShape.le_bot.1 hbot
    have hnotStruct : IsStruct ``Nat.succ = false := by
      change (natClassify ``Nat.succ matches some (.etaCtor ..)) = false
      rfl
    simp only [result, WShape.ctor', hnotStruct, Bool.false_eq_true,
      false_implies, dif_pos] at this
    cases congrArg (·.1) this
  have htermTyped : (WShape.lam termFun htermFun).HasType
      (.forallE predType typeFun) := by
    rw [WShape.lam_eq_lam']
    apply WShape.HasType.lam
    refine WShape.HasTypeLam.iff'.2 ⟨?_, ?_, fun x => ?_⟩
    · refine WShape.HasTypePi.def.2
        ⟨WShape.HasDom.single.2 (.inl hpred), ?_⟩
      intro x y hxy
      obtain ⟨rfl, rfl⟩ | ⟨_, rfl, rfl⟩ :=
        WShapeFun.mem_single.1 hxy
      · exact WShape.HasType.indTy
      · exact .bot' .sort
    · exact WShape.HasDom.single.2 (.inl hpred)
    · simp only [termFun, typeFun, WShapeFun.single_app]
      split
      · exact hresult
      · exact .bot' (.bot' .sort)
  have htype : LE_Interp.Witness (ρ.push value.T)
      (WShape.forallE predType typeFun).T
      (SExpr.forallE (SExpr.const ``Nat []) (SExpr.const ``Nat [])) := by
    have hNatWeak : LE_Interp.Witness (ρ.push value.T)
        predType.T (.const ``Nat []) := by
      simpa using hNat.weak (x := value.T)
    refine .forallE hNatWeak hNatWeak
      (WShape.HasDom.single.2 (.inl hpred)) (fun x _ => ?_)
      TShape.LE.rfl
    simp only [typeFun, WShapeFun.single_app]
    split
    · exact natTypeSemanticWitness univs ((ρ.push value.T).push x.T) n
    · exact .bot
  have hconst : LE_Interp.Const ``Nat.succ [] (fun _ _ => False)
      ([] : List (WShape (n + 1)))
      (WShape.lam termFun htermFun).T := by
    refine LE_Interp.Const.lam (R := fun _ _ => False) (f := termFun)
        (fun x y hmem => ?_) ?_
    · obtain ⟨rfl, rfl⟩ | ⟨_, rfl, rfl⟩ :=
        WShapeFun.mem_single.1 hmem
      · refine LE_Interp.Const.ctor
          (by change natClassify ``Nat.succ = some (.ctor 1); rfl) ?_
        have hlift : result.lift (n + 2) =
            WShape.ctor' ``Nat.succ [field.lift (n + 1)] := by
          simp only [result, WShape.lift_ctor' (Nat.le_succ n),
            List.map_cons, List.map_nil]
        refine (TShape.lift_eqv (Nat.le_succ (n + 1))).2.trans ?_
        rw [hlift]
        exact (WShape.ctor'_le_ctor'
          (List.Forall₂.cons hfield List.Forall₂.nil)).T
      · exact LE_Interp.Const.bot
    · rw [WShape.lam_eq_lam']
      exact TShape.LE.rfl
  have hfun : LE_Interp.Witness (ρ.push value.T)
      (WShape.lam termFun htermFun).T (SExpr.const ``Nat.succ []) := by
    refine .const InductiveReplayFixtures.nat_succ_env_lookup rfl
      TShape.LE.rfl htermTyped.T ?_ hconst (fun _ _ h => h.elim)
    simpa [probeNatSuccCtorTypeV_eq, SExpr.mkInst] using htype
  have harg : LE_Interp.Witness (ρ.push value.T)
      predElem.T (SExpr.bvar 0) := .bvar hvalue.T
  have happ := LE_Interp.Witness.app hfun harg TShape.LE.rfl
  simpa only [WShape.lam_eq_lam', WShape.lam'_app, termFun,
    WShapeFun.single_app, WShape.LE.rfl, ↓reduceIte, result] using happ

/--
info: 'Lean4Lean.SExpr.ParamsD0.natSuccBvarSemanticWitnessAligned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms natSuccBvarSemanticWitnessAligned

/-- Specialize the exact registered `Nat.rec` observation at `Nat.zero` and
retain only the three generated-rule captures.  The result shape is the
sparse singleton telescope determined by the same motive, zero-minor, and
successor-minor layers stored in the registered trace. -/
noncomputable def natZeroRegisteredRuleTypeSemanticWitness (univs : Nat)
    [semantic : @Params.Semantic (natParams univs)] :
    letI : Params := natParams univs
    ∀ {n : Nat} {Γ : List SExpr} {ρ : Valuation} {level : SLevel}
      {majorX majorY succX succY zeroX zeroY motiveX motiveY A : SExpr}
      {succShape zeroShape motiveShape : WShape (n + 1)}
      {outTy : WShape (n + 1)},
    ∀ (H : LR.DirectRegisteredTypeTrace Γ ρ
        (SExpr.mkInst [level]
          (VInductDecl.recConst 0 ``Nat 0 InductiveFixtures.natType).type)
        [majorX, succX, zeroX, motiveX]
        [majorY, succY, zeroY, motiveY]
        [(.ctor' ``Nat.zero []), succShape, zeroShape, motiveShape]
        A outTy),
      ∀ view : LR.DirectRegisteredTypeTrace.FourView H,
      LE_Interp.Witness ρ (view.sparsePrefix outTy).T
        (probeNatZeroRuleType univs level) := by
  letI : Params := natParams univs
  letI : Params.Semantic := semantic
  intro n Γ ρ level majorX majorY succX succY zeroX zeroY
    motiveX motiveY A succShape zeroShape motiveShape outTy H view
  let NatS : SExpr := SExpr.const ``Nat []
  let Motive : SExpr := SExpr.forallE NatS (SExpr.sort level)
  let MinorZero : SExpr :=
    (SExpr.bvar 0).app (SExpr.const ``Nat.zero [])
  let MinorSucc : SExpr :=
    SExpr.forallE NatS <|
      SExpr.forallE ((SExpr.bvar 2).app (SExpr.bvar 0)) <|
        (SExpr.bvar 3).app
          ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))
  let MajorTail : SExpr :=
    SExpr.forallE NatS ((SExpr.bvar 3).app (SExpr.bvar 0))
  let ZeroResult : SExpr :=
    (SExpr.bvar 2).app (SExpr.const ``Nat.zero [])
  have hroot0 := view.first.previous.nilWitness
  have hroot1 : LE_Interp.Witness ρ
      (WShape.forallE view.first.domain view.first.codomain).T
      (SExpr.mkInst [level]
        (VInductDecl.recConst 0 ``Nat 0 InductiveFixtures.natType).type) := by
    simpa only [view.first.previous.nilResult_eq] using hroot0
  simp only [probeNatRecTypeV_eq] at hroot1
  have hroot : LE_Interp.Witness ρ
      (WShape.forallE view.first.domain view.first.codomain).T
      (SExpr.forallE Motive
        (SExpr.forallE MinorZero (SExpr.forallE MinorSucc MajorTail))) := by
    simpa [probeNatRecTypeV, Motive, MinorZero, MinorSucc, MajorTail,
      NatS, SExpr.mkInst, probeInstVParamZero] using hroot1
  have hfirstLE : view.first.domainLevel ≤ n + 3 :=
    Nat.le_trans view.first.levelLE (by omega)
  have hmotiveTy : (motiveShape.lift (n + 3)).HasType
      (view.first.domain.lift (n + 3)) := by
    simpa only [WShape.lift_lift (.inl view.first.levelLE)] using
      (WShape.HasType.lift (n := n + 1) (n' := n + 3) (by omega)).2
        view.first.hasType
  have hrootLift : LE_Interp.Witness ρ
      (WShape.forallE (view.first.domain.lift (n + 3))
        (view.first.codomain.lift (n + 3))).T
      (SExpr.forallE Motive
        (SExpr.forallE MinorZero (SExpr.forallE MinorSucc MajorTail))) := by
    simpa only [WShape.lift_forallE hfirstLE] using
      hroot.mono (TShape.lift_eqv
        (a := (WShape.forallE
          view.first.domain view.first.codomain).T)
        (Nat.succ_le_succ hfirstLE)).1
  change LE_Interp.Witness ρ
    (WShape.forallE (view.first.domain.lift (n + 3))
      (WShapeFun.single (motiveShape.lift (n + 3)) <|
        WShape.forallE (view.second.domain.lift (n + 2))
          (WShapeFun.single (zeroShape.lift (n + 2)) <|
            WShape.forallE (view.third.domain.lift (n + 1))
              (WShapeFun.single succShape outTy)))).T
    (SExpr.forallE Motive
      (SExpr.forallE MinorZero (SExpr.forallE MinorSucc ZeroResult)))
  refine LE_Interp.Witness.forallE_singleMap hfirstLE hroot
    (motiveShape.lift (n + 3))
    (WShape.forallE (view.second.domain.lift (n + 2))
      (WShapeFun.single (zeroShape.lift (n + 2)) <|
        WShape.forallE (view.third.domain.lift (n + 1))
          (WShapeFun.single succShape outTy))) hmotiveTy ?_
  intro motive hmotive
  have hrest1Raw := view.first.bodyWitnessLift (by omega)
    hrootLift motive hmotive
  have hsecondLE : view.second.domainLevel ≤ n + 2 :=
    Nat.le_trans view.second.levelLE (by omega)
  have hrest1 : LE_Interp.Witness (ρ.push motive.T)
      (WShape.forallE (view.second.domain.lift (n + 2))
        (view.second.codomain.lift (n + 2))).T
      (SExpr.forallE MinorZero (SExpr.forallE MinorSucc MajorTail)) := by
    simpa only [WShape.lift_forallE hsecondLE] using hrest1Raw
  have hzeroTy : (zeroShape.lift (n + 2)).HasType
      (view.second.domain.lift (n + 2)) := by
    simpa only [WShape.lift_lift (.inl view.second.levelLE)] using
      (WShape.HasType.lift (n := n + 1) (n' := n + 2) (by omega)).2
        view.second.hasType
  refine LE_Interp.Witness.forallE_singleMapSelf
    (p := zeroShape.lift (n + 2))
    (result := WShape.forallE (view.third.domain.lift (n + 1))
      (WShapeFun.single succShape outTy)) hrest1 hzeroTy ?_
  intro zero hzero
  have hrest2Raw := view.second.bodyWitnessLift (by omega)
    hrest1 zero hzero
  have hrest2 : LE_Interp.Witness ((ρ.push motive.T).push zero.T)
      (WShape.forallE (view.third.domain.lift (n + 1))
        (view.third.codomain.lift (n + 1))).T
      (SExpr.forallE MinorSucc MajorTail) := by
    simpa only [WShape.lift_forallE view.third.levelLE] using hrest2Raw
  have hsuccTy : succShape.HasType
      (view.third.domain.lift (n + 1)) := view.third.hasType
  refine LE_Interp.Witness.forallE_singleMapSelf
    (p := succShape) (result := outTy) hrest2 hsuccTy ?_
  intro succ hsucc
  have hmajorRaw := view.third.bodyWitnessSelf hrest2 succ hsucc
  have hmajor : LE_Interp.Witness
      (((ρ.push motive.T).push zero.T).push succ.T)
      (WShape.forallE (view.fourth.domain.lift (n + 1))
        (view.fourth.codomain.lift (n + 1))).T MajorTail := by
    simpa only [WShape.lift_forallE view.fourth.levelLE] using
      hmajorRaw.mono (TShape.lift_eqv
        (a := (WShape.forallE
          view.fourth.domain view.fourth.codomain).T)
        (Nat.succ_le_succ view.fourth.levelLE)).1
  have hzeroWitness := natZeroSemanticWitness univs
    (((ρ.push motive.T).push zero.T).push succ.T) n
  have hterminal0 := hmajor.forallE_inst hzeroWitness
  have hterminal : LE_Interp.Witness
      (((ρ.push motive.T).push zero.T).push succ.T)
      outTy.T ZeroResult := by
    have houtLE : outTy.T ≤
        ((view.fourth.codomain.lift (n + 1)).app
          (WShape.ctor' ``Nat.zero [])).T := by
      rw [view.fourth.outTy_eq]
      exact TShape.LE.rfl
    exact (by
      simpa [MajorTail, ZeroResult, SExpr.inst, SExpr.subst,
        Subst.one, Subst.cons, Subst.id, NatS] using
        hterminal0.mono houtLE)
  exact hterminal

/--
info: 'Lean4Lean.SExpr.ParamsD0.natZeroRegisteredRuleTypeSemanticWitness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 probeNatRecTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms natZeroRegisteredRuleTypeSemanticWitness

/-- Build the registered successor-rule type at the exact sparse telescope
selected by a recursor trace and a native predecessor field.

The fourth binder is not synthesized from an unrelated semantic alignment:
its element is precisely the one-level lift of the constructor field.  The
body weakens the registered major tail under that binder and instantiates it
with `Nat.succ (bvar 0)`, preserving the constructor evaluator's lower field
observation throughout. -/
noncomputable def natSuccRegisteredRuleTypeSemanticWitness (univs : Nat)
    [semantic : @Params.Semantic (natParams univs)] :
    letI : Params := natParams univs
    ∀ {n : Nat} {Γ : List SExpr} {ρ : Valuation} {level : SLevel}
      {majorX majorY succX succY zeroX zeroY motiveX motiveY A : SExpr}
      {field : WShape n}
      {succShape zeroShape motiveShape : WShape (n + 1)}
      {outTy : WShape (n + 1)},
    ∀ (H : LR.DirectRegisteredTypeTrace Γ ρ
        (SExpr.mkInst [level]
          (VInductDecl.recConst 0 ``Nat 0 InductiveFixtures.natType).type)
        [majorX, succX, zeroX, motiveX]
        [majorY, succY, zeroY, motiveY]
        [(WShape.ctor' ``Nat.succ [field]), succShape, zeroShape, motiveShape]
        A outTy),
      ∀ view : LR.DirectRegisteredTypeTrace.FourView H,
      (field.lift (n + 1)).HasType (.indTy : WShape (n + 1)) →
      LE_Interp.Witness ρ
        (natSuccCaptureTower (field.lift (n + 1)) succShape
          zeroShape motiveShape .indTy
          (view.third.domain.lift (n + 1))
          (view.second.domain.lift (n + 1))
          (view.first.domain.lift (n + 1)) outTy).T
        (probeNatSuccRuleType univs level) := by
  letI : Params := natParams univs
  letI : Params.Semantic := semantic
  intro n Γ ρ level majorX majorY succX succY zeroX zeroY
    motiveX motiveY A field succShape zeroShape motiveShape outTy H view
    hfield
  let NatS : SExpr := SExpr.const ``Nat []
  let Motive : SExpr := SExpr.forallE NatS (SExpr.sort level)
  let MinorZero : SExpr :=
    (SExpr.bvar 0).app (SExpr.const ``Nat.zero [])
  let MinorSucc : SExpr :=
    SExpr.forallE NatS <|
      SExpr.forallE ((SExpr.bvar 2).app (SExpr.bvar 0)) <|
        (SExpr.bvar 3).app
          ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))
  let MajorTail : SExpr :=
    SExpr.forallE NatS ((SExpr.bvar 3).app (SExpr.bvar 0))
  let SuccResult : SExpr :=
    (SExpr.bvar 3).app
      ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0))
  have hroot0 := view.first.previous.nilWitness
  have hroot1 : LE_Interp.Witness ρ
      (WShape.forallE view.first.domain view.first.codomain).T
      (SExpr.mkInst [level]
        (VInductDecl.recConst 0 ``Nat 0 InductiveFixtures.natType).type) := by
    simpa only [view.first.previous.nilResult_eq] using hroot0
  simp only [probeNatRecTypeV_eq] at hroot1
  have hroot : LE_Interp.Witness ρ
      (WShape.forallE view.first.domain view.first.codomain).T
      (SExpr.forallE Motive
        (SExpr.forallE MinorZero (SExpr.forallE MinorSucc MajorTail))) := by
    simpa [probeNatRecTypeV, Motive, MinorZero, MinorSucc, MajorTail,
      NatS, SExpr.mkInst, probeInstVParamZero] using hroot1
  have hfirstLE : view.first.domainLevel ≤ n + 4 :=
    Nat.le_trans view.first.levelLE (by omega)
  have hmotiveTy : (motiveShape.lift (n + 4)).HasType
      (view.first.domain.lift (n + 4)) := by
    simpa only [WShape.lift_lift (.inl view.first.levelLE)] using
      (WShape.HasType.lift (n := n + 1) (n' := n + 4) (by omega)).2
        view.first.hasType
  have hrootLift : LE_Interp.Witness ρ
      (WShape.forallE (view.first.domain.lift (n + 4))
        (view.first.codomain.lift (n + 4))).T
      (SExpr.forallE Motive
        (SExpr.forallE MinorZero (SExpr.forallE MinorSucc MajorTail))) := by
    simpa only [WShape.lift_forallE hfirstLE] using
      hroot.mono (TShape.lift_eqv
        (a := (WShape.forallE view.first.domain view.first.codomain).T)
        (Nat.succ_le_succ hfirstLE)).1
  simp only [natSuccCaptureTower, probeNatSuccRuleType,
    WShape.lift_lift (.inl view.first.levelLE),
    WShape.lift_lift (.inl view.second.levelLE),
    WShape.lift_lift (.inl view.third.levelLE)]
  change LE_Interp.Witness ρ
    (WShape.forallE (view.first.domain.lift (n + 4))
      (WShapeFun.single (motiveShape.lift (n + 4)) <|
        WShape.forallE (view.second.domain.lift (n + 3))
          (WShapeFun.single (zeroShape.lift (n + 3)) <|
            WShape.forallE (view.third.domain.lift (n + 2))
              (WShapeFun.single (succShape.lift (n + 2)) <|
                WShape.forallE (.indTy : WShape (n + 1))
                  (WShapeFun.single (field.lift (n + 1)) outTy))))).T
    (SExpr.forallE Motive <|
      SExpr.forallE MinorZero <|
        SExpr.forallE MinorSucc <| SExpr.forallE NatS SuccResult)
  refine LE_Interp.Witness.forallE_singleMap hfirstLE hroot
    (motiveShape.lift (n + 4))
    (WShape.forallE (view.second.domain.lift (n + 3))
      (WShapeFun.single (zeroShape.lift (n + 3)) <|
        WShape.forallE (view.third.domain.lift (n + 2))
          (WShapeFun.single (succShape.lift (n + 2)) <|
            WShape.forallE (.indTy : WShape (n + 1))
              (WShapeFun.single (field.lift (n + 1)) outTy))))
    hmotiveTy ?_
  intro motive hmotive
  have hrest1Raw := view.first.bodyWitnessLift (by omega)
    hrootLift motive hmotive
  have hsecondLE : view.second.domainLevel ≤ n + 3 :=
    Nat.le_trans view.second.levelLE (by omega)
  have hrest1 : LE_Interp.Witness (ρ.push motive.T)
      (WShape.forallE (view.second.domain.lift (n + 3))
        (view.second.codomain.lift (n + 3))).T
      (SExpr.forallE MinorZero (SExpr.forallE MinorSucc MajorTail)) := by
    simpa only [WShape.lift_forallE hsecondLE] using hrest1Raw
  have hzeroTy : (zeroShape.lift (n + 3)).HasType
      (view.second.domain.lift (n + 3)) := by
    simpa only [WShape.lift_lift (.inl view.second.levelLE)] using
      (WShape.HasType.lift (n := n + 1) (n' := n + 3) (by omega)).2
        view.second.hasType
  refine LE_Interp.Witness.forallE_singleMapSelf
    (p := zeroShape.lift (n + 3))
    (result := WShape.forallE (view.third.domain.lift (n + 2))
      (WShapeFun.single (succShape.lift (n + 2)) <|
        WShape.forallE (.indTy : WShape (n + 1))
          (WShapeFun.single (field.lift (n + 1)) outTy)))
    hrest1 hzeroTy ?_
  intro zero hzero
  have hrest2Raw := view.second.bodyWitnessLift (by omega)
    hrest1 zero hzero
  have hthirdLE : view.third.domainLevel ≤ n + 2 :=
    Nat.le_trans view.third.levelLE (by omega)
  have hrest2 : LE_Interp.Witness ((ρ.push motive.T).push zero.T)
      (WShape.forallE (view.third.domain.lift (n + 2))
        (view.third.codomain.lift (n + 2))).T
      (SExpr.forallE MinorSucc MajorTail) := by
    simpa only [WShape.lift_forallE hthirdLE] using hrest2Raw
  have hsuccTy : (succShape.lift (n + 2)).HasType
      (view.third.domain.lift (n + 2)) := by
    simpa only [WShape.lift_lift (.inl view.third.levelLE)] using
      (WShape.HasType.lift (n := n + 1) (n' := n + 2) (by omega)).2
        view.third.hasType
  refine LE_Interp.Witness.forallE_singleMapSelf
    (p := succShape.lift (n + 2))
    (result := WShape.forallE (.indTy : WShape (n + 1))
      (WShapeFun.single (field.lift (n + 1)) outTy))
    hrest2 hsuccTy ?_
  intro succ hsucc
  have hmajorRaw := view.third.bodyWitnessLift (by omega)
    hrest2 succ hsucc
  have hmajor : LE_Interp.Witness
      (((ρ.push motive.T).push zero.T).push succ.T)
      (WShape.forallE (view.fourth.domain.lift (n + 1))
        (view.fourth.codomain.lift (n + 1))).T MajorTail := by
    simpa only [WShape.lift_forallE view.fourth.levelLE] using hmajorRaw
  have hnat := natTypeSemanticWitness univs
    (((ρ.push motive.T).push zero.T).push succ.T) n
  refine .forallE hnat hnat
    (WShape.HasDom.single.2 (.inl hfield)) (fun pred _ => ?_)
    TShape.LE.rfl
  rw [WShapeFun.single_app]
  split
  · rename_i hpred
    have hsuccPred := natSuccBvarSemanticWitness univs
      (ρ := ((ρ.push motive.T).push zero.T).push succ.T)
      field pred hfield hpred
    have hmajorWeak := hmajor.weak (x := pred.T)
    have hterminal0 := hmajorWeak.forallE_inst hsuccPred
    have hterminal : LE_Interp.Witness
        ((((ρ.push motive.T).push zero.T).push succ.T).push pred.T)
        outTy.T SuccResult := by
      have houtLE : outTy.T ≤
          ((view.fourth.codomain.lift (n + 1)).app
            (WShape.ctor' ``Nat.succ [field])).T := by
        rw [view.fourth.outTy_eq]
        exact TShape.LE.rfl
      simpa [MajorTail, SuccResult, SExpr.inst, SExpr.subst, Subst.one,
        Subst.cons, Subst.id, NatS] using hterminal0.mono houtLE
    exact hterminal
  · exact .bot

/--
info: 'Lean4Lean.SExpr.ParamsD0.natSuccRegisteredRuleTypeSemanticWitness' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 probeNatRecTypeV_eq._native.native_decide.ax_1_1,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms natSuccRegisteredRuleTypeSemanticWitness

/-- Build the registered successor-rule type at the exact predecessor
element/type shapes retained by the recursive branch.

The semantic Nat witness for the selected type shape is carried in from that
strict branch.  Thus neither predecessor shape is reselected, while the
constructor result still records the literal lower field fixed by the
registered major. -/
noncomputable def natSuccRegisteredRuleTypeSemanticWitnessAligned
    (univs : Nat) [semantic : @Params.Semantic (natParams univs)] :
    letI : Params := natParams univs
    ∀ {n : Nat} {Γ : List SExpr} {ρ : Valuation} {level : SLevel}
      {majorX majorY succX succY zeroX zeroY motiveX motiveY A : SExpr}
      {field : WShape n} {predElem predType : WShape (n + 1)}
      {succShape zeroShape motiveShape : WShape (n + 1)}
      {outTy : WShape (n + 1)},
    ∀ (H : LR.DirectRegisteredTypeTrace Γ ρ
        (SExpr.mkInst [level]
          (VInductDecl.recConst 0 ``Nat 0 InductiveFixtures.natType).type)
        [majorX, succX, zeroX, motiveX]
        [majorY, succY, zeroY, motiveY]
        [(WShape.ctor' ``Nat.succ [field]), succShape, zeroShape, motiveShape]
        A outTy),
      ∀ view : LR.DirectRegisteredTypeTrace.FourView H,
      (field.lift (n + 1)) ≤ predElem →
      predElem.HasType predType →
      LE_Interp.Witness ρ predType.T (.const ``Nat []) →
      LE_Interp.Witness ρ
        (natSuccCaptureTower predElem succShape zeroShape motiveShape
          predType
          (view.third.domain.lift (n + 1))
          (view.second.domain.lift (n + 1))
          (view.first.domain.lift (n + 1)) outTy).T
        (probeNatSuccRuleType univs level) := by
  letI : Params := natParams univs
  letI : Params.Semantic := semantic
  intro n Γ ρ level majorX majorY succX succY zeroX zeroY
    motiveX motiveY A field predElem predType succShape zeroShape
    motiveShape outTy H view hfield hpred hNat
  let NatS : SExpr := SExpr.const ``Nat []
  let Motive : SExpr := SExpr.forallE NatS (SExpr.sort level)
  let MinorZero : SExpr :=
    (SExpr.bvar 0).app (SExpr.const ``Nat.zero [])
  let MinorSucc : SExpr :=
    SExpr.forallE NatS <|
      SExpr.forallE ((SExpr.bvar 2).app (SExpr.bvar 0)) <|
        (SExpr.bvar 3).app
          ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))
  let MajorTail : SExpr :=
    SExpr.forallE NatS ((SExpr.bvar 3).app (SExpr.bvar 0))
  let SuccResult : SExpr :=
    (SExpr.bvar 3).app
      ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0))
  have hroot0 := view.first.previous.nilWitness
  have hroot1 : LE_Interp.Witness ρ
      (WShape.forallE view.first.domain view.first.codomain).T
      (SExpr.mkInst [level]
        (VInductDecl.recConst 0 ``Nat 0 InductiveFixtures.natType).type) := by
    simpa only [view.first.previous.nilResult_eq] using hroot0
  simp only [probeNatRecTypeV_eq] at hroot1
  have hroot : LE_Interp.Witness ρ
      (WShape.forallE view.first.domain view.first.codomain).T
      (SExpr.forallE Motive
        (SExpr.forallE MinorZero (SExpr.forallE MinorSucc MajorTail))) := by
    simpa [probeNatRecTypeV, Motive, MinorZero, MinorSucc, MajorTail,
      NatS, SExpr.mkInst, probeInstVParamZero] using hroot1
  have hfirstLE : view.first.domainLevel ≤ n + 4 :=
    Nat.le_trans view.first.levelLE (by omega)
  have hmotiveTy : (motiveShape.lift (n + 4)).HasType
      (view.first.domain.lift (n + 4)) := by
    simpa only [WShape.lift_lift (.inl view.first.levelLE)] using
      (WShape.HasType.lift (n := n + 1) (n' := n + 4) (by omega)).2
        view.first.hasType
  have hrootLift : LE_Interp.Witness ρ
      (WShape.forallE (view.first.domain.lift (n + 4))
        (view.first.codomain.lift (n + 4))).T
      (SExpr.forallE Motive
        (SExpr.forallE MinorZero (SExpr.forallE MinorSucc MajorTail))) := by
    simpa only [WShape.lift_forallE hfirstLE] using
      hroot.mono (TShape.lift_eqv
        (a := (WShape.forallE view.first.domain view.first.codomain).T)
        (Nat.succ_le_succ hfirstLE)).1
  simp only [natSuccCaptureTower, probeNatSuccRuleType,
    WShape.lift_lift (.inl view.first.levelLE),
    WShape.lift_lift (.inl view.second.levelLE),
    WShape.lift_lift (.inl view.third.levelLE)]
  change LE_Interp.Witness ρ
    (WShape.forallE (view.first.domain.lift (n + 4))
      (WShapeFun.single (motiveShape.lift (n + 4)) <|
        WShape.forallE (view.second.domain.lift (n + 3))
          (WShapeFun.single (zeroShape.lift (n + 3)) <|
            WShape.forallE (view.third.domain.lift (n + 2))
              (WShapeFun.single (succShape.lift (n + 2)) <|
                WShape.forallE predType
                  (WShapeFun.single predElem outTy))))).T
    (SExpr.forallE Motive <|
      SExpr.forallE MinorZero <|
        SExpr.forallE MinorSucc <| SExpr.forallE NatS SuccResult)
  refine LE_Interp.Witness.forallE_singleMap hfirstLE hroot
    (motiveShape.lift (n + 4))
    (WShape.forallE (view.second.domain.lift (n + 3))
      (WShapeFun.single (zeroShape.lift (n + 3)) <|
        WShape.forallE (view.third.domain.lift (n + 2))
          (WShapeFun.single (succShape.lift (n + 2)) <|
            WShape.forallE predType
              (WShapeFun.single predElem outTy))))
    hmotiveTy ?_
  intro motive hmotive
  have hrest1Raw := view.first.bodyWitnessLift (by omega)
    hrootLift motive hmotive
  have hsecondLE : view.second.domainLevel ≤ n + 3 :=
    Nat.le_trans view.second.levelLE (by omega)
  have hrest1 : LE_Interp.Witness (ρ.push motive.T)
      (WShape.forallE (view.second.domain.lift (n + 3))
        (view.second.codomain.lift (n + 3))).T
      (SExpr.forallE MinorZero (SExpr.forallE MinorSucc MajorTail)) := by
    simpa only [WShape.lift_forallE hsecondLE] using hrest1Raw
  have hzeroTy : (zeroShape.lift (n + 3)).HasType
      (view.second.domain.lift (n + 3)) := by
    simpa only [WShape.lift_lift (.inl view.second.levelLE)] using
      (WShape.HasType.lift (n := n + 1) (n' := n + 3) (by omega)).2
        view.second.hasType
  refine LE_Interp.Witness.forallE_singleMapSelf
    (p := zeroShape.lift (n + 3))
    (result := WShape.forallE (view.third.domain.lift (n + 2))
      (WShapeFun.single (succShape.lift (n + 2)) <|
        WShape.forallE predType (WShapeFun.single predElem outTy)))
    hrest1 hzeroTy ?_
  intro zero hzero
  have hrest2Raw := view.second.bodyWitnessLift (by omega)
    hrest1 zero hzero
  have hthirdLE : view.third.domainLevel ≤ n + 2 :=
    Nat.le_trans view.third.levelLE (by omega)
  have hrest2 : LE_Interp.Witness ((ρ.push motive.T).push zero.T)
      (WShape.forallE (view.third.domain.lift (n + 2))
        (view.third.codomain.lift (n + 2))).T
      (SExpr.forallE MinorSucc MajorTail) := by
    simpa only [WShape.lift_forallE hthirdLE] using hrest2Raw
  have hsuccTy : (succShape.lift (n + 2)).HasType
      (view.third.domain.lift (n + 2)) := by
    simpa only [WShape.lift_lift (.inl view.third.levelLE)] using
      (WShape.HasType.lift (n := n + 1) (n' := n + 2) (by omega)).2
        view.third.hasType
  refine LE_Interp.Witness.forallE_singleMapSelf
    (p := succShape.lift (n + 2))
    (result := WShape.forallE predType (WShapeFun.single predElem outTy))
    hrest2 hsuccTy ?_
  intro succ hsucc
  have hmajorRaw := view.third.bodyWitnessLift (by omega)
    hrest2 succ hsucc
  have hmajor : LE_Interp.Witness
      (((ρ.push motive.T).push zero.T).push succ.T)
      (WShape.forallE (view.fourth.domain.lift (n + 1))
        (view.fourth.codomain.lift (n + 1))).T MajorTail := by
    simpa only [WShape.lift_forallE view.fourth.levelLE] using hmajorRaw
  have hnat0 := hNat.weak (x := motive.T)
  have hnat1 := hnat0.weak (x := zero.T)
  have hnat2 := hnat1.weak (x := succ.T)
  have hnat : LE_Interp.Witness
      (((ρ.push motive.T).push zero.T).push succ.T)
      predType.T NatS := by
    simpa [NatS] using hnat2
  refine .forallE hnat hnat
    (WShape.HasDom.single.2 (.inl hpred)) (fun pred _ => ?_)
    TShape.LE.rfl
  rw [WShapeFun.single_app]
  split
  · rename_i hpredLE
    have hsuccPred := natSuccBvarSemanticWitnessAligned univs
      (ρ := ((ρ.push motive.T).push zero.T).push succ.T)
      field predElem predType pred hfield hpred hpredLE hnat
    have hmajorWeak := hmajor.weak (x := pred.T)
    have hterminal0 := hmajorWeak.forallE_inst hsuccPred
    have hterminal : LE_Interp.Witness
        ((((ρ.push motive.T).push zero.T).push succ.T).push pred.T)
        outTy.T SuccResult := by
      have houtLE : outTy.T ≤
          ((view.fourth.codomain.lift (n + 1)).app
            (WShape.ctor' ``Nat.succ [field])).T := by
        rw [view.fourth.outTy_eq]
        exact TShape.LE.rfl
      simpa [MajorTail, SuccResult, SExpr.inst, SExpr.subst, Subst.one,
        Subst.cons, Subst.id, NatS] using hterminal0.mono houtLE
    exact hterminal
  · exact .bot

/--
info: 'Lean4Lean.SExpr.ParamsD0.natSuccRegisteredRuleTypeSemanticWitnessAligned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 probeNatRecTypeV_eq._native.native_decide.ax_1_1,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms natSuccRegisteredRuleTypeSemanticWitnessAligned

/-- Eliminate a reached registered zero site into one synchronized package:
the literal four recursor applications, exact capture/domain relations for
the three generated-rule binders, and the sparse semantic witness of the
actual generated zero-rule type.  Constructor-match inversion is performed
before the dependent trace elimination, so the major shape is literally the
canonical nullary `Nat.zero` observation consumed by the specialization. -/
theorem natZeroRegisteredRecursorRuleViewElim
    (univs : Nat) [semantic : @Params.Semantic (natParams univs)] :
    letI : Params := natParams univs
    ∀ {n : Nat} {Γ : List SExpr} {ρ : Valuation} {level : SLevel}
      {ctorShapes : List (WShape n)}
      {recShapes : List (WShape (n + 1))}
      {mrec : (Pattern.varN (.const ``Nat.rec) 3).Path → TShape}
      {mctor : (Pattern.varN (.const ``Nat.zero) 0).Path → TShape}
      {majorX majorY : SExpr} {recXs recYs : List SExpr}
      {A : SExpr} {outTy : WShape (n + 1)},
    LE_Interp.Matches (n := n + 1)
      (Pattern.varN (.const ``Nat.rec) 3) ``Nat.rec recShapes mrec →
    LE_Interp.Matches (n := n)
      (Pattern.varN (.const ``Nat.zero) 0) ``Nat.zero ctorShapes mctor →
    (H : LR.DirectRegisteredTypeTrace Γ ρ
      (SExpr.mkInst [level]
        (VInductDecl.recConst 0 ``Nat 0 InductiveFixtures.natType).type)
      (majorX :: recXs) (majorY :: recYs)
      ((.ctor' ``Nat.zero ctorShapes.reverse) :: recShapes) A outTy) →
    ∀ {C : Prop},
      (∀ (succX zeroX motiveX succY zeroY motiveY : SExpr)
          (succShape zeroShape motiveShape : WShape (n + 1)),
        ∀ H' : LR.DirectRegisteredTypeTrace Γ ρ
          (SExpr.mkInst [level]
            (VInductDecl.recConst 0 ``Nat 0 InductiveFixtures.natType).type)
          [majorX, succX, zeroX, motiveX]
          [majorY, succY, zeroY, motiveY]
          [(.ctor' ``Nat.zero []), succShape, zeroShape, motiveShape]
          A outTy,
        ∀ view : LR.DirectRegisteredTypeTrace.FourView H',
          LR.DirectCaptureDefEqAligned.AtShapes (LRD Γ)
            (mrec none) succX succY view.third.domainExpr
            succShape (view.third.domain.lift (n + 1)) →
          LR.DirectCaptureDefEqAligned.AtShapes (LRD Γ)
            (mrec (some none)) zeroX zeroY view.second.domainExpr
            zeroShape (view.second.domain.lift (n + 1)) →
          LR.DirectCaptureDefEqAligned.AtShapes (LRD Γ)
            (mrec (some (some none))) motiveX motiveY
            view.first.domainExpr motiveShape
            (view.first.domain.lift (n + 1)) →
          LE_Interp.Witness ρ (view.sparsePrefix outTy).T
            (SExpr.mkInst [level]
              (NatGeneration.rule 0 NatGeneration.flatCtors[0]).type) → C) →
      C := by
  letI : Params := natParams univs
  letI : Params.Semantic := semantic
  intro n Γ ρ level ctorShapes recShapes mrec mctor majorX majorY
    recXs recYs A outTy hrec hctor H C K
  have hctorLen : ctorShapes.length = 0 := hctor.varN_length
  have hctorNil : ctorShapes = [] := List.length_eq_zero_iff.mp hctorLen
  subst ctorShapes
  apply natRegisteredRecursorTrace_fourViewElim univs hrec H
  intro succX zeroX motiveX succY zeroY motiveY
    succShape zeroShape motiveShape H' view hsucc hzero hmotive
  apply K succX zeroX motiveX succY zeroY motiveY
    succShape zeroShape motiveShape H' view hsucc hzero hmotive
  simpa only [probeNatZeroRuleTypeS_eq] using
    natZeroRegisteredRuleTypeSemanticWitness univs H' view

/--
info: 'Lean4Lean.SExpr.ParamsD0.natZeroRegisteredRecursorRuleViewElim' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 probeNatRecTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 probeNatZeroRuleTypeV_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms natZeroRegisteredRecursorRuleViewElim

/-- Relevel the three semantic Nat-zero capture applications to one
consecutive high-level spine.

`LE_Interp.RHS.ShapeSpine` permits each application edge to choose an
unrelated finite representative.  Registered recursor captures, by contrast,
all arrive at the recursor result level.  Raising both sides to one common
level preserves every semantic inequality and lets the exact direct captures
form the singleton Pi tower used by the registered zero-rule witness. -/
theorem natZeroShapeSpine_relevelDirect
    (univs : Nat) [semantic : @Params.Semantic (natParams univs)] :
    letI : Params := natParams univs
    ∀ {n : Nat} {Γ : List SExpr}
      {mrec : (Pattern.varN (.const ``Nat.rec) 3).Path → TShape}
      {mctor : (Pattern.varN (.const ``Nat.zero) 0).Path → TShape}
      {mx my captureType :
        (RecursorIotaPattern ``Nat.rec 3 ``Nat.zero 0).Path → SExpr}
      {succElem zeroElem motiveElem succType zeroType motiveType :
        WShape (n + 1)}
      {head : TShape} {out outTy : WShape (n + 1)},
    LE_Interp.RHS.ShapeSpine (Sum.elim mrec mctor) head
      [natZeroMotivePath, natZeroMinorPath, natZeroSuccMinorPath] out.T →
    LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
      (mrec none) (mx natZeroSuccMinorPath) (my natZeroSuccMinorPath)
      (captureType natZeroSuccMinorPath) succElem succType →
    LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
      (mrec (some none)) (mx natZeroMinorPath) (my natZeroMinorPath)
      (captureType natZeroMinorPath) zeroElem zeroType →
    LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
      (mrec (some (some none))) (mx natZeroMotivePath)
      (my natZeroMotivePath) (captureType natZeroMotivePath)
      motiveElem motiveType →
    out.HasType outTy →
    ∃ k, n + 1 ≤ k ∧ ∃ headK : WShape (k + 3),
      headK.T ≤ head ∧
      LR.DirectFixedHeadDominanceSpine Γ (Sum.elim mrec mctor)
        mx my captureType (outTy.lift k).T headK.T
        [natZeroMotivePath, natZeroMinorPath, natZeroSuccMinorPath]
        (out.lift k).T
        ((natZeroCaptureTower succElem zeroElem motiveElem
          succType zeroType motiveType outTy).lift (k + 3)) := by
  letI : Params := natParams univs
  letI : Params.Semantic := semantic
  intro n Γ mrec mctor mx my captureType succElem zeroElem motiveElem
    succType zeroType motiveType head out outTy hshape hsucc hzero
    hmotive hout
  cases hshape with
  | @cons motiveLevel motiveFun motiveArg middleHead _ _ _
      hargMotive happMotive middleSpine =>
    cases middleSpine with
    | @cons zeroLevel zeroFun zeroArg succHead _ _ _
        hargZero happZero succSpine =>
      cases succSpine with
      | @cons succLevel succFun succArg terminalHead _ _ _
          hargSucc happSucc terminalSpine =>
        cases terminalSpine with
        | nil =>
          let k := max (n + 1)
            (max motiveLevel (max zeroLevel succLevel))
          have hbase : n + 1 ≤ k := Nat.le_max_left _ _
          have hmotiveLevel : motiveLevel ≤ k := by
            exact Nat.le_trans (Nat.le_max_left _ _)
              (Nat.le_max_right _ _)
          have hzeroLevel : zeroLevel ≤ k := by
            exact Nat.le_trans
              (Nat.le_trans (Nat.le_max_left _ _)
                (Nat.le_max_right _ _))
              (Nat.le_max_right _ _)
          have hsuccLevel : succLevel ≤ k := by
            exact Nat.le_trans
              (Nat.le_trans (Nat.le_max_right _ _)
                (Nat.le_max_right _ _))
              (Nat.le_max_right _ _)
          have hmotiveArgLevel : motiveArg.T.1 ≤ k + 2 := by
            change motiveLevel ≤ k + 2
            omega
          have hzeroArgLevel : zeroArg.T.1 ≤ k + 1 := by
            change zeroLevel ≤ k + 1
            omega
          have hsuccArgLevel : succArg.T.1 ≤ k := by
            change succLevel ≤ k
            exact hsuccLevel
          have hmotiveFunLevel : motiveFun.T.1 ≤ k + 3 := by
            change motiveLevel + 1 ≤ k + 3
            omega
          have hzeroFunLevel₂ : zeroFun.T.1 ≤ k + 2 := by
            change zeroLevel + 1 ≤ k + 2
            omega
          have hzeroFunLevel₁ : zeroFun.T.1 ≤ k + 2 :=
            hzeroFunLevel₂
          have hsuccFunLevel₁ : succFun.T.1 ≤ k + 1 := by
            change succLevel + 1 ≤ k + 1
            omega
          have hargMotive' : (motiveArg.lift (k + 2)).T ≤
              Sum.elim mrec mctor natZeroMotivePath :=
            (TShape.lift_eqv hmotiveArgLevel).1.trans hargMotive
          have hargZero' : (zeroArg.lift (k + 1)).T ≤
              Sum.elim mrec mctor natZeroMinorPath :=
            (TShape.lift_eqv hzeroArgLevel).1.trans hargZero
          have hargSucc' : (succArg.lift k).T ≤
              Sum.elim mrec mctor natZeroSuccMinorPath :=
            (TShape.lift_eqv hsuccArgLevel).1.trans hargSucc
          have happMotive' : (zeroFun.lift (k + 2)).T ≤
              ((motiveFun.lift (k + 3)).app
                (motiveArg.lift (k + 2))).T := by
            refine (TShape.lift_eqv hzeroFunLevel₂).1 |>.trans
              (happMotive.trans ?_)
            exact TShape.app_mono
              (TShape.lift_eqv hmotiveFunLevel).2
              (TShape.lift_eqv hmotiveArgLevel).2
          have happZero' : (succFun.lift (k + 1)).T ≤
              ((zeroFun.lift (k + 2)).app
                (zeroArg.lift (k + 1))).T := by
            refine (TShape.lift_eqv hsuccFunLevel₁).1 |>.trans
              (happZero.trans ?_)
            exact TShape.app_mono
              (TShape.lift_eqv hzeroFunLevel₁).2
              (TShape.lift_eqv hzeroArgLevel).2
          have happSucc' : (out.lift k).T ≤
              ((succFun.lift (k + 1)).app (succArg.lift k)).T := by
            refine (TShape.lift_eqv hbase).1 |>.trans
              (happSucc.trans ?_)
            exact TShape.app_mono
              (TShape.lift_eqv hsuccFunLevel₁).2
              (TShape.lift_eqv hsuccArgLevel).2
          have hsucc' := hsucc.lift hbase
          have hzero' := hzero.lift (by omega : n + 1 ≤ k + 1)
          have hmotive' := hmotive.lift (by omega : n + 1 ≤ k + 2)
          have terminal :
              LR.DirectFixedHeadDominanceSpine Γ
                (Sum.elim mrec mctor) mx my captureType
                (outTy.lift k).T (out.lift k).T [] (out.lift k).T
                (outTy.lift k) :=
            .nil ((WShape.HasType.lift hbase).2 hout).T TShape.LE.rfl
          have succDominance :
              LR.DirectFixedHeadDominanceSpine Γ
                (Sum.elim mrec mctor) mx my captureType
                (outTy.lift k).T (succFun.lift (k + 1)).T
                [natZeroSuccMinorPath] (out.lift k).T
                (.forallE (succType.lift k)
                  (.single (succElem.lift k) (outTy.lift k))) :=
            .cons hargSucc' happSucc' hsucc' terminal
          have zeroDominance :
              LR.DirectFixedHeadDominanceSpine Γ
                (Sum.elim mrec mctor) mx my captureType
                (outTy.lift k).T (zeroFun.lift (k + 2)).T
                [natZeroMinorPath, natZeroSuccMinorPath]
                (out.lift k).T
                (.forallE (zeroType.lift (k + 1))
                  (.single (zeroElem.lift (k + 1))
                    (.forallE (succType.lift k)
                      (.single (succElem.lift k) (outTy.lift k))))) :=
            .cons hargZero' happZero' hzero' succDominance
          have motiveDominance :
              LR.DirectFixedHeadDominanceSpine Γ
                (Sum.elim mrec mctor) mx my captureType
                (outTy.lift k).T (motiveFun.lift (k + 3)).T
                [natZeroMotivePath, natZeroMinorPath,
                  natZeroSuccMinorPath]
                (out.lift k).T
                (.forallE (motiveType.lift (k + 2))
                  (.single (motiveElem.lift (k + 2))
                    (.forallE (zeroType.lift (k + 1))
                      (.single (zeroElem.lift (k + 1))
                        (.forallE (succType.lift k)
                          (.single (succElem.lift k)
                            (outTy.lift k))))))) :=
            .cons hargMotive' happMotive' hmotive' zeroDominance
          refine ⟨k, hbase, motiveFun.lift (k + 3),
            (TShape.lift_eqv hmotiveFunLevel).1, ?_⟩
          simpa only [natZeroCaptureTower,
            WShape.lift_forallE (by omega : n + 3 ≤ k + 2),
            WShapeFun.lift_single (by omega : n + 3 ≤ k + 2),
            WShape.lift_forallE (by omega : n + 2 ≤ k + 1),
            WShapeFun.lift_single (by omega : n + 2 ≤ k + 1),
            WShape.lift_forallE hbase,
            WShapeFun.lift_single (by omega : n + 1 ≤ k),
            WShape.lift_lift (.inl (by omega : n + 1 ≤ n + 2)),
            WShape.lift_lift (.inl (by omega : n + 1 ≤ n + 3)),
            WShape.lift_lift (.inl hbase)] using motiveDominance

/--
info: 'Lean4Lean.SExpr.ParamsD0.natZeroShapeSpine_relevelDirect' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms natZeroShapeSpine_relevelDirect

/-- Relevel the four successor-rule capture applications to one consecutive
high-level spine.  The predecessor capture enters at the one-level lift of
its native constructor-field observation; all later raising is uniform with
the three registered recursor captures. -/
theorem natSuccShapeSpine_relevelDirectAligned
    (univs : Nat) [semantic : @Params.Semantic (natParams univs)] :
    letI : Params := natParams univs
    ∀ {n : Nat} {Γ : List SExpr}
      {mrec : (Pattern.varN (.const ``Nat.rec) 3).Path → TShape}
      {mctor : (Pattern.varN (.const ``Nat.succ) 1).Path → TShape}
      {mx my captureType :
        (RecursorIotaPattern ``Nat.rec 3 ``Nat.succ 1).Path → SExpr}
      {predElem predType : WShape (n + 1)}
      {succElem zeroElem motiveElem succType zeroType motiveType :
        WShape (n + 1)}
      {head : TShape} {out outTy : WShape (n + 1)},
    LE_Interp.RHS.ShapeSpine (Sum.elim mrec mctor) head
      [natSuccMotivePath, natSuccZeroMinorPath,
        natSuccMinorPath, natSuccPredPath] out.T →
    LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
      (mrec none) (mx natSuccMinorPath) (my natSuccMinorPath)
      (captureType natSuccMinorPath) succElem succType →
    LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
      (mrec (some none)) (mx natSuccZeroMinorPath)
      (my natSuccZeroMinorPath) (captureType natSuccZeroMinorPath)
      zeroElem zeroType →
    LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
      (mrec (some (some none))) (mx natSuccMotivePath)
      (my natSuccMotivePath) (captureType natSuccMotivePath)
      motiveElem motiveType →
    LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
      (mctor none) (mx natSuccPredPath) (my natSuccPredPath)
      (captureType natSuccPredPath) predElem predType →
    out.HasType outTy →
    ∃ k, n + 1 ≤ k ∧ ∃ headK : WShape (k + 4),
      headK.T ≤ head ∧
      LR.DirectFixedHeadDominanceSpine Γ (Sum.elim mrec mctor)
        mx my captureType (outTy.lift k).T headK.T
        [natSuccMotivePath, natSuccZeroMinorPath,
          natSuccMinorPath, natSuccPredPath]
        (out.lift k).T
        ((natSuccCaptureTower predElem succElem zeroElem
          motiveElem predType succType zeroType motiveType outTy).lift
          (k + 4)) := by
  letI : Params := natParams univs
  letI : Params.Semantic := semantic
  intro n Γ mrec mctor mx my captureType predElem predType succElem
    zeroElem motiveElem succType zeroType motiveType head out outTy hshape
    hsucc hzero hmotive hpred hout
  cases hshape with
  | @cons motiveLevel motiveFun motiveArg middleHead _ _ _
      hargMotive happMotive middleSpine =>
    cases middleSpine with
    | @cons zeroLevel zeroFun zeroArg succHead _ _ _
        hargZero happZero succSpine =>
      cases succSpine with
      | @cons succLevel succFun succArg predHead _ _ _
          hargSucc happSucc predSpine =>
        cases predSpine with
        | @cons predLevel predFun predArg terminalHead _ _ _
            hargPred happPred terminalSpine =>
          cases terminalSpine with
          | nil =>
            let k := max (n + 1)
              (max motiveLevel (max zeroLevel (max succLevel predLevel)))
            have hbase : n + 1 ≤ k := Nat.le_max_left _ _
            have hmotiveLevel : motiveLevel ≤ k := by
              exact Nat.le_trans (Nat.le_max_left _ _)
                (Nat.le_max_right _ _)
            have hzeroLevel : zeroLevel ≤ k := by
              exact Nat.le_trans
                (Nat.le_trans (Nat.le_max_left _ _)
                  (Nat.le_max_right _ _))
                (Nat.le_max_right _ _)
            have hsuccLevel : succLevel ≤ k := by
              exact Nat.le_trans
                (Nat.le_trans
                  (Nat.le_trans (Nat.le_max_left _ _)
                    (Nat.le_max_right _ _))
                  (Nat.le_max_right _ _))
                (Nat.le_max_right _ _)
            have hpredLevel : predLevel ≤ k := by
              exact Nat.le_trans
                (Nat.le_trans
                  (Nat.le_trans (Nat.le_max_right _ _)
                    (Nat.le_max_right _ _))
                  (Nat.le_max_right _ _))
                (Nat.le_max_right _ _)
            have hmotiveArgLevel : motiveArg.T.1 ≤ k + 3 := by
              change motiveLevel ≤ k + 3
              omega
            have hzeroArgLevel : zeroArg.T.1 ≤ k + 2 := by
              change zeroLevel ≤ k + 2
              omega
            have hsuccArgLevel : succArg.T.1 ≤ k + 1 := by
              change succLevel ≤ k + 1
              omega
            have hpredArgLevel : predArg.T.1 ≤ k := by
              change predLevel ≤ k
              exact hpredLevel
            have hmotiveFunLevel : motiveFun.T.1 ≤ k + 4 := by
              change motiveLevel + 1 ≤ k + 4
              omega
            have hzeroFunLevel : zeroFun.T.1 ≤ k + 3 := by
              change zeroLevel + 1 ≤ k + 3
              omega
            have hsuccFunLevel : succFun.T.1 ≤ k + 2 := by
              change succLevel + 1 ≤ k + 2
              omega
            have hpredFunLevel : predFun.T.1 ≤ k + 1 := by
              change predLevel + 1 ≤ k + 1
              omega
            have hargMotive' : (motiveArg.lift (k + 3)).T ≤
                Sum.elim mrec mctor natSuccMotivePath :=
              (TShape.lift_eqv hmotiveArgLevel).1.trans hargMotive
            have hargZero' : (zeroArg.lift (k + 2)).T ≤
                Sum.elim mrec mctor natSuccZeroMinorPath :=
              (TShape.lift_eqv hzeroArgLevel).1.trans hargZero
            have hargSucc' : (succArg.lift (k + 1)).T ≤
                Sum.elim mrec mctor natSuccMinorPath :=
              (TShape.lift_eqv hsuccArgLevel).1.trans hargSucc
            have hargPred' : (predArg.lift k).T ≤
                Sum.elim mrec mctor natSuccPredPath :=
              (TShape.lift_eqv hpredArgLevel).1.trans hargPred
            have happMotive' : (zeroFun.lift (k + 3)).T ≤
                ((motiveFun.lift (k + 4)).app
                  (motiveArg.lift (k + 3))).T := by
              refine (TShape.lift_eqv hzeroFunLevel).1 |>.trans
                (happMotive.trans ?_)
              exact TShape.app_mono
                (TShape.lift_eqv hmotiveFunLevel).2
                (TShape.lift_eqv hmotiveArgLevel).2
            have happZero' : (succFun.lift (k + 2)).T ≤
                ((zeroFun.lift (k + 3)).app
                  (zeroArg.lift (k + 2))).T := by
              refine (TShape.lift_eqv hsuccFunLevel).1 |>.trans
                (happZero.trans ?_)
              exact TShape.app_mono
                (TShape.lift_eqv hzeroFunLevel).2
                (TShape.lift_eqv hzeroArgLevel).2
            have happSucc' : (predFun.lift (k + 1)).T ≤
                ((succFun.lift (k + 2)).app
                  (succArg.lift (k + 1))).T := by
              refine (TShape.lift_eqv hpredFunLevel).1 |>.trans
                (happSucc.trans ?_)
              exact TShape.app_mono
                (TShape.lift_eqv hsuccFunLevel).2
                (TShape.lift_eqv hsuccArgLevel).2
            have happPred' : (out.lift k).T ≤
                ((predFun.lift (k + 1)).app (predArg.lift k)).T := by
              refine (TShape.lift_eqv hbase).1 |>.trans
                (happPred.trans ?_)
              exact TShape.app_mono
                (TShape.lift_eqv hpredFunLevel).2
                (TShape.lift_eqv hpredArgLevel).2
            have hsucc' := hsucc.lift (by omega : n + 1 ≤ k + 1)
            have hzero' := hzero.lift (by omega : n + 1 ≤ k + 2)
            have hmotive' := hmotive.lift (by omega : n + 1 ≤ k + 3)
            have hpred' := hpred.lift hbase
            have terminal :
                LR.DirectFixedHeadDominanceSpine Γ
                  (Sum.elim mrec mctor) mx my captureType
                  (outTy.lift k).T (out.lift k).T [] (out.lift k).T
                  (outTy.lift k) :=
              .nil ((WShape.HasType.lift hbase).2 hout).T TShape.LE.rfl
            have predDominance :
                LR.DirectFixedHeadDominanceSpine Γ
                  (Sum.elim mrec mctor) mx my captureType
                  (outTy.lift k).T (predFun.lift (k + 1)).T
                  [natSuccPredPath] (out.lift k).T
                  (.forallE (predType.lift k)
                    (.single (predElem.lift k)
                      (outTy.lift k))) :=
              .cons hargPred' happPred' hpred' terminal
            have succDominance :
                LR.DirectFixedHeadDominanceSpine Γ
                  (Sum.elim mrec mctor) mx my captureType
                  (outTy.lift k).T (succFun.lift (k + 2)).T
                  [natSuccMinorPath, natSuccPredPath] (out.lift k).T
                  (.forallE (succType.lift (k + 1))
                    (.single (succElem.lift (k + 1))
                      (.forallE (predType.lift k)
                        (.single (predElem.lift k)
                          (outTy.lift k))))) :=
              .cons hargSucc' happSucc' hsucc' predDominance
            have zeroDominance :
                LR.DirectFixedHeadDominanceSpine Γ
                  (Sum.elim mrec mctor) mx my captureType
                  (outTy.lift k).T (zeroFun.lift (k + 3)).T
                  [natSuccZeroMinorPath, natSuccMinorPath,
                    natSuccPredPath]
                  (out.lift k).T
                  (.forallE (zeroType.lift (k + 2))
                    (.single (zeroElem.lift (k + 2))
                      (.forallE (succType.lift (k + 1))
                        (.single (succElem.lift (k + 1))
                          (.forallE (predType.lift k)
                            (.single (predElem.lift k)
                              (outTy.lift k))))))) :=
              .cons hargZero' happZero' hzero' succDominance
            have motiveDominance :
                LR.DirectFixedHeadDominanceSpine Γ
                  (Sum.elim mrec mctor) mx my captureType
                  (outTy.lift k).T (motiveFun.lift (k + 4)).T
                  [natSuccMotivePath, natSuccZeroMinorPath,
                    natSuccMinorPath, natSuccPredPath]
                  (out.lift k).T
                  (.forallE (motiveType.lift (k + 3))
                    (.single (motiveElem.lift (k + 3))
                      (.forallE (zeroType.lift (k + 2))
                        (.single (zeroElem.lift (k + 2))
                          (.forallE (succType.lift (k + 1))
                            (.single (succElem.lift (k + 1))
                              (.forallE (predType.lift k)
                                (.single (predElem.lift k)
                                  (outTy.lift k))))))))) :=
              .cons hargMotive' happMotive' hmotive' zeroDominance
            refine ⟨k, hbase, motiveFun.lift (k + 4),
              (TShape.lift_eqv hmotiveFunLevel).1, ?_⟩
            simpa only [natSuccCaptureTower,
              WShape.lift_forallE (by omega : n + 4 ≤ k + 3),
              WShapeFun.lift_single (by omega : n + 4 ≤ k + 3),
              WShape.lift_forallE (by omega : n + 3 ≤ k + 2),
              WShapeFun.lift_single (by omega : n + 3 ≤ k + 2),
              WShape.lift_forallE (by omega : n + 2 ≤ k + 1),
              WShapeFun.lift_single (by omega : n + 2 ≤ k + 1),
              WShape.lift_forallE hbase,
              WShapeFun.lift_single hbase,
              WShape.lift_lift (.inl (by omega : n + 1 ≤ n + 2)),
              WShape.lift_lift (.inl (by omega : n + 1 ≤ n + 3)),
              WShape.lift_lift (.inl (by omega : n + 1 ≤ n + 4)),
              WShape.lift_lift (.inl hbase)] using
              motiveDominance

/--
info: 'Lean4Lean.SExpr.ParamsD0.natSuccShapeSpine_relevelDirectAligned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms natSuccShapeSpine_relevelDirectAligned

/-- Canonical-field specialization of the exact-capture successor releveling
theorem. -/
theorem natSuccShapeSpine_relevelDirect
    (univs : Nat) [semantic : @Params.Semantic (natParams univs)] :
    letI : Params := natParams univs
    ∀ {n : Nat} {Γ : List SExpr}
      {mrec : (Pattern.varN (.const ``Nat.rec) 3).Path → TShape}
      {mctor : (Pattern.varN (.const ``Nat.succ) 1).Path → TShape}
      {mx my captureType :
        (RecursorIotaPattern ``Nat.rec 3 ``Nat.succ 1).Path → SExpr}
      {field : WShape n}
      {succElem zeroElem motiveElem succType zeroType motiveType :
        WShape (n + 1)}
      {head : TShape} {out outTy : WShape (n + 1)},
    LE_Interp.RHS.ShapeSpine (Sum.elim mrec mctor) head
      [natSuccMotivePath, natSuccZeroMinorPath,
        natSuccMinorPath, natSuccPredPath] out.T →
    LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
      (mrec none) (mx natSuccMinorPath) (my natSuccMinorPath)
      (captureType natSuccMinorPath) succElem succType →
    LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
      (mrec (some none)) (mx natSuccZeroMinorPath)
      (my natSuccZeroMinorPath) (captureType natSuccZeroMinorPath)
      zeroElem zeroType →
    LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
      (mrec (some (some none))) (mx natSuccMotivePath)
      (my natSuccMotivePath) (captureType natSuccMotivePath)
      motiveElem motiveType →
    LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
      (mctor none) (mx natSuccPredPath) (my natSuccPredPath)
      (captureType natSuccPredPath) (field.lift (n + 1)) .indTy →
    out.HasType outTy →
    ∃ k, n + 1 ≤ k ∧ ∃ headK : WShape (k + 4),
      headK.T ≤ head ∧
      LR.DirectFixedHeadDominanceSpine Γ (Sum.elim mrec mctor)
        mx my captureType (outTy.lift k).T headK.T
        [natSuccMotivePath, natSuccZeroMinorPath,
          natSuccMinorPath, natSuccPredPath]
        (out.lift k).T
        ((natSuccCaptureTower (field.lift (n + 1)) succElem zeroElem
          motiveElem .indTy succType zeroType motiveType outTy).lift
          (k + 4)) := by
  letI : Params := natParams univs
  letI : Params.Semantic := semantic
  intro n Γ mrec mctor mx my captureType field succElem zeroElem
    motiveElem succType zeroType motiveType head out outTy hshape hsucc
    hzero hmotive hpred hout
  exact natSuccShapeSpine_relevelDirectAligned univs hshape
    hsucc hzero hmotive hpred hout

/--
info: 'Lean4Lean.SExpr.ParamsD0.natSuccShapeSpine_relevelDirect' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms natSuccShapeSpine_relevelDirect

/-- The zero-rule telescope contains exactly the validity data needed to
type the recursor's one additional major-argument binder. -/
theorem natRecStrongOfZeroRuleType (univs : Nat)
    {Gamma : List (@SExpr (natParams univs))}
    (level : @SLevel (natParams univs))
    (hRuleType : ∃ u, @IsDefEqStrong (natParams univs) Gamma
      (probeNatZeroRuleType univs level)
      (probeNatZeroRuleType univs level)
      (@SExpr.sort (natParams univs) u)) :
    @IsDefEqStrong (natParams univs) Gamma
      (@SExpr.const (natParams univs) ``Nat.rec [level])
      (@SExpr.const (natParams univs) ``Nat.rec [level])
      (@SExpr.mkInst (natParams univs) [level]
        (VInductDecl.recConst 0 ``Nat 0 InductiveFixtures.natType).type) := by
  letI : Params := natParams univs
  let NatS : SExpr := SExpr.const ``Nat []
  let Motive : SExpr := SExpr.forallE NatS (SExpr.sort level)
  let MinorZero : SExpr := (SExpr.bvar 0).app (SExpr.const ``Nat.zero [])
  let MinorSucc : SExpr :=
    SExpr.forallE NatS <|
      SExpr.forallE ((SExpr.bvar 2).app (SExpr.bvar 0)) <|
        (SExpr.bvar 3).app
          ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))
  let ZeroResult : SExpr :=
    (SExpr.bvar 2).app (SExpr.const ``Nat.zero [])
  obtain ⟨ruleSort, hRuleType⟩ := hRuleType
  have hRuleType' : IsDefEqStrong Gamma
      (.forallE Motive (.forallE MinorZero (.forallE MinorSucc ZeroResult)))
      (.forallE Motive (.forallE MinorZero (.forallE MinorSucc ZeroResult)))
      (.sort ruleSort) := by
    simpa [probeNatZeroRuleType, Motive, MinorZero, MinorSucc, ZeroResult,
      NatS] using hRuleType
  clear hRuleType
  obtain ⟨⟨motiveSort, hMotiveType⟩, restSort1, hRest1⟩ :=
    hRuleType'.forallE_inv' (.inl rfl)
  obtain ⟨⟨zeroSort, hMinorZeroType⟩, restSort2, hRest2⟩ :=
    hRest1.forallE_inv' (.inl rfl)
  obtain ⟨⟨succSort, hMinorSuccType⟩, resultSort, hZeroResultType⟩ :=
    hRest2.forallE_inv' (.inl rfl)
  let Delta : List SExpr := MinorSucc :: MinorZero :: Motive :: Gamma
  have hMotiveDeep : IsDefEqStrong (NatS :: Delta)
      (.bvar 3) (.bvar 3) (.forallE NatS (.sort level)) := by
    let rho : Lift := .skip (.skip (.skip (.skip .refl)))
    have W4 : Ctx.Lift' rho Gamma (NatS :: Delta) := by
      exact .skip (.skip (.skip (.skip .refl)))
    have hMotiveLifted := natStrongWeak univs W4 hMotiveType
    have hLookup : Lookup (NatS :: Delta) 3
        (Motive.lift.lift.lift.lift) := .succ (.succ (.succ .zero))
    have hBvar : IsDefEqStrong (NatS :: Delta) (.bvar 3) (.bvar 3)
        (Motive.lift.lift.lift.lift) := .bvar hLookup hMotiveLifted
    simpa [Motive, NatS, SExpr.lift, SExpr.lift'] using hBvar
  have hMajor : IsDefEqStrong (NatS :: Delta)
      (SExpr.bvar 0) (SExpr.bvar 0) NatS := by
    have hNat := natTypeStrong univs (NatS :: Delta)
    change IsDefEqStrong (NatS :: Delta) (.const ``Nat []) (.const ``Nat [])
      (SExpr.mkInst [] InductiveFixtures.natType.type) at hNat
    rw [probeNatTypeTypeV_eq] at hNat
    exact .bvar .zero (by
      simpa [NatS, SExpr.lift, SExpr.lift', SExpr.mkInst] using hNat)
  have hMotiveMajor : IsDefEqStrong (NatS :: Delta)
      ((SExpr.bvar 3).app (SExpr.bvar 0))
      ((SExpr.bvar 3).app (SExpr.bvar 0)) (SExpr.sort level) := by
    exact .appDF
      (natTypeStrong univs (NatS :: Delta))
      (by exact IsDefEqStrong.sort)
      hMotiveDeep hMajor (by exact IsDefEqStrong.sort)
  have hMajorTail := IsDefEqStrong.forallEDF
    (natTypeStrong univs Delta) hMotiveMajor hMotiveMajor
  have hAfterSucc := IsDefEqStrong.forallEDF
    hMinorSuccType hMajorTail hMajorTail
  have hAfterZero := IsDefEqStrong.forallEDF
    hMinorZeroType hAfterSucc hAfterSucc
  have hRecType := IsDefEqStrong.forallEDF
    hMotiveType hAfterZero hAfterZero
  have hRecType' : ∃ u, IsDefEqStrong Gamma
      (SExpr.mkInst [level]
        (VInductDecl.recConst 0 ``Nat 0 InductiveFixtures.natType).type)
      (SExpr.mkInst [level]
        (VInductDecl.recConst 0 ``Nat 0 InductiveFixtures.natType).type)
      (.sort u) := by
    refine ⟨motiveSort.imax (zeroSort.imax
      (succSort.imax ((SLevel.instV [] VLevel.zero.succ).imax level))), ?_⟩
    rw [probeNatRecTypeV_eq]
    simpa [probeNatRecTypeV, Motive, MinorZero, MinorSucc, NatS,
      SExpr.mkInst, probeInstVParamZero] using hRecType
  obtain ⟨recSort, hRecType'⟩ := hRecType'
  let F : ∀ cl : CtorBundle.IsCtor ``Nat.rec,
      CtorBundle ``Nat.rec cl := fun cl => (natRec_not_ctor univs cl).elim
  refine .const InductiveReplayFixtures.nat_rec_env_lookup rfl hRecType' F ?_ ?_
  · intro cl
    exact (natRec_not_ctor univs cl).elim
  · intro r hpat
    exact (natPat_no_const univs hpat).elim

theorem natZeroRuleBodyStrong (univs : Nat)
    {Gamma : List (@SExpr (natParams univs))}
    (level : @SLevel (natParams univs))
    (hRuleType : ∃ u, @IsDefEqStrong (natParams univs) Gamma
      (probeNatZeroRuleType univs level)
      (probeNatZeroRuleType univs level)
      (@SExpr.sort (natParams univs) u)) :
    letI : Params := natParams univs
    let Motive : SExpr := SExpr.forallE (SExpr.const ``Nat []) (SExpr.sort level)
    let MinorZero : SExpr :=
      (SExpr.bvar 0).app (SExpr.const ``Nat.zero [])
    let MinorSucc : SExpr :=
      SExpr.forallE (SExpr.const ``Nat []) <|
        SExpr.forallE ((SExpr.bvar 2).app (SExpr.bvar 0)) <|
          (SExpr.bvar 3).app
            ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))
    IsDefEqStrong (MinorSucc :: MinorZero :: Motive :: Gamma)
      (((((SExpr.const ``Nat.rec [level]).app (SExpr.bvar 2)).app
        (SExpr.bvar 1)).app (SExpr.bvar 0)).app
          (SExpr.const ``Nat.zero []))
      (((((SExpr.const ``Nat.rec [level]).app (SExpr.bvar 2)).app
        (SExpr.bvar 1)).app (SExpr.bvar 0)).app
          (SExpr.const ``Nat.zero []))
      ((SExpr.bvar 2).app (SExpr.const ``Nat.zero [])) := by
  letI : Params := natParams univs
  let NatS : SExpr := SExpr.const ``Nat []
  let Motive : SExpr := SExpr.forallE NatS (SExpr.sort level)
  let MinorZero : SExpr :=
    (SExpr.bvar 0).app (SExpr.const ``Nat.zero [])
  let MinorSucc : SExpr :=
    SExpr.forallE NatS <|
      SExpr.forallE ((SExpr.bvar 2).app (SExpr.bvar 0)) <|
        (SExpr.bvar 3).app
          ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))
  let ZeroResult : SExpr :=
    (SExpr.bvar 2).app (SExpr.const ``Nat.zero [])
  let Delta : List SExpr := MinorSucc :: MinorZero :: Motive :: Gamma
  obtain ⟨ruleSort, hRuleType⟩ := hRuleType
  have hRuleType' : IsDefEqStrong Gamma
      (.forallE Motive (.forallE MinorZero (.forallE MinorSucc ZeroResult)))
      (.forallE Motive (.forallE MinorZero (.forallE MinorSucc ZeroResult)))
      (.sort ruleSort) := by
    simpa [probeNatZeroRuleType, Motive, MinorZero, MinorSucc, ZeroResult,
      NatS] using hRuleType
  obtain ⟨⟨motiveSort, hMotiveType⟩, restSort1, hRest1⟩ :=
    hRuleType'.forallE_inv' (.inl rfl)
  obtain ⟨⟨zeroSort, hMinorZeroType⟩, restSort2, hRest2⟩ :=
    hRest1.forallE_inv' (.inl rfl)
  obtain ⟨⟨succSort, hMinorSuccType⟩, resultSort, hResultType⟩ :=
    hRest2.forallE_inv' (.inl rfl)
  let rho3 : Lift := .skip (.skip (.skip .refl))
  have W3 : Ctx.Lift' rho3 Gamma Delta := by
    exact .skip (.skip (.skip .refl))
  let rho2 : Lift := .skip (.skip .refl)
  have W2 : Ctx.Lift' rho2 (Motive :: Gamma) Delta := by
    exact .skip (.skip .refl)
  let rho1 : Lift := .skip .refl
  have W1 : Ctx.Lift' rho1 (MinorZero :: Motive :: Gamma) Delta := by
    exact .skip .refl
  have hMotiveTypeD := natStrongWeak univs W3 hMotiveType
  have hRest1D := natStrongWeak univs W2 hRest1
  have hMinorZeroTypeD := natStrongWeak univs W2 hMinorZeroType
  have hRest2D := natStrongWeak univs W1 hRest2
  have hMinorSuccTypeD := natStrongWeak univs W1 hMinorSuccType
  have hP : IsDefEqStrong Delta (SExpr.bvar 2) (SExpr.bvar 2) Motive := by
    have hLookup : Lookup Delta 2 (Motive.lift.lift.lift) :=
      .succ (.succ .zero)
    have h := IsDefEqStrong.bvar hLookup hMotiveTypeD
    simpa [Motive, NatS, SExpr.lift, SExpr.lift'] using h
  have hMotiveTypeD' : IsDefEqStrong Delta Motive Motive
      (SExpr.sort motiveSort) := by
    simpa [rho3, Motive, NatS, SExpr.lift, SExpr.lift'] using hMotiveTypeD
  let ZeroTy : SExpr :=
    (SExpr.bvar 2).app (SExpr.const ``Nat.zero [])
  let SuccTy : SExpr :=
    SExpr.forallE NatS <|
      SExpr.forallE ((SExpr.bvar 3).app (SExpr.bvar 0)) <|
        (SExpr.bvar 4).app
          ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))
  have hZeroTypeD : IsDefEqStrong Delta ZeroTy ZeroTy
      (SExpr.sort zeroSort) := by
    simpa [rho2, ZeroTy, MinorZero, SExpr.lift, SExpr.lift'] using
      hMinorZeroTypeD
  have hSuccTypeD : IsDefEqStrong Delta SuccTy SuccTy
      (SExpr.sort succSort) := by
    simpa [rho1, SuccTy, MinorSucc, NatS, SExpr.lift, SExpr.lift'] using
      hMinorSuccTypeD
  have hZ : IsDefEqStrong Delta (SExpr.bvar 1) (SExpr.bvar 1) ZeroTy := by
    have hLookup : Lookup Delta 1 (MinorZero.lift.lift) := .succ .zero
    have hBvar := IsDefEqStrong.bvar hLookup (by
      simpa [ZeroTy, MinorZero, SExpr.lift, SExpr.lift'] using hZeroTypeD)
    simpa [ZeroTy, MinorZero, SExpr.lift, SExpr.lift'] using hBvar
  have hS : IsDefEqStrong Delta (SExpr.bvar 0) (SExpr.bvar 0) SuccTy := by
    have hLookup : Lookup Delta 0 MinorSucc.lift := .zero
    have hBvar := IsDefEqStrong.bvar hLookup (by
      simpa [SuccTy, MinorSucc, NatS, SExpr.lift, SExpr.lift'] using
        hSuccTypeD)
    simpa [SuccTy, MinorSucc, NatS, SExpr.lift, SExpr.lift'] using hBvar
  have hZero := natZeroStrong univs Delta
  have hPZero : IsDefEqStrong Delta ZeroTy ZeroTy (SExpr.sort level) := by
    simpa [ZeroTy, SExpr.inst, SExpr.subst, Subst.one, Subst.cons,
      Subst.lift, Subst.id] using
      (IsDefEqStrong.appDF (natTypeStrong univs Delta) .sort hP hZero .sort)
  have hMotiveDeep : IsDefEqStrong (NatS :: Delta)
      (SExpr.bvar 3) (SExpr.bvar 3)
      (SExpr.forallE NatS (SExpr.sort level)) := by
    let rho4 : Lift := .skip (.skip (.skip (.skip .refl)))
    have W4 : Ctx.Lift' rho4 Gamma (NatS :: Delta) := by
      exact .skip (.skip (.skip (.skip .refl)))
    have hMotiveLifted := natStrongWeak univs W4 hMotiveType
    have hLookup : Lookup (NatS :: Delta) 3
        (Motive.lift.lift.lift.lift) := .succ (.succ (.succ .zero))
    have hBvar := IsDefEqStrong.bvar hLookup hMotiveLifted
    simpa [Motive, NatS, SExpr.lift, SExpr.lift'] using hBvar
  have hMajor : IsDefEqStrong (NatS :: Delta)
      (SExpr.bvar 0) (SExpr.bvar 0) NatS := by
    have hNat := natTypeStrong univs (NatS :: Delta)
    change IsDefEqStrong (NatS :: Delta) (SExpr.const ``Nat [])
      (SExpr.const ``Nat [])
      (SExpr.mkInst [] InductiveFixtures.natType.type) at hNat
    rw [probeNatTypeTypeV_eq] at hNat
    exact .bvar .zero (by
      simpa [NatS, SExpr.lift, SExpr.lift', SExpr.mkInst] using hNat)
  have hMotiveMajor : IsDefEqStrong (NatS :: Delta)
      ((SExpr.bvar 3).app (SExpr.bvar 0))
      ((SExpr.bvar 3).app (SExpr.bvar 0)) (SExpr.sort level) :=
    .appDF (natTypeStrong univs (NatS :: Delta)) .sort
      hMotiveDeep hMajor .sort
  let MajorTail : SExpr :=
    SExpr.forallE NatS ((SExpr.bvar 3).app (SExpr.bvar 0))
  let natSort : SLevel := SLevel.instV [] VLevel.zero.succ
  let majorTailSort : SLevel := natSort.imax level
  have hMajorTail : IsDefEqStrong Delta MajorTail MajorTail
      (SExpr.sort majorTailSort) := by
    simpa [MajorTail, majorTailSort, natSort] using
      IsDefEqStrong.forallEDF
        (natTypeStrong univs Delta) hMotiveMajor hMotiveMajor
  /- Build the generic recursor tail under fresh motive/minor binders. -/
  let G1 : List SExpr := Motive :: Delta
  let G2 : List SExpr := MinorZero :: G1
  let G3 : List SExpr := MinorSucc :: G2
  have hZeroTypeG : IsDefEqStrong G1 MinorZero MinorZero
      (SExpr.sort zeroSort) := by
    have h := natStrongWeak univs W3.cons hMinorZeroType
    simpa [G1, rho3, Motive, MinorZero, NatS, SExpr.lift, SExpr.lift'] using h
  have hSuccTypeG : IsDefEqStrong G2 MinorSucc MinorSucc
      (SExpr.sort succSort) := by
    have h := natStrongWeak univs W3.cons.cons hMinorSuccType
    simpa [G2, G1, rho3, Motive, MinorZero, MinorSucc, NatS,
      SExpr.lift, SExpr.lift'] using h
  have hMotiveGeneric : IsDefEqStrong (NatS :: G3)
      (SExpr.bvar 3) (SExpr.bvar 3)
      (SExpr.forallE NatS (SExpr.sort level)) := by
    let rho4g : Lift := .skip (.skip (.skip (.skip .refl)))
    have W4g : Ctx.Lift' rho4g Delta (NatS :: G3) := by
      exact .skip (.skip (.skip (.skip .refl)))
    have hLift := natStrongWeak univs W4g hMotiveTypeD'
    have hLookup : Lookup (NatS :: G3) 3
        (Motive.lift.lift.lift.lift) := .succ (.succ (.succ .zero))
    have hBvar := IsDefEqStrong.bvar hLookup hLift
    simpa [G3, G2, G1, Motive, NatS, SExpr.lift, SExpr.lift'] using hBvar
  have hMajorGeneric : IsDefEqStrong (NatS :: G3)
      (SExpr.bvar 0) (SExpr.bvar 0) NatS := by
    have hNat := natTypeStrong univs (NatS :: G3)
    change IsDefEqStrong (NatS :: G3) (SExpr.const ``Nat [])
      (SExpr.const ``Nat [])
      (SExpr.mkInst [] InductiveFixtures.natType.type) at hNat
    rw [probeNatTypeTypeV_eq] at hNat
    exact .bvar .zero (by
      simpa [NatS, SExpr.lift, SExpr.lift', SExpr.mkInst] using hNat)
  have hGenericResult : IsDefEqStrong (NatS :: G3)
      ((SExpr.bvar 3).app (SExpr.bvar 0))
      ((SExpr.bvar 3).app (SExpr.bvar 0)) (SExpr.sort level) :=
    .appDF (natTypeStrong univs (NatS :: G3)) .sort
      hMotiveGeneric hMajorGeneric .sort
  have hMajorTailG : IsDefEqStrong G3
      (SExpr.forallE NatS ((SExpr.bvar 3).app (SExpr.bvar 0)))
      (SExpr.forallE NatS ((SExpr.bvar 3).app (SExpr.bvar 0)))
      (SExpr.sort majorTailSort) := by
    simpa [majorTailSort, natSort] using
      IsDefEqStrong.forallEDF
        (natTypeStrong univs G3) hGenericResult hGenericResult
  have hRecAfterSuccG := IsDefEqStrong.forallEDF
    hSuccTypeG hMajorTailG hMajorTailG
  have hRecAfterZeroG := IsDefEqStrong.forallEDF
    hZeroTypeG hRecAfterSuccG hRecAfterSuccG
  have hRecTypeD := IsDefEqStrong.forallEDF
    hMotiveTypeD' hRecAfterZeroG hRecAfterZeroG
  have hRecTypeInst : ∃ u, IsDefEqStrong Delta
      (SExpr.mkInst [level]
        (VInductDecl.recConst 0 ``Nat 0 InductiveFixtures.natType).type)
      (SExpr.mkInst [level]
        (VInductDecl.recConst 0 ``Nat 0 InductiveFixtures.natType).type)
      (SExpr.sort u) := by
    refine ⟨motiveSort.imax
      (zeroSort.imax (succSort.imax majorTailSort)), ?_⟩
    rw [probeNatRecTypeV_eq]
    simpa [probeNatRecTypeV, G3, G2, G1, Motive, MinorZero, MinorSucc,
      NatS, majorTailSort, natSort, SExpr.mkInst, probeInstVParamZero]
      using hRecTypeD
  obtain ⟨recSort, hRecTypeInst⟩ := hRecTypeInst
  let F : ∀ cl : CtorBundle.IsCtor ``Nat.rec,
      CtorBundle ``Nat.rec cl := fun cl => (natRec_not_ctor univs cl).elim
  have hRec : IsDefEqStrong Delta
      (SExpr.const ``Nat.rec [level]) (SExpr.const ``Nat.rec [level])
      (SExpr.mkInst [level]
        (VInductDecl.recConst 0 ``Nat 0 InductiveFixtures.natType).type) := by
    refine .const InductiveReplayFixtures.nat_rec_env_lookup rfl
      hRecTypeInst F ?_ ?_
    · intro cl
      exact (natRec_not_ctor univs cl).elim
    · intro r hpat
      exact (natPat_no_const univs hpat).elim
  /- Instantiate the generic recursor telescope with the three captures. -/
  have hMajorTailS : IsDefEqStrong (SuccTy :: Delta)
      MajorTail.lift MajorTail.lift (SExpr.sort majorTailSort) := by
    simpa [MajorTail, SuccTy, SExpr.lift, ← SExpr.lift'_comp] using
      natStrongWeak univs (Ctx.Lift'.one (A := SuccTy)) hMajorTail
  have hAfterSucc : IsDefEqStrong Delta
      (SExpr.forallE SuccTy MajorTail.lift)
      (SExpr.forallE SuccTy MajorTail.lift)
      (SExpr.sort (succSort.imax majorTailSort)) :=
    .forallEDF hSuccTypeD hMajorTailS hMajorTailS
  have hSuccTypeZ : IsDefEqStrong (ZeroTy :: Delta)
      SuccTy.lift SuccTy.lift (SExpr.sort succSort) := by
    simpa [SuccTy, ZeroTy, SExpr.lift, ← SExpr.lift'_comp] using
      natStrongWeak univs (Ctx.Lift'.one (A := ZeroTy)) hSuccTypeD
  let rhoZS : Lift := .skip (.skip .refl)
  have WZS : Ctx.Lift' rhoZS Delta (SuccTy.lift :: ZeroTy :: Delta) := by
    exact .skip (.skip .refl)
  have hMajorTailZS : IsDefEqStrong (SuccTy.lift :: ZeroTy :: Delta)
      MajorTail.lift.lift MajorTail.lift.lift
      (SExpr.sort majorTailSort) := by
    simpa [rhoZS, SExpr.lift, ← SExpr.lift'_comp] using
      natStrongWeak univs WZS hMajorTail
  have hAfterSuccZ : IsDefEqStrong (ZeroTy :: Delta)
      (SExpr.forallE SuccTy.lift MajorTail.lift.lift)
      (SExpr.forallE SuccTy.lift MajorTail.lift.lift)
      (SExpr.sort (succSort.imax majorTailSort)) :=
    .forallEDF hSuccTypeZ hMajorTailZS hMajorTailZS
  have hAfterZero : IsDefEqStrong Delta
      (SExpr.forallE ZeroTy
        (SExpr.forallE SuccTy.lift MajorTail.lift.lift))
      (SExpr.forallE ZeroTy
        (SExpr.forallE SuccTy.lift MajorTail.lift.lift))
      (SExpr.sort (zeroSort.imax (succSort.imax majorTailSort))) :=
    .forallEDF hZeroTypeD hAfterSuccZ hAfterSuccZ
  have hRecP0 := IsDefEqStrong.appDF
    hMotiveTypeD' hRecAfterZeroG hRec hP hAfterZero
  have hRecP : IsDefEqStrong Delta
      ((SExpr.const ``Nat.rec [level]).app (SExpr.bvar 2))
      ((SExpr.const ``Nat.rec [level]).app (SExpr.bvar 2))
      (SExpr.forallE ZeroTy
        (SExpr.forallE SuccTy.lift MajorTail.lift.lift)) := by
    simpa [G3, G2, G1, ZeroTy, SuccTy, MajorTail, Motive, MinorZero,
      MinorSucc, NatS, SExpr.inst, SExpr.subst, Subst.one, Subst.cons,
      Subst.lift, Subst.id, probeCancelUnderOne, probeCancelUnderTwo]
      using hRecP0
  have hRecPZ0 := IsDefEqStrong.appDF
    hZeroTypeD hAfterSuccZ hRecP hZ hAfterSucc
  have hRecPZ : IsDefEqStrong Delta
      (((SExpr.const ``Nat.rec [level]).app (SExpr.bvar 2)).app
        (SExpr.bvar 1))
      (((SExpr.const ``Nat.rec [level]).app (SExpr.bvar 2)).app
        (SExpr.bvar 1))
      (SExpr.forallE SuccTy MajorTail.lift) := by
    simpa [ZeroTy, SuccTy, MajorTail, NatS, SExpr.lift, SExpr.lift',
      SExpr.inst, SExpr.subst,
      Subst.one, Subst.cons, Subst.lift, Subst.id,
      probeCancelUnderOne, probeCancelUnderTwo] using hRecPZ0
  have hRecPZS0 := IsDefEqStrong.appDF
    hSuccTypeD hMajorTailS hRecPZ hS hMajorTail
  have hRecPZS : IsDefEqStrong Delta
      ((((SExpr.const ``Nat.rec [level]).app (SExpr.bvar 2)).app
        (SExpr.bvar 1)).app (SExpr.bvar 0))
      ((((SExpr.const ``Nat.rec [level]).app (SExpr.bvar 2)).app
        (SExpr.bvar 1)).app (SExpr.bvar 0)) MajorTail := by
    simpa [SuccTy, MajorTail, NatS, SExpr.lift, SExpr.lift',
      SExpr.inst, SExpr.subst,
      Subst.one, Subst.cons, Subst.lift, Subst.id,
      probeCancelUnderOne, probeCancelUnderTwo] using hRecPZS0
  have hBody0 := IsDefEqStrong.appDF
    (natTypeStrong univs Delta) hMotiveMajor hRecPZS hZero hPZero
  have hBody : IsDefEqStrong Delta
      (((((SExpr.const ``Nat.rec [level]).app (SExpr.bvar 2)).app
        (SExpr.bvar 1)).app (SExpr.bvar 0)).app
          (SExpr.const ``Nat.zero []))
      (((((SExpr.const ``Nat.rec [level]).app (SExpr.bvar 2)).app
        (SExpr.bvar 1)).app (SExpr.bvar 0)).app
          (SExpr.const ``Nat.zero [])) ZeroTy := by
    simpa [MajorTail, ZeroTy, SExpr.inst, SExpr.subst, Subst.one,
      Subst.cons, Subst.lift, Subst.id] using hBody0
  simpa [Delta, Motive, MinorZero, MinorSucc, ZeroResult, NatS,
    SExpr.lift, SExpr.lift', probeCancelUnderOne, probeCancelUnderTwo]
    using hBody

theorem natZeroRuleAppliedStrong (univs : Nat)
    {Gamma : List (@SExpr (natParams univs))}
    (level : @SLevel (natParams univs))
    (hRuleType : ∃ u, @IsDefEqStrong (natParams univs) Gamma
      (probeNatZeroRuleType univs level)
      (probeNatZeroRuleType univs level)
      (@SExpr.sort (natParams univs) u))
    (hHead : @IsDefEqStrong (natParams univs) Gamma
      (@SExpr.mkInst (natParams univs) [level]
        (NatGeneration.rule 0 NatGeneration.flatCtors[0]).rhs)
      (@SExpr.mkInst (natParams univs) [level]
        (NatGeneration.rule 0 NatGeneration.flatCtors[0]).rhs)
      (probeNatZeroRuleType univs level)) :
    letI : Params := natParams univs
    let Motive : SExpr :=
      SExpr.forallE (SExpr.const ``Nat []) (SExpr.sort level)
    let MinorZero : SExpr :=
      (SExpr.bvar 0).app (SExpr.const ``Nat.zero [])
    let MinorSucc : SExpr :=
      SExpr.forallE (SExpr.const ``Nat []) <|
        SExpr.forallE ((SExpr.bvar 2).app (SExpr.bvar 0)) <|
          (SExpr.bvar 3).app
            ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))
    let Delta : List SExpr := MinorSucc :: MinorZero :: Motive :: Gamma
    let AppliedRhs : SExpr :=
      [SExpr.bvar 2, SExpr.bvar 1, SExpr.bvar 0].foldl
        (fun f a => f.app a)
        (SExpr.mkInst [level]
          (NatGeneration.rule 0 NatGeneration.flatCtors[0]).rhs)
    IsDefEqStrong Delta AppliedRhs AppliedRhs
      ((SExpr.bvar 2).app (SExpr.const ``Nat.zero [])) := by
  letI : Params := natParams univs
  let NatS : SExpr := SExpr.const ``Nat []
  let Motive : SExpr := SExpr.forallE NatS (SExpr.sort level)
  let MinorZero : SExpr :=
    (SExpr.bvar 0).app (SExpr.const ``Nat.zero [])
  let MinorSucc : SExpr :=
    SExpr.forallE NatS <|
      SExpr.forallE ((SExpr.bvar 2).app (SExpr.bvar 0)) <|
        (SExpr.bvar 3).app
          ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))
  let Result : SExpr :=
    (SExpr.bvar 2).app (SExpr.const ``Nat.zero [])
  let Delta : List SExpr := MinorSucc :: MinorZero :: Motive :: Gamma
  let AppliedRhs : SExpr :=
    [SExpr.bvar 2, SExpr.bvar 1, SExpr.bvar 0].foldl
      (fun f a => f.app a)
      (SExpr.mkInst [level]
        (NatGeneration.rule 0 NatGeneration.flatCtors[0]).rhs)
  obtain ⟨ruleSort, hRuleType⟩ := hRuleType
  have hRuleType' : IsDefEqStrong Gamma
      (.forallE Motive (.forallE MinorZero (.forallE MinorSucc Result)))
      (.forallE Motive (.forallE MinorZero (.forallE MinorSucc Result)))
      (.sort ruleSort) := by
    simpa [probeNatZeroRuleType, Motive, MinorZero, MinorSucc, Result,
      NatS] using hRuleType
  obtain ⟨⟨motiveSort, hMotiveType⟩, restSort1, hRest1⟩ :=
    hRuleType'.forallE_inv' (.inl rfl)
  obtain ⟨⟨zeroSort, hMinorZeroType⟩, restSort2, hRest2⟩ :=
    hRest1.forallE_inv' (.inl rfl)
  obtain ⟨⟨succSort, hMinorSuccType⟩, resultSort, hResultType⟩ :=
    hRest2.forallE_inv' (.inl rfl)
  let rho3 : Lift := .skip (.skip (.skip .refl))
  have W3 : Ctx.Lift' rho3 Gamma Delta :=
    .skip (.skip (.skip .refl))
  let rho2 : Lift := .skip (.skip .refl)
  have W2 : Ctx.Lift' rho2 (Motive :: Gamma) Delta :=
    .skip (.skip .refl)
  let rho1 : Lift := .skip .refl
  have W1 : Ctx.Lift' rho1 (MinorZero :: Motive :: Gamma) Delta :=
    .skip .refl
  have hRuleTypeD0 := natStrongWeak univs W3 hRuleType'
  have hRuleTypeD : IsDefEqStrong Delta
      (.forallE Motive (.forallE MinorZero (.forallE MinorSucc Result)))
      (.forallE Motive (.forallE MinorZero (.forallE MinorSucc Result)))
      (.sort ruleSort) := by
    simpa [rho3, Motive, MinorZero, MinorSucc, Result, NatS,
      SExpr.lift, SExpr.lift'] using hRuleTypeD0
  obtain ⟨⟨_, hMotiveTypeD⟩, _, hCod1⟩ :=
    hRuleTypeD.forallE_inv' (.inl rfl)
  have hRest1D0 := natStrongWeak univs W2 hRest1
  have hRest1D : IsDefEqStrong Delta
      ((SExpr.forallE MinorZero
        (SExpr.forallE MinorSucc Result)).lift' rho2)
      ((SExpr.forallE MinorZero
        (SExpr.forallE MinorSucc Result)).lift' rho2)
      (SExpr.sort restSort1) := hRest1D0
  have hRest2D0 := natStrongWeak univs W1 hRest2
  have hRest2D : IsDefEqStrong Delta
      ((SExpr.forallE MinorSucc Result).lift' rho1)
      ((SExpr.forallE MinorSucc Result).lift' rho1)
      (SExpr.sort restSort2) := hRest2D0
  have hResultD : IsDefEqStrong Delta Result Result
      (.sort resultSort) := by
    simpa [Result, rho1, SExpr.lift, SExpr.lift'] using hResultType
  have hMotiveTypeD' : IsDefEqStrong Delta Motive Motive
      (.sort motiveSort) := by
    simpa [rho3, Motive, NatS, SExpr.lift, SExpr.lift'] using
      natStrongWeak univs W3 hMotiveType
  let ZeroTy : SExpr :=
    (SExpr.bvar 2).app (SExpr.const ``Nat.zero [])
  let SuccTy : SExpr :=
    SExpr.forallE NatS <|
      SExpr.forallE ((SExpr.bvar 3).app (SExpr.bvar 0)) <|
        (SExpr.bvar 4).app
          ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))
  have hZeroTypeD : IsDefEqStrong Delta ZeroTy ZeroTy
      (.sort zeroSort) := by
    simpa [rho2, ZeroTy, MinorZero, SExpr.lift, SExpr.lift'] using
      natStrongWeak univs W2 hMinorZeroType
  have hSuccTypeD : IsDefEqStrong Delta SuccTy SuccTy
      (.sort succSort) := by
    simpa [rho1, SuccTy, MinorSucc, NatS, SExpr.lift, SExpr.lift'] using
      natStrongWeak univs W1 hMinorSuccType
  have hP : IsDefEqStrong Delta (.bvar 2) (.bvar 2) Motive := by
    have hLookup : Lookup Delta 2 (Motive.lift.lift.lift) :=
      .succ (.succ .zero)
    simpa [Motive, NatS, SExpr.lift, SExpr.lift'] using
      IsDefEqStrong.bvar hLookup
        (natStrongWeak univs W3 hMotiveType)
  have hZ : IsDefEqStrong Delta (.bvar 1) (.bvar 1) ZeroTy := by
    have hLookup : Lookup Delta 1 (MinorZero.lift.lift) := .succ .zero
    have hBvar := IsDefEqStrong.bvar hLookup (by
      simpa [ZeroTy, MinorZero, SExpr.lift, SExpr.lift'] using hZeroTypeD)
    simpa [ZeroTy, MinorZero, SExpr.lift, SExpr.lift'] using hBvar
  have hS : IsDefEqStrong Delta (.bvar 0) (.bvar 0) SuccTy := by
    have hLookup : Lookup Delta 0 MinorSucc.lift := .zero
    have hBvar := IsDefEqStrong.bvar hLookup (by
      simpa [SuccTy, MinorSucc, NatS, SExpr.lift, SExpr.lift'] using
        hSuccTypeD)
    simpa [SuccTy, MinorSucc, NatS, SExpr.lift, SExpr.lift'] using hBvar
  have hHeadRaw : IsDefEqStrong Gamma
      (SExpr.mkInst [level]
        (NatGeneration.rule 0 NatGeneration.flatCtors[0]).rhs)
      (SExpr.mkInst [level]
        (NatGeneration.rule 0 NatGeneration.flatCtors[0]).rhs)
      (SExpr.mkInst [level]
        (NatGeneration.rule 0 NatGeneration.flatCtors[0]).type) := by
    simpa only [probeNatZeroRuleTypeS_eq] using hHead
  have hHeadD0 := natStrongWeak univs W3 hHeadRaw
  obtain ⟨⟨_, _⟩, ⟨rhsClosed, typeClosed⟩⟩ :=
    natFinalEnv_ordered.closed.2
      (natRule_registered probeNatFlatCtorZero_lookup)
  rw [rhsClosed.mkInstS.lift'_eq .zero,
    typeClosed.mkInstS.lift'_eq .zero] at hHeadD0
  have hHeadD : IsDefEqStrong Delta
      (SExpr.mkInst [level]
        (NatGeneration.rule 0 NatGeneration.flatCtors[0]).rhs)
      (SExpr.mkInst [level]
        (NatGeneration.rule 0 NatGeneration.flatCtors[0]).rhs)
      (.forallE Motive (.forallE MinorZero (.forallE MinorSucc Result))) := by
    simpa [probeNatZeroRuleTypeS_eq, probeNatZeroRuleType, Motive,
      MinorZero, MinorSucc, Result, NatS] using hHeadD0
  /- Rebuild the codomain tower once over generic binders and once over the
  three actual captures.  Keeping both towers at the same computed universe
  avoids relying on uniqueness of the sort witnesses returned by inversion. -/
  let G1 : List SExpr := Motive :: Delta
  let G2 : List SExpr := MinorZero :: G1
  let G3 : List SExpr := MinorSucc :: G2
  have hZeroTypeG : IsDefEqStrong G1 MinorZero MinorZero
      (SExpr.sort zeroSort) := by
    have h := natStrongWeak univs W3.cons hMinorZeroType
    simpa [G1, rho3, Motive, MinorZero, NatS,
      SExpr.lift, SExpr.lift'] using h
  have hSuccTypeG : IsDefEqStrong G2 MinorSucc MinorSucc
      (SExpr.sort succSort) := by
    have h := natStrongWeak univs W3.cons.cons hMinorSuccType
    simpa [G2, G1, rho3, Motive, MinorZero, MinorSucc, Result, NatS,
      SExpr.lift, SExpr.lift'] using h
  have hResultTypeG : IsDefEqStrong G3 Result Result
      (SExpr.sort resultSort) := by
    have h := natStrongWeak univs W3.cons.cons.cons hResultType
    simpa [G3, G2, G1, rho3, Motive, MinorZero, MinorSucc, Result,
      NatS, SExpr.lift, SExpr.lift'] using h
  have hAfterSuccG : IsDefEqStrong G2
      (SExpr.forallE MinorSucc Result)
      (SExpr.forallE MinorSucc Result)
      (SExpr.sort (succSort.imax resultSort)) :=
    .forallEDF hSuccTypeG hResultTypeG hResultTypeG
  have hAfterZeroG : IsDefEqStrong G1
      (SExpr.forallE MinorZero (SExpr.forallE MinorSucc Result))
      (SExpr.forallE MinorZero (SExpr.forallE MinorSucc Result))
      (SExpr.sort (zeroSort.imax (succSort.imax resultSort))) :=
    .forallEDF hZeroTypeG hAfterSuccG hAfterSuccG
  have hResultS : IsDefEqStrong (SuccTy :: Delta)
      Result.lift Result.lift (SExpr.sort resultSort) := by
    simpa [SExpr.lift] using
      natStrongWeak univs (Ctx.Lift'.one (A := SuccTy)) hResultD
  have hAfterSucc : IsDefEqStrong Delta
      (SExpr.forallE SuccTy Result.lift)
      (SExpr.forallE SuccTy Result.lift)
      (SExpr.sort (succSort.imax resultSort)) :=
    .forallEDF hSuccTypeD hResultS hResultS
  have hSuccTypeZ : IsDefEqStrong (ZeroTy :: Delta)
      SuccTy.lift SuccTy.lift (SExpr.sort succSort) := by
    simpa [SuccTy, ZeroTy, SExpr.lift, ← SExpr.lift'_comp] using
      natStrongWeak univs (Ctx.Lift'.one (A := ZeroTy)) hSuccTypeD
  let rhoZS : Lift := .skip (.skip .refl)
  have WZS : Ctx.Lift' rhoZS Delta
      (SuccTy.lift :: ZeroTy :: Delta) :=
    .skip (.skip .refl)
  have hResultZS : IsDefEqStrong (SuccTy.lift :: ZeroTy :: Delta)
      Result.lift.lift Result.lift.lift (SExpr.sort resultSort) := by
    simpa [rhoZS, SExpr.lift, ← SExpr.lift'_comp] using
      natStrongWeak univs WZS hResultD
  have hAfterSuccZ : IsDefEqStrong (ZeroTy :: Delta)
      (SExpr.forallE SuccTy.lift Result.lift.lift)
      (SExpr.forallE SuccTy.lift Result.lift.lift)
      (SExpr.sort (succSort.imax resultSort)) :=
    .forallEDF hSuccTypeZ hResultZS hResultZS
  have hAfterZero : IsDefEqStrong Delta
      (SExpr.forallE ZeroTy
        (SExpr.forallE SuccTy.lift Result.lift.lift))
      (SExpr.forallE ZeroTy
        (SExpr.forallE SuccTy.lift Result.lift.lift))
      (SExpr.sort (zeroSort.imax (succSort.imax resultSort))) :=
    .forallEDF hZeroTypeD hAfterSuccZ hAfterSuccZ
  have hAppP0 := IsDefEqStrong.appDF
    hMotiveTypeD' hAfterZeroG hHeadD hP hAfterZero
  have hAppP : IsDefEqStrong Delta
      ((SExpr.mkInst [level]
        (NatGeneration.rule 0 NatGeneration.flatCtors[0]).rhs).app (.bvar 2))
      ((SExpr.mkInst [level]
        (NatGeneration.rule 0 NatGeneration.flatCtors[0]).rhs).app (.bvar 2))
      (SExpr.forallE ZeroTy
        (SExpr.forallE SuccTy.lift Result.lift.lift)) := by
    simpa [G3, G2, G1, ZeroTy, SuccTy, Result, Motive, MinorZero,
      MinorSucc, NatS, SExpr.inst, SExpr.subst, Subst.one, Subst.cons,
      Subst.lift, Subst.id, probeCancelUnderOne, probeCancelUnderTwo]
      using hAppP0
  have hAppZ0 := IsDefEqStrong.appDF
    hZeroTypeD hAfterSuccZ hAppP hZ hAfterSucc
  have hAppZ : IsDefEqStrong Delta
      (((SExpr.mkInst [level]
        (NatGeneration.rule 0 NatGeneration.flatCtors[0]).rhs).app
          (.bvar 2)).app (.bvar 1))
      (((SExpr.mkInst [level]
        (NatGeneration.rule 0 NatGeneration.flatCtors[0]).rhs).app
          (.bvar 2)).app (.bvar 1))
      (SExpr.forallE SuccTy Result.lift) := by
    simpa [ZeroTy, SuccTy, Result, NatS, SExpr.lift, SExpr.lift',
      SExpr.inst, SExpr.subst, Subst.one, Subst.cons, Subst.lift,
      Subst.id, probeCancelUnderOne, probeCancelUnderTwo] using hAppZ0
  have hAppS0 := IsDefEqStrong.appDF
    hSuccTypeD hResultS hAppZ hS hResultD
  simpa [Delta, AppliedRhs, Result, SuccTy, MinorSucc, NatS,
    SExpr.lift, SExpr.lift', SExpr.inst, SExpr.subst,
    Subst.one, Subst.cons, Subst.lift, Subst.id,
    probeCancelUnderOne, probeCancelUnderTwo] using hAppS0

theorem natZeroRuleActionSound (univs : Nat)
    {Gamma : List (@SExpr (natParams univs))}
    (level : @SLevel (natParams univs)) :
    letI : Params := natParams univs
    let Motive : SExpr :=
      SExpr.forallE (SExpr.const ``Nat []) (SExpr.sort level)
    let MinorZero : SExpr :=
      (SExpr.bvar 0).app (SExpr.const ``Nat.zero [])
    let MinorSucc : SExpr :=
      SExpr.forallE (SExpr.const ``Nat []) <|
        SExpr.forallE ((SExpr.bvar 2).app (SExpr.bvar 0)) <|
          (SExpr.bvar 3).app
            ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))
    let Delta : List SExpr := MinorSucc :: MinorZero :: Motive :: Gamma
    let Redex : SExpr :=
      ((((SExpr.const ``Nat.rec [level]).app (SExpr.bvar 2)).app
        (SExpr.bvar 1)).app (SExpr.bvar 0)).app
          (SExpr.const ``Nat.zero [])
    let AppliedRhs : SExpr :=
      [SExpr.bvar 2, SExpr.bvar 1, SExpr.bvar 0].foldl
        (fun f a => f.app a)
        (SExpr.mkInst [level]
          (NatGeneration.rule 0 NatGeneration.flatCtors[0]).rhs)
    let Result : SExpr :=
      (SExpr.bvar 2).app (SExpr.const ``Nat.zero [])
    IsDefEq Delta Redex AppliedRhs Result := by
  letI : Params := natParams univs
  let Motive : SExpr :=
    SExpr.forallE (SExpr.const ``Nat []) (SExpr.sort level)
  let MinorZero : SExpr :=
    (SExpr.bvar 0).app (SExpr.const ``Nat.zero [])
  let MinorSucc : SExpr :=
    SExpr.forallE (SExpr.const ``Nat []) <|
      SExpr.forallE ((SExpr.bvar 2).app (SExpr.bvar 0)) <|
        (SExpr.bvar 3).app
          ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))
  let Delta0 : List SExpr := [MinorSucc, MinorZero, Motive]
  let Delta : List SExpr := Delta0 ++ Gamma
  let Redex : SExpr :=
    ((((SExpr.const ``Nat.rec [level]).app (SExpr.bvar 2)).app
      (SExpr.bvar 1)).app (SExpr.bvar 0)).app
        (SExpr.const ``Nat.zero [])
  let AppliedRhs : SExpr :=
    [SExpr.bvar 2, SExpr.bvar 1, SExpr.bvar 0].foldl
      (fun f a => f.app a)
      (SExpr.mkInst [level]
        (NatGeneration.rule 0 NatGeneration.flatCtors[0]).rhs)
  let Result : SExpr :=
    (SExpr.bvar 2).app (SExpr.const ``Nat.zero [])
  let vls : List VLevel := [level.reify]
  let argsV : List VExpr := [VExpr.bvar 2, VExpr.bvar 1, VExpr.bvar 0]
  let AsV : List VExpr :=
    probeNatRuleBindersV.map (VExpr.instL vls)
  let ResultV : VExpr := probeNatZeroRuleResultV.instL vls
  have hvls : ∀ l ∈ vls, l.WF univs := by
    intro l hl
    simp only [vls, List.mem_singleton] at hl
    subst l
    exact SLevel.reify_wf level
  have hreg := natRule_registered probeNatFlatCtorZero_lookup
  have hlhs0 := (natFinalEnv_ordered.defEqWF hreg).1.instL hvls
  rw [probeNatZeroRuleLhsV_eq] at hlhs0
  unfold probeNatZeroRuleLhsV at hlhs0
  rw [VExpr.instL_lamN] at hlhs0
  obtain ⟨hTel, bodyType, hbody⟩ :=
    VEnv.HasType.lamN_wf natFinalEnv_ordered (by trivial) hlhs0
  have hTel' : natFinalEnv.OnTel univs [] AsV := by
    simpa [AsV] using hTel
  have hbody' : natFinalEnv.HasType univs AsV.reverse
      (probeNatZeroRuleLhsBodyV.instL vls) bodyType := by
    simpa [AsV] using hbody
  have hDelta0 : OnCtx AsV.reverse (natFinalEnv.IsType univs) := by
    exact hTel'.toOnCtx (by trivial)
  have hprobeType : probeNatZeroRuleTypeV =
      VExpr.forallN probeNatRuleBindersV probeNatZeroRuleResultV := rfl
  have hargs : natFinalEnv.SpineWF univs AsV.reverse
      (VExpr.forallN AsV ResultV) argsV ResultV := by
    have hcore := natSelfSpine (env := natFinalEnv) (univs := univs)
      AsV ResultV []
    have hclosed : (VExpr.forallN AsV ResultV).Closed := by
      have ⟨⟨_, _⟩, _, htypeClosed⟩ := natFinalEnv_ordered.closed.2 hreg
      rw [probeNatZeroRuleTypeV_eq] at htypeClosed
      rw [hprobeType] at htypeClosed
      simpa [AsV, ResultV, VExpr.instL_forallN] using
        htypeClosed.instL (ls := vls)
    rw [hclosed.liftN_eq (Nat.zero_le _)] at hcore
    simpa [AsV, argsV, probeNatRuleBindersV,
      VExpr.bvarRevRange] using hcore
  have hTelLocal : natFinalEnv.OnTel univs AsV.reverse AsV := by
    simpa using natOnTelWeakR natFinalEnv_ordered (Base := [])
      (As := AsV) (by trivial) hTel' AsV.reverse
  have hbodyLocal : natFinalEnv.HasType univs
      (AsV.reverse ++ AsV.reverse)
      (probeNatZeroRuleLhsBodyV.instL vls) bodyType :=
    VEnv.IsDefEq.weakR natFinalEnv_ordered
      (VEnv.CtxWF.closed natFinalEnv_ordered hDelta0) hbody' AsV.reverse
  have hspineBody := VEnv.SpineWF.retarget hargs
    (by simp [AsV, argsV, probeNatRuleBindersV]) bodyType
  have hcollapseV := VEnv.IsDefEq.appN_lamN natFinalEnv_ordered
    hTelLocal hbodyLocal hspineBody
      (by simp [AsV, argsV, probeNatRuleBindersV])
  have htypeShape :
      (NatGeneration.rule 0 NatGeneration.flatCtors[0]).type.instL vls =
        VExpr.forallN AsV ResultV := by
    rw [probeNatZeroRuleTypeV_eq, hprobeType, VExpr.instL_forallN]
  have hlhsLocal : natFinalEnv.HasType univs AsV.reverse
      ((probeNatZeroRuleLhsV.instL vls).appN argsV)
      ResultV := by
    have hlhsWeak : natFinalEnv.HasType univs AsV.reverse
        ((NatGeneration.rule 0 NatGeneration.flatCtors[0]).lhs.instL vls)
        ((NatGeneration.rule 0 NatGeneration.flatCtors[0]).type.instL vls) :=
      ((natFinalEnv_ordered.defEqWF hreg).1.instL hvls).weak0
        natFinalEnv_ordered
    have hdeclared : natFinalEnv.SpineWF univs AsV.reverse
        ((NatGeneration.rule 0 NatGeneration.flatCtors[0]).type.instL vls)
        argsV ResultV := by
      rw [htypeShape]
      exact hargs
    rw [← probeNatZeroRuleLhsV_eq]
    exact hdeclared.hasType_appN hlhsWeak
  have hcollapseV' : natFinalEnv.IsDefEq univs AsV.reverse
      ((probeNatZeroRuleLhsV.instL vls).appN argsV)
      ((probeNatZeroRuleLhsBodyV.instL vls).instRev argsV)
      ResultV := by
    have ⟨_, htype⟩ := hcollapseV.symm.uniq
      InductiveReplayFixtures.nat_env_wf hDelta0 hlhsLocal
    exact htype.defeqDF hcollapseV
  have hrawV : natFinalEnv.IsDefEq univs AsV.reverse
      ((NatGeneration.rule 0 NatGeneration.flatCtors[0]).lhs.instL vls)
      ((NatGeneration.rule 0 NatGeneration.flatCtors[0]).rhs.instL vls)
      ((NatGeneration.rule 0 NatGeneration.flatCtors[0]).type.instL vls) :=
    .extra hreg hvls rfl
  have hdeclared : natFinalEnv.SpineWF univs AsV.reverse
      ((NatGeneration.rule 0 NatGeneration.flatCtors[0]).type.instL vls)
      argsV ResultV := by
    rw [htypeShape]
    exact hargs
  have happliedV := hrawV.appN_congr hdeclared
  have hsound0V := hcollapseV'.symm.trans happliedV
  have hsoundV := hsound0V.weakR natFinalEnv_ordered
    (VEnv.CtxWF.closed natFinalEnv_ordered hDelta0)
    (Gamma.map SExpr.reify)
  have hlevels : OnCtx
      (AsV.reverse ++ Gamma.map SExpr.reify)
      (fun _ A => A.LevelWF univs) := by
    have hAsLevels : ∀ A ∈ AsV, A.LevelWF univs := by
      intro A hA
      simp only [AsV, List.mem_map] at hA
      obtain ⟨A0, _, rfl⟩ := hA
      exact VExpr.LevelWF.instL hvls
    have hGammaLevels : OnCtx (Gamma.map SExpr.reify)
        (fun _ A => A.LevelWF univs) :=
      natReifyLevelWFContext Gamma
    have go : ∀ L : List VExpr,
        (∀ A ∈ L, A.LevelWF univs) →
        OnCtx (L ++ Gamma.map SExpr.reify)
          (fun _ A => A.LevelWF univs) := by
      intro L hall
      induction L with
      | nil => simpa using hGammaLevels
      | cons A rest ih =>
        exact ⟨ih (fun B hB => hall B (.tail _ hB)),
          hall A (.head _)⟩
    exact go AsV.reverse (by
      intro A hA
      exact hAsLevels A (by simpa using hA))
  have hsoundS := SExpr.IsDefEq.mkS (natStructureEtaSound univs)
    hsoundV hlevels
  have hmkInst (e : VExpr) :
      SExpr.mk (e.instL vls) = SExpr.mkInst [level] e := by
    unfold vls
    exact @SExpr.mk_instL_map_reify (natParams univs) e [level]
  have hctx :
      (AsV.reverse ++ Gamma.map SExpr.reify).map SExpr.mk = Delta := by
    rw [List.map_append]
    have hGamma : (Gamma.map SExpr.reify).map SExpr.mk = Gamma := by
      rw [List.map_map]
      exact List.map_id''' Gamma fun term _ => SExpr.mk_reify term
    have hAs : AsV.reverse.map SExpr.mk = Delta0 := by
      rw [List.map_reverse]
      have hforward : AsV.map SExpr.mk =
          [Motive, MinorZero, MinorSucc] := by
        simp [AsV, Motive, MinorZero, MinorSucc,
          probeNatRuleBindersV, hmkInst, SExpr.mkInst,
          probeInstVParamZero]
      rw [hforward]
      rfl
    rw [hAs, hGamma]
  rw [hctx] at hsoundS
  have hbodyCollapseV :
      (probeNatZeroRuleLhsBodyV.instL vls).instRev argsV =
      ((((VExpr.const ``Nat.rec [level.reify]).app (VExpr.bvar 2)).app
        (VExpr.bvar 1)).app (VExpr.bvar 0)).app
          (VExpr.const ``Nat.zero []) := by
    simp [probeNatZeroRuleLhsBodyV, vls, argsV, VExpr.instRev,
      VExpr.instL, VExpr.inst, VExpr.instVar, VExpr.liftN, liftVar,
      VExpr.liftN_succ, VExpr.liftN_zero, probeReifyInstVParamZero,
      probeVCancelThreeLifts, probeVCancelTwoLifts, VExpr.inst_lift]
  rw [hbodyCollapseV] at hsoundS
  have hresultMk :
      SExpr.mk ResultV = Result := by
    simp [ResultV, Result, probeNatZeroRuleResultV, vls,
      VExpr.instL, SExpr.mk]
  rw [hresultMk] at hsoundS
  simpa [Delta, Delta0, Redex, AppliedRhs, vls, argsV, hmkInst,
    probeNatZeroRuleLhsV, probeNatRuleBindersV, VExpr.lamN,
    VExpr.appN, SExpr.mk, SExpr.mkInst] using hsoundS

/-- The generated zero match supplies the single local extension leaf used
by the registered tower proof. -/
theorem natZeroRuleLocalStrong (univs : Nat)
    {Gamma : List (@SExpr (natParams univs))}
    (level : @SLevel (natParams univs))
    (hRuleType : ∃ u, @IsDefEqStrong (natParams univs) Gamma
      (probeNatZeroRuleType univs level)
      (probeNatZeroRuleType univs level)
      (@SExpr.sort (natParams univs) u))
    (hRhs : @IsDefEqStrong (natParams univs) Gamma
      (@SExpr.mkInst (natParams univs) [level]
        (NatGeneration.rule 0 NatGeneration.flatCtors[0]).rhs)
      (@SExpr.mkInst (natParams univs) [level]
        (NatGeneration.rule 0 NatGeneration.flatCtors[0]).rhs)
      (probeNatZeroRuleType univs level)) :
    letI : Params := natParams univs
    let NatS : SExpr := SExpr.const ``Nat []
    let Motive : SExpr := SExpr.forallE NatS (SExpr.sort level)
    let MinorZero : SExpr :=
      (SExpr.bvar 0).app (SExpr.const ``Nat.zero [])
    let MinorSucc : SExpr :=
      SExpr.forallE NatS <|
        SExpr.forallE ((SExpr.bvar 2).app (SExpr.bvar 0)) <|
          (SExpr.bvar 3).app
            ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))
    let Delta : List SExpr := MinorSucc :: MinorZero :: Motive :: Gamma
    let Redex : SExpr :=
      ((((SExpr.const ``Nat.rec [level]).app (SExpr.bvar 2)).app
        (SExpr.bvar 1)).app (SExpr.bvar 0)).app
          (SExpr.const ``Nat.zero [])
    let AppliedRhs : SExpr :=
      [SExpr.bvar 2, SExpr.bvar 1, SExpr.bvar 0].foldl
        (fun f a => f.app a)
        (SExpr.mkInst [level]
          (NatGeneration.rule 0 NatGeneration.flatCtors[0]).rhs)
    let Result : SExpr :=
      (SExpr.bvar 2).app (SExpr.const ``Nat.zero [])
    IsDefEqStrong Delta Redex AppliedRhs Result := by
  letI : Params := natParams univs
  let NatS : SExpr := SExpr.const ``Nat []
  let Motive : SExpr := SExpr.forallE NatS (SExpr.sort level)
  let MinorZero : SExpr :=
    (SExpr.bvar 0).app (SExpr.const ``Nat.zero [])
  let MinorSucc : SExpr :=
    SExpr.forallE NatS <|
      SExpr.forallE ((SExpr.bvar 2).app (SExpr.bvar 0)) <|
        (SExpr.bvar 3).app
          ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))
  let Delta : List SExpr := MinorSucc :: MinorZero :: Motive :: Gamma
  let Redex : SExpr :=
    ((((SExpr.const ``Nat.rec [level]).app (SExpr.bvar 2)).app
      (SExpr.bvar 1)).app (SExpr.bvar 0)).app
        (SExpr.const ``Nat.zero [])
  let AppliedRhs : SExpr :=
    [SExpr.bvar 2, SExpr.bvar 1, SExpr.bvar 0].foldl
      (fun f a => f.app a)
      (SExpr.mkInst [level]
        (NatGeneration.rule 0 NatGeneration.flatCtors[0]).rhs)
  let Result : SExpr :=
    (SExpr.bvar 2).app (SExpr.const ``Nat.zero [])
  let rgen :=
    (NatGeneration.ruleRHS natRuleClosure probeNatFlatCtorZero_lookup,
      NatGeneration.ruleCheck natRuleClosure
        (List.mem_of_getElem? probeNatFlatCtorZero_lookup))
  have hpat : NatPat
      (RecursorIotaPattern ``Nat.rec 3 ``Nat.zero 0) rgen :=
    .mk probeNatFlatCtorZero_lookup
  let rule : Pattern.IotaRule rgen := {
    pat := hpat
    df := NatGeneration.rule 0 NatGeneration.flatCtors[0]
    registered := natRule_registered probeNatFlatCtorZero_lookup
    rhsClosed := natRuleClosure.rhs_closed probeNatFlatCtorZero_lookup
    capturePaths := natCapturePaths NatGeneration.flatCtors[0]
    rhsTower := natRuleRHS_tower probeNatFlatCtorZero_lookup }
  obtain ⟨mcap, hmatch⟩ :=
    RecursorIotaPattern.matchesS_spines
      (rargs := [SExpr.bvar 0, SExpr.bvar 1, SExpr.bvar 2])
      (cargs := []) (rls := [level]) (cls := []) (by rfl) (by rfl)
  have hmatch' : (RecursorIotaPattern ``Nat.rec 3 ``Nat.zero 0).MatchesS
      Redex [level] mcap := by
    simpa [Redex] using hmatch
  obtain ⟨_, _, hcaps⟩ := natZeroCaptureValues univs hmatch
  have hrhsEq : AppliedRhs = rgen.1.applyS [level] mcap := by
    calc
      AppliedRhs =
          (rule.capturePaths.map mcap).foldl
            (fun (f a : SExpr) => f.app a)
            (SExpr.mkInst [level] rule.df.rhs) := by
        simp [AppliedRhs, rule, hcaps]
      _ = rgen.1.applyS [level] mcap := rule.rhsApply [level] mcap
  have hsound : IsDefEq Delta Redex (rgen.1.applyS [level] mcap)
      Result := by
    have hsoundCanonical : IsDefEq Delta Redex AppliedRhs Result := by
      simpa [Delta, Redex, AppliedRhs, Result] using
        (natZeroRuleActionSound univs (Gamma := Gamma) level)
    exact hrhsEq ▸ hsoundCanonical
  let action : Pattern.Action Delta rgen Redex [level] mcap Result := {
    pat := hpat
    matched := hmatch'
    dfs := []
    defeqs := by rfl
    checked := by simp
    sound := hsound }
  have hLeft := natZeroRuleBodyStrong univs (Gamma := Gamma) level hRuleType
  have hRightCanonical :=
    natZeroRuleAppliedStrong univs (Gamma := Gamma) level hRuleType hRhs
  have hRight : IsDefEqStrong Delta
      (rgen.1.applyS [level] mcap) (rgen.1.applyS [level] mcap)
      Result := by
    have hRightCanonical' : IsDefEqStrong Delta AppliedRhs AppliedRhs
        Result := by
      simpa [Delta, AppliedRhs, Result] using hRightCanonical
    exact hrhsEq ▸ hRightCanonical'
  have hLocal := IsDefEqStrong.extra action (by
    simpa [Delta, Redex, Result] using hLeft) hRight
  have hLocalCanonical : IsDefEqStrong Delta Redex AppliedRhs Result :=
    hrhsEq.symm ▸ hLocal
  simpa [Delta, Redex, AppliedRhs, Result] using hLocalCanonical

/-- The first two applications of the zero RHS tower, in the binder
contexts where the successive eta laws consume them. -/
theorem natZeroRulePrefixesStrong (univs : Nat)
    {Gamma : List (@SExpr (natParams univs))}
    (level : @SLevel (natParams univs))
    (hRuleType : ∃ u, @IsDefEqStrong (natParams univs) Gamma
      (probeNatZeroRuleType univs level)
      (probeNatZeroRuleType univs level)
      (@SExpr.sort (natParams univs) u))
    (hRhs : @IsDefEqStrong (natParams univs) Gamma
      (@SExpr.mkInst (natParams univs) [level]
        (NatGeneration.rule 0 NatGeneration.flatCtors[0]).rhs)
      (@SExpr.mkInst (natParams univs) [level]
        (NatGeneration.rule 0 NatGeneration.flatCtors[0]).rhs)
      (probeNatZeroRuleType univs level)) :
    letI : Params := natParams univs
    let NatS : SExpr := SExpr.const ``Nat []
    let Motive : SExpr := SExpr.forallE NatS (SExpr.sort level)
    let MinorZero : SExpr :=
      (SExpr.bvar 0).app (SExpr.const ``Nat.zero [])
    let MinorSucc : SExpr :=
      SExpr.forallE NatS <|
        SExpr.forallE ((SExpr.bvar 2).app (SExpr.bvar 0)) <|
          (SExpr.bvar 3).app
            ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))
    let Result : SExpr :=
      (SExpr.bvar 2).app (SExpr.const ``Nat.zero [])
    let Head : SExpr := SExpr.mkInst [level]
      (NatGeneration.rule 0 NatGeneration.flatCtors[0]).rhs
    let G1 : List SExpr := Motive :: Gamma
    let G2 : List SExpr := MinorZero :: G1
    IsDefEqStrong G1 (Head.app (SExpr.bvar 0))
        (Head.app (SExpr.bvar 0))
        (SExpr.forallE MinorZero (SExpr.forallE MinorSucc Result)) ∧
      IsDefEqStrong G2
        ((Head.app (SExpr.bvar 1)).app (SExpr.bvar 0))
        ((Head.app (SExpr.bvar 1)).app (SExpr.bvar 0))
        (SExpr.forallE MinorSucc Result) := by
  letI : Params := natParams univs
  let NatS : SExpr := SExpr.const ``Nat []
  let Motive : SExpr := SExpr.forallE NatS (SExpr.sort level)
  let MinorZero : SExpr :=
    (SExpr.bvar 0).app (SExpr.const ``Nat.zero [])
  let MinorSucc : SExpr :=
    SExpr.forallE NatS <|
      SExpr.forallE ((SExpr.bvar 2).app (SExpr.bvar 0)) <|
        (SExpr.bvar 3).app
          ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))
  let Result : SExpr :=
    (SExpr.bvar 2).app (SExpr.const ``Nat.zero [])
  let Head : SExpr := SExpr.mkInst [level]
    (NatGeneration.rule 0 NatGeneration.flatCtors[0]).rhs
  let G1 : List SExpr := Motive :: Gamma
  let G2 : List SExpr := MinorZero :: G1
  obtain ⟨ruleSort, hRuleType⟩ := hRuleType
  have hRuleType' : IsDefEqStrong Gamma
      (SExpr.forallE Motive
        (SExpr.forallE MinorZero (SExpr.forallE MinorSucc Result)))
      (SExpr.forallE Motive
        (SExpr.forallE MinorZero (SExpr.forallE MinorSucc Result)))
      (SExpr.sort ruleSort) := by
    simpa [probeNatZeroRuleType, Motive, MinorZero, MinorSucc, Result,
      NatS] using hRuleType
  obtain ⟨⟨motiveSort, hMotiveType⟩, restSort1, hRest1⟩ :=
    hRuleType'.forallE_inv' (.inl rfl)
  obtain ⟨⟨zeroSort, hMinorZeroType⟩, restSort2, hRest2⟩ :=
    hRest1.forallE_inv' (.inl rfl)
  let rhoP : Lift := .skip .refl
  have WP : Ctx.Lift' rhoP Gamma G1 := .skip .refl
  have hRhsRaw : IsDefEqStrong Gamma Head Head
      (SExpr.mkInst [level]
        (NatGeneration.rule 0 NatGeneration.flatCtors[0]).type) := by
    simpa only [Head, probeNatZeroRuleTypeS_eq] using hRhs
  have hHeadG10 := natStrongWeak univs WP hRhsRaw
  obtain ⟨⟨_, _⟩, ⟨rhsClosed, typeClosed⟩⟩ :=
    natFinalEnv_ordered.closed.2
      (natRule_registered probeNatFlatCtorZero_lookup)
  rw [rhsClosed.mkInstS.lift'_eq .zero,
    typeClosed.mkInstS.lift'_eq .zero] at hHeadG10
  have hHeadG1 : IsDefEqStrong G1 Head Head
      (SExpr.forallE Motive
        (SExpr.forallE MinorZero (SExpr.forallE MinorSucc Result))) := by
    simpa [Head, probeNatZeroRuleTypeS_eq, probeNatZeroRuleType,
      Motive, MinorZero, MinorSucc, Result, NatS] using hHeadG10
  have hMotiveTypeG1 : IsDefEqStrong G1 Motive Motive
      (SExpr.sort motiveSort) := by
    simpa [G1, rhoP, Motive, NatS, SExpr.lift, SExpr.lift'] using
      natStrongWeak univs WP hMotiveType
  have hP : IsDefEqStrong G1 (SExpr.bvar 0) (SExpr.bvar 0) Motive := by
    have hLookup : Lookup G1 0 Motive.lift := .zero
    have hBvar := IsDefEqStrong.bvar hLookup (by
      simpa [Motive, NatS, SExpr.lift, SExpr.lift'] using hMotiveTypeG1)
    simpa [Motive, NatS, SExpr.lift, SExpr.lift'] using hBvar
  have hCodP : IsDefEqStrong (Motive :: G1)
      (SExpr.forallE MinorZero (SExpr.forallE MinorSucc Result))
      (SExpr.forallE MinorZero (SExpr.forallE MinorSucc Result))
      (SExpr.sort restSort1) := by
    simpa [G1, rhoP, Motive, MinorZero, MinorSucc, Result, NatS,
      SExpr.lift, SExpr.lift'] using
      natStrongWeak univs WP.cons hRest1
  have hResultP : IsDefEqStrong G1
      ((SExpr.forallE MinorZero
        (SExpr.forallE MinorSucc Result)).inst (SExpr.bvar 0))
      ((SExpr.forallE MinorZero
        (SExpr.forallE MinorSucc Result)).inst (SExpr.bvar 0))
      (SExpr.sort restSort1) := by
    simpa [G1, Motive, MinorZero, MinorSucc, Result, NatS,
      SExpr.inst, SExpr.subst, Subst.one, Subst.cons, Subst.lift,
      Subst.id, probeCancelUnderOne, probeCancelUnderTwo] using hRest1
  have hPrefixP0 := IsDefEqStrong.appDF
    hMotiveTypeG1 hCodP hHeadG1 hP hResultP
  have hPrefixP : IsDefEqStrong G1 (Head.app (SExpr.bvar 0))
      (Head.app (SExpr.bvar 0))
      (SExpr.forallE MinorZero (SExpr.forallE MinorSucc Result)) := by
    simpa [Head, MinorZero, MinorSucc, Result, NatS,
      SExpr.inst, SExpr.subst, Subst.one, Subst.cons, Subst.lift,
      Subst.id, probeCancelUnderOne, probeCancelUnderTwo] using hPrefixP0
  let rhoZ : Lift := .skip .refl
  have WZ : Ctx.Lift' rhoZ G1 G2 := .skip .refl
  have hPrefixPG2 := natStrongWeak univs WZ hPrefixP
  have hHeadClosed : Head.lift' rhoZ = Head := by
    dsimp [Head]
    exact rhsClosed.mkInstS.lift'_eq .zero
  change IsDefEqStrong G2
    ((Head.lift' rhoZ).app (SExpr.bvar 1))
    ((Head.lift' rhoZ).app (SExpr.bvar 1))
    ((SExpr.forallE MinorZero
      (SExpr.forallE MinorSucc Result)).lift' rhoZ) at hPrefixPG2
  rw [hHeadClosed] at hPrefixPG2
  have hMinorZeroTypeG2 := natStrongWeak univs WZ hMinorZeroType
  have hRest2G := natStrongWeak univs WZ.cons hRest2
  have hZ : IsDefEqStrong G2 (SExpr.bvar 0) (SExpr.bvar 0)
      (MinorZero.lift' rhoZ) := by
    exact IsDefEqStrong.bvar (.zero : Lookup G2 0 MinorZero.lift)
      (by simpa [rhoZ, SExpr.lift] using hMinorZeroTypeG2)
  have hResultZ : IsDefEqStrong G2
      (((SExpr.forallE MinorSucc Result).lift' rhoZ.cons).inst
        (SExpr.bvar 0))
      (((SExpr.forallE MinorSucc Result).lift' rhoZ.cons).inst
        (SExpr.bvar 0))
      (SExpr.sort restSort2) := by
    simpa [G2, G1, rhoZ, Motive, MinorZero, MinorSucc, Result, NatS,
      SExpr.lift, SExpr.lift', SExpr.inst, SExpr.subst,
      Subst.one, Subst.cons, Subst.lift, Subst.id,
      probeCancelUnderOne, probeCancelUnderTwo] using hRest2
  have hPrefixPZ0 := IsDefEqStrong.appDF
    hMinorZeroTypeG2 hRest2G hPrefixPG2 hZ hResultZ
  have hPrefixPZ : IsDefEqStrong G2
      ((Head.app (SExpr.bvar 1)).app (SExpr.bvar 0))
      ((Head.app (SExpr.bvar 1)).app (SExpr.bvar 0))
      (SExpr.forallE MinorSucc Result) := by
    simpa [Head, G2, G1, rhoZ, Motive, MinorZero, MinorSucc, Result,
      NatS, SExpr.lift, SExpr.lift', SExpr.inst, SExpr.subst,
      Subst.one, Subst.cons, Subst.lift, Subst.id,
      probeCancelUnderOne, probeCancelUnderTwo] using hPrefixPZ0
  exact ⟨hPrefixP, hPrefixPZ⟩

/-- The closed generated zero equation is the local iota action under its
three binders, followed by three strong eta contractions on the RHS tower. -/
theorem natZeroRuleRegistered (univs : Nat)
    {Gamma : List (@SExpr (natParams univs))}
    (level : @SLevel (natParams univs))
    (_hLhs : @IsDefEqStrong (natParams univs) Gamma
      (@SExpr.mkInst (natParams univs) [level]
        (NatGeneration.rule 0 NatGeneration.flatCtors[0]).lhs)
      (@SExpr.mkInst (natParams univs) [level]
        (NatGeneration.rule 0 NatGeneration.flatCtors[0]).lhs)
      (probeNatZeroRuleType univs level))
    (hRhs : @IsDefEqStrong (natParams univs) Gamma
      (@SExpr.mkInst (natParams univs) [level]
        (NatGeneration.rule 0 NatGeneration.flatCtors[0]).rhs)
      (@SExpr.mkInst (natParams univs) [level]
        (NatGeneration.rule 0 NatGeneration.flatCtors[0]).rhs)
      (probeNatZeroRuleType univs level)) :
    @IsDefEqStrong (natParams univs) Gamma
      (@SExpr.mkInst (natParams univs) [level]
        (NatGeneration.rule 0 NatGeneration.flatCtors[0]).lhs)
      (@SExpr.mkInst (natParams univs) [level]
        (NatGeneration.rule 0 NatGeneration.flatCtors[0]).rhs)
      (probeNatZeroRuleType univs level) := by
  letI : Params := natParams univs
  let NatS : SExpr := SExpr.const ``Nat []
  let Motive : SExpr := SExpr.forallE NatS (SExpr.sort level)
  let MinorZero : SExpr :=
    (SExpr.bvar 0).app (SExpr.const ``Nat.zero [])
  let MinorSucc : SExpr :=
    SExpr.forallE NatS <|
      SExpr.forallE ((SExpr.bvar 2).app (SExpr.bvar 0)) <|
        (SExpr.bvar 3).app
          ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))
  let Result : SExpr :=
    (SExpr.bvar 2).app (SExpr.const ``Nat.zero [])
  let Head : SExpr := SExpr.mkInst [level]
    (NatGeneration.rule 0 NatGeneration.flatCtors[0]).rhs
  let G1 : List SExpr := Motive :: Gamma
  let G2 : List SExpr := MinorZero :: G1
  let Delta : List SExpr := MinorSucc :: G2
  let Redex : SExpr :=
    ((((SExpr.const ``Nat.rec [level]).app (SExpr.bvar 2)).app
      (SExpr.bvar 1)).app (SExpr.bvar 0)).app
        (SExpr.const ``Nat.zero [])
  let AppliedRhs : SExpr :=
    [SExpr.bvar 2, SExpr.bvar 1, SExpr.bvar 0].foldl
      (fun f a => f.app a) Head
  have hRuleType := hRhs.isType
  obtain ⟨ruleSort, hRuleType0⟩ := hRuleType
  have hRuleType' : IsDefEqStrong Gamma
      (SExpr.forallE Motive
        (SExpr.forallE MinorZero (SExpr.forallE MinorSucc Result)))
      (SExpr.forallE Motive
        (SExpr.forallE MinorZero (SExpr.forallE MinorSucc Result)))
      (SExpr.sort ruleSort) := by
    simpa [probeNatZeroRuleType, Motive, MinorZero, MinorSucc, Result,
      NatS] using hRuleType0
  obtain ⟨⟨motiveSort, hMotiveType⟩, restSort1, hRest1⟩ :=
    hRuleType'.forallE_inv' (.inl rfl)
  obtain ⟨⟨zeroSort, hMinorZeroType⟩, restSort2, hRest2⟩ :=
    hRest1.forallE_inv' (.inl rfl)
  obtain ⟨⟨succSort, hMinorSuccType⟩, resultSort, hResultType⟩ :=
    hRest2.forallE_inv' (.inl rfl)
  have hLocal : IsDefEqStrong Delta Redex AppliedRhs Result := by
    simpa [Head, G2, G1, Delta, Redex, AppliedRhs, Result] using
      natZeroRuleLocalStrong univs (Gamma := Gamma) level
        ⟨ruleSort, hRuleType0⟩ hRhs
  obtain ⟨hPrefixP, hPrefixPZ⟩ :=
    natZeroRulePrefixesStrong univs (Gamma := Gamma) level
      ⟨ruleSort, hRuleType0⟩ hRhs
  have hLamS : IsDefEqStrong G2
      (SExpr.lam MinorSucc Redex) (SExpr.lam MinorSucc AppliedRhs)
      (SExpr.forallE MinorSucc Result) := by
    exact .lamDF hMinorSuccType hResultType hResultType hLocal hLocal
  obtain ⟨⟨_, _⟩, ⟨rhsClosed, _⟩⟩ :=
    natFinalEnv_ordered.closed.2
      (natRule_registered probeNatFlatCtorZero_lookup)
  have hEtaS0 := IsDefEqStrong.eta hPrefixPZ hLamS.hasType.2
  have hEtaS : IsDefEqStrong G2
      (SExpr.lam MinorSucc AppliedRhs)
      ((Head.app (SExpr.bvar 1)).app (SExpr.bvar 0))
      (SExpr.forallE MinorSucc Result) := by
    simpa [Head, AppliedRhs, SExpr.lift, SExpr.lift',
      rhsClosed.mkInstS.lift_eq] using hEtaS0
  have hSucc : IsDefEqStrong G2
      (SExpr.lam MinorSucc Redex)
      ((Head.app (SExpr.bvar 1)).app (SExpr.bvar 0))
      (SExpr.forallE MinorSucc Result) := hLamS.trans hEtaS
  have hLamZ : IsDefEqStrong G1
      (SExpr.lam MinorZero (SExpr.lam MinorSucc Redex))
      (SExpr.lam MinorZero
        ((Head.app (SExpr.bvar 1)).app (SExpr.bvar 0)))
      (SExpr.forallE MinorZero (SExpr.forallE MinorSucc Result)) := by
    exact .lamDF hMinorZeroType hRest2 hRest2 hSucc hSucc
  have hEtaZ0 := IsDefEqStrong.eta hPrefixP hLamZ.hasType.2
  have hEtaZ : IsDefEqStrong G1
      (SExpr.lam MinorZero
        ((Head.app (SExpr.bvar 1)).app (SExpr.bvar 0)))
      (Head.app (SExpr.bvar 0))
      (SExpr.forallE MinorZero (SExpr.forallE MinorSucc Result)) := by
    simpa [Head, SExpr.lift, SExpr.lift',
      rhsClosed.mkInstS.lift_eq] using hEtaZ0
  have hZero : IsDefEqStrong G1
      (SExpr.lam MinorZero (SExpr.lam MinorSucc Redex))
      (Head.app (SExpr.bvar 0))
      (SExpr.forallE MinorZero (SExpr.forallE MinorSucc Result)) :=
    hLamZ.trans hEtaZ
  have hLamP : IsDefEqStrong Gamma
      (SExpr.lam Motive
        (SExpr.lam MinorZero (SExpr.lam MinorSucc Redex)))
      (SExpr.lam Motive (Head.app (SExpr.bvar 0)))
      (SExpr.forallE Motive
        (SExpr.forallE MinorZero (SExpr.forallE MinorSucc Result))) := by
    exact .lamDF hMotiveType hRest1 hRest1 hZero hZero
  have hHeadExplicit : IsDefEqStrong Gamma Head Head
      (SExpr.forallE Motive
        (SExpr.forallE MinorZero (SExpr.forallE MinorSucc Result))) := by
    simpa [Head, probeNatZeroRuleType, Motive, MinorZero, MinorSucc,
      Result, NatS] using hRhs
  have hEtaP0 := IsDefEqStrong.eta hHeadExplicit hLamP.hasType.2
  have hEtaP : IsDefEqStrong Gamma
      (SExpr.lam Motive (Head.app (SExpr.bvar 0))) Head
      (SExpr.forallE Motive
        (SExpr.forallE MinorZero (SExpr.forallE MinorSucc Result))) := by
    simpa [Head, SExpr.lift, SExpr.lift',
      rhsClosed.mkInstS.lift_eq] using hEtaP0
  have hClosed := hLamP.trans hEtaP
  simpa [Head, Motive, MinorZero, MinorSucc, Result, Redex, NatS,
    probeNatZeroRuleType, probeNatZeroRuleLhsV_eq,
    probeNatZeroRuleLhsV, probeNatRuleBindersV,
    probeNatZeroRuleLhsBodyV, SExpr.mkInst, VExpr.instL,
    VExpr.lamN, probeInstVParamZero] using hClosed

/-- Strong typing of the successor redex under the four generated rule
binders.  The recursor prefix is reconstructed from the common motive and
minor premises, then applied to `Nat.succ pred`. -/
theorem natSuccRuleBodyStrong (univs : Nat)
    {Gamma : List (@SExpr (natParams univs))}
    (level : @SLevel (natParams univs))
    (hRuleType : ∃ u, @IsDefEqStrong (natParams univs) Gamma
      (probeNatSuccRuleType univs level)
      (probeNatSuccRuleType univs level)
      (@SExpr.sort (natParams univs) u)) :
    letI : Params := natParams univs
    let NatS : SExpr := SExpr.const ``Nat []
    let Motive : SExpr := SExpr.forallE NatS (SExpr.sort level)
    let MinorZero : SExpr :=
      (SExpr.bvar 0).app (SExpr.const ``Nat.zero [])
    let MinorSucc : SExpr :=
      SExpr.forallE NatS <|
        SExpr.forallE ((SExpr.bvar 2).app (SExpr.bvar 0)) <|
          (SExpr.bvar 3).app
            ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))
    let Delta : List SExpr := NatS :: MinorSucc :: MinorZero :: Motive :: Gamma
    let Redex : SExpr :=
      ((((SExpr.const ``Nat.rec [level]).app (SExpr.bvar 3)).app
        (SExpr.bvar 2)).app (SExpr.bvar 1)).app
          ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0))
    let Result : SExpr :=
      (SExpr.bvar 3).app
        ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0))
    IsDefEqStrong Delta Redex Redex Result := by
  letI : Params := natParams univs
  let NatS : SExpr := SExpr.const ``Nat []
  let Motive : SExpr := SExpr.forallE NatS (SExpr.sort level)
  let MinorZero : SExpr :=
    (SExpr.bvar 0).app (SExpr.const ``Nat.zero [])
  let MinorSucc : SExpr :=
    SExpr.forallE NatS <|
      SExpr.forallE ((SExpr.bvar 2).app (SExpr.bvar 0)) <|
        (SExpr.bvar 3).app
          ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))
  let Result : SExpr :=
    (SExpr.bvar 3).app
      ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0))
  let Delta : List SExpr := NatS :: MinorSucc :: MinorZero :: Motive :: Gamma
  let Redex : SExpr :=
    ((((SExpr.const ``Nat.rec [level]).app (SExpr.bvar 3)).app
      (SExpr.bvar 2)).app (SExpr.bvar 1)).app
        ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0))
  obtain ⟨ruleSort, hRuleType⟩ := hRuleType
  have hRuleType' : IsDefEqStrong Gamma
      (SExpr.forallE Motive
        (SExpr.forallE MinorZero
          (SExpr.forallE MinorSucc (SExpr.forallE NatS Result))))
      (SExpr.forallE Motive
        (SExpr.forallE MinorZero
          (SExpr.forallE MinorSucc (SExpr.forallE NatS Result))))
      (SExpr.sort ruleSort) := by
    simpa [probeNatSuccRuleType, Motive, MinorZero, MinorSucc, Result,
      NatS] using hRuleType
  obtain ⟨⟨motiveSort, hMotiveType⟩, restSort1, hRest1⟩ :=
    hRuleType'.forallE_inv' (.inl rfl)
  obtain ⟨⟨zeroSort, hMinorZeroType⟩, restSort2, hRest2⟩ :=
    hRest1.forallE_inv' (.inl rfl)
  obtain ⟨⟨succSort, hMinorSuccType⟩, restSort3, hRest3⟩ :=
    hRest2.forallE_inv' (.inl rfl)
  obtain ⟨⟨natBinderSort, hNatBinderType⟩, resultSort, hResultType⟩ :=
    hRest3.forallE_inv' (.inl rfl)
  let G0 : List SExpr := Motive :: Gamma
  let G00 : List SExpr := MinorZero :: G0
  let G000 : List SExpr := MinorSucc :: G00
  let rho3base : Lift := .skip (.skip (.skip .refl))
  have W3base : Ctx.Lift' rho3base Gamma G000 :=
    .skip (.skip (.skip .refl))
  have hMotiveG000 := natStrongWeak univs W3base hMotiveType
  have hP0 : IsDefEqStrong G000 (SExpr.bvar 2) (SExpr.bvar 2)
      Motive := by
    have hLookup : Lookup G000 2 Motive.lift.lift.lift :=
      .succ (.succ .zero)
    have hBvar := IsDefEqStrong.bvar hLookup hMotiveG000
    simpa [G000, G00, G0, Motive, NatS,
      SExpr.lift, SExpr.lift'] using hBvar
  have hPZero : IsDefEqStrong G000
      ((SExpr.bvar 2).app (SExpr.const ``Nat.zero []))
      ((SExpr.bvar 2).app (SExpr.const ``Nat.zero []))
      (SExpr.sort level) := by
    simpa [SExpr.inst, SExpr.subst, Subst.one, Subst.cons,
      Subst.lift, Subst.id] using
      IsDefEqStrong.appDF (natTypeStrong univs G000) .sort hP0
        (natZeroStrong univs G000) .sort
  have hZeroAfterSucc : IsDefEqStrong G00
      (SExpr.forallE MinorSucc
        ((SExpr.bvar 2).app (SExpr.const ``Nat.zero [])))
      (SExpr.forallE MinorSucc
        ((SExpr.bvar 2).app (SExpr.const ``Nat.zero [])))
      (SExpr.sort (succSort.imax level)) :=
    .forallEDF hMinorSuccType hPZero hPZero
  have hZeroAfterZero : IsDefEqStrong G0
      (SExpr.forallE MinorZero
        (SExpr.forallE MinorSucc
          ((SExpr.bvar 2).app (SExpr.const ``Nat.zero []))))
      (SExpr.forallE MinorZero
        (SExpr.forallE MinorSucc
          ((SExpr.bvar 2).app (SExpr.const ``Nat.zero []))))
      (SExpr.sort (zeroSort.imax (succSort.imax level))) :=
    .forallEDF hMinorZeroType hZeroAfterSucc hZeroAfterSucc
  have hZeroRuleType0 : IsDefEqStrong Gamma
      (SExpr.forallE Motive
        (SExpr.forallE MinorZero
          (SExpr.forallE MinorSucc
            ((SExpr.bvar 2).app (SExpr.const ``Nat.zero [])))))
      (SExpr.forallE Motive
        (SExpr.forallE MinorZero
          (SExpr.forallE MinorSucc
            ((SExpr.bvar 2).app (SExpr.const ``Nat.zero [])))))
      (SExpr.sort
        (motiveSort.imax (zeroSort.imax (succSort.imax level)))) :=
    .forallEDF hMotiveType hZeroAfterZero hZeroAfterZero
  let rho4 : Lift := .skip (.skip (.skip (.skip .refl)))
  have W4 : Ctx.Lift' rho4 Gamma Delta :=
    .skip (.skip (.skip (.skip .refl)))
  have hZeroRuleTypeD0 := natStrongWeak univs W4 hZeroRuleType0
  have hZeroRuleTypeD : IsDefEqStrong Delta
      (probeNatZeroRuleType univs level)
      (probeNatZeroRuleType univs level)
      (SExpr.sort
        (motiveSort.imax (zeroSort.imax (succSort.imax level)))) := by
    simpa [rho4, probeNatZeroRuleType, Motive, MinorZero, MinorSucc,
      NatS, SExpr.lift, SExpr.lift'] using hZeroRuleTypeD0
  have hRec := natRecStrongOfZeroRuleType univs (Gamma := Delta) level
    ⟨_, hZeroRuleTypeD⟩
  let rho3 : Lift := .skip (.skip (.skip .refl))
  have W3 : Ctx.Lift' rho3 (Motive :: Gamma) Delta :=
    .skip (.skip (.skip .refl))
  let rho2 : Lift := .skip (.skip .refl)
  have W2 : Ctx.Lift' rho2 (MinorZero :: Motive :: Gamma) Delta :=
    .skip (.skip .refl)
  have hMotiveTypeD : IsDefEqStrong Delta Motive Motive
      (SExpr.sort motiveSort) := by
    simpa [rho4, Motive, NatS, SExpr.lift, SExpr.lift'] using
      natStrongWeak univs W4 hMotiveType
  let ZeroTy : SExpr :=
    (SExpr.bvar 3).app (SExpr.const ``Nat.zero [])
  let SuccTy : SExpr :=
    SExpr.forallE NatS <|
      SExpr.forallE ((SExpr.bvar 4).app (SExpr.bvar 0)) <|
        (SExpr.bvar 5).app
          ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))
  have hZeroTypeD : IsDefEqStrong Delta ZeroTy ZeroTy
      (SExpr.sort zeroSort) := by
    simpa [rho3, ZeroTy, MinorZero, SExpr.lift, SExpr.lift'] using
      natStrongWeak univs W3 hMinorZeroType
  have hSuccTypeD : IsDefEqStrong Delta SuccTy SuccTy
      (SExpr.sort succSort) := by
    simpa [rho2, SuccTy, MinorSucc, NatS, SExpr.lift, SExpr.lift'] using
      natStrongWeak univs W2 hMinorSuccType
  have hP : IsDefEqStrong Delta (SExpr.bvar 3) (SExpr.bvar 3) Motive := by
    have hLookup : Lookup Delta 3 (Motive.lift.lift.lift.lift) :=
      .succ (.succ (.succ .zero))
    have hBvar := IsDefEqStrong.bvar hLookup
      (natStrongWeak univs W4 hMotiveType)
    simpa [Motive, NatS, SExpr.lift, SExpr.lift'] using hBvar
  have hZ : IsDefEqStrong Delta (SExpr.bvar 2) (SExpr.bvar 2) ZeroTy := by
    have hLookup : Lookup Delta 2 (MinorZero.lift.lift.lift) :=
      .succ (.succ .zero)
    have hBvar := IsDefEqStrong.bvar hLookup (by
      simpa [ZeroTy, MinorZero, SExpr.lift, SExpr.lift'] using hZeroTypeD)
    simpa [ZeroTy, MinorZero, SExpr.lift, SExpr.lift'] using hBvar
  have hS : IsDefEqStrong Delta (SExpr.bvar 1) (SExpr.bvar 1) SuccTy := by
    have hLookup : Lookup Delta 1 (MinorSucc.lift.lift) := .succ .zero
    have hBvar := IsDefEqStrong.bvar hLookup (by
      simpa [SuccTy, MinorSucc, NatS, SExpr.lift, SExpr.lift'] using
        hSuccTypeD)
    simpa [SuccTy, MinorSucc, NatS, SExpr.lift, SExpr.lift'] using hBvar
  have hPred : IsDefEqStrong Delta (SExpr.bvar 0) (SExpr.bvar 0) NatS := by
    have hLookup : Lookup Delta 0 NatS.lift := .zero
    have hNat := natTypeStrong univs Delta
    change IsDefEqStrong Delta (SExpr.const ``Nat [])
      (SExpr.const ``Nat [])
      (SExpr.mkInst [] InductiveFixtures.natType.type) at hNat
    rw [probeNatTypeTypeV_eq] at hNat
    exact IsDefEqStrong.bvar hLookup (by
      simpa [NatS, SExpr.lift, SExpr.lift', SExpr.mkInst] using hNat)
  let MajorTail : SExpr :=
    SExpr.forallE NatS ((SExpr.bvar 4).app (SExpr.bvar 0))
  let natSort : SLevel := SLevel.instV [] VLevel.zero.succ
  let majorTailSort : SLevel := natSort.imax level
  have hMotiveDeep : IsDefEqStrong (NatS :: Delta)
      (SExpr.bvar 4) (SExpr.bvar 4) Motive := by
    let rho5 : Lift := .skip (.skip (.skip (.skip (.skip .refl))))
    have W5 : Ctx.Lift' rho5 Gamma (NatS :: Delta) :=
      .skip (.skip (.skip (.skip (.skip .refl))))
    have hLift := natStrongWeak univs W5 hMotiveType
    have hLookup : Lookup (NatS :: Delta) 4
        (Motive.lift.lift.lift.lift.lift) :=
      .succ (.succ (.succ (.succ .zero)))
    have hBvar := IsDefEqStrong.bvar hLookup hLift
    simpa [Motive, NatS, SExpr.lift, SExpr.lift'] using hBvar
  have hMajor : IsDefEqStrong (NatS :: Delta)
      (SExpr.bvar 0) (SExpr.bvar 0) NatS := by
    have hNat := natTypeStrong univs (NatS :: Delta)
    change IsDefEqStrong (NatS :: Delta) (SExpr.const ``Nat [])
      (SExpr.const ``Nat [])
      (SExpr.mkInst [] InductiveFixtures.natType.type) at hNat
    rw [probeNatTypeTypeV_eq] at hNat
    exact .bvar .zero (by
      simpa [NatS, SExpr.lift, SExpr.lift', SExpr.mkInst] using hNat)
  have hMotiveMajor : IsDefEqStrong (NatS :: Delta)
      ((SExpr.bvar 4).app (SExpr.bvar 0))
      ((SExpr.bvar 4).app (SExpr.bvar 0)) (SExpr.sort level) :=
    .appDF (natTypeStrong univs (NatS :: Delta)) .sort
      hMotiveDeep hMajor .sort
  have hMajorTail : IsDefEqStrong Delta MajorTail MajorTail
      (SExpr.sort majorTailSort) := by
    simpa [MajorTail, majorTailSort, natSort] using
      IsDefEqStrong.forallEDF
        (natTypeStrong univs Delta) hMotiveMajor hMotiveMajor
  let RG1 : List SExpr := Motive :: Delta
  let RG2 : List SExpr := MinorZero :: RG1
  let RG3 : List SExpr := MinorSucc :: RG2
  have hZeroTypeG : IsDefEqStrong RG1 MinorZero MinorZero
      (SExpr.sort zeroSort) := by
    have h := natStrongWeak univs W4.cons hMinorZeroType
    simpa [RG1, rho4, Motive, MinorZero, NatS,
      SExpr.lift, SExpr.lift'] using h
  have hSuccTypeG : IsDefEqStrong RG2 MinorSucc MinorSucc
      (SExpr.sort succSort) := by
    have h := natStrongWeak univs W4.cons.cons hMinorSuccType
    simpa [RG2, RG1, rho4, Motive, MinorZero, MinorSucc, NatS,
      SExpr.lift, SExpr.lift'] using h
  have hMotiveGeneric : IsDefEqStrong (NatS :: RG3)
      (SExpr.bvar 3) (SExpr.bvar 3) Motive := by
    let rho4g : Lift := .skip (.skip (.skip (.skip .refl)))
    have W4g : Ctx.Lift' rho4g Delta (NatS :: RG3) :=
      .skip (.skip (.skip (.skip .refl)))
    have hLift := natStrongWeak univs W4g hMotiveTypeD
    have hLookup : Lookup (NatS :: RG3) 3
        (Motive.lift.lift.lift.lift) := .succ (.succ (.succ .zero))
    have hBvar := IsDefEqStrong.bvar hLookup hLift
    simpa [RG3, RG2, RG1, Motive, NatS,
      SExpr.lift, SExpr.lift'] using hBvar
  have hMajorGeneric : IsDefEqStrong (NatS :: RG3)
      (SExpr.bvar 0) (SExpr.bvar 0) NatS := by
    have hNat := natTypeStrong univs (NatS :: RG3)
    change IsDefEqStrong (NatS :: RG3) (SExpr.const ``Nat [])
      (SExpr.const ``Nat [])
      (SExpr.mkInst [] InductiveFixtures.natType.type) at hNat
    rw [probeNatTypeTypeV_eq] at hNat
    exact .bvar .zero (by
      simpa [NatS, SExpr.lift, SExpr.lift', SExpr.mkInst] using hNat)
  have hGenericResult : IsDefEqStrong (NatS :: RG3)
      ((SExpr.bvar 3).app (SExpr.bvar 0))
      ((SExpr.bvar 3).app (SExpr.bvar 0)) (SExpr.sort level) :=
    .appDF (natTypeStrong univs (NatS :: RG3)) .sort
      hMotiveGeneric hMajorGeneric .sort
  have hMajorTailG : IsDefEqStrong RG3
      (SExpr.forallE NatS ((SExpr.bvar 3).app (SExpr.bvar 0)))
      (SExpr.forallE NatS ((SExpr.bvar 3).app (SExpr.bvar 0)))
      (SExpr.sort majorTailSort) := by
    simpa [majorTailSort, natSort] using
      IsDefEqStrong.forallEDF
        (natTypeStrong univs RG3) hGenericResult hGenericResult
  have hRecAfterSuccG := IsDefEqStrong.forallEDF
    hSuccTypeG hMajorTailG hMajorTailG
  have hRecAfterZeroG := IsDefEqStrong.forallEDF
    hZeroTypeG hRecAfterSuccG hRecAfterSuccG
  have hMajorTailS : IsDefEqStrong (SuccTy :: Delta)
      MajorTail.lift MajorTail.lift (SExpr.sort majorTailSort) := by
    simpa [MajorTail, SuccTy, SExpr.lift, ← SExpr.lift'_comp] using
      natStrongWeak univs (Ctx.Lift'.one (A := SuccTy)) hMajorTail
  have hAfterSucc : IsDefEqStrong Delta
      (SExpr.forallE SuccTy MajorTail.lift)
      (SExpr.forallE SuccTy MajorTail.lift)
      (SExpr.sort (succSort.imax majorTailSort)) :=
    .forallEDF hSuccTypeD hMajorTailS hMajorTailS
  have hSuccTypeZ : IsDefEqStrong (ZeroTy :: Delta)
      SuccTy.lift SuccTy.lift (SExpr.sort succSort) := by
    simpa [SuccTy, ZeroTy, SExpr.lift, ← SExpr.lift'_comp] using
      natStrongWeak univs (Ctx.Lift'.one (A := ZeroTy)) hSuccTypeD
  let rhoZS : Lift := .skip (.skip .refl)
  have WZS : Ctx.Lift' rhoZS Delta
      (SuccTy.lift :: ZeroTy :: Delta) := .skip (.skip .refl)
  have hMajorTailZS : IsDefEqStrong (SuccTy.lift :: ZeroTy :: Delta)
      MajorTail.lift.lift MajorTail.lift.lift
      (SExpr.sort majorTailSort) := by
    simpa [rhoZS, SExpr.lift, ← SExpr.lift'_comp] using
      natStrongWeak univs WZS hMajorTail
  have hAfterSuccZ : IsDefEqStrong (ZeroTy :: Delta)
      (SExpr.forallE SuccTy.lift MajorTail.lift.lift)
      (SExpr.forallE SuccTy.lift MajorTail.lift.lift)
      (SExpr.sort (succSort.imax majorTailSort)) :=
    .forallEDF hSuccTypeZ hMajorTailZS hMajorTailZS
  have hAfterZero : IsDefEqStrong Delta
      (SExpr.forallE ZeroTy
        (SExpr.forallE SuccTy.lift MajorTail.lift.lift))
      (SExpr.forallE ZeroTy
        (SExpr.forallE SuccTy.lift MajorTail.lift.lift))
      (SExpr.sort (zeroSort.imax (succSort.imax majorTailSort))) :=
    .forallEDF hZeroTypeD hAfterSuccZ hAfterSuccZ
  have hRecP0 := IsDefEqStrong.appDF
    hMotiveTypeD hRecAfterZeroG hRec hP hAfterZero
  have hRecP : IsDefEqStrong Delta
      ((SExpr.const ``Nat.rec [level]).app (SExpr.bvar 3))
      ((SExpr.const ``Nat.rec [level]).app (SExpr.bvar 3))
      (SExpr.forallE ZeroTy
        (SExpr.forallE SuccTy.lift MajorTail.lift.lift)) := by
    simpa [RG3, RG2, RG1, ZeroTy, SuccTy, MajorTail, Motive,
      MinorZero, MinorSucc, NatS, SExpr.inst, SExpr.subst,
      Subst.one, Subst.cons, Subst.lift, Subst.id,
      probeCancelUnderOne, probeCancelUnderTwo] using hRecP0
  have hRecPZ0 := IsDefEqStrong.appDF
    hZeroTypeD hAfterSuccZ hRecP hZ hAfterSucc
  have hRecPZ : IsDefEqStrong Delta
      (((SExpr.const ``Nat.rec [level]).app (SExpr.bvar 3)).app
        (SExpr.bvar 2))
      (((SExpr.const ``Nat.rec [level]).app (SExpr.bvar 3)).app
        (SExpr.bvar 2))
      (SExpr.forallE SuccTy MajorTail.lift) := by
    simpa [ZeroTy, SuccTy, MajorTail, NatS, SExpr.lift, SExpr.lift',
      SExpr.inst, SExpr.subst, Subst.one, Subst.cons, Subst.lift,
      Subst.id, probeCancelUnderOne, probeCancelUnderTwo] using hRecPZ0
  have hRecPZS0 := IsDefEqStrong.appDF
    hSuccTypeD hMajorTailS hRecPZ hS hMajorTail
  have hRecPZS : IsDefEqStrong Delta
      ((((SExpr.const ``Nat.rec [level]).app (SExpr.bvar 3)).app
        (SExpr.bvar 2)).app (SExpr.bvar 1))
      ((((SExpr.const ``Nat.rec [level]).app (SExpr.bvar 3)).app
        (SExpr.bvar 2)).app (SExpr.bvar 1)) MajorTail := by
    simpa [SuccTy, MajorTail, NatS, SExpr.lift, SExpr.lift',
      SExpr.inst, SExpr.subst, Subst.one, Subst.cons, Subst.lift,
      Subst.id, probeCancelUnderOne, probeCancelUnderTwo] using hRecPZS0
  have hSuccPred0 := IsDefEqStrong.appDF
    (natTypeStrong univs Delta)
    (natTypeStrong univs (NatS :: Delta))
    (natSuccStrong univs Delta) hPred (natTypeStrong univs Delta)
  have hSuccPred : IsDefEqStrong Delta
      ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0))
      ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0)) NatS := by
    simpa [NatS, SExpr.inst, SExpr.subst, Subst.one, Subst.cons,
      Subst.lift, Subst.id] using hSuccPred0
  have hPSuccPred : IsDefEqStrong Delta Result Result
      (SExpr.sort level) := by
    simpa [Result, SExpr.inst, SExpr.subst, Subst.one, Subst.cons,
      Subst.lift, Subst.id] using
      IsDefEqStrong.appDF (natTypeStrong univs Delta) .sort hP
        hSuccPred .sort
  have hBody0 := IsDefEqStrong.appDF
    (natTypeStrong univs Delta) hMotiveMajor hRecPZS hSuccPred hPSuccPred
  simpa [Delta, Redex, Result, MajorTail, NatS,
    SExpr.inst, SExpr.subst, Subst.one, Subst.cons,
    Subst.lift, Subst.id] using hBody0

/-- Apply the closed successor RHS tower to motive, minors, and predecessor. -/
theorem natSuccRuleAppliedStrong (univs : Nat)
    {Gamma : List (@SExpr (natParams univs))}
    (level : @SLevel (natParams univs))
    (hRuleType : ∃ u, @IsDefEqStrong (natParams univs) Gamma
      (probeNatSuccRuleType univs level)
      (probeNatSuccRuleType univs level)
      (@SExpr.sort (natParams univs) u))
    (hHead : @IsDefEqStrong (natParams univs) Gamma
      (@SExpr.mkInst (natParams univs) [level]
        (NatGeneration.rule 1 NatGeneration.flatCtors[1]).rhs)
      (@SExpr.mkInst (natParams univs) [level]
        (NatGeneration.rule 1 NatGeneration.flatCtors[1]).rhs)
      (probeNatSuccRuleType univs level)) :
    letI : Params := natParams univs
    let NatS : SExpr := SExpr.const ``Nat []
    let Motive : SExpr := SExpr.forallE NatS (SExpr.sort level)
    let MinorZero : SExpr :=
      (SExpr.bvar 0).app (SExpr.const ``Nat.zero [])
    let MinorSucc : SExpr :=
      SExpr.forallE NatS <|
        SExpr.forallE ((SExpr.bvar 2).app (SExpr.bvar 0)) <|
          (SExpr.bvar 3).app
            ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))
    let Delta : List SExpr := NatS :: MinorSucc :: MinorZero :: Motive :: Gamma
    let AppliedRhs : SExpr :=
      [SExpr.bvar 3, SExpr.bvar 2, SExpr.bvar 1,
        SExpr.bvar 0].foldl (fun f a => f.app a)
        (SExpr.mkInst [level]
          (NatGeneration.rule 1 NatGeneration.flatCtors[1]).rhs)
    let Result : SExpr :=
      (SExpr.bvar 3).app
        ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0))
    IsDefEqStrong Delta AppliedRhs AppliedRhs Result := by
  letI : Params := natParams univs
  let NatS : SExpr := SExpr.const ``Nat []
  let Motive : SExpr := SExpr.forallE NatS (SExpr.sort level)
  let MinorZero : SExpr :=
    (SExpr.bvar 0).app (SExpr.const ``Nat.zero [])
  let MinorSucc : SExpr :=
    SExpr.forallE NatS <|
      SExpr.forallE ((SExpr.bvar 2).app (SExpr.bvar 0)) <|
        (SExpr.bvar 3).app
          ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))
  let Delta : List SExpr := NatS :: MinorSucc :: MinorZero :: Motive :: Gamma
  let AppliedRhs : SExpr :=
    [SExpr.bvar 3, SExpr.bvar 2, SExpr.bvar 1,
      SExpr.bvar 0].foldl (fun f a => f.app a)
      (SExpr.mkInst [level]
        (NatGeneration.rule 1 NatGeneration.flatCtors[1]).rhs)
  let Result : SExpr :=
    (SExpr.bvar 3).app
      ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0))
  obtain ⟨ruleSort, hRuleType⟩ := hRuleType
  have hRuleType' : IsDefEqStrong Gamma
      (SExpr.forallE Motive
        (SExpr.forallE MinorZero
          (SExpr.forallE MinorSucc (SExpr.forallE NatS Result))))
      (SExpr.forallE Motive
        (SExpr.forallE MinorZero
          (SExpr.forallE MinorSucc (SExpr.forallE NatS Result))))
      (SExpr.sort ruleSort) := by
    simpa [probeNatSuccRuleType, Motive, MinorZero, MinorSucc, Result,
      NatS] using hRuleType
  obtain ⟨⟨motiveSort, hMotiveType⟩, _, hRest1⟩ :=
    hRuleType'.forallE_inv' (.inl rfl)
  obtain ⟨⟨zeroSort, hMinorZeroType⟩, _, hRest2⟩ :=
    hRest1.forallE_inv' (.inl rfl)
  obtain ⟨⟨succSort, hMinorSuccType⟩, _, _hRest3⟩ :=
    hRest2.forallE_inv' (.inl rfl)
  let rho4 : Lift := .skip (.skip (.skip (.skip .refl)))
  have W4 : Ctx.Lift' rho4 Gamma Delta :=
    .skip (.skip (.skip (.skip .refl)))
  let rho3 : Lift := .skip (.skip (.skip .refl))
  have W3 : Ctx.Lift' rho3 (Motive :: Gamma) Delta :=
    .skip (.skip (.skip .refl))
  let rho2 : Lift := .skip (.skip .refl)
  have W2 : Ctx.Lift' rho2 (MinorZero :: Motive :: Gamma) Delta :=
    .skip (.skip .refl)
  have hMotiveTypeD : IsDefEqStrong Delta Motive Motive
      (SExpr.sort motiveSort) := by
    simpa [rho4, Motive, NatS, SExpr.lift, SExpr.lift'] using
      natStrongWeak univs W4 hMotiveType
  let ZeroTy : SExpr :=
    (SExpr.bvar 3).app (SExpr.const ``Nat.zero [])
  let SuccTy : SExpr :=
    SExpr.forallE NatS <|
      SExpr.forallE ((SExpr.bvar 4).app (SExpr.bvar 0)) <|
        (SExpr.bvar 5).app
          ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))
  have hZeroTypeD : IsDefEqStrong Delta ZeroTy ZeroTy
      (SExpr.sort zeroSort) := by
    simpa [rho3, ZeroTy, MinorZero, SExpr.lift, SExpr.lift'] using
      natStrongWeak univs W3 hMinorZeroType
  have hSuccTypeD : IsDefEqStrong Delta SuccTy SuccTy
      (SExpr.sort succSort) := by
    simpa [rho2, SuccTy, MinorSucc, NatS, SExpr.lift, SExpr.lift'] using
      natStrongWeak univs W2 hMinorSuccType
  have hP : IsDefEqStrong Delta (SExpr.bvar 3) (SExpr.bvar 3) Motive := by
    have hLookup : Lookup Delta 3 (Motive.lift.lift.lift.lift) :=
      .succ (.succ (.succ .zero))
    have hBvar := IsDefEqStrong.bvar hLookup
      (natStrongWeak univs W4 hMotiveType)
    simpa [Motive, NatS, SExpr.lift, SExpr.lift'] using hBvar
  have hZ : IsDefEqStrong Delta (SExpr.bvar 2) (SExpr.bvar 2) ZeroTy := by
    have hLookup : Lookup Delta 2 (MinorZero.lift.lift.lift) :=
      .succ (.succ .zero)
    have hBvar := IsDefEqStrong.bvar hLookup (by
      simpa [ZeroTy, MinorZero, SExpr.lift, SExpr.lift'] using hZeroTypeD)
    simpa [ZeroTy, MinorZero, SExpr.lift, SExpr.lift'] using hBvar
  have hS : IsDefEqStrong Delta (SExpr.bvar 1) (SExpr.bvar 1) SuccTy := by
    have hLookup : Lookup Delta 1 (MinorSucc.lift.lift) := .succ .zero
    have hBvar := IsDefEqStrong.bvar hLookup (by
      simpa [SuccTy, MinorSucc, NatS, SExpr.lift, SExpr.lift'] using
        hSuccTypeD)
    simpa [SuccTy, MinorSucc, NatS, SExpr.lift, SExpr.lift'] using hBvar
  have hPred : IsDefEqStrong Delta (SExpr.bvar 0) (SExpr.bvar 0) NatS := by
    have hNat := natTypeStrong univs Delta
    change IsDefEqStrong Delta (SExpr.const ``Nat [])
      (SExpr.const ``Nat [])
      (SExpr.mkInst [] InductiveFixtures.natType.type) at hNat
    rw [probeNatTypeTypeV_eq] at hNat
    exact .bvar .zero (by
      simpa [NatS, SExpr.lift, SExpr.lift', SExpr.mkInst] using hNat)
  have hHeadRaw : IsDefEqStrong Gamma
      (SExpr.mkInst [level]
        (NatGeneration.rule 1 NatGeneration.flatCtors[1]).rhs)
      (SExpr.mkInst [level]
        (NatGeneration.rule 1 NatGeneration.flatCtors[1]).rhs)
      (SExpr.mkInst [level]
        (NatGeneration.rule 1 NatGeneration.flatCtors[1]).type) := by
    simpa only [probeNatSuccRuleTypeS_eq] using hHead
  have hHeadD0 := natStrongWeak univs W4 hHeadRaw
  obtain ⟨⟨_, _⟩, ⟨rhsClosed, typeClosed⟩⟩ :=
    natFinalEnv_ordered.closed.2
      (natRule_registered probeNatFlatCtorSucc_lookup)
  rw [rhsClosed.mkInstS.lift'_eq .zero,
    typeClosed.mkInstS.lift'_eq .zero] at hHeadD0
  have hHeadD : IsDefEqStrong Delta
      (SExpr.mkInst [level]
        (NatGeneration.rule 1 NatGeneration.flatCtors[1]).rhs)
      (SExpr.mkInst [level]
        (NatGeneration.rule 1 NatGeneration.flatCtors[1]).rhs)
      (SExpr.forallE Motive
        (SExpr.forallE MinorZero
          (SExpr.forallE MinorSucc (SExpr.forallE NatS Result)))) := by
    simpa [probeNatSuccRuleTypeS_eq, probeNatSuccRuleType, Motive,
      MinorZero, MinorSucc, Result, NatS] using hHeadD0
  let RG1 : List SExpr := Motive :: Delta
  let RG2 : List SExpr := MinorZero :: RG1
  let RG3 : List SExpr := MinorSucc :: RG2
  have hZeroTypeG : IsDefEqStrong RG1 MinorZero MinorZero
      (SExpr.sort zeroSort) := by
    have h := natStrongWeak univs W4.cons hMinorZeroType
    simpa [RG1, rho4, Motive, MinorZero, NatS,
      SExpr.lift, SExpr.lift'] using h
  have hSuccTypeG : IsDefEqStrong RG2 MinorSucc MinorSucc
      (SExpr.sort succSort) := by
    have h := natStrongWeak univs W4.cons.cons hMinorSuccType
    simpa [RG2, RG1, rho4, Motive, MinorZero, MinorSucc, NatS,
      SExpr.lift, SExpr.lift'] using h
  have hMotiveGeneric : IsDefEqStrong (NatS :: RG3)
      (SExpr.bvar 3) (SExpr.bvar 3) Motive := by
    let rho4g : Lift := .skip (.skip (.skip (.skip .refl)))
    have W4g : Ctx.Lift' rho4g Delta (NatS :: RG3) :=
      .skip (.skip (.skip (.skip .refl)))
    have hLift := natStrongWeak univs W4g hMotiveTypeD
    have hLookup : Lookup (NatS :: RG3) 3
        (Motive.lift.lift.lift.lift) := .succ (.succ (.succ .zero))
    have hBvar := IsDefEqStrong.bvar hLookup hLift
    simpa [RG3, RG2, RG1, Motive, NatS,
      SExpr.lift, SExpr.lift'] using hBvar
  have hGenericPred : IsDefEqStrong (NatS :: RG3)
      (SExpr.bvar 0) (SExpr.bvar 0) NatS := by
    have hNat := natTypeStrong univs (NatS :: RG3)
    change IsDefEqStrong (NatS :: RG3) (SExpr.const ``Nat [])
      (SExpr.const ``Nat [])
      (SExpr.mkInst [] InductiveFixtures.natType.type) at hNat
    rw [probeNatTypeTypeV_eq] at hNat
    exact .bvar .zero (by
      simpa [NatS, SExpr.lift, SExpr.lift', SExpr.mkInst] using hNat)
  have hGenericSucc0 := IsDefEqStrong.appDF
    (natTypeStrong univs (NatS :: RG3))
    (natTypeStrong univs (NatS :: NatS :: RG3))
    (natSuccStrong univs (NatS :: RG3)) hGenericPred
    (natTypeStrong univs (NatS :: RG3))
  have hGenericSucc : IsDefEqStrong (NatS :: RG3)
      ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0))
      ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0)) NatS := by
    simpa [NatS, SExpr.inst, SExpr.subst, Subst.one, Subst.cons,
      Subst.lift, Subst.id] using hGenericSucc0
  have hGenericResult : IsDefEqStrong (NatS :: RG3)
      ((SExpr.bvar 3).app
        ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0)))
      ((SExpr.bvar 3).app
        ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0)))
      (SExpr.sort level) := by
    simpa [SExpr.inst, SExpr.subst, Subst.one, Subst.cons,
      Subst.lift, Subst.id] using
      IsDefEqStrong.appDF (natTypeStrong univs (NatS :: RG3)) .sort
        hMotiveGeneric hGenericSucc .sort
  let predTailSort : SLevel :=
    (SLevel.instV [] VLevel.zero.succ).imax level
  have hPredTailG : IsDefEqStrong RG3
      (SExpr.forallE NatS
        ((SExpr.bvar 3).app
          ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0))))
      (SExpr.forallE NatS
        ((SExpr.bvar 3).app
          ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0))))
      (SExpr.sort predTailSort) := by
    simpa [predTailSort] using IsDefEqStrong.forallEDF
      (natTypeStrong univs RG3) hGenericResult hGenericResult
  have hAfterSuccG := IsDefEqStrong.forallEDF
    hSuccTypeG hPredTailG hPredTailG
  have hAfterZeroG := IsDefEqStrong.forallEDF
    hZeroTypeG hAfterSuccG hAfterSuccG
  let PredResult : SExpr :=
    (SExpr.bvar 4).app
      ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0))
  let PredTail : SExpr := SExpr.forallE NatS PredResult
  have hMotivePred : IsDefEqStrong (NatS :: Delta)
      (SExpr.bvar 4) (SExpr.bvar 4) Motive := by
    let rho5 : Lift := .skip (.skip (.skip (.skip (.skip .refl))))
    have W5 : Ctx.Lift' rho5 Gamma (NatS :: Delta) :=
      .skip (.skip (.skip (.skip (.skip .refl))))
    have hLift := natStrongWeak univs W5 hMotiveType
    have hLookup : Lookup (NatS :: Delta) 4
        (Motive.lift.lift.lift.lift.lift) :=
      .succ (.succ (.succ (.succ .zero)))
    have hBvar := IsDefEqStrong.bvar hLookup hLift
    simpa [Motive, NatS, SExpr.lift, SExpr.lift'] using hBvar
  have hFreshPred : IsDefEqStrong (NatS :: Delta)
      (SExpr.bvar 0) (SExpr.bvar 0) NatS := by
    have hNat := natTypeStrong univs (NatS :: Delta)
    change IsDefEqStrong (NatS :: Delta) (SExpr.const ``Nat [])
      (SExpr.const ``Nat [])
      (SExpr.mkInst [] InductiveFixtures.natType.type) at hNat
    rw [probeNatTypeTypeV_eq] at hNat
    exact .bvar .zero (by
      simpa [NatS, SExpr.lift, SExpr.lift', SExpr.mkInst] using hNat)
  have hFreshSucc0 := IsDefEqStrong.appDF
    (natTypeStrong univs (NatS :: Delta))
    (natTypeStrong univs (NatS :: NatS :: Delta))
    (natSuccStrong univs (NatS :: Delta)) hFreshPred
    (natTypeStrong univs (NatS :: Delta))
  have hFreshSucc : IsDefEqStrong (NatS :: Delta)
      ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0))
      ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0)) NatS := by
    simpa [NatS, SExpr.inst, SExpr.subst, Subst.one, Subst.cons,
      Subst.lift, Subst.id] using hFreshSucc0
  have hPredResult : IsDefEqStrong (NatS :: Delta)
      PredResult PredResult (SExpr.sort level) := by
    simpa [PredResult, SExpr.inst, SExpr.subst, Subst.one, Subst.cons,
      Subst.lift, Subst.id] using
      IsDefEqStrong.appDF (natTypeStrong univs (NatS :: Delta)) .sort
        hMotivePred hFreshSucc .sort
  have hPredTail : IsDefEqStrong Delta PredTail PredTail
      (SExpr.sort predTailSort) := by
    simpa [PredTail, predTailSort] using IsDefEqStrong.forallEDF
      (natTypeStrong univs Delta) hPredResult hPredResult
  have hPredTailS : IsDefEqStrong (SuccTy :: Delta)
      PredTail.lift PredTail.lift (SExpr.sort predTailSort) := by
    simpa [PredTail, SuccTy, SExpr.lift, ← SExpr.lift'_comp] using
      natStrongWeak univs (Ctx.Lift'.one (A := SuccTy)) hPredTail
  have hAfterSucc : IsDefEqStrong Delta
      (SExpr.forallE SuccTy PredTail.lift)
      (SExpr.forallE SuccTy PredTail.lift)
      (SExpr.sort (succSort.imax predTailSort)) :=
    .forallEDF hSuccTypeD hPredTailS hPredTailS
  have hSuccTypeZ : IsDefEqStrong (ZeroTy :: Delta)
      SuccTy.lift SuccTy.lift (SExpr.sort succSort) := by
    simpa [SuccTy, ZeroTy, SExpr.lift, ← SExpr.lift'_comp] using
      natStrongWeak univs (Ctx.Lift'.one (A := ZeroTy)) hSuccTypeD
  let rhoZS : Lift := .skip (.skip .refl)
  have WZS : Ctx.Lift' rhoZS Delta
      (SuccTy.lift :: ZeroTy :: Delta) := .skip (.skip .refl)
  have hPredTailZS : IsDefEqStrong (SuccTy.lift :: ZeroTy :: Delta)
      PredTail.lift.lift PredTail.lift.lift
      (SExpr.sort predTailSort) := by
    simpa [rhoZS, SExpr.lift, ← SExpr.lift'_comp] using
      natStrongWeak univs WZS hPredTail
  have hAfterSuccZ : IsDefEqStrong (ZeroTy :: Delta)
      (SExpr.forallE SuccTy.lift PredTail.lift.lift)
      (SExpr.forallE SuccTy.lift PredTail.lift.lift)
      (SExpr.sort (succSort.imax predTailSort)) :=
    .forallEDF hSuccTypeZ hPredTailZS hPredTailZS
  have hAfterZero : IsDefEqStrong Delta
      (SExpr.forallE ZeroTy
        (SExpr.forallE SuccTy.lift PredTail.lift.lift))
      (SExpr.forallE ZeroTy
        (SExpr.forallE SuccTy.lift PredTail.lift.lift))
      (SExpr.sort (zeroSort.imax (succSort.imax predTailSort))) :=
    .forallEDF hZeroTypeD hAfterSuccZ hAfterSuccZ
  have hAppP0 := IsDefEqStrong.appDF
    hMotiveTypeD hAfterZeroG hHeadD hP hAfterZero
  have hAppP : IsDefEqStrong Delta
      ((SExpr.mkInst [level]
        (NatGeneration.rule 1 NatGeneration.flatCtors[1]).rhs).app
          (SExpr.bvar 3))
      ((SExpr.mkInst [level]
        (NatGeneration.rule 1 NatGeneration.flatCtors[1]).rhs).app
          (SExpr.bvar 3))
      (SExpr.forallE ZeroTy
        (SExpr.forallE SuccTy.lift PredTail.lift.lift)) := by
    simpa [RG3, RG2, RG1, ZeroTy, SuccTy, PredTail, PredResult,
      Motive, MinorZero, MinorSucc, Result, NatS,
      SExpr.inst, SExpr.subst, Subst.one, Subst.cons, Subst.lift,
      Subst.id, probeCancelUnderOne, probeCancelUnderTwo] using hAppP0
  have hAppZ0 := IsDefEqStrong.appDF
    hZeroTypeD hAfterSuccZ hAppP hZ hAfterSucc
  have hAppZ : IsDefEqStrong Delta
      (((SExpr.mkInst [level]
        (NatGeneration.rule 1 NatGeneration.flatCtors[1]).rhs).app
          (SExpr.bvar 3)).app (SExpr.bvar 2))
      (((SExpr.mkInst [level]
        (NatGeneration.rule 1 NatGeneration.flatCtors[1]).rhs).app
          (SExpr.bvar 3)).app (SExpr.bvar 2))
      (SExpr.forallE SuccTy PredTail.lift) := by
    simpa [ZeroTy, SuccTy, PredTail, PredResult, NatS,
      SExpr.lift, SExpr.lift', SExpr.inst, SExpr.subst,
      Subst.one, Subst.cons, Subst.lift, Subst.id,
      probeCancelUnderOne, probeCancelUnderTwo] using hAppZ0
  have hAppS0 := IsDefEqStrong.appDF
    hSuccTypeD hPredTailS hAppZ hS hPredTail
  have hAppS : IsDefEqStrong Delta
      ((((SExpr.mkInst [level]
        (NatGeneration.rule 1 NatGeneration.flatCtors[1]).rhs).app
          (SExpr.bvar 3)).app (SExpr.bvar 2)).app (SExpr.bvar 1))
      ((((SExpr.mkInst [level]
        (NatGeneration.rule 1 NatGeneration.flatCtors[1]).rhs).app
          (SExpr.bvar 3)).app (SExpr.bvar 2)).app (SExpr.bvar 1))
      PredTail := by
    simpa [SuccTy, PredTail, PredResult, NatS,
      SExpr.lift, SExpr.lift', SExpr.inst, SExpr.subst,
      Subst.one, Subst.cons, Subst.lift, Subst.id,
      probeCancelUnderOne, probeCancelUnderTwo] using hAppS0
  have hFinalSucc0 := IsDefEqStrong.appDF
    (natTypeStrong univs Delta)
    (natTypeStrong univs (NatS :: Delta))
    (natSuccStrong univs Delta) hPred (natTypeStrong univs Delta)
  have hFinalSucc : IsDefEqStrong Delta
      ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0))
      ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0)) NatS := by
    simpa [NatS, SExpr.inst, SExpr.subst, Subst.one, Subst.cons,
      Subst.lift, Subst.id] using hFinalSucc0
  have hFinalResult : IsDefEqStrong Delta Result Result
      (SExpr.sort level) := by
    simpa [Result, SExpr.inst, SExpr.subst, Subst.one, Subst.cons,
      Subst.lift, Subst.id] using
      IsDefEqStrong.appDF (natTypeStrong univs Delta) .sort hP
        hFinalSucc .sort
  have hAppPred0 := IsDefEqStrong.appDF
    (natTypeStrong univs Delta) hPredResult hAppS hPred hFinalResult
  simpa [Delta, AppliedRhs, Result, PredTail, PredResult, NatS,
    SExpr.inst, SExpr.subst, Subst.one, Subst.cons,
    Subst.lift, Subst.id] using hAppPred0

/-- Weak local soundness for the successor action, proved in the closed
generated telescope and then right-weakened into the arbitrary ambient tail. -/
theorem natSuccRuleActionSound (univs : Nat)
    {Gamma : List (@SExpr (natParams univs))}
    (level : @SLevel (natParams univs)) :
    letI : Params := natParams univs
    let NatS : SExpr := SExpr.const ``Nat []
    let Motive : SExpr := SExpr.forallE NatS (SExpr.sort level)
    let MinorZero : SExpr :=
      (SExpr.bvar 0).app (SExpr.const ``Nat.zero [])
    let MinorSucc : SExpr :=
      SExpr.forallE NatS <|
        SExpr.forallE ((SExpr.bvar 2).app (SExpr.bvar 0)) <|
          (SExpr.bvar 3).app
            ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))
    let Delta : List SExpr := NatS :: MinorSucc :: MinorZero :: Motive :: Gamma
    let Redex : SExpr :=
      ((((SExpr.const ``Nat.rec [level]).app (SExpr.bvar 3)).app
        (SExpr.bvar 2)).app (SExpr.bvar 1)).app
          ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0))
    let AppliedRhs : SExpr :=
      [SExpr.bvar 3, SExpr.bvar 2, SExpr.bvar 1,
        SExpr.bvar 0].foldl (fun f a => f.app a)
        (SExpr.mkInst [level]
          (NatGeneration.rule 1 NatGeneration.flatCtors[1]).rhs)
    let Result : SExpr :=
      (SExpr.bvar 3).app
        ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0))
    IsDefEq Delta Redex AppliedRhs Result := by
  letI : Params := natParams univs
  let NatS : SExpr := SExpr.const ``Nat []
  let Motive : SExpr := SExpr.forallE NatS (SExpr.sort level)
  let MinorZero : SExpr :=
    (SExpr.bvar 0).app (SExpr.const ``Nat.zero [])
  let MinorSucc : SExpr :=
    SExpr.forallE NatS <|
      SExpr.forallE ((SExpr.bvar 2).app (SExpr.bvar 0)) <|
        (SExpr.bvar 3).app
          ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))
  let Delta0 : List SExpr := [NatS, MinorSucc, MinorZero, Motive]
  let Delta : List SExpr := Delta0 ++ Gamma
  let Redex : SExpr :=
    ((((SExpr.const ``Nat.rec [level]).app (SExpr.bvar 3)).app
      (SExpr.bvar 2)).app (SExpr.bvar 1)).app
        ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0))
  let AppliedRhs : SExpr :=
    [SExpr.bvar 3, SExpr.bvar 2, SExpr.bvar 1,
      SExpr.bvar 0].foldl (fun f a => f.app a)
      (SExpr.mkInst [level]
        (NatGeneration.rule 1 NatGeneration.flatCtors[1]).rhs)
  let Result : SExpr :=
    (SExpr.bvar 3).app
      ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0))
  let vls : List VLevel := [level.reify]
  let argsV : List VExpr :=
    [VExpr.bvar 3, VExpr.bvar 2, VExpr.bvar 1, VExpr.bvar 0]
  let AsV : List VExpr :=
    probeNatSuccRuleBindersV.map (VExpr.instL vls)
  let ResultV : VExpr := probeNatSuccRuleResultV.instL vls
  have hvls : ∀ l ∈ vls, l.WF univs := by
    intro l hl
    simp only [vls, List.mem_singleton] at hl
    subst l
    exact SLevel.reify_wf level
  have hreg := natRule_registered probeNatFlatCtorSucc_lookup
  have hlhs0 := (natFinalEnv_ordered.defEqWF hreg).1.instL hvls
  rw [probeNatSuccRuleLhsV_eq] at hlhs0
  unfold probeNatSuccRuleLhsV at hlhs0
  rw [VExpr.instL_lamN] at hlhs0
  obtain ⟨hTel, bodyType, hbody⟩ :=
    VEnv.HasType.lamN_wf natFinalEnv_ordered (by trivial) hlhs0
  have hTel' : natFinalEnv.OnTel univs [] AsV := by
    simpa [AsV] using hTel
  have hbody' : natFinalEnv.HasType univs AsV.reverse
      (probeNatSuccRuleLhsBodyV.instL vls) bodyType := by
    simpa [AsV] using hbody
  have hDelta0 : OnCtx AsV.reverse (natFinalEnv.IsType univs) :=
    hTel'.toOnCtx (by trivial)
  have hprobeType : probeNatSuccRuleTypeV =
      VExpr.forallN probeNatSuccRuleBindersV probeNatSuccRuleResultV := rfl
  have hargs : natFinalEnv.SpineWF univs AsV.reverse
      (VExpr.forallN AsV ResultV) argsV ResultV := by
    have hcore := natSelfSpine (env := natFinalEnv) (univs := univs)
      AsV ResultV []
    have hclosed : (VExpr.forallN AsV ResultV).Closed := by
      have ⟨⟨_, _⟩, _, htypeClosed⟩ := natFinalEnv_ordered.closed.2 hreg
      rw [probeNatSuccRuleTypeV_eq] at htypeClosed
      rw [hprobeType] at htypeClosed
      simpa [AsV, ResultV, VExpr.instL_forallN] using
        htypeClosed.instL (ls := vls)
    rw [hclosed.liftN_eq (Nat.zero_le _)] at hcore
    simpa [AsV, argsV, probeNatSuccRuleBindersV,
      probeNatRuleBindersV, VExpr.bvarRevRange] using hcore
  have hTelLocal : natFinalEnv.OnTel univs AsV.reverse AsV := by
    simpa using natOnTelWeakR natFinalEnv_ordered (Base := [])
      (As := AsV) (by trivial) hTel' AsV.reverse
  have hbodyLocal : natFinalEnv.HasType univs
      (AsV.reverse ++ AsV.reverse)
      (probeNatSuccRuleLhsBodyV.instL vls) bodyType :=
    VEnv.IsDefEq.weakR natFinalEnv_ordered
      (VEnv.CtxWF.closed natFinalEnv_ordered hDelta0) hbody' AsV.reverse
  have hspineBody := VEnv.SpineWF.retarget hargs
    (by simp [AsV, argsV, probeNatSuccRuleBindersV,
      probeNatRuleBindersV]) bodyType
  have hcollapseV := VEnv.IsDefEq.appN_lamN natFinalEnv_ordered
    hTelLocal hbodyLocal hspineBody
      (by simp [AsV, argsV, probeNatSuccRuleBindersV,
        probeNatRuleBindersV])
  have htypeShape :
      (NatGeneration.rule 1 NatGeneration.flatCtors[1]).type.instL vls =
        VExpr.forallN AsV ResultV := by
    rw [probeNatSuccRuleTypeV_eq, hprobeType, VExpr.instL_forallN]
  have hlhsLocal : natFinalEnv.HasType univs AsV.reverse
      ((probeNatSuccRuleLhsV.instL vls).appN argsV) ResultV := by
    have hlhsWeak : natFinalEnv.HasType univs AsV.reverse
        ((NatGeneration.rule 1 NatGeneration.flatCtors[1]).lhs.instL vls)
        ((NatGeneration.rule 1 NatGeneration.flatCtors[1]).type.instL vls) :=
      ((natFinalEnv_ordered.defEqWF hreg).1.instL hvls).weak0
        natFinalEnv_ordered
    have hdeclared : natFinalEnv.SpineWF univs AsV.reverse
        ((NatGeneration.rule 1 NatGeneration.flatCtors[1]).type.instL vls)
        argsV ResultV := by
      rw [htypeShape]
      exact hargs
    rw [← probeNatSuccRuleLhsV_eq]
    exact hdeclared.hasType_appN hlhsWeak
  have hcollapseV' : natFinalEnv.IsDefEq univs AsV.reverse
      ((probeNatSuccRuleLhsV.instL vls).appN argsV)
      ((probeNatSuccRuleLhsBodyV.instL vls).instRev argsV)
      ResultV := by
    have ⟨_, htype⟩ := hcollapseV.symm.uniq
      InductiveReplayFixtures.nat_env_wf hDelta0 hlhsLocal
    exact htype.defeqDF hcollapseV
  have hrawV : natFinalEnv.IsDefEq univs AsV.reverse
      ((NatGeneration.rule 1 NatGeneration.flatCtors[1]).lhs.instL vls)
      ((NatGeneration.rule 1 NatGeneration.flatCtors[1]).rhs.instL vls)
      ((NatGeneration.rule 1 NatGeneration.flatCtors[1]).type.instL vls) :=
    .extra hreg hvls rfl
  have hdeclared : natFinalEnv.SpineWF univs AsV.reverse
      ((NatGeneration.rule 1 NatGeneration.flatCtors[1]).type.instL vls)
      argsV ResultV := by
    rw [htypeShape]
    exact hargs
  have happliedV := hrawV.appN_congr hdeclared
  have hsound0V := hcollapseV'.symm.trans happliedV
  have hsoundV := hsound0V.weakR natFinalEnv_ordered
    (VEnv.CtxWF.closed natFinalEnv_ordered hDelta0)
    (Gamma.map SExpr.reify)
  have hlevels : OnCtx
      (AsV.reverse ++ Gamma.map SExpr.reify)
      (fun _ A => A.LevelWF univs) := by
    have hAsLevels : ∀ A ∈ AsV, A.LevelWF univs := by
      intro A hA
      simp only [AsV, List.mem_map] at hA
      obtain ⟨A0, _, rfl⟩ := hA
      exact VExpr.LevelWF.instL hvls
    have hGammaLevels : OnCtx (Gamma.map SExpr.reify)
        (fun _ A => A.LevelWF univs) := natReifyLevelWFContext Gamma
    have go : ∀ L : List VExpr,
        (∀ A ∈ L, A.LevelWF univs) →
        OnCtx (L ++ Gamma.map SExpr.reify)
          (fun _ A => A.LevelWF univs) := by
      intro L hall
      induction L with
      | nil => simpa using hGammaLevels
      | cons A rest ih =>
        exact ⟨ih (fun B hB => hall B (.tail _ hB)),
          hall A (.head _)⟩
    exact go AsV.reverse (by
      intro A hA
      exact hAsLevels A (by simpa using hA))
  have hsoundS := SExpr.IsDefEq.mkS (natStructureEtaSound univs)
    hsoundV hlevels
  have hmkInst (e : VExpr) :
      SExpr.mk (e.instL vls) = SExpr.mkInst [level] e := by
    unfold vls
    exact @SExpr.mk_instL_map_reify (natParams univs) e [level]
  have hctx :
      (AsV.reverse ++ Gamma.map SExpr.reify).map SExpr.mk = Delta := by
    rw [List.map_append]
    have hGamma : (Gamma.map SExpr.reify).map SExpr.mk = Gamma := by
      rw [List.map_map]
      exact List.map_id''' Gamma fun term _ => SExpr.mk_reify term
    have hAs : AsV.reverse.map SExpr.mk = Delta0 := by
      rw [List.map_reverse]
      have hforward : AsV.map SExpr.mk =
          [Motive, MinorZero, MinorSucc, NatS] := by
        simp [AsV, Motive, MinorZero, MinorSucc, NatS,
          probeNatSuccRuleBindersV, probeNatRuleBindersV,
          hmkInst, SExpr.mkInst, probeInstVParamZero]
      rw [hforward]
      rfl
    rw [hAs, hGamma]
  rw [hctx] at hsoundS
  have hbodyCollapseV :
      (probeNatSuccRuleLhsBodyV.instL vls).instRev argsV =
      ((((VExpr.const ``Nat.rec [level.reify]).app (VExpr.bvar 3)).app
        (VExpr.bvar 2)).app (VExpr.bvar 1)).app
          ((VExpr.const ``Nat.succ []).app (VExpr.bvar 0)) := by
    simp [probeNatSuccRuleLhsBodyV, vls, argsV, VExpr.instRev,
      VExpr.instL, VExpr.inst, VExpr.instVar, VExpr.liftN, liftVar,
      VExpr.liftN_succ, VExpr.liftN_zero, probeReifyInstVParamZero,
      probeVCancelThreeLifts, probeVCancelTwoLifts, VExpr.inst_lift]
  rw [hbodyCollapseV] at hsoundS
  have hresultMk : SExpr.mk ResultV = Result := by
    simp [ResultV, Result, probeNatSuccRuleResultV, vls,
      VExpr.instL, SExpr.mk]
  rw [hresultMk] at hsoundS
  simpa [Delta, Delta0, Redex, AppliedRhs, vls, argsV, hmkInst,
    probeNatSuccRuleLhsV, probeNatSuccRuleBindersV,
    probeNatRuleBindersV, VExpr.lamN, VExpr.appN,
    SExpr.mk, SExpr.mkInst] using hsoundS

/-- The generated successor match packages the four-capture local action. -/
theorem natSuccRuleLocalStrong (univs : Nat)
    {Gamma : List (@SExpr (natParams univs))}
    (level : @SLevel (natParams univs))
    (hRuleType : ∃ u, @IsDefEqStrong (natParams univs) Gamma
      (probeNatSuccRuleType univs level)
      (probeNatSuccRuleType univs level)
      (@SExpr.sort (natParams univs) u))
    (hRhs : @IsDefEqStrong (natParams univs) Gamma
      (@SExpr.mkInst (natParams univs) [level]
        (NatGeneration.rule 1 NatGeneration.flatCtors[1]).rhs)
      (@SExpr.mkInst (natParams univs) [level]
        (NatGeneration.rule 1 NatGeneration.flatCtors[1]).rhs)
      (probeNatSuccRuleType univs level)) :
    letI : Params := natParams univs
    let NatS : SExpr := SExpr.const ``Nat []
    let Motive : SExpr := SExpr.forallE NatS (SExpr.sort level)
    let MinorZero : SExpr :=
      (SExpr.bvar 0).app (SExpr.const ``Nat.zero [])
    let MinorSucc : SExpr :=
      SExpr.forallE NatS <|
        SExpr.forallE ((SExpr.bvar 2).app (SExpr.bvar 0)) <|
          (SExpr.bvar 3).app
            ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))
    let Delta : List SExpr := NatS :: MinorSucc :: MinorZero :: Motive :: Gamma
    let Redex : SExpr :=
      ((((SExpr.const ``Nat.rec [level]).app (SExpr.bvar 3)).app
        (SExpr.bvar 2)).app (SExpr.bvar 1)).app
          ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0))
    let AppliedRhs : SExpr :=
      [SExpr.bvar 3, SExpr.bvar 2, SExpr.bvar 1,
        SExpr.bvar 0].foldl (fun f a => f.app a)
        (SExpr.mkInst [level]
          (NatGeneration.rule 1 NatGeneration.flatCtors[1]).rhs)
    let Result : SExpr :=
      (SExpr.bvar 3).app
        ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0))
    IsDefEqStrong Delta Redex AppliedRhs Result := by
  letI : Params := natParams univs
  let NatS : SExpr := SExpr.const ``Nat []
  let Motive : SExpr := SExpr.forallE NatS (SExpr.sort level)
  let MinorZero : SExpr :=
    (SExpr.bvar 0).app (SExpr.const ``Nat.zero [])
  let MinorSucc : SExpr :=
    SExpr.forallE NatS <|
      SExpr.forallE ((SExpr.bvar 2).app (SExpr.bvar 0)) <|
        (SExpr.bvar 3).app
          ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))
  let Delta : List SExpr := NatS :: MinorSucc :: MinorZero :: Motive :: Gamma
  let Redex : SExpr :=
    ((((SExpr.const ``Nat.rec [level]).app (SExpr.bvar 3)).app
      (SExpr.bvar 2)).app (SExpr.bvar 1)).app
        ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0))
  let AppliedRhs : SExpr :=
    [SExpr.bvar 3, SExpr.bvar 2, SExpr.bvar 1,
      SExpr.bvar 0].foldl (fun f a => f.app a)
      (SExpr.mkInst [level]
        (NatGeneration.rule 1 NatGeneration.flatCtors[1]).rhs)
  let Result : SExpr :=
    (SExpr.bvar 3).app
      ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0))
  let rgen :=
    (NatGeneration.ruleRHS natRuleClosure probeNatFlatCtorSucc_lookup,
      NatGeneration.ruleCheck natRuleClosure
        (List.mem_of_getElem? probeNatFlatCtorSucc_lookup))
  have hpat : NatPat
      (RecursorIotaPattern ``Nat.rec 3 ``Nat.succ 1) rgen :=
    .mk probeNatFlatCtorSucc_lookup
  let rule : Pattern.IotaRule rgen := {
    pat := hpat
    df := NatGeneration.rule 1 NatGeneration.flatCtors[1]
    registered := natRule_registered probeNatFlatCtorSucc_lookup
    rhsClosed := natRuleClosure.rhs_closed probeNatFlatCtorSucc_lookup
    capturePaths := natCapturePaths NatGeneration.flatCtors[1]
    rhsTower := natRuleRHS_tower probeNatFlatCtorSucc_lookup }
  obtain ⟨mcap, hmatch⟩ :=
    RecursorIotaPattern.matchesS_spines
      (rargs := [SExpr.bvar 1, SExpr.bvar 2, SExpr.bvar 3])
      (cargs := [SExpr.bvar 0]) (rls := [level]) (cls := [])
      (by rfl) (by rfl)
  have hmatch' : (RecursorIotaPattern ``Nat.rec 3 ``Nat.succ 1).MatchesS
      Redex [level] mcap := by
    simpa [Redex] using hmatch
  obtain ⟨_, _, hcaps⟩ := natSuccCaptureValues univs hmatch
  have hrhsEq : AppliedRhs = rgen.1.applyS [level] mcap := by
    calc
      AppliedRhs =
          (rule.capturePaths.map mcap).foldl
            (fun (f a : SExpr) => f.app a)
            (SExpr.mkInst [level] rule.df.rhs) := by
        simp [AppliedRhs, rule, hcaps]
      _ = rgen.1.applyS [level] mcap := rule.rhsApply [level] mcap
  have hsound : IsDefEq Delta Redex (rgen.1.applyS [level] mcap)
      Result := by
    have hsoundCanonical : IsDefEq Delta Redex AppliedRhs Result := by
      simpa [Delta, Redex, AppliedRhs, Result] using
        (natSuccRuleActionSound univs (Gamma := Gamma) level)
    exact hrhsEq ▸ hsoundCanonical
  let action : Pattern.Action Delta rgen Redex [level] mcap Result := {
    pat := hpat
    matched := hmatch'
    dfs := []
    defeqs := by rfl
    checked := by simp
    sound := hsound }
  have hLeft := natSuccRuleBodyStrong univs (Gamma := Gamma) level hRuleType
  have hRightCanonical :=
    natSuccRuleAppliedStrong univs (Gamma := Gamma) level hRuleType hRhs
  have hRight : IsDefEqStrong Delta
      (rgen.1.applyS [level] mcap) (rgen.1.applyS [level] mcap)
      Result := by
    have hRightCanonical' : IsDefEqStrong Delta AppliedRhs AppliedRhs
        Result := by
      simpa [Delta, AppliedRhs, Result] using hRightCanonical
    exact hrhsEq ▸ hRightCanonical'
  have hLocal := IsDefEqStrong.extra action (by
    simpa [Delta, Redex, Result] using hLeft) hRight
  have hLocalCanonical : IsDefEqStrong Delta Redex AppliedRhs Result :=
    hrhsEq.symm ▸ hLocal
  simpa [Delta, Redex, AppliedRhs, Result] using hLocalCanonical

/-- The three proper prefixes of the four-argument successor RHS tower. -/
theorem natSuccRulePrefixesStrong (univs : Nat)
    {Gamma : List (@SExpr (natParams univs))}
    (level : @SLevel (natParams univs))
    (hRuleType : ∃ u, @IsDefEqStrong (natParams univs) Gamma
      (probeNatSuccRuleType univs level)
      (probeNatSuccRuleType univs level)
      (@SExpr.sort (natParams univs) u))
    (hRhs : @IsDefEqStrong (natParams univs) Gamma
      (@SExpr.mkInst (natParams univs) [level]
        (NatGeneration.rule 1 NatGeneration.flatCtors[1]).rhs)
      (@SExpr.mkInst (natParams univs) [level]
        (NatGeneration.rule 1 NatGeneration.flatCtors[1]).rhs)
      (probeNatSuccRuleType univs level)) :
    letI : Params := natParams univs
    let NatS : SExpr := SExpr.const ``Nat []
    let Motive : SExpr := SExpr.forallE NatS (SExpr.sort level)
    let MinorZero : SExpr :=
      (SExpr.bvar 0).app (SExpr.const ``Nat.zero [])
    let MinorSucc : SExpr :=
      SExpr.forallE NatS <|
        SExpr.forallE ((SExpr.bvar 2).app (SExpr.bvar 0)) <|
          (SExpr.bvar 3).app
            ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))
    let Result : SExpr :=
      (SExpr.bvar 3).app
        ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0))
    let Head : SExpr := SExpr.mkInst [level]
      (NatGeneration.rule 1 NatGeneration.flatCtors[1]).rhs
    let G1 : List SExpr := Motive :: Gamma
    let G2 : List SExpr := MinorZero :: G1
    let G3 : List SExpr := MinorSucc :: G2
    IsDefEqStrong G1 (Head.app (SExpr.bvar 0))
        (Head.app (SExpr.bvar 0))
        (SExpr.forallE MinorZero
          (SExpr.forallE MinorSucc (SExpr.forallE NatS Result))) ∧
      IsDefEqStrong G2
        ((Head.app (SExpr.bvar 1)).app (SExpr.bvar 0))
        ((Head.app (SExpr.bvar 1)).app (SExpr.bvar 0))
        (SExpr.forallE MinorSucc (SExpr.forallE NatS Result)) ∧
      IsDefEqStrong G3
        (((Head.app (SExpr.bvar 2)).app (SExpr.bvar 1)).app
          (SExpr.bvar 0))
        (((Head.app (SExpr.bvar 2)).app (SExpr.bvar 1)).app
          (SExpr.bvar 0))
        (SExpr.forallE NatS Result) := by
  letI : Params := natParams univs
  let NatS : SExpr := SExpr.const ``Nat []
  let Motive : SExpr := SExpr.forallE NatS (SExpr.sort level)
  let MinorZero : SExpr :=
    (SExpr.bvar 0).app (SExpr.const ``Nat.zero [])
  let MinorSucc : SExpr :=
    SExpr.forallE NatS <|
      SExpr.forallE ((SExpr.bvar 2).app (SExpr.bvar 0)) <|
        (SExpr.bvar 3).app
          ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))
  let Result : SExpr :=
    (SExpr.bvar 3).app
      ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0))
  let Head : SExpr := SExpr.mkInst [level]
    (NatGeneration.rule 1 NatGeneration.flatCtors[1]).rhs
  let G1 : List SExpr := Motive :: Gamma
  let G2 : List SExpr := MinorZero :: G1
  let G3 : List SExpr := MinorSucc :: G2
  obtain ⟨ruleSort, hRuleType⟩ := hRuleType
  have hRuleType' : IsDefEqStrong Gamma
      (SExpr.forallE Motive
        (SExpr.forallE MinorZero
          (SExpr.forallE MinorSucc (SExpr.forallE NatS Result))))
      (SExpr.forallE Motive
        (SExpr.forallE MinorZero
          (SExpr.forallE MinorSucc (SExpr.forallE NatS Result))))
      (SExpr.sort ruleSort) := by
    simpa [probeNatSuccRuleType, Motive, MinorZero, MinorSucc, Result,
      NatS] using hRuleType
  obtain ⟨⟨motiveSort, hMotiveType⟩, restSort1, hRest1⟩ :=
    hRuleType'.forallE_inv' (.inl rfl)
  obtain ⟨⟨zeroSort, hMinorZeroType⟩, restSort2, hRest2⟩ :=
    hRest1.forallE_inv' (.inl rfl)
  obtain ⟨⟨succSort, hMinorSuccType⟩, restSort3, hRest3⟩ :=
    hRest2.forallE_inv' (.inl rfl)
  let rhoP : Lift := .skip .refl
  have WP : Ctx.Lift' rhoP Gamma G1 := .skip .refl
  have hRhsRaw : IsDefEqStrong Gamma Head Head
      (SExpr.mkInst [level]
        (NatGeneration.rule 1 NatGeneration.flatCtors[1]).type) := by
    simpa only [Head, probeNatSuccRuleTypeS_eq] using hRhs
  have hHeadG10 := natStrongWeak univs WP hRhsRaw
  obtain ⟨⟨_, _⟩, ⟨rhsClosed, typeClosed⟩⟩ :=
    natFinalEnv_ordered.closed.2
      (natRule_registered probeNatFlatCtorSucc_lookup)
  rw [rhsClosed.mkInstS.lift'_eq .zero,
    typeClosed.mkInstS.lift'_eq .zero] at hHeadG10
  have hHeadG1 : IsDefEqStrong G1 Head Head
      (SExpr.forallE Motive
        (SExpr.forallE MinorZero
          (SExpr.forallE MinorSucc (SExpr.forallE NatS Result)))) := by
    simpa [Head, probeNatSuccRuleTypeS_eq, probeNatSuccRuleType,
      Motive, MinorZero, MinorSucc, Result, NatS] using hHeadG10
  have hMotiveTypeG1 : IsDefEqStrong G1 Motive Motive
      (SExpr.sort motiveSort) := by
    simpa [G1, rhoP, Motive, NatS, SExpr.lift, SExpr.lift'] using
      natStrongWeak univs WP hMotiveType
  have hP : IsDefEqStrong G1 (SExpr.bvar 0) (SExpr.bvar 0) Motive := by
    have hLookup : Lookup G1 0 Motive.lift := .zero
    have hBvar := IsDefEqStrong.bvar hLookup (by
      simpa [Motive, NatS, SExpr.lift, SExpr.lift'] using hMotiveTypeG1)
    simpa [Motive, NatS, SExpr.lift, SExpr.lift'] using hBvar
  have hCodP : IsDefEqStrong (Motive :: G1)
      (SExpr.forallE MinorZero
        (SExpr.forallE MinorSucc (SExpr.forallE NatS Result)))
      (SExpr.forallE MinorZero
        (SExpr.forallE MinorSucc (SExpr.forallE NatS Result)))
      (SExpr.sort restSort1) := by
    simpa [G1, rhoP, Motive, MinorZero, MinorSucc, Result, NatS,
      SExpr.lift, SExpr.lift'] using
      natStrongWeak univs WP.cons hRest1
  have hResultP : IsDefEqStrong G1
      ((SExpr.forallE MinorZero
        (SExpr.forallE MinorSucc
          (SExpr.forallE NatS Result))).inst (SExpr.bvar 0))
      ((SExpr.forallE MinorZero
        (SExpr.forallE MinorSucc
          (SExpr.forallE NatS Result))).inst (SExpr.bvar 0))
      (SExpr.sort restSort1) := by
    simpa [G1, Motive, MinorZero, MinorSucc, Result, NatS,
      SExpr.inst, SExpr.subst, Subst.one, Subst.cons, Subst.lift,
      Subst.id, probeCancelUnderOne, probeCancelUnderTwo] using hRest1
  have hPrefixP0 := IsDefEqStrong.appDF
    hMotiveTypeG1 hCodP hHeadG1 hP hResultP
  have hPrefixP : IsDefEqStrong G1 (Head.app (SExpr.bvar 0))
      (Head.app (SExpr.bvar 0))
      (SExpr.forallE MinorZero
        (SExpr.forallE MinorSucc (SExpr.forallE NatS Result))) := by
    simpa [Head, MinorZero, MinorSucc, Result, NatS,
      SExpr.inst, SExpr.subst, Subst.one, Subst.cons, Subst.lift,
      Subst.id, probeCancelUnderOne, probeCancelUnderTwo] using hPrefixP0
  let rhoZ : Lift := .skip .refl
  have WZ : Ctx.Lift' rhoZ G1 G2 := .skip .refl
  have hPrefixPG2 := natStrongWeak univs WZ hPrefixP
  have hHeadClosedZ : Head.lift' rhoZ = Head := by
    dsimp [Head]
    exact rhsClosed.mkInstS.lift'_eq .zero
  change IsDefEqStrong G2
    ((Head.lift' rhoZ).app (SExpr.bvar 1))
    ((Head.lift' rhoZ).app (SExpr.bvar 1))
    ((SExpr.forallE MinorZero
      (SExpr.forallE MinorSucc
        (SExpr.forallE NatS Result))).lift' rhoZ) at hPrefixPG2
  rw [hHeadClosedZ] at hPrefixPG2
  have hMinorZeroTypeG2 := natStrongWeak univs WZ hMinorZeroType
  have hRest2G := natStrongWeak univs WZ.cons hRest2
  have hZ : IsDefEqStrong G2 (SExpr.bvar 0) (SExpr.bvar 0)
      (MinorZero.lift' rhoZ) :=
    IsDefEqStrong.bvar (.zero : Lookup G2 0 MinorZero.lift) (by
      simpa [rhoZ, SExpr.lift] using hMinorZeroTypeG2)
  have hResultZ : IsDefEqStrong G2
      (((SExpr.forallE MinorSucc
        (SExpr.forallE NatS Result)).lift' rhoZ.cons).inst
          (SExpr.bvar 0))
      (((SExpr.forallE MinorSucc
        (SExpr.forallE NatS Result)).lift' rhoZ.cons).inst
          (SExpr.bvar 0))
      (SExpr.sort restSort2) := by
    simpa [G2, G1, rhoZ, Motive, MinorZero, MinorSucc, Result, NatS,
      SExpr.lift, SExpr.lift', SExpr.inst, SExpr.subst,
      Subst.one, Subst.cons, Subst.lift, Subst.id,
      probeCancelUnderOne, probeCancelUnderTwo] using hRest2
  have hPrefixPZ0 := IsDefEqStrong.appDF
    hMinorZeroTypeG2 hRest2G hPrefixPG2 hZ hResultZ
  have hPrefixPZ : IsDefEqStrong G2
      ((Head.app (SExpr.bvar 1)).app (SExpr.bvar 0))
      ((Head.app (SExpr.bvar 1)).app (SExpr.bvar 0))
      (SExpr.forallE MinorSucc (SExpr.forallE NatS Result)) := by
    simpa [Head, G2, G1, rhoZ, Motive, MinorZero, MinorSucc, Result,
      NatS, SExpr.lift, SExpr.lift', SExpr.inst, SExpr.subst,
      Subst.one, Subst.cons, Subst.lift, Subst.id,
      probeCancelUnderOne, probeCancelUnderTwo] using hPrefixPZ0
  let rhoS : Lift := .skip .refl
  have WS : Ctx.Lift' rhoS G2 G3 := .skip .refl
  have hPrefixPZG3 := natStrongWeak univs WS hPrefixPZ
  have hHeadClosedS : Head.lift' rhoS = Head := by
    dsimp [Head]
    exact rhsClosed.mkInstS.lift'_eq .zero
  change IsDefEqStrong G3
    (((Head.lift' rhoS).app (SExpr.bvar 2)).app (SExpr.bvar 1))
    (((Head.lift' rhoS).app (SExpr.bvar 2)).app (SExpr.bvar 1))
    ((SExpr.forallE MinorSucc
      (SExpr.forallE NatS Result)).lift' rhoS) at hPrefixPZG3
  rw [hHeadClosedS] at hPrefixPZG3
  have hMinorSuccTypeG3 := natStrongWeak univs WS hMinorSuccType
  have hRest3G := natStrongWeak univs WS.cons hRest3
  have hS : IsDefEqStrong G3 (SExpr.bvar 0) (SExpr.bvar 0)
      (MinorSucc.lift' rhoS) :=
    IsDefEqStrong.bvar (.zero : Lookup G3 0 MinorSucc.lift) (by
      simpa [rhoS, SExpr.lift] using hMinorSuccTypeG3)
  have hResultS : IsDefEqStrong G3
      (((SExpr.forallE NatS Result).lift' rhoS.cons).inst
        (SExpr.bvar 0))
      (((SExpr.forallE NatS Result).lift' rhoS.cons).inst
        (SExpr.bvar 0))
      (SExpr.sort restSort3) := by
    simpa [G3, G2, G1, rhoS, Motive, MinorZero, MinorSucc, Result,
      NatS, SExpr.lift, SExpr.lift', SExpr.inst, SExpr.subst,
      Subst.one, Subst.cons, Subst.lift, Subst.id,
      probeCancelUnderOne, probeCancelUnderTwo] using hRest3
  have hPrefixPZS0 := IsDefEqStrong.appDF
    hMinorSuccTypeG3 hRest3G hPrefixPZG3 hS hResultS
  have hPrefixPZS : IsDefEqStrong G3
      (((Head.app (SExpr.bvar 2)).app (SExpr.bvar 1)).app
        (SExpr.bvar 0))
      (((Head.app (SExpr.bvar 2)).app (SExpr.bvar 1)).app
        (SExpr.bvar 0))
      (SExpr.forallE NatS Result) := by
    simpa [Head, G3, G2, G1, rhoS, Motive, MinorZero, MinorSucc,
      Result, NatS, SExpr.lift, SExpr.lift', SExpr.inst, SExpr.subst,
      Subst.one, Subst.cons, Subst.lift, Subst.id,
      probeCancelUnderOne, probeCancelUnderTwo] using hPrefixPZS0
  exact ⟨hPrefixP, hPrefixPZ, hPrefixPZS⟩

/-- The closed generated successor equation, assembled from its local action
and four strong eta contractions. -/
theorem natSuccRuleRegistered (univs : Nat)
    {Gamma : List (@SExpr (natParams univs))}
    (level : @SLevel (natParams univs))
    (_hLhs : @IsDefEqStrong (natParams univs) Gamma
      (@SExpr.mkInst (natParams univs) [level]
        (NatGeneration.rule 1 NatGeneration.flatCtors[1]).lhs)
      (@SExpr.mkInst (natParams univs) [level]
        (NatGeneration.rule 1 NatGeneration.flatCtors[1]).lhs)
      (probeNatSuccRuleType univs level))
    (hRhs : @IsDefEqStrong (natParams univs) Gamma
      (@SExpr.mkInst (natParams univs) [level]
        (NatGeneration.rule 1 NatGeneration.flatCtors[1]).rhs)
      (@SExpr.mkInst (natParams univs) [level]
        (NatGeneration.rule 1 NatGeneration.flatCtors[1]).rhs)
      (probeNatSuccRuleType univs level)) :
    @IsDefEqStrong (natParams univs) Gamma
      (@SExpr.mkInst (natParams univs) [level]
        (NatGeneration.rule 1 NatGeneration.flatCtors[1]).lhs)
      (@SExpr.mkInst (natParams univs) [level]
        (NatGeneration.rule 1 NatGeneration.flatCtors[1]).rhs)
      (probeNatSuccRuleType univs level) := by
  letI : Params := natParams univs
  let NatS : SExpr := SExpr.const ``Nat []
  let Motive : SExpr := SExpr.forallE NatS (SExpr.sort level)
  let MinorZero : SExpr :=
    (SExpr.bvar 0).app (SExpr.const ``Nat.zero [])
  let MinorSucc : SExpr :=
    SExpr.forallE NatS <|
      SExpr.forallE ((SExpr.bvar 2).app (SExpr.bvar 0)) <|
        (SExpr.bvar 3).app
          ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))
  let Result : SExpr :=
    (SExpr.bvar 3).app
      ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0))
  let Head : SExpr := SExpr.mkInst [level]
    (NatGeneration.rule 1 NatGeneration.flatCtors[1]).rhs
  let G1 : List SExpr := Motive :: Gamma
  let G2 : List SExpr := MinorZero :: G1
  let G3 : List SExpr := MinorSucc :: G2
  let Delta : List SExpr := NatS :: G3
  let Redex : SExpr :=
    ((((SExpr.const ``Nat.rec [level]).app (SExpr.bvar 3)).app
      (SExpr.bvar 2)).app (SExpr.bvar 1)).app
        ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0))
  let AppliedRhs : SExpr :=
    [SExpr.bvar 3, SExpr.bvar 2, SExpr.bvar 1,
      SExpr.bvar 0].foldl (fun f a => f.app a) Head
  have hRuleType := hRhs.isType
  obtain ⟨ruleSort, hRuleType0⟩ := hRuleType
  have hRuleType' : IsDefEqStrong Gamma
      (SExpr.forallE Motive
        (SExpr.forallE MinorZero
          (SExpr.forallE MinorSucc (SExpr.forallE NatS Result))))
      (SExpr.forallE Motive
        (SExpr.forallE MinorZero
          (SExpr.forallE MinorSucc (SExpr.forallE NatS Result))))
      (SExpr.sort ruleSort) := by
    simpa [probeNatSuccRuleType, Motive, MinorZero, MinorSucc, Result,
      NatS] using hRuleType0
  obtain ⟨⟨motiveSort, hMotiveType⟩, restSort1, hRest1⟩ :=
    hRuleType'.forallE_inv' (.inl rfl)
  obtain ⟨⟨zeroSort, hMinorZeroType⟩, restSort2, hRest2⟩ :=
    hRest1.forallE_inv' (.inl rfl)
  obtain ⟨⟨succSort, hMinorSuccType⟩, restSort3, hRest3⟩ :=
    hRest2.forallE_inv' (.inl rfl)
  obtain ⟨⟨natSort, hNatType⟩, resultSort, hResultType⟩ :=
    hRest3.forallE_inv' (.inl rfl)
  have hLocal : IsDefEqStrong Delta Redex AppliedRhs Result := by
    simpa [Head, G3, G2, G1, Delta, Redex, AppliedRhs, Result] using
      natSuccRuleLocalStrong univs (Gamma := Gamma) level
        ⟨ruleSort, hRuleType0⟩ hRhs
  obtain ⟨hPrefixP, hPrefixPZ, hPrefixPZS⟩ :=
    natSuccRulePrefixesStrong univs (Gamma := Gamma) level
      ⟨ruleSort, hRuleType0⟩ hRhs
  obtain ⟨⟨_, _⟩, ⟨rhsClosed, _⟩⟩ :=
    natFinalEnv_ordered.closed.2
      (natRule_registered probeNatFlatCtorSucc_lookup)
  have hLamN : IsDefEqStrong G3
      (SExpr.lam NatS Redex) (SExpr.lam NatS AppliedRhs)
      (SExpr.forallE NatS Result) := by
    exact .lamDF hNatType hResultType hResultType hLocal hLocal
  have hEtaN0 := IsDefEqStrong.eta hPrefixPZS hLamN.hasType.2
  have hEtaN : IsDefEqStrong G3
      (SExpr.lam NatS AppliedRhs)
      (((Head.app (SExpr.bvar 2)).app (SExpr.bvar 1)).app
        (SExpr.bvar 0))
      (SExpr.forallE NatS Result) := by
    simpa [Head, AppliedRhs, SExpr.lift, SExpr.lift',
      rhsClosed.mkInstS.lift_eq] using hEtaN0
  have hPred : IsDefEqStrong G3
      (SExpr.lam NatS Redex)
      (((Head.app (SExpr.bvar 2)).app (SExpr.bvar 1)).app
        (SExpr.bvar 0))
      (SExpr.forallE NatS Result) := hLamN.trans hEtaN
  have hLamS : IsDefEqStrong G2
      (SExpr.lam MinorSucc (SExpr.lam NatS Redex))
      (SExpr.lam MinorSucc
        (((Head.app (SExpr.bvar 2)).app (SExpr.bvar 1)).app
          (SExpr.bvar 0)))
      (SExpr.forallE MinorSucc (SExpr.forallE NatS Result)) := by
    exact .lamDF hMinorSuccType hRest3 hRest3 hPred hPred
  have hEtaS0 := IsDefEqStrong.eta hPrefixPZ hLamS.hasType.2
  have hEtaS : IsDefEqStrong G2
      (SExpr.lam MinorSucc
        (((Head.app (SExpr.bvar 2)).app (SExpr.bvar 1)).app
          (SExpr.bvar 0)))
      ((Head.app (SExpr.bvar 1)).app (SExpr.bvar 0))
      (SExpr.forallE MinorSucc (SExpr.forallE NatS Result)) := by
    simpa [Head, SExpr.lift, SExpr.lift',
      rhsClosed.mkInstS.lift_eq] using hEtaS0
  have hSucc : IsDefEqStrong G2
      (SExpr.lam MinorSucc (SExpr.lam NatS Redex))
      ((Head.app (SExpr.bvar 1)).app (SExpr.bvar 0))
      (SExpr.forallE MinorSucc (SExpr.forallE NatS Result)) :=
    hLamS.trans hEtaS
  have hLamZ : IsDefEqStrong G1
      (SExpr.lam MinorZero
        (SExpr.lam MinorSucc (SExpr.lam NatS Redex)))
      (SExpr.lam MinorZero
        ((Head.app (SExpr.bvar 1)).app (SExpr.bvar 0)))
      (SExpr.forallE MinorZero
        (SExpr.forallE MinorSucc (SExpr.forallE NatS Result))) := by
    exact .lamDF hMinorZeroType hRest2 hRest2 hSucc hSucc
  have hEtaZ0 := IsDefEqStrong.eta hPrefixP hLamZ.hasType.2
  have hEtaZ : IsDefEqStrong G1
      (SExpr.lam MinorZero
        ((Head.app (SExpr.bvar 1)).app (SExpr.bvar 0)))
      (Head.app (SExpr.bvar 0))
      (SExpr.forallE MinorZero
        (SExpr.forallE MinorSucc (SExpr.forallE NatS Result))) := by
    simpa [Head, SExpr.lift, SExpr.lift',
      rhsClosed.mkInstS.lift_eq] using hEtaZ0
  have hZero : IsDefEqStrong G1
      (SExpr.lam MinorZero
        (SExpr.lam MinorSucc (SExpr.lam NatS Redex)))
      (Head.app (SExpr.bvar 0))
      (SExpr.forallE MinorZero
        (SExpr.forallE MinorSucc (SExpr.forallE NatS Result))) :=
    hLamZ.trans hEtaZ
  have hLamP : IsDefEqStrong Gamma
      (SExpr.lam Motive
        (SExpr.lam MinorZero
          (SExpr.lam MinorSucc (SExpr.lam NatS Redex))))
      (SExpr.lam Motive (Head.app (SExpr.bvar 0)))
      (SExpr.forallE Motive
        (SExpr.forallE MinorZero
          (SExpr.forallE MinorSucc (SExpr.forallE NatS Result)))) := by
    exact .lamDF hMotiveType hRest1 hRest1 hZero hZero
  have hHeadExplicit : IsDefEqStrong Gamma Head Head
      (SExpr.forallE Motive
        (SExpr.forallE MinorZero
          (SExpr.forallE MinorSucc (SExpr.forallE NatS Result)))) := by
    simpa [Head, probeNatSuccRuleType, Motive, MinorZero, MinorSucc,
      Result, NatS] using hRhs
  have hEtaP0 := IsDefEqStrong.eta hHeadExplicit hLamP.hasType.2
  have hEtaP : IsDefEqStrong Gamma
      (SExpr.lam Motive (Head.app (SExpr.bvar 0))) Head
      (SExpr.forallE Motive
        (SExpr.forallE MinorZero
          (SExpr.forallE MinorSucc (SExpr.forallE NatS Result)))) := by
    simpa [Head, SExpr.lift, SExpr.lift',
      rhsClosed.mkInstS.lift_eq] using hEtaP0
  have hClosed := hLamP.trans hEtaP
  simpa [Head, Motive, MinorZero, MinorSucc, Result, Redex, NatS,
    probeNatSuccRuleType, probeNatSuccRuleLhsV_eq,
    probeNatSuccRuleLhsV, probeNatSuccRuleBindersV,
    probeNatRuleBindersV, probeNatSuccRuleLhsBodyV,
    SExpr.mkInst, VExpr.instL, VExpr.lamN,
    probeInstVParamZero] using hClosed

/-- Dispatch every registered equation of the concrete Nat environment to
its generated zero or successor proof. -/
theorem natRegistered (univs : Nat)
    {df : VDefEq} {ls : List (@SLevel (natParams univs))}
    {Gamma : List (@SExpr (natParams univs))}
    (hreg : natFinalEnv.defeqs df) (hlen : ls.length = df.uvars)
    (hLhs : @IsDefEqStrong (natParams univs) Gamma
      (@SExpr.mkInst (natParams univs) ls df.lhs)
      (@SExpr.mkInst (natParams univs) ls df.lhs)
      (@SExpr.mkInst (natParams univs) ls df.type))
    (hRhs : @IsDefEqStrong (natParams univs) Gamma
      (@SExpr.mkInst (natParams univs) ls df.rhs)
      (@SExpr.mkInst (natParams univs) ls df.rhs)
      (@SExpr.mkInst (natParams univs) ls df.type)) :
    @IsDefEqStrong (natParams univs) Gamma
      (@SExpr.mkInst (natParams univs) ls df.lhs)
      (@SExpr.mkInst (natParams univs) ls df.rhs)
      (@SExpr.mkInst (natParams univs) ls df.type) := by
  letI : Params := natParams univs
  rw [natFinalEnv_defeqs_iff] at hreg
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hreg
  have hj' : j = 0 ∨ j = 1 := by
    obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hj
    have hlength : NatGeneration.generatedRules.length = 2 := rfl
    omega
  rcases hj' with rfl | rfl
  · have hdf := Option.some.inj
      (probeNatGeneratedRuleZero_lookup.symm.trans hj)
    subst df
    change ls.length = 1 at hlen
    obtain ⟨level, rfl⟩ := List.length_eq_one_iff.mp hlen
    have hLhs' : IsDefEqStrong Gamma
        (SExpr.mkInst [level]
          (NatGeneration.rule 0 NatGeneration.flatCtors[0]).lhs)
        (SExpr.mkInst [level]
          (NatGeneration.rule 0 NatGeneration.flatCtors[0]).lhs)
        (probeNatZeroRuleType univs level) := by
      simpa only [probeNatZeroRuleTypeS_eq] using hLhs
    have hRhs' : IsDefEqStrong Gamma
        (SExpr.mkInst [level]
          (NatGeneration.rule 0 NatGeneration.flatCtors[0]).rhs)
        (SExpr.mkInst [level]
          (NatGeneration.rule 0 NatGeneration.flatCtors[0]).rhs)
        (probeNatZeroRuleType univs level) := by
      simpa only [probeNatZeroRuleTypeS_eq] using hRhs
    simpa only [probeNatZeroRuleTypeS_eq] using
      natZeroRuleRegistered univs level hLhs' hRhs'
  · have hdf := Option.some.inj
      (probeNatGeneratedRuleSucc_lookup.symm.trans hj)
    subst df
    change ls.length = 1 at hlen
    obtain ⟨level, rfl⟩ := List.length_eq_one_iff.mp hlen
    have hLhs' : IsDefEqStrong Gamma
        (SExpr.mkInst [level]
          (NatGeneration.rule 1 NatGeneration.flatCtors[1]).lhs)
        (SExpr.mkInst [level]
          (NatGeneration.rule 1 NatGeneration.flatCtors[1]).lhs)
        (probeNatSuccRuleType univs level) := by
      simpa only [probeNatSuccRuleTypeS_eq] using hLhs
    have hRhs' : IsDefEqStrong Gamma
        (SExpr.mkInst [level]
          (NatGeneration.rule 1 NatGeneration.flatCtors[1]).rhs)
        (SExpr.mkInst [level]
          (NatGeneration.rule 1 NatGeneration.flatCtors[1]).rhs)
        (probeNatSuccRuleType univs level) := by
      simpa only [probeNatSuccRuleTypeS_eq] using hRhs
    simpa only [probeNatSuccRuleTypeS_eq] using
      natSuccRuleRegistered univs level hLhs' hRhs'

/-- The complete concrete semantic bridge for the generated Nat fixture. -/
noncomputable def natSemantic (univs : Nat) :
    letI : Params := natParams univs
    Params.Semantic := by
  letI : Params := natParams univs
  exact {
  structureEta := by
    intro rule levels Gamma params major hreg
    exact (natFinalEnv_no_structEta rule hreg).elim
  ctor := by
    intro c ci ls Gamma hci hlen cl
    exact natCtor univs hci hlen cl
  defn := by
    intro c r hpat
    exact (natPat_no_const univs hpat).elim
  iotaRule := by
    intro rec major ctor arity r hpat
    exact natIotaRule univs hpat
  iotaSite := by
    intro rec major ctor arity r Gamma A majorTerm recLs ctorLs
      recArgs ctorArgs mcap rule captureType captureTyping hGamma typing
      matched redexSelf AType
    exact natIotaSite univs rule captureType captureTyping hGamma typing
      matched redexSelf AType
  registered := by
    intro df ls Gamma hreg hlen hLhs hRhs
    exact natRegistered univs hreg hlen hLhs hRhs }

/-- Exact guarded output for the generated Nat-zero RHS.

The descriptor fixes the real registered body and its three generated
captures.  Since the zero constructor has no fields, every live capture is a
recursor-prefix capture and already carries paired guarded evidence; the
constructor side of the mixed iota contract is eliminated as `Empty`.
`convert` is consulted only at conversion edges retained by the actual
`PathSpineWF`, while `headSelf` is the recursive adequacy result for the
literal registered fixed body selected by the semantic RHS. -/
theorem natZeroRuleRHS_directOutput
    (univs : Nat) (level : @SLevel (natParams univs))
    [semantic : @Params.Semantic (natParams univs)] :
    letI : Params := natParams univs
    ∀ {Γ : List SExpr}
      {mrec : (Pattern.varN (.const ``Nat.rec) 3).Path → TShape}
      {mctor : (Pattern.varN (.const ``Nat.zero) 0).Path → TShape}
      {mx my captureType :
        (RecursorIotaPattern ``Nat.rec 3 ``Nat.zero 0).Path → SExpr}
      {head : TShape} {n : Nat}
      {out outTy : WShape (n + 1)} {resultType : SExpr},
    LE_Interp.RHS.ShapeSpine (Sum.elim mrec mctor) head
        (natZeroDirectIotaRule univs).capturePaths out.T →
    (∀ path,
      match path with
      | Sum.inl p => LR.DirectCaptureDefEqAligned
          (LRD Γ : LR.DirectRelBase Γ (n + 1))
          (mrec p) (mx path) (my path) (captureType path)
      | Sum.inr p => LRS.CaptureDefEqAligned (n := n) (LR Γ)
          (mctor p) (mx path) (my path) (captureType path)) →
    out.HasType outTy → ¬out.T ≤ TShape.bot →
    SExpr.PathSpineWF Γ mx captureType
      (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.type)
      (natZeroDirectIotaRule univs).capturePaths resultType →
    (LRD Γ).TyDefEq resultType resultType outTy →
    LRD.FixedHeadConvertStep Γ →
    (∀ {headLevel : Nat} {headElem headElemTy : WShape headLevel},
      headElem.T ≤ head → headElem.HasType headElemTy →
      (LRD Γ).DefEq
        (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.rhs)
        (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.rhs)
        (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.type)
        headElem headElemTy) →
    (LRD Γ).DefEq
      ((NatGeneration.ruleRHS natRuleClosure
        probeNatFlatCtorZero_lookup).applyS [level] mx)
      ((NatGeneration.ruleRHS natRuleClosure
        probeNatFlatCtorZero_lookup).applyS [level] my)
      resultType out outTy := by
  letI : Params := natParams univs
  letI : Params.Semantic := semantic
  intro Γ mrec mctor mx my captureType head n out outTy resultType
    H hcap hout houtNonbot raw resultRel convert headSelf
  apply H.directApplyRuleWithHeadSelf
  · intro path
    cases path with
    | inl p => exact (hcap (.inl p)).atSomeLevel.toTerm
    | inr p => exact nomatch p
  · exact hout
  · exact houtNonbot
  · rw [natZeroDirectIotaRule_capturePaths]
    simp
  · exact raw
  · exact resultRel
  · exact convert
  · exact headSelf

/-- The complete guarded generated-RHS contract for the Nat-zero rule.

The semantic evaluator may still choose bottom; that case closes uniformly.
At every informative output, `natZeroRuleRHS_directOutput` discharges the
literal capture inventory and exact generated syntax.  The caller supplies
only the proof-relevant recursive self-relation of the fixed body and the
guarded conversions authorized at actual path-spine edges. -/
theorem natZeroIotaRHSDefEq_of_headSelf
    (univs : Nat) (level : @SLevel (natParams univs))
    [semantic : @Params.Semantic (natParams univs)] :
    letI : Params := natParams univs
    ∀ {n : Nat} {Γ : List SExpr} {R : TShape → SExpr → Prop}
      {ρ : Valuation}
      {mrec : (Pattern.varN (.const ``Nat.rec) 3).Path → TShape}
      {mctor : (Pattern.varN (.const ``Nat.zero) 0).Path → TShape}
      {out : WShape (n + 1)},
    (∀ {m M}, R m M → LE_Interp.Witness ρ m M) →
    LRD.FixedHeadConvertStep Γ →
    (∀ {head : TShape},
      LE_Interp.Witness ρ head
          (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.rhs) →
      ∀ {headLevel : Nat} {headElem headElemTy : WShape headLevel},
        headElem.T ≤ head → headElem.HasType headElemTy →
        (LRD Γ).DefEq
          (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.rhs)
          (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.rhs)
          (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.type)
          headElem headElemTy) →
    LRD.IotaRHSDefEq (Γ := Γ) (LE_Interp.Lower R) [level]
      mrec mctor
      (NatGeneration.ruleRHS natRuleClosure
          probeNatFlatCtorZero_lookup,
        NatGeneration.ruleCheck natRuleClosure
          (List.mem_of_getElem? probeNatFlatCtorZero_lookup))
      (natZeroDirectIotaRule univs) out := by
  letI : Params := natParams univs
  letI : Params.Semantic := semantic
  intro n Γ R ρ mrec mctor out hR convert headSelf
  apply LRD.IotaRHSDefEq.of_nonbotWitness hR
  intro head mx my captureType A outTy hhead _hstrong hshape _htyped
    hspineX _hspineY hcap hout hA
  by_cases houtBot : out.T ≤ TShape.bot
  · have houtEq : out = .bot := TShape.le_bot.1 houtBot
    subst out
    exact LRD.DefEq.bot hout.isType
  · exact natZeroRuleRHS_directOutput univs level
      (Γ := Γ) (mrec := mrec) (mctor := mctor)
      (mx := mx) (my := my) (captureType := captureType)
      (head := head) (n := n) (out := out) (outTy := outTy)
      (resultType := A)
      hshape (fun path => by
        cases path with
        | inl p => exact hcap (.inl p)
        | inr p => exact nomatch p)
      hout houtBot hspineX hA convert (headSelf hhead)

/-- Exact guarded output for the generated Nat-successor RHS.

The three recursor-prefix captures already carry paired guarded evidence.
The fourth capture is the predecessor field, which enters the generic iota
contract at legacy level `n`; `predDirect` supplies precisely its recursive
guarded term edge.  The zipper reconstructs guarded domain typing from the
actual Pi edge, so no predecessor type sidecar is required. -/
theorem natSuccRuleRHS_directOutput
    (univs : Nat) (level : @SLevel (natParams univs))
    [semantic : @Params.Semantic (natParams univs)] :
    letI : Params := natParams univs
    ∀ {Γ : List SExpr}
      {mrec : (Pattern.varN (.const ``Nat.rec) 3).Path → TShape}
      {mctor : (Pattern.varN (.const ``Nat.succ) 1).Path → TShape}
      {mx my captureType :
        (RecursorIotaPattern ``Nat.rec 3 ``Nat.succ 1).Path → SExpr}
      {head : TShape} {n : Nat}
      {out outTy : WShape (n + 1)} {resultType : SExpr},
    LE_Interp.RHS.ShapeSpine (Sum.elim mrec mctor) head
        (natSuccDirectIotaRule univs).capturePaths out.T →
    (∀ path,
      match path with
      | Sum.inl p => LR.DirectCaptureDefEqAligned
          (LRD Γ : LR.DirectRelBase Γ (n + 1))
          (mrec p) (mx path) (my path) (captureType path)
      | Sum.inr p => LRS.CaptureDefEqAligned (n := n) (LR Γ)
          (mctor p) (mx path) (my path) (captureType path)) →
    LR.DirectTermCaptureDefEqAligned.AtSomeLevel Γ
      (mctor none) (mx natSuccPredPath) (my natSuccPredPath)
      (captureType natSuccPredPath) →
    out.HasType outTy → ¬out.T ≤ TShape.bot →
    SExpr.PathSpineWF Γ mx captureType
      (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.type)
      (natSuccDirectIotaRule univs).capturePaths resultType →
    (LRD Γ).TyDefEq resultType resultType outTy →
    LRD.FixedHeadConvertStep Γ →
    (∀ {headLevel : Nat} {headElem headElemTy : WShape headLevel},
      headElem.T ≤ head → headElem.HasType headElemTy →
      (LRD Γ).DefEq
        (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.rhs)
        (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.rhs)
        (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.type)
        headElem headElemTy) →
    (LRD Γ).DefEq
      ((NatGeneration.ruleRHS natRuleClosure
        probeNatFlatCtorSucc_lookup).applyS [level] mx)
      ((NatGeneration.ruleRHS natRuleClosure
        probeNatFlatCtorSucc_lookup).applyS [level] my)
      resultType out outTy := by
  letI : Params := natParams univs
  letI : Params.Semantic := semantic
  intro Γ mrec mctor mx my captureType head n out outTy resultType
    H hcap predDirect hout houtNonbot raw resultRel convert headSelf
  apply H.directApplyRuleWithHeadSelf
  · intro path
    cases path with
    | inl p => exact (hcap (.inl p)).atSomeLevel.toTerm
    | inr p =>
      cases p with
      | none => exact predDirect
      | some p => exact nomatch p
  · exact hout
  · exact houtNonbot
  · rw [natSuccDirectIotaRule_capturePaths]
    simp
  · exact raw
  · exact resultRel
  · exact convert
  · exact headSelf

/-- The complete guarded generated-RHS contract for the Nat-successor rule.

As in the zero case, bottom closes internally and the selected fixed body is
consumed proof-relevantly.  `upgradePred` exposes the sole recursive-field
term boundary left intentionally mixed by `LRD.IotaRHSDefEq`; guarded domain
typing is recovered from the generated telescope and no final RHS relation
is accepted as a premise. -/
theorem natSuccIotaRHSDefEq_of_headSelf
    (univs : Nat) (level : @SLevel (natParams univs))
    [semantic : @Params.Semantic (natParams univs)] :
    letI : Params := natParams univs
    ∀ {n : Nat} {Γ : List SExpr} {R : TShape → SExpr → Prop}
      {ρ : Valuation}
      {mrec : (Pattern.varN (.const ``Nat.rec) 3).Path → TShape}
      {mctor : (Pattern.varN (.const ``Nat.succ) 1).Path → TShape}
      {out : WShape (n + 1)},
    (∀ {m M}, R m M → LE_Interp.Witness ρ m M) →
    LRD.FixedHeadConvertStep Γ →
    (∀ {head : TShape},
      LE_Interp.Witness ρ head
          (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.rhs) →
      ∀ {headLevel : Nat} {headElem headElemTy : WShape headLevel},
        headElem.T ≤ head → headElem.HasType headElemTy →
        (LRD Γ).DefEq
          (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.rhs)
          (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.rhs)
          (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.type)
          headElem headElemTy) →
    (∀ {mx my captureType :
          (RecursorIotaPattern ``Nat.rec 3 ``Nat.succ 1).Path → SExpr}
        (H : LRS.CaptureDefEqAligned (n := n) (LR Γ)
          (mctor none) (mx natSuccPredPath) (my natSuccPredPath)
          (captureType natSuccPredPath)),
      LR.DirectTermCaptureDefEqAligned.Upgrade H) →
    LRD.IotaRHSDefEq (Γ := Γ) (LE_Interp.Lower R) [level]
      mrec mctor
      (NatGeneration.ruleRHS natRuleClosure
          probeNatFlatCtorSucc_lookup,
        NatGeneration.ruleCheck natRuleClosure
          (List.mem_of_getElem? probeNatFlatCtorSucc_lookup))
      (natSuccDirectIotaRule univs) out := by
  letI : Params := natParams univs
  letI : Params.Semantic := semantic
  intro n Γ R ρ mrec mctor out hR convert headSelf upgradePred
  apply LRD.IotaRHSDefEq.of_nonbotWitness hR
  intro head mx my captureType A outTy hhead _hstrong hshape _htyped
    hspineX _hspineY hcap hout hA
  by_cases houtBot : out.T ≤ TShape.bot
  · have houtEq : out = .bot := TShape.le_bot.1 houtBot
    subst out
    exact LRD.DefEq.bot hout.isType
  · apply natSuccRuleRHS_directOutput univs level
      (Γ := Γ) (mrec := mrec) (mctor := mctor)
      (mx := mx) (my := my) (captureType := captureType)
      (head := head) (n := n) (out := out) (outTy := outTy)
      (resultType := A) hshape
    · intro path
      cases path with
      | inl p => exact hcap (.inl p)
      | inr p =>
        cases p with
        | none => exact hcap (.inr none)
        | some p => exact nomatch p
    · exact (upgradePred (hcap natSuccPredPath)).atSomeLevel
    · exact hout
    · exact houtBot
    · exact hspineX
    · exact hA
    · exact convert
    · exact headSelf hhead

/-- Exact Nat-zero generated-RHS output from recursive guarded
self-adequacy.

The proof-relevant producer owns the direct capture telescope and the
registered type witness at one synchronized head observation.  Consequently
the recursive result is consumed through `LRD.SelfAdequateAt` rather than an
unrestricted `headSelf` callback over arbitrary typed lower pairs. -/
theorem natZeroRuleRHS_directOutput_of_selfAdequate
    (univs : Nat) (level : @SLevel (natParams univs))
    [semantic : @Params.Semantic (natParams univs)] :
    letI : Params := natParams univs
    ∀ {Γ : List SExpr} {ρ : Valuation} {root : TShape} {depth : Nat}
      {Δ : List SExpr} {σ σ' : Subst} {core : Bool}
      {mrec : (Pattern.varN (.const ``Nat.rec) 3).Path → TShape}
      {mctor : (Pattern.varN (.const ``Nat.zero) 0).Path → TShape}
      {mx my captureType :
        (RecursorIotaPattern ``Nat.rec 3 ``Nat.zero 0).Path → SExpr}
      {head : TShape} {n : Nat}
      {out outTy : WShape (n + 1)} {resultType : SExpr}
      {hX : LE_Interp.Witness ρ root
        (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.rhs)},
    ∀ H : LE_Interp.RHS.ShapeSpine (Sum.elim mrec mctor) head
        (natZeroDirectIotaRule univs).capturePaths out.T,
    LR.DirectFixedHeadProducer Γ ρ mx my captureType H
      (headType := SExpr.mkInst [level]
        (natZeroDirectIotaRule univs).df.type)
      (outTy := outTy) →
    ¬out.T ≤ TShape.bot →
    SExpr.PathSpineWF Γ mx captureType
      (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.type)
      (natZeroDirectIotaRule univs).capturePaths resultType →
    (LRD Γ).TyDefEq resultType resultType outTy →
    LRD.FixedHeadConvertStep Γ →
    LRD.SelfAdequateAt Γ hX depth →
    head ≤ root →
    HasTypeStratifiedS Δ
      (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.rhs)
      (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.type)
      core depth →
    LR.DirectSubstWF Γ σ σ' Δ ρ →
    (LRD Γ).DefEq
      ((NatGeneration.ruleRHS natRuleClosure
        probeNatFlatCtorZero_lookup).applyS [level] mx)
      ((NatGeneration.ruleRHS natRuleClosure
        probeNatFlatCtorZero_lookup).applyS [level] my)
      resultType out outTy := by
  letI : Params := natParams univs
  letI : Params.Semantic := semantic
  intro Γ ρ root depth Δ σ σ' core mrec mctor mx my captureType head n
    out outTy resultType hX H producer houtNonbot raw resultRel convert
    hself hhead hstrat W
  exact H.directApplyRuleWithProducerSelfAdequacy (hX := hX)
    producer houtNonbot
    (by rw [natZeroDirectIotaRule_capturePaths]; simp)
    raw resultRel convert hself hhead hstrat W

/-- Exact Nat-successor generated-RHS output from recursive guarded
self-adequacy.  The proof is identical to the zero branch once the producer
has incorporated the successor's sole predecessor capture. -/
theorem natSuccRuleRHS_directOutput_of_selfAdequate
    (univs : Nat) (level : @SLevel (natParams univs))
    [semantic : @Params.Semantic (natParams univs)] :
    letI : Params := natParams univs
    ∀ {Γ : List SExpr} {ρ : Valuation} {root : TShape} {depth : Nat}
      {Δ : List SExpr} {σ σ' : Subst} {core : Bool}
      {mrec : (Pattern.varN (.const ``Nat.rec) 3).Path → TShape}
      {mctor : (Pattern.varN (.const ``Nat.succ) 1).Path → TShape}
      {mx my captureType :
        (RecursorIotaPattern ``Nat.rec 3 ``Nat.succ 1).Path → SExpr}
      {head : TShape} {n : Nat}
      {out outTy : WShape (n + 1)} {resultType : SExpr}
      {hX : LE_Interp.Witness ρ root
        (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.rhs)},
    ∀ H : LE_Interp.RHS.ShapeSpine (Sum.elim mrec mctor) head
        (natSuccDirectIotaRule univs).capturePaths out.T,
    LR.DirectFixedHeadProducer Γ ρ mx my captureType H
      (headType := SExpr.mkInst [level]
        (natSuccDirectIotaRule univs).df.type)
      (outTy := outTy) →
    ¬out.T ≤ TShape.bot →
    SExpr.PathSpineWF Γ mx captureType
      (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.type)
      (natSuccDirectIotaRule univs).capturePaths resultType →
    (LRD Γ).TyDefEq resultType resultType outTy →
    LRD.FixedHeadConvertStep Γ →
    LRD.SelfAdequateAt Γ hX depth →
    head ≤ root →
    HasTypeStratifiedS Δ
      (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.rhs)
      (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.type)
      core depth →
    LR.DirectSubstWF Γ σ σ' Δ ρ →
    (LRD Γ).DefEq
      ((NatGeneration.ruleRHS natRuleClosure
        probeNatFlatCtorSucc_lookup).applyS [level] mx)
      ((NatGeneration.ruleRHS natRuleClosure
        probeNatFlatCtorSucc_lookup).applyS [level] my)
      resultType out outTy := by
  letI : Params := natParams univs
  letI : Params.Semantic := semantic
  intro Γ ρ root depth Δ σ σ' core mrec mctor mx my captureType head n
    out outTy resultType hX H producer houtNonbot raw resultRel convert
    hself hhead hstrat W
  exact H.directApplyRuleWithProducerSelfAdequacy (hX := hX)
    producer houtNonbot
    (by rw [natSuccDirectIotaRule_capturePaths]; simp)
    raw resultRel convert hself hhead hstrat W

/-- Full generated Nat-zero RHS contract driven by recursive
`LRD.SelfAdequateAt` and a synchronized guarded producer.

`makeAlignment` receives the literal evaluator witness, its synchronized
semantic typing package, direct captures, caller result typing, and the
already-established non-bottom result fact at the informative RHS leaf.  It
must expose the concrete dominance spine and its comparison to the selected
registered-type observation; the generic consumer then constructs the
producer. -/
theorem natZeroIotaRHSDefEq_of_selfAdequate
    (univs : Nat) (level : @SLevel (natParams univs))
    [semantic : @Params.Semantic (natParams univs)] :
    letI : Params := natParams univs
    ∀ {n : Nat} {Γ : List SExpr} {R : TShape → SExpr → Prop}
      {ρ : Valuation} {depth : Nat}
      {Δ : List SExpr} {σ σ' : Subst} {core : Bool}
      {mrec : (Pattern.varN (.const ``Nat.rec) 3).Path → TShape}
      {mctor : (Pattern.varN (.const ``Nat.zero) 0).Path → TShape}
      {out : WShape (n + 1)},
    (∀ {m M}, R m M → LE_Interp.Witness ρ m M) →
    LRD.FixedHeadConvertStep Γ →
    HasTypeStratifiedS Δ
      (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.rhs)
      (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.type)
      core depth →
    LR.DirectSubstWF Γ σ σ' Δ ρ →
    (∀ {root : TShape}
      (hX : LE_Interp.Witness ρ root
        (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.rhs)),
      LRD.SelfAdequateAt Γ hX depth) →
    (∀ {head : TShape}
        {mx my captureType :
          (RecursorIotaPattern ``Nat.rec 3 ``Nat.zero 0).Path → SExpr}
        {outTy : WShape (n + 1)}
        (_hhead : LE_Interp.Witness ρ head
          (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.rhs))
        (_htyped : LE_Interp.Witness.TypedRDeep (fun _ => True) ρ head
          (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.rhs)
          (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.type))
        (hshape : LE_Interp.RHS.ShapeSpine (Sum.elim mrec mctor) head
          (natZeroDirectIotaRule univs).capturePaths out.T)
        (_hcapDirect : ∀ path,
          LR.DirectTermCaptureDefEqAligned.AtSomeLevel Γ
            (Sum.elim mrec mctor path) (mx path) (my path)
            (captureType path))
        (_hout : out.HasType outTy),
      (¬out.T ≤ TShape.bot) →
      LR.DirectFixedHeadAlignedTyping Γ ρ mx my captureType
        (P := fun _ => True)
        (body := SExpr.mkInst [level]
          (natZeroDirectIotaRule univs).df.rhs)
        (headType := SExpr.mkInst [level]
          (natZeroDirectIotaRule univs).df.type)
        (outTy := outTy) hshape) →
    LRD.IotaRHSDefEq (Γ := Γ) (LE_Interp.Lower R) [level]
      mrec mctor
      (NatGeneration.ruleRHS natRuleClosure
          probeNatFlatCtorZero_lookup,
        NatGeneration.ruleCheck natRuleClosure
          (List.mem_of_getElem? probeNatFlatCtorZero_lookup))
      (natZeroDirectIotaRule univs) out := by
  letI : Params := natParams univs
  letI : Params.Semantic := semantic
  intro n Γ R ρ depth Δ σ σ' core mrec mctor out hR convert hstrat W
    self makeAlignment
  apply LRD.IotaRHSDefEq.of_nonbotWitness hR
  intro head mx my captureType A outTy hhead _hstrong hshape _htyped
    hspineX _hspineY hcap hout hA
  by_cases houtBot : out.T ≤ TShape.bot
  · have houtEq : out = .bot := TShape.le_bot.1 houtBot
    subst out
    exact LRD.DefEq.bot hout.isType
  · have hcapDirect : ∀ path,
        LR.DirectTermCaptureDefEqAligned.AtSomeLevel Γ
          (Sum.elim mrec mctor path) (mx path) (my path)
          (captureType path) := by
      intro path
      cases path with
      | inl p => exact (hcap (.inl p)).atSomeLevel.toTerm
      | inr p => exact nomatch p
    have hstrongΔ : IsDefEqStrong Δ
        (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.rhs)
        (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.rhs)
        (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.type) :=
      (natZeroDirectIotaRule univs).rhsStrong [level]
    have htyped := hhead.typedRDeepTrue_of_strong hstrongΔ W.fits
    have aligned :=
      makeAlignment hhead htyped hshape hcapDirect hout houtBot
    exact natZeroRuleRHS_directOutput_of_selfAdequate univs level
      (hX := hhead) hshape
      aligned.producer
      houtBot hspineX hA convert (self hhead) TShape.LE.rfl hstrat W

/-- Registered-view Nat-zero RHS closure with no alignment callback.

The listed action materializer identifies the exact motive, zero-minor, and
successor-minor shapes selected by the registered recursor trace.  The
semantic application spine is then relevelled to a common consecutive tower;
the registered zero-rule witness supplies that tower's type interpretation,
so recursive self-adequacy can be consumed directly. -/
theorem natZeroIotaRHSDefEq_of_registeredView
    (univs : Nat) (level : @SLevel (natParams univs))
    [semantic : @Params.Semantic (natParams univs)] :
    letI : Params := natParams univs
    ∀ {n : Nat} {Γ : List SExpr} {R : TShape → SExpr → Prop}
      {ρ : Valuation} {depth : Nat}
      {Δ : List SExpr} {σ σ' : Subst} {core : Bool}
      {mrec : (Pattern.varN (.const ``Nat.rec) 3).Path → TShape}
      {mctor : (Pattern.varN (.const ``Nat.zero) 0).Path → TShape}
      {majorX majorY succX zeroX motiveX succY zeroY motiveY : SExpr}
      {recHeadType A : SExpr}
      {succShape zeroShape motiveShape : WShape (n + 1)}
      {out outTy : WShape (n + 1)}
      {trace : LR.DirectRegisteredTypeTrace Γ ρ recHeadType
        [majorX, succX, zeroX, motiveX]
        [majorY, succY, zeroY, motiveY]
        [(.ctor' ``Nat.zero []), succShape, zeroShape, motiveShape]
        A outTy}
      {siteXs siteYs : List SExpr},
    ∀ (view : LR.DirectRegisteredTypeTrace.FourView trace),
    (∀ {m M}, R m M → LE_Interp.Witness ρ m M) →
    LRD.FixedHeadConvertStep Γ →
    HasTypeStratifiedS Δ
      (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.rhs)
      (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.type)
      core depth →
    LR.DirectSubstWF Γ σ σ' Δ ρ →
    (∀ {root : TShape}
      (hX : LE_Interp.Witness ρ root
        (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.rhs)),
      LRD.SelfAdequateAt Γ hX depth) →
    LE_Interp.Witness ρ (view.sparsePrefix outTy).T
      (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.type) →
    LRD.IotaRHSDefEqListedRecAt (Γ := Γ) (LE_Interp.Lower R) [level]
      mrec mctor
      (NatGeneration.ruleRHS natRuleClosure
          probeNatFlatCtorZero_lookup,
        NatGeneration.ruleCheck natRuleClosure
          (List.mem_of_getElem? probeNatFlatCtorZero_lookup))
      siteXs siteYs
      [view.third.domainExpr, view.second.domainExpr,
        view.first.domainExpr]
      [succShape, zeroShape, motiveShape]
      [view.third.domain.lift (n + 1),
        view.second.domain.lift (n + 1),
        view.first.domain.lift (n + 1)]
      (natZeroDirectIotaRule univs) A out outTy := by
  letI : Params := natParams univs
  letI : Params.Semantic := semantic
  intro n Γ R ρ depth Δ σ σ' core mrec mctor majorX majorY succX
    zeroX motiveX succY zeroY motiveY recHeadType A succShape zeroShape
    motiveShape out outTy trace siteXs siteYs view hR convert hstrat W self
    hRuleType
  intro hrhs mx my captureType recElemShape recTypeShape
    hspineX _hspineY _hcap hcapRec _hrecXs _hrecYs _hrecTypes
    hrecShapes hrecTypeShapes hout hA
  by_cases houtBot : out.T ≤ TShape.bot
  · have houtEq : out = .bot := TShape.le_bot.1 houtBot
    subst out
    exact LRD.DefEq.bot hout.isType
  obtain hbot | ⟨head, hhead, hshape⟩ :=
    (natZeroDirectIotaRule univs).rhsShapeSpine hrhs
  · exact (houtBot hbot).elim
  have hshape' := hshape
  rw [natZeroDirectIotaRule_capturePaths] at hshape'
  obtain ⟨hmotiveElem, hzeroElem, hsuccElem⟩ :=
    natRecThreeReadback hrecShapes
  obtain ⟨hmotiveType, hzeroType, hsuccType⟩ :=
    natRecThreeReadback hrecTypeShapes
  have hsuccCap : LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
      (mrec none) (mx natZeroSuccMinorPath) (my natZeroSuccMinorPath)
      (captureType natZeroSuccMinorPath) succShape
      (view.third.domain.lift (n + 1)) := by
    simpa only [natZeroSuccMinorPath, hsuccElem, hsuccType] using
      (hcapRec none).toTerm
  have hzeroCap : LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
      (mrec (some none)) (mx natZeroMinorPath) (my natZeroMinorPath)
      (captureType natZeroMinorPath) zeroShape
      (view.second.domain.lift (n + 1)) := by
    simpa only [natZeroMinorPath, hzeroElem, hzeroType] using
      (hcapRec (some none)).toTerm
  have hmotiveCap : LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
      (mrec (some (some none))) (mx natZeroMotivePath)
      (my natZeroMotivePath) (captureType natZeroMotivePath)
      motiveShape (view.first.domain.lift (n + 1)) := by
    simpa only [natZeroMotivePath, hmotiveElem, hmotiveType] using
      (hcapRec (some (some none))).toTerm
  obtain ⟨k, hbase, headK, hheadK, hdom⟩ :=
    natZeroShapeSpine_relevelDirect univs hshape'
      hsuccCap hzeroCap hmotiveCap hout
  have htower : natZeroCaptureTower succShape zeroShape motiveShape
        (view.third.domain.lift (n + 1))
        (view.second.domain.lift (n + 1))
        (view.first.domain.lift (n + 1)) outTy =
      view.sparsePrefix outTy := by
    simp only [natZeroCaptureTower,
      LR.DirectRegisteredTypeTrace.FourView.sparsePrefix,
      WShape.lift_lift (.inl view.first.levelLE),
      WShape.lift_lift (.inl view.second.levelLE)]
  have htowerLevel : (view.sparsePrefix outTy).T.1 ≤ k + 3 := by
    change n + 4 ≤ k + 3
    omega
  have hRuleTypeK : LE_Interp.Witness ρ
      ((natZeroCaptureTower succShape zeroShape motiveShape
        (view.third.domain.lift (n + 1))
        (view.second.domain.lift (n + 1))
        (view.first.domain.lift (n + 1)) outTy).lift (k + 3)).T
      (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.type) := by
    rw [htower]
    exact hRuleType.mono (TShape.lift_eqv htowerLevel).1
  rw [← natZeroDirectIotaRule_capturePaths] at hdom
  have hshapeK := hdom.spine
  have producer : LR.DirectFixedHeadProducer Γ ρ mx my captureType
      hshapeK
      (headType := SExpr.mkInst [level]
        (natZeroDirectIotaRule univs).df.type)
      (outTy := outTy.lift k) := by
    exact hdom.producer hRuleTypeK
  have houtKNonbot : ¬(out.lift k).T ≤ TShape.bot := by
    intro hbotK
    exact houtBot ((TShape.lift_eqv hbase).2.trans hbotK)
  have hAK : (LRD Γ).TyDefEq A A (outTy.lift k) :=
    (LRD.TyDefEq.lift hbase hout.isType).2 hA
  have hhigh : (LRD Γ).DefEq
      ((NatGeneration.ruleRHS natRuleClosure
        probeNatFlatCtorZero_lookup).applyS [level] mx)
      ((NatGeneration.ruleRHS natRuleClosure
        probeNatFlatCtorZero_lookup).applyS [level] my)
      A (out.lift k) (outTy.lift k) := by
    exact hshapeK.directApplyRuleWithProducerSelfAdequacy
      (hX := hhead.fixedLowerWitness hR) producer houtKNonbot
      (by rw [natZeroDirectIotaRule_capturePaths]; simp)
      hspineX hAK convert (self (hhead.fixedLowerWitness hR))
      hheadK hstrat W
  exact (LRD.DefEq.lift hbase hout).1 hhigh

/-- Registered-view Nat-successor RHS closure with no alignment callback.

The exact predecessor capture is the sole recursive-field input.  Once it is
fixed at the lifted native field and `indTy`, the registered recursor trace
constructs the fourth semantic binder itself; all four application edges are
then relevelled to one consecutive tower and consumed by recursive guarded
self-adequacy. -/
theorem natSuccIotaRHSDefEq_of_registeredView
    (univs : Nat) (level : @SLevel (natParams univs))
    [semantic : @Params.Semantic (natParams univs)] :
    letI : Params := natParams univs
    ∀ {n : Nat} {Γ : List SExpr} {R : TShape → SExpr → Prop}
      {ρ : Valuation} {depth : Nat}
      {Δ : List SExpr} {σ σ' : Subst} {core : Bool}
      {mrec : (Pattern.varN (.const ``Nat.rec) 3).Path → TShape}
      {mctor : (Pattern.varN (.const ``Nat.succ) 1).Path → TShape}
      {majorX majorY succX zeroX motiveX succY zeroY motiveY : SExpr}
      {A : SExpr} {field : WShape n}
      {succShape zeroShape motiveShape : WShape (n + 1)}
      {out outTy : WShape (n + 1)}
      {trace : LR.DirectRegisteredTypeTrace Γ ρ
        (SExpr.mkInst [level]
          (VInductDecl.recConst 0 ``Nat 0 InductiveFixtures.natType).type)
        [majorX, succX, zeroX, motiveX]
        [majorY, succY, zeroY, motiveY]
        [(.ctor' ``Nat.succ [field]), succShape, zeroShape, motiveShape]
        A outTy}
      {siteXs siteYs : List SExpr},
    ∀ (view : LR.DirectRegisteredTypeTrace.FourView trace),
    (∀ {m M}, R m M → LE_Interp.Witness ρ m M) →
    LRD.FixedHeadConvertStep Γ →
    HasTypeStratifiedS Δ
      (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.rhs)
      (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.type)
      core depth →
    LR.DirectSubstWF Γ σ σ' Δ ρ →
    (∀ {root : TShape}
      (hX : LE_Interp.Witness ρ root
        (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.rhs)),
      LRD.SelfAdequateAt Γ hX depth) →
    (∀ {mx my captureType :
          (RecursorIotaPattern ``Nat.rec 3 ``Nat.succ 1).Path → SExpr},
      LRS.CaptureDefEqAligned (n := n) (LR Γ)
          (mctor none) (mx natSuccPredPath) (my natSuccPredPath)
          (captureType natSuccPredPath) →
      LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
        (mctor none) (mx natSuccPredPath) (my natSuccPredPath)
        (captureType natSuccPredPath) (field.lift (n + 1)) .indTy) →
    LRD.IotaRHSDefEqListedRecAt (Γ := Γ) (LE_Interp.Lower R) [level]
      mrec mctor
      (NatGeneration.ruleRHS natRuleClosure
          probeNatFlatCtorSucc_lookup,
        NatGeneration.ruleCheck natRuleClosure
          (List.mem_of_getElem? probeNatFlatCtorSucc_lookup))
      siteXs siteYs
      [view.third.domainExpr, view.second.domainExpr,
        view.first.domainExpr]
      [succShape, zeroShape, motiveShape]
      [view.third.domain.lift (n + 1),
        view.second.domain.lift (n + 1),
        view.first.domain.lift (n + 1)]
      (natSuccDirectIotaRule univs) A out outTy := by
  letI : Params := natParams univs
  letI : Params.Semantic := semantic
  intro n Γ R ρ depth Δ σ σ' core mrec mctor majorX majorY succX
    zeroX motiveX succY zeroY motiveY A field succShape zeroShape
    motiveShape out outTy trace siteXs siteYs view hR convert hstrat W self
    predExact
  intro hrhs mx my captureType recElemShape recTypeShape
    hspineX _hspineY hcap hcapRec _hrecXs _hrecYs _hrecTypes
    hrecShapes hrecTypeShapes hout hA
  by_cases houtBot : out.T ≤ TShape.bot
  · have houtEq : out = .bot := TShape.le_bot.1 houtBot
    subst out
    exact LRD.DefEq.bot hout.isType
  obtain hbot | ⟨head, hhead, hshape⟩ :=
    (natSuccDirectIotaRule univs).rhsShapeSpine hrhs
  · exact (houtBot hbot).elim
  have hshape' := hshape
  rw [natSuccDirectIotaRule_capturePaths] at hshape'
  obtain ⟨hmotiveElem, hzeroElem, hsuccElem⟩ :=
    natRecThreeReadback hrecShapes
  obtain ⟨hmotiveType, hzeroType, hsuccType⟩ :=
    natRecThreeReadback hrecTypeShapes
  have hsuccCap : LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
      (mrec none) (mx natSuccMinorPath) (my natSuccMinorPath)
      (captureType natSuccMinorPath) succShape
      (view.third.domain.lift (n + 1)) := by
    simpa only [natSuccMinorPath, hsuccElem, hsuccType] using
      (hcapRec none).toTerm
  have hzeroCap : LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
      (mrec (some none)) (mx natSuccZeroMinorPath)
      (my natSuccZeroMinorPath) (captureType natSuccZeroMinorPath)
      zeroShape (view.second.domain.lift (n + 1)) := by
    simpa only [natSuccZeroMinorPath, hzeroElem, hzeroType] using
      (hcapRec (some none)).toTerm
  have hmotiveCap : LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
      (mrec (some (some none))) (mx natSuccMotivePath)
      (my natSuccMotivePath) (captureType natSuccMotivePath)
      motiveShape (view.first.domain.lift (n + 1)) := by
    simpa only [natSuccMotivePath, hmotiveElem, hmotiveType] using
      (hcapRec (some (some none))).toTerm
  have hpredCap : LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
      (mctor none) (mx natSuccPredPath) (my natSuccPredPath)
      (captureType natSuccPredPath) (field.lift (n + 1)) .indTy :=
    predExact (hcap natSuccPredPath)
  obtain ⟨k, hbase, headK, hheadK, hdom⟩ :=
    natSuccShapeSpine_relevelDirect univs hshape'
      hsuccCap hzeroCap hmotiveCap hpredCap hout
  have hRuleType : LE_Interp.Witness ρ
      (natSuccCaptureTower (field.lift (n + 1)) succShape zeroShape
        motiveShape .indTy
        (view.third.domain.lift (n + 1))
        (view.second.domain.lift (n + 1))
        (view.first.domain.lift (n + 1)) outTy).T
      (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.type) := by
    have hRegistered := natSuccRegisteredRuleTypeSemanticWitness
      (n := n) (Γ := Γ) (ρ := ρ) (level := level)
      (outTy := outTy) univs trace view hpredCap.2.1
    change LE_Interp.Witness ρ
      (natSuccCaptureTower (field.lift (n + 1)) succShape zeroShape
        motiveShape .indTy
        (view.third.domain.lift (n + 1))
        (view.second.domain.lift (n + 1))
        (view.first.domain.lift (n + 1)) outTy).T
      (SExpr.mkInst [level]
        (NatGeneration.rule 1 NatGeneration.flatCtors[1]).type)
    simpa only [probeNatSuccRuleTypeS_eq] using hRegistered
  have htowerLevel :
      (natSuccCaptureTower (field.lift (n + 1)) succShape zeroShape
        motiveShape .indTy
        (view.third.domain.lift (n + 1))
        (view.second.domain.lift (n + 1))
        (view.first.domain.lift (n + 1)) outTy).T.1 ≤ k + 4 := by
    change n + 5 ≤ k + 4
    omega
  have hRuleTypeK : LE_Interp.Witness ρ
      ((natSuccCaptureTower (field.lift (n + 1)) succShape zeroShape
        motiveShape .indTy
        (view.third.domain.lift (n + 1))
        (view.second.domain.lift (n + 1))
        (view.first.domain.lift (n + 1)) outTy).lift (k + 4)).T
      (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.type) :=
    hRuleType.mono (TShape.lift_eqv htowerLevel).1
  rw [← natSuccDirectIotaRule_capturePaths] at hdom
  have hshapeK := hdom.spine
  have producer : LR.DirectFixedHeadProducer Γ ρ mx my captureType
      hshapeK
      (headType := SExpr.mkInst [level]
        (natSuccDirectIotaRule univs).df.type)
      (outTy := outTy.lift k) := by
    exact hdom.producer hRuleTypeK
  have houtKNonbot : ¬(out.lift k).T ≤ TShape.bot := by
    intro hbotK
    exact houtBot ((TShape.lift_eqv hbase).2.trans hbotK)
  have hAK : (LRD Γ).TyDefEq A A (outTy.lift k) :=
    (LRD.TyDefEq.lift hbase hout.isType).2 hA
  have hhigh : (LRD Γ).DefEq
      ((NatGeneration.ruleRHS natRuleClosure
        probeNatFlatCtorSucc_lookup).applyS [level] mx)
      ((NatGeneration.ruleRHS natRuleClosure
        probeNatFlatCtorSucc_lookup).applyS [level] my)
      A (out.lift k) (outTy.lift k) := by
    exact hshapeK.directApplyRuleWithProducerSelfAdequacy
      (hX := hhead.fixedLowerWitness hR) producer houtKNonbot
      (by rw [natSuccDirectIotaRule_capturePaths]; simp)
      hspineX hAK convert (self (hhead.fixedLowerWitness hR))
      hheadK hstrat W
  exact (LRD.DefEq.lift hbase hout).1 hhigh

/--
info: 'Lean4Lean.SExpr.ParamsD0.natSuccIotaRHSDefEq_of_registeredView' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 probeNatRecTypeV_eq._native.native_decide.ax_1_1,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatSuccRuleTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms natSuccIotaRHSDefEq_of_registeredView

/-- The exact recursive predecessor package consumed by the registered
successor RHS.

Both fields refer to the proof-relevant shapes already selected by `H`: the
source evaluator retains the semantic Nat-type witness, while the strict
recursive branch supplies the single guarded term sidecar. -/
structure NatSuccPredCaptureCoherent [Params]
    (ρ : Valuation) {n : Nat} {Γ : List SExpr}
    {m : TShape} {x y A : SExpr}
    (H : LRS.CaptureDefEqAligned (LR Γ : LogRel Γ n) m x y A) where
  typeWitness : LE_Interp.Witness ρ H.witness.typeShape.T (.const ``Nat [])
  direct : LR.DirectTermCaptureDefEqAligned.Upgrade H

/-- One fully guarded predecessor field rebuilt at the registered root
observation.  The native constructor leaf may live at a different logical
relation level; a framed predecessor producer returns this exact package at
the root field selected by the registered match. -/
structure NatSuccPredArgCoherent [Params]
    (Γ : List SExpr) (ρ : Valuation) {n : Nat}
    (field : WShape n) (x y : SExpr) where
  typeExpr : SExpr
  typeShape : WShape n
  capture : LR.DirectCaptureDefEqAligned.AtShapes (LRD Γ)
    field.T x y typeExpr field typeShape
  typeWitness : LE_Interp.Witness ρ typeShape.T (.const ``Nat [])

/-- Expose a coherent predecessor field as the singleton direct-listed
constructor payload consumed by the exact action materializer. -/
theorem NatSuccPredArgCoherent.listed [Params]
    {Γ : List SExpr} {ρ : Valuation} {n : Nat}
    {field : WShape n} {x y : SExpr}
    (H : NatSuccPredArgCoherent Γ ρ field x y) :
    LR.DirectCtorArgsDefEqListed (LRD Γ)
      [x] [y] [H.typeExpr] [field] [H.typeShape] :=
  .cons H.capture.2.1 H.capture.2.2.1 H.capture.2.2.2.1
    H.capture.2.2.2.2.1 H.capture.2.2.2.2.2.1
    H.capture.2.2.2.2.2.2 .nil

/-- The remaining strict-recursion obligation for a framed successor leaf.

The frame only preserves the constructor head and arity.  This producer
transports the native unary field relation back to the registered root field
and supplies its semantic `Nat` type witness in one proof-relevant package. -/
structure NatSuccFramedPredStep [Params]
    (Γ : List SExpr) (ρ : Valuation) where
  produce :
    ∀ {n k : Nat} {J : LogRel Γ k}
      {field : WShape n} {nativeField : WShape k}
      {x y : SExpr}
      {nativeWF : IsStruct ``Nat.succ →
        WShape.ListNonZero [nativeField]},
      LRS.CtorFrame Γ (LR Γ)
        (.ctor' ``Nat.succ [field]) J
        (.ctor ``Nat.succ [nativeField] nativeWF) →
      LRS.CtorArgsDefEq J [x] [y] [nativeField] →
      NatSuccPredArgCoherent Γ ρ field x y

/-- Registered-view successor closure at the predecessor capture's exact
semantic shapes.

Unlike the canonical-field specialization, this theorem does not retype the
predecessor at `indTy`.  It lifts the selected legacy witness exactly once,
builds the registered rule-type tower from the retained Nat interpretation,
and relevels that same capture together with the three recursor-prefix
captures. -/
theorem natSuccIotaRHSDefEq_of_registeredViewAligned
    (univs : Nat) (level : @SLevel (natParams univs))
    [semantic : @Params.Semantic (natParams univs)] :
    letI : Params := natParams univs
    ∀ {n : Nat} {Γ : List SExpr} {R : TShape → SExpr → Prop}
      {ρ : Valuation} {depth : Nat}
      {Δ : List SExpr} {σ σ' : Subst} {core : Bool}
      {mrec : (Pattern.varN (.const ``Nat.rec) 3).Path → TShape}
      {mctor : (Pattern.varN (.const ``Nat.succ) 1).Path → TShape}
      {majorX majorY succX zeroX motiveX succY zeroY motiveY : SExpr}
      {A : SExpr} {field : WShape n}
      {succShape zeroShape motiveShape : WShape (n + 1)}
      {out outTy : WShape (n + 1)}
      {trace : LR.DirectRegisteredTypeTrace Γ ρ
        (SExpr.mkInst [level]
          (VInductDecl.recConst 0 ``Nat 0 InductiveFixtures.natType).type)
        [majorX, succX, zeroX, motiveX]
        [majorY, succY, zeroY, motiveY]
        [(.ctor' ``Nat.succ [field]), succShape, zeroShape, motiveShape]
        A outTy}
      {siteXs siteYs : List SExpr},
    ∀ (view : LR.DirectRegisteredTypeTrace.FourView trace),
    mctor none = field.T →
    (∀ {m M}, R m M → LE_Interp.Witness ρ m M) →
    LRD.FixedHeadConvertStep Γ →
    HasTypeStratifiedS Δ
      (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.rhs)
      (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.type)
      core depth →
    LR.DirectSubstWF Γ σ σ' Δ ρ →
    (∀ {root : TShape}
      (hX : LE_Interp.Witness ρ root
        (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.rhs)),
      LRD.SelfAdequateAt Γ hX depth) →
    (∀ {mx my captureType :
          (RecursorIotaPattern ``Nat.rec 3 ``Nat.succ 1).Path → SExpr},
      ∀ H : LRS.CaptureDefEqAligned (n := n) (LR Γ)
          (mctor none) (mx natSuccPredPath) (my natSuccPredPath)
          (captureType natSuccPredPath),
      NatSuccPredCaptureCoherent ρ H) →
    LRD.IotaRHSDefEqListedRecAt (Γ := Γ) (LE_Interp.Lower R) [level]
      mrec mctor
      (NatGeneration.ruleRHS natRuleClosure
          probeNatFlatCtorSucc_lookup,
        NatGeneration.ruleCheck natRuleClosure
          (List.mem_of_getElem? probeNatFlatCtorSucc_lookup))
      siteXs siteYs
      [view.third.domainExpr, view.second.domainExpr,
        view.first.domainExpr]
      [succShape, zeroShape, motiveShape]
      [view.third.domain.lift (n + 1),
        view.second.domain.lift (n + 1),
        view.first.domain.lift (n + 1)]
      (natSuccDirectIotaRule univs) A out outTy := by
  letI : Params := natParams univs
  letI : Params.Semantic := semantic
  intro n Γ R ρ depth Δ σ σ' core mrec mctor majorX majorY succX
    zeroX motiveX succY zeroY motiveY A field succShape zeroShape
    motiveShape out outTy trace siteXs siteYs view hmctor hR convert hstrat
    W self predExact
  intro hrhs mx my captureType recElemShape recTypeShape
    hspineX _hspineY hcap hcapRec _hrecXs _hrecYs _hrecTypes
    hrecShapes hrecTypeShapes hout hA
  by_cases houtBot : out.T ≤ TShape.bot
  · have houtEq : out = .bot := TShape.le_bot.1 houtBot
    subst out
    exact LRD.DefEq.bot hout.isType
  obtain hbot | ⟨head, hhead, hshape⟩ :=
    (natSuccDirectIotaRule univs).rhsShapeSpine hrhs
  · exact (houtBot hbot).elim
  have hshape' := hshape
  rw [natSuccDirectIotaRule_capturePaths] at hshape'
  obtain ⟨hmotiveElem, hzeroElem, hsuccElem⟩ :=
    natRecThreeReadback hrecShapes
  obtain ⟨hmotiveType, hzeroType, hsuccType⟩ :=
    natRecThreeReadback hrecTypeShapes
  have hsuccCap : LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
      (mrec none) (mx natSuccMinorPath) (my natSuccMinorPath)
      (captureType natSuccMinorPath) succShape
      (view.third.domain.lift (n + 1)) := by
    simpa only [natSuccMinorPath, hsuccElem, hsuccType] using
      (hcapRec none).toTerm
  have hzeroCap : LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
      (mrec (some none)) (mx natSuccZeroMinorPath)
      (my natSuccZeroMinorPath) (captureType natSuccZeroMinorPath)
      zeroShape (view.second.domain.lift (n + 1)) := by
    simpa only [natSuccZeroMinorPath, hzeroElem, hzeroType] using
      (hcapRec (some none)).toTerm
  have hmotiveCap : LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
      (mrec (some (some none))) (mx natSuccMotivePath)
      (my natSuccMotivePath) (captureType natSuccMotivePath)
      motiveShape (view.first.domain.lift (n + 1)) := by
    simpa only [natSuccMotivePath, hmotiveElem, hmotiveType] using
      (hcapRec (some (some none))).toTerm
  let predH := hcap natSuccPredPath
  let pred := predH.witness
  have predCoherent := predExact predH
  have hpredCap0 : LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
      (mctor none) (mx natSuccPredPath) (my natSuccPredPath)
      (captureType natSuccPredPath) pred.elemShape pred.typeShape := by
    exact ⟨pred.shape, pred.hasType, pred.typeRelated, pred.defeq,
      pred.related, predCoherent.direct.relatedDirect⟩
  have hpredCap : LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
      (mctor none) (mx natSuccPredPath) (my natSuccPredPath)
      (captureType natSuccPredPath) (pred.elemShape.lift (n + 1))
      (pred.typeShape.lift (n + 1)) :=
    hpredCap0.lift (Nat.le_succ n)
  have hfield0 : field ≤ pred.elemShape := by
    apply WShape.LE.of_T
    rw [← hmctor]
    exact pred.shape
  have hfield : field.lift (n + 1) ≤ pred.elemShape.lift (n + 1) :=
    WShape.lift_mono (Nat.le_succ n) hfield0
  have hNat : LE_Interp.Witness ρ
      (pred.typeShape.lift (n + 1)).T (.const ``Nat []) :=
    predCoherent.typeWitness.mono (TShape.lift_eqv (Nat.le_succ n)).1
  obtain ⟨k, hbase, headK, hheadK, hdom⟩ :=
    natSuccShapeSpine_relevelDirectAligned univs hshape'
      hsuccCap hzeroCap hmotiveCap hpredCap hout
  have hRuleType : LE_Interp.Witness ρ
      (natSuccCaptureTower (pred.elemShape.lift (n + 1)) succShape
        zeroShape motiveShape (pred.typeShape.lift (n + 1))
        (view.third.domain.lift (n + 1))
        (view.second.domain.lift (n + 1))
        (view.first.domain.lift (n + 1)) outTy).T
      (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.type) := by
    have hRegistered := natSuccRegisteredRuleTypeSemanticWitnessAligned
      (n := n) (Γ := Γ) (ρ := ρ) (level := level)
      (outTy := outTy) univs trace view hfield hpredCap.2.1 hNat
    change LE_Interp.Witness ρ
      (natSuccCaptureTower (pred.elemShape.lift (n + 1)) succShape
        zeroShape motiveShape (pred.typeShape.lift (n + 1))
        (view.third.domain.lift (n + 1))
        (view.second.domain.lift (n + 1))
        (view.first.domain.lift (n + 1)) outTy).T
      (SExpr.mkInst [level]
        (NatGeneration.rule 1 NatGeneration.flatCtors[1]).type)
    simpa only [probeNatSuccRuleTypeS_eq] using hRegistered
  have htowerLevel :
      (natSuccCaptureTower (pred.elemShape.lift (n + 1)) succShape
        zeroShape motiveShape (pred.typeShape.lift (n + 1))
        (view.third.domain.lift (n + 1))
        (view.second.domain.lift (n + 1))
        (view.first.domain.lift (n + 1)) outTy).T.1 ≤ k + 4 := by
    change n + 5 ≤ k + 4
    omega
  have hRuleTypeK : LE_Interp.Witness ρ
      ((natSuccCaptureTower (pred.elemShape.lift (n + 1)) succShape
        zeroShape motiveShape (pred.typeShape.lift (n + 1))
        (view.third.domain.lift (n + 1))
        (view.second.domain.lift (n + 1))
        (view.first.domain.lift (n + 1)) outTy).lift (k + 4)).T
      (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.type) :=
    hRuleType.mono (TShape.lift_eqv htowerLevel).1
  rw [← natSuccDirectIotaRule_capturePaths] at hdom
  have hshapeK := hdom.spine
  have producer : LR.DirectFixedHeadProducer Γ ρ mx my captureType
      hshapeK
      (headType := SExpr.mkInst [level]
        (natSuccDirectIotaRule univs).df.type)
      (outTy := outTy.lift k) := by
    exact hdom.producer hRuleTypeK
  have houtKNonbot : ¬(out.lift k).T ≤ TShape.bot := by
    intro hbotK
    exact houtBot ((TShape.lift_eqv hbase).2.trans hbotK)
  have hAK : (LRD Γ).TyDefEq A A (outTy.lift k) :=
    (LRD.TyDefEq.lift hbase hout.isType).2 hA
  have hhigh : (LRD Γ).DefEq
      ((NatGeneration.ruleRHS natRuleClosure
        probeNatFlatCtorSucc_lookup).applyS [level] mx)
      ((NatGeneration.ruleRHS natRuleClosure
        probeNatFlatCtorSucc_lookup).applyS [level] my)
      A (out.lift k) (outTy.lift k) := by
    exact hshapeK.directApplyRuleWithProducerSelfAdequacy
      (hX := hhead.fixedLowerWitness hR) producer houtKNonbot
      (by rw [natSuccDirectIotaRule_capturePaths]; simp)
      hspineX hAK convert (self (hhead.fixedLowerWitness hR))
      hheadK hstrat W
  exact (LRD.DefEq.lift hbase hout).1 hhigh

/--
info: 'Lean4Lean.SExpr.ParamsD0.natSuccIotaRHSDefEq_of_registeredViewAligned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 probeNatRecTypeV_eq._native.native_decide.ax_1_1,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatSuccRuleTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms natSuccIotaRHSDefEq_of_registeredViewAligned

/-- Registered-view successor closure from a fully listed guarded
constructor predecessor.

The unary constructor readbacks pin the generated predecessor capture to the
root field, its raw type, and its retained type shape.  This is the form used
by framed successor links: strict recursion rebuilds one direct field payload
and the action materializer consumes it without choosing any second legacy
witness. -/
theorem natSuccIotaRHSDefEq_of_registeredViewDirectListed
    (univs : Nat) (level : @SLevel (natParams univs))
    [semantic : @Params.Semantic (natParams univs)] :
    letI : Params := natParams univs
    ∀ {n : Nat} {Γ : List SExpr} {R : TShape → SExpr → Prop}
      {ρ : Valuation} {depth : Nat}
      {Δ : List SExpr} {σ σ' : Subst} {core : Bool}
      {mrec : (Pattern.varN (.const ``Nat.rec) 3).Path → TShape}
      {mctor : (Pattern.varN (.const ``Nat.succ) 1).Path → TShape}
      {majorX majorY succX zeroX motiveX succY zeroY motiveY : SExpr}
      {A : SExpr} {field : WShape n}
      {succShape zeroShape motiveShape : WShape (n + 1)}
      {out outTy : WShape (n + 1)}
      {trace : LR.DirectRegisteredTypeTrace Γ ρ
        (SExpr.mkInst [level]
          (VInductDecl.recConst 0 ``Nat 0 InductiveFixtures.natType).type)
        [majorX, succX, zeroX, motiveX]
        [majorY, succY, zeroY, motiveY]
        [(.ctor' ``Nat.succ [field]), succShape, zeroShape, motiveShape]
        A outTy}
      {siteXs siteYs : List SExpr}
      {predX predY predType : SExpr} {predTypeShape : WShape n},
    ∀ (view : LR.DirectRegisteredTypeTrace.FourView trace),
    mctor none = field.T →
    LE_Interp.Witness ρ predTypeShape.T (.const ``Nat []) →
    (∀ {m M}, R m M → LE_Interp.Witness ρ m M) →
    LRD.FixedHeadConvertStep Γ →
    HasTypeStratifiedS Δ
      (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.rhs)
      (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.type)
      core depth →
    LR.DirectSubstWF Γ σ σ' Δ ρ →
    (∀ {root : TShape}
      (hX : LE_Interp.Witness ρ root
        (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.rhs)),
      LRD.SelfAdequateAt Γ hX depth) →
    LRD.IotaRHSDefEqDirectListedRecAt (Γ := Γ)
      (LE_Interp.Lower R) [level] mrec mctor
      (NatGeneration.ruleRHS natRuleClosure
          probeNatFlatCtorSucc_lookup,
        NatGeneration.ruleCheck natRuleClosure
          (List.mem_of_getElem? probeNatFlatCtorSucc_lookup))
      siteXs siteYs
      [view.third.domainExpr, view.second.domainExpr,
        view.first.domainExpr]
      [succShape, zeroShape, motiveShape]
      [view.third.domain.lift (n + 1),
        view.second.domain.lift (n + 1),
        view.first.domain.lift (n + 1)]
      [predX] [predY] [predType] [field] [predTypeShape]
      (natSuccDirectIotaRule univs) A out outTy := by
  letI : Params := natParams univs
  letI : Params.Semantic := semantic
  intro n Γ R ρ depth Δ σ σ' core mrec mctor majorX majorY succX
    zeroX motiveX succY zeroY motiveY A field succShape zeroShape
    motiveShape out outTy trace siteXs siteYs predX predY predType
    predTypeShape view hmctor hNat hR convert hstrat W self
  intro hrhs mx my captureType recElemShape recTypeShape
    ctorElemShape ctorTypeShape hspineX _hspineY hcapRec hcapCtor
    _hrecXs _hrecYs _hrecTypes hrecShapes hrecTypeShapes
    hctorXs hctorYs hctorTypes hctorShapes hctorTypeShapes hout hA
  by_cases houtBot : out.T ≤ TShape.bot
  · have houtEq : out = .bot := TShape.le_bot.1 houtBot
    subst out
    exact LRD.DefEq.bot hout.isType
  obtain hbot | ⟨head, hhead, hshape⟩ :=
    (natSuccDirectIotaRule univs).rhsShapeSpine hrhs
  · exact (houtBot hbot).elim
  have hshape' := hshape
  rw [natSuccDirectIotaRule_capturePaths] at hshape'
  obtain ⟨hmotiveElem, hzeroElem, hsuccElem⟩ :=
    natRecThreeReadback hrecShapes
  obtain ⟨hmotiveType, hzeroType, hsuccType⟩ :=
    natRecThreeReadback hrecTypeShapes
  have hpredX : mx natSuccPredPath = predX := by
    simpa only [natSuccPredPath] using natSuccOneReadback hctorXs
  have hpredY : my natSuccPredPath = predY := by
    simpa only [natSuccPredPath] using natSuccOneReadback hctorYs
  have hpredType : captureType natSuccPredPath = predType := by
    simpa only [natSuccPredPath] using natSuccOneReadback hctorTypes
  have hpredElem : ctorElemShape none = field :=
    natSuccOneReadback hctorShapes
  have hpredTypeShape : ctorTypeShape none = predTypeShape :=
    natSuccOneReadback hctorTypeShapes
  have hsuccCap : LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
      (mrec none) (mx natSuccMinorPath) (my natSuccMinorPath)
      (captureType natSuccMinorPath) succShape
      (view.third.domain.lift (n + 1)) := by
    simpa only [natSuccMinorPath, hsuccElem, hsuccType] using
      (hcapRec none).toTerm
  have hzeroCap : LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
      (mrec (some none)) (mx natSuccZeroMinorPath)
      (my natSuccZeroMinorPath) (captureType natSuccZeroMinorPath)
      zeroShape (view.second.domain.lift (n + 1)) := by
    simpa only [natSuccZeroMinorPath, hzeroElem, hzeroType] using
      (hcapRec (some none)).toTerm
  have hmotiveCap : LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
      (mrec (some (some none))) (mx natSuccMotivePath)
      (my natSuccMotivePath) (captureType natSuccMotivePath)
      motiveShape (view.first.domain.lift (n + 1)) := by
    simpa only [natSuccMotivePath, hmotiveElem, hmotiveType] using
      (hcapRec (some (some none))).toTerm
  have hpredCap0 : LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
      (mctor none) (mx natSuccPredPath) (my natSuccPredPath)
      (captureType natSuccPredPath) field predTypeShape := by
    simpa only [natSuccPredPath, hpredX, hpredY, hpredType,
      hpredElem, hpredTypeShape] using (hcapCtor none).toTerm
  have hpredCap : LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
      (mctor none) (mx natSuccPredPath) (my natSuccPredPath)
      (captureType natSuccPredPath) (field.lift (n + 1))
      (predTypeShape.lift (n + 1)) :=
    hpredCap0.lift (Nat.le_succ n)
  have hfield : field.lift (n + 1) ≤ field.lift (n + 1) := .rfl
  have hNat : LE_Interp.Witness ρ
      (predTypeShape.lift (n + 1)).T (.const ``Nat []) :=
    hNat.mono (TShape.lift_eqv (Nat.le_succ n)).1
  obtain ⟨k, hbase, headK, hheadK, hdom⟩ :=
    natSuccShapeSpine_relevelDirectAligned univs hshape'
      hsuccCap hzeroCap hmotiveCap hpredCap hout
  have hRuleType : LE_Interp.Witness ρ
      (natSuccCaptureTower (field.lift (n + 1)) succShape
        zeroShape motiveShape (predTypeShape.lift (n + 1))
        (view.third.domain.lift (n + 1))
        (view.second.domain.lift (n + 1))
        (view.first.domain.lift (n + 1)) outTy).T
      (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.type) := by
    have hRegistered := natSuccRegisteredRuleTypeSemanticWitnessAligned
      (n := n) (Γ := Γ) (ρ := ρ) (level := level)
      (outTy := outTy) univs trace view hfield hpredCap.2.1 hNat
    change LE_Interp.Witness ρ
      (natSuccCaptureTower (field.lift (n + 1)) succShape
        zeroShape motiveShape (predTypeShape.lift (n + 1))
        (view.third.domain.lift (n + 1))
        (view.second.domain.lift (n + 1))
        (view.first.domain.lift (n + 1)) outTy).T
      (SExpr.mkInst [level]
        (NatGeneration.rule 1 NatGeneration.flatCtors[1]).type)
    simpa only [probeNatSuccRuleTypeS_eq] using hRegistered
  have htowerLevel :
      (natSuccCaptureTower (field.lift (n + 1)) succShape
        zeroShape motiveShape (predTypeShape.lift (n + 1))
        (view.third.domain.lift (n + 1))
        (view.second.domain.lift (n + 1))
        (view.first.domain.lift (n + 1)) outTy).T.1 ≤ k + 4 := by
    change n + 5 ≤ k + 4
    omega
  have hRuleTypeK : LE_Interp.Witness ρ
      ((natSuccCaptureTower (field.lift (n + 1)) succShape
        zeroShape motiveShape (predTypeShape.lift (n + 1))
        (view.third.domain.lift (n + 1))
        (view.second.domain.lift (n + 1))
        (view.first.domain.lift (n + 1)) outTy).lift (k + 4)).T
      (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.type) :=
    hRuleType.mono (TShape.lift_eqv htowerLevel).1
  rw [← natSuccDirectIotaRule_capturePaths] at hdom
  have hshapeK := hdom.spine
  have producer : LR.DirectFixedHeadProducer Γ ρ mx my captureType
      hshapeK
      (headType := SExpr.mkInst [level]
        (natSuccDirectIotaRule univs).df.type)
      (outTy := outTy.lift k) := by
    exact hdom.producer hRuleTypeK
  have houtKNonbot : ¬(out.lift k).T ≤ TShape.bot := by
    intro hbotK
    exact houtBot ((TShape.lift_eqv hbase).2.trans hbotK)
  have hAK : (LRD Γ).TyDefEq A A (outTy.lift k) :=
    (LRD.TyDefEq.lift hbase hout.isType).2 hA
  have hhigh : (LRD Γ).DefEq
      ((NatGeneration.ruleRHS natRuleClosure
        probeNatFlatCtorSucc_lookup).applyS [level] mx)
      ((NatGeneration.ruleRHS natRuleClosure
        probeNatFlatCtorSucc_lookup).applyS [level] my)
      A (out.lift k) (outTy.lift k) := by
    exact hshapeK.directApplyRuleWithProducerSelfAdequacy
      (hX := hhead.fixedLowerWitness hR) producer houtKNonbot
      (by rw [natSuccDirectIotaRule_capturePaths]; simp)
      hspineX hAK convert (self (hhead.fixedLowerWitness hR))
      hheadK hstrat W
  exact (LRD.DefEq.lift hbase hout).1 hhigh

/--
info: 'Lean4Lean.SExpr.ParamsD0.natSuccIotaRHSDefEq_of_registeredViewDirectListed' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 probeNatRecTypeV_eq._native.native_decide.ax_1_1,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatSuccRuleTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms natSuccIotaRHSDefEq_of_registeredViewDirectListed

/-- Full generated Nat-successor RHS contract driven by recursive
self-adequacy.  Its only additional logical input is the guarded term upgrade
for the exact predecessor capture; `makeAlignment` incorporates that upgrade
into the synchronized telescope and retains the required registered-type
comparison. -/
theorem natSuccIotaRHSDefEq_of_selfAdequate
    (univs : Nat) (level : @SLevel (natParams univs))
    [semantic : @Params.Semantic (natParams univs)] :
    letI : Params := natParams univs
    ∀ {n : Nat} {Γ : List SExpr} {R : TShape → SExpr → Prop}
      {ρ : Valuation} {depth : Nat}
      {Δ : List SExpr} {σ σ' : Subst} {core : Bool}
      {mrec : (Pattern.varN (.const ``Nat.rec) 3).Path → TShape}
      {mctor : (Pattern.varN (.const ``Nat.succ) 1).Path → TShape}
      {out : WShape (n + 1)},
    (∀ {m M}, R m M → LE_Interp.Witness ρ m M) →
    LRD.FixedHeadConvertStep Γ →
    HasTypeStratifiedS Δ
      (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.rhs)
      (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.type)
      core depth →
    LR.DirectSubstWF Γ σ σ' Δ ρ →
    (∀ {root : TShape}
      (hX : LE_Interp.Witness ρ root
        (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.rhs)),
      LRD.SelfAdequateAt Γ hX depth) →
    (∀ {mx my captureType :
          (RecursorIotaPattern ``Nat.rec 3 ``Nat.succ 1).Path → SExpr}
        (H : LRS.CaptureDefEqAligned (n := n) (LR Γ)
          (mctor none) (mx natSuccPredPath) (my natSuccPredPath)
          (captureType natSuccPredPath)),
      LR.DirectTermCaptureDefEqAligned.Upgrade H) →
    (∀ {head : TShape}
        {mx my captureType :
          (RecursorIotaPattern ``Nat.rec 3 ``Nat.succ 1).Path → SExpr}
        {outTy : WShape (n + 1)}
        (_hhead : LE_Interp.Witness ρ head
          (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.rhs))
        (_htyped : LE_Interp.Witness.TypedRDeep (fun _ => True) ρ head
          (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.rhs)
          (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.type))
        (hshape : LE_Interp.RHS.ShapeSpine (Sum.elim mrec mctor) head
          (natSuccDirectIotaRule univs).capturePaths out.T)
        (_hcapDirect : ∀ path,
          LR.DirectTermCaptureDefEqAligned.AtSomeLevel Γ
            (Sum.elim mrec mctor path) (mx path) (my path)
            (captureType path))
        (_hout : out.HasType outTy),
      (¬out.T ≤ TShape.bot) →
      LR.DirectFixedHeadAlignedTyping Γ ρ mx my captureType
        (P := fun _ => True)
        (body := SExpr.mkInst [level]
          (natSuccDirectIotaRule univs).df.rhs)
        (headType := SExpr.mkInst [level]
          (natSuccDirectIotaRule univs).df.type)
        (outTy := outTy) hshape) →
    LRD.IotaRHSDefEq (Γ := Γ) (LE_Interp.Lower R) [level]
      mrec mctor
      (NatGeneration.ruleRHS natRuleClosure
          probeNatFlatCtorSucc_lookup,
        NatGeneration.ruleCheck natRuleClosure
          (List.mem_of_getElem? probeNatFlatCtorSucc_lookup))
      (natSuccDirectIotaRule univs) out := by
  letI : Params := natParams univs
  letI : Params.Semantic := semantic
  intro n Γ R ρ depth Δ σ σ' core mrec mctor out hR convert hstrat W
    self upgradePred makeAlignment
  apply LRD.IotaRHSDefEq.of_nonbotWitness hR
  intro head mx my captureType A outTy hhead _hstrong hshape _htyped
    hspineX _hspineY hcap hout hA
  by_cases houtBot : out.T ≤ TShape.bot
  · have houtEq : out = .bot := TShape.le_bot.1 houtBot
    subst out
    exact LRD.DefEq.bot hout.isType
  · have hcapDirect : ∀ path,
        LR.DirectTermCaptureDefEqAligned.AtSomeLevel Γ
          (Sum.elim mrec mctor path) (mx path) (my path)
          (captureType path) := by
      intro path
      cases path with
      | inl p => exact (hcap (.inl p)).atSomeLevel.toTerm
      | inr p =>
        cases p with
        | none => exact (upgradePred (hcap natSuccPredPath)).atSomeLevel
        | some p => exact nomatch p
    have hstrongΔ : IsDefEqStrong Δ
        (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.rhs)
        (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.rhs)
        (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.type) :=
      (natSuccDirectIotaRule univs).rhsStrong [level]
    have htyped := hhead.typedRDeepTrue_of_strong hstrongΔ W.fits
    have aligned :=
      makeAlignment hhead htyped hshape hcapDirect hout houtBot
    exact natSuccRuleRHS_directOutput_of_selfAdequate univs level
      (hX := hhead) hshape
      aligned.producer
      houtBot hspineX hA convert (self hhead) TShape.LE.rfl hstrat W

/--
info: 'Lean4Lean.SExpr.ParamsD0.natZeroRuleRHS_directOutput' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms natZeroRuleRHS_directOutput

/--
info: 'Lean4Lean.SExpr.ParamsD0.natZeroIotaRHSDefEq_of_headSelf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms natZeroIotaRHSDefEq_of_headSelf

/--
info: 'Lean4Lean.SExpr.ParamsD0.natSuccRuleRHS_directOutput' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms natSuccRuleRHS_directOutput

/--
info: 'Lean4Lean.SExpr.ParamsD0.natSuccIotaRHSDefEq_of_headSelf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms natSuccIotaRHSDefEq_of_headSelf

/--
info: 'Lean4Lean.SExpr.ParamsD0.natZeroRuleRHS_directOutput_of_selfAdequate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms natZeroRuleRHS_directOutput_of_selfAdequate

/--
info: 'Lean4Lean.SExpr.ParamsD0.natSuccRuleRHS_directOutput_of_selfAdequate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms natSuccRuleRHS_directOutput_of_selfAdequate

/--
info: 'Lean4Lean.SExpr.ParamsD0.natZeroIotaRHSDefEq_of_selfAdequate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms natZeroIotaRHSDefEq_of_selfAdequate

/--
info: 'Lean4Lean.SExpr.ParamsD0.natZeroIotaRHSDefEq_of_registeredView' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms natZeroIotaRHSDefEq_of_registeredView

/--
info: 'Lean4Lean.SExpr.ParamsD0.natSuccIotaRHSDefEq_of_selfAdequate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms natSuccIotaRHSDefEq_of_selfAdequate

/-- Close one native exact Nat-zero constructor leaf in the guarded relation.

The registered descriptor is canonicalized internally, so the consumer sees
only the exact constructor leaf, the proof-relevant fixed-body self relation,
and guarded conversion at the generated path-spine's actual conversion
edges.  The generated RHS relation is produced, not assumed. -/
theorem natZeroIotaDefEq_of_ctorExactAt
    (univs : Nat) (level : @SLevel (natParams univs))
    [semantic : @Params.Semantic (natParams univs)] :
    letI : Params := natParams univs
    ∀ {n : Nat} {Γ : List SExpr} {R : TShape → SExpr → Prop}
      {ρ : Valuation}
      {recShapes : List (WShape (n + 1))}
      {ctorShapes : List (WShape n)}
      {mrec : (Pattern.varN (.const ``Nat.rec) 3).Path → TShape}
      {mctor : (Pattern.varN (.const ``Nat.zero) 0).Path → TShape}
      {recXs recYs : List SExpr} {majorX majorY recHeadType A : SExpr}
      {out outTy : WShape (n + 1)}
      {hwf : IsStruct ``Nat.zero → WShape.ListNonZero ctorShapes.reverse},
    Ctx.WF Γ →
    LE_Interp.Matches (n := n + 1)
      (Pattern.varN (.const ``Nat.rec) 3) ``Nat.rec recShapes mrec →
    LE_Interp.Matches (n := n)
      (Pattern.varN (.const ``Nat.zero) 0) ``Nat.zero ctorShapes mctor →
    LE_Interp.RHS [level] (Sum.elim mrec mctor)
      (LE_Interp.Lower R) out.T
      (NatGeneration.ruleRHS natRuleClosure
        probeNatFlatCtorZero_lookup) →
    (∀ {m M}, R m M → LE_Interp.Witness ρ m M) →
    LRS.CtorExact Γ (LR Γ) majorX majorY
      (.ctor ``Nat.zero ctorShapes.reverse hwf) →
    LR.DirectPatternLeafSpine Γ (LRD Γ) recHeadType
      (majorX :: recXs) (majorY :: recYs)
      ((.ctor ``Nat.zero ctorShapes.reverse hwf) :: recShapes)
      A out outTy →
    IsDefEq Γ (.const ``Nat.rec [level]) (.const ``Nat.rec [level])
      recHeadType →
    out.HasType outTy →
    (LRD Γ).TyDefEq A A outTy →
    LRD.FixedHeadConvertStep Γ →
    (∀ {head : TShape},
      LE_Interp.Witness ρ head
          (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.rhs) →
      ∀ {headLevel : Nat} {headElem headElemTy : WShape headLevel},
        headElem.T ≤ head → headElem.HasType headElemTy →
        (LRD Γ).DefEq
          (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.rhs)
          (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.rhs)
          (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.type)
          headElem headElemTy) →
    (LRD Γ).DefEq
      ((recXs.foldr (fun (a f : SExpr) => f.app a)
        (.const ``Nat.rec [level])).app majorX)
      ((recYs.foldr (fun (a f : SExpr) => f.app a)
        (.const ``Nat.rec [level])).app majorY)
      A out outTy := by
  letI : Params := natParams univs
  letI : Params.Semantic := semantic
  intro n Γ R ρ recShapes ctorShapes mrec mctor recXs recYs majorX majorY
    recHeadType A out outTy hwf hΓ hmf hma hrhs hR leaf hleaf hrecHead
    hout hA convert headSelf
  apply LRD.iotaDefEq_of_ctorExactAt hΓ
      (natZeroDirectIotaRule univs).pat hmf hma hrhs leaf hleaf
      hrecHead hout hA
  intro rule
  rw [natIotaRule_ext univs rule (natZeroDirectIotaRule univs)]
  exact natZeroIotaRHSDefEq_of_headSelf univs level hR convert headSelf

/-- Close one native exact Nat-successor constructor leaf in the guarded
relation.  Relative to the zero leaf, its sole extra input is the guarded
term upgrade of the exact predecessor capture selected by that leaf. -/
theorem natSuccIotaDefEq_of_ctorExactAt
    (univs : Nat) (level : @SLevel (natParams univs))
    [semantic : @Params.Semantic (natParams univs)] :
    letI : Params := natParams univs
    ∀ {n : Nat} {Γ : List SExpr} {R : TShape → SExpr → Prop}
      {ρ : Valuation}
      {recShapes : List (WShape (n + 1))}
      {ctorShapes : List (WShape n)}
      {mrec : (Pattern.varN (.const ``Nat.rec) 3).Path → TShape}
      {mctor : (Pattern.varN (.const ``Nat.succ) 1).Path → TShape}
      {recXs recYs : List SExpr} {majorX majorY recHeadType A : SExpr}
      {out outTy : WShape (n + 1)}
      {hwf : IsStruct ``Nat.succ → WShape.ListNonZero ctorShapes.reverse},
    Ctx.WF Γ →
    LE_Interp.Matches (n := n + 1)
      (Pattern.varN (.const ``Nat.rec) 3) ``Nat.rec recShapes mrec →
    LE_Interp.Matches (n := n)
      (Pattern.varN (.const ``Nat.succ) 1) ``Nat.succ ctorShapes mctor →
    LE_Interp.RHS [level] (Sum.elim mrec mctor)
      (LE_Interp.Lower R) out.T
      (NatGeneration.ruleRHS natRuleClosure
        probeNatFlatCtorSucc_lookup) →
    (∀ {m M}, R m M → LE_Interp.Witness ρ m M) →
    LRS.CtorExact Γ (LR Γ) majorX majorY
      (.ctor ``Nat.succ ctorShapes.reverse hwf) →
    LR.DirectPatternLeafSpine Γ (LRD Γ) recHeadType
      (majorX :: recXs) (majorY :: recYs)
      ((.ctor ``Nat.succ ctorShapes.reverse hwf) :: recShapes)
      A out outTy →
    IsDefEq Γ (.const ``Nat.rec [level]) (.const ``Nat.rec [level])
      recHeadType →
    out.HasType outTy →
    (LRD Γ).TyDefEq A A outTy →
    LRD.FixedHeadConvertStep Γ →
    (∀ {head : TShape},
      LE_Interp.Witness ρ head
          (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.rhs) →
      ∀ {headLevel : Nat} {headElem headElemTy : WShape headLevel},
        headElem.T ≤ head → headElem.HasType headElemTy →
        (LRD Γ).DefEq
          (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.rhs)
          (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.rhs)
          (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.type)
          headElem headElemTy) →
    (∀ {mx my captureType :
          (RecursorIotaPattern ``Nat.rec 3 ``Nat.succ 1).Path → SExpr}
        (H : LRS.CaptureDefEqAligned (n := n) (LR Γ)
          (mctor none) (mx natSuccPredPath) (my natSuccPredPath)
          (captureType natSuccPredPath)),
      LR.DirectTermCaptureDefEqAligned.Upgrade H) →
    (LRD Γ).DefEq
      ((recXs.foldr (fun (a f : SExpr) => f.app a)
        (.const ``Nat.rec [level])).app majorX)
      ((recYs.foldr (fun (a f : SExpr) => f.app a)
        (.const ``Nat.rec [level])).app majorY)
      A out outTy := by
  letI : Params := natParams univs
  letI : Params.Semantic := semantic
  intro n Γ R ρ recShapes ctorShapes mrec mctor recXs recYs majorX majorY
    recHeadType A out outTy hwf hΓ hmf hma hrhs hR leaf hleaf hrecHead
    hout hA convert headSelf upgradePred
  apply LRD.iotaDefEq_of_ctorExactAt hΓ
      (natSuccDirectIotaRule univs).pat hmf hma hrhs leaf hleaf
      hrecHead hout hA
  intro rule
  rw [natIotaRule_ext univs rule (natSuccDirectIotaRule univs)]
  exact natSuccIotaRHSDefEq_of_headSelf univs level
    hR convert headSelf upgradePred

/-- Close a native exact Nat-zero leaf from recursive guarded
self-adequacy and the synchronized direct fixed-head producer.

Descriptor canonicalization remains internal.  Compared with
`natZeroIotaDefEq_of_ctorExactAt`, the arbitrary fixed-body `headSelf`
callback is replaced by the literal evaluator-indexed self-adequacy family,
its direct substitution, and `makeAlignment`, which exposes the dominance
tower's comparison to the synchronized registered-type witness. -/
theorem natZeroIotaDefEq_of_ctorExactAt_selfAdequate
    (univs : Nat) (level : @SLevel (natParams univs))
    [semantic : @Params.Semantic (natParams univs)] :
    letI : Params := natParams univs
    ∀ {n : Nat} {Γ : List SExpr} {R : TShape → SExpr → Prop}
      {ρ : Valuation} {depth : Nat}
      {Δ : List SExpr} {σ σ' : Subst} {core : Bool}
      {recShapes : List (WShape (n + 1))}
      {ctorShapes : List (WShape n)}
      {mrec : (Pattern.varN (.const ``Nat.rec) 3).Path → TShape}
      {mctor : (Pattern.varN (.const ``Nat.zero) 0).Path → TShape}
      {recXs recYs : List SExpr} {majorX majorY recHeadType A : SExpr}
      {out outTy : WShape (n + 1)}
      {hwf : IsStruct ``Nat.zero → WShape.ListNonZero ctorShapes.reverse},
    Ctx.WF Γ →
    LE_Interp.Matches (n := n + 1)
      (Pattern.varN (.const ``Nat.rec) 3) ``Nat.rec recShapes mrec →
    LE_Interp.Matches (n := n)
      (Pattern.varN (.const ``Nat.zero) 0) ``Nat.zero ctorShapes mctor →
    LE_Interp.RHS [level] (Sum.elim mrec mctor)
      (LE_Interp.Lower R) out.T
      (NatGeneration.ruleRHS natRuleClosure
        probeNatFlatCtorZero_lookup) →
    (∀ {m M}, R m M → LE_Interp.Witness ρ m M) →
    LRS.CtorExact Γ (LR Γ) majorX majorY
      (.ctor ``Nat.zero ctorShapes.reverse hwf) →
    LR.DirectPatternLeafSpine Γ (LRD Γ) recHeadType
      (majorX :: recXs) (majorY :: recYs)
      ((.ctor ``Nat.zero ctorShapes.reverse hwf) :: recShapes)
      A out outTy →
    IsDefEq Γ (.const ``Nat.rec [level]) (.const ``Nat.rec [level])
      recHeadType →
    out.HasType outTy →
    (LRD Γ).TyDefEq A A outTy →
    LRD.FixedHeadConvertStep Γ →
    HasTypeStratifiedS Δ
      (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.rhs)
      (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.type)
      core depth →
    LR.DirectSubstWF Γ σ σ' Δ ρ →
    (∀ {root : TShape}
      (hX : LE_Interp.Witness ρ root
        (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.rhs)),
      LRD.SelfAdequateAt Γ hX depth) →
    (∀ {head : TShape}
        {mx my captureType :
          (RecursorIotaPattern ``Nat.rec 3 ``Nat.zero 0).Path → SExpr}
        {outTyP : WShape (n + 1)}
        (_hhead : LE_Interp.Witness ρ head
          (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.rhs))
        (_htyped : LE_Interp.Witness.TypedRDeep (fun _ => True) ρ head
          (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.rhs)
          (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.type))
        (hshape : LE_Interp.RHS.ShapeSpine (Sum.elim mrec mctor) head
          (natZeroDirectIotaRule univs).capturePaths out.T)
        (_hcapDirect : ∀ path,
          LR.DirectTermCaptureDefEqAligned.AtSomeLevel Γ
            (Sum.elim mrec mctor path) (mx path) (my path)
            (captureType path))
        (_hout : out.HasType outTyP),
      (¬out.T ≤ TShape.bot) →
      LR.DirectFixedHeadAlignedTyping Γ ρ mx my captureType
        (P := fun _ => True)
        (body := SExpr.mkInst [level]
          (natZeroDirectIotaRule univs).df.rhs)
        (headType := SExpr.mkInst [level]
          (natZeroDirectIotaRule univs).df.type)
        (outTy := outTyP) hshape) →
    (LRD Γ).DefEq
      ((recXs.foldr (fun (a f : SExpr) => f.app a)
        (.const ``Nat.rec [level])).app majorX)
      ((recYs.foldr (fun (a f : SExpr) => f.app a)
        (.const ``Nat.rec [level])).app majorY)
      A out outTy := by
  letI : Params := natParams univs
  letI : Params.Semantic := semantic
  intro n Γ R ρ depth Δ σ σ' core recShapes ctorShapes mrec mctor
    recXs recYs majorX majorY recHeadType A out outTy hwf hΓ hmf hma
    hrhs hR leaf hleaf hrecHead hout hA convert hstrat W self makeAlignment
  apply LRD.iotaDefEq_of_ctorExactAt hΓ
      (natZeroDirectIotaRule univs).pat hmf hma hrhs leaf hleaf
      hrecHead hout hA
  intro rule
  rw [natIotaRule_ext univs rule (natZeroDirectIotaRule univs)]
  exact natZeroIotaRHSDefEq_of_selfAdequate univs level
    hR convert hstrat W self makeAlignment

/-- Close the exact registered Nat-zero leaf directly from recursive
self-adequacy.

Unlike the compatibility theorem above, this boundary consumes the literal
registered `Nat.rec` trace.  Its `FourView.recArgsListed` payload drives the
listed iota materializer, while the same view supplies the generated rule
type witness used by `natZeroIotaRHSDefEq_of_registeredView`.  No external
alignment or completed RHS relation remains. -/
theorem natZeroIotaDefEq_of_registeredCtorExactAt_selfAdequate
    (univs : Nat) (level : @SLevel (natParams univs))
    [semantic : @Params.Semantic (natParams univs)] :
    letI : Params := natParams univs
    ∀ {n : Nat} {Γ : List SExpr} {R : TShape → SExpr → Prop}
      {ρ : Valuation} {depth : Nat}
      {Δ : List SExpr} {σ σ' : Subst} {core : Bool}
      {recShapes : List (WShape (n + 1))}
      {ctorShapes : List (WShape n)}
      {mrec : (Pattern.varN (.const ``Nat.rec) 3).Path → TShape}
      {mctor : (Pattern.varN (.const ``Nat.zero) 0).Path → TShape}
      {recXs recYs : List SExpr} {majorX majorY A : SExpr}
      {out outTy : WShape (n + 1)}
      {hwf : IsStruct ``Nat.zero → WShape.ListNonZero ctorShapes.reverse},
    Ctx.WF Γ →
    LE_Interp.Matches (n := n + 1)
      (Pattern.varN (.const ``Nat.rec) 3) ``Nat.rec recShapes mrec →
    LE_Interp.Matches (n := n)
      (Pattern.varN (.const ``Nat.zero) 0) ``Nat.zero ctorShapes mctor →
    LE_Interp.RHS [level] (Sum.elim mrec mctor)
      (LE_Interp.Lower R) out.T
      (NatGeneration.ruleRHS natRuleClosure
        probeNatFlatCtorZero_lookup) →
    (∀ {m M}, R m M → LE_Interp.Witness ρ m M) →
    LRS.CtorExact Γ (LR Γ) majorX majorY
      (.ctor ``Nat.zero ctorShapes.reverse hwf) →
    LR.DirectPatternLeafSpine Γ (LRD Γ)
      (SExpr.mkInst [level]
        (VInductDecl.recConst 0 ``Nat 0 InductiveFixtures.natType).type)
      (majorX :: recXs) (majorY :: recYs)
      ((.ctor ``Nat.zero ctorShapes.reverse hwf) :: recShapes)
      A out outTy →
    LR.DirectRegisteredTypeTrace Γ ρ
      (SExpr.mkInst [level]
        (VInductDecl.recConst 0 ``Nat 0 InductiveFixtures.natType).type)
      (majorX :: recXs) (majorY :: recYs)
      ((.ctor' ``Nat.zero ctorShapes.reverse) :: recShapes) A outTy →
    IsDefEq Γ (.const ``Nat.rec [level]) (.const ``Nat.rec [level])
      (SExpr.mkInst [level]
        (VInductDecl.recConst 0 ``Nat 0 InductiveFixtures.natType).type) →
    out.HasType outTy →
    (LRD Γ).TyDefEq A A outTy →
    LRD.FixedHeadConvertStep Γ →
    HasTypeStratifiedS Δ
      (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.rhs)
      (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.type)
      core depth →
    LR.DirectSubstWF Γ σ σ' Δ ρ →
    (∀ {root : TShape}
      (hX : LE_Interp.Witness ρ root
        (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.rhs)),
      LRD.SelfAdequateAt Γ hX depth) →
    (LRD Γ).DefEq
      ((recXs.foldr (fun (a f : SExpr) => f.app a)
        (.const ``Nat.rec [level])).app majorX)
      ((recYs.foldr (fun (a f : SExpr) => f.app a)
        (.const ``Nat.rec [level])).app majorY)
      A out outTy := by
  letI : Params := natParams univs
  letI : Params.Semantic := semantic
  intro n Γ R ρ depth Δ σ σ' core recShapes ctorShapes mrec mctor
    recXs recYs majorX majorY A out outTy hwf hΓ hmf hma hrhs hR
    leaf hleaf trace hrecHead hout hA convert hstrat W self
  have hctorLen : ctorShapes.length = 0 := hma.varN_length
  have hctorNil : ctorShapes = [] := List.length_eq_zero_iff.mp hctorLen
  subst ctorShapes
  have hrecShapesLen : recShapes.length = 3 := hmf.varN_length
  obtain ⟨succShape, zeroShape, motiveShape, rfl⟩ :
      ∃ succShape zeroShape motiveShape,
        recShapes = [succShape, zeroShape, motiveShape] :=
    ⟨recShapes[0], recShapes[1], recShapes[2],
      List.eq_getElem_of_length_eq_three recShapes hrecShapesLen⟩
  have hlens := trace.directArgs.lengths
  have hrecXsLen : recXs.length = 3 := Nat.succ.inj hlens.1
  have hrecYsLen : recYs.length = 3 := Nat.succ.inj hlens.2
  obtain ⟨succX, zeroX, motiveX, rfl⟩ :
      ∃ succX zeroX motiveX, recXs = [succX, zeroX, motiveX] :=
    ⟨recXs[0], recXs[1], recXs[2],
      List.eq_getElem_of_length_eq_three recXs hrecXsLen⟩
  obtain ⟨succY, zeroY, motiveY, rfl⟩ :
      ∃ succY zeroY motiveY, recYs = [succY, zeroY, motiveY] :=
    ⟨recYs[0], recYs[1], recYs[2],
      List.eq_getElem_of_length_eq_three recYs hrecYsLen⟩
  let view := trace.fourView
  have hRuleType : LE_Interp.Witness ρ
      (view.sparsePrefix outTy).T (probeNatZeroRuleType univs level) :=
    natZeroRegisteredRuleTypeSemanticWitness
      (n := n) (Γ := Γ) (ρ := ρ) (level := level)
      (outTy := outTy) univs trace view
  have hDirectRuleType : LE_Interp.Witness ρ
      (view.sparsePrefix outTy).T
      (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.type) := by
    change @LE_Interp.Witness (natParams univs) ρ
      (view.sparsePrefix outTy).T
      (SExpr.mkInst [level]
        (NatGeneration.rule 0 NatGeneration.flatCtors[0]).type)
    simpa only [probeNatZeroRuleTypeS_eq] using hRuleType
  apply LRD.iotaDefEq_of_ctorExactListedAt hΓ
      (natZeroDirectIotaRule univs).pat hmf hma hrhs leaf hleaf
      view.recArgsListed hrecHead hout hA
  intro rule
  rw [natIotaRule_ext univs rule (natZeroDirectIotaRule univs)]
  exact natZeroIotaRHSDefEq_of_registeredView univs level view
    hR convert hstrat W self hDirectRuleType

/-- Close the exact registered Nat-successor leaf from recursive guarded
self-adequacy and one canonical predecessor capture.

The constructor match fixes the unique field shape before the listed action
materializer runs.  The predecessor producer therefore targets that literal
one-level lift and `indTy`; the registered-view RHS theorem constructs every
remaining alignment and the final generated relation. -/
theorem natSuccIotaDefEq_of_registeredCtorExactAt_selfAdequate
    (univs : Nat) (level : @SLevel (natParams univs))
    [semantic : @Params.Semantic (natParams univs)] :
    letI : Params := natParams univs
    ∀ {n : Nat} {Γ : List SExpr} {R : TShape → SExpr → Prop}
      {ρ : Valuation} {depth : Nat}
      {Δ : List SExpr} {σ σ' : Subst} {core : Bool}
      {recShapes : List (WShape (n + 1))}
      {ctorShapes : List (WShape n)}
      {mrec : (Pattern.varN (.const ``Nat.rec) 3).Path → TShape}
      {mctor : (Pattern.varN (.const ``Nat.succ) 1).Path → TShape}
      {recXs recYs : List SExpr} {majorX majorY A : SExpr}
      {out outTy : WShape (n + 1)}
      {hwf : IsStruct ``Nat.succ → WShape.ListNonZero ctorShapes.reverse},
    Ctx.WF Γ →
    LE_Interp.Matches (n := n + 1)
      (Pattern.varN (.const ``Nat.rec) 3) ``Nat.rec recShapes mrec →
    LE_Interp.Matches (n := n)
      (Pattern.varN (.const ``Nat.succ) 1) ``Nat.succ ctorShapes mctor →
    LE_Interp.RHS [level] (Sum.elim mrec mctor)
      (LE_Interp.Lower R) out.T
      (NatGeneration.ruleRHS natRuleClosure
        probeNatFlatCtorSucc_lookup) →
    (∀ {m M}, R m M → LE_Interp.Witness ρ m M) →
    LRS.CtorExact Γ (LR Γ) majorX majorY
      (.ctor ``Nat.succ ctorShapes.reverse hwf) →
    LR.DirectPatternLeafSpine Γ (LRD Γ)
      (SExpr.mkInst [level]
        (VInductDecl.recConst 0 ``Nat 0 InductiveFixtures.natType).type)
      (majorX :: recXs) (majorY :: recYs)
      ((.ctor ``Nat.succ ctorShapes.reverse hwf) :: recShapes)
      A out outTy →
    LR.DirectRegisteredTypeTrace Γ ρ
      (SExpr.mkInst [level]
        (VInductDecl.recConst 0 ``Nat 0 InductiveFixtures.natType).type)
      (majorX :: recXs) (majorY :: recYs)
      ((.ctor' ``Nat.succ ctorShapes.reverse) :: recShapes) A outTy →
    IsDefEq Γ (.const ``Nat.rec [level]) (.const ``Nat.rec [level])
      (SExpr.mkInst [level]
        (VInductDecl.recConst 0 ``Nat 0 InductiveFixtures.natType).type) →
    out.HasType outTy →
    (LRD Γ).TyDefEq A A outTy →
    LRD.FixedHeadConvertStep Γ →
    HasTypeStratifiedS Δ
      (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.rhs)
      (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.type)
      core depth →
    LR.DirectSubstWF Γ σ σ' Δ ρ →
    (∀ {root : TShape}
      (hX : LE_Interp.Witness ρ root
        (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.rhs)),
      LRD.SelfAdequateAt Γ hX depth) →
    (∀ {field : WShape n}, ctorShapes = [field] →
      ∀ {mx my captureType :
          (RecursorIotaPattern ``Nat.rec 3 ``Nat.succ 1).Path → SExpr},
      LRS.CaptureDefEqAligned (n := n) (LR Γ)
          (mctor none) (mx natSuccPredPath) (my natSuccPredPath)
          (captureType natSuccPredPath) →
      LR.DirectTermCaptureDefEqAligned.AtShapes (LRD Γ)
        (mctor none) (mx natSuccPredPath) (my natSuccPredPath)
        (captureType natSuccPredPath) (field.lift (n + 1)) .indTy) →
    (LRD Γ).DefEq
      ((recXs.foldr (fun (a f : SExpr) => f.app a)
        (.const ``Nat.rec [level])).app majorX)
      ((recYs.foldr (fun (a f : SExpr) => f.app a)
        (.const ``Nat.rec [level])).app majorY)
      A out outTy := by
  letI : Params := natParams univs
  letI : Params.Semantic := semantic
  intro n Γ R ρ depth Δ σ σ' core recShapes ctorShapes mrec mctor
    recXs recYs majorX majorY A out outTy hwf hΓ hmf hma hrhs hR
    leaf hleaf trace hrecHead hout hA convert hstrat W self predExact
  have hctorLen : ctorShapes.length = 1 := hma.varN_length
  obtain ⟨field, rfl⟩ := List.length_eq_one_iff.mp hctorLen
  have hrecShapesLen : recShapes.length = 3 := hmf.varN_length
  obtain ⟨succShape, zeroShape, motiveShape, rfl⟩ :
      ∃ succShape zeroShape motiveShape,
        recShapes = [succShape, zeroShape, motiveShape] :=
    ⟨recShapes[0], recShapes[1], recShapes[2],
      List.eq_getElem_of_length_eq_three recShapes hrecShapesLen⟩
  have hlens := trace.directArgs.lengths
  have hrecXsLen : recXs.length = 3 := Nat.succ.inj hlens.1
  have hrecYsLen : recYs.length = 3 := Nat.succ.inj hlens.2
  obtain ⟨succX, zeroX, motiveX, rfl⟩ :
      ∃ succX zeroX motiveX, recXs = [succX, zeroX, motiveX] :=
    ⟨recXs[0], recXs[1], recXs[2],
      List.eq_getElem_of_length_eq_three recXs hrecXsLen⟩
  obtain ⟨succY, zeroY, motiveY, rfl⟩ :
      ∃ succY zeroY motiveY, recYs = [succY, zeroY, motiveY] :=
    ⟨recYs[0], recYs[1], recYs[2],
      List.eq_getElem_of_length_eq_three recYs hrecYsLen⟩
  let view := trace.fourView
  apply LRD.iotaDefEq_of_ctorExactListedAt hΓ
      (natSuccDirectIotaRule univs).pat hmf hma hrhs leaf hleaf
      view.recArgsListed hrecHead hout hA
  intro rule
  rw [natIotaRule_ext univs rule (natSuccDirectIotaRule univs)]
  exact natSuccIotaRHSDefEq_of_registeredView univs level view
    hR convert hstrat W self (predExact rfl)

/--
info: 'Lean4Lean.SExpr.ParamsD0.natSuccIotaDefEq_of_registeredCtorExactAt_selfAdequate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 probeNatGeneratedRuleSucc_lookup._native.native_decide.ax_1_1,
 probeNatGeneratedRuleZero_lookup._native.native_decide.ax_1_1,
 probeNatRecTypeV_eq._native.native_decide.ax_1_1,
 probeNatRuleRhs_ne._native.native_decide.ax_1_1,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatSuccRuleTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms natSuccIotaDefEq_of_registeredCtorExactAt_selfAdequate

/-- Close the exact registered Nat-successor leaf while preserving the
proof-relevant predecessor shapes selected by the listed action.

The constructor match still identifies the unique native field, but the
recursive producer is asked for semantic Nat typing and direct adequacy at
the selected capture's own element/type shapes.  No predecessor re-selection
or legacy type-functionality principle is required. -/
theorem natSuccIotaDefEq_of_registeredCtorExactAt_selfAdequateAligned
    (univs : Nat) (level : @SLevel (natParams univs))
    [semantic : @Params.Semantic (natParams univs)] :
    letI : Params := natParams univs
    ∀ {n : Nat} {Γ : List SExpr} {R : TShape → SExpr → Prop}
      {ρ : Valuation} {depth : Nat}
      {Δ : List SExpr} {σ σ' : Subst} {core : Bool}
      {recShapes : List (WShape (n + 1))}
      {ctorShapes : List (WShape n)}
      {mrec : (Pattern.varN (.const ``Nat.rec) 3).Path → TShape}
      {mctor : (Pattern.varN (.const ``Nat.succ) 1).Path → TShape}
      {recXs recYs : List SExpr} {majorX majorY A : SExpr}
      {out outTy : WShape (n + 1)}
      {hwf : IsStruct ``Nat.succ → WShape.ListNonZero ctorShapes.reverse},
    Ctx.WF Γ →
    LE_Interp.Matches (n := n + 1)
      (Pattern.varN (.const ``Nat.rec) 3) ``Nat.rec recShapes mrec →
    LE_Interp.Matches (n := n)
      (Pattern.varN (.const ``Nat.succ) 1) ``Nat.succ ctorShapes mctor →
    LE_Interp.RHS [level] (Sum.elim mrec mctor)
      (LE_Interp.Lower R) out.T
      (NatGeneration.ruleRHS natRuleClosure
        probeNatFlatCtorSucc_lookup) →
    (∀ {m M}, R m M → LE_Interp.Witness ρ m M) →
    LRS.CtorExact Γ (LR Γ) majorX majorY
      (.ctor ``Nat.succ ctorShapes.reverse hwf) →
    LR.DirectPatternLeafSpine Γ (LRD Γ)
      (SExpr.mkInst [level]
        (VInductDecl.recConst 0 ``Nat 0 InductiveFixtures.natType).type)
      (majorX :: recXs) (majorY :: recYs)
      ((.ctor ``Nat.succ ctorShapes.reverse hwf) :: recShapes)
      A out outTy →
    LR.DirectRegisteredTypeTrace Γ ρ
      (SExpr.mkInst [level]
        (VInductDecl.recConst 0 ``Nat 0 InductiveFixtures.natType).type)
      (majorX :: recXs) (majorY :: recYs)
      ((.ctor' ``Nat.succ ctorShapes.reverse) :: recShapes) A outTy →
    IsDefEq Γ (.const ``Nat.rec [level]) (.const ``Nat.rec [level])
      (SExpr.mkInst [level]
        (VInductDecl.recConst 0 ``Nat 0 InductiveFixtures.natType).type) →
    out.HasType outTy →
    (LRD Γ).TyDefEq A A outTy →
    LRD.FixedHeadConvertStep Γ →
    HasTypeStratifiedS Δ
      (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.rhs)
      (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.type)
      core depth →
    LR.DirectSubstWF Γ σ σ' Δ ρ →
    (∀ {root : TShape}
      (hX : LE_Interp.Witness ρ root
        (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.rhs)),
      LRD.SelfAdequateAt Γ hX depth) →
    (∀ {field : WShape n}, ctorShapes = [field] →
      ∀ {mx my captureType :
          (RecursorIotaPattern ``Nat.rec 3 ``Nat.succ 1).Path → SExpr},
      ∀ H : LRS.CaptureDefEqAligned (n := n) (LR Γ)
          (mctor none) (mx natSuccPredPath) (my natSuccPredPath)
          (captureType natSuccPredPath),
      NatSuccPredCaptureCoherent ρ H) →
    (LRD Γ).DefEq
      ((recXs.foldr (fun (a f : SExpr) => f.app a)
        (.const ``Nat.rec [level])).app majorX)
      ((recYs.foldr (fun (a f : SExpr) => f.app a)
        (.const ``Nat.rec [level])).app majorY)
      A out outTy := by
  letI : Params := natParams univs
  letI : Params.Semantic := semantic
  intro n Γ R ρ depth Δ σ σ' core recShapes ctorShapes mrec mctor
    recXs recYs majorX majorY A out outTy hwf hΓ hmf hma hrhs hR
    leaf hleaf trace hrecHead hout hA convert hstrat W self predExact
  have hctorLen : ctorShapes.length = 1 := hma.varN_length
  obtain ⟨field, rfl⟩ := List.length_eq_one_iff.mp hctorLen
  have hmctor : mctor none = field.T := by
    cases hma with
    | var _ => rfl
  have hrecShapesLen : recShapes.length = 3 := hmf.varN_length
  obtain ⟨succShape, zeroShape, motiveShape, rfl⟩ :
      ∃ succShape zeroShape motiveShape,
        recShapes = [succShape, zeroShape, motiveShape] :=
    ⟨recShapes[0], recShapes[1], recShapes[2],
      List.eq_getElem_of_length_eq_three recShapes hrecShapesLen⟩
  have hlens := trace.directArgs.lengths
  have hrecXsLen : recXs.length = 3 := Nat.succ.inj hlens.1
  have hrecYsLen : recYs.length = 3 := Nat.succ.inj hlens.2
  obtain ⟨succX, zeroX, motiveX, rfl⟩ :
      ∃ succX zeroX motiveX, recXs = [succX, zeroX, motiveX] :=
    ⟨recXs[0], recXs[1], recXs[2],
      List.eq_getElem_of_length_eq_three recXs hrecXsLen⟩
  obtain ⟨succY, zeroY, motiveY, rfl⟩ :
      ∃ succY zeroY motiveY, recYs = [succY, zeroY, motiveY] :=
    ⟨recYs[0], recYs[1], recYs[2],
      List.eq_getElem_of_length_eq_three recYs hrecYsLen⟩
  let view := trace.fourView
  apply LRD.iotaDefEq_of_ctorExactListedAt hΓ
      (natSuccDirectIotaRule univs).pat hmf hma hrhs leaf hleaf
      view.recArgsListed hrecHead hout hA
  intro rule
  rw [natIotaRule_ext univs rule (natSuccDirectIotaRule univs)]
  exact natSuccIotaRHSDefEq_of_registeredViewAligned univs level view
    hmctor hR convert hstrat W self (predExact rfl)

/--
info: 'Lean4Lean.SExpr.ParamsD0.natSuccIotaDefEq_of_registeredCtorExactAt_selfAdequateAligned' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 probeNatGeneratedRuleSucc_lookup._native.native_decide.ax_1_1,
 probeNatGeneratedRuleZero_lookup._native.native_decide.ax_1_1,
 probeNatRecTypeV_eq._native.native_decide.ax_1_1,
 probeNatRuleRhs_ne._native.native_decide.ax_1_1,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatSuccRuleTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms natSuccIotaDefEq_of_registeredCtorExactAt_selfAdequateAligned

/-- Close every framed native link of the registered Nat-zero major.

`CtorFrame.shape_ctor` preserves the zero head and its nullary arity.  After
that normalization the ambient framed relation has no constructor fields
left to transport: the raw head/spine certificates feed the listed action
materializer directly.  `LastPair.fullXAt`/`fullYAt` rebuild the three
recursor spines through heterogeneous codomain paths, and the registered
view closes all three generated RHS edges at the original observation. -/
theorem natZeroRegisteredIotaMajorLinkStepAt_of_selfAdequate
    (univs : Nat) (level : @SLevel (natParams univs))
    [semantic : @Params.Semantic (natParams univs)] :
    letI : Params := natParams univs
    ∀ {Γ : List SExpr} {R : TShape → SExpr → Prop}
      {ρ : Valuation} {siteLevel depth : Nat}
      {Δ : List SExpr} {σ σ' : Subst} {core : Bool},
    (∀ {m M}, R m M → LE_Interp.Witness ρ m M) →
    LRD.FixedHeadConvertStep Γ →
    HasTypeStratifiedS Δ
      (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.rhs)
      (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.type)
      core depth →
    LR.DirectSubstWF Γ σ σ' Δ ρ →
    (∀ {root : TShape}
      (hX : LE_Interp.Witness ρ root
        (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.rhs)),
      LRD.SelfAdequateAt Γ hX depth) →
    NatZeroRegisteredIotaMajorLinkStepAt univs Γ ρ
      (SExpr.mkInst [level]
        (VInductDecl.recConst 0 ``Nat 0 InductiveFixtures.natType).type)
      siteLevel level (LE_Interp.Lower R) := by
  letI : Params := natParams univs
  letI : Params.Semantic := semantic
  intro Γ R ρ siteLevel depth Δ σ σ' core hR convert hstrat W self
  intro n recShapes ctorShapes mrec mctor majorX majorY recXs recYs
    A out outTy _hsite hΓ hmf hma hrhs _hleaf trace pair hrecHead
    hout hA
  have hctorLen : ctorShapes.length = 0 := hma.varN_length
  have hctorNil : ctorShapes = [] := List.length_eq_zero_iff.mp hctorLen
  subst ctorShapes
  have hrecShapesLen : recShapes.length = 3 := hmf.varN_length
  obtain ⟨succShape, zeroShape, motiveShape, rfl⟩ :
      ∃ succShape zeroShape motiveShape,
        recShapes = [succShape, zeroShape, motiveShape] :=
    ⟨recShapes[0], recShapes[1], recShapes[2],
      List.eq_getElem_of_length_eq_three recShapes hrecShapesLen⟩
  have hlens := trace.directArgs.lengths
  have hrecXsLen : recXs.length = 3 := Nat.succ.inj hlens.1
  have hrecYsLen : recYs.length = 3 := Nat.succ.inj hlens.2
  obtain ⟨succX, zeroX, motiveX, rfl⟩ :
      ∃ succX zeroX motiveX, recXs = [succX, zeroX, motiveX] :=
    ⟨recXs[0], recXs[1], recXs[2],
      List.eq_getElem_of_length_eq_three recXs hrecXsLen⟩
  obtain ⟨succY, zeroY, motiveY, rfl⟩ :
      ∃ succY zeroY motiveY, recYs = [succY, zeroY, motiveY] :=
    ⟨recYs[0], recYs[1], recYs[2],
      List.eq_getElem_of_length_eq_three recYs hrecYsLen⟩
  let view := trace.fourView
  have hRuleType : LE_Interp.Witness ρ
      (view.sparsePrefix outTy).T (probeNatZeroRuleType univs level) :=
    natZeroRegisteredRuleTypeSemanticWitness
      (n := n) (Γ := Γ) (ρ := ρ) (level := level)
      (outTy := outTy) univs trace view
  have hDirectRuleType : LE_Interp.Witness ρ
      (view.sparsePrefix outTy).T
      (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.type) := by
    change @LE_Interp.Witness (natParams univs) ρ
      (view.sparsePrefix outTy).T
      (SExpr.mkInst [level]
        (NatGeneration.rule 0 NatGeneration.flatCtors[0]).type)
    simpa only [probeNatZeroRuleTypeS_eq] using hRuleType
  intro k J p X Y frame leafExact hXY hbridge
  have zeroWF : IsStruct ``Nat.zero →
      WShape.ListNonZero ([] : List (WShape n)) := by
    intro hs
    change (match Params.classify ``Nat.zero with
      | some (.etaCtor _ _) => true
      | _ => false) = true at hs
    have hc : Params.classify ``Nat.zero = some (.ctor 0) := rfl
    simp [hc] at hs
  have hrootShape : (WShape.ctor' ``Nat.zero [] : WShape (n + 1)) =
      WShape.ctor ``Nat.zero [] zeroWF := by
    exact WShape.ctor_eq_ctor'.symm
  obtain ⟨nativeShapes, nativeWF, hp, hnativeLen⟩ :=
    frame.shape_ctor (c := ``Nat.zero) (l := []) (h := zeroWF)
      (by simpa using hrootShape)
  have hnativeNil : nativeShapes = [] := by
    exact List.length_eq_zero_iff.mp (by simpa using hnativeLen)
  subst nativeShapes
  subst p
  generalize hm : (WShape.ctor ``Nat.zero [] nativeWF : WShape (k + 1)) =
      nativeShape at leafExact
  cases leafExact with
  | @intro _ leafShapes leafWF ctorLs ctorLs' ctorXs ctorYs
      ctorHeadTypeX ctorHeadTypeY ctorResultX ctorResultY
      hctorClass hctorLenX hctorLenY hctorLevels hctorHeadX hctorHeadY
      hctorSpineX hctorSpineY _hctorArgs _hctorAligned _hctorMirror =>
    subst ctorLs'
    obtain ⟨rfl, hleafShapes⟩ := WShape.ctor.inj.1 hm
    have hleafNil : leafShapes = [] := by
      simpa using hleafShapes.symm
    subst leafShapes
    have hctorXsNil : ctorXs = [] := by
      exact List.length_eq_zero_iff.mp (by simpa using hctorLenX)
    have hctorYsNil : ctorYs = [] := by
      exact List.length_eq_zero_iff.mp (by simpa using hctorLenY)
    subst ctorXs
    subst ctorYs
    have hzeroSelf : IsDefEq Γ (.const ``Nat.zero ctorLs)
        (.const ``Nat.zero ctorLs) pair.domain := hbridge.hasType.2
    have hAType : ∃ u, Γ ⊢ A : .sort u :=
      ⟨pair.resultSortX, pair.resultX.hasType.2⟩
    have closeEdge :
        ∀ {siteXs siteYs : List SExpr},
          LR.DirectCtorArgsDefEqListed (LRD Γ)
            siteXs siteYs
            [view.third.domainExpr, view.second.domainExpr,
              view.first.domainExpr]
            [succShape, zeroShape, motiveShape]
            [view.third.domain.lift (n + 1),
              view.second.domain.lift (n + 1),
              view.first.domain.lift (n + 1)] →
          SExpr.SpineWF Γ
            (SExpr.mkInst [level]
              (VInductDecl.recConst 0 ``Nat 0
                InductiveFixtures.natType).type)
            (siteXs.reverse ++ [.const ``Nat.zero ctorLs]) A →
          SExpr.SpineWF Γ
            (SExpr.mkInst [level]
              (VInductDecl.recConst 0 ``Nat 0
                InductiveFixtures.natType).type)
            (siteYs.reverse ++ [.const ``Nat.zero ctorLs]) A →
          (LRD Γ).DefEq
            ((siteXs.foldr (fun (a f : SExpr) => f.app a)
              (.const ``Nat.rec [level])).app (.const ``Nat.zero ctorLs))
            ((siteYs.foldr (fun (a f : SExpr) => f.app a)
              (.const ``Nat.rec [level])).app (.const ``Nat.zero ctorLs))
            A out outTy := by
      intro siteXs siteYs hrecargs hspineX hspineY
      have hsiteTypeX : Γ ⊢
          ((siteXs.foldr (fun (a f : SExpr) => f.app a)
            (.const ``Nat.rec [level])).app (.const ``Nat.zero ctorLs)) : A := by
        simpa only [List.foldl_append, List.foldl_reverse,
          List.foldl_cons, List.foldl_nil] using
          hspineX.hasType hrecHead
      have hsiteTypeY : Γ ⊢
          ((siteYs.foldr (fun (a f : SExpr) => f.app a)
            (.const ``Nat.rec [level])).app (.const ``Nat.zero ctorLs)) : A := by
        simpa only [List.foldl_append, List.foldl_reverse,
          List.foldl_cons, List.foldl_nil] using
          hspineY.hasType hrecHead
      apply LRD.iotaDefEq_of_exactListedDataAt hΓ
          (natZeroDirectIotaRule univs).pat hmf hma hrhs
          hrecargs (LRS.CtorArgsDefEq.nil (IH := LR Γ))
          .rfl .rfl hsiteTypeX hsiteTypeY hsiteTypeX hsiteTypeY
          hAType hrecHead hspineX hspineY
          hctorHeadX hctorHeadY hctorSpineX hctorSpineY
          hzeroSelf hzeroSelf hout hA
      intro rule
      rw [natIotaRule_ext univs rule (natZeroDirectIotaRule univs)]
      exact natZeroIotaRHSDefEq_of_registeredView univs level view
        hR convert hstrat W self hDirectRuleType
    refine ⟨?_, ?_, ?_⟩
    · exact closeEdge view.recArgsListed.left
        (pair.fullXAt hΓ hbridge)
        (pair.fullXAt hΓ (hbridge.trans hXY))
    · exact closeEdge view.recArgsListed.right
        (pair.fullYAt hΓ (pair.major.symm.trans hbridge))
        (pair.fullYAt hΓ (pair.major.symm.trans (hbridge.trans hXY)))
    · exact closeEdge view.recArgsListed
        (pair.fullXAt hΓ hbridge)
        (pair.fullYAt hΓ (pair.major.symm.trans (hbridge.trans hXY)))

/-- Close every framed native link of the registered Nat-successor major,
given the strict recursive producer for its sole predecessor field.

After `CtorFrame.shape_ctor` identifies the native unary leaf, the producer
rebuilds that field at the registered root observation.  The direct-listed
materializer then reuses the same proof-relevant predecessor package for all
three edges of the major-link rectangle. -/
theorem natSuccRegisteredIotaMajorLinkStepAt_of_selfAdequate
    (univs : Nat) (level : @SLevel (natParams univs))
    [semantic : @Params.Semantic (natParams univs)] :
    letI : Params := natParams univs
    ∀ {Γ : List SExpr} {R : TShape → SExpr → Prop}
      {ρ : Valuation} {siteLevel depth : Nat}
      {Δ : List SExpr} {σ σ' : Subst} {core : Bool},
    (∀ {m M}, R m M → LE_Interp.Witness ρ m M) →
    LRD.FixedHeadConvertStep Γ →
    HasTypeStratifiedS Δ
      (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.rhs)
      (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.type)
      core depth →
    LR.DirectSubstWF Γ σ σ' Δ ρ →
    (∀ {root : TShape}
      (hX : LE_Interp.Witness ρ root
        (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.rhs)),
      LRD.SelfAdequateAt Γ hX depth) →
    NatSuccFramedPredStep Γ ρ →
    NatSuccRegisteredIotaMajorLinkStepAt univs Γ ρ
      (SExpr.mkInst [level]
        (VInductDecl.recConst 0 ``Nat 0 InductiveFixtures.natType).type)
      siteLevel level (LE_Interp.Lower R) := by
  letI : Params := natParams univs
  letI : Params.Semantic := semantic
  intro Γ R ρ siteLevel depth Δ σ σ' core hR convert hstrat W self
    predStep
  intro n recShapes ctorShapes mrec mctor majorX majorY recXs recYs
    A out outTy _hsite hΓ hmf hma hrhs _hleaf trace pair hrecHead
    hout hA
  have hctorLen : ctorShapes.length = 1 := hma.varN_length
  obtain ⟨field, rfl⟩ := List.length_eq_one_iff.mp hctorLen
  have hmctor : mctor none = field.T := by
    cases hma with
    | var _ => rfl
  have hrecShapesLen : recShapes.length = 3 := hmf.varN_length
  obtain ⟨succShape, zeroShape, motiveShape, rfl⟩ :
      ∃ succShape zeroShape motiveShape,
        recShapes = [succShape, zeroShape, motiveShape] :=
    ⟨recShapes[0], recShapes[1], recShapes[2],
      List.eq_getElem_of_length_eq_three recShapes hrecShapesLen⟩
  have hlens := trace.directArgs.lengths
  have hrecXsLen : recXs.length = 3 := Nat.succ.inj hlens.1
  have hrecYsLen : recYs.length = 3 := Nat.succ.inj hlens.2
  obtain ⟨succX, zeroX, motiveX, rfl⟩ :
      ∃ succX zeroX motiveX, recXs = [succX, zeroX, motiveX] :=
    ⟨recXs[0], recXs[1], recXs[2],
      List.eq_getElem_of_length_eq_three recXs hrecXsLen⟩
  obtain ⟨succY, zeroY, motiveY, rfl⟩ :
      ∃ succY zeroY motiveY, recYs = [succY, zeroY, motiveY] :=
    ⟨recYs[0], recYs[1], recYs[2],
      List.eq_getElem_of_length_eq_three recYs hrecYsLen⟩
  let view := trace.fourView
  intro k J p X Y frame leafExact hXY hbridge
  have succWF : IsStruct ``Nat.succ →
      WShape.ListNonZero [field] := by
    intro hs
    change (match Params.classify ``Nat.succ with
      | some (.etaCtor _ _) => true
      | _ => false) = true at hs
    have hc : Params.classify ``Nat.succ = some (.ctor 1) := rfl
    simp [hc] at hs
  have hrootShape : (WShape.ctor' ``Nat.succ [field] : WShape (n + 1)) =
      WShape.ctor ``Nat.succ [field] succWF := by
    exact WShape.ctor_eq_ctor'.symm
  obtain ⟨nativeShapes, nativeWF, hp, hnativeLen⟩ :=
    frame.shape_ctor (c := ``Nat.succ) (l := [field]) (h := succWF)
      (by simpa using hrootShape)
  obtain ⟨nativeField, rfl⟩ :=
    List.length_eq_one_iff.mp (by simpa using hnativeLen)
  subst p
  generalize hm :
      (WShape.ctor ``Nat.succ [nativeField] nativeWF : WShape (k + 1)) =
        nativeShape at leafExact
  cases leafExact with
  | @intro _ leafShapes leafWF ctorLs ctorLs' ctorXs ctorYs
      ctorHeadTypeX ctorHeadTypeY ctorResultX ctorResultY
      hctorClass hctorLenX hctorLenY hctorLevels hctorHeadX hctorHeadY
      hctorSpineX hctorSpineY hctorArgs _hctorAligned _hctorMirror =>
    subst ctorLs'
    obtain ⟨rfl, hleafShapes⟩ := WShape.ctor.inj.1 hm
    have hleafOne : leafShapes = [nativeField] := by
      simpa using hleafShapes.symm
    subst leafShapes
    obtain ⟨predX, rfl⟩ :=
      List.length_eq_one_iff.mp (by simpa using hctorLenX)
    obtain ⟨predY, rfl⟩ :=
      List.length_eq_one_iff.mp (by simpa using hctorLenY)
    let pred := predStep.produce frame hctorArgs
    have hmajorSelfX : IsDefEq Γ
        ((SExpr.const ``Nat.succ ctorLs).app predX)
        ((SExpr.const ``Nat.succ ctorLs).app predX) pair.domain :=
      hbridge.hasType.2
    have hmajorSelfY : IsDefEq Γ
        ((SExpr.const ``Nat.succ ctorLs).app predY)
        ((SExpr.const ``Nat.succ ctorLs).app predY) pair.domain :=
      (hbridge.trans hXY).hasType.2
    have hAType : ∃ u, Γ ⊢ A : .sort u :=
      ⟨pair.resultSortX, pair.resultX.hasType.2⟩
    have closeEdge :
        ∀ {siteXs siteYs : List SExpr},
          LR.DirectCtorArgsDefEqListed (LRD Γ)
            siteXs siteYs
            [view.third.domainExpr, view.second.domainExpr,
              view.first.domainExpr]
            [succShape, zeroShape, motiveShape]
            [view.third.domain.lift (n + 1),
              view.second.domain.lift (n + 1),
              view.first.domain.lift (n + 1)] →
          SExpr.SpineWF Γ
            (SExpr.mkInst [level]
              (VInductDecl.recConst 0 ``Nat 0
                InductiveFixtures.natType).type)
            (siteXs.reverse ++
              [(SExpr.const ``Nat.succ ctorLs).app predX]) A →
          SExpr.SpineWF Γ
            (SExpr.mkInst [level]
              (VInductDecl.recConst 0 ``Nat 0
                InductiveFixtures.natType).type)
            (siteYs.reverse ++
              [(SExpr.const ``Nat.succ ctorLs).app predY]) A →
          (LRD Γ).DefEq
            ((siteXs.foldr (fun (a f : SExpr) => f.app a)
              (SExpr.const ``Nat.rec [level])).app
                ((SExpr.const ``Nat.succ ctorLs).app predX))
            ((siteYs.foldr (fun (a f : SExpr) => f.app a)
              (SExpr.const ``Nat.rec [level])).app
                ((SExpr.const ``Nat.succ ctorLs).app predY))
            A out outTy := by
      intro siteXs siteYs hrecargs hspineX hspineY
      have hsiteTypeX : Γ ⊢
          ((siteXs.foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const ``Nat.rec [level])).app
              ((SExpr.const ``Nat.succ ctorLs).app predX)) : A := by
        simpa only [List.foldl_append, List.foldl_reverse,
          List.foldl_cons, List.foldl_nil] using
          hspineX.hasType hrecHead
      have hsiteTypeY : Γ ⊢
          ((siteYs.foldr (fun (a f : SExpr) => f.app a)
            (SExpr.const ``Nat.rec [level])).app
              ((SExpr.const ``Nat.succ ctorLs).app predY)) : A := by
        simpa only [List.foldl_append, List.foldl_reverse,
          List.foldl_cons, List.foldl_nil] using
          hspineY.hasType hrecHead
      apply LRD.iotaDefEq_of_exactDirectListedDataAt hΓ
          (natSuccDirectIotaRule univs).pat hmf hma hrhs
          hrecargs (NatSuccPredArgCoherent.listed pred)
          .rfl .rfl hsiteTypeX hsiteTypeY hsiteTypeX hsiteTypeY
          hAType hrecHead hspineX hspineY
          hctorHeadX hctorHeadY hctorSpineX hctorSpineY
          hmajorSelfX hmajorSelfY hout hA
      intro rule
      rw [natIotaRule_ext univs rule (natSuccDirectIotaRule univs)]
      exact natSuccIotaRHSDefEq_of_registeredViewDirectListed
        univs level view hmctor pred.typeWitness
        hR convert hstrat W self
    refine ⟨?_, ?_, ?_⟩
    · exact closeEdge view.recArgsListed.left
        (pair.fullXAt hΓ hbridge)
        (pair.fullXAt hΓ (hbridge.trans hXY))
    · exact closeEdge view.recArgsListed.right
        (pair.fullYAt hΓ (pair.major.symm.trans hbridge))
        (pair.fullYAt hΓ (pair.major.symm.trans (hbridge.trans hXY)))
    · exact closeEdge view.recArgsListed
        (pair.fullXAt hΓ hbridge)
        (pair.fullYAt hΓ (pair.major.symm.trans (hbridge.trans hXY)))

/--
info: 'Lean4Lean.SExpr.ParamsD0.natSuccRegisteredIotaMajorLinkStepAt_of_selfAdequate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 probeNatGeneratedRuleSucc_lookup._native.native_decide.ax_1_1,
 probeNatGeneratedRuleZero_lookup._native.native_decide.ax_1_1,
 probeNatRecTypeV_eq._native.native_decide.ax_1_1,
 probeNatRuleRhs_ne._native.native_decide.ax_1_1,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatSuccRuleTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms natSuccRegisteredIotaMajorLinkStepAt_of_selfAdequate

/-- Assemble the complete registered Nat major-link dispatcher once the
successor branch is supplied.  The zero branch is now derived entirely from
the recursive self-adequacy inputs rather than exposed as another callback. -/
theorem natRegisteredIotaMajorLinkStepAt_of_zeroSelfAdequate
    (univs : Nat) (level : @SLevel (natParams univs))
    [semantic : @Params.Semantic (natParams univs)] :
    letI : Params := natParams univs
    ∀ {Γ : List SExpr} {R : TShape → SExpr → Prop}
      {ρ : Valuation} {siteLevel depth : Nat}
      {Δ : List SExpr} {σ σ' : Subst} {core : Bool},
    (∀ {m M}, R m M → LE_Interp.Witness ρ m M) →
    LRD.FixedHeadConvertStep Γ →
    HasTypeStratifiedS Δ
      (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.rhs)
      (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.type)
      core depth →
    LR.DirectSubstWF Γ σ σ' Δ ρ →
    (∀ {root : TShape}
      (hX : LE_Interp.Witness ρ root
        (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.rhs)),
      LRD.SelfAdequateAt Γ hX depth) →
    NatSuccRegisteredIotaMajorLinkStepAt univs Γ ρ
      (SExpr.mkInst [level]
        (VInductDecl.recConst 0 ``Nat 0 InductiveFixtures.natType).type)
      siteLevel level (LE_Interp.Lower R) →
    LRD.RegisteredIotaMajorLinkStepAt Γ ρ
      (SExpr.mkInst [level]
        (VInductDecl.recConst 0 ``Nat 0 InductiveFixtures.natType).type)
      siteLevel ``Nat.rec [level] (LE_Interp.Lower R) := by
  letI : Params := natParams univs
  letI : Params.Semantic := semantic
  intro Γ R ρ siteLevel depth Δ σ σ' core hR convert hstrat W self succ
  exact natRegisteredIotaMajorLinkStepAt_of_branches univs level
    (natZeroRegisteredIotaMajorLinkStepAt_of_selfAdequate univs level
      hR convert hstrat W self)
    succ

/-- Assemble the complete registered Nat major-link step from recursive
self-adequacy for both generated rules and the sole strict-recursion
obligation of the successor branch. -/
theorem natRegisteredIotaMajorLinkStepAt_of_selfAdequate
    (univs : Nat) (level : @SLevel (natParams univs))
    [semantic : @Params.Semantic (natParams univs)] :
    letI : Params := natParams univs
    ∀ {Γ : List SExpr} {R : TShape → SExpr → Prop}
      {ρ : Valuation} {siteLevel depth : Nat}
      {Δ : List SExpr} {σ σ' : Subst} {core : Bool},
    (∀ {m M}, R m M → LE_Interp.Witness ρ m M) →
    LRD.FixedHeadConvertStep Γ →
    HasTypeStratifiedS Δ
      (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.rhs)
      (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.type)
      core depth →
    HasTypeStratifiedS Δ
      (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.rhs)
      (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.type)
      core depth →
    LR.DirectSubstWF Γ σ σ' Δ ρ →
    (∀ {root : TShape}
      (hX : LE_Interp.Witness ρ root
        (SExpr.mkInst [level] (natZeroDirectIotaRule univs).df.rhs)),
      LRD.SelfAdequateAt Γ hX depth) →
    (∀ {root : TShape}
      (hX : LE_Interp.Witness ρ root
        (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.rhs)),
      LRD.SelfAdequateAt Γ hX depth) →
    NatSuccFramedPredStep Γ ρ →
    LRD.RegisteredIotaMajorLinkStepAt Γ ρ
      (SExpr.mkInst [level]
        (VInductDecl.recConst 0 ``Nat 0 InductiveFixtures.natType).type)
      siteLevel ``Nat.rec [level] (LE_Interp.Lower R) := by
  letI : Params := natParams univs
  letI : Params.Semantic := semantic
  intro Γ R ρ siteLevel depth Δ σ σ' core hR convert
    hzeroStrat hsuccStrat W zeroSelf succSelf predStep
  exact natRegisteredIotaMajorLinkStepAt_of_branches univs level
    (natZeroRegisteredIotaMajorLinkStepAt_of_selfAdequate univs level
      hR convert hzeroStrat W zeroSelf)
    (natSuccRegisteredIotaMajorLinkStepAt_of_selfAdequate univs level
      hR convert hsuccStrat W succSelf predStep)

/--
info: 'Lean4Lean.SExpr.ParamsD0.natRegisteredIotaMajorLinkStepAt_of_selfAdequate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 probeNatGeneratedRuleSucc_lookup._native.native_decide.ax_1_1,
 probeNatGeneratedRuleZero_lookup._native.native_decide.ax_1_1,
 probeNatRecTypeV_eq._native.native_decide.ax_1_1,
 probeNatRuleRhs_ne._native.native_decide.ax_1_1,
 probeNatSuccCtorTypeV_eq._native.native_decide.ax_1_1,
 probeNatSuccRuleTypeV_eq._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 probeNatZeroRuleTypeV_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms natRegisteredIotaMajorLinkStepAt_of_selfAdequate

/-- The self-adequate native exact Nat-successor leaf.  Its sole additional
logical premise is still the guarded term upgrade of the selected predecessor
capture; that upgrade is incorporated into the same aligned dominance
package used by the zero branch. -/
theorem natSuccIotaDefEq_of_ctorExactAt_selfAdequate
    (univs : Nat) (level : @SLevel (natParams univs))
    [semantic : @Params.Semantic (natParams univs)] :
    letI : Params := natParams univs
    ∀ {n : Nat} {Γ : List SExpr} {R : TShape → SExpr → Prop}
      {ρ : Valuation} {depth : Nat}
      {Δ : List SExpr} {σ σ' : Subst} {core : Bool}
      {recShapes : List (WShape (n + 1))}
      {ctorShapes : List (WShape n)}
      {mrec : (Pattern.varN (.const ``Nat.rec) 3).Path → TShape}
      {mctor : (Pattern.varN (.const ``Nat.succ) 1).Path → TShape}
      {recXs recYs : List SExpr} {majorX majorY recHeadType A : SExpr}
      {out outTy : WShape (n + 1)}
      {hwf : IsStruct ``Nat.succ → WShape.ListNonZero ctorShapes.reverse},
    Ctx.WF Γ →
    LE_Interp.Matches (n := n + 1)
      (Pattern.varN (.const ``Nat.rec) 3) ``Nat.rec recShapes mrec →
    LE_Interp.Matches (n := n)
      (Pattern.varN (.const ``Nat.succ) 1) ``Nat.succ ctorShapes mctor →
    LE_Interp.RHS [level] (Sum.elim mrec mctor)
      (LE_Interp.Lower R) out.T
      (NatGeneration.ruleRHS natRuleClosure
        probeNatFlatCtorSucc_lookup) →
    (∀ {m M}, R m M → LE_Interp.Witness ρ m M) →
    LRS.CtorExact Γ (LR Γ) majorX majorY
      (.ctor ``Nat.succ ctorShapes.reverse hwf) →
    LR.DirectPatternLeafSpine Γ (LRD Γ) recHeadType
      (majorX :: recXs) (majorY :: recYs)
      ((.ctor ``Nat.succ ctorShapes.reverse hwf) :: recShapes)
      A out outTy →
    IsDefEq Γ (.const ``Nat.rec [level]) (.const ``Nat.rec [level])
      recHeadType →
    out.HasType outTy →
    (LRD Γ).TyDefEq A A outTy →
    LRD.FixedHeadConvertStep Γ →
    HasTypeStratifiedS Δ
      (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.rhs)
      (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.type)
      core depth →
    LR.DirectSubstWF Γ σ σ' Δ ρ →
    (∀ {root : TShape}
      (hX : LE_Interp.Witness ρ root
        (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.rhs)),
      LRD.SelfAdequateAt Γ hX depth) →
    (∀ {mx my captureType :
          (RecursorIotaPattern ``Nat.rec 3 ``Nat.succ 1).Path → SExpr}
        (H : LRS.CaptureDefEqAligned (n := n) (LR Γ)
          (mctor none) (mx natSuccPredPath) (my natSuccPredPath)
          (captureType natSuccPredPath)),
      LR.DirectTermCaptureDefEqAligned.Upgrade H) →
    (∀ {head : TShape}
        {mx my captureType :
          (RecursorIotaPattern ``Nat.rec 3 ``Nat.succ 1).Path → SExpr}
        {outTyP : WShape (n + 1)}
        (_hhead : LE_Interp.Witness ρ head
          (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.rhs))
        (_htyped : LE_Interp.Witness.TypedRDeep (fun _ => True) ρ head
          (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.rhs)
          (SExpr.mkInst [level] (natSuccDirectIotaRule univs).df.type))
        (hshape : LE_Interp.RHS.ShapeSpine (Sum.elim mrec mctor) head
          (natSuccDirectIotaRule univs).capturePaths out.T)
        (_hcapDirect : ∀ path,
          LR.DirectTermCaptureDefEqAligned.AtSomeLevel Γ
            (Sum.elim mrec mctor path) (mx path) (my path)
            (captureType path))
        (_hout : out.HasType outTyP),
      (¬out.T ≤ TShape.bot) →
      LR.DirectFixedHeadAlignedTyping Γ ρ mx my captureType
        (P := fun _ => True)
        (body := SExpr.mkInst [level]
          (natSuccDirectIotaRule univs).df.rhs)
        (headType := SExpr.mkInst [level]
          (natSuccDirectIotaRule univs).df.type)
        (outTy := outTyP) hshape) →
    (LRD Γ).DefEq
      ((recXs.foldr (fun (a f : SExpr) => f.app a)
        (.const ``Nat.rec [level])).app majorX)
      ((recYs.foldr (fun (a f : SExpr) => f.app a)
        (.const ``Nat.rec [level])).app majorY)
      A out outTy := by
  letI : Params := natParams univs
  letI : Params.Semantic := semantic
  intro n Γ R ρ depth Δ σ σ' core recShapes ctorShapes mrec mctor
    recXs recYs majorX majorY recHeadType A out outTy hwf hΓ hmf hma
    hrhs hR leaf hleaf hrecHead hout hA convert hstrat W self upgradePred
    makeAlignment
  apply LRD.iotaDefEq_of_ctorExactAt hΓ
      (natSuccDirectIotaRule univs).pat hmf hma hrhs leaf hleaf
      hrecHead hout hA
  intro rule
  rw [natIotaRule_ext univs rule (natSuccDirectIotaRule univs)]
  exact natSuccIotaRHSDefEq_of_selfAdequate univs level
    hR convert hstrat W self upgradePred makeAlignment

/--
info: 'Lean4Lean.SExpr.ParamsD0.natZeroIotaDefEq_of_ctorExactAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 probeNatGeneratedRuleSucc_lookup._native.native_decide.ax_1_1,
 probeNatGeneratedRuleZero_lookup._native.native_decide.ax_1_1,
 probeNatRuleRhs_ne._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms natZeroIotaDefEq_of_ctorExactAt

/--
info: 'Lean4Lean.SExpr.ParamsD0.natSuccIotaDefEq_of_ctorExactAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 probeNatGeneratedRuleSucc_lookup._native.native_decide.ax_1_1,
 probeNatGeneratedRuleZero_lookup._native.native_decide.ax_1_1,
 probeNatRuleRhs_ne._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms natSuccIotaDefEq_of_ctorExactAt

/--
info: 'Lean4Lean.SExpr.ParamsD0.natZeroIotaDefEq_of_ctorExactAt_selfAdequate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 probeNatGeneratedRuleSucc_lookup._native.native_decide.ax_1_1,
 probeNatGeneratedRuleZero_lookup._native.native_decide.ax_1_1,
 probeNatRuleRhs_ne._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms natZeroIotaDefEq_of_ctorExactAt_selfAdequate

/--
info: 'Lean4Lean.SExpr.ParamsD0.natSuccIotaDefEq_of_ctorExactAt_selfAdequate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 probeNatGeneratedRuleSucc_lookup._native.native_decide.ax_1_1,
 probeNatGeneratedRuleZero_lookup._native.native_decide.ax_1_1,
 probeNatRuleRhs_ne._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms natSuccIotaDefEq_of_ctorExactAt_selfAdequate

/--
info: 'Lean4Lean.SExpr.ParamsD0.natZeroIotaDefEq_of_registeredCtorExactAt_selfAdequate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 probeNatGeneratedRuleSucc_lookup._native.native_decide.ax_1_1,
 probeNatGeneratedRuleZero_lookup._native.native_decide.ax_1_1,
 probeNatRecTypeV_eq._native.native_decide.ax_1_1,
 probeNatRuleRhs_ne._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 probeNatZeroRuleTypeV_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms natZeroIotaDefEq_of_registeredCtorExactAt_selfAdequate

/--
info: 'Lean4Lean.SExpr.ParamsD0.natZeroRegisteredIotaMajorLinkStepAt_of_selfAdequate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 probeNatGeneratedRuleSucc_lookup._native.native_decide.ax_1_1,
 probeNatGeneratedRuleZero_lookup._native.native_decide.ax_1_1,
 probeNatRecTypeV_eq._native.native_decide.ax_1_1,
 probeNatRuleRhs_ne._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 probeNatZeroRuleTypeV_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms natZeroRegisteredIotaMajorLinkStepAt_of_selfAdequate

/--
info: 'Lean4Lean.SExpr.ParamsD0.natRegisteredIotaMajorLinkStepAt_of_zeroSelfAdequate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 probeNatGeneratedRuleSucc_lookup._native.native_decide.ax_1_1,
 probeNatGeneratedRuleZero_lookup._native.native_decide.ax_1_1,
 probeNatRecTypeV_eq._native.native_decide.ax_1_1,
 probeNatRuleRhs_ne._native.native_decide.ax_1_1,
 probeNatTypeTypeV_eq._native.native_decide.ax_1_1,
 probeNatZeroRuleTypeV_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms natRegisteredIotaMajorLinkStepAt_of_zeroSelfAdequate

/-- The iota-only Nat constant callback from its one remaining guarded leaf
algebra.  `natPat_no_const` closes the entire definitional-pattern branch, so
the callback inherits no delta-rank premise; D0 adds that branch separately. -/
theorem natSelfAdequateConstStep_of_typedLeaf
    (univs : Nat) [semantic : @Params.Semantic (natParams univs)]
    {Γ : List (@SExpr (natParams univs))}
    (hΓ : @Ctx.WF (natParams univs) Γ)
    (leaf : @LRD.CoherentTypedIotaLeafStep (natParams univs) Γ) :
    @LRD.SelfAdequateConstStep (natParams univs) Γ := by
  exact @LRD.SelfAdequateConstStep.of_noConstPat_typed
    (natParams univs) semantic Γ hΓ leaf
    (fun {_ _} hpat => natPat_no_const univs hpat)

/--
info: 'Lean4Lean.SExpr.ParamsD0.natSelfAdequateConstStep_of_typedLeaf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms natSelfAdequateConstStep_of_typedLeaf

/-- Backwards-compatible Nat adapter for a leaf implementation that is
already uniform in an arbitrary numeric depth. -/
theorem natSelfAdequateConstStep_of_leaf
    (univs : Nat) [semantic : @Params.Semantic (natParams univs)]
    {Γ : List (@SExpr (natParams univs))}
    (hΓ : @Ctx.WF (natParams univs) Γ)
    (leaf : @LRD.CoherentIotaLeafStep (natParams univs) Γ) :
    @LRD.SelfAdequateConstStep (natParams univs) Γ := by
  exact @LRD.SelfAdequateConstStep.of_noConstPat
    (natParams univs) semantic Γ hΓ leaf
    (fun {_ _} hpat => natPat_no_const univs hpat)

/--
info: 'Lean4Lean.SExpr.ParamsD0.natSelfAdequateConstStep_of_leaf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms natSelfAdequateConstStep_of_leaf

/-! ## D0b semantic certificate -/

theorem d0StructureEtaSound (univs : Nat) :
    @Params.StructureEtaSound (d0Params univs) := by
  letI : Params := d0Params univs
  intro rule levels Gamma params major hreg
  exact (d0Env_no_structEta rule hreg).elim

def D0ContextValid (univs : Nat)
    (Gamma : List (@SExpr (d0Params univs))) : Prop :=
  letI : Params := d0Params univs
  OnCtx (Gamma.map SExpr.reify) (d0Env.IsType univs)

def D0TypesDefEq (univs : Nat) {Gamma : List (@SExpr (d0Params univs))}
    (A B : @SExpr (d0Params univs)) : Prop :=
  letI : Params := d0Params univs
  ∃ u, IsDefEq Gamma A B (.sort u)

theorem d0TypeUniq (univs : Nat)
    {Gamma : List (@SExpr (d0Params univs))}
    {x A B : @SExpr (d0Params univs)}
    (hGamma : D0ContextValid univs Gamma)
    (hxA : @IsDefEq (d0Params univs) Gamma x x A)
    (hxB : @IsDefEq (d0Params univs) Gamma x x B) :
    D0TypesDefEq (Gamma := Gamma) univs A B := by
  letI : Params := d0Params univs
  change OnCtx (Gamma.map SExpr.reify) (d0Env.IsType univs) at hGamma
  change ∃ u, IsDefEq Gamma A B (.sort u)
  have hxA' := hxA.reify hGamma
  have hxB' := hxB.reify hGamma
  obtain ⟨u, hAB⟩ := hxA'.uniq d0Env_wf hGamma hxB'
  have hlevels := (VEnv.CtxStrong.strong d0Env_ordered hGamma).levelWF
  have hAB' := SExpr.IsDefEq.mkS (d0StructureEtaSound univs) hAB hlevels
  have hctx : (Gamma.map SExpr.reify).map SExpr.mk = Gamma := by
    rw [List.map_map]
    exact List.map_id''' Gamma fun term _ => SExpr.mk_reify term
  rw [hctx] at hAB'
  refine ⟨SLevel.mk u, ?_⟩
  simpa only [SExpr.mk_reify, SExpr.mk] using hAB'

theorem d0TypesTrans (univs : Nat)
    {Gamma : List (@SExpr (d0Params univs))}
    {A B C : @SExpr (d0Params univs)}
    (hGamma : D0ContextValid univs Gamma)
    (hAB : D0TypesDefEq (Gamma := Gamma) univs A B)
    (hBC : D0TypesDefEq (Gamma := Gamma) univs B C) :
    D0TypesDefEq (Gamma := Gamma) univs A C := by
  letI : Params := d0Params univs
  obtain ⟨u, hAB⟩ := hAB
  obtain ⟨v, hBC⟩ := hBC
  obtain ⟨w, huv⟩ := d0TypeUniq univs hGamma hAB.hasType.2 hBC.hasType.1
  exact ⟨u, hAB.trans (huv.symm.defeqDF hBC)⟩

theorem d0TypesInst (univs : Nat)
    {Gamma : List (@SExpr (d0Params univs))}
    {D B B' e : @SExpr (d0Params univs)}
    (hBB' : D0TypesDefEq (Gamma := D :: Gamma) univs B B')
    (he : @IsDefEq (d0Params univs) Gamma e e D) :
    D0TypesDefEq (Gamma := Gamma) univs
      (@SExpr.inst (d0Params univs) B e)
      (@SExpr.inst (d0Params univs) B' e) := by
  letI : Params := d0Params univs
  obtain ⟨u, hBB'⟩ := hBB'
  have hsubst := hBB'.subst
    (Ctx.Subst.one IsDefEq.weak' IsDefEq.bvar he)
  change IsDefEq Gamma (B.inst e) (B'.inst e) (.sort u) at hsubst
  exact ⟨u, hsubst⟩

theorem d0ForallEInv (univs : Nat)
    {Gamma : List (@SExpr (d0Params univs))}
    {A B A' B' : @SExpr (d0Params univs)}
    (hGamma : D0ContextValid univs Gamma)
    (hPi : D0TypesDefEq (Gamma := Gamma) univs
      (@SExpr.forallE (d0Params univs) A B)
      (@SExpr.forallE (d0Params univs) A' B')) :
    D0TypesDefEq (Gamma := Gamma) univs A A' ∧
      D0TypesDefEq (Gamma := A :: Gamma) univs B B' := by
  letI : Params := d0Params univs
  change OnCtx (Gamma.map SExpr.reify) (d0Env.IsType univs) at hGamma
  obtain ⟨_, hPi⟩ := hPi
  have hPi' := hPi.reify hGamma
  have hPiU : d0Env.IsDefEqU univs (Gamma.map SExpr.reify)
      (.forallE A.reify B.reify) (.forallE A'.reify B'.reify) :=
    ⟨_, hPi'⟩
  obtain ⟨⟨u, hA⟩, v, hB⟩ :=
    VEnv.IsDefEqU.forallE_inv d0Env_wf hGamma hPiU
  have hlevels := (VEnv.CtxStrong.strong d0Env_ordered hGamma).levelWF
  have hA' := SExpr.IsDefEq.mkS (d0StructureEtaSound univs) hA hlevels
  have hAlevels := (hA.levelWF hlevels).1
  have hB' := SExpr.IsDefEq.mkS (d0StructureEtaSound univs) hB
    ⟨hlevels, hAlevels⟩
  have hctx : (Gamma.map SExpr.reify).map SExpr.mk = Gamma := by
    rw [List.map_map]
    exact List.map_id''' Gamma fun term _ => SExpr.mk_reify term
  constructor
  · refine ⟨SLevel.mk u, ?_⟩
    simpa only [hctx, SExpr.mk_reify, SExpr.mk] using hA'
  · refine ⟨SLevel.mk v, ?_⟩
    simpa only [List.map_cons, hctx, SExpr.mk_reify, SExpr.mk] using hB'

structure D0SpineConsView (univs : Nat)
    {Gamma : List (@SExpr (d0Params univs))}
    (D B e : @SExpr (d0Params univs))
    (es : List (@SExpr (d0Params univs)))
    (R : @SExpr (d0Params univs)) where
  domain : @SExpr (d0Params univs)
  codomain : @SExpr (d0Params univs)
  domainEq : D0TypesDefEq (Gamma := Gamma) univs D domain
  codomainEq : D0TypesDefEq (Gamma := D :: Gamma) univs B codomain
  argument : @IsDefEq (d0Params univs) Gamma e e domain
  tail : @SpineWF (d0Params univs) Gamma
    (@SExpr.inst (d0Params univs) codomain e) es R

theorem d0SpineConsView_nonempty (univs : Nat)
    {Gamma : List (@SExpr (d0Params univs))}
    {D B Head e R : @SExpr (d0Params univs)}
    {es : List (@SExpr (d0Params univs))}
    (hGamma : D0ContextValid univs Gamma)
    (hHead : D0TypesDefEq (Gamma := Gamma) univs
      (@SExpr.forallE (d0Params univs) D B) Head)
    (H : @SpineWF (d0Params univs) Gamma Head (e :: es) R) :
    Nonempty (D0SpineConsView (Gamma := Gamma) univs D B e es R) := by
  letI : Params := d0Params univs
  generalize hargsEq : e :: es = args at H
  induction H generalizing D B e es with
  | nil => cases hargsEq
  | @cons _ domain _ _ codomain harg htail ih =>
    cases hargsEq
    obtain ⟨hdom, hbody⟩ := d0ForallEInv univs hGamma hHead
    exact ⟨{
      domain := domain
      codomain := codomain
      domainEq := hdom
      codomainEq := hbody
      argument := harg
      tail := htail }⟩
  | @conv _ Head' u _ _ hconv htail ih =>
    exact ih (d0TypesTrans univs hGamma hHead ⟨u, hconv⟩) hargsEq
  | @ret _ _ R' _ _ htail hret ih =>
    let ⟨view⟩ := ih hHead hargsEq
    exact ⟨{ view with tail := .ret view.tail hret }⟩

noncomputable def d0SpineConsView (univs : Nat)
    {Gamma : List (@SExpr (d0Params univs))}
    {D B Head e R : @SExpr (d0Params univs)}
    {es : List (@SExpr (d0Params univs))}
    (hGamma : D0ContextValid univs Gamma)
    (hHead : D0TypesDefEq (Gamma := Gamma) univs
      (@SExpr.forallE (d0Params univs) D B) Head)
    (H : @SpineWF (d0Params univs) Gamma Head (e :: es) R) :
    D0SpineConsView (Gamma := Gamma) univs D B e es R :=
  Classical.choice (d0SpineConsView_nonempty univs hGamma hHead H)

theorem D0SpineConsView.argumentExpected (univs : Nat)
    {Gamma : List (@SExpr (d0Params univs))}
    {D B e R : @SExpr (d0Params univs)}
    {es : List (@SExpr (d0Params univs))}
    (view : D0SpineConsView (Gamma := Gamma) univs D B e es R) :
    @IsDefEq (d0Params univs) Gamma e e D := by
  letI : Params := d0Params univs
  obtain ⟨_, hdom⟩ := view.domainEq
  exact hdom.symm.defeqDF view.argument

theorem D0SpineConsView.restEq (univs : Nat)
    {Gamma : List (@SExpr (d0Params univs))}
    {D B e R : @SExpr (d0Params univs)}
    {es : List (@SExpr (d0Params univs))}
    (view : D0SpineConsView (Gamma := Gamma) univs D B e es R) :
    D0TypesDefEq (Gamma := Gamma) univs
      (@SExpr.inst (d0Params univs) B e)
      (@SExpr.inst (d0Params univs) view.codomain e) :=
  d0TypesInst univs view.codomainEq (view.argumentExpected univs)

theorem d0PathSpineOfSpineWF (univs : Nat)
    {Gamma : List (@SExpr (d0Params univs))}
    {alpha : Type}
    {value type : alpha → @SExpr (d0Params univs)}
    {A B : @SExpr (d0Params univs)} {paths : List alpha}
    (hGamma : D0ContextValid univs Gamma)
    (htyped : ∀ path, @IsDefEq (d0Params univs) Gamma
      (value path) (value path) (type path))
    (H : @SpineWF (d0Params univs) Gamma A (paths.map value) B) :
    @PathSpineWF (d0Params univs) Gamma alpha value type A paths B := by
  letI : Params := d0Params univs
  generalize hargs : paths.map value = args at H
  induction H generalizing paths with
  | nil =>
    have hpaths : paths = [] := by simpa using hargs
    subst paths
    exact .nil
  | @cons e domain es result codomain harg htail ih =>
    cases paths with
    | nil => simp at hargs
    | cons path paths =>
      simp only [List.map_cons, List.cons.injEq] at hargs
      obtain ⟨hvalue, hrest⟩ := hargs
      subst e
      obtain ⟨_, hdomain⟩ :=
        d0TypeUniq univs hGamma (htyped path) harg
      exact .cons hdomain (ih hrest)
  | @conv Head Head' u es result hHead htail ih =>
    exact .conv hHead (ih hargs)
  | @ret Head es result result' u htail hresult ih =>
    exact .ret (ih hargs) hresult

theorem d0ZeroCaptureValues (univs : Nat)
    {recLs ctorLs : List (@SLevel (d0Params univs))}
    {recArgs ctorArgs : List (@SExpr (d0Params univs))}
    {mcap : (RecursorIotaPattern ``Nat.rec 3 ``Nat.zero 0).Path →
      @SExpr (d0Params univs)}
    (H : @Pattern.MatchesS (d0Params univs)
      (RecursorIotaPattern ``Nat.rec 3 ``Nat.zero 0)
      (@SExpr.app (d0Params univs)
        (recArgs.foldr
          (fun a f => @SExpr.app (d0Params univs) f a)
          (@SExpr.const (d0Params univs) ``Nat.rec recLs))
        (ctorArgs.foldr
          (fun a f => @SExpr.app (d0Params univs) f a)
          (@SExpr.const (d0Params univs) ``Nat.zero ctorLs))) recLs mcap) :
    recArgs.length = 3 ∧ ctorArgs = [] ∧
      (natCapturePaths NatGeneration.flatCtors[0]).map mcap =
        recArgs.reverse := by
  letI : Params := d0Params univs
  cases H with
  | @app fPat recHead recLevels recCap ctorPat ctorHead ctorLevels ctorCap
      hrec hctor =>
    obtain ⟨-, hrecLen, hrecValues⟩ := matchesS_varN_foldr hrec
    obtain ⟨-, hctorLen, -⟩ := matchesS_varN_foldr hctor
    have hctorArgs : ctorArgs = [] := List.length_eq_zero_iff.mp hctorLen
    subst ctorArgs
    refine ⟨hrecLen, rfl, ?_⟩
    rw [natZeroCapturePaths]
    change
      ((Pattern.varNPaths (.const ``Nat.rec) 3).map Sum.inl).map
          (Sum.elim recCap ctorCap) = recArgs.reverse
    simpa [List.map_map, Function.comp_def] using hrecValues

theorem d0SuccCaptureValues (univs : Nat)
    {recLs ctorLs : List (@SLevel (d0Params univs))}
    {recArgs ctorArgs : List (@SExpr (d0Params univs))}
    {mcap : (RecursorIotaPattern ``Nat.rec 3 ``Nat.succ 1).Path →
      @SExpr (d0Params univs)}
    (H : @Pattern.MatchesS (d0Params univs)
      (RecursorIotaPattern ``Nat.rec 3 ``Nat.succ 1)
      (@SExpr.app (d0Params univs)
        (recArgs.foldr
          (fun a f => @SExpr.app (d0Params univs) f a)
          (@SExpr.const (d0Params univs) ``Nat.rec recLs))
        (ctorArgs.foldr
          (fun a f => @SExpr.app (d0Params univs) f a)
          (@SExpr.const (d0Params univs) ``Nat.succ ctorLs))) recLs mcap) :
    recArgs.length = 3 ∧ ctorArgs.length = 1 ∧
      (natCapturePaths NatGeneration.flatCtors[1]).map mcap =
        recArgs.reverse ++ ctorArgs.reverse := by
  letI : Params := d0Params univs
  cases H with
  | @app fPat recHead recLevels recCap ctorPat ctorHead ctorLevels ctorCap
      hrec hctor =>
    obtain ⟨-, hrecLen, hrecValues⟩ := matchesS_varN_foldr hrec
    obtain ⟨-, hctorLen, hctorValues⟩ := matchesS_varN_foldr hctor
    refine ⟨hrecLen, hctorLen, ?_⟩
    rw [natSuccCapturePaths]
    change
      (((Pattern.varNPaths (.const ``Nat.rec) 3).map Sum.inl ++
          (Pattern.varNPaths (.const ``Nat.succ) 1).map Sum.inr).map
        (Sum.elim recCap ctorCap)) = recArgs.reverse ++ ctorArgs.reverse
    simpa [List.map_append, List.map_map, Function.comp_def,
      hrecValues, hctorValues]

def d0ProbeNatZeroRuleType (univs : Nat)
    (level : @SLevel (d0Params univs)) : @SExpr (d0Params univs) :=
  letI : Params := d0Params univs
  SExpr.forallE
    (SExpr.forallE (SExpr.const ``Nat []) (SExpr.sort level))
    (SExpr.forallE
      ((SExpr.bvar 0).app (SExpr.const ``Nat.zero []))
      (SExpr.forallE
        (SExpr.forallE (SExpr.const ``Nat [])
          (SExpr.forallE
            ((SExpr.bvar 2).app (SExpr.bvar 0))
            ((SExpr.bvar 3).app
              ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1)))))
        ((SExpr.bvar 2).app (SExpr.const ``Nat.zero []))))

theorem d0ProbeNatZeroRuleTypeS_eq (univs : Nat)
    (level : @SLevel (d0Params univs)) :
    @SExpr.mkInst (d0Params univs) [level]
        (NatGeneration.rule 0 NatGeneration.flatCtors[0]).type =
      d0ProbeNatZeroRuleType univs level := by
  rw [probeNatZeroRuleTypeV_eq]
  rfl

def d0ProbeNatSuccRuleType (univs : Nat)
    (level : @SLevel (d0Params univs)) : @SExpr (d0Params univs) :=
  letI : Params := d0Params univs
  SExpr.forallE
    (SExpr.forallE (SExpr.const ``Nat []) (SExpr.sort level))
    (SExpr.forallE
      ((SExpr.bvar 0).app (SExpr.const ``Nat.zero []))
      (SExpr.forallE
        (SExpr.forallE (SExpr.const ``Nat [])
          (SExpr.forallE
            ((SExpr.bvar 2).app (SExpr.bvar 0))
            ((SExpr.bvar 3).app
              ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1)))))
        (SExpr.forallE (SExpr.const ``Nat [])
          ((SExpr.bvar 3).app
            ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0))))))

theorem d0ProbeNatSuccRuleTypeS_eq (univs : Nat)
    (level : @SLevel (d0Params univs)) :
    @SExpr.mkInst (d0Params univs) [level]
        (NatGeneration.rule 1 NatGeneration.flatCtors[1]).type =
      d0ProbeNatSuccRuleType univs level := by
  rw [probeNatSuccRuleTypeV_eq]
  rfl

theorem d0IotaRule_nonempty (univs : Nat)
    {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (H : (d0Params univs).Pat
      (RecursorIotaPattern rec major ctor arity) r) :
    Nonempty (@Pattern.IotaRule (d0Params univs)
      rec major ctor arity r) := by
  letI : Params := d0Params univs
  change D0Pat _ _ at H
  cases H with
  | iota H =>
    let oldRule := natIotaRule univs H
    rcases oldRule with
      ⟨oldPat, df, registered, rhsClosed, capturePaths, rhsTower⟩
    exact ⟨{
      pat := D0Pat.iota oldPat
      df := df
      registered := natFinalEnv_le_d0Env.defeqs registered
      rhsClosed := rhsClosed
      capturePaths := capturePaths
      rhsTower := rhsTower }⟩

noncomputable def d0IotaRule (univs : Nat)
    {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (H : (d0Params univs).Pat
      (RecursorIotaPattern rec major ctor arity) r) :
    @Pattern.IotaRule (d0Params univs) rec major ctor arity r :=
  Classical.choice (d0IotaRule_nonempty univs H)

/-- Structural descent survives the D0 environment extension.  Definition
patterns cannot inhabit an iota-pattern index, so the only case is the Nat
rule already certified above; registration is weakened to `d0Env` while the
generated origin is rebased unchanged. -/
theorem d0IotaStructuralDescent (univs : Nat)
    {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (H : (d0Params univs).Pat
      (RecursorIotaPattern rec major ctor arity) r) :
    ∃ rule : @Pattern.IotaRule (d0Params univs) rec major ctor arity r,
      @Pattern.IotaRule.StructuralDescent (d0Params univs)
        rec major ctor arity r rule := by
  letI : Params := d0Params univs
  change D0Pat _ _ at H
  cases H with
  | iota H =>
    obtain ⟨oldRule, hdescent⟩ := natIotaStructuralDescent univs H
    rcases oldRule with
      ⟨oldPat, df, registered, rhsClosed, capturePaths, rhsTower⟩
    let rule : @Pattern.IotaRule (d0Params univs)
        rec major ctor arity r := {
      pat := D0Pat.iota oldPat
      df := df
      registered := natFinalEnv_le_d0Env.defeqs registered
      rhsClosed := rhsClosed
      capturePaths := capturePaths
      rhsTower := rhsTower }
    refine ⟨rule, Pattern.IotaRule.StructuralDescent.rebase
      hdescent rule ?_⟩
    rfl

theorem d0NatRecEnvLookup :
    d0Env.constants ``Nat.rec =
      some (VInductDecl.recConst 0 ``Nat 0 InductiveFixtures.natType) :=
  natFinalEnv_le_d0Env.constants InductiveReplayFixtures.nat_rec_env_lookup

theorem d0NatZeroEnvLookup :
    d0Env.constants ``Nat.zero =
      some InductiveFixtures.natType.ctors[0].toVConstant :=
  natFinalEnv_le_d0Env.constants (by rfl)

theorem d0NatSuccEnvLookup :
    d0Env.constants ``Nat.succ =
      some InductiveFixtures.natType.ctors[1].toVConstant :=
  natFinalEnv_le_d0Env.constants InductiveReplayFixtures.nat_succ_env_lookup

theorem natRule_rhs_ne_d0Def {i : Nat}
    {constructor : NormalizedBlockCtor}
    (hentry : NatGeneration.flatCtors[i]? = some constructor) :
    (NatGeneration.rule i constructor).rhs ≠ d0DefVal.toDefEq.rhs := by
  have hi : i = 0 ∨ i = 1 := by
    obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hentry
    have : NatGeneration.flatCtors.length = 2 := rfl
    omega
  rcases hi with rfl | rfl
  · have hc := Option.some.inj
      (probeNatFlatCtorZero_lookup.symm.trans hentry)
    subst constructor
    native_decide
  · have hc := Option.some.inj
      (probeNatFlatCtorSucc_lookup.symm.trans hentry)
    subst constructor
    native_decide

theorem d0Def_not_ctor (univs : Nat)
    (cl : @CtorBundle.IsCtor (d0Params univs) d0DefVal.name) : False := by
  letI : Params := d0Params univs
  have hshape : ctorLike cl.cl.1 = true := by
    have hs := cl.cl.2.2
    cases hc : cl.cl.1 <;> simp [ctorLike, hc] at hs ⊢
  have hc := cl.cl.2.1
  change d0Classify d0DefVal.name = some cl.cl.1 at hc
  have hcl : cl.cl.1 = .symb 0 := by
    simpa [d0Classify] using hc.symm
  rw [hcl] at hshape
  simp [ctorLike] at hshape

theorem d0Ctor_name_ne_def (univs : Nat) {c : Name}
    (cl : @CtorBundle.IsCtor (d0Params univs) c) :
    c ≠ d0DefVal.name := by
  intro hc
  subst c
  exact d0Def_not_ctor univs cl

@[simp] theorem d0Expr_context_roundtrip (univs : Nat)
    (Gamma : List (@SExpr (d0Params univs))) :
    (Gamma.map (d0ToNatExpr univs)).map (natToD0Expr univs) = Gamma := by
  simp [List.map_map, Function.comp_def]

@[simp] theorem d0Level_list_roundtrip (univs : Nat)
    (ls : List (@SLevel (d0Params univs))) :
    (ls.map (d0ToNatLevel univs)).map (natToD0Level univs) = ls := by
  simp [List.map_map, Function.comp_def]

theorem d0NatTypeStrong (univs : Nat)
    (Gamma : List (@SExpr (d0Params univs))) :
    @IsDefEqStrong (d0Params univs) Gamma
      (@SExpr.const (d0Params univs) ``Nat [])
      (@SExpr.const (d0Params univs) ``Nat [])
      (@SExpr.sort (d0Params univs)
        (@SLevel.succ (d0Params univs) (@SLevel.zero (d0Params univs)))) := by
  have H := natStrongToD0 univs
    (natTypeStrong univs (Gamma.map (d0ToNatExpr univs)))
  simp only [d0Expr_context_roundtrip, natToD0Expr_const,
    natToD0Expr_mkInst, List.map_nil] at H
  change @IsDefEqStrong (d0Params univs) Gamma
    (@SExpr.const (d0Params univs) ``Nat [])
    (@SExpr.const (d0Params univs) ``Nat [])
    (@SExpr.sort (d0Params univs)
      (@SLevel.succ (d0Params univs) (@SLevel.zero (d0Params univs)))) at H
  exact H

theorem d0NatZeroStrong (univs : Nat)
    (Gamma : List (@SExpr (d0Params univs))) :
    @IsDefEqStrong (d0Params univs) Gamma
      (@SExpr.const (d0Params univs) ``Nat.zero [])
      (@SExpr.const (d0Params univs) ``Nat.zero [])
      (@SExpr.const (d0Params univs) ``Nat []) := by
  have H := natStrongToD0 univs
    (natZeroStrong univs (Gamma.map (d0ToNatExpr univs)))
  simpa only [d0Expr_context_roundtrip, natToD0Expr_const,
    List.map_nil] using H

noncomputable def d0Ctor (univs : Nat) {c : Name} {ci : VConstant}
    {ls : List (@SLevel (d0Params univs))}
    {Gamma : List (@SExpr (d0Params univs))}
    (hci : d0Env.constants c = some ci)
    (hlen : ls.length = ci.uvars)
    (cl : @CtorBundle.IsCtor (d0Params univs) c) :
    letI : Params := d0Params univs
    {F : CtorBundle c cl //
      IsDefEqStrong Gamma (SExpr.mkInst ls ci.type)
        (F.rhs ls) (.sort F.u)} := by
  letI : Params := d0Params univs
  let oldGamma := Gamma.map (d0ToNatExpr univs)
  let oldLs := ls.map (d0ToNatLevel univs)
  have oldHci : natFinalEnv.constants c = some ci :=
    d0Env_constants_old (d0Ctor_name_ne_def univs cl) hci
  have oldLen : oldLs.length = ci.uvars := by
    simpa [oldLs] using hlen
  let oldF : @CtorBundle (natParams univs) c (d0CtorToNat univs cl) :=
    (natCtor univs (Gamma := oldGamma) (ls := oldLs)
      oldHci oldLen (d0CtorToNat univs cl)).1
  have oldProof : @IsDefEqStrong (natParams univs) oldGamma
      (@SExpr.mkInst (natParams univs) oldLs ci.type)
      (@CtorBundle.rhs (natParams univs) c (d0CtorToNat univs cl)
        oldF oldLs)
      (@SExpr.sort (natParams univs)
        (@CtorBundle.u (natParams univs) c (d0CtorToNat univs cl) oldF)) :=
    (natCtor univs (Gamma := oldGamma) (ls := oldLs)
      oldHci oldLen (d0CtorToNat univs cl)).2
  let newF := natCtorBundleToD0 univs cl oldF
  refine ⟨newF, ?_⟩
  have H := natStrongToD0 univs oldProof
  dsimp only [oldGamma, oldLs] at H
  simp only [d0Expr_context_roundtrip,
    natToD0Expr_mkInst, natToD0Expr_sort] at H
  rw [natCtorBundleToD0_rhs univs cl oldF
    (ls.map (d0ToNatLevel univs))] at H
  simpa only [newF, d0Level_list_roundtrip,
    natCtorBundleToD0_u] using H

theorem d0DefStrong (univs : Nat)
    (Gamma : List (@SExpr (d0Params univs))) :
    @IsDefEqStrong (d0Params univs) Gamma
      (@SExpr.const (d0Params univs) d0DefVal.name [])
      (@SExpr.const (d0Params univs) ``Nat.zero [])
      (@SExpr.const (d0Params univs) ``Nat []) := by
  letI : Params := d0Params univs
  let r : (Pattern.const d0DefVal.name).RHS ×
      (Pattern.const d0DefVal.name).Check :=
    (.fixed d0DefVal.value d0DefClosed, .true)
  let action : Pattern.Action Gamma r (.const d0DefVal.name []) []
      Empty.elim (.const ``Nat []) := {
    pat := D0Pat.defn
    matched := by
      refine cast ?_ (@Pattern.MatchesS.const (d0Params univs)
        d0DefVal.name [])
      congr 1
      funext path
      exact Empty.elim path
    dfs := []
    defeqs := rfl
    checked := by simp
    sound := by
      have H := @IsDefEq.extra (d0Params univs) d0DefVal.toDefEq Gamma []
        VEnv.addDefEq_self rfl
      change IsDefEq Gamma (.const d0DefVal.name [])
        (.const ``Nat.zero []) (.const ``Nat []) at H
      exact H }
  let F : ∀ cl : CtorBundle.IsCtor d0DefVal.name,
      CtorBundle d0DefVal.name cl := fun cl =>
    (d0Def_not_ctor univs cl).elim
  refine @IsDefEqStrong.defn (d0Params univs) d0DefVal.name
    d0DefVal.toVConstant Gamma []
    (@SLevel.succ (d0Params univs) (@SLevel.zero (d0Params univs))) r
    d0Env_d0Def_lookup rfl ?_ F ?_ action ?_
  · change IsDefEqStrong Gamma (.const ``Nat []) (.const ``Nat [])
      (.sort (.succ .zero))
    exact d0NatTypeStrong univs Gamma
  · intro cl
    exact (d0Def_not_ctor univs cl).elim
  · change IsDefEqStrong Gamma (.const ``Nat.zero [])
      (.const ``Nat.zero []) (.const ``Nat [])
    exact d0NatZeroStrong univs Gamma

theorem d0Defn (univs : Nat) {c : Name}
    {r : (Pattern.const c).RHS × (Pattern.const c).Check}
    (H : (d0Params univs).Pat (.const c) r) :
    ∃ (value : VExpr) (closed : value.Closed),
      r = (.fixed value closed, .true) ∧
      ∀ {ci : VConstant} {ls : List (@SLevel (d0Params univs))}
        {Gamma : List (@SExpr (d0Params univs))},
        d0Env.constants c = some ci → ls.length = ci.uvars →
        @IsDefEqStrong (d0Params univs) Gamma
          (@SExpr.const (d0Params univs) c ls)
          (@SExpr.mkInst (d0Params univs) ls value)
          (@SExpr.mkInst (d0Params univs) ls ci.type) := by
  letI : Params := d0Params univs
  change D0Pat (.const c) r at H
  cases H with
  | iota H => exact (natPat_no_const univs H).elim
  | defn =>
    refine ⟨d0DefVal.value, d0DefClosed, rfl, ?_⟩
    intro ci ls Gamma hci hlen
    have hci' : ci = d0DefVal.toVConstant :=
      Option.some.inj (hci.symm.trans d0Env_d0Def_lookup)
    subst ci
    have hls : ls = [] := List.length_eq_zero_iff.mp hlen
    subst ls
    change @IsDefEqStrong (d0Params univs) Gamma
      (@SExpr.const (d0Params univs) d0DefVal.name [])
      (@SExpr.const (d0Params univs) ``Nat.zero [])
      (@SExpr.const (d0Params univs) ``Nat [])
    exact d0DefStrong univs Gamma

theorem d0Registered (univs : Nat)
    {df : VDefEq} {ls : List (@SLevel (d0Params univs))}
    {Gamma : List (@SExpr (d0Params univs))}
    (hreg : d0Env.defeqs df) (hlen : ls.length = df.uvars)
    (_hLhs : @IsDefEqStrong (d0Params univs) Gamma
      (@SExpr.mkInst (d0Params univs) ls df.lhs)
      (@SExpr.mkInst (d0Params univs) ls df.lhs)
      (@SExpr.mkInst (d0Params univs) ls df.type))
    (_hRhs : @IsDefEqStrong (d0Params univs) Gamma
      (@SExpr.mkInst (d0Params univs) ls df.rhs)
      (@SExpr.mkInst (d0Params univs) ls df.rhs)
      (@SExpr.mkInst (d0Params univs) ls df.type)) :
    @IsDefEqStrong (d0Params univs) Gamma
      (@SExpr.mkInst (d0Params univs) ls df.lhs)
      (@SExpr.mkInst (d0Params univs) ls df.rhs)
      (@SExpr.mkInst (d0Params univs) ls df.type) := by
  rw [d0Env_defeqs_iff] at hreg
  rcases hreg with hdef | hold
  · subst df
    change ls.length = 0 at hlen
    have hls : ls = [] := List.length_eq_zero_iff.mp hlen
    subst ls
    change @IsDefEqStrong (d0Params univs) Gamma
      (@SExpr.const (d0Params univs) d0DefVal.name [])
      (@SExpr.const (d0Params univs) ``Nat.zero [])
      (@SExpr.const (d0Params univs) ``Nat [])
    exact d0DefStrong univs Gamma
  · let oldGamma := Gamma.map (d0ToNatExpr univs)
    let oldLs := ls.map (d0ToNatLevel univs)
    have oldLen : oldLs.length = df.uvars := by
      simpa [oldLs] using hlen
    have oldLhs : @IsDefEqStrong (natParams univs) oldGamma
        (@SExpr.mkInst (natParams univs) oldLs df.lhs)
        (@SExpr.mkInst (natParams univs) oldLs df.lhs)
        (@SExpr.mkInst (natParams univs) oldLs df.type) := by
      letI : Params := natParams univs
      letI : Params.Semantic := natSemantic univs
      exact Params.Semantic.closedHasTypeStrong
        (natFinalEnv_ordered.defEqWF hold).1
    have oldRhs : @IsDefEqStrong (natParams univs) oldGamma
        (@SExpr.mkInst (natParams univs) oldLs df.rhs)
        (@SExpr.mkInst (natParams univs) oldLs df.rhs)
        (@SExpr.mkInst (natParams univs) oldLs df.type) := by
      letI : Params := natParams univs
      letI : Params.Semantic := natSemantic univs
      exact Params.Semantic.closedHasTypeStrong
        (natFinalEnv_ordered.defEqWF hold).2
    have oldEq := natRegistered univs hold oldLen oldLhs oldRhs
    have H := natStrongToD0 univs oldEq
    dsimp only [oldGamma, oldLs] at H
    simpa only [d0Expr_context_roundtrip, natToD0Expr_mkInst,
      d0Level_list_roundtrip] using H

theorem d0IotaSite_nonempty (univs : Nat)
    {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {Gamma : List (@SExpr (d0Params univs))}
    {A majorTerm : @SExpr (d0Params univs)}
    {recLs ctorLs : List (@SLevel (d0Params univs))}
    {recArgs ctorArgs : List (@SExpr (d0Params univs))}
    {mcap : (RecursorIotaPattern rec major ctor arity).Path →
      @SExpr (d0Params univs)}
    (rule : @Pattern.IotaRule (d0Params univs) rec major ctor arity r)
    (captureType : (RecursorIotaPattern rec major ctor arity).Path →
      @SExpr (d0Params univs))
    (captureTyping : @Pattern.CaptureTyping (d0Params univs) Gamma
      (RecursorIotaPattern rec major ctor arity) mcap captureType)
    (hGamma : D0ContextValid univs Gamma)
    (typing : @Pattern.IotaTyping (d0Params univs) Gamma rec ctor recLs ctorLs
      recArgs ctorArgs majorTerm A)
    (matched : @Pattern.MatchesS (d0Params univs)
      (RecursorIotaPattern rec major ctor arity)
      (@SExpr.app (d0Params univs)
        (recArgs.foldr (fun a f => @SExpr.app (d0Params univs) f a)
          (@SExpr.const (d0Params univs) rec recLs))
        (ctorArgs.foldr (fun a f => @SExpr.app (d0Params univs) f a)
          (@SExpr.const (d0Params univs) ctor ctorLs))) recLs mcap)
    (redexSelf : @IsDefEq (d0Params univs) Gamma
      (@SExpr.app (d0Params univs)
        (recArgs.foldr (fun a f => @SExpr.app (d0Params univs) f a)
          (@SExpr.const (d0Params univs) rec recLs))
        (ctorArgs.foldr (fun a f => @SExpr.app (d0Params univs) f a)
          (@SExpr.const (d0Params univs) ctor ctorLs)))
      (@SExpr.app (d0Params univs)
        (recArgs.foldr (fun a f => @SExpr.app (d0Params univs) f a)
          (@SExpr.const (d0Params univs) rec recLs))
        (ctorArgs.foldr (fun a f => @SExpr.app (d0Params univs) f a)
          (@SExpr.const (d0Params univs) ctor ctorLs))) A)
    (AType : ∃ u, @IsDefEq (d0Params univs) Gamma A A
      (@SExpr.sort (d0Params univs) u)) :
    Nonempty (@Pattern.IotaReductionSite (d0Params univs) Gamma rec major ctor
      arity r rule recLs ctorLs recArgs ctorArgs majorTerm A mcap captureType
      captureTyping) := by
  letI : Params := d0Params univs
  have hpatD0 := rule.pat
  change D0Pat _ _ at hpatD0
  have hpat : NatPat (RecursorIotaPattern rec major ctor arity) r := by
    cases hpatD0 with
    | iota H => exact H
  obtain ⟨i, constructor, hentry, hpattern, -⟩ :=
    VInductDecl.BlockGenerationChecked.IotaPat.recover NatGeneration hpat
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
      hpat Hgen .refl (Pattern.inter_self _)).2.2
  have hr' : r = rgen := eq_of_heq hr
  subst r
  rcases rule with
    ⟨rulePat, df, ruleRegistered, rhsClosed, capturePaths, rhsTower⟩
  change NatGeneration.ruleRHS natRuleClosure hentry =
    Pattern.RHS.appN (.fixed df.rhs rhsClosed)
      (capturePaths.map fun path => .var path) at rhsTower
  rw [natRuleRHS_tower hentry] at rhsTower
  obtain ⟨hrhs, hpaths⟩ := rhsFixedAppN_inj rhsTower
  subst capturePaths
  have hi : i = 0 ∨ i = 1 := by
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hentry
    have : NatGeneration.flatCtors.length = 2 := rfl
    omega
  have hregD0 := ruleRegistered
  change d0Env.defeqs df at hregD0
  have hreg : natFinalEnv.defeqs df := by
    rw [d0Env_defeqs_iff] at hregD0
    rcases hregD0 with hnew | hold
    · subst df
      exact (natRule_rhs_ne_d0Def hentry hrhs).elim
    · exact hold
  rw [natFinalEnv_defeqs_iff] at hreg
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hreg
  have hj' : j = 0 ∨ j = 1 := by
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hj
    have : NatGeneration.generatedRules.length = 2 := rfl
    omega
  rcases hi with rfl | rfl <;> rcases hj' with rfl | rfl
  all_goals
    first
    | have hc := Option.some.inj
        (probeNatFlatCtorZero_lookup.symm.trans hentry)
    | have hc := Option.some.inj
        (probeNatFlatCtorSucc_lookup.symm.trans hentry)
    first
    | have hdf := Option.some.inj
        (probeNatGeneratedRuleZero_lookup.symm.trans hj)
    | have hdf := Option.some.inj
        (probeNatGeneratedRuleSucc_lookup.symm.trans hj)
    subst df
  all_goals (try simp at hrhs ⊢)
  case inl.inl =>
    have hrecName : NatGeneration.ruleRecName constructor = ``Nat.rec := by
      rw [← hc]
      exact probeNatZeroRuleRecName
    have hctorName : constructor.ctor.raw.name = ``Nat.zero := by
      rw [← hc]
      exact probeNatZeroCtorName
    simp only [hrecName, hctorName] at typing matched redexSelf
    subst constructor
    have hrecLen := typing.recHead.const_left_levelsLength
      d0NatRecEnvLookup
    change recLs.length = 1 at hrecLen
    obtain ⟨level, rfl⟩ := List.length_eq_one_iff.mp hrecLen
    have hctorLen := typing.ctorHead.const_left_levelsLength
      (ci := InductiveFixtures.natType.ctors[0].toVConstant) d0NatZeroEnvLookup
    change ctorLs.length = 0 at hctorLen
    have hctorLs : ctorLs = [] := List.length_eq_zero_iff.mp hctorLen
    subst ctorLs
    obtain ⟨hrecArgsLen, hctorArgs, hcaptures⟩ :=
      d0ZeroCaptureValues univs matched
    rw [hctorArgs] at typing matched redexSelf ⊢
    have hrecArgs : ∃ x y z, recArgs = [x, y, z] :=
      ⟨recArgs[0], recArgs[1], recArgs[2],
        List.eq_getElem_of_length_eq_three recArgs hrecArgsLen⟩
    obtain ⟨minorSucc, minorZero, motive, rfl⟩ := hrecArgs
    have hrecCanonical : IsDefEq Gamma
        (.const ``Nat.rec [level]) (.const ``Nat.rec [level])
        (SExpr.mkInst [level]
          (VInductDecl.recConst 0 ``Nat 0 InductiveFixtures.natType).type) :=
      .const d0NatRecEnvLookup rfl
    rw [probeNatRecTypeV_eq] at hrecCanonical
    have hheadEq := d0TypeUniq univs hGamma hrecCanonical typing.recHead
    let motiveView := d0SpineConsView univs hGamma hheadEq typing.recSpine
    have hmotive := motiveView.argumentExpected univs
    have hrestMotive := motiveView.restEq univs
    let zeroView := d0SpineConsView univs hGamma hrestMotive motiveView.tail
    have hzero := zeroView.argumentExpected univs
    have hrestZero := zeroView.restEq univs
    let succView := d0SpineConsView univs hGamma hrestZero zeroView.tail
    have hsucc := succView.argumentExpected univs
    have hrestSucc := succView.restEq univs
    let majorView := d0SpineConsView univs hGamma hrestSucc succView.tail
    have hmajor := majorView.argumentExpected univs
    have hprefixMotive := IsDefEq.appDF hrecCanonical hmotive
    have hprefixZero := IsDefEq.appDF hprefixMotive hzero
    have hprefixSucc := IsDefEq.appDF hprefixZero hsucc
    obtain ⟨_, hmajorType⟩ := d0TypeUniq univs hGamma
      typing.majorEq.hasType.1 hmajor
    have hmajorEq := hmajorType.defeqDF typing.majorEq
    have hredexAtGenerated := IsDefEq.appDF hprefixSucc hmajorEq
    have hctorAtRuleResult :=
      IsDefEq.appDF hprefixSucc hmajorEq.hasType.2
    have redexSelf' : IsDefEq Gamma
        (((((SExpr.const ``Nat.rec [level]).app motive).app minorZero).app
          minorSucc).app (SExpr.const ``Nat.zero []))
        (((((SExpr.const ``Nat.rec [level]).app motive).app minorZero).app
          minorSucc).app (SExpr.const ``Nat.zero [])) A := by
      simpa using redexSelf
    obtain ⟨_, hruleMajor⟩ := d0TypeUniq univs hGamma
      hctorAtRuleResult hredexAtGenerated.hasType.2
    obtain ⟨_, hmajorA⟩ := d0TypeUniq univs hGamma
      hredexAtGenerated.hasType.2 redexSelf'
    have hruleA := d0TypesTrans univs hGamma
      ⟨_, hruleMajor⟩ ⟨_, hmajorA⟩
    obtain ⟨ruleSort, hruleA⟩ := hruleA
    have hruleA' : IsDefEq Gamma
        (motive.app (SExpr.const ``Nat.zero [])) A (.sort ruleSort) := by
      simpa [SExpr.mkInst, SExpr.inst, SExpr.subst, Subst.lift,
        Subst.cons, Subst.id, probeCancelThreeLifts] using hruleA
    have hmotive' : IsDefEq Gamma motive motive
        (.forallE (.const ``Nat []) (.sort level)) := by
      simpa [probeNatRecTypeV, SExpr.mkInst, probeInstVParamZero] using hmotive
    have hzero' : IsDefEq Gamma minorZero minorZero
        (motive.app (.const ``Nat.zero [])) := by
      simpa [probeNatRecTypeV, SExpr.mkInst, SExpr.inst, SExpr.subst,
        Subst.lift, Subst.cons, Subst.id] using hzero
    have hsucc' : IsDefEq Gamma minorSucc minorSucc
        (.forallE (SExpr.const ``Nat [])
          (.forallE
            (motive.lift.app (SExpr.bvar 0))
            (motive.lift.lift.app
              ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))))) := by
      simpa [probeNatRecTypeV, SExpr.mkInst, SExpr.inst, SExpr.subst,
        Subst.lift, Subst.cons, Subst.id, probeCancelTwoLifts,
        probeCancelUnderOne, probeCancelUnderTwo,
        probeInstVParamZero] using hsucc
    have hruleAForTelescope : IsDefEq Gamma
        (((((SExpr.bvar 2).app (SExpr.const ``Nat.zero [])).subst
          (Subst.one motive).lift.lift).subst
          (Subst.one minorZero).lift).inst minorSucc)
        A (.sort ruleSort) := by
      simpa [SExpr.inst, SExpr.subst, Subst.lift, Subst.cons,
        Subst.id, probeCancelTwoLifts] using hruleA'
    have hzeroForTelescope : IsDefEq Gamma minorZero minorZero
        (((SExpr.bvar 0).app (SExpr.const ``Nat.zero [])).subst
          (Subst.one motive)) := by
      simpa [SExpr.inst, SExpr.subst, Subst.lift, Subst.cons,
        Subst.id] using hzero'
    have hsuccForTelescope : IsDefEq Gamma minorSucc minorSucc
        (((SExpr.forallE (SExpr.const ``Nat [])
          (SExpr.forallE
            ((SExpr.bvar 2).app (SExpr.bvar 0))
            ((SExpr.bvar 3).app
              ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))))).subst
          (Subst.one motive).lift).subst (Subst.one minorZero)) := by
      simpa [SExpr.inst, SExpr.subst, Subst.lift, Subst.cons,
        Subst.id, probeCancelUnderOne, probeCancelUnderTwo] using hsucc'
    have hcoreExplicit : SpineWF Gamma (d0ProbeNatZeroRuleType univs level)
        [motive, minorZero, minorSucc]
        (((((SExpr.bvar 2).app (SExpr.const ``Nat.zero [])).subst
          (Subst.one motive).lift.lift).subst
          (Subst.one minorZero).lift).inst minorSucc) := by
      exact .cons hmotive' (.cons hzeroForTelescope
        (.cons hsuccForTelescope .nil))
    have hplainExplicit : SpineWF Gamma (d0ProbeNatZeroRuleType univs level)
        [motive, minorZero, minorSucc] A :=
      .ret hcoreExplicit hruleAForTelescope
    have hplain : SpineWF Gamma
        (SExpr.mkInst [level]
          (NatGeneration.rule 0 NatGeneration.flatCtors[0]).type)
        [motive, minorZero, minorSucc] A := by
      rw [d0ProbeNatZeroRuleTypeS_eq]
      exact hplainExplicit
    have hplainPaths : SpineWF Gamma
        (SExpr.mkInst [level]
          (NatGeneration.rule 0 NatGeneration.flatCtors[0]).type)
        ((natCapturePaths NatGeneration.flatCtors[0]).map mcap) A := by
      exact hcaptures.symm ▸ hplain
    have captureSpine := d0PathSpineOfSpineWF univs hGamma
      captureTyping.typed hplainPaths
    let vls : List VLevel := [level.reify]
    have hvls : ∀ l ∈ vls, l.WF univs := by
      intro l hl
      simp only [vls, List.mem_singleton] at hl
      subst l
      exact SLevel.reify_wf level
    have hlhs :=
      (d0Env_ordered.defEqWF ruleRegistered).1.instL hvls
    have hlhsGamma : d0Env.HasType univs (Gamma.map SExpr.reify)
        (probeNatZeroRuleLhsV.instL vls)
        ((NatGeneration.rule 0 NatGeneration.flatCtors[0]).type.instL vls) := by
      rw [← probeNatZeroRuleLhsV_eq]
      exact hlhs.weak0 d0Env_ordered
    unfold probeNatZeroRuleLhsV at hlhsGamma
    rw [VExpr.instL_lamN] at hlhsGamma
    obtain ⟨hTel, bodyType, hbody⟩ :=
      VEnv.HasType.lamN_wf d0Env_ordered hGamma hlhsGamma
    have hmotiveV := hmotive'.reify hGamma
    change d0Env.IsDefEq univs (Gamma.map SExpr.reify)
      motive.reify motive.reify _ at hmotiveV
    have hzeroV := hzeroForTelescope.reify hGamma
    change d0Env.IsDefEq univs (Gamma.map SExpr.reify)
      minorZero.reify minorZero.reify _ at hzeroV
    have hsuccV := hsuccForTelescope.reify hGamma
    change d0Env.IsDefEq univs (Gamma.map SExpr.reify)
      minorSucc.reify minorSucc.reify _ at hsuccV
    have hcoreV : d0Env.SpineWF univs (Gamma.map SExpr.reify)
        (VExpr.forallN (probeNatRuleBindersV.map (VExpr.instL vls))
          (probeNatZeroRuleResultV.instL vls))
        [motive.reify, minorZero.reify, minorSucc.reify]
        (VExpr.instRev (probeNatZeroRuleResultV.instL vls)
          [motive.reify, minorZero.reify, minorSucc.reify]) := by
      refine .cons hmotiveV ?_
      refine .cons ?_ ?_
      · simpa [d0Params, vls, VExpr.instL, SExpr.reify,
          SExpr.reify_subst,
          VExpr.inst_eq, probeReifySubstOne] using
          hzeroV
      refine .cons ?_ .nil
      simpa [d0Params, vls, VExpr.instL, SExpr.reify,
        SExpr.reify_subst,
        SExpr.reify_inst, VExpr.inst_eq, VExpr.instN_eq,
        VExpr.Subst.liftN,
        probeReifySubstOne, probeReifySubstLift] using
        hsuccV
    have hspineV := hcoreV
    have hspineBody := VEnv.SpineWF.retarget hspineV
      (by simp [probeNatRuleBindersV])
      bodyType
    have hcollapseV := VEnv.IsDefEq.appN_lamN d0Env_ordered
      hTel hbody hspineBody (by simp [probeNatRuleBindersV])
    have hlevels :=
      (VEnv.CtxStrong.strong d0Env_ordered hGamma).levelWF
    have hcollapseS := SExpr.IsDefEq.mkS (d0StructureEtaSound univs)
      hcollapseV hlevels
    have hctx : (Gamma.map SExpr.reify).map SExpr.mk = Gamma := by
      rw [List.map_map]
      exact List.map_id''' Gamma fun term _ => SExpr.mk_reify term
    rw [hctx] at hcollapseS
    have hmkInst (e : VExpr) :
        SExpr.mk (e.instL vls) = SExpr.mkInst [level] e := by
      unfold vls
      exact @SExpr.mk_instL_map_reify (d0Params univs) e [level]
    have hlevelMk :
        SLevel.mk (VLevel.inst vls (VLevel.param 0)) = level := by
      simp [vls, probeReifyInstVParamZero, SLevel.mk_reify]
    have hbodyCollapseV :
        (probeNatZeroRuleLhsBodyV.instL vls).instRev
          [motive.reify, minorZero.reify, minorSucc.reify] =
        (((((VExpr.const ``Nat.rec [level.reify]).app motive.reify).app
          minorZero.reify).app minorSucc.reify).app
          (VExpr.const ``Nat.zero [])) := by
      simp [probeNatZeroRuleLhsBodyV, vls, VExpr.instRev, VExpr.instL,
        VExpr.inst, VExpr.instVar, VExpr.liftN, liftVar,
        VExpr.liftN_succ, VExpr.liftN_zero, probeReifyInstVParamZero,
        probeVCancelTwoLifts, VExpr.inst_lift]
      simpa only [VExpr.liftN_zero] using
        probeVCancelTwoLifts motive.reify minorZero.reify minorSucc.reify
    rw [hbodyCollapseV] at hcollapseS
    have hcollapseCanonical : IsDefEq Gamma
        ([motive, minorZero, minorSucc].foldl
          (fun (f a : SExpr) => f.app a)
          (SExpr.mkInst [level]
            (NatGeneration.rule 0 NatGeneration.flatCtors[0]).lhs))
        (((((SExpr.const ``Nat.rec [level]).app motive).app minorZero).app
          minorSucc).app (SExpr.const ``Nat.zero []))
        (SExpr.mk (bodyType.instRev
          [motive.reify, minorZero.reify, minorSucc.reify])) := by
      rw [probeNatZeroRuleLhsV_eq]
      simpa [vls, hmkInst, hlevelMk, probeNatZeroRuleLhsV,
        probeNatRuleBindersV, probeNatZeroRuleLhsBodyV,
        VExpr.lamN, VExpr.appN,
        probeVCancelTwoLifts, VExpr.inst_lift, SExpr.mk,
        SExpr.mkInst] using
        hcollapseS
    obtain ⟨_, hcollapseType⟩ := d0TypeUniq univs hGamma
      hcollapseCanonical.hasType.2 redexSelf'
    have lhsCollapseCanonical : IsDefEq Gamma
        (((((SExpr.const ``Nat.rec [level]).app motive).app minorZero).app
          minorSucc).app (SExpr.const ``Nat.zero []))
        ([motive, minorZero, minorSucc].foldl
          (fun (f a : SExpr) => f.app a)
          (SExpr.mkInst [level]
            (NatGeneration.rule 0 NatGeneration.flatCtors[0]).lhs)) A :=
      hcollapseType.defeqDF hcollapseCanonical.symm
    refine ⟨{
      typing := typing
      matched := matched
      levelsLength := by rfl
      captureSpine := captureSpine
      lhsCollapse := ?_
      dfs := []
      defeqs := by rfl
      checked := by simp }⟩
    simpa [probeNatZeroRuleRecName] using
      (hcaptures.symm ▸ lhsCollapseCanonical)
  case inl.inr =>
    subst constructor
    exact (probeNatRuleRhs_ne (by simpa using hrhs)).elim
  case inr.inl =>
    subst constructor
    exact (probeNatRuleRhs_ne (by simpa using hrhs.symm)).elim
  case inr.inr =>
    have hrecName : NatGeneration.ruleRecName constructor = ``Nat.rec := by
      rw [← hc]
      exact probeNatSuccRuleRecName
    have hctorName : constructor.ctor.raw.name = ``Nat.succ := by
      rw [← hc]
      exact probeNatSuccCtorName
    simp only [hrecName, hctorName] at typing matched redexSelf
    subst constructor
    have hrecLen := typing.recHead.const_left_levelsLength
      d0NatRecEnvLookup
    change recLs.length = 1 at hrecLen
    obtain ⟨level, rfl⟩ := List.length_eq_one_iff.mp hrecLen
    have hctorLen := typing.ctorHead.const_left_levelsLength
      d0NatSuccEnvLookup
    change ctorLs.length = 0 at hctorLen
    have hctorLs : ctorLs = [] := List.length_eq_zero_iff.mp hctorLen
    subst ctorLs
    obtain ⟨hrecArgsLen, hctorArgsLen, hcaptures⟩ :=
      d0SuccCaptureValues univs matched
    obtain ⟨pred, rfl⟩ := List.length_eq_one_iff.mp hctorArgsLen
    have hrecArgs : ∃ x y z, recArgs = [x, y, z] :=
      ⟨recArgs[0], recArgs[1], recArgs[2],
        List.eq_getElem_of_length_eq_three recArgs hrecArgsLen⟩
    obtain ⟨minorSucc, minorZero, motive, rfl⟩ := hrecArgs
    have hrecCanonical : IsDefEq Gamma
        (.const ``Nat.rec [level]) (.const ``Nat.rec [level])
        (SExpr.mkInst [level]
          (VInductDecl.recConst 0 ``Nat 0 InductiveFixtures.natType).type) :=
      .const d0NatRecEnvLookup rfl
    rw [probeNatRecTypeV_eq] at hrecCanonical
    have hheadEq := d0TypeUniq univs hGamma hrecCanonical typing.recHead
    let motiveView := d0SpineConsView univs hGamma hheadEq typing.recSpine
    have hmotive := motiveView.argumentExpected univs
    have hrestMotive := motiveView.restEq univs
    let zeroView := d0SpineConsView univs hGamma hrestMotive motiveView.tail
    have hzero := zeroView.argumentExpected univs
    have hrestZero := zeroView.restEq univs
    let succView := d0SpineConsView univs hGamma hrestZero zeroView.tail
    have hsucc := succView.argumentExpected univs
    have hrestSucc := succView.restEq univs
    let majorView := d0SpineConsView univs hGamma hrestSucc succView.tail
    have hmajor := majorView.argumentExpected univs
    have hctorCanonical : IsDefEq Gamma
        (.const ``Nat.succ []) (.const ``Nat.succ [])
        (SExpr.mkInst [] InductiveFixtures.natType.ctors[1].type) :=
      .const d0NatSuccEnvLookup rfl
    rw [probeNatSuccCtorTypeV_eq] at hctorCanonical
    have hctorCanonical' : IsDefEq Gamma
        (.const ``Nat.succ []) (.const ``Nat.succ [])
        (.forallE (.const ``Nat []) (.const ``Nat [])) := by
      simpa [SExpr.mkInst] using hctorCanonical
    have hctorType := d0TypeUniq univs hGamma
      hctorCanonical' typing.ctorHead
    let predView := d0SpineConsView univs hGamma hctorType typing.ctorSpine
    have hpred := predView.argumentExpected univs
    have hpred' : IsDefEq Gamma pred pred (.const ``Nat []) := by
      simpa using hpred
    have hprefixMotive := IsDefEq.appDF hrecCanonical hmotive
    have hprefixZero := IsDefEq.appDF hprefixMotive hzero
    have hprefixSucc := IsDefEq.appDF hprefixZero hsucc
    obtain ⟨_, hmajorType⟩ := d0TypeUniq univs hGamma
      typing.majorEq.hasType.1 hmajor
    have hmajorEq := hmajorType.defeqDF typing.majorEq
    have hredexAtGenerated := IsDefEq.appDF hprefixSucc hmajorEq
    have hctorAtRuleResult :=
      IsDefEq.appDF hprefixSucc hmajorEq.hasType.2
    have redexSelf' : IsDefEq Gamma
        (((((SExpr.const ``Nat.rec [level]).app motive).app minorZero).app
          minorSucc).app
            ((SExpr.const ``Nat.succ []).app pred))
        (((((SExpr.const ``Nat.rec [level]).app motive).app minorZero).app
          minorSucc).app
            ((SExpr.const ``Nat.succ []).app pred)) A := by
      simpa using redexSelf
    obtain ⟨_, hruleMajor⟩ := d0TypeUniq univs hGamma
      hctorAtRuleResult hredexAtGenerated.hasType.2
    obtain ⟨_, hmajorA⟩ := d0TypeUniq univs hGamma
      hredexAtGenerated.hasType.2 redexSelf'
    have hruleA := d0TypesTrans univs hGamma
      ⟨_, hruleMajor⟩ ⟨_, hmajorA⟩
    obtain ⟨ruleSort, hruleA⟩ := hruleA
    have hruleA' : IsDefEq Gamma
        (motive.app ((SExpr.const ``Nat.succ []).app pred)) A
        (.sort ruleSort) := by
      simpa [SExpr.mkInst, SExpr.inst, SExpr.subst, Subst.lift,
        Subst.cons, Subst.id, probeCancelThreeLifts] using hruleA
    have hmotive' : IsDefEq Gamma motive motive
        (.forallE (.const ``Nat []) (.sort level)) := by
      simpa [probeNatRecTypeV, SExpr.mkInst, probeInstVParamZero] using hmotive
    have hzero' : IsDefEq Gamma minorZero minorZero
        (motive.app (.const ``Nat.zero [])) := by
      simpa [probeNatRecTypeV, SExpr.mkInst, SExpr.inst, SExpr.subst,
        Subst.lift, Subst.cons, Subst.id] using hzero
    have hsucc' : IsDefEq Gamma minorSucc minorSucc
        (.forallE (SExpr.const ``Nat [])
          (.forallE
            (motive.lift.app (SExpr.bvar 0))
            (motive.lift.lift.app
              ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))))) := by
      simpa [probeNatRecTypeV, SExpr.mkInst, SExpr.inst, SExpr.subst,
        Subst.lift, Subst.cons, Subst.id, probeCancelTwoLifts,
        probeCancelUnderOne, probeCancelUnderTwo,
        probeInstVParamZero] using hsucc
    have hruleAForTelescope : IsDefEq Gamma
        ((((((SExpr.bvar 3).app
          ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0))).subst
            (Subst.one motive).lift.lift.lift).subst
            (Subst.one minorZero).lift.lift).subst
            (Subst.one minorSucc).lift).inst pred)
        A (.sort ruleSort) := by
      simpa [SExpr.inst, SExpr.subst, Subst.lift, Subst.cons,
        Subst.id, probeCancelThreeLifts] using hruleA'
    have hzeroForTelescope : IsDefEq Gamma minorZero minorZero
        (((SExpr.bvar 0).app (SExpr.const ``Nat.zero [])).subst
          (Subst.one motive)) := by
      simpa [SExpr.inst, SExpr.subst, Subst.lift, Subst.cons,
        Subst.id] using hzero'
    have hsuccForTelescope : IsDefEq Gamma minorSucc minorSucc
        (((SExpr.forallE (SExpr.const ``Nat [])
          (SExpr.forallE
            ((SExpr.bvar 2).app (SExpr.bvar 0))
            ((SExpr.bvar 3).app
              ((SExpr.const ``Nat.succ []).app (SExpr.bvar 1))))).subst
          (Subst.one motive).lift).subst (Subst.one minorZero)) := by
      simpa [SExpr.inst, SExpr.subst, Subst.lift, Subst.cons,
        Subst.id, probeCancelUnderOne, probeCancelUnderTwo] using hsucc'
    have hcoreExplicit : SpineWF Gamma (d0ProbeNatSuccRuleType univs level)
        [motive, minorZero, minorSucc, pred]
        ((((((SExpr.bvar 3).app
          ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0))).subst
            (Subst.one motive).lift.lift.lift).subst
            (Subst.one minorZero).lift.lift).subst
            (Subst.one minorSucc).lift).inst pred) := by
      exact .cons hmotive' (.cons hzeroForTelescope
        (.cons hsuccForTelescope (.cons hpred' .nil)))
    have hplainExplicit : SpineWF Gamma (d0ProbeNatSuccRuleType univs level)
        [motive, minorZero, minorSucc, pred] A :=
      .ret hcoreExplicit hruleAForTelescope
    have hplain : SpineWF Gamma
        (SExpr.mkInst [level]
          (NatGeneration.rule 1 NatGeneration.flatCtors[1]).type)
        [motive, minorZero, minorSucc, pred] A := by
      rw [d0ProbeNatSuccRuleTypeS_eq]
      exact hplainExplicit
    have hplainPaths : SpineWF Gamma
        (SExpr.mkInst [level]
          (NatGeneration.rule 1 NatGeneration.flatCtors[1]).type)
        ((natCapturePaths NatGeneration.flatCtors[1]).map mcap) A := by
      exact hcaptures.symm ▸ hplain
    have captureSpine := d0PathSpineOfSpineWF univs hGamma
      captureTyping.typed hplainPaths
    let vls : List VLevel := [level.reify]
    have hvls : ∀ l ∈ vls, l.WF univs := by
      intro l hl
      simp only [vls, List.mem_singleton] at hl
      subst l
      exact SLevel.reify_wf level
    have hlhs :=
      (d0Env_ordered.defEqWF ruleRegistered).1.instL hvls
    have hlhsGamma : d0Env.HasType univs (Gamma.map SExpr.reify)
        (probeNatSuccRuleLhsV.instL vls)
        ((NatGeneration.rule 1 NatGeneration.flatCtors[1]).type.instL vls) := by
      rw [← probeNatSuccRuleLhsV_eq]
      exact hlhs.weak0 d0Env_ordered
    unfold probeNatSuccRuleLhsV at hlhsGamma
    rw [VExpr.instL_lamN] at hlhsGamma
    obtain ⟨hTel, bodyType, hbody⟩ :=
      VEnv.HasType.lamN_wf d0Env_ordered hGamma hlhsGamma
    have hmotiveV := hmotive'.reify hGamma
    change d0Env.IsDefEq univs (Gamma.map SExpr.reify)
      motive.reify motive.reify _ at hmotiveV
    have hzeroV := hzeroForTelescope.reify hGamma
    change d0Env.IsDefEq univs (Gamma.map SExpr.reify)
      minorZero.reify minorZero.reify _ at hzeroV
    have hsuccV := hsuccForTelescope.reify hGamma
    change d0Env.IsDefEq univs (Gamma.map SExpr.reify)
      minorSucc.reify minorSucc.reify _ at hsuccV
    have hpredV := hpred'.reify hGamma
    change d0Env.IsDefEq univs (Gamma.map SExpr.reify)
      pred.reify pred.reify _ at hpredV
    have hcoreV : d0Env.SpineWF univs (Gamma.map SExpr.reify)
        (VExpr.forallN
          (probeNatSuccRuleBindersV.map (VExpr.instL vls))
          (probeNatSuccRuleResultV.instL vls))
        [motive.reify, minorZero.reify, minorSucc.reify, pred.reify]
        (VExpr.instRev (probeNatSuccRuleResultV.instL vls)
          [motive.reify, minorZero.reify, minorSucc.reify, pred.reify]) := by
      refine .cons hmotiveV ?_
      refine .cons ?_ ?_
      · simpa [d0Params, vls, VExpr.instL, SExpr.reify,
          SExpr.reify_subst, VExpr.inst_eq, probeReifySubstOne] using hzeroV
      refine .cons ?_ ?_
      · simpa [d0Params, vls, VExpr.instL, SExpr.reify,
          SExpr.reify_subst, SExpr.reify_inst, VExpr.inst_eq,
          VExpr.instN_eq, VExpr.Subst.liftN, probeReifySubstOne,
          probeReifySubstLift] using hsuccV
      refine .cons ?_ .nil
      simpa [d0Params, vls, VExpr.instL, VExpr.inst, SExpr.reify] using hpredV
    have hspineBody := VEnv.SpineWF.retarget hcoreV
      (by simp [probeNatSuccRuleBindersV, probeNatRuleBindersV]) bodyType
    have hcollapseV := VEnv.IsDefEq.appN_lamN d0Env_ordered
      hTel hbody hspineBody
      (by simp [probeNatSuccRuleBindersV, probeNatRuleBindersV])
    have hlevels :=
      (VEnv.CtxStrong.strong d0Env_ordered hGamma).levelWF
    have hcollapseS := SExpr.IsDefEq.mkS (d0StructureEtaSound univs)
      hcollapseV hlevels
    have hctx : (Gamma.map SExpr.reify).map SExpr.mk = Gamma := by
      rw [List.map_map]
      exact List.map_id''' Gamma fun term _ => SExpr.mk_reify term
    rw [hctx] at hcollapseS
    have hmkInst (e : VExpr) :
        SExpr.mk (e.instL vls) = SExpr.mkInst [level] e := by
      unfold vls
      exact @SExpr.mk_instL_map_reify (d0Params univs) e [level]
    have hlevelMk :
        SLevel.mk (VLevel.inst vls (VLevel.param 0)) = level := by
      simp [vls, probeReifyInstVParamZero, SLevel.mk_reify]
    have hbodyCollapseV :
        (probeNatSuccRuleLhsBodyV.instL vls).instRev
          [motive.reify, minorZero.reify, minorSucc.reify, pred.reify] =
        (((((VExpr.const ``Nat.rec [level.reify]).app motive.reify).app
          minorZero.reify).app minorSucc.reify).app
          ((VExpr.const ``Nat.succ []).app pred.reify)) := by
      simp [probeNatSuccRuleLhsBodyV, vls, VExpr.instRev, VExpr.instL,
        VExpr.inst, VExpr.instVar, VExpr.liftN, liftVar,
        VExpr.liftN_succ, VExpr.liftN_zero, probeReifyInstVParamZero,
        probeVCancelThreeLifts, probeVCancelTwoLifts, VExpr.inst_lift]
      constructor
      · simpa only [VExpr.liftN_zero] using
          probeVCancelThreeLifts motive.reify minorZero.reify
            minorSucc.reify pred.reify
      · simpa only [VExpr.liftN_zero] using
          probeVCancelTwoLifts minorZero.reify minorSucc.reify pred.reify
    rw [hbodyCollapseV] at hcollapseS
    have hcollapseCanonical : IsDefEq Gamma
        ([motive, minorZero, minorSucc, pred].foldl
          (fun (f a : SExpr) => f.app a)
          (SExpr.mkInst [level]
            (NatGeneration.rule 1 NatGeneration.flatCtors[1]).lhs))
        (((((SExpr.const ``Nat.rec [level]).app motive).app minorZero).app
          minorSucc).app ((SExpr.const ``Nat.succ []).app pred))
        (SExpr.mk (bodyType.instRev
          [motive.reify, minorZero.reify, minorSucc.reify, pred.reify])) := by
      rw [probeNatSuccRuleLhsV_eq]
      simpa [vls, hmkInst, hlevelMk, probeNatSuccRuleLhsV,
        probeNatSuccRuleBindersV, probeNatRuleBindersV,
        probeNatSuccRuleLhsBodyV, VExpr.lamN, VExpr.appN,
        probeVCancelThreeLifts, probeVCancelTwoLifts, VExpr.inst_lift,
        SExpr.mk, SExpr.mkInst] using hcollapseS
    obtain ⟨_, hcollapseType⟩ := d0TypeUniq univs hGamma
      hcollapseCanonical.hasType.2 redexSelf'
    have lhsCollapseCanonical : IsDefEq Gamma
        (((((SExpr.const ``Nat.rec [level]).app motive).app minorZero).app
          minorSucc).app ((SExpr.const ``Nat.succ []).app pred))
        ([motive, minorZero, minorSucc, pred].foldl
          (fun (f a : SExpr) => f.app a)
          (SExpr.mkInst [level]
            (NatGeneration.rule 1 NatGeneration.flatCtors[1]).lhs)) A :=
      hcollapseType.defeqDF hcollapseCanonical.symm
    refine ⟨{
      typing := typing
      matched := matched
      levelsLength := by rfl
      captureSpine := captureSpine
      lhsCollapse := ?_
      dfs := []
      defeqs := by rfl
      checked := by simp }⟩
    simpa [probeNatSuccRuleRecName] using
      (hcaptures.symm ▸ lhsCollapseCanonical)
noncomputable def d0IotaSite (univs : Nat)
    {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {Gamma : List (@SExpr (d0Params univs))}
    {A majorTerm : @SExpr (d0Params univs)}
    {recLs ctorLs : List (@SLevel (d0Params univs))}
    {recArgs ctorArgs : List (@SExpr (d0Params univs))}
    {mcap : (RecursorIotaPattern rec major ctor arity).Path →
      @SExpr (d0Params univs)}
    (rule : @Pattern.IotaRule (d0Params univs) rec major ctor arity r)
    (captureType : (RecursorIotaPattern rec major ctor arity).Path →
      @SExpr (d0Params univs))
    (captureTyping : @Pattern.CaptureTyping (d0Params univs) Gamma
      (RecursorIotaPattern rec major ctor arity) mcap captureType)
    (hGamma : D0ContextValid univs Gamma)
    (typing : @Pattern.IotaTyping (d0Params univs) Gamma rec ctor recLs ctorLs
      recArgs ctorArgs majorTerm A)
    (matched : @Pattern.MatchesS (d0Params univs)
      (RecursorIotaPattern rec major ctor arity)
      (@SExpr.app (d0Params univs)
        (recArgs.foldr (fun a f => @SExpr.app (d0Params univs) f a)
          (@SExpr.const (d0Params univs) rec recLs))
        (ctorArgs.foldr (fun a f => @SExpr.app (d0Params univs) f a)
          (@SExpr.const (d0Params univs) ctor ctorLs))) recLs mcap)
    (redexSelf : @IsDefEq (d0Params univs) Gamma
      (@SExpr.app (d0Params univs)
        (recArgs.foldr (fun a f => @SExpr.app (d0Params univs) f a)
          (@SExpr.const (d0Params univs) rec recLs))
        (ctorArgs.foldr (fun a f => @SExpr.app (d0Params univs) f a)
          (@SExpr.const (d0Params univs) ctor ctorLs)))
      (@SExpr.app (d0Params univs)
        (recArgs.foldr (fun a f => @SExpr.app (d0Params univs) f a)
          (@SExpr.const (d0Params univs) rec recLs))
        (ctorArgs.foldr (fun a f => @SExpr.app (d0Params univs) f a)
          (@SExpr.const (d0Params univs) ctor ctorLs))) A)
    (AType : ∃ u, @IsDefEq (d0Params univs) Gamma A A
      (@SExpr.sort (d0Params univs) u)) :
    @Pattern.IotaReductionSite (d0Params univs) Gamma rec major ctor arity r
      rule recLs ctorLs recArgs ctorArgs majorTerm A mcap captureType
      captureTyping :=
  Classical.choice (d0IotaSite_nonempty univs rule captureType captureTyping
    hGamma typing matched redexSelf AType)

/-- The complete D0b bridge: generated Nat iota plus the checked `d0def`
unfolding, all against the extended environment. -/
noncomputable def d0Semantic (univs : Nat) :
    letI : Params := d0Params univs
    Params.Semantic := by
  letI : Params := d0Params univs
  exact {
  structureEta := by
    intro rule levels Gamma params major hreg
    exact (d0Env_no_structEta rule hreg).elim
  ctor := by
    intro c ci ls Gamma hci hlen cl
    exact d0Ctor univs hci hlen cl
  defn := by
    intro c r hpat
    exact d0Defn univs hpat
  iotaRule := by
    intro rec major ctor arity r hpat
    exact d0IotaRule univs hpat
  iotaSite := by
    intro rec major ctor arity r Gamma A majorTerm recLs ctorLs
      recArgs ctorArgs mcap rule captureType captureTyping hGamma typing
      matched redexSelf AType
    exact d0IotaSite univs rule captureType captureTyping hGamma typing
      matched redexSelf AType
  registered := by
    intro df ls Gamma hreg hlen hLhs hRhs
    exact d0Registered univs hreg hlen hLhs hRhs }

/-! ## Concrete δ-rank certificates

The adequacy fixpoint unfolds definitions under an outer induction on this
rank.  The generated Nat inventory has no constant-headed definition rules;
the D0 extension has exactly `d0def ≡ Nat.zero`, so its body lives at rank
zero below the definition head at rank one. -/

/-- Literal δ-rank for D0.  Non-definition heads sit at rank zero. -/
def d0DeltaRankFn : Name → Nat :=
  fun n => if n = ``d0def then 1 else 0

theorem d0DeltaRankFn_nat : d0DeltaRankFn ``Nat ≤ 0 := by decide

theorem d0DeltaRankFn_natZero : d0DeltaRankFn ``Nat.zero ≤ 0 := by
  decide

theorem d0NatTypeLookup :
    d0Env.constants ``Nat = some InductiveFixtures.natType.toVConstant :=
  natFinalEnv_le_d0Env.constants InductiveReplayFixtures.nat_type_env_lookup

/-- `Nat : Type` at rank zero, at every positive stratification depth. -/
theorem d0NatCertR (univs : Nat) :
    letI : Params := d0Params univs
    ∀ (Gamma : List SExpr) (n : Nat),
      HasTypeStratifiedR d0DeltaRankFn Gamma
        (.const ``Nat []) (.sort (.instV [] (.succ .zero))) true (n + 1) 0 := by
  letI : Params := d0Params univs
  intro Gamma n
  exact .base (.const d0NatTypeLookup rfl d0DeltaRankFn_nat
    (.base .sort'))

/-- `Nat.zero : Nat` at rank zero, the certificate consumed by `d0def`. -/
theorem d0ZeroCertR (univs : Nat) :
    letI : Params := d0Params univs
    ∀ (Gamma : List SExpr),
      HasTypeStratifiedR d0DeltaRankFn Gamma
        (.const ``Nat.zero []) (.const ``Nat []) true 2 0 := by
  letI : Params := d0Params univs
  intro Gamma
  exact .base (.const d0NatZeroEnvLookup rfl d0DeltaRankFn_natZero
    (d0NatCertR univs Gamma 0))

/-- The iota-only Nat fixture has no definitional-unfold obligations. -/
def natDeltaRank (univs : Nat) :
    letI : Params := natParams univs
    Params.DeltaRank := by
  letI : Params := natParams univs
  refine ⟨d0DeltaRankFn, ?_⟩
  intro c ci value closed ls Gamma hpat hreg hlen
  exact (natPat_no_const univs hpat).elim

/-- The D0 fixture's checked δ-rank certificate. -/
def d0DeltaRank (univs : Nat) :
    letI : Params := d0Params univs
    Params.DeltaRank := by
  letI : Params := d0Params univs
  refine ⟨d0DeltaRankFn, ?_⟩
  intro c ci value closed ls Gamma hpat hreg hlen
  change D0Pat _ _ at hpat
  cases hpat with
  | iota h => exact (natPat_no_const univs h).elim
  | defn =>
    obtain rfl := Option.some.inj (d0Env_d0Def_lookup.symm.trans hreg)
    obtain rfl := List.length_eq_zero_iff.mp hlen
    exact ⟨2, 0, by decide, d0ZeroCertR univs Gamma⟩

/-- The generated Nat environment inhabits the classified normalization
fragment.  Its only iota rules carry `NatGeneration` origins; the non-Prop
argument law is the generic consequence of its semantic constructor
bundles. -/
theorem natClassified (univs : Nat)
    [semantic : @Params.Semantic (natParams univs)] :
    letI : Params := natParams univs
    letI : Params.DeltaRank := natDeltaRank univs
    Params.Classified := by
  letI : Params := natParams univs
  letI : Params.Semantic := semantic
  letI : Params.DeltaRank := natDeltaRank univs
  exact {
    iotaDescent := natIotaStructuralDescent univs
    argumentNonProp := Params.patternArgumentNonProp }

/-- The zero-arity definition extension preserves the classified boundary;
`d0DeltaRank` supplies its one strict delta edge. -/
theorem d0Classified (univs : Nat)
    [semantic : @Params.Semantic (d0Params univs)] :
    letI : Params := d0Params univs
    letI : Params.DeltaRank := d0DeltaRank univs
    Params.Classified := by
  letI : Params := d0Params univs
  letI : Params.Semantic := semantic
  letI : Params.DeltaRank := d0DeltaRank univs
  exact {
    iotaDescent := d0IotaStructuralDescent univs
    argumentNonProp := Params.patternArgumentNonProp }

/-- End-to-end D0a smoke theorem: the generated Nat fixture supplies every
semantic certificate required by the experimental sort-injectivity bridge.
Conditional on the two L4L-16C′w leaf inputs at the fixture instance. -/
theorem natSortInvS (univs : Nat) {Gamma : List VExpr} {u v : VLevel}
    (piInv : @LRS.PiPathInv (natParams univs))
    (linkRect : ∀ Γ, @LR.MajorLinkRect (natParams univs) Γ)
    (hGamma : OnCtx Gamma (natFinalEnv.IsType univs))
    (h : natFinalEnv.IsDefEqU univs Gamma (.sort u) (.sort v)) : u ≈ v := by
  letI : Params := natParams univs
  letI : Params.Semantic := natSemantic univs
  exact VEnv.IsDefEqU.sort_invS piInv linkRect hGamma h

/-- End-to-end D0b endpoint for the combined L4L-16/17 deliverable.
Conditional on the two L4L-16C′w leaf inputs at the fixture instance. -/
theorem d0SortInvS (univs : Nat) {Gamma : List VExpr} {u v : VLevel}
    (piInv : @LRS.PiPathInv (d0Params univs))
    (linkRect : ∀ Γ, @LR.MajorLinkRect (d0Params univs) Γ)
    (hGamma : OnCtx Gamma (d0Env.IsType univs))
    (h : d0Env.IsDefEqU univs Gamma (.sort u) (.sort v)) : u ≈ v := by
  letI : Params := d0Params univs
  letI : Params.Semantic := d0Semantic univs
  exact VEnv.IsDefEqU.sort_invS piInv linkRect hGamma h

/--
info: 'Lean4Lean.SExpr.ParamsD0.d0SortInvS' depends on axioms: [propext,
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
 probeNatZeroRuleTypeV_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d0SortInvS


end SemanticCertificates

end ParamsD0
end SExpr
end Lean4Lean
