import Lean4Lean.Experimental.SExprParamsD0

/-!
# L4L-16D1: mutual definitions over the D0 fixture

This module extends the kernel-checked D0 instance
(`Lean4Lean/Experimental/SExprParamsD0.lean`) with the next staged slice of
live-environment coverage: a checked `mutualDef` declaration block.  The two
new definitions form an honest mutual package — the first body refers to the
second constant, which only the block-level `VDecl.WF.mutualDef` rule can
check — and the second body chains into the D0 definition, so unfolding now
crosses three definition layers before reaching a constructor.

The complete `Params`/`Params.Semantic` instance pair is rebuilt over the
extended environment by the same transport discipline D0 used over D0a:
old strong derivations cross instances through an explicit syntax functor,
while the iota reduction sites are replayed against the extended environment
itself, never cast back into the smaller one.

The quotient half of the D1 plan line (`CertifiedExtension.quot`) is
deliberately not instantiated here; the current `CtorBundle.hu0` interface
obligation is unsatisfiable for `Quot.mk` (a `Prop`-instantiable
    constructor, exactly the Prop-pattern boundary summarized in
    `plans/roadmap.md` under the D and NORM work packages).  See the
    obstruction record at the end of this file.
-/

namespace Lean4Lean
namespace SExpr
namespace ParamsD1

open InductiveFixtures InductiveReplayFixtures VInductDecl
open ParamsD0

/-! ## D1 declaration layer

Host declarations supply stable kernel names; the Theory payloads are spelled
out explicitly below. -/

/-- Host anchor for the second mutual definition: one more successor over the
checked D0 definition. -/
def d1mutB : Nat := Nat.succ ParamsD0.d0def

/-- Host anchor for the first mutual definition.  Its body is the *other*
member of the block, so its Theory value can only be checked after both
constants are added — the `mutualDef` shape. -/
def d1mutA : Nat := d1mutB

/-- Theory payload for `d1mutA : Nat := d1mutB`.  The value refers to the
block-mate constant `d1mutB`, which is *not* in scope for a plain `.def`
history step. -/
def d1MutAVal : VDefVal where
  name := ``d1mutA
  uvars := 0
  type := .const ``Nat []
  value := .const ``d1mutB []

/-- Theory payload for `d1mutB : Nat := Nat.succ d0def`. -/
def d1MutBVal : VDefVal where
  name := ``d1mutB
  uvars := 0
  type := .const ``Nat []
  value := .app (.const ``Nat.succ []) (.const ``d0def [])

/-- The mutual block, in declaration order. -/
def d1Muts : List VDefVal := [d1MutAVal, d1MutBVal]

theorem d1MutA_fresh : d0Env.constants d1MutAVal.name = none := by
  native_decide

theorem d1MutB_fresh : d0Env.constants d1MutBVal.name = none := by
  native_decide

theorem d1MutA_name_ne_nat : d1MutAVal.name ≠ ``Nat := by native_decide
theorem d1MutA_name_ne_natZero : d1MutAVal.name ≠ ``Nat.zero := by
  native_decide
theorem d1MutA_name_ne_natSucc : d1MutAVal.name ≠ ``Nat.succ := by
  native_decide
theorem d1MutA_name_ne_natRec : d1MutAVal.name ≠ ``Nat.rec := by
  native_decide
theorem d1MutA_name_ne_d0Def : d1MutAVal.name ≠ d0DefVal.name := by
  native_decide
theorem d1MutB_name_ne_nat : d1MutBVal.name ≠ ``Nat := by native_decide
theorem d1MutB_name_ne_natZero : d1MutBVal.name ≠ ``Nat.zero := by
  native_decide
theorem d1MutB_name_ne_natSucc : d1MutBVal.name ≠ ``Nat.succ := by
  native_decide
theorem d1MutB_name_ne_natRec : d1MutBVal.name ≠ ``Nat.rec := by
  native_decide
theorem d1MutB_name_ne_d0Def : d1MutBVal.name ≠ d0DefVal.name := by
  native_decide
theorem d1MutA_name_ne_mutB : d1MutAVal.name ≠ d1MutBVal.name := by
  native_decide

local instance : Inhabited VEnv := ⟨VEnv.empty⟩

/-- The environment after the block's constants but before its equations. -/
def d1ConstEnvA :=
  (d0Env.addConst d1MutAVal.name d1MutAVal.toVConstant).get!

def d1ConstEnv :=
  (d1ConstEnvA.addConst d1MutBVal.name d1MutBVal.toVConstant).get!

theorem d0Env_add_d1MutA :
    d0Env.addConst d1MutAVal.name d1MutAVal.toVConstant =
      some d1ConstEnvA := by
  simp [VEnv.addConst, d1MutA_fresh, d1ConstEnvA]

theorem d1MutB_fresh_A : d1ConstEnvA.constants d1MutBVal.name = none := by
  have hne := d1MutA_name_ne_mutB
  simp [d1ConstEnvA, VEnv.addConst, d1MutA_fresh, hne, d1MutB_fresh]

theorem d1ConstEnvA_add_d1MutB :
    d1ConstEnvA.addConst d1MutBVal.name d1MutBVal.toVConstant =
      some d1ConstEnv := by
  simp [VEnv.addConst, d1MutB_fresh_A, d1ConstEnv]

theorem d0Env_add_d1Muts : d0Env.addConsts d1Muts = some d1ConstEnv := by
  simp [VEnv.addConsts, d1Muts, List.foldlM, d0Env_add_d1MutA,
    d1ConstEnvA_add_d1MutB]

/-- The complete D1 environment: the D0 environment followed by one checked
mutual definition block. -/
def d1Env : VEnv := d1ConstEnv.addDefEqs d1Muts

theorem d1Env_eq_addDefEq :
    d1Env = (d1ConstEnv.addDefEq d1MutAVal.toDefEq).addDefEq
      d1MutBVal.toDefEq := rfl

theorem d0Env_le_d1ConstEnv : d0Env ≤ d1ConstEnv :=
  (VEnv.addConst_le d0Env_add_d1MutA).trans
    (VEnv.addConst_le d1ConstEnvA_add_d1MutB)

theorem d0Env_le_d1Env : d0Env ≤ d1Env :=
  d0Env_le_d1ConstEnv.trans
    (VEnv.addDefEq_le.trans VEnv.addDefEq_le)

/-- The Nat family head is a type in the D0 environment; both block members
declare it as their type. -/
theorem d1NatIsType : d0Env.IsType 0 [] (.const ``Nat []) := by
  have h := VEnv.HasType.const (U := 0) (Γ := [])
    (ls := [])
    (natFinalEnv_le_d0Env.constants
      InductiveReplayFixtures.nat_type_env_lookup)
    (by simp) rfl
  rw [probeNatTypeTypeV_eq] at h
  exact ⟨_, h⟩

theorem d1Muts_types_wf : ∀ ci ∈ d1Muts, ci.toVConstant.WF d0Env := by
  intro ci hci
  simp only [d1Muts, List.mem_cons, List.not_mem_nil, or_false] at hci
  rcases hci with rfl | rfl
  · exact d1NatIsType
  · exact d1NatIsType

theorem d1ConstEnv_d1MutA_lookup :
    d1ConstEnv.constants d1MutAVal.name =
      some d1MutAVal.toVConstant :=
  (VEnv.addConst_le d1ConstEnvA_add_d1MutB).constants
    (VEnv.addConst_self d0Env_add_d1MutA)

theorem d1ConstEnv_d1MutB_lookup :
    d1ConstEnv.constants d1MutBVal.name =
      some d1MutBVal.toVConstant :=
  VEnv.addConst_self d1ConstEnvA_add_d1MutB

theorem d1ConstEnv_natSucc_lookup :
    d1ConstEnv.constants ``Nat.succ =
      some InductiveFixtures.natType.ctors[1].toVConstant :=
  d0Env_le_d1ConstEnv.constants d0NatSuccEnvLookup

theorem d1ConstEnv_d0Def_lookup :
    d1ConstEnv.constants d0DefVal.name = some d0DefVal.toVConstant :=
  d0Env_le_d1ConstEnv.constants d0Env_d0Def_lookup

theorem d1MutAVal_wf : d1MutAVal.WF d1ConstEnv := by
  have h := VEnv.HasType.const (U := 0) (Γ := []) (ls := [])
    d1ConstEnv_d1MutB_lookup (by simp) rfl
  exact h

theorem d1MutBVal_wf : d1MutBVal.WF d1ConstEnv := by
  have hsucc := VEnv.HasType.const (U := 0) (Γ := []) (ls := [])
    d1ConstEnv_natSucc_lookup (by simp) rfl
  rw [probeNatSuccCtorTypeV_eq] at hsucc
  have hdef := VEnv.HasType.const (U := 0) (Γ := []) (ls := [])
    d1ConstEnv_d0Def_lookup (by simp) rfl
  exact VEnv.HasType.app hsucc hdef

theorem d1Muts_values_wf : ∀ ci ∈ d1Muts, ci.WF d1ConstEnv := by
  intro ci hci
  simp only [d1Muts, List.mem_cons, List.not_mem_nil, or_false] at hci
  rcases hci with rfl | rfl
  · exact d1MutAVal_wf
  · exact d1MutBVal_wf

theorem d1Env_wf : d1Env.WF := by
  obtain ⟨ds, hds⟩ := d0Env_wf
  exact ⟨.mutualDef d1Muts :: ds,
    .decl (.mutualDef d1Muts_types_wf d0Env_add_d1Muts d1Muts_values_wf)
      hds⟩

theorem d1Env_ordered : d1Env.Ordered := d1Env_wf.ordered

theorem d1Env_d1MutA_lookup :
    d1Env.constants d1MutAVal.name = some d1MutAVal.toVConstant :=
  (VEnv.addDefEq_le.trans VEnv.addDefEq_le).constants
    d1ConstEnv_d1MutA_lookup

theorem d1Env_d1MutB_lookup :
    d1Env.constants d1MutBVal.name = some d1MutBVal.toVConstant :=
  (VEnv.addDefEq_le.trans VEnv.addDefEq_le).constants
    d1ConstEnv_d1MutB_lookup

theorem d1Env_constants_old {c : Name} {ci : VConstant}
    (hneA : c ≠ d1MutAVal.name) (hneB : c ≠ d1MutBVal.name)
    (H : d1Env.constants c = some ci) :
    d0Env.constants c = some ci := by
  have hne := d1MutA_name_ne_mutB
  simpa [d1Env, VEnv.addDefEqs, d1Muts, d1ConstEnv, d1ConstEnvA,
    VEnv.addConst, d1MutA_fresh, d1MutB_fresh, hne, VEnv.addDefEq,
    Ne.symm hneA, Ne.symm hneB] using H

theorem d1Env_defeqs_iff (df : VDefEq) :
    d1Env.defeqs df ↔
      df = d1MutBVal.toDefEq ∨ df = d1MutAVal.toDefEq ∨
        d0Env.defeqs df := by
  have hne := d1MutA_name_ne_mutB
  simp [d1Env, VEnv.addDefEqs, d1Muts, d1ConstEnv, d1ConstEnvA,
    VEnv.addConst, d1MutA_fresh, d1MutB_fresh, hne, VEnv.addDefEq]

theorem d1Env_defeq_mutA : d1Env.defeqs d1MutAVal.toDefEq := by
  rw [d1Env_defeqs_iff]
  exact .inr (.inl rfl)

theorem d1Env_defeq_mutB : d1Env.defeqs d1MutBVal.toDefEq := by
  rw [d1Env_defeqs_iff]
  exact .inl rfl

theorem d1Env_no_structEta (rule : VStructEta) :
    ¬d1Env.structEtas rule := by
  change ¬False
  intro h
  exact h

/-! ## D1 pattern layer -/

/-- D1 adds the two mutual definition heads to the D0 table. -/
def d1Classify (n : Name) : Option Classification :=
  if n = d1MutAVal.name then some (.symb 0)
  else if n = d1MutBVal.name then some (.symb 0)
  else d0Classify n

theorem d1MutAClosed : d1MutAVal.value.Closed := by decide

theorem d1MutBClosed : d1MutBVal.value.Closed := by decide

/-- The complete D1 pattern inventory: the D0 inventory (both generated Nat
iota rules and the `d0def` rule) plus the two mutual definition rules. -/
inductive D1Pat : (p : Pattern) → p.RHS × p.Check → Prop where
  | old {p : Pattern} {r : p.RHS × p.Check} : D0Pat p r → D1Pat p r
  | defnA : D1Pat (.const d1MutAVal.name)
      (.fixed d1MutAVal.value d1MutAClosed, .true)
  | defnB : D1Pat (.const d1MutBVal.name)
      (.fixed d1MutBVal.value d1MutBClosed, .true)

theorem d0Classify_d1MutA_none : d0Classify d1MutAVal.name = none := by
  native_decide

theorem d0Classify_d1MutB_none : d0Classify d1MutBVal.name = none := by
  native_decide

theorem d1Pat_simple {p : Pattern} {r : p.RHS × p.Check}
    (H : D1Pat p r) : ∃ sp : SimplePattern, p = sp.toPattern := by
  cases H with
  | old H => exact d0Pat_simple H
  | defnA => exact ⟨.defn d1MutAVal.name, rfl⟩
  | defnB => exact ⟨.defn d1MutBVal.name, rfl⟩

theorem d0Classify_agrees {c : Name} {cl : Classification}
    (H : d0Classify c = some cl) : d1Classify c = some cl := by
  have hneA : c ≠ d1MutAVal.name := by
    intro h
    subst c
    rw [d0Classify_d1MutA_none] at H
    cases H
  have hneB : c ≠ d1MutBVal.name := by
    intro h
    subst c
    rw [d0Classify_d1MutB_none] at H
    cases H
  simpa [d1Classify, hneA, hneB] using H

theorem d0PatWF_lift {p : Pattern} {top : Bool} {extra : Nat}
    (H : p.WF d0Classify top extra) : p.WF d1Classify top extra := by
  induction p generalizing top extra with
  | const c =>
    exact d0Classify_agrees H
  | var f ih =>
    exact ih H
  | app f a ihf iha =>
    exact ⟨ihf H.1, iha H.2⟩

theorem d1Pat_wf {p : Pattern} {r : p.RHS × p.Check}
    (H : D1Pat p r) : p.WF d1Classify := by
  cases H with
  | old H => exact d0PatWF_lift (d0Pat_wf H)
  | defnA => simp [Pattern.WF, d1Classify]
  | defnB =>
    have hne := d1MutA_name_ne_mutB
    simp [Pattern.WF, d1Classify, Ne.symm hne]

/-- Neither fresh mutual-definition head intersects any subpattern of a D0
pattern. -/
theorem d1Def_inter_d0Subpattern_none {nm : Name}
    (hrec : nm ≠ ``Nat.rec) (hzero : nm ≠ ``Nat.zero)
    (hsucc : nm ≠ ``Nat.succ) (hdef : nm ≠ d0DefVal.name)
    {p p' : Pattern} {r : p.RHS × p.Check} (H : D0Pat p r)
    (hsub : Subpattern p' p) :
    (Pattern.const nm).inter p' = none := by
  cases H with
  | iota H =>
    rcases natPat_pattern H with hp | hp
    · subst p
      rcases RecursorIotaPattern.subpattern_inv hsub with
        rfl | ⟨j, -, rfl⟩ | ⟨j, -, rfl⟩
      · rfl
      · simpa only [Pattern.varN] using
          Pattern.varN_const_inter_of_ne_name hrec 0 j
      · simpa only [Pattern.varN] using
          Pattern.varN_const_inter_of_ne_name hzero 0 j
    · subst p
      rcases RecursorIotaPattern.subpattern_inv hsub with
        rfl | ⟨j, -, rfl⟩ | ⟨j, -, rfl⟩
      · rfl
      · simpa only [Pattern.varN] using
          Pattern.varN_const_inter_of_ne_name hrec 0 j
      · simpa only [Pattern.varN] using
          Pattern.varN_const_inter_of_ne_name hsucc 0 j
  | defn =>
    cases hsub
    simp [Pattern.inter, hdef]

theorem d1MutA_inter_d0_none {p p' : Pattern} {r : p.RHS × p.Check}
    (H : D0Pat p r) (hsub : Subpattern p' p) :
    (Pattern.const d1MutAVal.name).inter p' = none :=
  d1Def_inter_d0Subpattern_none d1MutA_name_ne_natRec
    d1MutA_name_ne_natZero d1MutA_name_ne_natSucc d1MutA_name_ne_d0Def
    H hsub

theorem d1MutB_inter_d0_none {p p' : Pattern} {r : p.RHS × p.Check}
    (H : D0Pat p r) (hsub : Subpattern p' p) :
    (Pattern.const d1MutBVal.name).inter p' = none :=
  d1Def_inter_d0Subpattern_none d1MutB_name_ne_natRec
    d1MutB_name_ne_natZero d1MutB_name_ne_natSucc d1MutB_name_ne_d0Def
    H hsub

/-- A D0 pattern head never matches either fresh definition head.  This is
the mirror image of the lemmas above, needed when the *old* pattern supplies
the intersection side. -/
theorem d0_inter_d1MutA_none {p p' : Pattern} {r : p.RHS × p.Check}
    (H : D0Pat p r) (hsub : Subpattern p' (Pattern.const d1MutAVal.name)) :
    p.inter p' = none := by
  cases hsub
  rw [Pattern.inter_comm]
  exact d1MutA_inter_d0_none H .refl

theorem d0_inter_d1MutB_none {p p' : Pattern} {r : p.RHS × p.Check}
    (H : D0Pat p r) (hsub : Subpattern p' (Pattern.const d1MutBVal.name)) :
    p.inter p' = none := by
  cases hsub
  rw [Pattern.inter_comm]
  exact d1MutB_inter_d0_none H .refl

theorem d1Pat_uniq {p₁ p₂ p₃ p₄ : Pattern}
    {r : p₁.RHS × p₁.Check} {r' : p₂.RHS × p₂.Check}
    (H1 : D1Pat p₁ r) (H2 : D1Pat p₂ r')
    (H3 : Subpattern p₃ p₁) (H4 : p₂.inter p₃ = some p₄) :
    p₁ = p₂ ∧ p₂ = p₃ ∧ r ≍ r' := by
  cases H1 with
  | old H1 =>
    cases H2 with
    | old H2 => exact d0Pat_uniq H1 H2 H3 H4
    | defnA =>
      rw [d1MutA_inter_d0_none H1 H3] at H4
      cases H4
    | defnB =>
      rw [d1MutB_inter_d0_none H1 H3] at H4
      cases H4
  | defnA =>
    cases H2 with
    | old H2 =>
      rw [d0_inter_d1MutA_none H2 H3] at H4
      cases H4
    | defnA =>
      cases H3
      simp [Pattern.inter] at H4
      subst p₄
      exact ⟨rfl, rfl, HEq.rfl⟩
    | defnB =>
      cases H3
      have hne := d1MutA_name_ne_mutB
      simp [Pattern.inter, Ne.symm hne] at H4
  | defnB =>
    cases H2 with
    | old H2 =>
      rw [d0_inter_d1MutB_none H2 H3] at H4
      cases H4
    | defnA =>
      cases H3
      have hne := d1MutA_name_ne_mutB
      simp [Pattern.inter, hne] at H4
    | defnB =>
      cases H3
      simp [Pattern.inter] at H4
      subst p₄
      exact ⟨rfl, rfl, HEq.rfl⟩

theorem d1Pat_app_l {p : Pattern} {r : p.RHS × p.Check}
    {p₁ p₂ p₃ p₄ : Pattern}
    (H : D1Pat p r) (h : Subpattern (.app p₁ p₂) p) :
    ¬Subpattern (.app p₃ p₄) p₁ := by
  cases H with
  | old H => exact d0Pat_app_l H h
  | defnA => cases h
  | defnB => cases h

theorem d1Pat_app_l_uniq {p p' : Pattern}
    {r : p.RHS × p.Check} {r' : p'.RHS × p'.Check}
    {p₁ p₂ p₁' p₂' p₃ : Pattern}
    (H : D1Pat p r) (H' : D1Pat p' r')
    (h : Subpattern (.app p₁ p₂) p)
    (h' : Subpattern (.app p₁' p₂') p')
    (h₃ : Subpattern (.var p₃) p₁) : p₁'.inter p₃ = none := by
  cases H with
  | old H =>
    cases H' with
    | old H' => exact d0Pat_app_l_uniq H H' h h' h₃
    | defnA => cases h'
    | defnB => cases h'
  | defnA => cases h
  | defnB => cases h

theorem d1Pat_app_uniq {p p' : Pattern}
    {r : p.RHS × p.Check} {r' : p'.RHS × p'.Check}
    {p₁ p₂ p₁' p₂' p₃ p₃' : Pattern}
    (H : D1Pat p r) (H' : D1Pat p' r')
    (h : Subpattern (.app p₁ p₂) p)
    (h' : Subpattern (.app p₁' p₂') p')
    (h₃ : Subpattern p₃ p₁) (h₃' : Subpattern p₃' p₂') :
    p₃.inter p₃' = none := by
  cases H with
  | old H =>
    cases H' with
    | old H' => exact d0Pat_app_uniq H H' h h' h₃ h₃'
    | defnA => cases h'
    | defnB => cases h'
  | defnA => cases h
  | defnB => cases h

/-- The complete D1 structural instance: the D0 inventory extended by the
checked mutual definition block. -/
def d1Params (univs : Nat) : Params where
  env := d1Env
  henv := d1Env_ordered
  univs := univs
  Pat := D1Pat
  classify := d1Classify
  pat_simple := d1Pat_simple
  pat_wf := d1Pat_wf
  pat_uniq := d1Pat_uniq
  pat_app_l := d1Pat_app_l
  pat_app_l_uniq := d1Pat_app_l_uniq
  pat_app_uniq := d1Pat_app_uniq

/-! ## D0-to-D1 proof transport

`SExpr` retains its complete `Params` value as an inductive parameter, so
crossing from the D0 instance into the extended D1 instance is an explicit
syntax map, exactly as in D0's own D0a→D0b transport.  Unlike that template,
the `const` and `defn` cases are now live: the source inventory already
contains a definition pattern (`d0def`), which transports along the
`D1Pat.old` inclusion. -/

def d0ToD1Level (univs : Nat)
    (u : @SLevel (d0Params univs)) : @SLevel (d1Params univs) := by
  refine ⟨u.1, ?_⟩
  obtain ⟨l, hl, heval⟩ := u.2
  refine ⟨l, ?_, heval⟩
  change l.WF univs
  change l.WF univs at hl
  exact hl

def d1ToD0Level (univs : Nat)
    (u : @SLevel (d1Params univs)) : @SLevel (d0Params univs) := by
  refine ⟨u.1, ?_⟩
  obtain ⟨l, hl, heval⟩ := u.2
  refine ⟨l, ?_, heval⟩
  change l.WF univs
  change l.WF univs at hl
  exact hl

@[simp] theorem d1ToD0Level_d0ToD1Level (univs : Nat)
    (u : @SLevel (d0Params univs)) :
    d1ToD0Level univs (d0ToD1Level univs u) = u := by
  apply Subtype.ext
  rfl

@[simp] theorem d0ToD1Level_d1ToD0Level (univs : Nat)
    (u : @SLevel (d1Params univs)) :
    d0ToD1Level univs (d1ToD0Level univs u) = u := by
  apply Subtype.ext
  rfl

noncomputable def d0ToD1Expr (univs : Nat) (e : @SExpr (d0Params univs)) :
    @SExpr (d1Params univs) :=
  @SExpr.rec (d0Params univs)
    (motive := fun _ => @SExpr (d1Params univs))
    (fun i => @SExpr.bvar (d1Params univs) i)
    (fun u => @SExpr.sort (d1Params univs) (d0ToD1Level univs u))
    (fun c ls => @SExpr.const (d1Params univs) c
      (ls.map (d0ToD1Level univs)))
    (fun _ _ f a => @SExpr.app (d1Params univs) f a)
    (fun _ _ A body => @SExpr.lam (d1Params univs) A body)
    (fun _ _ A B => @SExpr.forallE (d1Params univs) A B)
    e

noncomputable def d1ToD0Expr (univs : Nat) (e : @SExpr (d1Params univs)) :
    @SExpr (d0Params univs) :=
  @SExpr.rec (d1Params univs)
    (motive := fun _ => @SExpr (d0Params univs))
    (fun i => @SExpr.bvar (d0Params univs) i)
    (fun u => @SExpr.sort (d0Params univs) (d1ToD0Level univs u))
    (fun c ls => @SExpr.const (d0Params univs) c
      (ls.map (d1ToD0Level univs)))
    (fun _ _ f a => @SExpr.app (d0Params univs) f a)
    (fun _ _ A body => @SExpr.lam (d0Params univs) A body)
    (fun _ _ A B => @SExpr.forallE (d0Params univs) A B)
    e

@[simp] theorem d0ToD1Expr_bvar (univs i) :
    d0ToD1Expr univs (@SExpr.bvar (d0Params univs) i) =
      @SExpr.bvar (d1Params univs) i := rfl

@[simp] theorem d0ToD1Expr_sort (univs) (u : @SLevel (d0Params univs)) :
    d0ToD1Expr univs (@SExpr.sort (d0Params univs) u) =
      @SExpr.sort (d1Params univs) (d0ToD1Level univs u) := rfl

@[simp] theorem d0ToD1Expr_const (univs c)
    (ls : List (@SLevel (d0Params univs))) :
    d0ToD1Expr univs (@SExpr.const (d0Params univs) c ls) =
      @SExpr.const (d1Params univs) c (ls.map (d0ToD1Level univs)) := rfl

@[simp] theorem d0ToD1Expr_app (univs)
    (f a : @SExpr (d0Params univs)) :
    d0ToD1Expr univs (@SExpr.app (d0Params univs) f a) =
      @SExpr.app (d1Params univs) (d0ToD1Expr univs f)
        (d0ToD1Expr univs a) := rfl

@[simp] theorem d0ToD1Expr_lam (univs)
    (A e : @SExpr (d0Params univs)) :
    d0ToD1Expr univs (@SExpr.lam (d0Params univs) A e) =
      @SExpr.lam (d1Params univs) (d0ToD1Expr univs A)
        (d0ToD1Expr univs e) := rfl

@[simp] theorem d0ToD1Expr_forallE (univs)
    (A B : @SExpr (d0Params univs)) :
    d0ToD1Expr univs (@SExpr.forallE (d0Params univs) A B) =
      @SExpr.forallE (d1Params univs) (d0ToD1Expr univs A)
        (d0ToD1Expr univs B) := rfl

@[simp] theorem d1ToD0Expr_bvar (univs i) :
    d1ToD0Expr univs (@SExpr.bvar (d1Params univs) i) =
      @SExpr.bvar (d0Params univs) i := rfl

@[simp] theorem d1ToD0Expr_sort (univs) (u : @SLevel (d1Params univs)) :
    d1ToD0Expr univs (@SExpr.sort (d1Params univs) u) =
      @SExpr.sort (d0Params univs) (d1ToD0Level univs u) := rfl

@[simp] theorem d1ToD0Expr_const (univs c)
    (ls : List (@SLevel (d1Params univs))) :
    d1ToD0Expr univs (@SExpr.const (d1Params univs) c ls) =
      @SExpr.const (d0Params univs) c (ls.map (d1ToD0Level univs)) := rfl

@[simp] theorem d1ToD0Expr_app (univs)
    (f a : @SExpr (d1Params univs)) :
    d1ToD0Expr univs (@SExpr.app (d1Params univs) f a) =
      @SExpr.app (d0Params univs) (d1ToD0Expr univs f)
        (d1ToD0Expr univs a) := rfl

@[simp] theorem d1ToD0Expr_lam (univs)
    (A e : @SExpr (d1Params univs)) :
    d1ToD0Expr univs (@SExpr.lam (d1Params univs) A e) =
      @SExpr.lam (d0Params univs) (d1ToD0Expr univs A)
        (d1ToD0Expr univs e) := rfl

@[simp] theorem d1ToD0Expr_forallE (univs)
    (A B : @SExpr (d1Params univs)) :
    d1ToD0Expr univs (@SExpr.forallE (d1Params univs) A B) =
      @SExpr.forallE (d0Params univs) (d1ToD0Expr univs A)
        (d1ToD0Expr univs B) := rfl

@[simp] theorem d1ToD0Expr_d0ToD1Expr (univs : Nat)
    (e : @SExpr (d0Params univs)) :
    d1ToD0Expr univs (d0ToD1Expr univs e) = e := by
  induction e <;> simp [List.map_map, Function.comp_def, *]

@[simp] theorem d0ToD1Expr_d1ToD0Expr (univs : Nat)
    (e : @SExpr (d1Params univs)) :
    d0ToD1Expr univs (d1ToD0Expr univs e) = e := by
  induction e <;> simp [List.map_map, Function.comp_def, *]

noncomputable def d0ToD1Subst (univs : Nat)
    (sigma : @Subst (d0Params univs)) :
    @Subst (d1Params univs) := fun i => d0ToD1Expr univs (sigma i)

@[simp] theorem d0ToD1Expr_lift' (univs : Nat)
    (e : @SExpr (d0Params univs)) (rho : Lift) :
    d0ToD1Expr univs (@SExpr.lift' (d0Params univs) e rho) =
      @SExpr.lift' (d1Params univs) (d0ToD1Expr univs e) rho := by
  induction e generalizing rho <;> simp [SExpr.lift', *]

@[simp] theorem d0ToD1Subst_lift (univs : Nat)
    (sigma : @Subst (d0Params univs)) :
    d0ToD1Subst univs (@Subst.lift (d0Params univs) sigma) =
      @Subst.lift (d1Params univs) (d0ToD1Subst univs sigma) := by
  funext i
  cases i <;> simp [d0ToD1Subst, Subst.lift,
    d0ToD1Expr_lift']

@[simp] theorem d0ToD1Expr_subst (univs : Nat)
    (e : @SExpr (d0Params univs)) (sigma : @Subst (d0Params univs)) :
    d0ToD1Expr univs (@SExpr.subst (d0Params univs) e sigma) =
      @SExpr.subst (d1Params univs) (d0ToD1Expr univs e)
        (d0ToD1Subst univs sigma) := by
  induction e generalizing sigma <;>
    simp [SExpr.subst, d0ToD1Subst, *]

@[simp] theorem d0ToD1Expr_inst (univs : Nat)
    (e a : @SExpr (d0Params univs)) :
    d0ToD1Expr univs (@SExpr.inst (d0Params univs) e a) =
      @SExpr.inst (d1Params univs) (d0ToD1Expr univs e)
        (d0ToD1Expr univs a) := by
  change d0ToD1Expr univs
      (@SExpr.subst (d0Params univs) e (@Subst.one (d0Params univs) a)) =
    @SExpr.subst (d1Params univs) (d0ToD1Expr univs e)
      (@Subst.one (d1Params univs) (d0ToD1Expr univs a))
  rw [d0ToD1Expr_subst]
  congr 1
  funext i
  cases i <;> rfl

@[simp] theorem d0ToD1Level_instV (univs : Nat)
    (ls : List (@SLevel (d0Params univs))) (u : VLevel) :
    d0ToD1Level univs (@SLevel.instV (d0Params univs) ls u) =
      @SLevel.instV (d1Params univs) (ls.map (d0ToD1Level univs)) u := by
  apply Subtype.ext
  funext v
  change u.eval (ls.map fun l => l.1 v) =
    u.eval ((ls.map (d0ToD1Level univs)).map fun l => l.1 v)
  congr 1
  simp [List.map_map, Function.comp_def, d0ToD1Level]

@[simp] theorem d0ToD1Level_succ (univs : Nat)
    (u : @SLevel (d0Params univs)) :
    d0ToD1Level univs (@SLevel.succ (d0Params univs) u) =
      @SLevel.succ (d1Params univs) (d0ToD1Level univs u) := by
  apply Subtype.ext
  rfl

@[simp] theorem d0ToD1Level_imax (univs : Nat)
    (u v : @SLevel (d0Params univs)) :
    d0ToD1Level univs (@SLevel.imax (d0Params univs) u v) =
      @SLevel.imax (d1Params univs)
        (d0ToD1Level univs u) (d0ToD1Level univs v) := by
  apply Subtype.ext
  rfl

@[simp] theorem d0ToD1Expr_mkInst (univs : Nat)
    (ls : List (@SLevel (d0Params univs))) (e : VExpr) :
    d0ToD1Expr univs (@SExpr.mkInst (d0Params univs) ls e) =
      @SExpr.mkInst (d1Params univs) (ls.map (d0ToD1Level univs)) e := by
  induction e <;> simp [SExpr.mkInst, List.map_map, Function.comp_def, *]

theorem d0Lookup_to_d1 (univs : Nat)
    {Gamma : List (@SExpr (d0Params univs))} {i : Nat}
    {A : @SExpr (d0Params univs)}
    (H : @Lookup (d0Params univs) Gamma i A) :
    @Lookup (d1Params univs) (Gamma.map (d0ToD1Expr univs)) i
      (d0ToD1Expr univs A) := by
  letI : Params := d1Params univs
  induction H with
  | zero =>
    rw [d0ToD1Expr_lift']
    exact .zero
  | succ _ ih =>
    rw [d0ToD1Expr_lift']
    exact .succ ih

theorem d0IsDefEq_to_d1 (univs : Nat)
    {Gamma : List (@SExpr (d0Params univs))}
    {e₁ e₂ A : @SExpr (d0Params univs)}
    (H : @IsDefEq (d0Params univs) Gamma e₁ e₂ A) :
    @IsDefEq (d1Params univs) (Gamma.map (d0ToD1Expr univs))
      (d0ToD1Expr univs e₁) (d0ToD1Expr univs e₂)
      (d0ToD1Expr univs A) := by
  letI : Params := d1Params univs
  induction H with
  | bvar h => exact .bvar (d0Lookup_to_d1 univs h)
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | @sort Gamma l =>
    simpa only [d0ToD1Expr_sort, d0ToD1Level_succ] using
      (IsDefEq.sort : IsDefEq (Gamma.map (d0ToD1Expr univs))
        (.sort (d0ToD1Level univs l)) (.sort (d0ToD1Level univs l))
        (.sort (.succ (d0ToD1Level univs l))))
  | @const c ci Gamma ls hreg hlen =>
    simpa only [d0ToD1Expr_const, d0ToD1Expr_mkInst] using
      (IsDefEq.const (Γ := Gamma.map (d0ToD1Expr univs))
        (ls := ls.map (d0ToD1Level univs))
        (d0Env_le_d1Env.constants hreg) (by simpa using hlen))
  | appDF _ _ ihf iha =>
    rw [d0ToD1Expr_app, d0ToD1Expr_app, d0ToD1Expr_inst]
    exact IsDefEq.appDF ihf iha
  | lamDF _ _ ihA ihBody =>
    simpa only [List.map_cons, d0ToD1Expr_lam, d0ToD1Expr_forallE] using
      IsDefEq.lamDF ihA ihBody
  | forallEDF _ _ ihA ihBody =>
    simpa only [List.map_cons, d0ToD1Expr_forallE, d0ToD1Expr_sort,
      d0ToD1Level_imax] using IsDefEq.forallEDF ihA ihBody
  | defeqDF _ _ ihA ihe => exact .defeqDF ihA ihe
  | beta _ _ ihBody ihArg =>
    simpa only [List.map_cons, d0ToD1Expr_app, d0ToD1Expr_lam,
      d0ToD1Expr_inst] using
      IsDefEq.beta ihBody ihArg
  | eta _ ih =>
    rw [d0ToD1Expr_lam, d0ToD1Expr_app, d0ToD1Expr_bvar,
      d0ToD1Expr_forallE, d0ToD1Expr_lift']
    exact IsDefEq.eta ih
  | proofIrrel _ _ _ ihp ihh ihh' => exact .proofIrrel ihp ihh ihh'
  | @extra df Gamma ls hreg hlen =>
    simpa only [d0ToD1Expr_mkInst] using
      (IsDefEq.extra (Γ := Gamma.map (d0ToD1Expr univs))
        (ls := ls.map (d0ToD1Level univs))
        (d0Env_le_d1Env.defeqs hreg) (by simpa using hlen))

/-- A constructor-shaped D1 classification cannot be either fresh definition
head, and therefore restricts to the same constructor classification in D0.
-/
theorem d1CtorToD0 (univs : Nat) {c : Name}
    (H : @CtorBundle.IsCtor (d1Params univs) c) :
    @CtorBundle.IsCtor (d0Params univs) c := by
  change ∃ cl, d1Classify c = some cl ∧
    (match cl with | .ctor _ | .etaCtor _ _ => true | _ => false) = true at H
  change ∃ cl, d0Classify c = some cl ∧
    (match cl with | .ctor _ | .etaCtor _ _ => true | _ => false) = true
  obtain ⟨cl, hclass, hshape⟩ := H
  have hneA : c ≠ d1MutAVal.name := by
    intro hc
    subst c
    simp [d1Classify] at hclass
    subst cl
    simp at hshape
  have hneB : c ≠ d1MutBVal.name := by
    intro hc
    subst c
    simp [d1Classify, Ne.symm d1MutA_name_ne_mutB] at hclass
    subst cl
    simp at hshape
  exact ⟨cl, by simpa [d1Classify, hneA, hneB] using hclass, hshape⟩

theorem d0IndTyClassify_to_d1 {c : Name} {arity : Nat}
    (H : d0Classify c = some (.indTy arity)) :
    d1Classify c = some (.indTy arity) :=
  d0Classify_agrees H

theorem d1CtorToD0_cl_eq (univs : Nat) {c : Name}
    (cl : @CtorBundle.IsCtor (d1Params univs) c) :
    (@CtorBundle.IsCtor.cl (d0Params univs) c (d1CtorToD0 univs cl)).1 =
      (@CtorBundle.IsCtor.cl (d1Params univs) c cl).1 := by
  let oldCl := @CtorBundle.IsCtor.cl (d0Params univs) c
    (d1CtorToD0 univs cl)
  let newCl := @CtorBundle.IsCtor.cl (d1Params univs) c cl
  have hnewD0 : d0Classify c = some newCl.1 := by
    have hnew := newCl.2.1
    change d1Classify c = some newCl.1 at hnew
    have hneA : c ≠ d1MutAVal.name := by
      intro hc
      subst c
      simp [d1Classify] at hnew
      have hs := newCl.2.2
      rw [← hnew] at hs
      simp at hs
    have hneB : c ≠ d1MutBVal.name := by
      intro hc
      subst c
      simp [d1Classify, Ne.symm d1MutA_name_ne_mutB] at hnew
      have hs := newCl.2.2
      rw [← hnew] at hs
      simp at hs
    simpa [d1Classify, hneA, hneB] using hnew
  have hold := oldCl.2.1
  change d0Classify c = some oldCl.1 at hold
  exact Option.some.inj (hold.symm.trans hnewD0)

/-- Reindex a D0 constructor bundle through the syntax and classifier maps.
-/
noncomputable def d0CtorBundleToD1 (univs : Nat) {c : Name}
    (cl : @CtorBundle.IsCtor (d1Params univs) c)
    (F : @CtorBundle (d0Params univs) c (d1CtorToD0 univs cl)) :
    @CtorBundle (d1Params univs) c cl := by
  rcases F with ⟨I, Ts, args, u, hlen, hclI, hu0⟩
  refine @CtorBundle.mk (d1Params univs) c cl I
    (Ts.map (d0ToD1Expr univs)) (args.map (d0ToD1Expr univs))
    (d0ToD1Level univs u) ?_ ?_ ?_
  · rw [List.length_map, hlen, d1CtorToD0_cl_eq univs cl]
  · change d0Classify I = some (.indTy args.length) at hclI
    letI : Params := d1Params univs
    change d1Classify I = some (.indTy (args.map (d0ToD1Expr univs)).length)
    simpa using d0IndTyClassify_to_d1 hclI
  · intro hzero
    have hback := congrArg (d1ToD0Level univs) hzero
    apply hu0
    apply Subtype.ext
    exact congrArg Subtype.val hback

theorem d0ToD1Expr_foldr_forallE (univs : Nat)
    (Ts : List (@SExpr (d0Params univs))) (e : @SExpr (d0Params univs)) :
    d0ToD1Expr univs
        (Ts.foldr (fun A B => @SExpr.forallE (d0Params univs) A B) e) =
      (Ts.map (d0ToD1Expr univs)).foldr
        (fun A B => @SExpr.forallE (d1Params univs) A B)
        (d0ToD1Expr univs e) := by
  induction Ts <;> simp [*]

theorem d0ToD1Expr_foldr_app (univs : Nat)
    (args : List (@SExpr (d0Params univs)))
    (e : @SExpr (d0Params univs)) :
    d0ToD1Expr univs
        (args.foldr (fun A acc => @SExpr.app (d0Params univs) acc A) e) =
      (args.map (d0ToD1Expr univs)).foldr
        (fun A acc => @SExpr.app (d1Params univs) acc A)
        (d0ToD1Expr univs e) := by
  induction args <;> simp [*]

@[simp] theorem d0CtorBundleToD1_rhs (univs : Nat) {c : Name}
    (cl : @CtorBundle.IsCtor (d1Params univs) c)
    (F : @CtorBundle (d0Params univs) c (d1CtorToD0 univs cl))
    (ls : List (@SLevel (d0Params univs))) :
    d0ToD1Expr univs (@CtorBundle.rhs (d0Params univs) c
      (d1CtorToD0 univs cl) F ls) =
      @CtorBundle.rhs (d1Params univs) c cl
        (d0CtorBundleToD1 univs cl F)
        (ls.map (d0ToD1Level univs)) := by
  rcases F with ⟨I, Ts, args, u, hlen, hclI, hu0⟩
  simp [CtorBundle.rhs, d0CtorBundleToD1,
    d0ToD1Expr_foldr_forallE, d0ToD1Expr_foldr_app]

@[simp] theorem d0CtorBundleToD1_u (univs : Nat) {c : Name}
    (cl : @CtorBundle.IsCtor (d1Params univs) c)
    (F : @CtorBundle (d0Params univs) c (d1CtorToD0 univs cl)) :
    @CtorBundle.u (d1Params univs) c cl
        (d0CtorBundleToD1 univs cl F) =
      d0ToD1Level univs
        (@CtorBundle.u (d0Params univs) c (d1CtorToD0 univs cl) F) := by
  cases F
  rfl

@[simp] theorem d0ToD1Expr_rhs_applyS (univs : Nat) {p : Pattern}
    (r : p.RHS) (m₁ : List (@SLevel (d0Params univs)))
    (m₂ : p.Path → @SExpr (d0Params univs)) :
    d0ToD1Expr univs
        (@Pattern.RHS.applyS (d0Params univs) p m₁ m₂ r) =
      @Pattern.RHS.applyS (d1Params univs) p
        (m₁.map (d0ToD1Level univs))
        (fun path => d0ToD1Expr univs (m₂ path)) r := by
  induction r with
  | fixed e closed => exact d0ToD1Expr_mkInst univs m₁ e
  | var path => rfl
  | app f a ihf iha =>
    simp only [Pattern.RHS.applyS, d0ToD1Expr_app, ihf, iha]

theorem d0MatchesS_to_d1 (univs : Nat) {p : Pattern}
    {e : @SExpr (d0Params univs)}
    {m₁ : List (@SLevel (d0Params univs))}
    {m₂ : p.Path → @SExpr (d0Params univs)}
    (H : @Pattern.MatchesS (d0Params univs) p e m₁ m₂) :
    @Pattern.MatchesS (d1Params univs) p (d0ToD1Expr univs e)
      (m₁.map (d0ToD1Level univs))
      (fun path => d0ToD1Expr univs (m₂ path)) := by
  letI : Params := d1Params univs
  induction H with
  | @const c ls =>
    rw [d0ToD1Expr_const]
    refine cast ?_ (@Pattern.MatchesS.const (d1Params univs) c
      (ls.map (d0ToD1Level univs)))
    congr 1
    funext path
    exact Empty.elim path
  | @var f f' f₁ g₁ a' _ ih =>
    change @Pattern.MatchesS (d1Params univs) (.var f)
      (.app (d0ToD1Expr univs f') (d0ToD1Expr univs a'))
      (f₁.map (d0ToD1Level univs))
      (fun path => d0ToD1Expr univs (Option.elim path a' g₁))
    have heq : (fun path => d0ToD1Expr univs (Option.elim path a' g₁)) =
        (fun path => Option.elim path (d0ToD1Expr univs a')
          (fun path => d0ToD1Expr univs (g₁ path))) := by
      funext path
      cases path <;> rfl
    rw [heq]
    exact ih.var
  | @app f f' f₁ g₁ a a' f₂ g₂ _ _ ihf iha =>
    change @Pattern.MatchesS (d1Params univs) (.app f a)
      (@SExpr.app (d1Params univs)
        (d0ToD1Expr univs f') (d0ToD1Expr univs a'))
      (f₁.map (d0ToD1Level univs))
      (fun path => d0ToD1Expr univs (Sum.elim g₁ g₂ path))
    have heq : (fun path => d0ToD1Expr univs (Sum.elim g₁ g₂ path)) =
        Sum.elim (fun path => d0ToD1Expr univs (g₁ path))
          (fun path => d0ToD1Expr univs (g₂ path)) := by
      funext path
      cases path <;> rfl
    rw [heq]
    exact ihf.app iha

theorem d0ToD1_defeqsS (univs : Nat) {p : Pattern}
    (ck : p.Check) (m₁ : List (@SLevel (d0Params univs)))
    (m₂ : p.Path → @SExpr (d0Params univs)) :
    (@Pattern.Check.defeqsS (d0Params univs) p m₁ m₂ ck).map
        (fun ab => (d0ToD1Expr univs ab.1, d0ToD1Expr univs ab.2)) =
      @Pattern.Check.defeqsS (d1Params univs) p
        (m₁.map (d0ToD1Level univs))
        (fun path => d0ToD1Expr univs (m₂ path)) ck := by
  induction ck with
  | true => rfl
  | defeq a b rest ih =>
    simp only [Pattern.Check.defeqsS, List.map_cons, ih,
      d0ToD1Expr_rhs_applyS]

noncomputable def d0ToD1Dfs (univs : Nat)
    (dfs : List (@SExpr (d0Params univs) × @SExpr (d0Params univs) ×
      @SExpr (d0Params univs))) :
    List (@SExpr (d1Params univs) × @SExpr (d1Params univs) ×
      @SExpr (d1Params univs)) :=
  dfs.map fun (B, a, b) =>
    (d0ToD1Expr univs B, d0ToD1Expr univs a, d0ToD1Expr univs b)

theorem d0ToD1Dfs_map_snd (univs : Nat)
    (dfs : List (@SExpr (d0Params univs) × @SExpr (d0Params univs) ×
      @SExpr (d0Params univs))) :
    (d0ToD1Dfs univs dfs).map (fun x => x.2) =
      (dfs.map fun x => x.2).map fun ab =>
        (d0ToD1Expr univs ab.1, d0ToD1Expr univs ab.2) := by
  simp [d0ToD1Dfs, List.map_map, Function.comp_def]

noncomputable def d0Action_to_d1 (univs : Nat)
    {Gamma : List (@SExpr (d0Params univs))} {p : Pattern}
    {r : p.RHS × p.Check} {e A : @SExpr (d0Params univs)}
    {m₁ : List (@SLevel (d0Params univs))}
    {m₂ : p.Path → @SExpr (d0Params univs)}
    (H : @Pattern.Action (d0Params univs) Gamma p r e m₁ m₂ A) :
    @Pattern.Action (d1Params univs)
      (Gamma.map (d0ToD1Expr univs)) p r
      (d0ToD1Expr univs e) (m₁.map (d0ToD1Level univs))
      (fun path => d0ToD1Expr univs (m₂ path))
      (d0ToD1Expr univs A) := by
  rcases H with ⟨hpat, hmatched, dfs, hdefeqs, hchecked, hsound⟩
  change D0Pat p r at hpat
  refine @Pattern.Action.mk (d1Params univs)
    (Gamma := Gamma.map (d0ToD1Expr univs)) (p := p) (r := r)
    (e := d0ToD1Expr univs e)
    (m1 := m₁.map (d0ToD1Level univs))
    (m2 := fun path => d0ToD1Expr univs (m₂ path))
    (A := d0ToD1Expr univs A) (.old hpat)
    (d0MatchesS_to_d1 univs hmatched) (d0ToD1Dfs univs dfs) ?_ ?_ ?_
  · rw [d0ToD1Dfs_map_snd, hdefeqs]
    exact d0ToD1_defeqsS univs r.2 m₁ m₂
  · intro a b B hmem
    simp only [d0ToD1Dfs, List.mem_map] at hmem
    obtain ⟨⟨B₀, a₀, b₀⟩, hmem₀, heq⟩ := hmem
    cases heq
    exact d0IsDefEq_to_d1 univs (hchecked a₀ b₀ B₀ hmem₀)
  · simpa only [d0ToD1Expr_rhs_applyS] using
      d0IsDefEq_to_d1 univs hsound

/-- At a constant already present in the D0 environment, the only D1 pattern
members are the inherited D0 ones; both fresh definition heads are new
names. -/
theorem d1Pat_at_old_const {c : Name} {ci : VConstant}
    (hreg : d0Env.constants c = some ci)
    {r : (Pattern.const c).RHS × (Pattern.const c).Check}
    (H : D1Pat (.const c) r) : D0Pat (.const c) r := by
  cases H with
  | old H => exact H
  | defnA =>
    rw [d1MutA_fresh] at hreg
    cases hreg
  | defnB =>
    rw [d1MutB_fresh] at hreg
    cases hreg

/-- Transport a D0 evidence-rich derivation into the mutual-definition
extended D1 syntax and registry.  The `const` and `defn` cases carry the
inherited `d0def` pattern across the `D1Pat.old` inclusion. -/
noncomputable def d0StrongToD1 (univs : Nat)
    {Gamma : List (@SExpr (d0Params univs))}
    {e₁ e₂ A : @SExpr (d0Params univs)}
    (H : @IsDefEqStrong (d0Params univs) Gamma e₁ e₂ A) :
    @IsDefEqStrong (d1Params univs) (Gamma.map (d0ToD1Expr univs))
      (d0ToD1Expr univs e₁) (d0ToD1Expr univs e₂)
      (d0ToD1Expr univs A) := by
  letI : Params := d1Params univs
  induction H with
  | bvar h _ ihA => exact .bvar (d0Lookup_to_d1 univs h) ihA
  | symm _ ih => exact .symm ih
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | @sort Gamma l =>
    simpa only [d0ToD1Expr_sort, d0ToD1Level_succ] using
      (IsDefEqStrong.sort : IsDefEqStrong
        (Gamma.map (d0ToD1Expr univs))
        (.sort (d0ToD1Level univs l)) (.sort (d0ToD1Level univs l))
        (.sort (.succ (d0ToD1Level univs l))))
  | @const c ci Gamma ls u hreg hlen hTy F hF hDef
      ihTy ihF ihDef =>
    let F' : ∀ cl : CtorBundle.IsCtor c, CtorBundle c cl := fun cl =>
      d0CtorBundleToD1 univs cl (F (d1CtorToD0 univs cl))
    simpa only [d0ToD1Expr_const, d0ToD1Expr_mkInst] using
      (@IsDefEqStrong.const (d1Params univs) c ci
      (Gamma.map (d0ToD1Expr univs))
      (ls.map (d0ToD1Level univs)) (d0ToD1Level univs u)
      (d0Env_le_d1Env.constants hreg)
      (by simpa only [List.length_map] using hlen) (by
        simpa only [d0ToD1Expr_mkInst, d0ToD1Expr_sort] using ihTy)
      F' (by
        intro cl
        dsimp only [F']
        rw [← d0CtorBundleToD1_rhs, d0CtorBundleToD1_u]
        have H := ihF (d1CtorToD0 univs cl)
        simp only [d0ToD1Expr_mkInst, d0ToD1Expr_sort] at H
        exact H) (by
        intro r hpat
        have hold : D0Pat (.const c) r := d1Pat_at_old_const hreg hpat
        have H := ihDef hold
        rw [d0ToD1Expr_rhs_applyS] at H
        have hm2 : (fun path => d0ToD1Expr univs (Empty.elim path)) =
            (Empty.elim :
              (Pattern.const c).Path → @SExpr (d1Params univs)) :=
          funext fun path => nomatch path
        rw [hm2] at H
        simpa only [d0ToD1Expr_const, d0ToD1Expr_mkInst] using H))
  | appDF _ _ _ _ _ ihA ihCod ihf iha ihResult =>
    rw [d0ToD1Expr_inst, d0ToD1Expr_inst, d0ToD1Expr_sort] at ihResult
    simpa only [List.map_cons, d0ToD1Expr_app, d0ToD1Expr_forallE,
      d0ToD1Expr_inst] using
      IsDefEqStrong.appDF ihA ihCod ihf iha ihResult
  | lamDF _ _ _ _ _ ihA ihB ihB' ihBody ihBody' =>
    simpa only [List.map_cons, d0ToD1Expr_lam, d0ToD1Expr_forallE] using
      IsDefEqStrong.lamDF ihA ihB ihB' ihBody ihBody'
  | forallEDF _ _ _ ihA ihBody ihBody' =>
    simpa only [List.map_cons, d0ToD1Expr_forallE, d0ToD1Expr_sort,
      d0ToD1Level_imax] using
      IsDefEqStrong.forallEDF ihA ihBody ihBody'
  | defeqDF _ _ ihA ihe => exact .defeqDF ihA ihe
  | beta _ _ _ _ ihBody ihArg ihApp ihInst =>
    simp only [d0ToD1Expr_app, d0ToD1Expr_lam,
      d0ToD1Expr_inst] at ihApp
    simp only [d0ToD1Expr_inst] at ihInst
    simpa only [List.map_cons, d0ToD1Expr_app, d0ToD1Expr_lam,
      d0ToD1Expr_inst] using
      IsDefEqStrong.beta ihBody ihArg ihApp ihInst
  | @eta Gamma e A B _ _ ihTerm ihLam =>
    rw [d0ToD1Expr_lam, d0ToD1Expr_app, d0ToD1Expr_lift',
      d0ToD1Expr_bvar, d0ToD1Expr_forallE] at ihLam ⊢
    exact IsDefEqStrong.eta ihTerm ihLam
  | proofIrrel _ _ _ ihp ihh ihh' => exact .proofIrrel ihp ihh ihh'
  | @defn c ci Gamma ls u r hreg hlen hTy F hF action hRhs
      ihTy ihF ihRhs =>
    have hm2 : (fun path => d0ToD1Expr univs (Empty.elim path)) =
        (Empty.elim :
          (Pattern.const c).Path → @SExpr (d1Params univs)) :=
      funext fun path => nomatch path
    let F' : ∀ cl : CtorBundle.IsCtor c, CtorBundle c cl := fun cl =>
      d0CtorBundleToD1 univs cl (F (d1CtorToD0 univs cl))
    have action' := d0Action_to_d1 univs action
    rw [d0ToD1Expr_const, d0ToD1Expr_mkInst, hm2] at action'
    have hRhs' := ihRhs
    rw [d0ToD1Expr_rhs_applyS, hm2, d0ToD1Expr_mkInst] at hRhs'
    have hTy' := ihTy
    rw [d0ToD1Expr_mkInst, d0ToD1Expr_sort] at hTy'
    have hF' : ∀ cl, IsDefEqStrong (Gamma.map (d0ToD1Expr univs))
        (SExpr.mkInst (ls.map (d0ToD1Level univs)) ci.type)
        ((F' cl).rhs (ls.map (d0ToD1Level univs)))
        (.sort (F' cl).u) := by
      intro cl
      dsimp only [F']
      rw [← d0CtorBundleToD1_rhs, d0CtorBundleToD1_u]
      have H := ihF (d1CtorToD0 univs cl)
      simp only [d0ToD1Expr_mkInst, d0ToD1Expr_sort] at H
      exact H
    simpa only [d0ToD1Expr_const, d0ToD1Expr_mkInst,
      d0ToD1Expr_rhs_applyS, hm2] using
      IsDefEqStrong.defn (d0Env_le_d1Env.constants hreg)
        (by simpa only [List.length_map] using hlen)
        hTy' F' hF' action' hRhs'
  | extra action _ _ ihLeft ihRight =>
    rw [d0ToD1Expr_rhs_applyS] at ihRight
    simpa only [d0ToD1Expr_rhs_applyS] using
      IsDefEqStrong.extra (d0Action_to_d1 univs action) ihLeft ihRight

@[simp] theorem d1Expr_context_roundtrip (univs : Nat)
    (Gamma : List (@SExpr (d1Params univs))) :
    (Gamma.map (d1ToD0Expr univs)).map (d0ToD1Expr univs) = Gamma := by
  simp [List.map_map, Function.comp_def]

@[simp] theorem d1Level_list_roundtrip (univs : Nat)
    (ls : List (@SLevel (d1Params univs))) :
    (ls.map (d1ToD0Level univs)).map (d0ToD1Level univs) = ls := by
  simp [List.map_map, Function.comp_def]

section SemanticCertificates

/-! ## D1 semantic certificates -/

theorem d1StructureEtaSound (univs : Nat) :
    @Params.StructureEtaSound (d1Params univs) := by
  letI : Params := d1Params univs
  intro rule levels Gamma params major hreg
  exact (d1Env_no_structEta rule hreg).elim

def D1ContextValid (univs : Nat)
    (Gamma : List (@SExpr (d1Params univs))) : Prop :=
  letI : Params := d1Params univs
  OnCtx (Gamma.map SExpr.reify) (d1Env.IsType univs)

def D1TypesDefEq (univs : Nat) {Gamma : List (@SExpr (d1Params univs))}
    (A B : @SExpr (d1Params univs)) : Prop :=
  letI : Params := d1Params univs
  ∃ u, IsDefEq Gamma A B (.sort u)

theorem d1TypeUniq (univs : Nat)
    {Gamma : List (@SExpr (d1Params univs))}
    {x A B : @SExpr (d1Params univs)}
    (hGamma : D1ContextValid univs Gamma)
    (hxA : @IsDefEq (d1Params univs) Gamma x x A)
    (hxB : @IsDefEq (d1Params univs) Gamma x x B) :
    D1TypesDefEq (Gamma := Gamma) univs A B := by
  letI : Params := d1Params univs
  change OnCtx (Gamma.map SExpr.reify) (d1Env.IsType univs) at hGamma
  change ∃ u, IsDefEq Gamma A B (.sort u)
  have hxA' := hxA.reify hGamma
  have hxB' := hxB.reify hGamma
  obtain ⟨u, hAB⟩ := hxA'.uniq d1Env_wf hGamma hxB'
  have hlevels := (VEnv.CtxStrong.strong d1Env_ordered hGamma).levelWF
  have hAB' := SExpr.IsDefEq.mkS (d1StructureEtaSound univs) hAB hlevels
  have hctx : (Gamma.map SExpr.reify).map SExpr.mk = Gamma := by
    rw [List.map_map]
    exact List.map_id''' Gamma fun term _ => SExpr.mk_reify term
  rw [hctx] at hAB'
  refine ⟨SLevel.mk u, ?_⟩
  simpa only [SExpr.mk_reify, SExpr.mk] using hAB'

theorem d1TypesTrans (univs : Nat)
    {Gamma : List (@SExpr (d1Params univs))}
    {A B C : @SExpr (d1Params univs)}
    (hGamma : D1ContextValid univs Gamma)
    (hAB : D1TypesDefEq (Gamma := Gamma) univs A B)
    (hBC : D1TypesDefEq (Gamma := Gamma) univs B C) :
    D1TypesDefEq (Gamma := Gamma) univs A C := by
  letI : Params := d1Params univs
  obtain ⟨u, hAB⟩ := hAB
  obtain ⟨v, hBC⟩ := hBC
  obtain ⟨w, huv⟩ := d1TypeUniq univs hGamma hAB.hasType.2 hBC.hasType.1
  exact ⟨u, hAB.trans (huv.symm.defeqDF hBC)⟩

theorem d1TypesInst (univs : Nat)
    {Gamma : List (@SExpr (d1Params univs))}
    {D B B' e : @SExpr (d1Params univs)}
    (hBB' : D1TypesDefEq (Gamma := D :: Gamma) univs B B')
    (he : @IsDefEq (d1Params univs) Gamma e e D) :
    D1TypesDefEq (Gamma := Gamma) univs
      (@SExpr.inst (d1Params univs) B e)
      (@SExpr.inst (d1Params univs) B' e) := by
  letI : Params := d1Params univs
  obtain ⟨u, hBB'⟩ := hBB'
  have hsubst := hBB'.subst
    (Ctx.Subst.one IsDefEq.weak' IsDefEq.bvar he)
  change IsDefEq Gamma (B.inst e) (B'.inst e) (.sort u) at hsubst
  exact ⟨u, hsubst⟩

theorem d1ForallEInv (univs : Nat)
    {Gamma : List (@SExpr (d1Params univs))}
    {A B A' B' : @SExpr (d1Params univs)}
    (hGamma : D1ContextValid univs Gamma)
    (hPi : D1TypesDefEq (Gamma := Gamma) univs
      (@SExpr.forallE (d1Params univs) A B)
      (@SExpr.forallE (d1Params univs) A' B')) :
    D1TypesDefEq (Gamma := Gamma) univs A A' ∧
      D1TypesDefEq (Gamma := A :: Gamma) univs B B' := by
  letI : Params := d1Params univs
  change OnCtx (Gamma.map SExpr.reify) (d1Env.IsType univs) at hGamma
  obtain ⟨_, hPi⟩ := hPi
  have hPi' := hPi.reify hGamma
  have hPiU : d1Env.IsDefEqU univs (Gamma.map SExpr.reify)
      (.forallE A.reify B.reify) (.forallE A'.reify B'.reify) :=
    ⟨_, hPi'⟩
  obtain ⟨⟨u, hA⟩, v, hB⟩ :=
    hPiU.forallE_inv d1Env_wf hGamma
  have hlevels := (VEnv.CtxStrong.strong d1Env_ordered hGamma).levelWF
  have hA' := SExpr.IsDefEq.mkS (d1StructureEtaSound univs) hA hlevels
  have hActx : (Gamma.map SExpr.reify).map SExpr.mk = Gamma := by
    rw [List.map_map]
    exact List.map_id''' Gamma fun term _ => SExpr.mk_reify term
  rw [hActx] at hA'
  have hAwf : (A.reify).LevelWF univs := SExpr.reify_levelWF A
  have hB' := SExpr.IsDefEq.mkS (d1StructureEtaSound univs) hB
    ⟨hlevels, hAwf⟩
  have hBctx : ((A.reify :: Gamma.map SExpr.reify).map SExpr.mk) =
      A :: Gamma := by
    rw [List.map_cons, hActx, SExpr.mk_reify]
  rw [hBctx] at hB'
  constructor
  · refine ⟨SLevel.mk u, ?_⟩
    simpa only [SExpr.mk_reify, SExpr.mk] using hA'
  · refine ⟨SLevel.mk v, ?_⟩
    simpa only [SExpr.mk_reify, SExpr.mk] using hB'

structure D1SpineConsView (univs : Nat)
    {Gamma : List (@SExpr (d1Params univs))}
    (D B e : @SExpr (d1Params univs))
    (es : List (@SExpr (d1Params univs)))
    (R : @SExpr (d1Params univs)) where
  domain : @SExpr (d1Params univs)
  codomain : @SExpr (d1Params univs)
  domainEq : D1TypesDefEq (Gamma := Gamma) univs D domain
  codomainEq : D1TypesDefEq (Gamma := D :: Gamma) univs B codomain
  argument : @IsDefEq (d1Params univs) Gamma e e domain
  tail : @SpineWF (d1Params univs) Gamma
    (@SExpr.inst (d1Params univs) codomain e) es R

theorem d1SpineConsView_nonempty (univs : Nat)
    {Gamma : List (@SExpr (d1Params univs))}
    {D B Head e R : @SExpr (d1Params univs)}
    {es : List (@SExpr (d1Params univs))}
    (hGamma : D1ContextValid univs Gamma)
    (hHead : D1TypesDefEq (Gamma := Gamma) univs
      (@SExpr.forallE (d1Params univs) D B) Head)
    (H : @SpineWF (d1Params univs) Gamma Head (e :: es) R) :
    Nonempty (D1SpineConsView (Gamma := Gamma) univs D B e es R) := by
  letI : Params := d1Params univs
  generalize hargsEq : e :: es = args at H
  induction H generalizing D B e es with
  | nil => cases hargsEq
  | @cons _ domain _ _ codomain harg htail ih =>
    cases hargsEq
    obtain ⟨hdom, hbody⟩ := d1ForallEInv univs hGamma hHead
    exact ⟨{
      domain := domain
      codomain := codomain
      domainEq := hdom
      codomainEq := hbody
      argument := harg
      tail := htail }⟩
  | @conv _ Head' u _ _ hconv htail ih =>
    exact ih (d1TypesTrans univs hGamma hHead ⟨u, hconv⟩) hargsEq
  | @ret _ _ R' _ _ htail hret ih =>
    let ⟨view⟩ := ih hHead hargsEq
    exact ⟨{ view with tail := .ret view.tail hret }⟩

noncomputable def d1SpineConsView (univs : Nat)
    {Gamma : List (@SExpr (d1Params univs))}
    {D B Head e R : @SExpr (d1Params univs)}
    {es : List (@SExpr (d1Params univs))}
    (hGamma : D1ContextValid univs Gamma)
    (hHead : D1TypesDefEq (Gamma := Gamma) univs
      (@SExpr.forallE (d1Params univs) D B) Head)
    (H : @SpineWF (d1Params univs) Gamma Head (e :: es) R) :
    D1SpineConsView (Gamma := Gamma) univs D B e es R :=
  Classical.choice (d1SpineConsView_nonempty univs hGamma hHead H)

theorem D1SpineConsView.argumentExpected (univs : Nat)
    {Gamma : List (@SExpr (d1Params univs))}
    {D B e R : @SExpr (d1Params univs)}
    {es : List (@SExpr (d1Params univs))}
    (view : D1SpineConsView (Gamma := Gamma) univs D B e es R) :
    @IsDefEq (d1Params univs) Gamma e e D := by
  letI : Params := d1Params univs
  obtain ⟨_, hdom⟩ := view.domainEq
  exact hdom.symm.defeqDF view.argument

theorem D1SpineConsView.restEq (univs : Nat)
    {Gamma : List (@SExpr (d1Params univs))}
    {D B e R : @SExpr (d1Params univs)}
    {es : List (@SExpr (d1Params univs))}
    (view : D1SpineConsView (Gamma := Gamma) univs D B e es R) :
    D1TypesDefEq (Gamma := Gamma) univs
      (@SExpr.inst (d1Params univs) B e)
      (@SExpr.inst (d1Params univs) view.codomain e) :=
  d1TypesInst univs view.codomainEq (view.argumentExpected univs)

theorem d1PathSpineOfSpineWF (univs : Nat)
    {Gamma : List (@SExpr (d1Params univs))}
    {alpha : Type}
    {value type : alpha → @SExpr (d1Params univs)}
    {A B : @SExpr (d1Params univs)} {paths : List alpha}
    (hGamma : D1ContextValid univs Gamma)
    (htyped : ∀ path, @IsDefEq (d1Params univs) Gamma
      (value path) (value path) (type path))
    (H : @SpineWF (d1Params univs) Gamma A (paths.map value) B) :
    @PathSpineWF (d1Params univs) Gamma alpha value type A paths B := by
  letI : Params := d1Params univs
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
        d1TypeUniq univs hGamma (htyped path) harg
      exact .cons hdomain (ih hrest)
  | @conv Head Head' u es result hHead htail ih =>
    exact .conv hHead (ih hargs)
  | @ret Head es result result' u htail hresult ih =>
    exact .ret (ih hargs) hresult

theorem d1ZeroCaptureValues (univs : Nat)
    {recLs ctorLs : List (@SLevel (d1Params univs))}
    {recArgs ctorArgs : List (@SExpr (d1Params univs))}
    {mcap : (RecursorIotaPattern ``Nat.rec 3 ``Nat.zero 0).Path →
      @SExpr (d1Params univs)}
    (H : @Pattern.MatchesS (d1Params univs)
      (RecursorIotaPattern ``Nat.rec 3 ``Nat.zero 0)
      (@SExpr.app (d1Params univs)
        (recArgs.foldr
          (fun a f => @SExpr.app (d1Params univs) f a)
          (@SExpr.const (d1Params univs) ``Nat.rec recLs))
        (ctorArgs.foldr
          (fun a f => @SExpr.app (d1Params univs) f a)
          (@SExpr.const (d1Params univs) ``Nat.zero ctorLs))) recLs mcap) :
    recArgs.length = 3 ∧ ctorArgs = [] ∧
      (natCapturePaths NatGeneration.flatCtors[0]).map mcap =
        recArgs.reverse := by
  letI : Params := d1Params univs
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

theorem d1SuccCaptureValues (univs : Nat)
    {recLs ctorLs : List (@SLevel (d1Params univs))}
    {recArgs ctorArgs : List (@SExpr (d1Params univs))}
    {mcap : (RecursorIotaPattern ``Nat.rec 3 ``Nat.succ 1).Path →
      @SExpr (d1Params univs)}
    (H : @Pattern.MatchesS (d1Params univs)
      (RecursorIotaPattern ``Nat.rec 3 ``Nat.succ 1)
      (@SExpr.app (d1Params univs)
        (recArgs.foldr
          (fun a f => @SExpr.app (d1Params univs) f a)
          (@SExpr.const (d1Params univs) ``Nat.rec recLs))
        (ctorArgs.foldr
          (fun a f => @SExpr.app (d1Params univs) f a)
          (@SExpr.const (d1Params univs) ``Nat.succ ctorLs))) recLs mcap) :
    recArgs.length = 3 ∧ ctorArgs.length = 1 ∧
      (natCapturePaths NatGeneration.flatCtors[1]).map mcap =
        recArgs.reverse ++ ctorArgs.reverse := by
  letI : Params := d1Params univs
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

def d1ProbeNatZeroRuleType (univs : Nat)
    (level : @SLevel (d1Params univs)) : @SExpr (d1Params univs) :=
  letI : Params := d1Params univs
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

theorem d1ProbeNatZeroRuleTypeS_eq (univs : Nat)
    (level : @SLevel (d1Params univs)) :
    @SExpr.mkInst (d1Params univs) [level]
        (NatGeneration.rule 0 NatGeneration.flatCtors[0]).type =
      d1ProbeNatZeroRuleType univs level := by
  rw [probeNatZeroRuleTypeV_eq]
  rfl

def d1ProbeNatSuccRuleType (univs : Nat)
    (level : @SLevel (d1Params univs)) : @SExpr (d1Params univs) :=
  letI : Params := d1Params univs
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

theorem d1ProbeNatSuccRuleTypeS_eq (univs : Nat)
    (level : @SLevel (d1Params univs)) :
    @SExpr.mkInst (d1Params univs) [level]
        (NatGeneration.rule 1 NatGeneration.flatCtors[1]).type =
      d1ProbeNatSuccRuleType univs level := by
  rw [probeNatSuccRuleTypeV_eq]
  rfl

theorem d1IotaRule_nonempty (univs : Nat)
    {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (H : (d1Params univs).Pat
      (RecursorIotaPattern rec major ctor arity) r) :
    Nonempty (@Pattern.IotaRule (d1Params univs)
      rec major ctor arity r) := by
  letI : Params := d1Params univs
  change D1Pat _ _ at H
  cases H with
  | old H =>
    let oldRule := d0IotaRule univs H
    rcases oldRule with
      ⟨oldPat, df, registered, rhsClosed, capturePaths, rhsTower⟩
    exact ⟨{
      pat := D1Pat.old (by exact oldPat)
      df := df
      registered := d0Env_le_d1Env.defeqs registered
      rhsClosed := rhsClosed
      capturePaths := capturePaths
      rhsTower := rhsTower }⟩

noncomputable def d1IotaRule (univs : Nat)
    {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (H : (d1Params univs).Pat
      (RecursorIotaPattern rec major ctor arity) r) :
    @Pattern.IotaRule (d1Params univs) rec major ctor arity r :=
  Classical.choice (d1IotaRule_nonempty univs H)

/-- The mutual-definition extension adds no iota rules, so generated
structural descent is transported verbatim from D0. -/
theorem d1IotaStructuralDescent (univs : Nat)
    {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (H : (d1Params univs).Pat
      (RecursorIotaPattern rec major ctor arity) r) :
    ∃ rule : @Pattern.IotaRule (d1Params univs) rec major ctor arity r,
      @Pattern.IotaRule.StructuralDescent (d1Params univs)
        rec major ctor arity r rule := by
  letI : Params := d1Params univs
  change D1Pat _ _ at H
  cases H with
  | old H =>
    obtain ⟨oldRule, hdescent⟩ := d0IotaStructuralDescent univs H
    rcases oldRule with
      ⟨oldPat, df, registered, rhsClosed, capturePaths, rhsTower⟩
    let rule : @Pattern.IotaRule (d1Params univs)
        rec major ctor arity r := {
      pat := D1Pat.old oldPat
      df := df
      registered := d0Env_le_d1Env.defeqs registered
      rhsClosed := rhsClosed
      capturePaths := capturePaths
      rhsTower := rhsTower }
    refine ⟨rule, Pattern.IotaRule.StructuralDescent.rebase
      hdescent rule ?_⟩
    rfl

theorem d1NatRecEnvLookup :
    d1Env.constants ``Nat.rec =
      some (VInductDecl.recConst 0 ``Nat 0 InductiveFixtures.natType) :=
  d0Env_le_d1Env.constants d0NatRecEnvLookup

theorem d1NatZeroEnvLookup :
    d1Env.constants ``Nat.zero =
      some InductiveFixtures.natType.ctors[0].toVConstant :=
  d0Env_le_d1Env.constants d0NatZeroEnvLookup

theorem d1NatSuccEnvLookup :
    d1Env.constants ``Nat.succ =
      some InductiveFixtures.natType.ctors[1].toVConstant :=
  d0Env_le_d1Env.constants d0NatSuccEnvLookup

theorem natRule_rhs_ne_d1MutA {i : Nat}
    {constructor : NormalizedBlockCtor}
    (hentry : NatGeneration.flatCtors[i]? = some constructor) :
    (NatGeneration.rule i constructor).rhs ≠ d1MutAVal.toDefEq.rhs := by
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

theorem natRule_rhs_ne_d1MutB {i : Nat}
    {constructor : NormalizedBlockCtor}
    (hentry : NatGeneration.flatCtors[i]? = some constructor) :
    (NatGeneration.rule i constructor).rhs ≠ d1MutBVal.toDefEq.rhs := by
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

theorem d1MutA_not_ctor (univs : Nat)
    (cl : @CtorBundle.IsCtor (d1Params univs) d1MutAVal.name) : False := by
  letI : Params := d1Params univs
  have hshape : ctorLike cl.cl.1 = true := by
    have hs := cl.cl.2.2
    cases hc : cl.cl.1 <;> simp [ctorLike, hc] at hs ⊢
  have hc := cl.cl.2.1
  change d1Classify d1MutAVal.name = some cl.cl.1 at hc
  have hcl : cl.cl.1 = .symb 0 := by
    simpa [d1Classify] using hc.symm
  rw [hcl] at hshape
  simp [ctorLike] at hshape

theorem d1MutB_not_ctor (univs : Nat)
    (cl : @CtorBundle.IsCtor (d1Params univs) d1MutBVal.name) : False := by
  letI : Params := d1Params univs
  have hshape : ctorLike cl.cl.1 = true := by
    have hs := cl.cl.2.2
    cases hc : cl.cl.1 <;> simp [ctorLike, hc] at hs ⊢
  have hc := cl.cl.2.1
  change d1Classify d1MutBVal.name = some cl.cl.1 at hc
  have hne := d1MutA_name_ne_mutB
  have hcl : cl.cl.1 = .symb 0 := by
    simpa [d1Classify, Ne.symm hne] using hc.symm
  rw [hcl] at hshape
  simp [ctorLike] at hshape

theorem d1Ctor_name_ne_mutA (univs : Nat) {c : Name}
    (cl : @CtorBundle.IsCtor (d1Params univs) c) :
    c ≠ d1MutAVal.name := by
  intro hc
  subst c
  exact d1MutA_not_ctor univs cl

theorem d1Ctor_name_ne_mutB (univs : Nat) {c : Name}
    (cl : @CtorBundle.IsCtor (d1Params univs) c) :
    c ≠ d1MutBVal.name := by
  intro hc
  subst c
  exact d1MutB_not_ctor univs cl

theorem d1NatTypeStrong (univs : Nat)
    (Gamma : List (@SExpr (d1Params univs))) :
    @IsDefEqStrong (d1Params univs) Gamma
      (@SExpr.const (d1Params univs) ``Nat [])
      (@SExpr.const (d1Params univs) ``Nat [])
      (@SExpr.sort (d1Params univs)
        (@SLevel.succ (d1Params univs) (@SLevel.zero (d1Params univs)))) := by
  have H := d0StrongToD1 univs
    (d0NatTypeStrong univs (Gamma.map (d1ToD0Expr univs)))
  simp only [d1Expr_context_roundtrip, d0ToD1Expr_const,
    d0ToD1Expr_sort, List.map_nil] at H
  change @IsDefEqStrong (d1Params univs) Gamma
    (@SExpr.const (d1Params univs) ``Nat [])
    (@SExpr.const (d1Params univs) ``Nat [])
    (@SExpr.sort (d1Params univs)
      (@SLevel.succ (d1Params univs) (@SLevel.zero (d1Params univs)))) at H
  exact H

theorem d1NatZeroStrong (univs : Nat)
    (Gamma : List (@SExpr (d1Params univs))) :
    @IsDefEqStrong (d1Params univs) Gamma
      (@SExpr.const (d1Params univs) ``Nat.zero [])
      (@SExpr.const (d1Params univs) ``Nat.zero [])
      (@SExpr.const (d1Params univs) ``Nat []) := by
  have H := d0StrongToD1 univs
    (d0NatZeroStrong univs (Gamma.map (d1ToD0Expr univs)))
  simpa only [d1Expr_context_roundtrip, d0ToD1Expr_const,
    List.map_nil] using H

theorem d1NatSuccStrong (univs : Nat)
    (Gamma : List (@SExpr (d1Params univs))) :
    @IsDefEqStrong (d1Params univs) Gamma
      (@SExpr.const (d1Params univs) ``Nat.succ [])
      (@SExpr.const (d1Params univs) ``Nat.succ [])
      (@SExpr.forallE (d1Params univs)
        (@SExpr.const (d1Params univs) ``Nat [])
        (@SExpr.const (d1Params univs) ``Nat [])) := by
  have H0 := natStrongToD0 univs
    (natSuccStrong univs
      ((Gamma.map (d1ToD0Expr univs)).map (d0ToNatExpr univs)))
  simp only [d0Expr_context_roundtrip, natToD0Expr_const,
    natToD0Expr_forallE, List.map_nil] at H0
  have H := d0StrongToD1 univs H0
  simpa only [d1Expr_context_roundtrip, d0ToD1Expr_const,
    d0ToD1Expr_forallE, List.map_nil] using H

theorem d1D0DefStrong (univs : Nat)
    (Gamma : List (@SExpr (d1Params univs))) :
    @IsDefEqStrong (d1Params univs) Gamma
      (@SExpr.const (d1Params univs) d0DefVal.name [])
      (@SExpr.const (d1Params univs) ``Nat.zero [])
      (@SExpr.const (d1Params univs) ``Nat []) := by
  have H := d0StrongToD1 univs
    (d0DefStrong univs (Gamma.map (d1ToD0Expr univs)))
  simpa only [d1Expr_context_roundtrip, d0ToD1Expr_const,
    List.map_nil] using H

theorem d1D0DefConstStrong (univs : Nat)
    (Gamma : List (@SExpr (d1Params univs))) :
    @IsDefEqStrong (d1Params univs) Gamma
      (@SExpr.const (d1Params univs) d0DefVal.name [])
      (@SExpr.const (d1Params univs) d0DefVal.name [])
      (@SExpr.const (d1Params univs) ``Nat []) := by
  letI : Params := d1Params univs
  exact (d1D0DefStrong univs Gamma).trans (d1D0DefStrong univs Gamma).symm

theorem d1MutBRhsStrong (univs : Nat)
    (Gamma : List (@SExpr (d1Params univs))) :
    @IsDefEqStrong (d1Params univs) Gamma
      (@SExpr.app (d1Params univs)
        (@SExpr.const (d1Params univs) ``Nat.succ [])
        (@SExpr.const (d1Params univs) d0DefVal.name []))
      (@SExpr.app (d1Params univs)
        (@SExpr.const (d1Params univs) ``Nat.succ [])
        (@SExpr.const (d1Params univs) d0DefVal.name []))
      (@SExpr.const (d1Params univs) ``Nat []) := by
  letI : Params := d1Params univs
  exact IsDefEqStrong.appDF
    (d1NatTypeStrong univs Gamma)
    (d1NatTypeStrong univs (.const ``Nat [] :: Gamma))
    (d1NatSuccStrong univs Gamma)
    (d1D0DefConstStrong univs Gamma)
    (d1NatTypeStrong univs Gamma)

theorem d1MutBDefStrong (univs : Nat)
    (Gamma : List (@SExpr (d1Params univs))) :
    @IsDefEqStrong (d1Params univs) Gamma
      (@SExpr.const (d1Params univs) d1MutBVal.name [])
      (@SExpr.app (d1Params univs)
        (@SExpr.const (d1Params univs) ``Nat.succ [])
        (@SExpr.const (d1Params univs) d0DefVal.name []))
      (@SExpr.const (d1Params univs) ``Nat []) := by
  letI : Params := d1Params univs
  let r : (Pattern.const d1MutBVal.name).RHS ×
      (Pattern.const d1MutBVal.name).Check :=
    (.fixed d1MutBVal.value d1MutBClosed, .true)
  let action : Pattern.Action Gamma r (.const d1MutBVal.name []) []
      Empty.elim (.const ``Nat []) := {
    pat := D1Pat.defnB
    matched := by
      refine cast ?_ (@Pattern.MatchesS.const (d1Params univs)
        d1MutBVal.name [])
      congr 1
      funext path
      exact Empty.elim path
    dfs := []
    defeqs := rfl
    checked := by simp
    sound := by
      have H := @IsDefEq.extra (d1Params univs) d1MutBVal.toDefEq Gamma []
        d1Env_defeq_mutB rfl
      change IsDefEq Gamma (.const d1MutBVal.name [])
        (.app (.const ``Nat.succ []) (.const d0DefVal.name []))
        (.const ``Nat []) at H
      exact H }
  let F : ∀ cl : CtorBundle.IsCtor d1MutBVal.name,
      CtorBundle d1MutBVal.name cl := fun cl =>
    (d1MutB_not_ctor univs cl).elim
  refine @IsDefEqStrong.defn (d1Params univs) d1MutBVal.name
    d1MutBVal.toVConstant Gamma []
    (@SLevel.succ (d1Params univs) (@SLevel.zero (d1Params univs))) r
    d1Env_d1MutB_lookup rfl ?_ F ?_ action ?_
  · change IsDefEqStrong Gamma (.const ``Nat []) (.const ``Nat [])
      (.sort (.succ .zero))
    exact d1NatTypeStrong univs Gamma
  · intro cl
    exact (d1MutB_not_ctor univs cl).elim
  · change IsDefEqStrong Gamma
      (.app (.const ``Nat.succ []) (.const d0DefVal.name []))
      (.app (.const ``Nat.succ []) (.const d0DefVal.name []))
      (.const ``Nat [])
    exact d1MutBRhsStrong univs Gamma

theorem d1MutBConstStrong (univs : Nat)
    (Gamma : List (@SExpr (d1Params univs))) :
    @IsDefEqStrong (d1Params univs) Gamma
      (@SExpr.const (d1Params univs) d1MutBVal.name [])
      (@SExpr.const (d1Params univs) d1MutBVal.name [])
      (@SExpr.const (d1Params univs) ``Nat []) := by
  letI : Params := d1Params univs
  exact (d1MutBDefStrong univs Gamma).trans (d1MutBDefStrong univs Gamma).symm

theorem d1MutADefStrong (univs : Nat)
    (Gamma : List (@SExpr (d1Params univs))) :
    @IsDefEqStrong (d1Params univs) Gamma
      (@SExpr.const (d1Params univs) d1MutAVal.name [])
      (@SExpr.const (d1Params univs) d1MutBVal.name [])
      (@SExpr.const (d1Params univs) ``Nat []) := by
  letI : Params := d1Params univs
  let r : (Pattern.const d1MutAVal.name).RHS ×
      (Pattern.const d1MutAVal.name).Check :=
    (.fixed d1MutAVal.value d1MutAClosed, .true)
  let action : Pattern.Action Gamma r (.const d1MutAVal.name []) []
      Empty.elim (.const ``Nat []) := {
    pat := D1Pat.defnA
    matched := by
      refine cast ?_ (@Pattern.MatchesS.const (d1Params univs)
        d1MutAVal.name [])
      congr 1
      funext path
      exact Empty.elim path
    dfs := []
    defeqs := rfl
    checked := by simp
    sound := by
      have H := @IsDefEq.extra (d1Params univs) d1MutAVal.toDefEq Gamma []
        d1Env_defeq_mutA rfl
      change IsDefEq Gamma (.const d1MutAVal.name [])
        (.const d1MutBVal.name [])
        (.const ``Nat []) at H
      exact H }
  let F : ∀ cl : CtorBundle.IsCtor d1MutAVal.name,
      CtorBundle d1MutAVal.name cl := fun cl =>
    (d1MutA_not_ctor univs cl).elim
  refine @IsDefEqStrong.defn (d1Params univs) d1MutAVal.name
    d1MutAVal.toVConstant Gamma []
    (@SLevel.succ (d1Params univs) (@SLevel.zero (d1Params univs))) r
    d1Env_d1MutA_lookup rfl ?_ F ?_ action ?_
  · change IsDefEqStrong Gamma (.const ``Nat []) (.const ``Nat [])
      (.sort (.succ .zero))
    exact d1NatTypeStrong univs Gamma
  · intro cl
    exact (d1MutA_not_ctor univs cl).elim
  · change IsDefEqStrong Gamma
      (.const d1MutBVal.name []) (.const d1MutBVal.name [])
      (.const ``Nat [])
    exact d1MutBConstStrong univs Gamma

/-- `Params.Semantic.defn` for the extended inventory: the inherited
`d0def` rule plus the two mutual definitions.  The mutual chain unfolds
`d1mutA ↦ d1mutB` (its block-mate) and `d1mutB ↦ Nat.succ d0def`. -/
theorem d1Defn (univs : Nat) {c : Name}
    {r : (Pattern.const c).RHS × (Pattern.const c).Check}
    (H : (d1Params univs).Pat (.const c) r) :
    ∃ (value : VExpr) (closed : value.Closed),
      r = (.fixed value closed, .true) ∧
      ∀ {ci : VConstant} {ls : List (@SLevel (d1Params univs))}
        {Gamma : List (@SExpr (d1Params univs))},
        d1Env.constants c = some ci → ls.length = ci.uvars →
        @IsDefEqStrong (d1Params univs) Gamma
          (@SExpr.const (d1Params univs) c ls)
          (@SExpr.mkInst (d1Params univs) ls value)
          (@SExpr.mkInst (d1Params univs) ls ci.type) := by
  letI : Params := d1Params univs
  change D1Pat (.const c) r at H
  cases H with
  | old H =>
    cases H with
    | iota H => exact (natPat_no_const univs H).elim
    | defn =>
      refine ⟨d0DefVal.value, d0DefClosed, rfl, ?_⟩
      intro ci ls Gamma hci hlen
      have hlook : d1Env.constants d0DefVal.name =
          some d0DefVal.toVConstant :=
        d0Env_le_d1Env.constants d0Env_d0Def_lookup
      have hci' : ci = d0DefVal.toVConstant :=
        Option.some.inj (hci.symm.trans hlook)
      subst ci
      have hls : ls = [] := List.length_eq_zero_iff.mp hlen
      subst ls
      change @IsDefEqStrong (d1Params univs) Gamma
        (@SExpr.const (d1Params univs) d0DefVal.name [])
        (@SExpr.const (d1Params univs) ``Nat.zero [])
        (@SExpr.const (d1Params univs) ``Nat [])
      exact d1D0DefStrong univs Gamma
  | defnA =>
    refine ⟨d1MutAVal.value, d1MutAClosed, rfl, ?_⟩
    intro ci ls Gamma hci hlen
    have hci' : ci = d1MutAVal.toVConstant :=
      Option.some.inj (hci.symm.trans d1Env_d1MutA_lookup)
    subst ci
    have hls : ls = [] := List.length_eq_zero_iff.mp hlen
    subst ls
    change @IsDefEqStrong (d1Params univs) Gamma
      (@SExpr.const (d1Params univs) d1MutAVal.name [])
      (@SExpr.const (d1Params univs) d1MutBVal.name [])
      (@SExpr.const (d1Params univs) ``Nat [])
    exact d1MutADefStrong univs Gamma
  | defnB =>
    refine ⟨d1MutBVal.value, d1MutBClosed, rfl, ?_⟩
    intro ci ls Gamma hci hlen
    have hci' : ci = d1MutBVal.toVConstant :=
      Option.some.inj (hci.symm.trans d1Env_d1MutB_lookup)
    subst ci
    have hls : ls = [] := List.length_eq_zero_iff.mp hlen
    subst ls
    change @IsDefEqStrong (d1Params univs) Gamma
      (@SExpr.const (d1Params univs) d1MutBVal.name [])
      (@SExpr.app (d1Params univs)
        (@SExpr.const (d1Params univs) ``Nat.succ [])
        (@SExpr.const (d1Params univs) d0DefVal.name []))
      (@SExpr.const (d1Params univs) ``Nat [])
    exact d1MutBDefStrong univs Gamma

theorem d1Registered (univs : Nat)
    {df : VDefEq} {ls : List (@SLevel (d1Params univs))}
    {Gamma : List (@SExpr (d1Params univs))}
    (hreg : d1Env.defeqs df) (hlen : ls.length = df.uvars)
    (_hLhs : @IsDefEqStrong (d1Params univs) Gamma
      (@SExpr.mkInst (d1Params univs) ls df.lhs)
      (@SExpr.mkInst (d1Params univs) ls df.lhs)
      (@SExpr.mkInst (d1Params univs) ls df.type))
    (_hRhs : @IsDefEqStrong (d1Params univs) Gamma
      (@SExpr.mkInst (d1Params univs) ls df.rhs)
      (@SExpr.mkInst (d1Params univs) ls df.rhs)
      (@SExpr.mkInst (d1Params univs) ls df.type)) :
    @IsDefEqStrong (d1Params univs) Gamma
      (@SExpr.mkInst (d1Params univs) ls df.lhs)
      (@SExpr.mkInst (d1Params univs) ls df.rhs)
      (@SExpr.mkInst (d1Params univs) ls df.type) := by
  rw [d1Env_defeqs_iff] at hreg
  rcases hreg with hB | hA | hold
  · subst df
    change ls.length = 0 at hlen
    have hls : ls = [] := List.length_eq_zero_iff.mp hlen
    subst ls
    change @IsDefEqStrong (d1Params univs) Gamma
      (@SExpr.const (d1Params univs) d1MutBVal.name [])
      (@SExpr.app (d1Params univs)
        (@SExpr.const (d1Params univs) ``Nat.succ [])
        (@SExpr.const (d1Params univs) d0DefVal.name []))
      (@SExpr.const (d1Params univs) ``Nat [])
    exact d1MutBDefStrong univs Gamma
  · subst df
    change ls.length = 0 at hlen
    have hls : ls = [] := List.length_eq_zero_iff.mp hlen
    subst ls
    change @IsDefEqStrong (d1Params univs) Gamma
      (@SExpr.const (d1Params univs) d1MutAVal.name [])
      (@SExpr.const (d1Params univs) d1MutBVal.name [])
      (@SExpr.const (d1Params univs) ``Nat [])
    exact d1MutADefStrong univs Gamma
  · let oldGamma := Gamma.map (d1ToD0Expr univs)
    let oldLs := ls.map (d1ToD0Level univs)
    have oldLen : oldLs.length = df.uvars := by
      simpa [oldLs] using hlen
    have oldLhs : @IsDefEqStrong (d0Params univs) oldGamma
        (@SExpr.mkInst (d0Params univs) oldLs df.lhs)
        (@SExpr.mkInst (d0Params univs) oldLs df.lhs)
        (@SExpr.mkInst (d0Params univs) oldLs df.type) := by
      letI : Params := d0Params univs
      letI : Params.Semantic := d0Semantic univs
      exact Params.Semantic.closedHasTypeStrong
        (d0Env_ordered.defEqWF hold).1
    have oldRhs : @IsDefEqStrong (d0Params univs) oldGamma
        (@SExpr.mkInst (d0Params univs) oldLs df.rhs)
        (@SExpr.mkInst (d0Params univs) oldLs df.rhs)
        (@SExpr.mkInst (d0Params univs) oldLs df.type) := by
      letI : Params := d0Params univs
      letI : Params.Semantic := d0Semantic univs
      exact Params.Semantic.closedHasTypeStrong
        (d0Env_ordered.defEqWF hold).2
    have oldEq := d0Registered univs hold oldLen oldLhs oldRhs
    have H := d0StrongToD1 univs oldEq
    dsimp only [oldGamma, oldLs] at H
    simpa only [d1Expr_context_roundtrip, d0ToD1Expr_mkInst,
      d1Level_list_roundtrip] using H

noncomputable def d1Ctor (univs : Nat) {c : Name} {ci : VConstant}
    {ls : List (@SLevel (d1Params univs))}
    {Gamma : List (@SExpr (d1Params univs))}
    (hci : d1Env.constants c = some ci)
    (hlen : ls.length = ci.uvars)
    (cl : @CtorBundle.IsCtor (d1Params univs) c) :
    letI : Params := d1Params univs
    {F : CtorBundle c cl //
      IsDefEqStrong Gamma (SExpr.mkInst ls ci.type)
        (F.rhs ls) (.sort F.u)} := by
  letI : Params := d1Params univs
  let oldGamma := Gamma.map (d1ToD0Expr univs)
  let oldLs := ls.map (d1ToD0Level univs)
  have oldHci : d0Env.constants c = some ci :=
    d1Env_constants_old (d1Ctor_name_ne_mutA univs cl)
      (d1Ctor_name_ne_mutB univs cl) hci
  have oldLen : oldLs.length = ci.uvars := by
    simpa [oldLs] using hlen
  let oldF : @CtorBundle (d0Params univs) c (d1CtorToD0 univs cl) :=
    (d0Ctor univs (Gamma := oldGamma) (ls := oldLs)
      oldHci oldLen (d1CtorToD0 univs cl)).1
  have oldProof : @IsDefEqStrong (d0Params univs) oldGamma
      (@SExpr.mkInst (d0Params univs) oldLs ci.type)
      (@CtorBundle.rhs (d0Params univs) c (d1CtorToD0 univs cl)
        oldF oldLs)
      (@SExpr.sort (d0Params univs)
        (@CtorBundle.u (d0Params univs) c (d1CtorToD0 univs cl) oldF)) :=
    (d0Ctor univs (Gamma := oldGamma) (ls := oldLs)
      oldHci oldLen (d1CtorToD0 univs cl)).2
  let newF := d0CtorBundleToD1 univs cl oldF
  refine ⟨newF, ?_⟩
  have H := d0StrongToD1 univs oldProof
  dsimp only [oldGamma, oldLs] at H
  simp only [d1Expr_context_roundtrip,
    d0ToD1Expr_mkInst, d0ToD1Expr_sort] at H
  rw [d0CtorBundleToD1_rhs univs cl oldF
    (ls.map (d1ToD0Level univs))] at H
  simpa only [newF, d1Level_list_roundtrip,
    d0CtorBundleToD1_u] using H

/-- The D1 iota reduction sites, replayed against the extended environment
itself.  As in D0, the proof is *not* obtained by casting D1 contexts back
into the smaller environment: every typing step below is a D1-instance
derivation, so the certificate remains valid for contexts and captures that
mention the mutual definitions. -/
theorem d1IotaSite_nonempty (univs : Nat)
    {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {Gamma : List (@SExpr (d1Params univs))}
    {A majorTerm : @SExpr (d1Params univs)}
    {recLs ctorLs : List (@SLevel (d1Params univs))}
    {recArgs ctorArgs : List (@SExpr (d1Params univs))}
    {mcap : (RecursorIotaPattern rec major ctor arity).Path →
      @SExpr (d1Params univs)}
    (rule : @Pattern.IotaRule (d1Params univs) rec major ctor arity r)
    (captureType : (RecursorIotaPattern rec major ctor arity).Path →
      @SExpr (d1Params univs))
    (captureTyping : @Pattern.CaptureTyping (d1Params univs) Gamma
      (RecursorIotaPattern rec major ctor arity) mcap captureType)
    (hGamma : D1ContextValid univs Gamma)
    (typing : @Pattern.IotaTyping (d1Params univs) Gamma rec ctor recLs ctorLs
      recArgs ctorArgs majorTerm A)
    (matched : @Pattern.MatchesS (d1Params univs)
      (RecursorIotaPattern rec major ctor arity)
      (@SExpr.app (d1Params univs)
        (recArgs.foldr (fun a f => @SExpr.app (d1Params univs) f a)
          (@SExpr.const (d1Params univs) rec recLs))
        (ctorArgs.foldr (fun a f => @SExpr.app (d1Params univs) f a)
          (@SExpr.const (d1Params univs) ctor ctorLs))) recLs mcap)
    (redexSelf : @IsDefEq (d1Params univs) Gamma
      (@SExpr.app (d1Params univs)
        (recArgs.foldr (fun a f => @SExpr.app (d1Params univs) f a)
          (@SExpr.const (d1Params univs) rec recLs))
        (ctorArgs.foldr (fun a f => @SExpr.app (d1Params univs) f a)
          (@SExpr.const (d1Params univs) ctor ctorLs)))
      (@SExpr.app (d1Params univs)
        (recArgs.foldr (fun a f => @SExpr.app (d1Params univs) f a)
          (@SExpr.const (d1Params univs) rec recLs))
        (ctorArgs.foldr (fun a f => @SExpr.app (d1Params univs) f a)
          (@SExpr.const (d1Params univs) ctor ctorLs))) A)
    (AType : ∃ u, @IsDefEq (d1Params univs) Gamma A A
      (@SExpr.sort (d1Params univs) u)) :
    Nonempty (@Pattern.IotaReductionSite (d1Params univs) Gamma rec major ctor
      arity r rule recLs ctorLs recArgs ctorArgs majorTerm A mcap captureType
      captureTyping) := by
  letI : Params := d1Params univs
  have hpatD1 := rule.pat
  change D1Pat _ _ at hpatD1
  have hpat : NatPat (RecursorIotaPattern rec major ctor arity) r := by
    cases hpatD1 with
    | old H =>
      cases H with
      | iota H' => exact H'
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
  have hregD1 := ruleRegistered
  change d1Env.defeqs df at hregD1
  have hreg : natFinalEnv.defeqs df := by
    rw [d1Env_defeqs_iff] at hregD1
    rcases hregD1 with hnewB | hnewA | hold
    · subst df
      exact (natRule_rhs_ne_d1MutB hentry hrhs).elim
    · subst df
      exact (natRule_rhs_ne_d1MutA hentry hrhs).elim
    · rw [d0Env_defeqs_iff] at hold
      rcases hold with hnew0 | hold0
      · subst df
        exact (natRule_rhs_ne_d0Def hentry hrhs).elim
      · exact hold0
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
      d1NatRecEnvLookup
    change recLs.length = 1 at hrecLen
    obtain ⟨level, rfl⟩ := List.length_eq_one_iff.mp hrecLen
    have hctorLen := typing.ctorHead.const_left_levelsLength
      (ci := InductiveFixtures.natType.ctors[0].toVConstant) d1NatZeroEnvLookup
    change ctorLs.length = 0 at hctorLen
    have hctorLs : ctorLs = [] := List.length_eq_zero_iff.mp hctorLen
    subst ctorLs
    obtain ⟨hrecArgsLen, hctorArgs, hcaptures⟩ :=
      d1ZeroCaptureValues univs matched
    rw [hctorArgs] at typing matched redexSelf ⊢
    have hrecArgs : ∃ x y z, recArgs = [x, y, z] :=
      ⟨recArgs[0], recArgs[1], recArgs[2],
        List.eq_getElem_of_length_eq_three recArgs hrecArgsLen⟩
    obtain ⟨minorSucc, minorZero, motive, rfl⟩ := hrecArgs
    have hrecCanonical : IsDefEq Gamma
        (.const ``Nat.rec [level]) (.const ``Nat.rec [level])
        (SExpr.mkInst [level]
          (VInductDecl.recConst 0 ``Nat 0 InductiveFixtures.natType).type) :=
      .const d1NatRecEnvLookup rfl
    rw [probeNatRecTypeV_eq] at hrecCanonical
    have hheadEq := d1TypeUniq univs hGamma hrecCanonical typing.recHead
    let motiveView := d1SpineConsView univs hGamma hheadEq typing.recSpine
    have hmotive := motiveView.argumentExpected univs
    have hrestMotive := motiveView.restEq univs
    let zeroView := d1SpineConsView univs hGamma hrestMotive motiveView.tail
    have hzero := zeroView.argumentExpected univs
    have hrestZero := zeroView.restEq univs
    let succView := d1SpineConsView univs hGamma hrestZero zeroView.tail
    have hsucc := succView.argumentExpected univs
    have hrestSucc := succView.restEq univs
    let majorView := d1SpineConsView univs hGamma hrestSucc succView.tail
    have hmajor := majorView.argumentExpected univs
    have hprefixMotive := IsDefEq.appDF hrecCanonical hmotive
    have hprefixZero := IsDefEq.appDF hprefixMotive hzero
    have hprefixSucc := IsDefEq.appDF hprefixZero hsucc
    obtain ⟨_, hmajorType⟩ := d1TypeUniq univs hGamma
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
    obtain ⟨_, hruleMajor⟩ := d1TypeUniq univs hGamma
      hctorAtRuleResult hredexAtGenerated.hasType.2
    obtain ⟨_, hmajorA⟩ := d1TypeUniq univs hGamma
      hredexAtGenerated.hasType.2 redexSelf'
    have hruleA := d1TypesTrans univs hGamma
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
    have hcoreExplicit : SpineWF Gamma (d1ProbeNatZeroRuleType univs level)
        [motive, minorZero, minorSucc]
        (((((SExpr.bvar 2).app (SExpr.const ``Nat.zero [])).subst
          (Subst.one motive).lift.lift).subst
          (Subst.one minorZero).lift).inst minorSucc) := by
      exact .cons hmotive' (.cons hzeroForTelescope
        (.cons hsuccForTelescope .nil))
    have hplainExplicit : SpineWF Gamma (d1ProbeNatZeroRuleType univs level)
        [motive, minorZero, minorSucc] A :=
      .ret hcoreExplicit hruleAForTelescope
    have hplain : SpineWF Gamma
        (SExpr.mkInst [level]
          (NatGeneration.rule 0 NatGeneration.flatCtors[0]).type)
        [motive, minorZero, minorSucc] A := by
      rw [d1ProbeNatZeroRuleTypeS_eq]
      exact hplainExplicit
    have hplainPaths : SpineWF Gamma
        (SExpr.mkInst [level]
          (NatGeneration.rule 0 NatGeneration.flatCtors[0]).type)
        ((natCapturePaths NatGeneration.flatCtors[0]).map mcap) A := by
      exact hcaptures.symm ▸ hplain
    have captureSpine := d1PathSpineOfSpineWF univs hGamma
      captureTyping.typed hplainPaths
    let vls : List VLevel := [level.reify]
    have hvls : ∀ l ∈ vls, l.WF univs := by
      intro l hl
      simp only [vls, List.mem_singleton] at hl
      subst l
      exact SLevel.reify_wf level
    have hlhs :=
      (d1Env_ordered.defEqWF ruleRegistered).1.instL hvls
    have hlhsGamma : d1Env.HasType univs (Gamma.map SExpr.reify)
        (probeNatZeroRuleLhsV.instL vls)
        ((NatGeneration.rule 0 NatGeneration.flatCtors[0]).type.instL vls) := by
      rw [← probeNatZeroRuleLhsV_eq]
      exact hlhs.weak0 d1Env_ordered
    unfold probeNatZeroRuleLhsV at hlhsGamma
    rw [VExpr.instL_lamN] at hlhsGamma
    obtain ⟨hTel, bodyType, hbody⟩ :=
      VEnv.HasType.lamN_wf d1Env_ordered hGamma hlhsGamma
    have hmotiveV := hmotive'.reify hGamma
    change d1Env.IsDefEq univs (Gamma.map SExpr.reify)
      motive.reify motive.reify _ at hmotiveV
    have hzeroV := hzeroForTelescope.reify hGamma
    change d1Env.IsDefEq univs (Gamma.map SExpr.reify)
      minorZero.reify minorZero.reify _ at hzeroV
    have hsuccV := hsuccForTelescope.reify hGamma
    change d1Env.IsDefEq univs (Gamma.map SExpr.reify)
      minorSucc.reify minorSucc.reify _ at hsuccV
    have hcoreV : d1Env.SpineWF univs (Gamma.map SExpr.reify)
        (VExpr.forallN (probeNatRuleBindersV.map (VExpr.instL vls))
          (probeNatZeroRuleResultV.instL vls))
        [motive.reify, minorZero.reify, minorSucc.reify]
        (VExpr.instRev (probeNatZeroRuleResultV.instL vls)
          [motive.reify, minorZero.reify, minorSucc.reify]) := by
      refine .cons hmotiveV ?_
      refine .cons ?_ ?_
      · simpa [d1Params, vls, VExpr.instL, SExpr.reify,
          SExpr.reify_subst,
          VExpr.inst_eq, probeReifySubstOne] using
          hzeroV
      refine .cons ?_ .nil
      simpa [d1Params, vls, VExpr.instL, SExpr.reify,
        SExpr.reify_subst,
        SExpr.reify_inst, VExpr.inst_eq, VExpr.instN_eq,
        VExpr.Subst.liftN,
        probeReifySubstOne, probeReifySubstLift] using
        hsuccV
    have hspineV := hcoreV
    have hspineBody := VEnv.SpineWF.retarget hspineV
      (by simp [probeNatRuleBindersV])
      bodyType
    have hcollapseV := VEnv.IsDefEq.appN_lamN d1Env_ordered
      hTel hbody hspineBody (by simp [probeNatRuleBindersV])
    have hlevels :=
      (VEnv.CtxStrong.strong d1Env_ordered hGamma).levelWF
    have hcollapseS := SExpr.IsDefEq.mkS (d1StructureEtaSound univs)
      hcollapseV hlevels
    have hctx : (Gamma.map SExpr.reify).map SExpr.mk = Gamma := by
      rw [List.map_map]
      exact List.map_id''' Gamma fun term _ => SExpr.mk_reify term
    rw [hctx] at hcollapseS
    have hmkInst (e : VExpr) :
        SExpr.mk (e.instL vls) = SExpr.mkInst [level] e := by
      unfold vls
      exact @SExpr.mk_instL_map_reify (d1Params univs) e [level]
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
    obtain ⟨_, hcollapseType⟩ := d1TypeUniq univs hGamma
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
      d1NatRecEnvLookup
    change recLs.length = 1 at hrecLen
    obtain ⟨level, rfl⟩ := List.length_eq_one_iff.mp hrecLen
    have hctorLen := typing.ctorHead.const_left_levelsLength
      d1NatSuccEnvLookup
    change ctorLs.length = 0 at hctorLen
    have hctorLs : ctorLs = [] := List.length_eq_zero_iff.mp hctorLen
    subst ctorLs
    obtain ⟨hrecArgsLen, hctorArgsLen, hcaptures⟩ :=
      d1SuccCaptureValues univs matched
    obtain ⟨pred, rfl⟩ := List.length_eq_one_iff.mp hctorArgsLen
    have hrecArgs : ∃ x y z, recArgs = [x, y, z] :=
      ⟨recArgs[0], recArgs[1], recArgs[2],
        List.eq_getElem_of_length_eq_three recArgs hrecArgsLen⟩
    obtain ⟨minorSucc, minorZero, motive, rfl⟩ := hrecArgs
    have hrecCanonical : IsDefEq Gamma
        (.const ``Nat.rec [level]) (.const ``Nat.rec [level])
        (SExpr.mkInst [level]
          (VInductDecl.recConst 0 ``Nat 0 InductiveFixtures.natType).type) :=
      .const d1NatRecEnvLookup rfl
    rw [probeNatRecTypeV_eq] at hrecCanonical
    have hheadEq := d1TypeUniq univs hGamma hrecCanonical typing.recHead
    let motiveView := d1SpineConsView univs hGamma hheadEq typing.recSpine
    have hmotive := motiveView.argumentExpected univs
    have hrestMotive := motiveView.restEq univs
    let zeroView := d1SpineConsView univs hGamma hrestMotive motiveView.tail
    have hzero := zeroView.argumentExpected univs
    have hrestZero := zeroView.restEq univs
    let succView := d1SpineConsView univs hGamma hrestZero zeroView.tail
    have hsucc := succView.argumentExpected univs
    have hrestSucc := succView.restEq univs
    let majorView := d1SpineConsView univs hGamma hrestSucc succView.tail
    have hmajor := majorView.argumentExpected univs
    have hctorCanonical : IsDefEq Gamma
        (.const ``Nat.succ []) (.const ``Nat.succ [])
        (SExpr.mkInst [] InductiveFixtures.natType.ctors[1].type) :=
      .const d1NatSuccEnvLookup rfl
    rw [probeNatSuccCtorTypeV_eq] at hctorCanonical
    have hctorCanonical' : IsDefEq Gamma
        (.const ``Nat.succ []) (.const ``Nat.succ [])
        (.forallE (.const ``Nat []) (.const ``Nat [])) := by
      simpa [SExpr.mkInst] using hctorCanonical
    have hctorType := d1TypeUniq univs hGamma
      hctorCanonical' typing.ctorHead
    let predView := d1SpineConsView univs hGamma hctorType typing.ctorSpine
    have hpred := predView.argumentExpected univs
    have hpred' : IsDefEq Gamma pred pred (.const ``Nat []) := by
      simpa using hpred
    have hprefixMotive := IsDefEq.appDF hrecCanonical hmotive
    have hprefixZero := IsDefEq.appDF hprefixMotive hzero
    have hprefixSucc := IsDefEq.appDF hprefixZero hsucc
    obtain ⟨_, hmajorType⟩ := d1TypeUniq univs hGamma
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
    obtain ⟨_, hruleMajor⟩ := d1TypeUniq univs hGamma
      hctorAtRuleResult hredexAtGenerated.hasType.2
    obtain ⟨_, hmajorA⟩ := d1TypeUniq univs hGamma
      hredexAtGenerated.hasType.2 redexSelf'
    have hruleA := d1TypesTrans univs hGamma
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
    have hcoreExplicit : SpineWF Gamma (d1ProbeNatSuccRuleType univs level)
        [motive, minorZero, minorSucc, pred]
        ((((((SExpr.bvar 3).app
          ((SExpr.const ``Nat.succ []).app (SExpr.bvar 0))).subst
            (Subst.one motive).lift.lift.lift).subst
            (Subst.one minorZero).lift.lift).subst
            (Subst.one minorSucc).lift).inst pred) := by
      exact .cons hmotive' (.cons hzeroForTelescope
        (.cons hsuccForTelescope (.cons hpred' .nil)))
    have hplainExplicit : SpineWF Gamma (d1ProbeNatSuccRuleType univs level)
        [motive, minorZero, minorSucc, pred] A :=
      .ret hcoreExplicit hruleAForTelescope
    have hplain : SpineWF Gamma
        (SExpr.mkInst [level]
          (NatGeneration.rule 1 NatGeneration.flatCtors[1]).type)
        [motive, minorZero, minorSucc, pred] A := by
      rw [d1ProbeNatSuccRuleTypeS_eq]
      exact hplainExplicit
    have hplainPaths : SpineWF Gamma
        (SExpr.mkInst [level]
          (NatGeneration.rule 1 NatGeneration.flatCtors[1]).type)
        ((natCapturePaths NatGeneration.flatCtors[1]).map mcap) A := by
      exact hcaptures.symm ▸ hplain
    have captureSpine := d1PathSpineOfSpineWF univs hGamma
      captureTyping.typed hplainPaths
    let vls : List VLevel := [level.reify]
    have hvls : ∀ l ∈ vls, l.WF univs := by
      intro l hl
      simp only [vls, List.mem_singleton] at hl
      subst l
      exact SLevel.reify_wf level
    have hlhs :=
      (d1Env_ordered.defEqWF ruleRegistered).1.instL hvls
    have hlhsGamma : d1Env.HasType univs (Gamma.map SExpr.reify)
        (probeNatSuccRuleLhsV.instL vls)
        ((NatGeneration.rule 1 NatGeneration.flatCtors[1]).type.instL vls) := by
      rw [← probeNatSuccRuleLhsV_eq]
      exact hlhs.weak0 d1Env_ordered
    unfold probeNatSuccRuleLhsV at hlhsGamma
    rw [VExpr.instL_lamN] at hlhsGamma
    obtain ⟨hTel, bodyType, hbody⟩ :=
      VEnv.HasType.lamN_wf d1Env_ordered hGamma hlhsGamma
    have hmotiveV := hmotive'.reify hGamma
    change d1Env.IsDefEq univs (Gamma.map SExpr.reify)
      motive.reify motive.reify _ at hmotiveV
    have hzeroV := hzeroForTelescope.reify hGamma
    change d1Env.IsDefEq univs (Gamma.map SExpr.reify)
      minorZero.reify minorZero.reify _ at hzeroV
    have hsuccV := hsuccForTelescope.reify hGamma
    change d1Env.IsDefEq univs (Gamma.map SExpr.reify)
      minorSucc.reify minorSucc.reify _ at hsuccV
    have hpredV := hpred'.reify hGamma
    change d1Env.IsDefEq univs (Gamma.map SExpr.reify)
      pred.reify pred.reify _ at hpredV
    have hcoreV : d1Env.SpineWF univs (Gamma.map SExpr.reify)
        (VExpr.forallN
          (probeNatSuccRuleBindersV.map (VExpr.instL vls))
          (probeNatSuccRuleResultV.instL vls))
        [motive.reify, minorZero.reify, minorSucc.reify, pred.reify]
        (VExpr.instRev (probeNatSuccRuleResultV.instL vls)
          [motive.reify, minorZero.reify, minorSucc.reify, pred.reify]) := by
      refine .cons hmotiveV ?_
      refine .cons ?_ ?_
      · simpa [d1Params, vls, VExpr.instL, SExpr.reify,
          SExpr.reify_subst, VExpr.inst_eq, probeReifySubstOne] using hzeroV
      refine .cons ?_ ?_
      · simpa [d1Params, vls, VExpr.instL, SExpr.reify,
          SExpr.reify_subst, SExpr.reify_inst, VExpr.inst_eq,
          VExpr.instN_eq, VExpr.Subst.liftN, probeReifySubstOne,
          probeReifySubstLift] using hsuccV
      refine .cons ?_ .nil
      simpa [d1Params, vls, VExpr.instL, VExpr.inst, SExpr.reify] using hpredV
    have hspineBody := VEnv.SpineWF.retarget hcoreV
      (by simp [probeNatSuccRuleBindersV, probeNatRuleBindersV]) bodyType
    have hcollapseV := VEnv.IsDefEq.appN_lamN d1Env_ordered
      hTel hbody hspineBody
      (by simp [probeNatSuccRuleBindersV, probeNatRuleBindersV])
    have hlevels :=
      (VEnv.CtxStrong.strong d1Env_ordered hGamma).levelWF
    have hcollapseS := SExpr.IsDefEq.mkS (d1StructureEtaSound univs)
      hcollapseV hlevels
    have hctx : (Gamma.map SExpr.reify).map SExpr.mk = Gamma := by
      rw [List.map_map]
      exact List.map_id''' Gamma fun term _ => SExpr.mk_reify term
    rw [hctx] at hcollapseS
    have hmkInst (e : VExpr) :
        SExpr.mk (e.instL vls) = SExpr.mkInst [level] e := by
      unfold vls
      exact @SExpr.mk_instL_map_reify (d1Params univs) e [level]
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
    obtain ⟨_, hcollapseType⟩ := d1TypeUniq univs hGamma
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

noncomputable def d1IotaSite (univs : Nat)
    {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {Gamma : List (@SExpr (d1Params univs))}
    {A majorTerm : @SExpr (d1Params univs)}
    {recLs ctorLs : List (@SLevel (d1Params univs))}
    {recArgs ctorArgs : List (@SExpr (d1Params univs))}
    {mcap : (RecursorIotaPattern rec major ctor arity).Path →
      @SExpr (d1Params univs)}
    (rule : @Pattern.IotaRule (d1Params univs) rec major ctor arity r)
    (captureType : (RecursorIotaPattern rec major ctor arity).Path →
      @SExpr (d1Params univs))
    (captureTyping : @Pattern.CaptureTyping (d1Params univs) Gamma
      (RecursorIotaPattern rec major ctor arity) mcap captureType)
    (hGamma : D1ContextValid univs Gamma)
    (typing : @Pattern.IotaTyping (d1Params univs) Gamma rec ctor recLs ctorLs
      recArgs ctorArgs majorTerm A)
    (matched : @Pattern.MatchesS (d1Params univs)
      (RecursorIotaPattern rec major ctor arity)
      (@SExpr.app (d1Params univs)
        (recArgs.foldr (fun a f => @SExpr.app (d1Params univs) f a)
          (@SExpr.const (d1Params univs) rec recLs))
        (ctorArgs.foldr (fun a f => @SExpr.app (d1Params univs) f a)
          (@SExpr.const (d1Params univs) ctor ctorLs))) recLs mcap)
    (redexSelf : @IsDefEq (d1Params univs) Gamma
      (@SExpr.app (d1Params univs)
        (recArgs.foldr (fun a f => @SExpr.app (d1Params univs) f a)
          (@SExpr.const (d1Params univs) rec recLs))
        (ctorArgs.foldr (fun a f => @SExpr.app (d1Params univs) f a)
          (@SExpr.const (d1Params univs) ctor ctorLs)))
      (@SExpr.app (d1Params univs)
        (recArgs.foldr (fun a f => @SExpr.app (d1Params univs) f a)
          (@SExpr.const (d1Params univs) rec recLs))
        (ctorArgs.foldr (fun a f => @SExpr.app (d1Params univs) f a)
          (@SExpr.const (d1Params univs) ctor ctorLs))) A)
    (AType : ∃ u, @IsDefEq (d1Params univs) Gamma A A
      (@SExpr.sort (d1Params univs) u)) :
    @Pattern.IotaReductionSite (d1Params univs) Gamma rec major ctor
      arity r rule recLs ctorLs recArgs ctorArgs majorTerm A mcap captureType
      captureTyping :=
  Classical.choice (d1IotaSite_nonempty univs rule captureType captureTyping
    hGamma typing matched redexSelf AType)

/-- The complete D1 bridge: generated Nat iota, the inherited `d0def`
unfolding, and the checked mutual definition block, all against the extended
environment. -/
noncomputable def d1Semantic (univs : Nat) :
    letI : Params := d1Params univs
    Params.Semantic := by
  letI : Params := d1Params univs
  exact {
  structureEta := by
    intro rule levels Gamma params major hreg
    exact (d1Env_no_structEta rule hreg).elim
  ctor := by
    intro c ci ls Gamma hci hlen cl
    exact d1Ctor univs hci hlen cl
  defn := by
    intro c r hpat
    exact d1Defn univs hpat
  iotaRule := by
    intro rec major ctor arity r hpat
    exact d1IotaRule univs hpat
  iotaSite := by
    intro rec major ctor arity r Gamma A majorTerm recLs ctorLs
      recArgs ctorArgs mcap rule captureType captureTyping hGamma typing
      matched redexSelf AType
    exact d1IotaSite univs rule captureType captureTyping hGamma typing
      matched redexSelf AType
  registered := by
    intro df ls Gamma hreg hlen hLhs hRhs
    exact d1Registered univs hreg hlen hLhs hRhs }

/-! ## Concrete δ-rank certificate

The mutual block is ranked by dependency, not declaration order:
`d1mutA` unfolds to `d1mutB`, and `d1mutB` unfolds through `d0def`.
Thus their ranks are respectively three, two, and one. -/

def d1DeltaRankFn : Name → Nat := fun n =>
  if n = ``ParamsD1.d1mutA then 3
  else if n = ``ParamsD1.d1mutB then 2
  else if n = ``ParamsD0.d0def then 1
  else 0

theorem d1NatTypeLookup :
    d1Env.constants ``Nat = some InductiveFixtures.natType.toVConstant :=
  d0Env_le_d1Env.constants d0NatTypeLookup

theorem d1D0DefLookup :
    d1Env.constants ``ParamsD0.d0def = some d0DefVal.toVConstant :=
  d0Env_le_d1Env.constants d0Env_d0Def_lookup

theorem d1DeltaRankFn_nat : d1DeltaRankFn ``Nat ≤ 0 := by decide

theorem d1DeltaRankFn_natZero : d1DeltaRankFn ``Nat.zero ≤ 0 := by
  decide

theorem d1DeltaRankFn_natSucc : d1DeltaRankFn ``Nat.succ ≤ 0 := by
  decide

theorem d1DeltaRankFn_d0def :
    d1DeltaRankFn ``ParamsD0.d0def ≤ 1 := by
  decide

theorem d1DeltaRankFn_d1mutB :
    d1DeltaRankFn ``ParamsD1.d1mutB ≤ 2 := by
  decide

/-- `Nat : Type` in D1 at rank zero. -/
theorem d1NatCertR (univs : Nat) :
    letI : Params := d1Params univs
    ∀ (Gamma : List SExpr) (n : Nat),
      HasTypeStratifiedR d1DeltaRankFn Gamma
        (.const ``Nat []) (.sort (.instV [] (.succ .zero))) true (n + 1) 0 := by
  letI : Params := d1Params univs
  intro Gamma n
  exact .base (.const d1NatTypeLookup rfl d1DeltaRankFn_nat
    (.base .sort'))

/-- `Nat → Nat : Type` in D1 at rank zero. -/
theorem d1NatPiCertR (univs : Nat) :
    letI : Params := d1Params univs
    ∀ (Gamma : List SExpr) (n : Nat),
      HasTypeStratifiedR d1DeltaRankFn Gamma
        (.forallE (.const ``Nat []) (.const ``Nat []))
        (.sort (.imax (.instV [] (.succ .zero))
          (.instV [] (.succ .zero)))) true (n + 2) 0 := by
  letI : Params := d1Params univs
  intro Gamma n
  exact .base (.forallE (d1NatCertR univs Gamma n)
    (d1NatCertR univs (_ :: Gamma) n))

/-- `Nat.succ : Nat → Nat` in D1 at rank zero. -/
theorem d1SuccCertR (univs : Nat) :
    letI : Params := d1Params univs
    ∀ (Gamma : List SExpr) (n : Nat),
      HasTypeStratifiedR d1DeltaRankFn Gamma
        (.const ``Nat.succ [])
        (.forallE (.const ``Nat []) (.const ``Nat [])) true (n + 3) 0 := by
  letI : Params := d1Params univs
  intro Gamma n
  exact .base (.const d1NatSuccEnvLookup rfl d1DeltaRankFn_natSucc
    (d1NatPiCertR univs Gamma n))

/-- `Nat.zero : Nat` in D1 at rank zero. -/
theorem d1ZeroCertR (univs : Nat) :
    letI : Params := d1Params univs
    ∀ (Gamma : List SExpr),
      HasTypeStratifiedR d1DeltaRankFn Gamma
        (.const ``Nat.zero []) (.const ``Nat []) true 2 0 := by
  letI : Params := d1Params univs
  intro Gamma
  exact .base (.const d1NatZeroEnvLookup rfl d1DeltaRankFn_natZero
    (d1NatCertR univs Gamma 0))

/-- `d0def : Nat` as a used constant, at rank one. -/
theorem d1D0DefConstCertR (univs : Nat) :
    letI : Params := d1Params univs
    ∀ (Gamma : List SExpr) (n : Nat),
      HasTypeStratifiedR d1DeltaRankFn Gamma
        (.const ``ParamsD0.d0def []) (.const ``Nat []) true (n + 2) 1 := by
  letI : Params := d1Params univs
  intro Gamma n
  exact .base (.const d1D0DefLookup rfl d1DeltaRankFn_d0def
    ((d1NatCertR univs Gamma n).mono_rank (Nat.zero_le 1)))

/-- `Nat.succ d0def : Nat` at rank one, the body certificate for
`d1mutB`. -/
theorem d1MutBValueCertR (univs : Nat) :
    letI : Params := d1Params univs
    ∀ (Gamma : List SExpr),
      HasTypeStratifiedR d1DeltaRankFn Gamma
        (.app (.const ``Nat.succ []) (.const ``ParamsD0.d0def []))
        (.const ``Nat []) true 4 1 := by
  letI : Params := d1Params univs
  intro Gamma
  refine .base (.app (u := .instV [] (.succ .zero))
    (v := .instV [] (.succ .zero))
    ((d1NatCertR univs Gamma 2).mono_rank (Nat.zero_le 1))
    ((d1NatCertR univs (_ :: Gamma) 2).mono_rank (Nat.zero_le 1))
    ((d1SuccCertR univs Gamma 0).mono_rank (Nat.zero_le 1))
    (d1D0DefConstCertR univs Gamma 1)
    ((d1NatCertR univs Gamma 2).mono_rank (Nat.zero_le 1)))

/-- `d1mutB : Nat` as a used constant, at rank two, the body certificate
for `d1mutA`. -/
theorem d1MutBConstCertR (univs : Nat) :
    letI : Params := d1Params univs
    ∀ (Gamma : List SExpr),
      HasTypeStratifiedR d1DeltaRankFn Gamma
        (.const ``ParamsD1.d1mutB []) (.const ``Nat []) true 2 2 := by
  letI : Params := d1Params univs
  intro Gamma
  exact .base (.const d1Env_d1MutB_lookup rfl d1DeltaRankFn_d1mutB
    ((d1NatCertR univs Gamma 0).mono_rank (Nat.zero_le 2)))

/-- The D1 fixture's checked δ-rank certificate. -/
def d1DeltaRank (univs : Nat) :
    letI : Params := d1Params univs
    Params.DeltaRank := by
  letI : Params := d1Params univs
  refine ⟨d1DeltaRankFn, ?_⟩
  intro c ci value closed ls Gamma hpat hreg hlen
  change D1Pat _ _ at hpat
  cases hpat with
  | old h0 =>
    cases h0 with
    | iota h => exact (natPat_no_const univs h).elim
    | defn =>
      obtain rfl := Option.some.inj (d1D0DefLookup.symm.trans hreg)
      obtain rfl := List.length_eq_zero_iff.mp hlen
      exact ⟨2, 0, by decide, d1ZeroCertR univs Gamma⟩
  | defnA =>
    obtain rfl := Option.some.inj (d1Env_d1MutA_lookup.symm.trans hreg)
    obtain rfl := List.length_eq_zero_iff.mp hlen
    exact ⟨2, 2, by decide, d1MutBConstCertR univs Gamma⟩
  | defnB =>
    obtain rfl := Option.some.inj (d1Env_d1MutB_lookup.symm.trans hreg)
    obtain rfl := List.length_eq_zero_iff.mp hlen
    exact ⟨4, 1, by decide, d1MutBValueCertR univs Gamma⟩

/-- Mutual zero-arity definitions preserve the classified fragment.  Their
strict delta chain is certified by `d1DeltaRank`; all iota provenance is
transported from D0. -/
theorem d1Classified (univs : Nat)
    [semantic : @Params.Semantic (d1Params univs)] :
    letI : Params := d1Params univs
    letI : Params.DeltaRank := d1DeltaRank univs
    Params.Classified := by
  letI : Params := d1Params univs
  letI : Params.Semantic := semantic
  letI : Params.DeltaRank := d1DeltaRank univs
  exact {
    iotaDescent := d1IotaStructuralDescent univs
    argumentNonProp := Params.patternArgumentNonProp }

/-- End-to-end D1 endpoint: the mutual-definition-extended environment
supplies every semantic certificate required by the experimental
sort-injectivity bridge.  Conditional on the two L4L-16C′w leaf inputs at
the fixture instance. -/
theorem d1SortInvS (univs : Nat) {Gamma : List VExpr} {u v : VLevel}
    (piInv : @LRS.PiPathInv (d1Params univs))
    (linkRect : ∀ Γ, @LR.MajorLinkRect (d1Params univs) Γ)
    (hGamma : OnCtx Gamma (d1Env.IsType univs))
    (h : d1Env.IsDefEqU univs Gamma (.sort u) (.sort v)) : u ≈ v := by
  letI : Params := d1Params univs
  letI : Params.Semantic := d1Semantic univs
  exact VEnv.IsDefEqU.sort_invS piInv linkRect hGamma h

/--
info: 'Lean4Lean.SExpr.ParamsD1.d1SortInvS' depends on axioms: [propext,
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
 natRule_rhs_ne_d1MutB._native.native_decide.ax_1_3]
-/
#guard_msgs in
#print axioms d1SortInvS

end SemanticCertificates

/-! ## Quotient half of the D1 plan line: environment layer and the
interface obstruction

The consolidated D work package in `plans/roadmap.md` assigns
`CertifiedExtension.quot` to D1.
The environment-layer content is deliverable and is checked below: the D1
environment extends by the `Eq` axiom and the checked `.quot` history step
(`VDecl.WF.quot`), producing a WF/Ordered environment that registers
`quotDefEq`.

The *semantic* half is not instantiable under the current interface, for
three independent reasons, in escalating strength:

1. `Params.pat_wf` forces `classify ``Quot.mk = some (.ctor 3)` whenever
   the quot pattern is in `Pat` (`quotPattern_forces_ctor_classification`
   below is the kernel-checked forcing step).  Then `CtorBundle.IsCtor
   ``Quot.mk` holds, and `Params.Semantic.ctor` must produce a
   `CtorBundle` at *every* `ls` with `ls.length = 1` — including
   `ls = [.zero]`, where `mkInst ls quotMkConst.type` is a `Prop`
   (its sort evaluates to `imax 1 (imax 1 0) = 0`), so the bundle's
   equality at `.sort F.u` forces `F.u = .zero` against `CtorBundle.hu0`.
   This is exactly the Prop-instantiable-constructor boundary recorded in
   `plans/roadmap.md`; the non-Prop staging slice (Nat, List, tree blocks)
   excludes such constructors until the explicit Prop-pattern policy lands.
2. Keeping the pattern out of `Pat` but `quotDefEq` in `env.defeqs`
   instead breaks `Params.Semantic.registered`: the required strong
   equality between the two six-binder towers has a stuck
   `Quot.lift … (Quot.mk …)` head, and without a `Pat` member neither
   `.extra` (needs a `Pattern.Action`, hence a member) nor `defn`
   (constant patterns only) can derive it.
3. Even with 1 repaired, `Params.Semantic.iotaSite` for the quot rule
   must discharge `quotCheck`'s two obligations (`α' ≡ α`, `r' ≡ r`)
   from its typing inputs alone; that needs injectivity of the stuck
   application `@Quot α r ≡ @Quot α' r'`, a Church–Rosser-strength
   inversion the current system defers to L4L-18A′.

Repair options are an interface decision owned by the 16C′ writer (e.g. a
typing-conditional `hu0`, or restricting `Semantic.ctor`'s level
quantification to well-sorted instantiations); none is taken here.  The D1
deliverable for the quotient is therefore the environment layer plus this
record. -/

section QuotObstruction

open VInductDecl

/-- Any classifier making the quot pattern well-formed marks `Quot.mk` as a
three-argument constructor head.  This is the forcing step of obstruction 1:
pattern membership alone commits the semantic instance to constructor
bundles for `Quot.mk` at every universe instantiation. -/
theorem quotPattern_forces_ctor_classification
    (cl : Name → Option Classification)
    (H : (CertifiedExtension.quotPattern.toPattern).WF cl) :
    cl ``Quot.mk = some (.ctor 3) := by
  have h := H
  simp only [CertifiedExtension.quotPattern, SimplePattern.toPattern,
    RecursorIotaPattern, Pattern.varN, Pattern.WF] at h
  exact h.2

/-- The `Eq` head declared as an axiom over the D1 environment. -/
def d1qEqVal : VConstVal := ⟨eqConst, ``Eq⟩

theorem d1qEq_fresh : d1Env.constants ``Eq = none := by native_decide

local instance : Inhabited VEnv := ⟨VEnv.empty⟩

def d1qEqEnv := (d1Env.addConst ``Eq eqConst).get!

theorem d1Env_add_eq : d1Env.addConst ``Eq eqConst = some d1qEqEnv := by
  simp [VEnv.addConst, d1qEq_fresh, d1qEqEnv]

theorem d1qEqEnv_quotReady : d1qEqEnv.QuotReady :=
  VEnv.addConst_self d1Env_add_eq

theorem d1qEqVal_wf : d1qEqVal.toVConstant.WF d1Env := by
  have hp : VLevel.WF 1 (.param 0) := Nat.one_pos
  have hz : VLevel.WF 1 .zero := trivial
  have hα : _root_.Lean4Lean.Lookup [VExpr.sort (.param 0)] 0
      (.sort (.param 0)) := .zero
  have hx : _root_.Lean4Lean.Lookup [VExpr.bvar 0, VExpr.sort (.param 0)] 1
      (.sort (.param 0)) := .succ .zero
  exact ⟨_, VEnv.HasType.forallE (VEnv.HasType.sort hp)
    (VEnv.HasType.forallE (VEnv.HasType.bvar hα)
      (VEnv.HasType.forallE (VEnv.HasType.bvar hx)
        (VEnv.HasType.sort hz)))⟩

theorem d1qEq_step : VDecl.WF d1Env (.axiom d1qEqVal) d1qEqEnv :=
  .axiom d1qEqVal_wf d1Env_add_eq

def d1qQuotEnv1 := (d1qEqEnv.addConst ``Quot quotConst).get!
def d1qQuotEnv2 := (d1qQuotEnv1.addConst ``Quot.mk quotMkConst).get!
def d1qQuotEnv3 := (d1qQuotEnv2.addConst ``Quot.lift quotLiftConst).get!
def d1qQuotEnv4 := (d1qQuotEnv3.addConst ``Quot.ind quotIndConst).get!

/-- The complete quotient-extended environment. -/
def d1qEnv := d1qQuotEnv4.addDefEq quotDefEq

theorem d1qQuot_fresh : d1qEqEnv.constants ``Quot = none := by
  native_decide

theorem d1qQuotMk_fresh : d1qQuotEnv1.constants ``Quot.mk = none := by
  native_decide

theorem d1qQuotLift_fresh : d1qQuotEnv2.constants ``Quot.lift = none := by
  native_decide

theorem d1qQuotInd_fresh : d1qQuotEnv3.constants ``Quot.ind = none := by
  native_decide

theorem d1qEqEnv_add1 :
    d1qEqEnv.addConst ``Quot quotConst = some d1qQuotEnv1 := by
  simp [VEnv.addConst, d1qQuot_fresh, d1qQuotEnv1]

theorem d1qQuotEnv1_add2 :
    d1qQuotEnv1.addConst ``Quot.mk quotMkConst = some d1qQuotEnv2 := by
  simp [VEnv.addConst, d1qQuotMk_fresh, d1qQuotEnv2]

theorem d1qQuotEnv2_add3 :
    d1qQuotEnv2.addConst ``Quot.lift quotLiftConst = some d1qQuotEnv3 := by
  simp [VEnv.addConst, d1qQuotLift_fresh, d1qQuotEnv3]

theorem d1qQuotEnv3_add4 :
    d1qQuotEnv3.addConst ``Quot.ind quotIndConst = some d1qQuotEnv4 := by
  simp [VEnv.addConst, d1qQuotInd_fresh, d1qQuotEnv4]

theorem d1qEqEnv_addQuot : d1qEqEnv.addQuot = some d1qEnv := by
  simp [VEnv.addQuot, d1qEqEnv_add1, d1qQuotEnv1_add2,
    d1qQuotEnv2_add3, d1qQuotEnv3_add4, d1qEnv]

theorem d1qQuot_step : VDecl.WF d1qEqEnv .quot d1qEnv :=
  .quot d1qEqEnv_quotReady d1qEqEnv_addQuot

/-- The quotient-extended environment is well-formed by declaration
history: the D1 history followed by the `Eq` axiom and the checked `.quot`
step. -/
theorem d1qEnv_wf : d1qEnv.WF := by
  obtain ⟨ds, hds⟩ := d1Env_wf
  exact ⟨.quot :: .axiom d1qEqVal :: ds,
    .decl d1qQuot_step (.decl d1qEq_step hds)⟩

theorem d1qEnv_ordered : d1qEnv.Ordered := d1qEnv_wf.ordered

/-- The registered quotient contraction rule, exactly the payload certified
by `CertifiedExtension.quot`. -/
theorem d1qEnv_defeq_quot : d1qEnv.defeqs quotDefEq :=
  VEnv.addQuot_defeq d1qEqEnv_addQuot

/- The quotient environment layer carries no inherited admissions: unlike
the semantic endpoint, its closure is `sorryAx`-free — only the standard
logical axioms, the fixture persistent-map contracts, and named concrete
`native_decide` observations. -/
/--
info: 'Lean4Lean.SExpr.ParamsD1.d1qEnv_wf' depends on axioms: [propext,
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
 d1qEq_fresh._native.native_decide.ax_1_1,
 d1qQuotInd_fresh._native.native_decide.ax_1_1,
 d1qQuotLift_fresh._native.native_decide.ax_1_1,
 d1qQuotMk_fresh._native.native_decide.ax_1_1,
 d1qQuot_fresh._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms d1qEnv_wf

end QuotObstruction

end ParamsD1
end SExpr
end Lean4Lean
