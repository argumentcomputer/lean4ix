import Lean4Lean.Std.SMap
import Lean4Lean.Verify.Environment.Basic

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

theorem TrConstant.sf_mono (hsf : safety ≤ safety')
    (H : TrConstant safety' env ci ci') : TrConstant safety env ci ci' :=
  ⟨safety.le_trans hsf H.1, H.2⟩

theorem TrConstVal.sf_mono (hsf : safety ≤ safety')
    (H : TrConstVal safety' env ci ci') : TrConstVal safety env ci ci' :=
  ⟨H.1.sf_mono hsf, H.2⟩

theorem TrDefVal.sf_mono (hsf : safety ≤ safety')
    (H : TrDefVal safety' env ci ci') : TrDefVal safety env ci ci' :=
  ⟨H.1.sf_mono hsf, H.2⟩

theorem TrEnv'.sf_mono (hsf : safety ≤ safety') :
    TrEnv' safety' C Q env → TrEnv' safety C Q env
  | .empty => .empty
  | .axiom htr hfresh hwf hadd H =>
    .axiom (htr.sf_mono hsf) hfresh hwf hadd (H.sf_mono hsf)
  | .defn htr hfresh hwf hadd H =>
    .defn (htr.sf_mono hsf) hfresh hwf hadd (H.sf_mono hsf)
  | .opaque htr hfresh hwf hadd H =>
    .opaque (htr.sf_mono hsf) hfresh hwf hadd (H.sf_mono hsf)
  | .quot hready hadd H =>
    .quot hready hadd (H.sf_mono hsf)
  | .inductStaging hadd hwf H =>
    .inductStaging hadd hwf (H.sf_mono hsf)
  | .induct hadd H =>
    .induct hadd (H.sf_mono hsf)

theorem TrConstant.mono {env env' : VEnv} (henv : env ≤ env')
    (H : TrConstant safety env ci ci') : TrConstant safety env' ci ci' :=
  ⟨H.1, H.2.1, H.2.2.mono henv⟩

theorem TrConstVal.mono {env env' : VEnv} (henv : env ≤ env')
    (H : TrConstVal safety env ci ci') : TrConstVal safety env' ci ci' :=
  ⟨H.1.mono henv, H.2⟩

theorem TrDefVal.mono {env env' : VEnv} (henv : env ≤ env')
    (H : TrDefVal safety env ci ci') : TrDefVal safety env' ci ci' :=
  ⟨H.1.mono henv, H.2.mono henv⟩

variable (safety : DefinitionSafety) in
inductive Aligned : ConstMap → VEnv → Prop where
  | empty : Aligned {} .empty
  | ignoreConst : Aligned C venv → C.find? n = none → ¬safety ≤ ci.safety →
    ci.name = n → Aligned (C.insert n ci) venv
  | const : Aligned C venv → C.find? n = none → TrConstant safety venv ci ci' →
    venv.addConst n ci' = some venv' → ci.name = n → Aligned (C.insert n ci) venv'
  | defeq : Aligned C venv → Aligned C (venv.addDefEq df)

theorem Aligned.map_wf (H : Aligned safety C venv) : C.WF := by
  induction H with
  | empty => exact .empty
  | ignoreConst _ h1 _ _ ih
  | const _ h1 _ _ _ ih => exact ih.insert _ _ h1
  | defeq _ ih => exact ih

theorem Aligned.find?_iff (H : Aligned safety C venv) :
    (∃ ci, C.find? name = some ci ∧ safety ≤ ci.safety) ↔ ∃ ci, venv.constants name = some ci := by
  induction H with
  | empty => simp [SMap.find?, VEnv.empty]
  | ignoreConst H _ h2 _ ih =>
    simp [H.map_wf.find?_insert]; split <;> [skip; assumption]
    rename_i eq1 eq2; subst eq2; simp [← ih, *]
  | const H h1 h2 eq _ ih =>
    simp [H.map_wf.find?_insert]
    simp [VEnv.addConst] at eq; split at eq <;> cases eq
    split <;> simp_all; exact h2.1
  | defeq _ ih => exact ih

theorem Aligned.addQuot1 {Q : Prop}
    (H1 : ∀ c env, Aligned safety c env → P c env → Q)
    (C env) (wf : Aligned safety C env) (H2 : AddQuot1 n k ci P C env) : Q := by
  let ⟨_, _, _, h1, h2, h3, h4⟩ := H2
  exact H1 _ _ (wf.const h2 (h1.sf_mono DefinitionSafety.le_safe) h3 rfl) h4

nonrec theorem Aligned.addQuot (H : AddQuot C₁ C₂ venv₁ venv₂)
    (wf : Aligned safety C₁ venv₁) : Aligned safety C₂ venv₂ := by
  dsimp [AddQuot] at H
  refine (addQuot1 <| addQuot1 <| addQuot1 <| addQuot1 ?_) _ _ wf H
  rintro _ _ h ⟨rfl, rfl⟩; exact h.defeq

theorem AddInductConstant.map_wf
    (H : AddInductConstant kind C₁ env₁ ci C₂ env₂) (wf : C₁.WF) : C₂.WF := by
  rw [H.map_add]
  exact wf.insert _ _ H.map_fresh

/-- An inductive metadata insertion cannot introduce a declaration body.
Consequently, any value-bearing entry in the result map was already present
in the input map. -/
theorem AddInductConstant.old_of_value
    (H : AddInductConstant kind C₁ env₁ ci' C₂ env₂) (wf : C₁.WF)
    (hout : C₂.find? name = some ci) (hv : ci.value? = some v) :
    C₁.find? name = some ci := by
  rw [H.map_add, wf.find?_insert] at hout
  split at hout
  · cases hout
    have hnone := InductConstantKind.Matches.value?_eq_none H.kind_eq
    simp_all
  · exact hout

theorem AddInductConstants.map_wf :
    AddInductConstants kind C₁ env₁ cis C₂ env₂ → C₁.WF → C₂.WF
  | .nil, wf => wf
  | .cons h hrest, wf => hrest.map_wf (h.map_wf wf)

theorem AddInductConstants.old_of_value :
    (H : AddInductConstants kind C₁ env₁ cis C₂ env₂) → C₁.WF →
    C₂.find? name = some ci → ci.value? = some v → C₁.find? name = some ci
  | .nil, _, hout, _ => hout
  | .cons h hrest, wf, hout, hv =>
    h.old_of_value wf (hrest.old_of_value (h.map_wf wf) hout hv) hv

theorem AddInduct.map_wf (H : AddInduct C₁ env₁ decl C₂ env₂)
    (wf : C₁.WF) : C₂.WF := by
  rcases H with ⟨H⟩
  exact H.addRec.map_wf <| H.addCtors.map_wf <| H.addType.map_wf wf

theorem AddInduct.old_of_value (H : AddInduct C₁ env₁ decl C₂ env₂)
    (wf : C₁.WF) (hout : C₂.find? name = some ci) (hv : ci.value? = some v) :
    C₁.find? name = some ci := by
  rcases H with ⟨H⟩
  have wfType := H.addType.map_wf wf
  have wfCtors := H.addCtors.map_wf wfType
  exact H.addType.old_of_value wf
    (H.addCtors.old_of_value wfType (H.addRec.old_of_value wfCtors hout hv) hv) hv

theorem Aligned.addInductConstant
    (wf : Aligned safety C₁ env₁)
    (H : AddInductConstant kind C₁ env₁ ci C₂ env₂) : Aligned safety C₂ env₂ := by
  rw [H.map_add]
  exact wf.const H.map_fresh (H.tr.1.sf_mono DefinitionSafety.le_safe)
    H.env_add H.tr.2

theorem Aligned.addInductConstants :
    AddInductConstants kind C₁ env₁ cis C₂ env₂ →
      Aligned safety C₁ env₁ → Aligned safety C₂ env₂
  | .nil, wf => wf
  | .cons h hrest, wf =>
    Aligned.addInductConstants hrest (wf.addInductConstant h)

theorem Aligned.addDefEqFold : ∀ (dfs : List VDefEq),
    Aligned safety C env → Aligned safety C (dfs.foldl VEnv.addDefEq env)
  | [], wf => wf
  | _ :: dfs, wf => addDefEqFold dfs wf.defeq

theorem Aligned.addInduct (H : AddInduct C₁ env₁ decl C₂ env₂)
    (wf : Aligned safety C₁ env₁) : Aligned safety C₂ env₂ := by
  rcases H with ⟨H⟩
  rw [← H.addRules.to_add]
  have wfType := wf.addInductConstant H.addType
  have wfCtors := wfType.addInductConstants H.addCtors
  have wfRec := wfCtors.addInductConstant H.addRec
  exact wfRec.addDefEqFold _

/--
info: 'Lean4Lean.Aligned.addInduct' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Aligned.addInduct

theorem TrEnv'.aligned (H : TrEnv' safety C Q venv) : Aligned safety C venv := by
  induction H with
  | empty => exact .empty
  | «axiom» h1 h2 _ h _ ih => exact ih.const h2 h1 h rfl
  | «opaque» h1 h2 _ h _ ih => exact ih.const h2 h1.1.1 h rfl
  | defn h1 h2 _ h _ ih => exact (ih.const h2 h1.1.1 h rfl).defeq
  | quot _ h _ ih => exact ih.addQuot h
  | inductStaging h _ _ ih => exact ih.addInductConstant h
  | induct h _ ih => exact ih.addInduct h

/--
info: 'Lean4Lean.TrEnv'.aligned' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms TrEnv'.aligned

theorem TrEnv'.map_wf (H : TrEnv' safety C Q venv) : C.WF := H.aligned.map_wf

theorem Aligned.find? (H : Aligned safety C venv)
    (h : C.find? name = some ci) (hs : safety ≤ ci.safety) :
    ∃ ci', venv.constants name = some ci' ∧ TrConstant safety venv ci ci' := by
  have mono {env₁ env₂} (H : env₁.LE env₂) :
      (∃ ci', env₁.constants name = some ci' ∧ TrConstant safety env₁ ci ci') →
      (∃ ci', env₂.constants name = some ci' ∧ TrConstant safety env₂ ci ci')
    | ⟨_, h1, h2⟩ => ⟨_, H.constants h1, h2.mono H⟩
  induction H with
  | empty => simp [SMap.find?] at h
  | ignoreConst h1 _ _ _ ih =>
    rw [h1.map_wf.find?_insert] at h; split at h
    · cases h; contradiction
    · exact ih h
  | const h1 _ h2 h3 _ ih =>
    have := VEnv.addConst_le h3
    rw [h1.map_wf.find?_insert] at h; split at h
    · rename_i h'; cases h; simp at h'; subst h'
      simp [VEnv.addConst] at h3; split at h3 <;> cases h3
      simp; rename_i h'; refine h2.mono this
    · let ⟨_, h1, h2⟩ := ih h; exact ⟨_, this.constants h1, h2.mono this⟩
  | defeq h1 ih => let ⟨_, h1, h2⟩ := ih h; exact ⟨_, h1, h2.mono VEnv.addDefEq_le⟩

theorem Aligned.find?_uniq (H : Aligned safety C venv)
    (h : C.find? name = some ci) (hs : venv.constants name = some ci') :
    ci.name = name ∧ TrConstant safety venv ci ci' := by
  induction H with
  | empty => simp [SMap.find?] at h
  | ignoreConst H h2 h3 _ ih =>
    simp [H.map_wf.find?_insert] at h; split at h
    · rename_i n ci _ h'; subst n h'
      simpa [h2, hs] using H.find?_iff (name := ci.name)
    · exact ih h hs
  | const h1 h5 h2 h3 h4 ih =>
    have := VEnv.addConst_le h3
    simp [VEnv.addConst] at h3; split at h3 <;> cases h3
    simp [h1.map_wf.find?_insert] at h hs; revert h hs; split
    · rintro ⟨⟩ ⟨⟩; rename_i n _ _ _; subst n; exact ⟨h4, h2.mono this⟩
    · intro hs h; let ⟨h1, h2⟩ := ih h hs; exact ⟨h1, h2.mono this⟩
  | defeq h1 ih => let ⟨h1, h2⟩ := ih h hs; exact ⟨h1, h2.mono VEnv.addDefEq_le⟩

theorem TrEnv.find?_iff (H : TrEnv safety env venv) :
    (∃ ci, env.find? name = some ci ∧ safety ≤ ci.safety) ↔ ∃ ci, venv.constants name = some ci := by
  conv => enter [1,1,_,1,1]; apply H.map_wf.find?'_eq_find?
  exact H.aligned.find?_iff

-- theorem TrEnv.contains_iff (H : TrEnv safety env venv) :
--     env.contains name ↔ ∃ oci, venv.constants name = some oci := by
--   simp [← H.find?_iff, Kernel.Environment.find?, H.map_wf.find?'_eq_find?,
--     ← Option.isSome_iff_exists, ← SMap.find?_isSome, Kernel.Environment.contains]

theorem TrEnv.find? (H : TrEnv safety env venv)
    (h : env.find? name = some ci) (hs : safety ≤ ci.safety) :
    ∃ ci', venv.constants name = some ci' ∧ TrConstant safety venv ci ci' :=
  H.aligned.find? (H.map_wf.find?'_eq_find? _ ▸ h) hs

theorem TrEnv.find?_uniq (H : TrEnv safety env venv)
    (h : env.find? name = some ci) (hs : venv.constants name = some ci') :
    ci.name = name ∧ TrConstant safety venv ci ci' :=
  H.aligned.find?_uniq (H.map_wf.find?'_eq_find? _ ▸ h) hs

theorem TrEnv'.of_value (H : TrEnv' safety C Q venv) (h : C.find? name = some ci)
    (hs : safety ≤ ci.safety) (hv : ci.value? = some v) :
    TrExpr venv ci.levelParams [] v (.const ci.name (VLevel.params ci.levelParams.length)) := by
  have {C n ci'} (hC : C.WF) :
      (SMap.insert C n ci').find? name = some ci →
      C.find? name = some ci ∨ n = name ∧ ci' = ci := by
    rw [hC.find?_insert]; simp; split <;> simp +contextual [*]
  induction H with
  | empty => simp [SMap.find?] at h
  | «axiom» _ _ _ h1 H ih | «opaque» _ _ _ h1 H ih =>
    obtain h | ⟨rfl, rfl⟩ := this H.map_wf h
    · exact (ih h).mono (VEnv.addConst_le h1)
    · contradiction
  | defn h2 h3 h4 h1 H ih =>
    have' le := (VEnv.addConst_le h1).trans VEnv.addDefEq_le
    obtain h | ⟨rfl, rfl⟩ := this H.map_wf h
    · exact (ih h).mono le
    · cases hv
      have := VEnv.IsDefEq.extra0 VEnv.addDefEq_self <|
        (H.defn h2 h3 h4 h1).wf.ordered.defEqWF VEnv.addDefEq_self
      let ⟨⟨⟨b1, b2, b3⟩, b4⟩, b5⟩ := h2
      refine ⟨_, b5.mono le, b2.symm ▸ b4.symm ▸ ⟨_, this.symm⟩⟩
  | quot _ h1 H ih =>
    suffices ∀ {n k ci' P}, (∀ C env, Aligned safety C env → P C env → C.find? name = some ci) →
        ∀ C env, Aligned safety C env → AddQuot1 n k ci' P C env → C.find? name = some ci by
      refine (ih <| this (this <| this <| this ?_) _ _ H.aligned h1).mono h1.le
      rintro _ _ _ ⟨rfl, rfl⟩; exact h
    rintro n k ci' P ih C env wf ⟨_, h1, _, h2, h3, h4, h5⟩
    have wf' := wf.const h3 ⟨by cases safety <;> rfl, h2.2⟩ h4 rfl
    obtain h | ⟨rfl, rfl⟩ := this wf.map_wf (ih _ _ wf' h5)
    · exact h
    · contradiction
  | inductStaging h1 _ H ih =>
    exact (ih (h1.old_of_value H.map_wf h hv)).mono h1.le
  | induct h1 H ih =>
    exact (ih (h1.old_of_value H.map_wf h hv)).mono h1.le

nonrec theorem TrEnv.of_value (H : TrEnv safety env venv) (h : env.find? name = some ci)
    (hs : safety ≤ ci.safety) (hv : ci.value? = some v) :
    TrExpr venv ci.levelParams [] v (.const ci.name (VLevel.params ci.levelParams.length)) :=
  H.of_value (by rwa [← H.map_wf.find?'_eq_find?]) hs hv
