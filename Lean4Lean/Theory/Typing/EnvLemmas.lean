/-
This file is derived from lean4lean and has been modified by Argument Computer Corporation.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/

import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.Typing.QuotLemmas
import Lean4Lean.Theory.Typing.InductiveLemmas
import Lean4Lean.Theory.Typing.NestedInductiveLemmas

namespace Lean4Lean

theorem VEnv.addConsts_le {env env' : VEnv} : ∀ {cis}, env.addConsts cis = some env' → env ≤ env'
  | [], h => by cases h; exact .rfl
  | _ :: _, h => by
    simp [VEnv.addConsts, Option.bind_eq_some_iff] at h
    obtain ⟨_, h1, h2⟩ := h
    exact (addConst_le h1).trans (addConsts_le h2)

theorem VEnv.addDefEqs_le_theory {env : VEnv} (cis : List VDefVal) :
    env ≤ env.addDefEqs cis := by
  induction cis generalizing env with
  | nil => exact .rfl
  | cons ci cis ih =>
      exact VEnv.addDefEq_le.trans (ih (env := env.addDefEq ci.toDefEq))

theorem VEnv.addConst_structEtas_eq {env env' : VEnv}
    (hadd : env.addConst name ci = some env') :
    env'.structEtas = env.structEtas := by
  unfold VEnv.addConst at hadd
  split at hadd <;> cases hadd
  rfl

theorem VEnv.addConsts_structEtas_eq {env env' : VEnv} :
    ∀ {cis : List VDefVal}, env.addConsts cis = some env' →
      env'.structEtas = env.structEtas
  | [], h => by cases h; rfl
  | _ :: _, h => by
      simp only [VEnv.addConsts, List.foldlM_cons,
        Option.bind_eq_bind] at h
      obtain ⟨middle, hhead, htail⟩ := Option.bind_eq_some_iff.1 h
      exact (VEnv.addConsts_structEtas_eq htail).trans
        (VEnv.addConst_structEtas_eq hhead)

theorem VEnv.addDefEqs_structEtas_eq (env : VEnv) (cis : List VDefVal) :
    (env.addDefEqs cis).structEtas = env.structEtas := by
  induction cis generalizing env with
  | nil => rfl
  | cons ci cis ih => exact ih (env := env.addDefEq ci.toDefEq)

theorem VEnv.constFold_structEtas_eq {env env' : VEnv} :
    ∀ {cis : List VConstVal},
      cis.foldlM (fun env ci => env.addConst ci.name ci.toVConstant) env =
        some env' →
      env'.structEtas = env.structEtas
  | [], h => by cases h; rfl
  | _ :: _, h => by
      simp only [List.foldlM_cons, Option.bind_eq_bind] at h
      obtain ⟨middle, hhead, htail⟩ := Option.bind_eq_some_iff.1 h
      exact (VEnv.constFold_structEtas_eq htail).trans
        (VEnv.addConst_structEtas_eq hhead)

theorem VEnv.constFold_le {env env' : VEnv} :
    ∀ {cis : List VConstVal},
      cis.foldlM (fun env ci => env.addConst ci.name ci.toVConstant) env =
        some env' →
      env ≤ env'
  | [], h => by cases h; exact .rfl
  | _ :: _, h => by
      simp only [List.foldlM_cons, Option.bind_eq_bind] at h
      obtain ⟨middle, hhead, htail⟩ := Option.bind_eq_some_iff.1 h
      exact (VEnv.addConst_le hhead).trans (VEnv.constFold_le htail)

theorem VEnv.rulesFold_structEtas_eq (env : VEnv) (dfs : List VDefEq) :
    (dfs.foldl VEnv.addDefEq env).structEtas = env.structEtas := by
  induction dfs generalizing env with
  | nil => rfl
  | cons df dfs ih => exact ih (env := env.addDefEq df)

theorem VEnv.rulesFold_le (env : VEnv) (dfs : List VDefEq) :
    env ≤ dfs.foldl VEnv.addDefEq env := by
  induction dfs generalizing env with
  | nil => exact .rfl
  | cons df dfs ih => exact VEnv.addDefEq_le.trans (ih (env := env.addDefEq df))

theorem VEnv.addConst_eq_none {env : VEnv} {name ci}
    (h : env.constants name = none) : ∃ env', env.addConst name ci = some env' := by
  unfold VEnv.addConst; rw [h]; exact ⟨_, rfl⟩

theorem VEnv.addConst_constants_eq {env env' : VEnv} {name ci}
    (h : env.addConst name ci = some env') :
    env'.constants = fun n => if name = n then some ci else env.constants n := by
  unfold VEnv.addConst at h; split at h <;> cases h; rfl

/-- A block of constants can be added as long as each name is fresh and the block has no
duplicates; the latter is what `addMutual`'s `found` set checks. -/
theorem VEnv.exists_addConsts {env : VEnv} : ∀ {cis : List VDefVal},
    (∀ ci ∈ cis, env.constants ci.name = none) → (cis.map (·.name)).Nodup →
    ∃ env', env.addConsts cis = some env'
  | [], _, _ => ⟨_, rfl⟩
  | ci :: cis, hfresh, hnd => by
    obtain ⟨env₁, h₁⟩ := VEnv.addConst_eq_none (ci := ci.toVConstant) (hfresh _ (.head _))
    rw [List.map_cons, List.nodup_cons] at hnd
    have ⟨env₂, h₂⟩ := VEnv.exists_addConsts (env := env₁) (cis := cis) (fun c hc => ?_) hnd.2
    · exact ⟨env₂, by simp [VEnv.addConsts, h₁]; exact h₂⟩
    · rw [VEnv.addConst_constants_eq h₁]
      have : ci.name ≠ c.name := fun h => hnd.1 (List.mem_map.2 ⟨c, hc, h.symm⟩)
      simp [this, hfresh c (.tail _ hc)]

/-- A source-ordered block of constant headers can be inserted whenever all
of its names are initially fresh and pairwise distinct. -/
theorem VEnv.exists_constFold {env : VEnv} : ∀ {cis : List VConstVal},
    (∀ ci ∈ cis, env.constants ci.name = none) →
      (cis.map (·.name)).Nodup →
        ∃ env', cis.foldlM
          (fun env ci => env.addConst ci.name ci.toVConstant) env = some env'
  | [], _, _ => ⟨_, rfl⟩
  | ci :: cis, hfresh, hnd => by
    obtain ⟨env₁, h₁⟩ :=
      VEnv.addConst_eq_none (ci := ci.toVConstant) (hfresh _ (.head _))
    rw [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨env₂, h₂⟩ := VEnv.exists_constFold
      (env := env₁) (cis := cis) (fun c hc => by
        rw [VEnv.addConst_constants_eq h₁]
        have hne : ci.name ≠ c.name := fun h =>
          hnd.1 (List.mem_map.2 ⟨c, hc, h.symm⟩)
        simp [hne, hfresh c (.tail _ hc)]) hnd.2
    exact ⟨env₂, by
      simp only [List.foldlM_cons, h₁]
      exact h₂⟩

theorem VEnv.addConsts_congr {env : VEnv} : ∀ {cis cis' : List VDefVal},
    List.Forall₂ (fun a b => a.toVConstVal = b.toVConstVal) cis cis' →
    env.addConsts cis = env.addConsts cis'
  | [], [], _ => rfl
  | a :: _, b :: _, .cons h t => by
    have h1 : a.name = b.name := congrArg VConstVal.name h
    have h2 : a.toVConstant = b.toVConstant := congrArg VConstVal.toVConstant h
    show (env.addConst a.name a.toVConstant).bind _ = (env.addConst b.name b.toVConstant).bind _
    rw [h1, h2]
    cases env.addConst b.name b.toVConstant
    · rfl
    · exact VEnv.addConsts_congr t

theorem VEnv.addConsts_ordered {env env' : VEnv} : ∀ {cis}, Ordered env →
    (∀ ci ∈ cis, ci.toVConstant.WF env) → env.addConsts cis = some env' → Ordered env'
  | [], h, _, e => by cases e; exact h
  | _ :: _, h, hw, e => by
    simp [VEnv.addConsts, Option.bind_eq_some_iff] at e
    obtain ⟨_, h1, h2⟩ := e
    refine VEnv.addConsts_ordered (.const h (hw _ (.head _)) h1) (fun c hc => ?_) h2
    exact (hw c (.tail _ hc)).mono (VEnv.addConst_le h1)

theorem VEnv.addConsts_constants {env env' : VEnv} : ∀ {cis}, env.addConsts cis = some env' →
    ∀ ci ∈ cis, env'.constants ci.name = some ci.toVConstant
  | [], _, _, hc => nomatch hc
  | _ :: _, e, c, hc => by
    simp [VEnv.addConsts, Option.bind_eq_some_iff] at e
    obtain ⟨_, h1, h2⟩ := e
    cases hc with
    | head => exact (VEnv.addConsts_le h2).constants (VEnv.addConst_self h1)
    | tail _ hc => exact VEnv.addConsts_constants h2 c hc

theorem VEnv.addDefEqs_ordered : ∀ {env : VEnv} {cis}, Ordered env →
    (∀ ci ∈ cis, env.constants ci.name = some ci.toVConstant) →
    (∀ ci ∈ cis, ci.WF env) → Ordered (env.addDefEqs cis)
  | _, [], h, _, _ => h
  | env, ci :: cis, h, hmem, hw => by
    have hci : ci.WF env := hw _ (.head _)
    have hord : Ordered (env.addDefEq ci.toDefEq) := by
      refine .defeq h ⟨?_, hci⟩
      simp [VDefVal.toDefEq]
      rw [← (hci.levelWF ⟨⟩).2.2.instL_id]
      exact .const (hmem _ (.head _)) VLevel.id_WF (by simp)
    show Ordered ((env.addDefEq ci.toDefEq).addDefEqs cis)
    refine VEnv.addDefEqs_ordered hord (fun c hc => ?_) (fun c hc => ?_)
    · exact (VEnv.addDefEq_le (df := ci.toDefEq)).constants (hmem c (.tail _ hc))
    · exact (hw c (.tail _ hc)).mono VEnv.addDefEq_le

theorem VEnv.addQuot_le {env env' : VEnv}
    (hadd : env.addQuot = some env') : env ≤ env' := by
  unfold VEnv.addQuot at hadd
  obtain ⟨env₁, h₁, hadd⟩ := Option.bind_eq_some_iff.1 hadd
  obtain ⟨env₂, h₂, hadd⟩ := Option.bind_eq_some_iff.1 hadd
  obtain ⟨env₃, h₃, hadd⟩ := Option.bind_eq_some_iff.1 hadd
  obtain ⟨env₄, h₄, hadd⟩ := Option.bind_eq_some_iff.1 hadd
  cases hadd
  exact (VEnv.addConst_le h₁).trans <|
    (VEnv.addConst_le h₂).trans <|
      (VEnv.addConst_le h₃).trans <|
        (VEnv.addConst_le h₄).trans VEnv.addDefEq_le

theorem VEnv.addQuot_structEtas_eq {env env' : VEnv}
    (hadd : env.addQuot = some env') :
    env'.structEtas = env.structEtas := by
  unfold VEnv.addQuot at hadd
  obtain ⟨env₁, h₁, hadd⟩ := Option.bind_eq_some_iff.1 hadd
  obtain ⟨env₂, h₂, hadd⟩ := Option.bind_eq_some_iff.1 hadd
  obtain ⟨env₃, h₃, hadd⟩ := Option.bind_eq_some_iff.1 hadd
  obtain ⟨env₄, h₄, hadd⟩ := Option.bind_eq_some_iff.1 hadd
  cases hadd
  exact (VEnv.addConst_structEtas_eq h₄).trans <|
    (VEnv.addConst_structEtas_eq h₃).trans <|
      (VEnv.addConst_structEtas_eq h₂).trans <|
        VEnv.addConst_structEtas_eq h₁

theorem VEnv.addInductGeneration_structEtas_eq
    {env env' : VEnv} {source : VInductDecl}
    {gen : source.GenerationChecked}
    (hadd : VEnv.addInductGeneration env gen = some env') :
    env'.structEtas = env.structEtas := by
  unfold VEnv.addInductGeneration at hadd
  obtain ⟨typeEnv, htype, hadd⟩ := Option.bind_eq_some_iff.1 hadd
  obtain ⟨ctorEnv, hctors, hadd⟩ := Option.bind_eq_some_iff.1 hadd
  obtain ⟨recEnv, hrec, hadd⟩ := Option.bind_eq_some_iff.1 hadd
  cases hadd
  exact (VEnv.rulesFold_structEtas_eq recEnv gen.generatedRules).trans <|
    (VEnv.addConst_structEtas_eq hrec).trans <|
      (VEnv.constFold_structEtas_eq hctors).trans <|
        VEnv.addConst_structEtas_eq htype

theorem VEnv.addInductBlockGeneration_structEtas_eq
    {env env' : VEnv} {source : VInductDecl}
    {gen : source.BlockGenerationChecked}
    (hadd : VEnv.addInductBlockGeneration env gen = some env') :
    env'.structEtas = env.structEtas := by
  unfold VEnv.addInductBlockGeneration at hadd
  obtain ⟨typeEnv, htypes, hadd⟩ := Option.bind_eq_some_iff.1 hadd
  obtain ⟨ctorEnv, hctors, hadd⟩ := Option.bind_eq_some_iff.1 hadd
  obtain ⟨recEnv, hrecs, hadd⟩ := Option.bind_eq_some_iff.1 hadd
  cases hadd
  exact (VEnv.rulesFold_structEtas_eq recEnv gen.generatedRules).trans <|
    (VEnv.constFold_structEtas_eq hrecs).trans <|
      (VEnv.constFold_structEtas_eq hctors).trans <|
        VEnv.constFold_structEtas_eq htypes

theorem VEnv.addInductNested_structEtas_eq
    {env env' : VEnv} {source : VInductDecl}
    {nested : source.NestedBlockChecked}
    (hadd : VEnv.addInductNested env nested = some env') :
    env'.structEtas = env.structEtas := by
  unfold VEnv.addInductNested at hadd
  obtain ⟨typeEnv, htypes, hadd⟩ := Option.bind_eq_some_iff.1 hadd
  obtain ⟨ctorEnv, hctors, hadd⟩ := Option.bind_eq_some_iff.1 hadd
  obtain ⟨recEnv, hrecs, hadd⟩ := Option.bind_eq_some_iff.1 hadd
  cases hadd
  exact (VEnv.rulesFold_structEtas_eq recEnv nested.generatedRules).trans <|
    (VEnv.constFold_structEtas_eq hrecs).trans <|
      (VEnv.constFold_structEtas_eq hctors).trans <|
        VEnv.constFold_structEtas_eq htypes

theorem VEnv.addInductGeneration_le_theory
    {env env' : VEnv} {source : VInductDecl}
    {gen : source.GenerationChecked}
    (hadd : VEnv.addInductGeneration env gen = some env') : env ≤ env' := by
  unfold VEnv.addInductGeneration at hadd
  obtain ⟨typeEnv, htype, hadd⟩ := Option.bind_eq_some_iff.1 hadd
  obtain ⟨ctorEnv, hctors, hadd⟩ := Option.bind_eq_some_iff.1 hadd
  obtain ⟨recEnv, hrec, hadd⟩ := Option.bind_eq_some_iff.1 hadd
  cases hadd
  exact (VEnv.addConst_le htype).trans <|
    (VEnv.constFold_le hctors).trans <|
      (VEnv.addConst_le hrec).trans
        (VEnv.rulesFold_le recEnv gen.generatedRules)

theorem VEnv.addInductBlockGeneration_le_theory
    {env env' : VEnv} {source : VInductDecl}
    {gen : source.BlockGenerationChecked}
    (hadd : VEnv.addInductBlockGeneration env gen = some env') : env ≤ env' := by
  unfold VEnv.addInductBlockGeneration at hadd
  obtain ⟨typeEnv, htypes, hadd⟩ := Option.bind_eq_some_iff.1 hadd
  obtain ⟨ctorEnv, hctors, hadd⟩ := Option.bind_eq_some_iff.1 hadd
  obtain ⟨recEnv, hrecs, hadd⟩ := Option.bind_eq_some_iff.1 hadd
  cases hadd
  exact (VEnv.constFold_le htypes).trans <|
    (VEnv.constFold_le hctors).trans <|
      (VEnv.constFold_le hrecs).trans
        (VEnv.rulesFold_le recEnv gen.generatedRules)

theorem VEnv.addInductNested_le_theory
    {env env' : VEnv} {source : VInductDecl}
    {nested : source.NestedBlockChecked}
    (hadd : VEnv.addInductNested env nested = some env') : env ≤ env' := by
  unfold VEnv.addInductNested at hadd
  obtain ⟨typeEnv, htypes, hadd⟩ := Option.bind_eq_some_iff.1 hadd
  obtain ⟨ctorEnv, hctors, hadd⟩ := Option.bind_eq_some_iff.1 hadd
  obtain ⟨recEnv, hrecs, hadd⟩ := Option.bind_eq_some_iff.1 hadd
  cases hadd
  exact (VEnv.constFold_le htypes).trans <|
    (VEnv.constFold_le hctors).trans <|
      (VEnv.constFold_le hrecs).trans
        (VEnv.rulesFold_le recEnv nested.generatedRules)

theorem VDecl.WF.le : VDecl.WF env decl env' → env ≤ env'
  | .axiom _ hadd => VEnv.addConst_le hadd
  | .def _ hadd => (VEnv.addConst_le hadd).trans VEnv.addDefEq_le
  | .mutualDef _ hadd _ =>
      (VEnv.addConsts_le hadd).trans (VEnv.addDefEqs_le_theory _)
  | .opaque _ hadd => VEnv.addConst_le hadd
  | .example _ => .rfl
  | .quot _ hadd => VEnv.addQuot_le hadd
  | .induct _ hadd => VEnv.addInductGeneration_le_theory hadd
  | .inductBlock _ hadd => VEnv.addInductBlockGeneration_le_theory hadd
  | .inductNested _ hadd => VEnv.addInductNested_le_theory hadd

theorem VDecl.WF.structEtas_eq :
    VDecl.WF env decl env' → env'.structEtas = env.structEtas
  | .axiom _ hadd => VEnv.addConst_structEtas_eq hadd
  | @«def» env middle ci _ hadd => by
      change env.structEtas = middle.structEtas
      exact VEnv.addConst_structEtas_eq hadd
  | .mutualDef _ hadd _ =>
      (VEnv.addDefEqs_structEtas_eq _ _).trans
        (VEnv.addConsts_structEtas_eq hadd)
  | .opaque _ hadd => VEnv.addConst_structEtas_eq hadd
  | .example _ => rfl
  | .quot _ hadd => VEnv.addQuot_structEtas_eq hadd
  | .induct _ hadd => VEnv.addInductGeneration_structEtas_eq hadd
  | .inductBlock _ hadd =>
      VEnv.addInductBlockGeneration_structEtas_eq hadd
  | .inductNested _ hadd => VEnv.addInductNested_structEtas_eq hadd

theorem VEnv.WF.ordered : WF env → Ordered env
  | ⟨ds, H⟩ => by
    induction H with
    | empty => exact .empty
    | decl h _ ih =>
      cases h with
      | «axiom» h1 h2 => exact .const ih h1 h2
      | @«def» env env' ci h1 h2 =>
        refine .defeq (.const ih (h1.isType ih ⟨⟩) h2) ⟨?_, ?_⟩
        · simp [VDefVal.toDefEq]
          rw [← (h1.levelWF ⟨⟩).2.2.instL_id]
          exact .const (addConst_self h2) VLevel.id_WF (by simp)
        · exact h1.mono (addConst_le h2)
      | mutualDef h0 h1 h2 =>
        exact VEnv.addDefEqs_ordered (VEnv.addConsts_ordered ih h0 h1)
          (VEnv.addConsts_constants h1) h2
      | «opaque» h1 h2 => exact .const ih (h1.isType ih ⟨⟩) h2
      | «example» _ => exact ih
      | quot h1 h2 => exact addQuot_WF ih h1 h2
      | induct h1 h2 => exact addInductGeneration_WF ih h1 h2
      | inductBlock h1 h2 => exact addInductBlockGeneration_WF ih h1 h2
      | inductNested h1 h2 => exact VEnv.addInductNested_WF ih h1 h2
    | structEta hwf _ ih => exact .structEta ih hwf.toFoundationWF

instance : CoeOut (VEnv.WF env) env.Ordered := ⟨(·.ordered)⟩

/-- Recover the full subject-reduction certificate for a registered
structure-eta rule from the well-formed environment history.  `Ordered`
retains only the closure fragment needed by structural metatheory; the full
certificate deliberately lives here. -/
theorem VEnv.WF.structEtaWF (henv : VEnv.WF env)
    (hregistered : env.structEtas rule) : VStructEta.WF rule env := by
  rcases henv with ⟨decls, history⟩
  induction history with
  | empty => cases hregistered
  | decl hdecl _ ih =>
      have hbefore := hregistered
      rw [hdecl.structEtas_eq] at hbefore
      exact (ih hbefore).mono hdecl.le
  | structEta hrule _ ih =>
      change _ = _ ∨ _ at hregistered
      rcases hregistered with rfl | hregistered
      · exact hrule.mono VEnv.addStructEta_le
      · exact (ih hregistered).mono VEnv.addStructEta_le
