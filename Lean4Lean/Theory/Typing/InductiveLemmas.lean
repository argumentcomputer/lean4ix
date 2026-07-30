import Std
import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.Env
import Lean4Lean.Theory.Typing.Meta

namespace Lean4Lean

/-! ## Basic facts about the stage-1 generation helpers -/

namespace VLevel

theorem params'_length : (params' n k).length = n := by simp [params']

theorem params'_wf : ∀ l ∈ params' n k, l.WF (n + k) := by
  simp only [params', List.mem_map, List.mem_range]
  rintro _ ⟨i, hi, rfl⟩; exact Nat.add_lt_add_right hi _

theorem params'_one_wf : ∀ l ∈ params' n 1, l.WF (n + 1) := params'_wf

theorem params_map_inst_params' :
    (params n).map (VLevel.inst (params' n 1)) = params' n 1 :=
  inst_map_id params'_length

end VLevel

namespace VExpr

theorem forallN_append (As Bs : List VExpr) (e : VExpr) :
    forallN (As ++ Bs) e = forallN As (forallN Bs e) := by
  induction As with
  | nil => rfl
  | cons A As ih => simp [forallN, ih]

theorem instL_forallN (ls : List VLevel) (As : List VExpr) (e : VExpr) :
    (forallN As e).instL ls = forallN (As.map (instL ls)) (e.instL ls) := by
  induction As with
  | nil => rfl
  | cons A As ih => simp [forallN, instL, ih]

theorem instL_appN (ls : List VLevel) (as : List VExpr) (f : VExpr) :
    (appN f as).instL ls = appN (f.instL ls) (as.map (instL ls)) := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih => simp [appN, instL, ih]

/-- Substituting a variable for the sole loose variable is a lift. -/
theorem inst_bvar_of_closedN (h : ClosedN e (k+1)) :
    e.inst (.bvar n) k = e.liftN n k := by
  induction e generalizing k with simp_all [ClosedN, inst, liftN]
  | bvar i =>
    simp only [instVar]
    rcases Nat.lt_trichotomy i k with h' | rfl | h'
    · simp [h', liftVar_lt h']
    · simp [liftVar_le (Nat.le_refl _), liftN, liftVar_base, Nat.add_comm]
    · omega

theorem ClosedN.appN {f : VExpr} (hf : f.ClosedN k) {as : List VExpr}
    (has : ∀ a ∈ as, ClosedN a k) : (appN f as).ClosedN k := by
  induction as generalizing f with
  | nil => exact hf
  | cons a as ih =>
    exact ih ⟨hf, has _ (.head _)⟩ fun a h => has _ (.tail _ h)

theorem LevelWF.appN {f : VExpr} (hf : f.LevelWF U) {as : List VExpr}
    (has : ∀ a ∈ as, LevelWF U a) : (appN f as).LevelWF U := by
  induction as generalizing f with
  | nil => exact hf
  | cons a as ih =>
    exact ih ⟨hf, has _ (.head _)⟩ fun a h => has _ (.tail _ h)

theorem LevelWF.forallN {As : List VExpr} (hAs : ∀ A ∈ As, LevelWF U A)
    {e : VExpr} (he : e.LevelWF U) : (forallN As e).LevelWF U := by
  induction As with
  | nil => exact he
  | cons A As ih =>
    exact ⟨hAs _ (.head _), ih fun A h => hAs _ (.tail _ h)⟩

theorem LevelWF.lamN {As : List VExpr} (hAs : ∀ A ∈ As, LevelWF U A)
    {e : VExpr} (he : e.LevelWF U) : (lamN As e).LevelWF U := by
  induction As with
  | nil => exact he
  | cons A As ih =>
    exact ⟨hAs _ (.head _), ih fun A h => hAs _ (.tail _ h)⟩

end VExpr

/-! ## Anatomy of the stage-1 predicate -/

namespace VInductDecl

theorem stage1Field_iff {U T B} : stage1Field U T B ↔
    B = .const T (VLevel.params U) ∨ (B.ClosedN 0 ∧ B.hasConst T = false) := by
  simp [stage1Field, Bool.or_eq_true, Bool.and_eq_true]

theorem stage1Ctor_eq {U T} {e : VExpr} (h : stage1Ctor U T e) :
    e = VExpr.forallN (ctorFields e) (.const T (VLevel.params U)) ∧
    ∀ B ∈ ctorFields e, stage1Field U T B := by
  induction e with
  | forallE B rest _ ih =>
    simp only [stage1Ctor, Bool.and_eq_true] at h
    have ⟨ih1, ih2⟩ := ih h.2
    refine ⟨congrArg (VExpr.forallE B) ih1, ?_⟩
    intro B' hB'
    simp only [ctorFields] at hB'
    rcases List.mem_cons.1 hB' with rfl | hB'
    · exact h.1
    · exact ih2 _ hB'
  | const c ls =>
    simp only [stage1Ctor, beq_iff_eq, VExpr.const.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, by simp [ctorFields]⟩
  | _ => simp [stage1Ctor] at h

/-- Unpack `stage1` for a declaration already known (from `addInduct`
success) to have a singleton type list. -/
theorem stage1_anatomy {U np ty} (h : stage1 ⟨U, np, [ty]⟩) :
    np = 0 ∧ ty.uvars = U ∧
    (∃ l, ty.type = .sort l ∧ l.WF U ∧ l.isNeverZero) ∧
    ∀ c ∈ ty.ctors, c.uvars = U ∧ stage1Ctor U ty.name c.type := by
  cases np with
  | succ np => exact Bool.noConfusion h
  | zero =>
    simp only [stage1, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    refine ⟨rfl, h1, ?_, fun c hc => by simpa using h3 c hc⟩
    split at h2
    · next l heq => exact ⟨l, heq, by simpa [Bool.and_eq_true] using h2⟩
    · exact Bool.noConfusion h2

end VInductDecl

/-! ## `addInduct_WF` -/

namespace VEnv

theorem addInduct_WF (henv : Ordered env) (hdecl : decl.WF env)
    (henv' : addInduct env decl = some env') : Ordered env' :=
  sorry

end VEnv
