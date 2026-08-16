import Lean4Lean.Theory.Typing.Lemmas
import Lean4Lean.Theory.Typing.Pattern
import Lean4Lean.Theory.Typing.Strong

namespace Lean4Lean
open Lean4Lean

inductive Classification where
  | ctor (arity : Nat)
  | etaCtor (params args : Nat)
  | symb (arity : Nat)
  | indTy (arity : Nat)

def Classification.arity : Classification → Nat
  | .ctor k | .symb k | .indTy k => k
  | .etaCtor p a => p + a

def Pattern.WF (cl : Name → Option Classification) :
    Pattern → (top : Bool := true) → (extra : Nat := 0) → Prop
  | .const c, top, n => cl c = some (if top then .symb n else .ctor n)
  | .var p, top, n => WF cl p top (n + 1)
  | .app p p', top, n => WF cl p top (n + 1) ∧ WF cl p' false

class Params where
  env : VEnv
  henv : env.Ordered
  univs : Nat
  Pat : (p : Pattern) → p.RHS × p.Check → Prop
  classify : Name → Option Classification
  pat_simple : Pat p r → ∃ sp : SimplePattern, p = sp.toPattern
  pat_wf : Pat p r → p.WF classify
  pat_uniq : Pat p₁ r → Pat p₂ r' → Subpattern p₃ p₁ → p₂.inter p₃ = some p₄ →
    p₁ = p₂ ∧ p₂ = p₃ ∧ r ≍ r'
  -- pat_wf : Pat p r → p.Matches e m1 m2 → HasType env univs Γ e A →
  --   r.2.OK (IsDefEqU env univs Γ) m1 m2 → IsDefEqU env univs Γ e (r.1.apply m1 m2)
  pat_app_l : Pat p r → Subpattern (.app p₁ p₂) p → ¬Subpattern (.app p₃ p₄) p₁
  pat_app_l_uniq : Pat p r → Pat p' r' → Subpattern (.app p₁ p₂) p →
    Subpattern (.app p₁' p₂') p' → Subpattern (.var p₃) p₁ → p₁'.inter p₃ = none
  pat_app_uniq : Pat p r → Pat p' r' → Subpattern (.app p₁ p₂) p →
    Subpattern (.app p₁' p₂') p' → Subpattern p₃ p₁ → Subpattern p₃' p₂' → p₃.inter p₃' = none
  -- pat_app_r_arity : Pat p r → Pat p' r' → Subpattern (.app p₁ p₂) p →
  --   Subpattern (.app p₁' p₂') p' → Arity (.const c) n p₂ → Arity (.const c) n' p₂' → n = n'
  -- extra_pat : env.defeqs df → (∀ l ∈ ls, l.WF uvars) → ls.length = df.uvars →
  --   ∃ p r m1 m2, Pat p r ∧ p.Matches (df.lhs.instL ls) m1 m2 ∧ r.2.OK (IsDefEqU env univs Γ) m1 m2 ∧
  --   df.rhs.instL ls = r.1.apply m1 m2
open Params
variable [Params]

/-- A semantically quotiented version of `VLevel`. This avoids the need for some congruences. -/
def SLevel := { f : List Nat → Nat // ∃ l : VLevel, l.WF univs ∧ l.eval = f }

namespace SLevel

def zero : SLevel := ⟨_, .zero, ⟨⟩, rfl⟩

def mk (l : VLevel) : SLevel := if h : l.WF univs then ⟨_, l, h, rfl⟩ else .zero

/-- Choose a well-formed syntactic representative of a semantic level. -/
noncomputable def reify (l : SLevel) : VLevel := Classical.choose l.2

theorem reify_wf (l : SLevel) : (reify l).WF univs :=
  (Classical.choose_spec l.2).1

theorem reify_eval (l : SLevel) : (reify l).eval = l.1 :=
  (Classical.choose_spec l.2).2

theorem mk_of_wf (h : l.WF univs) :
    mk l = (⟨_, l, h, rfl⟩ : SLevel) := by
  have hm : mk l = if h' : l.WF univs then
      (⟨_, l, h', rfl⟩ : SLevel) else SLevel.zero := rfl
  rw [hm]
  exact dif_pos h

@[simp] theorem mk_reify (l : SLevel) : mk (reify l) = l := by
  rw [mk_of_wf (reify_wf l)]
  apply Subtype.ext
  exact reify_eval l

theorem mk_eq (hl : l.WF univs) (hl' : l'.WF univs) (h : l ≈ l') : mk l = mk l' := by
  rw [mk_of_wf hl, mk_of_wf hl']
  apply Subtype.ext
  exact VLevel.equiv_def'.1 h

theorem mk_val (h : l.WF univs) : (mk l).1 = l.eval := by rw [mk_of_wf h]

/-- Equality after semantic level translation reflects the source levels
up to Lean's level equivalence.  Literal syntactic injectivity is neither
true nor needed. -/
theorem equiv_of_mk_eq (hl : l.WF univs) (hl' : l'.WF univs)
    (h : mk l = mk l') : l ≈ l' := by
  apply VLevel.equiv_def'.2
  rw [← mk_val hl, ← mk_val hl', h]

theorem forall₂_equiv_of_map_mk_eq
    (hls : ∀ l ∈ ls, l.WF univs) (hls' : ∀ l ∈ ls', l.WF univs)
    (h : ls.map mk = ls'.map mk) : List.Forall₂ (· ≈ ·) ls ls' := by
  induction ls generalizing ls' with
  | nil =>
    cases ls' with
    | nil => exact .nil
    | cons => cases h
  | cons l ls ih =>
    cases ls' with
    | nil => cases h
    | cons l' ls' =>
      simp only [List.map_cons, List.cons.injEq] at h
      exact .cons
        (equiv_of_mk_eq (hls l (.head _)) (hls' l' (.head _)) h.1)
        (ih (fun x hx => hls x (.tail _ hx))
          (fun x hx => hls' x (.tail _ hx)) h.2)

@[simp] theorem mk_zero : mk .zero = zero := by
  apply Subtype.ext
  rfl

def succ (l : SLevel) : SLevel :=
  ⟨fun v => l.1 v + 1, let ⟨u, h1, h2⟩ := l.2; ⟨u.succ, h1, h2 ▸ rfl⟩⟩

def max (l₁ l₂ : SLevel) : SLevel :=
  ⟨fun v => (l₁.1 v).max (l₂.1 v),
    let ⟨u, h1, h2⟩ := l₁.2; let ⟨v, h3, h4⟩ := l₂.2; ⟨u.max v, ⟨h1, h3⟩, h2 ▸ h4 ▸ rfl⟩⟩

def imax (l₁ l₂ : SLevel) : SLevel :=
  ⟨fun v => Lean.Nat.imax (l₁.1 v) (l₂.1 v),
    let ⟨u, h1, h2⟩ := l₁.2; let ⟨v, h3, h4⟩ := l₂.2; ⟨u.imax v, ⟨h1, h3⟩, h2 ▸ h4 ▸ rfl⟩⟩

@[simp] theorem mk_succ (h : l.WF univs) : mk l.succ = succ (mk l) := by
  have hs : l.succ.WF univs := h
  rw [mk_of_wf hs, mk_of_wf h]; apply Subtype.ext; rfl

@[simp] theorem mk_max (h1 : l₁.WF univs) (h2 : l₂.WF univs) :
    mk (.max l₁ l₂) = max (mk l₁) (mk l₂) := by
  rw [mk_of_wf (l := l₁.max l₂) ⟨h1, h2⟩, mk_of_wf h1, mk_of_wf h2]
  apply Subtype.ext; rfl

@[simp] theorem mk_imax (h1 : l₁.WF univs) (h2 : l₂.WF univs) :
    mk (.imax l₁ l₂) = imax (mk l₁) (mk l₂) := by
  rw [mk_of_wf (l := l₁.imax l₂) ⟨h1, h2⟩, mk_of_wf h1, mk_of_wf h2]
  apply Subtype.ext; rfl

def inst (ls : List SLevel) (l : SLevel) : SLevel := by
  refine ⟨fun v => l.1 (ls.map (·.1 v)), ?_⟩
  simp [funext_iff]
  have ⟨ls', h3⟩ :
      ∃ ls' : List VLevel, ls'.Forall₂ (fun l' l => l'.WF univs ∧ l'.eval = l.1) ls := by
    induction ls with
    | nil => exact ⟨_, .nil⟩
    | cons a l ih =>
      let ⟨l', h1, h2⟩ := a.2; let ⟨ls', h3⟩ := ih
      exact ⟨l'::ls', .cons ⟨h1, h2⟩ h3⟩
  have ⟨l', h1, h2⟩ := l.2
  refine ⟨l'.inst ls', VLevel.WF.inst fun _ h => ?_, fun v => ?_⟩
  · let ⟨_, h⟩ := h3.forall_exists_l _ h; exact h.2.1
  · simp [VLevel.eval_inst, ← h2]; congr 1
    rw [← List.forall₂_eq, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact h3.imp fun _ _ h => congrFun h.2 _

/-- Instantiate a syntactic level directly into semantic levels. Unlike `inst ls (mk l)`,
this does not require `l` to be well-formed in the ambient universe context. -/
def instV (ls : List SLevel) (l : VLevel) : SLevel := by
  refine ⟨fun v => l.eval (ls.map (·.1 v)), ?_⟩
  have ⟨ls', h⟩ :
      ∃ ls' : List VLevel, ls'.Forall₂ (fun l' l => l'.WF univs ∧ l'.eval = l.1) ls := by
    induction ls with
    | nil => exact ⟨_, .nil⟩
    | cons a ls ih =>
      let ⟨l', h1, h2⟩ := a.2
      let ⟨ls', ih⟩ := ih
      exact ⟨l' :: ls', .cons ⟨h1, h2⟩ ih⟩
  refine ⟨l.inst ls', VLevel.WF.inst fun _ hl => ?_, ?_⟩
  · let ⟨_, hl⟩ := h.forall_exists_l _ hl; exact hl.2.1
  · funext v
    simp only [VLevel.eval_inst]
    congr 1
    rw [← List.forall₂_eq, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact h.imp fun _ _ hl => congrFun hl.2 _

theorem instV_map_mk (hls : ∀ u ∈ ls, u.WF univs) :
    instV (ls.map mk) l = mk (l.inst ls) := by
  apply Subtype.ext
  funext ns
  rw [congrFun (mk_val (VLevel.WF.inst hls)) ns]
  simp only [VLevel.eval_inst]
  change l.eval ((ls.map mk).map fun u => u.1 ns) = l.eval (ls.map (VLevel.eval ns))
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  intro u hu
  exact congrFun (mk_val (hls u hu)) ns

theorem mk_inst (hl : l.WF univs) (hls : ∀ u ∈ ls, u.WF univs) :
    mk (l.inst ls) = inst (ls.map mk) (mk l) := by
  apply Subtype.ext
  funext ns
  rw [congrFun (mk_val (VLevel.WF.inst hls)) ns]
  simp only [VLevel.eval_inst]
  change l.eval (ls.map (VLevel.eval ns)) = (mk l).1 ((ls.map mk).map fun u => u.1 ns)
  rw [congrFun (mk_val hl) _]
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  intro u hu
  exact (congrFun (mk_val (hls u hu)) ns).symm

theorem map_mk_eq (hls : ∀ l ∈ ls, l.WF univs) (hls' : ∀ l ∈ ls', l.WF univs)
    (h : List.Forall₂ (fun l l' => l ≈ l') ls ls') :
    ls.map mk = ls'.map mk := by
  induction h with
  | nil => rfl
  | cons h _ ih =>
    simp only [List.map_cons]
    rw [mk_eq (hls _ (by simp)) (hls' _ (by simp)) h,
      ih (fun _ hu => hls _ (by simp [hu])) (fun _ hu => hls' _ (by simp [hu]))]

end SLevel

inductive SExpr where
  | bvar (i : Nat)
  | sort (u : SLevel)
  | const (c : Name) (ls : List SLevel)
  | app (f a : SExpr)
  | lam (A e : SExpr)
  | forallE (A B : SExpr)

instance : Inhabited SExpr := ⟨.sort .zero⟩

namespace SExpr

@[simp] def lift' : SExpr → Lift → SExpr
  | .bvar i, k => .bvar (k.liftVar i)
  | .sort u, _ => .sort u
  | .const c us, _ => .const c us
  | .app fn arg, k => .app (fn.lift' k) (arg.lift' k)
  | .lam ty body, k => .lam (ty.lift' k) (body.lift' k.cons)
  | .forallE ty body, k => .forallE (ty.lift' k) (body.lift' k.cons)

abbrev lift e := lift' e (.skip .refl)

theorem lift'_comp {e : SExpr} : e.lift' (.comp l₁ l₂) = (e.lift' l₁).lift' l₂ := Eq.symm <| by
  induction e generalizing l₁ l₂ <;> simp [Lift.liftVar_comp, *]

theorem lift'_depth_zero {e : SExpr} (H : l.depth = 0) : e.lift' l = e := by
  induction e generalizing l <;> simp_all [Lift.liftVar_depth_zero]

@[simp] theorem lift'_refl {e : SExpr} : e.lift' .refl = e := lift'_depth_zero rfl

def ClosedN : SExpr → (k :_:= 0) → Prop
  | .bvar i, k => i < k
  | .sort .., _ | .const .., _ => True
  | .app fn arg, k => fn.ClosedN k ∧ arg.ClosedN k
  | .lam ty body, k => ty.ClosedN k ∧ body.ClosedN (k+1)
  | .forallE ty body, k => ty.ClosedN k ∧ body.ClosedN (k+1)

theorem ClosedN.mono (h : k ≤ k') (self : ClosedN e k) : ClosedN e k' := by
  induction e generalizing k k' with (simp [ClosedN] at self ⊢; try simp [self, *])
  | bvar i => exact Nat.lt_of_lt_of_le self h
  | app _ _ ih1 ih2 => exact ⟨ih1 h self.1, ih2 h self.2⟩
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 =>
    exact ⟨ih1 h self.1, ih2 (Nat.succ_le_succ h) self.2⟩

theorem ClosedN.lift'_eq (self : ClosedN e k) (h : ρ.Fixes k) : lift' e ρ = e := by
  induction e generalizing k ρ with (simp [ClosedN] at self; simp [*])
  | bvar i => exact h.liftVar_eq self
  | app _ _ ih1 ih2 => exact ⟨ih1 self.1 h, ih2 self.2 h⟩
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 => exact ⟨ih1 self.1 h, ih2 self.2 h⟩

theorem ClosedN.lift_eq (self : ClosedN e) : lift e = e := self.lift'_eq ⟨⟩

variable (ls : List SLevel) in
def instL : SExpr → SExpr
  | .bvar i => .bvar i
  | .sort u => .sort (u.inst ls)
  | .const c us => .const c (us.map (SLevel.inst ls))
  | .app fn arg => .app fn.instL arg.instL
  | .lam ty body => .lam ty.instL body.instL
  | .forallE ty body => .forallE ty.instL body.instL

theorem ClosedN.instL : ∀ {e}, ClosedN e k → ClosedN (e.instL ls) k
  | .bvar .., h | .sort .., h | .const .., h => h
  | .app .., h | .lam .., h | .forallE .., h => ⟨h.1.instL, h.2.instL⟩

def mk : VExpr → SExpr
  | .bvar i => .bvar i
  | .sort u => .sort (.mk u)
  | .const c us => .const c (us.map .mk)
  | .app fn arg => .app (.mk fn) (.mk arg)
  | .lam ty body => .lam (.mk ty) (.mk body)
  | .forallE ty body => .forallE (.mk ty) (.mk body)

/-- Choose a well-formed syntactic representative of a semantic expression. -/
noncomputable def reify : SExpr → VExpr
  | .bvar i => .bvar i
  | .sort u => .sort u.reify
  | .const c us => .const c (us.map SLevel.reify)
  | .app fn arg => .app fn.reify arg.reify
  | .lam ty body => .lam ty.reify body.reify
  | .forallE ty body => .forallE ty.reify body.reify

@[simp] theorem mk_reify : ∀ e : SExpr, mk e.reify = e
  | .bvar _ => rfl
  | .sort _ => by simp [reify, mk]
  | .const c us => by
    simp only [reify, mk, List.map_map]
    congr 1
    exact List.map_id''' us fun u _ => SLevel.mk_reify u
  | .app f a => by simp [reify, mk, mk_reify f, mk_reify a]
  | .lam A e => by simp [reify, mk, mk_reify A, mk_reify e]
  | .forallE A B => by simp [reify, mk, mk_reify A, mk_reify B]

theorem reify_levelWF : ∀ e : SExpr, e.reify.LevelWF univs
  | .bvar _ => trivial
  | .sort u => u.reify_wf
  | .const _ us => by
    intro l hl
    simp only [List.mem_map] at hl
    obtain ⟨u, _, rfl⟩ := hl
    exact u.reify_wf
  | .app f a => ⟨reify_levelWF f, reify_levelWF a⟩
  | .lam A e => ⟨reify_levelWF A, reify_levelWF e⟩
  | .forallE A B => ⟨reify_levelWF A, reify_levelWF B⟩

/-- `mk` is conservative on well-formed expressions modulo the source
theory's universe-level equivalence. -/
theorem _root_.Lean4Lean.VEnv.EqUpToLevels.of_mk_eq
    {e e' : VExpr} (he : e.LevelWF univs) (he' : e'.LevelWF univs)
    (h : SExpr.mk e = SExpr.mk e') : VEnv.EqUpToLevels univs e e' := by
  induction e generalizing e' with
  | bvar i =>
    cases e' with
    | bvar j => cases h; exact .bvar
    | sort | const | app | lam | forallE => cases h
  | sort l =>
    cases e' with
    | sort l' =>
      injection h with hl
      exact .sort he he' (SLevel.equiv_of_mk_eq he he' hl)
    | bvar | const | app | lam | forallE => cases h
  | const c ls =>
    cases e' with
    | const c' ls' =>
      injection h with hc hls
      subst c'
      exact .const he he' (SLevel.forall₂_equiv_of_map_mk_eq he he' hls)
    | bvar | sort | app | lam | forallE => cases h
  | app f a ihf iha =>
    cases e' with
    | app f' a' =>
      injection h with hf ha
      exact .app (ihf he.1 he'.1 hf) (iha he.2 he'.2 ha)
    | bvar | sort | const | lam | forallE => cases h
  | lam A e ihA ihe =>
    cases e' with
    | lam A' e' =>
      injection h with hA heq
      exact .lam (ihA he.1 he'.1 hA) (ihe he.2 he'.2 heq)
    | bvar | sort | const | app | forallE => cases h
  | forallE A B ihA ihB =>
    cases e' with
    | forallE A' B' =>
      injection h with hA hB
      exact .forallE (ihA he.1 he'.1 hA) (ihB he.2 he'.2 hB)
    | bvar | sort | const | app | lam => cases h

theorem _root_.Lean4Lean.VEnv.EqUpToLevels.reify_mk
    {e : VExpr} (he : e.LevelWF univs) :
    VEnv.EqUpToLevels univs e (SExpr.reify (SExpr.mk e)) :=
  .of_mk_eq he (SExpr.reify_levelWF (SExpr.mk e)) (SExpr.mk_reify _).symm

/-- Translate an expression while instantiating its universe parameters. -/
def mkInst (ls : List SLevel) : VExpr → SExpr
  | .bvar i => .bvar i
  | .sort u => .sort (.instV ls u)
  | .const c us => .const c (us.map (.instV ls))
  | .app fn arg => .app (mkInst ls fn) (mkInst ls arg)
  | .lam ty body => .lam (mkInst ls ty) (mkInst ls body)
  | .forallE ty body => .forallE (mkInst ls ty) (mkInst ls body)

@[simp] theorem mkInst_lift' : mkInst ls (e.lift' ρ) = (mkInst ls e).lift' ρ := by
  induction e generalizing ρ <;> simp [VExpr.lift', mkInst, *]

theorem _root_.Lean4Lean.VExpr.ClosedN.mkInstS : ∀ {e : VExpr},
    e.ClosedN k → (mkInst ls e).ClosedN k
  | .bvar .., h | .sort .., h | .const .., h => h
  | .app .., h | .lam .., h | .forallE .., h => ⟨h.1.mkInstS, h.2.mkInstS⟩

theorem mkInst_map_mk (hls : ∀ u ∈ ls, u.WF univs) :
    mkInst (ls.map SLevel.mk) e = mk (e.instL ls) := by
  induction e with
  | bvar => rfl
  | sort u => exact congrArg SExpr.sort (SLevel.instV_map_mk hls)
  | const c us =>
    simp only [mkInst, VExpr.instL, mk, List.map_map]
    congr 1
    apply List.map_congr_left
    intro u hu
    exact SLevel.instV_map_mk hls
  | app f a ihf iha | lam f a ihf iha | forallE f a ihf iha =>
    simp only [mkInst, VExpr.instL, mk]
    rw [ihf, iha]

@[simp] theorem mk_lift' : ∀ {e : VExpr}, mk (e.lift' ρ) = (mk e).lift' ρ
  | .bvar .. | .sort .. | .const .. => rfl
  | .app .. | .lam .. | .forallE .. => by simp [VExpr.lift', mk, mk_lift']

@[simp] theorem mk_lift {e : VExpr} : mk e.lift = (mk e).lift := by
  rw [VExpr.lift_eq_lift']
  exact mk_lift'

theorem mk_instL {e : VExpr} {ls : List VLevel}
    (he : e.LevelWF univs) (hls : ∀ u ∈ ls, u.WF univs) :
    mk (e.instL ls) = (mk e).instL (ls.map SLevel.mk) := by
  induction e with
  | bvar => rfl
  | app f a ihf iha | lam f a ihf iha | forallE f a ihf iha =>
    simp [VExpr.LevelWF] at he
    simp only [VExpr.instL, SExpr.mk, SExpr.instL]
    rw [ihf he.1, iha he.2]
  | sort u =>
    simp only [VExpr.instL, SExpr.mk, SExpr.instL]
    exact congrArg SExpr.sort (SLevel.mk_inst he hls)
  | const c us =>
    simp [VExpr.LevelWF] at he
    simp only [VExpr.instL, mk, instL, List.map_map]
    congr 1
    apply List.map_congr_left
    intro u hu
    exact SLevel.mk_inst (he u hu) hls

theorem _root_.Lean4Lean.VExpr.ClosedN.mkS : ∀ {e : VExpr}, e.ClosedN k → ClosedN (.mk e) k
  | .bvar .., h | .sort .., h | .const .., h => h
  | .app .., h | .lam .., h | .forallE .., h => ⟨h.1.mkS, h.2.mkS⟩

@[reducible] def Subst := Nat → SExpr

def Subst.Depth (σ : Subst) (n n' : Nat) := ∀ i, σ (i + n') = .bvar (i + n)

def Subst.Fixes (σ : Subst) (n : Nat) := ∀ i < n, σ i = .bvar i

theorem Subst.Fixes.zero : Fixes σ 0 := nofun

theorem Subst.Depth.add {σ : Subst} (H : σ.Depth n n') : σ.Depth (n + k) (n' + k) :=
  fun i => cast (by congr 2 <;> omega) <| H (k + i)

def Subst.lift (σ : Subst) : Subst
  | 0 => .bvar 0
  | i+1 => (σ i).lift

theorem Subst.Depth.lift {σ : Subst} (H : σ.Depth n n') : σ.lift.Depth (n + 1) (n' + 1) :=
  fun i => by simp [Subst.lift, H i]; rfl

theorem Subst.Fixes.lift {σ : Subst} (H : σ.Fixes n) : σ.lift.Fixes (n + 1) := fun
  | 0, _ => rfl
  | n+1, h => by simp [Subst.lift, H _ (Nat.lt_of_succ_lt_succ h)]

def Subst.id : Subst := .bvar
def Subst.head (σ : Subst) : SExpr := σ 0
def Subst.tail (σ : Subst) : Subst := fun n => σ (n+1)

theorem Subst.Depth.id : Subst.id.Depth 0 0 := fun _ => rfl
theorem Subst.Depth.tail {σ : Subst} (H : σ.Depth n (n' + 1)) : σ.tail.Depth n n' := H

def Subst.cons (σ : Subst) (e : SExpr) : Subst
  | 0 => e
  | i+1 => σ i

theorem Subst.Depth.cons {σ : Subst} (H : σ.Depth n n') : (σ.cons e).Depth n (n' + 1) := H

abbrev Subst.one (e : SExpr) : Subst := .cons .id e

theorem Subst.Depth.one : (Subst.one e).Depth 0 1 := .id

def Subst.trunc (σ : Subst) (n n' : Nat) : Subst :=
  fun i => if n' ≤ i then .bvar (i - n' + n) else σ i

theorem Subst.Depth.trunc {σ : Subst} : (σ.trunc n n').Depth n n' := by
  intro i; simp [Subst.trunc]

def _root_.Lean4Lean.Lift.invS : Lift → Subst
  | .refl => .id
  | .skip ρ => ρ.invS.cons default
  | .cons ρ => ρ.invS.lift

theorem Subst.Depth.invS : ∀ (ρ : Lift), ρ.invS.Depth ρ.dom ρ.size
  | .refl => .id
  | .skip l => (invS l).cons
  | .cons l => (invS l).lift

@[simp] theorem Subst.head_cons : (cons σ e).head = e := rfl
@[simp] theorem Subst.tail_cons : (cons σ e).tail = σ := rfl

def Subst.lift_r (σ : Subst) (ρ : Lift) : Subst := fun x => (σ x).lift' ρ
def Subst.lift_l (ρ : Lift) (σ : Subst) : Subst := fun x => σ (ρ.liftVar x)

theorem Subst.tail_eq_lift_l {σ : Subst} : σ.tail = σ.lift_l Lift.refl.skip := rfl

theorem Subst.lift_l_lift {σ : Subst} {ρ} : (σ.lift_l ρ).lift = σ.lift.lift_l ρ.cons := by
  funext i; cases i <;> simp! [lift_l]

theorem Subst.lift_r_lift {σ : Subst} {ρ} : (σ.lift_r ρ).lift = σ.lift.lift_r ρ.cons := by
  funext i; cases i <;> simp! [lift_r, ← lift'_comp]

theorem lift_l_inv {ρ : Lift} : .lift_l ρ ρ.invS = Subst.id := by
  funext i; simp [Subst.lift_l, Subst.id]
  induction ρ generalizing i with
  | refl => rfl
  | skip ρ ih => simp [Lift.invS, Subst.cons, ih]
  | cons ρ ih => cases i <;> simp [Lift.invS, Subst.lift, ih]

@[simp] theorem instL_lift' : (lift' e ρ).instL ls = lift' (e.instL ls) ρ := by
  cases e <;> simp [lift', instL, instL_lift']

def _root_.Lean4Lean.Lift.toSubst (ρ : Lift) : Subst := .lift_l ρ .id

theorem _root_.Lean4Lean.Lift.toSubst_apply (ρ : Lift) (i) : ρ.toSubst i = bvar (ρ.liftVar i) := rfl

theorem Subst.Depth.toSubst (ρ : Lift) : ρ.toSubst.Depth ρ.size ρ.dom := by
  intro i; simp [Lift.toSubst_apply]
  induction ρ <;> simp! [*] <;> omega

def subst : SExpr → Subst → SExpr
  | .bvar i, σ => σ i
  | .sort u, _ => .sort u
  | .const c us, _ => .const c us
  | .app fn arg, σ => .app (fn.subst σ) (arg.subst σ)
  | .lam ty body, σ => .lam (ty.subst σ) (body.subst σ.lift)
  | .forallE ty body, σ => .forallE (ty.subst σ) (body.subst σ.lift)

def mkSubst (σ : VExpr.Subst) : Subst := fun i => mk (σ i)

@[simp] theorem mkSubst_lift : mkSubst σ.lift = (mkSubst σ).lift := by
  funext i
  cases i with
  | zero => rfl
  | succ i => exact mk_lift

@[simp] theorem mk_subst : mk (e.subst σ) = (mk e).subst (mkSubst σ) := by
  induction e generalizing σ with
  | bvar => rfl
  | sort | const => rfl
  | app f a ihf iha => simp only [VExpr.subst, mk, subst, ihf, iha]
  | lam A e ihA ihe | forallE A e ihA ihe =>
    simp only [VExpr.subst, mk, subst, ihA, ihe, mkSubst_lift]

@[simp] theorem id_lift : Subst.id.lift = Subst.id := by funext i; cases i <;> rfl

@[simp] theorem subst_id {e : SExpr} : e.subst .id = e := by
  induction e <;> simp! [*]; rfl

theorem subst_lift' {e : SExpr} : (e.lift' ρ).subst σ = subst e (.lift_l ρ σ) := by
  induction e generalizing ρ σ <;> simp! [*, Subst.lift_l_lift]; rfl

theorem lift'_subst {e : SExpr} : (e.subst σ).lift' ρ = subst e (.lift_r σ ρ) := by
  induction e generalizing ρ σ <;> simp! [*, Subst.lift_r, Subst.lift_r_lift]

theorem lift'_inj {e e' : SExpr} {ρ : Lift} : e.lift' ρ = e'.lift' ρ ↔ e = e' :=
  ⟨(by simpa [subst_lift', lift_l_inv] using congrArg (·.subst ρ.invS) ·), (· ▸ rfl)⟩

theorem subst_toSubst {e : SExpr} : subst e ρ.toSubst = lift' e ρ := by
  simp [Lift.toSubst, ← subst_lift']

theorem subst_lift'_inv {e : SExpr} {ρ : Lift} : (e.lift' ρ).subst ρ.invS = e := by
  rw [subst_lift', lift_l_inv, subst_id]

nonrec def Subst.instL (ls : List SLevel) (σ : Subst) : Subst := instL ls ∘ σ

theorem Subst.instL_lift {σ : Subst} : (σ.instL ls).lift = σ.lift.instL ls := by
  funext i; obtain _|i := i <;> simp [Subst.instL, lift, SExpr.instL]

@[simp] theorem instL_subst : (subst e σ).instL ls = subst (e.instL ls) (σ.instL ls) := by
  cases e <;> simp [subst, instL, instL_subst, Subst.instL_lift] <;> simp [Subst.instL]

def Subst.comp (σ σ' : Subst) : Subst := fun x => (σ x).subst σ'

theorem Subst.comp_lift {σ σ' : Subst} : (σ.comp σ').lift = σ.lift.comp σ'.lift := by
  funext i; cases i <;> simp! [comp, SExpr.lift]
  rw [SExpr.lift, SExpr.lift, lift'_subst, subst_lift']; rfl

theorem subst_subst {e : SExpr} : (e.subst σ).subst σ' = subst e (.comp σ σ') := by
  induction e generalizing σ σ' <;> simp! [*, Subst.comp, Subst.comp_lift]

theorem lift_subst {e : SExpr} : e.lift.subst σ = e.subst σ.tail := by
  rw [lift, subst_lift', ← Subst.tail_eq_lift_l]

theorem lift_subst_cons {e : SExpr} : e.lift.subst (σ.cons t) = e.subst σ := by
  rw [lift_subst, Subst.tail_cons]

theorem Subst.lift_l_eq : Subst.lift_l ρ σ = Subst.comp ρ.toSubst σ := by
  funext; simp [lift_l, comp, Lift.toSubst_apply, SExpr.subst]

theorem Subst.lift_r_eq : Subst.lift_r σ ρ = Subst.comp σ ρ.toSubst := by
  funext i; simp [lift_r, comp, subst_toSubst]

theorem Subst.Depth.comp {σ σ' : Subst}
    (H : σ.Depth n₁ n₂) (H2 : σ'.Depth n₂ n₃) : (σ'.comp σ).Depth n₁ n₃ := by
  intro i; simp [Subst.comp, subst, H2 i, H i]

theorem Subst.Depth.lift_l {σ : Subst}
    (H : σ.Depth n ρ.size) : (Subst.lift_l ρ σ).Depth n ρ.dom := by
  rw [lift_l_eq]; exact .comp H (.toSubst _)

theorem Subst.Depth.lift_r {σ : Subst}
    (H : σ.Depth ρ.dom n) : (Subst.lift_r σ ρ).Depth ρ.size n := by
  rw [lift_r_eq]; exact .comp (.toSubst _) H

theorem ClosedN.subst_eq {e : SExpr} (self : ClosedN e k) (h : σ.Fixes k) : e.subst σ = e := by
  induction e generalizing k σ with (simp [ClosedN] at self; simp [*, SExpr.subst])
  | bvar i => exact h _ self
  | app _ _ ih1 ih2 => exact ⟨ih1 self.1 h, ih2 self.2 h⟩
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 => exact ⟨ih1 self.1 h, ih2 self.2 h.lift⟩

def inst (e a : SExpr) : SExpr := e.subst (.one a)

@[simp] theorem mkSubst_one : mkSubst (VExpr.Subst.one a) = Subst.one (mk a) := by
  funext i
  cases i <;> rfl

@[simp] theorem mk_instExpr : mk (e.inst a) = (mk e).inst (mk a) := by
  rw [VExpr.inst_eq, inst, mk_subst, mkSubst_one]

def Skips (e : SExpr) (ρ : Lift) : Prop := lift' (e.subst ρ.invS) ρ = e

theorem Skips.lift (e : SExpr) (ρ : Lift) : Skips (e.lift' ρ) ρ := by
  rw [Skips, subst_lift'_inv]

def Skips' : SExpr → (ρ : Lift) → Prop
  | .bvar i, ρ => ∃ j, ρ.liftVar j = i
  | .sort .., _ | .const .., _ => True
  | .app fn arg, ρ => fn.Skips' ρ ∧ arg.Skips' ρ
  | .lam ty body, ρ => ty.Skips' ρ ∧ body.Skips' ρ.cons
  | .forallE ty body, ρ => ty.Skips' ρ ∧ body.Skips' ρ.cons

theorem skips_iff {e : SExpr} {ρ : Lift} : Skips e ρ ↔ Skips' e ρ := by
  simp [Skips]; induction e generalizing ρ with simp!
  | app _ _ ih1 ih2 => exact and_congr ih1 ih2
  | lam _ _ ih1 ih2 | forallE _ _ ih1 ih2 => exact and_congr ih1 (@ih2 ρ.cons)
  | bvar i =>
    constructor <;> [intro h; intro ⟨j, h⟩]
    · refine (?_ : have := (match ρ.invS i with | SExpr.bvar .. => True | _ => True); _); split
      · rename_i eq; cases eq ▸ h; exact ⟨_, rfl⟩
      · suffices ρ.invS i = default by cases this ▸ h
        clear h; rename_i h
        induction ρ generalizing i <;> simp [Lift.invS, Subst.id] at * <;>
          cases i <;> simp [Subst.cons, Subst.lift] at *
        case skip.succ ih i => exact ih _ h
        case cons.succ ih i => rw [ih i fun j h' => h _ (by rw [h']; rfl)]; rfl
    · refine .trans (?_ : _ = (bvar j).lift' ρ) (congrArg bvar h); congr 1
      rw [← h]; exact congrFun (@lift_l_inv _ ρ) j

theorem skips_inter {e : SExpr} : Skips e (ρ.inter ρ') ↔ Skips e ρ ∧ Skips e ρ' := by
  simp [skips_iff]
  induction e generalizing ρ ρ' with simp_all!
  | app => grind
  | lam _ _ _ ih2 | forallE _ _ _ ih2 => have := @ih2 ρ.cons ρ'.cons; grind [Lift.inter]
  | bvar =>
    constructor
    · rintro ⟨j, rfl⟩; constructor
      · rw [Lift.inter_comm, ← Lift.diff_comp]; exact ⟨_, Lift.liftVar_comp.symm⟩
      · rw [← Lift.diff_comp]; exact ⟨_, Lift.liftVar_comp.symm⟩
    · rintro ⟨⟨i, h⟩, ⟨j, rfl⟩⟩
      induction ρ generalizing i j ρ' with
      | refl => simp [Lift.inter]
      | skip ρ ih =>
        cases ρ' with
        | refl => simp [Lift.inter]; cases h; exact ⟨_, rfl⟩
        | skip => simp_all [Lift.inter]; exact ih _ _ h
        | cons => cases j <;> simp_all [Lift.inter, Lift.liftVar]; exact ih _ _ h
      | cons ρ ih =>
        cases i <;> simp_all [Lift.liftVar]
        · cases ρ' with
          | refl => simp [Lift.inter]; cases h; exact ⟨0, rfl⟩
          | skip => let 0 := j; simp_all
          | cons => let 0 := j; exact ⟨0, rfl⟩
        · cases ρ' with
          | refl => cases h; exact ⟨_+1, rfl⟩
          | skip => simp_all [Lift.liftVar, Lift.inter]; exact ih _ _ h
          | cons =>
            let _+1 := j; simp_all [Lift.inter]
            have ⟨_, h⟩ := ih _ _ h; exact ⟨_+1, congrArg (·+1) h⟩

theorem lift_r_inj {σ σ' : Subst} : σ.lift_r ρ = σ'.lift_r ρ ↔ σ = σ' := by
  refine ⟨fun h => funext fun i => ?_, (· ▸ rfl)⟩
  simpa [Subst.lift_r, lift'_inj] using congrFun h i

theorem Subst.lift_r_comm (σ : Subst) (ρ : Lift) (H : Subst.Depth σ 0 n) :
    σ.lift_r ρ = .lift_l (ρ.consN n) ((σ.lift_r ρ).trunc 0 n) := by
  funext i; simp [Subst.lift_l, Subst.lift_r, Subst.trunc]
  have : (ρ.consN n).liftVar i = if n ≤ i then ρ.liftVar (i-n) + n else i := by
    clear H; induction n generalizing i <;> [skip; cases i] <;> simp! [*]; split <;> rfl
  rw [this]; split <;> simp
  have := H (i - n); rw [Nat.sub_add_cancel ‹_›] at this; simp [this]

theorem lift_r_one (e : SExpr) (ρ : Lift) :
    (Subst.one e).lift_r ρ = .lift_l ρ.cons (Subst.one (e.lift' ρ)) := by
  refine (Subst.lift_r_comm (Subst.one e) ρ .one).trans ?_; congr 1
  funext i; simp [Subst.trunc]
  cases i <;> simp [Subst.one, Subst.cons, Subst.lift_r, Subst.id]

theorem lift_inst (e : SExpr) : e.lift.inst e' = e := by
  rw [inst, Subst.one, lift, subst_lift', ← Subst.tail_eq_lift_l, Subst.tail_cons, subst_id]

theorem lift'_inst_hi (e1 e2 : SExpr) (ρ : Lift) :
    lift' (e1.inst e2) ρ = (lift' e1 ρ.cons).inst (lift' e2 ρ) := by
  simp [inst, subst_lift', lift'_subst, lift_r_one]

theorem subst_inst {e : SExpr} : (e.inst a).subst σ = (e.subst σ.lift).inst (a.subst σ) := by
  rw [SExpr.inst, SExpr.inst, subst_subst, subst_subst]; congr 1
  funext i; obtain _|i := i <;> simp [Subst.comp, Subst.lift, SExpr.subst]
  · simp [Subst.one, Subst.cons]
  · rw [← SExpr.inst, lift_inst]; rfl

theorem inst_lift_cons {e : SExpr} {σ : Subst} :
    (e.subst σ.lift).inst x = e.subst (σ.cons x) := by
  rw [SExpr.inst, subst_subst, Subst.one]; congr 1
  funext i; obtain _|i := i <;>
    simp [Subst.comp, Subst.lift, SExpr.subst, Subst.cons, lift_subst_cons]

inductive Ctx.Lift' : Lift → List SExpr → List SExpr → Prop where
  | refl : Ctx.Lift' .refl Γ Γ
  | skip : Ctx.Lift' l Γ Γ' → Ctx.Lift' (.skip l) Γ (A :: Γ')
  | cons : Ctx.Lift' l Γ Γ' → Ctx.Lift' (.cons l) (A::Γ) (A.lift' l :: Γ')

theorem Ctx.Lift'.one : Ctx.Lift' (.skip .refl) Γ (A::Γ) := .skip .refl

theorem Ctx.Lift'.comp (H1 : Ctx.Lift' l Γ₀ Γ₁) (H2 : Ctx.Lift' l' Γ₁ Γ₂) : Ctx.Lift' (l.comp l') Γ₀ Γ₂ := by
  induction H2 generalizing l Γ₀ with
  | refl => exact H1
  | skip _ ih => exact (ih H1).skip
  | cons H2 ih =>
    cases H1 with
    | refl => exact .cons H2
    | skip H1 => exact .skip (ih H1)
    | cons H1 => exact SExpr.lift'_comp ▸ .cons (ih H1)

inductive Ctx.Inter : List SExpr → List SExpr → Lift → List SExpr → Lift → List SExpr → Prop where
  | refl_l : Ctx.Lift' ρ Γ Δ → Ctx.Inter Γ Δ .refl Γ ρ Δ
  | refl_r : Ctx.Lift' ρ Γ Δ → Ctx.Inter Γ Γ ρ Δ .refl Δ
  | skip_skip : Ctx.Inter Γ Γ₁ ρ₁ Γ₂ ρ₂ Δ → Ctx.Inter Γ Γ₁ (.skip ρ₁) Γ₂ (.skip ρ₂) (A::Δ)
  | skip_cons : Ctx.Inter Γ Γ₁ ρ₁ Γ₂ ρ₂ Δ →
    Ctx.Inter Γ Γ₁ (.skip ρ₁) (A :: Γ₂) (.cons ρ₂) (A.lift' ρ₂ :: Δ)
  | cons_skip : Ctx.Inter Γ Γ₁ ρ₁ Γ₂ ρ₂ Δ →
    Ctx.Inter Γ (A :: Γ₁) (.cons ρ₁) Γ₂ (.skip ρ₂) (A.lift' ρ₁ :: Δ)
  | cons_cons : Ctx.Inter Γ Γ₁ ρ₁ Γ₂ ρ₂ Δ →
    Ctx.Inter (A :: Γ) (A.lift' (ρ₂.diff ρ₁) :: Γ₁) (.cons ρ₁)
      (A.lift' (ρ₁.diff ρ₂) :: Γ₂) (.cons ρ₂) (A.lift' (ρ₁.inter ρ₂) :: Δ)

theorem lift_eq_lift {e₁ e₂ : SExpr} (H : e₁.lift' ρ₁ = e₂.lift' ρ₂) :
    ∃ e, .lift' e (ρ₂.diff ρ₁) = e₁ ∧ e.lift' (ρ₁.diff ρ₂) = e₂ := by
  have := Skips.lift e₁ ρ₁
  have h1 : _ = _ := skips_inter.2 ⟨.lift e₁ ρ₁, H ▸ Skips.lift e₂ ρ₂⟩
  have h2 := h1; conv at h1 => enter [1,2]; rw [← Lift.diff_comp]
  conv at h2 => enter [1,2]; rw [Lift.inter_comm, ← Lift.diff_comp]
  rw [lift'_comp] at h1 h2
  exact ⟨_, lift'_inj.1 h2, lift'_inj.1 (h1.trans H)⟩

theorem Ctx.Inter.mk (H1 : Ctx.Lift' l₁ Γ₁ Δ) (H2 : Ctx.Lift' l₂ Γ₂ Δ) :
    ∃ Γ, Ctx.Inter Γ Γ₁ l₁ Γ₂ l₂ Δ := by
  induction H1 generalizing l₂ Γ₂ with
  | refl => exact ⟨_, .refl_l H2⟩
  | skip H1 ih =>
    cases H2 with
    | refl => exact ⟨_, .refl_r (.skip H1)⟩
    | skip H2 => let ⟨_, H⟩ := ih H2; exact ⟨_, .skip_skip H⟩
    | cons H2 => let ⟨_, H⟩ := ih H2; exact ⟨_, .skip_cons H⟩
  | @cons l₁ _ _ A₁ H1 ih =>
    generalize eq : A₁.lift' l₁ = A' at H2
    cases H2 with
    | refl => subst eq; exact ⟨_, .refl_r (.cons H1)⟩
    | skip H2 => subst eq; let ⟨_, H⟩ := ih H2; exact ⟨_, .cons_skip H⟩
    | @cons l₂ _ _ A₂ H2 =>
      obtain ⟨_, rfl, rfl⟩ := lift_eq_lift eq
      rw [← lift'_comp, Lift.diff_comp]
      let ⟨_, H⟩ := ih H2; exact ⟨_, .cons_cons H⟩

theorem Ctx.Inter.symm (H : Ctx.Inter Γ Γ₁ l₁ Γ₂ l₂ Δ) : Ctx.Inter Γ Γ₂ l₂ Γ₁ l₁ Δ := by
  induction H with
  | refl_l h => exact .refl_r h
  | refl_r h => exact .refl_l h
  | skip_skip _ ih => exact .skip_skip ih
  | skip_cons _ ih => exact .cons_skip ih
  | cons_skip _ ih => exact .skip_cons ih
  | cons_cons _ ih => rw [Lift.inter_comm]; exact .cons_cons ih

theorem Ctx.Inter.diff (H : Ctx.Inter Γ Γ₁ l₁ Γ₂ l₂ Δ) : Ctx.Lift' (l₁.diff l₂) Γ Γ₂ := by
  induction H with
  | refl_l h => exact .refl
  | refl_r h => simpa
  | skip_skip _ ih | cons_skip _ ih => exact ih
  | skip_cons _ ih => exact ih.skip
  | cons_cons _ ih => exact ih.cons

theorem Ctx.Inter.right (H : Ctx.Inter Γ Γ₁ l₁ Γ₂ l₂ Δ) : Ctx.Lift' l₂ Γ₂ Δ := by
  induction H with
  | refl_l h => exact h
  | refl_r h => exact .refl
  | skip_skip _ ih => exact ih.skip
  | cons_skip _ ih => exact ih.skip
  | skip_cons _ ih => exact ih.cons
  | cons_cons _ ih => rw [← Lift.diff_comp, SExpr.lift'_comp]; exact ih.cons

theorem Ctx.Inter.left (H : Ctx.Inter Γ Γ₁ l₁ Γ₂ l₂ Δ) : Ctx.Lift' l₁ Γ₁ Δ := H.symm.right

inductive _root_.Lean4Lean.Pattern.MatchesS :
    (p : Pattern) → SExpr → List SLevel → (p.Path → SExpr) → Prop
  | const : MatchesS (.const c) (.const c ls) ls nofun
  | var : MatchesS f f' f1 g1 → MatchesS (.var f) (.app f' a') f1 (·.elim a' g1)
  | app : MatchesS f f' f1 g1 → MatchesS a a' f2 g2 →
    MatchesS (.app f a) (.app f' a') f1 (Sum.elim g1 g2)

/-- A constant application spine is matched by the corresponding `varN`
pattern.  This is the SExpr-side constructor used when a logical-relation
head witness exposes a recursor or constructor spine. -/
theorem _root_.Lean4Lean.Pattern.varN_const_matchesS
    (c : Name) (ls : List SLevel) (args : List SExpr) :
    ∃ m2, (Pattern.varN (.const c) args.length).MatchesS
      (args.foldr (fun a f => f.app a) (.const c ls)) ls m2 := by
  induction args with
  | nil =>
    refine ⟨nofun, ?_⟩
    refine cast ?_ (Pattern.MatchesS.const (c := c) (ls := ls))
    simp only [List.length_nil, Pattern.varN, List.foldr_nil]
    congr 1
    funext path
    exact Empty.elim path
  | cons a args ih =>
    obtain ⟨m2, hm⟩ := ih
    refine ⟨fun path => Option.elim path a m2, ?_⟩
    simpa only [List.length_cons, Pattern.varN, List.foldr_cons] using hm.var

/-- Exact syntactic match for the simple recursor/iota pattern once both
constant-headed spines and their arities are known. -/
theorem _root_.Lean4Lean.RecursorIotaPattern.matchesS_spines
    {r c : Name} {rls cls : List SLevel} {rargs cargs : List SExpr}
    {major ctorArity : Nat}
    (hr : rargs.length = major) (hc : cargs.length = ctorArity) :
    ∃ m2, (RecursorIotaPattern r major c ctorArity).MatchesS
      (.app (rargs.foldr (fun a f => f.app a) (.const r rls))
        (cargs.foldr (fun a f => f.app a) (.const c cls))) rls m2 := by
  obtain ⟨mr, hmr⟩ := Pattern.varN_const_matchesS r rls rargs
  obtain ⟨mc, hmc⟩ := Pattern.varN_const_matchesS c cls cargs
  subst major
  subst ctorArity
  exact ⟨Sum.elim mr mc, hmr.app hmc⟩

/-- Invert a `varN` match headed by a constant into the exact application
spine it inspected.  Besides the arity equation, retain the capture map and
its original match proof so dependent consumers do not have to reconstruct
either one from list indexing. -/
theorem _root_.Lean4Lean.Pattern.MatchesS.varN_const_inv
    (H : (Pattern.varN (.const c) arity).MatchesS e ls mcap) :
    ∃ (args : List SExpr),
      args.length = arity ∧
      e = args.foldr (fun a f => f.app a) (.const c ls) ∧
      (Pattern.varN (.const c) arity).MatchesS
        (args.foldr (fun a f => f.app a) (.const c ls)) ls mcap := by
  induction arity generalizing e with
  | zero =>
    simp only [Pattern.varN] at H ⊢
    cases H
    exact ⟨[], rfl, rfl, .const⟩
  | succ arity ih =>
    simp only [Pattern.varN] at H ⊢
    cases H with
    | @var f f' f1 g1 a' h =>
      obtain ⟨args, hlen, rfl, hmatch⟩ := ih h
      exact ⟨a' :: args, congrArg Nat.succ hlen, rfl, hmatch.var⟩

/-- Exact decomposition of a semantic iota match.  In particular this
recovers the constructor universe levels, which are not stored in the
match's `m1` index, and separates the recursor and constructor capture maps.
Generated-rule soundness must validate those recovered levels against its
rule certificate before constructing a contraction. -/
theorem _root_.Lean4Lean.Pattern.MatchesS.iota_inv
    {rec ctor : Name} {major arity : Nat} {e : SExpr}
    {recLs : List SLevel}
    {mcap : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
    (H : (RecursorIotaPattern rec major ctor arity).MatchesS e recLs mcap) :
    ∃ (recArgs ctorArgs : List SExpr) (ctorLs : List SLevel)
        (mrec : (Pattern.varN (.const rec) major).Path → SExpr)
        (mctor : (Pattern.varN (.const ctor) arity).Path → SExpr),
      recArgs.length = major ∧ ctorArgs.length = arity ∧
      e = (recArgs.foldr (fun (a f : SExpr) => f.app a) (SExpr.const rec recLs)).app
        (ctorArgs.foldr (fun (a f : SExpr) => f.app a) (SExpr.const ctor ctorLs)) ∧
      mcap = Sum.elim mrec mctor ∧
      (Pattern.varN (.const rec) major).MatchesS
        (recArgs.foldr (fun (a f : SExpr) => f.app a) (SExpr.const rec recLs)) recLs mrec ∧
      (Pattern.varN (.const ctor) arity).MatchesS
        (ctorArgs.foldr (fun (a f : SExpr) => f.app a) (SExpr.const ctor ctorLs)) ctorLs mctor := by
  cases H with
  | @app fPat recHead recLevels recCap ctorPat ctorHead ctorLevels ctorCap
      hrec hctor =>
    obtain ⟨recArgs, hrecLen, rfl, hrec'⟩ := hrec.varN_const_inv
    obtain ⟨ctorArgs, hctorLen, rfl, hctor'⟩ := hctor.varN_const_inv
    exact ⟨recArgs, ctorArgs, ctorLevels, recCap, ctorCap,
      hrecLen, hctorLen, rfl, rfl, hrec', hctor'⟩

/-- A successful syntactic match remembers the constant-headed application
spine that it inspected. Arguments are stored in reverse application order,
matching the representation used by the shape interpretation. -/
theorem _root_.Lean4Lean.Pattern.MatchesS.head_spine (H : p.MatchesS e ls m) :
    ∃ (c : Name) (ls' : List SLevel) (args : List SExpr),
      e = args.foldr (fun a f => f.app a) (.const c ls') ∧
      Arity (.const c) args.length p := by
  induction H with
  | const => exact ⟨_, _, [], rfl, .refl⟩
  | @var f f' f1 g1 a' h ih =>
    obtain ⟨c, ls, args, heq, har⟩ := ih
    refine ⟨c, ls, a' :: args, ?_, .var har⟩
    simp only [List.foldr_cons]
    rw [← heq]
  | @app f f' f1 g1 a a' f2 g2 hf ha ihf iha =>
    obtain ⟨c, ls, args, heq, har⟩ := ihf
    refine ⟨c, ls, a' :: args, ?_, .app har⟩
    simp only [List.foldr_cons]
    rw [← heq]

theorem _root_.Lean4Lean.Pattern.matchesS_inter {p q : Pattern} {e : SExpr} :
    (∃ m1 m2, p.MatchesS e m1 m2) ∧ (∃ m1 m2, q.MatchesS e m1 m2) ↔
    (∃ r m1 m2, p.inter q = some r ∧ r.MatchesS e m1 m2) := by
  constructor
  · rintro ⟨⟨m1, m2, hp⟩, ⟨m3, m4, hq⟩⟩
    induction hp generalizing q m3 <;> cases hq <;> simp [Pattern.inter]
    · case const.const => exact ⟨_, _, .const⟩
    · case var.var ih _ _ ih' =>
      have ⟨rf, mf1, mf2, hf1, hf2⟩ := ih _ _ ih'
      exact ⟨_, ⟨_, hf1, rfl⟩, _, _, .var hf2⟩
    · case var.app ihf _ _ _ _ _ ha2 ihf' =>
      have ⟨rf, mf1, mf2, hf1, hf2⟩ := ihf _ _ ihf'
      exact ⟨_, ⟨_, hf1, rfl⟩, _, _, .app hf2 ha2⟩
    · case app.var ha2 ihf _ _ _ ihf' =>
      have ⟨rf, mf1, mf2, hf1, hf2⟩ := ihf _ _ ihf'
      exact ⟨_, ⟨_, hf1, rfl⟩, _, _, .app hf2 ha2⟩
    · case app.app ihf iha _ _ _ _ _ iha' ihf' =>
      have ⟨rf, mf1, mf2, hf1, hf2⟩ := ihf _ _ ihf'
      have ⟨ra, ma1, ma2, ha1, ha2⟩ := iha _ _ iha'
      exact ⟨_, ⟨_, hf1, _, ha1, rfl⟩, _, _, .app hf2 ha2⟩
  · rintro ⟨r, m1, m2, h1, h2⟩
    induction p generalizing q e r m1 <;> cases q <;> simp [Pattern.inter] at h1 <;> [
        obtain ⟨rfl, rfl⟩ := h1; obtain ⟨_, wf, _, wa, rfl⟩ := h1;
        obtain ⟨_, wf, rfl⟩ := h1; obtain ⟨_, wf, rfl⟩ := h1; obtain ⟨_, wf, rfl⟩ := h1
      ] <;> cases h2
    · exact ⟨⟨_, _, .const⟩, ⟨_, _, .const⟩⟩
    · next ihf iha _ _ _ _ _ _ _ _ _ ha hf =>
      have ⟨⟨mf1, mf2, hf⟩, ⟨mf1', mf2', hf'⟩⟩ := ihf _ _ _ wf hf
      have ⟨⟨ma1, ma2, ha⟩, ⟨ma1', ma2', ha'⟩⟩ := iha _ _ _ wa ha
      exact ⟨⟨_, _, .app hf ha⟩, ⟨_, _, .app hf' ha'⟩⟩
    · next ihf _ _ _ _ _ _ _ _ ha hf =>
      have ⟨⟨mf1, mf2, hf⟩, ⟨mf1', mf2', hf'⟩⟩ := ihf _ _ _ wf hf
      exact ⟨⟨_, _, .app hf ha⟩, ⟨_, _, .var hf'⟩⟩
    · next ihf _ _ _ _ _ _ _ _ ha' hf =>
      have ⟨⟨mf1, mf2, hf⟩, ⟨mf1', mf2', hf'⟩⟩ := ihf _ _ _ wf hf
      exact ⟨⟨_, _, .var hf⟩, ⟨_, _, .app hf' ha'⟩⟩
    · next ihf _ _ _ _ _ hf =>
      have ⟨⟨mf1, mf2, hf⟩, ⟨mf1', mf2', hf'⟩⟩ := ihf _ _ _ wf hf
      exact ⟨⟨_, _, .var hf⟩, ⟨_, _, .var hf'⟩⟩

theorem _root_.Lean4Lean.Pattern.MatchesS.determ
    (h1 : Pattern.MatchesS p e m1 m2) (h2 : Pattern.MatchesS p e m1' m2') :
    m1 = m1' ∧ m2 = m2' := by
  induction h1 generalizing m1' with
  | const => let .const := h2; simp
  | app l1 l2 ih1 ih2 => let .app r1 r2 := h2; simp [ih1 r1, ih2 r2]
  | var l1 ih1 => let .var r1 := h2; simp [ih1 r1]

/-- Reify a semantic match into an exact syntactic match. -/
theorem _root_.Lean4Lean.Pattern.MatchesS.reify
    (H : Pattern.MatchesS p e m1 m2) :
    Pattern.Matches p e.reify (m1.map SLevel.reify)
      fun path => (m2 path).reify := by
  induction H with
  | @const c ls =>
    refine cast ?_ (Pattern.Matches.const
      (c := c) (ls := ls.map SLevel.reify))
    simp only [SExpr.reify]
    congr 1
    funext path
    exact Empty.elim path
  | @var f f' f1 g1 a' _ ih =>
    change Pattern.Matches (.var f) (.app f'.reify a'.reify)
      (f1.map SLevel.reify) fun path => (Option.elim path a' g1).reify
    have heq : (fun path => (Option.elim path a' g1).reify) =
        (fun path => Option.elim path a'.reify fun path => (g1 path).reify) := by
      funext path
      cases path <;> rfl
    rw [heq]
    exact ih.var
  | @app f f' f1 g1 a a' f2 g2 _ _ ihf iha =>
    change Pattern.Matches (.app f a) (.app f'.reify a'.reify)
      (f1.map SLevel.reify) fun path => (Sum.elim g1 g2 path).reify
    have heq : (fun path => (Sum.elim g1 g2 path).reify) =
        Sum.elim (fun path => (g1 path).reify)
          (fun path => (g2 path).reify) := by
      funext path
      cases path <;> rfl
    rw [heq]
    exact ihf.app iha

def _root_.Lean4Lean.Pattern.RHS.applyS {p : Pattern}
    (m1 : List SLevel) (m2 : p.Path → SExpr) : p.RHS → SExpr
  | .fixed c _ => .mkInst m1 c
  | .var path => m2 path
  | .app f a => .app (f.applyS m1 m2) (a.applyS m1 m2)

/-- Applying a left-associated RHS application tower is the corresponding
left fold of the instantiated template arguments. -/
theorem _root_.Lean4Lean.Pattern.RHS.appN_applyS {p : Pattern}
    (f : p.RHS) (as : List p.RHS) (m1 : List SLevel)
    (m2 : p.Path → SExpr) :
    (Pattern.RHS.appN f as).applyS m1 m2 =
      as.foldl (fun acc a => acc.app (a.applyS m1 m2))
        (f.applyS m1 m2) := by
  induction as generalizing f with
  | nil => rfl
  | cons a as ih =>
    simpa only [Pattern.RHS.appN, Pattern.RHS.applyS,
      List.foldl_cons] using ih (.app f a)

/-- Expose the last application in an RHS application tower. -/
theorem _root_.Lean4Lean.Pattern.RHS.appN_append_singleton {p : Pattern}
    (f a : p.RHS) (as : List p.RHS) :
    Pattern.RHS.appN f (as ++ [a]) = .app (Pattern.RHS.appN f as) a := by
  induction as generalizing f with
  | nil => rfl
  | cons b as ih =>
    simpa only [List.cons_append, Pattern.RHS.appN] using ih (.app f b)

/-- Reification commutes with applying a pattern RHS, up to the semantic
quotient map. -/
theorem _root_.Lean4Lean.Pattern.RHS.mk_apply_reify {p : Pattern}
    (r : p.RHS) (m1 : List SLevel) (m2 : p.Path → SExpr) :
    SExpr.mk (r.apply (m1.map SLevel.reify) fun path => (m2 path).reify) =
      r.applyS m1 m2 := by
  induction r with
  | fixed e closed =>
    simp only [Pattern.RHS.apply, Pattern.RHS.applyS]
    rw [← SExpr.mkInst_map_mk
      (ls := m1.map SLevel.reify) (e := e)
      (by
        intro l hl
        simp only [List.mem_map] at hl
        obtain ⟨u, _, rfl⟩ := hl
        exact u.reify_wf)]
    congr 1
    rw [List.map_map]
    apply List.map_id'''
    intro u _
    exact SLevel.mk_reify u
  | var path => exact SExpr.mk_reify (m2 path)
  | app f a ihf iha =>
    simp only [Pattern.RHS.apply, Pattern.RHS.applyS, SExpr.mk]
    rw [ihf, iha]

def _root_.Lean4Lean.Pattern.RHS.Closed {p : Pattern} : p.RHS → Prop
  | .fixed c _ => c.Closed
  | .var _ => True
  | .app f a => f.Closed ∧ a.Closed

def _root_.Lean4Lean.Pattern.RHS.Closed.applyS {p : Pattern} {m1 m2} :
    ∀ r : p.RHS, r.Closed → (∀ a, (m2 a).ClosedN k) → (r.applyS m1 m2).ClosedN k
  | .fixed .., h1, _ => h1.mkInstS.mono (Nat.zero_le _)
  | .var _, _, h2 => h2 _
  | .app .., h1, h2 => ⟨h1.1.applyS _ h2, h1.2.applyS _ h2⟩

def _root_.Lean4Lean.Pattern.Check.defeqsS {p : Pattern}
    (m1 : List SLevel) (m2 : p.Path → SExpr) : p.Check → List (SExpr × SExpr)
  | .true => []
  | .defeq a b rest => (a.applyS m1 m2, b.applyS m1 m2) :: rest.defeqsS m1 m2

theorem _root_.Lean4Lean.Pattern.MatchesS.lift'
    (H : Pattern.MatchesS p e m1 m2) :
    Pattern.MatchesS p (e.lift' ρ) m1 fun path => (m2 path).lift' ρ := by
  induction H with
  | @const c ls =>
    refine cast ?_ (Pattern.MatchesS.const (c := c) (ls := ls))
    simp only [SExpr.lift']
    congr 1
    funext path
    exact Empty.elim path
  | @var f f' f1 g1 a' _ ih =>
    change Pattern.MatchesS (.var f) (.app (f'.lift' ρ) (a'.lift' ρ)) f1
      (fun path => (Option.elim path a' g1).lift' ρ)
    have heq : (fun path => (Option.elim path a' g1).lift' ρ) =
        (fun path => Option.elim path (a'.lift' ρ) fun path => (g1 path).lift' ρ) := by
      funext path
      cases path <;> rfl
    rw [heq]
    exact ih.var
  | @app f f' f1 g1 a a' f2 g2 _ _ ih1 ih2 =>
    change Pattern.MatchesS (.app f a) (.app (f'.lift' ρ) (a'.lift' ρ)) f1
      (fun path => (Sum.elim g1 g2 path).lift' ρ)
    have heq : (fun path => (Sum.elim g1 g2 path).lift' ρ) =
        Sum.elim (fun path => (g1 path).lift' ρ) (fun path => (g2 path).lift' ρ) := by
      funext path
      cases path <;> rfl
    rw [heq]
    exact ih1.app ih2

theorem _root_.Lean4Lean.Pattern.RHS.lift'_applyS {p : Pattern}
    (r : p.RHS) (m1 : List SLevel) (m2 : p.Path → SExpr) :
    (r.applyS m1 m2).lift' ρ = r.applyS m1 fun path => (m2 path).lift' ρ := by
  induction r with
  | fixed e cl => exact (cl.mkInstS.lift'_eq .zero)
  | var => rfl
  | app _ _ ih1 ih2 =>
    simp only [Pattern.RHS.applyS, SExpr.lift']
    rw [ih1, ih2]

theorem _root_.Lean4Lean.Pattern.Check.defeqsS_lift' {p : Pattern}
    (ck : p.Check) (m1 : List SLevel) (m2 : p.Path → SExpr) :
    (ck.defeqsS m1 m2).map (fun ab => (ab.1.lift' ρ, ab.2.lift' ρ)) =
      ck.defeqsS m1 fun path => (m2 path).lift' ρ := by
  induction ck with
  | true => rfl
  | defeq a b rest ih =>
    simp only [Pattern.Check.defeqsS, List.map_cons, ih]
    rw [a.lift'_applyS, b.lift'_applyS]

theorem _root_.Lean4Lean.Pattern.matchesS_lift' {p : Pattern} {e : SExpr} {m1 m2'} :
    p.MatchesS (e.lift' ρ) m1 m2' ↔
    ∃ m2, p.MatchesS e m1 m2 ∧ ∀ path, m2' path = (m2 path).lift' ρ := by
  constructor
  · intro h
    generalize eq : e.lift' ρ = e' at h
    induction h generalizing e with
    | const => cases e <;> cases eq; exact ⟨_, .const, nofun⟩
    | var _ ih =>
      cases e <;> cases eq
      have ⟨_, hmatch, hpath⟩ := ih rfl
      refine ⟨_, .var hmatch, ?_⟩
      intro path
      cases path <;> simp_all
    | app _ _ ihf iha =>
      cases e <;> cases eq
      have ⟨_, hf, hfp⟩ := ihf rfl
      have ⟨_, ha, hap⟩ := iha rfl
      refine ⟨_, .app hf ha, ?_⟩
      intro path
      cases path <;> simp_all
  · rintro ⟨m2, hmatch, hpath⟩
    induction hmatch with
    | const => exact (show m2' = _ by ext path; exact Empty.elim path) ▸ .const
    | @var f f' f1 g1 a' _ ih =>
      have h := ih (hpath <| some ·)
      have heq : m2' = fun path => Option.elim path (a'.lift' ρ) fun path => m2' (some path) := by
        funext path
        cases path <;> simp [hpath]
      rw [heq]
      exact h.var
    | app _ _ ihf iha =>
      have h := (ihf (hpath <| .inl ·)).app (iha (hpath <| .inr ·))
      refine cast ?_ h
      congr 1
      funext path
      cases path <;> rfl

theorem _root_.Lean4Lean.Pattern.MatchesS.subst
    (H : Pattern.MatchesS p e m1 m2) :
    Pattern.MatchesS p (e.subst σ) m1 fun path => (m2 path).subst σ := by
  induction H with
  | @const c ls =>
    refine cast ?_ (Pattern.MatchesS.const (c := c) (ls := ls))
    simp only [SExpr.subst]
    congr 1
    funext path
    exact Empty.elim path
  | @var f f' f1 g1 a' _ ih =>
    change Pattern.MatchesS (.var f) (.app (f'.subst σ) (a'.subst σ)) f1
      (fun path => (Option.elim path a' g1).subst σ)
    have heq : (fun path => (Option.elim path a' g1).subst σ) =
        (fun path => Option.elim path (a'.subst σ) fun path => (g1 path).subst σ) := by
      funext path
      cases path <;> rfl
    rw [heq]
    exact ih.var
  | @app f f' f1 g1 a a' f2 g2 _ _ ih1 ih2 =>
    change Pattern.MatchesS (.app f a) (.app (f'.subst σ) (a'.subst σ)) f1
      (fun path => (Sum.elim g1 g2 path).subst σ)
    have heq : (fun path => (Sum.elim g1 g2 path).subst σ) =
        Sum.elim (fun path => (g1 path).subst σ) (fun path => (g2 path).subst σ) := by
      funext path
      cases path <;> rfl
    rw [heq]
    exact ih1.app ih2

theorem _root_.Lean4Lean.Pattern.RHS.subst_applyS {p : Pattern}
    (r : p.RHS) (m1 : List SLevel) (m2 : p.Path → SExpr) :
    (r.applyS m1 m2).subst σ = r.applyS m1 fun path => (m2 path).subst σ := by
  induction r with
  | fixed e cl => exact cl.mkInstS.subst_eq .zero
  | var => rfl
  | app _ _ ih1 ih2 =>
    simp only [Pattern.RHS.applyS, SExpr.subst]
    rw [ih1, ih2]

theorem _root_.Lean4Lean.Pattern.Check.defeqsS_subst {p : Pattern}
    (ck : p.Check) (m1 : List SLevel) (m2 : p.Path → SExpr) :
    (ck.defeqsS m1 m2).map (fun ab => (ab.1.subst σ, ab.2.subst σ)) =
      ck.defeqsS m1 fun path => (m2 path).subst σ := by
  induction ck with
  | true => rfl
  | defeq a b rest ih =>
    simp only [Pattern.Check.defeqsS, List.map_cons, ih]
    rw [a.subst_applyS, b.subst_applyS]

section
set_option hygiene false

inductive Lookup : List SExpr → Nat → SExpr → Prop where
  | zero : Lookup (ty::Γ) 0 ty.lift
  | succ : Lookup Γ n ty → Lookup (A::Γ) (n+1) ty.lift

theorem Lookup.mkS (H : Lean4Lean.Lookup Γ i A) : Lookup (Γ.map mk) i (mk A) := by
  induction H with
  | zero => rw [mk_lift]; exact .zero
  | succ _ ih => rw [mk_lift]; exact .succ ih

theorem Lookup.weak' (W : Ctx.Lift' ρ Γ Γ') (H : Lookup Γ i A) :
    Lookup Γ' (ρ.liftVar i) (A.lift' ρ) := by
  induction W generalizing i A with
  | refl => simp; exact H
  | skip W ih => have' := (ih H).succ; rwa [SExpr.lift, ← SExpr.lift'_comp] at this
  | cons W ih =>
    cases H with
    | zero => refine' cast _ Lookup.zero; congr 1; simp [SExpr.lift, ← SExpr.lift'_comp]
    | succ H => refine' cast _ (ih H).succ; congr 1; simp [SExpr.lift, ← SExpr.lift'_comp]

theorem Lookup.weakU_inv (W : Ctx.Lift' ρ Γ Γ')
    (H : Lookup Γ' (ρ.liftVar i) A') : ∃ A, A' = A.lift' ρ ∧ Lookup Γ i A := by
  induction W generalizing i A' with
  | refl => simpa using H
  | @skip ρ W _ _ _ ih =>
    simp at H; let .succ H := H
    obtain ⟨_, rfl, h2⟩ := ih H; refine ⟨_, ?_, h2⟩
    rw [SExpr.lift, ← SExpr.lift'_comp]; rfl
  | @cons ρ Γ Δ B W ih =>
    cases i with
    | zero => cases H; exact ⟨_, by simp [SExpr.lift, ← SExpr.lift'_comp], .zero⟩
    | succ i =>
      let .succ (ty := C) H := H
      obtain ⟨C, rfl, h⟩ := ih H
      refine ⟨_, ?_, .succ h⟩
      simp [SExpr.lift, ← SExpr.lift'_comp]

theorem Lookup.weak'_inv (W : Ctx.Lift' ρ Γ Γ')
    (H : Lookup Γ' (ρ.liftVar i) (A.lift' ρ)) : Lookup Γ i A := by
  let ⟨_, h1, h2⟩ := H.weakU_inv W
  exact SExpr.lift'_inj.1 h1 ▸ h2

theorem Lookup.uniq (hA : Lookup Γ i A) (hB : Lookup Γ i B) : A = B :=
  match hA, hB with
  | .zero, .zero => rfl
  | .succ hA, .succ hB => Lookup.uniq hA hB ▸ rfl

theorem Lookup.determ (H1 : Lookup Γ i A) (H2 : Lookup Γ i A') : A = A' := by
  induction H1 generalizing A' with obtain _ | r1 := H2
  | zero => rfl
  | succ _ ih => cases ih r1; rfl

scoped notation:65 Γ " ⊢ " e " : " A:36 => IsDefEq Γ e e A
scoped notation:65 Γ " ⊢ " e1 " ≡ " e2 " : " A:36 => IsDefEq Γ e1 e2 A
inductive IsDefEq : List SExpr → SExpr → SExpr → SExpr → Prop where
  | bvar : Lookup Γ i A → Γ ⊢ .bvar i : A
  | symm : Γ ⊢ e ≡ e' : A → Γ ⊢ e' ≡ e : A
  | trans : Γ ⊢ e₁ ≡ e₂ : A → Γ ⊢ e₂ ≡ e₃ : A → Γ ⊢ e₁ ≡ e₃ : A
  | sort : Γ ⊢ .sort l : .sort (.succ l)
  | const : env.constants c = some ci → ls.length = ci.uvars →
    Γ ⊢ .const c ls : SExpr.mkInst ls ci.type
  | appDF : Γ ⊢ f ≡ f' : .forallE A B → Γ ⊢ a ≡ a' : A →
    Γ ⊢ .app f a ≡ .app f' a' : B.inst a
  | lamDF : Γ ⊢ A ≡ A' : .sort u → A::Γ ⊢ body ≡ body' : B →
    Γ ⊢ .lam A body ≡ .lam A' body' : .forallE A B
  | forallEDF : Γ ⊢ A ≡ A' : .sort u → A::Γ ⊢ body ≡ body' : .sort v →
    Γ ⊢ .forallE A body ≡ .forallE A' body' : .sort (.imax u v)
  | defeqDF : Γ ⊢ A ≡ B : .sort u → Γ ⊢ e1 ≡ e2 : A → Γ ⊢ e1 ≡ e2 : B
  | beta : A::Γ ⊢ e : B → Γ ⊢ e' : A → Γ ⊢ .app (.lam A e) e' ≡ e.inst e' : B.inst e'
  | eta : Γ ⊢ e : .forallE A B → Γ ⊢ .lam A (.app e.lift (.bvar 0)) ≡ e : .forallE A B
  | proofIrrel : Γ ⊢ p : .sort .zero → Γ ⊢ h : p → Γ ⊢ h' : p → Γ ⊢ h ≡ h' : p
  -- | extra : Pat p r → p.MatchesS e m1 m2 → (dfs : List _).map (·.2) = r.2.defeqsS m1 m2 →
  --   (∀ a b A, (A, a, b) ∈ dfs → Γ ⊢ a ≡ b : A) → Γ ⊢ e ≡ r.1.applyS m1 m2' : A
  | extra : env.defeqs df → ls.length = df.uvars →
    Γ ⊢ .mkInst ls df.lhs ≡ .mkInst ls df.rhs : .mkInst ls df.type

/-- The universe list of a constant at the head of `e` has the arity
registered for that constant. -/
def HeadConstLevelsWF (e : SExpr) : Prop :=
  ∀ {c ls ci}, e = .const c ls → Params.env.constants c = some ci →
    ls.length = ci.uvars

private theorem HeadConstLevelsWF.nonconst
    (h : ∀ {c ls}, e ≠ .const c ls) : HeadConstLevelsWF e := by
  intro c ls ci heq
  exact (h heq).elim

/-- Head-constant arity is preserved by term instantiation.  The only
nontrivial case is a substituted bound variable, whose result is the
instantiating argument itself. -/
theorem HeadConstLevelsWF.inst
    (he : HeadConstLevelsWF e) (ha : HeadConstLevelsWF a) :
    HeadConstLevelsWF (e.inst a) := by
  induction e with
  | bvar i =>
    cases i with
    | zero => exact ha
    | succ i =>
      refine HeadConstLevelsWF.nonconst ?_
      intro c ls heq
      change SExpr.bvar i = SExpr.const c ls at heq
      cases heq
  | const => exact he
  | sort | app | lam | forallE =>
    exact HeadConstLevelsWF.nonconst (by simp [SExpr.inst, SExpr.subst])

/-- A well-typed closed source expression instantiated into semantic levels
has a well-formed head constant. -/
private theorem HeadConstLevelsWF.mkInst_of_hasType
    (H : Params.env.HasType U [] e A) :
    HeadConstLevelsWF (SExpr.mkInst ls e) := by
  intro c levels ci heq hci
  cases e with
  | bvar | sort | app | lam | forallE => cases heq
  | const c' sourceLevels =>
    simp only [SExpr.mkInst] at heq
    injection heq with hc hlevels
    subst c'
    obtain ⟨ci', hci', _, hlen⟩ :=
      VEnv.HasType.const_inv Params.henv (by trivial) H
    have hciEq : ci' = ci := Option.some.inj (hci'.symm.trans hci)
    rw [← hciEq]
    rw [← hlen, ← hlevels, List.length_map]

/-- Both endpoints of a weak definitional equality have well-formed head
constant levels.  This survives beta substitution and raw registered
equations, the two cases not covered by a shallow constructor inversion. -/
theorem IsDefEq.headConstLevelsWF
    (H : IsDefEq Γ e₁ e₂ A) :
    HeadConstLevelsWF e₁ ∧ HeadConstLevelsWF e₂ := by
  induction H with
  | bvar =>
    exact ⟨HeadConstLevelsWF.nonconst (by simp),
      HeadConstLevelsWF.nonconst (by simp)⟩
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ⟨ih₁.1, ih₂.2⟩
  | sort =>
    exact ⟨HeadConstLevelsWF.nonconst (by simp),
      HeadConstLevelsWF.nonconst (by simp)⟩
  | const hreg hlen =>
    constructor <;> intro c' ls' ci' heq hreg'
    all_goals
      injection heq with hc hls
      subst c'; subst ls'
      have hciEq : _ = ci' := Option.some.inj (hreg.symm.trans hreg')
      simpa [hciEq] using hlen
  | appDF =>
    exact ⟨HeadConstLevelsWF.nonconst (by simp),
      HeadConstLevelsWF.nonconst (by simp)⟩
  | lamDF =>
    exact ⟨HeadConstLevelsWF.nonconst (by simp),
      HeadConstLevelsWF.nonconst (by simp)⟩
  | forallEDF =>
    exact ⟨HeadConstLevelsWF.nonconst (by simp),
      HeadConstLevelsWF.nonconst (by simp)⟩
  | defeqDF _ _ _ ih => exact ih
  | beta _ _ ihBody ihArg =>
    exact ⟨HeadConstLevelsWF.nonconst (by simp),
      HeadConstLevelsWF.inst ihBody.1 ihArg.1⟩
  | eta _ ih =>
    exact ⟨HeadConstLevelsWF.nonconst (by simp), ih.1⟩
  | proofIrrel _ _ _ _ ihLeft ihRight => exact ⟨ihLeft.1, ihRight.1⟩
  | extra hreg _ =>
    have hwf := Params.henv.defEqWF hreg
    exact ⟨HeadConstLevelsWF.mkInst_of_hasType hwf.1,
      HeadConstLevelsWF.mkInst_of_hasType hwf.2⟩

/-- Invert weak equality at a constant left endpoint to recover the exact
universe-list arity required by its registered declaration. -/
theorem IsDefEq.const_left_levelsLength
    (H : IsDefEq Γ (.const c ls) e A)
    (hci : Params.env.constants c = some ci) :
    ls.length = ci.uvars :=
  H.headConstLevelsWF.1 rfl hci

/-- Symmetric endpoint form of `const_left_levelsLength`. -/
theorem IsDefEq.const_right_levelsLength
    (H : IsDefEq Γ e (.const c ls) A)
    (hci : Params.env.constants c = some ci) :
    ls.length = ci.uvars :=
  H.headConstLevelsWF.2 rfl hci

/-- SExpr-side typing of an exact application spine.  Unlike a bare typing
of the final application, this retains the type of every argument at the
point where its surrounding pi is peeled.  Generated iota soundness needs
this evidence for the recursor, constructor, and captured-rule spines. -/
inductive SpineWF (Γ : List SExpr) : SExpr → List SExpr → SExpr → Prop where
  | nil : SpineWF Γ A [] A
  | cons :
    IsDefEq Γ e e A₁ →
    SpineWF Γ (A₂.inst e) es B →
    SpineWF Γ (.forallE A₁ A₂) (e :: es) B
  | conv :
    IsDefEq Γ A A' (.sort u) →
    SpineWF Γ A' es B →
    SpineWF Γ A es B
  | ret :
    SpineWF Γ A es B →
    IsDefEq Γ B B' (.sort u) →
    SpineWF Γ A es B'

/-- Concatenate conversion-aware spines without composing their result-type
conversions.  In the `ret` case the retained conversion is moved to the
head of the second spine.  This is the structural replacement for the old
heterogeneous `IsDefEq.trans'` rule: no equality between the two sort
indices is needed or assumed. -/
theorem SpineWF.append
    (H₁ : SpineWF Γ A es B) (H₂ : SpineWF Γ B fs C) :
    SpineWF Γ A (es ++ fs) C := by
  induction H₁ with
  | nil => simpa using H₂
  | cons harg _ ih => exact .cons harg (ih H₂)
  | conv hty _ ih => exact .conv hty (ih H₂)
  | ret _ hret ih => exact ih (.conv hret H₂)

/-- Extend a conversion-aware spine by its final argument. -/
theorem SpineWF.snoc
    (H : SpineWF Γ A es B)
    (hB : IsDefEq Γ B (.forallE D C) (.sort u))
    (he : IsDefEq Γ e e D) :
    SpineWF Γ A (es ++ [e]) (C.inst e) :=
  H.append (.conv hB (.cons he .nil))

/-- Two application spines with a common final Pi layer.  The explicit
codomain conversions are deliberately retained for both majors: they let a
consumer combine either recursor prefix with either endpoint of a related
major without appealing to global type uniqueness. -/
structure SpineWF.LastPair (Γ : List SExpr) (Head : SExpr)
    (xs ys : List SExpr) (x y A : SExpr) where
  prefixType : SExpr
  domain : SExpr
  codomain : SExpr
  piSort : SLevel
  resultSortX : SLevel
  resultSortY : SLevel
  prefixX : SpineWF Γ Head xs.reverse prefixType
  prefixY : SpineWF Γ Head ys.reverse prefixType
  pi : IsDefEq Γ prefixType (.forallE domain codomain) (.sort piSort)
  major : IsDefEq Γ x y domain
  resultX : IsDefEq Γ (codomain.inst x) A (.sort resultSortX)
  resultY : IsDefEq Γ (codomain.inst y) A (.sort resultSortY)

/-- Recover the complete left application spine. -/
theorem SpineWF.LastPair.fullX
    (H : SpineWF.LastPair Γ Head xs ys x y A) :
    SpineWF Γ Head (x :: xs).reverse A := by
  rw [List.reverse_cons]
  exact .ret (H.prefixX.snoc H.pi (H.major.trans H.major.symm)) H.resultX

/-- Recover the complete right application spine. -/
theorem SpineWF.LastPair.fullY
    (H : SpineWF.LastPair Γ Head xs ys x y A) :
    SpineWF Γ Head (y :: ys).reverse A := by
  rw [List.reverse_cons]
  exact .ret (H.prefixY.snoc H.pi (H.major.symm.trans H.major)) H.resultY

/-- Keep the major pair and use the left prefix at both endpoints. -/
def SpineWF.LastPair.leftPrefixes
    (H : SpineWF.LastPair Γ Head xs ys x y A) :
    SpineWF.LastPair Γ Head xs xs x y A :=
  { H with prefixY := H.prefixX }

/-- Keep the major pair and use the right prefix at both endpoints. -/
def SpineWF.LastPair.rightPrefixes
    (H : SpineWF.LastPair Γ Head xs ys x y A) :
    SpineWF.LastPair Γ Head ys ys x y A :=
  { H with prefixX := H.prefixY }

/-- Swap only the two recursor prefixes. -/
def SpineWF.LastPair.symmPrefixes
    (H : SpineWF.LastPair Γ Head xs ys x y A) :
    SpineWF.LastPair Γ Head ys xs x y A :=
  { H with prefixX := H.prefixY, prefixY := H.prefixX }

/-- Keep the prefixes and use the left major at both endpoints. -/
def SpineWF.LastPair.leftMajors
    (H : SpineWF.LastPair Γ Head xs ys x y A) :
    SpineWF.LastPair Γ Head xs ys x x A :=
  { H with
    major := H.major.trans H.major.symm
    resultSortY := H.resultSortX
    resultY := H.resultX }

/-- Keep the prefixes and use the right major at both endpoints. -/
def SpineWF.LastPair.rightMajors
    (H : SpineWF.LastPair Γ Head xs ys x y A) :
    SpineWF.LastPair Γ Head xs ys y y A :=
  { H with
    major := H.major.symm.trans H.major
    resultSortX := H.resultSortY
    resultX := H.resultY }

/-- Swap both prefixes and majors. -/
def SpineWF.LastPair.symm
    (H : SpineWF.LastPair Γ Head xs ys x y A) :
    SpineWF.LastPair Γ Head ys xs y x A :=
  { H with
    prefixX := H.prefixY
    prefixY := H.prefixX
    major := H.major.symm
    resultSortX := H.resultSortY
    resultSortY := H.resultSortX
    resultX := H.resultY
    resultY := H.resultX }

/-- Packaging of the final-application certificate for callers that keep
their accumulated spines as whole lists. -/
structure SpineWF.NonemptyLastPair (Γ : List SExpr) (Head : SExpr)
    (args args' : List SExpr) (A : SExpr) where
  x : SExpr
  xs : List SExpr
  y : SExpr
  ys : List SExpr
  args_eq : args = x :: xs
  args'_eq : args' = y :: ys
  pair : SpineWF.LastPair Γ Head xs ys x y A

/-- Apply a certified spine to a term typed at its head type. -/
theorem SpineWF.hasType
    (H : SpineWF Γ A es B) (hf : IsDefEq Γ f f A) :
    IsDefEq Γ (es.foldl (fun f a => f.app a) f)
      (es.foldl (fun f a => f.app a) f) B := by
  induction H generalizing f with
  | nil => exact hf
  | cons he _ ih =>
    simp only [List.foldl_cons]
    exact ih (.appDF hf he)
  | conv hty _ ih => exact ih (hty.defeqDF hf)
  | ret _ hty ih => exact hty.defeqDF (ih hf)

/-- Self-typing of the complete left application. -/
theorem SpineWF.LastPair.hasTypeX
    (H : SpineWF.LastPair Γ Head xs ys x y A)
    (hhead : IsDefEq Γ f f Head) :
    IsDefEq Γ ((x :: xs).foldr (fun a f => f.app a) f)
      ((x :: xs).foldr (fun a f => f.app a) f) A := by
  simpa only [List.foldl_reverse, List.foldr_cons] using H.fullX.hasType hhead

/-- Self-typing of the complete right application. -/
theorem SpineWF.LastPair.hasTypeY
    (H : SpineWF.LastPair Γ Head xs ys x y A)
    (hhead : IsDefEq Γ f f Head) :
    IsDefEq Γ ((y :: ys).foldr (fun a f => f.app a) f)
      ((y :: ys).foldr (fun a f => f.app a) f) A := by
  simpa only [List.foldl_reverse, List.foldr_cons] using H.fullY.hasType hhead

/-- Apply a certified spine congruently to both endpoints of a typed
equality.  This is the SExpr counterpart of Theory's `appN_congr`; retaining
the spine certificate avoids reconstructing the intermediate pi types. -/
theorem SpineWF.congr
    (H : SpineWF Γ A es B) (hf : IsDefEq Γ f f' A) :
    IsDefEq Γ (es.foldl (fun f a => f.app a) f)
      (es.foldl (fun f a => f.app a) f') B := by
  induction H generalizing f f' with
  | nil => exact hf
  | cons he _ ih =>
    simp only [List.foldl_cons]
    exact ih (.appDF hf he)
  | conv hty _ ih => exact ih (hty.defeqDF hf)
  | ret _ hty ih => exact hty.defeqDF (ih hf)

/-- A dependently typed pointwise equality between two application spines.
The recursive head is instantiated with the left argument, matching the
result type chosen by `IsDefEq.appDF`; the right endpoint is transported to
that same type by the equality stored at the current argument. -/
inductive SpineDefEq (Γ : List SExpr) :
    SExpr → List SExpr → List SExpr → SExpr → Prop where
  | nil : SpineDefEq Γ A [] [] A
  | cons :
    IsDefEq Γ e e' A₁ →
    SpineDefEq Γ (A₂.inst e) es es' B →
    SpineDefEq Γ (.forallE A₁ A₂) (e :: es) (e' :: es') B
  | conv :
    IsDefEq Γ A A' (.sort u) →
    SpineDefEq Γ A' es es' B →
    SpineDefEq Γ A es es' B
  | ret :
    SpineDefEq Γ A es es' B →
    IsDefEq Γ B B' (.sort u) →
    SpineDefEq Γ A es es' B'

/-- Concatenate pointwise spines while retaining successive result-type
conversions as separate certificates. -/
theorem SpineDefEq.append
    (H₁ : SpineDefEq Γ A es es' B) (H₂ : SpineDefEq Γ B fs fs' C) :
    SpineDefEq Γ A (es ++ fs) (es' ++ fs') C := by
  induction H₁ with
  | nil => simpa using H₂
  | cons harg _ ih => exact .cons harg (ih H₂)
  | conv hty _ ih => exact .conv hty (ih H₂)
  | ret _ hret ih => exact ih (.conv hret H₂)

/-- Extend a dependently typed pointwise spine by its final related
argument.  The conversion at the old result exposes the next Pi; the new
result is oriented at the left argument, exactly like `SpineDefEq.cons`. -/
theorem SpineDefEq.snoc
    (H : SpineDefEq Γ A es es' B)
    (hB : IsDefEq Γ B (.forallE D C) (.sort u))
    (he : IsDefEq Γ e e' D) :
    SpineDefEq Γ A (es ++ [e]) (es' ++ [e']) (C.inst e) :=
  H.append (.conv hB (.cons he .nil))

/-- A typed pointwise spine applies congruently to related heads. -/
theorem SpineDefEq.congr
    (H : SpineDefEq Γ A es es' B) (hf : IsDefEq Γ f f' A) :
    IsDefEq Γ (es.foldl (fun f a => f.app a) f)
      (es'.foldl (fun f a => f.app a) f') B := by
  induction H generalizing f f' with
  | nil => exact hf
  | cons he _ ih =>
    simp only [List.foldl_cons]
    exact ih (.appDF hf he)
  | conv hty _ ih => exact ih (hty.defeqDF hf)
  | ret _ hty ih => exact hty.defeqDF (ih hf)

/-- Forget the right endpoint of a pointwise spine equality. -/
theorem SpineDefEq.left
    (H : SpineDefEq Γ A es es' B) : SpineWF Γ A es B := by
  induction H with
  | nil => exact .nil
  | cons he _ ih => exact .cons (he.trans he.symm) ih
  | conv hty _ ih => exact .conv hty ih
  | ret _ hty ih => exact .ret ih hty

/-- Reflexive pointwise equality underlying a well-typed spine. -/
theorem SpineWF.toSpineDefEq
    (H : SpineWF Γ A es B) : SpineDefEq Γ A es es B := by
  induction H with
  | nil => exact .nil
  | cons he _ ih => exact .cons he ih
  | conv hty _ ih => exact .conv hty ih
  | ret _ hty ih => exact .ret ih hty

/-- A spine indexed by the keys that selected its arguments.  Besides
remembering order, the index fixes the exact domain type used at each
dependent application.  This is the alignment that a plain `List SExpr`
necessarily erases. -/
inductive PathSpineWF (Γ : List SExpr) {α : Type}
    (value type : α → SExpr) : SExpr → List α → SExpr → Prop where
  | nil : PathSpineWF Γ value type A [] A
  | cons :
    IsDefEq Γ (type path) A₁ (.sort u) →
    PathSpineWF Γ value type (A₂.inst (value path)) paths B →
    PathSpineWF Γ value type (.forallE A₁ A₂) (path :: paths) B
  | conv :
    IsDefEq Γ A A' (.sort u) →
    PathSpineWF Γ value type A' paths B →
    PathSpineWF Γ value type A paths B
  | ret :
    PathSpineWF Γ value type A paths B →
    IsDefEq Γ B B' (.sort u) →
    PathSpineWF Γ value type A paths B'

/-- Erase path indices after supplying the exact self-typing attached to
each selected argument. -/
theorem PathSpineWF.toSpineWF
    (H : PathSpineWF Γ value type A paths B)
    (htyped : ∀ path, IsDefEq Γ (value path) (value path) (type path)) :
    SpineWF Γ A (paths.map value) B := by
  induction H with
  | nil => exact .nil
  | cons hdom _ ih =>
    simp only [List.map_cons]
    exact .cons (hdom.defeqDF (htyped _)) ih
  | conv hty _ ih => exact .conv hty ih
  | ret _ hty ih => exact .ret ih hty

/-- Retain the path-indexed dependent spine while replacing each selected
capture by a related endpoint.  The recursive codomain is instantiated with
the left capture, exactly as in `SpineDefEq.cons`; consequently no type
uniqueness or reconstruction from the right spine is needed. -/
theorem PathSpineWF.toSpineDefEq
    (H : PathSpineWF Γ value type A paths B)
    (hvalue : ∀ path, IsDefEq Γ (value path) (value' path) (type path)) :
    SpineDefEq Γ A (paths.map value) (paths.map value') B := by
  induction H with
  | nil => exact .nil
  | cons hdom _ ih =>
    simp only [List.map_cons]
    exact .cons (hdom.defeqDF (hvalue _)) ih
  | conv hty _ ih => exact .conv hty ih
  | ret _ hty ih => exact .ret ih hty

/-- Concrete capture typings supplied to a generated reduction site.  Two
sites can share the same `type` map while carrying endpoint-specific
self-typings, which is precisely what dependent RHS congruence needs. -/
structure _root_.Lean4Lean.Pattern.CaptureTyping
    (Γ : List SExpr) {p : Pattern} (capture : p.Path → SExpr)
    (type : p.Path → SExpr) : Prop where
  typed : ∀ path, IsDefEq Γ (capture path) (capture path) (type path)

/-- Typed syntax retained at one concrete iota site before its generated
tower is selected.  Recursor arguments are in newest-first semantic order,
so the typing spine reverses them and appends the major premise. -/
structure _root_.Lean4Lean.Pattern.IotaTyping
    (Γ : List SExpr) (rec ctor : Name)
    (recLs ctorLs : List SLevel) (recArgs ctorArgs : List SExpr)
    (majorTerm A : SExpr) where
  recHeadType : SExpr
  ctorHeadType : SExpr
  ctorResultType : SExpr
  majorType : SExpr
  recHead : IsDefEq Γ (.const rec recLs) (.const rec recLs) recHeadType
  recSpine : SpineWF Γ recHeadType
    (recArgs.reverse ++ [majorTerm]) A
  ctorHead : IsDefEq Γ (.const ctor ctorLs) (.const ctor ctorLs) ctorHeadType
  ctorSpine : SpineWF Γ ctorHeadType ctorArgs.reverse ctorResultType
  majorEq : IsDefEq Γ majorTerm
    (ctorArgs.foldr (fun (a f : SExpr) => f.app a) (SExpr.const ctor ctorLs)) majorType

/-- The concrete registered tower selected by one iota-pattern payload.
This rule descriptor is independent of a particular match, so the two
endpoints of a logical-relation comparison share the same tower and the same
ordered capture paths by construction. -/
structure _root_.Lean4Lean.Pattern.IotaRule
    {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    (r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check) where
  pat : Params.Pat (RecursorIotaPattern rec major ctor arity) r
  df : VDefEq
  registered : Params.env.defeqs df
  rhsClosed : df.rhs.Closed
  capturePaths : List (RecursorIotaPattern rec major ctor arity).Path
  rhsTower : r.1 = Pattern.RHS.appN (.fixed df.rhs rhsClosed)
    (capturePaths.map fun path => .var path)

/-- The syntax computed by a rule descriptor is its registered right tower
applied to the descriptor's ordered concrete captures. -/
theorem _root_.Lean4Lean.Pattern.IotaRule.rhsApply
    {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (rule : Pattern.IotaRule r) (recLs : List SLevel)
    (mcap : (RecursorIotaPattern rec major ctor arity).Path → SExpr) :
    (rule.capturePaths.map mcap).foldl
        (fun (f a : SExpr) => f.app a) (SExpr.mkInst recLs rule.df.rhs) =
      r.1.applyS recLs mcap := by
  rw [rule.rhsTower, Pattern.RHS.appN_applyS]
  simp only [Pattern.RHS.applyS, List.foldl_map]

/-- Evidence-rich generated reduction site.  Unlike the former direct
`iotaAction` hook, this records the registered lambda tower, the exact typed
capture application used to instantiate it, and the local beta collapse to
the matched redex.  The final `Pattern.Action` is derived below. -/
structure _root_.Lean4Lean.Pattern.IotaReductionSite
    (Γ : List SExpr) {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    (r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check)
    (rule : Pattern.IotaRule r)
    (recLs ctorLs : List SLevel) (recArgs ctorArgs : List SExpr)
    (majorTerm A : SExpr)
    (mcap : (RecursorIotaPattern rec major ctor arity).Path → SExpr)
    (captureType : (RecursorIotaPattern rec major ctor arity).Path → SExpr)
    (captureTyping : Pattern.CaptureTyping Γ mcap captureType) where
  typing : Pattern.IotaTyping Γ rec ctor recLs ctorLs recArgs ctorArgs majorTerm A
  matched : (RecursorIotaPattern rec major ctor arity).MatchesS
    ((recArgs.foldr (fun (a f : SExpr) => f.app a) (SExpr.const rec recLs)).app
      (ctorArgs.foldr (fun (a f : SExpr) => f.app a) (SExpr.const ctor ctorLs))) recLs mcap
  levelsLength : recLs.length = rule.df.uvars
  captureSpine : PathSpineWF Γ mcap captureType
    (SExpr.mkInst recLs rule.df.type) rule.capturePaths A
  lhsCollapse : IsDefEq Γ
    ((recArgs.foldr (fun (a f : SExpr) => f.app a) (SExpr.const rec recLs)).app
      (ctorArgs.foldr (fun (a f : SExpr) => f.app a) (SExpr.const ctor ctorLs)))
    ((rule.capturePaths.map mcap).foldl
      (fun (f a : SExpr) => f.app a) (SExpr.mkInst recLs rule.df.lhs)) A
  dfs : List (SExpr × SExpr × SExpr)
  defeqs : dfs.map (·.2) = r.2.defeqsS recLs mcap
  checked : ∀ a b B, (B, a, b) ∈ dfs → IsDefEq Γ a b B

/-- The finite evidence attached to one concrete pattern contraction.

Pattern membership is only combinatorial. An `Action` additionally records
the exact matched redex and captures, the finite list of checked equalities,
and the local equality to the instantiated RHS. It deliberately does not
contain endpoint typings: consumers of the action must retain those at the
typing/reduction layer where they are known. -/
structure _root_.Lean4Lean.Pattern.Action (Gamma : List SExpr) {p : Pattern}
    (r : p.RHS × p.Check) (e : SExpr) (m1 : List SLevel)
    (m2 : p.Path → SExpr) (A : SExpr) where
  pat : Pat p r
  matched : p.MatchesS e m1 m2
  dfs : List (SExpr × SExpr × SExpr)
  defeqs : dfs.map (·.2) = r.2.defeqsS m1 m2
  checked : ∀ a b B, (B, a, b) ∈ dfs → IsDefEq Gamma a b B
  sound : IsDefEq Gamma e (r.1.applyS m1 m2) A

/-- Semantic closure required to translate the live registered structure-eta
rule.  This is a bridge obligation, not an axiom: L4L-16 constructs it from
the checked `VEnv.WF` history before exposing sort inversion. -/
def Params.StructureEtaSound : Prop :=
  ∀ {rule : VStructEta} {levels : List VLevel} {Γ params : List VExpr}
    {major : VExpr},
    env.structEtas rule →
    IsDefEq (Γ.map mk)
      (mk (rule.rebuild levels params major))
      (mk (rule.rebuild levels params major))
      (mk (rule.structureType levels params)) →
    IsDefEq (Γ.map mk) (mk major) (mk major)
      (mk (rule.structureType levels params)) →
    IsDefEq (Γ.map mk) (mk (rule.rebuild levels params major)) (mk major)
      (mk (rule.structureType levels params))

/-- Translate the main typing judgment into the semantically quotiented syntax. -/
theorem IsDefEq.mkS (hstruct : Params.StructureEtaSound)
    (H : Params.env.IsDefEq Params.univs Γ e₁ e₂ A) :
    OnCtx Γ (fun _ A => A.LevelWF Params.univs) →
    IsDefEq (Γ.map mk) (mk e₁) (mk e₂) (mk A) := by
  intro hΓ
  induction H using VEnv.IsDefEq.rec
      (motive_2 := fun _ _ _ _ _ => True) with
  | bvar h => exact .bvar (SExpr.Lookup.mkS h)
  | symm _ ih => exact .symm (ih hΓ)
  | trans _ _ ih₁ ih₂ => exact .trans (ih₁ hΓ) (ih₂ hΓ)
  | @sortDF l l' Γ hl hl' h =>
    change IsDefEq _ (.sort (SLevel.mk _)) (.sort (SLevel.mk _)) (.sort (SLevel.mk _))
    have hu := SLevel.mk_eq hl hl' h
    have hus : SLevel.mk l.succ = (SLevel.mk l').succ := by rw [SLevel.mk_succ hl, hu]
    rw [hu, hus]
    exact .sort
  | @constDF c ci ls ls' Γ h₁ h₂ h₃ h₄ h₅ =>
    change IsDefEq _ (.const c (ls.map SLevel.mk)) (.const c (ls'.map SLevel.mk))
      (mk (ci.type.instL ls))
    rw [← SLevel.map_mk_eq h₂ h₃ h₅, ← mkInst_map_mk h₂]
    exact IsDefEq.const (ls := ls.map SLevel.mk) h₁ (by simpa using h₄)
  | appDF _ _ ihf iha => simpa only [mk, mk_instExpr] using IsDefEq.appDF (ihf hΓ) (iha hΓ)
  | lamDF hA _ ihA ihb =>
    have hAwf := (hA.levelWF hΓ).1
    exact .lamDF (ihA hΓ) (ihb ⟨hΓ, hAwf⟩)
  | forallEDF hA hb ihA ihb =>
    have hAwf := (hA.levelWF hΓ).1
    have hu := (hA.levelWF hΓ).2.2
    have hv := (hb.levelWF ⟨hΓ, hAwf⟩).2.2
    simpa only [mk, SLevel.mk_imax hu hv] using IsDefEq.forallEDF (ihA hΓ) (ihb ⟨hΓ, hAwf⟩)
  | defeqDF _ _ ihA ihe => exact .defeqDF (ihA hΓ) (ihe hΓ)
  | beta _ he' ihe ihe' =>
    have hAwf := (he'.levelWF hΓ).2.2
    simpa only [mk, mk_instExpr] using IsDefEq.beta (ihe ⟨hΓ, hAwf⟩) (ihe' hΓ)
  | eta _ ih => simpa only [mk, mk_lift] using IsDefEq.eta (ih hΓ)
  | structEta hreg _ _ _ _ _ _ _ ihMajor ihRebuild =>
    exact hstruct hreg (ihRebuild hΓ) (ihMajor hΓ)
  | proofIrrel _ _ _ ihp ihh ihh' => exact .proofIrrel (ihp hΓ) (ihh hΓ) (ihh' hΓ)
  | @extra df ls Γ h₁ h₂ h₃ =>
    simpa only [mkInst_map_mk h₂] using
      (IsDefEq.extra (Γ := Γ.map mk) (ls := ls.map SLevel.mk) h₁ (by simpa using h₃))
  | nil => trivial
  | cons => trivial

/-- Translate a Theory application-spine certificate without erasing its
per-argument typings.  This is the bridge needed by a live generated-iota
reduction site; the endpoint-only translation is intentionally insufficient.
-/
theorem _root_.Lean4Lean.VEnv.SpineWF.mkS
    (hstruct : Params.StructureEtaSound)
    (H : Params.env.SpineWF Params.univs Γ A es B)
    (hΓ : OnCtx Γ (fun _ A => A.LevelWF Params.univs)) :
    SExpr.SpineWF (Γ.map SExpr.mk) (SExpr.mk A)
      (es.map SExpr.mk) (SExpr.mk B) := by
  exact VEnv.SpineWF.rec
    (motive_1 := fun _ _ _ _ _ => True)
    (motive_2 := fun Γ A es B _ =>
      OnCtx Γ (fun _ A => A.LevelWF Params.univs) →
      SExpr.SpineWF (Γ.map SExpr.mk) (SExpr.mk A)
        (es.map SExpr.mk) (SExpr.mk B))
    (bvar := by simp) (symm := by simp) (trans := by simp)
    (sortDF := by simp) (constDF := by simp) (appDF := by simp)
    (lamDF := by simp) (forallEDF := by simp) (defeqDF := by simp)
    (beta := by simp) (eta := by simp) (structEta := by simp)
    (proofIrrel := by simp) (extra := by simp)
    (nil := fun {_Γ _A} _hΓ => .nil)
    (cons := fun {_Γ _e _A₁ _es _B _A₂} he _ _ ih hΓ => by
      exact .cons (SExpr.IsDefEq.mkS hstruct he hΓ) (by
        simpa only [SExpr.mk_instExpr] using ih hΓ))
    H hΓ

def CtorBundle.IsCtor (c : Name) : Prop :=
  ∃ cl, Params.classify c = some cl ∧ cl matches .ctor .. | .etaCtor ..

def CtorBundle.IsCtor.cl (H : CtorBundle.IsCtor c) :
    {cl // Params.classify c = some cl ∧ cl matches .ctor .. | .etaCtor ..} := by
  dsimp [CtorBundle.IsCtor] at H
  match Params.classify c, H with
  | some cl, H => refine ⟨cl, ?_⟩; obtain ⟨_, ⟨⟩, H⟩ := H; exact ⟨rfl, H⟩

structure CtorBundle (c : Name) (cl : CtorBundle.IsCtor c) : Type where
  I : Name
  Ts : List SExpr
  args : List SExpr
  u : SLevel
  hlen : Ts.length = cl.cl.1.arity
  hclI : Params.classify I = some (.indTy args.length)
  hu0 : u ≠ .zero

def CtorBundle.rhs (H : CtorBundle c cl) (ls : List SLevel) : SExpr :=
  H.Ts.foldr .forallE (H.args.foldr (fun A acc => acc.app A) (.const H.I ls))

section
local notation:65 (priority := high) Γ " ⊢ " e1 " : " A:36 => IsDefEqStrong Γ e1 e1 A
local notation:65 (priority := high) Γ " ⊢ " e1 " ≡ " e2 " : " A:36 => IsDefEqStrong Γ e1 e2 A
inductive IsDefEqStrong : List SExpr → SExpr → SExpr → SExpr → Prop where
  | bvar : Lookup Γ i A → Γ ⊢ A : .sort u → Γ ⊢ .bvar i : A
  | symm : Γ ⊢ e ≡ e' : A → Γ ⊢ e' ≡ e : A
  | trans : Γ ⊢ e₁ ≡ e₂ : A → Γ ⊢ e₂ ≡ e₃ : A → Γ ⊢ e₁ ≡ e₃ : A
  | sort : Γ ⊢ .sort l : .sort (.succ l)
  | const : env.constants c = some ci → ls.length = ci.uvars →
    Γ ⊢ SExpr.mkInst ls ci.type : .sort u →
    (F : ∀ cl, CtorBundle c cl) →
    (∀ cl, Γ ⊢ SExpr.mkInst ls ci.type ≡ (F cl).rhs ls : .sort (F cl).u) →
    -- Definition bodies are stored in the direction used by semantic
    -- recursion: the body is the left endpoint, so its adequacy hypothesis can
    -- consume the strictly smaller `R`-child exposed by `LE_Interp.Const.pat`.
    -- The ordinary constant equality remains available by symmetry.
    (∀ {r : (Pattern.const c).RHS × (Pattern.const c).Check}, Pat (.const c) r →
      Γ ⊢ r.1.applyS ls Empty.elim ≡ .const c ls : SExpr.mkInst ls ci.type) →
    Γ ⊢ .const c ls : SExpr.mkInst ls ci.type
  | appDF : Γ ⊢ A : .sort u → A::Γ ⊢ B : .sort v →
    Γ ⊢ f ≡ f' : .forallE A B → Γ ⊢ a ≡ a' : A →
    Γ ⊢ B.inst a ≡ B.inst a' : .sort v →
    Γ ⊢ .app f a ≡ .app f' a' : B.inst a
  | lamDF : Γ ⊢ A ≡ A' : .sort u → A::Γ ⊢ B : .sort v →
    A'::Γ ⊢ B : .sort v →
    A::Γ ⊢ body ≡ body' : B → A'::Γ ⊢ body ≡ body' : B →
    Γ ⊢ .lam A body ≡ .lam A' body' : .forallE A B
  | forallEDF : Γ ⊢ A ≡ A' : .sort u →
    A::Γ ⊢ body ≡ body' : .sort v → A'::Γ ⊢ body ≡ body' : .sort v →
    Γ ⊢ .forallE A body ≡ .forallE A' body' : .sort (.imax u v)
  | defeqDF : Γ ⊢ A ≡ B : .sort u → Γ ⊢ e1 ≡ e2 : A → Γ ⊢ e1 ≡ e2 : B
  | beta : A::Γ ⊢ e : B → Γ ⊢ e' : A →
    Γ ⊢ .app (.lam A e) e' : B.inst e' → Γ ⊢ e.inst e' : B.inst e' →
    Γ ⊢ .app (.lam A e) e' ≡ e.inst e' : B.inst e'
  | eta : Γ ⊢ e : .forallE A B → Γ ⊢ .lam A (.app e.lift (.bvar 0)) : .forallE A B →
    Γ ⊢ .lam A (.app e.lift (.bvar 0)) ≡ e : .forallE A B
  | proofIrrel : Γ ⊢ p : .sort .zero → Γ ⊢ h : p → Γ ⊢ h' : p → Γ ⊢ h ≡ h' : p
  /-- A zero-arity definition contraction without the recursive constant-
  typing knot.  The local action supplies the ordinary equality, the RHS is
  strongly typed, and the constant metadata is exactly the non-definition
  fragment needed to type the left endpoint. -/
  | defn {r : (Pattern.const c).RHS × (Pattern.const c).Check} :
    env.constants c = some ci → ls.length = ci.uvars →
    Γ ⊢ SExpr.mkInst ls ci.type : .sort u →
    (F : ∀ cl, CtorBundle c cl) →
    (∀ cl, Γ ⊢ SExpr.mkInst ls ci.type ≡ (F cl).rhs ls : .sort (F cl).u) →
    (action : Pattern.Action Γ r (.const c ls) ls Empty.elim
      (SExpr.mkInst ls ci.type)) →
    Γ ⊢ r.1.applyS ls Empty.elim : SExpr.mkInst ls ci.type →
    Γ ⊢ .const c ls ≡ r.1.applyS ls Empty.elim : SExpr.mkInst ls ci.type
  /-- A local, proof-carrying extension contraction.  Unlike a registered
  raw equation, this constructor can be interpreted operationally: it names
  the concrete matched redex, carries its successful checks and exact local
  equality, and retains strong typings for both endpoints. -/
  | extra : (action : Pattern.Action Γ r e m1 m2 A) →
    Γ ⊢ e : A → Γ ⊢ r.1.applyS m1 m2 : A →
    Γ ⊢ e ≡ r.1.applyS m1 m2 : A
end

/-! The semantic bridge packages only environment-specific facts.  Its fields
are propositions carried by a concrete value; the public L4L-16 theorem
constructs that value from `VEnv.WF`, so none of these are trusted axioms. -/
class Params.Semantic [Params] where
  structureEta :
    ∀ {rule : VStructEta} {levels : List VLevel} {Γ params : List VExpr}
      {major : VExpr},
      env.structEtas rule →
      IsDefEqStrong (Γ.map mk)
        (mk (rule.rebuild levels params major))
        (mk (rule.rebuild levels params major))
        (mk (rule.structureType levels params)) →
      IsDefEqStrong (Γ.map mk) (mk major) (mk major)
        (mk (rule.structureType levels params)) →
      IsDefEqStrong (Γ.map mk) (mk (rule.rebuild levels params major))
        (mk major) (mk (rule.structureType levels params))
  ctor :
    ∀ {c : Name} {ci : VConstant} {ls : List SLevel} {Γ : List SExpr},
      env.constants c = some ci → ls.length = ci.uvars →
      ∀ cl : CtorBundle.IsCtor c,
        {F : CtorBundle c cl //
          IsDefEqStrong Γ (SExpr.mkInst ls ci.type) (F.rhs ls) (.sort F.u)}
  /-- Zero-arity patterns are definition rules.  The payload is a closed
  fixed expression and the bridge supplies its evidence-rich unfolding in
  every context.  This is proved from the declaration history; pattern
  membership by itself provides none of these facts. -/
  defn :
    ∀ {c : Name} {r : (Pattern.const c).RHS × (Pattern.const c).Check},
      Pat (.const c) r →
      ∃ (value : VExpr) (closed : value.Closed),
        r = (.fixed value closed, .true) ∧
        ∀ {ci : VConstant} {ls : List SLevel} {Γ : List SExpr},
          env.constants c = some ci → ls.length = ci.uvars →
          IsDefEqStrong Γ (.const c ls) (SExpr.mkInst ls value)
            (SExpr.mkInst ls ci.type)
  /-- Recover the one registered tower and ordered capture inventory selected
  by an iota payload.  This descriptor is match-independent and is therefore
  shared by both endpoints of a semantic comparison. -/
  iotaRule :
    ∀ {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
      {r : (RecursorIotaPattern rec major ctor arity).RHS ×
        (RecursorIotaPattern rec major ctor arity).Check},
      Pat (RecursorIotaPattern rec major ctor arity) r →
      Pattern.IotaRule r
  /-- Construct the evidence-rich site for a generated iota contraction.
  This field cannot return the contraction itself: it must expose the
  registered tower, typed capture application, and beta collapse, while the
  caller supplies the exact typed recursor and constructor spines (including
  the constructor levels recovered from the match).  `IotaReductionSite.action`
  derives the finite local contraction generically from this certificate. -/
  iotaSite :
    ∀ {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
      {r : (RecursorIotaPattern rec major ctor arity).RHS ×
        (RecursorIotaPattern rec major ctor arity).Check}
      {Γ : List SExpr} {A majorTerm : SExpr} {recLs ctorLs : List SLevel}
      {recArgs ctorArgs : List SExpr}
      {mcap : (RecursorIotaPattern rec major ctor arity).Path → SExpr},
      (rule : Pattern.IotaRule r) →
      (captureType : (RecursorIotaPattern rec major ctor arity).Path → SExpr) →
      (captureTyping : Pattern.CaptureTyping Γ mcap captureType) →
      /- Capture witnesses may arrive at an existentially selected common
      type.  Reified context validity is the finite evidence needed to align
      those types with the concrete generated telescope; without it this
      data-valued field is not constructible for an arbitrary `captureType`.
      The adequacy caller obtains this premise from `Ctx.WF.reify`. -/
      OnCtx (Γ.map SExpr.reify) (env.IsType univs) →
      (typing : Pattern.IotaTyping Γ rec ctor recLs ctorLs
        recArgs ctorArgs majorTerm A) →
      (RecursorIotaPattern rec major ctor arity).MatchesS
        ((recArgs.foldr (fun (a f : SExpr) => f.app a) (SExpr.const rec recLs)).app
          (ctorArgs.foldr (fun (a f : SExpr) => f.app a) (SExpr.const ctor ctorLs)))
        recLs mcap →
      IsDefEq Γ
        ((recArgs.foldr (fun (a f : SExpr) => f.app a) (SExpr.const rec recLs)).app
          (ctorArgs.foldr (fun (a f : SExpr) => f.app a) (SExpr.const ctor ctorLs)))
        ((recArgs.foldr (fun (a f : SExpr) => f.app a) (SExpr.const rec recLs)).app
          (ctorArgs.foldr (fun (a f : SExpr) => f.app a) (SExpr.const ctor ctorLs))) A →
      (∃ u, IsDefEq Γ A A (.sort u)) →
      Pattern.IotaReductionSite Γ r rule recLs ctorLs recArgs ctorArgs
        majorTerm A mcap captureType captureTyping
  /-- Expand a registered raw equation into structural strong equality whose
  only extension leaves are the proof-carrying local contractions above.
  Generated iota and quotient towers are therefore exposed under their
  lambdas instead of being falsely matched at the closed tower. -/
  registered :
    ∀ {df : VDefEq} {ls : List SLevel} {Γ : List SExpr},
      env.defeqs df → ls.length = df.uvars →
      IsDefEqStrong Γ (.mkInst ls df.lhs) (.mkInst ls df.lhs) (.mkInst ls df.type) →
      IsDefEqStrong Γ (.mkInst ls df.rhs) (.mkInst ls df.rhs) (.mkInst ls df.type) →
      IsDefEqStrong Γ (.mkInst ls df.lhs) (.mkInst ls df.rhs) (.mkInst ls df.type)

/-- A generated reduction-site certificate determines its finite local
contraction.  Soundness is assembled from the local beta collapse and the
registered tower equation applied along the retained capture spine; it is
not supplied by pattern membership. -/
def _root_.Lean4Lean.Pattern.IotaReductionSite.action
    {rec ctor : Name} {major arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {rule : Pattern.IotaRule r}
    {Γ : List SExpr} {recLs ctorLs : List SLevel}
    {recArgs ctorArgs : List SExpr} {majorTerm A : SExpr}
    {mcap : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
    {captureType : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
    {captureTyping : Pattern.CaptureTyping Γ mcap captureType}
    (site : Pattern.IotaReductionSite Γ r rule recLs ctorLs recArgs ctorArgs
      majorTerm A mcap captureType captureTyping) :
    Pattern.Action Γ r
      ((recArgs.foldr (fun (a f : SExpr) => f.app a) (SExpr.const rec recLs)).app
        (ctorArgs.foldr (fun (a f : SExpr) => f.app a) (SExpr.const ctor ctorLs)))
      recLs mcap A := by
  have hregistered : IsDefEq Γ
      (SExpr.mkInst recLs rule.df.lhs) (SExpr.mkInst recLs rule.df.rhs)
      (SExpr.mkInst recLs rule.df.type) :=
    .extra rule.registered site.levelsLength
  have hspine := site.captureSpine.toSpineWF captureTyping.typed
  have happlied := hspine.congr hregistered
  have hsound := site.lhsCollapse.trans happlied
  rw [rule.rhsApply recLs mcap] at hsound
  exact {
    pat := rule.pat
    matched := site.matched
    dfs := site.dfs
    defeqs := site.defeqs
    checked := site.checked
    sound := hsound }

/-- Translate Theory's evidence-rich judgment directly.  Unlike the former
admitted `SExpr.IsDefEq.strong`, this theorem never tries to recover missing
typing premises from a raw SExpr derivation. -/
theorem _root_.Lean4Lean.VEnv.IsDefEqStrong.mkS [Params.Semantic]
    (H : Params.env.IsDefEqStrong Params.univs Γ e₁ e₂ A) :
    IsDefEqStrong (Γ.map mk) (mk e₁) (mk e₂) (mk A) := by
  induction H with
  | bvar h _ _ ihA => exact .bvar (SExpr.Lookup.mkS h) ihA
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂
  | @sortDF l l' Γ hl hl' heq =>
    have hll := SLevel.mk_eq hl hl' heq
    have hsucc : SLevel.mk l.succ = (SLevel.mk l').succ := by
      rw [SLevel.mk_succ hl, hll]
    simpa only [mk, hll, hsucc] using (IsDefEqStrong.sort (Γ := Γ.map mk)
      (l := SLevel.mk l'))
  | @constDF c ci ls ls' u Γ hci hls hls' hlen hlevels _ _ _ ihGlobal ihLocal =>
    have hmap := SLevel.map_mk_eq hls hls' hlevels
    change IsDefEqStrong (Γ.map mk)
      (.const c (ls.map SLevel.mk)) (.const c (ls'.map SLevel.mk))
      (mk (ci.type.instL ls))
    rw [← hmap]
    have ihLocal' := ihLocal
    rw [← mkInst_map_mk hls, ← mkInst_map_mk hls', ← hmap] at ihLocal'
    have htype : IsDefEqStrong (Γ.map mk)
        (SExpr.mkInst (ls.map SLevel.mk) ci.type)
        (SExpr.mkInst (ls.map SLevel.mk) ci.type)
        (.sort (SLevel.mk u)) := by
      simpa only [mk] using ihLocal'
    let F : ∀ cl, CtorBundle c cl := fun cl =>
      (Params.Semantic.ctor (ls := ls.map SLevel.mk) (Γ := Γ.map mk)
        hci (by simpa using hlen) cl).1
    have hF : ∀ cl, IsDefEqStrong (Γ.map mk)
        (SExpr.mkInst (ls.map SLevel.mk) ci.type) ((F cl).rhs (ls.map SLevel.mk))
        (.sort (F cl).u) := by
      intro cl
      exact (Params.Semantic.ctor (ls := ls.map SLevel.mk) (Γ := Γ.map mk)
        hci (by simpa using hlen) cl).2
    have hDef : ∀ {r : (Pattern.const c).RHS × (Pattern.const c).Check},
        Params.Pat (.const c) r →
        IsDefEqStrong (Γ.map mk) (r.1.applyS (ls.map SLevel.mk) Empty.elim)
          (.const c (ls.map SLevel.mk))
          (SExpr.mkInst (ls.map SLevel.mk) ci.type) := by
      intro r hpat
      obtain ⟨value, closed, hr, hdef⟩ := Params.Semantic.defn hpat
      subst r
      simpa only [Pattern.RHS.applyS] using
        (hdef hci (by simpa using hlen) : IsDefEqStrong (Γ.map mk)
          (.const c (ls.map SLevel.mk)) (SExpr.mkInst (ls.map SLevel.mk) value)
          (SExpr.mkInst (ls.map SLevel.mk) ci.type)).symm
    simpa only [mkInst_map_mk hls] using
      (IsDefEqStrong.const hci (by simpa using hlen) htype F hF hDef)
  | appDF _ _ _ _ _ _ _ ihA ihCod ihf iha ihResult =>
    have ihResult' := ihResult
    simp only [mk, mk_instExpr] at ihResult'
    simpa only [List.map_cons, mk, mk_instExpr] using
      IsDefEqStrong.appDF ihA ihCod ihf iha ihResult'
  | lamDF _ _ _ _ _ _ _ ihA ihB ihB' ihBody ihBody' =>
    exact .lamDF ihA ihB ihB' ihBody ihBody'
  | forallEDF hu hv _ _ _ ihA ihBody ihBody' =>
    simpa only [mk, SLevel.mk_imax hu hv] using
      IsDefEqStrong.forallEDF ihA ihBody ihBody'
  | defeqDF _ _ _ ihA ihe => exact .defeqDF ihA ihe
  | beta _ _ _ _ _ _ _ _ ihA ihB ihBody ihArg ihResult ihInst =>
    have ihResult' := ihResult
    have ihInst' := ihInst
    simp only [mk, mk_instExpr] at ihResult' ihInst'
    have hlam := IsDefEqStrong.lamDF ihA ihB ihB ihBody ihBody
    have happ := IsDefEqStrong.appDF ihA ihB hlam ihArg ihResult'
    simpa only [mk, mk_instExpr] using
      IsDefEqStrong.beta ihBody ihArg happ ihInst'
  | @eta Γ A u B v e _ _ _ _ _ _ _ _
      ihA ihB ihBWeak ihe iheWeak ihAWeak =>
    have ihAWeak' : IsDefEqStrong (mk A :: Γ.map mk)
        (mk A).lift (mk A).lift (.sort (SLevel.mk u)) := by
      simpa only [List.map_cons, mk, mk_lift] using ihAWeak
    have iheWeak' : IsDefEqStrong (mk A :: Γ.map mk)
        (mk e).lift (mk e).lift
        (.forallE (mk A).lift (mk (B.liftN 1 1))) := by
      simpa only [List.map_cons, mk, mk_lift] using iheWeak
    have ihBWeak' : IsDefEqStrong ((mk A).lift :: mk A :: Γ.map mk)
        (mk (B.liftN 1 1)) (mk (B.liftN 1 1))
        (.sort (SLevel.mk v)) := by
      simpa only [List.map_cons, mk, mk_lift] using ihBWeak
    have hbvar : IsDefEqStrong (mk A :: Γ.map mk)
        (.bvar 0) (.bvar 0) (mk A).lift :=
      .bvar .zero ihAWeak'
    have hresult : (mk (B.liftN 1 1)).inst (.bvar 0) = mk B := by
      change (mk (B.liftN 1 1)).inst (mk (.bvar 0)) = mk B
      rw [← mk_instExpr]
      exact congrArg mk (VExpr.instN_bvar0 B 0)
    have happ : IsDefEqStrong (mk A :: Γ.map mk)
        (.app (mk e).lift (.bvar 0)) (.app (mk e).lift (.bvar 0)) (mk B) := by
      rw [← hresult]
      exact IsDefEqStrong.appDF ihAWeak' ihBWeak' iheWeak' hbvar (hresult ▸ ihB)
    have hlam := IsDefEqStrong.lamDF ihA ihB ihB happ happ
    simpa only [mk, mk_lift] using IsDefEqStrong.eta ihe hlam
  | structEta hreg _ _ _ _ _ _ _ _ ihType ihMajor ihRebuild =>
    exact Params.Semantic.structureEta hreg ihRebuild ihMajor
  | proofIrrel _ _ _ ihp ihh ihh' => exact .proofIrrel ihp ihh ihh'
  | @extra df ls u Γ hreg hlevels hlen _ _ _ _ _ _ _ _ _ ihLhs ihRhs =>
    have ihLhs' := ihLhs
    have ihRhs' := ihRhs
    rw [← mkInst_map_mk hlevels, ← mkInst_map_mk hlevels] at ihLhs' ihRhs'
    simpa only [mkInst_map_mk hlevels] using
      (Params.Semantic.registered (Γ := Γ.map mk) (ls := ls.map SLevel.mk)
        hreg (by simpa using hlen) ihLhs' ihRhs')

/-- Reify semantic universe levels to instantiate a closed Theory typing,
then translate its evidence-rich strengthening back to any SExpr context.
This is the fixed-head typing input needed by semantic `R`-recursion: it is
derived from `Params.henv`, not added to `Params.Semantic` as an oracle. -/
theorem Params.Semantic.closedHasTypeStrong
    [Params.Semantic]
    {U : Nat} {e A : VExpr} {ls : List SLevel} {Γ : List SExpr}
    (H : Params.env.HasType U [] e A) :
    IsDefEqStrong Γ (SExpr.mkInst ls e) (SExpr.mkInst ls e)
      (SExpr.mkInst ls A) := by
  let vls := ls.map SLevel.reify
  have hlevels : ∀ l ∈ vls, l.WF Params.univs := by
    intro l hl
    simp only [vls, List.mem_map] at hl
    obtain ⟨sl, _, rfl⟩ := hl
    exact SLevel.reify_wf sl
  have hStrong :=
    ((H.strong Params.henv (by trivial)).instL hlevels).weak0
      Params.henv (Γ := Γ.map SExpr.reify)
  have hS := hStrong.mkS
  have hvls : vls.map SLevel.mk = ls := by
    change (ls.map SLevel.reify).map SLevel.mk = ls
    rw [List.map_map]
    exact List.map_id''' ls fun sl _ => SLevel.mk_reify sl
  have hctx : (Γ.map SExpr.reify).map SExpr.mk = Γ := by
    rw [List.map_map]
    exact List.map_id''' Γ fun term _ => SExpr.mk_reify term
  have hmkinst (term : VExpr) :
      SExpr.mkInst ls term = SExpr.mk (term.instL vls) := by
    rw [← hvls]
    exact SExpr.mkInst_map_mk hlevels
  simpa only [hctx, hmkinst] using hS

/-- A registered equation's right tower has an evidence-rich self-typing at
every semantic level instantiation. -/
theorem Params.Semantic.registeredRhsStrong
    [Params.Semantic]
    {df : VDefEq} {ls : List SLevel} {Γ : List SExpr}
    (hreg : Params.env.defeqs df) :
    IsDefEqStrong Γ (SExpr.mkInst ls df.rhs) (SExpr.mkInst ls df.rhs)
      (SExpr.mkInst ls df.type) :=
  Params.Semantic.closedHasTypeStrong (Params.henv.defEqWF hreg).2

/-- The fixed head selected by an iota descriptor is strongly self-typed.
This is the syntactic half of the repaired `IotaRHSDefEq` contract; its
logical adequacy is supplied by the surrounding semantic `R` recursion. -/
theorem _root_.Lean4Lean.Pattern.IotaRule.rhsStrong
    [Params.Semantic]
    {rec ctor : Name} {major arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (rule : Pattern.IotaRule r) (ls : List SLevel) :
    IsDefEqStrong Γ (SExpr.mkInst ls rule.df.rhs)
      (SExpr.mkInst ls rule.df.rhs) (SExpr.mkInst ls rule.df.type) :=
  Params.Semantic.registeredRhsStrong rule.registered

theorem IsDefEqStrong.defeq : IsDefEqStrong Γ e1 e2 A → Γ ⊢ e1 ≡ e2 : A := by
  intro H
  induction H with
  | bvar h _ _ => exact .bvar h
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | sort => exact .sort
  | const hreg hlen _ _ _ => exact .const hreg hlen
  | appDF _ _ _ _ _ _ _ ihf iha _ => exact .appDF ihf iha
  | lamDF _ _ _ _ _ ihA _ _ ihBody _ => exact .lamDF ihA ihBody
  | forallEDF _ _ _ ihA ihBody _ => exact .forallEDF ihA ihBody
  | defeqDF _ _ ihA ihe => exact .defeqDF ihA ihe
  | beta _ _ _ _ ihBody ihArg _ _ => exact .beta ihBody ihArg
  | eta _ _ ihe _ => exact .eta ihe
  | proofIrrel _ _ _ ihp ihh ihh' => exact .proofIrrel ihp ihh ihh'
  | defn _ _ _ _ _ action => exact action.sound
  | extra action _ _ _ _ => exact action.sound

/-- Both endpoints of an evidence-rich equality retain evidence-rich
self-typings at its declared type.  Unlike the corresponding weak fact,
this is just homogeneous composition and therefore does not need type
uniqueness. -/
theorem IsDefEqStrong.hasType
    (H : IsDefEqStrong Γ e₁ e₂ A) :
    IsDefEqStrong Γ e₁ e₁ A ∧ IsDefEqStrong Γ e₂ e₂ A :=
  ⟨H.trans H.symm, H.symm.trans H⟩

/-- If either endpoint of an evidence-rich equality is syntactically a Pi,
recover evidence-rich validity of its domain and codomain.  All extension
leaves of `IsDefEqStrong` carry their endpoint typings, so this eliminator is
structural; in particular it does not appeal to weak type uniqueness or
Church--Rosser. -/
theorem IsDefEqStrong.forallE_inv'
    (H : IsDefEqStrong Γ e₁ e₂ V)
    (eq : e₁ = .forallE A B ∨ e₂ = .forallE A B) :
    (∃ u, IsDefEqStrong Γ A A (.sort u)) ∧
      ∃ v, IsDefEqStrong (A :: Γ) B B (.sort v) := by
  induction H generalizing A B with
  | bvar => nomatch eq
  | symm _ ih => exact ih eq.symm
  | trans _ _ ih₁ ih₂ =>
    obtain eq | eq := eq
    · exact ih₁ (.inl eq)
    · exact ih₂ (.inr eq)
  | sort => nomatch eq
  | const => nomatch eq
  | appDF => nomatch eq
  | lamDF => nomatch eq
  | forallEDF hA hBody hBody' _ _ _ =>
    obtain ⟨⟨⟩⟩ | ⟨⟨⟩⟩ := eq
    · exact ⟨⟨_, hA.hasType.1⟩, _, hBody.hasType.1⟩
    · exact ⟨⟨_, hA.hasType.2⟩, _, hBody'.hasType.2⟩
  | defeqDF _ _ _ ih => exact ih eq
  | beta _ _ _ _ _ _ _ ihInst =>
    obtain eq | eq := eq
    · nomatch eq
    · exact ihInst (.inl eq)
  | eta _ _ ihTerm _ =>
    obtain eq | eq := eq
    · nomatch eq
    · exact ihTerm (.inl eq)
  | proofIrrel _ _ _ ihProp ihLeft ihRight =>
    obtain eq | eq := eq
    · exact ihLeft (.inl eq)
    · exact ihRight (.inr eq)
  | defn _ _ _ _ _ _ _ _ _ ihRhs =>
    obtain eq | eq := eq
    · nomatch eq
    · exact ihRhs (.inl eq)
  | extra _ _ _ ihLeft ihRight =>
    obtain eq | eq := eq
    · exact ihLeft (.inl eq)
    · exact ihRight (.inr eq)

/-- The declared type of every evidence-rich equality is itself an
evidence-rich type.  The extra premises retained by application, lambda,
beta, eta, and local extension constructors make this a direct structural
proof. -/
theorem IsDefEqStrong.isType
    (H : IsDefEqStrong Γ e₁ e₂ A) :
    ∃ u, IsDefEqStrong Γ A A (.sort u) := by
  induction H with
  | bvar _ hA _ => exact ⟨_, hA⟩
  | symm _ ih => exact ih
  | trans _ _ ih _ => exact ih
  | sort => exact ⟨_, .sort⟩
  | const _ _ hTy _ _ _ _ _ _ => exact ⟨_, hTy⟩
  | appDF _ _ _ _ hResult _ _ _ _ _ =>
    exact ⟨_, hResult.hasType.1⟩
  | lamDF hA hBody _ _ _ _ _ _ _ _ =>
    have hAA := hA.hasType.1
    have hBB := hBody.hasType.1
    exact ⟨_, .forallEDF hAA hBB hBB⟩
  | forallEDF => exact ⟨_, .sort⟩
  | defeqDF hType _ _ _ => exact ⟨_, hType.hasType.2⟩
  | beta _ _ _ _ _ _ _ ihInst => exact ihInst
  | eta _ _ ihTerm _ => exact ihTerm
  | proofIrrel hProp _ _ _ _ _ => exact ⟨_, hProp⟩
  | defn _ _ hTy => exact ⟨_, hTy⟩
  | extra _ _ _ ihLeft _ => exact ihLeft

theorem IsDefEq.hasType (H : Γ ⊢ e1 ≡ e2 : A) :
    Γ ⊢ e1 ≡ e1 : A ∧ Γ ⊢ e2 ≡ e2 : A := ⟨H.trans H.symm, H.symm.trans H⟩

section
set_option hygiene false
local notation:65 Γ " ⊢ " e " : " A:36 " !! " n:36 => HasTypeStratifiedS Γ e A true n
local notation:65 Γ " ⊢ " e " :! " A:36 " !! " n:36 => HasTypeStratifiedS Γ e A false n

/-- SExpr-side analog of `HasTypeStratified`: a typing derivation indexed by
its tree depth `n`, used for well-founded induction on stratification. -/
inductive HasTypeStratifiedS : List SExpr → SExpr → SExpr → Bool → Nat → Prop where
  | bvar : Lookup Γ i A → Γ ⊢ A : .sort u !! n → Γ ⊢ .bvar i :! A !! n+1
  | sort' : Γ ⊢ .sort l :! .sort (.succ l) !! n
  | const :
    env.constants c = some ci →
    ls.length = ci.uvars →
    Γ ⊢ SExpr.mkInst ls ci.type : .sort u !! n →
    Γ ⊢ .const c ls :! SExpr.mkInst ls ci.type !! n+1
  | app :
    Γ ⊢ A : .sort u !! n →
    A::Γ ⊢ B : .sort v !! n →
    Γ ⊢ f : .forallE A B !! n →
    Γ ⊢ a : A !! n →
    Γ ⊢ B.inst a : .sort v !! n →
    Γ ⊢ .app f a :! B.inst a !! n+1
  | lam :
    Γ ⊢ A : .sort u !! n →
    A::Γ ⊢ B : .sort v !! n →
    A::Γ ⊢ body : B !! n →
    Γ ⊢ .forallE A B : .sort (.imax u v) !! n →
    Γ ⊢ .lam A body :! .forallE A B !! n+1
  | forallE :
    Γ ⊢ A : .sort u !! n →
    A::Γ ⊢ body : .sort v !! n →
    Γ ⊢ .forallE A body :! .sort (.imax u v) !! n+1
  | base : Γ ⊢ e :! A !! n → Γ ⊢ e : A !! n
  | defeq : IsDefEqStrong Γ A B (.sort u) →
    Γ ⊢ A : .sort u !! n → Γ ⊢ B : .sort u !! n →
    Γ ⊢ e : A !! n → Γ ⊢ e : B !! n+1
end

scoped notation:65 Γ " ⊢ " e " : " A:36 " !! " n:36 => HasTypeStratifiedS Γ e A true n
scoped notation:65 Γ " ⊢ " e " :! " A:36 " !! " n:36 => HasTypeStratifiedS Γ e A false n

theorem HasTypeStratifiedS.mono (le : m ≤ n)
    (H : HasTypeStratifiedS Γ e A b m) : HasTypeStratifiedS Γ e A b n := by
  induction H generalizing n with
  | bvar h _ ih =>
    let n + 1 := n
    exact .bvar h (ih (Nat.le_of_succ_le_succ le))
  | sort' => exact .sort'
  | const hreg hlen _ ih =>
    let n + 1 := n
    exact .const hreg hlen (ih (Nat.le_of_succ_le_succ le))
  | app _ _ _ _ _ ihA ihB ihf iha ihR =>
    let n + 1 := n
    replace le := Nat.le_of_succ_le_succ le
    exact .app (ihA le) (ihB le) (ihf le) (iha le) (ihR le)
  | lam _ _ _ _ ihA ihB ihBody ihPi =>
    let n + 1 := n
    replace le := Nat.le_of_succ_le_succ le
    exact .lam (ihA le) (ihB le) (ihBody le) (ihPi le)
  | forallE _ _ ihA ihBody =>
    let n + 1 := n
    replace le := Nat.le_of_succ_le_succ le
    exact .forallE (ihA le) (ihBody le)
  | base _ ih => exact .base (ih le)
  | defeq h _ _ _ ihA ihB ihe =>
    let n + 1 := n
    replace le := Nat.le_of_succ_le_succ le
    exact .defeq h (ihA le) (ihB le) (ihe le)

/-! ### A δ-rank refinement of stratified typing

`VEnv.WF` permits mutually recursive definition cycles, so termination of
the semantic constant evaluator cannot be recovered from declaration order.
The rank below is therefore explicit instance data.  The judgment refines
`HasTypeStratifiedS` without changing its depth index: only the `const` rule
records that the referenced declaration is available at the current rank.
-/

/-- Stratified typing with an additional upper bound on the δ-rank of every
constant used by the derivation. -/
inductive HasTypeStratifiedR (rank : Name → Nat) :
    List SExpr → SExpr → SExpr → Bool → Nat → Nat → Prop where
  | bvar {n r : Nat} :
    Lookup Γ i A →
    HasTypeStratifiedR rank Γ A (.sort u) true n r →
    HasTypeStratifiedR rank Γ (.bvar i) A false (n + 1) r
  | sort' {n r : Nat} :
    HasTypeStratifiedR rank Γ (.sort l) (.sort (.succ l)) false n r
  | const {n r : Nat} :
    env.constants c = some ci →
    ls.length = ci.uvars →
    rank c ≤ r →
    HasTypeStratifiedR rank Γ (SExpr.mkInst ls ci.type) (.sort u) true n r →
    HasTypeStratifiedR rank Γ (.const c ls)
      (SExpr.mkInst ls ci.type) false (n + 1) r
  | app {n r : Nat} :
    HasTypeStratifiedR rank Γ A (.sort u) true n r →
    HasTypeStratifiedR rank (A :: Γ) B (.sort v) true n r →
    HasTypeStratifiedR rank Γ f (.forallE A B) true n r →
    HasTypeStratifiedR rank Γ a A true n r →
    HasTypeStratifiedR rank Γ (B.inst a) (.sort v) true n r →
    HasTypeStratifiedR rank Γ (.app f a) (B.inst a) false (n + 1) r
  | lam {n r : Nat} :
    HasTypeStratifiedR rank Γ A (.sort u) true n r →
    HasTypeStratifiedR rank (A :: Γ) B (.sort v) true n r →
    HasTypeStratifiedR rank (A :: Γ) body B true n r →
    HasTypeStratifiedR rank Γ (.forallE A B) (.sort (.imax u v)) true n r →
    HasTypeStratifiedR rank Γ (.lam A body) (.forallE A B) false (n + 1) r
  | forallE {n r : Nat} :
    HasTypeStratifiedR rank Γ A (.sort u) true n r →
    HasTypeStratifiedR rank (A :: Γ) body (.sort v) true n r →
    HasTypeStratifiedR rank Γ (.forallE A body)
      (.sort (.imax u v)) false (n + 1) r
  | base :
    HasTypeStratifiedR rank Γ e A false n r →
    HasTypeStratifiedR rank Γ e A true n r
  | defeq :
    IsDefEqStrong Γ A B (.sort u) →
    HasTypeStratifiedR rank Γ A (.sort u) true n r →
    HasTypeStratifiedR rank Γ B (.sort u) true n r →
    HasTypeStratifiedR rank Γ e A true n r →
    HasTypeStratifiedR rank Γ e B true (n + 1) r

/-- Forgetting the δ-rank recovers the ordinary stratified judgment. -/
theorem HasTypeStratifiedR.toS
    (H : HasTypeStratifiedR rank Γ e A b n r) :
    HasTypeStratifiedS Γ e A b n := by
  induction H with
  | bvar h _ ih => exact .bvar h ih
  | sort' => exact .sort'
  | const hreg hlen _ _ ih => exact .const hreg hlen ih
  | app _ _ _ _ _ ihA ihB ihf iha ihR => exact .app ihA ihB ihf iha ihR
  | lam _ _ _ _ ihA ihB ihbody ihPi => exact .lam ihA ihB ihbody ihPi
  | forallE _ _ ihA ihbody => exact .forallE ihA ihbody
  | base _ ih => exact .base ih
  | defeq h _ _ _ ihA ihB ihe => exact .defeq h ihA ihB ihe

/-- The rank index is monotone. -/
theorem HasTypeStratifiedR.mono_rank
    (H : HasTypeStratifiedR rank Γ e A b n r) :
    ∀ {r' : Nat}, r ≤ r' → HasTypeStratifiedR rank Γ e A b n r' := by
  induction H with
  | bvar h _ ih => exact fun hle => .bvar h (ih hle)
  | sort' => exact fun _ => .sort'
  | const hreg hlen hrank _ ih =>
    exact fun hle => .const hreg hlen (Nat.le_trans hrank hle) (ih hle)
  | app _ _ _ _ _ ihA ihB ihf iha ihR =>
    exact fun hle => .app (ihA hle) (ihB hle) (ihf hle) (iha hle) (ihR hle)
  | lam _ _ _ _ ihA ihB ihbody ihPi =>
    exact fun hle => .lam (ihA hle) (ihB hle) (ihbody hle) (ihPi hle)
  | forallE _ _ ihA ihbody => exact fun hle => .forallE (ihA hle) (ihbody hle)
  | base _ ih => exact fun hle => .base (ih hle)
  | defeq h _ _ _ ihA ihB ihe =>
    exact fun hle => .defeq h (ihA hle) (ihB hle) (ihe hle)

/-- Every ordinary stratified derivation admits some rank bound.  Thus the
extra index is a recursion certificate, not a restriction on typing. -/
theorem HasTypeStratifiedR.exists_rank (rank : Name → Nat)
    (H : HasTypeStratifiedS Γ e A b n) :
    ∃ r, HasTypeStratifiedR rank Γ e A b n r := by
  induction H with
  | bvar h _ ih => obtain ⟨r, hr⟩ := ih; exact ⟨r, .bvar h hr⟩
  | sort' => exact ⟨0, .sort'⟩
  | @const c ci Γ ls u n hreg hlen _ ih =>
    obtain ⟨r, hr⟩ := ih
    exact ⟨max (rank c) r,
      .const hreg hlen (Nat.le_max_left ..)
        (hr.mono_rank (Nat.le_max_right ..))⟩
  | app _ _ _ _ _ ihA ihB ihf iha ihR =>
    obtain ⟨r1, h1⟩ := ihA; obtain ⟨r2, h2⟩ := ihB
    obtain ⟨r3, h3⟩ := ihf; obtain ⟨r4, h4⟩ := iha
    obtain ⟨r5, h5⟩ := ihR
    exact ⟨max (max (max r1 r2) (max r3 r4)) r5,
      .app (h1.mono_rank (by omega)) (h2.mono_rank (by omega))
        (h3.mono_rank (by omega)) (h4.mono_rank (by omega))
        (h5.mono_rank (by omega))⟩
  | lam _ _ _ _ ihA ihB ihbody ihPi =>
    obtain ⟨r1, h1⟩ := ihA; obtain ⟨r2, h2⟩ := ihB
    obtain ⟨r3, h3⟩ := ihbody; obtain ⟨r4, h4⟩ := ihPi
    exact ⟨max (max r1 r2) (max r3 r4),
      .lam (h1.mono_rank (by omega)) (h2.mono_rank (by omega))
        (h3.mono_rank (by omega)) (h4.mono_rank (by omega))⟩
  | forallE _ _ ihA ihbody =>
    obtain ⟨r1, h1⟩ := ihA; obtain ⟨r2, h2⟩ := ihbody
    exact ⟨max r1 r2, .forallE (h1.mono_rank (by omega))
      (h2.mono_rank (by omega))⟩
  | base _ ih => obtain ⟨r, hr⟩ := ih; exact ⟨r, .base hr⟩
  | defeq h _ _ _ ihA ihB ihe =>
    obtain ⟨r1, h1⟩ := ihA; obtain ⟨r2, h2⟩ := ihB
    obtain ⟨r3, h3⟩ := ihe
    exact ⟨max (max r1 r2) r3,
      .defeq h (h1.mono_rank (by omega)) (h2.mono_rank (by omega))
        (h3.mono_rank (by omega))⟩

/-- Per-environment δ-termination data.  A registered definition supplies a
typing certificate for its value strictly below the rank of the constant
whose reduction exposes that value. -/
class Params.DeltaRank [Params] : Type where
  rank : Name → Nat
  defnCert :
    ∀ {c : Name} {ci : VConstant} {value : VExpr} {closed : value.Closed}
      {ls : List SLevel} {Γ : List SExpr},
      Params.Pat (.const c) (.fixed value closed, .true) →
      env.constants c = some ci →
      ls.length = ci.uvars →
      ∃ (nV rV : Nat), rV < rank c ∧
        HasTypeStratifiedR rank Γ (SExpr.mkInst ls value)
          (SExpr.mkInst ls ci.type) true nV rV

/-- A definitional constant necessarily has positive δ-rank. -/
theorem Params.DeltaRank.defn_pos [Params.DeltaRank]
    {c : Name} {ci : VConstant} {value : VExpr} {closed : value.Closed}
    (hpat : Params.Pat (.const c) (.fixed value closed, .true))
    (hreg : env.constants c = some ci) : 0 < Params.DeltaRank.rank c := by
  obtain ⟨nV, rV, hlt, -⟩ := Params.DeltaRank.defnCert (Γ := [])
    (ls := List.replicate ci.uvars SLevel.zero) hpat hreg
    (List.length_replicate ..)
  exact Nat.lt_of_le_of_lt (Nat.zero_le rV) hlt

/-- info: 'Lean4Lean.SExpr.HasTypeStratifiedR.exists_rank' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms HasTypeStratifiedR.exists_rank

/-- info: 'Lean4Lean.SExpr.Params.DeltaRank.defn_pos' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Params.DeltaRank.defn_pos

/-- Every evidence-rich equality has stratified typings for both endpoints
at one common depth.  The application and lambda cases are the reason the
strong judgment retains codomain validity in both binder contexts: the
right endpoint is first typed at its native dependent result and then
transported back to the left-oriented conclusion type. -/
theorem IsDefEqStrong.stratify (H : IsDefEqStrong Γ e₁ e₂ A) :
    ∃ n, HasTypeStratifiedS Γ e₁ A true n ∧
      HasTypeStratifiedS Γ e₂ A true n := by
  induction H with
  | bvar h _ ihA =>
    obtain ⟨n, hA, _⟩ := ihA
    exact ⟨n + 1, .base (.bvar h hA), .base (.bvar h hA)⟩
  | symm _ ih =>
    obtain ⟨n, h₁, h₂⟩ := ih
    exact ⟨n, h₂, h₁⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨n₁, h₁, _⟩ := ih₁
    obtain ⟨n₂, _, h₂⟩ := ih₂
    exact ⟨max n₁ n₂, h₁.mono (Nat.le_max_left ..),
      h₂.mono (Nat.le_max_right ..)⟩
  | sort =>
    exact ⟨0, .base .sort', .base .sort'⟩
  | const hreg hlen _ _ _ _ ihTy _ _ =>
    obtain ⟨n, hTy, _⟩ := ihTy
    exact ⟨n + 1, .base (.const hreg hlen hTy),
      .base (.const hreg hlen hTy)⟩
  | @appDF Γ A u B v f f' a a' hA hCod hf ha hResult
      ihA ihCod ihf iha ihResult =>
    obtain ⟨nA, hA₁, _⟩ := ihA
    obtain ⟨nCod, hCod₁, _⟩ := ihCod
    obtain ⟨nf, hf₁, hf₂⟩ := ihf
    obtain ⟨na, ha₁, ha₂⟩ := iha
    obtain ⟨nR, hR₁, hR₂⟩ := ihResult
    let k := max nA (max nCod (max nf (max na nR)))
    have hleft : HasTypeStratifiedS Γ (.app f a) (B.inst a) true (k + 1) :=
      .base (.app (hA₁.mono (by omega)) (hCod₁.mono (by omega))
        (hf₁.mono (by omega)) (ha₁.mono (by omega))
        (hR₁.mono (by omega)))
    have hrightNative :
        HasTypeStratifiedS Γ (.app f' a') (B.inst a') true (k + 1) :=
      .base (.app (hA₁.mono (by omega)) (hCod₁.mono (by omega))
        (hf₂.mono (by omega)) (ha₂.mono (by omega))
        (hR₂.mono (by omega)))
    have hright : HasTypeStratifiedS Γ (.app f' a') (B.inst a) true (k + 2) :=
      .defeq hResult.symm
        (hR₂.mono (by omega)) (hR₁.mono (by omega))
        hrightNative
    exact ⟨k + 2, hleft.mono (by omega), hright⟩
  | @lamDF Γ A A' u B v body body' hA hB hB' hBody hBody'
      ihA ihB ihB' ihBody ihBody' =>
    obtain ⟨nA, hA₁, hA₂⟩ := ihA
    obtain ⟨nB, hB₁, _⟩ := ihB
    obtain ⟨nB', hB₁', hB₂'⟩ := ihB'
    obtain ⟨nBody, hBody₁, _⟩ := ihBody
    obtain ⟨nBody', _, hBody₂'⟩ := ihBody'
    let k := max nA (max nB (max nB' (max nBody nBody')))
    have hPi : HasTypeStratifiedS Γ (.forallE A B)
        (.sort (.imax u v)) true (k + 1) :=
      .base (.forallE (hA₁.mono (by omega)) (hB₁.mono (by omega)))
    have hPi' : HasTypeStratifiedS Γ (.forallE A' B)
        (.sort (.imax u v)) true (k + 1) :=
      .base (.forallE (hA₂.mono (by omega)) (hB₂'.mono (by omega)))
    have hleft : HasTypeStratifiedS Γ (.lam A body) (.forallE A B)
        true (k + 2) :=
      .base (.lam (hA₁.mono (by omega)) (hB₁.mono (by omega))
        (hBody₁.mono (by omega)) hPi)
    have hrightNative : HasTypeStratifiedS Γ (.lam A' body')
        (.forallE A' B) true (k + 2) :=
      .base (.lam (hA₂.mono (by omega)) (hB₂'.mono (by omega))
        (hBody₂'.mono (by omega)) hPi')
    have hPiEq : IsDefEqStrong Γ (.forallE A B) (.forallE A' B)
        (.sort (.imax u v)) :=
      .forallEDF hA hB hB'
    have hright : HasTypeStratifiedS Γ (.lam A' body') (.forallE A B)
        true (k + 3) :=
      .defeq hPiEq.symm (hPi'.mono (by omega)) (hPi.mono (by omega))
        hrightNative
    exact ⟨k + 3, hleft.mono (by omega), hright⟩
  | forallEDF _ _ _ ihA ihBody ihBody' =>
    obtain ⟨nA, hA₁, hA₂⟩ := ihA
    obtain ⟨nB, hB₁, _⟩ := ihBody
    obtain ⟨nB', _, hB₂⟩ := ihBody'
    let k := max nA (max nB nB')
    exact ⟨k + 1,
      .base (.forallE (hA₁.mono (by omega)) (hB₁.mono (by omega))),
      .base (.forallE (hA₂.mono (by omega)) (hB₂.mono (by omega)))⟩
  | defeqDF hA _ ihA ihe =>
    obtain ⟨nA, hA₁, hA₂⟩ := ihA
    obtain ⟨ne, he₁, he₂⟩ := ihe
    let k := max nA ne
    exact ⟨k + 1,
      .defeq hA (hA₁.mono (by omega)) (hA₂.mono (by omega))
        (he₁.mono (by omega)),
      .defeq hA (hA₁.mono (by omega)) (hA₂.mono (by omega))
        (he₂.mono (by omega))⟩
  | beta _ _ _ _ ihBody ihArg ihApp ihInst =>
    obtain ⟨nApp, hApp, _⟩ := ihApp
    obtain ⟨nInst, _, hInst⟩ := ihInst
    exact ⟨max nApp nInst, hApp.mono (Nat.le_max_left ..),
      hInst.mono (Nat.le_max_right ..)⟩
  | eta _ _ ihe ihLam =>
    obtain ⟨ne, _, he⟩ := ihe
    obtain ⟨nLam, hLam, _⟩ := ihLam
    exact ⟨max nLam ne, hLam.mono (Nat.le_max_left ..),
      he.mono (Nat.le_max_right ..)⟩
  | proofIrrel _ _ _ _ ihh ihh' =>
    obtain ⟨nh, hh, _⟩ := ihh
    obtain ⟨nh', _, hh'⟩ := ihh'
    exact ⟨max nh nh', hh.mono (Nat.le_max_left ..),
      hh'.mono (Nat.le_max_right ..)⟩
  | defn hreg hlen _ _ _ _ _ ihTy _ ihRhs =>
    obtain ⟨nTy, hTy, _⟩ := ihTy
    obtain ⟨nRhs, _, hRhs⟩ := ihRhs
    let k := max (nTy + 1) nRhs
    exact ⟨k,
      (HasTypeStratifiedS.base (.const hreg hlen hTy)).mono
        (Nat.le_max_left ..),
      hRhs.mono (Nat.le_max_right ..)⟩
  | extra _ _ _ ihLeft ihRight =>
    obtain ⟨nL, hL, _⟩ := ihLeft
    obtain ⟨nR, _, hR⟩ := ihRight
    exact ⟨max nL nR, hL.mono (Nat.le_max_left ..),
      hR.mono (Nat.le_max_right ..)⟩

/-- Erase only the stratification index, retaining the ordinary weak typing
judgment. -/
theorem HasTypeStratifiedS.hasType
    (H : HasTypeStratifiedS Γ e A b n) : Γ ⊢ e : A := by
  induction H with
  | bvar h _ _ => exact .bvar h
  | sort' => exact .sort
  | const hreg hlen _ _ => exact .const hreg hlen
  | app _ _ _ _ _ _ _ ihf iha _ => exact .appDF ihf iha
  | lam _ _ _ _ ihA _ ihBody _ => exact .lamDF ihA ihBody
  | forallE _ _ ihA ihBody => exact .forallEDF ihA ihBody
  | base _ ih => exact ih
  | defeq h _ _ _ _ _ ihe => exact h.defeq.defeqDF ihe

theorem HasTypeStratifiedS.to_core (H : Γ ⊢ e : A !! n) :
    ∃ A', Γ ⊢ e :! A' !! n := by
  generalize hb : true = b at H
  induction H with cases hb
  | base h _ => exact ⟨_, h⟩
  | defeq _ _ _ _ _ _ ih =>
    obtain ⟨A', hA'⟩ := ih rfl
    exact ⟨A', hA'.mono (Nat.le_succ _)⟩

/-- A stratified typing of a syntactic Pi exposes strictly shallower
stratified typings for its domain and codomain.  Outer conversions are
discarded by `to_core`; the remaining core derivation is forced to be the
syntax-directed `forallE` constructor.  This is the depth information the
joint adequacy/uniqueness induction needs in its application case. -/
theorem HasTypeStratifiedS.forallE_inv
    (H : HasTypeStratifiedS Γ (.forallE A B) V true n) :
    ∃ u v,
      HasTypeStratifiedS Γ A (.sort u) true (n - 1) ∧
      HasTypeStratifiedS (A :: Γ) B (.sort v) true (n - 1) := by
  obtain ⟨V', H⟩ := H.to_core
  cases H with
  | forallE hA hB =>
    exact ⟨_, _, by simpa using hA, by simpa using hB⟩

/-- A stratified typing of a concrete application exposes every native
typing premise one layer earlier.

Outer displayed-type conversions are discarded by `to_core`; consequently
the returned codomain is the one selected by the actual application
derivation, rather than an independently reconstructed typing of the public
result type.  Iterating this lemma down a focused registered RHS tower keeps
the exact endpoint derivation and provides the strict depth decrease needed
before rebuilding an evaluator edge. -/
theorem HasTypeStratifiedS.app_inv
    (H : HasTypeStratifiedS Γ (.app f a) V true n) :
    ∃ A u B v,
      HasTypeStratifiedS Γ A (.sort u) true (n - 1) ∧
      HasTypeStratifiedS (A :: Γ) B (.sort v) true (n - 1) ∧
      HasTypeStratifiedS Γ f (.forallE A B) true (n - 1) ∧
      HasTypeStratifiedS Γ a A true (n - 1) ∧
      HasTypeStratifiedS Γ (B.inst a) (.sort v) true (n - 1) := by
  obtain ⟨V', H⟩ := H.to_core
  cases H with
  | app hA hB hf ha hResult =>
    exact ⟨_, _, _, _, by simpa using hA, by simpa using hB,
      by simpa using hf, by simpa using ha, by simpa using hResult⟩

/-- Iteratively peel a concrete left-associated application tower while
retaining the native typing derivation of its literal head. -/
theorem HasTypeStratifiedS.foldl_app_head
    {args : List SExpr} {head V : SExpr}
    (H : HasTypeStratifiedS Γ
      (args.foldl (fun f a => f.app a) head) V true n) :
    ∃ HeadType,
      HasTypeStratifiedS Γ head HeadType true (n - args.length) := by
  induction args generalizing head n V with
  | nil => exact ⟨V, by simpa⟩
  | cons arg args ih =>
    simp only [List.foldl_cons] at H
    obtain ⟨_, hHeadApp⟩ := ih H
    obtain ⟨A, _, B, _, _, _, hHead, _, _⟩ := hHeadApp.app_inv
    refine ⟨.forallE A B, ?_⟩
    simpa only [List.length_cons, Nat.sub_sub, Nat.add_comm] using hHead

/-- A well-typed nonempty left-associated application tower has positive
stratification depth. -/
theorem HasTypeStratifiedS.foldl_app_depth_pos
    {args : List SExpr} {head V : SExpr}
    (H : HasTypeStratifiedS Γ
      (args.foldl (fun f a => f.app a) head) V true n)
    (hne : args ≠ []) :
    0 < n := by
  induction args generalizing head n V with
  | nil => exact (hne rfl).elim
  | cons arg args ih =>
    simp only [List.foldl_cons] at H
    by_cases hrest : args = []
    · subst args
      simp only [List.foldl_nil] at H
      obtain ⟨_, H⟩ := H.to_core
      cases H with
      | app => omega
    · exact ih H hrest

/-- A nonempty application tower exposes its literal head at a strictly
smaller stratification depth. -/
theorem HasTypeStratifiedS.foldl_app_head_of_ne_nil
    {args : List SExpr} {head V : SExpr}
    (H : HasTypeStratifiedS Γ
      (args.foldl (fun f a => f.app a) head) V true n)
    (hne : args ≠ []) :
    ∃ HeadType depth,
      depth < n ∧ HasTypeStratifiedS Γ head HeadType true depth := by
  obtain ⟨HeadType, hHead⟩ := H.foldl_app_head
  have hnpos : 0 < n := H.foldl_app_depth_pos hne
  have hlen : 0 < args.length := by
    cases args with
    | nil => exact (hne rfl).elim
    | cons => simp
  exact ⟨HeadType, n - args.length, by omega, hHead⟩

/-- Peel the concrete capture tower selected by an iota descriptor and
retain the native stratified typing of its literal registered RHS head. -/
theorem _root_.Lean4Lean.Pattern.IotaRule.rhsHeadStratified
    {rec ctor : Name} {major arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (rule : Pattern.IotaRule r) {recLs : List SLevel}
    {capture : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
    {V : SExpr}
    (H : HasTypeStratifiedS Γ (r.1.applyS recLs capture) V true depth) :
    ∃ HeadType,
      HasTypeStratifiedS Γ (SExpr.mkInst recLs rule.df.rhs) HeadType true
        (depth - rule.capturePaths.length) := by
  rw [← rule.rhsApply recLs capture] at H
  simpa only [List.length_map] using H.foldl_app_head

/-- A nonempty registered capture tower exposes its fixed RHS head at a
strictly smaller depth than the typed instantiated endpoint. -/
theorem _root_.Lean4Lean.Pattern.IotaRule.rhsHeadStratified_of_nonempty
    {rec ctor : Name} {major arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (rule : Pattern.IotaRule r) {recLs : List SLevel}
    {capture : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
    {V : SExpr}
    (H : HasTypeStratifiedS Γ (r.1.applyS recLs capture) V true depth)
    (hne : rule.capturePaths ≠ []) :
    ∃ HeadType headDepth,
      headDepth < depth ∧
        HasTypeStratifiedS Γ (SExpr.mkInst recLs rule.df.rhs)
          HeadType true headDepth := by
  rw [← rule.rhsApply recLs capture] at H
  apply H.foldl_app_head_of_ne_nil
  simpa using hne

theorem HasTypeStratifiedS.isType (H : HasTypeStratifiedS Γ e A b n) :
    ∃ u, Γ ⊢ A : .sort u !! n - 1 := by
  induction H with
  | base _ ih => exact ih
  | bvar _ h => exact ⟨_, h⟩
  | const _ _ h => exact ⟨_, h⟩
  | app _ _ _ _ h => exact ⟨_, h⟩
  | lam _ _ _ h => exact ⟨_, h⟩
  | defeq _ _ h => exact ⟨_, h⟩
  | @sort' _ l _ => exact ⟨_, .base (.sort' (l := l.succ))⟩
  | @forallE _ A u _ body v _ _ => exact ⟨_, .base (.sort' (l := .imax u v))⟩

/-- Reconstruct evidence-rich self-typing from a stratified typing.

The stratified judgment retains every validity premise needed by
`IsDefEqStrong`.  Its conversion constructor now also retains the strong
type equality, so this proof is structural.  The constant case obtains the
constructor and definition witnesses from `Params.Semantic`; it does not
postulate a generic weak-to-strong conversion. -/
theorem HasTypeStratifiedS.strong
    [Params.Semantic] (H : HasTypeStratifiedS Γ e A b n) :
    IsDefEqStrong Γ e e A := by
  induction H with
  | bvar h _ ihA =>
    exact .bvar h ihA
  | sort' =>
    exact .sort
  | @const c ci Γ ls u _ hreg hlen _ ihTy =>
    let F : ∀ cl, CtorBundle c cl := fun cl =>
      (Params.Semantic.ctor (ls := ls) (Γ := Γ) hreg hlen cl).1
    have hF : ∀ cl, IsDefEqStrong Γ
        (SExpr.mkInst ls ci.type) ((F cl).rhs ls) (.sort (F cl).u) := by
      intro cl
      exact (Params.Semantic.ctor (ls := ls) (Γ := Γ) hreg hlen cl).2
    have hDef : ∀ {r : (Pattern.const c).RHS × (Pattern.const c).Check},
        Params.Pat (.const c) r →
        IsDefEqStrong Γ (r.1.applyS ls Empty.elim) (.const c ls)
          (SExpr.mkInst ls ci.type) := by
      intro r hpat
      obtain ⟨value, closed, hr, hdef⟩ := Params.Semantic.defn hpat
      subst r
      simpa only [Pattern.RHS.applyS] using
        (hdef hreg hlen : IsDefEqStrong Γ
          (.const c ls) (SExpr.mkInst ls value)
          (SExpr.mkInst ls ci.type)).symm
    exact .const hreg hlen ihTy F hF hDef
  | app _ _ _ _ _ ihA ihB ihf iha ihResult =>
    exact .appDF ihA ihB ihf iha ihResult
  | lam _ _ _ _ ihA ihB ihBody _ =>
    exact .lamDF ihA ihB ihB ihBody ihBody
  | forallE _ _ ihA ihBody =>
    exact .forallEDF ihA ihBody ihBody
  | base _ ih =>
    exact ih
  | defeq hType _ _ _ _ _ ihTerm =>
    exact .defeqDF hType ihTerm

def Ctx.WF : List SExpr → Prop
  | [] => True
  | A::Γ => WF Γ ∧ ∃ u, Γ ⊢ A : .sort u
scoped notation:65 "⊢ " Γ:36 => Ctx.WF Γ

/-! ## Reflection and evidence recovery

Once heterogeneous transitivity has been eliminated, the weak SExpr
judgment reflects into the ordinary Theory judgment constructor for
constructor.  Reification is exactly homomorphic for term lifting and
substitution; universe `succ`, `imax`, and `instL` commute only modulo the
semantic level quotient, so those cases use Theory's proved
`EqUpToLevels` transport. -/

theorem reify_lift' (e : SExpr) : (e.lift' ρ).reify = e.reify.lift' ρ := by
  induction e generalizing ρ <;> simp [SExpr.lift', SExpr.reify, VExpr.lift', *]

theorem reify_subst (e : SExpr) :
    (e.subst σ).reify = e.reify.subst (fun i => (σ i).reify) := by
  induction e generalizing σ with
  | bvar => rfl
  | sort => rfl
  | const => rfl
  | app f a ihf iha =>
    simp only [SExpr.subst, SExpr.reify, VExpr.subst, ihf, iha]
  | lam A e ihA ihe | forallE A e ihA ihe =>
    simp only [SExpr.subst, SExpr.reify, VExpr.subst, ihA]
    rw [ihe]
    congr 2
    funext i
    cases i with
    | zero => rfl
    | succ i =>
      simp [SExpr.Subst.lift, VExpr.Subst.lift, reify_lift',
        VExpr.lift_eq_lift']

theorem reify_inst (e a : SExpr) :
    (e.inst a).reify = e.reify.inst a.reify := by
  rw [SExpr.inst, VExpr.inst_eq, reify_subst]
  congr 2
  funext i
  cases i <;> rfl

theorem Lookup.reify (H : SExpr.Lookup Γ i A) :
    Lean4Lean.Lookup (Γ.map SExpr.reify) i A.reify := by
  induction H with
  | zero =>
    rw [reify_lift', ← VExpr.lift_eq_lift']
    exact Lean4Lean.Lookup.zero
  | succ _ ih =>
    rw [reify_lift', ← VExpr.lift_eq_lift']
    exact Lean4Lean.Lookup.succ ih

theorem _root_.Lean4Lean.VEnv.EqUpToLevels.reify_of_mk_eq
    (he : e.LevelWF Params.univs) (h : SExpr.mk e = s) :
    VEnv.EqUpToLevels Params.univs e s.reify := by
  subst s
  exact VEnv.EqUpToLevels.reify_mk he

theorem _root_.Lean4Lean.VEnv.EqUpToLevels.reify_refl (e : SExpr) :
    VEnv.EqUpToLevels Params.univs e.reify e.reify := by
  simpa only [SExpr.mk_reify] using
    (VEnv.EqUpToLevels.reify_mk (SExpr.reify_levelWF e))

theorem mk_instL_map_reify (e : VExpr) (ls : List SLevel) :
    SExpr.mk (e.instL (ls.map SLevel.reify)) = SExpr.mkInst ls e := by
  let vls := ls.map SLevel.reify
  have hlevels : ∀ l ∈ vls, l.WF Params.univs := by
    intro l hl
    simp only [vls, List.mem_map] at hl
    obtain ⟨sl, _, rfl⟩ := hl
    exact SLevel.reify_wf sl
  have hvls : vls.map SLevel.mk = ls := by
    change (ls.map SLevel.reify).map SLevel.mk = ls
    rw [List.map_map]
    exact List.map_id''' ls fun sl _ => SLevel.mk_reify sl
  have h := (SExpr.mkInst_map_mk (e := e) hlevels).symm
  rw [hvls] at h
  exact h

/-- Simultaneously change both endpoints and the declared type of a Theory
judgment along universe-representative equivalence.  This uses only the
proved ordered-environment strengthening layer. -/
theorem _root_.Lean4Lean.VEnv.IsDefEq.alignEqUpToLevels
    (hΓ : OnCtx Γ (Params.env.IsType Params.univs))
    (H : Params.env.IsDefEq Params.univs Γ e₁ e₂ A)
    (he₁ : VEnv.EqUpToLevels Params.univs e₁ e₁')
    (he₂ : VEnv.EqUpToLevels Params.univs e₂ e₂')
    (hA : VEnv.EqUpToLevels Params.univs A A') :
    Params.env.IsDefEq Params.univs Γ e₁' e₂' A' := by
  let W := VEnv.CtxStrong.strong Params.henv hΓ
  have hs := H.strong Params.henv hΓ
  have hterm :=
    VEnv.EqUpToLevels.defeq Params.henv Params.henv.strong W hs he₁ he₂
  obtain ⟨u, htype⟩ := hs.isType' Params.henv Params.henv.strong W
  have hrefl := (VEnv.EqUpToLevels.refl W.levelWF htype).1
  have htype' := VEnv.EqUpToLevels.defeq Params.henv Params.henv.strong W
    htype hrefl hA
  exact .defeqDF htype'.defeq hterm.defeq

/-- Reflect the quotient syntax's weak judgment back into Theory.  The
target context validity is explicit so binder cases can extend it with the
typing recovered from their translated premises. -/
theorem IsDefEq.reify (H : IsDefEq Γ e₁ e₂ A) :
    OnCtx (Γ.map SExpr.reify) (Params.env.IsType Params.univs) →
    Params.env.IsDefEq Params.univs (Γ.map SExpr.reify)
      e₁.reify e₂.reify A.reify := by
  intro hΓ
  induction H with
  | bvar h => exact .bvar h.reify
  | symm _ ih => exact (ih hΓ).symm
  | trans _ _ ih₁ ih₂ => exact (ih₁ hΓ).trans (ih₂ hΓ)
  | @sort Γ l =>
    have hl : l.reify.WF Params.univs := SLevel.reify_wf l
    have hbase : Params.env.IsDefEq Params.univs (Γ.map SExpr.reify)
        (.sort l.reify) (.sort l.reify) (.sort l.reify.succ) :=
      .sortDF hl hl rfl
    have htype : VEnv.EqUpToLevels Params.univs
        (VExpr.sort l.reify.succ) (SExpr.sort l.succ).reify :=
      .reify_of_mk_eq (show l.reify.succ.WF Params.univs from hl)
        (by simp only [SExpr.mk, SLevel.mk_succ hl, SLevel.mk_reify])
    exact hbase.alignEqUpToLevels hΓ
      (.reify_refl (SExpr.sort l)) (.reify_refl (SExpr.sort l)) htype
  | @const c ci Γ ls hreg hlen =>
    let vls := ls.map SLevel.reify
    have hlevels : ∀ l ∈ vls, l.WF Params.univs := by
      intro l hl
      simp only [vls, List.mem_map] at hl
      obtain ⟨sl, _, rfl⟩ := hl
      exact SLevel.reify_wf sl
    have hbase : Params.env.IsDefEq Params.univs (Γ.map SExpr.reify)
        (.const c vls) (.const c vls) (ci.type.instL vls) :=
      .constDF hreg hlevels hlevels (by simpa [vls] using hlen)
        (List.Forall₂.rfl fun _ _ => rfl)
    let W := VEnv.CtxStrong.strong Params.henv hΓ
    have htype : VEnv.EqUpToLevels Params.univs
        (ci.type.instL vls) (SExpr.mkInst ls ci.type).reify :=
      .reify_of_mk_eq (hbase.levelWF W.levelWF).2.2
        (by simpa only [vls] using mk_instL_map_reify ci.type ls)
    exact hbase.alignEqUpToLevels hΓ
      (.reify_refl (SExpr.const c ls)) (.reify_refl (SExpr.const c ls)) htype
  | @appDF Γ f f' A B a a' _ _ ihf iha =>
    simpa only [SExpr.reify, reify_inst] using
      VEnv.IsDefEq.appDF (ihf hΓ) (iha hΓ)
  | @lamDF Γ A A' u body body' B _ _ ihA ihBody =>
    have hA := ihA hΓ
    have hΓ' : OnCtx (A.reify :: Γ.map SExpr.reify)
        (Params.env.IsType Params.univs) :=
      ⟨hΓ, ⟨_, hA.hasType.1⟩⟩
    exact .lamDF hA (ihBody hΓ')
  | @forallEDF Γ A A' u body body' v _ _ ihA ihBody =>
    have hA := ihA hΓ
    have hΓ' : OnCtx (A.reify :: Γ.map SExpr.reify)
        (Params.env.IsType Params.univs) :=
      ⟨hΓ, ⟨_, hA.hasType.1⟩⟩
    have hbase := VEnv.IsDefEq.forallEDF hA (ihBody hΓ')
    have hu : u.reify.WF Params.univs := SLevel.reify_wf u
    have hv : v.reify.WF Params.univs := SLevel.reify_wf v
    have htype : VEnv.EqUpToLevels Params.univs
        (VExpr.sort (.imax u.reify v.reify)) (SExpr.sort (.imax u v)).reify :=
      .reify_of_mk_eq
        (show (VLevel.imax u.reify v.reify).WF Params.univs from ⟨hu, hv⟩)
        (by simp only [SExpr.mk, SLevel.mk_imax hu hv, SLevel.mk_reify])
    exact hbase.alignEqUpToLevels hΓ
      (.reify_refl (SExpr.forallE A body))
      (.reify_refl (SExpr.forallE A' body')) htype
  | defeqDF _ _ ihA ihe => exact .defeqDF (ihA hΓ) (ihe hΓ)
  | @beta A Γ e B e' _ _ ihBody ihArg =>
    have harg := ihArg hΓ
    have hΓ' : OnCtx (A.reify :: Γ.map SExpr.reify)
        (Params.env.IsType Params.univs) :=
      ⟨hΓ, harg.isType Params.henv hΓ⟩
    simpa only [SExpr.reify, reify_inst] using
      VEnv.IsDefEq.beta (ihBody hΓ') harg
  | @eta Γ e A B _ ihe =>
    simpa only [SExpr.reify, reify_lift', ← VExpr.lift_eq_lift'] using
      VEnv.IsDefEq.eta (ihe hΓ)
  | @proofIrrel Γ p h h' _ _ _ ihp ihh ihh' =>
    have hp := ihp hΓ
    have hz : SLevel.zero.reify ≈ VLevel.zero :=
      SLevel.equiv_of_mk_eq (SLevel.reify_wf .zero) (by trivial)
        (by simp only [SLevel.mk_reify, SLevel.mk_zero])
    have hp' := hp.alignEqUpToLevels hΓ
      (.reify_refl p) (.reify_refl p)
      (VEnv.EqUpToLevels.sort (SLevel.reify_wf .zero) (by trivial) hz)
    exact .proofIrrel hp' (ihh hΓ) (ihh' hΓ)
  | @extra df Γ ls hreg hlen =>
    let vls := ls.map SLevel.reify
    have hlevels : ∀ l ∈ vls, l.WF Params.univs := by
      intro l hl
      simp only [vls, List.mem_map] at hl
      obtain ⟨sl, _, rfl⟩ := hl
      exact SLevel.reify_wf sl
    have hbase : Params.env.IsDefEq Params.univs (Γ.map SExpr.reify)
        (df.lhs.instL vls) (df.rhs.instL vls) (df.type.instL vls) :=
      .extra hreg hlevels (by simpa [vls] using hlen)
    let W := VEnv.CtxStrong.strong Params.henv hΓ
    have hwf := hbase.levelWF W.levelWF
    have hlhs : VEnv.EqUpToLevels Params.univs
        (df.lhs.instL vls) (SExpr.mkInst ls df.lhs).reify :=
      .reify_of_mk_eq hwf.1
        (by simpa only [vls] using mk_instL_map_reify df.lhs ls)
    have hrhs : VEnv.EqUpToLevels Params.univs
        (df.rhs.instL vls) (SExpr.mkInst ls df.rhs).reify :=
      .reify_of_mk_eq hwf.2.1
        (by simpa only [vls] using mk_instL_map_reify df.rhs ls)
    have htype : VEnv.EqUpToLevels Params.univs
        (df.type.instL vls) (SExpr.mkInst ls df.type).reify :=
      .reify_of_mk_eq hwf.2.2
        (by simpa only [vls] using mk_instL_map_reify df.type ls)
    exact hbase.alignEqUpToLevels hΓ hlhs hrhs htype

/-- A well-formed SExpr context reifies to a well-formed Theory context. -/
theorem Ctx.WF.reify (H : Ctx.WF Γ) :
    OnCtx (Γ.map SExpr.reify) (Params.env.IsType Params.univs) := by
  induction Γ with
  | nil => trivial
  | cons A Γ ih =>
    obtain ⟨hΓ, u, hA⟩ := H
    have hΓ' := ih hΓ
    exact ⟨hΓ', ⟨u.reify, hA.reify hΓ'⟩⟩

/-- Translate a well-formed Theory context through `SExpr.mk`.  This is the
context counterpart of `VEnv.IsDefEqStrong.mkS`; generated reduction sites
and the contextual adequacy tower use the two translations together. -/
theorem Ctx.WF.mkS [Params.Semantic]
    (H : OnCtx Γ (Params.env.IsType Params.univs)) :
    Ctx.WF (Γ.map SExpr.mk) := by
  induction Γ with
  | nil => trivial
  | cons A Γ ih =>
    obtain ⟨hΓ, u, hA⟩ := H
    have hΓS := ih hΓ
    have hAS := (hA.strong Params.henv hΓ).mkS
    exact ⟨hΓS, ⟨SLevel.mk u, hAS.defeq⟩⟩

/-- Recover the proof-carrying judgment from a weak SExpr derivation in a
well-formed context.  The proof reflects to Theory, uses its clean ordered
environment strengthening theorem, and translates back; it does not depend
on Theory's transitional uniqueness or injectivity declarations. -/
theorem IsDefEq.strong [Params.Semantic]
    (hΓ : Ctx.WF Γ) (H : IsDefEq Γ e₁ e₂ A) :
    IsDefEqStrong Γ e₁ e₂ A := by
  have hΓ' := hΓ.reify
  have hV := (H.reify hΓ').strong Params.henv hΓ'
  have hS := hV.mkS
  have hctx : (Γ.map SExpr.reify).map SExpr.mk = Γ := by
    rw [List.map_map]
    exact List.map_id''' Γ fun term _ => SExpr.mk_reify term
  simpa only [hctx, SExpr.mk_reify] using hS

variable (HasType : List SExpr → SExpr → SExpr → Prop)
inductive Ctx.Subst (Γ : List SExpr) : SExpr.Subst → List SExpr → Prop where
  | nil : Ctx.Subst Γ σ []
  | cons : Ctx.Subst Γ σ.tail Δ → HasType Γ σ.head (A.subst σ.tail) → Ctx.Subst Γ σ (A::Δ)

variable {HasType}
theorem Ctx.Subst.head (H : Ctx.Subst HasType Γ σ (A::Δ)) : HasType Γ σ.head (A.subst σ.tail) :=
  let .cons _ H := H; H

theorem Ctx.Subst.tail (H : Ctx.Subst HasType Γ σ (A::Δ)) : Ctx.Subst HasType Γ σ.tail Δ :=
  let .cons H _ := H; H

theorem Ctx.Subst.lookup (H : Ctx.Subst HasType Γ σ Δ) :
    Lookup Δ i A → HasType Γ (σ i) (A.subst σ) := by
  intro h
  induction H generalizing i A with
  | nil => cases h
  | @cons Δ σ A₀ H hhead ih =>
    cases h with
    | zero =>
      simpa only [show σ 0 = σ.head from rfl, SExpr.lift_subst] using hhead
    | succ h =>
      change HasType Γ (σ.tail _) (_)
      simpa only [SExpr.lift_subst] using ih h

/-- Change only the evidence relation carried by a substitution. -/
theorem Ctx.Subst.imp
    (f : ∀ {Γ e A}, HasType Γ e A → HasType' Γ e A)
    (H : Ctx.Subst HasType Γ σ Δ) : Ctx.Subst HasType' Γ σ Δ := by
  induction H with
  | nil => exact .nil
  | cons _ h ih => exact .cons ih (f h)

theorem Ctx.Subst.cons' (H1 : Ctx.Subst HasType Γ σ Δ) (H2 : HasType Γ e (A.subst σ)) :
    Ctx.Subst HasType Γ (σ.cons e) (A::Δ) := .cons H1 H2

theorem Ctx.Subst.lift_r
    (weak : ∀ {Γ Δ e A ρ}, Ctx.Lift' ρ Γ Δ → HasType Γ e A →
      HasType Δ (e.lift' ρ) (A.lift' ρ))
    (H1 : Ctx.Subst HasType Θ σ Γ) (H2 : Ctx.Lift' ρ Θ Δ) :
    Ctx.Subst HasType Δ (σ.lift_r ρ) Γ := by
  induction H1 with
  | nil => exact .nil
  | @cons Δ' σ' A H h ih =>
    refine .cons ih ?_
    change HasType Δ (σ'.head.lift' ρ) (A.subst (σ'.tail.lift_r ρ))
    rw [← SExpr.lift'_subst]
    exact weak H2 h

theorem Ctx.Subst.lift
    (weak : ∀ {Γ Δ e A ρ}, Ctx.Lift' ρ Γ Δ → HasType Γ e A →
      HasType Δ (e.lift' ρ) (A.lift' ρ))
    (bvar : ∀ {Γ i A}, Lookup Γ i A → HasType Γ (bvar i) A)
    (H : Ctx.Subst HasType Γ σ Δ) : Ctx.Subst HasType (A.subst σ :: Γ) σ.lift (A :: Δ) := by
  have : σ.lift.tail = σ.lift_r (.skip .refl) := by
    funext i; simp [SExpr.Subst.tail, SExpr.Subst.lift, SExpr.Subst.lift_r]
  refine .cons (this ▸ .lift_r weak H .one) (this ▸ bvar ?_)
  rw [← lift'_subst, ← SExpr.lift]; exact .zero

theorem Ctx.Subst.id
    (weak : ∀ {Γ Δ e A ρ}, Ctx.Lift' ρ Γ Δ → HasType Γ e A →
      HasType Δ (e.lift' ρ) (A.lift' ρ))
    (bvar : ∀ {Γ i A}, Lookup Γ i A → HasType Γ (bvar i) A) :
    ∀ {Γ}, Ctx.Subst HasType Γ .id Γ
  | [] => .nil
  | A :: Γ => by
    have htail : SExpr.Subst.id.tail = SExpr.Subst.id.lift_r (.skip .refl) := by
      funext i
      rfl
    refine .cons (htail ▸ (Ctx.Subst.id weak bvar).lift_r weak (.skip .refl)) ?_
    change HasType (A :: Γ) (.bvar 0) (A.subst SExpr.Subst.id.tail)
    rw [htail, ← SExpr.lift'_subst, SExpr.subst_id]
    exact bvar .zero

theorem Ctx.Subst.one
    (weak : ∀ {Γ Δ e A ρ}, Ctx.Lift' ρ Γ Δ → HasType Γ e A →
      HasType Δ (e.lift' ρ) (A.lift' ρ))
    (bvar : ∀ {Γ i A}, Lookup Γ i A → HasType Γ (bvar i) A)
    (H : HasType Γ e A) : Ctx.Subst HasType Γ (.one e) (A::Γ) :=
  .cons (.id weak bvar) (by simpa)

inductive Ctx.SubstEq (Γ₀ : List SExpr) : SExpr.Subst → SExpr.Subst → List SExpr → Prop where
  | nil : Ctx.SubstEq Γ₀ .id .id Γ₀
  /-- A pure context embedding is an equality substitution.  This base case
  is what makes equality substitutions stable under entering a binder; the
  old identity-only relation could not represent the weakened tail of a
  lifted substitution. -/
  | ofLift : Ctx.Lift' ρ Γ Γ₀ → Ctx.SubstEq Γ₀ ρ.toSubst ρ.toSubst Γ
  | cons : Ctx.SubstEq Γ₀ σ.tail σ'.tail Γ →
    Γ ⊢ A : .sort u →
    Γ₀ ⊢ σ.head ≡ σ'.head : A.subst σ.tail →
    Ctx.SubstEq Γ₀ σ σ' (A :: Γ)

theorem Ctx.Subst.ofLookup
    (H : ∀ {i A}, Lookup Δ i A → HasType Γ (σ i) (A.subst σ)) :
    Ctx.Subst HasType Γ σ Δ := by
  induction Δ generalizing σ with
  | nil => exact .nil
  | cons A Δ ih =>
    refine .cons (ih (σ := σ.tail) fun {i B} h => ?_) ?_
    · change HasType Γ (σ (i + 1)) (B.subst σ.tail)
      simpa only [SExpr.lift_subst] using H (.succ h)
    · change HasType Γ (σ 0) (A.subst σ.tail)
      simpa only [SExpr.lift_subst] using H (.zero (ty := A) (Γ := Δ))

theorem Ctx.Lift'.toSubst (W : Ctx.Lift' ρ Γ Γ') :
    Ctx.Subst (· ⊢ · : ·) Γ' ρ.toSubst Γ := by
  apply Ctx.Subst.ofLookup
  intro i A h
  simpa only [Lift.toSubst_apply, SExpr.subst_toSubst] using
    (IsDefEq.bvar (h.weak' W))

theorem Ctx.SubstEq.left (W : Ctx.SubstEq Γ₀ σ σ' Γ) : Ctx.Subst (· ⊢ · : ·) Γ₀ σ Γ := by
  induction W with
  | nil =>
    apply Ctx.Subst.ofLookup
    intro i A h
    change Γ₀ ⊢ SExpr.Subst.id i : A.subst SExpr.Subst.id
    rw [SExpr.subst_id]
    exact IsDefEq.bvar h
  | ofLift W => exact W.toSubst
  | cons _ _ h ih => exact .cons ih h.hasType.1

/-- Forget the right side of an equality substitution while retaining the
same evidence format.  This is the diagonal used by simultaneous
heterogeneous substitution proofs. -/
theorem Ctx.SubstEq.leftEq (W : Ctx.SubstEq Γ₀ σ σ' Γ) :
    Ctx.SubstEq Γ₀ σ σ Γ := by
  induction W with
  | nil => exact .nil
  | ofLift W => exact .ofLift W
  | cons _ hA hhead ih => exact .cons ih hA hhead.hasType.1

theorem Ctx.SubstEq.lookup (W : Ctx.SubstEq Γ₀ σ σ' Γ) :
    Lookup Γ i A → Γ₀ ⊢ σ i ≡ σ' i : A.subst σ := by
  intro h
  induction W generalizing i A with
  | nil =>
    change Γ₀ ⊢ .bvar i ≡ .bvar i : A.subst .id
    rw [subst_id]
    exact .bvar h
  | ofLift W =>
    simpa only [Lift.toSubst_apply, SExpr.subst_toSubst] using
      (IsDefEq.bvar (h.weak' W))
  | cons W' hA' hhead ih =>
    cases h with
    | zero =>
      simp only [show ∀ (s : SExpr.Subst), s 0 = s.head from fun _ => rfl, lift_subst]
      exact hhead
    | succ h' =>
      simp only [show ∀ (s : SExpr.Subst) n, s (n+1) = s.tail n from fun _ _ => rfl,
        lift_subst]
      exact ih h'

/-- The core weakening proof is placed before equality-substitution lifting:
the latter must weaken every equality stored in the substitution. -/
theorem IsDefEq.weakCore (W : Ctx.Lift' ρ Γ Γ') (H : Γ ⊢ e1 ≡ e2 : A) :
    Γ' ⊢ e1.lift' ρ ≡ e2.lift' ρ : A.lift' ρ := by
  induction H generalizing ρ Γ' with
  | bvar h => refine .bvar (h.weak' W)
  | symm _ ih => exact .symm (ih W)
  | trans _ _ ih1 ih2 => exact .trans (ih1 W) (ih2 W)
  | sort => exact .sort
  | const h1 h2 => rw [((henv.closedC h1).mkInstS).lift'_eq .zero]; exact .const h1 h2
  | appDF _ _ ih1 ih2 => exact SExpr.lift'_inst_hi .. ▸ .appDF (ih1 W) (ih2 W)
  | lamDF _ _ ih1 ih2 => exact .lamDF (ih1 W) (ih2 W.cons)
  | forallEDF _ _ ih1 ih2 => exact .forallEDF (ih1 W) (ih2 W.cons)
  | defeqDF _ _ ih1 ih2 => exact .defeqDF (ih1 W) (ih2 W)
  | beta _ _ ih1 ih2 =>
    rw [SExpr.lift'_inst_hi, SExpr.lift'_inst_hi]
    exact .beta (ih1 W.cons) (ih2 W)
  | eta _ ih => refine cast ?_ (IsDefEq.eta (ih W)); congr 1; simp [← SExpr.lift'_comp]
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel (ih1 W) (ih2 W) (ih3 W)
  | extra h1 h2 =>
    have ⟨⟨hA1, _⟩, hA2, hA3⟩ := henv.closed.2 h1
    rw [hA1.mkInstS.lift'_eq .zero, hA2.mkInstS.lift'_eq .zero,
      hA3.mkInstS.lift'_eq .zero]
    exact .extra h1 h2

theorem Ctx.SubstEq.weak' (W₀ : Ctx.Lift' ρ Γ₀ Γ₁)
    (W : Ctx.SubstEq Γ₀ σ σ' Γ) :
    Ctx.SubstEq Γ₁ (σ.lift_r ρ) (σ'.lift_r ρ) Γ := by
  induction W with
  | nil =>
    have hσ : SExpr.Subst.id.lift_r ρ = ρ.toSubst := by
      funext i
      rfl
    simpa only [hσ] using Ctx.SubstEq.ofLift W₀
  | @ofLift ρ' Γ' W' =>
    have h := Ctx.SubstEq.ofLift (W'.comp W₀)
    have heq : ρ'.toSubst.lift_r ρ = (ρ'.comp ρ).toSubst := by
      funext i
      simp only [SExpr.Subst.lift_r, Lift.toSubst_apply, SExpr.lift',
        Lift.liftVar_comp]
    simpa only [heq] using h
  | @cons Γ' A u τ τ' W hA hhead ih =>
    have ht : (τ.lift_r ρ).tail = τ.tail.lift_r ρ := by
      funext i
      rfl
    have ht' : (τ'.lift_r ρ).tail = τ'.tail.lift_r ρ := by
      funext i
      rfl
    refine .cons ?_ hA ?_
    · simpa only [ht, ht'] using ih
    · rw [ht, ← SExpr.lift'_subst]
      exact hhead.weakCore W₀

theorem Ctx.SubstEq.lift (W : Ctx.SubstEq Γ₀ σ σ' Γ)
    (hA : Γ ⊢ A : .sort u) :
    Ctx.SubstEq (A.subst σ :: Γ₀) σ.lift σ'.lift (A :: Γ) := by
  have W' := W.weak' (Ctx.Lift'.one (Γ := Γ₀) (A := A.subst σ))
  have hσ : σ.lift.tail = σ.lift_r (.skip .refl) := by
    funext i
    rfl
  have hσ' : σ'.lift.tail = σ'.lift_r (.skip .refl) := by
    funext i
    rfl
  refine .cons (σ := σ.lift) (σ' := σ'.lift) ?_ hA ?_
  · simpa only [hσ, hσ'] using W'
  · rw [hσ, ← SExpr.lift'_subst]
    exact IsDefEq.bvar (Lookup.zero (ty := A.subst σ) (Γ := Γ₀))

theorem IsDefEq.weak' (W : Ctx.Lift' ρ Γ Γ') (H : Γ ⊢ e1 ≡ e2 : A) :
    Γ' ⊢ e1.lift' ρ ≡ e2.lift' ρ : A.lift' ρ := H.weakCore W

/-- Weak definitional equality is stable under one typed substitution.

The two endpoints deliberately use the same substitution.  Heterogeneous
substitution needs the domain/codomain evidence retained by
`IsDefEqStrong`; erasing that evidence first makes the corresponding claim
false for dependent application and beta. -/
theorem IsDefEq.subst (W : Ctx.Subst (fun Γ e A => Γ ⊢ e : A) Γ₀ σ Γ)
    (H : Γ ⊢ e1 ≡ e2 : A) :
    Γ₀ ⊢ e1.subst σ ≡ e2.subst σ : A.subst σ := by
  induction H generalizing Γ₀ σ with
  | bvar h => exact W.lookup h
  | symm _ ih => exact (ih W).symm
  | trans _ _ ih₁ ih₂ => exact (ih₁ W).trans (ih₂ W)
  | sort => exact .sort
  | const hreg hlen =>
    rw [((henv.closedC hreg).mkInstS).subst_eq .zero]
    exact .const hreg hlen
  | appDF _ _ ihf iha =>
    rw [SExpr.subst_inst]
    exact .appDF (ihf W) (iha W)
  | lamDF _ _ ihA ihBody =>
    exact .lamDF (ihA W)
      (by simpa only [SExpr.subst] using
        ihBody (W.lift IsDefEq.weakCore IsDefEq.bvar))
  | forallEDF _ _ ihA ihBody =>
    exact .forallEDF (ihA W)
      (by simpa only [SExpr.subst] using
        ihBody (W.lift IsDefEq.weakCore IsDefEq.bvar))
  | defeqDF _ _ ihA ihe => exact .defeqDF (ihA W) (ihe W)
  | beta _ _ ihBody ihArg =>
    simpa only [SExpr.subst, SExpr.subst_inst] using
      (IsDefEq.beta
        (by simpa only [SExpr.subst] using
          ihBody (W.lift IsDefEq.weakCore IsDefEq.bvar))
        (ihArg W))
  | @eta Γ e A B _ ihe =>
    have hout := IsDefEq.eta (ihe W)
    have htail : σ.lift.tail = σ.lift_r (.skip .refl) := by
      funext i
      rfl
    have heq : e.lift.subst σ.lift = (e.subst σ).lift := by
      rw [SExpr.lift_subst, htail, ← SExpr.lift'_subst]
    simpa only [SExpr.subst, SExpr.Subst.lift, heq] using hout
  | proofIrrel _ _ _ ihp ihh ihh' =>
    exact .proofIrrel (ihp W) (ihh W) (ihh' W)
  | extra hreg hlen =>
    have ⟨⟨hlhs, _⟩, hrhs, htype⟩ := henv.closed.2 hreg
    rw [hlhs.mkInstS.subst_eq .zero, hrhs.mkInstS.subst_eq .zero,
      htype.mkInstS.subst_eq .zero]
    exact .extra hreg hlen

/-- A strong derivation retains enough local validity evidence to show that
each endpoint respects an equality substitution.  Both conclusions are
typed at the left-substituted source type; keeping them together makes
symmetry and transitivity structural instead of requiring an invalid
symmetry operation on weak equality substitutions. -/
theorem IsDefEqStrong.substCongr (W : Ctx.SubstEq Γ₀ σ σ' Γ)
    (H : IsDefEqStrong Γ e1 e2 A) :
    (Γ₀ ⊢ e1.subst σ ≡ e1.subst σ' : A.subst σ) ∧
    (Γ₀ ⊢ e2.subst σ ≡ e2.subst σ' : A.subst σ) := by
  induction H generalizing Γ₀ σ σ' with
  | bvar h _ _ =>
    exact ⟨W.lookup h, W.lookup h⟩
  | symm _ ih =>
    exact ⟨(ih W).2, (ih W).1⟩
  | trans _ _ ih₁ ih₂ =>
    exact ⟨(ih₁ W).1, (ih₂ W).2⟩
  | sort =>
    exact ⟨.sort, .sort⟩
  | const hreg hlen _ _ _ =>
    constructor <;>
      rw [((henv.closedC hreg).mkInstS).subst_eq .zero] <;>
      exact .const hreg hlen
  | @appDF Γ A u B v f f' a a' hA hCod hf ha hB
      ihA ihCod ihf iha ihB =>
    have hf' := ihf W
    have ha' := iha W
    have hcod : Γ₀ ⊢
        (B.subst σ.lift).inst (a.subst σ) ≡
        (B.subst σ.lift).inst (a'.subst σ) : .sort v := by
      simpa only [SExpr.subst, SExpr.subst_inst] using hB.defeq.subst W.left
    constructor
    · simpa only [SExpr.subst, SExpr.subst_inst] using
        (IsDefEq.appDF hf'.1 ha'.1)
    · have happ := IsDefEq.appDF hf'.2 ha'.2
      have happ' := hcod.symm.defeqDF happ
      simpa only [SExpr.subst, SExpr.subst_inst] using happ'
  | @lamDF Γ A A' u B v body body' hA hB hB' hBody hBody'
      ihA ihB ihB' ihBody ihBody' =>
    have WA := W.lift hA.defeq.hasType.1
    have WA' := W.lift hA.defeq.hasType.2
    have hdom := ihA W
    have hbody := ihBody WA
    have hbody' := ihBody' WA'
    constructor
    · simpa only [SExpr.subst] using
        (IsDefEq.lamDF hdom.1 hbody.1)
    · have hlam := IsDefEq.lamDF hdom.2 hbody'.2
      have hPi : Γ₀ ⊢
          .forallE (A.subst σ) (B.subst σ.lift) ≡
          .forallE (A'.subst σ) (B.subst σ.lift) : .sort (.imax u v) :=
        .forallEDF (hA.defeq.subst W.left)
          (hB.defeq.subst (W.left.lift IsDefEq.weakCore IsDefEq.bvar))
      simpa only [SExpr.subst] using hPi.symm.defeqDF hlam
  | @forallEDF Γ A A' u body body' v hA hBody hBody'
      ihA ihBody ihBody' =>
    have hdom := ihA W
    constructor
    · simpa only [SExpr.subst] using
        (IsDefEq.forallEDF hdom.1
          (ihBody (W.lift hA.defeq.hasType.1)).1)
    · simpa only [SExpr.subst] using
        (IsDefEq.forallEDF hdom.2
          (ihBody' (W.lift hA.defeq.hasType.2)).2)
  | defeqDF hA _ ihA ihe =>
    have htype := hA.defeq.subst W.left
    exact ⟨htype.defeqDF (ihe W).1, htype.defeqDF (ihe W).2⟩
  | beta _ _ _ _ ihBody ihArg ihApp ihInst =>
    exact ⟨(ihApp W).1, (ihInst W).1⟩
  | eta _ _ ihe ihLam =>
    exact ⟨(ihLam W).1, (ihe W).1⟩
  | proofIrrel _ _ _ ihp ihh ihh' =>
    exact ⟨(ihh W).1, (ihh' W).1⟩
  | defn hreg hlen _ _ _ _ _ _ _ ihRhs =>
    constructor
    · rw [((henv.closedC hreg).mkInstS).subst_eq .zero]
      exact .const hreg hlen
    · exact (ihRhs W).1
  | extra _ _ _ ihLeft ihRight =>
    exact ⟨(ihLeft W).1, (ihRight W).1⟩

/-- Heterogeneous substitution for the evidence-rich judgment, returned in
the weak judgment consumed by the logical relation. -/
theorem IsDefEqStrong.subst (W : Ctx.SubstEq Γ₀ σ σ' Γ)
    (H : IsDefEqStrong Γ e1 e2 A) :
    Γ₀ ⊢ e1.subst σ ≡ e2.subst σ' : A.subst σ :=
  (H.defeq.subst W.left).trans (H.substCongr W).2

/-- A certified local contraction remains certified after weakening.  The
finite check list is transported pointwise, so downstream reduction rules do
not need to unpack and rebuild the certificate themselves. -/
def _root_.Lean4Lean.Pattern.Action.weak' (action : Pattern.Action Γ r e m1 m2 A)
    (W : Ctx.Lift' ρ Γ Γ') :
    Pattern.Action Γ' r (e.lift' ρ) m1
      (fun path => (m2 path).lift' ρ) (A.lift' ρ) := by
  let dfs' := action.dfs.map fun d =>
    (d.1.lift' ρ, d.2.1.lift' ρ, d.2.2.lift' ρ)
  refine {
    pat := action.pat
    matched := action.matched.lift'
    dfs := dfs'
    defeqs := ?_
    checked := ?_
    sound := ?_ }
  · rw [← Pattern.Check.defeqsS_lift', ← action.defeqs]
    simp [dfs', Function.comp_def]
  · intro a b B hab
    simp only [dfs', List.mem_map] at hab
    obtain ⟨⟨B₀, a₀, b₀⟩, hab, heq⟩ := hab
    have hB : B₀.lift' ρ = B := congrArg Prod.fst heq
    have hab' : (a₀.lift' ρ, b₀.lift' ρ) = (a, b) := congrArg Prod.snd heq
    have ha : a₀.lift' ρ = a := congrArg Prod.fst hab'
    have hb : b₀.lift' ρ = b := congrArg Prod.snd hab'
    subst B
    subst a
    subst b
    exact (action.checked a₀ b₀ B₀ hab).weak' W
  · simpa only [Pattern.RHS.lift'_applyS] using action.sound.weak' W

/-- Evidence-rich equality is stable under context embeddings.  Constants
are rebuilt from the semantic environment at the target context, avoiding
any false assumption that the abstract constructor bundle's SExpr fields are
syntactically closed; local extension leaves weaken their finite `Action`
certificate pointwise. -/
theorem IsDefEqStrong.weak' [Params.Semantic]
    (W : Ctx.Lift' ρ Γ Γ')
    (H : IsDefEqStrong Γ e1 e2 A) :
    IsDefEqStrong Γ' (e1.lift' ρ) (e2.lift' ρ) (A.lift' ρ) := by
  induction H generalizing ρ Γ' with
  | bvar h _ ihA => exact .bvar (h.weak' W) (ihA W)
  | symm _ ih => exact (ih W).symm
  | trans _ _ ih1 ih2 => exact (ih1 W).trans (ih2 W)
  | sort => exact .sort
  | @const c ci Γ ls u hreg hlen hTy F hF hDef ihTy ihF ihDef =>
    rw [((Params.henv.closedC hreg).mkInstS).lift'_eq .zero]
    have hTy' := ihTy W
    rw [((Params.henv.closedC hreg).mkInstS).lift'_eq .zero] at hTy'
    let F' : ∀ cl, CtorBundle c cl := fun cl =>
      (Params.Semantic.ctor (ls := ls) (Γ := Γ') hreg hlen cl).1
    have hF' : ∀ cl, IsDefEqStrong Γ'
        (SExpr.mkInst ls ci.type) ((F' cl).rhs ls) (.sort (F' cl).u) := by
      intro cl
      exact (Params.Semantic.ctor (ls := ls) (Γ := Γ') hreg hlen cl).2
    have hDef' : ∀ {r : (Pattern.const c).RHS × (Pattern.const c).Check},
        Params.Pat (.const c) r →
        IsDefEqStrong Γ' (r.1.applyS ls Empty.elim) (.const c ls)
          (SExpr.mkInst ls ci.type) := by
      intro r hpat
      obtain ⟨value, closed, hr, hdef⟩ := Params.Semantic.defn hpat
      subst r
      simpa only [Pattern.RHS.applyS] using
        (hdef hreg hlen : IsDefEqStrong Γ'
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
  | @eta Γ e A B hTerm hLam ihTerm ihLam =>
    have hLam' : IsDefEqStrong Γ'
        (.lam (A.lift' ρ) ((e.lift' ρ).lift.app (.bvar 0)))
        (.lam (A.lift' ρ) ((e.lift' ρ).lift.app (.bvar 0)))
        (.forallE (A.lift' ρ) (B.lift' ρ.cons)) := by
      simpa [SExpr.lift, ← SExpr.lift'_comp] using ihLam W
    simpa [SExpr.lift, ← SExpr.lift'_comp] using
      IsDefEqStrong.eta (ihTerm W) hLam'
  | proofIrrel _ _ _ ihProp ihLeft ihRight =>
    exact .proofIrrel (ihProp W) (ihLeft W) (ihRight W)
  | @defn c ci Γ ls u r hreg hlen hTy F hF action hRhs
      ihTy ihF ihRhs =>
    rw [((Params.henv.closedC hreg).mkInstS).lift'_eq .zero]
    have hTy' := ihTy W
    rw [((Params.henv.closedC hreg).mkInstS).lift'_eq .zero] at hTy'
    let F' : ∀ cl, CtorBundle c cl := fun cl =>
      (Params.Semantic.ctor (ls := ls) (Γ := Γ') hreg hlen cl).1
    have hF' : ∀ cl, IsDefEqStrong Γ'
        (SExpr.mkInst ls ci.type) ((F' cl).rhs ls) (.sort (F' cl).u) := by
      intro cl
      exact (Params.Semantic.ctor (ls := ls) (Γ := Γ') hreg hlen cl).2
    have hempty :
        (fun path : Empty => (Empty.elim path : SExpr).lift' ρ) = Empty.elim := by
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

/-- A certified local contraction remains certified after a genuinely typed
substitution.  In particular, generated-rule checks and the final local
equality are transported by the same weak-defeq substitution theorem. -/
def _root_.Lean4Lean.Pattern.Action.subst
    (action : Pattern.Action Γ r e m1 m2 A)
    (W : Ctx.Subst (fun Γ e A => Γ ⊢ e : A) Δ σ Γ) :
    Pattern.Action Δ r (e.subst σ) m1
      (fun path => (m2 path).subst σ) (A.subst σ) := by
  let dfs' := action.dfs.map fun d =>
    (d.1.subst σ, d.2.1.subst σ, d.2.2.subst σ)
  refine {
    pat := action.pat
    matched := action.matched.subst
    dfs := dfs'
    defeqs := ?_
    checked := ?_
    sound := ?_ }
  · rw [← Pattern.Check.defeqsS_subst, ← action.defeqs]
    simp [dfs', Function.comp_def]
  · intro a b B hab
    simp only [dfs', List.mem_map] at hab
    obtain ⟨⟨B₀, a₀, b₀⟩, hab, heq⟩ := hab
    have hB : B₀.subst σ = B := congrArg Prod.fst heq
    have hab' : (a₀.subst σ, b₀.subst σ) = (a, b) := congrArg Prod.snd heq
    have ha : a₀.subst σ = a := congrArg Prod.fst hab'
    have hb : b₀.subst σ = b := congrArg Prod.snd hab'
    subst B
    subst a
    subst b
    exact (action.checked a₀ b₀ B₀ hab).subst W
  · simpa only [Pattern.RHS.subst_applyS] using action.sound.subst W

/-- A lookup remains typable when one older context entry is replaced by a
definitionally equal type.  The distinguished lookup is the only case that
needs conversion; entries above it are weakened and entries below it are
unchanged. -/
theorem Lookup.defeqDF_l' (h1 : Γ ⊢ A ≡ A' : .sort u)
    (h : Lookup (Δ ++ A :: Γ) i B) : Δ ++ A' :: Γ ⊢ .bvar i : B := by
  induction Δ generalizing i B with
  | nil =>
    cases h with
    | zero =>
      exact (h1.weak' (.skip .refl)).symm.defeqDF (.bvar .zero)
    | succ h => exact .bvar (.succ h)
  | cons D Δ ih =>
    cases h with
    | zero => exact .bvar .zero
    | succ h =>
      simpa only [List.cons_append, SExpr.lift, SExpr.lift', Lift.liftVar] using
        (ih h).weak' (.skip .refl)

theorem IsDefEq.defeqDF_l' (h1 : Γ ⊢ A ≡ A' : .sort u)
    (h2 : Δ++A::Γ ⊢ e1 ≡ e2 : B) : Δ++A'::Γ ⊢ e1 ≡ e2 : B := by
  generalize hctx : Δ ++ A :: Γ = Γ₁ at h2
  induction h2 generalizing Δ with
  | bvar h =>
    rw [← hctx] at h
    exact h.defeqDF_l' h1
  | symm _ ih => exact (ih hctx).symm
  | trans _ _ ih₁ ih₂ => exact (ih₁ hctx).trans (ih₂ hctx)
  | sort => exact .sort
  | const hreg hlen => exact .const hreg hlen
  | appDF _ _ ihf iha => exact .appDF (ihf hctx) (iha hctx)
  | lamDF _ _ ihA ihBody =>
    exact .lamDF (ihA hctx)
      (ihBody (Δ := _ :: Δ) (congrArg (List.cons _) hctx))
  | forallEDF _ _ ihA ihBody =>
    exact .forallEDF (ihA hctx)
      (ihBody (Δ := _ :: Δ) (congrArg (List.cons _) hctx))
  | defeqDF _ _ ihA ihe => exact .defeqDF (ihA hctx) (ihe hctx)
  | beta _ _ ihBody ihArg =>
    exact .beta
      (ihBody (Δ := _ :: Δ) (congrArg (List.cons _) hctx)) (ihArg hctx)
  | eta _ ih => exact .eta (ih hctx)
  | proofIrrel _ _ _ ihp ihh ihh' =>
    exact .proofIrrel (ihp hctx) (ihh hctx) (ihh' hctx)
  | extra hreg hlen => exact .extra hreg hlen

theorem IsDefEq.defeqDF_l (h1 : Γ ⊢ A ≡ A' : .sort u)
    (h2 : A::Γ ⊢ e1 ≡ e2 : B) : A'::Γ ⊢ e1 ≡ e2 : B :=
  .defeqDF_l' (Δ := []) h1 h2

theorem HasType.defeq_l (h1 : Γ ⊢ A ≡ A' : .sort u)
    (h2 : A::Γ ⊢ e : B) : A'::Γ ⊢ e : B := h1.defeqDF_l h2

/-! ### Heterogeneous type-equality paths

Relocated here from `Lean4Lean/Experimental/ShapeLogRel.lean` on 2026-08-15.
The whole API depends only on `IsDefEq.defeqDF`, `IsDefEq.defeqDF_l` (:3588),
`IsDefEq.subst` (:3255) and `Ctx.Subst` (:3025) — every one of them an SExpr
notion — so it belongs beside them rather than inside the logical-relation
development.  Moving it up is what lets the evidence-rich inversion suite
below state its conclusion: each inverter returns the *path* from the
subject's own type to the declared type.

`TypeDefEqPath.collapse` deliberately stays in `ShapeLogRel.lean`, beside
`LogRel.RawTypeUniq`, which is its one extra input and is the whole of raw
type uniqueness. -/

/-- A nonempty path of ordinary type equalities.  Adjacent edges may type
their shared endpoint in different universes; retaining the path avoids the
unsound heterogeneous transitivity rule while still supporting every
conversion operation one edge at a time. -/
inductive TypeDefEqPath (Γ : List SExpr) : SExpr → SExpr → SLevel → Prop where
  | single : IsDefEq Γ A B (.sort u) → TypeDefEqPath Γ A B u
  | trans : TypeDefEqPath Γ A B u → TypeDefEqPath Γ B C v →
      TypeDefEqPath Γ A C u

theorem TypeDefEqPath.leftType
    (H : TypeDefEqPath Γ A B u) : IsDefEq Γ A A (.sort u) := by
  induction H with
  | single h => exact h.hasType.1
  | trans _ _ ih _ => exact ih

theorem TypeDefEqPath.rightType
    (H : TypeDefEqPath Γ A B u) : ∃ v, IsDefEq Γ B B (.sort v) := by
  induction H with
  | single h => exact ⟨_, h.hasType.2⟩
  | trans _ _ _ ih => exact ih

theorem TypeDefEqPath.left
    (H : TypeDefEqPath Γ A B u) : TypeDefEqPath Γ A A u :=
  .single H.leftType

theorem TypeDefEqPath.right
    (H : TypeDefEqPath Γ A B u) : ∃ v, TypeDefEqPath Γ B B v := by
  obtain ⟨v, hB⟩ := H.rightType
  exact ⟨v, .single hB⟩

theorem TypeDefEqPath.symm
    (H : TypeDefEqPath Γ A B u) : ∃ v, TypeDefEqPath Γ B A v := by
  induction H with
  | single h => exact ⟨_, .single h.symm⟩
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨v₂, h₂⟩ := ih₂
    obtain ⟨_, h₁⟩ := ih₁
    exact ⟨v₂, .trans h₂ h₁⟩

/-- Transport a term equality through a path of type conversions. -/
theorem TypeDefEqPath.defeqDF
    (H : TypeDefEqPath Γ A B u)
    (h : IsDefEq Γ e₁ e₂ A) : IsDefEq Γ e₁ e₂ B := by
  induction H with
  | single hAB => exact hAB.defeqDF h
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ h)

/-- Replace the newest context entry along a path, one ordinary conversion
at a time. -/
theorem TypeDefEqPath.defeqDF_l
    (H : TypeDefEqPath Γ A B u)
    (h : IsDefEq (A :: Γ) e₁ e₂ C) : IsDefEq (B :: Γ) e₁ e₂ C := by
  induction H with
  | single hAB => exact hAB.defeqDF_l h
  | trans _ _ ih₁ ih₂ => exact ih₂ (ih₁ h)

/-- Transport every edge of a type-equality path into a converted binder
context. -/
theorem TypeDefEqPath.defeqDF_l_path
    (H : TypeDefEqPath Γ A B u)
    (P : TypeDefEqPath (A :: Γ) C D v) :
    TypeDefEqPath (B :: Γ) C D v := by
  induction P with
  | single h => exact .single (H.defeqDF_l h)
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

/-- Substitute every ordinary edge of a heterogeneous type path. -/
theorem TypeDefEqPath.subst
    (H : TypeDefEqPath Γ A B u)
    (W : Ctx.Subst (fun Γ e A => Γ ⊢ e : A) Γ₀ σ Γ) :
    TypeDefEqPath Γ₀ (A.subst σ) (B.subst σ) u := by
  induction H with
  | single h => exact .single (h.subst W)
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

/-! ### Evidence-rich inversion, with the declared-type path

The three theorems below extend `IsDefEqStrong.forallE_inv'` (:2284) to the
application and lambda shapes, and strengthen the Pi case, in one respect:
each also returns the `TypeDefEqPath` from the subject's **own** type to the
declared type `V`.  That is their whole novelty over Theory's
`VEnv.HasType.app_inv` / `.lam_inv`, and it is what removes the
`IsDefEq.trans_l` / `IsDefEqU.uniqU` fixups the Theory proofs have to spend:
a consumer that receives the path never has to re-derive the relation between
the two types, and in particular never charges type uniqueness to do so.

All three are structural in exactly the style of `forallE_inv'` — every
extension leaf of `IsDefEqStrong` carries its endpoint typings — so none of
them appeals to weak type uniqueness, to Church–Rosser, or to
`IsDefEq.strong`.  Measured `[propext, Quot.sound]` in
`plans/probes/probeR13-loop.lean`. -/

/-- Application inversion, evidence-rich.  Unlike Theory's
`VEnv.HasType.app_inv` this also returns the *path* from the application's own
result type `B.inst a` to the declared type `V`, which is what makes the
ordinary `trans_l` / type-uniqueness fixup unnecessary downstream. -/
theorem IsDefEqStrong.app_inv'
    (H : IsDefEqStrong Γ e₁ e₂ V)
    (eq : e₁ = .app f a ∨ e₂ = .app f a) :
    ∃ A B w, IsDefEqStrong Γ f f (.forallE A B) ∧ IsDefEqStrong Γ a a A ∧
      TypeDefEqPath Γ (B.inst a) V w := by
  induction H generalizing f a with
  | bvar => nomatch eq
  | symm _ ih => exact ih eq.symm
  | trans _ _ ih₁ ih₂ =>
    obtain eq | eq := eq
    · exact ih₁ (.inl eq)
    · exact ih₂ (.inr eq)
  | sort => nomatch eq
  | const => nomatch eq
  | @appDF _ A u B v _ _ _ _ _ _ hf ha hResult _ _ _ _ _ =>
    obtain ⟨⟨⟩⟩ | ⟨⟨⟩⟩ := eq
    · exact ⟨A, B, v, hf.hasType.1, ha.hasType.1, .single hResult.hasType.1.defeq⟩
    · exact ⟨A, B, v, hf.hasType.2, ha.hasType.2, .single hResult.symm.defeq⟩
  | lamDF => nomatch eq
  | forallEDF => nomatch eq
  | defeqDF hType _ _ ih =>
    obtain ⟨A, B, w, h1, h2, P⟩ := ih eq
    exact ⟨A, B, w, h1, h2, P.trans (.single hType.defeq)⟩
  | beta _ _ _ _ _ _ ihApp ihInst =>
    obtain eq | eq := eq
    · exact ihApp (.inl eq)
    · exact ihInst (.inl eq)
  | eta _ _ ihTerm _ =>
    obtain eq | eq := eq
    · nomatch eq
    · exact ihTerm (.inl eq)
  | proofIrrel _ _ _ _ ihLeft ihRight =>
    obtain eq | eq := eq
    · exact ihLeft (.inl eq)
    · exact ihRight (.inr eq)
  | defn _ _ _ _ _ _ _ _ _ ihRhs =>
    obtain eq | eq := eq
    · nomatch eq
    · exact ihRhs (.inl eq)
  | extra _ _ _ ihLeft ihRight =>
    obtain eq | eq := eq
    · exact ihLeft (.inl eq)
    · exact ihRight (.inr eq)

/-- Lambda inversion, evidence-rich.  Unlike Theory's `VEnv.HasType.lam_inv`
this returns the abstraction's *own* Pi type `.forallE A B` together with the
path from it to the declared type `V`, so no consumer has to reconcile the two
by type uniqueness. -/
theorem IsDefEqStrong.lam_inv'
    (H : IsDefEqStrong Γ e₁ e₂ V)
    (eq : e₁ = .lam A body ∨ e₂ = .lam A body) :
    ∃ B u v w, IsDefEqStrong Γ A A (.sort u) ∧
      IsDefEqStrong (A :: Γ) B B (.sort v) ∧
      IsDefEqStrong (A :: Γ) body body B ∧
      TypeDefEqPath Γ (.forallE A B) V w := by
  induction H generalizing A body with
  | bvar => nomatch eq
  | symm _ ih => exact ih eq.symm
  | trans _ _ ih₁ ih₂ =>
    obtain eq | eq := eq
    · exact ih₁ (.inl eq)
    · exact ih₂ (.inr eq)
  | sort => nomatch eq
  | const => nomatch eq
  | appDF => nomatch eq
  | @lamDF _ A₀ A₀' u B v _ _ hA hB hB' hbody hbody' _ _ _ _ _ =>
    obtain ⟨⟨⟩⟩ | ⟨⟨⟩⟩ := eq
    · exact ⟨B, u, v, _, hA.hasType.1, hB, hbody.hasType.1,
        .single (IsDefEqStrong.forallEDF hA.hasType.1 hB hB).defeq⟩
    · exact ⟨B, u, v, _, hA.hasType.2, hB', hbody'.hasType.2,
        .single (IsDefEqStrong.forallEDF hA.symm hB' hB).defeq⟩
  | forallEDF => nomatch eq
  | defeqDF hType _ _ ih =>
    obtain ⟨B, u, v, w, h1, h2, h3, P⟩ := ih eq
    exact ⟨B, u, v, w, h1, h2, h3, P.trans (.single hType.defeq)⟩
  | beta _ _ _ _ _ _ _ ihInst =>
    obtain eq | eq := eq
    · nomatch eq
    · exact ihInst (.inl eq)
  | eta _ _ ihTerm ihLam =>
    obtain eq | eq := eq
    · exact ihLam (.inl eq)
    · exact ihTerm (.inl eq)
  | proofIrrel _ _ _ _ ihLeft ihRight =>
    obtain eq | eq := eq
    · exact ihLeft (.inl eq)
    · exact ihRight (.inr eq)
  | defn _ _ _ _ _ _ _ _ _ ihRhs =>
    obtain eq | eq := eq
    · nomatch eq
    · exact ihRhs (.inl eq)
  | extra _ _ _ ihLeft ihRight =>
    obtain eq | eq := eq
    · exact ihLeft (.inl eq)
    · exact ihRight (.inr eq)

/-- `IsDefEqStrong.forallE_inv'` (:2284) with the declared-type path added, in
the same structural style: the Pi's own type `.sort (.imax u v)` is returned
together with the path from it to `V`. -/
theorem IsDefEqStrong.forallE_inv_path
    (H : IsDefEqStrong Γ e₁ e₂ V)
    (eq : e₁ = .forallE A B ∨ e₂ = .forallE A B) :
    ∃ u v w, IsDefEqStrong Γ A A (.sort u) ∧
      IsDefEqStrong (A :: Γ) B B (.sort v) ∧
      TypeDefEqPath Γ (.sort (.imax u v)) V w := by
  induction H generalizing A B with
  | bvar => nomatch eq
  | symm _ ih => exact ih eq.symm
  | trans _ _ ih₁ ih₂ =>
    obtain eq | eq := eq
    · exact ih₁ (.inl eq)
    · exact ih₂ (.inr eq)
  | sort => nomatch eq
  | const => nomatch eq
  | appDF => nomatch eq
  | lamDF => nomatch eq
  | forallEDF hA hBody hBody' _ _ _ =>
    obtain ⟨⟨⟩⟩ | ⟨⟨⟩⟩ := eq
    · exact ⟨_, _, _, hA.hasType.1, hBody.hasType.1, .single .sort⟩
    · exact ⟨_, _, _, hA.hasType.2, hBody'.hasType.2, .single .sort⟩
  | defeqDF hType _ _ ih =>
    obtain ⟨u, v, w, h1, h2, P⟩ := ih eq
    exact ⟨u, v, w, h1, h2, P.trans (.single hType.defeq)⟩
  | beta _ _ _ _ _ _ _ ihInst =>
    obtain eq | eq := eq
    · nomatch eq
    · exact ihInst (.inl eq)
  | eta _ _ ihTerm _ =>
    obtain eq | eq := eq
    · nomatch eq
    · exact ihTerm (.inl eq)
  | proofIrrel _ _ _ _ ihLeft ihRight =>
    obtain eq | eq := eq
    · exact ihLeft (.inl eq)
    · exact ihRight (.inr eq)
  | defn _ _ _ _ _ _ _ _ _ ihRhs =>
    obtain eq | eq := eq
    · nomatch eq
    · exact ihRhs (.inl eq)
  | extra _ _ _ ihLeft ihRight =>
    obtain eq | eq := eq
    · exact ihLeft (.inl eq)
    · exact ihRight (.inr eq)

variable (DefEq : List SExpr → SExpr → SExpr → SExpr → Prop) in
structure WithLift (Γ : List SExpr) (e1 e2 A : SExpr) : Prop where
  defeq' {{Δ ρ e1' e2' A'}} : Ctx.Lift' ρ Δ Γ →
    e1 = .lift' e1' ρ → e2 = .lift' e2' ρ → A = .lift' A' ρ → DefEq Δ e1' e2' A'
  left' {{Δ ρ e1' A'}} : Ctx.Lift' ρ Δ Γ → e1 = .lift' e1' ρ → A = .lift' A' ρ → DefEq Δ e1' e1' A'
  right' {{Δ ρ e2' A'}} : Ctx.Lift' ρ Δ Γ → e2 = .lift' e2' ρ → A = .lift' A' ρ → DefEq Δ e2' e2' A'

def IsDefEqLift := WithLift IsDefEq
scoped notation:65 Γ " ⊢ " e " :↑ " A:36 => IsDefEqLift Γ e e A
scoped notation:65 Γ " ⊢ " e1 " ≡ " e2 " :↑ " A:36 => IsDefEqLift Γ e1 e2 A

theorem WithLift.imp
    (imp : ∀ {Γ e1 e2 A}, DefEq Γ e1 e2 A → DefEq' Γ e1 e2 A)
    (H : WithLift DefEq Γ e1 e2 A) : WithLift DefEq' Γ e1 e2 A where
  defeq' _ _ _ _ _ W' h1 h2 h3 := imp (H.defeq' W' h1 h2 h3)
  left' _ _ _ _ W' h1 hA := imp (H.left' W' h1 hA)
  right' _ _ _ _ W' h1 hA := imp (H.right' W' h1 hA)

theorem WithLift.refl
    (refl : ∀ {ρ Δ e' A'}, Ctx.Lift' ρ Δ Γ →
      e = .lift' e' ρ → A = .lift' A' ρ → DefEq Δ e' e' A')
    : WithLift DefEq Γ e e A where
  defeq' _ _ _ _ _ W := by rintro rfl he rfl; cases SExpr.lift'_inj.1 he; exact refl W rfl rfl
  left' _ _ _ _ W := by rintro rfl rfl; exact refl W rfl rfl
  right' _ _ _ _ W := by rintro rfl rfl; exact refl W rfl rfl

theorem WithLift.weak'
    (weak : ∀ {ρ Γ Δ e1 e2 A}, Ctx.Lift' ρ Γ Δ → DefEq Γ e1 e2 A →
      DefEq Δ (e1.lift' ρ) (e2.lift' ρ) (A.lift' ρ))
    (W : Ctx.Lift' ρ Γ Δ) (H : WithLift DefEq Γ e1 e2 A) :
    WithLift DefEq Δ (e1.lift' ρ) (e2.lift' ρ) (A.lift' ρ) where
  defeq' Δ' ρ' e1' e2' A' W' h1 h2 hA := by
    have ⟨Δ₀, I⟩ := Ctx.Inter.mk W W'
    obtain ⟨e1, rfl, rfl⟩ := lift_eq_lift h1
    obtain ⟨e2, rfl, rfl⟩ := lift_eq_lift h2
    obtain ⟨A, rfl, rfl⟩ := lift_eq_lift hA
    exact weak I.diff (H.defeq' I.symm.diff rfl rfl rfl)
  left' Δ' ρ' e1' A' W' h1 hA := by
    have ⟨Δ₀, I⟩ := Ctx.Inter.mk W W'
    obtain ⟨e1, rfl, rfl⟩ := lift_eq_lift h1
    obtain ⟨A, rfl, rfl⟩ := lift_eq_lift hA
    exact weak I.diff (H.left' I.symm.diff rfl rfl)
  right' Δ' ρ' e1' A' W' h1 hA := by
    have ⟨Δ₀, I⟩ := Ctx.Inter.mk W W'
    obtain ⟨e1, rfl, rfl⟩ := lift_eq_lift h1
    obtain ⟨A, rfl, rfl⟩ := lift_eq_lift hA
    exact weak I.diff (H.right' I.symm.diff rfl rfl)

theorem IsDefEqLift.weak' : Ctx.Lift' ρ Γ Δ → Γ ⊢ e1 ≡ e2 :↑ A →
    Δ ⊢ e1.lift' ρ ≡ e2.lift' ρ :↑ A.lift' ρ := WithLift.weak' IsDefEq.weak'

/-- A lowering-stable equality may always be instantiated as an ordinary
typed equality.  This is the sound substitution fact that does not claim the
result still has universal inverse-weakening closure. -/
theorem IsDefEqLift.substDefEq
    (W : Ctx.Subst (fun Γ e A => Γ ⊢ e : A) Δ σ Γ)
    (H : Γ ⊢ e1 ≡ e2 :↑ A) :
    Δ ⊢ e1.subst σ ≡ e2.subst σ : A.subst σ :=
  (H.defeq' .refl SExpr.lift'_refl.symm SExpr.lift'_refl.symm
    SExpr.lift'_refl.symm).subst W

/- There is deliberately no `IsDefEqLift.subst` concluding at `:↑`. The
former statement quantified over the free section relation `HasType`, so
instantiating it at the trivial relation claimed lift-stability of `≡ :↑`
under arbitrary substitutions, which is false. `substDefEq` above is the
sound instantiation-to-ordinary-equality form; a `:↑`-valued conclusion
would additionally need a `Ctx.Subst`-vs-`Ctx.Lift'` commutation witness
in the premise, which no current consumer requires. -/

theorem WithLift.weak'_inv (W : Ctx.Lift' ρ Γ Δ)
    (H : WithLift DefEq Δ (e1.lift' ρ) (e2.lift' ρ) (A.lift' ρ)) : WithLift DefEq Γ e1 e2 A where
  defeq' Δ' ρ' _ _ _ W' := by
    rintro rfl rfl rfl
    simp only [← SExpr.lift'_comp] at H
    exact H.defeq' (W'.comp W) rfl rfl rfl
  left' Δ' ρ' _ _ W' := by
    rintro rfl rfl
    simp only [← SExpr.lift'_comp] at H
    exact H.left' (W'.comp W) rfl rfl
  right' Δ' ρ' _ _ W' := by
    rintro rfl rfl
    simp only [← SExpr.lift'_comp] at H
    exact H.right' (W'.comp W) rfl rfl

nonrec theorem IsDefEqLift.weak'_inv : Ctx.Lift' ρ Γ Δ →
    Δ ⊢ e1.lift' ρ ≡ e2.lift' ρ :↑ A.lift' ρ → Γ ⊢ e1 ≡ e2 :↑ A := .weak'_inv

theorem WithLift.symm
    (symm : ∀ {Γ e1 e2 A}, DefEq Γ e1 e2 A → DefEq Γ e2 e1 A)
    (H : WithLift DefEq Γ e1 e2 A) : WithLift DefEq Γ e2 e1 A where
  defeq' _ _ _ _ _ W' h1 h2 h3 := symm (H.defeq' W' h2 h1 h3)
  left' _ _ _ _ W' h1 hA := H.right' W' h1 hA
  right' _ _ _ _ W' h1 hA := H.left' W' h1 hA

nonrec theorem IsDefEqLift.symm : Γ ⊢ e1 ≡ e2 :↑ A → Γ ⊢ e2 ≡ e1 :↑ A := .symm .symm

theorem WithLift.left (H : WithLift DefEq Γ e1 e2 A) : WithLift DefEq Γ e1 e1 A :=
  .refl (H.left' ·)

theorem WithLift.right (H : WithLift DefEq Γ e1 e2 A) : WithLift DefEq Γ e2 e2 A :=
  .refl (H.right' ·)

theorem IsDefEqLift.left (H : Γ ⊢ e1 ≡ e2 :↑ A) : Γ ⊢ e1 :↑ A where
  defeq' _ _ _ _ _ W' := by rintro rfl he hA; exact SExpr.lift'_inj.1 he ▸ H.left' W' rfl hA
  left' := H.left'
  right' := H.left'

theorem WithLift.defeq (H : WithLift DefEq Γ e1 e2 A) : DefEq Γ e1 e2 A :=
  H.defeq' .refl SExpr.lift'_refl.symm SExpr.lift'_refl.symm SExpr.lift'_refl.symm

nonrec theorem IsDefEqLift.defeq (H : Γ ⊢ e1 ≡ e2 :↑ A) : Γ ⊢ e1 ≡ e2 : A := H.defeq

variable (Γ₀ : List SExpr) in
inductive IsDefEqCtx : List SExpr → List SExpr → Prop
  | zero : IsDefEqCtx Γ₀ Γ₀
  | succ :  IsDefEqCtx Γ₁ Γ₂ → Γ₁ ⊢ A₁ ≡ A₂ : .sort u → IsDefEqCtx (A₁ :: Γ₁) (A₂ :: Γ₂)

theorem IsDefEq.defeqDFC' (h1 : IsDefEqCtx Γ₀ Γ₁ Γ₂)
    (h2 : Δ ++ Γ₁ ⊢ e₁ ≡ e₂ : A) : Δ ++ Γ₂ ⊢ e₁ ≡ e₂ : A := by
  induction h1 generalizing e₁ e₂ A Δ with
  | zero => exact h2
  | @succ _ _ _ A₂ _ _ AA ih =>
    simpa using ih (Δ := Δ ++ [A₂]) (by simpa using AA.defeqDF_l' h2)

theorem IsDefEq.defeqDFC (h1 : IsDefEqCtx Γ₀ Γ₁ Γ₂)
    (h2 : Γ₁ ⊢ e₁ ≡ e₂ : A) : Γ₂ ⊢ e₁ ≡ e₂ : A := .defeqDFC' (Δ := []) h1 h2

omit [Params] in theorem Subpattern.varN_constS (H : Subpattern p (.varN (.const c) n)) :
    ∃ n, p = .varN (.const c) n := by
  generalize eq : Pattern.varN (.const c) n = p' at H
  induction H generalizing n with
  | refl => exact ⟨_, eq.symm⟩
  | appL | appR => cases n <;> cases eq
  | varL _ ih => cases n <;> cases eq; exact ih rfl

theorem Params.simple_appS (H : Pat p r) (h : Subpattern (.app p₁ p₂) p) :
    .app p₁ p₂ = p := by
  obtain ⟨_|_, rfl⟩ := Params.pat_simple H <;> cases h
  · rfl
  · obtain ⟨_|_, ⟨⟩⟩ := Subpattern.varN_constS ‹_›
  · obtain ⟨_|_, ⟨⟩⟩ := Subpattern.varN_constS ‹_›

/-- A function spine whose next argument is inspected by a registered
pattern.  This is the SExpr counterpart of Theory's `VEnv.IsMajorPremise`;
it is what permits weak-head reduction inside an iota major premise before
the proof-carrying pattern contraction fires. -/
def IsMajorPremise (e : SExpr) :=
  ∃ p, (∃ r, Pat p r) ∧ ∃ p₁ p₂, Subpattern (.app p₁ p₂) p ∧
    ∃ m1 m2, p₁.MatchesS e m1 m2

theorem IsMajorPremise.lift' {e : SExpr} {ρ : Lift} :
    IsMajorPremise (e.lift' ρ) ↔ IsMajorPremise e := by
  constructor <;> intro ⟨_, h1, _, _, h2, _, _, h3⟩
  · obtain ⟨_, h4, _⟩ := Pattern.matchesS_lift'.1 h3
    exact ⟨_, h1, _, _, h2, _, _, h4⟩
  · exact ⟨_, h1, _, _, h2, _, _, h3.lift'⟩

theorem IsMajorPremise.subst {e : SExpr} {σ : Subst} :
    IsMajorPremise e → IsMajorPremise (e.subst σ)
  | ⟨_, h1, _, _, h2, _, _, h3⟩ =>
    ⟨_, h1, _, _, h2, _, _, h3.subst⟩

theorem IsMajorPremise.lam : ¬IsMajorPremise (.lam A e) := nofun

theorem Params.pat_not_varS : ¬Pat (.var p) r := (nomatch Params.pat_simple ·)

scoped notation:65 Γ " ⊢ " e1 " ⤳ " e2:36 => WHRed Γ e1 e2
inductive WHRed (Γ : List SExpr) : SExpr → SExpr → Prop where
  | app : Γ ⊢ f ⤳ f' → Γ ⊢ .app f a ⤳ .app f' a
  | major : IsMajorPremise f → Γ ⊢ a ⤳ a' → Γ ⊢ .app f a ⤳ .app f a'
  | beta : Γ ⊢ .app (.lam A e) a ⤳ e.inst a
  /-- A local extension contraction consumes the same finite certificate as
  strong equality; pattern membership alone is not operational evidence. -/
  | extra : Pattern.Action Γ r e m1 m2 A →
    Γ ⊢ e ⤳ r.1.applyS m1 m2

theorem WHRed.subst
    (W : Ctx.Subst (fun Γ e A => Γ ⊢ e : A) Δ σ Γ) :
    Γ ⊢ e1 ⤳ e2 → Δ ⊢ e1.subst σ ⤳ e2.subst σ
  | .app h1 => .app (h1.subst W)
  | .major h1 h2 => .major h1.subst (h2.subst W)
  | .beta => subst_inst ▸ .beta
  | @extra _ Γ p r e m1 m2 A action => by
    rw [Pattern.RHS.subst_applyS]
    exact .extra (action.subst W)

theorem WHRed.weak' (W : Ctx.Lift' ρ Γ Γ') :
    Γ ⊢ e1 ⤳ e2 → Γ' ⊢ e1.lift' ρ ⤳ e2.lift' ρ
  | .app h1 => .app (h1.weak' W)
  | .major h1 h2 => .major (IsMajorPremise.lift'.2 h1) (h2.weak' W)
  | .beta => by rw [SExpr.lift'_inst_hi]; exact .beta
  | @extra _ Γ p r e m1 m2 A action => by
    rw [Pattern.RHS.lift'_applyS]
    exact .extra (action.weak' W)

/-- Inverse weakening for one weak-head step. The `.extra` case is
deferred (off the L4L-16 gate path; consumed only through the
`WHRedS.weakU_inv` mirror, whose live consumers are `InferType.weakU_inv`
below and `LRIsType.weak'` in `Experimental/LogRel.lean`): it needs to
lower the two `IsDefEq` fields of the matched `Pattern.Action`, which
requires either a context-WF-conditioned `IsDefEq` inverse weakening or
restating `Action.checked`/`sound` at `:↑`. See
plans/l4l-16-completion-plan.md §16B′. -/
theorem WHRed.weakU_inv (W : Ctx.Lift' ρ Γ Γ') (H : Γ' ⊢ e1.lift' ρ ⤳ e2') :
    ∃ e2, e2' = e2.lift' ρ ∧ Γ ⊢ e1 ⤳ e2 := by
  generalize he : e1.lift' ρ = e1' at H
  induction H generalizing e1 with
  | app h1 ih => let .app .. := e1; cases he; obtain ⟨_, rfl, a1⟩ := ih rfl; exact ⟨_, rfl, .app a1⟩
  | major h1 h2 ih =>
    let .app .. := e1
    cases he
    obtain ⟨_, rfl, a1⟩ := ih rfl
    exact ⟨_, rfl, .major (IsMajorPremise.lift'.1 h1) a1⟩
  | beta =>
    let .app e1 _ := e1; let .lam .. := e1; cases he
    simp [← SExpr.lift'_inst_hi, SExpr.lift'_inj]; exact .beta
  | extra => sorry

def WHNF (Γ : List SExpr) (e : SExpr) := ∀ e', ¬Γ ⊢ e ⤳ e'

theorem WHNF.lam : WHNF Γ (.lam A e) := by
  intro _ hred
  cases hred with
  | extra action => nomatch action.matched

theorem WHNF.sort : WHNF Γ (.sort A) := by
  intro _ hred
  cases hred with
  | extra action => nomatch action.matched

theorem WHNF.forallE : WHNF Γ (.forallE A B) := by
  intro _ hred
  cases hred with
  | extra action => nomatch action.matched

theorem WHNF.subpattern
    (h1 : Params.Pat p r) (h2 : Subpattern p₁ p) (h3 : p₁ ≠ p)
    (h4 : p₁.MatchesS e m1 m2) : WHNF Γ e := by
  intro _ H2
  obtain ⟨c, n, rfl⟩ : ∃ c n, p₁ = .varN (.const c) n := by
    obtain ⟨_|_, rfl⟩ := Params.pat_simple h1 <;> cases h2 <;>
      first | cases h3 rfl | exact ⟨_, Subpattern.varN_constS ‹_›⟩
  have hn : ∀ r, ¬Params.Pat (.const c) r := fun _ h => by
    cases (Params.pat_uniq h1 h (.trans (.varN .refl) h2) (Pattern.inter_self _)).1
    exact h3.symm (h2.antisymm (.varN .refl))
  clear h3
  induction H2 generalizing n with
  | app r1 ih =>
    let n+1 := n
    let .var h4 := h4
    exact ih _ (.trans (.varL .refl) h2) h4
  | major r1 r2 ih =>
    let n+1 := n
    let .var h4 := h4
    let ⟨p', ⟨_, h1'⟩, p₁', p₂', h2', _, _, h3'⟩ := r1
    cases Params.simple_appS h1' h2'
    obtain ⟨⟨_, n, _⟩ | _, rfl⟩ := Params.pat_simple h1 <;>
      [skip; cases n <;> cases h2]
    have ⟨_, _, _, a1, _a2⟩ := Pattern.matchesS_inter.1
      ⟨⟨_, _, h3'⟩, ⟨_, _, h4⟩⟩
    cases h2 with
    | appL h2 =>
      cases (Params.pat_app_l_uniq h1 h1' .refl .refl h2).symm.trans a1
    | appR h2 =>
      cases (Params.pat_app_uniq h1' h1 .refl .refl .refl
        (.trans (.varL .refl) h2)).symm.trans a1
  | beta => generalize Pattern.varN .. = p' at m1 m2 h4; nomatch h4
  | extra action =>
    have ⟨_, _, _, a1, a2⟩ := Pattern.matchesS_inter.1
      ⟨⟨_, _, action.matched⟩, ⟨_, _, h4⟩⟩
    obtain ⟨⟨_, major, _, _⟩ | _, rfl⟩ := Params.pat_simple h1 <;>
      [skip; cases n <;> cases h2]
    obtain ⟨rfl, eq, _⟩ := Params.pat_uniq h1 action.pat h2 a1
    cases n <;> cases eq
    exact hn _ h1

theorem IsMajorPremise.whnf : IsMajorPremise e → WHNF Γ e := by
  rintro ⟨p, ⟨_, h1⟩, p₁, p₂, h2, _, _, h3⟩
  refine .subpattern h1 (.trans (.appL .refl) h2) ?_ h3
  rintro rfl
  cases h2.antisymm (.appL .refl)

omit [Params] in
/-- Descend a pattern's arity chain to its head constant's classification.
With the registered defaults (`top := true`, `extra := 0`) this says every
registered pattern's head classifies as a symbol of the pattern's arity. -/
theorem _root_.Lean4Lean.Pattern.WF.arity_head
    {cl : Name → Option Classification} {c : Name} {k : Nat} {p : Pattern}
    (H : Arity (.const c) k p) :
    ∀ {top : Bool} {n : Nat}, p.WF cl top n →
      cl c = some (if top then .symb (k + n) else .ctor (k + n)) := by
  induction H with
  | refl => intro top n h; simp only [Nat.zero_add]; exact h
  | app _ ih =>
    intro top n h
    simpa only [Nat.succ_add, Nat.add_succ] using ih h.1
  | var _ ih =>
    intro top n h
    simpa only [Nat.succ_add, Nat.add_succ] using ih h

/-- Constant-headed application spines decompose uniquely. -/
theorem spine_inj :
    ∀ (args args' : List SExpr) {c c' : Name} {ls ls' : List SLevel},
      args.foldr (fun (a f : SExpr) => f.app a) (.const c ls) =
        args'.foldr (fun (a f : SExpr) => f.app a) (.const c' ls') →
      c = c' ∧ ls = ls' ∧ args = args'
  | [], [], _, _, _, _, h => by cases h; exact ⟨rfl, rfl, rfl⟩
  | [], _ :: _, _, _, _, _, h => by cases h
  | _ :: _, [], _, _, _, _, h => by cases h
  | _ :: args, _ :: args', _, _, _, _, h => by
    injection h with h1 h2
    obtain ⟨rfl, rfl, rfl⟩ := spine_inj args args' h1
    cases h2
    exact ⟨rfl, rfl, rfl⟩

/-- The subject of any registered-pattern match is a constant-headed spine
whose head classifies as a symbol of the spine's length. -/
theorem Params.matchesS_symb_head {p : Pattern} {r} {e : SExpr}
    {m1 : List SLevel} {m2 : p.Path → SExpr}
    (h1 : Params.Pat p r) (h2 : p.MatchesS e m1 m2) :
    ∃ (c' : Name) (ls' : List SLevel) (args' : List SExpr),
      e = args'.foldr (fun (a f : SExpr) => f.app a) (.const c' ls') ∧
      Params.classify c' = some (.symb args'.length) := by
  obtain ⟨c', ls', args', rfl, har⟩ := h2.head_spine
  refine ⟨c', ls', args', rfl, ?_⟩
  simpa using Pattern.WF.arity_head har (Params.pat_wf h1)

/-- A fully applied spine headed by a classified constructor is weak-head
normal: registered pattern heads classify as symbols, so no pattern matches
the spine or any prefix, no prefix is a major premise, and no prefix is a
lambda. -/
theorem WHNF.ctorSpine {c : Name} {k : Nat} {ls : List SLevel}
    (hcl : Params.classify c = some (.ctor k)) (args : List SExpr) :
    WHNF Γ (args.foldr (fun (a f : SExpr) => f.app a) (.const c ls)) := by
  induction args with
  | nil =>
    intro e' hred
    cases hred with
    | extra action =>
      obtain ⟨c', ls', args', heq, hsymb⟩ :=
        Params.matchesS_symb_head action.pat action.matched
      obtain ⟨rfl, -, rfl⟩ := spine_inj [] args' heq
      rw [hcl] at hsymb
      cases hsymb
  | cons a args ih =>
    simp only [List.foldr_cons]
    intro e' hred
    generalize hf :
      args.foldr (fun (a f : SExpr) => f.app a) (.const c ls) = fhead at hred ih
    cases hred with
    | app h1 => exact ih _ h1
    | major h1 _ =>
      obtain ⟨p, ⟨r', hp⟩, p₁, p₂, hsub, m1', m2', hm⟩ := h1
      cases Params.simple_appS hp hsub
      subst hf
      obtain ⟨ch, lsh, argsh, heqh, harh⟩ := hm.head_spine
      obtain ⟨rfl, -, rfl⟩ := spine_inj args argsh heqh
      have hhead := Pattern.WF.arity_head harh (Params.pat_wf hp).1
      rw [hcl] at hhead
      cases hhead
    | beta =>
      cases args <;> simp only [List.foldr_cons, List.foldr_nil] at hf <;> cases hf
    | extra action =>
      subst hf
      obtain ⟨c', ls', args', heq, hsymb⟩ :=
        Params.matchesS_symb_head action.pat action.matched
      have heq' : (a :: args).foldr (fun (a f : SExpr) => f.app a) (.const c ls) =
          args'.foldr (fun (a f : SExpr) => f.app a) (.const c' ls') := by
        simpa only [List.foldr_cons] using heq
      obtain ⟨rfl, -, rfl⟩ := spine_inj (a :: args) args' heq'
      rw [hcl] at hsymb
      cases hsymb

theorem WHRed.determ (H1 : Γ ⊢ e ⤳ e₁) (H2 : Γ ⊢ e ⤳ e₂) : e₁ = e₂ := by
  induction H1 generalizing e₂ with
  | app l1 ih =>
    cases H2 with
    | app r1 => cases ih r1; rfl
    | major r1 r2 => cases r1.whnf _ l1
    | beta => cases WHNF.lam _ l1
    | extra action =>
      cases action.matched with
      | app r3 =>
        cases IsMajorPremise.whnf ⟨_, ⟨_, action.pat⟩, _, _, .refl, _, _, r3⟩ _ l1
      | var => cases Params.pat_not_varS action.pat
  | major l1 l2 ih =>
    cases H2 with
    | app r1 => cases l1.whnf _ r1
    | major _ r2 => cases ih r2; rfl
    | beta => cases l1.lam
    | extra action =>
      cases action.matched with
      | var => cases Params.pat_not_varS action.pat
      | app _ r4 => cases WHNF.subpattern action.pat (.appR .refl) nofun r4 _ l2
  | beta =>
    cases H2 with
    | app r1 => cases WHNF.lam _ r1
    | major r1 => cases r1.lam
    | beta => rfl
    | extra action => nomatch action.matched
  | extra actionL =>
    cases H2 with
    | beta => nomatch actionL.matched
    | major r1 r2 =>
      cases actionL.matched with
      | var => cases Params.pat_not_varS actionL.pat
      | app _ l4 => cases WHNF.subpattern actionL.pat (.appR .refl) nofun l4 _ r2
    | app r1 =>
      cases actionL.matched with
      | app l3 =>
        cases IsMajorPremise.whnf ⟨_, ⟨_, actionL.pat⟩, _, _, .refl, _, _, l3⟩ _ r1
      | var => cases Params.pat_not_varS actionL.pat
    | extra actionR =>
      have ⟨_, _, _, a1, a2⟩ := Pattern.matchesS_inter.1
        ⟨⟨_, _, actionR.matched⟩, ⟨_, _, actionL.matched⟩⟩
      obtain ⟨rfl, -, ⟨⟩⟩ := Params.pat_uniq actionL.pat actionR.pat .refl a1
      obtain ⟨rfl, rfl⟩ := actionL.matched.determ actionR.matched
      rfl

def WHRedS (Γ : List SExpr) : SExpr → SExpr → Prop := ReflTransGen (WHRed Γ)
scoped notation:65 Γ " ⊢ " e1 " ⤳* " e2:36 => WHRedS Γ e1 e2

theorem WHRedS.subst
    (W : Ctx.Subst (fun Γ e A => Γ ⊢ e : A) Δ σ Γ)
    (H : Γ ⊢ e1 ⤳* e2) :
    Δ ⊢ e1.subst σ ⤳* e2.subst σ := by
  induction H with
  | rfl => exact .rfl
  | tail _ h2 ih => exact .tail ih (h2.subst W)

/-- Weak-head reduction is definitional equality. OPEN, and the one
`SExpr.lean` admission on the L4L-16 gate path. Native exact iota leaves no
longer use it: their reductions are reflexive and their typings come from
`CtorExact`/`PatternLeafSpine`.  The remaining uses are the two root-to-view
anchors of a normalized constructor chain (and generic compatibility
wrappers).  Proving those anchors is part of the merged weak-inversion/type-
uniqueness development; it cannot be replaced by an intermediate-link
certificate because arbitrary weak-head expansion erased that typing. See
plans/l4l-16-completion-plan.md §16C′. -/
theorem WHRedS.defeq (H : Γ ⊢ e1 ⤳* e2) (he : Γ ⊢ e1 : A) : Γ ⊢ e1 ≡ e2 : A := sorry

theorem WHRedS.weak' (W : Ctx.Lift' ρ Γ Δ) (H : Γ ⊢ e1 ⤳* e2) :
    Δ ⊢ e1.lift' ρ ⤳* e2.lift' ρ := by
  induction H with
  | rfl => exact .rfl
  | tail _ h2 ih => exact .tail ih (h2.weak' W)

theorem WHRedS.app (H : Γ ⊢ e1 ⤳* e2) : Γ ⊢ e1.app a ⤳* e2.app a := by
  induction H with
  | rfl => exact .rfl
  | tail _ h2 ih => exact .tail ih h2.app

theorem WHRedS.major (H1 : IsMajorPremise f) (H : Γ ⊢ a ⤳* a') :
    Γ ⊢ f.app a ⤳* f.app a' := by
  induction H with
  | rfl => exact .rfl
  | tail _ h2 ih => exact .tail ih (h2.major H1)

theorem WHRedS.weakU_inv (W : Ctx.Lift' ρ Γ Δ) (H : Δ ⊢ e1.lift' ρ ⤳* e2') :
    ∃ e2, e2' = e2.lift' ρ ∧ Γ ⊢ e1 ⤳* e2 := by
  induction H with
  | rfl => exact ⟨_, rfl, .rfl⟩
  | tail _ h2 ih =>
    obtain ⟨_, rfl, a1⟩ := ih
    obtain ⟨_, rfl, a2⟩ := h2.weakU_inv W
    exact ⟨_, rfl, .tail a1 a2⟩

theorem WHRedS.determ_l (H1 : Γ ⊢ e ⤳* e₁) (H2 : Γ ⊢ e ⤳* e₂) (W2 : WHNF Γ e₂) : Γ ⊢ e₁ ⤳* e₂ := by
  induction H1 using ReflTransGen.headIndOn generalizing e₂ with
  | rfl => exact H2
  | head l1 l2 ih =>
    cases H2 using ReflTransGen.headIndOn with
    | rfl => cases W2 _ l1
    | head r1 r2 => cases l1.determ r1; exact ih r2 W2

theorem WHNF.whRedS (W : WHNF Γ e) (H : Γ ⊢ e ⤳* e') : e = e' := by
  cases H using ReflTransGen.headIndOn with
  | rfl => rfl
  | head h1 => cases W _ h1

theorem WHRedS.determ
    (H1 : Γ ⊢ e ⤳* e₁) (W1 : WHNF Γ e₁)
    (H2 : Γ ⊢ e ⤳* e₂) (W2 : WHNF Γ e₂) : e₁ = e₂ := W1.whRedS (H1.determ_l H2 W2)

scoped notation:65 Γ " ⊢ " e1 " ≫ " e2:36 => ParRed Γ e1 e2
inductive ParRed : List SExpr → SExpr → SExpr → Prop where
  | bvar : Γ ⊢ .bvar i ≫ .bvar i
  | sort : Γ ⊢ .sort u ≫ .sort u
  | const : Γ ⊢ .const c ls ≫ .const c ls
  | app : Γ ⊢ f ≫ f' → Γ ⊢ a ≫ a' → Γ ⊢ .app f a ≫ .app f' a'
  | lam : Γ ⊢ A ≫ A' → A::Γ ⊢ body ≫ body' → Γ ⊢ .lam A body ≫ .lam A' body'
  | forallE : Γ ⊢ A ≫ A' → A::Γ ⊢ B ≫ B' → Γ ⊢ .forallE A B ≫ .forallE A' B'
  | beta : A::Γ ⊢ e₁ ≫ e₁' → Γ ⊢ e₂ ≫ e₂' → Γ ⊢ .app (.lam A e₁) e₂ ≫ e₁'.inst e₂'
  | extra : Pattern.Action Γ r e m1 m2 A →
    (∀ a, Γ ⊢ m2 a ≫ m2' a) → Γ ⊢ e ≫ r.1.applyS m1 m2'

protected theorem ParRed.rfl : ∀ {e}, Γ ⊢ e ≫ e
  | .bvar .. => .bvar
  | .sort .. => .sort
  | .const .. => .const
  | .app .. => .app ParRed.rfl ParRed.rfl
  | .lam .. => .lam ParRed.rfl ParRed.rfl
  | .forallE .. => .forallE ParRed.rfl ParRed.rfl

theorem ParRed.weak' (W : Ctx.Lift' ρ Γ Γ') :
    Γ ⊢ e1 ≫ e2 → Γ' ⊢ e1.lift' ρ ≫ e2.lift' ρ
  | .bvar => .bvar
  | .sort => .sort
  | .const => .const
  | .app h1 h2 => .app (h1.weak' W) (h2.weak' W)
  | .lam h1 h2 => .lam (h1.weak' W) (h2.weak' W.cons)
  | .forallE h1 h2 => .forallE (h1.weak' W) (h2.weak' W.cons)
  | .beta h1 h2 => by rw [SExpr.lift'_inst_hi]; exact (h1.weak' W.cons).beta (h2.weak' W)
  | extra action hred => by
    rw [Pattern.RHS.lift'_applyS]
    exact .extra (action.weak' W) fun a => (hred a).weak' W

def ParRedS (Γ : List SExpr) : SExpr → SExpr → Prop := ReflTransGen (ParRed Γ)
scoped notation:65 Γ " ⊢ " e1 " ≫* " e2:36 => ParRedS Γ e1 e2

theorem ParRedS.weak' (W : Ctx.Lift' ρ Γ Γ') (H : Γ ⊢ e1 ≫* e2) :
    Γ' ⊢ e1.lift' ρ ≫* e2.lift' ρ := by
  induction H with
  | rfl => exact .rfl
  | tail _ h2 ih => exact .tail ih (h2.weak' W)

scoped notation:65 Γ " ⊢ " e1 " ▷ " e2:36 => InferType Γ e1 e2
inductive InferType : List SExpr → SExpr → SExpr → Prop where
  | bvar : Lookup Γ i A → Γ ⊢ .bvar i ▷ A
  | sort : Γ ⊢ .sort u ▷ .sort (.succ u)
  | const : env.constants c = some ci → ls.length = ci.uvars →
    Γ ⊢ .const c ls ▷ SExpr.mkInst ls ci.type
  | app : Γ ⊢ f ▷ F → Γ ⊢ F ⤳* .forallE A B → Γ ⊢ a :↑ A → Γ ⊢ .app f a ▷ B.inst a
  | lam : Γ ⊢ A :↑ .sort u → A::Γ ⊢ body ▷ B → Γ ⊢ .lam A body ▷ .forallE A B
  | forallE : Γ ⊢ A ▷ U → Γ ⊢ U ⤳* .sort u →
    A::Γ ⊢ B ▷ V → A::Γ ⊢ V ⤳* .sort v → Γ ⊢ .forallE A B ▷ .sort (.imax u v)

theorem InferType.determ (H1 : Γ ⊢ e ▷ A) (H2 : Γ ⊢ e ▷ A') : A = A' := by
  induction H1 generalizing A' with
  | bvar h1 => cases H2 with | bvar h2 => exact h1.determ h2
  | sort => cases H2; rfl
  | const l1 l2 => cases H2 with | const r1 r2 => cases l1.symm.trans r1; rfl
  | app l1 l2 _ ih =>
    cases H2 with | app r1 r2 => cases ih r1; cases l2.determ .forallE r2 .forallE; rfl
  | lam _ l2 ih => cases H2 with | lam _ r2 => cases ih r2; rfl
  | forallE l1 l2 l3 l4 ih1 ih2 =>
    cases H2 with | forallE r1 r2 r3 r4
    cases ih1 r1; cases l2.determ .sort r2 .sort
    cases ih2 r3; cases l4.determ .sort r4 .sort; rfl

theorem InferType.weak' (W : Ctx.Lift' ρ Γ Δ) : Γ ⊢ e ▷ A → Δ ⊢ e.lift' ρ ▷ A.lift' ρ
  | .bvar h => .bvar (h.weak' W)
  | .sort => .sort
  | .const h1 h2 => by rw [(henv.closedC h1).mkInstS.lift'_eq .zero]; exact .const h1 h2
  | .app h1 h2 h3 => SExpr.lift'_inst_hi .. ▸ .app (h1.weak' W) (h2.weak' W) (h3.weak' W)
  | .lam h1 h2 => .lam (h1.weak' W) (h2.weak' W.cons)
  | .forallE h1 h2 h3 h4 => .forallE (h1.weak' W) (h2.weak' W) (h3.weak' W.cons) (h4.weak' W.cons)

theorem InferType.weakU_inv (W : Ctx.Lift' ρ Γ Δ) (H : Δ ⊢ e.lift' ρ ▷ A') :
    ∃ A, A' = A.lift' ρ ∧ Γ ⊢ e ▷ A := by
  generalize he : e.lift' ρ = e' at H
  induction H generalizing Γ ρ e with
  | bvar h => let .bvar _ := e; cases he; let ⟨_, h1, h2⟩ := h.weakU_inv W; exact ⟨_, h1, .bvar h2⟩
  | sort => let .sort _ := e; cases he; exact ⟨_, rfl, .sort⟩
  | const h1 h2 =>
    let .const .. := e; cases he
    exact ⟨_, ((henv.closedC h1).mkInstS.lift'_eq .zero).symm, .const h1 h2⟩
  | app h1 h2 h3 ih =>
    let .app .. := e; cases he
    obtain ⟨_, rfl, a1⟩ := ih W rfl
    obtain ⟨F, a2, a3⟩ := h2.weakU_inv W; cases F <;> cases a2
    refine ⟨_, by rw [SExpr.lift'_inst_hi], .app a1 a3 (h3.weak'_inv W)⟩
  | lam h1 h2 ih =>
    let .lam .. := e; cases he
    obtain ⟨_, rfl, a2⟩ := ih W.cons rfl
    exact ⟨_, rfl, .lam (h1.weak'_inv W) a2⟩
  | forallE h1 h2 h3 h4 ih1 ih2 =>
    let .forallE .. := e; cases he
    obtain ⟨_, rfl, a1⟩ := ih1 W rfl
    obtain ⟨U, a2, a3⟩ := h2.weakU_inv W; cases U <;> cases a2
    obtain ⟨_, rfl, b1⟩ := ih2 W.cons rfl
    obtain ⟨V, b2, b3⟩ := h4.weakU_inv W.cons; cases V <;> cases b2
    exact ⟨_, rfl, .forallE a1 a3 b1 b3⟩

theorem InferType.weak'_inv (W : Ctx.Lift' ρ Γ Δ) (H : Δ ⊢ e.lift' ρ ▷ A.lift' ρ) : Γ ⊢ e ▷ A := by
  obtain ⟨_, h1, h2⟩ := H.weakU_inv W
  exact SExpr.lift'_inj.1 h1 ▸ h2

/- `InferType.subst`/`InferType.inst` were deleted together with the
unsound `IsDefEqLift.subst`: their `app`/`lam` cases consumed it at the
instance `HasType := InferType`, i.e. their proofs rested on exactly the
free-relation unsoundness that forced the deletion, and their only
consumer was the also-deleted `InferType.whRed`. Restoring them requires
a `Ctx.Subst` premise whose entries carry `:↑` (lift-stable) typings,
which no current development needs. -/

def InferTypeS (Γ : List SExpr) (e A : SExpr) := ∃ A', Γ ⊢ e ▷ A' ∧ Γ ⊢ A' ⤳* A
scoped notation:65 Γ " ⊢ " e1 " ▷* " e2:36 => InferTypeS Γ e1 e2

theorem WHRedS.inferType
    (H1 : Γ ⊢ e ⤳* e₁) (W1 : WHNF Γ e₁)
    (H2 : Γ ⊢ e ⤳* e₂) (W2 : WHNF Γ e₂) : e₁ = e₂ := by
  induction H1 using ReflTransGen.headIndOn generalizing e₂ with
  | rfl =>
    cases H2 using ReflTransGen.headIndOn with
    | rfl => rfl
    | head r1 => cases W1 _ r1
  | head l1 l2 ih =>
    cases H2 using ReflTransGen.headIndOn with
    | rfl => cases W2 _ l1
    | head r1 r2 => cases l1.determ r1; exact ih r2 W2

/-- A classified constructor spine only reduces to itself. -/
theorem WHRedS.ctorSpine_eq {c : Name} {k : Nat} {ls : List SLevel}
    (hcl : Params.classify c = some (.ctor k)) {args : List SExpr}
    (H : Γ ⊢ args.foldr (fun (a f : SExpr) => f.app a) (.const c ls) ⤳* e') :
    e' = args.foldr (fun (a f : SExpr) => f.app a) (.const c ls) := by
  have gen : ∀ {e₀ e'}, Γ ⊢ e₀ ⤳* e' →
      e₀ = args.foldr (fun (a f : SExpr) => f.app a) (.const c ls) →
      e' = args.foldr (fun (a f : SExpr) => f.app a) (.const c ls) := by
    intro e₀ e' H
    induction H using ReflTransGen.headIndOn with
    | rfl => exact id
    | head h1 _ _ => rintro rfl; cases WHNF.ctorSpine hcl args _ h1
  exact gen H rfl

/-- Two weak-head reductions of one term to classified constructor spines
land on the same syntactic spine.  This is the midpoint agreement used to
concatenate constructor-observation chains. -/
theorem WHRedS.ctorSpine_determ
    {c c' : Name} {k k' : Nat} {ls ls' : List SLevel}
    {args args' : List SExpr}
    (hc : Params.classify c = some (.ctor k))
    (hc' : Params.classify c' = some (.ctor k'))
    (H1 : Γ ⊢ e ⤳* args.foldr (fun (a f : SExpr) => f.app a) (.const c ls))
    (H2 : Γ ⊢ e ⤳* args'.foldr (fun (a f : SExpr) => f.app a) (.const c' ls')) :
    args.foldr (fun (a f : SExpr) => f.app a) (.const c ls) =
      args'.foldr (fun (a f : SExpr) => f.app a) (.const c' ls') :=
  WHRedS.inferType H1 (.ctorSpine hc args) H2 (.ctorSpine hc' args')

theorem WHRed.parRed (H : Γ ⊢ e ⤳ e') : Γ ⊢ e ≫ e' := by
  induction H with
  | app _ ih => exact .app ih .rfl
  | major _ _ ih => exact .app .rfl ih
  | beta => exact .beta .rfl .rfl
  | extra action => exact .extra action fun _ => .rfl

theorem WHRedS.parRedS (H : Γ ⊢ e ⤳* e') : Γ ⊢ e ≫* e' := by
  induction H with
  | rfl => exact .rfl
  | tail _ h2 ih => exact .tail ih h2.parRed

theorem InferTypeS.determ
    (H1 : Γ ⊢ e ▷* A) (W1 : WHNF Γ A)
    (H2 : Γ ⊢ e ▷* A') (W2 : WHNF Γ A') : A = A' := by
  let ⟨_, h1, h2⟩ := H1; let ⟨_, h3, h4⟩ := H2
  cases h1.determ h3; exact h2.determ W1 h4 W2

theorem InferTypeS.weak' (W : Ctx.Lift' ρ Γ Δ) : Γ ⊢ e ▷* A → Δ ⊢ e.lift' ρ ▷* A.lift' ρ
  | ⟨_, h1, h2⟩ => ⟨_, h1.weak' W, h2.weak' W⟩

scoped notation:65 Γ " ⊢ " e1 " ≡ₚ " e2 " : " A:36 => NormalEq Γ e1 e2 A
inductive NormalEq : List SExpr → SExpr → SExpr → SExpr → Prop where
  | refl : Γ ⊢ e : A → Γ ⊢ e ≡ₚ e : A
  | appDF : Γ ⊢ f₁ ≡ₚ f₂ : .forallE A B → Γ ⊢ a₁ ≡ₚ a₂ : A →
    Γ ⊢ B.inst a₁ ≡ B.inst a₂ : .sort v →
    Γ ⊢ .app f₁ a₁ ≡ₚ .app f₂ a₂ : B.inst a₁
  | lamDF : Γ ⊢ A₁ ≡ A : .sort u → Γ ⊢ A₂ ≡ A : .sort u → A::Γ ⊢ B : .sort v →
    A::Γ ⊢ body₁ ≡ₚ body₂ : B → Γ ⊢ .lam A₁ body₁ ≡ₚ .lam A₂ body₂ : .forallE A B
  | forallEDF : Γ ⊢ A₁ ≡ A : .sort u → Γ ⊢ A₂ ≡ A : .sort u →
    Γ ⊢ A₁ ≡ₚ A₂ : .sort u → A::Γ ⊢ B₁ ≡ₚ B₂ : .sort v →
    Γ ⊢ .forallE A₁ B₁ ≡ₚ .forallE A₂ B₂ : .sort (.imax u v)
  | etaL : Γ ⊢ A : .sort u → A::Γ ⊢ B : .sort v → Γ ⊢ e' : .forallE A B →
    A::Γ ⊢ e ≡ₚ .app e'.lift (.bvar 0) : B → Γ ⊢ .lam A e ≡ₚ e' : .forallE A B
  | etaR : Γ ⊢ A : .sort u → A::Γ ⊢ B : .sort v → Γ ⊢ e' : .forallE A B →
    A::Γ ⊢ .app e'.lift (.bvar 0) ≡ₚ e : B → Γ ⊢ e' ≡ₚ .lam A e : .forallE A B
  | proofIrrel : Γ ⊢ p : .sort .zero → Γ ⊢ h : p → Γ ⊢ h' : p → Γ ⊢ h ≡ₚ h' : p
  | defeqDF : Γ ⊢ A ≡ B : .sort u → Γ ⊢ e1 ≡ₚ e2 : A → Γ ⊢ e1 ≡ₚ e2 : B

theorem NormalEq.defeqDFC (W : IsDefEqCtx Γ₀ Γ₁ Γ₂)
    (H : Γ₁ ⊢ e1 ≡ₚ e2 : A) : Γ₂ ⊢ e1 ≡ₚ e2 : A := by
  induction H generalizing Γ₂ with
  | refl h => refine .refl (h.defeqDFC W)
  | appDF h1 h2 h3 ih1 ih2 => exact .appDF (ih1 W) (ih2 W) (h3.defeqDFC W)
  | lamDF h1 h2 h3 _ ih2 =>
    exact .lamDF (h1.defeqDFC W) (h2.defeqDFC W)
      (h3.defeqDFC (W.succ h1.hasType.2)) (ih2 (W.succ h1.hasType.2))
  | forallEDF h1 h2 _ _ ih1 ih2 =>
    exact .forallEDF (h1.defeqDFC W) (h2.defeqDFC W) (ih1 W) (ih2 (W.succ h1.hasType.2))
  | etaL h1 h2 h3 _ ih =>
    exact .etaL (h1.defeqDFC W) (h2.defeqDFC (W.succ h1)) (h3.defeqDFC W) (ih (W.succ h1))
  | etaR h1 h2 h3 _ ih =>
    exact .etaR (h1.defeqDFC W) (h2.defeqDFC (W.succ h1)) (h3.defeqDFC W) (ih (W.succ h1))
  | proofIrrel h1 h2 h3 => exact .proofIrrel (h1.defeqDFC W) (h2.defeqDFC W) (h3.defeqDFC W)
  | defeqDF h1 _ ih => exact .defeqDF (h1.defeqDFC W) (ih W)

theorem NormalEq.defeq (H : Γ ⊢ e1 ≡ₚ e2 : A) : Γ ⊢ e1 ≡ e2 : A := by
  induction H with
  | refl h => exact h
  | appDF h1 h2 _ ih1 ih2 => exact .appDF ih1 ih2
  | lamDF hA₁ hA₂ hB _ ihB =>
    exact have W := .succ .zero hA₁.symm
      .defeqDF (.forallEDF hA₁ (hB.defeqDFC W)) (.lamDF (hA₁.trans hA₂.symm) (ihB.defeqDFC W))
  | forallEDF hA₁ hA₂ _ _ ihA ihB =>
    exact .forallEDF (hA₁.trans hA₂.symm) (ihB.defeqDFC (.succ .zero hA₁.symm))
  | etaL hA _ h1 _ ih => exact .trans (.lamDF hA ih) (.eta h1)
  | etaR hA _ h1 _ ih => exact .trans (.symm (.eta h1)) (.lamDF hA ih)
  | proofIrrel h1 h2 h3 => exact .proofIrrel h1 h2 h3
  | defeqDF h1 _ ih => exact .defeqDF h1 ih

theorem NormalEq.symm (H : Γ ⊢ e1 ≡ₚ e2 : A) : Γ ⊢ e2 ≡ₚ e1 : A := by
  induction H with
  | refl h => exact .refl h
  | appDF h1 h2 h3 ih1 ih2 => exact .defeqDF h3.symm <| .appDF ih1 ih2 h3.symm
  | lamDF h1 h2 h3 _ ih2 => exact .lamDF h2 h1 h3 ih2
  | forallEDF h1 h2 _ _ ih1 ih2 => exact .forallEDF h2 h1 ih1 ih2
  | etaL h1 h2 h3 _ ih => exact .etaR h1 h2 h3 ih
  | etaR h1 h2 h3 _ ih => exact .etaL h1 h2 h3 ih
  | proofIrrel h1 h2 h3 => exact .proofIrrel h1 h3 h2
  | defeqDF h1 _ ih => exact .defeqDF h1 ih

theorem NormalEq.weak' (W : Ctx.Lift' ρ Γ Γ') (H : Γ ⊢ e1 ≡ₚ e2 : A) :
    Γ' ⊢ e1.lift' ρ ≡ₚ e2.lift' ρ : A.lift' ρ := by
  induction H generalizing Γ' ρ with
  | refl h => exact .refl (h.weak' W)
  | appDF h1 h2 h3 ih1 ih2 =>
    simpa only [SExpr.lift', SExpr.lift'_inst_hi] using
      (NormalEq.appDF (ih1 W) (ih2 W) (by
        simpa only [SExpr.lift'_inst_hi, SExpr.lift'] using h3.weak' W))
  | lamDF h1 h2 h3 _ ih2 => exact .lamDF (h1.weak' W) (h2.weak' W) (h3.weak' W.cons) (ih2 W.cons)
  | forallEDF h1 h2 _ _ ih1 ih2 => exact .forallEDF (h1.weak' W) (h2.weak' W) (ih1 W) (ih2 W.cons)
  | etaL h1 h2 h3 _ ih =>
    refine .etaL (h1.weak' W) (h2.weak' W.cons) (h3.weak' W) ?_
    simpa [← SExpr.lift'_comp] using ih W.cons
  | etaR h1 h2 h3 _ ih =>
    refine .etaR (h1.weak' W) (h2.weak' W.cons) (h3.weak' W) ?_
    simpa [← SExpr.lift'_comp] using ih W.cons
  | proofIrrel h1 h2 h3 => exact .proofIrrel (h1.weak' W) (h2.weak' W) (h3.weak' W)
  | defeqDF h1 _ ih => exact .defeqDF (h1.weak' W) (ih W)

def CRDefEq (Γ : List SExpr) (e₁ e₂ A : SExpr) : Prop :=
  Γ ⊢ e₁ ≡ e₂ : A ∧
  ∃ e₁' e₂', Γ ⊢ e₁ ≫* e₁' ∧ Γ ⊢ e₂ ≫* e₂' ∧ Γ ⊢ e₁' ≡ₚ e₂' : A
scoped notation:65 Γ " ⊢ " e1 " ≫≪ " e2 " : " A:36 => CRDefEq Γ e1 e2 A

def CRDefEqLift := WithLift CRDefEq
scoped notation:65 Γ " ⊢ " e1 " ≫≪ " e2 " :↑ " A:36 => CRDefEqLift Γ e1 e2 A

theorem CRDefEq.normalEq (H : Γ ⊢ e₁ ≡ₚ e₂ : A) : Γ ⊢ e₁ ≫≪ e₂ : A :=
  ⟨H.defeq, _, _, .rfl, .rfl, H⟩

theorem CRDefEq.refl (H : Γ ⊢ e : A) : Γ ⊢ e ≫≪ e : A :=
  .normalEq (.refl H)

theorem CRDefEq.defeq : Γ ⊢ e₁ ≫≪ e₂ : A → Γ ⊢ e₁ ≡ e₂ : A := (·.1)

theorem CRDefEq.symm : Γ ⊢ e₁ ≫≪ e₂ : A → Γ ⊢ e₂ ≫≪ e₁ : A
  | ⟨h1, _, _, h3, h4, h5⟩ => ⟨h1.symm, _, _, h4, h3, h5.symm⟩

/- There is deliberately no `CRDefEq.trans` here. Its Theory counterpart
is five lines from `ParRedS.church_rosser`, `NormalEq.parRedS`, and
`NormalEq.trans`; none of that development exists on the SExpr side, and
Theory's own `NormalEq.parRed` `.extra` overlap cases are the open
L4L-18A obligations. Porting the joining argument lands with L4L-18A
against the finished Theory script — see plans/l4l-16-completion-plan.md
§L4L-18A′ — and nothing on the L4L-16 gate path consumes it. -/

theorem CRDefEq.defeqDF : Γ ⊢ e₁ ≫≪ e₂ : A → Γ ⊢ A ≡ B : .sort u → Γ ⊢ e₁ ≫≪ e₂ : B
  | ⟨l1, _, _, l3, l4, l5⟩, H => ⟨H.defeqDF l1, _, _, l3, l4, l5.defeqDF H⟩

theorem CRDefEq.weak' (W : Ctx.Lift' ρ Γ Γ') :
    Γ ⊢ e1 ≫≪ e2 : A → Γ' ⊢ e1.lift' ρ ≫≪ e2.lift' ρ : A.lift' ρ
  | ⟨h1, _, _, h3, h4, h5⟩ => ⟨h1.weak' W, _, _, h3.weak' W, h4.weak' W, h5.weak' W⟩

theorem WHRedS.crDefEq (H1 : Γ ⊢ e1 : A) (H2 : Γ ⊢ e1 ⤳* e2) : Γ ⊢ e1 ≫≪ e2 : A :=
  ⟨H2.defeq H1, _, _, H2.parRedS, .rfl, .refl (H2.defeq H1).hasType.2⟩

nonrec theorem CRDefEqLift.symm : Γ ⊢ e1 ≫≪ e2 :↑ A → Γ ⊢ e2 ≫≪ e1 :↑ A := .symm .symm

theorem CRDefEqLift.defeq (H : Γ ⊢ e1 ≫≪ e2 :↑ A) : Γ ⊢ e1 ≡ e2 :↑ A := H.imp (·.1)

theorem CRDefEqLift.left (H : Γ ⊢ e1 ≫≪ e2 :↑ A) : Γ ⊢ e1 :↑ A := H.defeq.left

nonrec theorem CRDefEqLift.refl (H : Γ ⊢ e :↑ A) : Γ ⊢ e ≫≪ e :↑ A :=
  .refl (.refl <| H.left' · · ·)

/- There is deliberately no `InferType.whRed` (subject reduction for
inferred types under one weak-head step). The former statement was false
as written: `▷` is syntax-directed with no conversion rule, so a `major`
step changes the inferred type from `B.inst a` to the merely-defeq
`B.inst a'`, a `beta` redex's argument is typed (`:↑`) at a domain that
need not be its principal type, and a `Pattern.Action` supplies a typing
of the RHS, not an inference. If a successor milestone needs this fact,
state it up to conversion (`Γ ⊢ e' ▷* A'` with `Γ ⊢ A ≡ A' : .sort u`);
Theory has no counterpart to port. -/
