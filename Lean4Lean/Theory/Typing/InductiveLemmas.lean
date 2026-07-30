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

theorem appN_append (f : VExpr) : ∀ (as bs : List VExpr),
    f.appN (as ++ bs) = (f.appN as).appN bs
  | [], _ => rfl
  | a :: as, bs => appN_append (f.app a) as bs

theorem liftN_appN (n k : Nat) (f : VExpr) : ∀ (as : List VExpr),
    (f.appN as).liftN n k = appN (f.liftN n k) (as.map (liftN n · k))
  | [] => rfl
  | a :: as => by
    show (VExpr.appN (f.app a) as).liftN n k = _
    rw [liftN_appN n k (f.app a) as]
    rfl

theorem bvarRevRange_liftN_low : ∀ (m off n : Nat),
    (bvarRevRange off m).map (liftN n · 0) = bvarRevRange (n + off) m
  | 0, _, _ => rfl
  | m+1, off, n => by
    show VExpr.bvar _ :: _ = VExpr.bvar _ :: _
    rw [bvarRevRange_liftN_low m off n]
    congr 2
    show liftVar n (off + m) 0 = n + off + m
    rw [liftVar_le (Nat.zero_le _)]; omega

theorem bvarRevRange_liftN_high : ∀ (m off n k : Nat), off + m ≤ k →
    (bvarRevRange off m).map (liftN n · k) = bvarRevRange off m
  | 0, _, _, _, _ => rfl
  | m+1, off, n, k, h => by
    show VExpr.bvar _ :: _ = VExpr.bvar _ :: _
    rw [bvarRevRange_liftN_high m off n k (by omega)]
    congr 2
    exact liftVar_lt (by omega)

/-- Instantiating at a fresh (lifted-over) position is the identity. -/
theorem inst_liftN1 : ∀ (e a : VExpr) (k : Nat), (e.liftN 1 k).inst a k = e := by
  intro e
  induction e with intro a k
  | bvar j =>
    show VExpr.instVar (liftVar 1 j k) a k = .bvar j
    unfold liftVar VExpr.instVar
    split
    · rfl
    · next h =>
      rw [if_neg (by omega), if_neg (by omega)]
      congr 1; omega
  | sort | const => rfl
  | app f b ihf ihb => simp [liftN, inst, ihf, ihb]
  | lam A b ihA ihb | forallE A b ihA ihb => simp [liftN, inst, ihA, ihb]

/-- Lifting a telescope of closed binders acts only on the body. -/
theorem liftN_forallN_closed : ∀ {As : List VExpr}, (∀ A ∈ As, A.ClosedN 0) →
    ∀ (e : VExpr) (n k : Nat),
    (forallN As e).liftN n k = forallN As (e.liftN n (k + As.length))
  | [], _, e, n, k => rfl
  | A :: As, hAs, e, n, k => by
    show VExpr.forallE _ _ = VExpr.forallE _ _
    rw [(hAs _ (.head _)).liftN_eq (Nat.zero_le _),
      liftN_forallN_closed (fun A h => hAs _ (.tail _ h)) e n (k+1),
      show k+1+As.length = k+(As.length+1) from by omega]
    rfl

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

/-! ## Context and spine lemmas -/

theorem Lookup.append {A : VExpr} : ∀ (Δ : List VExpr) {Γ},
    Lookup (Δ ++ A :: Γ) Δ.length (A.liftN (Δ.length + 1))
  | [], _ => .zero
  | B :: Δ, Γ => by
    simpa [← VExpr.liftN_succ] using (Lookup.append (A := A) Δ (Γ := Γ)).succ (A := B)

theorem Lookup.append_closed {A : VExpr} (hA : A.ClosedN 0) (Δ : List VExpr) {Γ} :
    Lookup (Δ ++ A :: Γ) Δ.length A := by
  simpa [hA.liftN_eq (Nat.zero_le _)] using Lookup.append (A := A) Δ (Γ := Γ)

theorem Lookup.of_getElem? : ∀ {Γ : List VExpr} {i : Nat} {A : VExpr},
    Γ[i]? = some A → Lookup Γ i (A.liftN (i+1))
  | B :: _, 0, A, h => by
    obtain rfl : B = A := by simpa using h
    exact .zero
  | B :: Γ, i+1, A, h => by
    have := Lookup.of_getElem? (Γ := Γ) (i := i) (A := A) (by simpa using h)
    simpa [← VExpr.liftN_succ] using this.succ (A := B)

theorem Lookup.of_getElem?_closed {Γ : List VExpr} {i : Nat} {A : VExpr}
    (h : Γ[i]? = some A) (hA : A.ClosedN 0) : Lookup Γ i A := by
  simpa [hA.liftN_eq (Nat.zero_le _)] using Lookup.of_getElem? h

/-- Right-associated: the element right past a two-part prefix. -/
theorem getElem?_rstack3 {α} (Δ mid : List α) (a : α) (Γ : List α) {i : Nat}
    (h : i = Δ.length + mid.length) : (Δ ++ (mid ++ a :: Γ))[i]? = some a := by
  rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega),
    show i - Δ.length - mid.length = 0 from by omega]
  rfl

/-- Right-associated: an element inside the middle block. -/
theorem getElem?_rstack_mid {α} (Δ mid Γ : List α) {i : Nat}
    (h1 : Δ.length ≤ i) (h2 : i - Δ.length < mid.length) :
    (Δ ++ (mid ++ Γ))[i]? = mid[i - Δ.length]? := by
  rw [List.getElem?_append_right h1, List.getElem?_append_left h2]

/-- The element right past a two-part prefix. -/
theorem getElem?_stack3 {α} (Δ mid Γ : List α) (a : α) {i : Nat}
    (h : i = Δ.length + mid.length) : (Δ ++ mid ++ a :: Γ)[i]? = some a := by
  rw [List.append_assoc, List.getElem?_append_right (by omega),
    show i - Δ.length = mid.length from by omega,
    List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

/-- An element inside the middle block of a three-part context. -/
theorem getElem?_stack_mid {α} (Δ mid Γ : List α) {i : Nat}
    (h1 : Δ.length ≤ i) (h2 : i - Δ.length < mid.length) :
    (Δ ++ mid ++ Γ)[i]? = mid[i - Δ.length]? := by
  rw [List.append_assoc, List.getElem?_append_right h1,
    List.getElem?_append_left h2]

namespace VEnv

/-- The spine `bvarRevRange Δ.length As.length` selects exactly the binders
`As` (reversed into the context past `Δ`), when all of `As` are closed. -/
theorem hasType_bvarRevRange {env : VEnv} {U : Nat} :
    ∀ {As : List VExpr}, (∀ A ∈ As, A.ClosedN 0) → ∀ {Δ Γ₀ : List VExpr},
    List.Forall₂ (env.HasType U (Δ ++ As.reverse ++ Γ₀))
      (VExpr.bvarRevRange Δ.length As.length) As
  | [], _, _, _ => .nil
  | A :: As, h, Δ, Γ₀ => by
    refine .cons (.bvar ?_) ?_
    · have := Lookup.append_closed (h _ (.head _)) (Δ ++ As.reverse) (Γ := Γ₀)
      simpa [List.append_assoc] using this
    · have := hasType_bvarRevRange (env := env) (U := U) (As := As)
        (fun A h' => h _ (.tail _ h')) (Δ := Δ) (Γ₀ := A :: Γ₀)
      simpa [List.append_assoc] using this

theorem ClosedN.forallN_of_all {As : List VExpr} (hAs : ∀ A ∈ As, A.ClosedN 0)
    {B : VExpr} (hB : B.ClosedN 0) {k : Nat} : (VExpr.forallN As B).ClosedN k := by
  induction As generalizing k with
  | nil => exact hB.mono (Nat.zero_le _)
  | cons A As ih =>
    exact ⟨(hAs _ (.head _)).mono (Nat.zero_le _), ih fun A h => hAs _ (.tail _ h)⟩

/-- Substituting a variable for the innermost binder of a lifted term is a
smaller lift: the telescope-self-application identity. Unconditional. -/
theorem _root_.Lean4Lean.VExpr.liftN_succ_inst_bvar (e : VExpr) :
    ∀ (s k : Nat), (e.liftN (s+1) (k+1)).inst (.bvar s) k = e.liftN s k := by
  induction e with intro s k
  | bvar j =>
    show VExpr.instVar (liftVar (s+1) j (k+1)) (.bvar s) k = .bvar (liftVar s j k)
    unfold liftVar
    rcases Nat.lt_trichotomy j k with h | rfl | h
    · rw [if_pos (Nat.lt_succ_of_lt h), if_pos h]
      simp [VExpr.instVar, h]
    · rw [if_pos (Nat.lt_succ_self _), if_neg (Nat.lt_irrefl _)]
      show VExpr.instVar j (.bvar s) j = _
      rw [show VExpr.instVar j (.bvar s) j = (VExpr.bvar s).liftN j from by
        unfold VExpr.instVar; rw [if_neg (Nat.lt_irrefl _), if_pos rfl]]
      show VExpr.bvar (liftVar j s) = _
      rw [liftVar_base, Nat.add_comm]
    · rw [if_neg (by omega), if_neg (by omega)]
      simp only [VExpr.instVar]
      rw [if_neg (by omega), if_neg (by omega)]
      congr 1; omega
  | sort | const => intros; rfl
  | app f a ihf iha => simp [VExpr.liftN, VExpr.inst, ihf, iha]
  | lam A b ihA ihb | forallE A b ihA ihb =>
    simp [VExpr.liftN, VExpr.inst, ihA s k, ihb s (k+1)]

/-- Applying `f : (∀ As, B).liftN Δ.length` to the spine of variables
referring to its own binders, sitting in the context right below `Δ`.
The lift on the type in the hypothesis is what makes the invariant close
over the recursion; no closedness is needed. -/
theorem HasType.appN_selfSpine {env : VEnv} {U : Nat} :
    ∀ {As : List VExpr} {B : VExpr} {Δ Γ : List VExpr} {f},
    env.HasType U (Δ ++ As.reverse ++ Γ) f
      ((VExpr.forallN As B).liftN (Δ.length + As.length)) →
    env.HasType U (Δ ++ As.reverse ++ Γ)
      (f.appN (VExpr.bvarRevRange Δ.length As.length)) (B.liftN Δ.length)
  | [], B, Δ, Γ, f, hf => by simpa using hf
  | A :: As, B, Δ, Γ, f, hf => by
    have harg : env.HasType U (Δ ++ (A :: As).reverse ++ Γ)
        (.bvar (Δ.length + As.length)) (A.liftN (Δ.length + As.length + 1)) := by
      have := Lookup.append (A := A) (Δ ++ As.reverse) (Γ := Γ)
      simp only [List.length_append, List.length_reverse] at this
      exact .bvar (by simpa [List.append_assoc, Nat.add_assoc] using this)
    have happ := HasType.app hf harg
    simp only [List.length_cons, Nat.add_succ] at happ
    rw [VExpr.liftN_succ_inst_bvar] at happ
    have := HasType.appN_selfSpine (As := As) (B := B) (Δ := Δ) (Γ := A :: Γ)
      (f := f.app (.bvar (Δ.length + As.length))) (by simpa [List.append_assoc] using happ)
    simp only [VExpr.appN] at this ⊢
    simpa [List.append_assoc, VExpr.bvarRevRange] using this

/-- The closed-telescope entry point for `appN_selfSpine`. -/
theorem HasType.appN_selfSpine' {env : VEnv} {U : Nat}
    {As : List VExpr} {B : VExpr} {Δ Γ : List VExpr} {f}
    (hcl : (VExpr.forallN As B).ClosedN 0)
    (hf : env.HasType U (Δ ++ As.reverse ++ Γ) f (VExpr.forallN As B)) :
    env.HasType U (Δ ++ As.reverse ++ Γ)
      (f.appN (VExpr.bvarRevRange Δ.length As.length)) (B.liftN Δ.length) :=
  HasType.appN_selfSpine (by rwa [hcl.liftN_eq (Nat.zero_le _)])

/-- Application of a closed non-dependent telescope. -/
theorem HasType.appN_closed {env : VEnv} {U : Nat} {Γ : List VExpr} :
    ∀ {As : List VExpr}, (∀ A ∈ As, A.ClosedN 0) → ∀ {B : VExpr}, B.ClosedN 0 →
    ∀ {f args}, env.HasType U Γ f (VExpr.forallN As B) →
    List.Forall₂ (env.HasType U Γ) args As →
    env.HasType U Γ (f.appN args) B
  | [], _, _, _, _, _, hf, .nil => hf
  | A :: As, hAs, B, hB, f, a :: as, hf, .cons ha hargs => by
    have h2 : env.HasType U Γ (f.app a) ((VExpr.forallN As B).inst a) := .app hf ha
    rw [(ClosedN.forallN_of_all (fun A h => hAs _ (.tail _ h)) hB).instN_eq
      (Nat.zero_le _)] at h2
    exact appN_closed (fun A h => hAs _ (.tail _ h)) hB (f := f.app a) h2 hargs

theorem isType_forallN_free {env : VEnv} {U : Nat} {As : List VExpr}
    (hAs : ∀ A ∈ As, ∀ Γ, env.IsType U Γ A)
    {B : VExpr} (hB : ∀ Γ, env.IsType U Γ B) : ∀ Γ, env.IsType U Γ (VExpr.forallN As B) := by
  induction As with
  | nil => exact hB
  | cons A As ih =>
    exact fun Γ => (hAs _ (.head _) Γ).forallE
      (ih (fun A h => hAs _ (.tail _ h)) (A :: Γ))

/-- Well-formedness of a binder telescope over a context. -/
def OnTel (env : VEnv) (U : Nat) : List VExpr → List VExpr → Prop
  | _, [] => True
  | Γ, A :: As => env.IsType U Γ A ∧ OnTel env U (A :: Γ) As

theorem HasType.lamN {env : VEnv} {U : Nat} : ∀ {As Γ body B},
    OnTel env U Γ As → env.HasType U (As.reverse ++ Γ) body B →
    env.HasType U Γ (VExpr.lamN As body) (VExpr.forallN As B)
  | [], _, _, _, _, hb => hb
  | A :: As, Γ, body, B, ⟨⟨_, hA⟩, hT⟩, hb =>
    HasType.lam hA (HasType.lamN hT (by simpa [List.append_assoc] using hb))

theorem IsType.forallN {env : VEnv} {U : Nat} : ∀ {As Γ B},
    OnTel env U Γ As → env.IsType U (As.reverse ++ Γ) B →
    env.IsType U Γ (VExpr.forallN As B)
  | [], _, _, _, hB => hB
  | A :: As, Γ, B, ⟨hA, hT⟩, hB =>
    IsType.forallE hA (IsType.forallN hT (by simpa [List.append_assoc] using hB))

theorem onTel_of_free {env : VEnv} {U : Nat} : ∀ {As Γ},
    (∀ A ∈ As, ∀ Γ', env.IsType U Γ' A) → OnTel env U Γ As
  | [], _, _ => trivial
  | _ :: _, _, h =>
    ⟨h _ (.head _) _, onTel_of_free fun A h' Γ' => h _ (.tail _ h') Γ'⟩

theorem OnTel.append {env : VEnv} {U : Nat} : ∀ {As Bs Γ},
    OnTel env U Γ As → OnTel env U (As.reverse ++ Γ) Bs → OnTel env U Γ (As ++ Bs)
  | [], _, _, _, h2 => h2
  | _ :: As, Bs, Γ, ⟨hA, h1⟩, h2 =>
    ⟨hA, OnTel.append h1 (by simpa [List.append_assoc] using h2)⟩

end VEnv

/-! ## The induction-hypothesis telescope under lifting -/

namespace VInductDecl

/-- `ihsFrom` after the motive-directed lift into the rule context. -/
def ihsR (m k : Nat) : List Nat → Nat → List VExpr
  | [], _ => []
  | j :: rs, p => .app (.bvar (k + (m + p))) (.bvar (m-1-j+p)) :: ihsR m k rs (p+1)

/-- Recursive-field positions are bounded by the field count. -/
theorem recIdxs_lt {U : Nat} {T : Name} : ∀ {Bs : List VExpr} {j₀ : Nat},
    ∀ j ∈ recIdxs U T Bs j₀, j < j₀ + Bs.length
  | B :: Bs, j₀, j, h => by
    unfold recIdxs at h
    split at h
    · rcases List.mem_cons.1 h with rfl | h
      · simp
      · have := recIdxs_lt _ h
        simp only [List.length_cons]; omega
    · have := recIdxs_lt _ h
      simp only [List.length_cons]; omega

theorem ihsFrom_liftN (m k : Nat) : ∀ (rs : List Nat), (∀ j ∈ rs, j < m) →
    ∀ (p : Nat) (X : VExpr),
    (VExpr.forallN (ihsFrom m rs p) X).liftN k (m + p) =
    VExpr.forallN (ihsR m k rs p) (X.liftN k (m + p + rs.length))
  | [], _, _, _ => rfl
  | j :: rs, hm, p, X => by
    show VExpr.forallE _ _ = VExpr.forallE _ _
    congr 1
    · show VExpr.app _ _ = VExpr.app _ _
      simp only [VExpr.liftN, liftVar]
      rw [if_neg (Nat.lt_irrefl _),
        if_pos (show m-1-j+p < m+p by have := hm j (.head _); omega)]
    · rw [show m + p + 1 = m + (p+1) from rfl,
        ihsFrom_liftN m k rs (fun j h => hm j (.tail _ h)) (p+1) X,
        show m + (p+1) + rs.length = m + p + (rs.length+1) from by omega]
      rfl

/-- `ihsFrom_liftN` with the cutoff generalized, for syntactic rewriting. -/
theorem ihsFrom_liftN' (m k : Nat) (rs : List Nat) (hm : ∀ j ∈ rs, j < m)
    (p : Nat) (X : VExpr) {cut : Nat} (hcut : cut = m + p) :
    (VExpr.forallN (ihsFrom m rs p) X).liftN k cut =
    VExpr.forallN (ihsR m k rs p) (X.liftN k (m + p + rs.length)) := by
  rw [hcut]; exact ihsFrom_liftN m k rs hm p X

theorem ihsR_liftN1 (m k : Nat) : ∀ (rs : List Nat) (p c : Nat), c ≤ p → ∀ (X : VExpr),
    VExpr.forallN (ihsR m k rs (p+1)) (X.liftN 1 (c + rs.length)) =
    (VExpr.forallN (ihsR m k rs p) X).liftN 1 c
  | [], p, c, _, X => by simp [ihsR, VExpr.forallN]
  | j :: rs, p, c, hc, X => by
    show VExpr.forallE _ _ = VExpr.forallE _ _
    congr 1
    · show VExpr.app _ _ = VExpr.app _ _
      simp only [VExpr.liftN, liftVar]
      rw [if_neg (show ¬(k + (m + p) < c) by omega),
        if_neg (show ¬(m-1-j+p < c) by omega)]
      congr 2 <;> omega
    · rw [show c + (j :: rs).length = (c+1) + rs.length from by simp; omega]
      exact ihsR_liftN1 m k rs (p+1) (c+1) (by omega) X

theorem ihsFrom_length (m : Nat) : ∀ (rs : List Nat) (p : Nat),
    (ihsFrom m rs p).length = rs.length
  | [], _ => rfl
  | _ :: rs, p => by simp [ihsFrom, ihsFrom_length m rs (p+1)]

theorem minorTypes_length (U : Nat) (T : Name) : ∀ (cs : List VConstVal) (i : Nat),
    (minorTypes U T cs i).length = cs.length
  | [], _ => rfl
  | _ :: cs, i => by simp [minorTypes, minorTypes_length U T cs (i+1)]

theorem recIdxs_ge {U : Nat} {T : Name} : ∀ {Bs : List VExpr} {j₀ : Nat},
    ∀ j ∈ recIdxs U T Bs j₀, j₀ ≤ j
  | _ :: Bs, j₀, j, h => by
    unfold recIdxs at h
    split at h
    · rcases List.mem_cons.1 h with rfl | h
      · exact Nat.le_refl _
      · exact Nat.le_of_succ_le (recIdxs_ge _ h)
    · exact Nat.le_of_succ_le (recIdxs_ge _ h)

/-- Recursive-field positions really hold the type constant. -/
theorem recIdxs_getElem {U : Nat} {T : Name} : ∀ {Bs : List VExpr} {j₀ : Nat},
    ∀ j ∈ recIdxs U T Bs j₀, Bs[j - j₀]? = some (.const T (VLevel.params U))
  | B :: Bs, j₀, j, h => by
    unfold recIdxs at h
    split at h
    · next heq =>
      rcases List.mem_cons.1 h with rfl | h
      · simpa [Nat.sub_self] using heq
      · have h1 := recIdxs_ge _ h
        have h2 := recIdxs_getElem _ h
        rw [show j - j₀ = (j - (j₀+1)) + 1 from by omega]
        simpa using h2
    · next heq =>
      have h1 := recIdxs_ge _ h
      have h2 := recIdxs_getElem _ h
      rw [show j - j₀ = (j - (j₀+1)) + 1 from by omega]
      simpa using h2

theorem bvarRevRange_closedN : ∀ (m off k : Nat), off + m ≤ k →
    ∀ e ∈ VExpr.bvarRevRange off m, e.ClosedN k
  | 0, _, _, _, _, h => nomatch h
  | m+1, off, k, hk, e, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact show off + m < k by omega
    · exact bvarRevRange_closedN m off k (by omega) e h

theorem bvarRevRange_levelWF {Uv : Nat} : ∀ (m off : Nat),
    ∀ e ∈ VExpr.bvarRevRange off m, e.LevelWF Uv
  | 0, _, _, h => nomatch h
  | m+1, off, e, h => by
    rcases List.mem_cons.1 h with rfl | h
    · trivial
    · exact bvarRevRange_levelWF m off e h

theorem ihsFrom_levelWF {Uv : Nat} {m : Nat} : ∀ (rs : List Nat) (p : Nat),
    ∀ e ∈ ihsFrom m rs p, e.LevelWF Uv
  | _ :: rs, p, e, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨trivial, trivial⟩
    · exact ihsFrom_levelWF rs (p+1) e h

/-- Closedness of a telescope of closed binders over an open body. -/
theorem _root_.Lean4Lean.VExpr.ClosedN.forallN_closed_binders :
    ∀ {As : List VExpr}, (∀ A ∈ As, A.ClosedN 0) →
    ∀ {X : VExpr} {k : Nat}, X.ClosedN (k + As.length) →
    (VExpr.forallN As X).ClosedN k
  | [], _, _, _, hX => hX
  | _ :: As, hAs, X, k, hX =>
    ⟨(hAs _ (.head _)).mono (Nat.zero_le _),
      VExpr.ClosedN.forallN_closed_binders (fun A h => hAs _ (.tail _ h))
        (by rw [show k+1+As.length = k+(As.length+1) from by omega]; exact hX)⟩

theorem ihsFrom_closedN {m : Nat} : ∀ (rs : List Nat) (p : Nat) {X : VExpr} {k : Nat},
    m < k → X.ClosedN (k + p + rs.length) →
    (VExpr.forallN (ihsFrom m rs p) X).ClosedN (k + p)
  | [], _, _, _, _, hX => hX
  | j :: rs, p, X, k, hm, hX =>
    ⟨⟨show m+p < k+p by omega, show m-1-j+p < k+p by omega⟩,
      ihsFrom_closedN rs (p+1) hm
        (X := X) (k := k)
        (by rw [show k+(p+1)+rs.length = k+p+(rs.length+1) from by omega]; exact hX)⟩

theorem stage1Field_closed {U : Nat} {T : Name} {B : VExpr}
    (h : stage1Field U T B) : B.ClosedN 0 := by
  rcases stage1Field_iff.1 h with rfl | ⟨h, -⟩
  · trivial
  · exact h

theorem minorType_closedN1 {U : Nat} {T : Name} {c : VConstVal}
    (h : stage1Ctor U T c.type) : (minorType U T c).ClosedN 1 := by
  have hBs := (stage1Ctor_eq h).2
  simp only [minorType]
  refine VExpr.ClosedN.forallN_closed_binders (fun B hB => ?_) ?_
  · obtain ⟨B₀, hB₀, rfl⟩ := List.mem_map.1 hB
    exact (stage1Field_closed (hBs _ hB₀)).instL
  · rw [List.length_map]
    exact ihsFrom_closedN (m := (ctorFields c.type).length)
      (recIdxs U T (ctorFields c.type)) 0
      (X := .app (.bvar ((ctorFields c.type).length + (recIdxs U T (ctorFields c.type)).length))
        (VExpr.appN (.const c.name (VLevel.params' U 1))
          (VExpr.bvarRevRange (recIdxs U T (ctorFields c.type)).length
            (ctorFields c.type).length)))
      (k := 1 + (ctorFields c.type).length)
      (by omega)
      ⟨show _ < _ by omega,
        VExpr.ClosedN.appN (f := .const c.name (VLevel.params' U 1)) trivial
          (bvarRevRange_closedN _ _ _ (by omega))⟩

theorem minorTypes_closedN {U : Nat} {T : Name} : ∀ {cs : List VConstVal} {i : Nat},
    (∀ c ∈ cs, (minorType U T c).ClosedN 1) →
    ∀ {X : VExpr}, X.ClosedN (1 + i + cs.length) →
    (VExpr.forallN (minorTypes U T cs i) X).ClosedN (1 + i)
  | [], _, _, _, hX => hX
  | _ :: cs, i, hcs, X, hX =>
    ⟨(hcs _ (.head _)).liftN,
      minorTypes_closedN (i := i+1) (fun c h => hcs _ (.tail _ h))
        (X := X)
        (by rw [show 1+(i+1)+cs.length = 1+i+(cs.length+1) from by omega]; exact hX)⟩

theorem motiveType_closedN {U : Nat} {T : Name} {k : Nat} :
    (motiveType U T).ClosedN k := ⟨trivial, trivial⟩

theorem recType_closedN {U : Nat} {T : Name} {ty : VInductiveType}
    (hcs : ∀ c ∈ ty.ctors, stage1Ctor U T c.type) : (recType U T ty).ClosedN 0 := by
  refine ⟨motiveType_closedN, ?_⟩
  apply minorTypes_closedN (fun c h => minorType_closedN1 (hcs c h))
  exact ⟨trivial, show _ < _ by omega, show _ < _ by omega⟩

theorem minorTypes_getElem? {U : Nat} {T : Name} : ∀ (cs : List VConstVal) (i₀ q : Nat),
    (minorTypes U T cs i₀)[q]? = cs[q]?.map fun c => VExpr.liftN (i₀+q) (minorType U T c)
  | [], _, q => by simp [minorTypes]
  | c :: cs, i₀, 0 => by simp [minorTypes]
  | c :: cs, i₀, q+1 => by
    simp only [minorTypes, List.getElem?_cons_succ]
    rw [minorTypes_getElem? cs (i₀+1) q, show i₀+1+q = i₀+(q+1) from by omega]

/-- `ctorType_isType` without the `Stage1Env` bundle: only the parts
available before the constructor has itself been added. -/
theorem ctorType_isType' {env : VEnv} {U : Nat} {T : Name} {l : VLevel} {ct : VExpr}
    (ord : env.Ordered) (hT : env.constants T = some ⟨U, .sort l⟩) (hl : l.WF U)
    (hs1c : stage1Ctor U T ct)
    (hfield : ∀ B ∈ ctorFields ct, B.ClosedN 0 → ∃ u, env.HasType U [] B (.sort u)) :
    env.IsType U [] ct := by
  have tconst : ∀ Γ, env.HasType U Γ (.const T (VLevel.params U)) (.sort l) := fun Γ => by
    have := VEnv.HasType.const (Γ := Γ) hT VLevel.params_wf VLevel.params_length
    simpa [VExpr.instL, VLevel.inst_id hl] using this
  obtain ⟨he, hBs⟩ := stage1Ctor_eq hs1c
  rw [he]
  refine VEnv.isType_forallN_free (fun B hB Γ => ?_) (fun Γ => ⟨_, tconst Γ⟩) []
  rcases stage1Field_iff.1 (hBs B hB) with rfl | ⟨hcl, -⟩
  · exact ⟨_, tconst Γ⟩
  · have ⟨u, h⟩ := hfield B hB hcl
    exact ⟨_, h.weak0 ord⟩

theorem motiveType_levelWF {U : Nat} {T : Name} : (motiveType U T).LevelWF (U+1) :=
  ⟨VLevel.params'_one_wf, Nat.succ_pos U⟩

theorem minorType_levelWF {U : Nat} {T : Name} {c : VConstVal} :
    (minorType U T c).LevelWF (U+1) := by
  simp only [minorType]
  refine VExpr.LevelWF.forallN (fun B hB => ?_)
    (VExpr.LevelWF.forallN (ihsFrom_levelWF _ _) ⟨trivial, ?_⟩)
  · obtain ⟨B₀, _, rfl⟩ := List.mem_map.1 hB
    exact VExpr.LevelWF.instL VLevel.params'_one_wf
  · exact VExpr.LevelWF.appN (f := .const c.name (VLevel.params' U 1))
      VLevel.params'_one_wf (bvarRevRange_levelWF _ _)

theorem minorTypes_levelWF {U : Nat} {T : Name} : ∀ (cs : List VConstVal) (i : Nat),
    ∀ e ∈ minorTypes U T cs i, e.LevelWF (U+1)
  | _ :: cs, i, e, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact minorType_levelWF.liftN
    · exact minorTypes_levelWF cs (i+1) e h

theorem recType_levelWF {U : Nat} {T : Name} {ty : VInductiveType} :
    (recType U T ty).LevelWF (U+1) :=
  ⟨motiveType_levelWF, VExpr.LevelWF.forallN (minorTypes_levelWF _ _)
    ⟨VLevel.params'_one_wf, trivial, trivial⟩⟩

/-- Consume the induction-hypothesis telescope with well-typed values. -/
theorem hasType_appN_ihs {env : VEnv} {U : Nat} {Γ : List VExpr} {m k : Nat}
    {argOf : Nat → VExpr} {Dfin : VExpr} :
    ∀ {rs : List Nat} {g : VExpr},
    (∀ j ∈ rs, env.HasType U Γ (argOf j) (.app (.bvar (k + m)) (.bvar (m-1-j)))) →
    env.HasType U Γ g (VExpr.forallN (ihsR m k rs 0) (Dfin.liftN rs.length)) →
    env.HasType U Γ (g.appN (rs.map argOf)) Dfin
  | [], g, _, hg => by simpa using hg
  | j :: rs, g, hargs, hg => by
    have happ := VEnv.HasType.app hg (hargs j (.head _))
    simp only [List.length_cons] at happ
    rw [show Dfin.liftN (rs.length+1) =
        (Dfin.liftN rs.length).liftN 1 (0 + rs.length) from by
        rw [Nat.zero_add, VExpr.liftN'_liftN' (Nat.zero_le _) (by omega)],
      ihsR_liftN1 m k rs 0 0 (Nat.le_refl _) (Dfin.liftN rs.length),
      VExpr.inst_liftN1] at happ
    exact hasType_appN_ihs (rs := rs) (fun j h => hargs j (.tail _ h)) happ

open VEnv

variable {env : VEnv} {U : Nat} {T : Name} {l : VLevel} {cs : List VConstVal}

/-- Everything the piece-typing lemmas need about an environment that
already contains the block's type constant and constructors. Holds of the
intermediate environment of `addInduct` after those `addConst`s, and is
monotone in the environment. -/
structure Stage1Env (env : VEnv) (U : Nat) (T : Name) (l : VLevel) (cs : List VConstVal) : Prop where
  ord : env.Ordered
  hl : l.WF U
  hT : env.constants T = some ⟨U, .sort l⟩
  hcs : ∀ c ∈ cs, env.constants c.name = some ⟨U, c.type⟩
  hs1 : ∀ c ∈ cs, stage1Ctor U T c.type
  hfield : ∀ c ∈ cs, ∀ B ∈ ctorFields c.type, B.ClosedN 0 →
    ∃ u, env.HasType U [] B (.sort u)

theorem Stage1Env.mono {env' : VEnv} (S : Stage1Env env U T l cs)
    (henv : env ≤ env') (ord' : env'.Ordered) : Stage1Env env' U T l cs where
  ord := ord'
  hl := S.hl
  hT := henv.constants S.hT
  hcs := fun c hc => henv.constants (S.hcs c hc)
  hs1 := S.hs1
  hfield := fun c hc B hB hcl =>
    let ⟨u, h⟩ := S.hfield c hc B hB hcl; ⟨u, h.mono henv⟩

variable (S : Stage1Env env U T l cs)
include S

/-- The type constant at the declaration's own universes. -/
theorem Stage1Env.tconst_decl {Γ} :
    env.HasType U Γ (.const T (VLevel.params U)) (.sort l) := by
  have := HasType.const (Γ := Γ) S.hT VLevel.params_wf VLevel.params_length
  simpa [VExpr.instL, VLevel.inst_id S.hl] using this

/-- The type constant in the recursor's universe context. -/
theorem Stage1Env.tconst {Γ} :
    env.HasType (U+1) Γ (.const T (VLevel.params' U 1))
      (.sort (l.inst (VLevel.params' U 1))) := by
  have := HasType.const (Γ := Γ) S.hT VLevel.params'_one_wf VLevel.params'_length
  simpa [VExpr.instL] using this

/-- Any stage-1 field, shifted into the recursor's universe context, is a
type in any context. -/
theorem Stage1Env.field_isType (hc : c ∈ cs) (hB : B ∈ ctorFields c.type) (Γ) :
    env.IsType (U+1) Γ (B.instL (VLevel.params' U 1)) := by
  rcases stage1Field_iff.1 ((stage1Ctor_eq (S.hs1 c hc)).2 B hB) with rfl | ⟨hcl, -⟩
  · rw [show (VExpr.const T (VLevel.params U)).instL (VLevel.params' U 1) =
      .const T (VLevel.params' U 1) by
        simp [VExpr.instL, VLevel.params_map_inst_params']]
    exact ⟨_, S.tconst⟩
  · have ⟨u, h⟩ := S.hfield c hc B hB hcl
    have := h.instL (U' := U+1) VLevel.params'_one_wf
    exact ⟨_, (this.weak0 S.ord : env.HasType _ Γ _ _)⟩

/-- Any stage-1 field at the declaration's own universes is a type in any
context. -/
theorem Stage1Env.field_isType_decl (hc : c ∈ cs) (hB : B ∈ ctorFields c.type) (Γ) :
    env.IsType U Γ B := by
  rcases stage1Field_iff.1 ((stage1Ctor_eq (S.hs1 c hc)).2 B hB) with rfl | ⟨hcl, -⟩
  · exact ⟨_, S.tconst_decl⟩
  · have ⟨u, h⟩ := S.hfield c hc B hB hcl
    exact ⟨_, h.weak0 S.ord⟩

/-- A constructor's declared type is well-formed over any stage-1
environment containing the block head (used at its `addConst` step, where
`cs` is the list of previously added constructors). -/
theorem Stage1Env.ctorType_isType (hc : c ∈ cs) : env.IsType U [] c.type := by
  obtain ⟨he, -⟩ := stage1Ctor_eq (S.hs1 c hc)
  rw [he]
  exact isType_forallN_free (fun B hB Γ => S.field_isType_decl hc hB Γ)
    (fun Γ => ⟨_, S.tconst_decl⟩) []

theorem Stage1Env.fields_closed (hc : c ∈ cs) :
    ∀ B ∈ ctorFields c.type, B.ClosedN 0 :=
  fun _ hB => stage1Field_closed ((stage1Ctor_eq (S.hs1 c hc)).2 _ hB)

/-- The constructor's type in the recursor's universe context. -/
theorem Stage1Env.ctorType_instL (hc : c ∈ cs) :
    c.type.instL (VLevel.params' U 1) =
    VExpr.forallN ((ctorFields c.type).map (VExpr.instL (VLevel.params' U 1)))
      (.const T (VLevel.params' U 1)) := by
  conv => lhs; rw [(stage1Ctor_eq (S.hs1 c hc)).1]
  rw [VExpr.instL_forallN]
  simp [VExpr.instL, VLevel.params_map_inst_params']

theorem Stage1Env.ctorConst (hc : c ∈ cs) {Γ} :
    env.HasType (U+1) Γ (.const c.name (VLevel.params' U 1))
      (VExpr.forallN ((ctorFields c.type).map (VExpr.instL (VLevel.params' U 1)))
        (.const T (VLevel.params' U 1))) := by
  have := HasType.const (Γ := Γ) (S.hcs c hc)
    VLevel.params'_one_wf VLevel.params'_length
  rwa [S.ctorType_instL hc] at this

theorem Stage1Env.motive_isType (Γ) : env.IsType (U+1) Γ (motiveType U T) :=
  ⟨_, HasType.forallE S.tconst (HasType.sort (Nat.succ_pos U))⟩

/-- Well-formedness of the induction-hypothesis telescope, at any suffix
of the recursive positions and any depth. -/
theorem Stage1Env.ihs_onTel (hc : c ∈ cs) :
    ∀ (rsSuf : List Nat),
    (∀ j ∈ rsSuf, ((ctorFields c.type).map (VExpr.instL (VLevel.params' U 1)))[j]? =
      some (.const T (VLevel.params' U 1))) →
    ∀ (Δ : List VExpr) (p : Nat), Δ.length = p →
    OnTel env (U+1)
      (Δ ++ ((ctorFields c.type).map (VExpr.instL (VLevel.params' U 1))).reverse
        ++ [motiveType U T])
      (ihsFrom (ctorFields c.type).length rsSuf p)
  | [], _, _, _, _ => trivial
  | j :: rsSuf, hjs, Δ, p, hΔ => by
    have hj := hjs j (.head _)
    have hjlt : j < (ctorFields c.type).length := by
      have := (List.getElem?_eq_some_iff.1 hj).1
      simpa using this
    have hM := getElem?_stack3 Δ
      ((ctorFields c.type).map (VExpr.instL (VLevel.params' U 1))).reverse []
      (motiveType U T)
      (i := (ctorFields c.type).length + p)
      (by simp only [hΔ, List.length_reverse, List.length_map]; omega)
    have hF := getElem?_stack_mid Δ
      ((ctorFields c.type).map (VExpr.instL (VLevel.params' U 1))).reverse
      [motiveType U T]
      (i := (ctorFields c.type).length - 1 - j + p)
      (by rw [hΔ]; omega)
      (by simp only [hΔ, List.length_reverse, List.length_map]; omega)
    rw [show (ctorFields c.type).length - 1 - j + p - Δ.length =
        (ctorFields c.type).length - 1 - j from by rw [hΔ]; omega,
      List.getElem?_reverse (by simp only [List.length_map]; omega),
      show ((ctorFields c.type).map (VExpr.instL (VLevel.params' U 1))).length - 1 -
        ((ctorFields c.type).length - 1 - j) = j from by
          simp only [List.length_map]; omega,
      hj] at hF
    refine ⟨⟨_, HasType.app
      (.bvar (Lookup.of_getElem?_closed hM motiveType_closedN))
      (.bvar (Lookup.of_getElem?_closed hF trivial))⟩, ?_⟩
    exact Stage1Env.ihs_onTel hc rsSuf (fun j h => hjs j (.tail _ h)) (_ :: Δ) (p+1)
      (by simp [hΔ])

/-- The minor premise for a constructor is a type over `[motive]`. -/
theorem Stage1Env.minor_isType (hc : c ∈ cs) :
    env.IsType (U+1) [motiveType U T] (minorType U T c) := by
  simp only [minorType]
  refine IsType.forallN (onTel_of_free fun B hB Γ' => ?_) ?_
  · obtain ⟨B₀, hB₀, rfl⟩ := List.mem_map.1 hB
    exact S.field_isType hc hB₀ Γ'
  · refine IsType.forallN
      (S.ihs_onTel hc _ (fun j hj => ?_) [] 0 rfl) ?_
    · have h0 := recIdxs_getElem _ hj
      rw [Nat.sub_zero] at h0
      rw [List.getElem?_map, h0]
      simp [VExpr.instL, VLevel.params_map_inst_params']
    · rw [← List.append_assoc]
      refine ⟨_, HasType.app (.bvar (Lookup.of_getElem?_closed
        (getElem?_stack3 _ _ [] _ (by
          simp only [List.length_reverse, ihsFrom_length, List.length_map]; omega))
        motiveType_closedN)) ?_⟩
      have hcl : (VExpr.forallN
          ((ctorFields c.type).map (VExpr.instL (VLevel.params' U 1)))
          (.const T (VLevel.params' U 1))).ClosedN 0 :=
        ClosedN.forallN_of_all
          (fun B hB => by
            obtain ⟨B₀, hB₀, rfl⟩ := List.mem_map.1 hB
            exact (S.fields_closed hc _ hB₀).instL)
          (B := .const T (VLevel.params' U 1)) trivial
      have := HasType.appN_selfSpine'
        (Δ := (ihsFrom (ctorFields c.type).length
          (recIdxs U T (ctorFields c.type)) 0).reverse)
        (Γ := [motiveType U T]) hcl (S.ctorConst hc)
      simpa only [List.length_reverse, ihsFrom_length, List.length_map] using this

/-- The minor premises, in position, are a telescope over `[motive]`. -/
theorem Stage1Env.minorTypes_onTel :
    ∀ (cs' : List VConstVal), (∀ c ∈ cs', c ∈ cs) →
    ∀ (Δ : List VExpr) (i : Nat), Δ.length = i →
    OnTel env (U+1) (Δ ++ [motiveType U T]) (minorTypes U T cs' i)
  | [], _, _, _, _ => trivial
  | c :: cs', hsub, Δ, i, hΔ =>
    ⟨by
      rw [← hΔ]
      exact (S.minor_isType (hsub c (.head _))).weakN S.ord (.zero Δ),
    Stage1Env.minorTypes_onTel cs' (fun c h => hsub c (.tail _ h)) (_ :: Δ) (i+1)
      (by simp [hΔ])⟩

end VInductDecl

namespace VInductDecl
open VEnv

/-- The generated recursor type is well-formed once the block's type and
constructors are present. -/
theorem Stage1Env.recType_isType {env : VEnv} {U : Nat} {T : Name} {l : VLevel}
    {ty : VInductiveType} (S : Stage1Env env U T l ty.ctors) :
    env.IsType (U+1) [] (recType U T ty) := by
  refine IsType.forallE (S.motive_isType []) ?_
  refine IsType.forallN (S.minorTypes_onTel ty.ctors (fun c h => h) [] 0 rfl) ?_
  refine IsType.forallE ⟨_, S.tconst⟩
    ⟨_, HasType.app (.bvar (Lookup.of_getElem?_closed ?_ motiveType_closedN))
      (.bvar (Lookup.of_getElem?_closed rfl trivial))⟩
  show (VExpr.const T (VLevel.params' U 1) ::
    ((minorTypes U T ty.ctors).reverse ++ ([] ++ [motiveType U T])))[ty.ctors.length + 1]? =
    some (motiveType U T)
  rw [List.getElem?_cons_succ]
  exact getElem?_stack3 [] (minorTypes U T ty.ctors).reverse []
    (motiveType U T)
    (by simp only [List.length_reverse, minorTypes_length, List.length_nil]; omega)

theorem Stage1Env.recConst_wf {env : VEnv} {U : Nat} {T : Name} {l : VLevel}
    {ty : VInductiveType} (S : Stage1Env env U T l ty.ctors) :
    (recConst U T ty).WF env :=
  S.recType_isType

end VInductDecl

/-! ## The iota rules -/

namespace VInductDecl
open VEnv

variable {env : VEnv} {U : Nat} {T : Name} {l : VLevel} {ty : VInductiveType}
  (S : Stage1Env env U T l ty.ctors)
include S

/-- The recursor constant at its own (identity) universe list. -/
theorem Stage1Env.recConst_hasType
    (hrec : env.constants (.str T "rec") = some (recConst U T ty)) {Γ} :
    env.HasType (U+1) Γ (.const (.str T "rec") (VLevel.params (U+1)))
      (recType U T ty) := by
  have := HasType.const (Γ := Γ) hrec VLevel.params_wf VLevel.params_length
  rw [show (recConst U T ty).uvars = U + 1 from rfl,
    show (recConst U T ty).type = recType U T ty from rfl] at this
  rwa [recType_levelWF.instL_id] at this

/-- The recursor spine of an iota rule, applied to one major argument, in
the rule's binder context. -/
theorem Stage1Env.recApp_hasType
    (hrec : env.constants (.str T "rec") = some (recConst U T ty))
    {c : VConstVal} (hc : c ∈ ty.ctors) {a : VExpr}
    (ha : env.HasType (U+1)
      (((ctorFields c.type).map (VExpr.instL (VLevel.params' U 1))).reverse ++
        ((minorTypes U T ty.ctors).reverse ++ [motiveType U T])) a
      (.const T (VLevel.params' U 1))) :
    env.HasType (U+1)
      (((ctorFields c.type).map (VExpr.instL (VLevel.params' U 1))).reverse ++
        ((minorTypes U T ty.ctors).reverse ++ [motiveType U T]))
      ((VExpr.appN (.const (.str T "rec") (VLevel.params (U+1)))
        (VExpr.bvarRevRange (ctorFields c.type).length (ty.ctors.length + 1))).app a)
      (.app (.bvar (ty.ctors.length + (ctorFields c.type).length)) a) := by
  have hspine := HasType.appN_selfSpine (env := env) (U := U + 1)
    (As := motiveType U T :: minorTypes U T ty.ctors)
    (B := .forallE (.const T (VLevel.params' U 1))
      (.app (.bvar (ty.ctors.length + 1)) (.bvar 0)))
    (Δ := ((ctorFields c.type).map (VExpr.instL (VLevel.params' U 1))).reverse)
    (Γ := []) (f := .const (.str T "rec") (VLevel.params (U+1))) ?hf
  case hf =>
    rw [show VExpr.forallN (motiveType U T :: minorTypes U T ty.ctors)
        (.forallE (.const T (VLevel.params' U 1))
          (.app (.bvar (ty.ctors.length + 1)) (.bvar 0))) = recType U T ty from rfl,
      (recType_closedN fun c h => S.hs1 c h).liftN_eq (Nat.zero_le _)]
    exact S.recConst_hasType hrec
  simp only [List.reverse_cons, List.append_nil, List.append_assoc, List.length_reverse,
    List.length_map, List.length_cons, minorTypes_length] at hspine
  rw [show (VExpr.forallE (.const T (VLevel.params' U 1))
      (.app (.bvar (ty.ctors.length + 1)) (.bvar 0))).liftN (ctorFields c.type).length =
    .forallE (.const T (VLevel.params' U 1))
      (.app (.bvar (ty.ctors.length + 1 + (ctorFields c.type).length)) (.bvar 0))
    from ?hB] at hspine
  case hB =>
    show VExpr.forallE _ _ = _
    congr 1
    show VExpr.app _ _ = _
    congr 1
    show VExpr.bvar (liftVar _ _ _) = _
    rw [liftVar_le (by omega)]
    congr 1; omega
  have happ := HasType.app hspine ha
  rwa [show (VExpr.app
      (.bvar (ty.ctors.length + 1 + (ctorFields c.type).length)) (.bvar 0)).inst a =
    .app (.bvar (ty.ctors.length + (ctorFields c.type).length)) a from ?hinst] at happ
  case hinst =>
    show VExpr.app _ _ = _
    congr 1
    · show VExpr.instVar _ a 0 = _
      unfold VExpr.instVar
      rw [if_neg (by omega), if_neg (by omega)]
      congr 1; omega
    · exact VExpr.instVar_zero

/-- The constructor-headed major, in the rule's binder context. -/
theorem Stage1Env.ctorApp_hasType {c : VConstVal} (hc : c ∈ ty.ctors) :
    env.HasType (U+1)
      (((ctorFields c.type).map (VExpr.instL (VLevel.params' U 1))).reverse ++
        ((minorTypes U T ty.ctors).reverse ++ [motiveType U T]))
      (VExpr.appN (.const c.name (VLevel.params' U 1))
        (VExpr.bvarRevRange 0 (ctorFields c.type).length))
      (.const T (VLevel.params' U 1)) := by
  have hcl : (VExpr.forallN ((ctorFields c.type).map (VExpr.instL (VLevel.params' U 1)))
      (.const T (VLevel.params' U 1))).ClosedN 0 :=
    ClosedN.forallN_of_all
      (fun B hB => by
        obtain ⟨B₀, hB₀, rfl⟩ := List.mem_map.1 hB
        exact (S.fields_closed hc _ hB₀).instL)
      (B := .const T (VLevel.params' U 1)) trivial
  have := HasType.appN_selfSpine' (Δ := [])
    (Γ := (minorTypes U T ty.ctors).reverse ++ [motiveType U T])
    hcl (S.ctorConst hc)
  simpa [List.length_map] using this

theorem Stage1Env.ruleBinders_onTel {c : VConstVal} (hc : c ∈ ty.ctors) :
    OnTel env (U+1) []
      (motiveType U T :: minorTypes U T ty.ctors ++
        (ctorFields c.type).map (VExpr.instL (VLevel.params' U 1))) :=
  ⟨S.motive_isType [], OnTel.append
    (S.minorTypes_onTel ty.ctors (fun _ h => h) [] 0 rfl)
    (onTel_of_free fun B hB Γ' => by
      obtain ⟨B₀, hB₀, rfl⟩ := List.mem_map.1 hB
      exact S.field_isType hc hB₀ Γ')⟩

theorem Stage1Env.ruleType_isType {i : Nat} {c : VConstVal}
    (hci : ty.ctors[i]? = some c) :
    env.IsType (U+1) [] ((rule U T ty i c).type) := by
  have hc := List.mem_of_getElem? hci
  show env.IsType (U+1) [] (VExpr.forallN
    (motiveType U T :: minorTypes U T ty.ctors ++
      (ctorFields c.type).map (VExpr.instL (VLevel.params' U 1)))
    (.app (.bvar (ty.ctors.length + (ctorFields c.type).length))
      (VExpr.appN (.const c.name (VLevel.params' U 1))
        (VExpr.bvarRevRange 0 (ctorFields c.type).length))))
  refine IsType.forallN (S.ruleBinders_onTel hc) ?_
  simp only [List.reverse_cons, List.reverse_append, List.append_nil, List.append_assoc]
  refine ⟨_, HasType.app (.bvar (Lookup.of_getElem?_closed
    (getElem?_rstack3 _ _ (motiveType U T) [] ?_) motiveType_closedN))
    (S.ctorApp_hasType hc)⟩
  simp only [List.length_reverse, List.length_map, minorTypes_length]
  omega

/-- The right-hand side of an iota rule: the constructor's minor premise
applied to the fields and the recursive calls, in the rule's binder
context. -/
theorem Stage1Env.minorApp_hasType {i : Nat} {c : VConstVal}
    (hci : ty.ctors[i]? = some c)
    (hrec : env.constants (.str T "rec") = some (recConst U T ty)) :
    env.HasType (U+1)
      (((ctorFields c.type).map (VExpr.instL (VLevel.params' U 1))).reverse ++
        ((minorTypes U T ty.ctors).reverse ++ [motiveType U T]))
      (VExpr.appN (.bvar (ty.ctors.length - 1 - i + (ctorFields c.type).length))
        (VExpr.bvarRevRange 0 (ctorFields c.type).length ++
          (recIdxs U T (ctorFields c.type)).map fun j =>
            (VExpr.appN (.const (.str T "rec") (VLevel.params (U+1)))
              (VExpr.bvarRevRange (ctorFields c.type).length (ty.ctors.length + 1))).app
              (.bvar ((ctorFields c.type).length - 1 - j))))
      (.app (.bvar (ty.ctors.length + (ctorFields c.type).length))
        (VExpr.appN (.const c.name (VLevel.params' U 1))
          (VExpr.bvarRevRange 0 (ctorFields c.type).length))) := by
  obtain ⟨hik, -⟩ := List.getElem?_eq_some_iff.1 hci
  have hc := List.mem_of_getElem? hci
  have hBs' : ∀ B ∈ (ctorFields c.type).map (VExpr.instL (VLevel.params' U 1)),
      B.ClosedN 0 := fun B hB => by
    obtain ⟨B₀, hB₀, rfl⟩ := List.mem_map.1 hB
    exact (S.fields_closed hc _ hB₀).instL
  rw [VExpr.appN_append]
  -- the minor premise variable, at its lifted type
  have hlu0 : ((((ctorFields c.type).map (VExpr.instL (VLevel.params' U 1))).reverse ++
      ((minorTypes U T ty.ctors).reverse ++ [motiveType U T])))[
        ty.ctors.length - 1 - i + (ctorFields c.type).length]? =
      some (VExpr.liftN i (minorType U T c)) := by
    rw [getElem?_rstack_mid _ _ _
        (by simp only [List.length_reverse, List.length_map]; omega)
        (by simp only [List.length_reverse, List.length_map, minorTypes_length]; omega),
      show ty.ctors.length - 1 - i + (ctorFields c.type).length -
        (((ctorFields c.type).map (VExpr.instL (VLevel.params' U 1))).reverse).length =
        ty.ctors.length - 1 - i from by
          simp only [List.length_reverse, List.length_map]; omega,
      List.getElem?_reverse (by simp only [minorTypes_length]; omega),
      show (minorTypes U T ty.ctors).length - 1 - (ty.ctors.length - 1 - i) = i from by
        simp only [minorTypes_length]; omega,
      minorTypes_getElem?, hci, Nat.zero_add]
    rfl
  have hlu := Lookup.of_getElem? hlu0
  rw [VExpr.liftN_liftN,
    show i + (ty.ctors.length - 1 - i + (ctorFields c.type).length + 1) =
      (ctorFields c.type).length + ty.ctors.length from by omega] at hlu
  -- phase 1: consume the field binders by self-application
  have hminorEq : (minorType U T c).liftN
      ((ctorFields c.type).length + ty.ctors.length) =
      (VExpr.forallN ((ctorFields c.type).map (VExpr.instL (VLevel.params' U 1)))
        ((VExpr.forallN
          (ihsFrom (ctorFields c.type).length (recIdxs U T (ctorFields c.type)) 0)
          (.app (.bvar ((ctorFields c.type).length +
              (recIdxs U T (ctorFields c.type)).length))
            (VExpr.appN (.const c.name (VLevel.params' U 1))
              (VExpr.bvarRevRange (recIdxs U T (ctorFields c.type)).length
                (ctorFields c.type).length)))).liftN
          ty.ctors.length (ctorFields c.type).length)).liftN
        (ctorFields c.type).length := by
    simp only [minorType]
    rw [VExpr.liftN_forallN_closed hBs', VExpr.liftN_forallN_closed hBs']
    congr 1
    rw [show (0:Nat) + ((ctorFields c.type).map (VExpr.instL (VLevel.params' U 1))).length =
      (ctorFields c.type).length from by simp [List.length_map],
      VExpr.liftN'_liftN_hi,
      Nat.add_comm ty.ctors.length (ctorFields c.type).length]
  have hspine1 := HasType.appN_selfSpine (env := env) (U := U + 1)
    (As := (ctorFields c.type).map (VExpr.instL (VLevel.params' U 1)))
    (B := (VExpr.forallN
        (ihsFrom (ctorFields c.type).length (recIdxs U T (ctorFields c.type)) 0)
        (.app (.bvar ((ctorFields c.type).length +
            (recIdxs U T (ctorFields c.type)).length))
          (VExpr.appN (.const c.name (VLevel.params' U 1))
            (VExpr.bvarRevRange (recIdxs U T (ctorFields c.type)).length
              (ctorFields c.type).length)))).liftN
        ty.ctors.length (ctorFields c.type).length)
    (Δ := []) (Γ := (minorTypes U T ty.ctors).reverse ++ [motiveType U T])
    (f := .bvar (ty.ctors.length - 1 - i + (ctorFields c.type).length)) ?hf1
  case hf1 =>
    have hb := VEnv.HasType.bvar (env := env) (U := U+1) hlu
    rw [hminorEq] at hb
    simpa [List.length_map] using hb
  simp only [List.length_nil, List.length_map, VExpr.liftN_zero] at hspine1
  rw [ihsFrom_liftN' (ctorFields c.type).length ty.ctors.length
    (recIdxs U T (ctorFields c.type))
    (fun j hj => by have := recIdxs_lt _ hj; omega) 0
    (.app (.bvar ((ctorFields c.type).length + (recIdxs U T (ctorFields c.type)).length))
      (VExpr.appN (.const c.name (VLevel.params' U 1))
        (VExpr.bvarRevRange (recIdxs U T (ctorFields c.type)).length
          (ctorFields c.type).length)))
    (cut := (ctorFields c.type).length) rfl] at hspine1
  -- rewrite the instantiated result into the final form, lifted past the ihs
  rw [show (VExpr.app (.bvar ((ctorFields c.type).length +
        (recIdxs U T (ctorFields c.type)).length))
      (VExpr.appN (.const c.name (VLevel.params' U 1))
        (VExpr.bvarRevRange (recIdxs U T (ctorFields c.type)).length
          (ctorFields c.type).length))).liftN ty.ctors.length
      ((ctorFields c.type).length + 0 + (recIdxs U T (ctorFields c.type)).length) =
    (VExpr.app (.bvar (ty.ctors.length + (ctorFields c.type).length))
      (VExpr.appN (.const c.name (VLevel.params' U 1))
        (VExpr.bvarRevRange 0 (ctorFields c.type).length))).liftN
      (recIdxs U T (ctorFields c.type)).length from ?hres] at hspine1
  case hres =>
    show VExpr.app _ _ = VExpr.app _ _
    congr 1
    · show VExpr.bvar (liftVar _ _ _) = VExpr.bvar (liftVar _ _ _)
      rw [liftVar_le (by omega), liftVar_le (Nat.zero_le _)]
      congr 1; omega
    · rw [VExpr.liftN_appN, VExpr.liftN_appN,
        VExpr.bvarRevRange_liftN_high _ _ _ _ (by omega),
        VExpr.bvarRevRange_liftN_low]
      rfl
  -- phase 2: consume the induction hypotheses
  refine hasType_appN_ihs (fun j hj => ?_) hspine1
  have hjm := recIdxs_lt _ hj
  refine S.recApp_hasType hrec hc (.bvar (Lookup.of_getElem?_closed ?_ trivial))
  rw [List.getElem?_append_left
      (by simp only [List.length_reverse, List.length_map]; omega),
    List.getElem?_reverse (by simp only [List.length_map]; omega),
    show (((ctorFields c.type).map (VExpr.instL (VLevel.params' U 1))).length - 1 -
      ((ctorFields c.type).length - 1 - j)) = j from by
        simp only [List.length_map]; omega]
  have h0 := recIdxs_getElem _ hj
  rw [Nat.sub_zero] at h0
  rw [List.getElem?_map, h0]
  simp [VExpr.instL, VLevel.params_map_inst_params']

/-- Well-formedness of the iota rule for the `i`-th constructor. -/
theorem Stage1Env.rule_WF {i : Nat} {c : VConstVal}
    (hci : ty.ctors[i]? = some c)
    (hrec : env.constants (.str T "rec") = some (recConst U T ty)) :
    (rule U T ty i c).WF env := by
  have hc := List.mem_of_getElem? hci
  refine ⟨?_, ?_⟩
  · show env.HasType (U+1) [] (VExpr.lamN
      (motiveType U T :: minorTypes U T ty.ctors ++
        (ctorFields c.type).map (VExpr.instL (VLevel.params' U 1))) _)
      (VExpr.forallN _ _)
    refine HasType.lamN (S.ruleBinders_onTel hc) ?_
    simp only [List.reverse_cons, List.reverse_append, List.append_nil, List.append_assoc]
    exact S.recApp_hasType hrec hc (S.ctorApp_hasType hc)
  · show env.HasType (U+1) [] (VExpr.lamN
      (motiveType U T :: minorTypes U T ty.ctors ++
        (ctorFields c.type).map (VExpr.instL (VLevel.params' U 1))) _)
      (VExpr.forallN _ _)
    refine HasType.lamN (S.ruleBinders_onTel hc) ?_
    simp only [List.reverse_cons, List.reverse_append, List.append_nil, List.append_assoc]
    exact S.minorApp_hasType hci hrec

end VInductDecl

/-! ## `addInduct_WF` -/

theorem _root_.List.mem_zipIdx_getElem? {α} : ∀ {l : List α} {n : Nat} {a : α} {i : Nat},
    (a, i) ∈ l.zipIdx n → n ≤ i ∧ l[i - n]? = some a
  | b :: l, n, a, i, h => by
    simp only [List.zipIdx] at h
    rcases List.mem_cons.1 h with h | h
    · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h
      simp
    · obtain ⟨h1, h2⟩ := List.mem_zipIdx_getElem? h
      refine ⟨by omega, ?_⟩
      rw [show i - n = (i - (n+1)) + 1 from by omega]
      simpa using h2

namespace VInductDecl

/-- Unpack the semantic constructor conditions over an extension containing
the block's type constant. -/
theorem ctorWF_fields {env env' : VEnv} {U : Nat} {T : Name} {l : VLevel}
    (hle : env ≤ env') (hT : env'.constants T = some ⟨U, .sort l⟩) (hl : l.WF U) :
    ∀ {ct : VExpr}, ctorWF U T env l ct →
    ∀ B ∈ ctorFields ct, B.ClosedN 0 → ∃ u, env'.HasType U [] B (.sort u)
  | .forallE B rest, ⟨hB, hrest⟩, B', hB', hcl => by
    simp only [ctorFields] at hB'
    rcases List.mem_cons.1 hB' with rfl | h'
    · rcases hB with rfl | ⟨u, h, -⟩
      · refine ⟨l, ?_⟩
        have := VEnv.HasType.const (Γ := []) hT VLevel.params_wf VLevel.params_length
        simpa [VExpr.instL, VLevel.inst_id hl] using this
      · exact ⟨u, h.mono hle⟩
    · exact ctorWF_fields hle hT hl hrest B' h' hcl

/-- Adding the constructors of a stage-1 block preserves order and records
their lookups. -/
theorem ctorFold_WF {U : Nat} {T : Name} {l : VLevel} :
    ∀ (cs' : List VConstVal) {env₀ env₁ : VEnv},
    env₀.Ordered → env₀.constants T = some ⟨U, .sort l⟩ → l.WF U →
    (∀ c ∈ cs', c.uvars = U ∧ stage1Ctor U T c.type ∧
      ∀ B ∈ ctorFields c.type, B.ClosedN 0 → ∃ u, env₀.HasType U [] B (.sort u)) →
    List.foldlM (fun env (c : VConstVal) => env.addConst c.name c.toVConstant) env₀ cs' =
      some env₁ →
    env₁.Ordered ∧ env₀ ≤ env₁ ∧
      ∀ c ∈ cs', env₁.constants c.name = some ⟨U, c.type⟩
  | [], env₀, env₁, ord, _, _, _, hfold => by
    cases hfold
    exact ⟨ord, .rfl, nofun⟩
  | c :: cs', env₀, env₁, ord, hT, hl, hcs, hfold => by
    rw [List.foldlM_cons] at hfold
    obtain ⟨env₀', hadd, hrest⟩ := Option.bind_eq_some_iff.1 hfold
    obtain ⟨hcU, hs1c, hfields⟩ := hcs c (.head _)
    have hwfc : c.toVConstant.WF env₀ := by
      show env₀.IsType c.toVConstant.uvars [] c.toVConstant.type
      rw [show c.toVConstant.uvars = c.uvars from rfl, hcU]
      exact ctorType_isType' ord hT hl hs1c hfields
    have ord' : env₀'.Ordered := .const ord hwfc hadd
    have hle' := VEnv.addConst_le hadd
    obtain ⟨ord₁, hle₁, hlook⟩ := ctorFold_WF cs' ord'
      (hle'.constants hT) hl
      (fun c' hc' => by
        obtain ⟨h1, h2, h3⟩ := hcs c' (.tail _ hc')
        exact ⟨h1, h2, fun B hB hcl =>
          let ⟨u, h⟩ := h3 B hB hcl; ⟨u, h.mono hle'⟩⟩)
      hrest
    refine ⟨ord₁, hle'.trans hle₁, fun c' hc' => ?_⟩
    rcases List.mem_cons.1 hc' with rfl | hc'
    · have hself := VEnv.addConst_self hadd
      rw [show c'.toVConstant = ⟨U, c'.type⟩ from by rw [← hcU]] at hself
      exact hle₁.constants hself
    · exact hlook c' hc'

theorem rulesFold_WF : ∀ (dfs : List VDefEq) {env₃ : VEnv},
    env₃.Ordered → (∀ df ∈ dfs, df.WF env₃) →
    (dfs.foldl VEnv.addDefEq env₃).Ordered
  | [], _, ord, _ => ord
  | df :: dfs, env₃, ord, hdfs => by
    rw [List.foldl_cons]
    exact rulesFold_WF dfs (.defeq ord (hdfs df (.head _)))
      (fun df' hdf' => (hdfs df' (.tail _ hdf')).mono VEnv.addDefEq_le)

end VInductDecl

namespace VEnv
open VInductDecl

theorem addInduct_WF (henv : Ordered env) (hdecl : decl.WF env)
    (henv' : addInduct env decl = some env') : Ordered env' := by
  obtain ⟨hs1, hwf⟩ := hdecl
  obtain ⟨U, np, tys⟩ := decl
  unfold addInduct at henv'
  obtain ⟨-, -, henv'⟩ := Option.bind_eq_some_iff.1 henv'
  match tys, hs1, hwf, henv' with
  | [ty], hs1, hwf, henv' => ?_
  obtain ⟨env₁, hadd1, henv'⟩ := Option.bind_eq_some_iff.1 henv'
  obtain ⟨env₂, hfold, henv'⟩ := Option.bind_eq_some_iff.1 henv'
  obtain ⟨env₃, hadd3, henv'⟩ := Option.bind_eq_some_iff.1 henv'
  cases henv'
  obtain ⟨-, htyU, ⟨l, hsort, hlWF, -⟩, hctors⟩ := stage1_anatomy hs1
  have hsl : sortLevel ty = l := by simp only [sortLevel, hsort]
  -- the type constant
  have hwfT : ty.toVConstant.WF env := by
    show env.IsType ty.toVConstant.uvars [] ty.toVConstant.type
    rw [show ty.toVConstant.uvars = ty.uvars from rfl, htyU,
      show ty.toVConstant.type = ty.type from rfl, hsort]
    exact ⟨_, HasType.sort hlWF⟩
  have ord₁ : env₁.Ordered := .const henv hwfT hadd1
  have hT₁ : env₁.constants ty.name = some ⟨U, .sort l⟩ := by
    have := addConst_self hadd1
    rwa [show ty.toVConstant = ⟨U, .sort l⟩ from by
      show (⟨ty.uvars, ty.type⟩ : VConstant) = _
      rw [htyU, hsort]] at this
  -- the constructors
  obtain ⟨ord₂, hle₂, hlook₂⟩ := ctorFold_WF ty.ctors ord₁ hT₁ hlWF
    (fun c hc => ⟨(hctors c hc).1, (hctors c hc).2,
      ctorWF_fields (addConst_le hadd1) hT₁ hlWF
        (by
          have := hwf ty (.head _) c hc
          rwa [hsl] at this)⟩)
    hfold
  -- the stage-1 environment invariant at env₂
  have S₂ : Stage1Env env₂ U ty.name l ty.ctors := by
    refine ⟨ord₂, hlWF, hle₂.constants hT₁, hlook₂, fun c hc => (hctors c hc).2,
      fun c hc B hB hcl => ?_⟩
    have := ctorWF_fields ((addConst_le hadd1).trans hle₂) (hle₂.constants hT₁) hlWF
      (by
        have := hwf ty (.head _) c hc
        rwa [hsl] at this) B hB hcl
    exact this
  -- the recursor
  have ord₃ : env₃.Ordered := .const ord₂ S₂.recConst_wf hadd3
  have S₃ : Stage1Env env₃ U ty.name l ty.ctors :=
    S₂.mono (addConst_le hadd3) ord₃
  have hrec₃ : env₃.constants (.str ty.name "rec") = some (recConst U ty.name ty) :=
    addConst_self hadd3
  -- the iota rules
  refine rulesFold_WF _ ord₃ fun df hdf => ?_
  obtain ⟨⟨c, i⟩, hmem, rfl⟩ := List.mem_map.1 hdf
  obtain ⟨-, hci⟩ := List.mem_zipIdx_getElem? hmem
  rw [Nat.sub_zero] at hci
  exact S₃.rule_WF hci hrec₃

end VEnv
