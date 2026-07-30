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

/-- Lifting through a dependent telescope. -/
theorem liftN_forallN (n : Nat) : ∀ (tel : List VExpr) (X : VExpr) (k : Nat),
    (forallN tel X).liftN n k = forallN (liftTelN n tel k) (X.liftN n (k + tel.length))
  | [], _, _ => rfl
  | A :: tel, X, k => by
    show VExpr.forallE _ _ = VExpr.forallE _ _
    rw [liftN_forallN n tel X (k+1),
      show k+1+tel.length = k+(tel.length+1) from by omega]
    rfl

theorem liftTelN_length (n : Nat) : ∀ (tel : List VExpr) (k : Nat),
    (liftTelN n tel k).length = tel.length
  | [], _ => rfl
  | _ :: tel, k => by simp [liftTelN, liftTelN_length n tel (k+1)]

theorem liftTelN_liftTelN (a b : Nat) : ∀ (tel : List VExpr) (k : Nat),
    liftTelN b (liftTelN a tel k) k = liftTelN (a+b) tel k
  | [], _ => rfl
  | A :: tel, k => by
    show _ :: _ = _ :: _
    rw [liftN'_liftN_hi, liftTelN_liftTelN a b tel (k+1)]

theorem liftTelN_getElem? (n : Nat) : ∀ (tel : List VExpr) (k q : Nat),
    (liftTelN n tel k)[q]? = tel[q]?.map fun A => A.liftN n (k+q)
  | [], _, q => by simp [liftTelN]
  | A :: tel, k, 0 => by simp [liftTelN]
  | A :: tel, k, q+1 => by
    simp only [liftTelN, List.getElem?_cons_succ]
    rw [liftTelN_getElem? n tel (k+1) q, show k+1+q = k+(q+1) from by omega]

end VExpr

/-! ## Anatomy of the stage-1 predicate -/

namespace VInductDecl

theorem stage2Field_iff {U T np j B} : stage2Field U T np j B ↔
    B = recApp U T np j ∨ B.hasConst T = false := by
  simp [stage2Field, Bool.or_eq_true]

theorem stage2Ctor_eq {U T np} : ∀ {j₀ : Nat} {e : VExpr}, stage2Ctor U T np j₀ e →
    e = VExpr.forallN (ctorFields e) (recApp U T np (j₀ + (ctorFields e).length)) ∧
    ∀ q B, (ctorFields e)[q]? = some B → stage2Field U T np (j₀ + q) B := by
  intro j₀ e h
  induction e generalizing j₀ with
  | forallE B rest _ ih =>
    simp only [stage2Ctor, Bool.and_eq_true] at h
    have ⟨ih1, ih2⟩ := ih h.2
    refine ⟨?_, ?_⟩
    · show VExpr.forallE _ _ = VExpr.forallE _ _
      conv => lhs; rw [ih1]
      rw [show j₀+1+(ctorFields rest).length = j₀+((ctorFields rest).length+1) from by omega]
      rfl
    · intro q B' hB'
      match q, hB' with
      | 0, hB' =>
        obtain rfl : B = B' := by simpa [ctorFields] using hB'
        exact h.1
      | q+1, hB' =>
        have := ih2 q B' (by simpa [ctorFields] using hB')
        rwa [show j₀+1+q = j₀+(q+1) from by omega] at this
  | bvar i =>
    simp only [stage2Ctor, beq_iff_eq] at h
    exact ⟨h, fun q B h' => by simp [ctorFields] at h'⟩
  | sort l =>
    simp only [stage2Ctor, beq_iff_eq] at h
    exact ⟨h, fun q B h' => by simp [ctorFields] at h'⟩
  | const c ls =>
    simp only [stage2Ctor, beq_iff_eq] at h
    exact ⟨h, fun q B h' => by simp [ctorFields] at h'⟩
  | app f a _ _ =>
    simp only [stage2Ctor, beq_iff_eq] at h
    exact ⟨h, fun q B h' => by simp [ctorFields] at h'⟩
  | lam A b _ _ =>
    simp only [stage2Ctor, beq_iff_eq] at h
    exact ⟨h, fun q B h' => by simp [ctorFields] at h'⟩

/-- Unpack `stage2` for a declaration already known (from `addInduct`
success) to have a singleton type list. -/
theorem stage2_anatomy {U np ty} (h : stage2 ⟨U, np, [ty]⟩) :
    ty.uvars = U ∧ (VExpr.telN np ty.type).length = np ∧
    (∃ l, VExpr.dropN np ty.type = .sort l ∧ l.WF U ∧ l.isNeverZero) ∧
    ∀ c ∈ ty.ctors, c.uvars = U ∧
      VExpr.telN np c.type = VExpr.telN np ty.type ∧
      stage2Ctor U ty.name np 0 (VExpr.dropN np c.type) := by
  simp only [stage2, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, ?_, fun c hc => by simpa [and_assoc] using h4 c hc⟩
  split at h3
  · next l heq => exact ⟨l, heq, by simpa [Bool.and_eq_true] using h3⟩
  · exact Bool.noConfusion h3

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

/-- Weakening a telescope: inserting binders at depth `k` of the context
shifts each entry at its own depth. -/
theorem OnTel.weakN {env : VEnv} {U n : Nat} (henv : env.Ordered) :
    ∀ {As Γ Γ' k}, Ctx.LiftN n k Γ Γ' → OnTel env U Γ As →
    OnTel env U Γ' (VExpr.liftTelN n As k)
  | [], _, _, _, _, _ => trivial
  | _ :: As, _, _, _, W, ⟨hA, hT⟩ =>
    ⟨hA.weakN henv W, OnTel.weakN henv W.succ hT⟩

/-- Universe instantiation of a telescope. -/
theorem OnTel.instL {env : VEnv} {U U' : Nat} {ls : List VLevel}
    (hls : ∀ l ∈ ls, l.WF U') :
    ∀ {As Γ}, OnTel env U Γ As →
    OnTel env U' (Γ.map (VExpr.instL ls)) (As.map (VExpr.instL ls))
  | [], _, _ => trivial
  | _ :: As, Γ, ⟨hA, hT⟩ =>
    ⟨hA.instL hls, by simpa using OnTel.instL hls (As := As) (Γ := _ :: Γ) hT⟩

end VEnv

/-! ## The induction-hypothesis telescope under lifting -/

namespace VInductDecl

/-- `ihsFrom` after the motive-directed lift into the rule context. -/
def ihsR (m k : Nat) : List Nat → Nat → List VExpr
  | [], _ => []
  | j :: rs, p => .app (.bvar (k + (m + p))) (.bvar (m-1-j+p)) :: ihsR m k rs (p+1)

/-- Recursive-field positions are bounded by the field count. -/
theorem recIdxs_lt {U : Nat} {T : Name} {np : Nat} : ∀ {Bs : List VExpr} {j₀ : Nat},
    ∀ j ∈ recIdxs U T np Bs j₀, j < j₀ + Bs.length
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

theorem minorTypes_length (U : Nat) (T : Name) (np : Nat) : ∀ (cs : List VConstVal) (i : Nat),
    (minorTypes U T np cs i).length = cs.length
  | [], _ => rfl
  | _ :: cs, i => by simp [minorTypes, minorTypes_length U T np cs (i+1)]

theorem recIdxs_ge {U : Nat} {T : Name} {np : Nat} : ∀ {Bs : List VExpr} {j₀ : Nat},
    ∀ j ∈ recIdxs U T np Bs j₀, j₀ ≤ j
  | _ :: Bs, j₀, j, h => by
    unfold recIdxs at h
    split at h
    · rcases List.mem_cons.1 h with rfl | h
      · exact Nat.le_refl _
      · exact Nat.le_of_succ_le (recIdxs_ge _ h)
    · exact Nat.le_of_succ_le (recIdxs_ge _ h)

/-- Recursive-field positions really hold the block type applied to the
parameters at their depth. -/
theorem recIdxs_getElem {U : Nat} {T : Name} {np : Nat} : ∀ {Bs : List VExpr} {j₀ : Nat},
    ∀ j ∈ recIdxs U T np Bs j₀, Bs[j - j₀]? = some (recApp U T np j)
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

theorem bvarRevRange_liftN_ge : ∀ (m off n k : Nat), k ≤ off →
    (VExpr.bvarRevRange off m).map (VExpr.liftN n · k) = VExpr.bvarRevRange (n + off) m
  | 0, _, _, _, _ => rfl
  | m+1, off, n, k, h => by
    show VExpr.bvar _ :: _ = VExpr.bvar _ :: _
    rw [bvarRevRange_liftN_ge m off n k h]
    congr 2
    show liftVar n (off + m) k = n + off + m
    rw [liftVar_le (by omega)]; omega

theorem bvarRevRange_instL : ∀ (m off : Nat) (ls : List VLevel),
    (VExpr.bvarRevRange off m).map (VExpr.instL ls) = VExpr.bvarRevRange off m
  | 0, _, _ => rfl
  | m+1, off, ls => by
    show _ :: _ = _ :: _
    rw [bvarRevRange_instL m off ls]
    rfl

/-- The key normalization: lifting a parameter spine past `off` binders. -/
theorem recApp'_liftN {U : Nat} {T : Name} {np : Nat} {n k off : Nat} (h : k ≤ off) :
    (recApp' U T np off).liftN n k = recApp' U T np (n + off) := by
  simp only [recApp', VExpr.liftN_appN]
  rw [bvarRevRange_liftN_ge _ _ _ _ h]
  rfl

theorem recApp_liftN {U : Nat} {T : Name} {np : Nat} {n k off : Nat} (h : k ≤ off) :
    (recApp U T np off).liftN n k = recApp U T np (n + off) := by
  simp only [recApp, VExpr.liftN_appN]
  rw [bvarRevRange_liftN_ge _ _ _ _ h]
  rfl

theorem recApp_instL {U : Nat} {T : Name} {np off : Nat} :
    (recApp U T np off).instL (VLevel.params' U 1) = recApp' U T np off := by
  simp only [recApp, recApp', VExpr.instL_appN]
  rw [bvarRevRange_instL]
  simp [VExpr.instL, VLevel.params_map_inst_params']

theorem recApp'_congr {U : Nat} {T : Name} {np : Nat} {off off' : Nat}
    (h : off = off') : recApp' U T np off = recApp' U T np off' := h ▸ rfl

theorem _root_.Lean4Lean.VExpr.bvarRevRange_congr {off off' : Nat} (m : Nat)
    (h : off = off') : VExpr.bvarRevRange off m = VExpr.bvarRevRange off' m := h ▸ rfl

theorem _root_.Lean4Lean.VExpr.bvarRevRange_congr' {m m' : Nat} (off : Nat)
    (h : m = m') : VExpr.bvarRevRange off m = VExpr.bvarRevRange off m' := h ▸ rfl

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

theorem stage2Field_recApp {U T np j B} (h : stage2Field U T np j B)
    (hB : B.hasConst T = true) : B = recApp U T np j := by
  rcases stage2Field_iff.1 h with rfl | h'
  · rfl
  · exact absurd hB (by simp [h'])

end VInductDecl

namespace VExpr

theorem forallN_telN_dropN : ∀ (n : Nat) (e : VExpr),
    forallN (telN n e) (dropN n e) = e
  | 0, _ => rfl
  | n+1, .forallE A rest => congrArg (VExpr.forallE A) (forallN_telN_dropN n rest)
  | _+1, .bvar _ | _+1, .sort _ | _+1, .const _ _ | _+1, .app _ _ | _+1, .lam _ _ => rfl

end VExpr

namespace VEnv

theorem OnTel.mono {env env' : VEnv} {U : Nat} (henv : env ≤ env') :
    ∀ {As Γ}, OnTel env U Γ As → OnTel env' U Γ As
  | [], _, _ => trivial
  | _ :: _, _, ⟨hA, hT⟩ => ⟨hA.mono henv, OnTel.mono henv hT⟩

end VEnv

namespace VInductDecl
open VEnv

theorem fieldsWF_mono {U : Nat} {T : Name} {np : Nat} {env env' : VEnv} {l : VLevel}
    (henv : env ≤ env') : ∀ {Γ j Bs}, fieldsWF U T np env l Γ j Bs →
    fieldsWF U T np env' l Γ j Bs
  | _, _, [], _ => trivial
  | _, _, _ :: _, ⟨hB, hT⟩ =>
    ⟨hB.imp_right fun ⟨u, h, hu⟩ => ⟨u, h.mono henv, hu⟩, fieldsWF_mono henv hT⟩

theorem minorTypes_getElem? {U : Nat} {T : Name} {np : Nat} :
    ∀ (cs : List VConstVal) (i₀ q : Nat),
    (minorTypes U T np cs i₀)[q]? = cs[q]?.map fun c => VExpr.liftN (i₀+q) (minorType U T np c)
  | [], _, q => by simp [minorTypes]
  | c :: cs, i₀, 0 => by simp [minorTypes]
  | c :: cs, i₀, q+1 => by
    simp only [minorTypes, List.getElem?_cons_succ]
    rw [minorTypes_getElem? cs (i₀+1) q, show i₀+1+q = i₀+(q+1) from by omega]

theorem recApp'_levelWF {U : Nat} {T : Name} {np off : Nat} :
    (recApp' U T np off).LevelWF (U+1) :=
  VExpr.LevelWF.appN (f := .const T (VLevel.params' U 1)) VLevel.params'_one_wf
    (bvarRevRange_levelWF _ _)

theorem motiveType_levelWF {U : Nat} {T : Name} {np : Nat} :
    (motiveType U T np).LevelWF (U+1) :=
  ⟨recApp'_levelWF, Nat.succ_pos U⟩

theorem motiveType_liftN {U : Nat} {T : Name} {np n : Nat} :
    (motiveType U T np).liftN n = .forallE (recApp' U T np n) (.sort (.param 0)) := by
  show VExpr.forallE ((recApp' U T np 0).liftN n) _ = _
  rw [recApp'_liftN (Nat.le_refl 0)]
  rfl

theorem liftTelN_levelWF {Uv n : Nat} : ∀ {tel : List VExpr} {k : Nat},
    (∀ A ∈ tel, A.LevelWF Uv) → ∀ A ∈ VExpr.liftTelN n tel k, A.LevelWF Uv
  | [], _, _, _, h => nomatch h
  | _ :: tel, k, hAs, A', h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact (hAs _ (.head _)).liftN
    · exact liftTelN_levelWF (fun A h => hAs _ (.tail _ h)) A' h

theorem minorType_levelWF {U : Nat} {T : Name} {np : Nat} {c : VConstVal} :
    (minorType U T np c).LevelWF (U+1) := by
  simp only [minorType]
  refine VExpr.LevelWF.forallN (liftTelN_levelWF fun B hB => ?_)
    (VExpr.LevelWF.forallN (ihsFrom_levelWF _ _) ⟨trivial, ?_⟩)
  · obtain ⟨B₀, _, rfl⟩ := List.mem_map.1 hB
    exact VExpr.LevelWF.instL VLevel.params'_one_wf
  · refine VExpr.LevelWF.appN (f := .const c.name (VLevel.params' U 1))
      VLevel.params'_one_wf fun e h => ?_
    rcases List.mem_append.1 h with h | h
    · exact bvarRevRange_levelWF _ _ _ h
    · exact bvarRevRange_levelWF _ _ _ h

theorem minorTypes_levelWF {U : Nat} {T : Name} {np : Nat} :
    ∀ (cs : List VConstVal) (i : Nat), ∀ e ∈ minorTypes U T np cs i, e.LevelWF (U+1)
  | _ :: cs, i, e, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact minorType_levelWF.liftN
    · exact minorTypes_levelWF cs (i+1) e h

theorem recType_levelWF {U : Nat} {T : Name} {np : Nat} {ty : VInductiveType} :
    (recType U T np ty).LevelWF (U+1) := by
  refine VExpr.LevelWF.forallN (fun A hA => ?_)
    ⟨motiveType_levelWF, VExpr.LevelWF.forallN (minorTypes_levelWF _ _)
      ⟨recApp'_levelWF, trivial, trivial⟩⟩
  obtain ⟨A₀, _, rfl⟩ := List.mem_map.1 hA
  exact VExpr.LevelWF.instL VLevel.params'_one_wf

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

theorem liftTelN_congr {a a' : Nat} (tel : List VExpr) (k : Nat) (h : a = a') :
    VExpr.liftTelN a tel k = VExpr.liftTelN a' tel k := h ▸ rfl

theorem ctorFieldsR_length {U np : Nat} {c : VConstVal} :
    (ctorFieldsR U np c).length = (ctorFields (VExpr.dropN np c.type)).length :=
  List.length_map ..

theorem ctorFieldsR_getElem? {U np : Nat} {c : VConstVal} {q : Nat} :
    (ctorFieldsR U np c)[q]? =
    (ctorFields (VExpr.dropN np c.type))[q]?.map (VExpr.instL (VLevel.params' U 1)) :=
  List.getElem?_map ..

/-! ## The stage-2 environment invariant -/

/-- Everything the piece-typing lemmas need about an environment that
already contains the block's type constant and constructors. -/
structure Stage2Env (env : VEnv) (U : Nat) (T : Name) (np : Nat) (l : VLevel)
    (ty : VInductiveType) : Prop where
  ord : env.Ordered
  hl : l.WF U
  hsort : VExpr.dropN np ty.type = .sort l
  hlen : (VExpr.telN np ty.type).length = np
  hT : env.constants T = some ⟨U, ty.type⟩
  hcs : ∀ c ∈ ty.ctors, env.constants c.name = some ⟨U, c.type⟩
  htel : ∀ c ∈ ty.ctors, VExpr.telN np c.type = VExpr.telN np ty.type
  hs2 : ∀ c ∈ ty.ctors, stage2Ctor U T np 0 (VExpr.dropN np c.type)
  hparams : OnTel env U [] (VExpr.telN np ty.type)
  hfields : ∀ c ∈ ty.ctors, fieldsWF U T np env l
    (VExpr.telN np ty.type).reverse 0 (ctorFields (VExpr.dropN np c.type))

variable {env : VEnv} {U : Nat} {T : Name} {np : Nat} {l : VLevel} {ty : VInductiveType}
  (S : Stage2Env env U T np l ty)
include S

theorem Stage2Env.mono {env' : VEnv} (henv : env ≤ env') (ord' : env'.Ordered) :
    Stage2Env env' U T np l ty where
  ord := ord'
  hl := S.hl
  hsort := S.hsort
  hlen := S.hlen
  hT := henv.constants S.hT
  hcs := fun c hc => henv.constants (S.hcs c hc)
  htel := S.htel
  hs2 := S.hs2
  hparams := S.hparams.mono henv
  hfields := fun c hc => fieldsWF_mono henv (S.hfields c hc)

/-- The type of the block constant is a type. -/
theorem Stage2Env.tyType_isType : env.IsType U [] ty.type := by
  rw [show ty.type = VExpr.forallN (VExpr.telN np ty.type) (.sort l) from by
    conv => lhs; rw [← VExpr.forallN_telN_dropN np ty.type]
    rw [S.hsort]]
  exact IsType.forallN S.hparams ⟨_, HasType.sort S.hl⟩

/-- The block constant at the declaration universes, in any context. -/
theorem Stage2Env.tconst_decl {Γ} :
    env.HasType U Γ (.const T (VLevel.params U)) ty.type :=
  (HasType.const0 S.hT S.tyType_isType).weak0 S.ord

/-- The type of the block constant, instantiated to the recursor universes. -/
theorem Stage2Env.tyType_instL :
    ty.type.instL (VLevel.params' U 1) =
    VExpr.forallN (paramsTel U np ty) (.sort (l.inst (VLevel.params' U 1))) := by
  conv => lhs; rw [← VExpr.forallN_telN_dropN np ty.type]
  rw [S.hsort, VExpr.instL_forallN]
  rfl

/-- The block constant at the recursor universes, in any context. -/
theorem Stage2Env.tconst {Γ} :
    env.HasType (U+1) Γ (.const T (VLevel.params' U 1)) (ty.type.instL (VLevel.params' U 1)) := by
  have := (S.tconst_decl (Γ := [])).instL (U' := U+1) VLevel.params'_one_wf
  rw [show (VExpr.const T (VLevel.params U)).instL (VLevel.params' U 1) =
    .const T (VLevel.params' U 1) from by
      simp [VExpr.instL, VLevel.params_map_inst_params']] at this
  exact this.weak0 S.ord

/-- The parameter spine applied to the block constant is a sort, below any
`Δ` on top of the parameter telescope (recursor universes). -/
theorem Stage2Env.recApp'_hasType (Δ : List VExpr) :
    env.HasType (U+1) (Δ ++ (paramsTel U np ty).reverse) (recApp' U T np Δ.length)
      (.sort (l.inst (VLevel.params' U 1))) := by
  have hcl : (VExpr.forallN (paramsTel U np ty)
      (.sort (l.inst (VLevel.params' U 1)))).ClosedN 0 := by
    rw [← S.tyType_instL]
    exact (Ordered.closedC (ci := ⟨U, ty.type⟩) S.ord S.hT).instL
  have hf : env.HasType (U+1) (Δ ++ (paramsTel U np ty).reverse ++ [])
      (.const T (VLevel.params' U 1))
      (VExpr.forallN (paramsTel U np ty) (.sort (l.inst (VLevel.params' U 1)))) := by
    rw [← S.tyType_instL]; exact S.tconst
  have := HasType.appN_selfSpine' (Δ := Δ) (Γ := []) hcl hf
  rw [show (paramsTel U np ty).length = np from by
    simp [paramsTel, List.length_map, S.hlen]] at this
  simpa [List.append_nil] using this

/-- The parameter spine at the declaration universes. -/
theorem Stage2Env.recApp_hasType_decl (Δ : List VExpr) :
    env.HasType U (Δ ++ (VExpr.telN np ty.type).reverse) (recApp U T np Δ.length)
      (.sort l) := by
  have hcl : (VExpr.forallN (VExpr.telN np ty.type) (.sort l)).ClosedN 0 := by
    rw [show VExpr.forallN (VExpr.telN np ty.type) (.sort l) = ty.type from by
      conv => rhs; rw [← VExpr.forallN_telN_dropN np ty.type]
      rw [S.hsort]]
    exact Ordered.closedC (ci := ⟨U, ty.type⟩) S.ord S.hT
  have hf : env.HasType U (Δ ++ (VExpr.telN np ty.type).reverse ++ [])
      (.const T (VLevel.params U))
      (VExpr.forallN (VExpr.telN np ty.type) (.sort l)) := by
    rw [show VExpr.forallN (VExpr.telN np ty.type) (.sort l) = ty.type from by
      conv => rhs; rw [← VExpr.forallN_telN_dropN np ty.type]
      rw [S.hsort]]
    exact S.tconst_decl
  have := HasType.appN_selfSpine' (Δ := Δ) (Γ := []) hcl hf
  rw [S.hlen] at this
  simpa [List.append_nil] using this

/-- Field telescopes are well-formed in context, at the declaration
universes (recursive fields via the block constant, which is present). -/
theorem Stage2Env.fieldsWF_onTel_decl :
    ∀ (Bs : List VExpr) (Δd : List VExpr) (j : Nat), Δd.length = j →
    fieldsWF U T np env l (Δd ++ (VExpr.telN np ty.type).reverse) j Bs →
    OnTel env U (Δd ++ (VExpr.telN np ty.type).reverse) Bs
  | [], _, _, _, _ => trivial
  | B :: Bs, Δd, j, hΔ, ⟨hB, hT⟩ => by
    refine ⟨?_, ?_⟩
    · rcases hB with rfl | ⟨u, h, -⟩
      · rw [← hΔ]
        exact ⟨_, S.recApp_hasType_decl Δd⟩
      · exact ⟨u, h⟩
    · exact Stage2Env.fieldsWF_onTel_decl Bs (B :: Δd) (j+1) (by simp [hΔ]) hT

/-- Field telescopes are well-formed in context, at the recursor
universes. -/
theorem Stage2Env.fieldsWF_onTel :
    ∀ (Bs : List VExpr) (Δd : List VExpr) (j : Nat), Δd.length = j →
    fieldsWF U T np env l (Δd ++ (VExpr.telN np ty.type).reverse) j Bs →
    OnTel env (U+1)
      ((Δd ++ (VExpr.telN np ty.type).reverse).map (VExpr.instL (VLevel.params' U 1)))
      (Bs.map (VExpr.instL (VLevel.params' U 1)))
  | [], _, _, _, _ => trivial
  | B :: Bs, Δd, j, hΔ, ⟨hB, hT⟩ => by
    refine ⟨?_, ?_⟩
    · rcases hB with rfl | ⟨u, h, -⟩
      · rw [recApp_instL]
        have := S.recApp'_hasType (Δd.map (VExpr.instL (VLevel.params' U 1)))
        rw [show (Δd.map (VExpr.instL (VLevel.params' U 1))).length = j from by
          simp [hΔ]] at this
        exact ⟨_, by simpa [List.map_append, List.map_reverse, paramsTel] using this⟩
      · exact ⟨_, h.instL VLevel.params'_one_wf⟩
    · have := Stage2Env.fieldsWF_onTel Bs (B :: Δd) (j+1) (by simp [hΔ]) hT
      simpa using this

/-- The constructor's type, split at the parameters. -/
theorem Stage2Env.ctorType_eq {c : VConstVal} (hc : c ∈ ty.ctors) :
    c.type = VExpr.forallN (VExpr.telN np ty.type)
      (VExpr.forallN (ctorFields (VExpr.dropN np c.type))
        (recApp U T np (0 + (ctorFields (VExpr.dropN np c.type)).length))) := by
  conv => lhs; rw [← VExpr.forallN_telN_dropN np c.type, S.htel c hc,
    (stage2Ctor_eq (S.hs2 c hc)).1]

theorem Stage2Env.ctorType_instL {c : VConstVal} (hc : c ∈ ty.ctors) :
    c.type.instL (VLevel.params' U 1) =
    VExpr.forallN (paramsTel U np ty)
      (VExpr.forallN (ctorFieldsR U np c)
        (recApp' U T np (0 + (ctorFields (VExpr.dropN np c.type)).length))) := by
  conv => lhs; rw [S.ctorType_eq hc, VExpr.instL_forallN, VExpr.instL_forallN,
    recApp_instL]
  rfl

/-- A constructor's declared type is well-formed (declaration universes). -/
theorem Stage2Env.ctorType_isType {c : VConstVal} (hc : c ∈ ty.ctors) :
    env.IsType U [] c.type := by
  rw [S.ctorType_eq hc]
  refine IsType.forallN S.hparams ?_
  simp only [List.append_nil]
  refine IsType.forallN
    (S.fieldsWF_onTel_decl _ [] 0 rfl (by simpa using S.hfields c hc)) ?_
  have := S.recApp_hasType_decl
    ((ctorFields (VExpr.dropN np c.type)).reverse)
  rw [List.length_reverse] at this
  exact ⟨_, by simpa using this⟩

/-- The constructor constant at the recursor universes, any context. -/
theorem Stage2Env.cConst {c : VConstVal} (hc : c ∈ ty.ctors) {Γ} :
    env.HasType (U+1) Γ (.const c.name (VLevel.params' U 1))
      (c.type.instL (VLevel.params' U 1)) := by
  have h0 := HasType.const0 (S.hcs c hc) (S.ctorType_isType hc)
  have := h0.instL (U' := U+1) VLevel.params'_one_wf
  rw [show (VExpr.const c.name (VLevel.params U)).instL (VLevel.params' U 1) =
    .const c.name (VLevel.params' U 1) from by
      simp [VExpr.instL, VLevel.params_map_inst_params']] at this
  exact this.weak0 S.ord

theorem Stage2Env.motive_isType :
    env.IsType (U+1) (paramsTel U np ty).reverse (motiveType U T np) := by
  have h1 := S.recApp'_hasType []
  simp only [List.nil_append] at h1
  exact ⟨_, HasType.forallE h1 (HasType.sort (Nat.succ_pos U))⟩

/-- Well-formedness of the induction-hypothesis telescope of a minor
premise, at any suffix of the recursive positions and any depth. -/
theorem Stage2Env.ihs_onTel {c : VConstVal} :
    ∀ (rsSuf : List Nat),
    (∀ j ∈ rsSuf, (ctorFields (VExpr.dropN np c.type))[j]? = some (recApp U T np j)) →
    ∀ (Δ : List VExpr) (p : Nat), Δ.length = p →
    OnTel env (U+1)
      (Δ ++ (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse ++
        (motiveType U T np :: (paramsTel U np ty).reverse))
      (ihsFrom (ctorFieldsR U np c).length rsSuf p)
  | [], _, _, _, _ => trivial
  | j :: rsSuf, hjs, Δ, p, hΔ => by
    have hj := hjs j (.head _)
    have hjlt : j < (ctorFields (VExpr.dropN np c.type)).length := by
      have := (List.getElem?_eq_some_iff.1 hj).1
      simpa using this
    have hM := getElem?_stack3 Δ
      ((VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse)
      (paramsTel U np ty).reverse (motiveType U T np)
      (i := (ctorFieldsR U np c).length + p)
      (by simp only [hΔ, List.length_reverse, VExpr.liftTelN_length]; omega)
    have hmlu := Lookup.of_getElem? hM
    rw [motiveType_liftN] at hmlu
    have hml : (ctorFieldsR U np c).length =
        (ctorFields (VExpr.dropN np c.type)).length := ctorFieldsR_length
    have hF := getElem?_stack_mid Δ
      ((VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse)
      (motiveType U T np :: (paramsTel U np ty).reverse)
      (i := (ctorFieldsR U np c).length - 1 - j + p)
      (by rw [hΔ]; omega)
      (by simp only [hΔ, List.length_reverse, VExpr.liftTelN_length]; omega)
    rw [show (ctorFieldsR U np c).length - 1 - j + p - Δ.length =
        (ctorFieldsR U np c).length - 1 - j from by rw [hΔ]; omega,
      List.getElem?_reverse (by simp only [VExpr.liftTelN_length]; omega),
      VExpr.liftTelN_length,
      show (ctorFieldsR U np c).length - 1 -
        ((ctorFieldsR U np c).length - 1 - j) = j from by omega,
      VExpr.liftTelN_getElem?, ctorFieldsR_getElem?, hj] at hF
    simp only [Option.map_some] at hF
    have hflu := Lookup.of_getElem? hF
    rw [show ((recApp U T np j).instL (VLevel.params' U 1)).liftN 1 (0+j) =
        recApp' U T np (1+j) from by
        rw [recApp_instL, recApp'_liftN (by omega)],
      recApp'_liftN (Nat.zero_le _),
      recApp'_congr (show (ctorFieldsR U np c).length - 1 - j + p + 1 + (1+j) =
        (ctorFieldsR U np c).length + p + 1 from by omega)] at hflu
    refine ⟨⟨_, HasType.app (.bvar hmlu) (.bvar hflu)⟩, ?_⟩
    exact Stage2Env.ihs_onTel rsSuf (fun j h => hjs j (.tail _ h)) (_ :: Δ) (p+1)
      (by simp [hΔ])

/-- The constructor applied to the parameter and field variables, `off`
binders past the fields (which sit `foff` binders past the motive), is the
block type at the parameters. This is the two-step self-application:
first the parameter spine, then the field spine. -/
theorem Stage2Env.ctorAppMin_hasType {c : VConstVal} (hc : c ∈ ty.ctors)
    (Δ : List VExpr) :
    env.HasType (U+1)
      (Δ ++ (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse ++
        (motiveType U T np :: (paramsTel U np ty).reverse))
      (VExpr.appN (.const c.name (VLevel.params' U 1))
        (VExpr.bvarRevRange (Δ.length + (ctorFieldsR U np c).length + 1) np ++
          VExpr.bvarRevRange Δ.length (ctorFieldsR U np c).length))
      (recApp' U T np (Δ.length + (ctorFieldsR U np c).length + 1)) := by
  have hml : (ctorFieldsR U np c).length =
      (ctorFields (VExpr.dropN np c.type)).length := ctorFieldsR_length
  have hml2 : (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).length =
      (ctorFieldsR U np c).length := VExpr.liftTelN_length ..
  have hcl : (c.type.instL (VLevel.params' U 1)).ClosedN 0 :=
    (Ordered.closedC (ci := ⟨U, c.type⟩) S.ord (S.hcs c hc)).instL
  -- step A: consume the parameter telescope
  have hfA : env.HasType (U+1)
      ((Δ ++ (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse ++ [motiveType U T np]) ++
        (paramsTel U np ty).reverse ++ [])
      (.const c.name (VLevel.params' U 1))
      ((VExpr.forallN (paramsTel U np ty)
        (VExpr.forallN (ctorFieldsR U np c)
          (recApp' U T np (0 + (ctorFields (VExpr.dropN np c.type)).length)))).liftN
        ((Δ ++ (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse ++
          [motiveType U T np]).length + (paramsTel U np ty).length)) := by
    rw [← S.ctorType_instL hc, hcl.liftN_eq (Nat.zero_le _)]
    exact S.cConst hc
  have hA := HasType.appN_selfSpine (env := env) (U := U+1) hfA
  -- step B: consume the field telescope
  rw [VExpr.liftN_forallN] at hA
  have hBeq : VExpr.forallN
      (VExpr.liftTelN ((Δ ++ (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse ++
          [motiveType U T np]).length) (ctorFieldsR U np c) 0)
      ((recApp' U T np (0 + (ctorFields (VExpr.dropN np c.type)).length)).liftN
        ((Δ ++ (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse ++
          [motiveType U T np]).length) (0 + (ctorFieldsR U np c).length)) =
      (VExpr.forallN (VExpr.liftTelN 1 (ctorFieldsR U np c) 0)
        (recApp' U T np ((ctorFieldsR U np c).length + 1))).liftN
        (Δ.length + (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).length) := by
    rw [VExpr.liftN_forallN, VExpr.liftTelN_liftTelN,
      liftTelN_congr _ _ (show (1:Nat) + (Δ.length +
        (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).length) =
        (Δ ++ (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse ++
          [motiveType U T np]).length from by
        simp only [List.length_append, List.length_reverse, VExpr.liftTelN_length,
          List.length_singleton]
        omega),
      recApp'_liftN (by omega),
      recApp'_liftN (by omega),
      recApp'_congr (show (Δ ++ (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse ++
          [motiveType U T np]).length + (0 + (ctorFields (VExpr.dropN np c.type)).length) =
        Δ.length + (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).length +
          ((ctorFieldsR U np c).length + 1) from by
        simp only [List.length_append, List.length_reverse, VExpr.liftTelN_length,
          List.length_singleton]
        omega)]
  rw [hBeq] at hA
  have hB := HasType.appN_selfSpine (env := env) (U := U+1)
    (Δ := Δ) (Γ := motiveType U T np :: (paramsTel U np ty).reverse)
    (As := VExpr.liftTelN 1 (ctorFieldsR U np c) 0)
    (B := recApp' U T np ((ctorFieldsR U np c).length + 1))
    (by simpa [List.append_assoc, List.append_nil] using hA)
  rw [recApp'_liftN (Nat.zero_le _),
    show (paramsTel U np ty).length = np from by
      simp [paramsTel, List.length_map, S.hlen],
    VExpr.bvarRevRange_congr np (show Δ.length +
      ((VExpr.liftTelN 1 (ctorFieldsR U np c) 0).length + 1) =
      Δ.length + (ctorFieldsR U np c).length + 1 from by omega),
    VExpr.liftTelN_length,
    recApp'_congr (show Δ.length + ((ctorFieldsR U np c).length + 1) =
      Δ.length + (ctorFieldsR U np c).length + 1 from by omega)] at hB
  rw [show VExpr.appN (.const c.name (VLevel.params' U 1))
      (VExpr.bvarRevRange (Δ.length + (ctorFieldsR U np c).length + 1) np ++
        VExpr.bvarRevRange Δ.length (ctorFieldsR U np c).length) =
    (VExpr.appN (.const c.name (VLevel.params' U 1))
      (VExpr.bvarRevRange (Δ.length + (ctorFieldsR U np c).length + 1) np)).appN
      (VExpr.bvarRevRange Δ.length (ctorFieldsR U np c).length) from
    VExpr.appN_append ..]
  exact hB

/-- The minor premise for a constructor is a type over
`params ++ [motive]`. -/
theorem Stage2Env.minor_isType {c : VConstVal} (hc : c ∈ ty.ctors) :
    env.IsType (U+1) (motiveType U T np :: (paramsTel U np ty).reverse)
      (minorType U T np c) := by
  simp only [minorType]
  refine IsType.forallN ?_ ?_
  · have h0 := S.fieldsWF_onTel _ [] 0 rfl (by simpa using S.hfields c hc)
    have h1 := h0.weakN S.ord (.zero [motiveType U T np])
    simpa [List.map_reverse, paramsTel] using h1
  · refine IsType.forallN (S.ihs_onTel _ (fun j hj => by
      have h0 := recIdxs_getElem _ hj
      rwa [Nat.sub_zero] at h0) [] 0 rfl) ?_
    have hM := getElem?_rstack3 ((ihsFrom (ctorFieldsR U np c).length
        (recIdxs U T np (ctorFields (VExpr.dropN np c.type))) 0).reverse)
      ((VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse)
      (motiveType U T np) (paramsTel U np ty).reverse
      (i := (ctorFieldsR U np c).length +
        (recIdxs U T np (ctorFields (VExpr.dropN np c.type))).length)
      (by simp only [List.length_reverse, ihsFrom_length, VExpr.liftTelN_length]; omega)
    have hmlu := Lookup.of_getElem? hM
    rw [motiveType_liftN] at hmlu
    have hctor := S.ctorAppMin_hasType hc
      ((ihsFrom (ctorFieldsR U np c).length
        (recIdxs U T np (ctorFields (VExpr.dropN np c.type))) 0).reverse)
    rw [show ((ihsFrom (ctorFieldsR U np c).length
        (recIdxs U T np (ctorFields (VExpr.dropN np c.type))) 0).reverse).length =
      (recIdxs U T np (ctorFields (VExpr.dropN np c.type))).length from by
      simp [ihsFrom_length],
      recApp'_congr (show (recIdxs U T np (ctorFields (VExpr.dropN np c.type))).length +
        (ctorFieldsR U np c).length + 1 =
        (ctorFieldsR U np c).length +
        (recIdxs U T np (ctorFields (VExpr.dropN np c.type))).length + 1 from by
        omega)] at hctor
    exact ⟨_, HasType.app (.bvar hmlu) (by simpa [List.append_assoc] using hctor)⟩

/-- The minor premises, in position, are a telescope over
`params ++ [motive]`. -/
theorem Stage2Env.minorTypes_onTel :
    ∀ (cs' : List VConstVal), (∀ c ∈ cs', c ∈ ty.ctors) →
    ∀ (Δ : List VExpr) (i : Nat), Δ.length = i →
    OnTel env (U+1) (Δ ++ (motiveType U T np :: (paramsTel U np ty).reverse))
      (minorTypes U T np cs' i)
  | [], _, _, _, _ => trivial
  | c :: cs', hsub, Δ, i, hΔ =>
    ⟨by
      rw [← hΔ]
      exact (S.minor_isType (hsub c (.head _))).weakN S.ord (.zero Δ),
    Stage2Env.minorTypes_onTel cs' (fun c h => hsub c (.tail _ h)) (_ :: Δ) (i+1)
      (by simp [hΔ])⟩

/-- The generated recursor type is well-formed. -/
theorem Stage2Env.recType_isType : env.IsType (U+1) [] (recType U T np ty) := by
  have hP : OnTel env (U+1) [] (paramsTel U np ty) := by
    have := S.hparams.instL (U' := U+1) VLevel.params'_one_wf
    simpa [paramsTel] using this
  refine IsType.forallN hP ?_
  simp only [List.append_nil]
  refine IsType.forallE S.motive_isType ?_
  refine IsType.forallN
    (by simpa using S.minorTypes_onTel ty.ctors (fun _ h => h) [] 0 rfl) ?_
  have hmaj := S.recApp'_hasType
    ((minorTypes U T np ty.ctors).reverse ++ [motiveType U T np])
  rw [show ((minorTypes U T np ty.ctors).reverse ++ [motiveType U T np]).length =
    ty.ctors.length + 1 from by
    simp [minorTypes_length]] at hmaj
  refine IsType.forallE ⟨_, by simpa [List.append_assoc] using hmaj⟩ ?_
  have hM := getElem?_rstack3 [recApp' U T np (ty.ctors.length + 1)]
    (minorTypes U T np ty.ctors).reverse
    (motiveType U T np) (paramsTel U np ty).reverse
    (i := ty.ctors.length + 1)
    (by simp only [List.length_singleton, List.length_reverse, minorTypes_length]; omega)
  have hmlu := Lookup.of_getElem? (by
    simpa only [List.singleton_append, List.append_assoc] using hM)
  rw [motiveType_liftN] at hmlu
  have harg : env.HasType (U+1)
      (recApp' U T np (ty.ctors.length + 1) ::
        ((minorTypes U T np ty.ctors).reverse ++
          (motiveType U T np :: (paramsTel U np ty).reverse)))
      (.bvar 0) (recApp' U T np (ty.ctors.length + 1 + 1)) := by
    have h0 : (recApp' U T np (ty.ctors.length + 1) ::
        ((minorTypes U T np ty.ctors).reverse ++
          (motiveType U T np :: (paramsTel U np ty).reverse)))[0]? =
        some (recApp' U T np (ty.ctors.length + 1)) := rfl
    have hlu := Lookup.of_getElem? h0
    rw [recApp'_liftN (Nat.zero_le _)] at hlu
    exact .bvar (by
      rwa [recApp'_congr (show (0:Nat) + 1 + (ty.ctors.length + 1) =
        ty.ctors.length + 1 + 1 from by omega)] at hlu)
  exact ⟨_, HasType.app (.bvar hmlu) harg⟩

theorem Stage2Env.recConst_wf : (recConst U T np ty).WF env :=
  S.recType_isType

/-! ## The iota rules -/

/-- The recursor type is closed, by well-formedness. -/
theorem Stage2Env.recType_closedN : (recType U T np ty).ClosedN 0 := by
  obtain ⟨u, h⟩ := S.recType_isType
  exact VExpr.WF.closedN S.ord ⟨_, h⟩ trivial

/-- The recursor constant at its own (identity) universe list. -/
theorem Stage2Env.recConst_hasType
    (hrec : env.constants (.str T "rec") = some (recConst U T np ty)) {Γ} :
    env.HasType (U+1) Γ (.const (.str T "rec") (VLevel.params (U+1)))
      (recType U T np ty) := by
  have := HasType.const (Γ := Γ) hrec VLevel.params_wf VLevel.params_length
  rw [show (recConst U T np ty).uvars = U + 1 from rfl,
    show (recConst U T np ty).type = recType U T np ty from rfl] at this
  rwa [recType_levelWF.instL_id] at this

/-- The recursor spine of an iota rule, applied to one major argument, in
the rule's binder context. -/
theorem Stage2Env.recApp_hasType {c : VConstVal}
    (hrec : env.constants (.str T "rec") = some (recConst U T np ty)) {a : VExpr}
    (ha : env.HasType (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypes U T np ty.ctors).reverse ++
          (motiveType U T np :: (paramsTel U np ty).reverse))) a
      (recApp' U T np ((ctorFieldsR U np c).length + ty.ctors.length + 1))) :
    env.HasType (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypes U T np ty.ctors).reverse ++
          (motiveType U T np :: (paramsTel U np ty).reverse)))
      ((VExpr.appN (.const (.str T "rec") (VLevel.params (U+1)))
        (VExpr.bvarRevRange (ctorFieldsR U np c).length
          (np + ty.ctors.length + 1))).app a)
      (.app (.bvar (ty.ctors.length + (ctorFieldsR U np c).length)) a) := by
  have hf : env.HasType (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        (paramsTel U np ty ++ motiveType U T np :: minorTypes U T np ty.ctors).reverse ++ [])
      (.const (.str T "rec") (VLevel.params (U+1)))
      ((VExpr.forallN
        (paramsTel U np ty ++ motiveType U T np :: minorTypes U T np ty.ctors)
        (.forallE (recApp' U T np (ty.ctors.length + 1))
          (.app (.bvar (ty.ctors.length + 1)) (.bvar 0)))).liftN
        (((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse).length +
          (paramsTel U np ty ++ motiveType U T np :: minorTypes U T np ty.ctors).length)) := by
    rw [show VExpr.forallN
        (paramsTel U np ty ++ motiveType U T np :: minorTypes U T np ty.ctors)
        (.forallE (recApp' U T np (ty.ctors.length + 1))
          (.app (.bvar (ty.ctors.length + 1)) (.bvar 0))) = recType U T np ty from by
      rw [VExpr.forallN_append]; rfl,
      S.recType_closedN.liftN_eq (Nat.zero_le _)]
    exact S.recConst_hasType hrec
  have hspine := HasType.appN_selfSpine (env := env) (U := U+1) hf
  simp only [List.reverse_append, List.reverse_cons, List.append_nil, List.append_assoc,
    List.singleton_append, List.length_reverse, VExpr.liftTelN_length,
    List.length_append, List.length_cons, minorTypes_length] at hspine
  rw [show (paramsTel U np ty).length = np from by
      simp [paramsTel, List.length_map, S.hlen],
    VExpr.bvarRevRange_congr' _ (show np + (ty.ctors.length + 1) =
      np + ty.ctors.length + 1 from by omega),
    show (VExpr.forallE (recApp' U T np (ty.ctors.length + 1))
      (.app (.bvar (ty.ctors.length + 1)) (.bvar 0))).liftN
        (ctorFieldsR U np c).length =
    .forallE (recApp' U T np ((ctorFieldsR U np c).length + ty.ctors.length + 1))
      (.app (.bvar (ty.ctors.length + 1 + (ctorFieldsR U np c).length)) (.bvar 0)) from ?hB]
    at hspine
  case hB =>
    show VExpr.forallE _ _ = _
    congr 1
    · rw [recApp'_liftN (Nat.zero_le _)]
      exact recApp'_congr (by omega)
    · show VExpr.app _ _ = _
      congr 1
      show VExpr.bvar (liftVar _ _ _) = _
      rw [liftVar_le (by omega)]
      congr 1; omega
  have happ := HasType.app hspine ha
  rwa [show (VExpr.app
      (.bvar (ty.ctors.length + 1 + (ctorFieldsR U np c).length)) (.bvar 0)).inst a =
    .app (.bvar (ty.ctors.length + (ctorFieldsR U np c).length)) a from ?hinst] at happ
  case hinst =>
    show VExpr.app _ _ = _
    congr 1
    · show VExpr.instVar _ a 0 = _
      unfold VExpr.instVar
      rw [if_neg (by omega), if_neg (by omega)]
      congr 1; omega
    · exact VExpr.instVar_zero

/-- The constructor-headed major of an iota rule, in the rule's binder
context (parameter spine past the motive, minors and fields). -/
theorem Stage2Env.ctorAppRule_hasType {c : VConstVal} (hc : c ∈ ty.ctors) :
    env.HasType (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypes U T np ty.ctors).reverse ++
          (motiveType U T np :: (paramsTel U np ty).reverse)))
      (VExpr.appN (.const c.name (VLevel.params' U 1))
        (VExpr.bvarRevRange ((ctorFieldsR U np c).length + ty.ctors.length + 1) np ++
          VExpr.bvarRevRange 0 (ctorFieldsR U np c).length))
      (recApp' U T np ((ctorFieldsR U np c).length + ty.ctors.length + 1)) := by
  have hml : (ctorFieldsR U np c).length =
      (ctorFields (VExpr.dropN np c.type)).length := ctorFieldsR_length
  have hml2 : (VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).length =
      (ctorFieldsR U np c).length := VExpr.liftTelN_length ..
  have hcl : (c.type.instL (VLevel.params' U 1)).ClosedN 0 :=
    (Ordered.closedC (ci := ⟨U, c.type⟩) S.ord (S.hcs c hc)).instL
  have hfA : env.HasType (U+1)
      (((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypes U T np ty.ctors).reverse ++ [motiveType U T np])) ++
        (paramsTel U np ty).reverse ++ [])
      (.const c.name (VLevel.params' U 1))
      ((VExpr.forallN (paramsTel U np ty)
        (VExpr.forallN (ctorFieldsR U np c)
          (recApp' U T np (0 + (ctorFields (VExpr.dropN np c.type)).length)))).liftN
        (((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
          ((minorTypes U T np ty.ctors).reverse ++ [motiveType U T np])).length +
          (paramsTel U np ty).length)) := by
    rw [← S.ctorType_instL hc, hcl.liftN_eq (Nat.zero_le _)]
    exact S.cConst hc
  have hA := HasType.appN_selfSpine (env := env) (U := U+1) hfA
  rw [VExpr.liftN_forallN] at hA
  have hBeq : VExpr.forallN
      (VExpr.liftTelN (((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
          ((minorTypes U T np ty.ctors).reverse ++ [motiveType U T np])).length)
        (ctorFieldsR U np c) 0)
      ((recApp' U T np (0 + (ctorFields (VExpr.dropN np c.type)).length)).liftN
        (((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
          ((minorTypes U T np ty.ctors).reverse ++ [motiveType U T np])).length)
        (0 + (ctorFieldsR U np c).length)) =
      (VExpr.forallN (VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0)
        (recApp' U T np ((ctorFieldsR U np c).length + (ty.ctors.length + 1)))).liftN
        (ctorFieldsR U np c).length := by
    rw [VExpr.liftN_forallN, VExpr.liftTelN_liftTelN,
      liftTelN_congr _ _ (show ty.ctors.length + 1 + (ctorFieldsR U np c).length =
        ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
          ((minorTypes U T np ty.ctors).reverse ++ [motiveType U T np])).length from by
        simp only [List.length_append, List.length_reverse, VExpr.liftTelN_length,
          List.length_singleton, minorTypes_length]
        omega),
      recApp'_liftN (by omega),
      recApp'_liftN (by omega),
      recApp'_congr (show ((VExpr.liftTelN (ty.ctors.length + 1)
          (ctorFieldsR U np c) 0).reverse ++
          ((minorTypes U T np ty.ctors).reverse ++ [motiveType U T np])).length +
          (0 + (ctorFields (VExpr.dropN np c.type)).length) =
        (ctorFieldsR U np c).length +
          ((ctorFieldsR U np c).length + (ty.ctors.length + 1)) from by
        simp only [List.length_append, List.length_reverse, VExpr.liftTelN_length,
          List.length_singleton, minorTypes_length]
        omega)]
  rw [hBeq] at hA
  have hB := HasType.appN_selfSpine (env := env) (U := U+1)
    (Δ := []) (Γ := (minorTypes U T np ty.ctors).reverse ++
      (motiveType U T np :: (paramsTel U np ty).reverse))
    (As := VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0)
    (B := recApp' U T np ((ctorFieldsR U np c).length + (ty.ctors.length + 1)))
    (by simpa [List.append_assoc, List.append_nil, VExpr.liftTelN_length] using hA)
  rw [recApp'_liftN (Nat.zero_le _)] at hB
  have hB2 : env.HasType (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypes U T np ty.ctors).reverse ++
          (motiveType U T np :: (paramsTel U np ty).reverse)))
      ((VExpr.appN (.const c.name (VLevel.params' U 1))
        (VExpr.bvarRevRange ((ctorFieldsR U np c).length + ty.ctors.length + 1) np)).appN
        (VExpr.bvarRevRange 0 (ctorFieldsR U np c).length))
      (recApp' U T np ((ctorFieldsR U np c).length + ty.ctors.length + 1)) := by
    have := hB
    rw [show (paramsTel U np ty).length = np from by
        simp [paramsTel, List.length_map, S.hlen],
      VExpr.bvarRevRange_congr np (show (ctorFieldsR U np c).length +
        ((minorTypes U T np ty.ctors).length + 1) =
        (ctorFieldsR U np c).length + ty.ctors.length + 1 from by
        simp only [minorTypes_length]; omega),
      recApp'_congr (show List.length ([] : List VExpr) +
          ((ctorFieldsR U np c).length + (ty.ctors.length + 1)) =
        (ctorFieldsR U np c).length + ty.ctors.length + 1 from by
        simp only [List.length_nil]; omega)] at this
    simpa [VExpr.liftTelN_length] using this
  rw [show VExpr.appN (.const c.name (VLevel.params' U 1))
      (VExpr.bvarRevRange ((ctorFieldsR U np c).length + ty.ctors.length + 1) np ++
        VExpr.bvarRevRange 0 (ctorFieldsR U np c).length) =
    (VExpr.appN (.const c.name (VLevel.params' U 1))
      (VExpr.bvarRevRange ((ctorFieldsR U np c).length + ty.ctors.length + 1) np)).appN
      (VExpr.bvarRevRange 0 (ctorFieldsR U np c).length) from
    VExpr.appN_append ..]
  exact hB2

theorem Stage2Env.ruleBinders_onTel {c : VConstVal} (hc : c ∈ ty.ctors) :
    OnTel env (U+1) []
      (paramsTel U np ty ++ motiveType U T np :: minorTypes U T np ty.ctors ++
        VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0) := by
  have hP : OnTel env (U+1) [] (paramsTel U np ty) := by
    have := S.hparams.instL (U' := U+1) VLevel.params'_one_wf
    simpa [paramsTel] using this
  have hF : OnTel env (U+1)
      ((minorTypes U T np ty.ctors).reverse ++
        (motiveType U T np :: (paramsTel U np ty).reverse))
      (VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0) := by
    have h0 := S.fieldsWF_onTel _ [] 0 rfl (by simpa using S.hfields c hc)
    have h1 := h0.weakN S.ord
      (.zero ((minorTypes U T np ty.ctors).reverse ++ [motiveType U T np]))
    rw [liftTelN_congr _ _ (show ((minorTypes U T np ty.ctors).reverse ++
        [motiveType U T np]).length = ty.ctors.length + 1 from by
      simp only [List.length_append, List.length_reverse, minorTypes_length,
        List.length_singleton])] at h1
    simpa [List.map_reverse, paramsTel, List.append_assoc] using h1
  refine OnTel.append (OnTel.append hP ⟨?_, ?_⟩) ?_
  · simpa only [List.append_nil] using S.motive_isType
  · have := S.minorTypes_onTel ty.ctors (fun _ h => h) [] 0 rfl
    simpa only [List.nil_append, List.append_nil] using this
  · simpa only [List.append_nil, List.append_assoc, List.reverse_append,
      List.reverse_cons, List.singleton_append] using hF

theorem Stage2Env.ruleType_isType {i : Nat} {c : VConstVal}
    (hci : ty.ctors[i]? = some c) :
    env.IsType (U+1) [] ((rule U T np ty i c).type) := by
  have hc := List.mem_of_getElem? hci
  show env.IsType (U+1) [] (VExpr.forallN
    (paramsTel U np ty ++ motiveType U T np :: minorTypes U T np ty.ctors ++
      VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0)
    (.app (.bvar (ty.ctors.length + (ctorFieldsR U np c).length))
      (VExpr.appN (.const c.name (VLevel.params' U 1))
        (VExpr.bvarRevRange ((ctorFieldsR U np c).length + ty.ctors.length + 1) np ++
          VExpr.bvarRevRange 0 (ctorFieldsR U np c).length))))
  refine IsType.forallN (S.ruleBinders_onTel hc) ?_
  simp only [List.reverse_append, List.reverse_cons, List.append_nil, List.append_assoc,
    List.singleton_append]
  have hM := getElem?_rstack3
    ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse)
    ((minorTypes U T np ty.ctors).reverse)
    (motiveType U T np) (paramsTel U np ty).reverse
    (i := ty.ctors.length + (ctorFieldsR U np c).length)
    (by simp only [List.length_reverse, VExpr.liftTelN_length, minorTypes_length]; omega)
  have hmlu := Lookup.of_getElem? hM
  rw [motiveType_liftN] at hmlu
  have hctor := S.ctorAppRule_hasType hc
  rw [recApp'_congr (show (ctorFieldsR U np c).length + ty.ctors.length + 1 =
    ty.ctors.length + (ctorFieldsR U np c).length + 1 from by omega)] at hctor
  exact ⟨_, HasType.app (.bvar hmlu) hctor⟩

/-- The right-hand side of an iota rule: the constructor's minor premise
applied to the fields and the recursive calls, in the rule's binder
context. -/
theorem Stage2Env.minorApp_hasType {i : Nat} {c : VConstVal}
    (hci : ty.ctors[i]? = some c)
    (hrec : env.constants (.str T "rec") = some (recConst U T np ty)) :
    env.HasType (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypes U T np ty.ctors).reverse ++
          (motiveType U T np :: (paramsTel U np ty).reverse)))
      (VExpr.appN (.bvar (ty.ctors.length - 1 - i + (ctorFieldsR U np c).length))
        (VExpr.bvarRevRange 0 (ctorFieldsR U np c).length ++
          (recIdxs U T np (ctorFields (VExpr.dropN np c.type))).map fun j =>
            (VExpr.appN (.const (.str T "rec") (VLevel.params (U+1)))
              (VExpr.bvarRevRange (ctorFieldsR U np c).length
                (np + ty.ctors.length + 1))).app
              (.bvar ((ctorFieldsR U np c).length - 1 - j))))
      (.app (.bvar (ty.ctors.length + (ctorFieldsR U np c).length))
        (VExpr.appN (.const c.name (VLevel.params' U 1))
          (VExpr.bvarRevRange ((ctorFieldsR U np c).length + ty.ctors.length + 1) np ++
            VExpr.bvarRevRange 0 (ctorFieldsR U np c).length))) := by
  obtain ⟨hik, -⟩ := List.getElem?_eq_some_iff.1 hci
  have hc := List.mem_of_getElem? hci
  have hml : (ctorFieldsR U np c).length =
      (ctorFields (VExpr.dropN np c.type)).length := ctorFieldsR_length
  have hml2 : (VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).length =
      (ctorFieldsR U np c).length := VExpr.liftTelN_length ..
  rw [VExpr.appN_append]
  have hlu0 : ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
      ((minorTypes U T np ty.ctors).reverse ++
        (motiveType U T np :: (paramsTel U np ty).reverse)))[
      ty.ctors.length - 1 - i + (ctorFieldsR U np c).length]? =
      some (VExpr.liftN i (minorType U T np c)) := by
    rw [getElem?_rstack_mid _ _ _
        (by simp only [List.length_reverse, VExpr.liftTelN_length]; omega)
        (by simp only [List.length_reverse, VExpr.liftTelN_length, minorTypes_length]
            omega),
      show ty.ctors.length - 1 - i + (ctorFieldsR U np c).length -
        ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse).length =
        ty.ctors.length - 1 - i from by
          simp only [List.length_reverse, VExpr.liftTelN_length]; omega,
      List.getElem?_reverse (by simp only [minorTypes_length]; omega),
      show (minorTypes U T np ty.ctors).length - 1 - (ty.ctors.length - 1 - i) = i from by
        simp only [minorTypes_length]; omega,
      minorTypes_getElem?, hci, Nat.zero_add]
    rfl
  have hlu := Lookup.of_getElem? hlu0
  rw [VExpr.liftN_liftN,
    show i + (ty.ctors.length - 1 - i + (ctorFieldsR U np c).length + 1) =
      (ctorFieldsR U np c).length + ty.ctors.length from by omega] at hlu
  -- phase 1: consume the field binders by self-application
  have hminorEq : (minorType U T np c).liftN
      ((ctorFieldsR U np c).length + ty.ctors.length) =
      (VExpr.forallN (VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0)
        ((VExpr.forallN (ihsFrom (ctorFieldsR U np c).length
          (recIdxs U T np (ctorFields (VExpr.dropN np c.type))) 0)
          (.app (.bvar ((ctorFieldsR U np c).length +
              (recIdxs U T np (ctorFields (VExpr.dropN np c.type))).length))
            (VExpr.appN (.const c.name (VLevel.params' U 1))
              (VExpr.bvarRevRange
                ((recIdxs U T np (ctorFields (VExpr.dropN np c.type))).length +
                  (ctorFieldsR U np c).length + 1) np ++
                VExpr.bvarRevRange
                  (recIdxs U T np (ctorFields (VExpr.dropN np c.type))).length
                  (ctorFieldsR U np c).length)))).liftN
          ty.ctors.length (ctorFieldsR U np c).length)).liftN
        (ctorFieldsR U np c).length := by
    simp only [minorType]
    conv => lhs; rw [VExpr.liftN_forallN, VExpr.liftTelN_liftTelN,
      liftTelN_congr _ _ (show (1:Nat) +
        ((ctorFieldsR U np c).length + ty.ctors.length) =
        ty.ctors.length + 1 + (ctorFieldsR U np c).length from by omega),
      show (0:Nat) + (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).length =
        (ctorFieldsR U np c).length from by simp [VExpr.liftTelN_length]]
    conv => rhs; rw [VExpr.liftN_forallN, VExpr.liftTelN_liftTelN,
      show (0:Nat) + (VExpr.liftTelN (ty.ctors.length + 1)
        (ctorFieldsR U np c) 0).length =
        (ctorFieldsR U np c).length from by simp [VExpr.liftTelN_length],
      VExpr.liftN'_liftN_hi,
      Nat.add_comm ty.ctors.length (ctorFieldsR U np c).length]
  have hspine1 := HasType.appN_selfSpine (env := env) (U := U + 1)
    (As := VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0)
    (B := (VExpr.forallN (ihsFrom (ctorFieldsR U np c).length
        (recIdxs U T np (ctorFields (VExpr.dropN np c.type))) 0)
        (.app (.bvar ((ctorFieldsR U np c).length +
            (recIdxs U T np (ctorFields (VExpr.dropN np c.type))).length))
          (VExpr.appN (.const c.name (VLevel.params' U 1))
            (VExpr.bvarRevRange
              ((recIdxs U T np (ctorFields (VExpr.dropN np c.type))).length +
                (ctorFieldsR U np c).length + 1) np ++
              VExpr.bvarRevRange
                (recIdxs U T np (ctorFields (VExpr.dropN np c.type))).length
                (ctorFieldsR U np c).length)))).liftN
        ty.ctors.length (ctorFieldsR U np c).length)
    (Δ := []) (Γ := (minorTypes U T np ty.ctors).reverse ++
      (motiveType U T np :: (paramsTel U np ty).reverse))
    (f := .bvar (ty.ctors.length - 1 - i + (ctorFieldsR U np c).length)) ?hf1
  case hf1 =>
    have hb := VEnv.HasType.bvar (env := env) (U := U+1) hlu
    rw [hminorEq] at hb
    simpa [VExpr.liftTelN_length] using hb
  simp only [List.length_nil, VExpr.liftTelN_length, VExpr.liftN_zero] at hspine1
  rw [ihsFrom_liftN' (ctorFieldsR U np c).length ty.ctors.length
    (recIdxs U T np (ctorFields (VExpr.dropN np c.type)))
    (fun j hj => by have := recIdxs_lt _ hj; omega) 0
    (.app (.bvar ((ctorFieldsR U np c).length +
        (recIdxs U T np (ctorFields (VExpr.dropN np c.type))).length))
      (VExpr.appN (.const c.name (VLevel.params' U 1))
        (VExpr.bvarRevRange
          ((recIdxs U T np (ctorFields (VExpr.dropN np c.type))).length +
            (ctorFieldsR U np c).length + 1) np ++
          VExpr.bvarRevRange
            (recIdxs U T np (ctorFields (VExpr.dropN np c.type))).length
            (ctorFieldsR U np c).length)))
    (cut := (ctorFieldsR U np c).length) rfl] at hspine1
  rw [show (VExpr.app (.bvar ((ctorFieldsR U np c).length +
        (recIdxs U T np (ctorFields (VExpr.dropN np c.type))).length))
      (VExpr.appN (.const c.name (VLevel.params' U 1))
        (VExpr.bvarRevRange
          ((recIdxs U T np (ctorFields (VExpr.dropN np c.type))).length +
            (ctorFieldsR U np c).length + 1) np ++
          VExpr.bvarRevRange
            (recIdxs U T np (ctorFields (VExpr.dropN np c.type))).length
            (ctorFieldsR U np c).length))).liftN ty.ctors.length
      ((ctorFieldsR U np c).length + 0 +
        (recIdxs U T np (ctorFields (VExpr.dropN np c.type))).length) =
    (VExpr.app (.bvar (ty.ctors.length + (ctorFieldsR U np c).length))
      (VExpr.appN (.const c.name (VLevel.params' U 1))
        (VExpr.bvarRevRange ((ctorFieldsR U np c).length + ty.ctors.length + 1) np ++
          VExpr.bvarRevRange 0 (ctorFieldsR U np c).length))).liftN
      (recIdxs U T np (ctorFields (VExpr.dropN np c.type))).length from ?hres]
    at hspine1
  case hres =>
    show VExpr.app _ _ = VExpr.app _ _
    congr 1
    · show VExpr.bvar (liftVar _ _ _) = VExpr.bvar (liftVar _ _ _)
      rw [liftVar_le (by omega), liftVar_le (Nat.zero_le _)]
      congr 1; omega
    · rw [VExpr.liftN_appN, VExpr.liftN_appN, List.map_append, List.map_append,
        bvarRevRange_liftN_ge _ _ _ _ (by omega),
        VExpr.bvarRevRange_liftN_high _ _ _ _ (by omega),
        bvarRevRange_liftN_ge _ _ _ _ (Nat.zero_le _),
        bvarRevRange_liftN_ge _ _ _ _ (Nat.zero_le _),
        VExpr.bvarRevRange_congr _ (show ty.ctors.length +
          ((recIdxs U T np (ctorFields (VExpr.dropN np c.type))).length +
            (ctorFieldsR U np c).length + 1) =
          (recIdxs U T np (ctorFields (VExpr.dropN np c.type))).length +
            ((ctorFieldsR U np c).length + ty.ctors.length + 1) from by omega),
        VExpr.bvarRevRange_congr _ (show
          (recIdxs U T np (ctorFields (VExpr.dropN np c.type))).length =
          (recIdxs U T np (ctorFields (VExpr.dropN np c.type))).length + 0 from by
            omega)]
      rfl
  -- phase 2: consume the induction hypotheses
  refine hasType_appN_ihs (fun j hj => ?_) hspine1
  have hjm := recIdxs_lt _ hj
  have hF0 : ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
      ((minorTypes U T np ty.ctors).reverse ++
        (motiveType U T np :: (paramsTel U np ty).reverse)))[
      (ctorFieldsR U np c).length - 1 - j]? =
      some (VExpr.liftN (ty.ctors.length + 1)
        ((recApp U T np j).instL (VLevel.params' U 1)) (0 + j)) := by
    rw [List.getElem?_append_left
        (by simp only [List.length_reverse, VExpr.liftTelN_length]; omega),
      List.getElem?_reverse (by simp only [VExpr.liftTelN_length]; omega),
      VExpr.liftTelN_length,
      show (ctorFieldsR U np c).length - 1 -
        ((ctorFieldsR U np c).length - 1 - j) = j from by omega,
      VExpr.liftTelN_getElem?, ctorFieldsR_getElem?]
    have h0 := recIdxs_getElem _ hj
    rw [Nat.sub_zero] at h0
    rw [h0]
    simp only [Option.map_some]
  have hflu := Lookup.of_getElem? hF0
  rw [show VExpr.liftN (ty.ctors.length + 1)
      ((recApp U T np j).instL (VLevel.params' U 1)) (0 + j) =
      recApp' U T np (ty.ctors.length + 1 + j) from by
      rw [recApp_instL, recApp'_liftN (by omega)],
    recApp'_liftN (Nat.zero_le _),
    recApp'_congr (show (ctorFieldsR U np c).length - 1 - j + 1 +
        (ty.ctors.length + 1 + j) =
      (ctorFieldsR U np c).length + ty.ctors.length + 1 from by omega)] at hflu
  exact S.recApp_hasType hrec (.bvar hflu)

/-- Well-formedness of the iota rule for the `i`-th constructor. -/
theorem Stage2Env.rule_WF {i : Nat} {c : VConstVal}
    (hci : ty.ctors[i]? = some c)
    (hrec : env.constants (.str T "rec") = some (recConst U T np ty)) :
    (rule U T np ty i c).WF env := by
  have hc := List.mem_of_getElem? hci
  refine ⟨?_, ?_⟩
  · show env.HasType (U+1) [] (VExpr.lamN
      (paramsTel U np ty ++ motiveType U T np :: minorTypes U T np ty.ctors ++
        VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0) _)
      (VExpr.forallN _ _)
    refine HasType.lamN (S.ruleBinders_onTel hc) ?_
    simp only [List.reverse_append, List.reverse_cons, List.append_nil,
      List.append_assoc, List.singleton_append]
    exact S.recApp_hasType hrec (S.ctorAppRule_hasType hc)
  · show env.HasType (U+1) [] (VExpr.lamN
      (paramsTel U np ty ++ motiveType U T np :: minorTypes U T np ty.ctors ++
        VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0) _)
      (VExpr.forallN _ _)
    refine HasType.lamN (S.ruleBinders_onTel hc) ?_
    simp only [List.reverse_append, List.reverse_cons, List.append_nil,
      List.append_assoc, List.singleton_append]
    exact S.minorApp_hasType hci hrec

/-- `ctorType_eq` from the per-constructor facts directly (for use before
the constructor is in the environment). -/
theorem Stage2Env.ctorType_eq' {c : VConstVal}
    (htelc : VExpr.telN np c.type = VExpr.telN np ty.type)
    (hs2c : stage2Ctor U T np 0 (VExpr.dropN np c.type)) :
    c.type = VExpr.forallN (VExpr.telN np ty.type)
      (VExpr.forallN (ctorFields (VExpr.dropN np c.type))
        (recApp U T np (0 + (ctorFields (VExpr.dropN np c.type)).length))) := by
  conv => lhs; rw [← VExpr.forallN_telN_dropN np c.type, htelc,
    (stage2Ctor_eq hs2c).1]

/-- `ctorType_isType` from the per-constructor facts directly. -/
theorem Stage2Env.ctorType_isType' {c : VConstVal}
    (htelc : VExpr.telN np c.type = VExpr.telN np ty.type)
    (hs2c : stage2Ctor U T np 0 (VExpr.dropN np c.type))
    (hfc : fieldsWF U T np env l (VExpr.telN np ty.type).reverse 0
      (ctorFields (VExpr.dropN np c.type))) :
    env.IsType U [] c.type := by
  rw [S.ctorType_eq' htelc hs2c]
  refine IsType.forallN S.hparams ?_
  simp only [List.append_nil]
  refine IsType.forallN
    (S.fieldsWF_onTel_decl _ [] 0 rfl (by simpa using hfc)) ?_
  have := S.recApp_hasType_decl
    ((ctorFields (VExpr.dropN np c.type)).reverse)
  rw [List.length_reverse] at this
  exact ⟨_, by simpa using this⟩

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

theorem rulesFold_WF : ∀ (dfs : List VDefEq) {env₃ : VEnv},
    env₃.Ordered → (∀ df ∈ dfs, df.WF env₃) →
    (dfs.foldl VEnv.addDefEq env₃).Ordered
  | [], _, ord, _ => ord
  | df :: dfs, env₃, ord, hdfs => by
    rw [List.foldl_cons]
    exact rulesFold_WF dfs (.defeq ord (hdfs df (.head _)))
      (fun df' hdf' => (hdfs df' (.tail _ hdf')).mono VEnv.addDefEq_le)

/-- Adding the constructors of a stage-2 block preserves order and records
their lookups. -/
theorem ctorFold_WF {U : Nat} {T : Name} {np : Nat} {l : VLevel} {ty : VInductiveType}
    (hsort : VExpr.dropN np ty.type = .sort l)
    (hlen : (VExpr.telN np ty.type).length = np) (hl : l.WF U) :
    ∀ (cs' : List VConstVal) {env₀ env₁ : VEnv},
    env₀.Ordered → env₀.constants T = some ⟨U, ty.type⟩ →
    VEnv.OnTel env₀ U [] (VExpr.telN np ty.type) →
    (∀ c ∈ cs', c.uvars = U ∧ VExpr.telN np c.type = VExpr.telN np ty.type ∧
      stage2Ctor U T np 0 (VExpr.dropN np c.type) ∧
      fieldsWF U T np env₀ l (VExpr.telN np ty.type).reverse 0
        (ctorFields (VExpr.dropN np c.type))) →
    List.foldlM (fun env (c : VConstVal) => env.addConst c.name c.toVConstant) env₀ cs' =
      some env₁ →
    env₁.Ordered ∧ env₀ ≤ env₁ ∧
      ∀ c ∈ cs', env₁.constants c.name = some ⟨U, c.type⟩
  | [], env₀, env₁, ord, _, _, _, hfold => by
    cases hfold
    exact ⟨ord, .rfl, nofun⟩
  | c :: cs', env₀, env₁, ord, hT, hpar, hcs, hfold => by
    rw [List.foldlM_cons] at hfold
    obtain ⟨env₀', hadd, hrest⟩ := Option.bind_eq_some_iff.1 hfold
    obtain ⟨hcU, htelc, hs2c, hfc⟩ := hcs c (.head _)
    have S₀ : Stage2Env env₀ U T np l ⟨⟨⟨ty.uvars, ty.type⟩, ty.name⟩, []⟩ :=
      ⟨ord, hl, hsort, hlen, hT, nofun, nofun, nofun, hpar, nofun⟩
    have hwfc : c.toVConstant.WF env₀ := by
      show env₀.IsType c.toVConstant.uvars [] c.toVConstant.type
      rw [show c.toVConstant.uvars = c.uvars from rfl, hcU]
      exact S₀.ctorType_isType' htelc hs2c hfc
    have ord' : env₀'.Ordered := .const ord hwfc hadd
    have hle' := VEnv.addConst_le hadd
    obtain ⟨ord₁, hle₁, hlook⟩ := ctorFold_WF hsort hlen hl cs' ord'
      (hle'.constants hT) (hpar.mono hle')
      (fun c' hc' => by
        obtain ⟨h1, h2, h3, h4⟩ := hcs c' (.tail _ hc')
        exact ⟨h1, h2, h3, fieldsWF_mono hle' h4⟩)
      hrest
    refine ⟨ord₁, hle'.trans hle₁, fun c' hc' => ?_⟩
    rcases List.mem_cons.1 hc' with rfl | hc'
    · have hself := VEnv.addConst_self hadd
      rw [show c'.toVConstant = ⟨U, c'.type⟩ from by rw [← hcU]] at hself
      exact hle₁.constants hself
    · exact hlook c' hc'

end VInductDecl

namespace VEnv
open VInductDecl

theorem addInduct_WF (henv : Ordered env) (hdecl : decl.WF env)
    (henv' : addInduct env decl = some env') : Ordered env' := by
  obtain ⟨hs2, hwf⟩ := hdecl
  obtain ⟨U, np, tys⟩ := decl
  unfold addInduct at henv'
  obtain ⟨-, -, henv'⟩ := Option.bind_eq_some_iff.1 henv'
  match tys, hs2, hwf, henv' with
  | [ty], hs2, hwf, henv' => ?_
  obtain ⟨env₁, hadd1, henv'⟩ := Option.bind_eq_some_iff.1 henv'
  obtain ⟨env₂, hfold, henv'⟩ := Option.bind_eq_some_iff.1 henv'
  obtain ⟨env₃, hadd3, henv'⟩ := Option.bind_eq_some_iff.1 henv'
  cases henv'
  obtain ⟨htyU, hlen, ⟨l, hsort, hlWF, -⟩, hctors⟩ := stage2_anatomy hs2
  obtain ⟨hparams₀, hfields₀⟩ := hwf ty (.head _)
  have hsl : sortLevel np ty = l := by simp only [sortLevel, hsort]
  rw [hsl] at hfields₀
  have hwfT : ty.toVConstant.WF env := by
    show env.IsType ty.toVConstant.uvars [] ty.toVConstant.type
    rw [show ty.toVConstant.uvars = ty.uvars from rfl, htyU,
      show ty.toVConstant.type = ty.type from rfl,
      show ty.type = VExpr.forallN (VExpr.telN np ty.type) (.sort l) from by
        conv => lhs; rw [← VExpr.forallN_telN_dropN np ty.type]
        rw [hsort]]
    exact IsType.forallN hparams₀ ⟨_, HasType.sort hlWF⟩
  have ord₁ : env₁.Ordered := .const henv hwfT hadd1
  have hT₁ : env₁.constants ty.name = some ⟨U, ty.type⟩ := by
    have := addConst_self hadd1
    rwa [show ty.toVConstant = ⟨U, ty.type⟩ from by
      show (⟨ty.uvars, ty.type⟩ : VConstant) = _
      rw [htyU]] at this
  obtain ⟨ord₂, hle₂, hlook₂⟩ := ctorFold_WF hsort hlen hlWF ty.ctors ord₁ hT₁
    (hparams₀.mono (addConst_le hadd1))
    (fun c hc => ⟨(hctors c hc).1, (hctors c hc).2.1, (hctors c hc).2.2,
      fieldsWF_mono (addConst_le hadd1) (hfields₀ c hc)⟩)
    hfold
  have S₂ : Stage2Env env₂ U ty.name np l ty :=
    ⟨ord₂, hlWF, hsort, hlen, hle₂.constants hT₁, hlook₂,
      fun c hc => (hctors c hc).2.1, fun c hc => (hctors c hc).2.2,
      hparams₀.mono ((addConst_le hadd1).trans hle₂),
      fun c hc => fieldsWF_mono ((addConst_le hadd1).trans hle₂) (hfields₀ c hc)⟩
  have ord₃ : env₃.Ordered := .const ord₂ S₂.recConst_wf hadd3
  have S₃ : Stage2Env env₃ U ty.name np l ty :=
    S₂.mono (addConst_le hadd3) ord₃
  have hrec₃ : env₃.constants (.str ty.name "rec") = some (recConst U ty.name np ty) :=
    addConst_self hadd3
  refine rulesFold_WF _ ord₃ fun df hdf => ?_
  obtain ⟨⟨c, i⟩, hmem, rfl⟩ := List.mem_map.1 hdf
  obtain ⟨-, hci⟩ := List.mem_zipIdx_getElem? hmem
  rw [Nat.sub_zero] at hci
  exact S₃.rule_WF hci hrec₃

end VEnv
