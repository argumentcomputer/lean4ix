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

theorem liftTelN_take (n : Nat) : ∀ (tel : List VExpr) (k q : Nat),
    (liftTelN n tel k).take q = liftTelN n (tel.take q) k
  | [], _, q => by simp [liftTelN]
  | A :: tel, k, 0 => rfl
  | A :: tel, k, q+1 => by
    show A.liftN n k :: (liftTelN n tel (k+1)).take q = _
    rw [liftTelN_take n tel (k+1) q]
    rfl

/-- Merging a telescope lift over another when the outer cutoff sits right
past the inner lift. -/
theorem liftTelN_liftTelN_hi (a b : Nat) : ∀ (tel : List VExpr) (k : Nat),
    liftTelN b (liftTelN a tel k) (k + a) = liftTelN (a + b) tel k
  | [], _ => rfl
  | A :: tel, k => by
    show (A.liftN a k).liftN b (k+a) :: _ = _
    rw [liftN'_liftN' (Nat.le_add_right _ _) (by omega),
      show k + a + 1 = (k+1) + a from by omega,
      liftTelN_liftTelN_hi a b tel (k+1)]
    rfl

/-- `liftTelN_liftTelN_hi` with the outer cutoff generalized, for
syntactic rewriting. -/
theorem liftTelN_liftTelN_hi' (a b : Nat) (tel : List VExpr) (k : Nat) {cut : Nat}
    (hcut : cut = k + a) :
    liftTelN b (liftTelN a tel k) cut = liftTelN (a + b) tel k := by
  rw [hcut]; exact liftTelN_liftTelN_hi a b tel k

/-- Merge telescope lifts when the outer cutoff lies anywhere inside the
range opened by the inner lift. This is the shape needed when new ambient
binders are inserted below a recursive argument's own Pi telescope. -/
theorem liftTelN_liftTelN_mid (a b : Nat) : ∀ (tel : List VExpr) (k cut : Nat),
    k ≤ cut → cut ≤ a + k →
    liftTelN b (liftTelN a tel k) cut = liftTelN (a+b) tel k
  | [], _, _, _, _ => rfl
  | A :: tel, k, cut, h₁, h₂ => by
    show (A.liftN a k).liftN b cut :: _ = _
    rw [VExpr.liftN'_liftN' h₁ h₂,
      liftTelN_liftTelN_mid a b tel (k+1) (cut+1)
        (Nat.succ_le_succ h₁) (by omega)]
    rfl

theorem liftTelN_instL (ls : List VLevel) (n : Nat) : ∀ (tel : List VExpr) (k : Nat),
    (liftTelN n tel k).map (instL ls) = liftTelN n (tel.map (instL ls)) k
  | [], _ => rfl
  | A :: tel, k => by
    show (A.liftN n k).instL ls :: _ = (A.instL ls).liftN n k :: _
    rw [instL_liftN, liftTelN_instL ls n tel (k+1)]

/-- Pulling a lift out of the middle of a two-step lift: the outer lift at
the seam between the two inner ones lands on the variables the innermost
lift moved. -/
theorem liftN_liftN_mid : ∀ (e : VExpr) {j c : Nat} (k d : Nat), c ≤ j →
    ((e.liftN 1 j).liftN d c).liftN k (j + d) = (e.liftN (k+1) j).liftN d c := by
  intro e
  induction e with intro j c k d hc
  | bvar i =>
    show VExpr.bvar (liftVar k (liftVar d (liftVar 1 i j) c) (j+d)) =
      .bvar (liftVar d (liftVar (k+1) i j) c)
    congr 1
    rcases Nat.lt_or_ge i j with h1 | h1
    · rw [liftVar_lt h1, liftVar_lt (show i < j from h1)]
      rcases Nat.lt_or_ge i c with h2 | h2
      · rw [liftVar_lt h2, liftVar_lt (show i < j+d from by omega)]
      · rw [liftVar_le h2, liftVar_lt (show d+i < j+d from by omega)]
    · rw [liftVar_le h1, liftVar_le h1,
        liftVar_le (show c ≤ 1+i from by omega),
        liftVar_le (show c ≤ k+1+i from by omega),
        liftVar_le (show j+d ≤ d+(1+i) from by omega)]
      omega
  | sort | const => intros; rfl
  | app f a ihf iha => simp [liftN, ihf _ _ hc, iha _ _ hc]
  | lam A b ihA ihb | forallE A b ihA ihb =>
    simp only [liftN]
    refine congr (congrArg _ (ihA _ _ hc)) ?_
    have := ihb (j := j+1) (c := c+1) k d (by omega)
    rwa [show j+1+d = j+d+1 from by omega] at this

/-- Telescope form of `liftN_liftN_mid`. The outer lift is inserted at the
seam between the lift below the telescope and the lift that opened the
telescope's original ambient context. -/
theorem liftTelN_liftN_mid : ∀ (tel : List VExpr) {j c : Nat} (k d : Nat), c ≤ j →
    liftTelN k (liftTelN d (liftTelN 1 tel j) c) (j+d) =
      liftTelN d (liftTelN (k+1) tel j) c
  | [], _, _, _, _, _ => rfl
  | A :: tel, j, c, k, d, hc => by
    show ((A.liftN 1 j).liftN d c).liftN k (j+d) :: _ =
      (A.liftN (k+1) j).liftN d c :: _
    rw [liftN_liftN_mid A k d hc]
    congr 1
    rw [show j+d+1 = j+1+d from by omega]
    exact liftTelN_liftN_mid tel k d (Nat.succ_le_succ hc)

/-- Disjoint lifts commute: an outer lift below an inner one slides past
it, pushing the inner cutoff up. -/
theorem liftN_liftN_comm : ∀ (e : VExpr) (n k c K : Nat), c ≤ K →
    (e.liftN k K).liftN n c = (e.liftN n c).liftN k (K + n) := by
  intro e
  induction e with intro n k c K hc
  | bvar i =>
    show VExpr.bvar (liftVar n (liftVar k i K) c) = .bvar (liftVar k (liftVar n i c) (K+n))
    congr 1
    rcases Nat.lt_or_ge i c with h2 | h2
    · rw [liftVar_lt (show i < K from by omega), liftVar_lt h2,
        liftVar_lt (show i < K+n from by omega)]
    · rcases Nat.lt_or_ge i K with h1 | h1
      · rw [liftVar_lt h1, liftVar_le h2,
          liftVar_lt (show n+i < K+n from by omega)]
      · rw [liftVar_le h1, liftVar_le (show c ≤ k+i from by omega), liftVar_le h2,
          liftVar_le (show K+n ≤ n+i from by omega)]
        omega
  | sort | const => intros; rfl
  | app f a ihf iha => simp [liftN, ihf _ _ _ _ hc, iha _ _ _ _ hc]
  | lam A b ihA ihb | forallE A b ihA ihb =>
    simp only [liftN]
    refine congr (congrArg _ (ihA _ _ _ _ hc)) ?_
    have := ihb n k (c+1) (K+1) (by omega)
    rwa [show K+1+n = K+n+1 from by omega] at this

theorem instN_appN (a : VExpr) (k : Nat) (f : VExpr) : ∀ (as : List VExpr),
    (f.appN as).inst a k = appN (f.inst a k) (as.map (·.inst a k))
  | [] => rfl
  | e :: as => by
    show (VExpr.appN (f.app e) as).inst a k = _
    rw [instN_appN a k (f.app e) as]
    rfl

/-- Instantiation under a telescope: the entry at depth `q` instantiates
at `k+q`. -/
def instTelN (a : VExpr) : List VExpr → Nat → List VExpr
  | [], _ => []
  | A :: As, k => A.inst a k :: instTelN a As (k+1)

theorem instTelN_length (a : VExpr) : ∀ (tel : List VExpr) (k : Nat),
    (instTelN a tel k).length = tel.length
  | [], _ => rfl
  | _ :: tel, k => by simp [instTelN, instTelN_length a tel (k+1)]

theorem instN_forallN (a : VExpr) : ∀ (tel : List VExpr) (X : VExpr) (k : Nat),
    (forallN tel X).inst a k = forallN (instTelN a tel k) (X.inst a (k + tel.length))
  | [], _, _ => rfl
  | A :: tel, X, k => by
    show VExpr.forallE _ _ = VExpr.forallE _ _
    rw [instN_forallN a tel X (k+1),
      show k+1+tel.length = k+(tel.length+1) from by omega]
    rfl

/-- Iterated instantiation of a body under `es.length` binders, consuming
the spine outermost-first. -/
def instRev : VExpr → List VExpr → VExpr
  | C, [] => C
  | C, e :: es => instRev (C.inst e es.length) es

theorem instRev_closedN : ∀ (es : List VExpr) {C : VExpr}, C.ClosedN 0 →
    instRev C es = C
  | [], _, _ => rfl
  | e :: es, C, hC => by
    show instRev (C.inst e es.length) es = C
    rw [hC.instN_eq (Nat.zero_le _)]
    exact instRev_closedN es hC

theorem instRev_bvar_ge : ∀ (es : List VExpr) {i : Nat}, es.length ≤ i →
    instRev (.bvar i) es = .bvar (i - es.length)
  | [], i, _ => by simp [instRev]
  | e :: es, i, h => by
    have h' : es.length < i := by simpa using h
    show instRev ((VExpr.bvar i).inst e es.length) es = _
    rw [show (VExpr.bvar i).inst e es.length = .bvar (i-1) from by
        show VExpr.instVar i e es.length = _
        unfold VExpr.instVar
        rw [if_neg (by omega), if_neg (by omega)],
      instRev_bvar_ge es (by omega)]
    congr 1
    simp only [List.length_cons]
    omega

/-- The spine consumes a fully lifted body without a trace. -/
theorem instRev_liftN_len : ∀ (es : List VExpr) (X : VExpr),
    instRev (X.liftN es.length) es = X
  | [], X => by simp [instRev, liftN_zero]
  | e :: es, X => by
    show instRev ((X.liftN (es.length+1)).inst e es.length) es = X
    rw [show X.liftN (es.length+1) = (X.liftN es.length).liftN 1 es.length from
        (liftN'_liftN' (Nat.zero_le _) (by omega)).symm,
      inst_liftN]
    exact instRev_liftN_len es X

theorem instRev_bvar_lt_cons (es : List VExpr) (e : VExpr) {i : Nat} (hi : i < es.length) :
    instRev (.bvar i) (e :: es) = instRev (.bvar i) es := by
  show instRev ((VExpr.bvar i).inst e es.length) es = _
  congr 1
  show VExpr.instVar i e es.length = .bvar i
  unfold VExpr.instVar
  rw [if_pos hi]

theorem mem_bvarRevRange : ∀ {m off : Nat} {x : VExpr}, x ∈ bvarRevRange off m →
    ∃ i, x = .bvar i ∧ off ≤ i ∧ i < off + m
  | m+1, off, x, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨off + m, rfl, by omega, by omega⟩
    · obtain ⟨i, rfl, h1, h2⟩ := mem_bvarRevRange h
      exact ⟨i, rfl, h1, by omega⟩

/-- The last `es.length` variables consume to the spine itself. -/
theorem map_instRev_bvarRevRange : ∀ (es : List VExpr),
    (bvarRevRange 0 es.length).map (instRev · es) = es
  | [] => rfl
  | e :: es => by
    show instRev (.bvar (0 + es.length)) (e :: es) ::
      (bvarRevRange 0 es.length).map (instRev · (e :: es)) = e :: es
    congr 1
    · show instRev ((VExpr.bvar (0 + es.length)).inst e es.length) es = e
      rw [Nat.zero_add,
        show (VExpr.bvar es.length).inst e es.length = e.liftN es.length from by
          show VExpr.instVar es.length e es.length = _
          unfold VExpr.instVar
          rw [if_neg (Nat.lt_irrefl _), if_pos rfl]]
      exact instRev_liftN_len es e
    · rw [List.map_congr_left fun x hx => ?_, map_instRev_bvarRevRange es]
      obtain ⟨i, rfl, -, h2⟩ := mem_bvarRevRange hx
      exact instRev_bvar_lt_cons es e (by omega)

theorem map_instRev_bvarRevRange_ge (es : List VExpr) : ∀ (q off : Nat),
    es.length ≤ off →
    (bvarRevRange off q).map (instRev · es) = bvarRevRange (off - es.length) q
  | 0, _, _ => rfl
  | q+1, off, h => by
    show instRev (.bvar (off+q)) es :: _ = _
    rw [instRev_bvar_ge es (by omega), map_instRev_bvarRevRange_ge es q off h]
    congr 2
    omega

theorem instRev_appN (es : List VExpr) : ∀ (f : VExpr) (as : List VExpr),
    instRev (appN f as) es = appN (instRev f es) (as.map (instRev · es)) := by
  induction es with intro f as
  | nil => simp [instRev, List.map_id']
  | cons e es ih =>
    show instRev ((appN f as).inst e es.length) es = _
    rw [instN_appN, ih]
    simp [instRev, List.map_map, Function.comp_def]

theorem instRev_forallE_sort (u : VLevel) : ∀ (es : List VExpr) (D : VExpr),
    instRev (.forallE D (.sort u)) es = .forallE (instRev D es) (.sort u)
  | [], _ => rfl
  | e :: es, D => instRev_forallE_sort u es (D.inst e es.length)

theorem bvarRevRange_append : ∀ (m k : Nat),
    bvarRevRange k m ++ bvarRevRange 0 k = bvarRevRange 0 (k + m)
  | 0, k => by simp [bvarRevRange]
  | m+1, k => by
    show VExpr.bvar (k + m) :: (bvarRevRange k m ++ bvarRevRange 0 k) = _
    rw [bvarRevRange_append m k, show k + (m+1) = (k+m)+1 from rfl]
    show _ = VExpr.bvar (0 + (k+m)) :: bvarRevRange 0 (k+m)
    rw [Nat.zero_add]

theorem appHead_appN : ∀ (as : List VExpr) (f : VExpr), (appN f as).appHead = f.appHead
  | [], _ => rfl
  | a :: as, f => appHead_appN as (f.app a)

theorem appArgs_appN : ∀ (as acc : List VExpr) (f : VExpr),
    (appN f as).appArgs acc = f.appArgs (as ++ acc)
  | [], _, _ => rfl
  | a :: as, acc, f => by
    show (VExpr.appN (f.app a) as).appArgs acc = _
    rw [appArgs_appN as acc (f.app a)]
    rfl

theorem appN_appHead_appArgs : ∀ (e : VExpr) (acc : List VExpr),
    appN e.appHead (e.appArgs acc) = appN e acc
  | .app f a, acc => by
    show appN f.appHead (f.appArgs (a :: acc)) = _
    rw [appN_appHead_appArgs f (a :: acc)]
    rfl
  | .bvar _, _ | .sort _, _ | .const _ _, _ | .lam _ _, _ | .forallE _ _, _ => rfl

end VExpr

/-! ## Anatomy of the stage-3 predicate -/

namespace VInductDecl

/-- A constructor-type telescope splits as fields over the result. -/
theorem forallN_ctorFields_resultOf : ∀ (e : VExpr),
    VExpr.forallN (ctorFields e) e.resultOf = e
  | .forallE B rest => congrArg (VExpr.forallE B) (forallN_ctorFields_resultOf rest)
  | .bvar _ | .sort _ | .const _ _ | .app _ _ | .lam _ _ => rfl

/-- Unpack a recursive-field check into its structural content. -/
theorem isRecField_eq {U T np ni j B} (h : isRecField U T np ni j B = true) :
    B = VExpr.appN (.const T (VLevel.params U))
      (VExpr.bvarRevRange j np ++ recFieldIdxs np B) ∧
    (recFieldIdxs np B).length = ni ∧
    ∀ e ∈ recFieldIdxs np B, e.hasConst T = false := by
  simp only [isRecField, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨?_, ?_, fun e he => by simpa [Bool.not_eq_true'] using h4 e he⟩
  · have hB : B = VExpr.appN B.appHead (B.appArgs []) :=
      (VExpr.appN_appHead_appArgs B []).symm
    conv => lhs; rw [hB, h1,
      show VExpr.appArgs B [] =
        (VExpr.appArgs B []).take np ++ (VExpr.appArgs B []).drop np from
        (List.take_append_drop ..).symm,
      h3]
    rfl
  · simp only [recFieldIdxs, List.length_drop, h2]
    omega

/-- Unpack recursive-argument analysis beneath a possibly empty Pi telescope.
The terminal family application is seen under both the preceding constructor
fields (`j`) and the returned recursive binders. -/
theorem recTarget?_eq {U T np ni j B As idxs}
    (h : recTarget? U T np ni j B = some (As, idxs)) :
    B = VExpr.forallN As
      (VExpr.appN (.const T (VLevel.params U))
        (VExpr.bvarRevRange (j + As.length) np ++ idxs)) ∧
    idxs.length = ni ∧
    (∀ e ∈ idxs, e.hasConst T = false) ∧
    ∀ (q : Nat) (A : VExpr), As[q]? = some A → A.hasConst T = false := by
  induction B generalizing j As idxs with
  | forallE A rest _ ih =>
    simp only [recTarget?] at h
    split at h
    · contradiction
    · next hA =>
      split at h
      · next As' idxs' hrest =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hshape, hlen, hfree, hbinders⟩ := ih hrest
        refine ⟨?_, hlen, hfree, ?_⟩
        · show VExpr.forallE A rest = VExpr.forallE A _
          rw [hshape, show j + 1 + As'.length = j + (As'.length + 1) from by omega]
          simp only [List.length_cons]
        · intro q A' hq
          match q, hq with
          | 0, hq =>
            obtain rfl : A = A' := by simpa using hq
            cases hAT : A.hasConst T with
            | false => rfl
            | true => exact (hA hAT).elim
          | q+1, hq => exact hbinders q A' (by simpa using hq)
      · contradiction
  | bvar i | sort i | const i | app i i | lam i i =>
    simp only [recTarget?] at h
    split at h
    · next hrec =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hshape, hlen, hfree⟩ := isRecField_eq hrec
      exact ⟨by simpa using hshape, hlen, hfree, by simp⟩
    · contradiction

/-- Public recursive-argument anatomy, including the stable field and
one-family target indices carried by the descriptor. -/
theorem recArg?_eq {U T np ni j B r}
    (h : recArg? U T np ni j B = some r) :
    r.fieldIndex = j ∧ r.targetType = 0 ∧
    B = VExpr.forallN r.binders
      (VExpr.appN (.const T (VLevel.params U))
        (VExpr.bvarRevRange (j + r.binders.length) np ++ r.indices)) ∧
    r.indices.length = ni ∧
    (∀ e ∈ r.indices, e.hasConst T = false) ∧
    ∀ (q : Nat) (A : VExpr), r.binders[q]? = some A → A.hasConst T = false := by
  unfold recArg? at h
  split at h
  · next binders indices htarget =>
    simp only [Option.some.injEq] at h
    subst r
    obtain ⟨hshape, hlen, hfree, hbinders⟩ := recTarget?_eq htarget
    exact ⟨rfl, rfl, hshape, hlen, hfree, hbinders⟩
  · contradiction

/-- With no Pi binders, recursive-argument recognition is exactly the direct
recursive-field check. -/
theorem recTarget?_nil {U T np ni j B idxs}
    (h : recTarget? U T np ni j B = some ([], idxs)) :
    isRecField U T np ni j B = true ∧ idxs = recFieldIdxs np B := by
  cases B with
  | forallE A rest =>
    simp only [recTarget?] at h
    split at h
    · contradiction
    · cases hrest : recTarget? U T np ni (j+1) rest with
      | none => simp [hrest] at h
      | some out =>
        obtain ⟨As, is⟩ := out
        simp [hrest] at h
  | bvar i | sort i | const i | app i i | lam i i =>
    simp only [recTarget?] at h
    split at h
    · next hrec =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨hrec, h.2.symm⟩
    · contradiction

theorem recArg?_nil {U T np ni j B r}
    (h : recArg? U T np ni j B = some r) (hr : r.binders = []) :
    isRecField U T np ni j B = true ∧ r.indices = recFieldIdxs np B := by
  unfold recArg? at h
  split at h
  · next binders indices htarget =>
    simp only [Option.some.injEq] at h
    subst r
    simp only at hr
    subst binders
    exact recTarget?_nil htarget
  · contradiction

/-- A direct recursive-field success normalizes to the descriptor with an
empty binder telescope. -/
theorem recArg?_of_isRecField {U T np ni j B}
    (h : isRecField U T np ni j B = true) :
    recArg? U T np ni j B = some
      { fieldIndex := j, binders := [], targetType := 0,
        indices := recFieldIdxs np B } := by
  cases B with
  | forallE A rest => simp [isRecField, VExpr.appHead] at h
  | bvar i | sort i | const i | app i i | lam i i =>
    simp_all [recArg?, recTarget?]

theorem stage3Ctor_eq {U T np ni} : ∀ {j₀ : Nat} {e : VExpr},
    stage3Ctor U T np ni j₀ e = true →
    e = VExpr.forallN (ctorFields e)
      (VExpr.appN (.const T (VLevel.params U))
        (VExpr.bvarRevRange (j₀ + (ctorFields e).length) np ++
          recFieldIdxs np e.resultOf)) ∧
    (recFieldIdxs np e.resultOf).length = ni ∧
    (∀ x ∈ recFieldIdxs np e.resultOf, x.hasConst T = false) ∧
    ∀ q B, (ctorFields e)[q]? = some B → stage3Field U T np ni (j₀ + q) B = true := by
  intro j₀ e h
  induction e generalizing j₀ with
  | forallE B rest _ ih =>
    rw [show stage3Ctor U T np ni j₀ (.forallE B rest) =
      (stage3Field U T np ni j₀ B && stage3Ctor U T np ni (j₀+1) rest) from rfl,
      Bool.and_eq_true] at h
    have ⟨ih1, ih2, ih3, ih4⟩ := ih h.2
    refine ⟨?_, ih2, ih3, ?_⟩
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
        have := ih4 q B' (by simpa [ctorFields] using hB')
        rwa [show j₀+1+q = j₀+(q+1) from by omega] at this
  | bvar i =>
    exact ⟨(isRecField_eq h).1, (isRecField_eq h).2.1, (isRecField_eq h).2.2,
      fun q B h' => by simp [ctorFields] at h'⟩
  | sort l =>
    exact ⟨(isRecField_eq h).1, (isRecField_eq h).2.1, (isRecField_eq h).2.2,
      fun q B h' => by simp [ctorFields] at h'⟩
  | const c ls =>
    exact ⟨(isRecField_eq h).1, (isRecField_eq h).2.1, (isRecField_eq h).2.2,
      fun q B h' => by simp [ctorFields] at h'⟩
  | app f a _ _ =>
    exact ⟨(isRecField_eq h).1, (isRecField_eq h).2.1, (isRecField_eq h).2.2,
      fun q B h' => by simp [ctorFields] at h'⟩
  | lam A b _ _ =>
    exact ⟨(isRecField_eq h).1, (isRecField_eq h).2.1, (isRecField_eq h).2.2,
      fun q B h' => by simp [ctorFields] at h'⟩

/-- Failure of the public acceptance predicate is exactly failure to produce
the shared checked descriptor. -/
theorem checked?_eq_none_iff {decl : VInductDecl} :
    decl.checked? = none ↔ decl.stage3 = false := by
  unfold stage3
  cases decl.checked? <;> simp

/-- Successful acceptance retains the descriptor rather than discarding it. -/
theorem exists_checked_of_stage3 {decl : VInductDecl} (h : decl.stage3 = true) :
    ∃ checked, decl.checked? = some checked := by
  unfold stage3 at h
  cases hc : decl.checked? with
  | none => simp [hc] at h
  | some checked => exact ⟨checked, rfl⟩

/-- Proof-level constructor-header coherence exported from the computational
normalization-shape check. -/
def CtorHeaderEq (source view : VConstVal) : Prop :=
  source.name = view.name ∧ source.uvars = view.uvars

/-- Proof-level family-header coherence, including constructor order. -/
def TypeHeaderEq (source view : VInductiveType) : Prop :=
  source.name = view.name ∧ source.uvars = view.uvars ∧
    List.Forall₂ CtorHeaderEq source.ctors view.ctors

theorem sameCtorHeaders_iff_forall₂ : ∀ {source view},
    sameCtorHeaders source view = true ↔
      List.Forall₂ CtorHeaderEq source view
  | [], [] => ⟨fun _ => .nil, fun _ => rfl⟩
  | [], _ :: _ => by
    constructor
    · intro h; exact Bool.noConfusion h
    · intro h; nomatch h
  | _ :: _, [] => by
    constructor
    · intro h; exact Bool.noConfusion h
    · intro h; nomatch h
  | source :: sources, view :: views => by
    constructor
    · intro h
      simp only [sameCtorHeaders, Bool.and_eq_true, beq_iff_eq] at h
      exact .cons ⟨h.1.1, h.1.2⟩ (sameCtorHeaders_iff_forall₂.1 h.2)
    · intro h
      obtain ⟨hhead, htail⟩ := List.forall₂_cons.1 h
      simp only [sameCtorHeaders, Bool.and_eq_true, beq_iff_eq]
      exact ⟨⟨hhead.1, hhead.2⟩, sameCtorHeaders_iff_forall₂.2 htail⟩

theorem sameTypeHeaders_iff_forall₂ : ∀ {source view},
    sameTypeHeaders source view = true ↔
      List.Forall₂ TypeHeaderEq source view
  | [], [] => ⟨fun _ => .nil, fun _ => rfl⟩
  | [], _ :: _ => by
    constructor
    · intro h; exact Bool.noConfusion h
    · intro h; nomatch h
  | _ :: _, [] => by
    constructor
    · intro h; exact Bool.noConfusion h
    · intro h; nomatch h
  | source :: sources, view :: views => by
    constructor
    · intro h
      simp only [sameTypeHeaders, Bool.and_eq_true, beq_iff_eq] at h
      exact .cons
        ⟨h.1.1.1, h.1.1.2, sameCtorHeaders_iff_forall₂.1 h.1.2⟩
        (sameTypeHeaders_iff_forall₂.1 h.2)
    · intro h
      obtain ⟨hhead, htail⟩ := List.forall₂_cons.1 h
      simp only [sameTypeHeaders, Bool.and_eq_true, beq_iff_eq]
      exact ⟨⟨⟨hhead.1, hhead.2.1⟩,
        sameCtorHeaders_iff_forall₂.2 hhead.2.2⟩,
        sameTypeHeaders_iff_forall₂.2 htail⟩

/-- Every accepted normalization preserves declaration arity and all
family/constructor identities in order. -/
theorem Normalization.shape {source : VInductDecl}
    (norm : Normalization source) :
    source.uvars = norm.view.uvars ∧
    source.nparams = norm.view.nparams ∧
    List.Forall₂ TypeHeaderEq source.types norm.view.types := by
  have h := norm.shape_eq
  simp only [normalizationShape, Bool.and_eq_true, beq_iff_eq,
    sameTypeHeaders_iff_forall₂] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- The singleton source family paired with the checked singleton analysis
view. This is the raw payload future normalized generation must insert. -/
theorem NormalizedChecked.source_anatomy {source : VInductDecl}
    (block : NormalizedChecked source) :
    ∃ raw,
      source.types = [raw] ∧
      raw.name = block.checked.type.name ∧
      raw.uvars = block.checked.type.uvars ∧
      List.Forall₂ CtorHeaderEq raw.ctors block.checked.type.ctors := by
  have htypes := block.normalization.shape.2.2
  rw [block.source_types_eq, block.checked.types_eq] at htypes
  obtain ⟨htype, -⟩ := List.forall₂_cons.1 htypes
  exact ⟨block.sourceType, block.source_types_eq,
    htype.1, htype.2.1, htype.2.2⟩

theorem NormalizedChecked.uvars_eq {source : VInductDecl}
    (block : NormalizedChecked source) :
    source.uvars = block.normalization.view.uvars :=
  block.normalization.shape.1

theorem NormalizedChecked.nparams_eq {source : VInductDecl}
    (block : NormalizedChecked source) :
    source.nparams = block.normalization.view.nparams :=
  block.normalization.shape.2.1

/-- Unpack the complete executable layout certificate used by mixed
raw/view generation. -/
theorem GenerationChecked.shape {source : VInductDecl}
    (gen : GenerationChecked source) :
    gen.block.rawParams.length = source.nparams ∧
    gen.block.rawParams.length = gen.block.checked.params.length ∧
    gen.block.rawIndices.length = gen.block.checked.indices.length ∧
    gen.block.ctorPairs.length = gen.block.sourceType.ctors.length ∧
    gen.block.ctorPairs.length = gen.block.checked.constructors.length ∧
    ∀ ctor ∈ gen.block.ctorPairs,
      ctor.raw.name = ctor.view.value.name ∧
      ctor.raw.uvars = ctor.view.value.uvars ∧
      (VExpr.telN source.nparams ctor.raw.type).length = source.nparams ∧
      (ctor.rawFields source.nparams).length = ctor.view.fields.length := by
  have h := gen.shape_eq
  simp only [NormalizedChecked.generationShape,
    NormalizedCtor.generationShape, Bool.and_eq_true, beq_iff_eq,
    List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hparams, hparams'⟩, hindices⟩, hraws⟩, hviews⟩,
    hctors⟩ := h
  refine ⟨hparams, hparams', hindices, hraws, hviews, ?_⟩
  intro ctor hctor
  obtain ⟨⟨⟨hname, hU⟩, htel⟩, hfields⟩ := hctors ctor hctor
  exact ⟨hname, hU, htel, hfields⟩

theorem pairNormalizedCtors_map_raw :
    ∀ (raws : List VConstVal) (views : List CheckedCtor),
      raws.length = views.length →
      (pairNormalizedCtors raws views).map (·.raw) = raws
  | [], [], _ => rfl
  | raw :: raws, view :: views, h => by
    simp only [pairNormalizedCtors, List.map_cons, List.cons.injEq, true_and]
    apply pairNormalizedCtors_map_raw
    simpa using h

theorem pairNormalizedCtors_map_view :
    ∀ (raws : List VConstVal) (views : List CheckedCtor),
      raws.length = views.length →
      (pairNormalizedCtors raws views).map (·.view) = views
  | [], [], _ => rfl
  | raw :: raws, view :: views, h => by
    simp only [pairNormalizedCtors, List.map_cons, List.cons.injEq, true_and]
    apply pairNormalizedCtors_map_view
    simpa using h

/-- Membership in an identity pairing recovers the single raw constructor
that supplied both sides of the pair. -/
theorem pairNormalizedCtors_map_self_mem
    {U : Nat} {T : Name} {np ni : Nat} :
    ∀ {cs : List VConstVal} {ctor : NormalizedCtor},
      ctor ∈ pairNormalizedCtors cs
        (cs.map (CheckedCtor.ofDirect U T np ni)) →
      ∃ c ∈ cs, ctor =
        ⟨c, CheckedCtor.ofDirect U T np ni c⟩
  | [], _, h => by simp [pairNormalizedCtors] at h
  | c :: cs, ctor, h => by
    simp only [List.map_cons, pairNormalizedCtors, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨c, .head _, rfl⟩
    · obtain ⟨c', hc', rfl⟩ :=
        pairNormalizedCtors_map_self_mem h
      exact ⟨c', .tail _ hc', rfl⟩

/-- Every raw constructor occurs in its canonical identity pair. -/
theorem pairNormalizedCtors_map_self_contains
    {U : Nat} {T : Name} {np ni : Nat} :
    ∀ {cs : List VConstVal} {c : VConstVal},
      c ∈ cs →
      (⟨c, CheckedCtor.ofDirect U T np ni c⟩ :
        NormalizedCtor) ∈
        pairNormalizedCtors cs
          (cs.map (CheckedCtor.ofDirect U T np ni))
  | _ :: _, _, .head _ => .head _
  | _ :: _, _, .tail _ hc =>
      .tail _ (pairNormalizedCtors_map_self_contains hc)

/-- The identity generation path pairs each stored constructor with its own
direct analyzer descriptor. -/
theorem Checked.identityGeneration_ctor
    {source : VInductDecl} (checked : source.Checked)
    {ctor : NormalizedCtor}
    (hctor : ctor ∈ checked.identityGeneration.block.ctorPairs) :
    ∃ c ∈ checked.type.ctors, ctor =
      ⟨c, CheckedCtor.ofDirect source.uvars checked.type.name
        source.nparams checked.indices.length c⟩ := by
  apply pairNormalizedCtors_map_self_mem
  simpa only [Checked.identityGeneration, Checked.identityBlock,
    NormalizedChecked.ctorPairs, checked.constructors_eq] using hctor

/-- Positional pairing neither drops nor reorders raw constructors. -/
theorem GenerationChecked.rawCtors_eq {source : VInductDecl}
    (gen : GenerationChecked source) :
    gen.block.ctorPairs.map (·.raw) = gen.block.sourceType.ctors := by
  apply pairNormalizedCtors_map_raw
  exact gen.shape.2.2.2.1.symm.trans gen.shape.2.2.2.2.1

/-- Every checked constructor appears in the same paired position. -/
theorem GenerationChecked.viewCtors_eq {source : VInductDecl}
    (gen : GenerationChecked source) :
    gen.block.ctorPairs.map (·.view) = gen.block.checked.constructors := by
  apply pairNormalizedCtors_map_view
  exact gen.shape.2.2.2.1.symm.trans gen.shape.2.2.2.2.1

/-- Identity normalization is computationally the legacy analyzer. -/
theorem Normalization.identity_checked? (source : VInductDecl) :
    (Normalization.identity source).checked? = source.checked? := rfl

theorem identityChecked?_isSome (source : VInductDecl) :
    (identityChecked? source).isSome = source.checked?.isSome := by
  obtain ⟨U, np, types⟩ := source
  cases types with
  | nil => rfl
  | cons type types =>
    cases types with
    | nil =>
      unfold identityChecked? Normalization.check?
      split
      · next sourceType hsource =>
        have htype : type = sourceType := by simpa using hsource
        subst sourceType
        split
        · next checked hchecked =>
          rw [← Normalization.identity_checked?]
          exact (congrArg (fun x => x.isSome) hchecked).symm
        · next hchecked =>
          rw [← Normalization.identity_checked?]
          exact (congrArg (fun x => x.isSome) hchecked).symm
      · next hsource => exact (hsource type rfl).elim
    | cons type' types => rfl

/--
info: 'Lean4Lean.VInductDecl.Normalization.shape' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Normalization.shape

/--
info: 'Lean4Lean.VInductDecl.NormalizedChecked.source_anatomy' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms NormalizedChecked.source_anatomy

/--
info: 'Lean4Lean.VInductDecl.GenerationChecked.shape' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms GenerationChecked.shape

/--
info: 'Lean4Lean.VInductDecl.GenerationChecked.rawCtors_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms GenerationChecked.rawCtors_eq

/--
info: 'Lean4Lean.VInductDecl.GenerationChecked.viewCtors_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms GenerationChecked.viewCtors_eq

/--
info: 'Lean4Lean.VInductDecl.identityChecked?_isSome' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms identityChecked?_isSome

/- Identity-normalization compatibility is part of the public artifact
boundary. The conversion itself is computational; its proof fields inherit
the standard `Classical.choice` dependency already present in
`Normalization.identity`'s reflexive header check. -/
/--
info: 'Lean4Lean.VInductDecl.Checked.analyzer_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Checked.analyzer_eq

/--
info: 'Lean4Lean.VInductDecl.Checked.identityBlock_generationShape' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Checked.identityBlock_generationShape

/--
info: 'Lean4Lean.VInductDecl.Checked.motiveType_eq_legacy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Checked.motiveType_eq_legacy

/--
info: 'Lean4Lean.VInductDecl.Checked.minorTypes_eq_legacy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Checked.minorTypes_eq_legacy

/--
info: 'Lean4Lean.VInductDecl.Checked.recursor_eq_legacy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Checked.recursor_eq_legacy

/--
info: 'Lean4Lean.VInductDecl.Checked.generatedRules_eq_legacy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Checked.generatedRules_eq_legacy

/-- The four executable checks retained by a successful descriptor. Keeping
this bridge centralized lets the public proof API expose logical facts without
each consumer re-destructing `stage3Core`. -/
theorem Checked.analysis_accepted {decl : VInductDecl} (checked : decl.Checked) :
    stage3DirectCore decl.uvars decl.nparams checked.type = true ∧
    namesOK checked.type = true ∧ closedOK checked.type = true ∧
    levelsOK decl.uvars checked.type = true := by
  cases decl with
  | mk U np tys =>
    have htypes : tys = [checked.type] := checked.types_eq
    have hcore := checked.accepted
    simp only [stage3Core, htypes, Bool.and_eq_true] at hcore
    exact ⟨hcore.1, hcore.2.1, hcore.2.2.1, hcore.2.2.2⟩

/-- Every successful descriptor has pairwise-distinct generated type,
constructor, and recursor names. Downstream proofs should consume this fact
instead of unfolding the boolean analyzer. -/
theorem Checked.names_nodup {decl : VInductDecl} (checked : decl.Checked) :
    checked.names.Nodup := by
  rw [checked.names_eq]
  exact of_decide_eq_true (by simpa [namesOK] using checked.analysis_accepted.2.1)

/-- A checked family's type metadata has no loose term variables. -/
theorem Checked.type_closed {decl : VInductDecl} (checked : decl.Checked) :
    checked.type.type.ClosedN 0 := by
  have hclosed := checked.analysis_accepted.2.2.1
  simp only [closedOK, Bool.and_eq_true, List.all_eq_true] at hclosed
  exact of_decide_eq_true hclosed.1

/-- Every constructor type retained by a successful descriptor has no loose
term variables. -/
theorem Checked.ctor_closed {decl : VInductDecl} (checked : decl.Checked)
    {ctor : VConstVal} (hctor : ctor ∈ checked.type.ctors) : ctor.type.ClosedN 0 := by
  have hclosed := checked.analysis_accepted.2.2.1
  simp only [closedOK, Bool.and_eq_true, List.all_eq_true] at hclosed
  exact of_decide_eq_true (hclosed.2 ctor hctor)

/-- Every universe annotation in a checked family's type is in range. -/
theorem Checked.type_levelWF {decl : VInductDecl} (checked : decl.Checked) :
    checked.type.type.LevelWF decl.uvars := by
  have hlevels := checked.analysis_accepted.2.2.2
  simp only [levelsOK, Bool.and_eq_true, List.all_eq_true] at hlevels
  exact of_decide_eq_true hlevels.1

/-- Every universe annotation in a checked constructor type is in range. -/
theorem Checked.ctor_levelWF {decl : VInductDecl} (checked : decl.Checked)
    {ctor : VConstVal} (hctor : ctor ∈ checked.type.ctors) :
    ctor.type.LevelWF decl.uvars := by
  have hlevels := checked.analysis_accepted.2.2.2
  simp only [levelsOK, Bool.and_eq_true, List.all_eq_true] at hlevels
  exact of_decide_eq_true (hlevels.2 ctor hctor)

/-- The direct one-family facts carried by the descriptor, including the
new pre-declaration prohibition on self-reference in parameter/index domains. -/
theorem Checked.direct_anatomy {decl : VInductDecl} (checked : decl.Checked) :
    checked.type.uvars = decl.uvars ∧ checked.params.length = decl.nparams ∧
    checked.resultLevel.WF decl.uvars ∧
    (∀ P ∈ checked.params, P.hasConst checked.type.name = false) ∧
    (∀ I ∈ checked.indices, I.hasConst checked.type.name = false) ∧
    ∀ c ∈ checked.type.ctors, c.uvars = decl.uvars ∧
      VExpr.telN decl.nparams c.type = VExpr.telN decl.nparams checked.type.type ∧
      stage3Ctor decl.uvars checked.type.name decl.nparams checked.indices.length 0
        (VExpr.dropN decl.nparams c.type) = true := by
  have hdirect := checked.analysis_accepted.1
  simp only [stage3DirectCore, Bool.and_eq_true, beq_iff_eq,
    List.all_eq_true] at hdirect
  obtain ⟨⟨⟨⟨⟨hU, hparams⟩, hresult⟩, hformer⟩, -⟩, hctors⟩ := hdirect
  simp only [typeFormerOK, Bool.and_eq_true, List.all_eq_true] at hformer
  refine ⟨hU, by simpa [checked.params_eq] using hparams, ?_, ?_, ?_, ?_⟩
  · rw [checked.result_eq] at hresult
    simpa using hresult
  · simpa [checked.params_eq] using hformer.1
  · simpa [checked.indices_eq] using hformer.2
  · intro c hc
    simpa [checked.indices_eq, and_assoc] using hctors c hc

/-- The raw family payload has the source declaration's universe arity. -/
theorem NormalizedChecked.sourceType_uvars_eq {source : VInductDecl}
    (block : NormalizedChecked source) :
    block.sourceType.uvars = source.uvars := by
  obtain ⟨raw, hsource, _, hrawU, _⟩ := block.source_anatomy
  have hraw : raw = block.sourceType := by
    simpa using hsource.symm.trans block.source_types_eq
  subst raw
  exact hrawU.trans
    (block.checked.direct_anatomy.1.trans block.uvars_eq.symm)

/-- The raw and checked family identities agree. -/
theorem NormalizedChecked.sourceType_name_eq {source : VInductDecl}
    (block : NormalizedChecked source) :
    block.sourceType.name = block.checked.type.name := by
  obtain ⟨raw, hsource, hname, _, _⟩ := block.source_anatomy
  have hraw : raw = block.sourceType := by
    simpa using hsource.symm.trans block.source_types_eq
  subst raw
  exact hname

/-- Every paired raw constructor has the source declaration's universe
arity. -/
theorem GenerationChecked.ctor_uvars_eq {source : VInductDecl}
    (gen : GenerationChecked source) {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) :
    ctor.raw.uvars = source.uvars := by
  have hview : ctor.view ∈ gen.block.checked.constructors := by
    rw [← gen.viewCtors_eq]
    exact List.mem_map.2 ⟨ctor, hctor, rfl⟩
  rw [gen.block.checked.constructors_eq] at hview
  have hviewU :
      ctor.view.value.uvars = gen.block.normalization.view.uvars := by
    obtain ⟨c, hc, hcview⟩ := List.mem_map.1 hview
    rw [← hcview]
    exact (gen.block.checked.direct_anatomy.2.2.2.2.2 c hc).1
  have hpairU := (gen.shape.2.2.2.2.2 ctor hctor).2.1
  exact hpairU.trans (hviewU.trans gen.block.uvars_eq.symm)

/-- A paired checked constructor is exactly the direct analyzer result for
the corresponding constructor in the normalized view. The statement is
rewritten to the raw block's public header, whose equality is certified by
normalization shape. -/
theorem GenerationChecked.viewCtor_ofDirect {source : VInductDecl}
    (gen : GenerationChecked source) {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) :
    ∃ c ∈ gen.block.checked.type.ctors,
      ctor.view = CheckedCtor.ofDirect source.uvars
        gen.block.sourceType.name source.nparams
        gen.block.checked.indices.length c := by
  have hview : ctor.view ∈ gen.block.checked.constructors := by
    rw [← gen.viewCtors_eq]
    exact List.mem_map.2 ⟨ctor, hctor, rfl⟩
  rw [gen.block.checked.constructors_eq] at hview
  obtain ⟨c, hc, hcview⟩ := List.mem_map.1 hview
  refine ⟨c, hc, ?_⟩
  rw [gen.block.uvars_eq, gen.block.nparams_eq,
    gen.block.sourceType_name_eq]
  exact hcview.symm

/-- Re-index declaration well-formedness onto the normalized checked data. -/
theorem Checked.wf_of_decl {decl : VInductDecl} (checked : decl.Checked)
    (hdecl : decl.WF env) : checked.WF env := by
  obtain ⟨-, hwf⟩ := hdecl
  obtain ⟨htel, hctors⟩ := hwf checked.type (by
    rw [checked.types_eq]
    exact .head _)
  have hsort : sortLevel decl.nparams checked.type = checked.resultLevel := by
    simp only [sortLevel, checked.result_eq]
  unfold Checked.WF
  refine ⟨?_, fun c hc => ?_⟩
  · simpa [checked.params_eq, checked.indices_eq] using htel
  · simpa [checked.params_eq, checked.indices_eq, hsort] using hctors c hc

/-- Normalized semantic evidence reconstructs the legacy declaration-level
`WF` contract. This is the compatibility direction used while clients migrate
to `Checked.WF`. -/
theorem Checked.to_declWF {decl : VInductDecl} (checked : decl.Checked)
    (hchecked : decl.checked? = some checked) (hwf : checked.WF env) : decl.WF env := by
  refine ⟨by simp [stage3, hchecked], ?_⟩
  intro ty hty
  rw [checked.types_eq] at hty
  obtain rfl := List.mem_singleton.1 hty
  have hsort : sortLevel decl.nparams checked.type = checked.resultLevel := by
    simp only [sortLevel, checked.result_eq]
  unfold Checked.WF at hwf
  simpa [checked.params_eq, checked.indices_eq, hsort] using hwf

/-- The environment-indexed declaration contract is exactly the existence of
the analyzer result together with semantic evidence for its normalized data. -/
theorem wf_iff_exists_checked {decl : VInductDecl} :
    decl.WF env ↔ ∃ checked, decl.checked? = some checked ∧ checked.WF env := by
  constructor
  · intro hdecl
    obtain ⟨checked, hchecked⟩ := exists_checked_of_stage3 hdecl.1
    exact ⟨checked, hchecked, checked.wf_of_decl hdecl⟩
  · rintro ⟨checked, hchecked, hwf⟩
    exact checked.to_declWF hchecked hwf

/- Keep the first exported descriptor invariants on the same accepted Theory
axiom baseline as the transaction API. -/
/--
info: 'Lean4Lean.VInductDecl.Checked.names_nodup' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Checked.names_nodup

/--
info: 'Lean4Lean.VInductDecl.Checked.type_closed' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Checked.type_closed

/--
info: 'Lean4Lean.VInductDecl.Checked.ctor_closed' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Checked.ctor_closed

/--
info: 'Lean4Lean.VInductDecl.Checked.analysis_accepted' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Checked.analysis_accepted

/--
info: 'Lean4Lean.VInductDecl.Checked.type_levelWF' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Checked.type_levelWF

/--
info: 'Lean4Lean.VInductDecl.Checked.ctor_levelWF' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Checked.ctor_levelWF

/--
info: 'Lean4Lean.VInductDecl.Checked.direct_anatomy' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Checked.direct_anatomy

/--
info: 'Lean4Lean.VInductDecl.Checked.wf_of_decl' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Checked.wf_of_decl

/--
info: 'Lean4Lean.VInductDecl.Checked.to_declWF' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Checked.to_declWF

/--
info: 'Lean4Lean.VInductDecl.wf_iff_exists_checked' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms wf_iff_exists_checked

/-- Unpack `stage3` for a declaration already known (from `addInduct`
success) to have a singleton type list. -/
theorem stage3_anatomy {U np ty} (h : stage3 ⟨U, np, [ty]⟩ = true) :
    ty.uvars = U ∧ (VExpr.telN np ty.type).length = np ∧
    (∃ l, VExpr.resultOf (VExpr.dropN np ty.type) = .sort l ∧ l.WF U) ∧
    (∀ I ∈ ctorFields (VExpr.dropN np ty.type), I.hasConst ty.name = false) ∧
    ∀ c ∈ ty.ctors, c.uvars = U ∧
      VExpr.telN np c.type = VExpr.telN np ty.type ∧
      stage3Ctor U ty.name np (ctorFields (VExpr.dropN np ty.type)).length 0
        (VExpr.dropN np c.type) = true := by
  obtain ⟨checked, -⟩ := exists_checked_of_stage3 h
  have hcore := checked.accepted
  simp only [stage3Core, Bool.and_eq_true] at hcore
  have hdirect := hcore.1
  simp only [stage3DirectCore, Bool.and_eq_true, beq_iff_eq,
    List.all_eq_true] at hdirect
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, -⟩, h6⟩ := hdirect
  simp only [typeFormerOK, Bool.and_eq_true, List.all_eq_true] at h4
  refine ⟨h1, h2, ?_, fun I hI => by simpa [Bool.not_eq_true'] using h4.2 I hI,
    fun c hc => by simpa [and_assoc] using h6 c hc⟩
  split at h3
  · next l heq => exact ⟨l, heq, by simpa using h3⟩
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

theorem OnTel.of_append {env : VEnv} {U : Nat} : ∀ {As Bs Γ},
    OnTel env U Γ (As ++ Bs) → OnTel env U Γ As ∧ OnTel env U (As.reverse ++ Γ) Bs
  | [], _, _, h => ⟨trivial, h⟩
  | A :: As, Bs, Γ, ⟨hA, hT⟩ => by
    obtain ⟨h1, h2⟩ := OnTel.of_append (As := As) hT
    exact ⟨⟨hA, h1⟩, by simpa [List.append_assoc] using h2⟩

/-- Push a context lift under a reversed telescope: inserting binders below
shifts each telescope entry at its own depth. -/
theorem _root_.Lean4Lean.Ctx.LiftN.consTel {n : Nat} : ∀ (As : List VExpr) {k : Nat}
    {Γ Γ' : List VExpr}, Ctx.LiftN n k Γ Γ' →
    Ctx.LiftN n (As.length + k) (As.reverse ++ Γ)
      ((VExpr.liftTelN n As k).reverse ++ Γ')
  | [], k, Γ, Γ', W => by simpa using W
  | A :: As, k, Γ, Γ', W => by
    have h := Ctx.LiftN.consTel As (Ctx.LiftN.succ (A := A) W)
    rw [show As.length + (k+1) = (A :: As).length + k from by simp; omega] at h
    simpa [VExpr.liftTelN, List.append_assoc] using h

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

/-! ### Spine typing -/

theorem SpineWF.hasType_appN {env : VEnv} {U : Nat} {Γ : List VExpr} :
    ∀ {es : List VExpr} {A B f : VExpr}, env.SpineWF U Γ A es B →
    env.HasType U Γ f A → env.HasType U Γ (f.appN es) B := by
  intro es
  induction es with intro A B f h hf
  | nil => exact h ▸ hf
  | cons e es ih =>
    obtain ⟨A₁, A₂, rfl, he, hrest⟩ := h
    exact ih hrest (hf.app he)

/-- Extend a well-typed application spine by one final argument. -/
theorem SpineWF.snoc {env : VEnv} {U : Nat} {Γ : List VExpr} {e D C : VExpr} :
    ∀ {es : List VExpr} {A : VExpr}, env.SpineWF U Γ A es (.forallE D C) →
    env.HasType U Γ e D → env.SpineWF U Γ A (es ++ [e]) (C.inst e)
  | [], A, h, he => by
    subst A
    exact ⟨D, C, rfl, he, rfl⟩
  | a :: es, A, ⟨A₁, A₂, hA, ha, hrest⟩, he =>
    ⟨A₁, A₂, hA, ha, SpineWF.snoc hrest he⟩

theorem SpineWF.mono {env env' : VEnv} (henv : env ≤ env') {U : Nat} {Γ : List VExpr} :
    ∀ {es : List VExpr} {A B : VExpr}, env.SpineWF U Γ A es B → env'.SpineWF U Γ A es B
  | [], _, _, h => h
  | _ :: _, _, _, ⟨A₁, A₂, hA, he, hrest⟩ =>
    ⟨A₁, A₂, hA, he.mono henv, SpineWF.mono henv hrest⟩

theorem SpineWF.instL {env : VEnv} {U U' : Nat} {ls : List VLevel}
    (hls : ∀ l ∈ ls, l.WF U') {Γ : List VExpr} :
    ∀ {es : List VExpr} {A B : VExpr}, env.SpineWF U Γ A es B →
    env.SpineWF U' (Γ.map (VExpr.instL ls)) (A.instL ls)
      (es.map (VExpr.instL ls)) (B.instL ls)
  | [], _, _, h => congrArg (VExpr.instL ls) h
  | _ :: es, _, _, ⟨A₁, A₂, rfl, he, hrest⟩ =>
    ⟨A₁.instL ls, A₂.instL ls, rfl, he.instL hls, by
      have := SpineWF.instL hls (es := es) hrest
      rwa [VExpr.instL_instN] at this⟩

theorem SpineWF.weakN {env : VEnv} (henv : env.Ordered) {U n k : Nat} {Γ Γ' : List VExpr}
    (W : Ctx.LiftN n k Γ Γ') :
    ∀ {es : List VExpr} {A B : VExpr}, env.SpineWF U Γ A es B →
    env.SpineWF U Γ' (A.liftN n k) (es.map (VExpr.liftN n · k)) (B.liftN n k)
  | [], _, _, h => congrArg (VExpr.liftN n · k) h
  | _ :: es, _, _, ⟨A₁, A₂, rfl, he, hrest⟩ =>
    ⟨A₁.liftN n k, A₂.liftN n (k+1), rfl, he.weakN henv W, by
      have := SpineWF.weakN henv W (es := es) hrest
      rwa [VExpr.liftN_inst_hi] at this⟩

/-- Retarget a spine judgment along a pi with the same domains: the
result is the iterated instantiation of the new codomain. -/
theorem SpineWF.retarget {env : VEnv} {U : Nat} {Γ : List VExpr} {es : List VExpr} :
    ∀ {Δ : List VExpr} {C B : VExpr}, env.SpineWF U Γ (VExpr.forallN Δ C) es B →
    es.length = Δ.length → ∀ (C' : VExpr),
    env.SpineWF U Γ (VExpr.forallN Δ C') es (VExpr.instRev C' es) := by
  induction es with intro Δ C B h hlen C'
  | nil =>
    obtain rfl : Δ = [] := by
      cases Δ with
      | nil => rfl
      | cons _ _ => simp at hlen
    exact rfl
  | cons e es ih =>
    cases Δ with
    | nil => simp at hlen
    | cons A Δ =>
      obtain ⟨A₁, A₂, hA, he, hrest⟩ := h
      rw [show VExpr.forallN (A :: Δ) C = .forallE A (VExpr.forallN Δ C) from rfl] at hA
      injection hA with h1 h2
      subst h1; subst h2
      have hlen' : es.length = Δ.length := by simpa using hlen
      refine ⟨A, VExpr.forallN Δ C', rfl, he, ?_⟩
      rw [VExpr.instN_forallN] at hrest
      have := ih hrest (by simp [VExpr.instTelN_length, hlen']) (C'.inst e Δ.length)
      show env.SpineWF U Γ ((VExpr.forallN Δ C').inst e) es
        (VExpr.instRev (C'.inst e es.length) es)
      rw [VExpr.instN_forallN, Nat.zero_add, hlen']
      exact this

end VEnv

/-! ## The induction-hypothesis telescope under lifting -/

namespace VInductDecl

/-- `ihsFrom` after the motive-directed lift into the rule context. -/
def ihsR (m k : Nat) : List (Nat × List VExpr) → Nat → List VExpr
  | [], _ => []
  | (j, idxs) :: rs, p =>
    VExpr.appN (.bvar (k + (m + p)))
      ((idxs.map fun e => ((e.liftN 1 j).liftN (m-j+p)).liftN k (m+p)) ++
        [.bvar (m-1-j+p)]) ::
    ihsR m k rs (p+1)

/-- Recursive-field positions are bounded by the field count. -/
theorem recPairs_lt {U : Nat} {T : Name} {np ni : Nat} : ∀ {Bs : List VExpr} {j₀ : Nat},
    ∀ q ∈ recPairs U T np ni Bs j₀, q.1 < j₀ + Bs.length
  | B :: Bs, j₀, q, h => by
    unfold recPairs at h
    split at h
    · rcases List.mem_cons.1 h with rfl | h
      · simp
      · have := recPairs_lt _ h
        simp only [List.length_cons]; omega
    · have := recPairs_lt _ h
      simp only [List.length_cons]; omega

theorem recPairs_ge {U : Nat} {T : Name} {np ni : Nat} : ∀ {Bs : List VExpr} {j₀ : Nat},
    ∀ q ∈ recPairs U T np ni Bs j₀, j₀ ≤ q.1
  | _ :: Bs, j₀, q, h => by
    unfold recPairs at h
    split at h
    · rcases List.mem_cons.1 h with rfl | h
      · exact Nat.le_refl _
      · exact Nat.le_of_succ_le (recPairs_ge _ h)
    · exact Nat.le_of_succ_le (recPairs_ge _ h)

/-- Recursive positions really hold a recursive field, and the recorded
index arguments are its index arguments. -/
theorem recPairs_getElem {U : Nat} {T : Name} {np ni : Nat} : ∀ {Bs : List VExpr} {j₀ : Nat},
    ∀ q ∈ recPairs U T np ni Bs j₀, ∃ B, Bs[q.1 - j₀]? = some B ∧
      isRecField U T np ni q.1 B = true ∧ q.2 = recFieldIdxs np B
  | B :: Bs, j₀, q, h => by
    unfold recPairs at h
    split at h
    · next heq =>
      rcases List.mem_cons.1 h with rfl | h
      · exact ⟨B, by simp, heq, rfl⟩
      · have h1 := recPairs_ge _ h
        obtain ⟨B', hB', hrec, hidx⟩ := recPairs_getElem _ h
        refine ⟨B', ?_, hrec, hidx⟩
        rw [show q.1 - j₀ = (q.1 - (j₀+1)) + 1 from by omega]
        simpa using hB'
    · have h1 := recPairs_ge _ h
      obtain ⟨B', hB', hrec, hidx⟩ := recPairs_getElem _ h
      refine ⟨B', ?_, hrec, hidx⟩
      rw [show q.1 - j₀ = (q.1 - (j₀+1)) + 1 from by omega]
      simpa using hB'

/-- Every analyzed recursive argument names a field within the source
telescope. -/
theorem recArgs_lt {U : Nat} {T : Name} {np ni : Nat} : ∀ {Bs : List VExpr} {j₀ : Nat},
    ∀ r ∈ recArgs U T np ni Bs j₀, r.fieldIndex < j₀ + Bs.length
  | B :: Bs, j₀, r, h => by
    unfold recArgs at h
    split at h
    · next r₀ hr₀ =>
      rcases List.mem_cons.1 h with rfl | h
      · have hj := (recArg?_eq hr₀).1
        simp only [List.length_cons]
        omega
      · have := recArgs_lt _ h
        simp only [List.length_cons]; omega
    · have := recArgs_lt _ h
      simp only [List.length_cons]; omega

/-- Recursive-argument field positions never precede the starting depth. -/
theorem recArgs_ge {U : Nat} {T : Name} {np ni : Nat} : ∀ {Bs : List VExpr} {j₀ : Nat},
    ∀ r ∈ recArgs U T np ni Bs j₀, j₀ ≤ r.fieldIndex
  | _ :: Bs, j₀, r, h => by
    unfold recArgs at h
    split at h
    · next r₀ hr₀ =>
      rcases List.mem_cons.1 h with rfl | h
      · simpa [(recArg?_eq hr₀).1]
      · exact Nat.le_of_succ_le (recArgs_ge _ h)
    · exact Nat.le_of_succ_le (recArgs_ge _ h)

/-- An analyzed recursive argument is backed by the field at its recorded
position, and re-analysis returns the same normalized descriptor. -/
theorem recArgs_getElem {U : Nat} {T : Name} {np ni : Nat} :
    ∀ {Bs : List VExpr} {j₀ : Nat}, ∀ r ∈ recArgs U T np ni Bs j₀,
    ∃ B, Bs[r.fieldIndex - j₀]? = some B ∧
      recArg? U T np ni r.fieldIndex B = some r
  | B :: Bs, j₀, r, h => by
    unfold recArgs at h
    split at h
    · next r₀ hr₀ =>
      rcases List.mem_cons.1 h with rfl | h
      · have hj := (recArg?_eq hr₀).1
        subst hj
        exact ⟨B, by simp, hr₀⟩
      · have hge := recArgs_ge _ h
        obtain ⟨B', hB', hr⟩ := recArgs_getElem _ h
        refine ⟨B', ?_, hr⟩
        rw [show r.fieldIndex - j₀ = (r.fieldIndex - (j₀+1)) + 1 from by omega]
        simpa using hB'
    · have hge := recArgs_ge _ h
      obtain ⟨B', hB', hr⟩ := recArgs_getElem _ h
      refine ⟨B', ?_, hr⟩
      rw [show r.fieldIndex - j₀ = (r.fieldIndex - (j₀+1)) + 1 from by omega]
      simpa using hB'

theorem ihsFrom_liftN (m k : Nat) : ∀ (rs : List (Nat × List VExpr)),
    (∀ q ∈ rs, q.1 < m) → ∀ (p : Nat) (X : VExpr),
    (VExpr.forallN (ihsFrom m rs p) X).liftN k (m + p) =
    VExpr.forallN (ihsR m k rs p) (X.liftN k (m + p + rs.length))
  | [], _, _, _ => rfl
  | (j, idxs) :: rs, hm, p, X => by
    show VExpr.forallE _ _ = VExpr.forallE _ _
    congr 1
    · rw [VExpr.liftN_appN, List.map_append, List.map_map,
        show ((VExpr.bvar (m+p)).liftN k (m+p)) = .bvar (k+(m+p)) from by
          show VExpr.bvar (liftVar k (m+p) (m+p)) = _
          rw [liftVar_le (Nat.le_refl _)],
        show ([VExpr.bvar (m-1-j+p)]).map (VExpr.liftN k · (m+p)) =
            [VExpr.bvar (m-1-j+p)] from by
          show [VExpr.bvar (liftVar k (m-1-j+p) (m+p))] = _
          rw [liftVar_lt (show m-1-j+p < m+p from by
            have := hm _ (List.Mem.head _); simp at this; omega)]]
      rfl
    · rw [show m + p + 1 = m + (p+1) from rfl,
        ihsFrom_liftN m k rs (fun q h => hm q (.tail _ h)) (p+1) X,
        show m + (p+1) + rs.length = m + p + (rs.length+1) from by omega]
      rfl

/-- `ihsFrom_liftN` with the cutoff generalized, for syntactic rewriting. -/
theorem ihsFrom_liftN' (m k : Nat) (rs : List (Nat × List VExpr))
    (hm : ∀ q ∈ rs, q.1 < m) (p : Nat) (X : VExpr) {cut : Nat} (hcut : cut = m + p) :
    (VExpr.forallN (ihsFrom m rs p) X).liftN k cut =
    VExpr.forallN (ihsR m k rs p) (X.liftN k (m + p + rs.length)) := by
  rw [hcut]; exact ihsFrom_liftN m k rs hm p X

theorem ihsR_liftN1 (m k : Nat) : ∀ (rs : List (Nat × List VExpr)) (p c : Nat), c ≤ p →
    (∀ q ∈ rs, q.1 < m) → ∀ (X : VExpr),
    VExpr.forallN (ihsR m k rs (p+1)) (X.liftN 1 (c + rs.length)) =
    (VExpr.forallN (ihsR m k rs p) X).liftN 1 c
  | [], p, c, _, _, X => by simp [ihsR, VExpr.forallN]
  | (j, idxs) :: rs, p, c, hc, hm, X => by
    have hjm : j < m := by have := hm _ (List.Mem.head _); simpa using this
    show VExpr.forallE _ _ = VExpr.forallE _ _
    congr 1
    · rw [VExpr.liftN_appN, List.map_append, List.map_map,
        show ((VExpr.bvar (k+(m+p))).liftN 1 c) = .bvar (k+(m+(p+1))) from by
          show VExpr.bvar (liftVar 1 (k+(m+p)) c) = _
          rw [liftVar_le (by omega)]
          congr 1; omega,
        show ([VExpr.bvar (m-1-j+p)]).map (VExpr.liftN 1 · c) =
            [VExpr.bvar (m-1-j+(p+1))] from by
          show [VExpr.bvar (liftVar 1 (m-1-j+p) c)] = _
          rw [liftVar_le (by omega)]
          congr 2; omega]
      refine congrArg (VExpr.appN _) (congrArg (· ++ [VExpr.bvar (m-1-j+(p+1))]) ?_)
      refine List.map_congr_left fun e _ => .symm ?_
      show (((e.liftN 1 j).liftN (m-j+p)).liftN k (m+p)).liftN 1 c = _
      rw [VExpr.liftN_liftN_comm _ 1 k c (m+p) (by omega),
        show ((e.liftN 1 j).liftN (m-j+p)).liftN 1 c =
          (e.liftN 1 j).liftN (m-j+(p+1)) from by
          rw [VExpr.liftN'_liftN' (Nat.zero_le _) (by omega)]
          rfl]
      rfl
    · rw [show c + ((j, idxs) :: rs).length = (c+1) + rs.length from by simp; omega]
      exact ihsR_liftN1 m k rs (p+1) (c+1) (by omega) (fun q h => hm q (.tail _ h)) X

theorem ihsFrom_length (m : Nat) : ∀ (rs : List (Nat × List VExpr)) (p : Nat),
    (ihsFrom m rs p).length = rs.length
  | [], _ => rfl
  | (_, _) :: rs, p => by simp [ihsFrom, ihsFrom_length m rs (p+1)]

theorem ihsFromRecArgs_length (m : Nat) : ∀ (rs : List RecArg) (p : Nat),
    (ihsFromRecArgs m rs p).length = rs.length
  | [], _ => rfl
  | _ :: rs, p => by simp [ihsFromRecArgs, ihsFromRecArgs_length m rs (p+1)]

theorem minorTypes_length (U : Nat) (T : Name) (np : Nat) (ty : VInductiveType) :
    ∀ (cs : List VConstVal) (i : Nat), (minorTypes U T np ty cs i).length = cs.length
  | [], _ => rfl
  | _ :: cs, i => by simp [minorTypes, minorTypes_length U T np ty cs (i+1)]

theorem minorTypesRec_length (U : Nat) (T : Name) (np : Nat) (ty : VInductiveType) :
    ∀ (cs : List VConstVal) (i : Nat), (minorTypesRec U T np ty cs i).length = cs.length
  | [], _ => rfl
  | _ :: cs, i => by
    simp [minorTypesRec, minorTypesRec_length U T np ty cs (i+1)]

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

/-- The transported type of an analyzed recursive field is exactly its
generated functional-IH domain telescope followed by the transported family
target. -/
theorem recArg_minor_fieldType {U : Nat} {T : Name} {np ni : Nat}
    {B : VExpr} {r₀ : RecArg}
    (hr : recArg? U T np ni r₀.fieldIndex B = some r₀)
    (m p : Nat) (hj : r₀.fieldIndex < m) :
    let r := r₀.instL (VLevel.params' U 1)
    ((B.instL (VLevel.params' U 1)).liftN 1 r.fieldIndex).liftN
        (m-r.fieldIndex+p) =
      VExpr.forallN (r.minorBinders m p)
        (VExpr.appN (.const T (VLevel.params' U 1))
          (VExpr.bvarRevRange (m+p+r.binders.length+1) np ++
            r.indices.map fun e =>
              (e.liftN 1 (r.fieldIndex+r.binders.length)).liftN
                (m-r.fieldIndex+p) r.binders.length)) := by
  dsimp only
  obtain ⟨-, -, hB, -, -, -⟩ := recArg?_eq hr
  conv => lhs; rw [hB]
  simp only [RecArg.instL, VExpr.instL_forallN, VExpr.instL_appN,
    List.map_append, bvarRevRange_instL,
    show (VExpr.const T (VLevel.params U)).instL (VLevel.params' U 1) =
      .const T (VLevel.params' U 1) from by
        simp [VExpr.instL, VLevel.params_map_inst_params'],
    VExpr.liftN_forallN, VExpr.liftN_appN]
  simp only [List.length_map, VExpr.liftTelN_length, Nat.zero_add]
  rw [bvarRevRange_liftN_ge _ _ _ _ (Nat.le_refl _),
    bvarRevRange_liftN_ge _ _ _ _ (by omega),
    show
      m - r₀.fieldIndex + p + (1 + (r₀.fieldIndex + r₀.binders.length)) =
        m + p + r₀.binders.length + 1 from by omega]
  simp only [List.map_map, RecArg.minorBinders]
  apply congrArg (VExpr.forallN _)
  apply congrArg (VExpr.appN (.const T (VLevel.params' U 1)))
  apply congrArg (VExpr.bvarRevRange (m + p + r₀.binders.length + 1) np ++ ·)
  apply List.map_congr_left
  intro e _
  simp only [Function.comp_apply]

/-- Rule-context analogue of `recArg_minor_fieldType`: transport a recursive
field beneath the motive and all constructor minors, then beneath the later
constructor fields. -/
theorem recArg_rule_fieldType {U : Nat} {T : Name} {np ni : Nat}
    {B : VExpr} {r₀ : RecArg}
    (hr : recArg? U T np ni r₀.fieldIndex B = some r₀)
    (m k : Nat) (hj : r₀.fieldIndex < m) :
    let r := r₀.instL (VLevel.params' U 1)
    ((B.instL (VLevel.params' U 1)).liftN (k+1) r.fieldIndex).liftN
        (m-r.fieldIndex) =
      VExpr.forallN (r.ruleBinders m k)
        (VExpr.appN (.const T (VLevel.params' U 1))
          (VExpr.bvarRevRange (m+k+r.binders.length+1) np ++
            r.indices.map fun e =>
              (e.liftN (k+1) (r.fieldIndex+r.binders.length)).liftN
                (m-r.fieldIndex) r.binders.length)) := by
  dsimp only
  obtain ⟨-, -, hB, -, -, -⟩ := recArg?_eq hr
  conv => lhs; rw [hB]
  simp only [RecArg.instL, VExpr.instL_forallN, VExpr.instL_appN,
    List.map_append, bvarRevRange_instL,
    show (VExpr.const T (VLevel.params U)).instL (VLevel.params' U 1) =
      .const T (VLevel.params' U 1) from by
        simp [VExpr.instL, VLevel.params_map_inst_params'],
    VExpr.liftN_forallN, VExpr.liftN_appN]
  simp only [List.length_map, VExpr.liftTelN_length, Nat.zero_add]
  rw [bvarRevRange_liftN_ge _ _ _ _ (Nat.le_refl _),
    bvarRevRange_liftN_ge _ _ _ _ (by omega),
    show m - r₀.fieldIndex + (k + 1 + (r₀.fieldIndex + r₀.binders.length)) =
      m + k + r₀.binders.length + 1 from by omega]
  simp only [List.map_map, RecArg.ruleBinders]
  apply congrArg (VExpr.forallN _)
  apply congrArg (VExpr.appN (.const T (VLevel.params' U 1)))
  apply congrArg (VExpr.bvarRevRange (m+k+r₀.binders.length+1) np ++ ·)
  apply List.map_congr_left
  intro e _
  simp only [Function.comp_apply]

theorem RecArg.minorBinders_shift (r : RecArg) (m p : Nat) :
    r.minorBinders m p =
      VExpr.liftTelN p (r.minorBinders m 0) 0 := by
  simp only [RecArg.minorBinders, Nat.add_zero]
  rw [VExpr.liftTelN_liftTelN]

/-- The `p` parameter of a minor IH is exactly weakening over the `p`
previous IH binders. -/
theorem RecArg.minorIH_shift (r : RecArg) (m p : Nat)
    (hj : r.fieldIndex < m) :
    r.minorIH m p = (r.minorIH m 0).liftN p := by
  simp only [RecArg.minorIH, VExpr.liftN_forallN, VExpr.liftTelN_length]
  rw [← r.minorBinders_shift m p]
  rw [show (r.minorBinders m 0).length = r.binders.length by
    simp [RecArg.minorBinders, VExpr.liftTelN_length], Nat.zero_add]
  apply congrArg (VExpr.forallN _)
  rw [VExpr.liftN_appN, List.map_append, List.map_map]
  show VExpr.appN _ (_ ++ [_]) = VExpr.appN _ (_ ++ [_])
  congr 1
  · rw [show (VExpr.bvar (m + 0 + r.binders.length)).liftN
        p r.binders.length = .bvar (m+p+r.binders.length) from by
      simp only [VExpr.liftN]
      rw [liftVar_le (by omega)]
      congr 1
      omega]
  · congr 1
    · apply List.map_congr_left
      intro e _
      simp only [Function.comp_apply, Nat.add_zero]
      rw [VExpr.liftN'_liftN_hi]
    · congr 1
      simp only [Function.comp_apply, Nat.add_zero, VExpr.liftN_appN]
      rw [show (VExpr.bvar (m - 1 - r.fieldIndex + r.binders.length)).liftN
          p r.binders.length =
          .bvar (m - 1 - r.fieldIndex + p + r.binders.length) from by
        simp only [VExpr.liftN]
        rw [liftVar_le (by omega)]
        congr 1
        omega,
        VExpr.bvarRevRange_liftN_high _ _ _ _ (by omega)]

/-- Lifting a base minor-IH through the constructor-minor stack produces the
normal form expected of the corresponding recursive call in an iota rule. -/
theorem RecArg.minorIH_zero_lift_ruleIH (r : RecArg) (m k : Nat)
    (hj : r.fieldIndex < m) :
    (r.minorIH m 0).liftN k m = r.ruleIH m k := by
  simp only [RecArg.minorIH, RecArg.ruleIH, VExpr.liftN_forallN,
    VExpr.liftTelN_length, RecArg.minorBinders, RecArg.ruleBinders, Nat.add_zero]
  congr 1
  · rw [show m = r.fieldIndex + (m-r.fieldIndex) from by omega]
    rw [show r.fieldIndex + (m-r.fieldIndex) - r.fieldIndex =
      m-r.fieldIndex from by omega]
    rw [VExpr.liftTelN_liftN_mid r.binders k (m-r.fieldIndex) (Nat.zero_le _)]
  · congr 1
    rw [VExpr.liftN_appN, List.map_append, List.map_map]
    show VExpr.appN _ (_ ++ [_]) = VExpr.appN _ (_ ++ [_])
    congr 1
    · simp only [VExpr.liftN]
      rw [liftVar_le (Nat.le_refl _)]
      congr 1
      omega
    · congr 1
      · apply List.map_congr_left
        intro e _
        simp only [Function.comp_apply]
        rw [show m + r.binders.length =
            (r.fieldIndex + r.binders.length) + (m-r.fieldIndex) from by omega,
          VExpr.liftN_liftN_mid e k (m-r.fieldIndex) (by omega)]
      · congr 1
        simp only [Function.comp_apply, VExpr.liftN_appN]
        rw [show (VExpr.bvar (m - 1 - r.fieldIndex + r.binders.length)).liftN
            k (m + r.binders.length) =
            .bvar (m - 1 - r.fieldIndex + r.binders.length) from by
              simp only [VExpr.liftN]
              rw [liftVar_lt (by omega)],
          VExpr.bvarRevRange_liftN_high _ _ _ _ (by omega)]

/-- General normalization for a minor-IH already shifted past `p` earlier IH
binders. In rule context it is the base `ruleIH`, weakened by the same `p`. -/
theorem RecArg.minorIH_lift_ruleIH (r : RecArg) (m k p : Nat)
    (hj : r.fieldIndex < m) :
    (r.minorIH m p).liftN k (m+p) = (r.ruleIH m k).liftN p := by
  rw [r.minorIH_shift m p hj]
  rw [← VExpr.liftN_liftN_comm (r.minorIH m 0) p k 0 m (Nat.zero_le _)]
  rw [r.minorIH_zero_lift_ruleIH m k hj]

theorem ruleIHs_length (m k : Nat) : ∀ (rs : List RecArg) (p : Nat),
    (ruleIHs m k rs p).length = rs.length
  | [], _ => rfl
  | _ :: rs, p => by simp [ruleIHs, ruleIHs_length m k rs (p+1)]

/-- Lifting the generalized minor-IH telescope into a rule context normalizes
each entry to `ruleIHs`; this is the list form of
`RecArg.minorIH_lift_ruleIH`. -/
theorem ihsFromRecArgs_liftN (m k : Nat) : ∀ (rs : List RecArg),
    (∀ r ∈ rs, r.fieldIndex < m) → ∀ (p : Nat) (X : VExpr),
    (VExpr.forallN (ihsFromRecArgs m rs p) X).liftN k (m+p) =
      VExpr.forallN (ruleIHs m k rs p) (X.liftN k (m+p+rs.length))
  | [], _, _, _ => rfl
  | r :: rs, hm, p, X => by
    show VExpr.forallE _ _ = VExpr.forallE _ _
    congr 1
    · exact r.minorIH_lift_ruleIH m k p (hm r (.head _))
    · rw [show m+p+1 = m+(p+1) from by omega,
        ihsFromRecArgs_liftN m k rs (fun q hq => hm q (.tail _ hq)) (p+1) X,
        show m+(p+1)+rs.length = m+p+((r :: rs).length) from by simp; omega]

theorem ihsFromRecArgs_liftN' (m k : Nat) (rs : List RecArg)
    (hm : ∀ r ∈ rs, r.fieldIndex < m) (p : Nat) (X : VExpr)
    {cut : Nat} (hcut : cut = m+p) :
    (VExpr.forallN (ihsFromRecArgs m rs p) X).liftN k cut =
      VExpr.forallN (ruleIHs m k rs p) (X.liftN k (m+p+rs.length)) := by
  rw [hcut]
  exact ihsFromRecArgs_liftN m k rs hm p X

/-- Weakening a normalized functional-IH telescope by one binder is the same
as incrementing its starting depth. -/
theorem ruleIHs_liftN1 (m k : Nat) : ∀ (rs : List RecArg) (p c : Nat), c ≤ p →
    ∀ (X : VExpr),
    VExpr.forallN (ruleIHs m k rs (p+1)) (X.liftN 1 (c+rs.length)) =
      (VExpr.forallN (ruleIHs m k rs p) X).liftN 1 c
  | [], p, c, _, X => by simp [ruleIHs, VExpr.forallN]
  | r :: rs, p, c, hc, X => by
    show VExpr.forallE _ _ = VExpr.forallE _ _
    congr 1
    · rw [VExpr.liftN'_liftN' (Nat.zero_le _) hc]
    · rw [show c+(r :: rs).length = (c+1)+rs.length from by simp; omega]
      exact ruleIHs_liftN1 m k rs (p+1) (c+1) (by omega) X

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

theorem ihsFrom_levelWF {Uv : Nat} {m : Nat} : ∀ (rs : List (Nat × List VExpr)) (p : Nat),
    (∀ q ∈ rs, ∀ e ∈ q.2, e.LevelWF Uv) → ∀ e ∈ ihsFrom m rs p, e.LevelWF Uv
  | (j, idxs) :: rs, p, hidx, e, h => by
    rcases List.mem_cons.1 h with rfl | h
    · refine VExpr.LevelWF.appN (f := .bvar (m+p)) trivial fun e he => ?_
      rcases List.mem_append.1 he with he | he
      · obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.1 he
        exact ((hidx _ (List.Mem.head _) e₀ he₀).liftN).liftN
      · rcases List.mem_cons.1 he with rfl | he
        · trivial
        · cases he
    · exact ihsFrom_levelWF rs (p+1) (fun q hq => hidx q (.tail _ hq)) e h

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

end VInductDecl

namespace VExpr

theorem forallN_telN_dropN : ∀ (n : Nat) (e : VExpr),
    forallN (telN n e) (dropN n e) = e
  | 0, _ => rfl
  | n+1, .forallE A rest => congrArg (VExpr.forallE A) (forallN_telN_dropN n rest)
  | _+1, .bvar _ | _+1, .sort _ | _+1, .const _ _ | _+1, .app _ _ | _+1, .lam _ _ => rfl

theorem resultOf_forallN : ∀ (As : List VExpr) (B : VExpr),
    resultOf (forallN As B) = resultOf B
  | [], _ => rfl
  | _ :: As, B => resultOf_forallN As B

theorem resultOf_appN_app (f a : VExpr) :
    ∀ es, resultOf ((f.app a).appN es) = (f.app a).appN es
  | [] => rfl
  | b :: bs => resultOf_appN_app (f.app a) b bs

theorem resultOf_appN_const (T : Name) (ls : List VLevel) :
    ∀ es, resultOf ((VExpr.const T ls).appN es) =
      (VExpr.const T ls).appN es
  | [] => rfl
  | a :: as => resultOf_appN_app (VExpr.const T ls) a as

end VExpr

namespace VEnv

theorem OnTel.mono {env env' : VEnv} {U : Nat} (henv : env ≤ env') :
    ∀ {As Γ}, OnTel env U Γ As → OnTel env' U Γ As
  | [], _, _ => trivial
  | _ :: _, _, ⟨hA, hT⟩ => ⟨hA.mono henv, OnTel.mono henv hT⟩

/-- A well-formed telescope is pointwise definitionally equal to itself. -/
theorem OnTel.telDefEq_refl {env : VEnv} {U : Nat} :
    ∀ {Γ As}, OnTel env U Γ As → TelDefEq env U Γ As As
  | _, [], _ => trivial
  | _, _ :: _, ⟨⟨u, hA⟩, hT⟩ =>
    ⟨⟨u, hA⟩, OnTel.telDefEq_refl hT⟩

/-- A structural telescope equality has equal arity. -/
theorem TelDefEq.length_eq {env : VEnv} {U : Nat} :
    ∀ {Γ As As'}, TelDefEq env U Γ As As' → As.length = As'.length
  | _, [], [], _ => rfl
  | _, _ :: _, _ :: _, ⟨_, hT⟩ =>
    congrArg Nat.succ (TelDefEq.length_eq hT)

/-- The raw side of a structural telescope equality is a well-formed
telescope. -/
theorem TelDefEq.raw_onTel {env : VEnv} {U : Nat} :
    ∀ {Γ As As'}, TelDefEq env U Γ As As' → OnTel env U Γ As
  | _, [], [], _ => trivial
  | _, _ :: _, _ :: _, ⟨⟨_, hA⟩, hT⟩ =>
    ⟨⟨_, hA.hasType.1⟩, TelDefEq.raw_onTel hT⟩

/-- Structural telescope equality is monotone in the environment. -/
theorem TelDefEq.mono {env env' : VEnv} {U : Nat} (henv : env ≤ env') :
    ∀ {Γ As As'}, TelDefEq env U Γ As As' → TelDefEq env' U Γ As As'
  | _, [], [], _ => trivial
  | _, _ :: _, _ :: _, ⟨⟨u, hA⟩, hT⟩ =>
    ⟨⟨u, hA.mono henv⟩, TelDefEq.mono henv hT⟩

/-- Instantiate every universe in a structural telescope equality. -/
theorem TelDefEq.instL {env : VEnv} {U U' : Nat} {ls : List VLevel}
    (hls : ∀ l ∈ ls, l.WF U') :
    ∀ {Γ As As'}, TelDefEq env U Γ As As' →
      TelDefEq env U' (Γ.map (VExpr.instL ls))
        (As.map (VExpr.instL ls)) (As'.map (VExpr.instL ls))
  | _, [], [], _ => trivial
  | _, _ :: As, _ :: As', ⟨⟨u, hA⟩, hT⟩ => by
    refine ⟨⟨u.inst ls, hA.instL hls⟩, ?_⟩
    simpa using TelDefEq.instL hls hT

/-- Extend an existing definitionally equal context by a structurally equal
raw/view telescope. -/
theorem TelDefEq.extendCtx {env : VEnv} {U : Nat} {Γ₀ : List VExpr} :
    ∀ {Γ Γ' As As'}, IsDefEqCtx env U Γ₀ Γ Γ' →
      TelDefEq env U Γ As As' →
      IsDefEqCtx env U Γ₀ (As.reverse ++ Γ) (As'.reverse ++ Γ')
  | Γ, Γ', [], [], hΓ, _ => by simpa using hΓ
  | Γ, Γ', _ :: As, _ :: As', hΓ, ⟨⟨_, hA⟩, hT⟩ => by
    simpa [List.reverse_cons, List.append_assoc] using
      TelDefEq.extendCtx (.succ hΓ hA) hT

/-- The completed raw and view contexts of a structural telescope equality
are definitionally equal over their common prefix. -/
theorem TelDefEq.ctx {env : VEnv} {U : Nat} {Γ As As' : List VExpr}
    (h : TelDefEq env U Γ As As') :
    IsDefEqCtx env U Γ (As.reverse ++ Γ) (As'.reverse ++ Γ) :=
  h.extendCtx .zero

/-- Any aligned prefix remains a structural telescope equality. -/
theorem TelDefEq.take {env : VEnv} {U : Nat} :
    ∀ (n : Nat) {Γ As As'}, TelDefEq env U Γ As As' →
      TelDefEq env U Γ (As.take n) (As'.take n)
  | 0, _, _, _, _ => trivial
  | _ + 1, _, [], [], _ => trivial
  | n + 1, _, _ :: _, _ :: _, ⟨hA, hT⟩ =>
    ⟨hA, TelDefEq.take n hT⟩

/-- Drop an aligned prefix, retaining the exact raw context accumulated by
the removed binders. -/
theorem TelDefEq.drop {env : VEnv} {U : Nat} :
    ∀ (n : Nat) {Γ As As'}, TelDefEq env U Γ As As' →
      TelDefEq env U ((As.take n).reverse ++ Γ)
        (As.drop n) (As'.drop n)
  | 0, _, _, _, h => by simpa using h
  | _ + 1, _, [], [], _ => trivial
  | n + 1, Γ, A :: As, _ :: As', ⟨_, hT⟩ => by
    have h := TelDefEq.drop n hT
    simpa [List.take_succ_cons, List.drop_succ_cons,
      List.reverse_cons, List.append_assoc] using h

/-- Recover the pointwise equality at one aligned binder position together
with its exact preceding raw context. -/
theorem TelDefEq.getElem? {env : VEnv} {U : Nat} :
    ∀ {Γ As As'}, TelDefEq env U Γ As As' →
      ∀ {n A A'}, As[n]? = some A → As'[n]? = some A' →
        ∃ u, env.IsDefEq U ((As.take n).reverse ++ Γ) A A' (.sort u)
  | _, [], [], _, n, _, _, hA, _ => by simp at hA
  | Γ, _ :: As, _ :: As', ⟨hhead, htail⟩, 0, A, A', hA, hA' => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hA hA'
    subst A
    subst A'
    simpa using hhead
  | Γ, A₀ :: As, A₀' :: As', ⟨_, htail⟩, n + 1, A, A', hA, hA' => by
    simp only [List.getElem?_cons_succ] at hA hA'
    have h := TelDefEq.getElem? htail hA hA'
    simpa [List.take_succ_cons, List.reverse_cons, List.append_assoc] using h

/-- Weakening preserves structural telescope equality and shifts both
surfaces at their binder-relative cutoffs. -/
theorem TelDefEq.weakN {env : VEnv} {U n : Nat} (ord : env.Ordered)
    {Γ Γ' : List VExpr} {k : Nat} (W : Ctx.LiftN n k Γ Γ') :
    ∀ {As As'}, TelDefEq env U Γ As As' →
      TelDefEq env U Γ'
        (VExpr.liftTelN n As k) (VExpr.liftTelN n As' k)
  | [], [], _ => trivial
  | _ :: As, _ :: As', ⟨⟨u, hA⟩, hT⟩ => by
    refine ⟨⟨u, hA.weakN ord W⟩, ?_⟩
    simpa [VExpr.liftTelN] using TelDefEq.weakN ord W.succ hT

/-- Substitute one typed term through a structural telescope equality. -/
theorem TelDefEq.instN {env : VEnv} {U : Nat} (ord : env.Ordered)
    {Γ₀ : List VExpr} {e₀ A₀ : VExpr}
    (h₀ : env.HasType U Γ₀ e₀ A₀) {k : Nat} {Γ₁ Γ : List VExpr}
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) :
    ∀ {As As'}, TelDefEq env U Γ₁ As As' →
      TelDefEq env U Γ
        (VExpr.instTelN e₀ As k) (VExpr.instTelN e₀ As' k)
  | [], [], _ => trivial
  | _ :: As, _ :: As', ⟨⟨u, hA⟩, hT⟩ => by
    refine ⟨⟨u, by simpa using hA.instN ord h₀ W⟩, ?_⟩
    simpa [VExpr.instTelN] using
      TelDefEq.instN ord h₀ W.succ hT

/-- Pointwise telescope equality extends to the corresponding iterated Pi
types once their terminal bodies are definitionally equal in the completed
raw context. This is the construction-side counterpart of `spine_sort`; it
does not require Pi injectivity. -/
theorem TelDefEq.forallN_defeq {env : VEnv} {U : Nat} :
    ∀ {Γ As As' C C' u},
      TelDefEq env U Γ As As' →
      env.IsDefEq U (As.reverse ++ Γ) C C' (.sort u) →
      ∃ v, env.IsDefEq U Γ
        (VExpr.forallN As C) (VExpr.forallN As' C') (.sort v)
  | _, [], [], _, _, u, _, hC => ⟨u, hC⟩
  | Γ, A :: As, A' :: As', C, C', u,
      ⟨⟨uA, hA⟩, hT⟩, hC => by
    have hC' : env.IsDefEq U (As.reverse ++ A :: Γ)
        C C' (.sort u) := by
      simpa [List.reverse_cons, List.append_assoc] using hC
    obtain ⟨v, hbody⟩ :=
      TelDefEq.forallN_defeq hT hC'
    exact ⟨.imax uA v, .forallEDF hA hbody⟩

/-- A fully applied spine accepted by the view telescope is also accepted by
the raw telescope. This is the substitution-aware consumer of `TelDefEq`;
it avoids any appeal to whole-Pi injectivity. -/
theorem TelDefEq.spine_sort {env : VEnv} {U : Nat} (ord : env.Ordered) :
    ∀ {Γ As As' es l}, TelDefEq env U Γ As As' →
      env.SpineWF U Γ (VExpr.forallN As' (.sort l)) es (.sort l) →
      es.length = As.length →
      env.SpineWF U Γ (VExpr.forallN As (.sort l)) es (.sort l)
  | _, [], [], [], _, _, hsp, _ => by simpa using hsp
  | _, [], [], _ :: _, _, _, _, hlen => by simp at hlen
  | Γ, A :: As, A' :: As', e :: es, l, ⟨⟨_, hA⟩, hT⟩,
      ⟨D, C, hshape, he, hrest⟩, hlen => by
    change VExpr.forallE A' (VExpr.forallN As' (.sort l)) =
      VExpr.forallE D C at hshape
    injection hshape with hD hC
    subst D
    subst C
    have heRaw : env.HasType U Γ e A := hA.defeq' he
    have hTinst := TelDefEq.instN ord heRaw (.zero) hT
    have hrest' : env.SpineWF U Γ
        (VExpr.forallN (VExpr.instTelN e As' 0) (.sort l))
        es (.sort l) := by
      simpa [VExpr.instN_forallN] using hrest
    have hlen' : es.length = As.length := by simpa using hlen
    have hlenInst :
        es.length = (VExpr.instTelN e As 0).length := by
      rw [VExpr.instTelN_length]
      exact hlen'
    have hout := TelDefEq.spine_sort ord hTinst hrest' hlenInst
    refine ⟨A, VExpr.forallN As (.sort l), rfl, heRaw, ?_⟩
    simpa [VExpr.instN_forallN] using hout

/-- Extend a definitionally equal context by the same well-formed telescope
on both sides. -/
theorem OnTel.extendDefEqCtx {env : VEnv} {U : Nat} {Γ₀ Γ₁ Γ₂ : List VExpr}
    (hΓ : IsDefEqCtx env U Γ₀ Γ₁ Γ₂) :
    ∀ {As}, OnTel env U Γ₁ As →
      IsDefEqCtx env U Γ₀ (As.reverse ++ Γ₁) (As.reverse ++ Γ₂)
  | [], _ => by simpa using hΓ
  | _ :: As, ⟨⟨_, hA⟩, hT⟩ => by
    simpa [List.reverse_cons, List.append_assoc] using
      OnTel.extendDefEqCtx (.succ hΓ hA) hT

/-- Transport a telescope across definitionally equal base contexts. -/
theorem OnTel.defeqDFC {env : VEnv} {U : Nat} (ord : env.Ordered)
    {Γ₀ Γ₁ Γ₂ : List VExpr} (hΓ : IsDefEqCtx env U Γ₀ Γ₁ Γ₂) :
    ∀ {As}, OnTel env U Γ₁ As → OnTel env U Γ₂ As
  | [], _ => trivial
  | _ :: As, ⟨hA, hT⟩ => by
    obtain ⟨u, hAt⟩ := hA
    exact ⟨⟨u, hAt.defeqDFC ord hΓ⟩,
      OnTel.defeqDFC ord (.succ hΓ hAt) hT⟩

/-- Transport application-spine typing across definitionally equal
contexts. -/
theorem SpineWF.defeqDFC {env : VEnv} {U : Nat} (ord : env.Ordered)
    {Γ₀ Γ₁ Γ₂ : List VExpr} (hΓ : IsDefEqCtx env U Γ₀ Γ₁ Γ₂) :
    ∀ {A es B}, SpineWF env U Γ₁ A es B → SpineWF env U Γ₂ A es B
  | _, [], _, h => h
  | _, _ :: _, _, ⟨A₁, A₂, hA, he, hT⟩ =>
    ⟨A₁, A₂, hA, he.defeqDFC ord hΓ,
      SpineWF.defeqDFC ord hΓ hT⟩

/--
info: 'Lean4Lean.VEnv.TelDefEq.raw_onTel' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms TelDefEq.raw_onTel

/--
info: 'Lean4Lean.VEnv.TelDefEq.instL' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms TelDefEq.instL

/--
info: 'Lean4Lean.VEnv.TelDefEq.ctx' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms TelDefEq.ctx

end VEnv

namespace VInductDecl
open VEnv

/-- The exact raw family telescope accepted for generation is well formed in
the pre-environment. -/
theorem GenerationChecked.WF.rawFamily_onTel {source : VInductDecl}
    {gen : GenerationChecked source} {env : VEnv} (h : gen.WF env) :
    env.OnTel source.uvars []
      (gen.block.rawParams ++ gen.block.rawIndices) :=
  h.familyTel.raw_onTel

/-- The granular family telescope/result contract proves that the stored raw
family constant can be inserted without appealing to whole-`forall`
injectivity. -/
theorem GenerationChecked.WF.rawFamily_isType {source : VInductDecl}
    {gen : GenerationChecked source} {env : VEnv} (h : gen.WF env) :
    env.IsType source.uvars [] gen.block.sourceType.type := by
  rw [← VExpr.forallN_telN_dropN source.nparams gen.block.sourceType.type,
    ← forallN_ctorFields_resultOf
      (VExpr.dropN source.nparams gen.block.sourceType.type),
    ← VExpr.forallN_append]
  have hresult₀ : env.IsType source.uvars
      (gen.block.rawParams ++ gen.block.rawIndices).reverse
      gen.block.rawResult :=
    ⟨_, h.familyResult.hasType.1⟩
  have hresult : env.IsType source.uvars
      ((gen.block.rawParams ++ gen.block.rawIndices).reverse ++ [])
      gen.block.rawResult := by
    simpa using hresult₀
  have hout := IsType.forallN h.rawFamily_onTel hresult
  simpa [NormalizedChecked.rawParams, NormalizedChecked.rawIndices,
    NormalizedChecked.rawResult] using hout

/-- The exact raw telescope stored in a paired constructor is well formed in
the post-family environment. -/
theorem NormalizedCtor.WF.rawDeclared_onTel {source : VInductDecl}
    {block : NormalizedChecked source} {ctor : NormalizedCtor} {env : VEnv}
    (h : ctor.WF block env) :
    env.OnTel source.uvars [] (ctor.declaredBinders source.nparams) :=
  h.declaredTel.raw_onTel

/-- The granular constructor telescope/result contract proves that the exact
stored raw constructor can be inserted. -/
theorem NormalizedCtor.WF.rawDeclared_isType {source : VInductDecl}
    {block : NormalizedChecked source} {ctor : NormalizedCtor} {env : VEnv}
    (h : ctor.WF block env) :
    env.IsType source.uvars [] ctor.raw.type := by
  rw [← VExpr.forallN_telN_dropN source.nparams ctor.raw.type,
    ← forallN_ctorFields_resultOf (VExpr.dropN source.nparams ctor.raw.type),
    ← VExpr.forallN_append]
  have hresult₀ : env.IsType source.uvars
      (ctor.declaredBinders source.nparams).reverse
      (ctor.rawResult source.nparams) :=
    ⟨_, h.declaredResult.hasType.1⟩
  have hresult : env.IsType source.uvars
      ((ctor.declaredBinders source.nparams).reverse ++ [])
      (ctor.rawResult source.nparams) := by
    simpa using hresult₀
  have hout := IsType.forallN h.rawDeclared_onTel hresult
  simpa [NormalizedCtor.declaredBinders, NormalizedCtor.rawFields,
    NormalizedCtor.rawResult] using hout

/-- The raw family/field telescope actually emitted in mixed artifacts is
well formed independently of the constructor's stored parameter surface. -/
theorem NormalizedCtor.WF.rawEmitted_onTel {source : VInductDecl}
    {block : NormalizedChecked source} {ctor : NormalizedCtor} {env : VEnv}
    (h : ctor.WF block env) :
    env.OnTel source.uvars [] (ctor.emittedBinders block) :=
  h.emittedTel.raw_onTel

/-- A granular constructor certificate is monotone after its staged family
insertion. -/
theorem NormalizedCtor.WF.mono {source : VInductDecl}
    {block : NormalizedChecked source} {ctor : NormalizedCtor}
    {env env' : VEnv} (henv : env ≤ env') (h : ctor.WF block env) :
    ctor.WF block env' where
  declaredTel := h.declaredTel.mono henv
  declaredResult := h.declaredResult.mono henv
  emittedTel := h.emittedTel.mono henv
  emittedResult := h.emittedResult.mono henv

/-- Retrieve the insertion-ready proof for any paired raw constructor in the
precise post-family environment named by the block certificate. -/
theorem GenerationChecked.WF.rawCtor_isType {source : VInductDecl}
    {gen : GenerationChecked source} {env envT : VEnv} (h : gen.WF env)
    (hadd : env.addConst gen.block.sourceType.name
      gen.block.sourceType.toVConstant = some envT)
    {ctor : NormalizedCtor} (hctor : ctor ∈ gen.block.ctorPairs) :
    envT.IsType source.uvars [] ctor.raw.type :=
  (h.ctors envT hadd ctor hctor).rawDeclared_isType

/--
info: 'Lean4Lean.VInductDecl.GenerationChecked.WF.rawFamily_isType' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms GenerationChecked.WF.rawFamily_isType

/--
info: 'Lean4Lean.VInductDecl.GenerationChecked.WF.rawCtor_isType' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms GenerationChecked.WF.rawCtor_isType

theorem RecArg.WF.mono {env env' : VEnv} {U : Nat} {l : VLevel}
    {Is Γ : List VExpr} {r : RecArg} (henv : env ≤ env')
    (h : r.WF U env l Is Γ) : r.WF U env' l Is Γ :=
  ⟨h.1.mono henv, h.2.mono henv⟩

/-- Transport recursive-argument evidence across definitionally equal base
contexts. The private binder telescope is transported first, then the
terminal family-index spine is transported beneath that same telescope. -/
theorem RecArg.WF.defeqDFC {env : VEnv} {U : Nat} {l : VLevel}
    {Is Γ₀ Γ₁ Γ₂ : List VExpr} {r : RecArg} (ord : env.Ordered)
    (hΓ : env.IsDefEqCtx U Γ₀ Γ₁ Γ₂)
    (h : r.WF U env l Is Γ₁) : r.WF U env l Is Γ₂ := by
  have htel := h.1.defeqDFC ord hΓ
  have hctx := h.1.extendDefEqCtx hΓ
  exact ⟨htel, h.2.defeqDFC ord hctx⟩

theorem fieldsWF_mono {U : Nat} {T : Name} {np : Nat} {env env' : VEnv} {l : VLevel}
    {Is : List VExpr} (henv : env ≤ env') : ∀ {Γ j Bs},
    fieldsWF U T np env l Is Γ j Bs → fieldsWF U T np env' l Is Γ j Bs
  | _, _, [], _ => trivial
  | _, _, _ :: _, ⟨hB, hSp, hT⟩ => by
    refine ⟨?_, fun hrec => (hSp hrec).mono henv, fieldsWF_mono henv hT⟩
    rcases hB with hrec | hfun | ⟨hnone, u, h, hl⟩
    · exact .inl hrec
    · obtain ⟨r, hr, hne, hwf⟩ := hfun
      exact .inr (.inl ⟨r, hr, hne, hwf.mono henv⟩)
    · exact .inr (.inr ⟨hnone, u, h.mono henv, hl⟩)

/-- The checked-view semantic certificate is monotone in the environment. -/
theorem Checked.WF.mono {decl : VInductDecl} {checked : decl.Checked}
    {env env' : VEnv} (henv : env ≤ env') (h : checked.WF env) :
    checked.WF env' := by
  unfold Checked.WF at h ⊢
  refine ⟨h.1.mono henv, fun c hc => ?_⟩
  exact ⟨fieldsWF_mono henv (h.2 c hc).1, (h.2 c hc).2.mono henv⟩

/-- Exact syntactic decomposition of an accepted family view into its
parameter telescope, index telescope, and terminal sort. -/
theorem Checked.type_eq
    {source : VInductDecl} (checked : source.Checked) :
    checked.type.type =
      VExpr.forallN checked.params
        (VExpr.forallN checked.indices (.sort checked.resultLevel)) := by
  rw [← VExpr.forallN_telN_dropN source.nparams checked.type.type,
    ← forallN_ctorFields_resultOf
      (VExpr.dropN source.nparams checked.type.type),
    checked.result_eq, checked.params_eq, checked.indices_eq]

/-- The semantic checker contract types the family before that family is
inserted. This is the exact premise needed by the first transaction step. -/
theorem Checked.WF.family_isType
    {source : VInductDecl} {checked : source.Checked}
    {env : VEnv} (h : checked.WF env) :
    env.IsType source.uvars [] checked.type.type := by
  rw [← VExpr.forallN_telN_dropN source.nparams checked.type.type,
    ← forallN_ctorFields_resultOf
      (VExpr.dropN source.nparams checked.type.type),
    checked.result_eq, ← VExpr.forallN_append]
  exact IsType.forallN
    (by simpa [checked.params_eq, checked.indices_eq] using h.1)
    ⟨_, HasType.sort checked.direct_anatomy.2.2.1⟩

/-- Once the retained family constant has the checked family type, the
checked constructor-result spine types the exact normalized family
application.  This fact depends only on analyzer semantics and the constant's
ordinary typing judgment; callers do not need to restate result typing for
each constructor candidate. -/
theorem GenerationChecked.checkedResultTarget_hasType
    {source : VInductDecl} (gen : GenerationChecked source)
    {env : VEnv} (henv : env.Ordered)
    (hchecked : gen.block.checked.WF env)
    (familyConst : env.HasType source.uvars []
      (.const gen.block.sourceType.name (VLevel.params source.uvars))
      gen.block.checked.type.type)
    {ctor : NormalizedCtor} (hctor : ctor ∈ gen.block.ctorPairs) :
    env.HasType source.uvars (ctor.viewBinders gen.block).reverse
      (ctor.resultTarget gen.block)
      (.sort gen.block.checked.resultLevel) := by
  have htype := gen.block.checked.type_eq
  have hfamily : env.HasType source.uvars
      (ctor.view.fields.reverse ++ gen.block.checked.params.reverse)
      (VExpr.appN
        (.const gen.block.sourceType.name (VLevel.params source.uvars))
        (VExpr.bvarRevRange ctor.view.fields.length
          gen.block.checked.params.length))
      (VExpr.forallN
        (VExpr.liftTelN ctor.view.fields.length
          gen.block.checked.indices 0)
        (.sort gen.block.checked.resultLevel)) := by
    have hconst : env.HasType source.uvars
        (ctor.view.fields.reverse ++
          gen.block.checked.params.reverse ++ [])
        (.const gen.block.sourceType.name (VLevel.params source.uvars))
        (VExpr.forallN gen.block.checked.params
          (VExpr.forallN gen.block.checked.indices
            (.sort gen.block.checked.resultLevel))) := by
      simpa only [htype] using familyConst.weak0 henv
    have happ := HasType.appN_selfSpine'
      (As := gen.block.checked.params)
      (B := VExpr.forallN gen.block.checked.indices
        (.sort gen.block.checked.resultLevel))
      (Δ := ctor.view.fields.reverse) (Γ := [])
      (by simpa only [← htype] using gen.block.checked.type_closed)
      hconst
    rw [List.length_reverse, VExpr.liftN_forallN] at happ
    simpa using happ
  have hspine : env.SpineWF source.uvars
      (ctor.view.fields.reverse ++ gen.block.checked.params.reverse)
      (VExpr.forallN
        (VExpr.liftTelN ctor.view.fields.length
          gen.block.checked.indices 0)
        (.sort gen.block.checked.resultLevel))
      ctor.view.resultIndices
      (.sort gen.block.checked.resultLevel) := by
    obtain ⟨c, hc, hview⟩ := gen.viewCtor_ofDirect hctor
    have h := (hchecked.2 c hc).2
    rw [hview]
    simpa [CheckedCtor.ofDirect, gen.block.uvars_eq,
      gen.block.nparams_eq] using h
  have hresult := hspine.hasType_appN hfamily
  rw [← VExpr.appN_append] at hresult
  have hparams : gen.block.checked.params.length = source.nparams :=
    gen.shape.2.1.symm.trans gen.shape.1
  have hfields := (gen.shape.2.2.2.2.2 ctor hctor).2.2.2
  rw [hparams, ← hfields] at hresult
  simpa [NormalizedCtor.viewBinders,
    NormalizedCtor.resultTarget] using hresult

/-- A paired checked constructor's stored view type is exactly its analyzed
binder telescope followed by the normalized family result application. -/
theorem GenerationChecked.viewCtorType_eq
    {source : VInductDecl} (gen : GenerationChecked source)
    {ctor : NormalizedCtor} (hctor : ctor ∈ gen.block.ctorPairs) :
    ctor.view.value.type =
      VExpr.forallN (ctor.viewBinders gen.block)
        (ctor.resultTarget gen.block) := by
  obtain ⟨c, hc, hview⟩ := gen.viewCtor_ofDirect hctor
  have hcAn := gen.block.checked.direct_anatomy.2.2.2.2.2 c hc
  have htype := VExpr.forallN_telN_dropN
    gen.block.normalization.view.nparams c.type
  rw [hcAn.2.1, (stage3Ctor_eq hcAn.2.2).1] at htype
  have hfields := (gen.shape.2.2.2.2.2 ctor hctor).2.2.2
  have hfields' :
      (ctor.rawFields gen.block.normalization.view.nparams).length =
        (ctorFields (VExpr.dropN
          gen.block.normalization.view.nparams c.type)).length := by
    simpa [gen.block.nparams_eq, hview,
      CheckedCtor.ofDirect] using hfields
  simpa [← VExpr.forallN_append, NormalizedCtor.viewBinders,
    NormalizedCtor.resultTarget, hview, hfields',
    CheckedCtor.ofDirect, gen.block.uvars_eq,
    gen.block.nparams_eq, gen.block.sourceType_name_eq,
    gen.block.checked.params_eq, Nat.zero_add] using htype.symm

/--
info: 'Lean4Lean.VInductDecl.Checked.type_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Checked.type_eq

/--
info: 'Lean4Lean.VInductDecl.GenerationChecked.viewCtorType_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms GenerationChecked.viewCtorType_eq

/--
info: 'Lean4Lean.VInductDecl.GenerationChecked.checkedResultTarget_hasType' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms GenerationChecked.checkedResultTarget_hasType

/-- Final-environment invariant for mixed raw/view generation. It contains
only facts stable after the raw family and constructors have been inserted;
the staged pre-family/post-family split remains in `GenerationChecked.WF`. -/
structure GenerationEnv {source : VInductDecl}
    (gen : GenerationChecked source) (env : VEnv) : Prop where
  ord : env.Ordered
  checked : gen.block.checked.WF env
  familyTel :
    env.TelDefEq source.uvars []
      (gen.block.rawParams ++ gen.block.rawIndices)
      (gen.block.checked.params ++ gen.block.checked.indices)
  familyResult :
    env.IsDefEq source.uvars
      (gen.block.rawParams ++ gen.block.rawIndices).reverse
      gen.block.rawResult (.sort gen.block.checked.resultLevel)
      (.sort (.succ gen.block.checked.resultLevel))
  ctorWF :
    ∀ ctor ∈ gen.block.ctorPairs, ctor.WF gen.block env
  familyConst :
    env.constants gen.block.sourceType.name =
      some gen.block.sourceType.toVConstant
  ctorConst :
    ∀ ctor ∈ gen.block.ctorPairs,
      env.constants ctor.raw.name = some ctor.raw.toVConstant

/-- Promote a staged generation certificate into the final invariant once the
transaction supplies environment growth and exact raw constant lookups. -/
theorem GenerationChecked.WF.toGenerationEnv {source : VInductDecl}
    {gen : GenerationChecked source} {pre envT env : VEnv}
    (h : gen.WF pre)
    (hadd : pre.addConst gen.block.sourceType.name
      gen.block.sourceType.toVConstant = some envT)
    (hlePre : pre ≤ env) (hleT : envT ≤ env) (ord : env.Ordered)
    (hfamily : env.constants gen.block.sourceType.name =
      some gen.block.sourceType.toVConstant)
    (hctors : ∀ ctor ∈ gen.block.ctorPairs,
      env.constants ctor.raw.name = some ctor.raw.toVConstant) :
    GenerationEnv gen env where
  ord := ord
  checked := h.blockWF.2.mono hlePre
  familyTel := h.familyTel.mono hlePre
  familyResult := h.familyResult.mono hlePre
  ctorWF := fun ctor hctor => (h.ctors envT hadd ctor hctor).mono hleT
  familyConst := hfamily
  ctorConst := hctors

/-- Exact decomposition of the stored raw family type. -/
theorem NormalizedChecked.rawType_eq {source : VInductDecl}
    (block : NormalizedChecked source) :
    block.sourceType.type =
      VExpr.forallN block.rawParams
        (VExpr.forallN block.rawIndices block.rawResult) := by
  conv => lhs
          rw [← VExpr.forallN_telN_dropN source.nparams
            block.sourceType.type,
            ← forallN_ctorFields_resultOf
              (VExpr.dropN source.nparams block.sourceType.type)]
  rfl

/-- Exact decomposition of a stored raw constructor type into its declared
parameter/field telescope and terminal result. -/
theorem NormalizedCtor.rawType_eq {source : VInductDecl}
    (ctor : NormalizedCtor) :
    ctor.raw.type =
      VExpr.forallN (ctor.declaredBinders source.nparams)
        (ctor.rawResult source.nparams) := by
  conv => lhs
          rw [← VExpr.forallN_telN_dropN source.nparams
            ctor.raw.type,
            ← forallN_ctorFields_resultOf
              (VExpr.dropN source.nparams ctor.raw.type)]
  rw [NormalizedCtor.declaredBinders, NormalizedCtor.rawFields,
    NormalizedCtor.rawResult, ← VExpr.forallN_append]

namespace GenerationEnv

variable {source : VInductDecl} {gen : GenerationChecked source}
  {env : VEnv} (S : GenerationEnv gen env)
include S

/-- The final mixed-generation invariant is monotone once the larger
environment is known to remain ordered. -/
theorem mono {env' : VEnv} (henv : env ≤ env') (ord : env'.Ordered) :
    GenerationEnv gen env' where
  ord := ord
  checked := S.checked.mono henv
  familyTel := S.familyTel.mono henv
  familyResult := S.familyResult.mono henv
  ctorWF := fun ctor hctor => (S.ctorWF ctor hctor).mono henv
  familyConst := henv.constants S.familyConst
  ctorConst := fun ctor hctor => henv.constants (S.ctorConst ctor hctor)

/-- The checked result universe is well formed at the source declaration's
universe arity. -/
theorem resultLevel_WF :
    gen.block.checked.resultLevel.WF source.uvars := by
  rw [gen.block.uvars_eq]
  exact gen.block.checked.direct_anatomy.2.2.1

theorem rawFamily_onTel :
    env.OnTel source.uvars []
      (gen.block.rawParams ++ gen.block.rawIndices) :=
  S.familyTel.raw_onTel

theorem rawFamily_isType :
    env.IsType source.uvars [] gen.block.sourceType.type := by
  rw [gen.block.rawType_eq, ← VExpr.forallN_append]
  have hresult₀ : env.IsType source.uvars
      (gen.block.rawParams ++ gen.block.rawIndices).reverse
      gen.block.rawResult :=
    ⟨_, S.familyResult.hasType.1⟩
  have hresult : env.IsType source.uvars
      ((gen.block.rawParams ++ gen.block.rawIndices).reverse ++ [])
      gen.block.rawResult := by
    simpa using hresult₀
  exact IsType.forallN S.rawFamily_onTel hresult

theorem rawCtor_isType {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) :
    env.IsType source.uvars [] ctor.raw.type :=
  (S.ctorWF ctor hctor).rawDeclared_isType

/-- The raw family constant at declaration universes, in any context. -/
theorem familyConst_decl {Γ : List VExpr} :
    env.HasType source.uvars Γ
      (.const gen.block.sourceType.name (VLevel.params source.uvars))
      gen.block.sourceType.type := by
  have hwf : gen.block.sourceType.toVConstant.WF env := by
    show env.IsType gen.block.sourceType.uvars []
      gen.block.sourceType.type
    rw [gen.block.sourceType_uvars_eq]
    exact S.rawFamily_isType
  have h := HasType.const0 S.familyConst hwf
  rw [gen.block.sourceType_uvars_eq] at h
  exact h.weak0 S.ord

/-- A stored raw constructor constant at declaration universes, in any
context. -/
theorem ctorConst_decl {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) {Γ : List VExpr} :
    env.HasType source.uvars Γ
      (.const ctor.raw.name (VLevel.params source.uvars))
      ctor.raw.type := by
  have hwf : ctor.raw.toVConstant.WF env := by
    show env.IsType ctor.raw.uvars [] ctor.raw.type
    rw [gen.ctor_uvars_eq hctor]
    exact S.rawCtor_isType hctor
  have h := HasType.const0 (S.ctorConst ctor hctor) hwf
  rw [gen.ctor_uvars_eq hctor] at h
  exact h.weak0 S.ord

/-- The stored constructor constant applied to the raw parameter/field
self-spine emitted by mixed artifacts. The proof passes through the common
checked view, so the constructor's declared raw parameter prefix need only be
definitionally equal to the block's emitted raw parameter prefix. -/
theorem ctorApp_emitted_decl {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) :
    env.HasType source.uvars
      ((ctor.rawFields source.nparams).reverse ++
        gen.block.rawParams.reverse)
      (VExpr.appN
        (.const ctor.raw.name (VLevel.params source.uvars))
        (VExpr.bvarRevRange
            (ctor.rawFields source.nparams).length source.nparams ++
          VExpr.bvarRevRange 0
            (ctor.rawFields source.nparams).length))
      (ctor.resultTarget gen.block) := by
  let E := ctor.emittedBinders gen.block
  let V := ctor.viewBinders gen.block
  have hc : env.HasType source.uvars []
      (.const ctor.raw.name (VLevel.params source.uvars))
      (VExpr.forallN (ctor.declaredBinders source.nparams)
        (ctor.rawResult source.nparams)) := by
    rw [← ctor.rawType_eq]
    exact S.ctorConst_decl hctor
  obtain ⟨_, hdecl⟩ :=
    (S.ctorWF ctor hctor).declaredTel.forallN_defeq
      (by
        simpa using (S.ctorWF ctor hctor).declaredResult)
  have hview : env.HasType source.uvars []
      (.const ctor.raw.name (VLevel.params source.uvars))
      (VExpr.forallN V (ctor.resultTarget gen.block)) := by
    simpa [V] using hdecl.defeq hc
  have hresult : env.HasType source.uvars E.reverse
      (ctor.resultTarget gen.block)
      (.sort gen.block.checked.resultLevel) := by
    simpa [E] using
      (S.ctorWF ctor hctor).emittedResult.hasType.2
  obtain ⟨_, hemit⟩ :=
    (S.ctorWF ctor hctor).emittedTel.forallN_defeq
      (by simpa [E] using hresult)
  have hcE₀ : env.HasType source.uvars []
      (.const ctor.raw.name (VLevel.params source.uvars))
      (VExpr.forallN E (ctor.resultTarget gen.block)) := by
    exact hemit.defeq' (by simpa [V] using hview)
  have hclosed :
      (VExpr.forallN E (ctor.resultTarget gen.block)).ClosedN 0 :=
    (hcE₀.closedN' S.ord.closed trivial).2.2
  have hcE : env.HasType source.uvars E.reverse
      (.const ctor.raw.name (VLevel.params source.uvars))
      (VExpr.forallN E (ctor.resultTarget gen.block)) :=
    hcE₀.weak0 S.ord
  have happ := HasType.appN_selfSpine'
    (As := E) (B := ctor.resultTarget gen.block)
    (Δ := []) (Γ := []) hclosed (by simpa using hcE)
  simp only [List.length_nil, VExpr.liftN_zero,
    List.nil_append, List.append_nil] at happ
  have hEctx :
      E.reverse =
        (ctor.rawFields source.nparams).reverse ++
          gen.block.rawParams.reverse := by
    simp [E, NormalizedCtor.emittedBinders,
      List.reverse_append]
  have hElen :
      E.length =
        (ctor.rawFields source.nparams).length +
          source.nparams := by
    simp [E, NormalizedCtor.emittedBinders, gen.shape.1]
    omega
  rw [hEctx, hElen,
    ← VExpr.bvarRevRange_append source.nparams
      (ctor.rawFields source.nparams).length] at happ
  exact happ

/-- The raw family constant instantiated into recursor universes. -/
theorem familyConst_rec {Γ : List VExpr} :
    env.HasType (source.uvars + 1) Γ
      (.const gen.block.sourceType.name
        (VLevel.params' source.uvars 1))
      (gen.block.sourceType.type.instL
        (VLevel.params' source.uvars 1)) := by
  have h := (S.familyConst_decl (Γ := [])).instL
    (U' := source.uvars + 1) VLevel.params'_one_wf
  rw [show
    (VExpr.const gen.block.sourceType.name
      (VLevel.params source.uvars)).instL
        (VLevel.params' source.uvars 1) =
      .const gen.block.sourceType.name
        (VLevel.params' source.uvars 1) by
    simp [VExpr.instL, VLevel.params_map_inst_params']] at h
  exact h.weak0 S.ord

/-- The raw family type decomposed in recursor universes. -/
theorem rawType_rec_eq :
    gen.block.sourceType.type.instL (VLevel.params' source.uvars 1) =
      VExpr.forallN gen.paramsTel
        (VExpr.forallN gen.idxTel
          (gen.block.rawResult.instL
            (VLevel.params' source.uvars 1))) := by
  rw [gen.block.rawType_eq, VExpr.instL_forallN,
    VExpr.instL_forallN]
  rfl

/-- The raw family applied to its complete raw self-spine has the normalized
result sort. -/
theorem familyApp_hasType :
    env.HasType (source.uvars + 1)
      (gen.idxTel.reverse ++ gen.paramsTel.reverse)
      (VExpr.appN
        (.const gen.block.sourceType.name
          (VLevel.params' source.uvars 1))
        (VExpr.bvarRevRange gen.idxTel.length source.nparams ++
          VExpr.bvarRevRange 0 gen.idxTel.length))
      (.sort
        (gen.block.checked.resultLevel.inst
          (VLevel.params' source.uvars 1))) := by
  let ls := VLevel.params' source.uvars 1
  have hclosed :
      (gen.block.sourceType.type.instL ls).ClosedN 0 :=
    (Ordered.closedC S.ord S.familyConst).instL
  have hconst : env.HasType (source.uvars + 1)
      ((gen.paramsTel ++ gen.idxTel).reverse)
      (.const gen.block.sourceType.name ls)
      (VExpr.forallN (gen.paramsTel ++ gen.idxTel)
        (gen.block.rawResult.instL ls)) := by
    rw [VExpr.forallN_append, ← S.rawType_rec_eq]
    exact S.familyConst_rec
  have hcanonicalClosed :
      (VExpr.forallN (gen.paramsTel ++ gen.idxTel)
        (gen.block.rawResult.instL ls)).ClosedN 0 := by
    rw [VExpr.forallN_append, ← S.rawType_rec_eq]
    exact hclosed
  have happ := HasType.appN_selfSpine'
    (Δ := []) (Γ := []) hcanonicalClosed (by
      simpa using hconst)
  simp only [List.length_nil, VExpr.liftN_zero, List.nil_append,
    List.append_nil] at happ
  have hlen :
      (gen.paramsTel ++ gen.idxTel).length =
        gen.idxTel.length + source.nparams := by
    simp only [List.length_append, GenerationChecked.paramsTel,
      GenerationChecked.idxTel, List.length_map]
    rw [gen.shape.1]
    omega
  rw [VExpr.bvarRevRange_congr' 0 hlen,
    ← VExpr.bvarRevRange_append] at happ
  have hresult := S.familyResult.instL
    (U' := source.uvars + 1) VLevel.params'_one_wf
  have hresult' : env.IsDefEq (source.uvars + 1)
      (gen.idxTel.reverse ++ gen.paramsTel.reverse)
      (gen.block.rawResult.instL ls)
      (.sort (gen.block.checked.resultLevel.inst ls))
      (.sort (.succ (gen.block.checked.resultLevel.inst ls))) := by
    simpa [ls, GenerationChecked.paramsTel, GenerationChecked.idxTel,
      List.map_reverse, VLevel.inst] using hresult
  exact hresult'.defeq (by
    simpa [List.reverse_append] using happ)

/-- The mixed motive is a well-formed type over the raw parameter context. -/
theorem motive_isType :
    env.IsType (source.uvars + 1) gen.paramsTel.reverse
      gen.motiveType := by
  have htel₀ := S.rawFamily_onTel.instL
    (U' := source.uvars + 1) VLevel.params'_one_wf
  have htel :
      env.OnTel (source.uvars + 1) []
        (gen.paramsTel ++ gen.idxTel) := by
    simpa [GenerationChecked.paramsTel, GenerationChecked.idxTel] using htel₀
  have hidx : env.OnTel (source.uvars + 1) gen.paramsTel.reverse
      gen.idxTel := by
    simpa using htel.of_append.2
  refine IsType.forallN hidx ?_
  exact ⟨_, by
    simpa [GenerationChecked.motiveType] using
      HasType.forallE S.familyApp_hasType
        (HasType.sort (by
          change 0 < source.uvars + 1
          omega))⟩

end GenerationEnv

/--
info: 'Lean4Lean.VInductDecl.GenerationEnv.motive_isType' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms GenerationEnv.motive_isType

/-- The public inductive-declaration contract is monotone in its prefix
environment. This lets replay fixtures prepend independently verified
declarations without rebuilding the block's Stage-3 derivation. -/
theorem WF.mono {env env' : VEnv} (henv : env ≤ env')
    (H : VInductDecl.WF env decl) : VInductDecl.WF env' decl := by
  refine ⟨H.1, fun ty hty => ?_⟩
  obtain ⟨htel, hctors⟩ := H.2 ty hty
  exact ⟨htel.mono henv, fun c hc =>
    ⟨fieldsWF_mono henv (hctors c hc).1, (hctors c hc).2.mono henv⟩⟩

/-- Extract the carried index-spine typing of the recursive field at
position `q` from a `fieldsWF` chain. -/
theorem fieldsWF_spine {U : Nat} {T : Name} {np : Nat} {env : VEnv} {l : VLevel}
    {Is : List VExpr} : ∀ {Bs : List VExpr} {Γ₀ : List VExpr} {j₀ : Nat},
    fieldsWF U T np env l Is Γ₀ j₀ Bs →
    ∀ q B, Bs[q]? = some B → isRecField U T np Is.length (j₀+q) B = true →
    env.SpineWF U ((Bs.take q).reverse ++ Γ₀)
      (VExpr.forallN (VExpr.liftTelN (j₀+q) Is 0) (.sort l)) (recFieldIdxs np B) (.sort l)
  | [], _, _, _, q, B, hB, _ => by simp at hB
  | B' :: Bs, Γ₀, j₀, ⟨_, hSp, hT⟩, 0, B, hB, hrec => by
    obtain rfl : B' = B := by simpa using hB
    simpa using hSp (by simpa using hrec)
  | B' :: Bs, Γ₀, j₀, ⟨_, _, hT⟩, q+1, B, hB, hrec => by
    have := fieldsWF_spine hT q B (by simpa using hB)
      (by rwa [show j₀+1+q = j₀+(q+1) from by omega])
    rw [show j₀+1+q = j₀+(q+1) from by omega] at this
    simpa [List.append_assoc] using this

/-- Extract the uniform semantic evidence for any analyzed recursive
argument. Direct fields are re-expressed as the empty-telescope case; genuine
recursive Pi fields return the evidence stored by `fieldsWF`. -/
theorem fieldsWF_recArg {U : Nat} {T : Name} {np : Nat} {env : VEnv} {l : VLevel}
    {Is : List VExpr} : ∀ {Bs : List VExpr} {Γ₀ : List VExpr} {j₀ : Nat},
    fieldsWF U T np env l Is Γ₀ j₀ Bs →
    ∀ q B r, Bs[q]? = some B →
      recArg? U T np Is.length (j₀+q) B = some r →
      r.WF U env l Is ((Bs.take q).reverse ++ Γ₀)
  | [], _, _, _, q, B, r, hB, _ => by simp at hB
  | B' :: Bs, Γ₀, j₀, ⟨hclass, hSp, htail⟩, 0, B, r, hB, hr => by
    obtain rfl : B' = B := by simpa using hB
    simp only [Nat.add_zero] at hr
    rcases hclass with hdirect | hfun | ⟨hnone, -, -, -⟩
    · have hcanon := recArg?_of_isRecField hdirect
      rw [hcanon] at hr
      obtain rfl := Option.some.inj hr
      exact ⟨trivial, by simpa [RecArg.WF] using hSp hdirect⟩
    · obtain ⟨r', hr', -, hwf⟩ := hfun
      rw [hr'] at hr
      obtain rfl := Option.some.inj hr
      simpa using hwf
    · rw [hnone] at hr
      contradiction
  | B' :: Bs, Γ₀, j₀, ⟨_, _, htail⟩, q+1, B, r, hB, hr => by
    have h := fieldsWF_recArg htail q B r (by simpa using hB)
      (by rwa [show j₀+1+q = j₀+(q+1) from by omega])
    simpa [List.append_assoc] using h

namespace GenerationEnv

variable {source : VInductDecl} {gen : GenerationChecked source}
  {env : VEnv} (S : GenerationEnv gen env)
include S

/-- Checked field semantics for one paired constructor, re-indexed onto the
raw block header used by mixed generation. -/
theorem viewFieldsWF {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) :
    fieldsWF source.uvars gen.block.sourceType.name source.nparams env
      gen.block.checked.resultLevel gen.block.checked.indices
      gen.block.checked.params.reverse 0 ctor.view.fields := by
  obtain ⟨c, hc, hview⟩ := gen.viewCtor_ofDirect hctor
  have h := (S.checked.2 c hc).1
  rw [hview]
  simpa [CheckedCtor.ofDirect, gen.block.uvars_eq,
    gen.block.nparams_eq, gen.block.sourceType_name_eq] using h

/-- Every retained recursive descriptor comes from re-analysis of the field
at its recorded position in the checked view. -/
theorem viewRecArg_data {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) {r : RecArg}
    (hr : r ∈ ctor.view.recursive) :
    ∃ B, ctor.view.fields[r.fieldIndex]? = some B ∧
      recArg? source.uvars gen.block.sourceType.name source.nparams
        gen.block.checked.indices.length r.fieldIndex B = some r := by
  obtain ⟨c, -, hview⟩ := gen.viewCtor_ofDirect hctor
  rw [hview] at hr ⊢
  simp only [CheckedCtor.ofDirect] at hr ⊢
  obtain ⟨B, hB, hrec⟩ := recArgs_getElem r hr
  exact ⟨B, by simpa using hB, hrec⟩

/-- Retained recursive descriptors have the checked family-index arity. -/
theorem viewRecArg_indices_length {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) {r : RecArg}
    (hr : r ∈ ctor.view.recursive) :
    r.indices.length = gen.block.checked.indices.length := by
  obtain ⟨B, hB, hrec⟩ := S.viewRecArg_data hctor hr
  exact (recArg?_eq hrec).2.2.2.1

/-- Retained recursive descriptors point inside the normalized field list. -/
theorem viewRecArg_lt {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) {r : RecArg}
    (hr : r ∈ ctor.view.recursive) :
    r.fieldIndex < ctor.view.fields.length := by
  obtain ⟨c, -, hview⟩ := gen.viewCtor_ofDirect hctor
  rw [hview] at hr ⊢
  simp only [CheckedCtor.ofDirect] at hr ⊢
  simpa using recArgs_lt r hr

/-- The checked-view certificate supplies recursive-argument semantics in
the exact normalized prefix context. -/
theorem viewRecArg_WF {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) {r : RecArg}
    (hr : r ∈ ctor.view.recursive) :
    r.WF source.uvars env gen.block.checked.resultLevel
      gen.block.checked.indices
      ((ctor.view.fields.take r.fieldIndex).reverse ++
        gen.block.checked.params.reverse) := by
  obtain ⟨B, hB, hrec⟩ := S.viewRecArg_data hctor hr
  have h := fieldsWF_recArg (S.viewFieldsWF hctor)
    r.fieldIndex B r hB (by simpa using hrec)
  simpa using h

/-- Definitionally equal raw/view contexts at any constructor-field prefix.
This is the structural bridge used before instantiation and weakening. -/
theorem emittedPrefix_ctx {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) (j : Nat) :
    env.IsDefEqCtx source.uvars []
      ((ctor.rawFields source.nparams |>.take j).reverse ++
        gen.block.rawParams.reverse)
      ((ctor.view.fields.take j).reverse ++
        gen.block.checked.params.reverse) := by
  have h := ((S.ctorWF ctor hctor).emittedTel.take
    (source.nparams + j)).ctx
  have hraw :
      (gen.block.rawParams ++ ctor.rawFields source.nparams).take
          (source.nparams + j) =
        gen.block.rawParams ++
          (ctor.rawFields source.nparams).take j := by
    rw [← gen.shape.1]
    rw [List.take_append, List.take_of_length_le (by omega)]
    simp
  have hviewLen :
      gen.block.checked.params.length = source.nparams :=
    gen.shape.2.1.symm.trans gen.shape.1
  have hview :
      (gen.block.checked.params ++ ctor.view.fields).take
          (source.nparams + j) =
        gen.block.checked.params ++ ctor.view.fields.take j := by
    rw [← hviewLen]
    rw [List.take_append, List.take_of_length_le (by omega)]
    simp
  simp only [NormalizedCtor.emittedBinders,
    NormalizedCtor.viewBinders] at h
  rw [hraw, hview] at h
  simpa [List.reverse_append] using h

/-- The pointwise raw/view field-domain equality at a paired position, in
the preceding raw context. -/
theorem emittedField_defeq {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) {j : Nat} {B B' : VExpr}
    (hB : (ctor.rawFields source.nparams)[j]? = some B)
    (hB' : ctor.view.fields[j]? = some B') :
    ∃ u, env.IsDefEq source.uvars
      ((ctor.rawFields source.nparams |>.take j).reverse ++
        gen.block.rawParams.reverse)
      B B' (.sort u) := by
  have hraw :
      getElem?
        (gen.block.rawParams ++ ctor.rawFields source.nparams)
        (source.nparams + j) = some B := by
    rw [List.getElem?_append_right (by
      rw [gen.shape.1]
      omega), gen.shape.1]
    simpa using hB
  have hviewLen :
      gen.block.checked.params.length = source.nparams :=
    gen.shape.2.1.symm.trans gen.shape.1
  have hview :
      getElem?
        (gen.block.checked.params ++ ctor.view.fields)
        (source.nparams + j) = some B' := by
    rw [List.getElem?_append_right (by
      rw [hviewLen]
      omega), hviewLen]
    simpa using hB'
  obtain ⟨u, h⟩ :=
    (S.ctorWF ctor hctor).emittedTel.getElem? hraw hview
  have htake :
      (gen.block.rawParams ++ ctor.rawFields source.nparams).take
          (source.nparams + j) =
        gen.block.rawParams ++
          (ctor.rawFields source.nparams).take j := by
    rw [← gen.shape.1]
    rw [List.take_append, List.take_of_length_le (by omega)]
    simp
  simp only [NormalizedCtor.emittedBinders] at h
  rw [htake, List.reverse_append] at h
  exact ⟨u, by simpa using h⟩

/-- Recursive-argument semantics transported from the checked view into the
raw constructor-field prefix that mixed artifacts actually bind. -/
theorem rawRecArg_WF {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) {r : RecArg}
    (hr : r ∈ ctor.view.recursive) :
    r.WF source.uvars env gen.block.checked.resultLevel
      gen.block.checked.indices
      ((ctor.rawFields source.nparams |>.take r.fieldIndex).reverse ++
        gen.block.rawParams.reverse) := by
  exact (S.viewRecArg_WF hctor hr).defeqDFC S.ord
    ((S.emittedPrefix_ctx hctor r.fieldIndex).symm S.ord)

/-- The family telescope contract restricted to the index suffix. -/
theorem rawIndexTel_defeq :
    env.TelDefEq source.uvars gen.block.rawParams.reverse
      gen.block.rawIndices gen.block.checked.indices := by
  have h := S.familyTel.drop source.nparams
  have hrawTake :
      (gen.block.rawParams ++ gen.block.rawIndices).take source.nparams =
        gen.block.rawParams := by
    rw [← gen.shape.1, List.take_append, List.take_length]
    simp
  have hrawDrop :
      (gen.block.rawParams ++ gen.block.rawIndices).drop source.nparams =
        gen.block.rawIndices := by
    rw [← gen.shape.1, List.drop_append]
    simp
  have hviewLen :
      gen.block.checked.params.length = source.nparams :=
    gen.shape.2.1.symm.trans gen.shape.1
  have hviewDrop :
      (gen.block.checked.params ++ gen.block.checked.indices).drop
          source.nparams =
        gen.block.checked.indices := by
    rw [← hviewLen, List.drop_append]
    simp
  rw [hrawTake, hrawDrop, hviewDrop] at h
  simpa using h

/-- The raw/view index telescope relation transported into recursor
universes. -/
theorem rawIndexTel_defeq_rec :
    env.TelDefEq (source.uvars + 1) gen.paramsTel.reverse gen.idxTel
      (gen.block.checked.indices.map
        (VExpr.instL (VLevel.params' source.uvars 1))) := by
  have h := S.rawIndexTel_defeq.instL
    (U' := source.uvars + 1) VLevel.params'_one_wf
  simpa [GenerationChecked.paramsTel, GenerationChecked.idxTel,
    List.map_reverse] using h

/-- Transport all retained recursive-argument evidence into a mixed
minor/rule context. Raw constructor fields and raw family indices are the
emitted surfaces; recursive classification and index expressions remain the
checked-view data. -/
theorem recArg_transport {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) {r₀ : RecArg}
    (hr₀ : r₀ ∈ ctor.view.recursive)
    (mid : List VExpr) {g : Nat} (hg : mid.length = g)
    (As₂ : List VExpr) {d : Nat} (hd : As₂.length = d) :
    let r := r₀.instL (VLevel.params' source.uvars 1)
    let As := VExpr.liftTelN d
      (VExpr.liftTelN g r.binders r.fieldIndex) 0
    env.OnTel (source.uvars + 1)
        (As₂ ++ ((VExpr.liftTelN g
          ((ctor.fieldsR source.uvars source.nparams).take
            r.fieldIndex) 0).reverse ++
          (mid ++ gen.paramsTel.reverse))) As ∧
      env.SpineWF (source.uvars + 1)
        (As.reverse ++
          (As₂ ++ ((VExpr.liftTelN g
            ((ctor.fieldsR source.uvars source.nparams).take
              r.fieldIndex) 0).reverse ++
            (mid ++ gen.paramsTel.reverse))))
        (VExpr.forallN
          (VExpr.liftTelN
            (r.fieldIndex + r.binders.length + g + d) gen.idxTel 0)
          (.sort (gen.block.checked.resultLevel.inst
            (VLevel.params' source.uvars 1))))
        (r.indices.map fun e =>
          (e.liftN g (r.fieldIndex + r.binders.length)).liftN d
            r.binders.length)
        (.sort (gen.block.checked.resultLevel.inst
          (VLevel.params' source.uvars 1))) := by
  dsimp only
  let ls := VLevel.params' source.uvars 1
  have hjlt :
      r₀.fieldIndex < (ctor.rawFields source.nparams).length := by
    have hview := S.viewRecArg_lt hctor hr₀
    have hfields :=
      (gen.shape.2.2.2.2.2 ctor hctor).2.2.2
    omega
  have hsem := S.rawRecArg_WF hctor hr₀
  have htel₁ := hsem.1.instL
    (U' := source.uvars + 1) VLevel.params'_one_wf
  have hsp₁ := hsem.2.instL
    (U' := source.uvars + 1) VLevel.params'_one_wf
  have hctx :
      (((ctor.rawFields source.nparams).take r₀.fieldIndex).reverse ++
        gen.block.rawParams.reverse).map (VExpr.instL ls) =
      ((ctor.fieldsR source.uvars source.nparams).take
          r₀.fieldIndex).reverse ++ gen.paramsTel.reverse := by
    simp [ls, NormalizedCtor.fieldsR, GenerationChecked.paramsTel,
      List.map_reverse, List.map_take]
  rw [hctx] at htel₁
  rw [List.map_append, List.map_reverse, hctx] at hsp₁
  simp only [RecArg.instL, VExpr.instL_forallN,
    VExpr.liftTelN_instL, List.map_reverse] at htel₁ hsp₁
  have hjlen :
      ((ctor.fieldsR source.uvars source.nparams).take
        r₀.fieldIndex).length = r₀.fieldIndex := by
    simp only [NormalizedCtor.fieldsR, List.length_take,
      List.length_map]
    omega
  have hidxField := S.rawIndexTel_defeq_rec.weakN S.ord
    (Ctx.LiftN.zero (Γ := gen.paramsTel.reverse)
      ((ctor.fieldsR source.uvars source.nparams).take
        r₀.fieldIndex).reverse)
  rw [List.length_reverse, hjlen] at hidxField
  have hidxPrivate := hidxField.weakN S.ord
    (Ctx.LiftN.zero
      (Γ := ((ctor.fieldsR source.uvars source.nparams).take
          r₀.fieldIndex).reverse ++ gen.paramsTel.reverse)
      (r₀.binders.map (VExpr.instL ls)).reverse)
  simp only [List.length_reverse, List.length_map] at hidxPrivate
  rw [VExpr.liftTelN_liftTelN,
    VExpr.liftTelN_liftTelN] at hidxPrivate
  have hidxLen :
      (r₀.indices.map (VExpr.instL ls)).length =
        (VExpr.liftTelN
          (r₀.fieldIndex + r₀.binders.length) gen.idxTel 0).length := by
    simp only [List.length_map, VExpr.liftTelN_length,
      GenerationChecked.idxTel]
    exact (S.viewRecArg_indices_length hctor hr₀).trans
      gen.shape.2.2.1.symm
  have hspRaw :=
    hidxPrivate.spine_sort S.ord hsp₁ hidxLen
  have W₁ := Ctx.LiftN.consTel (n := mid.length)
    ((ctor.fieldsR source.uvars source.nparams).take
      r₀.fieldIndex)
    (Ctx.LiftN.zero (Γ := gen.paramsTel.reverse) mid)
  rw [hjlen, Nat.add_zero] at W₁
  have htel₂ := htel₁.weakN S.ord W₁
  have hsp₂ := hspRaw.weakN S.ord
    (Ctx.LiftN.consTel
      (r₀.binders.map (VExpr.instL ls)) W₁)
  rw [hg] at htel₂ hsp₂
  have W₂ := Ctx.LiftN.zero
    (Γ := (VExpr.liftTelN g
        ((ctor.fieldsR source.uvars source.nparams).take
          r₀.fieldIndex) 0).reverse ++
      (mid ++ gen.paramsTel.reverse)) As₂ (h := hd)
  have htel₃ := htel₂.weakN S.ord W₂
  have hsp₃ := hsp₂.weakN S.ord
    (Ctx.LiftN.consTel
      (VExpr.liftTelN g
        (r₀.binders.map (VExpr.instL ls)) r₀.fieldIndex) W₂)
  refine ⟨?_, ?_⟩
  · simpa [ls, RecArg.instL, List.append_assoc] using htel₃
  · simp only [List.length_map, VExpr.liftTelN_length,
      Nat.add_zero] at hsp₃
    rw [VExpr.liftN_forallN, VExpr.liftN_forallN,
      VExpr.liftTelN_liftTelN_hi'
        (r₀.fieldIndex + r₀.binders.length) g _ 0 (by omega),
      VExpr.liftTelN_liftTelN_mid
        (r₀.fieldIndex + r₀.binders.length + g) d _ 0
        r₀.binders.length (Nat.zero_le _) (by omega)] at hsp₃
    rw [show r₀.binders.length + r₀.fieldIndex =
      r₀.fieldIndex + r₀.binders.length from Nat.add_comm _ _] at hsp₃
    simpa [ls, RecArg.instL, VExpr.instL, VExpr.liftN,
      List.map_map, Function.comp_def, List.append_assoc] using hsp₃

end GenerationEnv

/-- Raw mixed fields preserve their arity under recursor-universe
instantiation. -/
theorem NormalizedCtor.fieldsR_length {source : VInductDecl}
    (ctor : NormalizedCtor) :
    (ctor.fieldsR source.uvars source.nparams).length =
      (ctor.rawFields source.nparams).length :=
  List.length_map ..

/-- Pointwise lookup through the raw mixed field universe transport. -/
theorem NormalizedCtor.fieldsR_getElem? {source : VInductDecl}
    {ctor : NormalizedCtor} {q : Nat} :
    (ctor.fieldsR source.uvars source.nparams)[q]? =
      (ctor.rawFields source.nparams)[q]?.map
        (VExpr.instL (VLevel.params' source.uvars 1)) :=
  List.getElem?_map ..

/-- Unpack one mixed recursive descriptor to the retained declaration-level
descriptor from the checked view. -/
theorem NormalizedCtor.recArgsR_mem {source : VInductDecl}
    {ctor : NormalizedCtor} {r : RecArg}
    (hr : r ∈ ctor.recArgsR source.uvars) :
    ∃ r₀, r₀ ∈ ctor.view.recursive ∧
      r = r₀.instL (VLevel.params' source.uvars 1) := by
  obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.1 hr
  exact ⟨r₀, hr₀, rfl⟩

/-- Syntactic lifting law for the mixed motive. -/
theorem GenerationChecked.motiveType_liftN {source : VInductDecl}
    (gen : GenerationChecked source) (n : Nat) :
    gen.motiveType.liftN n =
      VExpr.forallN (VExpr.liftTelN n gen.idxTel 0)
        (.forallE
          (VExpr.appN
            (.const gen.block.sourceType.name
              (VLevel.params' source.uvars 1))
            (VExpr.bvarRevRange (n + gen.idxTel.length)
                source.nparams ++
              VExpr.bvarRevRange 0 gen.idxTel.length))
          (.sort (.param 0))) := by
  rw [show gen.motiveType =
      VExpr.forallN gen.idxTel
        (.forallE
          (VExpr.appN
            (.const gen.block.sourceType.name
              (VLevel.params' source.uvars 1))
            (VExpr.bvarRevRange gen.idxTel.length source.nparams ++
              VExpr.bvarRevRange 0 gen.idxTel.length))
          (.sort (.param 0))) from rfl,
    VExpr.liftN_forallN]
  refine congrArg _ ?_
  show VExpr.forallE _ _ = VExpr.forallE _ _
  refine congr (congrArg _ ?_) rfl
  rw [VExpr.liftN_appN, List.map_append,
    bvarRevRange_liftN_ge _ _ _ _ (by omega),
    VExpr.bvarRevRange_liftN_high _ _ _ _ (by omega)]
  rfl

/-- Apply a mixed motive variable to a raw-index spine and a typed family
major. -/
theorem GenerationChecked.motiveVarApp_hasType {source : VInductDecl}
    (gen : GenerationChecked source) {env : VEnv} {l : VLevel}
    {Γ : List VExpr} {K : Nat} {idxs : List VExpr} {a : VExpr}
    (hM : env.HasType (source.uvars + 1) Γ (.bvar K)
      (gen.motiveType.liftN (K+1)))
    (hidx : env.SpineWF (source.uvars + 1) Γ
      (VExpr.forallN (VExpr.liftTelN (K+1) gen.idxTel 0)
        (.sort l))
      idxs (.sort l))
    (hlen : idxs.length = gen.idxTel.length)
    (ha : env.HasType (source.uvars + 1) Γ a
      (VExpr.appN
        (.const gen.block.sourceType.name
          (VLevel.params' source.uvars 1))
        (VExpr.bvarRevRange (K+1) source.nparams ++ idxs))) :
    env.HasType (source.uvars + 1) Γ
      (VExpr.appN (.bvar K) (idxs ++ [a])) (.sort (.param 0)) := by
  rw [gen.motiveType_liftN] at hM
  have hshape := hidx.retarget
    (by simpa only [VExpr.liftTelN_length] using hlen)
    (.forallE
      (VExpr.appN
        (.const gen.block.sourceType.name
          (VLevel.params' source.uvars 1))
        (VExpr.bvarRevRange (K+1 + gen.idxTel.length)
            source.nparams ++
          VExpr.bvarRevRange 0 gen.idxTel.length))
      (.sort (.param 0)))
  rw [VExpr.instRev_forallE_sort, VExpr.instRev_appN,
    VExpr.instRev_closedN _
      (C := .const gen.block.sourceType.name
        (VLevel.params' source.uvars 1)) trivial,
    List.map_append,
    VExpr.map_instRev_bvarRevRange_ge _ _ _ (by rw [hlen]; omega),
    show K+1+gen.idxTel.length-idxs.length = K+1 from by
      rw [hlen, Nat.add_sub_cancel],
    VExpr.bvarRevRange_congr' 0 hlen.symm,
    VExpr.map_instRev_bvarRevRange] at hshape
  rw [hlen] at hshape
  have hApp := hshape.hasType_appN hM
  rw [VExpr.appN_append]
  exact HasType.app hApp (by simpa using ha)

/-- Mixed minor generation preserves constructor-list arity at every suffix
depth. -/
theorem GenerationChecked.minorTypesAux_length
    {source : VInductDecl} (gen : GenerationChecked source) :
    ∀ (ctors : List NormalizedCtor) (i : Nat),
      (gen.minorTypesAux ctors i).length = ctors.length
  | [], _ => rfl
  | _ :: ctors, i => by
    simp [GenerationChecked.minorTypesAux,
      gen.minorTypesAux_length ctors (i+1)]

/-- The complete mixed minor telescope has one entry per paired raw/view
constructor. -/
theorem GenerationChecked.minorTypes_length
    {source : VInductDecl} (gen : GenerationChecked source) :
    gen.minorTypes.length = gen.block.ctorPairs.length := by
  simpa [GenerationChecked.minorTypes] using
    gen.minorTypesAux_length gen.block.ctorPairs 0

/-- Positional lookup through mixed minor generation. -/
theorem GenerationChecked.minorTypesAux_getElem?
    {source : VInductDecl} (gen : GenerationChecked source) :
    ∀ (ctors : List NormalizedCtor) (i q : Nat),
      (gen.minorTypesAux ctors i)[q]? =
        ctors[q]?.map fun ctor =>
          VExpr.liftN (i+q)
            (GenerationChecked.minorType
              (source := source) ctor)
  | [], _, q => by simp [GenerationChecked.minorTypesAux]
  | _ :: _, _, 0 => by simp [GenerationChecked.minorTypesAux]
  | _ :: ctors, i, q+1 => by
    simp only [GenerationChecked.minorTypesAux,
      List.getElem?_cons_succ]
    rw [gen.minorTypesAux_getElem? ctors (i+1) q,
      show i+1+q = i+(q+1) by omega]

namespace GenerationEnv

variable {source : VInductDecl} {gen : GenerationChecked source}
  {env : VEnv} (S : GenerationEnv gen env)
include S

/-- One mixed generalized induction-hypothesis entry is a type. The bound
field keeps its raw domain; `emittedField_defeq` converts it to the retained
recursive-Pi view only at the semantic application point. -/
theorem recArgMinor_isType {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) {r : RecArg}
    (hrmem : r ∈ ctor.recArgsR source.uvars)
    (Δ : List VExpr) (p : Nat) (hΔ : Δ.length = p) :
    env.IsType (source.uvars + 1)
      (Δ ++
        (VExpr.liftTelN 1
          (ctor.fieldsR source.uvars source.nparams) 0).reverse ++
        (gen.motiveType :: gen.paramsTel.reverse))
      (r.minorIH
        (ctor.fieldsR source.uvars source.nparams).length p) := by
  obtain ⟨r₀, hr₀, rfl⟩ :=
    NormalizedCtor.recArgsR_mem hrmem
  obtain ⟨Bview, hBview, hrec⟩ :=
    S.viewRecArg_data hctor hr₀
  let ls := VLevel.params' source.uvars 1
  let r := r₀.instL ls
  let Bs := ctor.fieldsR source.uvars source.nparams
  let m := Bs.length
  let j := r₀.fieldIndex
  let Fs := VExpr.liftTelN 1 Bs 0
  let As := r.minorBinders m p
  let idxs := r.indices.map fun e =>
    (e.liftN 1 (r.fieldIndex+r.binders.length)).liftN
      (m-r.fieldIndex+p) r.binders.length
  let Γ := Δ ++ Fs.reverse ++
    (gen.motiveType :: gen.paramsTel.reverse)
  have hjm : j < m := by
    have hview := S.viewRecArg_lt hctor hr₀
    have hfields :=
      (gen.shape.2.2.2.2.2 ctor hctor).2.2.2
    simp only [j, m, Bs, NormalizedCtor.fieldsR_length]
    omega
  have hjraw :
      r₀.fieldIndex < (ctor.rawFields source.nparams).length := by
    simpa [j, m, Bs, NormalizedCtor.fieldsR_length] using hjm
  let Braw := (ctor.rawFields source.nparams)[r₀.fieldIndex]
  have hBraw :
      (ctor.rawFields source.nparams)[r₀.fieldIndex]? =
        some Braw :=
    List.getElem?_eq_getElem hjraw
  have hFsLen : Fs.length = m := by
    simp [Fs, m, VExpr.liftTelN_length]
  have hstackLen :
      (Δ ++ (Fs.drop j).reverse).length = m-j+p := by
    simp only [List.length_append, List.length_reverse,
      List.length_drop, hFsLen, hΔ]
    omega
  have ht := S.recArg_transport hctor hr₀ [gen.motiveType] rfl
    (Δ ++ (Fs.drop j).reverse) hstackLen
  simp only [List.length_singleton, RecArg.instL] at ht
  have hctx :
      (Δ ++ (Fs.drop j).reverse) ++
          ((VExpr.liftTelN 1 (Bs.take j) 0).reverse ++
            ([gen.motiveType] ++ gen.paramsTel.reverse)) = Γ := by
    dsimp only [Γ, Fs]
    rw [← VExpr.liftTelN_take, List.append_assoc,
      ← List.append_assoc
        ((VExpr.liftTelN 1 Bs 0).drop j).reverse,
      ← List.reverse_append, List.take_append_drop,
      List.singleton_append, ← List.append_assoc]
  dsimp only [j] at ht hctx
  have htel : env.OnTel (source.uvars + 1) Γ As := by
    rw [hctx] at ht
    simpa [r, As, m, j, Bs, RecArg.instL] using ht.1
  have hsp : env.SpineWF (source.uvars + 1)
      (As.reverse ++ Γ)
      (VExpr.forallN
        (VExpr.liftTelN
          (m+p+r.binders.length+1) gen.idxTel 0)
        (.sort (gen.block.checked.resultLevel.inst ls)))
      idxs
      (.sort (gen.block.checked.resultLevel.inst ls)) := by
    rw [hctx] at ht
    simpa [r, As, idxs, m, j, Bs, ls, RecArg.instL,
      List.append_assoc,
      show j + r₀.binders.length + 1 + (m-j+p) =
        m+p+r₀.binders.length+1 from by omega] using ht.2
  have hF : Γ[m-1-j+p]? =
      some ((Braw.instL ls).liftN 1 j) := by
    dsimp only [Γ, Fs]
    rw [getElem?_stack_mid Δ
        (VExpr.liftTelN 1 Bs 0).reverse
        (gen.motiveType :: gen.paramsTel.reverse)
        (i := m-1-j+p) (by rw [hΔ]; omega)
        (by simp only [hΔ, List.length_reverse,
          VExpr.liftTelN_length]; omega),
      show m - 1 - j + p - Δ.length = m - 1 - j from by
        rw [hΔ]
        omega,
      List.getElem?_reverse (by rw [hFsLen]; omega),
      VExpr.liftTelN_length,
      show m - 1 - (m - 1 - j) = j from by omega,
      VExpr.liftTelN_getElem?,
      NormalizedCtor.fieldsR_getElem?, hBraw]
    simp [ls]
  have hlu := Lookup.of_getElem? hF
  rw [show m-1-j+p+1 = m-j+p from by omega] at hlu
  dsimp only [j, r] at hlu
  have hf0 := VEnv.HasType.bvar
    (env := env) (U := source.uvars + 1) hlu
  obtain ⟨u, hdom₀⟩ :=
    S.emittedField_defeq hctor hBraw hBview
  have hdom₁ := hdom₀.instL
    (U' := source.uvars + 1) VLevel.params'_one_wf
  have hprefix :
      (((ctor.rawFields source.nparams).take r₀.fieldIndex).reverse ++
        gen.block.rawParams.reverse).map (VExpr.instL ls) =
      (Bs.take r₀.fieldIndex).reverse ++
        gen.paramsTel.reverse := by
    simp [Bs, ls, NormalizedCtor.fieldsR,
      GenerationChecked.paramsTel, List.map_reverse, List.map_take]
  rw [hprefix] at hdom₁
  have hjlen : (Bs.take r₀.fieldIndex).length =
      r₀.fieldIndex := by
    simp only [Bs, NormalizedCtor.fieldsR,
      List.length_take, List.length_map]
    omega
  have Wmid := Ctx.LiftN.consTel (n := 1)
    (Bs.take r₀.fieldIndex)
    (Ctx.LiftN.zero (Γ := gen.paramsTel.reverse)
      [gen.motiveType])
  rw [hjlen, Nat.add_zero] at Wmid
  have hdom₂ := hdom₁.weakN S.ord Wmid
  have Wstack := Ctx.LiftN.zero
    (Γ := (VExpr.liftTelN 1 (Bs.take j) 0).reverse ++
      ([gen.motiveType] ++ gen.paramsTel.reverse))
    (Δ ++ (Fs.drop j).reverse) (h := hstackLen)
  have hdom₃ := hdom₂.weakN S.ord Wstack
  rw [hctx] at hdom₃
  have hfView := hdom₃.defeq hf0
  have hfield := recArg_minor_fieldType hrec m p
    (by simpa [j] using hjm)
  simp only [RecArg.instL] at hfield
  rw [hfield] at hfView
  have hf := hfView.weakN S.ord
    (Ctx.LiftN.zero (Γ := Γ) As.reverse)
  have hmajor := VEnv.HasType.appN_selfSpine
    (env := env) (U := source.uvars + 1)
    (As := As)
    (B := VExpr.appN
      (.const gen.block.sourceType.name ls)
      (VExpr.bvarRevRange
        (m+p+r.binders.length+1) source.nparams ++ idxs))
    (Δ := []) (Γ := Γ) (by
      simpa [As, r, idxs, j, ls, RecArg.instL,
        List.length_reverse, List.map_map,
        Function.comp_def] using hf)
  simp only [List.length_nil, VExpr.liftN_zero,
    List.nil_append] at hmajor
  have hAsLen : As.length = r.binders.length := by
    simp [As, RecArg.minorBinders, VExpr.liftTelN_length]
  have hmajorHead :
      (VExpr.bvar (m-1-r.fieldIndex+p)).liftN As.length =
        .bvar (m-1-r.fieldIndex+p+r.binders.length) := by
    simp only [VExpr.liftN, liftVar_base]
    congr 1
    rw [hAsLen]
    omega
  change env.HasType (source.uvars + 1) (As.reverse ++ Γ)
    (((VExpr.bvar (m-1-r.fieldIndex+p)).liftN As.length).appN
      (VExpr.bvarRevRange 0 As.length))
    (VExpr.appN
      (.const gen.block.sourceType.name ls)
      (VExpr.bvarRevRange
        (m+p+r.binders.length+1) source.nparams ++ idxs)) at hmajor
  rw [hmajorHead, hAsLen] at hmajor
  have hMget :
      (As.reverse ++ Γ)[m+p+r.binders.length]? =
        some gen.motiveType := by
    have hM0 := getElem?_rstack3 As.reverse
      (Δ ++ Fs.reverse) gen.motiveType gen.paramsTel.reverse
      (i := m+p+r.binders.length)
      (by
        simp [As, RecArg.minorBinders, r, m, Fs, hΔ,
          VExpr.liftTelN_length, RecArg.instL]
        omega)
    simpa [Γ, List.append_assoc] using hM0
  have hM := VEnv.HasType.bvar
    (env := env) (U := source.uvars + 1)
    (Lookup.of_getElem? hMget)
  have hlen : idxs.length = gen.idxTel.length := by
    simpa [idxs, r, RecArg.instL,
      GenerationChecked.idxTel] using
      (S.viewRecArg_indices_length hctor hr₀).trans
        gen.shape.2.2.1.symm
  have hbody := gen.motiveVarApp_hasType
    (l := gen.block.checked.resultLevel.inst ls)
    hM hsp hlen hmajor
  refine IsType.forallN htel ⟨VLevel.param 0, ?_⟩
  simpa [RecArg.minorIH, r, As, idxs, m, Γ, Fs, Bs,
    List.append_assoc] using hbody

/-- The complete mixed functional-IH telescope is well formed at any suffix
and depth. -/
theorem ihs_onTel {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) :
    ∀ (rsSuf : List RecArg),
    (∀ r ∈ rsSuf, r ∈ ctor.recArgsR source.uvars) →
    ∀ (Δ : List VExpr) (p : Nat), Δ.length = p →
    env.OnTel (source.uvars + 1)
      (Δ ++
        (VExpr.liftTelN 1
          (ctor.fieldsR source.uvars source.nparams) 0).reverse ++
        (gen.motiveType :: gen.paramsTel.reverse))
      (ihsFromRecArgs
        (ctor.fieldsR source.uvars source.nparams).length rsSuf p)
  | [], _, _, _, _ => trivial
  | r :: rsSuf, hqs, Δ, p, hΔ =>
    ⟨S.recArgMinor_isType hctor
        (hqs r (.head _)) Δ p hΔ,
      GenerationEnv.ihs_onTel hctor rsSuf
        (fun q hq => hqs q (.tail _ hq))
        (_ :: Δ) (p+1) (by simp [hΔ])⟩

/-- The retained constructor result has exactly the checked family-index
arity. -/
theorem viewResultIndices_length {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) :
    ctor.view.resultIndices.length =
      gen.block.checked.indices.length := by
  obtain ⟨c, hc, hview⟩ := gen.viewCtor_ofDirect hctor
  have hstage :=
    (gen.block.checked.direct_anatomy.2.2.2.2.2 c hc).2.2
  have hlen := (stage3Ctor_eq hstage).2.1
  rw [hview]
  rw [gen.block.nparams_eq]
  simpa [CheckedCtor.ofDirect] using hlen

/-- Checked result-index spine semantics for a paired constructor. -/
theorem viewResultSpine {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) :
    env.SpineWF source.uvars
      (ctor.view.fields.reverse ++
        gen.block.checked.params.reverse)
      (VExpr.forallN
        (VExpr.liftTelN ctor.view.fields.length
          gen.block.checked.indices 0)
        (.sort gen.block.checked.resultLevel))
      ctor.view.resultIndices
      (.sort gen.block.checked.resultLevel) := by
  obtain ⟨c, hc, hview⟩ := gen.viewCtor_ofDirect hctor
  have h := (S.checked.2 c hc).2
  rw [hview]
  simpa [CheckedCtor.ofDirect, gen.block.uvars_eq,
    gen.block.nparams_eq] using h

/-- Constructor-result semantics transported to the exact raw emitted
field/parameter context and raw family-index telescope. -/
theorem rawResultSpine {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) :
    env.SpineWF source.uvars
      ((ctor.rawFields source.nparams).reverse ++
        gen.block.rawParams.reverse)
      (VExpr.forallN
        (VExpr.liftTelN
          (ctor.rawFields source.nparams).length
          gen.block.rawIndices 0)
        (.sort gen.block.checked.resultLevel))
      ctor.view.resultIndices
      (.sort gen.block.checked.resultLevel) := by
  have hctx := (S.ctorWF ctor hctor).emittedTel.ctx
  simp only [NormalizedCtor.emittedBinders,
    NormalizedCtor.viewBinders, List.reverse_append,
    List.append_nil] at hctx
  have hsp := (S.viewResultSpine hctor).defeqDFC S.ord
    (hctx.symm S.ord)
  have hfields :=
    (gen.shape.2.2.2.2.2 ctor hctor).2.2.2
  rw [← hfields] at hsp
  have hidx := S.rawIndexTel_defeq.weakN S.ord
    (Ctx.LiftN.zero (Γ := gen.block.rawParams.reverse)
      (ctor.rawFields source.nparams).reverse)
  rw [List.length_reverse] at hidx
  have hlen :
      ctor.view.resultIndices.length =
        (VExpr.liftTelN
          (ctor.rawFields source.nparams).length
          gen.block.rawIndices 0).length := by
    simp only [VExpr.liftTelN_length]
    exact (S.viewResultIndices_length hctor).trans
      gen.shape.2.2.1.symm
  exact hidx.spine_sort S.ord hsp hlen

/-- Transport the mixed constructor result spine into a minor or rule
context. -/
theorem result_transport {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs)
    (mid : List VExpr) {g : Nat} (hg : mid.length = g)
    (As₂ : List VExpr) {d : Nat} (hd : As₂.length = d) :
    env.SpineWF (source.uvars + 1)
      (As₂ ++
        ((VExpr.liftTelN g
          (ctor.fieldsR source.uvars source.nparams) 0).reverse ++
          (mid ++ gen.paramsTel.reverse)))
      (VExpr.forallN
        (VExpr.liftTelN
          ((ctor.fieldsR source.uvars source.nparams).length + g + d)
          gen.idxTel 0)
        (.sort (gen.block.checked.resultLevel.inst
          (VLevel.params' source.uvars 1))))
      ((ctor.resultIndicesR source.uvars).map fun e =>
        (e.liftN g
          (ctor.fieldsR source.uvars source.nparams).length).liftN d)
      (.sort (gen.block.checked.resultLevel.inst
        (VLevel.params' source.uvars 1))) := by
  let ls := VLevel.params' source.uvars 1
  have h1 := (S.rawResultSpine hctor).instL
    (U' := source.uvars + 1) VLevel.params'_one_wf
  rw [VExpr.instL_forallN, VExpr.liftTelN_instL,
    show
      (((ctor.rawFields source.nparams).reverse ++
          gen.block.rawParams.reverse).map (VExpr.instL ls)) =
        (ctor.fieldsR source.uvars source.nparams).reverse ++
          gen.paramsTel.reverse by
      simp [ls, NormalizedCtor.fieldsR,
        GenerationChecked.paramsTel, List.map_reverse],
    show
      (gen.block.rawIndices.map (VExpr.instL ls)) =
        gen.idxTel by rfl] at h1
  rw [← NormalizedCtor.fieldsR_length
    (source := source) ctor] at h1
  have W₁ := Ctx.LiftN.consTel (n := mid.length)
    (ctor.fieldsR source.uvars source.nparams)
    (Ctx.LiftN.zero (Γ := gen.paramsTel.reverse) mid)
  rw [Nat.add_zero] at W₁
  have h2 := h1.weakN S.ord W₁
  rw [VExpr.liftN_forallN, hg] at h2
  have h3 := h2.weakN S.ord
    (Ctx.LiftN.zero (Γ := _) As₂ (h := hd))
  rw [VExpr.liftN_forallN] at h3
  rw [VExpr.liftTelN_liftTelN_hi'
      (ctor.fieldsR source.uvars source.nparams).length
      g _ 0 (by omega),
    VExpr.liftTelN_liftTelN] at h3
  simpa [ls, NormalizedCtor.resultIndicesR,
    VExpr.instL, VExpr.liftN, List.map_map,
    Function.comp_def, List.append_assoc] using h3

/-- The exact emitted constructor application transported into recursor
universes, before inserting the motive or any induction-hypothesis stack. -/
theorem ctorApp_emitted_rec {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) :
    env.HasType (source.uvars + 1)
      ((ctor.fieldsR source.uvars source.nparams).reverse ++
        gen.paramsTel.reverse)
      (VExpr.appN
        (.const ctor.raw.name
          (VLevel.params' source.uvars 1))
        (VExpr.bvarRevRange
            (ctor.fieldsR source.uvars source.nparams).length
            source.nparams ++
          VExpr.bvarRevRange 0
            (ctor.fieldsR source.uvars source.nparams).length))
      (VExpr.appN
        (.const gen.block.sourceType.name
          (VLevel.params' source.uvars 1))
        (VExpr.bvarRevRange
            (ctor.fieldsR source.uvars source.nparams).length
            source.nparams ++
          ctor.resultIndicesR source.uvars)) := by
  let ls := VLevel.params' source.uvars 1
  have h := (S.ctorApp_emitted_decl hctor).instL
    (U' := source.uvars + 1) VLevel.params'_one_wf
  rw [← NormalizedCtor.fieldsR_length
    (source := source) ctor] at h
  simpa [ls, NormalizedCtor.fieldsR,
    GenerationChecked.paramsTel,
    NormalizedCtor.resultTarget,
    NormalizedCtor.resultIndicesR,
    VExpr.instL_appN, List.map_append,
    bvarRevRange_instL, List.map_reverse,
    VExpr.instL, VLevel.params_map_inst_params'] using h

/-- Transport the emitted constructor application under binders inserted
between parameters and fields, then under an arbitrary top stack. -/
theorem ctorApp_transport {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs)
    (mid : List VExpr) {g : Nat} (hg : mid.length = g)
    (As₂ : List VExpr) {d : Nat} (hd : As₂.length = d) :
    env.HasType (source.uvars + 1)
      (As₂ ++
        ((VExpr.liftTelN g
          (ctor.fieldsR source.uvars source.nparams) 0).reverse ++
          (mid ++ gen.paramsTel.reverse)))
      (VExpr.appN
        (.const ctor.raw.name
          (VLevel.params' source.uvars 1))
        (VExpr.bvarRevRange
            (d + (g +
              (ctor.fieldsR source.uvars source.nparams).length))
            source.nparams ++
          VExpr.bvarRevRange d
            (ctor.fieldsR source.uvars source.nparams).length))
      (VExpr.appN
        (.const gen.block.sourceType.name
          (VLevel.params' source.uvars 1))
        (VExpr.bvarRevRange
            (d + (g +
              (ctor.fieldsR source.uvars source.nparams).length))
            source.nparams ++
          (ctor.resultIndicesR source.uvars).map fun e =>
            (e.liftN g
              (ctor.fieldsR source.uvars source.nparams).length).liftN d)) := by
  let Bs := ctor.fieldsR source.uvars source.nparams
  have W₁ := Ctx.LiftN.consTel (n := mid.length) Bs
    (Ctx.LiftN.zero (Γ := gen.paramsTel.reverse) mid)
  rw [Nat.add_zero] at W₁
  have h₁ := (S.ctorApp_emitted_rec hctor).weakN S.ord W₁
  rw [hg] at h₁
  have hmid : env.HasType (source.uvars + 1)
      ((VExpr.liftTelN g Bs 0).reverse ++
        (mid ++ gen.paramsTel.reverse))
      (VExpr.appN
        (.const ctor.raw.name
          (VLevel.params' source.uvars 1))
        (VExpr.bvarRevRange (g + Bs.length) source.nparams ++
          VExpr.bvarRevRange 0 Bs.length))
      (VExpr.appN
        (.const gen.block.sourceType.name
          (VLevel.params' source.uvars 1))
        (VExpr.bvarRevRange (g + Bs.length) source.nparams ++
          (ctor.resultIndicesR source.uvars).map
            (VExpr.liftN g · Bs.length))) := by
    simpa [Bs, VExpr.liftN_appN, List.map_append,
      bvarRevRange_liftN_ge _ _ _ _ (Nat.le_refl _),
      VExpr.bvarRevRange_liftN_high
        Bs.length 0 g Bs.length (by omega),
      VExpr.liftN] using h₁
  have htop := hmid.weakN S.ord
    (Ctx.LiftN.zero (Γ := _) As₂ (h := hd))
  simpa [Bs, VExpr.liftN_appN, List.map_append,
    bvarRevRange_liftN_ge _ _ _ _ (Nat.zero_le _),
    VExpr.liftN, List.map_map, Function.comp_def,
    List.append_assoc] using htop

/-- Constructor application in the exact mixed minor-premise context. -/
theorem ctorAppMinor_hasType {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) (Δ : List VExpr) :
    env.HasType (source.uvars + 1)
      (Δ ++
        (VExpr.liftTelN 1
          (ctor.fieldsR source.uvars source.nparams) 0).reverse ++
        (gen.motiveType :: gen.paramsTel.reverse))
      (VExpr.appN
        (.const ctor.raw.name
          (VLevel.params' source.uvars 1))
        (VExpr.bvarRevRange
            (Δ.length +
              (ctor.fieldsR source.uvars source.nparams).length + 1)
            source.nparams ++
          VExpr.bvarRevRange Δ.length
            (ctor.fieldsR source.uvars source.nparams).length))
      (VExpr.appN
        (.const gen.block.sourceType.name
          (VLevel.params' source.uvars 1))
        (VExpr.bvarRevRange
            (Δ.length +
              (ctor.fieldsR source.uvars source.nparams).length + 1)
            source.nparams ++
          (ctor.resultIndicesR source.uvars).map fun e =>
            (e.liftN 1
              (ctor.fieldsR source.uvars source.nparams).length).liftN
                Δ.length)) := by
  have h := S.ctorApp_transport hctor [gen.motiveType]
    (g := 1) rfl Δ (d := Δ.length) rfl
  rw [VExpr.bvarRevRange_congr source.nparams
    (show
      Δ.length +
          (1 +
            (ctor.fieldsR source.uvars source.nparams).length) =
        Δ.length +
          (ctor.fieldsR source.uvars source.nparams).length + 1 by
      omega)] at h
  simpa [List.append_assoc] using h

/-- The exact raw field telescope used by a mixed minor is well formed after
universe instantiation and insertion of the motive. -/
theorem fields_onTel_minor {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) :
    env.OnTel (source.uvars + 1)
      (gen.motiveType :: gen.paramsTel.reverse)
      (VExpr.liftTelN 1
        (ctor.fieldsR source.uvars source.nparams) 0) := by
  have hemitted : env.OnTel source.uvars []
      (gen.block.rawParams ++
        ctor.rawFields source.nparams) := by
    simpa [NormalizedCtor.emittedBinders] using
      (S.ctorWF ctor hctor).rawEmitted_onTel
  have hfields₀ := (OnTel.of_append
    (As := gen.block.rawParams) hemitted).2
  have hfields₁ := hfields₀.instL
    (U' := source.uvars + 1) VLevel.params'_one_wf
  have hfields₂ : env.OnTel (source.uvars + 1)
      gen.paramsTel.reverse
      (ctor.fieldsR source.uvars source.nparams) := by
    simpa [GenerationChecked.paramsTel,
      NormalizedCtor.fieldsR, List.map_reverse] using hfields₁
  have hout := hfields₂.weakN S.ord
    (Ctx.LiftN.zero (Γ := gen.paramsTel.reverse)
      [gen.motiveType])
  simpa using hout

/-- Every mixed constructor minor is a type over the raw parameter telescope
and mixed motive. Raw field syntax is preserved; recursive classifications
and result indices come from the checked view. -/
theorem minor_isType {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) :
    env.IsType (source.uvars + 1)
      (gen.motiveType :: gen.paramsTel.reverse)
      (GenerationChecked.minorType
        (source := source) ctor) := by
  let Bs := ctor.fieldsR source.uvars source.nparams
  let m := Bs.length
  let rs := ctor.recArgsR source.uvars
  let IHs := ihsFromRecArgs m rs 0
  let Fs := VExpr.liftTelN 1 Bs 0
  let Γ := IHs.reverse ++
    (Fs.reverse ++
      (gen.motiveType :: gen.paramsTel.reverse))
  simp only [GenerationChecked.minorType]
  refine IsType.forallN (by
    simpa [Bs] using S.fields_onTel_minor hctor) ?_
  refine IsType.forallN (by
    simpa [Bs, m, rs, IHs, Fs, List.append_assoc] using
      S.ihs_onTel hctor rs (fun r hr => hr) [] 0 rfl) ?_
  have hrlen : IHs.reverse.length = rs.length := by
    simp [IHs, ihsFromRecArgs_length]
  have hMget : Γ[m + rs.length]? =
      some gen.motiveType := by
    have h := getElem?_rstack3 IHs.reverse Fs.reverse
      gen.motiveType gen.paramsTel.reverse
      (i := m + rs.length)
      (by
        simp [IHs, Fs, m, ihsFromRecArgs_length,
          VExpr.liftTelN_length]
        omega)
    simpa [Γ] using h
  have hM : env.HasType (source.uvars + 1) Γ
      (.bvar (m + rs.length))
      (gen.motiveType.liftN (m + rs.length + 1)) :=
    VEnv.HasType.bvar (Lookup.of_getElem? hMget)
  have hSp := S.result_transport hctor [gen.motiveType]
    (g := 1) rfl IHs.reverse
    (d := rs.length) hrlen
  rw [show m + 1 + rs.length =
    m + rs.length + 1 by omega] at hSp
  have hSp' : env.SpineWF (source.uvars + 1) Γ
      (VExpr.forallN
        (VExpr.liftTelN (m + rs.length + 1)
          gen.idxTel 0)
        (.sort (gen.block.checked.resultLevel.inst
          (VLevel.params' source.uvars 1))))
      ((ctor.resultIndicesR source.uvars).map fun e =>
        (e.liftN 1 m).liftN rs.length)
      (.sort (gen.block.checked.resultLevel.inst
        (VLevel.params' source.uvars 1))) := by
    simpa [Γ, Fs, Bs, m, List.append_assoc] using hSp
  have hlen :
      ((ctor.resultIndicesR source.uvars).map fun e =>
        (e.liftN 1 m).liftN rs.length).length =
        gen.idxTel.length := by
    simp only [List.length_map, NormalizedCtor.resultIndicesR,
      GenerationChecked.idxTel]
    exact (S.viewResultIndices_length hctor).trans
      gen.shape.2.2.1.symm
  have hctorApp := S.ctorAppMinor_hasType hctor IHs.reverse
  rw [hrlen,
    VExpr.bvarRevRange_congr source.nparams
      (show rs.length + m + 1 = m + rs.length + 1 by omega)] at hctorApp
  have hctorApp' : env.HasType (source.uvars + 1) Γ
      (VExpr.appN
        (.const ctor.raw.name
          (VLevel.params' source.uvars 1))
        (VExpr.bvarRevRange
            (m + rs.length + 1) source.nparams ++
          VExpr.bvarRevRange rs.length m))
      (VExpr.appN
        (.const gen.block.sourceType.name
          (VLevel.params' source.uvars 1))
        (VExpr.bvarRevRange
            (m + rs.length + 1) source.nparams ++
          (ctor.resultIndicesR source.uvars).map fun e =>
            (e.liftN 1 m).liftN rs.length)) := by
    simpa [Γ, Fs, Bs, m, IHs, rs,
      List.append_assoc] using hctorApp
  have hbody := gen.motiveVarApp_hasType hM hSp' hlen hctorApp'
  rw [VExpr.bvarRevRange_congr source.nparams
    (show m + rs.length + 1 =
      rs.length + m + 1 by omega)] at hbody
  exact ⟨.param 0, by
    simpa [Γ, Fs, Bs, m, rs, IHs,
      List.append_assoc] using hbody⟩

/-- The mixed raw parameter telescope is well formed in recursor universes. -/
theorem paramsTel_onTel :
    env.OnTel (source.uvars + 1) [] gen.paramsTel := by
  have h := S.rawFamily_onTel.instL
    (U' := source.uvars + 1) VLevel.params'_one_wf
  have h' : env.OnTel (source.uvars + 1) []
      (gen.paramsTel ++ gen.idxTel) := by
    simpa [GenerationChecked.paramsTel,
      GenerationChecked.idxTel] using h
  exact h'.of_append.1

/-- The mixed raw index telescope is well formed over the mixed parameters. -/
theorem idxTel_onTel :
    env.OnTel (source.uvars + 1)
      gen.paramsTel.reverse gen.idxTel := by
  have h := S.rawFamily_onTel.instL
    (U' := source.uvars + 1) VLevel.params'_one_wf
  have h' : env.OnTel (source.uvars + 1) []
      (gen.paramsTel ++ gen.idxTel) := by
    simpa [GenerationChecked.paramsTel,
      GenerationChecked.idxTel] using h
  simpa using h'.of_append.2

/-- Any suffix of paired constructors generates a well-formed mixed minor
telescope at its positional depth. -/
theorem minorTypesAux_onTel :
    ∀ (ctors : List NormalizedCtor),
      (∀ ctor ∈ ctors, ctor ∈ gen.block.ctorPairs) →
      ∀ (Δ : List VExpr) (i : Nat), Δ.length = i →
        env.OnTel (source.uvars + 1)
          (Δ ++
            (gen.motiveType :: gen.paramsTel.reverse))
          (gen.minorTypesAux ctors i)
  | [], _, _, _, _ => trivial
  | ctor :: ctors, hsub, Δ, i, hΔ =>
    ⟨by
      rw [← hΔ]
      exact (S.minor_isType
        (hsub ctor (.head _))).weakN S.ord
          (.zero Δ),
    GenerationEnv.minorTypesAux_onTel ctors
      (fun ctor hctor => hsub ctor (.tail _ hctor))
      (_ :: Δ) (i+1) (by simp [hΔ])⟩

/-- The complete mixed minor telescope is well formed over parameters and
motive. -/
theorem minorTypes_onTel :
    env.OnTel (source.uvars + 1)
      (gen.motiveType :: gen.paramsTel.reverse)
      gen.minorTypes := by
  simpa [GenerationChecked.minorTypes] using
    S.minorTypesAux_onTel gen.block.ctorPairs
      (fun _ h => h) [] 0 rfl

/-- Transport the fully applied raw family under binders inserted below its
indices and then under an arbitrary top stack. -/
theorem familyApp_transport
    (mid : List VExpr) {g : Nat} (hg : mid.length = g)
    (As₂ : List VExpr) {d : Nat} (hd : As₂.length = d) :
    env.HasType (source.uvars + 1)
      (As₂ ++
        ((VExpr.liftTelN g gen.idxTel 0).reverse ++
          (mid ++ gen.paramsTel.reverse)))
      (VExpr.appN
        (.const gen.block.sourceType.name
          (VLevel.params' source.uvars 1))
        (VExpr.bvarRevRange
            (d + (g + gen.idxTel.length))
            source.nparams ++
          VExpr.bvarRevRange d gen.idxTel.length))
      (.sort (gen.block.checked.resultLevel.inst
        (VLevel.params' source.uvars 1))) := by
  have W₁ := Ctx.LiftN.consTel (n := mid.length) gen.idxTel
    (Ctx.LiftN.zero (Γ := gen.paramsTel.reverse) mid)
  rw [Nat.add_zero] at W₁
  have h₁ := S.familyApp_hasType.weakN S.ord W₁
  rw [hg] at h₁
  have hmid : env.HasType (source.uvars + 1)
      ((VExpr.liftTelN g gen.idxTel 0).reverse ++
        (mid ++ gen.paramsTel.reverse))
      (VExpr.appN
        (.const gen.block.sourceType.name
          (VLevel.params' source.uvars 1))
        (VExpr.bvarRevRange
            (g + gen.idxTel.length) source.nparams ++
          VExpr.bvarRevRange 0 gen.idxTel.length))
      (.sort (gen.block.checked.resultLevel.inst
        (VLevel.params' source.uvars 1))) := by
    simpa [VExpr.liftN_appN, List.map_append,
      bvarRevRange_liftN_ge _ _ _ _ (Nat.le_refl _),
      VExpr.bvarRevRange_liftN_high
        gen.idxTel.length 0 g gen.idxTel.length (by omega),
      VExpr.liftN] using h₁
  have htop := hmid.weakN S.ord
    (Ctx.LiftN.zero (Γ := _) As₂ (h := hd))
  simpa [VExpr.liftN_appN, List.map_append,
    bvarRevRange_liftN_ge _ _ _ _ (Nat.zero_le _),
    VExpr.liftN, List.append_assoc] using htop

/-- The mixed recursor type is well formed. Its telescope retains raw
parameter and index syntax while its motive and minors use the checked
recursive classification. -/
theorem recType_isType :
    env.IsType (source.uvars + 1) [] gen.recType := by
  refine IsType.forallN S.paramsTel_onTel ?_
  simp only [List.append_nil]
  refine IsType.forallE S.motive_isType ?_
  refine IsType.forallN S.minorTypes_onTel ?_
  have hI : env.OnTel (source.uvars + 1)
      (gen.minorTypes.reverse ++
        (gen.motiveType :: gen.paramsTel.reverse))
      (VExpr.liftTelN (gen.block.ctorPairs.length + 1)
        gen.idxTel 0) := by
    have h := S.idxTel_onTel.weakN S.ord
      (Ctx.LiftN.zero
        (n := gen.block.ctorPairs.length + 1)
        (Γ := gen.paramsTel.reverse)
        (gen.minorTypes.reverse ++ [gen.motiveType])
        (h := by simp [gen.minorTypes_length]))
    simpa [List.append_assoc] using h
  refine IsType.forallN hI ?_
  have hmaj₀ := S.familyApp_transport
    (gen.minorTypes.reverse ++ [gen.motiveType])
    (g := gen.block.ctorPairs.length + 1)
    (by simp [gen.minorTypes_length])
    [] (d := 0) rfl
  rw [VExpr.bvarRevRange_congr source.nparams
    (show
      0 + ((gen.block.ctorPairs.length + 1) +
        gen.idxTel.length) =
      gen.idxTel.length + gen.block.ctorPairs.length + 1 by omega)] at hmaj₀
  have hmaj : env.HasType (source.uvars + 1)
      ((VExpr.liftTelN (gen.block.ctorPairs.length + 1)
          gen.idxTel 0).reverse ++
        (gen.minorTypes.reverse ++
          (gen.motiveType :: gen.paramsTel.reverse)))
      (VExpr.appN
        (.const gen.block.sourceType.name
          (VLevel.params' source.uvars 1))
        (VExpr.bvarRevRange
            (gen.idxTel.length +
              gen.block.ctorPairs.length + 1)
            source.nparams ++
          VExpr.bvarRevRange 0 gen.idxTel.length))
      (.sort (gen.block.checked.resultLevel.inst
        (VLevel.params' source.uvars 1))) := by
    simpa [List.append_assoc] using hmaj₀
  refine IsType.forallE ⟨_, hmaj⟩ ?_
  have hM := getElem?_rstack3
    [VExpr.appN
      (.const gen.block.sourceType.name
        (VLevel.params' source.uvars 1))
      (VExpr.bvarRevRange
          (gen.idxTel.length +
            gen.block.ctorPairs.length + 1)
          source.nparams ++
        VExpr.bvarRevRange 0 gen.idxTel.length)]
    ((VExpr.liftTelN (gen.block.ctorPairs.length + 1)
        gen.idxTel 0).reverse ++
      gen.minorTypes.reverse)
    gen.motiveType gen.paramsTel.reverse
    (i := gen.idxTel.length +
      gen.block.ctorPairs.length + 1)
    (by
      simp only [List.length_singleton, List.length_append,
        List.length_reverse, VExpr.liftTelN_length,
        gen.minorTypes_length]
      omega)
  have hmlu := Lookup.of_getElem? (by
    simpa only [List.singleton_append,
      List.append_assoc] using hM)
  rw [show gen.motiveType.liftN
        (gen.idxTel.length +
          gen.block.ctorPairs.length + 1 + 1) =
      (gen.motiveType.liftN
        (gen.block.ctorPairs.length + 1)).liftN
          (gen.idxTel.length + 1) from by
      rw [VExpr.liftN_liftN]
      congr 1
      omega,
    gen.motiveType_liftN] at hmlu
  have hfun : env.HasType (source.uvars + 1)
      (VExpr.appN
          (.const gen.block.sourceType.name
            (VLevel.params' source.uvars 1))
          (VExpr.bvarRevRange
              (gen.idxTel.length +
                gen.block.ctorPairs.length + 1)
              source.nparams ++
            VExpr.bvarRevRange 0 gen.idxTel.length) ::
        ((VExpr.liftTelN
            (gen.block.ctorPairs.length + 1)
            gen.idxTel 0).reverse ++
          (gen.minorTypes.reverse ++
            (gen.motiveType :: gen.paramsTel.reverse))))
      (.bvar
        (gen.idxTel.length +
          gen.block.ctorPairs.length + 1))
      ((VExpr.forallN
        (VExpr.liftTelN
          (gen.block.ctorPairs.length + 1)
          gen.idxTel 0)
        (.forallE
          (VExpr.appN
            (.const gen.block.sourceType.name
              (VLevel.params' source.uvars 1))
            (VExpr.bvarRevRange
                (gen.block.ctorPairs.length + 1 +
                  gen.idxTel.length)
                source.nparams ++
              VExpr.bvarRevRange 0 gen.idxTel.length))
          (.sort (.param 0)))).liftN
        (1 + (VExpr.liftTelN
          (gen.block.ctorPairs.length + 1)
          gen.idxTel 0).length)) := by
    exact .bvar (by
      simpa [List.append_assoc, VExpr.liftTelN_length,
        Nat.add_comm] using hmlu)
  have hMapp := HasType.appN_selfSpine
    (As := VExpr.liftTelN
      (gen.block.ctorPairs.length + 1)
      gen.idxTel 0)
    (Δ := [VExpr.appN
      (.const gen.block.sourceType.name
        (VLevel.params' source.uvars 1))
      (VExpr.bvarRevRange
          (gen.idxTel.length +
            gen.block.ctorPairs.length + 1)
          source.nparams ++
        VExpr.bvarRevRange 0 gen.idxTel.length)])
    (Γ := gen.minorTypes.reverse ++
      (gen.motiveType :: gen.paramsTel.reverse))
    (f := .bvar
      (gen.idxTel.length +
        gen.block.ctorPairs.length + 1))
    hfun
  have h0 :
      (VExpr.appN
          (.const gen.block.sourceType.name
            (VLevel.params' source.uvars 1))
          (VExpr.bvarRevRange
              (gen.idxTel.length +
                gen.block.ctorPairs.length + 1)
              source.nparams ++
            VExpr.bvarRevRange 0 gen.idxTel.length) ::
        ((VExpr.liftTelN
            (gen.block.ctorPairs.length + 1)
            gen.idxTel 0).reverse ++
          (gen.minorTypes.reverse ++
            (gen.motiveType :: gen.paramsTel.reverse))))[0]? =
        some (VExpr.appN
          (.const gen.block.sourceType.name
            (VLevel.params' source.uvars 1))
          (VExpr.bvarRevRange
              (gen.idxTel.length +
                gen.block.ctorPairs.length + 1)
              source.nparams ++
            VExpr.bvarRevRange 0 gen.idxTel.length)) := rfl
  have harg := HasType.bvar
    (env := env) (U := source.uvars + 1)
    (Lookup.of_getElem? h0)
  have harg' : env.HasType (source.uvars + 1)
      ([VExpr.appN
          (.const gen.block.sourceType.name
            (VLevel.params' source.uvars 1))
          (VExpr.bvarRevRange
              (gen.idxTel.length +
                gen.block.ctorPairs.length + 1)
              source.nparams ++
            VExpr.bvarRevRange 0 gen.idxTel.length)] ++
        (VExpr.liftTelN
          (gen.block.ctorPairs.length + 1)
          gen.idxTel 0).reverse ++
        (gen.minorTypes.reverse ++
          (gen.motiveType :: gen.paramsTel.reverse)))
      (.bvar 0)
      ((VExpr.appN
        (.const gen.block.sourceType.name
          (VLevel.params' source.uvars 1))
        (VExpr.bvarRevRange
            (gen.block.ctorPairs.length + 1 +
              gen.idxTel.length)
            source.nparams ++
          VExpr.bvarRevRange 0 gen.idxTel.length)).liftN 1) := by
    simpa [List.append_assoc, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc] using harg
  have happ := HasType.app hMapp harg'
  exact ⟨_, by
    simpa [GenerationChecked.recType, List.append_assoc,
      VExpr.liftTelN_length] using happ⟩

/-- The mixed generated recursor constant is well formed. -/
theorem recursor_wf : gen.recursor.WF env :=
  S.recType_isType

end GenerationEnv

theorem minorTypes_getElem? {U : Nat} {T : Name} {np : Nat} {ty : VInductiveType} :
    ∀ (cs : List VConstVal) (i₀ q : Nat),
    (minorTypes U T np ty cs i₀)[q]? =
      cs[q]?.map fun c => VExpr.liftN (i₀+q) (minorType U T np ty c)
  | [], _, q => by simp [minorTypes]
  | c :: cs, i₀, 0 => by simp [minorTypes]
  | c :: cs, i₀, q+1 => by
    simp only [minorTypes, List.getElem?_cons_succ]
    rw [minorTypes_getElem? cs (i₀+1) q, show i₀+1+q = i₀+(q+1) from by omega]

theorem minorTypesRec_getElem? {U : Nat} {T : Name} {np : Nat} {ty : VInductiveType} :
    ∀ (cs : List VConstVal) (i₀ q : Nat),
    (minorTypesRec U T np ty cs i₀)[q]? =
      cs[q]?.map fun c => VExpr.liftN (i₀+q) (minorTypeRec U T np ty c)
  | [], _, q => by simp [minorTypesRec]
  | c :: cs, i₀, 0 => by simp [minorTypesRec]
  | c :: cs, i₀, q+1 => by
    simp only [minorTypesRec, List.getElem?_cons_succ]
    rw [minorTypesRec_getElem? cs (i₀+1) q,
      show i₀+1+q = i₀+(q+1) from by omega]

theorem recApp'_levelWF {U : Nat} {T : Name} {np off : Nat} :
    (recApp' U T np off).LevelWF (U+1) :=
  VExpr.LevelWF.appN (f := .const T (VLevel.params' U 1)) VLevel.params'_one_wf
    (bvarRevRange_levelWF _ _)

theorem idxTel_length {U np : Nat} {ty : VInductiveType} :
    (idxTel U np ty).length = (ctorFields (VExpr.dropN np ty.type)).length :=
  List.length_map ..

theorem idxTel_levelWF {U np : Nat} {ty : VInductiveType} :
    ∀ A ∈ idxTel U np ty, A.LevelWF (U+1) := by
  intro A hA
  obtain ⟨A₀, -, rfl⟩ := List.mem_map.1 hA
  exact VExpr.LevelWF.instL VLevel.params'_one_wf

theorem ctorIdxs_length {U np : Nat} {c : VConstVal} :
    (ctorIdxs U np c).length =
      (recFieldIdxs np (VExpr.resultOf (VExpr.dropN np c.type))).length :=
  List.length_map ..

theorem ctorIdxs_levelWF {U np : Nat} {c : VConstVal} :
    ∀ e ∈ ctorIdxs U np c, e.LevelWF (U+1) := by
  intro e he
  obtain ⟨e₀, -, rfl⟩ := List.mem_map.1 he
  exact VExpr.LevelWF.instL VLevel.params'_one_wf

theorem recPairsR_lt {U : Nat} {T : Name} {np ni : Nat} {c : VConstVal} :
    ∀ q ∈ recPairsR U T np ni c, q.1 < (ctorFields (VExpr.dropN np c.type)).length := by
  intro q hq
  obtain ⟨⟨j, idxs⟩, hmem, rfl⟩ := List.mem_map.1 hq
  simpa using recPairs_lt _ hmem

theorem recPairsR_idx_levelWF {U : Nat} {T : Name} {np ni : Nat} {c : VConstVal} :
    ∀ q ∈ recPairsR U T np ni c, ∀ e ∈ q.2, e.LevelWF (U+1) := by
  intro q hq e he
  obtain ⟨⟨j, idxs⟩, -, rfl⟩ := List.mem_map.1 hq
  obtain ⟨e₀, -, rfl⟩ := List.mem_map.1 he
  exact VExpr.LevelWF.instL VLevel.params'_one_wf

/-- Unpack a recursor-universe recursive position: the underlying field and
its (declaration-universe) index arguments. -/
theorem recPairsR_mem {U : Nat} {T : Name} {np ni : Nat} {c : VConstVal} {q}
    (hq : q ∈ recPairsR U T np ni c) :
    ∃ B, (ctorFields (VExpr.dropN np c.type))[q.1]? = some B ∧
      isRecField U T np ni q.1 B = true ∧
      q.2 = (recFieldIdxs np B).map (VExpr.instL (VLevel.params' U 1)) := by
  obtain ⟨⟨j, idxs⟩, hmem, rfl⟩ := List.mem_map.1 hq
  obtain ⟨B, hB, hrec, hidx⟩ := recPairs_getElem _ hmem
  exact ⟨B, by simpa using hB, hrec, by simp only []; rw [show idxs = recFieldIdxs np B from hidx]⟩

/-- Recursor-universe transport preserves each recursive argument's source
field position. -/
theorem recArgsR_lt {U : Nat} {T : Name} {np ni : Nat} {c : VConstVal} :
    ∀ r ∈ recArgsR U T np ni c,
      r.fieldIndex < (ctorFields (VExpr.dropN np c.type)).length := by
  intro r hr
  obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.1 hr
  simpa [RecArg.instL] using recArgs_lt _ hr₀

/-- Every generated recursive-target index is level-well-formed in the
recursor universe context. -/
theorem recArgsR_idx_levelWF {U : Nat} {T : Name} {np ni : Nat} {c : VConstVal} :
    ∀ r ∈ recArgsR U T np ni c, ∀ e ∈ r.indices, e.LevelWF (U+1) := by
  intro r hr e he
  obtain ⟨r₀, -, rfl⟩ := List.mem_map.1 hr
  obtain ⟨e₀, -, rfl⟩ := List.mem_map.1 he
  exact VExpr.LevelWF.instL VLevel.params'_one_wf

/-- Every generated recursive-Pi domain is level-well-formed after universe
transport. -/
theorem recArgsR_binder_levelWF {U : Nat} {T : Name} {np ni : Nat} {c : VConstVal} :
    ∀ r ∈ recArgsR U T np ni c, ∀ A ∈ r.binders, A.LevelWF (U+1) := by
  intro r hr A hA
  obtain ⟨r₀, -, rfl⟩ := List.mem_map.1 hr
  obtain ⟨A₀, -, rfl⟩ := List.mem_map.1 hA
  exact VExpr.LevelWF.instL VLevel.params'_one_wf

/-- Unpack a recursor-universe recursive descriptor to the source field and
its declaration-universe analysis result. -/
theorem recArgsR_mem {U : Nat} {T : Name} {np ni : Nat} {c : VConstVal} {r}
    (hr : r ∈ recArgsR U T np ni c) :
    ∃ r₀ B, r = r₀.instL (VLevel.params' U 1) ∧
      (ctorFields (VExpr.dropN np c.type))[r₀.fieldIndex]? = some B ∧
      recArg? U T np ni r₀.fieldIndex B = some r₀ := by
  obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.1 hr
  obtain ⟨B, hB, hrec⟩ := recArgs_getElem _ hr₀
  exact ⟨r₀, B, rfl, by simpa using hB, hrec⟩

theorem motiveType_levelWF {U : Nat} {T : Name} {np : Nat} {ty : VInductiveType} :
    (motiveType U T np ty).LevelWF (U+1) := by
  refine VExpr.LevelWF.forallN idxTel_levelWF ⟨?_, Nat.succ_pos U⟩
  refine VExpr.LevelWF.appN (f := .const T (VLevel.params' U 1)) VLevel.params'_one_wf
    fun e h => ?_
  rcases List.mem_append.1 h with h | h
  · exact bvarRevRange_levelWF _ _ _ h
  · exact bvarRevRange_levelWF _ _ _ h

theorem motiveType_liftN {U : Nat} {T : Name} {np n : Nat} {ty : VInductiveType} :
    (motiveType U T np ty).liftN n =
    VExpr.forallN (VExpr.liftTelN n (idxTel U np ty) 0)
      (.forallE (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange (n + (idxTel U np ty).length) np ++
          VExpr.bvarRevRange 0 (idxTel U np ty).length))
        (.sort (.param 0))) := by
  rw [show motiveType U T np ty = VExpr.forallN (idxTel U np ty)
      (.forallE (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange (idxTel U np ty).length np ++
          VExpr.bvarRevRange 0 (idxTel U np ty).length))
        (.sort (.param 0))) from rfl,
    VExpr.liftN_forallN]
  refine congrArg _ ?_
  show VExpr.forallE _ _ = VExpr.forallE _ _
  refine congr (congrArg _ ?_) rfl
  rw [VExpr.liftN_appN, List.map_append,
    bvarRevRange_liftN_ge _ _ _ _ (by omega),
    VExpr.bvarRevRange_liftN_high _ _ _ _ (by omega)]
  rfl

theorem liftTelN_levelWF {Uv n : Nat} : ∀ {tel : List VExpr} {k : Nat},
    (∀ A ∈ tel, A.LevelWF Uv) → ∀ A ∈ VExpr.liftTelN n tel k, A.LevelWF Uv
  | [], _, _, _, h => nomatch h
  | _ :: tel, k, hAs, A', h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact (hAs _ (.head _)).liftN
    · exact liftTelN_levelWF (fun A h => hAs _ (.tail _ h)) A' h

theorem RecArg.minorBinders_levelWF {Uv m p : Nat} {r : RecArg}
    (hbind : ∀ A ∈ r.binders, A.LevelWF Uv) :
    ∀ A ∈ r.minorBinders m p, A.LevelWF Uv :=
  liftTelN_levelWF (liftTelN_levelWF hbind)

theorem RecArg.minorIH_levelWF {Uv m p : Nat} {r : RecArg}
    (hbind : ∀ A ∈ r.binders, A.LevelWF Uv)
    (hidx : ∀ e ∈ r.indices, e.LevelWF Uv) :
    (r.minorIH m p).LevelWF Uv := by
  simp only [RecArg.minorIH]
  refine VExpr.LevelWF.forallN (r.minorBinders_levelWF hbind)
    (VExpr.LevelWF.appN (f := .bvar _) trivial fun e he => ?_)
  rcases List.mem_append.1 he with he | he
  · obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.1 he
    exact ((hidx e₀ he₀).liftN).liftN
  · rcases List.mem_cons.1 he with rfl | he
    · exact VExpr.LevelWF.appN (f := .bvar _) trivial (bvarRevRange_levelWF _ _)
    · cases he

theorem ihsFromRecArgs_levelWF {Uv m : Nat} :
    ∀ (rs : List RecArg) (p : Nat),
    (∀ r ∈ rs, ∀ A ∈ r.binders, A.LevelWF Uv) →
    (∀ r ∈ rs, ∀ e ∈ r.indices, e.LevelWF Uv) →
    ∀ e ∈ ihsFromRecArgs m rs p, e.LevelWF Uv
  | [], _, _, _, _, h => nomatch h
  | r :: rs, p, hbind, hidx, e, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact r.minorIH_levelWF
        (hbind r (.head _)) (hidx r (.head _))
    · exact ihsFromRecArgs_levelWF rs (p+1)
        (fun q hq => hbind q (.tail _ hq))
        (fun q hq => hidx q (.tail _ hq)) e h

theorem minorType_levelWF {U : Nat} {T : Name} {np : Nat} {ty : VInductiveType}
    {c : VConstVal} : (minorType U T np ty c).LevelWF (U+1) := by
  simp only [minorType]
  refine VExpr.LevelWF.forallN (liftTelN_levelWF fun B hB => ?_)
    (VExpr.LevelWF.forallN (ihsFrom_levelWF _ _ recPairsR_idx_levelWF) ?_)
  · obtain ⟨B₀, _, rfl⟩ := List.mem_map.1 hB
    exact VExpr.LevelWF.instL VLevel.params'_one_wf
  · refine VExpr.LevelWF.appN (f := .bvar _) trivial fun e h => ?_
    rcases List.mem_append.1 h with h | h
    · obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.1 h
      exact ((ctorIdxs_levelWF _ he₀).liftN).liftN
    · rcases List.mem_cons.1 h with rfl | h
      · refine VExpr.LevelWF.appN (f := .const c.name (VLevel.params' U 1))
          VLevel.params'_one_wf fun e h => ?_
        rcases List.mem_append.1 h with h | h
        · exact bvarRevRange_levelWF _ _ _ h
        · exact bvarRevRange_levelWF _ _ _ h
      · cases h

theorem minorTypeRec_levelWF {U : Nat} {T : Name} {np : Nat} {ty : VInductiveType}
    {c : VConstVal} : (minorTypeRec U T np ty c).LevelWF (U+1) := by
  simp only [minorTypeRec]
  refine VExpr.LevelWF.forallN (liftTelN_levelWF fun B hB => ?_)
    (VExpr.LevelWF.forallN
      (ihsFromRecArgs_levelWF _ _ recArgsR_binder_levelWF recArgsR_idx_levelWF) ?_)
  · obtain ⟨B₀, _, rfl⟩ := List.mem_map.1 hB
    exact VExpr.LevelWF.instL VLevel.params'_one_wf
  · refine VExpr.LevelWF.appN (f := .bvar _) trivial fun e h => ?_
    rcases List.mem_append.1 h with h | h
    · obtain ⟨e₀, he₀, rfl⟩ := List.mem_map.1 h
      exact ((ctorIdxs_levelWF _ he₀).liftN).liftN
    · rcases List.mem_cons.1 h with rfl | h
      · refine VExpr.LevelWF.appN (f := .const c.name (VLevel.params' U 1))
          VLevel.params'_one_wf fun e h => ?_
        rcases List.mem_append.1 h with h | h
        · exact bvarRevRange_levelWF _ _ _ h
        · exact bvarRevRange_levelWF _ _ _ h
      · cases h

theorem minorTypes_levelWF {U : Nat} {T : Name} {np : Nat} {ty : VInductiveType} :
    ∀ (cs : List VConstVal) (i : Nat), ∀ e ∈ minorTypes U T np ty cs i, e.LevelWF (U+1)
  | _ :: cs, i, e, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact minorType_levelWF.liftN
    · exact minorTypes_levelWF cs (i+1) e h

theorem minorTypesRec_levelWF {U : Nat} {T : Name} {np : Nat} {ty : VInductiveType} :
    ∀ (cs : List VConstVal) (i : Nat),
      ∀ e ∈ minorTypesRec U T np ty cs i, e.LevelWF (U+1)
  | _ :: cs, i, e, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact minorTypeRec_levelWF.liftN
    · exact minorTypesRec_levelWF cs (i+1) e h

theorem recType_levelWF {U : Nat} {T : Name} {np : Nat} {ty : VInductiveType} :
    (recType U T np ty).LevelWF (U+1) := by
  refine VExpr.LevelWF.forallN (fun A hA => ?_)
    ⟨motiveType_levelWF, VExpr.LevelWF.forallN (minorTypes_levelWF _ _)
      (VExpr.LevelWF.forallN (liftTelN_levelWF idxTel_levelWF)
        ⟨?_, ?_, trivial⟩)⟩
  · obtain ⟨A₀, _, rfl⟩ := List.mem_map.1 hA
    exact VExpr.LevelWF.instL VLevel.params'_one_wf
  · refine VExpr.LevelWF.appN (f := .const T (VLevel.params' U 1)) VLevel.params'_one_wf
      fun e h => ?_
    rcases List.mem_append.1 h with h | h
    · exact bvarRevRange_levelWF _ _ _ h
    · exact bvarRevRange_levelWF _ _ _ h
  · exact VExpr.LevelWF.appN (f := .bvar _) trivial (bvarRevRange_levelWF _ _)

theorem recTypeRec_levelWF {U : Nat} {T : Name} {np : Nat} {ty : VInductiveType} :
    (recTypeRec U T np ty).LevelWF (U+1) := by
  refine VExpr.LevelWF.forallN (fun A hA => ?_)
    ⟨motiveType_levelWF, VExpr.LevelWF.forallN (minorTypesRec_levelWF _ _)
      (VExpr.LevelWF.forallN (liftTelN_levelWF idxTel_levelWF)
        ⟨?_, ?_, trivial⟩)⟩
  · obtain ⟨A₀, _, rfl⟩ := List.mem_map.1 hA
    exact VExpr.LevelWF.instL VLevel.params'_one_wf
  · refine VExpr.LevelWF.appN (f := .const T (VLevel.params' U 1)) VLevel.params'_one_wf
      fun e h => ?_
    rcases List.mem_append.1 h with h | h
    · exact bvarRevRange_levelWF _ _ _ h
    · exact bvarRevRange_levelWF _ _ _ h
  · exact VExpr.LevelWF.appN (f := .bvar _) trivial (bvarRevRange_levelWF _ _)

/-- Consume the induction-hypothesis telescope with well-typed values. -/
theorem hasType_appN_ihs {env : VEnv} {U : Nat} {Γ : List VExpr} {m k : Nat}
    {argOf : Nat × List VExpr → VExpr} {Dfin : VExpr} :
    ∀ {rs : List (Nat × List VExpr)} {g : VExpr}, (∀ q ∈ rs, q.1 < m) →
    (∀ q ∈ rs, env.HasType U Γ (argOf q)
      (VExpr.appN (.bvar (k + m))
        ((q.2.map fun e => ((e.liftN 1 q.1).liftN (m-q.1)).liftN k m) ++
          [.bvar (m-1-q.1)]))) →
    env.HasType U Γ g (VExpr.forallN (ihsR m k rs 0) (Dfin.liftN rs.length)) →
    env.HasType U Γ (g.appN (rs.map argOf)) Dfin
  | [], g, _, _, hg => by simpa using hg
  | (j, idxs) :: rs, g, hm, hargs, hg => by
    have happ := VEnv.HasType.app hg (hargs (j, idxs) (.head _))
    simp only [List.length_cons] at happ
    rw [show Dfin.liftN (rs.length+1) =
        (Dfin.liftN rs.length).liftN 1 (0 + rs.length) from by
        rw [Nat.zero_add, VExpr.liftN'_liftN' (Nat.zero_le _) (by omega)],
      ihsR_liftN1 m k rs 0 0 (Nat.le_refl _) (fun q hq => hm q (.tail _ hq))
        (Dfin.liftN rs.length),
      VExpr.inst_liftN1] at happ
    exact hasType_appN_ihs (rs := rs) (fun q hq => hm q (.tail _ hq))
      (fun q hq => hargs q (.tail _ hq)) happ

/-- Consume a normalized functional-IH telescope with one generated recursive
call per recursive argument. -/
theorem hasType_appN_ruleIHs {env : VEnv} {U : Nat} {Γ : List VExpr} {m k : Nat}
    {argOf : RecArg → VExpr} {Dfin : VExpr} :
    ∀ {rs : List RecArg} {g : VExpr},
    (∀ r ∈ rs, env.HasType U Γ (argOf r) (r.ruleIH m k)) →
    env.HasType U Γ g
      (VExpr.forallN (ruleIHs m k rs 0) (Dfin.liftN rs.length)) →
    env.HasType U Γ (g.appN (rs.map argOf)) Dfin
  | [], g, _, hg => by simpa using hg
  | r :: rs, g, hargs, hg => by
    have happ := VEnv.HasType.app hg (by
      simpa [ruleIHs] using hargs r (.head _))
    simp only [List.length_cons] at happ
    rw [show Dfin.liftN (rs.length+1) =
        (Dfin.liftN rs.length).liftN 1 (0+rs.length) from by
          rw [Nat.zero_add, VExpr.liftN'_liftN' (Nat.zero_le _) (by omega)],
      ruleIHs_liftN1 m k rs 0 0 (Nat.le_refl _) (Dfin.liftN rs.length),
      VExpr.inst_liftN1] at happ
    exact hasType_appN_ruleIHs (rs := rs)
      (fun q hq => hargs q (.tail _ hq)) happ

theorem liftTelN_congr {a a' : Nat} (tel : List VExpr) (k : Nat) (h : a = a') :
    VExpr.liftTelN a tel k = VExpr.liftTelN a' tel k := h ▸ rfl

namespace GenerationEnv

variable {source : VInductDecl} {gen : GenerationChecked source}
  {env : VEnv} (S : GenerationEnv gen env)
include S

/-! ## Mixed iota-rule preservation -/

/-- Syntactic universe well-formedness follows from semantic well-formedness
of the closed mixed recursor type. -/
theorem recType_levelWF :
    gen.recType.LevelWF (source.uvars + 1) := by
  obtain ⟨_, h⟩ := S.recType_isType
  exact (h.levelWF trivial).1

/-- The mixed recursor type is closed. -/
theorem recType_closedN : gen.recType.ClosedN 0 := by
  obtain ⟨_, h⟩ := S.recType_isType
  exact VExpr.WF.closedN S.ord ⟨_, h⟩ trivial

/-- The inserted mixed recursor constant at its identity universe list. -/
theorem recursor_hasType
    (hrec : env.constants
      (.str gen.block.sourceType.name "rec") =
        some gen.recursor) {Γ} :
    env.HasType (source.uvars + 1) Γ
      (.const (.str gen.block.sourceType.name "rec")
        (VLevel.params (source.uvars + 1)))
      gen.recType := by
  have h := HasType.const (Γ := Γ) hrec
    VLevel.params_wf VLevel.params_length
  rw [show gen.recursor.uvars =
      source.uvars + 1 from rfl,
    show gen.recursor.type = gen.recType from rfl] at h
  rwa [S.recType_levelWF.instL_id] at h

/-- Apply the mixed recursor to parameters, motive, and every constructor
minor. The remaining type binds the indices and major premise. -/
theorem recBase_hasType
    (hrec : env.constants
      (.str gen.block.sourceType.name "rec") =
        some gen.recursor)
    (Δ : List VExpr) :
    env.HasType (source.uvars + 1)
      (Δ ++ (gen.minorTypes.reverse ++
        (gen.motiveType :: gen.paramsTel.reverse)))
      (VExpr.appN
        (.const (.str gen.block.sourceType.name "rec")
          (VLevel.params (source.uvars + 1)))
        (VExpr.bvarRevRange Δ.length
          (source.nparams +
            gen.block.ctorPairs.length + 1)))
      ((VExpr.forallN
        (VExpr.liftTelN
          (gen.block.ctorPairs.length + 1)
          gen.idxTel 0)
        (.forallE
          (VExpr.appN
            (.const gen.block.sourceType.name
              (VLevel.params' source.uvars 1))
            (VExpr.bvarRevRange
                (gen.idxTel.length +
                  gen.block.ctorPairs.length + 1)
                source.nparams ++
              VExpr.bvarRevRange 0 gen.idxTel.length))
          (.app
            (VExpr.appN
              (.bvar
                (gen.idxTel.length +
                  gen.block.ctorPairs.length + 1))
              (VExpr.bvarRevRange 1 gen.idxTel.length))
            (.bvar 0)))).liftN Δ.length) := by
  have hf : env.HasType (source.uvars + 1)
      (Δ ++
        (gen.paramsTel ++
          gen.motiveType :: gen.minorTypes).reverse ++ [])
      (.const (.str gen.block.sourceType.name "rec")
        (VLevel.params (source.uvars + 1)))
      ((VExpr.forallN
        (gen.paramsTel ++
          gen.motiveType :: gen.minorTypes)
        (VExpr.forallN
          (VExpr.liftTelN
            (gen.block.ctorPairs.length + 1)
            gen.idxTel 0)
          (.forallE
            (VExpr.appN
              (.const gen.block.sourceType.name
                (VLevel.params' source.uvars 1))
              (VExpr.bvarRevRange
                  (gen.idxTel.length +
                    gen.block.ctorPairs.length + 1)
                  source.nparams ++
                VExpr.bvarRevRange 0 gen.idxTel.length))
            (.app
              (VExpr.appN
                (.bvar
                  (gen.idxTel.length +
                    gen.block.ctorPairs.length + 1))
                (VExpr.bvarRevRange 1 gen.idxTel.length))
              (.bvar 0))))).liftN
        (Δ.length +
          (gen.paramsTel ++
            gen.motiveType :: gen.minorTypes).length)) := by
    rw [show VExpr.forallN
        (gen.paramsTel ++
          gen.motiveType :: gen.minorTypes)
        (VExpr.forallN
          (VExpr.liftTelN
            (gen.block.ctorPairs.length + 1)
            gen.idxTel 0)
          (.forallE
            (VExpr.appN
              (.const gen.block.sourceType.name
                (VLevel.params' source.uvars 1))
              (VExpr.bvarRevRange
                  (gen.idxTel.length +
                    gen.block.ctorPairs.length + 1)
                  source.nparams ++
                VExpr.bvarRevRange 0 gen.idxTel.length))
            (.app
              (VExpr.appN
                (.bvar
                  (gen.idxTel.length +
                    gen.block.ctorPairs.length + 1))
                (VExpr.bvarRevRange 1 gen.idxTel.length))
              (.bvar 0)))) =
        gen.recType from by
          rw [VExpr.forallN_append]
          rfl,
      S.recType_closedN.liftN_eq (Nat.zero_le _)]
    exact S.recursor_hasType hrec
  have hspine := HasType.appN_selfSpine
    (env := env) (U := source.uvars + 1) hf
  simp only [GenerationChecked.recType,
    List.reverse_append, List.reverse_cons,
    List.append_nil, List.append_assoc,
    List.singleton_append, List.length_append,
    List.length_cons, List.length_reverse,
    gen.minorTypes_length] at hspine
  rw [show gen.paramsTel.length = source.nparams from by
      simp [GenerationChecked.paramsTel, gen.shape.1],
    VExpr.bvarRevRange_congr' Δ.length
      (show source.nparams +
          (gen.block.ctorPairs.length + 1) =
        source.nparams +
          gen.block.ctorPairs.length + 1 by omega)] at hspine
  simpa [List.append_assoc] using hspine

/-- Apply the inserted mixed recursor to a typed index spine and major. -/
theorem recApp_hasType
    (hrec : env.constants
      (.str gen.block.sourceType.name "rec") =
        some gen.recursor)
    (Δ : List VExpr) {idxs : List VExpr} {a : VExpr}
    (hidx : env.SpineWF (source.uvars + 1)
      (Δ ++ (gen.minorTypes.reverse ++
        (gen.motiveType :: gen.paramsTel.reverse)))
      (VExpr.forallN
        (VExpr.liftTelN
          (Δ.length +
            gen.block.ctorPairs.length + 1)
          gen.idxTel 0)
        (.sort (gen.block.checked.resultLevel.inst
          (VLevel.params' source.uvars 1))))
      idxs
      (.sort (gen.block.checked.resultLevel.inst
        (VLevel.params' source.uvars 1))))
    (hlen : idxs.length = gen.idxTel.length)
    (ha : env.HasType (source.uvars + 1)
      (Δ ++ (gen.minorTypes.reverse ++
        (gen.motiveType :: gen.paramsTel.reverse)))
      a
      (VExpr.appN
        (.const gen.block.sourceType.name
          (VLevel.params' source.uvars 1))
        (VExpr.bvarRevRange
            (Δ.length +
              gen.block.ctorPairs.length + 1)
            source.nparams ++
          idxs))) :
    env.HasType (source.uvars + 1)
      (Δ ++ (gen.minorTypes.reverse ++
        (gen.motiveType :: gen.paramsTel.reverse)))
      (VExpr.appN
        (VExpr.appN
          (.const (.str gen.block.sourceType.name "rec")
            (VLevel.params (source.uvars + 1)))
          (VExpr.bvarRevRange Δ.length
            (source.nparams +
              gen.block.ctorPairs.length + 1)))
        (idxs ++ [a]))
      (VExpr.appN
        (.bvar
          (Δ.length +
            gen.block.ctorPairs.length))
        (idxs ++ [a])) := by
  have hb := S.recBase_hasType hrec Δ
  rw [VExpr.liftN_forallN,
    VExpr.liftTelN_liftTelN,
    liftTelN_congr _ _
      (show gen.block.ctorPairs.length + 1 +
          Δ.length =
        Δ.length + gen.block.ctorPairs.length + 1 by omega)] at hb
  have hcod :
      (VExpr.forallE
        (VExpr.appN
          (.const gen.block.sourceType.name
            (VLevel.params' source.uvars 1))
          (VExpr.bvarRevRange
              (gen.idxTel.length +
                gen.block.ctorPairs.length + 1)
              source.nparams ++
            VExpr.bvarRevRange 0 gen.idxTel.length))
        (.app
          (VExpr.appN
            (.bvar
              (gen.idxTel.length +
                gen.block.ctorPairs.length + 1))
            (VExpr.bvarRevRange 1 gen.idxTel.length))
          (.bvar 0))).liftN Δ.length
            (0 + (VExpr.liftTelN
              (gen.block.ctorPairs.length + 1)
              gen.idxTel 0).length) =
      VExpr.forallE
        (VExpr.appN
          (.const gen.block.sourceType.name
            (VLevel.params' source.uvars 1))
          (VExpr.bvarRevRange
              (gen.idxTel.length + Δ.length +
                gen.block.ctorPairs.length + 1)
              source.nparams ++
            VExpr.bvarRevRange 0 gen.idxTel.length))
        (.app
          (VExpr.appN
            (.bvar
              (gen.idxTel.length + Δ.length +
                gen.block.ctorPairs.length + 1))
            (VExpr.bvarRevRange 1 gen.idxTel.length))
          (.bvar 0)) := by
    rw [VExpr.liftTelN_length, Nat.zero_add]
    show VExpr.forallE _ _ = VExpr.forallE _ _
    congr 1
    · rw [VExpr.liftN_appN, List.map_append,
        bvarRevRange_liftN_ge _ _ _ _ (by omega),
        VExpr.bvarRevRange_liftN_high _ _ _ _ (by omega),
        VExpr.bvarRevRange_congr source.nparams
          (show Δ.length +
              (gen.idxTel.length +
                gen.block.ctorPairs.length + 1) =
            gen.idxTel.length + Δ.length +
              gen.block.ctorPairs.length + 1 by omega)]
      rfl
    · show VExpr.app _ _ = VExpr.app _ _
      congr 1
      · rw [VExpr.liftN_appN,
          VExpr.bvarRevRange_liftN_high _ _ _ _ (by omega)]
        show VExpr.appN
          (.bvar (liftVar Δ.length
            (gen.idxTel.length +
              gen.block.ctorPairs.length + 1)
            (gen.idxTel.length + 1))) _ = _
        rw [liftVar_le (by omega),
          show Δ.length +
              (gen.idxTel.length +
                gen.block.ctorPairs.length + 1) =
            gen.idxTel.length + Δ.length +
              gen.block.ctorPairs.length + 1 by omega]
  rw [hcod] at hb
  have hshape := hidx.retarget
    (by simpa only [VExpr.liftTelN_length] using hlen)
    (.forallE
      (VExpr.appN
        (.const gen.block.sourceType.name
          (VLevel.params' source.uvars 1))
        (VExpr.bvarRevRange
            (gen.idxTel.length + Δ.length +
              gen.block.ctorPairs.length + 1)
            source.nparams ++
          VExpr.bvarRevRange 0 gen.idxTel.length))
      (.sort (.param 0)))
  rw [VExpr.instRev_forallE_sort, VExpr.instRev_appN,
    VExpr.instRev_closedN _
      (C := .const gen.block.sourceType.name
        (VLevel.params' source.uvars 1)) trivial,
    List.map_append,
    VExpr.map_instRev_bvarRevRange_ge _ _ _
      (by rw [hlen]; omega),
    show gen.idxTel.length + Δ.length +
        gen.block.ctorPairs.length + 1 - idxs.length =
      Δ.length + gen.block.ctorPairs.length + 1 from by
        rw [hlen]
        omega,
    VExpr.bvarRevRange_congr' 0 hlen.symm,
    VExpr.map_instRev_bvarRevRange] at hshape
  rw [hlen] at hshape
  have hfull := hshape.snoc ha
  simp only [VExpr.inst] at hfull
  change env.SpineWF (source.uvars + 1) _
    (VExpr.forallN
      (VExpr.liftTelN
        (Δ.length + gen.block.ctorPairs.length + 1)
        gen.idxTel 0)
      (VExpr.forallN
        [VExpr.appN
          (.const gen.block.sourceType.name
            (VLevel.params' source.uvars 1))
          (VExpr.bvarRevRange
              (gen.idxTel.length + Δ.length +
                gen.block.ctorPairs.length + 1)
              source.nparams ++
            VExpr.bvarRevRange 0 gen.idxTel.length)]
        (.sort (.param 0))))
    (idxs ++ [a]) (.sort (.param 0)) at hfull
  rw [← VExpr.forallN_append] at hfull
  have hfullLen : (idxs ++ [a]).length =
      (VExpr.liftTelN
          (Δ.length +
            gen.block.ctorPairs.length + 1)
          gen.idxTel 0 ++
        [VExpr.appN
          (.const gen.block.sourceType.name
            (VLevel.params' source.uvars 1))
          (VExpr.bvarRevRange
              (gen.idxTel.length + Δ.length +
                gen.block.ctorPairs.length + 1)
              source.nparams ++
            VExpr.bvarRevRange 0
              gen.idxTel.length)]).length := by
    simp only [List.length_append, List.length_singleton,
      VExpr.liftTelN_length, hlen]
  have hactual := hfull.retarget hfullLen
    (VExpr.app
      (VExpr.appN
        (.bvar
          (gen.idxTel.length + Δ.length +
            gen.block.ctorPairs.length + 1))
        (VExpr.bvarRevRange 1 gen.idxTel.length))
      (.bvar 0))
  rw [VExpr.forallN_append] at hactual
  have happ := hactual.hasType_appN hb
  rw [show VExpr.app
      (VExpr.appN
        (.bvar
          (gen.idxTel.length + Δ.length +
            gen.block.ctorPairs.length + 1))
        (VExpr.bvarRevRange 1 gen.idxTel.length))
      (.bvar 0) =
      VExpr.appN
        (.bvar
          (gen.idxTel.length + Δ.length +
            gen.block.ctorPairs.length + 1))
        (VExpr.bvarRevRange 0
          (gen.idxTel.length + 1)) from by
      rw [VExpr.bvarRevRange_congr' 0
          (show gen.idxTel.length + 1 =
            1 + gen.idxTel.length by omega),
        ← VExpr.bvarRevRange_append
          gen.idxTel.length 1]
      simpa [VExpr.bvarRevRange, VExpr.appN] using
        (VExpr.appN_append
          (.bvar
            (gen.idxTel.length + Δ.length +
              gen.block.ctorPairs.length + 1))
          (VExpr.bvarRevRange 1 gen.idxTel.length)
          [VExpr.bvar 0]).symm,
    VExpr.instRev_appN,
    VExpr.instRev_bvar_ge _ (by
      simp only [List.length_append,
        List.length_singleton]
      rw [hlen]
      omega),
    VExpr.bvarRevRange_congr' 0
      (show gen.idxTel.length + 1 =
        (idxs ++ [a]).length by simp [hlen]),
    VExpr.map_instRev_bvarRevRange] at happ
  rw [show gen.idxTel.length + Δ.length +
      gen.block.ctorPairs.length + 1 -
        (idxs ++ [a]).length =
      Δ.length + gen.block.ctorPairs.length from by
    simp only [List.length_append, List.length_singleton]
    rw [hlen]
    omega] at happ
  simpa [List.length_append, hlen] using happ

/-- The mixed motive variable applied to an index spine and major. -/
theorem motiveApp_hasType
    (Δ : List VExpr) {idxs : List VExpr} {a : VExpr}
    (hidx : env.SpineWF (source.uvars + 1)
      (Δ ++ (gen.minorTypes.reverse ++
        (gen.motiveType :: gen.paramsTel.reverse)))
      (VExpr.forallN
        (VExpr.liftTelN
          (Δ.length +
            gen.block.ctorPairs.length + 1)
          gen.idxTel 0)
        (.sort (gen.block.checked.resultLevel.inst
          (VLevel.params' source.uvars 1))))
      idxs
      (.sort (gen.block.checked.resultLevel.inst
        (VLevel.params' source.uvars 1))))
    (hlen : idxs.length = gen.idxTel.length)
    (ha : env.HasType (source.uvars + 1)
      (Δ ++ (gen.minorTypes.reverse ++
        (gen.motiveType :: gen.paramsTel.reverse)))
      a
      (VExpr.appN
        (.const gen.block.sourceType.name
          (VLevel.params' source.uvars 1))
        (VExpr.bvarRevRange
            (Δ.length +
              gen.block.ctorPairs.length + 1)
            source.nparams ++
          idxs))) :
    env.HasType (source.uvars + 1)
      (Δ ++ (gen.minorTypes.reverse ++
        (gen.motiveType :: gen.paramsTel.reverse)))
      (VExpr.appN
        (.bvar
          (Δ.length +
            gen.block.ctorPairs.length))
        (idxs ++ [a]))
      (.sort (.param 0)) := by
  have hM := getElem?_rstack3 Δ
    gen.minorTypes.reverse gen.motiveType
    gen.paramsTel.reverse
    (i := Δ.length + gen.block.ctorPairs.length)
    (by simp only [List.length_reverse,
      gen.minorTypes_length])
  exact gen.motiveVarApp_hasType
    (.bvar (Lookup.of_getElem? hM))
    hidx hlen ha

/-- The raw constructor-headed major in the complete mixed rule context. -/
theorem ctorAppRule_hasType {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) :
    env.HasType (source.uvars + 1)
      ((VExpr.liftTelN
          (gen.block.ctorPairs.length + 1)
          (ctor.fieldsR source.uvars source.nparams)
          0).reverse ++
        (gen.minorTypes.reverse ++
          (gen.motiveType :: gen.paramsTel.reverse)))
      (VExpr.appN
        (.const ctor.raw.name
          (VLevel.params' source.uvars 1))
        (VExpr.bvarRevRange
            ((ctor.fieldsR
                source.uvars source.nparams).length +
              gen.block.ctorPairs.length + 1)
            source.nparams ++
          VExpr.bvarRevRange 0
            (ctor.fieldsR
              source.uvars source.nparams).length))
      (VExpr.appN
        (.const gen.block.sourceType.name
          (VLevel.params' source.uvars 1))
        (VExpr.bvarRevRange
            ((ctor.fieldsR
                source.uvars source.nparams).length +
              gen.block.ctorPairs.length + 1)
            source.nparams ++
          (ctor.resultIndicesR source.uvars).map fun e =>
            e.liftN
              (gen.block.ctorPairs.length + 1)
              (ctor.fieldsR
                source.uvars source.nparams).length)) := by
  have h := S.ctorApp_transport hctor
    (gen.minorTypes.reverse ++ [gen.motiveType])
    (g := gen.block.ctorPairs.length + 1)
    (by simp [gen.minorTypes_length])
    [] (d := 0) rfl
  rw [VExpr.bvarRevRange_congr source.nparams
    (show
      0 + (gen.block.ctorPairs.length + 1 +
        (ctor.fieldsR
          source.uvars source.nparams).length) =
      (ctor.fieldsR
          source.uvars source.nparams).length +
        gen.block.ctorPairs.length + 1 by omega)] at h
  simpa [List.append_assoc] using h

/-- The complete mixed rule binder telescope is well formed. -/
theorem ruleBinders_onTel {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) :
    env.OnTel (source.uvars + 1) []
      (gen.paramsTel ++
        gen.motiveType :: gen.minorTypes ++
        VExpr.liftTelN
          (gen.block.ctorPairs.length + 1)
          (ctor.fieldsR source.uvars source.nparams)
          0) := by
  have hF₀ := S.fields_onTel_minor hctor
  have hF := hF₀.weakN S.ord
    (Ctx.LiftN.zero
      (Γ := gen.motiveType :: gen.paramsTel.reverse)
      gen.minorTypes.reverse)
  rw [VExpr.liftTelN_liftTelN,
    liftTelN_congr _ _
      (show 1 + gen.minorTypes.reverse.length =
        gen.block.ctorPairs.length + 1 by
          simp [gen.minorTypes_length, Nat.add_comm])] at hF
  refine OnTel.append
    (OnTel.append S.paramsTel_onTel ⟨?_, ?_⟩) ?_
  · simpa only [List.append_nil] using S.motive_isType
  · simpa only [List.append_nil] using S.minorTypes_onTel
  · simpa only [List.append_nil, List.append_assoc,
      List.reverse_append, List.reverse_cons,
      List.singleton_append] using hF

/-- The type recorded on every mixed iota rule is itself a type. -/
theorem ruleType_isType {i : Nat} {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) :
    env.IsType (source.uvars + 1) []
      ((gen.rule i ctor).type) := by
  show env.IsType (source.uvars + 1) []
    (VExpr.forallN
      (gen.paramsTel ++
        gen.motiveType :: gen.minorTypes ++
        VExpr.liftTelN
          (gen.block.ctorPairs.length + 1)
          (ctor.fieldsR source.uvars source.nparams)
          0)
      (VExpr.appN
        (.bvar
          (gen.block.ctorPairs.length +
            (ctor.fieldsR
              source.uvars source.nparams).length))
        (((ctor.resultIndicesR source.uvars).map fun e =>
            e.liftN
              (gen.block.ctorPairs.length + 1)
              (ctor.fieldsR
                source.uvars source.nparams).length) ++
          [VExpr.appN
            (.const ctor.raw.name
              (VLevel.params' source.uvars 1))
            (VExpr.bvarRevRange
                ((ctor.fieldsR
                    source.uvars source.nparams).length +
                  gen.block.ctorPairs.length + 1)
                source.nparams ++
              VExpr.bvarRevRange 0
                (ctor.fieldsR
                  source.uvars source.nparams).length)])))
  refine IsType.forallN (S.ruleBinders_onTel hctor) ?_
  simp only [List.reverse_append, List.reverse_cons,
    List.append_nil, List.append_assoc,
    List.singleton_append]
  have hSp₀ := S.result_transport hctor
    (gen.minorTypes.reverse ++ [gen.motiveType])
    (g := gen.block.ctorPairs.length + 1)
    (by simp [gen.minorTypes_length])
    [] (d := 0) rfl
  have hSp : env.SpineWF (source.uvars + 1)
      ((VExpr.liftTelN
          (gen.block.ctorPairs.length + 1)
          (ctor.fieldsR source.uvars source.nparams)
          0).reverse ++
        (gen.minorTypes.reverse ++
          (gen.motiveType :: gen.paramsTel.reverse)))
      (VExpr.forallN
        (VExpr.liftTelN
          ((ctor.fieldsR
              source.uvars source.nparams).length +
            gen.block.ctorPairs.length + 1)
          gen.idxTel 0)
        (.sort (gen.block.checked.resultLevel.inst
          (VLevel.params' source.uvars 1))))
      ((ctor.resultIndicesR source.uvars).map fun e =>
        e.liftN
          (gen.block.ctorPairs.length + 1)
          (ctor.fieldsR
            source.uvars source.nparams).length)
      (.sort (gen.block.checked.resultLevel.inst
        (VLevel.params' source.uvars 1))) := by
    simpa [List.append_assoc, Nat.add_assoc] using hSp₀
  have hidxLen :
      ((ctor.resultIndicesR source.uvars).map fun e =>
        e.liftN
          (gen.block.ctorPairs.length + 1)
          (ctor.fieldsR
            source.uvars source.nparams).length).length =
      gen.idxTel.length := by
    simp only [List.length_map,
      NormalizedCtor.resultIndicesR,
      GenerationChecked.idxTel]
    exact (S.viewResultIndices_length hctor).trans
      gen.shape.2.2.1.symm
  have hctorApp := S.ctorAppRule_hasType hctor
  have hSp' : env.SpineWF (source.uvars + 1)
      ((VExpr.liftTelN
          (gen.block.ctorPairs.length + 1)
          (ctor.fieldsR source.uvars source.nparams)
          0).reverse ++
        (gen.minorTypes.reverse ++
          (gen.motiveType :: gen.paramsTel.reverse)))
      (VExpr.forallN
        (VExpr.liftTelN
          ((VExpr.liftTelN
              (gen.block.ctorPairs.length + 1)
              (ctor.fieldsR
                source.uvars source.nparams)
              0).reverse.length +
            gen.block.ctorPairs.length + 1)
          gen.idxTel 0)
        (.sort (gen.block.checked.resultLevel.inst
          (VLevel.params' source.uvars 1))))
      ((ctor.resultIndicesR source.uvars).map fun e =>
        e.liftN
          (gen.block.ctorPairs.length + 1)
          (ctor.fieldsR
            source.uvars source.nparams).length)
      (.sort (gen.block.checked.resultLevel.inst
        (VLevel.params' source.uvars 1))) := by
    simpa only [List.length_reverse,
      VExpr.liftTelN_length] using hSp
  have hctorApp' : env.HasType (source.uvars + 1)
      ((VExpr.liftTelN
          (gen.block.ctorPairs.length + 1)
          (ctor.fieldsR source.uvars source.nparams)
          0).reverse ++
        (gen.minorTypes.reverse ++
          (gen.motiveType :: gen.paramsTel.reverse)))
      (VExpr.appN
        (.const ctor.raw.name
          (VLevel.params' source.uvars 1))
        (VExpr.bvarRevRange
            ((ctor.fieldsR
                source.uvars source.nparams).length +
              gen.block.ctorPairs.length + 1)
            source.nparams ++
          VExpr.bvarRevRange 0
            (ctor.fieldsR
              source.uvars source.nparams).length))
      (VExpr.appN
        (.const gen.block.sourceType.name
          (VLevel.params' source.uvars 1))
        (VExpr.bvarRevRange
            ((VExpr.liftTelN
                (gen.block.ctorPairs.length + 1)
                (ctor.fieldsR
                  source.uvars source.nparams)
                0).reverse.length +
              gen.block.ctorPairs.length + 1)
            source.nparams ++
          (ctor.resultIndicesR source.uvars).map fun e =>
            e.liftN
              (gen.block.ctorPairs.length + 1)
              (ctor.fieldsR
                source.uvars source.nparams).length)) := by
    simpa only [List.length_reverse,
      VExpr.liftTelN_length] using hctorApp
  refine ⟨.param 0, ?_⟩
  have hm := S.motiveApp_hasType
    (VExpr.liftTelN
      (gen.block.ctorPairs.length + 1)
      (ctor.fieldsR source.uvars source.nparams)
      0).reverse
    hSp' hidxLen hctorApp'
  rw [List.length_reverse, VExpr.liftTelN_length,
    show
      (ctor.fieldsR
          source.uvars source.nparams).length +
          gen.block.ctorPairs.length =
        gen.block.ctorPairs.length +
          (ctor.fieldsR
            source.uvars source.nparams).length by omega,
    show
      gen.block.ctorPairs.length +
          (ctor.fieldsR
            source.uvars source.nparams).length + 1 =
        (ctor.fieldsR
            source.uvars source.nparams).length +
          gen.block.ctorPairs.length + 1 by omega] at hm
  exact hm

/-- A retained recursive descriptor generates a well-typed direct or
lambda-valued recursive call in the complete mixed rule context. -/
theorem ruleCall_hasType {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs)
    (hrec : env.constants
      (.str gen.block.sourceType.name "rec") =
        some gen.recursor)
    {r : RecArg}
    (hr : r ∈ ctor.recArgsR source.uvars) :
    env.HasType (source.uvars + 1)
      ((VExpr.liftTelN
          (gen.block.ctorPairs.length + 1)
          (ctor.fieldsR source.uvars source.nparams)
          0).reverse ++
        (gen.minorTypes.reverse ++
          (gen.motiveType :: gen.paramsTel.reverse)))
      (r.ruleCall
        (ctor.fieldsR source.uvars source.nparams).length
        gen.block.ctorPairs.length
        (VExpr.appN
          (.const
            (.str gen.block.sourceType.name "rec")
            (VLevel.params (source.uvars + 1)))
          (VExpr.bvarRevRange
            (ctor.fieldsR
              source.uvars source.nparams).length
            (source.nparams +
              gen.block.ctorPairs.length + 1))))
      (r.ruleIH
        (ctor.fieldsR source.uvars source.nparams).length
        gen.block.ctorPairs.length) := by
  obtain ⟨r₀, hr₀, rfl⟩ :=
    NormalizedCtor.recArgsR_mem hr
  obtain ⟨Bview, hBview, hrecArg⟩ :=
    S.viewRecArg_data hctor hr₀
  let ls := VLevel.params' source.uvars 1
  let r := r₀.instL ls
  let Bs := ctor.fieldsR source.uvars source.nparams
  let m := Bs.length
  let k := gen.block.ctorPairs.length
  let j := r₀.fieldIndex
  let Fs := VExpr.liftTelN (k+1) Bs 0
  let As := r.ruleBinders m k
  let idxs := r.indices.map fun e =>
    (e.liftN (k+1)
      (r.fieldIndex+r.binders.length)).liftN
        (m-r.fieldIndex) r.binders.length
  let Γ := Fs.reverse ++
    (gen.minorTypes.reverse ++
      (gen.motiveType :: gen.paramsTel.reverse))
  have hjm : j < m := by
    have hview := S.viewRecArg_lt hctor hr₀
    have hfields :=
      (gen.shape.2.2.2.2.2 ctor hctor).2.2.2
    simp only [j, m, Bs, NormalizedCtor.fieldsR_length]
    omega
  have hjraw :
      r₀.fieldIndex <
        (ctor.rawFields source.nparams).length := by
    simpa [j, m, Bs,
      NormalizedCtor.fieldsR_length] using hjm
  let Braw :=
    (ctor.rawFields source.nparams)[r₀.fieldIndex]
  have hBraw :
      (ctor.rawFields source.nparams)[r₀.fieldIndex]? =
        some Braw :=
    List.getElem?_eq_getElem hjraw
  have hFsLen : Fs.length = m := by
    simp [Fs, m, VExpr.liftTelN_length]
  have ht := S.recArg_transport hctor hr₀
    (gen.minorTypes.reverse ++ [gen.motiveType])
    (g := k+1) (by simp [k, gen.minorTypes_length])
    (Fs.drop j).reverse (d := m-j) (by
      simp only [List.length_reverse, List.length_drop,
        hFsLen])
  dsimp only [r, j, RecArg.instL] at ht
  have hctx :
      (Fs.drop j).reverse ++
          ((VExpr.liftTelN (k+1)
              (Bs.take j) 0).reverse ++
            ((gen.minorTypes.reverse ++
              [gen.motiveType]) ++
              gen.paramsTel.reverse)) = Γ := by
    dsimp only [Γ, Fs]
    rw [← VExpr.liftTelN_take, List.append_assoc,
      ← List.append_assoc
        (((VExpr.liftTelN (k+1) Bs 0).drop j).reverse),
      ← List.reverse_append, List.take_append_drop,
      List.singleton_append, ← List.append_assoc]
  have htel : env.OnTel
      (source.uvars + 1) Γ As := by
    rw [hctx] at ht
    simpa [r, As, m, k, j, RecArg.instL,
      RecArg.ruleBinders] using ht.1
  have hsp : env.SpineWF (source.uvars + 1)
      (As.reverse ++ Γ)
      (VExpr.forallN
        (VExpr.liftTelN
          (m+k+r.binders.length+1)
          gen.idxTel 0)
        (.sort (gen.block.checked.resultLevel.inst ls)))
      idxs
      (.sort (gen.block.checked.resultLevel.inst ls)) := by
    rw [hctx] at ht
    simpa [r, As, idxs, m, k, j, ls,
      RecArg.instL, RecArg.ruleBinders,
      List.append_assoc,
      show j + r₀.binders.length + (k+1) + (m-j) =
        m+k+r₀.binders.length+1 by omega] using ht.2
  have hF : Γ[m-1-j]? =
      some ((Braw.instL ls).liftN (k+1) j) := by
    dsimp only [Γ, Fs]
    rw [List.getElem?_append_left
        (by
          simp only [List.length_reverse,
            VExpr.liftTelN_length]
          omega),
      List.getElem?_reverse (by rw [hFsLen]; omega),
      VExpr.liftTelN_length,
      show m - 1 - (m - 1 - j) = j by omega,
      VExpr.liftTelN_getElem?,
      NormalizedCtor.fieldsR_getElem?, hBraw]
    simp [ls]
  have hlu := Lookup.of_getElem? hF
  dsimp only [j, r] at hlu
  rw [show m-1-r₀.fieldIndex+1 =
      m-r₀.fieldIndex by omega] at hlu
  have hf0 := VEnv.HasType.bvar
    (env := env) (U := source.uvars + 1) hlu
  obtain ⟨u, hdom₀⟩ :=
    S.emittedField_defeq hctor hBraw hBview
  have hdom₁ := hdom₀.instL
    (U' := source.uvars + 1)
    VLevel.params'_one_wf
  have hprefix :
      (((ctor.rawFields source.nparams).take
          r₀.fieldIndex).reverse ++
        gen.block.rawParams.reverse).map
          (VExpr.instL ls) =
      (Bs.take r₀.fieldIndex).reverse ++
        gen.paramsTel.reverse := by
    simp [Bs, ls, NormalizedCtor.fieldsR,
      GenerationChecked.paramsTel,
      List.map_reverse, List.map_take]
  rw [hprefix] at hdom₁
  have hjlen :
      (Bs.take r₀.fieldIndex).length =
        r₀.fieldIndex := by
    simp only [Bs, NormalizedCtor.fieldsR,
      List.length_take, List.length_map]
    omega
  have Wmid := Ctx.LiftN.consTel
    (n := k+1)
    (Bs.take r₀.fieldIndex)
    (Ctx.LiftN.zero
      (n := k+1)
      (Γ := gen.paramsTel.reverse)
      (gen.minorTypes.reverse ++
        [gen.motiveType])
      (h := by simp [k, gen.minorTypes_length]))
  rw [hjlen, Nat.add_zero] at Wmid
  have hdom₂ := hdom₁.weakN S.ord Wmid
  have Wstack := Ctx.LiftN.zero
    (n := m-j)
    (Γ := (VExpr.liftTelN (k+1)
        (Bs.take j) 0).reverse ++
      ((gen.minorTypes.reverse ++
        [gen.motiveType]) ++
        gen.paramsTel.reverse))
    (Fs.drop j).reverse
    (h := by
      simp only [List.length_reverse, List.length_drop,
        hFsLen])
  have hdom₃ := hdom₂.weakN S.ord Wstack
  rw [hctx] at hdom₃
  have hfView := hdom₃.defeq hf0
  have hfield := recArg_rule_fieldType
    hrecArg m k (by simpa [j] using hjm)
  simp only [RecArg.instL] at hfield
  dsimp only [j] at hfView
  simp only [Nat.add_zero] at hfView
  rw [hfield] at hfView
  have hf := hfView.weakN S.ord
    (Ctx.LiftN.zero (Γ := Γ) As.reverse)
  have hmajor := VEnv.HasType.appN_selfSpine
    (env := env) (U := source.uvars + 1)
    (As := As)
    (B := VExpr.appN
      (.const gen.block.sourceType.name ls)
      (VExpr.bvarRevRange
          (m+k+r.binders.length+1)
          source.nparams ++
        idxs))
    (Δ := []) (Γ := Γ) (by
      simpa [As, r, idxs, j, ls,
        RecArg.instL, RecArg.ruleBinders,
        List.length_reverse, List.map_map,
        Function.comp_def] using hf)
  simp only [List.length_nil, VExpr.liftN_zero,
    List.nil_append] at hmajor
  have hAsLen :
      As.length = r.binders.length := by
    simp [As, RecArg.ruleBinders,
      VExpr.liftTelN_length]
  have hmajorHead :
      (VExpr.bvar
        (m-1-r.fieldIndex)).liftN As.length =
      .bvar
        (m-1-r.fieldIndex+r.binders.length) := by
    simp only [VExpr.liftN, liftVar_base]
    congr 1
    rw [hAsLen]
    omega
  change env.HasType (source.uvars + 1)
    (As.reverse ++ Γ)
    (((VExpr.bvar
      (m-1-r.fieldIndex)).liftN As.length).appN
        (VExpr.bvarRevRange 0 As.length))
    (VExpr.appN
      (.const gen.block.sourceType.name ls)
      (VExpr.bvarRevRange
          (m+k+r.binders.length+1)
          source.nparams ++
        idxs)) at hmajor
  rw [hmajorHead, hAsLen] at hmajor
  have hlen : idxs.length = gen.idxTel.length := by
    simpa [idxs, r, RecArg.instL,
      GenerationChecked.idxTel] using
      (S.viewRecArg_indices_length hctor hr₀).trans
        gen.shape.2.2.1.symm
  have hcall := S.recApp_hasType hrec
    (As.reverse ++ Fs.reverse)
    (by
      simpa [Γ, List.append_assoc, hAsLen, hFsLen,
        Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using hsp)
    hlen
    (by
      simpa [Γ, List.append_assoc, hAsLen, hFsLen,
        Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using hmajor)
  have hbase :
      (VExpr.appN
        (.const
          (.str gen.block.sourceType.name "rec")
          (VLevel.params (source.uvars + 1)))
        (VExpr.bvarRevRange m
          (source.nparams+(k+1)))).liftN
          r.binders.length =
      VExpr.appN
        (.const
          (.str gen.block.sourceType.name "rec")
          (VLevel.params (source.uvars + 1)))
        (VExpr.bvarRevRange
          (m+r.binders.length)
          (source.nparams+(1+k))) := by
    rw [VExpr.liftN_appN]
    simp only [VExpr.liftN]
    rw [bvarRevRange_liftN_ge _ _ _ _
      (Nat.zero_le _)]
    rw [show source.nparams+(k+1) =
      source.nparams+(1+k) by omega]
    apply congrArg (VExpr.appN _)
    apply VExpr.bvarRevRange_congr
    omega
  have hlam := HasType.lamN htel (by
    simpa [Γ, Fs, hAsLen, hFsLen,
      List.append_assoc, VExpr.liftN_appN,
      bvarRevRange_liftN_ge _ _ _ _
        (Nat.zero_le _),
      Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using hcall)
  simpa [RecArg.ruleCall, RecArg.ruleIH,
    r, Bs, ls, As, idxs, m, k, Γ, Fs, hbase,
    VExpr.liftTelN_length, List.append_assoc,
    Nat.add_assoc] using hlam

/-- The selected mixed constructor minor applied to all raw fields and to one
generated direct or functional recursive call for every retained `RecArg`. -/
theorem minorApp_hasType {i : Nat} {ctor : NormalizedCtor}
    (hci : gen.block.ctorPairs[i]? = some ctor)
    (hrec : env.constants
      (.str gen.block.sourceType.name "rec") =
        some gen.recursor) :
    env.HasType (source.uvars + 1)
      ((VExpr.liftTelN
          (gen.block.ctorPairs.length + 1)
          (ctor.fieldsR source.uvars source.nparams)
          0).reverse ++
        (gen.minorTypes.reverse ++
          (gen.motiveType :: gen.paramsTel.reverse)))
      (VExpr.appN
        (.bvar
          (gen.block.ctorPairs.length - 1 - i +
            (ctor.fieldsR
              source.uvars source.nparams).length))
        (VExpr.bvarRevRange 0
            (ctor.fieldsR source.uvars source.nparams).length ++
          List.map (fun r =>
              r.ruleCall
                (ctor.fieldsR
                  source.uvars source.nparams).length
                gen.block.ctorPairs.length
                (VExpr.appN
                  (.const
                    (.str gen.block.sourceType.name "rec")
                    (VLevel.params (source.uvars + 1)))
                  (VExpr.bvarRevRange
                    (ctor.fieldsR
                      source.uvars source.nparams).length
                    (source.nparams +
                      gen.block.ctorPairs.length + 1))))
            (ctor.recArgsR source.uvars)))
      (VExpr.appN
        (.bvar
          (gen.block.ctorPairs.length +
            (ctor.fieldsR
              source.uvars source.nparams).length))
        (((ctor.resultIndicesR source.uvars).map fun e =>
            e.liftN
              (gen.block.ctorPairs.length + 1)
              (ctor.fieldsR
                source.uvars source.nparams).length) ++
          [VExpr.appN
            (.const ctor.raw.name
              (VLevel.params' source.uvars 1))
            (VExpr.bvarRevRange
                ((ctor.fieldsR
                    source.uvars source.nparams).length +
                  gen.block.ctorPairs.length + 1)
                source.nparams ++
              VExpr.bvarRevRange 0
                (ctor.fieldsR
                  source.uvars source.nparams).length)])) := by
  obtain ⟨hik, -⟩ :=
    List.getElem?_eq_some_iff.1 hci
  have hctor := List.mem_of_getElem? hci
  let rs := ctor.recArgsR source.uvars
  have hrs :
      rs = ctor.recArgsR source.uvars := rfl
  have hrsLt : ∀ r ∈ rs,
      r.fieldIndex <
        (ctor.fieldsR
          source.uvars source.nparams).length := by
    intro r hr
    obtain ⟨r₀, hr₀, rfl⟩ :=
      NormalizedCtor.recArgsR_mem (hrs ▸ hr)
    have hview := S.viewRecArg_lt hctor hr₀
    have hfields :=
      (gen.shape.2.2.2.2.2 ctor hctor).2.2.2
    simp only [RecArg.instL,
      NormalizedCtor.fieldsR_length]
    omega
  rw [VExpr.appN_append]
  have hminorAt :
      gen.minorTypes[i]? =
        some
          (VExpr.liftN i
            (GenerationChecked.minorType
              (source := source) ctor)) := by
    simpa [GenerationChecked.minorTypes, hci] using
      gen.minorTypesAux_getElem?
        gen.block.ctorPairs 0 i
  have hlu0 :
      ((VExpr.liftTelN
          (gen.block.ctorPairs.length + 1)
          (ctor.fieldsR source.uvars source.nparams)
          0).reverse ++
        (gen.minorTypes.reverse ++
          (gen.motiveType :: gen.paramsTel.reverse)))[
          gen.block.ctorPairs.length - 1 - i +
            (ctor.fieldsR
              source.uvars source.nparams).length]? =
        some
          (VExpr.liftN i
            (GenerationChecked.minorType
              (source := source) ctor)) := by
    rw [getElem?_rstack_mid _ _ _
        (by
          simp only [List.length_reverse,
            VExpr.liftTelN_length]
          omega)
        (by
          simp only [List.length_reverse,
            VExpr.liftTelN_length,
            gen.minorTypes_length]
          omega),
      show
        gen.block.ctorPairs.length - 1 - i +
            (ctor.fieldsR
              source.uvars source.nparams).length -
            (VExpr.liftTelN
              (gen.block.ctorPairs.length + 1)
              (ctor.fieldsR
                source.uvars source.nparams)
              0).reverse.length =
          gen.block.ctorPairs.length - 1 - i by
        simp only [List.length_reverse,
          VExpr.liftTelN_length]
        omega,
      List.getElem?_reverse
        (by
          simp only [gen.minorTypes_length]
          omega),
      show
        gen.minorTypes.length - 1 -
            (gen.block.ctorPairs.length - 1 - i) =
          i by
        simp only [gen.minorTypes_length]
        omega,
      hminorAt]
  have hlu := Lookup.of_getElem? hlu0
  rw [VExpr.liftN_liftN,
    show
      i +
          (gen.block.ctorPairs.length - 1 - i +
            (ctor.fieldsR
              source.uvars source.nparams).length + 1) =
        (ctor.fieldsR
            source.uvars source.nparams).length +
          gen.block.ctorPairs.length by omega] at hlu
  have hminorEq :
      (GenerationChecked.minorType
        (source := source) ctor).liftN
          ((ctor.fieldsR
              source.uvars source.nparams).length +
            gen.block.ctorPairs.length) =
        (VExpr.forallN
          (VExpr.liftTelN
            (gen.block.ctorPairs.length + 1)
            (ctor.fieldsR
              source.uvars source.nparams)
            0)
          ((VExpr.forallN
            (ihsFromRecArgs
              (ctor.fieldsR
                source.uvars source.nparams).length
              rs 0)
            (VExpr.appN
              (.bvar
                ((ctor.fieldsR
                    source.uvars source.nparams).length +
                  rs.length))
              (((ctor.resultIndicesR source.uvars).map
                  fun e =>
                    (e.liftN 1
                      (ctor.fieldsR
                        source.uvars source.nparams).length).liftN
                      rs.length) ++
                [VExpr.appN
                  (.const ctor.raw.name
                    (VLevel.params' source.uvars 1))
                  (VExpr.bvarRevRange
                      (rs.length +
                        (ctor.fieldsR
                          source.uvars source.nparams).length +
                        1)
                      source.nparams ++
                    VExpr.bvarRevRange rs.length
                      (ctor.fieldsR
                        source.uvars source.nparams).length)]))).liftN
              gen.block.ctorPairs.length
              (ctor.fieldsR
                source.uvars source.nparams).length)).liftN
          (ctor.fieldsR
            source.uvars source.nparams).length := by
    simp only [GenerationChecked.minorType,
      rs, hrs]
    conv => lhs; rw [VExpr.liftN_forallN,
        VExpr.liftTelN_liftTelN,
        liftTelN_congr _ _
          (show
            (1 : Nat) +
                ((ctor.fieldsR
                    source.uvars source.nparams).length +
                  gen.block.ctorPairs.length) =
              gen.block.ctorPairs.length + 1 +
                (ctor.fieldsR
                  source.uvars source.nparams).length by
            omega),
        show
          (0 : Nat) +
              (VExpr.liftTelN 1
                (ctor.fieldsR
                  source.uvars source.nparams)
                0).length =
            (ctor.fieldsR
              source.uvars source.nparams).length by
          simp [VExpr.liftTelN_length]]
    conv => rhs; rw [VExpr.liftN_forallN,
        VExpr.liftTelN_liftTelN,
        show
          (0 : Nat) +
              (VExpr.liftTelN
                (gen.block.ctorPairs.length + 1)
                (ctor.fieldsR
                  source.uvars source.nparams)
                0).length =
            (ctor.fieldsR
              source.uvars source.nparams).length by
          simp [VExpr.liftTelN_length],
        VExpr.liftN'_liftN_hi,
        Nat.add_comm gen.block.ctorPairs.length
          (ctor.fieldsR
            source.uvars source.nparams).length]
  have hfields := HasType.appN_selfSpine
    (env := env) (U := source.uvars + 1)
    (As := VExpr.liftTelN
      (gen.block.ctorPairs.length + 1)
      (ctor.fieldsR source.uvars source.nparams)
      0)
    (B :=
      (VExpr.forallN
        (ihsFromRecArgs
          (ctor.fieldsR
            source.uvars source.nparams).length
          rs 0)
        (VExpr.appN
          (.bvar
            ((ctor.fieldsR
                source.uvars source.nparams).length +
              rs.length))
          (((ctor.resultIndicesR source.uvars).map
              fun e =>
                (e.liftN 1
                  (ctor.fieldsR
                    source.uvars source.nparams).length).liftN
                  rs.length) ++
            [VExpr.appN
              (.const ctor.raw.name
                (VLevel.params' source.uvars 1))
              (VExpr.bvarRevRange
                  (rs.length +
                    (ctor.fieldsR
                      source.uvars source.nparams).length +
                    1)
                  source.nparams ++
                VExpr.bvarRevRange rs.length
                  (ctor.fieldsR
                    source.uvars source.nparams).length)]))).liftN
        gen.block.ctorPairs.length
        (ctor.fieldsR
          source.uvars source.nparams).length)
    (Δ := [])
    (Γ := gen.minorTypes.reverse ++
      (gen.motiveType :: gen.paramsTel.reverse))
    (f := .bvar
      (gen.block.ctorPairs.length - 1 - i +
        (ctor.fieldsR
          source.uvars source.nparams).length))
    (by
      have hb := VEnv.HasType.bvar
        (env := env) (U := source.uvars + 1) hlu
      rw [hminorEq] at hb
      simpa [VExpr.liftTelN_length] using hb)
  simp only [List.length_nil,
    VExpr.liftTelN_length,
    VExpr.liftN_zero] at hfields
  rw [ihsFromRecArgs_liftN'
    (ctor.fieldsR source.uvars source.nparams).length
    gen.block.ctorPairs.length rs hrsLt 0
    (VExpr.appN
      (.bvar
        ((ctor.fieldsR
            source.uvars source.nparams).length +
          rs.length))
      (((ctor.resultIndicesR source.uvars).map fun e =>
          (e.liftN 1
            (ctor.fieldsR
              source.uvars source.nparams).length).liftN
            rs.length) ++
        [VExpr.appN
          (.const ctor.raw.name
            (VLevel.params' source.uvars 1))
          (VExpr.bvarRevRange
              (rs.length +
                (ctor.fieldsR
                  source.uvars source.nparams).length + 1)
              source.nparams ++
            VExpr.bvarRevRange rs.length
              (ctor.fieldsR
                source.uvars source.nparams).length)]))
    (cut :=
      (ctor.fieldsR
        source.uvars source.nparams).length)
    rfl] at hfields
  have hD :
      (VExpr.appN
        (.bvar
          ((ctor.fieldsR
              source.uvars source.nparams).length +
            rs.length))
        (((ctor.resultIndicesR source.uvars).map fun e =>
            (e.liftN 1
              (ctor.fieldsR
                source.uvars source.nparams).length).liftN
              rs.length) ++
          [VExpr.appN
            (.const ctor.raw.name
              (VLevel.params' source.uvars 1))
            (VExpr.bvarRevRange
                (rs.length +
                  (ctor.fieldsR
                    source.uvars source.nparams).length + 1)
                source.nparams ++
              VExpr.bvarRevRange rs.length
                (ctor.fieldsR
                  source.uvars source.nparams).length)])).liftN
        gen.block.ctorPairs.length
        ((ctor.fieldsR
            source.uvars source.nparams).length +
          0 + rs.length) =
      (VExpr.appN
        (.bvar
          (gen.block.ctorPairs.length +
            (ctor.fieldsR
              source.uvars source.nparams).length))
        (((ctor.resultIndicesR source.uvars).map fun e =>
            e.liftN
              (gen.block.ctorPairs.length + 1)
              (ctor.fieldsR
                source.uvars source.nparams).length) ++
          [VExpr.appN
            (.const ctor.raw.name
              (VLevel.params' source.uvars 1))
            (VExpr.bvarRevRange
                ((ctor.fieldsR
                    source.uvars source.nparams).length +
                  gen.block.ctorPairs.length + 1)
                source.nparams ++
              VExpr.bvarRevRange 0
                (ctor.fieldsR
                  source.uvars source.nparams).length)])).liftN
        rs.length := by
    rw [VExpr.liftN_appN, VExpr.liftN_appN,
      List.map_append, List.map_append,
      List.map_map, List.map_map]
    show VExpr.appN _ (_ ++ [_]) =
      VExpr.appN _ (_ ++ [_])
    congr 1
    · show
        VExpr.bvar
            (liftVar gen.block.ctorPairs.length
              ((ctor.fieldsR
                  source.uvars source.nparams).length +
                rs.length)
              ((ctor.fieldsR
                  source.uvars source.nparams).length +
                0 + rs.length)) =
          VExpr.bvar
            (liftVar rs.length
              (gen.block.ctorPairs.length +
                (ctor.fieldsR
                  source.uvars source.nparams).length)
              0)
      rw [liftVar_le (by omega),
        liftVar_le (Nat.zero_le _)]
      congr 1
      omega
    · congr 1
      · apply List.map_congr_left
        intro e _
        simp only [Function.comp_apply]
        rw [show
            (ctor.fieldsR
                source.uvars source.nparams).length +
                0 + rs.length =
              (ctor.fieldsR
                  source.uvars source.nparams).length +
                rs.length by omega,
          VExpr.liftN_liftN_mid e
            gen.block.ctorPairs.length rs.length
            (Nat.zero_le _)]
      · congr 1
        simp only [Function.comp_apply]
        rw [show
            (ctor.fieldsR
                source.uvars source.nparams).length +
                0 + rs.length =
              (ctor.fieldsR
                  source.uvars source.nparams).length +
                rs.length by omega]
        rw [VExpr.liftN_appN,
          VExpr.liftN_appN,
          List.map_append, List.map_append,
          bvarRevRange_liftN_ge _ _ _ _ (by omega),
          VExpr.bvarRevRange_liftN_high _ _ _ _
            (by omega),
          bvarRevRange_liftN_ge _ _ _ _
            (Nat.zero_le _),
          bvarRevRange_liftN_ge _ _ _ _
            (Nat.zero_le _),
          VExpr.bvarRevRange_congr source.nparams
            (show
              gen.block.ctorPairs.length +
                  (rs.length +
                    (ctor.fieldsR
                      source.uvars source.nparams).length +
                    1) =
                rs.length +
                  ((ctor.fieldsR
                      source.uvars source.nparams).length +
                    gen.block.ctorPairs.length + 1) by
              omega),
          VExpr.bvarRevRange_congr _
            (show rs.length = rs.length + 0 by omega)]
        rfl
  rw [hD] at hfields
  have hres := hasType_appN_ruleIHs
    (env := env) (U := source.uvars + 1)
    (m :=
      (ctor.fieldsR
        source.uvars source.nparams).length)
    (k := gen.block.ctorPairs.length)
    (rs := rs)
    (argOf := fun r =>
      r.ruleCall
        (ctor.fieldsR
          source.uvars source.nparams).length
        gen.block.ctorPairs.length
        (VExpr.appN
          (.const
            (.str gen.block.sourceType.name "rec")
            (VLevel.params (source.uvars + 1)))
          (VExpr.bvarRevRange
            (ctor.fieldsR
              source.uvars source.nparams).length
            (source.nparams +
              gen.block.ctorPairs.length + 1))))
    (fun r hr =>
      S.ruleCall_hasType hctor hrec (hrs ▸ hr))
    hfields
  simpa only [hrs] using hres

/-- The constructor-headed left side of a mixed iota rule. -/
theorem recRuleApp_hasType {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs)
    (hrec : env.constants
      (.str gen.block.sourceType.name "rec") =
        some gen.recursor) :
    env.HasType (source.uvars + 1)
      ((VExpr.liftTelN
          (gen.block.ctorPairs.length + 1)
          (ctor.fieldsR source.uvars source.nparams)
          0).reverse ++
        (gen.minorTypes.reverse ++
          (gen.motiveType :: gen.paramsTel.reverse)))
      (VExpr.appN
        (VExpr.appN
          (.const
            (.str gen.block.sourceType.name "rec")
            (VLevel.params (source.uvars + 1)))
          (VExpr.bvarRevRange
            (ctor.fieldsR
              source.uvars source.nparams).length
            (source.nparams +
              gen.block.ctorPairs.length + 1)))
        (((ctor.resultIndicesR source.uvars).map fun e =>
            e.liftN
              (gen.block.ctorPairs.length + 1)
              (ctor.fieldsR
                source.uvars source.nparams).length) ++
          [VExpr.appN
            (.const ctor.raw.name
              (VLevel.params' source.uvars 1))
            (VExpr.bvarRevRange
                ((ctor.fieldsR
                    source.uvars source.nparams).length +
                  gen.block.ctorPairs.length + 1)
                source.nparams ++
              VExpr.bvarRevRange 0
                (ctor.fieldsR
                  source.uvars source.nparams).length)]))
      (VExpr.appN
        (.bvar
          (gen.block.ctorPairs.length +
            (ctor.fieldsR
              source.uvars source.nparams).length))
        (((ctor.resultIndicesR source.uvars).map fun e =>
            e.liftN
              (gen.block.ctorPairs.length + 1)
              (ctor.fieldsR
                source.uvars source.nparams).length) ++
          [VExpr.appN
            (.const ctor.raw.name
              (VLevel.params' source.uvars 1))
            (VExpr.bvarRevRange
                ((ctor.fieldsR
                    source.uvars source.nparams).length +
                  gen.block.ctorPairs.length + 1)
                source.nparams ++
              VExpr.bvarRevRange 0
                (ctor.fieldsR
                  source.uvars source.nparams).length)])) := by
  have hSp₀ := S.result_transport hctor
    (gen.minorTypes.reverse ++ [gen.motiveType])
    (g := gen.block.ctorPairs.length + 1)
    (by simp [gen.minorTypes_length])
    [] (d := 0) rfl
  have hSp : env.SpineWF (source.uvars + 1)
      ((VExpr.liftTelN
          (gen.block.ctorPairs.length + 1)
          (ctor.fieldsR source.uvars source.nparams)
          0).reverse ++
        (gen.minorTypes.reverse ++
          (gen.motiveType :: gen.paramsTel.reverse)))
      (VExpr.forallN
        (VExpr.liftTelN
          ((VExpr.liftTelN
              (gen.block.ctorPairs.length + 1)
              (ctor.fieldsR
                source.uvars source.nparams)
              0).reverse.length +
            gen.block.ctorPairs.length + 1)
          gen.idxTel 0)
        (.sort
          (gen.block.checked.resultLevel.inst
            (VLevel.params' source.uvars 1))))
      ((ctor.resultIndicesR source.uvars).map fun e =>
        e.liftN
          (gen.block.ctorPairs.length + 1)
          (ctor.fieldsR
            source.uvars source.nparams).length)
      (.sort
        (gen.block.checked.resultLevel.inst
          (VLevel.params' source.uvars 1))) := by
    simpa [List.append_assoc, Nat.add_assoc,
      List.length_reverse, VExpr.liftTelN_length]
      using hSp₀
  have hidxLen :
      ((ctor.resultIndicesR source.uvars).map fun e =>
        e.liftN
          (gen.block.ctorPairs.length + 1)
          (ctor.fieldsR
            source.uvars source.nparams).length).length =
        gen.idxTel.length := by
    simp only [List.length_map,
      NormalizedCtor.resultIndicesR,
      GenerationChecked.idxTel]
    exact (S.viewResultIndices_length hctor).trans
      gen.shape.2.2.1.symm
  have ha₀ := S.ctorAppRule_hasType hctor
  have ha : env.HasType (source.uvars + 1)
      ((VExpr.liftTelN
          (gen.block.ctorPairs.length + 1)
          (ctor.fieldsR source.uvars source.nparams)
          0).reverse ++
        (gen.minorTypes.reverse ++
          (gen.motiveType :: gen.paramsTel.reverse)))
      (VExpr.appN
        (.const ctor.raw.name
          (VLevel.params' source.uvars 1))
        (VExpr.bvarRevRange
            ((ctor.fieldsR
                source.uvars source.nparams).length +
              gen.block.ctorPairs.length + 1)
            source.nparams ++
          VExpr.bvarRevRange 0
            (ctor.fieldsR
              source.uvars source.nparams).length))
      (VExpr.appN
        (.const gen.block.sourceType.name
          (VLevel.params' source.uvars 1))
        (VExpr.bvarRevRange
            ((VExpr.liftTelN
                (gen.block.ctorPairs.length + 1)
                (ctor.fieldsR
                  source.uvars source.nparams)
                0).reverse.length +
              gen.block.ctorPairs.length + 1)
            source.nparams ++
          (ctor.resultIndicesR source.uvars).map fun e =>
            e.liftN
              (gen.block.ctorPairs.length + 1)
              (ctor.fieldsR
                source.uvars source.nparams).length)) := by
    simpa only [List.length_reverse,
      VExpr.liftTelN_length] using ha₀
  have hr := S.recApp_hasType hrec
    (VExpr.liftTelN
      (gen.block.ctorPairs.length + 1)
      (ctor.fieldsR source.uvars source.nparams)
      0).reverse
    hSp hidxLen ha
  rw [List.length_reverse, VExpr.liftTelN_length,
    show
      (ctor.fieldsR
          source.uvars source.nparams).length +
          gen.block.ctorPairs.length =
        gen.block.ctorPairs.length +
          (ctor.fieldsR
            source.uvars source.nparams).length by
      omega,
    show
      gen.block.ctorPairs.length +
          (ctor.fieldsR
            source.uvars source.nparams).length + 1 =
        (ctor.fieldsR
            source.uvars source.nparams).length +
          gen.block.ctorPairs.length + 1 by
      omega] at hr
  exact hr

/-- Every per-constructor mixed iota rule is well formed in an environment
containing the generated recursor constant. -/
theorem rule_WF {i : Nat} {ctor : NormalizedCtor}
    (hci : gen.block.ctorPairs[i]? = some ctor)
    (hrec : env.constants
      (.str gen.block.sourceType.name "rec") =
        some gen.recursor) :
    (gen.rule i ctor).WF env := by
  have hctor := List.mem_of_getElem? hci
  refine ⟨?_, ?_⟩
  · show env.HasType (source.uvars + 1) []
      (VExpr.lamN
        (gen.paramsTel ++
          gen.motiveType :: gen.minorTypes ++
          VExpr.liftTelN
            (gen.block.ctorPairs.length + 1)
            (ctor.fieldsR
              source.uvars source.nparams)
            0)
        _)
      (VExpr.forallN _ _)
    refine HasType.lamN
      (S.ruleBinders_onTel hctor) ?_
    simp only [List.reverse_append,
      List.reverse_cons, List.append_nil,
      List.append_assoc, List.singleton_append]
    exact S.recRuleApp_hasType hctor hrec
  · show env.HasType (source.uvars + 1) []
      (VExpr.lamN
        (gen.paramsTel ++
          gen.motiveType :: gen.minorTypes ++
          VExpr.liftTelN
            (gen.block.ctorPairs.length + 1)
            (ctor.fieldsR
              source.uvars source.nparams)
            0)
        _)
      (VExpr.forallN _ _)
    refine HasType.lamN
      (S.ruleBinders_onTel hctor) ?_
    simp only [List.reverse_append,
      List.reverse_cons, List.append_nil,
      List.append_assoc, List.singleton_append]
    exact S.minorApp_hasType hci hrec

end GenerationEnv

theorem ctorFieldsR_length {U np : Nat} {c : VConstVal} :
    (ctorFieldsR U np c).length = (ctorFields (VExpr.dropN np c.type)).length :=
  List.length_map ..

theorem ctorFieldsR_getElem? {U np : Nat} {c : VConstVal} {q : Nat} :
    (ctorFieldsR U np c)[q]? =
    (ctorFields (VExpr.dropN np c.type))[q]?.map (VExpr.instL (VLevel.params' U 1)) :=
  List.getElem?_map ..

/-! ## The post-family environment invariant -/

/-- The facts available immediately after inserting a checked family,
before any constructor has been installed. Constructor types may refer to the
family, so this is the precise staging invariant needed to validate them. -/
structure DirectFamilyEnv (env : VEnv) (U : Nat) (T : Name)
    (np : Nat) (l : VLevel) (ty : VInductiveType) : Prop where
  ord : env.Ordered
  hl : l.WF U
  hsort : VExpr.resultOf (VExpr.dropN np ty.type) = .sort l
  hlen : (VExpr.telN np ty.type).length = np
  hT : env.constants T = some ⟨U, ty.type⟩
  hparams :
    OnTel env U []
      (VExpr.telN np ty.type ++
        ctorFields (VExpr.dropN np ty.type))

section DirectFamily

variable {env : VEnv} {U : Nat} {T : Name} {np : Nat}
  {l : VLevel} {ty : VInductiveType}
  (S : DirectFamilyEnv env U T np l ty)
include S

theorem DirectFamilyEnv.tyType_eq :
    ty.type =
      VExpr.forallN (VExpr.telN np ty.type)
        (VExpr.forallN
          (ctorFields (VExpr.dropN np ty.type)) (.sort l)) := by
  conv => lhs
          rw [← VExpr.forallN_telN_dropN np ty.type,
            ← forallN_ctorFields_resultOf
              (VExpr.dropN np ty.type), S.hsort]

theorem DirectFamilyEnv.tyType_isType :
    env.IsType U [] ty.type := by
  rw [S.tyType_eq, ← VExpr.forallN_append]
  exact IsType.forallN S.hparams ⟨_, HasType.sort S.hl⟩

theorem DirectFamilyEnv.tconst_decl {Γ} :
    env.HasType U Γ (.const T (VLevel.params U)) ty.type :=
  (HasType.const0 S.hT S.tyType_isType).weak0 S.ord

/-- Applying the newly inserted family to its parameter self-spine exposes
the index telescope in any constructor-field context. -/
theorem DirectFamilyEnv.recAppPi_hasType_decl (Δ : List VExpr) :
    env.HasType U (Δ ++ (VExpr.telN np ty.type).reverse)
      (recApp U T np Δ.length)
      ((VExpr.forallN
        (ctorFields (VExpr.dropN np ty.type)) (.sort l)).liftN
          Δ.length) := by
  have hcl : ty.type.ClosedN 0 :=
    Ordered.closedC (ci := ⟨U, ty.type⟩) S.ord S.hT
  have hf : env.HasType U
      (Δ ++ (VExpr.telN np ty.type).reverse ++ [])
      (.const T (VLevel.params U))
      ((VExpr.forallN (VExpr.telN np ty.type)
        (VExpr.forallN
          (ctorFields (VExpr.dropN np ty.type)) (.sort l))).liftN
            (Δ.length + (VExpr.telN np ty.type).length)) := by
    rw [← S.tyType_eq, hcl.liftN_eq (Nat.zero_le _)]
    exact S.tconst_decl
  have hout := HasType.appN_selfSpine (env := env) (U := U) hf
  rw [S.hlen] at hout
  simpa [List.append_nil] using hout

/-- Checked constructor fields form a telescope as soon as the family is
available; no constructor lookup is needed for recursive occurrences. -/
theorem DirectFamilyEnv.fieldsWF_onTel_decl :
    ∀ (Bs : List VExpr) (Δd : List VExpr) (j : Nat),
      Δd.length = j →
      fieldsWF U T np env l
        (ctorFields (VExpr.dropN np ty.type))
        (Δd ++ (VExpr.telN np ty.type).reverse) j Bs →
      OnTel env U
        (Δd ++ (VExpr.telN np ty.type).reverse) Bs
  | [], _, _, _, _ => trivial
  | B :: Bs, Δd, j, hΔ, ⟨hB, hSp, hrest⟩ => by
    refine ⟨?_, DirectFamilyEnv.fieldsWF_onTel_decl
      Bs (B :: Δd) (j+1) (by simp [hΔ]) hrest⟩
    rcases hB with hrec | hfun | ⟨-, u, h, -⟩
    · obtain ⟨hBeq, -, -⟩ := isRecField_eq hrec
      have hTapp := S.recAppPi_hasType_decl Δd
      rw [hΔ, VExpr.liftN_forallN] at hTapp
      have hgoal : env.HasType U
          (Δd ++ (VExpr.telN np ty.type).reverse)
          B (.sort l) := by
        rw [hBeq, VExpr.appN_append]
        exact (hSp hrec).hasType_appN hTapp
      exact ⟨_, hgoal⟩
    · obtain ⟨r, hr, -, hrtel, hrsp⟩ := hfun
      obtain ⟨hrj, -, hBeq, -, -, -⟩ := recArg?_eq hr
      rw [hBeq]
      refine IsType.forallN hrtel ⟨l, ?_⟩
      have hTapp :=
        S.recAppPi_hasType_decl (r.binders.reverse ++ Δd)
      rw [VExpr.liftN_forallN] at hTapp
      have hbase : env.HasType U
          (r.binders.reverse ++
            (Δd ++ (VExpr.telN np ty.type).reverse))
          (recApp U T np (j + r.binders.length))
          (VExpr.forallN
            (VExpr.liftTelN (j + r.binders.length)
              (ctorFields (VExpr.dropN np ty.type)) 0)
            (.sort l)) := by
        simpa [List.append_assoc, hΔ, Nat.add_comm] using hTapp
      rw [hrj] at hrsp
      simpa [recApp, VExpr.appN_append] using
        hrsp.hasType_appN hbase
    · exact ⟨u, h⟩

/-- The analyzed result spine types the exact family application at the end
of a constructor declaration. -/
theorem DirectFamilyEnv.ctorResult_hasType_decl
    {c : VConstVal}
    (hresult : env.SpineWF U
      ((ctorFields (VExpr.dropN np c.type)).reverse ++
        (VExpr.telN np ty.type).reverse)
      (VExpr.forallN
        (VExpr.liftTelN
          (ctorFields (VExpr.dropN np c.type)).length
          (ctorFields (VExpr.dropN np ty.type)) 0)
        (.sort l))
      (recFieldIdxs np
        (VExpr.resultOf (VExpr.dropN np c.type)))
      (.sort l)) :
    env.HasType U
      ((ctorFields (VExpr.dropN np c.type)).reverse ++
        (VExpr.telN np ty.type).reverse)
      (VExpr.appN (.const T (VLevel.params U))
        (VExpr.bvarRevRange
          (ctorFields (VExpr.dropN np c.type)).length np ++
          recFieldIdxs np
            (VExpr.resultOf (VExpr.dropN np c.type))))
      (.sort l) := by
  have hTapp := S.recAppPi_hasType_decl
    ((ctorFields (VExpr.dropN np c.type)).reverse)
  rw [List.length_reverse, VExpr.liftN_forallN] at hTapp
  rw [VExpr.appN_append]
  exact hresult.hasType_appN hTapp

end DirectFamily

/-- A checked family insertion constructs the post-family invariant directly
from the checker contract. -/
theorem Checked.WF.toDirectFamilyEnv
    {source : VInductDecl} {checked : source.Checked}
    {pre envT : VEnv} (hpre : pre.Ordered)
    (h : checked.WF pre)
    (hadd : pre.addConst checked.type.name
      checked.type.toVConstant = some envT) :
    DirectFamilyEnv envT source.uvars checked.type.name
      source.nparams checked.resultLevel checked.type where
  ord := by
    have hfamily : checked.type.toVConstant.WF pre := by
      show pre.IsType checked.type.uvars [] checked.type.type
      rw [checked.direct_anatomy.1]
      exact h.family_isType
    exact .const hpre hfamily hadd
  hl := checked.direct_anatomy.2.2.1
  hsort := checked.result_eq
  hlen := by simpa [checked.params_eq] using
    checked.direct_anatomy.2.1
  hT := by
    have hout := addConst_self hadd
    change envT.constants checked.type.name =
      some ⟨checked.type.uvars, checked.type.type⟩ at hout
    rw [checked.direct_anatomy.1] at hout
    exact hout
  hparams := by
    simpa [checked.params_eq, checked.indices_eq] using
      h.1.mono (addConst_le hadd)

/-! ## The stage-3 environment invariant -/

/-- Everything the piece-typing lemmas need about an environment that
already contains the block's type constant and constructors. -/
structure Stage3Env (env : VEnv) (U : Nat) (T : Name) (np : Nat) (l : VLevel)
    (ty : VInductiveType) : Prop where
  ord : env.Ordered
  hl : l.WF U
  hsort : VExpr.resultOf (VExpr.dropN np ty.type) = .sort l
  hlen : (VExpr.telN np ty.type).length = np
  hT : env.constants T = some ⟨U, ty.type⟩
  hcs : ∀ c ∈ ty.ctors, env.constants c.name = some ⟨U, c.type⟩
  htel : ∀ c ∈ ty.ctors, VExpr.telN np c.type = VExpr.telN np ty.type
  hs3 : ∀ c ∈ ty.ctors, stage3Ctor U T np (ctorFields (VExpr.dropN np ty.type)).length 0
    (VExpr.dropN np c.type) = true
  hparams : OnTel env U [] (VExpr.telN np ty.type ++ ctorFields (VExpr.dropN np ty.type))
  hfields : ∀ c ∈ ty.ctors, fieldsWF U T np env l (ctorFields (VExpr.dropN np ty.type))
    (VExpr.telN np ty.type).reverse 0 (ctorFields (VExpr.dropN np c.type))
  hresult : ∀ c ∈ ty.ctors, env.SpineWF U
    ((ctorFields (VExpr.dropN np c.type)).reverse ++ (VExpr.telN np ty.type).reverse)
    (VExpr.forallN (VExpr.liftTelN (ctorFields (VExpr.dropN np c.type)).length
      (ctorFields (VExpr.dropN np ty.type)) 0) (.sort l))
    (recFieldIdxs np (VExpr.resultOf (VExpr.dropN np c.type))) (.sort l)

variable {env : VEnv} {U : Nat} {T : Name} {np : Nat} {l : VLevel} {ty : VInductiveType}
  (S : Stage3Env env U T np l ty)
include S

theorem Stage3Env.mono {env' : VEnv} (henv : env ≤ env') (ord' : env'.Ordered) :
    Stage3Env env' U T np l ty where
  ord := ord'
  hl := S.hl
  hsort := S.hsort
  hlen := S.hlen
  hT := henv.constants S.hT
  hcs := fun c hc => henv.constants (S.hcs c hc)
  htel := S.htel
  hs3 := S.hs3
  hparams := S.hparams.mono henv
  hfields := fun c hc => fieldsWF_mono henv (S.hfields c hc)
  hresult := fun c hc => (S.hresult c hc).mono henv

/-- The block's type split at the parameters and indices. -/
theorem Stage3Env.tyType_eq : ty.type =
    VExpr.forallN (VExpr.telN np ty.type)
      (VExpr.forallN (ctorFields (VExpr.dropN np ty.type)) (.sort l)) := by
  conv => lhs; rw [← VExpr.forallN_telN_dropN np ty.type,
    ← forallN_ctorFields_resultOf (VExpr.dropN np ty.type), S.hsort]

/-- The type of the block constant is a type. -/
theorem Stage3Env.tyType_isType : env.IsType U [] ty.type := by
  rw [S.tyType_eq, ← VExpr.forallN_append]
  exact IsType.forallN S.hparams ⟨_, HasType.sort S.hl⟩

/-- The block constant at the declaration universes, in any context. -/
theorem Stage3Env.tconst_decl {Γ} :
    env.HasType U Γ (.const T (VLevel.params U)) ty.type :=
  (HasType.const0 S.hT S.tyType_isType).weak0 S.ord

/-- The type of the block constant, instantiated to the recursor universes. -/
theorem Stage3Env.tyType_instL :
    ty.type.instL (VLevel.params' U 1) =
    VExpr.forallN (paramsTel U np ty)
      (VExpr.forallN (idxTel U np ty) (.sort (l.inst (VLevel.params' U 1)))) := by
  conv => lhs; rw [S.tyType_eq]
  rw [VExpr.instL_forallN, VExpr.instL_forallN]
  rfl

/-- The block constant at the recursor universes, in any context. -/
theorem Stage3Env.tconst {Γ} :
    env.HasType (U+1) Γ (.const T (VLevel.params' U 1)) (ty.type.instL (VLevel.params' U 1)) := by
  have := (S.tconst_decl (Γ := [])).instL (U' := U+1) VLevel.params'_one_wf
  rw [show (VExpr.const T (VLevel.params U)).instL (VLevel.params' U 1) =
    .const T (VLevel.params' U 1) from by
      simp [VExpr.instL, VLevel.params_map_inst_params']] at this
  exact this.weak0 S.ord

/-- The parameter spine applied to the block constant, `Δ` binders past
the parameter telescope (declaration universes): the index pi. -/
theorem Stage3Env.recAppPi_hasType_decl (Δ : List VExpr) :
    env.HasType U (Δ ++ (VExpr.telN np ty.type).reverse) (recApp U T np Δ.length)
      ((VExpr.forallN (ctorFields (VExpr.dropN np ty.type)) (.sort l)).liftN Δ.length) := by
  have hcl : ty.type.ClosedN 0 := Ordered.closedC (ci := ⟨U, ty.type⟩) S.ord S.hT
  have hf : env.HasType U (Δ ++ (VExpr.telN np ty.type).reverse ++ [])
      (.const T (VLevel.params U))
      ((VExpr.forallN (VExpr.telN np ty.type)
        (VExpr.forallN (ctorFields (VExpr.dropN np ty.type)) (.sort l))).liftN
        (Δ.length + (VExpr.telN np ty.type).length)) := by
    rw [← S.tyType_eq, hcl.liftN_eq (Nat.zero_le _)]
    exact S.tconst_decl
  have := HasType.appN_selfSpine (env := env) (U := U) hf
  rw [S.hlen] at this
  simpa [List.append_nil] using this

/-- The parameter spine at the recursor universes: the index pi. -/
theorem Stage3Env.recAppPi_hasType (Δ : List VExpr) :
    env.HasType (U+1) (Δ ++ (paramsTel U np ty).reverse) (recApp' U T np Δ.length)
      ((VExpr.forallN (idxTel U np ty)
        (.sort (l.inst (VLevel.params' U 1)))).liftN Δ.length) := by
  have hcl : (ty.type.instL (VLevel.params' U 1)).ClosedN 0 :=
    (Ordered.closedC (ci := ⟨U, ty.type⟩) S.ord S.hT).instL
  have hf : env.HasType (U+1) (Δ ++ (paramsTel U np ty).reverse ++ [])
      (.const T (VLevel.params' U 1))
      ((VExpr.forallN (paramsTel U np ty)
        (VExpr.forallN (idxTel U np ty) (.sort (l.inst (VLevel.params' U 1))))).liftN
        (Δ.length + (paramsTel U np ty).length)) := by
    rw [← S.tyType_instL, hcl.liftN_eq (Nat.zero_le _)]
    exact S.tconst
  have := HasType.appN_selfSpine (env := env) (U := U+1) hf
  rw [show (paramsTel U np ty).length = np from by
    simp [paramsTel, List.length_map, S.hlen]] at this
  simpa [List.append_nil] using this

/-- The block applied to the full parameter-and-index self-spine is a
sort, in the context of the indices over the parameters. -/
theorem Stage3Env.motiveTApp_hasType :
    env.HasType (U+1) ((idxTel U np ty).reverse ++ (paramsTel U np ty).reverse)
      (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange (idxTel U np ty).length np ++
          VExpr.bvarRevRange 0 (idxTel U np ty).length))
      (.sort (l.inst (VLevel.params' U 1))) := by
  have hcl : (ty.type.instL (VLevel.params' U 1)).ClosedN 0 :=
    (Ordered.closedC (ci := ⟨U, ty.type⟩) S.ord S.hT).instL
  have hf : env.HasType (U+1)
      ([] ++ (paramsTel U np ty ++ idxTel U np ty).reverse ++ [])
      (.const T (VLevel.params' U 1))
      ((VExpr.forallN (paramsTel U np ty ++ idxTel U np ty)
        (.sort (l.inst (VLevel.params' U 1)))).liftN
        (List.length ([] : List VExpr) +
          (paramsTel U np ty ++ idxTel U np ty).length)) := by
    rw [VExpr.forallN_append, ← S.tyType_instL, hcl.liftN_eq (Nat.zero_le _)]
    exact S.tconst
  have h2 := HasType.appN_selfSpine (env := env) (U := U+1) hf
  rw [show List.length ([] : List VExpr) = 0 from rfl,
    VExpr.bvarRevRange_congr' 0 (show (paramsTel U np ty ++ idxTel U np ty).length =
      (idxTel U np ty).length + np from by
      simp [paramsTel, List.length_map, S.hlen]; omega),
    ← VExpr.bvarRevRange_append] at h2
  simpa [List.append_nil, List.reverse_append] using h2

/-- Field telescopes are well-formed in context, at the declaration
universes: recursive fields by the partial parameter application of the
block followed by the carried index-spine typing. -/
theorem Stage3Env.fieldsWF_onTel_decl :
    ∀ (Bs : List VExpr) (Δd : List VExpr) (j : Nat), Δd.length = j →
    fieldsWF U T np env l (ctorFields (VExpr.dropN np ty.type))
      (Δd ++ (VExpr.telN np ty.type).reverse) j Bs →
    OnTel env U (Δd ++ (VExpr.telN np ty.type).reverse) Bs
  | [], _, _, _, _ => trivial
  | B :: Bs, Δd, j, hΔ, ⟨hB, hSp, hT⟩ => by
    refine ⟨?_, Stage3Env.fieldsWF_onTel_decl Bs (B :: Δd) (j+1) (by simp [hΔ]) hT⟩
    rcases hB with hrec | hfun | ⟨-, u, h, -⟩
    · obtain ⟨hBeq, -, -⟩ := isRecField_eq hrec
      have hTapp := S.recAppPi_hasType_decl Δd
      rw [hΔ, VExpr.liftN_forallN] at hTapp
      have hgoal : env.HasType U (Δd ++ (VExpr.telN np ty.type).reverse) B (.sort l) := by
        rw [hBeq, VExpr.appN_append]
        exact (hSp hrec).hasType_appN hTapp
      exact ⟨_, hgoal⟩
    · obtain ⟨r, hr, -, hrtel, hrsp⟩ := hfun
      obtain ⟨hrj, -, hBeq, -, -, -⟩ := recArg?_eq hr
      rw [hBeq]
      refine IsType.forallN hrtel ⟨l, ?_⟩
      have hTapp := S.recAppPi_hasType_decl (r.binders.reverse ++ Δd)
      rw [VExpr.liftN_forallN] at hTapp
      have hbase : env.HasType U
          (r.binders.reverse ++ (Δd ++ (VExpr.telN np ty.type).reverse))
          (recApp U T np (j + r.binders.length))
          (VExpr.forallN
            (VExpr.liftTelN (j + r.binders.length)
              (ctorFields (VExpr.dropN np ty.type)) 0) (.sort l)) := by
        simpa [List.append_assoc, hΔ, Nat.add_comm] using hTapp
      rw [hrj] at hrsp
      simpa [recApp, VExpr.appN_append] using hrsp.hasType_appN hbase
    · exact ⟨u, h⟩

/-- Field telescopes are well-formed in context, at the recursor
universes. -/
theorem Stage3Env.fieldsWF_onTel :
    ∀ (Bs : List VExpr) (Δd : List VExpr) (j : Nat), Δd.length = j →
    fieldsWF U T np env l (ctorFields (VExpr.dropN np ty.type))
      (Δd ++ (VExpr.telN np ty.type).reverse) j Bs →
    OnTel env (U+1)
      ((Δd ++ (VExpr.telN np ty.type).reverse).map (VExpr.instL (VLevel.params' U 1)))
      (Bs.map (VExpr.instL (VLevel.params' U 1)))
  | Bs, Δd, j, hΔ, hfields => by
    exact (S.fieldsWF_onTel_decl Bs Δd j hΔ hfields).instL VLevel.params'_one_wf

/-- The constructor's type, split at the parameters. -/
theorem Stage3Env.ctorType_eq {c : VConstVal} (hc : c ∈ ty.ctors) :
    c.type = VExpr.forallN (VExpr.telN np ty.type)
      (VExpr.forallN (ctorFields (VExpr.dropN np c.type))
        (VExpr.appN (.const T (VLevel.params U))
          (VExpr.bvarRevRange (0 + (ctorFields (VExpr.dropN np c.type)).length) np ++
            recFieldIdxs np (VExpr.resultOf (VExpr.dropN np c.type))))) := by
  conv => lhs; rw [← VExpr.forallN_telN_dropN np c.type, S.htel c hc,
    (stage3Ctor_eq (S.hs3 c hc)).1]

theorem Stage3Env.ctorType_instL {c : VConstVal} (hc : c ∈ ty.ctors) :
    c.type.instL (VLevel.params' U 1) =
    VExpr.forallN (paramsTel U np ty)
      (VExpr.forallN (ctorFieldsR U np c)
        (VExpr.appN (.const T (VLevel.params' U 1))
          (VExpr.bvarRevRange (0 + (ctorFields (VExpr.dropN np c.type)).length) np ++
            ctorIdxs U np c))) := by
  conv => lhs; rw [S.ctorType_eq hc, VExpr.instL_forallN, VExpr.instL_forallN,
    VExpr.instL_appN, List.map_append, bvarRevRange_instL,
    show (VExpr.const T (VLevel.params U)).instL (VLevel.params' U 1) =
      .const T (VLevel.params' U 1) from by
      simp [VExpr.instL, VLevel.params_map_inst_params']]
  rfl

/-- The constructor's result, typed by the partial parameter application
and the carried result-spine typing (declaration universes). -/
theorem Stage3Env.ctorResult_hasType_decl {c : VConstVal} (hc : c ∈ ty.ctors) :
    env.HasType U
      ((ctorFields (VExpr.dropN np c.type)).reverse ++ (VExpr.telN np ty.type).reverse)
      (VExpr.appN (.const T (VLevel.params U))
        (VExpr.bvarRevRange (0 + (ctorFields (VExpr.dropN np c.type)).length) np ++
          recFieldIdxs np (VExpr.resultOf (VExpr.dropN np c.type))))
      (.sort l) := by
  have hTapp := S.recAppPi_hasType_decl ((ctorFields (VExpr.dropN np c.type)).reverse)
  rw [List.length_reverse, VExpr.liftN_forallN] at hTapp
  rw [VExpr.appN_append,
    VExpr.bvarRevRange_congr np (show 0 + (ctorFields (VExpr.dropN np c.type)).length =
      (ctorFields (VExpr.dropN np c.type)).length from by omega)]
  exact (S.hresult c hc).hasType_appN hTapp

/-- A constructor's declared type is well-formed (declaration universes). -/
theorem Stage3Env.ctorType_isType {c : VConstVal} (hc : c ∈ ty.ctors) :
    env.IsType U [] c.type := by
  rw [S.ctorType_eq hc]
  refine IsType.forallN (S.hparams.of_append.1) ?_
  simp only [List.append_nil]
  refine IsType.forallN
    (S.fieldsWF_onTel_decl _ [] 0 rfl (by simpa using S.hfields c hc)) ?_
  exact ⟨_, by simpa using S.ctorResult_hasType_decl hc⟩

/-- The constructor constant at the recursor universes, any context. -/
theorem Stage3Env.cConst {c : VConstVal} (hc : c ∈ ty.ctors) {Γ} :
    env.HasType (U+1) Γ (.const c.name (VLevel.params' U 1))
      (c.type.instL (VLevel.params' U 1)) := by
  have h0 := HasType.const0 (S.hcs c hc) (S.ctorType_isType hc)
  have := h0.instL (U' := U+1) VLevel.params'_one_wf
  rw [show (VExpr.const c.name (VLevel.params U)).instL (VLevel.params' U 1) =
    .const c.name (VLevel.params' U 1) from by
      simp [VExpr.instL, VLevel.params_map_inst_params']] at this
  exact this.weak0 S.ord

/-- The index telescope is well-formed over the parameters, at the
recursor universes. -/
theorem Stage3Env.idxTel_onTel :
    OnTel env (U+1) (paramsTel U np ty).reverse (idxTel U np ty) := by
  have h0 := (S.hparams.of_append.2).instL (U' := U+1) VLevel.params'_one_wf
  simpa [paramsTel, idxTel, List.map_reverse] using h0

theorem Stage3Env.motive_isType :
    env.IsType (U+1) (paramsTel U np ty).reverse (motiveType U T np ty) := by
  refine IsType.forallN S.idxTel_onTel ?_
  exact ⟨_, HasType.forallE S.motiveTApp_hasType (HasType.sort (Nat.succ_pos U))⟩

/-- Transport a recursive field's index-spine typing into a rule or minor
context: instantiate the universes, insert `mid` (motive, or motive and
minors) at the field's depth `j`, and push a `d`-entry stack underneath. -/
theorem Stage3Env.spine_transport {c : VConstVal} (hc : c ∈ ty.ctors)
    {j : Nat} {B : VExpr}
    (hBj : (ctorFields (VExpr.dropN np c.type))[j]? = some B)
    (hrec : isRecField U T np (ctorFields (VExpr.dropN np ty.type)).length j B = true)
    (mid : List VExpr) {g : Nat} (hg : mid.length = g)
    (As₂ : List VExpr) {d : Nat} (hd : As₂.length = d) :
    env.SpineWF (U+1)
      (As₂ ++ ((VExpr.liftTelN g ((ctorFieldsR U np c).take j) 0).reverse ++
        (mid ++ (paramsTel U np ty).reverse)))
      (VExpr.forallN (VExpr.liftTelN (j + g + d) (idxTel U np ty) 0)
        (.sort (l.inst (VLevel.params' U 1))))
      (((recFieldIdxs np B).map (VExpr.instL (VLevel.params' U 1))).map
        fun e => (e.liftN g j).liftN d)
      (.sort (l.inst (VLevel.params' U 1))) := by
  have hjlen : ((ctorFieldsR U np c).take j).length = j := by
    have h1 := (List.getElem?_eq_some_iff.1 hBj).1
    simp only [ctorFieldsR, List.length_take, List.length_map]
    omega
  -- (1) declaration-universe spine from the fieldsWF chain
  have h0 := fieldsWF_spine (S.hfields c hc) j B (by simpa using hBj)
    (by simpa using hrec)
  rw [Nat.zero_add] at h0
  -- (2) universe instantiation
  have h1 := h0.instL (U' := U+1) VLevel.params'_one_wf
  rw [VExpr.instL_forallN, VExpr.liftTelN_instL,
    show (((ctorFields (VExpr.dropN np c.type)).take j).reverse ++
        (VExpr.telN np ty.type).reverse).map (VExpr.instL (VLevel.params' U 1)) =
      ((ctorFieldsR U np c).take j).reverse ++ (paramsTel U np ty).reverse from by
      simp [ctorFieldsR, paramsTel, List.map_reverse, List.map_take]] at h1
  -- (3) insert `mid` at depth `j`
  have W₁ := Ctx.LiftN.consTel (n := mid.length) ((ctorFieldsR U np c).take j)
    (Ctx.LiftN.zero (Γ := (paramsTel U np ty).reverse) mid)
  rw [hjlen, Nat.add_zero] at W₁
  have h2 := h1.weakN S.ord W₁
  rw [VExpr.liftN_forallN, hg] at h2
  -- (4) push the stack underneath
  have h3 := h2.weakN S.ord (Ctx.LiftN.zero (Γ := _) As₂ (h := hd))
  rw [VExpr.liftN_forallN] at h3
  rw [VExpr.liftTelN_liftTelN_hi' j g _ 0 (by omega), VExpr.liftTelN_liftTelN,
    show (ctorFields (VExpr.dropN np ty.type)).map (VExpr.instL (VLevel.params' U 1)) =
      idxTel U np ty from rfl] at h3
  simpa [VExpr.instL, VExpr.liftN, List.map_map, Function.comp_def,
    List.append_assoc] using h3

/-- Transport all semantic evidence for a recursive argument beneath a Pi
telescope. This is the functional counterpart of `spine_transport`: it
transports both the argument telescope and the terminal family-index spine.
-/
theorem Stage3Env.recArg_transport {c : VConstVal} (hc : c ∈ ty.ctors)
    {r₀ : RecArg} {B : VExpr}
    (hB : (ctorFields (VExpr.dropN np c.type))[r₀.fieldIndex]? = some B)
    (hr : recArg? U T np (idxTel U np ty).length r₀.fieldIndex B = some r₀)
    (mid : List VExpr) {g : Nat} (hg : mid.length = g)
    (As₂ : List VExpr) {d : Nat} (hd : As₂.length = d) :
    let r := r₀.instL (VLevel.params' U 1)
    let As := VExpr.liftTelN d (VExpr.liftTelN g r.binders r.fieldIndex) 0
    OnTel env (U+1)
        (As₂ ++ ((VExpr.liftTelN g
          ((ctorFieldsR U np c).take r.fieldIndex) 0).reverse ++
          (mid ++ (paramsTel U np ty).reverse))) As ∧
      env.SpineWF (U+1)
        (As.reverse ++
          (As₂ ++ ((VExpr.liftTelN g
            ((ctorFieldsR U np c).take r.fieldIndex) 0).reverse ++
            (mid ++ (paramsTel U np ty).reverse))))
        (VExpr.forallN
          (VExpr.liftTelN
            (r.fieldIndex + r.binders.length + g + d) (idxTel U np ty) 0)
          (.sort (l.inst (VLevel.params' U 1))))
        (r.indices.map fun e =>
          (e.liftN g (r.fieldIndex + r.binders.length)).liftN d r.binders.length)
        (.sort (l.inst (VLevel.params' U 1))) := by
  dsimp only
  have hjlt : r₀.fieldIndex < (ctorFields (VExpr.dropN np c.type)).length :=
    (List.getElem?_eq_some_iff.1 hB).1
  have hsem := fieldsWF_recArg (S.hfields c hc) r₀.fieldIndex B r₀ hB (by
    simpa [idxTel_length] using hr)
  simp only [Nat.zero_add] at hsem
  have htel₁ := hsem.1.instL (U' := U+1) VLevel.params'_one_wf
  have hsp₁ := hsem.2.instL (U' := U+1) VLevel.params'_one_wf
  have hctx :
      (((ctorFields (VExpr.dropN np c.type)).take r₀.fieldIndex).reverse ++
        (VExpr.telN np ty.type).reverse).map (VExpr.instL (VLevel.params' U 1)) =
      ((ctorFieldsR U np c).take r₀.fieldIndex).reverse ++
        (paramsTel U np ty).reverse := by
    simp [ctorFieldsR, paramsTel, List.map_reverse, List.map_take]
  rw [hctx] at htel₁
  rw [List.map_append, List.map_reverse, hctx] at hsp₁
  simp only [RecArg.instL, VExpr.instL_forallN, VExpr.liftTelN_instL,
    List.map_reverse] at htel₁ hsp₁
  have hjlen : ((ctorFieldsR U np c).take r₀.fieldIndex).length =
      r₀.fieldIndex := by
    simp only [ctorFieldsR, List.length_take, List.length_map]
    omega
  have W₁ := Ctx.LiftN.consTel (n := mid.length)
    ((ctorFieldsR U np c).take r₀.fieldIndex)
    (Ctx.LiftN.zero (Γ := (paramsTel U np ty).reverse) mid)
  rw [hjlen, Nat.add_zero] at W₁
  have htel₂ := htel₁.weakN S.ord W₁
  have hsp₂ := hsp₁.weakN S.ord
    (Ctx.LiftN.consTel
      (r₀.binders.map (VExpr.instL (VLevel.params' U 1))) W₁)
  rw [hg] at htel₂ hsp₂
  have W₂ := Ctx.LiftN.zero
    (Γ := (VExpr.liftTelN g
        ((ctorFieldsR U np c).take r₀.fieldIndex) 0).reverse ++
      (mid ++ (paramsTel U np ty).reverse)) As₂ (h := hd)
  have htel₃ := htel₂.weakN S.ord W₂
  have hsp₃ := hsp₂.weakN S.ord
    (Ctx.LiftN.consTel
      (VExpr.liftTelN g
        (r₀.binders.map (VExpr.instL (VLevel.params' U 1))) r₀.fieldIndex) W₂)
  refine ⟨?_, ?_⟩
  · simpa [RecArg.instL, List.append_assoc] using htel₃
  · simp only [List.length_map, VExpr.liftTelN_length, Nat.add_zero] at hsp₃
    rw [VExpr.liftN_forallN, VExpr.liftN_forallN,
      VExpr.liftTelN_liftTelN_hi' (r₀.fieldIndex + r₀.binders.length) g _ 0
        (by omega),
      VExpr.liftTelN_liftTelN_mid
        (r₀.fieldIndex + r₀.binders.length + g) d _ 0 r₀.binders.length
        (Nat.zero_le _) (by omega),
      show (ctorFields (VExpr.dropN np ty.type)).map
          (VExpr.instL (VLevel.params' U 1)) = idxTel U np ty from rfl] at hsp₃
    rw [show r₀.binders.length + r₀.fieldIndex =
      r₀.fieldIndex + r₀.binders.length from Nat.add_comm _ _] at hsp₃
    simpa [RecArg.instL, VExpr.instL, VExpr.liftN, List.map_map,
      Function.comp_def, List.append_assoc] using hsp₃

omit S in
/-- Apply a motive variable to a typed family-index spine and major premise.
Unlike `Stage3Env.motiveApp_hasType`, this helper is independent of the
recursor's minor-premise stack, so it also applies under a recursive
argument's private Pi telescope. -/
theorem motiveVarApp_hasType {Γ : List VExpr} {K : Nat}
    {idxs : List VExpr} {a : VExpr}
    (hM : env.HasType (U+1) Γ (.bvar K)
      ((motiveType U T np ty).liftN (K+1)))
    (hidx : env.SpineWF (U+1) Γ
      (VExpr.forallN (VExpr.liftTelN (K+1) (idxTel U np ty) 0)
        (.sort (l.inst (VLevel.params' U 1))))
      idxs (.sort (l.inst (VLevel.params' U 1))))
    (hlen : idxs.length = (idxTel U np ty).length)
    (ha : env.HasType (U+1) Γ a
      (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange (K+1) np ++ idxs))) :
    env.HasType (U+1) Γ
      (VExpr.appN (.bvar K) (idxs ++ [a])) (.sort (.param 0)) := by
  rw [motiveType_liftN] at hM
  have hshape := hidx.retarget
    (by simpa only [VExpr.liftTelN_length] using hlen)
    (.forallE (VExpr.appN (.const T (VLevel.params' U 1))
      (VExpr.bvarRevRange (K+1 + (idxTel U np ty).length) np ++
        VExpr.bvarRevRange 0 (idxTel U np ty).length))
      (.sort (.param 0)))
  rw [VExpr.instRev_forallE_sort, VExpr.instRev_appN,
    VExpr.instRev_closedN _ (C := .const T (VLevel.params' U 1)) trivial,
    List.map_append,
    VExpr.map_instRev_bvarRevRange_ge _ _ _ (by rw [hlen]; omega),
    show K+1+(idxTel U np ty).length-idxs.length = K+1 from by
      rw [hlen, Nat.add_sub_cancel],
    VExpr.bvarRevRange_congr' 0 hlen.symm,
    VExpr.map_instRev_bvarRevRange] at hshape
  rw [hlen] at hshape
  have hApp := hshape.hasType_appN hM
  rw [VExpr.appN_append]
  exact HasType.app hApp (by simpa using ha)

/-- One generalized induction-hypothesis entry is a type in the minor
premise context. Recursive Pi arguments become Pi-valued hypotheses whose
body applies both the motive and the recursive field to the same private
self-spine. -/
theorem Stage3Env.recArgMinor_isType {c : VConstVal} (hc : c ∈ ty.ctors)
    {r : RecArg}
    (hrmem : r ∈ recArgsR U T np (idxTel U np ty).length c)
    (Δ : List VExpr) (p : Nat) (hΔ : Δ.length = p) :
    env.IsType (U+1)
      (Δ ++ (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse))
      (r.minorIH (ctorFieldsR U np c).length p) := by
  obtain ⟨r₀, B, rfl, hB, hr₀⟩ := recArgsR_mem hrmem
  let r := r₀.instL (VLevel.params' U 1)
  let m := (ctorFieldsR U np c).length
  let j := r₀.fieldIndex
  let Fs := VExpr.liftTelN 1 (ctorFieldsR U np c) 0
  let As := r.minorBinders m p
  let idxs := r.indices.map fun e =>
    (e.liftN 1 (r.fieldIndex+r.binders.length)).liftN (m-r.fieldIndex+p) r.binders.length
  let Γ := Δ ++ Fs.reverse ++
    (motiveType U T np ty :: (paramsTel U np ty).reverse)
  have hjm : j < m := by
    simpa [j, m, RecArg.instL, ctorFieldsR_length] using recArgsR_lt _ hrmem
  have hFsLen : Fs.length = m := by simp [Fs, m, VExpr.liftTelN_length]
  have hstackLen : (Δ ++ (Fs.drop j).reverse).length = m-j+p := by
    simp only [List.length_append, List.length_reverse, List.length_drop, hFsLen, hΔ]
    omega
  have ht := S.recArg_transport hc hB hr₀ [motiveType U T np ty] rfl
    (Δ ++ (Fs.drop j).reverse) hstackLen
  simp only [List.length_singleton, RecArg.instL] at ht
  have hctx :
      (Δ ++ (Fs.drop j).reverse) ++
          ((VExpr.liftTelN 1 ((ctorFieldsR U np c).take j) 0).reverse ++
            ([motiveType U T np ty] ++ (paramsTel U np ty).reverse)) = Γ := by
    dsimp only [Γ, Fs]
    rw [← VExpr.liftTelN_take, List.append_assoc,
      ← List.append_assoc ((VExpr.liftTelN 1 (ctorFieldsR U np c) 0).drop j).reverse,
      ← List.reverse_append, List.take_append_drop, List.singleton_append,
      ← List.append_assoc]
  dsimp only [j] at ht hctx
  have htel : OnTel env (U+1) Γ As := by
    rw [hctx] at ht
    simpa [r, As, m, j, RecArg.instL] using ht.1
  have hsp : env.SpineWF (U+1) (As.reverse ++ Γ)
      (VExpr.forallN
        (VExpr.liftTelN (m+p+r.binders.length+1) (idxTel U np ty) 0)
        (.sort (l.inst (VLevel.params' U 1))))
      idxs (.sort (l.inst (VLevel.params' U 1))) := by
    rw [hctx] at ht
    simpa [r, As, idxs, m, j, RecArg.instL, List.append_assoc,
      show j + r₀.binders.length + 1 + (m-j+p) =
        m+p+r₀.binders.length+1 from by omega] using ht.2
  have hF : Γ[m-1-j+p]? =
      some ((B.instL (VLevel.params' U 1)).liftN 1 j) := by
    dsimp only [Γ, Fs]
    rw [getElem?_stack_mid Δ
        (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse
        (motiveType U T np ty :: (paramsTel U np ty).reverse)
        (i := m-1-j+p) (by rw [hΔ]; omega)
        (by simp only [hΔ, List.length_reverse, VExpr.liftTelN_length]; omega),
      show m - 1 - j + p - Δ.length = m - 1 - j from by rw [hΔ]; omega,
      List.getElem?_reverse (by rw [hFsLen]; omega),
      VExpr.liftTelN_length,
      show m - 1 - (m - 1 - j) = j from by omega,
      VExpr.liftTelN_getElem?, ctorFieldsR_getElem?, hB]
    simp
  have hlu := Lookup.of_getElem? hF
  rw [show m-1-j+p+1 = m-j+p from by omega] at hlu
  dsimp only [j, r] at hlu
  have hfield := recArg_minor_fieldType hr₀ m p (by simpa [j] using hjm)
  simp only [RecArg.instL] at hfield
  rw [hfield] at hlu
  have hf0 := VEnv.HasType.bvar (env := env) (U := U+1) hlu
  have hf := hf0.weakN S.ord (Ctx.LiftN.zero (Γ := Γ) As.reverse)
  have hmajor := VEnv.HasType.appN_selfSpine (env := env) (U := U+1)
    (As := As) (B := VExpr.appN (.const T (VLevel.params' U 1))
      (VExpr.bvarRevRange (m+p+r.binders.length+1) np ++ idxs))
    (Δ := []) (Γ := Γ) (by
      simpa [As, r, idxs, j, RecArg.instL, List.length_reverse,
        List.map_map, Function.comp_def] using hf)
  simp only [List.length_nil, VExpr.liftN_zero, List.nil_append] at hmajor
  have hAsLen : As.length = r.binders.length := by
    simp [As, RecArg.minorBinders, VExpr.liftTelN_length]
  have hmajorHead :
      (VExpr.bvar (m-1-r.fieldIndex+p)).liftN As.length =
        .bvar (m-1-r.fieldIndex+p+r.binders.length) := by
    simp only [VExpr.liftN, liftVar_base]
    congr 1
    rw [hAsLen]
    omega
  change env.HasType (U+1) (As.reverse ++ Γ)
    (((VExpr.bvar (m-1-r.fieldIndex+p)).liftN As.length).appN
      (VExpr.bvarRevRange 0 As.length))
    (VExpr.appN (.const T (VLevel.params' U 1))
      (VExpr.bvarRevRange (m+p+r.binders.length+1) np ++ idxs)) at hmajor
  rw [hmajorHead, hAsLen] at hmajor
  have hMget : (As.reverse ++ Γ)[m+p+r.binders.length]? =
      some (motiveType U T np ty) := by
    have hM0 := getElem?_rstack3 As.reverse (Δ ++ Fs.reverse)
      (motiveType U T np ty) (paramsTel U np ty).reverse
      (i := m+p+r.binders.length)
      (by simp [As, RecArg.minorBinders, r, m, Fs, hΔ, VExpr.liftTelN_length,
        RecArg.instL]; omega)
    simpa [Γ, List.append_assoc] using hM0
  have hM := VEnv.HasType.bvar (env := env) (U := U+1)
    (Lookup.of_getElem? hMget)
  have hlen : idxs.length = (idxTel U np ty).length := by
    simpa [idxs, r, RecArg.instL] using (recArg?_eq hr₀).2.2.2.1
  have hbody := motiveVarApp_hasType (env := env) (U := U) (T := T)
    (np := np) (l := l) (ty := ty) hM hsp hlen hmajor
  refine IsType.forallN htel ⟨VLevel.param 0, ?_⟩
  simpa [RecArg.minorIH, r, As, idxs, m, Γ, Fs, List.append_assoc] using hbody

/-- Well-formedness of the generalized induction-hypothesis telescope. Each
entry is supplied by `recArgMinor_isType`; recursive Pi arguments therefore
contribute one functional IH, not one IH per private binder. -/
theorem Stage3Env.ihsRec_onTel {c : VConstVal} (hc : c ∈ ty.ctors) :
    ∀ (rsSuf : List RecArg),
    (∀ r ∈ rsSuf, r ∈ recArgsR U T np (idxTel U np ty).length c) →
    ∀ (Δ : List VExpr) (p : Nat), Δ.length = p →
    OnTel env (U+1)
      (Δ ++ (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse))
      (ihsFromRecArgs (ctorFieldsR U np c).length rsSuf p)
  | [], _, _, _, _ => trivial
  | r :: rsSuf, hqs, Δ, p, hΔ =>
    ⟨S.recArgMinor_isType hc (hqs r (.head _)) Δ p hΔ,
      Stage3Env.ihsRec_onTel hc rsSuf (fun q hq => hqs q (.tail _ hq))
        (_ :: Δ) (p+1) (by simp [hΔ])⟩

/-- Transport the constructor result's index-spine typing into a rule or
minor context, like `spine_transport` but at the bottom of the full field
telescope. -/
theorem Stage3Env.result_transport {c : VConstVal} (hc : c ∈ ty.ctors)
    (mid : List VExpr) {g : Nat} (hg : mid.length = g)
    (As₂ : List VExpr) {d : Nat} (hd : As₂.length = d) :
    env.SpineWF (U+1)
      (As₂ ++ ((VExpr.liftTelN g (ctorFieldsR U np c) 0).reverse ++
        (mid ++ (paramsTel U np ty).reverse)))
      (VExpr.forallN
        (VExpr.liftTelN ((ctorFieldsR U np c).length + g + d) (idxTel U np ty) 0)
        (.sort (l.inst (VLevel.params' U 1))))
      ((ctorIdxs U np c).map fun e => (e.liftN g (ctorFieldsR U np c).length).liftN d)
      (.sort (l.inst (VLevel.params' U 1)))
    := by
  have hml : (ctorFieldsR U np c).length =
      (ctorFields (VExpr.dropN np c.type)).length := ctorFieldsR_length
  -- (1) the carried result spine, universes instantiated
  have h1 := (S.hresult c hc).instL (U' := U+1) VLevel.params'_one_wf
  rw [VExpr.instL_forallN, VExpr.liftTelN_instL,
    show ((ctorFields (VExpr.dropN np c.type)).reverse ++
        (VExpr.telN np ty.type).reverse).map (VExpr.instL (VLevel.params' U 1)) =
      (ctorFieldsR U np c).reverse ++ (paramsTel U np ty).reverse from by
      simp [ctorFieldsR, paramsTel, List.map_reverse],
    liftTelN_congr _ _ hml.symm] at h1
  -- (2) insert `mid` at the bottom of the fields
  have W₁ := Ctx.LiftN.consTel (n := mid.length) (ctorFieldsR U np c)
    (Ctx.LiftN.zero (Γ := (paramsTel U np ty).reverse) mid)
  rw [Nat.add_zero] at W₁
  have h2 := h1.weakN S.ord W₁
  rw [VExpr.liftN_forallN, hg] at h2
  -- (3) push the stack underneath
  have h3 := h2.weakN S.ord (Ctx.LiftN.zero (Γ := _) As₂ (h := hd))
  rw [VExpr.liftN_forallN] at h3
  rw [VExpr.liftTelN_liftTelN_hi' (ctorFieldsR U np c).length g _ 0 (by omega),
    VExpr.liftTelN_liftTelN,
    show (ctorFields (VExpr.dropN np ty.type)).map (VExpr.instL (VLevel.params' U 1)) =
      idxTel U np ty from rfl] at h3
  simpa [ctorIdxs, VExpr.instL, VExpr.liftN, List.map_map, Function.comp_def,
    List.append_assoc] using h3

/-- Well-formedness of the induction-hypothesis telescope of a minor
premise, at any suffix of the recursive positions and any depth. -/
theorem Stage3Env.ihs_onTel {c : VConstVal} (hc : c ∈ ty.ctors) :
    ∀ (rsSuf : List (Nat × List VExpr)),
    (∀ q ∈ rsSuf, q ∈ recPairsR U T np (idxTel U np ty).length c) →
    ∀ (Δ : List VExpr) (p : Nat), Δ.length = p →
    OnTel env (U+1)
      (Δ ++ (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse))
      (ihsFrom (ctorFieldsR U np c).length rsSuf p)
  | [], _, _, _, _ => trivial
  | (j, idxs) :: rsSuf, hqs, Δ, p, hΔ => by
    have hq := hqs _ (List.Mem.head _)
    obtain ⟨B, hBj0, hrec0, hidx0⟩ := recPairsR_mem hq
    have hBj : (ctorFields (VExpr.dropN np c.type))[j]? = some B := hBj0
    have hrec : isRecField U T np (ctorFields (VExpr.dropN np ty.type)).length j B =
        true := by
      have h : isRecField U T np (idxTel U np ty).length j B = true := hrec0
      rwa [idxTel_length] at h
    have hidx' : idxs = (recFieldIdxs np B).map (VExpr.instL (VLevel.params' U 1)) := hidx0
    have hjlt : j < (ctorFields (VExpr.dropN np c.type)).length := by
      simpa using recPairsR_lt _ hq
    have hml : (ctorFieldsR U np c).length =
        (ctorFields (VExpr.dropN np c.type)).length := ctorFieldsR_length
    have hml2 : (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).length =
        (ctorFieldsR U np c).length := VExpr.liftTelN_length ..
    have hni : (recFieldIdxs np B).length = (ctorFields (VExpr.dropN np ty.type)).length :=
      (isRecField_eq hrec).2.1
    refine ⟨?_, Stage3Env.ihs_onTel hc rsSuf (fun q hq' => hqs q (.tail _ hq'))
      (_ :: Δ) (p+1) (by simp [hΔ])⟩
    -- the motive variable
    have hM := getElem?_stack3 Δ
      ((VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse)
      (paramsTel U np ty).reverse (motiveType U T np ty)
      (i := (ctorFieldsR U np c).length + p)
      (by simp only [hΔ, List.length_reverse, VExpr.liftTelN_length]; omega)
    have hmlu := Lookup.of_getElem? hM
    rw [motiveType_liftN] at hmlu
    -- the transported index spine
    have hSp := S.spine_transport hc hBj hrec [motiveType U T np ty] (g := 1) rfl
      (Δ ++ ((VExpr.liftTelN 1 (ctorFieldsR U np c) 0).drop j).reverse)
      (d := (ctorFieldsR U np c).length - j + p)
      (by simp only [List.length_append, List.length_reverse, List.length_drop,
            hml2, hΔ]
          omega)
    rw [show (Δ ++ ((VExpr.liftTelN 1 (ctorFieldsR U np c) 0).drop j).reverse) ++
        ((VExpr.liftTelN 1 ((ctorFieldsR U np c).take j) 0).reverse ++
          ([motiveType U T np ty] ++ (paramsTel U np ty).reverse)) =
      Δ ++ (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse) from by
        rw [← VExpr.liftTelN_take, List.append_assoc,
          ← List.append_assoc (((VExpr.liftTelN 1 (ctorFieldsR U np c) 0).drop j).reverse),
          ← List.reverse_append, List.take_append_drop, List.singleton_append,
          ← List.append_assoc],
      liftTelN_congr _ _ (show j + 1 + ((ctorFieldsR U np c).length - j + p) =
        (ctorFieldsR U np c).length + p + 1 from by omega),
      ← hidx'] at hSp
    -- retarget onto the motive's pi and compute the instantiation
    have hlen : (idxs.map fun e => (e.liftN 1 j).liftN
        ((ctorFieldsR U np c).length - j + p)).length =
      (VExpr.liftTelN ((ctorFieldsR U np c).length + p + 1) (idxTel U np ty) 0).length := by
      simp only [List.length_map, VExpr.liftTelN_length, hidx', idxTel_length]
      exact hni
    have hRe := hSp.retarget hlen (.forallE (VExpr.appN (.const T (VLevel.params' U 1))
      (VExpr.bvarRevRange ((ctorFieldsR U np c).length + p + 1 + (idxTel U np ty).length) np ++
        VExpr.bvarRevRange 0 (idxTel U np ty).length))
      (.sort (.param 0)))
    rw [show VExpr.instRev (.forallE (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange ((ctorFieldsR U np c).length + p + 1 +
          (idxTel U np ty).length) np ++
          VExpr.bvarRevRange 0 (idxTel U np ty).length))
        (.sort (.param 0)))
        (idxs.map fun e => (e.liftN 1 j).liftN ((ctorFieldsR U np c).length - j + p)) =
      .forallE (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange ((ctorFieldsR U np c).length + p + 1) np ++
          idxs.map fun e => (e.liftN 1 j).liftN ((ctorFieldsR U np c).length - j + p)))
        (.sort (.param 0)) from by
      rw [VExpr.instRev_forallE_sort, VExpr.instRev_appN,
        VExpr.instRev_closedN _ (C := .const T (VLevel.params' U 1)) trivial,
        List.map_append,
        VExpr.map_instRev_bvarRevRange_ge _ _ _ (by
          simp only [List.length_map]
          rw [hidx', List.length_map, hni, ← idxTel_length (U := U) (ty := ty)]
          omega),
        show (ctorFieldsR U np c).length + p + 1 + (idxTel U np ty).length -
            (idxs.map fun e => (e.liftN 1 j).liftN
              ((ctorFieldsR U np c).length - j + p)).length =
          (ctorFieldsR U np c).length + p + 1 from by
          simp only [List.length_map]
          rw [hidx', List.length_map, hni, ← idxTel_length (U := U) (ty := ty)]
          omega,
        VExpr.bvarRevRange_congr' 0 (show (idxTel U np ty).length =
          (idxs.map fun e => (e.liftN 1 j).liftN
            ((ctorFieldsR U np c).length - j + p)).length from by
          simp only [List.length_map]
          rw [hidx', List.length_map, hni, ← idxTel_length (U := U) (ty := ty)]),
        VExpr.map_instRev_bvarRevRange]] at hRe
    -- the motive applied to the index arguments
    have hApp := hRe.hasType_appN (f := .bvar ((ctorFieldsR U np c).length + p)) (.bvar hmlu)
    -- the recursive-field variable
    have hF := getElem?_stack_mid Δ
      ((VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse)
      (motiveType U T np ty :: (paramsTel U np ty).reverse)
      (i := (ctorFieldsR U np c).length - 1 - j + p)
      (by rw [hΔ]; omega)
      (by simp only [hΔ, List.length_reverse, VExpr.liftTelN_length]; omega)
    rw [show (ctorFieldsR U np c).length - 1 - j + p - Δ.length =
        (ctorFieldsR U np c).length - 1 - j from by rw [hΔ]; omega,
      List.getElem?_reverse (by simp only [VExpr.liftTelN_length]; omega),
      VExpr.liftTelN_length,
      show (ctorFieldsR U np c).length - 1 -
        ((ctorFieldsR U np c).length - 1 - j) = j from by omega,
      VExpr.liftTelN_getElem?, ctorFieldsR_getElem?, hBj] at hF
    simp only [Option.map_some] at hF
    have hflu := Lookup.of_getElem? hF
    rw [show (((B.instL (VLevel.params' U 1)).liftN 1 (0+j)).liftN
        ((ctorFieldsR U np c).length - 1 - j + p + 1)) =
      VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange ((ctorFieldsR U np c).length + p + 1) np ++
          idxs.map fun e => (e.liftN 1 j).liftN
            ((ctorFieldsR U np c).length - j + p)) from by
      conv => lhs; rw [(isRecField_eq hrec).1]
      rw [VExpr.instL_appN, List.map_append, bvarRevRange_instL,
        show (VExpr.const T (VLevel.params U)).instL (VLevel.params' U 1) =
          .const T (VLevel.params' U 1) from by
          simp [VExpr.instL, VLevel.params_map_inst_params'],
        VExpr.liftN_appN, VExpr.liftN_appN, List.map_append, List.map_append,
        bvarRevRange_liftN_ge _ _ _ _ (by omega),
        bvarRevRange_liftN_ge _ _ _ _ (Nat.zero_le _),
        VExpr.bvarRevRange_congr np (show (ctorFieldsR U np c).length - 1 - j + p + 1 +
          (1 + j) = (ctorFieldsR U np c).length + p + 1 from by omega),
        ← hidx', List.map_map]
      refine congrArg (VExpr.appN _) (congrArg (VExpr.bvarRevRange _ np ++ ·) ?_)
      refine List.map_congr_left fun e _ => ?_
      show (e.liftN 1 (0+j)).liftN ((ctorFieldsR U np c).length - 1 - j + p + 1) = _
      rw [show (0+j) = j from Nat.zero_add j,
        show (ctorFieldsR U np c).length - 1 - j + p + 1 =
          (ctorFieldsR U np c).length - j + p from by omega]] at hflu
    have happ2 : env.HasType (U+1)
        (Δ ++ (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse))
        (VExpr.appN (.bvar ((ctorFieldsR U np c).length + p))
          ((idxs.map fun e => (e.liftN 1 j).liftN
            ((ctorFieldsR U np c).length - j + p)) ++
            [.bvar ((ctorFieldsR U np c).length - 1 - j + p)]))
        ((VExpr.sort (.param 0)).inst
          (.bvar ((ctorFieldsR U np c).length - 1 - j + p))) := by
      rw [VExpr.appN_append]
      exact HasType.app hApp (.bvar hflu)
    exact ⟨_, happ2⟩
theorem Stage3Env.ctorAppMin_hasType {c : VConstVal} (hc : c ∈ ty.ctors)
    (Δ : List VExpr) :
    env.HasType (U+1)
      (Δ ++ (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse))
      (VExpr.appN (.const c.name (VLevel.params' U 1))
        (VExpr.bvarRevRange (Δ.length + (ctorFieldsR U np c).length + 1) np ++
          VExpr.bvarRevRange Δ.length (ctorFieldsR U np c).length))
      (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange (Δ.length + (ctorFieldsR U np c).length + 1) np ++
          (ctorIdxs U np c).map fun e =>
            (e.liftN 1 (ctorFieldsR U np c).length).liftN Δ.length)) := by
  have hml : (ctorFieldsR U np c).length =
      (ctorFields (VExpr.dropN np c.type)).length := ctorFieldsR_length
  have hml2 : (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).length =
      (ctorFieldsR U np c).length := VExpr.liftTelN_length ..
  have hcl : (c.type.instL (VLevel.params' U 1)).ClosedN 0 :=
    (Ordered.closedC (ci := ⟨U, c.type⟩) S.ord (S.hcs c hc)).instL
  -- step A: consume the parameter telescope
  have hfA : env.HasType (U+1)
      ((Δ ++ (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse ++
        [motiveType U T np ty]) ++ (paramsTel U np ty).reverse ++ [])
      (.const c.name (VLevel.params' U 1))
      ((VExpr.forallN (paramsTel U np ty)
        (VExpr.forallN (ctorFieldsR U np c)
          (VExpr.appN (.const T (VLevel.params' U 1))
            (VExpr.bvarRevRange (0 + (ctorFields (VExpr.dropN np c.type)).length) np ++
              ctorIdxs U np c)))).liftN
        ((Δ ++ (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse ++
          [motiveType U T np ty]).length + (paramsTel U np ty).length)) := by
    rw [← S.ctorType_instL hc, hcl.liftN_eq (Nat.zero_le _)]
    exact S.cConst hc
  have hA := HasType.appN_selfSpine (env := env) (U := U+1) hfA
  -- step B: consume the field telescope
  rw [VExpr.liftN_forallN] at hA
  have hBeq : VExpr.forallN
      (VExpr.liftTelN ((Δ ++ (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse ++
          [motiveType U T np ty]).length) (ctorFieldsR U np c) 0)
      ((VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange (0 + (ctorFields (VExpr.dropN np c.type)).length) np ++
          ctorIdxs U np c)).liftN
        ((Δ ++ (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse ++
          [motiveType U T np ty]).length) (0 + (ctorFieldsR U np c).length)) =
      (VExpr.forallN (VExpr.liftTelN 1 (ctorFieldsR U np c) 0)
        ((VExpr.appN (.const T (VLevel.params' U 1))
          (VExpr.bvarRevRange (0 + (ctorFields (VExpr.dropN np c.type)).length) np ++
            ctorIdxs U np c)).liftN 1 (0 + (ctorFieldsR U np c).length))).liftN
        (Δ.length + (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).length) := by
    conv => rhs; rw [VExpr.liftN_forallN, VExpr.liftTelN_liftTelN,
      show (0:Nat) + (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).length =
        0 + (ctorFieldsR U np c).length from by rw [hml2],
      VExpr.liftN'_liftN_hi]
    rw [liftTelN_congr _ _ (show (1:Nat) + (Δ.length +
        (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).length) =
      (Δ ++ (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse ++
        [motiveType U T np ty]).length from by
      simp only [List.length_append, List.length_reverse, VExpr.liftTelN_length,
        List.length_singleton]
      omega),
      show (1 + (Δ.length + (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).length)) =
        (Δ ++ (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse ++
          [motiveType U T np ty]).length from by
        simp only [List.length_append, List.length_reverse, VExpr.liftTelN_length,
          List.length_singleton]
        omega]
  rw [hBeq] at hA
  have hB := HasType.appN_selfSpine (env := env) (U := U+1)
    (Δ := Δ) (Γ := motiveType U T np ty :: (paramsTel U np ty).reverse)
    (As := VExpr.liftTelN 1 (ctorFieldsR U np c) 0)
    (B := (VExpr.appN (.const T (VLevel.params' U 1))
      (VExpr.bvarRevRange (0 + (ctorFields (VExpr.dropN np c.type)).length) np ++
        ctorIdxs U np c)).liftN 1 (0 + (ctorFieldsR U np c).length))
    (by simpa [List.append_assoc, List.append_nil] using hA)
  rw [show (paramsTel U np ty).length = np from by
      simp [paramsTel, List.length_map, S.hlen],
    VExpr.bvarRevRange_congr np (show Δ.length +
      ((VExpr.liftTelN 1 (ctorFieldsR U np c) 0).length + 1) =
      Δ.length + (ctorFieldsR U np c).length + 1 from by omega),
    VExpr.liftTelN_length] at hB
  rw [show ((VExpr.appN (.const T (VLevel.params' U 1))
      (VExpr.bvarRevRange (0 + (ctorFields (VExpr.dropN np c.type)).length) np ++
        ctorIdxs U np c)).liftN 1 (0 + (ctorFieldsR U np c).length)).liftN Δ.length =
    VExpr.appN (.const T (VLevel.params' U 1))
      (VExpr.bvarRevRange (Δ.length + (ctorFieldsR U np c).length + 1) np ++
        (ctorIdxs U np c).map fun e =>
          (e.liftN 1 (ctorFieldsR U np c).length).liftN Δ.length) from by
    rw [VExpr.liftN_appN, VExpr.liftN_appN, List.map_append, List.map_append,
      Nat.zero_add ((ctorFieldsR U np c).length),
      bvarRevRange_liftN_ge _ _ _ _ (by omega),
      bvarRevRange_liftN_ge _ _ _ _ (Nat.zero_le _),
      VExpr.bvarRevRange_congr np (show Δ.length +
        (1 + (0 + (ctorFields (VExpr.dropN np c.type)).length)) =
        Δ.length + (ctorFieldsR U np c).length + 1 from by omega),
      List.map_map]
    rfl] at hB
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
theorem Stage3Env.minor_isType {c : VConstVal} (hc : c ∈ ty.ctors) :
    env.IsType (U+1) (motiveType U T np ty :: (paramsTel U np ty).reverse)
      (minorType U T np ty c) := by
  simp only [minorType]
  refine IsType.forallN ?_ ?_
  · have h0 := S.fieldsWF_onTel _ [] 0 rfl (by simpa using S.hfields c hc)
    have h1 := h0.weakN S.ord (.zero [motiveType U T np ty])
    simpa [List.map_reverse, paramsTel] using h1
  · refine IsType.forallN (S.ihs_onTel hc _ (fun q hq => hq) [] 0 rfl) ?_
    have hml2 : (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).length =
        (ctorFieldsR U np c).length := VExpr.liftTelN_length ..
    have hrlen : ((ihsFrom (ctorFieldsR U np c).length
        (recPairsR U T np (idxTel U np ty).length c) 0).reverse).length =
        (recPairsR U T np (idxTel U np ty).length c).length := by
      simp [ihsFrom_length]
    -- the motive variable
    have hM := getElem?_rstack3 ((ihsFrom (ctorFieldsR U np c).length
        (recPairsR U T np (idxTel U np ty).length c) 0).reverse)
      ((VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse)
      (motiveType U T np ty) (paramsTel U np ty).reverse
      (i := (ctorFieldsR U np c).length +
        (recPairsR U T np (idxTel U np ty).length c).length)
      (by simp only [List.length_reverse, ihsFrom_length, VExpr.liftTelN_length]; omega)
    have hmlu := Lookup.of_getElem? hM
    rw [motiveType_liftN] at hmlu
    -- the transported result spine
    have hSp := S.result_transport hc [motiveType U T np ty] (g := 1) rfl
      ((ihsFrom (ctorFieldsR U np c).length
        (recPairsR U T np (idxTel U np ty).length c) 0).reverse)
      (d := (recPairsR U T np (idxTel U np ty).length c).length) hrlen
    rw [liftTelN_congr _ _ (show (ctorFieldsR U np c).length + 1 +
        (recPairsR U T np (idxTel U np ty).length c).length =
      (ctorFieldsR U np c).length +
        (recPairsR U T np (idxTel U np ty).length c).length + 1 from by omega)] at hSp
    have hlen : ((ctorIdxs U np c).map fun e =>
        (e.liftN 1 (ctorFieldsR U np c).length).liftN
          (recPairsR U T np (idxTel U np ty).length c).length).length =
      (VExpr.liftTelN ((ctorFieldsR U np c).length +
        (recPairsR U T np (idxTel U np ty).length c).length + 1)
        (idxTel U np ty) 0).length := by
      simp only [List.length_map, VExpr.liftTelN_length, ctorIdxs_length, idxTel_length]
      have hc3 := stage3Ctor_eq (S.hs3 c hc)
      exact hc3.2.1
    have hRe := hSp.retarget hlen (.forallE (VExpr.appN (.const T (VLevel.params' U 1))
      (VExpr.bvarRevRange ((ctorFieldsR U np c).length +
        (recPairsR U T np (idxTel U np ty).length c).length + 1 +
          (idxTel U np ty).length) np ++
        VExpr.bvarRevRange 0 (idxTel U np ty).length))
      (.sort (.param 0)))
    rw [show VExpr.instRev (.forallE (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange ((ctorFieldsR U np c).length +
          (recPairsR U T np (idxTel U np ty).length c).length + 1 +
            (idxTel U np ty).length) np ++
          VExpr.bvarRevRange 0 (idxTel U np ty).length))
        (.sort (.param 0)))
        ((ctorIdxs U np c).map fun e =>
          (e.liftN 1 (ctorFieldsR U np c).length).liftN
            (recPairsR U T np (idxTel U np ty).length c).length) =
      .forallE (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange ((ctorFieldsR U np c).length +
          (recPairsR U T np (idxTel U np ty).length c).length + 1) np ++
          (ctorIdxs U np c).map fun e =>
            (e.liftN 1 (ctorFieldsR U np c).length).liftN
              (recPairsR U T np (idxTel U np ty).length c).length))
        (.sort (.param 0)) from by
      rw [VExpr.instRev_forallE_sort, VExpr.instRev_appN,
        VExpr.instRev_closedN _ (C := .const T (VLevel.params' U 1)) trivial,
        List.map_append,
        VExpr.map_instRev_bvarRevRange_ge _ _ _ (by
          rw [hlen, VExpr.liftTelN_length]; omega),
        show (ctorFieldsR U np c).length +
            (recPairsR U T np (idxTel U np ty).length c).length + 1 +
            (idxTel U np ty).length -
            ((ctorIdxs U np c).map fun e =>
              (e.liftN 1 (ctorFieldsR U np c).length).liftN
                (recPairsR U T np (idxTel U np ty).length c).length).length =
          (ctorFieldsR U np c).length +
            (recPairsR U T np (idxTel U np ty).length c).length + 1 from by
          rw [hlen, VExpr.liftTelN_length]
          omega,
        VExpr.bvarRevRange_congr' 0 (show (idxTel U np ty).length =
          ((ctorIdxs U np c).map fun e =>
            (e.liftN 1 (ctorFieldsR U np c).length).liftN
              (recPairsR U T np (idxTel U np ty).length c).length).length from by
          rw [hlen, VExpr.liftTelN_length]),
        VExpr.map_instRev_bvarRevRange]] at hRe
    -- the motive applied to the result indices
    have hApp := hRe.hasType_appN (f := .bvar ((ctorFieldsR U np c).length +
      (recPairsR U T np (idxTel U np ty).length c).length)) (.bvar hmlu)
    -- the constructor application
    have hctor := S.ctorAppMin_hasType hc
      ((ihsFrom (ctorFieldsR U np c).length
        (recPairsR U T np (idxTel U np ty).length c) 0).reverse)
    rw [hrlen] at hctor
    rw [VExpr.bvarRevRange_congr np (show
        (recPairsR U T np (idxTel U np ty).length c).length +
          (ctorFieldsR U np c).length + 1 =
        (ctorFieldsR U np c).length +
          (recPairsR U T np (idxTel U np ty).length c).length + 1 from by omega)] at hctor
    have happ2 : env.HasType (U+1)
        ((ihsFrom (ctorFieldsR U np c).length
          (recPairsR U T np (idxTel U np ty).length c) 0).reverse ++
          ((VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse ++
            (motiveType U T np ty :: (paramsTel U np ty).reverse)))
        (VExpr.appN (.bvar ((ctorFieldsR U np c).length +
          (recPairsR U T np (idxTel U np ty).length c).length))
          (((ctorIdxs U np c).map fun e =>
            (e.liftN 1 (ctorFieldsR U np c).length).liftN
              (recPairsR U T np (idxTel U np ty).length c).length) ++
            [VExpr.appN (.const c.name (VLevel.params' U 1))
              (VExpr.bvarRevRange ((recPairsR U T np (idxTel U np ty).length c).length +
                (ctorFieldsR U np c).length + 1) np ++
                VExpr.bvarRevRange (recPairsR U T np (idxTel U np ty).length c).length
                  (ctorFieldsR U np c).length)]))
        ((VExpr.sort (.param 0)).inst
          (VExpr.appN (.const c.name (VLevel.params' U 1))
            (VExpr.bvarRevRange ((recPairsR U T np (idxTel U np ty).length c).length +
              (ctorFieldsR U np c).length + 1) np ++
              VExpr.bvarRevRange (recPairsR U T np (idxTel U np ty).length c).length
                (ctorFieldsR U np c).length))) := by
      rw [VExpr.appN_append,
        VExpr.bvarRevRange_congr np (show
          (recPairsR U T np (idxTel U np ty).length c).length +
            (ctorFieldsR U np c).length + 1 =
          (ctorFieldsR U np c).length +
            (recPairsR U T np (idxTel U np ty).length c).length + 1 from by omega)]
      exact HasType.app hApp (by simpa [List.append_assoc] using hctor)
    exact ⟨_, by simpa [List.append_assoc] using happ2⟩

/-- The generalized minor premise is a type over `params ++ [motive]`.
This is the preservation theorem used by `minorTypeRec`; it differs from
`minor_isType` only in the functional-IH telescope supplied for recursive
Pi arguments. -/
theorem Stage3Env.minor_isTypeRec {c : VConstVal} (hc : c ∈ ty.ctors) :
    env.IsType (U+1) (motiveType U T np ty :: (paramsTel U np ty).reverse)
      (minorTypeRec U T np ty c) := by
  simp only [minorTypeRec]
  refine IsType.forallN ?_ ?_
  · have h0 := S.fieldsWF_onTel _ [] 0 rfl (by simpa using S.hfields c hc)
    have h1 := h0.weakN S.ord (.zero [motiveType U T np ty])
    simpa [List.map_reverse, paramsTel] using h1
  · refine IsType.forallN (S.ihsRec_onTel hc _ (fun q hq => hq) [] 0 rfl) ?_
    have hml2 : (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).length =
        (ctorFieldsR U np c).length := VExpr.liftTelN_length ..
    have hrlen : ((ihsFromRecArgs (ctorFieldsR U np c).length
        (recArgsR U T np (idxTel U np ty).length c) 0).reverse).length =
        (recArgsR U T np (idxTel U np ty).length c).length := by
      simp [ihsFromRecArgs_length]
    -- the motive variable
    have hM := getElem?_rstack3 ((ihsFromRecArgs (ctorFieldsR U np c).length
        (recArgsR U T np (idxTel U np ty).length c) 0).reverse)
      ((VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse)
      (motiveType U T np ty) (paramsTel U np ty).reverse
      (i := (ctorFieldsR U np c).length +
        (recArgsR U T np (idxTel U np ty).length c).length)
      (by simp only [List.length_reverse, ihsFromRecArgs_length,
        VExpr.liftTelN_length]; omega)
    have hmlu := Lookup.of_getElem? hM
    rw [motiveType_liftN] at hmlu
    -- the transported result spine
    have hSp := S.result_transport hc [motiveType U T np ty] (g := 1) rfl
      ((ihsFromRecArgs (ctorFieldsR U np c).length
        (recArgsR U T np (idxTel U np ty).length c) 0).reverse)
      (d := (recArgsR U T np (idxTel U np ty).length c).length) hrlen
    rw [liftTelN_congr _ _ (show (ctorFieldsR U np c).length + 1 +
        (recArgsR U T np (idxTel U np ty).length c).length =
      (ctorFieldsR U np c).length +
        (recArgsR U T np (idxTel U np ty).length c).length + 1 from by omega)] at hSp
    have hlen : ((ctorIdxs U np c).map fun e =>
        (e.liftN 1 (ctorFieldsR U np c).length).liftN
          (recArgsR U T np (idxTel U np ty).length c).length).length =
      (VExpr.liftTelN ((ctorFieldsR U np c).length +
        (recArgsR U T np (idxTel U np ty).length c).length + 1)
        (idxTel U np ty) 0).length := by
      simp only [List.length_map, VExpr.liftTelN_length, ctorIdxs_length, idxTel_length]
      have hc3 := stage3Ctor_eq (S.hs3 c hc)
      exact hc3.2.1
    have hRe := hSp.retarget hlen (.forallE (VExpr.appN (.const T (VLevel.params' U 1))
      (VExpr.bvarRevRange ((ctorFieldsR U np c).length +
        (recArgsR U T np (idxTel U np ty).length c).length + 1 +
          (idxTel U np ty).length) np ++
        VExpr.bvarRevRange 0 (idxTel U np ty).length))
      (.sort (.param 0)))
    rw [show VExpr.instRev (.forallE (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange ((ctorFieldsR U np c).length +
          (recArgsR U T np (idxTel U np ty).length c).length + 1 +
            (idxTel U np ty).length) np ++
          VExpr.bvarRevRange 0 (idxTel U np ty).length))
        (.sort (.param 0)))
        ((ctorIdxs U np c).map fun e =>
          (e.liftN 1 (ctorFieldsR U np c).length).liftN
            (recArgsR U T np (idxTel U np ty).length c).length) =
      .forallE (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange ((ctorFieldsR U np c).length +
          (recArgsR U T np (idxTel U np ty).length c).length + 1) np ++
          (ctorIdxs U np c).map fun e =>
            (e.liftN 1 (ctorFieldsR U np c).length).liftN
              (recArgsR U T np (idxTel U np ty).length c).length))
        (.sort (.param 0)) from by
      rw [VExpr.instRev_forallE_sort, VExpr.instRev_appN,
        VExpr.instRev_closedN _ (C := .const T (VLevel.params' U 1)) trivial,
        List.map_append,
        VExpr.map_instRev_bvarRevRange_ge _ _ _ (by
          rw [hlen, VExpr.liftTelN_length]; omega),
        show (ctorFieldsR U np c).length +
            (recArgsR U T np (idxTel U np ty).length c).length + 1 +
            (idxTel U np ty).length -
            ((ctorIdxs U np c).map fun e =>
              (e.liftN 1 (ctorFieldsR U np c).length).liftN
                (recArgsR U T np (idxTel U np ty).length c).length).length =
          (ctorFieldsR U np c).length +
            (recArgsR U T np (idxTel U np ty).length c).length + 1 from by
          rw [hlen, VExpr.liftTelN_length]
          omega,
        VExpr.bvarRevRange_congr' 0 (show (idxTel U np ty).length =
          ((ctorIdxs U np c).map fun e =>
            (e.liftN 1 (ctorFieldsR U np c).length).liftN
              (recArgsR U T np (idxTel U np ty).length c).length).length from by
          rw [hlen, VExpr.liftTelN_length]),
        VExpr.map_instRev_bvarRevRange]] at hRe
    -- the motive applied to the result indices
    have hApp := hRe.hasType_appN (f := .bvar ((ctorFieldsR U np c).length +
      (recArgsR U T np (idxTel U np ty).length c).length)) (.bvar hmlu)
    -- the constructor application
    have hctor := S.ctorAppMin_hasType hc
      ((ihsFromRecArgs (ctorFieldsR U np c).length
        (recArgsR U T np (idxTel U np ty).length c) 0).reverse)
    rw [hrlen] at hctor
    rw [VExpr.bvarRevRange_congr np (show
        (recArgsR U T np (idxTel U np ty).length c).length +
          (ctorFieldsR U np c).length + 1 =
        (ctorFieldsR U np c).length +
          (recArgsR U T np (idxTel U np ty).length c).length + 1 from by omega)] at hctor
    have happ2 : env.HasType (U+1)
        ((ihsFromRecArgs (ctorFieldsR U np c).length
          (recArgsR U T np (idxTel U np ty).length c) 0).reverse ++
          ((VExpr.liftTelN 1 (ctorFieldsR U np c) 0).reverse ++
            (motiveType U T np ty :: (paramsTel U np ty).reverse)))
        (VExpr.appN (.bvar ((ctorFieldsR U np c).length +
          (recArgsR U T np (idxTel U np ty).length c).length))
          (((ctorIdxs U np c).map fun e =>
            (e.liftN 1 (ctorFieldsR U np c).length).liftN
              (recArgsR U T np (idxTel U np ty).length c).length) ++
            [VExpr.appN (.const c.name (VLevel.params' U 1))
              (VExpr.bvarRevRange ((recArgsR U T np (idxTel U np ty).length c).length +
                (ctorFieldsR U np c).length + 1) np ++
                VExpr.bvarRevRange (recArgsR U T np (idxTel U np ty).length c).length
                  (ctorFieldsR U np c).length)]))
        ((VExpr.sort (.param 0)).inst
          (VExpr.appN (.const c.name (VLevel.params' U 1))
            (VExpr.bvarRevRange ((recArgsR U T np (idxTel U np ty).length c).length +
              (ctorFieldsR U np c).length + 1) np ++
              VExpr.bvarRevRange (recArgsR U T np (idxTel U np ty).length c).length
                (ctorFieldsR U np c).length))) := by
      rw [VExpr.appN_append,
        VExpr.bvarRevRange_congr np (show
          (recArgsR U T np (idxTel U np ty).length c).length +
            (ctorFieldsR U np c).length + 1 =
          (ctorFieldsR U np c).length +
            (recArgsR U T np (idxTel U np ty).length c).length + 1 from by omega)]
      exact HasType.app hApp (by simpa [List.append_assoc] using hctor)
    exact ⟨_, by simpa [List.append_assoc] using happ2⟩

/-- The minor premises, in position, are a telescope over
`params ++ [motive]`. -/
theorem Stage3Env.minorTypes_onTel :
    ∀ (cs' : List VConstVal), (∀ c ∈ cs', c ∈ ty.ctors) →
    ∀ (Δ : List VExpr) (i : Nat), Δ.length = i →
    OnTel env (U+1) (Δ ++ (motiveType U T np ty :: (paramsTel U np ty).reverse))
      (minorTypes U T np ty cs' i)
  | [], _, _, _, _ => trivial
  | c :: cs', hsub, Δ, i, hΔ =>
    ⟨by
      rw [← hΔ]
      exact (S.minor_isType (hsub c (.head _))).weakN S.ord (.zero Δ),
    Stage3Env.minorTypes_onTel cs' (fun c h => hsub c (.tail _ h)) (_ :: Δ) (i+1)
      (by simp [hΔ])⟩

/-- Generalized minor premises, including functional recursive hypotheses,
form a telescope over `params ++ [motive]`. -/
theorem Stage3Env.minorTypesRec_onTel :
    ∀ (cs' : List VConstVal), (∀ c ∈ cs', c ∈ ty.ctors) →
    ∀ (Δ : List VExpr) (i : Nat), Δ.length = i →
    OnTel env (U+1) (Δ ++ (motiveType U T np ty :: (paramsTel U np ty).reverse))
      (minorTypesRec U T np ty cs' i)
  | [], _, _, _, _ => trivial
  | c :: cs', hsub, Δ, i, hΔ =>
    ⟨by
      rw [← hΔ]
      exact (S.minor_isTypeRec (hsub c (.head _))).weakN S.ord (.zero Δ),
    Stage3Env.minorTypesRec_onTel cs' (fun c h => hsub c (.tail _ h)) (_ :: Δ) (i+1)
      (by simp [hΔ])⟩

/-- The generated recursor type is well-formed. -/
theorem Stage3Env.recType_isType : env.IsType (U+1) [] (recType U T np ty) := by
  have hP : OnTel env (U+1) [] (paramsTel U np ty) := by
    have := S.hparams.of_append.1.instL (U' := U+1) VLevel.params'_one_wf
    simpa [paramsTel] using this
  refine IsType.forallN hP ?_
  simp only [List.append_nil]
  refine IsType.forallE S.motive_isType ?_
  refine IsType.forallN
    (by simpa using S.minorTypes_onTel ty.ctors (fun _ h => h) [] 0 rfl) ?_
  have hI : OnTel env (U+1)
      ((minorTypes U T np ty ty.ctors).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse))
      (VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0) := by
    have h := S.idxTel_onTel.weakN S.ord
      (Ctx.LiftN.zero (n := ty.ctors.length + 1)
        (Γ := (paramsTel U np ty).reverse)
        ((minorTypes U T np ty ty.ctors).reverse ++ [motiveType U T np ty])
        (h := by simp [minorTypes_length]))
    simpa [List.append_assoc] using h
  refine IsType.forallN hI ?_
  have hmaj : env.HasType (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0).reverse ++
        ((minorTypes U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
          VExpr.bvarRevRange 0 (idxTel U np ty).length))
      (.sort (l.inst (VLevel.params' U 1))) := by
    have W := Ctx.LiftN.consTel (n := ty.ctors.length + 1) (idxTel U np ty)
      (Ctx.LiftN.zero (n := ty.ctors.length + 1)
        (Γ := (paramsTel U np ty).reverse)
        ((minorTypes U T np ty ty.ctors).reverse ++ [motiveType U T np ty])
        (h := by simp [minorTypes_length]))
    have h := S.motiveTApp_hasType.weakN S.ord W
    simp only [Nat.add_zero, VExpr.liftN_appN, VExpr.liftN, List.map_append] at h
    rw [bvarRevRange_liftN_ge _ _ _ _ (Nat.le_refl _),
      VExpr.bvarRevRange_liftN_high _ _ _ _ (by omega),
      VExpr.bvarRevRange_congr np (show
        ty.ctors.length + 1 + (idxTel U np ty).length =
          (idxTel U np ty).length + ty.ctors.length + 1 from by omega)] at h
    simpa [List.append_assoc] using h
  refine IsType.forallE ⟨_, hmaj⟩ ?_
  have hM := getElem?_rstack3
    [VExpr.appN (.const T (VLevel.params' U 1))
      (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
        VExpr.bvarRevRange 0 (idxTel U np ty).length)]
    ((VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0).reverse ++
      (minorTypes U T np ty ty.ctors).reverse)
    (motiveType U T np ty) (paramsTel U np ty).reverse
    (i := (idxTel U np ty).length + ty.ctors.length + 1)
    (by simp only [List.length_singleton, List.length_append, List.length_reverse,
      VExpr.liftTelN_length, minorTypes_length]; omega)
  have hmlu := Lookup.of_getElem? (by
    simpa only [List.singleton_append, List.append_assoc] using hM)
  rw [show (motiveType U T np ty).liftN
        ((idxTel U np ty).length + ty.ctors.length + 1 + 1) =
      ((motiveType U T np ty).liftN (ty.ctors.length + 1)).liftN
        ((idxTel U np ty).length + 1) from by
      rw [VExpr.liftN_liftN]
      congr 1
      omega,
    motiveType_liftN] at hmlu
  have hfun : env.HasType (U+1)
      (VExpr.appN (.const T (VLevel.params' U 1))
          (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
            VExpr.bvarRevRange 0 (idxTel U np ty).length) ::
        ((VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0).reverse ++
          ((minorTypes U T np ty ty.ctors).reverse ++
            (motiveType U T np ty :: (paramsTel U np ty).reverse))))
      (.bvar ((idxTel U np ty).length + ty.ctors.length + 1))
      ((VExpr.forallN
        (VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0)
        (.forallE (VExpr.appN (.const T (VLevel.params' U 1))
          (VExpr.bvarRevRange (ty.ctors.length + 1 + (idxTel U np ty).length) np ++
            VExpr.bvarRevRange 0 (idxTel U np ty).length))
          (.sort (.param 0)))).liftN
        (1 + (VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0).length)) := by
    exact .bvar (by
      simpa [List.append_assoc, VExpr.liftTelN_length, Nat.add_comm] using hmlu)
  have hMapp := HasType.appN_selfSpine
    (As := VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0)
    (Δ := [VExpr.appN (.const T (VLevel.params' U 1))
      (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
        VExpr.bvarRevRange 0 (idxTel U np ty).length)])
    (Γ := (minorTypes U T np ty ty.ctors).reverse ++
      (motiveType U T np ty :: (paramsTel U np ty).reverse))
    (f := .bvar ((idxTel U np ty).length + ty.ctors.length + 1))
    hfun
  have h0 :
      (VExpr.appN (.const T (VLevel.params' U 1))
          (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
            VExpr.bvarRevRange 0 (idxTel U np ty).length) ::
        ((VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0).reverse ++
          ((minorTypes U T np ty ty.ctors).reverse ++
            (motiveType U T np ty :: (paramsTel U np ty).reverse))))[0]? =
        some (VExpr.appN (.const T (VLevel.params' U 1))
          (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
            VExpr.bvarRevRange 0 (idxTel U np ty).length)) := rfl
  have harg := HasType.bvar (env := env) (U := U+1) (Lookup.of_getElem? h0)
  have harg' : env.HasType (U+1)
      ([VExpr.appN (.const T (VLevel.params' U 1))
          (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
            VExpr.bvarRevRange 0 (idxTel U np ty).length)] ++
        (VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0).reverse ++
        ((minorTypes U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (.bvar 0)
      ((VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange (ty.ctors.length + 1 + (idxTel U np ty).length) np ++
          VExpr.bvarRevRange 0 (idxTel U np ty).length)).liftN
        [VExpr.appN (.const T (VLevel.params' U 1))
          (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
            VExpr.bvarRevRange 0 (idxTel U np ty).length)].length) := by
    simpa [List.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using harg
  have happ := HasType.app hMapp harg'
  exact ⟨_, by
    simpa [List.append_assoc, VExpr.liftTelN_length] using happ⟩

/-- The generalized recursor type, whose constructor minors include
functional IHs for recursive Pi arguments, is well-formed. -/
theorem Stage3Env.recTypeRec_isType : env.IsType (U+1) [] (recTypeRec U T np ty) := by
  have hP : OnTel env (U+1) [] (paramsTel U np ty) := by
    have := S.hparams.of_append.1.instL (U' := U+1) VLevel.params'_one_wf
    simpa [paramsTel] using this
  refine IsType.forallN hP ?_
  simp only [List.append_nil]
  refine IsType.forallE S.motive_isType ?_
  refine IsType.forallN
    (by simpa using S.minorTypesRec_onTel ty.ctors (fun _ h => h) [] 0 rfl) ?_
  have hI : OnTel env (U+1)
      ((minorTypesRec U T np ty ty.ctors).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse))
      (VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0) := by
    have h := S.idxTel_onTel.weakN S.ord
      (Ctx.LiftN.zero (n := ty.ctors.length + 1)
        (Γ := (paramsTel U np ty).reverse)
        ((minorTypesRec U T np ty ty.ctors).reverse ++ [motiveType U T np ty])
        (h := by simp [minorTypesRec_length]))
    simpa [List.append_assoc] using h
  refine IsType.forallN hI ?_
  have hmaj : env.HasType (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0).reverse ++
        ((minorTypesRec U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
          VExpr.bvarRevRange 0 (idxTel U np ty).length))
      (.sort (l.inst (VLevel.params' U 1))) := by
    have W := Ctx.LiftN.consTel (n := ty.ctors.length + 1) (idxTel U np ty)
      (Ctx.LiftN.zero (n := ty.ctors.length + 1)
        (Γ := (paramsTel U np ty).reverse)
        ((minorTypesRec U T np ty ty.ctors).reverse ++ [motiveType U T np ty])
        (h := by simp [minorTypesRec_length]))
    have h := S.motiveTApp_hasType.weakN S.ord W
    simp only [Nat.add_zero, VExpr.liftN_appN, VExpr.liftN, List.map_append] at h
    rw [bvarRevRange_liftN_ge _ _ _ _ (Nat.le_refl _),
      VExpr.bvarRevRange_liftN_high _ _ _ _ (by omega),
      VExpr.bvarRevRange_congr np (show
        ty.ctors.length + 1 + (idxTel U np ty).length =
          (idxTel U np ty).length + ty.ctors.length + 1 from by omega)] at h
    simpa [List.append_assoc] using h
  refine IsType.forallE ⟨_, hmaj⟩ ?_
  have hM := getElem?_rstack3
    [VExpr.appN (.const T (VLevel.params' U 1))
      (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
        VExpr.bvarRevRange 0 (idxTel U np ty).length)]
    ((VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0).reverse ++
      (minorTypesRec U T np ty ty.ctors).reverse)
    (motiveType U T np ty) (paramsTel U np ty).reverse
    (i := (idxTel U np ty).length + ty.ctors.length + 1)
    (by simp only [List.length_singleton, List.length_append, List.length_reverse,
      VExpr.liftTelN_length, minorTypesRec_length]; omega)
  have hmlu := Lookup.of_getElem? (by
    simpa only [List.singleton_append, List.append_assoc] using hM)
  rw [show (motiveType U T np ty).liftN
        ((idxTel U np ty).length + ty.ctors.length + 1 + 1) =
      ((motiveType U T np ty).liftN (ty.ctors.length + 1)).liftN
        ((idxTel U np ty).length + 1) from by
      rw [VExpr.liftN_liftN]
      congr 1
      omega,
    motiveType_liftN] at hmlu
  have hfun : env.HasType (U+1)
      (VExpr.appN (.const T (VLevel.params' U 1))
          (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
            VExpr.bvarRevRange 0 (idxTel U np ty).length) ::
        ((VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0).reverse ++
          ((minorTypesRec U T np ty ty.ctors).reverse ++
            (motiveType U T np ty :: (paramsTel U np ty).reverse))))
      (.bvar ((idxTel U np ty).length + ty.ctors.length + 1))
      ((VExpr.forallN
        (VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0)
        (.forallE (VExpr.appN (.const T (VLevel.params' U 1))
          (VExpr.bvarRevRange (ty.ctors.length + 1 + (idxTel U np ty).length) np ++
            VExpr.bvarRevRange 0 (idxTel U np ty).length))
          (.sort (.param 0)))).liftN
        (1 + (VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0).length)) := by
    exact .bvar (by
      simpa [List.append_assoc, VExpr.liftTelN_length, Nat.add_comm] using hmlu)
  have hMapp := HasType.appN_selfSpine
    (As := VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0)
    (Δ := [VExpr.appN (.const T (VLevel.params' U 1))
      (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
        VExpr.bvarRevRange 0 (idxTel U np ty).length)])
    (Γ := (minorTypesRec U T np ty ty.ctors).reverse ++
      (motiveType U T np ty :: (paramsTel U np ty).reverse))
    (f := .bvar ((idxTel U np ty).length + ty.ctors.length + 1))
    hfun
  have h0 :
      (VExpr.appN (.const T (VLevel.params' U 1))
          (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
            VExpr.bvarRevRange 0 (idxTel U np ty).length) ::
        ((VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0).reverse ++
          ((minorTypesRec U T np ty ty.ctors).reverse ++
            (motiveType U T np ty :: (paramsTel U np ty).reverse))))[0]? =
        some (VExpr.appN (.const T (VLevel.params' U 1))
          (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
            VExpr.bvarRevRange 0 (idxTel U np ty).length)) := rfl
  have harg := HasType.bvar (env := env) (U := U+1) (Lookup.of_getElem? h0)
  have harg' : env.HasType (U+1)
      ([VExpr.appN (.const T (VLevel.params' U 1))
          (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
            VExpr.bvarRevRange 0 (idxTel U np ty).length)] ++
        (VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0).reverse ++
        ((minorTypesRec U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (.bvar 0)
      ((VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange (ty.ctors.length + 1 + (idxTel U np ty).length) np ++
          VExpr.bvarRevRange 0 (idxTel U np ty).length)).liftN
        [VExpr.appN (.const T (VLevel.params' U 1))
          (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
            VExpr.bvarRevRange 0 (idxTel U np ty).length)].length) := by
    simpa [List.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using harg
  have happ := HasType.app hMapp harg'
  exact ⟨_, by
    simpa [List.append_assoc, VExpr.liftTelN_length] using happ⟩

theorem Stage3Env.recConstRec_wf : (recConstRec U T np ty).WF env :=
  S.recTypeRec_isType

theorem Stage3Env.recConst_wf : (recConst U T np ty).WF env :=
  S.recType_isType

/-! ## The iota rules -/

/-- The recursor type is closed, by well-formedness. -/
theorem Stage3Env.recType_closedN : (recType U T np ty).ClosedN 0 := by
  obtain ⟨u, h⟩ := S.recType_isType
  exact VExpr.WF.closedN S.ord ⟨_, h⟩ trivial

theorem Stage3Env.recTypeRec_closedN : (recTypeRec U T np ty).ClosedN 0 := by
  obtain ⟨u, h⟩ := S.recTypeRec_isType
  exact VExpr.WF.closedN S.ord ⟨_, h⟩ trivial

/-- The recursor constant at its own (identity) universe list. -/
theorem Stage3Env.recConst_hasType
    (hrec : env.constants (.str T "rec") = some (recConst U T np ty)) {Γ} :
    env.HasType (U+1) Γ (.const (.str T "rec") (VLevel.params (U+1)))
      (recType U T np ty) := by
  have := HasType.const (Γ := Γ) hrec VLevel.params_wf VLevel.params_length
  rw [show (recConst U T np ty).uvars = U + 1 from rfl,
    show (recConst U T np ty).type = recType U T np ty from rfl] at this
  rwa [recType_levelWF.instL_id] at this

theorem Stage3Env.recConstRec_hasType
    (hrec : env.constants (.str T "rec") = some (recConstRec U T np ty)) {Γ} :
    env.HasType (U+1) Γ (.const (.str T "rec") (VLevel.params (U+1)))
      (recTypeRec U T np ty) := by
  have := HasType.const (Γ := Γ) hrec VLevel.params_wf VLevel.params_length
  rw [show (recConstRec U T np ty).uvars = U + 1 from rfl,
    show (recConstRec U T np ty).type = recTypeRec U T np ty from rfl] at this
  rwa [recTypeRec_levelWF.instL_id] at this

/-- The recursor applied to its parameter, motive, and minor-premise
spine.  The remaining type is the (lifted) index telescope followed by
the major premise. -/
theorem Stage3Env.recBase_hasType
    (hrec : env.constants (.str T "rec") = some (recConst U T np ty))
    (Δ : List VExpr) :
    env.HasType (U+1)
      (Δ ++ ((minorTypes U T np ty ty.ctors).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.appN (.const (.str T "rec") (VLevel.params (U+1)))
        (VExpr.bvarRevRange Δ.length (np + ty.ctors.length + 1)))
      ((VExpr.forallN (VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0)
        (.forallE (VExpr.appN (.const T (VLevel.params' U 1))
          (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
            VExpr.bvarRevRange 0 (idxTel U np ty).length))
          (.app (VExpr.appN (.bvar ((idxTel U np ty).length + ty.ctors.length + 1))
            (VExpr.bvarRevRange 1 (idxTel U np ty).length)) (.bvar 0)))).liftN Δ.length) := by
  have hf : env.HasType (U+1)
      (Δ ++ (paramsTel U np ty ++
        motiveType U T np ty :: minorTypes U T np ty ty.ctors).reverse ++ [])
      (.const (.str T "rec") (VLevel.params (U+1)))
      ((VExpr.forallN (paramsTel U np ty ++
        motiveType U T np ty :: minorTypes U T np ty ty.ctors)
        (VExpr.forallN (VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0)
          (.forallE (VExpr.appN (.const T (VLevel.params' U 1))
            (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
              VExpr.bvarRevRange 0 (idxTel U np ty).length))
            (.app (VExpr.appN (.bvar ((idxTel U np ty).length + ty.ctors.length + 1))
              (VExpr.bvarRevRange 1 (idxTel U np ty).length)) (.bvar 0))))).liftN
        (Δ.length + (paramsTel U np ty ++
          motiveType U T np ty :: minorTypes U T np ty ty.ctors).length)) := by
    rw [show VExpr.forallN (paramsTel U np ty ++
        motiveType U T np ty :: minorTypes U T np ty ty.ctors)
        (VExpr.forallN (VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0)
          (.forallE (VExpr.appN (.const T (VLevel.params' U 1))
            (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
              VExpr.bvarRevRange 0 (idxTel U np ty).length))
            (.app (VExpr.appN (.bvar ((idxTel U np ty).length + ty.ctors.length + 1))
              (VExpr.bvarRevRange 1 (idxTel U np ty).length)) (.bvar 0)))) =
        recType U T np ty from by rw [VExpr.forallN_append]; rfl,
      S.recType_closedN.liftN_eq (Nat.zero_le _)]
    exact S.recConst_hasType hrec
  have hspine := HasType.appN_selfSpine (env := env) (U := U+1) hf
  simp only [recType, List.reverse_append, List.reverse_cons, List.append_nil,
    List.append_assoc, List.singleton_append, List.length_append, List.length_cons,
    List.length_reverse, minorTypes_length] at hspine
  rw [show (paramsTel U np ty).length = np from by
      simp [paramsTel, List.length_map, S.hlen],
    VExpr.bvarRevRange_congr' Δ.length (show
      np + (ty.ctors.length + 1) = np + ty.ctors.length + 1 from by omega)] at hspine
  simpa [List.append_assoc] using hspine

theorem Stage3Env.recBaseRec_hasType
    (hrec : env.constants (.str T "rec") = some (recConstRec U T np ty))
    (Δ : List VExpr) :
    env.HasType (U+1)
      (Δ ++ ((minorTypesRec U T np ty ty.ctors).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.appN (.const (.str T "rec") (VLevel.params (U+1)))
        (VExpr.bvarRevRange Δ.length (np + ty.ctors.length + 1)))
      ((VExpr.forallN (VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0)
        (.forallE (VExpr.appN (.const T (VLevel.params' U 1))
          (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
            VExpr.bvarRevRange 0 (idxTel U np ty).length))
          (.app (VExpr.appN (.bvar ((idxTel U np ty).length + ty.ctors.length + 1))
            (VExpr.bvarRevRange 1 (idxTel U np ty).length)) (.bvar 0)))).liftN Δ.length) := by
  have hf : env.HasType (U+1)
      (Δ ++ (paramsTel U np ty ++
        motiveType U T np ty :: minorTypesRec U T np ty ty.ctors).reverse ++ [])
      (.const (.str T "rec") (VLevel.params (U+1)))
      ((VExpr.forallN (paramsTel U np ty ++
        motiveType U T np ty :: minorTypesRec U T np ty ty.ctors)
        (VExpr.forallN (VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0)
          (.forallE (VExpr.appN (.const T (VLevel.params' U 1))
            (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
              VExpr.bvarRevRange 0 (idxTel U np ty).length))
            (.app (VExpr.appN (.bvar ((idxTel U np ty).length + ty.ctors.length + 1))
              (VExpr.bvarRevRange 1 (idxTel U np ty).length)) (.bvar 0))))).liftN
        (Δ.length + (paramsTel U np ty ++
          motiveType U T np ty :: minorTypesRec U T np ty ty.ctors).length)) := by
    rw [show VExpr.forallN (paramsTel U np ty ++
        motiveType U T np ty :: minorTypesRec U T np ty ty.ctors)
        (VExpr.forallN (VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0)
          (.forallE (VExpr.appN (.const T (VLevel.params' U 1))
            (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
              VExpr.bvarRevRange 0 (idxTel U np ty).length))
            (.app (VExpr.appN (.bvar ((idxTel U np ty).length + ty.ctors.length + 1))
              (VExpr.bvarRevRange 1 (idxTel U np ty).length)) (.bvar 0)))) =
        recTypeRec U T np ty from by rw [VExpr.forallN_append]; rfl,
      S.recTypeRec_closedN.liftN_eq (Nat.zero_le _)]
    exact S.recConstRec_hasType hrec
  have hspine := HasType.appN_selfSpine (env := env) (U := U+1) hf
  simp only [recTypeRec, List.reverse_append, List.reverse_cons, List.append_nil,
    List.append_assoc, List.singleton_append, List.length_append, List.length_cons,
    List.length_reverse, minorTypesRec_length] at hspine
  rw [show (paramsTel U np ty).length = np from by
      simp [paramsTel, List.length_map, S.hlen],
    VExpr.bvarRevRange_congr' Δ.length (show
      np + (ty.ctors.length + 1) = np + ty.ctors.length + 1 from by omega)] at hspine
  simpa [List.append_assoc] using hspine

/-- Apply the generated recursor to an index spine and its major premise.
This is shared by constructor-headed rule left sides and by the recursive
calls appearing in minor-premise right sides. -/
theorem Stage3Env.recApp_hasType
    (hrec : env.constants (.str T "rec") = some (recConst U T np ty))
    (Δ : List VExpr) {idxs : List VExpr} {a : VExpr}
    (hidx : env.SpineWF (U+1)
      (Δ ++ ((minorTypes U T np ty ty.ctors).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.forallN
        (VExpr.liftTelN (Δ.length + ty.ctors.length + 1) (idxTel U np ty) 0)
        (.sort (l.inst (VLevel.params' U 1))))
      idxs (.sort (l.inst (VLevel.params' U 1))))
    (hlen : idxs.length = (idxTel U np ty).length)
    (ha : env.HasType (U+1)
      (Δ ++ ((minorTypes U T np ty ty.ctors).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse))) a
      (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange (Δ.length + ty.ctors.length + 1) np ++ idxs))) :
    env.HasType (U+1)
      (Δ ++ ((minorTypes U T np ty ty.ctors).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.appN
        (VExpr.appN (.const (.str T "rec") (VLevel.params (U+1)))
          (VExpr.bvarRevRange Δ.length (np + ty.ctors.length + 1)))
        (idxs ++ [a]))
      (VExpr.appN (.bvar (Δ.length + ty.ctors.length)) (idxs ++ [a])) := by
  have hb := S.recBase_hasType hrec Δ
  rw [VExpr.liftN_forallN, VExpr.liftTelN_liftTelN,
    liftTelN_congr _ _ (show ty.ctors.length + 1 + Δ.length =
      Δ.length + ty.ctors.length + 1 from by omega)] at hb
  have hcod :
      (VExpr.forallE (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
          VExpr.bvarRevRange 0 (idxTel U np ty).length))
        (.app (VExpr.appN (.bvar ((idxTel U np ty).length + ty.ctors.length + 1))
          (VExpr.bvarRevRange 1 (idxTel U np ty).length)) (.bvar 0))).liftN Δ.length
          (0 + (VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0).length) =
      VExpr.forallE (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange ((idxTel U np ty).length + Δ.length +
            ty.ctors.length + 1) np ++
          VExpr.bvarRevRange 0 (idxTel U np ty).length))
        (.app (VExpr.appN (.bvar ((idxTel U np ty).length + Δ.length +
            ty.ctors.length + 1))
          (VExpr.bvarRevRange 1 (idxTel U np ty).length)) (.bvar 0)) := by
    rw [VExpr.liftTelN_length, Nat.zero_add]
    show VExpr.forallE _ _ = VExpr.forallE _ _
    congr 1
    · rw [VExpr.liftN_appN, List.map_append,
        bvarRevRange_liftN_ge _ _ _ _ (by omega),
        VExpr.bvarRevRange_liftN_high _ _ _ _ (by omega),
        VExpr.bvarRevRange_congr np (show Δ.length +
          ((idxTel U np ty).length + ty.ctors.length + 1) =
          (idxTel U np ty).length + Δ.length + ty.ctors.length + 1 from by omega)]
      rfl
    · show VExpr.app _ _ = VExpr.app _ _
      congr 1
      · rw [VExpr.liftN_appN,
          VExpr.bvarRevRange_liftN_high _ _ _ _ (by omega)]
        show VExpr.appN (.bvar (liftVar Δ.length
          ((idxTel U np ty).length + ty.ctors.length + 1)
          ((idxTel U np ty).length + 1))) _ = _
        rw [liftVar_le (by omega), show Δ.length +
          ((idxTel U np ty).length + ty.ctors.length + 1) =
          (idxTel U np ty).length + Δ.length + ty.ctors.length + 1 from by omega]
  rw [hcod] at hb
  have hshape := hidx.retarget (by simpa only [VExpr.liftTelN_length] using hlen)
    (.forallE (VExpr.appN (.const T (VLevel.params' U 1))
      (VExpr.bvarRevRange ((idxTel U np ty).length + Δ.length +
          ty.ctors.length + 1) np ++
        VExpr.bvarRevRange 0 (idxTel U np ty).length))
      (.sort (.param 0)))
  rw [VExpr.instRev_forallE_sort, VExpr.instRev_appN,
    VExpr.instRev_closedN _ (C := .const T (VLevel.params' U 1)) trivial,
    List.map_append,
    VExpr.map_instRev_bvarRevRange_ge _ _ _ (by rw [hlen]; omega),
    show (idxTel U np ty).length + Δ.length + ty.ctors.length + 1 - idxs.length =
      Δ.length + ty.ctors.length + 1 from by rw [hlen]; omega,
    VExpr.bvarRevRange_congr' 0 hlen.symm,
    VExpr.map_instRev_bvarRevRange] at hshape
  rw [hlen] at hshape
  have hfull := hshape.snoc ha
  simp only [VExpr.inst] at hfull
  change env.SpineWF (U+1) _
    (VExpr.forallN
      (VExpr.liftTelN (Δ.length + ty.ctors.length + 1) (idxTel U np ty) 0)
      (VExpr.forallN [VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange ((idxTel U np ty).length + Δ.length +
            ty.ctors.length + 1) np ++
          VExpr.bvarRevRange 0 (idxTel U np ty).length)]
        (.sort (.param 0))))
    (idxs ++ [a]) (.sort (.param 0)) at hfull
  rw [← VExpr.forallN_append] at hfull
  have hfullLen : (idxs ++ [a]).length =
      (VExpr.liftTelN (Δ.length + ty.ctors.length + 1) (idxTel U np ty) 0 ++
        [VExpr.appN (.const T (VLevel.params' U 1))
          (VExpr.bvarRevRange ((idxTel U np ty).length + Δ.length +
              ty.ctors.length + 1) np ++
            VExpr.bvarRevRange 0 (idxTel U np ty).length)]).length := by
    simp only [List.length_append, List.length_singleton, VExpr.liftTelN_length, hlen]
  have hactual := hfull.retarget hfullLen
    (VExpr.app
      (VExpr.appN (.bvar ((idxTel U np ty).length + Δ.length +
          ty.ctors.length + 1))
        (VExpr.bvarRevRange 1 (idxTel U np ty).length))
      (.bvar 0))
  rw [VExpr.forallN_append] at hactual
  have happ := hactual.hasType_appN hb
  rw [show VExpr.app
      (VExpr.appN (.bvar ((idxTel U np ty).length + Δ.length +
          ty.ctors.length + 1))
        (VExpr.bvarRevRange 1 (idxTel U np ty).length))
      (.bvar 0) =
      VExpr.appN (.bvar ((idxTel U np ty).length + Δ.length +
        ty.ctors.length + 1)) (VExpr.bvarRevRange 0 ((idxTel U np ty).length + 1)) from by
        rw [VExpr.bvarRevRange_congr' 0 (show (idxTel U np ty).length + 1 =
          1 + (idxTel U np ty).length from by omega),
          ← VExpr.bvarRevRange_append (idxTel U np ty).length 1]
        simpa [VExpr.bvarRevRange, VExpr.appN] using (VExpr.appN_append
          (.bvar ((idxTel U np ty).length + Δ.length + ty.ctors.length + 1))
          (VExpr.bvarRevRange 1 (idxTel U np ty).length) [VExpr.bvar 0]).symm,
    VExpr.instRev_appN,
    VExpr.instRev_bvar_ge _ (by
      simp only [List.length_append, List.length_singleton]
      rw [hlen]
      omega),
    VExpr.bvarRevRange_congr' 0 (show (idxTel U np ty).length + 1 =
      (idxs ++ [a]).length from by simp [hlen]),
    VExpr.map_instRev_bvarRevRange] at happ
  rw [show (idxTel U np ty).length + Δ.length + ty.ctors.length + 1 -
      (idxs ++ [a]).length = Δ.length + ty.ctors.length from by
    simp only [List.length_append, List.length_singleton]
    rw [hlen]
    omega] at happ
  simpa [List.length_append, hlen] using happ

theorem Stage3Env.recAppRec_hasType
    (hrec : env.constants (.str T "rec") = some (recConstRec U T np ty))
    (Δ : List VExpr) {idxs : List VExpr} {a : VExpr}
    (hidx : env.SpineWF (U+1)
      (Δ ++ ((minorTypesRec U T np ty ty.ctors).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.forallN
        (VExpr.liftTelN (Δ.length + ty.ctors.length + 1) (idxTel U np ty) 0)
        (.sort (l.inst (VLevel.params' U 1))))
      idxs (.sort (l.inst (VLevel.params' U 1))))
    (hlen : idxs.length = (idxTel U np ty).length)
    (ha : env.HasType (U+1)
      (Δ ++ ((minorTypesRec U T np ty ty.ctors).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse))) a
      (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange (Δ.length + ty.ctors.length + 1) np ++ idxs))) :
    env.HasType (U+1)
      (Δ ++ ((minorTypesRec U T np ty ty.ctors).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.appN
        (VExpr.appN (.const (.str T "rec") (VLevel.params (U+1)))
          (VExpr.bvarRevRange Δ.length (np + ty.ctors.length + 1)))
        (idxs ++ [a]))
      (VExpr.appN (.bvar (Δ.length + ty.ctors.length)) (idxs ++ [a])) := by
  have hb := S.recBaseRec_hasType hrec Δ
  rw [VExpr.liftN_forallN, VExpr.liftTelN_liftTelN,
    liftTelN_congr _ _ (show ty.ctors.length + 1 + Δ.length =
      Δ.length + ty.ctors.length + 1 from by omega)] at hb
  have hcod :
      (VExpr.forallE (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange ((idxTel U np ty).length + ty.ctors.length + 1) np ++
          VExpr.bvarRevRange 0 (idxTel U np ty).length))
        (.app (VExpr.appN (.bvar ((idxTel U np ty).length + ty.ctors.length + 1))
          (VExpr.bvarRevRange 1 (idxTel U np ty).length)) (.bvar 0))).liftN Δ.length
          (0 + (VExpr.liftTelN (ty.ctors.length + 1) (idxTel U np ty) 0).length) =
      VExpr.forallE (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange ((idxTel U np ty).length + Δ.length +
            ty.ctors.length + 1) np ++
          VExpr.bvarRevRange 0 (idxTel U np ty).length))
        (.app (VExpr.appN (.bvar ((idxTel U np ty).length + Δ.length +
            ty.ctors.length + 1))
          (VExpr.bvarRevRange 1 (idxTel U np ty).length)) (.bvar 0)) := by
    rw [VExpr.liftTelN_length, Nat.zero_add]
    show VExpr.forallE _ _ = VExpr.forallE _ _
    congr 1
    · rw [VExpr.liftN_appN, List.map_append,
        bvarRevRange_liftN_ge _ _ _ _ (by omega),
        VExpr.bvarRevRange_liftN_high _ _ _ _ (by omega),
        VExpr.bvarRevRange_congr np (show Δ.length +
          ((idxTel U np ty).length + ty.ctors.length + 1) =
          (idxTel U np ty).length + Δ.length + ty.ctors.length + 1 from by omega)]
      rfl
    · show VExpr.app _ _ = VExpr.app _ _
      congr 1
      · rw [VExpr.liftN_appN,
          VExpr.bvarRevRange_liftN_high _ _ _ _ (by omega)]
        show VExpr.appN (.bvar (liftVar Δ.length
          ((idxTel U np ty).length + ty.ctors.length + 1)
          ((idxTel U np ty).length + 1))) _ = _
        rw [liftVar_le (by omega), show Δ.length +
          ((idxTel U np ty).length + ty.ctors.length + 1) =
          (idxTel U np ty).length + Δ.length + ty.ctors.length + 1 from by omega]
  rw [hcod] at hb
  have hshape := hidx.retarget (by simpa only [VExpr.liftTelN_length] using hlen)
    (.forallE (VExpr.appN (.const T (VLevel.params' U 1))
      (VExpr.bvarRevRange ((idxTel U np ty).length + Δ.length +
          ty.ctors.length + 1) np ++
        VExpr.bvarRevRange 0 (idxTel U np ty).length))
      (.sort (.param 0)))
  rw [VExpr.instRev_forallE_sort, VExpr.instRev_appN,
    VExpr.instRev_closedN _ (C := .const T (VLevel.params' U 1)) trivial,
    List.map_append,
    VExpr.map_instRev_bvarRevRange_ge _ _ _ (by rw [hlen]; omega),
    show (idxTel U np ty).length + Δ.length + ty.ctors.length + 1 - idxs.length =
      Δ.length + ty.ctors.length + 1 from by rw [hlen]; omega,
    VExpr.bvarRevRange_congr' 0 hlen.symm,
    VExpr.map_instRev_bvarRevRange] at hshape
  rw [hlen] at hshape
  have hfull := hshape.snoc ha
  simp only [VExpr.inst] at hfull
  change env.SpineWF (U+1) _
    (VExpr.forallN
      (VExpr.liftTelN (Δ.length + ty.ctors.length + 1) (idxTel U np ty) 0)
      (VExpr.forallN [VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange ((idxTel U np ty).length + Δ.length +
            ty.ctors.length + 1) np ++
          VExpr.bvarRevRange 0 (idxTel U np ty).length)]
        (.sort (.param 0))))
    (idxs ++ [a]) (.sort (.param 0)) at hfull
  rw [← VExpr.forallN_append] at hfull
  have hfullLen : (idxs ++ [a]).length =
      (VExpr.liftTelN (Δ.length + ty.ctors.length + 1) (idxTel U np ty) 0 ++
        [VExpr.appN (.const T (VLevel.params' U 1))
          (VExpr.bvarRevRange ((idxTel U np ty).length + Δ.length +
              ty.ctors.length + 1) np ++
            VExpr.bvarRevRange 0 (idxTel U np ty).length)]).length := by
    simp only [List.length_append, List.length_singleton, VExpr.liftTelN_length, hlen]
  have hactual := hfull.retarget hfullLen
    (VExpr.app
      (VExpr.appN (.bvar ((idxTel U np ty).length + Δ.length +
          ty.ctors.length + 1))
        (VExpr.bvarRevRange 1 (idxTel U np ty).length))
      (.bvar 0))
  rw [VExpr.forallN_append] at hactual
  have happ := hactual.hasType_appN hb
  rw [show VExpr.app
      (VExpr.appN (.bvar ((idxTel U np ty).length + Δ.length +
          ty.ctors.length + 1))
        (VExpr.bvarRevRange 1 (idxTel U np ty).length))
      (.bvar 0) =
      VExpr.appN (.bvar ((idxTel U np ty).length + Δ.length +
        ty.ctors.length + 1)) (VExpr.bvarRevRange 0 ((idxTel U np ty).length + 1)) from by
        rw [VExpr.bvarRevRange_congr' 0 (show (idxTel U np ty).length + 1 =
          1 + (idxTel U np ty).length from by omega),
          ← VExpr.bvarRevRange_append (idxTel U np ty).length 1]
        simpa [VExpr.bvarRevRange, VExpr.appN] using (VExpr.appN_append
          (.bvar ((idxTel U np ty).length + Δ.length + ty.ctors.length + 1))
          (VExpr.bvarRevRange 1 (idxTel U np ty).length) [VExpr.bvar 0]).symm,
    VExpr.instRev_appN,
    VExpr.instRev_bvar_ge _ (by
      simp only [List.length_append, List.length_singleton]
      rw [hlen]
      omega),
    VExpr.bvarRevRange_congr' 0 (show (idxTel U np ty).length + 1 =
      (idxs ++ [a]).length from by simp [hlen]),
    VExpr.map_instRev_bvarRevRange] at happ
  rw [show (idxTel U np ty).length + Δ.length + ty.ctors.length + 1 -
      (idxs ++ [a]).length = Δ.length + ty.ctors.length from by
    simp only [List.length_append, List.length_singleton]
    rw [hlen]
    omega] at happ
  simpa [List.length_append, hlen] using happ

/-- The motive variable applied to a well-typed index spine and major
premise has the recursor's elimination sort. -/
theorem Stage3Env.motiveApp_hasType
    (Δ : List VExpr) {idxs : List VExpr} {a : VExpr}
    (hidx : env.SpineWF (U+1)
      (Δ ++ ((minorTypes U T np ty ty.ctors).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.forallN
        (VExpr.liftTelN (Δ.length + ty.ctors.length + 1) (idxTel U np ty) 0)
        (.sort (l.inst (VLevel.params' U 1))))
      idxs (.sort (l.inst (VLevel.params' U 1))))
    (hlen : idxs.length = (idxTel U np ty).length)
    (ha : env.HasType (U+1)
      (Δ ++ ((minorTypes U T np ty ty.ctors).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse))) a
      (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange (Δ.length + ty.ctors.length + 1) np ++ idxs))) :
    env.HasType (U+1)
      (Δ ++ ((minorTypes U T np ty ty.ctors).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.appN (.bvar (Δ.length + ty.ctors.length)) (idxs ++ [a]))
      (.sort (.param 0)) := by
  have hM := getElem?_rstack3 Δ (minorTypes U T np ty ty.ctors).reverse
    (motiveType U T np ty) (paramsTel U np ty).reverse
    (i := Δ.length + ty.ctors.length)
    (by simp only [List.length_reverse, minorTypes_length])
  have hmlu := Lookup.of_getElem? hM
  rw [motiveType_liftN] at hmlu
  have hshape := hidx.retarget (by simpa only [VExpr.liftTelN_length] using hlen)
    (.forallE (VExpr.appN (.const T (VLevel.params' U 1))
      (VExpr.bvarRevRange (Δ.length + ty.ctors.length + 1 +
          (idxTel U np ty).length) np ++
        VExpr.bvarRevRange 0 (idxTel U np ty).length))
      (.sort (.param 0)))
  rw [VExpr.instRev_forallE_sort, VExpr.instRev_appN,
    VExpr.instRev_closedN _ (C := .const T (VLevel.params' U 1)) trivial,
    List.map_append,
    VExpr.map_instRev_bvarRevRange_ge _ _ _ (by rw [hlen]; omega),
    show Δ.length + ty.ctors.length + 1 + (idxTel U np ty).length - idxs.length =
      Δ.length + ty.ctors.length + 1 from by rw [hlen]; omega,
    VExpr.bvarRevRange_congr' 0 hlen.symm,
    VExpr.map_instRev_bvarRevRange] at hshape
  rw [hlen] at hshape
  have hfull := hshape.snoc ha
  simp only [VExpr.inst] at hfull
  exact hfull.hasType_appN (.bvar hmlu)

theorem Stage3Env.motiveAppRec_hasType
    (Δ : List VExpr) {idxs : List VExpr} {a : VExpr}
    (hidx : env.SpineWF (U+1)
      (Δ ++ ((minorTypesRec U T np ty ty.ctors).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.forallN
        (VExpr.liftTelN (Δ.length + ty.ctors.length + 1) (idxTel U np ty) 0)
        (.sort (l.inst (VLevel.params' U 1))))
      idxs (.sort (l.inst (VLevel.params' U 1))))
    (hlen : idxs.length = (idxTel U np ty).length)
    (ha : env.HasType (U+1)
      (Δ ++ ((minorTypesRec U T np ty ty.ctors).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse))) a
      (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange (Δ.length + ty.ctors.length + 1) np ++ idxs))) :
    env.HasType (U+1)
      (Δ ++ ((minorTypesRec U T np ty ty.ctors).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.appN (.bvar (Δ.length + ty.ctors.length)) (idxs ++ [a]))
      (.sort (.param 0)) := by
  have hM := getElem?_rstack3 Δ (minorTypesRec U T np ty ty.ctors).reverse
    (motiveType U T np ty) (paramsTel U np ty).reverse
    (i := Δ.length + ty.ctors.length)
    (by simp only [List.length_reverse, minorTypesRec_length])
  exact motiveVarApp_hasType (env := env) (U := U) (T := T) (np := np)
    (l := l) (ty := ty) (.bvar (Lookup.of_getElem? hM)) hidx hlen ha

/-- The constructor-headed major of an iota rule, in the rule's binder
context (parameter spine past the motive, minors and fields). -/
theorem Stage3Env.ctorAppRule_hasType {c : VConstVal} (hc : c ∈ ty.ctors) :
    env.HasType (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypes U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.appN (.const c.name (VLevel.params' U 1))
        (VExpr.bvarRevRange ((ctorFieldsR U np c).length + ty.ctors.length + 1) np ++
          VExpr.bvarRevRange 0 (ctorFieldsR U np c).length))
      (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange ((ctorFieldsR U np c).length + ty.ctors.length + 1) np ++
          (ctorIdxs U np c).map fun e =>
            e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length)) := by
  have W := Ctx.LiftN.consTel (n := ty.ctors.length)
    (VExpr.liftTelN 1 (ctorFieldsR U np c) 0)
    (Ctx.LiftN.zero (n := ty.ctors.length)
      (Γ := motiveType U T np ty :: (paramsTel U np ty).reverse)
      (minorTypes U T np ty ty.ctors).reverse
      (h := by simp [minorTypes_length]))
  have h := (S.ctorAppMin_hasType hc []).weakN S.ord W
  have hlen : (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).length =
      (ctorFieldsR U np c).length := VExpr.liftTelN_length ..
  rw [hlen] at h
  simp only [List.nil_append, List.length_nil, Nat.zero_add, VExpr.liftN_appN,
    VExpr.liftN, List.map_append, List.map_map] at h
  rw [VExpr.liftTelN_liftTelN,
    bvarRevRange_liftN_ge _ _ _ _ (by omega),
    VExpr.bvarRevRange_liftN_high _ _ _ _ (by omega)] at h
  simp only [Function.comp_def, VExpr.liftN_zero, Nat.add_zero] at h
  have hmap : (ctorIdxs U np c).map (fun e =>
      (e.liftN 1 (ctorFieldsR U np c).length).liftN
        ty.ctors.length (ctorFieldsR U np c).length) =
      (ctorIdxs U np c).map (fun e =>
        e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length) := by
    apply List.map_congr_left
    intro e _
    rw [VExpr.liftN'_liftN_hi]
    congr 1
    omega
  rw [hmap] at h
  simpa [List.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

theorem Stage3Env.ctorAppRuleRec_hasType {c : VConstVal} (hc : c ∈ ty.ctors) :
    env.HasType (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypesRec U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.appN (.const c.name (VLevel.params' U 1))
        (VExpr.bvarRevRange ((ctorFieldsR U np c).length + ty.ctors.length + 1) np ++
          VExpr.bvarRevRange 0 (ctorFieldsR U np c).length))
      (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange ((ctorFieldsR U np c).length + ty.ctors.length + 1) np ++
          (ctorIdxs U np c).map fun e =>
            e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length)) := by
  have W := Ctx.LiftN.consTel (n := ty.ctors.length)
    (VExpr.liftTelN 1 (ctorFieldsR U np c) 0)
    (Ctx.LiftN.zero (n := ty.ctors.length)
      (Γ := motiveType U T np ty :: (paramsTel U np ty).reverse)
      (minorTypesRec U T np ty ty.ctors).reverse
      (h := by simp [minorTypesRec_length]))
  have h := (S.ctorAppMin_hasType hc []).weakN S.ord W
  have hlen : (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).length =
      (ctorFieldsR U np c).length := VExpr.liftTelN_length ..
  rw [hlen] at h
  simp only [List.nil_append, List.length_nil, Nat.zero_add, VExpr.liftN_appN,
    VExpr.liftN, List.map_append, List.map_map] at h
  rw [VExpr.liftTelN_liftTelN,
    bvarRevRange_liftN_ge _ _ _ _ (by omega),
    VExpr.bvarRevRange_liftN_high _ _ _ _ (by omega)] at h
  simp only [Function.comp_def, VExpr.liftN_zero, Nat.add_zero] at h
  have hmap : (ctorIdxs U np c).map (fun e =>
      (e.liftN 1 (ctorFieldsR U np c).length).liftN
        ty.ctors.length (ctorFieldsR U np c).length) =
      (ctorIdxs U np c).map (fun e =>
        e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length) := by
    apply List.map_congr_left
    intro e _
    rw [VExpr.liftN'_liftN_hi]
    congr 1
    omega
  rw [hmap] at h
  simpa [List.append_assoc, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

theorem Stage3Env.ruleBinders_onTel {c : VConstVal} (hc : c ∈ ty.ctors) :
    OnTel env (U+1) []
      (paramsTel U np ty ++ motiveType U T np ty :: minorTypes U T np ty ty.ctors ++
        VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0) := by
  have hP : OnTel env (U+1) [] (paramsTel U np ty) := by
    have := S.hparams.of_append.1.instL (U' := U+1) VLevel.params'_one_wf
    simpa [paramsTel] using this
  have hF : OnTel env (U+1)
      ((minorTypes U T np ty ty.ctors).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse))
      (VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0) := by
    have h0 := S.fieldsWF_onTel _ [] 0 rfl (by simpa using S.hfields c hc)
    have h1 := h0.weakN S.ord
      (.zero ((minorTypes U T np ty ty.ctors).reverse ++ [motiveType U T np ty]))
    rw [liftTelN_congr _ _ (show ((minorTypes U T np ty ty.ctors).reverse ++
        [motiveType U T np ty]).length = ty.ctors.length + 1 from by
      simp only [List.length_append, List.length_reverse, minorTypes_length,
        List.length_singleton])] at h1
    simpa [List.map_reverse, paramsTel, List.append_assoc] using h1
  refine OnTel.append (OnTel.append hP ⟨?_, ?_⟩) ?_
  · simpa only [List.append_nil] using S.motive_isType
  · have := S.minorTypes_onTel ty.ctors (fun _ h => h) [] 0 rfl
    simpa only [List.nil_append, List.append_nil] using this
  · simpa only [List.append_nil, List.append_assoc, List.reverse_append,
      List.reverse_cons, List.singleton_append] using hF

theorem Stage3Env.ruleBindersRec_onTel {c : VConstVal} (hc : c ∈ ty.ctors) :
    OnTel env (U+1) []
      (paramsTel U np ty ++ motiveType U T np ty :: minorTypesRec U T np ty ty.ctors ++
        VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0) := by
  have hP : OnTel env (U+1) [] (paramsTel U np ty) := by
    have := S.hparams.of_append.1.instL (U' := U+1) VLevel.params'_one_wf
    simpa [paramsTel] using this
  have hF : OnTel env (U+1)
      ((minorTypesRec U T np ty ty.ctors).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse))
      (VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0) := by
    have h0 := S.fieldsWF_onTel _ [] 0 rfl (by simpa using S.hfields c hc)
    have h1 := h0.weakN S.ord
      (.zero ((minorTypesRec U T np ty ty.ctors).reverse ++ [motiveType U T np ty]))
    rw [liftTelN_congr _ _ (show ((minorTypesRec U T np ty ty.ctors).reverse ++
        [motiveType U T np ty]).length = ty.ctors.length + 1 from by
      simp only [List.length_append, List.length_reverse, minorTypesRec_length,
        List.length_singleton])] at h1
    simpa [List.map_reverse, paramsTel, List.append_assoc] using h1
  refine OnTel.append (OnTel.append hP ⟨?_, ?_⟩) ?_
  · simpa only [List.append_nil] using S.motive_isType
  · have := S.minorTypesRec_onTel ty.ctors (fun _ h => h) [] 0 rfl
    simpa only [List.nil_append, List.append_nil] using this
  · simpa only [List.append_nil, List.append_assoc, List.reverse_append,
      List.reverse_cons, List.singleton_append] using hF

theorem Stage3Env.ruleType_isType {i : Nat} {c : VConstVal}
    (hci : ty.ctors[i]? = some c) :
    env.IsType (U+1) [] ((rule U T np ty i c).type) := by
  have hc := List.mem_of_getElem? hci
  show env.IsType (U+1) [] (VExpr.forallN
    (paramsTel U np ty ++ motiveType U T np ty :: minorTypes U T np ty ty.ctors ++
      VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0)
    (VExpr.appN (.bvar (ty.ctors.length + (ctorFieldsR U np c).length))
      (((ctorIdxs U np c).map fun e =>
          e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length) ++
        [VExpr.appN (.const c.name (VLevel.params' U 1))
          (VExpr.bvarRevRange ((ctorFieldsR U np c).length + ty.ctors.length + 1) np ++
            VExpr.bvarRevRange 0 (ctorFieldsR U np c).length)])))
  refine IsType.forallN (S.ruleBinders_onTel hc) ?_
  simp only [List.reverse_append, List.reverse_cons, List.append_nil, List.append_assoc,
    List.singleton_append]
  have hSp0 := S.result_transport hc
    ((minorTypes U T np ty ty.ctors).reverse ++ [motiveType U T np ty])
    (g := ty.ctors.length + 1) (by simp [minorTypes_length]) [] (d := 0) rfl
  have hSp : env.SpineWF (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypes U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.forallN (VExpr.liftTelN
        ((ctorFieldsR U np c).length + ty.ctors.length + 1)
        (idxTel U np ty) 0) (.sort (l.inst (VLevel.params' U 1))))
      ((ctorIdxs U np c).map fun e =>
        e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length)
      (.sort (l.inst (VLevel.params' U 1))) := by
    simpa [List.append_assoc, Nat.add_assoc] using hSp0
  have hidxLen : ((ctorIdxs U np c).map fun e =>
      e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length).length =
      (idxTel U np ty).length := by
    simp only [List.length_map, ctorIdxs_length, idxTel_length]
    exact (stage3Ctor_eq (S.hs3 c hc)).2.1
  have hctor := S.ctorAppRule_hasType hc
  have hSp' : env.SpineWF (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypes U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.forallN (VExpr.liftTelN
        ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse.length +
          ty.ctors.length + 1) (idxTel U np ty) 0)
        (.sort (l.inst (VLevel.params' U 1))))
      ((ctorIdxs U np c).map fun e =>
        e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length)
      (.sort (l.inst (VLevel.params' U 1))) := by
    simpa only [List.length_reverse, VExpr.liftTelN_length] using hSp
  have hctor' : env.HasType (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypes U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.appN (.const c.name (VLevel.params' U 1))
        (VExpr.bvarRevRange ((ctorFieldsR U np c).length + ty.ctors.length + 1) np ++
          VExpr.bvarRevRange 0 (ctorFieldsR U np c).length))
      (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange
          ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse.length +
            ty.ctors.length + 1) np ++
          (ctorIdxs U np c).map fun e =>
            e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length)) := by
    simpa only [List.length_reverse, VExpr.liftTelN_length] using hctor
  refine ⟨.param 0, ?_⟩
  have hm := S.motiveApp_hasType
    (VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse
    hSp' hidxLen hctor'
  rw [List.length_reverse, VExpr.liftTelN_length,
    show (ctorFieldsR U np c).length + ty.ctors.length =
      ty.ctors.length + (ctorFieldsR U np c).length from by omega,
    show ty.ctors.length + (ctorFieldsR U np c).length + 1 =
      (ctorFieldsR U np c).length + ty.ctors.length + 1 from by omega] at hm
  exact hm

theorem Stage3Env.ruleTypeRec_isType {i : Nat} {c : VConstVal}
    (hci : ty.ctors[i]? = some c) :
    env.IsType (U+1) [] ((ruleRec U T np ty i c).type) := by
  have hc := List.mem_of_getElem? hci
  show env.IsType (U+1) [] (VExpr.forallN
    (paramsTel U np ty ++ motiveType U T np ty :: minorTypesRec U T np ty ty.ctors ++
      VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0)
    (VExpr.appN (.bvar (ty.ctors.length + (ctorFieldsR U np c).length))
      (((ctorIdxs U np c).map fun e =>
          e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length) ++
        [VExpr.appN (.const c.name (VLevel.params' U 1))
          (VExpr.bvarRevRange ((ctorFieldsR U np c).length + ty.ctors.length + 1) np ++
            VExpr.bvarRevRange 0 (ctorFieldsR U np c).length)])))
  refine IsType.forallN (S.ruleBindersRec_onTel hc) ?_
  simp only [List.reverse_append, List.reverse_cons, List.append_nil, List.append_assoc,
    List.singleton_append]
  have hSp0 := S.result_transport hc
    ((minorTypesRec U T np ty ty.ctors).reverse ++ [motiveType U T np ty])
    (g := ty.ctors.length + 1) (by simp [minorTypesRec_length]) [] (d := 0) rfl
  have hSp : env.SpineWF (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypesRec U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.forallN (VExpr.liftTelN
        ((ctorFieldsR U np c).length + ty.ctors.length + 1)
        (idxTel U np ty) 0) (.sort (l.inst (VLevel.params' U 1))))
      ((ctorIdxs U np c).map fun e =>
        e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length)
      (.sort (l.inst (VLevel.params' U 1))) := by
    simpa [List.append_assoc, Nat.add_assoc] using hSp0
  have hidxLen : ((ctorIdxs U np c).map fun e =>
      e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length).length =
      (idxTel U np ty).length := by
    simp only [List.length_map, ctorIdxs_length, idxTel_length]
    exact (stage3Ctor_eq (S.hs3 c hc)).2.1
  have hctor := S.ctorAppRuleRec_hasType hc
  have hSp' : env.SpineWF (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypesRec U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.forallN (VExpr.liftTelN
        ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse.length +
          ty.ctors.length + 1) (idxTel U np ty) 0)
        (.sort (l.inst (VLevel.params' U 1))))
      ((ctorIdxs U np c).map fun e =>
        e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length)
      (.sort (l.inst (VLevel.params' U 1))) := by
    simpa only [List.length_reverse, VExpr.liftTelN_length] using hSp
  have hctor' : env.HasType (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypesRec U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.appN (.const c.name (VLevel.params' U 1))
        (VExpr.bvarRevRange ((ctorFieldsR U np c).length + ty.ctors.length + 1) np ++
          VExpr.bvarRevRange 0 (ctorFieldsR U np c).length))
      (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange
          ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse.length +
            ty.ctors.length + 1) np ++
          (ctorIdxs U np c).map fun e =>
            e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length)) := by
    simpa only [List.length_reverse, VExpr.liftTelN_length] using hctor
  refine ⟨.param 0, ?_⟩
  have hm := S.motiveAppRec_hasType
    (VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse
    hSp' hidxLen hctor'
  rw [List.length_reverse, VExpr.liftTelN_length,
    show (ctorFieldsR U np c).length + ty.ctors.length =
      ty.ctors.length + (ctorFieldsR U np c).length from by omega,
    show ty.ctors.length + (ctorFieldsR U np c).length + 1 =
      (ctorFieldsR U np c).length + ty.ctors.length + 1 from by omega] at hm
  exact hm

/-- A recursive field gives a well-typed recursive call in the full iota
rule context, carrying that field's own index arguments. -/
theorem Stage3Env.recCallRule_hasType {c : VConstVal} (hc : c ∈ ty.ctors)
    (hrec : env.constants (.str T "rec") = some (recConst U T np ty))
    {q : Nat × List VExpr}
    (hq : q ∈ recPairsR U T np (idxTel U np ty).length c) :
    env.HasType (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypes U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.appN
        (VExpr.appN (.const (.str T "rec") (VLevel.params (U+1)))
          (VExpr.bvarRevRange (ctorFieldsR U np c).length
            (np + ty.ctors.length + 1)))
        ((q.2.map fun e =>
          (e.liftN (ty.ctors.length + 1) q.1).liftN
            ((ctorFieldsR U np c).length - q.1)) ++
          [.bvar ((ctorFieldsR U np c).length - 1 - q.1)]))
      (VExpr.appN (.bvar (ty.ctors.length + (ctorFieldsR U np c).length))
        ((q.2.map fun e =>
          (e.liftN (ty.ctors.length + 1) q.1).liftN
            ((ctorFieldsR U np c).length - q.1)) ++
          [.bvar ((ctorFieldsR U np c).length - 1 - q.1)])) := by
  obtain ⟨B, hBj, hrecB0, hidx⟩ := recPairsR_mem hq
  have hrecB : isRecField U T np
      (ctorFields (VExpr.dropN np ty.type)).length q.1 B = true := by
    rwa [← idxTel_length (U := U) (ty := ty)]
  have hjm : q.1 < (ctorFieldsR U np c).length := by
    simpa [ctorFieldsR_length] using recPairsR_lt _ hq
  have hml2 : (VExpr.liftTelN (ty.ctors.length + 1)
      (ctorFieldsR U np c) 0).length = (ctorFieldsR U np c).length :=
    VExpr.liftTelN_length ..
  have hSp0 := S.spine_transport hc hBj hrecB
    ((minorTypes U T np ty ty.ctors).reverse ++ [motiveType U T np ty])
    (g := ty.ctors.length + 1) (by simp [minorTypes_length])
    ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).drop q.1).reverse
    (d := (ctorFieldsR U np c).length - q.1) (by
      simp only [List.length_reverse, List.length_drop, hml2])
  rw [show
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).drop q.1).reverse ++
          ((VExpr.liftTelN (ty.ctors.length + 1)
            ((ctorFieldsR U np c).take q.1) 0).reverse ++
            (((minorTypes U T np ty ty.ctors).reverse ++ [motiveType U T np ty]) ++
              (paramsTel U np ty).reverse)) =
        (VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
          ((minorTypes U T np ty ty.ctors).reverse ++
            (motiveType U T np ty :: (paramsTel U np ty).reverse)) from by
      rw [← VExpr.liftTelN_take, List.append_assoc,
        ← List.append_assoc
          (((VExpr.liftTelN (ty.ctors.length + 1)
            (ctorFieldsR U np c) 0).drop q.1).reverse),
        ← List.reverse_append, List.take_append_drop, List.singleton_append,
        ← List.append_assoc],
    liftTelN_congr _ _ (show q.1 + (ty.ctors.length + 1) +
        ((ctorFieldsR U np c).length - q.1) =
      (ctorFieldsR U np c).length + ty.ctors.length + 1 from by omega),
    ← hidx] at hSp0
  have hni : q.2.length = (idxTel U np ty).length := by
    rw [hidx, List.length_map, idxTel_length]
    exact (isRecField_eq hrecB).2.1
  have hSp : env.SpineWF (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypes U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.forallN (VExpr.liftTelN
        ((VExpr.liftTelN (ty.ctors.length + 1)
          (ctorFieldsR U np c) 0).reverse.length + ty.ctors.length + 1)
        (idxTel U np ty) 0) (.sort (l.inst (VLevel.params' U 1))))
      (q.2.map fun e => (e.liftN (ty.ctors.length + 1) q.1).liftN
        ((ctorFieldsR U np c).length - q.1))
      (.sort (l.inst (VLevel.params' U 1))) := by
    simpa only [List.length_reverse, VExpr.liftTelN_length] using hSp0
  have hSpLen : (q.2.map fun e =>
      (e.liftN (ty.ctors.length + 1) q.1).liftN
        ((ctorFieldsR U np c).length - q.1)).length =
      (idxTel U np ty).length := by simpa using hni
  have hF : ((VExpr.liftTelN (ty.ctors.length + 1)
      (ctorFieldsR U np c) 0).reverse ++
        ((minorTypes U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))[
      (ctorFieldsR U np c).length - 1 - q.1]? =
      some ((B.instL (VLevel.params' U 1)).liftN
        (ty.ctors.length + 1) q.1) := by
    rw [List.getElem?_append_left
        (by simp only [List.length_reverse, VExpr.liftTelN_length]; omega),
      List.getElem?_reverse (by simp only [VExpr.liftTelN_length]; omega),
      VExpr.liftTelN_length,
      show (ctorFieldsR U np c).length - 1 -
        ((ctorFieldsR U np c).length - 1 - q.1) = q.1 from by omega,
      VExpr.liftTelN_getElem?, ctorFieldsR_getElem?, hBj]
    simp only [Option.map_some, Nat.zero_add]
  have hflu := Lookup.of_getElem? hF
  rw [show (((B.instL (VLevel.params' U 1)).liftN
      (ty.ctors.length + 1) q.1).liftN
        ((ctorFieldsR U np c).length - 1 - q.1 + 1)) =
      VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange ((ctorFieldsR U np c).length + ty.ctors.length + 1) np ++
          q.2.map fun e => (e.liftN (ty.ctors.length + 1) q.1).liftN
            ((ctorFieldsR U np c).length - q.1)) from by
    conv => lhs; rw [(isRecField_eq hrecB).1]
    rw [VExpr.instL_appN, List.map_append, bvarRevRange_instL,
      show (VExpr.const T (VLevel.params U)).instL (VLevel.params' U 1) =
        .const T (VLevel.params' U 1) from by
        simp [VExpr.instL, VLevel.params_map_inst_params'],
      VExpr.liftN_appN, VExpr.liftN_appN, List.map_append, List.map_append,
      bvarRevRange_liftN_ge _ _ _ _ (by omega),
      bvarRevRange_liftN_ge _ _ _ _ (Nat.zero_le _),
      VExpr.bvarRevRange_congr np (show
        (ctorFieldsR U np c).length - 1 - q.1 + 1 +
          (ty.ctors.length + 1 + q.1) =
        (ctorFieldsR U np c).length + ty.ctors.length + 1 from by omega),
      ← hidx, List.map_map]
    apply congrArg (VExpr.appN (.const T (VLevel.params' U 1)))
    apply congrArg (VExpr.bvarRevRange
      ((ctorFieldsR U np c).length + ty.ctors.length + 1) np ++ ·)
    apply List.map_congr_left
    intro e _
    rw [show (ctorFieldsR U np c).length - 1 - q.1 + 1 =
      (ctorFieldsR U np c).length - q.1 from by omega]
    simp only [Function.comp_apply]
    ] at hflu
  have ha : env.HasType (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypes U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (.bvar ((ctorFieldsR U np c).length - 1 - q.1))
      (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange
          ((VExpr.liftTelN (ty.ctors.length + 1)
            (ctorFieldsR U np c) 0).reverse.length + ty.ctors.length + 1) np ++
          q.2.map fun e => (e.liftN (ty.ctors.length + 1) q.1).liftN
            ((ctorFieldsR U np c).length - q.1))) := by
    simpa only [List.length_reverse, VExpr.liftTelN_length] using
      (VEnv.HasType.bvar (env := env) (U := U+1) hflu)
  have hr := S.recApp_hasType hrec
    (VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse
    hSp hSpLen ha
  rw [List.length_reverse, VExpr.liftTelN_length,
    show (ctorFieldsR U np c).length + ty.ctors.length =
      ty.ctors.length + (ctorFieldsR U np c).length from by omega] at hr
  exact hr

/-- A generalized recursive argument yields the direct or lambda-valued
recursive call required by its functional IH in the complete rule context. -/
theorem Stage3Env.ruleCallRec_hasType {c : VConstVal} (hc : c ∈ ty.ctors)
    (hrec : env.constants (.str T "rec") = some (recConstRec U T np ty))
    {r : RecArg} (hr : r ∈ recArgsR U T np (idxTel U np ty).length c) :
    env.HasType (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypesRec U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (r.ruleCall (ctorFieldsR U np c).length ty.ctors.length
        (VExpr.appN (.const (.str T "rec") (VLevel.params (U+1)))
          (VExpr.bvarRevRange (ctorFieldsR U np c).length
            (np + ty.ctors.length + 1))))
      (r.ruleIH (ctorFieldsR U np c).length ty.ctors.length) := by
  obtain ⟨r₀, B, rfl, hB, hr₀⟩ := recArgsR_mem hr
  let r := r₀.instL (VLevel.params' U 1)
  let m := (ctorFieldsR U np c).length
  let k := ty.ctors.length
  let j := r₀.fieldIndex
  let Fs := VExpr.liftTelN (k+1) (ctorFieldsR U np c) 0
  let As := r.ruleBinders m k
  let idxs := r.indices.map fun e =>
    (e.liftN (k+1) (r.fieldIndex+r.binders.length)).liftN
      (m-r.fieldIndex) r.binders.length
  let Γ := Fs.reverse ++ ((minorTypesRec U T np ty ty.ctors).reverse ++
    (motiveType U T np ty :: (paramsTel U np ty).reverse))
  have hjm : j < m := by
    simpa [j, m, RecArg.instL, ctorFieldsR_length] using recArgsR_lt _ hr
  have hFsLen : Fs.length = m := by
    simp [Fs, m, VExpr.liftTelN_length]
  have ht := S.recArg_transport hc hB hr₀
    ((minorTypesRec U T np ty ty.ctors).reverse ++ [motiveType U T np ty])
    (g := k+1) (by simp [k, minorTypesRec_length])
    (Fs.drop j).reverse (d := m-j) (by
      simp only [List.length_reverse, List.length_drop, hFsLen])
  dsimp only [r, j, RecArg.instL] at ht
  have hctx :
      (Fs.drop j).reverse ++
          ((VExpr.liftTelN (k+1) ((ctorFieldsR U np c).take j) 0).reverse ++
            (((minorTypesRec U T np ty ty.ctors).reverse ++
              [motiveType U T np ty]) ++ (paramsTel U np ty).reverse)) = Γ := by
    dsimp only [Γ, Fs]
    rw [← VExpr.liftTelN_take, List.append_assoc,
      ← List.append_assoc
        (((VExpr.liftTelN (k+1) (ctorFieldsR U np c) 0).drop j).reverse),
      ← List.reverse_append, List.take_append_drop, List.singleton_append,
      ← List.append_assoc]
  have htel : OnTel env (U+1) Γ As := by
    rw [hctx] at ht
    simpa [r, As, m, k, j, RecArg.instL, RecArg.ruleBinders] using ht.1
  have hsp : env.SpineWF (U+1) (As.reverse ++ Γ)
      (VExpr.forallN
        (VExpr.liftTelN (m+k+r.binders.length+1) (idxTel U np ty) 0)
        (.sort (l.inst (VLevel.params' U 1))))
      idxs (.sort (l.inst (VLevel.params' U 1))) := by
    rw [hctx] at ht
    simpa [r, As, idxs, m, k, j, RecArg.instL, RecArg.ruleBinders,
      List.append_assoc,
      show j + r₀.binders.length + (k+1) + (m-j) =
        m+k+r₀.binders.length+1 from by omega] using ht.2
  have hF : Γ[m-1-j]? =
      some ((B.instL (VLevel.params' U 1)).liftN (k+1) j) := by
    dsimp only [Γ, Fs]
    rw [List.getElem?_append_left
        (by simp only [List.length_reverse, VExpr.liftTelN_length]; omega),
      List.getElem?_reverse (by rw [hFsLen]; omega),
      VExpr.liftTelN_length,
      show m - 1 - (m - 1 - j) = j from by omega,
      VExpr.liftTelN_getElem?, ctorFieldsR_getElem?, hB]
    simp
  have hlu := Lookup.of_getElem? hF
  dsimp only [j, r] at hlu
  rw [show m-1-r₀.fieldIndex+1 = m-r₀.fieldIndex from by omega]
    at hlu
  have hfield := recArg_rule_fieldType hr₀ m k (by simpa [j] using hjm)
  simp only [RecArg.instL] at hfield
  rw [hfield] at hlu
  have hf0 := VEnv.HasType.bvar (env := env) (U := U+1) hlu
  have hf := hf0.weakN S.ord (Ctx.LiftN.zero (Γ := Γ) As.reverse)
  have hmajor := VEnv.HasType.appN_selfSpine (env := env) (U := U+1)
    (As := As) (B := VExpr.appN (.const T (VLevel.params' U 1))
      (VExpr.bvarRevRange (m+k+r.binders.length+1) np ++ idxs))
    (Δ := []) (Γ := Γ) (by
      simpa [As, r, idxs, j, RecArg.instL, RecArg.ruleBinders,
        List.length_reverse, List.map_map, Function.comp_def] using hf)
  simp only [List.length_nil, VExpr.liftN_zero, List.nil_append] at hmajor
  have hAsLen : As.length = r.binders.length := by
    simp [As, RecArg.ruleBinders, VExpr.liftTelN_length]
  have hmajorHead :
      (VExpr.bvar (m-1-r.fieldIndex)).liftN As.length =
        .bvar (m-1-r.fieldIndex+r.binders.length) := by
    simp only [VExpr.liftN, liftVar_base]
    congr 1
    rw [hAsLen]
    omega
  change env.HasType (U+1) (As.reverse ++ Γ)
    (((VExpr.bvar (m-1-r.fieldIndex)).liftN As.length).appN
      (VExpr.bvarRevRange 0 As.length))
    (VExpr.appN (.const T (VLevel.params' U 1))
      (VExpr.bvarRevRange (m+k+r.binders.length+1) np ++ idxs)) at hmajor
  rw [hmajorHead, hAsLen] at hmajor
  have hlen : idxs.length = (idxTel U np ty).length := by
    simpa [idxs, r, RecArg.instL] using (recArg?_eq hr₀).2.2.2.1
  have hcall := S.recAppRec_hasType hrec (As.reverse ++ Fs.reverse)
    (by simpa [Γ, List.append_assoc, hAsLen, hFsLen, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc] using hsp)
    hlen
    (by simpa [Γ, List.append_assoc, hAsLen, hFsLen, Nat.add_comm,
      Nat.add_left_comm, Nat.add_assoc] using hmajor)
  have hbase :
      (VExpr.appN (.const (.str T "rec") (VLevel.params (U+1)))
        (VExpr.bvarRevRange m (np+(k+1)))).liftN r.binders.length =
      VExpr.appN (.const (.str T "rec") (VLevel.params (U+1)))
        (VExpr.bvarRevRange (m+r.binders.length) (np+(k+1))) := by
    rw [VExpr.liftN_appN]
    simp only [VExpr.liftN]
    rw [bvarRevRange_liftN_ge _ _ _ _ (Nat.zero_le _)]
    apply congrArg (VExpr.appN _)
    apply VExpr.bvarRevRange_congr
    omega
  have hlam := HasType.lamN htel (by
    simpa [Γ, Fs, hAsLen, hFsLen, List.append_assoc,
      VExpr.liftN_appN, bvarRevRange_liftN_ge _ _ _ _ (Nat.zero_le _),
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hcall)
  simpa [RecArg.ruleCall, RecArg.ruleIH, r, As, idxs, m, k, Γ, Fs, hbase,
    List.append_assoc, Nat.add_assoc] using hlam


/-- The right-hand side of an indexed iota rule: the constructor's minor
premise applied to its fields and to one indexed recursive call per recursive
field. -/
theorem Stage3Env.minorApp_hasType {i : Nat} {c : VConstVal}
    (hci : ty.ctors[i]? = some c)
    (hrec : env.constants (.str T "rec") = some (recConst U T np ty)) :
    env.HasType (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypes U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.appN (.bvar (ty.ctors.length - 1 - i + (ctorFieldsR U np c).length))
        (VExpr.bvarRevRange 0 (ctorFieldsR U np c).length ++
          List.map (fun q => VExpr.appN
              (VExpr.appN (.const (.str T "rec") (VLevel.params (U+1)))
                (VExpr.bvarRevRange (ctorFieldsR U np c).length
                  (np + ty.ctors.length + 1)))
              ((q.2.map fun e =>
                (e.liftN (ty.ctors.length + 1) q.1).liftN
                  ((ctorFieldsR U np c).length - q.1)) ++
                [.bvar ((ctorFieldsR U np c).length - 1 - q.1)]))
            (recPairsR U T np (idxTel U np ty).length c)))
      (VExpr.appN (.bvar (ty.ctors.length + (ctorFieldsR U np c).length))
        (((ctorIdxs U np c).map fun e =>
          e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length) ++
          [VExpr.appN (.const c.name (VLevel.params' U 1))
            (VExpr.bvarRevRange ((ctorFieldsR U np c).length +
                ty.ctors.length + 1) np ++
              VExpr.bvarRevRange 0 (ctorFieldsR U np c).length)])) := by
  obtain ⟨hik, -⟩ := List.getElem?_eq_some_iff.1 hci
  have hc := List.mem_of_getElem? hci
  let rs := recPairsR U T np (idxTel U np ty).length c
  have hrs : rs = recPairsR U T np (idxTel U np ty).length c := rfl
  have hrsLt : ∀ q ∈ rs, q.1 < (ctorFieldsR U np c).length := by
    intro q hq
    simpa [hrs, ctorFieldsR_length] using recPairsR_lt _ hq
  rw [VExpr.appN_append]
  have hlu0 : ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
      ((minorTypes U T np ty ty.ctors).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse)))[
      ty.ctors.length - 1 - i + (ctorFieldsR U np c).length]? =
      some (VExpr.liftN i (minorType U T np ty c)) := by
    rw [getElem?_rstack_mid _ _ _
        (by simp only [List.length_reverse, VExpr.liftTelN_length]; omega)
        (by simp only [List.length_reverse, VExpr.liftTelN_length, minorTypes_length]
            omega),
      show ty.ctors.length - 1 - i + (ctorFieldsR U np c).length -
        ((VExpr.liftTelN (ty.ctors.length + 1)
          (ctorFieldsR U np c) 0).reverse).length =
        ty.ctors.length - 1 - i from by
          simp only [List.length_reverse, VExpr.liftTelN_length]
          omega,
      List.getElem?_reverse (by simp only [minorTypes_length]; omega),
      show (minorTypes U T np ty ty.ctors).length - 1 -
          (ty.ctors.length - 1 - i) = i from by
        simp only [minorTypes_length]
        omega,
      minorTypes_getElem?, hci, Nat.zero_add]
    rfl
  have hlu := Lookup.of_getElem? hlu0
  rw [VExpr.liftN_liftN,
    show i + (ty.ctors.length - 1 - i + (ctorFieldsR U np c).length + 1) =
      (ctorFieldsR U np c).length + ty.ctors.length from by omega] at hlu
  have hminorEq : (minorType U T np ty c).liftN
      ((ctorFieldsR U np c).length + ty.ctors.length) =
      (VExpr.forallN
        (VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0)
        ((VExpr.forallN (ihsFrom (ctorFieldsR U np c).length rs 0)
          (VExpr.appN (.bvar ((ctorFieldsR U np c).length + rs.length))
            (((ctorIdxs U np c).map fun e =>
              (e.liftN 1 (ctorFieldsR U np c).length).liftN rs.length) ++
              [VExpr.appN (.const c.name (VLevel.params' U 1))
                (VExpr.bvarRevRange (rs.length +
                    (ctorFieldsR U np c).length + 1) np ++
                  VExpr.bvarRevRange rs.length (ctorFieldsR U np c).length)]))).liftN
            ty.ctors.length (ctorFieldsR U np c).length)).liftN
        (ctorFieldsR U np c).length := by
    simp only [minorType, rs, hrs]
    conv => lhs; rw [VExpr.liftN_forallN, VExpr.liftTelN_liftTelN,
        liftTelN_congr _ _ (show (1:Nat) +
          ((ctorFieldsR U np c).length + ty.ctors.length) =
          ty.ctors.length + 1 + (ctorFieldsR U np c).length from by omega),
        show (0:Nat) + (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).length =
          (ctorFieldsR U np c).length from by simp [VExpr.liftTelN_length]]
    conv => rhs; rw [VExpr.liftN_forallN, VExpr.liftTelN_liftTelN,
        show (0:Nat) + (VExpr.liftTelN (ty.ctors.length + 1)
          (ctorFieldsR U np c) 0).length = (ctorFieldsR U np c).length from by
          simp [VExpr.liftTelN_length],
        VExpr.liftN'_liftN_hi,
        Nat.add_comm ty.ctors.length (ctorFieldsR U np c).length]
  have hfields := HasType.appN_selfSpine (env := env) (U := U+1)
    (As := VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0)
    (B := (VExpr.forallN (ihsFrom (ctorFieldsR U np c).length rs 0)
      (VExpr.appN (.bvar ((ctorFieldsR U np c).length + rs.length))
        (((ctorIdxs U np c).map fun e =>
          (e.liftN 1 (ctorFieldsR U np c).length).liftN rs.length) ++
          [VExpr.appN (.const c.name (VLevel.params' U 1))
            (VExpr.bvarRevRange (rs.length + (ctorFieldsR U np c).length + 1) np ++
              VExpr.bvarRevRange rs.length (ctorFieldsR U np c).length)]))).liftN
        ty.ctors.length (ctorFieldsR U np c).length)
    (Δ := [])
    (Γ := (minorTypes U T np ty ty.ctors).reverse ++
      (motiveType U T np ty :: (paramsTel U np ty).reverse))
    (f := .bvar (ty.ctors.length - 1 - i + (ctorFieldsR U np c).length)) (by
      have hb := VEnv.HasType.bvar (env := env) (U := U+1) hlu
      rw [hminorEq] at hb
      simpa [VExpr.liftTelN_length] using hb)
  simp only [List.length_nil, VExpr.liftTelN_length, VExpr.liftN_zero] at hfields
  rw [ihsFrom_liftN' (ctorFieldsR U np c).length ty.ctors.length rs
    hrsLt 0
    (VExpr.appN (.bvar ((ctorFieldsR U np c).length + rs.length))
      (((ctorIdxs U np c).map fun e =>
        (e.liftN 1 (ctorFieldsR U np c).length).liftN rs.length) ++
        [VExpr.appN (.const c.name (VLevel.params' U 1))
          (VExpr.bvarRevRange (rs.length + (ctorFieldsR U np c).length + 1) np ++
            VExpr.bvarRevRange rs.length (ctorFieldsR U np c).length)]))
    (cut := (ctorFieldsR U np c).length) rfl] at hfields
  have hD :
      (VExpr.appN (.bvar ((ctorFieldsR U np c).length + rs.length))
        (((ctorIdxs U np c).map fun e =>
          (e.liftN 1 (ctorFieldsR U np c).length).liftN rs.length) ++
          [VExpr.appN (.const c.name (VLevel.params' U 1))
            (VExpr.bvarRevRange (rs.length + (ctorFieldsR U np c).length + 1) np ++
              VExpr.bvarRevRange rs.length (ctorFieldsR U np c).length)])).liftN
        ty.ctors.length ((ctorFieldsR U np c).length + 0 + rs.length) =
      (VExpr.appN (.bvar (ty.ctors.length + (ctorFieldsR U np c).length))
        (((ctorIdxs U np c).map fun e =>
          e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length) ++
          [VExpr.appN (.const c.name (VLevel.params' U 1))
            (VExpr.bvarRevRange ((ctorFieldsR U np c).length +
                ty.ctors.length + 1) np ++
              VExpr.bvarRevRange 0 (ctorFieldsR U np c).length)])).liftN rs.length := by
    rw [VExpr.liftN_appN, VExpr.liftN_appN, List.map_append, List.map_append,
      List.map_map, List.map_map]
    show VExpr.appN _ (_ ++ [_]) = VExpr.appN _ (_ ++ [_])
    congr 1
    · show VExpr.bvar (liftVar ty.ctors.length
          ((ctorFieldsR U np c).length + rs.length)
          ((ctorFieldsR U np c).length + 0 + rs.length)) =
        VExpr.bvar (liftVar rs.length
          (ty.ctors.length + (ctorFieldsR U np c).length) 0)
      rw [liftVar_le (by omega), liftVar_le (Nat.zero_le _)]
      congr 1
      omega
    · congr 1
      · apply List.map_congr_left
        intro e _
        simp only [Function.comp_apply]
        rw [show (ctorFieldsR U np c).length + 0 + rs.length =
          (ctorFieldsR U np c).length + rs.length from by omega,
          VExpr.liftN_liftN_mid e ty.ctors.length rs.length (Nat.zero_le _)]
      · congr 1
        simp only [Function.comp_apply]
        rw [show (ctorFieldsR U np c).length + 0 + rs.length =
          (ctorFieldsR U np c).length + rs.length from by omega]
        rw [VExpr.liftN_appN, VExpr.liftN_appN, List.map_append, List.map_append,
          bvarRevRange_liftN_ge _ _ _ _ (by omega),
          VExpr.bvarRevRange_liftN_high _ _ _ _ (by omega),
          bvarRevRange_liftN_ge _ _ _ _ (Nat.zero_le _),
          bvarRevRange_liftN_ge _ _ _ _ (Nat.zero_le _),
          VExpr.bvarRevRange_congr np (show ty.ctors.length +
            (rs.length + (ctorFieldsR U np c).length + 1) =
            rs.length + ((ctorFieldsR U np c).length + ty.ctors.length + 1) from by
              omega),
          VExpr.bvarRevRange_congr _ (show rs.length = rs.length + 0 from by omega)]
        rfl
  rw [hD] at hfields
  have hres := hasType_appN_ihs (env := env) (U := U+1)
    (m := (ctorFieldsR U np c).length) (k := ty.ctors.length)
    (rs := rs)
    (argOf := fun (j, idxs) =>
      VExpr.appN
        (VExpr.appN (.const (.str T "rec") (VLevel.params (U+1)))
          (VExpr.bvarRevRange (ctorFieldsR U np c).length
            (np + ty.ctors.length + 1)))
        ((idxs.map fun e => (e.liftN (ty.ctors.length + 1) j).liftN
          ((ctorFieldsR U np c).length - j)) ++
          [.bvar ((ctorFieldsR U np c).length - 1 - j)]))
    hrsLt (fun q hq => by
      have hr := S.recCallRule_hasType hc hrec (hrs ▸ hq)
      have hargs : (q.2.map fun e =>
          ((e.liftN 1 q.1).liftN ((ctorFieldsR U np c).length - q.1)).liftN
            ty.ctors.length (ctorFieldsR U np c).length) =
          q.2.map fun e => (e.liftN (ty.ctors.length + 1) q.1).liftN
            ((ctorFieldsR U np c).length - q.1) := by
        apply List.map_congr_left
        intro e _
        rw [← VExpr.liftN_liftN_mid e ty.ctors.length
          ((ctorFieldsR U np c).length - q.1) (Nat.zero_le _),
          show q.1 + ((ctorFieldsR U np c).length - q.1) =
            (ctorFieldsR U np c).length from by
              have := hrsLt q hq
              omega]
      rw [hargs]
      exact hr)
    hfields
  simpa only [hrs] using hres

/-- Generalized iota RHS: apply the selected constructor minor to every field
and then to the direct or functional recursive call generated for each
`RecArg`. -/
theorem Stage3Env.minorAppRec_hasType {i : Nat} {c : VConstVal}
    (hci : ty.ctors[i]? = some c)
    (hrec : env.constants (.str T "rec") = some (recConstRec U T np ty)) :
    env.HasType (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypesRec U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.appN (.bvar (ty.ctors.length - 1 - i + (ctorFieldsR U np c).length))
        (VExpr.bvarRevRange 0 (ctorFieldsR U np c).length ++
          List.map (fun r => r.ruleCall (ctorFieldsR U np c).length ty.ctors.length
              (VExpr.appN (.const (.str T "rec") (VLevel.params (U+1)))
                (VExpr.bvarRevRange (ctorFieldsR U np c).length
                  (np + ty.ctors.length + 1))))
            (recArgsR U T np (idxTel U np ty).length c)))
      (VExpr.appN (.bvar (ty.ctors.length + (ctorFieldsR U np c).length))
        (((ctorIdxs U np c).map fun e =>
          e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length) ++
          [VExpr.appN (.const c.name (VLevel.params' U 1))
            (VExpr.bvarRevRange ((ctorFieldsR U np c).length +
                ty.ctors.length + 1) np ++
              VExpr.bvarRevRange 0 (ctorFieldsR U np c).length)])) := by
  obtain ⟨hik, -⟩ := List.getElem?_eq_some_iff.1 hci
  have hc := List.mem_of_getElem? hci
  let rs := recArgsR U T np (idxTel U np ty).length c
  have hrs : rs = recArgsR U T np (idxTel U np ty).length c := rfl
  have hrsLt : ∀ r ∈ rs, r.fieldIndex < (ctorFieldsR U np c).length := by
    intro r hr
    simpa [hrs, ctorFieldsR_length] using recArgsR_lt _ hr
  rw [VExpr.appN_append]
  have hlu0 : ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
      ((minorTypesRec U T np ty ty.ctors).reverse ++
        (motiveType U T np ty :: (paramsTel U np ty).reverse)))[
      ty.ctors.length - 1 - i + (ctorFieldsR U np c).length]? =
      some (VExpr.liftN i (minorTypeRec U T np ty c)) := by
    rw [getElem?_rstack_mid _ _ _
        (by simp only [List.length_reverse, VExpr.liftTelN_length]; omega)
        (by simp only [List.length_reverse, VExpr.liftTelN_length,
          minorTypesRec_length]; omega),
      show ty.ctors.length - 1 - i + (ctorFieldsR U np c).length -
        ((VExpr.liftTelN (ty.ctors.length + 1)
          (ctorFieldsR U np c) 0).reverse).length =
        ty.ctors.length - 1 - i from by
          simp only [List.length_reverse, VExpr.liftTelN_length]
          omega,
      List.getElem?_reverse (by simp only [minorTypesRec_length]; omega),
      show (minorTypesRec U T np ty ty.ctors).length - 1 -
          (ty.ctors.length - 1 - i) = i from by
        simp only [minorTypesRec_length]
        omega,
      minorTypesRec_getElem?, hci, Nat.zero_add]
    rfl
  have hlu := Lookup.of_getElem? hlu0
  rw [VExpr.liftN_liftN,
    show i + (ty.ctors.length - 1 - i + (ctorFieldsR U np c).length + 1) =
      (ctorFieldsR U np c).length + ty.ctors.length from by omega] at hlu
  have hminorEq : (minorTypeRec U T np ty c).liftN
      ((ctorFieldsR U np c).length + ty.ctors.length) =
      (VExpr.forallN
        (VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0)
        ((VExpr.forallN (ihsFromRecArgs (ctorFieldsR U np c).length rs 0)
          (VExpr.appN (.bvar ((ctorFieldsR U np c).length + rs.length))
            (((ctorIdxs U np c).map fun e =>
              (e.liftN 1 (ctorFieldsR U np c).length).liftN rs.length) ++
              [VExpr.appN (.const c.name (VLevel.params' U 1))
                (VExpr.bvarRevRange (rs.length +
                    (ctorFieldsR U np c).length + 1) np ++
                  VExpr.bvarRevRange rs.length (ctorFieldsR U np c).length)]))).liftN
            ty.ctors.length (ctorFieldsR U np c).length)).liftN
        (ctorFieldsR U np c).length := by
    simp only [minorTypeRec, rs, hrs]
    conv => lhs; rw [VExpr.liftN_forallN, VExpr.liftTelN_liftTelN,
        liftTelN_congr _ _ (show (1:Nat) +
          ((ctorFieldsR U np c).length + ty.ctors.length) =
          ty.ctors.length + 1 + (ctorFieldsR U np c).length from by omega),
        show (0:Nat) + (VExpr.liftTelN 1 (ctorFieldsR U np c) 0).length =
          (ctorFieldsR U np c).length from by simp [VExpr.liftTelN_length]]
    conv => rhs; rw [VExpr.liftN_forallN, VExpr.liftTelN_liftTelN,
        show (0:Nat) + (VExpr.liftTelN (ty.ctors.length + 1)
          (ctorFieldsR U np c) 0).length = (ctorFieldsR U np c).length from by
          simp [VExpr.liftTelN_length],
        VExpr.liftN'_liftN_hi,
        Nat.add_comm ty.ctors.length (ctorFieldsR U np c).length]
  have hfields := HasType.appN_selfSpine (env := env) (U := U+1)
    (As := VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0)
    (B := (VExpr.forallN (ihsFromRecArgs (ctorFieldsR U np c).length rs 0)
      (VExpr.appN (.bvar ((ctorFieldsR U np c).length + rs.length))
        (((ctorIdxs U np c).map fun e =>
          (e.liftN 1 (ctorFieldsR U np c).length).liftN rs.length) ++
          [VExpr.appN (.const c.name (VLevel.params' U 1))
            (VExpr.bvarRevRange (rs.length + (ctorFieldsR U np c).length + 1) np ++
              VExpr.bvarRevRange rs.length (ctorFieldsR U np c).length)]))).liftN
        ty.ctors.length (ctorFieldsR U np c).length)
    (Δ := [])
    (Γ := (minorTypesRec U T np ty ty.ctors).reverse ++
      (motiveType U T np ty :: (paramsTel U np ty).reverse))
    (f := .bvar (ty.ctors.length - 1 - i + (ctorFieldsR U np c).length)) (by
      have hb := VEnv.HasType.bvar (env := env) (U := U+1) hlu
      rw [hminorEq] at hb
      simpa [VExpr.liftTelN_length] using hb)
  simp only [List.length_nil, VExpr.liftTelN_length, VExpr.liftN_zero] at hfields
  rw [ihsFromRecArgs_liftN' (ctorFieldsR U np c).length ty.ctors.length rs
    hrsLt 0
    (VExpr.appN (.bvar ((ctorFieldsR U np c).length + rs.length))
      (((ctorIdxs U np c).map fun e =>
        (e.liftN 1 (ctorFieldsR U np c).length).liftN rs.length) ++
        [VExpr.appN (.const c.name (VLevel.params' U 1))
          (VExpr.bvarRevRange (rs.length + (ctorFieldsR U np c).length + 1) np ++
            VExpr.bvarRevRange rs.length (ctorFieldsR U np c).length)]))
    (cut := (ctorFieldsR U np c).length) rfl] at hfields
  have hD :
      (VExpr.appN (.bvar ((ctorFieldsR U np c).length + rs.length))
        (((ctorIdxs U np c).map fun e =>
          (e.liftN 1 (ctorFieldsR U np c).length).liftN rs.length) ++
          [VExpr.appN (.const c.name (VLevel.params' U 1))
            (VExpr.bvarRevRange (rs.length + (ctorFieldsR U np c).length + 1) np ++
              VExpr.bvarRevRange rs.length (ctorFieldsR U np c).length)])).liftN
        ty.ctors.length ((ctorFieldsR U np c).length + 0 + rs.length) =
      (VExpr.appN (.bvar (ty.ctors.length + (ctorFieldsR U np c).length))
        (((ctorIdxs U np c).map fun e =>
          e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length) ++
          [VExpr.appN (.const c.name (VLevel.params' U 1))
            (VExpr.bvarRevRange ((ctorFieldsR U np c).length +
                ty.ctors.length + 1) np ++
              VExpr.bvarRevRange 0 (ctorFieldsR U np c).length)])).liftN rs.length := by
    rw [VExpr.liftN_appN, VExpr.liftN_appN, List.map_append, List.map_append,
      List.map_map, List.map_map]
    show VExpr.appN _ (_ ++ [_]) = VExpr.appN _ (_ ++ [_])
    congr 1
    · show VExpr.bvar (liftVar ty.ctors.length
          ((ctorFieldsR U np c).length + rs.length)
          ((ctorFieldsR U np c).length + 0 + rs.length)) =
        VExpr.bvar (liftVar rs.length
          (ty.ctors.length + (ctorFieldsR U np c).length) 0)
      rw [liftVar_le (by omega), liftVar_le (Nat.zero_le _)]
      congr 1
      omega
    · congr 1
      · apply List.map_congr_left
        intro e _
        simp only [Function.comp_apply]
        rw [show (ctorFieldsR U np c).length + 0 + rs.length =
          (ctorFieldsR U np c).length + rs.length from by omega,
          VExpr.liftN_liftN_mid e ty.ctors.length rs.length (Nat.zero_le _)]
      · congr 1
        simp only [Function.comp_apply]
        rw [show (ctorFieldsR U np c).length + 0 + rs.length =
          (ctorFieldsR U np c).length + rs.length from by omega]
        rw [VExpr.liftN_appN, VExpr.liftN_appN, List.map_append, List.map_append,
          bvarRevRange_liftN_ge _ _ _ _ (by omega),
          VExpr.bvarRevRange_liftN_high _ _ _ _ (by omega),
          bvarRevRange_liftN_ge _ _ _ _ (Nat.zero_le _),
          bvarRevRange_liftN_ge _ _ _ _ (Nat.zero_le _),
          VExpr.bvarRevRange_congr np (show ty.ctors.length +
            (rs.length + (ctorFieldsR U np c).length + 1) =
            rs.length + ((ctorFieldsR U np c).length + ty.ctors.length + 1) from by
              omega),
          VExpr.bvarRevRange_congr _ (show rs.length = rs.length + 0 from by omega)]
        rfl
  rw [hD] at hfields
  have hres := hasType_appN_ruleIHs (env := env) (U := U+1)
    (m := (ctorFieldsR U np c).length) (k := ty.ctors.length)
    (rs := rs)
    (argOf := fun r => r.ruleCall (ctorFieldsR U np c).length ty.ctors.length
      (VExpr.appN (.const (.str T "rec") (VLevel.params (U+1)))
        (VExpr.bvarRevRange (ctorFieldsR U np c).length
          (np + ty.ctors.length + 1))))
    (fun r hr => S.ruleCallRec_hasType hc hrec (hrs ▸ hr)) hfields
  simpa only [hrs] using hres

/-- The constructor-headed left side of an indexed iota rule. -/
theorem Stage3Env.recRuleApp_hasType {c : VConstVal} (hc : c ∈ ty.ctors)
    (hrec : env.constants (.str T "rec") = some (recConst U T np ty)) :
    env.HasType (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypes U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.appN
        (VExpr.appN (.const (.str T "rec") (VLevel.params (U+1)))
          (VExpr.bvarRevRange (ctorFieldsR U np c).length
            (np + ty.ctors.length + 1)))
        (((ctorIdxs U np c).map fun e =>
          e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length) ++
          [VExpr.appN (.const c.name (VLevel.params' U 1))
            (VExpr.bvarRevRange ((ctorFieldsR U np c).length +
                ty.ctors.length + 1) np ++
              VExpr.bvarRevRange 0 (ctorFieldsR U np c).length)]))
      (VExpr.appN (.bvar (ty.ctors.length + (ctorFieldsR U np c).length))
        (((ctorIdxs U np c).map fun e =>
          e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length) ++
          [VExpr.appN (.const c.name (VLevel.params' U 1))
            (VExpr.bvarRevRange ((ctorFieldsR U np c).length +
                ty.ctors.length + 1) np ++
              VExpr.bvarRevRange 0 (ctorFieldsR U np c).length)])) := by
  have hSp0 := S.result_transport hc
    ((minorTypes U T np ty ty.ctors).reverse ++ [motiveType U T np ty])
    (g := ty.ctors.length + 1) (by simp [minorTypes_length]) [] (d := 0) rfl
  have hSp : env.SpineWF (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypes U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.forallN (VExpr.liftTelN
        ((VExpr.liftTelN (ty.ctors.length + 1)
          (ctorFieldsR U np c) 0).reverse.length + ty.ctors.length + 1)
        (idxTel U np ty) 0) (.sort (l.inst (VLevel.params' U 1))))
      ((ctorIdxs U np c).map fun e =>
        e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length)
      (.sort (l.inst (VLevel.params' U 1))) := by
    simpa [List.append_assoc, Nat.add_assoc, List.length_reverse,
      VExpr.liftTelN_length] using hSp0
  have hidxLen : ((ctorIdxs U np c).map fun e =>
      e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length).length =
      (idxTel U np ty).length := by
    simp only [List.length_map, ctorIdxs_length, idxTel_length]
    exact (stage3Ctor_eq (S.hs3 c hc)).2.1
  have ha0 := S.ctorAppRule_hasType hc
  have ha : env.HasType (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypes U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.appN (.const c.name (VLevel.params' U 1))
        (VExpr.bvarRevRange ((ctorFieldsR U np c).length + ty.ctors.length + 1) np ++
          VExpr.bvarRevRange 0 (ctorFieldsR U np c).length))
      (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange
          ((VExpr.liftTelN (ty.ctors.length + 1)
            (ctorFieldsR U np c) 0).reverse.length + ty.ctors.length + 1) np ++
          (ctorIdxs U np c).map fun e =>
            e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length)) := by
    simpa only [List.length_reverse, VExpr.liftTelN_length] using ha0
  have hr := S.recApp_hasType hrec
    (VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse
    hSp hidxLen ha
  rw [List.length_reverse, VExpr.liftTelN_length,
    show (ctorFieldsR U np c).length + ty.ctors.length =
      ty.ctors.length + (ctorFieldsR U np c).length from by omega,
    show ty.ctors.length + (ctorFieldsR U np c).length + 1 =
      (ctorFieldsR U np c).length + ty.ctors.length + 1 from by omega] at hr
  exact hr

/-- The constructor-headed left side of a generalized indexed iota rule. -/
theorem Stage3Env.recRuleAppRec_hasType {c : VConstVal} (hc : c ∈ ty.ctors)
    (hrec : env.constants (.str T "rec") = some (recConstRec U T np ty)) :
    env.HasType (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypesRec U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.appN
        (VExpr.appN (.const (.str T "rec") (VLevel.params (U+1)))
          (VExpr.bvarRevRange (ctorFieldsR U np c).length
            (np + ty.ctors.length + 1)))
        (((ctorIdxs U np c).map fun e =>
          e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length) ++
          [VExpr.appN (.const c.name (VLevel.params' U 1))
            (VExpr.bvarRevRange ((ctorFieldsR U np c).length +
                ty.ctors.length + 1) np ++
              VExpr.bvarRevRange 0 (ctorFieldsR U np c).length)]))
      (VExpr.appN (.bvar (ty.ctors.length + (ctorFieldsR U np c).length))
        (((ctorIdxs U np c).map fun e =>
          e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length) ++
          [VExpr.appN (.const c.name (VLevel.params' U 1))
            (VExpr.bvarRevRange ((ctorFieldsR U np c).length +
                ty.ctors.length + 1) np ++
              VExpr.bvarRevRange 0 (ctorFieldsR U np c).length)])) := by
  have hSp0 := S.result_transport hc
    ((minorTypesRec U T np ty ty.ctors).reverse ++ [motiveType U T np ty])
    (g := ty.ctors.length + 1) (by simp [minorTypesRec_length]) [] (d := 0) rfl
  have hSp : env.SpineWF (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypesRec U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.forallN (VExpr.liftTelN
        ((VExpr.liftTelN (ty.ctors.length + 1)
          (ctorFieldsR U np c) 0).reverse.length + ty.ctors.length + 1)
        (idxTel U np ty) 0) (.sort (l.inst (VLevel.params' U 1))))
      ((ctorIdxs U np c).map fun e =>
        e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length)
      (.sort (l.inst (VLevel.params' U 1))) := by
    simpa [List.append_assoc, Nat.add_assoc, List.length_reverse,
      VExpr.liftTelN_length] using hSp0
  have hidxLen : ((ctorIdxs U np c).map fun e =>
      e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length).length =
      (idxTel U np ty).length := by
    simp only [List.length_map, ctorIdxs_length, idxTel_length]
    exact (stage3Ctor_eq (S.hs3 c hc)).2.1
  have ha0 := S.ctorAppRuleRec_hasType hc
  have ha : env.HasType (U+1)
      ((VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse ++
        ((minorTypesRec U T np ty ty.ctors).reverse ++
          (motiveType U T np ty :: (paramsTel U np ty).reverse)))
      (VExpr.appN (.const c.name (VLevel.params' U 1))
        (VExpr.bvarRevRange ((ctorFieldsR U np c).length + ty.ctors.length + 1) np ++
          VExpr.bvarRevRange 0 (ctorFieldsR U np c).length))
      (VExpr.appN (.const T (VLevel.params' U 1))
        (VExpr.bvarRevRange
          ((VExpr.liftTelN (ty.ctors.length + 1)
            (ctorFieldsR U np c) 0).reverse.length + ty.ctors.length + 1) np ++
          (ctorIdxs U np c).map fun e =>
            e.liftN (ty.ctors.length + 1) (ctorFieldsR U np c).length)) := by
    simpa only [List.length_reverse, VExpr.liftTelN_length] using ha0
  have hr := S.recAppRec_hasType hrec
    (VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0).reverse
    hSp hidxLen ha
  rw [List.length_reverse, VExpr.liftTelN_length,
    show (ctorFieldsR U np c).length + ty.ctors.length =
      ty.ctors.length + (ctorFieldsR U np c).length from by omega,
    show ty.ctors.length + (ctorFieldsR U np c).length + 1 =
      (ctorFieldsR U np c).length + ty.ctors.length + 1 from by omega] at hr
  exact hr

/-- Well-formedness of the iota rule for the `i`-th constructor. -/
theorem Stage3Env.rule_WF {i : Nat} {c : VConstVal}
    (hci : ty.ctors[i]? = some c)
    (hrec : env.constants (.str T "rec") = some (recConst U T np ty)) :
    (rule U T np ty i c).WF env := by
  have hc := List.mem_of_getElem? hci
  refine ⟨?_, ?_⟩
  · show env.HasType (U+1) [] (VExpr.lamN
      (paramsTel U np ty ++ motiveType U T np ty :: minorTypes U T np ty ty.ctors ++
        VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0) _)
      (VExpr.forallN _ _)
    refine HasType.lamN (S.ruleBinders_onTel hc) ?_
    simp only [List.reverse_append, List.reverse_cons, List.append_nil,
      List.append_assoc, List.singleton_append]
    exact S.recRuleApp_hasType hc hrec
  · show env.HasType (U+1) [] (VExpr.lamN
      (paramsTel U np ty ++ motiveType U T np ty :: minorTypes U T np ty ty.ctors ++
        VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0) _)
      (VExpr.forallN _ _)
    refine HasType.lamN (S.ruleBinders_onTel hc) ?_
    simp only [List.reverse_append, List.reverse_cons, List.append_nil,
      List.append_assoc, List.singleton_append]
    exact S.minorApp_hasType hci hrec

/-- Well-formedness of the generalized iota rule for the `i`-th constructor. -/
theorem Stage3Env.ruleRec_WF {i : Nat} {c : VConstVal}
    (hci : ty.ctors[i]? = some c)
    (hrec : env.constants (.str T "rec") = some (recConstRec U T np ty)) :
    (ruleRec U T np ty i c).WF env := by
  have hc := List.mem_of_getElem? hci
  refine ⟨?_, ?_⟩
  · show env.HasType (U+1) [] (VExpr.lamN
      (paramsTel U np ty ++ motiveType U T np ty :: minorTypesRec U T np ty ty.ctors ++
        VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0) _)
      (VExpr.forallN _ _)
    refine HasType.lamN (S.ruleBindersRec_onTel hc) ?_
    simp only [List.reverse_append, List.reverse_cons, List.append_nil,
      List.append_assoc, List.singleton_append]
    exact S.recRuleAppRec_hasType hc hrec
  · show env.HasType (U+1) [] (VExpr.lamN
      (paramsTel U np ty ++ motiveType U T np ty :: minorTypesRec U T np ty ty.ctors ++
        VExpr.liftTelN (ty.ctors.length + 1) (ctorFieldsR U np c) 0) _)
      (VExpr.forallN _ _)
    refine HasType.lamN (S.ruleBindersRec_onTel hc) ?_
    simp only [List.reverse_append, List.reverse_cons, List.append_nil,
      List.append_assoc, List.singleton_append]
    exact S.minorAppRec_hasType hci hrec

/-- `ctorType_eq` from the per-constructor facts directly (for use before
the constructor is in the environment). -/
theorem Stage3Env.ctorType_eq' {c : VConstVal}
    (htelc : VExpr.telN np c.type = VExpr.telN np ty.type)
    (hs3c : stage3Ctor U T np
      (ctorFields (VExpr.dropN np ty.type)).length 0 (VExpr.dropN np c.type)) :
    c.type = VExpr.forallN (VExpr.telN np ty.type)
      (VExpr.forallN (ctorFields (VExpr.dropN np c.type))
        (VExpr.appN (.const T (VLevel.params U))
          (VExpr.bvarRevRange (0 + (ctorFields (VExpr.dropN np c.type)).length) np ++
            recFieldIdxs np (VExpr.resultOf (VExpr.dropN np c.type))))) := by
  conv => lhs; rw [← VExpr.forallN_telN_dropN np c.type, htelc,
    (stage3Ctor_eq hs3c).1]

/-- `ctorType_isType` from the per-constructor facts directly. -/
theorem Stage3Env.ctorType_isType' {c : VConstVal}
    (htelc : VExpr.telN np c.type = VExpr.telN np ty.type)
    (hs3c : stage3Ctor U T np
      (ctorFields (VExpr.dropN np ty.type)).length 0 (VExpr.dropN np c.type))
    (hfc : fieldsWF U T np env l (ctorFields (VExpr.dropN np ty.type))
      (VExpr.telN np ty.type).reverse 0 (ctorFields (VExpr.dropN np c.type)))
    (hresultc : env.SpineWF U
      ((ctorFields (VExpr.dropN np c.type)).reverse ++
        (VExpr.telN np ty.type).reverse)
      (VExpr.forallN (VExpr.liftTelN
        (ctorFields (VExpr.dropN np c.type)).length
        (ctorFields (VExpr.dropN np ty.type)) 0) (.sort l))
      (recFieldIdxs np (VExpr.resultOf (VExpr.dropN np c.type))) (.sort l)) :
    env.IsType U [] c.type := by
  rw [S.ctorType_eq' htelc hs3c]
  refine IsType.forallN S.hparams.of_append.1 ?_
  simp only [List.append_nil]
  refine IsType.forallN
    (S.fieldsWF_onTel_decl _ [] 0 rfl (by simpa using hfc)) ?_
  have hTapp := S.recAppPi_hasType_decl
    ((ctorFields (VExpr.dropN np c.type)).reverse)
  rw [List.length_reverse, VExpr.liftN_forallN] at hTapp
  have hres := hresultc.hasType_appN hTapp
  exact ⟨_, by
    rw [VExpr.appN_append, Nat.zero_add]
    exact hres⟩

omit S in
/-- In the identity path, each paired constructor receives the granular
raw/view certificate required immediately after the family insertion. -/
theorem Checked.WF.identityCtorWF
    {source : VInductDecl} {checked : source.Checked}
    {pre envT : VEnv} (hpre : pre.Ordered)
    (h : checked.WF pre)
    (hadd : pre.addConst checked.type.name
      checked.type.toVConstant = some envT)
    {ctor : NormalizedCtor}
    (hctor : ctor ∈
      checked.identityGeneration.block.ctorPairs) :
    ctor.WF checked.identityGeneration.block envT := by
  obtain ⟨c, hc, rfl⟩ :=
    checked.identityGeneration_ctor hctor
  let S := h.toDirectFamilyEnv hpre hadd
  have hcAn := checked.direct_anatomy.2.2.2.2.2 c hc
  have hfields : fieldsWF source.uvars checked.type.name
      source.nparams envT checked.resultLevel
      (ctorFields (VExpr.dropN source.nparams checked.type.type))
      (VExpr.telN source.nparams checked.type.type).reverse 0
      (ctorFields (VExpr.dropN source.nparams c.type)) := by
    simpa [checked.params_eq, checked.indices_eq] using
      fieldsWF_mono (addConst_le hadd) (h.2 c hc).1
  have hfieldTel : OnTel envT source.uvars
      (VExpr.telN source.nparams checked.type.type).reverse
      (ctorFields (VExpr.dropN source.nparams c.type)) :=
    S.fieldsWF_onTel_decl _ [] 0 rfl hfields
  have hbinders : OnTel envT source.uvars []
      (VExpr.telN source.nparams checked.type.type ++
        ctorFields (VExpr.dropN source.nparams c.type)) :=
    S.hparams.of_append.1.append (by simpa using hfieldTel)
  have htelRefl := hbinders.telDefEq_refl
  have hresultSpine : envT.SpineWF source.uvars
      ((ctorFields
          (VExpr.dropN source.nparams c.type)).reverse ++
        (VExpr.telN source.nparams checked.type.type).reverse)
      (VExpr.forallN
        (VExpr.liftTelN
          (ctorFields
            (VExpr.dropN source.nparams c.type)).length
          (ctorFields
            (VExpr.dropN source.nparams checked.type.type)) 0)
        (.sort checked.resultLevel))
      (recFieldIdxs source.nparams
        (VExpr.resultOf
          (VExpr.dropN source.nparams c.type)))
      (.sort checked.resultLevel) := by
    simpa [checked.params_eq, checked.indices_eq] using
      (h.2 c hc).2.mono (addConst_le hadd)
  have hresultTyped :=
    S.ctorResult_hasType_decl hresultSpine
  have hrawResult :
      VExpr.resultOf (VExpr.dropN source.nparams c.type) =
        VExpr.appN
          (.const checked.type.name
            (VLevel.params source.uvars))
          (VExpr.bvarRevRange
            (ctorFields
              (VExpr.dropN source.nparams c.type)).length
            source.nparams ++
            recFieldIdxs source.nparams
              (VExpr.resultOf
                (VExpr.dropN source.nparams c.type))) := by
    have hout := congrArg VExpr.resultOf
      (stage3Ctor_eq hcAn.2.2).1
    rw [VExpr.resultOf_forallN,
      VExpr.resultOf_appN_const] at hout
    simpa only [Nat.zero_add] using hout
  have hresultDF : envT.IsDefEq source.uvars
      ((ctorFields
          (VExpr.dropN source.nparams c.type)).reverse ++
        (VExpr.telN source.nparams checked.type.type).reverse)
      (VExpr.resultOf (VExpr.dropN source.nparams c.type))
      (VExpr.appN
        (.const checked.type.name
          (VLevel.params source.uvars))
        (VExpr.bvarRevRange
          (ctorFields
            (VExpr.dropN source.nparams c.type)).length
          source.nparams ++
          recFieldIdxs source.nparams
            (VExpr.resultOf
              (VExpr.dropN source.nparams c.type))))
      (.sort checked.resultLevel) := by
    exact Eq.mpr
      (congrArg
        (fun e => envT.IsDefEq source.uvars
          ((ctorFields
              (VExpr.dropN source.nparams c.type)).reverse ++
            (VExpr.telN source.nparams
              checked.type.type).reverse)
          e
          (VExpr.appN
            (.const checked.type.name
              (VLevel.params source.uvars))
            (VExpr.bvarRevRange
              (ctorFields
                (VExpr.dropN source.nparams c.type)).length
              source.nparams ++
              recFieldIdxs source.nparams
                (VExpr.resultOf
                  (VExpr.dropN source.nparams c.type))))
          (.sort checked.resultLevel))
        hrawResult)
      hresultTyped
  constructor
  · simpa [NormalizedCtor.declaredBinders,
      NormalizedCtor.rawFields,
      NormalizedCtor.viewBinders, CheckedCtor.ofDirect,
      checked.params_eq, hcAn.2.1] using htelRefl
  · simpa [NormalizedCtor.declaredBinders,
      NormalizedCtor.rawFields, NormalizedCtor.rawResult,
      NormalizedCtor.resultTarget, CheckedCtor.ofDirect,
      checked.params_eq, hcAn.2.1] using hresultDF
  · simpa [NormalizedCtor.emittedBinders,
      NormalizedCtor.rawFields,
      NormalizedCtor.viewBinders, CheckedCtor.ofDirect,
      checked.params_eq] using htelRefl
  · simpa [NormalizedCtor.emittedBinders,
      NormalizedCtor.rawFields, NormalizedCtor.rawResult,
      NormalizedCtor.resultTarget, CheckedCtor.ofDirect,
      checked.params_eq] using hresultDF

omit S in
/-- Every semantically checked direct declaration admits the identity mixed
generation certificate. This is the public bridge from the legacy checker
contract to the normalized transaction. -/
theorem Checked.WF.identityGeneration
    {source : VInductDecl} {checked : source.Checked}
    {env : VEnv} (h : checked.WF env) (henv : env.Ordered) :
    checked.identityGeneration.WF env := by
  have hfamily := h.family_isType
  have hnorm : checked.identityGeneration.block.normalization.WF env := by
    refine ⟨checked.type, checked.type, checked.types_eq, ?_, ?_, ?_⟩
    · simpa only [Checked.identityGeneration, Checked.identityBlock,
        Normalization.identity] using checked.types_eq
    · obtain ⟨u, hu⟩ := hfamily
      exact ⟨.sort u, hu⟩
    · intro envT hadd
      have hadd' : env.addConst checked.type.name
          checked.type.toVConstant = some envT := by
        simpa only [Checked.identityGeneration,
          Checked.identityBlock] using hadd
      have hall : ∀ c ∈ checked.type.ctors,
          envT.IsDefEqU source.uvars [] c.type c.type := by
        intro c hc
        have hpair :
            (⟨c, CheckedCtor.ofDirect source.uvars
              checked.type.name source.nparams
              checked.indices.length c⟩ : NormalizedCtor) ∈
              checked.identityGeneration.block.ctorPairs := by
          simpa only [Checked.identityGeneration,
            Checked.identityBlock, NormalizedChecked.ctorPairs,
            checked.constructors_eq] using
              (pairNormalizedCtors_map_self_contains hc :
                (⟨c, CheckedCtor.ofDirect source.uvars
                  checked.type.name source.nparams
                  checked.indices.length c⟩ :
                  NormalizedCtor) ∈
                    pairNormalizedCtors checked.type.ctors
                      (checked.type.ctors.map
                        (CheckedCtor.ofDirect source.uvars
                          checked.type.name source.nparams
                          checked.indices.length)))
        obtain ⟨u, hu⟩ :=
          (h.identityCtorWF henv hadd' hpair).rawDeclared_isType
        exact ⟨.sort u, hu⟩
      have hrel : List.Forall₂
          (fun c c' => envT.IsDefEqU source.uvars []
            c.type c'.type)
          checked.type.ctors checked.type.ctors := by
        let R : VConstVal → VConstVal → Prop :=
          fun c c' => envT.IsDefEqU source.uvars []
            c.type c'.type
        let rec diagonal :
            ∀ cs : List VConstVal,
              (∀ c ∈ cs, R c c) →
              List.Forall₂ R cs cs
          | [], _ => .nil
          | c :: cs, hs =>
              .cons (hs c (.head _))
                (diagonal cs fun c hc => hs c (.tail _ hc))
        exact diagonal checked.type.ctors hall
      simpa only [Checked.identityGeneration,
        Checked.identityBlock, Normalization.identity] using hrel
  refine {
    blockWF := ⟨hnorm, h⟩
    familyTel := ?_
    familyResult := ?_
    ctors := ?_
  }
  · simpa only [Checked.identityGeneration,
      Checked.identityBlock, NormalizedChecked.rawParams,
      NormalizedChecked.rawIndices, checked.params_eq,
      checked.indices_eq] using h.1.telDefEq_refl
  · simpa only [Checked.identityGeneration,
      Checked.identityBlock, NormalizedChecked.rawParams,
      NormalizedChecked.rawIndices, NormalizedChecked.rawResult,
      checked.params_eq, checked.indices_eq,
      checked.result_eq] using
        (VEnv.IsDefEq.sortDF
          checked.direct_anatomy.2.2.1
          checked.direct_anatomy.2.2.1 rfl :
          env.IsDefEq source.uvars
            (checked.params ++ checked.indices).reverse
            (.sort checked.resultLevel)
            (.sort checked.resultLevel)
            (.sort (.succ checked.resultLevel)))
  · intro envT hadd ctor hctor
    have hadd' : env.addConst checked.type.name
        checked.type.toVConstant = some envT := by
      simpa only [Checked.identityGeneration,
        Checked.identityBlock] using hadd
    exact h.identityCtorWF henv hadd' hctor

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

/-- Every rule emitted from the paired constructor list is well formed in the
environment containing the mixed recursor. -/
theorem GenerationEnv.generatedRules_WF
    {source : VInductDecl}
    {gen : GenerationChecked source} {env : VEnv}
    (S : GenerationEnv gen env)
    (hrec : env.constants
      (.str gen.block.sourceType.name "rec") =
        some gen.recursor) :
    ∀ df ∈ gen.generatedRules, df.WF env := by
  intro df hdf
  change df ∈
    gen.block.ctorPairs.zipIdx.map
      (fun (ctor, i) => gen.rule i ctor) at hdf
  obtain ⟨⟨ctor, i⟩, hmem, rfl⟩ :=
    List.mem_map.1 hdf
  obtain ⟨-, hci⟩ :=
    List.mem_zipIdx_getElem? hmem
  rw [Nat.sub_zero] at hci
  exact S.rule_WF hci hrec

/-- Folding all mixed generated rules preserves environment ordering. -/
theorem GenerationEnv.generatedRulesFold_ordered
    {source : VInductDecl}
    {gen : GenerationChecked source} {env : VEnv}
    (S : GenerationEnv gen env)
    (hrec : env.constants
      (.str gen.block.sourceType.name "rec") =
        some gen.recursor) :
    (gen.generatedRules.foldl
      VEnv.addDefEq env).Ordered :=
  rulesFold_WF gen.generatedRules S.ord
    (S.generatedRules_WF hrec)

/-- Folding definitional equations only grows the environment and registers
every equation in the input list. -/
theorem rulesFold_spec : ∀ (dfs : List VDefEq) (env : VEnv),
    env ≤ dfs.foldl VEnv.addDefEq env ∧
      ∀ df ∈ dfs, (dfs.foldl VEnv.addDefEq env).defeqs df
  | [], _ => ⟨.rfl, nofun⟩
  | df :: dfs, env => by
    rw [List.foldl_cons]
    obtain ⟨hle, hmem⟩ := rulesFold_spec dfs (env.addDefEq df)
    refine ⟨VEnv.addDefEq_le.trans hle, fun df' hdf' => ?_⟩
    rcases List.mem_cons.1 hdf' with rfl | hdf'
    · exact hle.defeqs VEnv.addDefEq_self
    · exact hmem df' hdf'

/-- A successful constructor fold grows the environment, registers every
constructor, and certifies that every constructor name was fresh in the
fold's input environment. -/
theorem ctorFold_spec : ∀ (cs : List VConstVal) {env₀ env₁ : VEnv},
    List.foldlM (fun env (c : VConstVal) => env.addConst c.name c.toVConstant) env₀ cs =
      some env₁ →
    env₀ ≤ env₁ ∧
      (∀ c ∈ cs, env₁.constants c.name = some c.toVConstant) ∧
      ∀ c ∈ cs, env₀.constants c.name = none
  | [], _, _, hfold => by
    cases hfold
    exact ⟨.rfl, nofun, nofun⟩
  | c :: cs, env₀, env₁, hfold => by
    rw [List.foldlM_cons] at hfold
    obtain ⟨env₀', hadd, hrest⟩ := Option.bind_eq_some_iff.1 hfold
    obtain ⟨hle, hlook, hfresh⟩ := ctorFold_spec cs hrest
    have haddLe := VEnv.addConst_le hadd
    refine ⟨haddLe.trans hle, ?_, ?_⟩
    · intro c' hc'
      rcases List.mem_cons.1 hc' with rfl | hc'
      · exact hle.constants (VEnv.addConst_self hadd)
      · exact hlook c' hc'
    · intro c' hc'
      rcases List.mem_cons.1 hc' with rfl | hc'
      · exact VEnv.addConst_fresh hadd
      · exact haddLe.constants_none (hfresh c' hc')

/-- Sequentially inserting constants that are all well formed in the fold's
initial environment preserves ordering. Monotonicity transports the remaining
constant certificates after each insertion. -/
theorem constFold_ordered : ∀ (cs : List VConstVal) {env₀ env₁ : VEnv},
    env₀.Ordered →
    (∀ c ∈ cs, c.toVConstant.WF env₀) →
    List.foldlM
      (fun env (c : VConstVal) => env.addConst c.name c.toVConstant)
      env₀ cs = some env₁ →
    env₁.Ordered
  | [], _, _, ord, _, hfold => by
    cases hfold
    exact ord
  | c :: cs, env₀, env₁, ord, hwf, hfold => by
    rw [List.foldlM_cons] at hfold
    obtain ⟨env₀', hadd, hrest⟩ := Option.bind_eq_some_iff.1 hfold
    have hle := VEnv.addConst_le hadd
    have ord' : env₀'.Ordered :=
      .const ord (hwf c (.head _)) hadd
    exact constFold_ordered cs ord'
      (fun c' hc' => (hwf c' (.tail _ hc')).mono hle) hrest

/-- Adding the constructors of a stage-3 block preserves order and records
their lookups. -/
theorem ctorFold_WF {U : Nat} {T : Name} {np : Nat} {l : VLevel} {ty : VInductiveType}
    (hsort : VExpr.resultOf (VExpr.dropN np ty.type) = .sort l)
    (hlen : (VExpr.telN np ty.type).length = np) (hl : l.WF U) :
    ∀ (cs' : List VConstVal) {env₀ env₁ : VEnv},
    env₀.Ordered → env₀.constants T = some ⟨U, ty.type⟩ →
    VEnv.OnTel env₀ U []
      (VExpr.telN np ty.type ++ ctorFields (VExpr.dropN np ty.type)) →
    (∀ c ∈ cs', c.uvars = U ∧ VExpr.telN np c.type = VExpr.telN np ty.type ∧
      stage3Ctor U T np (ctorFields (VExpr.dropN np ty.type)).length 0
        (VExpr.dropN np c.type) ∧
      fieldsWF U T np env₀ l (ctorFields (VExpr.dropN np ty.type))
        (VExpr.telN np ty.type).reverse 0 (ctorFields (VExpr.dropN np c.type)) ∧
      env₀.SpineWF U
        ((ctorFields (VExpr.dropN np c.type)).reverse ++
          (VExpr.telN np ty.type).reverse)
        (VExpr.forallN (VExpr.liftTelN
          (ctorFields (VExpr.dropN np c.type)).length
          (ctorFields (VExpr.dropN np ty.type)) 0) (.sort l))
        (recFieldIdxs np (VExpr.resultOf (VExpr.dropN np c.type))) (.sort l)) →
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
    obtain ⟨hcU, htelc, hs3c, hfc, hresultc⟩ := hcs c (.head _)
    have S₀ : Stage3Env env₀ U T np l ⟨⟨⟨ty.uvars, ty.type⟩, ty.name⟩, []⟩ :=
      ⟨ord, hl, hsort, hlen, hT, nofun, nofun, nofun, hpar, nofun, nofun⟩
    have hwfc : c.toVConstant.WF env₀ := by
      show env₀.IsType c.toVConstant.uvars [] c.toVConstant.type
      rw [show c.toVConstant.uvars = c.uvars from rfl, hcU]
      exact S₀.ctorType_isType' htelc hs3c hfc hresultc
    have ord' : env₀'.Ordered := .const ord hwfc hadd
    have hle' := VEnv.addConst_le hadd
    obtain ⟨ord₁, hle₁, hlook⟩ := ctorFold_WF hsort hlen hl cs' ord'
      (hle'.constants hT) (hpar.mono hle')
      (fun c' hc' => by
        obtain ⟨h1, h2, h3, h4, h5⟩ := hcs c' (.tail _ hc')
        exact ⟨h1, h2, h3, fieldsWF_mono hle' h4, h5.mono hle'⟩)
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

/-- Recover the exact intermediate environments from a successful normalized
generation transaction. The data-bearing trace is wrapped in `Nonempty` so
proof consumers can eliminate it without adding a choice axiom merely to
recover bookkeeping states. -/
theorem addInductGeneration_trace {source : VInductDecl}
    {gen : source.GenerationChecked}
    (hadd : addInductGeneration env gen = some env') :
    Nonempty (AddInductGenerationTrace env env' gen) := by
  unfold addInductGeneration at hadd
  obtain ⟨typeEnv, addType, hadd⟩ := Option.bind_eq_some_iff.1 hadd
  obtain ⟨ctorEnv, addCtors, hadd⟩ := Option.bind_eq_some_iff.1 hadd
  obtain ⟨recEnv, addRec, hadd⟩ := Option.bind_eq_some_iff.1 hadd
  cases hadd
  exact ⟨⟨typeEnv, ctorEnv, recEnv, addType, addCtors, addRec, rfl⟩⟩

/-- The normalized core is atomic: failure returns no observable intermediate
environment, while success exposes one complete trace. -/
theorem addInductGeneration_atomic {source : VInductDecl}
    (env : VEnv) (gen : source.GenerationChecked) :
    addInductGeneration env gen = none ∨
      ∃ env', addInductGeneration env gen = some env' ∧
        Nonempty (AddInductGenerationTrace env env' gen) := by
  cases hadd : addInductGeneration env gen with
  | none => exact .inl rfl
  | some env' =>
    exact .inr ⟨env', rfl, addInductGeneration_trace hadd⟩

/-- A successful normalized generation transaction only grows its input
environment. -/
theorem AddInductGenerationTrace.le {source : VInductDecl}
    {gen : source.GenerationChecked}
    (H : AddInductGenerationTrace env env' gen) : env ≤ env' := by
  have htype := addConst_le H.addType
  have hctors := (ctorFold_spec gen.block.sourceType.ctors H.addCtors).1
  have hrec := addConst_le H.addRec
  have hrules : H.recEnv ≤ env' := by
    simpa only [H.addRules] using
      (rulesFold_spec gen.generatedRules H.recEnv).1
  exact htype.trans (hctors.trans (hrec.trans hrules))

/-- The raw family name was fresh before a successful normalized
transaction. -/
theorem AddInductGenerationTrace.family_fresh {source : VInductDecl}
    {gen : source.GenerationChecked}
    (H : AddInductGenerationTrace env env' gen) :
    env.constants gen.block.sourceType.name = none :=
  addConst_fresh H.addType

/-- The final environment contains the exact raw family constant. -/
theorem AddInductGenerationTrace.family_lookup {source : VInductDecl}
    {gen : source.GenerationChecked}
    (H : AddInductGenerationTrace env env' gen) :
    env'.constants gen.block.sourceType.name =
      some gen.block.sourceType.toVConstant := by
  have hctors := (ctorFold_spec gen.block.sourceType.ctors H.addCtors).1
  have hrec := addConst_le H.addRec
  have hrules : H.recEnv ≤ env' := by
    simpa only [H.addRules] using
      (rulesFold_spec gen.generatedRules H.recEnv).1
  exact (hctors.trans (hrec.trans hrules)).constants
    (addConst_self H.addType)

/-- Every raw constructor name was fresh in the transaction's input
environment. -/
theorem AddInductGenerationTrace.ctor_fresh {source : VInductDecl}
    {gen : source.GenerationChecked}
    (H : AddInductGenerationTrace env env' gen)
    {ctor : VConstVal} (hctor : ctor ∈ gen.block.sourceType.ctors) :
    env.constants ctor.name = none := by
  have htype := addConst_le H.addType
  have hfresh :=
    (ctorFold_spec gen.block.sourceType.ctors H.addCtors).2.2 ctor hctor
  exact htype.constants_none hfresh

/-- The final environment contains every exact raw constructor constant. -/
theorem AddInductGenerationTrace.ctor_lookup {source : VInductDecl}
    {gen : source.GenerationChecked}
    (H : AddInductGenerationTrace env env' gen)
    {ctor : VConstVal} (hctor : ctor ∈ gen.block.sourceType.ctors) :
    env'.constants ctor.name = some ctor.toVConstant := by
  have hlookup :=
    (ctorFold_spec gen.block.sourceType.ctors H.addCtors).2.1 ctor hctor
  have hrec := addConst_le H.addRec
  have hrules : H.recEnv ≤ env' := by
    simpa only [H.addRules] using
      (rulesFold_spec gen.generatedRules H.recEnv).1
  exact (hrec.trans hrules).constants hlookup

/-- The generated recursor name was fresh before a successful normalized
transaction. -/
theorem AddInductGenerationTrace.rec_fresh {source : VInductDecl}
    {gen : source.GenerationChecked}
    (H : AddInductGenerationTrace env env' gen) :
    env.constants (.str gen.block.sourceType.name "rec") = none := by
  have htype := addConst_le H.addType
  have hctors := (ctorFold_spec gen.block.sourceType.ctors H.addCtors).1
  exact (htype.trans hctors).constants_none (addConst_fresh H.addRec)

/-- The final environment contains the exact mixed generated recursor. -/
theorem AddInductGenerationTrace.rec_lookup {source : VInductDecl}
    {gen : source.GenerationChecked}
    (H : AddInductGenerationTrace env env' gen) :
    env'.constants (.str gen.block.sourceType.name "rec") =
      some gen.recursor := by
  have hrules : H.recEnv ≤ env' := by
    simpa only [H.addRules] using
      (rulesFold_spec gen.generatedRules H.recEnv).1
  exact hrules.constants (addConst_self H.addRec)

/-- The final environment registers every mixed generated iota rule. -/
theorem AddInductGenerationTrace.rule_mem {source : VInductDecl}
    {gen : source.GenerationChecked}
    (H : AddInductGenerationTrace env env' gen)
    {df : VDefEq} (hdf : df ∈ gen.generatedRules) :
    env'.defeqs df := by
  simpa only [H.addRules] using
    (rulesFold_spec gen.generatedRules H.recEnv).2 df hdf

/-- The normalized transaction preserves environment ordering from the
semantic raw/view generation certificate. Stored constants are checked in
their exact raw syntax; the mixed recursor and rules are checked only after
all raw constants are present. -/
theorem addInductGeneration_WF {source : VInductDecl}
    {gen : source.GenerationChecked}
    (henv : env.Ordered) (hgen : gen.WF env)
    (hadd : addInductGeneration env gen = some env') :
    env'.Ordered := by
  rcases addInductGeneration_trace hadd with ⟨H⟩
  have hfamilyWF : gen.block.sourceType.toVConstant.WF env := by
    show env.IsType gen.block.sourceType.uvars []
      gen.block.sourceType.type
    rw [gen.block.sourceType_uvars_eq]
    exact hgen.rawFamily_isType
  have ordT : H.typeEnv.Ordered :=
    .const henv hfamilyWF H.addType
  have hctorWF :
      ∀ c ∈ gen.block.sourceType.ctors,
        c.toVConstant.WF H.typeEnv := by
    intro c hc
    have hc' : c ∈ gen.block.ctorPairs.map (·.raw) := by
      rw [gen.rawCtors_eq]
      exact hc
    obtain ⟨ctor, hctor, rfl⟩ := List.mem_map.1 hc'
    show H.typeEnv.IsType ctor.raw.uvars [] ctor.raw.type
    rw [gen.ctor_uvars_eq hctor]
    exact hgen.rawCtor_isType H.addType hctor
  have ordC : H.ctorEnv.Ordered :=
    constFold_ordered gen.block.sourceType.ctors ordT hctorWF H.addCtors
  obtain ⟨hleTC, hctorLookup, -⟩ :=
    ctorFold_spec gen.block.sourceType.ctors H.addCtors
  have hlePreT := addConst_le H.addType
  have hlePreC := hlePreT.trans hleTC
  have hfamily :
      H.ctorEnv.constants gen.block.sourceType.name =
        some gen.block.sourceType.toVConstant :=
    hleTC.constants (addConst_self H.addType)
  have hctors :
      ∀ ctor ∈ gen.block.ctorPairs,
        H.ctorEnv.constants ctor.raw.name =
          some ctor.raw.toVConstant := by
    intro ctor hctor
    apply hctorLookup ctor.raw
    rw [← gen.rawCtors_eq]
    exact List.mem_map.2 ⟨ctor, hctor, rfl⟩
  have S : GenerationEnv gen H.ctorEnv :=
    hgen.toGenerationEnv H.addType hlePreC hleTC ordC hfamily hctors
  have ordR : H.recEnv.Ordered :=
    .const ordC S.recursor_wf H.addRec
  have hleCR := addConst_le H.addRec
  have SR : GenerationEnv gen H.recEnv :=
    S.mono hleCR ordR
  have hout :=
    SR.generatedRulesFold_ordered (addConst_self H.addRec)
  simpa only [H.addRules] using hout

/-- Recover the ordinary normalized transaction trace from the
proof-carrying public entry point.  The conclusion contains only Theory data;
the producer that established the certificate is deliberately absent. -/
theorem addInductCertified_trace {source : VInductDecl}
    {certificate : source.GenerationCertificate env}
    (hadd : addInductCertified env certificate = some env') :
    Nonempty
      (AddInductGenerationTrace env env' certificate.generation) := by
  apply addInductGeneration_trace
  simpa only [addInductCertified_eq_addInductGeneration] using hadd

/-- The proof-carrying wrapper has the same atomic success/failure behavior as
the underlying normalized transaction. -/
theorem addInductCertified_atomic {source : VInductDecl}
    (env : VEnv) (certificate : source.GenerationCertificate env) :
    addInductCertified env certificate = none ∨
      ∃ env', addInductCertified env certificate = some env' ∧
        Nonempty
          (AddInductGenerationTrace env env' certificate.generation) := by
  simpa only [addInductCertified_eq_addInductGeneration] using
    addInductGeneration_atomic env certificate.generation

/-- Ordering preservation for the public certified transaction.  Its
semantic premise is carried by the certificate rather than repeated at every
call site. -/
theorem addInductCertified_WF {source : VInductDecl}
    {certificate : source.GenerationCertificate env}
    (henv : env.Ordered)
    (hadd : addInductCertified env certificate = some env') :
    env'.Ordered := by
  apply addInductGeneration_WF henv certificate.wf
  simpa only [addInductCertified_eq_addInductGeneration] using hadd

/--
info: 'Lean4Lean.VEnv.addInductGeneration_trace' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms addInductGeneration_trace

/--
info: 'Lean4Lean.VEnv.addInductGeneration_atomic' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms addInductGeneration_atomic

/--
info: 'Lean4Lean.VEnv.AddInductGenerationTrace.le' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms AddInductGenerationTrace.le

/--
info: 'Lean4Lean.VEnv.AddInductGenerationTrace.family_lookup' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms AddInductGenerationTrace.family_lookup

/--
info: 'Lean4Lean.VEnv.AddInductGenerationTrace.ctor_lookup' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms AddInductGenerationTrace.ctor_lookup

/--
info: 'Lean4Lean.VEnv.AddInductGenerationTrace.rec_lookup' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms AddInductGenerationTrace.rec_lookup

/--
info: 'Lean4Lean.VEnv.AddInductGenerationTrace.rule_mem' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms AddInductGenerationTrace.rule_mem

/--
info: 'Lean4Lean.VEnv.addInductGeneration_WF' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms addInductGeneration_WF

/--
info: 'Lean4Lean.VEnv.addInductCertified_eq_addInductGeneration' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms addInductCertified_eq_addInductGeneration

/--
info: 'Lean4Lean.VEnv.addInductCertified_trace' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms addInductCertified_trace

/--
info: 'Lean4Lean.VEnv.addInductCertified_atomic' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms addInductCertified_atomic

/--
info: 'Lean4Lean.VEnv.addInductCertified_WF' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms addInductCertified_WF

/--
info: 'Lean4Lean.VEnv.addInduct_eq_addInductGeneration' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms addInduct_eq_addInductGeneration

/-- Elimination of a successful `addInduct` transaction into its stable
consumer-facing postcondition. -/
theorem addInduct_success (hadd : addInduct env decl = some env') :
    AddInductSuccess env env' decl := by
  unfold addInduct at hadd
  obtain ⟨checked, hchecked, hgen⟩ :=
    Option.bind_eq_some_iff.1 hadd
  rcases addInductGeneration_trace hgen with ⟨H⟩
  refine {
    checked := ⟨checked, hchecked⟩
    accepted := by simp [stage3, hchecked]
    singleton := ⟨checked.type, checked.types_eq⟩
    le := H.le
    type_fresh := ?_
    type_lookup := ?_
    ctor_fresh := ?_
    ctor_lookup := ?_
    rec_fresh := ?_
    rec_lookup := ?_
    rule_mem := ?_
  }
  · intro ty hty
    rw [checked.types_eq] at hty
    obtain rfl := List.mem_singleton.1 hty
    exact H.family_fresh
  · intro ty hty
    rw [checked.types_eq] at hty
    obtain rfl := List.mem_singleton.1 hty
    exact H.family_lookup
  · intro ty hty c hc
    rw [checked.types_eq] at hty
    obtain rfl := List.mem_singleton.1 hty
    exact H.ctor_fresh hc
  · intro ty hty c hc
    rw [checked.types_eq] at hty
    obtain rfl := List.mem_singleton.1 hty
    exact H.ctor_lookup hc
  · intro ty hty
    rw [checked.types_eq] at hty
    obtain rfl := List.mem_singleton.1 hty
    exact H.rec_fresh
  · intro ty hty
    rw [checked.types_eq] at hty
    obtain rfl := List.mem_singleton.1 hty
    have hout := H.rec_lookup
    change env'.constants (.str checked.type.name "rec") =
      some checked.recursor at hout
    rw [checked.recursor_eq_legacy] at hout
    exact hout
  · intro ty hty df hdf
    rw [checked.types_eq] at hty
    obtain rfl := List.mem_singleton.1 hty
    apply H.rule_mem
    change df ∈ checked.generatedRules
    rw [checked.generatedRules_eq_legacy]
    exact hdf

/-- Successful inductive addition is monotone. -/
theorem addInduct_le (hadd : addInduct env decl = some env') : env ≤ env' :=
  (addInduct_success hadd).le

/-- Successful environment extension exposes the exact checked descriptor that
drove generation, so consumers never need to re-run acceptance analysis. -/
theorem addInduct_checked (hadd : addInduct env decl = some env') :
    ∃ checked, decl.checked? = some checked :=
  (addInduct_success hadd).checked

theorem addInduct_type_fresh (hadd : addInduct env decl = some env')
    (hty : ty ∈ decl.types) : env.constants ty.name = none :=
  (addInduct_success hadd).type_fresh ty hty

theorem addInduct_type_lookup (hadd : addInduct env decl = some env')
    (hty : ty ∈ decl.types) : env'.constants ty.name = some ty.toVConstant :=
  (addInduct_success hadd).type_lookup ty hty

theorem addInduct_ctor_fresh (hadd : addInduct env decl = some env')
    (hty : ty ∈ decl.types) (hc : c ∈ ty.ctors) : env.constants c.name = none :=
  (addInduct_success hadd).ctor_fresh ty hty c hc

theorem addInduct_ctor_lookup (hadd : addInduct env decl = some env')
    (hty : ty ∈ decl.types) (hc : c ∈ ty.ctors) :
    env'.constants c.name = some c.toVConstant :=
  (addInduct_success hadd).ctor_lookup ty hty c hc

theorem addInduct_rec_fresh (hadd : addInduct env decl = some env')
    (hty : ty ∈ decl.types) : env.constants (.str ty.name "rec") = none :=
  (addInduct_success hadd).rec_fresh ty hty

theorem addInduct_rec_lookup (hadd : addInduct env decl = some env')
    (hty : ty ∈ decl.types) :
    env'.constants (.str ty.name "rec") =
      some (recConstRec decl.uvars ty.name decl.nparams ty) :=
  (addInduct_success hadd).rec_lookup ty hty

theorem addInduct_rule_mem (hadd : addInduct env decl = some env')
    (hty : ty ∈ decl.types) (hdf : df ∈ rulesRec decl.uvars ty.name decl.nparams ty) :
    env'.defeqs df :=
  (addInduct_success hadd).rule_mem ty hty df hdf

/-- `addInduct` is an all-or-nothing transaction: every evaluation either
returns no environment or returns an environment satisfying the complete
success contract. -/
theorem addInduct_atomic :
    addInduct env decl = none ∨
      ∃ env', addInduct env decl = some env' ∧ AddInductSuccess env env' decl := by
  cases hadd : addInduct env decl with
  | none => exact .inl rfl
  | some env' => exact .inr ⟨env', rfl, addInduct_success hadd⟩

/-- The Stage-3 guard is an exact early-rejection condition. -/
theorem addInduct_eq_none_of_stage3_false (h : decl.stage3 = false) :
    addInduct env decl = none := by
  have hchecked : decl.checked? = none := checked?_eq_none_iff.2 h
  simp [addInduct, hchecked]

/-- A pre-existing type name rejects the transaction before any generated
object is observable. -/
theorem addInduct_eq_none_of_type_present (htypes : decl.types = [ty])
    (hcontains : env.contains ty.name) : addInduct env decl = none := by
  obtain ⟨ci, hci⟩ := hcontains
  cases hstage : decl.stage3 with
  | false => exact addInduct_eq_none_of_stage3_false hstage
  | true =>
    obtain ⟨checked, hchecked⟩ := exists_checked_of_stage3 hstage
    have htype : checked.type = ty := by
      simpa using checked.types_eq.symm.trans htypes
    unfold addInduct
    rw [hchecked]
    simp [addInductGeneration, Checked.identityGeneration,
      Checked.identityBlock, htype, VEnv.addConst, hci]

/-- A pre-existing constructor name rejects the complete transaction. The
proof is stated through the stable success certificate, not the position of
the constructor in the internal `foldlM`. -/
theorem addInduct_eq_none_of_ctor_present (htypes : decl.types = [ty])
    (hctor : ctor ∈ ty.ctors) (hcontains : env.contains ctor.name) :
    addInduct env decl = none := by
  cases hadd : addInduct env decl with
  | none => rfl
  | some env' =>
    have hty : ty ∈ decl.types := by rw [htypes]; exact .head _
    have hfresh := (addInduct_success hadd).ctor_fresh ty hty ctor hctor
    obtain ⟨ci, hci⟩ := hcontains
    rw [hci] at hfresh
    contradiction

/-- A pre-existing generated recursor name likewise rejects the complete
transaction. -/
theorem addInduct_eq_none_of_rec_present (htypes : decl.types = [ty])
    (hcontains : env.contains (.str ty.name "rec")) : addInduct env decl = none := by
  cases hadd : addInduct env decl with
  | none => rfl
  | some env' =>
    have hty : ty ∈ decl.types := by rw [htypes]; exact .head _
    have hfresh := (addInduct_success hadd).rec_fresh ty hty
    obtain ⟨ci, hci⟩ := hcontains
    rw [hci] at hfresh
    contradiction

theorem addInduct_WF (henv : Ordered env) (hdecl : decl.WF env)
    (henv' : addInduct env decl = some env') : Ordered env' := by
  unfold addInduct at henv'
  obtain ⟨checked, -, hadd⟩ :=
    Option.bind_eq_some_iff.1 henv'
  exact addInductGeneration_WF henv
    ((checked.wf_of_decl hdecl).identityGeneration henv) hadd

end VEnv

/- Mixed raw/view generation must stay within Lean's standard logical
baseline. Guard each proof-critical boundary separately so a dependency change
identifies the first affected layer. -/
/--
info: 'Lean4Lean.VInductDecl.Checked.WF.identityGeneration' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VInductDecl.Checked.WF.identityGeneration

/--
info: 'Lean4Lean.VInductDecl.GenerationEnv.minor_isType' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VInductDecl.GenerationEnv.minor_isType

/--
info: 'Lean4Lean.VInductDecl.GenerationEnv.minorTypes_onTel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VInductDecl.GenerationEnv.minorTypes_onTel

/--
info: 'Lean4Lean.VInductDecl.GenerationEnv.familyApp_transport' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms VInductDecl.GenerationEnv.familyApp_transport

/--
info: 'Lean4Lean.VInductDecl.GenerationEnv.recType_isType' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VInductDecl.GenerationEnv.recType_isType

/--
info: 'Lean4Lean.VInductDecl.GenerationEnv.recursor_wf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VInductDecl.GenerationEnv.recursor_wf

/--
info: 'Lean4Lean.VInductDecl.GenerationEnv.ruleCall_hasType' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VInductDecl.GenerationEnv.ruleCall_hasType

/--
info: 'Lean4Lean.VInductDecl.GenerationEnv.rule_WF' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VInductDecl.GenerationEnv.rule_WF

/--
info: 'Lean4Lean.VInductDecl.GenerationEnv.generatedRules_WF' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VInductDecl.GenerationEnv.generatedRules_WF

/--
info: 'Lean4Lean.VInductDecl.GenerationEnv.generatedRulesFold_ordered' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms VInductDecl.GenerationEnv.generatedRulesFold_ordered

/- The generalized recursive-Pi artifact path must remain within the same
standard logical baseline as the public preservation theorem. These guards
make every proof-critical boundary independently auditable. -/
/--
info: 'Lean4Lean.VInductDecl.Stage3Env.recTypeRec_isType' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VInductDecl.Stage3Env.recTypeRec_isType

/--
info: 'Lean4Lean.VInductDecl.Stage3Env.recConstRec_wf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VInductDecl.Stage3Env.recConstRec_wf

/--
info: 'Lean4Lean.VInductDecl.Stage3Env.ruleCallRec_hasType' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VInductDecl.Stage3Env.ruleCallRec_hasType

/--
info: 'Lean4Lean.VInductDecl.Stage3Env.minorAppRec_hasType' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VInductDecl.Stage3Env.minorAppRec_hasType

/--
info: 'Lean4Lean.VInductDecl.Stage3Env.recRuleAppRec_hasType' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VInductDecl.Stage3Env.recRuleAppRec_hasType

/--
info: 'Lean4Lean.VInductDecl.Stage3Env.ruleRec_WF' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VInductDecl.Stage3Env.ruleRec_WF

/- The indexed-inductive preservation proof stays within Lean's standard
logical axiom baseline. Keep this guard adjacent to the theorem so a new
dependency fails during ordinary module compilation. -/
/--
info: 'Lean4Lean.VEnv.addInduct_success' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VEnv.addInduct_success

/--
info: 'Lean4Lean.VEnv.addInduct_checked' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VEnv.addInduct_checked

/--
info: 'Lean4Lean.VEnv.addInduct_eq_none_of_ctor_present' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VEnv.addInduct_eq_none_of_ctor_present

/--
info: 'Lean4Lean.VEnv.addInduct_eq_none_of_rec_present' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VEnv.addInduct_eq_none_of_rec_present

/--
info: 'Lean4Lean.VEnv.addInduct_WF' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms VEnv.addInduct_WF
