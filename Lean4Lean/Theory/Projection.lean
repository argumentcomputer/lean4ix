import Lean4Lean.Theory.Typing.InductivePatternWF

/-!
# Structure projections

This module is the consumer-neutral projection boundary.  A projection is
not determined by a structure name and field number alone: universe
instantiations, parameters, the constructor telescope, and the generated
recursor/iota package all affect its meaning.  `VStructureView` retains that
data from the same checked artifact used by inductive generation.

Projection terms are encoded with the generated recursor.  Earlier
projections occur in the motive of a dependent later projection, so one view
determines both the projected term and its dependent result type.  No
projection-function name map or unconstrained metadata witness is involved.
-/

namespace Lean4Lean

open VInductDecl

/-- Consume a syntactic prefix of dependent `forall` binders, instantiating
them outermost-first. -/
def VExpr.consumeForalls? : VExpr → List VExpr → Option VExpr
  | e, [] => some e
  | .forallE _ body, arg :: args => consumeForalls? (body.inst arg) args
  | _, _ :: _ => none

theorem VExpr.consumeForalls?_append (e : VExpr)
    (left right : List VExpr) :
    e.consumeForalls? (left ++ right) =
      (e.consumeForalls? left).bind fun cursor =>
        cursor.consumeForalls? right := by
  induction left generalizing e with
  | nil => rfl
  | cons arg left ih =>
      cases e <;> simp [VExpr.consumeForalls?, ih]

theorem VExpr.instTelN_getElem? (arg : VExpr) (fields : List VExpr)
    (k i : Nat) :
    (VExpr.instTelN arg fields k)[i]? =
      fields[i]?.map fun field => field.inst arg (k + i) := by
  induction fields generalizing k i with
  | nil => simp [VExpr.instTelN]
  | cons field fields ih =>
      cases i with
      | zero => simp [VExpr.instTelN]
      | succ i =>
          simp only [VExpr.instTelN, List.getElem?_cons_succ]
          simpa only [Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using ih (k + 1) i

/-- Consuming `args` from a telescope exposes the next original binder with
exactly those arguments substituted. -/
theorem VExpr.consumeForalls?_forallN_domain
    (fields : List VExpr) (result : VExpr) (args : List VExpr)
    (hlen : args.length < fields.length) :
    ∃ field body,
      fields[args.length]? = some field ∧
      VExpr.consumeForalls? (VExpr.forallN fields result) args =
        some (.forallE (field.instRevAt args 0) body) := by
  induction args generalizing fields result with
  | nil =>
      cases fields with
      | nil => simp at hlen
      | cons field fields =>
          exact ⟨field, VExpr.forallN fields result, rfl, rfl⟩
  | cons arg args ih =>
      cases fields with
      | nil => simp at hlen
      | cons field fields =>
          have hlen' : args.length <
              (VExpr.instTelN arg fields 0).length := by
            simpa [VExpr.instTelN_length] using hlen
          obtain ⟨field', body, hfield', hconsume⟩ :=
            ih (VExpr.instTelN arg fields 0)
              (result.inst arg fields.length) hlen'
          rw [VExpr.instTelN_getElem?] at hfield'
          obtain ⟨original, horiginal, rfl⟩ := Option.map_eq_some_iff.1 hfield'
          refine ⟨original, body, by simpa using horiginal, ?_⟩
          simp only [VExpr.forallN, VExpr.consumeForalls?,
            VExpr.instN_forallN]
          simp only [Nat.zero_add]
          simpa only [VExpr.instRevAt, Nat.zero_add] using hconsume

@[simp] theorem VExpr.instL_instRevAt (e : VExpr) (as : List VExpr)
    (k : Nat) :
    (e.instRevAt as k).instL ls =
      (e.instL ls).instRevAt (as.map (VExpr.instL ls)) k := by
  induction as generalizing e with
  | nil => rfl
  | cons a as ih =>
      simp only [VExpr.instRevAt, List.map_cons]
      simpa only [VExpr.instL_instN, List.length_map] using
        ih (e := e.inst a (k + as.length))

private theorem VExpr.instL_lamN_projection (ls : List VLevel) :
    ∀ (As : List VExpr) (e : VExpr),
      (VExpr.lamN As e).instL ls =
        VExpr.lamN (As.map (VExpr.instL ls)) (e.instL ls)
  | [], _ => rfl
  | _ :: As, e => by
      simp only [VExpr.lamN, VExpr.instL, List.map_cons]
      rw [VExpr.instL_lamN_projection ls As e]

private theorem VExpr.liftN_lamN_projection (n : Nat) :
    ∀ (As : List VExpr) (e : VExpr) (k : Nat),
      (VExpr.lamN As e).liftN n k =
        VExpr.lamN (VExpr.liftTelN n As k)
          (e.liftN n (k + As.length))
  | [], _, _ => rfl
  | _ :: As, e, k => by
      simp only [VExpr.lamN, VExpr.liftN, VExpr.liftTelN,
        List.length_cons]
      rw [VExpr.liftN_lamN_projection n As e (k + 1)]
      rw [show k + 1 + As.length = k + (As.length + 1) by omega]

private theorem VExpr.instN_lamN_projection (a : VExpr) :
    ∀ (As : List VExpr) (e : VExpr) (k : Nat),
      (VExpr.lamN As e).inst a k =
        VExpr.lamN (VExpr.instTelN a As k)
          (e.inst a (k + As.length))
  | [], _, _ => rfl
  | _ :: As, e, k => by
      simp only [VExpr.lamN, VExpr.inst, VExpr.instTelN,
        List.length_cons]
      rw [VExpr.instN_lamN_projection a As e (k + 1)]
      rw [show k + 1 + As.length = k + (As.length + 1) by omega]

/-- A recursor minor which ignores its induction hypotheses and returns the
`i`-th constructor field.  The induction-hypothesis telescope is explicit:
recursive singleton structures bind it after the constructor fields, while
the existing nonrecursive program is the `ihs = []` specialization. -/
def VExpr.selectFieldMinor (fields ihs : List VExpr) (i : Nat) : VExpr :=
  VExpr.lamN fields <| VExpr.lamN ihs <|
    .bvar (ihs.length + fields.length - 1 - i)

@[simp] theorem VExpr.selectFieldMinor_nil
    (fields : List VExpr) (i : Nat) :
    VExpr.selectFieldMinor fields [] i =
      VExpr.lamN fields (.bvar (fields.length - 1 - i)) := by
  simp [VExpr.selectFieldMinor, VExpr.lamN]

@[simp] theorem VExpr.selectFieldMinor_instL
    (fields ihs : List VExpr) (i : Nat) (ls : List VLevel) :
    (VExpr.selectFieldMinor fields ihs i).instL ls =
      VExpr.selectFieldMinor (fields.map (VExpr.instL ls))
        (ihs.map (VExpr.instL ls)) i := by
  simp [VExpr.selectFieldMinor, VExpr.instL_lamN_projection,
    VExpr.instL]

theorem VExpr.selectFieldMinor_liftN
    (fields ihs : List VExpr) (i n k : Nat)
    (hi : i < fields.length) :
    (VExpr.selectFieldMinor fields ihs i).liftN n k =
      VExpr.selectFieldMinor (VExpr.liftTelN n fields k)
        (VExpr.liftTelN n ihs (k + fields.length)) i := by
  simp only [VExpr.selectFieldMinor, VExpr.liftN_lamN_projection,
    VExpr.liftN, VExpr.liftTelN_length]
  rw [liftVar_lt]
  omega

theorem VExpr.selectFieldMinor_instN
    (fields ihs : List VExpr) (i k : Nat) (a : VExpr)
    (hi : i < fields.length) :
    (VExpr.selectFieldMinor fields ihs i).inst a k =
      VExpr.selectFieldMinor (VExpr.instTelN a fields k)
        (VExpr.instTelN a ihs (k + fields.length)) i := by
  simp only [VExpr.selectFieldMinor, VExpr.instN_lamN_projection,
    VExpr.inst, VExpr.instTelN_length]
  simp [VExpr.instVar, show
    ihs.length + fields.length - 1 - i <
      k + fields.length + ihs.length by omega]

private theorem VExpr.liftN_lift_projection (e : VExpr) (n k : Nat) :
    e.lift.liftN n (k + 1) = (e.liftN n k).lift :=
  (VExpr.lift_liftN' e k).symm

private theorem VExpr.liftN_liftAt_projection
    (e : VExpr) (n k i : Nat) :
    (e.liftN 1 i).liftN n (k + 1 + i) =
      (e.liftN n (k + i)).liftN 1 i := by
  symm
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    VExpr.liftN_liftN_comm e 1 n i (k + i) (by omega)

private theorem VExpr.liftTelN_liftAt_projection (As : List VExpr)
    (n k i : Nat) :
    VExpr.liftTelN n (VExpr.liftTelN 1 As i) (k + 1 + i) =
      VExpr.liftTelN 1 (VExpr.liftTelN n As (k + i)) i := by
  induction As generalizing i with
  | nil => rfl
  | cons A As ih =>
      simp only [VExpr.liftTelN]
      rw [VExpr.liftN_liftAt_projection A n k i]
      congr 1
      simpa only [Nat.add_assoc] using ih (i + 1)

private theorem VExpr.liftTelN_lift_projection (As : List VExpr)
    (n k : Nat) :
    VExpr.liftTelN n (VExpr.liftTelN 1 As 0) (k + 1) =
      VExpr.liftTelN 1 (VExpr.liftTelN n As k) 0 := by
  simpa using VExpr.liftTelN_liftAt_projection As n k 0

private theorem VExpr.instN_liftAt_projection
    (e a : VExpr) (k i : Nat) :
    (e.liftN 1 i).inst a (k + 1 + i) =
      (e.inst a (k + i)).liftN 1 i := by
  symm
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    VExpr.liftN_instN_lo 1 e a (k + i) i (by omega)

private theorem VExpr.instTelN_liftAt_projection (As : List VExpr)
    (a : VExpr) (k i : Nat) :
    VExpr.instTelN a (VExpr.liftTelN 1 As i) (k + 1 + i) =
      VExpr.liftTelN 1 (VExpr.instTelN a As (k + i)) i := by
  induction As generalizing i with
  | nil => rfl
  | cons A As ih =>
      simp only [VExpr.liftTelN, VExpr.instTelN]
      rw [VExpr.instN_liftAt_projection A a k i]
      congr 1
      simpa only [Nat.add_assoc] using ih (i + 1)

private theorem VExpr.instTelN_lift_projection (As : List VExpr)
    (a : VExpr) (k : Nat) :
    VExpr.instTelN a (VExpr.liftTelN 1 As 0) (k + 1) =
      VExpr.liftTelN 1 (VExpr.instTelN a As k) 0 := by
  simpa using VExpr.instTelN_liftAt_projection As a k 0

private theorem VExpr.instN_instRevAt_lift_projection
    (e : VExpr) (args : List VExpr) (a : VExpr) (i : Nat) :
    ((e.liftN 1 i).instRevAt args (i + 1)).inst a i =
      e.instRevAt args i := by
  induction args generalizing e with
  | nil => exact VExpr.inst_liftN1 e a i
  | cons arg args ih =>
      simp only [VExpr.instRevAt]
      rw [show i + 1 + args.length = args.length + 1 + i by omega,
        VExpr.instN_liftAt_projection e arg args.length i]
      simpa only [Nat.add_comm] using
        ih (e := e.inst arg (args.length + i))

private theorem VExpr.instTelN_instRevAt_lift_projection
    (fields : List VExpr) (args : List VExpr) (a : VExpr)
    (start : Nat) :
    VExpr.instTelN a
        ((VExpr.liftTelN 1 fields start).zipIdx (start + 1) |>.map
          fun x => x.1.instRevAt args x.2)
        start =
      (fields.zipIdx start |>.map
        fun x => x.1.instRevAt args x.2) := by
  induction fields generalizing start with
  | nil => rfl
  | cons field fields ih =>
      simp only [VExpr.liftTelN, List.zipIdx, List.map_cons,
        VExpr.instTelN]
      rw [VExpr.instN_instRevAt_lift_projection]
      congr 1
      simpa only [Nat.add_assoc] using ih (start + 1)

private theorem VExpr.inst_liftN_top (e a : VExpr) (n : Nat) :
    (e.liftN (n + 1)).inst a n = e.liftN n := by
  rw [← VExpr.liftN'_liftN' (e := e) (n1 := n) (n2 := 1)
    (k1 := 0) (k2 := n) (Nat.zero_le _) (by omega)]
  exact VExpr.inst_liftN (e.liftN n) a

private theorem VExpr.instRevAt_liftN_len (args : List VExpr)
    (e : VExpr) (k : Nat) :
    (e.liftN (k + args.length)).instRevAt args k = e.liftN k := by
  induction args with
  | nil => rfl
  | cons arg args ih =>
      simp only [List.length_cons, VExpr.instRevAt]
      rw [show k + (args.length + 1) = (k + args.length) + 1 by omega,
        VExpr.inst_liftN_top]
      exact ih

private theorem VExpr.instRevAt_bvar_lt_cons (args : List VExpr)
    (arg : VExpr) (k i : Nat) (hi : i < k + args.length) :
    (VExpr.bvar i).instRevAt (arg :: args) k =
      (VExpr.bvar i).instRevAt args k := by
  simp only [VExpr.instRevAt]
  congr 1
  simp [VExpr.inst, VExpr.instVar, hi]

private theorem VExpr.map_instRevAt_bvarRevRange
    (args : List VExpr) (k : Nat) :
    (VExpr.bvarRevRange k args.length).map
        (fun e => e.instRevAt args k) =
      args.map (VExpr.liftN k) := by
  induction args with
  | nil => rfl
  | cons arg args ih =>
      simp only [List.length_cons, VExpr.bvarRevRange,
        List.map_cons]
      congr 1
      · simp only [VExpr.instRevAt]
        rw [show (VExpr.bvar (k + args.length)).inst arg
              (k + args.length) = arg.liftN (k + args.length) by
            simp [VExpr.inst, VExpr.instVar]]
        exact VExpr.instRevAt_liftN_len args arg k
      · rw [← ih]
        apply List.map_congr_left
        intro e he
        obtain ⟨i, rfl, _, hi⟩ := VExpr.mem_bvarRevRange he
        exact VExpr.instRevAt_bvar_lt_cons args arg k i (by omega)

private theorem VExpr.instRevAt_appN_projection
    (f : VExpr) (es : List VExpr) (args : List VExpr) (k : Nat) :
    (VExpr.appN f es).instRevAt args k =
      VExpr.appN (f.instRevAt args k)
        (es.map fun e => e.instRevAt args k) := by
  induction args generalizing f es with
  | nil => simp [VExpr.instRevAt, List.map_id']
  | cons arg args ih =>
      simp only [VExpr.instRevAt, VExpr.instN_appN]
      rw [ih]
      simp only [List.map_map, Function.comp_def]

private theorem VExpr.map_instRevAt_closedN (args es : List VExpr)
    (k : Nat) (hclosed : ∀ e ∈ es, e.ClosedN k) :
    es.map (fun e => e.instRevAt args k) = es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      simp only [List.map_cons]
      rw [VExpr.instRevAt_closedN args (hclosed e (.head _))]
      congr 1
      exact ih (fun e he => hclosed e (.tail _ he))

private theorem VExpr.map_instN_closedN (a : VExpr) (es : List VExpr)
    (k : Nat) (hclosed : ∀ e ∈ es, e.ClosedN k) :
    es.map (fun e => e.inst a k) = es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
      simp only [List.map_cons]
      rw [(hclosed e (.head _)).instN_eq (Nat.le_refl _)]
      congr 1
      exact ih (fun e he => hclosed e (.tail _ he))

private theorem VExpr.map_instN_liftN_top
    (es : List VExpr) (a : VExpr) (n : Nat) :
    (es.map (VExpr.liftN (n + 1))).map
        (fun e => e.inst a n) =
      es.map (VExpr.liftN n) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro e _
  exact VExpr.inst_liftN_top e a n

private theorem VExpr.projectionMinorBody_shape
    (constructorName : Name) (levels : List VLevel)
    (params : List VExpr) (m : Nat) (typeFn : VExpr) :
    ((VExpr.appN (.bvar m)
          [VExpr.appN (.const constructorName levels)
            (VExpr.bvarRevRange (m + 1) params.length ++
              VExpr.bvarRevRange 0 m)]).instRevAt params (m + 1)).inst
        typeFn m =
      .app (typeFn.liftN m)
        (VExpr.appN (.const constructorName levels)
          (params.map (VExpr.liftN m) ++
            VExpr.bvarRevRange 0 m)) := by
  have hmotiveR : (VExpr.bvar m).instRevAt params (m + 1) =
      .bvar m := VExpr.instRevAt_closedN params (by
        exact Nat.lt_succ_self m)
  have hconstR : (VExpr.const constructorName levels).instRevAt
      params (m + 1) = .const constructorName levels :=
    VExpr.instRevAt_closedN params (by trivial)
  have hfieldsR := VExpr.map_instRevAt_closedN params
    (VExpr.bvarRevRange 0 m) (m + 1)
    (bvarRevRange_closedN m 0 (m + 1) (by omega))
  have hmotiveI : (VExpr.bvar m).inst typeFn m =
      typeFn.liftN m := by simp [VExpr.inst, VExpr.instVar]
  have hconstI : (VExpr.const constructorName levels).inst typeFn m =
      .const constructorName levels := by rfl
  have hparamsI := VExpr.map_instN_liftN_top params typeFn m
  have hfieldsI := VExpr.map_instN_closedN typeFn
    (VExpr.bvarRevRange 0 m) m
    (bvarRevRange_closedN m 0 m (by omega))
  rw [VExpr.instRevAt_appN_projection, hmotiveR]
  simp only [List.map_singleton]
  rw [VExpr.instRevAt_appN_projection, hconstR, List.map_append,
    VExpr.map_instRevAt_bvarRevRange, hfieldsR]
  rw [VExpr.instN_appN, hmotiveI]
  simp only [List.map_singleton]
  rw [VExpr.instN_appN, hconstI, List.map_append,
    hparamsI, hfieldsI]
  rfl

private theorem VExpr.projectionMajorTail_shape
    (familyName : Name) (levels : List VLevel)
    (params : List VExpr) (typeFn : VExpr) :
    (((VExpr.forallE
          (VExpr.appN (.const familyName levels)
            (VExpr.bvarRevRange 2 params.length))
          (.app (.appN (.bvar 2) []) (.bvar 0))).instRevAt
        params 2).inst typeFn 1) =
      VExpr.forallE
        (VExpr.appN (.const familyName levels)
          (params.map (VExpr.liftN 1)))
        (.app (typeFn.liftN 2) (.bvar 0)) := by
  have hconstR : (VExpr.const familyName levels).instRevAt
      params 2 = .const familyName levels :=
    VExpr.instRevAt_closedN params (by trivial)
  have hbodyR :
      (VExpr.app (VExpr.appN (.bvar 2) []) (.bvar 0)).instRevAt
          params 3 =
        VExpr.app (VExpr.appN (.bvar 2) []) (.bvar 0) :=
    VExpr.instRevAt_closedN params (by
      change 2 < 3 ∧ 0 < 3
      omega)
  rw [VExpr.instRevAt_forallE_projection,
    VExpr.instRevAt_appN_projection, hconstR,
    VExpr.map_instRevAt_bvarRevRange, hbodyR]
  simp only [VExpr.inst]
  congr 1
  · rw [VExpr.instN_appN]
    have hconstI : (VExpr.const familyName levels).inst typeFn 1 =
        .const familyName levels := by rfl
    rw [hconstI, VExpr.map_instN_liftN_top]

theorem VExpr.liftN_instRevAt (e : VExpr) (as : List VExpr)
    (i k n : Nat) :
    (e.instRevAt as i).liftN n (k + i) =
      (e.liftN n (k + i + as.length)).instRevAt
        (as.map fun a => a.liftN n k) i := by
  induction as generalizing e with
  | nil => simp [VExpr.instRevAt]
  | cons a as ih =>
      simp only [VExpr.instRevAt, List.map_cons]
      rw [ih]
      simp only [List.length_cons, List.length_map]
      rw [show k + i + as.length = k + (i + as.length) by omega,
        VExpr.liftN_instN_hi]
      congr 3 <;> omega

theorem VExpr.instN_instRevAt (e : VExpr) (as : List VExpr)
    (i k : Nat) (a : VExpr) :
    (e.instRevAt as i).inst a (k + i) =
      (e.inst a (k + i + as.length)).instRevAt
        (as.map fun arg => arg.inst a k) i := by
  induction as generalizing e with
  | nil => simp [VExpr.instRevAt]
  | cons arg as ih =>
      simp only [VExpr.instRevAt, List.map_cons]
      rw [ih]
      simp only [List.length_cons, List.length_map]
      rw [show k + i + as.length = k + (i + as.length) by omega,
        VExpr.inst_inst_hi]
      congr 3 <;> omega

/-- A telescope whose entries have the exact retained sort levels. -/
inductive VEnv.OnSortTel (env : VEnv) (U : Nat) :
    List VExpr → List VExpr → List VLevel → Prop where
  | nil : OnSortTel env U Γ [] []
  | cons :
      env.HasType U Γ A (.sort u) →
      OnSortTel env U (A :: Γ) As us →
      OnSortTel env U Γ (A :: As) (u :: us)

private theorem onCtx_levelWFProjection {env : VEnv} {U : Nat} :
    ∀ {Γ : List VExpr}, OnCtx Γ (env.IsType U) →
      OnCtx Γ fun _ A => A.LevelWF U
  | [], _ => trivial
  | _ :: _, ⟨hΓ, ⟨_, hA⟩⟩ =>
      let hΓ' := onCtx_levelWFProjection hΓ
      ⟨hΓ', (hA.levelWF hΓ').1⟩

/-- Every retained sort selected from a checked sort telescope is a
well-formed universe at the ambient universe bound. -/
theorem VEnv.OnSortTel.sortWF {env : VEnv} {U : Nat}
    : ∀ {Γ : List VExpr} {As : List VExpr} {us : List VLevel},
      OnCtx Γ (env.IsType U) → env.OnSortTel U Γ As us →
      ∀ {i : Nat} {u : VLevel}, us[i]? = some u → u.WF U
  | _, [], [], _, .nil, _, _, h => by simp at h
  | _, _ :: _, _ :: _, hΓ, .cons hA hT, 0, _, h => by
      injection h with h
      subst h
      exact (hA.levelWF (onCtx_levelWFProjection hΓ)).2.2
  | Γ, A :: As, u₀ :: us, hΓ, .cons hA hT, i + 1, u, h => by
      exact VEnv.OnSortTel.sortWF (env := env) (U := U)
        (Γ := A :: Γ) (As := As) (us := us)
        ⟨hΓ, ⟨u₀, hA⟩⟩ hT (by simpa using h)

private theorem VEnv.OnTel.monoProjection {env env' : VEnv}
    (henv : env ≤ env') (H : env.OnTel U Γ As) : env'.OnTel U Γ As := by
  induction As generalizing Γ with
  | nil => trivial
  | cons _ _ ih =>
      exact ⟨H.1.mono henv, ih H.2⟩

theorem VEnv.OnSortTel.mono {env env' : VEnv} (henv : env ≤ env')
    (H : env.OnSortTel U Γ As us) : env'.OnSortTel U Γ As us := by
  induction H with
  | nil => exact .nil
  | cons hA _ ih => exact .cons (hA.mono henv) ih

/-- Forget the retained sort labels, preserving the underlying telescope
well-formedness judgment. -/
theorem VEnv.OnSortTel.toOnTel {env : VEnv} :
    ∀ {U : Nat} {Γ As : List VExpr} {us : List VLevel},
      env.OnSortTel U Γ As us → env.OnTel U Γ As
  | _, _, [], [], .nil => trivial
  | _, _, _ :: _, _ :: _, .cons hA hT =>
      ⟨⟨_, hA⟩, VEnv.OnSortTel.toOnTel hT⟩

/-- Split a checked sort telescope immediately before a selected binder. -/
theorem VEnv.OnSortTel.prefix_getElem? {env : VEnv} {U : Nat} :
    ∀ {i : Nat} {Γ : List VExpr} {As : List VExpr} {us : List VLevel}
      {A : VExpr} {u : VLevel},
      env.OnSortTel U Γ As us →
      As[i]? = some A → us[i]? = some u →
      env.OnTel U Γ (As.take i) ∧
        env.HasType U ((As.take i).reverse ++ Γ) A (.sort u)
  | _, _, [], [], _, _, .nil, hA, _ => by simp at hA
  | 0, _, _ :: _, _ :: _, _, _, .cons hA _, hfield, hsort => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hfield hsort
      subst_vars
      exact ⟨by trivial, by simpa using hA⟩
  | i + 1, Γ, A₀ :: As, u₀ :: us, A, u, .cons hA hT,
      hfield, hsort => by
      simp only [List.getElem?_cons_succ] at hfield hsort
      obtain ⟨hprefix, hselected⟩ :=
        VEnv.OnSortTel.prefix_getElem? hT hfield hsort
      refine ⟨⟨⟨u₀, hA⟩, hprefix⟩, ?_⟩
      simpa [List.take_succ_cons, List.reverse_cons,
        List.append_assoc] using hselected

theorem VEnv.OnSortTel.instL {env : VEnv} {U U' : Nat}
    (hlevels : ∀ level ∈ levels, level.WF U') :
    ∀ {Γ As us}, env.OnSortTel U Γ As us →
      env.OnSortTel U' (Γ.map (VExpr.instL levels))
        (As.map (VExpr.instL levels))
        (us.map (VLevel.inst levels))
  | _, [], [], .nil => .nil
  | _, _ :: _, _ :: _, .cons hA hT =>
      .cons (hA.instL hlevels) (VEnv.OnSortTel.instL hlevels hT)

theorem VEnv.OnSortTel.weakN {env : VEnv} (henv : env.Ordered)
    {U n k : Nat} {Γ Γ' : List VExpr} (W : Ctx.LiftN n k Γ Γ') :
    ∀ {As us}, env.OnSortTel U Γ As us →
      env.OnSortTel U Γ' (VExpr.liftTelN n As k) us
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons hA hT =>
      .cons (hA.weakN henv W)
        (VEnv.OnSortTel.weakN henv W.succ hT)

private theorem VEnv.OnSortTel.instN {env : VEnv} (henv : env.Ordered)
    {U : Nat} {Γ₀ : List VExpr} {e₀ A₀ : VExpr}
    (h₀ : env.HasType U Γ₀ e₀ A₀) :
    ∀ {As : List VExpr} {us : List VLevel} {k : Nat}
      {Γ Γ' : List VExpr},
      Ctx.InstN Γ₀ e₀ A₀ k Γ Γ' →
      env.OnSortTel U Γ As us →
      env.OnSortTel U Γ' (VExpr.instTelN e₀ As k) us
  | [], [], _, _, _, _, .nil => .nil
  | _ :: _, _ :: _, _, _, _, W, .cons hA hT =>
      .cons (hA.instN henv W h₀)
        (VEnv.OnSortTel.instN henv h₀ W.succ hT)

/-- Synchronize a checked sort telescope with a typed application prefix and
recover the exact next domain together with its retained sort. -/
private theorem VEnv.OnSortTel.next_of_spine {env : VEnv}
    (henv : env.Ordered) {U : Nat} {Γ : List VExpr} :
    ∀ {As : List VExpr} {us : List VLevel} {args : List VExpr}
      {tail cursor : VExpr},
      env.OnSortTel U Γ As us →
      env.SpineWF U Γ (VExpr.forallN As tail) args cursor →
      args.length < As.length →
      ∃ A u body,
        cursor = .forallE A body ∧
        env.HasType U Γ A (.sort u) ∧
        us[args.length]? = some u := by
  intro As us args tail cursor
  induction args generalizing As us tail cursor with
  | nil =>
      intro htel hspine hlength
      cases As with
      | nil => simp at hlength
      | cons A As =>
        cases us with
        | nil => cases htel
        | cons u us =>
          cases htel with
          | cons hA _ =>
            cases hspine
            exact ⟨A, u, VExpr.forallN As tail, rfl, hA, rfl⟩
  | cons arg args ih =>
      intro htel hspine hlength
      cases As with
      | nil => simp at hlength
      | cons A As =>
        cases us with
        | nil => cases htel
        | cons u us =>
          cases htel with
          | cons hA htail =>
            cases hspine with
            | cons harg hrest =>
              have htail' : env.OnSortTel U Γ
                  (VExpr.instTelN arg As 0) us := by
                exact VEnv.OnSortTel.instN henv harg Ctx.InstN.zero htail
              have hrest' : env.SpineWF U Γ
                  (VExpr.forallN (VExpr.instTelN arg As 0)
                    (tail.inst arg As.length)) args cursor := by
                simpa [VExpr.instN_forallN] using hrest
              have hlength' : args.length <
                  (VExpr.instTelN arg As 0).length := by
                simpa [VExpr.instTelN_length] using hlength
              obtain ⟨next, nextSort, body, hcursor, hnext, hsort⟩ :=
                ih htail' hrest' hlength'
              exact ⟨next, nextSort, body, hcursor, hnext, by simpa using hsort⟩

private theorem VExpr.instRevAt_instTelN_cons
    (fields : List VExpr) (a : VExpr) (as : List VExpr) :
    ((VExpr.instTelN a fields as.length).zipIdx.map fun (field, i) =>
        VExpr.instRevAt field as i) =
      (fields.zipIdx.map fun (field, i) =>
        VExpr.instRevAt field (a :: as) i) := by
  suffices ∀ (start k : Nat), k = as.length + start →
      ((VExpr.instTelN a fields k).zipIdx start |>.map
          fun (field, i) => VExpr.instRevAt field as i) =
        (fields.zipIdx start |>.map fun (field, i) =>
          VExpr.instRevAt field (a :: as) i) by
    simpa using this 0 as.length (by omega)
  intro start k hk
  induction fields generalizing start k with
  | nil => rfl
  | cons field fields ih =>
      simp only [VExpr.instTelN, List.zipIdx, List.map_cons,
        VExpr.instRevAt]
      rw [hk]
      congr 1
      · congr 2 <;> omega
      · exact ih (start + 1) (as.length + start + 1) (by omega)

theorem VExpr.instRevAt_map_instL_zipIdx
    (fields : List VExpr) (levels : List VLevel)
    (params : List VExpr) (start : Nat := 0) :
    ((fields.map (VExpr.instL levels)).zipIdx start |>.map
        fun (field, i) => VExpr.instRevAt field params i) =
      (fields.zipIdx start |>.map fun (field, i) =>
        VExpr.instRevAt (field.instL levels) params i) := by
  induction fields generalizing start with
  | nil => rfl
  | cons field fields ih =>
      simp only [List.map_cons, List.zipIdx]
      congr 1
      exact ih (start + 1)

private theorem VEnv.OnSortTel.instRevParams {env : VEnv}
    (henv : env.Ordered) {U : Nat} :
    ∀ {Γ params args fields sorts resultLevel},
      env.SpineWF U Γ (VExpr.forallN params (.sort resultLevel))
        args (.sort resultLevel) →
      args.length = params.length →
      env.OnSortTel U (params.reverse ++ Γ) fields sorts →
      env.OnSortTel U Γ
        (fields.zipIdx.map fun (field, i) =>
          VExpr.instRevAt field args i) sorts
  | _, [], [], fields, sorts, _, hspine, _, hfields => by
      simpa [VExpr.instRevAt] using hfields
  | _, [], _ :: _, _, _, _, _, hlen, _ => by simp at hlen
  | Γ, param :: params, arg :: args, fields, sorts, resultLevel,
      .cons harg hrest, hlen, hfields => by
      have hparams : args.length = params.length := by simpa using hlen
      have W := Ctx.InstN.consTel (Γ₀ := Γ) (e₀ := arg)
        (A₀ := param) params (.zero)
      have hfields' : env.OnSortTel U
          ((VExpr.instTelN arg params 0).reverse ++ Γ)
          (VExpr.instTelN arg fields params.length) sorts := by
        apply VEnv.OnSortTel.instN henv harg W
        simpa [List.append_assoc] using hfields
      have hrest' : env.SpineWF U Γ
          (VExpr.forallN (VExpr.instTelN arg params 0)
            (.sort resultLevel)) args (.sort resultLevel) := by
        simpa [VExpr.instN_forallN, VExpr.inst] using hrest
      have hout := VEnv.OnSortTel.instRevParams henv
        hrest' (by simpa [VExpr.instTelN_length] using hparams) hfields'
      rw [← hparams, VExpr.instRevAt_instTelN_cons] at hout
      exact hout

/-- Extend a well-formed ambient context by a well-formed telescope. -/
theorem VEnv.OnTel.toOnCtx {env : VEnv} {U : Nat} :
    ∀ {As Γ}, env.OnTel U Γ As → OnCtx Γ (env.IsType U) →
      OnCtx (As.reverse ++ Γ) (env.IsType U)
  | [], _, _, hΓ => by simpa using hΓ
  | A :: As, Γ, ⟨hA, hAs⟩, hΓ => by
      simpa [List.append_assoc] using
        VEnv.OnTel.toOnCtx hAs (Γ := A :: Γ) ⟨hΓ, hA⟩

private theorem VEnv.OnSortTel.closedAt {env : VEnv} {U : Nat}
    (henv : env.Ordered) :
    ∀ {As us Γ}, env.OnSortTel U Γ As us → CtxClosed Γ →
      ∀ {i : Nat} {field : VExpr}, As[i]? = some field →
        field.ClosedN (Γ.length + i)
  | _, _, _, .nil, _, i, _, h => by simp at h
  | _ :: _, _ :: _, Γ, .cons hA hAs, hΓ, 0, _, h => by
      simp only [List.getElem?_cons_zero] at h
      cases h
      simpa using hA.closedN henv hΓ
  | A :: As, _ :: _, Γ, .cons hA hAs, hΓ, i + 1, field, h => by
      simp only [List.getElem?_cons_succ] at h
      have hclosed : A.ClosedN Γ.length := hA.closedN henv hΓ
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        VEnv.OnSortTel.closedAt henv hAs ⟨hΓ, hclosed⟩ h

private theorem VEnv.OnTel.liftTelN_eq {env : VEnv} {U : Nat}
    (henv : env.Ordered) :
    ∀ {As Γ}, env.OnTel U Γ As → CtxClosed Γ → ∀ n,
      VExpr.liftTelN n As Γ.length = As
  | [], _, _, _, _ => rfl
  | A :: As, Γ, ⟨hA, hAs⟩, hΓ, n => by
      obtain ⟨_, hA⟩ := hA
      have hclosed : A.ClosedN Γ.length := hA.closedN henv hΓ
      simp only [VExpr.liftTelN, hclosed.liftN_eq (Nat.le_refl _)]
      simpa using VEnv.OnTel.liftTelN_eq henv hAs ⟨hΓ, hclosed⟩ n

private theorem VEnv.OnSortTel.liftTelN_eq {env : VEnv} {U : Nat}
    (henv : env.Ordered) :
    ∀ {As us Γ}, env.OnSortTel U Γ As us → CtxClosed Γ → ∀ n,
      VExpr.liftTelN n As Γ.length = As
  | [], [], _, .nil, _, _ => rfl
  | A :: As, _ :: us, Γ, .cons hA hAs, hΓ, n => by
      have hclosed : A.ClosedN Γ.length := hA.closedN henv hΓ
      simp only [VExpr.liftTelN, hclosed.liftN_eq (Nat.le_refl _)]
      simpa using VEnv.OnSortTel.liftTelN_eq henv hAs ⟨hΓ, hclosed⟩ n

/-- The checked, generated description of a nonrecursive structure.

`generation` supplies the exact family, constructor, recursor, and iota rule
artifacts.  The shape fields restrict that general one-family artifact to the
kernel class on which `.proj` is meaningful: no indices, exactly one
constructor, and no recursive constructor arguments.  `fieldSorts` records
the motive universe required by each projection; `WF` below ties every entry
to the corresponding dependent constructor field type. -/
structure VStructureView where
  source : VInductDecl
  generation : source.GenerationChecked
  constructor : NormalizedCtor
  constructor_eq : generation.block.ctorPairs = [constructor]
  raw_indices_eq : generation.block.rawIndices = []
  checked_indices_eq : generation.block.checked.indices = []
  recursive_eq : constructor.view.recursive = []
  fieldSorts : List VLevel
  fieldSorts_length :
    fieldSorts.length = (constructor.rawFields source.nparams).length

namespace VStructureView

abbrev name (view : VStructureView) : Name :=
  view.generation.block.sourceType.name

abbrev constructorName (view : VStructureView) : Name :=
  view.constructor.raw.name

def recursorName (view : VStructureView) : Name :=
  .str view.name "rec"

abbrev uvars (view : VStructureView) : Nat := view.source.uvars

abbrev nparams (view : VStructureView) : Nat := view.source.nparams

abbrev familyType (view : VStructureView) : VExpr :=
  view.generation.block.sourceType.type

def constructorParams (view : VStructureView) : List VExpr :=
  VExpr.telN view.nparams view.constructor.raw.type

def fields (view : VStructureView) : List VExpr :=
  view.constructor.rawFields view.nparams

/-- The instantiated structure type `S.{levels} params`. -/
def structureType (view : VStructureView)
    (levels : List VLevel) (params : List VExpr) : VExpr :=
  VExpr.appN (.const view.name levels) params

/-- Specialize declaration universes and constructor parameters, retaining
the preceding field binders of each dependent field. -/
def specializedFields (view : VStructureView)
    (levels : List VLevel) (params : List VExpr) : List VExpr :=
  view.fields.zipIdx.map fun (field, i) =>
    VExpr.instRevAt (field.instL levels) params i

private theorem specializedFieldsAux_liftN
    (rawFields : List VExpr) (levels : List VLevel)
    (params : List VExpr) (p start n k : Nat)
    (hparams : params.length = p)
    (hclosed : ∀ (j : Nat) (field : VExpr),
      rawFields[j]? = some field →
        field.ClosedN (p + start + j)) :
    (rawFields.zipIdx start |>.map fun (field, i) =>
      VExpr.instRevAt (field.instL levels)
        (params.map fun param => param.liftN n k) i) =
    VExpr.liftTelN n
      (rawFields.zipIdx start |>.map fun (field, i) =>
        VExpr.instRevAt (field.instL levels) params i)
      (k + start) := by
  induction rawFields generalizing start with
  | nil => rfl
  | cons field rawFields ih =>
      have hfield : (field.instL levels).ClosedN (p + start + 0) :=
        VExpr.ClosedN.instL (ls := levels) (hclosed 0 field (by rfl))
      have hrawLift :
          (field.instL levels).liftN n
              (k + start + params.length) = field.instL levels :=
        hfield.liftN_eq (by rw [hparams]; omega)
      have hhead := VExpr.liftN_instRevAt
        (field.instL levels) params start k n
      rw [hrawLift] at hhead
      have htail := ih (start := start + 1)
        (fun j tailField htailField => by
          have := hclosed (j + 1) tailField (by simpa using htailField)
          simpa only [Nat.add_assoc, Nat.add_left_comm,
            Nat.add_comm] using this)
      simp only [List.zipIdx, List.map_cons, VExpr.liftTelN]
      rw [← hhead]
      exact congrArg
        (List.cons (VExpr.liftN n
          ((field.instL levels).instRevAt params start) (k + start)))
        (by simpa only [Nat.add_assoc] using htail)

private theorem specializedFieldsAux_instN
    (rawFields : List VExpr) (levels : List VLevel)
    (params : List VExpr) (p start k : Nat) (a : VExpr)
    (hparams : params.length = p)
    (hclosed : ∀ (j : Nat) (field : VExpr),
      rawFields[j]? = some field →
        field.ClosedN (p + start + j)) :
    (rawFields.zipIdx start |>.map fun (field, i) =>
      VExpr.instRevAt (field.instL levels)
        (params.map fun param => param.inst a k) i) =
    VExpr.instTelN a
      (rawFields.zipIdx start |>.map fun (field, i) =>
        VExpr.instRevAt (field.instL levels) params i)
      (k + start) := by
  induction rawFields generalizing start with
  | nil => rfl
  | cons field rawFields ih =>
      have hfield : (field.instL levels).ClosedN (p + start + 0) :=
        VExpr.ClosedN.instL (ls := levels) (hclosed 0 field (by rfl))
      have hrawInst :
          (field.instL levels).inst a
              (k + start + params.length) = field.instL levels :=
        hfield.instN_eq (by rw [hparams]; omega)
      have hhead := VExpr.instN_instRevAt
        (field.instL levels) params start k a
      rw [hrawInst] at hhead
      have htail := ih (start := start + 1)
        (fun j tailField htailField => by
          have := hclosed (j + 1) tailField (by simpa using htailField)
          simpa only [Nat.add_assoc, Nat.add_left_comm,
            Nat.add_comm] using this)
      simp only [List.zipIdx, List.map_cons, VExpr.instTelN]
      rw [← hhead]
      exact congrArg
        (List.cons (VExpr.inst
          ((field.instL levels).instRevAt params start) a (k + start)))
        (by simpa only [Nat.add_assoc] using htail)

/-- Universe arguments supplied to the generated recursor for a projection
whose result type inhabits `Sort fieldSort`. -/
def projectionLevels (view : VStructureView)
    (fieldSort : VLevel) (levels : List VLevel) : List VLevel :=
  match view.generation.elimination with
  | .large => fieldSort :: levels
  | .small => levels

/-- The two expressions generated for one field.  `typeFn` is the dependent
field type as a function of the structure value; `projector` is a recursor
program implementing the projection. -/
structure ProjectionCode where
  fieldSort : VLevel
  typeFn : VExpr
  minor : VExpr
  projector : VExpr

@[ext] theorem ProjectionCode.ext {left right : ProjectionCode}
    (fieldSort : left.fieldSort = right.fieldSort)
    (typeFn : left.typeFn = right.typeFn)
    (minor : left.minor = right.minor)
    (projector : left.projector = right.projector) : left = right := by
  cases left
  cases right
  simp_all

def ProjectionCode.liftN (code : ProjectionCode)
    (n k : Nat) : ProjectionCode where
  fieldSort := code.fieldSort
  typeFn := code.typeFn.liftN n k
  minor := code.minor.liftN n k
  projector := code.projector.liftN n k

def ProjectionCode.instN (code : ProjectionCode)
    (a : VExpr) (k : Nat) : ProjectionCode where
  fieldSort := code.fieldSort
  typeFn := code.typeFn.inst a k
  minor := code.minor.inst a k
  projector := code.projector.inst a k

def ProjectionCode.instL (code : ProjectionCode)
    (ls : List VLevel) : ProjectionCode where
  fieldSort := code.fieldSort.inst ls
  typeFn := code.typeFn.instL ls
  minor := code.minor.instL ls
  projector := code.projector.instL ls

/-- The constructor-headed major used by a projection minor after all fields
have been introduced. -/
def projectionConstructorApp (view : VStructureView)
    (levels : List VLevel) (params fields : List VExpr) : VExpr :=
  VExpr.appN (.const view.constructorName levels)
    (params.map (VExpr.liftN fields.length) ++
      VExpr.bvarRevRange 0 fields.length)

/-- The one-constructor, nonrecursive minor premise expected by the generated
recursor after parameters and a projection motive have been supplied. -/
def projectionMinorType (view : VStructureView)
    (levels : List VLevel) (params fields : List VExpr)
    (typeFn : VExpr) : VExpr :=
  VExpr.forallN fields
    (.app (typeFn.liftN fields.length)
      (view.projectionConstructorApp levels params fields))

/-- The exact generated minor domain after specializing recursor universes,
constructor parameters, and the projection motive.  Unlike
`projectionMinorType`, this expression still contains the generated
induction-hypothesis telescope when the singleton constructor is recursive. -/
def generatedProjectionMinorType (view : VStructureView)
    (fieldSort : VLevel) (levels : List VLevel) (params : List VExpr)
    (typeFn : VExpr) : VExpr :=
  (((VInductDecl.GenerationChecked.minorType
      (source := view.source) view.constructor view.generation.elimination).instL
      (view.projectionLevels fieldSort levels)).instRevAt params 1).inst
          typeFn

/-- The induction-hypothesis binder types occurring after the specialized
constructor fields in the exact generated projection minor. -/
def projectionIHTypes (view : VStructureView)
    (fieldSort : VLevel) (levels : List VLevel) (params : List VExpr)
    (typeFn : VExpr) : List VExpr :=
  VExpr.telN view.constructor.view.recursive.length <|
    VExpr.dropN (view.specializedFields levels params).length <|
      view.generatedProjectionMinorType fieldSort levels params typeFn

/-- The present nonrecursive view boundary specializes the exact IH
telescope to the empty list.  This theorem is intentionally the sole
compatibility reduction used by the legacy projection program. -/
@[simp] theorem projectionIHTypes_eq_nil (view : VStructureView)
    (fieldSort : VLevel) (levels : List VLevel) (params : List VExpr)
    (typeFn : VExpr) :
    view.projectionIHTypes fieldSort levels params typeFn = [] := by
  simp [projectionIHTypes, view.recursive_eq, VExpr.telN]

@[simp] theorem projectionLevels_instL (view : VStructureView)
    (fieldSort : VLevel) (levels ls : List VLevel) :
    (view.projectionLevels fieldSort levels).map (VLevel.inst ls) =
      view.projectionLevels (fieldSort.inst ls)
        (levels.map (VLevel.inst ls)) := by
  unfold projectionLevels
  split <;> rfl

@[simp] theorem structureType_instL (view : VStructureView)
    (levels : List VLevel) (params : List VExpr) (ls : List VLevel) :
    (view.structureType levels params).instL ls =
      view.structureType (levels.map (VLevel.inst ls))
        (params.map (VExpr.instL ls)) := by
  simp [structureType, VExpr.instL_appN, VExpr.instL]

@[simp] theorem structureType_liftN (view : VStructureView)
    (levels : List VLevel) (params : List VExpr) (n k : Nat) :
    (view.structureType levels params).liftN n k =
      view.structureType levels
        (params.map fun param => param.liftN n k) := by
  simp [structureType, VExpr.liftN_appN, VExpr.liftN]

@[simp] theorem structureType_instN (view : VStructureView)
    (levels : List VLevel) (params : List VExpr) (a : VExpr) (k : Nat) :
    (view.structureType levels params).inst a k =
      view.structureType levels
        (params.map fun param => param.inst a k) := by
  simp [structureType, VExpr.instN_appN, VExpr.inst]

@[simp] theorem specializedFields_instL (view : VStructureView)
    (levels : List VLevel) (params : List VExpr) (ls : List VLevel) :
    (view.specializedFields levels params).map (VExpr.instL ls) =
      view.specializedFields (levels.map (VLevel.inst ls))
        (params.map (VExpr.instL ls)) := by
  simp [specializedFields, VExpr.instL_instRevAt, VExpr.instL_instL, Function.comp_def]

private def projectionCode (view : VStructureView)
    (levels : List VLevel) (params allFields : List VExpr)
    (structType field : VExpr) (fieldSort : VLevel) (i : Nat)
    (previous : List ProjectionCode) : ProjectionCode :=
  let previousAtMajor := previous.map fun code =>
    .app code.projector.lift (.bvar 0)
  let motiveBody := VExpr.instRevAt
    (field.liftN 1 i) previousAtMajor 0
  let typeFn := .lam structType motiveBody
  let minor := VExpr.selectFieldMinor allFields
    (view.projectionIHTypes fieldSort levels params typeFn) i
  let recursor := .const view.recursorName
    (view.projectionLevels fieldSort levels)
  let projector := .lam structType <| VExpr.appN recursor <|
    params.map (VExpr.liftN 1) ++
      [typeFn.lift, minor.lift, .bvar 0]
  { fieldSort, typeFn, minor, projector }

private theorem projectionCode_liftN (view : VStructureView)
    (levels : List VLevel) (params allFields : List VExpr)
    (structType field : VExpr) (fieldSort : VLevel) (i : Nat)
    (previous : List ProjectionCode) (n k : Nat)
    (hprevious : previous.length = i)
    (hi : i < allFields.length) :
    (projectionCode view levels params allFields structType field
      fieldSort i previous).liftN n k =
    projectionCode view levels
      (params.map fun param => param.liftN n k)
      (VExpr.liftTelN n allFields k)
      (structType.liftN n k) (field.liftN n (k + i)) fieldSort i
      (previous.map fun code => code.liftN n k) := by
  have hfieldLift :
      (field.liftN 1 i).liftN n (k + 1 + i) =
        (field.liftN n (k + i)).liftN 1 i :=
    VExpr.liftN_liftAt_projection field n k i
  have hpreviousLift :
      (previous.map fun code =>
        VExpr.app code.projector.lift (.bvar 0)).map
          (fun (e : VExpr) => e.liftN n (k + 1)) =
      (previous.map fun code => code.liftN n k).map fun code =>
        VExpr.app code.projector.lift (.bvar 0) := by
    simp [ProjectionCode.liftN, VExpr.liftN,
      VExpr.liftN_lift_projection, List.map_map,
      Function.comp_def]
  have hmotive :
      ((field.liftN 1 i).instRevAt
          (previous.map fun code =>
            VExpr.app code.projector.lift (.bvar 0)) 0).liftN n (k + 1) =
      ((field.liftN n (k + i)).liftN 1 i).instRevAt
          ((previous.map fun code => code.liftN n k).map fun code =>
            VExpr.app code.projector.lift (.bvar 0)) 0 := by
    rw [VExpr.liftN_instRevAt]
    rw [List.length_map, hprevious, hfieldLift, hpreviousLift]
  have hminorBody :
      VExpr.liftN n (.bvar (allFields.length - 1 - i))
          (k + allFields.length) =
        .bvar (allFields.length - 1 - i) := by
    simp only [VExpr.liftN]
    rw [liftVar_lt]
    omega
  have hminorVar :
      liftVar n (allFields.length - 1 - i)
          (k + allFields.length) = allFields.length - 1 - i := by
    rw [liftVar_lt]
    omega
  have hminorNestedVar :
      liftVar n (liftVar 1 (allFields.length - 1 - i)
          allFields.length) (k + 1 + allFields.length) =
        liftVar 1 (allFields.length - 1 - i) allFields.length := by
    have hinner : liftVar 1 (allFields.length - 1 - i)
        allFields.length = allFields.length - 1 - i :=
      liftVar_lt (by omega)
    rw [hinner, liftVar_lt (by omega)]
  have hmotiveLift :
      (((field.liftN 1 i).instRevAt
          (previous.map fun code =>
            VExpr.app code.projector.lift (.bvar 0)) 0).liftN 1 1).liftN
          n (k + 1 + 1) =
      (((field.liftN n (k + i)).liftN 1 i).instRevAt
          ((previous.map fun code => code.liftN n k).map fun code =>
            VExpr.app code.projector.lift (.bvar 0)) 0).liftN 1 1 := by
    rw [VExpr.liftN_liftAt_projection]
    exact congrArg (fun e => e.liftN 1 1) hmotive
  apply ProjectionCode.ext
  · rfl
  · simp [projectionCode, ProjectionCode.liftN, VExpr.liftN,
      hmotive]
  · simp [projectionCode, ProjectionCode.liftN,
      VExpr.liftN_lamN_projection, VExpr.liftTelN_length,
      hminorBody]
  · simp [projectionCode, ProjectionCode.liftN, VExpr.liftN,
      VExpr.liftN_appN, VExpr.liftN_lamN_projection,
      VExpr.liftTelN_length, VExpr.liftN_lift_projection,
      VExpr.liftTelN_lift_projection, List.map_append,
      List.map_map, Function.comp_def, hmotive, hmotiveLift,
      hminorNestedVar]

private theorem projectionCode_instN (view : VStructureView)
    (levels : List VLevel) (params allFields : List VExpr)
    (structType field : VExpr) (fieldSort : VLevel) (i : Nat)
    (previous : List ProjectionCode) (a : VExpr) (k : Nat)
    (hprevious : previous.length = i)
    (hi : i < allFields.length) :
    (projectionCode view levels params allFields structType field
      fieldSort i previous).instN a k =
    projectionCode view levels
      (params.map fun param => param.inst a k)
      (VExpr.instTelN a allFields k)
      (structType.inst a k) (field.inst a (k + i)) fieldSort i
      (previous.map fun code => code.instN a k) := by
  have hfieldInst :
      (field.liftN 1 i).inst a (k + 1 + i) =
        (field.inst a (k + i)).liftN 1 i :=
    VExpr.instN_liftAt_projection field a k i
  have hpreviousInst :
      (previous.map fun code =>
        VExpr.app code.projector.lift (.bvar 0)).map
          (fun (e : VExpr) => e.inst a (k + 1)) =
      (previous.map fun code => code.instN a k).map fun code =>
        VExpr.app code.projector.lift (.bvar 0) := by
    simp [ProjectionCode.instN, VExpr.inst, VExpr.instVar,
      ← VExpr.lift_instN_lo, List.map_map, Function.comp_def]
  have hmotive :
      ((field.liftN 1 i).instRevAt
          (previous.map fun code =>
            VExpr.app code.projector.lift (.bvar 0)) 0).inst a (k + 1) =
      ((field.inst a (k + i)).liftN 1 i).instRevAt
          ((previous.map fun code => code.instN a k).map fun code =>
            VExpr.app code.projector.lift (.bvar 0)) 0 := by
    rw [VExpr.instN_instRevAt]
    rw [List.length_map, hprevious, hfieldInst, hpreviousInst]
  have hminorVar :
      VExpr.instVar (allFields.length - 1 - i) a
          (k + allFields.length) =
        .bvar (allFields.length - 1 - i) := by
    simp [VExpr.instVar, show
      allFields.length - 1 - i < k + allFields.length by omega]
  apply ProjectionCode.ext
  · rfl
  · simp [projectionCode, ProjectionCode.instN, VExpr.inst, hmotive]
  · simp [projectionCode, ProjectionCode.instN, VExpr.inst,
      VExpr.instN_lamN_projection, VExpr.instTelN_length,
      hminorVar]
  · simp [projectionCode, ProjectionCode.instN, VExpr.inst, VExpr.instN_appN,
      VExpr.instN_lamN_projection, VExpr.instTelN_length, ← VExpr.lift_instN_lo, List.map_append,
      List.map_map, Function.comp_def, hmotive, hminorVar]

private def projectionCodes.go (view : VStructureView)
    (levels : List VLevel) (params : List VExpr)
    (allFields : List VExpr) (structType : VExpr) :
    List VExpr → List VLevel → Nat → List ProjectionCode →
      List ProjectionCode
  | field :: fields, fieldSort :: fieldSorts, i, previous =>
      let code := projectionCode view levels params allFields structType
        field fieldSort i previous
      code :: projectionCodes.go view levels params allFields structType
        fields fieldSorts (i + 1) (previous ++ [code])
  | _, _, _, _ => []

private theorem projectionCodes.go_instN (view : VStructureView)
    (levels : List VLevel) (params allFields : List VExpr)
    (structType : VExpr) (fields : List VExpr)
    (fieldSorts : List VLevel) (i : Nat)
    (previous : List ProjectionCode) (a : VExpr) (k : Nat)
    (hprevious : previous.length = i)
    (hfields : i + fields.length = allFields.length) :
    (projectionCodes.go view levels params allFields structType
        fields fieldSorts i previous).map
      (fun code => code.instN a k) =
    projectionCodes.go view levels
      (params.map fun param => param.inst a k)
      (VExpr.instTelN a allFields k) (structType.inst a k)
      (VExpr.instTelN a fields (k + i)) fieldSorts i
      (previous.map fun code => code.instN a k) := by
  induction fields generalizing fieldSorts i previous with
  | nil =>
      cases fieldSorts <;> simp [projectionCodes.go, VExpr.instTelN]
  | cons field fields ih =>
      cases fieldSorts with
      | nil => simp [projectionCodes.go]
      | cons fieldSort fieldSorts =>
          have hi : i < allFields.length := by
            simp only [List.length_cons] at hfields
            omega
          have hcode := projectionCode_instN view levels params allFields
            structType field fieldSort i previous a k hprevious hi
          simp only [projectionCodes.go, List.map_cons,
            VExpr.instTelN]
          rw [hcode]
          congr 1
          have hprevious' :
              (previous ++ [projectionCode view levels params allFields
                structType field fieldSort i previous]).length = i + 1 := by
            simp [hprevious]
          have hfields' : i + 1 + fields.length = allFields.length := by
            simp only [List.length_cons] at hfields
            omega
          simpa only [List.map_append, List.map_singleton,
            hcode, Nat.add_assoc] using
              ih fieldSorts (i + 1)
                (previous ++ [projectionCode view levels params allFields
                  structType field fieldSort i previous])
                hprevious' hfields'

private theorem projectionCode_instL (view : VStructureView)
    (levels : List VLevel) (params allFields : List VExpr)
    (structType field : VExpr) (fieldSort : VLevel) (i : Nat)
    (previous : List ProjectionCode) (ls : List VLevel) :
    (projectionCode view levels params allFields structType field
      fieldSort i previous).instL ls =
    projectionCode view
      (levels.map (VLevel.inst ls))
      (params.map (VExpr.instL ls))
      (allFields.map (VExpr.instL ls))
      (structType.instL ls) (field.instL ls) (fieldSort.inst ls) i
      (previous.map fun code => code.instL ls) := by
  simp [projectionCode, ProjectionCode.instL, VExpr.instL,
    VExpr.instL_instRevAt, VExpr.instL_lamN_projection,
    VExpr.instL_appN, VExpr.instL_liftN,
    List.map_append, List.map_map, Function.comp_def]

private theorem projectionCodes.go_instL (view : VStructureView)
    (levels : List VLevel) (params allFields : List VExpr)
    (structType : VExpr) (fields : List VExpr)
    (fieldSorts : List VLevel) (i : Nat)
    (previous : List ProjectionCode) (ls : List VLevel) :
    (projectionCodes.go view levels params allFields structType
        fields fieldSorts i previous).map
      (fun code => code.instL ls) =
    projectionCodes.go view
      (levels.map (VLevel.inst ls))
      (params.map (VExpr.instL ls))
      (allFields.map (VExpr.instL ls))
      (structType.instL ls)
      (fields.map (VExpr.instL ls))
      (fieldSorts.map (VLevel.inst ls)) i
      (previous.map fun code => code.instL ls) := by
  induction fields generalizing fieldSorts i previous with
  | nil => simp [projectionCodes.go]
  | cons field fields ih =>
      cases fieldSorts with
      | nil => simp [projectionCodes.go]
      | cons fieldSort fieldSorts =>
          simp only [projectionCodes.go, List.map_cons,
            projectionCode_instL]
          congr 1
          simpa only [List.map_append, List.map_singleton,
            projectionCode_instL] using
            ih fieldSorts (i + 1)
              (previous ++ [projectionCode view levels params allFields
                structType field fieldSort i previous])

private theorem projectionCodes.go_liftN (view : VStructureView)
    (levels : List VLevel) (params allFields : List VExpr)
    (structType : VExpr) (fields : List VExpr)
    (fieldSorts : List VLevel) (i : Nat)
    (previous : List ProjectionCode) (n k : Nat)
    (hprevious : previous.length = i)
    (hfields : i + fields.length = allFields.length) :
    (projectionCodes.go view levels params allFields structType
        fields fieldSorts i previous).map
      (fun code => code.liftN n k) =
    projectionCodes.go view levels
      (params.map fun param => param.liftN n k)
      (VExpr.liftTelN n allFields k) (structType.liftN n k)
      (VExpr.liftTelN n fields (k + i)) fieldSorts i
      (previous.map fun code => code.liftN n k) := by
  induction fields generalizing fieldSorts i previous with
  | nil =>
      cases fieldSorts <;> simp [projectionCodes.go, VExpr.liftTelN]
  | cons field fields ih =>
      cases fieldSorts with
      | nil => simp [projectionCodes.go]
      | cons fieldSort fieldSorts =>
          have hi : i < allFields.length := by
            simp only [List.length_cons] at hfields
            omega
          have hcode := projectionCode_liftN view levels params allFields
            structType field fieldSort i previous n k hprevious hi
          simp only [projectionCodes.go, List.map_cons,
            VExpr.liftTelN]
          rw [hcode]
          congr 1
          have hprevious' :
              (previous ++ [projectionCode view levels params allFields
                structType field fieldSort i previous]).length = i + 1 := by
            simp [hprevious]
          have hfields' : i + 1 + fields.length = allFields.length := by
            simp only [List.length_cons] at hfields
            omega
          simpa only [List.map_append, List.map_singleton,
            hcode, Nat.add_assoc] using
              ih fieldSorts (i + 1)
                (previous ++ [projectionCode view levels params allFields
                  structType field fieldSort i previous])
                hprevious' hfields'

/-- All field projections, in constructor-field order. -/
def projectionCodes (view : VStructureView)
    (levels : List VLevel) (params : List VExpr) : List ProjectionCode :=
  let fields := view.specializedFields levels params
  projectionCodes.go view levels params fields
    (view.structureType levels params) fields
      (view.fieldSorts.map (VLevel.inst levels)) 0 []

private theorem projectionCodes.go_length (view : VStructureView)
    (levels : List VLevel) (params allFields : List VExpr)
    (structType : VExpr) :
    ∀ (fields : List VExpr) (fieldSorts : List VLevel)
      (i : Nat) (previous : List ProjectionCode),
      fields.length = fieldSorts.length →
      (projectionCodes.go view levels params allFields structType
        fields fieldSorts i previous).length = fields.length
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | field :: fields, fieldSort :: fieldSorts, i, previous, h => by
      simp only [List.length_cons] at h ⊢
      simp only [projectionCodes.go, List.length_cons]
      exact congrArg Nat.succ <|
        projectionCodes.go_length view levels params allFields structType
          fields fieldSorts (i + 1)
          (previous ++ [projectionCode view levels params allFields
            structType field fieldSort i previous]) (Nat.succ.inj h)

@[simp] theorem projectionCodes_length (view : VStructureView)
    (levels : List VLevel) (params : List VExpr) :
    (view.projectionCodes levels params).length =
      (view.specializedFields levels params).length := by
  apply projectionCodes.go_length
  simp [VStructureView.specializedFields, VStructureView.fields,
    view.fieldSorts_length]

/-- Semantic arguments substituted while walking to a later dependent
projection field. -/
def projectionArgs (view : VStructureView) (levels : List VLevel)
    (params : List VExpr) (count : Nat) (major : VExpr) : List VExpr :=
  (view.projectionCodes levels params).take count |>.map fun code =>
    .app code.projector major

/-- Rebuild a structure value from all of its canonical generated
projections.  This is syntax only: `ProgramsWF.projectionArgsSpine` below
supplies the rule-independent typing evidence, while any equality between
this term and `major` remains an explicit definitional-equality capability. -/
def etaRebuild (view : VStructureView) (levels : List VLevel)
    (params : List VExpr) (major : VExpr) : VExpr :=
  VExpr.appN (.const view.constructorName levels)
    (params ++ view.projectionArgs levels params
      (view.specializedFields levels params).length major)

@[simp] theorem projectionArgs_length (view : VStructureView)
    (levels : List VLevel) (params : List VExpr) (count : Nat)
    (major : VExpr) (hcount : count ≤
      (view.projectionCodes levels params).length) :
    (view.projectionArgs levels params count major).length = count := by
  simp only [projectionArgs, List.length_map, List.length_take]
  exact Nat.min_eq_left hcount

theorem projectionArgs_succ (view : VStructureView)
    (levels : List VLevel) (params : List VExpr) (count : Nat)
    (major : VExpr) {code : ProjectionCode}
    (hcode : (view.projectionCodes levels params)[count]? = some code) :
    view.projectionArgs levels params (count + 1) major =
      view.projectionArgs levels params count major ++
        [.app code.projector major] := by
  simp only [projectionArgs, List.take_add_one, hcode, Option.toList_some,
    List.map_append, List.map_singleton]

private theorem projectionCodes.go_get?_typeFn (view : VStructureView)
    (levels : List VLevel) (params allFields : List VExpr)
    (structType : VExpr) :
    ∀ {fields : List VExpr} {fieldSorts : List VLevel}
      {i : Nat} {previous : List ProjectionCode} {j : Nat}
      {code : ProjectionCode},
      (projectionCodes.go view levels params allFields structType
        fields fieldSorts i previous)[j]? = some code →
      ∃ field,
        fields[j]? = some field ∧
        code.typeFn = .lam structType
          ((field.liftN 1 (i + j)).instRevAt
            ((previous ++
              (projectionCodes.go view levels params allFields structType
                fields fieldSorts i previous).take j).map fun prior =>
                .app prior.projector.lift (.bvar 0)) 0) := by
  intro fields
  induction fields with
  | nil =>
      intro fieldSorts i previous j code h
      cases fieldSorts <;> simp [projectionCodes.go] at h
  | cons field fields ih =>
      intro fieldSorts i previous j code h
      cases fieldSorts with
      | nil => simp [projectionCodes.go] at h
      | cons fieldSort fieldSorts =>
          let head := projectionCode view levels params allFields structType
            field fieldSort i previous
          cases j with
          | zero =>
              change some head = some code at h
              injection h with hcode
              subst code
              refine ⟨field, rfl, ?_⟩
              simp [head, projectionCode]
          | succ j =>
              simp only [projectionCodes.go, List.getElem?_cons_succ] at h
              obtain ⟨tailField, htailField, htypeFn⟩ :=
                ih (fieldSorts := fieldSorts) (i := i + 1)
                  (previous := previous ++ [head]) h
              refine ⟨tailField, by simpa using htailField, ?_⟩
              have hpref :
                  previous ++
                    (projectionCodes.go view levels params allFields structType
                      (field :: fields) (fieldSort :: fieldSorts) i previous).take
                        (j + 1) =
                    (previous ++ [head]) ++
                      (projectionCodes.go view levels params allFields structType
                        fields fieldSorts (i + 1)
                          (previous ++ [head])).take j := by
                simp [head, projectionCodes.go, List.append_assoc]
              rw [hpref]
              simpa only [Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using htypeFn

/-- The generated type function at field `idx` is the corresponding
specialized constructor field with all earlier generated projectors
substituted at the major premise. -/
theorem projectionCodes_get?_typeFn (view : VStructureView)
    (levels : List VLevel) (params : List VExpr) {idx : Nat}
    {code : ProjectionCode}
    (hcode : (view.projectionCodes levels params)[idx]? = some code) :
    ∃ field,
      (view.specializedFields levels params)[idx]? = some field ∧
      code.typeFn = .lam (view.structureType levels params)
        ((field.liftN 1 idx).instRevAt
          ((view.projectionCodes levels params).take idx |>.map fun prior =>
            .app prior.projector.lift (.bvar 0)) 0) := by
  unfold projectionCodes at hcode ⊢
  simpa using projectionCodes.go_get?_typeFn view levels params
    (view.specializedFields levels params)
    (view.structureType levels params) hcode

private theorem projectionCodes.go_get?_program_shape
    (view : VStructureView) (levels : List VLevel)
    (params allFields : List VExpr) (structType : VExpr) :
    ∀ {fields : List VExpr} {fieldSorts : List VLevel}
      {i : Nat} {previous : List ProjectionCode} {j : Nat}
      {code : ProjectionCode},
      (projectionCodes.go view levels params allFields structType
        fields fieldSorts i previous)[j]? = some code →
      ∃ fieldSort,
        fieldSorts[j]? = some fieldSort ∧
          code.fieldSort = fieldSort ∧
          code.minor = VExpr.lamN allFields
            (.bvar (allFields.length - 1 - (i + j))) ∧
          code.projector = .lam structType
            (VExpr.appN
              (.const view.recursorName
                (view.projectionLevels code.fieldSort levels))
              (params.map (VExpr.liftN 1) ++
                [code.typeFn.lift, code.minor.lift, .bvar 0])) := by
  intro fields
  induction fields with
  | nil =>
      intro fieldSorts i previous j code h
      cases fieldSorts <;> simp [projectionCodes.go] at h
  | cons field fields ih =>
      intro fieldSorts i previous j code h
      cases fieldSorts with
      | nil => simp [projectionCodes.go] at h
      | cons fieldSort fieldSorts =>
          let head := projectionCode view levels params allFields structType
            field fieldSort i previous
          cases j with
          | zero =>
              change some head = some code at h
              injection h with hcode
              subst code
              simp [head, projectionCode]
          | succ j =>
              simp only [projectionCodes.go, List.getElem?_cons_succ] at h
              have hout := ih (fieldSorts := fieldSorts) (i := i + 1)
                (previous := previous ++ [head]) h
              simpa only [List.getElem?_cons_succ, Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using hout

/-- A selected projection code retains the exact selecting minor and
recursor program emitted by `projectionCodes`. -/
theorem projectionCodes_get?_program_shape (view : VStructureView)
    (levels : List VLevel) (params : List VExpr) {idx : Nat}
    {code : ProjectionCode}
    (hcode : (view.projectionCodes levels params)[idx]? = some code) :
    ∃ fieldSort,
      (view.fieldSorts.map (VLevel.inst levels))[idx]? = some fieldSort ∧
        code.fieldSort = fieldSort ∧
        code.minor = VExpr.lamN (view.specializedFields levels params)
          (.bvar ((view.specializedFields levels params).length - 1 - idx)) ∧
        code.projector = .lam (view.structureType levels params)
          (VExpr.appN
            (.const view.recursorName
              (view.projectionLevels code.fieldSort levels))
            (params.map (VExpr.liftN 1) ++
              [code.typeFn.lift, code.minor.lift, .bvar 0])) := by
  unfold projectionCodes at hcode
  simpa using projectionCodes.go_get?_program_shape view levels params
    (view.specializedFields levels params)
    (view.structureType levels params) hcode

/-- Applying a generated projection's type function to its major premise
substitutes that major into every earlier generated projector. -/
theorem projectionCodes_get?_typeFn_beta (view : VStructureView)
    (levels : List VLevel) (params : List VExpr) {idx : Nat}
    {code : ProjectionCode}
    (hcode : (view.projectionCodes levels params)[idx]? = some code)
    (major : VExpr) :
    ∃ field typeBody,
      (view.specializedFields levels params)[idx]? = some field ∧
      code.typeFn = .lam (view.structureType levels params) typeBody ∧
      typeBody.inst major =
        field.instRevAt
          ((view.projectionCodes levels params).take idx |>.map fun prior =>
            .app prior.projector major) 0 := by
  obtain ⟨field, hfield, htypeFn⟩ :=
    view.projectionCodes_get?_typeFn levels params hcode
  let codes := view.projectionCodes levels params
  have hidx : idx < codes.length :=
    (List.getElem?_eq_some_iff.1 hcode).1
  have htake : (codes.take idx).length = idx := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hidx)]
  have htake' :
      ((view.projectionCodes levels params).take idx).length = idx := by
    simpa [codes] using htake
  refine ⟨field, _, hfield, htypeFn, ?_⟩
  rw [VExpr.instN_instRevAt]
  rw [List.length_map, htake']
  simp only [Nat.zero_add, VExpr.inst_liftN1]
  congr 1
  induction (view.projectionCodes levels params).take idx with
  | nil => rfl
  | cons prior previous ih =>
      simp only [List.map_cons]
      rw [ih]
      simp only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero]

@[simp] theorem projectionCodes_instL (view : VStructureView)
    (levels : List VLevel) (params : List VExpr) (ls : List VLevel) :
    (view.projectionCodes levels params).map
        (fun code => code.instL ls) =
      view.projectionCodes (levels.map (VLevel.inst ls))
        (params.map (VExpr.instL ls)) := by
  simp [projectionCodes, projectionCodes.go_instL,
    VLevel.inst_inst, List.map_map, Function.comp_def]

/-- The dependent result type of projection `idx`, applied to `major`. -/
def projectionType? (view : VStructureView)
    (levels : List VLevel) (params : List VExpr)
    (idx : Nat) (major : VExpr) : Option VExpr := do
  let code ← (view.projectionCodes levels params)[idx]?
  return .app code.typeFn major

/-- The recursor encoding of projection `idx`, applied to `major`. -/
def project? (view : VStructureView)
    (levels : List VLevel) (params : List VExpr)
    (idx : Nat) (major : VExpr) : Option VExpr := do
  let code ← (view.projectionCodes levels params)[idx]?
  return .app code.projector major

/-- A proof-carrying boundary for the programs generated by
`projectionCodes`.  Generation fixes the program syntax, while this
certificate records the remaining semantic fact needed by consumers: every
selected projector is well typed at every well-formed instantiation.

This is intentionally separate from `VStructureView.WF`.  The latter is the
certificate produced by ordinary inductive generation; accepting primitive
projection syntax is a later capability boundary and must not silently add a
structure-eta rule to Theory's definitional equality. -/
def ProgramsWF (view : VStructureView) (env : VEnv) : Prop :=
  ∀ {U : Nat} {Γ : List VExpr} {levels : List VLevel}
      {params : List VExpr} {idx : Nat} {code : ProjectionCode},
    OnCtx Γ (env.IsType U) →
    (∀ level ∈ levels, level.WF U) →
    levels.length = view.uvars →
    params.length = view.nparams →
    (∃ resultLevel, env.SpineWF U Γ (view.familyType.instL levels)
      params (.sort resultLevel)) →
    (view.projectionCodes levels params)[idx]? = some code →
    env.HasType U Γ code.projector
      (.forallE (view.structureType levels params)
        (.app code.typeFn.lift (.bvar 0)))

/-- The source-ordered selecting minors used by generated projection
programs are well typed.  Unlike `ProgramsWF`, this boundary contains no
recursor-program obligation: `WF.toProgramsWF_of_minors` derives the latter
from checked generation and this strictly smaller premise. -/
def MinorsWF (view : VStructureView) (env : VEnv) : Prop :=
  ∀ {U : Nat} {Γ : List VExpr} {levels : List VLevel}
      {params : List VExpr} {idx : Nat} {code : ProjectionCode},
    OnCtx Γ (env.IsType U) →
    (∀ level ∈ levels, level.WF U) →
    levels.length = view.uvars →
    params.length = view.nparams →
    (∃ resultLevel, env.SpineWF U Γ (view.familyType.instL levels)
      params (.sort resultLevel)) →
    (view.projectionCodes levels params)[idx]? = some code →
    env.HasType U Γ code.minor
      (view.projectionMinorType levels params
        (view.specializedFields levels params) code.typeFn)

/-- The selecting-minor contract restricted to projection indices below a
source-order bound.  Keeping the bound outside the ambient typing data makes
this the induction-friendly form of `MinorsWF`: recursive projector proofs
may use exactly the already-established minor prefix. -/
def MinorsWFPrefix (view : VStructureView) (env : VEnv)
    (limit : Nat) : Prop :=
  ∀ {U : Nat} {Γ : List VExpr} {levels : List VLevel}
      {params : List VExpr} {idx : Nat} {code : ProjectionCode},
    idx < limit →
    OnCtx Γ (env.IsType U) →
    (∀ level ∈ levels, level.WF U) →
    levels.length = view.uvars →
    params.length = view.nparams →
    (∃ resultLevel, env.SpineWF U Γ (view.familyType.instL levels)
      params (.sort resultLevel)) →
    (view.projectionCodes levels params)[idx]? = some code →
    env.HasType U Γ code.minor
      (view.projectionMinorType levels params
        (view.specializedFields levels params) code.typeFn)

/-- The generated-projector contract restricted to projection indices below
a source-order bound. -/
def ProgramsWFPrefix (view : VStructureView) (env : VEnv)
    (limit : Nat) : Prop :=
  ∀ {U : Nat} {Γ : List VExpr} {levels : List VLevel}
      {params : List VExpr} {idx : Nat} {code : ProjectionCode},
    idx < limit →
    OnCtx Γ (env.IsType U) →
    (∀ level ∈ levels, level.WF U) →
    levels.length = view.uvars →
    params.length = view.nparams →
    (∃ resultLevel, env.SpineWF U Γ (view.familyType.instL levels)
      params (.sort resultLevel)) →
    (view.projectionCodes levels params)[idx]? = some code →
    env.HasType U Γ code.projector
      (.forallE (view.structureType levels params)
        (.app code.typeFn.lift (.bvar 0)))

/-- Exact constructor computation for a bounded source-order projector
prefix, stated in the canonical context containing every structure field.
The left spine is precisely the earlier generated projectors occurring in a
later dependent projection motive; the right spine names the corresponding
constructor field variables. -/
def ConstructorProjectorsExactPrefix (view : VStructureView) (env : VEnv)
    (limit : Nat) : Prop :=
  ∀ {U : Nat} {Γ : List VExpr} {levels : List VLevel}
      {params : List VExpr} {count : Nat},
    count ≤ limit →
    OnCtx Γ (env.IsType U) →
    (∀ level ∈ levels, level.WF U) →
    levels.length = view.uvars →
    params.length = view.nparams →
    (∃ resultLevel, env.SpineWF U Γ (view.familyType.instL levels)
      params (.sort resultLevel)) →
    count ≤ (view.projectionCodes levels params).length →
    let fields := view.specializedFields levels params
    List.Forall₂
      (fun projected selected => projected = selected ∨
        env.IsDefEqU U (fields.reverse ++ Γ) projected selected)
      (((view.projectionCodes levels params).take count).map fun prior =>
        .app (prior.projector.liftN fields.length)
          (view.projectionConstructorApp levels params fields))
      (VExpr.bvarRevRange (fields.length - count) count)

/-- The generated-rule capture spines needed to compute a bounded projector
prefix on the canonical constructor.  All deterministic parameters, motive,
minor, and field variables are fixed by the view; producers retain only the
typing of that exact capture list. -/
def ConstructorRuleCapturesPrefix (view : VStructureView) (env : VEnv)
    (limit : Nat) : Prop :=
  ∀ {U : Nat} {Γ : List VExpr} {levels : List VLevel}
      {params : List VExpr} {idx : Nat} {code : ProjectionCode},
    idx < limit →
    OnCtx Γ (env.IsType U) →
    (∀ level ∈ levels, level.WF U) →
    levels.length = view.uvars →
    params.length = view.nparams →
    (∃ resultLevel, env.SpineWF U Γ (view.familyType.instL levels)
      params (.sort resultLevel)) →
    (view.projectionCodes levels params)[idx]? = some code →
    let fields := view.specializedFields levels params
    let m := fields.length
    ∃ B, env.SpineWF U (fields.reverse ++ Γ)
      ((view.generation.rule 0 view.constructor).type.instL
        (view.projectionLevels code.fieldSort levels))
      (params.map (VExpr.liftN m) ++
        [(code.liftN m 0).typeFn, (code.liftN m 0).minor] ++
          VExpr.bvarRevRange 0 m) B

/-- Rule-independent subject reduction for rebuilding one well-typed
structure value from the canonical generated projections.  This is the
single-model core of `VStructEta.WF`; the latter additionally requires this
property in every future conversion-regular Theory extension because eta
rules are retained in the environment history. -/
def RebuildWF (view : VStructureView) (env : VEnv) : Prop :=
  ∀ {U : Nat} {Γ : List VExpr} {levels : List VLevel}
      {params : List VExpr} {major : VExpr},
    OnCtx Γ (env.IsType U) →
    (∀ level ∈ levels, level.WF U) →
    levels.length = view.uvars →
    params.length = view.nparams →
    (∃ resultLevel, env.SpineWF U Γ (view.familyType.instL levels)
      params (.sort resultLevel)) →
    env.HasType U Γ major (view.structureType levels params) →
    env.HasType U Γ (view.etaRebuild levels params major)
      (view.structureType levels params)

/-- One projector program with its generated function type computes the exact
dependent field type selected by the same code.  This is the one-code form of
`ProgramsWF.projector_hasType_field`; exposing it separately lets generated
program proofs proceed in source order without assuming the completed
`ProgramsWF` package circularly. -/
theorem projector_hasType_field_of_type
    {view : VStructureView} {env : VEnv} (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} {levels : List VLevel}
    {params : List VExpr} {idx : Nat} {code : ProjectionCode}
    (hΓ : OnCtx Γ (env.IsType U))
    (hcode : (view.projectionCodes levels params)[idx]? = some code)
    (hprojector : env.HasType U Γ code.projector
      (.forallE (view.structureType levels params)
        (.app code.typeFn.lift (.bvar 0))))
    {major : VExpr}
    (hmajor : env.HasType U Γ major (view.structureType levels params)) :
    ∃ field typeBody,
      (view.specializedFields levels params)[idx]? = some field ∧
      code.typeFn = .lam (view.structureType levels params) typeBody ∧
      env.HasType U Γ (.app code.projector major)
        (field.instRevAt (view.projectionArgs levels params idx major) 0) := by
  obtain ⟨field, typeBody, hfield, htypeFn, htypeBody⟩ :=
    view.projectionCodes_get?_typeFn_beta levels params hcode major
  have happ : env.HasType U Γ (.app code.projector major)
      (.app code.typeFn major) := by
    simpa only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero] using
      hprojector.app hmajor
  rw [htypeFn] at happ
  obtain ⟨sortLevel, hredexType⟩ := happ.isType henv hΓ
  obtain ⟨A, B, hlam, harg⟩ := hredexType.app_inv henv hΓ
  obtain ⟨⟨_, hstructType⟩, _, hbodyType⟩ :=
    hlam.lam_inv henv hΓ
  have hfunTypeEq := henv.hasType_uniqU hΓ hlam
    (hstructType.lam hbodyType)
  obtain ⟨⟨_, hdomainEq⟩, _⟩ :=
    henv.forallE_inv hΓ hfunTypeEq
  have harg' := henv.hasType_defeqU_r hΓ ⟨_, hdomainEq⟩ harg
  have hbeta : env.IsDefEqU U Γ
      (.app (.lam (view.structureType levels params) typeBody) major)
      (typeBody.inst major) :=
    ⟨_, VEnv.IsDefEq.beta hbodyType harg'⟩
  have hout := henv.hasType_defeqU_r hΓ hbeta happ
  rw [htypeBody] at hout
  refine ⟨field, typeBody, hfield, htypeFn, ?_⟩
  simpa [projectionArgs] using hout

/-- A source-ordered prefix of already typed projector programs forms the
corresponding dependent field spine.  The explicit bound is what permits the
program-typing proof to use strong induction on projection index. -/
theorem projectionArgsSpineAux_of_prefix
    {view : VStructureView} {env : VEnv} (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} {levels : List VLevel}
    {params : List VExpr} {major : VExpr} {limit : Nat}
    (hΓ : OnCtx Γ (env.IsType U))
    (hmajor : env.HasType U Γ major (view.structureType levels params))
    (programs : ∀ {idx : Nat} {code : ProjectionCode}, idx < limit →
      (view.projectionCodes levels params)[idx]? = some code →
      env.HasType U Γ code.projector
        (.forallE (view.structureType levels params)
          (.app code.typeFn.lift (.bvar 0))))
    (tailResult : VExpr) :
    ∀ {count : Nat}, count ≤ limit →
      count ≤ (view.specializedFields levels params).length →
      ∃ cursor,
        VExpr.consumeForalls?
            (VExpr.forallN (view.specializedFields levels params) tailResult)
            (view.projectionArgs levels params count major) = some cursor ∧
          env.SpineWF U Γ
            (VExpr.forallN (view.specializedFields levels params) tailResult)
            (view.projectionArgs levels params count major) cursor := by
  intro count hlimit hcount
  induction count with
  | zero =>
      exact ⟨_, rfl, .nil⟩
  | succ count ih =>
      have hcountLt : count <
          (view.specializedFields levels params).length := by omega
      have hcodeIdx : count <
          (view.projectionCodes levels params).length := by
        simpa using hcountLt
      let code := (view.projectionCodes levels params)[count]
      have hcode :
          (view.projectionCodes levels params)[count]? = some code :=
        List.getElem?_eq_getElem hcodeIdx
      have hargsLength :
          (view.projectionArgs levels params count major).length = count :=
        view.projectionArgs_length levels params count major
          (Nat.le_of_lt hcodeIdx)
      obtain ⟨cursor, hconsume, hspine⟩ :=
        ih (Nat.le_of_lt (Nat.lt_of_succ_le hlimit))
          (Nat.le_of_lt hcountLt)
      obtain ⟨field, semanticBody, hfield, hconsumeDomain⟩ :=
        VExpr.consumeForalls?_forallN_domain
          (view.specializedFields levels params) tailResult
          (view.projectionArgs levels params count major)
          (by simpa [hargsLength] using hcountLt)
      have hcursorShape : cursor =
          .forallE
            (field.instRevAt
              (view.projectionArgs levels params count major) 0)
            semanticBody :=
        Option.some.inj (hconsume.symm.trans hconsumeDomain)
      subst cursor
      have hprojector := programs (Nat.lt_of_succ_le hlimit) hcode
      obtain ⟨field', _, hfield', _, hprojectorField⟩ :=
        projector_hasType_field_of_type henv hΓ hcode hprojector hmajor
      have hfieldEq : field' = field :=
        Option.some.inj
          (hfield'.symm.trans (by simpa [hargsLength] using hfield))
      subst field'
      refine ⟨semanticBody.inst (.app code.projector major), ?_, ?_⟩
      · rw [view.projectionArgs_succ levels params count major hcode]
        rw [VExpr.consumeForalls?_append, hconsumeDomain]
        rfl
      · rw [view.projectionArgs_succ levels params count major hcode]
        exact hspine.snoc hprojectorField

/-- A certified projector is typed by the exact constructor-telescope domain
exposed after substituting all earlier projections. -/
theorem ProgramsWF.projector_hasType_field
    {view : VStructureView} {env : VEnv}
    (self : view.ProgramsWF env) (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} {levels : List VLevel}
    {params : List VExpr} {idx : Nat} {code : ProjectionCode}
    (hΓ : OnCtx Γ (env.IsType U))
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (hcode : (view.projectionCodes levels params)[idx]? = some code)
    {major : VExpr}
    (hmajor : env.HasType U Γ major (view.structureType levels params)) :
    ∃ field typeBody,
      (view.specializedFields levels params)[idx]? = some field ∧
      code.typeFn = .lam (view.structureType levels params) typeBody ∧
      env.HasType U Γ (.app code.projector major)
        (field.instRevAt (view.projectionArgs levels params idx major) 0) := by
  have hprojector := self hΓ hlevels hlevelsLength hparamsLength
    hparamsSpine hcode
  exact projector_hasType_field_of_type henv hΓ hcode hprojector hmajor

private theorem ProgramsWF.projectionArgsSpineAux
    {view : VStructureView} {env : VEnv}
    (self : view.ProgramsWF env) (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} {levels : List VLevel}
    {params : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U))
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    {major : VExpr}
    (hmajor : env.HasType U Γ major (view.structureType levels params))
    (tailResult : VExpr) :
    ∀ {count : Nat},
      count ≤ (view.specializedFields levels params).length →
      ∃ cursor,
        VExpr.consumeForalls?
            (VExpr.forallN (view.specializedFields levels params) tailResult)
            (view.projectionArgs levels params count major) = some cursor ∧
          env.SpineWF U Γ
            (VExpr.forallN (view.specializedFields levels params) tailResult)
            (view.projectionArgs levels params count major) cursor := by
  intro count hcount
  induction count with
  | zero =>
      exact ⟨_, rfl, .nil⟩
  | succ count ih =>
      have hcountLt : count <
          (view.specializedFields levels params).length := by omega
      have hcodeIdx : count <
          (view.projectionCodes levels params).length := by
        simpa using hcountLt
      let code := (view.projectionCodes levels params)[count]
      have hcode :
          (view.projectionCodes levels params)[count]? = some code :=
        List.getElem?_eq_getElem hcodeIdx
      have hargsLength :
          (view.projectionArgs levels params count major).length = count :=
        view.projectionArgs_length levels params count major
          (Nat.le_of_lt hcodeIdx)
      obtain ⟨cursor, hconsume, hspine⟩ :=
        ih (Nat.le_of_lt hcountLt)
      obtain ⟨field, semanticBody, hfield, hconsumeDomain⟩ :=
        VExpr.consumeForalls?_forallN_domain
          (view.specializedFields levels params) tailResult
          (view.projectionArgs levels params count major)
          (by simpa [hargsLength] using hcountLt)
      have hcursorShape : cursor =
          .forallE
            (field.instRevAt
              (view.projectionArgs levels params count major) 0)
            semanticBody :=
        Option.some.inj (hconsume.symm.trans hconsumeDomain)
      subst cursor
      obtain ⟨field', _, hfield', _, hprojectorField⟩ :=
        self.projector_hasType_field henv hΓ hlevels hlevelsLength
          hparamsLength hparamsSpine hcode hmajor
      have hfieldEq : field' = field :=
        Option.some.inj
          (hfield'.symm.trans (by simpa [hargsLength] using hfield))
      subst field'
      refine ⟨semanticBody.inst (.app code.projector major), ?_, ?_⟩
      · rw [view.projectionArgs_succ levels params count major hcode]
        rw [VExpr.consumeForalls?_append, hconsumeDomain]
        rfl
      · rw [view.projectionArgs_succ levels params count major hcode]
        exact hspine.snoc hprojectorField

/-- All canonical generated projections of a well-typed major form a single
well-typed dependent constructor-field spine.  This theorem deliberately
stops at typing: it does not assert structure eta. -/
theorem ProgramsWF.projectionArgsSpine
    {view : VStructureView} {env : VEnv}
    (self : view.ProgramsWF env) (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} {levels : List VLevel}
    {params : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U))
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    {major : VExpr}
    (hmajor : env.HasType U Γ major (view.structureType levels params))
    (tailResult : VExpr) :
    env.SpineWF U Γ
      (VExpr.forallN (view.specializedFields levels params) tailResult)
      (view.projectionArgs levels params
        (view.specializedFields levels params).length major)
      (VExpr.instRev tailResult
        (view.projectionArgs levels params
          (view.specializedFields levels params).length major)) := by
  obtain ⟨_, _, hspine⟩ := self.projectionArgsSpineAux henv hΓ hlevels
    hlevelsLength hparamsLength hparamsSpine hmajor tailResult
    (Nat.le_refl _)
  apply hspine.retarget
  · exact view.projectionArgs_length levels params
      (view.specializedFields levels params).length major (by simp)

/-- Applying the complete canonical projection spine to a constructor prefix
is well typed.  The constructor-prefix premise is kept explicit so this
lemma remains independent of any proposed structure-eta equality rule. -/
theorem ProgramsWF.etaRebuild_hasType_of_constructorPrefix
    {view : VStructureView} {env : VEnv}
    (self : view.ProgramsWF env) (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} {levels : List VLevel}
    {params : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U))
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    {major : VExpr}
    (hmajor : env.HasType U Γ major (view.structureType levels params))
    (hconstructorPrefix : env.HasType U Γ
      (VExpr.appN (.const view.constructorName levels) params)
      (VExpr.forallN (view.specializedFields levels params)
        ((view.structureType levels params).liftN
          (view.specializedFields levels params).length))) :
    env.HasType U Γ (view.etaRebuild levels params major)
      (view.structureType levels params) := by
  have hfields := self.projectionArgsSpine henv hΓ hlevels hlevelsLength
    hparamsLength hparamsSpine hmajor
    ((view.structureType levels params).liftN
      (view.specializedFields levels params).length)
  have hrebuild := hfields.hasType_appN hconstructorPrefix
  let args := view.projectionArgs levels params
    (view.specializedFields levels params).length major
  have hargsLength :
      args.length = (view.specializedFields levels params).length :=
    view.projectionArgs_length levels params
      (view.specializedFields levels params).length major (by simp)
  have hlift :
      (view.structureType levels params).liftN
          (view.specializedFields levels params).length =
        (view.structureType levels params).liftN args.length :=
    congrArg (view.structureType levels params).liftN hargsLength.symm
  have hresult :
      VExpr.instRev
        ((view.structureType levels params).liftN
          (view.specializedFields levels params).length)
        args =
        view.structureType levels params := by
    calc
      _ = VExpr.instRev
          ((view.structureType levels params).liftN args.length) args :=
        congrArg (VExpr.instRev · args) hlift
      _ = view.structureType levels params :=
        VExpr.instRev_liftN_len args _
  rw [hresult] at hrebuild
  simpa [etaRebuild, VExpr.appN_append] using hrebuild

/-- Exact registration of the checked structure artifact in a Theory
environment.  These are concrete lookups and generated iota rules, not an
oracle supplied by a projection consumer. -/
structure Registered (view : VStructureView) (env : VEnv) : Prop where
  family : env.constants view.name =
    some view.generation.block.sourceType.toVConstant
  constructor : env.constants view.constructorName =
    some view.constructor.raw.toVConstant
  recursor : env.constants view.recursorName =
    some view.generation.recursor
  rules : ∀ rule ∈ view.generation.generatedRules, env.defeqs rule

/-- The semantic fragment of `GenerationEnv` that remains monotone under an
arbitrary environment extension.  Ordering is supplied by the structural-law
caller; exact constant/rule registration is carried separately by
`Registered`. -/
structure GenerationSemantics (view : VStructureView) (env : VEnv) : Prop where
  checked : view.generation.block.checked.WF env
  familyTelescope :
    env.TelDefEq view.uvars []
      (view.generation.block.rawParams ++
        view.generation.block.rawIndices)
      (view.generation.block.checked.params ++
        view.generation.block.checked.indices)
  familyResult :
    env.IsDefEq view.uvars
      (view.generation.block.rawParams ++
        view.generation.block.rawIndices).reverse
      view.generation.block.rawResult
      (.sort view.generation.block.checked.resultLevel)
      (.sort (.succ view.generation.block.checked.resultLevel))
  constructor : view.constructor.WF view.generation.block env

/-- Semantic well-formedness of one structure view in its registered
environment.  The retained sort list is checked against the exact raw
dependent field telescope. -/
structure WF (view : VStructureView) (env : VEnv) : Prop
    extends VStructureView.Registered view env where
  generationSemantics : VStructureView.GenerationSemantics view env
  parameters : env.OnTel view.uvars []
    view.generation.block.checked.params
  parameters_length :
    view.generation.block.checked.params.length = view.nparams
  fieldTelescope : env.OnSortTel view.uvars
    view.generation.block.checked.params.reverse
      view.fields view.fieldSorts
  smallFields : view.generation.elimination = .small →
    ∀ level ∈ view.fieldSorts, level = .zero

theorem WF.rule_mem (self : VStructureView.WF view env) {df : VDefEq}
    (h : df ∈ VInductDecl.GenerationChecked.generatedRules view.generation) :
    VEnv.defeqs env df :=
  self.rules df h

/-- The semantic capability required by structure-eta consumers.

`VStructureView.WF` and `ProgramsWF` account for the registered structure
artifact and the typing of its generated projectors.  This property records
only the additional equality that those rule-independent certificates do not
derive: rebuilding every canonical projection is definitionally equal to the
original major premise.  Keeping it as an explicit environment capability
prevents checker verification from silently extending `VEnv.IsDefEq`. -/
def _root_.Lean4Lean.VEnv.HasStructureEta (env : VEnv) : Prop :=
  ∀ (view : VStructureView), view.WF env → view.ProgramsWF env →
    ∀ {U : Nat} {Γ : List VExpr} {levels : List VLevel}
      {params : List VExpr} {major : VExpr},
      OnCtx Γ (env.IsType U) →
      (∀ level ∈ levels, level.WF U) →
      levels.length = view.uvars →
      params.length = view.nparams →
      (∃ resultLevel, env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel)) →
      env.HasType U Γ major (view.structureType levels params) →
      env.IsDefEq U Γ (view.etaRebuild levels params major) major
        (view.structureType levels params)

theorem Registered.mono {env env' : VEnv} (henv : env ≤ env')
    (self : VStructureView.Registered view env) :
    VStructureView.Registered view env' where
  family := henv.1 self.family
  constructor := henv.1 self.constructor
  recursor := henv.1 self.recursor
  rules := fun rule hrule => henv.2 (self.rules rule hrule)

theorem GenerationSemantics.mono {env env' : VEnv} (henv : env ≤ env')
    (self : VStructureView.GenerationSemantics view env) :
    VStructureView.GenerationSemantics view env' where
  checked := self.checked.mono henv
  familyTelescope := self.familyTelescope.mono henv
  familyResult := self.familyResult.mono henv
  constructor := self.constructor.mono henv

/-- Recover the monotone semantic fragment of a generated structure from the
ordinary generation certificate and the exact successful transaction trace. -/
theorem GenerationSemantics.ofGenerationTrace {pre env : VEnv}
    (hgen : view.generation.WF pre)
    (trace : VEnv.AddInductGenerationTrace pre env view.generation) :
    VStructureView.GenerationSemantics view env := by
  have htypeFinal : trace.typeEnv ≤ env := by
    have hctors :=
      (ctorFold_spec view.generation.block.sourceType.ctors
        trace.addCtors).1
    have hrec := VEnv.addConst_le trace.addRec
    have hrules : trace.recEnv ≤ env := by
      simpa only [trace.addRules] using
        (rulesFold_spec view.generation.generatedRules trace.recEnv).1
    exact hctors.trans (hrec.trans hrules)
  have hpreFinal := trace.le
  refine {
    checked := hgen.blockWF.2.mono hpreFinal
    familyTelescope := hgen.familyTel.mono hpreFinal
    familyResult := hgen.familyResult.mono hpreFinal
    constructor := ?_ }
  have hconstructor :
      view.constructor ∈ view.generation.block.ctorPairs := by
    simp [view.constructor_eq]
  exact (hgen.ctors trace.typeEnv trace.addType view.constructor
    hconstructor).mono htypeFinal

theorem WF.mono {env env' : VEnv} (henv : env ≤ env')
    (self : VStructureView.WF view env) : VStructureView.WF view env' where
  toRegistered := self.toRegistered.mono henv
  generationSemantics := self.generationSemantics.mono henv
  parameters := self.parameters.monoProjection henv
  parameters_length := self.parameters_length
  fieldTelescope := self.fieldTelescope.mono henv
  smallFields := self.smallFields

/-- Reassemble the standard generated-artifact invariant when an ordered
environment is available. -/
theorem WF.toGenerationEnv (self : VStructureView.WF view env)
    (henv : env.Ordered) :
    VInductDecl.GenerationEnv view.generation env where
  ord := henv
  checked := self.generationSemantics.checked
  familyTel := self.generationSemantics.familyTelescope
  familyResult := self.generationSemantics.familyResult
  ctorWF := by
    intro ctor hctor
    rw [view.constructor_eq] at hctor
    simp only [List.mem_singleton] at hctor
    subst ctor
    exact self.generationSemantics.constructor
  familyConst := self.family
  ctorConst := by
    intro ctor hctor
    rw [view.constructor_eq] at hctor
    simp only [List.mem_singleton] at hctor
    subst ctor
    exact self.constructor

theorem WF.field_closed (self : VStructureView.WF view env)
    (henv : env.Ordered) {i : Nat} {field : VExpr}
    (hfield : view.fields[i]? = some field) :
    field.ClosedN (view.nparams + i) := by
  have hparamsCtx : OnCtx
      view.generation.block.checked.params.reverse
      (env.IsType view.uvars) :=
    by simpa using VEnv.OnTel.toOnCtx self.parameters (by trivial)
  have hclosed := VEnv.OnSortTel.closedAt henv self.fieldTelescope
    (VEnv.CtxWF.closed henv hparamsCtx) hfield
  simpa [self.parameters_length] using hclosed

theorem WF.specializedFields_liftN
    (self : VStructureView.WF view env) (henv : env.Ordered)
    (levels : List VLevel) (params : List VExpr)
    (hparams : params.length = view.nparams) (n k : Nat) :
    view.specializedFields levels
        (params.map fun param => param.liftN n k) =
      VExpr.liftTelN n (view.specializedFields levels params) k := by
  simpa [specializedFields] using
    specializedFieldsAux_liftN view.fields levels params view.nparams
      0 n k hparams
      (fun j field hfield => by
        simpa using self.field_closed henv hfield)

theorem WF.specializedFields_instN
    (self : VStructureView.WF view env) (henv : env.Ordered)
    (levels : List VLevel) (params : List VExpr)
    (hparams : params.length = view.nparams) (a : VExpr) (k : Nat) :
    view.specializedFields levels
        (params.map fun param => param.inst a k) =
      VExpr.instTelN a (view.specializedFields levels params) k := by
  simpa [specializedFields] using
    specializedFieldsAux_instN view.fields levels params view.nparams
      0 k a hparams
      (fun j field hfield => by
        simpa using self.field_closed henv hfield)

private theorem projectionLevels_length (view : VStructureView)
    (fieldSort : VLevel) (levels : List VLevel)
    (hlevels : levels.length = view.uvars) :
    (view.projectionLevels fieldSort levels).length =
      view.generation.recUvars := by
  unfold projectionLevels
  cases h : view.generation.elimination <;>
    simp [VInductDecl.GenerationChecked.recUvars,
      VInductDecl.ElimMode.recUvars, h, hlevels]

private theorem projectionLevels_wf (view : VStructureView)
    {U : Nat} (fieldSort : VLevel) (levels : List VLevel)
    (hfieldSort : fieldSort.WF U)
    (hlevels : ∀ level ∈ levels, level.WF U) :
    ∀ level ∈ view.projectionLevels fieldSort levels, level.WF U := by
  unfold projectionLevels
  cases view.generation.elimination <;> simp_all

private theorem sourceLevels_projectionLevels (view : VStructureView)
    (fieldSort : VLevel) (levels : List VLevel)
    (hlevels : levels.length = view.uvars) :
    view.generation.sourceLevels.map
        (VLevel.inst (view.projectionLevels fieldSort levels)) = levels := by
  unfold VInductDecl.GenerationChecked.sourceLevels
  unfold VInductDecl.ElimMode.sourceLevels projectionLevels
  cases h : view.generation.elimination
  ·
    change (VLevel.params' view.uvars 1).map
      (VLevel.inst (fieldSort :: levels)) = levels
    have hshift :
        (VLevel.params' view.uvars 1).map
            (VLevel.inst (fieldSort :: levels)) =
          (VLevel.params view.uvars).map (VLevel.inst levels) := by
      simp [VLevel.params', VLevel.params, List.map_map,
        Function.comp_def, VLevel.inst,
        List.getD_eq_getElem?_getD]
    rw [hshift]
    exact VLevel.inst_map_id hlevels
  ·
    change (VLevel.params' view.uvars 0).map
      (VLevel.inst levels) = levels
    have hzero : VLevel.params' view.uvars 0 =
        VLevel.params view.uvars := by
      simp [VLevel.params', VLevel.params]
    rw [hzero]
    exact VLevel.inst_map_id hlevels

private theorem motiveLevel_projectionLevels (view : VStructureView)
    (fieldSort : VLevel) (levels : List VLevel) :
    view.generation.motiveLevel.inst
        (view.projectionLevels fieldSort levels) =
      match view.generation.elimination with
      | .large => fieldSort
      | .small => .zero := by
  unfold VInductDecl.GenerationChecked.motiveLevel
  unfold VInductDecl.ElimMode.motiveLevel projectionLevels
  cases view.generation.elimination <;> rfl

private theorem WF.motiveLevel_projectionLevels
    (self : VStructureView.WF view env)
    (fieldSort : VLevel) (hfieldSort : fieldSort ∈ view.fieldSorts)
    (levels : List VLevel) :
    view.generation.motiveLevel.inst
        (view.projectionLevels (fieldSort.inst levels) levels) =
      fieldSort.inst levels := by
  rw [VStructureView.motiveLevel_projectionLevels]
  cases hmode : view.generation.elimination with
  | large => rfl
  | small =>
      rw [self.smallFields hmode fieldSort hfieldSort]
      rfl

@[simp] theorem WF.projectionCodes_liftN
    (self : VStructureView.WF view env) (henv : env.Ordered)
    (levels : List VLevel) (params : List VExpr)
    (hparams : params.length = view.nparams) (n k : Nat) :
    (view.projectionCodes levels params).map
        (fun code => code.liftN n k) =
      view.projectionCodes levels
        (params.map fun param => param.liftN n k) := by
  unfold projectionCodes
  rw [self.specializedFields_liftN henv levels params hparams n k]
  rw [← structureType_liftN]
  apply projectionCodes.go_liftN
  · rfl
  · simp

@[simp] theorem WF.projectionCodes_instN
    (self : VStructureView.WF view env) (henv : env.Ordered)
    (levels : List VLevel) (params : List VExpr)
    (hparams : params.length = view.nparams) (a : VExpr) (k : Nat) :
    (view.projectionCodes levels params).map
        (fun code => code.instN a k) =
      view.projectionCodes levels
        (params.map fun param => param.inst a k) := by
  unfold projectionCodes
  rw [self.specializedFields_instN henv levels params hparams a k]
  rw [← structureType_instN]
  apply projectionCodes.go_instN
  · rfl
  · simp

/-- The exact lower-layer structure-eta descriptor generated by a checked
structure view.  Its projector syntax is the deterministic projector program
list already certified by the view; the proof fields are only the three
syntactic naturality laws required by Theory transport. -/
def WF.toStructEta (self : VStructureView.WF view env)
    (henv : env.Ordered) : VStructEta where
  uvars := view.uvars
  nparams := view.nparams
  nfields := view.fields.length
  familyName := view.name
  familyType := view.familyType
  constructorName := view.constructorName
  projectors := fun levels params =>
    (view.projectionCodes levels params).map (·.projector)
  projectors_length := by
    intro levels params _ _
    simp [VStructureView.specializedFields, VStructureView.fields]
  projectors_liftN := by
    intro levels params n k hparams
    have h := self.projectionCodes_liftN henv levels params hparams n k
    simpa [List.map_map, ProjectionCode.liftN, Function.comp_def] using
      congrArg (List.map (·.projector)) h
  projectors_instN := by
    intro levels params a k hparams
    have h := self.projectionCodes_instN henv levels params hparams a k
    simpa [List.map_map, ProjectionCode.instN, Function.comp_def] using
      congrArg (List.map (·.projector)) h
  projectors_instL := by
    intro levels params ls
    have h := projectionCodes_instL view levels params ls
    simpa [List.map_map, ProjectionCode.instL, Function.comp_def] using
      congrArg (List.map (·.projector)) h

@[simp] theorem WF.toStructEta_structureType
    (self : VStructureView.WF view env) (henv : env.Ordered)
    (levels : List VLevel) (params : List VExpr) :
    (self.toStructEta henv).structureType levels params =
      view.structureType levels params := rfl

@[simp] theorem WF.toStructEta_rebuild
    (self : VStructureView.WF view env) (henv : env.Ordered)
    (levels : List VLevel) (params : List VExpr) (major : VExpr) :
    (self.toStructEta henv).rebuild levels params major =
      view.etaRebuild levels params major := by
  simp only [VStructEta.rebuild, VStructEta.projectionArgs, WF.toStructEta,
    VStructureView.etaRebuild, VStructureView.projectionArgs]
  rw [← view.projectionCodes_length levels params, List.take_length]
  simp [List.map_map, Function.comp_def]

end VStructureView

namespace VEnv

/-- Registered checked views supply the former semantic structure-eta
capability.  The registry contributes only membership; subject reduction is
recovered from the well-formed environment history, and the equality itself
is the primitive `IsDefEq.structEta` step. -/
theorem hasStructureEta_of_registry (henv : env.WF)
    (registered : ∀ (view : VStructureView)
      (hview : view.WF env) (_ : view.ProgramsWF env),
      env.structEtas (hview.toStructEta henv.ordered)) :
    env.HasStructureEta := by
  intro view hview programs U Γ levels params major hΓ hlevels
    hlevelsLength hparamsLength hparamsSpine hmajor
  let rule := hview.toStructEta henv.ordered
  have hregistered : env.structEtas rule := registered view hview programs
  have hruleWF : rule.WF env := henv.structEtaWF hregistered
  obtain ⟨resultLevel, hparamsSpine⟩ := hparamsSpine
  have hrebuild := hruleWF.rebuild_hasType VEnv.LE.rfl
    henv.conversionRegular hΓ hlevels
    hlevelsLength hparamsLength ⟨resultLevel, hparamsSpine⟩ hmajor
  have heta := IsDefEq.structEta hregistered hlevels hlevelsLength
    hparamsLength hparamsSpine hmajor hrebuild
  simpa [rule] using heta

private theorem SpineWF.monoProjection {env env' : VEnv}
    (henv : env ≤ env') :
    ∀ {A es B}, env.SpineWF U Γ A es B → env'.SpineWF U Γ A es B
  | _, _, _, h => h.mono henv

/-- The view-facing direction of `TelDefEq.spine_sort`: arguments checked
against the retained raw telescope also consume its definitionally equal
view telescope. -/
theorem TelDefEq.spine_sort_view
    {env : VEnv} {U : Nat} (henv : env.Ordered) :
    ∀ {Γ As As' es l}, env.TelDefEq U Γ As As' →
      env.SpineWF U Γ (VExpr.forallN As (.sort l)) es (.sort l) →
      es.length = As.length →
      env.SpineWF U Γ (VExpr.forallN As' (.sort l)) es (.sort l)
  | _, [], [], [], _, _, hspine, _ => by simpa using hspine
  | _, [], [], _ :: _, _, _, _, hlen => by simp at hlen
  | Γ, A :: As, A' :: As', e :: es, l, ⟨⟨_, hA⟩, hT⟩,
      .cons he hrest, hlen => by
    have heView : env.HasType U Γ e A' := hA.defeq he
    have hTinst := TelDefEq.instN henv he (.zero) hT
    have hrest' : env.SpineWF U Γ
        (VExpr.forallN (VExpr.instTelN e As 0) (.sort l))
        es (.sort l) := by
      simpa [VExpr.instN_forallN, VExpr.inst] using hrest
    have hlen' : es.length = As.length := by simpa using hlen
    have hlenInst :
        es.length = (VExpr.instTelN e As 0).length := by
      rw [VExpr.instTelN_length]
      exact hlen'
    have hout := TelDefEq.spine_sort_view henv
      hTinst hrest' hlenInst
    refine .cons heView ?_
    simpa [VExpr.instN_forallN, VExpr.inst] using hout

/-- Parameters accepted by the structure family also consume the stored raw
constructor parameter prefix.  This is the semantic bridge used by the
kernel projection checker before it traverses the constructor fields. -/
theorem _root_.Lean4Lean.VStructureView.WF.constructorParamsSpine
    (self : VStructureView.WF view env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (_hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (target : VExpr) :
    env.SpineWF U Γ
      (VExpr.forallN
        (view.constructorParams.map (VExpr.instL levels))
        target) params (VExpr.instRev target params) := by
  let S := self.toGenerationEnv henv
  obtain ⟨resultLevel, hspine⟩ := paramsSpine
  have hrawLength :
      view.generation.block.rawParams.length = view.nparams :=
    view.generation.shape.1
  have hspineShape : env.SpineWF U Γ
      (VExpr.forallN
        (view.generation.block.rawParams.map (VExpr.instL levels))
        (view.generation.block.rawResult.instL levels))
      params (.sort resultLevel) := by
    simpa [VStructureView.familyType,
      VInductDecl.NormalizedChecked.rawType_eq,
      view.raw_indices_eq, VExpr.instL_forallN,
      VExpr.forallN] using hspine
  have hparamsRaw : env.SpineWF U Γ
      (VExpr.forallN
        (view.generation.block.rawParams.map (VExpr.instL levels))
        (.sort .zero)) params (.sort .zero) := by
    have hout := hspineShape.retarget
      (by simpa [hrawLength] using hparamsLength) (.sort .zero)
    rw [VExpr.instRev_closedN params (by trivial)] at hout
    exact hout
  have hfamilyDefEq := S.rawParams_defeq.instL hlevels
  have hrawLift : VExpr.liftTelN Γ.length
      (view.generation.block.rawParams.map (VExpr.instL levels)) 0 =
      view.generation.block.rawParams.map (VExpr.instL levels) := by
    simpa using VEnv.OnTel.liftTelN_eq henv
      hfamilyDefEq.raw_onTel (by trivial) Γ.length
  have hcheckedLift : VExpr.liftTelN Γ.length
      (view.generation.block.checked.params.map (VExpr.instL levels)) 0 =
      view.generation.block.checked.params.map (VExpr.instL levels) := by
    simpa using VEnv.OnTel.liftTelN_eq henv
      (hfamilyDefEq.view_onTel henv) (by trivial) Γ.length
  have hfamilyDefEqΓ := hfamilyDefEq.weakN henv
    (Ctx.LiftN.zero (n := Γ.length) (Γ := []) Γ)
  rw [hrawLift, hcheckedLift] at hfamilyDefEqΓ
  simp only [List.append_nil] at hfamilyDefEqΓ
  have hparamsChecked : env.SpineWF U Γ
      (VExpr.forallN
        (view.generation.block.checked.params.map (VExpr.instL levels))
        (.sort .zero)) params (.sort .zero) :=
    TelDefEq.spine_sort_view henv hfamilyDefEqΓ hparamsRaw
      (by simpa [hrawLength] using hparamsLength)
  have hconstructorMem :
      view.constructor ∈ view.generation.block.ctorPairs := by
    simp [view.constructor_eq]
  have hconstructorShape :=
    view.generation.shape.2.2.2.2.2 view.constructor hconstructorMem
  have hconstructorDefEq₀ :=
    ((S.ctorWF view.constructor hconstructorMem).declaredTel.take
      view.nparams).instL hlevels
  have hconstructorDefEq : env.TelDefEq U []
      (view.constructorParams.map (VExpr.instL levels))
      (view.generation.block.checked.params.map (VExpr.instL levels)) := by
    simpa [VStructureView.constructorParams,
      VInductDecl.NormalizedCtor.declaredBinders,
      VInductDecl.NormalizedCtor.viewBinders,
      hconstructorShape.2.2.1, self.parameters_length] using
        hconstructorDefEq₀
  have hconstructorRawLift : VExpr.liftTelN Γ.length
      (view.constructorParams.map (VExpr.instL levels)) 0 =
      view.constructorParams.map (VExpr.instL levels) := by
    simpa using VEnv.OnTel.liftTelN_eq henv
      hconstructorDefEq.raw_onTel (by trivial) Γ.length
  have hconstructorCheckedLift : VExpr.liftTelN Γ.length
      (view.generation.block.checked.params.map (VExpr.instL levels)) 0 =
      view.generation.block.checked.params.map (VExpr.instL levels) :=
    hcheckedLift
  have hconstructorDefEqΓ := hconstructorDefEq.weakN henv
    (Ctx.LiftN.zero (n := Γ.length) (Γ := []) Γ)
  rw [hconstructorRawLift, hconstructorCheckedLift] at hconstructorDefEqΓ
  simp only [List.append_nil] at hconstructorDefEqΓ
  have hout := TelDefEq.spine_sort henv hconstructorDefEqΓ hparamsChecked
    (by simpa [VStructureView.constructorParams] using
      hparamsLength.trans hconstructorShape.2.2.1.symm)
  exact hout.retarget
    (by simpa [VStructureView.constructorParams] using
      hparamsLength.trans hconstructorShape.2.2.1.symm) target

/-- Parameters accepted by the structure family also consume the checked
family-parameter prefix used by mixed constructor generation.  Keeping this
bridge separate from `constructorParamsSpine` lets later consumers apply the
constructor at arbitrary parameters without re-proving the raw/view
parameter alignment. -/
theorem _root_.Lean4Lean.VStructureView.WF.checkedParamsSpine
    (self : VStructureView.WF view env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (target : VExpr) :
    env.SpineWF U Γ
      (VExpr.forallN
        (view.generation.block.checked.params.map (VExpr.instL levels))
        target) params (VExpr.instRev target params) := by
  let S := self.toGenerationEnv henv
  have hconstructorMem :
      view.constructor ∈ view.generation.block.ctorPairs := by
    simp [view.constructor_eq]
  have hconstructorShape :=
    view.generation.shape.2.2.2.2.2 view.constructor hconstructorMem
  have hraw := self.constructorParamsSpine henv levels hlevels
    hlevelsLength params hparamsLength paramsSpine (.sort .zero)
  have hrawLength : params.length =
      (view.constructorParams.map (VExpr.instL levels)).length := by
    simpa [VStructureView.constructorParams] using
      hparamsLength.trans hconstructorShape.2.2.1.symm
  have hrawSort : env.SpineWF U Γ
      (VExpr.forallN
        (view.constructorParams.map (VExpr.instL levels)) (.sort .zero))
      params (.sort .zero) := by
    rw [VExpr.instRev_closedN params (by trivial)] at hraw
    exact hraw
  have hconstructorDefEq₀ :=
    ((S.ctorWF view.constructor hconstructorMem).declaredTel.take
      view.nparams).instL hlevels
  have hconstructorDefEq : env.TelDefEq U []
      (view.constructorParams.map (VExpr.instL levels))
      (view.generation.block.checked.params.map (VExpr.instL levels)) := by
    simpa [VStructureView.constructorParams,
      VInductDecl.NormalizedCtor.declaredBinders,
      VInductDecl.NormalizedCtor.viewBinders,
      hconstructorShape.2.2.1, self.parameters_length] using
        hconstructorDefEq₀
  have hconstructorRawLift : VExpr.liftTelN Γ.length
      (view.constructorParams.map (VExpr.instL levels)) 0 =
      view.constructorParams.map (VExpr.instL levels) := by
    simpa using VEnv.OnTel.liftTelN_eq henv
      hconstructorDefEq.raw_onTel (by trivial) Γ.length
  have hconstructorCheckedLift : VExpr.liftTelN Γ.length
      (view.generation.block.checked.params.map (VExpr.instL levels)) 0 =
      view.generation.block.checked.params.map (VExpr.instL levels) := by
    simpa using VEnv.OnTel.liftTelN_eq henv
      (hconstructorDefEq.view_onTel henv) (by trivial) Γ.length
  have hconstructorDefEqΓ := hconstructorDefEq.weakN henv
    (Ctx.LiftN.zero (n := Γ.length) (Γ := []) Γ)
  rw [hconstructorRawLift, hconstructorCheckedLift] at hconstructorDefEqΓ
  simp only [List.append_nil] at hconstructorDefEqΓ
  have hcheckedSort := VEnv.TelDefEq.spine_sort_view henv
    hconstructorDefEqΓ hrawSort hrawLength
  have hcheckedLength : params.length =
      (view.generation.block.checked.params.map
        (VExpr.instL levels)).length := by
    simpa [self.parameters_length] using hparamsLength
  exact hcheckedSort.retarget hcheckedLength target

/-- The generated constructor, after the exact checked parameter prefix, has
the canonical specialized field telescope and returns the corresponding
structure family application.  This is the constructor half of
rule-independent structure-eta subject reduction. -/
theorem _root_.Lean4Lean.VStructureView.WF.constructorPrefix_hasType
    (self : VStructureView.WF view env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel)) :
    env.HasType U Γ
      (VExpr.appN (.const view.constructorName levels) params)
      (VExpr.forallN (view.specializedFields levels params)
        ((view.structureType levels params).liftN
          (view.specializedFields levels params).length)) := by
  let S := self.toGenerationEnv henv
  let E := view.constructor.emittedBinders view.generation.block
  let V := view.constructor.viewBinders view.generation.block
  have hconstructorMem :
      view.constructor ∈ view.generation.block.ctorPairs := by
    simp [view.constructor_eq]
  have hc : env.HasType view.uvars []
      (.const view.constructorName (VLevel.params view.uvars))
      (VExpr.forallN
        (view.constructor.declaredBinders view.nparams)
        (view.constructor.rawResult view.nparams)) := by
    rw [← view.constructor.rawType_eq]
    exact S.ctorConst_decl hconstructorMem
  obtain ⟨_, hdecl⟩ :=
    (S.ctorWF view.constructor hconstructorMem).declaredTel.forallN_defeq
      (by simpa using
        (S.ctorWF view.constructor hconstructorMem).declaredResult)
  have hview : env.HasType view.uvars []
      (.const view.constructorName (VLevel.params view.uvars))
      (VExpr.forallN V
        (view.constructor.resultTarget view.generation.block)) := by
    simpa [V] using hdecl.defeq hc
  have hresult : env.HasType view.uvars E.reverse
      (view.constructor.resultTarget view.generation.block)
      (.sort view.generation.block.checked.resultLevel) := by
    simpa [E] using
      (S.ctorWF view.constructor hconstructorMem).emittedResult.hasType.2
  obtain ⟨_, hemit⟩ :=
    (S.ctorWF view.constructor hconstructorMem).emittedTel.forallN_defeq
      (by simpa [E, VEnv.HasType] using hresult)
  have hcE₀ : env.HasType view.uvars []
      (.const view.constructorName (VLevel.params view.uvars))
      (VExpr.forallN E
        (view.constructor.resultTarget view.generation.block)) := by
    exact hemit.defeq' (by simpa [V] using hview)
  have hcE := hcE₀.instL (U' := U) hlevels
  have hlevelIdentity :
      (VLevel.params view.uvars).map (VLevel.inst levels) = levels :=
    VLevel.inst_map_id hlevelsLength
  rw [show
      ((.const view.constructorName (VLevel.params view.uvars) : VExpr).instL
        levels) = .const view.constructorName levels by
        simp only [VExpr.instL, hlevelIdentity]] at hcE
  have hcE' : env.HasType U []
      (.const view.constructorName levels)
      ((VExpr.forallN E
        (view.constructor.resultTarget view.generation.block)).instL levels) := by
    simpa using hcE
  have hcEΓ : env.HasType U Γ
      (.const view.constructorName levels)
      ((VExpr.forallN E
        (view.constructor.resultTarget view.generation.block)).instL levels) :=
    hcE'.weak0 henv
  let htarget : VExpr :=
    VExpr.forallN
      (view.constructor.rawFields view.nparams |>.map (VExpr.instL levels))
      ((view.constructor.resultTarget view.generation.block).instL levels)
  have hparams := self.checkedParamsSpine henv levels hlevels
    hlevelsLength params hparamsLength paramsSpine htarget
  have hcEΓ' : env.HasType U Γ
      (.const view.constructorName levels)
      (VExpr.forallN
        (view.generation.block.checked.params.map (VExpr.instL levels))
        htarget) := by
    simpa [E, htarget, VInductDecl.NormalizedCtor.emittedBinders,
      VExpr.instL_forallN, VExpr.forallN_append,
      List.map_append] using hcEΓ
  have hprefix := hparams.hasType_appN hcEΓ'
  have hprefix' : env.HasType U Γ
      (VExpr.appN (.const view.constructorName levels) params)
      (VExpr.forallN (view.specializedFields levels params)
        ((view.constructor.resultTarget view.generation.block).instL levels
          |>.instRevAt params
            (view.constructor.rawFields view.nparams).length)) := by
    simpa [htarget, VExpr.instRev_forallN_projection,
      VStructureView.specializedFields, VStructureView.fields,
      VExpr.instRevAt_map_instL_zipIdx] using hprefix
  have hparamsRange :
      (VExpr.bvarRevRange
          (view.constructor.rawFields view.nparams).length view.nparams).map
          (fun expression => expression.instRevAt params
            (view.constructor.rawFields view.nparams).length) =
        params.map (VExpr.liftN
          (view.constructor.rawFields view.nparams).length) := by
    have h := VExpr.map_instRevAt_bvarRevRange params
      (view.constructor.rawFields view.nparams).length
    rw [hparamsLength] at h
    exact h
  have hresultIndices : view.constructor.view.resultIndices = [] := by
    apply List.length_eq_zero_iff.1
    rw [S.viewResultIndices_length hconstructorMem]
    simp [view.checked_indices_eq]
  have htail :
      ((view.constructor.resultTarget view.generation.block).instL levels
        |>.instRevAt params
          (view.constructor.rawFields view.nparams).length) =
        (view.structureType levels params).liftN
          (view.constructor.rawFields view.nparams).length := by
    rw [VInductDecl.NormalizedCtor.resultTarget,
      VExpr.instL_appN, VExpr.instRevAt_appN_projection]
    rw [VExpr.instRevAt_closedN params (by trivial)]
    simp only [VExpr.instL, hlevelIdentity,
      hresultIndices, List.append_nil,
      VExpr.bvarRevRange_map_instL, hparamsRange]
    rw [VStructureView.structureType, VExpr.liftN_appN]
    simp [VExpr.liftN]
  rw [htail] at hprefix'
  simpa [VStructureView.specializedFields, VStructureView.fields] using
    hprefix'

/-- Recover the structure-family parameter spine from the corresponding
constructor-parameter prefix.  This is the converse consumer bridge needed
when a checker recognizes a fully applied constructor before it knows the
family application carried by its result type. -/
theorem _root_.Lean4Lean.VStructureView.WF.familyParamsSpine_of_constructor
    (self : VStructureView.WF view env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (_hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    {target cursor : VExpr}
    (constructorSpine : env.SpineWF U Γ
      (VExpr.forallN
        (view.constructorParams.map (VExpr.instL levels)) target)
      params cursor)
    (resultLevel : VLevel)
    (hresult : view.generation.block.rawResult = .sort resultLevel) :
    env.SpineWF U Γ (view.familyType.instL levels) params
      (.sort (resultLevel.inst levels)) := by
  let S := self.toGenerationEnv henv
  have hrawLength :
      view.generation.block.rawParams.length = view.nparams :=
    view.generation.shape.1
  have hconstructorMem :
      view.constructor ∈ view.generation.block.ctorPairs := by
    simp [view.constructor_eq]
  have hconstructorShape :=
    view.generation.shape.2.2.2.2.2 view.constructor hconstructorMem
  have hconstructorLength : params.length =
      (view.constructorParams.map (VExpr.instL levels)).length := by
    simpa [VStructureView.constructorParams] using
      hparamsLength.trans hconstructorShape.2.2.1.symm
  have hparamsConstructor : env.SpineWF U Γ
      (VExpr.forallN
        (view.constructorParams.map (VExpr.instL levels)) (.sort .zero))
      params (.sort .zero) := by
    have hout := constructorSpine.retarget hconstructorLength (.sort .zero)
    rw [VExpr.instRev_closedN params (by trivial)] at hout
    exact hout
  have hfamilyDefEq := S.rawParams_defeq.instL hlevels
  have hrawLift : VExpr.liftTelN Γ.length
      (view.generation.block.rawParams.map (VExpr.instL levels)) 0 =
      view.generation.block.rawParams.map (VExpr.instL levels) := by
    simpa using VEnv.OnTel.liftTelN_eq henv
      hfamilyDefEq.raw_onTel (by trivial) Γ.length
  have hcheckedLift : VExpr.liftTelN Γ.length
      (view.generation.block.checked.params.map (VExpr.instL levels)) 0 =
      view.generation.block.checked.params.map (VExpr.instL levels) := by
    simpa using VEnv.OnTel.liftTelN_eq henv
      (hfamilyDefEq.view_onTel henv) (by trivial) Γ.length
  have hfamilyDefEqΓ := hfamilyDefEq.weakN henv
    (Ctx.LiftN.zero (n := Γ.length) (Γ := []) Γ)
  rw [hrawLift, hcheckedLift] at hfamilyDefEqΓ
  simp only [List.append_nil] at hfamilyDefEqΓ
  have hconstructorDefEq₀ :=
    ((S.ctorWF view.constructor hconstructorMem).declaredTel.take
      view.nparams).instL hlevels
  have hconstructorDefEq : env.TelDefEq U []
      (view.constructorParams.map (VExpr.instL levels))
      (view.generation.block.checked.params.map (VExpr.instL levels)) := by
    simpa [VStructureView.constructorParams,
      VInductDecl.NormalizedCtor.declaredBinders,
      VInductDecl.NormalizedCtor.viewBinders,
      hconstructorShape.2.2.1, self.parameters_length] using
        hconstructorDefEq₀
  have hconstructorRawLift : VExpr.liftTelN Γ.length
      (view.constructorParams.map (VExpr.instL levels)) 0 =
      view.constructorParams.map (VExpr.instL levels) := by
    simpa using VEnv.OnTel.liftTelN_eq henv
      hconstructorDefEq.raw_onTel (by trivial) Γ.length
  have hconstructorDefEqΓ := hconstructorDefEq.weakN henv
    (Ctx.LiftN.zero (n := Γ.length) (Γ := []) Γ)
  rw [hconstructorRawLift, hcheckedLift] at hconstructorDefEqΓ
  simp only [List.append_nil] at hconstructorDefEqΓ
  have hparamsChecked : env.SpineWF U Γ
      (VExpr.forallN
        (view.generation.block.checked.params.map (VExpr.instL levels))
        (.sort .zero)) params (.sort .zero) :=
    VEnv.TelDefEq.spine_sort_view henv hconstructorDefEqΓ
      hparamsConstructor hconstructorLength
  have hrawParamsLength : params.length =
      (view.generation.block.rawParams.map (VExpr.instL levels)).length := by
    simpa [hrawLength] using hparamsLength
  have hparamsRaw : env.SpineWF U Γ
      (VExpr.forallN
        (view.generation.block.rawParams.map (VExpr.instL levels))
        (.sort .zero)) params (.sort .zero) :=
    VEnv.TelDefEq.spine_sort henv hfamilyDefEqΓ hparamsChecked
      hrawParamsLength
  have hout := hparamsRaw.retarget hrawParamsLength
    (.sort (resultLevel.inst levels))
  rw [VExpr.instRev_closedN params (by trivial)] at hout
  simpa [VStructureView.familyType,
    VInductDecl.NormalizedChecked.rawType_eq,
    view.raw_indices_eq, hresult, VExpr.instL_forallN,
    VExpr.forallN, VExpr.instL] using hout

theorem _root_.Lean4Lean.VStructureView.WF.specializedFields_onSortTel
    (self : VStructureView.WF view env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (_hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel)) :
    env.OnSortTel U Γ (view.specializedFields levels params)
      (view.fieldSorts.map (VLevel.inst levels)) := by
  let S := self.toGenerationEnv henv
  obtain ⟨resultLevel, hspine⟩ := paramsSpine
  have hrawLength :
      view.generation.block.rawParams.length = view.nparams :=
    view.generation.shape.1
  have hspineShape : env.SpineWF U Γ
      (VExpr.forallN
        (view.generation.block.rawParams.map (VExpr.instL levels))
        (view.generation.block.rawResult.instL levels))
      params (.sort resultLevel) := by
    simpa [VStructureView.familyType,
      VInductDecl.NormalizedChecked.rawType_eq,
      view.raw_indices_eq, VExpr.instL_forallN,
      VExpr.forallN] using hspine
  have hparamsRaw : env.SpineWF U Γ
      (VExpr.forallN
        (view.generation.block.rawParams.map (VExpr.instL levels))
        (.sort resultLevel)) params (.sort resultLevel) := by
    have hout := hspineShape.retarget
      (by simpa [hrawLength] using hparamsLength)
      (.sort resultLevel)
    rw [VExpr.instRev_closedN params (by trivial)] at hout
    exact hout
  have hrawChecked := S.rawParams_defeq.instL hlevels
  have hrawLift := VEnv.OnTel.liftTelN_eq henv
    hrawChecked.raw_onTel (by trivial) Γ.length
  have hcheckedLift := VEnv.OnTel.liftTelN_eq henv
    (hrawChecked.view_onTel henv) (by trivial) Γ.length
  have hrawLift' : VExpr.liftTelN Γ.length
      (view.generation.block.rawParams.map (VExpr.instL levels)) 0 =
      view.generation.block.rawParams.map (VExpr.instL levels) := by
    simpa using hrawLift
  have hcheckedLift' : VExpr.liftTelN Γ.length
      (view.generation.block.checked.params.map (VExpr.instL levels)) 0 =
      view.generation.block.checked.params.map (VExpr.instL levels) := by
    simpa using hcheckedLift
  have hrawCheckedΓ := hrawChecked.weakN henv
    (Ctx.LiftN.zero (n := Γ.length) (Γ := []) Γ)
  rw [hrawLift', hcheckedLift'] at hrawCheckedΓ
  simp only [List.append_nil] at hrawCheckedΓ
  have hparamsChecked : env.SpineWF U Γ
      (VExpr.forallN
        (view.generation.block.checked.params.map
          (VExpr.instL levels)) (.sort resultLevel))
      params (.sort resultLevel) := by
    exact TelDefEq.spine_sort_view henv hrawCheckedΓ hparamsRaw
      (by simpa [hrawLength] using hparamsLength)
  have hfields := self.fieldTelescope.instL hlevels
  have hcheckedParams := self.parameters.instL hlevels
  have Wparams := Ctx.LiftN.consTel
    (view.generation.block.checked.params.map (VExpr.instL levels))
    (Ctx.LiftN.zero (n := Γ.length) (Γ := []) Γ)
  rw [hcheckedLift'] at Wparams
  have hcheckedCtx : OnCtx
      (view.generation.block.checked.params.reverse.map
        (VExpr.instL levels)) (env.IsType U) := by
    simpa [List.map_reverse] using
      VEnv.OnTel.toOnCtx hcheckedParams (by trivial)
  have hfieldLift := VEnv.OnSortTel.liftTelN_eq henv hfields
    (VEnv.CtxWF.closed henv hcheckedCtx) Γ.length
  have hfieldsΓ := VEnv.OnSortTel.weakN henv
    (by simpa [List.map_reverse] using Wparams) hfields
  simp only [List.length_reverse, List.length_map] at hfieldLift
  rw [hfieldLift] at hfieldsΓ
  have hspecialized := VEnv.OnSortTel.instRevParams henv
    hparamsChecked (by simpa [self.parameters_length] using hparamsLength)
    (by simpa [List.map_reverse] using hfieldsΓ)
  rw [VExpr.instRevAt_map_instL_zipIdx] at hspecialized
  simpa [VStructureView.specializedFields] using hspecialized

private theorem _root_.Lean4Lean.VStructureView.WF.generationParamsSpine
    (self : VStructureView.WF view env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (fieldSort : VLevel) :
    env.SpineWF U Γ
      (VExpr.forallN
        (view.generation.paramsTel.map
          (VExpr.instL
            (view.projectionLevels fieldSort levels)))
        (.sort fieldSort)) params (.sort fieldSort) := by
  let S := self.toGenerationEnv henv
  obtain ⟨resultLevel, hspine⟩ := paramsSpine
  have hrawLength :
      view.generation.block.rawParams.length = view.nparams :=
    view.generation.shape.1
  have hspineShape : env.SpineWF U Γ
      (VExpr.forallN
        (view.generation.block.rawParams.map (VExpr.instL levels))
        (view.generation.block.rawResult.instL levels))
      params (.sort resultLevel) := by
    simpa [VStructureView.familyType,
      VInductDecl.NormalizedChecked.rawType_eq,
      view.raw_indices_eq, VExpr.instL_forallN,
      VExpr.forallN] using hspine
  have hparamsRaw : env.SpineWF U Γ
      (VExpr.forallN
        (view.generation.block.rawParams.map (VExpr.instL levels))
        (.sort fieldSort)) params (.sort fieldSort) := by
    have hout := hspineShape.retarget
      (by simpa [hrawLength] using hparamsLength) (.sort fieldSort)
    rw [VExpr.instRev_closedN params (by trivial)] at hout
    exact hout
  have hrawChecked := S.rawParams_defeq.instL hlevels
  have hrawLift : VExpr.liftTelN Γ.length
      (view.generation.block.rawParams.map (VExpr.instL levels)) 0 =
      view.generation.block.rawParams.map (VExpr.instL levels) := by
    simpa using VEnv.OnTel.liftTelN_eq henv
      hrawChecked.raw_onTel (by trivial) Γ.length
  have hcheckedLift : VExpr.liftTelN Γ.length
      (view.generation.block.checked.params.map (VExpr.instL levels)) 0 =
      view.generation.block.checked.params.map (VExpr.instL levels) := by
    simpa using VEnv.OnTel.liftTelN_eq henv
      (hrawChecked.view_onTel henv) (by trivial) Γ.length
  have hrawCheckedΓ := hrawChecked.weakN henv
    (Ctx.LiftN.zero (n := Γ.length) (Γ := []) Γ)
  rw [hrawLift, hcheckedLift] at hrawCheckedΓ
  simp only [List.append_nil] at hrawCheckedΓ
  have hparamsChecked : env.SpineWF U Γ
      (VExpr.forallN
        (view.generation.block.checked.params.map
          (VExpr.instL levels)) (.sort fieldSort))
      params (.sort fieldSort) :=
    TelDefEq.spine_sort_view henv hrawCheckedΓ hparamsRaw
      (by simpa [hrawLength] using hparamsLength)
  have hgenerationChecked := S.generationParams_defeq.instL hlevels
  have hgenerationLift : VExpr.liftTelN Γ.length
      (view.generation.block.generationParams.map
        (VExpr.instL levels)) 0 =
      view.generation.block.generationParams.map
        (VExpr.instL levels) := by
    simpa using VEnv.OnTel.liftTelN_eq henv
      hgenerationChecked.raw_onTel (by trivial) Γ.length
  have hcheckedLift₂ : VExpr.liftTelN Γ.length
      (view.generation.block.checked.params.map
        (VExpr.instL levels)) 0 =
      view.generation.block.checked.params.map
        (VExpr.instL levels) := hcheckedLift
  have hgenerationCheckedΓ := hgenerationChecked.weakN henv
    (Ctx.LiftN.zero (n := Γ.length) (Γ := []) Γ)
  rw [hgenerationLift, hcheckedLift₂] at hgenerationCheckedΓ
  simp only [List.append_nil] at hgenerationCheckedΓ
  have hparamsGeneration := TelDefEq.spine_sort henv
    hgenerationCheckedΓ hparamsChecked
    (by simpa [S.generationParams_length] using hparamsLength)
  have hsource := VStructureView.sourceLevels_projectionLevels
    view fieldSort levels
    hlevelsLength
  have hparamsTel :
      view.generation.paramsTel.map
          (VExpr.instL (view.projectionLevels fieldSort levels)) =
        view.generation.block.generationParams.map
          (VExpr.instL levels) := by
    simp [VInductDecl.GenerationChecked.paramsTel,
      List.map_map, Function.comp_def, VExpr.instL_instL, hsource]
  rw [hparamsTel]
  exact hparamsGeneration

/-- For the current nonrecursive view boundary, the exact generated minor
domain specializes to the legacy field-only projection minor.  Keeping this
normalization separate exposes the precise equation that must be generalized
when recursive singleton structures retain their IH telescope. -/
theorem _root_.Lean4Lean.VStructureView.WF.generatedProjectionMinorType_eq
    (self : VStructureView.WF view env) (henv : env.Ordered)
    (fieldSort : VLevel) (levels : List VLevel)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (typeFn : VExpr) :
    view.generatedProjectionMinorType fieldSort levels params typeFn =
      view.projectionMinorType levels params
        (view.specializedFields levels params) typeFn := by
  let S := self.toGenerationEnv henv
  let pLevels := view.projectionLevels fieldSort levels
  have hconstructorMem :
      view.constructor ∈ view.generation.block.ctorPairs := by
    simp [view.constructor_eq]
  have hresultIndices : view.constructor.view.resultIndices = [] := by
    apply List.length_eq_zero_iff.1
    rw [S.viewResultIndices_length hconstructorMem]
    simp [view.checked_indices_eq]
  simp [VStructureView.generatedProjectionMinorType,
    VInductDecl.GenerationChecked.minorType,
    VInductDecl.NormalizedCtor.fieldsR,
    VInductDecl.NormalizedCtor.recArgsR,
    VInductDecl.NormalizedCtor.resultIndicesR,
    VInductDecl.ihsFromRecArgs, VStructureView.projectionMinorType,
    VStructureView.projectionConstructorApp, hresultIndices,
    view.recursive_eq, VExpr.instL_forallN, VExpr.instL_appN,
    VExpr.liftTelN_instL, VExpr.instL_instL, VExpr.instN_forallN,
    VExpr.instTelN, VExpr.instRevAt_forallN_projection,
    List.map_append, List.map_map,
    Function.comp_def,
    VStructureView.sourceLevels_projectionLevels view fieldSort levels
      hlevelsLength]
  have hfieldTel :=
    VExpr.instTelN_instRevAt_lift_projection
      ((view.constructor.rawFields view.source.nparams).map
        (VExpr.instL levels)) params typeFn 0
  rw [VExpr.instRevAt_map_instL_zipIdx] at hfieldTel
  have hfieldTel' :
      VExpr.instTelN typeFn
          ((VExpr.liftTelN 1
              ((view.constructor.rawFields view.source.nparams).map
                (VExpr.instL levels)) 0).zipIdx 1 |>.map
            fun x => x.1.instRevAt params x.2) 0 =
        view.specializedFields levels params := by
    simpa [VStructureView.specializedFields,
      VStructureView.fields] using hfieldTel
  rw [hfieldTel']
  simp only [VExpr.forallN]
  congr 1
  have hsourceLevels :=
    VStructureView.sourceLevels_projectionLevels view fieldSort levels
      hlevelsLength
  change
    (VLevel.params' view.source.uvars
        view.generation.elimination.offset).map
          (VLevel.inst pLevels) = levels at hsourceLevels
  have hliftedLength :
      (VExpr.liftTelN 1
          ((view.constructor.rawFields view.source.nparams).map
            (VExpr.instL levels)) 0).length =
        (view.constructor.rawFields view.source.nparams).length := by
    rw [VExpr.liftTelN_length]
    simp
  have hspecializedLength :
      (view.specializedFields levels params).length =
        (view.constructor.rawFields view.source.nparams).length := by
    simp [VStructureView.specializedFields,
      VStructureView.fields]
  simp only [VExpr.instL,
    VExpr.bvarRevRange_map_instL, hliftedLength,
    hspecializedLength]
  rw [hsourceLevels]
  have hbody :=
    VExpr.projectionMinorBody_shape view.constructorName levels
      params (view.constructor.rawFields view.source.nparams).length
      typeFn
  rw [hparamsLength] at hbody
  simpa only [Nat.add_comm] using hbody

/-- The parameters, projection motive, and selecting minor form the complete
common prefix of the generated recursor.  The remaining cursor is the major
premise; exposing this spine lets generated iota rules reuse exactly the same
checked-generation normalization as projector typing. -/
theorem _root_.Lean4Lean.VStructureView.WF.projectionCommonSpine
    (self : VStructureView.WF view env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (fieldSort : VLevel)
    (hmotiveLevel :
      view.generation.motiveLevel.inst
          (view.projectionLevels fieldSort levels) = fieldSort)
    {typeFn minor : VExpr}
    (typeFnType : env.HasType U Γ typeFn
      (.forallE (view.structureType levels params) (.sort fieldSort)))
    (minorType : env.HasType U Γ minor
      (view.projectionMinorType levels params
        (view.specializedFields levels params) typeFn)) :
    env.SpineWF U Γ
      (view.generation.recType.instL
        (view.projectionLevels fieldSort levels))
      (params ++ [typeFn, minor])
      (.forallE (view.structureType levels params)
        (.app typeFn.lift (.bvar 0))) := by
  let gen := view.generation
  let S := self.toGenerationEnv henv
  let pLevels := view.projectionLevels fieldSort levels
  let k := gen.block.ctorPairs.length
  let ni := gen.idxTel.length
  let recRest : VExpr :=
    VExpr.forallN gen.minorTypes <|
      VExpr.forallN (VExpr.liftTelN (k + 1) gen.idxTel 0) <|
        .forallE
          (VExpr.appN (.const gen.block.sourceType.name gen.sourceLevels)
            (VExpr.bvarRevRange (ni + k + 1) view.nparams ++
              VExpr.bvarRevRange 0 ni))
          (.app
            (VExpr.appN (.bvar (ni + k + 1))
              (VExpr.bvarRevRange 1 ni))
            (.bvar 0))
  let recTail : VExpr := .forallE gen.motiveType recRest
  have hparams := self.generationParamsSpine henv levels hlevels
    hlevelsLength params hparamsLength paramsSpine fieldSort
  have hparamsTelLength : params.length =
      (gen.paramsTel.map (VExpr.instL pLevels)).length := by
    simp [gen, VInductDecl.GenerationChecked.paramsTel,
      S.generationParams_length, hparamsLength]
  have hparamsFull := hparams.retarget hparamsTelLength
    (recTail.instL pLevels)
  have hparamsFull' : env.SpineWF U Γ
      ((VExpr.forallN gen.paramsTel recTail).instL pLevels)
      params (VExpr.instRev (recTail.instL pLevels) params) := by
    simpa [VExpr.instL_forallN] using hparamsFull
  have hmotiveShape :
      VExpr.instRev (recTail.instL pLevels) params =
        .forallE
          (.forallE (view.structureType levels params) (.sort fieldSort))
          (VExpr.instRevAt (recRest.instL pLevels) params 1) := by
    change VExpr.instRev
      (.forallE (gen.motiveType.instL pLevels)
        (recRest.instL pLevels)) params = _
    have hconst : VExpr.instRev
        (.const view.generation.block.sourceType.name levels) params =
        .const view.generation.block.sourceType.name levels :=
      VExpr.instRev_closedN params (by trivial)
    have hrange :
        (VExpr.bvarRevRange 0 view.source.nparams).map
            (VExpr.instRev · params) = params := by
      have hparamsLength' : params.length = view.source.nparams :=
        hparamsLength
      rw [← hparamsLength']
      exact VExpr.map_instRev_bvarRevRange params
    have hrangeL :
        (VExpr.bvarRevRange 0 view.source.nparams).map
            (fun x => (x.instL pLevels).instRev params) = params := by
      calc
        _ = ((VExpr.bvarRevRange 0 view.source.nparams).map
              (VExpr.instL pLevels)).map (VExpr.instRev · params) := by
            rw [List.map_map]
            rfl
        _ = params := by
          rw [VExpr.bvarRevRange_map_instL]
          exact hrange
    have hsort :
        (VExpr.sort fieldSort).instRevAt params 1 =
          .sort fieldSort :=
      VExpr.instRevAt_closedN params (by trivial)
    rw [VExpr.instRev_forallE_projection]
    congr 1
    simp [gen, pLevels,
      VInductDecl.GenerationChecked.motiveType,
      VInductDecl.GenerationChecked.idxTel,
      view.raw_indices_eq, VExpr.forallN, VExpr.bvarRevRange,
      VExpr.instL, VExpr.instL_appN,
      VExpr.instRev_forallE_projection,
      VExpr.instRev_appN, Function.comp_def,
      hconst, hrangeL, hsort, hmotiveLevel,
      VStructureView.structureType,
      VStructureView.sourceLevels_projectionLevels view fieldSort levels
        hlevelsLength]
  rw [hmotiveShape] at hparamsFull'
  have hwithMotive := hparamsFull'.snoc typeFnType
  have hconstructorMem :
      view.constructor ∈ view.generation.block.ctorPairs := by
    simp [view.constructor_eq]
  have hresultIndices : view.constructor.view.resultIndices = [] := by
    apply List.length_eq_zero_iff.1
    rw [S.viewResultIndices_length hconstructorMem]
    simp [view.checked_indices_eq]
  have hminorShape :
      ((VExpr.instRevAt (recRest.instL pLevels) params 1).inst typeFn) =
        .forallE (view.projectionMinorType levels params
            (view.specializedFields levels params) typeFn)
          (.forallE (view.structureType levels params).lift
            (.app (typeFn.liftN 2) (.bvar 0))) := by
    rw [← self.generatedProjectionMinorType_eq henv fieldSort levels
      hlevelsLength params hparamsLength typeFn]
    simp [gen, pLevels, recRest, k, ni,
      VInductDecl.GenerationChecked.minorTypes,
      VInductDecl.GenerationChecked.minorTypesAux,
      VInductDecl.GenerationChecked.minorType,
      VInductDecl.GenerationChecked.idxTel,
      VInductDecl.NormalizedCtor.fieldsR,
      VInductDecl.NormalizedCtor.recArgsR,
      VInductDecl.NormalizedCtor.resultIndicesR,
      VInductDecl.ihsFromRecArgs,
      VStructureView.generatedProjectionMinorType,
      view.constructor_eq, view.raw_indices_eq, hresultIndices,
      view.recursive_eq, VExpr.instL_forallN, VExpr.instL_appN,
      VExpr.liftTelN_instL, VExpr.instL_instL,
      VExpr.instN_forallN, VExpr.instTelN,
      VExpr.instRevAt_forallN_projection, List.map_append,
      VExpr.bvarRevRange, List.map_map, Function.comp_def,
      VStructureView.sourceLevels_projectionLevels view fieldSort levels
        hlevelsLength]
    change VExpr.forallE _ _ = VExpr.forallE _ _
    congr 1
    have hsourceLevels :=
      VStructureView.sourceLevels_projectionLevels view fieldSort levels
        hlevelsLength
    change
      (VLevel.params' view.source.uvars
          view.generation.elimination.offset).map
            (VLevel.inst pLevels) = levels at hsourceLevels
    simp only [VExpr.forallN, VExpr.liftTelN, List.zipIdx_nil,
      List.map_nil, VExpr.instTelN, VExpr.instL,
      VExpr.instL_appN, VExpr.bvarRevRange_map_instL]
    rw [hsourceLevels]
    simpa [gen, hparamsLength, VStructureView.structureType] using
      (VExpr.projectionMajorTail_shape view.name levels params typeFn)
  rw [hminorShape] at hwithMotive
  have hwithMinor := hwithMotive.snoc minorType
  have htypeFnMinor :
      (typeFn.liftN 2).inst minor 1 = typeFn.lift := by
    rw [← VExpr.liftN_liftN typeFn 1 1,
      VExpr.instN_liftAt_projection, VExpr.inst_lift]
  have hminorVar : VExpr.instVar 0 minor 1 = .bvar 0 := by
    simp [VExpr.instVar]
  have htail :
      (VExpr.forallE (view.structureType levels params).lift
        (.app (typeFn.liftN 2) (.bvar 0))).inst minor =
        VExpr.forallE (view.structureType levels params)
          (.app typeFn.lift (.bvar 0)) := by
    simp only [VExpr.inst]
    rw [VExpr.inst_lift, htypeFnMinor, hminorVar]
  rw [htail] at hwithMinor
  simpa [gen, pLevels, recTail, recRest, k, ni,
    VInductDecl.GenerationChecked.recType, List.append_assoc] using hwithMinor

/-- The exact parameters, projection motive, selecting minor, and canonical
field variables form a saturated capture spine for the constructor's
generated iota rule. -/
theorem _root_.Lean4Lean.VStructureView.WF.projectionRuleCaptureSpine
    (self : VStructureView.WF view env) (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (fieldSort : VLevel)
    (hmotiveLevel :
      view.generation.motiveLevel.inst
          (view.projectionLevels fieldSort levels) = fieldSort)
    {typeFn minor : VExpr}
    (typeFnType : env.HasType U Γ typeFn
      (.forallE (view.structureType levels params) (.sort fieldSort)))
    (minorType : env.HasType U Γ minor
      (view.projectionMinorType levels params
        (view.specializedFields levels params) typeFn)) :
    let fields := view.specializedFields levels params
    let m := fields.length
    ∃ B, env.SpineWF U (fields.reverse ++ Γ)
      ((view.generation.rule 0 view.constructor).type.instL
        (view.projectionLevels fieldSort levels))
      (params.map (VExpr.liftN m) ++
        [typeFn.liftN m, minor.liftN m] ++
          VExpr.bvarRevRange 0 m) B := by
  let gen := view.generation
  let S := self.toGenerationEnv henv.ordered
  let fields := view.specializedFields levels params
  let m := fields.length
  let pLevels := view.projectionLevels fieldSort levels
  let common := gen.paramsTel ++ gen.motiveType :: gen.minorTypes
  let k := gen.block.ctorPairs.length
  let ni := gen.idxTel.length
  let recAfterCommon : VExpr :=
    VExpr.forallN (VExpr.liftTelN (k + 1) gen.idxTel 0) <|
      .forallE
        (VExpr.appN (.const gen.block.sourceType.name gen.sourceLevels)
          (VExpr.bvarRevRange (ni + k + 1) view.nparams ++
            VExpr.bvarRevRange 0 ni))
        (.app
          (VExpr.appN (.bvar (ni + k + 1))
            (VExpr.bvarRevRange 1 ni))
          (.bvar 0))
  let Bs := view.constructor.fieldsR view.source.uvars view.source.nparams
    gen.elimination
  let rawFields := view.constructor.rawFields view.source.nparams
  let fieldBinders := VExpr.liftTelN (k + 1) Bs 0
  let idxR := view.constructor.resultIndicesR view.source.uvars
      gen.elimination |>.map fun e => e.liftN (k + 1) Bs.length
  let ctorApp := VExpr.appN
    (.const view.constructor.raw.name gen.sourceLevels)
    (VExpr.bvarRevRange (Bs.length + k + 1) view.source.nparams ++
      VExpr.bvarRevRange 0 Bs.length)
  let ruleResult := VExpr.appN (.bvar (k + Bs.length))
    (idxR ++ [ctorApp])
  let ruleTail := VExpr.forallN fieldBinders ruleResult
  have hcommon := self.projectionCommonSpine henv.ordered
    levels hlevels hlevelsLength params hparamsLength paramsSpine
    fieldSort hmotiveLevel typeFnType minorType
  have hcommonWeak := hcommon.weakN henv.ordered
    (Ctx.LiftN.zero (n := m) (Γ := Γ) fields.reverse
      (h := by simp [m]))
  have hrecClosed :
      (gen.recType.instL pLevels).ClosedN 0 :=
    S.recType_closedN.instL
  rw [hrecClosed.liftN_eq (Nat.zero_le _)] at hcommonWeak
  have hctorCount : gen.block.ctorPairs.length = 1 := by
    simp [gen, view.constructor_eq]
  have hminorCount : gen.minorTypes.length = 1 := by
    rw [gen.minorTypes_length, hctorCount]
  have hcommonLength :
      (params.map (VExpr.liftN m) ++
        [typeFn.liftN m, minor.liftN m]).length =
        (common.map (VExpr.instL pLevels)).length := by
    simp [common, gen, VInductDecl.GenerationChecked.paramsTel,
      S.generationParams_length, hparamsLength, hminorCount]
  have hrecShapeRaw : gen.recType =
      VExpr.forallN common recAfterCommon := by
    simp [gen, common, recAfterCommon, k, ni,
      VInductDecl.GenerationChecked.recType,
      VExpr.forallN_append, VExpr.forallN]
  have hrecShape : gen.recType.instL pLevels =
      VExpr.forallN (common.map (VExpr.instL pLevels))
        (recAfterCommon.instL pLevels) := by
    rw [hrecShapeRaw, VExpr.instL_forallN]
  rw [hrecShape] at hcommonWeak
  simp only [List.map_append, List.map_cons, List.map_nil] at hcommonWeak
  change env.SpineWF U (fields.reverse ++ Γ)
    (VExpr.forallN (common.map (VExpr.instL pLevels))
      (recAfterCommon.instL pLevels))
    (params.map (VExpr.liftN m) ++
      [typeFn.liftN m, minor.liftN m]) _ at hcommonWeak
  have hrulePrefix := hcommonWeak.retarget hcommonLength
    (ruleTail.instL pLevels)
  let commonArgs := params.map (VExpr.liftN m) ++
    [typeFn.liftN m, minor.liftN m]
  have hsourceLevels :=
    VStructureView.sourceLevels_projectionLevels view fieldSort levels
      hlevelsLength
  change
    (VLevel.params' view.source.uvars
        view.generation.elimination.offset).map
          (VLevel.inst pLevels) = levels at hsourceLevels
  have hfieldBindersShape :
      fieldBinders.map (VExpr.instL pLevels) =
        VExpr.liftTelN 2 (rawFields.map (VExpr.instL levels)) 0 := by
    simp [fieldBinders, Bs, rawFields, k, gen,
      VInductDecl.NormalizedCtor.fieldsR, VExpr.liftTelN_instL,
      List.map_map, Function.comp_def, VExpr.instL_instL,
      hsourceLevels, hctorCount]
  have hfieldDomains :
      ((fieldBinders.map (VExpr.instL pLevels)).zipIdx.map fun x =>
        x.1.instRevAt commonArgs x.2) =
        VExpr.liftTelN m fields 0 := by
    rw [hfieldBindersShape]
    have hcancelMinor :=
      VExpr.map_instRevAt_liftTelN_one_append_singleton
        (VExpr.liftTelN 1 (rawFields.map (VExpr.instL levels)) 0)
        (params.map (VExpr.liftN m) ++ [typeFn.liftN m])
        (minor.liftN m) 0
    have hcancelTypeFn :=
      VExpr.map_instRevAt_liftTelN_one_append_singleton
        (rawFields.map (VExpr.instL levels))
        (params.map (VExpr.liftN m)) (typeFn.liftN m) 0
    calc
      _ = ((VExpr.liftTelN 1
              (rawFields.map (VExpr.instL levels)) 0).zipIdx.map fun x =>
            x.1.instRevAt
              (params.map (VExpr.liftN m) ++ [typeFn.liftN m]) x.2) := by
          have hdouble : VExpr.liftTelN 2
                (rawFields.map (VExpr.instL levels)) 0 =
              VExpr.liftTelN 1
                (VExpr.liftTelN 1
                  (rawFields.map (VExpr.instL levels)) 0) 0 := by
            simpa using (VExpr.liftTelN_liftTelN 1 1
              (rawFields.map (VExpr.instL levels)) 0).symm
          rw [hdouble]
          simpa [commonArgs, List.append_assoc] using hcancelMinor
      _ = ((rawFields.map (VExpr.instL levels)).zipIdx.map fun x =>
            x.1.instRevAt (params.map (VExpr.liftN m)) x.2) :=
        hcancelTypeFn
      _ = view.specializedFields levels
          (params.map (VExpr.liftN m)) := by
        simpa [rawFields, VStructureView.specializedFields,
          VStructureView.fields] using
          VExpr.instRevAt_map_instL_zipIdx rawFields levels
            (params.map (VExpr.liftN m)) 0
      _ = VExpr.liftTelN m fields 0 := by
        simpa [fields] using self.specializedFields_liftN
          henv.ordered levels params hparamsLength m 0
  simp only [ruleTail, VExpr.instL_forallN] at hrulePrefix
  rw [VExpr.instRev_forallN_projection, hfieldDomains] at hrulePrefix
  obtain ⟨resultLevel, hparamsSpine₀⟩ := paramsSpine
  have hsortTel := self.specializedFields_onSortTel henv.ordered
    levels hlevels hlevelsLength params hparamsLength
    ⟨resultLevel, hparamsSpine₀⟩
  have hfieldsOnTel : env.OnTel U Γ fields := by
    simpa [fields] using hsortTel.toOnTel
  have hfieldBase := hfieldsOnTel.selfSpineWF
    (B := .sort .zero) (Δ := ([] : List VExpr))
  have hfieldBase' : env.SpineWF U (fields.reverse ++ Γ)
      (VExpr.forallN (VExpr.liftTelN m fields 0) (.sort .zero))
      (VExpr.bvarRevRange 0 m) (.sort .zero) := by
    simpa [m, VExpr.liftN_forallN, VExpr.liftN] using hfieldBase
  let residualResult := (ruleResult.instL pLevels).instRevAt
    commonArgs fieldBinders.length
  have hfieldBindersLength :
      (fieldBinders.map (VExpr.instL pLevels)).length =
        fieldBinders.length := by simp
  rw [hfieldBindersLength] at hrulePrefix
  change env.SpineWF U (fields.reverse ++ Γ) _ commonArgs
    (VExpr.forallN (VExpr.liftTelN m fields 0) residualResult) at hrulePrefix
  have hfieldLength : (VExpr.bvarRevRange 0 m).length =
      (VExpr.liftTelN m fields 0).length := by
    rw [VExpr.bvarRevRange_length, VExpr.liftTelN_length]
  have hfieldSpine := hfieldBase'.retarget hfieldLength residualResult
  have hfull := hrulePrefix.append hfieldSpine
  refine ⟨residualResult.instRev (VExpr.bvarRevRange 0 m), ?_⟩
  have hruleShapeRaw : (gen.rule 0 view.constructor).type =
      VExpr.forallN common ruleTail := by
    simp [gen, common, ruleTail, ruleResult, fieldBinders, idxR,
      ctorApp, Bs, k, VInductDecl.GenerationChecked.rule,
      VExpr.forallN_append, VExpr.forallN, List.append_assoc]
  rw [hruleShapeRaw, VExpr.instL_forallN, VExpr.instL_forallN]
  simpa [commonArgs, List.append_assoc] using hfull

theorem _root_.Lean4Lean.VStructureView.WF.recursorProjection_hasType
    (self : VStructureView.WF view env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (fieldSort : VLevel)
    (hfieldSort : fieldSort.WF U)
    (hmotiveLevel :
      view.generation.motiveLevel.inst
          (view.projectionLevels fieldSort levels) = fieldSort)
    (_structIsType : env.IsType U Γ
      (view.structureType levels params))
    {typeFn minor major : VExpr}
    (typeFnType : env.HasType U Γ typeFn
      (.forallE (view.structureType levels params) (.sort fieldSort)))
    (minorType : env.HasType U Γ minor
      (view.projectionMinorType levels params
        (view.specializedFields levels params) typeFn))
    (majorType : env.HasType U Γ major
      (view.structureType levels params)) :
    env.HasType U Γ
      (VExpr.appN (.const view.recursorName
        (view.projectionLevels fieldSort levels))
        (params ++ [typeFn, minor, major]))
      (.app typeFn major) := by
  let pLevels := view.projectionLevels fieldSort levels
  have hrec : env.HasType U Γ
      (.const view.recursorName pLevels)
      (view.generation.recType.instL pLevels) := by
    have hout := VEnv.HasType.const (Γ := Γ) self.recursor
      (VStructureView.projectionLevels_wf view fieldSort levels
        hfieldSort hlevels)
      (VStructureView.projectionLevels_length view fieldSort levels
        hlevelsLength)
    simpa [pLevels, VStructureView.recursorName,
      VInductDecl.GenerationChecked.recursor] using hout
  have hprefix := self.projectionCommonSpine henv
    levels hlevels hlevelsLength params hparamsLength paramsSpine
    fieldSort hmotiveLevel typeFnType minorType
  have hfull := hprefix.snoc majorType
  have hfull' : env.SpineWF U Γ
      (view.generation.recType.instL pLevels)
      (params ++ [typeFn, minor, major]) (.app typeFn major) := by
    simpa [pLevels, List.append_assoc, VExpr.inst,
      VExpr.inst_lift, VExpr.instVar_zero] using hfull
  exact hfull'.hasType_appN hrec

/-- The first selecting minor is well typed directly from the checked field
telescope.  No projector iota equation is needed at index zero: its motive is
the first field type with an empty projection prefix, and the generated minor
selects the corresponding constructor argument. -/
theorem _root_.Lean4Lean.VStructureView.WF.toMinorsWFPrefix_one
    (self : VStructureView.WF view env) (henv : env.ConversionRegular) :
    view.MinorsWFPrefix env 1 := by
  intro U Γ levels params idx code hlimit hΓ hlevels hlevelsLength
    hparamsLength hparamsSpine hcode
  have hidx : idx = 0 := by omega
  subst idx
  obtain ⟨resultLevel, hparamsSpine₀⟩ := hparamsSpine
  let fields := view.specializedFields levels params
  let m := fields.length
  have hcodeLength : 0 < fields.length := by
    have : 0 < (view.projectionCodes levels params).length :=
      (List.getElem?_eq_some_iff.1 hcode).1
    simpa [fields] using this
  obtain ⟨fieldSort, hfieldSort, hcodeSort, hminorShape, -⟩ :=
    view.projectionCodes_get?_program_shape levels params hcode
  obtain ⟨field, hfield, htypeFnShape⟩ :=
    view.projectionCodes_get?_typeFn levels params hcode
  have hsortTel := self.specializedFields_onSortTel henv.ordered
    levels hlevels hlevelsLength params hparamsLength
    ⟨resultLevel, hparamsSpine₀⟩
  have hfieldType : env.HasType U Γ field (.sort code.fieldSort) := by
    cases hfields : view.specializedFields levels params with
    | nil => simp [hfields] at hfield
    | cons first rest =>
        have hfirst : first = field := by simpa [hfields] using hfield
        subst first
        cases hsorts : view.fieldSorts.map (VLevel.inst levels) with
        | nil =>
            rw [hfields, hsorts] at hsortTel
            cases hsortTel
        | cons firstSort restSorts =>
            have hfirstSort : firstSort = code.fieldSort := by
              have : firstSort = fieldSort := by
                simpa [hsorts] using hfieldSort
              exact this.trans hcodeSort.symm
            subst firstSort
            rw [hfields, hsorts] at hsortTel
            cases hsortTel with
            | cons hfirst _ => exact hfirst
  have htypeFnShape₀ : code.typeFn =
      .lam (view.structureType levels params) field.lift := by
    simpa [VExpr.instRevAt] using htypeFnShape
  have hfieldsOnTel : env.OnTel U Γ fields := by
    simpa [fields] using hsortTel.toOnTel
  have hfieldsCtx : OnCtx (fields.reverse ++ Γ) (env.IsType U) :=
    hfieldsOnTel.toOnCtx hΓ
  have hprefix := self.constructorPrefix_hasType henv.ordered levels hlevels
    hlevelsLength params hparamsLength ⟨resultLevel, hparamsSpine₀⟩
  have hprefixWeak := hprefix.weakN henv.ordered
    (Ctx.LiftN.zero (n := m) (Γ := Γ) fields.reverse
      (h := by simp [m]))
  have hprefixWeak' : env.HasType U (fields.reverse ++ Γ)
      ((VExpr.appN (.const view.constructorName levels) params).liftN m)
      ((VExpr.forallN fields
        ((view.structureType levels params).liftN m)).liftN m) := by
    simpa [fields, m] using hprefixWeak
  have hprefixSelf : env.HasType U
      (([] : List VExpr) ++ fields.reverse ++ Γ)
      ((VExpr.appN (.const view.constructorName levels) params).liftN m)
      ((VExpr.forallN fields
        ((view.structureType levels params).liftN m)).liftN
          (([] : List VExpr).length + fields.length)) := by
    simpa [m] using hprefixWeak'
  have hmajor₀ := VEnv.HasType.appN_selfSpine
    (env := env) (U := U) (As := fields)
    (B := (view.structureType levels params).liftN m)
    (Δ := []) (Γ := Γ)
    (f := (VExpr.appN (.const view.constructorName levels) params).liftN m)
    hprefixSelf
  have hmajor : env.HasType U (fields.reverse ++ Γ)
      (view.projectionConstructorApp levels params fields)
      ((view.structureType levels params).liftN m) := by
    simpa [fields, m, VStructureView.projectionConstructorApp,
      VExpr.liftN, VExpr.liftN_appN, VExpr.appN_append, List.map_map,
      Function.comp_def] using hmajor₀
  have hfieldInner : env.HasType U (fields.reverse ++ Γ)
      (field.liftN m) (.sort code.fieldSort) := by
    exact hfieldType.weakN henv.ordered
      (Ctx.LiftN.zero (n := m) (Γ := Γ) fields.reverse
        (h := by simp [m]))
  have hfieldUnderMajor : env.HasType U
      ((view.structureType levels params).liftN m :: fields.reverse ++ Γ)
      (field.liftN m).lift (.sort code.fieldSort) := by
    exact hfieldInner.weakN henv.ordered
      (Ctx.LiftN.one (A := (view.structureType levels params).liftN m))
  rw [VExpr.lift_liftN'] at hfieldUnderMajor
  have hbeta₀ := VEnv.IsDefEq.beta hfieldUnderMajor hmajor
  have hbodyInst : (field.lift.liftN m 1).inst
      (view.projectionConstructorApp levels params fields) =
      field.liftN m := by
    rw [← VExpr.lift_liftN', VExpr.inst_lift]
  have hbeta : env.IsDefEqU U (fields.reverse ++ Γ)
      (.app (code.typeFn.liftN m)
        (view.projectionConstructorApp levels params fields))
      (field.liftN m) := by
    refine ⟨.sort code.fieldSort, ?_⟩
    simpa [htypeFnShape₀, VExpr.liftN, VExpr.inst,
      VExpr.inst_lift, hbodyInst] using hbeta₀
  let q := fields.length - 1
  have hqLt : q < fields.length := by
    dsimp only [q]
    omega
  have hfieldReverse : fields.reverse[q]? = some field := by
    rw [List.getElem?_reverse hqLt,
      show fields.length - 1 - q = 0 by simp [q], show
        fields[0]? = some field by simpa [fields] using hfield]
  have hfieldCtx : (fields.reverse ++ Γ)[q]? = some field := by
    rw [List.getElem?_append_left (by simpa using hqLt), hfieldReverse]
  have hbody : env.HasType U (fields.reverse ++ Γ) (.bvar q)
      (field.liftN m) := by
    have hlookup := VEnv.HasType.bvar (env := env) (U := U)
      (Lookup.of_getElem? hfieldCtx)
    have hqSucc : q + 1 = m := by
      dsimp only [q, m]
      omega
    rw [hqSucc] at hlookup
    exact hlookup
  have hbodyExpected : env.HasType U (fields.reverse ++ Γ) (.bvar q)
      (.app (code.typeFn.liftN m)
        (view.projectionConstructorApp levels params fields)) :=
    henv.hasType_defeqU_r hfieldsCtx hbeta.symm hbody
  have hminor := VEnv.HasType.lamN hfieldsOnTel hbodyExpected
  rw [hminorShape]
  simpa [VStructureView.projectionMinorType, fields, m, q] using hminor

/-- Earlier projector programs determine the generated motive function for
the next source-order field.  This isolates the non-mutual half of the
minor/program induction: the current selecting minor is not used. -/
theorem _root_.Lean4Lean.VStructureView.WF.projectionTypeFn_hasType_of_programsPrefix
    (self : VStructureView.WF view env) (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} {levels : List VLevel}
    {params : List VExpr} {idx : Nat}
    {code : VStructureView.ProjectionCode}
    (programs : view.ProgramsWFPrefix env idx)
    (hΓ : OnCtx Γ (env.IsType U))
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (hcode : (view.projectionCodes levels params)[idx]? = some code) :
    env.HasType U Γ code.typeFn
      (.forallE (view.structureType levels params) (.sort code.fieldSort)) := by
  obtain ⟨resultLevel, hparamsSpine₀⟩ := hparamsSpine
  have hfamily : env.HasType U Γ (.const view.name levels)
      (view.familyType.instL levels) := by
    apply VEnv.HasType.const self.family hlevels
    rw [view.generation.block.sourceType_uvars_eq]
    exact hlevelsLength
  have hstruct : env.HasType U Γ
      (view.structureType levels params) (.sort resultLevel) := by
    simpa [VStructureView.structureType] using
      hparamsSpine₀.hasType_appN hfamily
  have hidx : idx < (view.projectionCodes levels params).length :=
    (List.getElem?_eq_some_iff.1 hcode).1
  obtain ⟨fieldSort, hfieldSort, hcodeSort, -, -⟩ :=
    view.projectionCodes_get?_program_shape levels params hcode
  have hfamilyClosed : (view.familyType.instL levels).ClosedN 0 := by
    simpa using (henv.ordered.closedC self.family).instL
  let paramsLift := params.map (VExpr.liftN 1)
  have hparamsLengthLift : paramsLift.length = view.nparams := by
    simpa [paramsLift] using hparamsLength
  have hparamsSpineLift : env.SpineWF U
      (view.structureType levels params :: Γ)
      (view.familyType.instL levels) paramsLift (.sort resultLevel) := by
    have h := hparamsSpine₀.weakN henv.ordered
      (Ctx.LiftN.one (A := view.structureType levels params))
    rw [hfamilyClosed.liftN_eq (Nat.zero_le _)] at h
    simpa [paramsLift, VExpr.liftN] using h
  have hstructLift : view.structureType levels paramsLift =
      (view.structureType levels params).lift := by
    change view.structureType levels
        (params.map fun param => param.liftN 1 0) =
      (view.structureType levels params).liftN 1 0
    exact (view.structureType_liftN levels params 1 0).symm
  have hΓLift : OnCtx (view.structureType levels params :: Γ)
      (env.IsType U) := ⟨hΓ, resultLevel, hstruct⟩
  have hmajorLift : env.HasType U
      (view.structureType levels params :: Γ) (.bvar 0)
      (view.structureType levels paramsLift) := by
    rw [hstructLift]
    exact .bvar .zero
  have hcodesLift := self.projectionCodes_liftN henv.ordered
    levels params hparamsLength 1 0
  have hidxLift : idx <
      (view.projectionCodes levels paramsLift).length := by
    rw [← hcodesLift]
    simpa using hidx
  have hargsLength :
      (view.projectionArgs levels paramsLift idx (.bvar 0)).length = idx :=
    view.projectionArgs_length levels paramsLift idx (.bvar 0)
      (Nat.le_of_lt hidxLift)
  have hsortTelLift := self.specializedFields_onSortTel henv.ordered
    levels hlevels hlevelsLength paramsLift hparamsLengthLift
    ⟨resultLevel, hparamsSpineLift⟩
  have hprior : ∀ {j : Nat}
      {prior : VStructureView.ProjectionCode}, j < idx →
      (view.projectionCodes levels paramsLift)[j]? = some prior →
      env.HasType U (view.structureType levels params :: Γ)
        prior.projector
        (.forallE (view.structureType levels paramsLift)
          (.app prior.typeFn.lift (.bvar 0))) := by
    intro j prior hj hpriorCode
    exact programs hj hΓLift hlevels hlevelsLength hparamsLengthLift
      ⟨resultLevel, hparamsSpineLift⟩ hpriorCode
  obtain ⟨cursor, hconsume, hprefix⟩ :=
    VStructureView.projectionArgsSpineAux_of_prefix henv hΓLift
      hmajorLift hprior
      (.sort .zero) (Nat.le_refl idx)
        (Nat.le_of_lt (by simpa using hidxLift))
  obtain ⟨next, nextSort, cursorBody, hcursor, hnextType,
      hnextSort⟩ :=
    hsortTelLift.next_of_spine henv.ordered hprefix
      (by simpa [hargsLength] using hidxLift)
  obtain ⟨field, hfield, htypeFnShape⟩ :=
    view.projectionCodes_get?_typeFn levels params hcode
  have hfieldLift :
      (view.specializedFields levels paramsLift)[idx]? =
        some (field.liftN 1 idx) := by
    rw [self.specializedFields_liftN henv.ordered levels params
      hparamsLength 1 0, VExpr.liftTelN_getElem?, hfield]
    simp
  have hargsLift :
      view.projectionArgs levels paramsLift idx (.bvar 0) =
        ((view.projectionCodes levels params).take idx).map fun prior =>
          .app prior.projector.lift (.bvar 0) := by
    unfold VStructureView.projectionArgs
    rw [← hcodesLift]
    simp [List.map_take, List.map_map,
      VStructureView.ProjectionCode.liftN, Function.comp_def]
  obtain ⟨field', semanticBody, hfield', hconsumeDomain⟩ :=
    VExpr.consumeForalls?_forallN_domain
      (view.specializedFields levels paramsLift) (.sort .zero)
      (view.projectionArgs levels paramsLift idx (.bvar 0))
      (by simpa [hargsLength] using hidxLift)
  have hfieldEq : field' = field.liftN 1 idx :=
    Option.some.inj
      (hfield'.symm.trans (by simpa [hargsLength] using hfieldLift))
  subst field'
  have hcursorDomain : cursor =
      .forallE
        ((field.liftN 1 idx).instRevAt
          (view.projectionArgs levels paramsLift idx (.bvar 0)) 0)
        semanticBody :=
    Option.some.inj (hconsume.symm.trans hconsumeDomain)
  have hnextEq : next =
      (field.liftN 1 idx).instRevAt
        (view.projectionArgs levels paramsLift idx (.bvar 0)) 0 := by
    have hforall := hcursor.symm.trans hcursorDomain
    injection hforall
  have hsortEq : nextSort = code.fieldSort := by
    rw [hargsLength] at hnextSort
    have hnextField : nextSort = fieldSort :=
      Option.some.inj (hnextSort.symm.trans hfieldSort)
    exact hnextField.trans hcodeSort.symm
  have htypeBody : env.HasType U
      (view.structureType levels params :: Γ)
      ((field.liftN 1 idx).instRevAt
        (((view.projectionCodes levels params).take idx).map fun prior =>
          .app prior.projector.lift (.bvar 0)) 0)
      (.sort code.fieldSort) := by
    rw [← hargsLift, ← hnextEq, ← hsortEq]
    exact hnextType
  rw [htypeFnShape]
  exact hstruct.lam htypeBody

/-- A checked structure turns any source-ordered selecting-minor prefix into
the matching projector-program prefix.  This is the induction-facing core of
`toProgramsWF_of_minors`: no proof about a later minor is available while an
earlier projector is reconstructed. -/
theorem _root_.Lean4Lean.VStructureView.WF.toProgramsWFPrefix_of_minorsWFPrefix
    (self : VStructureView.WF view env) (henv : env.ConversionRegular)
    {limit : Nat} (minors : view.MinorsWFPrefix env limit) :
    view.ProgramsWFPrefix env limit := by
  intro U Γ levels params idx code hlimit hΓ hlevels hlevelsLength
    hparamsLength hparamsSpine hcode
  induction idx using Nat.strongRecOn generalizing U Γ levels params code with
  | _ idx ih =>
    obtain ⟨resultLevel, hparamsSpine₀⟩ := hparamsSpine
    have hfamily : env.HasType U Γ (.const view.name levels)
        (view.familyType.instL levels) := by
      apply VEnv.HasType.const self.family hlevels
      rw [view.generation.block.sourceType_uvars_eq]
      exact hlevelsLength
    have hstruct : env.HasType U Γ
        (view.structureType levels params) (.sort resultLevel) := by
      simpa [VStructureView.structureType] using
        hparamsSpine₀.hasType_appN hfamily
    have hstructIsType : env.IsType U Γ
        (view.structureType levels params) := ⟨resultLevel, hstruct⟩
    have hidx : idx < (view.projectionCodes levels params).length :=
      (List.getElem?_eq_some_iff.1 hcode).1
    obtain ⟨fieldSort, hfieldSort, hcodeSort, hminorShape,
        hprojectorShape⟩ :=
      view.projectionCodes_get?_program_shape levels params hcode
    have hsortTel := self.specializedFields_onSortTel henv.ordered
      levels hlevels hlevelsLength params hparamsLength
      ⟨resultLevel, hparamsSpine₀⟩
    have hfieldSortWF : code.fieldSort.WF U := by
      rw [hcodeSort]
      exact hsortTel.sortWF hΓ hfieldSort
    have hfamilyClosed : (view.familyType.instL levels).ClosedN 0 := by
      simpa using (henv.ordered.closedC self.family).instL
    let paramsLift := params.map (VExpr.liftN 1)
    have hparamsLengthLift : paramsLift.length = view.nparams := by
      simpa [paramsLift] using hparamsLength
    have hparamsSpineLift : env.SpineWF U
        (view.structureType levels params :: Γ)
        (view.familyType.instL levels) paramsLift (.sort resultLevel) := by
      have h := hparamsSpine₀.weakN henv.ordered
        (Ctx.LiftN.one (A := view.structureType levels params))
      rw [hfamilyClosed.liftN_eq (Nat.zero_le _)] at h
      simpa [paramsLift, VExpr.liftN] using h
    have hstructLift : view.structureType levels paramsLift =
        (view.structureType levels params).lift := by
      change view.structureType levels
          (params.map fun param => param.liftN 1 0) =
        (view.structureType levels params).liftN 1 0
      exact (view.structureType_liftN levels params 1 0).symm
    have hΓLift : OnCtx (view.structureType levels params :: Γ)
        (env.IsType U) := ⟨hΓ, resultLevel, hstruct⟩
    have hmajorLift : env.HasType U
        (view.structureType levels params :: Γ) (.bvar 0)
        (view.structureType levels paramsLift) := by
      rw [hstructLift]
      exact .bvar .zero
    have hcodesLift := self.projectionCodes_liftN henv.ordered
      levels params hparamsLength 1 0
    have hidxLift : idx <
        (view.projectionCodes levels paramsLift).length := by
      rw [← hcodesLift]
      simpa using hidx
    have hargsLength :
        (view.projectionArgs levels paramsLift idx (.bvar 0)).length = idx :=
      view.projectionArgs_length levels paramsLift idx (.bvar 0)
        (Nat.le_of_lt hidxLift)
    have hsortTelLift := self.specializedFields_onSortTel henv.ordered
      levels hlevels hlevelsLength paramsLift hparamsLengthLift
      ⟨resultLevel, hparamsSpineLift⟩
    have hprior : ∀ {j : Nat}
        {prior : VStructureView.ProjectionCode}, j < idx →
        (view.projectionCodes levels paramsLift)[j]? = some prior →
        env.HasType U (view.structureType levels params :: Γ)
          prior.projector
          (.forallE (view.structureType levels paramsLift)
            (.app prior.typeFn.lift (.bvar 0))) := by
      intro j prior hj hpriorCode
      exact ih j hj (Nat.lt_trans hj hlimit) hΓLift hlevels
        hlevelsLength hparamsLengthLift ⟨resultLevel, hparamsSpineLift⟩
        hpriorCode
    obtain ⟨cursor, hconsume, hprefix⟩ :=
      VStructureView.projectionArgsSpineAux_of_prefix henv hΓLift
        hmajorLift hprior
        (.sort .zero) (Nat.le_refl idx)
          (Nat.le_of_lt (by simpa using hidxLift))
    obtain ⟨next, nextSort, cursorBody, hcursor, hnextType,
        hnextSort⟩ :=
      hsortTelLift.next_of_spine henv.ordered hprefix
        (by simpa [hargsLength] using hidxLift)
    obtain ⟨field, hfield, htypeFnShape⟩ :=
      view.projectionCodes_get?_typeFn levels params hcode
    have hfieldLift :
        (view.specializedFields levels paramsLift)[idx]? =
          some (field.liftN 1 idx) := by
      rw [self.specializedFields_liftN henv.ordered levels params
        hparamsLength 1 0, VExpr.liftTelN_getElem?, hfield]
      simp
    have hargsLift :
        view.projectionArgs levels paramsLift idx (.bvar 0) =
          ((view.projectionCodes levels params).take idx).map fun prior =>
            .app prior.projector.lift (.bvar 0) := by
      unfold VStructureView.projectionArgs
      rw [← hcodesLift]
      simp [List.map_take, List.map_map,
        VStructureView.ProjectionCode.liftN, Function.comp_def]
    obtain ⟨field', semanticBody, hfield', hconsumeDomain⟩ :=
      VExpr.consumeForalls?_forallN_domain
        (view.specializedFields levels paramsLift) (.sort .zero)
        (view.projectionArgs levels paramsLift idx (.bvar 0))
        (by simpa [hargsLength] using hidxLift)
    have hfieldEq : field' = field.liftN 1 idx :=
      Option.some.inj
        (hfield'.symm.trans (by simpa [hargsLength] using hfieldLift))
    subst field'
    have hcursorDomain : cursor =
        .forallE
          ((field.liftN 1 idx).instRevAt
            (view.projectionArgs levels paramsLift idx (.bvar 0)) 0)
          semanticBody :=
      Option.some.inj (hconsume.symm.trans hconsumeDomain)
    have hnextEq : next =
        (field.liftN 1 idx).instRevAt
          (view.projectionArgs levels paramsLift idx (.bvar 0)) 0 := by
      have hforall := hcursor.symm.trans hcursorDomain
      injection hforall
    have hsortEq : nextSort = code.fieldSort := by
      rw [hargsLength] at hnextSort
      have hnextField : nextSort = fieldSort :=
        Option.some.inj (hnextSort.symm.trans hfieldSort)
      exact hnextField.trans hcodeSort.symm
    have htypeBody : env.HasType U
        (view.structureType levels params :: Γ)
        ((field.liftN 1 idx).instRevAt
          (((view.projectionCodes levels params).take idx).map fun prior =>
            .app prior.projector.lift (.bvar 0)) 0)
        (.sort code.fieldSort) := by
      rw [← hargsLift, ← hnextEq, ← hsortEq]
      exact hnextType
    have htypeFn : env.HasType U Γ code.typeFn
        (.forallE (view.structureType levels params)
          (.sort code.fieldSort)) := by
      rw [htypeFnShape]
      exact hstruct.lam htypeBody
    have hminor := minors hlimit hΓ hlevels hlevelsLength hparamsLength
      ⟨resultLevel, hparamsSpine₀⟩ hcode
    have hmotiveLevel :
        view.generation.motiveLevel.inst
          (view.projectionLevels code.fieldSort levels) = code.fieldSort := by
      rw [hcodeSort]
      rw [List.getElem?_map] at hfieldSort
      obtain ⟨rawSort, hrawSort, rfl⟩ := Option.map_eq_some_iff.1 hfieldSort
      have hrawSortMem : rawSort ∈ view.fieldSorts :=
        List.mem_iff_getElem?.2 ⟨idx, hrawSort⟩
      exact self.motiveLevel_projectionLevels rawSort hrawSortMem levels
    have htypeFnLift : env.HasType U
        (view.structureType levels params :: Γ) code.typeFn.lift
        (.forallE (view.structureType levels paramsLift)
          (.sort code.fieldSort)) := by
      have h := htypeFn.weakN henv.ordered
        (Ctx.LiftN.one (A := view.structureType levels params))
      simpa [hstructLift, VExpr.liftN] using h
    have hminorLift : env.HasType U
        (view.structureType levels params :: Γ) code.minor.lift
        (view.projectionMinorType levels paramsLift
          (view.specializedFields levels paramsLift) code.typeFn.lift) := by
      have h := hminor.weakN henv.ordered
        (Ctx.LiftN.one (A := view.structureType levels params))
      have hliftComm (e : VExpr) :
          (e.liftN (view.specializedFields levels params).length).liftN 1
              (view.specializedFields levels params).length =
            e.lift.liftN (view.specializedFields levels params).length := by
        symm
        simpa using VExpr.liftN_liftN_comm e
          (view.specializedFields levels params).length 1 0 0
          (Nat.le_refl 0)
      simpa [VStructureView.projectionMinorType,
        VStructureView.projectionConstructorApp,
        VExpr.liftN_forallN, VExpr.liftN_appN,
        VExpr.liftTelN_length, hliftComm,
        VExpr.bvarRevRange_liftN_high,
        self.specializedFields_liftN henv.ordered levels params
          hparamsLength 1 0,
        hstructLift, paramsLift, VExpr.liftN,
        List.map_append, List.map_map, Function.comp_def] using h
    have hstructIsTypeLift : env.IsType U
        (view.structureType levels params :: Γ)
        (view.structureType levels paramsLift) := by
      rw [hstructLift]
      exact hstructIsType.weakN henv.ordered
        (Ctx.LiftN.one (A := view.structureType levels params))
    have hbody := self.recursorProjection_hasType henv.ordered
      levels hlevels hlevelsLength paramsLift hparamsLengthLift
      ⟨resultLevel, hparamsSpineLift⟩ code.fieldSort hfieldSortWF
      hmotiveLevel hstructIsTypeLift
      htypeFnLift hminorLift hmajorLift
    rw [hprojectorShape]
    apply hstruct.lam
    simpa [paramsLift, VExpr.liftN] using hbody

/-- Checked selecting minors determine the exact canonical capture spines
for every generated iota rule in the same source-order prefix. -/
theorem _root_.Lean4Lean.VStructureView.WF.toConstructorRuleCapturesPrefix_of_minorsWFPrefix
    (self : VStructureView.WF view env) (henv : env.ConversionRegular) {limit : Nat}
    (minors : view.MinorsWFPrefix env limit) :
    view.ConstructorRuleCapturesPrefix env limit := by
  intro U Γ levels params idx code hlimit hΓ hlevels hlevelsLength
    hparamsLength hparamsSpine hcode
  obtain ⟨fieldSort, hfieldSort, hcodeSort, -, -⟩ :=
    view.projectionCodes_get?_program_shape levels params hcode
  have minorsBefore : view.MinorsWFPrefix env idx := by
    intro U' Γ' levels' params' j prior hj
    exact minors (Nat.lt_trans hj hlimit)
  have programsBefore : view.ProgramsWFPrefix env idx :=
    self.toProgramsWFPrefix_of_minorsWFPrefix henv
      (limit := idx) minorsBefore
  have htypeFn := self.projectionTypeFn_hasType_of_programsPrefix henv
    programsBefore hΓ hlevels hlevelsLength hparamsLength
      hparamsSpine hcode
  have hminor := minors hlimit hΓ hlevels hlevelsLength hparamsLength
    hparamsSpine hcode
  have hmotiveLevel :
      view.generation.motiveLevel.inst
        (view.projectionLevels code.fieldSort levels) = code.fieldSort := by
    rw [hcodeSort]
    rw [List.getElem?_map] at hfieldSort
    obtain ⟨rawSort, hrawSort, rfl⟩ := Option.map_eq_some_iff.1 hfieldSort
    have hrawSortMem : rawSort ∈ view.fieldSorts :=
      List.mem_iff_getElem?.2 ⟨idx, hrawSort⟩
    exact self.motiveLevel_projectionLevels rawSort hrawSortMem levels
  have hcaptures := self.projectionRuleCaptureSpine henv
    levels hlevels hlevelsLength params hparamsLength hparamsSpine
    code.fieldSort hmotiveLevel htypeFn hminor
  simpa [VStructureView.ProjectionCode.liftN] using hcaptures

/-- Extend a source-ordered selecting-minor prefix by one field once the
already-generated projectors compute exactly on the canonical constructor.
The earlier minor prefix supplies their typing; the separate exactness
contract supplies only the iota equations needed by dependent substitution. -/
theorem _root_.Lean4Lean.VStructureView.WF.toMinorsWFPrefix_succ_of_constructorProjectorsExactPrefix
    (self : VStructureView.WF view env) (henv : env.ConversionRegular) {limit : Nat}
    (minors : view.MinorsWFPrefix env limit)
    (exact : view.ConstructorProjectorsExactPrefix env limit) :
    view.MinorsWFPrefix env (limit + 1) := by
  intro U Γ levels params idx code hlimit hΓ hlevels hlevelsLength
    hparamsLength hparamsSpine hcode
  by_cases hbefore : idx < limit
  · exact minors hbefore hΓ hlevels hlevelsLength hparamsLength
      hparamsSpine hcode
  have hidxEq : idx = limit := by omega
  subst idx
  obtain ⟨resultLevel, hparamsSpine₀⟩ := hparamsSpine
  let fields := view.specializedFields levels params
  let m := fields.length
  have hidx : limit < fields.length := by
    have := (List.getElem?_eq_some_iff.1 hcode).1
    simpa [fields] using this
  obtain ⟨fieldSort, hfieldSort, hcodeSort, hminorShape, -⟩ :=
    view.projectionCodes_get?_program_shape levels params hcode
  obtain ⟨field, hfield, -⟩ :=
    view.projectionCodes_get?_typeFn levels params hcode
  have hsortTel := self.specializedFields_onSortTel henv.ordered
    levels hlevels hlevelsLength params hparamsLength
    ⟨resultLevel, hparamsSpine₀⟩
  have hfieldsOnTel : env.OnTel U Γ fields := by
    simpa [fields] using hsortTel.toOnTel
  have hfieldsCtx : OnCtx (fields.reverse ++ Γ) (env.IsType U) :=
    hfieldsOnTel.toOnCtx hΓ
  have hfamily : env.HasType U Γ (.const view.name levels)
      (view.familyType.instL levels) := by
    apply VEnv.HasType.const self.family hlevels
    rw [view.generation.block.sourceType_uvars_eq]
    exact hlevelsLength
  have hstruct : env.HasType U Γ
      (view.structureType levels params) (.sort resultLevel) := by
    simpa [VStructureView.structureType] using
      hparamsSpine₀.hasType_appN hfamily
  have hconstructorPrefix := self.constructorPrefix_hasType henv.ordered
    levels hlevels hlevelsLength params hparamsLength
    ⟨resultLevel, hparamsSpine₀⟩
  have hconstructorPrefixWeak := hconstructorPrefix.weakN henv.ordered
    (Ctx.LiftN.zero (n := m) (Γ := Γ) fields.reverse
      (h := by simp [m]))
  have hconstructorPrefixSelf : env.HasType U
      (([] : List VExpr) ++ fields.reverse ++ Γ)
      ((VExpr.appN (.const view.constructorName levels) params).liftN m)
      ((VExpr.forallN fields
        ((view.structureType levels params).liftN m)).liftN
          (([] : List VExpr).length + fields.length)) := by
    simpa [fields, m] using hconstructorPrefixWeak
  have hmajor₀ := VEnv.HasType.appN_selfSpine
    (env := env) (U := U) (As := fields)
    (B := (view.structureType levels params).liftN m)
    (Δ := []) (Γ := Γ)
    (f := (VExpr.appN (.const view.constructorName levels) params).liftN m)
    hconstructorPrefixSelf
  have hmajor : env.HasType U (fields.reverse ++ Γ)
      (view.projectionConstructorApp levels params fields)
      ((view.structureType levels params).liftN m) := by
    simpa [fields, m, VStructureView.projectionConstructorApp,
      VExpr.liftN, VExpr.liftN_appN, VExpr.appN_append, List.map_map,
      Function.comp_def] using hmajor₀
  have programs : view.ProgramsWFPrefix env limit :=
    self.toProgramsWFPrefix_of_minorsWFPrefix henv minors
  have htypeFn := self.projectionTypeFn_hasType_of_programsPrefix henv
    programs hΓ hlevels hlevelsLength hparamsLength
    ⟨resultLevel, hparamsSpine₀⟩ hcode

  have hsortAt :
      (view.fieldSorts.map (VLevel.inst levels))[limit]? =
        some code.fieldSort := by
    simpa [hcodeSort] using hfieldSort
  obtain ⟨hprefixOriginal, -⟩ :=
    hsortTel.prefix_getElem? hfield hsortAt
  have hsortTelFull := hsortTel.weakN henv.ordered
    (Ctx.LiftN.zero (n := m) (Γ := Γ) fields.reverse
      (h := by simp [m]))
  have hfieldLiftGet :
      (VExpr.liftTelN m fields 0)[limit]? =
        some (field.liftN m limit) := by
    rw [VExpr.liftTelN_getElem?]
    simp [fields, hfield]
  have hsortTelFull' : env.OnSortTel U (fields.reverse ++ Γ)
      (VExpr.liftTelN m fields 0)
      (view.fieldSorts.map (VLevel.inst levels)) := by
    simpa [fields] using hsortTelFull
  obtain ⟨hprefixLift, hfieldLiftType⟩ :=
    hsortTelFull'.prefix_getElem? hfieldLiftGet hsortAt

  let paramsLift := params.map (VExpr.liftN m)
  have hparamsLengthLift : paramsLift.length = view.nparams := by
    simpa [paramsLift] using hparamsLength
  have hfamilyClosed : (view.familyType.instL levels).ClosedN 0 := by
    simpa using (henv.ordered.closedC self.family).instL
  have hparamsSpineLift : env.SpineWF U (fields.reverse ++ Γ)
      (view.familyType.instL levels) paramsLift (.sort resultLevel) := by
    have h := hparamsSpine₀.weakN henv.ordered
      (Ctx.LiftN.zero (n := m) (Γ := Γ) fields.reverse
        (h := by simp [m]))
    rw [hfamilyClosed.liftN_eq (Nat.zero_le _)] at h
    simpa [paramsLift, m, VExpr.liftN] using h
  have hstructLift : view.structureType levels paramsLift =
      (view.structureType levels params).liftN m := by
    simp [paramsLift]
  have hmajorLift : env.HasType U (fields.reverse ++ Γ)
      (view.projectionConstructorApp levels params fields)
      (view.structureType levels paramsLift) := by
    rwa [hstructLift]
  have hΓLift : OnCtx (fields.reverse ++ Γ) (env.IsType U) :=
    hfieldsCtx
  have hcodesLift := self.projectionCodes_liftN henv.ordered
    levels params hparamsLength m 0
  have hidxLift : limit <
      (view.projectionCodes levels paramsLift).length := by
    rw [← hcodesLift]
    simpa using (List.getElem?_eq_some_iff.1 hcode).1
  have hprior : ∀ {j : Nat}
      {prior : VStructureView.ProjectionCode}, j < limit →
      (view.projectionCodes levels paramsLift)[j]? = some prior →
      env.HasType U (fields.reverse ++ Γ) prior.projector
        (.forallE (view.structureType levels paramsLift)
          (.app prior.typeFn.lift (.bvar 0))) := by
    intro j prior hj hpriorCode
    exact programs hj hΓLift hlevels hlevelsLength hparamsLengthLift
      ⟨resultLevel, hparamsSpineLift⟩ hpriorCode
  have hargsLength :
      (view.projectionArgs levels paramsLift limit
        (view.projectionConstructorApp levels params fields)).length =
          limit :=
    view.projectionArgs_length levels paramsLift limit
      (view.projectionConstructorApp levels params fields)
      (Nat.le_of_lt hidxLift)
  obtain ⟨_, _, hleftFull⟩ :=
    VStructureView.projectionArgsSpineAux_of_prefix henv hΓLift
      hmajorLift hprior (.sort .zero) (Nat.le_refl limit)
        (Nat.le_of_lt (by simpa using hidxLift))
  have hspecializedLift :
      view.specializedFields levels paramsLift =
        VExpr.liftTelN m fields 0 := by
    simpa [paramsLift, fields] using
      self.specializedFields_liftN henv.ordered levels params
        hparamsLength m 0
  rw [hspecializedLift] at hleftFull
  rw [← List.take_append_drop limit (VExpr.liftTelN m fields 0),
    VExpr.forallN_append] at hleftFull
  have hprefixLength :
      (VExpr.liftTelN m fields 0 |>.take limit).length = limit := by
    rw [List.length_take, VExpr.liftTelN_length,
      Nat.min_eq_left (Nat.le_of_lt hidx)]
  have hleftPrefix := hleftFull.retarget
    (by simpa [hprefixLength] using hargsLength) (.sort code.fieldSort)

  have hrightPrefix₀ := hprefixOriginal.selfSpineWF
    (B := .sort code.fieldSort) (Δ := (fields.drop limit).reverse)
  have hrightPrefix : env.SpineWF U (fields.reverse ++ Γ)
      (VExpr.forallN (VExpr.liftTelN m fields 0 |>.take limit)
        (.sort code.fieldSort))
      (VExpr.bvarRevRange (m - limit) limit) (.sort code.fieldSort) := by
    have htakeLength : (fields.take limit).length = limit := by
      rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hidx)]
    have hdropLength : (fields.drop limit).length = m - limit := by
      simp [m]
    have htotalLength :
        (fields.drop limit).length + (fields.take limit).length = m := by
      rw [hdropLength, htakeLength]
      dsimp only [m]
      omega
    have hcontext : (fields.drop limit).reverse ++
        (fields.take limit).reverse ++ Γ = fields.reverse ++ Γ := by
      rw [← List.reverse_append, List.take_append_drop]
    rw [hcontext] at hrightPrefix₀
    simp only [List.length_reverse] at hrightPrefix₀
    rw [htotalLength, hdropLength, htakeLength] at hrightPrefix₀
    have hsource :
        (VExpr.forallN (fields.take limit) (.sort code.fieldSort)).liftN m =
          VExpr.forallN (VExpr.liftTelN m fields 0 |>.take limit)
            (.sort code.fieldSort) := by
      rw [VExpr.liftN_forallN, ← VExpr.liftTelN_take]
      rfl
    rw [hsource] at hrightPrefix₀
    simpa [VExpr.liftN] using hrightPrefix₀

  have hleftArgs :
      view.projectionArgs levels paramsLift limit
          (view.projectionConstructorApp levels params fields) =
        ((view.projectionCodes levels params).take limit).map fun prior =>
          .app (prior.projector.liftN m)
            (view.projectionConstructorApp levels params fields) := by
    unfold VStructureView.projectionArgs
    rw [← hcodesLift]
    simp [List.map_take, List.map_map,
      VStructureView.ProjectionCode.liftN, Function.comp_def]
  have hleftPrefix' : env.SpineWF U (fields.reverse ++ Γ)
      (VExpr.forallN (VExpr.liftTelN m fields 0 |>.take limit)
        (.sort code.fieldSort))
      (((view.projectionCodes levels params).take limit).map fun prior =>
        .app (prior.projector.liftN m)
          (view.projectionConstructorApp levels params fields))
      (.sort code.fieldSort) := by
    rw [hleftArgs] at hleftPrefix
    have hsortInst : (VExpr.sort code.fieldSort).instRev
        (((view.projectionCodes levels params).take limit).map fun prior =>
          .app (prior.projector.liftN m)
            (view.projectionConstructorApp levels params fields)) =
          .sort code.fieldSort :=
      VExpr.instRev_closedN _ (by trivial)
    rw [hsortInst] at hleftPrefix
    exact hleftPrefix
  have hpoint := exact (Nat.le_refl limit) hΓ hlevels hlevelsLength
    hparamsLength ⟨resultLevel, hparamsSpine₀⟩
    (Nat.le_of_lt (by simpa [fields] using hidx))
  have hpoint' : List.Forall₂
      (fun projected selected => projected = selected ∨
        env.IsDefEqU U (fields.reverse ++ Γ) projected selected)
      (((view.projectionCodes levels params).take limit).map fun prior =>
        VExpr.app (prior.projector.liftN m)
          (view.projectionConstructorApp levels params fields))
      (VExpr.bvarRevRange (m - limit) limit) := by
    simpa only [fields, m] using hpoint
  have hleftLength :
      (((view.projectionCodes levels params).take limit).map fun prior =>
        VExpr.app (prior.projector.liftN m)
          (view.projectionConstructorApp levels params fields)).length =
        (VExpr.liftTelN m fields 0 |>.take limit).length := by
    simp [hprefixLength, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt (by simpa [fields] using hidx))]
  have hinstEq := hprefixLift.instRev_defeq_of_spines henv hfieldsCtx
    hfieldLiftType hleftPrefix' hrightPrefix hleftLength hpoint'
  have hrightContract :
      (field.liftN m limit).instRev
          (VExpr.bvarRevRange (m - limit) limit) =
        field.liftN (m - limit) :=
    VExpr.instRev_liftN_bvarRevRange field m limit
      (Nat.le_of_lt hidx)

  have hcodeLift :
      (view.projectionCodes levels paramsLift)[limit]? =
        some (code.liftN m 0) := by
    rw [← hcodesLift, List.getElem?_map, hcode]
    rfl
  have hfieldLiftCode :
      (view.specializedFields levels paramsLift)[limit]? =
        some (field.liftN m limit) := by
    rw [hspecializedLift]
    exact hfieldLiftGet
  obtain ⟨fieldLift, typeBody, hfieldLiftCode', htypeFnLiftShape,
      htypeBodyContract⟩ :=
    view.projectionCodes_get?_typeFn_beta levels paramsLift hcodeLift
      (view.projectionConstructorApp levels params fields)
  have hfieldLiftEq : fieldLift = field.liftN m limit :=
    Option.some.inj (hfieldLiftCode'.symm.trans hfieldLiftCode)
  subst fieldLift
  have htypeFnFull := htypeFn.weakN henv.ordered
    (Ctx.LiftN.zero (n := m) (Γ := Γ) fields.reverse
      (h := by simp [m]))
  have htypeFnLift : env.HasType U (fields.reverse ++ Γ)
      (code.liftN m 0).typeFn
      (.forallE (view.structureType levels paramsLift)
        (.sort code.fieldSort)) := by
    simpa [VStructureView.ProjectionCode.liftN, hstructLift,
      VExpr.liftN] using htypeFnFull
  rw [htypeFnLiftShape] at htypeFnLift
  obtain ⟨_, ⟨typeBodyType, htypeBody⟩⟩ :=
    htypeFnLift.lam_inv henv.ordered hfieldsCtx
  have hbetaRaw := VEnv.IsDefEq.beta htypeBody hmajorLift
  have hleftArgsRaw :
      ((view.projectionCodes levels paramsLift).take limit).map
          (fun prior => VExpr.app prior.projector
            (view.projectionConstructorApp levels params fields)) =
        ((view.projectionCodes levels params).take limit).map fun prior =>
          VExpr.app (prior.projector.liftN m)
            (view.projectionConstructorApp levels params fields) := by
    simpa [VStructureView.projectionArgs] using hleftArgs
  rw [htypeBodyContract, VExpr.instRevAt_zero, hleftArgsRaw,
    ← htypeFnLiftShape] at hbetaRaw
  have hbeta : env.IsDefEqU U (fields.reverse ++ Γ)
      (.app (code.typeFn.liftN m)
        (view.projectionConstructorApp levels params fields))
      ((field.liftN m limit).instRev
        (((view.projectionCodes levels params).take limit).map fun prior =>
          .app (prior.projector.liftN m)
            (view.projectionConstructorApp levels params fields))) := by
    exact ⟨_, by simpa [VStructureView.ProjectionCode.liftN] using hbetaRaw⟩
  have hmotiveEq : env.IsDefEqU U (fields.reverse ++ Γ)
      (.app (code.typeFn.liftN m)
        (view.projectionConstructorApp levels params fields))
      (field.liftN (m - limit)) := by
    have h := henv.isDefEqU_trans hfieldsCtx hbeta hinstEq
    rwa [hrightContract] at h

  let q := m - 1 - limit
  have hqLt : q < fields.length := by
    dsimp only [q, m]
    omega
  have hfieldOriginal : fields[limit]? = some field := by
    simpa [fields] using hfield
  have hfieldReverse : fields.reverse[q]? = some field := by
    rw [List.getElem?_reverse hqLt,
      show fields.length - 1 - q = limit by
        dsimp only [q, m]
        omega,
      hfieldOriginal]
  have hfieldCtx : (fields.reverse ++ Γ)[q]? = some field := by
    rw [List.getElem?_append_left (by simpa using hqLt), hfieldReverse]
  have hbody : env.HasType U (fields.reverse ++ Γ) (.bvar q)
      (field.liftN (m - limit)) := by
    have hlookup := VEnv.HasType.bvar (env := env) (U := U)
      (Lookup.of_getElem? hfieldCtx)
    have hqSucc : q + 1 = m - limit := by
      dsimp only [q, m]
      omega
    rwa [hqSucc] at hlookup
  have hbodyExpected : env.HasType U (fields.reverse ++ Γ) (.bvar q)
      (.app (code.typeFn.liftN m)
        (view.projectionConstructorApp levels params fields)) :=
    henv.hasType_defeqU_r hfieldsCtx hmotiveEq.symm hbody
  have hminor := VEnv.HasType.lamN hfieldsOnTel hbodyExpected
  rw [hminorShape]
  simpa [VStructureView.projectionMinorType, fields, m, q] using hminor

private theorem List.Forall₂.of_getElem? {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β},
      xs.length = ys.length →
      (∀ {i : Nat} {x : α} {y : β},
        xs[i]? = some x → ys[i]? = some y → R x y) →
      List.Forall₂ R xs ys
  | [], [], _, _ => .nil
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen
  | x :: xs, y :: ys, hlen, h => by
      refine .cons (h (i := 0) rfl rfl) ?_
      apply List.Forall₂.of_getElem? (Nat.succ.inj hlen)
      intro i x' y' hx hy
      exact h (i := i + 1) (by simpa using hx) (by simpa using hy)

private theorem VExpr.bvarRevRange_getElem?
    (off count i : Nat) (hi : i < count) :
    (VExpr.bvarRevRange off count)[i]? =
      some (.bvar (off + (count - 1 - i))) := by
  induction count generalizing i with
  | zero => omega
  | succ count ih =>
      cases i with
      | zero => simp [VExpr.bvarRevRange]
      | succ i =>
          simp only [VExpr.bvarRevRange, List.getElem?_cons_succ]
          rw [ih i (by omega)]
          congr 3
          omega

/-- Checked generation turns source-ordered selecting-minor typing into the
complete generated projector-program certificate.  Motive functions and
recursor applications are reconstructed here; consumers need not certify
those deterministic pieces separately. -/
theorem _root_.Lean4Lean.VStructureView.WF.toProgramsWF_of_minors
    (self : VStructureView.WF view env) (henv : env.ConversionRegular)
    (minors : view.MinorsWF env) : view.ProgramsWF env := by
  intro U Γ levels params idx code hΓ hlevels hlevelsLength
    hparamsLength hparamsSpine hcode
  exact self.toProgramsWFPrefix_of_minorsWFPrefix henv
    (limit := idx + 1)
    (fun _ hΓ hlevels hlevelsLength hparamsLength hparamsSpine hcode =>
      minors hΓ hlevels hlevelsLength hparamsLength hparamsSpine hcode)
    (Nat.lt_succ_self idx) hΓ hlevels hlevelsLength hparamsLength
    hparamsSpine hcode

/-- Checked constructor generation and certified projector programs derive
the rule-independent, single-model reconstruction typing obligation. -/
theorem _root_.Lean4Lean.VStructureView.WF.toRebuildWF_of_programs
    (self : VStructureView.WF view env) (henv : env.ConversionRegular)
    (programs : view.ProgramsWF env) : view.RebuildWF env := by
  intro U Γ levels params major hΓ hlevels hlevelsLength
    hparamsLength hparamsSpine hmajor
  exact programs.etaRebuild_hasType_of_constructorPrefix henv hΓ hlevels
    hlevelsLength hparamsLength hparamsSpine hmajor
    (self.constructorPrefix_hasType henv.ordered levels hlevels
      hlevelsLength params hparamsLength hparamsSpine)

/-- A persistent family of rule-independent reconstruction proofs is exactly
the semantic input needed to package the deterministic checked descriptor as
a registry-valid `VStructEta.WF`. -/
theorem _root_.Lean4Lean.VStructureView.WF.toStructEtaWF_of_rebuilds
    (self : VStructureView.WF view env) (henv : env.Ordered)
    (rebuilds : ∀ {env' : VEnv}, env ≤ env' →
      env'.ConversionRegular → view.RebuildWF env') :
    (self.toStructEta henv).WF env where
  familyType_closed := by
    change view.familyType.ClosedN
    exact henv.closedC self.family
  rebuild_hasType := by
    intro env' hle hregular U Γ levels params major hΓ hlevels hlevelsLength
      hparamsLength hparamsSpine hmajor
    simpa using rebuilds hle hregular hΓ hlevels hlevelsLength hparamsLength
      hparamsSpine hmajor

theorem SpineWF.instNProjection {env : VEnv} {U k : Nat}
    {Γ₀ Γ₁ Γ : List VExpr} {e₀ A₀ : VExpr}
    (henv : env.Ordered)
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ)
    (h₀ : env.HasType U Γ₀ e₀ A₀) :
    ∀ {es : List VExpr} {A B : VExpr}, env.SpineWF U Γ₁ A es B →
      env.SpineWF U Γ (A.inst e₀ k)
        (es.map fun e => e.inst e₀ k) (B.inst e₀ k)
  | _, _, _, h => h.instN henv W h₀

/-- A generated projector computes on the matching generated constructor
once the registered rule's capture spine has been checked.  This is the
exact iota layer; constructor-head and parameter-prefix alignment are kept
outside this theorem. -/
theorem _root_.Lean4Lean.VStructureView.WF.projector_constructor_exact
    (self : VStructureView.WF view env) (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    {levels : List VLevel} (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    {params : List VExpr} (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    {idx : Nat} {code : VStructureView.ProjectionCode}
    (hcode : (view.projectionCodes levels params)[idx]? = some code)
    (hprojector : env.HasType U Γ code.projector
      (.forallE (view.structureType levels params)
        (.app code.typeFn.lift (.bvar 0))))
    {fields : List VExpr} (hfieldsLength :
      fields.length = (view.specializedFields levels params).length)
    {field : VExpr} (hfield : fields[idx]? = some field)
    (hctorType : env.HasType U Γ
      (VExpr.appN (.const view.constructorName levels) (params ++ fields))
      (view.structureType levels params))
    (hfieldsSpine : env.SpineWF U Γ
      (VExpr.forallN (view.specializedFields levels params) (.sort .zero))
      fields (.sort .zero))
    {B : VExpr}
    (hcaps : env.SpineWF U Γ
      ((view.generation.rule 0 view.constructor).type.instL
        (view.projectionLevels code.fieldSort levels))
      (params ++ [code.typeFn, code.minor] ++ fields) B) :
    env.IsDefEqU U Γ
      (.app code.projector
        (VExpr.appN (.const view.constructorName levels) (params ++ fields)))
      field := by
  obtain ⟨fieldSort, hfieldSort, hcodeSort, hminorShape,
      hprojectorShape⟩ :=
    view.projectionCodes_get?_program_shape levels params hcode
  have hsortTel := self.specializedFields_onSortTel henv.ordered
    levels hlevels hlevelsLength params hparamsLength hparamsSpine
  have hfieldSortWF : code.fieldSort.WF U := by
    rw [hcodeSort]
    exact hsortTel.sortWF hΓ hfieldSort
  let pLevels := view.projectionLevels code.fieldSort levels
  have hpLevelsWF : ∀ level ∈ pLevels, level.WF U :=
    VStructureView.projectionLevels_wf view code.fieldSort levels
      hfieldSortWF hlevels
  have hpLevelsLength : pLevels.length = view.generation.recUvars :=
    VStructureView.projectionLevels_length view code.fieldSort levels
      hlevelsLength
  have hruleMem : view.generation.rule 0 view.constructor ∈
      view.generation.generatedRules := by
    simp [VInductDecl.GenerationChecked.generatedRules,
      view.constructor_eq]
  have hregistered := self.rule_mem hruleMem
  have hruleWF := henv.ordered.defEqWF hregistered
  rw [hprojectorShape] at hprojector
  obtain ⟨_, ⟨projectorBodyType, hprojectorBody⟩⟩ :=
    hprojector.lam_inv henv.ordered hΓ
  have hprojectorBeta := VEnv.IsDefEq.beta hprojectorBody hctorType
  have hprojectorToRule : env.IsDefEqU U Γ
      (.app code.projector
        (VExpr.appN (.const view.constructorName levels) (params ++ fields)))
      (VExpr.appN (.const view.recursorName pLevels)
        (params ++ [code.typeFn, code.minor,
          VExpr.appN (.const view.constructorName levels)
            (params ++ fields)])) := by
    refine ⟨projectorBodyType.inst
      (VExpr.appN (.const view.constructorName levels) (params ++ fields)), ?_⟩
    rw [hprojectorShape]
    simpa [pLevels, VExpr.inst, VExpr.instN_appN, VExpr.inst_lift,
      VExpr.instVar_zero,
      List.map_append, List.map_map, Function.comp_def] using
        hprojectorBeta
  let gen := view.generation
  let Bs := view.constructor.fieldsR view.source.uvars view.source.nparams
    gen.elimination
  let m := Bs.length
  let rs := view.constructor.recArgsR view.source.uvars gen.elimination
  let binders := gen.paramsTel ++ gen.motiveType :: gen.minorTypes ++
    VExpr.liftTelN (gen.block.ctorPairs.length + 1) Bs 0
  let recBase := VExpr.appN
    (.const (.str gen.block.sourceType.name "rec") gen.recLevels)
    (VExpr.bvarRevRange m (view.source.nparams +
      gen.block.ctorPairs.length + 1))
  let idxR := view.constructor.resultIndicesR view.source.uvars
    gen.elimination |>.map fun expression =>
      expression.liftN (gen.block.ctorPairs.length + 1) m
  let ctorApp := VExpr.appN
    (.const view.constructor.raw.name gen.sourceLevels)
    (VExpr.bvarRevRange (m + gen.block.ctorPairs.length + 1)
        view.source.nparams ++ VExpr.bvarRevRange 0 m)
  let ihs := rs.map fun recursive =>
    recursive.ruleCall m gen.block.ctorPairs.length recBase
  let lhsBody := VExpr.appN recBase (idxR ++ [ctorApp])
  let rhsBody := VExpr.appN
    (.bvar (gen.block.ctorPairs.length - 1 - 0 + m))
    (VExpr.bvarRevRange 0 m ++ ihs)
  let typeBody := VExpr.appN
    (.bvar (gen.block.ctorPairs.length + m)) (idxR ++ [ctorApp])
  have hlhs₀ := hruleWF.1
  change env.HasType gen.recUvars [] (VExpr.lamN binders lhsBody)
    (VExpr.forallN binders typeBody) at hlhs₀
  have hrhs₀ := hruleWF.2
  change env.HasType gen.recUvars [] (VExpr.lamN binders rhsBody)
    (VExpr.forallN binders typeBody) at hrhs₀
  have hlhs : env.HasType U Γ
      ((VExpr.lamN binders lhsBody).instL pLevels)
      ((VExpr.forallN binders typeBody).instL pLevels) :=
    (hlhs₀.instL hpLevelsWF).weak0 henv.ordered
  have hrhs : env.HasType U Γ
      ((VExpr.lamN binders rhsBody).instL pLevels)
      ((VExpr.forallN binders typeBody).instL pLevels) :=
    (hrhs₀.instL hpLevelsWF).weak0 henv.ordered
  rw [VExpr.instL_lamN, VExpr.instL_forallN] at hlhs hrhs
  have hcaps' : env.SpineWF U Γ
      (VExpr.forallN (binders.map (VExpr.instL pLevels))
        (typeBody.instL pLevels))
      (params ++ [code.typeFn, code.minor] ++ fields) B := by
    change env.SpineWF U Γ
      ((VExpr.forallN binders typeBody).instL pLevels)
      (params ++ [code.typeFn, code.minor] ++ fields) B at hcaps
    simpa only [VExpr.instL_forallN] using hcaps
  let S := self.toGenerationEnv henv.ordered
  have hparamsTelLength : gen.paramsTel.length = view.nparams := by
    simp [gen, VInductDecl.GenerationChecked.paramsTel,
      S.generationParams_length]
  have hspecializedLength :
      (view.specializedFields levels params).length =
        (view.constructor.rawFields view.nparams).length := by
    simp [VStructureView.specializedFields, VStructureView.fields]
  have hBsLength : Bs.length =
      (view.constructor.rawFields view.nparams).length := by
    simpa [Bs] using
      (VInductDecl.NormalizedCtor.fieldsR_length
        (source := view.source) view.constructor
        (mode := gen.elimination))
  have hcapturesLength :
      (params ++ [code.typeFn, code.minor] ++ fields).length =
        (binders.map (VExpr.instL pLevels)).length := by
    simp only [List.length_append, List.length_cons, List.length_nil,
      List.length_map, VExpr.liftTelN_length, binders]
    rw [hparamsLength, hfieldsLength, hspecializedLength,
      hparamsTelLength, gen.minorTypes_length, view.constructor_eq,
      hBsLength]
    simp
  obtain ⟨hlhsTel, lhsType, hlhsBody⟩ :=
    VEnv.HasType.lamN_wf henv.ordered hΓ hlhs
  obtain ⟨hrhsTel, rhsType, hrhsBody⟩ :=
    VEnv.HasType.lamN_wf henv.ordered hΓ hrhs
  have hlhsSpine := hcaps'.retarget hcapturesLength lhsType
  have hrhsSpine := hcaps'.retarget hcapturesLength rhsType
  have hcollapseL := VEnv.IsDefEq.appN_lamN henv.ordered
    hlhsTel hlhsBody hlhsSpine hcapturesLength
  have hcollapseR := VEnv.IsDefEq.appN_lamN henv.ordered
    hrhsTel hrhsBody hrhsSpine hcapturesLength
  have hregisteredRule : env.IsDefEq U Γ
      ((view.generation.rule 0 view.constructor).lhs.instL pLevels)
      ((view.generation.rule 0 view.constructor).rhs.instL pLevels)
      ((view.generation.rule 0 view.constructor).type.instL pLevels) :=
    .extra hregistered hpLevelsWF hpLevelsLength
  have happlied := VEnv.IsDefEq.appN_congr hregisteredRule hcaps
  rw [show (view.generation.rule 0 view.constructor).lhs =
      VExpr.lamN binders lhsBody from rfl,
    show (view.generation.rule 0 view.constructor).rhs =
      VExpr.lamN binders rhsBody from rfl,
    VExpr.instL_lamN] at happlied
  simp only [VExpr.instL_lamN] at happlied
  have hiotaBodies : env.IsDefEqU U Γ
      (VExpr.instRev (lhsBody.instL pLevels)
        (params ++ [code.typeFn, code.minor] ++ fields))
      (VExpr.instRev (rhsBody.instL pLevels)
        (params ++ [code.typeFn, code.minor] ++ fields)) :=
    henv.isDefEqU_trans hΓ ⟨_, hcollapseL.symm⟩
      (henv.isDefEqU_trans hΓ ⟨_, happlied⟩ ⟨_, hcollapseR⟩)
  have hconstructorMem : view.constructor ∈
      view.generation.block.ctorPairs := by
    simp [view.constructor_eq]
  have hresultIndices : view.constructor.view.resultIndices = [] := by
    apply List.length_eq_zero_iff.1
    rw [S.viewResultIndices_length hconstructorMem]
    simp [view.checked_indices_eq]
  have hfieldsLengthRaw : fields.length = m := by
    exact hfieldsLength.trans (hspecializedLength.trans hBsLength.symm)
  have hprefixLength :
      (params ++ [code.typeFn, code.minor]).length = view.nparams + 2 := by
    simp [hparamsLength]
  have hcapturesLength' :
      (params ++ [code.typeFn, code.minor] ++ fields).length =
        view.nparams + 2 + m := by
    simp [hparamsLength, hfieldsLengthRaw]
    omega
  have hsegCommon :
      (VExpr.bvarRevRange m (view.nparams + 2)).map
          (VExpr.instRev ·
            (params ++ [code.typeFn, code.minor] ++ fields)) =
        params ++ [code.typeFn, code.minor] := by
    have h := VExpr.map_instRev_bvarRevRange_seg
      (params ++ [code.typeFn, code.minor] ++ fields)
      (view.nparams + 2) m (by rw [hcapturesLength']; omega)
    rw [← hparamsLength] at h ⊢
    rw [show (params ++ [code.typeFn, code.minor] ++ fields).length -
        m - (params.length + 2) = 0 by
          simp only [List.length_append, List.length_cons, List.length_nil]
          rw [hfieldsLengthRaw]
          omega,
      List.drop_zero] at h
    rw [List.take_append,
      show params.length + 2 =
        (params ++ [code.typeFn, code.minor]).length by simp,
      List.take_length] at h
    simpa using h
  have hsegParams :
      (VExpr.bvarRevRange (m + 2) view.nparams).map
          (VExpr.instRev ·
            (params ++ [code.typeFn, code.minor] ++ fields)) = params := by
    have h := VExpr.map_instRev_bvarRevRange_seg
      (params ++ [code.typeFn, code.minor] ++ fields)
      view.nparams (m + 2) (by rw [hcapturesLength']; omega)
    rw [← hparamsLength] at h ⊢
    rw [show (params ++ [code.typeFn, code.minor] ++ fields).length -
        (m + 2) - params.length = 0 by
          simp only [List.length_append, List.length_cons, List.length_nil]
          rw [hfieldsLengthRaw]
          omega,
      List.drop_zero] at h
    simpa using h
  have hsegFields :
      (VExpr.bvarRevRange 0 m).map
          (VExpr.instRev ·
            (params ++ [code.typeFn, code.minor] ++ fields)) = fields := by
    have h := VExpr.map_instRev_bvarRevRange_seg
      (params ++ [code.typeFn, code.minor] ++ fields) m 0
      (by rw [hcapturesLength']; omega)
    rw [show (params ++ [code.typeFn, code.minor] ++ fields).length -
        0 - m = view.nparams + 2 by rw [hcapturesLength']; omega,
      show view.nparams + 2 =
        (params ++ [code.typeFn, code.minor]).length by
          exact hprefixLength.symm,
      List.drop_left] at h
    have htake : fields.take m = fields :=
      List.take_of_length_le (Nat.le_of_eq hfieldsLengthRaw)
    rw [htake] at h
    exact h
  have hsourceLevels := VStructureView.sourceLevels_projectionLevels
    view code.fieldSort levels hlevelsLength
  have hrecLevels : gen.recLevels.map (VLevel.inst pLevels) = pLevels := by
    exact VLevel.inst_map_id hpLevelsLength
  have hrecConst :
      VExpr.instRev
          ((.const (.str gen.block.sourceType.name "rec") gen.recLevels :
            VExpr).instL pLevels)
          (params ++ [code.typeFn, code.minor] ++ fields) =
        .const view.recursorName pLevels := by
    rw [VExpr.instRev_closedN _ (by trivial)]
    simp only [VExpr.instL]
    rw [hrecLevels]
    rfl
  have hsegCommonL :
      (VExpr.bvarRevRange m (view.nparams + 2)).map
          (fun expression => VExpr.instRev (expression.instL pLevels)
            (params ++ [code.typeFn, code.minor] ++ fields)) =
        params ++ [code.typeFn, code.minor] := by
    calc
      _ = ((VExpr.bvarRevRange m (view.nparams + 2)).map
            (VExpr.instL pLevels)).map
          (VExpr.instRev ·
            (params ++ [code.typeFn, code.minor] ++ fields)) := by
          rw [List.map_map]
          exact List.map_congr_left fun _ _ => rfl
      _ = _ := by
        rw [VExpr.bvarRevRange_map_instL]
        exact hsegCommon
  have hsegParamsL :
      (VExpr.bvarRevRange (m + 2) view.nparams).map
          (fun expression => VExpr.instRev (expression.instL pLevels)
            (params ++ [code.typeFn, code.minor] ++ fields)) = params := by
    calc
      _ = ((VExpr.bvarRevRange (m + 2) view.nparams).map
            (VExpr.instL pLevels)).map
          (VExpr.instRev ·
            (params ++ [code.typeFn, code.minor] ++ fields)) := by
          rw [List.map_map]
          exact List.map_congr_left fun _ _ => rfl
      _ = _ := by
        rw [VExpr.bvarRevRange_map_instL]
        exact hsegParams
  have hsegFieldsL :
      (VExpr.bvarRevRange 0 m).map
          (fun expression => VExpr.instRev (expression.instL pLevels)
            (params ++ [code.typeFn, code.minor] ++ fields)) = fields := by
    calc
      _ = ((VExpr.bvarRevRange 0 m).map
            (VExpr.instL pLevels)).map
          (VExpr.instRev ·
            (params ++ [code.typeFn, code.minor] ++ fields)) := by
          rw [List.map_map]
          exact List.map_congr_left fun _ _ => rfl
      _ = _ := by
        rw [VExpr.bvarRevRange_map_instL]
        exact hsegFields
  have hidxRNil : idxR = [] := by
    simp [idxR, VInductDecl.NormalizedCtor.resultIndicesR,
      hresultIndices]
  have hrecBaseShape :
      VExpr.instRev (recBase.instL pLevels)
          (params ++ [code.typeFn, code.minor] ++ fields) =
        VExpr.appN (.const view.recursorName pLevels)
          (params ++ [code.typeFn, code.minor]) := by
    rw [show recBase = VExpr.appN
        (.const (.str gen.block.sourceType.name "rec") gen.recLevels)
        (VExpr.bvarRevRange m (view.nparams + 2)) by
          unfold recBase
          rw [view.constructor_eq]
          rfl,
      VExpr.instL_appN, VExpr.instRev_appN, hrecConst]
    rw [List.map_map]
    exact congrArg (VExpr.appN (.const view.recursorName pLevels))
      hsegCommonL
  have hctorShape :
      VExpr.instRev (ctorApp.instL pLevels)
          (params ++ [code.typeFn, code.minor] ++ fields) =
        VExpr.appN (.const view.constructorName levels)
          (params ++ fields) := by
    rw [show ctorApp = VExpr.appN
        (.const view.constructorName gen.sourceLevels)
        (VExpr.bvarRevRange (m + 2) view.nparams ++
          VExpr.bvarRevRange 0 m) by
          unfold ctorApp
          rw [view.constructor_eq]
          rfl,
      VExpr.instL_appN, VExpr.instRev_appN]
    rw [VExpr.instRev_closedN _ (by trivial)]
    simp only [VExpr.instL]
    rw [hsourceLevels]
    simp only [List.map_append, List.map_map, Function.comp_def]
    rw [hsegParamsL, hsegFieldsL]
  have hleftShape :
      VExpr.instRev (lhsBody.instL pLevels)
          (params ++ [code.typeFn, code.minor] ++ fields) =
        VExpr.appN (.const view.recursorName pLevels)
          (params ++ [code.typeFn, code.minor,
            VExpr.appN (.const view.constructorName levels)
              (params ++ fields)]) := by
    rw [show lhsBody = VExpr.appN recBase (idxR ++ [ctorApp]) by
          rfl,
      VExpr.instL_appN, VExpr.instRev_appN, hrecBaseShape, hidxRNil,
      List.nil_append]
    simp only [List.map_cons, List.map_nil, hctorShape]
    rw [← VExpr.appN_append]
    simp only [List.append_assoc]
    rfl
  have hminorCapture :
      VExpr.instRev (.bvar m)
          (params ++ [code.typeFn, code.minor] ++ fields) =
        code.minor := by
    have h := VExpr.map_instRev_bvarRevRange_seg
      (params ++ [code.typeFn, code.minor] ++ fields) 1 m
      (by rw [hcapturesLength']; omega)
    rw [show (params ++ [code.typeFn, code.minor] ++ fields).length -
        m - 1 = params.length + 1 by
          rw [hcapturesLength', hparamsLength]
          omega] at h
    simpa [VExpr.bvarRevRange] using h
  have hrightBodyShape :
      rhsBody = VExpr.appN (.bvar m) (VExpr.bvarRevRange 0 m) := by
    simp [rhsBody, ihs, rs, gen,
      VInductDecl.NormalizedCtor.recArgsR, view.recursive_eq,
      view.constructor_eq]
  have hrightShape :
      VExpr.instRev (rhsBody.instL pLevels)
          (params ++ [code.typeFn, code.minor] ++ fields) =
        VExpr.appN code.minor fields := by
    rw [hrightBodyShape, VExpr.instL_appN,
      VExpr.bvarRevRange_map_instL, VExpr.instRev_appN]
    simp only [VExpr.instL]
    rw [hminorCapture, hsegFields]
  rw [hleftShape, hrightShape] at hiotaBodies
  obtain ⟨selectedType, hselectedType, -⟩ :=
    view.projectionCodes_get?_typeFn levels params hcode
  have hidxLt : idx < (view.specializedFields levels params).length :=
    (List.getElem?_eq_some_iff.1 hselectedType).1
  let q := (view.specializedFields levels params).length - 1 - idx
  have hqLt : q < (view.specializedFields levels params).length := by
    simp only [q]
    omega
  have hselectedReverse :
      (view.specializedFields levels params).reverse[q]? =
        some selectedType := by
    rw [List.getElem?_reverse hqLt,
      show (view.specializedFields levels params).length - 1 - q = idx by
        simp only [q]
        omega,
      hselectedType]
  have hselectedCtx :
      ((view.specializedFields levels params).reverse ++ Γ)[q]? =
        some selectedType := by
    rw [List.getElem?_append_left (by simpa using hqLt),
      hselectedReverse]
  have hminorBodyType : env.HasType U
      ((view.specializedFields levels params).reverse ++ Γ)
      (.bvar q) (selectedType.liftN (q + 1)) :=
    .bvar (Lookup.of_getElem? hselectedCtx)
  have hminorSpine := hfieldsSpine.retarget hfieldsLength
    (selectedType.liftN (q + 1))
  have hminorBetaRaw := VEnv.IsDefEq.appN_lamN henv.ordered
    hsortTel.toOnTel hminorBodyType hminorSpine hfieldsLength
  have hfieldInst : VExpr.instRev (.bvar q) fields = field := by
    have h := VExpr.map_instRev_bvarRevRange_seg fields 1 q
      (by rw [hfieldsLength]; exact Nat.add_one_le_iff.2 hqLt)
    rw [show fields.length - q - 1 = idx by
      rw [hfieldsLength]
      simp only [q]
      omega] at h
    obtain ⟨hidxFields, hfieldGet⟩ :=
      List.getElem?_eq_some_iff.1 hfield
    rw [List.drop_eq_getElem_cons hidxFields, hfieldGet,
      List.take_succ_cons] at h
    simpa [VExpr.bvarRevRange] using h
  have hminorBeta : env.IsDefEqU U Γ
      (VExpr.appN code.minor fields) field := by
    refine ⟨VExpr.instRev (selectedType.liftN (q + 1)) fields, ?_⟩
    rw [hminorShape]
    simpa only [hfieldInst] using hminorBetaRaw
  exact henv.isDefEqU_trans hΓ hprojectorToRule
    (henv.isDefEqU_trans hΓ hiotaBodies hminorBeta)

/-- Registered generated-iota rules turn canonical capture-spine typing into
the exact projector equations consumed by the dependent minor induction. -/
theorem _root_.Lean4Lean.VStructureView.WF.toConstructorProjectorsExactPrefix_of_ruleCaptures
    (self : VStructureView.WF view env) (henv : env.ConversionRegular) {limit : Nat}
    (minors : view.MinorsWFPrefix env limit)
    (captures : view.ConstructorRuleCapturesPrefix env limit) :
    view.ConstructorProjectorsExactPrefix env limit := by
  intro U Γ levels params count hcount hΓ hlevels hlevelsLength
    hparamsLength hparamsSpine hcountCodes
  obtain ⟨resultLevel, hparamsSpine₀⟩ := hparamsSpine
  let fields := view.specializedFields levels params
  let m := fields.length
  have hcountFields : count ≤ m := by
    simpa [fields, m] using hcountCodes
  have hsortTel := self.specializedFields_onSortTel henv.ordered
    levels hlevels hlevelsLength params hparamsLength
    ⟨resultLevel, hparamsSpine₀⟩
  have hfieldsOnTel : env.OnTel U Γ fields := by
    simpa [fields] using hsortTel.toOnTel
  have hfieldsCtx : OnCtx (fields.reverse ++ Γ) (env.IsType U) :=
    hfieldsOnTel.toOnCtx hΓ
  have hfamily : env.HasType U Γ (.const view.name levels)
      (view.familyType.instL levels) := by
    apply VEnv.HasType.const self.family hlevels
    rw [view.generation.block.sourceType_uvars_eq]
    exact hlevelsLength
  have hstruct : env.HasType U Γ
      (view.structureType levels params) (.sort resultLevel) := by
    simpa [VStructureView.structureType] using
      hparamsSpine₀.hasType_appN hfamily
  have hconstructorPrefix := self.constructorPrefix_hasType henv.ordered
    levels hlevels hlevelsLength params hparamsLength
    ⟨resultLevel, hparamsSpine₀⟩
  have hconstructorPrefixWeak := hconstructorPrefix.weakN henv.ordered
    (Ctx.LiftN.zero (n := m) (Γ := Γ) fields.reverse
      (h := by simp [m]))
  have hconstructorPrefixSelf : env.HasType U
      (([] : List VExpr) ++ fields.reverse ++ Γ)
      ((VExpr.appN (.const view.constructorName levels) params).liftN m)
      ((VExpr.forallN fields
        ((view.structureType levels params).liftN m)).liftN
          (([] : List VExpr).length + fields.length)) := by
    simpa [fields, m] using hconstructorPrefixWeak
  have hmajor₀ := VEnv.HasType.appN_selfSpine
    (env := env) (U := U) (As := fields)
    (B := (view.structureType levels params).liftN m)
    (Δ := []) (Γ := Γ)
    (f := (VExpr.appN (.const view.constructorName levels) params).liftN m)
    hconstructorPrefixSelf
  have hmajor : env.HasType U (fields.reverse ++ Γ)
      (view.projectionConstructorApp levels params fields)
      ((view.structureType levels params).liftN m) := by
    simpa [fields, m, VStructureView.projectionConstructorApp,
      VExpr.liftN, VExpr.liftN_appN, VExpr.appN_append, List.map_map,
      Function.comp_def] using hmajor₀
  let paramsLift := params.map (VExpr.liftN m)
  have hparamsLengthLift : paramsLift.length = view.nparams := by
    simpa [paramsLift] using hparamsLength
  have hfamilyClosed : (view.familyType.instL levels).ClosedN 0 := by
    simpa using (henv.ordered.closedC self.family).instL
  have hparamsSpineLift : env.SpineWF U (fields.reverse ++ Γ)
      (view.familyType.instL levels) paramsLift (.sort resultLevel) := by
    have h := hparamsSpine₀.weakN henv.ordered
      (Ctx.LiftN.zero (n := m) (Γ := Γ) fields.reverse
        (h := by simp [m]))
    rw [hfamilyClosed.liftN_eq (Nat.zero_le _)] at h
    simpa [paramsLift, m, VExpr.liftN] using h
  have hstructLift : view.structureType levels paramsLift =
      (view.structureType levels params).liftN m := by
    simp [paramsLift]
  have hmajorLift : env.HasType U (fields.reverse ++ Γ)
      (view.projectionConstructorApp levels params fields)
      (view.structureType levels paramsLift) := by
    rwa [hstructLift]
  have hcodesLift := self.projectionCodes_liftN henv.ordered
    levels params hparamsLength m 0
  have hspecializedLift :
      view.specializedFields levels paramsLift =
        VExpr.liftTelN m fields 0 := by
    simpa [paramsLift, fields] using
      self.specializedFields_liftN henv.ordered levels params
        hparamsLength m 0
  have hfieldArgsSpine₀ := hfieldsOnTel.selfSpineWF
    (B := .sort .zero) (Δ := ([] : List VExpr))
  have hfieldArgsSpine : env.SpineWF U (fields.reverse ++ Γ)
      (VExpr.forallN (view.specializedFields levels paramsLift)
        (.sort .zero))
      (VExpr.bvarRevRange 0 m) (.sort .zero) := by
    rw [hspecializedLift]
    have hsource :
        (VExpr.forallN fields (.sort .zero)).liftN m =
          VExpr.forallN (VExpr.liftTelN m fields 0) (.sort .zero) := by
      rw [VExpr.liftN_forallN]
      rfl
    rw [← hsource]
    simpa [m, VExpr.liftN] using hfieldArgsSpine₀
  have hfieldsLength :
      (VExpr.bvarRevRange 0 m).length =
        (view.specializedFields levels paramsLift).length := by
    rw [VExpr.bvarRevRange_length, hspecializedLift,
      VExpr.liftTelN_length]
  have hctor : env.HasType U (fields.reverse ++ Γ)
      (VExpr.appN (.const view.constructorName levels)
        (paramsLift ++ VExpr.bvarRevRange 0 m))
      (view.structureType levels paramsLift) := by
    simpa [VStructureView.projectionConstructorApp, paramsLift] using
      hmajorLift
  have programs : view.ProgramsWFPrefix env limit :=
    self.toProgramsWFPrefix_of_minorsWFPrefix henv minors
  apply List.Forall₂.of_getElem?
  · rw [List.length_map, List.length_take,
      VExpr.bvarRevRange_length,
      Nat.min_eq_left hcountCodes]
  intro i projected selected hprojected hselected
  have hiCount : i < count := by
    have := (List.getElem?_eq_some_iff.1 hprojected).1
    simp only [List.length_map] at this
    rw [List.length_take, Nat.min_eq_left hcountCodes] at this
    exact this
  rw [List.getElem?_map,
    List.getElem?_take_of_lt hiCount] at hprojected
  obtain ⟨prior, hpriorCode, hprojectedEq⟩ :=
    Option.map_eq_some_iff.1 hprojected
  subst projected
  have hselectedCanonical :=
    VExpr.bvarRevRange_getElem? (m - count) count i hiCount
  have hselectedEq : selected = .bvar (m - 1 - i) := by
    have heq := Option.some.inj (hselected.symm.trans hselectedCanonical)
    rw [show m - count + (count - 1 - i) = m - 1 - i by omega] at heq
    exact heq
  subst selected
  have hiLimit : i < limit := Nat.lt_of_lt_of_le hiCount hcount
  have hcodeLift :
      (view.projectionCodes levels paramsLift)[i]? =
        some (prior.liftN m 0) := by
    rw [← hcodesLift, List.getElem?_map, hpriorCode]
    rfl
  have hprojector := programs hiLimit hfieldsCtx hlevels hlevelsLength
    hparamsLengthLift ⟨resultLevel, hparamsSpineLift⟩ hcodeLift
  have hfieldArg : (VExpr.bvarRevRange 0 m)[i]? =
      some (.bvar (m - 1 - i)) := by
    have hiM : i < m := Nat.lt_of_lt_of_le hiCount hcountFields
    simpa using VExpr.bvarRevRange_getElem? 0 m i hiM
  obtain ⟨_, hcaptures⟩ :=
    captures hiLimit hΓ hlevels hlevelsLength hparamsLength
      ⟨resultLevel, hparamsSpine₀⟩ hpriorCode
  have hiota := self.projector_constructor_exact henv hfieldsCtx
    hlevels hlevelsLength hparamsLengthLift
    ⟨resultLevel, hparamsSpineLift⟩ hcodeLift hprojector
    hfieldsLength hfieldArg hctor hfieldArgsSpine hcaptures
  exact .inr (by
    simpa [VStructureView.ProjectionCode.liftN,
      VStructureView.projectionConstructorApp, paramsLift] using hiota)

/-- Advance the selecting-minor prefix using only its already established
source-order segment.  Canonical rule captures and exact earlier-projector
iota are now derived internally from checked generation. -/
theorem _root_.Lean4Lean.VStructureView.WF.toMinorsWFPrefix_succ
    (self : VStructureView.WF view env) (henv : env.ConversionRegular) {limit : Nat}
    (minors : view.MinorsWFPrefix env limit) :
    view.MinorsWFPrefix env (limit + 1) := by
  have captures : view.ConstructorRuleCapturesPrefix env limit :=
    self.toConstructorRuleCapturesPrefix_of_minorsWFPrefix henv
      (limit := limit) minors
  have exact : view.ConstructorProjectorsExactPrefix env limit :=
    self.toConstructorProjectorsExactPrefix_of_ruleCaptures
      henv (limit := limit) minors captures
  apply self.toMinorsWFPrefix_succ_of_constructorProjectorsExactPrefix
    henv (limit := limit)
  · exact minors
  · exact exact

/-- Every generated selecting minor is well typed.  The proof iterates the
source-order prefix step, so each dependent field uses only projectors whose
minors have already been established. -/
theorem _root_.Lean4Lean.VStructureView.WF.toMinorsWF
    (self : VStructureView.WF view env) (henv : env.ConversionRegular) :
    view.MinorsWF env := by
  have prefixes : ∀ limit, view.MinorsWFPrefix env limit := by
    intro limit
    induction limit with
    | zero =>
        intro U Γ levels params idx code hidx
        omega
    | succ limit ih =>
        exact self.toMinorsWFPrefix_succ henv (limit := limit) ih
  intro U Γ levels params idx code hΓ hlevels hlevelsLength
    hparamsLength hparamsSpine hcode
  exact prefixes (idx + 1) (Nat.lt_succ_self idx) hΓ hlevels
    hlevelsLength hparamsLength hparamsSpine hcode

/-- Checked structure generation determines every generated projector
program; selecting-minor typing is no longer an external premise. -/
theorem _root_.Lean4Lean.VStructureView.WF.toProgramsWF
    (self : VStructureView.WF view env) (henv : env.ConversionRegular) :
    view.ProgramsWF env :=
  self.toProgramsWF_of_minors henv (self.toMinorsWF henv)

/-- Checked structure generation determines the canonical reconstruction
typing in the current Theory environment. -/
theorem _root_.Lean4Lean.VStructureView.WF.toRebuildWF
    (self : VStructureView.WF view env) (henv : env.ConversionRegular) :
    view.RebuildWF env :=
  self.toRebuildWF_of_programs henv (self.toProgramsWF henv)

/-- Checked generation supplies the persistent structure-eta certificate.
The retained inventory may grow through raw `VEnv.LE`, while each actual
typing target supplies the conversion-regularity laws derived from its own
`VEnv.WF` proof. -/
theorem _root_.Lean4Lean.VStructureView.WF.toStructEtaWF
    (self : VStructureView.WF view env) (henv : env.WF) :
    (self.toStructEta henv.ordered).WF env :=
  self.toStructEtaWF_of_rebuilds henv.ordered fun hle hregular =>
    (self.mono hle).toRebuildWF hregular

/-- Environment-indexed projection semantics.

The universe and parameter spines are explicit.  The major premise must have
the exact instantiated structure type, and the result is the unique program
computed by the registered view. -/
structure TrProj (env : VEnv) (U : Nat) (Γ : List VExpr)
    (view : VStructureView) (levels : List VLevel) (params : List VExpr)
    (idx : Nat) (major result : VExpr) : Prop where
  viewWF : VStructureView.WF view env
  levelsWF : ∀ level ∈ levels, level.WF U
  levels_length : levels.length = view.uvars
  params_length : params.length = view.nparams
  paramsSpine : ∃ resultLevel,
    env.SpineWF U Γ (view.familyType.instL levels)
      params (.sort resultLevel)
  majorType : env.HasType U Γ major (view.structureType levels params)
  program : ∃ code : VStructureView.ProjectionCode,
    (view.projectionCodes levels params)[idx]? = some code ∧
      result = .app code.projector major ∧
      env.HasType U Γ code.projector
        (.forallE (view.structureType levels params)
          (.app code.typeFn.lift (.bvar 0)))

/-- The projection-specific output of registered constructor-head inversion.

This package performs no iota computation.  It only aligns a constructor
normal form and one selected runtime argument with the canonical registered
view, and supplies the typed spines needed by
`projector_constructor_exact`. -/
structure ProjectionConstructorAlignment (env : VEnv) (U : Nat)
    (Γ : List VExpr) (view : VStructureView) (levels : List VLevel)
    (params : List VExpr) (idx : Nat)
    (code : VStructureView.ProjectionCode)
    (runtimeConstructorName : Name) (runtimeMajor runtimeField : VExpr) where
  constructor_name_eq : runtimeConstructorName = view.constructorName
  fields : List VExpr
  field : VExpr
  fields_length :
    fields.length = (view.specializedFields levels params).length
  field_get : fields[idx]? = some field
  constructorType : env.HasType U Γ
    (VExpr.appN (.const view.constructorName levels) (params ++ fields))
    (view.structureType levels params)
  fieldsSpine : env.SpineWF U Γ
    (VExpr.forallN (view.specializedFields levels params) (.sort .zero))
    fields (.sort .zero)
  captures : ∃ B, env.SpineWF U Γ
    ((view.generation.rule 0 view.constructor).type.instL
      (view.projectionLevels code.fieldSort levels))
    (params ++ [code.typeFn, code.minor] ++ fields) B
  major_eq : env.IsDefEqU U Γ runtimeMajor
    (VExpr.appN (.const view.constructorName levels) (params ++ fields))
  field_eq : env.IsDefEqU U Γ runtimeField field

/-- Consume registered-head alignment with the separately proved exact iota
theorem.  This keeps the transitional injectivity boundary from hiding the
projection computation itself. -/
theorem TrProj.projector_constructor_aligned
    (self : VEnv.TrProj env U Γ view levels params idx major result)
    (henv : env.WF) (hΓ : OnCtx Γ (env.IsType U))
    {code : VStructureView.ProjectionCode}
    (hcode : (view.projectionCodes levels params)[idx]? = some code)
    (hprojector : env.HasType U Γ code.projector
      (.forallE (view.structureType levels params)
        (.app code.typeFn.lift (.bvar 0))))
    {runtimeMajor runtimeField : VExpr}
    {runtimeConstructorName : Name}
    (alignment : ProjectionConstructorAlignment env U Γ view levels params idx
      code runtimeConstructorName runtimeMajor runtimeField) :
    env.IsDefEqU U Γ (.app code.projector runtimeMajor) runtimeField := by
  have hmajorEq := alignment.major_eq.of_r henv hΓ
    alignment.constructorType
  have hmajorCongr : env.IsDefEqU U Γ
      (.app code.projector runtimeMajor)
      (.app code.projector
        (VExpr.appN (.const view.constructorName levels)
          (params ++ alignment.fields))) :=
    ⟨_, hprojector.appDF hmajorEq⟩
  obtain ⟨captureType, hcaptures⟩ := alignment.captures
  have hiota := self.viewWF.projector_constructor_exact henv hΓ
    self.levelsWF self.levels_length self.params_length self.paramsSpine
    hcode hprojector alignment.fields_length alignment.field_get
    alignment.constructorType alignment.fieldsSpine hcaptures
  exact VEnv.IsDefEqU.trans henv hΓ hmajorCongr
    (VEnv.IsDefEqU.trans henv hΓ hiota alignment.field_eq.symm)

theorem TrProj.project_eq
    (self : VEnv.TrProj env U Γ view levels params idx major result) :
    VStructureView.project? view levels params idx major = some result := by
  obtain ⟨code, hcode, rfl, -⟩ := self.program
  simp [VStructureView.project?, hcode]

theorem TrProj.type_eq
    (self : VEnv.TrProj env U Γ view levels params idx major result) :
    ∃ code : VStructureView.ProjectionCode,
      VStructureView.projectionType? view levels params idx major =
        some (VExpr.app code.typeFn major) := by
  obtain ⟨code, hcode, _, -⟩ := self.program
  exact ⟨code, by simp [VStructureView.projectionType?, hcode]⟩

/-- A fixed checked view, universe/parameter instantiation, field index, and
major determine the projection result syntactically. -/
theorem TrProj.result_eq
    (self : VEnv.TrProj env U Γ view levels params idx major result)
    (other : VEnv.TrProj env U Γ view levels params idx major result') :
    result = result' :=
  Option.some.inj (self.project_eq.symm.trans other.project_eq)

/-- Projection evidence is stable when the registered environment is
extended without changing any existing constants or reduction rules. -/
theorem TrProj.mono {env env' : VEnv} (henv : env ≤ env')
    (self : VEnv.TrProj env U Γ view levels params idx major result) :
    VEnv.TrProj env' U Γ view levels params idx major result where
  viewWF := self.viewWF.mono henv
  levelsWF := self.levelsWF
  levels_length := self.levels_length
  params_length := self.params_length
  paramsSpine := self.paramsSpine.imp fun _ h => h.monoProjection henv
  majorType := self.majorType.mono henv
  program := self.program.imp fun _ ⟨hcode, hresult, htype⟩ =>
    ⟨hcode, hresult, htype.mono henv⟩

/-- Weakening acts pointwise on the explicit parameters, major, and computed
projection program. -/
theorem TrProj.weakN (henv : env.Ordered)
    (W : Ctx.LiftN n k Γ Γ')
    (self : VEnv.TrProj env U Γ view levels params idx major result) :
    VEnv.TrProj env U Γ' view levels
      (params.map fun param => param.liftN n k) idx
      (major.liftN n k) (result.liftN n k) := by
  refine {
    viewWF := self.viewWF
    levelsWF := self.levelsWF
    levels_length := self.levels_length
    params_length := by simpa using self.params_length
    paramsSpine := ?_
    majorType := by simpa using self.majorType.weakN henv W
    program := ?_ }
  · have hfamilyClosed : (view.familyType.instL levels).ClosedN 0 := by
      simpa using (henv.closedC self.viewWF.family).instL
    obtain ⟨resultLevel, hspine⟩ := self.paramsSpine
    refine ⟨resultLevel, ?_⟩
    have hspine' := hspine.weakN henv W
    rw [hfamilyClosed.liftN_eq (Nat.zero_le _)] at hspine'
    simpa [VExpr.liftN] using hspine'
  · obtain ⟨code, hcode, rfl, htype⟩ := self.program
    refine ⟨code.liftN n k, ?_, rfl, ?_⟩
    rw [← self.viewWF.projectionCodes_liftN henv levels params
      self.params_length n k]
    simp only [List.getElem?_map, hcode, Option.map_some]
    simpa [VStructureView.ProjectionCode.liftN, VExpr.liftN,
      VExpr.liftN_lift_projection] using htype.weakN henv W

/-- General context lifting, derived one inserted binder at a time from
`weakN`. -/
theorem TrProj.weak' (henv : env.Ordered)
    (W : Ctx.Lift' l Γ Γ')
    (self : VEnv.TrProj env U Γ view levels params idx major result) :
    VEnv.TrProj env U Γ' view levels
      (params.map fun param => param.lift' l) idx
      (major.lift' l) (result.lift' l) := by
  generalize hdepth : l.depth = depth
  induction depth generalizing l Γ' with
  | zero =>
      have hctx := W.depth_zero hdepth
      subst Γ'
      simpa [VExpr.lift'_depth_zero (l := l) hdepth] using self
  | succ depth ih =>
      obtain ⟨tail, k, rfl, rfl⟩ := Lift.depth_succ hdepth
      obtain ⟨Γ₁, W₁, W₂⟩ := W.of_cons_skip
      have h := (ih W₁ Lift.depth_consN).weakN henv W₂
      rw [Lift.consN_skip_eq]
      have hlift : ∀ e : VExpr,
          e.lift' ((tail.consN k).comp
              (Lift.refl.skip.consN k)) =
            (e.lift' (tail.consN k)).liftN 1 k := by
        intro e
        rw [VExpr.lift'_comp, ← Lift.skipN_one,
          VExpr.lift'_consN_skipN]
      have hparams :
          params.map (fun param => param.lift' ((tail.consN k).comp
              (Lift.refl.skip.consN k))) =
            (params.map fun param => param.lift' (tail.consN k)).map
              (fun param => param.liftN 1 k) := by
        rw [List.map_map]
        exact List.map_congr_left fun param _ => hlift param
      rw [hparams, hlift major, hlift result]
      exact h

/-- Substitution acts pointwise on the explicit parameters, major, and
computed projection program. -/
theorem TrProj.instN (henv : env.Ordered)
    (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ)
    (h₀ : env.HasType U Γ₀ e₀ A₀)
    (self : VEnv.TrProj env U Γ₁ view levels params idx major result) :
    VEnv.TrProj env U Γ view levels
      (params.map fun param => param.inst e₀ k) idx
      (major.inst e₀ k) (result.inst e₀ k) := by
  refine {
    viewWF := self.viewWF
    levelsWF := self.levelsWF
    levels_length := self.levels_length
    params_length := by simpa using self.params_length
    paramsSpine := ?_
    majorType := by simpa using self.majorType.instN henv W h₀
    program := ?_ }
  · have hfamilyClosed : (view.familyType.instL levels).ClosedN 0 := by
      simpa using (henv.closedC self.viewWF.family).instL
    obtain ⟨resultLevel, hspine⟩ := self.paramsSpine
    refine ⟨resultLevel, ?_⟩
    have hspine' := hspine.instNProjection henv W h₀
    rw [hfamilyClosed.instN_eq (Nat.zero_le _)] at hspine'
    simpa [VExpr.inst] using hspine'
  · obtain ⟨code, hcode, rfl, htype⟩ := self.program
    refine ⟨code.instN e₀ k, ?_, rfl, ?_⟩
    rw [← self.viewWF.projectionCodes_instN henv levels params
      self.params_length e₀ k]
    simp only [List.getElem?_map, hcode, Option.map_some]
    simpa [VStructureView.ProjectionCode.instN, VExpr.inst,
      ← VExpr.lift_instN_lo] using htype.instN henv W h₀

/-- Transport projection evidence to a definitionally equal context and a
new major already checked against the same instantiated structure type. -/
theorem TrProj.defeqDFC (henv : env.Ordered)
    (hΓ : env.IsDefEqCtx U Γ₀ Γ₁ Γ₂)
    (majorType' : env.HasType U Γ₂ major'
      (view.structureType levels params))
    (self : VEnv.TrProj env U Γ₁ view levels params idx major result) :
    ∃ result', VEnv.TrProj env U Γ₂ view levels params idx major' result' := by
  obtain ⟨code, hcode, -, htype⟩ := self.program
  refine ⟨.app code.projector major', {
    viewWF := self.viewWF
    levelsWF := self.levelsWF
    levels_length := self.levels_length
    params_length := self.params_length
    paramsSpine := self.paramsSpine.imp fun _ h => h.defeqDFC henv hΓ
    majorType := majorType'
    program := ⟨code, hcode, rfl,
      htype.defeqDFC henv hΓ⟩ }⟩

/-- Universe instantiation acts pointwise on the explicit structure
universes and parameters, and on the recursor program they determine. -/
theorem TrProj.instL {ls : List VLevel}
    (hls : ∀ level ∈ ls, level.WF U')
    (self : VEnv.TrProj env U Γ view levels params idx major result) :
    VEnv.TrProj env U' (Γ.map (VExpr.instL ls)) view
      (levels.map (VLevel.inst ls))
      (params.map (VExpr.instL ls)) idx
      (major.instL ls) (result.instL ls) := by
  refine {
    viewWF := self.viewWF
    levelsWF := ?_
    levels_length := by simpa using self.levels_length
    params_length := by simpa using self.params_length
    paramsSpine := ?_
    majorType := by simpa using self.majorType.instL hls
    program := ?_ }
  · intro level hlevel
    obtain ⟨sourceLevel, hsourceLevel, rfl⟩ := List.mem_map.1 hlevel
    exact VLevel.WF.inst hls
  · obtain ⟨resultLevel, hspine⟩ := self.paramsSpine
    refine ⟨resultLevel.inst ls, ?_⟩
    simpa [VExpr.instL, VExpr.instL_instL] using hspine.instL hls
  · obtain ⟨code, hcode, rfl, htype⟩ := self.program
    refine ⟨code.instL ls, ?_, ?_, ?_⟩
    · rw [← VStructureView.projectionCodes_instL]
      simp only [List.getElem?_map, hcode, Option.map_some]
    · rfl
    · simpa [VStructureView.ProjectionCode.instL, VExpr.instL,
        VExpr.instL_liftN] using htype.instL hls

/-- The registered-structure constant-head inversion boundary.

The four conclusions are the projection-specific eliminators supplied by
constant-head injectivity: a type assigned to a syntactically weakened major
recovers an instantiation below the inserted context; definitionally equal
majors recover the same registered view/instantiation strongly enough for the
generated projector programs to be definitionally equal; a runtime
constructor head recovers the registered constructor name; and that head plus
one selected argument is aligned with the registered constructor and field.
The last conclusion deliberately provides only typed alignment—the iota step
remains the proved `projector_constructor_exact` theorem.

Its eventual proof uses `IsDefEqU.weakN_iff` together with injectivity of
registered inductive heads.  The constructor conclusions additionally
require a genuine completed-inductive head certificate.  A translated axiom
with the same result type, or a definition alias which unfolds to a
constructor, is deliberately not enough.  Keeping the boundary in Theory
makes the temporary L4L-16/17 dependency explicit instead of leaving
Verify's structural laws as local holes. -/
structure RegisteredStructureHeadInversion (env : VEnv) : Prop where
  weak'_inv :
    ∀ {U : Nat} {Γ Γ' : List VExpr} {view : VStructureView}
      {levels : List VLevel} {params : List VExpr} {idx : Nat}
      {major result : VExpr} {lift : Lift},
      OnCtx Γ' (env.IsType U) →
      Ctx.Lift' lift Γ Γ' →
      env.TrProj U Γ' view levels params idx (major.lift' lift) result →
      ∃ params' result',
        env.TrProj U Γ view levels params' idx major result'
  unique :
    ∀ {U : Nat} {Γ₁ Γ₂ : List VExpr}
      {view₁ view₂ : VStructureView}
      {levels₁ levels₂ : List VLevel} {params₁ params₂ : List VExpr}
      {idx : Nat} {major₁ major₂ result₁ result₂ : VExpr},
      env.IsDefEqCtx U [] Γ₁ Γ₂ →
      env.TrProj U Γ₁ view₁ levels₁ params₁ idx major₁ result₁ →
      env.TrProj U Γ₂ view₂ levels₂ params₂ idx major₂ result₂ →
      env.IsDefEqU U Γ₁ major₁ major₂ →
      env.IsDefEqU U Γ₁ result₁ result₂
  constructor_name_inv :
    ∀ {U : Nat} {Γ : List VExpr} {view : VStructureView}
      {levels : List VLevel} {params : List VExpr} {idx : Nat}
      {major result runtimeMajor : VExpr}
      {constructorName : Name} {constructorLevels : List VLevel}
      {constructorArgs : List VExpr},
      OnCtx Γ (env.IsType U) →
      env.TrProj U Γ view levels params idx major result →
      env.ConstructorHead constructorName →
      runtimeMajor = VExpr.appN
        (.const constructorName constructorLevels) constructorArgs →
      env.IsDefEqU U Γ runtimeMajor major →
      constructorName = view.constructorName
  constructor_inv :
    ∀ {U : Nat} {Γ : List VExpr} {view : VStructureView}
      {levels : List VLevel} {params : List VExpr} {idx : Nat}
      {major result : VExpr} {code : VStructureView.ProjectionCode}
      {runtimeMajor runtimeField : VExpr}
      {constructorName : Name} {constructorLevels : List VLevel}
      {constructorArgs : List VExpr},
      OnCtx Γ (env.IsType U) →
      env.TrProj U Γ view levels params idx major result →
      env.ConstructorHead constructorName →
      (view.projectionCodes levels params)[idx]? = some code →
      runtimeMajor = VExpr.appN
        (.const constructorName constructorLevels) constructorArgs →
      constructorArgs[view.nparams + idx]? = some runtimeField →
      env.IsDefEqU U Γ runtimeMajor major →
      Nonempty (ProjectionConstructorAlignment env U Γ view levels params idx
        code constructorName runtimeMajor runtimeField)

set_option warn.sorry false in
/-- Public Tier-R registered-head inversion statement.  L4L-16/17 discharge
the underlying constant-head theorem; projection structural laws consume only
this stable interface and therefore shed `sorryAx` automatically when it is
proved. -/
theorem WF.registeredStructureHeadInversion
    (self : VEnv.WF env) : RegisteredStructureHeadInversion env := by
  sorry

/--
info: 'Lean4Lean.VEnv.WF.registeredStructureHeadInversion' depends on axioms: [propext, sorryAx, Quot.sound]
-/
#guard_msgs in
#print axioms WF.registeredStructureHeadInversion

/--
info: 'Lean4Lean.VEnv.TrProj.result_eq' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms TrProj.result_eq

/--
info: 'Lean4Lean.VEnv.TrProj.mono' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms TrProj.mono

end VEnv

end Lean4Lean
