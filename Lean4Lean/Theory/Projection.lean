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

/-- Universe instantiation distributes through a lambda telescope. -/
theorem VExpr.instL_lamN_projection (ls : List VLevel) :
    ∀ (As : List VExpr) (e : VExpr),
      (VExpr.lamN As e).instL ls =
        VExpr.lamN (As.map (VExpr.instL ls)) (e.instL ls)
  | [], _ => rfl
  | _ :: As, e => by
      simp only [VExpr.lamN, VExpr.instL, List.map_cons]
      rw [VExpr.instL_lamN_projection ls As e]

/-- Term lifting distributes through a lambda telescope, increasing the
cutoff across its binders. -/
theorem VExpr.liftN_lamN_projection (n : Nat) :
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

/-- Term instantiation distributes through a lambda telescope, increasing the
cutoff across its binders. -/
theorem VExpr.instN_lamN_projection (a : VExpr) :
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

@[simp] theorem VExpr.telN_forallN_length
    (binders : List VExpr) (body : VExpr) :
    VExpr.telN binders.length (VExpr.forallN binders body) = binders := by
  induction binders with
  | nil => rfl
  | cons binder binders ih =>
      simp [VExpr.telN, VExpr.forallN, ih]

@[simp] theorem VExpr.dropN_forallN_length
    (binders : List VExpr) (body : VExpr) :
    VExpr.dropN binders.length (VExpr.forallN binders body) = body := by
  induction binders with
  | nil => rfl
  | cons binder binders ih =>
      simp [VExpr.dropN, VExpr.forallN, ih]

/-- Splitting a raw telescope after at most `count` binders preserves its
total syntactic arity.  This remains true when `count` exceeds the available
telescope, because both `telN` and `dropN` stop at the same non-`forall`
cursor. -/
theorem VExpr.telN_length_add_ctorFields_dropN_length
    (count : Nat) (expression : VExpr) :
    (VExpr.telN count expression).length +
        (ctorFields (VExpr.dropN count expression)).length =
      (ctorFields expression).length := by
  induction count generalizing expression with
  | zero => simp [VExpr.telN, VExpr.dropN]
  | succ count ih =>
      cases expression <;> simp [VExpr.telN, VExpr.dropN, ctorFields]
      case forallE _ body =>
        have := ih body
        omega

@[simp] theorem VExpr.telN_liftN (count n k : Nat) (expression : VExpr) :
    VExpr.telN count (expression.liftN n k) =
      VExpr.liftTelN n (VExpr.telN count expression) k := by
  induction count generalizing expression k with
  | zero => rfl
  | succ count ih =>
      cases expression with
      | forallE domain body =>
          simp only [VExpr.liftN, VExpr.telN, VExpr.liftTelN]
          rw [ih (expression := body) (k := k + 1)]
      | _ => rfl

@[simp] theorem VExpr.dropN_liftN (count n k : Nat)
    (expression : VExpr) :
    VExpr.dropN count (expression.liftN n k) =
      (VExpr.dropN count expression).liftN n
        (k + (VExpr.telN count expression).length) := by
  induction count generalizing expression k with
  | zero => simp [VExpr.dropN, VExpr.telN]
  | succ count ih =>
      cases expression with
      | forallE domain body =>
          simp only [VExpr.liftN, VExpr.dropN, VExpr.telN,
            List.length_cons]
          rw [ih (expression := body) (k := k + 1)]
          congr 1 <;> omega
      | _ => simp [VExpr.telN, VExpr.dropN, VExpr.liftN]

@[simp] theorem VExpr.telN_instL (count : Nat) (expression : VExpr)
    (levels : List VLevel) :
    VExpr.telN count (expression.instL levels) =
      (VExpr.telN count expression).map (VExpr.instL levels) := by
  induction count generalizing expression with
  | zero => rfl
  | succ count ih =>
      cases expression with
      | forallE domain body =>
          simp only [VExpr.instL, VExpr.telN, List.map_cons]
          rw [ih (expression := body)]
      | _ => rfl

@[simp] theorem VExpr.dropN_instL (count : Nat) (expression : VExpr)
    (levels : List VLevel) :
    VExpr.dropN count (expression.instL levels) =
      (VExpr.dropN count expression).instL levels := by
  induction count generalizing expression with
  | zero => rfl
  | succ count ih =>
      cases expression with
      | forallE domain body =>
          simp only [VExpr.instL, VExpr.dropN]
          rw [ih (expression := body)]
      | _ => rfl

/-- Recovering the IH telescope from a known field/IH Pi shape commutes with
term lifting. -/
theorem VExpr.projectionIHTel_liftN
    (fields ihs : List VExpr) (body : VExpr) (n k : Nat) :
    VExpr.telN ihs.length
        (VExpr.dropN fields.length
          ((VExpr.forallN fields (VExpr.forallN ihs body)).liftN n k)) =
      VExpr.liftTelN n ihs (k + fields.length) := by
  rw [VExpr.liftN_forallN]
  have hfields : fields.length = (VExpr.liftTelN n fields k).length := by
    rw [VExpr.liftTelN_length]
  rw [hfields, VExpr.dropN_forallN_length]
  simp only [VExpr.liftTelN_length]
  rw [VExpr.liftN_forallN]
  have hihs : ihs.length =
      (VExpr.liftTelN n ihs (k + fields.length)).length := by
    rw [VExpr.liftTelN_length]
  rw [hihs, VExpr.telN_forallN_length]

/-- Recovering the IH telescope from a known field/IH Pi shape commutes with
term instantiation. -/
theorem VExpr.projectionIHTel_instN
    (fields ihs : List VExpr) (body a : VExpr) (k : Nat) :
    VExpr.telN ihs.length
        (VExpr.dropN fields.length
          ((VExpr.forallN fields (VExpr.forallN ihs body)).inst a k)) =
      VExpr.instTelN a ihs (k + fields.length) := by
  rw [VExpr.instN_forallN]
  have hfields : fields.length = (VExpr.instTelN a fields k).length := by
    rw [VExpr.instTelN_length]
  rw [hfields, VExpr.dropN_forallN_length]
  simp only [VExpr.instTelN_length]
  rw [VExpr.instN_forallN]
  have hihs : ihs.length =
      (VExpr.instTelN a ihs (k + fields.length)).length := by
    rw [VExpr.instTelN_length]
  rw [hihs, VExpr.telN_forallN_length]

/-- Close a dependent `forall` telescope from pointwise closure at each
binder depth and closure of the terminal body. -/
private theorem VExpr.forallN_closedN_of_getElem
    (binders : List VExpr) (body : VExpr) (k : Nat)
    (hbinders : ∀ (i : Nat) (binder : VExpr), binders[i]? = some binder →
      binder.ClosedN (k + i))
    (hbody : body.ClosedN (k + binders.length)) :
    (VExpr.forallN binders body).ClosedN k := by
  induction binders generalizing k with
  | nil => simpa [VExpr.forallN] using hbody
  | cons binder binders ih =>
      simp only [VExpr.forallN, VExpr.ClosedN]
      constructor
      · exact hbinders 0 binder (by simp)
      · apply ih (k := k + 1)
        · intro i binder' hbinder'
          have hlookup : (binder :: binders)[i + 1]? = some binder' := by
            simpa [Nat.add_comm] using hbinder'
          have h := hbinders (i + 1) binder' hlookup
          simpa only [Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using h
        · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm,
            Nat.add_left_comm] using hbody

/-- Pointwise closure of a telescope is preserved by telescope lifting. -/
private theorem VExpr.liftTelN_closedN_of_getElem
    (binders : List VExpr) (n cutoff base : Nat)
    (hbinders : ∀ (i : Nat) (binder : VExpr),
      binders[i]? = some binder →
      binder.ClosedN (base + i)) :
    ∀ (i : Nat) (binder : VExpr),
      (VExpr.liftTelN n binders cutoff)[i]? = some binder →
      binder.ClosedN (base + n + i) := by
  intro i binder hbinder
  rw [VExpr.liftTelN_getElem?] at hbinder
  obtain ⟨original, horiginal, rfl⟩ :=
    Option.map_eq_some_iff.1 hbinder
  have hclosed := (hbinders i original horiginal).liftN
    (n := n) (j := cutoff + i)
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hclosed

/-- The generated IH for one recursive argument is closed over parameters,
the motive, all constructor fields, and the preceding IH binders. -/
private theorem VInductDecl.RecArg.minorIH_closedN
    (recursive : RecArg) (nparams fields preceding : Nat)
    (hfield : recursive.fieldIndex < fields)
    (hbinders : ∀ (i : Nat) (binder : VExpr),
      recursive.binders[i]? = some binder →
      binder.ClosedN (nparams + recursive.fieldIndex + i))
    (hindices : ∀ (index : VExpr), index ∈ recursive.indices →
      index.ClosedN
        (nparams + recursive.fieldIndex + recursive.binders.length)) :
    (recursive.minorIH fields preceding).ClosedN
      (nparams + 1 + fields + preceding) := by
  unfold RecArg.minorIH
  apply VExpr.forallN_closedN_of_getElem
  · intro i binder hbinder
    have hfirst := VExpr.liftTelN_closedN_of_getElem
      recursive.binders 1 recursive.fieldIndex
      (nparams + recursive.fieldIndex) hbinders
    have hsecond := VExpr.liftTelN_closedN_of_getElem
      (VExpr.liftTelN 1 recursive.binders recursive.fieldIndex)
      (fields - recursive.fieldIndex + preceding) 0
      (nparams + recursive.fieldIndex + 1) hfirst i binder hbinder
    have hfield' : recursive.fieldIndex ≤ fields := Nat.le_of_lt hfield
    have hdepth :
        nparams + recursive.fieldIndex + 1 +
            (fields - recursive.fieldIndex + preceding) + i =
          nparams + 1 + fields + preceding + i := by
      omega
    rw [hdepth] at hsecond
    exact hsecond
  · have hminorBindersLength :
        (recursive.minorBinders fields preceding).length =
          recursive.binders.length := by
      simp [RecArg.minorBinders, VExpr.liftTelN_length]
    rw [hminorBindersLength]
    apply VExpr.ClosedN.appN
    · change fields + preceding + recursive.binders.length <
          nparams + 1 + fields + preceding + recursive.binders.length
      omega
    · intro argument hargument
      rcases List.mem_append.1 hargument with hindex | hfieldApp
      · obtain ⟨index, hindexOriginal, hindexEq⟩ :=
          List.mem_map.1 hindex
        subst argument
        have hclosed := hindices index hindexOriginal
        have hfirst := hclosed.liftN (n := 1)
          (j := recursive.fieldIndex + recursive.binders.length)
        have hsecond := hfirst.liftN
          (n := fields - recursive.fieldIndex + preceding)
          (j := recursive.binders.length)
        have hfield' : recursive.fieldIndex ≤ fields := Nat.le_of_lt hfield
        have hdepth :
            nparams + recursive.fieldIndex + recursive.binders.length + 1 +
                (fields - recursive.fieldIndex + preceding) =
              nparams + 1 + fields + preceding +
                recursive.binders.length := by
          omega
        rw [hdepth] at hsecond
        exact hsecond
      · have hsingleton := List.mem_singleton.1 hfieldApp
        subst argument
        apply VExpr.ClosedN.appN
        · change fields - 1 - recursive.fieldIndex + preceding +
              recursive.binders.length <
            nparams + 1 + fields + preceding + recursive.binders.length
          omega
        · exact fun argument hargument =>
            bvarRevRange_closedN recursive.binders.length 0
              (nparams + 1 + fields + preceding +
                recursive.binders.length) (by omega) argument hargument

@[simp] theorem VExpr.lamN_append
    (left right : List VExpr) (body : VExpr) :
    VExpr.lamN (left ++ right) body =
      VExpr.lamN left (VExpr.lamN right body) := by
  induction left with
  | nil => rfl
  | cons binder left ih =>
      simp [VExpr.lamN, ih]

/-- A selected field remains a valid minor body after weakening beneath an
arbitrary well-formed induction-hypothesis telescope. -/
theorem VEnv.HasType.selectFieldMinor_of_weak
    {env : VEnv} (henv : env.Ordered) {U : Nat} {Γ : List VExpr}
    {fields ihs : List VExpr} {i : Nat} {result : VExpr}
    (hfields : env.OnTel U Γ fields)
    (hihs : env.OnTel U (fields.reverse ++ Γ) ihs)
    (hi : i < fields.length)
    (hbody : env.HasType U (fields.reverse ++ Γ)
      (.bvar (fields.length - 1 - i)) result) :
    env.HasType U Γ (VExpr.selectFieldMinor fields ihs i)
      (VExpr.forallN fields
        (VExpr.forallN ihs (result.liftN ihs.length))) := by
  have hbodyWeak := hbody.weakN henv
    (Ctx.LiftN.zero (Γ := fields.reverse ++ Γ) ihs.reverse)
  have hbodyWeak' : env.HasType U
      (ihs.reverse ++ (fields.reverse ++ Γ))
      (.bvar (ihs.length + fields.length - 1 - i))
      (result.liftN ihs.length) := by
    simp only [List.length_reverse, VExpr.liftN,
      liftVar_le (Nat.zero_le _)] at hbodyWeak
    rw [show ihs.length + (fields.length - 1 - i) =
      ihs.length + fields.length - 1 - i by omega] at hbodyWeak
    exact hbodyWeak
  exact VEnv.HasType.lamN hfields (VEnv.HasType.lamN hihs hbodyWeak')

/-- Lifting an expression already opened by one binder commutes with an
ambient lift whose cutoff is shifted across that binder. -/
theorem VExpr.liftN_lift_projection (e : VExpr) (n k : Nat) :
    e.lift.liftN n (k + 1) = (e.liftN n k).lift :=
  (VExpr.lift_liftN' e k).symm

/-- General cutoff form of `liftN_lift_projection`. -/
theorem VExpr.liftN_liftAt_projection
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

/-- Instantiating an expression already opened at an arbitrary cutoff
commutes with that opening lift. -/
theorem VExpr.instN_liftAt_projection
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

/-- Instantiating the parameter range which sits above a field telescope
produces those parameters lifted across the fields. -/
theorem VExpr.map_instRevAt_bvarRevRange
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

/-- Reverse instantiation distributes through an application spine. -/
theorem VExpr.instRevAt_appN_projection
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
    (params : List VExpr) (m r : Nat) (typeFn : VExpr) :
    ((VExpr.appN (.bvar (r + m))
          [VExpr.appN (.const constructorName levels)
            (VExpr.bvarRevRange (r + m + 1) params.length ++
              VExpr.bvarRevRange r m)]).instRevAt params
        (r + m + 1)).inst typeFn (r + m) =
      .app (typeFn.liftN (r + m))
        (VExpr.appN (.const constructorName levels)
          (params.map (VExpr.liftN (r + m)) ++
            VExpr.bvarRevRange r m)) := by
  have hmotiveR : (VExpr.bvar (r + m)).instRevAt params
      (r + m + 1) = .bvar (r + m) :=
    VExpr.instRevAt_closedN params (by exact Nat.lt_succ_self _)
  have hconstR : (VExpr.const constructorName levels).instRevAt
      params (r + m + 1) = .const constructorName levels :=
    VExpr.instRevAt_closedN params (by trivial)
  have hfieldsR := VExpr.map_instRevAt_closedN params
    (VExpr.bvarRevRange r m) (r + m + 1)
    (bvarRevRange_closedN m r (r + m + 1) (by omega))
  have hmotiveI : (VExpr.bvar (r + m)).inst typeFn (r + m) =
      typeFn.liftN (r + m) := by simp [VExpr.inst, VExpr.instVar]
  have hconstI : (VExpr.const constructorName levels).inst typeFn (r + m) =
      .const constructorName levels := by rfl
  have hparamsI := VExpr.map_instN_liftN_top params typeFn (r + m)
  have hfieldsI := VExpr.map_instN_closedN typeFn
    (VExpr.bvarRevRange r m) (r + m)
    (bvarRevRange_closedN m r (r + m) (by omega))
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

private theorem VExpr.liftN_instRevAt_inst_of_closedN_at
    (e typeFn : VExpr) (params : List VExpr) (n k i : Nat)
    (hclosed : e.ClosedN (i + params.length + 1)) :
    (((e.instRevAt params (i + 1)).inst typeFn i).liftN n (k + i)) =
      (e.instRevAt (params.map fun param => param.liftN n k) (i + 1)).inst
        (typeFn.liftN n k) i := by
  rw [VExpr.liftN_instN_hi]
  rw [show k + i + 1 = k + (i + 1) by omega,
    VExpr.liftN_instRevAt]
  rw [hclosed.liftN_eq (by omega)]

private theorem VExpr.instN_instRevAt_inst_of_closedN_at
    (e typeFn a : VExpr) (params : List VExpr) (k i : Nat)
    (hclosed : e.ClosedN (i + params.length + 1)) :
    ((e.instRevAt params (i + 1)).inst typeFn i).inst a (k + i) =
      (e.instRevAt (params.map fun param => param.inst a k) (i + 1)).inst
        (typeFn.inst a k) i := by
  rw [VExpr.inst_inst_hi]
  rw [show k + i + 1 = k + (i + 1) by omega,
    VExpr.instN_instRevAt]
  rw [hclosed.instN_eq (by omega)]

/-- Specializing a generated IH telescope commutes with weakening of its
external parameter and motive arguments. -/
private theorem VExpr.specializeProjectionIHs_liftN
    (rawIHs params : List VExpr) (typeFn : VExpr) (m n k : Nat)
    (hclosed : ∀ (i : Nat) (ih : VExpr), rawIHs[i]? = some ih →
      ih.ClosedN (m + i + params.length + 1)) :
    VExpr.liftTelN n
        (VExpr.instTelN typeFn
          ((rawIHs.zipIdx (m + 1)).map fun entry =>
            entry.1.instRevAt params entry.2) m)
        (k + m) =
      VExpr.instTelN (typeFn.liftN n k)
        ((rawIHs.zipIdx (m + 1)).map fun entry =>
          entry.1.instRevAt
            (params.map fun param => param.liftN n k) entry.2) m := by
  induction rawIHs generalizing m with
  | nil => rfl
  | cons ih rawIHs induction =>
      simp only [List.zipIdx, List.map_cons, VExpr.instTelN,
        VExpr.liftTelN]
      congr 1
      · apply VExpr.liftN_instRevAt_inst_of_closedN_at
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hclosed 0 ih (by simp)
      · apply induction
        intro i ih' hih'
        have hlookup : (ih :: rawIHs)[i + 1]? = some ih' := by
          simpa [Nat.add_comm] using hih'
        have h := hclosed (i + 1) ih' hlookup
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- Specializing a generated IH telescope commutes with term substitution of
its external parameter and motive arguments. -/
private theorem VExpr.specializeProjectionIHs_instN
    (rawIHs params : List VExpr) (typeFn argument : VExpr) (m k : Nat)
    (hclosed : ∀ (i : Nat) (ih : VExpr), rawIHs[i]? = some ih →
      ih.ClosedN (m + i + params.length + 1)) :
    VExpr.instTelN argument
        (VExpr.instTelN typeFn
          ((rawIHs.zipIdx (m + 1)).map fun entry =>
            entry.1.instRevAt params entry.2) m)
        (k + m) =
      VExpr.instTelN (typeFn.inst argument k)
        ((rawIHs.zipIdx (m + 1)).map fun entry =>
          entry.1.instRevAt
            (params.map fun param => param.inst argument k) entry.2) m := by
  induction rawIHs generalizing m with
  | nil => rfl
  | cons ih rawIHs induction =>
      simp only [List.zipIdx, List.map_cons, VExpr.instTelN]
      congr 1
      · apply VExpr.instN_instRevAt_inst_of_closedN_at
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          hclosed 0 ih (by simp)
      · apply induction
        intro i ih' hih'
        have hlookup : (ih :: rawIHs)[i + 1]? = some ih' := by
          simpa [Nat.add_comm] using hih'
        have h := hclosed (i + 1) ih' hlookup
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

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

/-- Transport a sort-labelled telescope across definitionally equal base
contexts without changing either its binders or retained universe labels. -/
theorem VEnv.OnSortTel.defeqDFC {env : VEnv} (henv : env.Ordered)
    {U : Nat} {Γ₀ Γ₁ Γ₂ : List VExpr}
    (hΓ : env.IsDefEqCtx U Γ₀ Γ₁ Γ₂) :
    ∀ {As us}, env.OnSortTel U Γ₁ As us →
      env.OnSortTel U Γ₂ As us
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons hA hT =>
      .cons (hA.defeqDFC henv hΓ)
        (VEnv.OnSortTel.defeqDFC henv (.succ hΓ hA) hT)

/-- A raw/view telescope equality transfers the validator-selected universe
labels from the view binders back to the exact raw binders. -/
theorem VEnv.TelDefEq.raw_onSortTel {env : VEnv} (henv : env.WF)
    {U : Nat} {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ {raw view sorts}, env.TelDefEq U Γ raw view →
      env.OnSortTel U Γ view sorts →
      env.OnSortTel U Γ raw sorts
  | [], [], [], _, .nil => .nil
  | rawHead :: rawTail, viewHead :: viewTail, sort :: sorts,
      ⟨⟨_, hhead⟩, htail⟩,
      .cons hview hviews => by
      have sortEq := hhead.hasType.2.uniqU henv hΓ hview
      have hraw := hhead.hasType.1.defeqU_r henv hΓ sortEq
      have hctx : env.IsDefEqCtx U Γ (rawHead :: Γ) (viewHead :: Γ) :=
        .succ .zero hhead
      have hviews' := hviews.defeqDFC henv.ordered
        (hctx.symm henv.ordered)
      have hrawCtx : OnCtx (rawHead :: Γ) (env.IsType U) :=
        ⟨hΓ, ⟨sort, hraw⟩⟩
      exact .cons hraw
        (VEnv.TelDefEq.raw_onSortTel henv hrawCtx
          htail hviews')

/-- Forget the retained sort labels, preserving the underlying telescope
well-formedness judgment. -/
theorem VEnv.OnSortTel.toOnTel {env : VEnv} :
    ∀ {U : Nat} {Γ As : List VExpr} {us : List VLevel},
      env.OnSortTel U Γ As us → env.OnTel U Γ As
  | _, _, [], [], .nil => trivial
  | _, _, _ :: _, _ :: _, .cons hA hT =>
      ⟨⟨_, hA⟩, VEnv.OnSortTel.toOnTel hT⟩

/-- Retain one exact inferred sort for every entry of an ordinary
well-formed telescope.  This finite choice is structural: the sort witness
is already carried by each `IsType` node. -/
theorem VEnv.OnTel.exists_onSortTel {env : VEnv} :
    ∀ {U : Nat} {Γ As : List VExpr}, env.OnTel U Γ As →
      ∃ us, env.OnSortTel U Γ As us
  | _, _, [], _ => ⟨[], .nil⟩
  | _, Γ, A :: As, ⟨⟨u, hA⟩, hAs⟩ => by
      obtain ⟨us, hsorts⟩ :=
        VEnv.OnTel.exists_onSortTel (Γ := A :: Γ) hAs
      exact ⟨u :: us, .cons hA hsorts⟩

/-- A sort-labelled telescope carries exactly one sort for every binder. -/
theorem VEnv.OnSortTel.length_eq {env : VEnv} :
    ∀ {U : Nat} {Γ As : List VExpr} {us : List VLevel},
      env.OnSortTel U Γ As us → As.length = us.length
  | _, _, [], [], .nil => rfl
  | _, _, _ :: _, _ :: _, .cons _ tail => by
      simp only [List.length_cons, Nat.succ.injEq]
      exact VEnv.OnSortTel.length_eq tail

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
theorem VEnv.OnSortTel.next_of_spine {env : VEnv}
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

/-- Instantiate a dependent sort telescope by an exact parameter spine. -/
theorem VEnv.OnSortTel.instRevParams {env : VEnv}
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

/-- Instantiate a dependent type telescope by an exact parameter spine. -/
theorem VEnv.OnTel.instRevParams {env : VEnv}
    (henv : env.Ordered) {U : Nat} :
    ∀ {Γ params args fields tail cursor},
      env.SpineWF U Γ (VExpr.forallN params tail) args cursor →
      args.length = params.length →
      env.OnTel U (params.reverse ++ Γ) fields →
      env.OnTel U Γ
        (fields.zipIdx.map fun (field, i) =>
          VExpr.instRevAt field args i)
  | _, [], [], fields, _, _, _, _, hfields => by
      simpa [VExpr.instRevAt] using hfields
  | _, [], _ :: _, _, _, _, _, hlen, _ => by simp at hlen
  | Γ, param :: params, arg :: args, fields, tail, cursor,
      .cons harg hrest, hlen, hfields => by
      have hparams : args.length = params.length := by simpa using hlen
      have W := Ctx.InstN.consTel (Γ₀ := Γ) (e₀ := arg)
        (A₀ := param) params (.zero)
      have hfields' : env.OnTel U
          ((VExpr.instTelN arg params 0).reverse ++ Γ)
          (VExpr.instTelN arg fields params.length) := by
        apply VEnv.OnTel.instN henv harg W
        simpa [List.append_assoc] using hfields
      have hrest' : env.SpineWF U Γ
          (VExpr.forallN (VExpr.instTelN arg params 0)
            (tail.inst arg params.length)) args cursor := by
        simpa [VExpr.instN_forallN] using hrest
      have hout := VEnv.OnTel.instRevParams henv hrest'
        (by simpa [VExpr.instTelN_length] using hparams) hfields'
      rw [← hparams, VExpr.instRevAt_instTelN_cons] at hout
      exact hout

/-- A prefix of a well-formed telescope is well formed in the same base
context. -/
private theorem VEnv.OnTel.take {env : VEnv} {U : Nat} :
    ∀ {As Γ}, env.OnTel U Γ As → ∀ count,
      env.OnTel U Γ (As.take count)
  | [], _, h, count => by simpa using h
  | _ :: _, _, _, 0 => trivial
  | _ :: _, _, ⟨hA, hAs⟩, count + 1 =>
      ⟨hA, VEnv.OnTel.take hAs count⟩

/-- A binder in a well-formed telescope is closed at the size of its base
context plus its telescope position. -/
theorem VEnv.OnTel.closedAt {env : VEnv} {U : Nat}
    (henv : env.Ordered) :
    ∀ {As Γ}, env.OnTel U Γ As → CtxClosed Γ →
      ∀ {i : Nat} {binder : VExpr}, As[i]? = some binder →
        binder.ClosedN (Γ.length + i)
  | [], _, _, _, _, _, h => by simp at h
  | _ :: _, Γ, ⟨hA, _⟩, hΓ, 0, _, h => by
      simp only [List.getElem?_cons_zero] at h
      cases h
      obtain ⟨_, hA⟩ := hA
      simpa using hA.closedN henv hΓ
  | A :: As, Γ, ⟨hA, hAs⟩, hΓ, i + 1, binder, h => by
      simp only [List.getElem?_cons_succ] at h
      obtain ⟨_, hA⟩ := hA
      have hclosed : A.ClosedN Γ.length := hA.closedN henv hΓ
      have hout := VEnv.OnTel.closedAt henv hAs ⟨hΓ, hclosed⟩ h
      have hdepth : (A :: Γ).length + i = Γ.length + (i + 1) := by
        simp
        omega
      rw [hdepth] at hout
      exact hout

/-- Every argument retained by a well-formed spine has a typing derivation
in the spine's ambient context.  This local form is used before the public
projection-consumer theorem of the same shape below. -/
private theorem VEnv.SpineWF.projectionArg_hasType
    {env : VEnv} {U : Nat} {Γ : List VExpr} :
    ∀ {A B : VExpr} {args : List VExpr},
      env.SpineWF U Γ A args B →
      ∀ {arg : VExpr}, arg ∈ args → ∃ T, env.HasType U Γ arg T
  | _, _, _ :: _, .cons harg _, _, .head _ => ⟨_, harg⟩
  | _, _, _ :: _, .cons _ hrest, _, .tail _ hmem =>
      projectionArg_hasType hrest hmem

/-- The semantic certificate for one retained recursive argument is enough
to close its generated induction-hypothesis syntax. -/
private theorem VInductDecl.GenerationEnv.recArgMinorIH_closedN
    {source : VInductDecl} {gen : GenerationChecked source}
    {env : VEnv} (S : GenerationEnv gen env)
    {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) {recursive : RecArg}
    (hrecursive : recursive ∈
      ctor.recArgsR source.uvars gen.elimination) (preceding : Nat) :
    (recursive.minorIH
      (ctor.fieldsR source.uvars source.nparams
        gen.elimination).length preceding).ClosedN
      (source.nparams + 1 +
        (ctor.fieldsR source.uvars source.nparams
          gen.elimination).length + preceding) := by
  obtain ⟨recursive₀, hrecursive₀, rfl⟩ :=
    NormalizedCtor.recArgsR_mem hrecursive
  let levels := gen.sourceLevels
  let recursive := recursive₀.instL levels
  let fields := ctor.fieldsR source.uvars source.nparams gen.elimination
  let fieldCount := fields.length
  let fieldIndex := recursive₀.fieldIndex
  have hfield : fieldIndex < fieldCount := by
    have hview := S.viewRecArg_lt hctor hrecursive₀
    have hfields := (gen.shape.2.2.2.2.2 ctor hctor).2.2.2
    simp only [fieldIndex, fieldCount, fields,
      NormalizedCtor.fieldsR_length]
    omega
  have hsem := S.rawRecArg_WF hctor hrecursive₀
  have htel₀ := hsem.1.instL
    (U' := gen.recUvars) gen.sourceLevels_wf
  have hspine₀ := hsem.2.instL
    (U' := gen.recUvars) gen.sourceLevels_wf
  have htelChecked : env.OnTel gen.recUvars
      ((fields.take fieldIndex).reverse ++
        (gen.block.checked.params.map
          (VExpr.instL gen.sourceLevels)).reverse)
      recursive.binders := by
    simpa [NormalizedCtor.fieldsR, GenerationChecked.paramsTel,
      List.map_append, List.map_reverse, List.map_take,
      recursive, fields, fieldIndex, levels, RecArg.instL] using htel₀
  have hspineChecked : env.SpineWF gen.recUvars
      (recursive.binders.reverse ++
        ((fields.take fieldIndex).reverse ++
          (gen.block.checked.params.map
            (VExpr.instL gen.sourceLevels)).reverse))
      (VExpr.instL gen.sourceLevels
        (VExpr.forallN
          (VExpr.liftTelN
            (recursive₀.fieldIndex + recursive₀.binders.length)
            gen.block.checked.indices 0)
          (.sort gen.block.checked.resultLevel)))
      recursive.indices
      (VExpr.instL gen.sourceLevels
        (.sort gen.block.checked.resultLevel)) := by
    simpa [NormalizedCtor.fieldsR, GenerationChecked.paramsTel,
      List.map_append, List.map_reverse, List.map_take,
      recursive, fields, fieldIndex, levels, RecArg.instL] using hspine₀
  have hprefix := S.generationFieldPrefix_ctx_rec hctor fieldIndex
  have htel : env.OnTel gen.recUvars
      ((fields.take fieldIndex).reverse ++ gen.paramsTel.reverse)
      recursive.binders :=
    htelChecked.defeqDFC S.ord (hprefix.symm S.ord)
  have hfullDefEq := htel.extendDefEqCtx hprefix
  have hspine :=
    hspineChecked.defeqDFC S.ord (hfullDefEq.symm S.ord)
  have hparamsCtx : OnCtx gen.paramsTel.reverse
      (env.IsType gen.recUvars) := by
    simpa using VEnv.OnTel.toOnCtx S.paramsTel_onTel (by trivial)
  have hfieldsPrefix :=
    VEnv.OnTel.take (S.generationFields_onTel_rec hctor) fieldIndex
  have hbaseCtx : OnCtx
      ((fields.take fieldIndex).reverse ++ gen.paramsTel.reverse)
      (env.IsType gen.recUvars) :=
    VEnv.OnTel.toOnCtx hfieldsPrefix hparamsCtx
  have hbaseClosed := VEnv.CtxWF.closed S.ord hbaseCtx
  have hfullCtx : OnCtx
      (recursive.binders.reverse ++
        ((fields.take fieldIndex).reverse ++ gen.paramsTel.reverse))
      (env.IsType gen.recUvars) :=
    VEnv.OnTel.toOnCtx htel hbaseCtx
  have hfullClosed := VEnv.CtxWF.closed S.ord hfullCtx
  have hbaseLength :
      ((fields.take fieldIndex).reverse ++ gen.paramsTel.reverse).length =
        source.nparams + fieldIndex := by
    simp only [List.length_append, List.length_reverse, List.length_take,
      GenerationChecked.paramsTel, List.length_map]
    rw [S.generationParams_length]
    omega
  have hfullLength :
      (recursive.binders.reverse ++
        ((fields.take fieldIndex).reverse ++ gen.paramsTel.reverse)).length =
        source.nparams + fieldIndex + recursive.binders.length := by
    simp only [List.length_append, List.length_reverse, hbaseLength]
    omega
  apply RecArg.minorIH_closedN recursive source.nparams fieldCount preceding
  · simpa [recursive, fieldCount, fieldIndex, RecArg.instL] using hfield
  · intro index binder hbinder
    have hclosed :=
      VEnv.OnTel.closedAt S.ord htel hbaseClosed hbinder
    rw [hbaseLength] at hclosed
    simpa [recursive, fieldIndex, RecArg.instL] using hclosed
  · intro index hindex
    obtain ⟨_, hindexType⟩ :=
      VEnv.SpineWF.projectionArg_hasType hspine hindex
    have hclosed := hindexType.closedN S.ord hfullClosed
    rw [hfullLength] at hclosed
    simpa [recursive, fieldIndex, RecArg.instL] using hclosed

/-- Pointwise closure of the generated IH list follows by accumulating the
number of preceding IH binders. -/
private theorem VInductDecl.GenerationEnv.ihsFromRecArgs_closedN
    {source : VInductDecl} {gen : GenerationChecked source}
    {env : VEnv} (S : GenerationEnv gen env)
    {ctor : NormalizedCtor}
    (hctor : ctor ∈ gen.block.ctorPairs) :
    ∀ (recursive : List RecArg),
      (∀ argument ∈ recursive,
        argument ∈ ctor.recArgsR source.uvars gen.elimination) →
      ∀ (preceding index : Nat) (ih : VExpr),
        (VInductDecl.ihsFromRecArgs
          (ctor.fieldsR source.uvars source.nparams
            gen.elimination).length recursive preceding)[index]? = some ih →
        ih.ClosedN
          (source.nparams + 1 +
            (ctor.fieldsR source.uvars source.nparams
              gen.elimination).length + preceding + index)
  | [], _, _, _, _, hlookup => by
      simp [VInductDecl.ihsFromRecArgs] at hlookup
  | argument :: recursive, hsub, preceding, 0, ih, hlookup => by
      simp only [VInductDecl.ihsFromRecArgs,
        List.getElem?_cons_zero] at hlookup
      cases hlookup
      exact S.recArgMinorIH_closedN hctor
        (hsub argument (.head _)) preceding
  | argument :: recursive, hsub, preceding, index + 1, ih, hlookup => by
      simp only [VInductDecl.ihsFromRecArgs,
        List.getElem?_cons_succ] at hlookup
      have hclosed := S.ihsFromRecArgs_closedN hctor recursive
        (fun recursive hrecursive => hsub recursive (.tail _ hrecursive))
        (preceding + 1) index ih hlookup
      simpa only [Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hclosed

/-- A binder in a sort-annotated telescope is closed at the size of its base
context plus its telescope position. -/
theorem VEnv.OnSortTel.closedAt {env : VEnv} {U : Nat}
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

/-- A well-formed telescope over a closed base context is unchanged by an
ambient lift inserted immediately below that context. -/
theorem VEnv.OnTel.liftTelN_eq {env : VEnv} {U : Nat}
    (henv : env.Ordered) :
    ∀ {As Γ}, env.OnTel U Γ As → CtxClosed Γ → ∀ n,
      VExpr.liftTelN n As Γ.length = As
  | [], _, _, _, _ => rfl
  | A :: As, Γ, ⟨hA, hAs⟩, hΓ, n => by
      obtain ⟨_, hA⟩ := hA
      have hclosed : A.ClosedN Γ.length := hA.closedN henv hΓ
      simp only [VExpr.liftTelN, hclosed.liftN_eq (Nat.le_refl _)]
      simpa using VEnv.OnTel.liftTelN_eq henv hAs ⟨hΓ, hclosed⟩ n

/-- Sort-annotated form of `VEnv.OnTel.liftTelN_eq`. -/
theorem VEnv.OnSortTel.liftTelN_eq {env : VEnv} {U : Nat}
    (henv : env.Ordered) :
    ∀ {As us Γ}, env.OnSortTel U Γ As us → CtxClosed Γ → ∀ n,
      VExpr.liftTelN n As Γ.length = As
  | [], [], _, .nil, _, _ => rfl
  | A :: As, _ :: us, Γ, .cons hA hAs, hΓ, n => by
      have hclosed : A.ClosedN Γ.length := hA.closedN henv hΓ
      simp only [VExpr.liftTelN, hclosed.liftN_eq (Nat.le_refl _)]
      simpa using VEnv.OnSortTel.liftTelN_eq henv hAs ⟨hΓ, hclosed⟩ n

/-- The checked, generated description of a one-constructor unindexed
structure-shaped inductive family.

`generation` supplies the exact family, constructor, recursor, and iota rule
artifacts.  The shape fields restrict that general one-family artifact to the
kernel class on which generated projection programs are meaningful: no
indices and exactly one constructor. Recursive constructor arguments are
retained, together with their generated induction-hypothesis binders.
`fieldSorts` records the motive universe required by each projection; `WF`
below ties every entry to the corresponding dependent constructor field type. -/
structure VStructureView where
  source : VInductDecl
  generation : source.GenerationChecked
  constructor : NormalizedCtor
  constructor_eq : generation.block.ctorPairs = [constructor]
  raw_indices_eq : generation.block.rawIndices = []
  checked_indices_eq : generation.block.checked.indices = []
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

abbrev rawFamilyType (view : VStructureView) : VExpr :=
  view.generation.block.sourceType.type

/-- Projection-facing family type.  The registered constant retains
`rawFamilyType`; checked generation proves that its terminal result is
definitionally equal to this validated sort.  Keeping the raw parameter
telescope makes application spines exact without requiring the source's
terminal syntax itself to be a `sort`. -/
def familyType (view : VStructureView) : VExpr :=
  VExpr.forallN view.generation.block.rawParams
    (.sort view.generation.block.checked.resultLevel)

def constructorParams (view : VStructureView) : List VExpr :=
  VExpr.telN view.nparams view.constructor.raw.type

def fields (view : VStructureView) : List VExpr :=
  view.constructor.rawFields view.nparams

/-- A structure view has no family indices, so its declared parameter count
is determined by the complete registered raw family telescope. -/
theorem nparams_eq_rawFamilyArity (view : VStructureView) :
    view.nparams =
      (ctorFields view.rawFamilyType).length := by
  have paramsLength :
      (VExpr.telN view.nparams view.rawFamilyType).length = view.nparams := by
    simpa only [rawFamilyType, NormalizedChecked.rawParams] using
      view.generation.shape.1
  have noIndices :
      ctorFields (VExpr.dropN view.nparams view.rawFamilyType) = [] := by
    simpa only [rawFamilyType, NormalizedChecked.rawIndices] using
      view.raw_indices_eq
  have split := VExpr.telN_length_add_ctorFields_dropN_length
    view.nparams view.rawFamilyType
  rw [paramsLength, noIndices, List.length_nil, Nat.add_zero] at split
  exact split

/-- The projection-facing sort-normalized family type has the same exact raw
parameter arity as the registered declaration. -/
theorem nparams_eq_familyArity (view : VStructureView) :
    view.nparams = (ctorFields view.familyType).length := by
  have fields_eq :
      ctorFields view.familyType = view.generation.block.rawParams := by
    change ctorFields (VExpr.forallN view.generation.block.rawParams
      (.sort view.generation.block.checked.resultLevel)) = _
    induction view.generation.block.rawParams with
    | nil => rfl
    | cons _ params ih => simp only [VExpr.forallN, ctorFields, ih]
  rw [fields_eq, view.generation.shape.1]

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

/-- Specializing a closed dependent telescope commutes with lifting its
parameter arguments.  This helper is shared by singleton and block-backed
structure views. -/
theorem specializedFieldsAux_liftN
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

/-- Specializing a closed dependent telescope commutes with instantiating its
parameter arguments.  This helper is shared by singleton and block-backed
structure views. -/
theorem specializedFieldsAux_instN
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

/-- Instantiate an outermost-first term telescope in every expression
payload of one projection program.  The field sort is universe metadata and
is therefore unaffected. -/
def ProjectionCode.instRevAt (code : ProjectionCode)
    (args : List VExpr) (k : Nat) : ProjectionCode where
  fieldSort := code.fieldSort
  typeFn := code.typeFn.instRevAt args k
  minor := code.minor.instRevAt args k
  projector := code.projector.instRevAt args k

@[simp] theorem ProjectionCode.instRevAt_fieldSort
    (code : ProjectionCode) (args : List VExpr) (k : Nat) :
    (code.instRevAt args k).fieldSort = code.fieldSort :=
  rfl

@[simp] theorem ProjectionCode.instRevAt_nil
    (code : ProjectionCode) (k : Nat) :
    code.instRevAt [] k = code := by
  cases code
  rfl

@[simp] theorem ProjectionCode.instRevAt_cons
    (code : ProjectionCode) (arg : VExpr) (args : List VExpr)
    (k : Nat) :
    code.instRevAt (arg :: args) k =
      (code.instN arg (k + args.length)).instRevAt args k := by
  cases code
  rfl

def ProjectionCode.instL (code : ProjectionCode)
    (ls : List VLevel) : ProjectionCode where
  fieldSort := code.fieldSort.inst ls
  typeFn := code.typeFn.instL ls
  minor := code.minor.instL ls
  projector := code.projector.instL ls

@[simp] theorem ProjectionCode.instL_instRevAt
    (code : ProjectionCode) (args : List VExpr) (k : Nat)
    (levels : List VLevel) :
    (code.instRevAt args k).instL levels =
      (code.instL levels).instRevAt (args.map (VExpr.instL levels)) k := by
  apply ProjectionCode.ext <;>
    simp [ProjectionCode.instRevAt, ProjectionCode.instL]

theorem ProjectionCode.liftN_instRevAt
    (code : ProjectionCode) (args : List VExpr)
    (offset cutoff count : Nat) :
    (code.instRevAt args offset).liftN count (cutoff + offset) =
      (code.liftN count (cutoff + offset + args.length)).instRevAt
        (args.map fun argument => argument.liftN count cutoff) offset := by
  apply ProjectionCode.ext <;>
    simp [ProjectionCode.instRevAt, ProjectionCode.liftN,
      VExpr.liftN_instRevAt]

theorem ProjectionCode.instN_instRevAt
    (code : ProjectionCode) (args : List VExpr)
    (offset cutoff : Nat) (argument : VExpr) :
    (code.instRevAt args offset).instN argument (cutoff + offset) =
      (code.instN argument
          (cutoff + offset + args.length)).instRevAt
        (args.map fun arg => arg.inst argument cutoff) offset := by
  apply ProjectionCode.ext <;>
    simp [ProjectionCode.instRevAt, ProjectionCode.instN,
      VExpr.instN_instRevAt]

/-- Every expression payload of a projection program is closed over the
same term context. -/
def ProjectionCode.ClosedN (code : ProjectionCode) (k : Nat) : Prop :=
  code.typeFn.ClosedN k ∧ code.minor.ClosedN k ∧ code.projector.ClosedN k

theorem ProjectionCode.closedN_of_liftN_one_eq
    (code : ProjectionCode) (cutoff : Nat)
    (equality : code.liftN 1 cutoff = code) :
    code.ClosedN cutoff := by
  refine ⟨VExpr.closedN_of_liftN_one_eq code.typeFn cutoff ?_,
    VExpr.closedN_of_liftN_one_eq code.minor cutoff ?_,
    VExpr.closedN_of_liftN_one_eq code.projector cutoff ?_⟩
  · simpa [ProjectionCode.liftN] using
      congrArg ProjectionCode.typeFn equality
  · simpa [ProjectionCode.liftN] using
      congrArg ProjectionCode.minor equality
  · simpa [ProjectionCode.liftN] using
      congrArg ProjectionCode.projector equality

theorem ProjectionCode.ClosedN.instN_eq
    {code : ProjectionCode} {cutoff : Nat}
    (self : code.ClosedN cutoff) (argument : VExpr) (index : Nat)
    (above : cutoff ≤ index) :
    code.instN argument index = code := by
  apply ProjectionCode.ext
  · rfl
  · exact self.1.instN_eq above
  · exact self.2.1.instN_eq above
  · exact self.2.2.instN_eq above

/-- The constructor-headed major used by a projection minor after all fields
have been introduced. -/
def projectionConstructorApp (view : VStructureView)
    (levels : List VLevel) (params fields : List VExpr) : VExpr :=
  VExpr.appN (.const view.constructorName levels)
    (params.map (VExpr.liftN fields.length) ++
      VExpr.bvarRevRange 0 fields.length)

/-- The field-context reference shape of a one-constructor projection minor.
Semantic contracts use the exact generated domain below, which additionally
retains every recursive induction-hypothesis binder. -/
def fieldProjectionMinorType (view : VStructureView)
    (levels : List VLevel) (params fields : List VExpr)
    (typeFn : VExpr) : VExpr :=
  VExpr.forallN fields
    (.app (typeFn.liftN fields.length)
      (view.projectionConstructorApp levels params fields))

/-- The exact generated minor domain after specializing recursor universes,
constructor parameters, and the projection motive.  This is the underlying
definition used by the semantic `projectionMinorType` contract below. -/
def generatedProjectionMinorType (view : VStructureView)
    (fieldSort : VLevel) (levels : List VLevel) (params : List VExpr)
    (typeFn : VExpr) : VExpr :=
  (((VInductDecl.GenerationChecked.minorType
      (source := view.source) view.constructor view.generation.elimination).instL
      (view.projectionLevels fieldSort levels)).instRevAt params 1).inst
          typeFn

/-- The semantic projection-minor domain is exactly the domain emitted by
checked recursor generation, including any recursive induction hypotheses. -/
def projectionMinorType (view : VStructureView)
    (fieldSort : VLevel) (levels : List VLevel) (params : List VExpr)
    (typeFn : VExpr) : VExpr :=
  view.generatedProjectionMinorType fieldSort levels params typeFn

/-- The induction-hypothesis binder types occurring after the specialized
constructor fields in the exact generated projection minor. -/
def projectionIHTypes (view : VStructureView)
    (fieldSort : VLevel) (levels : List VLevel) (params : List VExpr)
    (typeFn : VExpr) : List VExpr :=
  VExpr.telN view.constructor.view.recursive.length <|
    VExpr.dropN (view.specializedFields levels params).length <|
      view.generatedProjectionMinorType fieldSort levels params typeFn

/-- The generated IH telescope before it is recovered from the exact minor
Pi tower. Naming this syntax makes its parameter/motive naturality explicit. -/
private def generatedProjectionIHBinders (view : VStructureView)
    (fieldSort : VLevel) (levels : List VLevel) (params : List VExpr)
    (typeFn : VExpr) : List VExpr :=
  let pLevels := view.projectionLevels fieldSort levels
  let rawFields := view.constructor.fieldsR view.source.uvars
    view.source.nparams view.generation.elimination
  let m := rawFields.length
  let rawIHs := VInductDecl.ihsFromRecArgs m
    (view.constructor.recArgsR view.source.uvars
      view.generation.elimination) 0
  VExpr.instTelN typeFn
    (((rawIHs.map (VExpr.instL pLevels)).zipIdx (1 + m)).map
      fun entry => entry.1.instRevAt params entry.2) m

private theorem generatedProjectionMinorType_telescope_shape
    (view : VStructureView) (fieldSort : VLevel)
    (levels : List VLevel) (params : List VExpr) (typeFn : VExpr) :
    ∃ fieldBinders body,
      fieldBinders.length = (view.specializedFields levels params).length ∧
      (view.generatedProjectionIHBinders fieldSort levels params typeFn).length =
        view.constructor.view.recursive.length ∧
      view.generatedProjectionMinorType fieldSort levels params typeFn =
        VExpr.forallN fieldBinders
          (VExpr.forallN
            (view.generatedProjectionIHBinders fieldSort levels params typeFn)
            body) := by
  let pLevels := view.projectionLevels fieldSort levels
  let rawFields := view.constructor.fieldsR view.source.uvars
    view.source.nparams view.generation.elimination
  let recArgs := view.constructor.recArgsR view.source.uvars
    view.generation.elimination
  let m := rawFields.length
  let r := recArgs.length
  let rawIHs := VInductDecl.ihsFromRecArgs m recArgs 0
  let fieldBinders := VExpr.instTelN typeFn
    (((VExpr.liftTelN 1 rawFields 0).map (VExpr.instL pLevels)).zipIdx 1 |>.map
      fun entry => entry.1.instRevAt params entry.2) 0
  let ihBinders := view.generatedProjectionIHBinders
    fieldSort levels params typeFn
  let rawBody := VExpr.appN (.bvar (m + r))
    ((view.constructor.resultIndicesR view.source.uvars
        view.generation.elimination |>.map fun expression =>
          (expression.liftN 1 m).liftN r) ++
      [VExpr.appN
        (.const view.constructor.raw.name view.generation.sourceLevels)
        (VExpr.bvarRevRange (r + m + 1) view.source.nparams ++
          VExpr.bvarRevRange r m)])
  let body := ((rawBody.instL pLevels).instRevAt params (1 + m + r)).inst
    typeFn (m + r)
  refine ⟨fieldBinders, body, ?_, ?_, ?_⟩
  · rw [VExpr.instTelN_length]
    simp [rawFields, specializedFields, fields,
      VInductDecl.NormalizedCtor.fieldsR]
    rw [VExpr.liftTelN_length]
    simp
  · unfold generatedProjectionIHBinders
    rw [VExpr.instTelN_length]
    simp [VInductDecl.NormalizedCtor.recArgsR,
      VInductDecl.ihsFromRecArgs_length]
  · simp [generatedProjectionMinorType,
      VInductDecl.GenerationChecked.minorType,
      VExpr.instL_forallN, VExpr.instN_forallN,
      VExpr.instRevAt_forallN_projection,
      VExpr.liftTelN_instL, VExpr.liftTelN_length,
      VInductDecl.ihsFromRecArgs_length,
      pLevels, rawFields, recArgs, m, r,
      fieldBinders, generatedProjectionIHBinders, rawBody, body,
      Nat.add_assoc, Nat.add_comm]

private theorem projectionIHTypes_eq_generatedProjectionIHBinders
    (view : VStructureView) (fieldSort : VLevel)
    (levels : List VLevel) (params : List VExpr) (typeFn : VExpr) :
    view.projectionIHTypes fieldSort levels params typeFn =
      view.generatedProjectionIHBinders fieldSort levels params typeFn := by
  obtain ⟨fieldBinders, body, hfields, hihs, hshape⟩ :=
    generatedProjectionMinorType_telescope_shape
      view fieldSort levels params typeFn
  unfold projectionIHTypes
  rw [hshape, ← hfields, VExpr.dropN_forallN_length,
    ← hihs, VExpr.telN_forallN_length]

/-- The exact generated minor contains one induction-hypothesis binder for
every recursive argument, independently of later semantic typing evidence. -/
@[simp] theorem projectionIHTypes_length (view : VStructureView)
    (fieldSort : VLevel) (levels : List VLevel) (params : List VExpr)
    (typeFn : VExpr) :
    (view.projectionIHTypes fieldSort levels params typeFn).length =
      view.constructor.view.recursive.length := by
  obtain ⟨fieldBinders, body, hfields, hihs, hshape⟩ :=
    generatedProjectionMinorType_telescope_shape view fieldSort levels params typeFn
  unfold projectionIHTypes
  rw [hshape, ← hfields, VExpr.dropN_forallN_length,
    ← hihs, VExpr.telN_forallN_length, hihs]

/-- The generated minor result after stripping its constructor-field and
induction-hypothesis binders. -/
def projectionMinorResult (view : VStructureView)
    (fieldSort : VLevel) (levels : List VLevel) (params : List VExpr)
    (typeFn : VExpr) : VExpr :=
  VExpr.dropN view.constructor.view.recursive.length <|
    VExpr.dropN (view.specializedFields levels params).length <|
      view.generatedProjectionMinorType fieldSort levels params typeFn

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

@[simp] theorem generatedProjectionMinorType_instL (view : VStructureView)
    (fieldSort : VLevel) (levels : List VLevel) (params : List VExpr)
    (typeFn : VExpr) (ls : List VLevel) :
    (view.generatedProjectionMinorType fieldSort levels params typeFn).instL ls =
      view.generatedProjectionMinorType (fieldSort.inst ls)
        (levels.map (VLevel.inst ls)) (params.map (VExpr.instL ls))
        (typeFn.instL ls) := by
  simp [generatedProjectionMinorType, VExpr.instL_instRevAt,
    VExpr.instL_instL, VExpr.instL_instN,
    projectionLevels_instL]

@[simp] theorem projectionIHTypes_instL (view : VStructureView)
    (fieldSort : VLevel) (levels : List VLevel) (params : List VExpr)
    (typeFn : VExpr) (ls : List VLevel) :
    (view.projectionIHTypes fieldSort levels params typeFn).map
        (VExpr.instL ls) =
      view.projectionIHTypes (fieldSort.inst ls)
        (levels.map (VLevel.inst ls)) (params.map (VExpr.instL ls))
        (typeFn.instL ls) := by
  unfold projectionIHTypes
  rw [← VExpr.telN_instL, ← VExpr.dropN_instL,
    generatedProjectionMinorType_instL]
  have hfields := view.specializedFields_instL levels params ls
  have hfieldsLength := congrArg List.length hfields
  simp only [List.length_map] at hfieldsLength
  rw [hfieldsLength]

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
    (hi : i < allFields.length)
    (hIHTypes : ∀ (sort : VLevel) (fn : VExpr),
      VExpr.liftTelN n
          (view.projectionIHTypes sort levels params fn)
          (k + allFields.length) =
        view.projectionIHTypes sort levels
          (params.map fun param => param.liftN n k)
          (fn.liftN n k)) :
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
  have hminorLift :
      (VExpr.selectFieldMinor allFields
          (view.projectionIHTypes fieldSort levels params
            (.lam structType
              ((field.liftN 1 i).instRevAt
                (previous.map fun code =>
                  VExpr.app code.projector.lift (.bvar 0)) 0)))
          i).liftN n k =
        VExpr.selectFieldMinor (VExpr.liftTelN n allFields k)
          (view.projectionIHTypes fieldSort levels
            (params.map fun param => param.liftN n k)
            (.lam (structType.liftN n k)
              (((field.liftN n (k + i)).liftN 1 i).instRevAt
                ((previous.map fun code => code.liftN n k).map fun code =>
                  VExpr.app code.projector.lift (.bvar 0)) 0)))
          i := by
    rw [VExpr.selectFieldMinor_liftN _ _ _ n k hi,
      hIHTypes fieldSort]
    simp [VExpr.liftN, hmotive]
  apply ProjectionCode.ext
  · rfl
  · simp [projectionCode, ProjectionCode.liftN, VExpr.liftN,
      hmotive]
  · simpa [projectionCode, ProjectionCode.liftN] using hminorLift
  · simp [projectionCode, ProjectionCode.liftN, VExpr.liftN,
      VExpr.liftN_appN, VExpr.liftN_lift_projection, List.map_append,
      List.map_map, Function.comp_def, hmotive, hmotiveLift,
      hminorLift]

private theorem projectionCode_instN (view : VStructureView)
    (levels : List VLevel) (params allFields : List VExpr)
    (structType field : VExpr) (fieldSort : VLevel) (i : Nat)
    (previous : List ProjectionCode) (a : VExpr) (k : Nat)
    (hprevious : previous.length = i)
    (hi : i < allFields.length)
    (hIHTypes : ∀ (sort : VLevel) (fn : VExpr),
      VExpr.instTelN a
          (view.projectionIHTypes sort levels params fn)
          (k + allFields.length) =
        view.projectionIHTypes sort levels
          (params.map fun param => param.inst a k)
          (fn.inst a k)) :
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
  have hminorInst :
      (VExpr.selectFieldMinor allFields
          (view.projectionIHTypes fieldSort levels params
            (.lam structType
              ((field.liftN 1 i).instRevAt
                (previous.map fun code =>
                  VExpr.app code.projector.lift (.bvar 0)) 0)))
          i).inst a k =
        VExpr.selectFieldMinor (VExpr.instTelN a allFields k)
          (view.projectionIHTypes fieldSort levels
            (params.map fun param => param.inst a k)
            (.lam (structType.inst a k)
              (((field.inst a (k + i)).liftN 1 i).instRevAt
                ((previous.map fun code => code.instN a k).map fun code =>
                  VExpr.app code.projector.lift (.bvar 0)) 0)))
          i := by
    rw [VExpr.selectFieldMinor_instN _ _ _ k a hi,
      hIHTypes fieldSort]
    simp [VExpr.inst, hmotive]
  apply ProjectionCode.ext
  · rfl
  · simp [projectionCode, ProjectionCode.instN, VExpr.inst, hmotive]
  · simpa [projectionCode, ProjectionCode.instN] using hminorInst
  · simp [projectionCode, ProjectionCode.instN, VExpr.inst, VExpr.instN_appN,
      ← VExpr.lift_instN_lo, List.map_append, List.map_map,
      Function.comp_def, hmotive, hminorInst]

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
    (hfields : i + fields.length = allFields.length)
    (hIHTypes : ∀ (sort : VLevel) (fn : VExpr),
      VExpr.instTelN a
          (view.projectionIHTypes sort levels params fn)
          (k + allFields.length) =
        view.projectionIHTypes sort levels
          (params.map fun param => param.inst a k)
          (fn.inst a k)) :
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
            structType field fieldSort i previous a k hprevious hi hIHTypes
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
    VExpr.instL_instRevAt, VExpr.instL_appN, VExpr.instL_liftN,
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
    (hfields : i + fields.length = allFields.length)
    (hIHTypes : ∀ (sort : VLevel) (fn : VExpr),
      VExpr.liftTelN n
          (view.projectionIHTypes sort levels params fn)
          (k + allFields.length) =
        view.projectionIHTypes sort levels
          (params.map fun param => param.liftN n k)
          (fn.liftN n k)) :
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
            structType field fieldSort i previous n k hprevious hi hIHTypes
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
          code.minor = VExpr.selectFieldMinor allFields
            (view.projectionIHTypes code.fieldSort levels params code.typeFn)
            (i + j) ∧
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
        code.minor = VExpr.selectFieldMinor
          (view.specializedFields levels params)
          (view.projectionIHTypes code.fieldSort levels params code.typeFn) idx ∧
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
      (view.projectionMinorType code.fieldSort levels params code.typeFn)

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
      (view.projectionMinorType code.fieldSort levels params code.typeFn)

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

/-- Producer-owned layout well-formedness of one structure view in its
registered environment.  This is exactly the metadata/telescope fragment
available for every host projection-ready family.  In particular it does
not claim that small elimination can synthesize a projector into every field
sort; that operational capability is intentionally kept in `WF` below. -/
structure LayoutWF (view : VStructureView) (env : VEnv) : Prop
    extends VStructureView.Registered view env where
  generationSemantics : VStructureView.GenerationSemantics view env
  parameters : env.OnTel view.uvars []
    view.generation.block.checked.params
  parameters_length :
    view.generation.block.checked.params.length = view.nparams
  fieldTelescope : env.OnSortTel view.uvars
    view.generation.block.checked.params.reverse
      view.fields view.fieldSorts

/-- Full generated-projector well-formedness for a singleton-backed view.
The extra condition is stronger than kernel projection readiness: it says
that every retained field is a legal motive target when the generated
recursor has small elimination. -/
structure WF (view : VStructureView) (env : VEnv) : Prop
    extends VStructureView.LayoutWF view env where
  smallFields : view.generation.elimination = .small →
    ∀ level ∈ view.fieldSorts, level = .zero

/-- The literal registered family type is definitionally equal to the
projection-facing type whose terminal is the validator-owned result sort. -/
theorem LayoutWF.rawFamilyType_defeq_familyType
    (self : VStructureView.LayoutWF view env) :
    ∃ sortLevel, env.IsDefEq view.uvars []
      view.rawFamilyType view.familyType (.sort sortLevel) := by
  have htel :=
    self.generationSemantics.familyTelescope.raw_onTel.telDefEq_refl
  have hresult : env.IsDefEq view.uvars
      ((view.generation.block.rawParams ++
        view.generation.block.rawIndices).reverse ++ [])
      view.generation.block.rawResult
      (.sort view.generation.block.checked.resultLevel)
      (.sort (.succ view.generation.block.checked.resultLevel)) := by
    simpa using self.generationSemantics.familyResult
  obtain ⟨sortLevel, hforall⟩ :=
    htel.forallN_defeq hresult
  refine ⟨sortLevel, ?_⟩
  simpa [VStructureView.rawFamilyType, VStructureView.familyType,
    VInductDecl.NormalizedChecked.rawType_eq, view.raw_indices_eq,
    VExpr.forallN_append, VExpr.forallN] using hforall

/-- A registered family constant may be typed at the projection-facing
sort-normalized family type in every ambient context. -/
theorem LayoutWF.familyConst_hasType
    (self : VStructureView.LayoutWF view env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars) :
    env.HasType U Γ (.const view.name levels)
      (view.familyType.instL levels) := by
  obtain ⟨_, htype⟩ := self.rawFamilyType_defeq_familyType
  have htypeLevels := htype.instL hlevels
  have hraw : env.HasType U [] (.const view.name levels)
      (view.rawFamilyType.instL levels) := by
    apply VEnv.HasType.const self.family hlevels
    rw [view.generation.block.sourceType_uvars_eq]
    exact hlevelsLength
  exact (htypeLevels.defeq hraw).weak0 henv

/-- The projection-facing normalized family type is syntactically closed. -/
theorem LayoutWF.familyType_closed
    (self : VStructureView.LayoutWF view env) (henv : env.Ordered) :
    view.familyType.ClosedN := by
  obtain ⟨_, htype⟩ := self.rawFamilyType_defeq_familyType
  exact (htype.closedN' henv.closed trivial).2.1

/-- Registered structure views at the same family name have the same
parameter count.  Exact family lookup identifies their raw type payloads,
and `nparams_eq_familyArity` then recovers the count from that shared syntax.
This is the family-side rigidity needed by projection metadata alignment. -/
theorem WF.nparams_eq_of_name_eq
    {left right : VStructureView} {env : VEnv}
    (self : left.WF env) (other : right.WF env)
    (name_eq : left.name = right.name) :
    left.nparams = right.nparams := by
  have familyEq :
      left.generation.block.sourceType.toVConstant =
        right.generation.block.sourceType.toVConstant := by
    apply Option.some.inj
    exact self.family.symm.trans <|
      (congrArg env.constants name_eq).trans other.family
  have typeEq :
      left.generation.block.sourceType.type =
        right.generation.block.sourceType.type := by
    simpa using congrArg VConstant.type familyEq
  calc
    left.nparams =
        (ctorFields left.generation.block.sourceType.type).length :=
      left.nparams_eq_rawFamilyArity
    _ = (ctorFields right.generation.block.sourceType.type).length := by
      rw [typeEq]
    _ = right.nparams := right.nparams_eq_rawFamilyArity.symm

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

theorem LayoutWF.mono {env env' : VEnv} (henv : env ≤ env')
    (self : VStructureView.LayoutWF view env) :
    VStructureView.LayoutWF view env' where
  toRegistered := self.toRegistered.mono henv
  generationSemantics := self.generationSemantics.mono henv
  parameters := self.parameters.monoProjection henv
  parameters_length := self.parameters_length
  fieldTelescope := self.fieldTelescope.mono henv

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
  toLayoutWF := self.toLayoutWF.mono henv
  smallFields := self.smallFields

/-- Reassemble the standard generated-artifact invariant when an ordered
environment is available. -/
theorem LayoutWF.toGenerationEnv (self : VStructureView.LayoutWF view env)
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

theorem WF.toGenerationEnv (self : VStructureView.WF view env)
    (henv : env.Ordered) :
    VInductDecl.GenerationEnv view.generation env :=
  self.toLayoutWF.toGenerationEnv henv

theorem LayoutWF.field_closed (self : VStructureView.LayoutWF view env)
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

theorem LayoutWF.specializedFields_liftN
    (self : VStructureView.LayoutWF view env) (henv : env.Ordered)
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

abbrev WF.field_closed (self : VStructureView.WF view env) :=
  self.toLayoutWF.field_closed

abbrev WF.specializedFields_liftN
    (self : VStructureView.WF view env) :=
  self.toLayoutWF.specializedFields_liftN

theorem LayoutWF.specializedFields_instN
    (self : VStructureView.LayoutWF view env) (henv : env.Ordered)
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

abbrev WF.specializedFields_instN
    (self : VStructureView.WF view env) :=
  self.toLayoutWF.specializedFields_instN

/-- The raw generated IH entries are closed at their exact positions before
parameter and motive specialization.  This proof uses only recursive-argument
well-formedness, not semantic typing of the complete minor. -/
private theorem LayoutWF.generatedProjectionRawIHs_closedN
    (self : VStructureView.LayoutWF view env) (henv : env.Ordered)
    (fieldSort : VLevel) (levels : List VLevel) (params : List VExpr)
    (hparams : params.length = view.nparams) :
    ∀ (index : Nat) (ih : VExpr),
      ((VInductDecl.ihsFromRecArgs
          (view.constructor.fieldsR view.source.uvars view.source.nparams
            view.generation.elimination).length
          (view.constructor.recArgsR view.source.uvars
            view.generation.elimination) 0).map
        (VExpr.instL (view.projectionLevels fieldSort levels)))[index]? =
          some ih →
      ih.ClosedN
        ((view.constructor.fieldsR view.source.uvars view.source.nparams
          view.generation.elimination).length + index + params.length + 1) := by
  let S := self.toGenerationEnv henv
  have hconstructor :
      view.constructor ∈ view.generation.block.ctorPairs := by
    rw [view.constructor_eq]
    exact .head _
  intro index ih hlookup
  rw [List.getElem?_map] at hlookup
  obtain ⟨rawIH, hrawIH, rfl⟩ := Option.map_eq_some_iff.1 hlookup
  have hclosed := S.ihsFromRecArgs_closedN hconstructor
    (view.constructor.recArgsR view.source.uvars
      view.generation.elimination)
    (fun _ hrecursive => hrecursive) 0 index rawIH hrawIH
  have hclosed' := VExpr.ClosedN.instL
    (ls := view.projectionLevels fieldSort levels) hclosed
  simpa only [hparams, Nat.zero_add, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using hclosed'

private theorem LayoutWF.projectionIHTypes_liftN
    (self : VStructureView.LayoutWF view env) (henv : env.Ordered)
    (fieldSort : VLevel) (levels : List VLevel) (params : List VExpr)
    (hparams : params.length = view.nparams) (typeFn : VExpr)
    (n k : Nat) :
    VExpr.liftTelN n
        (view.projectionIHTypes fieldSort levels params typeFn)
        (k + (view.specializedFields levels params).length) =
      view.projectionIHTypes fieldSort levels
        (params.map fun param => param.liftN n k) (typeFn.liftN n k) := by
  rw [projectionIHTypes_eq_generatedProjectionIHBinders,
    projectionIHTypes_eq_generatedProjectionIHBinders]
  have hfieldsLength :
      (view.specializedFields levels params).length =
        (view.constructor.fieldsR view.source.uvars view.source.nparams
          view.generation.elimination).length := by
    simp [specializedFields, fields, NormalizedCtor.fieldsR_length]
  rw [hfieldsLength]
  dsimp only [generatedProjectionIHBinders]
  simpa only [Nat.add_comm] using
    VExpr.specializeProjectionIHs_liftN
      ((VInductDecl.ihsFromRecArgs
        (view.constructor.fieldsR view.source.uvars view.source.nparams
          view.generation.elimination).length
        (view.constructor.recArgsR view.source.uvars
          view.generation.elimination) 0).map
        (VExpr.instL (view.projectionLevels fieldSort levels)))
      params typeFn
      (view.constructor.fieldsR view.source.uvars view.source.nparams
        view.generation.elimination).length n k
      (self.generatedProjectionRawIHs_closedN henv fieldSort levels params
        hparams)

private theorem LayoutWF.projectionIHTypes_instN
    (self : VStructureView.LayoutWF view env) (henv : env.Ordered)
    (fieldSort : VLevel) (levels : List VLevel) (params : List VExpr)
    (hparams : params.length = view.nparams) (typeFn a : VExpr)
    (k : Nat) :
    VExpr.instTelN a
        (view.projectionIHTypes fieldSort levels params typeFn)
        (k + (view.specializedFields levels params).length) =
      view.projectionIHTypes fieldSort levels
        (params.map fun param => param.inst a k) (typeFn.inst a k) := by
  rw [projectionIHTypes_eq_generatedProjectionIHBinders,
    projectionIHTypes_eq_generatedProjectionIHBinders]
  have hfieldsLength :
      (view.specializedFields levels params).length =
        (view.constructor.fieldsR view.source.uvars view.source.nparams
          view.generation.elimination).length := by
    simp [specializedFields, fields, NormalizedCtor.fieldsR_length]
  rw [hfieldsLength]
  dsimp only [generatedProjectionIHBinders]
  simpa only [Nat.add_comm] using
    VExpr.specializeProjectionIHs_instN
      ((VInductDecl.ihsFromRecArgs
        (view.constructor.fieldsR view.source.uvars view.source.nparams
          view.generation.elimination).length
        (view.constructor.recArgsR view.source.uvars
          view.generation.elimination) 0).map
        (VExpr.instL (view.projectionLevels fieldSort levels)))
      params typeFn a
      (view.constructor.fieldsR view.source.uvars view.source.nparams
        view.generation.elimination).length k
      (self.generatedProjectionRawIHs_closedN henv fieldSort levels params
        hparams)

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

/-- The outer binder telescope of the exact generated projection minor is
the source-order specialized constructor-field telescope.  Recursive
classification affects only the following IH binders. -/
theorem generatedProjectionMinorType_fields (view : VStructureView)
    (fieldSort : VLevel) (levels : List VLevel)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (typeFn : VExpr) :
    VExpr.telN (view.specializedFields levels params).length
        (view.generatedProjectionMinorType fieldSort levels params typeFn) =
      view.specializedFields levels params := by
  let pLevels := view.projectionLevels fieldSort levels
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
  have hspecializedLength :
      (view.specializedFields levels params).length =
        (view.constructor.rawFields view.source.nparams).length := by
    simp [VStructureView.specializedFields, VStructureView.fields]
  simp [VStructureView.generatedProjectionMinorType,
    VInductDecl.GenerationChecked.minorType,
    VInductDecl.NormalizedCtor.fieldsR,
    VExpr.instL_forallN, VExpr.liftTelN_instL,
    VExpr.instL_instL, VExpr.instN_forallN,
    VExpr.instRevAt_forallN_projection,
    List.map_map, Function.comp_def,
    VStructureView.sourceLevels_projectionLevels view fieldSort levels
      hlevelsLength,
    hspecializedLength, hfieldTel']
  rw [← hspecializedLength]
  exact VExpr.telN_forallN_length _ _

/-- The exact semantic minor domain decomposes into specialized fields, the
generated IH telescope, and the generated result cursor. -/
theorem projectionMinorType_decompose (view : VStructureView)
    (fieldSort : VLevel) (levels : List VLevel)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (typeFn : VExpr) :
    view.projectionMinorType fieldSort levels params typeFn =
      VExpr.forallN (view.specializedFields levels params)
        (VExpr.forallN
          (view.projectionIHTypes fieldSort levels params typeFn)
          (view.projectionMinorResult fieldSort levels params typeFn)) := by
  let exactMinor :=
    view.generatedProjectionMinorType fieldSort levels params typeFn
  let fields := view.specializedFields levels params
  let cursor := VExpr.dropN fields.length exactMinor
  have hfields : VExpr.telN fields.length exactMinor = fields := by
    simpa [fields, exactMinor] using
      view.generatedProjectionMinorType_fields fieldSort levels
        hlevelsLength params typeFn
  calc
    view.projectionMinorType fieldSort levels params typeFn = exactMinor := rfl
    _ = VExpr.forallN (VExpr.telN fields.length exactMinor) cursor :=
      (VExpr.forallN_telN_dropN fields.length exactMinor).symm
    _ = VExpr.forallN fields cursor := by rw [hfields]
    _ = VExpr.forallN fields
        (VExpr.forallN
          (VExpr.telN view.constructor.view.recursive.length cursor)
          (VExpr.dropN view.constructor.view.recursive.length cursor)) := by
      rw [VExpr.forallN_telN_dropN]
    _ = _ := by
      rfl

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

@[simp] theorem LayoutWF.projectionCodes_liftN
    (self : VStructureView.LayoutWF view env) (henv : env.Ordered)
    (levels : List VLevel) (params : List VExpr)
    (hparams : params.length = view.nparams) (n k : Nat) :
    (view.projectionCodes levels params).map
        (fun code => code.liftN n k) =
      view.projectionCodes levels
        (params.map fun param => param.liftN n k) := by
  unfold projectionCodes
  rw [self.specializedFields_liftN henv levels params hparams n k]
  rw [← structureType_liftN]
  apply projectionCodes.go_liftN (hIHTypes := ?_)
  · rfl
  · simp
  · intro fieldSort typeFn
    exact self.projectionIHTypes_liftN henv fieldSort levels params
      hparams typeFn n k

@[simp] theorem LayoutWF.projectionCodes_instN
    (self : VStructureView.LayoutWF view env) (henv : env.Ordered)
    (levels : List VLevel) (params : List VExpr)
    (hparams : params.length = view.nparams) (a : VExpr) (k : Nat) :
    (view.projectionCodes levels params).map
        (fun code => code.instN a k) =
      view.projectionCodes levels
        (params.map fun param => param.inst a k) := by
  unfold projectionCodes
  rw [self.specializedFields_instN henv levels params hparams a k]
  rw [← structureType_instN]
  apply projectionCodes.go_instN (hIHTypes := ?_)
  · rfl
  · simp
  · intro fieldSort typeFn
    exact self.projectionIHTypes_instN henv fieldSort levels params
      hparams typeFn a k

abbrev WF.projectionCodes_liftN
    (self : VStructureView.WF view env) :=
  self.toLayoutWF.projectionCodes_liftN

abbrev WF.projectionCodes_instN
    (self : VStructureView.WF view env) :=
  self.toLayoutWF.projectionCodes_instN

/-- The exact lower-layer structure-eta descriptor generated by a checked
structure view.  Its projector syntax is the deterministic projector program
list already certified by the view; the proof fields are only the three
syntactic naturality laws required by Theory transport. -/
def LayoutWF.toStructEta (self : VStructureView.LayoutWF view env)
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

abbrev WF.toStructEta (self : VStructureView.WF view env) :=
  self.toLayoutWF.toStructEta

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
    LayoutWF.toStructEta, VStructureView.etaRebuild,
    VStructureView.projectionArgs]
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
theorem _root_.Lean4Lean.VStructureView.LayoutWF.constructorParamsSpine
    (self : VStructureView.LayoutWF view env) (henv : env.Ordered)
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
        (.sort (view.generation.block.checked.resultLevel.inst levels)))
      params (.sort resultLevel) := by
    simpa [VStructureView.familyType, VExpr.instL_forallN,
      VExpr.instL] using hspine
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

abbrev _root_.Lean4Lean.VStructureView.WF.constructorParamsSpine
    (self : VStructureView.WF view env) :=
  self.toLayoutWF.constructorParamsSpine

/-- Parameters accepted by the structure family also consume the checked
family-parameter prefix used by mixed constructor generation.  Keeping this
bridge separate from `constructorParamsSpine` lets later consumers apply the
constructor at arbitrary parameters without re-proving the raw/view
parameter alignment. -/
theorem _root_.Lean4Lean.VStructureView.LayoutWF.checkedParamsSpine
    (self : VStructureView.LayoutWF view env) (henv : env.Ordered)
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

abbrev _root_.Lean4Lean.VStructureView.WF.checkedParamsSpine
    (self : VStructureView.WF view env) :=
  self.toLayoutWF.checkedParamsSpine

/-- The generated constructor, after the exact checked parameter prefix, has
the canonical specialized field telescope and returns the corresponding
structure family application.  This is the constructor half of
rule-independent structure-eta subject reduction. -/
theorem _root_.Lean4Lean.VStructureView.LayoutWF.constructorPrefix_hasType
    (self : VStructureView.LayoutWF view env) (henv : env.Ordered)
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

abbrev _root_.Lean4Lean.VStructureView.WF.constructorPrefix_hasType
    (self : VStructureView.WF view env) :=
  self.toLayoutWF.constructorPrefix_hasType

/-- Recover the structure-family parameter spine from the corresponding
constructor-parameter prefix.  This is the converse consumer bridge needed
when a checker recognizes a fully applied constructor before it knows the
family application carried by its result type. -/
theorem _root_.Lean4Lean.VStructureView.LayoutWF.familyParamsSpine_of_constructor
    (self : VStructureView.LayoutWF view env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (_hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    {target cursor : VExpr}
    (constructorSpine : env.SpineWF U Γ
      (VExpr.forallN
        (view.constructorParams.map (VExpr.instL levels)) target)
      params cursor) :
    env.SpineWF U Γ (view.familyType.instL levels) params
      (.sort (view.generation.block.checked.resultLevel.inst levels)) := by
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
    (.sort (view.generation.block.checked.resultLevel.inst levels))
  rw [VExpr.instRev_closedN params (by trivial)] at hout
  simpa [VStructureView.familyType, VExpr.instL_forallN,
    VExpr.forallN, VExpr.instL] using hout

abbrev _root_.Lean4Lean.VStructureView.WF.familyParamsSpine_of_constructor
    (self : VStructureView.WF view env) :=
  self.toLayoutWF.familyParamsSpine_of_constructor

theorem _root_.Lean4Lean.VStructureView.LayoutWF.specializedFields_onSortTel
    (self : VStructureView.LayoutWF view env) (henv : env.Ordered)
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
        (.sort (view.generation.block.checked.resultLevel.inst levels)))
      params (.sort resultLevel) := by
    simpa [VStructureView.familyType, VExpr.instL_forallN,
      VExpr.instL] using hspine
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

abbrev _root_.Lean4Lean.VStructureView.WF.specializedFields_onSortTel
    (self : VStructureView.WF view env) :=
  self.toLayoutWF.specializedFields_onSortTel

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
        (.sort (view.generation.block.checked.resultLevel.inst levels)))
      params (.sort resultLevel) := by
    simpa [VStructureView.familyType, VExpr.instL_forallN,
      VExpr.instL] using hspine
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

/-- The exact generated projection minor retains one IH binder per checked
recursive argument and, after those binders, applies the motive to the exact
constructor application. -/
theorem _root_.Lean4Lean.VStructureView.WF.projectionMinorGenerated_shape
    (self : VStructureView.WF view env) (henv : env.Ordered)
    (fieldSort : VLevel) (levels : List VLevel)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (typeFn : VExpr) :
    let m := (view.constructor.rawFields view.source.nparams).length
    let r := view.constructor.view.recursive.length
    (view.projectionIHTypes fieldSort levels params typeFn).length = r ∧
      view.projectionMinorResult fieldSort levels params typeFn =
        .app (typeFn.liftN (r + m))
          (VExpr.appN (.const view.constructorName levels)
            (params.map (VExpr.liftN (r + m)) ++
              VExpr.bvarRevRange r m)) := by
  let S := self.toGenerationEnv henv
  let pLevels := view.projectionLevels fieldSort levels
  let m := (view.constructor.rawFields view.source.nparams).length
  let r := view.constructor.view.recursive.length
  have hconstructorMem :
      view.constructor ∈ view.generation.block.ctorPairs := by
    simp [view.constructor_eq]
  have hresultIndices : view.constructor.view.resultIndices = [] := by
    apply List.length_eq_zero_iff.1
    rw [S.viewResultIndices_length hconstructorMem]
    simp [view.checked_indices_eq]
  let rawFields := view.constructor.rawFields view.source.nparams
  let recArgs := view.constructor.view.recursive.map fun recArg =>
    recArg.instL view.generation.sourceLevels
  let rawIHs := VInductDecl.ihsFromRecArgs rawFields.length recArgs 0
  let fieldBinders := VExpr.instTelN typeFn
    ((VExpr.liftTelN 1 (rawFields.map (VExpr.instL levels)) 0).zipIdx 1 |>.map
      fun entry => entry.1.instRevAt params entry.2) 0
  let ihBinders := VExpr.instTelN typeFn
    (((rawIHs.map (VExpr.instL pLevels)).zipIdx (1 + rawFields.length)).map
      fun entry => entry.1.instRevAt params entry.2) rawFields.length
  let body :=
    ((VExpr.appN (.bvar (r + m))
        [VExpr.appN (.const view.constructorName levels)
          (VExpr.bvarRevRange (r + m + 1) view.nparams ++
            VExpr.bvarRevRange r m)]).instRevAt params
      (r + m + 1)).inst typeFn (r + m)
  have hminorShape :
      view.generatedProjectionMinorType fieldSort levels params typeFn =
        VExpr.forallN fieldBinders (VExpr.forallN ihBinders body) := by
    simp [VStructureView.generatedProjectionMinorType,
      VInductDecl.GenerationChecked.minorType,
      VInductDecl.NormalizedCtor.fieldsR,
      VInductDecl.NormalizedCtor.recArgsR,
      VInductDecl.NormalizedCtor.resultIndicesR,
      hresultIndices, VExpr.instL_forallN, VExpr.instL_appN,
      VExpr.liftTelN_instL, VExpr.instL_instL,
      VExpr.instN_forallN,
      VExpr.instRevAt_forallN_projection,
      VExpr.liftTelN_length,
      VInductDecl.ihsFromRecArgs_length,
      VExpr.instL, VExpr.bvarRevRange_map_instL,
      List.map_append, List.map_map, Function.comp_def,
      VStructureView.sourceLevels_projectionLevels view fieldSort levels
        hlevelsLength,
      pLevels, rawFields, recArgs, rawIHs, fieldBinders, ihBinders,
      body, m, r, Nat.add_left_comm, Nat.add_comm]
  have hspecializedLength :
      (view.specializedFields levels params).length = m := by
    simp [VStructureView.specializedFields, VStructureView.fields, m]
  have hfieldBindersLength : fieldBinders.length = m := by
    simp [fieldBinders, rawFields, m, VExpr.instTelN_length,
      VExpr.liftTelN_length]
  have hihBindersLength : ihBinders.length = r := by
    simp [ihBinders, rawIHs, recArgs, rawFields, r,
      VExpr.instTelN_length, VInductDecl.ihsFromRecArgs_length]
  have hdropFields :
      VExpr.dropN m
          (VExpr.forallN fieldBinders (VExpr.forallN ihBinders body)) =
        VExpr.forallN ihBinders body := by
    rw [← hfieldBindersLength, VExpr.dropN_forallN_length]
  have hihsShape :
      view.projectionIHTypes fieldSort levels params typeFn = ihBinders := by
    unfold VStructureView.projectionIHTypes
    rw [hspecializedLength, hminorShape, hdropFields]
    change VExpr.telN r (VExpr.forallN ihBinders body) = ihBinders
    rw [← hihBindersLength, VExpr.telN_forallN_length]
  have hdropIHs :
      VExpr.dropN r (VExpr.forallN ihBinders body) = body := by
    rw [← hihBindersLength, VExpr.dropN_forallN_length]
  constructor
  · rw [hihsShape, hihBindersLength]
  · unfold VStructureView.projectionMinorResult
    rw [hspecializedLength, hminorShape, hdropFields, hdropIHs]
    have hbody := VExpr.projectionMinorBody_shape
      view.constructorName levels params m r typeFn
    rw [hparamsLength] at hbody
    simpa [body, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hbody

/-- After stripping the specialized fields and every generated recursive-IH
binder, the exact minor cursor is the projection motive applied to the exact
constructor application.  The constructor fields are shifted past the IH
stack, while the selector itself may ignore that stack. -/
theorem _root_.Lean4Lean.VStructureView.WF.projectionMinorResult_shape
    (self : VStructureView.WF view env) (henv : env.Ordered)
    (fieldSort : VLevel) (levels : List VLevel)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (typeFn : VExpr) :
    let m := (view.constructor.rawFields view.source.nparams).length
    let r := view.constructor.view.recursive.length
    view.projectionMinorResult fieldSort levels params typeFn =
      .app (typeFn.liftN (r + m))
        (VExpr.appN (.const view.constructorName levels)
          (params.map (VExpr.liftN (r + m)) ++
            VExpr.bvarRevRange r m)) :=
  (self.projectionMinorGenerated_shape henv fieldSort levels
    hlevelsLength params hparamsLength typeFn).2

/-- The generated result cursor is exactly the legacy field-context result
weakened beneath the retained recursive-IH telescope. -/
theorem _root_.Lean4Lean.VStructureView.WF.projectionMinorResult_eq_lift
    (self : VStructureView.WF view env) (henv : env.Ordered)
    (fieldSort : VLevel) (levels : List VLevel)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (typeFn : VExpr) :
    let fields := view.specializedFields levels params
    let ihs := view.projectionIHTypes fieldSort levels params typeFn
    view.projectionMinorResult fieldSort levels params typeFn =
      (VExpr.app (typeFn.liftN fields.length)
        (view.projectionConstructorApp levels params fields)).liftN ihs.length := by
  let fields := view.specializedFields levels params
  let ihs := view.projectionIHTypes fieldSort levels params typeFn
  have hfieldsLength : fields.length =
      (view.constructor.rawFields view.source.nparams).length := by
    simp [fields, VStructureView.specializedFields, VStructureView.fields]
  have hihsLength : ihs.length =
      view.constructor.view.recursive.length := by
    simp [ihs]
  rw [self.projectionMinorResult_shape henv fieldSort levels
    hlevelsLength params hparamsLength typeFn]
  change _ = (VExpr.app (typeFn.liftN fields.length)
    (view.projectionConstructorApp levels params fields)).liftN ihs.length
  rw [hfieldsLength, hihsLength]
  simp only [VStructureView.projectionConstructorApp,
    VExpr.liftN, VExpr.liftN_appN, VExpr.liftN_liftN,
    VExpr.bvarRevRange_liftN_low,
    List.map_append, List.map_map, Function.comp_def,
    Nat.add_zero, Nat.add_comm]
  rw [hfieldsLength]

/-- The parameters and projection motive expose the exact generated minor
domain at the head of the remaining recursor cursor.  Keeping this boundary
before supplying a minor lets later proofs recover well-formedness of the
generated field/IH telescope directly from recursor regularity. -/
theorem _root_.Lean4Lean.VStructureView.WF.projectionMotiveSpine
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
    {typeFn : VExpr}
    (typeFnType : env.HasType U Γ typeFn
      (.forallE (view.structureType levels params) (.sort fieldSort))) :
    env.SpineWF U Γ
      (view.generation.recType.instL
        (view.projectionLevels fieldSort levels))
      (params ++ [typeFn])
      (.forallE (view.projectionMinorType fieldSort levels params typeFn)
        (.forallE (view.structureType levels params).lift
          (.app (typeFn.liftN 2) (.bvar 0)))) := by
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
        .forallE (view.projectionMinorType fieldSort levels params typeFn)
          (.forallE (view.structureType levels params).lift
            (.app (typeFn.liftN 2) (.bvar 0))) := by
    simp only [VStructureView.projectionMinorType]
    simp [gen, pLevels, recRest, k, ni,
      VInductDecl.GenerationChecked.minorTypes,
      VInductDecl.GenerationChecked.minorTypesAux,
      VInductDecl.GenerationChecked.minorType,
      VInductDecl.GenerationChecked.idxTel,
      VInductDecl.NormalizedCtor.fieldsR,
      VInductDecl.NormalizedCtor.recArgsR,
      VInductDecl.NormalizedCtor.resultIndicesR,
      VStructureView.generatedProjectionMinorType,
      view.constructor_eq, view.raw_indices_eq, hresultIndices,
      VExpr.instL_forallN, VExpr.instL_appN,
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
  simpa [gen, pLevels, recTail, recRest, k, ni,
    VInductDecl.GenerationChecked.recType, List.append_assoc] using hwithMotive

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
      (view.projectionMinorType fieldSort levels params typeFn)) :
    env.SpineWF U Γ
      (view.generation.recType.instL
        (view.projectionLevels fieldSort levels))
      (params ++ [typeFn, minor])
      (.forallE (view.structureType levels params)
        (.app typeFn.lift (.bvar 0))) := by
  have hwithMotive := self.projectionMotiveSpine henv
    levels hlevels hlevelsLength params hparamsLength paramsSpine
    fieldSort hmotiveLevel typeFnType
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
  simpa [List.append_assoc] using hwithMinor

/-- The exact generated projection-minor domain is a type.  This follows by
applying the generated recursor through its projection motive and inverting
regularity of the remaining pi cursor, so recursive IH binders are retained
rather than normalized away. -/
theorem _root_.Lean4Lean.VStructureView.WF.projectionMinorType_isType
    (self : VStructureView.WF view env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (fieldSort : VLevel) (hfieldSort : fieldSort.WF U)
    (hmotiveLevel :
      view.generation.motiveLevel.inst
          (view.projectionLevels fieldSort levels) = fieldSort)
    {typeFn : VExpr}
    (typeFnType : env.HasType U Γ typeFn
      (.forallE (view.structureType levels params) (.sort fieldSort))) :
    env.IsType U Γ
      (view.projectionMinorType fieldSort levels params typeFn) := by
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
  have hspine := self.projectionMotiveSpine henv
    levels hlevels hlevelsLength params hparamsLength paramsSpine
    fieldSort hmotiveLevel typeFnType
  have happ := hspine.hasType_appN hrec
  obtain ⟨_, hcursorType⟩ := happ.isType henv hΓ
  exact (hcursorType.forallE_inv henv).1

/-- The recursive-IH portion extracted from the exact generated projection
minor is a well-formed telescope after the specialized constructor fields. -/
theorem _root_.Lean4Lean.VStructureView.WF.projectionIHTypes_onTel
    (self : VStructureView.WF view env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (fieldSort : VLevel) (hfieldSort : fieldSort.WF U)
    (hmotiveLevel :
      view.generation.motiveLevel.inst
          (view.projectionLevels fieldSort levels) = fieldSort)
    {typeFn : VExpr}
    (typeFnType : env.HasType U Γ typeFn
      (.forallE (view.structureType levels params) (.sort fieldSort))) :
    env.OnTel U ((view.specializedFields levels params).reverse ++ Γ)
      (view.projectionIHTypes fieldSort levels params typeFn) := by
  obtain ⟨minorSort, hminor⟩ := self.projectionMinorType_isType henv hΓ
    levels hlevels hlevelsLength params hparamsLength paramsSpine
    fieldSort hfieldSort hmotiveLevel typeFnType
  rw [view.projectionMinorType_decompose fieldSort levels
    hlevelsLength params typeFn] at hminor
  obtain ⟨_, afterFieldsSort, hafterFields⟩ :=
    VEnv.HasType.forallN_wf henv hminor
  obtain ⟨hihs, _, _⟩ :=
    VEnv.HasType.forallN_wf henv hafterFields
  exact hihs

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
      (view.projectionMinorType fieldSort levels params typeFn)) :
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
      (view.projectionMinorType fieldSort levels params typeFn))
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
  have hfamily : env.HasType U Γ (.const view.name levels)
      (view.familyType.instL levels) := by
    exact self.toLayoutWF.familyConst_hasType henv.ordered levels hlevels
      hlevelsLength
  have hstruct : env.HasType U Γ
      (view.structureType levels params) (.sort resultLevel) := by
    simpa [VStructureView.structureType] using
      hparamsSpine₀.hasType_appN hfamily
  have hfieldUnderStruct : env.HasType U
      (view.structureType levels params :: Γ) field.lift
      (.sort code.fieldSort) := by
    have h := hfieldType.weakN henv.ordered
      (Ctx.LiftN.one (A := view.structureType levels params))
    simpa [VExpr.liftN] using h
  have htypeFn : env.HasType U Γ code.typeFn
      (.forallE (view.structureType levels params)
        (.sort code.fieldSort)) := by
    rw [htypeFnShape₀]
    exact hstruct.lam hfieldUnderStruct
  have hfieldSortWF : code.fieldSort.WF U := by
    rw [hcodeSort]
    exact hsortTel.sortWF hΓ hfieldSort
  have hmotiveLevel :
      view.generation.motiveLevel.inst
        (view.projectionLevels code.fieldSort levels) = code.fieldSort := by
    rw [hcodeSort]
    rw [List.getElem?_map] at hfieldSort
    obtain ⟨rawSort, hrawSort, rfl⟩ := Option.map_eq_some_iff.1 hfieldSort
    have hrawSortMem : rawSort ∈ view.fieldSorts :=
      List.mem_iff_getElem?.2 ⟨0, hrawSort⟩
    exact self.motiveLevel_projectionLevels rawSort hrawSortMem levels
  have hfieldsOnTel : env.OnTel U Γ fields := by
    simpa [fields] using hsortTel.toOnTel
  have hfieldsCtx : OnCtx (fields.reverse ++ Γ) (env.IsType U) :=
    hfieldsOnTel.toOnCtx hΓ
  let ihs := view.projectionIHTypes code.fieldSort levels params code.typeFn
  have hihsOnTel : env.OnTel U (fields.reverse ++ Γ) ihs := by
    simpa [fields, ihs] using self.projectionIHTypes_onTel henv.ordered hΓ
      levels hlevels hlevelsLength params hparamsLength
      ⟨resultLevel, hparamsSpine₀⟩ code.fieldSort hfieldSortWF
      hmotiveLevel htypeFn
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
  have hminor := VEnv.HasType.selectFieldMinor_of_weak henv.ordered
    (i := 0) hfieldsOnTel hihsOnTel hcodeLength
      (by simpa [q] using hbodyExpected)
  rw [hminorShape]
  rw [view.projectionMinorType_decompose code.fieldSort levels
    hlevelsLength params code.typeFn]
  rw [self.projectionMinorResult_eq_lift henv.ordered code.fieldSort levels
    hlevelsLength params hparamsLength code.typeFn]
  simpa [fields, ihs, m, q] using hminor

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
    exact self.toLayoutWF.familyConst_hasType henv.ordered levels hlevels
      hlevelsLength
  have hstruct : env.HasType U Γ
      (view.structureType levels params) (.sort resultLevel) := by
    simpa [VStructureView.structureType] using
      hparamsSpine₀.hasType_appN hfamily
  have hidx : idx < (view.projectionCodes levels params).length :=
    (List.getElem?_eq_some_iff.1 hcode).1
  obtain ⟨fieldSort, hfieldSort, hcodeSort, -, -⟩ :=
    view.projectionCodes_get?_program_shape levels params hcode
  have hfamilyClosed : (view.familyType.instL levels).ClosedN 0 := by
    simpa using (self.toLayoutWF.familyType_closed henv.ordered).instL
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
      exact self.toLayoutWF.familyConst_hasType henv.ordered levels hlevels
        hlevelsLength
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
      simpa using (self.toLayoutWF.familyType_closed henv.ordered).instL
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
        (view.projectionMinorType code.fieldSort levels paramsLift
          code.typeFn.lift) := by
      have hcodeLift :
          (view.projectionCodes levels paramsLift)[idx]? =
            some (code.liftN 1 0) := by
        rw [← hcodesLift, List.getElem?_map, hcode]
        rfl
      have h := minors hlimit hΓLift hlevels hlevelsLength
        hparamsLengthLift ⟨resultLevel, hparamsSpineLift⟩ hcodeLift
      simpa [VStructureView.ProjectionCode.liftN] using h
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
    exact self.toLayoutWF.familyConst_hasType henv.ordered levels hlevels
      hlevelsLength
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
  have hfieldSortWF : code.fieldSort.WF U := by
    rw [hcodeSort]
    exact hsortTel.sortWF hΓ hfieldSort
  have hmotiveLevel :
      view.generation.motiveLevel.inst
        (view.projectionLevels code.fieldSort levels) = code.fieldSort := by
    rw [hcodeSort]
    have hfieldSort' := hfieldSort
    rw [List.getElem?_map] at hfieldSort'
    obtain ⟨rawSort, hrawSort, rfl⟩ :=
      Option.map_eq_some_iff.1 hfieldSort'
    have hrawSortMem : rawSort ∈ view.fieldSorts :=
      List.mem_iff_getElem?.2 ⟨limit, hrawSort⟩
    exact self.motiveLevel_projectionLevels rawSort hrawSortMem levels
  let ihs := view.projectionIHTypes code.fieldSort levels params code.typeFn
  have hihsOnTel : env.OnTel U (fields.reverse ++ Γ) ihs := by
    simpa [fields, ihs] using self.projectionIHTypes_onTel henv.ordered hΓ
      levels hlevels hlevelsLength params hparamsLength
      ⟨resultLevel, hparamsSpine₀⟩ code.fieldSort hfieldSortWF
      hmotiveLevel htypeFn

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
    simpa using (self.toLayoutWF.familyType_closed henv.ordered).instL
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
  have hminor := VEnv.HasType.selectFieldMinor_of_weak henv.ordered
    (i := limit) hfieldsOnTel hihsOnTel hidx
      (by simpa [q, m] using hbodyExpected)
  rw [hminorShape]
  rw [view.projectionMinorType_decompose code.fieldSort levels
    hlevelsLength params code.typeFn]
  rw [self.projectionMinorResult_eq_lift henv.ordered code.fieldSort levels
    hlevelsLength params hparamsLength code.typeFn]
  simpa [fields, ihs, m, q] using hminor

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
    exact self.toLayoutWF.familyType_closed henv
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

/-- Every argument retained by a well-typed application spine has a typing
derivation at the spine's ambient context. -/
theorem _root_.Lean4Lean.VEnv.SpineWF.arg_hasType
    {env : VEnv} {U : Nat} {Γ : List VExpr} :
    ∀ {A B : VExpr} {args : List VExpr},
      env.SpineWF U Γ A args B →
      ∀ {arg : VExpr}, arg ∈ args → ∃ T, env.HasType U Γ arg T
  | _, _, _ :: _, .cons harg _, _, .head _ => ⟨_, harg⟩
  | _, _, _ :: _, .cons _ hrest, _, .tail _ hmem =>
      arg_hasType hrest hmem

/-- Recover typing of the unapplied head from a typed iterated application. -/
private theorem VEnv.HasType.appN_head_hasType
    {env : VEnv} (henv : env.Ordered) {U : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ {f : VExpr} {args : List VExpr} {B : VExpr},
      env.HasType U Γ (VExpr.appN f args) B →
        ∃ A, env.HasType U Γ f A
  | _, [], _, h => ⟨_, h⟩
  | f, arg :: args, _, h => by
      obtain ⟨result, happ⟩ :=
        VEnv.HasType.appN_head_hasType henv hΓ
          (f := .app f arg) (args := args) h
      obtain ⟨A, body, hf, _⟩ := happ.app_inv henv hΓ
      exact ⟨.forallE A body, hf⟩

/-- A typed saturated application of a term with an exact pi telescope
recovers the corresponding exact application spine.  Conversion regularity
aligns the domains exposed by application inversion with the named source
telescope. -/
theorem _root_.Lean4Lean.VEnv.HasType.spineWF_of_appN
    {env : VEnv} (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ {binders args : List VExpr} {f body B : VExpr},
      env.HasType U Γ f (VExpr.forallN binders body) →
      env.HasType U Γ (VExpr.appN f args) B →
      args.length = binders.length →
      env.SpineWF U Γ (VExpr.forallN binders body) args
        (VExpr.instRev body args)
  | [], [], _, _, _, _, _, _ => .nil
  | [], _ :: _, _, _, _, _, _, hlen => by simp at hlen
  | _ :: _, [], _, _, _, _, _, hlen => by simp at hlen
  | binder :: binders, arg :: args, f, body, _, hf, happ, hlen => by
      obtain ⟨prefixType, hprefix⟩ :=
        VEnv.HasType.appN_head_hasType henv.ordered hΓ
          (f := .app f arg) (args := args) happ
      obtain ⟨binder', rest', hf', harg'⟩ :=
        hprefix.app_inv henv.ordered hΓ
      have hfunEq := henv.hasType_uniqU hΓ hf hf'
      obtain ⟨⟨domainSort, hdomain⟩, _⟩ :=
        henv.forallE_inv hΓ hfunEq
      have harg : env.HasType U Γ arg binder :=
        hdomain.defeq' harg'
      have hprefixExact := hf.app harg
      have hprefixExact' : env.HasType U Γ (.app f arg)
          (VExpr.forallN (VExpr.instTelN arg binders 0)
            (body.inst arg binders.length)) := by
        simpa [VExpr.instN_forallN] using hprefixExact
      have htailLength : args.length = binders.length := by
        simpa using hlen
      have htail := spineWF_of_appN henv hΓ
        (binders := VExpr.instTelN arg binders 0)
        (args := args) (f := .app f arg)
        (body := body.inst arg binders.length)
        hprefixExact' happ (by
          rw [VExpr.instTelN_length]
          exact htailLength)
      refine .cons harg ?_
      rw [VExpr.instN_forallN]
      simpa [VExpr.instRev, htailLength] using htail

/-- A generated projector computes on the matching generated constructor
once the registered rule's capture spine has been checked.  This is the
exact iota layer; constructor-head and parameter-prefix alignment are kept
outside this theorem. -/
theorem _root_.Lean4Lean.VStructureView.LayoutWF.projector_constructor_exact
    (self : VStructureView.LayoutWF view env)
    (henv : env.ConversionRegular)
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
    (_hfieldsSpine : env.SpineWF U Γ
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
  have hregistered := self.rules _ hruleMem
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
      rhsBody = VExpr.appN (.bvar m)
        (VExpr.bvarRevRange 0 m ++ ihs) := by
    simp [rhsBody, gen, view.constructor_eq]
  let capturedIHs := ihs.map fun expression =>
    VExpr.instRev (expression.instL pLevels)
      (params ++ [code.typeFn, code.minor] ++ fields)
  have hrightShape :
      VExpr.instRev (rhsBody.instL pLevels)
          (params ++ [code.typeFn, code.minor] ++ fields) =
        VExpr.appN code.minor (fields ++ capturedIHs) := by
    rw [hrightBodyShape, VExpr.instL_appN, VExpr.instRev_appN]
    simp only [List.map_append, VExpr.bvarRevRange_map_instL,
      VExpr.instL, List.map_map,
      Function.comp_def]
    rw [hminorCapture, hsegFields]
  rw [hleftShape, hrightShape] at hiotaBodies
  let formalFields := view.specializedFields levels params
  let formalIHs :=
    view.projectionIHTypes code.fieldSort levels params code.typeFn
  let selectorBinders := formalFields ++ formalIHs
  let selectorBody :=
    VExpr.bvar (formalIHs.length + formalFields.length - 1 - idx)
  let allArgs := fields ++ capturedIHs
  have hminorLamShape :
      code.minor = VExpr.lamN selectorBinders selectorBody := by
    rw [hminorShape]
    unfold VExpr.selectFieldMinor
    change
      VExpr.lamN formalFields (VExpr.lamN formalIHs selectorBody) =
        VExpr.lamN (formalFields ++ formalIHs) selectorBody
    exact (VExpr.lamN_append formalFields formalIHs selectorBody).symm
  obtain ⟨_, hminorAny⟩ :=
      VEnv.SpineWF.arg_hasType hcaps (arg := code.minor) (by simp)
  rw [hminorLamShape] at hminorAny
  obtain ⟨hselectorTel, selectorResultType, hselectorBody⟩ :=
    VEnv.HasType.lamN_wf henv.ordered hΓ hminorAny
  have hminorExact : env.HasType U Γ code.minor
      (VExpr.forallN selectorBinders selectorResultType) := by
    rw [hminorLamShape]
    exact VEnv.HasType.lamN hselectorTel hselectorBody
  have hminorAppType := hcollapseR.hasType.2
  rw [hrightShape] at hminorAppType
  have hcapturedIHsLength : capturedIHs.length = formalIHs.length := by
    calc
      capturedIHs.length = ihs.length := by
        simp only [capturedIHs, List.length_map]
      _ = rs.length := by simp only [ihs, List.length_map]
      _ = view.constructor.view.recursive.length := by
        simp only [rs, VInductDecl.NormalizedCtor.recArgsR,
          List.length_map]
      _ = formalIHs.length := by
        symm
        simpa only [formalIHs] using
          view.projectionIHTypes_length code.fieldSort levels params code.typeFn
  have hallArgsLength : allArgs.length = selectorBinders.length := by
    simp only [allArgs, selectorBinders, List.length_append]
    rw [hfieldsLength, hcapturedIHsLength]
  have hminorSpine := VEnv.HasType.spineWF_of_appN henv hΓ
    hminorExact hminorAppType hallArgsLength
  have hminorBetaRaw := VEnv.IsDefEq.appN_lamN henv.ordered
    hselectorTel hselectorBody hminorSpine hallArgsLength
  obtain ⟨hidxFields, hfieldGet⟩ :=
    List.getElem?_eq_some_iff.1 hfield
  have hfieldAll : allArgs[idx]? = some field := by
    rw [show allArgs = fields ++ capturedIHs by rfl,
      List.getElem?_append_left hidxFields, hfield]
  obtain ⟨hidxAll, hfieldGetAll⟩ :=
    List.getElem?_eq_some_iff.1 hfieldAll
  have hidxFormal : idx < formalFields.length := by
    change idx < (view.specializedFields levels params).length
    rw [← hfieldsLength]
    exact hidxFields
  have hselectorBodyLt :
      formalIHs.length + formalFields.length - 1 - idx < allArgs.length := by
    rw [hallArgsLength]
    simp only [selectorBinders, List.length_append]
    omega
  have hfieldInst : VExpr.instRev selectorBody allArgs = field := by
    unfold selectorBody
    rw [VExpr.instRev_bvar_lt allArgs hselectorBodyLt]
    have hposition :
        allArgs.length - 1 -
            (formalIHs.length + formalFields.length - 1 - idx) = idx := by
      rw [hallArgsLength]
      simp only [selectorBinders, List.length_append]
      omega
    simpa only [hposition] using hfieldGetAll
  change VExpr.instRev selectorBody (fields ++ capturedIHs) = field at hfieldInst
  have hminorBeta : env.IsDefEqU U Γ
      (VExpr.appN code.minor (fields ++ capturedIHs)) field := by
    refine ⟨VExpr.instRev selectorResultType allArgs, ?_⟩
    rw [hminorLamShape]
    simpa only [allArgs, hfieldInst] using hminorBetaRaw
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
    exact self.toLayoutWF.familyConst_hasType henv.ordered levels hlevels
      hlevelsLength
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
    simpa using (self.toLayoutWF.familyType_closed henv.ordered).instL
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
      simpa using
        (self.viewWF.toLayoutWF.familyType_closed henv).instL
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
      simpa using
        (self.viewWF.toLayoutWF.familyType_closed henv).instL
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
