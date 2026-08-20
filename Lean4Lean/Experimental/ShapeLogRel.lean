import Lean4Lean.Experimental.SExpr

/-
`Shape.plift` and friends below are written in `Option`-monad `do`/`return` notation, and
the proofs about them `simp` through the exact term that notation elaborates to.
leanprover/lean4#13305 made the new `do` elaborator the default in v4.32.0, which reshapes
those terms. Pin the legacy elaborator here until the proofs are migrated
(digama0/lean4lean#31).
-/
set_option backward.do.legacy true

namespace Lean4Lean
open Lean4Lean

namespace SExpr
variable [Params]

private noncomputable instance : DecidableEq SLevel := fun a b => Classical.propDecidable (a = b)

@[simp] theorem SLevel.succ_ne_zero {l : SLevel} : l.succ ≠ .zero := by
  intro h
  have := congrArg Subtype.val h
  simp [SLevel.succ, SLevel.zero] at this
  have := congrFun this []
  simp [VLevel.eval] at this

@[simp] theorem SLevel.imax_eq_zero {l l' : SLevel} : l.imax l' = .zero ↔ l' = .zero := by
  constructor
  · intro h
    have hv := congrArg Subtype.val h
    simp [SLevel.imax, SLevel.zero] at hv
    apply Subtype.ext; funext v
    have := congrFun hv v
    simp [Lean.Nat.imax, VLevel.eval] at this
    exact Decidable.byContradiction fun h => absurd (this h).2 h
  · intro h
    subst h
    apply Subtype.ext; funext v
    simp [SLevel.imax, SLevel.zero, Lean.Nat.imax, VLevel.eval]

inductive Shape0 : Type where
  | bot : Shape0
  | sort (rel : Bool) : Shape0

inductive ShapeS (Shape : Type) : Type where
  | bot : ShapeS Shape
  | sort (rel : Bool) : ShapeS Shape
  | forallE : Shape → List (Shape × Shape) → ShapeS Shape
  | lam : List (Shape × Shape) → ShapeS Shape
  | ctor : Name → List Shape → ShapeS Shape
  | indTy : ShapeS Shape

@[implicit_reducible] def Shape : Nat → Type
  | 0 => Shape0
  | n + 1 => ShapeS (Shape n)

abbrev ShapeFun (n) := List (Shape n × Shape n)

@[match_pattern] def Shape.bot : ∀ {n}, Shape n
  | 0 => Shape0.bot
  | _+1 => ShapeS.bot

@[match_pattern] def Shape.sort (rel : Bool) : ∀ {n}, Shape n
  | 0 => Shape0.sort rel
  | _+1 => ShapeS.sort rel

abbrev Shape.prop : ∀ {n}, Shape n := .sort false
abbrev Shape.type : ∀ {n}, Shape n := .sort true

def ShapeFun.bot : ShapeFun n := [(.bot, .bot)]

def ShapeFun.Compat (R : α → β → Bool) (f : List (α × α)) (f' : List (β × β)) : Bool :=
  f.all fun (x, y) => f'.all fun (x', y') => R x x' → R y y'

omit [Params] in
theorem ShapeFun.Compat.def : Compat R f f' ↔ ∀ x ∈ f, ∀ y ∈ f', R x.1 y.1 → R x.2 y.2 := by
  simp [ShapeFun.Compat, -decide_implies]

def Shape.Compat : ∀ {n}, Shape n → Shape n → Bool
  | 0, .bot, _ | 0, _, .bot | _+1, .bot, _ | _+1, _, .bot => true
  | 0, .sort r, .sort r' | _+1, .sort r, .sort r' => r = r'
  | _+1, .forallE s f, .forallE s' f' => s.Compat s' && ShapeFun.Compat Compat f f'
  | _+1, .lam f, .lam f' => ShapeFun.Compat Compat f f'
  | _+1, .ctor c l, .ctor c' l' => c = c' && List.Forall₂ (Compat · ·) l l'
  | _+1, .indTy, .indTy => true
  | _, _, _ => false

omit [Params] in
theorem Shape.Compat.comm {n} {s t : Shape n} : s.Compat t = t.Compat s := by
  induction n with | zero => cases s <;> cases t <;> simp [Compat, eq_comm] | succ n ih
  let rec go {f f' : ShapeFun n} : ShapeFun.Compat Compat f f' = ShapeFun.Compat Compat f' f := by
    rw [Bool.eq_iff_iff]; simp [ShapeFun.Compat.def]
    constructor <;> intro H _ _ h1 _ _ h2 h3 <;> exact ih ▸ H _ _ h2 _ _ h1 (ih ▸ h3)
  cases s <;> cases t <;> simp +singlePass [Compat, eq_comm, ih, go]
  · rw [Bool.eq_iff_iff]; simp; intro
    constructor <;> refine fun h => h.flip.imp fun _ _ h => ih ▸ h

omit [Params] in
theorem ShapeFun.Compat.comm {n} {f f' : ShapeFun n} :
    Compat Shape.Compat f f' = Compat Shape.Compat f' f := Shape.Compat.comm.go _ Shape.Compat.comm

omit [Params] in
theorem Shape.Compat.symm {n} {s t : Shape n} : s.Compat t → t.Compat s := (comm ▸ ·)

omit [Params] in
theorem ShapeFun.Compat.symm {n} {f f' : ShapeFun n} :
    Compat Shape.Compat f f' → Compat Shape.Compat f' f := (comm ▸ ·)

omit [Params] in theorem Shape.Compat.bot_l {n} {s : Shape n} : bot.Compat s := by cases n <;> rfl
omit [Params] in theorem Shape.Compat.bot_r {n} {s : Shape n} : s.Compat bot := symm bot_l

omit [Params] in theorem Shape.Compat.sort_sort : Compat (sort r : Shape n) (sort r') ↔ r = r' := by
  cases n <;> simp [Compat]
omit [Params] in theorem Shape.Compat.forallE_forallE {a a' : Shape n} {f f' : ShapeFun n} :
    Compat (n := n+1) (.forallE a f) (.forallE a' f') ↔
    a.Compat a' ∧ ShapeFun.Compat Compat f f' := by simp only [Compat, Bool.and_eq_true]
omit [Params] in theorem Shape.Compat.lam_lam {f f' : ShapeFun n} :
    Compat (n := n+1) (.lam f) (.lam f') ↔ ShapeFun.Compat Compat f f' := by simp only [Compat]
omit [Params] in theorem Shape.Compat.ctor_ctor {l l' : List (Shape n)} :
    Compat (n := n+1) (.ctor c l) (.ctor c' l') ↔ c = c' ∧ l.Forall₂ (Compat · ·) l' := by
  simp [Compat]

def ShapeFun.ble (R : α → α → Bool) (f f' : List (α × α)) : Bool :=
  f.all fun (x, y) => f'.any fun (x', y') => R x' x && R y y'

def Shape.ble : ∀ {n}, Shape n → Shape n → Bool
  | 0, .bot, _ | _+1, .bot, _ => true
  | 0, .sort r, .sort r' | _+1, .sort r, .sort r' => r = r'
  | _+1, .forallE s f, .forallE s' f' => s.ble s' && ShapeFun.ble ble f f'
  | _+1, .lam f, .lam f' => ShapeFun.ble ble f f'
  | _+1, .ctor c l, .ctor c' l' => c == c' && l.Forall₂ (Shape.ble · ·) l'
  | _+1, .indTy, .indTy => true
  | _, _, _ => false

def ShapeFun.LE (s s' : ShapeFun n) : Prop := ShapeFun.ble Shape.ble s s'
def Shape.LE (s s' : Shape n) : Prop := s.ble s'
instance : LE (Shape n) := ⟨Shape.LE⟩
instance : DecidableRel (α := Shape n) (· ≤ ·) := fun x y => inferInstanceAs (Decidable (x.ble y))
instance : DecidableRel (ShapeFun.LE (n := n)) :=
  fun x y => inferInstanceAs (Decidable (ShapeFun.ble _ x y))

omit [Params] in
@[simp] theorem Shape.bot_le : Shape.bot ≤ (s : Shape n) := by cases n <;> rfl

omit [Params] in
theorem ShapeFun.LE.def' {f f' : ShapeFun n} : ShapeFun.LE f f' ↔
    ∀ x ∈ f, ∃ x' ∈ f', x'.1 ≤ x.1 ∧ x.2 ≤ x'.2 := by
  simp [LE, ble]; rfl

omit [Params] in
theorem ShapeFun.LE.def {f f' : ShapeFun n} : ShapeFun.LE f f' ↔
    ∀ x y : Shape n, (x, y) ∈ f → ∃ x' y' : Shape n, (x', y') ∈ f' ∧ x' ≤ x ∧ y ≤ y' := by
  simp [LE, ble]; rfl

omit [Params] in
theorem Shape.LE.def {s s' : Shape (n + 1)} : s ≤ s' ↔
    match s, s' with
    | .bot, _ => True
    | .sort r, .sort r' => r = r' --j ≤ i
    | .forallE s f, .forallE s' f' => s ≤ s' ∧ ShapeFun.LE f f'
    | .lam f, .lam f' => ShapeFun.LE f f'
    | .ctor c f, .ctor c' f' => c = c' ∧ f.Forall₂ Shape.LE f'
    | .indTy, .indTy => True
    | _, _ => False := by
  dsimp only [(· ≤ ·), LE, ShapeFun.LE]
  rw [Shape.ble.eq_def]; cases s <;> cases s' <;> simp
  · intro; rfl

omit [Params] in
theorem Shape.LE.rfl {s : Shape n} : s ≤ s := by
  dsimp [(· ≤ ·), Shape.LE]
  induction n with
  | zero => cases s <;> simp [ble]
  | succ n ih =>
    have ihf {s : List (Shape n × Shape n)} : ShapeFun.ble ble s s := by
      simp only [ShapeFun.ble, List.all_eq_true, List.any_eq_true, Bool.and_eq_true]
      exact fun _ h => ⟨_, h, ih, ih⟩
    cases s <;> simp [ble, ih, ihf]
    · exact .rfl fun _ _ => ih

omit [Params] in
theorem Shape.LE.of_eq {s : Shape n} : s = t → s ≤ t := by rintro ⟨⟩; exact .rfl

omit [Params] in
theorem ShapeFun.LE.rfl {s : ShapeFun n} : s.LE s := by
  simp only [ShapeFun.LE, ShapeFun.ble, List.all_eq_true, List.any_eq_true, Bool.and_eq_true]
  exact fun _ h => ⟨_, h, Shape.LE.rfl, Shape.LE.rfl⟩

omit [Params] in
theorem Shape.le_bot {s : Shape n} : s ≤ .bot ↔ s = .bot :=
  ⟨(by cases n <;> cases s <;> first | rfl | cases ·), (· ▸ LE.rfl)⟩

omit [Params] in
theorem Shape.le_sort {s : Shape n} : s ≤ .sort r ↔ s = .bot ∨ s = .sort r := by
  cases n <;> simp [sort, bot, (· ≤ ·), Shape.LE] <;> cases s <;>
    simp [ble] <;> exact ⟨fun h => h ▸ rfl, fun h => by injection h⟩

omit [Params] in
theorem Shape.sort_le {s : Shape n} : .sort r ≤ s ↔ .sort r = s := by
  cases n <;> simp [sort, (· ≤ ·), Shape.LE] <;> cases s <;> simp [ble, Shape]

omit [Params] in
theorem Shape.le_indTy {s : Shape (n+1)} : s ≤ .indTy ↔ s = .bot ∨ s = .indTy := by
  simp [Shape.bot, (· ≤ ·), Shape.LE]; cases s <;> simp [Shape.ble]

omit [Params] in
theorem Shape.indTy_le {s : Shape (n+1)} : .indTy ≤ s ↔ s = .indTy := by
  simp [Shape.LE.def]; cases s <;> simp

omit [Params] in
theorem Shape.forallE_le {s : Shape (n+1)} :
    .forallE a b ≤ s ↔ ∃ a' b', a ≤ a' ∧ ShapeFun.LE b b' ∧ .forallE a' b' = s := by
  rw [Shape.LE.def]; cases s <;> simp [Shape]

omit [Params] in
@[simp] theorem Shape.forallE_le_forallE :
    (by exact .forallE a b : Shape (n+1)) ≤ .forallE a' b' ↔ a ≤ a' ∧ ShapeFun.LE b b' := by
  refine Shape.forallE_le.trans ⟨?_, fun ⟨h1, h2⟩ => ⟨_, _, h1, h2, rfl⟩⟩
  rintro ⟨_, _, h1, h2, ⟨⟩⟩; exact ⟨h1, h2⟩

omit [Params] in
theorem Shape.lam_le {s : Shape (n+1)} :
    .lam f ≤ s ↔ ∃ f', ShapeFun.LE f f' ∧ .lam f' = s := by
  rw [Shape.LE.def]; cases s <;> simp [Shape]

omit [Params] in
@[simp] theorem Shape.lam_le_lam :
    (by exact .lam f : Shape (n+1)) ≤ .lam f' ↔ ShapeFun.LE f f' :=
  Shape.lam_le.trans ⟨by rintro ⟨_, h, ⟨⟩⟩; exact h, fun h => ⟨_, h, rfl⟩⟩

omit [Params] in
theorem Shape.LE.trans {s t u : Shape n} : s ≤ t → t ≤ u → s ≤ u := by
  dsimp [(· ≤ ·), Shape.LE]
  induction n with
  | zero => cases s <;> cases t <;> simp [ble] <;> cases u <;> simp [ble, *] <;>
      (intro h1 h2; exact h1.trans h2)
  | succ n ih =>
    have ihf {s t u : List (Shape n × Shape n)} :
        ShapeFun.ble ble s t → ShapeFun.ble ble t u → ShapeFun.ble ble s u := by
      simp only [ShapeFun.ble, List.all_eq_true, List.any_eq_true, Bool.and_eq_true]
      rintro h1 h2 x hx; let ⟨_, hy, x1, x2⟩ := h1 _ hx; let ⟨_, hz, y1, y2⟩ := h2 _ hy
      exact ⟨_, hz, ih y1 x1, ih x2 y2⟩
    cases s <;> cases t <;> simp [ble] <;> cases u <;> simp [ble, *] <;> grind [List.Forall₂.trans]

omit [Params] in
theorem ShapeFun.LE.trans {s t u : ShapeFun n} : s.LE t → t.LE u → s.LE u := by
  simp only [ShapeFun.LE, ShapeFun.ble, List.all_eq_true, List.any_eq_true, Bool.and_eq_true]
  rintro h1 h2 x hx; let ⟨_, hy, x1, x2⟩ := h1 _ hx; let ⟨_, hz, y1, y2⟩ := h2 _ hy
  exact ⟨_, hz, Shape.LE.trans y1 x1, Shape.LE.trans x2 y2⟩

omit [Params] in
theorem Shape.Compat.mono_r {n} {s t t' : Shape n}
    (le : t ≤ t') (H : s.Compat t') : s.Compat t := by
  induction n with
  | zero =>
    cases s <;> [simp [Compat]; skip]
    cases t <;> cases t' <;> simp [Compat, (·≤·), Shape.LE, Shape.ble] at H le ⊢
    exact H.trans le.symm
  | succ n ih
  let rec go {s t t' : ShapeFun n}
      (le : t.LE t') (H : ShapeFun.Compat Compat s t') : ShapeFun.Compat Compat s t := by
    simp [ShapeFun.Compat.def, ShapeFun.LE.def] at H le ⊢
    intro _ _ h1 _ _ h2 h3; have ⟨_, _, a1, a2, a3⟩ := le _ _ h2
    exact ih a3 <| H _ _ h1 _ _ a1 <| ih a2 h3
  (cases s with | bot => rfl | _) <;>
    (cases t' with | bot => cases le_bot.1 le; rfl | _) <;>
    simp [Compat] at H <;> (cases t with | bot => rfl | _) <;>
    simp [Shape.LE.def, Compat] at le ⊢
  · exact H.trans le.symm
  · exact ⟨ih le.1 H.1, go le.2 H.2⟩
  · exact go le H
  · exact ⟨H.1.trans le.1.symm, H.2.trans (fun _ _ _ h1 h2 => by exact ih h2 h1) le.2.flip⟩

omit [Params] in
theorem ShapeFun.Compat.mono_r {n} {s t t' : ShapeFun n} :
    t.LE t' → Compat Shape.Compat s t' → Compat Shape.Compat s t :=
  Shape.Compat.mono_r.go _ Shape.Compat.mono_r

omit [Params] in
theorem Shape.Compat.mono {n} {s s' t t' : Shape n}
    (le₁ : s ≤ s') (le₂ : t ≤ t') (H : s'.Compat t') : s.Compat t :=
  mono_r le₂ <| symm <| mono_r le₁ <| symm H

def ShapeFun.lift (lift : α → β) (x : List (α × α)) : List (β × β) :=
  x.map fun (a, b) => (lift a, lift b)

def Shape.lift : ∀ {n} m, Shape n → Shape m
  | 0, _, .sort r | _+1, _, .sort r => .sort r
  | 0, _, .bot | _+1, _, .bot | _, 0, _ => .bot
  | _+1, _+1, .forallE s f => .forallE (lift _ s) <| ShapeFun.lift (lift _) f
  | _+1, _+1, .lam f => .lam <| ShapeFun.lift (lift _) f
  | _+1, _+1, .ctor c l => .ctor c <| l.map (lift _)
  | _+1, _+1, .indTy => .indTy

omit [Params] in
@[simp] theorem Shape.lift_bot : (.bot : Shape n).lift m = .bot := by
  cases n <;> [rfl; cases m <;> rfl]

omit [Params] in
@[simp] theorem ShapeFun.lift_bot :
    ShapeFun.lift (Shape.lift m) (.bot : ShapeFun n) = ShapeFun.bot := by simp [ShapeFun.lift, bot]

omit [Params] in
@[simp] theorem Shape.lift_sort : (.sort r : Shape n).lift m = .sort r := by
  cases n <;> [rfl; cases m <;> rfl]

omit [Params] in theorem Shape.lift_prop : (.prop : Shape n).lift m = .prop := lift_sort
omit [Params] in theorem Shape.lift_type : (.type : Shape n).lift m = .type := lift_sort

omit [Params] in
theorem Shape.lift_self {s : Shape n} : s.lift n = s := by
  have {α} {lift : α → α} (IH : ∀ {s}, lift s = s) {s} : ShapeFun.lift lift s = s := by
    simp [ShapeFun.lift]; apply List.map_id''; simp [IH]
  unfold lift <;> split <;> (try rfl)
  · cases s <;> [rfl; grind]
  · rw [Shape.lift_self, this Shape.lift_self]
  · rw [this Shape.lift_self]
  · rw [List.map_id'' fun _ => Shape.lift_self]

omit [Params] in
theorem ShapeFun.lift_self {s : ShapeFun n} : lift (Shape.lift n) s = s := by
  simp [ShapeFun.lift]; apply List.map_id''; simp [Shape.lift_self]

omit [Params] in
theorem Shape.lift_lift {s : Shape n₁} (le : n₁ ≤ n₂ ∨ n₃ ≤ n₂) :
    (s.lift n₂).lift n₃ = s.lift _ := by
  induction n₁ generalizing n₂ n₃ with
  | zero => cases s <;> simp [lift]
  | succ n₁ ih =>
    cases n₃ with
    | zero =>
      cases n₂ with | zero => rw [lift_self] | succ n₃
      cases s <;> simp [lift]
    | succ n₃ =>
      let n₂ + 1 := n₂; simp at le; replace ih {s} := ih (s := s) le
      have ihf {s : ShapeFun n₁} :
          ShapeFun.lift (lift n₃) (ShapeFun.lift (lift n₂) s) = ShapeFun.lift (lift _) s := by
        simp [ShapeFun.lift, ih]
      cases s <;> simp [lift, ih, ihf]
      · congr 2; ext; exact ih

omit [Params] in
theorem ShapeFun.lift_lift {s : ShapeFun n₁} (le : n₁ ≤ n₂ ∨ n₃ ≤ n₂) :
    lift (Shape.lift n₃) (lift (Shape.lift n₂) s) = lift (Shape.lift _) s := by
  simp [ShapeFun.lift, Shape.lift_lift le]

omit [Params] in
theorem Shape.lift_le_lift {s t : Shape n} (le : n ≤ m) : s.lift m ≤ t.lift m ↔ s ≤ t := by
  dsimp [(· ≤ ·), Shape.LE]; rw [← Bool.eq_iff_iff]
  induction n generalizing m with
  | zero =>
    cases m with | zero => simp [lift_self] | succ m
    cases s <;> cases t <;> simp [lift, ble]
  | succ n ih =>
    let m + 1 := m; replace le := Nat.le_of_succ_le_succ le; replace ih {t' s} := @ih m t' s le
    let rec go {s t : ShapeFun n} :
        ShapeFun.ble ble (ShapeFun.lift (lift m) s) (ShapeFun.lift (lift m) t) =
        ShapeFun.ble ble s t := by
      simp only [ShapeFun.ble, ShapeFun.lift, List.all_map, List.any_map, Function.comp_def, ih]
    cases s <;> cases t <;> simp [ble, lift, go, *]

omit [Params] in
theorem ShapeFun.lift_le_lift {s t : ShapeFun n} (le : n ≤ m) :
    ShapeFun.LE (lift (Shape.lift m) s) (lift (Shape.lift m) t) ↔ ShapeFun.LE s t := by
  dsimp [ShapeFun.LE]; rw [← Bool.eq_iff_iff,
    Shape.lift_le_lift.go _ _ (Bool.eq_iff_iff.2 (Shape.lift_le_lift le))]

omit [Params] in
theorem Shape.lift_le_bot {s : Shape n} (h : n ≤ m) : s.lift m ≤ .bot ↔ s = .bot := by
  rw [← le_bot, ← lift_bot, Shape.lift_le_lift h]

omit [Params] in
theorem Shape.lift_eq_bot {s : Shape n} (h : n ≤ m) : s.lift m = .bot ↔ s = .bot := by
  rw [← le_bot, Shape.lift_le_bot h]

omit [Params] in
theorem Shape.lift_mono {s t : Shape n} : s ≤ t → s.lift m ≤ t.lift m := by
  dsimp [(· ≤ ·), Shape.LE]
  cases n with
  | zero =>
    cases s <;> cases t <;> simp [lift, ble] <;>
      first | exact Shape.bot_le | (intro h; subst h; exact Shape.LE.rfl)
  | succ n =>
    cases m with
    | zero => cases s <;> cases t <;> simp [lift, ble]
    | succ m =>
      let rec go {n m} (ih : ∀ {s t : Shape n}, s ≤ t → s.lift m ≤ t.lift m)
          {s t} : ShapeFun.ble ble s t → ShapeFun.ble ble
            (ShapeFun.lift (lift m) s) (ShapeFun.lift (lift m) t) := by
        simp only [ShapeFun.ble, List.all_eq_true, List.any_eq_true, Bool.and_eq_true,
          ShapeFun.lift, List.any_map, List.all_map, Function.comp_apply]
        exact fun H _ h1 => let ⟨_, h2, h3, h4⟩ := H _ h1; ⟨_, h2, ih h3, ih h4⟩
      have := @Shape.lift_mono n m; dsimp [(· ≤ ·), Shape.LE] at this
      have := @go n m Shape.lift_mono
      cases s <;> cases t <;> simp [ble, lift, *] <;> grind [List.Forall₂.imp]

omit [Params] in
theorem ShapeFun.lift_mono {s t : ShapeFun n} : s.LE t →
    LE (lift (Shape.lift m) s) (lift (Shape.lift _) t) := Shape.lift_mono.go Shape.lift_mono

omit [Params] in
protected theorem Shape.Compat.lift {x y : Shape n} (le : n ≤ m) :
    (x.lift m).Compat (y.lift m) = x.Compat y := by
  induction n generalizing m with
  | zero =>
    cases m with | zero => simp [lift_self] | succ m
    cases x <;> cases y <;> simp [lift, Compat]
  | succ n ih
  let m + 1 := m; replace le := Nat.le_of_succ_le_succ le; replace ih {x y} := @ih m x y le
  let rec go {x y : ShapeFun n} :
      ShapeFun.Compat Compat (ShapeFun.lift (lift m) x) (ShapeFun.lift (lift m) y) =
      ShapeFun.Compat Compat x y := by
    rw [Bool.eq_iff_iff]; simp only [ShapeFun.lift, ShapeFun.Compat.def, List.forall_mem_map, ih]
  cases x <;> cases y <;> simp [Compat, lift, go, *]

omit [Params] in
theorem ShapeFun.Compat.lift {x y : ShapeFun n} (le : n ≤ m) :
    Compat Shape.Compat (lift (Shape.lift m) x) (lift (Shape.lift m) y) =
    Compat Shape.Compat x y := Shape.Compat.lift.go _ _ (Shape.Compat.lift le)

def ShapeFun.plift (lift : α → β × Option β) (x : List (α × α)) :
    List (β × β) × Option (List (β × β)) :=
  (x.filterMap fun (a, b) => (lift a).2.map fun a => (a, (lift b).1),
   x.mapM fun (a, b) => (lift b).2.map fun b => ((lift a).1, b))

def Shape.plift : ∀ {n m}, Shape n → Shape m × Option (Shape m)
  | 0, _, .sort r | _+1, _, .sort r => (.sort r, some (.sort r))
  | 0, _, .bot | _+1, _, .bot => (.bot, some .bot)
  | _+1, 0, _ => (.bot, none)
  | _+1, _+1, .forallE s f =>
    let (s₀, s₁) := s.plift
    let (f₀, f₁) := ShapeFun.plift plift f
    (.forallE s₀ f₀, return .forallE (← s₁) (← f₁))
  | _+1, _+1, .lam f =>
    let (f₀, f₁) := ShapeFun.plift plift f
    (.lam f₀, return .lam (← f₁))
  | _+1, _+1, .ctor c l => (.ctor c (l.map (·.plift.1)), return .ctor c (← l.mapM (·.plift.2)))
  | _+1, _+1, .indTy => (.indTy, some .indTy)

omit [Params] in
theorem Shape.plift_eq_lift (le : n ≤ m) {s : Shape n} :
    s.plift = (s.lift m, some (s.lift m)) := by
  let rec go {n m} (IH : n ≤ m → ∀ {s : Shape n}, s.plift = (s.lift m, some (s.lift m)))
      (le : n ≤ m) {s : ShapeFun n} :
      ShapeFun.plift plift s = (ShapeFun.lift (lift m) s, some (ShapeFun.lift (lift m) s)) := by
    simp only [ShapeFun.plift, ShapeFun.lift, IH le]; congr 1
    · rw [← List.filterMap_eq_map]; rfl
    · rw [List.mapM_eq_some, List.forall₂_map_right_iff]
      exact .rfl fun _ _ => rfl
  unfold plift; split <;> simp [lift] at le ⊢ <;> simp [plift_eq_lift le, go plift_eq_lift le]
  · exact ⟨_, List.mapM_pure, rfl⟩

omit [Params] in
theorem ShapeFun.plift_eq_lift (le : n ≤ m) {s : ShapeFun n} :
    plift Shape.plift s = (lift (Shape.lift m) s, some (lift (Shape.lift m) s)) :=
  Shape.plift_eq_lift.go Shape.plift_eq_lift le

omit [Params] in
theorem Shape.plift_lift (le : n ≤ m) {s : Shape n} :
    (s.lift m).plift = (s, some s) := by
  let rec go {n m} (IH : n ≤ m → ∀ {s : Shape n}, (s.lift m).plift = (s, some s))
      (le : n ≤ m) {s : ShapeFun n} :
      ShapeFun.plift plift (ShapeFun.lift (lift m) s) = (s, some s) := by
    simp only [ShapeFun.plift, ShapeFun.lift, List.filterMap_map, List.mapM_map]; congr 1
    · refine .trans ?_ List.filterMap_some; congr 1; funext (a, b); simp [IH le]
    · rw [List.mapM_eq_some]; refine .rfl fun (a, b) _ => by simp [IH le]
  unfold lift; split <;> (try cases m) <;> try simp [plift, sort, bot] at le ⊢
  · cases le; cases s <;> grind
  · simp [plift_lift le, go plift_lift le]
  · simp [go plift_lift le]
  · simp [Function.comp_def, plift_lift le]
    exact ⟨_, List.mapM_pure, List.map_id _ ▸ rfl⟩

omit [Params] in
@[simp] theorem Shape.bot_plift : (bot (n := n)).plift (m := m) = (bot, some bot) := by
  cases n <;> simp [bot, plift]

omit [Params] in
theorem List.mapM_mapM_option (f : α → Option β) (g : β → Option γ) :
    (List.mapM f l).bind (List.mapM g) = List.mapM (f · |>.bind g) l := by
  induction l with simp [Option.bind_assoc] | cons a l ih
  congr 1; ext1; rw [Option.bind_comm]; congr 1; ext1; simp [← ih, Option.bind_assoc]

omit [Params] in
theorem Shape.plift_plift (le : n₁ ≤ n₂ ∨ n₃ ≤ n₂) {s : Shape n₁} :
    ((s.plift.1 : Shape n₂).plift.1 : Shape n₃) = s.plift.1 ∧
    (s.plift.2 : Option (Shape n₃)) = (s.plift.2 : Option (Shape n₂)).bind (·.plift.2) := by
  suffices ∀ {n₁ n₂ n₃}, n₂ ≤ n₁ → n₃ ≤ n₂ → ∀ {s : Shape n₁},
      ((s.plift.1 : Shape n₂).plift.1 : Shape n₃) = s.plift.1 ∧
      (s.plift.2 : Option (Shape n₃)) = (s.plift.2 : Option (Shape n₂)).bind (·.plift.2) by
    obtain le | le := le
    · simp [plift_eq_lift le]
      obtain h1 | h1 := Nat.le_total n₂ n₃
      · simp [plift_eq_lift h1, plift_eq_lift (Nat.le_trans le h1), lift_lift (.inl le)]
      obtain h2 | h2 := Nat.le_total n₁ n₃
      · rw [← lift_lift (.inl h2), plift_lift h1, plift_eq_lift h2]; exact ⟨rfl, rfl⟩
      · rw [← (this le h2).1, (this le h2).2, plift_lift le]; exact ⟨rfl, rfl⟩
    · obtain h1 | h1 := Nat.le_total n₂ n₁
      · rw [(this h1 le).1, (this h1 le).2]; exact ⟨rfl, rfl⟩
      simp [plift_eq_lift h1]
      obtain h2 | h2 := Nat.le_total n₁ n₃
      · rw [← lift_lift (.inl h2), plift_lift le, plift_eq_lift h2]; exact ⟨rfl, rfl⟩
      · rw [← (this h1 h2).1, (this h1 h2).2, plift_lift h1]; exact ⟨rfl, rfl⟩
  intro n₁ n₂ n₃ h1 h2 s
  induction n₁ generalizing n₂ n₃ with
  | zero => cases h1; simp [plift_eq_lift (Nat.le_refl _), lift_self] | succ n₁ ih
  cases n₂ with | zero => cases h2; simp [plift_eq_lift (Nat.le_refl _), lift_self] | succ n₂
  cases n₃ with
  | zero =>
    cases s with simp [plift]
    | forallE s f => cases s.plift.2 <;> simp; cases (ShapeFun.plift plift f).2 <;> simp [plift]
    | lam f => cases (ShapeFun.plift plift f).2 <;> simp [plift]
    | ctor _ l => cases eq: l.mapM (·.plift (m := n₂) |>.2) <;> simp [plift]
  | succ n₃
  simp at h1 h2; replace ih {s} := ih (s := s) h1 h2
  let rec go {s : ShapeFun n₁} :
      (ShapeFun.plift (plift (m := n₃)) (ShapeFun.plift (plift (m := n₂)) s).1).1 =
      (ShapeFun.plift plift s).1 ∧
      ((ShapeFun.plift plift s).2 : Option (ShapeFun n₃)) =
      ((ShapeFun.plift plift s).2 : Option (ShapeFun n₂)).bind (ShapeFun.plift plift · |>.2) := by
    simp [ShapeFun.plift]; constructor
    · rw [List.filterMap_filterMap]; congr 1; ext1 ⟨x, y⟩; dsimp
      simp [Option.bind_map, Function.comp_def]
      have := @ih x; revert this
      cases (x.plift.2 : Option (Shape n₂)) <;> simp +contextual [ih.1]
    · rw [List.mapM_mapM_option]; congr 1; ext1
      simp [Option.map_eq_bind, Option.bind_assoc, Function.comp_def, ih]
  cases s with simp [plift, ih, go, Function.comp_def, Option.bind_assoc]
  | forallE => congr 1; ext; rw [Option.bind_comm]
  | ctor _ l =>
    rw [← Option.bind_assoc]; congr 1
    induction l with simp | cons a l ihl
    simp [Option.bind_assoc, ihl]; congr 1; ext1; rw [Option.bind_comm]

omit [Params] in
theorem ShapeFun.plift_plift (le : n₁ ≤ n₂ ∨ n₃ ≤ n₂) {s : ShapeFun n₁} :
    (plift (Shape.plift (m := n₃)) (plift (Shape.plift (m := n₂)) s).1).1 =
    (plift Shape.plift s).1 ∧
    ((plift Shape.plift s).2 : Option (ShapeFun n₃)) =
    ((plift Shape.plift s).2 : Option (ShapeFun n₂)).bind (plift Shape.plift · |>.2) :=
  Shape.plift_plift.go _ _ _ (Shape.plift_plift le)

omit [Params] in
theorem Shape.plift_thm (le : n ≤ m) {s : Shape m} {t : Shape n} :
    (t.lift m ≤ s ↔ t ≤ (s.plift (m := n)).1) ∧
    (s ≤ t.lift m ↔ ∃ z, (s.plift (m := n)).2 = some z ∧ z ≤ t) := by
  let rec go {n m}
      (IH : n ≤ m → ∀ {s : Shape m} {t : Shape n},
        (t.lift m ≤ s ↔ t ≤ s.plift.1) ∧ (s ≤ t.lift m ↔ ∃ z, s.plift.2 = some z ∧ z ≤ t))
      (le : n ≤ m) {s : ShapeFun m} {t : ShapeFun n} :
      (ShapeFun.LE (ShapeFun.lift (lift _) t) s ↔ ShapeFun.LE t (ShapeFun.plift plift s).1) ∧
      (ShapeFun.LE s (ShapeFun.lift (lift _) t) ↔
        ∃ z, (ShapeFun.plift plift s).2 = some z ∧ ShapeFun.LE z t) := by
    simp [ShapeFun.LE, ShapeFun.ble, ShapeFun.lift, ShapeFun.plift, List.mapM_eq_some,
      -List.any_filterMap, -Prod.forall]
    refine ⟨⟨fun H (a, b) h => ?_, fun H (a, b) h => ?_⟩,
      ⟨fun H => ?_, fun ⟨l, hl, hl2⟩ (a, b) h => ?_⟩⟩
    · obtain ⟨a₁, b₁, h1, h2, h3⟩ := H _ h
      have ⟨z, hz, hz2⟩ := (IH le).2.1 h2
      exact ⟨_, _, ⟨_, _, h1, _, hz, rfl, rfl⟩, hz2, (IH le).1.1 h3⟩
    · obtain ⟨_, _, ⟨_, _, h1, _, h2, rfl, rfl⟩, h3, h4⟩ := H _ h
      exact ⟨_, _, h1, (IH le).2.2 ⟨_, h2, h3⟩, (IH le).1.2 h4⟩
    · induction s with | nil => exact ⟨[], .nil, nofun⟩ | cons p s ih
      simp only [List.mem_cons, or_imp, forall_and, forall_eq] at H
      have ⟨⟨a', b', h1, h2, h3⟩, H⟩ := H
      have ⟨l, hl, hl2⟩ := ih H
      have ⟨z, hz, hz2⟩ := (IH le).2.1 h3
      refine ⟨_::l, .cons ⟨_, hz, rfl⟩ hl, ?_⟩
      exact List.forall_mem_cons.2 ⟨⟨_, _, h1, (IH le).1.1 h2, hz2⟩, hl2⟩
    · obtain ⟨_, h1, _, h2, rfl⟩ := hl.forall_exists_l _ h
      have ⟨_, _, h3, h4, h5⟩ := hl2 _ h1
      exact ⟨_, _, h3, (IH le).1.2 h4, (IH le).2.2 ⟨_, h2, h5⟩⟩
  unfold plift; split
    <;> (try (first | cases Nat.le_zero.1 le | cases n); cases t)
    <;> (try · simp [lift, sort, bot, (· ≤ ·), LE, ble])
    <;> (try · cases t <;> simp [lift, sort, bot, Shape.LE.def])
  · rename_i s _ _; cases s with
    | bot | sort => grind
    | _ => cases t <;> simp [lift, sort, bot, (· ≤ ·), LE, ble]
  all_goals have le := Nat.le_of_succ_le_succ le
  · cases t with simp [lift, sort, bot, Shape.LE.def]
    | forallE => ?_ | _ => intros; subst_vars; simp
    simp [Shape.plift_thm le,
      go Shape.plift_thm le]; grind
  · cases t with simp [lift, sort, bot, Shape.LE.def]
    | lam => ?_ | _ => intros; subst_vars; simp
    simp [go Shape.plift_thm le]; grind
  · cases t with simp [lift, sort, bot, Shape.LE.def, List.mapM_eq_some]
    | ctor => ?_ | _ => intros; subst_vars; simp
    refine ⟨fun _ => ?_, ?_, ?_⟩
    · apply Iff.of_eq; congr; funext a b
      exact propext (Shape.plift_thm le).1
    · rintro ⟨rfl, h⟩; rename_i c l _ l'
      suffices ∃ z, l.Forall₂ (·.plift.2 = some ·) z ∧ z.Forall₂ LE l' from
        have ⟨z, h1, h2⟩ := this; ⟨_, ⟨_, h1, rfl⟩, rfl, h2⟩
      induction h with | nil => exact ⟨_, .nil, .nil⟩ | cons h _ ih
      have ⟨a, a1, a2⟩ := (Shape.plift_thm le).2.1 h; have ⟨z, b1, b2⟩ := ih
      exact ⟨_, .cons a1 b1, .cons a2 b2⟩
    · rintro ⟨z, ⟨a, h1, rfl⟩, h2, h3⟩; refine ⟨h2, h1.trans (fun _ _ _ h1 h3 => ?_) h3⟩
      exact (Shape.plift_thm le).2.2 ⟨_, h1, h3⟩

omit [Params] in
theorem Shape.le_plift (le : n ≤ m) {s : Shape m} {t : Shape n} :
    t ≤ s.plift.1 ↔ t.lift m ≤ s := (Shape.plift_thm le).1.symm

omit [Params] in
theorem Shape.plift_le (le : n ≤ m) {s : Shape m} {t : Shape n} :
    (∃ z, s.plift.2 = some z ∧ z ≤ t) ↔ s ≤ t.lift m := (Shape.plift_thm le).2.symm

omit [Params] in
theorem ShapeFun.le_plift (le : n ≤ m) {s : ShapeFun m} {t : ShapeFun n} :
    LE t (plift Shape.plift s).1 ↔ LE (lift (Shape.lift m) t) s :=
  (Shape.plift_thm.go Shape.plift_thm le).1.symm

omit [Params] in
theorem ShapeFun.plift_le (le : n ≤ m) {s : ShapeFun m} {t : ShapeFun n} :
    (∃ z, (plift Shape.plift s).2 = some z ∧ LE z t) ↔ LE s (lift (Shape.lift m) t) :=
  (Shape.plift_thm.go Shape.plift_thm le).2.symm

omit [Params] in
theorem Shape.plift_mono {s t : Shape m} (H : s ≤ t) : (s.plift (m := n)).1 ≤ t.plift.1 := by
  obtain le | le := Nat.le_total m n
  · rw [Shape.plift_eq_lift le, Shape.plift_eq_lift le]; exact Shape.lift_mono H
  · exact (Shape.le_plift le).2 (.trans ((Shape.le_plift le).1 .rfl) H)

omit [Params] in
protected theorem Shape.Compat.plift {x y : Shape n} :
    (x.Compat y → (x.plift.1 : Shape m).Compat y.plift.1) ∧
    ∀ {x' y' : Shape m}, x.plift.2 = some x' → y.plift.2 = some y' → x'.Compat y' → x.Compat y := by
  obtain le | le := Nat.le_total n m
  · simp [plift_eq_lift le, Compat.lift le]
  refine ⟨fun h => ?_, fun h1 h2 h => ?_⟩
  · rw [← Compat.lift le]
    exact Compat.mono ((Shape.le_plift le).1 .rfl) ((Shape.le_plift le).1 .rfl) h
  · apply Compat.mono ((Shape.plift_le le).1 ⟨_, h1, .rfl⟩) ((Shape.plift_le le).1 ⟨_, h2, .rfl⟩)
    rwa [Compat.lift le]

def ShapeFun.olift (lift : α → Option β) (x : List (α × α)) : Option (List (β × β)) :=
  x.mapM fun (a, b) => return (← lift a, ← lift b)

def Shape.olift : ∀ {n m}, Shape n → Option (Shape m)
  | 0, _, .sort r | _+1, _, .sort r => some (.sort r)
  | 0, _, .bot | _+1, _, .bot => some .bot
  | _+1, 0, _ => none
  | _+1, _+1, .forallE s f => return .forallE (← s.olift) (← ShapeFun.olift olift f)
  | _+1, _+1, .lam f => return .lam (← ShapeFun.olift olift f)
  | _+1, _+1, .ctor c l => return .ctor c (← l.mapM (·.olift))
  | _+1, _+1, .indTy => some .indTy

omit [Params] in
theorem Shape.olift_eq_lift (le : n ≤ m) {s : Shape n} :
    s.olift = some (s.lift m) := by
  let rec go {n m} (IH : n ≤ m → ∀ {s : Shape n}, s.olift = some (s.lift m))
      (le : n ≤ m) {s : ShapeFun n} :
      ShapeFun.olift olift s = some (ShapeFun.lift (lift m) s) := by
    simp only [ShapeFun.olift, ShapeFun.lift, IH le]
    rw [List.mapM_eq_some, List.forall₂_map_right_iff]
    exact .rfl fun _ _ => rfl
  unfold olift; split <;> simp [lift] at le ⊢ <;> simp [olift_eq_lift le, go olift_eq_lift le]
  · exact ⟨_, List.mapM_pure, rfl⟩

omit [Params] in
theorem ShapeFun.olift_eq_lift (le : n ≤ m) {s : ShapeFun n} :
    olift Shape.olift s = some (lift (Shape.lift m) s) :=
  Shape.olift_eq_lift.go Shape.olift_eq_lift le

omit [Params] in
theorem Shape.olift_thm (le : n ≤ m) {s : Shape m} {t : Shape n} :
    s.olift (m := n) = some t ↔ s = t.lift m := by
  let rec go {n m}
      (IH : n ≤ m → ∀ {s : Shape m} {t : Shape n}, s.olift (m := n) = some t ↔ s = t.lift m)
      (le : n ≤ m) {s : ShapeFun m} {t : ShapeFun n} :
      ShapeFun.olift olift s = some t ↔ s = ShapeFun.lift (lift m) t := by
    simp [ShapeFun.lift, ShapeFun.olift, List.mapM_eq_some]
    rw [← List.forall₂_eq, List.forall₂_map_right_iff]
    apply iff_of_eq; congr; ext ⟨a, a'⟩ ⟨b, b'⟩; simp [IH le]
  unfold olift; split
    <;> (try first | cases Nat.le_zero.1 le | cases n)
    <;> cases t <;> simp [lift, bot, sort]
  iterate 4 · grind
  all_goals have le := Nat.le_of_succ_le_succ le
  · simp [olift_thm le, go olift_thm le]; grind
  · simp [go olift_thm le]; grind
  · simp [List.mapM_eq_some, olift_thm le]
    conv => rhs; apply ShapeS.ctor.injEq
    rw [← List.forall₂_eq, List.forall₂_map_right_iff]; grind

omit [Params] in
theorem ShapeFun.olift_thm (le : n ≤ m) {s : ShapeFun m} {t : ShapeFun n} :
    olift Shape.olift s = some t ↔ s = lift (Shape.lift m) t :=
  Shape.olift_thm.go Shape.olift_thm le

omit [Params] in
theorem Shape.lift_inj (le : n ≤ m) {s t : Shape n} : s.lift m = t.lift m ↔ s = t := by
  refine ⟨fun H => ?_, (· ▸ rfl)⟩
  cases ((Shape.olift_thm le).2 H).symm.trans <| (Shape.olift_thm le).2 rfl; rfl

omit [Params] in
theorem ShapeFun.lift_inj (le : n ≤ m) {s t : ShapeFun n} :
    lift (Shape.lift m) s = lift (Shape.lift m) t ↔ s = t := by
  refine ⟨fun H => ?_, (· ▸ rfl)⟩
  cases ((ShapeFun.olift_thm le).2 H).symm.trans <| (ShapeFun.olift_thm le).2 rfl; rfl

omit [Params] in
@[simp] theorem Shape.olift_bot : Shape.olift (n := n) (m := m) .bot = some .bot := by
  cases n <;> cases m <;> rfl

omit [Params] in
@[simp] theorem ShapeFun.olift_bot :
    olift (Shape.olift (n := n) (m := m)) ShapeFun.bot = some ShapeFun.bot := by
  simp [bot, olift]

omit [Params] in
@[simp] theorem Shape.olift_sort : Shape.olift (n := n) (m := m) (.sort r) = some (.sort r) := by
  cases n <;> cases m <;> rfl

def ShapeFun.maxBelow (s : ShapeFun n) : Shape n × Shape n :=
  (s.find? fun (x, _) => s.all fun (x', _) => x' ≤ x).getD (.bot, .bot)

def ShapeFun.trunc (s : ShapeFun n) (a : Shape n) : ShapeFun n := s.filter (·.1 ≤ a)
def ShapeFun.app (s : ShapeFun n) (a : Shape n) : Shape n := maxBelow (s.trunc a) |>.2

omit [Params] in
theorem ShapeFun.lift_trunc (le : n ≤ m) :
    lift (Shape.lift m) (trunc f a : ShapeFun n) = trunc (lift (Shape.lift m) f) (a.lift m) := by
  simp [trunc, lift, List.filter_map]; congr 2; ext x; simp [Shape.lift_le_lift le]

omit [Params] in
theorem ShapeFun.lift_maxBelow {f : ShapeFun n} (le : n ≤ m) :
    (maxBelow f).1.lift m = (maxBelow (lift (Shape.lift m) f)).1 ∧
    (maxBelow f).2.lift m = (maxBelow (lift (Shape.lift m) f)).2 := by
  refine let F x := (x.1.lift m, x.2.lift m)
    have : F (maxBelow f) = maxBelow (lift (Shape.lift m) f) := ?_
    ⟨congrArg (·.1) this, congrArg (·.2) this⟩
  simp [maxBelow, lift]
  generalize eq₁ : List.find? .. = r, eq₂ : List.find? .. = r'
  suffices r = r' by subst this; cases r <;> simp [F]
  subst eq₁ eq₂; congr 1; ext x; simp; congr 1; ext y; simp [Shape.lift_le_lift le]

omit [Params] in
@[simp] theorem ShapeFun.lift_app (le : n ≤ m) :
    (app f a : Shape n).lift m = app (lift (Shape.lift m) f) (a.lift m) := by
  simp [app, lift_trunc le, lift_maxBelow le]

def ShapeFun.join (join : Shape n → Shape n → Shape n) (f f' : ShapeFun n) : ShapeFun n :=
  f.foldl (init := []) fun l x => f'.foldl (init := l) fun l y =>
  if x.1.Compat y.1 then let j := join x.1 y.1; (j, join (f.app j) (f'.app j)) :: l else l

omit [Params] in
theorem ShapeFun.mem_join {join} {f f' : ShapeFun n} {a} :
    a ∈ ShapeFun.join join f f' ↔ ∃ x ∈ f, ∃ y ∈ f', x.1.Compat y.1 ∧
      let j := join x.1 y.1; a = (j, join (f.app j) (f'.app j)) := by
  refine let F x := _; let G x y := _
    (?_ : a ∈ f.foldl (fun l x => f'.foldl (F x) l) [] ↔ (∃ x ∈ f, ∃ y ∈ f', G x y) ∨ a ∈ [])
    |>.trans (or_iff_left (by simp))
  generalize f = f₁, f' = f₂, [] = l
  induction f₁ generalizing l with simp [-Prod.exists, or_assoc, *] | cons _ f₁ ih
  refine .trans (or_congr_right ?_) or_left_comm; clear ih
  induction f₂ generalizing l <;> simp [-Prod.exists, or_assoc, *]
  refine .trans (or_congr_right ?_) or_left_comm
  unfold F G; split <;> rename_i h <;> simp [h]

def Shape.join : ∀ {n}, Shape n → Shape n → Shape n
  | 0, s, .bot | 0, .bot, s | _+1, .bot, s | _+1, s, .bot => s
  | 0, .sort r, .sort r' | _+1, .sort r, .sort r' => if r = r' then .sort r else .bot
  | _+1, .forallE s f, .forallE s' f' => .forallE (join s s') (ShapeFun.join join f f')
  | _+1, .lam f, .lam f' => .lam (ShapeFun.join join f f')
  | _+1, .ctor c l, .ctor c' l' => if c = c' then .ctor c (l.zipWith join l') else .bot
  | _+1, .indTy, .indTy => .indTy
  | _+1, _, _ => .bot

omit [Params] in
theorem Shape.lift_join {x y : Shape n} (le : n ≤ m) :
    (x.join y).lift m = (x.lift m).join (y.lift m) := by
  induction n generalizing m with
  | zero =>
    cases m with | zero => simp [lift_self] | succ m
    cases x <;> cases y <;> simp [lift, join, sort]; split <;> simp [lift, sort]
  | succ n ih
  let m + 1 := m; replace le := Nat.le_of_succ_le_succ le; replace ih {x y} := @ih m x y le
  let rec go {x y : ShapeFun n} :
      ShapeFun.lift (lift m) (ShapeFun.join join x y) =
      ShapeFun.join join (ShapeFun.lift (lift m) x) (ShapeFun.lift (lift m) y) := by
    refine
      let G _ := _; let F l x := List.foldl (G x) l y
      let G' _ := _; let F' l x := List.foldl (G' x) l (ShapeFun.lift (lift m) y)
      have (r:_) : ShapeFun.lift (lift m) (x.foldl F r) =
        (ShapeFun.lift (lift m) x).foldl F' (r.map fun x => (lift m x.1, lift m x.2)) := ?_
      this []
    simp [ShapeFun.lift]; generalize x = x'; induction x' generalizing r <;> simp [*]; congr 1
    unfold F F'
    simp [ShapeFun.lift]; generalize y = y'; induction y' generalizing r <;> simp [*]; congr 1
    simp [G, G', Compat.lift le]; split <;> simp [ih, ShapeFun.lift_app le]
  cases x with cases y <;> simp [join, lift, go, sort, ih]
  | sort => split <;> simp [lift, sort]
  | ctor => split <;> simp [lift, ih]

omit [Params] in
theorem Shape.bot_join {x : Shape n} : bot.join x = x := by cases n <;> cases x <;> rfl
omit [Params] in
theorem Shape.join_bot {x : Shape n} : x.join bot = x := by cases n <;> cases x <;> rfl
omit [Params] in
@[simp] theorem Shape.sort_join_sort :
    join (.sort r : Shape n) (.sort r') = if r = r' then .sort r else .bot := by cases n <;> rfl

omit [Params] in
theorem ShapeFun.lift_join {x y : ShapeFun n} (le : n ≤ m) :
    lift (Shape.lift m) (join Shape.join x y) =
    join Shape.join (lift (Shape.lift m) x) (lift (Shape.lift m) y) :=
  Shape.lift_join.go _ _ le (Shape.lift_join le)

def Shape.lam' (s : ShapeFun n) : Shape (n + 1) :=
  if s.all (·.2 ≤ .bot) then .bot else .lam s

def IsStruct [Params] (n : Name) : Bool := Params.classify n matches some (.etaCtor ..)

def Shape.ctor' (c : Name) (l : List (Shape n)) : Shape (n + 1) :=
  if IsStruct c ∧ l.all (· ≤ .bot) then .bot else .ctor c l

def Shape.trim : ∀ {n}, Shape n → Shape n
  | 0, s => s
  | _+1, .bot => .bot
  | _+1, .sort r => .sort r
  | _+1, .forallE s f => .forallE s.trim (f.map fun x => (x.1.trim, x.2.trim))
  | _+1, .lam f => .lam' (f.map fun x => (x.1.trim, x.2.trim))
  | _+1, .ctor c l => .ctor' c (l.map trim)
  | _+1, .indTy => .indTy

def ShapeFun.WF (WF : Shape n → Prop) (f : ShapeFun n) : Prop :=
  ((∃ y, (.bot, y) ∈ f) ∧ ∀ x ∈ f, ∀ y ∈ f,
    (x.1.Compat y.1 → ∃ z ∈ f, x.1.join y.1 ≤ z.1 ∧ z.1 ≤ x.1.join y.1) ∧
    (x.1 ≤ y.1 → x.2 ≤ y.2)) ∧
  ∀ x ∈ f, WF x.1 ∧ WF x.2

def ShapeFun.NonZero (f : ShapeFun n) := ∃ x ∈ f, ¬x.2 ≤ .bot
def Shape.ListNonZero (l : List (Shape n)) := ∃ x ∈ l, ¬x ≤ .bot

instance {f : ShapeFun n} : Decidable f.NonZero :=
  inferInstanceAs (Decidable (∃ x ∈ f, ¬x.2 ≤ .bot))
instance {l : List (Shape n)} : Decidable (Shape.ListNonZero l) :=
  inferInstanceAs (Decidable (∃ x ∈ l, ¬x ≤ .bot))

omit [Params] in
theorem ShapeFun.NonZero.mono {f f' : ShapeFun n} (le : f.LE f') : NonZero f → NonZero f'
  | ⟨_, h1, h2⟩ => have ⟨_, _, a1, _, a2⟩ := ShapeFun.LE.def.1 le _ _ h1; ⟨_, a1, mt a2.trans h2⟩

omit [Params] in
theorem Shape.ListNonZero.mono {l l' : List (Shape n)}
    (le : l.Forall₂ (· ≤ ·) l') : ListNonZero l → ListNonZero l'
  | ⟨_, h1, h2⟩ => have ⟨_, a1, a2⟩ := le.forall_exists_l _ h1; ⟨_, a1, mt a2.trans h2⟩

def Shape.WF : ∀ {n}, Shape n → Prop
  | 0, _ | _+1, .bot | _+1, .sort .. => True
  | _+1, .forallE s f => s.WF ∧ ShapeFun.WF WF f
  | _+1, .lam f => ShapeFun.WF WF f ∧ ShapeFun.NonZero f
  | _+1, .ctor n l => (∀ x ∈ l, WF x) ∧ (IsStruct n → ListNonZero l)
  | _+1, .indTy => True

omit [Params] in
theorem ShapeFun.NonZero.lift_iff {n m} {x : ShapeFun n} (le : n ≤ m) :
    NonZero (lift (Shape.lift m) x) ↔ NonZero (n := n) x := by
  simp [NonZero, lift]
  refine ⟨fun ⟨_, _, ⟨_, _, h1, rfl, rfl⟩, h2⟩ => ?_, fun ⟨_, _, h1, h2⟩ => ?_⟩
  · exact ⟨_, _, h1, mt ((Shape.lift_le_bot le).2 ∘ Shape.le_bot.1) h2⟩
  · exact ⟨_, _, ⟨_, _, h1, rfl, rfl⟩, mt (Shape.le_bot.2 ∘ (Shape.lift_le_bot le).1) h2⟩

omit [Params] in
theorem Shape.ListNonZero.lift_iff {n m} {x : List (Shape n)} (le : n ≤ m) :
    ListNonZero (x.map (lift m)) ↔ ListNonZero (n := n) x := by
  simp [ListNonZero]
  constructor
  · exact fun ⟨_, ⟨_, h1, rfl⟩, h2⟩ => ⟨_, h1, mt ((Shape.lift_le_bot le).2 ∘ Shape.le_bot.1) h2⟩
  · exact fun ⟨_, h1, h2⟩ => ⟨_, ⟨_, h1, rfl⟩, mt (Shape.le_bot.2 ∘ (Shape.lift_le_bot le).1) h2⟩

theorem Shape.WF.lift_iff (le : n ≤ m) : WF (x.lift m) ↔ WF (n := n) x := by
  induction n generalizing m with | zero => cases m <;> cases x <;> trivial | succ n ih
  let m + 1 := m; replace le := Nat.le_of_succ_le_succ le; replace ih {x} := @ih m x le
  let rec go {x : ShapeFun n} : ShapeFun.WF WF (ShapeFun.lift (lift m) x) ↔ ShapeFun.WF WF x := by
    simp only [ShapeFun.WF, ShapeFun.lift, List.mem_map, Prod.mk.injEq,
      lift_eq_bot le, Prod.exists, exists_and_right, forall_exists_index, and_imp, Prod.forall]
    constructor
    · intro ⟨⟨⟨_, _, _, a1, rfl, rfl⟩, a2⟩, a3⟩; refine ⟨⟨⟨_, a1⟩, ?_⟩, fun _ _ h1 => ?_⟩
      · intro _ _ h1 _ _ h2; have := a2 _ _ _ _ h1 rfl rfl _ _ _ _ h2 rfl rfl
        simp [lift_le_lift le, Compat.lift le, ← lift_join le] at this
        refine ⟨fun h => ?_, this.2⟩
        let ⟨_, ⟨_, _, _, b1, rfl, rfl⟩, b2⟩ := this.1 h
        simp only [lift_le_lift le] at b2; exact ⟨_, ⟨_, b1⟩, b2⟩
      · simpa only [ih] using a3 _ _ _ _ h1 rfl rfl
    · intro ⟨⟨⟨_, a1⟩, a2⟩, a3⟩; refine ⟨⟨?_, ?_⟩, ?_⟩
      · exact ⟨_, _, _, a1, rfl, rfl⟩
      · intro _ _ _ _ h1 rfl rfl _ _ _ _ h2 rfl rfl; have := a2 _ _ h1 _ _ h2
        simp [lift_le_lift le, Compat.lift le, ← lift_join le]
        refine ⟨fun h => ?_, this.2⟩
        let ⟨_, ⟨_, b1⟩, b2⟩ := this.1 h
        refine ⟨_, ⟨_, _, _, b1, rfl, rfl⟩, ?_⟩; simpa only [lift_le_lift le] using b2
      · intro _ _ _ _ h1 rfl rfl; simpa only [ih] using a3 _ _ h1
  cases x with simp [lift, WF, go, *]
  | lam => exact fun _ => ShapeFun.NonZero.lift_iff le
  | ctor => exact fun _ => imp_congr_right fun _ => Shape.ListNonZero.lift_iff le

theorem ShapeFun.WF.lift_iff {x : ShapeFun n} (le : n ≤ m) :
    WF Shape.WF (lift (Shape.lift m) x) ↔ WF Shape.WF x :=
  Shape.WF.lift_iff.go _ _ le (Shape.WF.lift_iff le)

protected theorem Shape.WF.lift (le : n ≤ m) : WF (n := n) x → WF (x.lift m) := (lift_iff le).2

protected theorem ShapeFun.WF.lift {x : ShapeFun n} (le : n ≤ m) : WF Shape.WF x →
    WF Shape.WF (lift (Shape.lift m) x) := (lift_iff le).2

protected theorem Shape.WF.olift {x : Shape n} (H : x.olift (m := m) = some x') :
    WF x ↔ WF x' := by
  obtain le | le := Nat.le_total n m
  · cases olift_eq_lift le ▸ H; rw [WF.lift_iff le]
  · cases (olift_thm le).1 H; rw [WF.lift_iff le]

protected theorem ShapeFun.WF.olift {x : ShapeFun n}
    (H : olift (Shape.olift (m := m)) x = some x') : WF Shape.WF x ↔ WF Shape.WF x' := by
  obtain le | le := Nat.le_total n m
  · cases ShapeFun.olift_eq_lift le ▸ H; rw [WF.lift_iff le]
  · cases (olift_thm le).1 H; rw [WF.lift_iff le]

protected theorem Shape.WF.bot : (Shape.bot (n := n)).WF := by cases n <;> trivial
protected theorem Shape.WF.sort : (Shape.sort (n := n) r).WF := by cases n <;> trivial

protected theorem ShapeFun.WF.bot : (ShapeFun.bot (n := n)).WF Shape.WF := by
  simp [WF, bot, Shape.Compat.bot_l, Shape.bot_join, Shape.WF.bot]

@[implicit_reducible] def WShape (n : Nat) := {s : Shape n // s.WF}
@[implicit_reducible] def WShapeFun (n : Nat) := {s : ShapeFun n // s.WF Shape.WF}

instance : Membership (WShape n × WShape n) (WShapeFun n) := ⟨fun f a => (a.1.1, a.2.1) ∈ f.1⟩

theorem WShapeFun.mem_def {f : WShapeFun n} : a ∈ f ↔ (a.1.1, a.2.1) ∈ f.1 := .rfl

theorem WShapeFun.mem_val {f : WShapeFun n} {s t : Shape n} (h : (s, t) ∈ f.1) :
    (⟨s, (f.2.2 _ h).1⟩, ⟨t, (f.2.2 _ h).2⟩) ∈ f := h
theorem WShapeFun.mem_val' {f : WShapeFun n} {s t : Shape n} (h : (s, t) ∈ f.1) :
    ∃ hs ht, (⟨s, hs⟩, ⟨t, ht⟩) ∈ f := ⟨(f.2.2 _ h).1, (f.2.2 _ h).2, h⟩

def WShapeFun.elems (f : WShapeFun n) : List (WShape n × WShape n) :=
  f.1.pmap (fun a wf => (⟨a.1, wf.1⟩, ⟨a.2, wf.2⟩)) f.2.2

@[simp] theorem WShapeFun.mem_elems {f : WShapeFun n} : a ∈ f.elems ↔ a ∈ f := by
  simp only [elems, List.mem_pmap, Prod.exists, mem_def]
  exact ⟨fun ⟨_, _, h, rfl⟩ => h, fun h => ⟨_, _, h, rfl⟩⟩

@[ext] theorem WShape.ext {s t : WShape n} (h : s.1 = t.1) : s = t := Subtype.ext h
@[ext] theorem WShapeFun.ext {s t : WShapeFun n} (h : s.1 = t.1) : s = t := Subtype.ext h

def WShapeFun.NonZero (f : WShapeFun n) := f.1.NonZero
instance {f : WShapeFun n} : Decidable f.NonZero := inferInstanceAs (Decidable f.1.NonZero)

def WShape.bot : WShape n := ⟨.bot, .bot⟩
def WShape.sort (r : Bool) : WShape n := ⟨.sort r, .sort⟩
abbrev WShape.type : WShape n := .sort true
abbrev WShape.prop : WShape n := .sort false
def WShape.indTy : WShape (n+1) := ⟨.indTy, trivial⟩
def WShape.forallE (s : WShape n) (f : WShapeFun n) : WShape (n + 1) := ⟨.forallE s.1 f.1, s.2, f.2⟩
def WShape.lam (f : WShapeFun n) (h : f.NonZero) :
    WShape (n + 1) := ⟨.lam f.1, f.2, h⟩
def WShape.lam' (f : WShapeFun n) : WShape (n + 1) := if h : f.NonZero then .lam f h else .bot
theorem WShape.lam_eq_lam' {f : WShapeFun n} {hl} : WShape.lam f hl = .lam' f := by
  simp [lam', hl]

def WShape.ListNonZero (l : List (WShape n)) := ∃ x ∈ l, ¬x.1 ≤ .bot
instance {l : List (WShape n)} : Decidable (WShape.ListNonZero l) :=
  inferInstanceAs (Decidable (∃ x ∈ l, ¬x.1 ≤ .bot))

theorem WShape.ListNonZero.def {l : List (WShape n)} :
    ListNonZero l ↔ Shape.ListNonZero (l.map (·.1)) := by
  simp only [ListNonZero, Shape.ListNonZero, List.mem_map]
  exact ⟨fun ⟨_, h1, h2⟩ => ⟨_, ⟨_, h1, rfl⟩, h2⟩, fun ⟨_, ⟨_, h1, rfl⟩, h2⟩ => ⟨_, h1, h2⟩⟩
def WShape.ctor (c : Name) (l : List (WShape n))
    (H : IsStruct c → ListNonZero l) : WShape (n + 1) := by
  refine ⟨.ctor c (l.map (·.1)), fun _ h => ?_, ListNonZero.def.1 ∘ H⟩
  have ⟨x, _, eq⟩ := List.mem_map.1 h; exact eq ▸ x.2
def WShape.ctor' (c : Name) (l : List (WShape n)) : WShape (n + 1) :=
  if h : IsStruct c → ListNonZero l then
    .ctor c l (by simpa [Shape.le_bot] using h)
  else .bot

theorem WShape.mk_ctor {n} (l : List (Shape n)) (wf : Shape.WF (n := n+1) (.ctor c l)) :
    ∃ h, WShape.ctor c (l.pmap Subtype.mk wf.1) h = ⟨.ctor c l, wf⟩ := by
  refine ⟨fun h => ?_, Subtype.ext ?_⟩
  · simp [ListNonZero]; let ⟨_, h1, h2⟩ := wf.2 h; exact ⟨_, ⟨_, h1, rfl⟩, h2⟩
  · simp [WShape.ctor]; congr 1; rw [List.map_pmap, List.pmap_eq_map, List.map_id']

theorem WShape.ctor_eq_ctor' : ctor c l h = ctor' c l := by rw [ctor', dif_pos]

def WShapeFun.bot {n : Nat} : WShapeFun n := ⟨.bot, .bot⟩

theorem WShapeFun.NonZero.bot : ¬NonZero (n := n) .bot := by
  simp [NonZero, WShapeFun.bot, ShapeFun.bot, ShapeFun.NonZero]

@[simp] theorem WShape.lam'_bot : WShape.lam' (n := n) .bot = .bot := by
  simp [lam', WShapeFun.NonZero.bot]

theorem WShapeFun.mem_bot : (x, y) ∈ WShapeFun.bot ↔ x = .bot ∧ y = .bot := by
  simp [WShapeFun.mem_def, bot, WShape.ext_iff, WShape.bot, ShapeFun.bot]

/-- Case split on a `WShape (n+1)`. -/
@[elab_as_elim]
def WShape.casesOn' {motive : WShape (n+1) → Sort u}
    (s : WShape (n+1))
    (bot : motive .bot)
    (sort : ∀ r, motive (.sort r))
    (forallE : ∀ s f, motive (.forallE s f))
    (lam : ∀ f h, motive (.lam f h))
    (ctor : ∀ c l h, motive (.ctor c l h))
    (indTy : motive .indTy) : motive s := by
  obtain ⟨s, wf⟩ := s
  cases s with
  | bot => exact bot
  | sort r => exact sort r
  | forallE s' f' => exact forallE ⟨s', wf.1⟩ ⟨f', wf.2⟩
  | lam f' => exact lam ⟨f', wf.1⟩ wf.2
  | ctor c l => exact (WShape.mk_ctor l wf).2 ▸ ctor ..
  | indTy => exact indTy

/-- Case split on a `WShape n`. -/
@[elab_as_elim]
def WShape.casesOn {motive : ∀ {n}, WShape n → Sort u}
    {n} (s : WShape n)
    (bot : motive (n := n) .bot)
    (sort : ∀ r, motive (n := n) (.sort r))
    (forallE : ∀ {n'} s f, motive (n := n'+1) (.forallE s f))
    (lam : ∀ {n'} f h, motive (n := n'+1) (.lam f h))
    (ctor : ∀ {n'} c l h, motive (n := n'+1) (.ctor c l h))
    (indTy : ∀ {n'}, motive (n := n'+1) .indTy) : motive s := by
  cases n with
  | zero =>
    obtain ⟨s, wf⟩ := s
    cases s with
    | bot => exact bot
    | sort r => exact sort r
  | succ n => exact s.casesOn' bot sort forallE lam ctor indTy

def WShape.lift {n} (m) (s : WShape n) : WShape m := by
  refine ⟨(s.1.olift (m := m)).getD .bot, ?_⟩
  cases eq : s.1.olift <;> [exact .bot; exact (Shape.WF.olift eq).1 s.2]

def WShapeFun.lift {n} (m) (s : WShapeFun n) : WShapeFun m := by
  refine ⟨(ShapeFun.olift Shape.olift s.1).getD ShapeFun.bot, ?_⟩
  cases eq : ShapeFun.olift Shape.olift s.1 <;> [exact .bot; exact (ShapeFun.WF.olift eq).1 s.2]

abbrev WShape.LE (a b : WShape n) := a.1 ≤ b.1
abbrev WShapeFun.LE (a b : WShapeFun n) := a.1.LE b.1
instance : LE (WShape n) := ⟨WShape.LE⟩
instance : LE (WShapeFun n) := ⟨WShapeFun.LE⟩

instance : DecidableRel (α := WShape n) (· ≤ ·) := fun a b => inferInstanceAs (Decidable (a.1 ≤ b.1))
instance : DecidableRel (α := WShapeFun n) (· ≤ ·) :=
  fun a b => inferInstanceAs (Decidable (a.1.LE b.1))

theorem WShape.LE.def {a b : WShape n} : a ≤ b ↔ a.1 ≤ b.1 := .rfl
theorem WShapeFun.LE.def {a b : WShapeFun n} : a ≤ b ↔ a.1.LE b.1 := .rfl

theorem WShapeFun.NonZero.iff {f : WShapeFun n} : f.NonZero ↔ ∃ x ∈ f, ¬x.2 ≤ .bot :=
  ⟨fun ⟨_, h1, h2⟩ => ⟨_, f.mem_val h1, h2⟩, fun ⟨_, h1, h2⟩ => ⟨_, h1, h2⟩⟩

theorem WShapeFun.NonZero.mono {f f' : WShapeFun n} :
    (h1 : f.LE f') → (h2 : NonZero f) → NonZero f' :=
  ShapeFun.NonZero.mono

theorem WShape.ListNonZero.mono {l l' : List (WShape n)}
    (le : l.Forall₂ (· ≤ ·) l') : ListNonZero l → ListNonZero l' := by
  simp [ListNonZero.def]; apply Shape.ListNonZero.mono; simpa

theorem WShape.lift_val {s : WShape n} (le : n ≤ m) : (s.lift m).1 = s.1.lift m := by
  simp [lift, Shape.olift_eq_lift le]

theorem WShapeFun.lift_val {s : WShapeFun n} (le : n ≤ m) :
    (s.lift m).1 = ShapeFun.lift (Shape.lift m) s.1 := by
  simp [lift, ShapeFun.olift_eq_lift le]

theorem WShapeFun.mem_lift {s : WShapeFun n} (le : n ≤ m) :
    (x, x') ∈ s.lift m ↔ ∃ y y', (y, y') ∈ s ∧ x = y.lift m ∧ x' = y'.lift m := by
  cases x; cases x'
  simp [mem_def, lift_val le, WShape.lift_val le, ShapeFun.lift, WShape.ext_iff]
  constructor <;> exact fun ⟨_, _, h1, h2, h3⟩ => ⟨_, _, s.mem_val h1, h2.symm, h3.symm⟩

theorem WShape.forallE.inj {f : WShapeFun n} :
    WShape.forallE a f = WShape.forallE a' f' ↔ a = a' ∧ f = f' := by
  simp [WShape.ext_iff, WShapeFun.ext_iff, forallE]
  exact iff_of_eq (ShapeS.forallE.injEq ..)

@[simp] theorem WShape.lift_bot : (WShape.bot : WShape n).lift m = .bot := by
  ext; simp [lift, bot]

@[simp] theorem WShapeFun.lift_bot : WShapeFun.lift (n := n) m .bot = .bot := by
  ext1; simp [WShapeFun.lift, bot, ShapeFun.olift_bot]

@[simp] theorem WShape.lift_sort : (WShape.sort r : WShape n).lift m = .sort r := by
  ext; simp [lift, sort]

@[simp] theorem WShape.lift_type : (WShape.type (n := n)).lift m = WShape.type := WShape.lift_sort

@[simp] theorem WShape.lift_indTy {n m : Nat} : (.indTy : WShape (n+1)).lift (m+1) = .indTy :=
  Subtype.ext <| by simp [lift, indTy, Shape.olift]

theorem WShape.lift_self {s : WShape n} : s.lift n = s := by
  ext; rw [lift_val (Nat.le_refl _), Shape.lift_self]

theorem WShapeFun.lift_self {s : WShapeFun n} : s.lift n = s := by
  ext; rw [lift_val (Nat.le_refl _), ShapeFun.lift_self]

theorem WShape.lift_lift {s : WShape n₁} (le : n₁ ≤ n₂ ∨ n₃ ≤ n₂) :
    (s.lift n₂).lift n₃ = s.lift n₃ := by
  ext; simp [lift]
  by_cases h1 : n₁ ≤ n₂
  · congr 1; ext t; rw [Shape.olift_eq_lift h1, Option.getD]
    obtain h2 | h2 := Nat.le_total n₂ n₃
    · rw [Shape.olift_eq_lift h2, Shape.lift_lift (.inl h1),
        Shape.olift_eq_lift (Nat.le_trans h1 h2)]
    rw [Shape.olift_thm h2]
    obtain h3 | h3 := Nat.le_total n₁ n₃
    · rw [Shape.olift_eq_lift h3, Option.some_inj, ← Shape.lift_lift (.inl h3), Shape.lift_inj h2]
    · rw [Shape.olift_thm h3, ← Shape.lift_lift (.inl h3), Shape.lift_inj h1]
  · have h2 := le.resolve_left h1; have h1 := Nat.le_of_not_ge h1
    cases eq : s.1.olift (m := n₂) <;> simp
    · cases eq' : s.1.olift (m := n₃) <;> simp
      rw [Shape.olift_thm (Nat.le_trans h2 h1), ← Shape.lift_lift (.inl h2),
        ← Shape.olift_thm h1, eq] at eq'; cases eq'
    · rw [(Shape.olift_thm h1).1 eq]; rename_i t
      cases eq₁ : t.olift
      · cases eq₂ : (Shape.lift n₁ t).olift; · rfl
        rw [Shape.olift_thm (Nat.le_trans h2 h1), ← Shape.lift_lift (.inl h2)] at eq₂
        rw [(Shape.lift_inj h1).1 eq₂, (Shape.olift_thm h2).2 rfl] at eq₁; cases eq₁
      · rw [(Shape.olift_thm h2).1 eq₁, Shape.lift_lift (.inl h2),
          (Shape.olift_thm (Nat.le_trans h2 h1)).2 rfl]

theorem WShapeFun.lift_lift {s : WShapeFun n₁} (le : n₁ ≤ n₂ ∨ n₃ ≤ n₂) :
    (s.lift n₂).lift n₃ = s.lift n₃ := by
  ext1; simp [lift]
  by_cases h1 : n₁ ≤ n₂
  · congr 1; ext t; rw [ShapeFun.olift_eq_lift h1, Option.getD]
    obtain h2 | h2 := Nat.le_total n₂ n₃
    · rw [ShapeFun.olift_eq_lift h2, ShapeFun.lift_lift (.inl h1),
        ShapeFun.olift_eq_lift (Nat.le_trans h1 h2)]
    rw [ShapeFun.olift_thm h2]
    obtain h3 | h3 := Nat.le_total n₁ n₃
    · rw [ShapeFun.olift_eq_lift h3, Option.some_inj, ← ShapeFun.lift_lift (.inl h3),
        ShapeFun.lift_inj h2]
    · rw [ShapeFun.olift_thm h3, ← ShapeFun.lift_lift (.inl h3), ShapeFun.lift_inj h1]
  · have h2 := le.resolve_left h1; have h1 := Nat.le_of_not_ge h1
    cases eq : ShapeFun.olift (Shape.olift (m := n₂)) s.1 <;> simp
    · cases eq' : ShapeFun.olift (Shape.olift (m := n₃)) s.1 <;> simp
      rw [ShapeFun.olift_thm (Nat.le_trans h2 h1), ← ShapeFun.lift_lift (.inl h2),
        ← ShapeFun.olift_thm h1, eq] at eq'; cases eq'
    · rw [(ShapeFun.olift_thm h1).1 eq]; rename_i t
      cases eq₁ : ShapeFun.olift Shape.olift t
      · cases eq₂ : ShapeFun.olift Shape.olift (ShapeFun.lift (Shape.lift n₁) t); · rfl
        rw [ShapeFun.olift_thm (Nat.le_trans h2 h1), ← ShapeFun.lift_lift (.inl h2)] at eq₂
        rw [(ShapeFun.lift_inj h1).1 eq₂, (ShapeFun.olift_thm h2).2 rfl] at eq₁; cases eq₁
      · rw [(ShapeFun.olift_thm h2).1 eq₁, ShapeFun.lift_lift (.inl h2),
          (ShapeFun.olift_thm (Nat.le_trans h2 h1)).2 rfl]

theorem WShape.lift_le_lift {s t : WShape n} (le : n ≤ m) :
    s.lift m ≤ t.lift m ↔ s ≤ t := by
  show (s.lift m).1 ≤ (t.lift m).1 ↔ s.1 ≤ t.1
  rw [lift_val le, lift_val le]; exact Shape.lift_le_lift le

theorem WShapeFun.lift_le_lift {s t : WShapeFun n} (le : n ≤ m) :
    s.lift m ≤ t.lift m ↔ s ≤ t := by
  show (s.lift m).1.LE (t.lift m).1 ↔ s.1.LE t.1
  rw [lift_val le, lift_val le]; exact ShapeFun.lift_le_lift le

theorem WShapeFun.lift_mono {s t : WShapeFun n} (le : n ≤ m) (h : s ≤ t) : s.lift m ≤ t.lift m :=
  (lift_le_lift le).2 h

theorem WShapeFun.LE.def' {f f' : WShapeFun n} : f ≤ f' ↔
    ∀ x y : WShape n, (x, y) ∈ f → ∃ x' y' : WShape n, (x', y') ∈ f' ∧ x' ≤ x ∧ y ≤ y' := by
  simp [(· ≤ ·), ShapeFun.LE.def]
  constructor <;> intro H x y h1
  · have ⟨_, _, h2, h3⟩ := H _ _ h1
    exact ⟨⟨_, (f'.2.2 _ h2).1⟩, ⟨_, (f'.2.2 _ h2).2⟩, h2, h3⟩
  · have ⟨x', y', h2, h3⟩ := H ⟨_, (f.2.2 _ h1).1⟩ ⟨_, (f.2.2 _ h1).2⟩ h1
    exact ⟨_, _, h2, h3⟩

theorem WShape.lift_mono {s t : WShape n} (le : n ≤ m) : s ≤ t → s.lift m ≤ t.lift m :=
  (lift_le_lift le).2

/-- Lift both sides of a pointwise list bound through a second common
shape level.  This is the list-level transport used when a constant's
semantic function depth and its accumulated application-spine depth differ. -/
theorem WShape.forall₂_lift
    {xs : List (WShape n)} {ys : List (WShape n')}
    (hn : n ≤ n') (hnk : n' ≤ k)
    (H : List.Forall₂ (· ≤ ·) (xs.map (fun x => x.lift n')) ys) :
    List.Forall₂ (· ≤ ·) (xs.map (fun x => x.lift k))
      (ys.map (fun y => y.lift k)) := by
  induction xs generalizing ys with
  | nil =>
    simp only [List.map_nil] at H ⊢
    cases H
    exact .nil
  | cons x xs ih =>
    simp only [List.map_cons] at H ⊢
    cases H with
    | cons hxy hrest =>
      refine .cons ?_ (ih hrest)
      have h := WShape.lift_mono hnk hxy
      rwa [WShape.lift_lift (.inl hn)] at h

theorem WShape.lift_le_bot {s : WShape n} (h : n ≤ m) : s.lift m ≤ .bot ↔ s = .bot := by
  rw [← WShape.lift_bot (n := n), WShape.lift_le_lift h]
  exact ⟨fun h => WShape.ext (Shape.le_bot.1 h), fun h => h ▸ Shape.LE.rfl⟩

theorem WShape.lift_eq_bot {s : WShape n} (h : n ≤ m) : s.lift m = .bot ↔ s = .bot := by
  exact ⟨fun h' => (lift_le_bot h).1 (h' ▸ Shape.LE.rfl), fun h' => h' ▸ lift_bot⟩

theorem WShape.le_bot {s : WShape n} : s ≤ .bot ↔ s = .bot :=
  Shape.le_bot.trans (Subtype.ext_iff (a1 := s) (a2 := WShape.bot)).symm

@[simp] theorem WShape.lift_forallE {s : WShape n} {f : WShapeFun n} (h : n ≤ m) :
    (WShape.forallE s f).lift (m+1) = .forallE (s.lift m) (f.lift m) := by
  ext; simp [lift_val (Nat.succ_le_succ h), Shape.lift, WShape.forallE,
    lift_val h, WShapeFun.lift_val h]

theorem WShapeFun.NonZero.lift_iff {n m} {x : WShapeFun n} (le : n ≤ m) :
    (x.lift m).NonZero ↔ NonZero (n := n) x := by
  simp [NonZero, lift_val le, ShapeFun.NonZero.lift_iff le]

theorem WShape.ListNonZero.lift_iff {n m} {x : List (WShape n)} (le : n ≤ m) :
    ListNonZero (x.map (lift m)) ↔ ListNonZero (n := n) x := by
  simp [ListNonZero.def, ← Shape.ListNonZero.lift_iff le]
  apply iff_of_eq; congr 2; ext x; simp [lift_val le]

@[simp] theorem WShape.lift_lam' {f : WShapeFun n} (le : n ≤ m) :
    (WShape.lam' f).lift (m+1) = .lam' (f.lift m) := by
  ext1; simp [lam']; split <;> simp [WShapeFun.lift_val le, WShapeFun.NonZero.lift_iff le,
    lift_val (Nat.succ_le_succ le), lam, Shape.lift, *]

theorem WShape.lift_lam {f : WShapeFun n} {hl} (h : n ≤ m) :
    (WShape.lam f hl).lift (m+1) = .lam (f.lift m) ((WShapeFun.NonZero.lift_iff h).2 hl) := by
  ext1; simp [WShape.lift_val (Nat.succ_le_succ h), lam, WShapeFun.lift_val h, Shape.lift]

theorem WShape.lift_eq_lam' {s : WShape (n+1)} (le : n ≤ m)
    {f : WShapeFun m} (eq : s.lift (m+1) = .lam' f) :
    s = .bot ∧ f ≤ .bot ∨ ∃ f' : WShapeFun n, s = .lam' f' ∧ f = f'.lift m := by
  obtain ⟨f, hf⟩ := f
  have eq := congrArg (·.1) eq; simp [lift_val (Nat.succ_le_succ le)] at eq
  unfold lam' at eq; split at eq <;> rename_i h <;>
    obtain ⟨⟨⟩, wf⟩ := s <;> simp [lam, Shape.lift] at eq <;> cases eq
  · refine .inr ⟨⟨_, wf.1⟩, ?_⟩; rw [lam', dif_pos (by exact (ShapeFun.NonZero.lift_iff le).1 h)]
    exact ⟨rfl, WShapeFun.ext (WShapeFun.lift_val le ▸ rfl)⟩
  · refine .inl ⟨rfl, WShapeFun.LE.def'.2 fun x y h => ?_⟩; rename_i hn
    refine ⟨_, _, WShapeFun.mem_bot.2 ⟨rfl, rfl⟩, Shape.bot_le, Decidable.by_contra (hn ⟨_, h, ·⟩)⟩

theorem WShape.lift_ctor {c : Name} {l : List (WShape n)} {hc} (le : n ≤ m) :
    (WShape.ctor c l hc).lift (m+1) =
    .ctor c (l.map (.lift m)) ((WShape.ListNonZero.lift_iff le).2 ∘ hc) := by
  ext1; simp [WShape.lift_val (Nat.succ_le_succ le), ctor, Shape.lift]
  congr 2; ext1 x; simp [lift_val le]

@[simp] theorem WShape.lift_ctor' {c : Name} {l : List (WShape n)} (le : n ≤ m) :
    (WShape.ctor' c l).lift (m+1) = .ctor' c (l.map (.lift m)) := by
  ext1; simp [ctor']; split <;> rename_i hc <;>
    [rw [dif_pos ((WShape.ListNonZero.lift_iff le).2 ∘ hc)];
     rw [dif_neg (mt ((WShape.ListNonZero.lift_iff le).1 ∘ ·) hc)]] <;>
    simp [lift_val (Nat.succ_le_succ le), ctor, Shape.lift]
  congr 2; ext1 x; simp [lift_val le]

@[simp] theorem WShape.bot_le : WShape.bot ≤ (s : WShape n) := Shape.bot_le

protected theorem WShape.LE.rfl {s : WShape n} : s ≤ s := Shape.LE.rfl
protected theorem WShape.LE.trans {s t u : WShape n} : s ≤ t → t ≤ u → s ≤ u := Shape.LE.trans

theorem WShape.LE.forallE_decomp {s : WShape (n+1)} {a : WShape n} {f : WShapeFun n} :
    s ≤ .forallE a f → s = .bot ∨ ∃ a' f', s = .forallE a' f' := by
  simp [WShape.LE.def, Shape.LE.def, forallE]; obtain ⟨⟨⟩, _⟩ := s <;> simp
  · simp [bot, Shape.bot]
  · rename_i wf; intros; exact .inr ⟨⟨_, wf.1⟩, ⟨_, wf.2⟩, rfl⟩

@[simp] theorem WShape.forallE_le_forallE {a a' : WShape n} {f f' : WShapeFun n} :
    WShape.forallE a f ≤ .forallE a' f' ↔ a ≤ a' ∧ f ≤ f' := Shape.forallE_le_forallE

theorem WShape.le_forallE_iff {s : WShape (n+1)} {a' : WShape n} {f' : WShapeFun n} :
    s ≤ .forallE a' f' ↔ s = .bot ∨ ∃ a f, s = .forallE a f ∧ a ≤ a' ∧ f ≤ f' := by
  constructor
  · cases s using WShape.casesOn' with
    | bot => exact fun _ => .inl rfl
    | forallE a f => exact fun h => .inr ⟨a, f, rfl, forallE_le_forallE.1 h⟩
    | indTy => apply Not.elim; simp [indTy, forallE, LE.def, Shape.LE.def]
    | _ => simp only [sort, lam, ctor, forallE, LE.def, Shape.LE.def, false_implies]
  · rintro (rfl | ⟨a, f, rfl, h1, h2⟩)
    · exact bot_le
    · exact forallE_le_forallE.2 ⟨h1, h2⟩

theorem WShape.le_sort {s : WShape n} : s ≤ .sort r ↔ s = .bot ∨ s = .sort r :=
  Shape.le_sort.trans <| by simp [WShape.ext_iff, WShape.bot, WShape.sort]

theorem WShape.sort_le {s : WShape n} : .sort r ≤ s ↔ .sort r = s :=
  Shape.sort_le.trans <| by simp [WShape.ext_iff, WShape.sort]

theorem WShape.le_indTy {s : WShape (n+1)} : s ≤ .indTy ↔ s = .bot ∨ s = .indTy :=
  Shape.le_indTy.trans <| by simp [WShape.ext_iff, WShape.bot, WShape.indTy]

theorem WShape.indTy_le {s : WShape (n+1)} : .indTy ≤ s ↔ s = .indTy :=
  Shape.indTy_le.trans ⟨(Subtype.ext ·), (congrArg (·.1) ·)⟩

theorem WShape.forallE_le {s : WShape (n+1)} {a : WShape n} {f : WShapeFun n} :
    WShape.forallE a f ≤ s ↔
      ∃ a' : WShape n, ∃ f' : WShapeFun n, a ≤ a' ∧ f ≤ f' ∧ s = .forallE a' f' := by
  constructor
  · intro h
    have ⟨a', b', h1, h2, h3⟩ := Shape.forallE_le.1 h
    have wf := h3 ▸ s.2
    exact ⟨⟨a', wf.1⟩, ⟨b', wf.2⟩, h1, h2, WShape.ext h3.symm⟩
  · intro ⟨a', f', h1, h2, h3⟩; subst h3; exact WShape.forallE_le_forallE.2 ⟨h1, h2⟩

theorem WShape.lam_le_lam {f f' : WShapeFun n} {hf hf'} :
    WShape.lam f hf ≤ .lam f' hf' ↔ f ≤ f' := .rfl

theorem WShape.lam'_le_lam' {f f' : WShapeFun n} :
    WShape.lam' f ≤ .lam' f' ↔ f ≤ f' := by
  simp [WShape.LE.def, lam', WShapeFun.LE.def]
  split <;> [split <;> rename_i h h'; rename_i h] <;> simp [lam, bot, Shape.LE.def, ShapeFun.LE.def]
  · let ⟨_, h1, h2⟩ := h
    refine ⟨_, _, h1, fun _ _ h3 h4 h5 => h' ⟨_, h3, mt h5.trans h2⟩⟩
  · intro _ y h1; have h2 := Decidable.by_contra (mt (⟨_, h1, ·⟩) h)
    have ⟨_, h⟩ := f'.2.1.1; exact ⟨_, _, h, Shape.bot_le, .trans h2 Shape.bot_le⟩

theorem WShape.LE.le_lam {s : WShape (n+1)} {f : WShapeFun n} {hl} :
    s ≤ .lam f hl → s = .bot ∨ ∃ f' hl', s = .lam f' hl' := by
  simp [WShape.LE.def, Shape.LE.def, lam]; obtain ⟨⟨⟩, _⟩ := s <;> simp
  · simp [bot, Shape.bot]
  · rename_i wf; intros; exact .inr ⟨⟨_, wf.1⟩, wf.2, rfl⟩

theorem WShape.LE.lam_le {s : WShape (n+1)} {f : WShapeFun n} {hl} :
    .lam f hl ≤ s → ∃ f' hl', s = .lam f' hl' := by
  simp [WShape.LE.def, Shape.LE.def, lam]; obtain ⟨⟨⟩, _⟩ := s <;> simp
  rename_i wf; intros; exact ⟨⟨_, wf.1⟩, wf.2, rfl⟩

theorem WShape.LE.le_lam' {s : WShape (n+1)} {f : WShapeFun n} :
    s ≤ .lam' f → ∃ f', s = .lam' f' := by
  rw [lam']; split
  · intro h; obtain rfl | ⟨_, h, rfl⟩ := h.le_lam
    · exact ⟨.bot, by simp⟩
    · exact ⟨_, lam_eq_lam'⟩
  · simp [le_bot]; rintro rfl; exact ⟨.bot, by simp⟩

theorem WShape.lam.inj {f f' : WShapeFun n} {h h'} :
    WShape.lam f h = WShape.lam f' h' ↔ f = f' := by
  simp [WShape.ext_iff, WShapeFun.ext_iff, lam]
  exact iff_of_eq (ShapeS.lam.injEq ..)

theorem WShape.ctor.inj {f f' : List (WShape n)} {h h'} :
    WShape.ctor c f h = WShape.ctor c' f' h' ↔ c = c' ∧ f = f' := by
  simp [WShape.ext_iff, ctor]
  refine iff_of_eq (ShapeS.ctor.injEq ..) |>.trans ?_
  exact and_congr_right' <| List.map_inj_right fun _ _ => Subtype.ext

theorem WShapeFun.bot_mem (f : WShapeFun n) : ∃ y, (.bot, y) ∈ f :=
  let ⟨_, h⟩ := f.2.1.1; ⟨_, f.mem_val h⟩

@[simp] theorem WShapeFun.bot_le {f : WShapeFun n} : bot ≤ f := by
  simp [LE.def', mem_bot, WShape.le_bot, and_left_comm, WShape.bot_le, f.bot_mem]

def WShape.Compat (a b : WShape n) : Prop := a.1.Compat b.1
def WShapeFun.Compat (a b : WShapeFun n) : Prop := ShapeFun.Compat Shape.Compat a.1 b.1
instance : Decidable (WShape.Compat a b) := inferInstanceAs (Decidable (_ = true))
instance : Decidable (WShapeFun.Compat a b) := inferInstanceAs (Decidable (_ = true))

@[simp] theorem WShape.Compat.bot_l {n} {s : WShape n} : bot.Compat s := Shape.Compat.bot_l
@[simp] theorem WShape.Compat.bot_r {n} {s : WShape n} : s.Compat bot := Shape.Compat.bot_r
@[simp] theorem WShape.Compat.sort_sort : Compat (sort r : WShape n) (sort r') ↔ r = r' :=
  Shape.Compat.sort_sort

@[simp] theorem WShape.Compat.forallE_forallE {a a' : WShape n} {f f' : WShapeFun n} :
    (WShape.forallE a f).Compat (.forallE a' f') ↔ a.Compat a' ∧ WShapeFun.Compat f f' :=
  Shape.Compat.forallE_forallE

@[simp] theorem WShape.Compat.lam_lam {f f' : WShapeFun n} {hf hf'} :
    (WShape.lam f hf).Compat (.lam f' hf') ↔ WShapeFun.Compat f f' := Shape.Compat.lam_lam

@[simp] theorem WShape.Compat.ctor_ctor {l l' : List (WShape n)} {hl hl'} :
    (WShape.ctor c l hl).Compat (.ctor c' l' hl') ↔ c = c' ∧ l.Forall₂ Compat l' := by
  simp [WShape.Compat, ctor, Shape.Compat.ctor_ctor]; intro; rfl

theorem WShape.Compat.lam'_lam' {f f' : WShapeFun n} (H : f.Compat f') :
    (WShape.lam' f).Compat (.lam' f') := by
  unfold lam'; split <;> [split <;> [exact lam_lam.2 H; exact .bot_r]; exact .bot_l]

theorem WShape.Compat.ctor'_ctor' {l l' : List (WShape n)}
    (H : l.Forall₂ Compat l') : (WShape.ctor' c l).Compat (.ctor' c l') := by
  unfold ctor'; split <;> [split <;> [exact ctor_ctor.2 ⟨rfl, H⟩; exact .bot_r]; exact .bot_l]

theorem WShapeFun.Compat.def {n} {f f' : WShapeFun n} :
    f.Compat f' ↔ ∀ x ∈ f, ∀ y ∈ f', x.1.Compat y.1 → x.2.Compat y.2 := by
  simp [Compat, ShapeFun.Compat.def]
  constructor <;> intro H _ _ h1 _ _ h2
  · exact H _ _ h1 _ _ h2
  · exact H _ _ (f.mem_val h1) _ _ (f'.mem_val h2)

theorem WShapeFun.join_mem' {f : WShapeFun n}
    (hx : (x, y) ∈ f) (hy : (x', y') ∈ f) (hc : x.Compat x') :
    ∃ z, z ∈ f ∧ x.1.join x'.1 ≤ z.1.1 ∧ z.1.1 ≤ x.1.join x'.1 := by
  let ⟨_, h1, h2⟩ := (f.2.1.2 _ (f.mem_val hx) _ (f.mem_val hy)).1 hc
  exact ⟨_, f.mem_val h1, h2⟩

theorem WShapeFun.mem_mono {f : WShapeFun n}
    (hx : (x, y) ∈ f) (hy : (x', y') ∈ f) : x ≤ x' → y ≤ y' :=
  (f.2.1.2 _ (f.mem_val hx) _ (f.mem_val hy)).2

protected theorem WShape.Compat.lift {x y : WShape n} (le : n ≤ m) :
    (x.lift m).Compat (y.lift m) ↔ x.Compat y := by
  simp [WShape.Compat, lift_val le, Shape.Compat.lift le]

omit [Params] in
theorem ShapeFun.mem_trunc {f : ShapeFun n} : x ∈ f.trunc a ↔ x ∈ f ∧ x.1 ≤ a := by simp [trunc]

namespace WShape.join_prop
variable (ih : ∀ {x y : WShape n}, (∀ z, x ≤ z → y ≤ z → x.Compat y) ∧
  (x.Compat y → (x.1.join y.1).WF ∧ ∀ z, x.1.join y.1 ≤ z.1 ↔ x ≤ z ∧ y ≤ z))
include ih

theorem exists_max {f : WShapeFun n}
    (hc : ∀ x ∈ f, ∀ y ∈ f, x.1.Compat y.1) : ∃ x ∈ f.1, ∀ x' ∈ f.1, x'.1 ≤ x.1 := by
  suffices ∀ l : ShapeFun n, (∀ x ∈ l, x ∈ f.1) → ∃ x ∈ f.1, ∀ x' ∈ l, x'.1 ≤ x.1 from
    have ⟨_, h1, h2⟩ := this _ fun _ => id; ⟨_, f.mem_val h1, fun _ => h2 _⟩
  intro l hl; induction l with
  | nil => let ⟨_, h⟩ := f.2.1.1; exact ⟨_, h, nofun⟩
  | cons a l ihl =>
    have ⟨hm, hl⟩ := List.forall_mem_cons.1 hl
    have ⟨x, h1, h2⟩ := ihl hl
    have := hc _ (f.mem_val hm) _ (f.mem_val h1)
    have ⟨_, a1, a2⟩ := f.join_mem' (f.mem_val hm) (f.mem_val h1) this
    have ⟨b1, b2⟩ := ((ih.2 this).2 ⟨_, (f.2.2 _ a1).1⟩).1 a2.1
    exact ⟨_, a1, List.forall_mem_cons.2 ⟨b1, fun _ h => (h2 _ h).trans b2⟩⟩

def wf_trunc (f : WShapeFun n) (a : WShape n) : WShapeFun n := by
  refine ⟨f.1.trunc a.1, ?_, fun _ h1 => f.2.2 _ (ShapeFun.mem_trunc.1 h1).1⟩
  simp [ShapeFun.trunc]
  refine ⟨f.2.1.1, fun _ _ h1 h2 _ _ h3 h4 => ?_⟩
  have ⟨a1, a2, h1⟩ := f.mem_val' h1; have ⟨b1, b2, h3⟩ := f.mem_val' h3
  have ⟨a3, a4⟩ := f.2.1.2 _ h1 _ h3; refine ⟨fun h => ?_, a4⟩
  have ⟨⟨z, z'⟩, a5, a6⟩ := a3 h
  refine ⟨_, ⟨⟨_, a5⟩, a6.2.trans ?_⟩, a6⟩
  exact (ih.2 <| (@ih ⟨_, a1⟩ ⟨_, b1⟩).1 _ h2 h4).2 _ |>.2 ⟨h2, h4⟩

theorem trunc_compat (f : WShapeFun n) (a : WShape n)
    {{x}} (h1 : x ∈ wf_trunc ih f a) {{y}} (h2 : y ∈ wf_trunc ih f a) : x.1.Compat y.1 :=
  have ⟨a1, a2⟩ := ShapeFun.mem_trunc.1 h1
  have ⟨b1, b2⟩ := ShapeFun.mem_trunc.1 h2
  (@ih ⟨_, (f.2.2 _ a1).1⟩ ⟨_, (f.2.2 _ b1).1⟩).1 a a2 b2

theorem app_core (f : WShapeFun n) (x : WShape n) :
    ∃ x', x' ≤ x.1 ∧ (x', f.1.app x.1) ∈ f.1 ∧ ∀ y ∈ f.1, y.1 ≤ x.1 → y.2 ≤ f.1.app x.1 := by
  simp only [ShapeFun.app, ShapeFun.maxBelow]
  have ⟨_, h1, h2⟩ := exists_max ih (trunc_compat ih f x)
  simp [wf_trunc, ShapeFun.mem_trunc] at h1 h2
  show let P := _; ∃ x', x' ≤ x.1 ∧ let y' := ((List.find? P _).getD (Shape.bot, Shape.bot)).snd
    (x', y') ∈ f.1 ∧ ∀ y ∈ f.1, y.1 ≤ x.1 → y.2 ≤ y'
  intro P
  have ⟨⟨x', y'⟩, h⟩ := Option.isSome_iff_exists.1 <|
    (List.find?_isSome (p := P)).2 ⟨_, ShapeFun.mem_trunc.2 h1, by simpa [P, ShapeFun.mem_trunc]⟩
  have := List.find?_some h; simp [P, ShapeFun.mem_trunc, h] at this ⊢
  have ⟨h1, h2⟩ := ShapeFun.mem_trunc.1 <| List.mem_of_find?_eq_some h
  exact ⟨_, h2, h1, fun _ _ a1 a2 => (f.2.1.2 _ a1 _ h1).2 (this _ _ a1 a2)⟩

theorem of_compat {x x' : WShape n} (hc : x.Compat x') :
    ∃ j : WShape n, j.1 = x.1.join x'.1 ∧ ∀ w, j ≤ w ↔ x ≤ w ∧ x' ≤ w :=
  ⟨⟨_, (ih.2 hc).1⟩, rfl, (ih.2 hc).2⟩

theorem join_mem' {f : WShapeFun n} {x y x' y'}
    (hx : (x, y) ∈ f) (hy : (x', y') ∈ f) (hc : x.Compat x') :
    ∃ j : WShape n, j.1 = x.1.join x'.1 ∧ ∃ z, z ∈ f ∧ j ≤ z.1 ∧ z.1 ≤ j ∧
      ∀ w, j ≤ w ↔ x ≤ w ∧ x' ≤ w :=
  let ⟨_, a1, a2, a3⟩ := f.join_mem' hx hy hc
  ⟨⟨_, (ih.2 hc).1⟩, rfl, _, a1, a2, a3, (ih.2 hc).2⟩

theorem compat_app_r {f : WShapeFun n} {x x' : WShape n} (hc : x.Compat x') :
    (f.1.app x.1).Compat (f.1.app x'.1) :=
  have ⟨_, a1, a2, _⟩ := app_core ih f x; have a2 := f.mem_val a2
  have ⟨_, b1, b2, _⟩ := app_core ih f x'; have b2 := f.mem_val b2
  have ⟨_, _, _, c2, c3, _, c5⟩ := join_mem' ih a2 b2 (Shape.Compat.mono a1 b1 hc)
  have ⟨c6, c7⟩ := (c5 _).1 .rfl
  ih.1 _ (f.mem_mono a2 c2 (c6.trans c3)) (f.mem_mono b2 c2 (c7.trans c3))

theorem compat_app_l {f f' : WShapeFun n} (hc : f.Compat f') (x : WShape n) :
    (f.1.app x.1).Compat (f'.1.app x.1) := by
  have ⟨_, a1, a2, _⟩ := app_core ih f x; have ⟨a4, a5, a2⟩ := f.mem_val' a2
  have ⟨_, b1, b2, _⟩ := app_core ih f' x; have ⟨b4, b5, b2⟩ := f'.mem_val' b2
  exact (ShapeFun.Compat.def.1 hc _ a2 _ b2 ((@ih ⟨_, a4⟩ ⟨_, b4⟩).1 _ a1 b1) :)

theorem ih_fun {f f' : WShapeFun n} :
    (∀ z, f ≤ z → f' ≤ z → f.Compat f') ∧
    (f.Compat f' → ∃ h, ∀ z, ⟨ShapeFun.join Shape.join f.1 f'.1, h⟩ ≤ z ↔ f ≤ z ∧ f' ≤ z) := by
  simp only [WShapeFun.LE.def']
  refine ⟨fun z le₁ le₂ => ShapeFun.Compat.def.2 fun _ h1 _ h2 h => ?_, fun hc => ?_⟩
  · have ⟨_, _, a1, a2, a3⟩ := le₁ _ _ (f.mem_val h1)
    have ⟨_, _, b1, b2, b3⟩ := le₂ _ _ (f'.mem_val h2)
    have h := Shape.Compat.mono a2 b2 h
    refine Shape.Compat.mono a3 b3 ?_
    have ⟨_, c1, c2, c3⟩ := z.join_mem' a1 b1 h
    have ⟨e1, e2⟩ := ((ih.2 h).2 _).1 c2
    exact ih.1 _ (z.mem_mono a1 c1 e1) (z.mem_mono b1 c1 e2)
  simp only [ShapeFun.WF, ShapeFun.mem_join]
  refine ⟨⟨⟨?_, ?_⟩, fun a => ?_⟩, ?_⟩
  · let ⟨_, a1⟩ := f.bot_mem; let ⟨_, a2⟩ := f'.bot_mem
    refine ⟨_, _, a1, _, a2, Compat.bot_l, cast (Prod.mk.injEq ..).symm ⟨.symm ?_, rfl⟩⟩
    exact Shape.le_bot.1 <| ((ih.2 .bot_l).2 _).2 ⟨.rfl, .rfl⟩
  · rintro _ ⟨x, a1, x', a2, a3, rfl⟩ _ ⟨y, b1, y', b2, b3, rfl⟩
    replace a1 := f.mem_val a1; replace a2 := f'.mem_val a2
    replace b1 := f.mem_val b1; replace b2 := f'.mem_val b2
    change Compat ⟨x.1, (f.2.2 _ a1).1⟩ ⟨x'.1, (f'.2.2 _ a2).1⟩ at a3
    change Compat ⟨y.1, (f.2.2 _ b1).1⟩ ⟨y'.1, (f'.2.2 _ b2).1⟩ at b3
    dsimp only
    have ⟨a, a5, a6⟩ := of_compat ih a3; have ⟨a31, a32⟩ := (a6 _).1 .rfl; have ac := ih.1 _ a31 a32
    have ⟨b, b5, b6⟩ := of_compat ih b3; have ⟨b31, b32⟩ := (b6 _).1 .rfl; have bc := ih.1 _ b31 b32
    refine ⟨fun h1 => ?_, fun h1 => a5 ▸ b5 ▸ ?_⟩
    · have h1' : a.Compat b := by simp [Compat, a5, b5, h1]
      have ⟨c, c1, c2⟩ := of_compat ih h1'; have ⟨c3, c4⟩ := (c2 _).1 .rfl
      have dc := ih.1 _ (a31.trans c3) (b31.trans c4)
      have ⟨d, d1, d', d2, d3, d4, d5⟩ := join_mem' ih a1 b1 dc; have ⟨d6, d7⟩ := (d5 _).1 .rfl
      have ec := ih.1 _ (a32.trans c3) (b32.trans c4)
      have ⟨e, e1, e', e2, e3, e4, e5⟩ := join_mem' ih a2 b2 ec; have ⟨e6, e7⟩ := (e5 _).1 .rfl
      have h4 := d4.trans <| (d5 _).2 ⟨a31.trans c3, b31.trans c4⟩
      have h5 := e4.trans <| (e5 _).2 ⟨a32.trans c3, b32.trans c4⟩
      have hc := ih.1 _ h4 h5
      have ⟨j, j1, j2⟩ := of_compat ih hc; have ⟨j3, j4⟩ := (j2 _).1 .rfl
      refine ⟨_, ⟨_, d2, _, e2, hc, rfl⟩, j1 ▸ a5 ▸ b5 ▸ c1 ▸ ?_⟩; dsimp only
      refine ⟨(c2 _).2 ⟨?_, ?_⟩, (j2 _).2 ⟨h4, h5⟩⟩
      · exact (a6 _).2 ⟨d6.trans (d3.trans j3), e6.trans (e3.trans j4)⟩
      · exact (b6 _).2 ⟨d7.trans (d3.trans j3), e7.trans (e3.trans j4)⟩
    · have ⟨_, c1, c2, _⟩ := app_core ih f a; have ⟨c3, c4, c2⟩ := f.mem_val' c2
      have ⟨_, d1, d2, _⟩ := app_core ih f' a; have ⟨d3, d4, d2⟩ := f'.mem_val' d2
      have ⟨_, f1, f2, cf⟩ := app_core ih f b; have ⟨f3, f4, f2⟩ := f.mem_val' f2
      have ⟨_, g1, g2, dg⟩ := app_core ih f' b; have ⟨g3, g4, g2⟩ := f'.mem_val' g2
      have ⟨e, e1, e2⟩ := of_compat ih (x := ⟨_, c4⟩) (x' := ⟨_, d4⟩) (compat_app_l ih hc a)
      have ⟨k, k1, k2⟩ := of_compat ih (x := ⟨_, f4⟩) (x' := ⟨_, g4⟩) (compat_app_l ih hc b)
      refine e1 ▸ k1 ▸ (e2 _).2 ⟨?_, ?_⟩
      · exact (cf _ c2 (c1.trans (a5 ▸ b5 ▸ h1))).trans ((k2 _).1 .rfl).1
      · exact (dg _ d2 (d1.trans (a5 ▸ b5 ▸ h1))).trans ((k2 _).1 .rfl).2
  · rintro ⟨b, b3, c, c3, a1, rfl⟩
    have ⟨b1, b2, b3⟩ := f.mem_val' b3; have ⟨c1, c2, c3⟩ := f'.mem_val' c3
    have ⟨d, d1, d2⟩ := of_compat ih (x := ⟨_, b1⟩) (x' := ⟨_, c1⟩) a1
    have ⟨_, f1, f2, cf⟩ := app_core ih f d; have ⟨f3, f4, f2⟩ := f.mem_val' f2
    have ⟨_, g1, g2, dg⟩ := app_core ih f' d; have ⟨g3, g4, g2⟩ := f'.mem_val' g2
    have ⟨e, e1, e2⟩ := of_compat ih (x := ⟨_, f4⟩) (x' := ⟨_, g4⟩) (compat_app_l ih hc d)
    refine d1 ▸ e1 ▸ ⟨d.2, e.2⟩
  · intro f₃; conv =>
      enter [1,x,y,1]; (conv => apply propext WShapeFun.mem_def); simp only [ShapeFun.mem_join]
    refine ⟨fun H => ?_, fun ⟨H1, H2⟩ => ?_⟩
    · refine ⟨fun x y hf => ?_, fun x y hf' => ?_⟩
      · have ⟨_, hf'⟩ := f'.bot_mem
        have ⟨_, f1, f2, cf⟩ := app_core ih f x; have ⟨f3, f4, f2⟩ := f.mem_val' f2
        have ⟨_, g1, g2, dg⟩ := app_core ih f' x; have ⟨g3, g4, g2⟩ := f'.mem_val' g2
        have ⟨e, e1, e2⟩ := of_compat ih (x := ⟨_, f4⟩) (x' := ⟨_, g4⟩) (compat_app_l ih hc x)
        have ⟨c₁, c₂, c1, c2, c3⟩ := H ⟨_, Shape.join_bot ▸ x.2⟩ ⟨_, Shape.join_bot ▸ e1 ▸ e.2⟩
          ⟨_, hf, _, hf', Compat.bot_r, rfl⟩
        simp only [bot, Shape.join_bot] at c2 c3
        exact ⟨_, _, c1, c2, .trans ((cf _ hf .rfl).trans (e1 ▸ (show _ ≤ e.1 from ((e2 _).1 .rfl).1) :)) c3⟩
      · have ⟨_, hf⟩ := f.bot_mem
        have ⟨_, f1, f2, cf⟩ := app_core ih f x; have ⟨f3, f4, f2⟩ := f.mem_val' f2
        have ⟨_, g1, g2, dg⟩ := app_core ih f' x; have ⟨g3, g4, g2⟩ := f'.mem_val' g2
        have ⟨e, e1, e2⟩ := of_compat ih (x := ⟨_, f4⟩) (x' := ⟨_, g4⟩) (compat_app_l ih hc x)
        have ⟨c₁, c₂, c1, c2, c3⟩ := H ⟨_, Shape.bot_join ▸ x.2⟩ ⟨_, Shape.bot_join ▸ e1 ▸ e.2⟩
          ⟨_, hf, _, hf', Compat.bot_l, rfl⟩
        simp only [bot, Shape.bot_join] at c2 c3
        exact ⟨_, _, c1, c2, .trans ((dg _ hf' .rfl).trans (e1 ▸ (show _ ≤ e.1 from ((e2 _).1 .rfl).2) :)) c3⟩
    · rintro ⟨_, hx⟩ ⟨_, hy⟩ ⟨x, a3, y, b3, xy, ⟨⟩⟩
      have ⟨a1, a2, a3⟩ := f.mem_val' a3; have ⟨b1, b2, b3⟩ := f'.mem_val' b3
      have ⟨e, e1, e2⟩ := of_compat ih (x := ⟨_, a1⟩) (x' := ⟨_, b1⟩) xy
      have ⟨f₁, f1, f2, cf⟩ := app_core ih f e; have ⟨f3, f4, f2⟩ := f.mem_val' f2
      have ⟨g₁, g1, g2, dg⟩ := app_core ih f' e; have ⟨g3, g4, g2⟩ := f'.mem_val' g2
      have ⟨i, i1, i2, hi⟩ := app_core ih f₃ e; have ⟨i3, i4, i2⟩ := f₃.mem_val' i2
      have ⟨j, j1, j2⟩ := of_compat ih (x := ⟨_, f4⟩) (x' := ⟨_, g4⟩) (compat_app_l ih hc e)
      have ⟨l1, l2⟩ := (e2 _).1 .rfl
      refine ⟨_, _, i2, (e1 ▸ i1 :), ?_⟩
      simp only [WShape.LE.def, ← e1, ← j1]
      refine (j2 ⟨_, i4⟩).2 ⟨?_, ?_⟩
      · have ⟨m, m', m1, m2, m3⟩ := H1 _ _ f2; exact m3.trans (hi _ m1 (m2.trans f1))
      · have ⟨m, m', m1, m2, m3⟩ := H2 _ _ g2; exact m3.trans (hi _ m1 (m2.trans g1))

end WShape.join_prop

theorem WShape.join_prop {x y : WShape n} :
    (∀ z, x ≤ z → y ≤ z → x.Compat y) ∧
    (x.Compat y → (x.1.join y.1).WF ∧ ∀ z, x.1.join y.1 ≤ z.1 ↔ x ≤ z ∧ y ≤ z) := by
  induction n with
  | zero =>
    obtain ⟨⟨⟩, wf⟩ := x <;> obtain ⟨⟨⟩, _⟩ := y <;>
      simp +contextual [(·≤·), Compat, Shape.LE, Shape.ble, Shape.Compat, Shape.join, *]
    refine ⟨?_, (· ▸ ⟨wf, ?_⟩)⟩ <;> rintro ⟨⟨⟩⟩ <;> simp [Shape.ble]
    exact (·.trans ·.symm)
  | succ n ih
  have go {f f' : ShapeFun n} (wf : ShapeFun.WF Shape.WF f) (wf' : ShapeFun.WF Shape.WF f') :=
    @join_prop.ih_fun _ _ @ih ⟨f, wf⟩ ⟨f', wf'⟩
  let ⟨x, wf⟩ := x; let ⟨y, wf'⟩ := y
  simp only [WShape.LE.def]; simp [WShape, Compat]
  constructor
  · (cases x with | bot => exact fun _ _ _ _ => Shape.Compat.bot_l | _) <;>
    rintro ⟨⟩ wf₃ h2 h3 <;> simp [Shape.LE.def] at h2 <;>
    (cases y with | bot => exact Shape.Compat.bot_r | _) <;>
    simp [Shape.LE.def, Shape.Compat] at h3 ⊢ <;> dsimp [Shape.WF] at wf wf' wf₃
    · exact h2.trans h3.symm
    · exact ⟨(@ih ⟨_, wf.1⟩ ⟨_, wf'.1⟩).1 ⟨_, wf₃.1⟩ h2.1 h3.1,
        (go wf.2 wf'.2).1 ⟨_, wf₃.2⟩ h2.2 h3.2⟩
    · exact (go wf.1 wf'.1).1 ⟨_, wf₃.1⟩ h2 h3
    · refine ⟨h2.1.trans h3.1.symm, h2.2.and_mem.trans ?_ h3.2.and_mem.flip⟩
      rintro _ _ _ ⟨h1, h2, h3⟩ ⟨h4, h5, _⟩
      exact (@ih ⟨_, wf.1 _ h2⟩ ⟨_, wf'.1 _ h5⟩).1 ⟨_, wf₃.1 _ h3⟩ h1 h4
  · (cases x with | bot => intro; exact ⟨wf', fun _ _ => (and_iff_right Shape.bot_le).symm⟩ | _) <;>
    (cases y with | bot => intro; exact ⟨wf, fun _ _ => (and_iff_left Shape.bot_le).symm⟩ | _) <;>
    simp [Shape.WF] at wf wf' <;>
    simp +contextual [Shape.Compat, Shape.join, Shape.sort, Shape.LE.def, Shape.WF]
    · intro h1 h2
      have ⟨a1, a2⟩ := (@ih ⟨_, wf.1⟩ ⟨_, wf'.1⟩).2 h1
      have ⟨b1, b2⟩ := (go wf.2 wf'.2).2 h2
      simp only [WShape.LE.def, WShapeFun.LE.def] at a1 a2 b1 b2
      simp [WShape, WShapeFun] at a2 b2 ⊢
      refine ⟨⟨a1, b1⟩, ?_⟩
      rintro ⟨⟨⟩⟩ <;> simp +contextual [Shape.WF, and_assoc, and_left_comm, *]
    · intro h1
      have ⟨a1, a2⟩ := (go wf.1 wf'.1).2 h1
      simp only [WShapeFun.LE.def] at a1 a2; simp [WShapeFun] at a2
      exact ⟨⟨a1, wf.2.mono ((a2 _ a1).1 .rfl).1⟩, by rintro ⟨⟩ <;> simp +contextual [Shape.WF, *]⟩
    · rintro rfl H; constructor
      · have := H.and_mem.zipWith_l (f := Shape.join) (S := fun x y => x ≤ y ∧ y.WF)
          fun _ _ ⟨h1, h2⟩ =>
            have ⟨a1, a2⟩ := (@ih ⟨_, wf.1 _ h2.1⟩ ⟨_, wf'.1 _ h2.2⟩).2 h1
            ⟨((a2 ⟨_, a1⟩).1 .rfl).1, a1⟩
        refine ⟨fun _ h => ?_, fun hs => (wf.2 hs).mono <| this.imp fun _ _ => And.left⟩
        have ⟨_, h⟩ := this.forall_exists_r _ h; exact h.2.2
      · rintro ⟨⟩ <;> simp +contextual [Shape.WF, and_left_comm]; rintro wf₃ - -
        rename_i l l' _ l₃
        replace wf := wf.1; replace wf' := wf'.1
        induction l₃ generalizing l l' with cases H <;> simp | cons a₃ l₃ ihl
        have ⟨wf₁, wf₂⟩ := List.forall_mem_cons.1 wf
        have ⟨wf₁', wf₂'⟩ := List.forall_mem_cons.1 wf'
        have ⟨wf₁₃, wf₂₃⟩ := List.forall_mem_cons.1 wf₃
        rename_i h₃ H₃
        refine and_congr (((@ih ⟨_, wf₁⟩ ⟨_, wf₁'⟩).2 h₃).2 ⟨_, wf₁₃⟩)
          (ihl _ _ H₃ wf₂₃ wf₂ wf₂') |>.trans ?_
        simp [(· ≤ ·), and_comm, and_assoc, and_left_comm]

theorem WShape.Compat.iff {x y : WShape n} : x.Compat y ↔ ∃ z, x ≤ z ∧ y ≤ z := by
  refine ⟨fun h => ?_, fun ⟨_, h1, h2⟩ => WShape.join_prop.1 _ h1 h2⟩
  have ⟨_, _, h2⟩ := WShape.join_prop.of_compat WShape.join_prop h
  exact ⟨_, (h2 _).1 .rfl⟩

theorem WShape.Compat.of_le {x : WShape n} (h : x ≤ y) : x.Compat y :=
  WShape.Compat.iff.2 ⟨_, h, .rfl⟩
theorem WShape.Compat.rfl {x : WShape n} : x.Compat x := .of_le .rfl
theorem WShape.Compat.symm {x : WShape n} : x.Compat y → y.Compat x := Shape.Compat.symm

def WShape.join (a b : WShape n) : WShape n :=
  if h : a.Compat b then ⟨a.1.join b.1, (WShape.join_prop.2 h).1⟩ else .bot
def WShape.Join (x y z : WShape n) : Prop :=
  ∀ w : WShape n, z ≤ w ↔ x ≤ w ∧ y ≤ w
theorem WShape.join_val {a b : WShape n} (h : a.Compat b) : (a.join b).1 = a.1.join b.1 := by
  simp [WShape.join, h]
theorem WShape.Join.le (H : WShape.Join x y z) : x ≤ z ∧ y ≤ z := (H _).1 .rfl
theorem WShape.Join.mk (h : x.Compat y) : WShape.Join x y (x.join y) := by
  simp only [join, dif_pos h]; exact (WShape.join_prop.2 h).2

theorem WShape.Join.compat (H : WShape.Join x y z) : x.Compat y :=
  WShape.Compat.iff.2 ⟨z, (H _).1 .rfl⟩

theorem WShape.Join.iff {x y z : WShape n} :
    WShape.Join x y z ↔ x.Compat y ∧ x.join y ≤ z ∧ z ≤ x.join y := by
  refine ⟨fun h => ⟨Compat.iff.2 ⟨_, h.le⟩, ?_⟩, fun ⟨h1, h2, h3⟩ w => ?_⟩
  · exact ⟨((mk h.compat _).2 h.le), (h _).2 (mk h.compat).le⟩
  · exact ⟨fun h => (mk h1 _).1 (h2.trans h), fun h => h3.trans <| (mk h1 _).2 h⟩

theorem WShape.lift_join {x y : WShape n} (le : n ≤ m) :
    (x.join y).lift m = (x.lift m).join (y.lift m) := by
  simp [join]; split <;> rename_i h
  · rw [dif_pos ((WShape.Compat.lift le).2 h)]; ext1; simp [lift_val le, Shape.lift_join le]
  · rw [dif_neg (mt (WShape.Compat.lift le).1 h), lift_bot]

theorem WShapeFun.join_mem {f : WShapeFun n}
    (hx : (x, y) ∈ f) (hy : (x', y') ∈ f) (hc : x.Compat x') :
    ∃ z, z ∈ f ∧ x.join x' ≤ z.1 ∧ z.1 ≤ x.join x' := by
  simp only [WShape.LE.def, WShape.join_val hc, f.join_mem' hx hy hc]

@[simp] theorem WShape.bot_join {x : WShape n} : bot.join x = x := by
  ext1; rw [join_val Compat.bot_l, bot, Shape.bot_join]
@[simp] theorem WShape.join_bot {x : WShape n} : x.join bot = x := by
  ext1; rw [join_val Compat.bot_r, bot, Shape.join_bot]
@[simp] theorem WShape.sort_join_sort :
    join (.sort r : WShape n) (.sort r') = if r = r' then .sort r else .bot := by
  ext1; simp [join, WShape.Compat, sort, Shape.Compat.sort_sort]; split <;> rfl

/- The general `Shape.WF.plift` well-formedness-projection principle
(pushing a well-formed higher-level shape down to an arbitrary lower
level) was rejected and its prototype deleted: downward projection can
destroy the `NonZero`/join-closure invariants at `lam`/`ctor` nodes. The
order-theoretic `plift` lemmas above are the surviving true fragment;
transport of refinement evidence is instead carried as data by
`LRS.CtorDefEq.lift`/`.unlift` and `LogRel.LiftEquiv` below. -/

theorem WShape.Join.lift {x y z : WShape n} (le : n ≤ m) :
    (x.lift m).Join (y.lift m) (z.lift m) ↔ x.Join y z := by
  constructor
  · intro hJ w
    have := hJ (w.lift m)
    rwa [lift_le_lift le, lift_le_lift le, lift_le_lift le] at this
  · intro hJ; have ⟨h1, h2, h3⟩ := Join.iff.1 hJ
    refine Join.iff.2 ⟨(Compat.lift le).2 h1, ?_⟩
    exact lift_join le ▸ ⟨WShape.lift_mono le h2, WShape.lift_mono le h3⟩

theorem WShape.join_self {x y : WShape n} : WShape.Join x x y ↔ x ≤ y ∧ y ≤ x :=
  ⟨fun H => ⟨((H _).1 .rfl).1, (H _).2 ⟨.rfl, .rfl⟩⟩,
   fun ⟨H1, H2⟩ _ => ⟨fun h => ⟨H1.trans h, H1.trans h⟩, fun h => H2.trans h.1⟩⟩

theorem WShape.Join.left {x y : WShape n} (h : y ≤ x) : WShape.Join x y x :=
  fun _ => ⟨fun H => ⟨H, h.trans H⟩, (·.1)⟩

theorem WShape.Join.right {x y : WShape n} (h : y ≤ x) : WShape.Join y x x :=
  fun _ => ⟨fun H => ⟨h.trans H, H⟩, (·.2)⟩

def WShapeFun.Join (x y z : WShapeFun n) : Prop := ∀ w : WShapeFun n, z ≤ w ↔ x ≤ w ∧ y ≤ w

theorem WShapeFun.Join.le (H : WShapeFun.Join x y z) : x ≤ z ∧ y ≤ z := (H _).1 .rfl

def WShapeFun.join (x y : WShapeFun n) : WShapeFun n :=
  if h : x.Compat y then
    ⟨ShapeFun.join Shape.join x.1 y.1, ((WShape.join_prop.ih_fun WShape.join_prop).2 h).1⟩
  else .bot

theorem WShapeFun.join_val {x y : WShapeFun n} (H : Compat x y) :
    (x.join y).1 = x.1.join Shape.join y.1 := by simp [join, dif_pos H]

@[simp] theorem WShape.forallE_join_forallE {a a' : WShape n} {f f' : WShapeFun n}
    (hc1 : a.Compat a') (hc2 : WShapeFun.Compat f f') :
    (WShape.forallE a f).join (.forallE a' f') = .forallE (a.join a') (f.join f') := by
  have hc := Compat.forallE_forallE.2 ⟨hc1, hc2⟩
  ext1; rw [join_val hc]; simp [forallE, Shape.join, join_val hc1, WShapeFun.join_val hc2]

theorem WShapeFun.Join.mk (H : WShapeFun.Compat x y) : WShapeFun.Join x y (x.join y) := by
  simp [Join, WShapeFun.LE.def, join_val H]
  have ⟨_, h⟩ := (WShape.join_prop.ih_fun WShape.join_prop).2 H; exact h

theorem WShapeFun.Compat.iff {x y : WShapeFun n} : x.Compat y ↔ ∃ z, x ≤ z ∧ y ≤ z := by
  refine ⟨fun h => ⟨_, (Join.mk h).le⟩, fun ⟨_, h1, h2⟩ => ?_⟩
  exact (WShape.join_prop.ih_fun WShape.join_prop).1 _ h1 h2

@[simp] theorem WShapeFun.Compat.bot_l {s : WShapeFun n} : bot.Compat s := iff.2 ⟨_, bot_le, .rfl⟩
@[simp] theorem WShapeFun.Compat.bot_r {s : WShapeFun n} : s.Compat bot := iff.2 ⟨_, .rfl, bot_le⟩

theorem WShapeFun.Join.compat (H : Join x y z) : x.Compat y := Compat.iff.2 ⟨z, (H _).1 .rfl⟩

theorem WShapeFun.Join.iff :
    Join x y z ↔ x.Compat y ∧ x.join y ≤ z ∧ z ≤ x.join y := by
  refine ⟨fun h => ⟨Compat.iff.2 ⟨_, h.le⟩, ?_⟩, fun ⟨h1, h2, h3⟩ w => ?_⟩
  · exact ⟨((mk h.compat _).2 h.le), (h _).2 (mk h.compat).le⟩
  · exact ⟨fun h => (mk h1 _).1 (h2.trans h), fun h => h3.trans <| (mk h1 _).2 h⟩

theorem WShapeFun.join_mem'' {f : WShapeFun n}
    (hx : (x, y) ∈ f) (hy : (x', y') ∈ f) (hc : x.Compat x') : ∃ z, z ∈ f ∧ x.Join x' z.1 := by
  have ⟨⟨z, w⟩, h1, h2⟩ := f.join_mem' hx hy hc
  refine ⟨_, h1, WShape.Join.iff.2 ⟨hc, ?_⟩⟩
  simpa only [WShape.LE.def, WShape.join_val hc]

def WShapeFun.ofElems (f : List (WShape n × WShape n))
    (h1 : ∃ y, (WShape.bot, y) ∈ f)
    (h2 : ∀ x ∈ f, ∀ y ∈ f,
      (x.1.Compat y.1 → ∃ z ∈ f, x.1.Join y.1 z.1) ∧
      (x.1 ≤ y.1 → x.2 ≤ y.2)) : WShapeFun n := by
  refine ⟨f.map fun x => (x.1.1, x.2.1), ?_, ?_⟩
  · simp only [List.mem_map, Prod.mk.injEq]
    have ⟨_, h1⟩ := h1; refine ⟨⟨_, _, h1, rfl, rfl⟩, ?_⟩
    rintro _ ⟨⟨x, y⟩, a1, rfl⟩ ⟨x', y'⟩ ⟨⟨u, v⟩, a2, ⟨⟩⟩; dsimp
    have ⟨b1, b2⟩ := h2 _ a1 _ a2; refine ⟨fun hc => ?_, b2⟩
    have ⟨_, c1, c2⟩ := b1 hc; have := (WShape.Join.iff.1 c2).2
    simp only [WShape.LE.def, WShape.join_val hc] at this
    exact ⟨_, ⟨⟨_, _⟩, c1, rfl⟩, this⟩
  · simp; rintro _ _ x y _ rfl rfl; exact ⟨x.2, y.2⟩

theorem WShapeFun.mem_ofElems {f : List (WShape n × WShape n)} {h1 h2} :
    (x, y) ∈ WShapeFun.ofElems f h1 h2 ↔ (x, y) ∈ f := by
  show (x.1, y.1) ∈ f.map (fun p => (p.1.1, p.2.1)) ↔ _
  simp only [List.mem_map, Prod.mk.injEq]
  exact ⟨fun ⟨⟨a, b⟩, h, ha, hb⟩ => by cases WShape.ext ha; cases WShape.ext hb; exact h,
    fun h => ⟨_, h, rfl, rfl⟩⟩

@[implicit_reducible] def TShape := Σ n, WShape n
abbrev WShape.T : WShape n → TShape := Sigma.mk _

def TShape.LE (a b : TShape) : Prop := a.2.lift (max a.1 b.1) ≤ b.2.lift _
instance : _root_.LE TShape := ⟨TShape.LE⟩
theorem TShape.LE.def' {a b : TShape} : a ≤ b ↔ a.2.lift (max a.1 b.1) ≤ b.2.lift _ := .rfl

def TShapeFun.LE (a : WShapeFun n) (b : WShapeFun m) : Prop :=
  a.lift (max n m) ≤ b.lift _

theorem TShape.LE.def {a b : TShape} (h1 : a.1 ≤ m) (h2 : b.1 ≤ m) :
    a ≤ b ↔ a.2.lift m ≤ b.2.lift m := by
  refine (WShape.lift_le_lift (Nat.max_le.2 ⟨h1, h2⟩)).symm.trans ?_
  rw [WShape.lift_lift (.inl (Nat.le_max_left ..)), WShape.lift_lift (.inl (Nat.le_max_right ..))]

theorem TShapeFun.LE.def {a : WShapeFun n} {b : WShapeFun m} (h1 : n ≤ k) (h2 : m ≤ k) :
    TShapeFun.LE a b ↔ a.lift k ≤ b.lift k := by
  refine (WShapeFun.lift_le_lift (Nat.max_le.2 ⟨h1, h2⟩)).symm.trans ?_
  rw [WShapeFun.lift_lift (.inl (Nat.le_max_left ..)),
    WShapeFun.lift_lift (.inl (Nat.le_max_right ..))]

theorem TShape.LE.forallE_decomp {b : WShape n} {f : WShapeFun n} {b' : WShape n'} {f' : WShapeFun n'}
    (le : (WShape.forallE b f).T ≤ (WShape.forallE b' f').T) :
    b.lift (max n n') ≤ b'.lift (max n n') ∧
      f.lift (max n n') ≤ f'.lift (max n n') := by
  have le₁ := Nat.le_max_left n n'; have le₂ := Nat.le_max_right n n'
  have h := (TShape.LE.def (Nat.succ_le_succ le₁) (Nat.succ_le_succ le₂)).1 le
  have h_raw : ((WShape.forallE b f).lift _).1 ≤ ((WShape.forallE b' f').lift _).1 := h
  rw [WShape.lift_val (Nat.succ_le_succ le₁), WShape.lift_val (Nat.succ_le_succ le₂)] at h_raw
  simp only [WShape.forallE, Shape.lift, Shape.LE.def] at h_raw
  constructor
  · show (b.lift _).1 ≤ (b'.lift _).1
    rw [WShape.lift_val le₁, WShape.lift_val le₂]; exact h_raw.1
  · show (f.lift _).1.LE (f'.lift _).1
    rw [WShapeFun.lift_val le₁, WShapeFun.lift_val le₂]; exact h_raw.2

theorem TShape.LE.lam'_decomp {f : WShapeFun n} {f' : WShapeFun n'} :
    (WShape.lam' f).T ≤ (WShape.lam' f').T →
    f.lift (max n n') ≤ f'.lift (max n n') := by
  have le₁ := Nat.le_max_left n n'; have le₂ := Nat.le_max_right n n'
  have le₁' := Nat.succ_le_succ le₁; have le₂' := Nat.succ_le_succ le₂
  rw [TShape.LE.def le₁' le₂', WShape.LE.def, WShape.lift_val le₁', WShape.lift_val le₂',
    WShape.lam', WShape.lam']
  dsimp; split <;> rename_i hf
  · split <;> rename_i hf' <;>
      simp [WShape.lam, Shape.lift, WShapeFun.LE.def, WShapeFun.lift_val, le₁, le₂]
    intro h; cases Shape.le_bot.1 h
  · rintro -
    refine WShapeFun.LE.def'.2 fun x y h => ?_
    obtain ⟨_, _, h1, ⟨⟩, ⟨⟩⟩ := (WShapeFun.mem_lift le₁).1 h
    have := WShape.le_bot.1 <| Decidable.by_contra fun h => hf ⟨_, h1, h⟩
    dsimp at this; cases this
    have ⟨_, h⟩ := f'.bot_mem
    exact ⟨_, _, (WShapeFun.mem_lift le₂).2 ⟨_, _, h, rfl, rfl⟩, by simp⟩

theorem TShape.LE.le_lam {f : WShapeFun n} {hl} {f' : WShapeFun n'} {hl'}
    (le : (WShape.lam f hl).T ≤ (WShape.lam f' hl').T) :
    f.lift (max n n') ≤ f'.lift (max n n') := by
  have le₁ := Nat.le_max_left n n'; have le₂ := Nat.le_max_right n n'
  have h := (TShape.LE.def (Nat.succ_le_succ le₁) (Nat.succ_le_succ le₂)).1 le
  have h_raw : ((WShape.lam f hl).lift _).1 ≤ ((WShape.lam f' hl').lift _).1 := h
  rw [WShape.lift_val (Nat.succ_le_succ le₁), WShape.lift_val (Nat.succ_le_succ le₂)] at h_raw
  simp only [WShape.lam, Shape.lift, Shape.LE.def] at h_raw
  show (f.lift _).1.LE (f'.lift _).1
  rw [WShapeFun.lift_val le₁, WShapeFun.lift_val le₂]; exact h_raw

def TShape.bot : TShape := WShape.T (n := 0) .bot
def TShape.sort (r : Bool) : TShape := WShape.T (n := 0) (.sort r)
def TShape.type : TShape := .sort true

nonrec theorem TShape.LE.rfl {a : TShape} : a ≤ a := WShape.LE.rfl

theorem TShape.LE.trans {a b c : TShape} (h1 : a ≤ b) (h2 : b ≤ c) : a ≤ c := by
  let k := max (max a.1 b.1) c.1
  have hk := Nat.max_le.1 (Nat.le_refl k); rw [Nat.max_le] at hk
  exact (LE.def hk.1.1 hk.2).2 (.trans ((LE.def hk.1.1 hk.1.2).1 h1) ((LE.def hk.1.2 hk.2).1 h2))

theorem TShape.LE.lift_l {a b : TShape} (h1 : a.1 ≤ b.1) : a ≤ b ↔ a.2.lift (b.1) ≤ b.2 :=
  (LE.def h1 (Nat.le_refl _)).trans (WShape.lift_self ▸ .rfl)
theorem TShape.LE.lift_r {a b : TShape} (h1 : b.1 ≤ a.1) : a ≤ b ↔ a.2 ≤ b.2.lift (a.1) :=
  (LE.def (Nat.le_refl _) h1).trans (WShape.lift_self ▸ .rfl)
theorem WShape.LE.T_iff {a b : WShape n} : a.T ≤ b.T ↔ a ≤ b :=
  (TShape.LE.lift_l (Nat.le_refl _) (a := a.T) (b := b.T)).trans (WShape.lift_self ▸ .rfl)
theorem WShape.LE.T {a b : WShape n} : a ≤ b → a.T ≤ b.T := T_iff.2
theorem WShape.LE.of_T {a b : WShape n} : a.T ≤ b.T → a ≤ b := T_iff.1

theorem TShape.bot_eqv : (WShape.bot (n := n)).T ≤ bot ∧ bot ≤ (WShape.bot (n := n)).T := by
  simp [TShape.LE.def', bot, WShape.lift_bot]

theorem TShape.bot_le' : (WShape.bot (n := n)).T ≤ a := by
  simp [TShape.LE.def', WShape.lift_bot]

theorem TShape.bot_le {a : TShape} : bot ≤ a := bot_le'

theorem TShape.le_bot {a : TShape} : a ≤ bot ↔ a.2 = .bot := by
  simp [TShape.LE.def', bot, WShape.lift_le_bot (Nat.le_max_left ..), WShape.lift_bot]

theorem TShape.le_bot' {a : TShape} : a ≤ bot ↔ a = WShape.T (n := a.1) .bot := by
  rw [le_bot]; let ⟨n, s⟩ := a
  exact ⟨fun h => congrArg (Sigma.mk n) h, fun h => Sigma.mk.inj h |>.2 |> eq_of_heq⟩

theorem TShape.lift_eqv {a : TShape} (h : a.1 ≤ m) :
    (a.2.lift m).T ≤ a ∧ a ≤ (a.2.lift m).T := by
  simp [TShape.LE.def', WShape.lift_lift (.inl h), WShape.LE.rfl]

theorem TShape.sort_eqv :
    (WShape.sort (n := n) r).T ≤ .sort r ∧ .sort r ≤ (WShape.sort (n := n) r).T := by
  simp [sort, TShape.LE.def', WShape.lift_sort, WShape.LE.rfl]

theorem TShape.sort_not_le_lam' {f : WShapeFun n'} :
    ¬(.sort r : WShape n).T ≤ (WShape.lam' f).T := by
  rw [TShape.LE.def']; simp only [WShape.T, WShape.lift_sort]
  intro h; have h := congrArg (·.1) (WShape.sort_le.1 h)
  simp only [WShape.sort, WShape.lam'] at h; split at h <;>
  · simp only [WShape.lam, WShape.bot, WShape.lift_val (Nat.le_max_right ..)] at h
    have hk : max n (n' + 1) = max n (n' + 1) - 1 + 1 := by omega
    rw [hk] at h; simp [Shape.sort, Shape.lift, Shape.bot] at h

theorem TShape.forallE_not_le_lam' {a : WShape n} {f₁ : WShapeFun n} {f₂ : WShapeFun n'} :
    ¬(.forallE a f₁ : WShape (n+1)).T ≤ (WShape.lam' f₂).T := by
  have' le₁ := Nat.le_max_left ..; have' le₂ := Nat.le_max_right ..
  rw [TShape.LE.def (Nat.succ_le_succ le₁) (Nat.succ_le_succ le₂),
    WShape.lift_forallE le₁, WShape.lift_lam' le₂]
  intro hle; have ⟨_, _, _, _, hle⟩ := WShape.forallE_le.1 hle
  unfold WShape.lam' at hle; split at hle <;>
    simp [WShape.ext_iff, WShape.forallE, WShape.lam] at hle
  cases hle

theorem TShape.ctor_not_le_lam' {c : Name} {l : List (WShape n)} {h} {f : WShapeFun n'} :
    ¬(WShape.ctor c l h : WShape (n+1)).T ≤ (WShape.lam' f).T := by
  have' le₁ := Nat.le_max_left ..; have' le₂ := Nat.le_max_right ..
  rw [TShape.LE.def (Nat.succ_le_succ le₁) (Nat.succ_le_succ le₂),
    WShape.lift_ctor le₁, WShape.lift_lam' le₂]
  intro hle
  unfold WShape.lam' at hle; split at hle <;>
    simp_all [WShape.LE.def, WShape.ctor, WShape.lam, WShape.bot, Shape.LE.def]

theorem TShape.indTy_not_le_lam' {f : WShapeFun n'} :
    ¬(WShape.indTy : WShape (n+1)).T ≤ (WShape.lam' f).T := by
  rw [TShape.LE.def (Nat.succ_le_succ (Nat.le_max_left ..))
    (Nat.succ_le_succ (Nat.le_max_right ..)), WShape.lift_indTy,
    WShape.lift_lam' (Nat.le_max_right ..), WShape.indTy_le]
  unfold WShape.lam'; split <;> rintro ⟨⟩

theorem TShape.indTy_not_le_ctor' {c : Name} {l : List (WShape n')} :
    ¬(WShape.indTy : WShape (n+1)).T ≤ (WShape.ctor' c l).T := by
  intro h
  rw [TShape.LE.def (m := max n n' + 1)
      (Nat.succ_le_succ (Nat.le_max_left ..))
      (Nat.succ_le_succ (Nat.le_max_right ..)),
    WShape.lift_indTy (n := n) (m := max n n'),
    WShape.lift_ctor' (Nat.le_max_right ..), WShape.indTy_le] at h
  unfold WShape.ctor' at h
  split at h <;> simp_all [WShape.ext_iff, WShape.ctor, WShape.bot,
    WShape.indTy, Shape.bot]

theorem TShape.lam_not_le_forallE {f₁ : WShapeFun n} {hl} {a' : WShape n'} {f' : WShapeFun n'} :
    ¬(.lam f₁ hl : WShape (n+1)).T ≤ (.forallE a' f' : WShape (n'+1)).T := by
  have' le₁ := Nat.le_max_left ..; have' le₂ := Nat.le_max_right ..
  rw [TShape.LE.def (Nat.succ_le_succ le₁) (Nat.succ_le_succ le₂),
    WShape.lift_lam le₁, WShape.lift_forallE le₂]
  simp [(· ≤ ·), Shape.LE, Shape.ble, WShape.lam, WShape.forallE]

theorem TShape.sort_not_le_forallE {a' : WShape n'} {f' : WShapeFun n'} :
    ¬(.sort r : WShape n).T ≤ (.forallE a' f' : WShape (n'+1)).T := by
  rw [TShape.LE.def']; simp only [WShape.T, WShape.lift_sort]
  intro h; have h := congrArg (·.1) (WShape.sort_le.1 h)
  simp only [WShape.sort, WShape.forallE, WShape.lift_val (Nat.le_max_right ..)] at h
  have hk : max n (n' + 1) = max n (n' + 1) - 1 + 1 := by omega
  rw [hk] at h; simp [Shape.sort, Shape.lift] at h

theorem TShape.sort_not_le_ctor' {c : Name} {l : List (WShape n')} :
    ¬(.sort r : WShape n).T ≤ (WShape.ctor' c l).T := by
  rw [TShape.LE.def']; simp only [WShape.T, WShape.lift_sort]
  intro h; have h := congrArg (·.1) (WShape.sort_le.1 h)
  simp only [WShape.sort, WShape.ctor', WShape.lift_val (Nat.le_max_right ..)] at h
  split at h
  · simp only [WShape.ctor] at h
    have hk : max n (n' + 1) = max n (n' + 1) - 1 + 1 := by omega
    rw [hk] at h; simp [Shape.sort, Shape.lift] at h
  · simp only [WShape.bot] at h
    have hk : max n (n' + 1) = max n (n' + 1) - 1 + 1 := by omega
    rw [hk] at h; simp [Shape.sort, Shape.lift, Shape.bot] at h

theorem TShape.forallE_not_le_ctor' {a : WShape n} {f : WShapeFun n}
    {c : Name} {l : List (WShape n')} :
    ¬(.forallE a f : WShape (n+1)).T ≤ (WShape.ctor' c l).T := by
  have' le₁ := Nat.le_max_left ..; have' le₂ := Nat.le_max_right ..
  rw [TShape.LE.def (Nat.succ_le_succ le₁) (Nat.succ_le_succ le₂),
    WShape.lift_forallE le₁, WShape.lift_ctor' le₂]
  intro hle; have ⟨_, _, _, _, hle⟩ := WShape.forallE_le.1 hle
  unfold WShape.ctor' at hle; split at hle
  · simp [WShape.ext_iff, WShape.forallE, WShape.ctor] at hle
  · have := congrArg (·.1) hle
    simp only [WShape.forallE, WShape.bot, Shape.bot] at this
    cases this

theorem TShape.lam_not_le_ctor' {f : WShapeFun n} {hl}
    {c : Name} {l : List (WShape n')} :
    ¬(.lam f hl : WShape (n+1)).T ≤ (WShape.ctor' c l).T := by
  have' le₁ := Nat.le_max_left ..; have' le₂ := Nat.le_max_right ..
  rw [TShape.LE.def (Nat.succ_le_succ le₁) (Nat.succ_le_succ le₂),
    WShape.lift_lam le₁, WShape.lift_ctor' le₂]
  unfold WShape.ctor'; split <;>
    simp [(· ≤ ·), Shape.LE, Shape.ble, WShape.lam, WShape.ctor, WShape.bot]

theorem TShape.indTy_not_le_forallE {a' : WShape n'} {f' : WShapeFun n'} :
    ¬(WShape.indTy : WShape (n+1)).T ≤ (.forallE a' f' : WShape (n'+1)).T := by
  rw [TShape.LE.def (Nat.succ_le_succ (Nat.le_max_left ..))
    (Nat.succ_le_succ (Nat.le_max_right ..)),
    WShape.lift_indTy, WShape.lift_forallE (Nat.le_max_right ..), WShape.indTy_le]
  rintro ⟨⟩

theorem TShape.indTy_not_le_sort :
    ¬(WShape.indTy : WShape (n+1)).T ≤ (.sort r : WShape n').T := by
  intro h
  have := h.trans TShape.sort_eqv.1
  rw [TShape.LE.def (Nat.le_refl _) (Nat.zero_le _), WShape.lift_self, WShape.indTy_le] at this
  cases this

theorem TShape.sort_not_le_indTy :
    ¬(.sort r : WShape n).T ≤ (WShape.indTy : WShape (n'+1)).T := by
  intro h
  have le₁ : n ≤ n + n' + 1 := by omega
  have le₂ : n' + 1 ≤ n + n' + 1 := by omega
  rw [TShape.LE.def (m := n + n' + 1) le₁ le₂, WShape.lift_sort,
    WShape.lift_indTy (n := n') (m := n + n'), WShape.le_indTy] at h
  simp [WShape.ext_iff, WShape.sort, WShape.bot, WShape.indTy,
    Shape.sort, Shape.bot] at h

theorem TShape.forallE_not_le_indTy {a : WShape n} {f : WShapeFun n} :
    ¬(.forallE a f : WShape (n+1)).T ≤ (WShape.indTy : WShape (n'+1)).T := by
  intro h
  rw [TShape.LE.def (m := max n n' + 1)
      (Nat.succ_le_succ (Nat.le_max_left ..))
      (Nat.succ_le_succ (Nat.le_max_right ..)),
    WShape.lift_forallE (Nat.le_max_left ..),
    WShape.lift_indTy (n := n') (m := max n n'), WShape.le_indTy] at h
  simp [WShape.ext_iff, WShape.forallE, WShape.bot, WShape.indTy, Shape.bot] at h

theorem TShape.lam_not_le_indTy {f : WShapeFun n} {hl : f.NonZero} :
    ¬(.lam f hl : WShape (n+1)).T ≤ (WShape.indTy : WShape (n'+1)).T := by
  intro h
  rw [TShape.LE.def (m := max n n' + 1)
      (Nat.succ_le_succ (Nat.le_max_left ..))
      (Nat.succ_le_succ (Nat.le_max_right ..)),
    WShape.lift_lam (Nat.le_max_left ..),
    WShape.lift_indTy (n := n') (m := max n n'), WShape.le_indTy] at h
  simp [WShape.ext_iff, WShape.lam, WShape.bot, WShape.indTy, Shape.bot] at h

theorem TShape.ctor_not_le_indTy {c : Name} {l : List (WShape n)} {wf} :
    ¬(.ctor c l wf : WShape (n+1)).T ≤ (WShape.indTy : WShape (n'+1)).T := by
  intro h
  rw [TShape.LE.def (m := max n n' + 1)
      (Nat.succ_le_succ (Nat.le_max_left ..))
      (Nat.succ_le_succ (Nat.le_max_right ..)),
    WShape.lift_ctor (Nat.le_max_left ..),
    WShape.lift_indTy (n := n') (m := max n n'), WShape.le_indTy] at h
  simp [WShape.ext_iff, WShape.ctor, WShape.bot, WShape.indTy, Shape.bot] at h

theorem WShape.Compat_lift_val {a : WShape n₁} {b : WShape n₂}
    (le₁ : n₁ ≤ m) (le₂ : n₂ ≤ m) :
    (a.lift m).Compat (b.lift m) ↔ (a.1.lift m).Compat (b.1.lift m) := by
  show (a.lift m).1.Compat (b.lift m).1 ↔ _
  rw [lift_val le₁, lift_val le₂]

def TShape.Compat (x y : TShape) : Prop := (x.2.lift (max x.1 y.1)).Compat (y.2.lift _)

theorem TShape.Compat.def {x y : TShape} (h1 : x.1 ≤ m) (h2 : y.1 ≤ m) :
    x.Compat y ↔ (x.2.lift m).Compat (y.2.lift _) := by
  refine (WShape.Compat.lift (Nat.max_le.2 ⟨h1, h2⟩)).symm.trans ?_
  rw [WShape.lift_lift (.inl (Nat.le_max_left ..)), WShape.lift_lift (.inl (Nat.le_max_right ..))]

theorem WShape.Compat.T_iff {x y : WShape n} : x.Compat y ↔ x.T.Compat y.T := by
  refine .trans ?_ (TShape.Compat.def (x := x.T) (y := y.T) (Nat.le_refl _) (Nat.le_refl _)).symm
  rw [WShape.lift_self, WShape.lift_self]

theorem WShape.Compat.T {x y : WShape n} : x.Compat y → x.T.Compat y.T := T_iff.1

theorem TShape.Compat.def' {x y : TShape} : x.Compat y ↔ ∃ z, x ≤ z ∧ y ≤ z := by
  refine ⟨fun h => ?_, fun ⟨z, h1, h2⟩ => ?_⟩
  · have ⟨z, h1, h2⟩ := WShape.Compat.iff.1 h
    exact ⟨z.T, (LE.lift_l (Nat.le_max_left ..)).2 h1, (LE.lift_l (Nat.le_max_right ..)).2 h2⟩
  · let k := max x.1 (max y.1 z.1); have hk := Nat.max_le.1 (Nat.le_refl k); rw [Nat.max_le] at hk
    exact (TShape.Compat.def hk.1 hk.2.1).2 <|
      WShape.Compat.iff.2 ⟨z.2.lift k, (LE.def hk.1 hk.2.2).1 h1, (LE.def hk.2.1 hk.2.2).1 h2⟩

theorem TShape.Compat.bot_l : TShape.bot.Compat x :=
  TShape.Compat.def'.2 ⟨x, TShape.bot_le, .rfl⟩

theorem TShape.Compat.bot_r : Compat x TShape.bot :=
  TShape.Compat.def'.2 ⟨x, .rfl, TShape.bot_le⟩

theorem TShape.Compat.bot_l' : (WShape.bot (n := n)).T.Compat x :=
  TShape.Compat.def'.2 ⟨x, TShape.bot_le', .rfl⟩

theorem TShape.Compat.bot_r' : Compat x (WShape.bot (n := n)).T :=
  TShape.Compat.def'.2 ⟨x, .rfl, TShape.bot_le'⟩

theorem NonZero.not_iff {f : WShapeFun n} : ¬f.NonZero ↔ f ≤ .bot := by
  simp only [WShapeFun.NonZero, ShapeFun.NonZero, Prod.exists, not_exists, not_and,
    Decidable.not_not, WShapeFun.bot, ShapeFun.bot, WShapeFun.LE.def, ShapeFun.LE.def,
    List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false, and_assoc, exists_and_left,
    exists_eq_left, Shape.bot_le, true_and]

theorem NonZero.iff {f : WShapeFun n} : f.NonZero ↔ ¬f ≤ .bot :=
  (Decidable.not_iff_comm.1 NonZero.not_iff).symm

theorem WShapeFun.NonZero.join {f f' : WShapeFun n} (h : f.Compat f') :
    (f.join f').NonZero ↔ f.NonZero ∨ f'.NonZero := by
  refine ⟨fun hjoin => ?_, ?_⟩
  · by_cases h1 : f.NonZero <;> [exact .inl h1; skip]
    by_cases h2 : f'.NonZero <;> [exact .inr h2; skip]
    refine (SExpr.NonZero.iff.1 hjoin ?_).elim
    exact (WShapeFun.Join.mk h _).2 ⟨SExpr.NonZero.not_iff.1 h1, SExpr.NonZero.not_iff.1 h2⟩
  · rintro (h1 | h1) <;> refine SExpr.NonZero.iff.2 fun hbot => SExpr.NonZero.iff.1 h1 ?_
    · exact ((WShapeFun.Join.mk h _).1 hbot).1
    · exact ((WShapeFun.Join.mk h _).1 hbot).2

theorem WShape.Compat.mono {x y x' y' : WShape n}
    (h1 : x ≤ x') (h2 : y ≤ y') (H : x'.Compat y') : x.Compat y :=
  have ⟨_, a1, a2⟩ := WShape.Compat.iff.1 H
  WShape.Compat.iff.2 ⟨_, h1.trans a1, h2.trans a2⟩

theorem WShapeFun.Compat.mono {x y x' y' : WShapeFun n}
    (h1 : x ≤ x') (h2 : y ≤ y') (H : x'.Compat y') : x.Compat y :=
  have ⟨_, a1, a2⟩ := WShapeFun.Compat.iff.1 H
  WShapeFun.Compat.iff.2 ⟨_, h1.trans a1, h2.trans a2⟩

theorem TShape.Compat.mono {x y x' y' : TShape}
    (h1 : x ≤ x') (h2 : y ≤ y') (H : x'.Compat y') : x.Compat y := by
  let k := max (max x.1 y.1) (max x'.1 y'.1)
  have hk := Nat.max_le.1 (Nat.le_refl k); simp only [Nat.max_le] at hk
  have h1 := (TShape.LE.def hk.1.1 hk.2.1).1 h1
  have h2 := (TShape.LE.def hk.1.2 hk.2.2).1 h2
  have H := (TShape.Compat.def hk.2.1 hk.2.2).1 H
  exact (TShape.Compat.def hk.1.1 hk.1.2).2 <| H.mono h1 h2

theorem WShape.Compat.lam' {a b : WShapeFun n} : Compat (.lam' a) (.lam' b) ↔ a.Compat b := by
  rw [WShape.lam']; split <;> rename_i h1
  · rw [WShape.lam']; split <;> [rfl; rename_i h2]
    simp; exact .mono .rfl (NonZero.not_iff.1 h2) .bot_r
  · simp; exact .mono (NonZero.not_iff.1 h1) .rfl .bot_l

theorem WShape.Join.lam' {a b c : WShapeFun n} :
    Join (.lam' a) (.lam' b) (.lam' c) ↔ a.Join b c := by
  refine ⟨fun H z => by simpa [lam'_le_lam'] using H (.lam' z), fun H z => ?_⟩
  by_cases hz : ∃ z', .lam' z' = z
  · obtain ⟨z', rfl⟩ := hz; simp only [lam'_le_lam', H _]
  have {x} : WShape.lam' x ≤ z ↔ x ≤ .bot := by
    unfold WShape.lam'; split <;> rename_i h
    · simp [← NonZero.not_iff, h, WShape.LE.def, lam, Shape.lam_le]
      obtain ⟨_, wf⟩ := z; rintro _ h1 ⟨⟩; refine hz ⟨⟨_, wf.1⟩, ?_⟩
      rw [WShape.lam', dif_pos (by exact wf.2)]; rfl
    · simp [NonZero.not_iff.1 h]
  simp only [this, H _]

theorem WShape.ctor'_join {l l' : List (WShape n)} {c : Name}
    (h : List.Forall₂ Compat l l') :
    (WShape.ctor' c l).join (WShape.ctor' c l') = WShape.ctor' c (l.zipWith join l') := by
  have key : (IsStruct c = true → ListNonZero (l.zipWith join l')) ↔
      (IsStruct c = true → ListNonZero l) ∨ (IsStruct c = true → ListNonZero l') := by
    suffices ListNonZero (l.zipWith join l') ↔ ListNonZero l ∨ ListNonZero l' by
      rw [this]
      by_cases hIs : IsStruct c <;> simp [hIs]
    induction h with | nil => simp [ListNonZero] | @cons x y L L' hh _ ih
    have hcompat_join : ¬(x.join y).1 ≤ .bot ↔ ¬x.1 ≤ .bot ∨ ¬y.1 ≤ .bot := by
      have hJ := WShape.Join.mk hh .bot
      simp only [WShape.LE.def, WShape.bot] at hJ
      rw [hJ]
      by_cases hx : x.1 ≤ .bot <;> by_cases hy : y.1 ≤ .bot <;> simp [hx, hy]
    simp only [List.zipWith, ListNonZero, List.mem_cons]
    constructor
    · rintro ⟨z, (rfl | hzL), hznz⟩
      · rcases hcompat_join.mp hznz with hh | hh
        · exact .inl ⟨x, .inl rfl, hh⟩
        · exact .inr ⟨y, .inl rfl, hh⟩
      · rcases ih.mp ⟨z, hzL, hznz⟩ with ⟨z', hz'L, hz'nz⟩ | ⟨z', hz'L, hz'nz⟩
        · exact .inl ⟨z', .inr hz'L, hz'nz⟩
        · exact .inr ⟨z', .inr hz'L, hz'nz⟩
    · rintro (⟨z, (rfl | hzL), hznz⟩ | ⟨z, (rfl | hzL), hznz⟩)
      · exact ⟨_, .inl rfl, hcompat_join.mpr (.inl hznz)⟩
      · obtain ⟨w, hwL, hwnz⟩ := ih.mpr (.inl ⟨z, hzL, hznz⟩)
        exact ⟨w, .inr hwL, hwnz⟩
      · exact ⟨_, .inl rfl, hcompat_join.mpr (.inr hznz)⟩
      · obtain ⟨w, hwL, hwnz⟩ := ih.mpr (.inr ⟨z, hzL, hznz⟩)
        exact ⟨w, .inr hwL, hwnz⟩
  ext1; rw [join_val (Compat.ctor'_ctor' h)]
  unfold WShape.ctor'; split <;> rename_i h1 <;> split <;> rename_i h2
  · rw [dif_pos (key.mpr (.inl h1))]; simp [ctor, Shape.join]
    congr 1; clear h1 h2 key
    induction h with
    | nil => rfl
    | @cons x y L L' hh _ ih => simp [WShape.join_val hh, ih]
  · rw [dif_pos (key.mpr (.inl h1))]; simp [ctor, bot, Shape.join_bot]
    have h2' : ∀ x ∈ l', x.1 ≤ Shape.bot := by simpa [ListNonZero] using fun hNZ => h2 fun _ => hNZ
    congr 1; clear h1 h2 key
    induction h with | nil => rfl | @cons x y L L' hh _ ih
    have hy_bot : y.1 = .bot := Shape.le_bot.1 (h2' y (.head _))
    simp [WShape.join_val hh, hy_bot, Shape.join_bot]
    exact ih (fun z hz => h2' z (.tail _ hz))
  · rw [dif_pos (key.mpr (.inr h2))]; simp [ctor, bot, Shape.bot_join]
    have h1' : ∀ x ∈ l, x.1 ≤ Shape.bot := by
      have ⟨_, hNZ⟩ := Decidable.not_imp_iff_and_not.1 h1
      simp [ListNonZero] at hNZ; exact hNZ
    congr 1; clear h1 h2 key
    induction h with | nil => rfl | @cons x y L L' hh _ ih
    have hx_bot : x.1 = .bot := Shape.le_bot.1 (h1' x (.head _))
    simp [WShape.join_val hh, hx_bot, Shape.bot_join]
    exact ih fun z hz => h1' z (.tail _ hz)
  · rw [dif_neg fun hh => (key.mp hh).elim h1 h2]; rfl

theorem WShape.ctor_le :
    WShape.ctor c l h ≤ s ↔ ∃ l' h', s = WShape.ctor c l' h' ∧ l.Forall₂ (· ≤ ·) l' := by
  simp [ctor, WShape.LE.def, WShape.ext_iff]
  cases s using WShape.casesOn' <;>
    simp [bot, sort, forallE, lam, ctor, indTy, Shape.bot, Shape.sort, Shape.LE.def]
  rename_i l₁ wf; refine ⟨fun ⟨rfl, h2⟩ => ⟨_, rfl, wf, h2⟩, fun ⟨_, h1, _, h3⟩ => ?_⟩
  injection h1 with eq1 eq2
  rw [← List.forall₂_map_right_iff, eq2, List.forall₂_map_right_iff]
  exact ⟨eq1.symm, h3⟩

theorem WShape.ctor'_le : WShape.ctor' c l ≤ s ↔
    ((IsStruct c → ListNonZero l) → ∃ l' h', s = WShape.ctor c l' h' ∧ l.Forall₂ (· ≤ ·) l') := by
  unfold ctor'; split <;> rename_i h1 <;> simp [eq_true h1, h1, WShape.ctor_le]

theorem WShape.ctor'_le_ctor' (h : List.Forall₂ (· ≤ ·) l l') :
    WShape.ctor' c l ≤ WShape.ctor' c l' := by
  unfold ctor'
  split <;> rename_i h1 <;> [skip; exact WShape.bot_le]
  rw [dif_pos (WShape.ListNonZero.mono h ∘ h1)]
  exact Shape.LE.def.2 ⟨rfl, by simpa⟩

theorem TShape.ctor_le_ctor'_nil
    {c c' : Name} {l : List (WShape n)} {h} {n' : Nat}
    (hcl : Params.classify c' = some (.ctor 0))
    (hle : (WShape.ctor c l h : WShape (n+1)).T ≤
      (WShape.ctor' c' ([] : List (WShape n'))).T) : c = c' ∧ l = [] := by
  have le₁ := Nat.le_max_left n n'
  have le₂ := Nat.le_max_right n n'
  rw [TShape.LE.def (Nat.succ_le_succ le₁) (Nat.succ_le_succ le₂),
    WShape.lift_ctor le₁, WShape.lift_ctor' le₂] at hle
  unfold WShape.ctor' at hle
  rw [dif_pos (by simpa [IsStruct, hcl])] at hle
  rw [WShape.ctor_le] at hle
  obtain ⟨l', h', heq, hargs⟩ := hle
  have ⟨hc, hl'⟩ := WShape.ctor.inj.1 heq
  cases hl'
  have hnil : l = [] := by
    cases l with
    | nil => rfl
    | cons => cases hargs
  exact ⟨hc.symm, hnil⟩

theorem TShape.ctor_not_le_forallE :
    ¬(WShape.ctor c l h : WShape (n+1)).T ≤ (.forallE a' f' : WShape (n'+1)).T := fun h => by
  rw [TShape.LE.def (Nat.succ_le_succ (Nat.le_max_left ..))
    (Nat.succ_le_succ (Nat.le_max_right ..)), WShape.lift_ctor (Nat.le_max_left ..),
    WShape.lift_forallE (Nat.le_max_right ..), WShape.ctor_le] at h; obtain ⟨_, _, ⟨⟩, _⟩ := h

theorem WShape.le_zipWith_join (hc : List.Forall₂ WShape.Compat l l') :
    l.Forall₂ (· ≤ ·) (l.zipWith WShape.join l') ∧
    l'.Forall₂ (· ≤ ·) (l.zipWith WShape.join l') := by
  induction hc with | nil => exact ⟨.nil, .nil⟩ | cons h _ ih
  have h := (WShape.Join.mk h).le; exact ⟨.cons h.1 ih.1, .cons h.2 ih.2⟩

def TShape.join (x y : TShape) : TShape := ⟨max x.1 y.1, (x.2.lift _).join (y.2.lift _)⟩

theorem TShape.lift_join {x y : TShape} (h1 : x.1 ≤ m) (h2 : y.1 ≤ m) :
    (x.join y).2.lift m = (x.2.lift m).join (y.2.lift m) := by
  simp [join, WShape.lift_join (Nat.max_le.2 ⟨h1, h2⟩), WShape.lift_lift (.inl (Nat.le_max_left ..)),
    WShape.lift_lift (.inl (Nat.le_max_right ..))]

theorem WShape.T_join {a b : WShape n} : a.T.join b.T = (a.join b).T := by
  rw [TShape.join, Nat.max_self n]; simp [lift_self]

def TShape.Join (x y z : TShape) := ∀ w, z ≤ w ↔ x ≤ w ∧ y ≤ w

theorem TShape.Join.le (H : Join x y z) : x ≤ z ∧ y ≤ z := (H _).1 .rfl

theorem TShape.Join.def (h1 : x.1 ≤ m) (h2 : y.1 ≤ m) (h3 : z.1 ≤ m) :
    Join x y z ↔ WShape.Join (x.2.lift m) (y.2.lift m) (z.2.lift m) := by
  constructor <;> intro hJ w
  · have hle : m ≤ m := Nat.le_refl m
    have := hJ (⟨m, w⟩ : TShape)
    rwa [TShape.LE.def h3 hle, TShape.LE.def h1 hle, TShape.LE.def h2 hle, WShape.lift_self] at this
  · let k := max m w.1
    have hk : m ≤ k := Nat.le_max_left ..
    have hwk : w.1 ≤ k := Nat.le_max_right ..
    rw [TShape.LE.def (Nat.le_trans h3 hk) hwk, TShape.LE.def (Nat.le_trans h1 hk) hwk,
      TShape.LE.def (Nat.le_trans h2 hk) hwk, ← WShape.lift_lift (.inl h3),
      ← WShape.lift_lift (.inl h1), ← WShape.lift_lift (.inl h2)]
    exact (WShape.Join.lift hk |>.2 hJ) _

theorem WShape.Join.T_iff {x y z : WShape n} : WShape.Join x y z ↔ TShape.Join x.T y.T z.T := by
  refine .symm <| (TShape.Join.def (x := x.T) (y := y.T) (z := z.T)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)).trans ?_
  rw [WShape.lift_self, WShape.lift_self, WShape.lift_self]

theorem WShape.Join.T {x y z : WShape n} : Join x y z → TShape.Join x.T y.T z.T := T_iff.1

theorem TShape.Join.mk (H : x.Compat y) : Join x y (x.join y) := by
  let m := max x.1 y.1; have ⟨hx, hy⟩ := Nat.max_le.1 (Nat.le_refl m)
  rw [TShape.Join.def hx hy (Nat.le_refl _), TShape.lift_join hx hy]
  exact .mk ((TShape.Compat.def hx hy).1 H)

theorem ShapeFun.WF.bot_le (wf : WF Shape.WF f) : ShapeFun.bot.LE f := by
  simp [ShapeFun.LE.def, bot]
  exact ⟨.bot, wf.1.1, Shape.bot_le⟩

theorem Shape.WF.lam_non_bot (wf : WF (n := n+1) (.lam f)) : ∃ x y, (x, y) ∈ f ∧ y ≠ .bot :=
  have ⟨⟨_, _⟩, h1, h2⟩ := wf.2; ⟨_, _, h1, mt Shape.le_bot.2 h2⟩

omit [Params] in
theorem ShapeFun.app_core (f : ShapeFun n) (x) :
    f.app x = .bot ∨ ∃ x', x' ≤ x ∧ (x', f.app x) ∈ f ∧ ∀ y ∈ f, y.1 ≤ x → y.1 ≤ x' := by
  refine let P := _; let f' := f.trunc x; (?_ :
    let y' := ((f'.find? P).getD (.bot, .bot)).2
    y' = .bot ∨ ∃ x', x' ≤ x ∧ (x', y') ∈ f ∧ ∀ y ∈ f, y.1 ≤ x → y.1 ≤ x')
  cases h : f'.find? P <;> simp
  have := List.find?_some h; simp [P, mem_trunc] at this ⊢
  have ⟨h1, h2⟩ := mem_trunc.1 <| List.mem_of_find?_eq_some h
  refine .inr ⟨_, h2, h1, this⟩

theorem ShapeFun.WF.app {f : ShapeFun n} (wf : WF Shape.WF f) (wfa : a.WF) : (ShapeFun.app f a).WF := by
  have ⟨_, _, h, _⟩ := WShape.join_prop.app_core WShape.join_prop ⟨_, wf⟩ ⟨_, wfa⟩
  exact (wf.2 _ h).2

def WShapeFun.app (f : WShapeFun n) (a : WShape n) : WShape n :=
  ⟨ShapeFun.app f.1 a.1, f.2.app a.2⟩

theorem WShapeFun.app_core (f : WShapeFun n) (x) :
    ∃ x', x' ≤ x ∧ (x', f.app x) ∈ f ∧ ∀ y ∈ f, y.1 ≤ x → y.2 ≤ f.app x := by
  have ⟨_, h1, h2, h3⟩ := WShape.join_prop.app_core WShape.join_prop f x
  exact ⟨_, h1, f.mem_val h2, fun _ a1 => h3 _ (f.mem_val a1)⟩

theorem WShapeFun.Compat.app_l {f f' : WShapeFun n} :
    f.Compat f' → ∀ x, (f.app x).Compat (f'.app x) := WShape.join_prop.compat_app_l WShape.join_prop

theorem WShape.Compat.app_r (f : WShapeFun n) :
    x.Compat x' → (f.app x).Compat (f.app x') := WShape.join_prop.compat_app_r WShape.join_prop

omit [Params] in
@[simp] theorem ShapeFun.bot_app : (@ShapeFun.bot n).app x = .bot := by
  simp [ShapeFun.bot, ShapeFun.app, ShapeFun.maxBelow, trunc]

def Shape.app : Shape (n + 1) → Shape n → Shape n
  | .lam f, x => ShapeFun.app f x
  | _, _ => .bot

omit [Params] in
@[simp] theorem Shape.bot_app : (@Shape.bot (n+1)).app x = .bot := rfl

omit [Params] in
@[simp] theorem Shape.lift_app (le : n ≤ m) :
    (app f a : Shape n).lift m = app (f.lift _) (a.lift _) := by
  cases f <;> simp [app, lift, ShapeFun.lift_app le]

def WShape.app (f : WShape (n+1)) (a : WShape n) : WShape n := by
  refine ⟨Shape.app f.1 a.1, ?_⟩
  obtain ⟨⟨⟩, wf⟩ := f <;> try exact .bot
  exact (WShapeFun.app ⟨_, wf.1⟩ _).2

@[simp] theorem WShape.bot_app {x : WShape n} : WShape.app (WShape.bot (n := n+1)) x = .bot :=
  WShape.ext (Shape.bot_app (x := x.1))

@[simp] theorem WShape.lam_app {f : WShapeFun n} {hl} {x : WShape n} :
    WShape.app (WShape.lam f hl) x = f.app x := rfl

theorem WShapeFun.app_of_mem {f : WShapeFun n} (h : (x, y) ∈ f) :
    f.app x ≤ y ∧ y ≤ f.app x :=
  have ⟨_, h1, h2, h3⟩ := f.app_core x
  ⟨f.mem_mono h2 h h1, h3 _ h .rfl⟩

theorem WShapeFun.app_eq (f : WShapeFun n) (x : WShape n) :
    ∃ x', x' ≤ x ∧ (x', f.app x) ∈ f :=
  let ⟨x', h1, h2, _⟩ := f.app_core x; ⟨x', h1, h2⟩

theorem WShapeFun.app_mono_l {f f' : WShapeFun n} (h : f ≤ f') (a : WShape n) :
    f.app a ≤ f'.app a := by
  have ⟨_, a1, a2, a3⟩ := f.app_core a
  have ⟨_, b1, b2, b3⟩ := f'.app_core a
  have ⟨_, _, c1, c2, c3⟩ := WShapeFun.LE.def'.1 h _ _ a2
  exact c3.trans <| b3 _ c1 (c2.trans a1)

theorem WShapeFun.app_mono_r {f : WShapeFun n} {a a' : WShape n} (h : a ≤ a') :
    f.app a ≤ f.app a' := by
  have ⟨_, a1, a2, a3⟩ := f.app_core a
  have ⟨_, b1, b2, b3⟩ := f.app_core a'
  exact b3 _ a2 (a1.trans h)

theorem WShape.app_mono_l {f f' : WShape (n+1)} (h : f ≤ f') (a : WShape n) :
    f.app a ≤ f'.app a := by
  change f.1 ≤ f'.1 at h; show Shape.app f.1 a.1 ≤ Shape.app f'.1 a.1
  cases hf : f.1 with | lam => ?_ | _ => exact Shape.bot_le
  let ⟨f', wf'⟩ := f'; have := hf ▸ f.2
  cases f' with rw [hf] at h | lam => ?_ | _ => exact (Shape.LE.def.1 h).elim
  exact WShapeFun.app_mono_l (f := ⟨_, (hf ▸ f.2).1⟩) (f' := ⟨_, wf'.1⟩) h _

theorem WShape.app_mono_r {f : WShape (n+1)} {a a' : WShape n} (h : a ≤ a') :
    f.app a ≤ f.app a' := by
  obtain ⟨⟨⟩, wf⟩ := f <;> try exact .rfl
  exact WShapeFun.app_mono_r (f := ⟨_, wf.1⟩) h

@[simp] theorem WShapeFun.bot_app : (WShapeFun.bot (n := n)).app x = .bot := by
  ext1; exact ShapeFun.bot_app

theorem WShapeFun.lift_app {f : WShapeFun n} {a : WShape n} (le : n ≤ m) :
    (f.app a).lift m = (f.lift m).app (a.lift m) := by
  ext1; simp [WShape.lift_val le, app, WShapeFun.lift_val le]
  exact ShapeFun.lift_app le

@[simp] theorem WShape.lift_app (le : n ≤ m) :
    (app f a : WShape n).lift m = app (f.lift _) (a.lift _) := by
  ext1; simp [lift_val le, app, Shape.lift_app le, lift_val (Nat.succ_le_succ le)]

@[simp] theorem WShape.lam'_app {f : WShapeFun n} {x : WShape n} : (lam' f).app x = f.app x := by
  simp [lam']; split <;> simp; rename_i h
  have ⟨_, h1, h2⟩ := f.app_eq x
  rw [eq_comm, ← WShape.le_bot]; exact Decidable.by_contra <| mt (⟨_, h2, ·⟩) h

theorem TShape.app_mono {f : WShape (n + 1)} {f' : WShape (m + 1)} {a : WShape n} {a' : WShape m}
    (le₁ : f.T ≤ f'.T) (le₂ : a.T ≤ a'.T) : (f.app a).T ≤ (f'.app a').T := by
  have lm₁ := Nat.le_max_left n m; have lm₂ := Nat.le_max_right n m
  rw [TShape.LE.def', WShape.lift_app lm₁, WShape.lift_app lm₂]
  refine (WShape.app_mono_l ?_ _).trans (WShape.app_mono_r le₂)
  exact (LE.def (Nat.succ_le_succ lm₁) (Nat.succ_le_succ lm₂)).1 le₁

theorem WShape.Compat.app {f f' : WShape (n+1)} {a a' : WShape n}
    (cf : f.Compat f') (ca : a.Compat a') : (f.app a).Compat (f'.app a') := by
  have ⟨zf, hf1, hf2⟩ := WShape.Compat.iff.1 cf
  have ⟨za, ha1, ha2⟩ := WShape.Compat.iff.1 ca
  exact WShape.Compat.iff.2 ⟨zf.app za,
    (WShape.app_mono_l hf1 _).trans (WShape.app_mono_r ha1),
    (WShape.app_mono_l hf2 _).trans (WShape.app_mono_r ha2)⟩

theorem TShape.Compat.app {f : WShape (n + 1)} {f' : WShape (m + 1)}
    {a : WShape n} {a' : WShape m}
    (cf : f.T.Compat f'.T) (ca : a.T.Compat a'.T) :
    (f.app a).T.Compat (f'.app a').T := by
  have le₁ := Nat.le_max_left n m; have le₂ := Nat.le_max_right n m
  rw [TShape.Compat.def le₁ le₂, WShape.lift_app le₁, WShape.lift_app le₂]
  exact WShape.Compat.app
    ((TShape.Compat.def (Nat.succ_le_succ le₁) (Nat.succ_le_succ le₂)).1 cf)
    ((TShape.Compat.def le₁ le₂).1 ca)

theorem WShapeFun.mem_join {f f' : WShapeFun n} {a} (hc : f.Compat f') :
    (a, b) ∈ f.join f' ↔ ∃ x ∈ f, ∃ y ∈ f', x.1.Compat y.1 ∧
      let j := x.1.join y.1; a = j ∧ b = (f.app j).join (f'.app j) := by
  simp only [WShapeFun.mem_def, WShapeFun.join_val hc, ShapeFun.mem_join]
  constructor
  · intro ⟨x, h1, y, h2, h3, h4⟩
    refine have h3' := ?_; ⟨_, f.mem_val h1, _, f'.mem_val h2, h3', ?_⟩; · exact h3
    cases a; cases b; cases h4; simp; constructor <;> ext1
    · simp [WShape.join_val h3']
    · rw [WShape.join_val (hc.app_l _)]; simp [app, WShape.join_val h3']
  · rintro ⟨x, h1, y, h2, h3, rfl, rfl⟩; refine ⟨_, h1, _, h2, h3, ?_⟩
    simp [WShape.join_val h3]; rw [WShape.join_val (hc.app_l _)]; simp [app, WShape.join_val h3]

def ShapeFun.single (x y : Shape n) : ShapeFun n :=
  (x, y) :: if x ≤ .bot then [] else [(.bot, .bot)]

omit [Params] in
theorem ShapeFun.self_mem_single : (x, y) ∈ single x y := .head _

protected theorem ShapeFun.WF.single (x y : WShape n) : WF Shape.WF (single x.1 y.1) := by
  refine ⟨?_, fun p hp => ?_⟩; rotate_left
  · simp [single] at hp
    obtain rfl | ⟨_, rfl⟩ := hp
    · exact ⟨x.2, y.2⟩
    · exact ⟨.bot, .bot⟩
  simp only [single, List.mem_cons, List.mem_ite_nil_left, List.not_mem_nil, or_false,
    exists_eq_or_imp, forall_eq_or_imp, and_imp, forall_eq_apply_imp_iff, Shape.bot_le,
    imp_self, and_true]
  have self : x.1.join x.1 ≤ x.1 ∧ x.1 ≤ x.1.join x.1 :=
    WShape.join_val .rfl ▸ (WShape.Join.iff.1 (WShape.join_self.2 ⟨.rfl, .rfl⟩)).2
  refine ⟨?_, ⟨⟨fun _ => .inl self, fun _ => .rfl⟩, ?_⟩, fun nle => ⟨fun h1 => ?_, fun h1 => ?_⟩⟩
  · obtain ⟨x, _⟩ := x; by_cases h : x ≤ .bot
    · cases Shape.le_bot.1 h; exact ⟨_, .inl rfl⟩
    · exact ⟨_, .inr ⟨h, rfl⟩⟩
  · exact (⟨by simp [Shape.join_bot, Shape.LE.rfl], ·.elim⟩)
  · simp [Shape.bot_join, Shape.LE.rfl]
  · simp [Shape.bot_join, nle]

def WShapeFun.single (x y : WShape n) : WShapeFun n :=
  ⟨ShapeFun.single x.1 y.1, .single x y⟩

omit [Params] in
theorem ShapeFun.single_app : (single x y).app x' = if x ≤ x' then y else .bot := by
  simp [single, app, trunc, maxBelow, List.find?]
  by_cases h : x ≤ x' <;> simp [h, Shape.LE.rfl]; split <;> simp

theorem WShapeFun.single_app {x y : WShape n} {x' : WShape n} :
    (WShapeFun.single x y).app x' = if x ≤ x' then y else .bot := by
  ext1; simp [WShapeFun.single, app, ShapeFun.single_app]
  split <;> simp [*, WShape.LE.def, WShape.bot]

theorem WShapeFun.mem_single {x y : WShape n} :
    a ∈ WShapeFun.single x y ↔ a = (x, y) ∨ ¬x ≤ .bot ∧ a = (.bot, .bot) := by
  cases a; simp [WShapeFun.mem_def, WShapeFun.single, ShapeFun.single,
    WShape.ext_iff, WShape.LE.def, WShape.bot]

theorem WShapeFun.single_le {f : WShapeFun n} :
    WShapeFun.single x y ≤ f ↔ ∃ x' y', (x', y') ∈ f ∧ x' ≤ x ∧ y ≤ y' := by
  simp [WShapeFun.LE.def', WShapeFun.mem_single]
  refine ⟨fun H => H _ _ (.inl ⟨rfl, rfl⟩), ?_⟩
  rintro H _ _ (⟨rfl, rfl⟩ | ⟨h4, rfl, rfl⟩)
  · exact H
  · let ⟨_, h1⟩ := f.bot_mem; exact ⟨_, _, h1, .rfl, WShape.bot_le⟩

theorem WShapeFun.lift_single (le : n ≤ m) {x y : WShape n} :
    (WShapeFun.single x y).lift m = WShapeFun.single (x.lift m) (y.lift m) := by
  ext1; simp [lift_val le, single, WShape.lift_val le, ShapeFun.single, ShapeFun.lift]
  split <;> simp [*, Shape.lift_le_bot le, ← Shape.le_bot]

theorem WShapeFun.compat_single {f : WShapeFun n} :
    Compat f (single x y) ↔ ∀ a ∈ f, a.1.Compat x → a.2.Compat y := by
  simp [WShapeFun.Compat.def, mem_single, WShape.Compat.bot_r]

omit [Params] in
theorem ShapeFun.lift_single (le : n ≤ m) {x y : Shape n} :
    lift (Shape.lift _) (ShapeFun.single x y) = (ShapeFun.single (x.lift m) (y.lift m)) := by
  simp [lift, single] <;> split <;> rename_i h <;>
    simpa [Shape.lift_le_bot le, Shape.le_bot] using h

theorem WShapeFun.Join.app_l {f g h : WShapeFun n}
    (hJ : Join f g h) (p : WShape n) : WShape.Join (f.app p) (g.app p) (h.app p) := by
  refine fun z => ⟨fun H => ⟨?_, ?_⟩, fun ⟨h1, h2⟩ => ?_⟩
  · exact (app_mono_l hJ.le.1 p).trans H
  · exact (app_mono_l hJ.le.2 p).trans H
  · refine (app_mono_l (Join.iff.1 hJ).2.2 _).trans ?_
    have ⟨x, a1, a2, a3⟩ := (f.join g).app_core p
    obtain ⟨⟨a, _⟩, b1, ⟨b, _⟩, b2, b3, rfl, b5⟩ := (WShapeFun.mem_join hJ.compat).1 a2
    have hJ' := WShape.Join.mk (hJ.compat.app_l (a.join b))
    exact b5 ▸ (hJ' _).2 ⟨(app_mono_r a1).trans h1, (app_mono_r a1).trans h2⟩

def hasType.core (hasType : Shape n → Shape n → Bool)
    (f : ShapeFun n) (a : Shape n) (G : Shape n → Shape n) : Bool :=
  f.all fun (x, y) => (f.any fun (x', y') => x' ≤ x && y ≤ y' && hasType x' a) && hasType y (G x)

def Shape.hasType : ∀ {n}, Shape n → Shape n → Bool
  | _+1, .bot, .forallE a b => hasType.core hasType b a fun _ => .type
  | _+1, .forallE a b, .sort r => hasType.core hasType b a fun _ => .sort r
  | 0, .bot, _ | _+1, .bot, .bot | _+1, .bot, .sort _ | _+1, .bot, .indTy => true
  | 0, .sort _, .sort j | _+1, .sort _, .sort j => j
  | _+1, .lam f, .forallE a b =>
    hasType.core hasType b a (fun _ => .type) && hasType.core hasType f a (ShapeFun.app b)
  | _+1, .ctor _ _, .indTy => true
  | _+1, .indTy, .sort r => r
  | _, _, _ => false

def Shape.HasType : Shape n → Shape n → Prop := (hasType · ·)

def Shape.HasDom (f : ShapeFun n) (a : Shape n) :=
  ∀ x y, (x, y) ∈ f → ∃ x' y', (x', y') ∈ f ∧ x' ≤ x ∧ y ≤ y' ∧ x'.HasType a

def Shape.HasTypePi (b : ShapeFun n) (a : Shape n) (rel : Bool) :=
  Shape.HasDom b a ∧ ∀ x y, (x, y) ∈ b → y.HasType (.sort rel)

def Shape.HasTypeLam (f : ShapeFun n) (a : Shape n) (b : ShapeFun n) :=
  Shape.HasTypePi b a true ∧ Shape.HasDom f a ∧ ∀ x y, (x, y) ∈ f → y.HasType (b.app x)

omit [Params] in
theorem Shape.hasType.core.iff {a : Shape n} :
    hasType.core hasType f a G ↔ HasDom f a ∧ ∀ x y, (x, y) ∈ f → y.HasType (G x) := by
  simp [hasType.core, HasDom, forall_and, HasType, and_assoc]

inductive Shape.HasTypeU : ∀ {n}, Shape n → Shape n → Prop
  | bot : HasType x .type → HasTypeU .bot x
  | sort : HasTypeU (.sort r) .type
  | forallE : HasTypePi (n := n) b a r → HasTypeU (n := n+1) (.forallE a b) (.sort r)
  | lam : HasTypeLam (n := n) f a b → HasTypeU (n := n+1) (.lam f) (.forallE a b)
  | ctor : HasTypeU (n := n+1) (.ctor c l) .indTy
  | indTy : HasTypeU (n := n+1) .indTy .type

omit [Params] in
theorem Shape.HasType.unfold {m a : Shape n} : HasType m a → HasTypeU m a := by
  unfold HasType Shape.hasType
  split <;> (try simp [hasType.core.iff]) <;> intros <;> subst_vars <;> try constructor
  · simp [HasType, hasType.core.iff, hasType]; exact ⟨‹_›, ‹_›⟩
  · simp [HasTypePi]; exact ⟨‹_›, ‹_›⟩
  · rename_i x; cases x <;> rfl
  · rfl
  · rfl
  · rfl
  · simp only [HasTypeLam, HasTypePi]; exact ⟨⟨‹_›, ‹_›⟩, ⟨‹_›, ‹_›⟩⟩

omit [Params] in
theorem Shape.HasType.unfold_iff {m a : Shape n} : HasType m a ↔ HasTypeU m a := by
  refine ⟨(·.unfold), fun h => ?_⟩
  cases h with
  | bot h =>
    cases h.unfold with
    | bot | sort => cases n <;> rfl
    | indTy => rfl
    | forallE => simpa [HasType, hasType] using h
  | sort => cases n <;> rfl
  | forallE H => simpa [HasType, hasType, hasType.core.iff, HasTypePi] using H
  | lam H => simp [HasType, hasType, hasType.core.iff]; exact H
  | ctor | indTy => rfl

omit [Params] in
protected theorem Shape.HasType.lift (le : n ≤ n') :
    Shape.HasType (m.lift n') (a.lift n') ↔ Shape.HasType (n := n) m a := by
  dsimp [HasType]; rw [← Bool.eq_iff_iff]
  induction n generalizing n' with
  | zero =>
    cases n' with | zero => simp [Shape.lift_self] | succ n'
    cases m <;> cases a <;> simp [Shape.lift, hasType]
  | succ n ih =>
    let n' + 1 := n'; replace le := Nat.le_of_succ_le_succ le
    replace ih {m a} := @ih _ m a le
    have core {a : ShapeFun n} {a' : Shape n} {G G'}
        (H : ∀ x, G' (lift n' x) = lift n' (G x)) :
        hasType.core hasType (ShapeFun.lift (lift n') a) (lift n' a') G' =
        hasType.core hasType a a' G := by
      rw [Bool.eq_iff_iff]; simp [hasType.core, ShapeFun.lift, H, ih, lift_le_lift le]
    cases m <;> cases a <;> simp only [lift, hasType, type] <;> try rw [core fun _ => lift_sort.symm]
    · rw [core fun _ => (ShapeFun.lift_app le).symm]

omit [Params] in
protected theorem Shape.HasDom.lift (le : n ≤ n') :
    HasDom (ShapeFun.lift (lift n') m) (a.lift n') ↔ HasDom (n := n) m a := by
  simp only [HasDom, ShapeFun.lift, List.mem_map, Prod.mk.injEq]
  constructor <;> [intro H x y h; rintro H x y ⟨_, h, rfl, rfl⟩]
  · obtain ⟨_, _, ⟨_, h1, rfl, rfl⟩, h2, h3, h4⟩ := H _ _ ⟨_, h, rfl, rfl⟩
    exact ⟨_, _, h1, (Shape.lift_le_lift le).1 h2,
      (Shape.lift_le_lift le).1 h3, (Shape.HasType.lift le).1 h4⟩
  · have ⟨_, _, h1, h2, h3, h4⟩ := H _ _ h
    exact ⟨_, _, ⟨_, h1, rfl, rfl⟩, Shape.lift_mono h2,
      Shape.lift_mono h3, (Shape.HasType.lift le).2 h4⟩

omit [Params] in
protected theorem Shape.HasTypePi.lift (le : n ≤ n') :
    HasTypePi (ShapeFun.lift (lift n') m) (a.lift n') rel ↔ HasTypePi (n := n) m a rel := by
  simp only [HasTypePi]
  exact and_congr (HasDom.lift le) <| by
    simp only [ShapeFun.lift, List.mem_map, Prod.mk.injEq]
    constructor <;> [intro H x y h; rintro H _ _ ⟨⟨x, y⟩, h, rfl, rfl⟩]
    · exact (Shape.HasType.lift le).1 (Shape.lift_sort.symm ▸ H _ _ ⟨_, h, rfl, rfl⟩)
    · exact Shape.lift_sort ▸ (Shape.HasType.lift le).2 (H _ _ h)

omit [Params] in
theorem Shape.HasTypeLam.lift (le : n ≤ n') :
    HasTypeLam (ShapeFun.lift (lift n') f) (a.lift n') (ShapeFun.lift (lift n') b) ↔
    HasTypeLam (n := n) f a b := by
  simp only [HasTypeLam]
  refine and_congr (HasTypePi.lift le) <| and_congr (HasDom.lift le) ⟨?_, ?_⟩ <;> intro H x y h
  · have h' : (x.lift n', y.lift n') ∈ ShapeFun.lift (Shape.lift n') f :=
      List.mem_map.2 ⟨_, h, rfl⟩
    have := H _ _ h'
    rw [← ShapeFun.lift_app le] at this
    exact (Shape.HasType.lift le).1 this
  · obtain ⟨⟨x₀, y₀⟩, h₀, heq⟩ := List.mem_map.1 h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    rw [← ShapeFun.lift_app le]
    exact (Shape.HasType.lift le).2 (H _ _ h₀)

omit [Params] in
protected theorem Shape.HasType.bot {a : Shape n} (H : HasType a .type) : HasType .bot a :=
  unfold_iff.2 (.bot H)
omit [Params] in
protected theorem Shape.HasType.sort : HasType (n := n) (.sort rel) .type := unfold_iff.2 .sort
omit [Params] in
protected theorem Shape.HasType.forallE (H : HasTypePi (n := n) b a r) :
    HasType (n := n+1) (.forallE a b) (.sort r) := unfold_iff.2 (.forallE H)
omit [Params] in
protected theorem Shape.HasType.lam (H : HasTypeLam (n := n) f a b) :
    HasType (n := n+1) (.lam f) (.forallE a b) := unfold_iff.2 (.lam H)
omit [Params] in
protected theorem Shape.HasType.indTy : HasType (n := n+1) .indTy .type := unfold_iff.2 .indTy

omit [Params] in
theorem Shape.HasType.bot_r (H : HasType (n := n) x .bot) : x = .bot := by
  cases n <;> cases x <;> simp [HasType, hasType, bot] at H ⊢

omit [Params] in
theorem Shape.HasType.toType (H : HasType (n := n) m (.sort r)) : HasType m .type := by
  unfold HasType hasType at H; revert H; generalize eq : sort r = s
  split <;> cases eq <;> simp [HasType, hasType]
  · simp only [hasType.core.iff]; refine fun ⟨h1, h2⟩ => ⟨h1, fun _ _ h3 => toType (h2 _ _ h3)⟩

omit [Params] in
theorem Shape.HasType.isType (H : HasType m a) : a.HasType .type := by
  cases H.unfold with
  | bot H => exact H
  | sort | forallE | indTy => exact .sort
  | lam H' => exact .forallE H'.1
  | ctor => exact .indTy

omit [Params] in
theorem Shape.HasTypePi.toType (H : HasTypePi b a r) : HasTypePi b a true :=
  ⟨H.1, fun _ _ h => (H.2 _ _ h).toType⟩

def WShape.HasType (m a : WShape n) : Prop := Shape.HasType m.1 a.1
def WShape.HasDom (f : WShapeFun n) (a : WShape n) := Shape.HasDom f.1 a.1
def WShape.HasTypePi (b : WShapeFun n) (a : WShape n) := Shape.HasTypePi b.1 a.1
def WShape.HasTypeLam (f : WShapeFun n) (a : WShape n) (b : WShapeFun n) :=
  Shape.HasTypeLam f.1 a.1 b.1

theorem WShape.HasDom.def : HasDom f a ↔
    ∀ x y, (x, y) ∈ f → ∃ x' y', (x', y') ∈ f ∧ x' ≤ x ∧ y ≤ y' ∧ x'.HasType a :=
  ⟨fun H _ _ h => have ⟨_, _, h1, h2⟩ := H _ _ h; ⟨_, _, f.mem_val h1, h2⟩,
   fun H _ _ h => have ⟨_, _, h1, h2⟩ := H _ _ (f.mem_val h); ⟨_, _, h1, h2⟩⟩

theorem WShape.HasTypePi.def {b : WShapeFun n} :
    HasTypePi b a rel ↔ HasDom b a ∧ ∀ x y, (x, y) ∈ b → y.HasType (.sort rel) :=
  and_congr_right' ⟨fun H _ _ h => H _ _ h, fun H _ _ h => H _ _ (b.mem_val h)⟩

theorem WShape.HasTypeLam.def {f : WShapeFun n} {a b} :
  HasTypeLam f a b ↔ HasTypePi b a true ∧ HasDom f a ∧ ∀ x y, (x, y) ∈ f → y.HasType (b.app x) :=
  and_congr_right' <| and_congr_right' ⟨fun H _ _ h => H _ _ h, fun H _ _ h => H _ _ (f.mem_val h)⟩

theorem WShape.HasDom.lift (le : n ≤ m) :
    HasDom (f.lift m) (a.lift m) ↔ HasDom (n := n) f a := by
  simp only [HasDom, Shape.HasDom, WShapeFun.lift_val le, ShapeFun.lift, List.mem_map,
    Prod.mk.injEq, WShape.lift_val le]
  constructor <;> [intro H x y h; rintro H x y ⟨_, h, rfl, rfl⟩]
  · obtain ⟨_, _, ⟨_, h1, rfl, rfl⟩, h2, h3, h4⟩ := H _ _ ⟨_, h, rfl, rfl⟩
    exact ⟨_, _, h1, (Shape.lift_le_lift le).1 h2,
      (Shape.lift_le_lift le).1 h3, (Shape.HasType.lift le).1 h4⟩
  · have ⟨_, _, h1, h2, h3, h4⟩ := H _ _ h
    exact ⟨_, _, ⟨_, h1, rfl, rfl⟩, Shape.lift_mono h2,
      Shape.lift_mono h3, (Shape.HasType.lift le).2 h4⟩

theorem WShape.HasType.toType : HasType (n := n) x (.sort r) → HasType x .type :=
  Shape.HasType.toType

theorem WShape.HasType.isType : HasType m a → a.HasType .type := Shape.HasType.isType

theorem WShape.HasDom.isType (H : WShape.HasDom f a) : a.HasType .type := by
  have ⟨_, h⟩ := f.bot_mem
  have ⟨_, _, _, h2, _, h4⟩ := HasDom.def.1 H _ _ h
  cases le_bot.1 h2; exact h4.isType

theorem WShape.HasType.mono_r {m a a' : WShape n} (ha : a ≤ a')
    (Ha : HasType a' (.sort r)) (H : HasType m a) : HasType m a' := by
  have ⟨m, mwf⟩ := m; have ⟨a, awf⟩ := a; have ⟨a', awf'⟩ := a'
  simp only [HasType, sort, WShape.LE.def] at *
  cases H.unfold with
  | bot H => exact .bot Ha.toType
  | sort | forallE | indTy => cases Shape.sort_le.1 ha; exact H
  | ctor => cases Shape.indTy_le.1 ha; exact H
  | @lam n _ _ _ H' =>
    obtain ⟨_, _, h1, h2, ⟨⟩⟩ := Shape.forallE_le.1 ha
    let .forallE Ha := Ha.unfold
    have ih := @WShape.HasType.mono_r n
    let rec ih_dom {f : WShapeFun n} {a a' r} (ha : a ≤ a') (Ha : HasType a' (.sort r))
        (H : HasDom (n := n) f a) : HasDom f a' := by
      rw [WShape.HasDom.def] at H ⊢; intro _ _ h
      have ⟨_, _, h1, h2, h3, h4⟩ := H _ _ h
      exact ⟨_, _, h1, h2, h3, ih ha Ha h4⟩
    let rec ih_lam {f : WShapeFun n} {a a' b b'} (Ha : HasTypePi b' a' r)
        (ha : a ≤ a') (hb : b ≤ b') (H : HasTypeLam f a b) : HasTypeLam f a' b' := by
      rw [HasTypeLam.def] at H ⊢
      have ht := (HasTypePi.def.1 Ha).1.isType
      refine ⟨Ha.toType, ih_dom ha ht H.2.1, fun x y h => ?_⟩
      have ⟨_, h1, h2⟩ := b'.app_eq x
      exact .mono_r (WShapeFun.app_mono_l hb _) ((HasTypePi.def.1 Ha).2 _ _ h2) (H.2.2 _ _ h)
    exact .lam (ih_lam (f := ⟨_, mwf.1⟩) (a := ⟨_, awf.1⟩)
      (a' := ⟨_, awf'.1⟩) (b := ⟨_, awf.2⟩) (b' := ⟨_, awf'.2⟩) Ha h1 h2 H')

theorem WShape.HasDom.mono_r {f : WShapeFun n} {a a' r} :
    a ≤ a' → HasType a' (.sort r) → HasDom f a → HasDom f a' := HasType.mono_r.ih_dom HasType.mono_r

theorem WShape.HasTypeLam.mono_r {f : WShapeFun n} {a a' b b'} :
    HasTypePi b' a' r → a ≤ a' → b ≤ b' → HasTypeLam f a b → HasTypeLam f a' b' :=
  HasType.mono_r.ih_lam HasType.mono_r

omit [Params] in
private theorem find_cycle (R : α → α → Prop)
    (trans : ∀ {x y z}, R x y → R y z → R x z) (l : List α)
    (H : ∀ x ∈ l, ∃ y ∈ l, R x y) : ∀ x ∈ l, ∃ y ∈ l, R x y ∧ R y y := by
  intro x h
  suffices ∀ l₁ l₂, l.Perm (l₁ ++ l₂) → (∀ y ∈ l₂, ∀ z ∈ l, R x z → R y z) →
      ∃ y ∈ l, R x y ∧ R y y from this l [] (by simp) nofun
  intro l₁; generalize eq : l₁.length = i; revert x l₁
  refine i.strongRecOn ?_; rintro i ih x₀ h₀ l₁ rfl l₂ he hl
  have ⟨x', a1, a2⟩ := H x₀ h₀
  obtain hm | hm := List.mem_append.1 (he.mem_iff.1 a1)
  · have ⟨l', hp⟩ := List.perm_cons_of_mem hm
    have he' := he.trans (.append_right _ hp) |>.trans List.perm_middle.symm
    refine have ⟨_, c1, c2, c3⟩ := ih l'.length ?_ _ a1 _ rfl _ he' ?_; ⟨_, c1, trans a2 c2, c3⟩
    · rw [hp.length_eq]; apply Nat.lt_succ_self
    · rintro x' (⟨⟩ | ⟨_, hx⟩) z hz hr <;> [exact hr; exact hl _ hx _ hz (trans a2 hr)]
  · exact ⟨_, a1, a2, hl _ hm _ a1 a2⟩

namespace WShape.HasType.mono_l
variable (ih : ∀ {m m' a : WShape n}, m ≤ m' → m' ≤ m → HasType m a → HasType m' a)
include ih

theorem ih_dom {f f' : WShapeFun n} (hf1 : f ≤ f') (hf2 : f' ≤ f)
    (H : HasDom f a) : HasDom f' a := by
  rw [HasDom.def] at H ⊢; intro x y h
  have ⟨z, h1, ⟨c, c1, c2, c3, _⟩, d, d1, d2, _, d4⟩ := find_cycle ?_ f'.1 ?_ _ h
    (R := fun x y => ∃ z : WShape n, y.1 ≤ z.1 ∧ z.1 ≤ x.1 ∧ x.2 ≤ y.2 ∧ z.HasType a)
  · exact ⟨_, _, f'.mem_val h1, c1.trans c2, c3, ih d2 d1 d4⟩
  · rintro x y z ⟨_, a1, a2, a3, a4⟩ ⟨_, b1, b2, b3, b4⟩
    exact ⟨_, b1, b2.trans (a1.trans a2), a3.trans b3, b4⟩
  · rintro x h
    have ⟨x₁, y₁, a1, a2, a3⟩ := WShapeFun.LE.def'.1 hf2 _ _ (f'.mem_val h)
    have ⟨x₂, y₂, b1, b2, b3, b4⟩ := H _ _ a1
    have ⟨x₃, y₃, c1, c2, c3⟩ := WShapeFun.LE.def'.1 hf1 _ _ b1
    exact ⟨_, c1, _, c2, b2.trans a2, a3.trans (b3.trans c3), b4⟩

theorem ih_pi {b b'} {a a' : WShape n}
    (hb1 : b ≤ b') (hb2 : b' ≤ b) (ha1 : a ≤ a') (ha2 : a' ≤ a)
    (H : HasTypePi b a r) : HasTypePi b' a' r := by
  rw [HasTypePi.def] at H ⊢
  refine ⟨ih_dom ih hb1 hb2 H.1 |>.mono_r ha1 (ih ha1 ha2 H.1.isType), fun x y h => ?_⟩
  have ⟨x₁, y₁, a1, a2, a3⟩ := WShapeFun.LE.def'.1 hb2 _ _ h
  have ⟨x₂, y₂, b1, b2, b3⟩ := WShapeFun.LE.def'.1 hb1 _ _ a1
  have ⟨_, c1, c2⟩ := b.app_eq x
  exact ih (b3.trans <| b'.mem_mono b1 h (b2.trans a2)) a3 (H.2 _ _ a1)

theorem ih_lam {f f' : WShapeFun n} (hf1 : f ≤ f') (hf2 : f' ≤ f)
    (H : HasTypeLam f a b) : HasTypeLam f' a b := by
  rw [HasTypeLam.def] at H ⊢; refine ⟨H.1, ih_dom ih hf1 hf2 H.2.1, fun x y h => ?_⟩
  have ⟨x₁, y₁, a1, a2, a3⟩ := WShapeFun.LE.def'.1 hf2 _ _ h
  have ⟨x₂, y₂, b1, b2, b3⟩ := WShapeFun.LE.def'.1 hf1 _ _ a1
  have ⟨_, c1, c2⟩ := b.app_eq x
  refine .mono_r (b.app_mono_r a2) ((HasTypePi.def.1 H.1).2 _ _ c2) ?_
  exact ih (b3.trans <| f'.mem_mono b1 h (b2.trans a2)) a3 (H.2.2 _ _ a1)

end WShape.HasType.mono_l

theorem WShape.HasType.mono_l {m m' a : WShape n}
    (hm1 : m ≤ m') (hm2 : m' ≤ m) (H : HasType m a) : HasType m' a := by
  have ⟨m, mwf⟩ := m; have ⟨m', mwf'⟩ := m'; have ⟨a, awf⟩ := a
  simp only [HasType, WShape.LE.def] at *
  cases H.unfold with
  | bot => cases Shape.le_bot.1 hm2; exact H
  | sort => cases Shape.sort_le.1 hm1; exact H
  | forallE H' =>
    obtain ⟨_, _, a1, a2, ⟨⟩⟩ := Shape.forallE_le.1 hm1
    have ⟨b1, b2⟩ := Shape.forallE_le_forallE.1 hm2
    exact .forallE <| mono_l.ih_pi mono_l (b := ⟨_, mwf.2⟩) (b' := ⟨_, mwf'.2⟩)
      (a := ⟨_, mwf.1⟩) (a' := ⟨_, mwf'.1⟩) a2 b2 a1 b1 H'
  | lam H' =>
    obtain ⟨_, a1, ⟨⟩⟩ := Shape.lam_le.1 hm1; have b1 := Shape.lam_le_lam.1 hm2
    exact .lam <| mono_l.ih_lam mono_l (f := ⟨_, mwf.1⟩) (f' := ⟨_, mwf'.1⟩)
      (a := ⟨_, awf.1⟩) (b := ⟨_, awf.2⟩) hm1 hm2 H'
  | ctor => cases m' <;> simp [Shape.LE.def] at hm1; rfl
  | indTy => cases Shape.indTy_le.1 hm1; exact H

theorem WShape.HasDom.mono_l {f f' : WShapeFun n} : f ≤ f' → f' ≤ f →
    HasDom f a → HasDom f' a := WShape.HasType.mono_l.ih_dom WShape.HasType.mono_l
theorem WShape.HasTypePi.mono_l {a a' : WShape n} : b ≤ b' → b' ≤ b → a ≤ a' → a' ≤ a →
    HasTypePi b a r → HasTypePi b' a' r := WShape.HasType.mono_l.ih_pi WShape.HasType.mono_l
theorem WShape.HasTypeLam.mono_l {f f' : WShapeFun n} : f ≤ f' → f' ≤ f →
    HasTypeLam f a b → HasTypeLam f' a b := WShape.HasType.mono_l.ih_lam WShape.HasType.mono_l

theorem WShape.HasDom.iff {f : WShapeFun n} :
    HasDom f a ↔ ∀ x, ∃ x', x' ≤ x ∧ x'.HasType a ∧ f.app x ≤ f.app x' := by
  refine WShape.HasDom.def.trans ⟨fun H x => ?_, fun H x₀ y₀ h₀ => ?_⟩
  · have ⟨x', a1, a2⟩ := WShapeFun.app_eq f x
    have ⟨x₂, y₂, b1, b2, b3, b4⟩ := H _ _ a2
    exact ⟨_, b2.trans a1, b4, .trans b3 (f.app_of_mem b1).2⟩
  · have ⟨z, h1, ⟨c, c1, c2, c3, _⟩, d, d1, d2, _, d4⟩ := find_cycle ?_ f.1 ?_ _ h₀
      (R := fun x y => ∃ z : WShape n, y.1 ≤ z.1 ∧ z.1 ≤ x.1 ∧ x.2 ≤ y.2 ∧ z.HasType a)
    · exact ⟨_, _, f.mem_val h1, c1.trans c2, c3, d4.mono_l d2 d1⟩
    · rintro x y z ⟨_, a1, a2, a3, a4⟩ ⟨_, b1, b2, b3, b4⟩
      exact ⟨_, b1, b2.trans (a1.trans a2), a3.trans b3, b4⟩
    · rintro x h
      have ⟨x', a1, a2, a3⟩ := H ⟨_, (f.2.2 _ h).1⟩
      have ⟨x₁, b1, b2⟩ := f.app_eq x'
      exact ⟨_, b2, _, b1, a1, (f.app_of_mem (f.mem_val h)).2.trans a3, a2⟩

theorem WShape.HasTypePi.iff {b : WShapeFun n} :
    HasTypePi b a rel ↔ HasDom b a ∧ ∀ x, x.HasType a → (b.app x).HasType (.sort rel) := by
  refine WShape.HasTypePi.def.trans <| and_congr_right fun hd =>
    ⟨fun H x h => ?_, fun H x y h => ?_⟩
  · have ⟨_, h1, h2⟩ := b.app_eq x; exact H _ _ h2
  · have ⟨h1, h2⟩ := b.app_of_mem h
    have ⟨x', a1, a2, a3⟩ := HasDom.iff.1 hd x
    exact (H _ a2).mono_l (b.app_mono_r a1 |>.trans h1) (h2.trans a3)

theorem WShape.HasTypePi.iff' {b : WShapeFun n} :
    HasTypePi b a rel ↔ HasDom b a ∧ ∀ x, (b.app x).HasType (.sort rel) := by
  refine WShape.HasTypePi.iff.trans <| and_congr_right fun h1 => ⟨fun H x => ?_, fun H _ _ => H _⟩
  have ⟨x', a1, a2, a3⟩ := HasDom.iff.1 h1 x
  exact (H _ a2).mono_l (WShapeFun.app_mono_r a1) a3

theorem WShape.HasTypeLam.iff {f : WShapeFun n} {a b} :
    HasTypeLam f a b ↔ HasTypePi b a true ∧ HasDom f a ∧
      ∀ x, x.HasType a → (f.app x).HasType (b.app x) := by
  refine WShape.HasTypeLam.def.trans <| and_congr_right fun hp => and_congr_right fun hd =>
    ⟨fun H x h => ?_, fun H x y h => ?_⟩
  · have ⟨_, h1, h2⟩ := f.app_eq x
    exact .mono_r (b.app_mono_r h1) ((WShape.HasTypePi.iff.1 hp).2 _ h) <| H _ _ h2
  · have ⟨h1, h2⟩ := f.app_of_mem h
    have ⟨x', a1, a2, a3⟩ := HasDom.iff.1 hd x
    have ⟨x₂, b1, b2, b3⟩ := HasDom.iff.1 hp.1 x
    exact .mono_r (b.app_mono_r a1)
      ((WShape.HasTypePi.iff.1 hp).2 _ b2 |>.mono_l (b.app_mono_r b1) b3)
      ((H _ a2).mono_l (.trans (f.app_mono_r a1) h1) (h2.trans a3))

theorem WShape.HasTypeLam.iff' {b : WShapeFun n} :
    HasTypeLam f a b ↔ HasTypePi b a true ∧ HasDom f a ∧ ∀ x, (f.app x).HasType (b.app x) := by
  refine WShape.HasTypeLam.iff.trans <| and_congr_right fun h1 => and_congr_right fun h2 =>
    ⟨fun H x => ?_, fun H _ _ => H _⟩
  have ⟨x', a1, a2, a3⟩ := HasDom.iff.1 h2 x
  have := (H _ a2).mono_l (WShapeFun.app_mono_r a1) a3
  exact ((HasTypePi.iff'.1 h1).2 _).mono_r (WShapeFun.app_mono_r a1) this

theorem WShape.HasTypePi.lift (le : n ≤ m) :
    HasTypePi (b.lift m) (a.lift m) rel ↔ HasTypePi (n := n) b a rel := by
  simp only [HasTypePi, WShapeFun.lift_val le, WShape.lift_val le]
  exact Shape.HasTypePi.lift le

theorem WShape.HasTypeLam.lift (le : n ≤ m) :
    HasTypeLam (f.lift m) (a.lift m) (b.lift m) ↔
    HasTypeLam (n := n) f a b := by
  simp only [HasTypeLam, WShapeFun.lift_val le, WShape.lift_val le]
  exact Shape.HasTypeLam.lift le

inductive WShape.HasTypeU : ∀ {n}, WShape n → WShape n → Prop
  | bot : HasType x .type → HasTypeU .bot x
  | sort : HasTypeU (.sort r) .type
  | forallE : HasTypePi (n := n) b a r → HasTypeU (n := n+1) (.forallE a b) (.sort r)
  | lam : HasTypeLam (n := n) f a b → HasTypeU (n := n+1) (.lam' f) (.forallE a b)
  | ctor : HasTypeU (n := n+1) (.ctor c l wf) .indTy
  | indTy : HasTypeU (n := n+1) .indTy .type

theorem WShape.HasType.unfold {m a : WShape n} (H : HasType m a) : HasTypeU m a := by
  let ⟨m, mwf⟩ := m; let ⟨a, awf⟩ := a
  dsimp only [HasType] at H
  cases H.unfold with
  | bot h => exact .bot h
  | sort => exact .sort
  | forallE h => exact .forallE (a := ⟨_, mwf.1⟩) (b := ⟨_, mwf.2⟩) h
  | lam h =>
    have := HasTypeU.lam (f := ⟨_, mwf.1⟩) (a := ⟨_, awf.1⟩) (b := ⟨_, awf.2⟩) h
    rwa [lam', dif_pos (by exact mwf.2)] at this
  | ctor => exact (WShape.mk_ctor _ mwf).2 ▸ .ctor
  | indTy => exact .indTy

theorem WShape.HasType.unfold_iff {m a : WShape n} : HasType m a ↔ HasTypeU m a := by
  refine ⟨(·.unfold), fun h => ?_⟩
  cases h with
  | bot h => exact .bot h
  | sort => exact .sort
  | forallE h => exact .forallE h
  | @lam _ f a b h => unfold lam'; split <;> [exact .lam h; exact .bot (.forallE h.1)]
  | ctor => exact Shape.HasType.unfold_iff.2 .ctor
  | indTy => exact .indTy

theorem WShape.HasType.bot' : HasType (n := n) x .type → HasType .bot x :=
  (unfold_iff.2 <| .bot ·)
theorem WShape.HasType.sort : HasType (n := n) (.sort r) .type := unfold_iff.2 .sort
theorem WShape.HasType.forallE : HasTypePi (n := n) b a r →
    HasType (n := n+1) (.forallE a b) (.sort r) := (unfold_iff.2 <| .forallE ·)
theorem WShape.HasType.lam : HasTypeLam (n := n) f a b →
    HasType (n := n+1) (.lam' f) (.forallE a b) := (unfold_iff.2 <| .lam ·)
theorem WShape.HasType.indTy {n : Nat} : HasType (n := n+1) .indTy .type := unfold_iff.2 .indTy
theorem WShape.HasType.ctor : HasType (.ctor (n := n) c l wf) .indTy := unfold_iff.2 .ctor
theorem WShape.HasType.ctor' : HasType (n := n+1) (.ctor' c l) .indTy := by
  unfold WShape.ctor'; split <;> [apply ctor; exact bot' .indTy]

theorem WShape.HasTypePi.toType (H : HasTypePi (n := n) b a r) : HasTypePi (n := n) b a true :=
  ⟨H.1, fun _ _ h' => (H.2 _ _ h').toType⟩

theorem WShape.HasType.lam_isType {f : WShapeFun n} {hf} :
    ¬HasType (WShape.lam f hf) (.sort r) := nofun
theorem WShape.HasType.ctor_isType {c : Name} {l : List (WShape n)} {h} :
    ¬HasType (n := n+1) (WShape.ctor c l h) (.sort r) := nofun
theorem WShape.HasType.sort_not_forallE {a : WShape n} {f : WShapeFun n} :
    ¬HasType (n := n+1) (.sort r) (.forallE a f) := nofun
theorem WShape.HasType.forallE_not_forallE {a a' : WShape n} {f f' : WShapeFun n} :
    ¬HasType (n := n+1) (.forallE a f) (.forallE a' f') := nofun
theorem WShape.HasType.ctor_not_forallE {c l h a} {f : WShapeFun n} :
    ¬HasType (n := n+1) (WShape.ctor c l h) (.forallE a f) := nofun

theorem WShape.HasType.bot : HasType (n := n) x (.sort r) → HasType .bot x := (.bot' ·.toType)

theorem WShape.HasType.bot_r (H : HasType (n := n) x .bot) : x = .bot := by
  cases n <;> cases H.unfold <;> rfl

theorem WShape.HasType.bot_iff : HasType (n := n) .bot x ↔ HasType x .type := ⟨.isType, .bot'⟩

theorem WShape.HasDom.bot_iff {a : WShape n} : HasDom .bot a ↔ a.HasType .type := by
  simp [HasDom.def, WShapeFun.mem_bot, HasType.bot_iff]

theorem WShape.HasDom.bot : a.HasType .type → HasDom .bot a := bot_iff.2

theorem WShape.HasTypeLam.bot {b : WShapeFun n} : HasTypeLam .bot a b ↔ HasTypePi b a true := by
  simp only [HasTypeLam.def, WShapeFun.mem_bot, and_imp, forall_eq_apply_imp_iff,
    forall_eq, and_iff_left_iff_imp]
  exact fun h => ⟨.bot (HasDom.isType h.1), .bot' ((HasTypePi.iff'.1 h).2 _)⟩

theorem WShape.HasType.lift (h : n ≤ n') :
    HasType (m.lift n') (a.lift n') ↔ HasType (n := n) m a := by
  simp only [HasType, lift_val h]; exact Shape.HasType.lift h

theorem WShape.HasType.forallE_l {a : WShape n} {f : WShapeFun n} :
    HasType (.forallE a f) t ↔ ∃ r, HasTypePi f a r ∧ t = .sort r := by
  simp only [HasType, WShape.forallE, HasTypePi, WShape.sort,
    WShape.ext_iff, Shape.HasType.unfold_iff]
  generalize a.1 = a₁, f.1 = f₁, t.1 = t₁
  refine ⟨fun (.forallE H) => ⟨_, H, rfl⟩, fun ⟨_, H, eq⟩ => eq ▸ .forallE H⟩

theorem WShape.HasType.lam_l {f : WShapeFun n} {hf : f.NonZero}
    {t : WShape (n + 1)} :
    HasType (.lam f hf) t ↔
      ∃ a b, HasTypeLam f a b ∧ t = .forallE a b := by
  constructor
  · intro H
    obtain ⟨t, twf⟩ := t
    change @Shape.HasType (n + 1) (ShapeS.lam f.1) t at H
    cases Shape.HasType.unfold H with
    | @lam _ _ _ _ hLam =>
      exact ⟨⟨_, twf.1⟩, ⟨_, twf.2⟩, hLam, rfl⟩
  · rintro ⟨a, b, H, rfl⟩
    change @Shape.HasType (n + 1) (ShapeS.lam f.1)
      (ShapeS.forallE a.1 b.1)
    exact Shape.HasType.lam H

theorem WShape.HasType.forallE_inv {m : WShape (n+1)} {a : WShape n} {f : WShapeFun n}
    (H : HasType m (.forallE a f)) : ∃ g, m = .lam' g ∧ HasTypeLam g a f := by
  generalize eq : a.forallE f = a' at H
  cases H.unfold with
  | bot H' =>
    refine ⟨.bot, by simp, ?_⟩; subst eq
    obtain ⟨_, H, ⟨⟩⟩ := HasType.forallE_l.1 H'
    simp [HasTypeLam.def, WShapeFun.mem_bot, HasDom.def]
    have ⟨h1, h2⟩ := HasTypePi.iff.1 H
    exact have := .bot h1.isType; ⟨H, this, .bot (h2 _ this)⟩
  | lam H' => obtain ⟨rfl, rfl⟩ := forallE.inj.1 eq; exact ⟨_, rfl, H'⟩
  | _ => cases congrArg (·.1) eq

theorem WShape.HasType.join {m₁ m₂ a : WShape n} (hJ : m₁.Compat m₂)
    (h1 : m₁.HasType a) (h2 : m₂.HasType a) : (m₁.join m₂).HasType a := by
  obtain ⟨m₁, wf₁⟩ := m₁; obtain ⟨m₂, wf₂⟩ := m₂; obtain ⟨a, wf'⟩ := a
  simp [HasType, WShape.join_val hJ, Compat] at h1 h2 hJ ⊢
  cases n with
  | zero =>
    cases m₂ with | bot => exact h1 | sort
    cases m₁ with | bot => exact h2 | sort
    simp only [Shape.Compat, decide_eq_true_eq] at hJ
    simpa only [Shape.join, hJ]
  | succ n
  have ih := @join n
  let rec go_dom {a a' : WShape n} {f f' : WShapeFun n}
      (hf : f.Compat f') (ha : a.Compat a')
      (h1 : WShape.HasDom f a) (h2 : WShape.HasDom f' a') :
      WShape.HasDom (f.join f') (a.join a') := by
    rw [WShape.HasDom.iff] at h1 h2 ⊢
    have hJa := WShape.Join.mk ha
    have hJf := WShapeFun.Join.mk hf
    intro x
    have ⟨x₁, a1, a2, a3⟩ := h1 x
    have ⟨x₂, b1, b2, b3⟩ := h2 x
    have hcx := Compat.iff.2 ⟨_, a1, b1⟩; have hjx := WShape.Join.mk hcx
    have ajt := ih ha a2.isType b2.isType
    have := ih hcx (.mono_r hJa.le.1 ajt a2) (.mono_r hJa.le.2 ajt b2)
    refine ⟨_, (hjx _).2 ⟨a1, b1⟩, this, ?_⟩
    refine (hJf.app_l x _).2 ⟨a3.trans ?_, b3.trans ?_⟩
    · exact (WShapeFun.app_mono_r hjx.le.1).trans (hJf.app_l _).le.1
    · exact (WShapeFun.app_mono_r hjx.le.2).trans (hJf.app_l _).le.2
  let rec go_pi {a a' : WShape n} {b b' : WShapeFun n} {r}
      (ha : a.Compat a') (hb : b.Compat b')
      (h1 : WShape.HasTypePi b a r) (h2 : WShape.HasTypePi b' a' r) :
      WShape.HasTypePi (b.join b') (a.join a') r := by
    rw [WShape.HasTypePi.iff'] at h1 h2 ⊢
    have hJa := WShape.Join.mk ha
    have hJb := WShapeFun.Join.mk hb
    refine ⟨go_dom hb ha h1.1 h2.1, fun x => ?_⟩
    have ⟨a1, a2, a3⟩ := Join.iff.1 (hJb.app_l x)
    exact ih a1 (h1.2 _) (h2.2 _) |>.mono_l a2 a3
  let rec go_lam {f f' : WShapeFun n} {a b} (hf : f.Compat f')
      (h1 : WShape.HasTypeLam f a b) (h2 : WShape.HasTypeLam f' a b) :
      WShape.HasTypeLam (f.join f') a b := by
    rw [WShape.HasTypeLam.iff'] at h1 h2 ⊢
    have := Join.iff.1 <| (join_self (x := a)).2 ⟨.rfl, .rfl⟩
    refine ⟨h1.1, go_dom hf .rfl h1.2.1 h2.2.1 |>.mono_r this.2.1 h1.2.1.isType, fun x => ?_⟩
    have hJf := WShapeFun.Join.mk hf
    have ⟨a1, a2, a3⟩ := Join.iff.1 (hJf.app_l x)
    exact ih a1 (h1.2.2 _) (h2.2.2 _) |>.mono_l a2 a3
  cases h1.unfold with
  | bot => exact h2
  | sort =>
    (cases m₂ with | bot => exact h1 | _) <;>
      simp only [Shape.Compat, decide_eq_true_eq, Bool.false_eq_true] at hJ
    simpa only [Shape.join, hJ]
  | forallE h1' =>
    (cases h2.unfold with | bot => exact h1 | forallE h2' | _) <;>
      simp only [Shape.Compat, Bool.false_eq_true, Bool.and_eq_true] at hJ
    have := go_pi (b := ⟨_, wf₁.2⟩) (b' := ⟨_, wf₂.2⟩)
      (a := ⟨_, wf₁.1⟩) (a' := ⟨_, wf₂.1⟩) hJ.1 hJ.2 h1' h2'
    rw [HasTypePi, WShape.join_val (by exact hJ.1), WShapeFun.join_val (by exact hJ.2)] at this
    exact .forallE this
  | lam h1' =>
    (cases h2.unfold with | bot => exact h1 | lam h2' | _) <;> simp only [Shape.Compat] at hJ
    have := go_lam (f := ⟨_, wf₁.1⟩) (f' := ⟨_, wf₂.1⟩)
      (a := ⟨_, wf'.1⟩) (b := ⟨_, wf'.2⟩) hJ h1' h2'
    rw [HasTypeLam, WShapeFun.join_val (by exact hJ)] at this
    exact .lam this
  | ctor =>
    (cases h2.unfold with | bot => exact h1 | ctor | _) <;>
      simp only [Shape.Compat, Bool.and_eq_true, decide_eq_true_eq] at hJ
    simp only [Shape.join, if_pos hJ.1]; exact Shape.HasType.unfold_iff.2 .ctor
  | indTy =>
    (cases h2.unfold with | bot => exact h1 | indTy => rfl | _) <;>
      simp only [Shape.Compat, Bool.false_eq_true] at hJ

theorem WShape.HasDom.join {a a' : WShape n} {f f' : WShapeFun n} :
    f.Compat f' → a.Compat a' → HasDom f a → HasDom f' a' →
    HasDom (f.join f') (a.join a') := HasType.join.go_dom _ HasType.join
theorem WShape.HasTypePi.join {a a' : WShape n} {b b' : WShapeFun n} {r} :
    a.Compat a' → b.Compat b' → HasTypePi b a r → HasTypePi b' a' r →
    WShape.HasTypePi (b.join b') (a.join a') r := HasType.join.go_pi _ HasType.join
theorem WShape.HasTypeLam.join {f f' : WShapeFun n} {a b} :
    f.Compat f' → HasTypeLam f a b → HasTypeLam f' a b →
    WShape.HasTypeLam (f.join f') a b := HasType.join.go_lam _ HasType.join

theorem WShape.HasType.join' {m₁ m₂ m a : WShape n} (hJ : m₁.Join m₂ m)
    (h1 : m₁.HasType a) (h2 : m₂.HasType a) : m.HasType a :=
  have ⟨a1, a2, a3⟩ := Join.iff.1 hJ
  h1.join a1 h2 |>.mono_l a2 a3

theorem WShape.HasDom.join' (h1 : HasDom f₁ a₁) (h2 : HasDom f₂ a₂)
    (hJ : WShapeFun.Join f₁ f₂ h') (hJa : WShape.Join a₁ a₂ a') : HasDom h' a' := by
  have ⟨a1, a2, a3⟩ := WShapeFun.Join.iff.1 hJ
  have ⟨b1, b2, b3⟩ := WShape.Join.iff.1 hJa
  have := h1.join a1 b1 h2 |>.mono_l a2 a3
  exact this.mono_r b2 <| this.isType.mono_l b2 b3

def TShape.HasType (x y : TShape) : Prop := (x.2.lift (max x.1 y.1)).HasType (y.2.lift _)

theorem TShape.HasType.def {x y : TShape} (h1 : x.1 ≤ m) (h2 : y.1 ≤ m) :
    x.HasType y ↔ (x.2.lift m).HasType (y.2.lift m) := by
  refine (WShape.HasType.lift (Nat.max_le.2 ⟨h1, h2⟩)).symm.trans ?_
  rw [WShape.lift_lift (.inl (Nat.le_max_left ..)), WShape.lift_lift (.inl (Nat.le_max_right ..))]

theorem WShape.HasType.T_iff {x y : WShape n} : x.T.HasType y.T ↔ x.HasType y := by
  refine (TShape.HasType.def (x := x.T) (y := y.T) (Nat.le_refl _) (Nat.le_refl _)).trans ?_
  simp [WShape.HasType, WShape.lift_self]

theorem WShape.HasType.T {x y : WShape n} : x.HasType y → x.T.HasType y.T := T_iff.2

theorem TShape.HasType.bot_r (H : HasType x .bot) : x ≤ .bot := by
  simp only [TShape.HasType, bot, WShape.lift_bot] at H
  have h := WShape.HasType.bot_r H
  simp only [TShape.LE.def', bot, WShape.lift_bot]
  exact (h : x.2.lift _ = .bot) ▸ WShape.LE.rfl

theorem TShape.HasType.mono_r {m a a' : TShape} (ha : a ≤ a')
    (h1 : HasType a' (.sort r)) (h2 : HasType m a) : HasType m a' := by
  let k := max (max m.1 a.1) a'.1
  have hk := Nat.max_le.1 (Nat.le_refl k); rw [Nat.max_le] at hk
  have h1 := (TShape.HasType.def hk.2 (Nat.zero_le _)).1 h1
  have h2 := (TShape.HasType.def hk.1.1 hk.1.2).1 h2
  have ha := (TShape.LE.def hk.1.2 hk.2).1 ha
  exact (TShape.HasType.def hk.1.1 hk.2).2 (h1.mono_r ha h2)

theorem TShape.HasType.bot : HasType x (.sort r) → HasType .bot x := by
  rw [TShape.HasType.def (Nat.le_refl _) (Nat.zero_le _),
    TShape.HasType.def (Nat.zero_le _) (Nat.le_refl _)]
  simp [sort]; exact .bot

theorem TShape.HasType.bot' : HasType x .type → HasType .bot x := .bot

theorem TShape.HasType.sort : HasType (.sort r) .type := by
  simp [HasType, TShape.sort, TShape.type, WShape.lift_sort, WShape.HasType]
  exact WShape.HasType.sort

theorem TShape.HasType.join' (hJ : Join m₁ m₂ m)
    (h1 : HasType m₁ a) (h2 : HasType m₂ a) : HasType m a := by
  let k := max (max m₁.1 m₂.1) (max m.1 a.1)
  have hk := Nat.max_le.1 (Nat.le_refl k); simp only [Nat.max_le] at hk
  have h1 := (TShape.HasType.def hk.1.1 hk.2.2).1 h1
  have h2 := (TShape.HasType.def hk.1.2 hk.2.2).1 h2
  have hJ := (TShape.Join.def hk.1.1 hk.1.2 hk.2.1).1 hJ
  exact (TShape.HasType.def hk.2.1 hk.2.2).2 (h1.join' hJ h2)

theorem TShape.HasType.bot_r' (ha : a ≤ .bot) (H : HasType x a) : x ≤ .bot :=
  (mono_r (r := true) ha (.bot' .sort) H).bot_r

nonrec theorem TShape.HasType.isType (H : HasType m a) : a.HasType .type :=
  let k := max m.1 a.1; have hk := Nat.max_le.1 (Nat.le_refl k)
  (TShape.HasType.def hk.2 (Nat.zero_le _)).2 H.isType

inductive LE_Forall {n} : TShape → WShape n → WShapeFun n → Prop where
  | bot : a ≤ .bot → LE_Forall a b f
  | forallE : b'.T ≤ b.T → TShapeFun.LE (n := m) f' f →
    LE_Forall (WShape.T (n := m+1) (.forallE b' f')) b f

theorem TShape.LE.le_forall (ha : a ≤ WShape.T (n := n+1) (.forallE b f)) :
    LE_Forall a b f := by
  by_cases h : a ≤ .bot; · exact .bot h
  obtain ⟨an, aw⟩ := a
  cases an with
  | zero =>
    exfalso; apply h; rw [TShape.le_bot]
    have hle := (TShape.LE.def (Nat.zero_le _) (Nat.le_refl _)).1 ha
    have hle_raw : (aw.lift _).1 ≤ ((WShape.forallE b f).lift _).1 := hle
    rw [WShape.lift_val (Nat.zero_le _), WShape.lift_val (Nat.le_refl _)] at hle_raw
    obtain ⟨val, wf⟩ := aw
    cases val with | bot => rfl | sort r
    simp [Shape.lift, WShape.forallE, Shape.LE.def] at hle_raw
  | succ m =>
    have hle := (TShape.LE.def (Nat.succ_le_succ (Nat.le_max_left m n))
        (Nat.succ_le_succ (Nat.le_max_right m n))).1 ha
    have hle_raw : (aw.lift _).1 ≤ ((WShape.forallE b f).lift _).1 := hle
    rw [WShape.lift_val (Nat.succ_le_succ (Nat.le_max_left m n)),
        WShape.lift_val (Nat.succ_le_succ (Nat.le_max_right m n))] at hle_raw
    simp only [WShape.forallE, Shape.lift] at hle_raw
    obtain ⟨val, wf⟩ := aw
    cases val with
    | bot => exfalso; apply h; rw [TShape.le_bot]; rfl
    | forallE b' f' =>
      simp [Shape.lift, Shape.LE.def] at hle_raw
      let b'w : WShape m := ⟨b', wf.1⟩; let f'w : WShapeFun m := ⟨f', wf.2⟩
      have le₁ := Nat.le_max_left m n; have le₂ := Nat.le_max_right m n
      refine .forallE
        ((TShape.LE.def le₁ le₂).2 (?_ : (b'w.lift _).1 ≤ (b.lift _).1))
        ((TShapeFun.LE.def le₁ le₂).2 (?_ : (f'w.lift _).1.LE (f.lift _).1))
      · rw [WShape.lift_val le₁, WShape.lift_val le₂]; exact hle_raw.1
      · rw [WShapeFun.lift_val le₁, WShapeFun.lift_val le₂]; exact hle_raw.2
    | _ => simp [Shape.lift, Shape.LE.def] at hle_raw

def TShape.HasTypeLam (f : WShapeFun n) (a : WShape m) (b : WShapeFun m) :=
  WShape.HasTypeLam (f.lift (max n m)) (a.lift (max n m)) (b.lift (max n m))

theorem TShape.HasTypeLam.def (le₁ : n ≤ k) (le₂ : m ≤ k) :
    HasTypeLam (n := n) (m := m) f a b ↔
    WShape.HasTypeLam (f.lift k) (a.lift k) (b.lift k) := by
  rw [TShape.HasTypeLam, ← WShape.HasTypeLam.lift (Nat.max_le.2 ⟨le₁, le₂⟩),
    WShapeFun.lift_lift (.inl (Nat.le_max_left ..)), WShape.lift_lift (.inl (Nat.le_max_right ..)),
    WShapeFun.lift_lift (.inl (Nat.le_max_right ..))]

theorem TShape.HasType.ty_forallE_inv
    {x : TShape} (H : x.HasType (WShape.T (n := m+1) (.forallE b f))) :
    x = .bot ∨ ∃ n g, x = WShape.T (n := n+1) (.lam' g) ∧ TShape.HasTypeLam g b f := by
  refine have le₁ := Nat.le_succ_of_le (Nat.le_max_left ..)
    have le₂ := Nat.succ_le_succ (Nat.le_max_right ..)
    have H := (TShape.HasType.def le₁ le₂).1 H; ?_
  rw [WShape.lift_forallE (Nat.le_of_succ_le_succ le₂)] at H
  have ⟨g, hg, htl⟩ := WShape.HasType.forallE_inv H
  obtain ⟨_|n, x⟩ := x
  · unfold WShape.lam' at hg; split at hg
    · obtain ⟨⟨⟩, _⟩ := x <;> cases congrArg (·.1) hg
    · dsimp at le₁; cases (WShape.lift_eq_bot le₁).1 hg; exact .inl rfl
  refine .inr ⟨n, ?_⟩; dsimp at *
  obtain ⟨rfl, h⟩ | ⟨g, rfl, rfl⟩ := WShape.lift_eq_lam' (Nat.le_of_succ_le_succ le₁) hg
  · refine ⟨.bot, by simp, ?_⟩
    rw [HasTypeLam, WShapeFun.lift_bot, ← WShapeFun.lift_bot,
      WShape.HasTypeLam.lift (Nat.le_max_right ..), WShape.HasTypeLam.bot]
    obtain ⟨_, h, _⟩ := WShape.HasType.forallE_l.1 <| WShape.HasType.bot_iff.1 H
    exact (WShape.HasTypePi.lift (Nat.le_of_succ_le_succ le₂)).1 h |>.toType
  · exact ⟨_, rfl, (HasTypeLam.def (by omega) (by omega)).2 htl⟩

theorem TShape.HasType.mono_l {m a : TShape}
    (hm1 : m ≤ m') (hm2 : m' ≤ m) (H : HasType m a) : HasType m' a := by
  let k := max (max m.1 a.1) m'.1
  have hk := Nat.max_le.1 (Nat.le_refl k); rw [Nat.max_le] at hk
  have H := (TShape.HasType.def hk.1.1 hk.1.2).1 H
  have hm1 := (TShape.LE.def hk.1.1 hk.2).1 hm1
  have hm2 := (TShape.LE.def hk.2 hk.1.1).1 hm2
  exact (TShape.HasType.def hk.2 hk.1.2).2 (H.mono_l hm1 hm2)

theorem TShape.HasType.sort_T : HasType (WShape.T (n := n) (.sort r)) .type :=
  mono_l TShape.sort_eqv.2 TShape.sort_eqv.1 .sort

theorem TShape.HasType.sort_r {x : WShape n} : x.T.HasType (.sort r) ↔ x.HasType (.sort r) :=
  .trans ⟨mono_r TShape.sort_eqv.2 .sort_T, mono_r TShape.sort_eqv.1 .sort⟩ WShape.HasType.T_iff

theorem TShape.HasType.bot_T (H : HasType x (.sort r)) : HasType (WShape.T (n := n) .bot) x :=
  H.bot.mono_l bot_eqv.2 bot_eqv.1
theorem TShape.HasType.bot_T' (H : HasType x .type) : HasType (WShape.T (n := n) .bot) x := H.bot_T

theorem TShape.HasType.join {m₁ m₂ a : TShape} (hJ : m₁.Compat m₂)
    (h1 : m₁.HasType a) (h2 : m₂.HasType a) : (m₁.join m₂).HasType a := by
  let k := max (max m₁.1 m₂.1) a.1
  have hk := Nat.max_le.1 (Nat.le_refl k); simp only [Nat.max_le] at hk
  have h1 := (TShape.HasType.def hk.1.1 hk.2).1 h1
  have h2 := (TShape.HasType.def hk.1.2 hk.2).1 h2
  have hJ := (TShape.Compat.def hk.1.1 hk.1.2).1 hJ
  have := TShape.lift_join hk.1.1 hk.1.2 ▸ h1.join hJ h2
  exact (TShape.HasType.def (Nat.max_le.2 hk.1) hk.2).1 this

theorem WShape.HasType.proofIrrel
    (ha : HasType (n := n) a .prop) (hx : HasType x a) : x = .bot := by
  cases n with | zero => cases ha.unfold; exact hx.bot_r | succ n
  cases ha.unfold with | bot => exact hx.bot_r | @forallE _ b a _ ha
  generalize eq : WShape.forallE .. = t at hx
  cases hx.unfold with | bot => rfl | @lam _ f a' b' hx' => ?_ | _ => cases eq
  obtain ⟨rfl, rfl⟩ : a = a' ∧ b = b' := by
    cases a'; cases b'; cases congrArg (·.1) eq; exact ⟨rfl, rfl⟩
  unfold lam'; split <;> [rename_i hf; rfl]
  obtain ⟨⟨x, y⟩, h1, h2⟩ := hf; have ⟨hx, hy⟩ := f.2.2 _ h1; change (⟨x,hx⟩, ⟨y,hy⟩) ∈ f at h1
  have ⟨x', a1, a2, a3⟩ := WShape.HasDom.iff.1 hx'.2.1 ⟨x, hx⟩
  have hfx := (WShape.HasTypeLam.iff.1 hx').2.2 x' a2
  have hba := (WShape.HasTypePi.iff.1 ha).2 x' a2
  cases h2 <| (f.app_of_mem h1).2.trans <| a3.trans <| le_bot.2 <| proofIrrel hba hfx

theorem TShape.HasType.proofIrrel
    (ha : HasType a (.sort false)) (hx : HasType x a) : x ≤ .bot := by
  let k := max x.1 a.1; have hk := Nat.max_le.1 (Nat.le_refl k)
  have ha' := (TShape.HasType.def hk.2 (Nat.zero_le _)).1 ha
  have hx' := (TShape.HasType.def hk.1 hk.2).1 hx
  simp [TShape.sort] at ha'
  have := ha'.proofIrrel hx'
  rw [TShape.LE.def hk.1 (Nat.zero_le _)]
  simp [TShape.bot, WShape.lift_bot, this]

theorem WShape.HasType.retype (ha : HasType (n := n) a (.sort r))
    (ha' : HasType a' (.sort r')) (le : a ≤ a') : HasType a (.sort r') := by
  cases n with
  | zero =>
    cases ha.unfold with
    | bot => exact .bot .sort
    | sort => exact sort_le.1 le ▸ ha'
  | succ n
  cases ha.unfold with
  | bot => exact .bot .sort
  | sort => exact sort_le.1 le ▸ ha'
  | indTy => exact (show a' = .indTy from Subtype.ext (Shape.indTy_le.1 le)) ▸ ha'
  | forallE Ha
  obtain ⟨_, _, le₁, le₂, rfl⟩ := WShape.forallE_le.1 le
  have ⟨H1, H2⟩ := HasTypePi.iff'.1 Ha
  obtain ⟨_, Ha', ⟨⟩⟩ := forallE_l.1 ha'
  refine .forallE <| HasTypePi.iff'.2 ⟨H1, fun x => ?_⟩
  exact retype (H2 _) ((HasTypePi.iff'.1 Ha').2 x) (WShapeFun.app_mono_l le₂ _)

theorem TShape.HasType.retype (ha : HasType a (.sort r))
    (ha' : HasType a' (.sort r')) (le : a ≤ a') : HasType a (.sort r') := by
  let k := max a.1 a'.1; have hk := Nat.max_le.1 (Nat.le_refl k)
  have ha := (TShape.HasType.def hk.1 (Nat.zero_le _)).1 ha
  have ha' := (TShape.HasType.def hk.2 (Nat.zero_le _)).1 ha'
  exact (TShape.HasType.def hk.1 (Nat.zero_le _)).2 <| ha.retype ha' le

theorem WShape.HasDom.single :
    HasDom (WShapeFun.single x y) a ↔ x.HasType a ∨ y ≤ .bot ∧ a.HasType .type := by
  simp [HasDom.def, WShapeFun.mem_single]
  refine ⟨fun H => ?_, ?_⟩
  · obtain ⟨x, y, ⟨rfl, rfl⟩ | ⟨h, rfl, rfl⟩, h2, h3, h4⟩ := H _ _ (.inl ⟨rfl, rfl⟩)
    · exact .inl h4
    · exact .inr ⟨h3, h4.isType⟩
  · rintro H x y (⟨rfl, rfl⟩ | ⟨h, rfl, rfl⟩)
    · obtain h | ⟨h1, h2⟩ := H
      · exact ⟨_, _, .inl ⟨rfl, rfl⟩, .rfl, .rfl, h⟩
      · by_cases hx : x ≤ .bot
        · exact ⟨_, _, .inl ⟨rfl, rfl⟩, .rfl, .rfl, le_bot.1 hx ▸ .bot' h2⟩
        · exact ⟨_, _, .inr ⟨hx, rfl, rfl⟩, bot_le, h1, .bot' h2⟩
    · refine ⟨_, _, .inr ⟨h, rfl, rfl⟩, .rfl, .rfl, .bot' ?_⟩
      obtain h | ⟨_, h⟩ := H <;> [exact h.isType; exact h]

theorem WShape.HasDom.mono (le : a ≤ a') (h : a'.HasType .type) (H : HasDom f a) : HasDom f a' :=
  HasDom.def.2 fun x y hm => let ⟨x', y', h1, h2, h3, h4⟩ := HasDom.def.1 H x y hm
    ⟨x', y', h1, h2, h3, .mono_r le h h4⟩

def Valuation := Nat → TShape

def Valuation.nil : Valuation := fun _ => ⟨0, .bot⟩
def Valuation.push (ρ : Valuation) (u : TShape) : Valuation
  | 0 => u
  | n+1 => ρ n

def Valuation.LE (ρ ρ' : Valuation) : Prop := ∀ n, ρ n ≤ ρ' n

theorem Valuation.LE.rfl {ρ : Valuation} : ρ.LE ρ := fun _ => .rfl

theorem Valuation.LE.push {ρ ρ' : Valuation} :
    (ρ.push a).LE (ρ'.push a') ↔ ρ.LE ρ' ∧ a ≤ a' :=
  ⟨fun H => ⟨fun _ => H (_+1), H 0⟩, fun ⟨H1, H2⟩ => fun | 0 => H2 | _+1 => H1 _⟩

/-- Two valuations are compatible if their entries are compatible at each index
(after lifting to a common level). -/
def Valuation.Compat (ρ₁ ρ₂ : Valuation) : Prop := ∀ i, (ρ₁ i).Compat (ρ₂ i)

/-- Pointwise join of two valuations. Each entry is lifted to a common level and joined. -/
def Valuation.join (ρ₁ ρ₂ : Valuation) : Valuation := fun i => (ρ₁ i).join (ρ₂ i)

theorem Valuation.Compat.le_join {ρ₁ ρ₂ : Valuation}
    (hc : ρ₁.Compat ρ₂) : ρ₁.LE (ρ₁.join ρ₂) ∧ ρ₂.LE (ρ₁.join ρ₂) :=
  ⟨fun i => (TShape.Join.mk (hc i)).le.1, fun i => (TShape.Join.mk (hc i)).le.2⟩

inductive LE_Interp.Matches : (p : Pattern) → ∀ {n}, Name → List (WShape n) → (p.Path → TShape) → Prop
  | const : Matches (.const c) c [] nofun
  | var : Matches f c rargs mf → Matches (.var f) c (a :: rargs) (·.elim a.T mf)
  | app : Matches (n := n+1) f c rargs mf → Matches (n := n) a c' rargs' ma →
    Matches (n := n+1) (.app f a) c (.ctor' c' rargs'.reverse :: rargs) (Sum.elim mf ma)

variable {p : Pattern} (ls : List SLevel) (m2 : p.Path → TShape)
  (R : TShape → SExpr → Prop) in
inductive LE_Interp.RHS : TShape → p.RHS → Prop
  | bot : RHS (WShape.T .bot) r
  | const : R m (SExpr.mkInst ls e) → RHS m (.fixed e cl)
  | var : m ≤ m2 path → RHS m (.var path)
  | app : RHS (WShape.T (n := n + 1) f) F → RHS a.T A → m ≤ (f.app a).T → RHS m (.app F A)

/-- The semantic application spine selected by an ordered list of capture
paths.  Each step retains both the semantic argument bound attached to the
path and the (possibly strict) result bound chosen by `RHS.app`. -/
inductive LE_Interp.RHS.ShapeSpine {p : Pattern}
    (m2 : p.Path → TShape) : TShape → List p.Path → TShape → Prop
  | nil : ShapeSpine m2 head [] head
  | cons {n : Nat} {f : WShape (n + 1)} {a : WShape n}
      {m out : TShape} {path : p.Path} {paths : List p.Path} :
    a.T ≤ m2 path →
    m ≤ (f.app a).T →
    ShapeSpine m2 m paths out →
    ShapeSpine m2 f.T (path :: paths) out

/-- A semantic variable RHS is bounded by the shape assigned to its path,
including the proof-irrelevant bottom interpretation. -/
theorem LE_Interp.RHS.var_le
    (H : LE_Interp.RHS ls m2 R m (.var path)) : m ≤ m2 path := by
  cases H with
  | bot => exact TShape.bot_le'
  | var h => exact h

/-- Once the head of a semantic application spine is bottom, every later
application result is bottom as well. -/
theorem LE_Interp.RHS.ShapeSpine.le_bot
    (H : ShapeSpine m2 head paths out) (hhead : head ≤ TShape.bot) :
    out ≤ TShape.bot := by
  induction H with
  | nil => exact hhead
  | @cons n f a m out path paths harg happ hrest ih =>
    have hf_bot : f = .bot := by
      exact TShape.le_bot.1 hhead
    have happ_bot : (f.app a).T ≤ TShape.bot := by
      rw [hf_bot, WShape.bot_app]
      exact TShape.bot_eqv.1
    exact ih (happ.trans happ_bot)

/-- Enlarge every capture bound without changing the ordered application
spine.  This is used by proof-relevant RHS inversion when the same capture
path occurs more than once: its selected argument observations are joined,
while the fixed-head witness remains untouched. -/
theorem LE_Interp.RHS.ShapeSpine.mono_l
    (H : ShapeSpine m2 head paths out)
    (hle : ∀ path, m2 path ≤ m2' path) :
    ShapeSpine m2' head paths out := by
  induction H with
  | nil => exact .nil
  | cons harg happ _ ih => exact .cons (harg.trans (hle _)) happ ih

/-- Reassemble an `appN` RHS from its fixed head and ordered semantic
application spine.  Keeping this direction separate from `appN_vars` lets a
proof-relevant producer replace the ambient evaluator relation by the
singleton relation generated by the exact fixed-head witness it selected. -/
theorem LE_Interp.RHS.ShapeSpine.to_appN
    (H : ShapeSpine m2 head paths out)
    (hhead : LE_Interp.RHS ls m2 R head f) :
    LE_Interp.RHS ls m2 R out
      (Pattern.RHS.appN f (paths.map fun path => .var path)) := by
  induction H generalizing f with
  | nil => exact hhead
  | cons harg happ _ ih =>
    simp only [List.map_cons, Pattern.RHS.appN]
    exact ih (.app hhead (.var harg) happ)

/-- Reconstruct a typed lower approximation of the fixed head from a typed
semantic RHS result.  Each application layer is represented by a singleton
function shape: its input is the related capture approximation and its output
is the typed approximation recursively recovered from the remaining spine.

This is the shape-level half of the generated-iota logical telescope.  It is
deliberately independent of syntax and of the logical relation; the adequacy
consumer separately aligns the synthesized type telescope with the registered
RHS type while following the well-founded semantic `R` edge. -/
theorem LE_Interp.RHS.ShapeSpine.typedLowerHead
    {p : Pattern} {m2 : p.Path → TShape} {paths : List p.Path}
    {head out outTy : TShape}
    (H : LE_Interp.RHS.ShapeSpine m2 head paths out)
    (hcap : ∀ path, ∃ elem elemTy : TShape,
      m2 path ≤ elem ∧ elem.HasType elemTy)
    (hout : out.HasType outTy) :
    ∃ elem elemTy : TShape, elem ≤ head ∧ elem.HasType elemTy := by
  induction H generalizing outTy with
  | @nil head0 => exact ⟨head0, outTy, .rfl, hout⟩
  | @cons n f a m out path paths harg happ hrest ih =>
    obtain ⟨next, nextTy, hnext, hnextTy⟩ := ih hout
    by_cases hnextBot : next ≤ TShape.bot
    · exact ⟨WShape.T (n := n + 1) .bot, WShape.T .type,
        TShape.bot_le', WShape.HasType.T (.bot' .sort)⟩
    obtain ⟨arg, argTy, harg', hargTy⟩ := hcap path
    have hnextApp : next ≤ (f.app a).T := hnext.trans happ
    cases f using WShape.casesOn' with
    | bot => exact (hnextBot (hnextApp.trans TShape.bot_eqv.1)).elim
    | sort => exact (hnextBot (hnextApp.trans TShape.bot_eqv.1)).elim
    | forallE => exact (hnextBot (hnextApp.trans TShape.bot_eqv.1)).elim
    | ctor => exact (hnextBot (hnextApp.trans TShape.bot_eqv.1)).elim
    | indTy => exact (hnextBot (hnextApp.trans TShape.bot_eqv.1)).elim
    | @lam g hg =>
      let k := max n (max (max arg.1 argTy.1) (max next.1 nextTy.1))
      have hk : n ≤ k ∧ arg.1 ≤ k ∧ argTy.1 ≤ k ∧
          next.1 ≤ k ∧ nextTy.1 ≤ k := by
        dsimp [k]
        omega
      let argK : WShape k := arg.2.lift k
      let argTyK : WShape k := argTy.2.lift k
      let nextK : WShape k := next.2.lift k
      let nextTyK : WShape k := nextTy.2.lift k
      let elemFun : WShapeFun k := .single argK nextK
      let typeFun : WShapeFun k := .single argK nextTyK
      let elemHead : WShape (k + 1) := .lam' elemFun
      let typeHead : WShape (k + 1) := .forallE argTyK typeFun
      have hargKTy : argK.HasType argTyK :=
        (TShape.HasType.def hk.2.1 hk.2.2.1).1 hargTy
      have hnextKTy : nextK.HasType nextTyK :=
        (TShape.HasType.def hk.2.2.2.1 hk.2.2.2.2).1 hnextTy
      have helemTyped : elemHead.HasType typeHead := by
        apply WShape.HasType.lam
        refine WShape.HasTypeLam.iff'.2 ⟨?_, ?_, fun x => ?_⟩
        · refine WShape.HasTypePi.def.2
            ⟨WShape.HasDom.single.2 (.inl hargKTy), ?_⟩
          intro x y hxy
          obtain ⟨rfl, rfl⟩ | ⟨_, rfl, rfl⟩ := WShapeFun.mem_single.1 hxy
          · exact hnextKTy.isType
          · exact .bot' .sort
        · exact WShape.HasDom.single.2 (.inl hargKTy)
        · simp only [elemFun, typeFun, WShapeFun.single_app]
          split <;> [exact hnextKTy; exact .bot' (.bot' .sort)]
      have hargBound : a.T ≤ arg := harg.trans harg'
      have hnextAppK : nextK ≤ (g.lift k).app argK := by
        have hnextApp' : next ≤ ((WShape.lam g hg).app a).T := by
          simpa using hnextApp
        have hmono : ((WShape.lam g hg).app a).T ≤
            ((WShape.lam (g.lift k)
              (WShapeFun.NonZero.lift_iff hk.1 |>.2 hg)).app argK).T := by
          apply TShape.app_mono
          · have hLift := (TShape.lift_eqv
              (a := (WShape.lam g hg).T) (Nat.succ_le_succ hk.1)).2
            rw [WShape.lift_lam hk.1] at hLift
            exact hLift
          · exact hargBound.trans (TShape.lift_eqv hk.2.1).2
        have hT : next ≤ ((g.lift k).app argK).T := by
          simpa [WShape.lam_eq_lam'] using hnextApp'.trans hmono
        have hTK := (TShape.LE.def
          (a := next) (b := ((g.lift k).app argK).T)
          hk.2.2.2.1 (Nat.le_refl k)).1 hT
        simpa only [nextK, WShape.lift_self] using hTK
      have helemLe : elemHead.T ≤ (WShape.lam g hg).T := by
        apply (TShape.LE.def (a := elemHead.T) (b := (WShape.lam g hg).T)
          (Nat.le_refl (k + 1)) (Nat.succ_le_succ hk.1)).2
        simp only [WShape.lift_self]
        rw [WShape.lift_lam hk.1, WShape.lam_eq_lam']
        apply WShape.lam'_le_lam'.2
        obtain ⟨x, hx, hmem⟩ := (g.lift k).app_eq argK
        exact WShapeFun.single_le.2 ⟨x, _, hmem, hx, hnextAppK⟩
      exact ⟨elemHead.T, typeHead.T, helemLe, helemTyped.T⟩

/-- Rebuild one synchronized function/type layer below a semantic RHS head.

The non-structural input is `hargCap`: the semantic argument selected by the
RHS spine must have a typed upper bound in the domain exposed by the
registered type telescope.  Once that capture-domain link is retained, the
singleton layer is entirely shape-theoretic.  In particular, no typing is
pulled down through an arbitrary function observation. -/
theorem LE_Interp.RHS.ShapeSpine.peelTypedLayer
    {n : Nat} {g : WShapeFun n}
    {tyDom : WShape n} {tyFun : WShapeFun n}
    {aSp argCap : WShape n}
    (hargCap : aSp ≤ argCap)
    (hcapDom : argCap.HasType tyDom)
    {next nextTy : WShape n}
    (hnext : next ≤ g.app aSp)
    (hnextTy : next.HasType nextTy)
    (hnextLe : nextTy ≤ tyFun.app argCap) :
    ∃ elem elemTy : WShape (n + 1),
      elem ≤ .lam' g ∧ elem.HasType elemTy ∧
        elemTy ≤ .forallE tyDom tyFun := by
  refine ⟨.lam' (.single argCap next), .forallE tyDom (.single argCap nextTy),
    ?_, ?_, ?_⟩
  · apply WShape.lam'_le_lam'.2
    obtain ⟨x', hx', hmem⟩ := g.app_eq argCap
    exact WShapeFun.single_le.2
      ⟨x', _, hmem, hx', hnext.trans (WShapeFun.app_mono_r hargCap)⟩
  · apply WShape.HasType.lam
    refine WShape.HasTypeLam.iff'.2 ⟨?_, ?_, fun x => ?_⟩
    · refine WShape.HasTypePi.def.2
        ⟨WShape.HasDom.single.2 (.inl hcapDom), ?_⟩
      intro x y hxy
      obtain ⟨rfl, rfl⟩ | ⟨_, rfl, rfl⟩ := WShapeFun.mem_single.1 hxy
      · exact hnextTy.isType
      · exact .bot' .sort
    · exact WShape.HasDom.single.2 (.inl hcapDom)
    · simp only [WShapeFun.single_app]
      split <;> [exact hnextTy; exact .bot' (.bot' .sort)]
  · apply WShape.forallE_le_forallE.2
    refine ⟨.rfl, ?_⟩
    obtain ⟨x', hx', hmem⟩ := tyFun.app_eq argCap
    exact WShapeFun.single_le.2 ⟨x', _, hmem, hx', hnextLe⟩

/-- The recursively synchronized endpoint of a semantic RHS application
spine.  Besides rebuilding a typed lower approximation of the term head,
the package records that its type observation lies below the *particular*
registered-type observation threaded through the same ordered telescope.

This is intentionally a certificate over an existing `ShapeSpine`, rather
than a pointwise family indexed by capture paths: dependent application
requires the domain selected at one layer to determine the type observation
used by every later layer. -/
def LE_Interp.RHS.ShapeSpine.TypedLowerHead
    {p : Pattern} {m2 : p.Path → TShape}
    {head out : TShape} {paths : List p.Path}
    (spine : LE_Interp.RHS.ShapeSpine m2 head paths out)
    (headTy : TShape) : Prop :=
  ∃ elem elemTy : TShape,
    elem ≤ head ∧ elem.HasType elemTy ∧ elemTy ≤ headTy

/-- An ordered type telescope synchronized with one exact semantic
`ShapeSpine`.  The codomain observation in the recursive constructor is
definitionally the application of the current type function to the same
`argCap` that types the current semantic argument.  This is the dependency
that a pointwise path map cannot express. -/
inductive LE_Interp.RHS.ShapeSpine.TypedTelescope
    {p : Pattern} (m2 : p.Path → TShape) :
  ∀ {head paths out},
      LE_Interp.RHS.ShapeSpine m2 head paths out →
        TShape → TShape → Prop where
  | nil (htyped : head.HasType headTy) :
      TypedTelescope m2
        (LE_Interp.RHS.ShapeSpine.nil (m2 := m2) (head := head))
        headTy headTy
  | cons
      {n : Nat} {f : WShape (n + 1)} {a : WShape n}
      {m out : TShape} {path : p.Path} {paths : List p.Path}
      {harg : a.T ≤ m2 path} {happ : m ≤ (f.app a).T}
      {rest : LE_Interp.RHS.ShapeSpine m2 m paths out}
      {tyDom : WShape n} {tyFun : WShapeFun n} {argCap : WShape n}
      {outTy : TShape} :
      a ≤ argCap → argCap.HasType tyDom →
      TypedTelescope m2 rest (tyFun.app argCap).T outTy →
      TypedTelescope m2
        (LE_Interp.RHS.ShapeSpine.cons harg happ rest)
        (WShape.forallE tyDom tyFun).T outTy

/-- Consumer-specific evidence synchronized with an ordered typed
telescope.  `Cap path argCap tyDom` is deliberately indexed by the exact
argument and domain shapes stored in the telescope constructor: this keeps
the semantic bound, typing fact, and later logical application witness from
choosing three unrelated existential representatives.

The shape module leaves `Cap` abstract.  The adequacy consumer instantiates
it with the aligned capture relation at the logical-relation level selected
by that application layer. -/
inductive LE_Interp.RHS.ShapeSpine.TypedTelescope.Captures
    {p : Pattern} {m2 : p.Path → TShape}
    (Cap : ∀ {n}, p.Path → WShape n → WShape n → Prop) :
    ∀ {head out headTy outTy : TShape} {paths : List p.Path}
      {spine : LE_Interp.RHS.ShapeSpine m2 head paths out},
      LE_Interp.RHS.ShapeSpine.TypedTelescope
        m2 spine headTy outTy → Prop where
  | nil {head headTy : TShape} (htyped : head.HasType headTy) :
      Captures Cap
        (LE_Interp.RHS.ShapeSpine.TypedTelescope.nil htyped)
  | cons
      {n : Nat} {f : WShape (n + 1)} {a : WShape n}
      {m out : TShape} {path : p.Path} {paths : List p.Path}
      {harg : a.T ≤ m2 path} {happ : m ≤ (f.app a).T}
      {rest : LE_Interp.RHS.ShapeSpine m2 m paths out}
      {tyDom : WShape n} {tyFun : WShapeFun n} {argCap : WShape n}
      {outTy : TShape}
      (hargCap : a ≤ argCap) (hcapDom : argCap.HasType tyDom)
      {tail : LE_Interp.RHS.ShapeSpine.TypedTelescope
        m2 rest (tyFun.app argCap).T outTy} :
      Cap path argCap tyDom →
      Captures Cap tail →
      Captures Cap
        (LE_Interp.RHS.ShapeSpine.TypedTelescope.cons
          (harg := harg) (happ := happ)
          hargCap hcapDom tail)

/-- One ordered telescope with its consumer payload stored in the same
constructor tree.

`TypedTelescope` plus `Captures` is a useful eliminator-facing view, but the
pair is cumbersome at a producer boundary: dependent elimination must prove
that two separately supplied proofs describe the same layer choices.  This
packed form makes that synchronization definitional. -/
inductive LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCaptures
    {p : Pattern} {m2 : p.Path → TShape}
    (Cap : ∀ {n}, p.Path → WShape n → WShape n → Prop) :
    TShape → List p.Path → TShape → TShape → TShape → Prop where
  | nil (htyped : head.HasType headTy) :
      WithCaptures Cap head [] head headTy headTy
  | cons
      {n : Nat} {f : WShape (n + 1)} {a : WShape n}
      {m out : TShape} {path : p.Path} {paths : List p.Path}
      {tyDom : WShape n} {tyFun : WShapeFun n} {argCap : WShape n}
      {outTy : TShape} :
      a.T ≤ m2 path → m ≤ (f.app a).T →
      a ≤ argCap → argCap.HasType tyDom →
      Cap path argCap tyDom →
      WithCaptures Cap m paths out (tyFun.app argCap).T outTy →
      WithCaptures Cap f.T (path :: paths) out
        (WShape.forallE tyDom tyFun).T outTy

/-- Recover the semantic spine retained by a packed telescope. -/
theorem LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCaptures.spine
    {p : Pattern} {m2 : p.Path → TShape}
    {Cap : ∀ {n}, p.Path → WShape n → WShape n → Prop}
    {head out headTy outTy : TShape} {paths : List p.Path}
    (H : LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCaptures
      (m2 := m2) Cap head paths out headTy outTy) :
    LE_Interp.RHS.ShapeSpine m2 head paths out := by
  induction H with
  | nil _ => exact .nil
  | cons harg happ _ _ _ _ ih => exact .cons harg happ ih

/-- Forget a packed telescope's payload while retaining every ordered shape
choice definitionally. -/
theorem LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCaptures.telescope
    {p : Pattern} {m2 : p.Path → TShape}
    {Cap : ∀ {n}, p.Path → WShape n → WShape n → Prop}
    {head out headTy outTy : TShape} {paths : List p.Path}
    (H : LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCaptures
      (m2 := m2) Cap head paths out headTy outTy) :
    LE_Interp.RHS.ShapeSpine.TypedTelescope
      m2 H.spine headTy outTy := by
  induction H with
  | nil htyped => exact .nil htyped
  | cons harg happ hargCap hcapDom _ _ ih =>
    exact .cons (harg := harg) (happ := happ) hargCap hcapDom ih

/-- Recover the indexed payload view when an existing consumer expects the
older split presentation. -/
theorem LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCaptures.captures
    {p : Pattern} {m2 : p.Path → TShape}
    {Cap : ∀ {n}, p.Path → WShape n → WShape n → Prop}
    {head out headTy outTy : TShape} {paths : List p.Path}
    (H : LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCaptures
      (m2 := m2) Cap head paths out headTy outTy) :
    LE_Interp.RHS.ShapeSpine.TypedTelescope.Captures
      Cap H.telescope := by
  induction H with
  | nil htyped => exact .nil htyped
  | cons harg happ hargCap hcapDom capture _ ih =>
    exact .cons (harg := harg) (happ := happ)
      hargCap hcapDom capture ih

/-- The empty ordered telescope retains the supplied result typing
verbatim. -/
theorem LE_Interp.RHS.ShapeSpine.TypedLowerHead.of_nil
    {p : Pattern} {m2 : p.Path → TShape} {head headTy : TShape}
    (htyped : head.HasType headTy) :
    LE_Interp.RHS.ShapeSpine.TypedLowerHead
      (LE_Interp.RHS.ShapeSpine.nil (m2 := m2) (head := head)) headTy :=
  ⟨head, headTy, .rfl, htyped, .rfl⟩

/-- Add one synchronized capture layer to a completed ordered telescope.

The recursive certificate is anchored at the codomain observation selected
by `argCap`.  All level changes are equivalence lifts; the only substantive
step is `peelTypedLayer`, so no typing is pulled backwards through an
arbitrary function-shape inequality. -/
theorem LE_Interp.RHS.ShapeSpine.TypedLowerHead.cons
    {p : Pattern} {m2 : p.Path → TShape}
    {n : Nat} {f : WShape (n + 1)} {a : WShape n}
    {m out : TShape} {path : p.Path} {paths : List p.Path}
    (harg : a.T ≤ m2 path) (happ : m ≤ (f.app a).T)
    (rest : LE_Interp.RHS.ShapeSpine m2 m paths out)
    {tyDom : WShape n} {tyFun : WShapeFun n} {argCap : WShape n}
    (hargCap : a ≤ argCap) (hcapDom : argCap.HasType tyDom)
    (tail : LE_Interp.RHS.ShapeSpine.TypedLowerHead rest
      (tyFun.app argCap).T) :
    LE_Interp.RHS.ShapeSpine.TypedLowerHead
      (LE_Interp.RHS.ShapeSpine.cons harg happ rest)
      (WShape.forallE tyDom tyFun).T := by
  obtain ⟨next, nextTy, hnext, hnextTy, hnextTyLe⟩ := tail
  by_cases hnextBot : next ≤ TShape.bot
  · exact ⟨(WShape.bot (n := n + 1)).T,
      (WShape.bot (n := n + 1)).T, TShape.bot_le',
      WShape.HasType.T (.bot' (.bot' .sort)), TShape.bot_le'⟩
  have hnextApp : next ≤ (f.app a).T := hnext.trans happ
  cases f using WShape.casesOn' with
  | bot => exact (hnextBot (hnextApp.trans TShape.bot_eqv.1)).elim
  | sort => exact (hnextBot (hnextApp.trans TShape.bot_eqv.1)).elim
  | forallE => exact (hnextBot (hnextApp.trans TShape.bot_eqv.1)).elim
  | ctor => exact (hnextBot (hnextApp.trans TShape.bot_eqv.1)).elim
  | indTy => exact (hnextBot (hnextApp.trans TShape.bot_eqv.1)).elim
  | @lam g hg =>
    let k := max n (max next.1 nextTy.1)
    have hk : n ≤ k ∧ next.1 ≤ k ∧ nextTy.1 ≤ k := by
      dsimp [k]
      omega
    let aK : WShape k := a.lift k
    let argCapK : WShape k := argCap.lift k
    let tyDomK : WShape k := tyDom.lift k
    let nextK : WShape k := next.2.lift k
    let nextTyK : WShape k := nextTy.2.lift k
    have hargCapK : aK ≤ argCapK := WShape.lift_mono hk.1 hargCap
    have hcapDomK : argCapK.HasType tyDomK :=
      (WShape.HasType.lift hk.1).2 hcapDom
    have hnextAppK : nextK ≤ (g.lift k).app aK := by
      have hnextApp' : next ≤ ((WShape.lam g hg).app a).T := by
        simpa using hnextApp
      have hmono : ((WShape.lam g hg).app a).T ≤
          ((WShape.lam (g.lift k)
            (WShapeFun.NonZero.lift_iff hk.1 |>.2 hg)).app aK).T := by
        apply TShape.app_mono
        · have hLift := (TShape.lift_eqv
            (a := (WShape.lam g hg).T) (Nat.succ_le_succ hk.1)).2
          rw [WShape.lift_lam hk.1] at hLift
          exact hLift
        · exact (TShape.lift_eqv hk.1).2
      have hT : next ≤ ((g.lift k).app aK).T := by
        simpa [WShape.lam_eq_lam'] using hnextApp'.trans hmono
      have hTK := (TShape.LE.def
        (a := next) (b := ((g.lift k).app aK).T)
        hk.2.1 (Nat.le_refl k)).1 hT
      simpa only [nextK, WShape.lift_self] using hTK
    have hnextTyKLe : nextTyK ≤ (tyFun.lift k).app argCapK := by
      have hTK := (TShape.LE.def
        (a := nextTy) (b := (tyFun.app argCap).T)
        hk.2.2 hk.1).1 hnextTyLe
      simpa only [nextTyK, argCapK, WShape.lift_self,
        WShapeFun.lift_app hk.1] using hTK
    obtain ⟨elem, elemTy, helem, helemTy, helemTyLe⟩ :=
      LE_Interp.RHS.ShapeSpine.peelTypedLayer
        (g := g.lift k) (tyFun := tyFun.lift k)
        hargCapK hcapDomK hnextAppK
        ((TShape.HasType.def hk.2.1 hk.2.2).1 hnextTy)
        hnextTyKLe
    refine ⟨elem.T, elemTy.T, ?_, helemTy.T, ?_⟩
    · refine helem.T.trans ?_
      have hLift := (TShape.lift_eqv
        (a := (WShape.lam g hg).T) (Nat.succ_le_succ hk.1)).1
      rw [WShape.lift_lam hk.1, WShape.lam_eq_lam'] at hLift
      exact hLift
    · refine helemTyLe.T.trans ?_
      have hLift := (TShape.lift_eqv
        (a := (WShape.forallE tyDom tyFun).T)
        (Nat.succ_le_succ hk.1)).1
      rw [WShape.lift_forallE hk.1] at hLift
      exact hLift

/-- Forget the internal ordered layers after constructing their synchronized
lower head and its registered-type bound. -/
theorem LE_Interp.RHS.ShapeSpine.TypedTelescope.lowerHead
    {p : Pattern} {m2 : p.Path → TShape}
    {head out headTy outTy : TShape} {paths : List p.Path}
    {spine : LE_Interp.RHS.ShapeSpine m2 head paths out}
    (H : LE_Interp.RHS.ShapeSpine.TypedTelescope
      m2 spine headTy outTy) :
    spine.TypedLowerHead headTy := by
  induction H with
  | nil htyped => exact .of_nil htyped
  | @cons n f a m out path paths harg happ rest tyDom tyFun argCap outTy
      hargCap hcapDom _ ih =>
    exact LE_Interp.RHS.ShapeSpine.TypedLowerHead.cons
      harg happ rest hargCap hcapDom ih

/-- The terminal type observation is retained as an index of the ordered
telescope, so a later logical application fold lands at the caller's exact
result typing rather than at an existentially chosen type shape. -/
theorem LE_Interp.RHS.ShapeSpine.TypedTelescope.outHasType
    {p : Pattern} {m2 : p.Path → TShape}
    {head out headTy outTy : TShape} {paths : List p.Path}
    {spine : LE_Interp.RHS.ShapeSpine m2 head paths out}
    (H : LE_Interp.RHS.ShapeSpine.TypedTelescope
      m2 spine headTy outTy) :
    out.HasType outTy := by
  induction H with
  | nil htyped => exact htyped
  | cons _ _ _ ih => exact ih

/-! ### Terminal-index monotonicity for the packed ordered telescope

`WithCaptures.nil` identifies the telescope's head observation with its
terminal observation as an *index equality*.  That equality is what forces a
finished telescope to terminate at exactly the codomain observation an ordered
type peel reaches, while every consumer of the telescope reads its terminal
index at the result observation its own caller already fixed.  Those two are
independently determined, and identifying them is refutable: the corresponding
retarget statement is `HasType`-functionality at the terminal head, and
`TShape.HasType.bot` types `.bot` at every sort.

`WithCapturesLE` is the additive repair.  Only the base changes: the terminal
observation is recorded *below* the head observation the peel reached rather
than equal to it, and the base typing is stated at the terminal observation —
which is the fact a consumer's caller already holds.  Nothing else moves;
`cons` is verbatim, so every layer is the same layer.

The direction is forced by how the head index is used.  Every consumer reads it
only as an upper bound (`TypedLowerHead` bounds the synthesized lower type by
it; `fixedHeadShapeChain` returns `headElemTy.T ≤ headTy`), so weakening it
upward at the base is sound and is exactly what lets a peel-reached observation
sit above a caller-fixed one. -/

/-- The packed ordered telescope with a monotone terminal index.

`nil` records the caller's result-type observation `outTy` together with the
one comparison `outTy ≤ headTy` against the observation the ordered peel
reached.  `WithCaptures` is the special case `outTy = headTy`
(`WithCaptures.toLE`). -/
inductive LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCapturesLE
    {p : Pattern} {m2 : p.Path → TShape}
    (Cap : ∀ {n}, p.Path → WShape n → WShape n → Prop) :
    TShape → List p.Path → TShape → TShape → TShape → Prop where
  | nil {head headTy outTy : TShape}
      (htyped : head.HasType outTy) (hle : outTy ≤ headTy) :
      WithCapturesLE Cap head [] head headTy outTy
  | cons
      {n : Nat} {f : WShape (n + 1)} {a : WShape n}
      {m out : TShape} {path : p.Path} {paths : List p.Path}
      {tyDom : WShape n} {tyFun : WShapeFun n} {argCap : WShape n}
      {outTy : TShape} :
      a.T ≤ m2 path → m ≤ (f.app a).T →
      a ≤ argCap → argCap.HasType tyDom →
      Cap path argCap tyDom →
      WithCapturesLE Cap m paths out (tyFun.app argCap).T outTy →
      WithCapturesLE Cap f.T (path :: paths) out
        (WShape.forallE tyDom tyFun).T outTy

/-- Faithfulness: the exact packed telescope is the reflexive case of the
monotone one, so every producer of the old form still supplies the new. -/
theorem LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCaptures.toLE
    {p : Pattern} {m2 : p.Path → TShape}
    {Cap : ∀ {n}, p.Path → WShape n → WShape n → Prop}
    {head out headTy outTy : TShape} {paths : List p.Path}
    (H : LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCaptures
      (m2 := m2) Cap head paths out headTy outTy) :
    LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCapturesLE
      (m2 := m2) Cap head paths out headTy outTy := by
  induction H with
  | nil htyped => exact .nil htyped TShape.LE.rfl
  | cons harg happ hargCap hcapDom capture _ ih =>
    exact .cons harg happ hargCap hcapDom capture ih

/-- **THE TERMINAL-INDEX MONOTONICITY.**  A finished telescope may be read at
any result observation below the one it terminates at, provided that
observation types the spine's result.

This is the lemma `WithCaptures` cannot have: its `nil` identifies the two
indices, so the rebuild has to happen at the base, and only the monotone base
admits it.  Both extra inputs are held by the consumer's caller — `htyped` is
the caller's own `out.HasType outTy`, and `hle` is the single residual
comparison against the observation the ordered peel reached. -/
theorem LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCaptures.retarget
    {p : Pattern} {m2 : p.Path → TShape}
    {Cap : ∀ {n}, p.Path → WShape n → WShape n → Prop}
    {head out headTy reachedTy outTy : TShape} {paths : List p.Path}
    (H : LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCaptures
      (m2 := m2) Cap head paths out headTy reachedTy)
    (htyped : out.HasType outTy) (hle : outTy ≤ reachedTy) :
    LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCapturesLE
      (m2 := m2) Cap head paths out headTy outTy := by
  induction H with
  | nil _ => exact .nil htyped hle
  | cons harg happ hargCap hcapDom capture _ ih =>
    exact .cons harg happ hargCap hcapDom capture (ih htyped hle)

/-- Recover the semantic spine retained by a monotone packed telescope. -/
theorem LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCapturesLE.spine
    {p : Pattern} {m2 : p.Path → TShape}
    {Cap : ∀ {n}, p.Path → WShape n → WShape n → Prop}
    {head out headTy outTy : TShape} {paths : List p.Path}
    (H : LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCapturesLE
      (m2 := m2) Cap head paths out headTy outTy) :
    LE_Interp.RHS.ShapeSpine m2 head paths out := by
  induction H with
  | nil _ _ => exact .nil
  | cons harg happ _ _ _ _ ih => exact .cons harg happ ih

/-- The monotone telescope still lands at the caller's exact result typing:
that fact is what its base now records directly. -/
theorem LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCapturesLE.outHasType
    {p : Pattern} {m2 : p.Path → TShape}
    {Cap : ∀ {n}, p.Path → WShape n → WShape n → Prop}
    {head out headTy outTy : TShape} {paths : List p.Path}
    (H : LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCapturesLE
      (m2 := m2) Cap head paths out headTy outTy) :
    out.HasType outTy := by
  induction H with
  | nil htyped _ => exact htyped
  | cons _ _ _ _ _ _ ih => exact ih

/-- The synchronized lower head survives the weakening: the head observation
is used only as an upper bound, and the base now bounds the caller's result
observation by the reached one. -/
theorem LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCapturesLE.lowerHead
    {p : Pattern} {m2 : p.Path → TShape}
    {Cap : ∀ {n}, p.Path → WShape n → WShape n → Prop}
    {head out headTy outTy : TShape} {paths : List p.Path}
    (H : LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCapturesLE
      (m2 := m2) Cap head paths out headTy outTy) :
    LE_Interp.RHS.ShapeSpine.TypedLowerHead H.spine headTy := by
  induction H with
  | nil htyped hle => exact ⟨_, _, TShape.LE.rfl, htyped, hle⟩
  | cons harg happ hargCap hcapDom _ tail ih =>
    exact LE_Interp.RHS.ShapeSpine.TypedLowerHead.cons
      harg happ tail.spine hargCap hcapDom ih

/-- Extract the semantic application chain from an `appN` tower of capture
variables.  A proof may interpret any syntax as bottom; otherwise its head
is an interpretation of the fixed tower and every capture application is
retained in `ShapeSpine`. -/
theorem LE_Interp.RHS.appN_vars
    (H : LE_Interp.RHS ls m2 R out
      (Pattern.RHS.appN f (paths.map fun path => .var path))) :
    out ≤ TShape.bot ∨
      ∃ head, LE_Interp.RHS ls m2 R head f ∧
        LE_Interp.RHS.ShapeSpine m2 head paths out := by
  induction paths generalizing f out with
  | nil =>
    exact .inr ⟨out, H, .nil⟩
  | cons path paths ih =>
    simp only [List.map_cons, Pattern.RHS.appN] at H
    obtain hout | ⟨head, hhead, hspine⟩ := ih H
    · exact .inl hout
    · cases hhead with
      | bot => exact .inl (hspine.le_bot TShape.bot_eqv.1)
      | app hf ha happ =>
        exact .inr ⟨_, hf, .cons ha.var_le happ hspine⟩

/-- Specialize `appN_vars` to the fixed tower and ordered capture inventory
stored by a generated iota rule. -/
theorem _root_.Lean4Lean.Pattern.IotaRule.rhsShapeSpine
    {rec ctor : Name} {major arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (rule : Pattern.IotaRule r)
    {ls : List SLevel}
    {mcap : (RecursorIotaPattern rec major ctor arity).Path → TShape}
    {R : TShape → SExpr → Prop} {out : TShape}
    (H : LE_Interp.RHS ls mcap R out r.1) :
    out ≤ TShape.bot ∨
      ∃ head,
        LE_Interp.RHS ls mcap R head (.fixed rule.df.rhs rule.rhsClosed) ∧
        LE_Interp.RHS.ShapeSpine mcap head rule.capturePaths out := by
  rw [rule.rhsTower] at H
  exact H.appN_vars

variable (c : Name) (ls : List SLevel) (R : TShape → SExpr → Prop) {n : Nat} in
inductive LE_Interp.Const : List (WShape n) → TShape → Prop
  | bot : Const rargs (WShape.T (n := n') .bot)
  | lam : (∀ x y : WShape n, (x, y) ∈ f → Const (x :: rargs) y.T) →
    m ≤ WShape.T (n := n + 1) (.lam' f) → Const rargs m
  | ctor : Params.classify c = some (.ctor rargs.length) →
    m ≤ WShape.T (n := n + 1) (.ctor' c rargs.reverse) → Const rargs m
  | indTy : Params.classify c = some (.indTy rargs.length) →
    m ≤ (WShape.indTy : WShape (n+1)).T → Const rargs m
  | pat : Params.Pat p r → Matches p c rargs m' → RHS ls m' R m r.1 → Const rargs m

inductive LE_Interp : Valuation → TShape → SExpr → Prop
  | bot : LE_Interp ρ (WShape.T (n := n) .bot) M
  | bvar : m ≤ ρ i → LE_Interp ρ m (.bvar i)
  | sort : m ≤ .sort (l ≠ .zero) → LE_Interp ρ m (.sort l)
  | app : LE_Interp ρ (WShape.T f) F → LE_Interp ρ a.T A →
    m ≤ (f.app a).T → LE_Interp ρ m (.app F A)
  | lam : LE_Interp ρ (WShape.T (n := n) a) A →
    WShape.HasDom f a → (∀ x, x.HasType a → LE_Interp (ρ.push x.T) (f.app x).T F) →
    m ≤ WShape.T (n := _+1) (.lam' f) → LE_Interp ρ m (.lam A F)
  | forallE : LE_Interp ρ (WShape.T (n := n) b) B → LE_Interp ρ (WShape.T (n := n) b') B →
    WShape.HasDom f b' → (∀ x, x.HasType b' → LE_Interp (ρ.push x.T) (f.app x).T F) →
    m ≤ WShape.T (n := n+1) (.forallE b f) → LE_Interp ρ m (.forallE B F)
  | const :
    Params.env.constants c = some ci → ls.length = ci.uvars →
    m ≤ m' → m'.HasType a →
    LE_Interp ρ a (SExpr.mkInst ls ci.type) →
    LE_Interp.Const c ls R [] m' → (∀ m e, R m e → LE_Interp ρ m e) →
    LE_Interp ρ m (.const c ls)

/-! #### Proof-relevant interpretation witnesses

`LE_Interp` remains a proposition: all public semantic statements should be
proof-irrelevant.  Its derivation tree, however, cannot itself be used as a
recursion certificate.  Proof irrelevance identifies two derivations at the
same indices, including derivations that chose different abstract relations
in the constant case.  A predicate indexed by an `LE_Interp` proof therefore
cannot remember which `R` witness an evaluator actually exposed.

`LE_Interp.Witness` is the proof-relevant mirror used only at that internal
recursion boundary.  Every propositional interpretation has a witness, and a
witness forgets back to the original proposition.  Choosing a witness is
noncomputable but adds no semantic assumption; it merely retains one
consistent constructor tree through recursive constant evaluation. -/

inductive LE_Interp.Witness : Valuation → TShape → SExpr → Type where
  | bot : Witness ρ (WShape.T (n := n) .bot) M
  | bvar : m ≤ ρ i → Witness ρ m (.bvar i)
  | sort : m ≤ .sort (l ≠ .zero) → Witness ρ m (.sort l)
  | app : Witness ρ (WShape.T f) F → Witness ρ a.T A →
    m ≤ (f.app a).T → Witness ρ m (.app F A)
  | lam : Witness ρ (WShape.T (n := n) a) A →
    WShape.HasDom f a →
    (∀ x, x.HasType a → Witness (ρ.push x.T) (f.app x).T F) →
    m ≤ WShape.T (n := _ + 1) (.lam' f) → Witness ρ m (.lam A F)
  | forallE : Witness ρ (WShape.T (n := n) b) B →
    Witness ρ (WShape.T (n := n) b') B →
    WShape.HasDom f b' →
    (∀ x, x.HasType b' → Witness (ρ.push x.T) (f.app x).T F) →
    m ≤ WShape.T (n := n + 1) (.forallE b f) → Witness ρ m (.forallE B F)
  | const :
    Params.env.constants c = some ci → ls.length = ci.uvars →
    m ≤ m' → m'.HasType a →
    Witness ρ a (SExpr.mkInst ls ci.type) →
    LE_Interp.Const c ls R [] m' →
    (∀ m e, R m e → Witness ρ m e) →
    Witness ρ m (.const c ls)

/-- Forget the proof-relevant recursion witness. -/
theorem LE_Interp.Witness.toInterp :
    LE_Interp.Witness ρ m M → LE_Interp ρ m M
  | .bot => .bot
  | .bvar h => .bvar h
  | .sort h => .sort h
  | .app hf ha h => .app hf.toInterp ha.toInterp h
  | .lam ha hdom hbody h =>
      .lam ha.toInterp hdom (fun x hx => (hbody x hx).toInterp) h
  | .forallE hb hb' hdom hbody h =>
      .forallE hb.toInterp hb'.toInterp hdom
        (fun x hx => (hbody x hx).toInterp) h
  | .const hreg hlen hle hty hA hC hR =>
      .const hreg hlen hle hty hA.toInterp hC
        (fun m e hr => (hR m e hr).toInterp)

/-- Every propositional interpretation contains at least one consistent
proof-relevant constructor tree. -/
theorem LE_Interp.witnessNonempty (H : LE_Interp ρ m M) :
    Nonempty (LE_Interp.Witness ρ m M) := by
  induction H with
  | bot => exact ⟨LE_Interp.Witness.bot⟩
  | bvar h => exact ⟨LE_Interp.Witness.bvar h⟩
  | sort h => exact ⟨LE_Interp.Witness.sort h⟩
  | app hf ha h ihf iha =>
    exact ⟨LE_Interp.Witness.app (Classical.choice ihf) (Classical.choice iha) h⟩
  | lam ha hdom hbody h iha ihbody =>
    exact ⟨LE_Interp.Witness.lam (Classical.choice iha) hdom
      (fun x hx => Classical.choice (ihbody x hx)) h⟩
  | forallE hb hb' hdom hbody h ihb ihb' ihbody =>
    exact ⟨LE_Interp.Witness.forallE (Classical.choice ihb)
      (Classical.choice ihb') hdom
      (fun x hx => Classical.choice (ihbody x hx)) h⟩
  | const hreg hlen hle hty hA hC hR ihA ihR =>
    exact ⟨LE_Interp.Witness.const hreg hlen hle hty
      (Classical.choice ihA) hC
      (fun m e hr => Classical.choice (ihR m e hr))⟩

/-- Choose the internal constructor tree used by a recursive semantic
consumer.  Consumers must remain proof-independent after forgetting it. -/
noncomputable def LE_Interp.witness (H : LE_Interp ρ m M) :
    LE_Interp.Witness ρ m M :=
  Classical.choice H.witnessNonempty

theorem LE_Interp.witness_toInterp (H : LE_Interp ρ m M) :
    H.witness.toInterp = H :=
  Subsingleton.elim _ _

/-- Lower the root observation without changing the chosen constructor tree
or any abstract relation witness stored below it. -/
def LE_Interp.Witness.mono (h : m ≤ m') :
    LE_Interp.Witness ρ m' M → LE_Interp.Witness ρ m M
  | .bot =>
      TShape.le_bot'.1 (h.trans TShape.bot_eqv.1) ▸ .bot
  | .bvar h₁ => .bvar (h.trans h₁)
  | .sort h₁ => .sort (h.trans h₁)
  | .app hf ha h₁ => .app hf ha (h.trans h₁)
  | .lam ha hdom hbody h₁ => .lam ha hdom hbody (h.trans h₁)
  | .forallE hb hb' hdom hbody h₁ =>
      .forallE hb hb' hdom hbody (h.trans h₁)
  | .const hreg hlen hle hty hA hC hR =>
      .const hreg hlen (h.trans hle) hty hA hC hR

/-- Turn a synchronized ordered-telescope type bound into the exact
proof-relevant type witness required by the fixed-head consumer. -/
theorem LE_Interp.RHS.ShapeSpine.TypedLowerHead.withWitness
    {p : Pattern} {m2 : p.Path → TShape}
    {head out headTy : TShape} {paths : List p.Path}
    {spine : LE_Interp.RHS.ShapeSpine m2 head paths out}
    (H : spine.TypedLowerHead headTy)
    (hTy : LE_Interp.Witness ρ headTy A) :
    ∃ elem elemTy : TShape,
      elem ≤ head ∧ elem.HasType elemTy ∧
        Nonempty (LE_Interp.Witness ρ elemTy A) := by
  obtain ⟨elem, elemTy, helem, htyped, hty⟩ := H
  exact ⟨elem, elemTy, helem, htyped, ⟨hTy.mono hty⟩⟩

/-- Enlarge a valuation while retaining the same proof-relevant semantic
tree. -/
def LE_Interp.Witness.mono_l (hρ : ρ.LE ρ') :
    LE_Interp.Witness ρ m M → LE_Interp.Witness ρ' m M
  | .bot => .bot
  | .bvar hle => .bvar (hle.trans (hρ _))
  | .sort hle => .sort hle
  | .app hf ha hle => .app (hf.mono_l hρ) (ha.mono_l hρ) hle
  | .lam ha hdom hbody hle =>
      .lam (ha.mono_l hρ) hdom
        (fun x hx => (hbody x hx).mono_l
          (Valuation.LE.push.2 ⟨hρ, .rfl⟩)) hle
  | .forallE hb hb' hdom hbody hle =>
      .forallE (hb.mono_l hρ) (hb'.mono_l hρ) hdom
        (fun x hx => (hbody x hx).mono_l
          (Valuation.LE.push.2 ⟨hρ, .rfl⟩)) hle
  | .const hreg hlen hle hty hA hC hR =>
      .const hreg hlen hle hty (hA.mono_l hρ) hC
        (fun m e hr => (hR m e hr).mono_l hρ)

/-- Well-founded recursion through the abstract `R` leaves of one chosen
interpretation tree.  Unlike `LE_Interp.recR`, the recursive hypothesis is
attached to the proof-relevant witness that supplied the leaf. -/
theorem LE_Interp.Witness.recR
    {P : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop}
    (step : ∀ {ρ m M} (H : LE_Interp.Witness ρ m M),
      (match H with
       | .const _ _ _ _ _ _ hR => ∀ m e hr, P (hR m e hr)
       | _ => True) → P H)
    {rho m M} (H : LE_Interp.Witness rho m M) : P H := by
  induction H with
  | bot => exact step _ trivial
  | bvar => exact step _ trivial
  | sort => exact step _ trivial
  | app => exact step _ trivial
  | lam => exact step _ trivial
  | forallE => exact step _ trivial
  | const hreg hlen hle hty hA hC hR ihA ihR =>
    exact step _ ihR

/-- Regard a predicate on public semantic indices as a predicate on a
proof-relevant witness. -/
abbrev LE_Interp.Witness.AtIndices
    (P : Valuation → TShape → SExpr → Prop)
    {ρ m M} (_ : LE_Interp.Witness ρ m M) : Prop :=
  P ρ m M

/-- Proof-independent specialization of `Witness.recR`.  This is the form
an adequacy consumer should expose: the chosen witness controls recursive
calls, but the theorem proved at each node depends only on its public
semantic indices. -/
theorem LE_Interp.Witness.recRIndex
    {P : Valuation → TShape → SExpr → Prop}
    (step : ∀ {ρ m M} (H : LE_Interp.Witness ρ m M),
      (match H with
       | .const _ _ _ _ _ _ hR => ∀ m e hr, AtIndices P (hR m e hr)
       | _ => True) → AtIndices P H)
    {rho m M} (H : LE_Interp.Witness rho m M) : P rho m M :=
  H.recR (P := AtIndices P) step

/-- Recursive results attached to every immediate child of one exact
proof-relevant interpretation tree. -/
def LE_Interp.Witness.DeepChildren
    (P : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop)
    {ρ m M} (H : LE_Interp.Witness ρ m M) : Prop :=
  match H with
  | .app hf ha _ => P hf ∧ P ha
  | .lam ha _ hbody _ => P ha ∧ ∀ x hx, P (hbody x hx)
  | .forallE hb hb' _ hbody _ =>
      P hb ∧ P hb' ∧ ∀ x hx, P (hbody x hx)
  | .const _ _ _ _ hA _ hR =>
      P hA ∧ ∀ m e hr, P (hR m e hr)
  | _ => True

/-- Structural recursion through one complete proof-relevant interpretation
tree.  Unlike `recR`, the step receives recursive results for ordinary
syntax/type children as well as the exact constant relation children.  This
is the semantic half of the stratified self-validity induction. -/
theorem LE_Interp.Witness.recDeep
    {P : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop}
    (step : ∀ {ρ m M} (H : LE_Interp.Witness ρ m M),
      H.DeepChildren P → P H)
    {rho m M} (H : LE_Interp.Witness rho m M) : P H := by
  induction H with
  | bot => exact step _ trivial
  | bvar => exact step _ trivial
  | sort => exact step _ trivial
  | app hf ha hle ihf iha => exact step _ ⟨ihf, iha⟩
  | lam ha hdom hbody hle iha ihbody =>
    exact step _ ⟨iha, ihbody⟩
  | forallE hb hb' hdom hbody hle ihb ihb' ihbody =>
    exact step _ ⟨ihb, ihb', ihbody⟩
  | const hreg hlen hle hty hA hC hR ihA ihR =>
    exact step _ ⟨ihA, ihR⟩

/-- Nested structural recursion over two exact interpretation trees.  The
first tree's child hypotheses are polymorphic in the second tree, so an
inner syntactic proof may swap the displayed term/type roles without losing
either tree's recursive constant callbacks. -/
theorem LE_Interp.Witness.recDeep₂
    {P : ∀ {ρm m M ρa a A},
      LE_Interp.Witness ρm m M → LE_Interp.Witness ρa a A → Prop}
    (step : ∀ {ρm m M ρa a A}
        (hM : LE_Interp.Witness ρm m M)
        (hA : LE_Interp.Witness ρa a A),
      hM.DeepChildren
        (fun hM' => ∀ {ρa a A} (hA' : LE_Interp.Witness ρa a A),
          P hM' hA') →
      hA.DeepChildren (fun hA' => P hM hA') →
      P hM hA)
    {rhom m M rhoa a A}
    (hM : LE_Interp.Witness rhom m M)
    (hA : LE_Interp.Witness rhoa a A) : P hM hA := by
  refine hM.recDeep
    (P := fun hM => ∀ {rhoa a A}
      (hA : LE_Interp.Witness rhoa a A), P hM hA) ?_ hA
  intro rhom m M hM childrenM rhoa a A hA
  exact hA.recDeep
    (P := fun hA => P hM hA)
    (fun hA childrenA => step hM hA childrenM childrenA)

/-- The complete proof-relevant witness tree for a consumer that recurses
only at abstract constant `R` edges.  Ordinary syntax children retain their
exact constructor trees, so a nested stratified induction may descend into
them without treating that descent as a semantic recursive call.

This is the proof-relevant counterpart of `LE_Interp.RDeepChildren`.
Unlike the propositional version, every retained child preserves the exact
constant relation and callback selected by the evaluator. -/
inductive LE_Interp.Witness.RDeepChildren
    (P : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop) :
    ∀ {ρ m M} (H : LE_Interp.Witness ρ m M), Prop where
  | bot : RDeepChildren P (.bot (ρ := ρ) (M := M) (n := n))
  | bvar : RDeepChildren P (.bvar h)
  | sort : RDeepChildren P (.sort h)
  | app : RDeepChildren P hf → RDeepChildren P ha →
      RDeepChildren P (.app hf ha h)
  | lam : RDeepChildren P ha →
      (∀ x hx, RDeepChildren P (hbody x hx)) →
      RDeepChildren P (.lam ha hdom hbody h)
  | forallE : RDeepChildren P hb → RDeepChildren P hb' →
      (∀ x hx, RDeepChildren P (hbody x hx)) →
      RDeepChildren P (.forallE hb hb' hdom hbody h)
  | const : RDeepChildren P hA →
      (∀ m e hr, P (hR m e hr)) →
      (∀ m e hr, RDeepChildren P (hR m e hr)) →
      RDeepChildren P (.const hreg hlen hle hty hA hC hR)

/-- Algebraic closure needed to merge two exact retained trees.  The join
law deliberately quantifies over the selected joined witness: compatible
constant evaluators construct that witness from their proof-relevant
callbacks, rather than reselecting a propositional interpretation. -/
structure LE_Interp.Witness.RDeepChildren.JoinLaws
    (P : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop) : Prop where
  bot : ∀ {ρ n M},
    P (LE_Interp.Witness.bot (ρ := ρ) (n := n) (M := M))
  mono : ∀ {ρ m m' M} (H : LE_Interp.Witness ρ m' M)
    (hle : m ≤ m'), P H → P (H.mono hle)
  mono_l : ∀ {ρ ρ' m M} (H : LE_Interp.Witness ρ m M)
    (hρ : ρ.LE ρ'), P H → P (H.mono_l hρ)
  join : ∀ {ρ m₁ m₂ M}
    (H₁ : LE_Interp.Witness ρ m₁ M)
    (H₂ : LE_Interp.Witness ρ m₂ M)
    (HJ : LE_Interp.Witness ρ (m₁.join m₂) M),
    P H₁ → P H₂ → P HJ

/-- Change the recursive-result predicate throughout a retained tree without
changing any exact witness or evaluator callback. -/
theorem LE_Interp.Witness.RDeepChildren.map
    {P Q : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop}
    (hPQ : ∀ {ρ m M} (H : LE_Interp.Witness ρ m M), P H → Q H)
    {H : LE_Interp.Witness ρ m M}
    (children : H.RDeepChildren P) : H.RDeepChildren Q := by
  induction children with
  | bot => exact .bot
  | bvar => exact .bvar
  | sort => exact .sort
  | app _ _ ihf iha => exact .app ihf iha
  | lam _ _ iha ihbody => exact .lam iha ihbody
  | forallE _ _ _ ihb ihb' ihbody => exact .forallE ihb ihb' ihbody
  | const _ pR _ ihA ihR =>
    exact .const ihA (fun m e hr => hPQ _ (pR m e hr)) ihR

/-- Lowering only the root observation of an exact witness preserves its
complete retained recursion tree.  In particular, the abstract relation and
every proof-relevant `R` callback in a constant witness are definitionally
the same after lowering; no transport law for the recursive predicate is
needed. -/
theorem LE_Interp.Witness.RDeepChildren.mono
    {P : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop}
    {H : LE_Interp.Witness ρ m' M}
    (children : H.RDeepChildren P) (hle : m ≤ m') :
    (H.mono hle).RDeepChildren P := by
  cases H with
  | @bot ρ n M =>
    cases children
    rcases m with ⟨k, s⟩
    have hs : s = .bot :=
      TShape.le_bot.1 (hle.trans TShape.bot_eqv.1)
    subst s
    simp only [LE_Interp.Witness.mono]
    exact .bot
  | bvar h =>
    cases children
    exact .bvar
  | sort h =>
    cases children
    exact .sort
  | app hf ha h =>
    cases children with
    | app cf ca => exact .app cf ca
  | lam ha hdom hbody h =>
    cases children with
    | lam ca cbody => exact .lam ca cbody
  | forallE hb hb' hdom hbody h =>
    cases children with
    | forallE cb cb' cbody => exact .forallE cb cb' cbody
  | const hreg hlen hle' hty hA hC hR =>
    cases children with
    | const cA pR cR => exact .const cA pR cR

/-- Enlarge the valuation throughout a retained exact recursion tree.

Unlike root lowering, valuation enlargement also transforms every recursive
`R` child.  The caller therefore supplies the corresponding transport law
for the recursive result predicate.  Quantifying that law over arbitrary
valuations is essential below binders, where the recursive call uses the
pointwise enlarged pushed valuation. -/
theorem LE_Interp.Witness.RDeepChildren.mono_l
    {P : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop}
    (hP : ∀ {ρ ρ' m M} (H : LE_Interp.Witness ρ m M)
      (hρ : ρ.LE ρ'), P H → P (H.mono_l hρ))
    {H : LE_Interp.Witness ρ m M}
    (children : H.RDeepChildren P) (hρ : ρ.LE ρ') :
    (H.mono_l hρ).RDeepChildren P := by
  induction H generalizing ρ' with
  | @bot ρ n M =>
    cases children
    cases M <;> exact .bot
  | bvar hle =>
    cases children
    exact .bvar
  | sort hle =>
    cases children
    exact .sort
  | app hf ha hle ihf iha =>
    cases children with
    | app cf ca => exact .app (ihf cf hρ) (iha ca hρ)
  | lam ha hdom hbody hle iha ihbody =>
    cases children with
    | lam ca cbody =>
      exact .lam (iha ca hρ) (fun x hx =>
        ihbody x hx (cbody x hx)
          (Valuation.LE.push.2 ⟨hρ, .rfl⟩))
  | forallE hb hb' hdom hbody hle ihb ihb' ihbody =>
    cases children with
    | forallE cb cb' cbody =>
      exact .forallE (ihb cb hρ) (ihb' cb' hρ) (fun x hx =>
        ihbody x hx (cbody x hx)
          (Valuation.LE.push.2 ⟨hρ, .rfl⟩))
  | const hreg hlen hle hty hA hC hR ihA ihR =>
    cases children with
    | const cA pR cR =>
      exact .const (ihA cA hρ)
        (fun m e hr => hP (hR m e hr) hρ (pR m e hr))
        (fun m e hr => ihR m e hr (cR m e hr) hρ)

/-- Well-founded recursion through one exact witness tree, granting the
recursive predicate only at abstract constant `R` edges.  The result is
paired with the complete retained tree so an enclosing syntax-indexed
induction can continue through ordinary children before taking another
semantic edge. -/
theorem LE_Interp.Witness.recRDeep
    {P : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop}
    (step : ∀ {ρ m M} (H : LE_Interp.Witness ρ m M),
      H.RDeepChildren P → P H)
    {ρ m M} (H : LE_Interp.Witness ρ m M) : P H := by
  suffices P H ∧ H.RDeepChildren P from this.1
  induction H with
  | bot => exact ⟨step _ .bot, .bot⟩
  | bvar h => exact ⟨step _ (.bvar (h := h)), .bvar (h := h)⟩
  | sort h => exact ⟨step _ (.sort (h := h)), .sort (h := h)⟩
  | app hf ha h ihf iha =>
    exact ⟨step _ (.app (h := h) ihf.2 iha.2),
      .app (h := h) ihf.2 iha.2⟩
  | lam ha hdom hbody h iha ihbody =>
    exact ⟨step _ (.lam (hdom := hdom) (hbody := hbody) (h := h)
        iha.2 (fun x hx => (ihbody x hx).2)),
      .lam (hdom := hdom) (hbody := hbody) (h := h)
        iha.2 (fun x hx => (ihbody x hx).2)⟩
  | forallE hb hb' hdom hbody h ihb ihb' ihbody =>
    exact ⟨step _ (.forallE (hdom := hdom) (hbody := hbody) (h := h)
        ihb.2 ihb'.2 (fun x hx => (ihbody x hx).2)),
      .forallE (hdom := hdom) (hbody := hbody) (h := h)
        ihb.2 ihb'.2 (fun x hx => (ihbody x hx).2)⟩
  | const hreg hlen hle hty hA hC hR ihA ihR =>
    exact ⟨step _ (.const (hreg := hreg) (hlen := hlen) (hle := hle)
        (hty := hty) (hC := hC) ihA.2 (fun m e hr => (ihR m e hr).1)
        (fun m e hr => (ihR m e hr).2)),
      .const (hreg := hreg) (hlen := hlen) (hle := hle)
        (hty := hty) (hC := hC) ihA.2 (fun m e hr => (ihR m e hr).1)
        (fun m e hr => (ihR m e hr).2)⟩

/-- Rebuild a complete retained tree from a local result constructor.

The constructor is invoked only after the corresponding witness's genuine
`R` children have themselves been rebuilt.  This is the proof-relevant
operation needed at a strict Nat decrease: a converted endpoint may select a
fresh exact witness, but no recursive result is attached until structural
semantic descent has exposed its actual evaluator children. -/
theorem LE_Interp.Witness.RDeepChildren.of_step
    {P : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop}
    (step : ∀ {ρ m M} (H : LE_Interp.Witness ρ m M),
      H.RDeepChildren P → P H)
    {rho m M} (H : LE_Interp.Witness rho m M) :
    H.RDeepChildren P := by
  induction H with
  | bot => exact .bot
  | bvar => exact .bvar
  | sort => exact .sort
  | app _ _ _ ihf iha => exact .app ihf iha
  | lam _ _ _ _ iha ihbody => exact .lam iha ihbody
  | forallE _ _ _ _ _ ihb ihb' ihbody =>
    exact .forallE ihb ihb' ihbody
  | const _ _ _ _ _ _ hR ihA ihR =>
    exact .const ihA (fun m e hr => step (hR m e hr) (ihR m e hr)) ihR

/-- Lexicographic recursion over one exact semantic tree and a syntactic
depth.

Abstract constant `R` edges receive the recursive result at every depth.
Ordinary semantic children retain only their exact trees, but a restart at
one of those children may be made after strictly lowering `d`.  Unlike the
binary eliminator below, this form deliberately leaves any displayed type
witness outside the semantic recursion.  It is the right interface when a
proof-relevant soundness package constructs the retained result-type tree
from the subject tree instead of recursively selecting an unrelated type
witness. -/
theorem LE_Interp.Witness.recRDeepNat
    {Q : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Nat → Prop}
    (step : ∀ (d : Nat)
        {ρ m M} (hM : LE_Interp.Witness ρ m M),
      hM.RDeepChildren (fun hM' => ∀ d, Q hM' d) →
      (∀ (d' : Nat), d' < d →
        ∀ {ρ m M} (hM' : LE_Interp.Witness ρ m M),
          hM'.RDeepChildren (fun hM'' => ∀ d, Q hM'' d) →
          Q hM' d') →
      Q hM d)
    {rho m M} (hM : LE_Interp.Witness rho m M) : ∀ d, Q hM d := by
  let P : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop :=
    fun hM => ∀ d, Q hM d
  apply hM.recRDeep (P := P)
  intro ρ m M hM children
  let motive := fun d =>
    ∀ {ρ m M} (hM : LE_Interp.Witness ρ m M),
      hM.RDeepChildren (fun hM' => ∀ d, Q hM' d) → Q hM d
  have go : ∀ d, motive d := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
      intro ρ m M hM children
      exact step d hM children
        (fun d' hd' {_ _ _} hM' children' =>
          ih d' hd' hM' children')
  exact fun d => go d hM children

/-- Lexicographic recursion with syntactic depth as the primary component
and exact semantic-tree descent as the secondary component.

At a fixed depth, abstract constant `R` edges receive the recursive result
by structural descent through the selected witness.  After strictly lowering
the depth, the continuation may restart from any exact witness; its retained
tree is rebuilt by the semantic recursor rather than required from the
caller.  This ordering is the conversion-compatible form of the recursion. -/
theorem LE_Interp.Witness.recNatRDeep
    {Q : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Nat → Prop}
    (step : ∀ (d : Nat)
        {ρ m M} (hM : LE_Interp.Witness ρ m M),
      hM.RDeepChildren (fun hM' => Q hM' d) →
      (∀ (d' : Nat), d' < d →
        ∀ {ρ m M} (hM' : LE_Interp.Witness ρ m M), Q hM' d') →
      Q hM d)
    {rho m M} (hM : LE_Interp.Witness rho m M) : ∀ d, Q hM d := by
  have go : ∀ d, ∀ {ρ m M}
      (hM : LE_Interp.Witness ρ m M), Q hM d := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
      intro ρ m M hM
      exact hM.recRDeep
        (P := fun hM => Q hM d)
        (fun hM children => step d hM children
          (fun d' hd' {_ _ _} hM' => ih d' hd' hM'))
  exact fun d => go d hM

/-- Nested proof-relevant `R`-edge recursion.  The first exact tree remains
available while traversing the second, and ordinary children on either side
retain their evaluator provenance for the inner stratified induction. -/
theorem LE_Interp.Witness.recRDeep₂
    {P : ∀ {ρm m M ρa a A},
      LE_Interp.Witness ρm m M → LE_Interp.Witness ρa a A → Prop}
    (step : ∀ {ρm m M ρa a A}
        (hM : LE_Interp.Witness ρm m M)
        (hA : LE_Interp.Witness ρa a A),
      hM.RDeepChildren
          (fun hM' => ∀ {ρa a A} (hA' : LE_Interp.Witness ρa a A),
            P hM' hA') →
      hA.RDeepChildren (fun hA' => P hM hA') →
      P hM hA)
    {ρm m M ρa a A}
    (hM : LE_Interp.Witness ρm m M)
    (hA : LE_Interp.Witness ρa a A) : P hM hA := by
  refine hM.recRDeep
    (P := fun hM => ∀ {ρa a A}
      (hA : LE_Interp.Witness ρa a A), P hM hA) ?_ hA
  intro ρm m M hM childrenM ρa a A hA
  exact hA.recRDeep
    (P := fun hA => P hM hA)
    (fun hA childrenA => step hM hA childrenM childrenA)

/-- Lexicographic recursion over two exact semantic trees and a syntactic
depth.

Abstract constant `R` edges receive the recursive result at every depth and
may therefore restart a typing derivation.  Every other recursive restart may
select new exact witnesses (which is needed by conversion and dependent
application), but must strictly lower `d`.  This is the eliminator used by
fixed-head self-validity: it makes the two independent decreases explicit
without assigning a numeric size to proof-relevant evaluator callbacks. -/
theorem LE_Interp.Witness.recRDeep₂Nat
    {Q : ∀ {ρm m M ρa a A},
      LE_Interp.Witness ρm m M → LE_Interp.Witness ρa a A → Nat → Prop}
    (step : ∀ (d : Nat)
        {ρm m M ρa a A}
        (hM : LE_Interp.Witness ρm m M)
        (hA : LE_Interp.Witness ρa a A),
      hM.RDeepChildren
          (fun hM' => ∀ {ρa a A} (hA' : LE_Interp.Witness ρa a A),
            ∀ d, Q hM' hA' d) →
      hA.RDeepChildren (fun hA' => ∀ d, Q hM hA' d) →
      (∀ (d' : Nat), d' < d →
        ∀ {ρm m M ρa a A}
          (hM' : LE_Interp.Witness ρm m M)
          (hA' : LE_Interp.Witness ρa a A),
        hM'.RDeepChildren
            (fun hM'' => ∀ {ρa a A}
              (hA'' : LE_Interp.Witness ρa a A), ∀ d, Q hM'' hA'' d) →
        hA'.RDeepChildren (fun hA'' => ∀ d, Q hM' hA'' d) →
        Q hM' hA' d') →
      Q hM hA d)
    {rhom m M rhoa a A}
    (hM : LE_Interp.Witness rhom m M)
    (hA : LE_Interp.Witness rhoa a A) : ∀ d, Q hM hA d := by
  let P : ∀ {ρm m M ρa a A},
      LE_Interp.Witness ρm m M → LE_Interp.Witness ρa a A → Prop :=
    fun hM hA => ∀ d, Q hM hA d
  apply hM.recRDeep₂ (P := P) (hA := hA)
  intro ρm m M ρa a A hM hA childrenM childrenA
  let motive := fun d =>
    ∀ {ρm m M ρa a A}
      (hM : LE_Interp.Witness ρm m M)
      (hA : LE_Interp.Witness ρa a A),
      hM.RDeepChildren
          (fun hM' => ∀ {ρa a A} (hA' : LE_Interp.Witness ρa a A),
            ∀ d, Q hM' hA' d) →
      hA.RDeepChildren (fun hA' => ∀ d, Q hM hA' d) →
      Q hM hA d
  have go : ∀ d, motive d := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
      intro ρm m M ρa a A hM hA childrenM childrenA
      exact step d hM hA childrenM childrenA
        (fun d' hd' {_ _ _ _ _ _} hM' hA' childrenM' childrenA' =>
          ih d' hd' hM' hA' childrenM' childrenA')
  exact fun d => go d hM hA childrenM childrenA

/-- Nat-first nested recursion over two exact semantic trees.

Both trees are traversed structurally at the current syntactic depth.  A
strict depth decrease then permits an arbitrary new pair of witnesses, which
is needed when application swaps the term/type roles and conversion replaces
the displayed type witness. -/
theorem LE_Interp.Witness.recNatRDeep₂
    {Q : ∀ {ρm m M ρa a A},
      LE_Interp.Witness ρm m M → LE_Interp.Witness ρa a A → Nat → Prop}
    (step : ∀ (d : Nat)
        {ρm m M ρa a A}
        (hM : LE_Interp.Witness ρm m M)
        (hA : LE_Interp.Witness ρa a A),
      hM.RDeepChildren
          (fun hM' => ∀ {ρa a A} (hA' : LE_Interp.Witness ρa a A),
            Q hM' hA' d) →
      hA.RDeepChildren (fun hA' => Q hM hA' d) →
      (∀ (d' : Nat), d' < d →
        ∀ {ρm m M ρa a A}
          (hM' : LE_Interp.Witness ρm m M)
          (hA' : LE_Interp.Witness ρa a A),
        Q hM' hA' d') →
      Q hM hA d)
    {rhom m M rhoa a A}
    (hM : LE_Interp.Witness rhom m M)
    (hA : LE_Interp.Witness rhoa a A) : ∀ d, Q hM hA d := by
  have go : ∀ d, ∀ {ρm m M ρa a A}
      (hM : LE_Interp.Witness ρm m M)
      (hA : LE_Interp.Witness ρa a A), Q hM hA d := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
      intro ρm m M ρa a A hM hA
      exact hM.recRDeep₂ (hA := hA)
        (P := fun hM hA => Q hM hA d)
        (fun hM hA childrenM childrenA =>
          step d hM hA childrenM childrenA
            (fun d' hd' {_ _ _ _ _ _} hM' hA' =>
              ih d' hd' hM' hA'))
  exact fun d => go d hM hA

/-- The recursive interpretations exposed by a propositional constant
derivation.  Ordinary syntax children are deliberately absent.

Because `LE_Interp` is a proposition, this interface is suitable only when
`P` is insensitive to the particular derivation chosen at fixed indices.
Use `LE_Interp.Witness` when a consumer must retain the exact abstract
relation and recursive callback supplied by one constructor tree. -/
inductive LE_Interp.RChildren
    (P : ∀ {ρ m M}, LE_Interp ρ m M → Prop) :
    ∀ {ρ m M}, LE_Interp ρ m M → Prop where
  | bot : RChildren P (.bot (ρ := ρ) (M := M) (n := n))
  | bvar : RChildren P (.bvar (ρ := ρ) (i := i) h)
  | sort : RChildren P (.sort (ρ := ρ) (l := l) h)
  | app : RChildren P (.app hf ha h)
  | lam : RChildren P (.lam ha hdom hbody h)
  | forallE : RChildren P (.forallE hb hb' hdom hbody h)
  | const : (∀ m e hr, P (hR m e hr)) →
      RChildren P (.const hreg hlen hle hty hA hC hR)

/-- The complete propositional proof tree for a consumer that also follows
ordinary syntax children.  At a constant, every abstract `R` edge carries a
fresh copy of the consumer predicate as well as the tree below that edge.
Ordinary children carry only the tree: a second, syntax-indexed induction is
responsible for making progress there.

This is deliberately stronger than `RChildren`.  The shallow predicate is
the right interface for consumers whose current proof remains fixed;
`RDeepChildren` supports lexicographic arguments that decrease either a
syntax index along ordinary children or the semantic `R` tree at a constant.

This remains proof-irrelevant provenance: it cannot distinguish constructor
trees at equal public indices.  Derivation-sensitive evaluator recursion must
instead choose an `LE_Interp.Witness` and use `Witness.recR`.
-/
inductive LE_Interp.RDeepChildren
    (P : ∀ {ρ m M}, LE_Interp ρ m M → Prop) :
    ∀ {ρ m M}, LE_Interp ρ m M → Prop where
  | bot : RDeepChildren P (.bot (ρ := ρ) (M := M) (n := n))
  | bvar : RDeepChildren P (.bvar (ρ := ρ) (i := i) h)
  | sort : RDeepChildren P (.sort (ρ := ρ) (l := l) h)
  | app : RDeepChildren P hf → RDeepChildren P ha →
      RDeepChildren P (.app hf ha h)
  | lam : RDeepChildren P ha →
      (∀ x hx, RDeepChildren P (hbody x hx)) →
      RDeepChildren P (.lam ha hdom hbody h)
  | forallE : RDeepChildren P hb → RDeepChildren P hb' →
      (∀ x hx, RDeepChildren P (hbody x hx)) →
      RDeepChildren P (.forallE hb hb' hdom hbody h)
  | const : RDeepChildren P hA →
      (∀ m e hr, P (hR m e hr)) →
      (∀ m e hr, RDeepChildren P (hR m e hr)) →
      RDeepChildren P (.const hreg hlen hle hty hA hC hR)

/-- Well-founded recursion along the semantic `R` edges visible in a
propositional constant derivation.  The ordinary `LE_Interp` recursor proves
accessibility because its constant minor already receives induction
hypotheses for every `hR` child.

The result must be invariant under proof choice.  No pattern or reduction
evidence is manufactured here; a derivation-sensitive consumer should use
`Witness.recR` and must still supply the proof-carrying contraction required
by L4L-18B. -/
theorem LE_Interp.recR
    {P : ∀ {ρ m M}, LE_Interp ρ m M → Prop}
    (step : ∀ {ρ m M} (H : LE_Interp ρ m M), H.RChildren P → P H)
    {rho m M} (H : LE_Interp rho m M) : P H := by
  induction H with
  | bot => exact step _ .bot
  | bvar h => exact step _ (.bvar (h := h))
  | sort h => exact step _ (.sort (h := h))
  | app hf ha h _ _ => exact step _ (.app (hf := hf) (ha := ha) (h := h))
  | lam ha hdom hbody h _ _ =>
    exact step _ (.lam (ha := ha) (hdom := hdom) (hbody := hbody) (h := h))
  | forallE hb hb' hdom hbody h _ _ _ =>
    exact step _ (.forallE (hb := hb) (hb' := hb') (hdom := hdom)
      (hbody := hbody) (h := h))
  | const hreg hlen hle hty hA hC hR _ ihR =>
    exact step _ (.const (hreg := hreg) (hlen := hlen) (hle := hle)
      (hty := hty) (hA := hA) (hC := hC) (hR := hR) ihR)

/-- Well-founded recursion through the complete propositional proof tree,
while granting recursive calls only at abstract constant `R` edges.  Each
`R` child simultaneously supplies both `P` and its tree.  This can be the
semantic half of a lexicographic proof whose other half decreases an
independent syntax/typing index along ordinary children, provided the result
is insensitive to the proof chosen at fixed indices. -/
theorem LE_Interp.recRDeep
    {P : ∀ {ρ m M}, LE_Interp ρ m M → Prop}
    (step : ∀ {ρ m M} (H : LE_Interp ρ m M),
      LE_Interp.RDeepChildren P H → P H)
    {rho m M} (H : LE_Interp rho m M) : P H := by
  suffices P H ∧ LE_Interp.RDeepChildren P H from this.1
  induction H with
  | bot => exact ⟨step _ .bot, .bot⟩
  | bvar h => exact ⟨step _ (.bvar (h := h)), .bvar (h := h)⟩
  | sort h => exact ⟨step _ (.sort (h := h)), .sort (h := h)⟩
  | app hf ha h ihf iha =>
    exact ⟨step _ (.app (h := h) ihf.2 iha.2),
      .app (h := h) ihf.2 iha.2⟩
  | lam ha hdom hbody h iha ihbody =>
    exact ⟨step _ (.lam (hdom := hdom) (hbody := hbody) (h := h)
        iha.2 (fun x hx => (ihbody x hx).2)),
      .lam (hdom := hdom) (hbody := hbody) (h := h)
        iha.2 (fun x hx => (ihbody x hx).2)⟩
  | forallE hb hb' hdom hbody h ihb ihb' ihbody =>
    exact ⟨step _ (.forallE (hdom := hdom) (hbody := hbody) (h := h)
        ihb.2 ihb'.2 (fun x hx => (ihbody x hx).2)),
      .forallE (hdom := hdom) (hbody := hbody) (h := h)
        ihb.2 ihb'.2 (fun x hx => (ihbody x hx).2)⟩
  | const hreg hlen hle hty hA hC hR ihA ihR =>
    exact ⟨step _ (.const (hreg := hreg) (hlen := hlen) (hle := hle)
        (hty := hty) (hC := hC) ihA.2 (fun m e hr => (ihR m e hr).1)
        (fun m e hr => (ihR m e hr).2)),
      .const (hreg := hreg) (hlen := hlen) (hle := hle)
        (hty := hty) (hC := hC) ihA.2 (fun m e hr => (ihR m e hr).1)
        (fun m e hr => (ihR m e hr).2)⟩

/-- Nested well-founded recursion over two propositional semantic trees.

The first tree's recursive predicate is quantified over every possible
second tree.  Consequently an abstract `R` edge on either side is a recursive
call, while ordinary syntax children retain the tree needed by a second,
syntax-indexed induction.  Proof irrelevance means this construction cannot
retain an evaluator's exact constructor choice; it is therefore appropriate
only for proof-independent binary predicates. -/
theorem LE_Interp.recRDeep₂
    {P : ∀ {ρm m M ρa a A},
      LE_Interp ρm m M → LE_Interp ρa a A → Prop}
    (step : ∀ {ρm m M ρa a A}
        (hM : LE_Interp ρm m M) (hA : LE_Interp ρa a A),
      LE_Interp.RDeepChildren
          (fun hM' => ∀ {ρa a A} (hA' : LE_Interp ρa a A), P hM' hA') hM →
      LE_Interp.RDeepChildren (fun hA' => P hM hA') hA →
      P hM hA)
    {rhom m M rhoa a A}
    (hM : LE_Interp rhom m M) (hA : LE_Interp rhoa a A) :
    P hM hA := by
  refine LE_Interp.recRDeep
    (P := fun hM =>
      ∀ {rhoa a A} (hA : LE_Interp rhoa a A), P hM hA) ?_ hM hA
  intro rhom m M hM childrenM rhoa a A hA
  exact LE_Interp.recRDeep
    (P := fun hA => P hM hA)
    (fun hA childrenA => step hM hA childrenM childrenA) hA

theorem LE_Interp.bvar' : LE_Interp ρ (ρ i) (.bvar i) := .bvar .rfl
theorem LE_Interp.bvar0 : LE_Interp (.push ρ x) x (.bvar 0) := .bvar' (ρ := ρ.push x) (i := 0)
theorem LE_Interp.sort' : LE_Interp ρ (.sort (l ≠ .zero)) (.sort l) := .sort .rfl
theorem LE_Interp.app' (h1 : LE_Interp ρ (WShape.T f) F) (h2 : LE_Interp ρ a.T A) :
    LE_Interp ρ (f.app a).T (.app F A) := .app h1 h2 .rfl
theorem LE_Interp.lam' {f : WShapeFun n} {a : WShape n}
    (h1 : LE_Interp ρ (WShape.T a) A) (h2 : WShape.HasDom f a)
    (h3 : ∀ x, x.HasType a → LE_Interp (ρ.push x.T) (f.app x).T F) :
    LE_Interp ρ (WShape.T (n := n+1) (WShape.lam' f)) (.lam A F) := .lam h1 h2 h3 .rfl
theorem LE_Interp.forallE' {f : WShapeFun n} {b b' : WShape n}
    (h1 : LE_Interp ρ b.T B) (h2 : LE_Interp ρ b'.T B) (h3 : WShape.HasDom f b')
    (h4 : ∀ x, x.HasType b' → LE_Interp (ρ.push x.T) (f.app x).T F) :
    LE_Interp ρ (WShape.T (n := n+1) (.forallE b f)) (.forallE B F) := .forallE h1 h2 h3 h4 .rfl

theorem LE_Interp.bvar_iff : LE_Interp ρ m (.bvar i) ↔ m ≤ ρ i :=
  ⟨fun | .bot => TShape.bot_le' | .bvar h => h, .bvar⟩

theorem LE_Interp.le_sort (H : LE_Interp ρ m (.sort u)) : m ≤ .sort (u ≠ .zero) := by
  generalize eq : SExpr.sort u = M at H
  induction H with cases eq
  | bot => exact TShape.bot_le'
  | sort h => exact h.trans TShape.sort_eqv.1

theorem LE_Interp.le_sort' (H : LE_Interp ρ m (.sort u)) : m.2 ≤ .sort (u ≠ .zero) :=
  (TShape.LE.lift_r (Nat.zero_le _)).1 H.le_sort

theorem LE_Interp.RHS.mono (h : m ≤ m')
    (hR : ∀ {a a' A}, a ≤ a' → R a' A → R' a A)
    (H : RHS m1 m2 R m' r) : RHS m1 m2 R' m r := by
  induction H generalizing m with
  | bot => exact TShape.le_bot'.1 (h.trans TShape.bot_eqv.1) ▸ .bot
  | const h1 => exact .const (hR h h1)
  | var h1 => exact .var (h.trans h1)
  | app hf ha h1 ihf iha => exact .app (ihf .rfl) (iha .rfl) (h.trans h1)

theorem LE_Interp.Const.mono (h : m ≤ m')
    (hR : ∀ {a a' A}, a ≤ a' → R a' A → R' a A)
    (H : Const c ls R rargs m') : Const c ls R' rargs m := by
  induction H generalizing m with
  | bot => exact TShape.le_bot'.1 (h.trans TShape.bot_eqv.1) ▸ .bot
  | lam _ h2 ih => exact .lam (ih · · · .rfl) (h.trans h2)
  | ctor h1 h2 => exact .ctor h1 (h.trans h2)
  | indTy h1 h2 => exact .indTy h1 (h.trans h2)
  | pat h1 h2 h3 => exact .pat h1 h2 (h3.mono h hR)

theorem LE_Interp.mono (h : m ≤ m') (H : LE_Interp ρ m' M) : LE_Interp ρ m M := by
  induction H generalizing m with
  | bot => exact TShape.le_bot'.1 (h.trans TShape.bot_eqv.1) ▸ .bot
  | bvar h1 => exact .bvar (h.trans h1)
  | sort h1 => exact .sort (h.trans h1)
  | app hf ha h1 => exact .app hf ha (h.trans h1)
  | lam ha hdom hbody h1 => exact .lam ha hdom hbody (h.trans h1)
  | forallE hb hb' hdom hbody h1 => exact .forallE hb hb' hdom hbody (h.trans h1)
  | const h1 h2 h3 h4 h5 h6 h7 => exact .const h1 h2 (h.trans h3) h4 h5 h6 h7

/-- Realize a semantic RHS as the concrete S-expression obtained by
instantiating its fixed leaves and materializing its captures.  Keeping this
lemma separate from `RHS.mono` preserves the original `R` witness, which is
what a proof-relevant fixed-head consumer uses before forgetting its chosen
constructor tree. -/
theorem LE_Interp.RHS.realize
    (hR : ∀ {m M}, R m M → LE_Interp ρ m M)
    (hcap : ∀ path, LE_Interp ρ (m2 path) (capture path))
    (H : RHS ls m2 R m r) :
    LE_Interp ρ m (r.applyS ls capture) := by
  induction H with
  | bot => exact .bot
  | const hr => exact hR hr
  | var hle => exact (hcap _).mono hle
  | app _ _ hle ihf iha => exact .app ihf iha hle

/-- Materialize a semantic RHS without forgetting the exact witness trees
selected for its fixed leaves and captures.  The intermediate `Nonempty`
result is the permitted elimination boundary from the propositional RHS
derivation into the proof-relevant interpreter. -/
theorem LE_Interp.RHS.realizeWitnessNonempty
    {p : Pattern} {m2 : p.Path → TShape}
    {capture : p.Path → SExpr} {r : p.RHS}
    (hR : ∀ {m M}, R m M → LE_Interp.Witness ρ m M)
    (hcap : ∀ path, LE_Interp.Witness ρ (m2 path) (capture path))
    (H : RHS ls m2 R m r) :
    Nonempty (LE_Interp.Witness ρ m (r.applyS ls capture)) := by
  induction H with
  | bot => exact ⟨.bot⟩
  | const hr => exact ⟨hR hr⟩
  | var hle => exact ⟨(hcap _).mono hle⟩
  | app _ _ hle ihf iha =>
    exact ⟨.app (Classical.choice ihf) (Classical.choice iha) hle⟩

/-- Choose the proof-relevant materialization of a complete semantic RHS. -/
noncomputable def LE_Interp.RHS.realizeWitness
    {p : Pattern} {m2 : p.Path → TShape}
    {capture : p.Path → SExpr} {r : p.RHS}
    (hR : ∀ {m M}, R m M → LE_Interp.Witness ρ m M)
    (hcap : ∀ path, LE_Interp.Witness ρ (m2 path) (capture path))
    (H : RHS ls m2 R m r) :
    LE_Interp.Witness ρ m (r.applyS ls capture) :=
  Classical.choice (H.realizeWitnessNonempty hR hcap)

theorem LE_Interp.RHS.realizeWitness_toInterp
    {p : Pattern} {m2 : p.Path → TShape}
    {capture : p.Path → SExpr} {r : p.RHS}
    (hR : ∀ {m M}, R m M → LE_Interp.Witness ρ m M)
    (hcap : ∀ path, LE_Interp.Witness ρ (m2 path) (capture path))
    (H : RHS ls m2 R m r) :
    (H.realizeWitness hR hcap).toInterp =
      H.realize (fun hr => (hR hr).toInterp)
        (fun path => (hcap path).toInterp) :=
  Subsingleton.elim _ _

/-- A fixed semantic RHS selects either bottom or one exact recursive
interpretation witness.  Returning `Nonempty` first is the permitted
Prop-to-Type boundary; the relation parameter and its callback remain fixed
even though the `RHS` derivation itself is proof-irrelevant. -/
theorem LE_Interp.RHS.fixedWitnessNonempty
    (hR : ∀ {m M}, R m M → LE_Interp.Witness ρ m M)
    (H : RHS ls m2 R m (.fixed e cl)) :
    Nonempty (LE_Interp.Witness ρ m (SExpr.mkInst ls e)) := by
  cases H with
  | bot => exact ⟨.bot⟩
  | const hr => exact ⟨hR hr⟩

/-- Choose the exact witness selected by a fixed RHS. -/
noncomputable def LE_Interp.RHS.fixedWitness
    (hR : ∀ {m M}, R m M → LE_Interp.Witness ρ m M)
    (H : RHS ls m2 R m (.fixed e cl)) :
    LE_Interp.Witness ρ m (SExpr.mkInst ls e) :=
  Classical.choice (H.fixedWitnessNonempty hR)

theorem LE_Interp.RHS.fixedWitness_toInterp
    (hR : ∀ {m M}, R m M → LE_Interp.Witness ρ m M)
    (H : RHS ls m2 R m (.fixed e cl)) :
    LE_Interp ρ m (SExpr.mkInst ls e) :=
  (H.fixedWitness hR).toInterp

/-- The downward-closed singleton relation generated by one exact witness.

This is the focused evaluator relation used when reverse action soundness
reconstructs a constant from a particular RHS endpoint.  Its only possible
term is the endpoint retained by `hX`, and every realization is literally
that witness with its root observation lowered.  Consequently the relation
cannot broaden to an unrelated semantic derivation at the same public
indices. -/
def LE_Interp.Witness.LowerEdge
    {ρ : Valuation} {root : TShape} {X : SExpr}
    (hX : LE_Interp.Witness ρ root X)
    (m : TShape) (M : SExpr) : Prop :=
  M = X ∧ m ≤ root

/-- Realize a focused edge without reselecting its proof-relevant tree. -/
def LE_Interp.Witness.LowerEdge.realize
    {hX : LE_Interp.Witness ρ root X}
    (H : hX.LowerEdge m M) : LE_Interp.Witness ρ m M := by
  obtain ⟨rfl, hle⟩ := H
  exact hX.mono hle

/-- Focused edges are closed under further root lowering. -/
theorem LE_Interp.Witness.LowerEdge.mono
    {hX : LE_Interp.Witness ρ root X}
    (hle : m ≤ m') (H : hX.LowerEdge m' M) : hX.LowerEdge m M :=
  ⟨H.1, hle.trans H.2⟩

/-- The generating witness is the maximal focused edge. -/
theorem LE_Interp.Witness.LowerEdge.self
    (hX : LE_Interp.Witness ρ root X) : hX.LowerEdge root X :=
  ⟨rfl, .rfl⟩

/-- Downward closure of an abstract semantic relation.  Unlike mapping the
relation into `LE_Interp`, this wrapper retains the original witness so that
the matching proof-relevant callback remains recoverable at fixed RHS heads. -/
def LE_Interp.Lower (R : TShape → SExpr → Prop) (m : TShape) (M : SExpr) : Prop :=
  ∃ m', m ≤ m' ∧ R m' M

theorem LE_Interp.Lower.of (H : R m M) : LE_Interp.Lower R m M :=
  ⟨m, .rfl, H⟩

theorem LE_Interp.Lower.mono
    (h : m ≤ m') (H : LE_Interp.Lower R m' M) : LE_Interp.Lower R m M := by
  obtain ⟨m'', hm', hR⟩ := H
  exact ⟨m'', h.trans hm', hR⟩

theorem LE_Interp.Lower.realize
    (hR : ∀ {m M}, R m M → LE_Interp ρ m M)
    (H : LE_Interp.Lower R m M) : LE_Interp ρ m M := by
  obtain ⟨m', hm, hr⟩ := H
  exact (hR hr).mono hm

/-- Proof-relevant realization of downward closure.  The returned witness is
the original `R` child with only its root observation lowered. -/
noncomputable def LE_Interp.Lower.realizeWitness
    (hR : ∀ {m M}, R m M → LE_Interp.Witness ρ m M)
    (H : LE_Interp.Lower R m M) : LE_Interp.Witness ρ m M := by
  let m' := Classical.choose H
  have hm : m ≤ m' := (Classical.choose_spec H).1
  have hr : R m' M := (Classical.choose_spec H).2
  exact (hR hr).mono hm

/-- Realize the fixed head selected by a downward-closed evaluator branch
through the exact recursive witness callback of its enclosing constant. -/
noncomputable def LE_Interp.RHS.fixedLowerWitness
    (hR : ∀ {m M}, R m M → LE_Interp.Witness ρ m M)
    (H : RHS ls m2 (LE_Interp.Lower R) m (.fixed e cl)) :
    LE_Interp.Witness ρ m (SExpr.mkInst ls e) :=
  H.fixedWitness (LE_Interp.Lower.realizeWitness hR)

/-- Select a non-bottom fixed head together with the recursive result carried
by the exact `R` edge that produced it.  The ordinary `fixedLowerWitness`
adapter intentionally forgets this second component; adequacy cannot do so,
because choosing another witness at the same public indices may choose a
different abstract constant relation.

The monotonicity callback accounts for `Lower`: the evaluator may expose an
`R` witness at a larger observation and then lower only its root. -/
theorem LE_Interp.RHS.fixedLowerWitnessResultNonempty
    {P : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop}
    (hR : ∀ {m M}, R m M → LE_Interp.Witness ρ m M)
    (hP : ∀ {m M} (hr : R m M), P (hR hr))
    (hmono : ∀ {m m' M} (hle : m ≤ m')
      (H : LE_Interp.Witness ρ m' M), P H → P (H.mono hle))
    (H : RHS ls m2 (LE_Interp.Lower R) m (.fixed e cl))
    (hnonbot : ¬m ≤ TShape.bot) :
    Nonempty {H : LE_Interp.Witness ρ m (SExpr.mkInst ls e) // P H} := by
  cases H with
  | bot => exact (hnonbot TShape.bot_eqv.1).elim
  | const hr =>
    obtain ⟨m', hle, hr⟩ := hr
    exact ⟨⟨(hR hr).mono hle, hmono hle (hR hr) (hP hr)⟩⟩

/-- The proof-relevant fixed-head package selected by
`fixedLowerWitnessResultNonempty`. -/
noncomputable def LE_Interp.RHS.fixedLowerWitnessResult
    {P : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop}
    (hR : ∀ {m M}, R m M → LE_Interp.Witness ρ m M)
    (hP : ∀ {m M} (hr : R m M), P (hR hr))
    (hmono : ∀ {m m' M} (hle : m ≤ m')
      (H : LE_Interp.Witness ρ m' M), P H → P (H.mono hle))
    (H : RHS ls m2 (LE_Interp.Lower R) m (.fixed e cl))
    (hnonbot : ¬m ≤ TShape.bot) :
    {H : LE_Interp.Witness ρ m (SExpr.mkInst ls e) // P H} :=
  Classical.choice
    (H.fixedLowerWitnessResultNonempty hR hP hmono hnonbot)

theorem LE_Interp.RHS.fixedLowerWitness_toInterp
    (hR : ∀ {m M}, R m M → LE_Interp.Witness ρ m M)
    (H : RHS ls m2 (LE_Interp.Lower R) m (.fixed e cl)) :
    LE_Interp ρ m (SExpr.mkInst ls e) :=
  (H.fixedLowerWitness hR).toInterp

theorem LE_Interp.mono_l (hρ : ρ.LE ρ') (H : LE_Interp ρ m M) : LE_Interp ρ' m M := by
  induction H generalizing ρ' with
  | bot => exact .bot
  | bvar h1 => exact .bvar (h1.trans (hρ _))
  | sort h1 => exact .sort h1
  | app _ _ h1 ih_f ih_a => exact .app (ih_f hρ) (ih_a hρ) h1
  | lam _ hdom _ h1 ih_a ih_body =>
    exact .lam (ih_a hρ) hdom (fun x hx => ih_body x hx (Valuation.LE.push.2 ⟨hρ, .rfl⟩)) h1
  | forallE _ _ hdom _ h1 ih_b ih_b' ih_body =>
    refine .forallE (ih_b hρ) (ih_b' hρ) hdom ?_ h1
    exact fun x hx => ih_body x hx (Valuation.LE.push.2 ⟨hρ, .rfl⟩)
  | const h1 h2 h3 h4 _ h6 _ ihA ihR => exact .const h1 h2 h3 h4 (ihA hρ) h6 (ihR · · · hρ)

theorem LE_Interp.unlift (le : m.1 ≤ n)
    (H : LE_Interp ρ (m.2.lift n).T M) : LE_Interp ρ m M := H.mono (TShape.lift_eqv le).2

theorem LE_Interp.RHS.mono_l (hm : ∀ p, m2' p ≤ m2 p) (H : RHS m1 m2' R m r) : RHS m1 m2 R m r := by
  induction H  with try subst eq
  | bot => exact .bot
  | const h1 => exact .const h1
  | app hf ha h1 ihf iha => exact .app ihf iha h1
  | @var _ path h1 => exact .var (h1.trans (hm path))

theorem LE_Interp.Matches.varN_const_head
    (H : Matches (.varN (.const c) n) c' rargs m) : c = c' := by
  induction n generalizing rargs with
  | zero => cases H; rfl
  | succ n ih => let .var H := H; exact ih H

theorem LE_Interp.Matches.arity (H : Matches p c rargs m) : Arity (.const c) rargs.length p := by
  induction H with
  | const => exact .refl
  | var _ ih => exact .var ih
  | app _ _ ih_f _ => exact .app ih_f

theorem LE_Interp.Matches.nil_inv
    (H : Matches (n := n) p c [] m) : p = .const c := by
  cases H
  rfl

/-- A reached nonempty pattern spine is necessarily an iota pattern.
Definition patterns match only the bare constant, so they cannot occur after
the constant evaluator has consumed its first related argument. -/
theorem LE_Interp.Matches.iota_of_pat_nonempty
    (hpat : Params.Pat p r) (H : Matches (n := n) p c rargs m)
    (hne : rargs ≠ []) :
    ∃ rec major ctor arity,
      p = RecursorIotaPattern rec major ctor arity := by
  obtain ⟨sp, hp⟩ := Params.pat_simple hpat
  cases sp with
  | defn head =>
    subst p
    cases H
    exact (hne rfl).elim
  | iota rec major ctor arity =>
    exact ⟨rec, major, ctor, arity, hp⟩

theorem LE_Interp.Matches.head_wf (H : Matches p c rargs m) (wf : p.WF cl top k) :
    ∃ k, cl c = some (if top then .symb k else .ctor k) := by
  induction H generalizing k with
  | const => exact ⟨_, wf⟩
  | var _ ih => exact ih wf
  | app _ _ ih => exact ih wf.1

theorem LE_Interp.Matches.head_wf_eq (H : Matches p c rargs m) (wf : p.WF cl top k) :
    cl c = some (if top then .symb (k + rargs.length) else .ctor (k + rargs.length)) := by
  induction H generalizing k with
  | const => simpa [Pattern.WF] using wf
  | var _ ih =>
    have := ih (k := k + 1) wf
    rw [List.length_cons]; rw [Nat.add_succ, ← Nat.succ_add]; exact this
  | app _ _ ih =>
    have := ih (k := k + 1) wf.1
    rw [List.length_cons]; rw [Nat.add_succ, ← Nat.succ_add]; exact this

theorem LE_Interp.Matches.mono_l {rargs rargs'} (wfp : p.WF Params.classify b k)
    (hc : List.Forall₂ (· ≤ ·) rargs rargs') (H : Matches (n := n) p c rargs m) :
    ∃ m', Matches (n := n) p c rargs' m' ∧ ∀ p, m p ≤ m' p := by
  induction H generalizing b k with
  | const => cases hc; exact ⟨_, .const, nofun⟩
  | var _ ih =>
    have .cons hc1 hc := hc; have ⟨_, h1, h2⟩ := ih wfp hc
    exact ⟨_, h1.var, (·.casesOn hc1.T h2)⟩
  | app _ ha ih1 ih2 =>
    have .cons hc1 hc := hc; have ⟨m2f, f1, f2⟩ := ih1 wfp.1 hc
    obtain ⟨l, b1, rfl, b2⟩ := WShape.ctor'_le.1 hc1 fun h => by
      have ⟨_, eq⟩ := ha.head_wf wfp.2; simp [IsStruct, eq] at h
    obtain ⟨l, rfl⟩ : ∃ l', List.reverse l' = l := ⟨_, l.reverse_reverse⟩
    simp [List.Forall₂.reverse, WShape.ctor_eq_ctor'] at b2 hc1 ⊢
    have ⟨m2a, a1, a2⟩ := ih2 wfp.2 b2
    exact ⟨Sum.elim m2f m2a, f1.app a1, (·.casesOn f2 a2)⟩

theorem LE_Interp.Const.mono_l (h : rargs.Forall₂ (· ≤ ·) rargs')
    (H : Const c ls R rargs m) : Const c ls R rargs' m := by
  induction H generalizing rargs' with
  | bot => exact .bot
  | lam h1 h2 ih => exact .lam (fun x y h' => ih _ _ h' (.cons .rfl h)) h2
  | ctor h1 h2 =>
    exact .ctor (h.length_eq ▸ h1) <| h2.trans (WShape.ctor'_le_ctor' (List.Forall₂.reverse.2 h)).T
  | indTy h1 h2 => exact .indTy (h.length_eq ▸ h1) h2
  | pat h1 h2 h3 =>
    have ⟨_, a1, a2⟩ := h2.mono_l (Params.pat_wf h1) h
    refine .pat h1 a1 (h3.mono_l a2)

theorem LE_Interp.Const.lam_apply
    {g f : WShapeFun n} {hg : g.NonZero}
    (hrec : ∀ x y : WShape n, (x, y) ∈ f →
      Const c ls R (x :: rargs) y.T)
    (hle : (WShape.lam g hg).T ≤ (WShape.lam' f).T)
    (hR : ∀ {a a' A}, a ≤ a' → R a' A → R a A)
    (p : WShape n) :
    Const c ls R (p :: rargs) (g.app p).T := by
  have hgf : g ≤ f := by
    have hle' : (WShape.lam' g).T ≤ (WShape.lam' f).T := by
      rw [← WShape.lam_eq_lam' (f := g) (hl := hg)]
      exact hle
    have hgf := TShape.LE.lam'_decomp hle'
    exact (WShapeFun.lift_le_lift (Nat.le_max_left n n)).1 hgf
  obtain ⟨x₀, hx₀, hmemg⟩ := g.app_eq p
  obtain ⟨x, y, hmemf, hx, hy⟩ := WShapeFun.LE.def'.1 hgf _ _ hmemg
  have hc : Const c ls R (x :: rargs) (g.app p).T :=
    LE_Interp.Const.mono (c := c) (ls := ls) (R := R) (R' := R)
      hy.T (fun le hr => hR le hr) (hrec x y hmemf)
  exact hc.mono_l (.cons (hx.trans hx₀) (.rfl fun _ _ => .rfl))

theorem LE_Interp.Matches.matches_inter {rargs rargs'}
    (hc : List.Forall₂ WShape.Compat rargs rargs')
    (hp : Matches (n := n) p c rargs m) (wfp : p.WF Params.classify b k)
    (hq : Matches (n := n) q c rargs' m') (wfq : q.WF Params.classify b' k') :
    ∃ r, p.inter q = some r := by
  induction hp generalizing q b b' k k' with
  | const => cases hc; cases hq; simp [Pattern.inter]
  | var _ ih =>
    have .cons _ hc := hc
    cases hq with
    | var hq' => obtain ⟨_, ihf⟩ := ih hc wfp hq' wfq; simp [Pattern.inter, ihf]
    | app hf' => obtain ⟨_, ihf⟩ := ih hc wfp hf' wfq.1; simp [Pattern.inter, ihf]
  | @app _ _ _ _ _ _ c rargs _ hf ha ihf iha =>
    have .cons hc1 hc := hc
    cases hq with
    | var hf' => have ⟨_, ih⟩ := ihf hc wfp.1 hf' wfq; simp [Pattern.inter, ih]
    | @app _ _ _ _ _ _ c' rargs' _ hf' ha' =>
      obtain ⟨_, ihf⟩ := ihf hc wfp.1 hf' wfq.1
      obtain ⟨rfl, hc'⟩ : c = c' ∧ List.Forall₂ WShape.Compat rargs rargs' := by
        unfold WShape.ctor' at hc1; split at hc1 <;> [split at hc1; skip] <;> rename_i hn
        · simp [WShape.Compat, WShape.ctor, Shape.Compat, List.Forall₂.reverse] at hc1; exact hc1
        · have ⟨_, wf⟩ := ha'.head_wf wfq.2; simp [IsStruct, wf] at hn
        · have ⟨_, wf⟩ := ha.head_wf wfp.2; simp [IsStruct, wf] at hn
      have ⟨_, iha⟩ := iha hc' wfp.2 ha' wfq.2
      simp [Pattern.inter, ihf, iha]

theorem LE_Interp.Matches.compat_join {rargs rargs'}
    (hc : List.Forall₂ WShape.Compat rargs rargs')
    (hp : Matches (n := n) p c rargs m) (hp' : Matches (n := n) p c rargs' m')
    (wf : p.WF Params.classify b k) :
    (∀ x, (m x).Compat (m' x)) ∧
    Matches p c (rargs.zipWith WShape.join rargs') fun x => (m x).join (m' x) := by
  induction hp generalizing b k with
  | const => cases hp'; exact ⟨nofun, cast (by congr 1; ext ⟨⟩) Matches.const⟩
  | @var f c n rargs mf a _ ih =>
    let .cons hc1 hc := hc
    let .var (a := a') (mf := mf') hf' := hp'
    have ⟨ihC, ihM⟩ := ih hc hf' wf
    refine' ⟨(·.casesOn hc1.T ihC), cast ?_ ihM.var⟩; congr 1; ext ⟨⟩
    · exact WShape.T_join.symm
    · rfl
  | @app _ _ _ _ _ _ c₁ rargs _ hf ha ihf iha =>
    let .cons hc1 hc := hc; let .app (c' := c₂) (rargs' := rargs') hf' ha' := hp'
    obtain ⟨rfl, hc'⟩ : c₁ = c₂ ∧ List.Forall₂ WShape.Compat rargs rargs' := by
      unfold WShape.ctor' at hc1; split at hc1 <;> [split at hc1; skip] <;> rename_i hn
      · simp [WShape.Compat, WShape.ctor, Shape.Compat, List.Forall₂.reverse] at hc1; exact hc1
      · have ⟨_, wf⟩ := ha'.head_wf wf.2; simp [IsStruct, wf] at hn
      · have ⟨_, wf⟩ := ha.head_wf wf.2; simp [IsStruct, wf] at hn
    have ⟨ihfC, ihfM⟩ := ihf hc hf' wf.1
    have ⟨ihaC, ihaM⟩ := iha hc' ha' wf.2
    refine ⟨(·.casesOn ihfC ihaC), cast ?_ (ihfM.app ihaM)⟩; congr 1
    · simp [List.reverse_zipWith hc'.length_eq, ← WShape.ctor'_join (List.Forall₂.reverse.2 hc')]
    · ext ⟨⟩ <;> rfl

theorem LE_Interp.Matches.unique {p : Pattern} {c : Name} {n : Nat} {rargs : List (WShape n)}
    {m m' : p.Path → TShape}
    (wf : p.WF Params.classify b k)
    (H : Matches (n := n) p c rargs m) (H' : Matches (n := n) p c rargs m') : m = m' := by
  induction H generalizing b k with
  | const => cases H'; rfl
  | var _ ih =>
    let .var hf' := H'
    refine funext fun | none => rfl | some p => congrFun (ih wf hf') p
  | app _ ha ihf iha =>
    generalize eq' : WShape.ctor' .. = head_w at H'
    let .app hf' ha' := H'
    have ⟨_, wf_a⟩ := ha.head_wf wf.2
    have ⟨_, wf_a'⟩ := ha'.head_wf wf.2
    simp [WShape.ctor', IsStruct, wf_a, wf_a'] at eq'
    obtain ⟨rfl, eq⟩ := WShape.ctor.inj.1 eq'; cases List.reverse_inj.1 eq
    rw [ihf wf.1 hf', iha wf.2 ha']

theorem LE_Interp.RHS.compat_join
    {m₁ m₂} (hpm : ∀ x, (m₁ x).Compat (m₂ x))
    (hR_bot : ∀ {n e}, R (WShape.T (n := n) .bot) e)
    (hR'_bot : ∀ {n e}, R' (WShape.T (n := n) .bot) e)
    (hRR : ∀ {m₁ m₂ A}, R m₁ A → R' m₂ A → m₁.Compat m₂ ∧ R₃ (m₁.join m₂) A)
    (hR₃_mono : ∀ {a a' A}, a ≤ a' → R₃ a' A → R₃ a A)
    (H1 : RHS (p := p) ls m₁ R m r) (H2 : RHS ls m₂ R' m' r) :
    m.Compat m' ∧ RHS ls (fun x => (m₁ x).join (m₂ x)) R₃ (m.join m') r := by
  induction H1 generalizing m' with
  | bot =>
    refine ⟨.bot_l', ?_⟩
    cases H2 with
    | bot => (conv => arg 4; simp [TShape.join]); exact .bot
    | const h2 => exact .const (hRR hR_bot h2).2
    | var h2 =>
      conv => arg 4; simp [TShape.join]
      refine .var <| (TShape.lift_eqv (Nat.le_max_right ..)).1.trans ?_
      exact h2.trans (TShape.Join.mk (hpm _)).le.2
    | app hf' ha' h2 =>
      refine .mono ?_ ?_ <| .mono_l (fun p => (TShape.Join.mk (hpm p)).le.2) <| .app hf' ha' h2
      · exact (TShape.Join.mk .bot_l' _).2 ⟨TShape.bot_le', .rfl⟩
      · intro a a' A le hr
        have := hRR (@hR_bot 0 A) hr
        exact hR₃_mono (le.trans (TShape.Join.mk this.1).le.2) this.2
  | const h1 =>
    cases H2 with
    | bot => exact ⟨.bot_r', .const (hRR h1 hR'_bot).2⟩
    | const h2 => exact ⟨(hRR h1 h2).1, .const (hRR h1 h2).2⟩
  | var h1 => cases H2 with
    | bot =>
      refine ⟨.bot_r', ?_⟩
      conv => arg 4; simp [TShape.join]
      refine .var <| (TShape.lift_eqv (Nat.le_max_left ..)).1.trans ?_
      exact h1.trans (TShape.Join.mk (hpm _)).le.1
    | var h2 =>
      refine ⟨(hpm _).mono h1 h2, .var ?_⟩
      exact have ⟨a1, a2⟩ := (TShape.Join.mk (hpm _)).le
        (TShape.Join.mk ((hpm _).mono h1 h2) _).2 ⟨h1.trans a1, h2.trans a2⟩
  | @app n₁ f₁ _ _ _ a₁ hf ha h1 ihf iha => cases H2 with
    | bot =>
      refine ⟨.bot_r', ?_⟩
      refine .mono ?_ ?_ <| .mono_l (fun p => (TShape.Join.mk (hpm p)).le.1) <| .app hf ha h1
      · conv => lhs; simp [TShape.join]
        exact (TShape.lift_eqv (Nat.le_max_left ..)).1
      · intro a a' A le hr
        have := hRR hr (@hR'_bot 0 A)
        exact hR₃_mono (le.trans (TShape.Join.mk this.1).le.1) this.2
    | @app n f _ _ _ a hf' ha' h2 =>
      have ⟨cf, jf⟩ := ihf hf'
      have ⟨ca, ja⟩ := iha ha'
      refine have cM := .mono h1 h2 <| cf.app ca; ⟨cM, ?_⟩
      have hf := (TShape.Join.mk cf).le
      have ha := (TShape.Join.mk ca).le
      have le' := Nat.le_of_eq <| Nat.add_max_add_right n₁ n 1
      refine .mono (R := R₃) (R' := R₃) ((TShape.Join.mk cM _).2 ⟨?_, ?_⟩) hR₃_mono <|
        .app (jf.mono (R := R₃) (R' := R₃) (TShape.lift_eqv le').1 hR₃_mono) ja .rfl
      · exact h1.trans <| TShape.app_mono (hf.1.trans (TShape.lift_eqv le').2) ha.1
      · exact h2.trans <| TShape.app_mono (hf.2.trans (TShape.lift_eqv le').2) ha.2

theorem pat_arity (hP : Params.Pat p r) (h : Arity (.const c) n p) :
    Params.classify c = some (.symb n) := by
  suffices ∀ cl n k, p.WF cl true k → Arity (.const c) n p → cl c = some (.symb (n + k)) from
    this _ _ _ (Params.pat_wf hP) h
  clear r hP h; intro cl n k h1 h2
  induction h2 generalizing k with
  | refl => simpa only [Nat.zero_add]
  | var _ ih => simpa [Nat.succ_add, ← Nat.add_assoc] using ih _ h1
  | app _ ih => simpa [Nat.succ_add, ← Nat.add_assoc] using ih _ h1.1

theorem const_spine_ne_lam
    {c : Name} {ls : List SLevel} {args : List SExpr} {A e : SExpr} :
    args.foldr (fun (a f : SExpr) => .app f a) (.const c ls) ≠ .lam A e := by
  induction args with
  | nil => simp
  | cons => simp

private def constHead? : SExpr → Option Name
  | .const c _ => some c
  | .app f _ => constHead? f
  | _ => none

@[simp] private theorem constHead?_spine
    {c : Name} {ls : List SLevel} {args : List SExpr} :
    constHead? (args.foldr (fun a f => f.app a) (.const c ls)) = some c := by
  induction args with
  | nil => rfl
  | cons _ _ ih => exact ih

/-- A constant-headed spine whose head is not a rewrite symbol cannot be
selected by the user reduction-pattern system. -/
theorem WHNF.const_spine
    {c : Name} {ls : List SLevel} {args : List SExpr}
    (hcl : ∀ k, Params.classify c ≠ some (.symb k)) :
    WHNF Γ (args.foldr (fun a f => f.app a) (.const c ls)) := by
  induction args with
  | nil =>
    intro e hred
    cases hred with
    | extra action =>
      obtain ⟨c', ls', as, heq, har⟩ := action.matched.head_spine
      simp only [List.foldr_nil] at heq
      have hc : c = c' := by
        simpa only [constHead?, constHead?_spine, Option.some.injEq] using
          congrArg constHead? heq
      subst c'
      exact hcl _ (pat_arity action.pat har)
  | cons a args ih =>
    simp only [List.foldr_cons]
    intro e hred
    generalize hf : args.foldr (fun (a f : SExpr) => .app f a) (.const c ls) = f at hred
    cases hred with
    | app h =>
      rw [← hf] at h
      exact ih _ h
    | major hmajor _ =>
      obtain ⟨p, ⟨r, hp⟩, p₁, p₂, hsub, m1, m2, hm⟩ := hmajor
      cases Params.simple_appS hp hsub
      obtain ⟨c', ls', as, heq, har⟩ := hm.head_spine
      rw [← hf] at heq
      have hc : c = c' := by
        simpa only [constHead?, constHead?_spine, Option.some.injEq] using
          congrArg constHead? heq
      subst c'
      exact hcl _ (pat_arity hp (.app har))
    | beta => exact const_spine_ne_lam hf
    | extra action =>
      obtain ⟨c', ls', as, heq, har⟩ := action.matched.head_spine
      rw [← hf] at heq
      have hc : c = c' := by
        simpa only [constHead?, constHead?_spine, Option.some.injEq] using
          congrArg constHead? heq
      subst c'
      exact hcl _ (pat_arity action.pat har)

/-- Inductive-type heads are weak-head normal. -/
theorem WHNF.indTy_spine
    {c : Name} {ls : List SLevel} {args : List SExpr} {k : Nat}
    (hcl : Params.classify c = some (.indTy k)) :
    WHNF Γ (args.foldr (fun a f => f.app a) (.const c ls)) :=
  .const_spine fun _ hs => by
    have hbad : (.indTy k : Classification) = .symb _ := Option.some.inj (hcl.symm.trans hs)
    cases hbad

/-- Fully applied ordinary constructor heads are weak-head normal. -/
theorem WHNF.ctor_spine
    {c : Name} {ls : List SLevel} {args : List SExpr} {k : Nat}
    (hcl : Params.classify c = some (.ctor k)) :
    WHNF Γ (args.foldr (fun a f => f.app a) (.const c ls)) :=
  .const_spine fun _ hs => by
    have hbad : (.ctor k : Classification) = .symb _ := Option.some.inj (hcl.symm.trans hs)
    cases hbad

theorem LE_Interp.Matches.lift (le : n ≤ n') (H : Matches (n := n) p c rargs m) :
    ∃ m', Matches p c (rargs.map (.lift n')) m' ∧ ∀ p, m p ≤ m' p ∧ m' p ≤ m p := by
  induction H generalizing n' with
  | const => exact ⟨_, .const, nofun⟩
  | var _ ih =>
    have ⟨m2', h1, h2⟩ := ih le; exact ⟨_, .var h1, (·.casesOn (TShape.lift_eqv le).symm h2)⟩
  | app _ _ ih1 ih2 =>
    have ⟨m2f, f1, f2⟩ := ih1 le; let n' + 1 := n'
    have ⟨m2a, a1, a2⟩ := ih2 (Nat.le_of_succ_le_succ le)
    refine ⟨Sum.elim m2f m2a, ?_, (·.casesOn f2 a2)⟩
    show Matches _ _ (WShape.lift (n'+1) (WShape.ctor' _ _) :: _) _
    rw [WShape.lift_ctor' (Nat.le_of_succ_le_succ le), List.map_reverse]
    exact f1.app a1

/-- Reflect an ordinary-constructor observation through an exact lift.

The classification premise rules out the structure-constructor bottom case,
so a lifted constructor head has a genuine constructor predecessor and its
fields are exact lifts of the predecessor fields. -/
theorem WShape.lift_eq_ctor'_of_classify_ctor
    {c : Name} {arity : Nat}
    {s : WShape (n + 1)} {l : List (WShape m)}
    (le : n ≤ m)
    (hcl : Params.classify c = some (.ctor arity))
    (eq : s.lift (m + 1) = .ctor' c l) :
    ∃ l0 : List (WShape n),
      s = .ctor' c l0 ∧ l = l0.map (fun x => x.lift m) := by
  have hns : ¬ IsStruct c := by
    simp [IsStruct, hcl]
  have htarget : IsStruct c → WShape.ListNonZero l :=
    fun hs => (hns hs).elim
  rw [WShape.ctor', dif_pos htarget] at eq
  cases s using WShape.casesOn' with
  | bot =>
    simp only [WShape.lift_bot] at eq
    simp [WShape.ext_iff, WShape.bot, WShape.ctor, Shape.bot] at eq
  | sort r =>
    simp only [WShape.lift_sort] at eq
    simp [WShape.ext_iff, WShape.sort, WShape.ctor, Shape.sort] at eq
  | forallE a f =>
    rw [WShape.lift_forallE le] at eq
    simp [WShape.ext_iff, WShape.forallE, WShape.ctor] at eq
  | lam f hf =>
    rw [WShape.lift_lam le] at eq
    simp [WShape.ext_iff, WShape.lam, WShape.ctor] at eq
  | ctor c0 l0 h0 =>
    rw [WShape.lift_ctor le] at eq
    obtain ⟨rfl, hl⟩ := WShape.ctor.inj.1 eq
    exact ⟨l0, (WShape.ctor_eq_ctor' (h := h0)), hl.symm⟩
  | indTy =>
    rw [WShape.lift_indTy] at eq
    simp [WShape.ext_iff, WShape.indTy, WShape.ctor] at eq

private theorem LE_Interp.Matches.unlift_aux
    {p : Pattern} {c : Name} {n n' : Nat}
    {rs : List (WShape n')} {rargs : List (WShape n)}
    {m : p.Path → TShape}
    (le : n ≤ n')
    (wf : p.WF Params.classify b k)
    (H : Matches (n := n') p c rs m)
    (heq : rs = rargs.map (fun x => x.lift n')) :
    ∃ m0, Matches (n := n) p c rargs m0 := by
  induction H generalizing n rargs b k with
  | const =>
    cases rargs with
    | nil => exact ⟨_, .const⟩
    | cons a rargs => simp at heq
  | @var f c n' rargs' mf a H ih =>
    cases rargs with
    | nil => simp at heq
    | cons a0 rargs0 =>
      simp only [List.map_cons, List.cons.injEq] at heq
      obtain ⟨_ha, htail⟩ := heq
      obtain ⟨m0, hm0⟩ := ih le wf htail
      exact ⟨_, hm0.var⟩
  | @app fPat nHigh head rargsHigh mf aPat c' rargsArg ma hf ha ihf iha =>
    cases rargs with
    | nil => simp at heq
    | cons head0 tail0 =>
      simp only [List.map_cons, List.cons.injEq] at heq
      obtain ⟨hhead, htail⟩ := heq
      obtain ⟨arity, hcl⟩ := ha.head_wf wf.2
      simp only [Bool.false_eq_true, if_false] at hcl
      cases n with
      | zero =>
        have htarget : IsStruct c' → WShape.ListNonZero rargsArg.reverse := by
          intro hs
          simp [IsStruct, hcl] at hs
        have hctorNeBot :
            WShape.ctor c' rargsArg.reverse htarget ≠
              (WShape.bot : WShape (nHigh + 1)) := by
          intro h
          have h' := congrArg (fun x => x.1) h
          simp [WShape.ctor, WShape.bot, Shape.bot] at h'
        rw [WShape.ctor', dif_pos htarget] at hhead
        cases head0 using WShape.casesOn with
        | bot =>
          change WShape.ctor c' rargsArg.reverse htarget =
            (WShape.bot : WShape 0).lift (nHigh + 1) at hhead
          rw [WShape.lift_bot] at hhead
          exact (hctorNeBot hhead).elim
        | sort r0 =>
          change WShape.ctor c' rargsArg.reverse htarget =
            (WShape.sort r0 : WShape 0).lift (nHigh + 1) at hhead
          rw [WShape.lift_sort] at hhead
          have hbad : (WShape.sort r0 : WShape (nHigh + 1)).T ≤
              (WShape.ctor c' rargsArg.reverse htarget).T := by
            exact WShape.LE.T (by rw [hhead]; exact .rfl)
          have hbad' : (WShape.sort r0 : WShape (nHigh + 1)).T ≤
              (WShape.ctor' c' rargsArg.reverse).T := by
            rw [WShape.ctor', dif_pos htarget]
            exact hbad
          exact (TShape.sort_not_le_ctor'
            (r := r0) (c := c') (l := rargsArg.reverse) hbad').elim
      | succ nLow =>
        have lePred : nLow ≤ nHigh := Nat.le_of_succ_le_succ le
        obtain ⟨fields0, hhead0, hfields⟩ :=
          WShape.lift_eq_ctor'_of_classify_ctor lePred hcl hhead.symm
        have hfields' : rargsArg =
            fields0.reverse.map (fun x => x.lift nHigh) := by
          have h := congrArg List.reverse hfields
          simpa only [List.reverse_reverse, List.map_reverse] using h
        obtain ⟨mf0, hmf0⟩ := ihf le wf.1 htail
        obtain ⟨ma0, hma0⟩ := iha lePred wf.2 hfields'
        subst head0
        exact ⟨_, by
          simpa only [List.reverse_reverse] using hmf0.app hma0⟩

/-- Reflect a semantic pattern match from exact lifted arguments. -/
theorem LE_Interp.Matches.unlift
    {p : Pattern} {c : Name} {n n' : Nat}
    {rargs : List (WShape n)}
    {m : p.Path → TShape}
    (le : n ≤ n')
    (wf : p.WF Params.classify b k)
    (H : Matches (n := n') p c
      (rargs.map (fun x => x.lift n')) m) :
    ∃ m0, Matches (n := n) p c rargs m0 ∧
      ∀ path, m path ≤ m0 path ∧ m0 path ≤ m path := by
  obtain ⟨m0, hm0⟩ := LE_Interp.Matches.unlift_aux le wf H rfl
  obtain ⟨mLift, hmLift, hcap⟩ := hm0.lift le
  have heq : m = mLift := H.unique wf hmLift
  subst mLift
  exact ⟨m0, hm0, fun path => ⟨(hcap path).2, (hcap path).1⟩⟩

/-- Lift a heterogeneous list of `TShape` bounds to one common concrete
shape level. -/
theorem WShape.forall₂_liftT
    {xs : List (WShape n)} {ys : List (WShape n')}
    (hn : n ≤ K) (hn' : n' ≤ K)
    (H : List.Forall₂ (fun x y => x.T ≤ y.T) xs ys) :
    List.Forall₂ (· ≤ ·)
      (xs.map (fun x => x.lift K))
      (ys.map (fun y => y.lift K)) := by
  induction H with
  | nil => exact .nil
  | cons hxy hrest ih =>
    exact .cons ((TShape.LE.def hn hn').1 hxy) ih

/-- Lift only the target of a heterogeneous list bound. -/
theorem WShape.forall₂_liftT_right
    {xs : List (WShape n)} {ys : List (WShape n')}
    (hn' : n' ≤ K)
    (H : List.Forall₂ (fun x y => x.T ≤ y.T) xs ys) :
    List.Forall₂ (fun x y => x.T ≤ y.T)
      xs (ys.map (fun y => y.lift K)) := by
  induction H with
  | nil => exact .nil
  | cons hxy hrest ih =>
    exact .cons (hxy.trans (TShape.lift_eqv hn').2) ih

/-- Enlarge a semantic match across unrelated concrete shape depths.

Only the level-free `TShape` bounds are semantically relevant.  Both sides
are lifted to a temporary common level, the ordinary monotonicity theorem is
applied there, and exact-lift reflection returns to the target level. -/
theorem LE_Interp.Matches.mono_lT
    {p : Pattern} {c : Name} {n n' : Nat}
    {rargs : List (WShape n)} {rargs' : List (WShape n')}
    {m : p.Path → TShape}
    (wf : p.WF Params.classify b k)
    (hc : List.Forall₂ (fun x y => x.T ≤ y.T) rargs rargs')
    (H : Matches (n := n) p c rargs m) :
    ∃ m', Matches (n := n') p c rargs' m' ∧
      ∀ path, m path ≤ m' path := by
  let K := max n n'
  have hn : n ≤ K := Nat.le_max_left ..
  have hn' : n' ≤ K := Nat.le_max_right ..
  obtain ⟨mK, hmK, hcapK⟩ := H.lift hn
  have hcK := WShape.forall₂_liftT hn hn' hc
  obtain ⟨mK', hmK', hcapK'⟩ := hmK.mono_l wf hcK
  obtain ⟨m', hm', hcap'⟩ := hmK'.unlift hn' wf
  refine ⟨m', hm', fun path => ?_⟩
  exact (hcapK path).1 |>.trans <|
    (hcapK' path).trans (hcap' path).1

theorem LE_Interp.Const.lift (hn : n₁ ≤ n₂)
    (hR : ∀ {a a' A}, a ≤ a' → R a' A → R a A)
    (H : Const (n := n₁) c ls R rargs m) : Const c ls R (rargs.map (.lift n₂)) m := by
  induction H generalizing n₂ with
  | bot => exact .bot
  | @lam f rargs m h1 h2 ih =>
    refine .lam (f := f.lift n₂) (fun _ _ h => ?_) ?_
    · obtain ⟨x, y, h', rfl, rfl⟩ := (WShapeFun.mem_lift hn).1 h
      exact (ih _ _ h' hn).mono (TShape.lift_eqv hn).1 hR
    · exact WShape.lift_lam' hn ▸ h2.trans (TShape.lift_eqv (Nat.succ_le_succ hn)).2
  | ctor h1 h2 =>
    refine .ctor (by rw [List.length_map]; exact h1) (h2.trans ?_)
    rw [← List.map_reverse, ← WShape.lift_ctor' hn]
    exact (TShape.lift_eqv (Nat.succ_le_succ hn)).2
  | indTy h1 h2 =>
    refine .indTy (by rw [List.length_map]; exact h1) (h2.trans ?_)
    rw [← WShape.lift_indTy (n := n₁) (m := n₂)]
    exact (TShape.lift_eqv (Nat.succ_le_succ hn)).2
  | pat h1 h2 h3 =>
    have ⟨_, a1, a2⟩ := h2.lift hn
    exact .pat h1 a1 <| h3.mono_l (a2 · |>.1)

theorem LE_Interp.lift (le : m.1 ≤ n)
    (H : LE_Interp ρ m M) : LE_Interp ρ (m.2.lift n).T M := H.mono (TShape.lift_eqv le).1

theorem LE_Interp.RHS.closed
    (H : RHS m1 m2 R m r) : RHS m1 m2 (fun e A => A.ClosedN ∧ R e A) m r := by
  induction H with
  | bot => exact .bot
  | @const _ _ cl h1 => exact .const ⟨cl.mkInstS, h1⟩
  | var h1 => exact .var h1
  | app hf ha h1 ih_f ih_a => exact .app ih_f ih_a h1

theorem LE_Interp.Const.closed
    (H : Const c ls R rargs m) : Const c ls (fun e A => A.ClosedN ∧ R e A) rargs m := by
  induction H with
  | bot => exact .bot
  | lam _ h2 ih => exact .lam ih h2
  | ctor h1 h2 => exact .ctor h1 h2
  | indTy h1 h2 => exact .indTy h1 h2
  | pat h1 h2 h3 => exact .pat h1 h2 h3.closed

theorem LE_Interp.closed (cl : ClosedN M k) (h : ∀ i < k, ρ i = ρ' i)
    (H : LE_Interp ρ m M) : LE_Interp ρ' m M := by
  induction H generalizing k ρ' with
  | bot => exact .bot
  | sort h1 => exact .sort h1
  | bvar h1 => exact .bvar ((h _ cl).symm ▸ h1)
  | app hf ha h1 ih_f ih_a =>
    exact .app (ih_f cl.1 h) (ih_a cl.2 h) h1
  | lam ha hdom hbody h1 ih_a ih_body =>
    refine .lam (ih_a cl.1 h) hdom (fun x hx => ih_body x hx cl.2 ?_) h1
    intro | 0, _ => rfl | j+1, hi => exact h j (Nat.lt_of_succ_lt_succ hi)
  | forallE hb hb' hdom hbody h1 ih_b ih_b' ih_body =>
    refine .forallE (ih_b cl.1 h) (ih_b' cl.1 h) hdom (fun x hx => ih_body x hx cl.2 ?_) h1
    intro | 0, _ => rfl | i+1, hi => exact h i (Nat.lt_of_succ_lt_succ hi)
  | const h1 h2 h3 h4 _ h6 _ ih1 ih2 =>
    refine .const h1 h2 h3 h4 (ih1 ?_ h) h6.closed fun m e ⟨a1, a2⟩ => ?_
    · exact (Params.henv.closedC h1).mkInstS.mono (Nat.zero_le _)
    · exact ih2 m e a2 (a1.mono (Nat.zero_le _)) h

theorem LE_Interp.closed_iff {M : SExpr} (cl : ClosedN M)
    {ρ ρ' : Valuation} {m : TShape} : LE_Interp ρ m M ↔ LE_Interp ρ' m M :=
  ⟨closed cl nofun, closed cl nofun⟩

/-- Change the valuation of a closed expression without discarding its
chosen constructor tree or recursive constant callbacks.  This internal
transport is noncomputable because the constant case uses the propositional
closure certificate returned by `Const.closed`. -/
noncomputable def LE_Interp.Witness.closed (cl : ClosedN M k)
    (hρ : ∀ i < k, ρ i = ρ' i)
    (H : LE_Interp.Witness ρ m M) : LE_Interp.Witness ρ' m M := by
  induction H generalizing k ρ' with
  | bot => exact .bot
  | sort hle => exact .sort hle
  | bvar hle => exact .bvar ((hρ _ cl).symm ▸ hle)
  | app hf ha hle ihf iha =>
    exact .app (ihf cl.1 hρ) (iha cl.2 hρ) hle
  | lam ha hdom hbody hle iha ihbody =>
    refine .lam (iha cl.1 hρ) hdom (fun x hx => ihbody x hx cl.2 ?_) hle
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact hρ i (Nat.lt_of_succ_lt_succ hi)
  | forallE hb hb' hdom hbody hle ihb ihb' ihbody =>
    refine .forallE (ihb cl.1 hρ) (ihb' cl.1 hρ) hdom
      (fun x hx => ihbody x hx cl.2 ?_) hle
    intro i hi
    cases i with
    | zero => rfl
    | succ i => exact hρ i (Nat.lt_of_succ_lt_succ hi)
  | const hreg hlen hle hty hA hC hR ihA ihR =>
    refine .const hreg hlen hle hty
      (ihA ((Params.henv.closedC hreg).mkInstS.mono (Nat.zero_le _)) hρ)
      hC.closed (fun m e hr => ?_)
    exact ihR m e hr.2 hr.1 nofun

/-- A closed witness is independent of its valuation. -/
noncomputable def LE_Interp.Witness.closedAt {M : SExpr} (cl : ClosedN M)
    (H : LE_Interp.Witness ρ m M) : LE_Interp.Witness ρ' m M :=
  H.closed cl nofun

theorem LE_Interp.Witness.closed_toInterp
    {ρ ρ' : Valuation} {m : TShape} {M : SExpr} {k : Nat}
    (cl : ClosedN M k)
    (hρ : ∀ i < k, ρ i = ρ' i)
    (H : LE_Interp.Witness ρ m M) :
    (H.closed cl hρ).toInterp = H.toInterp.closed cl hρ :=
  Subsingleton.elim _ _

/-- Change the valuation throughout a retained recursion tree for a closed
expression.  Constant callbacks acquire the closure certificate stored by
`Const.closed`; the recursive-result transport is consequently passed that
same certificate, ensuring it follows the exact transformed callback rather
than a freshly chosen interpretation. -/
theorem LE_Interp.Witness.RDeepChildren.closed
    {P : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop}
    (hP : ∀ {ρ ρ' : Valuation} {m : TShape} {M : SExpr} {k : Nat}
      (H : LE_Interp.Witness ρ m M)
      (cl : ClosedN M k) (hρ : ∀ i < k, ρ i = ρ' i),
      P H → P (H.closed cl hρ))
    {ρ ρ' : Valuation} {m : TShape} {M : SExpr} {k : Nat}
    {H : LE_Interp.Witness ρ m M}
    (children : H.RDeepChildren P)
    (cl : ClosedN M k) (hρ : ∀ i < k, ρ i = ρ' i) :
    (H.closed cl hρ).RDeepChildren P := by
  induction H generalizing k ρ' with
  | @bot ρ n M =>
    cases children
    cases M <;> exact .bot
  | sort hle =>
    cases children
    exact .sort
  | bvar hle =>
    cases children
    exact .bvar
  | app hf ha hle ihf iha =>
    cases children with
    | app cf ca => exact .app (ihf cf cl.1 hρ) (iha ca cl.2 hρ)
  | lam ha hdom hbody hle iha ihbody =>
    cases children with
    | lam ca cbody =>
      exact .lam (iha ca cl.1 hρ) (fun x hx =>
        ihbody x hx (cbody x hx) cl.2 (fun i hi => by
          cases i with
          | zero => rfl
          | succ i => exact hρ i (Nat.lt_of_succ_lt_succ hi)))
  | forallE hb hb' hdom hbody hle ihb ihb' ihbody =>
    cases children with
    | forallE cb cb' cbody =>
      exact .forallE (ihb cb cl.1 hρ) (ihb' cb' cl.1 hρ)
        (fun x hx => ihbody x hx (cbody x hx) cl.2 (fun i hi => by
          cases i with
          | zero => rfl
          | succ i => exact hρ i (Nat.lt_of_succ_lt_succ hi)))
  | const hreg hlen hle hty hA hC hR ihA ihR =>
    cases children with
    | const cA pR cR =>
      exact .const
        (ihA cA ((Params.henv.closedC hreg).mkInstS.mono
          (Nat.zero_le _)) hρ)
        (fun m e hr => hP (hR m e hr.2) hr.1 nofun (pR m e hr.2))
        (fun m e hr => ihR m e hr.2 (cR m e hr.2) hr.1 nofun)

/-- Remove one syntactic lift from a proof-relevant interpretation while
retaining its exact constructor tree.  The valuation equation is the same
one used by `LE_Interp.weak'_iff`; the constant case keeps the underlying
recursive callback and merely records the closed syntax wrapper introduced
by transport. -/
noncomputable def LE_Interp.Witness.unlift'
    (l : Lift) (hρ : ∀ i, ρ i = ρ' (l.liftVar i))
    (H : LE_Interp.Witness ρ' m (M.lift' l)) :
    LE_Interp.Witness ρ m M := by
  generalize eq : M.lift' l = M' at H
  induction H generalizing M ρ l with first
    | subst eq | cases M <;> cases eq
  | bot => exact .bot
  | sort hle => exact .sort hle
  | bvar hle => exact .bvar (hρ _ ▸ hle)
  | app hf ha hle ihf iha =>
    exact .app (ihf _ hρ rfl) (iha _ hρ rfl) hle
  | lam ha hdom hbody hle iha ihbody =>
    refine .lam (iha _ hρ rfl) hdom (fun y hy => ?_) hle
    exact ihbody y hy _
      (fun i => by cases i <;> simp [Valuation.push, hρ]) rfl
  | forallE hb hb' hdom hbody hle ihb ihb' ihbody =>
    refine .forallE (ihb _ hρ rfl) (ihb' _ hρ rfl) hdom
      (fun y hy => ?_) hle
    exact ihbody y hy _
      (fun i => by cases i <;> simp [Valuation.push, hρ]) rfl
  | const hreg hlen hle hty hA hC hR ihA ihR =>
    refine .const hreg hlen hle hty ?_ hC.closed ?_
    · exact ihA _ hρ <| (Params.henv.closedC hreg).mkInstS.lift'_eq .zero
    · rintro m A ⟨hclosed, hr⟩
      exact ihR _ _ hr _ hρ <| hclosed.lift'_eq .zero

/-- Add a syntactic lift to a proof-relevant interpretation without choosing
a fresh propositional derivation. -/
noncomputable def LE_Interp.Witness.lift'
    (l : Lift) (hρ : ∀ i, ρ i = ρ' (l.liftVar i))
    (H : LE_Interp.Witness ρ m M) :
    LE_Interp.Witness ρ' m (M.lift' l) := by
  induction H generalizing ρ' l with
  | bot => exact .bot
  | sort hle => exact .sort hle
  | bvar hle => exact .bvar (hρ _ ▸ hle)
  | app hf ha hle ihf iha =>
    exact .app (ihf l hρ) (iha l hρ) hle
  | lam ha hdom hbody hle iha ihbody =>
    refine .lam (iha l hρ) hdom (fun y hy => ?_) hle
    exact ihbody y hy l.cons fun i => by
      cases i <;> simp [Valuation.push, hρ]
  | forallE hb hb' hdom hbody hle ihb ihb' ihbody =>
    refine .forallE (ihb l hρ) (ihb' l hρ) hdom (fun y hy => ?_) hle
    exact ihbody y hy l.cons fun i => by
      cases i <;> simp [Valuation.push, hρ]
  | const hreg hlen hle hty hA hC hR _ _ =>
    refine .const hreg hlen hle hty
      (hA.closedAt (Params.henv.closedC hreg).mkInstS)
      hC.closed (fun m A hr => ?_)
    exact (hR m A hr.2).closedAt hr.1

/-- Syntactic lifting preserves a retained recursion tree.  Registered
constant children are closed, so their exact callbacks change valuation via
`Witness.closed`; the caller supplies precisely that recursive-result
transport and no proof-irrelevant witness is reselected. -/
theorem LE_Interp.Witness.RDeepChildren.lift'
    {P : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop}
    (hP : ∀ {ρ ρ' : Valuation} {m M k}
      (H : LE_Interp.Witness ρ m M)
      (cl : ClosedN M k) (hρ : ∀ i < k, ρ i = ρ' i),
      P H → P (H.closed cl hρ))
    {ρ ρ' : Valuation} {H : LE_Interp.Witness ρ m M}
    (children : H.RDeepChildren P)
    (l : Lift) (hρ : ∀ i, ρ i = ρ' (l.liftVar i)) :
    (H.lift' l hρ).RDeepChildren P := by
  induction H generalizing ρ' l with
  | bot =>
    cases children
    exact .bot
  | bvar hle =>
    cases children
    exact .bvar
  | sort hle =>
    cases children
    exact .sort
  | app hf ha hle ihf iha =>
    cases children with
    | app cf ca => exact .app (ihf cf l hρ) (iha ca l hρ)
  | lam ha hdom hbody hle iha ihbody =>
    cases children with
    | lam ca cbody =>
      exact .lam (iha ca l hρ) (fun x hx =>
        ihbody x hx (cbody x hx) l.cons (fun i => by
          cases i <;> simp [Valuation.push, hρ]))
  | forallE hb hb' hdom hbody hle ihb ihb' ihbody =>
    cases children with
    | forallE cb cb' cbody =>
      exact .forallE (ihb cb l hρ) (ihb' cb' l hρ)
        (fun x hx => ihbody x hx (cbody x hx) l.cons (fun i => by
          cases i <;> simp [Valuation.push, hρ]))
  | const hreg hlen hle hty hA hC hR ihA ihR =>
    cases children with
    | const cA pR cR =>
      exact .const
        (cA.closed hP (Params.henv.closedC hreg).mkInstS nofun)
        (fun m e hr => hP (hR m e hr.2) hr.1 nofun (pR m e hr.2))
        (fun m e hr => (cR m e hr.2).closed hP hr.1 nofun)

/-- Remove the standard one-variable weakening from a witness. -/
noncomputable def LE_Interp.Witness.unweak
    (H : LE_Interp.Witness (ρ.push x) m M.lift) :
    LE_Interp.Witness ρ m M :=
  H.unlift' (.skip .refl) (fun _ => rfl)

/-- Weaken a witness by one variable while preserving its recursive
provenance. -/
noncomputable def LE_Interp.Witness.weak
    (H : LE_Interp.Witness ρ m M) :
    LE_Interp.Witness (ρ.push x) m M.lift :=
  H.lift' (.skip .refl) (fun _ => rfl)

/-- Standard one-variable weakening preserves every exact recursive
callback. -/
theorem LE_Interp.Witness.RDeepChildren.weak
    {P : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop}
    (hP : ∀ {ρ ρ' : Valuation} {m M k}
      (H : LE_Interp.Witness ρ m M)
      (cl : ClosedN M k) (hρ : ∀ i < k, ρ i = ρ' i),
      P H → P (H.closed cl hρ))
    {H : LE_Interp.Witness ρ m M}
    (children : H.RDeepChildren P) :
    (H.weak (x := x)).RDeepChildren P := by
  exact children.lift' hP (.skip .refl) (fun _ => rfl)

/-- Substitute a proof-relevant interpretation forward while retaining the
exact constructor choices and recursive constant callbacks.  Under a binder,
the substitution witnesses are weakened in lockstep with `Subst.lift`. -/
noncomputable def LE_Interp.Witness.subst
    (H : LE_Interp.Witness ρ' m M)
    (hσ : ∀ i, LE_Interp.Witness ρ (ρ' i) (σ i)) :
    LE_Interp.Witness ρ m (M.subst σ) := by
  induction H generalizing ρ σ with
  | bot => exact .bot
  | bvar hle => exact (hσ _).mono hle
  | sort hle => exact .sort hle
  | app hf ha hle ihf iha =>
    exact .app (ihf hσ) (iha hσ) hle
  | lam ha hdom hbody hle iha ihbody =>
    refine .lam (iha hσ) hdom (fun x hx => ?_) hle
    exact ihbody x hx fun
      | 0 => .bvar .rfl
      | i + 1 => (hσ i).weak
  | forallE hb hb' hdom hbody hle ihb ihb' ihbody =>
    refine .forallE (ihb hσ) (ihb' hσ) hdom (fun x hx => ?_) hle
    exact ihbody x hx fun
      | 0 => .bvar .rfl
      | i + 1 => (hσ i).weak
  | const hreg hlen hle hty hA hC hR ihA ihR =>
    refine .const hreg hlen hle hty
      (hA.closedAt (Params.henv.closedC hreg).mkInstS)
      hC.closed (fun m e hr => ?_)
    exact (hR m e hr.2).closedAt hr.1

/-- Substitute exact witnesses throughout a retained recursion tree.
Variable nodes reuse the supplied tree, while registered constant callbacks
use their evaluator-provided closure certificate. -/
theorem LE_Interp.Witness.RDeepChildren.subst
    {P : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop}
    (hP : ∀ {ρ ρ' : Valuation} {m M k}
      (H : LE_Interp.Witness ρ m M)
      (cl : ClosedN M k) (hρ : ∀ i < k, ρ i = ρ' i),
      P H → P (H.closed cl hρ))
    {ρ ρ' : Valuation} {σ : Subst}
    {H : LE_Interp.Witness ρ' m M}
    (children : H.RDeepChildren P)
    (hσ : ∀ i, LE_Interp.Witness ρ (ρ' i) (σ i))
    (cσ : ∀ i, (hσ i).RDeepChildren P) :
    (H.subst hσ).RDeepChildren P := by
  induction H generalizing ρ σ with
  | bot =>
    cases children
    exact .bot
  | bvar hle =>
    cases children
    exact (cσ _).mono hle
  | sort hle =>
    cases children
    exact .sort
  | app hf ha hle ihf iha =>
    cases children with
    | app cf ca => exact .app (ihf cf hσ cσ) (iha ca hσ cσ)
  | lam ha hdom hbody hle iha ihbody =>
    cases children with
    | lam ca cbody =>
      refine .lam (iha ca hσ cσ) (fun x hx => ?_)
      exact ihbody x hx (cbody x hx) (ρ := ρ.push x.T)
        (σ := σ.lift)
        (fun | 0 => .bvar .rfl | i + 1 => (hσ i).weak)
        (fun | 0 => .bvar | i + 1 => (cσ i).weak hP)
  | forallE hb hb' hdom hbody hle ihb ihb' ihbody =>
    cases children with
    | forallE cb cb' cbody =>
      refine .forallE (ihb cb hσ cσ) (ihb' cb' hσ cσ)
        (fun x hx => ?_)
      exact ihbody x hx (cbody x hx) (ρ := ρ.push x.T)
        (σ := σ.lift)
        (fun | 0 => .bvar .rfl | i + 1 => (hσ i).weak)
        (fun | 0 => .bvar | i + 1 => (cσ i).weak hP)
  | const hreg hlen hle hty hA hC hR ihA ihR =>
    cases children with
    | const cA pR cR =>
      exact .const
        (cA.closed hP (Params.henv.closedC hreg).mkInstS nofun)
        (fun m e hr => hP (hR m e hr.2) hr.1 nofun (pR m e hr.2))
        (fun m e hr => (cR m e hr.2).closed hP hr.1 nofun)

/-- Instantiate the leading variable of a proof-relevant witness without
forgetting the witness tree on either the body or the argument. -/
noncomputable def LE_Interp.Witness.inst
    (H : LE_Interp.Witness (ρ.push a) m F)
    (hA : LE_Interp.Witness ρ a A) :
    LE_Interp.Witness ρ m (F.inst A) :=
  H.subst fun
    | 0 => hA
    | _ + 1 => .bvar .rfl

/-- Leading-variable instantiation combines the retained body and argument
trees without choosing a new semantic derivation. -/
theorem LE_Interp.Witness.RDeepChildren.inst
    {P : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop}
    (hP : ∀ {ρ ρ' : Valuation} {m M k}
      (H : LE_Interp.Witness ρ m M)
      (cl : ClosedN M k) (hρ : ∀ i < k, ρ i = ρ' i),
      P H → P (H.closed cl hρ))
    {H : LE_Interp.Witness (ρ.push a) m F}
    (children : H.RDeepChildren P)
    {hA : LE_Interp.Witness ρ a A}
    (childrenA : hA.RDeepChildren P) :
    (H.inst hA).RDeepChildren P := by
  let hσ : ∀ i, LE_Interp.Witness ρ ((ρ.push a) i) ((Subst.one A) i)
    | 0 => hA
    | _ + 1 => .bvar .rfl
  have cσ : ∀ i, (hσ i).RDeepChildren P := by
    intro i
    cases i with
    | zero => exact childrenA
    | succ i => exact .bvar
  exact children.subst hP hσ cσ

theorem LE_Interp.weak'_iff (l : Lift) (h : ∀ i, ρ i = ρ' (l.liftVar i)) :
    LE_Interp ρ' m (M.lift' l) ↔ LE_Interp ρ m M := by
  refine ⟨fun H => ?_, fun H => ?_⟩
  · generalize eq : M.lift' l = M' at H
    induction H generalizing M ρ l with first
      | subst eq | cases M <;> cases eq
    | bot => exact .bot
    | sort h1 => exact .sort h1
    | bvar h1 => exact .bvar (h _ ▸ h1)
    | app _ _ h1 ih_f ih_a => exact .app (ih_f _ h rfl) (ih_a _ h rfl) h1
    | lam _ hdom _ h1 ih_a ih_body =>
      refine .lam (ih_a _ h rfl) hdom (fun y hy => ?_) h1
      exact ih_body y hy _ (fun i => by cases i <;> simp [Valuation.push, h]) rfl
    | forallE _ _ hdom _ h1 ih_b ih_b' ih_body =>
      refine .forallE (ih_b _ h rfl) (ih_b' _ h rfl) hdom (fun y hy => ?_) h1
      exact ih_body y hy _ (fun i => by cases i <;> simp [Valuation.push, h]) rfl
    | const h1 h2 h3 h4 _ h6 _ ih1 ih2 =>
      refine .const h1 h2 h3 h4 ?_ h6.closed ?_
      · exact ih1 _ h <| (Params.henv.closedC h1).mkInstS.lift'_eq .zero
      · rintro m A ⟨a1, a2⟩; exact ih2 _ _ a2 _ h <| a1.lift'_eq .zero
  · induction H generalizing ρ' l with
    | bot => exact .bot
    | sort h1 => exact .sort h1
    | bvar h1 => exact .bvar (h _ ▸ h1)
    | app _ _ h1 ih_f ih_a => exact .app (ih_f l h) (ih_a l h) h1
    | lam _ hdom _ h1 ih_a ih_body =>
      refine .lam (ih_a l h) hdom (fun y hy => ?_) h1
      exact ih_body y hy l.cons fun i => by cases i <;> simp [Valuation.push, h]
    | forallE _ _ hdom _ h1 ih_b ih_b' ih_body =>
      refine .forallE (ih_b l h) (ih_b' l h) hdom (fun y hy => ?_) h1
      exact ih_body y hy l.cons fun i => by cases i <;> simp [Valuation.push, h]
    | const h1 h2 h3 h4 _ h6 _ ih1 ih2 =>
      refine .const h1 h2 h3 h4 ?_ h6.closed ?_
      · exact (Params.henv.closedC h1).mkInstS.lift'_eq .zero ▸ ih1 _ h
      · rintro m A ⟨a1, a2⟩; exact a1.lift'_eq .zero ▸ ih2 _ _ a2 _ h

theorem LE_Interp.weak_iff : LE_Interp (ρ.push x) m M.lift ↔ LE_Interp ρ m M :=
  LE_Interp.weak'_iff (.skip .refl) (fun _ => rfl)

theorem LE_Interp.weak (H : LE_Interp ρ m M) : LE_Interp (ρ.push x) m M.lift :=
  weak_iff.2 H

theorem LE_Interp.Witness.unlift'_toInterp
    {ρ ρ' : Valuation} {m : TShape} {M : SExpr}
    (l : Lift) (hρ : ∀ i, ρ i = ρ' (l.liftVar i))
    (H : LE_Interp.Witness ρ' m (M.lift' l)) :
    (H.unlift' l hρ).toInterp =
      (LE_Interp.weak'_iff l hρ).1 H.toInterp :=
  Subsingleton.elim _ _

theorem LE_Interp.Witness.lift'_toInterp
    {ρ ρ' : Valuation} {m : TShape} {M : SExpr}
    (l : Lift) (hρ : ∀ i, ρ i = ρ' (l.liftVar i))
    (H : LE_Interp.Witness ρ m M) :
    (H.lift' l hρ).toInterp =
      (LE_Interp.weak'_iff l hρ).2 H.toInterp :=
  Subsingleton.elim _ _

theorem LE_Interp.Const.compat_mismatch {rargs1 rargs2 : List (WShape n)} {m : TShape}
    (h_len : rargs2.length < rargs1.length) (H1 : Const c ls R rargs1 m)
    (H2 : Params.classify c = some (.ctor rargs2.length) ∨
      Params.classify c = some (.indTy rargs2.length) ∨
      ∃ p r m, Params.Pat p r ∧ Matches p c rargs2 m) :
    m ≤ .bot := by
  induction H1 with
  | bot => exact TShape.bot_eqv.1
  | @lam f _ _ he m_le ih =>
    by_cases hf : f.NonZero
    · obtain ⟨⟨s, t⟩, hxy, hn⟩ := WShapeFun.NonZero.iff.1 hf
      have := ih _ t (WShapeFun.mem_val hxy) (by simp; omega)
      cases hn <| WShape.LE.T_iff.1 <| this.trans TShape.bot_eqv.2
    · have := WShape.lam'_le_lam'.2 <| NonZero.not_iff.1 hf
      exact m_le.trans <| (WShape.lam'_bot ▸ this).T.trans TShape.bot_eqv.1
  | ctor hct m_le_ctor =>
    obtain hct' | hct' | ⟨p, r, m, hP, hM⟩ := H2
    · generalize rargs2.length = n at hct' h_len
      cases hct.symm.trans hct'; cases Nat.lt_irrefl _ h_len
    · cases hct.symm.trans hct'
    · cases hct.symm.trans <| pat_arity hP hM.arity
  | indTy hct _ =>
    obtain hct' | hct' | ⟨_, _, _, hP', hM'⟩ := H2
    · cases hct.symm.trans hct'
    · generalize rargs2.length = n at hct' h_len
      cases hct.symm.trans hct'; cases Nat.lt_irrefl _ h_len
    · cases hct.symm.trans <| pat_arity hP' hM'.arity
  | pat hP hM hR =>
    obtain hct' | hct' | ⟨_, _, _, hP', hM'⟩ := H2
    · cases hct'.symm.trans <| pat_arity hP hM.arity
    · cases hct'.symm.trans <| pat_arity hP hM.arity
    · have := pat_arity hP' hM'.arity
      generalize rargs2.length = n at h_len this
      cases (pat_arity hP hM.arity).symm.trans this; cases Nat.lt_irrefl _ h_len

theorem LE_Interp.Const.compat_join
    {rargs1 rargs2} (hc : List.Forall₂ WShape.Compat rargs1 rargs2)
    (H1 : Const (n := n) c ls R rargs1 m) (H2 : Const c ls R' rargs2 m')
    (hR_bot : ∀ {n} {e}, R (WShape.T (n := n) .bot) e)
    (hR'_bot : ∀ {n} {e}, R' (WShape.T (n := n) .bot) e)
    (hR₃_mono : ∀ {a a' A}, a ≤ a' → R₃ a' A → R₃ a A)
    (hRR : ∀ {m₁ m₂ A}, R m₁ A → R' m₂ A → m₁.Compat m₂ ∧ R₃ (m₁.join m₂) A) :
    m.Compat m' ∧ Const c ls R₃ (rargs1.zipWith WShape.join rargs2) (m.join m') := by
  have hRR_c : ∀ {m₁ m₂ A}, R m₁ A → R' m₂ A → m₁.Compat m₂ := fun h1 h2 => (hRR h1 h2).1
  have bot_r {n n' m rargs rargs2} (H : Const (n := n) c ls R rargs m)
      (hc : List.Forall₂ WShape.Compat rargs rargs2) :
      TShape.Compat m (WShape.bot (n := n')).T ∧
      Const c ls R₃ (List.zipWith WShape.join rargs rargs2) (m.join (WShape.bot (n := n')).T) := by
    refine have hbc := .bot_r'; ⟨hbc, .mono ?_ (fun h1 h2 => ?_) (H.mono_l ?_)⟩
    · exact (TShape.Join.mk hbc _).2 ⟨.rfl, TShape.bot_le'⟩
    · have ⟨a1, a2⟩ := hRR h2 (hR'_bot (n := 0))
      exact hR₃_mono (h1.trans (TShape.Join.mk a1).le.1) a2
    · exact (WShape.le_zipWith_join hc).1
  induction H1 generalizing rargs2 m' with
  | bot =>
    refine have hbc := .bot_l'; ⟨hbc, .mono ?_ (fun h1 h2 => ?_) (H2.mono_l ?_)⟩
    · exact (TShape.Join.mk hbc _).2 ⟨TShape.bot_le', .rfl⟩
    · have ⟨a1, a2⟩ := hRR (hR_bot (n := 0)) h2
      exact hR₃_mono (h1.trans (TShape.Join.mk a1).le.2) a2
    · exact (WShape.le_zipWith_join hc).2
  | @lam f rargs m he m_le ih =>
    cases H2 with
    | bot => exact bot_r (.lam he m_le) hc
    | @lam f' _ k' he' m_le' =>
      have hfc : WShapeFun.Compat f f' := by
        simp only [WShapeFun.Compat.def, Prod.forall]
        intro x y h1 x' y' h2 hc'
        exact WShape.Compat.T_iff.2 (ih _ _ h1 (hc.cons hc') (he' _ _ h2)).1
      refine have hmc := .mono m_le m_le' (WShape.Compat.lam'_lam' hfc).T; ⟨hmc, ?_⟩
      have hJ_lam : WShape.Join (.lam' f) (.lam' f') (.lam' (f.join f')) :=
        WShape.Join.lam'.2 (.mk hfc)
      refine .lam (f := f.join f') ?_ <|
        (TShape.Join.mk hmc _).2 ⟨m_le.trans hJ_lam.le.1.T, m_le'.trans hJ_lam.le.2.T⟩
      simp only [WShapeFun.mem_join hfc]
      rintro _ _ ⟨⟨x, y⟩, h1, ⟨x', y'⟩, h2, hc', rfl, rfl⟩; dsimp only at *
      have ⟨x₁, le, a1⟩ := f.app_eq (x.join x')
      have ⟨x₂, le', a2⟩ := f'.app_eq (x.join x')
      have hxc := hfc.app_l (x.join x')
      have hxc' := WShape.Compat.iff.2 ⟨_, le, le'⟩
      have ⟨hyc, ih⟩ := ih _ _ a1 (hc.cons hxc') (he' _ _ a2)
      rw [WShape.T_join] at ih
      exact ih.mono_l <| .cons ((WShape.Join.mk hxc' _).2 ⟨le, le'⟩) <| .rfl fun _ _ => .rfl
    | ctor hct' m_le' =>
      unfold WShape.lam' at m_le; split at m_le <;> rename_i hf
      · obtain ⟨⟨s, t⟩, hxy, hn⟩ := WShapeFun.NonZero.iff.1 hf
        have h_const := he s t (f.mem_val hxy)
        have hL : rargs.length = rargs2.length := hc.length_eq
        refine hn (WShape.LE.T_iff.1 <| .trans ?_ TShape.bot_eqv.2) |>.elim
        exact compat_mismatch (rargs2 := rargs2) (by simp; omega) h_const <| .inl hct'
      · refine have hmc := .mono (m_le.trans TShape.bot_eqv.1) .rfl .bot_l; ⟨hmc, ?_⟩
        refine .ctor ?_ (List.reverse_zipWith hc.length_eq ▸ (TShape.Join.mk hmc _).2 ⟨?_, ?_⟩)
        · rw [List.length_zipWith, hc.length_eq, Nat.min_self, hct']
        · exact m_le.trans TShape.bot_le'
        · refine m_le'.trans (WShape.ctor'_le_ctor' ?_).T
          exact (WShape.le_zipWith_join (List.Forall₂.reverse.2 hc)).2
    | pat hP hM hR =>
      unfold WShape.lam' at m_le; split at m_le <;> rename_i hf
      · obtain ⟨⟨s, t⟩, hxy, hn⟩ := WShapeFun.NonZero.iff.1 hf
        have h_const := he _ _ (f.mem_val hxy)
        have hL : rargs.length = rargs2.length := hc.length_eq
        refine hn (WShape.LE.T_iff.1 <| .trans ?_ TShape.bot_eqv.2) |>.elim
        exact compat_mismatch (by simp; omega) h_const <| .inr <| .inr ⟨_, _, _, hP, hM⟩
      · refine have hmc := .mono (m_le.trans TShape.bot_eqv.1) .rfl .bot_l; ⟨hmc, ?_⟩
        have h_le : m.join m' ≤ m' := (TShape.Join.mk hmc _).2 ⟨m_le.trans TShape.bot_le', .rfl⟩
        refine .mono h_le (fun le hr => ?_) <| .mono_l (WShape.le_zipWith_join hc).2 (.pat hP hM hR)
        have hc := hRR (hR_bot (n := 0)) hr
        exact hR₃_mono (le.trans (TShape.Join.mk hc.1).le.2) hc.2
    | indTy hct' m_le' =>
      unfold WShape.lam' at m_le; split at m_le <;> rename_i hf
      · obtain ⟨⟨s, t⟩, hxy, hn⟩ := WShapeFun.NonZero.iff.1 hf
        have h_const := he _ _ (f.mem_val hxy)
        have hL : rargs.length = rargs2.length := hc.length_eq
        refine hn (WShape.LE.T_iff.1 <| .trans ?_ TShape.bot_eqv.2) |>.elim
        exact compat_mismatch (by simp; omega) h_const <| .inr <| .inl hct'
      · refine have hmc := .mono (m_le.trans TShape.bot_eqv.1) .rfl .bot_l; ⟨hmc, ?_⟩
        have h_le : m.join m' ≤ m' := (TShape.Join.mk hmc _).2 ⟨m_le.trans TShape.bot_le', .rfl⟩
        exact .mono h_le hR₃_mono <| .mono_l (WShape.le_zipWith_join hc).2 (.indTy hct' m_le')
  | @ctor m rargs hct m_le =>
    cases H2 with
    | bot => exact bot_r (.ctor hct m_le) hc
    | lam he' m_le' =>
      unfold WShape.lam' at m_le'; split at m_le' <;> rename_i hf'
      · obtain ⟨⟨s, t⟩, hxy, hn⟩ := WShapeFun.NonZero.iff.1 hf'
        refine hn (WShape.LE.T_iff.1 <| .trans ?_ TShape.bot_eqv.2) |>.elim
        have h_const := he' _ _ (WShapeFun.mem_val hxy)
        have hL := hc.length_eq
        exact compat_mismatch (by simp; omega) h_const (.inl hct)
      · refine have hmc := .mono .rfl (m_le'.trans TShape.bot_eqv.1) .bot_r; ⟨hmc, ?_⟩
        refine .ctor ?_ (List.reverse_zipWith hc.length_eq ▸ (TShape.Join.mk hmc _).2 ⟨?_, ?_⟩)
        · rw [List.length_zipWith, ← hc.length_eq, Nat.min_self, hct]
        · refine m_le.trans (WShape.ctor'_le_ctor' ?_).T
          exact (WShape.le_zipWith_join (List.Forall₂.reverse.2 hc)).1
        · exact m_le'.trans TShape.bot_le'
    | ctor _ m_le' =>
      refine have hc_rev := List.Forall₂.reverse.2 hc
        have hc' := (WShape.Compat.ctor'_ctor' hc_rev).T.mono m_le m_le'; ⟨hc', ?_⟩
      refine .ctor ?_ (List.reverse_zipWith hc.length_eq ▸ (TShape.Join.mk hc' _).2 ⟨?_, ?_⟩)
      · rw [List.length_zipWith, ← hc.length_eq, Nat.min_self, hct]
      · exact m_le.trans (WShape.ctor'_le_ctor' (WShape.le_zipWith_join hc_rev).1).T
      · exact m_le'.trans (WShape.ctor'_le_ctor' (WShape.le_zipWith_join hc_rev).2).T
    | pat hP hM hR => cases hct.symm.trans <| pat_arity hP hM.arity
    | indTy hct' _ => cases hct.symm.trans hct'
  | @indTy _ rargs hct m_le =>
    cases H2 with
    | bot => exact bot_r (.indTy hct m_le) hc
    | lam he' m_le' =>
      unfold WShape.lam' at m_le'; split at m_le' <;> rename_i hf'
      · obtain ⟨⟨s, t⟩, hxy, hn⟩ := WShapeFun.NonZero.iff.1 hf'
        refine hn (WShape.LE.T_iff.1 <| .trans ?_ TShape.bot_eqv.2) |>.elim
        have h_const := he' _ _ (WShapeFun.mem_val hxy)
        have hL := hc.length_eq
        exact compat_mismatch (rargs2 := rargs) (by simp; omega) h_const <| .inr <| .inl hct
      · refine have hmc := .mono .rfl (m_le'.trans TShape.bot_eqv.1) .bot_r; ⟨hmc, ?_⟩
        refine .indTy ?_ ((TShape.Join.mk hmc _).2 ⟨m_le, m_le'.trans TShape.bot_le'⟩)
        rw [List.length_zipWith, ← hc.length_eq, Nat.min_self, hct]
    | ctor hct' m_le' => cases hct.symm.trans hct'
    | pat hP hM hR => cases hct.symm.trans <| pat_arity hP hM.arity
    | indTy hct' m_le' =>
      refine have hc' := TShape.Compat.def'.2 ⟨_, m_le, m_le'⟩; ⟨hc', ?_⟩
      refine .indTy ?_ ((TShape.Join.mk hc' _).2 ⟨m_le, m_le'⟩)
      rw [List.length_zipWith, ← hc.length_eq, Nat.min_self, hct]
  | @pat _ _ rargs _ m hP hM hR =>
    cases H2 with
    | bot => exact bot_r (.pat hP hM hR) hc
    | lam he' m_le' =>
      unfold WShape.lam' at m_le'; split at m_le' <;> rename_i hf'
      · obtain ⟨⟨s, t⟩, hxy, hn⟩ := WShapeFun.NonZero.iff.1 hf'
        refine hn (WShape.LE.T_iff.1 <| .trans ?_ TShape.bot_eqv.2) |>.elim
        have h_const := he' _ _ (WShapeFun.mem_val hxy)
        have hL := hc.length_eq
        exact compat_mismatch (by simp; omega) h_const <| .inr <| .inr ⟨_, _, _, hP, hM⟩
      · refine have hmc := .mono .rfl (m_le'.trans TShape.bot_eqv.1) .bot_r; ⟨hmc, ?_⟩
        have h_le : m.join m' ≤ m := (TShape.Join.mk hmc _).2 ⟨.rfl, m_le'.trans TShape.bot_le'⟩
        refine .mono h_le (fun le hr => ?_) <| .mono_l (WShape.le_zipWith_join hc).1 (.pat hP hM hR)
        have hc := hRR hr (hR'_bot (n := 0))
        exact hR₃_mono (le.trans (TShape.Join.mk hc.1).le.1) hc.2
    | ctor hct' => cases hct'.symm.trans <| pat_arity hP hM.arity
    | indTy hct' _ => cases hct'.symm.trans <| pat_arity hP hM.arity
    | pat hP' hM' hR' =>
      have ⟨_, hi⟩ := hM.matches_inter hc (Params.pat_wf hP) hM' (Params.pat_wf hP')
      obtain ⟨rfl, -, ⟨⟩⟩ := Params.pat_uniq hP' hP .refl hi
      have ⟨hc, hj⟩ := hM.compat_join hc hM' (Params.pat_wf hP)
      have ⟨a1, a2⟩ := hR.compat_join hc hR_bot hR'_bot hRR hR₃_mono hR'
      exact ⟨a1, .pat hP hj a2⟩

theorem LE_Interp.compat_join {m₁ m₂ : TShape}
    (hρ : ρ'.LE ρ) (H1 : LE_Interp ρ' m₁ M) (H2 : LE_Interp ρ m₂ M) :
    m₁.Compat m₂ ∧ LE_Interp ρ (m₁.join m₂) M := by
  have mk {m₁ m₂ m ρ M} (H1 : m₁ ≤ m) (H2 : m₂ ≤ m) (H : LE_Interp ρ m M) :
      m₁.Compat m₂ ∧ LE_Interp ρ (m₁.join m₂) M :=
    have := TShape.Compat.def'.2 ⟨_, H1, H2⟩
    ⟨this, H.mono ((TShape.Join.mk this _).2 ⟨H1, H2⟩)⟩
  have bot_r {m₁ n₂ ρ' ρ M} (hρ : ρ'.LE ρ) (H : LE_Interp ρ' m₁ M) :
      m₁.Compat (WShape.bot (n := n₂)).T ∧ LE_Interp ρ (m₁.join (WShape.bot (n := n₂)).T) M :=
    mk .rfl TShape.bot_le' (H.mono_l hρ)
  induction H1 generalizing ρ m₂ with
  | bot => exact mk TShape.bot_le' .rfl H2
  | sort h1 =>
    cases H2 with | bot => exact bot_r hρ (.sort h1) | sort h2
    exact mk h1 (h2.trans TShape.sort_eqv.2) (.sort .rfl)
  | bvar h1 =>
    cases H2 with | bot => exact bot_r hρ (.bvar h1) | bvar h2
    exact mk (h1.trans (hρ _)) h2 .bvar'
  | app hf ha h1 ih_f ih_a =>
    cases H2 with | bot => exact bot_r hρ (.app hf ha h1) | app hf' ha' h1'
    have ⟨cf, jf⟩ := ih_f hρ hf'
    have ⟨ca, ja⟩ := ih_a hρ ha'
    have hf := (TShape.Join.mk cf).le
    have ha := (TShape.Join.mk ca).le
    refine have le' := Nat.add_max_add_right .. ▸ Nat.le_refl _; mk ?_ ?_ ((jf.lift le').app' ja)
    · exact h1.trans <| TShape.app_mono (hf.1.trans (TShape.lift_eqv le').2) ha.1
    · exact h1'.trans <| TShape.app_mono (hf.2.trans (TShape.lift_eqv le').2) ha.2
  | lam ha hdom he h1 ih_a ih_f =>
    cases H2 with | bot => exact bot_r hρ (.lam ha hdom he h1) | lam ha' hdom' he' h1'
    rename_i ρ' n₁ a₁ A f₁ F m₁ n₂ a₂ f₂
    have ⟨ca, ia⟩ := ih_a hρ ha'
    have hC {x₁ y₁ x₂ y₂} (h1 : (x₁, y₁) ∈ f₁) (h2 : (x₂, y₂) ∈ f₂) (hc : x₁.T.Compat x₂.T) :
        y₁.T.Compat y₂.T ∧ LE_Interp (ρ.push (x₁.T.join x₂.T)) (y₁.T.join y₂.T) F := by
      have ⟨j1, j2⟩ := (TShape.Join.mk hc).le
      have ⟨x'₁, hx1_le, hx1, happ1⟩ := WShape.HasDom.iff.1 hdom x₁
      have ⟨x'₂, hx2_le, hx2, happ2⟩ := WShape.HasDom.iff.1 hdom' x₂
      have hi1 := (he x'₁ hx1).mono (WShape.LE.T happ1)
        |>.mono_l (Valuation.LE.push.2 ⟨hρ, hx1_le.T.trans j1⟩)
      have hi2 := (he' x'₂ hx2).mono (WShape.LE.T happ2)
        |>.mono_l (Valuation.LE.push.2 ⟨.rfl, hx2_le.T.trans j2⟩)
      have ⟨hc', hle'⟩ := ih_f x'₁ hx1 (Valuation.LE.push.2 ⟨hρ, hx1_le.T.trans j1⟩) hi2
      refine mk ?_ ?_ hle'
      · exact (WShapeFun.app_of_mem h1).2.T.trans happ1.T |>.trans (TShape.Join.mk hc').le.1
      · exact (WShapeFun.app_of_mem h2).2.T.trans (TShape.Join.mk hc').le.2
    have le₁ := Nat.le_max_left n₁ n₂; have le₂ := Nat.le_max_right n₁ n₂
    have cf : WShapeFun.Compat (f₁.lift (max n₁ n₂)) (f₂.lift (max n₁ n₂)) := by
      simp only [WShapeFun.Compat.def, Prod.forall, le₂, WShapeFun.mem_lift, le₁]
      rintro _ _ ⟨x₁, y₁, h1, rfl, rfl⟩ _ _ ⟨x₂, y₂, h2, rfl, rfl⟩ hc; exact (hC h1 h2 hc).1
    have jf := WShapeFun.Join.mk cf
    have hdom := (WShape.HasDom.lift le₁).2 hdom
    have hdom' := (WShape.HasDom.lift le₂).2 hdom'
    have ca_w : WShape.Compat (a₁.lift _) (a₂.lift _) := (TShape.Compat.def le₁ le₂).1 ca
    refine mk (h1.trans ?_) (h1'.trans ?_) <| .lam' ia (hdom.join cf ca_w hdom') fun x hx => ?_
    · exact (TShape.LE.lift_l (Nat.succ_le_succ le₁)).2 <|
        WShape.lift_lam' le₁ ▸ WShape.lam'_le_lam'.2 jf.le.1
    · exact (TShape.LE.lift_l (Nat.succ_le_succ le₂)).2 <|
        WShape.lift_lam' le₂ ▸ WShape.lam'_le_lam'.2 jf.le.2
    have ⟨x₁', a1, a2'⟩ := WShapeFun.app_eq (f₁.lift _) x
    have ⟨x₂', b1, b2'⟩ := WShapeFun.app_eq (f₂.lift _) x
    have ⟨ox₁, oy₁, hm₁, hx₁eq, hy₁eq⟩ := (WShapeFun.mem_lift le₁).1 a2'
    have ⟨ox₂, oy₂, hm₂, hx₂eq, hy₂eq⟩ := (WShapeFun.mem_lift le₂).1 b2'
    have a1' : ox₁.T ≤ x.T := ((TShape.LE.lift_l le₁).2 .rfl).trans (hx₁eq ▸ a1).T
    have b1' : ox₂.T ≤ x.T := ((TShape.LE.lift_l le₂).2 .rfl).trans (hx₂eq ▸ b1).T
    have hc := TShape.Compat.def'.2 ⟨x.T, a1', b1'⟩
    have ⟨_, hj⟩ := hC hm₁ hm₂ hc
    refine hj.mono_l (Valuation.LE.push.2 ⟨.rfl, (TShape.Join.mk hc x.T).2 ⟨a1', b1'⟩⟩) |>.mono ?_
    have ja := hy₁eq ▸ hy₂eq ▸ jf.app_l x
    have oy_c := WShape.Compat.iff.2 ⟨_, ja.le.1, ja.le.2⟩
    exact (ja _).2 (WShape.Join.mk oy_c).le |>.T
  | forallE hb ha hdom he h1 ih_b ih_a ih_f =>
    cases H2 with
    | bot => exact bot_r hρ (.forallE hb ha hdom he h1) | forallE hb2 ha2 hdom2 he2 h12
    rename_i ρ' n₁ b₁ B b₁' f₁ F m₁ n₂ b₂ b₂' f₂
    have ⟨cb, ib⟩ := ih_b hρ hb2
    have ⟨ca, ia⟩ := ih_a hρ ha2
    have hC {x₁ y₁ x₂ y₂} (h1 : (x₁, y₁) ∈ f₁) (h2 : (x₂, y₂) ∈ f₂) (hc : x₁.T.Compat x₂.T) :
        y₁.T.Compat y₂.T ∧ LE_Interp (ρ.push (x₁.T.join x₂.T)) (y₁.T.join y₂.T) F := by
      have ⟨j1, j2⟩ := (TShape.Join.mk hc).le
      have ⟨x'₁, hx1_le, hx1, happ1⟩ := WShape.HasDom.iff.1 hdom x₁
      have ⟨x'₂, hx2_le, hx2, happ2⟩ := WShape.HasDom.iff.1 hdom2 x₂
      have hi1 := (he x'₁ hx1).mono (WShape.LE.T happ1)
        |>.mono_l (Valuation.LE.push.2 ⟨hρ, hx1_le.T.trans j1⟩)
      have hi2 := (he2 x'₂ hx2).mono (WShape.LE.T happ2)
        |>.mono_l (Valuation.LE.push.2 ⟨.rfl, hx2_le.T.trans j2⟩)
      have ⟨hc', hle'⟩ := ih_f x'₁ hx1 (Valuation.LE.push.2 ⟨hρ, hx1_le.T.trans j1⟩) hi2
      exact mk ((WShapeFun.app_of_mem h1).2.T.trans happ1.T |>.trans (TShape.Join.mk hc').le.1)
        ((WShapeFun.app_of_mem h2).2.T.trans (TShape.Join.mk hc').le.2) hle'
    have le₁ := Nat.le_max_left n₁ n₂; have le₂ := Nat.le_max_right n₁ n₂
    have cf : (f₁.lift (max n₁ n₂)).Compat (f₂.lift (max n₁ n₂)) := by
      simp only [WShapeFun.Compat.def, Prod.forall, le₂, WShapeFun.mem_lift, le₁]
      rintro _ _ ⟨x₁, y₁, h1, rfl, rfl⟩ _ _ ⟨x₂, y₂, h2, rfl, rfl⟩ hc; exact (hC h1 h2 hc).1
    have cb_w := (TShape.Compat.def le₁ le₂).1 cb
    have jb := WShape.Join.mk cb_w; have jf := WShapeFun.Join.mk cf
    have hdom := (WShape.HasDom.lift le₁).2 hdom
    have hdom2 := (WShape.HasDom.lift le₂).2 hdom2
    have ca_w := (TShape.Compat.def le₁ le₂).1 ca
    refine mk (h1.trans ?_) (h12.trans ?_) <|
      .forallE' ib ia (hdom.join cf ca_w hdom2) fun x hx => ?_
    · refine (TShape.LE.lift_l (Nat.succ_le_succ le₁)).2 ?_
      exact WShape.lift_forallE le₁ ▸ WShape.forallE_le_forallE.2 ⟨jb.le.1, jf.le.1⟩
    · refine (TShape.LE.lift_l (Nat.succ_le_succ le₂)).2 ?_
      exact WShape.lift_forallE le₂ ▸ WShape.forallE_le_forallE.2 ⟨jb.le.2, jf.le.2⟩
    have ⟨x₁', a1, a2'⟩ := WShapeFun.app_eq (f₁.lift _) x
    have ⟨x₂', b1, b2'⟩ := WShapeFun.app_eq (f₂.lift _) x
    have ⟨ox₁, oy₁, hm₁, hx₁eq, hy₁eq⟩ := (WShapeFun.mem_lift le₁).1 a2'
    have ⟨ox₂, oy₂, hm₂, hx₂eq, hy₂eq⟩ := (WShapeFun.mem_lift le₂).1 b2'
    have a1' : ox₁.T ≤ x.T := ((TShape.LE.lift_l le₁).2 .rfl).trans (hx₁eq ▸ a1).T
    have b1' : ox₂.T ≤ x.T := ((TShape.LE.lift_l le₂).2 .rfl).trans (hx₂eq ▸ b1).T
    have hc := TShape.Compat.def'.2 ⟨x.T, a1', b1'⟩
    have ⟨_, hj⟩ := hC hm₁ hm₂ hc
    refine hj.mono_l (Valuation.LE.push.2 ⟨.rfl, (TShape.Join.mk hc x.T).2 ⟨a1', b1'⟩⟩) |>.mono ?_
    have ja := hy₁eq ▸ hy₂eq ▸ jf.app_l x
    exact (ja _).2 (WShape.Join.mk <| WShape.Compat.iff.2 ⟨_, ja.le.1, ja.le.2⟩).le |>.T
  | @const _ _ _ _ _ _ _ _ R₁ h1 h2 h3 h4 h5 h6 h7 ih1 ih2 =>
    cases H2 with | @const _ _ _ _ _ _ _ _ R₂ a1 a2 a3 a4 a5 a6 a7 => ?_ | bot =>
      exact bot_r hρ (.const h1 h2 h3 h4 h5 h6 h7)
    cases h1.symm.trans a1
    let Rd (R : TShape → SExpr → Prop) m e := m ≤ .bot ∨ ∃ m', m ≤ m' ∧ R m' e
    have h6' := h6.mono (R' := Rd R₁) .rfl (fun le hr => Or.inr ⟨_, le, hr⟩)
    have a6' := a6.mono (R' := Rd R₂) .rfl (fun le hr => Or.inr ⟨_, le, hr⟩)
    have mono {R a a' A} (le : a ≤ a') : Rd R a' A → Rd R a A :=
      .imp (by exact le.trans) fun ⟨_, le', hr⟩ => by exact ⟨_, le.trans le', hr⟩
    have ⟨hc1, hj1⟩ := (h6'.lift (Nat.le_max_left ..) mono).compat_join
        (R₃ := LE_Interp ρ) .nil (a6'.lift (Nat.le_max_right ..) mono)
        (.inl TShape.bot_le') (.inl TShape.bot_le') .mono <| by
      rintro m₁ m₂ A (hb1 | ⟨m₁', le1, hr1⟩) (hb2 | ⟨m₂', le2, hr2⟩)
      · exact mk hb1 hb2 .bot
      · exact mk (hb1.trans TShape.bot_le') le2 (a7 m₂' A hr2)
      · exact mk le1 (hb2.trans TShape.bot_le') ((h7 m₁' A hr1).mono_l hρ)
      · have ⟨c, lej⟩ := ih2 m₁' A hr1 hρ (a7 m₂' A hr2)
        exact mk (le1.trans (TShape.Join.mk c).le.1) (le2.trans (TShape.Join.mk c).le.2) lej
    have ⟨ac, alej⟩ := ih1 hρ a5
    have ⟨b1, b2⟩ := (TShape.Join.mk hc1).le
    have ⟨b3, b4⟩ := (TShape.Join.mk ac).le
    refine have hc := .mono h3 a3 hc1; ⟨hc, ?_⟩
    refine .const h1 h2 ?_ ?_ alej hj1 fun _ _ => id
    · exact (TShape.Join.mk hc _).2 ⟨h3.trans b1, a3.trans b2⟩
    · have aty := h4.isType.join ac a4.isType
      exact .join hc1 (aty.mono_r b3 h4) (aty.mono_r b4 a4)

/-- Merge two compatible proof-relevant interpretations without losing the
exact constructor trees or abstract constant callbacks retained by either
side.  The recursive predicate is used only at constant `R` edges; its four
closure laws are exactly the operations performed while joining evaluator
results and saturating binder observations. -/
theorem LE_Interp.Witness.RDeepChildren.compat_join
    {P : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop}
    (laws : LE_Interp.Witness.RDeepChildren.JoinLaws P)
    (hρ : ρ'.LE ρ)
    {H₁ : LE_Interp.Witness ρ' m₁ M}
    (c₁ : H₁.RDeepChildren P)
    {H₂ : LE_Interp.Witness ρ m₂ M}
    (c₂ : H₂.RDeepChildren P) :
    m₁.Compat m₂ ∧
      ∃ HJ : LE_Interp.Witness ρ (m₁.join m₂) M,
        HJ.RDeepChildren P := by
  have mk {m₁ m₂ m ρ M}
      (hle₁ : m₁ ≤ m) (hle₂ : m₂ ≤ m)
      {H : LE_Interp.Witness ρ m M}
      (children : H.RDeepChildren P) :
      m₁.Compat m₂ ∧
        ∃ HJ : LE_Interp.Witness ρ (m₁.join m₂) M,
          HJ.RDeepChildren P := by
    have hc := TShape.Compat.def'.2 ⟨m, hle₁, hle₂⟩
    have hjoin : m₁.join m₂ ≤ m :=
      (TShape.Join.mk hc _).2 ⟨hle₁, hle₂⟩
    exact ⟨hc, H.mono hjoin, children.mono hjoin⟩
  have bot_r {m₁ n₂ ρ' ρ M}
      (hρ : ρ'.LE ρ)
      {H : LE_Interp.Witness ρ' m₁ M}
      (children : H.RDeepChildren P) :
      m₁.Compat (WShape.bot (n := n₂)).T ∧
        ∃ HJ : LE_Interp.Witness ρ
            (m₁.join (WShape.bot (n := n₂)).T) M,
          HJ.RDeepChildren P :=
    mk .rfl TShape.bot_le' (children.mono_l laws.mono_l hρ)
  induction H₁ generalizing ρ m₂ with
  | bot => exact mk TShape.bot_le' .rfl c₂
  | sort hle =>
    cases c₁
    cases H₂ with
    | bot => exact bot_r hρ (.sort (h := hle))
    | sort hle₂ =>
      cases c₂
      exact mk (hle.trans (TShape.sort_eqv.2))
        (hle₂.trans TShape.sort_eqv.2) (.sort (h := TShape.LE.rfl))
  | bvar hle =>
    cases c₁
    cases H₂ with
    | bot => exact bot_r hρ (.bvar (h := hle))
    | bvar hle₂ =>
      cases c₂
      exact mk (hle.trans (hρ _)) hle₂ (.bvar (h := TShape.LE.rfl))
  | @app ρ₁ n₁ f₁ F A m₁ a₁ hf ha hle ihf iha =>
    cases c₁ with
    | app cf ca =>
      cases H₂ with
      | bot =>
        exact bot_r hρ (H := .app hf ha hle) (.app cf ca)
      | @app _ n₂ f₂ _ _ _ a₂ hf₂ ha₂ hle₂ =>
        cases c₂ with
        | app cf₂ ca₂ =>
          obtain ⟨hcf, hfj, cfj⟩ := ihf hρ cf cf₂
          obtain ⟨hca, haj, caj⟩ := iha hρ ca ca₂
          have hfl := (TShape.Join.mk hcf).le
          have hal := (TShape.Join.mk hca).le
          have le' : (f₁.T.join f₂.T).1 ≤ max n₁ n₂ + 1 := by
            simp [TShape.join]
          have hfjLe := (TShape.lift_eqv le').1
          let HJ := LE_Interp.Witness.app
            (hfj.mono hfjLe) haj TShape.LE.rfl
          have cHJ : HJ.RDeepChildren P := by
            dsimp only [HJ]
            exact .app (cfj.mono hfjLe) caj
          exact mk
            (hle.trans <| TShape.app_mono
              (hfl.1.trans (TShape.lift_eqv le').2) hal.1)
            (hle₂.trans <| TShape.app_mono
              (hfl.2.trans (TShape.lift_eqv le').2) hal.2)
            cHJ
  | @lam ρ₁ n₁ a₁ A f₁ F m₁ ha hdom he hle iha ihf =>
    cases c₁ with
    | lam ca cbody =>
      cases H₂ with
      | bot =>
        exact bot_r hρ (H := .lam ha hdom he hle) (.lam ca cbody)
      | @lam _ n₂ a₂ _ f₂ _ _ ha₂ hdom₂ he₂ hle₂ =>
        cases c₂ with
        | lam ca₂ cbody₂ =>
          obtain ⟨hca, ia, cia⟩ := iha hρ ca ca₂
          have hC {x₁ y₁ x₂ y₂}
              (hm₁ : (x₁, y₁) ∈ f₁) (hm₂ : (x₂, y₂) ∈ f₂)
              (hc : x₁.T.Compat x₂.T) :
              y₁.T.Compat y₂.T ∧
                ∃ hJ : LE_Interp.Witness
                    (ρ.push (x₁.T.join x₂.T)) (y₁.T.join y₂.T) F,
                  hJ.RDeepChildren P := by
            have ⟨j₁, j₂⟩ := (TShape.Join.mk hc).le
            have ⟨x'₁, hx1_le, hx1, happ1⟩ := WShape.HasDom.iff.1 hdom x₁
            have ⟨x'₂, hx2_le, hx2, happ2⟩ := WShape.HasDom.iff.1 hdom₂ x₂
            let hi₂ := (he₂ x'₂ hx2).mono (WShape.LE.T happ2)
              |>.mono_l (Valuation.LE.push.2
                ⟨Valuation.LE.rfl, hx2_le.T.trans j₂⟩)
            have ci₂ : hi₂.RDeepChildren P := by
              dsimp only [hi₂]
              exact ((cbody₂ x'₂ hx2).mono (WShape.LE.T happ2))
                |>.mono_l laws.mono_l (Valuation.LE.push.2
                  ⟨Valuation.LE.rfl, hx2_le.T.trans j₂⟩)
            obtain ⟨hc', hJ, cJ⟩ := ihf x'₁ hx1
              (Valuation.LE.push.2 ⟨hρ, hx1_le.T.trans j₁⟩)
              (cbody x'₁ hx1) ci₂
            exact mk
              ((WShapeFun.app_of_mem hm₁).2.T.trans happ1.T
                |>.trans (TShape.Join.mk hc').le.1)
              ((WShapeFun.app_of_mem hm₂).2.T.trans
                (TShape.Join.mk hc').le.2) cJ
          have le₁ := Nat.le_max_left n₁ n₂
          have le₂ := Nat.le_max_right n₁ n₂
          have cf : WShapeFun.Compat
              (f₁.lift (max n₁ n₂)) (f₂.lift (max n₁ n₂)) := by
            simp only [WShapeFun.Compat.def, Prod.forall, le₂,
              WShapeFun.mem_lift, le₁]
            rintro _ _ ⟨x₁, y₁, hm₁, rfl, rfl⟩
              _ _ ⟨x₂, y₂, hm₂, rfl, rfl⟩ hc
            exact (hC hm₁ hm₂ hc).1
          let fJ := (f₁.lift (max n₁ n₂)).join
            (f₂.lift (max n₁ n₂))
          have jf : WShapeFun.Join (f₁.lift (max n₁ n₂))
              (f₂.lift (max n₁ n₂)) fJ := by
            simpa only [fJ] using WShapeFun.Join.mk cf
          have hdom₁ := (WShape.HasDom.lift le₁).2 hdom
          have hdom₂' := (WShape.HasDom.lift le₂).2 hdom₂
          have ca_w : WShape.Compat (a₁.lift _) (a₂.lift _) :=
            (TShape.Compat.def le₁ le₂).1 hca
          have hdomJ := hdom₁.join cf ca_w hdom₂'
          have bodyJ (x : WShape (max n₁ n₂))
              (hx : x.HasType (a₁.lift _ |>.join (a₂.lift _))) :
              ∃ hJ : LE_Interp.Witness (ρ.push x.T) (fJ.app x).T F,
                hJ.RDeepChildren P := by
            have ⟨x₁', a1, a2'⟩ := WShapeFun.app_eq (f₁.lift _) x
            have ⟨x₂', b1, b2'⟩ := WShapeFun.app_eq (f₂.lift _) x
            have ⟨ox₁, oy₁, hm₁, hx₁eq, hy₁eq⟩ :=
              (WShapeFun.mem_lift le₁).1 a2'
            have ⟨ox₂, oy₂, hm₂, hx₂eq, hy₂eq⟩ :=
              (WShapeFun.mem_lift le₂).1 b2'
            have a1' : ox₁.T ≤ x.T :=
              ((TShape.LE.lift_l le₁).2 .rfl).trans
                (hx₁eq ▸ a1).T
            have b1' : ox₂.T ≤ x.T :=
              ((TShape.LE.lift_l le₂).2 .rfl).trans
                (hx₂eq ▸ b1).T
            have hc := TShape.Compat.def'.2 ⟨x.T, a1', b1'⟩
            obtain ⟨_, hJ, cJ⟩ := hC hm₁ hm₂ hc
            have hρx : (ρ.push (ox₁.T.join ox₂.T)).LE (ρ.push x.T) :=
              Valuation.LE.push.2
              ⟨Valuation.LE.rfl,
                (TShape.Join.mk hc x.T).2 ⟨a1', b1'⟩⟩
            have ja := hy₁eq ▸ hy₂eq ▸ jf.app_l x
            have oy_c := WShape.Compat.iff.2 ⟨_, ja.le.1, ja.le.2⟩
            have hout := (ja _).2 (WShape.Join.mk oy_c).le |>.T
            exact ⟨hJ.mono_l hρx |>.mono hout,
              (cJ.mono_l laws.mono_l hρx).mono hout⟩
          let hbodyJ := fun x hx => Classical.choose (bodyJ x hx)
          have cbodyJ : ∀ x hx, (hbodyJ x hx).RDeepChildren P :=
            fun x hx => Classical.choose_spec (bodyJ x hx)
          let HJ := LE_Interp.Witness.lam ia hdomJ hbodyJ TShape.LE.rfl
          have cHJ : HJ.RDeepChildren P := by
            dsimp only [HJ]
            exact .lam cia cbodyJ
          exact mk
            (hle.trans <| (TShape.LE.lift_l (Nat.succ_le_succ le₁)).2 <|
              WShape.lift_lam' le₁ ▸
                WShape.lam'_le_lam'.2 jf.le.1)
            (hle₂.trans <| (TShape.LE.lift_l (Nat.succ_le_succ le₂)).2 <|
              WShape.lift_lam' le₂ ▸
                WShape.lam'_le_lam'.2 jf.le.2)
            cHJ
  | @forallE ρ₁ n₁ b₁ B b₁' f₁ F m₁ hb ha hdom he hle ihb iha ihf =>
    cases c₁ with
    | forallE cb ca cbody =>
      cases H₂ with
      | bot =>
        exact bot_r hρ (H := .forallE hb ha hdom he hle)
          (.forallE cb ca cbody)
      | @forallE _ n₂ b₂ _ b₂' f₂ _ _ hb₂ ha₂ hdom₂ he₂ hle₂ =>
        cases c₂ with
        | forallE cb₂ ca₂ cbody₂ =>
          obtain ⟨hcb, ib, cib⟩ := ihb hρ cb cb₂
          obtain ⟨hca, ia, cia⟩ := iha hρ ca ca₂
          have hC {x₁ y₁ x₂ y₂}
              (hm₁ : (x₁, y₁) ∈ f₁) (hm₂ : (x₂, y₂) ∈ f₂)
              (hc : x₁.T.Compat x₂.T) :
              y₁.T.Compat y₂.T ∧
                ∃ hJ : LE_Interp.Witness
                    (ρ.push (x₁.T.join x₂.T)) (y₁.T.join y₂.T) F,
                  hJ.RDeepChildren P := by
            have ⟨j₁, j₂⟩ := (TShape.Join.mk hc).le
            have ⟨x'₁, hx1_le, hx1, happ1⟩ := WShape.HasDom.iff.1 hdom x₁
            have ⟨x'₂, hx2_le, hx2, happ2⟩ := WShape.HasDom.iff.1 hdom₂ x₂
            let hi₂ := (he₂ x'₂ hx2).mono (WShape.LE.T happ2)
              |>.mono_l (Valuation.LE.push.2
                ⟨Valuation.LE.rfl, hx2_le.T.trans j₂⟩)
            have ci₂ : hi₂.RDeepChildren P := by
              dsimp only [hi₂]
              exact ((cbody₂ x'₂ hx2).mono (WShape.LE.T happ2))
                |>.mono_l laws.mono_l (Valuation.LE.push.2
                  ⟨Valuation.LE.rfl, hx2_le.T.trans j₂⟩)
            obtain ⟨hc', hJ, cJ⟩ := ihf x'₁ hx1
              (Valuation.LE.push.2 ⟨hρ, hx1_le.T.trans j₁⟩)
              (cbody x'₁ hx1) ci₂
            exact mk
              ((WShapeFun.app_of_mem hm₁).2.T.trans happ1.T
                |>.trans (TShape.Join.mk hc').le.1)
              ((WShapeFun.app_of_mem hm₂).2.T.trans
                (TShape.Join.mk hc').le.2) cJ
          have le₁ := Nat.le_max_left n₁ n₂
          have le₂ := Nat.le_max_right n₁ n₂
          have cf : WShapeFun.Compat
              (f₁.lift (max n₁ n₂)) (f₂.lift (max n₁ n₂)) := by
            simp only [WShapeFun.Compat.def, Prod.forall, le₂,
              WShapeFun.mem_lift, le₁]
            rintro _ _ ⟨x₁, y₁, hm₁, rfl, rfl⟩
              _ _ ⟨x₂, y₂, hm₂, rfl, rfl⟩ hc
            exact (hC hm₁ hm₂ hc).1
          let fJ := (f₁.lift (max n₁ n₂)).join
            (f₂.lift (max n₁ n₂))
          have jf : WShapeFun.Join (f₁.lift (max n₁ n₂))
              (f₂.lift (max n₁ n₂)) fJ := by
            simpa only [fJ] using WShapeFun.Join.mk cf
          have cb_w : WShape.Compat (b₁.lift _) (b₂.lift _) :=
            (TShape.Compat.def le₁ le₂).1 hcb
          let bJ := (b₁.lift (max n₁ n₂)).join
            (b₂.lift (max n₁ n₂))
          have jb : WShape.Join (b₁.lift (max n₁ n₂))
              (b₂.lift (max n₁ n₂)) bJ := by
            simpa only [bJ] using WShape.Join.mk cb_w
          have hdom₁ := (WShape.HasDom.lift le₁).2 hdom
          have hdom₂' := (WShape.HasDom.lift le₂).2 hdom₂
          have ca_w : WShape.Compat (b₁'.lift _) (b₂'.lift _) :=
            (TShape.Compat.def le₁ le₂).1 hca
          have hdomJ := hdom₁.join cf ca_w hdom₂'
          have bodyJ (x : WShape (max n₁ n₂))
              (hx : x.HasType (b₁'.lift _ |>.join (b₂'.lift _))) :
              ∃ hJ : LE_Interp.Witness (ρ.push x.T) (fJ.app x).T F,
                hJ.RDeepChildren P := by
            have ⟨x₁', a1, a2'⟩ := WShapeFun.app_eq (f₁.lift _) x
            have ⟨x₂', b1, b2'⟩ := WShapeFun.app_eq (f₂.lift _) x
            have ⟨ox₁, oy₁, hm₁, hx₁eq, hy₁eq⟩ :=
              (WShapeFun.mem_lift le₁).1 a2'
            have ⟨ox₂, oy₂, hm₂, hx₂eq, hy₂eq⟩ :=
              (WShapeFun.mem_lift le₂).1 b2'
            have a1' : ox₁.T ≤ x.T :=
              ((TShape.LE.lift_l le₁).2 .rfl).trans
                (hx₁eq ▸ a1).T
            have b1' : ox₂.T ≤ x.T :=
              ((TShape.LE.lift_l le₂).2 .rfl).trans
                (hx₂eq ▸ b1).T
            have hc := TShape.Compat.def'.2 ⟨x.T, a1', b1'⟩
            obtain ⟨_, hJ, cJ⟩ := hC hm₁ hm₂ hc
            have hρx : (ρ.push (ox₁.T.join ox₂.T)).LE (ρ.push x.T) :=
              Valuation.LE.push.2
                ⟨Valuation.LE.rfl,
                  (TShape.Join.mk hc x.T).2 ⟨a1', b1'⟩⟩
            have ja := hy₁eq ▸ hy₂eq ▸ jf.app_l x
            have oy_c := WShape.Compat.iff.2 ⟨_, ja.le.1, ja.le.2⟩
            have hout := (ja _).2 (WShape.Join.mk oy_c).le |>.T
            exact ⟨hJ.mono_l hρx |>.mono hout,
              (cJ.mono_l laws.mono_l hρx).mono hout⟩
          let hbodyJ := fun x hx => Classical.choose (bodyJ x hx)
          have cbodyJ : ∀ x hx, (hbodyJ x hx).RDeepChildren P :=
            fun x hx => Classical.choose_spec (bodyJ x hx)
          let HJ := LE_Interp.Witness.forallE ib ia hdomJ hbodyJ TShape.LE.rfl
          have cHJ : HJ.RDeepChildren P := by
            dsimp only [HJ]
            exact .forallE cib cia cbodyJ
          exact mk
            (hle.trans <| (TShape.LE.lift_l (Nat.succ_le_succ le₁)).2 <|
              WShape.lift_forallE le₁ ▸
                WShape.forallE_le_forallE.2 ⟨jb.le.1, jf.le.1⟩)
            (hle₂.trans <| (TShape.LE.lift_l (Nat.succ_le_succ le₂)).2 <|
              WShape.lift_forallE le₂ ▸
                WShape.forallE_le_forallE.2 ⟨jb.le.2, jf.le.2⟩)
            cHJ
  | @const _ _ _ mRoot₁ mEval₁ _ aTy₁ _ R₁
      hreg hlen hle hty hA hC hR ihA ihR =>
    cases c₁ with
    | const cA pR cR =>
      cases H₂ with
      | bot =>
        exact bot_r hρ (H := .const hreg hlen hle hty hA hC hR)
          (.const cA pR cR)
      | @const _ _ _ _ mEval₂ _ aTy₂ _ R₂
          hreg₂ hlen₂ hle₂ hty₂ hA₂ hC₂ hR₂ =>
        cases c₂ with
        | const cA₂ pR₂ cR₂ =>
          cases hreg.symm.trans hreg₂
          let R₃ (m : TShape) (e : SExpr) : Prop :=
            ∃ H : LE_Interp.Witness ρ m e, H.RDeepChildren P ∧ P H
          have R₃_mono {a a' A} (le : a ≤ a') : R₃ a' A → R₃ a A := by
            rintro ⟨H, cH, pH⟩
            exact ⟨H.mono le, cH.mono le, laws.mono H le pH⟩
          have mkR {m₁ m₂ m : TShape} {e : SExpr}
              (hle₁ : m₁ ≤ m) (hle₂ : m₂ ≤ m)
              {H : LE_Interp.Witness ρ m e}
              (cH : H.RDeepChildren P) (pH : P H) :
              m₁.Compat m₂ ∧ R₃ (m₁.join m₂) e := by
            have hc := TShape.Compat.def'.2 ⟨m, hle₁, hle₂⟩
            have hJle : m₁.join m₂ ≤ m :=
              (TShape.Join.mk hc _).2 ⟨hle₁, hle₂⟩
            exact ⟨hc, H.mono hJle, cH.mono hJle,
              laws.mono H hJle pH⟩
          let Rd (R : TShape → SExpr → Prop) m e :=
            m ≤ .bot ∨ ∃ m', m ≤ m' ∧ R m' e
          have hC₁ := hC.mono (R' := Rd R₁) TShape.LE.rfl
            (fun le hr => Or.inr ⟨_, le, hr⟩)
          have hC₂ := hC₂.mono (R' := Rd R₂) TShape.LE.rfl
            (fun le hr => Or.inr ⟨_, le, hr⟩)
          have rd_mono {R a a' A} (le : a ≤ a') : Rd R a' A → Rd R a A :=
            .imp (by exact le.trans) fun ⟨_, le', hr⟩ => by
              exact ⟨_, le.trans le', hr⟩
          have hRR : ∀ {m₁ m₂ A}, Rd R₁ m₁ A → Rd R₂ m₂ A →
              m₁.Compat m₂ ∧ R₃ (m₁.join m₂) A := by
            rintro m₁ m₂ A (hb₁ | ⟨m₁', le₁, hr₁⟩)
              (hb₂ | ⟨m₂', le₂, hr₂⟩)
            · exact mkR hb₁ hb₂ (H := LE_Interp.Witness.bot)
                .bot laws.bot
            · exact mkR (hb₁.trans TShape.bot_le') le₂
                (cR₂ m₂' A hr₂) (pR₂ m₂' A hr₂)
            · let H₁ := (hR m₁' A hr₁).mono_l hρ
              have cH₁ : H₁.RDeepChildren P := by
                dsimp only [H₁]
                exact (cR m₁' A hr₁).mono_l laws.mono_l hρ
              have pH₁ : P H₁ := by
                dsimp only [H₁]
                exact laws.mono_l (hR m₁' A hr₁) hρ
                  (pR m₁' A hr₁)
              exact mkR le₁ (hb₂.trans TShape.bot_le') cH₁ pH₁
            · let H₁ := (hR m₁' A hr₁).mono_l hρ
              let H₂ := hR₂ m₂' A hr₂
              have cH₁ : H₁.RDeepChildren P := by
                dsimp only [H₁]
                exact (cR m₁' A hr₁).mono_l laws.mono_l hρ
              have pH₁ : P H₁ := by
                dsimp only [H₁]
                exact laws.mono_l (hR m₁' A hr₁) hρ
                  (pR m₁' A hr₁)
              have cH₂ : H₂.RDeepChildren P := by
                dsimp only [H₂]
                exact cR₂ m₂' A hr₂
              have pH₂ : P H₂ := by
                dsimp only [H₂]
                exact pR₂ m₂' A hr₂
              obtain ⟨hc, hJ, cJ⟩ := ihR m₁' A hr₁ hρ
                (cR m₁' A hr₁) cH₂
              have pJ : P hJ := laws.join H₁ H₂ hJ pH₁ pH₂
              exact mkR
                (le₁.trans (TShape.Join.mk hc).le.1)
                (le₂.trans (TShape.Join.mk hc).le.2) cJ pJ
          obtain ⟨hcEval, hCEval⟩ :=
            (hC₁.lift (Nat.le_max_left ..) rd_mono).compat_join
              (R₃ := R₃) .nil
              (hC₂.lift (Nat.le_max_right ..) rd_mono)
              (.inl TShape.bot_le') (.inl TShape.bot_le') R₃_mono hRR
          obtain ⟨hcTy, hATyJ, cATyJ⟩ := ihA hρ cA cA₂
          have ⟨evalLe₁, evalLe₂⟩ := (TShape.Join.mk hcEval).le
          have ⟨tyLe₁, tyLe₂⟩ := (TShape.Join.mk hcTy).le
          have hcRoot := TShape.Compat.mono hle hle₂ hcEval
          have hrootLe : mRoot₁.join m₂ ≤ mEval₁.join mEval₂ :=
            (TShape.Join.mk hcRoot _).2
              ⟨hle.trans evalLe₁, hle₂.trans evalLe₂⟩
          have hresultTy : (mEval₁.join mEval₂).HasType
              (aTy₁.join aTy₂) := by
            have aty := hty.isType.join hcTy hty₂.isType
            exact .join hcEval (aty.mono_r tyLe₁ hty)
              (aty.mono_r tyLe₂ hty₂)
          let hRJ := fun m e (hr : R₃ m e) => Classical.choose hr
          have pRJ : ∀ m e hr, P (hRJ m e hr) :=
            fun m e hr => (Classical.choose_spec hr).2
          have cRJ : ∀ m e hr, (hRJ m e hr).RDeepChildren P :=
            fun m e hr => (Classical.choose_spec hr).1
          let HJ := LE_Interp.Witness.const hreg hlen hrootLe hresultTy
            hATyJ hCEval hRJ
          have cHJ : HJ.RDeepChildren P := by
            dsimp only [HJ]
            exact .const cATyJ pRJ cRJ
          exact ⟨hcRoot, HJ, cHJ⟩

theorem LE_Interp.compat (H1 : LE_Interp ρ m₁ M) (H2 : LE_Interp ρ m₂ M) : m₁.Compat m₂ :=
  (compat_join .rfl H1 H2).1

theorem LE_Interp.join' (H1 : LE_Interp ρ m₁ M) (H2 : LE_Interp ρ m₂ M) :
    LE_Interp ρ (m₁.join m₂) M :=
  (compat_join .rfl H1 H2).2

theorem LE_Interp.join (J : m₁.Join m₂ m) (H1 : LE_Interp ρ m₁ M) (H2 : LE_Interp ρ m₂ M) :
    LE_Interp ρ m M :=
  (H1.join' H2).mono ((J _).2 (TShape.Join.mk (H1.compat H2)).le)

/-- Invert an interpreted `appN` tower without reselecting its fixed-head
witness.

The returned capture map joins repeated observations of the same path.  Only
those capture observations are proof-independent; `hhead` is the literal
sub-witness obtained by peeling `H`.  Thus a caller can rebuild the enclosing
constant with `hhead.LowerEdge` and know that every fixed RHS edge realizes by
root-lowering this exact witness. -/
theorem LE_Interp.Witness.appNVarsFocused
    {p : Pattern} {f : p.RHS} {paths : List p.Path}
    {capture : p.Path → SExpr} {out : TShape}
    (H : LE_Interp.Witness ρ out
      ((Pattern.RHS.appN f (paths.map fun path => .var path)).applyS
        ls capture))
    (hnonbot : ¬out ≤ TShape.bot) :
    ∃ mcap : p.Path → TShape,
      (∀ path, LE_Interp ρ (mcap path) (capture path)) ∧
      ∃ head, ∃ hhead : LE_Interp.Witness ρ head (f.applyS ls capture),
        LE_Interp.RHS.ShapeSpine mcap head paths out := by
  classical
  induction paths generalizing f out with
  | nil =>
    refine ⟨fun _ => TShape.bot, fun _ => .bot, out, H, ?_⟩
    exact .nil
  | cons path paths ih =>
    simp only [List.map_cons, Pattern.RHS.appN] at H
    obtain ⟨mcap, hcap, head, hhead, hspine⟩ := ih H hnonbot
    have hheadNonbot : ¬head ≤ TShape.bot := by
      intro hbot
      exact hnonbot (hspine.le_bot hbot)
    cases hhead with
    | bot => exact (hheadNonbot TShape.bot_eqv.1).elim
    | @app _ n funShape _ _ _ argShape hfun harg happ =>
      have hargInterp : LE_Interp ρ argShape.T (capture path) := by
        simpa only [Pattern.RHS.applyS] using harg.toInterp
      let mcap' : p.Path → TShape := fun current =>
        if current = path then argShape.T.join (mcap current)
        else mcap current
      have htail : ∀ current, mcap current ≤ mcap' current := by
        intro current
        dsimp only [mcap']
        split <;> rename_i heq
        · subst current
          exact (TShape.Join.mk (hargInterp.compat (hcap path))).le.2
        · exact TShape.LE.rfl
      have hcurrent : argShape.T ≤ mcap' path := by
        simp only [mcap', if_pos rfl]
        exact (TShape.Join.mk (hargInterp.compat (hcap path))).le.1
      refine ⟨mcap', ?_, funShape.T, hfun, ?_⟩
      · intro current
        dsimp only [mcap']
        split <;> rename_i heq
        · subst current
          exact hargInterp.join' (hcap path)
        · exact hcap current
      · exact .cons hcurrent happ (hspine.mono_l htail)

/-- Specialize `appNVarsFocused` to the registered fixed tower selected by an
iota descriptor. -/
theorem _root_.Lean4Lean.Pattern.IotaRule.focusedShapeSpine
    {rec ctor : Name} {major arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (rule : Pattern.IotaRule r) {ls : List SLevel}
    {capture : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
    {out : TShape}
    (H : LE_Interp.Witness ρ out (r.1.applyS ls capture))
    (hnonbot : ¬out ≤ TShape.bot) :
    ∃ mcap : (RecursorIotaPattern rec major ctor arity).Path → TShape,
      (∀ path, LE_Interp ρ (mcap path) (capture path)) ∧
      ∃ head, ∃ hhead : LE_Interp.Witness ρ head
          (SExpr.mkInst ls rule.df.rhs),
        LE_Interp.RHS.ShapeSpine mcap head rule.capturePaths out := by
  rw [rule.rhsTower] at H
  exact H.appNVarsFocused hnonbot

/-- Rebuild the registered iota RHS using the singleton evaluator relation
generated by the exact fixed-head witness selected above. -/
theorem _root_.Lean4Lean.Pattern.IotaRule.focusedRHS
    {rec ctor : Name} {major arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (rule : Pattern.IotaRule r) {ls : List SLevel}
    {mcap : (RecursorIotaPattern rec major ctor arity).Path → TShape}
    {head out : TShape}
    (hhead : LE_Interp.Witness ρ head (SExpr.mkInst ls rule.df.rhs))
    (spine : LE_Interp.RHS.ShapeSpine
      mcap head rule.capturePaths out) :
    LE_Interp.RHS ls mcap hhead.LowerEdge out r.1 := by
  rw [rule.rhsTower]
  exact spine.to_appN (.const
    (LE_Interp.Witness.LowerEdge.self hhead))

theorem LE_Interp.subst : LE_Interp ρ m (M.subst σ) ↔
    ∃ ρ', LE_Interp ρ' m M ∧ ∀ i, LE_Interp ρ (ρ' i) (σ i) := by
  refine ⟨fun H => ?_, ?_⟩
  · suffices ∀ {ρ m N}, LE_Interp ρ m N → ∀ (M : SExpr) (σ : Subst), M.subst σ = N →
        ∃ ρ', LE_Interp ρ' m M ∧ ∀ i, LE_Interp ρ (ρ' i) (σ i) from this H M σ rfl
    intro ρ m N H M σ eq
    have bvar {ρ : Valuation} {m N} {σ : Subst} {j} (hσj : σ j = N) (hN : LE_Interp ρ m N) :
        ∃ ρ', LE_Interp ρ' m (.bvar j) ∧ ∀ i, LE_Interp ρ (ρ' i) (σ i) := by
      refine ⟨fun k => if k = j then m else ⟨0, .bot⟩, .bvar (if_pos rfl ▸ .rfl), fun k => ?_⟩
      dsimp; split <;> rename_i ek
      · subst ek; exact hσj ▸ hN
      · exact .bot
    induction H generalizing M σ with
    | bot => exact ⟨.nil, .bot, fun _ => .bot⟩
    | sort h1 =>
      cases M with | bvar => exact bvar eq (.sort h1) | sort => ?_ | _ => cases eq
      cases eq; exact ⟨.nil, .sort h1, fun _ => .bot⟩
    | bvar h1 => cases M with | bvar => exact bvar eq (.bvar h1) | _ => cases eq
    | app hf ha h1 ih_f ih_a =>
      cases M with | bvar => exact bvar eq (.app hf ha h1) | app F' A' => ?_ | _ => cases eq
      cases eq
      have ⟨ρ₁, hF, h₁⟩ := ih_f F' σ rfl
      have ⟨ρ₂, hA, h₂⟩ := ih_a A' σ rfl
      have hc : ρ₁.Compat ρ₂ := fun i => (h₁ i).compat (h₂ i)
      have ⟨hj1, hj2⟩ := hc.le_join
      refine ⟨ρ₁.join ρ₂, .app (hF.mono_l hj1) (hA.mono_l hj2) h1, fun i => ?_⟩
      exact (h₁ i).join' (h₂ i)
    | @lam ρ n₁ a A f F m_orig ha hdom hbody h1 ih_a ih_body =>
      cases M with | bvar => exact bvar eq (.lam ha hdom hbody h1) | lam A' F' => ?_ | _ => cases eq
      cases eq
      suffices ∃ ρ', LE_Interp ρ' a.T A' ∧ (∀ i, LE_Interp ρ (ρ' i) (σ i)) ∧
          ∀ x ∈ f, LE_Interp (ρ'.push x.1.T) x.2.T F' by
        have ⟨ρ', ha', hρ, H⟩ := this
        refine ⟨ρ', .lam ha' hdom (fun x h => ?_) h1, hρ⟩
        obtain ⟨x', a1, a2⟩ := WShapeFun.app_eq f x
        exact (H _ a2).mono_l (Valuation.LE.push.2 ⟨.rfl, a1.T⟩)
      have H x (h : x ∈ f) :
          ∃ ρ', LE_Interp ρ' x.2.T F' ∧ ∀ i, LE_Interp (ρ.push x.1.T) (ρ' i) (σ.lift i) := by
        have ⟨x', hle, hht, happ⟩ := WShape.HasDom.iff.1 hdom x.1
        have ⟨ρ_x, hF_x, hρ_x⟩ := ih_body x' hht F' σ.lift rfl
        refine ⟨ρ_x, hF_x.mono ((WShapeFun.app_of_mem h).2.trans happ).T, fun i => ?_⟩
        exact (hρ_x i).mono_l (Valuation.LE.push.2 ⟨.rfl, hle.T⟩)
      have ⟨ρA, ha', hρA⟩ := ih_a A' σ rfl
      suffices ∀ (fl : List (Shape n₁ × Shape n₁))
          (wf : ∀ x ∈ fl, x.1.WF ∧ x.2.WF),
          (∀ (x : WShape n₁ × WShape n₁), (x.1.1, x.2.1) ∈ fl →
            ∃ ρ', LE_Interp ρ' x.2.T F' ∧ ∀ i, LE_Interp (ρ.push x.1.T) (ρ' i) (σ.lift i)) →
          ∃ ρ', LE_Interp ρ' a.T A' ∧ (∀ i, LE_Interp ρ (ρ' i) (σ i)) ∧
            ∀ (x : WShape n₁ × WShape n₁), (x.1.1, x.2.1) ∈ fl →
              LE_Interp (ρ'.push x.1.T) x.2.T F' from this f.1 f.2.2 H
      intro fl wf H
      induction fl with | nil => exact ⟨ρA, ha', hρA, nofun⟩ | cons p fl ih
      have ⟨hwf1, hwf2⟩ := wf _ (List.mem_cons_self ..)
      have ⟨ρ₁, hy, hρ₁⟩ := H ⟨⟨p.1, hwf1⟩, ⟨p.2, hwf2⟩⟩ (List.mem_cons_self ..)
      have ⟨ρ₂, ha₂, hρ₂, H_tl⟩ := ih (fun x h => wf x (List.mem_cons.2 (.inr h)))
        (fun x h => H x (List.mem_cons.2 (.inr h)))
      let ρ₁' : Valuation := fun i => ρ₁ (i + 1)
      have hρ₁' i : LE_Interp ρ (ρ₁' i) (σ i) := weak_iff.1 (hρ₁ (i + 1))
      have : ρ₁'.Compat ρ₂ := fun i => (hρ₁' i).compat (hρ₂ i)
      have ⟨hj1, hj2⟩ := this.le_join
      refine ⟨ρ₁'.join ρ₂, ha₂.mono_l hj2, fun i => (hρ₁' i).join' (hρ₂ i), fun x h => ?_⟩
      cases List.mem_cons.1 h with
      | inl h =>
        have heq : x = ⟨⟨p.1, hwf1⟩, ⟨p.2, hwf2⟩⟩ := by
          ext <;> [exact (Prod.ext_iff.1 h).1; exact (Prod.ext_iff.1 h).2]
        subst heq
        exact hy.mono_l <| by
          rw [← (show ρ₁'.push (ρ₁ 0) = ρ₁ by funext i; cases i <;> rfl)]
          exact Valuation.LE.push.2 ⟨hj1, bvar_iff.1 (hρ₁ 0)⟩
      | inr h => exact (H_tl x h).mono_l (Valuation.LE.push.2 ⟨hj2, .rfl⟩)
    | @forallE ρ n₁ b B b' f F m_orig hb hb' hdom hbody h1 ih_b ih_b' ih_body =>
      cases M with
      | bvar => exact bvar eq (.forallE hb hb' hdom hbody h1) | forallE B' F' => ?_ | _ => cases eq
      cases eq
      suffices ∃ ρ', LE_Interp ρ' b.T B' ∧ LE_Interp ρ' b'.T B' ∧
          (∀ i, LE_Interp ρ (ρ' i) (σ i)) ∧ ∀ x ∈ f, LE_Interp (ρ'.push x.1.T) x.2.T F' by
        have ⟨ρ', hb, hb', hρ, H⟩ := this
        refine ⟨ρ', .forallE hb hb' hdom (fun x h => ?_) h1, hρ⟩
        obtain ⟨x', a1, a2⟩ := WShapeFun.app_eq f x
        exact (H _ a2).mono_l <| Valuation.LE.push.2 ⟨.rfl, a1.T⟩
      have H x (h : x ∈ f) :
          ∃ ρ', LE_Interp ρ' x.2.T F' ∧ ∀ i, LE_Interp (ρ.push x.1.T) (ρ' i) (σ.lift i) := by
        have ⟨x', hle, hht, happ⟩ := WShape.HasDom.iff.1 hdom x.1
        have ⟨ρ_x, hF_x, hρ_x⟩ := ih_body x' hht F' σ.lift rfl
        refine ⟨ρ_x, hF_x.mono ((WShapeFun.app_of_mem h).2.trans happ).T, fun i => ?_⟩
        exact (hρ_x i).mono_l (Valuation.LE.push.2 ⟨.rfl, hle.T⟩)
      have ⟨ρ₁, hb₁, hρ₁⟩ := ih_b B' σ rfl
      have ⟨ρ₂, hb₂, hρ₂⟩ := ih_b' B' σ rfl
      have hc₀ : ρ₁.Compat ρ₂ := fun i => (hρ₁ i).compat (hρ₂ i)
      have ⟨hj1₀, hj2₀⟩ := hc₀.le_join
      let ρ₀ := ρ₁.join ρ₂
      suffices ∀ (fl : List (Shape n₁ × Shape n₁))
          (wf : ∀ x ∈ fl, x.1.WF ∧ x.2.WF),
          (∀ (x : WShape n₁ × WShape n₁), (x.1.1, x.2.1) ∈ fl →
            ∃ ρ', LE_Interp ρ' x.2.T F' ∧ ∀ i, LE_Interp (ρ.push x.1.T) (ρ' i) (σ.lift i)) →
          ∃ ρ', LE_Interp ρ' b.T B' ∧ LE_Interp ρ' b'.T B' ∧ (∀ i, LE_Interp ρ (ρ' i) (σ i)) ∧
            ∀ (x : WShape n₁ × WShape n₁), (x.1.1, x.2.1) ∈ fl →
              LE_Interp (ρ'.push x.1.T) x.2.T F' from this f.1 f.2.2 H
      intro fl wf H
      induction fl with
      | nil => exact ⟨ρ₀, hb₁.mono_l hj1₀, hb₂.mono_l hj2₀,
          fun i => (hρ₁ i).join' (hρ₂ i), fun _ h => absurd h List.not_mem_nil⟩
      | cons p fl ih
      have ⟨hwf1, hwf2⟩ := wf _ (List.mem_cons_self ..)
      have ⟨ρ₁, hy, hρ₁⟩ := H ⟨⟨p.1, hwf1⟩, ⟨p.2, hwf2⟩⟩ (List.mem_cons_self ..)
      have ⟨ρ₂, hb₂, hb'₂, hρ₂, H_tl⟩ := ih (fun x h => wf x (List.mem_cons.2 (.inr h)))
        (fun x h => H x (List.mem_cons.2 (.inr h)))
      let ρ₁' : Valuation := fun i => ρ₁ (i + 1)
      have hρ₁' i : LE_Interp ρ (ρ₁' i) (σ i) := weak_iff.1 (hρ₁ (i + 1))
      have : ρ₁'.Compat ρ₂ := fun i => (hρ₁' i).compat (hρ₂ i)
      have ⟨hj1, hj2⟩ := this.le_join
      refine ⟨ρ₁'.join ρ₂, hb₂.mono_l hj2, hb'₂.mono_l hj2,
        fun i => (hρ₁' i).join' (hρ₂ i), fun x h => ?_⟩
      cases List.mem_cons.1 h with
      | inl h =>
        have heq : x = ⟨⟨p.1, hwf1⟩, ⟨p.2, hwf2⟩⟩ := by
          ext <;> [exact (Prod.ext_iff.1 h).1; exact (Prod.ext_iff.1 h).2]
        subst heq
        refine hy.mono_l ?_
        rw [← show ρ₁'.push (ρ₁ 0) = ρ₁ from by funext i; cases i <;> rfl]
        exact Valuation.LE.push.2 ⟨hj1, bvar_iff.1 (hρ₁ 0)⟩
      | inr h => exact (H_tl x h).mono_l (Valuation.LE.push.2 ⟨hj2, .rfl⟩)
    | const h1 h2 h3 h4 h5 h6 h7 ih1 ih2 =>
      cases M with
      | bvar => exact bvar eq (.const h1 h2 h3 h4 h5 h6 h7) | const => ?_ | _ => cases eq
      cases eq
      refine ⟨.nil, .const h1 h2 h3 h4 ?_ h6.closed fun m e ⟨a1, a2⟩ => ?_, fun _ => .bot⟩
      · exact (closed_iff (Params.henv.closedC h1).mkInstS).1 h5
      · exact (closed_iff a1).1 (h7 m e a2)
  · rintro ⟨ρ', H, h⟩
    induction H generalizing ρ σ with
    | bot => exact .bot
    | sort h1 => exact .sort h1
    | bvar h1 => exact (h _).mono h1
    | app hf ha h1 ih_f ih_a => exact .app (ih_f h) (ih_a h) h1
    | lam ha hdom hbody h1 ih_a ih_body =>
      refine .lam (ih_a h) hdom (fun y hy => ?_) h1
      exact ih_body y hy fun | 0 => .bvar0 | i + 1 => (h i).weak
    | forallE hb hb' hdom hbody h1 ih_b ih_b' ih_body =>
      refine .forallE (ih_b h) (ih_b' h) hdom (fun y hy => ?_) h1
      exact ih_body y hy fun | 0 => .bvar0 | i + 1 => (h i).weak
    | const h1 h2 h3 h4 _ h6 _ ih1 ih2 =>
      refine .const h1 h2 h3 h4 ?_ h6.closed fun _ _ ⟨a1, a2⟩ => ?_
      · exact (Params.henv.closedC h1).mkInstS.subst_eq .zero ▸ ih1 h
      · exact a1.subst_eq .zero ▸ ih2 _ _ a2 h

theorem LE_Interp.inst : LE_Interp ρ f (F.inst A) ↔
    ∃ a, LE_Interp (ρ.push a) f F ∧ LE_Interp ρ a A := by
  refine ⟨fun H => ?_, fun ⟨a, hF, hA⟩ => ?_⟩
  · have ⟨ρ', hF, hσ⟩ := LE_Interp.subst.1 H
    refine ⟨_, hF.mono_l ?_, hσ 0⟩
    intro | 0 => exact .rfl | i+1 => exact (bvar_iff.1 (hσ (i+1)) :)
  · exact (LE_Interp.subst (σ := .one A)).2 ⟨_, hF, fun | 0 => hA | _+1 => .bvar'⟩

theorem LE_Interp.Witness.subst_toInterp
    {σ : Subst}
    (H : LE_Interp.Witness ρ' m M)
    (hσ : ∀ i, LE_Interp.Witness ρ (ρ' i) (σ i)) :
    (H.subst hσ).toInterp =
      (LE_Interp.subst.2 ⟨ρ', H.toInterp, fun i => (hσ i).toInterp⟩) :=
  Subsingleton.elim _ _

theorem LE_Interp.Witness.inst_toInterp
    (H : LE_Interp.Witness (ρ.push a) m F)
    (hA : LE_Interp.Witness ρ a A) :
    (H.inst hA).toInterp =
      (LE_Interp.inst.2 ⟨a, H.toInterp, hA.toInterp⟩) :=
  Subsingleton.elim _ _

theorem LE_Interp.forallE_inv {b} {f : WShapeFun n} {B F}
    (H : LE_Interp ρ (WShape.T (n := n+1) (.forallE b f)) (.forallE B F)) :
    LE_Interp ρ b.T B ∧ ∀ {{X x}}, LE_Interp ρ x.T X → LE_Interp ρ (f.app x).T (F.inst X) := by
  let .forallE (n := n') (f := f₁) hb₁ hb₂ hd hiB le := H
  have le₁ := Nat.le_max_left n n'; have le₂ := Nat.le_max_right n n'
  have ⟨hle_b, hle_f⟩ := TShape.LE.forallE_decomp le
  refine ⟨hb₁.mono ((TShape.LE.def le₁ le₂).2 hle_b), fun X x hx => ?_⟩
  obtain ⟨x', le1, hf⟩ := WShapeFun.app_eq f x
  have hle_f_raw : ShapeFun.LE
      (ShapeFun.lift (Shape.lift (max n n')) f.1)
      (ShapeFun.lift (Shape.lift (max n n')) f₁.1) := by
    rw [← WShapeFun.lift_val le₁, ← WShapeFun.lift_val le₂]; exact hle_f
  obtain ⟨_, _, hf', le2, lf⟩ := ShapeFun.LE.def.1 hle_f_raw _ _
    (List.mem_map.2 ⟨_, hf, rfl⟩)
  obtain ⟨⟨x₁, y₁⟩, hfm, ⟨⟩⟩ := List.mem_map.1 hf'
  have ⟨x₁_wf, y₁_wf⟩ : x₁.WF ∧ y₁.WF := f₁.2.2 _ hfm
  let x₁w : WShape n' := ⟨x₁, x₁_wf⟩
  let y₁w : WShape n' := ⟨y₁, y₁_wf⟩
  have hfm_w : (x₁w, y₁w) ∈ f₁ := (hfm : (x₁w.1, y₁w.1) ∈ f₁.1)
  have ⟨x'dom, hle_dom, hdom_mem, happ_dom⟩ := WShape.HasDom.iff.1 hd x₁w
  have le2_w : x₁w.lift (max n n') ≤ x'.lift (max n n') := by
    show (x₁w.lift _).1 ≤ (x'.lift _).1
    rw [WShape.lift_val le₂, WShape.lift_val le₁]; exact le2
  have le2_T : x₁w.T ≤ x'.T := (TShape.LE.def le₂ le₁).2 le2_w
  refine inst.2 ⟨_, ?_, hx.mono le1.T⟩
  refine hiB x'dom hdom_mem
    |>.mono_l (Valuation.LE.push.2 ⟨.rfl, hle_dom.T.trans le2_T⟩)
    |>.mono (WShape.LE.T happ_dom) |>.mono ?_
  show (f.app x).T ≤ (f₁.app x₁w).T
  have lf : (f.app x).lift (max n n') ≤ y₁w.lift (max n n') := by
    change ((f.app x).lift _).1 ≤ (y₁w.lift _).1
    rw [WShape.lift_val le₁, WShape.lift_val le₂]; exact lf
  exact ((TShape.LE.def le₁ le₂).2 lf).trans (WShape.LE.T (WShapeFun.app_of_mem hfm_w).2)

theorem LE_Interp.forallE_inv' {b} {f : WShapeFun n} {B F}
    (H : LE_Interp ρ (WShape.T (n := n+1) (.forallE b f)) (.forallE B F)) :
    LE_Interp ρ b.T B ∧ ∀ x, LE_Interp (ρ.push x.T) (f.app x).T F := by
  refine ⟨H.forallE_inv.1, fun x => ?_⟩
  have := (LE_Interp.weak (x := x.T) H).forallE_inv.2 .bvar0
  rwa [SExpr.inst, SExpr.subst_lift', (?_ : Subst.lift_l _ _ = Subst.id), subst_id] at this
  funext i; cases i <;> rfl

theorem LE_Interp.lam_inv {f : WShapeFun n} {B F}
    (H : LE_Interp ρ (WShape.T (n := n+1) (.lam' f)) (.lam B F))
    {{X x}} (hx : LE_Interp ρ x.T X) : LE_Interp ρ (f.app x).T (F.inst X) := by
  unfold WShape.lam' at H; split at H <;> rename_i hn; rotate_left
  · by_cases hl : f.app x ≤ .bot; · exact .mono hl.T .bot
    have ⟨_, _, h⟩ := f.app_eq x; exact absurd ⟨_, h, hl⟩ hn
  let .lam (n := n') (f := f₁) _ hd hiF le := H
  have le₁ := Nat.le_max_left n n'; have le₂ := Nat.le_max_right n n'
  have hle_f : f.lift (max n n') ≤ f₁.lift (max n n') := by
    rw [WShape.lam_eq_lam' (hl := hn)] at le; exact le.lam'_decomp
  obtain ⟨x', le1, hf⟩ := WShapeFun.app_eq f x
  have hle_f_raw : ShapeFun.LE
      (ShapeFun.lift (Shape.lift (max n n')) f.1)
      (ShapeFun.lift (Shape.lift (max n n')) f₁.1) := by
    rw [← WShapeFun.lift_val le₁, ← WShapeFun.lift_val le₂]; exact hle_f
  obtain ⟨_, _, hf', le2, lf⟩ := ShapeFun.LE.def.1 hle_f_raw _ _ (List.mem_map.2 ⟨_, hf, rfl⟩)
  obtain ⟨⟨x₁, y₁⟩, hfm, ⟨⟩⟩ := List.mem_map.1 hf'
  have ⟨x₁_wf, y₁_wf⟩ : x₁.WF ∧ y₁.WF := f₁.2.2 _ hfm
  let x₁w : WShape n' := ⟨x₁, x₁_wf⟩
  let y₁w : WShape n' := ⟨y₁, y₁_wf⟩
  have le2_w : x₁w.lift (max n n') ≤ x'.lift (max n n') := by
    rw [WShape.LE.def, WShape.lift_val le₂, WShape.lift_val le₁]; exact le2
  have hfm_w : (x₁w, y₁w) ∈ f₁ := (hfm : (x₁w.1, y₁w.1) ∈ f₁.1)
  have ⟨x'dom, hle_dom, hdom_mem, happ_dom⟩ := WShape.HasDom.iff.1 hd x₁w
  refine inst.2 ⟨_, ?_, hx.mono le1.T⟩
  refine hiF x'dom hdom_mem
    |>.mono_l (Valuation.LE.push.2 ⟨.rfl, hle_dom.T.trans ((TShape.LE.def le₂ le₁).2 le2_w)⟩)
    |>.mono (WShape.LE.T happ_dom) |>.mono (?_ : (f.app x).T ≤ (f₁.app x₁w).T)
  have lf : (f.app x).lift (max n n') ≤ y₁w.lift (max n n') := by
    show ((f.app x).lift _).1 ≤ (y₁w.lift _).1
    rw [WShape.lift_val le₁, WShape.lift_val le₂]; exact lf
  exact ((TShape.LE.def le₁ le₂).2 lf).trans (WShape.LE.T (WShapeFun.app_of_mem hfm_w).2)

theorem LE_Interp.lam_inv' {f : WShapeFun n} {hl : f.NonZero} {B F}
    (H : LE_Interp ρ (WShape.T (n := n+1) (WShape.lam f hl)) (.lam B F)) (x : WShape n) :
    LE_Interp (ρ.push x.T) (f.app x).T F := by
  have := (WShape.lam_eq_lam' ▸ LE_Interp.weak (x := x.T) H).lam_inv .bvar0
  rwa [SExpr.inst, SExpr.subst_lift', (?_ : Subst.lift_l _ _ = Subst.id), subst_id] at this
  funext i; cases i <;> rfl

/-- Chosen data witnessing how application is transported along a lifted
function-shape inclusion.  Packaging the choices in `Type` lets the
proof-relevant interpreter retain them instead of eliminating `Exists`
proofs into a witness. -/
structure WShapeFun.AppLEData (f : WShapeFun n) (g : WShapeFun n') (x : WShape n) where
  source : WShape n
  source_le : source ≤ x
  source_mem : (source, f.app x) ∈ f
  input : WShape n'
  output : WShape n'
  mem : (input, output) ∈ g
  input_le : input.lift (max n n') ≤ source.lift (max n n')
  output_le : (f.app x).lift (max n n') ≤ output.lift (max n n')

noncomputable def WShapeFun.appLEData (f : WShapeFun n) (g : WShapeFun n')
    (x : WShape n) (hfg : f.lift (max n n') ≤ g.lift (max n n')) :
    WShapeFun.AppLEData f g x := by
  let hs := WShapeFun.app_eq f x
  let source := hs.choose
  have hs' := hs.choose_spec
  have hsource_mem :
      (source.lift (max n n'), (f.app x).lift (max n n')) ∈
        f.lift (max n n') :=
    (WShapeFun.mem_lift (Nat.le_max_left n n')).2
      ⟨source, f.app x, hs'.2, rfl, rfl⟩
  let ht := WShapeFun.LE.def'.1 hfg _ _ hsource_mem
  let inputLift := ht.choose
  let ht' := ht.choose_spec
  let outputLift := ht'.choose
  have ht'' := ht'.choose_spec
  let hu := (WShapeFun.mem_lift (Nat.le_max_right n n')).1 ht''.1
  let input := hu.choose
  let hu' := hu.choose_spec
  let output := hu'.choose
  have hu'' := hu'.choose_spec
  exact {
    source
    source_le := hs'.1
    source_mem := hs'.2
    input
    output
    mem := hu''.1
    input_le := by rw [← hu''.2.1]; exact ht''.2.1
    output_le := by rw [← hu''.2.2]; exact ht''.2.2
  }

/-- A chosen typed argument supplied by a function shape's domain proof. -/
structure WShape.HasDomData (f : WShapeFun n) (a x : WShape n) where
  arg : WShape n
  arg_le : arg ≤ x
  hasType : arg.HasType a
  app_le : f.app x ≤ f.app arg

noncomputable def WShape.HasDom.data {f : WShapeFun n} {a : WShape n}
    (h : WShape.HasDom f a) (x : WShape n) : WShape.HasDomData f a x := by
  let hx := WShape.HasDom.iff.1 h x
  let arg := hx.choose
  have hx' := hx.choose_spec
  exact ⟨arg, hx'.1, hx'.2.1, hx'.2.2⟩

/-- Proof-relevant Pi inversion.  The body callback is transported directly
to the requested argument valuation, so recursive constant provenance below
the binder is retained. -/
noncomputable def LE_Interp.Witness.forallE_inv'
    {b : WShape n} {f : WShapeFun n} {B F : SExpr}
    (H : LE_Interp.Witness ρ
      (WShape.T (n := n + 1) (.forallE b f)) (.forallE B F)) :
    LE_Interp.Witness ρ b.T B ×
      ∀ x, LE_Interp.Witness (ρ.push x.T) (f.app x).T F := by
  let .forallE (n := n') (f := f₁) hb _ hdom hbody hle := H
  have le₁ := Nat.le_max_left n n'
  have le₂ := Nat.le_max_right n n'
  have ⟨hle_b, hle_f⟩ := TShape.LE.forallE_decomp hle
  refine ⟨hb.mono ((TShape.LE.def le₁ le₂).2 hle_b), fun x => ?_⟩
  let ha := WShapeFun.appLEData f f₁ x hle_f
  let hd := WShape.HasDom.data hdom ha.input
  have hinput : ha.input.T ≤ ha.source.T :=
    (TShape.LE.def le₂ le₁).2 ha.input_le
  have hout : (f.app x).T ≤ (f₁.app ha.input).T :=
    ((TShape.LE.def le₁ le₂).2 ha.output_le).trans
      (WShape.LE.T (WShapeFun.app_of_mem ha.mem).2)
  exact (hbody hd.arg hd.hasType).mono_l
      (Valuation.LE.push.2
        ⟨.rfl, hd.arg_le.T.trans (hinput.trans ha.source_le.T)⟩)
    |>.mono (WShape.LE.T hd.app_le)
    |>.mono hout

/-- Proof-relevant lambda inversion at one semantic argument. -/
noncomputable def LE_Interp.Witness.lam_inv'
    {f : WShapeFun n} {hl : f.NonZero} {B F : SExpr}
    (H : LE_Interp.Witness ρ
      (WShape.T (n := n + 1) (WShape.lam f hl)) (.lam B F))
    (x : WShape n) :
    LE_Interp.Witness (ρ.push x.T) (f.app x).T F := by
  let .lam (n := n') (f := f₁) _ hdom hbody hle := H
  have le₁ := Nat.le_max_left n n'
  have le₂ := Nat.le_max_right n n'
  have hle' := hle
  rw [WShape.lam_eq_lam'] at hle'
  have hle_f : f.lift (max n n') ≤ f₁.lift (max n n') :=
    hle'.lam'_decomp
  let ha := WShapeFun.appLEData f f₁ x hle_f
  let hd := WShape.HasDom.data hdom ha.input
  have hinput : ha.input.T ≤ ha.source.T :=
    (TShape.LE.def le₂ le₁).2 ha.input_le
  have hout : (f.app x).T ≤ (f₁.app ha.input).T :=
    ((TShape.LE.def le₁ le₂).2 ha.output_le).trans
      (WShape.LE.T (WShapeFun.app_of_mem ha.mem).2)
  exact (hbody hd.arg hd.hasType).mono_l
      (Valuation.LE.push.2
        ⟨.rfl, hd.arg_le.T.trans (hinput.trans ha.source_le.T)⟩)
    |>.mono (WShape.LE.T hd.app_le)
    |>.mono hout

/-- Proof-relevant Pi inversion together with the retained recursion trees
of the selected domain and body observations.  The result stays in `Prop`:
`RDeepChildren` is proof data, so eliminating it to choose a witness in
`Type` would violate Lean's proof-irrelevance boundary. -/
theorem LE_Interp.Witness.RDeepChildren.forallE_inv'
    {P : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop}
    (hP : ∀ {ρ ρ' m M} (H : LE_Interp.Witness ρ m M)
      (hρ : ρ.LE ρ'), P H → P (H.mono_l hρ))
    {b : WShape n} {f : WShapeFun n} {B F : SExpr}
    {H : LE_Interp.Witness ρ
      (WShape.T (n := n + 1) (.forallE b f)) (.forallE B F)}
    (children : H.RDeepChildren P) :
    (∃ hB : LE_Interp.Witness ρ b.T B, hB.RDeepChildren P) ∧
      ∀ x, ∃ hF : LE_Interp.Witness (ρ.push x.T) (f.app x).T F,
        hF.RDeepChildren P := by
  let .forallE (n := n') (b := b₁) (f := f₁)
      hb hb' hdom hbody hle := H
  cases children with
  | forallE cb cb' cbody =>
    have le₁ := Nat.le_max_left n n'
    have le₂ := Nat.le_max_right n n'
    obtain ⟨hle_b, hle_f⟩ := TShape.LE.forallE_decomp hle
    have hbLe : b.T ≤ b₁.T := (TShape.LE.def le₁ le₂).2 hle_b
    refine ⟨⟨hb.mono hbLe, cb.mono hbLe⟩, fun x => ?_⟩
    let ha := WShapeFun.appLEData f f₁ x hle_f
    let hd := WShape.HasDom.data hdom ha.input
    have hinput : ha.input.T ≤ ha.source.T :=
      (TShape.LE.def le₂ le₁).2 ha.input_le
    have hout : (f.app x).T ≤ (f₁.app ha.input).T :=
      ((TShape.LE.def le₁ le₂).2 ha.output_le).trans
        (WShape.LE.T (WShapeFun.app_of_mem ha.mem).2)
    let hFx := (hbody hd.arg hd.hasType).mono_l
        (Valuation.LE.push.2
          ⟨.rfl, hd.arg_le.T.trans (hinput.trans ha.source_le.T)⟩)
      |>.mono (WShape.LE.T hd.app_le)
      |>.mono hout
    have cFx : hFx.RDeepChildren P :=
      ((cbody hd.arg hd.hasType).mono_l hP
          (Valuation.LE.push.2
            ⟨.rfl, hd.arg_le.T.trans (hinput.trans ha.source_le.T)⟩))
        |>.mono (WShape.LE.T hd.app_le)
        |>.mono hout
    exact ⟨hFx, cFx⟩

/-- Lambda inversion with the exact retained body tree selected at each
semantic argument. -/
theorem LE_Interp.Witness.RDeepChildren.lam_inv'
    {P : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop}
    (hP : ∀ {ρ ρ' m M} (H : LE_Interp.Witness ρ m M)
      (hρ : ρ.LE ρ'), P H → P (H.mono_l hρ))
    {f : WShapeFun n} {hf : f.NonZero} {B F : SExpr}
    {H : LE_Interp.Witness ρ
      (WShape.T (n := n + 1) (WShape.lam f hf)) (.lam B F)}
    (children : H.RDeepChildren P) :
    ∀ x, ∃ hF : LE_Interp.Witness (ρ.push x.T) (f.app x).T F,
      hF.RDeepChildren P := by
  let .lam (n := n') (f := f₁) ha hdom hbody hle := H
  cases children with
  | lam ca cbody =>
    have le₁ := Nat.le_max_left n n'
    have le₂ := Nat.le_max_right n n'
    have hle' := hle
    rw [WShape.lam_eq_lam'] at hle'
    have hle_f : f.lift (max n n') ≤ f₁.lift (max n n') :=
      hle'.lam'_decomp
    intro x
    let haData := WShapeFun.appLEData f f₁ x hle_f
    let hd := WShape.HasDom.data hdom haData.input
    have hinput : haData.input.T ≤ haData.source.T :=
      (TShape.LE.def le₂ le₁).2 haData.input_le
    have hout : (f.app x).T ≤ (f₁.app haData.input).T :=
      ((TShape.LE.def le₁ le₂).2 haData.output_le).trans
        (WShape.LE.T (WShapeFun.app_of_mem haData.mem).2)
    let hFx := (hbody hd.arg hd.hasType).mono_l
        (Valuation.LE.push.2
          ⟨.rfl, hd.arg_le.T.trans (hinput.trans haData.source_le.T)⟩)
      |>.mono (WShape.LE.T hd.app_le)
      |>.mono hout
    have cFx : hFx.RDeepChildren P :=
      ((cbody hd.arg hd.hasType).mono_l hP
          (Valuation.LE.push.2
            ⟨.rfl, hd.arg_le.T.trans (hinput.trans haData.source_le.T)⟩))
        |>.mono (WShape.LE.T hd.app_le)
        |>.mono hout
    exact ⟨hFx, cFx⟩

/-- Instantiate the body selected by proof-relevant Pi inversion.  This is
the exact one-step operation used when a semantic fixed head follows its
registered dependent application telescope. -/
noncomputable def LE_Interp.Witness.forallE_inst
    {b x : WShape n} {f : WShapeFun n} {B F X : SExpr}
    (H : LE_Interp.Witness ρ
      (WShape.T (n := n + 1) (.forallE b f)) (.forallE B F))
    (hX : LE_Interp.Witness ρ x.T X) :
    LE_Interp.Witness ρ (f.app x).T (F.inst X) :=
  (H.forallE_inv'.2 x).inst hX

/-- Instantiate the body selected by proof-relevant lambda inversion. -/
noncomputable def LE_Interp.Witness.lam_inst
    {x : WShape n} {f : WShapeFun n} {hf : f.NonZero} {B F X : SExpr}
    (H : LE_Interp.Witness ρ
      (WShape.T (n := n + 1) (.lam f hf)) (.lam B F))
    (hX : LE_Interp.Witness ρ x.T X) :
    LE_Interp.Witness ρ (f.app x).T (F.inst X) :=
  (H.lam_inv' x).inst hX

/-- Instantiate the exact Pi body while preserving both its retained tree
and the argument's tree. -/
theorem LE_Interp.Witness.RDeepChildren.forallE_inst
    {P : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop}
    (hmono_l : ∀ {ρ ρ' m M} (H : LE_Interp.Witness ρ m M)
      (hρ : ρ.LE ρ'), P H → P (H.mono_l hρ))
    (hclosed : ∀ {ρ ρ' : Valuation} {m M k}
      (H : LE_Interp.Witness ρ m M)
      (cl : ClosedN M k) (hρ : ∀ i < k, ρ i = ρ' i),
      P H → P (H.closed cl hρ))
    {b x : WShape n} {f : WShapeFun n} {B F X : SExpr}
    {H : LE_Interp.Witness ρ
      (WShape.T (n := n + 1) (.forallE b f)) (.forallE B F)}
    (children : H.RDeepChildren P)
    {hX : LE_Interp.Witness ρ x.T X}
    (childrenX : hX.RDeepChildren P) :
    ∃ h : LE_Interp.Witness ρ (f.app x).T (F.inst X),
      h.RDeepChildren P := by
  obtain ⟨hbody, cbody⟩ := (children.forallE_inv' hmono_l).2 x
  exact ⟨hbody.inst hX, cbody.inst hclosed childrenX⟩

/-- Instantiate the exact lambda body while preserving both retained trees. -/
theorem LE_Interp.Witness.RDeepChildren.lam_inst
    {P : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop}
    (hmono_l : ∀ {ρ ρ' m M} (H : LE_Interp.Witness ρ m M)
      (hρ : ρ.LE ρ'), P H → P (H.mono_l hρ))
    (hclosed : ∀ {ρ ρ' : Valuation} {m M k}
      (H : LE_Interp.Witness ρ m M)
      (cl : ClosedN M k) (hρ : ∀ i < k, ρ i = ρ' i),
      P H → P (H.closed cl hρ))
    {x : WShape n} {f : WShapeFun n} {hf : f.NonZero}
    {B F X : SExpr}
    {H : LE_Interp.Witness ρ
      (WShape.T (n := n + 1) (WShape.lam f hf)) (.lam B F)}
    (children : H.RDeepChildren P)
    {hX : LE_Interp.Witness ρ x.T X}
    (childrenX : hX.RDeepChildren P) :
    ∃ h : LE_Interp.Witness ρ (f.app x).T (F.inst X),
      h.RDeepChildren P := by
  obtain ⟨hbody, cbody⟩ := children.lam_inv' hmono_l x
  exact ⟨hbody.inst hX, cbody.inst hclosed childrenX⟩

theorem LE_Interp.Witness.forallE_inst_toInterp
    {b x : WShape n} {f : WShapeFun n} {B F X : SExpr}
    (H : LE_Interp.Witness ρ
      (WShape.T (n := n + 1) (.forallE b f)) (.forallE B F))
    (hX : LE_Interp.Witness ρ x.T X) :
    (H.forallE_inst hX).toInterp =
      H.toInterp.forallE_inv.2 hX.toInterp :=
  Subsingleton.elim _ _

theorem LE_Interp.Witness.lam_inst_toInterp
    {x : WShape n} {f : WShapeFun n} {hf : f.NonZero} {B F X : SExpr}
    (H : LE_Interp.Witness ρ
      (WShape.T (n := n + 1) (.lam f hf)) (.lam B F))
    (hX : LE_Interp.Witness ρ x.T X) :
    (H.lam_inst hX).toInterp =
      (WShape.lam_eq_lam' ▸ H.toInterp).lam_inv hX.toInterp :=
  Subsingleton.elim _ _

/-- A typed interpretation whose term witness, type witness, and complete
`R`-edge recursion trees remain synchronized.  This is the proof-relevant
internal counterpart of `InterpTyped`; it lives in `Prop`, allowing exact
witnesses to be unpacked only while proving semantic propositions. -/
def LE_Interp.Witness.TypedRDeep
    (P : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop)
    (ρ : Valuation) (m : TShape) (M A : SExpr) : Prop :=
  ∃ (m' a : TShape)
      (hM : LE_Interp.Witness ρ m' M)
      (hA : LE_Interp.Witness ρ a A),
    m ≤ m' ∧ m'.HasType a ∧
      hM.RDeepChildren P ∧ hA.RDeepChildren P

/-- A retained witness enlarged to a semantic type observation. -/
def LE_Interp.Witness.TypeRDeep
    (P : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop)
    (ρ : Valuation) (m : TShape) (M : SExpr) : Prop :=
  ∃ (a : TShape) (hA : LE_Interp.Witness ρ a M),
    m ≤ a ∧ a.HasType .type ∧ hA.RDeepChildren P

/-- A retained typing at a syntactic sort supplies the type-shaped package
needed by dependent application. -/
theorem LE_Interp.Witness.TypedRDeep.toType
    (H : LE_Interp.Witness.TypedRDeep P ρ m M (.sort U)) :
    LE_Interp.Witness.TypeRDeep P ρ m M := by
  obtain ⟨m', a, hM, hA, hle, hty, cM, _⟩ := H
  exact ⟨m', hM, hle,
    (TShape.HasType.mono_r hA.toInterp.le_sort .sort hty).toType, cM⟩

/-- Bottom observations carry synchronized trivial term and type trees. -/
theorem LE_Interp.Witness.TypedRDeep.bot
    {P : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop}
    (hm : m ≤ TShape.bot) :
    LE_Interp.Witness.TypedRDeep P ρ m M A := by
  exact ⟨(WShape.bot (n := m.1)).T, (WShape.bot (n := m.1)).T,
    .bot, .bot, hm.trans TShape.bot_eqv.2,
    WShape.HasType.T (.bot' (.bot' .sort)), .bot, .bot⟩

/-- Proof-relevant dependent application soundness.

The function and result-type callbacks return exact witnesses together with
their retained recursion trees.  Application itself introduces no new
semantic `R` edge: it only lifts roots, performs exact Pi instantiation, and
combines the already-retained function and argument trees. -/
theorem LE_Interp.Witness.TypedRDeep.app
    {P : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop}
    (hmono_l : ∀ {ρ ρ' m M} (H : LE_Interp.Witness ρ m M)
      (hρ : ρ.LE ρ'), P H → P (H.mono_l hρ))
    (hclosed : ∀ {ρ ρ' : Valuation} {m M k}
      (H : LE_Interp.Witness ρ m M)
      (cl : ClosedN M k) (hρ : ∀ i < k, ρ i = ρ' i),
      P H → P (H.closed cl hρ))
    (H1 : ∀ {m} (hF : LE_Interp.Witness ρ m F),
      hF.RDeepChildren P →
      LE_Interp.Witness.TypedRDeep P ρ m F (.forallE A B))
    (H2 : ∀ {b} (hB : LE_Interp.Witness ρ b (B.inst X)),
      hB.RDeepChildren P →
      LE_Interp.Witness.TypeRDeep P ρ b (B.inst X))
    {hApp : LE_Interp.Witness ρ m (F.app X)}
    (children : hApp.RDeepChildren P) :
    LE_Interp.Witness.TypedRDeep P ρ m (F.app X) (B.inst X) := by
  by_cases hm : m ≤ .bot
  · exact .bot hm
  cases hApp with
  | bot => exact (hm TShape.bot_eqv.1).elim
  | @app _ nf fShape _ _ _ argShape hfun harg hroot =>
    cases children with
    | app cfun carg =>
      obtain ⟨fShape', typeShape, hF, hPi, leF, htyped, cF, cPi⟩ :=
        H1 hfun cfun
      have hf : ¬fShape' ≤ .bot := fun h => by
        rw [show fShape = .bot from TShape.le_bot.1 (leF.trans h),
          WShape.bot_app] at hroot
        exact hm (hroot.trans TShape.bot_le')
      have hs : ¬typeShape ≤ .bot := fun h => hf (htyped.bot_r' h)
      cases hPi with
      | bot => exact (hs TShape.bot_le').elim
      | forallE hDom hDom' hHasDom hBody hlePi =>
        rename_i npi piDom piDom' piFun
        cases cPi with
        | forallE cDom cDom' cBody =>
          cases hlePi.le_forall with
          | bot hb => exact (hs hb).elim
          | @forallE nType _ _ _ _ hDomLe hFunLe =>
            obtain hbot | ⟨nFun, termFun, htermShape, hLamTy⟩ :=
              htyped.ty_forallE_inv
            · exact (hf (hbot ▸ TShape.LE.rfl)).elim
            subst fShape'
            let k := max (max nFun nType) (max npi nf)
            have hk := Nat.max_le.1 (Nat.le_refl k)
            simp only [Nat.max_le] at hk
            have hPiRoot :
                (WShape.T (n := k + 1)
                  (.forallE (piDom.lift k) (piFun.lift k))) ≤
                (WShape.T (n := npi + 1) (.forallE piDom piFun)) := by
              have h :=
                (TShape.lift_eqv (Nat.succ_le_succ hk.2.1)
                  (a := (WShape.T (n := npi + 1)
                    (.forallE piDom piFun)))).1
              rw [WShape.lift_forallE hk.2.1] at h
              exact h
            let hPiK : LE_Interp.Witness ρ
                (WShape.T (n := k + 1)
                  (.forallE (piDom.lift k) (piFun.lift k)))
                (.forallE A B) :=
              .forallE hDom hDom' hHasDom hBody hPiRoot
            have cPiK : hPiK.RDeepChildren P := by
              exact .forallE cDom cDom' cBody
            let hArgK := harg.mono (TShape.lift_eqv hk.2.2).1
            have cArgK : hArgK.RDeepChildren P := carg.mono _
            obtain ⟨hBinst, cBinst⟩ :=
              cPiK.forallE_inst hmono_l hclosed cArgK
            obtain ⟨resultType, hType, leType, hTypeType, cType⟩ :=
              H2 hBinst cBinst
            have hLamTy :=
              (TShape.HasTypeLam.def hk.1.1 hk.1.2).1 hLamTy
            have hLamDom := WShape.HasDom.iff.1 hLamTy.2.1
            have ⟨_, hArgLe, hArgTy, hAppLe⟩ :=
              hLamDom (argShape.lift k)
            have hFuncRoot : (WShape.lam' (termFun.lift k)).T ≤
                (WShape.lam' termFun).T := by
              have h := (TShape.lift_eqv
                (Nat.succ_le_succ hk.1.1)
                (a := (WShape.lam' termFun).T)).1
              rw [WShape.lift_lam' hk.1.1] at h
              exact h
            have hFuncUp : (WShape.lam' termFun).T ≤
                (WShape.lam' (termFun.lift k)).T := by
              have h := (TShape.lift_eqv
                (Nat.succ_le_succ hk.1.1)
                (a := (WShape.lam' termFun).T)).2
              rw [WShape.lift_lam' hk.1.1] at h
              exact h
            let hFuncK := hF.mono hFuncRoot
            have cFuncK : hFuncK.RDeepChildren P := cF.mono hFuncRoot
            let hTerm : LE_Interp.Witness ρ
                ((WShape.lam' (termFun.lift k)).app
                  (argShape.lift k)).T (F.app X) :=
              .app hFuncK hArgK .rfl
            have cTerm : hTerm.RDeepChildren P := .app cFuncK cArgK
            refine ⟨_, resultType, hTerm, hType, ?_, ?_, cTerm, cType⟩
            · refine hroot.trans <| TShape.app_mono ?_
                (TShape.lift_eqv hk.2.2).2
              exact leF.trans hFuncUp
            · have hFunLe :=
                (TShapeFun.LE.def hk.1.2 hk.2.1).1 hFunLe
              rw [WShape.lam'_app]
              refine hTypeType.mono_r
                ((WShapeFun.app_mono_l hFunLe _).trans
                  (WShapeFun.app_mono_r hArgLe) |>.T.trans leType) ?_
              exact (WShape.HasTypeLam.iff.1 hLamTy).2.2 _ hArgTy
                |>.mono_l (WShapeFun.app_mono_r hArgLe) hAppLe |>.T

inductive Valuation.Fits : (Γ Δ : List SExpr) → Valuation → Prop
  | nil : Valuation.Fits Γ Γ .nil
  | cons : Valuation.Fits Γ Δ ρ →
    (∀ {a}, LE_Interp ρ a A → ∃ a', a ≤ a' ∧ LE_Interp ρ a' A ∧ a'.HasType .type) →
    LE_Interp ρ a A → x.HasType a →
    Valuation.Fits Γ (A::Δ) (ρ.push x)

def InterpTyped (ρ : Valuation) (m : TShape) (M A : SExpr) :=
  ∃ m' a, m ≤ m' ∧ LE_Interp ρ m' M ∧ LE_Interp ρ a A ∧ m'.HasType a

/-- Forget retained recursion data and recover the public typed
interpretation package. -/
theorem LE_Interp.Witness.TypedRDeep.toInterpTyped
    (H : LE_Interp.Witness.TypedRDeep P ρ m M A) :
    InterpTyped ρ m M A := by
  obtain ⟨m', a, hM, hA, hle, hty, _, _⟩ := H
  exact ⟨m', a, hle, hM.toInterp, hA.toInterp, hty⟩

theorem InterpTyped.bot : InterpTyped ρ (WShape.T (n := n) .bot) M A := by
  refine ⟨WShape.T (n := n) .bot, WShape.T (n := n) .bot, TShape.bot_le', .bot, .bot, ?_⟩
  exact WShape.HasType.T_iff.2 <| .bot' <| .bot' .sort

theorem InterpTyped.mk (le : m ≤ m') (h_m : LE_Interp ρ m' M) (h_a : LE_Interp ρ a A)
    (h_type : m'.HasType a) : InterpTyped ρ m M A := ⟨_, _, le, h_m, h_a, h_type⟩

theorem InterpTyped.out (H : InterpTyped ρ m M A) :
    ∃ n', ∃ m' : WShape n', ∃ a : WShape n', m.1 ≤ n' ∧ m ≤ m'.T ∧
      LE_Interp ρ m'.T M ∧ LE_Interp ρ a.T A ∧ m'.HasType a := by
  obtain ⟨m', a, hle, hm, ha, hty⟩ := H
  let k := max m.1 (max m'.1 a.1)
  have hk := Nat.max_le.1 (Nat.le_refl k); simp only [Nat.max_le] at hk
  refine ⟨k, m'.2.lift k, a.2.lift k, hk.1, ?_, hm.lift hk.2.1, ha.lift hk.2.2, ?_⟩
  · exact hle.trans (TShape.lift_eqv hk.2.1).2
  · exact (TShape.HasType.def hk.2.1 hk.2.2).1 hty

theorem InterpTyped.hsort' {ρ A U}
    (H : ∀ {a}, LE_Interp ρ a A → InterpTyped ρ a A (.sort U))
    {a} (h : LE_Interp ρ a A) :
    ∃ a', a ≤ a' ∧ LE_Interp ρ a' A ∧ a'.HasType (.sort (U ≠ .zero)) :=
  have ⟨_, _, h1, h2, h3, h4⟩ := H h; ⟨_, h1, h2, .mono_r h3.le_sort .sort h4⟩

theorem InterpTyped.hsort {ρ A U}
    (H : ∀ {a}, LE_Interp ρ a A → InterpTyped ρ a A (.sort U))
    {a} (h : LE_Interp ρ a A) : ∃ a', a ≤ a' ∧ LE_Interp ρ a' A ∧ a'.HasType .type :=
  have ⟨a', h1, h2, h3⟩ := hsort' H h; ⟨a', h1, h2, h3.toType⟩

theorem LE_Interp.sound_bot :
    (LE_Interp ρ (WShape.T (n := n) .bot) M ↔ LE_Interp ρ (WShape.T (n := n) .bot) N) ∧
    (LE_Interp ρ (WShape.T (n := n) .bot) M → InterpTyped ρ (WShape.T (n := n) .bot) M A) :=
  ⟨⟨fun _ => .bot, fun _ => .bot⟩, fun _ => .bot⟩

structure LE_Interp.Witness.RDeepChildren.Laws
    (P : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop) : Prop
    extends LE_Interp.Witness.RDeepChildren.JoinLaws P where
  closed : ∀ {ρ ρ' : Valuation} {m M k}
    (H : LE_Interp.Witness ρ m M)
    (cl : ClosedN M k) (hρ : ∀ i < k, ρ i = ρ' i),
    P H → P (H.closed cl hρ)

/-- The transport predicate used when retained semantic typing only needs the
exact witness tree, while a separate consumer follows recursive `R` edges. -/
theorem LE_Interp.Witness.RDeepChildren.Laws.true :
    LE_Interp.Witness.RDeepChildren.Laws (fun _ => True) where
  bot := trivial
  mono := by intros; trivial
  mono_l := by intros; trivial
  join := by intros; trivial
  closed := by intros; trivial

/-- The free provenance-preserving transport closure of a recursive-result
predicate.

Semantic typing does not need the final consumer itself to be closed under
joins and valuation changes.  It only needs to remember how a selected
witness was obtained from an exact recursive `R` child.  This predicate
records precisely those admissible operations.  Its `Laws` instance below
is structural, so no consumer theorem is assumed while an enlarged or joined
witness is being constructed. -/
inductive LE_Interp.Witness.TransportClosure
    (P : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop) :
    ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop where
  | base {H : LE_Interp.Witness ρ m M} :
      P H → TransportClosure P H
  | bot : TransportClosure P
      (LE_Interp.Witness.bot (ρ := ρ) (n := n) (M := M))
  | mono {H : LE_Interp.Witness ρ m' M} (hle : m ≤ m') :
      TransportClosure P H → TransportClosure P (H.mono hle)
  | mono_l {H : LE_Interp.Witness ρ m M} (hρ : ρ.LE ρ') :
      TransportClosure P H → TransportClosure P (H.mono_l hρ)
  | join {H₁ : LE_Interp.Witness ρ m₁ M}
      {H₂ : LE_Interp.Witness ρ m₂ M}
      (HJ : LE_Interp.Witness ρ (m₁.join m₂) M) :
      TransportClosure P H₁ → TransportClosure P H₂ →
        TransportClosure P HJ
  | closed {ρ' : Valuation} {H : LE_Interp.Witness ρ m M}
      (cl : ClosedN M k) (hρ : ∀ i < k, ρ i = ρ' i) :
      TransportClosure P H → TransportClosure P (H.closed cl hρ)

/-- The transport closure is the free `RDeepChildren.Laws` algebra over
`P`.  In particular, `P` itself need not provide a join law. -/
theorem LE_Interp.Witness.TransportClosure.laws :
    LE_Interp.Witness.RDeepChildren.Laws
      (LE_Interp.Witness.TransportClosure P) where
  bot := .bot
  mono := fun _ hle h => .mono hle h
  mono_l := fun _ hρ h => .mono_l hρ h
  join := fun _ _ HJ h₁ h₂ => .join HJ h₁ h₂
  closed := fun _ cl hρ h => .closed cl hρ h

/-- Anchor every exact recursive `R` result in the free transport closure
without changing the retained evaluator tree. -/
theorem LE_Interp.Witness.RDeepChildren.toTransportClosure
    {H : LE_Interp.Witness ρ m M}
    (children : H.RDeepChildren P) :
    H.RDeepChildren (LE_Interp.Witness.TransportClosure P) :=
  children.map (fun _ h => .base h)

/-- Structural semantic recursion whose step receives transport-stable
provenance rather than demanding transport laws from its final consumer.

This is the evaluator-coherent replacement for threading a consumer result
unchanged through `recNatRDeep`: actual `R` children are marked by `base`,
and every later semantic enlargement records its derivation in
`TransportClosure`. -/
theorem LE_Interp.Witness.recRDeepTransport
    {P : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop}
    (step : ∀ {ρ m M} (H : LE_Interp.Witness ρ m M),
      H.RDeepChildren (LE_Interp.Witness.TransportClosure P) → P H)
    {ρ m M} (H : LE_Interp.Witness ρ m M) : P H := by
  apply H.recRDeep
  intro ρ m M H children
  exact step H children.toTransportClosure

/-- Semantic-first recursion with provenance-checked Nat restarts.

Genuine evaluator `R` edges receive the result at every Nat index by
structural descent through the exact witness.  A strictly smaller Nat index
may restart at another witness only when the caller supplies a complete tree
whose recursive edges are traced back to those genuine results through
`TransportClosure`.  Thus root/valuation/closed/instantiation/join transports
remain available without admitting an unrelated same-index restart. -/
theorem LE_Interp.Witness.recRDeepNatTransport
    {Q : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Nat → Prop}
    (step : ∀ (d : Nat)
        {ρ m M} (hM : LE_Interp.Witness ρ m M),
      hM.RDeepChildren
        (LE_Interp.Witness.TransportClosure (fun hM' => ∀ d, Q hM' d)) →
      (∀ (d' : Nat), d' < d →
        ∀ {ρ m M} (hM' : LE_Interp.Witness ρ m M),
          hM'.RDeepChildren
            (LE_Interp.Witness.TransportClosure
              (fun hM'' => ∀ d, Q hM'' d)) →
          Q hM' d') →
      Q hM d)
    {ρ m M} (hM : LE_Interp.Witness ρ m M) : ∀ d, Q hM d := by
  let P : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop :=
    fun hM => ∀ d, Q hM d
  apply hM.recRDeepTransport (P := P)
  intro ρ m M hM children
  let motive := fun d =>
    ∀ {ρ m M} (hM : LE_Interp.Witness ρ m M),
      hM.RDeepChildren
        (LE_Interp.Witness.TransportClosure P) → Q hM d
  have go : ∀ d, motive d := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
      intro ρ m M hM children
      exact step d hM children
        (fun d' hd' {_ _ _} hM' children' =>
          ih d' hd' hM' children')
  exact fun d => go d hM children

/-- The inspectable recursive seed available at one Nat index.

The left injection is reserved for a genuine semantic `R` child and carries
its structurally recursive result at every index.  The right injection is a
local seed at exactly `d`; it is what a strictly-smaller syntax derivation may
attach after rebuilding a freshly selected witness's evaluator tree. -/
abbrev LE_Interp.Witness.NatSeed
    (Q : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Nat → Prop)
    (d : Nat) {ρ m M} (H : LE_Interp.Witness ρ m M) : Prop :=
  (∀ k, Q H k) ∨ Q H d

/-- Free semantic transport closure over a depth-local recursive seed.

This predicate is used inside retained semantic typing, where root,
valuation, closed-term, and compatible-join transports must be recorded.
The outer consumer algebra receives `NatSeed` instead, so it can inspect why
an actual evaluator edge is justified without assuming that the final
consumer is closed under every semantic transport. -/
abbrev LE_Interp.Witness.NatProvenance
    (Q : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Nat → Prop)
    (d : Nat) {ρ m M} (H : LE_Interp.Witness ρ m M) : Prop :=
  LE_Interp.Witness.TransportClosure
    (LE_Interp.Witness.NatSeed Q d) H

/-- Semantic-first/Nat-second recursion with depth-local provenance.

Every actual evaluator edge is injected on the all-depth side of `NatSeed`.
At a strict Nat decrease, a restarted witness may instead
carry local seeds at that smaller index.  This is the guarded form needed by
conversion: folding a definition may point a new constant edge at the
current witness, but it can attach only the result already obtained from the
smaller endpoint derivation, never the all-depth result under construction. -/
theorem LE_Interp.Witness.recRDeepNatProvenance
    {Q : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Nat → Prop}
    (step : ∀ (d : Nat)
        {ρ m M} (hM : LE_Interp.Witness ρ m M),
      hM.RDeepChildren (LE_Interp.Witness.NatSeed Q d) →
      (∀ (d' : Nat), d' < d →
        ∀ {ρ m M} (hM' : LE_Interp.Witness ρ m M),
          hM'.RDeepChildren
            (LE_Interp.Witness.NatSeed Q d') →
          Q hM' d') →
      Q hM d)
    {ρ m M} (hM : LE_Interp.Witness ρ m M) : ∀ d, Q hM d := by
  let P : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop :=
    fun hM => ∀ d, Q hM d
  apply hM.recRDeep (P := P)
  intro ρ m M hM children
  let motive := fun d =>
    ∀ {ρ m M} (hM : LE_Interp.Witness ρ m M),
      hM.RDeepChildren (LE_Interp.Witness.NatSeed Q d) →
        Q hM d
  have go : ∀ d, motive d := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
      intro ρ m M hM childrenAt
      exact step d hM childrenAt
        (fun d' hd' {_ _ _} hM' children' =>
          ih d' hd' hM' children')
  exact fun d => go d hM
    (children.map (fun _ h => .inl h))

/-- Every exact witness retains its complete constructor tree when recursive
`R` edges carry no additional consumer data. -/
theorem LE_Interp.Witness.RDeepChildren.trivial
    (H : LE_Interp.Witness ρ m M) :
    H.RDeepChildren (fun _ => True) := by
  induction H with
  | bot => exact .bot
  | bvar => exact .bvar
  | sort => exact .sort
  | app _ _ _ ihf iha => exact .app ihf iha
  | lam _ _ _ _ iha ihbody => exact .lam iha ihbody
  | forallE _ _ _ _ _ ihb ihb' ihbody =>
    exact .forallE ihb ihb' ihbody
  | const _ _ _ _ _ _ _ ihA ihR =>
    exact .const ihA (fun _ _ _ => True.intro) ihR

noncomputable def LE_Interp.Witness.RDeepChildren.choose
    (H : ∃ h : LE_Interp.Witness ρ m M, h.RDeepChildren P) :
    {h : LE_Interp.Witness ρ m M // h.RDeepChildren P} :=
  Classical.choice (by
    obtain ⟨h, ch⟩ := H
    exact ⟨⟨h, ch⟩⟩)

theorem LE_Interp.Witness.TypedRDeep.mono
    (hle : m ≤ m')
    (H : LE_Interp.Witness.TypedRDeep P ρ m' M A) :
    LE_Interp.Witness.TypedRDeep P ρ m M A := by
  obtain ⟨mm, aa, hM, hA, hm, hty, cM, cA⟩ := H
  exact ⟨mm, aa, hM, hA, hle.trans hm, hty, cM, cA⟩

theorem LE_Interp.Witness.TypedRDeep.weak
    (hclosed : ∀ {ρ ρ' : Valuation} {m M k}
      (H : LE_Interp.Witness ρ m M)
      (cl : ClosedN M k) (hρ : ∀ i < k, ρ i = ρ' i),
      P H → P (H.closed cl hρ))
    (H : LE_Interp.Witness.TypedRDeep P ρ m M A) :
    LE_Interp.Witness.TypedRDeep P (ρ.push x) m M.lift A.lift := by
  obtain ⟨mm, aa, hM, hA, hm, hty, cM, cA⟩ := H
  exact ⟨mm, aa, hM.weak, hA.weak, hm, hty,
    cM.weak hclosed, cA.weak hclosed⟩

theorem LE_Interp.Witness.TypedRDeep.out
    (H : LE_Interp.Witness.TypedRDeep P ρ m M A) :
    ∃ n', ∃ m' a' : WShape n', ∃
        (hM : LE_Interp.Witness ρ m'.T M)
        (hA : LE_Interp.Witness ρ a'.T A),
      m.1 ≤ n' ∧ m ≤ m'.T ∧ m'.HasType a' ∧
        hM.RDeepChildren P ∧ hA.RDeepChildren P := by
  obtain ⟨m', a', hM, hA, hm, hty, cM, cA⟩ := H
  let k := max m.1 (max m'.1 a'.1)
  have hk := Nat.max_le.1 (Nat.le_refl k)
  simp only [Nat.max_le] at hk
  let mw := m'.2.lift k
  let aw := a'.2.lift k
  let hMk := hM.mono (TShape.lift_eqv hk.2.1).1
  let hAk := hA.mono (TShape.lift_eqv hk.2.2).1
  exact ⟨k, mw, aw, hMk, hAk, hk.1,
    hm.trans (TShape.lift_eqv hk.2.1).2,
    (TShape.HasType.def hk.2.1 hk.2.2).1 hty,
    cM.mono _, cA.mono _⟩

/-- Proof-relevant lambda soundness with every recursive constant edge
retained in both the term family and its dependent result-type family. -/
theorem LE_Interp.Witness.TypedRDeep.lam
    (laws : LE_Interp.Witness.RDeepChildren.Laws P)
    (H2 : ∀ {a x} (hA : LE_Interp.Witness ρ a A),
      hA.RDeepChildren P → x.HasType a →
      ∀ {e} (hF : LE_Interp.Witness (ρ.push x) e F),
        hF.RDeepChildren P →
        LE_Interp.Witness.TypedRDeep P (ρ.push x) e F B)
    {hLam : LE_Interp.Witness ρ m (A.lam F)}
    (children : hLam.RDeepChildren P) :
    LE_Interp.Witness.TypedRDeep P ρ m (A.lam F) (A.forallE B) := by
  by_cases hm : m ≤ .bot
  · exact .bot hm
  cases hLam with
  | bot => exact (hm TShape.bot_eqv.1).elim
  | @lam _ n a _ f _ _ hA hdom hbody hroot =>
    cases children with
    | lam cA cbody =>
      suffices ∀ (fl : List (WShape n × WShape n)),
          (∀ p ∈ fl, p ∈ f ∧
            ∃ h : LE_Interp.Witness (ρ.push p.1.T) p.2.T F,
              h.RDeepChildren P) →
          ∃ n', n ≤ n' ∧ ∀ k, n' ≤ k →
            ∃ f' b : WShapeFun k,
              (∀ p ∈ fl,
                WShapeFun.single (p.1.lift k) (p.2.lift k) ≤ f') ∧
              WShape.HasDom f' (a.lift k) ∧
              WShape.HasDom b (a.lift k) ∧
              (∀ x, x.HasType (a.lift k) →
                ∃ h : LE_Interp.Witness (ρ.push x.T) (f'.app x).T F,
                  h.RDeepChildren P) ∧
              (∀ x, x.HasType (a.lift k) →
                ∃ h : LE_Interp.Witness (ρ.push x.T) (b.app x).T B,
                  h.RDeepChildren P) ∧
              (∀ x, x.HasType (a.lift k) →
                (f'.app x).HasType (b.app x)) by
        have hElems : ∀ p ∈ f.elems, p ∈ f ∧
            ∃ h : LE_Interp.Witness (ρ.push p.1.T) p.2.T F,
              h.RDeepChildren P := by
          intro p hp
          have hpMem := WShapeFun.mem_elems.1 hp
          have ⟨x', hxle, hxty, happ⟩ := WShape.HasDom.iff.1 hdom p.1
          let hFx := (hbody x' hxty).mono_l
              (Valuation.LE.push.2 ⟨.rfl, hxle.T⟩)
            |>.mono ((WShapeFun.app_of_mem hpMem).2.trans happ).T
          have cFx : hFx.RDeepChildren P :=
            ((cbody x' hxty).mono_l laws.mono_l
                (Valuation.LE.push.2 ⟨.rfl, hxle.T⟩))
              |>.mono ((WShapeFun.app_of_mem hpMem).2.trans happ).T
          exact ⟨hpMem, hFx, cFx⟩
        obtain ⟨n', le, build⟩ := this f.elems hElems
        obtain ⟨f', b, hsingle, hd1, hd2, hi1, hi2, hi3⟩ :=
          build _ (Nat.le_refl _)
        let hAK := hA.mono (TShape.lift_eqv le).1
        have cAK : hAK.RDeepChildren P := cA.mono _
        let bodyTerm := fun x hx =>
          (LE_Interp.Witness.RDeepChildren.choose (hi1 x hx)).1
        let bodyType := fun x hx =>
          (LE_Interp.Witness.RDeepChildren.choose (hi2 x hx)).1
        have htermRoot : m ≤ (WShape.lam' f').T := by
          refine hroot.trans <|
            (TShape.LE.lift_l (Nat.succ_le_succ le)).2
              (WShape.lift_lam' le ▸ ?_)
          refine WShape.lam'_le_lam'.2 <|
            WShapeFun.LE.def'.2 fun x y hxy => ?_
          obtain ⟨x₀, y₀, h₀, rfl, rfl⟩ :=
            (WShapeFun.mem_lift le).1 hxy
          exact WShapeFun.single_le.1
            (hsingle _ (WShapeFun.mem_elems.2 h₀))
        let hTerm : LE_Interp.Witness ρ (WShape.lam' f').T (A.lam F) :=
          .lam hAK hd1 bodyTerm .rfl
        let hType : LE_Interp.Witness ρ
            ((a.lift n').forallE b).T (A.forallE B) :=
          .forallE hAK hAK hd2 bodyType .rfl
        have cTerm : hTerm.RDeepChildren P :=
          .lam cAK (fun x hx =>
            (LE_Interp.Witness.RDeepChildren.choose (hi1 x hx)).2)
        have cType : hType.RDeepChildren P :=
          .forallE cAK cAK (fun x hx =>
            (LE_Interp.Witness.RDeepChildren.choose (hi2 x hx)).2)
        exact ⟨_, _, hTerm, hType, htermRoot,
          WShape.HasType.T <| .lam <| WShape.HasTypeLam.iff.2
            ⟨WShape.HasTypePi.iff.2
                ⟨hd2, fun x hx => (hi3 x hx).isType⟩,
              hd1, hi3⟩,
          cTerm, cType⟩
      intro fl Hfl
      induction fl with
      | nil =>
        refine ⟨n, Nat.le_refl _, fun k hk => ?_⟩
        have ha : (a.lift k).HasType .type :=
          WShape.lift_type.symm ▸
            (WShape.HasType.lift hk).2 hdom.isType
        refine ⟨.bot, .bot, nofun, .bot ha, .bot ha,
          fun x hx => ?_,
          fun x hx => ?_,
          fun x hx => ?_⟩
        · rw [WShapeFun.bot_app]
          exact ⟨.bot, .bot⟩
        · rw [WShapeFun.bot_app]
          exact ⟨.bot, .bot⟩
        simp [WShapeFun.bot_app]
        exact .bot' (.bot' .sort)
      | cons p fl ih =>
        have ⟨⟨hpMem, hpBody⟩, Htail⟩ :=
          List.forall_mem_cons.1 Hfl
        have ⟨k₁, le1, H1⟩ := ih Htail
        obtain ⟨x', x'le, hx', happ⟩ :=
          WShape.HasDom.iff.1 hdom p.1
        obtain ⟨hp, cp⟩ := hpBody
        obtain ⟨nBody, e', b', he', hb', leBody, le_e,
          heb', ce', cb'⟩ :=
          (H2 hA cA (WShape.HasType.T hx')
            (hbody x' hx') (cbody x' hx')).out
        refine ⟨max k₁ nBody,
          Nat.le_trans le1 (Nat.le_max_left ..),
          fun k le' => ?_⟩
        have ⟨le₁, le₂⟩ := Nat.max_le.1 le'
        have le_nk : n ≤ k := Nat.le_trans le1 le₁
        have le_ek := le₂
        have le_bk := le₂
        obtain ⟨f₁, b₁, hsingle₁, hd1₁, hd2₁,
          hi1₁, hi2₁, hi3₁⟩ := H1 _ le₁
        let sf := WShapeFun.single (x'.lift k) (e'.lift k)
        let sb := WShapeFun.single (x'.lift k) (b'.lift k)
        have hi1Any z : ∃ h : LE_Interp.Witness
            (ρ.push z.T) (f₁.app z).T F, h.RDeepChildren P := by
          obtain ⟨z', z'le, z'ht, z'app⟩ :=
            WShape.HasDom.iff.1 hd1₁ z
          obtain ⟨hz, cz⟩ := hi1₁ z' z'ht
          let hz' := hz.mono z'app.T |>.mono_l
            (Valuation.LE.push.2 ⟨.rfl, z'le.T⟩)
          exact ⟨hz', (cz.mono z'app.T).mono_l laws.mono_l
            (Valuation.LE.push.2 ⟨.rfl, z'le.T⟩)⟩
        have hi2Any z : ∃ h : LE_Interp.Witness
            (ρ.push z.T) (b₁.app z).T B, h.RDeepChildren P := by
          obtain ⟨z', z'le, z'ht, z'app⟩ :=
            WShape.HasDom.iff.1 hd2₁ z
          obtain ⟨hz, cz⟩ := hi2₁ z' z'ht
          let hz' := hz.mono z'app.T |>.mono_l
            (Valuation.LE.push.2 ⟨.rfl, z'le.T⟩)
          exact ⟨hz', (cz.mono z'app.T).mono_l laws.mono_l
            (Valuation.LE.push.2 ⟨.rfl, z'le.T⟩)⟩
        have hxLift : x'.T ≤ (x'.lift k).T := by
          apply (TShape.LE.lift_l (a := x'.T)
            (b := (x'.lift k).T) le_nk).2
          exact WShape.LE.rfl
        let heK : LE_Interp.Witness (ρ.push (x'.lift k).T)
            (e'.lift k).T F :=
          he'.mono (TShape.lift_eqv le_ek).1 |>.mono_l
            (Valuation.LE.push.2 ⟨.rfl, hxLift⟩)
        have ceK : heK.RDeepChildren P :=
          (ce'.mono (TShape.lift_eqv le_ek).1).mono_l laws.mono_l
            (Valuation.LE.push.2 ⟨.rfl, hxLift⟩)
        let hbK : LE_Interp.Witness (ρ.push (x'.lift k).T)
            (b'.lift k).T B :=
          hb'.mono (TShape.lift_eqv le_bk).1 |>.mono_l
            (Valuation.LE.push.2 ⟨.rfl, hxLift⟩)
        have cbK : hbK.RDeepChildren P :=
          (cb'.mono (TShape.lift_eqv le_bk).1).mono_l laws.mono_l
            (Valuation.LE.push.2 ⟨.rfl, hxLift⟩)
        have hc : f₁.Compat sf := by
          rw [WShapeFun.compat_single]
          intro ⟨xj, yj⟩ hmem hc
          obtain ⟨z, hz1, hz2⟩ := WShape.Compat.iff.1 hc
          have sfApp : sf.app z = e'.lift k := by
            rw [WShapeFun.single_app, if_pos hz2]
          obtain ⟨hz, _⟩ := hi1Any z
          exact .mono
            ((WShapeFun.app_of_mem hmem).2.trans
              (WShapeFun.app_mono_r hz1))
            (sfApp ▸ WShape.LE.rfl) <|
            WShape.Compat.T_iff.2 <|
              hz.toInterp.compat
                (sfApp ▸ heK.toInterp.mono_l
                  (Valuation.LE.push.2 ⟨.rfl, hz2.T⟩))
        have hcb : b₁.Compat sb := by
          rw [WShapeFun.compat_single]
          intro ⟨xj, yj⟩ hmem hc
          obtain ⟨z, hz1, hz2⟩ := WShape.Compat.iff.1 hc
          have sbApp : sb.app z = b'.lift k := by
            rw [WShapeFun.single_app, if_pos hz2]
          obtain ⟨hz, _⟩ := hi2Any z
          exact .mono
            ((WShapeFun.app_of_mem hmem).2.trans
              (WShapeFun.app_mono_r hz1))
            (sbApp ▸ WShape.LE.rfl) <|
            WShape.Compat.T_iff.2 <|
              hz.toInterp.compat
                (sbApp ▸ hbK.toInterp.mono_l
                  (Valuation.LE.push.2 ⟨.rfl, hz2.T⟩))
        have jf := WShapeFun.Join.mk hc
        have jb := WShapeFun.Join.mk hcb
        refine ⟨f₁.join sf, b₁.join sb, ?_, ?_, ?_,
          fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
        · refine List.forall_mem_cons.2 ⟨?_, fun r hr =>
            (hsingle₁ r hr).trans jf.le.1⟩
          refine (WShapeFun.single_le.2
            ⟨_, _, WShapeFun.mem_single.2 (.inl rfl), ?_, ?_⟩).trans
              jf.le.2
          · exact WShape.lift_mono le_nk x'le
          · exact WShape.lift_mono le_nk
              ((WShapeFun.app_of_mem hpMem).2.trans happ)
              |>.trans ((TShape.LE.def le_nk le_ek).1 le_e)
        · refine hd1₁.join' ?_ jf (WShape.join_self.2 ⟨.rfl, .rfl⟩)
          exact WShape.HasDom.single.2 <|
            .inl <| (WShape.HasType.lift le_nk).2 hx'
        · refine hd2₁.join' ?_ jb (WShape.join_self.2 ⟨.rfl, .rfl⟩)
          exact WShape.HasDom.single.2 <|
            .inl <| (WShape.HasType.lift le_nk).2 hx'
        · obtain ⟨hz, cz⟩ := hi1Any x
          have hs : ∃ h : LE_Interp.Witness
              (ρ.push x.T) (sf.app x).T F, h.RDeepChildren P := by
            dsimp only [sf]
            by_cases hmatch : x'.lift k ≤ x
            · rw [WShapeFun.single_app, if_pos hmatch]
              exact ⟨heK.mono_l
                  (Valuation.LE.push.2 ⟨.rfl, WShape.LE.T hmatch⟩),
                ceK.mono_l laws.mono_l
                  (Valuation.LE.push.2 ⟨.rfl, WShape.LE.T hmatch⟩)⟩
            · rw [WShapeFun.single_app, if_neg hmatch]
              exact ⟨.bot, .bot⟩
          obtain ⟨hs, cs⟩ := hs
          obtain ⟨_, joined⟩ := cz.compat_join laws.toJoinLaws
            .rfl cs
          have hJ := LE_Interp.Witness.RDeepChildren.choose joined
          have jx := jf.app_l x
          have hcRoot : (f₁.app x).T.Compat (sf.app x).T :=
            WShape.Compat.T_iff.1 jx.compat
          have jxT : TShape.Join (f₁.app x).T (sf.app x).T
              ((f₁.join sf).app x).T := jx.T
          have hin : ((f₁.join sf).app x).T ≤
              (f₁.app x).T.join (sf.app x).T :=
            (jxT _).2 (TShape.Join.mk hcRoot).le
          exact ⟨hJ.1.mono hin, hJ.2.mono hin⟩
        · obtain ⟨hz, cz⟩ := hi2Any x
          have hs : ∃ h : LE_Interp.Witness
              (ρ.push x.T) (sb.app x).T B, h.RDeepChildren P := by
            dsimp only [sb]
            by_cases hmatch : x'.lift k ≤ x
            · rw [WShapeFun.single_app, if_pos hmatch]
              exact ⟨hbK.mono_l
                  (Valuation.LE.push.2 ⟨.rfl, WShape.LE.T hmatch⟩),
                cbK.mono_l laws.mono_l
                  (Valuation.LE.push.2 ⟨.rfl, WShape.LE.T hmatch⟩)⟩
            · rw [WShapeFun.single_app, if_neg hmatch]
              exact ⟨.bot, .bot⟩
          obtain ⟨hs, cs⟩ := hs
          obtain ⟨_, joined⟩ := cz.compat_join laws.toJoinLaws
            .rfl cs
          have hJ := LE_Interp.Witness.RDeepChildren.choose joined
          have jx := jb.app_l x
          have hcRoot : (b₁.app x).T.Compat (sb.app x).T :=
            WShape.Compat.T_iff.1 jx.compat
          have jxT : TShape.Join (b₁.app x).T (sb.app x).T
              ((b₁.join sb).app x).T := jx.T
          have hin : ((b₁.join sb).app x).T ≤
              (b₁.app x).T.join (sb.app x).T :=
            (jxT _).2 (TShape.Join.mk hcRoot).le
          exact ⟨hJ.1.mono hin, hJ.2.mono hin⟩
        · have hT1 := hi3₁ x hx
          have hT2 : (sf.app x).HasType (sb.app x) := by
            rw [WShapeFun.single_app, WShapeFun.single_app]
            split
            · exact (WShape.HasType.lift le₂).2 heb'
            · exact .bot' (.bot' .sort)
          have jbx := jb.app_l x
          have hJT := hT1.isType.join' jbx hT2.isType
          exact (hJT.mono_r jbx.le.1 hT1).join' (jf.app_l x)
            (hJT.mono_r jbx.le.2 hT2)

/-- Proof-relevant dependent-function type soundness.  The observed body
family is saturated while retaining the exact witness selected at every
point, and the two domain observations in the input witness are joined
without discarding either recursive tree. -/
theorem LE_Interp.Witness.TypedRDeep.forallE
    (laws : LE_Interp.Witness.RDeepChildren.Laws P)
    (H1 : ∀ {a} (hA : LE_Interp.Witness ρ a A),
      hA.RDeepChildren P →
      LE_Interp.Witness.TypedRDeep P ρ a A (.sort u))
    (H2 : ∀ {a x} (hA : LE_Interp.Witness ρ a A),
      hA.RDeepChildren P → x.HasType a →
      ∀ {e} (hB : LE_Interp.Witness (ρ.push x) e B),
        hB.RDeepChildren P →
        LE_Interp.Witness.TypedRDeep P (ρ.push x) e B (.sort v))
    {hPi : LE_Interp.Witness ρ m (A.forallE B)}
    (children : hPi.RDeepChildren P) :
    LE_Interp.Witness.TypedRDeep P ρ m (A.forallE B)
      (.sort (.imax u v)) := by
  by_cases hm : m ≤ .bot
  · exact .bot hm
  cases hPi with
  | bot => exact (hm TShape.bot_eqv.1).elim
  | @forallE _ n b₀ _ b f _ _ hb₀ hb hdom hbody hroot =>
    cases children with
    | forallE cb₀ cb cbody =>
      suffices ∀ (fl : List (WShape n × WShape n)),
          (∀ p ∈ fl, p ∈ f ∧
            ∃ h : LE_Interp.Witness (ρ.push p.1.T) p.2.T B,
              h.RDeepChildren P) →
          ∃ n', n ≤ n' ∧ ∀ k, n' ≤ k →
            ∃ f' : WShapeFun k,
              (∀ p ∈ fl,
                WShapeFun.single (p.1.lift k) (p.2.lift k) ≤ f') ∧
              WShape.HasDom f' (b.lift k) ∧
              (∀ x, x.HasType (b.lift k) →
                ∃ h : LE_Interp.Witness (ρ.push x.T) (f'.app x).T B,
                  h.RDeepChildren P) ∧
              (∀ x, x.HasType (b.lift k) →
                (f'.app x).HasType (.sort (v ≠ .zero))) by
        have hElems : ∀ p ∈ f.elems, p ∈ f ∧
            ∃ h : LE_Interp.Witness (ρ.push p.1.T) p.2.T B,
              h.RDeepChildren P := by
          intro p hp
          have hpMem := WShapeFun.mem_elems.1 hp
          obtain ⟨x', hxle, hxty, happ⟩ :=
            WShape.HasDom.iff.1 hdom p.1
          let hBx := (hbody x' hxty).mono
              ((WShapeFun.app_of_mem hpMem).2.trans happ).T
            |>.mono_l (Valuation.LE.push.2 ⟨.rfl, hxle.T⟩)
          have cBx : hBx.RDeepChildren P :=
            ((cbody x' hxty).mono
                ((WShapeFun.app_of_mem hpMem).2.trans happ).T)
              |>.mono_l laws.mono_l
                (Valuation.LE.push.2 ⟨.rfl, hxle.T⟩)
          exact ⟨hpMem, hBx, cBx⟩
        obtain ⟨n', le, build⟩ := this f.elems hElems
        obtain ⟨f', hsingle, hd1, hi1, hi2⟩ :=
          build _ (Nat.le_refl _)
        obtain ⟨hcompat, joinedDom⟩ :=
          cb₀.compat_join laws.toJoinLaws .rfl cb
        have hDomJ := LE_Interp.Witness.RDeepChildren.choose joinedDom
        obtain ⟨b₂, s₂, hB₂, hS₂, hDomLe, hB₂Ty,
          cB₂, cS₂⟩ := H1 hDomJ.1 hDomJ.2
        have hB₂Sort : b₂.HasType (TShape.sort (u ≠ .zero)) :=
          TShape.HasType.mono_r hS₂.toInterp.le_sort .sort hB₂Ty
        let k := max n' b₂.1
        have ⟨le₂, le₁⟩ := Nat.max_le.1 (Nat.le_refl k)
        have hdK₀ := (WShape.HasDom.lift le₂).2 hd1
        have hdK : WShape.HasDom (f'.lift k) (b.lift k) :=
          WShape.lift_lift (.inl le) ▸ hdK₀
        have hB₂Le : (b₂.2.lift k).T ≤ b₂ :=
          (TShape.lift_eqv le₁).1
        let hB₂K : LE_Interp.Witness ρ (b₂.2.lift k).T A :=
          hB₂.mono hB₂Le
        have cB₂K : hB₂K.RDeepChildren P := by
          dsimp only [hB₂K]
          exact cB₂.mono hB₂Le
        have hBLe : (b.lift k).T ≤ b.T :=
          (TShape.lift_eqv (Nat.le_trans le le₂)).1
        let hBK : LE_Interp.Witness ρ (b.lift k).T A :=
          hb.mono hBLe
        have cBK : hBK.RDeepChildren P := by
          dsimp only [hBK]
          exact cb.mono hBLe
        have bodyK (x : WShape k) (hx : x.HasType (b.lift k)) :
            ∃ h : LE_Interp.Witness (ρ.push x.T)
                ((f'.lift k).app x).T B,
              h.RDeepChildren P := by
          obtain ⟨x', xle, xmem⟩ := (f'.lift k).app_eq x
          obtain ⟨z₀, -, -, rfl, -⟩ :=
            (WShapeFun.mem_lift le₂).1 xmem
          obtain ⟨z', zle, zty, zapp⟩ :=
            WShape.HasDom.iff.1 hd1 z₀
          obtain ⟨hz, cz⟩ := hi1 z' zty
          have hρz : (ρ.push z'.T).LE
              (ρ.push (z₀.lift k).T) := by
            refine Valuation.LE.push.2 ⟨.rfl, ?_⟩
            exact zle.T.trans (TShape.lift_eqv le₂).2
          have hzKPair : ∃ h : LE_Interp.Witness
              (ρ.push (z₀.lift k).T)
                ((f'.lift k).app (z₀.lift k)).T B,
              h.RDeepChildren P := by
            let hz₀ := (hz.mono zapp.T |>.mono_l hρz).mono
              (TShape.lift_eqv le₂).1
            have hz₀Pair : ∃ h : LE_Interp.Witness
                (ρ.push (z₀.lift k).T)
                  ((f'.app z₀).lift k).T B,
                h.RDeepChildren P := ⟨hz₀, by
              dsimp only [hz₀]
              exact ((cz.mono zapp.T).mono_l laws.mono_l hρz).mono
                (TShape.lift_eqv le₂).1⟩
            exact WShapeFun.lift_app le₂ ▸ hz₀Pair
          obtain ⟨hzK, czK⟩ := hzKPair
          let hzX := hzK.mono_l <|
            Valuation.LE.push.2 ⟨.rfl, xle.T⟩
          have czX : hzX.RDeepChildren P := by
            dsimp only [hzX]
            exact czK.mono_l laws.mono_l <|
              Valuation.LE.push.2 ⟨.rfl, xle.T⟩
          have hApp := (WShapeFun.app_of_mem xmem).2.T
          exact ⟨hzX.mono hApp, czX.mono hApp⟩
        let hBody := fun x hx =>
          (LE_Interp.Witness.RDeepChildren.choose (bodyK x hx)).1
        let hTerm : LE_Interp.Witness ρ
            ((b₂.2.lift k).forallE (f'.lift k)).T
            (A.forallE B) :=
          .forallE hB₂K hBK hdK hBody .rfl
        let hType : LE_Interp.Witness ρ
            (TShape.sort (u.imax v ≠ .zero))
            (.sort (u.imax v)) :=
          .sort TShape.LE.rfl
        have cTerm : hTerm.RDeepChildren P :=
          .forallE cB₂K cBK (fun x hx =>
            (LE_Interp.Witness.RDeepChildren.choose (bodyK x hx)).2)
        have cType : hType.RDeepChildren P := .sort
        have hroot' : m ≤
            ((b₂.2.lift k).forallE (f'.lift k)).T := by
          refine hroot.trans ?_
          rw [TShape.LE.lift_l
            (Nat.succ_le_succ (Nat.le_trans le le₂)),
            WShape.lift_forallE (Nat.le_trans le le₂)]
          refine WShape.forallE_le_forallE.2 ⟨?_, ?_⟩
          · exact (TShape.LE.def (Nat.le_trans le le₂) le₁).1 <|
              (TShape.Join.mk hcompat).le.1.trans hDomLe
          · rw [← WShapeFun.lift_lift (.inl le)]
            refine WShapeFun.lift_mono le₂ <|
              WShapeFun.LE.def'.2 fun x y hxy => ?_
            obtain ⟨x₀, y₀, h₀, rfl, rfl⟩ :=
              (WShapeFun.mem_lift le).1 hxy
            exact WShapeFun.single_le.1 <|
              hsingle _ (WShapeFun.mem_elems.2 h₀)
        have hTyped : ((b₂.2.lift k).forallE (f'.lift k)).T.HasType
            (TShape.sort (u.imax v ≠ .zero)) := by
          apply (TShape.HasType.def (Nat.le_refl _)
            (Nat.zero_le _)).2
          simp only [WShape.lift_self, TShape.sort, WShape.lift_sort, ne_eq,
            SLevel.imax_eq_zero]
          have hB₂SortK :=
            (TShape.HasType.def le₁ (Nat.zero_le k)).1 hB₂Sort
          refine .forallE <| WShape.HasTypePi.iff.2
            ⟨hdK.mono_r ?_ hB₂SortK, fun x hx => ?_⟩
          · exact (TShape.LE.def (Nat.le_trans le le₂) le₁).1 <|
              (TShape.Join.mk hcompat).le.2.trans hDomLe
          · obtain ⟨x', _, xmem⟩ := (f'.lift k).app_eq x
            obtain ⟨x₀, y₀, hm, rfl, heq⟩ :=
              (WShapeFun.mem_lift le₂).1 xmem
            have ⟨appLe, appEq⟩ := WShapeFun.app_of_mem hm
            refine heq ▸ WShape.lift_sort.symm ▸
              (WShape.HasType.lift le₂).2 (.mono_l appLe appEq ?_)
            obtain ⟨y, yle, yty, yapp⟩ :=
              WShape.HasDom.iff.1 hd1 x₀
            exact (hi2 _ yty).mono_l
              (WShapeFun.app_mono_r yle) yapp
        exact ⟨_, _, hTerm, hType, hroot', hTyped, cTerm, cType⟩
      intro fl Hfl
      induction fl with
      | nil =>
        refine ⟨n, Nat.le_refl _, fun k hk => ?_⟩
        have hbTy : (b.lift k).HasType .type := by
          simpa [WShape.lift_sort] using
            (WShape.HasType.lift hk).2 hdom.isType
        refine ⟨.bot, nofun, .bot hbTy, fun x hx => ?_,
          fun x hx => ?_⟩
        · rw [WShapeFun.bot_app]
          exact ⟨.bot, .bot⟩
        · simp [WShapeFun.bot_app]
          exact .bot' .sort
      | cons p fl ih =>
        have ⟨⟨hpMem, hpBody⟩, Htail⟩ :=
          List.forall_mem_cons.1 Hfl
        obtain ⟨k₁, le1, H1'⟩ := ih Htail
        obtain ⟨x', x'le, hx', happ⟩ :=
          WShape.HasDom.iff.1 hdom p.1
        obtain ⟨nBody, e', s', he', hs', leBody, le_e,
          heTy, ce', cs'⟩ :=
          (H2 hb cb (WShape.HasType.T hx')
            (hbody x' hx') (cbody x' hx')).out
        have heSortT : e'.T.HasType (TShape.sort (v ≠ .zero)) :=
          TShape.HasType.mono_r hs'.toInterp.le_sort .sort heTy.T
        have heSort : e'.HasType (.sort (v ≠ .zero)) := by
          simpa only [TShape.sort, WShape.lift_sort,
            WShape.lift_self] using
            (TShape.HasType.def (Nat.le_refl nBody)
              (Nat.zero_le nBody)).1 heSortT
        refine ⟨max k₁ nBody,
          Nat.le_trans le1 (Nat.le_max_left ..), fun k le' => ?_⟩
        have ⟨le₁, le₂⟩ := Nat.max_le.1 le'
        have le_nk : n ≤ k := Nat.le_trans le1 le₁
        obtain ⟨f₁, hsingle₁, hd1₁, hi1₁, hi2₁⟩ :=
          H1' _ le₁
        let sf := WShapeFun.single (x'.lift k) (e'.lift k)
        have hi1Any z : ∃ h : LE_Interp.Witness
            (ρ.push z.T) (f₁.app z).T B, h.RDeepChildren P := by
          obtain ⟨z', z'le, z'ty, z'app⟩ :=
            WShape.HasDom.iff.1 hd1₁ z
          obtain ⟨hz, cz⟩ := hi1₁ z' z'ty
          let hz' := hz.mono z'app.T |>.mono_l
            (Valuation.LE.push.2 ⟨.rfl, z'le.T⟩)
          exact ⟨hz', (cz.mono z'app.T).mono_l laws.mono_l
            (Valuation.LE.push.2 ⟨.rfl, z'le.T⟩)⟩
        have hxLift : x'.T ≤ (x'.lift k).T := by
          apply (TShape.LE.lift_l (a := x'.T)
            (b := (x'.lift k).T) le_nk).2
          exact WShape.LE.rfl
        let heK : LE_Interp.Witness (ρ.push (x'.lift k).T)
            (e'.lift k).T B :=
          he'.mono (TShape.lift_eqv le₂).1 |>.mono_l
            (Valuation.LE.push.2 ⟨.rfl, hxLift⟩)
        have ceK : heK.RDeepChildren P :=
          (ce'.mono (TShape.lift_eqv le₂).1).mono_l laws.mono_l
            (Valuation.LE.push.2 ⟨.rfl, hxLift⟩)
        have hc : f₁.Compat sf := by
          rw [WShapeFun.compat_single]
          intro ⟨xj, yj⟩ hmem hc
          obtain ⟨z, hz1, hz2⟩ := WShape.Compat.iff.1 hc
          have sfApp : sf.app z = e'.lift k := by
            rw [WShapeFun.single_app, if_pos hz2]
          obtain ⟨hz, _⟩ := hi1Any z
          exact .mono
            ((WShapeFun.app_of_mem hmem).2.trans
              (WShapeFun.app_mono_r hz1))
            (sfApp ▸ WShape.LE.rfl) <|
            WShape.Compat.T_iff.2 <|
              hz.toInterp.compat
                (sfApp ▸ heK.toInterp.mono_l
                  (Valuation.LE.push.2 ⟨.rfl, hz2.T⟩))
        have jf := WShapeFun.Join.mk hc
        refine ⟨f₁.join sf, ?_, ?_, fun x hx => ?_,
          fun x hx => ?_⟩
        · refine List.forall_mem_cons.2 ⟨?_, fun r hr =>
            (hsingle₁ r hr).trans jf.le.1⟩
          refine (WShapeFun.single_le.2
            ⟨_, _, WShapeFun.mem_single.2 (.inl rfl), ?_, ?_⟩).trans
              jf.le.2
          · exact WShape.lift_mono le_nk x'le
          · exact WShape.lift_mono le_nk
              ((WShapeFun.app_of_mem hpMem).2.trans happ)
              |>.trans ((TShape.LE.def le_nk le₂).1 le_e)
        · refine hd1₁.join' ?_ jf
            (WShape.join_self.2 ⟨.rfl, .rfl⟩)
          exact WShape.HasDom.single.2 <|
            .inl <| (WShape.HasType.lift le_nk).2 hx'
        · obtain ⟨hz, cz⟩ := hi1Any x
          have hs : ∃ h : LE_Interp.Witness
              (ρ.push x.T) (sf.app x).T B, h.RDeepChildren P := by
            dsimp only [sf]
            by_cases hmatch : x'.lift k ≤ x
            · rw [WShapeFun.single_app, if_pos hmatch]
              exact ⟨heK.mono_l
                  (Valuation.LE.push.2 ⟨.rfl, WShape.LE.T hmatch⟩),
                ceK.mono_l laws.mono_l
                  (Valuation.LE.push.2 ⟨.rfl, WShape.LE.T hmatch⟩)⟩
            · rw [WShapeFun.single_app, if_neg hmatch]
              exact ⟨.bot, .bot⟩
          obtain ⟨hs, cs⟩ := hs
          obtain ⟨_, joined⟩ := cz.compat_join laws.toJoinLaws
            .rfl cs
          have hJ := LE_Interp.Witness.RDeepChildren.choose joined
          have jx := jf.app_l x
          have hcRoot : (f₁.app x).T.Compat (sf.app x).T :=
            WShape.Compat.T_iff.1 jx.compat
          have jxT : TShape.Join (f₁.app x).T (sf.app x).T
              ((f₁.join sf).app x).T := jx.T
          have hin : ((f₁.join sf).app x).T ≤
              (f₁.app x).T.join (sf.app x).T :=
            (jxT _).2 (TShape.Join.mk hcRoot).le
          exact ⟨hJ.1.mono hin, hJ.2.mono hin⟩
        · have hT1 := hi2₁ x hx
          have hT2 : (sf.app x).HasType
              (.sort (v ≠ .zero)) := by
            dsimp only [sf]
            rw [WShapeFun.single_app]
            split
            · simpa only [WShape.lift_sort] using
                (WShape.HasType.lift le₂).2 heSort
            · exact .bot' .sort
          exact hT1.join' (jf.app_l x) hT2

theorem LE_Interp.sound_app
    (H1 : ∀ {m}, LE_Interp ρ m F → InterpTyped ρ m F (.forallE A B))
    (H2 : ∀ {b}, LE_Interp ρ b (B.inst X) →
      ∃ b', b ≤ b' ∧ LE_Interp ρ b' (B.inst X) ∧ b'.HasType .type)
    (h1 : LE_Interp ρ m (F.app X)) : InterpTyped ρ m (F.app X) (B.inst X) := by
  by_cases hm : m ≤ .bot; · exact TShape.le_bot'.1 hm ▸ .bot
  cases h1 with | bot => exact .bot | app h1 h2 h3
  rename_i nf f_shape a_sh
  have ⟨f_ts, s_ts, le_f, a2, a3, a4⟩ := H1 h1
  have hf : ¬f_ts ≤ .bot := fun h => by
    rw [show f_shape = .bot from TShape.le_bot.1 (le_f.trans h), WShape.bot_app] at h3
    exact hm (h3.trans TShape.bot_le')
  have hs : ¬s_ts ≤ .bot := fun h => hf (a4.bot_r' h)
  cases a3 with | bot => cases hs TShape.bot_le' | forallE b1 b2 b3 b4 b5
  rename_i npi b_pi b_pi' f_pi
  cases b5.le_forall with | bot b5 => cases hs b5 | @forallE m _ _ _ _ b5 b6
  obtain c1 | ⟨n₂, g_lam, rfl, c1⟩ := a4.ty_forallE_inv; · cases hf (c1 ▸ .rfl)
  let k := max (max n₂ m) (max npi nf)
  have hk := Nat.max_le.1 (Nat.le_refl k); simp only [Nat.max_le] at hk
  have a3' := LE_Interp.forallE b1 b2 b3 b4 (TShape.lift_eqv (Nat.succ_le_succ hk.2.1)).1
  rw [WShape.lift_forallE hk.2.1] at a3'
  have h_Binst := a3'.forallE_inv.2 (h2.lift hk.2.2)
  have ⟨a', le', g1, g2⟩ := H2 h_Binst
  have c1 := (TShape.HasTypeLam.def hk.1.1 hk.1.2).1 c1
  have c1_d := WShape.HasDom.iff.1 c1.2.1
  have c1_f := (WShape.HasTypeLam.iff.1 c1).2.2
  have ⟨_, e1, e2, e3⟩ := c1_d (a_sh.lift k)
  refine ⟨_, a', ?_, .app' (a2.lift (Nat.succ_le_succ hk.1.1)) (h2.lift hk.2.2), g1, ?_⟩
  · refine h3.trans <| TShape.app_mono ?_ (TShape.lift_eqv hk.2.2).2
    exact le_f.trans (TShape.lift_eqv (Nat.succ_le_succ hk.1.1)).2
  · have b6 := (TShapeFun.LE.def hk.1.2 hk.2.1).1 b6
    rw [WShape.lift_lam' hk.1.1, WShape.lam'_app]
    refine g2.mono_r ((WShapeFun.app_mono_l b6 _).trans (WShapeFun.app_mono_r e1) |>.T.trans le') ?_
    exact (WShape.HasTypeLam.iff.1 c1).2.2 _ e2 |>.mono_l (WShapeFun.app_mono_r e1) e3 |>.T

theorem LE_Interp.sound_lam
    (H1 : ∀ {m}, LE_Interp ρ m A →
      ∃ a', m ≤ a' ∧ LE_Interp ρ a' A ∧ a'.HasType .type)
    (H2 : ∀ {a x}, LE_Interp ρ a A → x.HasType a →
      ∀ {e}, LE_Interp (ρ.push x) e F → InterpTyped (ρ.push x) e F B)
    (h1 : LE_Interp ρ m (A.lam F)) : InterpTyped ρ m (A.lam F) (A.forallE B) := by
  by_cases hm : m ≤ .bot; · exact TShape.le_bot'.1 hm ▸ .bot
  cases h1 with | bot => cases hm TShape.bot_le' | @lam _ n a _ f _ _ h1 h2 h3 h4
  have ⟨a', a1, a2, a3⟩ := H1 h1
  suffices ∀ (fl : List (WShape n × WShape n)),
      (∀ p ∈ fl, p ∈ f ∧ LE_Interp (ρ.push p.1.T) p.2.T F) →
      ∃ n', n ≤ n' ∧ ∀ k, n' ≤ k → ∃ f' b : WShapeFun k,
        (∀ p ∈ fl, WShapeFun.single (p.1.lift k) (p.2.lift k) ≤ f') ∧
        WShape.HasDom f' (a.lift k) ∧ WShape.HasDom b (a.lift k) ∧
        (∀ x, x.HasType (a.lift k) → LE_Interp (ρ.push x.T) (f'.app x).T F) ∧
        (∀ x, x.HasType (a.lift k) → LE_Interp (ρ.push x.T) (b.app x).T B) ∧
        (∀ x, x.HasType (a.lift k) → (f'.app x).HasType (b.app x)) by
    have ⟨n', le, H⟩ := this f.elems fun p h => by
      have := WShapeFun.mem_elems.1 h
      have ⟨x', hle, hht, happ⟩ := WShape.HasDom.iff.1 h2 p.1
      refine ⟨this, .mono ((WShapeFun.app_of_mem this).2.trans happ).T ?_⟩
      exact (h3 x' hht).mono_l (Valuation.LE.push.2 ⟨.rfl, hle.T⟩)
    have ⟨f', b, hsingle, hd1, hd2, hi1, hi2, hi3⟩ := H _ (Nat.le_refl _)
    have h1' := h1.lift le
    refine ⟨_, _, ?_, .lam' h1' hd1 hi1, .forallE' h1' h1' hd2 hi2, ?_⟩
    · refine h4.trans <| (TShape.LE.lift_l (Nat.succ_le_succ le)).2 (WShape.lift_lam' le ▸ ?_)
      refine WShape.lam'_le_lam'.2 <| WShapeFun.LE.def'.2 fun x y hm => ?_
      obtain ⟨x₀, y₀, h₀, rfl, rfl⟩ := (WShapeFun.mem_lift le).1 hm
      exact WShapeFun.single_le.1 (hsingle _ (WShapeFun.mem_elems.2 h₀))
    · exact WShape.HasType.T <| .lam <| WShape.HasTypeLam.iff.2
        ⟨WShape.HasTypePi.iff.2 ⟨hd2, fun x h => (hi3 x h).isType⟩, hd1, hi3⟩
  intro fl H
  induction fl with
  | nil =>
    refine ⟨_, Nat.le_refl _, fun k hk => ?_⟩
    have ha : (a.lift k).HasType .type :=
      WShape.lift_type.symm ▸ (WShape.HasType.lift hk).2 h2.isType
    refine ⟨.bot, .bot, nofun, .bot ha, .bot ha, fun x h => ?_, fun x h => ?_, fun x h => ?_⟩
    · exact WShapeFun.bot_app ▸ .bot
    · exact WShapeFun.bot_app ▸ .bot
    · simp [WShapeFun.bot_app]; exact .bot' (.bot' .sort)
  | cons p fl ih =>
    have ⟨⟨sub1, h3a⟩, H⟩ := List.forall_mem_cons.1 H
    have ⟨k₁, le1, H1⟩ := ih H
    have ⟨x', x'le, hx', happ⟩ := WShape.HasDom.iff.1 h2 p.1
    have ⟨e', b', le_e, he', hb', heb'⟩ := H2 h1 (WShape.HasType.T hx') (h3 x' hx')
    let m' := max e'.1 b'.1; have ⟨lf, lb⟩ := Nat.max_le.1 (Nat.le_refl m')
    refine ⟨k₁.max m', Nat.le_trans le1 (Nat.le_max_left ..), fun k le' => ?_⟩
    have ⟨le₁, le₂⟩ := Nat.max_le.1 le'
    have le_nk : n ≤ k := Nat.le_trans le1 le₁
    have le_ek := Nat.le_trans lf le₂; have le_bk := Nat.le_trans lb le₂
    have ⟨f₁, b₁, hsingle₁, hd1₁, hd2₁, hi1₁, hi2₁, hi3₁⟩ := H1 _ le₁
    let sf := WShapeFun.single (x'.lift k) (e'.2.lift k)
    let sb := WShapeFun.single (x'.lift k) (b'.2.lift k)
    have hi1_any z : LE_Interp (ρ.push z.T) (f₁.app z).T F :=
      have ⟨z', z'le, z'ht, z'app⟩ := WShape.HasDom.iff.1 hd1₁ z
      (hi1₁ z' z'ht).mono z'app.T |>.mono_l (Valuation.LE.push.2 ⟨.rfl, z'le.T⟩)
    have hi2_any z : LE_Interp (ρ.push z.T) (b₁.app z).T B :=
      have ⟨z', z'le, z'ht, z'app⟩ := WShape.HasDom.iff.1 hd2₁ z
      (hi2₁ z' z'ht).mono z'app.T |>.mono_l (Valuation.LE.push.2 ⟨.rfl, z'le.T⟩)
    have he'_at_x' : LE_Interp (ρ.push (x'.lift k).T) (e'.2.lift k).T F :=
      (he'.lift le_ek).mono_l (Valuation.LE.push.2 ⟨.rfl, (TShape.LE.lift_l le_nk).2 .rfl⟩)
    have hb'_at_x' : LE_Interp (ρ.push (x'.lift k).T) (b'.2.lift k).T B :=
      (hb'.lift le_bk).mono_l (Valuation.LE.push.2 ⟨.rfl, (TShape.LE.lift_l le_nk).2 .rfl⟩)
    have hc : f₁.Compat sf := by
      rw [WShapeFun.compat_single]; intro ⟨xj, yj⟩ hmem hc
      have ⟨z, hz1, hz2⟩ := WShape.Compat.iff.1 hc
      have sf_app : sf.app z = e'.2.lift k := by rw [WShapeFun.single_app, if_pos hz2]
      refine .mono ?_ (sf_app ▸ .rfl) <| WShape.Compat.T_iff.2 <|
        (hi1_any z).compat (sf_app ▸ he'_at_x'.mono_l (Valuation.LE.push.2 ⟨.rfl, hz2.T⟩))
      exact (WShapeFun.app_of_mem hmem).2.trans (WShapeFun.app_mono_r hz1)
    have hcb : b₁.Compat sb := by
      rw [WShapeFun.compat_single]; intro ⟨xj, yj⟩ hmem hc
      have ⟨z, hz1, hz2⟩ := WShape.Compat.iff.1 hc
      have sb_app : sb.app z = b'.2.lift k := by rw [WShapeFun.single_app, if_pos hz2]
      refine .mono ?_ (sb_app ▸ .rfl) <| WShape.Compat.T_iff.2 <|
        (hi2_any z).compat (sb_app ▸ hb'_at_x'.mono_l (Valuation.LE.push.2 ⟨.rfl, hz2.T⟩))
      exact (WShapeFun.app_of_mem hmem).2.trans (WShapeFun.app_mono_r hz1)
    have jf := WShapeFun.Join.mk hc
    have jb := WShapeFun.Join.mk hcb
    refine ⟨f₁.join sf, b₁.join sb, ?_, ?_, ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
    · refine List.forall_mem_cons.2 ⟨?_, fun r hr => (hsingle₁ r hr).trans jf.le.1⟩
      refine (WShapeFun.single_le.2 ⟨_, _, WShapeFun.mem_single.2 (.inl rfl), ?_, ?_⟩).trans jf.le.2
      · exact WShape.lift_mono le_nk x'le
      · exact WShape.lift_mono le_nk ((WShapeFun.app_of_mem sub1).2.trans happ)
          |>.trans ((TShape.LE.def le_nk le_ek).1 le_e)
    · refine hd1₁.join' ?_ jf (WShape.join_self.2 ⟨.rfl, .rfl⟩)
      exact WShape.HasDom.single.2 <| .inl <| (WShape.HasType.lift le_nk).2 hx'
    · refine hd2₁.join' ?_ jb (WShape.join_self.2 ⟨.rfl, .rfl⟩)
      exact WShape.HasDom.single.2 <| .inl <| (WShape.HasType.lift le_nk).2 hx'
    · refine (hi1_any x).join (jf.app_l x).T (WShapeFun.single_app ▸ ?_); split
      · exact he'_at_x'.mono_l (Valuation.LE.push.2 ⟨.rfl, WShape.LE.T ‹_›⟩)
      · exact .bot
    · refine LE_Interp.join (jb.app_l x).T (hi2_any x) (WShapeFun.single_app ▸ ?_); split
      · exact hb'_at_x'.mono_l (Valuation.LE.push.2 ⟨.rfl, WShape.LE.T ‹_›⟩)
      · exact .bot
    · have hT1 := hi3₁ x hx
      have hT2 : (sf.app x).HasType (sb.app x) := by
        rw [WShapeFun.single_app, WShapeFun.single_app]; split
        · exact (TShape.HasType.def le_ek le_bk).1 heb'
        · exact .bot' (.bot' .sort)
      have jb_x := jb.app_l x
      have := hT1.isType.join' jb_x hT2.isType
      exact (this.mono_r jb_x.le.1 hT1).join' (jf.app_l x) (this.mono_r jb_x.le.2 hT2)

theorem LE_Interp.sound_forallE
    (H1 : ∀ {m}, LE_Interp ρ m A →
      ∃ a', m ≤ a' ∧ LE_Interp ρ a' A ∧ a'.HasType (.sort (u ≠ .zero)))
    (H2 : ∀ {a x}, LE_Interp ρ a A → x.HasType a →
      ∀ {e}, LE_Interp (ρ.push x) e B → InterpTyped (ρ.push x) e B (.sort v))
    (h1 : LE_Interp ρ m (A.forallE B)) :
    InterpTyped ρ m (A.forallE B) (.sort (.imax u v)) := by
  by_cases hm : m ≤ .bot; · exact TShape.le_bot'.1 hm ▸ .bot
  cases h1 with | bot => cases hm TShape.bot_le' | @forallE _ n b₀ _ b f _ _ h1 h2 h3 h4 h5
  have ⟨a', a1, a2, a3⟩ := H1 h2
  suffices ∀ (fl : List (WShape n × WShape n)),
      (∀ p ∈ fl, p ∈ f ∧ LE_Interp (ρ.push p.1.T) p.2.T B) →
      ∃ n', n ≤ n' ∧ ∀ k, n' ≤ k → ∃ f' : WShapeFun k,
        (∀ p ∈ fl, WShapeFun.single (p.1.lift k) (p.2.lift k) ≤ f') ∧
        WShape.HasDom f' (b.lift k) ∧
        (∀ x, x.HasType (b.lift k) → LE_Interp (ρ.push x.T) (f'.app x).T B) ∧
        (∀ x, x.HasType (b.lift k) → (f'.app x).HasType (.sort (v ≠ .zero))) by
    have ⟨n', le, H⟩ := this f.elems fun p h => by
      have := WShapeFun.mem_elems.1 h
      have ⟨x', hle, hht, happ⟩ := WShape.HasDom.iff.1 h3 p.1
      refine ⟨this, .mono ((WShapeFun.app_of_mem this).2.trans happ).T ?_⟩
      exact (h4 x' hht).mono_l (Valuation.LE.push.2 ⟨.rfl, hle.T⟩)
    have ⟨f', hsingle, hd1, hi1, hi2⟩ := H _ (Nat.le_refl _)
    have hJ := WShape.Join.mk <| WShape.Compat.T_iff.2 <| h1.compat h2
    have ⟨b₂, c1, c2, c3⟩ := H1 (h1.join hJ.T h2)
    let k := max n' b₂.1; have ⟨le₂, le₁⟩ := Nat.max_le.1 (Nat.le_refl k)
    have b2' := (WShape.HasDom.lift le₂).2 hd1
    refine ⟨((b₂.2.lift k).forallE (f'.lift k)).T, _, h5.trans ?_, ?_, .sort .rfl, ?_⟩
    · rw [TShape.LE.lift_l (Nat.succ_le_succ (Nat.le_trans le le₂)),
        WShape.lift_forallE (Nat.le_trans le le₂)]
      refine WShape.forallE_le_forallE.2 ⟨?_, WShapeFun.lift_lift (.inl le) ▸ ?_⟩
      · exact (TShape.LE.def (Nat.le_trans le le₂) le₁).1 (hJ.le.1.T.trans c1)
      refine WShapeFun.lift_mono le₂ <| WShapeFun.LE.def'.2 fun x y hm => ?_
      obtain ⟨x₀, y₀, h₀, rfl, rfl⟩ := (WShapeFun.mem_lift le).1 hm
      exact WShapeFun.single_le.1 <| hsingle _ (WShapeFun.mem_elems.2 h₀)
    · refine .forallE' (c2.lift le₁) ((h2.lift le).lift le₂) b2' fun x h => ?_
      have ⟨x', d1, dmem⟩ := (f'.lift k).app_eq x
      refine .mono (WShapeFun.app_of_mem dmem).2.T ?_
      obtain ⟨z₀, -, -, rfl, -⟩ := (WShapeFun.mem_lift le₂).1 dmem
      have ⟨z', z'le, z'ht, z'app⟩ := WShape.HasDom.iff.1 hd1 z₀
      refine WShapeFun.lift_app le₂ ▸ .lift (m := (f'.app _).T) le₂ ?_
      refine hi1 _ z'ht |>.mono z'app.T |>.mono_l <| Valuation.LE.push.2 ⟨.rfl, ?_⟩
      exact z'le.T.trans <| (TShape.LE.lift_l le₂).2 d1
    · apply (TShape.HasType.def (Nat.le_refl _) (Nat.zero_le _)).2
      simp only [WShape.lift_self, TShape.sort, WShape.lift_sort, ne_eq, SLevel.imax_eq_zero]
      have b2' := WShape.lift_lift (.inl le) ▸ b2'
      have := (TShape.HasType.def le₁ (Nat.zero_le k)).1 c3
      refine .forallE <| WShape.HasTypePi.iff.2 ⟨b2'.mono_r ?_ this, fun x hx => ?_⟩
      · exact (TShape.LE.def (Nat.le_trans le le₂) le₁).1 (hJ.le.2.T.trans c1)
      have ⟨x', _, dmem⟩ := (f'.lift k).app_eq x
      obtain ⟨x', y', e1, rfl, eq⟩ := (WShapeFun.mem_lift le₂).1 dmem
      have ⟨e2, e3⟩ := WShapeFun.app_of_mem e1
      refine eq ▸ WShape.lift_sort.symm ▸ (WShape.HasType.lift le₂).2 (.mono_l e2 e3 ?_)
      have ⟨y, d1, d2, d3⟩ := WShape.HasDom.iff.1 hd1 x'
      exact (hi2 _ d2).mono_l (WShapeFun.app_mono_r d1) d3
  intro fl H
  induction fl with
  | nil =>
    refine ⟨_, Nat.le_refl _, fun k hk => ?_⟩
    refine ⟨.bot, nofun, .bot ?_, fun x h => WShapeFun.bot_app ▸ .bot, fun x h => ?_⟩
    · simpa [WShape.lift_sort] using (WShape.HasType.lift hk).2 h3.isType
    · simp [WShapeFun.bot_app]; exact .bot' .sort
  | cons p fl ih =>
    have ⟨⟨sub1, h3a⟩, H⟩ := List.forall_mem_cons.1 H
    have ⟨k₁, le1, H1⟩ := ih H
    have ⟨x', x'le, hx', happ⟩ := WShape.HasDom.iff.1 h3 p.1
    have ⟨f'x, _, le_e, he', hb', heb'⟩ := H2 h2 hx'.T (h4 x' hx')
    replace heb' : f'x.HasType (.sort (v ≠ .zero)) := .mono_r hb'.le_sort .sort heb'
    refine ⟨k₁.max f'x.1, Nat.le_trans le1 (Nat.le_max_left ..), fun k le' => ?_⟩
    have ⟨le₁, le₂⟩ := Nat.max_le.1 le'
    have le_nk := Nat.le_trans le1 le₁
    have ⟨f₁, hsingle₁, hd1₁, hi1₁, hi2₁⟩ := H1 _ le₁
    let sf := WShapeFun.single (x'.lift k) (f'x.2.lift k)
    have hi1_any z : LE_Interp (ρ.push z.T) (f₁.app z).T B :=
      have ⟨z', z'le, z'ht, z'app⟩ := WShape.HasDom.iff.1 hd1₁ z
      (hi1₁ z' z'ht).mono z'app.T |>.mono_l (Valuation.LE.push.2 ⟨.rfl, WShape.LE.T z'le⟩)
    have he'_at_x' : LE_Interp (ρ.push (x'.lift k).T) (f'x.2.lift k).T B :=
      (he'.lift le₂).mono_l <| Valuation.LE.push.2 ⟨.rfl, (TShape.LE.lift_l le_nk).2 .rfl⟩
    have hc : f₁.Compat sf := by
      rw [WShapeFun.compat_single]; intro ⟨xj, yj⟩ hmem hc
      have ⟨z, hz1, hz2⟩ := WShape.Compat.iff.1 hc
      have sf_app : sf.app z = f'x.2.lift k := by rw [WShapeFun.single_app, if_pos hz2]
      refine .mono ?_ (sf_app ▸ .rfl) <| WShape.Compat.T_iff.2 <|
        (hi1_any z).compat (sf_app ▸ he'_at_x'.mono_l (Valuation.LE.push.2 ⟨.rfl, hz2.T⟩))
      exact (WShapeFun.app_of_mem hmem).2.trans (WShapeFun.app_mono_r hz1)
    have jf := WShapeFun.Join.mk hc
    refine ⟨f₁.join sf, ?_, ?_, fun x hx => ?_, fun x hx => ?_⟩
    · refine List.forall_mem_cons.2 ⟨?_, fun r hr => (hsingle₁ r hr).trans jf.le.1⟩
      refine (WShapeFun.single_le.2 ⟨_, _, WShapeFun.mem_single.2 (.inl rfl), ?_, ?_⟩).trans jf.le.2
      · exact WShape.lift_mono le_nk x'le
      · exact WShape.lift_mono le_nk ((WShapeFun.app_of_mem sub1).2.trans happ)
          |>.trans ((TShape.LE.def le_nk le₂).1 le_e)
    · refine hd1₁.join' ?_ jf (WShape.join_self.2 ⟨.rfl, .rfl⟩)
      exact WShape.HasDom.single.2 <| .inl <| (WShape.HasType.lift le_nk).2 hx'
    · refine (hi1_any x).join (jf.app_l x).T (WShapeFun.single_app ▸ ?_); split
      · exact he'_at_x'.mono_l (Valuation.LE.push.2 ⟨.rfl, WShape.LE.T ‹_›⟩)
      · exact .bot
    · refine (hi2₁ x hx).join' (jf.app_l x) (WShapeFun.single_app ▸ ?_); split
      · exact (TShape.HasType.def le₂ (Nat.zero_le k)).1 heb'
      · exact .bot' .sort

def SoundEq (Γ : List SExpr) (M N : SExpr) : Prop :=
  ∀ {{Γ₀ ρ}}, Valuation.Fits Γ₀ Γ ρ → ∀ {m}, LE_Interp ρ m M ↔ LE_Interp ρ m N
def SoundTy (Γ : List SExpr) (M A : SExpr) : Prop :=
  ∀ {{Γ₀ ρ}}, Valuation.Fits Γ₀ Γ ρ → ∀ {m}, LE_Interp ρ m M → InterpTyped ρ m M A

mutual
inductive StrongSound : List SExpr → SExpr → SExpr → Prop where
  | mk : Γ ⊢ M : A → SoundTy Γ M A →
    StrongSoundCore Γ M A' → SoundEq Γ A' A → StrongSound Γ M A

inductive StrongSoundCore : List SExpr → SExpr → SExpr → Prop where
  | bvar : Lookup Γ i A → StrongSoundCore Γ (.bvar i) A
  | sort : StrongSoundCore Γ (.sort l) (.sort (.succ l))
  | lam : SoundTy Γ A (.sort u) →
    StrongSound (A::Γ) e B → StrongSoundCore Γ (.lam A e) (.forallE A B)
  | const : Params.env.constants c = some ci → ls.length = ci.uvars →
    (F : ∀ cl, CtorBundle c cl) →
    (∀ cl, SoundEq Γ (SExpr.mkInst ls ci.type) ((F cl).rhs ls)) →
    (∀ cl, StrongSound Γ ((F cl).rhs ls) (.sort (F cl).u)) →
    StrongSoundCore Γ (.const c ls) (SExpr.mkInst ls ci.type)
  | app : SoundTy Γ A (.sort u) →
    StrongSound Γ f (.forallE A B) → StrongSound Γ a A →
    StrongSoundCore Γ (.app f a) (B.inst a)
  | forallE : StrongSound Γ A (.sort u) → StrongSound (A::Γ) B (.sort v) →
    StrongSoundCore Γ (.forallE A B) (.sort (.imax u v))
end
structure StrongSoundEq (Γ : List SExpr) (M N A : SExpr) : Prop where
  defeq : Γ ⊢ M ≡ N : A
  sound : SoundEq Γ M N
  left : StrongSound Γ M A
  right : StrongSound Γ N A

protected theorem SoundEq.rfl : SoundEq Γ M M := fun _ _ _ _ => .rfl
theorem SoundEq.symm : SoundEq Γ M N → SoundEq Γ N M := fun H _ _ W _ => (H W).symm
theorem StrongSoundEq.hasType : StrongSoundEq Γ M N A → StrongSound Γ M A ∧ StrongSound Γ N A
  | ⟨_, _, h1, h2⟩ => ⟨h1, h2⟩
theorem StrongSoundEq.symm : StrongSoundEq Γ M N A → StrongSoundEq Γ N M A
  | ⟨h1, h2, h3, h4⟩ => ⟨h1.symm, h2.symm, h4, h3⟩
theorem StrongSound.defeq : StrongSound Γ M A → Γ ⊢ M : A
  | ⟨h, _, _, _⟩ => h
theorem StrongSound.sound : StrongSound Γ M A → SoundTy Γ M A
  | ⟨_, h, _, _⟩ => h
theorem StrongSoundEq.rfl (H : StrongSound Γ M A) : StrongSoundEq Γ M M A :=
  ⟨H.defeq, .rfl, H, H⟩
theorem SoundEq.trans (H1 : SoundEq Γ M N) (H2 : SoundEq Γ N P) : SoundEq Γ M P :=
  fun _ _ W _ => (H1 W).trans (H2 W)
theorem StrongSoundEq.trans :
    StrongSoundEq Γ M N A → StrongSoundEq Γ N P A → StrongSoundEq Γ M P A
  | ⟨a1, a2, a3, _⟩, ⟨b1, b2, _, b4⟩ => ⟨.trans a1 b1, a2.trans b2, a3, b4⟩
theorem SoundTy.defeq_l (H1 : SoundEq Γ M N) (H : SoundTy Γ M A) : SoundTy Γ N A := fun _ _ W _ h =>
  have ⟨_, _, a1, a2, a3, a4⟩ := H W ((H1 W).2 h); ⟨_, _, a1, (H1 W).1 a2, a3, a4⟩
theorem SoundTy.defeq_r (H1 : SoundEq Γ A B) (H : SoundTy Γ M A) : SoundTy Γ M B := fun _ _ W _ h =>
  have ⟨_, _, a1, a2, a3, a4⟩ := H W h; ⟨_, _, a1, a2, (H1 W).1 a3, a4⟩

theorem StrongSoundEq.mk' (h1 : Γ ⊢ M ≡ N : A)
    (h2 : StrongSoundCore Γ M A₁) (h2' : SoundEq Γ A₁ A)
    (h3 : StrongSoundCore Γ N A₂) (h3' : SoundEq Γ A₂ A)
    (h4 : ∀ {{Γ₀ ρ}}, Valuation.Fits Γ₀ Γ ρ → ∀ {m},
      (LE_Interp ρ m M ↔ LE_Interp ρ m N) ∧ (LE_Interp ρ m M → InterpTyped ρ m M A)) :
    StrongSoundEq Γ M N A := by
  refine have ha := ?_; have ht := ?_
    ⟨h1, ha, ⟨h1.hasType.1, ht, h2, h2'⟩, h1.hasType.2, ht.defeq_l ha, h3, h3'⟩
  · exact fun _ _ W _ => (h4 W).1
  · exact fun _ _ W _ => (h4 W).2

theorem SoundEq.inst (ht : SoundTy Γ X A) (hA : SoundTy Γ A (.sort u))
    (H : SoundEq (A::Γ) M N) : SoundEq Γ (M.inst X) (N.inst X) := fun _ ρ W m => by
  suffices ∀ M N, SoundEq (A::Γ) M N → LE_Interp ρ m (M.inst X) → LE_Interp ρ m (N.inst X) from
    ⟨this _ _ H, this _ _ H.symm⟩
  simp only [LE_Interp.inst]; intro M N H ⟨x, h1, h2⟩
  have ⟨x', a, a1, a2, a3, a4⟩ := ht W h2
  refine ⟨_, (H (W.cons (InterpTyped.hsort (hA W)) a3 a4)).1 ?_, a2⟩
  exact h1.mono_l <| Valuation.LE.push.2 ⟨.rfl, a1⟩

theorem SoundEq.sort : SoundEq Γ (.sort u) (.sort v) ↔ (u ≠ .zero ↔ v ≠ .zero) := by
  refine ⟨fun H => ?_, fun H => ?_⟩
  · injection congrArg (·.1) <| WShape.sort_le.1 <| ((H .nil).1 .sort').le_sort' with eq
    exact decide_eq_decide.1 eq
  · intro _ ρ W m
    suffices ∀ {u v}, (u ≠ .zero ↔ v ≠ .zero) →
        LE_Interp ρ m (SExpr.sort u) → LE_Interp ρ m (SExpr.sort v) from ⟨this H, this H.symm⟩
    intro u v H h; exact .mono (decide_eq_decide.2 H ▸ h.le_sort) .sort'

theorem SoundEq.forallE (hA : SoundTy Γ A (.sort u))
    (H1 : SoundEq Γ A A') (H2 : SoundEq (A::Γ) B B') :
    SoundEq Γ (.forallE A B) (.forallE A' B') := by
  intro _ ρ W m
  suffices ∀ {A₁ A₂ B₁ B₂}, SoundEq Γ A A₁ → SoundEq Γ A A₂ → SoundEq (A::Γ) B₁ B₂ →
      LE_Interp ρ m (.forallE A₁ B₁) → LE_Interp ρ m (.forallE A₂ B₂) from
    ⟨this .rfl H1 H2, this H1 .rfl H2.symm⟩
  intro A₁ A₂ B₁ B₂ H1 H2 H3 h
  cases h with | bot => exact .bot | forallE h1 h2 h3 h4 h5
  have HA := H1.symm.trans H2
  refine .forallE ((HA W).1 h1) ((HA W).1 h2) h3 (fun _ h' => ?_) h5
  exact (H3 (W.cons (InterpTyped.hsort (hA W)) ((H1 W).2 h2) h'.T)).1 (h4 _ h')

theorem SoundEq.forallE_inv (H : SoundEq Γ (.forallE A B) (.forallE A' B'))
    (hA : SoundTy Γ A (.sort u)) (hA' : SoundTy Γ A' (.sort u')) :
    SoundEq Γ A A' ∧ SoundEq (A::Γ) B B' := by
  refine have hAA _ ρ W m := ?_; ⟨hAA, fun Γ₀ ρ W m => ?_⟩
  · suffices ∀ {A A' B B' u}, SoundEq Γ (.forallE A B) (.forallE A' B') → SoundTy Γ A (.sort u) →
        LE_Interp ρ m A → LE_Interp ρ m A' from ⟨this H hA, this H.symm hA'⟩
    intro A A' B B' u H hA h
    have ⟨_, a1, a2, a3⟩ := InterpTyped.hsort (hA W) h
    refine (H W).1 (.forallE' a2 a2 (.bot (TShape.HasType.sort_r.1 a3)) ?_) |>.forallE_inv.1.mono a1
    intro x _; simpa using .bot
  · suffices ∀ {A₁ A₂ B₁ B₂}, SoundEq Γ (.forallE A₁ B₁) (.forallE A₂ B₂) →
        SoundEq Γ A A₁ → LE_Interp ρ m B₁ → LE_Interp ρ m B₂ from ⟨this H .rfl, this H.symm hAA⟩
    intro A A' B B' H hAA h
    cases W with
    | nil =>
      have := (H .nil).1 <| .forallE' (f := .single .bot m.2) .bot .bot (WShape.HasDom.iff.2 ?_) ?_
      · have := this.forallE_inv'.2 .bot
        simp [WShapeFun.single_app] at this
        refine this.mono_l ?_; rintro ⟨⟩ <;> exact TShape.bot_eqv.1
      · refine fun _ => ⟨_, WShape.bot_le, .bot' (.bot' .sort), ?_⟩
        simpa [WShapeFun.single_app] using .rfl
      · intro x h'; cases h'.bot_r
        simpa [WShapeFun.single_app, show m.2.T = m from rfl] using
          h.mono_l fun _ => TShape.bot_le'
    | @cons Γ ρ A a x b1 b2 b3 b4 =>
      let k := max (max x.1 m.1) a.1
      have hk := Nat.max_le.1 (Nat.le_refl k); simp [Nat.max_le] at hk
      have b4' := (TShape.HasType.def hk.1.1 hk.2).1 b4
      have := (hAA b1).1 (b3.lift hk.2)
      have := (H b1).1 <| .forallE' (f := .single (x.2.lift k) (m.2.lift k))
        this this (WShape.HasDom.iff.2 ?_) ?_
      · have := this.forallE_inv'.2 (x.2.lift k)
        simp [WShapeFun.single_app, WShape.LE.rfl] at this
        exact this.mono (TShape.lift_eqv hk.1.2).2 |>.mono_l <|
          Valuation.LE.push.2 ⟨.rfl, (TShape.lift_eqv hk.1.1).1⟩
      · intro x'; simp [WShapeFun.single_app]
        split <;> [rename_i h; exact ⟨_, WShape.bot_le, .bot' b4'.isType, WShape.bot_le⟩]
        refine ⟨_, h, b4', if_pos ?_ ▸ .rfl⟩; exact .rfl
      · intro x' h1; simp [WShapeFun.single_app]; split <;> [rename_i h2; exact .bot]
        refine h.mono (TShape.lift_eqv hk.1.2).1 |>.mono_l <| Valuation.LE.push.2 ⟨.rfl, ?_⟩
        exact (TShape.LE.lift_l hk.1.1).2 h2

theorem StrongSound.uniq_of_core
    (H : ∀ {A B}, StrongSoundCore Γ M A → StrongSoundCore Γ M B → SoundEq Γ A B) :
    StrongSound Γ M A → StrongSound Γ M B → SoundEq Γ A B
  | ⟨_, _, a3, a4⟩, ⟨_, _, b3, b4⟩ => a4.symm.trans <| (H a3 b3).trans b4

theorem StrongSound.uniq : StrongSound Γ M A → StrongSound Γ M B → SoundEq Γ A B := by
  induction M generalizing Γ A B with refine uniq_of_core fun {A B} H1 H2 => ?_
  | bvar => let .bvar a1 := H1; let .bvar b1 := H2; exact a1.uniq b1 ▸ .rfl
  | sort => let .sort := H1; let .sort := H2; exact .rfl
  | const => let .const a1 .. := H1; let .const b1 .. := H2; cases a1.symm.trans b1; exact .rfl
  | app _ _ ihf =>
    let .app a1 a2 a3 := H1; let .app b1 b2 b3 := H2
    exact .inst a3.sound a1 ((ihf a2 b2).forallE_inv a1 b1).2
  | lam _ _ _ ihe => let .lam a1 a2 := H1; let .lam b1 b2 := H2; exact .forallE a1 .rfl (ihe a2 b2)
  | forallE _ _ ihA ihB =>
    let .forallE a1 a2 := H1; let .forallE b1 b2 := H2
    simp only [SoundEq.sort, ne_eq, SLevel.imax_eq_zero]
    exact SoundEq.sort.1 (ihB a2 b2)

/-- Data-bearing view of the constant case of `StrongSound`.  The view is
chosen classically so proof-relevant consumers do not eliminate a `Prop`
derivation directly into `Type`. -/
structure StrongSound.ConstView
    {Γ : List SExpr} {c : Name} {ls : List SLevel} {T : SExpr}
    (H : StrongSound Γ (.const c ls) T) where
  ci : VConstant
  hreg : Params.env.constants c = some ci
  hlen : ls.length = ci.uvars
  resultEq : SoundEq Γ (SExpr.mkInst ls ci.type) T

theorem StrongSound.constViewNonempty
    (H : StrongSound Γ (.const c ls) T) : Nonempty H.ConstView := by
  obtain ⟨_, _, hcore, heq⟩ := H
  cases hcore with
  | const hreg hlen _ _ _ => exact ⟨⟨_, hreg, hlen, heq⟩⟩

noncomputable def StrongSound.constView
    (H : StrongSound Γ (.const c ls) T) : H.ConstView :=
  Classical.choice H.constViewNonempty

/-- Data-bearing view of the application case of `StrongSound`. -/
structure StrongSound.AppView
    {Γ : List SExpr} {f a T : SExpr}
    (H : StrongSound Γ (.app f a) T) where
  dom : SExpr
  cod : SExpr
  funType : StrongSound Γ f (.forallE dom cod)
  argType : StrongSound Γ a dom
  resultEq : SoundEq Γ (cod.inst a) T

theorem StrongSound.appViewNonempty
    (H : StrongSound Γ (.app f a) T) : Nonempty H.AppView := by
  obtain ⟨_, _, hcore, heq⟩ := H
  cases hcore with
  | app _ hfun harg => exact ⟨⟨_, _, hfun, harg, heq⟩⟩

noncomputable def StrongSound.appView
    (H : StrongSound Γ (.app f a) T) : H.AppView :=
  Classical.choice H.appViewNonempty

/-- A data-bearing witness for semantic instantiation. -/
structure LE_Interp.InstView
    {ρ : Valuation} {m : TShape} {F A : SExpr}
    (H : LE_Interp ρ m (F.inst A)) where
  arg : TShape
  body : LE_Interp (ρ.push arg) m F
  value : LE_Interp ρ arg A

theorem LE_Interp.instViewNonempty
    {ρ : Valuation} {m : TShape} {F A : SExpr}
    (H : LE_Interp ρ m (F.inst A)) : Nonempty H.InstView := by
  obtain ⟨arg, hbody, hvalue⟩ := LE_Interp.inst.1 H
  exact ⟨⟨arg, hbody, hvalue⟩⟩

noncomputable def LE_Interp.instView
    {ρ : Valuation} {m : TShape} {F A : SExpr}
    (H : LE_Interp ρ m (F.inst A)) : H.InstView :=
  Classical.choice H.instViewNonempty

/-- Data-bearing form of `InterpTyped.out` for proof-relevant builders. -/
structure InterpTyped.OutView
    {ρ : Valuation} {m : TShape} {M A : SExpr}
    (H : InterpTyped ρ m M A) where
  level : Nat
  termShape : WShape level
  typeShape : WShape level
  rootLevel_le : m.1 ≤ level
  root_le : m ≤ termShape.T
  termInterp : LE_Interp ρ termShape.T M
  typeInterp : LE_Interp ρ typeShape.T A
  typed : termShape.HasType typeShape

theorem InterpTyped.outViewNonempty
    (H : InterpTyped ρ m M A) : Nonempty H.OutView := by
  obtain ⟨level, termShape, typeShape, hlevel, hle, hterm, htype, htyped⟩ := H.out
  exact ⟨⟨level, termShape, typeShape, hlevel, hle, hterm, htype, htyped⟩⟩

noncomputable def InterpTyped.outView
    (H : InterpTyped ρ m M A) : H.OutView :=
  Classical.choice H.outViewNonempty

theorem LE_Interp.apps_realize_inv (W : Valuation.Fits Γ₀ Γ ρ)
    (h_env : Params.env.constants c = some ci)
    (h_intr_defeq : SoundEq Γ (SExpr.mkInst ls ci.type) (List.foldr .forallE body Ts))
    (h_k_eq : List.length srev + k = Ts.length)
    (hTy : StrongSound Γ (srev.foldr (fun A acc => acc.app A) (.const c ls)) T)
    (H : LE_Interp (srev.length.repeat (·.push .bot) ρ) m
      ((Ts.drop srev.length).foldr .forallE body)) :
    LE_Interp ρ m T := by
  induction srev generalizing k m T with | cons a rest ih => ?_ | nil =>
    cases (Nat.zero_add _).symm.trans h_k_eq
    have ⟨_, _, hTy, h_T_eq_intr⟩ := hTy; have .const h_env' .. := hTy
    cases h_env'.symm.trans h_env
    exact (h_T_eq_intr.symm.trans h_intr_defeq W).2 H
  have ⟨_, _, hTy, h_T_eq⟩ := hTy; have .app _ h_fun_ty _ := hTy
  have h_k_rest : rest.length + (k + 1) = Ts.length := by
    simp only [List.length_cons] at h_k_eq; omega
  have h_lt : rest.length < Ts.length := by omega
  have h_app := ih (k := k + 1) (m := WShape.T (n := _+1) (.forallE .bot (.single .bot m.2)))
    h_k_rest h_fun_ty ?_ |>.forallE_inv.2 (X := a) .bot
  · rw [WShapeFun.single_app, if_pos .rfl] at h_app
    exact (h_T_eq W).1 h_app
  · rw [List.drop_eq_getElem_cons h_lt, List.foldr_cons]
    refine .forallE' .bot .bot ?_ ?_
    · exact WShape.HasDom.single.2 (.inl (.bot' (.bot' .sort)))
    · intro x hx; cases hx.bot_r; simp [WShapeFun.single_app]
      exact H.mono_l <| Valuation.LE.push.2 ⟨.rfl, TShape.bot_eqv.2⟩

/-- Realize a typed constant application through an explicitly selected
evaluator relation.

Unlike `apps_realize` below, this theorem does not replace the relation
stored by the constant with the proof-irrelevant ambient interpretation.
The caller supplies both the exact relation and its realization callback,
so a later proof-relevant consumer can retain the evaluator edge that was
actually used to build the constant. -/
theorem LE_Interp.apps_realizeWith (W : Valuation.Fits Γ₀ Γ ρ)
    (mty : m'.HasType a) (ha : LE_Interp ρ a T)
    (hTy_lhs : StrongSound Γ (rAs.foldr (fun A acc => acc.app A) (.const c ls)) T)
    (hargs : List.Forall₂ (LE_Interp ρ ·.T) (rargs : List (WShape n)) rAs)
    (hC : Const c ls R rargs m')
    (hR : ∀ m e, R m e → LE_Interp ρ m e)
    (hRmono : ∀ {m m' e}, m ≤ m' → R m' e → R m e) :
    LE_Interp ρ m' (rAs.foldr (fun A acc => acc.app A) (.const c ls)) := by
  generalize h_len : rargs.length = k
  induction k generalizing m' a T rAs n with | succ k ih => ?_ | zero =>
    let .nil := hargs
    have ⟨_, _, hTy, hType⟩ := hTy_lhs; have .const h1 h2 .. := hTy
    exact .const h1 h2 .rfl mty ((hType W).2 ha) hC hR
  let .cons (a := arg) (b := A) (l₁ := rest_r) (l₂ := rest_s) h_arg h_rest := hargs
  cases h_len
  have ⟨_, _, hTy, hC_inst⟩ := hTy_lhs; have .app _ hMf hMa := hTy
  obtain ⟨y, hya, hy⟩ := LE_Interp.inst.1 ((hC_inst W).2 ha)
  obtain ⟨n', arg', aT, _, jle, h_LE, ha', harg'⟩ := (hMa.sound W (h_arg.join' hy)).out
  let k := max (max n m'.1) (max n' a.1)
  have hk := Nat.max_le.1 (Nat.le_refl k); simp only [Nat.max_le] at hk
  let arg'' := arg'.lift k; let m'' := m'.2.lift k
  let m2 : WShape (k+1) := .lam' (.single arg'' m'')
  suffices LE_Interp ρ m2.T (rest_s.foldr (fun A acc => acc.app A) (.const c ls)) by
    have h_arg'_T : LE_Interp ρ arg''.T A := h_LE.lift hk.2.1
    have h_app := this.app' h_arg'_T
    simp only [m2, WShape.lam'_app, WShapeFun.single_app, WShape.LE.rfl, ↓reduceIte] at h_app
    exact h_app.mono (TShape.lift_eqv hk.1.2).2
  have hJ := TShape.Join.mk (h_arg.compat hy)
  let aT' := aT.lift k; let a' := a.2.lift k
  let a2 : WShape (k+1) := .forallE aT' (.single arg'' a')
  have h_argw_typed : arg''.HasType aT' := (WShape.HasType.lift hk.2.1).2 harg'
  refine ih (a := a2.T) (rargs := rest_r.map (WShape.lift k)) ?_ ?_ hMf ?_ ?_ (by simp)
  · have h_m_typed := (TShape.HasType.def hk.1.2 hk.2.2).1 mty
    refine WShape.HasType.T <| .lam <| WShape.HasTypeLam.iff'.2 ⟨?_, ?_, fun x => ?_⟩
    · refine WShape.HasTypePi.def.2 ⟨WShape.HasDom.single.2 (.inl h_argw_typed), fun x y h => ?_⟩
      obtain ⟨rfl, rfl⟩ | ⟨_, rfl, rfl⟩ := WShapeFun.mem_single.1 h
      · exact h_m_typed.isType
      · exact .bot' .sort
    · exact WShape.HasDom.single.2 (.inl h_argw_typed)
    · simp only [WShapeFun.single_app]; split <;> [exact h_m_typed; exact .bot' (.bot' .sort)]
  · refine .forallE' (ha'.lift hk.2.1) (ha'.lift hk.2.1)
      (WShape.HasDom.single.2 (.inl h_argw_typed)) fun x _ => ?_
    rw [WShapeFun.single_app]; split <;> [rename_i h1; exact .bot]
    refine .lift hk.2.2 <| hya.mono_l (Valuation.LE.push.2 ⟨.rfl, ?_⟩)
    exact (hJ.le.2.trans jle).trans (TShape.lift_eqv hk.2.1).2 |>.trans h1.T
  · exact List.forall₂_map_left_iff.2 <| h_rest.imp fun _ _ h => h.mono (TShape.lift_eqv hk.1.1).1
  · refine Const.lam (fun x y hmem => ?_) .rfl
    obtain ⟨⟨⟩⟩ | ⟨_, ⟨⟩⟩ := WShapeFun.mem_single.1 hmem <;> [skip; exact .bot]
    have hClift : Const c ls R ((arg :: rest_r).map (.lift k)) m' :=
      hC.lift hk.1.1 hRmono
    have hargsLe : ((arg :: rest_r).map (.lift k)).Forall₂ (· ≤ ·)
        (arg'' :: rest_r.map (.lift k)) :=
      .cons ((TShape.LE.def hk.1.1 hk.2.1).1
        (hJ.le.1.trans jle)) <| .rfl fun _ _ => .rfl
    have hCargs : Const c ls R (arg'' :: rest_r.map (.lift k)) m' :=
      hClift.mono_l hargsLe
    exact hCargs.mono (TShape.lift_eqv hk.1.2).1 hRmono

/-- Proof-relevant realization of a typed constant application through an
explicit evaluator relation.

The returned `Witness` is assembled directly.  In particular, its constant
node stores `hC` and `hR` literally; it is never recovered from the public
`LE_Interp` proposition by `LE_Interp.witness`.  Ordinary argument and type
observations may still be chosen noncomputably, but the evaluator edge whose
provenance drives recursive unfolding remains the caller's exact witness. -/
noncomputable def LE_Interp.Witness.appsRealizeWith
    (W : Valuation.Fits Γ₀ Γ ρ)
    (mty : m'.HasType a) (ha : LE_Interp.Witness ρ a T)
    (hTy_lhs : StrongSound Γ
      (rAs.foldr (fun A acc => acc.app A) (.const c ls)) T)
    (hargs : List.Forall₂ (LE_Interp ρ ·.T)
      (rargs : List (WShape n)) rAs)
    (hC : Const c ls R rargs m')
    (hR : ∀ m e, R m e → LE_Interp.Witness ρ m e)
    (hRmono : ∀ {m m' e}, m ≤ m' → R m' e → R m e) :
    LE_Interp.Witness ρ m'
      (rAs.foldr (fun A acc => acc.app A) (.const c ls)) := by
  generalize h_len : rargs.length = k
  induction k generalizing m' a T rAs n with
  | zero =>
    have hrargs : rargs = [] := List.eq_nil_of_length_eq_zero h_len
    have hrAs : rAs = [] := List.eq_nil_of_length_eq_zero
      (hargs.length_eq.symm.trans h_len)
    subst rargs
    subst rAs
    let hview := hTy_lhs.constView
    let hTypeWitness := ((hview.resultEq W).2 ha.toInterp).witness
    exact .const hview.hreg hview.hlen .rfl mty hTypeWitness hC hR
  | succ k ih =>
    cases rargs with
    | nil => simp at h_len
    | cons arg rest_r =>
      cases rAs with
      | nil => simp at hargs
      | cons A rest_s =>
       have h_arg := (List.forall₂_cons.1 hargs).1
       have h_rest := (List.forall₂_cons.1 hargs).2
       have hrest_len : rest_r.length = k := by simpa using h_len
       let hTyView := hTy_lhs.appView
       let hInst := ((hTyView.resultEq W).2 ha.toInterp).instView
       let y := hInst.arg
       have hya := hInst.body
       have hy := hInst.value
       let hTyped := (hTyView.argType.sound W (h_arg.join' hy)).outView
       let n' := hTyped.level
       let arg' := hTyped.termShape
       let aT := hTyped.typeShape
       have jle := hTyped.root_le
       have h_LE := hTyped.termInterp
       have ha' := hTyped.typeInterp
       have harg' := hTyped.typed
       let depth := max (max n m'.1) (max n' a.1)
       have hk := Nat.max_le.1 (Nat.le_refl depth)
       simp only [Nat.max_le] at hk
       let arg'' := arg'.lift depth
       let m'' := m'.2.lift depth
       let m2 : WShape (depth + 1) := .lam' (.single arg'' m'')
       suffices hrest : LE_Interp.Witness ρ m2.T
           (rest_s.foldr (fun A acc => acc.app A) (.const c ls)) by
         let hargWitness : LE_Interp.Witness ρ arg''.T A :=
           (h_LE.lift hk.2.1).witness
         have happ := LE_Interp.Witness.app hrest hargWitness
           (TShape.LE.rfl : (m2.app arg'').T ≤ (m2.app arg'').T)
         simp only [m2, WShape.lam'_app, WShapeFun.single_app,
           WShape.LE.rfl, ↓reduceIte] at happ
         exact happ.mono (TShape.lift_eqv hk.1.2).2
       have hJ := TShape.Join.mk (h_arg.compat hy)
       let aT' := aT.lift depth
       let a' := a.2.lift depth
       let a2 : WShape (depth + 1) := .forallE aT' (.single arg'' a')
       have h_argw_typed : arg''.HasType aT' :=
         (WShape.HasType.lift hk.2.1).2 harg'
       let ha2Interp : LE_Interp ρ a2.T
           (.forallE hTyView.dom hTyView.cod) := by
         refine .forallE' (ha'.lift hk.2.1) (ha'.lift hk.2.1)
           (WShape.HasDom.single.2 (.inl h_argw_typed)) fun x _ => ?_
         rw [WShapeFun.single_app]
         split <;> [rename_i h1; exact .bot]
         refine .lift hk.2.2 <| hya.mono_l
           (Valuation.LE.push.2 ⟨.rfl, ?_⟩)
         exact (hJ.le.2.trans jle).trans
           (TShape.lift_eqv hk.2.1).2 |>.trans h1.T
       let ha2 : LE_Interp.Witness ρ a2.T
           (.forallE hTyView.dom hTyView.cod) := ha2Interp.witness
       refine ih (a := a2.T) (rargs := rest_r.map (.lift depth))
           (m' := m2.T) ?_ ha2 hTyView.funType ?_ ?_ ?_
       · have h_m_typed := (TShape.HasType.def hk.1.2 hk.2.2).1 mty
         refine WShape.HasType.T <| .lam <|
           WShape.HasTypeLam.iff'.2 ⟨?_, ?_, fun x => ?_⟩
         · refine WShape.HasTypePi.def.2
             ⟨WShape.HasDom.single.2 (.inl h_argw_typed), fun x y h => ?_⟩
           obtain ⟨rfl, rfl⟩ | ⟨_, rfl, rfl⟩ :=
             WShapeFun.mem_single.1 h
           · exact h_m_typed.isType
           · exact .bot' .sort
         · exact WShape.HasDom.single.2 (.inl h_argw_typed)
         · simp only [WShapeFun.single_app]
           split <;> [exact h_m_typed; exact .bot' (.bot' .sort)]
       · exact List.forall₂_map_left_iff.2 <|
           h_rest.imp fun _ _ h => h.mono (TShape.lift_eqv hk.1.1).1
       · refine Const.lam (fun x y hmem => ?_) .rfl
         obtain ⟨⟨⟩⟩ | ⟨_, ⟨⟩⟩ := WShapeFun.mem_single.1 hmem <;>
           [skip; exact .bot]
         have hClift : Const c ls R ((arg :: rest_r).map (.lift depth)) m' :=
           hC.lift hk.1.1 hRmono
         have hargsLe : ((arg :: rest_r).map (.lift depth)).Forall₂ (· ≤ ·)
             (arg'' :: rest_r.map (.lift depth)) :=
           .cons ((TShape.LE.def hk.1.1 hk.2.1).1
             (hJ.le.1.trans jle)) <| .rfl fun _ _ => .rfl
         have hCargs : Const c ls R
             (arg'' :: rest_r.map (.lift depth)) m' :=
           hClift.mono_l hargsLe
         exact hCargs.mono (TShape.lift_eqv hk.1.2).1 hRmono
       · simpa using hrest_len

/-- Realize a constant application with the singleton evaluator relation
generated by one exact RHS witness.  Every evaluator edge stored in the
result is therefore a root lowering of `hX`, never an ambient re-selection. -/
noncomputable def LE_Interp.Witness.appsRealizeFocused
    (W : Valuation.Fits Γ₀ Γ ρ)
    (mty : m'.HasType a) (ha : LE_Interp.Witness ρ a T)
    (hTy_lhs : StrongSound Γ
      (rAs.foldr (fun A acc => acc.app A) (.const c ls)) T)
    (hargs : List.Forall₂ (LE_Interp ρ ·.T)
      (rargs : List (WShape n)) rAs)
    (hX : LE_Interp.Witness ρ root X)
    (hC : Const c ls hX.LowerEdge rargs m') :
    LE_Interp.Witness ρ m'
      (rAs.foldr (fun A acc => acc.app A) (.const c ls)) :=
  LE_Interp.Witness.appsRealizeWith W mty ha hTy_lhs hargs hC
    (fun _ _ edge => edge.realize)
    (fun hle edge => edge.mono hle)

/-- Compatibility form of `apps_realizeWith` using every ambient semantic
interpretation as a possible evaluator edge.  Proof-relevant conversion
producers should call `apps_realizeWith` directly with a focused relation. -/
theorem LE_Interp.apps_realize (W : Valuation.Fits Γ₀ Γ ρ)
    (mty : m'.HasType a) (ha : LE_Interp ρ a T)
    (hTy_lhs : StrongSound Γ (rAs.foldr (fun A acc => acc.app A) (.const c ls)) T)
    (hargs : List.Forall₂ (LE_Interp ρ ·.T) (rargs : List (WShape n)) rAs)
    (hC : Const c ls (LE_Interp ρ) rargs m') :
    LE_Interp ρ m' (rAs.foldr (fun A acc => acc.app A) (.const c ls)) :=
  LE_Interp.apps_realizeWith W mty ha hTy_lhs hargs hC
    (fun _ _ h => h) (fun hle h => h.mono hle)

theorem LE_Interp.RHS.le_applyS
    (hpath : ∀ path, LE_Interp ρ (m1 path) (m2 path))
    (hR_sound : ∀ m e, R m e → LE_Interp ρ m e)
    (hRHS : LE_Interp.RHS ls m1 R m r) :
    LE_Interp ρ m (r.applyS ls m2) := by
  induction hRHS with
  | bot => exact .bot
  | const h1 => exact hR_sound _ _ h1
  | var h1 => exact (hpath _).mono h1
  | app _ _ h3 ihf iha => exact .app ihf iha h3

theorem LE_Interp.RHS.of_applyS {r : Pattern.RHS p} (hLE : LE_Interp ρ m (r.applyS ls m2)) :
    ∃ m1, (∀ path, LE_Interp ρ (m1 path) (m2 path)) ∧ LE_Interp.RHS ls m1 (LE_Interp ρ) m r := by
  induction r generalizing m with
  | fixed e cl => exact ⟨fun _ => .bot, fun _ => .bot, .const hLE⟩
  | var path =>
    classical
    refine ⟨fun p' => if p' = path then m else .bot, fun p' => ?_, ?_⟩
    · dsimp; split <;> [simpa [*]; exact .bot]
    · exact .var (by simp [TShape.LE.rfl])
  | app r_f r_a ih_f ih_a =>
    cases hLE with | bot => exact ⟨fun _ => .bot, fun _ => .bot, .bot⟩ | app hLE_f hLE_a hle_app
    obtain ⟨mf, hf, rf⟩ := ih_f hLE_f
    obtain ⟨ma, ha, ra⟩ := ih_a hLE_a
    refine ⟨fun path => (mf path).join (ma path), fun path => ?_, ?_⟩
    · exact (hf path).join' (ha path)
    · refine .app (rf.mono_l fun path => ?_) (ra.mono_l fun path => ?_) hle_app
      · exact (TShape.Join.mk ((hf path).compat (ha path))).le.1
      · exact (TShape.Join.mk ((hf path).compat (ha path))).le.2

theorem LE_Interp.Matches.of_matchesS (a2 : p.MatchesS M ls m2)
    (hWF : p.WF Params.classify top n_off) (hLE : LE_Interp ρ x M) :
    ∃ n', ∀ k, n' ≤ k → ∃ c rargs m' m_arg,
      LE_Interp.Matches (n := k) p c rargs m' ∧
      (∀ path, LE_Interp ρ (m' path) (m2 path)) ∧
      x ≤ m_arg ∧ Const c ls (LE_Interp ρ) rargs m_arg := by
  induction a2 generalizing x top n_off with
  | const =>
    cases hLE with | @const n _ _ _ _ _ _ _ _ _ _ hle _ _ hConst hR => ?_ | bot =>
      exact ⟨0, fun _ _ => ⟨_, [], nofun, _, .const, nofun, .rfl, .bot⟩⟩
    refine ⟨n, fun k hk => ⟨_, [], nofun, _, .const, nofun, hle, ?_⟩⟩
    exact hConst.mono (R' := LE_Interp ρ) .rfl (fun le hr => (hR _ _ hr).mono le) |>.lift hk .mono
  | var hMinner ih =>
    cases hLE with
    | bot =>
      obtain ⟨n', ih'⟩ := ih (x := .bot) hWF .bot
      refine ⟨n', fun k hk => ?_⟩
      obtain ⟨_, rargs, m', m_arg, hMatch, hpath, _⟩ := ih' k hk
      exact ⟨_, _, _, _, hMatch.var, (·.casesOn .bot hpath), TShape.bot_eqv.1, .bot⟩
    | @app _ n f _ _ _ x_arg hLE_f hLE_a hle_app
    obtain ⟨n', ih'⟩ := ih hWF hLE_f
    refine ⟨max (n + 1) n', fun k hk => ?_⟩
    have ⟨hk_app, hk⟩ := Nat.max_le.1 hk
    obtain ⟨_, rargs, m', m_arg, hMatch, hpath, hle, hConst⟩ := ih' k hk
    have hk_n : n ≤ k := Nat.le_of_succ_le hk_app
    refine ⟨_, _, _, _, hMatch.var,
      (·.casesOn (hLE_a.mono (TShape.lift_eqv hk_n).1) hpath), hle_app, ?_⟩
    cases hConst with
    | bot =>
      have hf_bot : f.T ≤ .bot := hle.trans TShape.bot_eqv.1
      have h_app_bot : (f.app x_arg).T ≤ .bot := by
        have : f = .bot := TShape.le_bot.1 hf_bot
        rw [this]; simp; exact TShape.bot_eqv.1
      refine TShape.le_bot'.1 h_app_bot ▸ .bot
    | ctor h =>
      cases top
      · injection h ▸ hMatch.head_wf_eq hWF with h_eq; injection h_eq; omega
      · cases h ▸ hMatch.head_wf_eq hWF
    | indTy h => cases top <;> cases h ▸ hMatch.head_wf_eq hWF
    | pat hP hM =>
      cases top
      · cases pat_arity hP hM.arity ▸ hMatch.head_wf_eq hWF
      · injection pat_arity hP hM.arity ▸ hMatch.head_wf_eq hWF with h_eq
        injection h_eq; omega
    | @lam f_const _ _ hRec hle_lam
    let x_arg' : WShape k := x_arg.lift k
    obtain ⟨x', hx'_le, hx'_mem⟩ := WShapeFun.app_eq f_const x_arg'
    refine hRec x' (f_const.app x_arg') hx'_mem
      |>.mono_l (.cons hx'_le <| .rfl fun _ _ => .rfl) |>.mono ?_ .mono
    rw [← WShape.lam'_app (f := f_const) (x := x_arg')]
    exact TShape.app_mono (hle.trans hle_lam) (TShape.lift_eqv hk_n).2
  | @app p_f E_f _ g_f p_a E_a _ g_a hMf hMa ihf iha =>
    cases hLE with | @app _ _ f _ _ _ x_arg hLE_f hLE_a hle_app => ?_ | bot =>
      obtain ⟨n'_f, ihf'⟩ := ihf (x := .bot) hWF.1 .bot
      obtain ⟨n'_a, iha'⟩ := iha (x := .bot) hWF.2 .bot
      refine ⟨max 1 (max n'_f (n'_a + 1)), fun k hk => ?_⟩
      have ⟨hk_one, hk_rest⟩ := Nat.max_le.1 hk
      have ⟨hk_f, hk_a_plus⟩ := Nat.max_le.1 hk_rest
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 :=
        ⟨k - 1, (Nat.sub_add_cancel hk_one).symm⟩
      have hk_a : n'_a ≤ k' := Nat.le_of_succ_le_succ hk_a_plus
      obtain ⟨_, rargs_f, mf', _, hMatch_f, hpath_f, _⟩ := ihf' (k' + 1) hk_f
      obtain ⟨_, rargs_a, ma', _, hMatch_a, hpath_a, _⟩ := iha' k' hk_a
      refine ⟨_, WShape.ctor' _ rargs_a.reverse :: rargs_f,
        Sum.elim mf' ma', _, hMatch_f.app hMatch_a, (·.casesOn hpath_f hpath_a),
        TShape.bot_eqv.1, .bot⟩
    obtain ⟨n'_f, ihf'⟩ := ihf hWF.1 hLE_f
    obtain ⟨n'_a, iha'⟩ := iha hWF.2 hLE_a
    refine ⟨max n'_f n'_a + 1, fun k hk => ?_⟩
    let k' + 1 := k; have hk := Nat.max_le.1 (Nat.le_of_succ_le_succ hk)
    let ⟨_, rargs_f, mf', _, hMatch_f, hpath_f, hle_f, hConst_f⟩ := ihf' _ (Nat.le_succ_of_le hk.1)
    let ⟨c_a, rargs_a, ma', _, hMatch_a, hpath_a, hle_a, hConst_a⟩ := iha' k' hk.2
    refine ⟨_, WShape.ctor' _ rargs_a.reverse :: rargs_f,
      Sum.elim mf' ma', (f.app x_arg).T, hMatch_f.app hMatch_a,
      (·.casesOn hpath_f hpath_a), hle_app, ?_⟩
    cases hConst_f with
    | bot =>
      have hf_bot : f.T ≤ .bot := hle_f.trans TShape.bot_eqv.1
      have h_app_bot : (f.app x_arg).T ≤ .bot := by
        simp [show f = .bot from TShape.le_bot.1 hf_bot]; exact TShape.bot_eqv.1
      exact TShape.le_bot'.1 h_app_bot ▸ .bot
    | ctor h_classify =>
      cases top
      · injection h_classify ▸ hMatch_f.head_wf_eq hWF.1 with h_eq; injection h_eq; omega
      · cases h_classify ▸ hMatch_f.head_wf_eq hWF.1
    | indTy h => cases top <;> cases h ▸ hMatch_f.head_wf_eq hWF.1
    | pat hP hM =>
      cases top
      · cases pat_arity hP hM.arity ▸ hMatch_f.head_wf_eq hWF.1
      · injection pat_arity hP hM.arity ▸ hMatch_f.head_wf_eq hWF.1 with h_eq
        injection h_eq; omega
    | @lam f' _ _ hRec hle_lam
    let arg : WShape (k' + 1) := .ctor' c_a rargs_a.reverse
    obtain ⟨x', hx'_le, hx'_mem⟩ := WShapeFun.app_eq f' arg
    refine hRec x' (f'.app arg) hx'_mem
      |>.mono_l (.cons hx'_le <| .rfl fun _ _ => .rfl) |>.mono ?_ .mono
    refine WShape.lam'_app ▸ TShape.app_mono (hle_f.trans hle_lam) (hle_a.trans ?_)
    cases hConst_a with
    | bot => exact TShape.bot_eqv.1.trans TShape.bot_le'
    | ctor _ h_bound => exact h_bound
    | pat hP hM => cases pat_arity hP hM.arity ▸ hMatch_a.head_wf_eq hWF.2
    | indTy h => cases h ▸ hMatch_a.head_wf_eq hWF.2
    | lam hRec hle_lam
    refine hle_lam.trans ?_ |>.trans TShape.bot_le
    rw [WShape.lam']; split <;> [rename_i hf; exact TShape.bot_eqv.1]
    obtain ⟨⟨s, t⟩, hxy, hn⟩ := WShapeFun.NonZero.iff.1 hf
    refine hn (WShape.LE.T_iff.1 (.trans ?_ TShape.bot_eqv.2)) |>.elim
    refine (hRec s t hxy).compat_mismatch (rargs2 := rargs_a) (by simp) <| .inl ?_
    simpa using hMatch_a.head_wf_eq hWF.2

theorem LE_Interp.build_spine {m1 : p.Path → TShape} {m2} (a2 : p.MatchesS LHS ls m2)
    (W : Valuation.Fits Γ₀ Γ ρ) (hTy : StrongSound Γ LHS A)
    (p_wf : p.WF Params.classify top extra)
    (hpath : ∀ path, LE_Interp ρ (m1 path) (m2 path)) :
    ∃ n', ∀ k, n' ≤ k → ∃ c rargs m' rAs,
      Matches (n := k) p c rargs m' ∧ (∀ path, m1 path ≤ m' path) ∧
      List.Forall₂ (LE_Interp ρ ·.T) rargs rAs ∧
      rAs.foldr (fun A acc => .app acc A) (.const c ls) = LHS := by
  induction a2 generalizing A top extra with
  | const => exact ⟨0, fun k _ => ⟨_, [], nofun, [], .const, nofun, .nil, rfl⟩⟩
  | @var _ _ _ _ X _ ih =>
    have ⟨_, _, hTy, _⟩ := hTy; have .app _ hTy_inner _ := hTy
    obtain ⟨n', ih⟩ := ih hTy_inner p_wf (hpath <| .some ·)
    refine ⟨max n' (m1 none).1, fun k hk => ?_⟩
    have ⟨hk_inner, hk_none⟩ := Nat.max_le.1 hk
    obtain ⟨_, _, m', spine, hMatch, hpath', forall2, foldr_eq⟩ := ih _ hk_inner
    let a_top : WShape k := (m1 none).2.lift k
    exact ⟨_, _, _, _, hMatch.var, (·.casesOn (TShape.lift_eqv hk_none).2 hpath'),
      .cons ((hpath none).mono (TShape.lift_eqv hk_none).1) forall2, congrArg (·.app X) foldr_eq⟩
  | @app _ _ _ _ _ M_a f2 _ _ _ ihf iha =>
    have ⟨_, _, hTy, _⟩ := hTy; have .app (A := B) hB hTy_f hTy_a := hTy
    obtain ⟨nf, ihf'⟩ := ihf hTy_f p_wf.1 (hpath <| .inl ·)
    obtain ⟨na, iha'⟩ := iha hTy_a p_wf.2 (hpath <| .inr ·)
    refine ⟨max nf (na + 1), fun k hk => ?_⟩
    rw [Nat.max_le] at hk; let k' + 1 := k; simp at hk
    obtain ⟨_, rargs_f, mf', Fs, hMatch_f, hpath_f, forall2_f, foldr_eq_f⟩ := ihf' _ hk.1
    obtain ⟨c_a, rargs_a, ma', As, hMatch_a, hpath_a, forall2_a, foldr_eq_a⟩ := iha' _ hk.2
    have hTy_at_foldr := foldr_eq_a ▸ hTy_a
    have h_ctor_head := by simpa using hMatch_a.head_wf_eq (k := 0) p_wf.2
    obtain ⟨ci, h_env, h_uvars, I, Ts, args, _, hTs, hI, hu0, heq, hcit⟩ :
        ∃ ci, Params.env.constants c_a = some ci ∧ f2.length = ci.uvars ∧ ∃ I Ts args u,
          Ts.length = rargs_a.length ∧ Params.classify I = some (.indTy args.length) ∧ u ≠ .zero ∧
          let e := List.foldr .forallE (List.foldr (fun A acc => acc.app A) (.const I f2) args) Ts
          SoundEq Γ (SExpr.mkInst f2 ci.type) e ∧ StrongSound Γ e (.sort u) := by
      clear forall2_a hTy_f hTy_a foldr_eq_a hB
      induction As generalizing B with have ⟨_, _, hTy, _⟩ := hTy_at_foldr
      | nil =>
        have .const h1 h2 F h3 h4 := hTy
        have cl : CtorBundle.IsCtor c_a := ⟨_, h_ctor_head, rfl⟩
        unfold CtorBundle.rhs at h3
        have cl1 := Option.some.inj <| cl.cl.2.1.symm.trans h_ctor_head
        exact ⟨_, h1, h2, _, _, _, _, (cl1 ▸ (F cl).hlen :), (F cl).hclI, (F cl).hu0, h3 cl, h4 cl⟩
      | cons A rest ih => have .app _ hMf _ := hTy; exact ih _ hMf
    have h_classify' := forall2_a.length_eq ▸ h_ctor_head
    refine ⟨_, _, _, _, hMatch_f.app hMatch_a, (·.casesOn hpath_f hpath_a),
      .cons ?_ forall2_f, congrArg (·.app M_a) foldr_eq_f⟩
    refine foldr_eq_a ▸ .apps_realize W (WShape.HasType.T_iff.2 .ctor')
      ?_ hTy_at_foldr forall2_a (.ctor h_ctor_head .rfl)
    refine LE_Interp.apps_realize_inv (k := 0) W h_env heq
      (hTs.trans forall2_a.length_eq).symm hTy_at_foldr ?_
    let e := args.foldr (fun A acc => acc.app A) (SExpr.const I f2)
    have {Ts Γ ρ u} (W : Valuation.Fits Γ₀ Γ ρ) (hu0 : u ≠ .zero)
        (h_intr : StrongSound Γ (List.foldr .forallE e Ts) (.sort u)) :
        ∃ Γ u, u ≠ .zero ∧ (Ts.length.repeatTR (·.push .bot) ρ).Fits Γ₀ Γ ∧
          StrongSound Γ e (.sort u) := by
      induction Ts generalizing Γ ρ u with | nil => exact ⟨_, _, hu0, W, h_intr⟩ | cons T Ts ih
      have ⟨_, _, h_intr, h_imax_defeq⟩ := h_intr; have .forallE (u := u) (v := v) h1 h2 := h_intr
      refine ih ?_ (mt (fun h_zero => ?_) hu0) h2
      · exact W.cons (InterpTyped.hsort (h1.sound W)) .bot (.bot' (.bot' .sort))
      have h_LE_zero : LE_Interp ρ (.sort false) (.sort (u.imax v)) :=
        .sort (by simp [TShape.LE.rfl, SLevel.imax_eq_zero, h_zero])
      have := WShape.sort_le.1 <| .of_T ((h_imax_defeq W).1 h_LE_zero).le_sort
      injection congrArg (·.1) this with eq; simpa using eq
    obtain ⟨Γ', u_body, hu0, W, h_body_typed⟩ := this W hu0 hcit
    rw [← Nat.repeat_eq_repeatTR] at W; simp [← forall2_a.length_eq, ← hTs]
    refine .apps_realize (rargs := .replicate args.length (.bot (n := k'+1)))
      W (WShape.HasType.T_iff.2 .indTy) ?_ h_body_typed ?_ ?_
    · exact .sort (decide_eq_true hu0 ▸ TShape.sort_eqv.1)
    · clear hI h_body_typed hcit this heq
      induction args with | nil => exact .nil | cons _ _ ih => exact .cons .bot ih
    · simpa only [List.map_replicate, WShape.lift_bot] using
        Const.indTy (rargs := .replicate args.length .bot) (List.length_replicate ▸ hI) .rfl
          |>.lift k'.le_succ .mono

/-- The proof-relevant payload retained while reversing one generated iota
action.

The public equality only says that the instantiated RHS and the matched
redex have the same interpretations.  That is insufficient for recursive
consumers: rebuilding the redex through the ambient `LE_Interp` relation may
select a different witness for the registered fixed head.  This certificate
instead stores the literal head sub-witness peeled from `hRhs`, the ordered
semantic capture spine, and the constant evaluator whose recursive relation
is exactly `headWitness.LowerEdge`.

The certificate also retains the exact stratified typing of the applied RHS
and the native typing exposed for its literal fixed head.  The
derivation-aware conversion caller still supplies the semantic type witness
used to realize the redex below; retaining the syntax derivations here keeps
the later guarded producer from reselecting either endpoint. -/
structure _root_.Lean4Lean.Pattern.IotaRule.FocusedActionPreimage
    {rec ctor : Name} {major arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (rule : Pattern.IotaRule r)
    {Gamma : List SExpr} {e : SExpr} {ls : List SLevel}
    {capture : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
    {A : SExpr} {rho : Valuation} {out : TShape}
    (action : Pattern.Action Gamma r e ls capture A)
    (hRhs : LE_Interp.Witness rho out (r.1.applyS ls capture))
    (rhsDepth : Nat) where
  rhsStratified : HasTypeStratifiedS Gamma
    (r.1.applyS ls capture) A true rhsDepth
  headType : SExpr
  headStratified : HasTypeStratifiedS Gamma
    (SExpr.mkInst ls rule.df.rhs) headType true
      (rhsDepth - rule.capturePaths.length)
  mcap : (RecursorIotaPattern rec major ctor arity).Path → TShape
  captureInterp : ∀ path, LE_Interp rho (mcap path) (capture path)
  head : TShape
  headWitness : LE_Interp.Witness rho head
    (SExpr.mkInst ls rule.df.rhs)
  spine : LE_Interp.RHS.ShapeSpine
    mcap head rule.capturePaths out
  argLevel : Nat
  constantName : Name
  args : List (WShape argLevel)
  matchedCapture :
    (RecursorIotaPattern rec major ctor arity).Path → TShape
  argExprs : List SExpr
  matched : LE_Interp.Matches
    (RecursorIotaPattern rec major ctor arity)
    constantName args matchedCapture
  capture_le : ∀ path, mcap path ≤ matchedCapture path
  argsInterp : List.Forall₂ (LE_Interp rho ·.T) args argExprs
  lhs_eq :
    argExprs.foldr (fun arg fn => fn.app arg)
      (.const constantName ls) = e
  constantInterp : LE_Interp.Const constantName ls
    headWitness.LowerEdge args out

/-- Reverse a generated iota action without broadening its fixed-head
evaluator edge.

`focusedShapeSpine` first peels the exact RHS witness.  `build_spine` then
reconstructs only the matched constant/argument prefix, and `focusedRHS`
installs root lowerings of that same head witness as the constant's abstract
evaluator relation.  No proof-independent call to `RHS.of_applyS` occurs. -/
theorem _root_.Lean4Lean.Pattern.IotaRule.focusedActionPreimage
    {rec ctor : Name} {major arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (rule : Pattern.IotaRule r)
    {Gamma : List SExpr} {e : SExpr} {ls : List SLevel}
    {capture : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
    {A : SExpr} {rho : Valuation} {out : TShape}
    (action : Pattern.Action Gamma r e ls capture A)
    (hLeft : StrongSound Gamma e A)
    (W : Valuation.Fits Gamma0 Gamma rho)
    (hRhs : LE_Interp.Witness rho out (r.1.applyS ls capture))
    (hRhsStratified : HasTypeStratifiedS Gamma
      (r.1.applyS ls capture) A true rhsDepth)
    (hout : ¬out ≤ TShape.bot) :
    Nonempty (rule.FocusedActionPreimage action hRhs rhsDepth) := by
  obtain ⟨mcap, hcap, head, hhead, hspine⟩ :=
    rule.focusedShapeSpine hRhs hout
  obtain ⟨headType, hheadStratified⟩ :=
    rule.rhsHeadStratified hRhsStratified
  obtain ⟨threshold, built⟩ :=
    LE_Interp.build_spine action.matched W hLeft
      (Params.pat_wf action.pat) hcap
  obtain ⟨constantName, args, matchedCapture, argExprs,
    hmatch, hcapture, hargs, hlhs⟩ :=
    built threshold (Nat.le_refl threshold)
  refine ⟨{
    rhsStratified := hRhsStratified
    headType := headType
    headStratified := hheadStratified
    mcap := mcap
    captureInterp := hcap
    head := head
    headWitness := hhead
    spine := hspine
    argLevel := threshold
    constantName := constantName
    args := args
    matchedCapture := matchedCapture
    argExprs := argExprs
    matched := hmatch
    capture_le := hcapture
    argsInterp := hargs
    lhs_eq := hlhs
    constantInterp := ?_ }⟩
  exact .pat action.pat hmatch
    ((rule.focusedRHS hhead hspine).mono_l hcapture)

/-- Realize the redex stored by a focused reverse-action certificate at the
caller's exact typed observation.

The returned witness is built with `appsRealizeFocused`; unfolding this
definition exposes the certificate's `headWitness.LowerEdge` relation at the
constant node.  A later `RDeepChildren` rebuild can therefore attach its
local seed to the same fixed-head witness that was peeled from the RHS. -/
noncomputable def _root_.Lean4Lean.Pattern.IotaRule.FocusedActionPreimage.witness
    {rec ctor : Name} {major arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {rule : Pattern.IotaRule r}
    {Gamma : List SExpr} {e : SExpr} {ls : List SLevel}
    {capture : (RecursorIotaPattern rec major ctor arity).Path → SExpr}
    {A : SExpr} {rho : Valuation} {out outTy : TShape}
    {action : Pattern.Action Gamma r e ls capture A}
    {hRhs : LE_Interp.Witness rho out (r.1.applyS ls capture)}
    {rhsDepth : Nat}
    (H : rule.FocusedActionPreimage action hRhs rhsDepth)
    (W : Valuation.Fits Gamma0 Gamma rho)
    (hLeft : StrongSound Gamma e A)
    (hout : out.HasType outTy)
    (hA : LE_Interp.Witness rho outTy A) :
    LE_Interp.Witness rho out e := by
  let hbuilt := LE_Interp.Witness.appsRealizeFocused
    W hout hA (H.lhs_eq.symm ▸ hLeft) H.argsInterp
    H.headWitness H.constantInterp
  exact H.lhs_eq ▸ hbuilt

/-- Semantic strong typing of a constant needs its constructor bundles but
not its definition unfoldings.  Keeping this fragment separate is what lets
the definition-only strong constructor type its left endpoint finitely. -/
theorem StrongSound.of_const
    (hreg : Params.env.constants c = some ci)
    (hlen : ls.length = ci.uvars)
    (F : ∀ cl, CtorBundle c cl)
    (hF : ∀ cl, StrongSoundEq Γ (SExpr.mkInst ls ci.type)
      ((F cl).rhs ls) (.sort (F cl).u)) :
    StrongSound Γ (.const c ls) (SExpr.mkInst ls ci.type) := by
  refine ⟨.const hreg hlen, fun _ _ W _ h => ?_,
    .const hreg hlen F (fun cl => (hF cl).sound) (fun cl => (hF cl).right),
    .rfl⟩
  generalize eq : SExpr.const c ls = M at h
  induction h with cases eq
  | bot => exact .mk .rfl .bot .bot (.bot_T' <| .bot .sort)
  | const b1 b2 b3 b4 b5 b6 b7 =>
    cases hreg.symm.trans b1
    exact .mk b3 (.const b1 b2 .rfl b4 b5 b6 b7) b5 b4

/-- Turn one proof-carrying local contraction into semantic soundness once
both endpoints have independently obtained strong typings. -/
theorem StrongSoundEq.ofAction
    (action : Pattern.Action Γ r e m1 m2 A)
    (hLeft : StrongSound Γ e A)
    (hRight : StrongSound Γ (r.1.applyS m1 m2) A) :
    StrongSoundEq Γ e (r.1.applyS m1 m2) A := by
  refine ⟨action.sound, fun Γ₀ ρ W m => ?_, hLeft, hRight⟩
  by_cases hm : m ≤ TShape.bot
  · exact TShape.le_bot'.1 hm ▸ (LE_Interp.sound_bot (A := default)).1
  refine ⟨fun hLE => ?_, fun hLE => ?_⟩
  · obtain ⟨_, built⟩ :=
      LE_Interp.Matches.of_matchesS action.matched
        (Params.pat_wf action.pat) hLE
    obtain ⟨_, rargs, m_path, m_head, hMatch, hpath, hle, hConst⟩ :=
      built _ (Nat.le_refl _)
    cases hConst with
    | bot => cases hm (hle.trans TShape.bot_eqv.1)
    | lam hRec hle_lam =>
      refine hm ((hle.trans hle_lam).trans ?_) |>.elim
      rw [WShape.lam']
      split <;> [rename_i hf; exact TShape.bot_eqv.1]
      obtain ⟨⟨s, t⟩, hxy, hn⟩ := WShapeFun.NonZero.iff.1 hf
      refine (hn (WShape.LE.T_iff.1 (.trans ?_ TShape.bot_eqv.2))).elim
      exact (hRec s t hxy).compat_mismatch (by simp) <|
        .inr <| .inr ⟨_, _, _, action.pat, hMatch⟩
    | ctor h | indTy h =>
      obtain ⟨_, h_symb⟩ := hMatch.head_wf (Params.pat_wf action.pat)
      cases h ▸ h_symb
    | pat hP hM hRHS' =>
      obtain ⟨_, hi⟩ := hM.matches_inter (.rfl fun _ _ => .rfl)
        (Params.pat_wf hP) hMatch (Params.pat_wf action.pat)
      obtain ⟨rfl, -, ⟨⟩⟩ := Params.pat_uniq action.pat hP .refl hi
      exact .mono hle <| LE_Interp.RHS.le_applyS hpath (fun _ _ => id) <|
        LE_Interp.Matches.unique (Params.pat_wf action.pat) hM hMatch ▸ hRHS'
  · have ⟨_, _, a, hm_lvl, hm_le_typed, h_LE_m_typed_R, ha,
        h_m_typed_HT⟩ := (hRight.sound W hLE).out
    obtain ⟨m_path_T, hpath, hRHS⟩ :=
      LE_Interp.RHS.of_applyS h_LE_m_typed_R
    obtain ⟨_, built⟩ :=
      LE_Interp.build_spine action.matched W hLeft
        (Params.pat_wf action.pat) hpath
    obtain ⟨c, rargs, m', rAs, hMatch, hbnd, h_per_arg, h_foldr_eq⟩ :=
      built _ (Nat.le_refl _)
    exact .mono hm_le_typed <| h_foldr_eq ▸
      LE_Interp.apps_realize W h_m_typed_HT.T ha
      (h_foldr_eq ▸ hLeft) h_per_arg (.pat action.pat hMatch (hRHS.mono_l hbnd))

theorem LE_Interp.strongSound (H : IsDefEqStrong Γ M N A) : StrongSoundEq Γ M N A := by
  induction H with
  | @bvar _ i A _ h h2 ih =>
    refine .rfl ⟨.bvar h, fun _ _ W _ h => ?_, .bvar h, .rfl⟩; clear h2 ih
    generalize eq : SExpr.bvar i = M at h
    induction h with cases eq | bot => exact .mk .rfl .bot .bot (.bot_T' <| .bot .sort) | bvar a1
    induction W generalizing i A with | cons _ h1 h2 h3 ih => ?_ | nil =>
      exact TShape.le_bot'.1 a1 ▸ .mk .rfl .bot .bot (.bot_T' <| .bot .sort)
    cases h with simp [Valuation.push] at a1
    | zero => exact ⟨_, _, a1, .bvar .rfl, h2.weak, h3⟩
    | succ h => have ⟨_, _, le, h1, h2, h3⟩ := ih h a1; exact ⟨_, _, le, h1.weak, h2.weak, h3⟩
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | @sort _ l =>
    refine .rfl ⟨.sort, fun _ _ W _ h => ?_, .sort, .rfl⟩
    generalize eq : SExpr.sort l = M at h
    induction h with cases eq
    | bot => exact .mk .rfl .bot .bot (.bot_T' <| .bot .sort)
    | sort h1 => exact .mk h1 (.sort .rfl) (.sort .rfl) (by simpa using .sort)
  | @const c _ _ ls _ a1 a2 a3 F a4 hDef ih1 ih2 ihDef =>
    exact .rfl (StrongSound.of_const a1 a2 F ih2)
  | appDF _ _ _ _ _ ihA _ ih1 ih2 ih3 =>
    refine .mk' (.appDF ih1.defeq ih2.defeq)
      (.app ihA.left.sound ih1.left ih2.left) .rfl
      (.app ihA.left.sound ih1.right ih2.right) ih3.sound.symm fun _ _ W m => ?_
    by_cases hm : m ≤ TShape.bot; · exact TShape.le_bot'.1 hm ▸ sound_bot
    refine ⟨⟨fun h => ?_, fun h => ?_⟩,
      sound_app (ih1.left.sound W) (InterpTyped.hsort (ih3.left.sound W))⟩ <;>
      cases h with | bot => cases hm TShape.bot_le' | app h1 h2 h3
    · exact .app ((ih1.sound W).1 h1) ((ih2.sound W).1 h2) h3
    · exact .app ((ih1.sound W).2 h1) ((ih2.sound W).2 h2) h3
  | lamDF _ _ _ _ _ ih1 _ _ ih2 ih3 =>
    refine .mk' (.lamDF ih1.defeq ih2.defeq)
      (.lam ih1.left.sound ih2.left) .rfl
      (.lam ih1.right.sound ih3.right)
      (.symm <| .forallE ih1.left.sound ih1.sound .rfl) fun _ _ W m => ?_
    by_cases hm : m ≤ TShape.bot; · exact TShape.le_bot'.1 hm ▸ sound_bot
    refine ⟨⟨fun h => ?_, fun h => ?_⟩,
      sound_lam (InterpTyped.hsort (ih1.left.sound W)) fun h1 h2 =>
      (ih2.left.sound (W.cons (InterpTyped.hsort (ih1.left.sound W)) h1 h2))⟩ <;>
      cases h with | bot => cases hm TShape.bot_le' | lam h1 h2 h3 h4
    · refine .lam ((ih1.sound W).1 h1) h2 (fun _ h => ?_) h4
      exact (ih2.sound (W.cons (InterpTyped.hsort (ih1.left.sound W)) h1 h.T)).1 (h3 _ h)
    · refine .lam ((ih1.sound W).2 h1) h2 (fun _ h => ?_) h4
      refine (ih2.sound (W.cons ?_ ((ih1.sound W).2 h1) h.T)).2 (h3 _ h)
      exact InterpTyped.hsort (ih1.left.sound W)
  | forallEDF _ _ _ ih1 ih2 ih3 =>
    refine .mk' (.forallEDF ih1.defeq ih2.defeq)
      (.forallE ih1.left ih2.left) .rfl (.forallE ih1.right ih3.right) .rfl fun _ _ W m => ?_
    by_cases hm : m ≤ .bot; · exact TShape.le_bot'.1 hm ▸ sound_bot
    refine ⟨⟨fun h => ?_, fun h => ?_⟩,
      sound_forallE (InterpTyped.hsort' (ih1.left.sound W)) fun h1 h2 =>
      (ih2.left.sound (W.cons (InterpTyped.hsort (ih1.left.sound W)) h1 h2))⟩ <;>
      try cases h with | bot => cases hm TShape.bot_le' | forallE h1 h2 h3 h4 h5
    · refine .forallE ((ih1.sound W).1 h1) ((ih1.sound W).1 h2) h3 (fun _ h => ?_) h5
      exact (ih2.sound (W.cons (InterpTyped.hsort (ih1.left.sound W)) h2 h.T)).1 (h4 _ h)
    · refine .forallE ((ih1.sound W).2 h1) ((ih1.sound W).2 h2) h3 (fun _ h => ?_) h5
      refine (ih2.sound (W.cons ?_ ((ih1.sound W).2 h2) h.T)).2 (h4 _ h)
      exact InterpTyped.hsort (ih1.left.sound W)
  | defeqDF h1 h2 ih1 ih2 =>
    have ⟨a1, a2, a3, a4⟩ := ih2.left
    have ⟨b1, b2, b3, b4⟩ := ih2.right
    have hd := h1.defeq.defeqDF h2.defeq
    refine ⟨hd, ih2.sound, ?_, ?_⟩
    · exact ⟨hd.hasType.1, a2.defeq_r ih1.sound, a3, a4.trans ih1.sound⟩
    · exact ⟨hd.hasType.2, ih2.right.sound.defeq_r ih1.sound, b3, b4.trans ih1.sound⟩
  | beta _ _ _ _ ih1 ih2 ih3 ih4 =>
    refine ⟨.beta ih1.defeq ih2.defeq, fun _ _ W m => ?_, ih3.left, ih4.left⟩
    by_cases hm : m ≤ .bot; · exact TShape.le_bot'.1 hm ▸ (sound_bot (A := default)).1
    refine ⟨fun h => ?_, fun h => ?_⟩
    · cases h with | bot => cases hm TShape.bot_le' | @app _ n₁ _ _ _ _ a h1 h2 h3
      cases h1 with | bot => cases hm (h3.trans TShape.bot_eqv.1) | @lam _ n₂ _ _ f' _ _ h4 h5 h6 h7
      let k := max n₂ n₁; have hk := Nat.max_le.1 (Nat.le_refl k)
      have ⟨_, _, a1, a2, a3, a4⟩ := ih2.left.sound W h2
      obtain ⟨_, b1, b2⟩ := WShapeFun.app_eq (f'.lift k) (a.lift k)
      obtain ⟨a', y', b2', rfl, yb_eq⟩ := (WShapeFun.mem_lift hk.1).1 b2
      obtain ⟨bx', bxle, bx_ht, bapp⟩ := WShape.HasDom.iff.1 h5 a'
      refine LE_Interp.inst.2 ⟨_, ?_, (h2.lift hk.2).mono b1.T⟩
      refine .mono_l (Valuation.LE.push.2 ⟨.rfl, bxle.T.trans (TShape.lift_eqv hk.1).2⟩) ?_
      refine (h6 bx' bx_ht).mono <| h3.trans <| .trans ?_ bapp.T
      rw [TShape.LE.def hk.2 hk.1, WShape.lift_app hk.2]
      have h7' := (TShape.LE.def (Nat.succ_le_succ hk.2) (Nat.succ_le_succ hk.1)).1 h7
      refine (WShape.app_mono_l h7' _).trans ?_
      rw [WShape.lift_lam' hk.1, WShape.lam'_app, yb_eq]
      exact WShape.lift_mono hk.1 (WShapeFun.app_of_mem b2').2
    · have ⟨_, h1, h2⟩ := LE_Interp.inst.1 h
      have ⟨e, a, a1, a2, a3, a4⟩ := ih2.left.sound W h2
      let k := max m.1 (max e.1 a.1); have hk := Nat.max_le.1 (Nat.le_refl k); rw [Nat.max_le] at hk
      have := (WShape.HasDom.single (y := m.2.lift k)).2 <| .inl <|
        (TShape.HasType.def hk.2.1 hk.2.2).1 a4
      refine .mono ?_ <| .app' (.lam' (a3.lift hk.2.2) this fun _ hx => ?_) (a2.lift hk.2.1)
      · rw [WShape.lam'_app, WShapeFun.single_app, if_pos .rfl]; exact (TShape.lift_eqv hk.1).2
      · simp [WShapeFun.single_app]; split <;> [rename_i h; exact .bot]
        refine (h1.lift hk.1).mono_l <| Valuation.LE.push.2 ⟨.rfl, a1.trans ?_⟩
        exact (TShape.LE.lift_l hk.2.1).2 h
  | @eta _ F _ _ _ _ ih1 ih2 =>
    refine ⟨.eta ih1.defeq, fun _ ρ W m => ?_, ih2.left, ih1.left⟩
    by_cases hm : m ≤ .bot; · exact TShape.le_bot'.1 hm ▸ (sound_bot (A := default)).1
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have ⟨e, t, h1, h2, h3, h4⟩ := ih2.left.sound W h
      have ht : ¬t ≤ .bot := fun h => hm (h1.trans (h4.bot_r' h))
      cases h2 with
      | bot => cases hm (h1.trans TShape.bot_le')
      | @lam _ n _ _ f' _ _ h2a h2d h2f h2le
      cases h3 with | bot => cases ht TShape.bot_le' | forallE b1 b2 b3 b4 b5
      cases b5.le_forall with | bot b5 => cases ht b5 | forallE b5 b6
      obtain rfl | ⟨n₂, g, rfl, c1⟩ := h4.ty_forallE_inv; · cases hm (h1.trans TShape.bot_le')
      have key {x y} (hmem : (x, y) ∈ f') :
          LE_Interp ρ (WShape.T (n := n+1) (.lam' (WShapeFun.single x y))) F := by
        by_cases hy : y ≤ .bot
        · refine .mono (WShape.LE.T (?_ : _ ≤ .bot)) .bot
          rw [← WShape.lam'_bot, WShape.lam'_le_lam', WShapeFun.single_le]
          exact ⟨_, _, by simp [WShapeFun.mem_bot], WShape.bot_le, hy⟩
        rw [WShape.le_bot] at hy
        obtain ⟨x', x'le, x'ht, x'app⟩ := WShape.HasDom.iff.1 h2d x
        have := (h2f x' x'ht)
          |>.mono_l (Valuation.LE.push.2 ⟨.rfl, x'le.T⟩)
          |>.mono (WShape.LE.T <| (WShapeFun.app_of_mem hmem).2.trans x'app)
        cases this with | bot => cases hy rfl | @app _ n' f _ _ _ a' c1 c2 c3
        cases f using WShape.casesOn' with
        | lam g => ?_
        | _ => cases hy (TShape.le_bot.1 (c3.trans TShape.bot_le'))
        obtain ⟨x'', hle, mem⟩ := WShapeFun.app_eq g a'
        have le₁ := Nat.le_max_left n' n; have le₂ := Nat.le_max_right n' n
        refine (LE_Interp.weak_iff.1 c1).mono ?_
        refine (TShape.LE.def (Nat.succ_le_succ le₂) (Nat.succ_le_succ le₁)).2 ?_
        rw [WShape.lift_lam' le₂, WShapeFun.lift_single le₂, WShape.lam_eq_lam',
          WShape.lift_lam' le₁, WShape.lam'_le_lam', WShapeFun.single_le]
        exact ⟨_, _, (WShapeFun.mem_lift le₁).2 ⟨_, _, mem, rfl, rfl⟩,
          hle.T.trans (LE_Interp.bvar_iff.1 c2), (TShape.LE.def le₂ le₁).1 c3⟩
      have main (l : List (WShape n × WShape n)) (H : ∀ p, p ∈ l → p ∈ f') :
          ∃ g, (∀ z : WShapeFun n, g ≤ z ↔ ∀ x ∈ l, .single x.1 x.2 ≤ z) ∧
            LE_Interp ρ (WShape.T (.lam' g)) F := by
        induction l with | nil => exact ⟨.bot, by simp, WShape.lam'_bot ▸ .bot⟩ | cons p l ih
        obtain ⟨x, y⟩ := p; simp only [List.mem_cons, forall_eq_or_imp] at H
        have ⟨g, a1, a2⟩ := ih H.2
        have hc := (key H.1).compat a2
        have hJ := WShapeFun.Join.mk <| WShape.Compat.lam'.1 <| WShape.Compat.T_iff.2 hc
        refine ⟨_, fun z => (hJ _).trans <| .trans ?_ List.forall_mem_cons.symm, ?_⟩
        · exact and_congr_right' (a1 _)
        · exact (key H.1).join (WShape.Join.lam'.2 hJ).T a2
      have ⟨g, a1, a2⟩ := main f'.elems fun _ => WShapeFun.mem_elems.1
      refine a2.mono (h2le.trans (WShape.lam'_le_lam'.2 ?_).T) |>.mono h1
      refine WShapeFun.LE.def'.2 fun x' y' hmem => WShapeFun.single_le.1 ?_
      exact (a1 _).1 .rfl _ (WShapeFun.mem_elems.2 hmem)
    · have ⟨m', f, a1, a2, a3, a4⟩ := ih1.left.sound W h
      have hm' : ¬m' ≤ .bot := fun h => hm (a1.trans h)
      have hf : ¬f ≤ .bot := fun h => hm' (a4.bot_r' h)
      cases a3 with | bot => cases hf TShape.bot_le' | forallE b1 b2 b3 b4 b5
      cases b5.le_forall with | bot b5 => cases hf b5 | @forallE m _ _ _ _ b5 b6
      obtain rfl | ⟨n₂, g, rfl, c1⟩ := a4.ty_forallE_inv; · cases hm' TShape.bot_le'
      have le_k := Nat.le_max_left n₂ m; have le_m := Nat.le_max_right n₂ m
      refine .mono (WShape.lift_lam' le_k ▸ a1.trans (TShape.lift_eqv (Nat.succ_le_succ le_k)).2) <|
        .lam' ((b1.mono b5).lift (Nat.le_max_right ..)) c1.2.1 fun _ _ => ?_
      simpa only [WShape.lift_lam' le_k, WShape.lam'_app] using
        (a2.lift (Nat.succ_le_succ le_k)).weak.app' .bvar0
  | @proofIrrel _ p h h' _ _ _ ih1 ih2 ih3 =>
    refine ⟨.proofIrrel ih1.defeq ih2.defeq ih3.defeq, fun _ ρ W m => ?_, ih2.left, ih3.left⟩
    suffices ∀ {h h'}, InterpTyped ρ m h p → LE_Interp ρ m h → LE_Interp ρ m h' from
      ⟨fun h => this (ih2.left.sound W h) h, fun h => this (ih3.left.sound W h) h⟩
    refine fun ⟨_, _, a1, a2, a3, a4⟩ h1 => .mono (?_ : m ≤ .bot) .bot
    have ⟨_, _, b1, b2, b3, b4⟩ := ih1.left.sound W a3
    have b4' := TShape.HasType.mono_r (by simpa using b3.le_sort) .sort b4
    exact a1.trans (b4'.proofIrrel (b4'.mono_r b1 a4))
  | @defn c ci Γ ls u r hreg hlen hTy F hF action hRhs
      ihTy ihF ihRhs =>
    exact StrongSoundEq.ofAction action
      (StrongSound.of_const hreg hlen F ihF) ihRhs.left
  | extra action hTy_lhs hTy_rhs ih1 ih2 =>
    exact StrongSoundEq.ofAction action ih1.left ih2.left

theorem LE_Interp.sound (H : IsDefEqStrong Γ M N A) (W : Valuation.Fits Γ₀ Γ ρ) {m} :
    (LE_Interp ρ m M ↔ LE_Interp ρ m N) ∧ (LE_Interp ρ m M → InterpTyped ρ m M A) :=
  ⟨(strongSound H).sound W, (strongSound H).left.sound W⟩

/-- A source valuation whose non-identity entries retain exact witnesses
for their syntactic types and every recursive constant edge below them. -/
inductive LE_Interp.Witness.FitsRDeep
    (P : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop)
    (base : List SExpr) : List SExpr → Valuation → Prop where
  | nil : FitsRDeep P base base .nil
  | cons : FitsRDeep P base Γ ρ →
    (∃ a, ∃ hA : LE_Interp.Witness ρ a A,
      x.HasType a ∧ hA.RDeepChildren P) →
    FitsRDeep P base (A :: Γ) (ρ.push x)

theorem LE_Interp.Witness.FitsRDeep.lookup
    (laws : LE_Interp.Witness.RDeepChildren.Laws P)
    (W : LE_Interp.Witness.FitsRDeep P Γ₀ Γ ρ)
    (H : Lookup Γ i A) :
    LE_Interp.Witness.TypedRDeep P ρ (ρ i) (.bvar i) A := by
  induction W generalizing i A with
  | nil => exact .bot TShape.bot_eqv.1
  | @cons Γ' ρ' A' x W binding ih =>
    cases H with
    | zero =>
      obtain ⟨a, hA, hxa, cA⟩ := binding
      let hvar : LE_Interp.Witness (ρ'.push x) x (.bvar 0) := .bvar .rfl
      exact ⟨x, a, hvar, hA.weak, .rfl, hxa,
        .bvar, cA.weak laws.closed⟩
    | succ H =>
      simpa [Valuation.push, SExpr.lift, SExpr.lift', Lift.liftVar,
        Nat.add_comm] using (ih H).weak laws.closed (x := x)

theorem LE_Interp.Witness.FitsRDeep.push
    (W : LE_Interp.Witness.FitsRDeep P Γ₀ Γ ρ)
    (hA : LE_Interp.Witness.TypeRDeep P ρ a A)
    (hx : x.HasType a) :
    LE_Interp.Witness.FitsRDeep P Γ₀ (A :: Γ) (ρ.push x) := by
  obtain ⟨a', hA, hle, ha', cA⟩ := hA
  exact .cons W ⟨a', hA, ha'.mono_r hle hx, cA⟩

/-- Choose exact binding witnesses from an ordinary valid valuation.  The
retained predicate is trivial, so this changes no public semantic content. -/
theorem Valuation.Fits.toFitsRDeepTrue
    (W : Valuation.Fits Γ₀ Γ ρ) :
    LE_Interp.Witness.FitsRDeep (fun _ => True) Γ₀ Γ ρ := by
  induction W with
  | nil => exact .nil
  | cons _ _ hA hx ih =>
    exact .cons ih ⟨_, hA.witness, hx,
      LE_Interp.Witness.RDeepChildren.trivial _⟩

/-- Retained semantic typing for every stratified derivation at one exact
depth. Public valuation validity is kept alongside the exact witness trees
because semantic conversion is intentionally proof-independent. -/
def LE_Interp.Witness.SoundRDeepAt
    (P : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop)
    (Γ₀ : List SExpr) {ρ m M}
    (hM : LE_Interp.Witness ρ m M) (d : Nat) : Prop :=
  ∀ {Γ A core}, HasTypeStratifiedS Γ M A core d →
    LE_Interp.Witness.FitsRDeep P Γ₀ Γ ρ →
    Valuation.Fits Γ₀ Γ ρ →
    LE_Interp.Witness.TypedRDeep P ρ m M A

/-- Prove retained semantic typing below a fixed depth bound. Syntax-directed
children use the ordinary typing induction; conversion and binder valuation
validity restart on an arbitrary exact witness only after a strict depth
decrease. -/
theorem LE_Interp.Witness.soundRDeepRestart
    (laws : LE_Interp.Witness.RDeepChildren.Laws P)
    (restart : ∀ (d' : Nat), d' < D → ∀ {ρ m M}
      (hM' : LE_Interp.Witness ρ m M),
      P hM' ∧ hM'.RDeepChildren P ∧
        LE_Interp.Witness.SoundRDeepAt P Γ₀ hM' d')
    (H : HasTypeStratifiedS Γ M A core d)
    (hd : d ≤ D)
    (W : LE_Interp.Witness.FitsRDeep P Γ₀ Γ ρ)
    (Wfits : Valuation.Fits Γ₀ Γ ρ)
    (hM : LE_Interp.Witness ρ m M)
    (childrenP : hM.RDeepChildren P) :
    LE_Interp.Witness.TypedRDeep P ρ m M A := by
  induction H generalizing ρ m with
  | base _ ih => exact ih hd W Wfits hM childrenP
  | @sort' Γ l d =>
    let tm := TShape.sort (decide (l ≠ .zero))
    let ty := TShape.type
    let hterm : LE_Interp.Witness ρ tm (.sort l) := .sort .rfl
    let htype : LE_Interp.Witness ρ ty (.sort l.succ) :=
      .sort (by simpa [ty, TShape.type] using
        (TShape.LE.rfl : TShape.sort true ≤ TShape.sort true))
    exact ⟨tm, ty, hterm, htype, hM.toInterp.le_sort, .sort, .sort, .sort⟩
  | @bvar Γ i A u d hlookup hA ihA =>
    have hle := LE_Interp.bvar_iff.1 hM.toInterp
    exact (W.lookup laws hlookup).mono hle
  | @const c ci Γ ls u d hreg hlen hTy ihTy =>
    cases hM with
    | bot => exact .bot TShape.bot_eqv.1
    | @const _ _ ci' _ m' _ a' _ R hreg' hlen' hle hty hA hC hR =>
      cases hreg.symm.trans hreg'
      cases childrenP with
      | const cA pR cR =>
        let hconst : LE_Interp.Witness ρ m' (.const c ls) :=
          .const hreg hlen .rfl hty hA hC hR
        exact ⟨m', a', hconst, hA, hle, hty,
          .const cA pR cR, cA⟩
  | @app Γ A u n B v f a hA hCod hf ha hResult
      ihA ihCod ihf iha ihResult =>
    have hnD : n ≤ D := Nat.le_trans (Nat.le_succ n) hd
    exact LE_Interp.Witness.TypedRDeep.app
      (F := f) (A := A) (B := B) (X := a)
      laws.mono_l laws.closed
      (H1 := fun hF cF => ihf hnD W Wfits hF cF)
      (H2 := fun hB cB => (ihResult hnD W Wfits hB cB).toType)
      childrenP
  | @lam Γ A u n B v body hA hB hbody hPi
      ihA ihB ihbody ihPi =>
    have hnD : n ≤ D := Nat.le_trans (Nat.le_succ n) hd
    have hnLtD : n < D := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hd
    have fitType : ∀ {a}, LE_Interp ρ a A →
        ∃ a', a ≤ a' ∧ LE_Interp ρ a' A ∧ a'.HasType .type := by
      intro a ha
      let wa := ha.witness
      have qa := restart n hnLtD wa
      obtain ⟨a', hA', hle, hty, _⟩ :=
        (qa.2.2 hA W Wfits).toType
      exact ⟨a', hle, hA'.toInterp, hty⟩
    exact LE_Interp.Witness.TypedRDeep.lam laws
      (H2 := fun {a x} hDom cDom hx {e} hBody cBody =>
        ihbody hnD
          (W.push (ihA hnD W Wfits hDom cDom).toType hx)
          (Wfits.cons fitType hDom.toInterp hx) hBody cBody)
      childrenP
  | @forallE Γ A u n body v hA hbody ihA ihbody =>
    have hnD : n ≤ D := Nat.le_trans (Nat.le_succ n) hd
    have hnLtD : n < D := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hd
    have fitType : ∀ {a}, LE_Interp ρ a A →
        ∃ a', a ≤ a' ∧ LE_Interp ρ a' A ∧ a'.HasType .type := by
      intro a ha
      let wa := ha.witness
      have qa := restart n hnLtD wa
      obtain ⟨a', hA', hle, hty, _⟩ :=
        (qa.2.2 hA W Wfits).toType
      exact ⟨a', hle, hA'.toInterp, hty⟩
    exact LE_Interp.Witness.TypedRDeep.forallE laws
      (H1 := fun hDom cDom => ihA hnD W Wfits hDom cDom)
      (H2 := fun {a x} hDom cDom hx {e} hBody cBody =>
        ihbody hnD
          (W.push (ihA hnD W Wfits hDom cDom).toType hx)
          (Wfits.cons fitType hDom.toInterp hx) hBody cBody)
      childrenP
  | @defeq Γ A B u n e hEq hA hB he ihA ihB ihe =>
    have hnD : n ≤ D := Nat.le_trans (Nat.le_succ n) hd
    have hnLtD : n < D := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hd
    obtain ⟨tm, a, he', hA', hle, htyped, ce, cA⟩ :=
      ihe hnD W Wfits hM childrenP
    have hBpublic : LE_Interp ρ a B :=
      (LE_Interp.sound hEq Wfits).1.1 hA'.toInterp
    let hB0 := hBpublic.witness
    have qB := restart n hnLtD hB0
    obtain ⟨b, hB', hab, hbtype, cB⟩ :=
      (qB.2.2 hB W Wfits).toType
    exact ⟨tm, b, he', hB', hle,
      hbtype.mono_r hab htyped, ce, cB⟩

/-- Combine a consumer property with its retained tree and stratified semantic
typing. The caller proves the property at one witness from same-depth `R`-edge
results and strictly-smaller-depth restarts; the Nat-first witness recursor
supplies the well-founded fixed point. -/
theorem LE_Interp.Witness.recNatRDeepSound
    (laws : LE_Interp.Witness.RDeepChildren.Laws P)
    (buildP : ∀ (d : Nat) {ρ m M}
        (hM : LE_Interp.Witness ρ m M),
      hM.RDeepChildren (fun hM' =>
        P hM' ∧ hM'.RDeepChildren P ∧
          LE_Interp.Witness.SoundRDeepAt P Γ₀ hM' d) →
      (∀ (d' : Nat), d' < d → ∀ {ρ m M}
        (hM' : LE_Interp.Witness ρ m M),
        P hM' ∧ hM'.RDeepChildren P ∧
          LE_Interp.Witness.SoundRDeepAt P Γ₀ hM' d') →
      P hM)
    {ρ m M} (hM : LE_Interp.Witness ρ m M) : ∀ d,
      P hM ∧ hM.RDeepChildren P ∧
        LE_Interp.Witness.SoundRDeepAt P Γ₀ hM d := by
  let Q : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Nat → Prop :=
    fun hM d => P hM ∧ hM.RDeepChildren P ∧
      LE_Interp.Witness.SoundRDeepAt P Γ₀ hM d
  change ∀ d, Q hM d
  apply hM.recNatRDeep (Q := Q)
  intro d ρ m M hM children lower
  dsimp only [Q] at children lower ⊢
  have childrenP : hM.RDeepChildren P :=
    children.map (fun _ h => h.1)
  refine ⟨buildP d hM children lower, childrenP, ?_⟩
  intro Γ A core H W Wfits
  exact LE_Interp.Witness.soundRDeepRestart laws lower H (Nat.le_refl d)
    W Wfits hM childrenP


/-- Separate the exact-edge consumer from the predicate retained by semantic
typing. -/
theorem LE_Interp.Witness.recNatRDeepConsumer
    {C T : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop}
    (laws : LE_Interp.Witness.RDeepChildren.Laws T)
    (toTree : ∀ {ρ m M} (hM : LE_Interp.Witness ρ m M), C hM → T hM)
    (buildC : ∀ (d : Nat) {ρ m M}
        (hM : LE_Interp.Witness ρ m M),
      hM.RDeepChildren (fun hM' =>
        C hM' ∧ hM'.RDeepChildren T ∧
          LE_Interp.Witness.SoundRDeepAt T Γ₀ hM' d) →
      (∀ (d' : Nat), d' < d → ∀ {ρ m M}
        (hM' : LE_Interp.Witness ρ m M),
        C hM' ∧ hM'.RDeepChildren T ∧
          LE_Interp.Witness.SoundRDeepAt T Γ₀ hM' d') →
      C hM)
    {ρ m M} (hM : LE_Interp.Witness ρ m M) : ∀ d,
      C hM ∧ hM.RDeepChildren T ∧
        LE_Interp.Witness.SoundRDeepAt T Γ₀ hM d := by
  let Q : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Nat → Prop :=
    fun hM d => C hM ∧ hM.RDeepChildren T ∧
      LE_Interp.Witness.SoundRDeepAt T Γ₀ hM d
  change ∀ d, Q hM d
  apply hM.recNatRDeep (Q := Q)
  intro d ρ m M hM children lower
  dsimp only [Q] at children lower ⊢
  have childrenT : hM.RDeepChildren T :=
    children.map (fun h q => toTree h q.1)
  have restartT : ∀ (d' : Nat), d' < d → ∀ {ρ m M}
      (hM' : LE_Interp.Witness ρ m M),
      T hM' ∧ hM'.RDeepChildren T ∧
        LE_Interp.Witness.SoundRDeepAt T Γ₀ hM' d' := by
    intro d' hd' ρ m M hM'
    have q := lower d' hd' hM'
    exact ⟨toTree hM' q.1, q.2⟩
  refine ⟨buildC d hM children lower, childrenT, ?_⟩
  intro Γ A core H W Wfits
  exact hM.soundRDeepRestart laws restartT H (Nat.le_refl d)
    W Wfits childrenT

/-- Depth-indexed form of `recNatRDeepConsumer`. -/
theorem LE_Interp.Witness.recNatRDeepConsumerAt
    {C : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Nat → Prop}
    {T : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Prop}
    (laws : LE_Interp.Witness.RDeepChildren.Laws T)
    (toTree : ∀ (d : Nat) {ρ m M}
      (hM : LE_Interp.Witness ρ m M), C hM d → T hM)
    (buildC : ∀ (d : Nat) {ρ m M}
        (hM : LE_Interp.Witness ρ m M),
      hM.RDeepChildren (fun hM' =>
        C hM' d ∧ hM'.RDeepChildren T ∧
          LE_Interp.Witness.SoundRDeepAt T Γ₀ hM' d) →
      (∀ (d' : Nat), d' < d → ∀ {ρ m M}
        (hM' : LE_Interp.Witness ρ m M),
        C hM' d' ∧ hM'.RDeepChildren T ∧
          LE_Interp.Witness.SoundRDeepAt T Γ₀ hM' d') →
      C hM d)
    {ρ m M} (hM : LE_Interp.Witness ρ m M) : ∀ d,
      C hM d ∧ hM.RDeepChildren T ∧
        LE_Interp.Witness.SoundRDeepAt T Γ₀ hM d := by
  let Q : ∀ {ρ m M}, LE_Interp.Witness ρ m M → Nat → Prop :=
    fun hM d => C hM d ∧ hM.RDeepChildren T ∧
      LE_Interp.Witness.SoundRDeepAt T Γ₀ hM d
  change ∀ d, Q hM d
  apply hM.recNatRDeep (Q := Q)
  intro d ρ m M hM children lower
  dsimp only [Q] at children lower ⊢
  have childrenT : hM.RDeepChildren T :=
    children.map (fun h q => toTree d h q.1)
  have restartT : ∀ (d' : Nat), d' < d → ∀ {ρ m M}
      (hM' : LE_Interp.Witness ρ m M),
      T hM' ∧ hM'.RDeepChildren T ∧
        LE_Interp.Witness.SoundRDeepAt T Γ₀ hM' d' := by
    intro d' hd' ρ m M hM'
    have q := lower d' hd' hM'
    exact ⟨toTree d' hM' q.1, q.2⟩
  refine ⟨buildC d hM children lower, childrenT, ?_⟩
  intro Γ A core H W Wfits
  exact hM.soundRDeepRestart laws restartT H (Nat.le_refl d)
    W Wfits childrenT

structure LogRelBase (Γ : List SExpr) (n : Nat) where
  /-- Term validity: `M ≡ N : A` at element-shape `m` and type-shape `a`. -/
  DefEq (M N A : SExpr) (m a : WShape n) : Prop
  /-- Type validity: `A ≡ B` are valid types at type-shape `a`. -/
  TyDefEq (A B : SExpr) (a : WShape n) : Prop

structure LogRel (Γ : List SExpr) (n : Nat) extends LogRelBase Γ n where
  sort_iff : DefEq M N A (.sort r) (.sort r') ↔ ∃ u, Γ ⊢ M ⤳* .sort u ∧ Γ ⊢ N ⤳* .sort u
  sort_iff_ty : TyDefEq M N (.sort r) ↔ ∃ u, Γ ⊢ M ⤳* .sort u ∧ Γ ⊢ N ⤳* .sort u
  bot : a.HasType .type → DefEq M N A .bot a
  toType : DefEq M N A m (.sort r) → TyDefEq M N m
  left : DefEq M N A m a → DefEq M M A m a
  left_ty : TyDefEq M N m → TyDefEq M M m
  symm : DefEq M N A m a → DefEq N M A m a
  symm_ty : TyDefEq M N m → TyDefEq N M m
  trans : DefEq M₁ M₂ A m a → DefEq M₂ M₃ A m a → DefEq M₁ M₃ A m a
  trans' : DefEq A₁ A₂ (.sort u) a s → DefEq A₂ A₃ (.sort v) a (.sort r) → DefEq A₁ A₃ (.sort u) a s
  trans_ty : TyDefEq M₁ M₂ m → TyDefEq M₂ M₃ m → TyDefEq M₁ M₃ m
  conv : TyDefEq A B a → DefEq M N A m a → DefEq M N B m a
  mono_r_2 : a ≤ a' → m.HasType a → a'.HasType .type → DefEq M N A m a' → DefEq M N A m a
  mono_r_2_ty : a ≤ a' → a.HasType .type → a'.HasType .type → TyDefEq A B a' → TyDefEq A B a
  mono_r_1 : a ≤ a' → m.HasType a → m.HasType a' → TyDefEq A A a' → DefEq M N A m a → DefEq M N A m a'
  mono_l : m ≤ m' → m.HasType a → m'.HasType a → DefEq M N A m' a → DefEq M N A m a
  join_ty : m₁.Compat m₂ → m₁.HasType .type → m₂.HasType .type →
    TyDefEq A B m₁ → TyDefEq A B m₂ → TyDefEq A B (m₁.join m₂)
  whr : Γ ⊢ M ⤳* M' → Γ ⊢ N ⤳* N' → (DefEq M N A m a ↔ DefEq M' N' A m a)
  whr_ty : Γ ⊢ A ⤳* A' → Γ ⊢ B ⤳* B' → (TyDefEq A B m ↔ TyDefEq A' B' m)

/-- The three synchronized edges produced by evaluating two related heads
at two related arguments.  The horizontal edges are the endpoint
self-congruences; the diagonal is the heterogeneous result ultimately
consumed by `LamDefEq`.  Packaging them together is important at semantic
transport boundaries: retyping the diagonal may require the two endpoint
witnesses at the very same observation. -/
structure LogRel.DefEqRect (R : LogRel Γ n)
    (M₁ M₂ N₁ N₂ A : SExpr) (m a : WShape n) : Prop where
  left : R.DefEq M₁ M₂ A m a
  right : R.DefEq N₁ N₂ A m a
  cross : R.DefEq M₁ N₂ A m a

/-- A single logical-relation edge supplies the degenerate rectangle used
when both evaluated heads coincide. -/
theorem LogRel.DefEqRect.diagonal
    (H : R.DefEq M₁ M₂ A m a) :
    LogRel.DefEqRect R M₁ M₂ M₁ M₂ A m a :=
  ⟨H, H, H⟩

/-- Compose two synchronized rectangles that share their middle endpoints. -/
theorem LogRel.DefEqRect.trans
    (H₁ : LogRel.DefEqRect R M₁ M₂ N₁ N₂ A m a)
    (H₂ : LogRel.DefEqRect R M₂ M₃ N₂ N₃ A m a) :
    LogRel.DefEqRect R M₁ M₃ N₁ N₃ A m a :=
  ⟨R.trans H₁.left H₂.left,
    R.trans H₁.right H₂.right,
    R.trans H₁.cross H₂.right⟩

/-- Convert the common declared type of all three rectangle edges. -/
theorem LogRel.DefEqRect.conv
    (hAB : R.TyDefEq A B a)
    (H : LogRel.DefEqRect R M₁ M₂ N₁ N₂ A m a) :
    LogRel.DefEqRect R M₁ M₂ N₁ N₂ B m a :=
  ⟨R.conv hAB H.left, R.conv hAB H.right, R.conv hAB H.cross⟩

/-- Lower the common element observation of a rectangle. -/
theorem LogRel.DefEqRect.mono_l
    (hle : m ≤ m') (hm : m.HasType a) (hm' : m'.HasType a)
    (H : LogRel.DefEqRect R M₁ M₂ N₁ N₂ A m' a) :
    LogRel.DefEqRect R M₁ M₂ N₁ N₂ A m a :=
  ⟨R.mono_l hle hm hm' H.left,
    R.mono_l hle hm hm' H.right,
    R.mono_l hle hm hm' H.cross⟩

/-- Raise the common type observation of a rectangle. -/
theorem LogRel.DefEqRect.mono_r_1
    (hle : a ≤ a') (hma : m.HasType a) (hma' : m.HasType a')
    (hA : R.TyDefEq A A a')
    (H : LogRel.DefEqRect R M₁ M₂ N₁ N₂ A m a) :
    LogRel.DefEqRect R M₁ M₂ N₁ N₂ A m a' :=
  ⟨R.mono_r_1 hle hma hma' hA H.left,
    R.mono_r_1 hle hma hma' hA H.right,
    R.mono_r_1 hle hma hma' hA H.cross⟩

/-- Lower the common type observation of a rectangle. -/
theorem LogRel.DefEqRect.mono_r_2
    (hle : a ≤ a') (hma : m.HasType a) (ha' : a'.HasType .type)
    (H : LogRel.DefEqRect R M₁ M₂ N₁ N₂ A m a') :
    LogRel.DefEqRect R M₁ M₂ N₁ N₂ A m a :=
  ⟨R.mono_r_2 hle hma ha' H.left,
    R.mono_r_2 hle hma ha' H.right,
    R.mono_r_2 hle hma ha' H.cross⟩

/-- Weak-head normalize all four endpoints of a rectangle in lockstep. -/
theorem LogRel.DefEqRect.whr
    {R : LogRel Γ n}
    (hM₁ : WHRedS Γ M₁ M₁') (hM₂ : WHRedS Γ M₂ M₂')
    (hN₁ : WHRedS Γ N₁ N₁') (hN₂ : WHRedS Γ N₂ N₂') :
    LogRel.DefEqRect R M₁ M₂ N₁ N₂ A m a ↔
      LogRel.DefEqRect R M₁' M₂' N₁' N₂' A m a := by
  constructor
  · intro H
    exact ⟨(R.whr hM₁ hM₂).1 H.left,
      (R.whr hN₁ hN₂).1 H.right,
      (R.whr hM₁ hN₂).1 H.cross⟩
  · intro H
    exact ⟨(R.whr hM₁ hM₂).2 H.left,
      (R.whr hN₁ hN₂).2 H.right,
      (R.whr hM₁ hN₂).2 H.cross⟩

/-- Transport a term relation from one valid type shape to another through a
semantic equality at their join.  This packages the raise/convert/lower
pattern used by successor-level lambda retyping. -/
theorem LogRel.DefEq.retype_join {R : LogRel Γ n}
    (compat : a.Compat b)
    (hpA : p.HasType a) (hpB : p.HasType b)
    (hTy : R.TyDefEq A B (a.join b))
    (hxy : R.DefEq x y B p b) :
    R.DefEq x y A p a := by
  have hjoin := WShape.Join.mk compat
  have htypeJoin := WShape.HasType.join compat hpA.isType hpB.isType
  have hpJoin := WShape.HasType.mono_r hjoin.le.1 htypeJoin hpA
  have hBB := R.left_ty (R.symm_ty hTy)
  have hxyJoin := R.mono_r_1 hjoin.le.2 hpB hpJoin hBB hxy
  have hxyA := R.conv (R.symm_ty hTy) hxyJoin
  exact R.mono_r_2 hjoin.le.1 hpA htypeJoin hxyA

theorem LogRelBase.TyDefEq.sort {R : LogRel Γ n} : R.TyDefEq (.sort u) (.sort u) (.sort r) :=
  R.toType (A := default) (r := default) (R.sort_iff.2 ⟨_, .rfl, .rfl⟩)

/-! #### Concrete definitions at level 0 -/

def LR0.TyDefEq (Γ : List SExpr) (M N : SExpr) : WShape 0 → Prop
  | ⟨.bot, _⟩ => True
  | ⟨.sort _, _⟩ => ∃ u, Γ ⊢ M ⤳* .sort u ∧ Γ ⊢ N ⤳* .sort u

def LR0.DefEq (Γ : List SExpr) (M N : SExpr) (m a : WShape 0) : Prop :=
  match a.1 with
  | .bot => True
  | .sort _ => LR0.TyDefEq Γ M N m

def LR0 : LogRel Γ 0 where
  DefEq M N _ := LR0.DefEq Γ M N
  TyDefEq := LR0.TyDefEq Γ
  sort_iff := by simp [LR0.DefEq, LR0.TyDefEq, WShape.sort]
  sort_iff_ty := by simp [LR0.TyDefEq, WShape.sort]
  bot {_ _ _ _} _ := by simp only [LR0.DefEq, LR0.TyDefEq, WShape.bot]; split <;> trivial
  toType := id
  left {M N A m a} := by
    dsimp [LR0.DefEq]; split <;> [trivial; skip]
    dsimp [LR0.TyDefEq]; split <;> [trivial; skip]
    intro ⟨u, hM, _⟩; exact ⟨u, hM, hM⟩
  left_ty {M N m} := by
    dsimp [LR0.TyDefEq]; split <;> [trivial; skip]
    intro ⟨u, hM, _⟩; exact ⟨u, hM, hM⟩
  symm {M N A m a} := by
    dsimp [LR0.DefEq]; split <;> [trivial; skip]
    dsimp [LR0.TyDefEq]; split <;> [trivial; skip]
    intro ⟨u, hM, hN⟩; exact ⟨u, hN, hM⟩
  symm_ty {M N m} := by
    dsimp [LR0.TyDefEq]; split <;> [trivial; skip]
    intro ⟨u, hM, hN⟩; exact ⟨u, hN, hM⟩
  trans {M₁ M₂ A m a M₃} := by
    dsimp [LR0.DefEq]; split <;> [trivial; skip]
    dsimp [LR0.TyDefEq]; split <;> [trivial; skip]
    intro ⟨u, h1, h2⟩ ⟨u', h2', h3⟩
    cases h2.determ .sort h2' .sort; exact ⟨u, h1, h3⟩
  trans' {A₁ A₂ u a s A₃ v r} := by
    dsimp [LR0.DefEq]; split <;> [(intros; trivial); skip]
    dsimp [LR0.TyDefEq]; split <;> [(intros; trivial); skip]
    intro ⟨u, h1, h2⟩ ⟨u', h2', h3⟩
    cases h2.determ .sort h2' .sort; exact ⟨u, h1, h3⟩
  trans_ty {M₁ M₂ m M₃} := by
    dsimp [LR0.TyDefEq]; split <;> [trivial; skip]
    intro ⟨u, h1, h2⟩ ⟨u', h2', h3⟩
    cases h2.determ .sort h2' .sort; exact ⟨u, h1, h3⟩
  conv _ := id
  mono_r_2 {a a' _ _ _ _} le _ _ := by
    obtain ⟨⟨⟩, _⟩ := a <;> obtain ⟨⟨⟩, _⟩ := a' <;> simp [LR0.DefEq]; cases le
  mono_r_2_ty {a a' _ _} le _ _ := by
    obtain ⟨⟨⟩, _⟩ := a <;> obtain ⟨⟨⟩, _⟩ := a' <;> simp [LR0.TyDefEq]; cases le
  mono_r_1 {a a' _ _ _ b} le h1 _ h2 := by
    obtain ⟨⟨⟩, _⟩ := a <;> obtain ⟨⟨⟩, _⟩ := a' <;>
      (try exact id) <;> [cases h1.bot_r; cases le]; exact id
  mono_l {m m' M N A a} le _ _ := by
    simp only [LR0.DefEq]; split <;> [trivial; skip]
    obtain ⟨⟨⟩, _⟩ := m <;> obtain ⟨⟨⟩, _⟩ := m' <;>
      (try exact id) <;> [exact fun _ => trivial; cases le]
  join_ty {A B m₁ m₂} hC hm₁ hm₂ := by
    obtain ⟨⟨⟩, _⟩ := m₁ <;> obtain ⟨⟨⟩, _⟩ := m₂ <;>
      simp [LR0.TyDefEq, WShape.join, Shape.join, dif_pos hC]
    simp [WShape.Compat, Shape.Compat] at hC; subst hC; simp
    intro u h1 h2 _ h3 h4; exact ⟨u, h1, h2⟩
  whr {M M' N N' A m a} hM hN := by
    dsimp [LR0.DefEq]; split <;> [exact .rfl; skip]
    dsimp [LR0.TyDefEq]; split <;> [exact .rfl; skip]
    constructor <;> intro ⟨u, r1, r2⟩
    · exact ⟨u, hM.determ_l r1 .sort, hN.determ_l r2 .sort⟩
    · exact ⟨u, .trans hM r1, .trans hN r2⟩
  whr_ty {A A' B B' m} hA hB := by
    dsimp [LR0.TyDefEq]; split <;> [exact .rfl; skip]
    constructor <;> intro ⟨u, r1, r2⟩
    · exact ⟨u, hA.determ_l r1 .sort, hB.determ_l r2 .sort⟩
    · exact ⟨u, .trans hA r1, .trans hB r2⟩

/-! #### Concrete definitions at level n+1 -/

/-! `TypeDefEqPath` and its conversion API (`single`, `trans`, `leftType`,
`rightType`, `left`, `right`, `symm`, `defeqDF`, `defeqDF_l`,
`defeqDF_l_path`, `subst`) moved to `Lean4Lean/Experimental/SExpr.lean` on
2026-08-15, beside `IsDefEq.defeqDF_l` and `IsDefEq.subst`, which are its only
inputs.  Nothing about it was logical-relation-flavoured, and the relocation
is what lets `IsDefEqStrong.app_inv'` / `.lam_inv'` / `.forallE_inv_path`
state their conclusions there.  `TypeDefEqPath.collapse` (below) stays here:
its extra input `LogRel.RawTypeUniq` is declared here. -/

/-- The four synchronized facts retained after applying a Pi codomain to
related arguments.  The raw equalities are the evidence needed by dependent
application/spine construction; the semantic equalities are what the
logical relation consumes. -/
structure LRS.PiInstDefEq (IH : LogRel Γ n) (F₁ F₂ a b : SExpr)
    (p : WShape n) : Prop where
  leftTy : IH.TyDefEq (F₁.inst a) (F₁.inst b) p
  rightTy : IH.TyDefEq (F₂.inst a) (F₂.inst b) p
  leftDefEq : ∃ u, Γ ⊢ F₁.inst a ≡ F₁.inst b : .sort u
  rightDefEq : ∃ u, Γ ⊢ F₂.inst a ≡ F₂.inst b : .sort u

/-- Pi edge validity (merged `PiEdgeDefEq` / `PiEdgeEq2`).
For each argument `a ≡ b : A₁`, the substituted codomains are valid and
raw-equal types.  For each argument `a : A₁`, the codomains `A₂[a]` and
`B₂[a]` are equal types. -/
def LRS.PiDefEq (IH : LogRel Γ n)
    (B F₁ F₂ : SExpr) (b : WShape n) (f : WShapeFun n) : Prop :=
  (∀ {{a b' p}}, p.HasType b → Γ ⊢ a ≡ b' : B → IH.DefEq a b' B p b →
    LRS.PiInstDefEq IH F₁ F₂ a b' (f.app p)) ∧
  ∀ {{a p}}, p.HasType b → Γ ⊢ a : B → IH.DefEq a a B p b →
    IH.TyDefEq (F₁.inst a) (F₂.inst a) (f.app p)

theorem LRS.PiDefEq.left {IH : LogRel Γ n} :
    LRS.PiDefEq IH B F₁ F₂ b f → LRS.PiDefEq IH B F₁ F₁ b f := fun ⟨h1, _⟩ =>
  ⟨fun _ _ _ hp ha a1 =>
      let h := h1 hp ha a1
      ⟨h.leftTy, h.leftTy, h.leftDefEq, h.leftDefEq⟩,
    fun _ _ hp ha a1 => (h1 hp ha a1).leftTy⟩

def LRS.ValTyPi2 (IH : LogRel Γ n) (M₁ M₂ : SExpr) (b : WShape n) (f : WShapeFun n) : Prop :=
  ∃ B₁ F₁ B₂ F₂ u v,
    Γ ⊢ M₁ ⤳* .forallE B₁ F₁ ∧ Γ ⊢ M₂ ⤳* .forallE B₂ F₂ ∧
    TypeDefEqPath Γ B₁ B₂ u ∧ TypeDefEqPath (B₁ :: Γ) F₁ F₂ v ∧
    IH.TyDefEq B₁ B₂ b ∧
    LRS.PiDefEq IH B₁ F₁ F₂ b f

def LRS.LamDefEq (IH : LogRel Γ n)
    (M N A₁ A₂ : SExpr) (m : WShapeFun n) (a₁ : WShape n) (a₂ : WShapeFun n) : Prop :=
  (∀ {{a b p}}, WShape.HasType p a₁ → Γ ⊢ a ≡ b : A₁ → IH.DefEq a b A₁ p a₁ →
    IH.DefEq (M.app a) (M.app b) (A₂.inst a) (m.app p) (a₂.app p) ∧
    IH.DefEq (N.app a) (N.app b) (A₂.inst a) (m.app p) (a₂.app p)) ∧
  (∀ {{a p}}, WShape.HasType p a₁ → Γ ⊢ a : A₁ → IH.DefEq a a A₁ p a₁ →
    IH.DefEq (M.app a) (N.app a) (A₂.inst a) (m.app p) (a₂.app p))

/-- Monotonicity of `LamDefEq` in the type-shape: increase. -/
theorem LRS.LamDefEq.mono_r_1 {IH : LogRel Γ n}
    (le₁ : a₁ ≤ a₁') (le₂ : a₂ ≤ a₂') (hm : WShape.HasTypeLam m a₁ a₂)
    (hm' : WShape.HasTypeLam m a₁' a₂') (piEV : LRS.PiDefEq IH A₁ A₂ A₂ a₁' a₂') :
    LRS.LamDefEq IH M N A₁ A₂ m a₁ a₂ → LRS.LamDefEq IH M N A₁ A₂ m a₁' a₂' := by
  have hm_d := WShape.HasDom.iff.1 hm.2.1
  have hm_f := WShape.HasTypeLam.iff.1 hm |>.2.2
  intro ⟨pav, pae⟩
  refine ⟨fun _ _ x hx ha a1 => ?_, fun _ x hx ha a1 => ?_⟩
  all_goals
    have ⟨x', le', hax, h1⟩ := hm_d x
    have hax' := hx.isType.mono_r le₁ hax
    have a1_x := IH.mono_l le' hax' hx a1
    have a1_down := IH.mono_r_2 le₁ hax hx.isType a1_x
    have hg_x := hm_f x' hax
    have hg_p := hg_x.mono_l (WShapeFun.app_mono_r le') h1
    have le_cod := (WShapeFun.app_mono_r le').trans (WShapeFun.app_mono_l le₂ _)
    have ht_cod := (WShape.HasTypePi.iff.1 hm'.1).2 x hx
    have hm_target := ht_cod.mono_r le_cod hg_p
  · have ⟨p1, p2⟩ := pav hax ha a1_down
    have tyA₂ := (piEV.1 hx ha.hasType.1 (IH.left a1)).leftTy
    exact ⟨IH.mono_r_1 le_cod hg_p hm_target tyA₂ (IH.mono_l h1 hg_p hg_x p1),
           IH.mono_r_1 le_cod hg_p hm_target tyA₂ (IH.mono_l h1 hg_p hg_x p2)⟩
  · have q := pae hax ha a1_down
    have tyA₂ := piEV.2 hx ha a1
    exact IH.mono_r_1 le_cod hg_p hm_target tyA₂ (IH.mono_l h1 hg_p hg_x q)

/-! #### Observable inductive heads -/

/-- A syntactic type realizes an inductive-type head when it weak-head reduces
to a fully applied constant registered as an `indTy`. -/
def LRS.IndTyHead (Γ : List SExpr) (A : SExpr) : Prop :=
  ∃ (c : Name) (ls : List SLevel) (args : List SExpr),
    Params.classify c = some (.indTy args.length) ∧
    WHRedS Γ A (args.foldr (fun a f => f.app a) (.const c ls))

theorem LRS.IndTyHead.whr (hA : WHRedS Γ A A') :
    LRS.IndTyHead Γ A ↔ LRS.IndTyHead Γ A' := by
  constructor
  · rintro ⟨c, ls, args, hcl, rA⟩
    exact ⟨c, ls, args, hcl, hA.determ_l rA (.indTy_spine hcl)⟩
  · rintro ⟨c, ls, args, hcl, rA⟩
    exact ⟨c, ls, args, hcl, .trans hA rA⟩

theorem LRS.IndTyHead.not_sort : ¬LRS.IndTyHead Γ (.sort u) := by
  rintro ⟨c, ls, args, _, rA⟩
  have heq := WHNF.sort.whRedS rA
  have hh := congrArg constHead? heq
  simp only [constHead?, constHead?_spine] at hh
  cases hh

/-- Observable constructor-head evidence for a semantic element shape.  At
bottom there is no observation; at a non-bottom constructor shape both the
registered constructor name and the arity of its syntactic application spine
must agree with the semantic head. -/
def LRS.CtorHead (Γ : List SExpr) (M : SExpr) {n : Nat} (m : WShape (n+1)) : Prop :=
  match m.1 with
  | .bot => True
  | .ctor c l =>
    ∃ (ls : List SLevel) (args : List SExpr),
      Params.classify c = some (.ctor args.length) ∧ args.length = l.length ∧
      WHRedS Γ M (args.foldr (fun a f => f.app a) (.const c ls))
  | _ => False

@[simp] theorem LRS.CtorHead.bot : LRS.CtorHead Γ M (WShape.bot : WShape (n+1)) := by
  trivial

@[simp] theorem LRS.CtorHead.ctor {h : IsStruct c → WShape.ListNonZero l} :
    LRS.CtorHead Γ M (WShape.ctor c l h) ↔
      ∃ (ls : List SLevel) (args : List SExpr),
        Params.classify c = some (.ctor args.length) ∧ args.length = l.length ∧
        WHRedS Γ M (args.foldr (fun a f => f.app a) (.const c ls)) := by
  simp only [LRS.CtorHead, WShape.ctor, List.length_map]

theorem LRS.CtorHead.whr (hM : WHRedS Γ M M') :
    LRS.CtorHead Γ M m ↔ LRS.CtorHead Γ M' m := by
  cases m using WShape.casesOn' with
  | ctor c l h =>
    simp only [LRS.CtorHead.ctor]
    constructor
    · rintro ⟨ls, args, hcl, hlen, rM⟩
      exact ⟨ls, args, hcl, hlen, hM.determ_l rM (.ctor_spine hcl)⟩
    · rintro ⟨ls, args, hcl, hlen, rM⟩
      exact ⟨ls, args, hcl, hlen, .trans hM rM⟩
  | _ => rfl

theorem LRS.CtorHead.mono_l (le : m ≤ m') (hm : m.HasType WShape.indTy) :
    LRS.CtorHead Γ M m' → LRS.CtorHead Γ M m := by
  cases m using WShape.casesOn' with
  | bot => intro; trivial
  | ctor c l h =>
    rw [WShape.ctor_le] at le
    obtain ⟨l', h', rfl, hll⟩ := le
    simp only [LRS.CtorHead.ctor]
    rintro ⟨ls, args, hcl, hlen, rM⟩
    exact ⟨ls, args, hcl, hlen.trans hll.length_eq.symm, rM⟩
  | _ => cases hm

theorem LRS.CtorHead.lift {m : WShape (n+1)} (le : n ≤ n') :
    LRS.CtorHead Γ M (m.lift (n'+1)) ↔ LRS.CtorHead Γ M m := by
  cases m using WShape.casesOn' with
  | bot => simp only [WShape.lift_bot, LRS.CtorHead.bot]
  | sort r =>
    change LRS.CtorHead Γ M ((WShape.sort r : WShape (n+1)).lift (n'+1)) ↔
      LRS.CtorHead Γ M (WShape.sort r)
    rw [WShape.lift_sort]
    rfl
  | forallE b f => rw [WShape.lift_forallE le]; simp [LRS.CtorHead, WShape.forallE]
  | lam f h => rw [WShape.lift_lam le]; simp [LRS.CtorHead, WShape.lam]
  | ctor c l h =>
    rw [WShape.lift_ctor le]
    simp only [LRS.CtorHead.ctor, List.length_map]
  | indTy =>
    change LRS.CtorHead Γ M ((WShape.indTy : WShape (n+1)).lift (n'+1)) ↔
      LRS.CtorHead Γ M WShape.indTy
    rw [WShape.lift_indTy]
    rfl

/-- A constructor application spine whose raw dependent typing and semantic
field relation are one certificate.  Arguments and shapes are stored in
newest-first order, matching `CtorArgsDefEq`; `cons` appends the displayed
argument to the actual left-to-right application spine.  The final equality
records the dependent codomain transport from the right argument back to the
left-oriented result, which makes reflexive and symmetric observations
structural rather than dependent on type uniqueness. -/
inductive LRS.CtorSpineDefEq (IH : LogRel Γ n) (Head : SExpr) :
    List SExpr → List SExpr → List (WShape n) → SExpr → Prop where
  | nil : CtorSpineDefEq IH Head [] [] [] Head
  | cons
      (hrest : CtorSpineDefEq IH Head xs ys ps A)
      (hPi : IsDefEq Γ A (.forallE D C) (.sort u))
      (hp : p.HasType a)
      (hty : IH.TyDefEq D D a)
      (hxy : IsDefEq Γ x y D)
      (hv : IH.DefEq x y D p a)
      (hresult : IsDefEq Γ (C.inst y) (C.inst x) (.sort v)) :
      CtorSpineDefEq IH Head (x :: xs) (y :: ys) (p :: ps) (C.inst x)
  | ret
      (hrest : CtorSpineDefEq IH Head xs ys ps A)
      (hresult : IsDefEq Γ A A' (.sort u)) :
      CtorSpineDefEq IH Head xs ys ps A'

/-- Relational evidence for the fields of one constructor application spine.
Besides the lower-level logical-relation witness, each field retains the raw
typed equality used to build a concrete proof-carrying pattern action. -/
inductive LRS.CtorArgsDefEq (IH : LogRel Γ n) :
    List SExpr → List SExpr → List (WShape n) → Prop where
  | nil : CtorArgsDefEq IH [] [] []
  | cons (hp : p.HasType a) (hty : IH.TyDefEq A A a)
      (hxy : Γ ⊢ x ≡ y : A)
      (hv : IH.DefEq x y A p a) (hrest : CtorArgsDefEq IH xs ys ps) :
      CtorArgsDefEq IH (x :: xs) (y :: ys) (p :: ps)

/-- The level-indexed uniqueness fragment needed when two exact constructor
observations share a middle field.  It does not assert unrestricted
faithfulness of the logical relation: both typings and both semantic
validity witnesses for the *same term and shape* are supplied.  The result
aligns the raw field types and their semantic type interpretations, exactly
the two conversions required by dependent constructor-spine composition.

In the joint L4L-16 proof this package is not derivable from same-level
adequacy alone: bottom shapes erase weak typing evidence, and weak judgments
require a well-formed target context.  The sound tower first establishes
adequacy at positive level one, uses its sort/Pi observations and context
validity to obtain the level-zero package, and thereafter constructs
successor packages in the offset order recorded by `LR.JointBuilder`.
Constructor composition in `LRS` consumes the predecessor package. -/
structure LogRel.LimitedUniq (IH : LogRel Γ n) : Prop where
  align : ∀ {x A B : SExpr} {p a b : WShape n},
    p.HasType a → p.HasType b →
    IsDefEq Γ x x A → IsDefEq Γ x x B →
    IH.TyDefEq A A a → IH.TyDefEq B B b →
    IH.DefEq x x A p a → IH.DefEq x x B p b →
    ∃ u, IsDefEq Γ A B (.sort u) ∧
      ∀ {y : SExpr}, IsDefEq Γ x y B → IH.DefEq x y B p b →
        IH.DefEq x y A p a

/-- Retype all three edges of a result rectangle in lockstep.

The two target self-relations are explicit because `LimitedUniq` is
term-indexed: the left and right heads may justify the target observation by
different typing derivations.  The diagonal deliberately reuses the left
head's transport, which preserves the left-oriented dependent result type
used by application congruence. -/
theorem LogRel.DefEqRect.retype_of_limitedUniq
    {R : LogRel Γ n} (uniq : LogRel.LimitedUniq R)
    {M₁ M₂ N₁ N₂ A B : SExpr} {p a b : WShape n}
    (hpA : p.HasType a) (hpB : p.HasType b)
    (hM₁A : IsDefEq Γ M₁ M₁ A)
    (hN₁A : IsDefEq Γ N₁ N₁ A)
    (hA : R.TyDefEq A A a) (hB : R.TyDefEq B B b)
    (hM₁rel : R.DefEq M₁ M₁ A p a)
    (hN₁rel : R.DefEq N₁ N₁ A p a)
    (hleft : IsDefEq Γ M₁ M₂ B)
    (hright : IsDefEq Γ N₁ N₂ B)
    (hcross : IsDefEq Γ M₁ N₂ B)
    (H : LogRel.DefEqRect R M₁ M₂ N₁ N₂ B p b) :
    LogRel.DefEqRect R M₁ M₂ N₁ N₂ A p a := by
  obtain ⟨_, _, retypeLeft⟩ := uniq.align hpA hpB
    hM₁A hleft.hasType.1 hA hB hM₁rel (R.left H.left)
  obtain ⟨_, _, retypeRight⟩ := uniq.align hpA hpB
    hN₁A hright.hasType.1 hA hB hN₁rel (R.left H.right)
  exact ⟨retypeLeft hleft H.left,
    retypeRight hright H.right,
    retypeLeft hcross H.cross⟩

/-- Raw weak type uniqueness in one target context.  This is separated from
`LimitedUniq`: the latter additionally transports semantic witnesses between
the two type shapes, while this proposition is exactly the former L4L-17
co-deliverable derived from the level-zero stratified-inversion bootstrap. -/
def LogRel.RawTypeUniq (Γ : List SExpr) : Prop :=
  ∀ {x A B : SExpr}, IsDefEq Γ x x A → IsDefEq Γ x x B →
    ∃ u, IsDefEq Γ A B (.sort u)

/-- Raw type uniqueness uniformly over well-formed target contexts.  Binder
inversion needs this contextual form: after aligning a Pi domain it consumes
the same theorem once more in the extended context. -/
def LogRel.ContextualRawTypeUniq : Prop :=
  ∀ {Γ : List SExpr}, Ctx.WF Γ → LogRel.RawTypeUniq Γ

/-- Collapse a heterogeneous type-equality path once ordinary type
uniqueness is available in its context.  At a concatenation point,
uniqueness aligns the two universe assignments for the shared type before
the raw equalities are composed. -/
theorem TypeDefEqPath.collapse
    (uniq : LogRel.RawTypeUniq Γ)
    (H : TypeDefEqPath Γ A B u) : IsDefEq Γ A B (.sort u) := by
  induction H with
  | single h => exact h
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨_, huv⟩ := uniq ih₁.hasType.2 ih₂.hasType.1
    exact ih₁.trans (huv.symm.defeqDF ih₂)

/-- At the bottom stratum, limited semantic uniqueness has no additional
content beyond raw weak type uniqueness.  A non-bottom element shape is a
sort and therefore fixes its type shape; at bottom, both term relations are
definitionally trivial.  This is the semantic half of the positive
level-one bootstrap used after the path-valued positive-adequacy argument
derives contextual raw type uniqueness. -/
theorem LR0.limitedUniq_of_typeUniq
    (typeUniq : LogRel.RawTypeUniq Γ) :
    LogRel.LimitedUniq (LR0 : LogRel Γ 0) where
  align := by
    intro x A B p a b hpA hpB hxA hxB _ _ _ _
    obtain ⟨u, hAB⟩ := typeUniq hxA hxB
    refine ⟨u, hAB, ?_⟩
    intro y _ hxy
    cases p using WShape.casesOn with
    | bot =>
      simp only [LR0, LR0.DefEq, LR0.TyDefEq]
      split <;> trivial
    | sort r =>
      cases hpA.unfold
      cases hpB.unfold
      exact hxy

/-- Forget the dependent constructor telescope while retaining its aligned
per-field logical-relation evidence. -/
theorem LRS.CtorSpineDefEq.args
    (H : CtorSpineDefEq IH Head xs ys ps A) :
    CtorArgsDefEq IH xs ys ps := by
  induction H with
  | nil => exact .nil
  | cons _ _ hp hty hxy hv _ ih => exact .cons hp hty hxy hv ih
  | ret _ _ ih => exact ih

/-- Forget semantic fields while retaining the exact dependent pointwise
application spine. -/
theorem LRS.CtorSpineDefEq.spine
    {Γ : List SExpr} {n : Nat} {IH : LogRel Γ n}
    {Head A : SExpr} {xs ys : List SExpr} {ps : List (WShape n)}
    (H : CtorSpineDefEq IH Head xs ys ps A) :
    SExpr.SpineDefEq Γ Head xs.reverse ys.reverse A := by
  induction H with
  | nil => exact .nil
  | cons _ hPi _ _ hxy _ _ ih =>
    simpa only [List.reverse_cons] using ih.snoc hPi hxy
  | ret _ hresult ih => exact .ret ih hresult

/-- Keep the left constructor application at both endpoints. -/
theorem LRS.CtorSpineDefEq.left
    (H : CtorSpineDefEq IH Head xs ys ps A) :
    CtorSpineDefEq IH Head xs xs ps A := by
  induction H with
  | nil => exact .nil
  | cons _ hPi hp hty hxy hv hresult ih =>
    exact .cons ih hPi hp hty hxy.hasType.1 (IH.left hv)
      (hresult.symm.trans hresult)
  | ret _ hresult ih => exact .ret ih hresult

/-- Keep the right constructor application at both endpoints while
transporting its dependent result back to the original left-oriented type. -/
theorem LRS.CtorSpineDefEq.right
    (H : CtorSpineDefEq IH Head xs ys ps A) :
    CtorSpineDefEq IH Head ys ys ps A := by
  induction H with
  | nil => exact .nil
  | cons _ hPi hp hty hxy hv hresult ih =>
    exact .ret
      (.cons ih hPi hp hty hxy.hasType.2 (IH.left (IH.symm hv))
        (hresult.trans hresult.symm))
      hresult
  | ret _ hresult ih => exact .ret ih hresult

/-- Keep the final argument pair while using the left dependent prefix at
both endpoints.  Constructor spines are stored newest-first, so after the
outer result conversions have been crossed the displayed `cons` is exactly
the final application and its recursive tail is the prefix to duplicate. -/
theorem LRS.CtorSpineDefEq.leftPrefixes
    (H : CtorSpineDefEq IH Head (x :: xs) (y :: ys) (p :: ps) A) :
    CtorSpineDefEq IH Head (x :: xs) (y :: xs) (p :: ps) A := by
  generalize hx : x :: xs = xs' at H
  generalize hy : y :: ys = ys' at H
  generalize hp : p :: ps = ps' at H
  induction H generalizing x xs y ys p ps with
  | nil => simp at hx
  | cons hrest hPi hpty hty hxy hrel hresult ih =>
    simp only [List.cons.injEq] at hx hy hp
    rcases hx with ⟨rfl, rfl⟩
    rcases hy with ⟨rfl, rfl⟩
    rcases hp with ⟨rfl, rfl⟩
    exact .cons hrest.left hPi hpty hty hxy hrel hresult
  | ret hrest hresult ih =>
    exact .ret (ih hx hy hp) hresult

/-- Keep the final argument pair while using the right dependent prefix at
both endpoints. -/
theorem LRS.CtorSpineDefEq.rightPrefixes
    (H : CtorSpineDefEq IH Head (x :: xs) (y :: ys) (p :: ps) A) :
    CtorSpineDefEq IH Head (x :: ys) (y :: ys) (p :: ps) A := by
  generalize hx : x :: xs = xs' at H
  generalize hy : y :: ys = ys' at H
  generalize hp : p :: ps = ps' at H
  induction H generalizing x xs y ys p ps with
  | nil => simp at hx
  | cons hrest hPi hpty hty hxy hrel hresult ih =>
    simp only [List.cons.injEq] at hx hy hp
    rcases hx with ⟨rfl, rfl⟩
    rcases hy with ⟨rfl, rfl⟩
    rcases hp with ⟨rfl, rfl⟩
    exact .cons hrest.right hPi hpty hty hxy hrel hresult
  | ret hrest hresult ih =>
    exact .ret (ih hx hy hp) hresult

/-- Swap the two concrete constructor spines without changing the
left-oriented final result type. -/
theorem LRS.CtorSpineDefEq.symm
    (H : CtorSpineDefEq IH Head xs ys ps A) :
    CtorSpineDefEq IH Head ys xs ps A := by
  induction H with
  | nil => exact .nil
  | cons _ hPi hp hty hxy hv hresult ih =>
    exact .ret
      (.cons ih hPi hp hty hxy.symm (IH.symm hv) hresult.symm)
      hresult
  | ret _ hresult ih => exact .ret ih hresult

/-- Rebase every semantic field while preserving the same raw dependent
constructor telescope. -/
theorem LRS.CtorSpineDefEq.lift
    {IH : LogRel Γ n} {IH' : LogRel Γ n'} (le : n ≤ n')
    (hliftTy : ∀ {A B : SExpr} {a : WShape n}, a.HasType .type →
      (IH'.TyDefEq A B (a.lift n') ↔ IH.TyDefEq A B a))
    (hlift : ∀ {M N A : SExpr} {m a : WShape n}, m.HasType a →
      (IH'.DefEq M N A (m.lift n') (a.lift n') ↔ IH.DefEq M N A m a))
    (H : CtorSpineDefEq IH Head xs ys ps A) :
    CtorSpineDefEq IH' Head xs ys (ps.map (.lift n')) A := by
  induction H with
  | nil => exact .nil
  | cons _ hPi hp hty hxy hv hresult ih =>
    exact .cons ih hPi ((WShape.HasType.lift le).2 hp)
      ((hliftTy hp.isType).2 hty) hxy ((hlift hp).2 hv) hresult
  | ret _ hresult ih => exact .ret ih hresult

theorem LRS.CtorArgsDefEq.lengths
    (H : CtorArgsDefEq IH xs ys ps) :
    xs.length = ps.length ∧ ys.length = ps.length := by
  induction H with
  | nil => exact ⟨rfl, rfl⟩
  | cons _ _ _ _ _ ih =>
    exact ⟨congrArg Nat.succ ih.1, congrArg Nat.succ ih.2⟩

/-- Drop the newest related constructor field. -/
theorem LRS.CtorArgsDefEq.tail
    (H : CtorArgsDefEq IH (x :: xs) (y :: ys) (p :: ps)) :
    CtorArgsDefEq IH xs ys ps := by
  cases H with
  | cons _ _ _ _ hrest => exact hrest

/-- Compose adjacent exact constructor-field bundles using only the
level-indexed uniqueness fragment.  The output is left-oriented: its raw
and semantic equalities retain the first link's field type. -/
theorem LRS.CtorArgsDefEq.trans
    (uniq : LogRel.LimitedUniq IH)
    (H₁ : CtorArgsDefEq IH xs ys ps)
    (H₂ : CtorArgsDefEq IH ys zs ps) :
    CtorArgsDefEq IH xs zs ps := by
  induction H₁ generalizing zs with
  | nil =>
    cases H₂
    exact .nil
  | cons hp htyA hxy hvxy hrest ih =>
    cases H₂ with
    | cons hpB htyB hyz hvyz hrest₂ =>
      have hyyA := hxy.hasType.2
      have hyyB := hyz.hasType.1
      have vyyA := IH.left (IH.symm hvxy)
      have vyyB := IH.left hvyz
      obtain ⟨_, hAB, retype⟩ :=
        uniq.align hp hpB hyyA hyyB htyA htyB vyyA vyyB
      have hyzA := IsDefEq.defeqDF hAB.symm hyz
      have vyzA := retype hyz hvyz
      exact .cons hp htyA (hxy.trans hyzA) (IH.trans hvxy vyzA)
        (ih hrest₂)

theorem LRS.CtorArgsDefEq.left
    (H : CtorArgsDefEq IH xs ys ps) : CtorArgsDefEq IH xs xs ps := by
  induction H with
  | nil => exact .nil
  | cons hp hty hxy hv _ ih =>
    exact .cons hp hty hxy.hasType.1 (IH.left hv) ih

theorem LRS.CtorArgsDefEq.right
    (H : CtorArgsDefEq IH xs ys ps) : CtorArgsDefEq IH ys ys ps := by
  induction H with
  | nil => exact .nil
  | cons hp hty hxy hv _ ih =>
    exact .cons hp hty hxy.hasType.2 (IH.left (IH.symm hv)) ih

theorem LRS.CtorArgsDefEq.symm
    (H : CtorArgsDefEq IH xs ys ps) : CtorArgsDefEq IH ys xs ps := by
  induction H with
  | nil => exact .nil
  | cons hp hty hxy hv _ ih =>
    exact .cons hp hty hxy.symm (IH.symm hv) ih

theorem LRS.CtorArgsDefEq.lift
    {IH : LogRel Γ n} {IH' : LogRel Γ n'} (le : n ≤ n')
    (hliftTy : ∀ {A B : SExpr} {a : WShape n}, a.HasType .type →
      (IH'.TyDefEq A B (a.lift n') ↔ IH.TyDefEq A B a))
    (hlift : ∀ {M N A : SExpr} {m a : WShape n}, m.HasType a →
      (IH'.DefEq M N A (m.lift n') (a.lift n') ↔ IH.DefEq M N A m a))
    (H : CtorArgsDefEq IH xs ys ps) :
    CtorArgsDefEq IH' xs ys (ps.map (.lift n')) := by
  induction H with
  | nil => exact .nil
  | cons hp hty hxy hv _ ih =>
    exact .cons ((WShape.HasType.lift le).2 hp)
      ((hliftTy hp.isType).2 hty) hxy ((hlift hp).2 hv) ih

/-- Constructor observations, freely closed under the structural laws of a
logical relation.  The explicit `lift`/`unlift` constructors are important:
a high-level constructor field can contain refinements with no well-formed
projection at a lower shape level.  Retaining the original finite evidence
avoids the invalid general `Shape.WF.plift` principle while still exposing an
exact constructor spine at the leaves consumed by pattern adequacy. -/
inductive LRS.CtorDefEq (Γ : List SExpr) :
    {n : Nat} → LogRel Γ n → SExpr → SExpr → WShape (n + 1) → Prop where
  | exact {IH : LogRel Γ n} {c : Name} {rargs : List (WShape n)} {hwf}
      {M N : SExpr} {ls ls' : List SLevel} {args args' : List SExpr}
      {CHead CHead' A A' : SExpr} :
      Params.classify c = some (.ctor args.length) →
      args.length = rargs.length → args'.length = rargs.length →
      ls = ls' →
      WHRedS Γ M (args.foldr (fun a f => f.app a) (.const c ls)) →
      WHRedS Γ N (args'.foldr (fun a f => f.app a) (.const c ls')) →
      IsDefEq Γ (.const c ls) (.const c ls) CHead →
      IsDefEq Γ (.const c ls') (.const c ls') CHead' →
      SExpr.SpineWF Γ CHead args.reverse A →
      SExpr.SpineWF Γ CHead' args'.reverse A' →
      CtorArgsDefEq IH args args' rargs →
      CtorSpineDefEq IH CHead args args' rargs A →
      CtorSpineDefEq IH CHead' args' args rargs A' →
      CtorDefEq Γ IH M N (.ctor c rargs.reverse hwf)
  | left : CtorDefEq Γ IH M N m → CtorDefEq Γ IH M M m
  | symm : CtorDefEq Γ IH M N m → CtorDefEq Γ IH N M m
  | trans : CtorDefEq Γ IH M N m → CtorDefEq Γ IH N P m →
      CtorDefEq Γ IH M P m
  | mono : m ≤ m' → CtorDefEq Γ IH M N m' → CtorDefEq Γ IH M N m
  | whr : WHRedS Γ M M' → WHRedS Γ N N' → CtorDefEq Γ IH M N m →
      CtorDefEq Γ IH M' N' m
  | unwhr : WHRedS Γ M M' → WHRedS Γ N N' → CtorDefEq Γ IH M' N' m →
      CtorDefEq Γ IH M N m
  | lift {IH : LogRel Γ n} {IH' : LogRel Γ n'} (le : n ≤ n')
      (hliftTy : ∀ {A B : SExpr} {a : WShape n}, a.HasType .type →
        (IH'.TyDefEq A B (a.lift n') ↔ IH.TyDefEq A B a))
      (hlift : ∀ {M N A : SExpr} {m a : WShape n}, m.HasType a →
        (IH'.DefEq M N A (m.lift n') (a.lift n') ↔ IH.DefEq M N A m a)) :
      CtorDefEq Γ IH M N m → CtorDefEq Γ IH' M N (m.lift (n' + 1))
  | unlift {IH : LogRel Γ n} {IH' : LogRel Γ n'} (le : n ≤ n')
      (hliftTy : ∀ {A B : SExpr} {a : WShape n}, a.HasType .type →
        (IH'.TyDefEq A B (a.lift n') ↔ IH.TyDefEq A B a))
      (hlift : ∀ {M N A : SExpr} {m a : WShape n}, m.HasType a →
        (IH'.DefEq M N A (m.lift n') (a.lift n') ↔ IH.DefEq M N A m a)) :
      CtorDefEq Γ IH' M N (m.lift (n' + 1)) → CtorDefEq Γ IH M N m

theorem LRS.CtorDefEq.whr_iff
    (hM : WHRedS Γ M M') (hN : WHRedS Γ N N') :
    LRS.CtorDefEq Γ IH M N m ↔ LRS.CtorDefEq Γ IH M' N' m :=
  ⟨.whr hM hN, .unwhr hM hN⟩

theorem LRS.CtorDefEq.lift_iff {IH : LogRel Γ n} {IH' : LogRel Γ n'}
    (le : n ≤ n')
    (hliftTy : ∀ {A B : SExpr} {a : WShape n}, a.HasType .type →
      (IH'.TyDefEq A B (a.lift n') ↔ IH.TyDefEq A B a))
    (hlift : ∀ {M N A : SExpr} {m a : WShape n}, m.HasType a →
      (IH'.DefEq M N A (m.lift n') (a.lift n') ↔ IH.DefEq M N A m a)) :
    LRS.CtorDefEq Γ IH' M N (m.lift (n' + 1)) ↔
      LRS.CtorDefEq Γ IH M N m :=
  ⟨.unlift le hliftTy hlift, .lift le hliftTy hlift⟩

/-- An explicit equivalence between a logical relation and its realization
at a higher shape level.  `CtorDefEq` exposes these two clauses separately;
packaging them makes the target-level continuation used by its fold
composable. -/
structure LogRel.LiftEquiv
    (IH : LogRel Γ n) (IH' : LogRel Γ n') (le : n ≤ n') : Prop where
  ty : ∀ {A B : SExpr} {a : WShape n}, a.HasType .type →
    (IH'.TyDefEq A B (a.lift n') ↔ IH.TyDefEq A B a)
  term : ∀ {M N A : SExpr} {m a : WShape n}, m.HasType a →
    (IH'.DefEq M N A (m.lift n') (a.lift n') ↔
      IH.DefEq M N A m a)

/-- The two transport clauses supplied by a `CtorDefEq` lift constructor. -/
def LogRel.LiftEquiv.ofFields
    {IH : LogRel Γ n} {IH' : LogRel Γ n'} (le : n ≤ n')
    (hliftTy : ∀ {A B : SExpr} {a : WShape n}, a.HasType .type →
      (IH'.TyDefEq A B (a.lift n') ↔ IH.TyDefEq A B a))
    (hlift : ∀ {M N A : SExpr} {m a : WShape n}, m.HasType a →
      (IH'.DefEq M N A (m.lift n') (a.lift n') ↔
        IH.DefEq M N A m a)) :
    LogRel.LiftEquiv IH IH' le := ⟨hliftTy, hlift⟩

/-- Every relation is trivially equivalent to itself at the same level. -/
def LogRel.LiftEquiv.refl (IH : LogRel Γ n) :
    LogRel.LiftEquiv IH IH (Nat.le_refl n) where
  ty := by
    intro A B a ha
    simp only [WShape.lift_self]
  term := by
    intro M N A m a hma
    simp only [WShape.lift_self]

/-- Rebase a synchronized rectangle through a logical-relation lift
equivalence.  The iff is intentionally restricted to observations lifted
from the lower endpoint; it makes no projection claim about arbitrary
higher-level refinements. -/
theorem LogRel.LiftEquiv.rect
    {IH : LogRel Γ n} {IH' : LogRel Γ n'} {le : n ≤ n'}
    (E : LogRel.LiftEquiv IH IH' le) (hma : m.HasType a) :
    LogRel.DefEqRect IH' M₁ M₂ N₁ N₂ A
        (m.lift n') (a.lift n') ↔
      LogRel.DefEqRect IH M₁ M₂ N₁ N₂ A m a := by
  constructor
  · intro H
    exact ⟨(E.term hma).1 H.left,
      (E.term hma).1 H.right,
      (E.term hma).1 H.cross⟩
  · intro H
    exact ⟨(E.term hma).2 H.left,
      (E.term hma).2 H.right,
      (E.term hma).2 H.cross⟩

/-- Lift equivalences compose without exposing any high-level refinements at
the lower endpoint. -/
theorem LogRel.LiftEquiv.trans
    {IH₀ : LogRel Γ n₀} {IH₁ : LogRel Γ n₁}
    {IH₂ : LogRel Γ n₂} {le₀₁ : n₀ ≤ n₁} {le₁₂ : n₁ ≤ n₂}
    (H₀₁ : LogRel.LiftEquiv IH₀ IH₁ le₀₁)
    (H₁₂ : LogRel.LiftEquiv IH₁ IH₂ le₁₂) :
    LogRel.LiftEquiv IH₀ IH₂ (Nat.le_trans le₀₁ le₁₂) where
  ty := by
    intro A B a ha
    have ha' : (a.lift n₁).HasType .type := by
      simpa only [WShape.lift_type] using
        (WShape.HasType.lift le₀₁).2 ha
    rw [← WShape.lift_lift (s := a) (.inl le₀₁)]
    exact (H₁₂.ty ha').trans
      (H₀₁.ty ha)
  term := by
    intro M N A m a hma
    rw [← WShape.lift_lift (s := m) (.inl le₀₁),
      ← WShape.lift_lift (s := a) (.inl le₀₁)]
    exact (H₁₂.term ((WShape.HasType.lift le₀₁).2 hma)).trans
      (H₀₁.term hma)

/-- Cancel a common higher realization on shapes that originate at the
lowest relation.  This is deliberately weaker than projecting arbitrary
`IH₁` refinements: the only queried `IH₁` shapes are lifts of `IH₀`
shapes.  That restriction is what makes the operation valid and is the
transport law used by the `.lift` branch of a target-level continuation. -/
theorem LogRel.LiftEquiv.cancelRight
    {IH₀ : LogRel Γ n₀} {IH₁ : LogRel Γ n₁}
    {IH₂ : LogRel Γ n₂} {le₀₁ : n₀ ≤ n₁} {le₁₂ : n₁ ≤ n₂}
    (H₀₂ : LogRel.LiftEquiv IH₀ IH₂ (Nat.le_trans le₀₁ le₁₂))
    (H₁₂ : LogRel.LiftEquiv IH₁ IH₂ le₁₂) :
    LogRel.LiftEquiv IH₀ IH₁ le₀₁ where
  ty := by
    intro A B a ha
    have ha₁ : (a.lift n₁).HasType .type := by
      simpa only [WShape.lift_type] using
        (WShape.HasType.lift le₀₁).2 ha
    have hhigh := H₁₂.ty (A := A) (B := B) ha₁
    rw [WShape.lift_lift (s := a) (.inl le₀₁)] at hhigh
    exact hhigh.symm.trans (H₀₂.ty ha)
  term := by
    intro M N A m a hma
    have hhigh := H₁₂.term (M := M) (N := N) (A := A)
      ((WShape.HasType.lift le₀₁).2 hma)
    rw [WShape.lift_lift (s := m) (.inl le₀₁),
      WShape.lift_lift (s := a) (.inl le₀₁)] at hhigh
    exact hhigh.symm.trans (H₀₂.term hma)

/-- Rebase a related constructor spine through a packaged lift
equivalence. -/
theorem LRS.CtorArgsDefEq.rebase
    {IH : LogRel Γ n} {IH' : LogRel Γ n'} {le : n ≤ n'}
    (E : LogRel.LiftEquiv IH IH' le)
    (H : LRS.CtorArgsDefEq IH xs ys ps) :
    LRS.CtorArgsDefEq IH' xs ys (ps.map (.lift n')) :=
  H.lift le E.ty E.term

/-- A unary transport context from a native exact constructor observation
back to the logical relation and shape requested at the root.  In
particular, an `unlift` frame retains its high-level evidence instead of
projecting arbitrary higher-level constructor fields. -/
inductive LRS.CtorFrame (Γ : List SExpr) :
    {n k : Nat} → LogRel Γ n → WShape (n + 1) →
      LogRel Γ k → WShape (k + 1) → Prop where
  | refl : CtorFrame Γ IH m IH m
  | mono : m ≤ m' → CtorFrame Γ IH m' J p → CtorFrame Γ IH m J p
  | lift {IH : LogRel Γ n} {IH' : LogRel Γ n'} (le : n ≤ n')
      (E : LogRel.LiftEquiv IH IH' le) :
      CtorFrame Γ IH m J p →
      CtorFrame Γ IH' (m.lift (n' + 1)) J p
  | unlift {IH : LogRel Γ n} {IH' : LogRel Γ n'} (le : n ≤ n')
      (E : LogRel.LiftEquiv IH IH' le) :
      CtorFrame Γ IH' (m.lift (n' + 1)) J p →
      CtorFrame Γ IH m J p

/-- Reapply a constructor transport frame to native evidence. -/
theorem LRS.CtorFrame.apply
    (F : LRS.CtorFrame Γ IH m J p)
    (H : LRS.CtorDefEq Γ J M N p) :
    LRS.CtorDefEq Γ IH M N m := by
  induction F with
  | refl => exact H
  | mono hle _ ih => exact .mono hle (ih H)
  | lift le E _ ih => exact .lift le E.ty E.term (ih H)
  | unlift le E _ ih => exact .unlift le E.ty E.term (ih H)

/-- One native, exact constructor-spine observation.  Endpoint weak-head
reductions live in `CtorView`; this certificate contains only the finite
head, telescope, and field payload of the exact leaf. -/
inductive LRS.CtorExact (Γ : List SExpr) :
    {n : Nat} → LogRel Γ n → SExpr → SExpr → WShape (n + 1) → Prop where
  | intro {IH : LogRel Γ n} {c : Name} {rargs : List (WShape n)} {hwf}
      {ls ls' : List SLevel} {args args' : List SExpr}
      {CHead CHead' A A' : SExpr} :
      Params.classify c = some (.ctor args.length) →
      args.length = rargs.length → args'.length = rargs.length →
      ls = ls' →
      IsDefEq Γ (.const c ls) (.const c ls) CHead →
      IsDefEq Γ (.const c ls') (.const c ls') CHead' →
      SExpr.SpineWF Γ CHead args.reverse A →
      SExpr.SpineWF Γ CHead' args'.reverse A' →
      LRS.CtorArgsDefEq IH args args' rargs →
      LRS.CtorSpineDefEq IH CHead args args' rargs A →
      LRS.CtorSpineDefEq IH CHead' args' args rargs A' →
      CtorExact Γ IH
        (args.foldr (fun a f => f.app a) (.const c ls))
        (args'.foldr (fun a f => f.app a) (.const c ls'))
        (.ctor c rargs.reverse hwf)

/-- Reconstitute the free relation's exact constructor from a normalized
native leaf. -/
theorem LRS.CtorExact.toCtorDefEq
    (H : LRS.CtorExact Γ IH M N m) :
    LRS.CtorDefEq Γ IH M N m := by
  cases H with
  | intro hcl hlen hlen' hlevels hhead hhead' hspine hspine' hargs haligned hmirror =>
    exact .exact hcl hlen hlen' hlevels .rfl .rfl hhead hhead' hspine hspine'
      hargs haligned hmirror

/-- Mirror one exact native link. -/
theorem LRS.CtorExact.symm
    (H : LRS.CtorExact Γ IH M N m) :
    LRS.CtorExact Γ IH N M m := by
  cases H with
  | @intro c rargs hwf ls ls' args args' CHead CHead' A A'
      hcl hlen hlen' hlevels hhead hhead' hspine hspine' hargs haligned hmirror =>
    have hcl' : Params.classify c = some (.ctor args'.length) := by
      simpa [hlen, hlen'] using hcl
    exact .intro hcl' hlen' hlen hlevels.symm hhead' hhead hspine' hspine
      hargs.symm hmirror haligned

/-- Every native constructor link retains an ordinary typed equality of its
two concrete spines.  The result type is intentionally existential: adjacent
links may expose different telescope result types, and the normalized-chain
consumer aligns those types only after choosing the recursor domain at the
root. -/
theorem LRS.CtorExact.rawDefEq
    (H : LRS.CtorExact Γ IH M N m) :
    ∃ A, IsDefEq Γ M N A := by
  cases H with
  | @intro c rargs hwf ls ls' args args' CHead CHead' A A'
      hcl hlen hlen' hlevels hhead hhead' hspine hspine' hargs haligned hmirror =>
    subst ls'
    refine ⟨A, ?_⟩
    simpa only [List.foldl_reverse] using haligned.spine.congr hhead

/-- A term anchored to a classified constructor spine. -/
inductive LRS.CtorView (Γ : List SExpr) (M : SExpr) : SExpr → Prop where
  | intro {c : Name} {ls : List SLevel} {args : List SExpr} :
      Params.classify c = some (.ctor args.length) →
      WHRedS Γ M (args.foldr (fun a f => f.app a) (.const c ls)) →
      CtorView Γ M (args.foldr (fun a f => f.app a) (.const c ls))

/-- Move a constructor view forward along a weak-head reduction. -/
theorem LRS.CtorView.whr
    (hM : WHRedS Γ M M') (V : LRS.CtorView Γ M X) :
    LRS.CtorView Γ M' X := by
  cases V with
  | intro hcl hred =>
    exact .intro hcl (hM.determ_l hred (.ctorSpine hcl _))

/-- Move a constructor view backward along a weak-head reduction. -/
theorem LRS.CtorView.unwhr
    (hM : WHRedS Γ M M') (V : LRS.CtorView Γ M' X) :
    LRS.CtorView Γ M X := by
  cases V with
  | intro hcl hred => exact .intro hcl (.trans hM hred)

/-- A normalized link: one native exact leaf plus its transport frame back
to the root relation. -/
inductive LRS.CtorLink (Γ : List SExpr) (IH : LogRel Γ n)
    (m : WShape (n + 1)) : SExpr → SExpr → Prop where
  | intro (frame : LRS.CtorFrame Γ IH m J p)
      (exact : LRS.CtorExact Γ J X Y p) : CtorLink Γ IH m X Y

theorem LRS.CtorLink.toCtorDefEq
    (H : LRS.CtorLink Γ IH m X Y) :
    LRS.CtorDefEq Γ IH X Y m := by
  cases H with
  | intro frame exact => exact frame.apply exact.toCtorDefEq

theorem LRS.CtorLink.symm
    (H : LRS.CtorLink Γ IH m X Y) :
    LRS.CtorLink Γ IH m Y X := by
  cases H with
  | intro frame exact => exact .intro frame exact.symm

/-- Frames change only the semantic relation and observation shape; the raw
typed equality carried by the native leaf is unchanged. -/
theorem LRS.CtorLink.rawDefEq
    (H : LRS.CtorLink Γ IH m X Y) :
    ∃ A, IsDefEq Γ X Y A := by
  cases H with
  | intro _ exact => exact exact.rawDefEq

theorem LRS.CtorLink.mono (hle : m' ≤ m)
    (H : LRS.CtorLink Γ IH m X Y) :
    LRS.CtorLink Γ IH m' X Y := by
  cases H with
  | intro frame exact => exact .intro (.mono hle frame) exact

theorem LRS.CtorLink.lift
    {IH : LogRel Γ n} {IH' : LogRel Γ n'} (le : n ≤ n')
    (E : LogRel.LiftEquiv IH IH' le)
    (H : LRS.CtorLink Γ IH m X Y) :
    LRS.CtorLink Γ IH' (m.lift (n' + 1)) X Y := by
  cases H with
  | intro frame exact => exact .intro (.lift le E frame) exact

theorem LRS.CtorLink.unlift
    {IH : LogRel Γ n} {IH' : LogRel Γ n'} (le : n ≤ n')
    (E : LogRel.LiftEquiv IH IH' le)
    (H : LRS.CtorLink Γ IH' (m.lift (n' + 1)) X Y) :
    LRS.CtorLink Γ IH m X Y := by
  cases H with
  | intro frame exact => exact .intro (.unlift le E frame) exact

/-- A nonempty sequence of native exact links.  All free structural closure
has been pushed into link frames or into the sequence itself. -/
inductive LRS.CtorPath (Γ : List SExpr) (IH : LogRel Γ n)
    (m : WShape (n + 1)) : SExpr → SExpr → Prop where
  | single : LRS.CtorLink Γ IH m X Y → CtorPath Γ IH m X Y
  | cons : LRS.CtorLink Γ IH m X Y → CtorPath Γ IH m Y Z →
      CtorPath Γ IH m X Z

theorem LRS.CtorPath.toCtorDefEq
    (H : LRS.CtorPath Γ IH m X Y) :
    LRS.CtorDefEq Γ IH X Y m := by
  induction H with
  | single link => exact link.toCtorDefEq
  | cons link _ ih => exact link.toCtorDefEq.trans ih

/-- Retype and compose a normalized constructor path at one externally
chosen domain.  Only raw type uniqueness is needed: each native link already
carries its own typed equality, and the right endpoint of a retyped link is
the typed anchor for the remainder of the path.

This is the raw half of the joint L4L-16/17 chain consumer.  Weak-head
subject reduction is deliberately absent here; it is needed only to provide
the first root-to-view anchor consumed by `CtorChain.rawDefEqAt`. -/
theorem LRS.CtorPath.rawDefEqAt
    (uniq : LogRel.RawTypeUniq Γ)
    (H : LRS.CtorPath Γ IH m X Y)
    (hX : IsDefEq Γ X X D) :
    IsDefEq Γ X Y D := by
  induction H with
  | single link =>
    obtain ⟨A, hXY⟩ := link.rawDefEq
    obtain ⟨_, hAD⟩ := uniq hXY.hasType.1 hX
    exact hAD.defeqDF hXY
  | cons link rest ih =>
    obtain ⟨A, hXY⟩ := link.rawDefEq
    obtain ⟨_, hAD⟩ := uniq hXY.hasType.1 hX
    have hXYD : IsDefEq Γ _ _ D := hAD.defeqDF hXY
    exact hXYD.trans (ih hXYD.hasType.2)

/-- A native-path consumer that receives every exact link already retyped at
one common root domain.  This is stronger than `CtorChain.Algebra.exact` in
exactly one controlled way: raw uniqueness is used by `foldRaw` before the
handler runs, so the handler never has to reconcile telescope result types
or manufacture typing for a shared midpoint. -/
structure LRS.CtorPath.RawAlgebra (Γ : List SExpr) (IH : LogRel Γ n)
    (m : WShape (n + 1)) (D : SExpr) (Q : SExpr → SExpr → Prop) where
  exact : ∀ {k : Nat} {J : LogRel Γ k} {p : WShape (k + 1)} {X Y : SExpr},
    LRS.CtorFrame Γ IH m J p → LRS.CtorExact Γ J X Y p →
    IsDefEq Γ X Y D → Q X Y
  trans : ∀ {X Y Z : SExpr}, Q X Y → Q Y Z → Q X Z

/-- Fold a normalized path while threading the common-domain self-typing of
its current vertex.  Each exact leaf is retyped once; its right endpoint then
anchors the recursive tail. -/
theorem LRS.CtorPath.foldRaw
    (uniq : LogRel.RawTypeUniq Γ)
    (alg : LRS.CtorPath.RawAlgebra Γ IH m D Q)
    (H : LRS.CtorPath Γ IH m X Y)
    (hX : IsDefEq Γ X X D) : Q X Y := by
  induction H with
  | single link =>
    cases link with
    | intro frame leaf =>
      obtain ⟨A, hXY⟩ := leaf.rawDefEq
      obtain ⟨_, hAD⟩ := uniq hXY.hasType.1 hX
      exact alg.exact frame leaf (hAD.defeqDF hXY)
  | cons link rest ih =>
    cases link with
    | intro frame leaf =>
      obtain ⟨A, hXY⟩ := leaf.rawDefEq
      obtain ⟨_, hAD⟩ := uniq hXY.hasType.1 hX
      have hXYD : IsDefEq Γ _ _ D := hAD.defeqDF hXY
      exact alg.trans (alg.exact frame leaf hXYD) (ih hXYD.hasType.2)

/-! #### Anchored native links: the chain fold without raw type uniqueness

`CtorPath.foldRaw` above spends `LogRel.RawTypeUniq` once per link, and not to
type the middle term of a `trans`: after the first link the anchor travels with
the term.  What it reconciles is the link's *own* result type — the `A` of
`CtorExact`'s retained `SpineWF` certificate — against the anchor inherited
from the root.  The definitions below retain that reconciliation as a transport
attached to the native leaf, so that the fold performs no type identification
of its own.  See the 2026-08-15 chain-wall entry in
`plans/l4l-16c-buildp-premortem.md`. -/

/-- The retyping action a normalized chain performs at one native link:
transport the link's typed equality to any domain that types one of its
endpoints.

This is deliberately a transport rather than a sort-level type equality.  The
fold never needs the two types identified — only the equality moved — so
producing `∃ u, IsDefEq Γ A D (.sort u)` and then converting at every call site
would erase the very step a consumer replays.  Both endpoints are served so
that a mirrored link (`CtorExact.symm`) needs no separate producer. -/
structure LRS.CtorRetype (Γ : List SExpr) (X Y : SExpr) : Prop where
  /-- Retype from a domain that types the left endpoint. -/
  ofLeft : ∀ {D : SExpr}, IsDefEq Γ X X D → IsDefEq Γ X Y D
  /-- Retype from a domain that types the right endpoint. -/
  ofRight : ∀ {D : SExpr}, IsDefEq Γ Y Y D → IsDefEq Γ X Y D

/-- The retyping of a link is unchanged by mirroring it. -/
theorem LRS.CtorRetype.symm (H : LRS.CtorRetype Γ X Y) :
    LRS.CtorRetype Γ Y X where
  ofLeft h := (H.ofRight h).symm
  ofRight h := (H.ofLeft h).symm

/-- Environment-level constructor result-type discipline, path-valued: the
result type recorded by a classified constructor's application spine *is* the
type of that application, up to a heterogeneous conversion path.

This is route (ii) of the 2026-08-15 chain-wall audit, stated exactly.  It is
strictly weaker than `LogRel.RawTypeUniq` in two independent ways: its subject
is a registered constructor application whose head typing and spine
certificate are both retained, rather than an arbitrary term; and its
conclusion is a `TypeDefEqPath` rather than a collapsed conversion, so it never
charges `TypeDefEqPath.collapse` — which is itself the whole of raw type
uniqueness. -/
def LRS.CtorSpineTypeUniqPath (Γ : List SExpr) : Prop :=
  ∀ {c : Name} {ls : List SLevel} {args : List SExpr} {CHead A D : SExpr},
    Params.classify c = some (.ctor args.length) →
    IsDefEq Γ (.const c ls) (.const c ls) CHead →
    SExpr.SpineWF Γ CHead args.reverse A →
    IsDefEq Γ (args.foldr (fun a f => f.app a) (.const c ls))
      (args.foldr (fun a f => f.app a) (.const c ls)) D →
    ∃ u, TypeDefEqPath Γ A D u

/-- Raw type uniqueness supplies the discipline by a single-edge path.  This
certifies that nothing has been strengthened: the new obligation is implied by
the one it replaces. -/
theorem LRS.CtorSpineTypeUniqPath.of_rawTypeUniq
    (uniq : LogRel.RawTypeUniq Γ) : LRS.CtorSpineTypeUniqPath Γ := by
  intro c ls args CHead A D _ hhead hspine hXD
  have hXA : IsDefEq Γ (args.foldr (fun a f => f.app a) (.const c ls))
      (args.foldr (fun a f => f.app a) (.const c ls)) A := by
    simpa only [List.foldl_reverse] using hspine.hasType hhead
  obtain ⟨u, hAD⟩ := uniq hXA hXD
  exact ⟨u, .single hAD⟩

/-! #### Generation-side discharge of the constructor result-type discipline

Everything below discharges `LRS.CtorSpineTypeUniqPath` — and, with it, root
subject reduction — from one named residual, without any depth index and
without any derivation induction on the ambient equality.

The pivot is an erasure repair.  `HasTypeStratifiedS.to_core` (SExpr:2580)
*discards* the outer conversions of a stratified typing, and that discard is
the only reason `core_aligned_of_typeUniq` has to buy the alignment back with
`LogRel.RawTypeUniq`.  Those conversions are already `IsDefEqStrong` type
equalities, so retaining them as a `TypeDefEqPath` costs nothing
(`HasTypeStratifiedS.to_core_path`).  Once retained, three free steps follow:

1. *Any* typing of an application spine reconstructs, one `app` node at a
   time, as a `SExpr.SpineWF` starting from a typing of the spine's literal
   head (`HasTypeStratifiedS.spineWF_of_foldl`).  `SpineWF` already absorbs
   conversion paths at both ends, so no type is identified in the process.
2. The head of a classified constructor spine is a *registered constant*, and
   the environment assigns it exactly one declaration.  Two typings of
   `.const c ls` therefore expose literally the same core type
   (`LRS.constTypeUniqPath`).  This is the generation-side step, and it
   consumes nothing at all.
3. The two `SpineWF` runs are then compared layer by layer
   (`SExpr.SpineWF.result_path`).

Only step 3 has content, and its content is exactly Pi injectivity for type
paths — `LRS.PiPathInv`.  Nothing here charges `TypeDefEqPath.collapse`
(which is the whole of raw type uniqueness), nothing aligns two universe
indices, and nothing mentions a stratification depth in its statement. -/

/-- Strip the outer conversions of a stratified typing while *retaining* them
as a heterogeneous type path.

This is `HasTypeStratifiedS.to_core` (SExpr:2580) with the erasure removed.
Every `defeq` node of a stratified derivation carries an `IsDefEqStrong` type
equality, so the discarded conversions already form a `TypeDefEqPath`; the
base case closes because a syntax-directed core derivation always retains a
typing of its own type (`HasTypeStratifiedS.isType`, SExpr:2716). -/
theorem HasTypeStratifiedS.to_core_path
    {Γ : List SExpr} {e A : SExpr} {n : Nat}
    (H : HasTypeStratifiedS Γ e A true n) :
    ∃ A' u, HasTypeStratifiedS Γ e A' false n ∧ TypeDefEqPath Γ A' A u := by
  generalize hb : true = b at H
  induction H with cases hb
  | base h _ =>
    obtain ⟨u, hty⟩ := h.isType
    exact ⟨_, u, h, .single hty.hasType⟩
  | defeq hEq _ _ _ _ _ ih =>
    obtain ⟨A', u, hcore, hpath⟩ := ih rfl
    exact ⟨A', u, hcore.mono (Nat.le_succ _), hpath.trans (.single hEq.defeq)⟩

/-- Align a weak self-typing with a syntax-directed core, path-valued.

This is `IsDefEq.core_aligned_of_stratified_inversion` (ADQ:780) with its
inversion package deleted: the alignment that theorem obtains from raw type
uniqueness is the path `to_core_path` never threw away. -/
theorem IsDefEq.core_aligned_path [Params.Semantic]
    {Γ : List SExpr} {e A : SExpr}
    (hΓ : Ctx.WF Γ) (H : IsDefEq Γ e e A) :
    ∃ n A' u, HasTypeStratifiedS Γ e A' false n ∧ TypeDefEqPath Γ A' A u := by
  obtain ⟨n, hs, _⟩ := (H.strong hΓ).stratify
  obtain ⟨A', u, hcore, hpath⟩ := hs.to_core_path
  exact ⟨n, A', u, hcore, hpath⟩

/-- A spine absorbs an entire conversion path on its head type, one `conv`
edge at a time.  No universe alignment between adjacent edges is needed,
which is why the path never has to be collapsed first. -/
theorem SpineWF.conv_path {Γ : List SExpr} {A A' B : SExpr} {u : SLevel}
    {es : List SExpr} (P : TypeDefEqPath Γ A A' u) :
    SExpr.SpineWF Γ A' es B → SExpr.SpineWF Γ A es B := by
  induction P with
  | single h => exact fun H => .conv h H
  | trans _ _ ih₁ ih₂ => exact fun H => ih₁ (ih₂ H)

/-- The `ret` dual of `SpineWF.conv_path`: a spine absorbs an entire
conversion path on its *result* type as well.  Ported from the green probe
`plans/probes/probeS-spinedepth.lean`. -/
theorem SpineWF.ret_path {Γ : List SExpr} {B B' : SExpr} {u : SLevel}
    (P : TypeDefEqPath Γ B B' u) :
    ∀ {A : SExpr} {es : List SExpr},
      SExpr.SpineWF Γ A es B → SExpr.SpineWF Γ A es B' := by
  induction P with
  | single h => exact fun H => H.ret h
  | trans _ _ ih₁ ih₂ => exact fun H => ih₂ (ih₁ H)

/-- Path-threading inversion of an empty spine.  The incoming path is carried
through the `conv`/`ret` edges rather than being re-created, so no typing of
the head is required. -/
theorem SpineWF.nil_path {Γ : List SExpr} {A B : SExpr} {es : List SExpr}
    (H : SExpr.SpineWF Γ A es B) (hes : es = []) :
    ∀ {C : SExpr} {u : SLevel}, TypeDefEqPath Γ C A u →
      ∃ v, TypeDefEqPath Γ C B v := by
  induction H with
  | nil => exact fun P => ⟨_, P⟩
  | cons => exact absurd hes (by simp)
  | conv hty _ ih => exact fun P => ih hes (P.trans (.single hty))
  | ret _ hret ih =>
    intro C u P
    obtain ⟨v, Q⟩ := ih hes P
    exact ⟨v, Q.trans (.single hret)⟩

/-- Path-threading inversion of a nonempty spine: the incoming path is
extended until it reaches the syntactic Pi at which the first argument is
consumed.  The Pi is exposed *as the path's right endpoint*, which is exactly
the form `LRS.PiPathInv` inverts. -/
theorem SpineWF.cons_path {Γ : List SExpr} {A B : SExpr} {es : List SExpr}
    {e : SExpr} {es' : List SExpr}
    (H : SExpr.SpineWF Γ A es B) (hes : es = e :: es') :
    ∀ {C : SExpr} {u : SLevel}, TypeDefEqPath Γ C A u →
      ∃ D₁ D₂ w, TypeDefEqPath Γ C (.forallE D₁ D₂) w ∧
        IsDefEq Γ e e D₁ ∧ SExpr.SpineWF Γ (D₂.inst e) es' B := by
  induction H with
  | nil => exact absurd hes (by simp)
  | cons he rest _ =>
    intro C u P
    injection hes with hee hess
    subst hee
    subst hess
    exact ⟨_, _, u, P, he, rest⟩
  | conv hty _ ih => exact fun P => ih hes (P.trans (.single hty))
  | ret _ hret ih =>
    intro C u P
    obtain ⟨D₁, D₂, w, Q, hD, rest⟩ := ih hes P
    exact ⟨D₁, D₂, w, Q, hD, rest.ret hret⟩

/-- Every stratified typing of a left-associated application spine *is* a
`SExpr.SpineWF` from a typing of the spine's literal head.

`HasTypeStratifiedS.foldl_app_head` (SExpr:2634) already walks the spine, but
retains only the head; this retains the whole layer structure and the exact
result type of the walk.  The proof consumes nothing: the recursion is on the
argument list, each `app` node is exposed by `to_core_path`, and the discarded
conversions are absorbed by `SpineWF.conv_path`. -/
theorem HasTypeStratifiedS.spineWF_of_foldl_bound {Γ : List SExpr} :
    ∀ {es : List SExpr} {hd V : SExpr} {n : Nat},
      HasTypeStratifiedS Γ (es.foldl (fun f a => f.app a) hd) V true n →
      ∃ HdTy m, m + es.length ≤ n ∧ HasTypeStratifiedS Γ hd HdTy true m ∧
        SExpr.SpineWF Γ HdTy es V := by
  intro es
  induction es with
  | nil => intro hd V n H; exact ⟨V, n, by simp, H, .nil⟩
  | cons a es ih =>
    intro hd V n H
    simp only [List.foldl_cons] at H
    obtain ⟨HdTy', m, hle, hHead', hspine⟩ := ih H
    obtain ⟨T, u, hcore, hpath⟩ := hHead'.to_core_path
    cases hcore with
    | app hA hB hf ha hR =>
      simp only [List.length_cons] at hle ⊢
      exact ⟨_, _, by omega, hf,
        .cons ha.hasType (SpineWF.conv_path hpath hspine)⟩

/-- The unbounded form.  Statement unchanged; the bound follows by `omega`
wherever a consumer wants it. -/
theorem HasTypeStratifiedS.spineWF_of_foldl {Γ : List SExpr} :
    ∀ {es : List SExpr} {hd V : SExpr} {n : Nat},
      HasTypeStratifiedS Γ (es.foldl (fun f a => f.app a) hd) V true n →
      ∃ HdTy m, HasTypeStratifiedS Γ hd HdTy true m ∧
        SExpr.SpineWF Γ HdTy es V := by
  intro es hd V n H
  obtain ⟨HdTy, m, _, hhd, hspine⟩ := H.spineWF_of_foldl_bound
  exact ⟨HdTy, m, hhd, hspine⟩

/-- **The generation-side step.**  Two typings of one registered constant are
path-equal, and the proof consumes no uniqueness, no inversion and no
adequacy.

The environment assigns `c` exactly one declaration, so the two core
derivations expose *literally the same* type `SExpr.mkInst ls ci.type`; the
two conversion paths retained by `to_core_path` then compose.  This is the
sense in which the residual has left the depth-indexed fixpoint: its subject
is a registered declaration, and a registered declaration has one type. -/
theorem LRS.constTypeUniqPath [Params.Semantic] {Γ : List SExpr} {c : Name}
    {ls : List SLevel} {T₁ T₂ : SExpr} {n : Nat} (hΓ : Ctx.WF Γ)
    (h₁ : IsDefEq Γ (.const c ls) (.const c ls) T₁)
    (h₂ : HasTypeStratifiedS Γ (.const c ls) T₂ true n) :
    ∃ u, TypeDefEqPath Γ T₁ T₂ u := by
  obtain ⟨_, C₁, u₁, hcore₁, hpath₁⟩ := h₁.core_aligned_path hΓ
  obtain ⟨C₂, u₂, hcore₂, hpath₂⟩ := h₂.to_core_path
  cases hcore₁ with
  | const hreg₁ _ _ =>
    cases hcore₂ with
    | const hreg₂ _ _ =>
      cases hreg₁.symm.trans hreg₂
      obtain ⟨v, hpath₁'⟩ := hpath₁.symm
      exact ⟨v, hpath₁'.trans hpath₂⟩

/-- Pi injectivity for heterogeneous type paths, uniformly over well-formed
target contexts.  This is the *single* residual of the chain wall after the
repair.

Three things are deliberately absent from the statement.  There is no
stratification depth: unlike `JointStratifiedPathInversion.forallEInv`
(ADQ:234) it demands no endpoint certificates, so no consumer has to name a
depth.  There is no universe alignment: `sortPathInv` is never needed by any
consumer below.  And there is no collapse: the conclusion is again path-valued,
so `TypeDefEqPath.collapse` — which is the whole of raw type uniqueness — is
never charged.  `LRS.PiPathInv.of_adequacy` in `ShapeLogRelAdequacy.lean` is
the producer, and `LRS.PiPathInv.of_jointStratifiedPathInversion` there
certifies that this is a weakening of the package it replaces. -/
def LRS.PiPathInv : Prop :=
  ∀ {Γ : List SExpr} {A B A' B' : SExpr} {s : SLevel},
    Ctx.WF Γ → TypeDefEqPath Γ (.forallE A B) (.forallE A' B') s →
    ∃ u v, TypeDefEqPath Γ A A' u ∧ TypeDefEqPath (A :: Γ) B B' v

/-- Two spines over the *same* argument list, started from path-equal head
types, reach path-equal result types.

This is the only step with content, and its content is `LRS.PiPathInv`, spent
once per argument.  Each layer inverts the Pi exposed by `SpineWF.cons_path`
and substitutes the shared argument into the resulting codomain path; the
`conv`/`ret` edges of either spine are absorbed into the running path without
any identification. -/
theorem SpineWF.result_path {Γ : List SExpr} {A₁ B₁ : SExpr} {es : List SExpr}
    (piInv : LRS.PiPathInv) (hΓ : Ctx.WF Γ)
    (H₁ : SExpr.SpineWF Γ A₁ es B₁) :
    ∀ {A₂ B₂ : SExpr} {u : SLevel}, SExpr.SpineWF Γ A₂ es B₂ →
      TypeDefEqPath Γ A₁ A₂ u → ∃ v, TypeDefEqPath Γ B₁ B₂ v := by
  induction H₁ with
  | nil => exact fun H₂ P => H₂.nil_path rfl P
  | @cons e A₁' A₂' es₀ B₀ he _ ih =>
    intro A₂ B₂ u H₂ P
    obtain ⟨D₁, D₂, w, Q, _, H₂'⟩ := H₂.cons_path rfl P
    obtain ⟨_, _, _, hcod⟩ := piInv hΓ Q
    have hsub := hcod.subst (Ctx.Subst.one IsDefEq.weakCore IsDefEq.bvar he)
    exact ih H₂' (by simpa only [SExpr.inst] using hsub)
  | conv hty _ ih =>
    intro A₂ B₂ u H₂ P
    exact ih H₂ ((TypeDefEqPath.single hty.symm).trans P)
  | ret _ hret ih =>
    intro A₂ B₂ u H₂ P
    obtain ⟨v, Q⟩ := ih H₂ P
    exact ⟨_, (TypeDefEqPath.single hret.symm).trans Q⟩

/-- **The environment-level statement, in full generality.**  Any two typings
of one fully-applied *registered-constant* spine are path-equal.

Note what the proof does not use: no classification of `c` is required at all.
The result-type discipline the chain fold needs is not special to
constructors — it is the discipline of registered declarations, and the
constructor classification only selects which spines the fold meets. -/
theorem LRS.constSpineTypeUniqPath [Params.Semantic] {Γ : List SExpr}
    {c : Name} {ls : List SLevel} {args : List SExpr} {T₁ T₂ : SExpr}
    (piInv : LRS.PiPathInv) (hΓ : Ctx.WF Γ)
    (h₁ : IsDefEq Γ (args.foldr (fun a f => f.app a) (.const c ls))
      (args.foldr (fun a f => f.app a) (.const c ls)) T₁)
    (h₂ : IsDefEq Γ (args.foldr (fun a f => f.app a) (.const c ls))
      (args.foldr (fun a f => f.app a) (.const c ls)) T₂) :
    ∃ u, TypeDefEqPath Γ T₁ T₂ u := by
  obtain ⟨n₁, hs₁, _⟩ := (h₁.strong hΓ).stratify
  obtain ⟨n₂, hs₂, _⟩ := (h₂.strong hΓ).stratify
  rw [← List.foldl_reverse] at hs₁ hs₂
  obtain ⟨Hd₁, m₁, hhd₁, hsp₁⟩ := hs₁.spineWF_of_foldl
  obtain ⟨Hd₂, m₂, hhd₂, hsp₂⟩ := hs₂.spineWF_of_foldl
  obtain ⟨_, hlink⟩ := LRS.constTypeUniqPath hΓ hhd₁.hasType hhd₂
  exact hsp₁.result_path piInv hΓ hsp₂ hlink

/-- Path-valued Pi injectivity discharges the constructor result-type
discipline outright.  This is the intended producer of
`LRS.CtorSpineTypeUniqPath`, and the counterpart of `.of_rawTypeUniq` above:
the same conclusion from a strictly weaker input. -/
theorem LRS.CtorSpineTypeUniqPath.of_piPathInv [Params.Semantic]
    {Γ : List SExpr} (piInv : LRS.PiPathInv) (hΓ : Ctx.WF Γ) :
    LRS.CtorSpineTypeUniqPath Γ := by
  intro c ls args CHead A D _ hhead hspine hXD
  have hXA : IsDefEq Γ (args.foldr (fun a f => f.app a) (.const c ls))
      (args.foldr (fun a f => f.app a) (.const c ls)) A := by
    simpa only [List.foldl_reverse] using hspine.hasType hhead
  exact LRS.constSpineTypeUniqPath piInv hΓ hXA hXD

/-! #### Weak-head subject reduction from the same residual

`WHRed.defeq_of_stratified_inversion` (ADQ:796) opens every case with
`core_aligned_of_stratified_inversion`, i.e. with raw type uniqueness at the
reducing term.  With the alignment retained instead of repurchased, the
application and major cases become free, `beta` spends only `LRS.PiPathInv`,
and the registered-contraction case spends only the spine discipline above —
`Pattern.MatchesS.head_spine` (SExpr:899) says a matched redex *is* a
constant-headed spine, so its two type observations are reconciled by exactly
the environment-level fact the constructor leaves use.

The multi-step form then needs no re-certification at all.  The 2026-08-15
audit's obstruction was that `WHRedS.defeq_of_stratified_inversion` (ADQ:841)
takes each next step's typing from `ih.hasType.2`, whose stratified depth is
existential, so a redex certificate bounds only the first step.  That
obstruction is dissolved rather than answered: the per-step lemma below names
no depth, so there is nothing left for the induction to lose. -/

/-- One weak-head step preserves a supplied type, from path-valued Pi
injectivity alone. -/
theorem WHRed.defeq_of_piPathInv [Params.Semantic] {Γ : List SExpr}
    {e1 e2 A : SExpr}
    (piInv : LRS.PiPathInv) (hΓ : Ctx.WF Γ)
    (H : WHRed Γ e1 e2) (he : IsDefEq Γ e1 e1 A) :
    IsDefEq Γ e1 e2 A := by
  induction H generalizing A with
  | app hred ih =>
    obtain ⟨_, _, _, hcore, hty⟩ := he.core_aligned_path hΓ
    cases hcore with
    | app hD hC hf ha hR =>
      exact hty.defeqDF (.appDF (ih hf.hasType) ha.hasType)
  | major hmajor hred ih =>
    obtain ⟨_, _, _, hcore, hty⟩ := he.core_aligned_path hΓ
    cases hcore with
    | app hD hC hf ha hR =>
      exact hty.defeqDF (.appDF hf.hasType (ih ha.hasType))
  | beta =>
    obtain ⟨_, _, _, hcore, hty⟩ := he.core_aligned_path hΓ
    cases hcore with
    | app hD hC hlam ha hR =>
      obtain ⟨_, _, _, hlamCore, hlamTy⟩ := hlam.hasType.core_aligned_path hΓ
      cases hlamCore with
      | lam hDom hCod hBody hPi =>
        obtain ⟨_, _, hDomEq, hCodEq⟩ := piInv hΓ hlamTy
        obtain ⟨_, hDomEq'⟩ := hDomEq.symm
        have haDom := hDomEq'.defeqDF ha.hasType
        have hβ := IsDefEq.beta hBody.hasType haDom
        have hCodInst := hCodEq.subst
          (Ctx.Subst.one IsDefEq.weakCore IsDefEq.bvar haDom)
        exact hty.defeqDF (hCodInst.defeqDF hβ)
  | extra action =>
    obtain ⟨_, _, _, hcore, hty⟩ := he.core_aligned_path hΓ
    obtain ⟨c, ls', args, heq, _⟩ := action.matched.head_spine
    subst heq
    obtain ⟨_, hActionTy⟩ :=
      LRS.constSpineTypeUniqPath piInv hΓ hcore.hasType action.sound.hasType.1
    obtain ⟨_, hActionTy'⟩ := hActionTy.symm
    exact hty.defeqDF (hActionTy'.defeqDF action.sound)

/-- Multi-step weak-head subject reduction, from the same residual.  Nothing
is re-certified along the sequence because nothing in the per-step lemma is
indexed by a depth. -/
theorem WHRedS.defeq_of_piPathInv [Params.Semantic] {Γ : List SExpr}
    {e1 e2 A : SExpr}
    (piInv : LRS.PiPathInv) (hΓ : Ctx.WF Γ)
    (H : WHRedS Γ e1 e2) (he : IsDefEq Γ e1 e1 A) :
    IsDefEq Γ e1 e2 A := by
  induction H with
  | rfl => exact he
  | tail hred hstep ih =>
    exact ih.trans (hstep.defeq_of_piPathInv piInv hΓ ih.hasType.2)

/-- The constructor result-type discipline retypes every native exact link.
Both directions are served by the same environment-level fact: for the right
endpoint it is applied twice at that endpoint's own spine certificate, once
against the link's type and once against the requested domain, and the two
paths are composed.  No sort index is ever identified. -/
theorem LRS.CtorExact.retype_of_ctorSpineTypeUniqPath
    (disc : LRS.CtorSpineTypeUniqPath Γ)
    (H : LRS.CtorExact Γ J X Y p) : LRS.CtorRetype Γ X Y := by
  cases H with
  | @intro c rargs hwf ls ls' args args' CHead CHead' A A'
      hcl hlen hlen' hlevels hhead hhead' hspine hspine' hargs haligned hmirror =>
    subst ls'
    have hXY : IsDefEq Γ (args.foldr (fun a f => f.app a) (.const c ls))
        (args'.foldr (fun a f => f.app a) (.const c ls)) A := by
      simpa only [List.foldl_reverse] using haligned.spine.congr hhead
    have hcl' : Params.classify c = some (.ctor args'.length) := by
      simpa [hlen, hlen'] using hcl
    refine ⟨?_, ?_⟩
    · intro D hXD
      obtain ⟨_, hpath⟩ := disc hcl hhead hspine hXD
      exact hpath.defeqDF hXY
    · intro D hYD
      obtain ⟨_, hpathA⟩ := disc hcl' hhead' hspine' hXY.hasType.2
      obtain ⟨_, hpathD⟩ := disc hcl' hhead' hspine' hYD
      obtain ⟨_, hpathAr⟩ := hpathA.symm
      exact (hpathAr.trans hpathD).defeqDF hXY

/-- Every framed native leaf under one root observation admits the link
retyping.  Scoped to the frame and the leaf rather than to the whole
environment: this is exactly the pair `LRS.CtorPath.RawAlgebra.exact` already
receives, so the discipline cannot be satisfied by a retyping belonging to some
other constructor observation. -/
def LRS.CtorAnchorDisciplineAt (Γ : List SExpr) (IH : LogRel Γ n)
    (m : WShape (n + 1)) : Prop :=
  ∀ {k : Nat} {J : LogRel Γ k} {p : WShape (k + 1)} {X Y : SExpr},
    LRS.CtorFrame Γ IH m J p → LRS.CtorExact Γ J X Y p →
    LRS.CtorRetype Γ X Y

theorem LRS.CtorAnchorDisciplineAt.of_ctorSpineTypeUniqPath
    (disc : LRS.CtorSpineTypeUniqPath Γ) :
    LRS.CtorAnchorDisciplineAt Γ IH m :=
  fun _ leaf => leaf.retype_of_ctorSpineTypeUniqPath disc

/-- The discipline is implied by the raw type uniqueness it replaces. -/
theorem LRS.CtorAnchorDisciplineAt.of_rawTypeUniq
    (uniq : LogRel.RawTypeUniq Γ) :
    LRS.CtorAnchorDisciplineAt Γ IH m :=
  LRS.CtorAnchorDisciplineAt.of_ctorSpineTypeUniqPath
    (LRS.CtorSpineTypeUniqPath.of_rawTypeUniq uniq)

/-- Fold a normalized path with no type identification at all: each link
retypes itself at the inherited anchor, and the retyped right endpoint anchors
the tail.  This is `CtorPath.foldRaw` with `LogRel.RawTypeUniq` replaced by the
strictly weaker per-leaf transport. -/
theorem LRS.CtorPath.foldRaw_of_anchorDiscipline
    (disc : LRS.CtorAnchorDisciplineAt Γ IH m)
    (alg : LRS.CtorPath.RawAlgebra Γ IH m D Q)
    (H : LRS.CtorPath Γ IH m X Y)
    (hX : IsDefEq Γ X X D) : Q X Y := by
  induction H with
  | single link =>
    cases link with
    | intro frame leaf =>
      exact alg.exact frame leaf ((disc frame leaf).ofLeft hX)
  | cons link rest ih =>
    cases link with
    | intro frame leaf =>
      have hXYD := (disc frame leaf).ofLeft hX
      exact alg.trans (alg.exact frame leaf hXYD) (ih hXYD.hasType.2)

/-- The raw half of the path consumer, likewise free of type identification.
This is `CtorPath.rawDefEqAt` with the per-leaf transport in place of
`LogRel.RawTypeUniq`. -/
theorem LRS.CtorPath.rawDefEqAt_of_anchorDiscipline
    (disc : LRS.CtorAnchorDisciplineAt Γ IH m)
    (H : LRS.CtorPath Γ IH m X Y)
    (hX : IsDefEq Γ X X D) : IsDefEq Γ X Y D := by
  induction H with
  | single link =>
    cases link with
    | intro frame leaf => exact (disc frame leaf).ofLeft hX
  | cons link rest ih =>
    cases link with
    | intro frame leaf =>
      have hXYD := (disc frame leaf).ofLeft hX
      exact hXYD.trans (ih hXYD.hasType.2)

theorem LRS.CtorPath.append
    (H₁ : LRS.CtorPath Γ IH m X Y)
    (H₂ : LRS.CtorPath Γ IH m Y Z) :
    LRS.CtorPath Γ IH m X Z := by
  induction H₁ with
  | single link => exact .cons link H₂
  | cons link _ ih => exact .cons link (ih H₂)

theorem LRS.CtorPath.symm
    (H : LRS.CtorPath Γ IH m X Y) :
    LRS.CtorPath Γ IH m Y X := by
  induction H with
  | single link => exact .single link.symm
  | cons link _ ih => exact ih.append (.single link.symm)

theorem LRS.CtorPath.mono (hle : m' ≤ m)
    (H : LRS.CtorPath Γ IH m X Y) :
    LRS.CtorPath Γ IH m' X Y := by
  induction H with
  | single link => exact .single (link.mono hle)
  | cons link _ ih => exact .cons (link.mono hle) ih

theorem LRS.CtorPath.lift
    {IH : LogRel Γ n} {IH' : LogRel Γ n'} (le : n ≤ n')
    (E : LogRel.LiftEquiv IH IH' le)
    (H : LRS.CtorPath Γ IH m X Y) :
    LRS.CtorPath Γ IH' (m.lift (n' + 1)) X Y := by
  induction H with
  | single link => exact .single (link.lift le E)
  | cons link _ ih => exact .cons (link.lift le E) ih

theorem LRS.CtorPath.unlift
    {IH : LogRel Γ n} {IH' : LogRel Γ n'} (le : n ≤ n')
    (E : LogRel.LiftEquiv IH IH' le)
    (H : LRS.CtorPath Γ IH' (m.lift (n' + 1)) X Y) :
    LRS.CtorPath Γ IH m X Y := by
  induction H with
  | single link => exact .single (link.unlift le E)
  | cons link _ ih => exact .cons (link.unlift le E) ih

/-- Root-anchored constructor normal form.  The endpoint views isolate all
weak-head bookkeeping; the path between their classified spines consists
only of exact native links. -/
inductive LRS.CtorChain (Γ : List SExpr) (IH : LogRel Γ n)
    (M N : SExpr) (m : WShape (n + 1)) : Prop where
  | intro {X Y : SExpr} :
      LRS.CtorView Γ M X → LRS.CtorView Γ N Y →
      LRS.CtorPath Γ IH m X Y → CtorChain Γ IH M N m

theorem LRS.CtorChain.toCtorDefEq
    (H : LRS.CtorChain Γ IH M N m) :
    LRS.CtorDefEq Γ IH M N m := by
  cases H with
  | intro left right links =>
    cases left with
    | intro _ hM =>
    cases right with
      | intro _ hN => exact .unwhr hM hN links.toCtorDefEq

/-- Compose the raw equality of a normalized chain once its two weak-head
views have been certified at a common root type.  The callbacks are the
precise subject-reduction boundary: chain normalization and native-link
composition themselves do not inspect weak-head reductions. -/
theorem LRS.CtorChain.rawDefEqAt
    (uniq : LogRel.RawTypeUniq Γ)
    (H : LRS.CtorChain Γ IH M N m)
    (left : ∀ {X}, LRS.CtorView Γ M X → IsDefEq Γ M X D)
    (right : ∀ {Y}, LRS.CtorView Γ N Y → IsDefEq Γ N Y D) :
    IsDefEq Γ M N D := by
  cases H with
  | intro hleft hright path =>
    have hMX := left hleft
    have hNY := right hright
    exact hMX.trans (path.rawDefEqAt uniq hMX.hasType.2) |>.trans hNY.symm

/-- A normalized-chain consumer whose native leaves and root views have all
been retyped at one externally chosen domain.  This is the complete raw
boundary used by the joint adequacy/uniqueness proof: `foldRaw` spends raw
type uniqueness internally on path vertices, while the caller supplies
subject reduction only for the two weak-head root views. -/
structure LRS.CtorChain.RawAlgebra (Γ : List SExpr) (IH : LogRel Γ n)
    (m : WShape (n + 1)) (D : SExpr) (Q : SExpr → SExpr → Prop) where
  exact : ∀ {k : Nat} {J : LogRel Γ k} {p : WShape (k + 1)} {X Y : SExpr},
    LRS.CtorFrame Γ IH m J p → LRS.CtorExact Γ J X Y p →
    IsDefEq Γ X Y D → Q X Y
  trans : ∀ {X Y Z : SExpr}, Q X Y → Q Y Z → Q X Z
  anchor : ∀ {M N X Y : SExpr},
    LRS.CtorView Γ M X → LRS.CtorView Γ N Y →
    IsDefEq Γ M X D → IsDefEq Γ N Y D → Q X Y → Q M N

/-- Consume a root-anchored chain at one common raw domain.  No weak-head
subject-reduction theorem is hidden in this fold: its only two uses are the
explicit root callbacks. -/
theorem LRS.CtorChain.foldRaw
    (uniq : LogRel.RawTypeUniq Γ)
    (alg : LRS.CtorChain.RawAlgebra Γ IH m D Q)
    (H : LRS.CtorChain Γ IH M N m)
    (left : ∀ {X}, LRS.CtorView Γ M X → IsDefEq Γ M X D)
    (right : ∀ {Y}, LRS.CtorView Γ N Y → IsDefEq Γ N Y D) : Q M N := by
  cases H with
  | intro hleft hright path =>
    have hMX := left hleft
    have hNY := right hright
    let pathAlg : LRS.CtorPath.RawAlgebra Γ IH m D Q := {
      exact := alg.exact
      trans := alg.trans }
    exact alg.anchor hleft hright hMX hNY
      (path.foldRaw uniq pathAlg hMX.hasType.2)

/-- Consume a root-anchored chain with no raw type uniqueness anywhere.  The
only remaining raw inputs are the two root callbacks, i.e. weak-head subject
reduction *to a classified constructor spine* at the two endpoints — the one
half of the old residual that a redex's own stratified certificate bounds. -/
theorem LRS.CtorChain.foldRaw_of_anchorDiscipline
    (disc : LRS.CtorAnchorDisciplineAt Γ IH m)
    (alg : LRS.CtorChain.RawAlgebra Γ IH m D Q)
    (H : LRS.CtorChain Γ IH M N m)
    (left : ∀ {X}, LRS.CtorView Γ M X → IsDefEq Γ M X D)
    (right : ∀ {Y}, LRS.CtorView Γ N Y → IsDefEq Γ N Y D) : Q M N := by
  cases H with
  | intro hleft hright path =>
    have hMX := left hleft
    have hNY := right hright
    let pathAlg : LRS.CtorPath.RawAlgebra Γ IH m D Q := {
      exact := alg.exact
      trans := alg.trans }
    exact alg.anchor hleft hright hMX hNY
      (path.foldRaw_of_anchorDiscipline disc pathAlg hMX.hasType.2)

/-- Extract the raw equality of a normalized chain with no type
identification; the two root callbacks remain the only raw inputs. -/
theorem LRS.CtorChain.rawDefEqAt_of_anchorDiscipline
    (disc : LRS.CtorAnchorDisciplineAt Γ IH m)
    (H : LRS.CtorChain Γ IH M N m)
    (left : ∀ {X}, LRS.CtorView Γ M X → IsDefEq Γ M X D)
    (right : ∀ {Y}, LRS.CtorView Γ N Y → IsDefEq Γ N Y D) :
    IsDefEq Γ M N D := by
  cases H with
  | intro hleft hright path =>
    have hMX := left hleft
    have hNY := right hright
    exact hMX.trans
      (path.rawDefEqAt_of_anchorDiscipline disc hMX.hasType.2) |>.trans hNY.symm

theorem LRS.CtorChain.symm
    (H : LRS.CtorChain Γ IH M N m) :
    LRS.CtorChain Γ IH N M m := by
  cases H with
  | intro left right links => exact .intro right left links.symm

/-- Retain a constructor witness while making both root endpoints the left
endpoint.  A path followed by its mirror stays nonempty and therefore keeps
the observation evidence needed by later consumers. -/
theorem LRS.CtorChain.left
    (H : LRS.CtorChain Γ IH M N m) :
    LRS.CtorChain Γ IH M M m := by
  cases H with
  | intro left _ links => exact .intro left left (links.append links.symm)

/-- Concatenate two root-anchored chains.  Weak-head determinism identifies
the two classified constructor spines chosen for their shared root term. -/
theorem LRS.CtorChain.trans
    (H₁ : LRS.CtorChain Γ IH M N m)
    (H₂ : LRS.CtorChain Γ IH N P m) :
    LRS.CtorChain Γ IH M P m := by
  cases H₁ with
  | intro left middle₁ links₁ =>
    cases H₂ with
    | intro middle₂ right links₂ =>
      cases middle₁ with
      | intro hcl₁ hred₁ =>
        cases middle₂ with
        | intro hcl₂ hred₂ =>
          have hmid := WHRedS.ctorSpine_determ hcl₁ hcl₂ hred₁ hred₂
          exact .intro left right (links₁.append (hmid.symm ▸ links₂))

theorem LRS.CtorChain.mono (hle : m' ≤ m)
    (H : LRS.CtorChain Γ IH M N m) :
    LRS.CtorChain Γ IH M N m' := by
  cases H with
  | intro left right links => exact .intro left right (links.mono hle)

theorem LRS.CtorChain.whr
    (hM : WHRedS Γ M M') (hN : WHRedS Γ N N')
    (H : LRS.CtorChain Γ IH M N m) :
    LRS.CtorChain Γ IH M' N' m := by
  cases H with
  | intro left right links =>
    exact .intro (left.whr hM) (right.whr hN) links

theorem LRS.CtorChain.unwhr
    (hM : WHRedS Γ M M') (hN : WHRedS Γ N N')
    (H : LRS.CtorChain Γ IH M' N' m) :
    LRS.CtorChain Γ IH M N m := by
  cases H with
  | intro left right links =>
    exact .intro (left.unwhr hM) (right.unwhr hN) links

theorem LRS.CtorChain.lift
    {IH : LogRel Γ n} {IH' : LogRel Γ n'} (le : n ≤ n')
    (E : LogRel.LiftEquiv IH IH' le)
    (H : LRS.CtorChain Γ IH M N m) :
    LRS.CtorChain Γ IH' M N (m.lift (n' + 1)) := by
  cases H with
  | intro left right links => exact .intro left right (links.lift le E)

theorem LRS.CtorChain.unlift
    {IH : LogRel Γ n} {IH' : LogRel Γ n'} (le : n ≤ n')
    (E : LogRel.LiftEquiv IH IH' le)
    (H : LRS.CtorChain Γ IH' M N (m.lift (n' + 1))) :
    LRS.CtorChain Γ IH M N m := by
  cases H with
  | intro left right links => exact .intro left right (links.unlift le E)

/-- The elimination interface exposed by normalized constructor chains.
A consumer handles native exact leaves (with their full transport frame),
ordinary composition, and the two root views.  In particular it never sees
the original `left`/`symm`/`mono`/`lift`/`unlift` free closure. -/
structure LRS.CtorChain.Algebra (Γ : List SExpr) (IH : LogRel Γ n)
    (m : WShape (n + 1)) (Q : SExpr → SExpr → Prop) where
  exact : ∀ {k : Nat} {J : LogRel Γ k} {p : WShape (k + 1)} {X Y : SExpr},
    LRS.CtorFrame Γ IH m J p → LRS.CtorExact Γ J X Y p → Q X Y
  trans : ∀ {X Y Z : SExpr}, Q X Y → Q Y Z → Q X Z
  anchor : ∀ {M N X Y : SExpr},
    LRS.CtorView Γ M X → LRS.CtorView Γ N Y → Q X Y → Q M N

/-- Fold a nonempty exact-link path through the normalized consumer
interface. -/
theorem LRS.CtorPath.fold
    (alg : LRS.CtorChain.Algebra Γ IH m Q)
    (H : LRS.CtorPath Γ IH m X Y) : Q X Y := by
  induction H with
  | single link =>
    cases link with
    | intro frame exact => exact alg.exact frame exact
  | cons link _ ih =>
    cases link with
    | intro frame exact => exact alg.trans (alg.exact frame exact) ih

/-- Consume a root-anchored chain.  This is the intended entry point for the
limited-uniqueness-aware iota leaf: all transport choices remain local to
the exact link that introduced them. -/
theorem LRS.CtorChain.fold
    (alg : LRS.CtorChain.Algebra Γ IH m Q)
    (H : LRS.CtorChain Γ IH M N m) : Q M N := by
  cases H with
  | intro left right links => exact alg.anchor left right (links.fold alg)

/-- The original free constructor relation is one consumer of the normalized
interface.  This instance is also a sanity check that the algebra loses no
transport or endpoint evidence. -/
theorem LRS.CtorChain.defEqAlgebra :
    LRS.CtorChain.Algebra Γ IH m
      (fun X Y => LRS.CtorDefEq Γ IH X Y m) where
  exact frame leaf := frame.apply leaf.toCtorDefEq
  trans H₁ H₂ := H₁.trans H₂
  anchor left right H := by
    cases left with
    | intro _ hM =>
      cases right with
      | intro _ hN => exact .unwhr hM hN H

theorem LRS.CtorChain.fold_toCtorDefEq
    (H : LRS.CtorChain Γ IH M N m) :
    LRS.CtorDefEq Γ IH M N m :=
  H.fold LRS.CtorChain.defEqAlgebra

/-- Transport operations for an indexed result produced at a native exact
leaf.  Folding a `CtorFrame` applies these operations only after that leaf
has been completely consumed; no native field is projected through an
`unlift`. -/
structure LRS.CtorFrame.Algebra (Γ : List SExpr)
    (Q : {n : Nat} → LogRel Γ n → WShape (n + 1) →
      SExpr → SExpr → Prop) where
  mono : ∀ {n : Nat} {IH : LogRel Γ n} {m m' : WShape (n + 1)}
      {X Y : SExpr},
    m ≤ m' → Q IH m' X Y → Q IH m X Y
  lift : ∀ {n n' : Nat} {IH : LogRel Γ n} {IH' : LogRel Γ n'}
      {m : WShape (n + 1)} {X Y : SExpr},
    (le : n ≤ n') → LogRel.LiftEquiv IH IH' le →
    Q IH m X Y → Q IH' (m.lift (n' + 1)) X Y
  unlift : ∀ {n n' : Nat} {IH : LogRel Γ n} {IH' : LogRel Γ n'}
      {m : WShape (n + 1)} {X Y : SExpr},
    (le : n ≤ n') → LogRel.LiftEquiv IH IH' le →
    Q IH' (m.lift (n' + 1)) X Y → Q IH m X Y

/-- Consume a transport frame around an already completed native result. -/
theorem LRS.CtorFrame.fold
    (alg : LRS.CtorFrame.Algebra Γ Q)
    (F : LRS.CtorFrame Γ IH m J p)
    (H : Q J p X Y) : Q IH m X Y := by
  induction F with
  | refl => exact H
  | mono hle _ ih => exact alg.mono hle (ih H)
  | lift le E _ ih => exact alg.lift le E (ih H)
  | unlift le E _ ih => exact alg.unlift le E (ih H)

/-- A normalized-chain consumer split at the well-founded boundary: `exact`
works at the leaf's native level, `frame` returns its completed result to the
root, and `trans` composes only root-level results.  This is the interface on
which adequacy at level `n + 1` consumes limited uniqueness at level `n`. -/
structure LRS.CtorChain.NativeAlgebra (Γ : List SExpr)
    (Q : {n : Nat} → LogRel Γ n → WShape (n + 1) →
      SExpr → SExpr → Prop) where
  frame : LRS.CtorFrame.Algebra Γ Q
  exact : ∀ {n : Nat} {IH : LogRel Γ n} {m : WShape (n + 1)}
      {X Y : SExpr},
    LRS.CtorExact Γ IH X Y m → Q IH m X Y
  trans : ∀ {n : Nat} {IH : LogRel Γ n} {m : WShape (n + 1)}
      {X Y Z : SExpr},
    Q IH m X Y → Q IH m Y Z → Q IH m X Z
  anchor : ∀ {n : Nat} {IH : LogRel Γ n} {m : WShape (n + 1)}
      {M N X Y : SExpr},
    LRS.CtorView Γ M X → LRS.CtorView Γ N Y →
    Q IH m X Y → Q IH m M N

/-- Specialize an indexed native consumer to one root relation and shape. -/
theorem LRS.CtorChain.NativeAlgebra.atRoot
    (alg : LRS.CtorChain.NativeAlgebra Γ Q) :
    LRS.CtorChain.Algebra Γ IH m (Q IH m) where
  exact frame leaf := frame.fold alg.frame (alg.exact leaf)
  trans H₁ H₂ := alg.trans H₁ H₂
  anchor left right H := alg.anchor left right H

/-- Fold a normalized chain with native completion preceding root
composition. -/
theorem LRS.CtorChain.foldNative
    (alg : LRS.CtorChain.NativeAlgebra Γ Q)
    (H : LRS.CtorChain Γ IH M N m) : Q IH m M N :=
  H.fold alg.atRoot

/-- Normalize the free constructor-observation closure into a root-anchored
chain of native exact leaves. -/
theorem LRS.CtorDefEq.toChain
    (H : LRS.CtorDefEq Γ IH M N m) :
    LRS.CtorChain Γ IH M N m := by
  induction H with
  | exact hcl hlen hlen' hlevels hM hN hhead hhead' hspine hspine' hargs haligned
      hmirror =>
    exact .intro (.intro hcl hM)
      (.intro (by simpa [hlen, hlen'] using hcl) hN) <|
      .single <| .intro .refl <|
        .intro hcl hlen hlen' hlevels hhead hhead' hspine hspine'
          hargs haligned hmirror
  | left _ ih => exact ih.left
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | mono hle _ ih => exact ih.mono hle
  | whr hM hN _ ih => exact ih.whr hM hN
  | unwhr hM hN _ ih => exact ih.unwhr hM hN
  | lift le hliftTy hlift _ ih =>
    exact ih.lift le (.ofFields le hliftTy hlift)
  | unlift le hliftTy hlift _ ih =>
    exact ih.unlift le (.ofFields le hliftTy hlift)

/-- Extract a raw equality from the original free constructor-observation
closure through its normalized chain.  The caller-visible assumptions are
exactly those of `CtorChain.rawDefEqAt`; in particular no subject reduction
is smuggled into normalization. -/
theorem LRS.CtorDefEq.rawDefEqAt
    (uniq : LogRel.RawTypeUniq Γ)
    (H : LRS.CtorDefEq Γ IH M N m)
    (left : ∀ {X}, LRS.CtorView Γ M X → IsDefEq Γ M X D)
    (right : ∀ {Y}, LRS.CtorView Γ N Y → IsDefEq Γ N Y D) :
    IsDefEq Γ M N D :=
  H.toChain.rawDefEqAt uniq left right

/-- Consume the original free constructor relation through the raw-aware
normalized interface.  This is the intended adequacy entry point: callers
handle one framed native leaf, composition, and the two explicitly typed
root views rather than the nine constructors of `CtorDefEq`. -/
theorem LRS.CtorDefEq.foldRaw
    (uniq : LogRel.RawTypeUniq Γ)
    (alg : LRS.CtorChain.RawAlgebra Γ IH m D Q)
    (H : LRS.CtorDefEq Γ IH M N m)
    (left : ∀ {X}, LRS.CtorView Γ M X → IsDefEq Γ M X D)
    (right : ∀ {Y}, LRS.CtorView Γ N Y → IsDefEq Γ N Y D) : Q M N :=
  H.toChain.foldRaw uniq alg left right

/-- Consume the original free constructor relation with the per-leaf retyping
in place of raw type uniqueness.  Same conclusion and same root callbacks as
`CtorDefEq.foldRaw`; the interior of the chain now identifies no types. -/
theorem LRS.CtorDefEq.foldRaw_of_anchorDiscipline
    (disc : LRS.CtorAnchorDisciplineAt Γ IH m)
    (alg : LRS.CtorChain.RawAlgebra Γ IH m D Q)
    (H : LRS.CtorDefEq Γ IH M N m)
    (left : ∀ {X}, LRS.CtorView Γ M X → IsDefEq Γ M X D)
    (right : ∀ {Y}, LRS.CtorView Γ N Y → IsDefEq Γ N Y D) : Q M N :=
  H.toChain.foldRaw_of_anchorDiscipline disc alg left right

/-- Extract the raw equality of the original free constructor relation with no
type identification; caller-visible assumptions are the two root callbacks
alone. -/
theorem LRS.CtorDefEq.rawDefEqAt_of_anchorDiscipline
    (disc : LRS.CtorAnchorDisciplineAt Γ IH m)
    (H : LRS.CtorDefEq Γ IH M N m)
    (left : ∀ {X}, LRS.CtorView Γ M X → IsDefEq Γ M X D)
    (right : ∀ {Y}, LRS.CtorView Γ N Y → IsDefEq Γ N Y D) :
    IsDefEq Γ M N D :=
  H.toChain.rawDefEqAt_of_anchorDiscipline disc left right

/-- An algebra for consuming the free closure carried by `CtorDefEq`.

The transport operations consume an already folded result.  In particular,
`unlift` cannot inspect or project individual high-level constructor fields;
an algebra that returns a logical-relation continuation must first evaluate
that continuation at the higher level and then lower the completed result.
This is the sound elimination boundary needed by proof-carrying iota
materialization. -/
structure LRS.CtorDefEq.Algebra (Γ : List SExpr)
    (Q : {n : Nat} → LogRel Γ n → SExpr → SExpr → WShape (n + 1) → Prop) where
  exact : ∀ {n : Nat} {IH : LogRel Γ n} {c : Name}
      {rargs : List (WShape n)} {hwf} {M N : SExpr}
      {ls ls' : List SLevel} {args args' : List SExpr}
      {CHead CHead' A A' : SExpr},
      Params.classify c = some (.ctor args.length) →
      args.length = rargs.length → args'.length = rargs.length →
      ls = ls' →
      WHRedS Γ M (args.foldr (fun a f => f.app a) (.const c ls)) →
      WHRedS Γ N (args'.foldr (fun a f => f.app a) (.const c ls')) →
      IsDefEq Γ (.const c ls) (.const c ls) CHead →
      IsDefEq Γ (.const c ls') (.const c ls') CHead' →
      SExpr.SpineWF Γ CHead args.reverse A →
      SExpr.SpineWF Γ CHead' args'.reverse A' →
      LRS.CtorArgsDefEq IH args args' rargs →
      LRS.CtorSpineDefEq IH CHead args args' rargs A →
      LRS.CtorSpineDefEq IH CHead' args' args rargs A' →
      Q IH M N (.ctor c rargs.reverse hwf)
  left : ∀ {n : Nat} {IH : LogRel Γ n} {M N : SExpr} {m : WShape (n + 1)},
      Q IH M N m → Q IH M M m
  symm : ∀ {n : Nat} {IH : LogRel Γ n} {M N : SExpr} {m : WShape (n + 1)},
      Q IH M N m → Q IH N M m
  trans : ∀ {n : Nat} {IH : LogRel Γ n} {M N P : SExpr} {m : WShape (n + 1)},
      Q IH M N m → Q IH N P m → Q IH M P m
  mono : ∀ {n : Nat} {IH : LogRel Γ n} {M N : SExpr}
      {m m' : WShape (n + 1)},
      m ≤ m' → Q IH M N m' → Q IH M N m
  whr : ∀ {n : Nat} {IH : LogRel Γ n} {M M' N N' : SExpr}
      {m : WShape (n + 1)},
      WHRedS Γ M M' → WHRedS Γ N N' → Q IH M N m → Q IH M' N' m
  unwhr : ∀ {n : Nat} {IH : LogRel Γ n} {M M' N N' : SExpr}
      {m : WShape (n + 1)},
      WHRedS Γ M M' → WHRedS Γ N N' → Q IH M' N' m → Q IH M N m
  lift : ∀ {n n' : Nat} {IH : LogRel Γ n} {IH' : LogRel Γ n'}
      {M N : SExpr} {m : WShape (n + 1)},
      (le : n ≤ n') →
      (hliftTy : ∀ {A B : SExpr} {a : WShape n}, a.HasType .type →
        (IH'.TyDefEq A B (a.lift n') ↔ IH.TyDefEq A B a)) →
      (hlift : ∀ {M N A : SExpr} {m a : WShape n}, m.HasType a →
        (IH'.DefEq M N A (m.lift n') (a.lift n') ↔ IH.DefEq M N A m a)) →
      Q IH M N m → Q IH' M N (m.lift (n' + 1))
  unlift : ∀ {n n' : Nat} {IH : LogRel Γ n} {IH' : LogRel Γ n'}
      {M N : SExpr} {m : WShape (n + 1)},
      (le : n ≤ n') →
      (hliftTy : ∀ {A B : SExpr} {a : WShape n}, a.HasType .type →
        (IH'.TyDefEq A B (a.lift n') ↔ IH.TyDefEq A B a)) →
      (hlift : ∀ {M N A : SExpr} {m a : WShape n}, m.HasType a →
        (IH'.DefEq M N A (m.lift n') (a.lift n') ↔ IH.DefEq M N A m a)) →
      Q IH' M N (m.lift (n' + 1)) → Q IH M N m

/-- Fold a constructor observation through a transport-aware algebra. -/
theorem LRS.CtorDefEq.fold
    (alg : LRS.CtorDefEq.Algebra Γ Q)
    (H : LRS.CtorDefEq Γ IH M N m) : Q IH M N m := by
  induction H with
  | exact hcl hlen hlen' hlevels hM hN hhead hhead' hspine hspine' hargs haligned
      haligned' =>
    exact alg.exact hcl hlen hlen' hlevels hM hN hhead hhead' hspine hspine'
      hargs haligned haligned'
  | left _ ih => exact alg.left ih
  | symm _ ih => exact alg.symm ih
  | trans _ _ ih ih' => exact alg.trans ih ih'
  | mono hle _ ih => exact alg.mono hle ih
  | whr hM hN _ ih => exact alg.whr hM hN ih
  | unwhr hM hN _ ih => exact alg.unwhr hM hN ih
  | lift le hliftTy hlift _ ih => exact alg.lift le hliftTy hlift ih
  | unlift le hliftTy hlift _ ih => exact alg.unlift le hliftTy hlift ih

/-- Every transport-aware free-closure algebra induces a normalized native
consumer.  Structural `left`/`symm`/`whr` cases have already become exact
path operations and root views, so only exact completion, root composition,
root expansion, and the three frame operations remain. -/
theorem LRS.CtorDefEq.Algebra.toNative
    (alg : LRS.CtorDefEq.Algebra Γ Q) :
    LRS.CtorChain.NativeAlgebra Γ
      (fun IH m M N => Q IH M N m) where
  frame := {
    mono := fun hle H => alg.mono hle H
    lift := fun le E H => alg.lift le E.ty E.term H
    unlift := fun le E H => alg.unlift le E.ty E.term H }
  exact leaf := by
    cases leaf with
    | intro hcl hlen hlen' hlevels hhead hhead' hspine hspine' hargs haligned hmirror =>
      exact alg.exact hcl hlen hlen' hlevels .rfl .rfl hhead hhead' hspine hspine'
        hargs haligned hmirror
  trans H₁ H₂ := alg.trans H₁ H₂
  anchor left right H := by
    cases left with
    | intro _ hM =>
      cases right with
      | intro _ hN => exact alg.unwhr hM hN H

/-- The normalized route can consume every original constructor observation
through any existing algebra. -/
theorem LRS.CtorDefEq.foldChain
    (alg : LRS.CtorDefEq.Algebra Γ Q)
    (H : LRS.CtorDefEq Γ IH M N m) : Q IH M N m :=
  H.toChain.foldNative alg.toNative

def LRS.IndDefEq (Γ : List SExpr) (IH : LogRel Γ n)
    (M N A : SExpr) (m : WShape (n+1)) : Prop :=
  match m.1 with
  | .bot => True
  | _ => LRS.IndTyHead Γ A ∧ LRS.CtorDefEq Γ IH M N m

theorem LRS.IndDefEq.left :
    LRS.IndDefEq Γ IH M N A m → LRS.IndDefEq Γ IH M M A m := by
  dsimp [LRS.IndDefEq]; split <;> try trivial
  exact fun h => ⟨h.1, .left h.2⟩

theorem LRS.IndDefEq.symm :
    LRS.IndDefEq Γ IH M N A m → LRS.IndDefEq Γ IH N M A m := by
  dsimp [LRS.IndDefEq]; split <;> try trivial
  exact fun h => ⟨h.1, .symm h.2⟩

theorem LRS.IndDefEq.trans :
    LRS.IndDefEq Γ IH M₁ M₂ A m → LRS.IndDefEq Γ IH M₂ M₃ A m →
      LRS.IndDefEq Γ IH M₁ M₃ A m := by
  dsimp [LRS.IndDefEq]; split <;> try trivial
  exact fun h₁ h₂ => ⟨h₁.1, .trans h₁.2 h₂.2⟩

theorem LRS.IndDefEq.mono_l (le : m ≤ m') (hm : m.HasType WShape.indTy) :
    LRS.IndDefEq Γ IH M N A m' → LRS.IndDefEq Γ IH M N A m := by
  cases m using WShape.casesOn' with
  | bot => intro; trivial
  | ctor c l h =>
    have le' := le
    rw [WShape.ctor_le] at le'
    obtain ⟨l', h', rfl, _⟩ := le'
    intro hE
    exact ⟨hE.1, .mono le hE.2⟩
  | _ => cases hm

theorem LRS.IndDefEq.whr (hM : WHRedS Γ M M') (hN : WHRedS Γ N N') :
    LRS.IndDefEq Γ IH M N A m ↔ LRS.IndDefEq Γ IH M' N' A m := by
  dsimp [LRS.IndDefEq]; split
  · rfl
  · exact and_congr Iff.rfl (LRS.CtorDefEq.whr_iff hM hN)

theorem LRS.IndDefEq.lift {IH : LogRel Γ n} {IH' : LogRel Γ n'}
    {m : WShape (n+1)} (le : n ≤ n')
    (hliftTy : ∀ {A B : SExpr} {a : WShape n}, a.HasType .type →
      (IH'.TyDefEq A B (a.lift n') ↔ IH.TyDefEq A B a))
    (hlift : ∀ {M N A : SExpr} {m a : WShape n}, m.HasType a →
      (IH'.DefEq M N A (m.lift n') (a.lift n') ↔ IH.DefEq M N A m a)) :
    LRS.IndDefEq Γ IH' M N A (m.lift (n'+1)) ↔
      LRS.IndDefEq Γ IH M N A m := by
  cases m using WShape.casesOn' with
  | bot => rw [WShape.lift_bot]; exact Iff.rfl
  | sort r =>
    change (LRS.IndTyHead Γ A ∧ LRS.CtorDefEq Γ IH' M N
      ((WShape.sort r : WShape (n+1)).lift (n'+1))) ↔
      (LRS.IndTyHead Γ A ∧ LRS.CtorDefEq Γ IH M N (WShape.sort r))
    exact and_congr Iff.rfl (LRS.CtorDefEq.lift_iff le hliftTy hlift)
  | forallE b f =>
    have hc := LRS.CtorDefEq.lift_iff
      (M := M) (N := N) (m := WShape.forallE b f) le hliftTy hlift
    rw [WShape.lift_forallE le] at hc ⊢
    simpa only [LRS.IndDefEq, WShape.forallE] using
      (and_congr Iff.rfl hc)
  | lam f h =>
    have hc := LRS.CtorDefEq.lift_iff
      (M := M) (N := N) (m := WShape.lam f h) le hliftTy hlift
    rw [WShape.lift_lam le] at hc ⊢
    simpa only [LRS.IndDefEq, WShape.lam] using
      (and_congr Iff.rfl hc)
  | ctor c l h =>
    have hc := LRS.CtorDefEq.lift_iff
      (M := M) (N := N) (m := WShape.ctor c l h) le hliftTy hlift
    rw [WShape.lift_ctor le] at hc ⊢
    simpa only [LRS.IndDefEq, WShape.ctor] using
      (and_congr Iff.rfl hc)
  | indTy =>
    change (LRS.IndTyHead Γ A ∧ LRS.CtorDefEq Γ IH' M N
      ((WShape.indTy : WShape (n+1)).lift (n'+1))) ↔
      (LRS.IndTyHead Γ A ∧ LRS.CtorDefEq Γ IH M N WShape.indTy)
    exact and_congr Iff.rfl (LRS.CtorDefEq.lift_iff le hliftTy hlift)

/-- Type validity at element-shape `m` (merged `TyDefEq` / `EqTyDefEq`).
Non-trivial at `.forallE` (Pi injectivity) and `.sort` (sort injectivity). -/
def LRS.TyDefEq (IH : LogRel Γ n) (M N : SExpr) : WShape (n+1) → Prop
  | ⟨.bot, _⟩ | ⟨.lam _, _⟩ | ⟨.ctor _ _, _⟩ => True
  | ⟨.sort _, _⟩ => ∃ u, Γ ⊢ M ⤳* .sort u ∧ Γ ⊢ N ⤳* .sort u
  | ⟨.forallE b f, wf⟩ => LRS.ValTyPi2 IH M N ⟨b, wf.1⟩ ⟨f, wf.2⟩
  | ⟨.indTy, _⟩ => LRS.IndTyHead Γ M ∧ LRS.IndTyHead Γ N

@[simp] theorem LRS.TyDefEq.bot : LRS.TyDefEq IH M N .bot := trivial
@[simp] theorem LRS.TyDefEq.sort_iff :
    LRS.TyDefEq (Γ := Γ) IH M N (.sort r) ↔ ∃ u, Γ ⊢ M ⤳* .sort u ∧ Γ ⊢ N ⤳* .sort u := .rfl
@[simp] theorem LRS.TyDefEq.lam' : LRS.TyDefEq IH M N (.lam' f) := by
  unfold WShape.lam'; split <;> trivial
@[simp] theorem LRS.TyDefEq.ctor' : LRS.TyDefEq IH M N (.ctor' c l) := by
  unfold WShape.ctor'; split <;> trivial
@[simp] theorem LRS.TyDefEq.forallE_iff :
    LRS.TyDefEq (Γ := Γ) IH M N (.forallE b f) ↔ LRS.ValTyPi2 (Γ := Γ) IH M N b f := .rfl

theorem LRS.TyDefEq.left {IH : LogRel Γ n} :
    LRS.TyDefEq IH M N m → LRS.TyDefEq IH M M m := by
  dsimp [LRS.TyDefEq]; split <;> try trivial
  · intro ⟨u, hM, _⟩; exact ⟨u, hM, hM⟩
  · intro ⟨B₁, F₁, _, _, u, v, rM, _, hB, hF, hValB, hE⟩
    exact ⟨B₁, F₁, B₁, F₁, u, v, rM, rM, hB.left, hF.left,
      IH.left_ty hValB, hE.left⟩
  · intro h; exact ⟨h.1, h.1⟩

theorem LRS.TyDefEq.symm {IH : LogRel Γ n} :
    LRS.TyDefEq IH M N m → LRS.TyDefEq IH N M m := by
  dsimp [LRS.TyDefEq]; split <;> try trivial
  · intro ⟨u, hM, hN⟩; exact ⟨u, hN, hM⟩
  · intro ⟨_, _, _, _, _, _, rM, rN, hB, hF, hValB, hE1, hE2⟩
    have hValB' := IH.symm_ty hValB
    obtain ⟨u', hB'⟩ := hB.symm
    obtain ⟨v', hF'⟩ := hF.symm
    have hF'' := hB.defeqDF_l_path hF'
    refine ⟨_, _, _, _, u', v', rN, rM, hB', hF'',
      hValB', fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
    · let h := hE1 hp (hB'.defeqDF ha) (IH.conv hValB' a1)
      exact ⟨h.rightTy, h.leftTy, h.rightDefEq, h.leftDefEq⟩
    · exact IH.symm_ty (hE2 hp (hB'.defeqDF ha) (IH.conv hValB' a1))
  · exact And.symm

theorem LRS.TyDefEq.trans {IH : LogRel Γ n} :
    LRS.TyDefEq IH M₁ M₂ m → LRS.TyDefEq IH M₂ M₃ m → LRS.TyDefEq IH M₁ M₃ m := by
  dsimp [LRS.TyDefEq]; split <;> try trivial
  · intro ⟨u, hM₁, hM₂⟩ ⟨u', hM₂', hM₃⟩
    cases hM₂.determ .sort hM₂' .sort; exact ⟨u, hM₁, hM₃⟩
  · intro ⟨B₁, F₁, B₂, F₂, u, v, rM₁, rM₂, hB₁₂, hF₁₂, hValB₁₂, hE1⟩
          ⟨_, _, B₃, F₃, u', v', rM₂', rM₃, hB₂₃, hF₂₃, hValB₂₃, hE2⟩
    cases rM₂.determ .forallE rM₂' .forallE
    obtain ⟨_, hB₂₁⟩ := hB₁₂.symm
    have hF₂₃' := hB₂₁.defeqDF_l_path hF₂₃
    refine ⟨_, _, _, _, _, _, rM₁, rM₃,
      TypeDefEqPath.trans hB₁₂ hB₂₃, TypeDefEqPath.trans hF₁₂ hF₂₃',
      IH.trans_ty hValB₁₂ hValB₂₃, fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
    · let h₁ := hE1.1 hp ha a1
      let h₂ := hE2.1 hp (hB₁₂.defeqDF ha) (IH.conv hValB₁₂ a1)
      exact ⟨h₁.leftTy, h₂.rightTy, h₁.leftDefEq, h₂.rightDefEq⟩
    · exact IH.trans_ty (hE1.2 hp ha a1) (hE2.2 hp (hB₁₂.defeqDF ha) (IH.conv hValB₁₂ a1))
  · exact fun h₁ h₂ => ⟨h₁.1, h₂.2⟩

theorem LRS.LamDefEq.left {IH : LogRel Γ n} :
    LRS.LamDefEq IH M N B F m m₁ m₂ → LRS.LamDefEq IH M M B F m m₁ m₂ := by
  refine fun hP => ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
  · exact ⟨(hP.1 hp ha a1).1, (hP.1 hp ha a1).1⟩
  · exact (hP.1 hp ha a1).1

theorem LRS.LamDefEq.symm {IH : LogRel Γ n} :
    LRS.LamDefEq IH M N B F m m₁ m₂ → LRS.LamDefEq IH N M B F m m₁ m₂ := by
  refine fun hP => ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
  · exact ⟨(hP.1 hp ha a1).2, (hP.1 hp ha a1).1⟩
  · exact IH.symm (hP.2 hp ha a1)

theorem LRS.LamDefEq.trans {IH : LogRel Γ n} :
    LRS.LamDefEq IH M₁ M₂ B F m m₁ m₂ →
    LRS.LamDefEq IH M₂ M₃ B F m m₁ m₂ → LRS.LamDefEq IH M₁ M₃ B F m m₁ m₂ := by
  refine fun ⟨hP1, hP2⟩ ⟨hP1', hP2'⟩ => ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
  · exact ⟨(hP1 hp ha a1).1, (hP1' hp ha a1).2⟩
  · exact IH.trans (hP2 hp ha a1) (hP2' hp ha a1)

theorem LRS.PiDefEq.mono_r_2 {IH : LogRel Γ n}
    (le₁ : b ≤ b') (le₂ : f ≤ f')
    (htpi : WShape.HasTypePi f b r) (htpi' : WShape.HasTypePi f' b' r')
    (hValA₁ : IH.TyDefEq A₁ A₁ b') :
    LRS.PiDefEq IH A₁ A₂ B₂ b' f' → LRS.PiDefEq IH A₁ A₂ B₂ b f
  | ⟨h1, h2⟩ => by
    have htpi_w := WShape.HasTypePi.iff.1 htpi
    have htpi'_w := WShape.HasTypePi.iff.1 htpi'
    refine ⟨fun _ _ x hp ha a1 => ?_, fun _ x hp ha a1 => ?_⟩
    all_goals
      have hp' := WShape.HasType.mono_r le₁ (WShape.HasDom.isType htpi'.1) hp
      have a2 := IH.mono_r_1 le₁ hp hp' hValA₁ a1
      have hm_tgt := (htpi_w.2 _ hp).toType; have hm_src := (htpi'_w.2 _ hp').toType
    · let h := h1 hp' ha a2
      exact ⟨IH.mono_r_2_ty (WShapeFun.app_mono_l le₂ x) hm_tgt hm_src h.leftTy,
        IH.mono_r_2_ty (WShapeFun.app_mono_l le₂ x) hm_tgt hm_src h.rightTy,
        h.leftDefEq, h.rightDefEq⟩
    · exact IH.mono_r_2_ty (WShapeFun.app_mono_l le₂ x) hm_tgt hm_src (h2 hp' ha a2)

theorem LRS.LamDefEq.mono_r_2 {IH : LogRel Γ n}
    (le₁ : a₁ ≤ a₁') (le₂ : a₂ ≤ a₂') (hm : WShape.HasTypeLam m a₁ a₂)
    (hValA₁ : IH.TyDefEq A₁ A₁ a₁') (htpi' : WShape.HasTypePi a₂' a₁' r') :
    LRS.LamDefEq IH M N A₁ A₂ m a₁' a₂' → LRS.LamDefEq IH M N A₁ A₂ m a₁ a₂ := by
  have hm_w := WShape.HasTypeLam.iff.1 hm
  have htpi'_w := WShape.HasTypePi.iff.1 htpi'
  intro ⟨h1, h2⟩
  refine ⟨fun _ _ x hp ha a1 => ?_, fun _ x hp ha a1 => ?_⟩
  all_goals
    have hp' := WShape.HasType.mono_r le₁ (WShape.HasDom.isType htpi'.1) hp
    have a1' := IH.mono_r_1 le₁ hp hp' hValA₁ a1
    have hm_tgt := hm_w.2.2 _ hp
    have ht_src := (htpi'_w.2 _ hp').toType
  · have ⟨d1, d2⟩ := h1 hp' ha a1'
    exact ⟨IH.mono_r_2 (WShapeFun.app_mono_l le₂ x) hm_tgt ht_src d1,
           IH.mono_r_2 (WShapeFun.app_mono_l le₂ x) hm_tgt ht_src d2⟩
  · have q := h2 hp' ha a1'
    exact IH.mono_r_2 (WShapeFun.app_mono_l le₂ _) hm_tgt ht_src q

/-- Monotonicity of `LamDefEq` in the element-shape: decrease. -/
theorem LRS.LamDefEq.mono_l {IH : LogRel Γ n}
    (le : m ≤ m') (hm : WShape.HasTypeLam m a₁ a₂)
    (hm' : WShape.HasTypeLam m' a₁ a₂) :
    LRS.LamDefEq IH M N A₁ A₂ m' a₁ a₂ → LRS.LamDefEq IH M N A₁ A₂ m a₁ a₂ := by
  have hm_w := WShape.HasTypeLam.iff.1 hm
  have hm'_w := WShape.HasTypeLam.iff.1 hm'
  intro ⟨pav, pae⟩
  refine ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
  all_goals
    have hm_tgt := hm_w.2.2 _ hp
    have hm_src := hm'_w.2.2 _ hp
  · have ⟨d1, d2⟩ := pav hp ha a1
    exact ⟨IH.mono_l (WShapeFun.app_mono_l le _) hm_tgt hm_src d1,
           IH.mono_l (WShapeFun.app_mono_l le _) hm_tgt hm_src d2⟩
  · have q := pae hp ha a1
    exact IH.mono_l (WShapeFun.app_mono_l le _) hm_tgt hm_src q

/-- Join of `PiDefEq`: given edge validity at `(b₁, f₁)` and `(b₂, f₂)`,
produce edge validity at `(b₁.join b₂, f₁.join f₂)`.
Follows the same representative-based strategy as old `LRS.join`. -/
theorem LRS.PiDefEq.join {IH : LogRel Γ n}
    (htB₁ : b₁.HasType .type) (htB₂ : b₂.HasType .type)
    (hC_b : b₁.Compat b₂)
    (ht₁ : WShape.HasTypePi f₁ b₁ r₁) (ht₂ : WShape.HasTypePi f₂ b₂ r₂)
    (hC_f : WShapeFun.Compat f₁ f₂)
    (hE₁ : LRS.PiDefEq IH B₁ F₁ F₂ b₁ f₁)
    (hE₂ : LRS.PiDefEq IH B₁ F₁ F₂ b₂ f₂) :
    LRS.PiDefEq IH B₁ F₁ F₂ (b₁.join b₂) (f₁.join f₂) := by
  have hJ_b := WShape.Join.mk hC_b
  have htB_join := htB₁.join hC_b htB₂
  have hJ_f := WShapeFun.Join.mk hC_f
  have ht₁_w := WShape.HasTypePi.iff.1 ht₁
  have ht₂_w := WShape.HasTypePi.iff.1 ht₂
  have hd₁ := WShape.HasDom.iff.1 ht₁.1
  have hd₂ := WShape.HasDom.iff.1 ht₂.1
  refine ⟨fun _ _ p hp ha a1 => ?_, fun _ p hp ha a1 => ?_⟩
  all_goals
    obtain ⟨d_x, d_le, d_ht, d_app⟩ := hd₁ p
    have c2 := IH.mono_r_2 hJ_b.le.1 d_ht htB_join
      (IH.mono_l d_le (WShape.HasType.mono_r hJ_b.le.1 htB_join d_ht) hp a1)
    obtain ⟨e_x, e_le, e_ht, e_app⟩ := hd₂ p
    have c3 := IH.mono_r_2 hJ_b.le.2 e_ht htB_join
      (IH.mono_l e_le (WShape.HasType.mono_r hJ_b.le.2 htB_join e_ht) hp a1)
    have ht_f1 : (f₁.app p).HasType .type :=
      have ⟨_, _, hm⟩ := f₁.app_eq p; (ht₁.2 _ _ hm).toType
    have ht_f2 : (f₂.app p).HasType .type :=
      have ⟨_, _, hm⟩ := f₂.app_eq p; (ht₂.2 _ _ hm).toType
    have hJ_fp := hJ_f.app_l p
    have ⟨hC_fp, _, hC_fJ⟩ := WShape.Join.iff.1 hJ_fp
    have ht_fJ := ht_f1.join' hJ_fp ht_f2
    have ht_fJ' := ht_f1.join hC_fp ht_f2
    have cvt_d {A B} (h : IH.TyDefEq A B (f₁.app d_x)) : IH.TyDefEq A B (f₁.app p) :=
      IH.mono_r_2_ty d_app ht_f1 (ht₁_w.2 d_x d_ht).toType h
    have cvt_e {A B} (h : IH.TyDefEq A B (f₂.app e_x)) : IH.TyDefEq A B (f₂.app p) :=
      IH.mono_r_2_ty e_app ht_f2 (ht₂_w.2 e_x e_ht).toType h
  · let hd := hE₁.1 d_ht ha c2
    let he := hE₂.1 e_ht ha c3
    exact ⟨
      IH.mono_r_2_ty hC_fJ ht_fJ ht_fJ' <| IH.join_ty hC_fp ht_f1 ht_f2
        (cvt_d hd.leftTy) (cvt_e he.leftTy),
      IH.mono_r_2_ty hC_fJ ht_fJ ht_fJ' <| IH.join_ty hC_fp ht_f1 ht_f2
        (cvt_d hd.rightTy) (cvt_e he.rightTy),
      hd.leftDefEq, hd.rightDefEq⟩
  · exact IH.mono_r_2_ty hC_fJ ht_fJ ht_fJ' <| IH.join_ty hC_fp ht_f1 ht_f2
      (cvt_d (hE₁.2 d_ht ha c2)) (cvt_e (hE₂.2 e_ht ha c3))

/-- Head reduction on M, N preserves `LamDefEq`. Uses `IH.whr` (with `WHRed.app`)
to transport the inner `IH.DefEq` terms. HasType is preserved trivially (doesn't mention M, N). -/
theorem LRS.LamDefEq.whr {IH : LogRel Γ n}
    (hM : Γ ⊢ M ⤳* M') (hN : Γ ⊢ N ⤳* N') :
    LRS.LamDefEq IH M N A₁ A₂ m a₁ a₂ ↔ LRS.LamDefEq IH M' N' A₁ A₂ m a₁ a₂ := by
  constructor <;> intro ⟨pav, pae⟩ <;> refine ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩
  · have ⟨d1, d2⟩ := pav hp ha a1
    exact ⟨(IH.whr (.app hM) (.app hM)).1 d1, (IH.whr (.app hN) (.app hN)).1 d2⟩
  · exact (IH.whr (.app hM) (.app hN)).1 (pae hp ha a1)
  · have ⟨d1, d2⟩ := pav hp ha a1
    exact ⟨(IH.whr (.app hM) (.app hM)).2 d1, (IH.whr (.app hN) (.app hN)).2 d2⟩
  · exact (IH.whr (.app hM) (.app hN)).2 (pae hp ha a1)

/-- Term validity at `(m, a)`. -/
def LRS.DefEq (IH : LogRel Γ n) (M N A : SExpr) (m a : WShape (n+1)) : Prop :=
  match ha : a.1 with
  | .bot => True
  | .sort _ => LRS.TyDefEq IH M N m
  | .forallE a₁ a₂ =>
    have wfa1 := (ha ▸ a.2).1; have wfa2 := (ha ▸ a.2).2
    match hm : m.1 with
    | .bot => True
    | .lam mg =>
      ∃ A₁ A₂ u v, Γ ⊢ A ⤳* .forallE A₁ A₂ ∧
      Γ ⊢ A₁ : .sort u ∧ IH.TyDefEq A₁ A₁ ⟨a₁, wfa1⟩ ∧ A₁::Γ ⊢ A₂ : sort v ∧
      LRS.PiDefEq IH A₁ A₂ A₂ ⟨a₁, wfa1⟩ ⟨a₂, wfa2⟩ ∧
      LRS.LamDefEq IH M N A₁ A₂ ⟨mg, (hm ▸ m.2).1⟩ ⟨a₁, wfa1⟩ ⟨a₂, wfa2⟩
    | _ => False
  | .indTy => LRS.IndDefEq Γ IH M N A m
  | _ => False

@[simp] theorem LRS.DefEq.bot_a : LRS.DefEq IH M N A m .bot = True := rfl
@[simp] theorem LRS.DefEq.sort_a : LRS.DefEq IH M N A m (.sort r) = LRS.TyDefEq IH M N m := rfl
@[simp] theorem LRS.DefEq.bot_m : LRS.DefEq IH M N A .bot (.forallE a₁ a₂) = True := rfl
@[simp] theorem LRS.DefEq.lam_forallE (IH : LogRel Γ n) :
    LRS.DefEq IH M N A (.lam f hf) (.forallE a₁ a₂) ↔
    (∃ A₁ A₂ u v, Γ ⊢ A ⤳* .forallE A₁ A₂ ∧
      Γ ⊢ A₁ : .sort u ∧ IH.TyDefEq A₁ A₁ a₁ ∧ A₁::Γ ⊢ A₂ : sort v ∧
      LRS.PiDefEq IH A₁ A₂ A₂ a₁ a₂ ∧
      LRS.LamDefEq IH M N A₁ A₂ f a₁ a₂) := by
  show (∃ A₁ A₂ u v, _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ LRS.LamDefEq IH _ _ _ _ ⟨_, _⟩ ⟨_, _⟩ ⟨_, _⟩) ↔ _
  simp only [Subtype.eta]
@[simp] theorem LRS.DefEq.sort_forallE :
    LRS.DefEq IH M N A (.sort r) (.forallE a₁ a₂) ↔ False := .rfl
@[simp] theorem LRS.DefEq.forallE_forallE :
    LRS.DefEq IH M N A (.forallE b g) (.forallE a₁ a₂) ↔ False := .rfl
@[simp] theorem LRS.DefEq.ctor_forallE :
    LRS.DefEq IH M N A (.ctor c l h) (.forallE a₁ a₂) ↔ False := .rfl
@[simp] theorem LRS.DefEq.indTy_forallE :
    LRS.DefEq IH M N A .indTy (.forallE a₁ a₂) ↔ False := .rfl
@[simp] theorem LRS.DefEq.lam_a : LRS.DefEq IH M N A m (.lam f hf) ↔ False := .rfl
@[simp] theorem LRS.DefEq.ctor_a {c l h} :
    LRS.DefEq (n := n) IH M N A m (.ctor c l h) ↔ False := .rfl
@[simp] theorem LRS.TyDefEq.lam_m : LRS.TyDefEq IH M N (.lam f hf) ↔ True := .rfl
@[simp] theorem LRS.TyDefEq.ctor_m {c l h} :
    LRS.TyDefEq (n := n) IH M N (.ctor c l h) ↔ True := .rfl
@[simp] theorem LRS.TyDefEq.indTy_m :
    LRS.TyDefEq (n := n) (Γ := Γ) IH M N .indTy ↔
      LRS.IndTyHead Γ M ∧ LRS.IndTyHead Γ N := by
  rfl
@[simp] theorem LRS.DefEq.indTy_a :
    LRS.DefEq (n := n) (Γ := Γ) IH M N A m .indTy ↔
      LRS.IndDefEq Γ IH M N A m := by
  rfl

def LRS (IH : LogRel Γ n) : LogRel Γ (n+1) where
  DefEq := LRS.DefEq IH
  TyDefEq := LRS.TyDefEq IH
  sort_iff := .rfl
  sort_iff_ty := .rfl
  bot ha := by cases ha.unfold <;> trivial
  left_ty := .left
  left {M N A m a} := by
    dsimp [LRS.DefEq]; split <;> try trivial
    · exact .left
    · cases m using WShape.casesOn' with | lam => ?_ | _ => exact id
      intro ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, hP⟩
      exact ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, hP.left⟩
    · exact LRS.IndDefEq.left
  symm_ty := .symm
  symm {M N A m a} := by
    dsimp [LRS.DefEq]; split <;> try trivial
    · exact .symm
    · cases m using WShape.casesOn' with | lam => ?_ | _ => exact id
      intro ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, hP⟩
      exact ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, hP.symm⟩
    · exact LRS.IndDefEq.symm
  trans_ty := .trans
  trans {M₁ M₂ A m a M₃} := by
    dsimp [LRS.DefEq]; split <;> try trivial
    · exact .trans
    · split <;> try trivial
      intro ⟨B, F, u, v, rA, hA1, hA2, hA₂, hE, hP⟩ ⟨_, _, _, _, rA', _, _, _, _, hP'⟩
      cases rA.determ .forallE rA' .forallE
      exact ⟨_, _, _, _, rA, hA1, hA2, hA₂, hE, hP.trans hP'⟩
    · exact LRS.IndDefEq.trans
  trans' {A₁ A₂ u a s A₃ v r} := by
    dsimp [LRS.DefEq]; split <;> try intros; trivial
    · exact .trans
    · split <;> try intros; trivial
      intro ⟨_, _, _, _, rA, _⟩; cases WHNF.sort.whRedS rA
    · intro h _
      cases a using WShape.casesOn' with
      | bot => trivial
      | _ => exact h.1.not_sort.elim
  conv {A A' a M N m} := by
    cases a using WShape.casesOn' with
    | bot => intro _; exact id
    | sort => intro _; exact id
    | forallE a₁ a₂ =>
      simp only [LRS.TyDefEq.forallE_iff]
      intro ⟨B, F, B', F', u, v, rA, rA', hBB', hFF', hValB, hEdge⟩
      cases m using WShape.casesOn' with | lam => ?_ | _ => exact id
      simp only [LRS.DefEq.lam_forallE]
      intro ⟨_, _, _, v', rA₁, hA1, hValA, hA₂, hEdge₁, hP⟩
      cases rA.determ .forallE rA₁ .forallE
      obtain ⟨u', hB'⟩ := hBB'.rightType
      obtain ⟨v'', hF'⟩ := hFF'.rightType
      obtain ⟨_, hBBsymm⟩ := hBB'.symm
      refine ⟨_, _, u', v'', rA', hB', IH.left_ty (IH.symm_ty hValB),
        hBB'.defeqDF_l hF', ?_, ?_⟩
      · refine ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩ <;>
          have ha' := hBBsymm.defeqDF ha
        · let h := hEdge.1 hp ha' (IH.conv (IH.symm_ty hValB) a1)
          exact ⟨h.rightTy, h.rightTy, h.rightDefEq, h.rightDefEq⟩
        · exact (hEdge.1 hp ha' (IH.conv (IH.symm_ty hValB) a1)).rightTy
      refine ⟨fun _ _ _ hp ha a1 => ?_, fun _ _ hp ha a1 => ?_⟩ <;> (
        have a2 := IH.conv (IH.symm_ty hValB) a1
        have ha' := hBBsymm.defeqDF ha
        have c := hEdge.2 hp ha'.hasType.1 (IH.left a2))
      · have ⟨v1, v2⟩ := hP.1 hp ha' a2; exact ⟨IH.conv c v1, IH.conv c v2⟩
      · exact IH.conv c (hP.2 hp ha' a2)
    | indTy =>
      intro hTy hE
      cases m using WShape.casesOn' with
      | bot => trivial
      | _ =>
        exact ⟨hTy.2, hE.2⟩
    | _ => intro _; exact id
  toType := id
  mono_r_2 {a a' M N A m} le hm ht h := by
    cases a using WShape.casesOn' with
    | bot => trivial
    | sort => cases WShape.sort_le.1 le; exact h
    | forallE a₁ a₂ =>
      obtain ⟨a₁', a₂', le1, le2, rfl⟩ := WShape.forallE_le.1 le
      cases m using WShape.casesOn' with
      | bot => simp [LRS.DefEq.bot_m]
      | lam f hf =>
        simp only [LRS.DefEq.lam_forallE] at h ⊢
        have ⟨_, hp, _⟩ := WShape.HasType.forallE_l.1 hm.isType
        have ⟨_, hp', _⟩ := WShape.HasType.forallE_l.1 ht
        obtain ⟨g, hg, hm'⟩ := WShape.HasType.forallE_inv hm
        have hgf : g = f := by
          have := congrArg (·.1) hg; simp only [WShape.lam, WShape.lam'] at this
          split at this
          · injection this with this; exact WShapeFun.ext this.symm
          · cases this
        subst hgf
        let ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hEdge, hP⟩ := h
        have ht := (WShape.HasTypePi.iff.1 hp).1.isType
        have ht' := (WShape.HasTypePi.iff.1 hp').1.isType
        refine ⟨A₁, A₂, u, v, rA, hA1, IH.mono_r_2_ty le1 ht ht' hA2, hA₂, ?_⟩
        exact ⟨hEdge.mono_r_2 le1 le2 hp hp' hA2, hP.mono_r_2 le1 le2 hm' hA2 hp'⟩
      | sort => simp [LRS.DefEq.sort_forallE] at h
      | forallE => simp [LRS.DefEq.forallE_forallE] at h
      | ctor => simp [LRS.DefEq.ctor_forallE] at h
      | indTy => simp [LRS.DefEq.indTy_forallE] at h
    | lam f hf => exact absurd hm.isType WShape.HasType.lam_isType
    | ctor => exact absurd hm.isType WShape.HasType.ctor_isType
    | indTy =>
      cases WShape.indTy_le.1 le
      exact h
  mono_r_2_ty {a a' A B} le ha ha' h := by
    cases a using WShape.casesOn' with
    | bot => trivial
    | sort => simp [LRS.TyDefEq] at h ⊢; cases WShape.sort_le.1 le; exact h
    | forallE a₁ a₂ =>
      simp [LRS.TyDefEq] at h ⊢
      obtain ⟨a₁', a₂', le1, le2, rfl⟩ := WShape.forallE_le.1 le
      have ⟨_, hp, _⟩ := WShape.HasType.forallE_l.1 ha
      have ⟨_, hp', _⟩ := WShape.HasType.forallE_l.1 ha'
      let ⟨B₁, F₁, B₂, F₂, u, v, rA, rB, hBB', hFF', hValB, hEdge⟩ := h
      have ht := (WShape.HasTypePi.iff.1 hp).1.isType
      have ht' := (WShape.HasTypePi.iff.1 hp').1.isType
      refine ⟨B₁, F₁, B₂, F₂, u, v, rA, rB, hBB', hFF', IH.mono_r_2_ty le1 ht ht' hValB, ?_⟩
      exact hEdge.mono_r_2 le1 le2 hp hp' (IH.left_ty hValB)
    | lam f hf => simp [LRS.TyDefEq.lam_m]
    | ctor => simp [LRS.TyDefEq.ctor_m]
    | indTy =>
      cases WShape.indTy_le.1 le
      exact h
  mono_r_1 {a a' A M N m} le ha ha' hA h := by
    cases a' using WShape.casesOn' with
    | bot => simp only [LRS.DefEq.bot_a]
    | sort r =>
      obtain rfl | rfl := WShape.le_sort.1 le
      · have := ha.bot_r; subst this; simp only [LRS.DefEq.sort_a, LRS.TyDefEq.bot]
      · exact h
    | forallE a₁' a₂' =>
      obtain rfl | ⟨a₁, a₂, rfl, le1, le2⟩ := WShape.le_forallE_iff.1 le
      · have := ha.bot_r; subst this; simp only [LRS.DefEq.bot_m]
      · cases m using WShape.casesOn' with
        | bot => simp only [LRS.DefEq.bot_m]
        | lam f hf =>
          simp only [LRS.DefEq.lam_forallE] at h ⊢
          obtain ⟨g, hg, hm_lam⟩ := WShape.HasType.forallE_inv ha
          have hgf' : (WShape.lam f hf).1 = (WShape.lam' g).1 := congrArg (·.1) hg
          simp only [WShape.lam, WShape.lam'] at hgf'; split at hgf'
          · injection hgf' with hgf'
            have := WShapeFun.ext hgf'.symm; subst this  -- now f = g
            obtain ⟨g', hg', hm'_lam⟩ := WShape.HasType.forallE_inv ha'
            have hgf2 : (WShape.lam g hf).1 = (WShape.lam' g').1 := congrArg (·.1) hg'
            simp only [WShape.lam, WShape.lam'] at hgf2; split at hgf2
            · injection hgf2 with hgf2; have := WShapeFun.ext hgf2.symm; subst this
              let ⟨A₁, A₂, u, v, rA, hA1, hValA, hA₂, hEdge_src, hP⟩ := h
              let ⟨B₁, F₁, B₂, F₂, u', v', rA', rA'', hBB_tgt, hFF_tgt, hValB_tgt, hEdge_tgt⟩ := hA
              cases rA.determ .forallE rA' .forallE
              cases rA.determ .forallE rA'' .forallE
              refine ⟨_, _, _, _, rA, hBB_tgt.leftType, hValB_tgt, hA₂, hEdge_tgt, ?_⟩
              exact hP.mono_r_1 le1 le2 hm_lam hm'_lam hEdge_tgt
            · cases hgf2
          · cases hgf'
        | sort => exact (LRS.DefEq.sort_forallE.1 h).elim
        | forallE => exact (LRS.DefEq.forallE_forallE.1 h).elim
        | ctor => exact (LRS.DefEq.ctor_forallE.1 h).elim
        | indTy => exact (LRS.DefEq.indTy_forallE.1 h).elim
    | lam f hf => exact absurd ha'.isType WShape.HasType.lam_isType
    | ctor => exact absurd ha'.isType WShape.HasType.ctor_isType
    | indTy =>
      obtain rfl | rfl := WShape.le_indTy.1 le
      · have hm0 := ha.bot_r; subst m
        trivial
      · exact h
  mono_l {m m' M N A a} le hm hm' h := by
    cases a using WShape.casesOn' with
    | bot => simp only [LRS.DefEq.bot_a]
    | sort r =>
      simp only [LRS.DefEq.sort_a] at h ⊢
      cases m using WShape.casesOn' with
      | bot => simp only [LRS.TyDefEq.bot]
      | sort => cases WShape.sort_le.1 le; exact h
      | forallE s f =>
        simp only [LRS.TyDefEq.forallE_iff] at ⊢
        obtain ⟨s', f', h1, h2, rfl⟩ := WShape.forallE_le.1 le
        simp only [LRS.TyDefEq.forallE_iff] at h ⊢
        have ⟨_, hm_pi, _⟩ := WShape.HasType.forallE_l.1 hm
        have ⟨_, hm'_pi, _⟩ := WShape.HasType.forallE_l.1 hm'
        let ⟨B₁, F₁, B₂, F₂, u, v, rM, rN, hBB', hFF', hValB, hEdge⟩ := h
        have ht := (WShape.HasTypePi.iff.1 hm_pi).1.isType
        have ht' := (WShape.HasTypePi.iff.1 hm'_pi).1.isType
        exact ⟨B₁, F₁, B₂, F₂, u, v, rM, rN, hBB', hFF', IH.mono_r_2_ty h1 ht ht' hValB,
          hEdge.mono_r_2 h1 h2 hm_pi hm'_pi (IH.left_ty hValB)⟩
      | lam => simp only [LRS.TyDefEq.lam_m]
      | ctor => simp only [LRS.TyDefEq.ctor_m]
      | indTy =>
        cases WShape.indTy_le.1 le
        exact h
    | forallE a₁ a₂ =>
      cases m using WShape.casesOn' with
      | bot => simp only [LRS.DefEq.bot_m]
      | lam f hf =>
        obtain ⟨g, hg, hm_lam⟩ := WShape.HasType.forallE_inv hm
        have hgf' : (WShape.lam f hf).1 = (WShape.lam' g).1 := congrArg (·.1) hg
        simp only [WShape.lam, WShape.lam'] at hgf'; split at hgf'
        · injection hgf' with hgf'; have := WShapeFun.ext hgf'.symm; subst this
          obtain ⟨g'', hg'', hm'_lam⟩ := WShape.HasType.forallE_inv hm'
          rw [hg''] at h
          by_cases hg''nz : g''.NonZero
          · rw [show WShape.lam' g'' = WShape.lam g'' hg''nz from
              (WShape.lam_eq_lam' (hl := hg''nz)).symm] at h
            simp only [LRS.DefEq.lam_forallE] at h ⊢
            rw [WShape.lam_eq_lam' (hl := hf), hg''] at le
            have le_g := WShape.lam'_le_lam'.1 le
            let ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, hP⟩ := h
            exact ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, hP.mono_l le_g hm_lam hm'_lam⟩
          · simp only [WShape.lam', dif_neg hg''nz] at hg''
            cases WShape.le_bot.1 (hg'' ▸ le)
        · cases hgf'
      | _ => cases hm
    | indTy => exact h.mono_l le hm
    | _ => cases hm.isType
  join_ty {A B m₁ m₂} hC hm₁ hm₂ h1 h2 := by
    cases hm₁.unfold with
    | bot h₁ => rwa [WShape.bot_join]
    | sort =>
      cases hm₂.unfold with
      | bot => rwa [WShape.join_bot]
      | sort =>
        simp only [WShape.sort_join_sort] at h1 h2 ⊢
        split <;> simp_all only [LRS.TyDefEq.sort_iff, WShape.Compat.sort_sort]
      | _ => cases hC
    | forallE hp₁ =>
      cases hm₂.unfold with | bot => rwa [WShape.join_bot] | forallE hp₂ => ?_ | _ => cases hC
      simp only [LRS.TyDefEq.forallE_iff] at h1 h2
      simp [WShape.Compat, WShape.forallE, Shape.Compat] at hC
      let ⟨B₁, F₁, B₂, F₂, u, v, rA, rB, hBB, hFF, hValB₁, hEdge₁⟩ := h1
      let ⟨_, _, _, _, u', v', rA', rB', hBB', hFF', hValB₂, hEdge₂⟩ := h2
      cases rA.determ .forallE rA' .forallE
      cases rB.determ .forallE rB' .forallE
      simp only [LRS.TyDefEq.forallE_iff, WShape.forallE_join_forallE hC.1 hC.2]
      have ht₁ := (WShape.HasTypePi.iff.1 hp₁).1.isType
      have ht₂ := (WShape.HasTypePi.iff.1 hp₂).1.isType
      refine ⟨B₁, F₁, B₂, F₂, u, v, rA, rB, hBB, hFF, IH.join_ty hC.1 ht₁ ht₂ hValB₁ hValB₂, ?_⟩
      exact .join ht₁ ht₂ hC.1 hp₁ hp₂ hC.2 hEdge₁ hEdge₂
    | indTy =>
      cases hm₂.unfold with
      | bot => rwa [WShape.join_bot]
      | indTy => exact ⟨h1.1, h2.2⟩
      | _ => cases hC
  whr {M M' N N' A m a} hM hN := by
    cases a using WShape.casesOn' with
    | sort =>
      cases m using WShape.casesOn' with
      | sort =>
        constructor <;> intro ⟨u, r1, r2⟩
        · exact ⟨u, hM.determ_l r1 .sort, hN.determ_l r2 .sort⟩
        · exact ⟨u, .trans hM r1, .trans hN r2⟩
      | forallE =>
        constructor <;> intro ⟨B₁, F₁, B₂, F₂, u, v, rM, rN, rest⟩
        · exact ⟨B₁, F₁, B₂, F₂, u, v, hM.determ_l rM .forallE, hN.determ_l rN .forallE, rest⟩
        · exact ⟨B₁, F₁, B₂, F₂, u, v, .trans hM rM, .trans hN rN, rest⟩
      | indTy => exact and_congr (LRS.IndTyHead.whr hM) (LRS.IndTyHead.whr hN)
      | _ => rfl
    | forallE =>
      cases m using WShape.casesOn' with | lam => ?_ | _ => rfl
      constructor <;> intro ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, hP⟩
      · exact ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, (LRS.LamDefEq.whr hM hN).1 hP⟩
      · exact ⟨A₁, A₂, u, v, rA, hA1, hA2, hA₂, hE, (LRS.LamDefEq.whr hM hN).2 hP⟩
    | indTy => exact LRS.IndDefEq.whr hM hN
    | _ => rfl
  whr_ty {A A' B B' m} hA hB := by
    cases m using WShape.casesOn' with
    | sort =>
      constructor <;> intro ⟨u, r1, r2⟩
      · exact ⟨u, hA.determ_l r1 .sort, hB.determ_l r2 .sort⟩
      · exact ⟨u, .trans hA r1, .trans hB r2⟩
    | forallE =>
      constructor <;> intro ⟨B₁, F₁, B₂, F₂, u, v, rM, rN, rest⟩
      · exact ⟨B₁, F₁, B₂, F₂, u, v, hA.determ_l rM .forallE, hB.determ_l rN .forallE, rest⟩
      · exact ⟨B₁, F₁, B₂, F₂, u, v, .trans hA rM, .trans hB rN, rest⟩
    | indTy => exact and_congr (LRS.IndTyHead.whr hA) (LRS.IndTyHead.whr hB)
    | _ => rfl

def LR (Γ : List SExpr) : LogRel Γ n :=
  match n with
  | 0 => LR0
  | _+1 => LRS (LR Γ)

@[simp] theorem LR_zero : LR (n := 0) Γ = LR0 := rfl
@[simp] theorem LR_succ : LR (n := n+1) Γ = LRS (LR Γ) := rfl

/-- The only non-structural case in successor-level semantic retyping.

For bottom, sort, Pi, constructor, and inductive-type element shapes, the
result type either is not inspected by `LRS.DefEq` or its required head is
already supplied by type validity.  A lambda observation is different: its
two typings may expose different Pi shapes, so transporting the stored
`LamDefEq` package requires the merged inversion/uniqueness argument. -/
def LogRel.LimitedUniq.LamRetype (IH : LogRel Γ n) : Prop :=
  ∀ {x A B : SExpr} {f : WShapeFun n} {hf : f.NonZero}
      {a b : WShape (n + 1)} {u : SLevel},
    (WShape.lam f hf).HasType a →
    (WShape.lam f hf).HasType b →
    IsDefEq Γ x x A → IsDefEq Γ x x B →
    (LRS IH).TyDefEq A A a → (LRS IH).TyDefEq B B b →
    (LRS IH).DefEq x x A (WShape.lam f hf) a →
    (LRS IH).DefEq x x B (WShape.lam f hf) b →
    IsDefEq Γ A B (.sort u) →
    ∀ {y : SExpr}, IsDefEq Γ x y B →
      (LRS IH).DefEq x y B (WShape.lam f hf) b →
      (LRS IH).DefEq x y A (WShape.lam f hf) a

/-- A strong sufficient condition for lambda retyping: two arbitrary Pi-type
observations related by one raw type equality admit a joined observation.

This property is intentionally not part of `LR.JointBuilder`.  In general a
type may have incompatible finite observations (already at the first positive
level), whereas `LimitedUniq.LamRetype` only asks for the term-indexed
transport actually consumed by successor uniqueness. -/
def LogRel.PiTypeAlign (R : LogRel Γ (n + 1)) : Prop :=
  ∀ {A B : SExpr} {a₁ b₁ : WShape n} {a₂ b₂ : WShapeFun n}
      {u : SLevel},
    IsDefEq Γ A B (.sort u) →
    R.TyDefEq A A (.forallE a₁ a₂) →
    R.TyDefEq B B (.forallE b₁ b₂) →
    ∃ _compat : (WShape.forallE a₁ a₂).Compat (.forallE b₁ b₂),
      R.TyDefEq A B ((WShape.forallE a₁ a₂).join (.forallE b₁ b₂))

/-- Pi-type alignment supplies the sole non-structural lambda-retyping case. -/
theorem LogRel.LimitedUniq.LamRetype.of_piTypeAlign
    {IH : LogRel Γ n} (align : LogRel.PiTypeAlign (LRS IH)) :
    LogRel.LimitedUniq.LamRetype IH := by
  intro x A B f hf a b u hpA hpB _ _ htyA htyB _ _ hAB y _ hxy
  obtain ⟨a₁, a₂, _, rfl⟩ := WShape.HasType.lam_l.1 hpA
  obtain ⟨b₁, b₂, _, rfl⟩ := WShape.HasType.lam_l.1 hpB
  obtain ⟨compat, hTy⟩ := align hAB htyA htyB
  exact LogRel.DefEq.retype_join compat hpA hpB hTy hxy

/-- Successor-level limited uniqueness decomposes into raw weak type
uniqueness and exactly one lambda-retyping case.  This theorem discharges
all other element shapes definitionally or from the supplied semantic type
validity, making the former L4L-17 obligation consumed by the joint tower
explicit and minimal. -/
theorem LRS.limitedUniq_of_typeUniq
    {IH : LogRel Γ n}
    (typeUniq : LogRel.RawTypeUniq Γ)
    (lamRetype : LogRel.LimitedUniq.LamRetype IH) :
    LogRel.LimitedUniq (LRS IH) where
  align := by
    intro x A B p a b hpA hpB hxA hxB htyA htyB hxxA hxxB
    obtain ⟨u, hAB⟩ := typeUniq hxA hxB
    refine ⟨u, hAB, ?_⟩
    cases p using WShape.casesOn' with
    | bot =>
      intro y _ _
      exact (LRS IH).bot hpA.isType
    | sort r =>
      cases a using WShape.casesOn' <;>
        simp [WShape.HasType, WShape.bot, WShape.sort, WShape.forallE,
          WShape.lam, WShape.ctor, WShape.indTy, Shape.HasType,
          Shape.hasType] at hpA
      cases b using WShape.casesOn' <;>
        simp [WShape.HasType, WShape.bot, WShape.sort, WShape.forallE,
          WShape.lam, WShape.ctor, WShape.indTy, Shape.HasType,
          Shape.hasType] at hpB
      intro y _ hxy
      change LRS.TyDefEq IH x y (WShape.sort r)
      change LRS.TyDefEq IH x y (WShape.sort r) at hxy
      exact hxy
    | forallE d c =>
      obtain ⟨_, _, rfl⟩ := WShape.HasType.forallE_l.1 hpA
      obtain ⟨_, _, rfl⟩ := WShape.HasType.forallE_l.1 hpB
      intro y _ hxy
      change LRS.TyDefEq IH x y (WShape.forallE d c)
      change LRS.TyDefEq IH x y (WShape.forallE d c) at hxy
      exact hxy
    | lam f hf =>
      exact lamRetype hpA hpB hxA hxB htyA htyB hxxA hxxB hAB
    | ctor c fields hwf =>
      cases a using WShape.casesOn' <;>
        simp [WShape.HasType, WShape.bot, WShape.sort, WShape.forallE,
          WShape.lam, WShape.ctor, WShape.indTy, Shape.HasType,
          Shape.hasType] at hpA
      cases b using WShape.casesOn' <;>
        simp [WShape.HasType, WShape.bot, WShape.sort, WShape.forallE,
          WShape.lam, WShape.ctor, WShape.indTy, Shape.HasType,
          Shape.hasType] at hpB
      intro y _ hxy
      exact ⟨htyA.1, hxy.2⟩
    | indTy =>
      cases a using WShape.casesOn' <;>
        simp [WShape.HasType, WShape.bot, WShape.sort, WShape.forallE,
          WShape.lam, WShape.ctor, WShape.indTy, Shape.HasType,
          Shape.hasType] at hpA
      cases b using WShape.casesOn' <;>
        simp [WShape.HasType, WShape.bot, WShape.sort, WShape.forallE,
          WShape.lam, WShape.ctor, WShape.indTy, Shape.HasType,
          Shape.hasType] at hpB
      intro y _ hxy
      change LRS.TyDefEq IH x y WShape.indTy
      change LRS.TyDefEq IH x y WShape.indTy at hxy
      exact hxy

/-- Optional adapter from the stronger Pi-observation alignment property.
The joint tower consumes `LamRetype` directly; this theorem remains useful to
callers that happen to have compatible observations for independent reasons. -/
theorem LRS.limitedUniq_of_typeUniq_of_piTypeAlign
    {IH : LogRel Γ n}
    (typeUniq : LogRel.RawTypeUniq Γ)
    (align : LogRel.PiTypeAlign (LRS IH)) :
    LogRel.LimitedUniq (LRS IH) :=
  LRS.limitedUniq_of_typeUniq typeUniq
    (LogRel.LimitedUniq.LamRetype.of_piTypeAlign align)

/-- Apply functions related one stratum above `IH` to arguments related in
`IH`.  `LamDefEq` stores the two same-head congruences and the same-argument
cross-head equality separately; their composition is the ordinary
heterogeneous application rule.  Keeping this statement polymorphic in
`IH` is essential for consumers of `CtorDefEq.fold`, whose lift and unlift
branches temporarily replace the canonical logical relation by an
equivalent one. -/
theorem LRS.DefEq.app
    {n : Nat} {M N A₁ A₂ x y : SExpr}
    {mf : WShapeFun n} {hmf : mf.NonZero}
    {b p : WShape n} {tf : WShapeFun n}
    {IH : LogRel Γ n}
    (hfun : (LRS IH).DefEq M N (.forallE A₁ A₂)
      (.lam mf hmf) (.forallE b tf))
    (hp : p.HasType b) (hxy : Γ ⊢ x ≡ y : A₁)
    (harg : IH.DefEq x y A₁ p b) :
    IH.DefEq (M.app x) (N.app y) (A₂.inst x)
      (mf.app p) (tf.app p) := by
  change LRS.DefEq IH M N (.forallE A₁ A₂)
    (.lam mf hmf) (.forallE b tf) at hfun
  rw [LRS.DefEq.lam_forallE] at hfun
  obtain ⟨B, F, u, v, hred, hB, hValB, hF, hPi, hLam⟩ := hfun
  have hhead : SExpr.forallE A₁ A₂ = SExpr.forallE B F :=
    WHNF.forallE.whRedS hred
  cases hhead
  exact IH.trans
    (hLam.2 hp hxy.hasType.1 (IH.left harg))
    (hLam.1 hp hxy harg).2

/-- Apply a synchronized rectangle of related functions to one related
argument pair.  All three result edges use the same argument observation and
the same left-oriented dependent codomain, so later retyping cannot silently
mix endpoint witnesses selected at different shapes. -/
theorem LRS.DefEqRect.app
    {n : Nat} {M₁ M₂ N₁ N₂ A₁ A₂ x y : SExpr}
    {mf : WShapeFun n} {hmf : mf.NonZero}
    {b p : WShape n} {tf : WShapeFun n}
    {IH : LogRel Γ n}
    (hfun : LogRel.DefEqRect (LRS IH)
      M₁ M₂ N₁ N₂ (.forallE A₁ A₂)
      (.lam mf hmf) (.forallE b tf))
    (hp : p.HasType b) (hxy : Γ ⊢ x ≡ y : A₁)
    (harg : IH.DefEq x y A₁ p b) :
    LogRel.DefEqRect IH
      (M₁.app x) (M₂.app y) (N₁.app x) (N₂.app y)
      (A₂.inst x) (mf.app p) (tf.app p) :=
  ⟨LRS.DefEq.app hfun.left hp hxy harg,
    LRS.DefEq.app hfun.right hp hxy harg,
    LRS.DefEq.app hfun.cross hp hxy harg⟩

/-- Expose the Pi telescope stored by a function relation whose declared
type is not syntactically a Pi, then apply it at that exact exposed domain.

This is the conversion-safe one-step interface used by path-indexed
application spines: raw `PathSpineWF.conv` edges are not converted into a
semantic type equality prematurely.  Instead the logical function
observation selects its own weak-head Pi telescope, and a later alignment
step reconciles that domain with the path-selected capture type. -/
theorem LRS.DefEq.app_exposed
    {n : Nat} {M N T x y : SExpr}
    {mf : WShapeFun n} {hmf : mf.NonZero}
    {b p : WShape n} {tf : WShapeFun n}
    {IH : LogRel Γ n}
    (hfun : (LRS IH).DefEq M N T
      (.lam mf hmf) (.forallE b tf))
    (hp : p.HasType b) :
    ∃ B F u v, WHRedS Γ T (.forallE B F) ∧
      Γ ⊢ B : .sort u ∧ IH.TyDefEq B B b ∧
      B :: Γ ⊢ F : .sort v ∧
      LRS.PiDefEq IH B F F b tf ∧
      ∀ (_hxy : Γ ⊢ x ≡ y : B),
        IH.DefEq x y B p b →
        IH.DefEq (M.app x) (N.app y) (F.inst x)
          (mf.app p) (tf.app p) := by
  change LRS.DefEq IH M N T
    (.lam mf hmf) (.forallE b tf) at hfun
  rw [LRS.DefEq.lam_forallE] at hfun
  obtain ⟨B, F, u, v, hred, hB, hValB, hF, hPi, hLam⟩ := hfun
  refine ⟨B, F, u, v, hred, hB, hValB, hF, hPi, ?_⟩
  intro hxy harg
  exact IH.trans
    (hLam.2 hp hxy.hasType.1 (IH.left harg))
    (hLam.1 hp hxy harg).2

/-- Rectangle form of `LRS.DefEq.app_exposed`.

Weak-head determinism identifies the three Pi telescopes selected by the
left, right, and cross edges before any application is performed.  The
result therefore keeps one left-oriented dependent codomain across the
whole synchronized rectangle. -/
theorem LRS.DefEqRect.app_exposed
    {n : Nat} {M₁ M₂ N₁ N₂ T x y : SExpr}
    {mf : WShapeFun n} {hmf : mf.NonZero}
    {b p : WShape n} {tf : WShapeFun n}
    {IH : LogRel Γ n}
    (hfun : LogRel.DefEqRect (LRS IH)
      M₁ M₂ N₁ N₂ T
      (.lam mf hmf) (.forallE b tf))
    (hp : p.HasType b) :
    ∃ B F u v, WHRedS Γ T (.forallE B F) ∧
      Γ ⊢ B : .sort u ∧ IH.TyDefEq B B b ∧
      B :: Γ ⊢ F : .sort v ∧
      LRS.PiDefEq IH B F F b tf ∧
      ∀ (_hxy : Γ ⊢ x ≡ y : B),
        IH.DefEq x y B p b →
        LogRel.DefEqRect IH
          (M₁.app x) (M₂.app y) (N₁.app x) (N₂.app y)
          (F.inst x) (mf.app p) (tf.app p) := by
  have hleft := hfun.left
  have hright := hfun.right
  have hcross := hfun.cross
  change LRS.DefEq IH M₁ M₂ T
    (.lam mf hmf) (.forallE b tf) at hleft
  change LRS.DefEq IH N₁ N₂ T
    (.lam mf hmf) (.forallE b tf) at hright
  change LRS.DefEq IH M₁ N₂ T
    (.lam mf hmf) (.forallE b tf) at hcross
  rw [LRS.DefEq.lam_forallE] at hleft hright hcross
  obtain ⟨BL, FL, uL, vL, hredL, hBL, hValBL, hFL, hPiL, hLamL⟩ := hleft
  obtain ⟨BR, FR, _, _, hredR, _, _, _, _, hLamR⟩ := hright
  obtain ⟨BC, FC, _, _, hredC, _, _, _, _, hLamC⟩ := hcross
  have hLR : SExpr.forallE BL FL = .forallE BR FR :=
    hredL.determ .forallE hredR .forallE
  have hLC : SExpr.forallE BL FL = .forallE BC FC :=
    hredL.determ .forallE hredC .forallE
  cases hLR
  cases hLC
  refine ⟨BL, FL, uL, vL, hredL, hBL, hValBL, hFL, hPiL, ?_⟩
  intro hxy harg
  exact ⟨
    IH.trans (hLamL.2 hp hxy.hasType.1 (IH.left harg))
      (hLamL.1 hp hxy harg).2,
    IH.trans (hLamR.2 hp hxy.hasType.1 (IH.left harg))
      (hLamR.1 hp hxy harg).2,
    IH.trans (hLamC.2 hp hxy.hasType.1 (IH.left harg))
      (hLamC.1 hp hxy harg).2⟩

/-- Canonical specialization of `LRS.DefEq.app`. -/
theorem LR.DefEq.app
    {n : Nat} {M N A₁ A₂ x y : SExpr}
    {mf : WShapeFun n} {hmf : mf.NonZero}
    {b p : WShape n} {tf : WShapeFun n}
    (hfun : (LR Γ).DefEq M N (.forallE A₁ A₂)
      (.lam mf hmf) (.forallE b tf))
    (hp : p.HasType b) (hxy : Γ ⊢ x ≡ y : A₁)
    (harg : (LR Γ).DefEq x y A₁ p b) :
    (LR Γ).DefEq (M.app x) (N.app y) (A₂.inst x)
      (mf.app p) (tf.app p) := by
  rw [LR_succ] at hfun
  exact LRS.DefEq.app hfun hp hxy harg

/-- Canonical specialization of `LRS.DefEqRect.app`. -/
theorem LR.DefEqRect.app
    {n : Nat} {M₁ M₂ N₁ N₂ A₁ A₂ x y : SExpr}
    {mf : WShapeFun n} {hmf : mf.NonZero}
    {b p : WShape n} {tf : WShapeFun n}
    (hfun : LogRel.DefEqRect (LR Γ)
      M₁ M₂ N₁ N₂ (.forallE A₁ A₂)
      (.lam mf hmf) (.forallE b tf))
    (hp : p.HasType b) (hxy : Γ ⊢ x ≡ y : A₁)
    (harg : (LR Γ).DefEq x y A₁ p b) :
    LogRel.DefEqRect (LR Γ)
      (M₁.app x) (M₂.app y) (N₁.app x) (N₂.app y)
      (A₂.inst x) (mf.app p) (tf.app p) := by
  rw [LR_succ] at hfun
  exact LRS.DefEqRect.app hfun hp hxy harg

/-- An ordinary constructor observation has inductive type, so a logical-
relation witness at its exact `ctor'` shape exposes the observable
`CtorDefEq` evidence.  The classification hypothesis matters here:
`ctor'` is allowed to collapse an eta-constructor whose fields are all
bottom, but an iota pattern's constructor is classified as `.ctor`. -/
theorem LR.DefEq.ctor'_inv
    {n : Nat} {c : Name} {fields : List (WShape n)}
    {M N A : SExpr} {a : WShape (n + 1)}
    (hcl : Params.classify c = some (.ctor fields.length))
    (ht : (WShape.ctor' c fields).HasType a)
    (H : (LR Γ).DefEq M N A (WShape.ctor' c fields) a) :
    LRS.IndTyHead Γ A ∧
      LRS.CtorDefEq Γ (LR Γ) M N (WShape.ctor' c fields) := by
  have hwf : IsStruct c → WShape.ListNonZero fields := by
    simp [IsStruct, hcl]
  rw [WShape.ctor', dif_pos hwf] at ht H
  have ha : a = WShape.indTy := by
    apply WShape.ext
    change Shape.hasType (n := n + 1)
      (ShapeS.ctor c (fields.map fun x : WShape n => x.1)) a.1 at ht
    cases ha : a.1 <;> simp [ha, Shape.hasType, WShape.indTy] at ht ⊢
  subst a
  rw [LR_succ] at H
  change LRS.IndDefEq Γ (LR Γ) M N A (WShape.ctor c fields hwf) at H
  have hctor : WShape.ctor' c fields = WShape.ctor c fields hwf := by
    exact WShape.ctor_eq_ctor'.symm
  rw [hctor]
  simpa [LRS.IndDefEq, WShape.ctor] using H

private theorem LRS.PiDefEq.lift_aux
    {IH : LogRel Γ n} {IH' : LogRel Γ n'}
    {b : WShape n} {f : WShapeFun n} (le : n ≤ n') (htpi_a : WShape.HasTypePi f b true)
    (IH1 : ∀ {M N : SExpr} {m : WShape n}, WShape.HasType m .type →
      (IH'.TyDefEq M N (m.lift n') ↔ IH.TyDefEq M N m))
    (IH2 : ∀ {M N A : SExpr} {m a : WShape n}, WShape.HasType m a →
      (IH'.DefEq M N A (m.lift n') (a.lift _) ↔ IH.DefEq M N A m a)) :
    LRS.PiDefEq IH' B F₁ F₂ (b.lift n') (f.lift n') ↔
    LRS.PiDefEq IH B F₁ F₂ b f := by
  have htpi_w := WShape.HasTypePi.iff.1 htpi_a
  constructor <;> intro hEdge
  · refine ⟨fun _ _ _ hp ha v => ?_, fun _ _ hp ha v => ?_⟩ <;> (
      have hp' := (WShape.HasType.lift le).2 hp
      have v' := (IH2 hp).2 v)
    · have h := hEdge.1 hp' ha v'
      exact ⟨(IH1 (htpi_w.2 _ hp)).1 (WShapeFun.lift_app le ▸ h.leftTy),
        (IH1 (htpi_w.2 _ hp)).1 (WShapeFun.lift_app le ▸ h.rightTy),
        h.leftDefEq, h.rightDefEq⟩
    · exact (IH1 (htpi_w.2 _ hp)).1 (WShapeFun.lift_app le ▸ hEdge.2 hp' ha v')
  · refine ⟨fun _ _ _ hp ha v => ?_, fun _ _ hp ha v => ?_⟩ <;> (
      obtain ⟨q, d1, d2⟩ := WShapeFun.app_eq (f.lift n') _
      obtain ⟨q₀, y₀, d2₀, rfl, d3⟩ := (WShapeFun.mem_lift le).1 d2
      obtain ⟨qx', qy', d2₀', qxle, qyle, hq⟩ := WShape.HasDom.def.1 htpi_a.1 _ _ d2₀
      have v' := (IH2 hq).1 (IH'.mono_l (((WShape.lift_le_lift le).2 qxle).trans d1)
        ((WShape.HasType.lift le).2 hq) hp v))
    · have h := hEdge.1 hq ha v'
      have ht_q := (htpi_w.2 _ hq).toType
      have ht_y₀ : (y₀ : WShape n).HasType WShape.type := (htpi_a.2 _ _ d2₀).toType
      have y₀_le_fqx : y₀ ≤ f.app qx' := qyle.trans (f.app_of_mem d2₀').2
      have ht_q_l : ((f.app qx').lift n').HasType WShape.type := by
        have := (WShape.HasType.lift le).2 ht_q; rwa [WShape.lift_sort] at this
      have ht_y₀_l : (y₀.lift n').HasType WShape.type := by
        have := (WShape.HasType.lift le).2 ht_y₀; rwa [WShape.lift_sort] at this
      exact d3 ▸ ⟨
        IH'.mono_r_2_ty (WShape.lift_mono le y₀_le_fqx) ht_y₀_l ht_q_l
          ((IH1 ht_q).2 h.leftTy),
        IH'.mono_r_2_ty (WShape.lift_mono le y₀_le_fqx) ht_y₀_l ht_q_l
          ((IH1 ht_q).2 h.rightTy),
        h.leftDefEq, h.rightDefEq⟩
    · have hq_body := hEdge.2 hq ha v'
      have ht_q := (htpi_w.2 _ hq).toType
      have ht_y₀ : (y₀ : WShape n).HasType WShape.type := (htpi_a.2 _ _ d2₀).toType
      have y₀_le_fqx : y₀ ≤ f.app qx' := qyle.trans (f.app_of_mem d2₀').2
      have ht_q_l : ((f.app qx').lift n').HasType WShape.type := by
        have := (WShape.HasType.lift le).2 ht_q; rwa [WShape.lift_sort] at this
      have ht_y₀_l : (y₀.lift n').HasType WShape.type := by
        have := (WShape.HasType.lift le).2 ht_y₀; rwa [WShape.lift_sort] at this
      exact d3 ▸
        IH'.mono_r_2_ty (WShape.lift_mono le y₀_le_fqx) ht_y₀_l ht_q_l ((IH1 ht_q).2 hq_body)

/-- Rebase a Pi edge through the packaged equivalence carried by a
normalized constructor frame. -/
theorem LRS.PiDefEq.liftEquiv
    {IH : LogRel Γ n} {IH' : LogRel Γ n'}
    {b : WShape n} {f : WShapeFun n} (le : n ≤ n')
    (htpi : WShape.HasTypePi f b true)
    (E : LogRel.LiftEquiv IH IH' le) :
    LRS.PiDefEq IH' B F₁ F₂ (b.lift n') (f.lift n') ↔
      LRS.PiDefEq IH B F₁ F₂ b f :=
  LRS.PiDefEq.lift_aux le htpi E.ty E.term

private theorem LRS.LamDefEq.lift_aux
    {IH : LogRel Γ n} {IH' : LogRel Γ n'}
    {g : WShapeFun n} {a₁ a₂} (le : n ≤ n') (htm : WShape.HasTypeLam g a₁ a₂)
    (IHDef : ∀ {M N A : SExpr} {m a : WShape n}, WShape.HasType m a →
      (IH'.DefEq M N A (m.lift n') (a.lift _) ↔ IH.DefEq M N A m a))
    (hEdge : LRS.PiDefEq IH A₁ A₂ A₂ a₁ a₂) :
    LRS.LamDefEq IH' M N A₁ A₂ (g.lift n') (a₁.lift n') (a₂.lift n') ↔
    LRS.LamDefEq IH M N A₁ A₂ g a₁ a₂ := by
  have htm_w := WShape.HasTypeLam.iff.1 htm
  constructor <;> intro hP
  · refine ⟨fun _ _ _ hp ha v => ?_, fun _ _ hp ha v => ?_⟩ <;> (
      have hp' := (WShape.HasType.lift le).2 hp
      have v' := (IHDef hp).2 v)
    · have ⟨r1, r2⟩ := hP.1 hp' ha v'
      refine ⟨(IHDef (htm_w.2.2 _ hp)).1 ?_, (IHDef (htm_w.2.2 _ hp)).1 ?_⟩
        <;> rw [WShapeFun.lift_app le, WShapeFun.lift_app le] <;> [exact r1; exact r2]
    · apply (IHDef (htm_w.2.2 _ hp)).1
      rw [WShapeFun.lift_app le, WShapeFun.lift_app le]
      exact hP.2 hp' ha v'
  · refine ⟨fun a' b' p hp ha v => ?_, fun a' p hp ha v => ?_⟩
    all_goals
      obtain ⟨_, dg1, dg2⟩ := WShapeFun.app_eq (g.lift n') p
      obtain ⟨_, da1, da2⟩ := WShapeFun.app_eq (a₂.lift n') p
      obtain ⟨qg, yg, dg2₀, rfl, dg3⟩ := (WShapeFun.mem_lift le).1 dg2
      obtain ⟨qa, ya, da2₀, rfl, da3⟩ := (WShapeFun.mem_lift le).1 da2
      have ⟨yg₁, yg₂⟩ := WShapeFun.app_of_mem dg2₀
      have ⟨ya₁, ya₂⟩ := WShapeFun.app_of_mem da2₀
      have ⟨qg', qg'le, hqg, qg'app⟩ := WShape.HasDom.iff.1 htm.2.1 qg
      have ⟨qa', qa'le, hqa, qa'app⟩ := WShape.HasDom.iff.1 htm.1.1 qa
      rw [dg3, da3]
      have v_lo := (IHDef hqg).1 <| IH'.mono_l
        (((WShape.lift_le_lift le).2 qg'le).trans dg1) ((WShape.HasType.lift le).2 hqg) hp v
      have v_lo_qa := (IHDef hqa).1 <| IH'.mono_l
        (((WShape.lift_le_lift le).2 qa'le).trans da1) ((WShape.HasType.lift le).2 hqa) hp v
      have ht_lo := htm_w.2.2 _ hqg
      have htm_p := WShape.HasTypePi.iff'.1 htm_w.1
      have vt_qa := hEdge.2 hqa ha.hasType.1 (IH.left v_lo_qa)
      have vt_qa' := IH.mono_r_2_ty qa'app (htm_p.2 qa) (htm_p.2 qa') vt_qa
      have ya_sort := (htm_p.2 qa).mono_l ya₁ ya₂
      have ht_yg_qg' : yg.HasType (a₂.app qg') :=
        ht_lo.mono_l (WShapeFun.app_mono_r qg'le |>.trans yg₁) (yg₂.trans qg'app)
      have le_a2_ya := by
        refine (a₂.app_mono_r qg'le).trans (.trans ?_ ya₁)
        rw [← WShape.lift_le_lift le, WShapeFun.lift_app le]
        exact (WShapeFun.app_mono_r dg1 (f := a₂.lift n')).trans <| da3 ▸ WShape.lift_mono le ya₂
      have ya_sort := (htm_p.2 qa).mono_l ya₁ ya₂
      have ht_yg := ya_sort.mono_r le_a2_ya ht_yg_qg'
      have vt_ya := IH.mono_r_2_ty ya₂ ya_sort (htm_p.2 qa) vt_qa'
      have go {M N} (r : IH.DefEq M N (A₂.inst a') (g.app qg') (a₂.app qg')) :
          IH'.DefEq M N (A₂.inst a') (yg.lift n') (ya.lift n') :=
        (IHDef ht_yg).2 <|
        IH.mono_r_1 le_a2_ya ht_yg_qg' ht_yg vt_ya <|
        IH.mono_l (yg₂.trans qg'app) ht_yg_qg' ht_lo r
    · have ⟨r1, r2⟩ := hP.1 hqg ha v_lo; exact ⟨go r1, go r2⟩
    · exact go (hP.2 hqg ha v_lo)

/-- Transport the successor type relation along an arbitrary lower-relation
equivalence.  This is the continuation law required by constructor
observations that cross shape levels. -/
theorem LRS.TyDefEq.lift
    {IH : LogRel Γ n} {IH' : LogRel Γ n'}
    (le : n ≤ n')
    (IH1 : ∀ {M N : SExpr} {m : WShape n}, m.HasType .type →
      (IH'.TyDefEq M N (m.lift n') ↔ IH.TyDefEq M N m))
    (IH2 : ∀ {M N A : SExpr} {m a : WShape n}, m.HasType a →
      (IH'.DefEq M N A (m.lift n') (a.lift n') ↔ IH.DefEq M N A m a))
    {m : WShape (n + 1)} (hmt : m.HasType .type) :
    LRS.TyDefEq IH' M N (m.lift (n' + 1)) ↔
      LRS.TyDefEq IH M N m := by
  cases m using WShape.casesOn' with
  | bot => rw [WShape.lift_bot]; rfl
  | sort r => rw [WShape.lift_sort]; rfl
  | forallE b f =>
    rw [WShape.lift_forallE le]
    have ⟨_, htpi, rfl⟩ := WShape.HasType.forallE_l.1 hmt
    constructor <;>
      intro ⟨B₁, F₁, B₂, F₂, u, v, rM, rN, hB, hF, hValB, hE⟩ <;>
      refine ⟨B₁, F₁, B₂, F₂, u, v, rM, rN, hB, hF, ?_, ?_⟩
    · exact (IH1 (WShape.HasTypePi.iff.1 htpi).1.isType).1 hValB
    · exact (LRS.PiDefEq.lift_aux le htpi IH1 IH2).1 hE
    · exact (IH1 (WShape.HasTypePi.iff.1 htpi).1.isType).2 hValB
    · exact (LRS.PiDefEq.lift_aux le htpi IH1 IH2).2 hE
  | lam f h => rw [WShape.lift_lam le]; rfl
  | ctor c l h => rw [WShape.lift_ctor le]; rfl
  | indTy => rw [WShape.lift_indTy]; rfl

/-- Transport the full successor term relation along arbitrary term- and
type-relation lift equivalences. -/
theorem LRS.DefEq.lift
    {IH : LogRel Γ n} {IH' : LogRel Γ n'}
    (le : n ≤ n')
    (IH1 : ∀ {M N : SExpr} {m : WShape n}, m.HasType .type →
      (IH'.TyDefEq M N (m.lift n') ↔ IH.TyDefEq M N m))
    (IH2 : ∀ {M N A : SExpr} {m a : WShape n}, m.HasType a →
      (IH'.DefEq M N A (m.lift n') (a.lift n') ↔ IH.DefEq M N A m a))
    {m a : WShape (n + 1)} (hma : m.HasType a) :
    LRS.DefEq IH' M N A (m.lift (n' + 1)) (a.lift (n' + 1)) ↔
      LRS.DefEq IH M N A m a := by
  cases a using WShape.casesOn' with
  | bot => rw [WShape.lift_bot]; rfl
  | sort r =>
    rw [WShape.lift_sort]
    exact LRS.TyDefEq.lift le IH1 IH2 hma.toType
  | indTy =>
    rw [WShape.lift_indTy]
    exact LRS.IndDefEq.lift le IH1 IH2
  | forallE a₁ a₂ =>
    have ⟨_, htpi_a, _⟩ := WShape.HasType.forallE_l.1 hma.isType
    obtain ⟨g, rfl, htm⟩ := WShape.HasType.forallE_inv hma
    unfold WShape.lam'
    split
    · rw [WShape.lift_lam le, WShape.lift_forallE le]
      simp only [LRS.DefEq.lam_forallE]
      constructor <;>
        intro ⟨A₁, A₂, u, v, rA, hA1, hValA, hA₂, hEdge, hP⟩
      · have hEdge' := (LRS.PiDefEq.lift_aux le htm.1 IH1 IH2).1 hEdge
        exact ⟨A₁, A₂, u, v, rA, hA1,
          (IH1 (WShape.HasTypePi.iff.1 htpi_a).1.isType).1 hValA,
          hA₂, hEdge', (LRS.LamDefEq.lift_aux le htm IH2 hEdge').1 hP⟩
      · have hEdge' := (LRS.PiDefEq.lift_aux le htm.1 IH1 IH2).2 hEdge
        exact ⟨A₁, A₂, u, v, rA, hA1,
          (IH1 (WShape.HasTypePi.iff.1 htpi_a).1.isType).2 hValA,
          hA₂, hEdge', (LRS.LamDefEq.lift_aux le htm IH2 hEdge).2 hP⟩
    · rw [WShape.lift_forallE le]
      rfl
  | _ => cases hma.isType

/-- Lift a packaged relation equivalence through one `LRS` layer. -/
def LogRel.LiftEquiv.succ
    {IH : LogRel Γ n} {IH' : LogRel Γ n'} {le : n ≤ n'}
    (E : LogRel.LiftEquiv IH IH' le) :
    LogRel.LiftEquiv (LRS IH) (LRS IH') (Nat.succ_le_succ le) where
  ty := by
    intro A B a ha
    exact LRS.TyDefEq.lift le E.ty E.term ha
  term := by
    intro M N A m a hma
    exact LRS.DefEq.lift le E.ty E.term hma

private theorem LR.lift_succ_aux :
    (∀ {M N : SExpr} {m : WShape n}, WShape.HasType m .type →
      (LRS.TyDefEq (n := n) (LR Γ) M N (m.lift _) ↔ (LR Γ).TyDefEq M N m)) ∧
    (∀ {M N A : SExpr} {m a : WShape n}, WShape.HasType m a →
      (LRS.DefEq (n := n) (LR Γ) M N A (m.lift _) (a.lift _) ↔ (LR Γ).DefEq M N A m a)) := by
  induction n with
  | zero =>
    refine ⟨fun {M N m} _ => ?_, fun {M N A m a} _ => ?_⟩
    · cases m using WShape.casesOn <;> trivial
    · cases m using WShape.casesOn <;> cases a using WShape.casesOn <;> trivial
  | succ k ih =>
    refine have h1 := ?_; ⟨h1, ?_⟩
    · intro M N m hmt
      cases m using WShape.casesOn' with
      | forallE b f => ?_
      | indTy =>
        change LRS.TyDefEq (LR Γ) M N ((WShape.indTy : WShape (k+1)).lift (k+2)) ↔ _
        rw [WShape.lift_indTy]
        rw [LR_succ]
        change (LRS.IndTyHead Γ M ∧ LRS.IndTyHead Γ N) ↔
          (LRS.IndTyHead Γ M ∧ LRS.IndTyHead Γ N)
        rfl
      | _ => constructor <;> intro <;> trivial
      rw [WShape.lift_forallE (Nat.le_succ k)]
      have ⟨_, htpi, rfl⟩ := WShape.HasType.forallE_l.1 hmt
      constructor <;> intro ⟨B₁, F₁, B₂, F₂, u, v, rM, rN, hB, hF, hValB, hE⟩ <;>
        refine ⟨B₁, F₁, B₂, F₂, u, v, rM, rN, hB, hF, ?_, ?_⟩
      · exact (ih.1 (WShape.HasTypePi.iff.1 htpi).1.isType).1 hValB
      · exact (LRS.PiDefEq.lift_aux (IH := LR Γ) (IH' := LRS (LR Γ))
          (Nat.le_succ k) htpi ih.1 ih.2).1 hE
      · exact (ih.1 (WShape.HasTypePi.iff.1 htpi).1.isType).2 hValB
      · exact (LRS.PiDefEq.lift_aux (IH := LR Γ) (IH' := LRS (LR Γ))
          (Nat.le_succ k) htpi ih.1 ih.2).2 hE
    · intro M N A m a hma
      cases a using WShape.casesOn' with
      | bot => constructor <;> intro <;> trivial
      | indTy =>
        rw [WShape.lift_indTy]
        exact LRS.IndDefEq.lift (Nat.le_succ k) ih.1 ih.2
      | sort => exact h1 hma.toType
      | forallE a₁ a₂ => ?_ | _ => cases hma.isType
      have ⟨_, htpi_a, _⟩ := WShape.HasType.forallE_l.1 hma.isType
      obtain ⟨g, rfl, htm⟩ := WShape.HasType.forallE_inv hma
      unfold WShape.lam'; split <;> [skip; (simp; trivial)]
      rw [WShape.lift_lam (Nat.le_succ k), WShape.lift_forallE (Nat.le_succ k)]
      simp only [LRS.DefEq.lam_forallE]
      constructor <;> intro ⟨A₁, A₂, u, v, rA, hA1, hValA, hA₂, hEdge, hP⟩ <;>
        [ have hEdge' := (LRS.PiDefEq.lift_aux
            (IH := LR Γ) (IH' := LRS (LR Γ))
            (Nat.le_succ k) htm.1 ih.1 ih.2).1 hEdge;
          have hEdge' := (LRS.PiDefEq.lift_aux
            (IH := LR Γ) (IH' := LRS (LR Γ))
            (Nat.le_succ k) htm.1 ih.1 ih.2).2 hEdge ] <;>
        refine ⟨A₁, A₂, u, v, rA, hA1, ?_, hA₂, hEdge', ?_⟩
      · exact (ih.1 (WShape.HasTypePi.iff.1 htpi_a).1.isType).1 hValA
      · exact (LRS.LamDefEq.lift_aux (IH := LR Γ) (IH' := LRS (LR Γ))
          (Nat.le_succ k) htm ih.2 hEdge').1 hP
      · exact (ih.1 (WShape.HasTypePi.iff.1 htpi_a).1.isType).2 hValA
      · exact (LRS.LamDefEq.lift_aux (IH := LR Γ) (IH' := LRS (LR Γ))
          (Nat.le_succ k) htm ih.2 hEdge).2 hP

theorem LR.DefEq.lift {m a : WShape n} (le : n ≤ n') (hma : WShape.HasType m a) :
    (LR Γ).DefEq M N A (m.lift n') (a.lift _) ↔ (LR Γ).DefEq M N A m a := by
  induction le with | refl => simp [WShape.lift_self] | step le ih
  rw [(WShape.lift_lift (.inl le)).symm, (WShape.lift_lift (s := a) (.inl le)).symm]
  exact (LR.lift_succ_aux.2 ((WShape.HasType.lift le).2 hma)).trans ih

theorem LR.TyDefEq.lift {m : WShape n} (le : n ≤ n') (hmt : WShape.HasType m .type) :
    (LR Γ).TyDefEq (n := n') M N (m.lift _) ↔ (LR Γ).TyDefEq M N m := by
  induction le with | refl => simp [WShape.lift_self] | step le ih
  rw [(WShape.lift_lift (.inl le)).symm]
  have := (WShape.HasType.lift le).2 hmt
  simp [WShape.type] at this
  exact (LR.lift_succ_aux.1 this).trans ih

/-- The canonical stratified logical relation realizes itself at every
higher level. -/
def LogRel.LiftEquiv.canonical (le : n ≤ n') :
    LogRel.LiftEquiv (LR Γ : LogRel Γ n) (LR Γ : LogRel Γ n') le where
  ty := by
    intro A B a ha
    exact LR.TyDefEq.lift le ha
  term := by
    intro M N A m a hma
    exact LR.DefEq.lift le hma

/-- Canonical cross-level transport for synchronized rectangles. -/
theorem LR.DefEqRect.lift
    {m a : WShape n} (le : n ≤ n') (hma : m.HasType a) :
    LogRel.DefEqRect (LR Γ : LogRel Γ n') M₁ M₂ N₁ N₂ A
        (m.lift n') (a.lift n') ↔
      LogRel.DefEqRect (LR Γ : LogRel Γ n) M₁ M₂ N₁ N₂ A m a :=
  (LogRel.LiftEquiv.canonical (Γ := Γ) le).rect hma

/-- Build an observable constructor relation from exact related application
spines and a semantic constructor bound at a level at least as large as the
spine's.  Semantic arguments are newest-first, so the constructor's field
list is their reverse. -/
theorem LRS.CtorDefEq.of_exact_ctor_spines_of_le
    {n k : Nat} {c : Name} {ls ls' : List SLevel}
    {rargs : List (WShape n)} {xs ys : List SExpr}
    {CHead CHead' A A' : SExpr}
    (hargs : CtorArgsDefEq (LR Γ) xs ys rargs)
    (haligned : CtorSpineDefEq (LR Γ) CHead xs ys rargs A)
    (hmirror : CtorSpineDefEq (LR Γ) CHead' ys xs rargs A')
    (hcl : Params.classify c = some (.ctor rargs.length))
    (hlevels : ls = ls')
    (hhead : IsDefEq Γ (.const c ls) (.const c ls) CHead)
    (hhead' : IsDefEq Γ (.const c ls') (.const c ls') CHead')
    (hspine : SExpr.SpineWF Γ CHead xs.reverse A)
    (hspine' : SExpr.SpineWF Γ CHead' ys.reverse A')
    (hn : n ≤ k)
    {m : WShape (k + 1)}
    (hle : m.T ≤ (WShape.ctor' c rargs.reverse).T) :
    CtorDefEq Γ (LR Γ)
      (xs.foldr (fun a f => f.app a) (.const c ls))
      (ys.foldr (fun a f => f.app a) (.const c ls')) m := by
  have hargs' : CtorArgsDefEq (LR Γ) xs ys (rargs.map (.lift k)) :=
    hargs.lift hn (fun hmt => LR.TyDefEq.lift hn hmt)
      (fun hma => LR.DefEq.lift hn hma)
  have haligned' : CtorSpineDefEq (LR Γ) CHead xs ys
      (rargs.map (.lift k)) A :=
    haligned.lift hn (fun hmt => LR.TyDefEq.lift hn hmt)
      (fun hma => LR.DefEq.lift hn hma)
  have hmirror' : CtorSpineDefEq (LR Γ) CHead' ys xs
      (rargs.map (.lift k)) A' :=
    hmirror.lift hn (fun hmt => LR.TyDefEq.lift hn hmt)
      (fun hma => LR.DefEq.lift hn hma)
  have hwf : IsStruct c → WShape.ListNonZero ((rargs.map (.lift k)).reverse) := by
    intro hs
    simp [IsStruct, hcl] at hs
  have hexact : CtorDefEq Γ (LR Γ)
      (xs.foldr (fun a f => f.app a) (.const c ls))
      (ys.foldr (fun a f => f.app a) (.const c ls'))
      (.ctor c (rargs.map (.lift k)).reverse hwf) := by
    exact .exact (hargs.lengths.1.symm ▸ hcl)
      hargs'.lengths.1 hargs'.lengths.2 hlevels .rfl .rfl
      hhead hhead' hspine hspine' hargs' haligned' hmirror'
  have hle' : m ≤
      WShape.ctor c (rargs.map (.lift k)).reverse hwf := by
    have hle' := (TShape.LE.def (Nat.le_refl (k + 1))
      (Nat.succ_le_succ hn)).1 hle
    rw [WShape.lift_ctor' hn, List.map_reverse] at hle'
    simpa only [WShape.lift_self, WShape.ctor_eq_ctor'] using hle'
  exact .mono hle' hexact

/-- Build an observable constructor relation from exact related application
spines at arbitrary shape levels.  The finite evidence is first lifted to a
common level; the relation's transport closure records that construction. -/
theorem LRS.CtorDefEq.of_exact_ctor_spines
    {n k : Nat} {c : Name} {ls ls' : List SLevel}
    {rargs : List (WShape n)} {xs ys : List SExpr}
    {CHead CHead' A A' : SExpr}
    (hargs : CtorArgsDefEq (LR Γ) xs ys rargs)
    (haligned : CtorSpineDefEq (LR Γ) CHead xs ys rargs A)
    (hmirror : CtorSpineDefEq (LR Γ) CHead' ys xs rargs A')
    (hcl : Params.classify c = some (.ctor rargs.length))
    (hlevels : ls = ls')
    (hhead : IsDefEq Γ (.const c ls) (.const c ls) CHead)
    (hhead' : IsDefEq Γ (.const c ls') (.const c ls') CHead')
    (hspine : SExpr.SpineWF Γ CHead xs.reverse A)
    (hspine' : SExpr.SpineWF Γ CHead' ys.reverse A')
    {m : WShape (k + 1)}
    (hle : m.T ≤ (WShape.ctor' c rargs.reverse).T) :
    CtorDefEq Γ (LR Γ)
      (xs.foldr (fun a f => f.app a) (.const c ls))
      (ys.foldr (fun a f => f.app a) (.const c ls')) m := by
  let K := max k n
  have hk : k ≤ K := Nat.le_max_left ..
  have hn : n ≤ K := Nat.le_max_right ..
  have hle' : (m.lift (K + 1)).T ≤
      (WShape.ctor' c rargs.reverse).T :=
    (TShape.lift_eqv (a := m.T) (Nat.succ_le_succ hk)).1.trans hle
  exact .unlift hk (fun hmt => LR.TyDefEq.lift hk hmt)
    (fun hma => LR.DefEq.lift hk hma) <|
    of_exact_ctor_spines_of_le hargs haligned hmirror hcl hlevels hhead hhead'
      hspine hspine' hn hle'

/-- A concrete capture realized in one explicitly supplied logical
relation.  This is the transport-friendly form consumed by
`CtorDefEq.fold`: constructor fields live in `IH`, while recursor captures
live one level higher in `LRS IH`. -/
def LRS.CaptureDefEqAt (IH : LogRel Γ n) (m : TShape)
    (x y : SExpr) : Prop :=
  ∃ (elemShape typeShape : WShape n) (typeExpr : SExpr),
    m ≤ elemShape.T ∧ elemShape.HasType typeShape ∧
    IH.TyDefEq typeExpr typeExpr typeShape ∧
    Γ ⊢ x ≡ y : typeExpr ∧
    IH.DefEq x y typeExpr elemShape typeShape

/-- Data chosen from a capture proposition when downstream dependent
indices must refer to its exact type expression and shapes. -/
structure LRS.CaptureDefEqAt.Witness
    (IH : LogRel Γ n) (m : TShape) (x y : SExpr) where
  elemShape : WShape n
  typeShape : WShape n
  typeExpr : SExpr
  shape : m ≤ elemShape.T
  hasType : elemShape.HasType typeShape
  typeRelated : IH.TyDefEq typeExpr typeExpr typeShape
  defeq : Γ ⊢ x ≡ y : typeExpr
  related : IH.DefEq x y typeExpr elemShape typeShape

/-- Choose the evidence-rich representative of an existential capture.
The logical proposition remains proof-irrelevant; only this local
noncomputable projection exposes its dependent indices. -/
noncomputable def LRS.CaptureDefEqAt.witness
    (H : CaptureDefEqAt IH m x y) : CaptureDefEqAt.Witness IH m x y :=
  Classical.choice (by
    rcases H with ⟨elemShape, typeShape, typeExpr,
      hshape, htype, hty, hxy, hrel⟩
    exact ⟨⟨elemShape, typeShape, typeExpr,
      hshape, htype, hty, hxy, hrel⟩⟩)

/-- A capture witness whose SExpr type is fixed by the surrounding dependent
application spine.  Unlike `CaptureDefEqAt`, this proposition cannot choose
an unrelated existential type at a variable RHS leaf. -/
def LRS.CaptureDefEqAligned (IH : LogRel Γ n) (m : TShape)
    (x y typeExpr : SExpr) : Prop :=
  ∃ (elemShape typeShape : WShape n),
    m ≤ elemShape.T ∧ elemShape.HasType typeShape ∧
    IH.TyDefEq typeExpr typeExpr typeShape ∧
    Γ ⊢ x ≡ y : typeExpr ∧
    IH.DefEq x y typeExpr elemShape typeShape

/-- The non-existential payload of an aligned capture at explicitly chosen
element and type shapes.  This is the layer predicate retained by an
ordered typed telescope. -/
def LRS.CaptureDefEqAligned.AtShapes
    (IH : LogRel Γ n) (m : TShape) (x y typeExpr : SExpr)
    (elemShape typeShape : WShape n) : Prop :=
  m ≤ elemShape.T ∧ elemShape.HasType typeShape ∧
    IH.TyDefEq typeExpr typeExpr typeShape ∧
    Γ ⊢ x ≡ y : typeExpr ∧
    IH.DefEq x y typeExpr elemShape typeShape

/-- Evidence-rich representative of an aligned capture.  The ordered
dependent telescope must reuse one and the same `elemShape`/`typeShape`
pair for the semantic argument bound, the function-domain typing, and the
logical application step; choosing those existentials independently would
erase precisely that synchronization. -/
structure LRS.CaptureDefEqAligned.Witness
    (IH : LogRel Γ n) (m : TShape)
    (x y typeExpr : SExpr) where
  elemShape : WShape n
  typeShape : WShape n
  shape : m ≤ elemShape.T
  hasType : elemShape.HasType typeShape
  typeRelated : IH.TyDefEq typeExpr typeExpr typeShape
  defeq : Γ ⊢ x ≡ y : typeExpr
  related : IH.DefEq x y typeExpr elemShape typeShape

/-- Select the synchronized representative of an aligned capture once.
Downstream dependent indices may refer to its exact shapes without adding
any semantic premise. -/
noncomputable def LRS.CaptureDefEqAligned.witness
    (H : LRS.CaptureDefEqAligned IH m x y typeExpr) :
    LRS.CaptureDefEqAligned.Witness IH m x y typeExpr :=
  Classical.choice (by
    rcases H with ⟨elemShape, typeShape, hshape, htype,
      hty, hxy, hrel⟩
    exact ⟨⟨elemShape, typeShape, hshape, htype,
      hty, hxy, hrel⟩⟩)

/-- Forget the chosen representative back to the proof-irrelevant aligned
capture proposition. -/
theorem LRS.CaptureDefEqAligned.Witness.aligned
    (H : LRS.CaptureDefEqAligned.Witness IH m x y typeExpr) :
    LRS.CaptureDefEqAligned IH m x y typeExpr :=
  ⟨H.elemShape, H.typeShape, H.shape, H.hasType,
    H.typeRelated, H.defeq, H.related⟩

/-- Expose all aligned-capture fields at the witness's exact shapes. -/
theorem LRS.CaptureDefEqAligned.Witness.atShapes
    (H : LRS.CaptureDefEqAligned.Witness IH m x y typeExpr) :
    LRS.CaptureDefEqAligned.AtShapes IH m x y typeExpr
      H.elemShape H.typeShape :=
  ⟨H.shape, H.hasType, H.typeRelated, H.defeq, H.related⟩

/-- Consume one literally aligned dependent-application layer.

The function relation lives one canonical stratum above the capture
relation.  Because `elemShape` and `typeShape` are the exact pair retained
by the ordered telescope, the ordinary logical application rule applies
without lowering, lifting, or reselecting either shape.  Conversion edges
in a surrounding `PathSpineWF` are intentionally outside this lemma. -/
theorem LRS.CaptureDefEqAligned.AtShapes.app
    {m : TShape} {x y A B M N : SExpr}
    {elemShape typeShape : WShape n}
    {termFun typeFun : WShapeFun n} {hterm : termFun.NonZero}
    (H : LRS.CaptureDefEqAligned.AtShapes (LR Γ)
      m x y A elemShape typeShape)
    (hfun : (LR Γ).DefEq M N (.forallE A B)
      (.lam termFun hterm) (.forallE typeShape typeFun)) :
    (LR Γ).DefEq (M.app x) (N.app y) (B.inst x)
      (termFun.app elemShape) (typeFun.app elemShape) := by
  exact LR.DefEq.app hfun H.2.1 H.2.2.2.1 H.2.2.2.2

/-- Lift a literally chosen aligned capture without reselecting either of its
shape indices.  This is the exact transport used by the ordered fixed-head
producer when a semantic application layer, its recursive result, and its
logical capture initially live at different finite levels. -/
theorem LRS.CaptureDefEqAligned.AtShapes.lift
    {m : TShape} {x y A : SExpr} {elemShape typeShape : WShape n}
    (le : n ≤ n')
    (H : LRS.CaptureDefEqAligned.AtShapes (LR Γ)
      m x y A elemShape typeShape) :
    LRS.CaptureDefEqAligned.AtShapes (LR Γ)
      m x y A (elemShape.lift n') (typeShape.lift n') := by
  exact ⟨H.1.trans (TShape.lift_eqv le).2,
    (WShape.HasType.lift le).2 H.2.1,
    (LR.TyDefEq.lift le H.2.1.isType).2 H.2.2.1,
    H.2.2.2.1,
    (LR.DefEq.lift le H.2.1).2 H.2.2.2.2⟩

/-- An aligned capture at an existential canonical shape level.

Generated iota paths mix recursor arguments and constructor fields from
adjacent logical strata, while a semantic `ShapeSpine` may expose either at
yet another `TShape` level.  Keeping the level existential here permits the
producer to choose one common *higher* level and use `AtShapes.lift`; no
downward projection of a logical observation is admitted. -/
def LRS.CaptureDefEqAligned.AtSomeLevel (Γ : List SExpr)
    (m : TShape) (x y typeExpr : SExpr) : Prop :=
  ∃ (n : Nat) (elemShape typeShape : WShape n),
    LRS.CaptureDefEqAligned.AtShapes (LR Γ)
      m x y typeExpr elemShape typeShape

/-- Package an ordinary aligned capture at its existing canonical level. -/
theorem LRS.CaptureDefEqAligned.atSomeLevel
    (H : LRS.CaptureDefEqAligned (LR Γ : LogRel Γ n)
      m x y typeExpr) :
    LRS.CaptureDefEqAligned.AtSomeLevel Γ m x y typeExpr := by
  rcases H with ⟨elemShape, typeShape, hshape, htyped,
    htype, hraw, hrel⟩
  exact ⟨n, elemShape, typeShape,
    hshape, htyped, htype, hraw, hrel⟩

/-- The syntax-independent shape ladder for one fixed-head application
spine.

`cons` records exactly one canonical logical application layer.  `liftHead`
is deliberately one-sided: it raises only the current head observation and
leaves the already-built tail/output untouched.  Its consumer can erase the
frame with `LR.DefEq.lift`; the constructor therefore supports application
layers whose semantic shape, recursive lower head, and capture relation were
born at different levels without ever projecting a high refinement down. -/
inductive LR.FixedHeadShapeChain (Γ : List SExpr)
    {p : Pattern} (mcap : p.Path → TShape)
    (mx my captureType : p.Path → SExpr) :
    ∀ (paths : List p.Path)
      {headLevel : Nat}, WShape headLevel → WShape headLevel →
      ∀ {outLevel : Nat}, WShape outLevel → WShape outLevel → Prop where
  | nil {n : Nat} {out outTy : WShape n} :
      LR.FixedHeadShapeChain Γ mcap mx my captureType
        [] out outTy out outTy
  | cons
      {n : Nat} {path : p.Path} {paths : List p.Path}
      {termFun typeFun : WShapeFun n} {hterm : termFun.NonZero}
      {argCap tyDom : WShape n}
      {outLevel : Nat} {out outTy : WShape outLevel}
      (capture : LRS.CaptureDefEqAligned.AtShapes (LR Γ)
        (mcap path) (mx path) (my path) (captureType path)
        argCap tyDom)
      (tail : LR.FixedHeadShapeChain Γ mcap mx my captureType
        paths (termFun.app argCap) (typeFun.app argCap) out outTy) :
      LR.FixedHeadShapeChain Γ mcap mx my captureType
        (path :: paths) (.lam termFun hterm) (.forallE tyDom typeFun)
        out outTy
  | liftHead
      {n n' : Nat} {head headTy : WShape n}
      {paths : List p.Path} {outLevel : Nat}
      {out outTy : WShape outLevel}
      (le : n ≤ n') (htyped : head.HasType headTy)
      (tail : LR.FixedHeadShapeChain Γ mcap mx my captureType
        paths head headTy out outTy) :
      LR.FixedHeadShapeChain Γ mcap mx my captureType
        paths (head.lift n') (headTy.lift n') out outTy

/-- Build the complete syntax-independent logical shape ladder below one
non-bottom semantic RHS spine.

The construction proceeds from the result back to the fixed head.  At each
layer it raises the semantic function/argument, the recursively synthesized
head, and the chosen aligned capture to a common maximum level.  The new
singleton lambda/Pi pair is typed at that exact common capture and lies below
the semantic function head.  The terminal `out`/`outTy` pair is never lifted,
so the eventual logical fold still lands at the caller's exact observation. -/
theorem LE_Interp.RHS.ShapeSpine.fixedHeadShapeChain
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {paths : List p.Path} {head : TShape}
    {outLevel : Nat} {out outTy : WShape outLevel}
    (H : LE_Interp.RHS.ShapeSpine mcap head paths out.T)
    (hcap : ∀ path, LRS.CaptureDefEqAligned.AtSomeLevel Γ
      (mcap path) (mx path) (my path) (captureType path))
    (hout : out.HasType outTy) (houtNonbot : ¬out.T ≤ TShape.bot) :
    ∃ (headLevel : Nat) (headElem headElemTy : WShape headLevel),
      headElem.T ≤ head ∧ headElem.HasType headElemTy ∧
        ¬headElem.T ≤ TShape.bot ∧
        LR.FixedHeadShapeChain Γ mcap mx my captureType
          paths headElem headElemTy out outTy := by
  generalize houtT : out.T = outT at H
  induction H generalizing outLevel out outTy with
  | @nil head0 =>
    have houtLe : out.T ≤ head0 := by
      rw [houtT]
      exact TShape.LE.rfl
    exact ⟨outLevel, out, outTy, houtLe, hout, houtNonbot,
      LR.FixedHeadShapeChain.nil⟩
  | @cons n f a m outT path paths harg happ hrest ih =>
    obtain ⟨nextLevel, next, nextTy, hnext, hnextTy,
      hnextNonbot, tail⟩ := ih hout houtNonbot houtT
    obtain ⟨capLevel, argCap, tyDom, capture⟩ := hcap path
    have hnextApp : next.T ≤ (f.app a).T := hnext.trans happ
    cases f using WShape.casesOn' with
    | bot => exact (hnextNonbot (hnextApp.trans TShape.bot_eqv.1)).elim
    | sort => exact (hnextNonbot (hnextApp.trans TShape.bot_eqv.1)).elim
    | forallE => exact (hnextNonbot (hnextApp.trans TShape.bot_eqv.1)).elim
    | ctor => exact (hnextNonbot (hnextApp.trans TShape.bot_eqv.1)).elim
    | indTy => exact (hnextNonbot (hnextApp.trans TShape.bot_eqv.1)).elim
    | @lam g hg =>
      let k := max n (max nextLevel capLevel)
      have hk : n ≤ k ∧ nextLevel ≤ k ∧ capLevel ≤ k := by
        dsimp [k]
        omega
      let aK : WShape k := a.lift k
      let argCapK : WShape k := argCap.lift k
      let tyDomK : WShape k := tyDom.lift k
      let nextK : WShape k := next.lift k
      let nextTyK : WShape k := nextTy.lift k
      let elemFun : WShapeFun k := .single argCapK nextK
      let typeFun : WShapeFun k := .single argCapK nextTyK
      have hargBound : a.T ≤ argCap.T := harg.trans capture.1
      have hargK : aK ≤ argCapK := by
        exact (TShape.LE.def hk.1 hk.2.2).1 hargBound
      have hnextAppK : nextK ≤ (g.lift k).app argCapK := by
        have hmono : ((WShape.lam g hg).app a).T ≤
            ((WShape.lam (g.lift k)
              (WShapeFun.NonZero.lift_iff hk.1 |>.2 hg)).app argCapK).T := by
          apply TShape.app_mono
          · have hLift := (TShape.lift_eqv
              (a := (WShape.lam g hg).T)
              (Nat.succ_le_succ hk.1)).2
            rw [WShape.lift_lam hk.1] at hLift
            exact hLift
          · exact hargBound.trans (TShape.lift_eqv hk.2.2).2
        have hT : next.T ≤ ((g.lift k).app argCapK).T := by
          simpa [WShape.lam_eq_lam'] using hnextApp.trans hmono
        have hTK := (TShape.LE.def hk.2.1 (Nat.le_refl k)).1 hT
        simpa only [nextK, WShape.lift_self] using hTK
      have hnextKTy : nextK.HasType nextTyK :=
        (WShape.HasType.lift hk.2.1).2 hnextTy
      have hnextKNonbot : ¬nextK.T ≤ TShape.bot := by
        intro hbot
        exact hnextNonbot <|
          (TShape.lift_eqv hk.2.1).2.trans
            (hbot.trans TShape.bot_eqv.1)
      have helemNonzero : elemFun.NonZero := by
        rw [WShapeFun.NonZero.iff]
        refine ⟨(argCapK, nextK),
          WShapeFun.mem_single.2 (.inl rfl), ?_⟩
        intro hbot
        exact hnextKNonbot <|
          (WShape.LE.T hbot).trans TShape.bot_eqv.1
      let headElem : WShape (k + 1) := .lam elemFun helemNonzero
      let headElemTy : WShape (k + 1) := .forallE tyDomK typeFun
      have hcaptureK : LRS.CaptureDefEqAligned.AtShapes (LR Γ)
          (mcap path) (mx path) (my path) (captureType path)
          argCapK tyDomK := by
        exact capture.lift hk.2.2
      have hheadTyped : headElem.HasType headElemTy := by
        change (WShape.lam elemFun helemNonzero).HasType
          (WShape.forallE tyDomK typeFun)
        rw [WShape.lam_eq_lam']
        apply WShape.HasType.lam
        refine WShape.HasTypeLam.iff'.2 ⟨?_, ?_, fun x => ?_⟩
        · refine WShape.HasTypePi.def.2
            ⟨WShape.HasDom.single.2 (.inl hcaptureK.2.1), ?_⟩
          intro x y hxy
          obtain ⟨rfl, rfl⟩ | ⟨_, rfl, rfl⟩ :=
            WShapeFun.mem_single.1 hxy
          · exact hnextKTy.isType
          · exact .bot' .sort
        · exact WShape.HasDom.single.2 (.inl hcaptureK.2.1)
        · simp only [elemFun, typeFun, WShapeFun.single_app]
          split <;> [exact hnextKTy; exact .bot' (.bot' .sort)]
      have hheadLeK : headElem ≤ .lam' (g.lift k) := by
        change WShape.lam elemFun helemNonzero ≤ .lam' (g.lift k)
        rw [WShape.lam_eq_lam']
        apply WShape.lam'_le_lam'.2
        obtain ⟨x', hx', hmem⟩ := (g.lift k).app_eq argCapK
        exact WShapeFun.single_le.2
          ⟨x', _, hmem, hx', hnextAppK⟩
      have hliftHead : (WShape.lam' (g.lift k)).T ≤
          (WShape.lam g hg).T := by
        have hLift := (TShape.lift_eqv
          (a := (WShape.lam g hg).T)
          (Nat.succ_le_succ hk.1)).1
        rw [WShape.lift_lam hk.1, WShape.lam_eq_lam'] at hLift
        exact hLift
      have hheadLe : headElem.T ≤ (WShape.lam g hg).T :=
        hheadLeK.T.trans hliftHead
      have tailK : LR.FixedHeadShapeChain Γ mcap mx my captureType
          paths nextK nextTyK out outTy :=
        LR.FixedHeadShapeChain.liftHead hk.2.1 hnextTy tail
      have tailApp : LR.FixedHeadShapeChain Γ mcap mx my captureType
          paths (elemFun.app argCapK) (typeFun.app argCapK) out outTy := by
        simpa only [elemFun, typeFun, WShapeFun.single_app,
          WShape.LE.rfl, ↓reduceIte] using tailK
      have chain : LR.FixedHeadShapeChain Γ mcap mx my captureType
          (path :: paths) headElem headElemTy out outTy := by
        exact LR.FixedHeadShapeChain.cons hcaptureK tailApp
      exact ⟨k + 1, headElem, headElemTy, hheadLe,
        hheadTyped, by
          intro hbot
          have happBotSame : (headElem.app argCapK).T ≤
              ((WShape.bot (n := k + 1)).app argCapK).T :=
            TShape.app_mono
              (hbot.trans (TShape.bot_eqv (n := k + 1)).2)
              TShape.LE.rfl
          rw [WShape.bot_app] at happBotSame
          have happBot : (headElem.app argCapK).T ≤ TShape.bot :=
            happBotSame.trans TShape.bot_eqv.1
          apply hnextKNonbot
          simpa only [headElem, WShape.lam_eq_lam', WShape.lam'_app,
            elemFun, WShapeFun.single_app, WShape.LE.rfl, ↓reduceIte]
            using happBot,
        chain⟩

/-- Fold an ordered typed telescope into the logical application chain for
the *same* lower term/type endpoint.

Unlike `ShapeSpine.fixedHeadShapeChain`, this theorem does not choose a fresh
capture representative at each path occurrence.  Its `Captures` argument is
indexed by the exact `argCap`/`tyDom` pair stored in every telescope layer,
and the returned `headElemTy ≤ headTy` proof follows the very same recursive
choices.  Consequently a registered-type witness may be lowered to the
returned head type without losing the capture chain that will consume it.

Stated for the monotone packed telescope.  The base is the only place the
terminal index is read at all, and it is read twice: once for the caller's own
`out.HasType outTy` (which `WithCapturesLE.nil` now records at the caller's
observation) and once for the returned bound `headElemTy.T ≤ headTy` (which
now goes through the base comparison instead of an index equality).  The cons
layer is untouched, which is why the exact form below is a one-line
corollary. -/
theorem LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCapturesLE.fixedHeadShapeChain
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {paths : List p.Path} {head headTy : TShape}
    {outLevel : Nat} {out outTy : WShape outLevel}
    {outShape outTyShape : TShape}
    (H : LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCapturesLE
      (m2 := mcap)
      (fun {n} path (elemShape typeShape : WShape n) =>
        LRS.CaptureDefEqAligned.AtShapes (LR Γ)
          (mcap path) (mx path) (my path) (captureType path)
          elemShape typeShape)
      head paths outShape headTy outTyShape)
    (houtShapeEq : out.T = outShape)
    (houtTyShapeEq : outTy.T = outTyShape)
    (houtNonbot : ¬out.T ≤ TShape.bot) :
    ∃ (headLevel : Nat) (headElem headElemTy : WShape headLevel),
      headElem.T ≤ head ∧ headElem.HasType headElemTy ∧
        headElemTy.T ≤ headTy ∧ ¬headElem.T ≤ TShape.bot ∧
        LR.FixedHeadShapeChain Γ mcap mx my captureType
          paths headElem headElemTy out outTy := by
  revert out outTy
  revert outLevel
  let Motive := fun (head : TShape) (paths : List p.Path)
      (outShape headTy outTyShape : TShape)
      (_ : LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCapturesLE
        (m2 := mcap)
        (fun {n} path (elemShape typeShape : WShape n) =>
          LRS.CaptureDefEqAligned.AtShapes (LR Γ)
            (mcap path) (mx path) (my path) (captureType path)
            elemShape typeShape)
        head paths outShape headTy outTyShape) =>
      ∀ (outLevel : Nat) (out outTy : WShape outLevel),
        out.T = outShape → outTy.T = outTyShape →
        (¬out.T ≤ TShape.bot) →
        ∃ (headLevel : Nat) (headElem headElemTy : WShape headLevel),
          headElem.T ≤ head ∧ headElem.HasType headElemTy ∧
            headElemTy.T ≤ headTy ∧ ¬headElem.T ≤ TShape.bot ∧
            LR.FixedHeadShapeChain Γ mcap mx my captureType
              paths headElem headElemTy out outTy
  change Motive head paths outShape headTy outTyShape H
  refine LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCapturesLE.rec
    (motive := Motive) ?_ ?_ H
  · intro head headTy terminalTy htyped hle
    intro outLevel out outTy houtShapeEq houtTyShapeEq houtNonbot
    have houtLe : out.T ≤ head := by
      rw [houtShapeEq]
      exact TShape.LE.rfl
    have houtTyLe : outTy.T ≤ headTy := by
      rw [houtTyShapeEq]
      exact hle
    have houtTyped : out.HasType outTy := by
      apply WShape.HasType.T_iff.1
      rw [houtShapeEq, houtTyShapeEq]
      exact htyped
    exact ⟨outLevel, out, outTy, houtLe, houtTyped, houtTyLe,
      houtNonbot, LR.FixedHeadShapeChain.nil⟩
  · intro n f a m outT path paths tyDom tyFun argCap outTyT
      harg happ hargCap hcapDom capture tail ih
    intro outLevel out outTy houtShapeEq houtTyShapeEq houtNonbot
    obtain ⟨nextLevel, next, nextTy, hnext, hnextTy,
      hnextTyLe, hnextNonbot, tailChain⟩ :=
      ih outLevel out outTy houtShapeEq houtTyShapeEq houtNonbot
    have hnextApp : next.T ≤ (f.app a).T := hnext.trans happ
    cases f using WShape.casesOn' with
    | bot => exact (hnextNonbot (hnextApp.trans TShape.bot_eqv.1)).elim
    | sort => exact (hnextNonbot (hnextApp.trans TShape.bot_eqv.1)).elim
    | forallE => exact (hnextNonbot (hnextApp.trans TShape.bot_eqv.1)).elim
    | ctor => exact (hnextNonbot (hnextApp.trans TShape.bot_eqv.1)).elim
    | indTy => exact (hnextNonbot (hnextApp.trans TShape.bot_eqv.1)).elim
    | @lam g hg =>
      let k := max n nextLevel
      have hk : n ≤ k ∧ nextLevel ≤ k := by
        dsimp [k]
        omega
      let aK : WShape k := a.lift k
      let argCapK : WShape k := argCap.lift k
      let tyDomK : WShape k := tyDom.lift k
      let nextK : WShape k := next.lift k
      let nextTyK : WShape k := nextTy.lift k
      let elemFun : WShapeFun k := .single argCapK nextK
      let typeFun : WShapeFun k := .single argCapK nextTyK
      have hargCapK : aK ≤ argCapK :=
        WShape.lift_mono hk.1 hargCap
      have hnextAppK : nextK ≤ (g.lift k).app argCapK := by
        have hnextApp' : next.T ≤ ((WShape.lam g hg).app a).T := by
          simpa using hnextApp
        have hmono : ((WShape.lam g hg).app a).T ≤
            ((WShape.lam (g.lift k)
              (WShapeFun.NonZero.lift_iff hk.1 |>.2 hg)).app argCapK).T := by
          apply TShape.app_mono
          · have hLift := (TShape.lift_eqv
              (a := (WShape.lam g hg).T)
              (Nat.succ_le_succ hk.1)).2
            rw [WShape.lift_lam hk.1] at hLift
            exact hLift
          · exact hargCap.T.trans (TShape.lift_eqv hk.1).2
        have hT : next.T ≤ ((g.lift k).app argCapK).T := by
          simpa [WShape.lam_eq_lam'] using hnextApp'.trans hmono
        have hTK := (TShape.LE.def hk.2 (Nat.le_refl k)).1 hT
        simpa only [nextK, WShape.lift_self] using hTK
      have hnextTyKLe : nextTyK ≤ (tyFun.lift k).app argCapK := by
        have hTK := (TShape.LE.def
          (a := nextTy.T) (b := (tyFun.app argCap).T)
          hk.2 hk.1).1 hnextTyLe
        simpa only [nextTyK, argCapK, WShape.lift_self,
          WShapeFun.lift_app hk.1] using hTK
      have hnextKTy : nextK.HasType nextTyK :=
        (WShape.HasType.lift hk.2).2 hnextTy
      have hnextKNonbot : ¬nextK.T ≤ TShape.bot := by
        intro hbot
        exact hnextNonbot <|
          (TShape.lift_eqv hk.2).2.trans
            (hbot.trans TShape.bot_eqv.1)
      have helemNonzero : elemFun.NonZero := by
        rw [WShapeFun.NonZero.iff]
        refine ⟨(argCapK, nextK),
          WShapeFun.mem_single.2 (.inl rfl), ?_⟩
        intro hbot
        exact hnextKNonbot <|
          (WShape.LE.T hbot).trans TShape.bot_eqv.1
      let headElem : WShape (k + 1) := .lam elemFun helemNonzero
      let headElemTy : WShape (k + 1) := .forallE tyDomK typeFun
      have hcaptureK : LRS.CaptureDefEqAligned.AtShapes (LR Γ)
          (mcap path) (mx path) (my path) (captureType path)
          argCapK tyDomK := by
        exact capture.lift hk.1
      have hheadTyped : headElem.HasType headElemTy := by
        change (WShape.lam elemFun helemNonzero).HasType
          (WShape.forallE tyDomK typeFun)
        rw [WShape.lam_eq_lam']
        apply WShape.HasType.lam
        refine WShape.HasTypeLam.iff'.2 ⟨?_, ?_, fun x => ?_⟩
        · refine WShape.HasTypePi.def.2
            ⟨WShape.HasDom.single.2 (.inl hcaptureK.2.1), ?_⟩
          intro x y hxy
          obtain ⟨rfl, rfl⟩ | ⟨_, rfl, rfl⟩ :=
            WShapeFun.mem_single.1 hxy
          · exact hnextKTy.isType
          · exact .bot' .sort
        · exact WShape.HasDom.single.2 (.inl hcaptureK.2.1)
        · simp only [elemFun, typeFun, WShapeFun.single_app]
          split <;> [exact hnextKTy; exact .bot' (.bot' .sort)]
      have hheadLeK : headElem ≤ .lam' (g.lift k) := by
        change WShape.lam elemFun helemNonzero ≤ .lam' (g.lift k)
        rw [WShape.lam_eq_lam']
        apply WShape.lam'_le_lam'.2
        obtain ⟨x', hx', hmem⟩ := (g.lift k).app_eq argCapK
        exact WShapeFun.single_le.2
          ⟨x', _, hmem, hx', hnextAppK⟩
      have hliftHead : (WShape.lam' (g.lift k)).T ≤
          (WShape.lam g hg).T := by
        have hLift := (TShape.lift_eqv
          (a := (WShape.lam g hg).T)
          (Nat.succ_le_succ hk.1)).1
        rw [WShape.lift_lam hk.1, WShape.lam_eq_lam'] at hLift
        exact hLift
      have hheadLe : headElem.T ≤ (WShape.lam g hg).T :=
        hheadLeK.T.trans hliftHead
      have htypeFunLe : typeFun ≤ tyFun.lift k := by
        obtain ⟨x', hx', hmem⟩ := (tyFun.lift k).app_eq argCapK
        exact WShapeFun.single_le.2
          ⟨x', _, hmem, hx', hnextTyKLe⟩
      have hheadTyLeK : headElemTy ≤
          .forallE tyDomK (tyFun.lift k) := by
        exact WShape.forallE_le_forallE.2 ⟨.rfl, htypeFunLe⟩
      have hliftHeadTy : (WShape.forallE tyDomK (tyFun.lift k)).T ≤
          (WShape.forallE tyDom tyFun).T := by
        have hLift := (TShape.lift_eqv
          (a := (WShape.forallE tyDom tyFun).T)
          (Nat.succ_le_succ hk.1)).1
        rw [WShape.lift_forallE hk.1] at hLift
        exact hLift
      have hheadTyLe : headElemTy.T ≤
          (WShape.forallE tyDom tyFun).T :=
        hheadTyLeK.T.trans hliftHeadTy
      have tailK : LR.FixedHeadShapeChain Γ mcap mx my captureType
          paths nextK nextTyK out outTy :=
        LR.FixedHeadShapeChain.liftHead hk.2 hnextTy tailChain
      have tailApp : LR.FixedHeadShapeChain Γ mcap mx my captureType
          paths (elemFun.app argCapK) (typeFun.app argCapK)
            out outTy := by
        simpa only [elemFun, typeFun, WShapeFun.single_app,
          WShape.LE.rfl, ↓reduceIte] using tailK
      have chain : LR.FixedHeadShapeChain Γ mcap mx my captureType
          (path :: paths) headElem headElemTy out outTy := by
        exact LR.FixedHeadShapeChain.cons hcaptureK tailApp
      exact ⟨k + 1, headElem, headElemTy, hheadLe,
        hheadTyped, hheadTyLe, by
          intro hbot
          have happBotSame : (headElem.app argCapK).T ≤
              ((WShape.bot (n := k + 1)).app argCapK).T :=
            TShape.app_mono
              (hbot.trans (TShape.bot_eqv (n := k + 1)).2)
              TShape.LE.rfl
          rw [WShape.bot_app] at happBotSame
          have happBot : (headElem.app argCapK).T ≤ TShape.bot :=
            happBotSame.trans TShape.bot_eqv.1
          apply hnextKNonbot
          simpa only [headElem, WShape.lam_eq_lam', WShape.lam'_app,
            elemFun, WShapeFun.single_app, WShape.LE.rfl, ↓reduceIte]
            using happBot,
        chain⟩

/-- The exact packed telescope folds through the monotone one.  Statement
unchanged; every existing consumer applies verbatim. -/
theorem LE_Interp.RHS.ShapeSpine.TypedTelescope.fixedHeadShapeChain
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {paths : List p.Path} {head headTy : TShape}
    {outLevel : Nat} {out outTy : WShape outLevel}
    {outShape outTyShape : TShape}
    (H : LE_Interp.RHS.ShapeSpine.TypedTelescope.WithCaptures
      (m2 := mcap)
      (fun {n} path (elemShape typeShape : WShape n) =>
        LRS.CaptureDefEqAligned.AtShapes (LR Γ)
          (mcap path) (mx path) (my path) (captureType path)
          elemShape typeShape)
      head paths outShape headTy outTyShape)
    (houtShapeEq : out.T = outShape)
    (houtTyShapeEq : outTy.T = outTyShape)
    (houtNonbot : ¬out.T ≤ TShape.bot) :
    ∃ (headLevel : Nat) (headElem headElemTy : WShape headLevel),
      headElem.T ≤ head ∧ headElem.HasType headElemTy ∧
        headElemTy.T ≤ headTy ∧ ¬headElem.T ≤ TShape.bot ∧
        LR.FixedHeadShapeChain Γ mcap mx my captureType
          paths headElem headElemTy out outTy :=
  H.toLE.fixedHeadShapeChain houtShapeEq houtTyShapeEq houtNonbot

/-- A canonical logical application chain over one ordered capture list.

Every constructor records the exact function/type observations used by one
`LR.DefEq.app` step and recurses at the predecessor shape level selected by
that application.  The terminal constructor pins both shapes and the result
syntax literally.  Thus this structure contains no conversion or endpoint
coercion; those belong to the separate bridge from `PathSpineWF` and the
semantic typed telescope. -/
inductive LR.FixedHeadChain (Γ : List SExpr)
    {p : Pattern} (mcap : p.Path → TShape)
    (mx my captureType : p.Path → SExpr) :
    ∀ (paths : List p.Path) (headType resultType : SExpr)
      {headLevel : Nat}, WShape headLevel → WShape headLevel →
      ∀ {outLevel : Nat}, WShape outLevel → WShape outLevel → Prop where
  | nil {A : SExpr} {n : Nat} {out outTy : WShape n} :
      LR.FixedHeadChain Γ mcap mx my captureType
        [] A A out outTy out outTy
  | cons
      {n : Nat} {path : p.Path} {paths : List p.Path}
      {body resultType : SExpr}
      {termFun typeFun : WShapeFun n} {hterm : termFun.NonZero}
      {argCap tyDom : WShape n}
      {outLevel : Nat} {out outTy : WShape outLevel}
      (capture : LRS.CaptureDefEqAligned.AtShapes (LR Γ)
        (mcap path) (mx path) (my path) (captureType path)
        argCap tyDom)
      (tail : LR.FixedHeadChain Γ mcap mx my captureType
        paths (body.inst (mx path)) resultType
        (termFun.app argCap) (typeFun.app argCap) out outTy) :
      LR.FixedHeadChain Γ mcap mx my captureType
        (path :: paths) (.forallE (captureType path) body) resultType
        (.lam termFun hterm) (.forallE tyDom typeFun) out outTy

/-- Fold a canonical fixed-head chain by repeated dependent logical
application.  Shape levels decrease exactly where `LR.DefEq.app` decreases
them; no lift/unlift frame appears in this consumer. -/
theorem LR.FixedHeadChain.apply
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {paths : List p.Path} {headType resultType : SExpr}
    {headLevel : Nat} {head headTy : WShape headLevel}
    {outLevel : Nat} {out outTy : WShape outLevel}
    (H : LR.FixedHeadChain Γ mcap mx my captureType
      paths headType resultType head headTy out outTy)
    {M N : SExpr}
    (hhead : (LR Γ).DefEq M N headType head headTy) :
    (LR Γ).DefEq
      (paths.foldl (fun f path => f.app (mx path)) M)
      (paths.foldl (fun f path => f.app (my path)) N)
      resultType out outTy := by
  induction H generalizing M N with
  | nil => exact hhead
  | cons capture tail ih =>
    simp only [List.foldl_cons]
    exact ih (capture.app hhead)

/-- A conversion-safe logical application chain over one path-indexed
capture spine.

Every application node stores the weak-head Pi telescope exposed for the
*current declared type*.  Thus a raw `PathSpineWF.conv` is normalized by the
producer before it reaches this certificate; the consumer never promotes
that raw equality to a same-level semantic equality.  The only semantic
conversion fields are the exact lower-level domain and terminal alignments
needed by dependent application.  `liftHead` records canonical upward shape
alignment without changing either syntax endpoint or the exact output. -/
inductive LR.FixedHeadExposedChain (Γ : List SExpr)
    {p : Pattern} (mcap : p.Path → TShape)
    (mx my captureType : p.Path → SExpr) :
    ∀ (paths : List p.Path) (headType resultType : SExpr)
      {headLevel : Nat}, WShape headLevel → WShape headLevel →
      ∀ {outLevel : Nat}, WShape outLevel → WShape outLevel → Prop where
  | nil {A : SExpr} {n : Nat} {out outTy : WShape n} :
      LR.FixedHeadExposedChain Γ mcap mx my captureType
        [] A A out outTy out outTy
  | cons
      {n : Nat} {path : p.Path} {paths : List p.Path}
      {headType A₁ A₂ resultType : SExpr} {u : SLevel}
      {termFun typeFun : WShapeFun n} {hterm : termFun.NonZero}
      {argCap tyDom : WShape n}
      {outLevel : Nat} {out outTy : WShape outLevel}
      (headRed : WHRedS Γ headType (.forallE A₁ A₂))
      (capture : LRS.CaptureDefEqAligned.AtShapes (LR Γ)
        (mcap path) (mx path) (my path) (captureType path)
        argCap tyDom)
      (domainRaw : TypeDefEqPath Γ (captureType path) A₁ u)
      (domainRel : (LR Γ).TyDefEq (captureType path) A₁ tyDom)
      (tail : LR.FixedHeadExposedChain Γ mcap mx my captureType
        paths (A₂.inst (mx path)) resultType
        (termFun.app argCap) (typeFun.app argCap) out outTy) :
      LR.FixedHeadExposedChain Γ mcap mx my captureType
        (path :: paths) headType resultType
        (.lam termFun hterm) (.forallE tyDom typeFun) out outTy
  | liftHead
      {n n' : Nat} {head headTy : WShape n}
      {paths : List p.Path} {headType resultType : SExpr}
      {outLevel : Nat} {out outTy : WShape outLevel}
      (le : n ≤ n') (htyped : head.HasType headTy)
      (tail : LR.FixedHeadExposedChain Γ mcap mx my captureType
        paths headType resultType head headTy out outTy) :
      LR.FixedHeadExposedChain Γ mcap mx my captureType
        paths headType resultType
        (head.lift n') (headTy.lift n') out outTy
  | ret
      {paths : List p.Path} {headType resultType resultType' : SExpr}
      {u : SLevel}
      {headLevel : Nat} {head headTy : WShape headLevel}
      {outLevel : Nat} {out outTy : WShape outLevel}
      (tail : LR.FixedHeadExposedChain Γ mcap mx my captureType
        paths headType resultType head headTy out outTy)
      (resultRaw : TypeDefEqPath Γ resultType resultType' u)
      (resultRel : (LR Γ).TyDefEq resultType resultType' outTy) :
      LR.FixedHeadExposedChain Γ mcap mx my captureType
        paths headType resultType' head headTy out outTy

/-- Change the declared type at the fixed head after an exact semantic type
alignment has already been constructed.

This is the consumer-side operation needed for `PathSpineWF.conv`.  It does
not derive a logical relation from the raw equality: the producer must pass
that relation explicitly (and, in the adequacy construction, obtains it only
from the strictly-smaller-depth provenance restart).  At a nonempty spine the
stored Pi observation exposes both sides of the supplied type relation;
weak-head determinism identifies its right observation with the telescope
already retained by the chain. -/
theorem LR.FixedHeadExposedChain.rehead
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {paths : List p.Path} {headType headType' resultType : SExpr}
    {headLevel : Nat} {head headTy : WShape headLevel}
    {outLevel : Nat} {out outTy : WShape outLevel}
    (H : LR.FixedHeadExposedChain Γ mcap mx my captureType
      paths headType' resultType head headTy out outTy)
    {u : SLevel}
    (hraw : TypeDefEqPath Γ headType headType' u)
    (hrel : (LR Γ).TyDefEq headType headType' headTy) :
    LR.FixedHeadExposedChain Γ mcap mx my captureType
      paths headType resultType head headTy out outTy := by
  induction H generalizing headType u with
  | nil =>
    exact LR.FixedHeadExposedChain.ret
      LR.FixedHeadExposedChain.nil hraw hrel
  | @cons n path paths headType' A₁ A₂ resultType v termFun typeFun
      hterm argCap tyDom outLevel out outTy headRed capture domainRaw
      domainRel tail ih =>
    rw [LR_succ] at hrel
    obtain ⟨B₁, F₁, B₂, F₂, _u₁, _u₂,
      hred₁, hred₂, hdom, hcod, hvalDom, hpi⟩ := hrel
    have hPiEq : SExpr.forallE B₂ F₂ = .forallE A₁ A₂ :=
      hred₂.determ .forallE headRed .forallE
    cases hPiEq
    obtain ⟨_, hdomSymm⟩ := hdom.symm
    let domainRaw' : TypeDefEqPath Γ (captureType path) B₁ v :=
      .trans domainRaw hdomSymm
    let domainRel' : (LR Γ).TyDefEq
        (captureType path) B₁ tyDom :=
      (LR Γ).trans_ty domainRel ((LR Γ).symm_ty hvalDom)
    have hargRaw : IsDefEq Γ (mx path) (my path) B₁ :=
      domainRaw'.defeqDF capture.2.2.2.1
    have hargRel : (LR Γ).DefEq
        (mx path) (my path) B₁ argCap tyDom :=
      (LR Γ).conv domainRel' capture.2.2.2.2
    have hcodInst : TypeDefEqPath Γ
        (F₁.inst (mx path)) (A₂.inst (mx path)) _u₂ := by
      simpa only [SExpr.inst] using hcod.subst
        (Ctx.Subst.one IsDefEq.weakCore IsDefEq.bvar hargRaw.hasType.1)
    have hcodRel : (LR Γ).TyDefEq
        (F₁.inst (mx path)) (A₂.inst (mx path))
        (typeFun.app argCap) :=
      hpi.2 capture.2.1 hargRaw.hasType.1 ((LR Γ).left hargRel)
    exact LR.FixedHeadExposedChain.cons hred₁ capture
      domainRaw' domainRel' (ih hcodInst hcodRel)
  | liftHead le htyped tail ih =>
    exact LR.FixedHeadExposedChain.liftHead le htyped <|
      ih hraw ((LR.TyDefEq.lift le htyped.isType).1 hrel)
  | ret tail resultRaw resultRel ih =>
    exact LR.FixedHeadExposedChain.ret
      (ih hraw hrel) resultRaw resultRel

/-- The semantic alignments for one concrete path-indexed typing spine.

This certificate zips a syntax-independent `FixedHeadShapeChain` with the
*actual* `PathSpineWF` derivation used by the generated RHS.  Only conversion
edges present in that derivation receive semantic payloads.  In particular,
there is no callback that can turn an arbitrary raw equality into a logical
type equality; the adequacy producer must construct each `headRel`,
`domainRel`, and `resultRel` at its reviewed smaller-depth boundary. -/
inductive LR.FixedHeadPathSemantics (Γ : List SExpr)
    {p : Pattern} (mcap : p.Path → TShape)
    (mx my captureType : p.Path → SExpr) :
    ∀ {paths : List p.Path} {headType resultType : SExpr}
      {headLevel : Nat} {head headTy : WShape headLevel}
      {outLevel : Nat} {out outTy : WShape outLevel},
      LR.FixedHeadShapeChain Γ mcap mx my captureType
        paths head headTy out outTy →
      SExpr.PathSpineWF Γ mx captureType
        headType paths resultType → Prop where
  | nil {A : SExpr} {n : Nat} {out outTy : WShape n} :
      LR.FixedHeadPathSemantics Γ mcap mx my captureType
        (LR.FixedHeadShapeChain.nil (out := out) (outTy := outTy))
        (SExpr.PathSpineWF.nil (A := A))
  | cons
      {n : Nat} {path : p.Path} {paths : List p.Path}
      {A₁ A₂ resultType : SExpr} {u : SLevel}
      {termFun typeFun : WShapeFun n} {hterm : termFun.NonZero}
      {argCap tyDom : WShape n}
      {outLevel : Nat} {out outTy : WShape outLevel}
      {capture : LRS.CaptureDefEqAligned.AtShapes (LR Γ)
        (mcap path) (mx path) (my path) (captureType path)
        argCap tyDom}
      {tailShape : LR.FixedHeadShapeChain Γ mcap mx my captureType
        paths (termFun.app argCap) (typeFun.app argCap) out outTy}
      {domainRaw : IsDefEq Γ (captureType path) A₁ (.sort u)}
      {tailRaw : SExpr.PathSpineWF Γ mx captureType
        (A₂.inst (mx path)) paths resultType}
      (domainRel : (LR Γ).TyDefEq (captureType path) A₁ tyDom)
      (tail : LR.FixedHeadPathSemantics Γ mcap mx my captureType
        tailShape tailRaw) :
      LR.FixedHeadPathSemantics Γ mcap mx my captureType
        (LR.FixedHeadShapeChain.cons (hterm := hterm) capture tailShape)
        (SExpr.PathSpineWF.cons domainRaw tailRaw)
  | liftHead
      {n n' : Nat} {head headTy : WShape n}
      {paths : List p.Path} {headType resultType : SExpr}
      {outLevel : Nat} {out outTy : WShape outLevel}
      {le : n ≤ n'} {htyped : head.HasType headTy}
      {tailShape : LR.FixedHeadShapeChain Γ mcap mx my captureType
        paths head headTy out outTy}
      {raw : SExpr.PathSpineWF Γ mx captureType
        headType paths resultType}
      (tail : LR.FixedHeadPathSemantics Γ mcap mx my captureType
        tailShape raw) :
      LR.FixedHeadPathSemantics Γ mcap mx my captureType
        (LR.FixedHeadShapeChain.liftHead le htyped tailShape) raw
  | conv
      {paths : List p.Path} {headType headType' resultType : SExpr}
      {u : SLevel}
      {headLevel : Nat} {head headTy : WShape headLevel}
      {outLevel : Nat} {out outTy : WShape outLevel}
      {shape : LR.FixedHeadShapeChain Γ mcap mx my captureType
        paths head headTy out outTy}
      {headRaw : IsDefEq Γ headType headType' (.sort u)}
      {tailRaw : SExpr.PathSpineWF Γ mx captureType
        headType' paths resultType}
      (headRel : (LR Γ).TyDefEq headType headType' headTy)
      (tail : LR.FixedHeadPathSemantics Γ mcap mx my captureType
        shape tailRaw) :
      LR.FixedHeadPathSemantics Γ mcap mx my captureType shape
        (SExpr.PathSpineWF.conv headRaw tailRaw)
  | ret
      {paths : List p.Path} {headType resultType resultType' : SExpr}
      {u : SLevel}
      {headLevel : Nat} {head headTy : WShape headLevel}
      {outLevel : Nat} {out outTy : WShape outLevel}
      {shape : LR.FixedHeadShapeChain Γ mcap mx my captureType
        paths head headTy out outTy}
      {tailRaw : SExpr.PathSpineWF Γ mx captureType
        headType paths resultType}
      {resultRaw : IsDefEq Γ resultType resultType' (.sort u)}
      (resultRel : (LR Γ).TyDefEq resultType resultType' outTy)
      (tail : LR.FixedHeadPathSemantics Γ mcap mx my captureType
        shape tailRaw) :
      LR.FixedHeadPathSemantics Γ mcap mx my captureType shape
        (SExpr.PathSpineWF.ret tailRaw resultRaw)

/-- Zip an empty concrete spine with a shape chain containing only terminal
and head-lift frames.  The explicit path-index equality keeps the structural
recursor general enough to recognize each `liftHead` tail as a subderivation. -/
theorem LR.FixedHeadShapeChain.pathSemanticsNil
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {shapePaths : List p.Path} {A : SExpr}
    {headLevel : Nat} {head headTy : WShape headLevel}
    {outLevel : Nat} {out outTy : WShape outLevel}
    (shape : LR.FixedHeadShapeChain Γ mcap mx my captureType
      shapePaths head headTy out outTy)
    (hpaths : shapePaths = []) :
    LR.FixedHeadPathSemantics Γ mcap mx my captureType
      (hpaths ▸ shape) (SExpr.PathSpineWF.nil (A := A)) := by
  induction shape with
  | nil =>
    cases hpaths
    exact LR.FixedHeadPathSemantics.nil
  | cons capture tail =>
    cases hpaths
  | liftHead le htyped tail ih =>
    cases hpaths
    exact LR.FixedHeadPathSemantics.liftHead
      (le := le) (htyped := htyped)
      (raw := SExpr.PathSpineWF.nil (A := A))
      (ih rfl)

/-- Zip one concrete application edge after stripping any leading head-lift
frames from the syntax-independent shape chain. -/
theorem LR.FixedHeadShapeChain.pathSemanticsCons
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {shapePaths : List p.Path}
    {path : p.Path} {paths : List p.Path}
    {A₁ A₂ resultType : SExpr} {u : SLevel}
    {headLevel : Nat} {head headTy : WShape headLevel}
    {outLevel : Nat} {out outTy : WShape outLevel}
    (shape : LR.FixedHeadShapeChain Γ mcap mx my captureType
      shapePaths head headTy out outTy)
    (hpaths : shapePaths = path :: paths)
    (domainRaw : IsDefEq Γ (captureType path) A₁ (.sort u))
    (tailRaw : SExpr.PathSpineWF Γ mx captureType
      (A₂.inst (mx path)) paths resultType)
    (headRel : (LR Γ).TyDefEq
      (.forallE A₁ A₂) (.forallE A₁ A₂) headTy)
    (convert : ∀ {n : Nat} {A B : SExpr} {v : SLevel}
        {a : WShape n},
      IsDefEq Γ A B (.sort v) →
      (LR Γ).TyDefEq A A a →
      (LR Γ).TyDefEq A B a)
    (tailSemantics : ∀ {tailLevel : Nat}
        {tailHead tailHeadTy : WShape tailLevel},
      (tailShape : LR.FixedHeadShapeChain Γ mcap mx my captureType
        paths tailHead tailHeadTy out outTy) →
      (LR Γ).TyDefEq
        (A₂.inst (mx path)) (A₂.inst (mx path)) tailHeadTy →
      LR.FixedHeadPathSemantics Γ mcap mx my captureType
        tailShape tailRaw) :
    LR.FixedHeadPathSemantics Γ mcap mx my captureType
      (hpaths ▸ shape) (SExpr.PathSpineWF.cons domainRaw tailRaw) := by
  induction shape with
  | nil =>
    cases hpaths
  | @cons n path₀ paths₀ termFun typeFun hterm argCap tyDom
      outLevel out outTy capture tail =>
    cases hpaths
    rw [LR_succ] at headRel
    obtain ⟨B₁, F₁, B₂, F₂, _u₁, _u₂,
      hred₁, hred₂, _hdom, _hcod, _domainSelf, hpi⟩ := headRel
    have hPi₁ : SExpr.forallE B₁ F₁ = .forallE A₁ A₂ :=
      hred₁.determ .forallE .rfl .forallE
    have hPi₂ : SExpr.forallE B₂ F₂ = .forallE A₁ A₂ :=
      hred₂.determ .forallE .rfl .forallE
    cases hPi₁
    cases hPi₂
    have domainRel : (LR Γ).TyDefEq
        (captureType path) A₁ tyDom :=
      convert domainRaw capture.2.2.1
    have argRaw : IsDefEq Γ (mx path) (my path) A₁ :=
      domainRaw.defeqDF capture.2.2.2.1
    have argRel : (LR Γ).DefEq
        (mx path) (my path) A₁ argCap tyDom :=
      (LR Γ).conv domainRel capture.2.2.2.2
    have tailHeadRel : (LR Γ).TyDefEq
        (A₂.inst (mx path)) (A₂.inst (mx path))
        (typeFun.app argCap) :=
      hpi.2 capture.2.1 argRaw.hasType.1 ((LR Γ).left argRel)
    exact LR.FixedHeadPathSemantics.cons
      (u := u) (capture := capture)
      (domainRaw := domainRaw) (tailRaw := tailRaw)
      domainRel (tailSemantics tail tailHeadRel)
  | liftHead le htyped tail ih =>
    cases hpaths
    exact LR.FixedHeadPathSemantics.liftHead
      (le := le) (htyped := htyped)
      (raw := SExpr.PathSpineWF.cons domainRaw tailRaw) <|
      ih rfl ((LR.TyDefEq.lift le htyped.isType).1 headRel)
        tailSemantics

/-- Add the semantic payloads to one concrete path-indexed typing spine.

The conversion callback is invoked only for an equality edge occurring in
the supplied `PathSpineWF`, and only after the source endpoint is already
known to be a valid logical type at the exact shape threaded by the fixed
head chain.  Its destination self-validity is recovered from the returned
heterogeneous edge.  This is the structural half of the ordered producer;
the adequacy construction supplies `convert` from its strictly-smaller-depth
provenance restart. -/
theorem LR.FixedHeadShapeChain.pathSemantics
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {paths : List p.Path} {headType resultType : SExpr}
    {headLevel : Nat} {head headTy : WShape headLevel}
    {outLevel : Nat} {out outTy : WShape outLevel}
    (shape : LR.FixedHeadShapeChain Γ mcap mx my captureType
      paths head headTy out outTy)
    (raw : SExpr.PathSpineWF Γ mx captureType
      headType paths resultType)
    (headRel : (LR Γ).TyDefEq headType headType headTy)
    (resultRel : (LR Γ).TyDefEq resultType resultType outTy)
    (convert : ∀ {n : Nat} {A B : SExpr} {u : SLevel}
        {a : WShape n},
      IsDefEq Γ A B (.sort u) →
      (LR Γ).TyDefEq A A a →
      (LR Γ).TyDefEq A B a) :
    LR.FixedHeadPathSemantics Γ mcap mx my captureType shape raw := by
  induction raw generalizing headLevel head headTy with
  | @nil A =>
    simpa only using shape.pathSemanticsNil (A := A) rfl
  | @cons path A₁ u paths resultType A₂ domainRaw tailRaw ih =>
    exact shape.pathSemanticsCons rfl domainRaw tailRaw headRel convert
      (fun tail tailHeadRel => ih tail tailHeadRel resultRel)
  | @conv headType headType' u paths resultType headRaw tailRaw ih =>
    have headCross : (LR Γ).TyDefEq headType headType' headTy :=
      convert headRaw headRel
    have tailHeadRel : (LR Γ).TyDefEq headType' headType' headTy :=
      (LR Γ).left_ty ((LR Γ).symm_ty headCross)
    exact LR.FixedHeadPathSemantics.conv
      (u := u) (headRaw := headRaw) (tailRaw := tailRaw) headCross
      (ih shape tailHeadRel resultRel)
  | @ret headType paths resultType resultType' u tailRaw resultRaw ih =>
    have resultCrossRev : (LR Γ).TyDefEq
        resultType' resultType outTy :=
      convert resultRaw.symm resultRel
    have tailResultRel : (LR Γ).TyDefEq
        resultType resultType outTy :=
      (LR Γ).left_ty ((LR Γ).symm_ty resultCrossRev)
    exact LR.FixedHeadPathSemantics.ret
      (u := u) (tailRaw := tailRaw) (resultRaw := resultRaw)
      ((LR Γ).symm_ty resultCrossRev)
      (ih shape headRel tailResultRel)

/-- Forget the producer provenance and obtain the canonical exposed-head
application certificate consumed by the logical fold. -/
theorem LR.FixedHeadPathSemantics.exposed
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {paths : List p.Path} {headType resultType : SExpr}
    {headLevel : Nat} {head headTy : WShape headLevel}
    {outLevel : Nat} {out outTy : WShape outLevel}
    {shape : LR.FixedHeadShapeChain Γ mcap mx my captureType
      paths head headTy out outTy}
    {raw : SExpr.PathSpineWF Γ mx captureType
      headType paths resultType}
    (H : LR.FixedHeadPathSemantics Γ mcap mx my captureType shape raw) :
    LR.FixedHeadExposedChain Γ mcap mx my captureType
      paths headType resultType head headTy out outTy := by
  induction H with
  | nil => exact LR.FixedHeadExposedChain.nil
  | @cons n path paths A₁ A₂ resultType u termFun typeFun hterm
      argCap tyDom outLevel out outTy capture tailShape domainRaw tailRaw
      domainRel tail ih =>
    exact LR.FixedHeadExposedChain.cons .rfl capture
      (.single domainRaw) domainRel ih
  | @liftHead n n' head headTy paths headType resultType outLevel out outTy
      le htyped tailShape raw tail ih =>
    exact LR.FixedHeadExposedChain.liftHead le htyped ih
  | @conv paths headType headType' resultType u headLevel head headTy
      outLevel out outTy shape headRaw tailRaw headRel tail ih =>
    exact ih.rehead (.single headRaw) headRel
  | @ret paths headType resultType resultType' u headLevel head headTy
      outLevel out outTy shape tailRaw resultRaw resultRel tail ih =>
    exact LR.FixedHeadExposedChain.ret ih (.single resultRaw) resultRel

/-- Fold the exposed-head fixed-head certificate.

At an application node `app_exposed` independently reveals the Pi telescope
stored by the function relation.  Weak-head determinism identifies it with
the producer's retained telescope, after which the exact domain conversion
retypes the aligned capture.  In particular there is no semantic analogue of
`PathSpineWF.conv` in this induction. -/
theorem LR.FixedHeadExposedChain.apply
    {p : Pattern} {mcap : p.Path → TShape}
    {mx my captureType : p.Path → SExpr}
    {paths : List p.Path} {headType resultType : SExpr}
    {headLevel : Nat} {head headTy : WShape headLevel}
    {outLevel : Nat} {out outTy : WShape outLevel}
    (H : LR.FixedHeadExposedChain Γ mcap mx my captureType
      paths headType resultType head headTy out outTy)
    {M N : SExpr}
    (hhead : (LR Γ).DefEq M N headType head headTy) :
    (LR Γ).DefEq
      (paths.foldl (fun f path => f.app (mx path)) M)
      (paths.foldl (fun f path => f.app (my path)) N)
      resultType out outTy := by
  induction H generalizing M N with
  | nil => exact hhead
  | @cons n path paths headType A₁ A₂ resultType u termFun typeFun
      hterm argCap tyDom outLevel out outTy headRed capture domainRaw
      domainRel tail ih =>
    simp only [List.foldl_cons]
    rw [LR_succ] at hhead
    obtain ⟨B, F, _u, _v, hred, _hB, _hValB, _hF, _hPi, happ⟩ :=
      LRS.DefEq.app_exposed hhead capture.2.1
    have hPiEq : SExpr.forallE B F = .forallE A₁ A₂ :=
      hred.determ .forallE headRed .forallE
    cases hPiEq
    apply ih
    exact happ
      (domainRaw.defeqDF capture.2.2.2.1)
      ((LR Γ).conv domainRel capture.2.2.2.2)
  | liftHead le htyped tail ih =>
    exact ih ((LR.DefEq.lift le htyped).1 hhead)
  | ret tail _resultRaw resultRel ih =>
    exact (LR Γ).conv resultRel (ih hhead)

/-- The chosen type of an existential capture gives its aligned form. -/
theorem LRS.CaptureDefEqAt.Witness.aligned
    (H : CaptureDefEqAt.Witness IH m x y) :
    CaptureDefEqAligned IH m x y H.typeExpr :=
  ⟨H.elemShape, H.typeShape, H.shape, H.hasType,
    H.typeRelated, H.defeq, H.related⟩

/-- Forget a fixed capture type back to the existential packaging. -/
theorem LRS.CaptureDefEqAligned.toCapture
    (H : CaptureDefEqAligned IH m x y typeExpr) :
    CaptureDefEqAt IH m x y := by
  rcases H with ⟨elemShape, typeShape, hshape, htype, hty, hxy, hrel⟩
  exact ⟨elemShape, typeShape, typeExpr,
    hshape, htype, hty, hxy, hrel⟩

theorem LRS.CaptureDefEqAligned.mono (hle : m ≤ m') :
    CaptureDefEqAligned IH m' x y typeExpr →
      CaptureDefEqAligned IH m x y typeExpr := by
  rintro ⟨elemShape, typeShape, hshape, htype, hty, hxy, hrel⟩
  exact ⟨elemShape, typeShape, hle.trans hshape,
    htype, hty, hxy, hrel⟩

theorem LRS.CaptureDefEqAligned.lift
    {IH : LogRel Γ n} {IH' : LogRel Γ n'} (le : n ≤ n')
    (hliftTy : ∀ {A B : SExpr} {a : WShape n}, a.HasType .type →
      (IH'.TyDefEq A B (a.lift n') ↔ IH.TyDefEq A B a))
    (hlift : ∀ {M N A : SExpr} {m a : WShape n}, m.HasType a →
      (IH'.DefEq M N A (m.lift n') (a.lift n') ↔ IH.DefEq M N A m a)) :
    CaptureDefEqAligned IH cap x y typeExpr →
      CaptureDefEqAligned IH' cap x y typeExpr := by
  rintro ⟨elemShape, typeShape, hshape, htype, hty, hxy, hrel⟩
  exact ⟨elemShape.lift n', typeShape.lift n',
    hshape.trans (TShape.lift_eqv le).2,
    (WShape.HasType.lift le).2 htype,
    (hliftTy htype.isType).2 hty, hxy, (hlift htype).2 hrel⟩

/-- Rebase an aligned capture through the packaged equivalence used by a
target-level constructor continuation. -/
theorem LRS.CaptureDefEqAligned.rebase
    {IH : LogRel Γ n} {IH' : LogRel Γ n'} {le : n ≤ n'}
    (E : LogRel.LiftEquiv IH IH' le) :
    CaptureDefEqAligned IH cap x y typeExpr →
      CaptureDefEqAligned IH' cap x y typeExpr :=
  LRS.CaptureDefEqAligned.lift le E.ty E.term

theorem LRS.CaptureDefEqAt.mono (hle : m ≤ m') :
    CaptureDefEqAt IH m' x y → CaptureDefEqAt IH m x y := by
  rintro ⟨elemShape, typeShape, typeExpr, hshape, htype, hty, hxy, hrel⟩
  exact ⟨elemShape, typeShape, typeExpr,
    hle.trans hshape, htype, hty, hxy, hrel⟩

/-- Lift a capture witness along an explicit logical-relation equivalence.
There is intentionally no converse for arbitrary high-level witnesses: that
would require projecting refinements and would recreate the invalid general
`Shape.WF.plift` principle. -/
theorem LRS.CaptureDefEqAt.lift
    {IH : LogRel Γ n} {IH' : LogRel Γ n'} (le : n ≤ n')
    (hliftTy : ∀ {A B : SExpr} {a : WShape n}, a.HasType .type →
      (IH'.TyDefEq A B (a.lift n') ↔ IH.TyDefEq A B a))
    (hlift : ∀ {M N A : SExpr} {m a : WShape n}, m.HasType a →
      (IH'.DefEq M N A (m.lift n') (a.lift n') ↔ IH.DefEq M N A m a)) :
    CaptureDefEqAt IH cap x y → CaptureDefEqAt IH' cap x y := by
  rintro ⟨elemShape, typeShape, typeExpr, hshape, htype, hty, hxy, hrel⟩
  exact ⟨elemShape.lift n', typeShape.lift n', typeExpr,
    hshape.trans (TShape.lift_eqv le).2,
    (WShape.HasType.lift le).2 htype,
    (hliftTy htype.isType).2 hty, hxy, (hlift htype).2 hrel⟩

/-- Rebase an existential capture through a packaged lift equivalence. -/
theorem LRS.CaptureDefEqAt.rebase
    {IH : LogRel Γ n} {IH' : LogRel Γ n'} {le : n ≤ n'}
    (E : LogRel.LiftEquiv IH IH' le) :
    CaptureDefEqAt IH cap x y → CaptureDefEqAt IH' cap x y :=
  LRS.CaptureDefEqAt.lift le E.ty E.term

/-- A pair of concrete captures together with the canonical logical-relation
witness that realizes a (possibly lower) semantic capture shape.  The depth
is existential because an iota pattern combines recursor arguments and
constructor fields, which live at adjacent stratification levels. -/
def LRS.CaptureDefEq (Γ : List SExpr) (m : TShape)
    (x y : SExpr) : Prop :=
  ∃ (depth : Nat) (elemShape typeShape : WShape depth) (typeExpr : SExpr),
    m ≤ elemShape.T ∧ elemShape.HasType typeShape ∧
    (LR Γ).TyDefEq typeExpr typeExpr typeShape ∧
    Γ ⊢ x ≡ y : typeExpr ∧
    (LR Γ).DefEq x y typeExpr elemShape typeShape

theorem LRS.CaptureDefEq.mono (hle : m ≤ m') :
    CaptureDefEq Γ m' x y → CaptureDefEq Γ m x y := by
  rintro ⟨depth, elemShape, typeShape, typeExpr,
    hshape, htype, hty, hxy, hrel⟩
  exact ⟨depth, elemShape, typeShape, typeExpr,
    hle.trans hshape, htype, hty, hxy, hrel⟩

/-- Materialize a semantic `varN` match in an arbitrary logical relation.
The level is fixed by `IH`, so no existential depth is introduced. -/
theorem LE_Interp.Matches.varN_materializeAt
    {IH : LogRel Γ n}
    {c c' : Name} {arity : Nat} {rargs : List (WShape n)}
    {mcap : (Pattern.varN (.const c) arity).Path → TShape}
    {xs ys : List SExpr} {ls ls' : List SLevel}
    (hm : LE_Interp.Matches (Pattern.varN (.const c) arity) c' rargs mcap)
    (hargs : LRS.CtorArgsDefEq IH xs ys rargs) :
    c' = c ∧ ∃ mx my,
      (Pattern.varN (.const c) arity).MatchesS
        (xs.foldr (fun a f => f.app a) (.const c ls)) ls mx ∧
      (Pattern.varN (.const c) arity).MatchesS
        (ys.foldr (fun a f => f.app a) (.const c ls')) ls' my ∧
      ∀ path, LRS.CaptureDefEqAt IH (mcap path) (mx path) (my path) := by
  induction arity generalizing c' n rargs xs ys with
  | zero =>
    simp only [Pattern.varN] at hm
    cases hm
    cases hargs
    refine ⟨rfl, nofun, nofun, ?_, ?_, nofun⟩
    · exact .const
    · exact .const
  | succ arity ih =>
    simp only [Pattern.varN] at hm
    cases hm with
    | var hm =>
      cases hargs with
      | @cons A a x y p xs ys ps hp hty hxy hv hrest =>
        obtain ⟨rfl, mx, my, hmx, hmy, hcap⟩ := ih hm hrest
        refine ⟨rfl, (fun path => Option.elim path x mx),
          (fun path => Option.elim path y my), hmx.var, hmy.var, ?_⟩
        intro path
        cases path with
        | none => exact ⟨_, _, _, TShape.LE.rfl, hp, hty, hxy, hv⟩
        | some path => exact hcap path

/-- Materialize a semantic `varN` match from the exact related application
spines that produced it.  This is purely structural: every captured syntax
pair retains its raw typing equality and its logical-relation witness. -/
theorem LE_Interp.Matches.varN_materialize
    {c c' : Name} {arity n : Nat} {rargs : List (WShape n)}
    {mcap : (Pattern.varN (.const c) arity).Path → TShape}
    {xs ys : List SExpr} {ls ls' : List SLevel}
    (hm : LE_Interp.Matches (Pattern.varN (.const c) arity) c' rargs mcap)
    (hargs : LRS.CtorArgsDefEq (LR Γ) xs ys rargs) :
    c' = c ∧ ∃ mx my,
      (Pattern.varN (.const c) arity).MatchesS
        (xs.foldr (fun a f => f.app a) (.const c ls)) ls mx ∧
      (Pattern.varN (.const c) arity).MatchesS
        (ys.foldr (fun a f => f.app a) (.const c ls')) ls' my ∧
      ∀ path, LRS.CaptureDefEq Γ (mcap path) (mx path) (my path) := by
  induction arity generalizing c' n rargs xs ys with
  | zero =>
    simp only [Pattern.varN] at hm
    cases hm
    cases hargs
    refine ⟨rfl, nofun, nofun, ?_, ?_, nofun⟩
    · exact .const
    · exact .const
  | succ arity ih =>
    simp only [Pattern.varN] at hm
    cases hm with
    | var hm =>
      cases hargs with
      | @cons A a x y p xs ys ps hp hty hxy hv hrest =>
        obtain ⟨rfl, mx, my, hmx, hmy, hcap⟩ := ih hm hrest
        refine ⟨rfl, (fun path => Option.elim path x mx),
          (fun path => Option.elim path y my), hmx.var, hmy.var, ?_⟩
        intro path
        cases path with
        | none => exact ⟨_, _, _, _, TShape.LE.rfl, hp, hty, hxy, hv⟩
        | some path => exact hcap path

/-- Materialize an exact semantic iota match over an arbitrary predecessor
relation.  Recursor captures are witnessed in `LRS IH`; constructor captures
remain in `IH`.  This adjacent-level statement is stable under the
transport operations exposed by `CtorDefEq.fold`. -/
theorem LE_Interp.Matches.iota_materialize_exactAt
    {IH : LogRel Γ n}
    {rec ctor ctor' : Name} {major arity : Nat}
    {recShapes : List (WShape (n + 1))}
    {ctorShapes : List (WShape n)}
    {mrec : (Pattern.varN (.const rec) major).Path → TShape}
    {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
    {recXs recYs ctorXs ctorYs : List SExpr}
    {recLs ctorLs ctorLs' : List SLevel}
    {majorX majorY : SExpr}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (hpat : Params.Pat (RecursorIotaPattern rec major ctor arity) r)
    (hmf : LE_Interp.Matches (n := n + 1)
      (Pattern.varN (.const rec) major) rec recShapes mrec)
    (hma : LE_Interp.Matches (n := n)
      (Pattern.varN (.const ctor) arity) ctor' ctorShapes mctor)
    (hrecargs : LRS.CtorArgsDefEq (LRS IH) recXs recYs recShapes)
    (hctorargs : LRS.CtorArgsDefEq IH ctorXs ctorYs ctorShapes)
    (hMajorX : Γ ⊢ majorX ⤳*
      ctorXs.foldr (fun (a f : SExpr) => f.app a) (.const ctor' ctorLs))
    (hMajorY : Γ ⊢ majorY ⤳*
      ctorYs.foldr (fun (a f : SExpr) => f.app a) (.const ctor' ctorLs')) :
    ∃ mx my,
      (RecursorIotaPattern rec major ctor arity).MatchesS
        ((recXs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app
          (ctorXs.foldr (fun (a f : SExpr) => f.app a) (.const ctor ctorLs)))
        recLs mx ∧
      (RecursorIotaPattern rec major ctor arity).MatchesS
        ((recYs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app
          (ctorYs.foldr (fun (a f : SExpr) => f.app a) (.const ctor ctorLs')))
        recLs my ∧
      (∀ path : (RecursorIotaPattern rec major ctor arity).Path,
        match path with
        | Sum.inl p => LRS.CaptureDefEqAt (LRS IH) (mrec p) (mx path) (my path)
        | Sum.inr p => LRS.CaptureDefEqAt IH (mctor p) (mx path) (my path)) ∧
      Γ ⊢ (recXs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app
          majorX ⤳*
        (recXs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app
          (ctorXs.foldr (fun (a f : SExpr) => f.app a) (.const ctor ctorLs)) ∧
      Γ ⊢ (recYs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app
          majorY ⤳*
        (recYs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app
          (ctorYs.foldr (fun (a f : SExpr) => f.app a) (.const ctor ctorLs')) := by
  obtain ⟨_, mxf, myf, hmxf, hmyf, hcapf⟩ :=
    hmf.varN_materializeAt (ls := recLs) (ls' := recLs) hrecargs
  obtain ⟨hctor, mxa, mya, hmxa, hmya, hcapa⟩ :=
    hma.varN_materializeAt (ls := ctorLs) (ls' := ctorLs') hctorargs
  subst ctor'
  refine ⟨Sum.elim mxf mxa, Sum.elim myf mya,
    hmxf.app hmxa, hmyf.app hmya, ?_, ?_, ?_⟩
  · intro path
    cases path with
    | inl path => exact hcapf path
    | inr path => exact hcapa path
  · exact hMajorX.major ⟨_, ⟨_, hpat⟩, _, _, .refl, _, _, hmxf⟩
  · exact hMajorY.major ⟨_, ⟨_, hpat⟩, _, _, .refl, _, _, hmyf⟩

/-- Materialize an exact semantic iota match once the recursor spine and the
constructor-field spine have both been exposed.  This canonical wrapper
forgets the two explicit adjacent relations into existential capture depths. -/
theorem LE_Interp.Matches.iota_materialize_exact
    {rec ctor ctor' : Name} {major arity n : Nat}
    {recShapes : List (WShape (n + 1))}
    {ctorShapes : List (WShape n)}
    {mrec : (Pattern.varN (.const rec) major).Path → TShape}
    {mctor : (Pattern.varN (.const ctor) arity).Path → TShape}
    {recXs recYs ctorXs ctorYs : List SExpr}
    {recLs ctorLs ctorLs' : List SLevel}
    {majorX majorY : SExpr}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (hpat : Params.Pat (RecursorIotaPattern rec major ctor arity) r)
    (hmf : LE_Interp.Matches (n := n + 1)
      (Pattern.varN (.const rec) major) rec recShapes mrec)
    (hma : LE_Interp.Matches (n := n)
      (Pattern.varN (.const ctor) arity) ctor' ctorShapes mctor)
    (hrecargs : LRS.CtorArgsDefEq (LR Γ) recXs recYs recShapes)
    (hctorargs : LRS.CtorArgsDefEq (LR Γ) ctorXs ctorYs ctorShapes)
    (hMajorX : Γ ⊢ majorX ⤳*
      ctorXs.foldr (fun (a f : SExpr) => f.app a) (.const ctor' ctorLs))
    (hMajorY : Γ ⊢ majorY ⤳*
      ctorYs.foldr (fun (a f : SExpr) => f.app a) (.const ctor' ctorLs')) :
    ∃ mx my,
      (RecursorIotaPattern rec major ctor arity).MatchesS
        ((recXs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app
          (ctorXs.foldr (fun (a f : SExpr) => f.app a) (.const ctor ctorLs)))
        recLs mx ∧
      (RecursorIotaPattern rec major ctor arity).MatchesS
        ((recYs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app
          (ctorYs.foldr (fun (a f : SExpr) => f.app a) (.const ctor ctorLs')))
        recLs my ∧
      (∀ path, LRS.CaptureDefEq Γ (Sum.elim mrec mctor path)
        (mx path) (my path)) ∧
      Γ ⊢ (recXs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app
          majorX ⤳*
        (recXs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app
          (ctorXs.foldr (fun (a f : SExpr) => f.app a) (.const ctor ctorLs)) ∧
      Γ ⊢ (recYs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app
          majorY ⤳*
        (recYs.foldr (fun (a f : SExpr) => f.app a) (.const rec recLs)).app
          (ctorYs.foldr (fun (a f : SExpr) => f.app a) (.const ctor ctorLs')) := by
  obtain ⟨mx, my, hmatchX, hmatchY, hcap, hredX, hredY⟩ :=
    LE_Interp.Matches.iota_materialize_exactAt
      (IH := LR Γ) hpat hmf hma hrecargs hctorargs hMajorX hMajorY
  refine ⟨mx, my, hmatchX, hmatchY, ?_, hredX, hredY⟩
  intro path
  cases path with
  | inl path =>
    obtain ⟨elemShape, typeShape, typeExpr,
      hshape, htype, hty, hxy, hrel⟩ :=
      hcap (Sum.inl path)
    exact ⟨n + 1, elemShape, typeShape, typeExpr,
      hshape, htype, hty, hxy, hrel⟩
  | inr path =>
    obtain ⟨elemShape, typeShape, typeExpr,
      hshape, htype, hty, hxy, hrel⟩ :=
      hcap (Sum.inr path)
    exact ⟨n, elemShape, typeShape, typeExpr,
      hshape, htype, hty, hxy, hrel⟩

theorem LRS.PiDefEq.lift
    {b : WShape n} {f : WShapeFun n} (le : n ≤ n')
    (htpi : WShape.HasTypePi f b true) :
    LRS.PiDefEq (LR Γ) B F₁ F₂ (b.lift n') (f.lift n') ↔
      LRS.PiDefEq (LR Γ) B F₁ F₂ b f :=
  LRS.PiDefEq.lift_aux le htpi
    (fun hmt => LR.TyDefEq.lift le hmt)
    (fun hma => LR.DefEq.lift le hma)


def LR.Subst1 (Γ₀ : List SExpr) (x x' A₀ A A' : SExpr) (ρ : Valuation) (i := 0) : Prop :=
  Γ₀ ⊢ x ≡ x' : A ∧ ∀ {{n}} (a : WShape n), LE_Interp ρ a.T A₀ →
    (a.HasType .type → (∃ u, Γ₀ ⊢ A ≡ A' : .sort u) ∧ (LR Γ₀).TyDefEq A A' a) ∧
    ∀ {{m : WShape n}}, LE_Interp ρ m.T (.bvar i) → m.HasType a → (LR Γ₀).DefEq x x' A m a

inductive LR.SubstWF (Γ₀ : List SExpr) : Subst → Subst → List SExpr → Valuation → Prop where
  | id : LR.SubstWF Γ₀ .id .id Γ₀ .nil
  | cons : LR.SubstWF Γ₀ σ.tail σ'.tail Γ ρ →
    (∀ {a}, LE_Interp ρ a A →
      ∃ a', a ≤ a' ∧ LE_Interp ρ a' A ∧ a'.HasType .type) →
    LE_Interp ρ a A → x.HasType a → Γ ⊢ A : .sort u →
    LR.Subst1 Γ₀ σ.head σ'.head A.lift (A.subst σ.tail) (A.subst σ'.tail) (ρ.push x) →
    LR.SubstWF Γ₀ σ σ' (A :: Γ) (ρ.push x)

theorem LR.SubstWF.fits : LR.SubstWF Γ₀ σ σ' Γ ρ → ρ.Fits Γ₀ Γ
  | .id => .nil
  | .cons W h1 h2 h3 _ _ => .cons W.fits h1 h2 h3

theorem LR.SubstWF.toSubstEq : LR.SubstWF Γ₀ σ σ' Γ ρ → Ctx.SubstEq Γ₀ σ σ' Γ
  | .id => .nil
  | .cons W _ _ _ hA h0 => .cons W.toSubstEq hA h0.1

theorem LR.SubstWF.left (W : LR.SubstWF Γ₀ σ σ' Γ ρ) : LR.SubstWF Γ₀ σ σ Γ ρ := by
  induction W with
  | id => exact .id
  | cons _ h1 h2 h3 hA h0 ih =>
    refine .cons ih h1 h2 h3 hA ⟨h0.1.hasType.1, fun _ a ha => ⟨fun ht => ?_, fun _ hM hmem => ?_⟩⟩
    · have ⟨⟨_, h1⟩, h2⟩ := (h0.2 a ha).1 ht; exact ⟨⟨_, h1.hasType.1⟩, (LR _).left_ty h2⟩
    · exact (LR _).left <| (h0.2 a ha).2 hM hmem

theorem LR.SubstWF.symm (W : LR.SubstWF Γ₀ σ σ' Γ ρ) : LR.SubstWF Γ₀ σ' σ Γ ρ := by
  induction W with
  | id => exact .id
  | cons _ h1 h2 h3 hA h0 ih =>
    refine .cons ih h1 h2 h3 hA ⟨?_, fun _ a ha => ⟨fun ht => ?_, fun _ hM hmem => ?_⟩⟩
    · have ⟨⟨_, h1⟩, _⟩ := (h0.2 (n := 0) _ .bot).1 (.bot .sort)
      exact h1.defeqDF h0.1.symm
    · exact let ⟨⟨u, h1⟩, h2⟩ := (h0.2 a ha).1 ht; ⟨⟨u, h1.symm⟩, (LR _).symm_ty h2⟩
    · let ⟨_, h2⟩ := (h0.2 a ha).1 hmem.isType
      exact (LR _).conv h2 ((LR _).symm ((h0.2 a ha).2 hM hmem))

/-! ## Shape disjointness, and the CR ladder that reaches `LRS.PiPathInv`

Ported from `plans/probes/probeW-disjointness.lean`.  The §4.4 shape facts
split into two groups, and the split is exactly where the shape lattice puts
it.

* *Disjointness* is a statement about **head shapes**, and a head shape is
  already recorded by `LE_Interp`: `WShape.sort r` and `WShape.forallE b f`
  are incomparable (`WShape.le_sort`, `WShape.sort_le`), and `LE_Interp.sound`
  transports a shape across a strong equality.  A sort equated to a Pi would
  have to carry both shapes at once.  **No fixpoint rung is involved**, which
  is why the three theorems below take no adequacy hypothesis at all.
* *Injectivity* is a statement about the **level** `u`, and `WShape.sort`
  records only `decide (u ≠ .zero)` — see the negative control
  `LRS.sortInv_bit_only` at the end of this section.  Recovering `u` needs the
  logical relation's `sort_iff`, hence a genuine adequacy rung; the producers
  live in `ShapeLogRelAdequacy.lean`, and the rung they need is `0`.

The consequence recorded at the end of the section is that
`LRS.PiPathInv` — the single residual of the chain wall — follows from the
Church–Rosser / standardization / subject-reduction rungs **alone**
(`LRS.PiPathInv.of_crLadder_noAdequacy`), so no cycle runs between it and the
adequacy fixpoint. -/

/-! ### The four §4.4 facts, restated on `SExpr` -/

/-- `IsDefEqU.sort_forallE_inv` (`Theory/Typing/Injectivity.lean:34`, `sorry`)
and `Params.structEta_sort_disjoint` (`ChurchRosser.lean:54`), transported. -/
def LRS.SortForallEDisj : Prop :=
  ∀ {Γ : List SExpr} {A B : SExpr} {u s : SLevel},
    Ctx.WF Γ → ¬ IsDefEq Γ (.sort u) (.forallE A B) (.sort s)

/-- "A Pi is not typed at a Pi."  Kills `NormalEq.etaL`; it is what
`Params.structEta_forallE_disjoint` (`ChurchRosser.lean:61`) is used for at
`HeadReduction.lean:524`. -/
def LRS.PiNotFunTyped : Prop :=
  ∀ {Γ : List SExpr} {A B A₀ B₀ : SExpr},
    Ctx.WF Γ → ¬ IsDefEq Γ (.forallE A B) (.forallE A B) (.forallE A₀ B₀)

/-- "A Pi is not a proof of a proposition."  Kills `NormalEq.proofIrrel`;
Theory spends `IsDefEqU.sort_inv` on it at `HeadReduction.lean:527`. -/
def LRS.PiNotProof : Prop :=
  ∀ {Γ : List SExpr} {A B p : SExpr},
    Ctx.WF Γ → IsDefEq Γ p p (.sort .zero) →
    ¬ IsDefEq Γ (.forallE A B) (.forallE A B) p

/-- `IsDefEqU.sort_inv` (`Theory/Typing/Injectivity.lean:11`, `sorry`), the
declared L4L-16 gate theorem, transported.  This is the *fourth* §4.4 fact and
the only one that needs an adequacy rung; the producer is
`LRS.SortInv.of_adequacyAtDepth_zero` (ADQ), and the rung is `0`. -/
def LRS.SortInv : Prop :=
  ∀ {Γ : List SExpr} {u v : SLevel} {V : SExpr},
    Ctx.WF Γ → IsDefEq Γ (.sort u) (.sort v) V → u = v

/-! ### The shape lattice separates sorts from Pis

Three tiny lemmas plus one transport.  They are the entire semantic content
of disjointness. -/

/-- A Pi shape never interprets a syntactic sort.  `LE_Interp.le_sort'` says a
syntactic sort only carries shapes `≤ .sort r`, and `WShape.le_sort` says
those are `.bot` and `.sort r` only. -/
theorem LE_Interp.forallE_not_sort {ρ : Valuation} {n : Nat} {b : WShape n}
    {f : WShapeFun n} {l : SLevel} :
    ¬ LE_Interp ρ (WShape.T (WShape.forallE b f)) (.sort l) := by
  intro H
  have h := LE_Interp.le_sort' H
  simp only [WShape.T] at h
  rcases WShape.le_sort.1 h with h | h <;>
    · have h := congrArg Subtype.val h
      simp only [WShape.forallE, WShape.bot, WShape.sort, Shape.bot, Shape.sort] at h
      cases h

/-- Shape inversion at a syntactic Pi: the observed shape is either the bottom
shape, or below a Pi shape.  Only the `bot` and `forallE` constructors of
`LE_Interp` can produce a `.forallE` subject. -/
theorem LE_Interp.forallE_shape_inv {ρ : Valuation} {m : TShape} {B F : SExpr}
    (H : LE_Interp ρ m (.forallE B F)) :
    (∃ n', m = WShape.T (n := n') WShape.bot) ∨
      ∃ (n' : Nat) (b : WShape n') (f : WShapeFun n'),
        m ≤ WShape.T (WShape.forallE b f) := by
  cases H with
  | bot => exact .inl ⟨_, rfl⟩
  | forallE _ _ _ _ hle => exact .inr ⟨_, _, _, hle⟩

/-- A sort shape never interprets a syntactic Pi. -/
theorem LE_Interp.sort_not_forallE {ρ : Valuation} {n : Nat} {r : Bool}
    {B F : SExpr} :
    ¬ LE_Interp ρ (WShape.T (WShape.sort (n := n) r)) (.forallE B F) := by
  intro H
  rcases H.forallE_shape_inv with ⟨n', h⟩ | ⟨n', b, f, hle⟩
  · obtain ⟨rfl, h⟩ := Sigma.mk.inj h
    have h := congrArg Subtype.val (eq_of_heq h)
    simp only [WShape.bot, WShape.sort] at h
    cases n <;> simp only [Shape.bot, Shape.sort] at h <;> cases h
  · exact TShape.sort_not_le_forallE hle

/-- A Pi shape is not the bottom shape. -/
theorem TShape.forallE_not_le_bot {n : Nat} {b : WShape n} {f : WShapeFun n} :
    ¬ (WShape.forallE b f).T ≤ TShape.bot := by
  rw [TShape.LE.def (Nat.le_refl (n+1)) (Nat.zero_le (n+1))]
  simp only [WShape.T, WShape.lift_self, TShape.bot, WShape.lift_bot]
  intro h
  have h := congrArg Subtype.val (WShape.le_bot.1 h)
  simp only [WShape.forallE, WShape.bot, Shape.bot] at h
  cases h

/-- The minimal Pi observation of a syntactic Pi, available with no hypotheses
at all.  The same shape `forallE_whRed_l_of_adequacy` (ADQ) builds inline. -/
theorem LE_Interp.piBot {ρ : Valuation} {n : Nat} {B F : SExpr} :
    LE_Interp ρ (WShape.T (n := n+1) (.forallE (.bot : WShape n) WShapeFun.bot))
      (.forallE B F) := by
  refine .forallE' .bot .bot (.bot <| .bot' .sort) fun _ h => ?_
  cases h.bot_r
  exact WShapeFun.bot_app.symm ▸ .bot

/-- **The workhorse.**  A subject observed at the minimal Pi shape really has
a Pi shape, and therefore a *sort* shape for its type.  This is exactly
`WShape.HasType.forallE_l` ("the type shape of a Pi shape is a sort shape")
transported through `InterpTyped.out`'s level alignment. -/
theorem InterpTyped.piBot_out {Γ : List SExpr} {M N A : SExpr}
    (d : IsDefEqStrong Γ M N A)
    (hM : LE_Interp .nil (WShape.T (n := 1) (.forallE (.bot : WShape 0) WShapeFun.bot)) M) :
    ∃ (k : Nat) (a' : WShape k) (f' : WShapeFun k) (r : Bool),
      (WShape.forallE a' f').HasType (WShape.sort r) ∧
      LE_Interp .nil (WShape.T (WShape.sort (n := k + 1) r)) A := by
  obtain ⟨n', m', a, hn, hle, _, hA, hty⟩ := ((LE_Interp.sound d .nil).2 hM).out
  have hn1 : 1 ≤ n' := hn
  obtain ⟨k, rfl⟩ : ∃ k, n' = k + 1 := ⟨n' - 1, by omega⟩
  rw [TShape.LE.def hn (Nat.le_refl _)] at hle
  simp only [WShape.T, WShape.lift_self, WShape.lift_forallE (Nat.zero_le k),
    WShape.lift_bot, WShapeFun.lift_bot] at hle
  obtain ⟨a', f', _, _, rfl⟩ := WShape.forallE_le.1 hle
  obtain ⟨r, _, rfl⟩ := WShape.HasType.forallE_l.1 hty
  exact ⟨k, a', f', r, hty, hA⟩

/-! ### Three of the four facts, from soundness alone

None of the three theorems below takes an adequacy hypothesis, and none of
them consumes `LR.adequacy` (which, since the 16C′w wrap, is conditional on
the named leaf inputs `LRS.PiPathInv`/`LR.MajorLinkRect` rather than
sorried). -/

/-- **§4.4 fact 2** (`IsDefEqU.sort_forallE_inv`) and **fact 3**
(`Params.structEta_sort_disjoint`).  Soundness transports the Pi shape of the
right endpoint onto the left endpoint, where it meets a syntactic sort. -/
theorem LRS.SortForallEDisj.of_soundness [Params.Semantic] :
    LRS.SortForallEDisj := by
  intro Γ A B u s hΓ h
  have hPi : LE_Interp .nil
      (WShape.T (n := 1) (.forallE (.bot : WShape 0) WShapeFun.bot)) (.forallE A B) :=
    LE_Interp.piBot
  exact LE_Interp.forallE_not_sort ((LE_Interp.sound (h.strong hΓ) .nil).1.2 hPi)

/-- **§4.4 fact 4** (`Params.structEta_forallE_disjoint`, as spent at
`HeadReduction.lean:524`).  The type shape of a Pi shape is a sort shape, and
a sort shape cannot interpret a syntactic Pi. -/
theorem LRS.PiNotFunTyped.of_soundness [Params.Semantic] :
    LRS.PiNotFunTyped := by
  intro Γ A B A₀ B₀ hΓ h
  obtain ⟨k, a', f', r, _, hA⟩ :=
    InterpTyped.piBot_out (h.strong hΓ) LE_Interp.piBot
  exact LE_Interp.sort_not_forallE hA

/-- The `proofIrrel` half.  Theory spends `IsDefEqU.sort_inv` here
(`HeadReduction.lean:527`); the shape system already knows it, as
`TShape.HasType.proofIrrel`: everything inhabiting a `Prop`-shaped type is the
bottom shape, and a Pi shape is not bottom. -/
theorem LRS.PiNotProof.of_soundness [Params.Semantic] : LRS.PiNotProof := by
  intro Γ A B p hΓ hp h
  obtain ⟨k, a', f', r, hPiTy, hA⟩ :=
    InterpTyped.piBot_out (h.strong hΓ) LE_Interp.piBot
  -- `p` carries a sort shape; read off that that shape is `Prop`-typed.
  obtain ⟨a₂, b₂, hle₂, _, hb₂, hty₂⟩ := (LE_Interp.sound (hp.strong hΓ) .nil).2 hA
  have hb₂' : b₂ ≤ TShape.sort false := by
    have h0 := LE_Interp.le_sort hb₂
    simpa using h0
  have hprop : a₂.HasType (TShape.sort false) :=
    TShape.HasType.mono_r hb₂' TShape.HasType.sort hty₂
  -- the Pi's own shape inhabits a `Prop`-shaped type, so it is bottom.
  exact TShape.forallE_not_le_bot
    (TShape.HasType.proofIrrel hprop
      (TShape.HasType.mono_r hle₂ hprop (WShape.HasType.T hPiTy)))

/-! ### The depth ledger for `LRS.SortInv`

`sort_inv` is the one §4.4 fact soundness cannot supply.  The rung it needs is
**depth 0**, and the reason is one line of `HasTypeStratifiedS`. -/

/-- A syntactic sort is stratified at depth `0`.  `HasTypeStratifiedS.sort'`
(SExpr:2384) is a *nullary* constructor whose depth index is a free variable,
so the sort case never consumes depth.  This is exactly the asymmetry with
`LRS.PiPathInv`, whose subject is an arbitrary type. -/
theorem HasTypeStratifiedS.sort_zero {Γ : List SExpr} {u : SLevel} :
    HasTypeStratifiedS Γ (.sort u) (.sort u.succ) true 0 := .base .sort'

/-- Depth-indexed sort/Pi disjointness, in the shape of
`JointStratifiedPathInversionAt.sortInv` (ADQ). -/
def LRS.SortForallEDisjAt (depth : Nat) : Prop :=
  ∀ {Γ : List SExpr} {A B V : SExpr} {u s : SLevel} {core : Bool} {d : Nat},
    d ≤ depth → Ctx.WF Γ → HasTypeStratifiedS Γ (.sort u) V core d →
    ¬ IsDefEq Γ (.sort u) (.forallE A B) (.sort s)

/-- Depth-indexed sort injectivity, matching `JointStratifiedInversionAt`. -/
def LRS.SortInvAt (depth : Nat) : Prop :=
  ∀ {Γ : List SExpr} {u v : SLevel} {V B : SExpr} {core : Bool} {d : Nat},
    d ≤ depth → Ctx.WF Γ → IsDefEq Γ (.sort u) (.sort v) V →
    HasTypeStratifiedS Γ (.sort u) B core d → u = v

/-- **Faithfulness, at depth 0.**  The depth-indexed form at `d = 0` already
implies the bare form the consumers use, because the certificate it demands is
`HasTypeStratifiedS.sort_zero`, which holds unconditionally. -/
theorem LRS.SortForallEDisj.of_at_zero (h : LRS.SortForallEDisjAt 0) :
    LRS.SortForallEDisj :=
  fun hΓ => h (Nat.le_refl 0) hΓ HasTypeStratifiedS.sort_zero

/-- **Faithfulness, at depth 0**, for sort injectivity. -/
theorem LRS.SortInv.of_at_zero (h : LRS.SortInvAt 0) : LRS.SortInv :=
  fun hΓ hEq => h (Nat.le_refl 0) hΓ hEq HasTypeStratifiedS.sort_zero

theorem LRS.SortForallEDisjAt.of_soundness [Params.Semantic] (depth : Nat) :
    LRS.SortForallEDisjAt depth :=
  fun _ hΓ _ => LRS.SortForallEDisj.of_soundness hΓ

/-- All four §4.4 facts as one package.  The pass records here that three of
its four fields need no input at all; only `sortInv` has a producer, and that
producer sits at rung `0` (`LRS.ShapeDisj.of_lowerAdequacy`, ADQ).

Deliberately *not* depth-indexed: `PiNotFunTyped` and `PiNotProof` have an
arbitrary Pi as subject, so recovering a bare form from a depth-`d` form would
need a stratification certificate for an arbitrary type at a fixed depth, i.e.
`LRS.PathRestratifyAt`-strength uniform depth bound, which collapses the depth
hierarchy.  They are proved outright instead. -/
structure LRS.ShapeDisj : Prop where
  sortInv : LRS.SortInv
  sortForallEDisj : LRS.SortForallEDisj
  piNotFunTyped : LRS.PiNotFunTyped
  piNotProof : LRS.PiNotProof

/-! ### The CR ladder

Everything from `LRS.SubjectRedS` to `LRS.PiPathInv.of_crLadder` transports a
Church–Rosser / standardization fact from `Theory/Typing/ChurchRosser.lean`
and `Theory/Typing/HeadReduction.lean`.  Not one of them is an adequacy
rung. -/

/-- Weak-head subject reduction (`SExpr.WHRedS.defeq`, plus `Ctx.WF`). -/
def LRS.SubjectRedS : Prop :=
  ∀ {Γ : List SExpr} {e₁ e₂ A : SExpr},
    Ctx.WF Γ → WHRedS Γ e₁ e₂ → IsDefEq Γ e₁ e₁ A → IsDefEq Γ e₁ e₂ A

/-- Pi injectivity for a single ordinary equality between two syntactic Pis. -/
def LRS.PiEdgeInv : Prop :=
  ∀ {Γ : List SExpr} {A B A' B' : SExpr} {s : SLevel},
    Ctx.WF Γ → IsDefEq Γ (.forallE A B) (.forallE A' B') (.sort s) →
    ∃ u v, TypeDefEqPath Γ A A' u ∧ TypeDefEqPath (A :: Γ) B B' v

/-- Pi-headedness is stable under ordinary type equality. -/
def LRS.PiHeadNorm : Prop :=
  ∀ {Γ : List SExpr} {X Y A B : SExpr} {s : SLevel},
    Ctx.WF Γ → IsDefEq Γ X Y (.sort s) → WHRedS Γ X (.forallE A B) →
    ∃ A' B', WHRedS Γ Y (.forallE A' B')

/-- `VEnv.IsDefEq.church_rosser` (ChurchRosser:1952), transported. -/
def LRS.CRComplete : Prop :=
  ∀ {Γ : List SExpr} {e₁ e₂ A : SExpr},
    Ctx.WF Γ → IsDefEq Γ e₁ e₂ A → CRDefEq Γ e₁ e₂ A

/-- `NormalEq` inversion when the right endpoint is a Pi. -/
def LRS.NormalEqPiInvL : Prop :=
  ∀ {Γ : List SExpr} {e A B X : SExpr},
    Ctx.WF Γ → NormalEq Γ e (.forallE A B) X → ∃ A' B', e = .forallE A' B'

/-- The Pi-shaped consequence of standardization (`VEnv.ParRedS.standard`,
HeadReduction:489, ∘ `VEnv.StRed.forallE_l`). -/
def LRS.PiStandard : Prop :=
  ∀ {Γ : List SExpr} {e A B V : SExpr},
    Ctx.WF Γ → IsDefEq Γ e e V → ParRedS Γ e (.forallE A B) →
    ∃ A' B', WHRedS Γ e (.forallE A' B')

/-- `VEnv.ParRedS.defeq` (ChurchRosser:1431), transported. -/
def LRS.ParRedSDefeq : Prop :=
  ∀ {Γ : List SExpr} {e e' A : SExpr},
    Ctx.WF Γ → ParRedS Γ e e' → IsDefEq Γ e e A → IsDefEq Γ e e' A

/-- `VEnv.IsDefEq.reduce_forallE` (HeadReduction:512), transported. -/
def LRS.ReduceForallE : Prop :=
  ∀ {Γ : List SExpr} {e A B V : SExpr},
    Ctx.WF Γ → IsDefEq Γ e (.forallE A B) V →
    ∃ A' B', WHRedS Γ e (.forallE A' B')

/-- Pi *typing* inversion: the domain and codomain of a well-typed syntactic Pi
are themselves types.  Theory's `VEnv.HasType.forallE_inv`, spent at
`HeadReduction.lean:516`, transported.

Listed among the ladder `Prop`s for uniformity only — unlike its neighbours it
is **not** an open rung: `LRS.PiTypeInv.of_strong` proves it outright from
SExpr's own strong relation, with no Church–Rosser, no standardization and no
adequacy.  It is the single premise of rung R11 that is not already a named
rung. -/
def LRS.PiTypeInv : Prop :=
  ∀ {Γ : List SExpr} {A B V : SExpr},
    Ctx.WF Γ → IsDefEq Γ (.forallE A B) (.forallE A B) V →
    (∃ u, IsDefEq Γ A A (.sort u)) ∧ ∃ v, IsDefEq (A :: Γ) B B (.sort v)

theorem ParRed.forallE_inv {Γ : List SExpr} {A B e : SExpr}
    (H : ParRed Γ (.forallE A B) e) :
    ∃ A' B', e = .forallE A' B' ∧ ParRed Γ A A' ∧ ParRed (A :: Γ) B B' := by
  cases H with
  | forallE h1 h2 => exact ⟨_, _, rfl, h1, h2⟩
  | extra action _ =>
    obtain ⟨c, ls, args, heq, _⟩ := action.matched.head_spine
    cases args <;> cases heq

theorem ParRedS.forallE_inv {Γ : List SExpr} {A B e : SExpr}
    (H : ParRedS Γ (.forallE A B) e) : ∃ A' B', e = .forallE A' B' := by
  induction H with
  | rfl => exact ⟨_, _, rfl⟩
  | tail _ h2 ih =>
    obtain ⟨_, _, rfl⟩ := ih
    obtain ⟨_, _, rfl, _, _⟩ := h2.forallE_inv
    exact ⟨_, _, rfl⟩

theorem LRS.ReduceForallE.of_ladder (cr : LRS.CRComplete)
    (neInv : LRS.NormalEqPiInvL) (std : LRS.PiStandard) : LRS.ReduceForallE := by
  intro Γ e A B V hΓ H
  obtain ⟨_, e₁', e₂', h1, h2, h3⟩ := cr hΓ H
  obtain ⟨_, _, rfl⟩ := ParRedS.forallE_inv h2
  obtain ⟨_, _, rfl⟩ := neInv hΓ h3
  exact std hΓ H.hasType.1 h1

theorem LRS.PiHeadNorm.of_reduceForallE (sr : LRS.SubjectRedS)
    (rf : LRS.ReduceForallE) : LRS.PiHeadNorm := by
  intro Γ X Y A B s hΓ h hred
  exact rf hΓ (h.symm.trans (sr hΓ hred h.hasType.1))

theorem LRS.PiHeadNorm.of_crLadder (sr : LRS.SubjectRedS) (cr : LRS.CRComplete)
    (neInv : LRS.NormalEqPiInvL) (std : LRS.PiStandard) : LRS.PiHeadNorm :=
  LRS.PiHeadNorm.of_reduceForallE sr (LRS.ReduceForallE.of_ladder cr neInv std)

theorem LRS.SubjectRedS.of_parRedSDefeq (h : LRS.ParRedSDefeq) :
    LRS.SubjectRedS :=
  fun hΓ hred he => h hΓ hred.parRedS he

/-- **`NormalEq` inversion is a shape fact.**  The only two `NormalEq`
constructors that could put a non-Pi on the left of a Pi are `etaL` and
`proofIrrel`, and both are refuted by Part 2's soundness-derived
disjointness. -/
theorem LRS.NormalEqPiInvL.of_parts (h1 : LRS.PiNotFunTyped)
    (h2 : LRS.PiNotProof) : LRS.NormalEqPiInvL := by
  have go : ∀ {Γ : List SExpr} {e₁ e₂ Y : SExpr}, NormalEq Γ e₁ e₂ Y →
      Ctx.WF Γ → ∀ (A' B' : SExpr), e₂ = .forallE A' B' →
      ∃ A'' B'', e₁ = .forallE A'' B'' := by
    intro Γ e₁ e₂ Y H
    induction H with
    | refl _ => intro _ A' B' h; exact ⟨A', B', h⟩
    | appDF _ _ _ _ _ => intro _ _ _ h; cases h
    | lamDF _ _ _ _ _ => intro _ _ _ h; cases h
    | forallEDF _ _ _ _ _ _ => intro _ _ _ _; exact ⟨_, _, rfl⟩
    | etaL _ _ he' _ _ => intro hΓ _ _ h; subst h; exact absurd he' (h1 hΓ)
    | etaR _ _ _ _ _ => intro _ _ _ h; cases h
    | proofIrrel hp _ hh' => intro hΓ _ _ h; subst h; exact absurd hh' (h2 hΓ hp)
    | defeqDF _ _ ih => exact ih
  intro Γ e A B X hΓ H
  exact go H hΓ _ _ rfl

/-- The single-edge Pi observation. -/
def LRS.PiEdgeObs : Prop :=
  ∀ {Γ : List SExpr} {X Y A B : SExpr} {s : SLevel},
    Ctx.WF Γ → IsDefEq Γ X Y (.sort s) → WHRedS Γ X (.forallE A B) →
    ∃ A' B' u v, WHRedS Γ Y (.forallE A' B') ∧
      TypeDefEqPath Γ A A' u ∧ TypeDefEqPath (A :: Γ) B B' v

/-- Component half of the single-edge Pi observation. -/
def LRS.PiEdgeInvObs : Prop :=
  ∀ {Γ : List SExpr} {X Y A B A' B' : SExpr} {s : SLevel},
    Ctx.WF Γ → IsDefEq Γ X Y (.sort s) →
    WHRedS Γ X (.forallE A B) → WHRedS Γ Y (.forallE A' B') →
    ∃ u v, TypeDefEqPath Γ A A' u ∧ TypeDefEqPath (A :: Γ) B B' v

theorem LRS.PiPathInv.of_piEdgeObs (obs : LRS.PiEdgeObs) : LRS.PiPathInv := by
  intro Γ A B A' B' s hΓ H
  have go : ∀ {X Y t A₀ B₀ : _}, TypeDefEqPath Γ X Y t →
      WHRedS Γ X (.forallE A₀ B₀) →
      ∃ AY BY u v, WHRedS Γ Y (.forallE AY BY) ∧
        TypeDefEqPath Γ A₀ AY u ∧ TypeDefEqPath (A₀ :: Γ) B₀ BY v := by
    intro X Y t A₀ B₀ P
    induction P generalizing A₀ B₀ with
    | single h => intro hred; exact obs hΓ h hred
    | trans _ _ ih₁ ih₂ =>
      intro hred
      obtain ⟨AY, BY, u₁, v₁, hredY, hdom₁, hcod₁⟩ := ih₁ hred
      obtain ⟨AZ, BZ, _, _, hredZ, hdom₂, hcod₂⟩ := ih₂ hredY
      obtain ⟨_, hdom₁'⟩ := hdom₁.symm
      exact ⟨AZ, BZ, u₁, v₁, hredZ, .trans hdom₁ hdom₂,
        .trans hcod₁ (hdom₁'.defeqDF_l_path hcod₂)⟩
  obtain ⟨_, _, u, v, hfinal, hdom, hcod⟩ := go H .rfl
  cases WHNF.forallE.whRedS hfinal
  exact ⟨u, v, hdom, hcod⟩

theorem LRS.PiEdgeObs.of_parts (inv : LRS.PiEdgeInvObs)
    (norm : LRS.PiHeadNorm) : LRS.PiEdgeObs := by
  intro Γ X Y A B s hΓ h hred
  obtain ⟨A', B', hredY⟩ := norm hΓ h hred
  obtain ⟨u, v, hdom, hcod⟩ := inv hΓ h hred hredY
  exact ⟨A', B', u, v, hredY, hdom, hcod⟩

theorem LRS.PiEdgeInvObs.of_parts (sr : LRS.SubjectRedS)
    (inv : LRS.PiEdgeInv) : LRS.PiEdgeInvObs := by
  intro Γ X Y A B A' B' s hΓ h hredX hredY
  exact inv hΓ ((sr hΓ hredX h.hasType.1).symm.trans (h.trans (sr hΓ hredY h.hasType.2)))

theorem LRS.PiPathInv.of_crLadder (srp : LRS.ParRedSDefeq) (cr : LRS.CRComplete)
    (std : LRS.PiStandard) (nf : LRS.PiNotFunTyped) (np : LRS.PiNotProof)
    (inv : LRS.PiEdgeInv) : LRS.PiPathInv :=
  have sr : LRS.SubjectRedS := LRS.SubjectRedS.of_parRedSDefeq srp
  LRS.PiPathInv.of_piEdgeObs
    (LRS.PiEdgeObs.of_parts (LRS.PiEdgeInvObs.of_parts sr inv)
      (LRS.PiHeadNorm.of_crLadder sr cr (LRS.NormalEqPiInvL.of_parts nf np) std))

/-- **HEADLINE.**  The 16C′ leaf follows from the L4L-18A′ rungs **alone**.
Every hypothesis is a Church–Rosser / standardization / subject-reduction fact
about `Theory/Typing/ChurchRosser.lean` and `Theory/Typing/HeadReduction.lean`;
not one of them is an adequacy rung, and the two semantic side conditions
(`LRS.PiNotFunTyped`, `LRS.PiNotProof`) are discharged here from soundness.

Consequently the suspected 16C′ ⇄ **ADQ-fixpoint** cycle does not exist: the
18A′ rungs need no adequacy input, so they can be scheduled independently of
the ADQ fixpoint.

**Superseded gloss, corrected 2026-08-15.**  This used to be read as "16C′ ⇄
18A′ has no cycle", i.e. as making the leaf schedulable.  It does not.  The
18A′ rungs are independent of the *adequacy fixpoint* but not of the *leaf*:
`LRS.ParRedSDefeq` and `LRS.CRComplete` are downstream of `LRS.PiPathInv`
itself.  The loop is written out on `LRS.crComplete_is_the_last_input`
below. -/
theorem LRS.PiPathInv.of_crLadder_noAdequacy [Params.Semantic]
    (srp : LRS.ParRedSDefeq) (cr : LRS.CRComplete) (std : LRS.PiStandard)
    (inv : LRS.PiEdgeInv) : LRS.PiPathInv :=
  LRS.PiPathInv.of_crLadder srp cr std
    LRS.PiNotFunTyped.of_soundness LRS.PiNotProof.of_soundness inv

/-- The same for `LRS.PiHeadNorm`, the irreducible factor. -/
theorem LRS.PiHeadNorm.of_crLadder_noAdequacy [Params.Semantic]
    (sr : LRS.SubjectRedS) (cr : LRS.CRComplete) (std : LRS.PiStandard) :
    LRS.PiHeadNorm :=
  LRS.PiHeadNorm.of_crLadder sr cr
    (LRS.NormalEqPiInvL.of_parts LRS.PiNotFunTyped.of_soundness
      LRS.PiNotProof.of_soundness) std

/-! ### Rung R11 — single-edge Pi injectivity, from Church–Rosser

`LRS.PiEdgeInv` is the last hypothesis of `LRS.PiPathInv.of_crLadder` above
with no producer; L4L-18A′ §5 records it as rung R11 with a sketch only.  This
subsection proves it from the ladder rungs.  Ported from
`plans/probes/probeR11-piedgeinv.lean`, which imports `ShapeLogRel` and nothing
else — so independence from the *adequacy fixpoint* is structural there and is
confirmed here by the absence of `sorryAx` in the axiom closures.

**What R11 is, and is not (2026-08-15).**  It is an *interderivability*
result, not a reduction.  `LRS.PiEdgeInv.of_piPathInv` runs the other
direction in one line, and the ladder rungs R11 consumes are themselves
downstream of `LRS.PiPathInv` — the loop is written out on
`LRS.crComplete_is_the_last_input` at the end of this subsection.  So R11
narrows the leaf's *presentation* (single-edge Pi injectivity suffices; the
path-valued form is not independently needed) without making the leaf cheaper.
Everything below is true and `sorryAx`-free; only the scheduling gloss that
originally accompanied the sketch was wrong.

Two facts about R11's *price* are worth stating up front, because both narrow
the recorded ladder.

**R11 sits strictly below the `PiHeadNorm` rung, not beside it.**  Not one
step of the proof performs a weak-head reduction: `LRS.PiStandard`,
`LRS.PiHeadNorm`, `LRS.ReduceForallE` and `LRS.TypeWHNFEx` are all absent.  The
`≫*` chains supplied by `LRS.CRComplete` are consumed *as chains*, by
`LRS.parRedS_forallE_path`; nothing ever needs them standardized into a
weak-head sequence.

**R11 costs `LRS.PiNotProof` but not `LRS.PiNotFunTyped`** — one of the two
sort facts that `LRS.NormalEqPiInvL.of_parts` spends, not both.  The reason is
that R11 already knows *both* `NormalEq` endpoints are Pis (Part 2 put them
there), which makes the two eta cases structural: `etaL`/`etaR` each place a
`.lam` node on one side, and a `.lam` is not a `.forallE`, so `cases` closes
them.  `LRS.NormalEqPiInvL`, which knows only the right endpoint's shape, has
to refute `etaL` semantically and therefore does need `LRS.PiNotFunTyped`.
Six of the eight `NormalEq` constructors are structural here; `refl` costs
`LRS.PiTypeInv` (proved outright) and `proofIrrel` costs `LRS.PiNotProof`
(proved from soundness above). -/

/-- **R11, Part 1.**  `LRS.PiTypeInv` is not an open obligation: it follows
from SExpr's own strong-relation machinery — `IsDefEq.strong` (SExpr:3013)
crossing the weak/strong bridge, then `IsDefEqStrong.forallE_inv'`
(SExpr:2284), whose docstring notes that it "does not appeal to weak type
uniqueness or Church–Rosser".  No Church–Rosser, no normalization, no
adequacy.

Since the `Prop` is inhabited, its vacuity question is settled affirmatively:
it cannot be false. -/
theorem LRS.PiTypeInv.of_strong [Params.Semantic] : LRS.PiTypeInv := by
  intro Γ A B V hΓ H
  obtain ⟨⟨u, hA⟩, v, hB⟩ := (H.strong hΓ).forallE_inv' (.inl rfl)
  exact ⟨⟨u, hA.defeq⟩, v, hB.defeq⟩

/-- **R11, Part 2.**  A `≫*` chain out of a well-typed Pi lands on a Pi, and
its two components are joined to the originals by ordinary type paths in the
*fixed* contexts `Γ` and `A :: Γ`.

Charges `LRS.ParRedSDefeq` once per component per step and nothing else; in
particular it charges neither Church–Rosser nor standardization.

Iterating `ParRed.forallE_inv` along the chain and *then* converting is not an
option, and this is the reason the statement is path-valued rather than
equality-valued:

* the codomain components of successive steps live in the successive contexts
  `A₀ :: Γ`, `A₁ :: Γ`, …, whereas the conclusion wants the single context
  `A :: Γ`, and SExpr's `ParRed` has no context-conversion lemma to move them
  (it is ported only at `rfl` and `weak'`).  The fix is to convert *as we go*:
  each step becomes an ordinary type equality via `LRS.ParRedSDefeq`
  immediately, and `TypeDefEqPath.defeqDF_l` walks the codomain from `Aₖ :: Γ`
  to `A :: Γ` one edge at a time.
* adjacent edges may type their shared endpoint in different universes, so
  collapsing the accumulated path into a single equality would charge
  `TypeDefEqPath.collapse`, i.e. raw type uniqueness — precisely the currency
  the path representation exists to avoid spending. -/
theorem LRS.parRedS_forallE_path (srp : LRS.ParRedSDefeq)
    {Γ : List SExpr} {A B e : SExpr} {u v : SLevel}
    (hΓ : Ctx.WF Γ) (hA : IsDefEq Γ A A (.sort u))
    (hB : IsDefEq (A :: Γ) B B (.sort v))
    (H : ParRedS Γ (.forallE A B) e) :
    ∃ A₁ B₁, e = .forallE A₁ B₁ ∧
      TypeDefEqPath Γ A A₁ u ∧ TypeDefEqPath (A :: Γ) B B₁ v := by
  induction H with
  | rfl => exact ⟨A, B, rfl, .single hA, .single hB⟩
  | tail _ h2 ih =>
    obtain ⟨A₁, B₁, rfl, PA, PB⟩ := ih
    obtain ⟨A₂, B₂, rfl, r1, r2⟩ := h2.forallE_inv
    obtain ⟨w, hA₁⟩ := PA.rightType
    have s1 : ParRedS Γ A₁ A₂ := .tail .rfl r1
    have hdom : IsDefEq Γ A₁ A₂ (.sort w) := srp hΓ s1 hA₁
    obtain ⟨w', hB₁⟩ := PB.rightType
    have hΓ₁ : Ctx.WF (A₁ :: Γ) := ⟨hΓ, w, hA₁⟩
    have s2 : ParRedS (A₁ :: Γ) B₁ B₂ := .tail .rfl r2
    have hcod : IsDefEq (A₁ :: Γ) B₁ B₂ (.sort w') := srp hΓ₁ s2 (PA.defeqDF_l hB₁)
    obtain ⟨_, PAsym⟩ := PA.symm
    exact ⟨A₂, B₂, rfl, PA.trans (.single hdom),
      PB.trans (.single (PAsym.defeqDF_l hcod))⟩

/-- **R11, Part 3.**  A `NormalEq` between two syntactic Pis yields ordinary
equalities of the domains and of the codomains, the latter in the *left*
domain's context.

This is the component-level strengthening of `LRS.NormalEqPiInvL`, which reads
off only the *shape* of the left endpoint — and it is strictly cheaper, since
knowing both endpoints are Pis makes `etaL`/`etaR` structural and so drops the
`LRS.PiNotFunTyped` premise (see the section header).

The `forallEDF` case is the reason the codomain context has to be adjusted:
that constructor relates `E₁` and `E₂` in the context of a third type that both
domains convert to, so its component equality is transported to `D₁ :: Γ` along
the edge it carries. -/
theorem LRS.normalEqPiInv (pti : LRS.PiTypeInv) (np : LRS.PiNotProof)
    {Γ : List SExpr} {D₁ E₁ D₂ E₂ X : SExpr} (hΓ : Ctx.WF Γ)
    (H : NormalEq Γ (.forallE D₁ E₁) (.forallE D₂ E₂) X) :
    (∃ w, IsDefEq Γ D₁ D₂ (.sort w)) ∧
      ∃ w', IsDefEq (D₁ :: Γ) E₁ E₂ (.sort w') := by
  have go : ∀ {Γ : List SExpr} {e₁ e₂ X : SExpr}, NormalEq Γ e₁ e₂ X →
      Ctx.WF Γ → ∀ (D₁ E₁ D₂ E₂ : SExpr),
        e₁ = .forallE D₁ E₁ → e₂ = .forallE D₂ E₂ →
        (∃ w, IsDefEq Γ D₁ D₂ (.sort w)) ∧
          ∃ w', IsDefEq (D₁ :: Γ) E₁ E₂ (.sort w') := by
    intro Γ e₁ e₂ X H
    induction H with
    | refl h =>
      intro hΓ _ _ _ _ h1 h2
      subst h1; injection h2 with p q; subst p; subst q
      exact pti hΓ h
    | appDF _ _ _ _ _ => intro _ _ _ _ _ h1 _; cases h1
    | lamDF _ _ _ _ _ => intro _ _ _ _ _ h1 _; cases h1
    | forallEDF hA₁ _ hA hB _ _ =>
      intro _ _ _ _ _ h1 h2
      injection h1 with p q; subst p; subst q
      injection h2 with p q; subst p; subst q
      exact ⟨⟨_, hA.defeq⟩, _, hA₁.symm.defeqDF_l hB.defeq⟩
    | etaL _ _ _ _ _ => intro _ _ _ _ _ h1 _; cases h1
    | etaR _ _ _ _ _ => intro _ _ _ _ _ _ h2; cases h2
    | proofIrrel hp hh _ => intro hΓ _ _ _ _ h1 _; subst h1; exact absurd hh (np hΓ hp)
    | defeqDF _ _ ih => exact ih
  exact go H hΓ _ _ _ _ rfl rfl

/-- **HEADLINE — L4L-18A′ rung R11.**  Single-edge Pi injectivity from
Church–Rosser, supplying the one hypothesis of `LRS.PiPathInv.of_crLadder`
that had no producer.  (Not a reduction of the leaf — see the subsection
header and `LRS.crComplete_is_the_last_input`.)

`LRS.CRComplete` splits the edge into two `≫*` chains meeting at a `NormalEq`;
Part 2 turns each chain into a pair of type paths with fixed contexts; Part 3
extracts the two component equalities at the meeting point; the three pieces
are then concatenated, with the right-hand codomain path transported from
`A' :: Γ` to `A :: Γ` along the assembled domain path.

No `WHRedS`, no `LRS.PiStandard`, no `LRS.PiHeadNorm`, no `LRS.TypeWHNFEx`, no
`LRS.PiNotFunTyped`.  The three premises beyond `LRS.PiTypeInv` (proved) are
all rungs the leaf already required. -/
theorem LRS.PiEdgeInv.of_crLadder (srp : LRS.ParRedSDefeq) (cr : LRS.CRComplete)
    (pti : LRS.PiTypeInv) (np : LRS.PiNotProof) : LRS.PiEdgeInv := by
  intro Γ A B A' B' s hΓ H
  obtain ⟨⟨u, hA⟩, v, hB⟩ := pti hΓ H.hasType.1
  obtain ⟨⟨u', hA'⟩, v', hB'⟩ := pti hΓ H.hasType.2
  obtain ⟨_, e₁', e₂', h1, h2, h3⟩ := cr hΓ H
  obtain ⟨A₁, B₁, rfl, PA, PB⟩ := LRS.parRedS_forallE_path srp hΓ hA hB h1
  obtain ⟨A₂, B₂, rfl, PA', PB'⟩ := LRS.parRedS_forallE_path srp hΓ hA' hB' h2
  obtain ⟨⟨w, hdom⟩, w', hcod⟩ := LRS.normalEqPiInv pti np hΓ h3
  obtain ⟨_, PA'sym⟩ := PA'.symm
  have PAA' : TypeDefEqPath Γ A A' u := PA.trans ((TypeDefEqPath.single hdom).trans PA'sym)
  refine ⟨u, v, PAA', ?_⟩
  obtain ⟨_, PAsym⟩ := PA.symm
  obtain ⟨_, PB'sym⟩ := PB'.symm
  obtain ⟨_, PA'A⟩ := PAA'.symm
  exact PB.trans ((TypeDefEqPath.single (PAsym.defeqDF_l hcod)).trans
    (PA'A.defeqDF_l_path PB'sym))

/-- The same, packaged against the two `Prop`s that are discharged outright
(`LRS.PiTypeInv` from the strong relation, `LRS.PiNotProof` from soundness), so
that only the ladder rungs remain visible.  R11 therefore consumes **nothing
the leaf did not already require**. -/
theorem LRS.PiEdgeInv.of_crLadder_noAdequacy [Params.Semantic]
    (srp : LRS.ParRedSDefeq) (cr : LRS.CRComplete) : LRS.PiEdgeInv :=
  LRS.PiEdgeInv.of_crLadder srp cr LRS.PiTypeInv.of_strong
    LRS.PiNotProof.of_soundness

/-- **HEADLINE — the 16C′ leaf from the ladder rungs, with R11 spent.**
`LRS.PiPathInv.of_crLadder_noAdequacy` closes the leaf from four inputs; R11
removes the fourth without adding anything, since
`LRS.PiEdgeInv.of_crLadder_noAdequacy` consumes only the first two of the
remaining three.  The leaf therefore rests on exactly three ladder rungs.

**Read this as an interderivability result, not a reduction.**  See the
circularity note on `LRS.crComplete_is_the_last_input` below: the three rungs
are not independent of the leaf, so this theorem narrows the leaf's
presentation without making it cheaper. -/
theorem LRS.PiPathInv.of_crLadder_R11 [Params.Semantic]
    (srp : LRS.ParRedSDefeq) (cr : LRS.CRComplete) (std : LRS.PiStandard) :
    LRS.PiPathInv :=
  LRS.PiPathInv.of_crLadder_noAdequacy srp cr std
    (LRS.PiEdgeInv.of_crLadder_noAdequacy srp cr)

/-- **CORRECTED 2026-08-15 — the name is wrong and the claim it recorded is
false.  `LRS.CRComplete` is NOT the last input to the L4L-16C′ leaf: the CR
ladder is CIRCULAR with respect to it.**

The measurement is `plans/probes/probeR12-parredS-clean.lean` (green, no
`sorryAx`), and it overturns the earlier reading of the axiom closures.
`VEnv.ParRedS.defeq` and `VEnv.ParRedS.standard` do *not* depend on
`VEnv.IsDefEq.weakN_iff`, as the superseded note here claimed.  Their `sorry`
roots are `IsDefEqU.sort_inv` and `IsDefEqU.forallE_inv_stratified` — the
L4L-16C′ deliverables themselves.  The loop, and every arrow in it is a
definitional identity or a proved implication:

    LRS.PiPathInv  =  SExpr.forallE_inv          (`LRS.PiPathInv.of_adequacy`,
                                                   ADQ, is definitionally
                                                   `TypeDefEqPath.forallE_inv_of_adequacy`)
      ⇒ IsDefEqU.forallE_inv_stratified
      ⇒ IsDefEqU.forallE_inv
      ⇒ VEnv.ParRed.defeq
      ⇒ VEnv.ParRedS.defeq
      ⇒ (transport) LRS.ParRedSDefeq
      ⇒ (rung R11, above) LRS.PiPathInv

The β case is where the dependency is essential, and it is essential for a
reason worth stating rather than citing: firing β requires reconciling an
application's *domain* with its abstraction's own domain, which is Pi
injectivity. The two essential uses are `ParRed.defeq`
(`Theory/Typing/ChurchRosser.lean`, β case) and `StRed.triangle`
(`Theory/Typing/HeadReduction.lean`, β case).  Anchor on those *names*: both
files are being edited concurrently and their line numbers shift.

**Consequence for R11.**  `LRS.PiEdgeInv.of_piPathInv` is a one-liner in the
other direction, so R11 is a *re-presentation* of the leaf — single-edge Pi
injectivity and path-valued Pi injectivity are interderivable given the ladder
— and not a reduction of it to something cheaper.  R11's theorems are all true
and `sorryAx`-free, and the narrowing they record is real; what is not real is
the earlier claim that they discharge the leaf.

**Closing ChurchRosser's remaining `sorry` will not help.**  `church_rosser`
retains the roots `weakN_iff`, `sort_inv` and `forallE_inv_stratified`
independently of it.

The statement below is retained verbatim because it is *true* — it is a
correct implication — and because keeping the false gloss's target visible is
how the ledger records that the arrow does not point where it was thought to.
It is the name and the old docstring that were wrong. -/
theorem LRS.crComplete_is_the_last_input [Params.Semantic]
    (srp : LRS.ParRedSDefeq) (std : LRS.PiStandard) :
    LRS.CRComplete → LRS.PiPathInv :=
  fun cr => LRS.PiPathInv.of_crLadder_R11 srp cr std

/-- **The constructor-spine residual, reduced to the leaf and no further.**
`LRS.CtorSpineTypeUniqPath.of_piPathInv` (:11544) already discharged this from
`LRS.PiPathInv`; with R11 the chain runs back to the ladder rungs, so the
constructor-observation route charges **no adequacy rung** and no raw type
uniqueness.  Its ADQ consumer is `LR.MajorChainAnchorStep`.

What this does *not* say (2026-08-15): that the residual is cheaper than the
leaf.  The ladder rungs are inside the loop recorded on
`LRS.crComplete_is_the_last_input`, so the honest reading is
"`LRS.CtorSpineTypeUniqPath` costs exactly `LRS.PiPathInv`, and in particular
adds nothing on top of it". -/
theorem LRS.CtorSpineTypeUniqPath.of_crLadder [Params.Semantic] {Γ : List SExpr}
    (srp : LRS.ParRedSDefeq) (cr : LRS.CRComplete) (std : LRS.PiStandard)
    (hΓ : Ctx.WF Γ) : LRS.CtorSpineTypeUniqPath Γ :=
  LRS.CtorSpineTypeUniqPath.of_piPathInv
    (LRS.PiPathInv.of_crLadder_R11 srp cr std) hΓ

/-! ### Observation-level unfoldings of the logical relation

The residuals of `LR.FixedHeadConvertStep` / `LR.FixedHeadConvertRightValid`
(ADQ) at each observation.  Kept here because their statements mention only
`LR`, `LogRel` and `SExpr`; the theorems that name the ADQ obligations sit
beside those obligations in `ShapeLogRelAdequacy.lean`. -/

/-- The sort analogue of `LRS.PiHeadNorm`; the sort observation's residual.
It is the SExpr transport of `VEnv.IsDefEq.reduce_sort`
(`HeadReduction.lean:493`), which Theory *proves*. -/
def LRS.SortHeadNorm : Prop :=
  ∀ {Γ : List SExpr} {X Y : SExpr} {w s : SLevel},
    Ctx.WF Γ → IsDefEq Γ X Y (.sort s) → WHRedS Γ X (.sort w) →
    ∃ w', WHRedS Γ Y (.sort w')

theorem LR.tyDefEq_sort_self_iff {Γ₀ : List SExpr} {n : Nat} {B : SExpr}
    {r : Bool} :
    (LR Γ₀ : LogRel Γ₀ n).TyDefEq B B (.sort r) ↔ ∃ w, Γ₀ ⊢ B ⤳* .sort w :=
  ⟨fun h => have ⟨w, h, _⟩ := (LR Γ₀).sort_iff_ty.1 h; ⟨w, h⟩,
   fun ⟨w, h⟩ => (LR Γ₀).sort_iff_ty.2 ⟨w, h, h⟩⟩

theorem LR.tyDefEq_sort_iff {Γ₀ : List SExpr} {n : Nat} {A B : SExpr}
    {r : Bool} :
    (LR Γ₀ : LogRel Γ₀ n).TyDefEq A B (.sort r) ↔
      ∃ w, Γ₀ ⊢ A ⤳* .sort w ∧ Γ₀ ⊢ B ⤳* .sort w := (LR Γ₀).sort_iff_ty

/-- The Pi observation, unfolded.  `LRS.ValTyPi2`'s first two conjuncts are the
two weak-head reductions: given the left endpoint's, the right endpoint's is
exactly `LRS.PiHeadNorm`.  The remaining four conjuncts are *semantic
component* data that the CR ladder does not produce. -/
theorem LR.tyDefEq_forallE_unfold {Γ₀ : List SExpr} {n : Nat} {M N : SExpr}
    {b : WShape n} {f : WShapeFun n} :
    (LR Γ₀ : LogRel Γ₀ (n+1)).TyDefEq M N (.forallE b f) ↔
      ∃ B₁ F₁ B₂ F₂ u v,
        Γ₀ ⊢ M ⤳* .forallE B₁ F₁ ∧ Γ₀ ⊢ N ⤳* .forallE B₂ F₂ ∧
        TypeDefEqPath Γ₀ B₁ B₂ u ∧ TypeDefEqPath (B₁ :: Γ₀) F₁ F₂ v ∧
        (LR Γ₀ : LogRel Γ₀ n).TyDefEq B₁ B₂ b ∧
        LRS.PiDefEq (LR Γ₀ : LogRel Γ₀ n) B₁ F₁ F₂ b f := .rfl

/-- The precise residual at the Pi observation, beside `LRS.PiHeadNorm`: a
named *component* transport.  The CR ladder covers the head-shape half only. -/
def LR.PiComponentTransport (Γ₀ : List SExpr) : Prop :=
  ∀ {n : Nat} {A B B₁ F₁ B₂ F₂ : SExpr} {u : SLevel} {b : WShape n}
      {f : WShapeFun n},
    IsDefEq Γ₀ A B (.sort u) →
    (LR Γ₀ : LogRel Γ₀ (n+1)).TyDefEq A A (.forallE b f) →
    Γ₀ ⊢ B ⤳* .forallE B₁ F₁ → Γ₀ ⊢ B ⤳* .forallE B₂ F₂ →
    ∃ u' v', TypeDefEqPath Γ₀ B₁ B₂ u' ∧ TypeDefEqPath (B₁ :: Γ₀) F₁ F₂ v' ∧
      (LR Γ₀ : LogRel Γ₀ n).TyDefEq B₁ B₂ b ∧
      LRS.PiDefEq (LR Γ₀ : LogRel Γ₀ n) B₁ F₁ F₂ b f

/-! ### The convert step is an induction on the shape level

Ported from `plans/probes/probeR12-picomponent.lean`.  The recorded status of
`LR.PiComponentTransport` was "the one genuinely new residual on the leaf path
that neither the CR ladder nor the adequacy fixpoint covers".  That is wrong,
and the correction is structural rather than a new trick.

**The component data at the Pi observation is the *same statement* one shape
level down.**  Unfolding `TyDefEq A B (.forallE b f)` at level `n+1` exposes
component obligations at level `n` — `TyDefEq B₁ B₂ b` and, inside
`LRS.PiDefEq`, `TyDefEq (F.inst a) (F.inst b') (f.app p)`.  So the convert step
at level `n+1` consumes the convert step at level `n`, and the residual is not
new: it is the inductive step of an induction on the shape level.  The previous
account missed it because it unfolded the Pi observation only once and read the
component conjuncts as *data* rather than as recursive occurrences.

**The two-reduct form is illusory.**  `LR.PiComponentTransport`'s two
weak-head reductions are both reductions of the *same* `B`, so
`WHRedS.determ` collapses them (`LR.PiComponentTransport.of_diag`, and the
converse `.diag`).  There is nothing to reconcile.

**What the induction costs, per shape constructor of `WShape (n+1)`:**

| shape        | obligation                                      |
| ------------ | ----------------------------------------------- |
| `bot`        | `True`                                          |
| `lam`,`ctor` | `True`                                          |
| `sort r`     | `LRS.SortHeadNorm` + `LRS.SubjectRedS` + `LRS.SortInv` |
| `forallE b f`| `LRS.PiHeadNorm` + `LRS.SubjectRedS` + `LRS.PiEdgeInv` + level `n` |
| `indTy`      | `LRS.IndTyHeadNorm` (new, see below)            |

Three of six are `True`; the sort rung is exactly what
`LR.fixedHeadConvertStep_sort_of_parts` (ADQ) already charged; the Pi rung
needs `LRS.PiEdgeInv`, which rung R11 above now *proves*.

**G4 is unaffected.**  The induction is on the *shape level*, which is
orthogonal to the adequacy rung.  `LRS.SortInv` is consumed exactly where it
was before — at the sort observation, at every level — so the same-rung
consumption recorded on `LR.FixedHeadConvertStep` neither improves nor worsens.
-/

/-- Diagonal form of `LR.PiComponentTransport`: one weak-head reduction of `B`,
not two.  Equivalent to the two-reduct form by `WHRedS.determ`. -/
def LR.PiComponentTransportDiag (Γ₀ : List SExpr) : Prop :=
  ∀ {n : Nat} {A B B₁ F₁ : SExpr} {u : SLevel} {b : WShape n} {f : WShapeFun n},
    IsDefEq Γ₀ A B (.sort u) →
    (LR Γ₀ : LogRel Γ₀ (n+1)).TyDefEq A A (.forallE b f) →
    Γ₀ ⊢ B ⤳* .forallE B₁ F₁ →
    ∃ u' v', TypeDefEqPath Γ₀ B₁ B₁ u' ∧ TypeDefEqPath (B₁ :: Γ₀) F₁ F₁ v' ∧
      (LR Γ₀ : LogRel Γ₀ n).TyDefEq B₁ B₁ b ∧
      LRS.PiDefEq (LR Γ₀ : LogRel Γ₀ n) B₁ F₁ F₁ b f

theorem LR.PiComponentTransport.of_diag {Γ₀ : List SExpr}
    (h : LR.PiComponentTransportDiag Γ₀) : LR.PiComponentTransport Γ₀ := by
  intro n A B B₁ F₁ B₂ F₂ u b f hEq hAA hred₁ hred₂
  cases hred₁.determ WHNF.forallE hred₂ WHNF.forallE
  exact h hEq hAA hred₁

theorem LR.PiComponentTransport.diag {Γ₀ : List SExpr}
    (h : LR.PiComponentTransport Γ₀) : LR.PiComponentTransportDiag Γ₀ :=
  fun hEq hAA hred => h hEq hAA hred hred

/-- `LR.FixedHeadConvertStep` (ADQ), indexed by the shape level so it can be
proved by induction.  `∀ n, LR.ConvertStepAt Γ₀ n` *is* that obligation. -/
def LR.ConvertStepAt (Γ₀ : List SExpr) (n : Nat) : Prop :=
  ∀ {A B : SExpr} {u : SLevel} {a : WShape n},
    IsDefEq Γ₀ A B (.sort u) →
    (LR Γ₀ : LogRel Γ₀ n).TyDefEq A A a →
    (LR Γ₀ : LogRel Γ₀ n).TyDefEq A B a

/-- The convert step lifts from a single ordinary type equality to a whole
`TypeDefEqPath`, one edge at a time.  This is what lets the Pi rung consume
`LRS.PiEdgeInv`'s *path*-valued output without ever charging path collapse. -/
theorem LR.ConvertStepAt.path {Γ₀ : List SExpr} {n : Nat}
    (conv : LR.ConvertStepAt Γ₀ n) {A B : SExpr} {u : SLevel} {a : WShape n}
    (P : TypeDefEqPath Γ₀ A B u)
    (hAA : (LR Γ₀ : LogRel Γ₀ n).TyDefEq A A a) :
    (LR Γ₀ : LogRel Γ₀ n).TyDefEq A B a := by
  induction P generalizing a with
  | single h => exact conv h hAA
  | trans _ _ ih₁ ih₂ =>
    have h₁ := ih₁ hAA
    have h₂ := ih₂ ((LR Γ₀).left_ty ((LR Γ₀).symm_ty h₁))
    exact (LR Γ₀).trans_ty h₁ h₂

theorem LR.ConvertStepAt.path_right {Γ₀ : List SExpr} {n : Nat}
    (conv : LR.ConvertStepAt Γ₀ n) {A B : SExpr} {u : SLevel} {a : WShape n}
    (P : TypeDefEqPath Γ₀ A B u)
    (hAA : (LR Γ₀ : LogRel Γ₀ n).TyDefEq A A a) :
    (LR Γ₀ : LogRel Γ₀ n).TyDefEq B B a :=
  (LR Γ₀).left_ty ((LR Γ₀).symm_ty (LR.ConvertStepAt.path conv P hAA))

/-- The inductive-type analogue of `LRS.SortHeadNorm` and `LRS.PiHeadNorm`:
an inductive-type head is stable under ordinary type equality.

**This one has no upstream analogue.**  Theory's `reduce_*` family stops at
`VEnv.IsDefEq.reduce_sort` (`HeadReduction.lean:493`) and
`VEnv.IsDefEq.reduce_forallE` (`:512`); there is no `reduce_const`.  So unlike
its two siblings this is a genuinely new named obligation — but it is
CR-ladder *shaped* (a head-form transport, no semantic component data), not
adequacy-shaped, and it is the only such residual the level induction
exposes. -/
def LRS.IndTyHeadNorm : Prop :=
  ∀ {Γ : List SExpr} {X Y : SExpr} {s : SLevel},
    Ctx.WF Γ → IsDefEq Γ X Y (.sort s) → LRS.IndTyHead Γ X → LRS.IndTyHead Γ Y

/-- **Triage (2026-08-15): `LRS.IndTyHeadNorm` is banked-consumer plumbing,
not leaf-critical.**  Every consumer of `LRS.IndTyHeadNorm` sits inside a
CR-conditional producer: `LR.convertStepAt_all` and
`LR.PiComponentTransport.of_crLadder` (below) take the ladder rungs
`LRS.SubjectRedS` / `LRS.PiHeadNorm` / `LRS.PiEdgeInv` as hypotheses, and
the three ADQ consumers are `LR.FixedHeadConvertStep.of_crLadder`,
`LR.FixedHeadConvertRightValid.of_crLadder` and
`LR.FixedHeadConvertStep.of_crLadder_R11`.  The ladder rungs are
interderivable with the 16C′ leaf (`LRS.piPathInv_iff_parRedSDefeq`), so
nothing on the mandatory leaf path consumes this Prop; it fires only in the
banked consumer direction, after the leaf lands.  This corrects the
premortem's framing of the rung as a leaf-path residual.

**What soundness does and does not supply.**  The ShapeDisj precedent
(`LRS.SortForallEDisj.of_soundness` and friends) does not extend to a
producer here.  `IndTyHeadNorm` factors as

    whr-expansion  ∘  shape transport  ∘  indTy adequacy

and only the middle factor is soundness-shaped — it is this theorem.  The
left flank — moving `IndTyHead Γ X`'s `WHRedS Γ X spine` into a defeq that
`LE_Interp.sound` can consume — is exactly `LRS.SubjectRedS` (equivalently a
direct whr-invariance of `LE_Interp`, which does not exist; the former
mirror `SExpr.WHRedS.defeq` was deleted at the 16C′w wrap in favour of the
conditional `WHRedS.defeq_of_piPathInv`).  The right flank — recovering
`WHRedS Γ Y spine'` from `Y` carrying the `indTy` shape — is the adequacy
fixpoint's `indTy` observation (`LR.adequacy`, ADQ).  Both flanks are
leaf-equivalent and neither is soundness-derivable, because the conclusion
`LRS.IndTyHead Γ Y` carries a *syntactic* reduction — which is what
distinguishes this rung from the refutation-shaped §4.4 facts that
soundness does prove.  There is also no `Params.Semantic` certificate to
bridge either flank: its fields (`structureEta`, `ctor`, `defn`,
`iotaRule`, `iotaSite`) are equational, not normalizing. -/
theorem LRS.indTyShapeTransport [Params.Semantic] {Γ : List SExpr}
    {X Y : SExpr} {s : SLevel} {n : Nat} (hΓ : Ctx.WF Γ)
    (h : IsDefEq Γ X Y (.sort s))
    (hX : LE_Interp .nil (WShape.indTy : WShape (n+1)).T X) :
    LE_Interp .nil (WShape.indTy : WShape (n+1)).T Y :=
  (LE_Interp.sound (h.strong hΓ) .nil).1.1 hX

/--
info: 'Lean4Lean.SExpr.LRS.indTyShapeTransport' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRS.indTyShapeTransport

/-- **The Pi rung of the induction.**  Note the conclusion is the
*heterogeneous* `TyDefEq A B`, which is strictly more convenient than the
right-endpoint form: `LRS.PiEdgeInv` hands back paths `A₁ ⇝ B₁` and
`G₁ ⇝ F₁` that slot directly into `LRS.ValTyPi2`'s two `TypeDefEqPath`
fields, so no path is ever reversed, composed, or collapsed.

The `LRS.PiDefEq` field is where the recursion lives: its `rightTy` component
is `TyDefEq (F₁.inst a) (F₁.inst b') (f.app p)`, obtained from the `G₁`
version by converting each endpoint along the substituted codomain path — two
uses of `LR.ConvertStepAt.path` at level `n`.  Its `rightDefEq` component is
raw and comes from `IsDefEqStrong.subst` at the equality substitution
`a ≡ b' : A₁`, charging no semantics at all. -/
theorem LR.convertStep_forallE [Params.Semantic] {Γ₀ : List SExpr} {n : Nat}
    (hΓ₀ : Ctx.WF Γ₀) (sr : LRS.SubjectRedS) (norm : LRS.PiHeadNorm)
    (inv : LRS.PiEdgeInv) (lower : LR.ConvertStepAt Γ₀ n)
    {A B : SExpr} {u : SLevel} {b : WShape n} {f : WShapeFun n}
    (hEq : IsDefEq Γ₀ A B (.sort u))
    (hAA : (LR Γ₀ : LogRel Γ₀ (n+1)).TyDefEq A A (.forallE b f)) :
    (LR Γ₀ : LogRel Γ₀ (n+1)).TyDefEq A B (.forallE b f) := by
  obtain ⟨A₁, G₁, A₂, G₂, u₀, v₀, hredA, hredA', hdomA, hcodA, htyA, hpiA⟩ :=
    LR.tyDefEq_forallE_unfold.1 hAA
  cases hredA.determ WHNF.forallE hredA' WHNF.forallE
  obtain ⟨B₁, F₁, hredB⟩ := norm hΓ₀ hEq hredA
  have hA' : IsDefEq Γ₀ A (.forallE A₁ G₁) (.sort u) := sr hΓ₀ hredA hEq.hasType.1
  have hB' : IsDefEq Γ₀ B (.forallE B₁ F₁) (.sort u) := sr hΓ₀ hredB hEq.hasType.2
  obtain ⟨ud, vd, Pdom, Pcod⟩ := inv hΓ₀ (hA'.symm.trans (hEq.trans hB'))
  obtain ⟨wF, hF₁⟩ := Pcod.rightType
  have hΓA : Ctx.WF (A₁ :: Γ₀) := ⟨hΓ₀, ud, Pdom.leftType⟩
  refine LR.tyDefEq_forallE_unfold.2
    ⟨A₁, G₁, B₁, F₁, ud, vd, hredA, hredB, Pdom, Pcod,
      LR.ConvertStepAt.path lower Pdom htyA, ?_, ?_⟩
  · intro a b' p hp hab hsem
    have hinst := hpiA.1 hp hab hsem
    have Pa : TypeDefEqPath Γ₀ (G₁.inst a) (F₁.inst a) vd := by
      simpa only [SExpr.inst] using
        Pcod.subst (Ctx.Subst.one IsDefEq.weakCore IsDefEq.bvar hab.hasType.1)
    have Pb : TypeDefEqPath Γ₀ (G₁.inst b') (F₁.inst b') vd := by
      simpa only [SExpr.inst] using
        Pcod.subst (Ctx.Subst.one IsDefEq.weakCore IsDefEq.bvar hab.hasType.2)
    have cL := LR.ConvertStepAt.path lower Pa ((LR Γ₀).left_ty hinst.leftTy)
    have cR := LR.ConvertStepAt.path lower Pb ((LR Γ₀).left_ty ((LR Γ₀).symm_ty hinst.leftTy))
    have W : Ctx.SubstEq Γ₀ (.one a) (.one b') (A₁ :: Γ₀) := by
      refine .cons .nil Pdom.leftType ?_
      show Γ₀ ⊢ a ≡ b' : A₁.subst SExpr.Subst.id
      rw [SExpr.subst_id]; exact hab
    exact ⟨hinst.leftTy,
      (LR Γ₀).trans_ty ((LR Γ₀).symm_ty cL) ((LR Γ₀).trans_ty hinst.leftTy cR),
      hinst.leftDefEq, ⟨wF, (hF₁.strong hΓA).subst W⟩⟩
  · intro a p hp ha hsem
    have hinst := hpiA.2 hp ha hsem
    have Pa : TypeDefEqPath Γ₀ (G₁.inst a) (F₁.inst a) vd := by
      simpa only [SExpr.inst] using
        Pcod.subst (Ctx.Subst.one IsDefEq.weakCore IsDefEq.bvar ha)
    exact LR.ConvertStepAt.path lower Pa hinst

/-- **The sort rung of the induction.**  Uniform in the level — the sort
observation is a `LogRel` *field* (`sort_iff_ty`), not a shape recursion — so
it never appeals to the inductive hypothesis.  Identical in content to
`LR.fixedHeadConvertStep_sort_of_parts` (ADQ); restated here because the
induction needs it at the same level as the other rungs. -/
theorem LR.convertStep_sort {Γ₀ : List SExpr} {n : Nat}
    (hΓ₀ : Ctx.WF Γ₀) (sr : LRS.SubjectRedS) (snorm : LRS.SortHeadNorm)
    (sinv : LRS.SortInv) {A B : SExpr} {u : SLevel} {r : Bool}
    (hEq : IsDefEq Γ₀ A B (.sort u))
    (hAA : (LR Γ₀ : LogRel Γ₀ n).TyDefEq A A (.sort r)) :
    (LR Γ₀ : LogRel Γ₀ n).TyDefEq A B (.sort r) := by
  obtain ⟨w, hredA⟩ := LR.tyDefEq_sort_self_iff.1 hAA
  obtain ⟨w', hredB⟩ := snorm hΓ₀ hEq hredA
  have hA' : IsDefEq Γ₀ A (.sort w) (.sort u) := sr hΓ₀ hredA hEq.hasType.1
  have hB' : IsDefEq Γ₀ B (.sort w') (.sort u) := sr hΓ₀ hredB hEq.hasType.2
  cases sinv hΓ₀ (hA'.symm.trans (hEq.trans hB'))
  exact LR.tyDefEq_sort_iff.2 ⟨w, hredA, hredB⟩

/-- **HEADLINE — the convert step, at every shape level.**  Induction on the
level, case split by `WShape.casesOn'`.  Three of the six shape constructors
are `True` for `LRS.TyDefEq`; the sort rung is level-uniform; only the Pi rung
recurses; and `indTy` is the single new named residual.

Its consumer `LR.FixedHeadConvertStep` (ADQ) was recorded as "THE ONE MISSING
INPUT"; this discharges it from CR-ladder rungs, `LRS.SortInv` (adequacy rung
`0`, unchanged) and `LRS.IndTyHeadNorm`. -/
theorem LR.convertStepAt_all [Params.Semantic] {Γ₀ : List SExpr}
    (hΓ₀ : Ctx.WF Γ₀) (sr : LRS.SubjectRedS) (snorm : LRS.SortHeadNorm)
    (sinv : LRS.SortInv) (norm : LRS.PiHeadNorm) (inv : LRS.PiEdgeInv)
    (ind : LRS.IndTyHeadNorm) : ∀ n, LR.ConvertStepAt Γ₀ n := by
  intro n
  induction n with
  | zero =>
    intro A B u a hEq hAA
    obtain ⟨s, wf⟩ := a
    match s with
    | .bot => trivial
    | .sort r => exact LR.convertStep_sort hΓ₀ sr snorm sinv hEq hAA
  | succ n ih =>
    intro A B u a hEq hAA
    cases a using WShape.casesOn' with
    | bot => trivial
    | sort r => exact LR.convertStep_sort hΓ₀ sr snorm sinv hEq hAA
    | forallE b f => exact LR.convertStep_forallE hΓ₀ sr norm inv ih hEq hAA
    | lam f h => trivial
    | ctor c l h => trivial
    | indTy => exact ⟨hAA.1, ind hΓ₀ hEq hAA.1⟩

/-- **The recorded residual, discharged.**  `LR.PiComponentTransport` is not a
new obligation: the level induction supplies it. -/
theorem LR.PiComponentTransport.of_crLadder [Params.Semantic] {Γ₀ : List SExpr}
    (hΓ₀ : Ctx.WF Γ₀) (sr : LRS.SubjectRedS) (snorm : LRS.SortHeadNorm)
    (sinv : LRS.SortInv) (norm : LRS.PiHeadNorm) (inv : LRS.PiEdgeInv)
    (ind : LRS.IndTyHeadNorm) : LR.PiComponentTransport Γ₀ := by
  refine LR.PiComponentTransport.of_diag ?_
  intro n A B B₁ F₁ u b f hEq hAA hredB
  have step := LR.convertStepAt_all hΓ₀ sr snorm sinv norm inv ind
  obtain ⟨A₁, G₁, B₁', F₁', ud, vd, hredA, hredB', Pdom, Pcod, hty, hpi⟩ :=
    LR.tyDefEq_forallE_unfold.1
      (LR.convertStep_forallE hΓ₀ sr norm inv (step n) hEq hAA)
  cases hredB.determ WHNF.forallE hredB' WHNF.forallE
  obtain ⟨wB, hB₁⟩ := Pdom.rightType
  obtain ⟨wF, hF₁⟩ := Pcod.rightType
  obtain ⟨_, Pdomsym⟩ := Pdom.symm
  refine ⟨wB, wF, .single hB₁, .single (Pdom.defeqDF_l hF₁),
    (LR Γ₀).left_ty ((LR Γ₀).symm_ty hty), ?_, ?_⟩
  · intro a b' p hp hab hsem
    have hab' : Γ₀ ⊢ a ≡ b' : A₁ := Pdomsym.defeqDF hab
    have hsem' : (LR Γ₀ : LogRel Γ₀ n).DefEq a b' A₁ p b :=
      (LR Γ₀).conv ((LR Γ₀).symm_ty hty) hsem
    have hinst := hpi.1 hp hab' hsem'
    exact ⟨hinst.rightTy, hinst.rightTy, hinst.rightDefEq, hinst.rightDefEq⟩
  · intro a p hp ha hsem
    have ha' : Γ₀ ⊢ a : A₁ := Pdomsym.defeqDF ha
    have hsem' : (LR Γ₀ : LogRel Γ₀ n).DefEq a a A₁ p b :=
      (LR Γ₀).conv ((LR Γ₀).symm_ty hty) hsem
    have hinst := hpi.1 hp ha' hsem'
    exact hinst.rightTy

/-! ### Vacuity discipline

Standing policy since 2026-08-15: every new `Prop` either exhibits an
inhabitant or an attempted derivation of `False`.  The three proved
disjointness facts are *refutations*, so the risk they carry is that the
judgment they refute is empty; `LRS.nonvacuous_sort` and `LRS.nonvacuous_pi`
show it is not.  `LRS.sortInv_bit_only` is the sharp negative control: the
soundness machinery recovers the `decide (u ≠ .zero)` bit and *nothing more*,
which is exactly why `LRS.SortInv` still needs a rung.  `LRS.SortHeadNorm` and
`LR.PiComponentTransport` are inhabited on the diagonal. -/

theorem LRS.nonvacuous_sort {Γ : List SExpr} {u : SLevel} :
    IsDefEq Γ (.sort u) (.sort u) (.sort u.succ) := .sort

/-- **Negative control — the sharp boundary.**  Soundness alone recovers the
`decide (u ≠ .zero)` bit shared by two equated sorts, and *nothing more*: the
level itself is not determined, which is precisely why `LRS.SortInv` still
needs an adequacy rung while the three disjointness facts do not.

This is also the strongest available evidence that the pass is not vacuous.
If `[Params] [Params.Semantic]` were inconsistent, or if the soundness
machinery proved too much, `LRS.SortInv` would fall out of the same two lines
— it does not. -/
theorem LRS.sortInv_bit_only [Params.Semantic] {Γ : List SExpr} {V : SExpr}
    {a b : SLevel} (hΓ : Ctx.WF Γ)
    (h : IsDefEq Γ (.sort a) (.sort b) V) :
    decide (a ≠ .zero) = decide (b ≠ .zero) := by
  have hstart : LE_Interp .nil (TShape.sort (decide (a ≠ .zero))) (.sort a) :=
    LE_Interp.sort'
  have hend := (LE_Interp.sound (h.strong hΓ) .nil).1.1 hstart
  have hle := LE_Interp.le_sort hend
  rw [TShape.LE.def (Nat.le_refl 0) (Nat.le_refl 0)] at hle
  simp only [TShape.sort, WShape.T, WShape.lift_self] at hle
  have hval := congrArg Subtype.val (WShape.sort_le.1 hle)
  simp only [WShape.sort, Shape.sort] at hval
  injection hval

theorem LRS.nonvacuous_pi {Γ : List SExpr} {A B : SExpr} {u v : SLevel}
    (hA : IsDefEq Γ A A (.sort u)) (hB : IsDefEq (A :: Γ) B B (.sort v)) :
    IsDefEq Γ (.forallE A B) (.forallE A B) (.sort (.imax u v)) :=
  .forallEDF hA hB

/-- Non-vacuity of `LRS.PiTypeInv`'s hypothesis, in the *empty* context and
with no environment assumptions at all: a Pi over two sorts is well-typed, so
the `Prop` proved by `LRS.PiTypeInv.of_strong` has content. -/
theorem LRS.piTypeInv_nonvacuous (pti : LRS.PiTypeInv) {l l' : SLevel} :
    (∃ u, IsDefEq [] (.sort l) (.sort l) (.sort u)) ∧
      ∃ v, IsDefEq [.sort l] (.sort l') (.sort l') (.sort v) :=
  pti trivial (LRS.nonvacuous_pi .sort .sort)

/-- Non-vacuity of rung R11, at the same witness.  Together with
`LRS.PiEdgeInv.of_crLadder`, this pins the vacuity question exactly:
`LRS.PiEdgeInv` is refutable only if `LRS.CRComplete` or `LRS.ParRedSDefeq` is,
since the other two premises are proved outright. -/
theorem LRS.piEdgeInv_nonvacuous (inv : LRS.PiEdgeInv) {l l' : SLevel} :
    ∃ u v, TypeDefEqPath [] (.sort l) (.sort l) u ∧
      TypeDefEqPath [.sort l] (.sort l') (.sort l') v :=
  inv trivial (LRS.nonvacuous_pi .sort .sort)

theorem LRS.sortHeadNorm_diagonal {Γ : List SExpr} {X : SExpr} {w : SLevel}
    (hred : WHRedS Γ X (.sort w)) : ∃ w', WHRedS Γ X (.sort w') := ⟨w, hred⟩

theorem LR.piComponentTransport_diagonal_witness {Γ₀ : List SExpr} {n : Nat}
    {A : SExpr} {b : WShape n} {f : WShapeFun n}
    (hAA : (LR Γ₀ : LogRel Γ₀ (n+1)).TyDefEq A A (.forallE b f)) :
    ∃ B₁ F₁ u' v', Γ₀ ⊢ A ⤳* .forallE B₁ F₁ ∧
      TypeDefEqPath Γ₀ B₁ B₁ u' ∧ TypeDefEqPath (B₁ :: Γ₀) F₁ F₁ v' ∧
      (LR Γ₀ : LogRel Γ₀ n).TyDefEq B₁ B₁ b ∧
      LRS.PiDefEq (LR Γ₀ : LogRel Γ₀ n) B₁ F₁ F₁ b f := by
  obtain ⟨B₁, F₁, B₂, F₂, u, v, hred, hred₂, hdom, hcod, hty, hpi⟩ :=
    LR.tyDefEq_forallE_unfold.1 hAA
  cases hred.determ WHNF.forallE hred₂ WHNF.forallE
  exact ⟨B₁, F₁, u, v, hred, hdom, hcod, hty, hpi⟩

/-- Non-vacuity of `LR.PiComponentTransportDiag`, at an arbitrary valid Pi
observation.  Sharper than the diagonal witness above: the *reduct* is chosen
by the caller rather than read off the observation, and determinism forces the
two to agree.  So the conclusion of the diagonal form is inhabited at every
instance whose hypotheses are, with no ladder input at all — which is exactly
why `LR.PiComponentTransportDiag` can only fail off the diagonal, where the
level induction supplies it. -/
theorem LR.piComponentTransportDiag_nonvacuous {Γ₀ : List SExpr} {n : Nat}
    {A B₁ F₁ : SExpr} {b : WShape n} {f : WShapeFun n}
    (hAA : (LR Γ₀ : LogRel Γ₀ (n+1)).TyDefEq A A (.forallE b f))
    (hred : Γ₀ ⊢ A ⤳* .forallE B₁ F₁) :
    ∃ u' v', TypeDefEqPath Γ₀ B₁ B₁ u' ∧ TypeDefEqPath (B₁ :: Γ₀) F₁ F₁ v' ∧
      (LR Γ₀ : LogRel Γ₀ n).TyDefEq B₁ B₁ b ∧
      LRS.PiDefEq (LR Γ₀ : LogRel Γ₀ n) B₁ F₁ F₁ b f := by
  obtain ⟨B₁', F₁', u', v', hredA, hdom, hcod, hty, hpi⟩ :=
    LR.piComponentTransport_diagonal_witness hAA
  cases hred.determ WHNF.forallE hredA WHNF.forallE
  exact ⟨u', v', hdom, hcod, hty, hpi⟩

/-- Non-vacuity of `LR.ConvertStepAt` at a **non-degenerate** shape: a
syntactic sort is a valid type at the sort observation, at every level and
every relevance bit, so the Prop's hypothesis is inhabited and its conclusion
carries content (it forces `B` to reach the *same* sort). -/
theorem LR.convertStepAt_nonvacuous {Γ₀ : List SExpr} {n : Nat}
    (conv : LR.ConvertStepAt Γ₀ n) {B : SExpr} {w u : SLevel} {r : Bool}
    (hEq : IsDefEq Γ₀ (.sort w) B (.sort u)) :
    ∃ w', Γ₀ ⊢ SExpr.sort w ⤳* .sort w' ∧ Γ₀ ⊢ B ⤳* .sort w' :=
  LR.tyDefEq_sort_iff.1 (conv (a := .sort r) hEq (LR.tyDefEq_sort_iff.2 ⟨w, .rfl, .rfl⟩))

/-- Non-vacuity of `LRS.IndTyHeadNorm`: its hypothesis is inhabited as soon as
the environment declares any nullary inductive type.  Unlike the sort and Pi
witnesses this one is environment-conditional — there is no `Params`-free
inductive type — which is the honest statement of the residual's scope. -/
theorem LRS.indTyHead_nonvacuous {Γ : List SExpr} {c : Name} {ls : List SLevel}
    (h : Params.classify c = some (.indTy 0)) : LRS.IndTyHead Γ (.const c ls) :=
  ⟨c, ls, [], h, .rfl⟩

/-! ### The Church–Rosser ladder, banked as a *consumer* of the 16C′ leaf

Source: `plans/probes/probeR13-loop.lean` (green; all 22 `#print axioms`
`sorryAx`-free).  R13 proved that the ladder rung `LRS.ParRedSDefeq` and the
L4L-16C′ leaf `LRS.PiPathInv` are **interderivable**
(`LRS.piPathInv_iff_parRedSDefeq` below).  That definitively closes the ladder
as a way to *discharge* the leaf — any proof of the rung is a proof of the
leaf, so it is not a cheaper input.  The same fact makes the ladder a valuable
downstream **consumer**, and the consumer direction is what is banked here.

**The payoff.**  Everything below fires the moment 16C′ lands, and no
derivation in this block uses Church–Rosser, standardization or adequacy:

* `LRS.parRedSDefeq_of_piPathInv` — the rung `LRS.ParRedSDefeq` outright, from
  the leaf and nothing else;
* `WHRedS.defeq_of_piPathInv` (:11549) — the rung `LRS.SubjectRedS`, already
  landed and definitionally that statement;
* `LRS.PiEdgeInv.of_piPathInv` — the single-edge rung, and with it
  `LRS.PiEdgeInvObs.of_parts` (:15308) and `LRS.PiEdgeObs.of_parts` (:15301)
  as soon as `LRS.PiHeadNorm` is in hand.

So the leaf pays for the ladder, not the other way round.  It also retires the
`sorryAx` that Theory's `VEnv.ParRed.defeq` (`Theory/Typing/ChurchRosser.lean`)
and `VEnv.StRed.triangle` (`Theory/Typing/HeadReduction.lean`) currently carry:
probeR12 measured their roots as `IsDefEqU.sort_inv` /
`IsDefEqU.forallE_inv_stratified`, i.e. the 16C′ deliverables themselves.
Anchor on those *names* — both files move.

Structurally the derivation is Theory's `VEnv.ParRed.defeq` with every
`IsDefEq.trans_l` / `uniqU` fixup replaced by the declared-type path returned
by the SExpr inversion suite (`IsDefEqStrong.app_inv'` SExpr:3705,
`.lam_inv'` :3753, `.forallE_inv_path` :3804).  The leaf is charged **exactly
once**, in the `beta` case, and its bare output is consumed only by
`TypeDefEqPath.defeqDF` / `.subst` on unindexed judgments, after both
inductive hypotheses have already fired at inversion-supplied types. -/

/-- **The pattern-contraction rung — the second, independent uniqueness
site.**  A registered contraction carries its local equality only at the type
`A` that the `Pattern.Action` chose; using it at the type `V` at which the
redex is actually typed is Theory's `IsDefEqU.defeqU_l`, i.e. **type
uniqueness**.  It is isolated here because it is *not* Π-injectivity:
`LRS.PatStep.of_typeUniq` proves it from raw type uniqueness and from nothing
whatever about Pi shapes.

It is nevertheless not an extra residual on top of the leaf.  Every redex a
`Pattern.Action` can match is a constant-headed spine, and spine type
uniqueness is already reduced to the leaf here (`LRS.constSpineTypeUniqPath`,
:11458), so `LRS.PatStep.of_piPathInv` discharges it from `LRS.PiPathInv` too
— exactly as the `extra` case of `WHRed.defeq_of_piPathInv` (:11507) already
does for weak-head steps. -/
def LRS.PatStep : Prop :=
  ∀ {Γ : List SExpr} {p : Pattern} {r : p.RHS × p.Check} {e V A : SExpr}
    {m1 : List SLevel} {m2 : p.Path → SExpr},
    Ctx.WF Γ → Pattern.Action Γ r e m1 m2 A → IsDefEq Γ e e V →
    IsDefEq Γ e (r.1.applyS m1 m2) V

/-- The pattern rung follows from raw type uniqueness, and from nothing about
Pi shapes.  This pins its content: it is a retyping step, not an inversion. -/
theorem LRS.PatStep.of_typeUniq (uniq : LogRel.ContextualRawTypeUniq) :
    LRS.PatStep := by
  intro Γ p r e V A m1 m2 hΓ action he
  obtain ⟨u, h⟩ := uniq hΓ action.sound.hasType.1 he
  exact h.defeqDF action.sound

/-- …and it also follows from the leaf alone, because the redex of a
`Pattern.Action` is a constant-headed spine and spine type uniqueness is
already `LRS.PiPathInv` (:11458).  Hence `LRS.PatStep` is not an additional
residual: the ladder's consumer direction below costs the leaf and nothing
more (`LRS.parRedSDefeq_of_piPathInv`). -/
theorem LRS.PatStep.of_piPathInv [Params.Semantic] (piInv : LRS.PiPathInv) :
    LRS.PatStep := by
  intro Γ p r e V A m1 m2 hΓ action he
  obtain ⟨c, ls', args, heq, _⟩ := action.matched.head_spine
  subst heq
  obtain ⟨_, hty⟩ :=
    LRS.constSpineTypeUniqPath piInv hΓ action.sound.hasType.1 he
  exact hty.defeqDF action.sound

/-- Congruence of an RHS template under equalities of its captures.  Proved
structurally from `IsDefEqStrong.app_inv'`: no injectivity, no uniqueness, and
in particular no `piInv` — the application case transports along the path the
inverter returns. -/
theorem applyS_congr [Params.Semantic] {p : Pattern} {Γ : List SExpr}
    {m1 : List SLevel} {m2 m2' : p.Path → SExpr}
    (hΓ : Ctx.WF Γ)
    (hm : ∀ (path : p.Path) (W : SExpr),
      IsDefEq Γ (m2 path) (m2 path) W → IsDefEq Γ (m2 path) (m2' path) W) :
    ∀ (r : p.RHS) (V : SExpr), IsDefEq Γ (r.applyS m1 m2) (r.applyS m1 m2) V →
      IsDefEq Γ (r.applyS m1 m2) (r.applyS m1 m2') V := by
  intro r
  induction r with
  | fixed c hc => exact fun _ hr => hr
  | var path => exact fun V hr => hm path V hr
  | app f a ihf iha =>
    intro V hr
    simp only [Pattern.RHS.applyS] at hr ⊢
    obtain ⟨A₀, B₀, w, hfT, haT, P⟩ := (hr.strong hΓ).app_inv' (.inl rfl)
    exact P.defeqDF (.appDF (ihf _ hfT.defeq) (iha _ haT.defeq))

/-- **Native `ParRed` subject reduction from the leaf.**  Structurally Theory's
`VEnv.ParRed.defeq` (ChurchRosser, β case), except that every
`IsDefEq.trans_l` / `uniqU` fixup is replaced by the declared-type path
returned by the inversion suite.  The only residual inputs are
`LRS.PiPathInv` — charged exactly once, in the `beta` case — and
`LRS.PatStep`, itself dischargeable from either (`.of_typeUniq`,
`.of_piPathInv`).

No Church–Rosser, no standardization, no adequacy: `ShapeLogRel.lean` does not
import `Theory/Typing/ChurchRosser.lean`, so independence from the Theory CR
development is module-level rather than merely unreached. -/
theorem ParRed.defeq_of_piPathInv [Params.Semantic]
    (piInv : LRS.PiPathInv) (pat : LRS.PatStep) :
    ∀ {Γ : List SExpr} {e e' : SExpr}, ParRed Γ e e' →
      ∀ (A : SExpr), Ctx.WF Γ → IsDefEq Γ e e A → IsDefEq Γ e e' A := by
  intro Γ e e' H
  induction H with
  | bvar => exact fun _ _ he => he
  | sort => exact fun _ _ he => he
  | const => exact fun _ _ he => he
  | app _ _ ih1 ih2 =>
    intro V hΓ he
    obtain ⟨A₀, B₀, w, hf, ha, P⟩ := (he.strong hΓ).app_inv' (.inl rfl)
    exact P.defeqDF (.appDF (ih1 _ hΓ hf.defeq) (ih2 _ hΓ ha.defeq))
  | lam _ _ ih1 ih2 =>
    intro V hΓ he
    obtain ⟨B₀, u, v, w, hA, hB, hbody, P⟩ := (he.strong hΓ).lam_inv' (.inl rfl)
    exact P.defeqDF (.lamDF (ih1 _ hΓ hA.defeq) (ih2 _ ⟨hΓ, u, hA.defeq⟩ hbody.defeq))
  | forallE _ _ ih1 ih2 =>
    intro V hΓ he
    obtain ⟨u, v, w, hA, hB, P⟩ := (he.strong hΓ).forallE_inv_path (.inl rfl)
    exact P.defeqDF (.forallEDF (ih1 _ hΓ hA.defeq) (ih2 _ ⟨hΓ, u, hA.defeq⟩ hB.defeq))
  | @beta Adom Γ₂ e₁ e₁' e₂ e₂' _ _ ih1 ih2 =>
    intro V hΓ he
    obtain ⟨A₀, B₀, w, hf, ha, P⟩ := (he.strong hΓ).app_inv' (.inl rfl)
    obtain ⟨B₁, u, v, w', hA, hB₁, hb, Q⟩ := hf.lam_inv' (.inl rfl)
    -- ↓↓↓ the one and only use of the leaf ↓↓↓
    obtain ⟨ud, vd, Pdom, Pcod⟩ := piInv hΓ Q
    obtain ⟨_, Pdom'⟩ := Pdom.symm
    -- the leaf's *output* is consumed only by `defeqDF` / `subst` on unindexed
    -- equalities, and only **after** the inductive hypotheses have fired.
    have hb' := ih1 _ ⟨hΓ, u, hA.defeq⟩ hb.defeq
    have ha'' := Pdom'.defeqDF (ih2 _ hΓ ha.defeq)
    have ha' := ha''.hasType.1
    have main := IsDefEq.trans
      (.symm (.appDF (.symm (.lamDF hA.defeq hb')) (.symm ha'')))
      (.beta hb'.hasType.2 ha''.hasType.2)
    have W : Ctx.SubstEq Γ₂ (.one e₂') (.one e₂) (Adom :: Γ₂) := by
      refine .cons .nil hA.defeq ?_
      show IsDefEq Γ₂ e₂' e₂ (SExpr.subst Adom SExpr.Subst.id)
      rw [SExpr.subst_id]; exact ha''.symm
    have hconv : IsDefEq Γ₂ (B₁.inst e₂') (B₁.inst e₂) (.sort v) := (hB₁.substCongr W).1
    have Pcod' : TypeDefEqPath Γ₂ (B₁.inst e₂) (B₀.inst e₂) vd := by
      simpa only [SExpr.inst] using
        Pcod.subst (Ctx.Subst.one IsDefEq.weakCore IsDefEq.bvar ha')
    exact (((TypeDefEqPath.single hconv).trans Pcod').trans P).defeqDF main
  | extra action _ ih =>
    intro V hΓ he
    have h1 := pat hΓ action he
    exact h1.trans (applyS_congr hΓ (fun path W hW => ih path W hΓ hW) _ _ h1.hasType.2)

/-- The `≫*` closure, i.e. the rung `LRS.ParRedSDefeq` itself.  Nothing is
re-certified along the sequence: the per-step lemma is indexed by no depth. -/
theorem ParRedS.defeq_of_piPathInv [Params.Semantic]
    (piInv : LRS.PiPathInv) (pat : LRS.PatStep) : LRS.ParRedSDefeq := by
  intro Γ e e' A hΓ H he
  induction H with
  | rfl => exact he
  | tail _ h2 ih =>
    exact ih.trans (ParRed.defeq_of_piPathInv piInv pat h2 _ hΓ ih.hasType.2)

/-- **The consumer statement, with no side conditions.**  The 16C′ leaf pays
for the CR-ladder rung `LRS.ParRedSDefeq` outright — `LRS.PatStep` is
discharged from the same input by `LRS.PatStep.of_piPathInv`.  Composed with
`LRS.SubjectRedS.of_parRedSDefeq` (:15241) this also delivers
`LRS.SubjectRedS` (which `WHRedS.defeq_of_piPathInv` already gives directly),
and with `LRS.PiEdgeInv.of_piPathInv` the single-edge rung. -/
theorem LRS.parRedSDefeq_of_piPathInv [Params.Semantic] (piInv : LRS.PiPathInv) :
    LRS.ParRedSDefeq :=
  ParRedS.defeq_of_piPathInv piInv (LRS.PatStep.of_piPathInv piInv)

/-- **HEADLINE (probeR13).**  The CR-ladder rung `LRS.ParRedSDefeq` and the
L4L-16C′ leaf `LRS.PiPathInv` are *interderivable* modulo the other two rungs.
Forward is `ParRedS.defeq_of_piPathInv` (native: no Church–Rosser, no
standardization, no adequacy); backward is `LRS.PiPathInv.of_crLadder_R11`
(:15543).

Read this in the consumer direction.  As a *producer* route it is closed: the
rung is not a cheaper input than the leaf, since any proof of it is a proof of
the leaf.  As a *consumer* it says the ladder comes free with 16C′.  The `pat`
premise is not an extra cost either — `LRS.PatStep.of_piPathInv` discharges it
from the leaf, which is why `LRS.parRedSDefeq_of_piPathInv` above needs no
side conditions. -/
theorem LRS.piPathInv_iff_parRedSDefeq [Params.Semantic]
    (pat : LRS.PatStep) (cr : LRS.CRComplete) (std : LRS.PiStandard) :
    LRS.PiPathInv ↔ LRS.ParRedSDefeq :=
  ⟨fun piInv => ParRedS.defeq_of_piPathInv piInv pat,
   fun srp => LRS.PiPathInv.of_crLadder_R11 srp cr std⟩

/-- The single-edge rung from the path-valued leaf: an edge is a one-edge
path.  The one-liner the R11 notes (:15361, :15579) refer to, now checked. -/
theorem LRS.PiEdgeInv.of_piPathInv (piInv : LRS.PiPathInv) : LRS.PiEdgeInv :=
  fun hΓ h => piInv hΓ (.single h)

/-- **The price of the `PiEdgeInv` framing.**  `IsDefEqStrong.lam_inv'` returns
a *path* — one edge per `defeqDF` in the abstraction's own derivation, and
adjacent edges may live at different universes — so collapsing it to the
single edge `LRS.PiEdgeInv` consumes is exactly `TypeDefEqPath.collapse`
(:10521), i.e. raw type uniqueness.

That is the trade this direction makes, stated plainly: the `PiEdgeInv`
framing **trades the 16C′ leaf for the L4L-17 co-deliverable**
(`LogRel.ContextualRawTypeUniq`, :10514) rather than avoiding it.  With
`LRS.PiEdgeInv.of_piPathInv` above, the two framings are interderivable modulo
exactly that uniqueness input. -/
theorem LRS.PiPathInv.of_piEdgeInv_collapse
    (uniq : LogRel.ContextualRawTypeUniq) (inv : LRS.PiEdgeInv) :
    LRS.PiPathInv := fun hΓ H => inv hΓ (H.collapse (uniq hΓ))

/-- Vacuity discipline for `LRS.PatStep`.  Its hypothesis set is inhabited
wherever `Pattern.Action` is — environment-conditional, like
`LRS.indTyHead_nonvacuous` — and at the action's own type the conclusion is
`action.sound` itself, so no derivation of `False` is available that does not
also refute `Pattern.Action.sound`.  The content is entirely the *retyping*
from `A` to `V`, which is what `.of_typeUniq` and `.of_piPathInv` supply. -/
theorem LRS.patStep_nonvacuous (pat : LRS.PatStep) {Γ : List SExpr}
    {p : Pattern} {r : p.RHS × p.Check} {e A : SExpr} {m1 : List SLevel}
    {m2 : p.Path → SExpr} (hΓ : Ctx.WF Γ)
    (action : Pattern.Action Γ r e m1 m2 A) :
    IsDefEq Γ e (r.1.applyS m1 m2) A :=
  pat hΓ action action.sound.hasType.1

/-! ### Closure records — where the leaf is charged, and three dead routes

Banked from probeR13 Parts 5–7 so that the dead routes are not re-attempted.
Each entry is a machine-checked statement of a negative result. -/

/-- **The β *congruence* is Π-injectivity-free.**  With the inversion suite in
hand, `.app (.lam A e₁) e₂ ≡ .app (.lam A e₁') e₂'` is derivable at the
declared type `V` with **no** `piInv` call at all: the abstraction's own Pi is
transported to the application's along `Q` by `defeqDF`, which needs no
inversion.  So the leaf is not charged by the congruence — do not look for it
there. -/
theorem beta_congr_no_piInv {Γ : List SExpr} {A A₀ B₀ B₁ e₁ e₁' e₂ e₂' V : SExpr}
    {u w₁ w₂ : SLevel}
    (hA : IsDefEq Γ A A (.sort u))
    (P : TypeDefEqPath Γ (B₀.inst e₂) V w₁)
    (Q : TypeDefEqPath Γ (.forallE A B₁) (.forallE A₀ B₀) w₂)
    (rec₁ : IsDefEq (A :: Γ) e₁ e₁' B₁)
    (rec₂ : IsDefEq Γ e₂ e₂' A₀) :
    IsDefEq Γ (.app (.lam A e₁) e₂) (.app (.lam A e₁') e₂') V :=
  P.defeqDF (.appDF (Q.defeqDF (.lamDF hA rec₁)) rec₂)

/-- **…and the *contraction* is where it is charged.**  `IsDefEq.beta` and
`IsDefEqStrong.beta` both demand the argument at the **abstraction's own**
domain `A`; the inversion suite supplies it only at the application's domain
`A₀`.  Reconciling the two is inverting `Q`, and `Q` is a path between two
syntactic Pis — i.e. `LRS.PiPathInv` verbatim.  This is the whole of the
residual, isolated. -/
def LRS.BetaFire : Prop :=
  ∀ {Γ : List SExpr} {A A₀ B₀ B₁ e e' : SExpr} {w : SLevel},
    Ctx.WF Γ → TypeDefEqPath Γ (.forallE A B₁) (.forallE A₀ B₀) w →
    IsDefEq (A :: Γ) e e B₁ → IsDefEq Γ e' e' A₀ →
    IsDefEq Γ (.app (.lam A e) e') (e.inst e') (B₀.inst e')

theorem LRS.BetaFire.of_piPathInv (piInv : LRS.PiPathInv) : LRS.BetaFire := by
  intro Γ A A₀ B₀ B₁ e e' w hΓ Q hb ha
  obtain ⟨ud, vd, Pdom, Pcod⟩ := piInv hΓ Q
  obtain ⟨_, Pdom'⟩ := Pdom.symm
  have ha' := Pdom'.defeqDF ha
  have Pcod' : TypeDefEqPath Γ (B₁.inst e') (B₀.inst e') vd := by
    simpa only [SExpr.inst] using
      Pcod.subst (Ctx.Subst.one IsDefEq.weakCore IsDefEq.bvar ha')
  exact Pcod'.defeqDF (.beta hb ha')

/-- **The sort restriction does not dodge β.**  A sort-typed β-redex whose
application domain is *not* the abstraction's own: `A₀` is the redex
`(fun _ : Sort (l+2) => #0) (Sort (l+1))`, which is `IsDefEq`-equal to
`Sort (l+1)` but syntactically an `.app`, so no syntactic reconciliation is
available.  Everything is in the empty context with no environment
assumptions.

Consequently, restricting a rung to sort-typed subjects removes nothing from
the β case: sort-typedness constrains the *result* type, never the domain.
The narrowing is not an escape. -/
theorem betaSort_domain_unconstrained {l : SLevel} :
    ∃ A₀ : SExpr, A₀ ≠ .sort l.succ ∧
      IsDefEq [] (.lam (.sort l.succ) (.bvar 0)) (.lam (.sort l.succ) (.bvar 0))
        (.forallE A₀ (.sort l.succ)) ∧
      IsDefEq [] (.sort l) (.sort l) A₀ ∧
      IsDefEq [] (.app (.lam (.sort l.succ) (.bvar 0)) (.sort l))
        (.app (.lam (.sort l.succ) (.bvar 0)) (.sort l)) (.sort l.succ) ∧
      ParRed [] (.app (.lam (.sort l.succ) (.bvar 0)) (.sort l)) (.sort l) := by
  have hβ : IsDefEq ([] : List SExpr)
      (.app (.lam (.sort l.succ.succ) (.bvar 0)) (.sort l.succ)) (.sort l.succ)
      (.sort l.succ.succ) := .beta (.bvar .zero) .sort
  have hlam : IsDefEq ([] : List SExpr) (.lam (.sort l.succ) (.bvar 0))
      (.lam (.sort l.succ) (.bvar 0))
      (.forallE (.sort l.succ) (.sort l.succ)) := .lamDF .sort (.bvar .zero)
  have hPi := IsDefEq.forallEDF hβ.symm (IsDefEq.sort (l := l.succ))
  refine ⟨.app (.lam (.sort l.succ.succ) (.bvar 0)) (.sort l.succ), nofun,
    hPi.defeqDF hlam, hβ.symm.defeqDF .sort,
    .appDF (hPi.defeqDF hlam) (hβ.symm.defeqDF .sort), .beta .rfl .rfl⟩

/-- Vacuity discipline for `LRS.BetaFire`, at a **non-degenerate** instance:
the witness of `betaSort_domain_unconstrained`, whose application domain is
syntactically different from the abstraction's own.  So the Prop is inhabited
off the diagonal, where all its content is. -/
theorem LRS.betaFire_nonvacuous (fire : LRS.BetaFire) {l : SLevel} :
    IsDefEq [] (.app (.lam (.sort l.succ) (.bvar 0)) (.sort l)) (.sort l)
      (.sort l.succ) := by
  have hβ : IsDefEq ([] : List SExpr)
      (.app (.lam (.sort l.succ.succ) (.bvar 0)) (.sort l.succ)) (.sort l.succ)
      (.sort l.succ.succ) := .beta (.bvar .zero) .sort
  have hPi := IsDefEq.forallEDF hβ.symm (IsDefEq.sort (l := l.succ))
  exact fire (Γ := []) (A := .sort l.succ) (B₁ := .sort l.succ)
    (B₀ := .sort l.succ) (e := .bvar 0) (e' := .sort l)
    trivial (.single hPi) (.bvar .zero) (hβ.symm.defeqDF .sort)

/-- **The stratification escape, on the consumer side.**  A depth-indexed rung
would have to be spent once per `≫` link of a `ParRedS` chain, and at link
`i+1` the walk anchors the call at the *accumulated* `TypeDefEqPath`'s right
endpoint — a path that carries no stratification data and whose length is
bounded by nothing in scope.  This is the datum the walk must then manufacture
at every link. -/
def LRS.ChainAnchorAt (d : Nat) : Prop :=
  ∀ {Γ : List SExpr} {A B : SExpr} {u : SLevel},
    Ctx.WF Γ → TypeDefEqPath Γ A B u → ∃ V c, HasTypeStratifiedS Γ B V c d

/-- **The obstruction.**  The anchor demand *is* a uniform stratification
bound: every well-typed type in every well-formed context stratified at one
fixed `d`.  That is exactly probeS's `LRS.PathRestratifyAt.uniformDepthBound`
— the same fatal proposition, whose truth makes the bootstrap's strong
induction vacuous. -/
theorem LRS.ChainAnchorAt.uniformDepthBound {d : Nat} (anc : LRS.ChainAnchorAt d)
    {Γ : List SExpr} {A : SExpr} {u : SLevel} (hΓ : Ctx.WF Γ)
    (h : IsDefEq Γ A A (.sort u)) : ∃ V c, HasTypeStratifiedS Γ A V c d :=
  anc hΓ (.single h)

/-- …and conversely, so there is nothing weaker to aim at: the anchor demand
and the uniform bound are the same proposition.  Net: the stratification
escape does not close. -/
theorem LRS.ChainAnchorAt.of_uniformDepthBound {d : Nat}
    (bound : ∀ {Γ : List SExpr} {A : SExpr} {u : SLevel}, Ctx.WF Γ →
      IsDefEq Γ A A (.sort u) → ∃ V c, HasTypeStratifiedS Γ A V c d) :
    LRS.ChainAnchorAt d := by
  intro Γ A B u hΓ P
  obtain ⟨_, h⟩ := P.rightType
  exact bound hΓ h

/-- Vacuity discipline for `LRS.ChainAnchorAt`: its hypothesis is inhabited in
the empty context with no environment assumptions, so the Prop is not empty —
which is what makes the equivalence above a real obstruction rather than a
vacuous one. -/
theorem LRS.chainAnchorAt_nonvacuous (anc : LRS.ChainAnchorAt 0) {l : SLevel} :
    ∃ V c, HasTypeStratifiedS [] (.sort l) V c 0 :=
  anc trivial (.single (IsDefEq.sort (l := l)))

/-! ## Banking probe R13 — the `RectFrame` bridge at the `indTy` observation

`plans/probes/probeR13-rectframe.lean` established that the frame layer of
the coherent iota leaf is mechanical *given* a frame that carries the type
shape alongside the element shape (`LRS.RectFrame` below), and recorded its
production as a non-additive residual: `LogRel.DefEqRect.mono_l` needs
`m.HasType a` and `m'.HasType a` for one common `a`, a frame recording only
`m ≤ m'` can supply neither, and choosing `a` inside the transport is the
independent re-selection of the type observation the N2 decision forbids —
so the shape seemed to require threading through every frame *producer*.

The residual dissolves: at a constructor observation the type shape is not
an independent choice at all.  It is always `WShape.indTy` (`LRS.IndDefEq`
pairs a `CtorDefEq` with exactly that observation), the shapes an unpaired
`LRS.CtorFrame` passes through are only `.bot` and `.ctor` forms
(`WShape.le_ctor` below closes the missing right-hand inversion; the
existing `WShape.ctor_le` has `ctor` on the left, and
`WShape.HasType.mono_l` demands antisymmetry), both of those rows of the
`Shape.hasType` table at `.indTy` are true, and `indTy` is lift-stable
(`WShape.lift_indTy`) — matching the frame's `lift`/`unlift` moves.  So the
paired frame is *recoverable* from the unpaired one
(`LRS.CtorFrame.toRectFrame`), additively, with no producer touched. -/

/-- Right-hand constructor inversion for the shape order: anything below a
`ctor` shape is `.bot` or a `ctor` form with the same head.  The existing
`WShape.ctor_le` inverts from the left only; this is the mirror of
`WShape.le_indTy` one constructor over. -/
theorem WShape.le_ctor {s : WShape (n+1)} {c : Name} {l : List (WShape n)} {h} :
    s ≤ .ctor c l h ↔
      s = .bot ∨ ∃ l' h', s = .ctor c l' h' ∧ List.Forall₂ (· ≤ ·) l' l := by
  constructor
  · cases s using WShape.casesOn' with
    | bot => exact fun _ => .inl rfl
    | ctor c' l' h' =>
      intro hle
      obtain ⟨l'', h'', heq, hf⟩ := WShape.ctor_le.1 hle
      obtain ⟨rfl, rfl⟩ := WShape.ctor.inj.1 heq
      exact .inr ⟨l', h', rfl, hf⟩
    | indTy => apply Not.elim; simp [indTy, ctor, LE.def, Shape.LE.def]
    | _ => simp only [sort, forallE, lam, ctor, LE.def, Shape.LE.def, false_implies]
  · rintro (rfl | ⟨l', h', rfl, hf⟩)
    · exact bot_le
    · exact WShape.ctor_le.2 ⟨l, h, rfl, hf⟩

/-- info: 'Lean4Lean.SExpr.WShape.le_ctor' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms WShape.le_ctor

/-- `HasType · .indTy` is downward closed along the shape order: below a
shape typed at `indTy` there are only `.bot` and `.ctor` forms
(`WShape.le_ctor`), and both rows of the `Shape.hasType` table at `.indTy`
are true. -/
theorem WShape.hasType_indTy_of_le {m m' : WShape (n+1)}
    (hle : m ≤ m') (hm' : m'.HasType .indTy) : m.HasType .indTy := by
  cases m' using WShape.casesOn' with
  | bot =>
    cases WShape.le_bot.1 hle
    exact WShape.HasType.bot' WShape.HasType.indTy
  | ctor c l h =>
    obtain rfl | ⟨l', h', rfl, -⟩ := WShape.le_ctor.1 hle
    · exact WShape.HasType.bot' WShape.HasType.indTy
    · exact WShape.HasType.ctor
  | _ => cases hm'

/-- info: 'Lean4Lean.SExpr.WShape.hasType_indTy_of_le' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms WShape.hasType_indTy_of_le

/-- `HasType · .indTy` is lift-stable, because `indTy` itself is
(`WShape.lift_indTy`). -/
theorem WShape.hasType_indTy_lift {n n' : Nat} (le : n ≤ n') {m : WShape (n+1)} :
    (m.lift (n'+1)).HasType .indTy ↔ m.HasType .indTy := by
  have h := WShape.HasType.lift (m := m) (a := .indTy) (Nat.succ_le_succ le)
  rwa [WShape.lift_indTy] at h

/--
info: 'Lean4Lean.SExpr.WShape.hasType_indTy_lift' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms WShape.hasType_indTy_lift

/-- `LRS.CtorFrame` with the **type** shape threaded alongside the element
shape, and the `HasType` coherence recorded at each step where the element
shape moves.  Structurally identical to `LRS.CtorFrame` (same four
constructors, same level arithmetic); the only difference is that `a` rides
along instead of being re-chosen. -/
inductive LRS.RectFrame (Γ : List SExpr) :
    {n k : Nat} → LogRel Γ n → WShape n → WShape n →
      LogRel Γ k → WShape k → WShape k → Prop where
  | refl : RectFrame Γ IH m a IH m a
  | mono : m ≤ m' → m.HasType a → m'.HasType a →
      RectFrame Γ IH m' a J p q → RectFrame Γ IH m a J p q
  | lift {IH : LogRel Γ n} {IH' : LogRel Γ n'} (le : n ≤ n')
      (E : LogRel.LiftEquiv IH IH' le) (hma : m.HasType a) :
      RectFrame Γ IH m a J p q →
      RectFrame Γ IH' (m.lift n') (a.lift n') J p q
  | unlift {IH : LogRel Γ n} {IH' : LogRel Γ n'} (le : n ≤ n')
      (E : LogRel.LiftEquiv IH IH' le) (hma : m.HasType a) :
      RectFrame Γ IH' (m.lift n') (a.lift n') J p q →
      RectFrame Γ IH m a J p q

/-- **The frame layer is mechanical.**  Every case is a one-liner against
machinery that already exists: `LogRel.DefEqRect.mono_l` for `mono` and
`LogRel.LiftEquiv.rect` (both directions) for `lift`/`unlift`. -/
theorem LRS.RectFrame.rect {Γ : List SExpr} {n k : Nat}
    {IH : LogRel Γ n} {m a : WShape n} {J : LogRel Γ k} {p q : WShape k}
    {M₁ M₂ N₁ N₂ A : SExpr}
    (F : LRS.RectFrame Γ IH m a J p q)
    (H : LogRel.DefEqRect J M₁ M₂ N₁ N₂ A p q) :
    LogRel.DefEqRect IH M₁ M₂ N₁ N₂ A m a := by
  induction F with
  | refl => exact H
  | mono hle hm hm' _ ih => exact (ih H).mono_l hle hm hm'
  | lift le E hma _ ih => exact (E.rect hma).2 (ih H)
  | unlift le E hma _ ih => exact (E.rect hma).1 (ih H)

/--
info: 'Lean4Lean.SExpr.LRS.RectFrame.rect' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRS.RectFrame.rect

/-- The transported rectangle with both rows flipped, from the same frame. -/
theorem LRS.RectFrame.symm_rect {Γ : List SExpr} {n k : Nat}
    {IH : LogRel Γ n} {m a : WShape n} {J : LogRel Γ k} {p q : WShape k}
    {M₁ M₂ N₁ N₂ A : SExpr}
    (F : LRS.RectFrame Γ IH m a J p q)
    (H : LogRel.DefEqRect J M₁ M₂ N₁ N₂ A p q) :
    LogRel.DefEqRect IH M₂ M₁ N₂ N₁ A m a :=
  let R := F.rect H
  ⟨IH.symm R.left, IH.symm R.right,
    IH.trans (IH.symm R.left) (IH.trans R.cross (IH.symm R.right))⟩

/--
info: 'Lean4Lean.SExpr.LRS.RectFrame.symm_rect' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRS.RectFrame.symm_rect

/-- The paired frame composes, so it is a usable index. -/
theorem LRS.RectFrame.trans {Γ : List SExpr} {n k l : Nat}
    {IH : LogRel Γ n} {m a : WShape n} {J : LogRel Γ k} {p q : WShape k}
    {K : LogRel Γ l} {x y : WShape l}
    (F : LRS.RectFrame Γ IH m a J p q) (G : LRS.RectFrame Γ J p q K x y) :
    LRS.RectFrame Γ IH m a K x y := by
  induction F with
  | refl => exact G
  | mono hle hm hm' _ ih => exact .mono hle hm hm' (ih G)
  | lift le E hma _ ih => exact .lift le E hma (ih G)
  | unlift le E hma _ ih => exact .unlift le E hma (ih G)

/--
info: 'Lean4Lean.SExpr.LRS.RectFrame.trans' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRS.RectFrame.trans

/-- Vacuity discipline: `LRS.RectFrame` is inhabited by `refl` at every
`(IH, m, a)`, which is the frame every native leaf starts from. -/
theorem LRS.rectFrame_nonvacuous {Γ : List SExpr} {n : Nat}
    {IH : LogRel Γ n} {m a : WShape n} : LRS.RectFrame Γ IH m a IH m a := .refl

/--
info: 'Lean4Lean.SExpr.LRS.rectFrame_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRS.rectFrame_nonvacuous

/-- The `indTy` observation rides along an unpaired constructor frame: every
element shape the frame passes through is typed at `indTy` as soon as the
leaf shape is. -/
theorem LRS.CtorFrame.hasType_indTy
    (F : LRS.CtorFrame Γ IH m J p) :
    p.HasType .indTy → m.HasType .indTy := by
  induction F with
  | refl => exact id
  | mono hle _ ih => exact fun hp => WShape.hasType_indTy_of_le hle (ih hp)
  | lift le E _ ih => exact fun hp => (WShape.hasType_indTy_lift le).2 (ih hp)
  | unlift le E _ ih => exact fun hp => (WShape.hasType_indTy_lift le).1 (ih hp)

/--
info: 'Lean4Lean.SExpr.LRS.CtorFrame.hasType_indTy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRS.CtorFrame.hasType_indTy

/-- **The index upgrade is recoverable.**  At a constructor observation the
type shape is not an independent choice: it is always `indTy`, and an
unpaired `LRS.CtorFrame` upgrades to the paired `LRS.RectFrame` at
`a := q := .indTy` with no producer touched.  `mono` recovers both `HasType`
witnesses from `WShape.hasType_indTy_of_le`; `lift`/`unlift` ride
`WShape.lift_indTy` through one `LRS` layer via `LogRel.LiftEquiv.succ`. -/
theorem LRS.CtorFrame.toRectFrame
    (F : LRS.CtorFrame Γ IH m J p) :
    p.HasType .indTy →
      LRS.RectFrame Γ (LRS IH) m .indTy (LRS J) p .indTy := by
  induction F with
  | refl => exact fun _ => .refl
  | mono hle F' ih =>
    intro hp
    have hm' := F'.hasType_indTy hp
    exact .mono hle (WShape.hasType_indTy_of_le hle hm') hm' (ih hp)
  | lift le E F' ih =>
    intro hp
    have h := LRS.RectFrame.lift (Nat.succ_le_succ le) E.succ
      (F'.hasType_indTy hp) (ih hp)
    rwa [WShape.lift_indTy] at h
  | unlift le E F' ih =>
    intro hp
    refine LRS.RectFrame.unlift (Nat.succ_le_succ le) E.succ
      ((WShape.hasType_indTy_lift le).1 (F'.hasType_indTy hp)) ?_
    rw [WShape.lift_indTy]
    exact ih hp

/--
info: 'Lean4Lean.SExpr.LRS.CtorFrame.toRectFrame' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRS.CtorFrame.toRectFrame

/-- The residual, discharged end-to-end: an unpaired constructor frame
transports a synchronized rectangle at the `indTy` observation. -/
theorem LRS.CtorFrame.rect
    (F : LRS.CtorFrame Γ IH m J p) (hp : p.HasType .indTy)
    {M₁ M₂ N₁ N₂ A : SExpr}
    (H : LogRel.DefEqRect (LRS J) M₁ M₂ N₁ N₂ A p .indTy) :
    LogRel.DefEqRect (LRS IH) M₁ M₂ N₁ N₂ A m .indTy :=
  (F.toRectFrame hp).rect H

/--
info: 'Lean4Lean.SExpr.LRS.CtorFrame.rect' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRS.CtorFrame.rect

/-! ## Banking probe W16 — the rec-app-observation frame: the `RecAppFrame`
widening

`plans/probes/probeW16-rectframe-recapp.lean` discharged the remaining
`RectFrame` transport instance of the coherent iota leaf: the one at the
recursor-application observation `(out, outTy)`.  The rec-app observation at
a frame vertex with major observation `m` is `(f.app m, g.app m)` for the
spine's result/result-type shape functions.  Unlike the `.indTy` type shape
of the constructor observation — constant, lift-rigid, and recoverable at
every vertex — the rec-app TYPE observation `g.app m` *moves* along the
frame's `mono` steps (`WShapeFun.app_mono_r`), while `LRS.RectFrame.mono`
holds its type shape fixed.  That is a theorem, not a style choice: the
landed frame's type observation is rigid up to lifts
(`LRS.RectFrame.tyShape_rigid`), and the moving two-point family
`LRS.RecAppMoving` below is connected by the widened frame
(`LRS.recAppFrame_reaches`) but provably by no `RectFrame`
(`LRS.rectFrame_cannot_recApp`).

So the honest instance is a *minimal widening*: `LRS.RecAppFrame` is
`RectFrame` with the `mono` constructor allowed to lower the type shape
alongside the element shape, carrying exactly the coherence facts the
composite `DefEqRect.mono_l ∘ DefEqRect.mono_r_2` spends.  Every
widened-`mono` premise is derivable at applied observations from *diagonal*
data only — the pointwise typings `(f.app x).HasType (g.app x)` and
sort-typedness of `g.app`, i.e. the `WShape.HasTypeLam.iff'`/`HasTypePi.iff'`
components the spine already retains — so no independent re-selection of the
type observation occurs (N2-compliant): `appMono`/`appLift`/`appUnlift` are
the per-frame-step producers and `ofApp_le` the one-step instance.
`LRS.RecAppSync` packages the whole obligation the way `toRectFrame` did:
it refines `CtorFrame` with the per-vertex function pair,
`RecAppSync.toRecAppFrame` is the rec-app-observation instance, and
`RecAppSync.rect` is the end-to-end transport whose hypothesis is the exact
conclusion type of the leaf rectangle producer.  Finally the landed
ctor-observation instance factors through the widening
(`LRS.CtorFrame.toRecAppFrame_indTy`), so one transport type serves both
observations. -/

/-- `LRS.RectFrame` with a type-shape-moving `mono`.  Fields of `mono`, in
order: element order, type order, the target diagonal `m.HasType a`, the
cross fact `m.HasType a'`, the source diagonal `m'.HasType a'`, and
`a'.HasType .type` (spent by `DefEqRect.mono_r_2`).  `refl`/`lift`/`unlift`
are verbatim `RectFrame`'s. -/
inductive LRS.RecAppFrame (Γ : List SExpr) :
    {n k : Nat} → LogRel Γ n → WShape n → WShape n →
      LogRel Γ k → WShape k → WShape k → Prop where
  | refl : RecAppFrame Γ IH m a IH m a
  | mono : m ≤ m' → a ≤ a' → m.HasType a → m.HasType a' → m'.HasType a' →
      WShape.HasType a' .type →
      RecAppFrame Γ IH m' a' J p q → RecAppFrame Γ IH m a J p q
  | lift {IH : LogRel Γ n} {IH' : LogRel Γ n'} (le : n ≤ n')
      (E : LogRel.LiftEquiv IH IH' le) (hma : m.HasType a) :
      RecAppFrame Γ IH m a J p q →
      RecAppFrame Γ IH' (m.lift n') (a.lift n') J p q
  | unlift {IH : LogRel Γ n} {IH' : LogRel Γ n'} (le : n ≤ n')
      (E : LogRel.LiftEquiv IH IH' le) (hma : m.HasType a) :
      RecAppFrame Γ IH' (m.lift n') (a.lift n') J p q →
      RecAppFrame Γ IH m a J p q

/-- **The widened frame layer is still mechanical.**  `mono` is the composite
`DefEqRect.mono_l` (element down, at the source type shape) then
`DefEqRect.mono_r_2` (type down, at the target element shape); the other
cases are `RectFrame.rect`'s one-liners. -/
theorem LRS.RecAppFrame.rect {Γ : List SExpr} {n k : Nat}
    {IH : LogRel Γ n} {m a : WShape n} {J : LogRel Γ k} {p q : WShape k}
    {M₁ M₂ N₁ N₂ A : SExpr}
    (F : LRS.RecAppFrame Γ IH m a J p q)
    (H : LogRel.DefEqRect J M₁ M₂ N₁ N₂ A p q) :
    LogRel.DefEqRect IH M₁ M₂ N₁ N₂ A m a := by
  induction F with
  | refl => exact H
  | mono hm ha hma hma' hm'a' ha' _ ih =>
    exact ((ih H).mono_l hm hma' hm'a').mono_r_2 ha hma ha'
  | lift le E hma _ ih => exact (E.rect hma).2 (ih H)
  | unlift le E hma _ ih => exact (E.rect hma).1 (ih H)

/--
info: 'Lean4Lean.SExpr.LRS.RecAppFrame.rect' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRS.RecAppFrame.rect

/-- The transported rectangle with both rows flipped, from the same frame. -/
theorem LRS.RecAppFrame.symm_rect {Γ : List SExpr} {n k : Nat}
    {IH : LogRel Γ n} {m a : WShape n} {J : LogRel Γ k} {p q : WShape k}
    {M₁ M₂ N₁ N₂ A : SExpr}
    (F : LRS.RecAppFrame Γ IH m a J p q)
    (H : LogRel.DefEqRect J M₁ M₂ N₁ N₂ A p q) :
    LogRel.DefEqRect IH M₂ M₁ N₂ N₁ A m a :=
  let R := F.rect H
  ⟨IH.symm R.left, IH.symm R.right,
    IH.trans (IH.symm R.left) (IH.trans R.cross (IH.symm R.right))⟩

/--
info: 'Lean4Lean.SExpr.LRS.RecAppFrame.symm_rect' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRS.RecAppFrame.symm_rect

/-- The widened frame composes, so it is a usable index. -/
theorem LRS.RecAppFrame.trans {Γ : List SExpr} {n k l : Nat}
    {IH : LogRel Γ n} {m a : WShape n} {J : LogRel Γ k} {p q : WShape k}
    {K : LogRel Γ l} {x y : WShape l}
    (F : LRS.RecAppFrame Γ IH m a J p q) (G : LRS.RecAppFrame Γ J p q K x y) :
    LRS.RecAppFrame Γ IH m a K x y := by
  induction F with
  | refl => exact G
  | mono hm ha hma hma' hm'a' ha' _ ih => exact .mono hm ha hma hma' hm'a' ha' (ih G)
  | lift le E hma _ ih => exact .lift le E hma (ih G)
  | unlift le E hma _ ih => exact .unlift le E hma (ih G)

/--
info: 'Lean4Lean.SExpr.LRS.RecAppFrame.trans' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRS.RecAppFrame.trans

/-- Nothing is lost: every landed `RectFrame` is a `RecAppFrame` (the
degenerate type move, with `a'.HasType .type` recovered from the frame's own
diagonal via `WShape.HasType.isType`). -/
theorem LRS.RectFrame.toRecAppFrame {Γ : List SExpr} {n k : Nat}
    {IH : LogRel Γ n} {m a : WShape n} {J : LogRel Γ k} {p q : WShape k}
    (F : LRS.RectFrame Γ IH m a J p q) :
    LRS.RecAppFrame Γ IH m a J p q := by
  induction F with
  | refl => exact .refl
  | mono hle hm hm' _ ih => exact .mono hle WShape.LE.rfl hm hm hm' hm'.isType ih
  | lift le E hma _ ih => exact .lift le E hma ih
  | unlift le E hma _ ih => exact .unlift le E hma ih

/--
info: 'Lean4Lean.SExpr.LRS.RectFrame.toRecAppFrame' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRS.RectFrame.toRecAppFrame

/-- Vacuity discipline: inhabited by `refl` at every `(IH, m, a)`. -/
theorem LRS.recAppFrame_nonvacuous {Γ : List SExpr} {n : Nat}
    {IH : LogRel Γ n} {m a : WShape n} : LRS.RecAppFrame Γ IH m a IH m a := .refl

/--
info: 'Lean4Lean.SExpr.LRS.recAppFrame_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRS.recAppFrame_nonvacuous

/-! ### The applied-observation step producers

One producer per `CtorFrame` constructor shape, each consuming only data the
spine retains: the *diagonal* pointwise typings `(f.app x).HasType (g.app x)`
(the third component of `WShape.HasTypeLam.iff'`) and sort-typedness of the
type-side application (the second component of `WShape.HasTypePi.iff'`).
The cross fact `(f.app m).HasType (g.app m')` is *derived* —
`WShape.HasType.mono_r` raises the diagonal along `WShapeFun.app_mono_r` —
never chosen, which is what keeps the N2 discipline intact. -/

/-- One frame-`mono` step at the rec-app observation, from diagonal data. -/
theorem LRS.RecAppFrame.appMono {Γ : List SExpr} {n k : Nat}
    {IH : LogRel Γ n} {J : LogRel Γ k} {p q : WShape k}
    {f g : WShapeFun n} {m m' : WShape n} {r : Bool}
    (hle : m ≤ m')
    (hdm : (f.app m).HasType (g.app m))
    (hdm' : (f.app m').HasType (g.app m'))
    (hsort : (g.app m').HasType (.sort r))
    (F : LRS.RecAppFrame Γ IH (f.app m') (g.app m') J p q) :
    LRS.RecAppFrame Γ IH (f.app m) (g.app m) J p q :=
  .mono (WShapeFun.app_mono_r hle) (WShapeFun.app_mono_r hle)
    hdm (WShape.HasType.mono_r (WShapeFun.app_mono_r hle) hsort hdm) hdm'
    hsort.toType F

/--
info: 'Lean4Lean.SExpr.LRS.RecAppFrame.appMono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRS.RecAppFrame.appMono

/-- One frame-`lift` step at the rec-app observation: the function pair
lifts, and `WShapeFun.lift_app` commutes the applied observation. -/
theorem LRS.RecAppFrame.appLift {Γ : List SExpr} {n n' k : Nat}
    {IH : LogRel Γ n} {IH' : LogRel Γ n'} {J : LogRel Γ k} {p q : WShape k}
    (le : n ≤ n') (E : LogRel.LiftEquiv IH IH' le)
    {f g : WShapeFun n} {x : WShape n}
    (hd : (f.app x).HasType (g.app x))
    (F : LRS.RecAppFrame Γ IH (f.app x) (g.app x) J p q) :
    LRS.RecAppFrame Γ IH' ((f.lift n').app (x.lift n'))
      ((g.lift n').app (x.lift n')) J p q := by
  rw [← WShapeFun.lift_app le, ← WShapeFun.lift_app le]
  exact .lift le E hd F

/--
info: 'Lean4Lean.SExpr.LRS.RecAppFrame.appLift' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRS.RecAppFrame.appLift

/-- One frame-`unlift` step at the rec-app observation. -/
theorem LRS.RecAppFrame.appUnlift {Γ : List SExpr} {n n' k : Nat}
    {IH : LogRel Γ n} {IH' : LogRel Γ n'} {J : LogRel Γ k} {p q : WShape k}
    (le : n ≤ n') (E : LogRel.LiftEquiv IH IH' le)
    {f g : WShapeFun n} {x : WShape n}
    (hd : (f.app x).HasType (g.app x))
    (F : LRS.RecAppFrame Γ IH' ((f.lift n').app (x.lift n'))
      ((g.lift n').app (x.lift n')) J p q) :
    LRS.RecAppFrame Γ IH (f.app x) (g.app x) J p q := by
  rw [← WShapeFun.lift_app le, ← WShapeFun.lift_app le] at F
  exact .unlift le E hd F

/--
info: 'Lean4Lean.SExpr.LRS.RecAppFrame.appUnlift' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRS.RecAppFrame.appUnlift

/-- The same-level rec-app-observation instance in one step: any `m ≤ m'`
induces the widened frame between the two applied observations, from
diagonal data alone.  (This is the `toRectFrame` analogue for the fragment
of a `CtorFrame` that stays at one level.) -/
theorem LRS.RecAppFrame.ofApp_le {Γ : List SExpr} {n : Nat}
    {IH : LogRel Γ n} {f g : WShapeFun n} {m m' : WShape n} {r : Bool}
    (hle : m ≤ m')
    (hdm : (f.app m).HasType (g.app m))
    (hdm' : (f.app m').HasType (g.app m'))
    (hsort : (g.app m').HasType (.sort r)) :
    LRS.RecAppFrame Γ IH (f.app m) (g.app m) IH (f.app m') (g.app m') :=
  LRS.RecAppFrame.appMono hle hdm hdm' hsort .refl

/--
info: 'Lean4Lean.SExpr.LRS.RecAppFrame.ofApp_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRS.RecAppFrame.ofApp_le

/-- For contrast, where the landed frame already suffices: a family whose
type observation is a *constant* shape transports through plain
`RectFrame.mono` from the diagonal alone. -/
theorem LRS.RectFrame.ofApp_le_constTy {Γ : List SExpr} {n : Nat}
    {IH : LogRel Γ n} {f : WShapeFun n} {c : WShape n} {m m' : WShape n}
    (hle : m ≤ m')
    (hdm : (f.app m).HasType c) (hdm' : (f.app m').HasType c) :
    LRS.RectFrame Γ IH (f.app m) c IH (f.app m') c :=
  .mono (WShapeFun.app_mono_r hle) hdm hdm' .refl

/--
info: 'Lean4Lean.SExpr.LRS.RectFrame.ofApp_le_constTy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRS.RectFrame.ofApp_le_constTy

/-! ### Separation: the widening is necessary, not stylistic

The landed `RectFrame`'s type observation is rigid up to lifts, as a
theorem; and the concrete two-point rec-app family `LRS.RecAppMoving` moves
its type observation, so no `RectFrame` connects its endpoints while
`ofApp_le` does.  The moving family also serves as the off-diagonal
non-vacuity witness for the step producers. -/

/-- The landed frame's type observation is constant up to lift-erasure. -/
theorem LRS.RectFrame.tyShape_rigid {Γ : List SExpr} {n k : Nat}
    {IH : LogRel Γ n} {m a : WShape n} {J : LogRel Γ k} {p q : WShape k}
    (F : LRS.RectFrame Γ IH m a J p q) : a.T ≤ q.T ∧ q.T ≤ a.T := by
  induction F with
  | refl => exact ⟨TShape.LE.rfl, TShape.LE.rfl⟩
  | mono _ _ _ _ ih => exact ih
  | lift le E hma _ ih =>
    exact ⟨(TShape.lift_eqv le).1.trans ih.1, ih.2.trans (TShape.lift_eqv le).2⟩
  | unlift le E hma _ ih =>
    exact ⟨(TShape.lift_eqv le).2.trans ih.1, ih.2.trans (TShape.lift_eqv le).1⟩

/--
info: 'Lean4Lean.SExpr.LRS.RectFrame.tyShape_rigid' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRS.RectFrame.tyShape_rigid

/-- A sort shape never sits below bottom (the two-point separation witness
needs this inversion at both of its vertices). -/
theorem WShape.sort_not_le_bot {n : Nat} {r : Bool} :
    ¬((WShape.sort r : WShape n) ≤ .bot) := by
  intro h
  have h' := WShape.le_bot.1 h
  have h'' : (WShape.sort r : WShape n).1 = (WShape.bot : WShape n).1 :=
    congrArg Subtype.val h'
  cases n <;> simp [WShape.sort, WShape.bot, Shape.sort, Shape.bot] at h''

/-- Bottom is typed at bottom, at every level. -/
theorem WShape.hasType_bot_bot {n : Nat} :
    (WShape.bot : WShape n).HasType .bot :=
  WShape.HasType.bot' (WShape.HasType.bot' WShape.HasType.sort)

/-- The moving rec-app family, element side: `.bot ↦ .bot`,
`.sort true ↦ .sort false`. -/
abbrev LRS.RecAppMoving.f {n : Nat} : WShapeFun n :=
  WShapeFun.single (.sort true) (.sort false)

/-- The moving rec-app family, type side: `.bot ↦ .bot`,
`.sort true ↦ .sort true`. -/
abbrev LRS.RecAppMoving.g {n : Nat} : WShapeFun n :=
  WShapeFun.single (.sort true) (.sort true)

theorem LRS.RecAppMoving.f_bot {n : Nat} :
    (LRS.RecAppMoving.f (n := n)).app .bot = .bot := by
  rw [LRS.RecAppMoving.f, WShapeFun.single_app, if_neg WShape.sort_not_le_bot]

theorem LRS.RecAppMoving.f_sort {n : Nat} :
    (LRS.RecAppMoving.f (n := n)).app (.sort true) = .sort false := by
  rw [LRS.RecAppMoving.f, WShapeFun.single_app, if_pos WShape.LE.rfl]

theorem LRS.RecAppMoving.g_bot {n : Nat} :
    (LRS.RecAppMoving.g (n := n)).app .bot = .bot := by
  rw [LRS.RecAppMoving.g, WShapeFun.single_app, if_neg WShape.sort_not_le_bot]

theorem LRS.RecAppMoving.g_sort {n : Nat} :
    (LRS.RecAppMoving.g (n := n)).app (.sort true) = .sort true := by
  rw [LRS.RecAppMoving.g, WShapeFun.single_app, if_pos WShape.LE.rfl]

/-- Diagonal typing of the moving family at `.bot`. -/
theorem LRS.RecAppMoving.diag_bot {n : Nat} :
    ((LRS.RecAppMoving.f (n := n)).app .bot).HasType
      ((LRS.RecAppMoving.g (n := n)).app .bot) := by
  rw [LRS.RecAppMoving.f_bot, LRS.RecAppMoving.g_bot]
  exact WShape.hasType_bot_bot

/-- Diagonal typing of the moving family at `.sort true`. -/
theorem LRS.RecAppMoving.diag_sort {n : Nat} :
    ((LRS.RecAppMoving.f (n := n)).app (.sort true)).HasType
      ((LRS.RecAppMoving.g (n := n)).app (.sort true)) := by
  rw [LRS.RecAppMoving.f_sort, LRS.RecAppMoving.g_sort]
  exact WShape.HasType.sort

/-- Sort-typedness of the moving family's type side at `.sort true`. -/
theorem LRS.RecAppMoving.sortTy_sort {n : Nat} :
    ((LRS.RecAppMoving.g (n := n)).app (.sort true)).HasType (.sort true) := by
  rw [LRS.RecAppMoving.g_sort]
  exact WShape.HasType.sort

/-- **Separation, negative half.**  No landed `RectFrame` connects the moving
family's two observations: the family's type observation moves from `.bot`
to `.sort true` while `tyShape_rigid` pins any `RectFrame`'s type observation
up to lift-erasure. -/
theorem LRS.rectFrame_cannot_recApp {Γ : List SExpr} {n : Nat}
    {IH : LogRel Γ n} :
    ¬ LRS.RectFrame Γ IH ((LRS.RecAppMoving.f (n := n)).app .bot)
        ((LRS.RecAppMoving.g (n := n)).app .bot)
        IH ((LRS.RecAppMoving.f (n := n)).app (.sort true))
        ((LRS.RecAppMoving.g (n := n)).app (.sort true)) := by
  intro F
  have h := F.tyShape_rigid.2
  rw [LRS.RecAppMoving.g_bot, LRS.RecAppMoving.g_sort] at h
  exact WShape.sort_not_le_bot (WShape.LE.of_T h)

/--
info: 'Lean4Lean.SExpr.LRS.rectFrame_cannot_recApp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRS.rectFrame_cannot_recApp

/-- **Separation, positive half** (and the step producers' off-diagonal
non-vacuity witness): the widened frame connects the same two observations
from the diagonal data alone. -/
theorem LRS.recAppFrame_reaches {Γ : List SExpr} {n : Nat}
    {IH : LogRel Γ n} :
    LRS.RecAppFrame Γ IH ((LRS.RecAppMoving.f (n := n)).app .bot)
      ((LRS.RecAppMoving.g (n := n)).app .bot)
      IH ((LRS.RecAppMoving.f (n := n)).app (.sort true))
      ((LRS.RecAppMoving.g (n := n)).app (.sort true)) :=
  LRS.RecAppFrame.ofApp_le WShape.bot_le LRS.RecAppMoving.diag_bot
    LRS.RecAppMoving.diag_sort LRS.RecAppMoving.sortTy_sort

/--
info: 'Lean4Lean.SExpr.LRS.recAppFrame_reaches' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRS.recAppFrame_reaches

/-- The witness really is off-diagonal: both observations move. -/
theorem LRS.RecAppMoving.moves {n : Nat} :
    (LRS.RecAppMoving.f (n := n)).app .bot ≠
      (LRS.RecAppMoving.f (n := n)).app (.sort true) := by
  rw [LRS.RecAppMoving.f_bot, LRS.RecAppMoving.f_sort]
  intro h
  have h' : (WShape.bot : WShape n).1 = (WShape.sort false : WShape n).1 :=
    congrArg Subtype.val h
  cases n <;> simp [WShape.sort, WShape.bot, Shape.sort, Shape.bot] at h'

/--
info: 'Lean4Lean.SExpr.LRS.RecAppMoving.moves' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRS.RecAppMoving.moves

/-! ### The synchronized producer along a constructor frame

`LRS.RecAppSync` refines `LRS.CtorFrame` with the per-vertex result-shape
function pair: constant across `mono` (a `mono` step moves only the major
observation), lifted across `lift`/`unlift` (a level step lifts the whole
spine — `LR.PatternLeafSpine.lift` lifts `resultShape`/`resultTypeShape` by
exactly `WShapeFun.lift`, and `LE_Interp.Matches.lift`/`.unlift` move the
match data in both directions).  Each constructor carries the diagonal facts
the step producers spend.  `toCtorFrame` shows it is a refinement;
`toRecAppFrame` is **the rec-app-observation instance**; `rect` is the
end-to-end transport whose hypothesis is the exact conclusion type of
`LRS.iotaDefEqRect_of_ctorExactAt` at the native leaf. -/

/-- A constructor frame synchronized with its rec-app observation data. -/
inductive LRS.RecAppSync (Γ : List SExpr) :
    {n k : Nat} → LogRel Γ n → WShape (n + 1) →
      WShapeFun (n + 1) → WShapeFun (n + 1) →
      LogRel Γ k → WShape (k + 1) →
      WShapeFun (k + 1) → WShapeFun (k + 1) → Prop where
  | refl : RecAppSync Γ IH m f g IH m f g
  | mono {n k : Nat} {IH : LogRel Γ n} {J : LogRel Γ k}
      {m m' : WShape (n + 1)} {f g : WShapeFun (n + 1)}
      {p : WShape (k + 1)} {f₀ g₀ : WShapeFun (k + 1)} {r : Bool} :
      m ≤ m' →
      (f.app m).HasType (g.app m) →
      (f.app m').HasType (g.app m') →
      (g.app m').HasType (.sort r) →
      RecAppSync Γ IH m' f g J p f₀ g₀ →
      RecAppSync Γ IH m f g J p f₀ g₀
  | lift {n n' k : Nat} {IH : LogRel Γ n} {IH' : LogRel Γ n'} {J : LogRel Γ k}
      {m : WShape (n + 1)} {f g : WShapeFun (n + 1)}
      {p : WShape (k + 1)} {f₀ g₀ : WShapeFun (k + 1)}
      (le : n ≤ n') (E : LogRel.LiftEquiv IH IH' le) :
      (f.app m).HasType (g.app m) →
      RecAppSync Γ IH m f g J p f₀ g₀ →
      RecAppSync Γ IH' (m.lift (n' + 1)) (f.lift (n' + 1)) (g.lift (n' + 1))
        J p f₀ g₀
  | unlift {n n' k : Nat} {IH : LogRel Γ n} {IH' : LogRel Γ n'} {J : LogRel Γ k}
      {m : WShape (n + 1)} {f g : WShapeFun (n + 1)}
      {p : WShape (k + 1)} {f₀ g₀ : WShapeFun (k + 1)}
      (le : n ≤ n') (E : LogRel.LiftEquiv IH IH' le) :
      (f.app m).HasType (g.app m) →
      RecAppSync Γ IH' (m.lift (n' + 1)) (f.lift (n' + 1)) (g.lift (n' + 1))
        J p f₀ g₀ →
      RecAppSync Γ IH m f g J p f₀ g₀

/-- The synchronization is a refinement: forgetting the function pair
recovers the unpaired constructor frame, step for step. -/
theorem LRS.RecAppSync.toCtorFrame {Γ : List SExpr} {n k : Nat}
    {IH : LogRel Γ n} {m : WShape (n + 1)} {f g : WShapeFun (n + 1)}
    {J : LogRel Γ k} {p : WShape (k + 1)} {f₀ g₀ : WShapeFun (k + 1)}
    (S : LRS.RecAppSync Γ IH m f g J p f₀ g₀) :
    LRS.CtorFrame Γ IH m J p := by
  induction S with
  | refl => exact .refl
  | mono hle _ _ _ _ ih => exact .mono hle ih
  | lift le E _ _ ih => exact .lift le E ih
  | unlift le E _ _ ih => exact .unlift le E ih

/--
info: 'Lean4Lean.SExpr.LRS.RecAppSync.toCtorFrame' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRS.RecAppSync.toCtorFrame

/-- **The rec-app-observation instance.**  A synchronized constructor frame
yields the widened paired frame between the root's rec-app observation
`(f.app m, g.app m)` and the native leaf's `(f₀.app p, g₀.app p)`, one shape
level up — exactly where `LRS.CtorFrame.toRectFrame` puts the constructor
observation's instance. -/
theorem LRS.RecAppSync.toRecAppFrame {Γ : List SExpr} {n k : Nat}
    {IH : LogRel Γ n} {m : WShape (n + 1)} {f g : WShapeFun (n + 1)}
    {J : LogRel Γ k} {p : WShape (k + 1)} {f₀ g₀ : WShapeFun (k + 1)}
    (S : LRS.RecAppSync Γ IH m f g J p f₀ g₀) :
    LRS.RecAppFrame Γ (LRS IH) (f.app m) (g.app m)
      (LRS J) (f₀.app p) (g₀.app p) := by
  induction S with
  | refl => exact .refl
  | mono hle hd hd' hs _ ih => exact LRS.RecAppFrame.appMono hle hd hd' hs ih
  | lift le E hd _ ih =>
    exact LRS.RecAppFrame.appLift (Nat.succ_le_succ le) E.succ hd ih
  | unlift le E hd _ ih =>
    exact LRS.RecAppFrame.appUnlift (Nat.succ_le_succ le) E.succ hd ih

/--
info: 'Lean4Lean.SExpr.LRS.RecAppSync.toRecAppFrame' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRS.RecAppSync.toRecAppFrame

/-- **End to end**: the synchronized frame transports the rectangle produced
at the native leaf's recursor-application observation — the conclusion type
of `LRS.iotaDefEqRect_of_ctorExactAt` — back to the root's. -/
theorem LRS.RecAppSync.rect {Γ : List SExpr} {n k : Nat}
    {IH : LogRel Γ n} {m : WShape (n + 1)} {f g : WShapeFun (n + 1)}
    {J : LogRel Γ k} {p : WShape (k + 1)} {f₀ g₀ : WShapeFun (k + 1)}
    {M₁ M₂ N₁ N₂ A : SExpr}
    (S : LRS.RecAppSync Γ IH m f g J p f₀ g₀)
    (H : LogRel.DefEqRect (LRS J) M₁ M₂ N₁ N₂ A (f₀.app p) (g₀.app p)) :
    LogRel.DefEqRect (LRS IH) M₁ M₂ N₁ N₂ A (f.app m) (g.app m) :=
  S.toRecAppFrame.rect H

/--
info: 'Lean4Lean.SExpr.LRS.RecAppSync.rect' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRS.RecAppSync.rect

/-- Vacuity discipline: the synchronization is inhabited by `refl` at every
`(IH, m, f, g)`. -/
theorem LRS.recAppSync_nonvacuous {Γ : List SExpr} {n : Nat}
    {IH : LogRel Γ n} {m : WShape (n + 1)} {f g : WShapeFun (n + 1)} :
    LRS.RecAppSync Γ IH m f g IH m f g := .refl

/--
info: 'Lean4Lean.SExpr.LRS.recAppSync_nonvacuous' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRS.recAppSync_nonvacuous

/-- Off-diagonal non-vacuity: a synchronization with a genuine `mono` step —
the separation's moving family one level up, so the two ends' rec-app
observations differ (`LRS.RecAppMoving.moves`). -/
theorem LRS.recAppSync_offDiagonal {Γ : List SExpr} {n : Nat}
    {IH : LogRel Γ n} :
    LRS.RecAppSync Γ IH (.bot) (LRS.RecAppMoving.f (n := n + 1))
      (LRS.RecAppMoving.g (n := n + 1))
      IH (.sort true) (LRS.RecAppMoving.f (n := n + 1))
      (LRS.RecAppMoving.g (n := n + 1)) :=
  .mono WShape.bot_le LRS.RecAppMoving.diag_bot LRS.RecAppMoving.diag_sort
    LRS.RecAppMoving.sortTy_sort .refl

/--
info: 'Lean4Lean.SExpr.LRS.recAppSync_offDiagonal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRS.recAppSync_offDiagonal

/-! ### The landed instance factors through the widening

The constructor observation's instance (`LRS.CtorFrame.toRectFrame`) lands
inside the widened frame unchanged, so one transport type serves both the
ctor observation and the rec-app observation. -/

theorem LRS.CtorFrame.toRecAppFrame_indTy {Γ : List SExpr} {n k : Nat}
    {IH : LogRel Γ n} {m : WShape (n + 1)} {J : LogRel Γ k} {p : WShape (k + 1)}
    (F : LRS.CtorFrame Γ IH m J p) (hp : p.HasType .indTy) :
    LRS.RecAppFrame Γ (LRS IH) m .indTy (LRS J) p .indTy :=
  (F.toRectFrame hp).toRecAppFrame

/--
info: 'Lean4Lean.SExpr.LRS.CtorFrame.toRecAppFrame_indTy' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRS.CtorFrame.toRecAppFrame_indTy

/-- And the ctor-observation rectangle transport re-derives through the
widened frame — same statement as the landed `LRS.CtorFrame.rect`. -/
theorem LRS.CtorFrame.rect_via_recAppFrame {Γ : List SExpr} {n k : Nat}
    {IH : LogRel Γ n} {m : WShape (n + 1)} {J : LogRel Γ k} {p : WShape (k + 1)}
    (F : LRS.CtorFrame Γ IH m J p) (hp : p.HasType .indTy)
    {M₁ M₂ N₁ N₂ A : SExpr}
    (H : LogRel.DefEqRect (LRS J) M₁ M₂ N₁ N₂ A p .indTy) :
    LogRel.DefEqRect (LRS IH) M₁ M₂ N₁ N₂ A m .indTy :=
  (F.toRecAppFrame_indTy hp).rect H

/--
info: 'Lean4Lean.SExpr.LRS.CtorFrame.rect_via_recAppFrame' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LRS.CtorFrame.rect_via_recAppFrame
