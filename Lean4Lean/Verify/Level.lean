import Lean4Lean.Theory.VLevel
import Lean4Lean.Level
import Lean4Lean.Verify.Axioms
import Std.Tactic.BVDecide
import Std.Data.TreeMap.Lemmas

namespace Lean

namespace Name
open Std

instance : TransCmp cmp := by
  have eq_swap {a b : Name} : a.cmp b = (b.cmp a).swap := by
    induction a generalizing b with obtain _|⟨b₁,b₂⟩|⟨b₁,b₂⟩ := b <;> simp [cmp]
    | str a₁ a₂ ih | num a₁ a₂ ih =>
      rw [ih]; cases b₁.cmp a₁ <;> simp [← OrientedOrd.eq_swap]
  refine { eq_swap, isLE_trans {a b c} := ?_ }
  have {α} [Ord α] [TransOrd α] {a₁ b₁ c₁} {a₂ b₂ c₂ : α}
      (H1 : (cmp a₁ b₁).isLE → (cmp b₁ c₁).isLE → (cmp a₁ c₁).isLE)
      (H2 : (cmp c₁ a₁).isLE → (cmp a₁ b₁).isLE → (cmp c₁ b₁).isLE)
      (H3 : (cmp b₁ c₁).isLE → (cmp c₁ a₁).isLE → (cmp b₁ a₁).isLE) :
      ((cmp a₁ b₁).then (compare a₂ b₂)).isLE →
      ((cmp b₁ c₁).then (compare b₂ c₂)).isLE →
      ((cmp a₁ c₁).then (compare a₂ c₂)).isLE := by
    simp [Ordering.isLE_then_iff_and]
    intro h1 h2 h3 h4
    refine have := H1 h1 h3; ⟨this, ?_⟩
    obtain eq | eq := Ordering.isLE_iff_eq_lt_or_eq_eq.1 this; · exact .inl eq
    obtain h2 | h2 := h2
    · rw [@eq_swap c₁, eq, @eq_swap _ a₁, h2] at H3; simp [h3] at H3
    obtain h4 | h4 := h4
    · rw [eq_swap, eq, @eq_swap c₁, h4] at H2; simp [h1] at H2
    exact .inr (TransCmp.isLE_trans h2 h4)
  refine (?_ : _ ∧ ((cmp c a).isLE → (cmp a b).isLE → (cmp c b).isLE) ∧
    ((cmp b c).isLE → (cmp c a).isLE → (cmp b a).isLE)).1
  induction a generalizing b c with
    obtain _|⟨b₁,b₂⟩|⟨b₁,b₂⟩ := b <;> simp [cmp] at * <;>
    obtain _|⟨c₁,c₂⟩|⟨c₁,c₂⟩ := c <;> simp [cmp] at *
  | str a₁ a₂ ih | num a₁ a₂ ih =>
    let ⟨h1, h2, h3⟩ := @ih b₁ c₁
    exact ⟨this h1 h2 h3, this h2 h3 h1, this h3 h1 h2⟩

instance : LawfulBEqCmp cmp where
  compare_eq_iff_beq {a b} := by
    simp; refine ⟨?_, fun h => h ▸ ReflCmp.compare_self⟩
    induction a generalizing b with obtain _|⟨b₁,b₂⟩|⟨b₁,b₂⟩ := b <;> simp [cmp]
    | str a₁ a₂ ih | num a₁ a₂ ih =>
      refine ?_ ∘ Ordering.then_eq_eq.1
      simp +contextual; exact fun h _ => ih h

instance : TransCmp quickCmp where
  eq_swap {a b} := by
    simp [quickCmp]
    rw [OrientedOrd.eq_swap]
    cases compare b.hash a.hash <;> simp
    induction a generalizing b with obtain _|⟨b₁,b₂⟩|⟨b₁,b₂⟩ := b <;> simp [quickCmpAux]
    | str a₁ a₂ ih | num a₁ a₂ ih =>
      rw [OrientedOrd.eq_swap]
      cases compare b₂ a₂ <;> simp [ih]
  isLE_trans {a b c} := by
    have {α} [Ord α] [TransOrd α] {a₁ b₁ c₁ : α} {a₂ b₂ c₂}
        (H : (quickCmpAux a₂ b₂).isLE → (quickCmpAux b₂ c₂).isLE → (quickCmpAux a₂ c₂).isLE) :
        ((compare a₁ b₁).then (quickCmpAux a₂ b₂)).isLE →
        ((compare b₁ c₁).then (quickCmpAux b₂ c₂)).isLE →
        ((compare a₁ c₁).then (quickCmpAux a₂ c₂)).isLE := by
      simp [Ordering.isLE_then_iff_and]
      intro h1 h2 h3 h4
      refine ⟨TransCmp.isLE_trans h1 h3, ?_⟩
      refine h2.elim (fun h2 => .inl <| TransCmp.lt_of_lt_of_isLE h2 h3) fun h2 => ?_
      refine h4.elim (fun h4 => .inl <| TransCmp.lt_of_isLE_of_lt h1 h4) fun h4 => .inr (H h2 h4)
    apply this
    induction a generalizing b c with
      obtain _|⟨b₁,b₂⟩|⟨b₁,b₂⟩ := b <;> simp [quickCmpAux] at * <;>
      obtain _|⟨c₁,c₂⟩|⟨c₁,c₂⟩ := c <;> simp [quickCmpAux] at *
    | str a₁ a₂ ih | num a₁ a₂ ih => apply this ih

instance : LawfulBEqCmp quickCmp where
  compare_eq_iff_beq {a b} := by
    simp; refine ⟨fun h => ?_, fun h => h ▸ ReflCmp.compare_self⟩
    replace h := (Ordering.then_eq_eq.1 h).2; revert h
    induction a generalizing b with obtain _|⟨b₁,b₂⟩|⟨b₁,b₂⟩ := b <;> simp [quickCmpAux]
    | str a₁ a₂ ih | num a₁ a₂ ih =>
      refine ?_ ∘ Ordering.then_eq_eq.1
      simp +contextual; exact fun _ => ih

end Name

namespace Level
open Lean4Lean

attribute [simp] mkLevelSucc mkLevelMax mkLevelIMax updateSucc! updateMax! updateIMax!

-- variable (ls : List Name) in
-- def _root_.Lean4Lean.VLevel.toLevel : VLevel → Level
--   | .zero => .zero
--   | .succ l => .succ l.toLevel
--   | .max l₁ l₂ => .max l₁.toLevel l₂.toLevel
--   | .imax l₁ l₂ => .imax l₁.toLevel l₂.toLevel
--   | .param n => match ls.get? n with
--     | some l => .param l
--     | none => .zero

-- theorem toLevel_inj {ls : List Name} (d : ls.Nodup)
--     {l₁ l₂ : VLevel} (eq : l₁.toLevel ls = l₂.toLevel ls) : l₁ = l₂ := sorry

@[simp] def getOffset' : Level → Nat
  | succ u => getOffset' u + 1
  | _      => 0

@[simp] theorem getOffset_eq (u : Level) : u.getOffset = u.getOffset' := go _ 0 where
  go (u : Level) (i) : u.getOffsetAux i = u.getOffset' + i := by
    unfold getOffsetAux getOffset'; split <;> simp
    rw [go]; simp [Nat.add_right_comm, Nat.add_assoc]

theorem mkData_depth (H : d < 2 ^ 24) : (mkData h d hmv hp).depth.toNat = d := by
  rw [mkData_eq, mkData', if_neg (Nat.not_lt.2 (Nat.le_sub_one_of_lt H)), Data.depth]
  have : d.toUInt64.toUInt32.toNat = d := by simp; omega
  refine .trans ?_ this; congr 2
  rw [← UInt64.toBitVec_inj]
  have : d.toUInt64.toNat = d := by simp; omega
  have : d.toUInt64.toBitVec ≤ 0xffffff#64 := (this ▸ Nat.le_sub_one_of_lt H :)
  have : h.toUInt32.toUInt64.toBitVec ≤ 0xffffffff#64 := Nat.le_of_lt_succ h.toUInt32.1.1.2
  have hb : ∀ (b : Bool), b.toUInt64.toBitVec ≤ 1#64 := by decide
  have := hb hmv; have := hb hp
  change (
    h.toUInt32.toUInt64.toBitVec +
    hmv.toUInt64.toBitVec <<< 32#64 +
    hp.toUInt64.toBitVec <<< 33#64 +
    d.toUInt64.toBitVec <<< 40#64) >>> 40#64 = d.toUInt64.toBitVec
  bv_decide

theorem mkData_hasParam (H : d < 2 ^ 24) : (mkData h d hmv hp).hasParam = hp := by
  rw [mkData_eq, mkData', if_neg (Nat.not_lt.2 (Nat.le_sub_one_of_lt H))]
  simp [Data.hasParam, (· == ·), ← UInt64.toBitVec_inj]
  have : h.toUInt32.toUInt64.toBitVec ≤ 0xffffffff#64 := Nat.le_of_lt_succ h.toUInt32.1.1.2
  have hb : ∀ (b : Bool), b.toUInt64.toBitVec ≤ 1#64 := by decide
  have := hb hmv; have := hb hp
  let L := ((
    h.toUInt32.toUInt64.toBitVec +
    hmv.toUInt64.toBitVec <<< 32#64 +
    hp.toUInt64.toBitVec <<< 33#64 +
    d.toUInt64.toBitVec <<< 40#64) >>> 33#64) &&& 1#64
  change decide (L = 1#64) = hp
  rw [show L = hp.toUInt64.toBitVec by bv_decide]
  cases hp <;> decide

theorem mkData_hasMVar (H : d < 2 ^ 24) : (mkData h d hmv hp).hasMVar = hmv := by
  rw [mkData_eq, mkData', if_neg (Nat.not_lt.2 (Nat.le_sub_one_of_lt H))]
  simp [Data.hasMVar, (· == ·), ← UInt64.toBitVec_inj]
  have : h.toUInt32.toUInt64.toBitVec ≤ 0xffffffff#64 := Nat.le_of_lt_succ h.toUInt32.1.1.2
  have hb : ∀ (b : Bool), b.toUInt64.toBitVec ≤ 1#64 := by decide
  have := hb hmv; have := hb hp
  let L := ((
    h.toUInt32.toUInt64.toBitVec +
    hmv.toUInt64.toBitVec <<< 32#64 +
    hp.toUInt64.toBitVec <<< 33#64 +
    d.toUInt64.toBitVec <<< 40#64) >>> 32#64) &&& 1#64
  change decide (L = 1#64) = hmv
  rw [show L = hmv.toUInt64.toBitVec by bv_decide]
  cases hmv <;> decide

theorem ofLevel_of_not_hasParam (Us) {l : Level}
    (hl : l.hasParam' = false) (hmv : l.hasMVar' = false) :
    ∃ u', VLevel.ofLevel Us l = some u' := by
  induction l <;> simp_all [hasParam', hasMVar', VLevel.ofLevel, exists_comm]

def getUndefParam.F (ps : List Name) (l : Level) : StateT (Option Name) Id Bool := do
  if !l.hasParam || (← get).isSome then
    return false
  if let .param n := l then
    if n ∉ ps then
      set (some n)
  return true

theorem getUndefParam_none {l : Level} (hmv : l.hasMVar' = false) :
    l.getUndefParam Us = none → ∃ u', VLevel.ofLevel Us l = some u' := by
  suffices ∀ s, ((l.forEach (getUndefParam.F Us)).run s).run.snd = none → s = none ∧ _ from
    (this _ · |>.2)
  have {l} (hmv : l.hasMVar' = false)
      {g} (H : ∀ {s'}, (g.run s').run.snd = none → s' = none ∧
        (((getUndefParam.F Us l).run none).run = (true, none) →
          ∃ u', VLevel.ofLevel Us l = some u')) (s) :
      ((do if (!(← getUndefParam.F Us l)) = true then pure PUnit.unit else g)
        |>.run s).run.snd = none →
      s = none ∧ ∃ u', VLevel.ofLevel Us l = some u' := by
    simp; split <;> rename_i h
    · simp; revert h
      simp [getUndefParam.F]; split <;> [simp; split <;> [split <;> simp; simp]]
      rintro rfl; simp at *
      exact ofLevel_of_not_hasParam Us ‹_› hmv
    · refine fun h' => let ⟨h1, h2⟩ := H h'; have := ?_; ⟨this, h2 ?_⟩
      · revert h h1
        simp [getUndefParam.F]; split <;> [simp; split <;> [split <;> simp; simp]]
      · revert h h1; subst s
        cases (getUndefParam.F Us l).run none; simp; rintro rfl rfl; rfl
  have lt {n a} : n + 1 < a → n < a := by omega
  induction l with (
    refine this hmv fun h => ?_; clear this
    simp [hasMVar', VLevel.ofLevel, *] at *)
  | succ _ ih =>
    have ⟨h, _, h1⟩ := ih hmv _ h
    exact ⟨h, fun _ => ⟨_, _, h1, rfl⟩⟩
  | max _ _ ih1 ih2 | imax _ _ ih1 ih2 =>
    have ⟨h, _, h2⟩ := ih2 hmv.2 _ h
    have ⟨h, _, h1⟩ := ih1 hmv.1 _ h
    exact ⟨h, fun _ => ⟨_, _, h1, _, h2, rfl⟩⟩
  | param =>
    simp [getUndefParam.F, hasParam', List.idxOf_lt_length_iff, *]
    split <;> simp [*]
  | _ => simp [*]

variable (s : Name → Level) in
def substParams' (red : Bool) : Level → Level
  | .zero       => .zero
  | .succ v     => .succ (substParams' (v.hasParam ∧ red) v)
  | .max v₁ v₂  =>
    let red := (v₁.hasParam ∨ v₂.hasParam) ∧ red
    (if red then mkLevelMax' else .max) (substParams' red v₁) (substParams' red v₂)
  | .imax v₁ v₂ =>
    let red := (v₁.hasParam ∨ v₂.hasParam) ∧ red
    (if red then mkLevelIMax' else .imax) (substParams' red v₁) (substParams' red v₂)
  | .param n => s n
  | u => u

theorem substParams_eq_self {u : Level} (h : u.hasParam' = false) :
    substParams' s red u = u := by
  induction u generalizing red <;> simp_all [substParams', hasParam']

open private substParams.go from Lean.Level in
@[simp] theorem substParams_eq (u : Level) (s : Name → Option Level) :
    substParams u s = substParams' (fun x => (s x).getD (.param x)) true u := by
  unfold substParams
  induction u <;> simp [substParams.go, substParams', hasParam', ← Bool.or_eq_true] <;>
    split <;> simp [*, substParams_eq_self] <;> simp_all [substParams_eq_self]

theorem substParams_id {u : Level} :
    substParams' .param false u = u := by induction u <;> simp_all [substParams']

local notation "max'" => Max.max

namespace Normalize

attribute [local instance] Lean.Level.Normalize.instOrdName_lean4Lean

local instance : Std.TransCmp (α := Name) compare := inferInstanceAs (Std.TransCmp Name.cmp)
local instance : Std.LawfulBEqCmp (α := List Name) compare :=
  inferInstanceAs (Std.LawfulBEqCmp (List.compareLex Name.cmp))

instance : LawfulBEq VarNode where
  rfl {a} := by cases a <;> simp! +instances [instBEqVarNode]
  eq_of_beq {a b} := by cases a <;> cases b <;> simp! +instances [instBEqVarNode]

@[reducible] local instance : Membership (List Name) NormLevel :=
  inferInstanceAs (Membership _ (Std.TreeMap _ _ compare))

@[reducible] local instance : GetElem? NormLevel (List Name) Node (fun m a => a ∈ m) :=
  inferInstanceAs (GetElem? (Std.TreeMap _ _ compare) ..)

section
variable (ls : List Name) (ρ : List Nat) in
def evalParam (x : Name) : Nat :=
let i := ls.idxOf x; if i < ls.length then ρ[i]?.getD 0 else 0

theorem evalParam_eq (hv : ls.idxOf x < ls.length) :
    evalParam ls ρ x = ρ[List.idxOf x ls]?.getD 0 := if_pos hv

variable (ls : List Name) (ρ : List Nat) in
def VarNode.eval (l : VarNode) : Nat := evalParam ls ρ l.var + l.offset

variable (ls : List Name) (ρ : List Nat) in
def Node.eval (l : Node) : Nat :=
  l.var.foldl (init := l.const) fun n v => max' n (v.eval ls ρ)

theorem Node.eval_le : eval ls ρ l ≤ n ↔
    l.const ≤ n ∧ ∀ v ∈ l.var, v.eval ls ρ ≤ n := by
  simp [eval, ← List.foldr_reverse]; simp only [← l.var.mem_reverse]
  induction l.var.reverse with simp | cons a l
  simp [Nat.max_le, and_comm, and_left_comm, *]

variable (ls : List Name) (ρ : List Nat) in
def allNZ (path : List Name) : Bool := path.all (0 < evalParam ls ρ ·)

theorem allNZ_cons : allNZ ls ρ (a :: path) ↔
    0 < evalParam ls ρ a ∧ allNZ ls ρ path := by simp [allNZ]

theorem allNZ_mono (H : ∀ x ∈ path, x ∈ path') : allNZ ls ρ path' → allNZ ls ρ path := by
  simp [allNZ]; grind

variable (ls : List Name) (ρ : List Nat) in
def evalPath (path : List Name) (n : Nat) : Nat :=
  if allNZ ls ρ path then n else 0

theorem evalPath_cons : evalPath ls ρ (a :: path) n =
    evalPath ls ρ path (if 0 < evalParam ls ρ a then n else 0) := by
  by_cases h : 0 < evalParam ls ρ a <;> simp [evalPath, allNZ_cons, h]

theorem evalPath_max :
    evalPath ls ρ path (max' m n) = max' (evalPath ls ρ path m) (evalPath ls ρ path n) := by
  simp [evalPath]; split <;> simp

theorem evalPath_mono (h : n ≤ m) :
    evalPath ls ρ path n ≤ evalPath ls ρ path m := by
  simp [evalPath]; split <;> simp [*]

theorem evalPath_le : evalPath ls ρ path n ≤ m ↔ (allNZ ls ρ path → n ≤ m) := by
  simp [evalPath]; split <;> simp [*]

variable (ls : List Name) (ρ : List Nat) in
inductive EvalPaths : List Name → Nat → Prop
  | nil : EvalPaths [] n
  | insert : orderedInsert Name.cmp a path = some path' →
    evalPath ls ρ path (evalParam ls ρ a) ≤ n → EvalPaths path n → EvalPaths path' n

theorem EvalPaths.mono (h : n ≤ n') : EvalPaths ls ρ path n → EvalPaths ls ρ path n'
  | .nil => .nil
  | .insert h1 h2 h3 => .insert h1 (Nat.le_trans h2 h) (h3.mono h)

theorem EvalPaths.max : EvalPaths ls ρ path n → EvalPaths ls ρ path (max' n m) :=
  .mono (Nat.le_max_left ..)

variable (ls : List Name) (ρ : List Nat) in
def NormLevel.eval (l : NormLevel) : Nat :=
  l.foldl (init := 0) fun n a b => max' n (evalPath ls ρ a (b.eval ls ρ))

theorem NormLevel.eval_le : eval ls ρ l ≤ n ↔
    ∀ a b, l.get? a = some b → evalPath ls ρ a (b.eval ls ρ) ≤ n := by
  simp [eval, Std.TreeMap.foldl_eq_foldl_toList, ← List.foldr_reverse]
  simp only [← Std.TreeMap.mem_toList_iff_getElem?_eq_some, ← l.toList.mem_reverse]
  induction l.toList.reverse with simp | cons a l; let (a, b) := a
  simp [or_imp, forall_and, Nat.max_le, and_comm, *]

end

theorem NormLevel.addVar_contains (H : acc.contains x) : (addVar v k path acc).contains x := by
  simp_all [addVar, Std.TreeMap.mem_modify]

theorem NormLevel.addNode_contains (H : acc.contains x) : (addNode v k path acc).contains x := by
  simp [addNode, Std.TreeMap.mem_alter] at *; split <;> simp [*]

theorem NormLevel.addNode_contains_self : (addNode v k path acc).contains path := by
  simp [addNode]; split <;> simp

theorem NormLevel.addConst_contains (H : acc.contains x) : (addConst k path acc).contains x := by
  simp [addConst] at *; split <;> simp [H, Std.TreeMap.mem_modify]

theorem normalizeAux_contains (H : acc.contains x) : (normalizeAux u path k acc).contains x := by
  unfold normalizeAux; split
  · exact NormLevel.addConst_contains H
  · exact NormLevel.addConst_contains H
  · exact normalizeAux_contains H
  · exact normalizeAux_contains (normalizeAux_contains H)
  · exact normalizeAux_contains (normalizeAux_contains H)
  · exact normalizeAux_contains (normalizeAux_contains H)
  · exact normalizeAux_contains (normalizeAux_contains H)
  · split <;> [skip; (dsimp; split)]
    · exact normalizeAux_contains (NormLevel.addNode_contains (NormLevel.addConst_contains H))
    · exact normalizeAux_contains H
    · exact normalizeAux_contains (NormLevel.addVar_contains H)
  · exact H
  · exact H
  · split <;> [skip; split]
    · exact NormLevel.addNode_contains (NormLevel.addConst_contains H)
    · exact H
    · exact NormLevel.addVar_contains H

theorem imax_max : Nat.imax a (max' b c) = max' (Nat.imax a b) (Nat.imax a c) := by
  simp [Nat.imax]; symm; split <;> simp [*]; split <;> simp [*, Nat.max_eq_max]
  rw [Nat.max_left_comm b, ← Nat.max_assoc, Nat.max_self]

theorem imax_imax : Nat.imax a (Nat.imax b c) = max' (Nat.imax a c) (Nat.imax b c) := by
  simp [Nat.imax]; by_cases h : c = 0 <;> simp [*, Nat.max_eq_max]
  rw [Nat.max_left_comm c, Nat.max_self]

theorem mem_orderedInsert [BEq α] [LawfulBEq α] [Std.LawfulBEqCmp (α := α) cmp] :
    b ∈ (orderedInsert cmp a ls).getD ls ↔ b = a ∨ b ∈ ls := by
  induction ls <;> simp [orderedInsert]; split <;> simp_all [or_left_comm]

theorem allNZ_orderedInsert :
    allNZ ls ρ ((orderedInsert Name.cmp a path).getD path) = allNZ ls ρ (a :: path) := by
  rw [Bool.eq_iff_iff]; simp [allNZ, mem_orderedInsert]

theorem evalPath_orderedInsert :
    evalPath ls ρ ((orderedInsert Name.cmp a path).getD path) = evalPath ls ρ (a :: path) := by
  ext n; simp [evalPath, allNZ_orderedInsert]

theorem EvalPaths.of_mem (hm : v ∈ path) (H : EvalPaths ls ρ path n) :
    ∃ path₁ path₂, (∀ x ∈ path₁, x ∈ path) ∧
      orderedInsert Name.cmp v path₁ = some path₂ ∧
      evalPath ls ρ path₁ (evalParam ls ρ v) ≤ n ∧
      EvalPaths ls ρ path₁ n := by
  induction H with | nil => cases hm | insert h1 h2 h3 ih
  obtain rfl | hm := (h1 ▸ mem_orderedInsert).1 hm
  · exact ⟨_, _, fun _ h => (h1 ▸ mem_orderedInsert).2 (.inr h), h1, h2, h3⟩
  · let ⟨_, _, a1, a2, a3, a4⟩ := ih hm
    exact ⟨_, _, fun _ h => (h1 ▸ mem_orderedInsert).2 (.inr (a1 _ h)), a2, a3, a4⟩

theorem ext_le {n m : Nat} (H : ∀ x, n ≤ x ↔ m ≤ x) : n = m :=
  Nat.le_antisymm ((H _).2 (Nat.le_refl _)) ((H _).1 (Nat.le_refl _))

theorem le_ext_le {n m : Nat} (H : ∀ x, n ≤ x → m ≤ x) : m ≤ n := H _ (Nat.le_refl _)

theorem NormLevel.addConst_eval
    (H : acc.contains path) (le : EvalPaths ls ρ path (acc.eval ls ρ)) :
    (addConst k path acc).eval ls ρ = max' (acc.eval ls ρ) (evalPath ls ρ path k) := by
  simp [addConst]; split <;> rename_i h
  · obtain rfl | ⟨rfl, _⟩ := h
    · simp [evalPath]
    · let a::path := path; let .insert h1 le h3 := le
      have := h1 ▸ evalPath_orderedInsert (ls := ls) (ρ := ρ); simp at this
      rw [this, Nat.max_eq_left]; simp [evalPath]; split <;> [rename_i h; simp]
      let ⟨h1, h2⟩ := allNZ_cons.1 h; exact Nat.le_trans h1 (evalPath_le.1 le h2)
  · refine ext_le fun x => ?_
    rw [← Std.TreeMap.isSome_getElem?_eq_contains, Option.isSome_iff_exists] at H; let ⟨v, H⟩ := H
    simp [eval_le, Nat.max_le, Std.TreeMap.getElem?_modify, evalPath_le, Node.eval_le, H]
    refine ⟨fun h1 => ?_, fun ⟨h1, h2⟩ a b => ?_⟩
    · have := h1 path; simp [Nat.max_le] at this
      refine ⟨fun a b h3 h4 => ?_, fun h => (this h).1.1⟩
      specialize h1 a; split at h1
      · subst a; cases H.symm.trans h3; exact ⟨(this h4).1.2, (this h4).2⟩
      · exact h1 _ h3 h4
    · split
      · subst a; rintro ⟨⟩ nz; simp [Nat.max_le, nz, h2]; exact h1 _ _ H nz
      · exact h1 _ _

theorem VarNode.addVar_le : (∀ vn ∈ VarNode.addVar v k l, vn.eval ls ρ ≤ x) ↔
    evalParam ls ρ v + k ≤ x ∧ (∀ vn ∈ l, vn.eval ls ρ ≤ x) := by
  simp [eval]; induction l with simp [VarNode.addVar] | cons vn l ih; split <;> simp [*]
  · simp at *; subst v
    rw [← and_assoc, ← Nat.max_le, Nat.add_max_add_left, Nat.max_comm, Nat.max_eq_max]
  · rw [and_left_comm]

theorem NormLevel.addNode_eval : (addNode v k path acc).eval ls ρ =
    max' (acc.eval ls ρ) (evalPath ls ρ path (evalParam ls ρ v + k)) := by
  refine ext_le fun x => ?_
  simp [addNode, eval_le, Std.TreeMap.getElem?_alter, evalPath_le, Node.eval_le, Nat.max_le]
  refine ⟨fun H => ⟨fun a b h nz => ?_, fun nz => ?_⟩, fun ⟨H1, H2⟩ a b h nz => ?_⟩
  · have := H a; split at this
    · subst a; simp_all [VarNode.addVar_le]
    · exact this _ h nz
  · have := H path; simp at this; split at this <;> specialize this _ rfl nz
    · simp_all [VarNode.eval]
    · simp_all [VarNode.addVar_le]
  · split at h
    · subst a; split at h <;> cases h
      · simp_all [VarNode.eval]
      · simp_all [VarNode.addVar_le]; grind
    · grind

theorem NormLevel.addVar_eval (H : acc.contains path) : (addVar v k path acc).eval ls ρ =
    max' (acc.eval ls ρ) (evalPath ls ρ path (evalParam ls ρ v + k)) := by
  refine ext_le fun x => ?_
  rw [← Std.TreeMap.isSome_getElem?_eq_contains, Option.isSome_iff_exists] at H; let ⟨v, H⟩ := H
  simp [addVar, eval_le, Nat.max_le, Std.TreeMap.getElem?_modify, evalPath_le, Node.eval_le, H]
  refine ⟨fun H => ⟨fun a b h nz => ?_, fun nz => ?_⟩, fun ⟨H1, H2⟩ a b h nz => ?_⟩
  · have := H a; split at this
    · subst a; simp_all [VarNode.addVar_le]
    · exact this _ h nz
  · have := H path; simp at this; specialize this nz; simp_all [VarNode.addVar_le]
  · split at h
    · subst a; cases h; simp_all [VarNode.addVar_le]; grind
    · grind

theorem normalizeAux_eval (hu : VLevel.ofLevel ls u = some u')
    (H : acc.contains path) (le : EvalPaths ls ρ path (acc.eval ls ρ)) :
    (normalizeAux u path k acc).eval ls ρ =
    max' (acc.eval ls ρ) (evalPath ls ρ path (u'.eval ρ + k)) := by
  unfold normalizeAux; split
  · cases hu; simp [NormLevel.addConst_eval H le, VLevel.eval]
  · simp [VLevel.ofLevel] at hu; obtain ⟨_, hu, rfl⟩ := hu
    simp [VLevel.eval, Nat.imax, NormLevel.addConst_eval H le]
  · simp [VLevel.ofLevel] at hu; obtain ⟨_, hu, rfl⟩ := hu
    rw [normalizeAux_eval hu H le, Nat.add_succ, ← Nat.succ_add]; rfl
  · simp [VLevel.ofLevel] at hu; obtain ⟨_, hu, _, hv, rfl⟩ := hu
    rw [normalizeAux_eval hv (normalizeAux_contains H)] <;> rw [normalizeAux_eval hu H le]
    · rw [Nat.max_assoc, ← evalPath_max, Nat.add_max_add_right]; rfl
    · exact le.max
  · simp [VLevel.ofLevel] at hu; obtain ⟨_, hu, _, ⟨_, hv, rfl⟩, rfl⟩ := hu
    rw [normalizeAux_eval hv (normalizeAux_contains H)] <;> rw [normalizeAux_eval hu H le]
    · rw [Nat.max_assoc, Nat.add_succ, ← Nat.succ_add, ← evalPath_max, Nat.add_max_add_right]; rfl
    · exact le.max
  · rename_i u v w
    simp [VLevel.ofLevel] at hu; obtain ⟨_, hu, _, ⟨_, hv, _, hw, rfl⟩, rfl⟩ := hu
    rw [normalizeAux_eval
        (by simpa [VLevel.ofLevel] using ⟨_, hu, _, hw, rfl⟩) (normalizeAux_contains H)] <;>
      rw [normalizeAux_eval (by simpa [VLevel.ofLevel] using ⟨_, hu, _, hv, rfl⟩) H le]
    · rw [Nat.max_assoc, ← evalPath_max, Nat.add_max_add_right]; simp [VLevel.eval, imax_max]
    · exact le.max
  · rename_i u v w
    simp [VLevel.ofLevel] at hu; obtain ⟨_, hu, _, ⟨_, hv, _, hw, rfl⟩, rfl⟩ := hu
    rw [normalizeAux_eval (by simpa [VLevel.ofLevel] using ⟨_, hv, _, hw, rfl⟩)
        (normalizeAux_contains H)] <;>
      rw [normalizeAux_eval (by simpa [VLevel.ofLevel] using ⟨_, hu, _, hw, rfl⟩) H le]
    · rw [Nat.max_assoc, ← evalPath_max, Nat.add_max_add_right]; simp [VLevel.eval, imax_imax]
    · exact le.max
  · rename_i u v
    simp [VLevel.ofLevel] at hu; obtain ⟨_, hu, _, ⟨hv, rfl⟩, rfl⟩ := hu
    have := @evalPath_orderedInsert ls ρ v path
    split <;> rename_i h <;> simp [h] at this
    · rw [normalizeAux_eval hu NormLevel.addNode_contains_self] <;>
        rw [NormLevel.addNode_eval, NormLevel.addConst_eval H le, Nat.max_assoc]
      · rw [Nat.max_assoc, ← evalPath_max, this, evalPath_cons, ← evalPath_max,
          Nat.add_max_add_right]; congr 2
        simp [VLevel.eval, ← evalParam_eq hv, Nat.imax]
        cases evalParam .. <;> simp [Nat.max_eq_max, Nat.max_comm]
      · refine .insert h (Nat.le_trans ?_ (Nat.le_max_right ..)) le.max
        rw [this, evalPath_cons, ← evalPath_max]; apply evalPath_mono; grind
    · dsimp; split
      · rw [normalizeAux_eval hu H le]
        simp [evalPath]; split <;> [rename_i nz; simp]
        have hm := (h ▸ mem_orderedInsert).2 (.inl rfl)
        have ⟨p1, p2, a1, a2, a3, a4⟩ := le.of_mem hm
        have := evalPath_le.1 a3 (allNZ_mono a1 nz)
        simp [allNZ] at nz; specialize nz _ hm
        simp [VLevel.eval, Nat.imax]; simp [← evalParam_eq hv]
        revert this nz; cases evalParam .. <;> simp
        rw [Nat.max_eq_max, Nat.max_comm (a := VLevel.eval ..), ← Nat.add_max_add_right, ← Nat.max_assoc]
        intro h; rw [Nat.max_eq_left (b := _+1+k)]; omega
      · rw [normalizeAux_eval hu (NormLevel.addVar_contains H)] <;> rw [NormLevel.addVar_eval H]
        · rw [Nat.max_assoc, ← evalPath_max, Nat.add_max_add_right, this,
            evalPath_cons, evalPath_cons]; congr 2; split <;> simp [VLevel.eval, Nat.imax]
          rename_i h; revert h; simp [← evalParam_eq hv]
          cases evalParam .. <;> simp [Nat.max_eq_max, Nat.max_comm]
        · exact le.max
  · cases hu
  · simp [VLevel.ofLevel] at hu
  · rename_i v; simp [VLevel.ofLevel] at hu; obtain ⟨hv, rfl⟩ := hu
    have := @evalPath_orderedInsert ls ρ v path
    split <;> rename_i h <;> simp [h] at this
    · rw [NormLevel.addNode_eval, NormLevel.addConst_eval H le, Nat.max_assoc,
        this, evalPath_cons, ← evalPath_max]
      simp [VLevel.eval, ← evalParam_eq hv]; congr 2; split <;> simp; omega
    · split
      · simp [evalPath]; split <;> [rename_i nz; simp]
        have hm := (h ▸ mem_orderedInsert).2 (.inl rfl)
        have ⟨p1, p2, a1, a2, a3, a4⟩ := le.of_mem hm
        have := evalPath_le.1 a3 (allNZ_mono a1 nz)
        simp [allNZ] at nz; specialize nz _ hm
        simp [VLevel.eval, ← evalParam_eq hv]
        revert this nz; cases evalParam .. <;> simp; omega
      · rw [NormLevel.addVar_eval H, this, evalPath_cons, evalPath_cons]
        congr 2; split <;> simp [VLevel.eval, ← evalParam_eq hv]

private theorem subset_subset {xs ys : List Name} (h : subset Name.cmp xs ys) :
    xs ⊆ ys := by
  induction ys generalizing xs with
  | nil => cases xs <;> simp_all [subset]
  | cons y ys ih =>
    cases xs with
    | nil => simp
    | cons x xs =>
      simp only [subset] at h
      split at h
      · contradiction
      · rename_i hxy
        have : x = y := by simpa using hxy
        subst y
        exact List.cons_subset_cons _ (ih h)
      · exact List.subset_cons_of_subset _ (ih h)

private theorem leVars_dominated {xs ys : List VarNode} (h : leVars xs ys)
    (hv : v ∈ xs) : ∃ w ∈ ys, v.var = w.var ∧ v.offset ≤ w.offset := by
  induction xs, ys using leVars.induct with
  | case1 ys => cases hv
  | case2 xs => simp [leVars] at h
  | case3 x xs y ys hcmp => simp [leVars, hcmp] at h
  | case4 x xs y ys hcmp ih =>
    simp only [leVars, hcmp, Bool.and_eq_true] at h
    have hvar : x.var = y.var := by simpa using hcmp
    rcases List.mem_cons.mp hv with rfl | hv
    · exact ⟨y, by simp, hvar, of_decide_eq_true h.1⟩
    · rcases ih h.2 hv with ⟨w, hw, hvar, hoff⟩
      exact ⟨w, by simp [hw], hvar, hoff⟩
  | case5 x xs y ys hcmp ih =>
    simp only [leVars, hcmp] at h
    rcases ih h hv with ⟨w, hw, hvar, hoff⟩
    exact ⟨w, by simp [hw], hvar, hoff⟩

private theorem subsumeVars_subset {xs ys : List VarNode} :
    subsumeVars xs ys ⊆ xs := by
  induction xs, ys using subsumeVars.induct with
  | case1 ys => simp [subsumeVars]
  | case2 xs h => simp [subsumeVars]
  | case3 x xs y ys hcmp ih => simpa [subsumeVars, hcmp] using List.cons_subset_cons x ih
  | case4 x xs y ys hcmp hoff ih =>
    simpa [subsumeVars, hcmp, hoff] using
      List.Subset.trans ih (List.subset_cons_self x xs)
  | case5 x xs y ys hcmp hoff ih =>
    simpa [subsumeVars, hcmp, hoff] using List.cons_subset_cons x ih
  | case6 x xs y ys hcmp ih => simpa [subsumeVars, hcmp] using ih

private theorem subsumeVars_dominated {xs ys : List VarNode} (hz : z ∈ xs) :
    z ∈ subsumeVars xs ys ∨
      ∃ y ∈ ys, z.var = y.var ∧ z.offset ≤ y.offset := by
  induction xs, ys using subsumeVars.induct with
  | case1 ys => cases hz
  | case2 xs h => exact .inl (by simpa [subsumeVars])
  | case3 x xs y ys hcmp ih =>
    rcases List.mem_cons.mp hz with hzx | hz
    · subst x; exact .inl (by simp [subsumeVars, hcmp])
    · exact (ih hz).imp
        (by simp only [subsumeVars, hcmp, List.mem_cons]; exact .inr)
        (by rintro ⟨w, hw, hvar, hoff⟩; exact ⟨w, by simp [hw], hvar, hoff⟩)
  | case4 x xs y ys hcmp hoff ih =>
    have hvar : x.var = y.var := by simpa using hcmp
    rcases List.mem_cons.mp hz with hzx | hz
    · subst x; exact .inr ⟨y, by simp, hvar, hoff⟩
    · rcases ih hz with hout | ⟨w, hw, hvar, hoff⟩
      · exact .inl (by simpa [subsumeVars, hcmp, hoff] using hout)
      · exact .inr ⟨w, by simp [hw], hvar, hoff⟩
  | case5 x xs y ys hcmp hoff ih =>
    rcases List.mem_cons.mp hz with hzx | hz
    · subst x; exact .inl (by simp [subsumeVars, hcmp, hoff])
    · rcases ih hz with hout | ⟨w, hw, hvar, hoff'⟩
      · exact .inl (by
          simp only [subsumeVars, hcmp, if_neg hoff, List.mem_cons]
          exact .inr hout)
      · exact .inr ⟨w, by simp [hw], hvar, hoff'⟩
  | case6 x xs y ys hcmp ih =>
    exact (ih hz).imp
      (by simp [subsumeVars, hcmp])
      (by rintro ⟨w, hw, hvar, hoff⟩; exact ⟨w, by simp [hw], hvar, hoff⟩)

private theorem eval_insert_le {m : NormLevel} {p : List Name} {n : Node}
    (h : evalPath ls ρ p (n.eval ls ρ) ≤ m.eval ls ρ) :
    NormLevel.eval ls ρ (m.insert p n) ≤ m.eval ls ρ := by
  rw [NormLevel.eval_le]
  intro a b hab
  simp only [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert] at hab
  split at hab
  · rename_i heq
    have : p = a := by simpa using heq
    subst a
    cases hab
    exact h
  · exact NormLevel.eval_le.1 (Nat.le_refl _) _ _ hab

private theorem eval_le_insert {m : NormLevel} {p : List Name} {old new : Node}
    (hget : m.get? p = some old)
    (h : evalPath ls ρ p (old.eval ls ρ) ≤ NormLevel.eval ls ρ (m.insert p new)) :
    m.eval ls ρ ≤ NormLevel.eval ls ρ (m.insert p new) := by
  rw [NormLevel.eval_le]
  intro a b hab
  by_cases hpa : p = a
  · subst a
    cases hget.symm.trans hab
    exact h
  · apply NormLevel.eval_le.1 (Nat.le_refl _) a b
    simp only [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert]
    have hcmp : compare p a ≠ .eq := by simpa using hpa
    rw [if_neg hcmp]
    exact hab

private theorem eval_insert_eq {m : NormLevel} {p : List Name} {old new : Node}
    (hget : m.get? p = some old)
    (hnew : evalPath ls ρ p (new.eval ls ρ) ≤ evalPath ls ρ p (old.eval ls ρ))
    (hold : evalPath ls ρ p (old.eval ls ρ) ≤ NormLevel.eval ls ρ (m.insert p new)) :
    NormLevel.eval ls ρ (m.insert p new) = m.eval ls ρ := by
  apply Nat.le_antisymm
  · apply eval_insert_le
    exact Nat.le_trans hnew (NormLevel.eval_le.1 (Nat.le_refl _) p old hget)
  · exact eval_le_insert hget hold

private theorem node_eval_mono {a b : Node} (hc : a.const ≤ b.const)
    (hv : a.var ⊆ b.var) : a.eval ls ρ ≤ b.eval ls ρ := by
  apply Node.eval_le.2
  refine ⟨Nat.le_trans hc (Node.eval_le.1 (Nat.le_refl _) |>.1), ?_⟩
  intro v hv'
  exact Node.eval_le.1 (Nat.le_refl _) |>.2 v (hv hv')

private theorem eval_replace_eq {m : NormLevel} {p : List Name} {old new : Node}
    (hnew : evalPath ls ρ p (new.eval ls ρ) ≤ evalPath ls ρ p (old.eval ls ρ))
    (hold : evalPath ls ρ p (old.eval ls ρ) ≤ NormLevel.eval ls ρ (m.insert p new)) :
    NormLevel.eval ls ρ (m.insert p new) = NormLevel.eval ls ρ (m.insert p old) := by
  apply Nat.le_antisymm
  · rw [NormLevel.eval_le]
    intro a b hab
    simp only [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert] at hab
    split at hab
    · rename_i heq
      have : p = a := by simpa using heq
      subst a
      cases hab
      exact Nat.le_trans hnew
        (NormLevel.eval_le.1 (Nat.le_refl _) p old (by
          simpa only [Std.TreeMap.get?_eq_getElem?] using
            (Std.TreeMap.getElem?_insert_self (t := m) (k := p) (v := old))))
    · rename_i hneq
      apply NormLevel.eval_le.1 (Nat.le_refl _) a b
      simp only [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert]
      rw [if_neg hneq]
      exact hab
  · rw [NormLevel.eval_le]
    intro a b hab
    simp only [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert] at hab
    split at hab
    · rename_i heq
      have : p = a := by simpa using heq
      subst a
      cases hab
      exact hold
    · rename_i hneq
      apply NormLevel.eval_le.1 (Nat.le_refl _) a b
      simp only [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert]
      rw [if_neg hneq]
      exact hab

private theorem subsumptionStep_eval_le (n₁ n₂ : Node) (p₁ p₂ : List Name) :
    (n₁.subsumptionStep p₁ p₂ n₂).eval ls ρ ≤ n₁.eval ls ρ := by
  unfold Node.subsumptionStep
  split
  · exact Nat.le_refl _
  · dsimp only
    split <;> split
    all_goals apply node_eval_mono
    all_goals simp [subsumeVars_subset]

private theorem insert_self_bound {m : NormLevel} {p : List Name} {n : Node} :
    evalPath ls ρ p (n.eval ls ρ) ≤ NormLevel.eval ls ρ (m.insert p n) := by
  apply NormLevel.eval_le.1 (Nat.le_refl _) p n
  simpa only [Std.TreeMap.get?_eq_getElem?] using
    (Std.TreeMap.getElem?_insert_self (t := m) (k := p) (v := n))

private theorem insert_other_bound {m : NormLevel} {p q : List Name} {new n : Node}
    (hpq : p ≠ q) (hget : m.get? q = some n) :
    evalPath ls ρ q (n.eval ls ρ) ≤ NormLevel.eval ls ρ (m.insert p new) := by
  apply NormLevel.eval_le.1 (Nat.le_refl _) q n
  simp only [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert]
  have hcmp : compare p q ≠ .eq := by simpa using hpq
  rw [if_neg hcmp]
  exact hget

private theorem const_le_activeVar_eval {v : VarNode} (hv : v.var ∈ p)
    (hnz : allNZ ls ρ p) (hc : c ≤ v.offset + 1) : c ≤ v.eval ls ρ := by
  simp [allNZ] at hnz
  simp only [VarNode.eval]
  specialize hnz _ hv
  omega

private theorem varNode_eval_mono {v w : VarNode} (hvar : v.var = w.var)
    (hoff : v.offset ≤ w.offset) : v.eval ls ρ ≤ w.eval ls ρ := by
  simp only [VarNode.eval, hvar]
  omega

private theorem vars_le_self {m : NormLevel} {p : List Name} {old new : Node}
    (hvars : old.var ⊆ new.var) (hnz : allNZ ls ρ p) :
    ∀ v ∈ old.var, v.eval ls ρ ≤ NormLevel.eval ls ρ (m.insert p new) := by
  have hnode := evalPath_le.1 (insert_self_bound (ls := ls) (ρ := ρ)
    (m := m) (p := p) (n := new)) hnz
  exact fun v hv => Node.eval_le.1 hnode |>.2 v (hvars hv)

private theorem vars_le_after_subsume {m : NormLevel} {p₁ p₂ : List Name}
    {old new n₂ : Node} (hvars : new.var = subsumeVars old.var n₂.var)
    (hsub : subset Name.cmp p₂ p₁) (hlen : p₁.length ≠ p₂.length)
    (hget : m.get? p₂ = some n₂) (hnz : allNZ ls ρ p₁) :
    ∀ v ∈ old.var, v.eval ls ρ ≤ NormLevel.eval ls ρ (m.insert p₁ new) := by
  intro v hv
  rcases subsumeVars_dominated hv with hkeep | ⟨w, hw, hvar, hoff⟩
  · have hnode := evalPath_le.1 (insert_self_bound (ls := ls) (ρ := ρ)
      (m := m) (p := p₁) (n := new)) hnz
    exact Node.eval_le.1 hnode |>.2 v (by rw [hvars]; exact hkeep)
  · have hpne : p₁ ≠ p₂ := fun h => hlen (congrArg List.length h)
    have hnz₂ := allNZ_mono (subset_subset hsub) hnz
    have hnode := evalPath_le.1 (insert_other_bound (ls := ls) (ρ := ρ)
      (m := m) (p := p₁) (q := p₂) (new := new) hpne hget) hnz₂
    exact Nat.le_trans (varNode_eval_mono hvar hoff)
      (Node.eval_le.1 hnode |>.2 w hw)

private theorem const_le_of_subsumed {m : NormLevel} {p₁ p₂ : List Name}
    {old new n₂ : Node} (hdom : old.constIsSubsumedBy p₁ p₂ n₂)
    (hsub : subset Name.cmp p₂ p₁) (hget : m.get? p₂ = some n₂)
    (hvars : ∀ v ∈ old.var,
      v.eval ls ρ ≤ NormLevel.eval ls ρ (m.insert p₁ new))
    (hnz : allNZ ls ρ p₁) :
    old.const ≤ NormLevel.eval ls ρ (m.insert p₁ new) := by
  rcases hdom with ⟨hlen, hc⟩ | ⟨hne, v, hv, hvp, hc⟩ |
      ⟨hlen, hc, v, hv, hvp⟩
  · have hpne : p₁ ≠ p₂ := fun h => hlen (congrArg List.length h)
    have hnz₂ := allNZ_mono (subset_subset hsub) hnz
    have hnode := evalPath_le.1 (insert_other_bound (ls := ls) (ρ := ρ)
      (m := m) (p := p₁) (q := p₂) (new := new) hpne hget) hnz₂
    exact Nat.le_trans hc (Node.eval_le.1 hnode |>.1)
  · exact Nat.le_trans (const_le_activeVar_eval hvp hnz hc) (hvars v hv)
  · have hpne : p₁ ≠ p₂ := fun h => hlen (congrArg List.length h)
    have hnz₂ := allNZ_mono (subset_subset hsub) hnz
    have hnode := evalPath_le.1 (insert_other_bound (ls := ls) (ρ := ρ)
      (m := m) (p := p₁) (q := p₂) (new := new) hpne hget) hnz₂
    have hcv : old.const ≤ v.offset + 1 := by omega
    exact Nat.le_trans (const_le_activeVar_eval hvp hnz₂ hcv)
      (Node.eval_le.1 hnode |>.2 v hv)

private theorem subsumptionStep_bound {m : NormLevel} {p₁ p₂ : List Name}
    {n₁ n₂ : Node} (hget : m.get? p₂ = some n₂) :
    evalPath ls ρ p₁ (n₁.eval ls ρ) ≤
      NormLevel.eval ls ρ (m.insert p₁ (n₁.subsumptionStep p₁ p₂ n₂)) := by
  unfold Node.subsumptionStep
  split
  · exact insert_self_bound
  · rename_i hsub'
    simp at hsub'
    change subset Name.cmp p₂ p₁ at hsub'
    have hsub := hsub'
    dsimp only
    split
    · rename_i hvars'
      split
      · exact insert_self_bound
      · rename_i hconst
        have hdom : n₁.constIsSubsumedBy p₁ p₂ n₂ := by
          by_cases hdom : n₁.constIsSubsumedBy p₁ p₂ n₂
          · exact hdom
          · exact False.elim (hconst (.inr hdom))
        apply evalPath_le.2
        intro hnz
        apply Node.eval_le.2
        have hvars := vars_le_self (ls := ls) (ρ := ρ)
          (m := m) (p := p₁) (old := n₁) (new := { n₁ with const := 0 })
          (by simp) hnz
        exact ⟨const_le_of_subsumed (ls := ls) (ρ := ρ)
          hdom hsub hget hvars hnz, hvars⟩
    · rename_i hvars'
      simp at hvars'
      split
      · rename_i hconst
        apply evalPath_le.2
        intro hnz
        apply Node.eval_le.2
        have hvars := vars_le_after_subsume (ls := ls) (ρ := ρ)
          (m := m) (p₁ := p₁) (p₂ := p₂) (old := n₁)
          (new := { n₁ with var := subsumeVars n₁.var n₂.var }) (n₂ := n₂)
          (by simp) hsub hvars'.1 hget hnz
        have hnode := evalPath_le.1 (insert_self_bound (ls := ls) (ρ := ρ)
          (m := m) (p := p₁) (n := { n₁ with var := subsumeVars n₁.var n₂.var })) hnz
        exact ⟨Node.eval_le.1 hnode |>.1, hvars⟩
      · rename_i hconst
        have hdom : n₁.constIsSubsumedBy p₁ p₂ n₂ := by
          by_cases hdom : n₁.constIsSubsumedBy p₁ p₂ n₂
          · exact hdom
          · exact False.elim (hconst (.inr hdom))
        apply evalPath_le.2
        intro hnz
        apply Node.eval_le.2
        have hvars := vars_le_after_subsume (ls := ls) (ρ := ρ)
          (m := m) (p₁ := p₁) (p₂ := p₂) (old := n₁)
          (new := { n₁ with const := 0, var := subsumeVars n₁.var n₂.var })
          (n₂ := n₂) (by simp) hsub hvars'.1 hget hnz
        exact ⟨const_le_of_subsumed (ls := ls) (ρ := ρ)
          hdom hsub hget hvars hnz, hvars⟩

private theorem subsumptionStep_eval {m : NormLevel} {p₁ p₂ : List Name}
    {n₁ n₂ : Node} (hget : m.get? p₂ = some n₂) :
    NormLevel.eval ls ρ (m.insert p₁ (n₁.subsumptionStep p₁ p₂ n₂)) =
      NormLevel.eval ls ρ (m.insert p₁ n₁) := by
  apply eval_replace_eq
  · exact evalPath_mono (subsumptionStep_eval_le n₁ n₂ p₁ p₂)
  · exact subsumptionStep_bound hget

private theorem subsumptionList_eval {m : NormLevel} {p₁ : List Name}
    {entries : List (List Name × Node)}
    (hentries : ∀ x ∈ entries, m.get? x.1 = some x.2) (n₁ : Node) :
    NormLevel.eval ls ρ
      (m.insert p₁ (entries.foldl (init := n₁)
        fun n₁ x => n₁.subsumptionStep p₁ x.1 x.2)) =
      NormLevel.eval ls ρ (m.insert p₁ n₁) := by
  induction entries generalizing n₁ with
  | nil => rfl
  | cons x entries ih =>
    rcases x with ⟨p₂, n₂⟩
    simp only [List.foldl_cons]
    calc
      NormLevel.eval ls ρ
          (m.insert p₁ (entries.foldl (init := n₁.subsumptionStep p₁ p₂ n₂)
            fun n₁ x => n₁.subsumptionStep p₁ x.1 x.2)) =
        NormLevel.eval ls ρ (m.insert p₁ (n₁.subsumptionStep p₁ p₂ n₂)) :=
          ih (fun x hx => hentries x (List.Mem.tail _ hx)) _
      _ = NormLevel.eval ls ρ (m.insert p₁ n₁) :=
        subsumptionStep_eval (hentries _ (.head _))

private theorem subsumptionFold_eval {m : NormLevel} {p₁ : List Name} (n₁ : Node) :
    NormLevel.eval ls ρ
      (m.insert p₁ (m.foldl (init := n₁)
        fun n₁ p₂ n₂ => n₁.subsumptionStep p₁ p₂ n₂)) =
      NormLevel.eval ls ρ (m.insert p₁ n₁) := by
  rw [Std.TreeMap.foldl_eq_foldl_toList]
  apply subsumptionList_eval
  intro x hx
  exact Std.TreeMap.mem_toList_iff_getElem?_eq_some.1 hx

private theorem subsumptionOuterList_eval {entries : List (List Name × Node)}
    {m : NormLevel}
    (hentries : ∀ x ∈ entries, m.get? x.1 = some x.2)
    (hdistinct : entries.Pairwise fun a b => ¬compare a.1 b.1 = .eq) :
    NormLevel.eval ls ρ
      (entries.foldl (init := m) fun m x =>
        m.insert x.1 (m.foldl (init := x.2)
          fun n₁ p₂ n₂ => n₁.subsumptionStep x.1 p₂ n₂)) =
      NormLevel.eval ls ρ m := by
  induction entries generalizing m with
  | nil => rfl
  | cons x entries ih =>
    rcases x with ⟨p₁, n₁⟩
    simp only [List.pairwise_cons] at hdistinct
    simp only [List.foldl_cons]
    let n₁' := m.foldl (init := n₁)
      fun n₁ p₂ n₂ => n₁.subsumptionStep p₁ p₂ n₂
    let m' := m.insert p₁ n₁'
    have hentries' : ∀ x ∈ entries, m'.get? x.1 = some x.2 := by
      intro x hx
      simp only [m', Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert]
      rw [if_neg (hdistinct.1 x hx)]
      exact hentries x (.tail _ hx)
    have hstep : NormLevel.eval ls ρ m' = NormLevel.eval ls ρ m := by
      calc
        NormLevel.eval ls ρ m' = NormLevel.eval ls ρ (m.insert p₁ n₁) :=
          subsumptionFold_eval n₁
        _ = NormLevel.eval ls ρ m := eval_insert_eq
          (hentries _ (.head _)) (Nat.le_refl _) insert_self_bound
    exact (ih hentries' hdistinct.2).trans hstep

theorem NormLevel.subsumption_eval {s : NormLevel} :
    s.subsumption.eval ls ρ = s.eval ls ρ := by
  unfold NormLevel.subsumption
  rw [Std.TreeMap.foldl_eq_foldl_toList]
  simp only [Bool.false_eq_true, if_false]
  apply subsumptionOuterList_eval
  · intro x hx
    exact Std.TreeMap.mem_toList_iff_getElem?_eq_some.1 hx
  · exact Std.TreeMap.distinct_keys_toList

theorem normalize_eval (hu : VLevel.ofLevel ls u = some u') :
    (normalize u).eval ls ρ = u'.eval ρ := by
  simp [normalize, NormLevel.subsumption_eval]
  exact normalizeAux_eval hu (by simp) .nil

theorem Node.eval_congr {a b : Node} (H : a == b) : a.eval ls ρ = b.eval ls ρ := by
  simp +instances [instBEqNode] at H; simp [H, eval]

private theorem evalList_congr {a b : List (List Name × Node)} (H : a == b) (init : Nat) :
    a.foldl (init := init) (fun n x => max' n (evalPath ls ρ x.1 (x.2.eval ls ρ))) =
    b.foldl (init := init) (fun n x => max' n (evalPath ls ρ x.1 (x.2.eval ls ρ))) := by
  induction a generalizing b init with
  | nil =>
    cases b <;> simp_all
  | cons x xs ih =>
    cases b with
    | nil => simp_all
    | cons y ys =>
      rcases x with ⟨px, nx⟩
      rcases y with ⟨py, ny⟩
      simp [BEq.beq, List.beq] at H
      have hp : px = py := LawfulBEq.eq_of_beq H.1.1
      have hv : nx.var = ny.var := LawfulBEq.eq_of_beq H.1.2.2
      have hn := Node.eval_congr (ls := ls) (ρ := ρ) (show nx == ny by
        simp +instances [instBEqNode, H.1.2.1, hv])
      cases hp
      simp only [List.foldl_cons]
      rw [hn]
      exact ih H.2 _

theorem NormLevel.eval_congr {a b : NormLevel} (H : a == b) : a.eval ls ρ = b.eval ls ρ := by
  change a.toList == b.toList at H
  simp only [eval, Std.TreeMap.foldl_eq_foldl_toList]
  exact evalList_congr H 0

theorem NormLevel.le_eval {a b : NormLevel} (h : a.le b) :
    a.eval ls ρ ≤ b.eval ls ρ := by
  rw [NormLevel.eval_le]
  intro p₁ n₁ hget₁
  have hmem₁ : (p₁, n₁) ∈ a.toList :=
    Std.TreeMap.mem_toList_iff_getElem?_eq_some.2 hget₁
  simp only [NormLevel.le, List.all_eq_true] at h
  have hentry := h (p₁, n₁) hmem₁
  dsimp only at hentry
  split at hentry
  · rename_i hz
    simp only [Bool.and_eq_true] at hz
    have hc : n₁.const = 0 := of_decide_eq_true hz.1
    have hv : n₁.var = [] := by simpa using hz.2
    simp [Node.eval, hc, hv, evalPath]
  · simp only [List.any_eq_true] at hentry
    rcases hentry with ⟨⟨p₂, n₂⟩, hmem₂, hcmp⟩
    dsimp only at hcmp
    simp only [Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true] at hcmp
    have hsub := hcmp.1.1.2
    have hconst := hcmp.1.2
    have hvars := hcmp.2
    have hget₂ : b.get? p₂ = some n₂ :=
      Std.TreeMap.mem_toList_iff_getElem?_eq_some.1 hmem₂
    apply evalPath_le.2
    intro hnz₁
    have hnz₂ := allNZ_mono (subset_subset hsub) hnz₁
    have hnode : n₁.eval ls ρ ≤ n₂.eval ls ρ := by
      apply Node.eval_le.2
      constructor
      · rcases hconst with hc | ⟨w, hw, hpath, hoff⟩
        · exact Nat.le_trans (of_decide_eq_true hc)
            (Node.eval_le.1 (Nat.le_refl _) |>.1)
        · have hpath' : w.var ∈ p₂ := by simpa using hpath
          exact Nat.le_trans
            (const_le_activeVar_eval hpath' hnz₂ (of_decide_eq_true hoff))
            (Node.eval_le.1 (Nat.le_refl _) |>.2 w hw)
      · intro v hv
        rcases leVars_dominated hvars hv with ⟨w, hw, hvar, hoff⟩
        exact Nat.le_trans (varNode_eval_mono hvar hoff)
          (Node.eval_le.1 (Nat.le_refl _) |>.2 w hw)
    exact Nat.le_trans hnode
      (evalPath_le.1 (NormLevel.eval_le.1 (Nat.le_refl _) p₂ n₂ hget₂) hnz₂)

end Normalize

theorem geq'_wf (h : geq' u v)
    (hu : VLevel.ofLevel ls u = some u') (hv : VLevel.ofLevel ls v = some v') :
    v' ≤ u' := by
  intro ρ
  rw [← Normalize.normalize_eval hv, ← Normalize.normalize_eval hu]
  exact Normalize.NormLevel.le_eval h

/- The verified comparison bridge closes over Lean's standard logical
quotient/classical basis only.  In particular it does not inherit a project
axiom or any of this repository's remaining sorry frontier. -/
/--
info: 'Lean.Level.Normalize.NormLevel.le_eval' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Normalize.NormLevel.le_eval

/--
info: 'Lean.Level.geq'_wf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms geq'_wf

theorem isStructEq_eq {u v : Level} (h : isStructEq u v) : u = v := by
  induction u generalizing v with
  | zero => cases v <;> simp_all [isStructEq]
  | succ u ih =>
    cases v <;> simp [isStructEq] at h
    exact congrArg Level.succ (ih h)
  | max u₁ u₂ ih₁ ih₂ =>
    cases v <;> simp [isStructEq] at h
    cases ih₁ h.1
    cases ih₂ h.2
    rfl
  | imax u₁ u₂ ih₁ ih₂ =>
    cases v <;> simp [isStructEq] at h
    cases ih₁ h.1
    cases ih₂ h.2
    rfl
  | param u =>
    cases v <;> simp_all [isStructEq]
  | mvar u =>
    rcases u with ⟨u⟩
    cases v <;> simp_all [isStructEq]

theorem isStructEq_iff_eq {u v : Level} : isStructEq u v ↔ u = v := by
  constructor
  · exact isStructEq_eq
  · rintro rfl
    induction u <;> simp_all [isStructEq]

theorem isEquiv_wf (h : isEquiv' u v)
    (hu : VLevel.ofLevel ls u = some u') (hv : VLevel.ofLevel ls v = some v') : u' ≈ v' := by
  simp only [isEquiv', Bool.or_eq_true] at h
  obtain h | h := h
  · cases isStructEq_iff_eq.1 h
    cases hu.symm.trans hv
    rfl
  · refine VLevel.equiv_def.2 fun ls' => ?_
    rw [← Normalize.normalize_eval hu, ← Normalize.normalize_eval hv]
    exact Normalize.NormLevel.eval_congr h

theorem isEquivList_wf (H : Level.isEquivList us vs) :
    List.mapM (VLevel.ofLevel Us) us = some us' →
    List.mapM (VLevel.ofLevel Us) vs = some vs' → us'.Forall₂ (· ≈ ·) vs' := by
  simp [Level.isEquivList] at H; revert us' vs'
  induction us generalizing vs with cases vs <;> simp [List.all2] at H <;> simp | cons u us ih
  rename_i v vs; rintro _ _ u' hu us' hus rfl v' hv vs' hvs rfl
  exact .cons (isEquiv_wf H.1 hu hv) (ih H.2 hus hvs)
