/-
This file is derived from lean4lean and has been modified by Argument Computer Corporation.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/

import Batteries.Tactic.OpenPrivate
import Lean.Data.SMap
import Std.Data.HashMap.Lemmas
import Lean4Lean.Std.Basic
import Lean4Lean.Std.HashMap
import Lean4Lean.Std.NodupKeys

namespace Std.DTreeMap.Internal.Impl

private theorem any_eq_any_toListModel
    {α : Type u} {β : α → Type v} {p : (a : α) → β a → Bool} {m : Impl α β} :
    m.any p = m.toListModel.any (fun x => p x.1 x.2) := by
  simp [any, ForIn.forIn, Id.run_bind]
  rw [forIn_eq_forIn_toListModel, ← toList_eq_toListModel, forIn_eq_forIn']
  induction m.toList with
  | nil => simp
  | cons hd tl ih =>
    simp only [forIn'_eq_forIn, List.any_cons]
    by_cases h : p hd.fst hd.snd = true
    · simp [h]
    · simp only [forIn'_eq_forIn] at ih
      simp [h, ih]

end Std.DTreeMap.Internal.Impl

namespace Std.TreeMap

variable {α : Type u} {β : Type v} {cmp : α → α → Ordering} {t : TreeMap α β cmp}

/-- https://github.com/leanprover/lean4/issues/12798 -/
theorem all_eq_all_toList {p : α → β → Bool} :
    t.all p = t.toList.all fun a => p a.1 a.2 := by
  change t.inner.inner.all p =
    (Std.DTreeMap.Internal.Impl.Const.toList t.inner.inner).all fun a => p a.1 a.2
  rw [Std.DTreeMap.Internal.Impl.all_eq_all_toListModel,
    Std.DTreeMap.Internal.Impl.Const.toList_eq_toListModel_map]
  generalize t.inner.inner.toListModel = l
  induction l with
  | nil => rfl
  | cons x l ih => cases x; simp [ih]

/-- https://github.com/leanprover/lean4/issues/12798 -/
theorem any_eq_any_toList {p : α → β → Bool} :
    t.any p = t.toList.any fun a => p a.1 a.2 := by
  change t.inner.inner.any p =
    (Std.DTreeMap.Internal.Impl.Const.toList t.inner.inner).any fun a => p a.1 a.2
  rw [Std.DTreeMap.Internal.Impl.any_eq_any_toListModel,
    Std.DTreeMap.Internal.Impl.Const.toList_eq_toListModel_map]
  generalize t.inner.inner.toListModel = l
  induction l with
  | nil => rfl
  | cons x l ih => cases x; simp [ih]

end Std.TreeMap

open scoped _root_.List
namespace Lean

noncomputable def PersistentArrayNode.toList' : PersistentArrayNode α → List α :=
  PersistentArrayNode.rec
    (motive_1 := fun _ => List α) (motive_2 := fun _ => List α) (motive_3 := fun _ => List α)
    (node := fun _ => id) (leaf := (·.toList)) (fun _ => id) [] (fun _ _ a b => a ++ b)

namespace PersistentArray

inductive WF : PersistentArray α → Prop where
  | empty : WF .empty
  | push : WF arr → WF (arr.push x)

noncomputable def toList' (arr : PersistentArray α) : List α :=
  arr.root.toList' ++ arr.tail.toList

@[simp] theorem toList'_empty : (.empty : PersistentArray α).toList' = [] := rfl

/-- We cannot prove this because `insertNewLeaf` is partial -/
axiom toList'_push {α} (arr : PersistentArray α) (x : α) :
    (arr.push x).toList' = arr.toList' ++ [x]

@[simp] theorem size_empty : (.empty : PersistentArray α).size = 0 := rfl

@[simp] theorem size_push {α} (arr : PersistentArray α) (x : α) :
    (arr.push x).size = arr.size + 1 := by
  simp [push]; split <;> [rfl; (simp [mkNewTail]; split <;> rfl)]

@[simp] theorem WF.toList'_length (h : WF arr) : arr.toList'.length = arr.size := by
  induction h <;> simp [*, toList'_push]

end PersistentArray

namespace PersistentHashMap

noncomputable def Node.toList' : Node α β → List (α × β) :=
  Node.rec
    (motive_1 := fun _ => List (α × β)) (motive_2 := fun _ => List (α × β))
    (motive_3 := fun _ => List (α × β)) (motive_4 := fun _ => List (α × β))
    (entries := fun _ => id) (collision := fun ks xs _ => ks.toList.zip xs.toList)
    (mk := fun _ => id)
    (nil := []) (cons := fun _ _ l1 l2 => l1 ++ l2)
    (entry := fun a b => [(a, b)]) (ref := fun _ => id) (null := [])

noncomputable def toList' [BEq α] [Hashable α] (m : PersistentHashMap α β) :
    List (α × β) := m.root.toList'

inductive WF [BEq α] [Hashable α] : PersistentHashMap α β → Prop where
  | empty : WF .empty
  | insert : WF m → WF (m.insert a b)

/-- We can't prove this because `Lean.PersistentHashMap.insertAux` is opaque -/
axiom WF.toList'_insert {α β} [BEq α] [Hashable α]
    [PartialEquivBEq α] [LawfulHashable α]
    {m : PersistentHashMap α β} (_ : WF m) (a : α) (b : β) :
    (m.insert a b).toList' ~ (a, b) :: m.toList'.filter (¬a == ·.1)

/-- We can't prove this because `Lean.PersistentHashMap.findAux` is opaque -/
axiom WF.find?_eq {α β} [BEq α] [Hashable α]
    [PartialEquivBEq α] [LawfulHashable α]
    {m : PersistentHashMap α β} (_ : WF m) (a : α) : m.find? a = m.toList'.lookup a

/-- We can't prove this because `Lean.PersistentHashMap.{findAux, containsAux}` are opaque -/
axiom findAux_isSome {α β} [BEq α] {node : Node α β} (i : USize) (a : α) :
    containsAux node i a = (findAux node i a).isSome

@[simp] theorem toList'_empty [BEq α] [Hashable α] :
    (.empty : PersistentHashMap α β).toList' = [] := by
  have this n : @Node.toList' α β (.entries ⟨.replicate n .null⟩) = [] := by
    simp [Node.toList']
    induction n <;> simp [*, List.replicate_succ]
  apply this

@[simp] theorem toList'_empty' [BEq α] [Hashable α] :
    ({} : PersistentHashMap α β).toList' = [] := toList'_empty

theorem find?_isSome {α β} [BEq α] [Hashable α]
    (m : PersistentHashMap α β) (a : α) : m.contains a = (m.find? a).isSome := findAux_isSome ..

theorem WF.nodupKeys [BEq α] [Hashable α]
    [LawfulBEq α] [LawfulHashable α]
    {m : PersistentHashMap α β} (h : WF m) : m.toList'.NodupKeys := by
  induction h with
  | empty => simp; exact .nil
  | insert h1 ih =>
    refine (h1.toList'_insert ..).nodupKeys_iff.2 (List.nodupKeys_cons.2 ⟨?_, ih.filter _⟩)
    rintro _ h3 rfl
    simpa using (List.mem_filter.1 h3).2

variable [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α] in
theorem WF.find?_insert {s : PersistentHashMap α β} (h : s.WF) :
    (s.insert k v).find? x = if k == x then some v else s.find? x := by
  rw [h.insert.find?_eq, h.find?_eq, BEq.comm,
    (h.toList'_insert ..).lookup_eq h.insert.nodupKeys, List.lookup]
  cases eq : x == k <;> simp
  induction s.toList' with
  | nil => rfl
  | cons kv l ih =>
    simp [List.filter]; split <;> simp [List.lookup, *]
    split <;> [skip; rfl]
    rename_i h1 _ h2
    simp at h1 h2; simp [h1, h2] at eq

end PersistentHashMap

namespace SMap

variable [BEq α] [Hashable α]
structure WF (s : SMap α β) where
  map₂ : s.map₂.WF
  stage : s.stage₁ → s.map₂ = .empty
  disjoint : s.map₂.contains a → ¬a ∈ s.map₁

theorem WF.empty : WF ({} : SMap α β) := ⟨.empty, fun _ => rfl, by simp⟩

protected nonrec theorem WF.insert [LawfulBEq α] [LawfulHashable α] {s : SMap α β}
    (h : s.WF) (k : α) (v : β) (hn : s.find? k = none) : (s.insert k v).WF := by
  unfold insert; split
  · refine ⟨h.map₂, h.stage, fun _ h' => ?_⟩
    have := h.stage
    simp_all [find?, PersistentHashMap.find?_isSome, PersistentHashMap.WF.empty.find?_eq]
  · refine ⟨h.map₂.insert .., nofun, fun h1 => ?_⟩
    simp_all [PersistentHashMap.find?_isSome, h.map₂.find?_insert]
    revert ‹_›; split
    · simp_all [find?]
    · exact h.disjoint ∘ by simp [PersistentHashMap.find?_isSome]

variable [LawfulBEq α] [LawfulHashable α] in
theorem WF.find?_insert {s : SMap α β} (h : s.WF) :
    (s.insert k v).find? x = if k == x then some v else s.find? x := by
  unfold insert; split <;> simp [find?]
  · exact Std.HashMap.getElem?_insert (α := α)
  · rw [h.map₂.find?_insert]; split <;> rfl

noncomputable def toList' [BEq α] [Hashable α] (m : SMap α β) :
    List (α × β) := m.map₂.toList' ++ m.map₁.toList

open scoped _root_.List in
theorem WF.toList'_insert {α β} [BEq α] [LawfulBEq α] [Hashable α] [LawfulHashable α]
    {m : SMap α β} (wf : WF m) (a : α) (b : β)
    (h : m.find? a = none) :
    (m.insert a b).toList' ~ (a, b) :: m.toList' := by
  unfold insert; split <;> simp [toList']
  · have : EquivBEq α := inferInstance; clear ‹LawfulBEq _›
    have := wf.stage rfl; simp [find?] at this h; subst this; simp
    refine (List.filter_eq_self.2 ?_ ▸ Std.HashMap.insert_toList (α := α) .. :)
    rintro ⟨a', b⟩ h
    refine Decidable.by_contra fun h2 => ?_
    simp at h2
    have := Std.HashMap.getElem?_eq_some_iff_exists_beq_and_mem_toList.2 ⟨_, h2, h⟩
    exact ‹¬_› (Std.HashMap.mem_of_getElem? this)
  · refine .append_right (l₂ := _::_) _ ?_
    refine (List.filter_eq_self.2 ?_ ▸ wf.map₂.toList'_insert .. :)
    rintro ⟨a', b⟩ h'
    have := wf.map₂.find?_eq a
    simp_all [find?]; rintro rfl
    exact h.1 _ _ h' rfl

theorem WF.find?_eq {α β} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
    {m : SMap α β} (wf : WF m) (a : α) : m.find? a = m.toList'.lookup a := by
  simp [find?]; split
  · cases wf.stage rfl
    simp [toList']
    exact Std.HashMap.getElem?_eq_lookup_toList ..
  · simp [toList', List.lookup_append, wf.map₂.find?_eq]
    cases List.lookup a .. <;> simp [Std.HashMap.getElem?_eq_lookup_toList]

theorem WF.find?'_eq_find? {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    {m : SMap α β} (wf : WF m) (a : α) : m.find?' a = m.find? a := by
  simp [find?, find?']; split; · rfl
  rename_i m₁ m₂
  cases e1 : m₁[a]? <;> cases e2 : m₂.find? a <;> simp
  cases wf.disjoint (by simp [PersistentHashMap.find?_isSome, e2]) (Std.HashMap.mem_of_getElem? e1)

theorem find?_isSome {α β} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
    (m : SMap α β) (a : α) : m.contains a = (m.find? a).isSome := by
  simp [find?, contains]; split <;> simp [← PersistentHashMap.find?_isSome, Bool.or_comm]

end SMap

namespace Syntax

def structEq' : Syntax → Syntax → Bool
  | .missing, .missing => true
  | .node _ k args, .node _ k' args' => k == k' &&
    (args.size == args'.size &&
      (args.toList.attach.zip args'.toList.attach).all fun (a, b) =>
        have := Array.mem_toList_iff.1 a.2; structEq' a b)
  | .atom _ val, .atom _ val' => val == val'
  | .ident _ rawVal val preresolved, Syntax.ident _ rawVal' val' preresolved' =>
    rawVal == rawVal' && val == val' && preresolved == preresolved'
  | _, _ => false
termination_by x _ => x

theorem structEq'_node :
    structEq' (.node _x k args) (.node _y k' args') = (k == k' && args.isEqv args' structEq') := by
  unfold structEq'; simp; congr 1
  by_cases h : args.size = args'.size <;> [simp [h]; simp [Array.isEqv, h]]
  let ⟨args⟩ := args; let ⟨args'⟩ := args'; simp at h ⊢
  have' : ((args.attach.map (·.1)).zip (args'.attach.map (·.1))).all
      (fun x => x.1.structEq' x.2) = _ := by
    simp only [List.zip_map_left, List.zip_map_right]; simp [Function.comp_def]; rfl
  rw [← this]; simp; clear this
  induction args generalizing args' <;> cases args' <;> simp at h <;> simp [List.isEqv, *]

/-- This is a `partial` because it is not obviously terminating. The `structEq'_node` theorem
shows that a definition with the same clauses can be defined manually. -/
axiom structEq_eq : structEq a b = structEq' a b
end Syntax

namespace Level

/-!
### A total copy of `Lean.Level.normalize`

`Lean.Level.normalize` and four of its helpers are `partial def`s, so they are opaque and nothing
can be proved about them. The `Total` namespace below is a clause-by-clause copy of
[Lean's `Lean/Level.lean`](https://github.com/leanprover/lean4/blob/v4.33.0-rc2/src/Lean/Level.lean#L319-L404),
under the same names, with the termination proofs supplied. That makes `normalize_eq` below a
purely syntactic trust assumption, checkable by reading the two definitions side by side;
`Lean4Lean.Tests.LevelStd` also checks it on a finite corpus of levels.
-/
namespace Total

/-- The structural size of a level, used as the termination measure for `normalize`. -/
def size : Level → Nat
  | .zero | .param _ | .mvar _ => 1
  | .succ l => size l + 1
  | .max l₁ l₂ => size l₁ + size l₂ + 1
  | .imax l₁ l₂ => size l₁ + size l₂ + 2

/-- Secondary termination measure for `normalize`: in the `imax` branch it recurses on
`mkLevelMax l₁ l₂`, which has the same `size` as `imax l₁ l₂` but a smaller `tag`. -/
private def tag (l : Level) : Nat :=
  match l.getLevelOffset with
  | .imax .. => 1
  | _ => 0

private theorem tag_le (l : Level) : tag l ≤ 1 := by unfold tag; split <;> omega

theorem one_le_size (l : Level) : 1 ≤ size l := by cases l <;> simp [size]

private theorem getOffsetAux_eq (l : Level) (k) : getOffsetAux l k = getOffsetAux l 0 + k := by
  induction l generalizing k with
  | succ l ih => rw [getOffsetAux, ih (k+1), getOffsetAux, ih 1]; omega
  | _ => simp [getOffsetAux]

theorem size_getLevelOffset (l : Level) :
    size l.getLevelOffset + l.getOffset = size l := by
  simp only [getOffset]
  induction l with | succ l ih => ?_ | _ => rfl
  show size l.getLevelOffset + getOffsetAux l 1 = size l + 1
  rw [getOffsetAux_eq l 1]; omega

end Total
open private accMax mkIMaxAux isExplicitSubsumedAux isExplicitSubsumed from Lean.Level

def Total.mkMaxAux (lvls : Array Level) (extraK : Nat) (i : Nat)
    (prev : Level) (prevK : Nat) (result : Level) : Level :=
  if h : i < lvls.size then
    let lvl   := lvls[i]
    let curr  := lvl.getLevelOffset
    let currK := lvl.getOffset
    if curr == prev then mkMaxAux lvls extraK (i+1) curr currK result
    else mkMaxAux lvls extraK (i+1) curr currK (accMax result prev (extraK + prevK))
  else accMax result prev (extraK + prevK)

def Total.skipExplicit (lvls : Array Level) (i : Nat) : Nat :=
  if h : i < lvls.size then
    if lvls[i].getLevelOffset.isZero then skipExplicit lvls (i+1) else i
  else i

def Total.isExplicitSubsumedAux (lvls : Array Level) (maxExplicit : Nat) (i : Nat) : Bool :=
  if h : i < lvls.size then
    if lvls[i].getOffset ≥ maxExplicit then true
    else isExplicitSubsumedAux lvls maxExplicit (i+1)
  else false

/-- Patch for `partial def Lean.Level.isExplicitSubsumedAux`. -/
axiom isExplicitSubsumedAux_eq : isExplicitSubsumedAux = Total.isExplicitSubsumedAux

mutual

/-- A total copy of `partial def Lean.Level.normalize`. -/
def Total.normalize (l : Level) : Level :=
  if isAlreadyNormalizedCheap l then l else
  let k := l.getOffset
  match h : l.getLevelOffset with
  | .max l₁ l₂ =>
    let lvls  := getMaxArgsAux l₁ false #[]
    let lvls  := getMaxArgsAux l₂ false lvls
    let lvls  := lvls.qsort normLt
    let firstNonExplicit := skipExplicit lvls 0
    let i := if isExplicitSubsumed lvls firstNonExplicit then firstNonExplicit
              else firstNonExplicit - 1
    let lvl₁  := lvls[i]!
    let prev  := lvl₁.getLevelOffset
    let prevK := lvl₁.getOffset
    mkMaxAux lvls k (i+1) prev prevK Level.zero
  | .imax l₁ l₂ =>
    if l₂.isNeverZero then addOffset (normalize (mkLevelMax l₁ l₂)) k
    else addOffset (mkIMaxAux (normalize l₁) (normalize l₂)) k
  | _ => unreachable!
termination_by (1, 3 * size l + tag l)
decreasing_by all_goals
  refine .right _ ?_
  have hsz := size_getLevelOffset l
  rw [h] at hsz
  simp only [size] at hsz
  have := one_le_size l₁
  have := one_le_size l₂
  have := tag_le l₁
  have := tag_le l₂
  first
  | omega
  | have ht : tag l = 1 := by simp [tag, h]
    have e1 : size (mkLevelMax l₁ l₂) = size l₁ + size l₂ + 1 := rfl
    have e2 : tag (mkLevelMax l₁ l₂) = 0 := rfl
    omega

def Total.getMaxArgsAux : Level → Bool → Array Level → Array Level
  | .max l₁ l₂, norm, lvls => getMaxArgsAux l₂ norm (getMaxArgsAux l₁ norm lvls)
  | l, false, lvls => getMaxArgsAux (normalize l) true lvls
  | l, true, lvls => lvls.push l
termination_by l b => (if b then 0 else 1, 3 * size l + tag l + 1)
decreasing_by
  any_goals cases norm
  any_goals first | refine .right _ ?_ | exact .left _ _ (by decide)
  all_goals first
  | omega
  | have e1 : size (Level.max l₁ l₂) = size l₁ + size l₂ + 1 := rfl
    have e2 : tag (Level.max l₁ l₂) = 0 := rfl
    have := one_le_size l₁
    have := one_le_size l₂
    have := tag_le l₁
    have := tag_le l₂
    omega

end

/-- `Lean.Level.normalize` is a `partial def`, so it is opaque;
`Total.normalize` above is a total copy of it. -/
axiom normalize_eq : normalize = Total.normalize

def mkData' (h : UInt64) (depth : Nat := 0) (hasMVar hasParam : Bool := false) : Level.Data :=
  if depth > Nat.pow 2 24 - 1 then panic! "universe level depth is too big"
  else
    h.toUInt32.toUInt64 +
    hasMVar.toUInt64.shiftLeft 32 +
    hasParam.toUInt64.shiftLeft 33 +
    depth.toUInt64.shiftLeft 40

/-- This exists only for the bit-twiddling proofs, it shouldn't appear
in the main results, which use the functions below instead -/
axiom mkData_eq : @mkData = @mkData'

def hasParam' : Level → Bool
  | .param .. => true
  | .zero | .mvar .. => false
  | .succ l => l.hasParam'
  | .max l₁ l₂ | .imax l₁ l₂ => l₁.hasParam' || l₂.hasParam'

/-- This was false prior to the fix of lean4#8554; it should now be provable
using `mkData_eq` and friends, but this has not been done yet -/
axiom hasParam_eq (l : Level) : l.hasParam = l.hasParam'

def hasMVar' : Level → Bool
  | .mvar .. => true
  | .zero | .param .. => false
  | .succ l => l.hasMVar'
  | .max l₁ l₂ | .imax l₁ l₂ => l₁.hasMVar' || l₂.hasMVar'

/-- This was false prior to the fix of lean4#8554; it should now be provable
using `mkData_eq` and friends, but this has not been done yet -/
axiom hasMVar_eq (l : Level) : l.hasMVar = l.hasMVar'

/-- This is because the `BEq` instance is implemented in C++ -/
@[instance] axiom instLawfulBEqLevel : LawfulBEq Level

end Level

namespace Expr

def mkData'
    (h : UInt64) (looseBVarRange : Nat := 0) (approxDepth : UInt32 := 0)
    (hasFVar hasExprMVar hasLevelMVar hasLevelParam : Bool := false)
    : Expr.Data :=
  let approxDepth : UInt8 := if approxDepth > 255 then 255 else approxDepth.toUInt8
  assert! (looseBVarRange ≤ Nat.pow 2 20 - 1)
  h.toUInt32.toUInt64 +
  approxDepth.toUInt64.shiftLeft 32 +
  hasFVar.toUInt64.shiftLeft 40 +
  hasExprMVar.toUInt64.shiftLeft 41 +
  hasLevelMVar.toUInt64.shiftLeft 42 +
  hasLevelParam.toUInt64.shiftLeft 43 +
  looseBVarRange.toUInt64.shiftLeft 44

/-- This exists only for the bit-twiddling proofs, it shouldn't appear
in the main results, which use the functions below instead -/
axiom mkData_eq : @mkData = @mkData'

@[inline] def mkAppData' (fData : Data) (aData : Data) : Data :=
  let depth          := max fData.approxDepth.toUInt16 aData.approxDepth.toUInt16 + 1
  let approxDepth    := if depth > 255 then 255 else depth.toUInt8
  let looseBVarRange := max fData.looseBVarRange aData.looseBVarRange
  let hash           := mixHash fData aData
  let fData : UInt64 := fData
  let aData : UInt64 := aData
  assert! looseBVarRange ≤ (Nat.pow 2 20 - 1).toUInt32
  (fData ||| aData) &&& (15 : UInt64) <<< (40 : UInt64) |||
  hash.toUInt32.toUInt64 |||
  approxDepth.toUInt64 <<< (32 : UInt64) |||
  looseBVarRange.toUInt64 <<< (44 : UInt64)

/-- This exists only for the bit-twiddling proofs, it shouldn't appear
in the main results, which use the functions below instead -/
axiom mkAppData_eq : @mkAppData = @mkAppData'

def looseBVarRange' : Expr → Nat
  | .bvar i => i + 1
  | .const ..
  | .sort _
  | .fvar _
  | .mvar _
  | .lit _ => 0
  | .mdata _ e
  | .proj _ _ e => e.looseBVarRange'
  | .app e1 e2 => max e1.looseBVarRange' e2.looseBVarRange'
  | .lam _ e1 e2 _
  | .forallE _ e1 e2 _ => max e1.looseBVarRange' (e2.looseBVarRange' - 1)
  | .letE _ e1 e2 e3 _ => max (max e1.looseBVarRange' e2.looseBVarRange') (e3.looseBVarRange' - 1)

/-- This was false prior to the fix of lean4#8554; it should now be provable
using `mkData_eq` and friends, but this has not been done yet -/
axiom looseBVarRange_eq (e : Expr) : e.looseBVarRange = e.looseBVarRange'

/-- This could be an `@[implemented_by]` -/
axiom replace_eq (e : Expr) (f) : e.replace f = e.replaceNoCache f

def liftLooseBVars' (e : @& Expr) (s d : @& Nat) : Expr :=
  match e with
  | .bvar i => .bvar (if i < s then i else i + d)
  | .mdata m e => .mdata m (liftLooseBVars' e s d)
  | .proj n i e => .proj n i (liftLooseBVars' e s d)
  | .app f a => .app (liftLooseBVars' f s d) (liftLooseBVars' a s d)
  | .lam n t b bi => .lam n (liftLooseBVars' t s d) (liftLooseBVars' b (s+1) d) bi
  | .forallE n t b bi => .forallE n (liftLooseBVars' t s d) (liftLooseBVars' b (s+1) d) bi
  | .letE n t v b bi =>
    .letE n (liftLooseBVars' t s d) (liftLooseBVars' v s d) (liftLooseBVars' b (s+1) d) bi
  | e@(.const ..)
  | e@(.sort _)
  | e@(.fvar _)
  | e@(.mvar _)
  | e@(.lit _) => e

def lowerLooseBVars' (e : @& Expr) (s d : @& Nat) : Expr :=
  if s < d then e else
  match e with
  | .bvar i => .bvar (if i < s then i else i - d)
  | .mdata m e => .mdata m (lowerLooseBVars' e s d)
  | .proj n i e => .proj n i (lowerLooseBVars' e s d)
  | .app f a => .app (lowerLooseBVars' f s d) (lowerLooseBVars' a s d)
  | .lam n t b bi => .lam n (lowerLooseBVars' t s d) (lowerLooseBVars' b (s+1) d) bi
  | .forallE n t b bi => .forallE n (lowerLooseBVars' t s d) (lowerLooseBVars' b (s+1) d) bi
  | .letE n t v b bi =>
    .letE n (lowerLooseBVars' t s d) (lowerLooseBVars' v s d) (lowerLooseBVars' b (s+1) d) bi
  | e@(.const ..)
  | e@(.sort _)
  | e@(.fvar _)
  | e@(.mvar _)
  | e@(.lit _) => e

/-- This could be an `@[implemented_by]` -/
axiom lowerLooseBVars_eq (e : Expr) (s d) : e.lowerLooseBVars s d = e.lowerLooseBVars' s d

def instantiate1' (e : Expr) (subst : Expr) (d := 0) : Expr :=
  match e with
  | .bvar i => if i < d then e else if i = d then subst.liftLooseBVars' 0 d else .bvar (i - 1)
  | .mdata m e => .mdata m (instantiate1' e subst d)
  | .proj s i e => .proj s i (instantiate1' e subst d)
  | .app f a => .app (instantiate1' f subst d) (instantiate1' a subst d)
  | .lam n t b bi => .lam n (instantiate1' t subst d) (instantiate1' b subst (d+1)) bi
  | .forallE n t b bi => .forallE n (instantiate1' t subst d) (instantiate1' b subst (d+1)) bi
  | .letE n t v b bi =>
    .letE n (instantiate1' t subst d) (instantiate1' v subst d) (instantiate1' b subst (d+1)) bi
  | .const ..
  | .sort _
  | .fvar _
  | .mvar _
  | .lit _ => e

/-- This could be an `@[implemented_by]` -/
axiom instantiate1_eq (e : Expr) (subst) : e.instantiate1 subst = e.instantiate1' subst

@[simp] def instantiateList : Expr → List Expr → (k :_:= 0) → Expr
  | e, [], _ => e
  | e, a :: as, k => instantiateList (instantiate1' e a k) as k

/-- This could be an `@[implemented_by]` -/
axiom instantiate_eq (e : Expr) (subst) :
    e.instantiate subst = e.instantiateList subst.toList

/-- This could be an `@[implemented_by]` -/
axiom instantiateRev_eq (e : Expr) (subst) :
    e.instantiateRev subst = e.instantiate subst.reverse

/-- This could be an `@[implemented_by]` -/
axiom instantiateRange_eq (e : Expr) (subst) :
    e.instantiateRange start stop subst = e.instantiate (subst.extract start stop)

/-- This could be an `@[implemented_by]` -/
axiom instantiateRevRange_eq (e : Expr) (subst) :
    e.instantiateRevRange start stop subst = e.instantiateRev (subst.extract start stop)

def abstract1 (v : FVarId) : Expr → (k :_:= 0) → Expr
  | .bvar i, d => .bvar (if i < d then i else i + 1)
  | e@(.fvar v'), d => if v == v' then .bvar d else e
  | .mdata m e, d => .mdata m (abstract1 v e d)
  | .proj s i e, d => .proj s i (abstract1 v e d)
  | .app f a, d => .app (abstract1 v f d) (abstract1 v a d)
  | .lam n t b bi, d => .lam n (abstract1 v t d) (abstract1 v b (d+1)) bi
  | .forallE n t b bi, d => .forallE n (abstract1 v t d) (abstract1 v b (d+1)) bi
  | .letE n t val b bi, d =>
    .letE n (abstract1 v t d) (abstract1 v val d) (abstract1 v b (d+1)) bi
  | e@(.const ..), _
  | e@(.sort _), _
  | e@(.mvar _), _
  | e@(.lit _), _ => e

@[simp] def abstractList : Expr → List FVarId → (k :_:= 0) → Expr
  | e, [], _ => e
  | e, a :: as, k => abstractList (abstract1 a e k) as k

/-- This could be an `@[implemented_by]` -/
axiom abstract_eq (e : Expr) (xs : List FVarId) :
    e.abstract ⟨xs.map .fvar⟩ = e.abstractList xs

/-- This could be an `@[implemented_by]` -/
axiom abstractRange_eq (e : Expr) (n : Nat) (xs : Array Expr) :
    e.abstractRange n xs = e.abstract (xs.extract 0 n)

def hasLooseBVar' : (e : @& Expr) → (bvarIdx : @& Nat) → Bool
  | .bvar i, d => i = d
  | .mdata _ e, d
  | .proj _ _ e, d => hasLooseBVar' e d
  | .app f a, d => hasLooseBVar' f d || hasLooseBVar' a d
  | .lam _ t b _, d
  | .forallE _ t b _, d => hasLooseBVar' t d || hasLooseBVar' b (d+1)
  | .letE _ t v b _, d => hasLooseBVar' t d || hasLooseBVar' v d || hasLooseBVar' b (d+1)
  | .const .., _
  | .sort _, _
  | .fvar _, _
  | .mvar _, _
  | .lit _, _ => false

/-- This could be an `@[implemented_by]` -/
axiom hasLooseBVar_eq (e : Expr) (n : Nat) : e.hasLooseBVar n = e.hasLooseBVar' n

def eqv' : (e1 e2 : Expr) → (strict : Bool := false) → Bool
  | .bvar i, .bvar i', _
  | .lit i, .lit i', _
  | .mvar i, .mvar i', _
  | .fvar i, .fvar i', _
  | .sort i, .sort i', _ => i == i'
  | .mdata d e, .mdata d' e', st => e.eqv' e' st && d.entries == d'.entries
  | .proj s i e, .proj s' i' e', st => e.eqv' e' st && s == s' && i == i'
  | .const n ls, .const n' ls', _ => n == n' && ls == ls'
  | .app f a, .app f' a', st => f.eqv' f' st && a.eqv' a' st
  | .lam n t b bi, .lam n' t' b' bi', st
  | .forallE n t b bi, .forallE n' t' b' bi', st =>
    t.eqv' t' st && b.eqv' b' st && (!st || (n == n' && bi == bi'))
  | .letE n t v b nd, .letE n' t' v' b' nd', st =>
    t.eqv' t' st && v.eqv' v' st && b.eqv' b' st && nd == nd' && (!st || n == n')
  | _, _, _ => false

/-- This could be an `@[implemented_by]` -/
axiom eqv_eq (e1 e2 : Expr) : e1.eqv e2 = e1.eqv' e2

end Expr
