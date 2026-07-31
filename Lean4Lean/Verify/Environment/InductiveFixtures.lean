import Lean4Lean.Verify.Environment.Lemmas
import Lean4Lean.Verify.Environment.Normalization
import Lean4Lean.Inductive.Add
import Lean4Lean.Theory.Meta
import Lean4Lean.Theory.InductiveFixtures
import Lean4Lean.Theory.Typing.Meta

/-! End-to-end replay fixtures for inductive environment alignment.

The Theory fixtures compare generated recursors and iota rules with Lean's
kernel declarations. This module closes the next bridge: it quotes the actual
`ConstantInfo` metadata, translates each metadata type in the precise
intermediate Theory environment, constructs `AddInduct`, and drives the live
`TrEnv'.induct` case. -/

namespace Lean4Lean.InductiveReplayFixtures
open Lean Meta Elab Term
open Lean4Lean.InductiveFixtures

/- These instances are used only by the elaborators below to quote the kernel
metadata returned by `getConstInfo`. -/
deriving instance ToExpr for ConstantVal
deriving instance ToExpr for InductiveVal
deriving instance ToExpr for ConstructorVal
deriving instance ToExpr for RecursorRule
deriving instance ToExpr for RecursorVal
deriving instance ToExpr for ReducibilityHints
deriving instance ToExpr for DefinitionSafety
deriving instance ToExpr for DefinitionVal

syntax "kernelInductInfo%" ident : term
syntax "kernelCtorInfo%" ident : term
syntax "kernelRecInfo%" ident : term
syntax "kernelRecRuleRhs%" ident num : term
syntax "kernelDefVal%" ident : term

elab_rules : term
  | `(kernelInductInfo% $n:ident) => do
    let name ← realizeGlobalConstNoOverloadWithInfo n
    let .inductInfo info ← getConstInfo name
      | throwError "expected inductive metadata for {name}"
    return mkApp (mkConst ``ConstantInfo.inductInfo) (toExpr info)
  | `(kernelCtorInfo% $n:ident) => do
    let name ← realizeGlobalConstNoOverloadWithInfo n
    let .ctorInfo info ← getConstInfo name
      | throwError "expected constructor metadata for {name}"
    return mkApp (mkConst ``ConstantInfo.ctorInfo) (toExpr info)
  | `(kernelRecInfo% $n:ident) => do
    let name ← realizeGlobalConstNoOverloadWithInfo n
    let .recInfo info ← getConstInfo name
      | throwError "expected recursor metadata for {name}"
    return mkApp (mkConst ``ConstantInfo.recInfo) (toExpr info)
  | `(kernelDefVal% $n:ident) => do
    let name ← realizeGlobalConstNoOverloadWithInfo n
    let .defnInfo info ← getConstInfo name
      | throwError "expected definition metadata for {name}"
    return toExpr info

/-- Quote one kernel recursor-rule RHS using the rule's own universe-parameter
order. This lets replay fixtures compare implementation metadata with the
Theory equation generator by reduction, including lambdas under recursive Pi
arguments. -/
elab_rules : term
  | `(kernelRecRuleRhs% $n:ident $i:num) => do
    let name ← realizeGlobalConstNoOverloadWithInfo n
    let .recInfo info ← getConstInfo name
      | throwError "expected recursor metadata for {name}"
    let some rule := info.rules[i.getNat]?
      | throwError "missing recursor rule {i.getNat} for {name}"
    let rhs ← Lean4Lean.Meta.expandExpr rule.rhs
    let rhs ← Lean4Lean.Meta.ofExpr info.levelParams {} rhs
    return toExpr rhs

/- Construct the representation-only half of a metadata-type translation.
The `to_trExprS` theorem supplies every typing premise from the declaration's
actual Theory `WF` evidence. -/
syntax "tr_type_expr_tac" : tactic
macro_rules
  | `(tactic| tr_type_expr_tac) => `(tactic|
    first
    | apply TrTypeExpr.bvar; rfl
    | apply TrTypeExpr.sort; rfl
    | apply TrTypeExpr.const <;>
        (first | assumption | rfl | (dsimp; simp [VLevel.params']))
    | apply TrTypeExpr.app <;> tr_type_expr_tac
    | apply TrTypeExpr.forallE <;> tr_type_expr_tac)

local instance : Inhabited VEnv := ⟨.empty⟩

/-! ## Nat -/

/-- Kernel metadata, captured at elaboration rather than reconstructed by the
fixture. A change in Lean's emitted record is therefore a compile failure. -/
def natInfo : ConstantInfo := kernelInductInfo% Nat
def natZeroInfo : ConstantInfo := kernelCtorInfo% Nat.zero
def natSuccInfo : ConstantInfo := kernelCtorInfo% Nat.succ
def natRecInfo : ConstantInfo := kernelRecInfo% Nat.rec
def natZeroKernelRuleRhs : VExpr := kernelRecRuleRhs% Nat.rec 0
def natSuccKernelRuleRhs : VExpr := kernelRecRuleRhs% Nat.rec 1

example : natInfo.name = ``Nat := rfl
example : natZeroInfo.name = ``Nat.zero := rfl
example : natSuccInfo.name = ``Nat.succ := rfl
example : natRecInfo.name = ``Nat.rec := rfl
example : natZeroKernelRuleRhs =
    natChecked.identityGeneration.generatedRules[0].rhs := rfl
example : natSuccKernelRuleRhs =
    natChecked.identityGeneration.generatedRules[1].rhs := rfl

def natTypeEnv := (VEnv.empty.addConst natType.name natType.toVConstant).get!
def natZeroEnv :=
  (natTypeEnv.addConst natType.ctors[0].name natType.ctors[0].toVConstant).get!
def natCtorEnv :=
  (natZeroEnv.addConst natType.ctors[1].name natType.ctors[1].toVConstant).get!
def natRecEnv :=
  (natCtorEnv.addConst ``Nat.rec (VInductDecl.recConst 0 ``Nat 0 natType)).get!

theorem natTypeEnv_ordered : natTypeEnv.Ordered := by
  refine .const .empty ?_ rfl
  exact ⟨.succ (.succ .zero), VEnv.HasType.sort (by decide)⟩

theorem natZeroEnv_ordered : natZeroEnv.Ordered := by
  refine .const (n := natType.ctors[0].name) (ci := natType.ctors[0].toVConstant)
    natTypeEnv_ordered ?_ rfl
  have hNat : natTypeEnv.constants ``Nat = some natType.toVConstant := rfl
  exact ⟨.succ .zero, by type_tac⟩

theorem natSucc_wf : natType.ctors[1].toVConstant.WF natZeroEnv := by
  have hNat : natZeroEnv.constants ``Nat = some natType.toVConstant := rfl
  refine ⟨.imax (.succ .zero) (.succ .zero), ?_⟩
  refine VEnv.HasType.forallE (u := .succ .zero) (v := .succ .zero) ?_ ?_
  · type_tac
  · type_tac

theorem natCtorEnv_ordered : natCtorEnv.Ordered := by
  exact .const (n := natType.ctors[1].name) (ci := natType.ctors[1].toVConstant)
    natZeroEnv_ordered natSucc_wf rfl

/-- `Nat` satisfies the public Stage-3 declaration contract without a fixture
assumption. -/
theorem natDecl_wf : natDecl.WF VEnv.empty := by
  refine ⟨rfl, ?_⟩
  intro ty hty
  have hty' : ty = natType := List.mem_singleton.1 (by simpa [natDecl] using hty)
  subst ty
  refine ⟨?_, ?_⟩
  · change True
    trivial
  intro c hc
  rcases List.mem_cons.1 hc with rfl | hc
  · constructor
    · change True
      trivial
    · change VExpr.sort (.succ .zero) = VExpr.sort (.succ .zero)
      rfl
  · have hc' := List.mem_singleton.1 hc
    subst c
    constructor
    · refine ⟨.inl rfl, ?_, trivial⟩
      intro
      rfl
    · change VExpr.sort (.succ .zero) = VExpr.sort (.succ .zero)
      rfl

/-- The exact intermediate invariant used to type the generated recursor. -/
theorem natStage3 :
    VInductDecl.Stage3Env natCtorEnv 0 ``Nat 0 (.succ .zero) natType := by
  refine {
    ord := natCtorEnv_ordered
    hl := by decide
    hsort := rfl
    hlen := rfl
    hT := rfl
    hcs := ?_
    htel := ?_
    hs3 := ?_
    hparams := ?_
    hfields := ?_
    hresult := ?_ }
  · intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · rfl
    · have hc' := List.mem_singleton.1 hc
      subst c
      rfl
  · intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · rfl
    · have hc' := List.mem_singleton.1 hc
      subst c
      rfl
  · intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · rfl
    · have hc' := List.mem_singleton.1 hc
      subst c
      rfl
  · change True
    trivial
  · intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · change True
      trivial
    · have hc' := List.mem_singleton.1 hc
      subst c
      refine ⟨.inl rfl, ?_, trivial⟩
      intro
      rfl
  · intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · change VExpr.sort (.succ .zero) = VExpr.sort (.succ .zero)
      rfl
    · have hc' := List.mem_singleton.1 hc
      subst c
      change VExpr.sort (.succ .zero) = VExpr.sort (.succ .zero)
      rfl

theorem natInfo_tr :
    TrConstVal .safe VEnv.empty natInfo natType.toVConstVal := by
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  exact .sort rfl

theorem natZeroInfo_tr :
    TrConstVal .safe natTypeEnv natZeroInfo natType.ctors[0] := by
  have hNat : natTypeEnv.constants ``Nat = some natType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr natTypeEnv natZeroInfo.levelParams []
      natZeroInfo.type natType.ctors[0].type := by tr_type_expr_tac
  exact hshape.to_trExprS natTypeEnv_ordered trivial
    ⟨.sort (.succ .zero), by type_tac⟩

theorem natSuccInfo_tr :
    TrConstVal .safe natZeroEnv natSuccInfo natType.ctors[1] := by
  have hNat : natZeroEnv.constants ``Nat = some natType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr natZeroEnv natSuccInfo.levelParams []
      natSuccInfo.type natType.ctors[1].type := by
    exact .forallE (.const hNat rfl rfl) (.const hNat rfl rfl)
  exact hshape.to_trExprS natZeroEnv_ordered trivial
    ⟨.sort (.imax (.succ .zero) (.succ .zero)), by
      refine VEnv.HasType.forallE (u := .succ .zero) (v := .succ .zero) ?_ ?_
      · type_tac
      · type_tac⟩

theorem natRecInfo_tr :
    TrConstVal .safe natCtorEnv natRecInfo (inductRecVal natDecl natType) := by
  have hNat : natCtorEnv.constants ``Nat = some natType.toVConstant := rfl
  have hZero :
      natCtorEnv.constants ``Nat.zero = some natType.ctors[0].toVConstant := rfl
  have hSucc :
      natCtorEnv.constants ``Nat.succ = some natType.ctors[1].toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr natCtorEnv natRecInfo.levelParams [] natRecInfo.type
      (inductRecVal natDecl natType).type := by tr_type_expr_tac
  obtain ⟨u, hrec⟩ := natStage3.recConst_wf
  exact hshape.to_trExprS natCtorEnv_ordered trivial ⟨.sort u, hrec⟩

def natTypeMap : ConstMap := ({} : ConstMap).insert ``Nat natInfo
def natZeroMap : ConstMap := natTypeMap.insert ``Nat.zero natZeroInfo
def natCtorMap : ConstMap := natZeroMap.insert ``Nat.succ natSuccInfo
def natMap : ConstMap := natCtorMap.insert ``Nat.rec natRecInfo
def natFinalEnv : VEnv :=
  (VInductDecl.rules 0 ``Nat 0 natType).foldl VEnv.addDefEq natRecEnv

theorem natType_fresh : ({} : ConstMap).find? ``Nat = none := by
  simp [SMap.find?]

theorem natTypeMap_wf : natTypeMap.WF :=
  SMap.WF.empty.insert _ _ natType_fresh

theorem natZero_fresh : natTypeMap.find? ``Nat.zero = none := by
  rw [natTypeMap, SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem natZeroMap_wf : natZeroMap.WF :=
  natTypeMap_wf.insert _ _ natZero_fresh

theorem natSucc_fresh : natZeroMap.find? ``Nat.succ = none := by
  rw [natZeroMap, natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem natCtorMap_wf : natCtorMap.WF :=
  natZeroMap_wf.insert _ _ natSucc_fresh

theorem natRec_fresh : natCtorMap.find? ``Nat.rec = none := by
  rw [natCtorMap, natZeroMap_wf.find?_insert, natZeroMap,
    natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

/-- A concrete `AddInduct` witness whose implementation side consists of the
actual kernel metadata above and whose Theory side is the Stage-3 Nat
transaction. -/
theorem nat_addInduct :
    AddInduct ({} : ConstMap) VEnv.empty natDecl natMap natFinalEnv := by
  refine ⟨{
    generation := natChecked.identityGeneration
    generation_wf :=
      (natChecked.wf_of_decl natDecl_wf).identityGeneration .empty
    typeMap := natTypeMap
    typeEnv := natTypeEnv
    ctorMap := natCtorMap
    ctorEnv := natCtorEnv
    recEnv := natRecEnv
    addType := {
      info := natInfo
      kind_eq := by simp [natInfo, InductConstantKind.Matches]
      tr := natInfo_tr
      map_fresh := by simpa [natType] using natType_fresh
      env_add := rfl
      map_add := rfl }
    addCtors := ?_
    addRec := {
      info := natRecInfo
      kind_eq := by simp [natRecInfo, InductConstantKind.Matches]
      tr := natRecInfo_tr
      map_fresh := by simpa [inductRecVal, natDecl, natType] using natRec_fresh
      env_add := rfl
      map_add := rfl }
    addRules := ⟨rfl⟩ }⟩
  exact .cons {
      info := natZeroInfo
      kind_eq := by simp [natZeroInfo, InductConstantKind.Matches]
      tr := natZeroInfo_tr
      map_fresh := by simpa [natType] using natZero_fresh
      env_add := rfl
      map_add := rfl }
    (.cons {
      info := natSuccInfo
      kind_eq := by simp [natSuccInfo, InductConstantKind.Matches]
      tr := natSuccInfo_tr
      map_fresh := by simpa [natType] using natSucc_fresh
      env_add := rfl
      map_add := rfl } .nil)

/-- The formerly impossible `TrEnv'.induct` branch, instantiated with a real
Lean declaration transaction. -/
theorem nat_trEnv' : TrEnv' .safe natMap false natFinalEnv :=
  .induct nat_addInduct .empty

theorem nat_final_matches_addInduct :
    VEnv.empty.addInduct natDecl = some natFinalEnv :=
  rfl

theorem nat_env_wf : natFinalEnv.WF := nat_trEnv'.wf

theorem nat_aligned : Aligned .safe natMap natFinalEnv := nat_trEnv'.aligned

theorem nat_type_map_lookup : natMap.find? ``Nat = some natInfo := by
  rw [natMap, natCtorMap_wf.find?_insert, natCtorMap,
    natZeroMap_wf.find?_insert, natZeroMap, natTypeMap_wf.find?_insert,
    natTypeMap, SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  rfl

theorem nat_type_env_lookup :
    natFinalEnv.constants ``Nat = some natType.toVConstant := rfl

theorem nat_type_lookup_unique :
    natInfo.name = ``Nat ∧
      TrConstant .safe natFinalEnv natInfo natType.toVConstant :=
  nat_aligned.find?_uniq nat_type_map_lookup nat_type_env_lookup

theorem nat_succ_map_lookup : natMap.find? ``Nat.succ = some natSuccInfo := by
  rw [natMap, natCtorMap_wf.find?_insert, natCtorMap,
    natZeroMap_wf.find?_insert]
  rfl

theorem nat_succ_env_lookup : natFinalEnv.constants ``Nat.succ =
    some natType.ctors[1].toVConstant := rfl

theorem nat_succ_lookup_unique :
    natSuccInfo.name = ``Nat.succ ∧
      TrConstant .safe natFinalEnv natSuccInfo
        natType.ctors[1].toVConstant :=
  nat_aligned.find?_uniq nat_succ_map_lookup nat_succ_env_lookup

theorem nat_rec_map_lookup : natMap.find? ``Nat.rec = some natRecInfo := by
  rw [natMap, natCtorMap_wf.find?_insert]
  rfl

theorem nat_rec_env_lookup : natFinalEnv.constants ``Nat.rec =
    some (VInductDecl.recConst 0 ``Nat 0 natType) := rfl

/-- Lookup uniqueness is tested at the generated recursor, after all iota
rules have been installed. -/
theorem nat_rec_lookup_unique :
    natRecInfo.name = ``Nat.rec ∧
      TrConstant .safe natFinalEnv natRecInfo
        (VInductDecl.recConst 0 ``Nat 0 natType) :=
  nat_aligned.find?_uniq nat_rec_map_lookup nat_rec_env_lookup

/- This closure is transitional for exactly the reasons recorded in the
roadmap: `sorryAx` comes from `TrProj`, and the persistent-map contracts come
from proving concrete `SMap` freshness. The fixture introduces no new axiom. -/
/--
info: 'Lean4Lean.InductiveReplayFixtures.nat_trEnv'' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms nat_trEnv'

/-! ## A value-bearing prefix followed by Nat -/

/-- A dependency-free definition used to ensure value translation survives a
later inductive metadata transaction. -/
def ReplaySeed : Type 1 := Type

def seedKernelDef : DefinitionVal := kernelDefVal% ReplaySeed
def seedInfo : ConstantInfo := .defnInfo seedKernelDef

def seedVal : VDefVal where
  name := ``ReplaySeed
  uvars := 0
  type := .sort (.succ (.succ .zero))
  value := .sort (.succ .zero)

theorem seedInfo_tr : TrDefVal .safe VEnv.empty seedInfo seedVal := by
  refine ⟨⟨⟨by decide, rfl, ?_⟩, rfl⟩, ?_⟩
  · exact .sort rfl
  · exact .sort rfl

theorem seedVal_wf : seedVal.WF VEnv.empty :=
  VEnv.HasType.sort (by decide)

def seedConstEnv := (VEnv.empty.addConst seedVal.name seedVal.toVConstant).get!
def seedEnv := seedConstEnv.addDefEq seedVal.toDefEq
def seedMap : ConstMap := ({} : ConstMap).insert seedVal.name seedInfo

theorem seed_fresh : ({} : ConstMap).find? seedVal.name = none := by
  simp [seedVal, SMap.find?]

theorem seed_trEnv' : TrEnv' .safe seedMap false seedEnv :=
  .defn (ci := seedKernelDef) (ci' := seedVal) seedInfo_tr seed_fresh
    seedVal_wf rfl .empty

theorem seed_map_lookup : seedMap.find? ``ReplaySeed = some seedInfo := by
  rw [seedMap, SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  rfl

theorem seed_le : VEnv.empty ≤ seedEnv :=
  (VEnv.addConst_le (show VEnv.empty.addConst seedVal.name seedVal.toVConstant =
    some seedConstEnv from rfl)).trans VEnv.addDefEq_le

theorem seedEnv_ordered : seedEnv.Ordered := seed_trEnv'.wf.ordered

def seedNatTypeEnv := (seedEnv.addConst natType.name natType.toVConstant).get!
def seedNatZeroEnv :=
  (seedNatTypeEnv.addConst natType.ctors[0].name natType.ctors[0].toVConstant).get!
def seedNatCtorEnv :=
  (seedNatZeroEnv.addConst natType.ctors[1].name natType.ctors[1].toVConstant).get!
def seedNatRecEnv :=
  (seedNatCtorEnv.addConst ``Nat.rec (VInductDecl.recConst 0 ``Nat 0 natType)).get!

theorem natTypeEnv_le_seedNatTypeEnv : natTypeEnv ≤ seedNatTypeEnv :=
  VEnv.LE.addConst (n := natType.name) (ci := natType.toVConstant) seed_le rfl rfl

theorem natZeroEnv_le_seedNatZeroEnv : natZeroEnv ≤ seedNatZeroEnv :=
  VEnv.LE.addConst (n := natType.ctors[0].name)
    (ci := natType.ctors[0].toVConstant) natTypeEnv_le_seedNatTypeEnv rfl rfl

theorem natCtorEnv_le_seedNatCtorEnv : natCtorEnv ≤ seedNatCtorEnv :=
  VEnv.LE.addConst (n := natType.ctors[1].name)
    (ci := natType.ctors[1].toVConstant) natZeroEnv_le_seedNatZeroEnv rfl rfl

theorem seedNatTypeEnv_ordered : seedNatTypeEnv.Ordered := by
  refine .const (n := natType.name) (ci := natType.toVConstant)
    seedEnv_ordered ?_ rfl
  exact ⟨.succ (.succ .zero), VEnv.HasType.sort (by decide)⟩

theorem seedNatZeroEnv_ordered : seedNatZeroEnv.Ordered := by
  refine .const (n := natType.ctors[0].name) (ci := natType.ctors[0].toVConstant)
    seedNatTypeEnv_ordered ?_ rfl
  have hNat : seedNatTypeEnv.constants ``Nat = some natType.toVConstant := rfl
  exact ⟨.succ .zero, by type_tac⟩

theorem seedNatSucc_wf : natType.ctors[1].toVConstant.WF seedNatZeroEnv := by
  have hNat : seedNatZeroEnv.constants ``Nat = some natType.toVConstant := rfl
  refine ⟨.imax (.succ .zero) (.succ .zero), ?_⟩
  refine VEnv.HasType.forallE (u := .succ .zero) (v := .succ .zero) ?_ ?_
  · type_tac
  · type_tac

theorem seedNatCtorEnv_ordered : seedNatCtorEnv.Ordered :=
  .const (n := natType.ctors[1].name) (ci := natType.ctors[1].toVConstant)
    seedNatZeroEnv_ordered seedNatSucc_wf rfl

theorem seedNatInfo_tr :
    TrConstVal .safe seedEnv natInfo natType.toVConstVal :=
  natInfo_tr.mono seed_le

theorem seedNatZeroInfo_tr :
    TrConstVal .safe seedNatTypeEnv natZeroInfo natType.ctors[0] :=
  natZeroInfo_tr.mono natTypeEnv_le_seedNatTypeEnv

theorem seedNatSuccInfo_tr :
    TrConstVal .safe seedNatZeroEnv natSuccInfo natType.ctors[1] :=
  natSuccInfo_tr.mono natZeroEnv_le_seedNatZeroEnv

theorem seedNatRecInfo_tr :
    TrConstVal .safe seedNatCtorEnv natRecInfo (inductRecVal natDecl natType) :=
  natRecInfo_tr.mono natCtorEnv_le_seedNatCtorEnv

def seedNatTypeMap : ConstMap := seedMap.insert ``Nat natInfo
def seedNatZeroMap : ConstMap := seedNatTypeMap.insert ``Nat.zero natZeroInfo
def seedNatCtorMap : ConstMap := seedNatZeroMap.insert ``Nat.succ natSuccInfo
def seedNatMap : ConstMap := seedNatCtorMap.insert ``Nat.rec natRecInfo
def seedNatFinalEnv : VEnv :=
  (VInductDecl.rules 0 ``Nat 0 natType).foldl VEnv.addDefEq seedNatRecEnv

theorem seedMap_wf : seedMap.WF := seed_trEnv'.map_wf

theorem seedNatType_fresh : seedMap.find? ``Nat = none := by
  rw [seedMap, SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [seedVal, SMap.find?]

theorem seedNatTypeMap_wf : seedNatTypeMap.WF :=
  seedMap_wf.insert _ _ seedNatType_fresh

theorem seedNatZero_fresh : seedNatTypeMap.find? ``Nat.zero = none := by
  rw [seedNatTypeMap, seedMap_wf.find?_insert, seedMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [seedVal, SMap.find?]

theorem seedNatZeroMap_wf : seedNatZeroMap.WF :=
  seedNatTypeMap_wf.insert _ _ seedNatZero_fresh

theorem seedNatSucc_fresh : seedNatZeroMap.find? ``Nat.succ = none := by
  rw [seedNatZeroMap, seedNatTypeMap_wf.find?_insert, seedNatTypeMap,
    seedMap_wf.find?_insert, seedMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [seedVal, SMap.find?]

theorem seedNatCtorMap_wf : seedNatCtorMap.WF :=
  seedNatZeroMap_wf.insert _ _ seedNatSucc_fresh

theorem seedNatRec_fresh : seedNatCtorMap.find? ``Nat.rec = none := by
  rw [seedNatCtorMap, seedNatZeroMap_wf.find?_insert, seedNatZeroMap,
    seedNatTypeMap_wf.find?_insert, seedNatTypeMap, seedMap_wf.find?_insert,
    seedMap, SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [seedVal, SMap.find?]

theorem seedNat_addInduct :
    AddInduct seedMap seedEnv natDecl seedNatMap seedNatFinalEnv := by
  refine ⟨{
    generation := natChecked.identityGeneration
    generation_wf :=
      (natChecked.wf_of_decl (natDecl_wf.mono seed_le)).identityGeneration
        seedEnv_ordered
    typeMap := seedNatTypeMap
    typeEnv := seedNatTypeEnv
    ctorMap := seedNatCtorMap
    ctorEnv := seedNatCtorEnv
    recEnv := seedNatRecEnv
    addType := {
      info := natInfo
      kind_eq := by simp [natInfo, InductConstantKind.Matches]
      tr := seedNatInfo_tr
      map_fresh := by simpa [natType] using seedNatType_fresh
      env_add := rfl
      map_add := rfl }
    addCtors := ?_
    addRec := {
      info := natRecInfo
      kind_eq := by simp [natRecInfo, InductConstantKind.Matches]
      tr := seedNatRecInfo_tr
      map_fresh := by simpa [inductRecVal, natDecl, natType] using seedNatRec_fresh
      env_add := rfl
      map_add := rfl }
    addRules := ⟨rfl⟩ }⟩
  exact .cons {
      info := natZeroInfo
      kind_eq := by simp [natZeroInfo, InductConstantKind.Matches]
      tr := seedNatZeroInfo_tr
      map_fresh := by simpa [natType] using seedNatZero_fresh
      env_add := rfl
      map_add := rfl }
    (.cons {
      info := natSuccInfo
      kind_eq := by simp [natSuccInfo, InductConstantKind.Matches]
      tr := seedNatSuccInfo_tr
      map_fresh := by simpa [natType] using seedNatSucc_fresh
      env_add := rfl
      map_add := rfl } .nil)

theorem seedNat_trEnv' : TrEnv' .safe seedNatMap false seedNatFinalEnv :=
  .induct seedNat_addInduct seed_trEnv'

theorem seedNat_seed_lookup : seedNatMap.find? ``ReplaySeed = some seedInfo := by
  rw [seedNatMap, seedNatCtorMap_wf.find?_insert, seedNatCtorMap,
    seedNatZeroMap_wf.find?_insert, seedNatZeroMap,
    seedNatTypeMap_wf.find?_insert, seedNatTypeMap, seedMap_wf.find?_insert]
  simpa [seedVal] using seed_map_lookup

/-- A concrete regression for the formerly impossible `TrEnv'.of_value`
inductive branch: the value was inserted before Nat, so this theorem must pull
its lookup back through every Nat metadata insertion. -/
theorem seed_after_nat_of_value :
    TrExpr seedNatFinalEnv seedInfo.levelParams [] seedKernelDef.value
      (.const seedInfo.name (VLevel.params seedInfo.levelParams.length)) :=
  seedNat_trEnv'.of_value (name := ``ReplaySeed) (ci := seedInfo)
    (v := seedKernelDef.value) seedNat_seed_lookup (by decide) rfl

/--
info: 'Lean4Lean.InductiveReplayFixtures.seed_after_nat_of_value' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms seed_after_nat_of_value

/-! ## Eq -/

/- `Eq` exercises parameters, a genuine index, Prop-valued elimination, and
the kernel/generated recursor universe permutation. -/
def eqInfo : ConstantInfo := kernelInductInfo% Eq
def eqReflInfo : ConstantInfo := kernelCtorInfo% Eq.refl
def eqRecInfo : ConstantInfo := kernelRecInfo% Eq.rec
def eqReflKernelRuleRhs : VExpr := kernelRecRuleRhs% Eq.rec 0

example : eqReflKernelRuleRhs =
    eqChecked.identityGeneration.generatedRules[0].rhs := rfl

def eqTypeEnv := (VEnv.empty.addConst eqType.name eqType.toVConstant).get!
def eqCtorEnv :=
  (eqTypeEnv.addConst eqType.ctors[0].name eqType.ctors[0].toVConstant).get!
def eqRecEnv :=
  (eqCtorEnv.addConst ``Eq.rec (VInductDecl.recConst 1 ``Eq 2 eqType)).get!

theorem eqType_wf : eqType.toVConstant.WF VEnv.empty := by
  refine ⟨.imax (.succ (.param 0))
    (.imax (.param 0) (.imax (.param 0) (.succ .zero))), ?_⟩
  refine VEnv.HasType.forallE
    (u := .succ (.param 0))
    (v := .imax (.param 0) (.imax (.param 0) (.succ .zero))) ?_ ?_
  · exact VEnv.HasType.sort (by decide)
  · refine VEnv.HasType.forallE
      (u := .param 0) (v := .imax (.param 0) (.succ .zero)) ?_ ?_
    · type_tac
    · refine VEnv.HasType.forallE
        (u := .param 0) (v := .succ .zero) ?_ ?_
      · type_tac
      · exact VEnv.HasType.sort (by decide)

theorem eqTypeEnv_ordered : eqTypeEnv.Ordered :=
  .const .empty eqType_wf rfl

theorem eqDecl_wf : eqDecl.WF VEnv.empty := by
  refine ⟨rfl, ?_⟩
  intro ty hty
  have hty' : ty = eqType := List.mem_singleton.1 (by simpa [eqDecl] using hty)
  subst ty
  refine ⟨?_, ?_⟩
  · change VEnv.empty.OnTel 1 []
      [.sort (.param 0), .bvar 0, .bvar 1]
    exact ⟨⟨.succ (.param 0), VEnv.HasType.sort (by decide)⟩,
      ⟨⟨.param 0, by type_tac⟩, ⟨⟨.param 0, by type_tac⟩, trivial⟩⟩⟩
  · intro c hc
    have hc' := List.mem_singleton.1 hc
    subst c
    constructor
    · change True
      trivial
    · refine ⟨_, _, rfl, ?_, rfl⟩
      type_tac

theorem eqRefl_wf : eqType.ctors[0].toVConstant.WF eqTypeEnv := by
  have hblock := eqDecl_wf.2 eqType (by simp [eqDecl])
  have hctor := hblock.2 eqType.ctors[0] (by simp)
  have hle : VEnv.empty ≤ eqTypeEnv := VEnv.addConst_le rfl
  have S0 : VInductDecl.Stage3Env eqTypeEnv 1 ``Eq 2 .zero
      { eqType with ctors := [] } := {
    ord := eqTypeEnv_ordered
    hl := by decide
    hsort := rfl
    hlen := rfl
    hT := rfl
    hcs := by simp
    htel := by simp
    hs3 := by simp
    hparams := hblock.1.mono hle
    hfields := by simp
    hresult := by simp }
  exact S0.ctorType_isType' rfl rfl
    (VInductDecl.fieldsWF_mono hle hctor.1) (hctor.2.mono hle)

theorem eqCtorEnv_ordered : eqCtorEnv.Ordered :=
  .const (n := eqType.ctors[0].name) (ci := eqType.ctors[0].toVConstant)
    eqTypeEnv_ordered eqRefl_wf rfl

theorem eqStage3 :
    VInductDecl.Stage3Env eqCtorEnv 1 ``Eq 2 .zero eqType := by
  have hblock := eqDecl_wf.2 eqType (by simp [eqDecl])
  have hctor := hblock.2 eqType.ctors[0] (by simp)
  have h0 : VEnv.empty ≤ eqTypeEnv :=
    VEnv.addConst_le (show VEnv.empty.addConst eqType.name eqType.toVConstant =
      some eqTypeEnv from rfl)
  have h1 : eqTypeEnv ≤ eqCtorEnv :=
    VEnv.addConst_le (show eqTypeEnv.addConst eqType.ctors[0].name
      eqType.ctors[0].toVConstant = some eqCtorEnv from rfl)
  have hle : VEnv.empty ≤ eqCtorEnv := h0.trans h1
  refine {
    ord := eqCtorEnv_ordered
    hl := by decide
    hsort := rfl
    hlen := rfl
    hT := rfl
    hcs := by
      intro c hc
      have hc' := List.mem_singleton.1 hc
      subst c
      rfl
    htel := by
      intro c hc
      have hc' := List.mem_singleton.1 hc
      subst c
      rfl
    hs3 := by
      intro c hc
      have hc' := List.mem_singleton.1 hc
      subst c
      rfl
    hparams := hblock.1.mono hle
    hfields := by
      intro c hc
      have hc' := List.mem_singleton.1 hc
      subst c
      exact VInductDecl.fieldsWF_mono hle hctor.1
    hresult := by
      intro c hc
      have hc' := List.mem_singleton.1 hc
      subst c
      exact hctor.2.mono hle }

theorem eqInfo_tr :
    TrConstVal .safe VEnv.empty eqInfo eqType.toVConstVal := by
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr VEnv.empty eqInfo.levelParams [] eqInfo.type
      eqType.type := by tr_type_expr_tac
  obtain ⟨u, htype⟩ := eqType_wf
  exact hshape.to_trExprS .empty trivial ⟨.sort u, htype⟩

theorem eqReflInfo_tr :
    TrConstVal .safe eqTypeEnv eqReflInfo eqType.ctors[0] := by
  have hEq : eqTypeEnv.constants ``Eq = some eqType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr eqTypeEnv eqReflInfo.levelParams [] eqReflInfo.type
      eqType.ctors[0].type := by tr_type_expr_tac
  obtain ⟨u, htype⟩ := eqRefl_wf
  exact hshape.to_trExprS eqTypeEnv_ordered trivial ⟨.sort u, htype⟩

theorem eqRecInfo_tr :
    TrConstVal .safe eqCtorEnv eqRecInfo (inductRecVal eqDecl eqType) := by
  have hEq : eqCtorEnv.constants ``Eq = some eqType.toVConstant := rfl
  have hRefl : eqCtorEnv.constants ``Eq.refl =
      some eqType.ctors[0].toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr eqCtorEnv eqRecInfo.levelParams [] eqRecInfo.type
      (inductRecVal eqDecl eqType).type := by tr_type_expr_tac
  obtain ⟨u, hrec⟩ := eqStage3.recConst_wf
  exact hshape.to_trExprS eqCtorEnv_ordered trivial ⟨.sort u, hrec⟩

def eqTypeMap : ConstMap := ({} : ConstMap).insert ``Eq eqInfo
def eqCtorMap : ConstMap := eqTypeMap.insert ``Eq.refl eqReflInfo
def eqMap : ConstMap := eqCtorMap.insert ``Eq.rec eqRecInfo
def eqFinalEnv : VEnv :=
  (VInductDecl.rules 1 ``Eq 2 eqType).foldl VEnv.addDefEq eqRecEnv

theorem eqType_fresh : ({} : ConstMap).find? ``Eq = none := by
  simp [SMap.find?]

theorem eqTypeMap_wf : eqTypeMap.WF :=
  SMap.WF.empty.insert _ _ eqType_fresh

theorem eqRefl_fresh : eqTypeMap.find? ``Eq.refl = none := by
  rw [eqTypeMap, SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem eqCtorMap_wf : eqCtorMap.WF :=
  eqTypeMap_wf.insert _ _ eqRefl_fresh

theorem eqRec_fresh : eqCtorMap.find? ``Eq.rec = none := by
  rw [eqCtorMap, eqTypeMap_wf.find?_insert, eqTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem eq_addInduct :
    AddInduct ({} : ConstMap) VEnv.empty eqDecl eqMap eqFinalEnv := by
  refine ⟨{
    generation := eqChecked.identityGeneration
    generation_wf :=
      (eqChecked.wf_of_decl eqDecl_wf).identityGeneration .empty
    typeMap := eqTypeMap
    typeEnv := eqTypeEnv
    ctorMap := eqCtorMap
    ctorEnv := eqCtorEnv
    recEnv := eqRecEnv
    addType := {
      info := eqInfo
      kind_eq := by simp [eqInfo, InductConstantKind.Matches]
      tr := eqInfo_tr
      map_fresh := by simpa [eqType] using eqType_fresh
      env_add := rfl
      map_add := rfl }
    addCtors := ?_
    addRec := {
      info := eqRecInfo
      kind_eq := by simp [eqRecInfo, InductConstantKind.Matches]
      tr := eqRecInfo_tr
      map_fresh := by simpa [inductRecVal, eqDecl, eqType] using eqRec_fresh
      env_add := rfl
      map_add := rfl }
    addRules := ⟨rfl⟩ }⟩
  exact .cons {
    info := eqReflInfo
    kind_eq := by simp [eqReflInfo, InductConstantKind.Matches]
    tr := eqReflInfo_tr
    map_fresh := by simpa [eqType] using eqRefl_fresh
    env_add := rfl
    map_add := rfl } .nil

/-- Replay actual kernel `Eq` metadata through the formerly empty inductive
environment branch. -/
theorem eq_trEnv' : TrEnv' .safe eqMap false eqFinalEnv :=
  .induct eq_addInduct .empty

theorem eq_final_matches_addInduct :
    VEnv.empty.addInduct eqDecl = some eqFinalEnv :=
  rfl

theorem eq_env_wf : eqFinalEnv.WF := eq_trEnv'.wf

theorem eq_aligned : Aligned .safe eqMap eqFinalEnv := eq_trEnv'.aligned

theorem eq_type_map_lookup : eqMap.find? ``Eq = some eqInfo := by
  rw [eqMap, eqCtorMap_wf.find?_insert, eqCtorMap,
    eqTypeMap_wf.find?_insert, eqTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  rfl

theorem eq_type_env_lookup :
    eqFinalEnv.constants ``Eq = some eqType.toVConstant := rfl

theorem eq_type_lookup_unique :
    eqInfo.name = ``Eq ∧
      TrConstant .safe eqFinalEnv eqInfo eqType.toVConstant :=
  eq_aligned.find?_uniq eq_type_map_lookup eq_type_env_lookup

theorem eq_refl_map_lookup : eqMap.find? ``Eq.refl = some eqReflInfo := by
  rw [eqMap, eqCtorMap_wf.find?_insert, eqCtorMap,
    eqTypeMap_wf.find?_insert]
  rfl

theorem eq_refl_env_lookup : eqFinalEnv.constants ``Eq.refl =
    some eqType.ctors[0].toVConstant := rfl

theorem eq_refl_lookup_unique :
    eqReflInfo.name = ``Eq.refl ∧
      TrConstant .safe eqFinalEnv eqReflInfo
        eqType.ctors[0].toVConstant :=
  eq_aligned.find?_uniq eq_refl_map_lookup eq_refl_env_lookup

theorem eq_rec_map_lookup : eqMap.find? ``Eq.rec = some eqRecInfo := by
  rw [eqMap, eqCtorMap_wf.find?_insert]
  rfl

theorem eq_rec_env_lookup : eqFinalEnv.constants ``Eq.rec =
    some (VInductDecl.recConst 1 ``Eq 2 eqType) := rfl

theorem eq_rec_lookup_unique :
    eqRecInfo.name = ``Eq.rec ∧
      TrConstant .safe eqFinalEnv eqRecInfo
        (VInductDecl.recConst 1 ``Eq 2 eqType) :=
  eq_aligned.find?_uniq eq_rec_map_lookup eq_rec_env_lookup

/--
info: 'Lean4Lean.InductiveReplayFixtures.eq_trEnv'' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms eq_trEnv'

/-! ## IndexedVec over the replayed Nat prefix -/

/- The fixture spells its changing index as `Nat.succ n` (and its base as
`Nat.zero`) so its kernel metadata has exactly the semantically relevant Nat
dependency prefix, rather than the unrelated `OfNat`/`HAdd` instance
implementation generated by notation. The declaration and every metadata
record below are still quoted from and checked against the real kernel
objects. -/
def indexedVecInfo : ConstantInfo := kernelInductInfo% IndexedVec
def indexedVecNilInfo : ConstantInfo := kernelCtorInfo% IndexedVec.nil
def indexedVecConsInfo : ConstantInfo := kernelCtorInfo% IndexedVec.cons
def indexedVecRecInfo : ConstantInfo := kernelRecInfo% IndexedVec.rec
def indexedVecNilKernelRuleRhs : VExpr :=
  kernelRecRuleRhs% IndexedVec.rec 0
def indexedVecConsKernelRuleRhs : VExpr :=
  kernelRecRuleRhs% IndexedVec.rec 1

example : indexedVecNilKernelRuleRhs =
    indexedVecChecked.identityGeneration.generatedRules[0].rhs := rfl
example : indexedVecConsKernelRuleRhs =
    indexedVecChecked.identityGeneration.generatedRules[1].rhs := rfl

def indexedVecTypeEnv :=
  (natFinalEnv.addConst indexedVecType.name indexedVecType.toVConstant).get!
def indexedVecNilEnv :=
  (indexedVecTypeEnv.addConst indexedVecType.ctors[0].name
    indexedVecType.ctors[0].toVConstant).get!
def indexedVecCtorEnv :=
  (indexedVecNilEnv.addConst indexedVecType.ctors[1].name
    indexedVecType.ctors[1].toVConstant).get!
def indexedVecRecEnv :=
  (indexedVecCtorEnv.addConst ``IndexedVec.rec
    (VInductDecl.recConst 1 ``IndexedVec 1 indexedVecType)).get!
theorem indexedVecType_wf : indexedVecType.toVConstant.WF natFinalEnv := by
  have hNat : natFinalEnv.constants ``Nat = some natType.toVConstant := rfl
  refine ⟨.imax (.succ (.succ (.param 0)))
    (.imax (.succ .zero) (.succ (.succ (.param 0)))), ?_⟩
  refine VEnv.HasType.forallE
    (u := .succ (.succ (.param 0)))
    (v := .imax (.succ .zero) (.succ (.succ (.param 0)))) ?_ ?_
  · exact VEnv.HasType.sort (by decide)
  · refine VEnv.HasType.forallE
      (u := .succ .zero) (v := .succ (.succ (.param 0))) ?_ ?_
    · type_tac
    · exact VEnv.HasType.sort (by decide)

theorem indexedVecDecl_wf : indexedVecDecl.WF natFinalEnv := by
  refine ⟨rfl, ?_⟩
  intro ty hty
  have hty' : ty = indexedVecType :=
    List.mem_singleton.1 (by simpa [indexedVecDecl] using hty)
  subst ty
  refine ⟨?_, ?_⟩
  · change natFinalEnv.OnTel 1 []
      [.sort (.succ (.param 0)), .const ``Nat []]
    have hNat : natFinalEnv.constants ``Nat = some natType.toVConstant := rfl
    exact ⟨⟨.succ (.succ (.param 0)), VEnv.HasType.sort (by decide)⟩,
      ⟨⟨.succ .zero, by type_tac⟩, trivial⟩⟩
  · intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · constructor
      · change True
        trivial
      · change natFinalEnv.SpineWF 1
          [.sort (.succ (.param 0))]
          (.forallE (.const ``Nat []) (.sort (.succ (.param 0))))
          [.const ``Nat.zero []] (.sort (.succ (.param 0)))
        have hNat : natFinalEnv.constants ``Nat = some natType.toVConstant := rfl
        have hZero : natFinalEnv.constants ``Nat.zero =
            some natType.ctors[0].toVConstant := rfl
        exact ⟨.const ``Nat [], .sort (.succ (.param 0)), rfl,
          (by type_tac), rfl⟩
    · have hc' := List.mem_singleton.1 hc
      subst c
      constructor
      · change VInductDecl.fieldsWF 1 ``IndexedVec 1 natFinalEnv
          (VLevel.succ (VLevel.param 0)) [VExpr.const ``Nat []]
          [VExpr.sort (VLevel.succ (VLevel.param 0))] 0
          [VExpr.const ``Nat [], VExpr.bvar 1,
            VExpr.app (VExpr.app (VExpr.const ``IndexedVec [VLevel.param 0])
              (VExpr.bvar 2)) (VExpr.bvar 1)]
        have hNat : natFinalEnv.constants ``Nat = some natType.toVConstant := rfl
        constructor
        · exact .inr (.inr ⟨rfl, .succ .zero, (by type_tac),
            .inr (VLevel.succ_le_succ VLevel.zero_le)⟩)
        constructor
        · intro h
          contradiction
        constructor
        · exact .inr (.inr ⟨rfl, .succ (.param 0), (by type_tac),
            .inr (VLevel.le_refl _)⟩)
        constructor
        · intro h
          contradiction
        constructor
        · exact .inl rfl
        constructor
        · intro _
          exact ⟨.const ``Nat [], .sort (.succ (.param 0)), rfl,
            (by type_tac), rfl⟩
        · trivial
      · change natFinalEnv.SpineWF 1
          [VExpr.app (VExpr.app (VExpr.const ``IndexedVec [VLevel.param 0])
              (VExpr.bvar 2)) (VExpr.bvar 1),
            VExpr.bvar 1, VExpr.const ``Nat [],
            VExpr.sort (VLevel.succ (VLevel.param 0))]
          (VExpr.forallE (VExpr.const ``Nat [])
            (VExpr.sort (VLevel.succ (VLevel.param 0))))
          [VExpr.app (VExpr.const ``Nat.succ []) (VExpr.bvar 2)]
          (VExpr.sort (VLevel.succ (VLevel.param 0)))
        have hNat : natFinalEnv.constants ``Nat = some natType.toVConstant := rfl
        have hSucc : natFinalEnv.constants ``Nat.succ =
            some natType.ctors[1].toVConstant := rfl
        exact ⟨.const ``Nat [], .sort (.succ (.param 0)), rfl,
          (by type_tac), rfl⟩

theorem natFinalEnv_le_indexedVecTypeEnv : natFinalEnv ≤ indexedVecTypeEnv :=
  VEnv.addConst_le (show natFinalEnv.addConst indexedVecType.name
    indexedVecType.toVConstant = some indexedVecTypeEnv from rfl)

theorem indexedVecTypeEnv_le_indexedVecNilEnv :
    indexedVecTypeEnv ≤ indexedVecNilEnv :=
  VEnv.addConst_le (show indexedVecTypeEnv.addConst
    indexedVecType.ctors[0].name indexedVecType.ctors[0].toVConstant =
      some indexedVecNilEnv from rfl)

theorem indexedVecNilEnv_le_indexedVecCtorEnv :
    indexedVecNilEnv ≤ indexedVecCtorEnv :=
  VEnv.addConst_le (show indexedVecNilEnv.addConst
    indexedVecType.ctors[1].name indexedVecType.ctors[1].toVConstant =
      some indexedVecCtorEnv from rfl)

theorem indexedVecTypeEnv_ordered : indexedVecTypeEnv.Ordered :=
  .const (n := indexedVecType.name) (ci := indexedVecType.toVConstant)
    nat_env_wf.ordered indexedVecType_wf rfl

theorem indexedVecNil_wf :
    indexedVecType.ctors[0].toVConstant.WF indexedVecTypeEnv := by
  have hblock := indexedVecDecl_wf.2 indexedVecType
    (by simp [indexedVecDecl])
  have hctor := hblock.2 indexedVecType.ctors[0] (by simp)
  have hle : natFinalEnv ≤ indexedVecTypeEnv :=
    natFinalEnv_le_indexedVecTypeEnv
  have S0 : VInductDecl.Stage3Env indexedVecTypeEnv 1 ``IndexedVec 1
      (.succ (.param 0)) { indexedVecType with ctors := [] } := {
    ord := indexedVecTypeEnv_ordered
    hl := by decide
    hsort := rfl
    hlen := rfl
    hT := rfl
    hcs := by simp
    htel := by simp
    hs3 := by simp
    hparams := hblock.1.mono hle
    hfields := by simp
    hresult := by simp }
  exact S0.ctorType_isType' rfl rfl
    (VInductDecl.fieldsWF_mono hle hctor.1) (hctor.2.mono hle)

theorem indexedVecNilEnv_ordered : indexedVecNilEnv.Ordered :=
  .const (n := indexedVecType.ctors[0].name)
    (ci := indexedVecType.ctors[0].toVConstant)
    indexedVecTypeEnv_ordered indexedVecNil_wf rfl

theorem indexedVecCons_wf :
    indexedVecType.ctors[1].toVConstant.WF indexedVecNilEnv := by
  have hblock := indexedVecDecl_wf.2 indexedVecType
    (by simp [indexedVecDecl])
  have hnil := hblock.2 indexedVecType.ctors[0] (by simp)
  have hcons := hblock.2 indexedVecType.ctors[1] (by simp)
  have h0 : natFinalEnv ≤ indexedVecTypeEnv :=
    natFinalEnv_le_indexedVecTypeEnv
  have h1 : indexedVecTypeEnv ≤ indexedVecNilEnv :=
    indexedVecTypeEnv_le_indexedVecNilEnv
  have hle : natFinalEnv ≤ indexedVecNilEnv := h0.trans h1
  have S1 : VInductDecl.Stage3Env indexedVecNilEnv 1 ``IndexedVec 1
      (.succ (.param 0))
      { indexedVecType with ctors := [indexedVecType.ctors[0]] } := {
    ord := indexedVecNilEnv_ordered
    hl := by decide
    hsort := rfl
    hlen := rfl
    hT := rfl
    hcs := by
      intro c hc
      have hc' := List.mem_singleton.1 hc
      subst c
      rfl
    htel := by
      intro c hc
      have hc' := List.mem_singleton.1 hc
      subst c
      rfl
    hs3 := by
      intro c hc
      have hc' := List.mem_singleton.1 hc
      subst c
      rfl
    hparams := hblock.1.mono hle
    hfields := by
      intro c hc
      have hc' := List.mem_singleton.1 hc
      subst c
      exact VInductDecl.fieldsWF_mono hle hnil.1
    hresult := by
      intro c hc
      have hc' := List.mem_singleton.1 hc
      subst c
      exact hnil.2.mono hle }
  exact S1.ctorType_isType' rfl rfl
    (VInductDecl.fieldsWF_mono hle hcons.1) (hcons.2.mono hle)

theorem indexedVecCtorEnv_ordered : indexedVecCtorEnv.Ordered :=
  .const (n := indexedVecType.ctors[1].name)
    (ci := indexedVecType.ctors[1].toVConstant)
    indexedVecNilEnv_ordered indexedVecCons_wf rfl

theorem indexedVecStage3 :
    VInductDecl.Stage3Env indexedVecCtorEnv 1 ``IndexedVec 1
      (.succ (.param 0)) indexedVecType := by
  have hblock := indexedVecDecl_wf.2 indexedVecType
    (by simp [indexedVecDecl])
  have h0 : natFinalEnv ≤ indexedVecTypeEnv :=
    natFinalEnv_le_indexedVecTypeEnv
  have h1 : indexedVecTypeEnv ≤ indexedVecNilEnv :=
    indexedVecTypeEnv_le_indexedVecNilEnv
  have h2 : indexedVecNilEnv ≤ indexedVecCtorEnv :=
    indexedVecNilEnv_le_indexedVecCtorEnv
  have hle : natFinalEnv ≤ indexedVecCtorEnv := (h0.trans h1).trans h2
  refine {
    ord := indexedVecCtorEnv_ordered
    hl := by decide
    hsort := rfl
    hlen := rfl
    hT := rfl
    hcs := ?_
    htel := ?_
    hs3 := ?_
    hparams := hblock.1.mono hle
    hfields := ?_
    hresult := ?_ }
  · intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · rfl
    · have hc' := List.mem_singleton.1 hc
      subst c
      rfl
  · intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · rfl
    · have hc' := List.mem_singleton.1 hc
      subst c
      rfl
  · intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · rfl
    · have hc' := List.mem_singleton.1 hc
      subst c
      rfl
  · intro c hc
    exact VInductDecl.fieldsWF_mono hle (hblock.2 c hc).1
  · intro c hc
    exact (hblock.2 c hc).2.mono hle

theorem indexedVecInfo_tr :
    TrConstVal .safe natFinalEnv indexedVecInfo indexedVecType.toVConstVal := by
  have hNat : natFinalEnv.constants ``Nat = some natType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr natFinalEnv indexedVecInfo.levelParams []
      indexedVecInfo.type indexedVecType.type := by tr_type_expr_tac
  obtain ⟨u, htype⟩ := indexedVecType_wf
  exact hshape.to_trExprS nat_env_wf.ordered trivial ⟨.sort u, htype⟩

theorem indexedVecNilInfo_tr :
    TrConstVal .safe indexedVecTypeEnv indexedVecNilInfo
      indexedVecType.ctors[0] := by
  have hNat : indexedVecTypeEnv.constants ``Nat = some natType.toVConstant := rfl
  have hZero : indexedVecTypeEnv.constants ``Nat.zero =
      some natType.ctors[0].toVConstant := rfl
  have hVec : indexedVecTypeEnv.constants ``IndexedVec =
      some indexedVecType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr indexedVecTypeEnv indexedVecNilInfo.levelParams []
      indexedVecNilInfo.type indexedVecType.ctors[0].type := by
    tr_type_expr_tac
  obtain ⟨u, htype⟩ := indexedVecNil_wf
  exact hshape.to_trExprS indexedVecTypeEnv_ordered trivial ⟨.sort u, htype⟩

theorem indexedVecConsInfo_tr :
    TrConstVal .safe indexedVecNilEnv indexedVecConsInfo
      indexedVecType.ctors[1] := by
  have hNat : indexedVecNilEnv.constants ``Nat = some natType.toVConstant := rfl
  have hSucc : indexedVecNilEnv.constants ``Nat.succ =
      some natType.ctors[1].toVConstant := rfl
  have hVec : indexedVecNilEnv.constants ``IndexedVec =
      some indexedVecType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr indexedVecNilEnv indexedVecConsInfo.levelParams []
      indexedVecConsInfo.type indexedVecType.ctors[1].type := by
    tr_type_expr_tac
  obtain ⟨u, htype⟩ := indexedVecCons_wf
  exact hshape.to_trExprS indexedVecNilEnv_ordered trivial ⟨.sort u, htype⟩

theorem indexedVecRecInfo_tr :
    TrConstVal .safe indexedVecCtorEnv indexedVecRecInfo
      (inductRecVal indexedVecDecl indexedVecType) := by
  have hNat : indexedVecCtorEnv.constants ``Nat = some natType.toVConstant := rfl
  have hZero : indexedVecCtorEnv.constants ``Nat.zero =
      some natType.ctors[0].toVConstant := rfl
  have hSucc : indexedVecCtorEnv.constants ``Nat.succ =
      some natType.ctors[1].toVConstant := rfl
  have hVec : indexedVecCtorEnv.constants ``IndexedVec =
      some indexedVecType.toVConstant := rfl
  have hNil : indexedVecCtorEnv.constants ``IndexedVec.nil =
      some indexedVecType.ctors[0].toVConstant := rfl
  have hCons : indexedVecCtorEnv.constants ``IndexedVec.cons =
      some indexedVecType.ctors[1].toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr indexedVecCtorEnv indexedVecRecInfo.levelParams []
      indexedVecRecInfo.type
      (inductRecVal indexedVecDecl indexedVecType).type := by
    tr_type_expr_tac
  obtain ⟨u, hrec⟩ := indexedVecStage3.recConst_wf
  exact hshape.to_trExprS indexedVecCtorEnv_ordered trivial ⟨.sort u, hrec⟩

def indexedVecTypeMap : ConstMap := natMap.insert ``IndexedVec indexedVecInfo
def indexedVecNilMap : ConstMap :=
  indexedVecTypeMap.insert ``IndexedVec.nil indexedVecNilInfo
def indexedVecCtorMap : ConstMap :=
  indexedVecNilMap.insert ``IndexedVec.cons indexedVecConsInfo
def indexedVecMap : ConstMap :=
  indexedVecCtorMap.insert ``IndexedVec.rec indexedVecRecInfo
def indexedVecFinalEnv : VEnv :=
  (VInductDecl.rules 1 ``IndexedVec 1 indexedVecType).foldl
    VEnv.addDefEq indexedVecRecEnv

theorem natMap_wf : natMap.WF := nat_trEnv'.map_wf

theorem indexedVecType_fresh : natMap.find? ``IndexedVec = none := by
  rw [natMap, natCtorMap_wf.find?_insert, natCtorMap,
    natZeroMap_wf.find?_insert, natZeroMap,
    natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem indexedVecTypeMap_wf : indexedVecTypeMap.WF :=
  natMap_wf.insert _ _ indexedVecType_fresh

theorem indexedVecNil_fresh :
    indexedVecTypeMap.find? ``IndexedVec.nil = none := by
  rw [indexedVecTypeMap, natMap_wf.find?_insert, natMap,
    natCtorMap_wf.find?_insert, natCtorMap,
    natZeroMap_wf.find?_insert, natZeroMap,
    natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem indexedVecNilMap_wf : indexedVecNilMap.WF :=
  indexedVecTypeMap_wf.insert _ _ indexedVecNil_fresh

theorem indexedVecCons_fresh :
    indexedVecNilMap.find? ``IndexedVec.cons = none := by
  rw [indexedVecNilMap, indexedVecTypeMap_wf.find?_insert,
    indexedVecTypeMap, natMap_wf.find?_insert, natMap,
    natCtorMap_wf.find?_insert, natCtorMap,
    natZeroMap_wf.find?_insert, natZeroMap,
    natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem indexedVecCtorMap_wf : indexedVecCtorMap.WF :=
  indexedVecNilMap_wf.insert _ _ indexedVecCons_fresh

theorem indexedVecRec_fresh :
    indexedVecCtorMap.find? ``IndexedVec.rec = none := by
  rw [indexedVecCtorMap, indexedVecNilMap_wf.find?_insert,
    indexedVecNilMap, indexedVecTypeMap_wf.find?_insert,
    indexedVecTypeMap, natMap_wf.find?_insert, natMap,
    natCtorMap_wf.find?_insert, natCtorMap,
    natZeroMap_wf.find?_insert, natZeroMap,
    natTypeMap_wf.find?_insert, natTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem indexedVec_addInduct :
    AddInduct natMap natFinalEnv indexedVecDecl indexedVecMap
      indexedVecFinalEnv := by
  refine ⟨{
    generation := indexedVecChecked.identityGeneration
    generation_wf :=
      (indexedVecChecked.wf_of_decl indexedVecDecl_wf).identityGeneration
        nat_env_wf.ordered
    typeMap := indexedVecTypeMap
    typeEnv := indexedVecTypeEnv
    ctorMap := indexedVecCtorMap
    ctorEnv := indexedVecCtorEnv
    recEnv := indexedVecRecEnv
    addType := {
      info := indexedVecInfo
      kind_eq := by simp [indexedVecInfo, InductConstantKind.Matches]
      tr := indexedVecInfo_tr
      map_fresh := by simpa [indexedVecType] using indexedVecType_fresh
      env_add := rfl
      map_add := rfl }
    addCtors := ?_
    addRec := {
      info := indexedVecRecInfo
      kind_eq := by simp [indexedVecRecInfo, InductConstantKind.Matches]
      tr := indexedVecRecInfo_tr
      map_fresh := by
        simpa [inductRecVal, indexedVecDecl, indexedVecType] using
          indexedVecRec_fresh
      env_add := rfl
      map_add := rfl }
    addRules := ⟨rfl⟩ }⟩
  exact .cons {
      info := indexedVecNilInfo
      kind_eq := by simp [indexedVecNilInfo, InductConstantKind.Matches]
      tr := indexedVecNilInfo_tr
      map_fresh := by simpa [indexedVecType] using indexedVecNil_fresh
      env_add := rfl
      map_add := rfl }
    (.cons {
      info := indexedVecConsInfo
      kind_eq := by simp [indexedVecConsInfo, InductConstantKind.Matches]
      tr := indexedVecConsInfo_tr
      map_fresh := by simpa [indexedVecType] using indexedVecCons_fresh
      env_add := rfl
      map_add := rfl } .nil)

theorem indexedVec_trEnv' :
    TrEnv' .safe indexedVecMap false indexedVecFinalEnv :=
  .induct indexedVec_addInduct nat_trEnv'

theorem indexedVec_final_matches_addInduct :
    natFinalEnv.addInduct indexedVecDecl = some indexedVecFinalEnv :=
  rfl

theorem indexedVec_env_wf : indexedVecFinalEnv.WF := indexedVec_trEnv'.wf

theorem indexedVec_aligned :
    Aligned .safe indexedVecMap indexedVecFinalEnv :=
  indexedVec_trEnv'.aligned

theorem indexedVec_type_map_lookup :
    indexedVecMap.find? ``IndexedVec = some indexedVecInfo := by
  rw [indexedVecMap, indexedVecCtorMap_wf.find?_insert, indexedVecCtorMap,
    indexedVecNilMap_wf.find?_insert, indexedVecNilMap,
    indexedVecTypeMap_wf.find?_insert, indexedVecTypeMap,
    natMap_wf.find?_insert]
  rfl

theorem indexedVec_type_env_lookup :
    indexedVecFinalEnv.constants ``IndexedVec =
      some indexedVecType.toVConstant := rfl

theorem indexedVec_type_lookup_unique :
    indexedVecInfo.name = ``IndexedVec ∧
      TrConstant .safe indexedVecFinalEnv indexedVecInfo
        indexedVecType.toVConstant :=
  indexedVec_aligned.find?_uniq indexedVec_type_map_lookup
    indexedVec_type_env_lookup

theorem indexedVec_cons_map_lookup :
    indexedVecMap.find? ``IndexedVec.cons = some indexedVecConsInfo := by
  rw [indexedVecMap, indexedVecCtorMap_wf.find?_insert, indexedVecCtorMap,
    indexedVecNilMap_wf.find?_insert]
  rfl

theorem indexedVec_cons_env_lookup :
    indexedVecFinalEnv.constants ``IndexedVec.cons =
      some indexedVecType.ctors[1].toVConstant := rfl

theorem indexedVec_cons_lookup_unique :
    indexedVecConsInfo.name = ``IndexedVec.cons ∧
      TrConstant .safe indexedVecFinalEnv indexedVecConsInfo
        indexedVecType.ctors[1].toVConstant :=
  indexedVec_aligned.find?_uniq indexedVec_cons_map_lookup
    indexedVec_cons_env_lookup

theorem indexedVec_rec_map_lookup :
    indexedVecMap.find? ``IndexedVec.rec = some indexedVecRecInfo := by
  rw [indexedVecMap, indexedVecCtorMap_wf.find?_insert]
  rfl

theorem indexedVec_rec_env_lookup :
    indexedVecFinalEnv.constants ``IndexedVec.rec =
      some (VInductDecl.recConst 1 ``IndexedVec 1 indexedVecType) := rfl

theorem indexedVec_rec_lookup_unique :
    indexedVecRecInfo.name = ``IndexedVec.rec ∧
      TrConstant .safe indexedVecFinalEnv indexedVecRecInfo
        (VInductDecl.recConst 1 ``IndexedVec 1 indexedVecType) :=
  indexedVec_aligned.find?_uniq indexedVec_rec_map_lookup
    indexedVec_rec_env_lookup

/--
info: 'Lean4Lean.InductiveReplayFixtures.indexedVec_trEnv'' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms indexedVec_trEnv'

/-! ## Acc: recursive Pi metadata -/

/- `Acc` is the first replay whose recursive constructor argument is a
function. In addition to translating the three kernel constants, this fixture
quotes the actual `RecursorRule.rhs` and compares it definitionally with the
public generalized Theory rule. -/
def accInfo : ConstantInfo := kernelInductInfo% Acc
def accIntroInfo : ConstantInfo := kernelCtorInfo% Acc.intro
def accRecInfo : ConstantInfo := kernelRecInfo% Acc.rec
def accKernelRuleRhs : VExpr := kernelRecRuleRhs% Acc.rec 0

example : (match accIntroInfo with
    | .ctorInfo ci => ci.numParams
    | _ => 0) = 2 := rfl
example : (match accIntroInfo with
    | .ctorInfo ci => ci.numFields
    | _ => 0) = 2 := rfl
example : (match accRecInfo with
    | .recInfo ci => ci.numParams
    | _ => 0) = 2 := rfl
example : (match accRecInfo with
    | .recInfo ci => ci.numIndices
    | _ => 0) = 1 := rfl
example : (match accRecInfo with
    | .recInfo ci => ci.numMotives
    | _ => 0) = 1 := rfl
example : (match accRecInfo with
    | .recInfo ci => ci.numMinors
    | _ => 0) = 1 := rfl
example : (match accRecInfo with
    | .recInfo ci => ci.rules.length
    | _ => 0) = 1 := rfl
example : (match accRecInfo with
    | .recInfo ci => ci.rules[0]?.map (·.ctor) |>.getD .anonymous
    | _ => .anonymous) = ``Acc.intro := rfl
example : (match accRecInfo with
    | .recInfo ci => ci.rules[0]?.map (·.nfields) |>.getD 0
    | _ => 0) = 2 := rfl

/-- The actual kernel rule has the same lambda-wrapped functional recursive
call as the public Theory generator, in the kernel recursor's universe order. -/
example : accKernelRuleRhs =
    (VInductDecl.ruleRec 1 ``Acc 2 accType 0 accType.ctors[0]).rhs := rfl
example : accKernelRuleRhs =
    accChecked.identityGeneration.generatedRules[0].rhs := rfl

def accTypeEnv := (VEnv.empty.addConst accType.name accType.toVConstant).get!
def accCtorEnv :=
  (accTypeEnv.addConst accType.ctors[0].name accType.ctors[0].toVConstant).get!
def accRecEnv :=
  (accCtorEnv.addConst ``Acc.rec
    (VInductDecl.recConstRec 1 ``Acc 2 accType)).get!

theorem accType_wf : accType.toVConstant.WF VEnv.empty := by
  have htel := (accDecl_wf.2 accType (by simp [accDecl])).1
  change VEnv.empty.IsType 1 [] accType.type
  rw [show accType.type = VExpr.forallN
    [.sort (.param 0),
      .forallE (.bvar 0) (.forallE (.bvar 1) (.sort .zero)),
      .bvar 1] (.sort .zero) from rfl]
  exact VEnv.IsType.forallN htel ⟨.succ .zero, VEnv.HasType.sort (by decide)⟩

theorem accTypeEnv_ordered : accTypeEnv.Ordered :=
  .const .empty accType_wf rfl

theorem accIntro_wf : accType.ctors[0].toVConstant.WF accTypeEnv := by
  have hblock := accDecl_wf.2 accType (by simp [accDecl])
  have hctor := hblock.2 accType.ctors[0] (by simp)
  have hle : VEnv.empty ≤ accTypeEnv := VEnv.addConst_le rfl
  have S0 : VInductDecl.Stage3Env accTypeEnv 1 ``Acc 2 .zero
      { accType with ctors := [] } := {
    ord := accTypeEnv_ordered
    hl := by decide
    hsort := rfl
    hlen := rfl
    hT := rfl
    hcs := by simp
    htel := by simp
    hs3 := by simp
    hparams := hblock.1.mono hle
    hfields := by simp
    hresult := by simp }
  exact S0.ctorType_isType' rfl rfl
    (VInductDecl.fieldsWF_mono hle hctor.1) (hctor.2.mono hle)

theorem accCtorEnv_ordered : accCtorEnv.Ordered :=
  .const (n := accType.ctors[0].name) (ci := accType.ctors[0].toVConstant)
    accTypeEnv_ordered accIntro_wf rfl

theorem accStage3 :
    VInductDecl.Stage3Env accCtorEnv 1 ``Acc 2 .zero accType := by
  have hblock := accDecl_wf.2 accType (by simp [accDecl])
  have hctor := hblock.2 accType.ctors[0] (by simp)
  have h0 : VEnv.empty ≤ accTypeEnv := VEnv.addConst_le rfl
  have h1 : accTypeEnv ≤ accCtorEnv :=
    VEnv.addConst_le (show accTypeEnv.addConst accType.ctors[0].name
      accType.ctors[0].toVConstant = some accCtorEnv from rfl)
  have hle : VEnv.empty ≤ accCtorEnv := h0.trans h1
  refine {
    ord := accCtorEnv_ordered
    hl := by decide
    hsort := rfl
    hlen := rfl
    hT := rfl
    hcs := ?_
    htel := ?_
    hs3 := ?_
    hparams := hblock.1.mono hle
    hfields := ?_
    hresult := ?_ }
  · intro c hc
    have hc' := List.mem_singleton.1 hc
    subst c
    rfl
  · intro c hc
    have hc' := List.mem_singleton.1 hc
    subst c
    rfl
  · intro c hc
    have hc' := List.mem_singleton.1 hc
    subst c
    rfl
  · intro c hc
    have hc' := List.mem_singleton.1 hc
    subst c
    exact VInductDecl.fieldsWF_mono hle hctor.1
  · intro c hc
    have hc' := List.mem_singleton.1 hc
    subst c
    exact hctor.2.mono hle

theorem accInfo_tr :
    TrConstVal .safe VEnv.empty accInfo accType.toVConstVal := by
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr VEnv.empty accInfo.levelParams [] accInfo.type
      accType.type := by tr_type_expr_tac
  obtain ⟨u, htype⟩ := accType_wf
  exact hshape.to_trExprS .empty trivial ⟨.sort u, htype⟩

theorem accIntroInfo_tr :
    TrConstVal .safe accTypeEnv accIntroInfo accType.ctors[0] := by
  have hAcc : accTypeEnv.constants ``Acc = some accType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr accTypeEnv accIntroInfo.levelParams []
      accIntroInfo.type accType.ctors[0].type := by tr_type_expr_tac
  obtain ⟨u, htype⟩ := accIntro_wf
  exact hshape.to_trExprS accTypeEnv_ordered trivial ⟨.sort u, htype⟩

theorem accRecInfo_tr :
    TrConstVal .safe accCtorEnv accRecInfo (inductRecVal accDecl accType) := by
  have hAcc : accCtorEnv.constants ``Acc = some accType.toVConstant := rfl
  have hIntro : accCtorEnv.constants ``Acc.intro =
      some accType.ctors[0].toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr accCtorEnv accRecInfo.levelParams []
      accRecInfo.type (inductRecVal accDecl accType).type := by tr_type_expr_tac
  obtain ⟨u, hrec⟩ := accStage3.recConstRec_wf
  exact hshape.to_trExprS accCtorEnv_ordered trivial ⟨.sort u, hrec⟩

def accTypeMap : ConstMap := ({} : ConstMap).insert ``Acc accInfo
def accCtorMap : ConstMap := accTypeMap.insert ``Acc.intro accIntroInfo
def accMap : ConstMap := accCtorMap.insert ``Acc.rec accRecInfo
def accFinalEnv : VEnv :=
  (VInductDecl.rulesRec 1 ``Acc 2 accType).foldl VEnv.addDefEq accRecEnv

theorem accType_fresh : ({} : ConstMap).find? ``Acc = none := by
  simp [SMap.find?]

theorem accTypeMap_wf : accTypeMap.WF :=
  SMap.WF.empty.insert _ _ accType_fresh

theorem accIntro_fresh : accTypeMap.find? ``Acc.intro = none := by
  rw [accTypeMap, SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem accCtorMap_wf : accCtorMap.WF :=
  accTypeMap_wf.insert _ _ accIntro_fresh

theorem accRec_fresh : accCtorMap.find? ``Acc.rec = none := by
  rw [accCtorMap, accTypeMap_wf.find?_insert, accTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem acc_addInduct :
    AddInduct ({} : ConstMap) VEnv.empty accDecl accMap accFinalEnv := by
  refine ⟨{
    generation := accChecked.identityGeneration
    generation_wf :=
      (accChecked.wf_of_decl accDecl_wf).identityGeneration .empty
    typeMap := accTypeMap
    typeEnv := accTypeEnv
    ctorMap := accCtorMap
    ctorEnv := accCtorEnv
    recEnv := accRecEnv
    addType := {
      info := accInfo
      kind_eq := by simp [accInfo, InductConstantKind.Matches]
      tr := accInfo_tr
      map_fresh := by simpa [accType] using accType_fresh
      env_add := rfl
      map_add := rfl }
    addCtors := ?_
    addRec := {
      info := accRecInfo
      kind_eq := by simp [accRecInfo, InductConstantKind.Matches]
      tr := accRecInfo_tr
      map_fresh := by
        simpa [inductRecVal, accDecl, accType] using accRec_fresh
      env_add := rfl
      map_add := rfl }
    addRules := ⟨rfl⟩ }⟩
  exact .cons {
    info := accIntroInfo
    kind_eq := by simp [accIntroInfo, InductConstantKind.Matches]
    tr := accIntroInfo_tr
    map_fresh := by simpa [accType] using accIntro_fresh
    env_add := rfl
    map_add := rfl } .nil

/-- Replay the actual kernel `Acc` metadata through the live inductive
environment branch. -/
theorem acc_trEnv' : TrEnv' .safe accMap false accFinalEnv :=
  .induct acc_addInduct .empty

theorem acc_final_matches_addInduct :
    VEnv.empty.addInduct accDecl = some accFinalEnv :=
  rfl

theorem acc_env_wf : accFinalEnv.WF := acc_trEnv'.wf

theorem acc_aligned : Aligned .safe accMap accFinalEnv := acc_trEnv'.aligned

theorem acc_type_map_lookup : accMap.find? ``Acc = some accInfo := by
  rw [accMap, accCtorMap_wf.find?_insert, accCtorMap,
    accTypeMap_wf.find?_insert, accTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  rfl

theorem acc_type_env_lookup :
    accFinalEnv.constants ``Acc = some accType.toVConstant := rfl

theorem acc_type_lookup_unique :
    accInfo.name = ``Acc ∧
      TrConstant .safe accFinalEnv accInfo accType.toVConstant :=
  acc_aligned.find?_uniq acc_type_map_lookup acc_type_env_lookup

theorem acc_intro_map_lookup :
    accMap.find? ``Acc.intro = some accIntroInfo := by
  rw [accMap, accCtorMap_wf.find?_insert, accCtorMap,
    accTypeMap_wf.find?_insert]
  rfl

theorem acc_intro_env_lookup :
    accFinalEnv.constants ``Acc.intro =
      some accType.ctors[0].toVConstant := rfl

theorem acc_intro_lookup_unique :
    accIntroInfo.name = ``Acc.intro ∧
      TrConstant .safe accFinalEnv accIntroInfo
        accType.ctors[0].toVConstant :=
  acc_aligned.find?_uniq acc_intro_map_lookup acc_intro_env_lookup

theorem acc_rec_map_lookup : accMap.find? ``Acc.rec = some accRecInfo := by
  rw [accMap, accCtorMap_wf.find?_insert]
  rfl

theorem acc_rec_env_lookup :
    accFinalEnv.constants ``Acc.rec =
      some (VInductDecl.recConstRec 1 ``Acc 2 accType) := rfl

theorem acc_rec_lookup_unique :
    accRecInfo.name = ``Acc.rec ∧
      TrConstant .safe accFinalEnv accRecInfo
        (VInductDecl.recConstRec 1 ``Acc 2 accType) :=
  acc_aligned.find?_uniq acc_rec_map_lookup acc_rec_env_lookup

/- This has the same transitional Verify closure as the direct replay roots:
`sorryAx` enters through `TrProj`, and the persistent-map contracts enter
through concrete `SMap` freshness proofs. -/
/--
info: 'Lean4Lean.InductiveReplayFixtures.acc_trEnv'' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms acc_trEnv'

/-! ## AliasFormer: non-identity family-result normalization -/

/-- The actual reducible alias declaration that precedes `AliasFormer` in the
kernel environment. -/
def typeFamilyAliasKernelDef : DefinitionVal :=
  kernelDefVal% TypeFamilyAlias

def typeFamilyAliasInfo : ConstantInfo :=
  .defnInfo typeFamilyAliasKernelDef

def typeFamilyAliasVal : VDefVal where
  name := ``TypeFamilyAlias
  uvars := (vconst(type_of% @TypeFamilyAlias) : VConstant).uvars
  type := (vconst(type_of% @TypeFamilyAlias) : VConstant).type
  value := typeFamilyAliasDefEq.rhs

theorem typeFamilyAliasInfo_tr :
    TrDefVal .safe VEnv.empty typeFamilyAliasInfo typeFamilyAliasVal := by
  refine ⟨⟨⟨by decide, rfl, ?_⟩, rfl⟩, ?_⟩
  · exact .sort rfl
  · exact .sort rfl

theorem typeFamilyAliasVal_wf :
    typeFamilyAliasVal.WF VEnv.empty :=
  VEnv.HasType.sort (by decide)

def typeFamilyAliasMap : ConstMap :=
  ({} : ConstMap).insert ``TypeFamilyAlias typeFamilyAliasInfo

theorem typeFamilyAliasMap_fresh :
    ({} : ConstMap).find? ``TypeFamilyAlias = none := by
  simp [SMap.find?]

/-- Replay the actual alias definition, including its Theory delta rule. -/
theorem typeFamilyAlias_trEnv' :
    TrEnv' .safe typeFamilyAliasMap false typeFamilyAliasEnv :=
  .defn (ci := typeFamilyAliasKernelDef) (ci' := typeFamilyAliasVal)
    typeFamilyAliasInfo_tr typeFamilyAliasMap_fresh
    typeFamilyAliasVal_wf rfl .empty

def aliasFormerInfo : ConstantInfo := kernelInductInfo% AliasFormer
def aliasFormerMkInfo : ConstantInfo := kernelCtorInfo% AliasFormer.mk
def aliasFormerRecInfo : ConstantInfo := kernelRecInfo% AliasFormer.rec
def aliasFormerKernelRuleRhs : VExpr :=
  kernelRecRuleRhs% AliasFormer.rec 0

example : aliasFormerRawDecl.checked? = none := rfl
example : aliasFormerGenerationChecked.block.sourceType =
    aliasFormerRawType := rfl
example : aliasFormerGenerationChecked.block.checked.type =
    aliasFormerViewType := rfl
example : aliasFormerKernelRuleRhs =
    aliasFormerGenerationChecked.generatedRules[0].rhs := rfl

def aliasFormerTypeEnv :=
  (typeFamilyAliasEnv.addConst aliasFormerRawType.name
    aliasFormerRawType.toVConstant).get!

def aliasFormerCtorEnv :=
  (aliasFormerTypeEnv.addConst aliasFormerRawType.ctors[0].name
    aliasFormerRawType.ctors[0].toVConstant).get!

def aliasFormerRecEnv :=
  (aliasFormerCtorEnv.addConst ``AliasFormer.rec
    aliasFormerGenerationChecked.recursor).get!

theorem aliasFormerTypeEnv_ordered : aliasFormerTypeEnv.Ordered := by
  refine .const (n := aliasFormerRawType.name)
    (ci := aliasFormerRawType.toVConstant)
    typeFamilyAliasEnv_ordered ?_ rfl
  show typeFamilyAliasEnv.IsType
    aliasFormerGenerationChecked.block.sourceType.uvars []
    aliasFormerGenerationChecked.block.sourceType.type
  rw [aliasFormerGenerationChecked.block.sourceType_uvars_eq]
  exact aliasFormerGenerationChecked_wf.rawFamily_isType

theorem aliasFormerRawCtor_wf :
    aliasFormerRawType.ctors[0].toVConstant.WF aliasFormerTypeEnv := by
  have hctor :
      (⟨aliasFormerRawType.ctors[0],
        aliasFormerViewChecked.constructors[0]⟩ :
          VInductDecl.NormalizedCtor) ∈
        aliasFormerGenerationChecked.block.ctorPairs := by
    exact .head _
  show aliasFormerTypeEnv.IsType
    aliasFormerRawType.ctors[0].uvars []
    aliasFormerRawType.ctors[0].type
  rw [aliasFormerGenerationChecked.ctor_uvars_eq hctor]
  exact aliasFormerGenerationChecked_wf.rawCtor_isType rfl hctor

theorem aliasFormerCtorEnv_ordered : aliasFormerCtorEnv.Ordered :=
  .const (n := aliasFormerRawType.ctors[0].name)
    (ci := aliasFormerRawType.ctors[0].toVConstant)
    aliasFormerTypeEnv_ordered aliasFormerRawCtor_wf rfl

theorem aliasFormerGenerationEnv :
    VInductDecl.GenerationEnv aliasFormerGenerationChecked
      aliasFormerCtorEnv := by
  apply aliasFormerGenerationChecked_wf.toGenerationEnv
    (envT := aliasFormerTypeEnv)
  · rfl
  · exact (VEnv.addConst_le (show
      typeFamilyAliasEnv.addConst aliasFormerRawType.name
        aliasFormerRawType.toVConstant = some aliasFormerTypeEnv from rfl)).trans
      (VEnv.addConst_le (show
        aliasFormerTypeEnv.addConst aliasFormerRawType.ctors[0].name
          aliasFormerRawType.ctors[0].toVConstant =
            some aliasFormerCtorEnv from rfl))
  · exact VEnv.addConst_le (show
      aliasFormerTypeEnv.addConst aliasFormerRawType.ctors[0].name
        aliasFormerRawType.ctors[0].toVConstant =
          some aliasFormerCtorEnv from rfl)
  · exact aliasFormerCtorEnv_ordered
  · rfl
  · intro ctor hctor
    change ctor ∈
      [⟨aliasFormerRawType.ctors[0],
        aliasFormerViewChecked.constructors[0]⟩] at hctor
    obtain rfl := List.mem_singleton.1 hctor
    rfl

theorem aliasFormerInfo_tr :
    TrConstVal .safe typeFamilyAliasEnv aliasFormerInfo
      aliasFormerRawType.toVConstVal := by
  have hAlias : typeFamilyAliasEnv.constants ``TypeFamilyAlias =
      some (vconst(type_of% @TypeFamilyAlias)) := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr typeFamilyAliasEnv
      aliasFormerInfo.levelParams [] aliasFormerInfo.type
      aliasFormerRawType.type := by
    tr_type_expr_tac
  obtain ⟨u, htype⟩ :=
    aliasFormerGenerationChecked_wf.rawFamily_isType
  exact hshape.to_trExprS typeFamilyAliasEnv_ordered trivial
    ⟨.sort u, htype⟩

theorem aliasFormerMkInfo_tr :
    TrConstVal .safe aliasFormerTypeEnv aliasFormerMkInfo
      aliasFormerRawType.ctors[0] := by
  have hFamily : aliasFormerTypeEnv.constants ``AliasFormer =
      some aliasFormerRawType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr aliasFormerTypeEnv
      aliasFormerMkInfo.levelParams [] aliasFormerMkInfo.type
      aliasFormerRawType.ctors[0].type := by
    tr_type_expr_tac
  obtain ⟨u, htype⟩ := aliasFormerRawCtor_wf
  exact hshape.to_trExprS aliasFormerTypeEnv_ordered trivial
    ⟨.sort u, htype⟩

theorem aliasFormerRecInfo_tr :
    TrConstVal .safe aliasFormerCtorEnv aliasFormerRecInfo
      (inductGenerationRecVal aliasFormerGenerationChecked) := by
  have hFamily : aliasFormerCtorEnv.constants ``AliasFormer =
      some aliasFormerRawType.toVConstant := rfl
  have hMk : aliasFormerCtorEnv.constants ``AliasFormer.mk =
      some aliasFormerRawType.ctors[0].toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr aliasFormerCtorEnv
      aliasFormerRecInfo.levelParams [] aliasFormerRecInfo.type
      (inductGenerationRecVal aliasFormerGenerationChecked).type := by
    tr_type_expr_tac
  obtain ⟨u, hrec⟩ := aliasFormerGenerationEnv.recursor_wf
  exact hshape.to_trExprS aliasFormerCtorEnv_ordered trivial
    ⟨.sort u, hrec⟩

def aliasFormerTypeMap : ConstMap :=
  typeFamilyAliasMap.insert ``AliasFormer aliasFormerInfo

def aliasFormerCtorMap : ConstMap :=
  aliasFormerTypeMap.insert ``AliasFormer.mk aliasFormerMkInfo

def aliasFormerMap : ConstMap :=
  aliasFormerCtorMap.insert ``AliasFormer.rec aliasFormerRecInfo

theorem typeFamilyAliasMap_wf : typeFamilyAliasMap.WF :=
  typeFamilyAlias_trEnv'.map_wf

theorem aliasFormerType_fresh :
    typeFamilyAliasMap.find? ``AliasFormer = none := by
  rw [typeFamilyAliasMap, SMap.WF.find?_insert
    (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem aliasFormerTypeMap_wf : aliasFormerTypeMap.WF :=
  typeFamilyAliasMap_wf.insert _ _ aliasFormerType_fresh

theorem aliasFormerMk_fresh :
    aliasFormerTypeMap.find? ``AliasFormer.mk = none := by
  rw [aliasFormerTypeMap, typeFamilyAliasMap_wf.find?_insert,
    typeFamilyAliasMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem aliasFormerCtorMap_wf : aliasFormerCtorMap.WF :=
  aliasFormerTypeMap_wf.insert _ _ aliasFormerMk_fresh

theorem aliasFormerRec_fresh :
    aliasFormerCtorMap.find? ``AliasFormer.rec = none := by
  rw [aliasFormerCtorMap, aliasFormerTypeMap_wf.find?_insert,
    aliasFormerTypeMap, typeFamilyAliasMap_wf.find?_insert,
    typeFamilyAliasMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

private def aliasFormerAddInductTraceWith
    (generation_wf :
      aliasFormerGenerationChecked.WF typeFamilyAliasEnv) :
    AddInductTrace typeFamilyAliasMap typeFamilyAliasEnv
      aliasFormerRawDecl aliasFormerMap aliasFormerFinalEnv := by
  refine {
    generation := aliasFormerGenerationChecked
    generation_wf := generation_wf
    typeMap := aliasFormerTypeMap
    typeEnv := aliasFormerTypeEnv
    ctorMap := aliasFormerCtorMap
    ctorEnv := aliasFormerCtorEnv
    recEnv := aliasFormerRecEnv
    addType := {
      info := aliasFormerInfo
      kind_eq := by simp [aliasFormerInfo, InductConstantKind.Matches]
      tr := aliasFormerInfo_tr
      map_fresh := by
        simpa [aliasFormerRawType] using aliasFormerType_fresh
      env_add := rfl
      map_add := rfl }
    addCtors := ?_
    addRec := {
      info := aliasFormerRecInfo
      kind_eq := by simp [aliasFormerRecInfo, InductConstantKind.Matches]
      tr := aliasFormerRecInfo_tr
      map_fresh := by
        simpa [inductGenerationRecVal, aliasFormerRawType] using
          aliasFormerRec_fresh
      env_add := rfl
      map_add := rfl }
    addRules := ⟨rfl⟩ }
  exact .cons {
    info := aliasFormerMkInfo
    kind_eq := by simp [aliasFormerMkInfo, InductConstantKind.Matches]
    tr := aliasFormerMkInfo_tr
    map_fresh := by
      simpa [aliasFormerRawType] using aliasFormerMk_fresh
    env_add := rfl
    map_add := rfl } .nil

theorem aliasFormer_addInduct :
    AddInduct typeFamilyAliasMap typeFamilyAliasEnv
      aliasFormerRawDecl aliasFormerMap aliasFormerFinalEnv :=
  ⟨aliasFormerAddInductTraceWith aliasFormerGenerationChecked_wf⟩

theorem aliasFormer_trEnv' :
    TrEnv' .safe aliasFormerMap false aliasFormerFinalEnv :=
  .induct aliasFormer_addInduct typeFamilyAlias_trEnv'

theorem aliasFormer_final_matches_generation :
    typeFamilyAliasEnv.addInductGeneration
      aliasFormerGenerationChecked = some aliasFormerFinalEnv :=
  aliasFormer_addInductGeneration

theorem aliasFormer_env_wf : aliasFormerFinalEnv.WF :=
  aliasFormer_trEnv'.wf

theorem aliasFormer_aligned :
    Aligned .safe aliasFormerMap aliasFormerFinalEnv :=
  aliasFormer_trEnv'.aligned

theorem aliasFormer_type_map_lookup :
    aliasFormerMap.find? ``AliasFormer = some aliasFormerInfo := by
  rw [aliasFormerMap, aliasFormerCtorMap_wf.find?_insert,
    aliasFormerCtorMap, aliasFormerTypeMap_wf.find?_insert,
    aliasFormerTypeMap, typeFamilyAliasMap_wf.find?_insert]
  rfl

theorem aliasFormer_type_lookup_unique :
    aliasFormerInfo.name = ``AliasFormer ∧
      TrConstant .safe aliasFormerFinalEnv aliasFormerInfo
        aliasFormerRawType.toVConstant :=
  aliasFormer_aligned.find?_uniq aliasFormer_type_map_lookup
    aliasFormerFinalEnv_family_lookup

theorem aliasFormer_mk_map_lookup :
    aliasFormerMap.find? ``AliasFormer.mk = some aliasFormerMkInfo := by
  rw [aliasFormerMap, aliasFormerCtorMap_wf.find?_insert,
    aliasFormerCtorMap, aliasFormerTypeMap_wf.find?_insert]
  rfl

theorem aliasFormer_mk_lookup_unique :
    aliasFormerMkInfo.name = ``AliasFormer.mk ∧
      TrConstant .safe aliasFormerFinalEnv aliasFormerMkInfo
        aliasFormerRawType.ctors[0].toVConstant :=
  aliasFormer_aligned.find?_uniq aliasFormer_mk_map_lookup
    (aliasFormerFinalEnv_ctor_lookup _ (.head _))

theorem aliasFormer_rec_map_lookup :
    aliasFormerMap.find? ``AliasFormer.rec = some aliasFormerRecInfo := by
  rw [aliasFormerMap, aliasFormerCtorMap_wf.find?_insert]
  rfl

theorem aliasFormer_rec_lookup_unique :
    aliasFormerRecInfo.name = ``AliasFormer.rec ∧
      TrConstant .safe aliasFormerFinalEnv aliasFormerRecInfo
        aliasFormerGenerationChecked.recursor :=
  aliasFormer_aligned.find?_uniq aliasFormer_rec_map_lookup
    aliasFormerFinalEnv_rec_lookup

/-! ## AliasRec: non-identity recursive-field normalization -/

def recAliasKernelDef : DefinitionVal := kernelDefVal% RecAlias

def recAliasInfo : ConstantInfo := .defnInfo recAliasKernelDef

def recAliasVal : VDefVal where
  name := ``RecAlias
  uvars := (vconst(type_of% @RecAlias) : VConstant).uvars
  type := (vconst(type_of% @RecAlias) : VConstant).type
  value := recAliasDefEq.rhs

theorem recAliasInfo_tr :
    TrDefVal .safe VEnv.empty recAliasInfo recAliasVal := by
  refine ⟨⟨⟨by decide, rfl, ?_⟩, rfl⟩, ?_⟩
  · have hshape : TrTypeExpr VEnv.empty recAliasInfo.levelParams []
        recAliasInfo.type recAliasVal.type := by
      tr_type_expr_tac
    obtain ⟨u, htype⟩ := recAliasConstant_wf
    exact hshape.to_trExprS .empty trivial ⟨.sort u, htype⟩
  · refine .lam ?_ (.sort rfl) (.bvar rfl)
    exact ⟨_, VEnv.HasType.sort (by decide)⟩

theorem recAliasVal_wf : recAliasVal.WF VEnv.empty := by
  exact VEnv.HasType.lam
    (VEnv.HasType.sort (by decide))
    (VEnv.HasType.bvar .zero)

def recAliasMap : ConstMap :=
  ({} : ConstMap).insert ``RecAlias recAliasInfo

theorem recAliasMap_fresh :
    ({} : ConstMap).find? ``RecAlias = none := by
  simp [SMap.find?]

theorem recAlias_trEnv' :
    TrEnv' .safe recAliasMap false recAliasEnv :=
  .defn (ci := recAliasKernelDef) (ci' := recAliasVal)
    recAliasInfo_tr recAliasMap_fresh recAliasVal_wf rfl .empty

def aliasRecInfo : ConstantInfo := kernelInductInfo% AliasRec
def aliasRecMkInfo : ConstantInfo := kernelCtorInfo% AliasRec.mk
def aliasRecRecInfo : ConstantInfo := kernelRecInfo% AliasRec.rec
def aliasRecKernelRuleRhs : VExpr :=
  kernelRecRuleRhs% AliasRec.rec 0

example : aliasRecRawDecl.checked? = none := rfl
example : aliasRecGenerationChecked.block.sourceType = aliasRecRawType := rfl
example : aliasRecGenerationChecked.block.checked.type = aliasRecViewType := rfl
example : aliasRecGenerationChecked.block.ctorPairs[0].rawFields 0 =
    [aliasRecRawField] := rfl
example : (VInductDecl.ctorFields
    aliasRecGenerationChecked.minorTypes[0])[0]? =
      some aliasRecRawField := rfl
example : aliasRecKernelRuleRhs =
    aliasRecGenerationChecked.generatedRules[0].rhs := rfl

def aliasRecTypeEnv :=
  (recAliasEnv.addConst aliasRecRawType.name
    aliasRecRawType.toVConstant).get!

def aliasRecCtorEnv :=
  (aliasRecTypeEnv.addConst aliasRecRawType.ctors[0].name
    aliasRecRawType.ctors[0].toVConstant).get!

def aliasRecRecEnv :=
  (aliasRecCtorEnv.addConst ``AliasRec.rec
    aliasRecGenerationChecked.recursor).get!

theorem aliasRecTypeEnv_ordered : aliasRecTypeEnv.Ordered := by
  refine .const (n := aliasRecRawType.name)
    (ci := aliasRecRawType.toVConstant)
    recAliasEnv_ordered ?_ rfl
  show recAliasEnv.IsType
    aliasRecGenerationChecked.block.sourceType.uvars []
    aliasRecGenerationChecked.block.sourceType.type
  rw [aliasRecGenerationChecked.block.sourceType_uvars_eq]
  exact aliasRecGenerationChecked_wf.rawFamily_isType

theorem aliasRecRawCtor_wf :
    aliasRecRawType.ctors[0].toVConstant.WF aliasRecTypeEnv := by
  have hctor :
      (⟨aliasRecRawType.ctors[0],
        aliasRecViewChecked.constructors[0]⟩ :
          VInductDecl.NormalizedCtor) ∈
        aliasRecGenerationChecked.block.ctorPairs := by
    exact .head _
  show aliasRecTypeEnv.IsType aliasRecRawType.ctors[0].uvars []
    aliasRecRawType.ctors[0].type
  rw [aliasRecGenerationChecked.ctor_uvars_eq hctor]
  exact aliasRecGenerationChecked_wf.rawCtor_isType rfl hctor

theorem aliasRecCtorEnv_ordered : aliasRecCtorEnv.Ordered :=
  .const (n := aliasRecRawType.ctors[0].name)
    (ci := aliasRecRawType.ctors[0].toVConstant)
    aliasRecTypeEnv_ordered aliasRecRawCtor_wf rfl

theorem aliasRecGenerationEnv :
    VInductDecl.GenerationEnv aliasRecGenerationChecked aliasRecCtorEnv := by
  apply aliasRecGenerationChecked_wf.toGenerationEnv
    (envT := aliasRecTypeEnv)
  · rfl
  · exact (VEnv.addConst_le (show
      recAliasEnv.addConst aliasRecRawType.name
        aliasRecRawType.toVConstant = some aliasRecTypeEnv from rfl)).trans
      (VEnv.addConst_le (show
        aliasRecTypeEnv.addConst aliasRecRawType.ctors[0].name
          aliasRecRawType.ctors[0].toVConstant =
            some aliasRecCtorEnv from rfl))
  · exact VEnv.addConst_le (show
      aliasRecTypeEnv.addConst aliasRecRawType.ctors[0].name
        aliasRecRawType.ctors[0].toVConstant =
          some aliasRecCtorEnv from rfl)
  · exact aliasRecCtorEnv_ordered
  · rfl
  · intro ctor hctor
    change ctor ∈
      [⟨aliasRecRawType.ctors[0],
        aliasRecViewChecked.constructors[0]⟩] at hctor
    obtain rfl := List.mem_singleton.1 hctor
    rfl

theorem aliasRecInfo_tr :
    TrConstVal .safe recAliasEnv aliasRecInfo
      aliasRecRawType.toVConstVal := by
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr recAliasEnv aliasRecInfo.levelParams []
      aliasRecInfo.type aliasRecRawType.type := by
    tr_type_expr_tac
  exact hshape.to_trExprS recAliasEnv_ordered trivial
    ⟨.sort (.succ (.succ .zero)), VEnv.HasType.sort (by decide)⟩

theorem aliasRecMkInfo_tr :
    TrConstVal .safe aliasRecTypeEnv aliasRecMkInfo
      aliasRecRawType.ctors[0] := by
  have hAlias : aliasRecTypeEnv.constants ``RecAlias =
      some (vconst(type_of% @RecAlias)) := rfl
  have hFamily : aliasRecTypeEnv.constants ``AliasRec =
      some aliasRecRawType.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr aliasRecTypeEnv
      aliasRecMkInfo.levelParams [] aliasRecMkInfo.type
      aliasRecRawType.ctors[0].type := by
    tr_type_expr_tac
  obtain ⟨u, htype⟩ := aliasRecRawCtor_wf
  exact hshape.to_trExprS aliasRecTypeEnv_ordered trivial
    ⟨.sort u, htype⟩

theorem aliasRecRecInfo_tr :
    TrConstVal .safe aliasRecCtorEnv aliasRecRecInfo
      (inductGenerationRecVal aliasRecGenerationChecked) := by
  have hAlias : aliasRecCtorEnv.constants ``RecAlias =
      some (vconst(type_of% @RecAlias)) := rfl
  have hFamily : aliasRecCtorEnv.constants ``AliasRec =
      some aliasRecRawType.toVConstant := rfl
  have hMk : aliasRecCtorEnv.constants ``AliasRec.mk =
      some aliasRecRawType.ctors[0].toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have hshape : TrTypeExpr aliasRecCtorEnv
      aliasRecRecInfo.levelParams [] aliasRecRecInfo.type
      (inductGenerationRecVal aliasRecGenerationChecked).type := by
    tr_type_expr_tac
  obtain ⟨u, hrec⟩ := aliasRecGenerationEnv.recursor_wf
  exact hshape.to_trExprS aliasRecCtorEnv_ordered trivial
    ⟨.sort u, hrec⟩

def aliasRecTypeMap : ConstMap :=
  recAliasMap.insert ``AliasRec aliasRecInfo

def aliasRecCtorMap : ConstMap :=
  aliasRecTypeMap.insert ``AliasRec.mk aliasRecMkInfo

def aliasRecMap : ConstMap :=
  aliasRecCtorMap.insert ``AliasRec.rec aliasRecRecInfo

theorem recAliasMap_wf : recAliasMap.WF := recAlias_trEnv'.map_wf

theorem aliasRecType_fresh :
    recAliasMap.find? ``AliasRec = none := by
  rw [recAliasMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem aliasRecTypeMap_wf : aliasRecTypeMap.WF :=
  recAliasMap_wf.insert _ _ aliasRecType_fresh

theorem aliasRecMk_fresh :
    aliasRecTypeMap.find? ``AliasRec.mk = none := by
  rw [aliasRecTypeMap, recAliasMap_wf.find?_insert, recAliasMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem aliasRecCtorMap_wf : aliasRecCtorMap.WF :=
  aliasRecTypeMap_wf.insert _ _ aliasRecMk_fresh

theorem aliasRecRec_fresh :
    aliasRecCtorMap.find? ``AliasRec.rec = none := by
  rw [aliasRecCtorMap, aliasRecTypeMap_wf.find?_insert,
    aliasRecTypeMap, recAliasMap_wf.find?_insert, recAliasMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

private def aliasRecAddInductTraceWith
    (generation_wf : aliasRecGenerationChecked.WF recAliasEnv) :
    AddInductTrace recAliasMap recAliasEnv aliasRecRawDecl
      aliasRecMap aliasRecFinalEnv := by
  refine {
    generation := aliasRecGenerationChecked
    generation_wf := generation_wf
    typeMap := aliasRecTypeMap
    typeEnv := aliasRecTypeEnv
    ctorMap := aliasRecCtorMap
    ctorEnv := aliasRecCtorEnv
    recEnv := aliasRecRecEnv
    addType := {
      info := aliasRecInfo
      kind_eq := by simp [aliasRecInfo, InductConstantKind.Matches]
      tr := aliasRecInfo_tr
      map_fresh := by simpa [aliasRecRawType] using aliasRecType_fresh
      env_add := rfl
      map_add := rfl }
    addCtors := ?_
    addRec := {
      info := aliasRecRecInfo
      kind_eq := by simp [aliasRecRecInfo, InductConstantKind.Matches]
      tr := aliasRecRecInfo_tr
      map_fresh := by
        simpa [inductGenerationRecVal, aliasRecRawType] using
          aliasRecRec_fresh
      env_add := rfl
      map_add := rfl }
    addRules := ⟨rfl⟩ }
  exact .cons {
    info := aliasRecMkInfo
    kind_eq := by simp [aliasRecMkInfo, InductConstantKind.Matches]
    tr := aliasRecMkInfo_tr
    map_fresh := by simpa [aliasRecRawType] using aliasRecMk_fresh
    env_add := rfl
    map_add := rfl } .nil

theorem aliasRec_addInduct :
    AddInduct recAliasMap recAliasEnv aliasRecRawDecl
      aliasRecMap aliasRecFinalEnv :=
  ⟨aliasRecAddInductTraceWith aliasRecGenerationChecked_wf⟩

theorem aliasRec_trEnv' :
    TrEnv' .safe aliasRecMap false aliasRecFinalEnv :=
  .induct aliasRec_addInduct recAlias_trEnv'

theorem aliasRec_final_matches_generation :
    recAliasEnv.addInductGeneration aliasRecGenerationChecked =
      some aliasRecFinalEnv :=
  aliasRec_addInductGeneration

theorem aliasRec_env_wf : aliasRecFinalEnv.WF :=
  aliasRec_trEnv'.wf

theorem aliasRec_aligned :
    Aligned .safe aliasRecMap aliasRecFinalEnv :=
  aliasRec_trEnv'.aligned

theorem aliasRec_type_map_lookup :
    aliasRecMap.find? ``AliasRec = some aliasRecInfo := by
  rw [aliasRecMap, aliasRecCtorMap_wf.find?_insert,
    aliasRecCtorMap, aliasRecTypeMap_wf.find?_insert,
    aliasRecTypeMap, recAliasMap_wf.find?_insert]
  rfl

theorem aliasRec_type_lookup_unique :
    aliasRecInfo.name = ``AliasRec ∧
      TrConstant .safe aliasRecFinalEnv aliasRecInfo
        aliasRecRawType.toVConstant :=
  aliasRec_aligned.find?_uniq aliasRec_type_map_lookup
    aliasRecFinalEnv_family_lookup

theorem aliasRec_mk_map_lookup :
    aliasRecMap.find? ``AliasRec.mk = some aliasRecMkInfo := by
  rw [aliasRecMap, aliasRecCtorMap_wf.find?_insert,
    aliasRecCtorMap, aliasRecTypeMap_wf.find?_insert]
  rfl

theorem aliasRec_mk_lookup_unique :
    aliasRecMkInfo.name = ``AliasRec.mk ∧
      TrConstant .safe aliasRecFinalEnv aliasRecMkInfo
        aliasRecRawType.ctors[0].toVConstant :=
  aliasRec_aligned.find?_uniq aliasRec_mk_map_lookup
    (aliasRecFinalEnv_ctor_lookup _ (.head _))

theorem aliasRec_rec_map_lookup :
    aliasRecMap.find? ``AliasRec.rec = some aliasRecRecInfo := by
  rw [aliasRecMap, aliasRecCtorMap_wf.find?_insert]
  rfl

theorem aliasRec_rec_lookup_unique :
    aliasRecRecInfo.name = ``AliasRec.rec ∧
      TrConstant .safe aliasRecFinalEnv aliasRecRecInfo
        aliasRecGenerationChecked.recursor :=
  aliasRec_aligned.find?_uniq aliasRec_rec_map_lookup
    aliasRecFinalEnv_rec_lookup

/-! ## Checker-produced alias normalization certificates -/

/-- Minimal kernel environment used to replay family-result WHNF without
bringing unrelated constants or primitives into the certificate. -/
private def aliasFormerNormalizationKernelEnv : Kernel.Environment :=
  Kernel.Environment.ofConstants `_aliasFormerNormalization
    typeFamilyAliasMap

private theorem aliasFormerNormalization_trEnv :
    TrEnv .safe aliasFormerNormalizationKernelEnv typeFamilyAliasEnv := by
  simpa [TrEnv, aliasFormerNormalizationKernelEnv] using
    typeFamilyAlias_trEnv'

private theorem aliasFormerNormalization_hasPrimitives :
    VEnv.HasPrimitives typeFamilyAliasEnv := by
  apply TypeChecker.VEnv.HasPrimitives.of_avoids
  intro n hn
  simp only [TypeChecker.reflectedPrimitiveNames, List.mem_cons,
    List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;>
    rfl

private theorem aliasFormerNormalization_safePrimitives :
    aliasFormerNormalizationKernelEnv.find? n = some ci →
      Kernel.Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = [] := by
  intro hfind hprim
  change typeFamilyAliasMap.find?' n = some ci at hfind
  rw [typeFamilyAliasMap_wf.find?'_eq_find?,
    typeFamilyAliasMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty] at hfind
  simp [SMap.find?] at hfind
  obtain ⟨rfl, rfl⟩ := hfind
  simp [Kernel.Environment.primitives, NameSet.ofList] at hprim
  simp +decide [NameSet.contains] at hprim

private def aliasFormerNormalizationVEnvs : VEnvs where
  venv _ := typeFamilyAliasEnv

private theorem aliasFormerNormalizationVEnvs_wf :
    aliasFormerNormalizationVEnvs.WF
      aliasFormerNormalizationKernelEnv where
  tr := by
    intro safety
    change TrEnv' _ typeFamilyAliasMap false typeFamilyAliasEnv
    exact typeFamilyAlias_trEnv'.sf_mono DefinitionSafety.le_safe
  hasPrimitives := aliasFormerNormalization_hasPrimitives
  safePrimitives := aliasFormerNormalization_safePrimitives
  mono := fun _ => .rfl

private def aliasFormerNormalizationContext : TypeChecker.VContext :=
  TypeChecker.VContext.mk' aliasFormerNormalizationVEnvs_wf
    (fuel := { whnf := 2 })

private def aliasFormerNormalizationRawContext : TypeChecker.Context where
  env := aliasFormerNormalizationKernelEnv
  fuel := { whnf := 2 }

private def aliasFormerCheckTypeState (state : TypeChecker.State) :
    TypeChecker.State :=
  { state with
    inferTypeC := state.inferTypeC.insert
      (.const ``TypeFamilyAlias [])
      (.sort (.succ (.succ .zero))) }

/-- Insert the raw AliasFormer family before checking its constructor type. -/
private def aliasFormerCtorNormalizationAddType :
    AddInductConstant .induct typeFamilyAliasMap typeFamilyAliasEnv
      aliasFormerRawType.toVConstVal aliasFormerTypeMap
      aliasFormerTypeEnv where
  info := aliasFormerInfo
  kind_eq := by simp [aliasFormerInfo, InductConstantKind.Matches]
  tr := aliasFormerInfo_tr
  map_fresh := by simpa [aliasFormerRawType] using aliasFormerType_fresh
  env_add := rfl
  map_add := rfl

private theorem aliasFormerCtorNormalization_trEnv' :
    TrEnv' .safe aliasFormerTypeMap false aliasFormerTypeEnv :=
  .inductStaging aliasFormerCtorNormalizationAddType
    (by
      show typeFamilyAliasEnv.IsType aliasFormerRawType.uvars []
        aliasFormerRawType.type
      refine ⟨.succ (.succ .zero), ?_⟩
      change typeFamilyAliasEnv.HasType 0 []
        (.const ``TypeFamilyAlias []) (.sort (.succ (.succ .zero)))
      exact VEnv.HasType.const
        (ci := (vconst(type_of% @TypeFamilyAlias) : VConstant))
        (ls := []) rfl (by simp) rfl)
    typeFamilyAlias_trEnv'

private def aliasFormerCtorNormalizationKernelEnv : Kernel.Environment :=
  Kernel.Environment.ofConstants `_aliasFormerCtorNormalization
    aliasFormerTypeMap

private theorem aliasFormerCtorNormalization_trEnv :
    TrEnv .safe aliasFormerCtorNormalizationKernelEnv
      aliasFormerTypeEnv := by
  simpa [TrEnv, aliasFormerCtorNormalizationKernelEnv] using
    aliasFormerCtorNormalization_trEnv'

private theorem aliasFormerCtorNormalization_hasPrimitives :
    VEnv.HasPrimitives aliasFormerTypeEnv := by
  apply TypeChecker.VEnv.HasPrimitives.of_avoids
  intro n hn
  simp only [TypeChecker.reflectedPrimitiveNames, List.mem_cons,
    List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;>
    rfl

private theorem aliasFormerCtorNormalization_safePrimitives :
    aliasFormerCtorNormalizationKernelEnv.find? n = some ci →
      Kernel.Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = [] := by
  intro hfind hprim
  change aliasFormerTypeMap.find?' n = some ci at hfind
  rw [aliasFormerTypeMap_wf.find?'_eq_find?,
    aliasFormerTypeMap, typeFamilyAliasMap_wf.find?_insert] at hfind
  split at hfind
  · rename_i heq
    simp at heq
    subst n
    simp [Kernel.Environment.primitives, NameSet.ofList] at hprim
    simp +decide [NameSet.contains] at hprim
  · rw [typeFamilyAliasMap,
      SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty] at hfind
    simp [SMap.find?] at hfind
    obtain ⟨rfl, rfl⟩ := hfind
    simp [Kernel.Environment.primitives, NameSet.ofList] at hprim
    simp +decide [NameSet.contains] at hprim

private def aliasFormerCtorNormalizationVEnvs : VEnvs where
  venv _ := aliasFormerTypeEnv

private theorem aliasFormerCtorNormalizationVEnvs_wf :
    aliasFormerCtorNormalizationVEnvs.WF
      aliasFormerCtorNormalizationKernelEnv where
  tr := by
    intro safety
    change TrEnv' _ aliasFormerTypeMap false aliasFormerTypeEnv
    exact aliasFormerCtorNormalization_trEnv'.sf_mono
      DefinitionSafety.le_safe
  hasPrimitives := aliasFormerCtorNormalization_hasPrimitives
  safePrimitives := aliasFormerCtorNormalization_safePrimitives
  mono := fun _ => .rfl

private def aliasFormerCtorNormalizationContext : TypeChecker.VContext :=
  TypeChecker.VContext.mk' aliasFormerCtorNormalizationVEnvs_wf
    (fuel := { whnf := 2 })

private def aliasFormerCtorNormalizationRawContext : TypeChecker.Context where
  env := aliasFormerCtorNormalizationKernelEnv
  fuel := { whnf := 2 }

private def aliasFormerCtorCheckTypeState (state : TypeChecker.State) :
    TypeChecker.State :=
  { state with
    inferTypeC := state.inferTypeC.insert
      (.const ``AliasFormer [])
      (.const ``TypeFamilyAlias []) }

/-- Insert only the raw `AliasRec` family into the replay environment. This is
the exact staging at which constructor domains are normalized. -/
private def aliasRecNormalizationAddType :
    AddInductConstant .induct recAliasMap recAliasEnv
      aliasRecRawType.toVConstVal aliasRecTypeMap aliasRecTypeEnv where
  info := aliasRecInfo
  kind_eq := by simp [aliasRecInfo, InductConstantKind.Matches]
  tr := aliasRecInfo_tr
  map_fresh := by simpa [aliasRecRawType] using aliasRecType_fresh
  env_add := rfl
  map_add := rfl

private theorem aliasRecNormalization_trEnv' :
    TrEnv' .safe aliasRecTypeMap false aliasRecTypeEnv :=
  .inductStaging aliasRecNormalizationAddType
    ⟨.succ (.succ .zero), VEnv.HasType.sort (by decide)⟩
    recAlias_trEnv'

private def aliasRecNormalizationKernelEnv : Kernel.Environment :=
  Kernel.Environment.ofConstants `_aliasRecNormalization aliasRecTypeMap

private theorem aliasRecNormalization_trEnv :
    TrEnv .safe aliasRecNormalizationKernelEnv aliasRecTypeEnv := by
  simpa [TrEnv, aliasRecNormalizationKernelEnv] using
    aliasRecNormalization_trEnv'

private theorem aliasRecNormalization_hasPrimitives :
    VEnv.HasPrimitives aliasRecTypeEnv := by
  apply TypeChecker.VEnv.HasPrimitives.of_avoids
  intro n hn
  simp only [TypeChecker.reflectedPrimitiveNames, List.mem_cons,
    List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;>
    rfl

private theorem aliasRecNormalization_safePrimitives :
    aliasRecNormalizationKernelEnv.find? n = some ci →
      Kernel.Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = [] := by
  intro hfind hprim
  change aliasRecTypeMap.find?' n = some ci at hfind
  rw [aliasRecTypeMap_wf.find?'_eq_find?,
    aliasRecTypeMap, recAliasMap_wf.find?_insert] at hfind
  split at hfind
  · rename_i heq
    simp at heq
    subst n
    simp [Kernel.Environment.primitives, NameSet.ofList] at hprim
    simp +decide [NameSet.contains] at hprim
  · rw [recAliasMap,
      SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty] at hfind
    simp [SMap.find?] at hfind
    obtain ⟨rfl, rfl⟩ := hfind
    simp [Kernel.Environment.primitives, NameSet.ofList] at hprim
    simp +decide [NameSet.contains] at hprim

private def aliasRecNormalizationVEnvs : VEnvs where
  venv _ := aliasRecTypeEnv

private theorem aliasRecNormalizationVEnvs_wf :
    aliasRecNormalizationVEnvs.WF aliasRecNormalizationKernelEnv where
  tr := by
    intro safety
    change TrEnv' _ aliasRecTypeMap false aliasRecTypeEnv
    exact aliasRecNormalization_trEnv'.sf_mono DefinitionSafety.le_safe
  hasPrimitives := aliasRecNormalization_hasPrimitives
  safePrimitives := aliasRecNormalization_safePrimitives
  mono := fun _ => .rfl

private def aliasRecNormalizationContext : TypeChecker.VContext :=
  TypeChecker.VContext.mk' aliasRecNormalizationVEnvs_wf
    (fuel := { whnf := 2 })

private def aliasRecNormalizationRawContext : TypeChecker.Context where
  env := aliasRecNormalizationKernelEnv
  fuel := { whnf := 2 }

private def aliasFormerCandidateContext : AddInductive.Context where
  env := aliasFormerNormalizationKernelEnv
  lparams := []
  safety := .safe
  allowPrimitive := false
  fuel := { whnf := 2 }

private def aliasFormerCtorCandidateContext : AddInductive.Context where
  env := aliasFormerCtorNormalizationKernelEnv
  lparams := []
  safety := .safe
  allowPrimitive := false
  fuel := { whnf := 2 }

private theorem aliasFormerNormalization_lookup :
    aliasFormerNormalizationKernelEnv.find? ``TypeFamilyAlias =
      some typeFamilyAliasInfo := by
  change typeFamilyAliasMap.find?' ``TypeFamilyAlias =
    some typeFamilyAliasInfo
  rw [typeFamilyAliasMap_wf.find?'_eq_find?, typeFamilyAliasMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  rfl

private theorem aliasFormerCtorNormalization_lookup :
    aliasFormerCtorNormalizationKernelEnv.find? ``AliasFormer =
      some aliasFormerInfo := by
  change aliasFormerTypeMap.find?' ``AliasFormer = some aliasFormerInfo
  rw [aliasFormerTypeMap_wf.find?'_eq_find?, aliasFormerTypeMap,
    typeFamilyAliasMap_wf.find?_insert]
  rfl

private theorem aliasRecNormalization_lookup :
    aliasRecNormalizationKernelEnv.find? ``RecAlias =
      some recAliasInfo := by
  change aliasRecTypeMap.find?' ``RecAlias = some recAliasInfo
  rw [aliasRecTypeMap_wf.find?'_eq_find?, aliasRecTypeMap,
    recAliasMap_wf.find?_insert, recAliasMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  rfl

private theorem aliasRecNormalization_family_lookup :
    aliasRecNormalizationKernelEnv.find? ``AliasRec =
      some aliasRecInfo := by
  change aliasRecTypeMap.find?' ``AliasRec = some aliasRecInfo
  rw [aliasRecTypeMap_wf.find?'_eq_find?, aliasRecTypeMap,
    recAliasMap_wf.find?_insert]
  rfl

private def recAliasWhnfKernelExpr : Expr :=
  recAliasInfo.instantiateValueLevelParams! [.succ .zero]

private def aliasRecFieldKernelExpr : Expr :=
  aliasRecMkInfo.type.bindingDomain!

private theorem aliasRecFieldKernelExpr_eq :
    aliasRecFieldKernelExpr =
      .app (.const ``RecAlias [.succ .zero])
        (.const ``AliasRec []) := rfl

private theorem recAliasWhnfKernelExpr_eq :
    recAliasWhnfKernelExpr =
      .lam `α (.sort (.succ .zero)) (.bvar 0) .default := by
  simp [recAliasWhnfKernelExpr, recAliasInfo,
    recAliasKernelDef, ConstantInfo.instantiateValueLevelParams!,
    ConstantInfo.levelParams, ConstantInfo.value!,
    ConstantInfo.toConstantVal,
    Expr.instantiateLevelParams_eq, Expr.instantiateLevelParamsCore',
    Level.substParams']

private def recAliasUnfoldState (state : TypeChecker.State) :
    TypeChecker.State :=
  { state with
    unfold := state.unfold.insert
      (.const ``RecAlias [.succ .zero])
      recAliasWhnfKernelExpr }

/- The following small operational equations expose only the transformer
plumbing needed to kernel-reduce the two concrete WHNF traces. -/

@[simp] private theorem normalizationRecMGet (methods context state) :
    (get : TypeChecker.RecM TypeChecker.State) methods context state =
      .ok (state, state) := rfl

@[simp] private theorem normalizationRecMReadContext
    (methods context state) :
    (readThe TypeChecker.Context : TypeChecker.RecM TypeChecker.Context)
        methods context state =
      .ok (context, state) := rfl

@[simp] private theorem normalizationRecMModify
    (f : TypeChecker.State → TypeChecker.State)
    (methods context state) :
    (modify f : TypeChecker.RecM PUnit) methods context state =
      .ok (.unit, f state) := rfl

@[simp] private theorem normalizationRecMPure
    {α} (a : α) (methods context state) :
    (pure a : TypeChecker.RecM α) methods context state =
      .ok (a, state) := rfl

@[simp] private theorem normalizationRecMBind
    {α β} (x : TypeChecker.RecM α)
    (f : α → TypeChecker.RecM β) (methods context state) :
    (x >>= f) methods context state =
      match x methods context state with
      | .error e => .error e
      | .ok (a, state') => f a methods context state' := by
  simp [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  cases h : x methods context state with
  | error => rfl
  | ok value => cases value; rfl

@[simp] private theorem normalizationRecMGetEnv
    (methods context state) :
    (liftM TypeChecker.getEnv :
        TypeChecker.RecM Kernel.Environment) methods context state =
      .ok (context.env, state) := rfl

@[simp] private theorem normalizationRecMLiftExceptOk
    {α} (a : α) (methods context state) :
    (liftM (.ok a : Except Kernel.Exception α) :
        TypeChecker.RecM α) methods context state =
      .ok (a, state) := rfl

private theorem normalizationExceptPure
    {α} (a : α) :
    (pure a : Except Kernel.Exception α) = .ok a := rfl

@[simp] private theorem typeFamilyAlias_noLooseBVars :
    (Expr.const ``TypeFamilyAlias []).hasLooseBVars = false := by
  simp [Expr.hasLooseBVars, Expr.looseBVarRange']

@[simp] private theorem aliasFormer_noLooseBVars :
    (Expr.const ``AliasFormer []).hasLooseBVars = false := by
  simp [Expr.hasLooseBVars, Expr.looseBVarRange']

@[simp] private theorem recAlias_noLooseBVars :
    (Expr.const ``RecAlias [.succ .zero]).hasLooseBVars = false := by
  simp [Expr.hasLooseBVars, Expr.looseBVarRange']

@[simp] private theorem aliasRec_noLooseBVars :
    (Expr.const ``AliasRec []).hasLooseBVars = false := by
  simp [Expr.hasLooseBVars, Expr.looseBVarRange']

@[simp] private theorem aliasRecField_noLooseBVars :
    (Expr.app
      (.const ``RecAlias [.succ .zero])
      (.const ``AliasRec [])).hasLooseBVars = false := by
  simp [Expr.hasLooseBVars, Expr.looseBVarRange']

@[simp] private theorem emptyCheckTypeCache_typeFamilyAlias :
    (({} : TypeChecker.State).inferTypeC)[
      Expr.const ``TypeFamilyAlias []]? = none := by
  exact Std.HashMap.getElem?_empty

@[simp] private theorem emptyCheckTypeCache_aliasFormer :
    (({} : TypeChecker.State).inferTypeC)[
      Expr.const ``AliasFormer []]? = none := by
  exact Std.HashMap.getElem?_empty

@[simp] private theorem emptyCheckTypeCache_recAlias :
    (({} : TypeChecker.State).inferTypeC)[
      Expr.const ``RecAlias [.succ .zero]]? = none := by
  exact Std.HashMap.getElem?_empty

@[simp] private theorem emptyCheckTypeCache_aliasRecField :
    (({} : TypeChecker.State).inferTypeC)[
      Expr.app
        (.const ``RecAlias [.succ .zero])
        (.const ``AliasRec [])]? = none := by
  exact Std.HashMap.getElem?_empty

@[simp] private theorem aliasFormerNormalization_get :
    aliasFormerNormalizationRawContext.env.get ``TypeFamilyAlias =
      .ok typeFamilyAliasInfo := by
  unfold Kernel.Environment.get
  change
    (match aliasFormerNormalizationKernelEnv.find? ``TypeFamilyAlias with
    | some ci => pure ci
    | none => throw <| Kernel.Exception.unknownConstant
        aliasFormerNormalizationKernelEnv ``TypeFamilyAlias) =
      Except.ok typeFamilyAliasInfo
  rw [aliasFormerNormalization_lookup]
  rfl

@[simp] private theorem inferConstantTypeFamilyAlias :
    TypeChecker.Inner.inferConstant aliasFormerNormalizationRawContext
        ``TypeFamilyAlias [] false =
      .ok (.sort (.succ (.succ .zero))) := by
  unfold TypeChecker.Inner.inferConstant
  rw [aliasFormerNormalization_get]
  rfl

@[simp] private theorem aliasFormerCtorNormalization_get :
    aliasFormerCtorNormalizationRawContext.env.get ``AliasFormer =
      .ok aliasFormerInfo := by
  unfold Kernel.Environment.get
  change
    (match aliasFormerCtorNormalizationKernelEnv.find? ``AliasFormer with
    | some ci => pure ci
    | none => throw <| Kernel.Exception.unknownConstant
        aliasFormerCtorNormalizationKernelEnv ``AliasFormer) =
      Except.ok aliasFormerInfo
  rw [aliasFormerCtorNormalization_lookup]
  rfl

@[simp] private theorem inferConstantAliasFormer :
    TypeChecker.Inner.inferConstant aliasFormerCtorNormalizationRawContext
        ``AliasFormer [] false =
      .ok (.const ``TypeFamilyAlias []) := by
  unfold TypeChecker.Inner.inferConstant
  rw [aliasFormerCtorNormalization_get]
  rfl

private theorem checkTypeTypeFamilyAlias :
    TypeChecker.Inner.inferType (.const ``TypeFamilyAlias []) false
        (TypeChecker.Methods.withFuel 9999)
        aliasFormerNormalizationRawContext ({} : TypeChecker.State) =
      .ok (.sort (.succ (.succ .zero)),
        aliasFormerCheckTypeState {}) := by
  change TypeChecker.Inner.inferType'
      (.const ``TypeFamilyAlias []) false
      (TypeChecker.Methods.withFuel 9998)
      aliasFormerNormalizationRawContext ({} : TypeChecker.State) =
    .ok (.sort (.succ (.succ .zero)),
      aliasFormerCheckTypeState {})
  unfold TypeChecker.Inner.inferType'
  simp [aliasFormerCheckTypeState,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

private theorem checkTypeTypeFamilyAliasCandidate :
    TypeChecker.Inner.inferType (.const ``TypeFamilyAlias []) false
        (TypeChecker.Methods.withFuel 10000)
        aliasFormerNormalizationRawContext ({} : TypeChecker.State) =
      .ok (.sort (.succ (.succ .zero)),
        aliasFormerCheckTypeState {}) := by
  change TypeChecker.Inner.inferType'
      (.const ``TypeFamilyAlias []) false
      (TypeChecker.Methods.withFuel 9999)
      aliasFormerNormalizationRawContext ({} : TypeChecker.State) =
    .ok (.sort (.succ (.succ .zero)),
      aliasFormerCheckTypeState {})
  unfold TypeChecker.Inner.inferType'
  simp [aliasFormerCheckTypeState,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

private theorem checkTypeAliasFormer :
    TypeChecker.Inner.inferType (.const ``AliasFormer []) false
        (TypeChecker.Methods.withFuel 9999)
        aliasFormerCtorNormalizationRawContext ({} : TypeChecker.State) =
      .ok (.const ``TypeFamilyAlias [],
        aliasFormerCtorCheckTypeState {}) := by
  change TypeChecker.Inner.inferType'
      (.const ``AliasFormer []) false
      (TypeChecker.Methods.withFuel 9998)
      aliasFormerCtorNormalizationRawContext ({} : TypeChecker.State) =
    .ok (.const ``TypeFamilyAlias [],
      aliasFormerCtorCheckTypeState {})
  unfold TypeChecker.Inner.inferType'
  simp [aliasFormerCtorCheckTypeState,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

private theorem checkTypeAliasFormerCandidate :
    TypeChecker.Inner.inferType (.const ``AliasFormer []) false
        (TypeChecker.Methods.withFuel 10000)
        aliasFormerCtorNormalizationRawContext ({} : TypeChecker.State) =
      .ok (.const ``TypeFamilyAlias [],
        aliasFormerCtorCheckTypeState {}) := by
  change TypeChecker.Inner.inferType'
      (.const ``AliasFormer []) false
      (TypeChecker.Methods.withFuel 9999)
      aliasFormerCtorNormalizationRawContext ({} : TypeChecker.State) =
    .ok (.const ``TypeFamilyAlias [],
      aliasFormerCtorCheckTypeState {})
  unfold TypeChecker.Inner.inferType'
  simp [aliasFormerCtorCheckTypeState,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

@[simp] private theorem aliasRecNormalization_getRecAlias :
    aliasRecNormalizationRawContext.env.get ``RecAlias =
      .ok recAliasInfo := by
  unfold Kernel.Environment.get
  change
    (match aliasRecNormalizationKernelEnv.find? ``RecAlias with
    | some ci => pure ci
    | none => throw <| Kernel.Exception.unknownConstant
        aliasRecNormalizationKernelEnv ``RecAlias) =
      Except.ok recAliasInfo
  rw [aliasRecNormalization_lookup]
  rfl

@[simp] private theorem aliasRecNormalization_getFamily :
    aliasRecNormalizationRawContext.env.get ``AliasRec =
      .ok aliasRecInfo := by
  unfold Kernel.Environment.get
  change
    (match aliasRecNormalizationKernelEnv.find? ``AliasRec with
    | some ci => pure ci
    | none => throw <| Kernel.Exception.unknownConstant
        aliasRecNormalizationKernelEnv ``AliasRec) =
      Except.ok aliasRecInfo
  rw [aliasRecNormalization_family_lookup]
  rfl

@[simp] private theorem aliasRecNormalization_checkLevelSuccZero :
    TypeChecker.Inner.checkLevel aliasRecNormalizationRawContext
      (.succ .zero) = .ok () := by
  simp [TypeChecker.Inner.checkLevel, Level.getUndefParam, Level.forEach,
    Level.hasParam_eq,
    Level.hasParam', normalizationExceptPure]

@[simp] private theorem recAliasInfo_isUnsafe :
    recAliasInfo.isUnsafe = false := rfl

@[simp] private theorem aliasRecNormalization_safety :
    aliasRecNormalizationRawContext.safety = .safe := rfl

@[simp] private theorem recAliasInfo_instantiateType :
    recAliasInfo.instantiateTypeLevelParams [.succ .zero] =
      .forallE `α (.sort (.succ .zero))
        (.sort (.succ .zero)) .default := by
  simp [recAliasInfo, recAliasKernelDef,
    ConstantInfo.instantiateTypeLevelParams,
    ConstantVal.instantiateTypeLevelParams,
    ConstantInfo.toConstantVal,
    Expr.instantiateLevelParams_eq, Expr.instantiateLevelParamsCore',
    Level.substParams']

@[simp] private theorem inferConstantRecAlias :
    TypeChecker.Inner.inferConstant aliasRecNormalizationRawContext
        ``RecAlias [.succ .zero] false =
      .ok (.forallE `α (.sort (.succ .zero))
        (.sort (.succ .zero)) .default) := by
  unfold TypeChecker.Inner.inferConstant
  rw [aliasRecNormalization_getRecAlias]
  simp [recAliasInfo, recAliasKernelDef,
    Bind.bind, Except.bind,
    normalizationExceptPure,
    aliasRecNormalization_checkLevelSuccZero,
    ConstantInfo.levelParams, ConstantInfo.isUnsafe,
    ConstantInfo.instantiateTypeLevelParams,
    ConstantInfo.toConstantVal,
    ConstantVal.instantiateTypeLevelParams,
    Expr.instantiateLevelParams_eq, Expr.instantiateLevelParamsCore',
    Level.substParams']

@[simp] private theorem inferConstantAliasRec :
    TypeChecker.Inner.inferConstant aliasRecNormalizationRawContext
        ``AliasRec [] false =
      .ok (.sort (.succ .zero)) := by
  unfold TypeChecker.Inner.inferConstant
  rw [aliasRecNormalization_getFamily]
  rfl

@[simp] private theorem normalizationWhnfCoreConst
    (methods context state n ls) :
    (TypeChecker.Inner.whnfCore' (.const n ls)
        (cheapRec := false) (cheapProj := false))
        methods context state =
      .ok (.const n ls, state) := rfl

@[simp] private theorem normalizationWhnfCoreSort
    (methods context state u) :
    (TypeChecker.Inner.whnfCore' (.sort u)
        (cheapRec := false) (cheapProj := false))
        methods context state =
      .ok (.sort u, state) := rfl

@[simp] private theorem normalizationWhnfCoreLam
    (methods context state name ty body bi) :
    (TypeChecker.Inner.whnfCore' (.lam name ty body bi)
        (cheapRec := false) (cheapProj := false))
        methods context state =
      .ok (.lam name ty body bi, state) := rfl

@[simp] private theorem normalizationReduceNativeConst
    (env methods context state n ls) :
    (liftM (TypeChecker.Inner.reduceNative env (.const n ls)) :
        TypeChecker.RecM (Option Expr)) methods context state =
      .ok (none, state) := rfl

@[simp] private theorem normalizationReduceNativeSort
    (env methods context state u) :
    (liftM (TypeChecker.Inner.reduceNative env (.sort u)) :
        TypeChecker.RecM (Option Expr)) methods context state =
      .ok (none, state) := rfl

@[simp] private theorem normalizationReduceNativeLam
    (env methods context state name ty body bi) :
    (liftM (TypeChecker.Inner.reduceNative env (.lam name ty body bi)) :
        TypeChecker.RecM (Option Expr)) methods context state =
      .ok (none, state) := rfl

@[simp] private theorem normalizationReduceNatConst
    (methods context state n ls) :
    TypeChecker.Inner.reduceNat (.const n ls) methods context state =
      .ok (none, state) := rfl

@[simp] private theorem normalizationReduceNatSort
    (methods context state u) :
    TypeChecker.Inner.reduceNat (.sort u) methods context state =
      .ok (none, state) := rfl

@[simp] private theorem normalizationReduceNatLam
    (methods context state name ty body bi) :
    TypeChecker.Inner.reduceNat (.lam name ty body bi)
        methods context state =
      .ok (none, state) := rfl

@[simp] private theorem normalizationUnfoldSort
    (methods context state u) :
    TypeChecker.Inner.unfoldDefinition (.sort u) methods context state =
      .ok (none, state) := rfl

@[simp] private theorem normalizationUnfoldLam
    (methods context state name ty body bi) :
    TypeChecker.Inner.unfoldDefinition (.lam name ty body bi)
        methods context state =
      .ok (none, state) := rfl

private theorem unfoldTypeFamilyAlias (methods state) :
    TypeChecker.Inner.unfoldDefinition (.const ``TypeFamilyAlias [])
        methods aliasFormerNormalizationRawContext state =
      .ok (some (.sort (.succ .zero)), state) := by
  change
    TypeChecker.Inner.unfoldDefinitionCore (.const ``TypeFamilyAlias [])
        methods aliasFormerNormalizationRawContext state =
      .ok (some (.sort (.succ .zero)), state)
  simp [TypeChecker.Inner.unfoldDefinitionCore, TypeChecker.Inner.isDelta,
    Expr.getAppFn, aliasFormerNormalizationRawContext,
    aliasFormerNormalization_lookup, Bind.bind, ReaderT.bind,
    StateT.bind, Except.bind, typeFamilyAliasInfo,
    typeFamilyAliasKernelDef, ConstantInfo.hasValue,
    ConstantInfo.numLevelParams,
    ConstantInfo.instantiateValueLevelParams!, ConstantInfo.levelParams,
    ConstantInfo.value!, ConstantInfo.toConstantVal,
    Expr.instantiateLevelParams]

private theorem unfoldRecAliasInitial (methods) :
    TypeChecker.Inner.unfoldDefinition
        (.const ``RecAlias [.succ .zero])
        methods aliasRecNormalizationRawContext ({} : TypeChecker.State) =
      .ok (some recAliasWhnfKernelExpr, recAliasUnfoldState {}) := by
  change
    TypeChecker.Inner.unfoldDefinitionCore
        (.const ``RecAlias [.succ .zero])
        methods aliasRecNormalizationRawContext ({} : TypeChecker.State) =
      .ok (some recAliasWhnfKernelExpr, recAliasUnfoldState {})
  simp [TypeChecker.Inner.unfoldDefinitionCore, TypeChecker.Inner.isDelta,
    Expr.getAppFn, aliasRecNormalizationRawContext,
    aliasRecNormalization_lookup, Bind.bind, ReaderT.bind,
    StateT.bind, Except.bind, recAliasInfo, recAliasKernelDef,
    ConstantInfo.hasValue, ConstantInfo.numLevelParams,
    ConstantInfo.instantiateValueLevelParams!, ConstantInfo.levelParams,
    ConstantInfo.value!, ConstantInfo.toConstantVal,
    Expr.instantiateLevelParams, recAliasWhnfKernelExpr,
    recAliasUnfoldState]

private theorem unfoldRecAliasCoreInitial (methods) :
    TypeChecker.Inner.unfoldDefinitionCore
        (.const ``RecAlias [.succ .zero])
        methods aliasRecNormalizationRawContext ({} : TypeChecker.State) =
      .ok (some recAliasWhnfKernelExpr, recAliasUnfoldState {}) := by
  change
    TypeChecker.Inner.unfoldDefinition
        (.const ``RecAlias [.succ .zero])
        methods aliasRecNormalizationRawContext ({} : TypeChecker.State) =
      .ok (some recAliasWhnfKernelExpr, recAliasUnfoldState {})
  exact unfoldRecAliasInitial methods

private theorem unfoldAliasRecFieldInitial (methods) :
    TypeChecker.Inner.unfoldDefinition aliasRecFieldKernelExpr
        methods aliasRecNormalizationRawContext ({} : TypeChecker.State) =
      .ok (some (.app recAliasWhnfKernelExpr
        (.const ``AliasRec [])), recAliasUnfoldState {}) := by
  rw [aliasRecFieldKernelExpr_eq]
  unfold TypeChecker.Inner.unfoldDefinition
  simp only [Expr.isApp, if_true]
  rw [show
    (Expr.app (.const ``RecAlias [.succ .zero])
      (.const ``AliasRec [])).getAppFn =
        .const ``RecAlias [.succ .zero] by rfl]
  simp only [normalizationRecMBind]
  rw [unfoldRecAliasCoreInitial]
  rw [show
    (Expr.app (.const ``RecAlias [.succ .zero])
      (.const ``AliasRec [])).getAppRevArgs =
        #[.const ``AliasRec []] by rfl]
  simp only [normalizationRecMPure]
  rw [Expr.mkAppRevRange_eq
    (l₁ := []) (l₂ := [.const ``AliasRec []]) (l₃ := [])
    (by simp) (by rfl) (by rfl)]
  rfl

private theorem whnfLoopTypeFamilyAlias (methods state) :
    TypeChecker.Inner.whnf'.loop (.const ``TypeFamilyAlias []) 2
        methods aliasFormerNormalizationRawContext state =
      .ok (.sort (.succ .zero), state) := by
  unfold TypeChecker.Inner.whnf'.loop
  simp [unfoldTypeFamilyAlias]
  unfold TypeChecker.Inner.whnf'.loop
  simp

private theorem whnfLoopRecAlias (methods) :
    TypeChecker.Inner.whnf'.loop
        (.const ``RecAlias [.succ .zero]) 2
        methods aliasRecNormalizationRawContext ({} : TypeChecker.State) =
      .ok (recAliasWhnfKernelExpr, recAliasUnfoldState {}) := by
  unfold TypeChecker.Inner.whnf'.loop
  simp [unfoldRecAliasInitial]
  unfold TypeChecker.Inner.whnf'.loop
  rw [recAliasWhnfKernelExpr_eq]
  simp

/-- The actual verified WHNF computation for the raw AliasFormer family
result. -/
theorem aliasFormerFamily_whnf :
    ∃ state : TypeChecker.State,
      TypeChecker.Inner.whnf' (.const ``TypeFamilyAlias [])
          (TypeChecker.Methods.withFuel 9999)
          aliasFormerNormalizationRawContext ({} : TypeChecker.State) =
        .ok (.sort (.succ .zero), state) := by
  unfold TypeChecker.Inner.whnf'
  simp
  rw [show (if aliasFormerNormalizationRawContext.eagerReduce then
      aliasFormerNormalizationRawContext.fuel.whnfEager
    else aliasFormerNormalizationRawContext.fuel.whnf) = 2 by rfl]
  rw [whnfLoopTypeFamilyAlias]
  simp [Functor.map, StateT.map, Except.map]

/-- The full non-inference-only checker run for the raw AliasFormer family
type. The returned sort is recorded together with the checker's cache update,
rather than supplied as an external Theory premise. -/
theorem aliasFormerFamily_checkType :
    ∃ state : TypeChecker.State,
      TypeChecker.Inner.inferType aliasFormerInfo.type false
          (TypeChecker.Methods.withFuel 9999)
          aliasFormerNormalizationContext.toContext
          ({} : TypeChecker.State) =
        .ok (.sort (.succ (.succ .zero)), state) := by
  exact ⟨aliasFormerCheckTypeState {}, by
    simpa [aliasFormerInfo, aliasFormerNormalizationContext,
      TypeChecker.VContext.mk', aliasFormerNormalizationRawContext] using
      checkTypeTypeFamilyAlias⟩

/-- The exact full checker run for the actual AliasFormer constructor type,
staged after insertion of the raw family. The checker returns the retained
family-type alias rather than silently normalizing it. -/
theorem aliasFormerCtor_checkType :
    ∃ state : TypeChecker.State,
      TypeChecker.Inner.inferType aliasFormerMkInfo.type false
          (TypeChecker.Methods.withFuel 9999)
          aliasFormerCtorNormalizationContext.toContext
          ({} : TypeChecker.State) =
        .ok (.const ``TypeFamilyAlias [], state) := by
  exact ⟨aliasFormerCtorCheckTypeState {}, by
    simpa [aliasFormerMkInfo, aliasFormerCtorNormalizationContext,
      TypeChecker.VContext.mk',
      aliasFormerCtorNormalizationRawContext] using
      checkTypeAliasFormer⟩

/-- The actual verified WHNF computation for the reducible `RecAlias`
head at the universe used by `AliasRec.mk`. -/
theorem recAlias_whnf :
    ∃ state : TypeChecker.State,
      TypeChecker.Inner.whnf'
          (.const ``RecAlias [.succ .zero])
          (TypeChecker.Methods.withFuel 9999)
          aliasRecNormalizationRawContext ({} : TypeChecker.State) =
        .ok (recAliasWhnfKernelExpr, state) := by
  unfold TypeChecker.Inner.whnf'
  simp
  rw [show (if aliasRecNormalizationRawContext.eagerReduce then
      aliasRecNormalizationRawContext.fuel.whnfEager
    else aliasRecNormalizationRawContext.fuel.whnf) = 2 by rfl]
  rw [whnfLoopRecAlias]
  simp [Functor.map, StateT.map, Except.map]

private theorem aliasFormerFamily_whnfM :
    TypeChecker.M.run aliasFormerNormalizationKernelEnv .safe {} []
        { whnf := 2 } (TypeChecker.whnf aliasFormerInfo.type) =
      .ok (.sort (.succ .zero)) := by
  change
    Except.map (fun x : Expr × TypeChecker.State => x.1)
      (TypeChecker.Inner.whnf'
        (.const ``TypeFamilyAlias [])
        (TypeChecker.Methods.withFuel 9999)
        aliasFormerNormalizationRawContext ({} : TypeChecker.State)) =
        Except.ok (.sort (.succ .zero))
  obtain ⟨state, hrun⟩ := aliasFormerFamily_whnf
  rw [hrun]
  rfl

private theorem aliasFormerFamily_checkTypeM :
    TypeChecker.M.run aliasFormerNormalizationKernelEnv .safe {} []
        { whnf := 2 } (TypeChecker.checkType aliasFormerInfo.type) =
      .ok (.sort (.succ (.succ .zero))) := by
  change
    Except.map (fun x : Expr × TypeChecker.State => x.1)
      (TypeChecker.Inner.inferType aliasFormerInfo.type false
        (TypeChecker.Methods.withFuel 10000)
        aliasFormerNormalizationRawContext ({} : TypeChecker.State)) =
      Except.ok (.sort (.succ (.succ .zero)))
  rw [show aliasFormerInfo.type =
    .const ``TypeFamilyAlias [] by rfl]
  rw [checkTypeTypeFamilyAliasCandidate]
  rfl

private theorem aliasFormerCtor_checkTypeM :
    TypeChecker.M.run aliasFormerCtorNormalizationKernelEnv .safe {} []
        { whnf := 2 } (TypeChecker.checkType aliasFormerMkInfo.type) =
      .ok (.const ``TypeFamilyAlias []) := by
  change
    Except.map (fun x : Expr × TypeChecker.State => x.1)
      (TypeChecker.Inner.inferType aliasFormerMkInfo.type false
        (TypeChecker.Methods.withFuel 10000)
        aliasFormerCtorNormalizationRawContext ({} : TypeChecker.State)) =
      Except.ok (.const ``TypeFamilyAlias [])
  rw [show aliasFormerMkInfo.type =
    .const ``AliasFormer [] by rfl]
  rw [checkTypeAliasFormerCandidate]
  rfl

private def aliasFormerFamilyCandidateStep :
    AddInductive.CandidateWhnfStep where
  context := aliasFormerCandidateContext
  source := aliasFormerInfo.type
  result := .sort (.succ .zero)

private theorem aliasFormerFamilyCandidateStep_valid :
    aliasFormerFamilyCandidateStep.Valid := by
  change
    TypeChecker.M.run aliasFormerNormalizationKernelEnv .safe {} []
        { whnf := 2 } (TypeChecker.whnf aliasFormerInfo.type) =
      .ok (.sort (.succ .zero))
  exact aliasFormerFamily_whnfM

private def aliasFormerFamilyCheckTypeStep :
    AddInductive.CandidateCheckTypeStep where
  context := aliasFormerCandidateContext
  source := aliasFormerInfo.type
  inferred := .sort (.succ (.succ .zero))

private theorem aliasFormerFamilyCheckTypeStep_valid :
    aliasFormerFamilyCheckTypeStep.Valid := by
  change
    TypeChecker.M.run aliasFormerNormalizationKernelEnv .safe {} []
        { whnf := 2 } (TypeChecker.checkType aliasFormerInfo.type) =
      .ok (.sort (.succ (.succ .zero)))
  exact aliasFormerFamily_checkTypeM

private def aliasFormerCtorCheckTypeStep :
    AddInductive.CandidateCheckTypeStep where
  context := aliasFormerCtorCandidateContext
  source := aliasFormerMkInfo.type
  inferred := .const ``TypeFamilyAlias []

private theorem aliasFormerCtorCheckTypeStep_valid :
    aliasFormerCtorCheckTypeStep.Valid := by
  change
    TypeChecker.M.run aliasFormerCtorNormalizationKernelEnv .safe {} []
        { whnf := 2 } (TypeChecker.checkType aliasFormerMkInfo.type) =
      .ok (.const ``TypeFamilyAlias [])
  exact aliasFormerCtor_checkTypeM

private def aliasFormerFamilyCandidate :
    AddInductive.CandidateExpr aliasFormerInfo.type :=
  ⟨aliasFormerCandidateContext,
    .terminal aliasFormerCandidateContext aliasFormerInfo.type
      (.sort (.succ (.succ .zero))) (.sort (.succ .zero))
      aliasFormerFamilyCheckTypeStep_valid
      aliasFormerFamilyCandidateStep_valid⟩

/-- The generic candidate traversal retains the exact context, input, and
result of the actual AliasFormer family WHNF observation. -/
theorem aliasFormerFamily_candidateTrace :
    AddInductive.buildCandidateExpr aliasFormerInfo.type
        aliasFormerCandidateContext =
      .ok aliasFormerFamilyCandidate := by
  apply AddInductive.buildCandidateExpr_of_whnf_nonForall
  · decide
  · rfl

/-- Erasing the retained trace produces the expected AliasFormer analysis
view at the same checker boundary. -/
theorem aliasFormerFamily_candidate :
    AddInductive.normalizeCandidateExpr aliasFormerInfo.type
        aliasFormerCandidateContext =
      .ok (.sort (.succ .zero)) := by
  apply AddInductive.normalizeCandidateExpr_of_whnf_nonForall
  · decide
  · simpa [aliasFormerCandidateContext] using
      aliasFormerFamily_checkTypeM
  · simpa [aliasFormerCandidateContext] using
      aliasFormerFamily_whnfM
  · rfl

private def aliasRecFieldFnType : Expr :=
  .forallE `α (.sort (.succ .zero))
    (.sort (.succ .zero)) .default

@[simp] private theorem aliasRecFieldFnType_isForall :
    aliasRecFieldFnType.isForall = true := rfl

@[simp] private theorem aliasRecFieldFnType_bindingDomain :
    aliasRecFieldFnType.bindingDomain! =
      .sort (.succ .zero) := rfl

@[simp] private theorem aliasRecFieldFnType_instantiatedBody :
    aliasRecFieldFnType.bindingBody!.instantiate1
        (.const ``AliasRec []) =
      .sort (.succ .zero) := by
  simp [aliasRecFieldFnType, Expr.bindingBody!,
    Expr.instantiate1_eq,
    Expr.instantiate1']

@[simp] private theorem aliasRecFamily_notEagerReduce :
    (Expr.const ``AliasRec []).isAppOfArity ``eagerReduce 2 =
      false := rfl

private def aliasRecFieldFnState (state : TypeChecker.State) :
    TypeChecker.State :=
  { state with
    inferTypeC := state.inferTypeC.insert
      (.const ``RecAlias [.succ .zero]) aliasRecFieldFnType }

private def aliasRecFieldArgState (state : TypeChecker.State) :
    TypeChecker.State :=
  { state with
    inferTypeC := state.inferTypeC.insert
      (.const ``AliasRec []) (.sort (.succ .zero)) }

private def aliasRecFieldResultState (state : TypeChecker.State) :
    TypeChecker.State :=
  { state with
    inferTypeC := state.inferTypeC.insert
      aliasRecFieldKernelExpr (.sort (.succ .zero)) }

@[simp] private theorem aliasRecFieldArgState_eqvManager :
    (aliasRecFieldArgState
      (aliasRecFieldFnState {})).eqvManager = {} := rfl

@[simp] private theorem aliasRecFieldFnCache_miss :
    (({} : Lean4Lean.InferCache).insert
      (Expr.const ``RecAlias [.succ .zero]) aliasRecFieldFnType)[
        Expr.const ``AliasRec []]? = none := by
  rw [Std.HashMap.getElem?_insert]
  have h :
      (Expr.const ``RecAlias [.succ .zero] ==
        Expr.const ``AliasRec []) = false := by
    change Expr.eqv
      (Expr.const ``RecAlias [.succ .zero])
      (Expr.const ``AliasRec []) = false
    rw [Expr.eqv_eq]
    rfl
  rw [h]
  exact Std.HashMap.getElem?_empty

@[simp] private theorem aliasRecFieldFnState_cache_miss :
    (aliasRecFieldFnState {}).inferTypeC[
      Expr.const ``AliasRec []]? = none := by
  change
    (({} : Lean4Lean.InferCache).insert
      (Expr.const ``RecAlias [.succ .zero]) aliasRecFieldFnType)[
        Expr.const ``AliasRec []]? = none
  exact aliasRecFieldFnCache_miss

private theorem aliasRecEmptyEqv_isEquivSort :
    ∃ m : EquivManager,
      EquivManager.isEquiv true
          (.sort (.succ .zero)) (.sort (.succ .zero))
          ({} : EquivManager) =
        (true, m) := by
  let r := EquivManager.isEquiv true
    (.sort (.succ .zero)) (.sort (.succ .zero))
    ({} : EquivManager)
  refine ⟨r.2, Prod.ext ?_ rfl⟩
  dsimp only [r]
  rw [EquivManager.isEquiv.eq_def]
  by_cases h :
      ptrEqExpr (.sort (.succ .zero)) (.sort (.succ .zero)) = true
  · rw [if_pos h]
    rfl
  · rw [if_neg h]
    simp [Expr.isBVar, StateT.pure, pure, Bind.bind, StateT.bind,
      EquivManager.toNode, EquivManager.find, EquivManager.merge]

private def aliasRecWithEqvManager
    (state : TypeChecker.State) (m : EquivManager) :
    TypeChecker.State :=
  { state with eqvManager := m }

private theorem quickIsDefEqSort
    (methods : TypeChecker.Methods)
    (context : TypeChecker.Context)
    (initial : TypeChecker.State)
    (heqv : initial.eqvManager = {}) :
    ∃ state : TypeChecker.State,
      TypeChecker.Inner.quickIsDefEq
          (.sort (.succ .zero)) (.sort (.succ .zero)) true
          methods context initial =
        .ok (.true, state) := by
  obtain ⟨m, hm⟩ := aliasRecEmptyEqv_isEquivSort
  refine ⟨aliasRecWithEqvManager initial m, ?_⟩
  unfold TypeChecker.Inner.quickIsDefEq
  simp [modifyGet, MonadStateOf.modifyGet, monadLift,
    MonadLift.monadLift, StateT.modifyGet, pure, ReaderT.pure,
    StateT.pure, Except.pure, heqv, hm, aliasRecWithEqvManager,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

private theorem isDefEqCoreSort
    (methods : TypeChecker.Methods)
    (context : TypeChecker.Context)
    (initial : TypeChecker.State)
    (heqv : initial.eqvManager = {}) :
    ∃ state : TypeChecker.State,
      TypeChecker.Inner.isDefEqCore'
          (.sort (.succ .zero)) (.sort (.succ .zero))
          methods context initial =
        .ok (true, state) := by
  obtain ⟨state, hr⟩ :=
    quickIsDefEqSort methods context initial heqv
  refine ⟨state, ?_⟩
  unfold TypeChecker.Inner.isDefEqCore'
  simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [hr]
  rfl

private def aliasRecAfterAddEquiv
    (state : TypeChecker.State) : TypeChecker.State :=
  { state with
    eqvManager := state.eqvManager.addEquiv
      (.sort (.succ .zero)) (.sort (.succ .zero)) }

private theorem isDefEqSort
    (context : TypeChecker.Context)
    (initial : TypeChecker.State)
    (heqv : initial.eqvManager = {}) :
    ∃ state : TypeChecker.State,
      TypeChecker.Inner.isDefEq
          (.sort (.succ .zero)) (.sort (.succ .zero))
          (TypeChecker.Methods.withFuel 9998) context initial =
        .ok (true, state) := by
  obtain ⟨state, hr⟩ :=
    isDefEqCoreSort (TypeChecker.Methods.withFuel 9997)
      context initial heqv
  have hr' :
      TypeChecker.Inner.isDefEqCore
          (.sort (.succ .zero)) (.sort (.succ .zero))
          (TypeChecker.Methods.withFuel 9998) context initial =
        .ok (true, state) := by
    change
      TypeChecker.Inner.isDefEqCore'
          (.sort (.succ .zero)) (.sort (.succ .zero))
          (TypeChecker.Methods.withFuel 9997) context initial =
        .ok (true, state)
    exact hr
  refine ⟨aliasRecAfterAddEquiv state, ?_⟩
  unfold TypeChecker.Inner.isDefEq
  simp only [Bind.bind, ReaderT.bind, StateT.bind, Except.bind]
  rw [hr']
  rfl

private theorem inferTypeRecAliasInitial :
    TypeChecker.Inner.inferType'
        (.const ``RecAlias [.succ .zero]) false
        (TypeChecker.Methods.withFuel 9998)
        aliasRecNormalizationRawContext ({} : TypeChecker.State) =
      .ok (aliasRecFieldFnType, aliasRecFieldFnState {}) := by
  unfold TypeChecker.Inner.inferType'
  simp [aliasRecFieldFnType, aliasRecFieldFnState,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

private theorem inferTypeAliasRecAfterRecAlias :
    TypeChecker.Inner.inferType'
        (.const ``AliasRec []) false
        (TypeChecker.Methods.withFuel 9998)
        aliasRecNormalizationRawContext (aliasRecFieldFnState {}) =
      .ok (.sort (.succ .zero),
        aliasRecFieldArgState (aliasRecFieldFnState {})) := by
  unfold TypeChecker.Inner.inferType'
  simp [aliasRecFieldArgState, Bind.bind, ReaderT.bind,
    StateT.bind, Except.bind]

/-- The exact full checker run for the raw `RecAlias AliasRec` constructor
field in the post-family environment. -/
theorem aliasRecField_checkType :
    ∃ state : TypeChecker.State,
      TypeChecker.Inner.inferType aliasRecFieldKernelExpr false
          (TypeChecker.Methods.withFuel 9999)
          aliasRecNormalizationRawContext ({} : TypeChecker.State) =
        .ok (.sort (.succ .zero), state) := by
  change ∃ state : TypeChecker.State,
    TypeChecker.Inner.inferType' aliasRecFieldKernelExpr false
        (TypeChecker.Methods.withFuel 9998)
        aliasRecNormalizationRawContext ({} : TypeChecker.State) =
      .ok (.sort (.succ .zero), state)
  rw [aliasRecFieldKernelExpr_eq]
  unfold TypeChecker.Inner.inferType'
  simp only [aliasRecField_noLooseBVars, Bool.false_eq_true, if_false, cond,
    normalizationRecMPure, normalizationRecMGet,
    Std.HashMap.getElem?_empty, normalizationRecMBind]
  rw [inferTypeRecAliasInitial]
  simp only
    [TypeChecker.Inner.ensureForallCore,
      aliasRecFieldFnType_isForall, if_true, normalizationRecMPure]
  rw [inferTypeAliasRecAfterRecAlias]
  obtain ⟨eqState, heq⟩ :=
    isDefEqSort aliasRecNormalizationRawContext
      (aliasRecFieldArgState (aliasRecFieldFnState {}))
      aliasRecFieldArgState_eqvManager
  simp only [aliasRecFamily_notEagerReduce, Bool.false_eq_true,
    if_false, aliasRecFieldFnType_bindingDomain,
    normalizationRecMBind]
  rw [heq]
  rw [aliasRecFieldFnType_instantiatedBody]
  refine ⟨aliasRecFieldResultState eqState, ?_⟩
  simp [aliasRecFieldResultState, aliasRecFieldKernelExpr_eq,
    Bind.bind, ReaderT.bind, StateT.bind, Except.bind]

/-- The paired full-check/WHNF interpretation of the retained AliasFormer
family node.  Both semantic runs are obtained from the candidate's exact
observations in one verified context. -/
private def aliasFormerFamilyCandidateNodeRun :
    TypeChecker.CandidateNodeRun typeFamilyAliasEnv [] []
      aliasFormerCandidateContext aliasFormerInfo.type
      (.sort (.succ (.succ .zero))) (.sort (.succ .zero))
      aliasFormerRawType.type aliasFormerViewType.type
      (.sort (.succ (.succ .zero))) := by
  exact TypeChecker.CandidateNodeRun.ofCandidate
    aliasFormerCandidateContext aliasFormerInfo.type
    (.sort (.succ (.succ .zero))) (.sort (.succ .zero))
    aliasFormerFamilyCheckTypeStep_valid
    aliasFormerFamilyCandidateStep_valid
    aliasFormerNormalizationContext (by rfl)
    rfl rfl rfl TypeChecker.VState.WF.empty
    (.const rfl rfl rfl) (.sort rfl)
    (by
      have hs : TrExprS typeFamilyAliasEnv [] []
          (.sort (.succ .zero)) (.sort (.succ .zero)) := .sort rfl
      exact ⟨_, hs, ⟨_, VEnv.HasType.sort (by decide)⟩⟩)
    10000 9999 (by rfl) (by rfl)

/-- Verified family-result normalization leaf for AliasFormer. -/
def aliasFormerFamilyWhnfRun :
    TypeChecker.WhnfRun typeFamilyAliasEnv [] []
      aliasFormerInfo.type (.sort (.succ .zero))
      aliasFormerRawType.type aliasFormerViewType.type :=
  aliasFormerFamilyCandidateNodeRun.whnf

/-- Verified full-check certificate for the raw AliasFormer family type. -/
def aliasFormerFamilyCheckTypeRun :
    TypeChecker.CheckTypeRun typeFamilyAliasEnv [] []
      aliasFormerInfo.type (.sort (.succ (.succ .zero)))
      aliasFormerRawType.type (.sort (.succ (.succ .zero))) :=
  aliasFormerFamilyCandidateNodeRun.check

/-- Recursive semantic interpretation of the exact source-indexed candidate
trace.  This terminal fixture is the base case used by the generic Pi
interpreter for larger metadata. -/
private def aliasFormerFamilyCandidateRun :
    TypeChecker.CandidateExprRun typeFamilyAliasEnv []
      aliasFormerFamilyCandidate.trace []
      aliasFormerRawType.type aliasFormerViewType.type
      (.sort (.succ (.succ .zero))) :=
  .terminal aliasFormerFamilyCandidateNodeRun

/-- The generic interpreter retains the strict translation of the raw
candidate endpoint. -/
theorem aliasFormerFamily_candidateSource_tr :
    TrExprS typeFamilyAliasEnv [] [] aliasFormerInfo.type
      aliasFormerRawType.type :=
  aliasFormerFamilyCandidateRun.source_tr

/-- The reconstructed candidate endpoint is also tied back to the concrete
kernel WHNF result, closing the source/view translation pair. -/
theorem aliasFormerFamily_candidateView_tr :
    TrExpr typeFamilyAliasEnv [] [] (.sort (.succ .zero))
      aliasFormerViewType.type := by
  simpa [aliasFormerFamilyCandidate,
    AddInductive.CandidateExprTrace.view] using
    aliasFormerFamilyCandidateRun.view_tr

/-- Verified full-check certificate for the actual AliasFormer constructor
type in the post-family environment. -/
def aliasFormerCtorCheckTypeRun :
    TypeChecker.CheckTypeRun aliasFormerTypeEnv [] []
      aliasFormerMkInfo.type (.const ``TypeFamilyAlias [])
      aliasFormerRawType.ctors[0].type
      (.const ``TypeFamilyAlias []) := by
  exact TypeChecker.CheckTypeRun.ofCandidateStep
    aliasFormerCtorCheckTypeStep aliasFormerCtorCheckTypeStep_valid
    aliasFormerCtorNormalizationContext (by rfl)
    rfl rfl rfl TypeChecker.VState.WF.empty
    (.const rfl rfl rfl) (.const rfl rfl rfl)
    10000 (by rfl)

/-- The actual AliasFormer constructor type is typed by the verified full
checker in the post-family environment. -/
theorem aliasFormerCtor_hasType_checked :
    aliasFormerTypeEnv.HasType 0 []
      aliasFormerRawType.ctors[0].type
      (.const ``TypeFamilyAlias []) :=
  aliasFormerCtorCheckTypeRun.hasType

/-- The raw AliasFormer family is a Theory type because the verified checker
actually accepted it and inferred a sort. -/
theorem aliasFormerFamily_isType_checked :
    typeFamilyAliasEnv.IsType 0 [] aliasFormerRawType.type :=
  aliasFormerFamilyCheckTypeRun.isType

/-- Verified delta-normalization leaf for `RecAlias.{1}`. -/
def recAliasWhnfRun :
    TypeChecker.WhnfRun aliasRecTypeEnv [] []
      (.const ``RecAlias [.succ .zero])
      recAliasWhnfKernelExpr
      (.const ``RecAlias [.succ .zero])
      (.lam (.sort (.succ .zero)) (.bvar 0)) where
  context := aliasRecNormalizationContext
  venv_eq := rfl
  lparams_eq := rfl
  vlctx_eq := rfl
  state_wf := TypeChecker.VState.WF.empty
  lhs_tr := .const rfl rfl rfl
  rhs_tr := by
    have hs : TrExprS aliasRecTypeEnv [] []
        recAliasWhnfKernelExpr
        (.lam (.sort (.succ .zero)) (.bvar 0)) := by
      rw [recAliasWhnfKernelExpr_eq]
      exact .lam
        ⟨_, VEnv.HasType.sort (by decide)⟩
        (.sort rfl) (.bvar rfl)
    exact ⟨_, hs, ⟨_,
      VEnv.HasType.lam
        (VEnv.HasType.sort (by decide))
        (VEnv.HasType.bvar .zero)⟩⟩
  recursionFuel := 9999
  run_eq := by
    simpa [aliasRecNormalizationContext, TypeChecker.VContext.mk',
      aliasRecNormalizationRawContext] using
      recAlias_whnf

private theorem recAliasConst_hasType :
    aliasRecTypeEnv.HasType 0 []
      (.const ``RecAlias [.succ .zero])
      (.forallE (.sort (.succ .zero)) (.sort (.succ .zero))) := by
  have hAlias : aliasRecTypeEnv.constants ``RecAlias =
      some (vconst(type_of% @RecAlias)) := rfl
  type_tac

private theorem aliasRecConst_hasType :
    aliasRecTypeEnv.HasType 0 []
      (.const ``AliasRec []) (.sort (.succ .zero)) := by
  exact .constDF
    (VEnv.addConst_self (show
      recAliasEnv.addConst aliasRecRawType.name
      aliasRecRawType.toVConstant = some aliasRecTypeEnv from rfl))
    (fun _ h => nomatch h) (fun _ h => nomatch h) rfl .nil

/-- Verified full-check certificate for the actual raw recursive field in the
exact environment produced by inserting `AliasRec`. -/
def aliasRecFieldCheckTypeRun :
    TypeChecker.CheckTypeRun aliasRecTypeEnv [] []
      aliasRecFieldKernelExpr (.sort (.succ .zero))
      aliasRecRawField (.sort (.succ .zero)) where
  context := aliasRecNormalizationContext
  venv_eq := rfl
  lparams_eq := rfl
  vlctx_eq := rfl
  state_wf := TypeChecker.VState.WF.empty
  expr_tr := .app recAliasConst_hasType aliasRecConst_hasType
    (.const rfl rfl rfl) (.const rfl rfl rfl)
  inferred_tr := .sort rfl
  recursionFuel := 9999
  run_eq := by
    simpa [aliasRecNormalizationContext, TypeChecker.VContext.mk',
      aliasRecNormalizationRawContext] using
      aliasRecField_checkType

/-- The raw recursive field is typed by an exact full checker execution in
the post-family environment. -/
theorem aliasRecField_hasType_checked :
    aliasRecTypeEnv.HasType 0 []
      aliasRecRawField (.sort (.succ .zero)) :=
  aliasRecFieldCheckTypeRun.hasType

private def aliasRecFieldEvidenceBase :
    TypeChecker.DefEqEvidence aliasRecTypeEnv 0 []
      aliasRecRawField (.const ``AliasRec []) (.sort (.succ .zero)) := by
  exact .trans
    (.app
      (.whnf recAliasWhnfRun recAliasConst_hasType)
      (.refl aliasRecConst_hasType))
    (.beta (VEnv.HasType.bvar .zero) aliasRecConst_hasType)

private def aliasRecFieldEvidence :
    TypeChecker.DefEqEvidence aliasRecTypeEnv 0 []
      aliasRecRawField (.const ``AliasRec []) (.sort (.succ .zero)) :=
  .trans (.refl aliasRecField_hasType_checked)
    aliasRecFieldEvidenceBase

private def aliasRecCtorEvidence :
    ∃ A, TypeChecker.DefEqEvidence aliasRecTypeEnv 0 []
      aliasRecRawType.ctors[0].type aliasRecViewCtor.type A := by
  exact ⟨.sort (.imax (.succ .zero) (.succ .zero)),
    .forallE aliasRecFieldEvidence
      (.refl (aliasRecResult_hasType rfl))⟩

/-- Complete checker-produced semantic normalization certificate for
AliasFormer. -/
def aliasFormerNormalizationRun :
    VInductDecl.NormalizationRun aliasFormerNormalization
      typeFamilyAliasEnv := by
  refine {
    raw := aliasFormerRawType
    view := aliasFormerViewType
    source_types_eq := rfl
    view_types_eq := rfl
    family := ?_
    typeEnv := aliasFormerTypeEnv
    addType := rfl
    constructors := ?_ }
  · exact ⟨.sort (.succ (.succ .zero)),
      aliasFormerFamilyCandidateRun.evidence⟩
  · refine .cons ?_ .nil
    have htype : aliasFormerTypeEnv.HasType 0 []
        (.const aliasFormerRawType.name [])
        (aliasFormerRawType.type.instL []) :=
      .const rfl (fun _ h => nomatch h) rfl
    change aliasFormerTypeEnv.HasType 0 []
      aliasFormerRawType.ctors[0].type
      (.const ``TypeFamilyAlias []) at htype
    exact ⟨.const ``TypeFamilyAlias [], .refl htype⟩

theorem aliasFormerNormalization_wf_checked :
    aliasFormerNormalization.WF typeFamilyAliasEnv :=
  aliasFormerNormalizationRun.wf

/-- Complete checker-produced semantic normalization certificate for
AliasRec. The field comparison is assembled from verified WHNF, application,
beta, and outer-forall congruence. -/
def aliasRecNormalizationRun :
    VInductDecl.NormalizationRun aliasRecNormalization recAliasEnv := by
  refine {
    raw := aliasRecRawType
    view := aliasRecViewType
    source_types_eq := rfl
    view_types_eq := rfl
    family := ?_
    typeEnv := aliasRecTypeEnv
    addType := rfl
    constructors := ?_ }
  · exact ⟨.sort (.succ (.succ .zero)),
      .refl (VEnv.HasType.sort (by decide))⟩
  · exact .cons aliasRecCtorEvidence .nil

theorem aliasRecNormalization_wf_checked :
    aliasRecNormalization.WF recAliasEnv :=
  aliasRecNormalizationRun.wf

/-- The paired AliasFormer block with its normalization component supplied by
the checked WHNF path. The view's structural semantics remain the ordinary
Theory `Checked.WF` proof. -/
theorem aliasFormerBlock_wf_checked :
    aliasFormerBlock.WF typeFamilyAliasEnv := by
  refine ⟨aliasFormerNormalization_wf_checked, ?_⟩
  change aliasFormerViewChecked.WF typeFamilyAliasEnv
  exact aliasFormerViewChecked.wf_of_decl aliasFormerViewDecl_wf

private theorem aliasFormerFamily_defeq_checked :
    typeFamilyAliasEnv.IsDefEq 0 []
      (.const ``TypeFamilyAlias []) (.sort (.succ .zero))
      (.sort (.succ (.succ .zero))) :=
  aliasFormerFamilyWhnfRun.isDefEq
    aliasFormerFamilyCheckTypeRun.hasType

/-- Combining the constructor's exact full-check result with the verified
family-alias WHNF fixes its Theory sort. -/
theorem aliasFormerCtor_hasSort_checked :
    aliasFormerTypeEnv.HasType 0 []
      aliasFormerRawType.ctors[0].type (.sort (.succ .zero)) := by
  have halias :=
    aliasFormerFamily_defeq_checked.mono (VEnv.addConst_le (show
      typeFamilyAliasEnv.addConst aliasFormerRawType.name
        aliasFormerRawType.toVConstant = some aliasFormerTypeEnv from rfl))
  exact halias.defeq aliasFormerCtor_hasType_checked

theorem aliasFormerCtor_isType_checked :
    aliasFormerTypeEnv.IsType 0 []
      aliasFormerRawType.ctors[0].type :=
  ⟨.succ .zero, aliasFormerCtor_hasSort_checked⟩

/-- Complete checker-side AliasFormer generation run. The family result is the
verified WHNF step, while the unchanged constructor result is staged in the
exact environment produced by inserting the raw family. -/
def aliasFormerGenerationRun :
    VInductDecl.GenerationRun aliasFormerGenerationChecked
      typeFamilyAliasEnv := by
  refine {
    normalization := aliasFormerNormalizationRun
    checked :=
      aliasFormerViewChecked.wf_of_decl aliasFormerViewDecl_wf
    familyTel := .nil
    familyResult := aliasFormerFamilyCandidateRun.evidence
    typeEnv := aliasFormerTypeEnv
    addType := rfl
    constructors := ?_ }
  intro ctor hctor
  change ctor ∈
    [⟨aliasFormerRawType.ctors[0],
      aliasFormerViewChecked.constructors[0]⟩] at hctor
  obtain rfl := List.mem_singleton.1 hctor
  exact {
    declaredTel := .nil
    declaredResult := .refl aliasFormerCtor_hasSort_checked
    emittedTel := .nil
    emittedResult := .refl aliasFormerCtor_hasSort_checked }

/-- Generation-ready AliasFormer certificate whose raw/view family equality
comes from the verified checker execution rather than the fixture's explicit
delta rule. -/
theorem aliasFormerGenerationChecked_wf_checked :
    aliasFormerGenerationChecked.WF typeFamilyAliasEnv :=
  aliasFormerGenerationRun.wf

/-- The paired AliasRec block with its field normalization supplied by the
checked WHNF/application/beta certificate. -/
theorem aliasRecBlock_wf_checked :
    aliasRecBlock.WF recAliasEnv := by
  refine ⟨aliasRecNormalization_wf_checked, ?_⟩
  change aliasRecViewChecked.WF recAliasEnv
  exact aliasRecViewChecked.wf_of_decl aliasRecViewDecl_wf

/-- Complete checker-side AliasRec generation run. Its constructor telescope
retains the checked compositional alias equality as pointwise evidence. -/
def aliasRecGenerationRun :
    VInductDecl.GenerationRun aliasRecGenerationChecked recAliasEnv := by
  refine {
    normalization := aliasRecNormalizationRun
    checked := aliasRecViewChecked.wf_of_decl aliasRecViewDecl_wf
    familyTel := .nil
    familyResult := .refl (VEnv.HasType.sort (by decide))
    typeEnv := aliasRecTypeEnv
    addType := rfl
    constructors := ?_ }
  intro ctor hctor
  change ctor ∈
    [⟨aliasRecRawType.ctors[0],
      aliasRecViewChecked.constructors[0]⟩] at hctor
  obtain rfl := List.mem_singleton.1 hctor
  have hresult := aliasRecResult_hasType rfl
  exact {
    declaredTel := .cons aliasRecFieldEvidence .nil
    declaredResult := .refl hresult
    emittedTel := .cons aliasRecFieldEvidence .nil
    emittedResult := .refl hresult }

/-- Generation-ready AliasRec certificate whose raw field typing comes from
the exact post-family full-check run and whose normalization equality composes
the verified WHNF, application, and beta steps. -/
theorem aliasRecGenerationChecked_wf_checked :
    aliasRecGenerationChecked.WF recAliasEnv :=
  aliasRecGenerationRun.wf

/-- The complete AliasFormer metadata trace with the generation-WF field
supplied by the checker-produced certificate. All computational metadata
witnesses are shared with the existing replay. -/
def aliasFormerAddInductTraceChecked :
    AddInductTrace typeFamilyAliasMap typeFamilyAliasEnv
      aliasFormerRawDecl aliasFormerMap aliasFormerFinalEnv :=
  aliasFormerAddInductTraceWith aliasFormerGenerationChecked_wf_checked

theorem aliasFormer_addInduct_checked :
    AddInduct typeFamilyAliasMap typeFamilyAliasEnv
      aliasFormerRawDecl aliasFormerMap aliasFormerFinalEnv :=
  ⟨aliasFormerAddInductTraceChecked⟩

theorem aliasFormer_trEnv'_checked :
    TrEnv' .safe aliasFormerMap false aliasFormerFinalEnv :=
  .induct aliasFormer_addInduct_checked typeFamilyAlias_trEnv'

theorem aliasFormer_env_wf_checked : aliasFormerFinalEnv.WF :=
  aliasFormer_trEnv'_checked.wf

theorem aliasFormer_aligned_checked :
    Aligned .safe aliasFormerMap aliasFormerFinalEnv :=
  aliasFormer_trEnv'_checked.aligned

/-- The complete AliasRec metadata trace with the generation-WF field supplied
by the checker-produced normalization certificate. -/
def aliasRecAddInductTraceChecked :
    AddInductTrace recAliasMap recAliasEnv aliasRecRawDecl
      aliasRecMap aliasRecFinalEnv :=
  aliasRecAddInductTraceWith aliasRecGenerationChecked_wf_checked

theorem aliasRec_addInduct_checked :
    AddInduct recAliasMap recAliasEnv aliasRecRawDecl
      aliasRecMap aliasRecFinalEnv :=
  ⟨aliasRecAddInductTraceChecked⟩

theorem aliasRec_trEnv'_checked :
    TrEnv' .safe aliasRecMap false aliasRecFinalEnv :=
  .induct aliasRec_addInduct_checked recAlias_trEnv'

theorem aliasRec_env_wf_checked : aliasRecFinalEnv.WF :=
  aliasRec_trEnv'_checked.wf

theorem aliasRec_aligned_checked :
    Aligned .safe aliasRecMap aliasRecFinalEnv :=
  aliasRec_trEnv'_checked.aligned

/- The operational traces do not reach the pointer-equality contracts. Their
semantic endpoints intentionally inherit Verify's existing checker-refinement
and reflection contracts, including pointer equality, plus the separately
tracked `TrProj` frontier. No new axiom or native-evaluation principle is
used. -/
/--
info: 'Lean4Lean.InductiveReplayFixtures.aliasFormerFamily_candidateTrace' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Expr.eqv_eq,
 Expr.looseBVarRange_eq,
 Level.instLawfulBEqLevel,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms aliasFormerFamily_candidateTrace

/--
info: 'Lean4Lean.InductiveReplayFixtures.aliasFormerFamily_candidate' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Expr.eqv_eq,
 Expr.looseBVarRange_eq,
 Level.instLawfulBEqLevel,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms aliasFormerFamily_candidate

/--
info: 'Lean4Lean.InductiveReplayFixtures.aliasFormerFamily_candidateSource_tr' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Expr.eqv_eq,
 Expr.looseBVarRange_eq,
 Level.instLawfulBEqLevel,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms aliasFormerFamily_candidateSource_tr

/--
info: 'Lean4Lean.InductiveReplayFixtures.aliasFormerFamily_candidateView_tr' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLevelParam_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 Std.TreeMap.all_eq_all_toList,
 Expr.mkAppRangeAux.eq_def,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms aliasFormerFamily_candidateView_tr

/--
info: 'Lean4Lean.InductiveReplayFixtures.aliasRecField_checkType' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Expr.eqv_eq,
 Expr.hasLevelParam_eq,
 Expr.instantiate1_eq,
 Expr.looseBVarRange_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms aliasRecField_checkType

/--
info: 'Lean4Lean.InductiveReplayFixtures.aliasRecField_hasType_checked' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLevelParam_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 Std.TreeMap.all_eq_all_toList,
 Expr.mkAppRangeAux.eq_def,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms aliasRecField_hasType_checked

/--
info: 'Lean4Lean.InductiveReplayFixtures.aliasFormerFamily_whnf' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Expr.eqv_eq,
 Level.instLawfulBEqLevel,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms aliasFormerFamily_whnf

/--
info: 'Lean4Lean.InductiveReplayFixtures.recAlias_whnf' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Expr.eqv_eq,
 Expr.hasLevelParam_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms recAlias_whnf

/--
info: 'Lean4Lean.InductiveReplayFixtures.aliasFormerFamily_checkType' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Expr.eqv_eq,
 Expr.looseBVarRange_eq,
 Level.instLawfulBEqLevel,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms aliasFormerFamily_checkType

/--
info: 'Lean4Lean.InductiveReplayFixtures.aliasFormerCtor_checkType' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Expr.eqv_eq,
 Expr.looseBVarRange_eq,
 Level.instLawfulBEqLevel,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms aliasFormerCtor_checkType

/--
info: 'Lean4Lean.InductiveReplayFixtures.aliasFormerFamily_isType_checked' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLevelParam_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 Std.TreeMap.all_eq_all_toList,
 Expr.mkAppRangeAux.eq_def,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms aliasFormerFamily_isType_checked

/--
info: 'Lean4Lean.InductiveReplayFixtures.aliasFormerCtor_isType_checked' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLevelParam_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 Std.TreeMap.all_eq_all_toList,
 Expr.mkAppRangeAux.eq_def,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms aliasFormerCtor_isType_checked

/--
info: 'Lean4Lean.InductiveReplayFixtures.aliasFormerNormalization_wf_checked' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLevelParam_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 Std.TreeMap.all_eq_all_toList,
 Expr.mkAppRangeAux.eq_def,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms aliasFormerNormalization_wf_checked

/--
info: 'Lean4Lean.InductiveReplayFixtures.aliasRecNormalization_wf_checked' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLevelParam_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 Std.TreeMap.all_eq_all_toList,
 Expr.mkAppRangeAux.eq_def,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms aliasRecNormalization_wf_checked

/--
info: 'Lean4Lean.InductiveReplayFixtures.aliasFormerBlock_wf_checked' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLevelParam_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 Std.TreeMap.all_eq_all_toList,
 Expr.mkAppRangeAux.eq_def,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms aliasFormerBlock_wf_checked

/--
info: 'Lean4Lean.InductiveReplayFixtures.aliasFormerGenerationChecked_wf_checked' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLevelParam_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 Std.TreeMap.all_eq_all_toList,
 Expr.mkAppRangeAux.eq_def,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms aliasFormerGenerationChecked_wf_checked

/--
info: 'Lean4Lean.InductiveReplayFixtures.aliasRecBlock_wf_checked' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLevelParam_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 Std.TreeMap.all_eq_all_toList,
 Expr.mkAppRangeAux.eq_def,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms aliasRecBlock_wf_checked

/--
info: 'Lean4Lean.InductiveReplayFixtures.aliasRecGenerationChecked_wf_checked' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLevelParam_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 Std.TreeMap.all_eq_all_toList,
 Expr.mkAppRangeAux.eq_def,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms aliasRecGenerationChecked_wf_checked

/--
info: 'Lean4Lean.InductiveReplayFixtures.aliasFormerAddInductTraceChecked' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLevelParam_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 Std.TreeMap.all_eq_all_toList,
 Expr.mkAppRangeAux.eq_def,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms aliasFormerAddInductTraceChecked

/--
info: 'Lean4Lean.InductiveReplayFixtures.aliasFormer_trEnv'_checked' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLevelParam_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 Std.TreeMap.all_eq_all_toList,
 Expr.mkAppRangeAux.eq_def,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms aliasFormer_trEnv'_checked

/--
info: 'Lean4Lean.InductiveReplayFixtures.aliasRecAddInductTraceChecked' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLevelParam_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 Std.TreeMap.all_eq_all_toList,
 Expr.mkAppRangeAux.eq_def,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms aliasRecAddInductTraceChecked

/--
info: 'Lean4Lean.InductiveReplayFixtures.aliasRec_trEnv'_checked' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLevelParam_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 Std.TreeMap.all_eq_all_toList,
 Expr.mkAppRangeAux.eq_def,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms aliasRec_trEnv'_checked

/- Both alias replays have the same explicitly transitional Verify closure as
the identity fixtures. `sorryAx` is inherited only through `TrProj`, and the
three persistent-map contracts enter through concrete `ConstMap` freshness
proofs. -/
/--
info: 'Lean4Lean.InductiveReplayFixtures.aliasFormer_trEnv'' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms aliasFormer_trEnv'

/--
info: 'Lean4Lean.InductiveReplayFixtures.aliasFormer_env_wf' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms aliasFormer_env_wf

/--
info: 'Lean4Lean.InductiveReplayFixtures.aliasFormer_aligned' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms aliasFormer_aligned

/--
info: 'Lean4Lean.InductiveReplayFixtures.aliasRec_trEnv'' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms aliasRec_trEnv'

/--
info: 'Lean4Lean.InductiveReplayFixtures.aliasRec_env_wf' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms aliasRec_env_wf

/--
info: 'Lean4Lean.InductiveReplayFixtures.aliasRec_aligned' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms aliasRec_aligned

end Lean4Lean.InductiveReplayFixtures
