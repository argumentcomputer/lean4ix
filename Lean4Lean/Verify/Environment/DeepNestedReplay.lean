import Lean4Lean.Verify.Environment.NestedReplay

/-!
# Deep, multi-parameter nested replay

`BiBox` supplies an actual two-parameter dependency block. `DeepBi` then
nests through `BiBox` twice: the second occurrence is discovered only while
the first auxiliary constructor is processed.  The pair exercises both
simultaneous parameter substitution and the flattening work queue beyond the
original one-parameter ladder fixtures.
-/

namespace Lean4Lean.DeepNestedReplayFixtures

open Lean
open Lean4Lean.InductiveReplayFixtures
open Lean4Lean.NestedRepresentation
open VInductDecl

/- `nestedBlockChecked?` is executable Theory data.  Reify one of its closed
generated equations as constructor syntax so the ordinary `type_tac` checker
can audit the equation without unfolding the analyzer.  This is the same
elaboration-time quotation boundary used by the kernel-metadata macros; the
subsequent `rfl` parity lemmas below separately pin every quoted RHS to the
actual stored recursor metadata. -/
syntax "computedVDefEq%" term : term

elab_rules : term
  | `(computedVDefEq% $rule:term) => do
    let e ← Lean.Elab.Term.elabTerm rule (Lean.mkConst ``VDefEq)
    let e ← Lean.instantiateMVars e
    let value ← unsafe Lean.Meta.evalExpr VDefEq (Lean.mkConst ``VDefEq) e
    return Lean.toExpr value

local instance : Inhabited VEnv := ⟨.empty⟩
local instance : Inhabited VConstVal :=
  ⟨⟨⟨0, .sort .zero⟩, .anonymous⟩⟩
local instance : Inhabited VDefEq :=
  ⟨⟨0, .sort .zero, .sort .zero, .sort (.succ .zero)⟩⟩

/-! ## An actual two-parameter dependency replay -/

inductive BiBox (α β : Type) : Type where
  | mk : α → β → BiBox α β

def biBoxType : VInductiveType where
  name := ``BiBox
  uvars := 0
  type := nestedConstVType09A% BiBox
  ctors := [⟨⟨0, nestedConstVType09A% BiBox.mk⟩, ``BiBox.mk⟩]

def biBoxDecl : VInductDecl where
  uvars := 0
  nparams := 2
  types := [biBoxType]

def biBoxChecked : biBoxDecl.Checked :=
  biBoxDecl.checked?.get (by decide)

def biBoxGeneration : biBoxDecl.GenerationChecked :=
  biBoxDecl.identityGeneration?.get (by decide)

def biBoxFamilyV : VConstVal := biBoxType.toVConstVal
def biBoxCtorV : VConstVal := biBoxType.ctors[0]
def biBoxRecV : VConstVal := inductGenerationRecVal biBoxGeneration

/-- The executable analyzer's concrete view of the actual dependency block.
Keep these observations in one named trust-manifest entry. -/
theorem biBoxObservedShape :
    biBoxChecked.type.name = ``BiBox ∧
    biBoxChecked.resultLevel = .succ .zero ∧
    biBoxChecked.indices = [] ∧
    biBoxChecked.params.reverse =
      [.sort (.succ .zero), .sort (.succ .zero)] ∧
    biBoxGeneration.block.sourceType.ctors = [biBoxCtorV] := by
  native_decide

theorem biBoxCheckedWF : biBoxChecked.WF VEnv.empty := by
  constructor
  · change VEnv.empty.OnTel 0 []
      [.sort (.succ .zero), .sort (.succ .zero)]
    exact ⟨⟨.succ (.succ .zero), VEnv.HasType.sort (by decide)⟩,
      ⟨⟨.succ (.succ .zero), VEnv.HasType.sort (by decide)⟩, trivial⟩⟩
  · intro ctor hctor
    have hctor' := List.mem_singleton.1 hctor
    subst ctor
    obtain ⟨hname, hresult, hindices, hparams, -⟩ := biBoxObservedShape
    constructor
    · rw [show biBoxDecl.uvars = 0 from rfl,
        hname,
        show biBoxDecl.nparams = 2 from rfl,
        hresult, hindices, hparams]
      change VInductDecl.fieldsWF 0 ``BiBox 2 VEnv.empty
        (.succ .zero) [] [.sort (.succ .zero), .sort (.succ .zero)] 0
        [.bvar 1, .bvar 1]
      constructor
      · exact .inr (.inr ⟨rfl, .succ .zero, by type_tac,
          .inr (VLevel.le_refl _)⟩)
      constructor
      · intro recursive
        contradiction
      constructor
      · exact .inr (.inr ⟨rfl, .succ .zero, by type_tac,
          .inr (VLevel.le_refl _)⟩)
      constructor
      · intro recursive
        contradiction
      · trivial
    · rw [show biBoxDecl.uvars = 0 from rfl,
        show biBoxDecl.nparams = 2 from rfl,
        hresult, hindices, hparams]
      exact .nil

def biBoxGenerationWF : biBoxGeneration.WF VEnv.empty := by
  exact biBoxCheckedWF.identityGeneration .empty

def biBoxTypeEnv : VEnv :=
  (VEnv.empty.addConst biBoxFamilyV.name biBoxFamilyV.toVConstant).get!

def biBoxCtorEnv : VEnv :=
  (biBoxTypeEnv.addConst biBoxCtorV.name biBoxCtorV.toVConstant).get!

def biBoxRecEnv : VEnv :=
  (biBoxCtorEnv.addConst biBoxRecV.name biBoxRecV.toVConstant).get!

def biBoxFinalEnv : VEnv :=
  biBoxGeneration.generatedRules.foldl VEnv.addDefEq biBoxRecEnv

def biBoxInfo : ConstantInfo := kernelInductInfo% BiBox
def biBoxMkInfo : ConstantInfo := kernelCtorInfo% BiBox.mk
def biBoxRecInfo : ConstantInfo := kernelRecInfo% BiBox.rec

def biBoxTypeMap : ConstMap :=
  ({} : ConstMap).insert ``BiBox biBoxInfo

def biBoxCtorMap : ConstMap :=
  biBoxTypeMap.insert ``BiBox.mk biBoxMkInfo

def biBoxMap : ConstMap :=
  biBoxCtorMap.insert ``BiBox.rec biBoxRecInfo

theorem biBoxTypeEnvOrdered : biBoxTypeEnv.Ordered :=
  replayTypeEnv_ordered07 .empty biBoxGenerationWF rfl

theorem biBoxCtorEnvOrdered : biBoxCtorEnv.Ordered :=
  replayCtorEnv_ordered07 biBoxGenerationWF rfl biBoxTypeEnvOrdered rfl

def biBoxGenerationEnv :
    VInductDecl.GenerationEnv biBoxGeneration biBoxCtorEnv :=
  replayGenerationEnv07 biBoxGenerationWF rfl rfl biBoxCtorEnvOrdered

theorem biBoxInfoTr :
    TrConstVal .safe VEnv.empty biBoxInfo biBoxFamilyV := by
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr VEnv.empty biBoxInfo.levelParams []
      biBoxInfo.type biBoxFamilyV.type := by
    tr_type_expr_tac
  obtain ⟨sort, familyType⟩ := replayRawFamilyWF07 biBoxGenerationWF
  exact shape.to_trExprS .empty trivial ⟨.sort sort, familyType⟩

theorem biBoxCtorInfoTr :
    TrConstVal .safe biBoxTypeEnv biBoxMkInfo biBoxCtorV := by
  have hBiBox : biBoxTypeEnv.constants ``BiBox =
      some biBoxFamilyV.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr biBoxTypeEnv biBoxMkInfo.levelParams []
      biBoxMkInfo.type biBoxCtorV.type := by
    tr_type_expr_tac
  have hctors := biBoxObservedShape.2.2.2.2
  obtain ⟨sort, ctorType⟩ := replayRawCtorWF07 biBoxGenerationWF rfl
    biBoxCtorV (by rw [hctors]; simp)
  exact shape.to_trExprS biBoxTypeEnvOrdered trivial
    ⟨.sort sort, ctorType⟩

theorem biBoxRecInfoTr :
    TrConstVal .safe biBoxCtorEnv biBoxRecInfo biBoxRecV := by
  have hBiBox : biBoxCtorEnv.constants ``BiBox =
      some biBoxFamilyV.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr biBoxCtorEnv biBoxRecInfo.levelParams []
      biBoxRecInfo.type biBoxRecV.type := by
    tr_type_expr_tac
  obtain ⟨sort, recursorType⟩ := biBoxGenerationEnv.recursor_wf
  exact shape.to_trExprS biBoxCtorEnvOrdered trivial
    ⟨.sort sort, recursorType⟩

theorem biBoxTypeFresh : ({} : ConstMap).find? ``BiBox = none := by
  simp [SMap.find?]

theorem biBoxTypeMapWF : biBoxTypeMap.WF :=
  SMap.WF.empty.insert _ _ biBoxTypeFresh

theorem biBoxCtorFresh : biBoxTypeMap.find? ``BiBox.mk = none := by
  rw [biBoxTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem biBoxCtorMapWF : biBoxCtorMap.WF :=
  biBoxTypeMapWF.insert _ _ biBoxCtorFresh

theorem biBoxRecFresh : biBoxCtorMap.find? ``BiBox.rec = none := by
  rw [biBoxCtorMap, biBoxTypeMapWF.find?_insert, biBoxTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem biBoxAddInduct : AddInduct ({} : ConstMap) VEnv.empty biBoxDecl
    biBoxMap biBoxFinalEnv := by
  refine ⟨{
    generation := biBoxGeneration
    generation_wf := biBoxGenerationWF
    typeMap := biBoxTypeMap
    typeEnv := biBoxTypeEnv
    ctorMap := biBoxCtorMap
    ctorEnv := biBoxCtorEnv
    recEnv := biBoxRecEnv
    addType := {
      info := biBoxInfo
      kind_eq := by simp [biBoxInfo, InductConstantKind.Matches]
      tr := biBoxInfoTr
      map_fresh := biBoxTypeFresh
      env_add := rfl
      map_add := rfl }
    addCtors := ?_
    addRec := {
      info := biBoxRecInfo
      kind_eq := by simp [biBoxRecInfo, InductConstantKind.Matches]
      tr := biBoxRecInfoTr
      map_fresh := biBoxRecFresh
      env_add := rfl
      map_add := rfl }
    recK := by decide
    addRules := ⟨rfl⟩ }⟩
  exact .cons {
    info := biBoxMkInfo
    kind_eq := by simp [biBoxMkInfo, InductConstantKind.Matches]
    tr := biBoxCtorInfoTr
    map_fresh := by simpa [biBoxCtorV, biBoxType] using biBoxCtorFresh
    env_add := rfl
    map_add := rfl } .nil

theorem biBoxAligned : Aligned .safe biBoxMap biBoxFinalEnv :=
  Aligned.addInduct biBoxAddInduct .empty

def biBoxReplay : SingletonReplayArtifact where
  label := ``BiBox
  source := biBoxDecl
  inputMap := {}
  inputEnv := .empty
  inputMapWF := SMap.WF.empty
  outputMap := biBoxMap
  outputEnv := biBoxFinalEnv
  inputOrdered := .empty
  transaction := biBoxAddInduct
  aligned := biBoxAligned

/-! ## Analyzer-produced deep nested block -/

inductive DeepBi (α β : Type) : Type where
  | node : BiBox (DeepBi α β) (BiBox α (DeepBi α β)) → DeepBi α β

def biBoxTarget : NestedTargetBlock where
  nparams := 2
  families := biBoxDecl.types

def deepSourceV : VInductDecl where
  uvars := 0
  nparams := 2
  types :=
    [{ name := ``DeepBi
       uvars := 0
       type := nestedConstVType09A% DeepBi
       ctors :=
         [⟨⟨0, nestedConstVType09A% DeepBi.node⟩, ``DeepBi.node⟩] }]

def deepNestedC? : Option (NestedBlockChecked deepSourceV) :=
  nestedBlockChecked? [biBoxTarget] deepSourceV

#guard deepNestedC?.isSome

theorem deepNestedC_some : deepNestedC?.isSome := by
  native_decide

def deepNestedC : NestedBlockChecked deepSourceV :=
  deepNestedC?.get deepNestedC_some

theorem deepNestedC_produced :
    nestedBlockChecked? [biBoxTarget] deepSourceV = some deepNestedC := by
  change deepNestedC? = some deepNestedC
  exact (Option.some_get deepNestedC_some).symm

#guard deepNestedC.elim.numNested == 2
#guard deepNestedC.recursors.length == 3
#guard deepNestedC.recursors.map (·.name) ==
  [``DeepBi.rec,
   `Lean4Lean.DeepNestedReplayFixtures.DeepBi.rec_1,
   `Lean4Lean.DeepNestedReplayFixtures.DeepBi.rec_2]

def deepFamilyV : VConstVal := deepSourceV.types[0].toVConstVal
def deepNodeV : VConstVal := deepSourceV.types[0].ctors[0]

def deepRecTypeL : VExpr := nestedConstVType09A% DeepBi.rec
def deepRec1TypeL : VExpr := nestedConstVType09A% DeepBi.rec_1
def deepRec2TypeL : VExpr := nestedConstVType09A% DeepBi.rec_2

def deepRecVL : VConstVal :=
  ⟨⟨1, deepRecTypeL⟩, ``DeepBi.rec⟩
def deepRec1VL : VConstVal :=
  ⟨⟨1, deepRec1TypeL⟩,
    `Lean4Lean.DeepNestedReplayFixtures.DeepBi.rec_1⟩
def deepRec2VL : VConstVal :=
  ⟨⟨1, deepRec2TypeL⟩,
    `Lean4Lean.DeepNestedReplayFixtures.DeepBi.rec_2⟩

theorem deepRecursors_eq :
    deepNestedC.recursors = [deepRecVL, deepRec1VL, deepRec2VL] := by
  native_decide

def deepRule0L : VDefEq :=
  computedVDefEq% deepNestedC.generatedRules[0]!
def deepRule1L : VDefEq :=
  computedVDefEq% deepNestedC.generatedRules[1]!
def deepRule2L : VDefEq :=
  computedVDefEq% deepNestedC.generatedRules[2]!

def deepRulesL : List VDefEq := [deepRule0L, deepRule1L, deepRule2L]

theorem deepRules_eq : deepNestedC.generatedRules = deepRulesL := by
  native_decide

/- Each analyzer-produced rule is pinned to the corresponding rule emitted
by Lean for the actual declaration.  The equality is definitional after the
two independent elaboration-time quotations. -/
theorem deepRule0_rhs_metadata :
    deepRule0L.rhs = kernelRecRuleRhs% DeepBi.rec 0 := by
  rfl

theorem deepRule1_rhs_metadata :
    deepRule1L.rhs = kernelRecRuleRhs% DeepBi.rec_1 0 := by
  rfl

theorem deepRule2_rhs_metadata :
    deepRule2L.rhs = kernelRecRuleRhs% DeepBi.rec_2 0 := by
  rfl

/-! ## Exact semantic phase environments -/

def deepTypeEnv : VEnv :=
  (biBoxFinalEnv.addConst deepFamilyV.name deepFamilyV.toVConstant).get!

def deepCtorEnv : VEnv :=
  (deepTypeEnv.addConst deepNodeV.name deepNodeV.toVConstant).get!

def deepRecEnv : VEnv :=
  (deepCtorEnv.addConst deepRecVL.name deepRecVL.toVConstant).get!

def deepRec1Env : VEnv :=
  (deepRecEnv.addConst deepRec1VL.name deepRec1VL.toVConstant).get!

def deepRec2Env : VEnv :=
  (deepRec1Env.addConst deepRec2VL.name deepRec2VL.toVConstant).get!

def deepFinalEnv : VEnv :=
  deepRulesL.foldl VEnv.addDefEq deepRec2Env

theorem biBoxTrEnv : TrEnv' .safe biBoxMap false biBoxFinalEnv :=
  .induct biBoxAddInduct .empty

theorem biBoxFinalOrdered : biBoxFinalEnv.Ordered :=
  biBoxTrEnv.wf.ordered

theorem biBoxFinalWF : biBoxFinalEnv.WF :=
  biBoxTrEnv.wf

theorem deepFamilyWF : deepFamilyV.toVConstant.WF biBoxFinalEnv :=
  ⟨_, by type_tac⟩

theorem deepTypeEnv_eq :
    biBoxFinalEnv.addConst deepFamilyV.name deepFamilyV.toVConstant =
      some deepTypeEnv := rfl

theorem deepTypeOrdered : deepTypeEnv.Ordered :=
  .const biBoxFinalOrdered deepFamilyWF deepTypeEnv_eq

theorem deepNodeWF : deepNodeV.toVConstant.WF deepTypeEnv := by
  have hBiBox : deepTypeEnv.constants ``BiBox =
      some biBoxFamilyV.toVConstant := rfl
  have hDeep : deepTypeEnv.constants ``DeepBi =
      some deepFamilyV.toVConstant := rfl
  exact ⟨_, by type_tac⟩

theorem deepCtorEnv_eq :
    deepTypeEnv.addConst deepNodeV.name deepNodeV.toVConstant =
      some deepCtorEnv := rfl

theorem deepCtorOrdered : deepCtorEnv.Ordered :=
  .const deepTypeOrdered deepNodeWF deepCtorEnv_eq

macro "deep_const_hyps" e:term : tactic => `(tactic| (
  have hBiBox : VEnv.constants $e ``BiBox =
      some biBoxFamilyV.toVConstant := rfl
  have hBiBoxMk : VEnv.constants $e ``BiBox.mk =
      some biBoxCtorV.toVConstant := rfl
  have hDeep : VEnv.constants $e ``DeepBi =
      some deepFamilyV.toVConstant := rfl
  have hNode : VEnv.constants $e ``DeepBi.node =
      some deepNodeV.toVConstant := rfl))

set_option maxRecDepth 20000 in
theorem deepRecWF : deepRecVL.toVConstant.WF deepCtorEnv := by
  deep_const_hyps deepCtorEnv
  exact ⟨_, by type_tac⟩

theorem deepRecEnv_eq :
    deepCtorEnv.addConst deepRecVL.name deepRecVL.toVConstant =
      some deepRecEnv := rfl

theorem deepRecOrdered : deepRecEnv.Ordered :=
  .const deepCtorOrdered deepRecWF deepRecEnv_eq

set_option maxRecDepth 20000 in
theorem deepRec1WF : deepRec1VL.toVConstant.WF deepRecEnv := by
  deep_const_hyps deepRecEnv
  exact ⟨_, by type_tac⟩

theorem deepRec1Env_eq :
    deepRecEnv.addConst deepRec1VL.name deepRec1VL.toVConstant =
      some deepRec1Env := rfl

theorem deepRec1Ordered : deepRec1Env.Ordered :=
  .const deepRecOrdered deepRec1WF deepRec1Env_eq

set_option maxRecDepth 20000 in
theorem deepRec2WF : deepRec2VL.toVConstant.WF deepRec1Env := by
  deep_const_hyps deepRec1Env
  exact ⟨_, by type_tac⟩

theorem deepRec2Env_eq :
    deepRec1Env.addConst deepRec2VL.name deepRec2VL.toVConstant =
      some deepRec2Env := rfl

theorem deepRec2Ordered : deepRec2Env.Ordered :=
  .const deepRec1Ordered deepRec2WF deepRec2Env_eq

/-! ## Restored rule well-formedness -/

macro "deep_rule_hyps" e:term : tactic => `(tactic| (
  deep_const_hyps $e
  have hRec : VEnv.constants $e ``DeepBi.rec =
      some deepRecVL.toVConstant := rfl
  have hRec1 : VEnv.constants $e
      `Lean4Lean.DeepNestedReplayFixtures.DeepBi.rec_1 =
      some deepRec1VL.toVConstant := rfl
  have hRec2 : VEnv.constants $e
      `Lean4Lean.DeepNestedReplayFixtures.DeepBi.rec_2 =
      some deepRec2VL.toVConstant := rfl))

def deepRuleEnv1 : VEnv := deepRec2Env.addDefEq deepRule0L
def deepRuleEnv2 : VEnv := deepRuleEnv1.addDefEq deepRule1L

set_option maxRecDepth 30000 in
theorem deepRule0WF : deepRule0L.WF deepRec2Env := by
  constructor
  · deep_rule_hyps deepRec2Env
    type_tac
  · deep_rule_hyps deepRec2Env
    type_tac

set_option maxRecDepth 30000 in
theorem deepRule1WF : deepRule1L.WF deepRuleEnv1 := by
  constructor
  · deep_rule_hyps deepRuleEnv1
    type_tac
  · deep_rule_hyps deepRuleEnv1
    type_tac

set_option maxRecDepth 30000 in
theorem deepRule2WF : deepRule2L.WF deepRuleEnv2 := by
  constructor
  · deep_rule_hyps deepRuleEnv2
    type_tac
  · deep_rule_hyps deepRuleEnv2
    type_tac

/-! ## Semantic package and exact nested transaction phases -/

theorem deepTypesFold_eq :
    deepSourceV.blockTypeConstants.foldlM
      (fun env c => env.addConst c.name c.toVConstant) biBoxFinalEnv =
      some deepTypeEnv := rfl

theorem deepCtorsFold_eq :
    deepSourceV.blockConstructorConstants.foldlM
      (fun env c => env.addConst c.name c.toVConstant) deepTypeEnv =
      some deepCtorEnv := rfl

theorem deepRecsFold_eq :
    deepNestedC.recursors.foldlM
      (fun env c => env.addConst c.name c.toVConstant) deepCtorEnv =
      some deepRec2Env := by
  rw [deepRecursors_eq]
  rfl

theorem deepNestedWF : deepNestedC.WF biBoxFinalEnv := by
  refine ⟨⟨deepFamilyWF, fun env' h => ?_⟩, fun {typeEnv} h => ?_,
    fun {typeEnv ctorEnv} hT hC => ?_,
    fun {typeEnv ctorEnv recEnv} hT hC hR => ?_⟩
  · cases Option.some.inj (deepTypeEnv_eq.symm.trans h)
    exact trivial
  · cases Option.some.inj (deepTypesFold_eq.symm.trans h)
    exact ⟨deepNodeWF, fun env' h' => by
      cases Option.some.inj (deepCtorEnv_eq.symm.trans h')
      exact trivial⟩
  · cases Option.some.inj (deepTypesFold_eq.symm.trans hT)
    cases Option.some.inj (deepCtorsFold_eq.symm.trans hC)
    rw [deepRecursors_eq]
    exact ⟨deepRecWF, fun env' h' => by
      cases Option.some.inj (deepRecEnv_eq.symm.trans h')
      exact ⟨deepRec1WF, fun env'' h'' => by
        cases Option.some.inj (deepRec1Env_eq.symm.trans h'')
        exact ⟨deepRec2WF, fun env''' h''' => by
          cases Option.some.inj (deepRec2Env_eq.symm.trans h''')
          exact trivial⟩⟩⟩
  · cases Option.some.inj (deepTypesFold_eq.symm.trans hT)
    cases Option.some.inj (deepCtorsFold_eq.symm.trans hC)
    cases Option.some.inj (deepRecsFold_eq.symm.trans hR)
    rw [deepRules_eq]
    exact ⟨deepRule0WF, deepRule1WF, deepRule2WF, trivial⟩

/-! ## Actual stored metadata and implementation maps -/

def deepInfo : ConstantInfo := kernelInductInfo% DeepBi
def deepNodeInfo : ConstantInfo := kernelCtorInfo% DeepBi.node
def deepRecInfo : ConstantInfo := kernelRecInfo% DeepBi.rec
def deepRec1Info : ConstantInfo := kernelRecInfo% DeepBi.rec_1
def deepRec2Info : ConstantInfo := kernelRecInfo% DeepBi.rec_2

def deepTypeMap : ConstMap :=
  biBoxMap.insert ``DeepBi deepInfo

def deepCtorMap : ConstMap :=
  deepTypeMap.insert ``DeepBi.node deepNodeInfo

def deepRecMap : ConstMap :=
  deepCtorMap.insert ``DeepBi.rec deepRecInfo

def deepRec1Map : ConstMap :=
  deepRecMap.insert
    `Lean4Lean.DeepNestedReplayFixtures.DeepBi.rec_1 deepRec1Info

def deepMap : ConstMap :=
  deepRec1Map.insert
    `Lean4Lean.DeepNestedReplayFixtures.DeepBi.rec_2 deepRec2Info

theorem biBoxMapWF : biBoxMap.WF :=
  biBoxCtorMapWF.insert _ _ biBoxRecFresh

theorem deepTypeFresh : biBoxMap.find? ``DeepBi = none := by
  rw [biBoxMap, biBoxCtorMapWF.find?_insert, biBoxCtorMap,
    biBoxTypeMapWF.find?_insert, biBoxTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem deepTypeMapWF : deepTypeMap.WF :=
  biBoxMapWF.insert _ _ deepTypeFresh

theorem deepNodeFresh : deepTypeMap.find? ``DeepBi.node = none := by
  rw [deepTypeMap, biBoxMapWF.find?_insert, biBoxMap,
    biBoxCtorMapWF.find?_insert, biBoxCtorMap,
    biBoxTypeMapWF.find?_insert, biBoxTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem deepCtorMapWF : deepCtorMap.WF :=
  deepTypeMapWF.insert _ _ deepNodeFresh

theorem deepRecFresh : deepCtorMap.find? ``DeepBi.rec = none := by
  rw [deepCtorMap, deepTypeMapWF.find?_insert, deepTypeMap,
    biBoxMapWF.find?_insert, biBoxMap,
    biBoxCtorMapWF.find?_insert, biBoxCtorMap,
    biBoxTypeMapWF.find?_insert, biBoxTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem deepRecMapWF : deepRecMap.WF :=
  deepCtorMapWF.insert _ _ deepRecFresh

theorem deepRec1Fresh : deepRecMap.find?
    `Lean4Lean.DeepNestedReplayFixtures.DeepBi.rec_1 = none := by
  rw [deepRecMap, deepCtorMapWF.find?_insert, deepCtorMap,
    deepTypeMapWF.find?_insert, deepTypeMap,
    biBoxMapWF.find?_insert, biBoxMap,
    biBoxCtorMapWF.find?_insert, biBoxCtorMap,
    biBoxTypeMapWF.find?_insert, biBoxTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

theorem deepRec1MapWF : deepRec1Map.WF :=
  deepRecMapWF.insert _ _ deepRec1Fresh

theorem deepRec2Fresh : deepRec1Map.find?
    `Lean4Lean.DeepNestedReplayFixtures.DeepBi.rec_2 = none := by
  rw [deepRec1Map, deepRecMapWF.find?_insert, deepRecMap,
    deepCtorMapWF.find?_insert, deepCtorMap,
    deepTypeMapWF.find?_insert, deepTypeMap,
    biBoxMapWF.find?_insert, biBoxMap,
    biBoxCtorMapWF.find?_insert, biBoxCtorMap,
    biBoxTypeMapWF.find?_insert, biBoxTypeMap,
    SMap.WF.find?_insert (s := ({} : ConstMap)) SMap.WF.empty]
  simp [SMap.find?]

/-! ## Stored metadata translations at the exact insertion boundaries -/

theorem deepInfoTr :
    TrConstVal .safe biBoxFinalEnv deepInfo deepFamilyV := by
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr biBoxFinalEnv deepInfo.levelParams []
      deepInfo.type deepFamilyV.toVConstant.type := by
    tr_type_expr_tac
  obtain ⟨u, hty⟩ := deepFamilyWF
  exact shape.to_trExprS biBoxFinalOrdered trivial ⟨_, hty⟩

theorem deepNodeInfoTr :
    TrConstVal .safe deepTypeEnv deepNodeInfo deepNodeV := by
  have hBiBox : deepTypeEnv.constants ``BiBox =
      some biBoxFamilyV.toVConstant := rfl
  have hDeep : deepTypeEnv.constants ``DeepBi =
      some deepFamilyV.toVConstant := rfl
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr deepTypeEnv deepNodeInfo.levelParams []
      deepNodeInfo.type deepNodeV.toVConstant.type := by
    tr_type_expr_tac
  obtain ⟨u, hty⟩ := deepNodeWF
  exact shape.to_trExprS deepTypeOrdered trivial ⟨_, hty⟩

set_option maxRecDepth 20000 in
theorem deepRecInfoTr :
    TrConstVal .safe deepCtorEnv deepRecInfo deepRecVL := by
  deep_const_hyps deepCtorEnv
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr deepCtorEnv deepRecInfo.levelParams []
      deepRecInfo.type deepRecVL.toVConstant.type := by
    tr_type_expr_tac
  obtain ⟨u, hty⟩ := deepRecWF
  exact shape.to_trExprS deepCtorOrdered trivial ⟨_, hty⟩

set_option maxRecDepth 20000 in
theorem deepRec1InfoTr :
    TrConstVal .safe deepRecEnv deepRec1Info deepRec1VL := by
  deep_const_hyps deepRecEnv
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr deepRecEnv deepRec1Info.levelParams []
      deepRec1Info.type deepRec1VL.toVConstant.type := by
    tr_type_expr_tac
  obtain ⟨u, hty⟩ := deepRec1WF
  exact shape.to_trExprS deepRecOrdered trivial ⟨_, hty⟩

set_option maxRecDepth 20000 in
theorem deepRec2InfoTr :
    TrConstVal .safe deepRec1Env deepRec2Info deepRec2VL := by
  deep_const_hyps deepRec1Env
  refine ⟨⟨by decide, rfl, ?_⟩, rfl⟩
  have shape : TrTypeExpr deepRec1Env deepRec2Info.levelParams []
      deepRec2Info.type deepRec2VL.toVConstant.type := by
    tr_type_expr_tac
  obtain ⟨u, hty⟩ := deepRec2WF
  exact shape.to_trExprS deepRec1Ordered trivial ⟨_, hty⟩

/-! ## Recursor flags, final lookups, and the replay trace -/

theorem deepMapWF : deepMap.WF :=
  deepRec1MapWF.insert _ _ deepRec2Fresh

theorem deepKTarget : deepNestedC.generation.kTarget = false := by
  native_decide

theorem deepRecLookup :
    deepMap.find? ``DeepBi.rec = some deepRecInfo := by
  rw [deepMap, deepRec1MapWF.find?_insert, deepRec1Map,
    deepRecMapWF.find?_insert, deepRecMap,
    deepCtorMapWF.find?_insert]
  simp

theorem deepRec1Lookup :
    deepMap.find?
      `Lean4Lean.DeepNestedReplayFixtures.DeepBi.rec_1 =
        some deepRec1Info := by
  rw [deepMap, deepRec1MapWF.find?_insert]
  simp [deepRec1Map, deepRecMapWF.find?_insert]

theorem deepRec2Lookup :
    deepMap.find?
      `Lean4Lean.DeepNestedReplayFixtures.DeepBi.rec_2 =
        some deepRec2Info := by
  rw [deepMap, deepRec1MapWF.find?_insert]
  simp

theorem deepRecK :
    RecursorMapKMatches deepMap deepNestedC.recursors
      deepNestedC.generation.kTarget := by
  rw [deepRecursors_eq, deepKTarget]
  intro recursor hmem
  rcases List.mem_cons.1 hmem with rfl | hmem
  · exact ⟨deepRecInfo, deepRecLookup, by decide⟩
  rcases List.mem_cons.1 hmem with rfl | hmem
  · exact ⟨deepRec1Info, deepRec1Lookup, by decide⟩
  rcases List.mem_cons.1 hmem with rfl | hmem
  · exact ⟨deepRec2Info, deepRec2Lookup, by decide⟩
  · cases hmem

def deepTrace :
    AddInductNestedTrace biBoxMap biBoxFinalEnv deepSourceV
      deepMap deepFinalEnv where
  nested := deepNestedC
  nested_wf := deepNestedWF
  typeMap := deepTypeMap
  typeEnv := deepTypeEnv
  ctorMap := deepCtorMap
  ctorEnv := deepCtorEnv
  recEnv := deepRec2Env
  addTypes := .cons
    { info := deepInfo
      kind_eq := by simp [deepInfo, InductConstantKind.Matches]
      tr := deepInfoTr
      map_fresh := deepTypeFresh
      env_add := deepTypeEnv_eq
      map_add := rfl } .nil
  addCtors := .cons
    { info := deepNodeInfo
      kind_eq := by simp [deepNodeInfo, InductConstantKind.Matches]
      tr := deepNodeInfoTr
      map_fresh := deepNodeFresh
      env_add := deepCtorEnv_eq
      map_add := rfl } .nil
  addRecs := deepRecursors_eq ▸ .cons
    { info := deepRecInfo
      kind_eq := by simp [deepRecInfo, InductConstantKind.Matches]
      tr := deepRecInfoTr
      map_fresh := deepRecFresh
      env_add := deepRecEnv_eq
      map_add := rfl } (.cons
    { info := deepRec1Info
      kind_eq := by simp [deepRec1Info, InductConstantKind.Matches]
      tr := deepRec1InfoTr
      map_fresh := deepRec1Fresh
      env_add := deepRec1Env_eq
      map_add := rfl } (.cons
    { info := deepRec2Info
      kind_eq := by simp [deepRec2Info, InductConstantKind.Matches]
      tr := deepRec2InfoTr
      map_fresh := deepRec2Fresh
      env_add := deepRec2Env_eq
      map_add := rfl } .nil))
  recK := deepRecK
  addRules := ⟨by rw [deepRules_eq]; rfl⟩

theorem deepAddInductNested :
    AddInductNested biBoxMap biBoxFinalEnv deepSourceV
      deepMap deepFinalEnv :=
  ⟨deepTrace⟩

theorem deepTrEnv : TrEnv' .safe deepMap false deepFinalEnv :=
  .inductNested deepAddInductNested biBoxTrEnv

theorem deepFinalOrdered : deepFinalEnv.Ordered :=
  deepTrEnv.wf.ordered

theorem deepFinalWF : deepFinalEnv.WF :=
  deepTrEnv.wf

theorem deepAddInductNested_success :
    biBoxFinalEnv.addInductNested deepNestedC = some deepFinalEnv :=
  deepTrace.to_addInductNested

/- The replay is now free of `sorryAx`; its remaining native-decision and
persistent-map closure is recorded exactly below. The Theory certificate
exported from this trace has the stricter guards in `InductiveCertificate`. -/
/--
info: 'Lean4Lean.DeepNestedReplayFixtures.deepTrEnv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert,
 biBoxObservedShape._native.native_decide.ax_1_1,
 deepKTarget._native.native_decide.ax_1_1,
 deepNestedC_some._native.native_decide.ax_1_1,
 deepRecursors_eq._native.native_decide.ax_1_1,
 deepRules_eq._native.native_decide.ax_1_1]
-/
#guard_msgs in
#print axioms deepTrEnv

end Lean4Lean.DeepNestedReplayFixtures
