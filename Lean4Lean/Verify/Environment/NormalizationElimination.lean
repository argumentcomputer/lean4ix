import Lean4Lean.Verify.Environment.Normalization
import Lean4Lean.Verify.Environment.Elimination
import Lean4Lean.Verify.Environment.Lemmas
import Lean4Lean.Theory.Typing.InductiveCertificate
import Lean4Lean.Environment

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

namespace AddInductive

/-- Exact alignment between the post-constructor elimination decisions of the
ordinary kernel execution and the corresponding fields of a Theory mutual
generation.  This is the block analogue of `CheckerEliminationRun`. -/
structure CheckerBlockEliminationRun
    {source : VInductDecl}
    (generation : VInductDecl.BlockGenerationChecked source)
    {nparams : Nat} {types : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool} {candidateContext : Context}
    (execution : NormalizationEliminationExecution nparams types numNested
      isUnsafe candidateContext) : Type where
  nparams_eq : nparams = source.nparams
  sourceUvars_eq : source.uvars =
    execution.normalization.validationContext.lparams.length
  mode_eq : generation.elimination =
    VInductDecl.ElimMode.ofBool execution.elimination.large.result
  kTarget_eq : generation.kTarget = execution.kTarget.result
  recUvars_eq : generation.recUvars = execution.recLevelParams.length
  recLevels_eq : execution.recLevels.mapM
    (VLevel.ofLevel execution.recLevelParams) = some generation.recLevels

namespace CheckerBlockEliminationRun

/-- Decide every block-elimination alignment field from the retained ordinary
execution. -/
def build?
    {source : VInductDecl}
    (generation : VInductDecl.BlockGenerationChecked source)
    {nparams : Nat} {types : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool} {candidateContext : Context}
    (execution : NormalizationEliminationExecution nparams types numNested
      isUnsafe candidateContext) :
    Option (CheckerBlockEliminationRun generation execution) := do
  if hparams : nparams = source.nparams then
    if huvars : source.uvars =
        execution.normalization.validationContext.lparams.length then
      if hmode : generation.elimination =
          VInductDecl.ElimMode.ofBool execution.elimination.large.result then
        if hkTarget : generation.kTarget = execution.kTarget.result then
          if hrecUvars : generation.recUvars =
              execution.recLevelParams.length then
            if hlevels : execution.recLevels.mapM
                (VLevel.ofLevel execution.recLevelParams) =
                  some generation.recLevels then
              some {
                nparams_eq := hparams
                sourceUvars_eq := huvars
                mode_eq := hmode
                kTarget_eq := hkTarget
                recUvars_eq := hrecUvars
                recLevels_eq := hlevels }
            else none
          else none
        else none
      else none
    else none
  else none

theorem large_result_iff
    (run : CheckerBlockEliminationRun generation execution) :
    execution.elimination.large.result = true ↔
      generation.elimination = VInductDecl.ElimMode.large := by
  cases hresult : execution.elimination.large.result with
  | false =>
      have hmode : generation.elimination = VInductDecl.ElimMode.small := by
        simpa [hresult] using run.mode_eq
      simp [hmode]
  | true =>
      have hmode : generation.elimination = VInductDecl.ElimMode.large := by
        simpa [hresult] using run.mode_eq
      simp [hmode]

theorem kTarget_result_iff
    (run : CheckerBlockEliminationRun generation execution) :
    execution.kTarget.result = true ↔ generation.kTarget = true := by
  rw [run.kTarget_eq]

end CheckerBlockEliminationRun

/-- Recompose a retained outer inductive execution through the public
`addDecl` dispatcher.  Primitive recognition is retained as an explicit
equation because it selects the `allowPrimitive` input of the execution. -/
theorem EnvironmentInductiveExecution.addDeclRun
    (execution : EnvironmentInductiveExecution env lparams nparams types
      isUnsafe allowPrimitive fuel finalEnv)
    (primitiveRun : Environment.checkPrimitiveInductive env lparams nparams
      types isUnsafe = .ok allowPrimitive) :
    addDecl env (.inductDecl lparams nparams types isUnsafe)
      (check := true) (fuel := fuel) = .ok finalEnv := by
  change (do
    let actualAllowPrimitive ← Environment.checkPrimitiveInductive env
      lparams nparams types isUnsafe
    Environment.addInductive env lparams nparams types isUnsafe
      actualAllowPrimitive fuel) = .ok finalEnv
  rw [primitiveRun]
  exact execution.addInductiveRun

/-- A successful retained build therefore certifies the matching public
`addDecl` result once the primitive-recognizer branch is fixed. -/
theorem EnvironmentInductiveExecution.buildExecution_addDeclRun
    {produced : Σ finalEnv, EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv}
    (_run : EnvironmentInductiveExecution.buildExecution env lparams nparams
      types isUnsafe allowPrimitive fuel = .ok produced)
    (primitiveRun : Environment.checkPrimitiveInductive env lparams nparams
      types isUnsafe = .ok allowPrimitive) :
    addDecl env (.inductDecl lparams nparams types isUnsafe)
      (check := true) (fuel := fuel) = .ok produced.1 :=
  produced.2.addDeclRun primitiveRun

/-- Exact semantic transaction aligned with the final branch of one retained
outer execution.  An ordinary execution is interpreted by the mutual-block
transaction; a genuinely nested execution is interpreted by the restored
nested transaction. -/
inductive EnvironmentInductiveExecution.ExactSemanticTransaction
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : EnvironmentInductiveExecution env lparams nparams types
      isUnsafe allowPrimitive fuel finalEnv)
    (source : VInductDecl) (input output : VEnv) : Prop where
  | ordinary
      (numNested_eq : execution.nested.aux2nested.size = 0)
      (transaction : AddInductBlock env.constants input source
        finalEnv.constants output) :
      execution.ExactSemanticTransaction source input output
  | nested
      (numNested_ne : execution.nested.aux2nested.size ≠ 0)
      (transaction : AddInductNested env.constants input source
        finalEnv.constants output) :
      execution.ExactSemanticTransaction source input output

namespace EnvironmentInductiveExecution.ExactSemanticTransaction

/-- Replay an exact transaction after any translated input history. -/
theorem trEnv
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : EnvironmentInductiveExecution env lparams nparams types
      isUnsafe allowPrimitive fuel finalEnv}
    {source : VInductDecl} {input output : VEnv}
    (transaction : EnvironmentInductiveExecution.ExactSemanticTransaction
      execution source input output)
    (pre : TrEnv' safety env.constants env.quotInit input) :
    TrEnv' safety finalEnv.constants finalEnv.quotInit output := by
  rw [execution.quotInit_eq]
  cases transaction with
  | ordinary _ block => exact .inductBlock block pre
  | nested _ restored => exact .inductNested restored pre

/-- Every exact block or nested transaction monotonically extends its input
Theory environment. -/
theorem le
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : EnvironmentInductiveExecution env lparams nparams types
      isUnsafe allowPrimitive fuel finalEnv}
    {source : VInductDecl} {input output : VEnv}
    (transaction : EnvironmentInductiveExecution.ExactSemanticTransaction
      execution source input output) :
    input ≤ output := by
  cases transaction with
  | ordinary _ block => exact block.le
  | nested _ restored => exact restored.le

end EnvironmentInductiveExecution.ExactSemanticTransaction

end AddInductive

namespace VInductDecl

/-- One exact kernel constructor record translates to a raw Theory
constructor when their source headers and strict types agree.  This is the
candidate-independent semantic core used by both retained checker runs and
closed canonical inventories. -/
theorem declaredConstructorInfo_tr
    {stats : AddInductive.InductiveStats} {induct : Name}
    {source : Constructor} {cidx : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context} {env : VEnv} {Us : List Name}
    {raw : VConstVal}
    (safe : isUnsafe = false)
    (lparams_eq : context.lparams = Us)
    (name_eq : source.name = raw.name)
    (uvars_eq : raw.uvars = Us.length)
    (type_tr : TrExprS env Us [] source.type raw.type) :
    TrConstVal .safe env
      (.ctorInfo (AddInductive.declaredConstructorInfo stats induct source
        cidx isUnsafe context)) raw := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · simp [ConstantInfo.safety, ConstantInfo.isUnsafe,
      ConstantInfo.isPartial, AddInductive.declaredConstructorInfo, safe]
  · simpa [ConstantInfo.toConstantVal, ConstantInfo.levelParams,
      AddInductive.declaredConstructorInfo, lparams_eq] using uvars_eq.symm
  · simpa [ConstantInfo.toConstantVal, ConstantInfo.levelParams,
      ConstantInfo.type, AddInductive.declaredConstructorInfo,
      lparams_eq] using type_tr
  · simpa [ConstantInfo.toConstantVal, ConstantInfo.name,
      AddInductive.declaredConstructorInfo] using name_eq

/-- One exact kernel constructor record translates to the raw Theory
constructor at the same source position.  Metadata-only fields such as owner,
ordinal, and field count do not enter `TrConstVal`; their exact values remain
retained in the record and declaration trace. -/
theorem CandidateConstructorSemanticRun.declaredConstructorInfo_tr
    {stats : AddInductive.InductiveStats} {induct : Name}
    {source : Constructor} {cidx : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context} {env : VEnv} {Us : List Name}
    {candidate : AddInductive.CandidateConstructor source}
    {raw : VConstVal}
    (run : CandidateConstructorSemanticRun env Us candidate raw)
    (safe : isUnsafe = false)
    (lparams_eq : context.lparams = Us) :
    TrConstVal .safe env
      (.ctorInfo (AddInductive.declaredConstructorInfo stats induct source
        cidx isUnsafe context)) raw := by
  exact _root_.Lean4Lean.VInductDecl.declaredConstructorInfo_tr safe
    lparams_eq run.name_eq run.uvars_eq run.type.source_tr

/-- Translate one complete source-indexed constructor list, preserving the
kernel's zero-based constructor ordinals. -/
theorem CandidateConstructorSemanticListRun.declarationEvidence
    {env : VEnv} {Us : List Name}
    {sources : List Constructor}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor sources}
    {raws : List VConstVal}
    (run : CandidateConstructorSemanticListRun env Us candidates raws)
    (stats : AddInductive.InductiveStats) (induct : Name)
    (isUnsafe : Bool) (context : AddInductive.Context)
    (safe : isUnsafe = false)
    (lparams_eq : context.lparams = Us) (cidx : Nat := 0) :
    List.Forall₂
      (fun info raw => TrConstVal .safe env (.ctorInfo info) raw)
      (AddInductive.declaredConstructorInfosFor stats induct isUnsafe
        context cidx sources) raws := by
  induction run generalizing cidx with
  | nil => exact .nil
  | cons head tail ih =>
      exact .cons
        (head.declaredConstructorInfo_tr safe lparams_eq)
        (ih (cidx := cidx + 1))

/-- Flatten the constructor translations in the same family-major order as
the implementation declaration phase and Theory's block transaction. -/
theorem CandidateBlockFamilySemanticListRun.constructorDeclarationEvidence
    {env blockEnv : VEnv} {Us : List Name}
    {kernelSources : List InductiveType}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateFamily kernelSources}
    {raws : List VInductiveType}
    (run : CandidateBlockFamilySemanticListRun env blockEnv Us candidates raws)
    (stats : AddInductive.InductiveStats) (isUnsafe : Bool)
    (context : AddInductive.Context) (safe : isUnsafe = false)
    (lparams_eq : context.lparams = Us) :
    List.Forall₂
      (fun info raw => TrConstVal .safe blockEnv (.ctorInfo info) raw)
      (kernelSources.flatMap fun source =>
        AddInductive.declaredConstructorInfosFor stats source.name isUnsafe
          context 0 source.ctors)
      (raws.flatMap (·.ctors)) := by
  induction run with
  | @nil => exact .nil
  | @cons familySource candidate raw sources candidates raws head tail ih =>
      have headEvidence := head.constructors.declarationEvidence stats
        familySource.name isUnsafe context safe lparams_eq
      exact (List.Forall₂.append_of_left
        (Lean4Lean.List.Forall₂.length_eq headEvidence)).2
        ⟨headEvidence, ih⟩

private theorem constructor_forall₂_cons_iff
    {R : α → β → Prop} {a : α} {as : List α} {b : β} {bs : List β} :
    List.Forall₂ R (a :: as) (b :: bs) ↔
      R a b ∧ List.Forall₂ R as bs := by
  constructor
  · intro relation
    cases relation with
    | cons head tail => exact ⟨head, tail⟩
  · rintro ⟨head, tail⟩
    exact .cons head tail

/-- The constructor metadata trace replayed as an exact Theory insertion fold,
without requiring a translated-history postcondition at the post-constructor
boundary. -/
structure ConstructorDeclarationInsertionRun
    (allowPrimitive : Bool) (kernelEnv finalKernelEnv : Environment)
    (infos : List ConstructorVal) (typeEnv : VEnv)
    (raws : List VConstVal) where
  ctorEnv : VEnv
  kernelTrace : AddInductive.DeclareConstructorInfoListRun
    allowPrimitive kernelEnv infos finalKernelEnv
  addCtors : AddInductConstants .ctor kernelEnv.constants typeEnv raws
    finalKernelEnv.constants ctorEnv

/-- Constructor declaration preserves persistent-map well-formedness. -/
theorem _root_.Lean4Lean.AddInductive.DeclareConstructorInfoListRun.map_wf
    (run : AddInductive.DeclareConstructorInfoListRun allowPrimitive env infos
      finalEnv) (wf : env.constants.WF) : finalEnv.constants.WF := by
  induction run with
  | nil => exact wf
  | cons checkName tail ih =>
      apply ih
      exact wf.insert _ _ (VInductDecl.checkName_constants_fresh checkName)

/-- Every constructor accepted by a declaration fold was absent from the
fold's input family environment.  Later name checks reflect backwards across
the preceding fresh constructor insertions. -/
theorem _root_.Lean4Lean.AddInductive.DeclareConstructorInfoListRun.names_fresh
    (run : AddInductive.DeclareConstructorInfoListRun allowPrimitive env infos
      finalEnv) (wf : env.constants.WF) :
    ∀ info ∈ infos, env.constants.find? info.name = none := by
  induction run with
  | nil => intro info member; nomatch member
  | @cons infosTail finalEnvTail startEnv inserted checkName tail ih =>
      intro info member
      rcases List.mem_cons.mp member with rfl | member
      · exact VInductDecl.checkName_constants_fresh checkName
      · have insertedFresh :=
          VInductDecl.checkName_constants_fresh checkName
        have nextWF := wf.insert inserted.name (.ctorInfo inserted)
          insertedFresh
        have tailFresh := ih nextWF info member
        change (startEnv.constants.insert inserted.name
          (.ctorInfo inserted)).find? info.name = none at tailFresh
        rw [wf.find?_insert] at tailFresh
        split at tailFresh <;> simp_all

/-- Sequential constructor name checks make the exact declaration inventory
pairwise distinct. -/
theorem _root_.Lean4Lean.AddInductive.DeclareConstructorInfoListRun.names_nodup
    (run : AddInductive.DeclareConstructorInfoListRun allowPrimitive env infos
      finalEnv) (wf : env.constants.WF) :
    (infos.map (·.name)).Nodup := by
  induction run with
  | nil => simp
  | @cons infosTail finalEnvTail startEnv inserted checkName tail ih =>
      rw [List.map_cons, List.nodup_cons]
      constructor
      · intro member
        obtain ⟨other, otherMember, nameEq⟩ := List.mem_map.1 member
        have insertedFresh :=
          VInductDecl.checkName_constants_fresh checkName
        have nextWF := wf.insert inserted.name (.ctorInfo inserted)
          insertedFresh
        have fresh := tail.names_fresh nextWF other otherMember
        change (startEnv.constants.insert inserted.name
          (.ctorInfo inserted)).find? other.name = none at fresh
        rw [nameEq, wf.find?_insert] at fresh
        simp at fresh
      · exact ih (wf.insert _ _
          (VInductDecl.checkName_constants_fresh checkName))

/-- Every constructor accepted by a nonprimitive declaration fold avoids
both the kernel primitive inventory and its reflected Theory subset. -/
theorem _root_.Lean4Lean.AddInductive.DeclareConstructorInfoListRun.names_not_primitive
    (run : AddInductive.DeclareConstructorInfoListRun false env infos
      finalEnv) :
    ∀ info ∈ infos,
      info.name ∉ VEnv.reflectedPrimitiveNames ∧
        Environment.primitives.contains info.name = false := by
  induction run with
  | nil => intro info member; nomatch member
  | cons checkName tail ih =>
      intro info member
      rcases List.mem_cons.mp member with rfl | member
      · have fresh := VInductDecl.checkName_primitives_fresh checkName
        exact ⟨VInductDecl.not_reflectedPrimitive_of_primitives_fresh fresh,
          fresh⟩
      · exact ih info member

/-- Constructor declaration preserves every lookup already present in its
input map. -/
theorem _root_.Lean4Lean.AddInductive.DeclareConstructorInfoListRun.preserve_map_lookup
    (run : AddInductive.DeclareConstructorInfoListRun allowPrimitive env infos
      finalEnv) (wf : env.constants.WF)
    (old : env.constants.find? name = some found) :
    finalEnv.constants.find? name = some found := by
  induction run with
  | nil => exact old
  | @cons infos finalEnv env info checkName tail ih =>
      have fresh := VInductDecl.checkName_constants_fresh checkName
      have mid : (env.add (.ctorInfo info)).constants.find? name =
          some found := by
        change (env.constants.insert info.name (.ctorInfo info)).find? name = _
        rw [wf.find?_insert]
        split
        · rename_i equal
          have nameEq : info.name = name := LawfulBEq.eq_of_beq equal
          subst name
          rw [old] at fresh
          contradiction
        · exact old
      exact ih (wf.insert _ _ fresh) mid

/-- Every synthesized constructor record remains at its name in the final
constructor-declaration map. -/
theorem _root_.Lean4Lean.AddInductive.DeclareConstructorInfoListRun.map_lookup
    (run : AddInductive.DeclareConstructorInfoListRun allowPrimitive env infos
      finalEnv) (wf : env.constants.WF) {info : ConstructorVal}
    (member : info ∈ infos) :
    finalEnv.constants.find? info.name = some (.ctorInfo info) := by
  induction run with
  | nil => contradiction
  | @cons infosTail finalEnvTail startEnv inserted checkName tail ih =>
      rcases List.mem_cons.1 member with rfl | member
      · apply tail.preserve_map_lookup
          (wf.insert _ _ (VInductDecl.checkName_constants_fresh checkName))
        change SMap.find? (SMap.insert _ info.name
          (ConstantInfo.ctorInfo info)) info.name = _
        rw [wf.find?_insert]
        simp
      · exact ih (wf.insert _ _
          (VInductDecl.checkName_constants_fresh checkName)) member

/-- Classify an arbitrary constant lookup after the constructor declaration
fold. The inserted branch retains both the exact constructor record and the
queried key. -/
theorem _root_.Lean4Lean.AddInductive.DeclareConstructorInfoListRun.constant_lookup_cases
    (run : AddInductive.DeclareConstructorInfoListRun allowPrimitive env infos
      finalEnv) (wf : env.constants.WF) {name : Name}
    {found : ConstantInfo}
    (lookup : finalEnv.constants.find? name = some found) :
    env.constants.find? name = some found ∨
      ∃ info ∈ infos, found = .ctorInfo info ∧ info.name = name := by
  induction run with
  | nil => exact .inl lookup
  | @cons infosTail finalEnvTail startEnv inserted checkName tail ih =>
      have fresh := VInductDecl.checkName_constants_fresh checkName
      rcases ih (wf.insert _ _ fresh) lookup with mid |
          ⟨info, member, tagged_eq, name_eq⟩
      · change (startEnv.constants.insert inserted.name
          (.ctorInfo inserted)).find? name = _ at mid
        rw [wf.find?_insert] at mid
        split at mid
        · rename_i name_equal
          exact .inr ⟨inserted, List.mem_cons_self,
            (Option.some.inj mid).symm, LawfulBEq.eq_of_beq name_equal⟩
        · exact .inl mid
      · exact .inr ⟨info, List.mem_cons_of_mem inserted member,
          tagged_eq, name_eq⟩

/-- Every constructor lookup in the output of the declaration fold is either
an unchanged input lookup or one of the records inserted by that fold. -/
theorem _root_.Lean4Lean.AddInductive.DeclareConstructorInfoListRun.map_lookup_cases
    (run : AddInductive.DeclareConstructorInfoListRun allowPrimitive env infos
      finalEnv) (wf : env.constants.WF) {name : Name}
    {info : ConstructorVal}
    (found : finalEnv.constants.find? name = some (.ctorInfo info)) :
    env.constants.find? name = some (.ctorInfo info) ∨
      info ∈ infos ∧ info.name = name := by
  induction run with
  | nil => exact .inl found
  | @cons infosTail finalEnvTail startEnv inserted checkName tail ih =>
      have fresh := VInductDecl.checkName_constants_fresh checkName
      rcases ih (wf.insert _ _ fresh) found with mid | member
      · change (startEnv.constants.insert inserted.name
          (.ctorInfo inserted)).find? name = _ at mid
        rw [wf.find?_insert] at mid
        split at mid
        · rename_i name_equal
          have inserted_name_eq : inserted.name = name :=
            LawfulBEq.eq_of_beq name_equal
          have tagged_eq :
              (.ctorInfo inserted : ConstantInfo) = .ctorInfo info :=
            Option.some.inj mid
          have info_eq : inserted = info :=
            ConstantInfo.ctorInfo.inj tagged_eq
          exact .inr ⟨info_eq ▸ List.mem_cons_self,
            info_eq ▸ inserted_name_eq⟩
        · exact .inl mid
      · exact .inr ⟨List.mem_cons_of_mem inserted member.1, member.2⟩

/--
info: 'Lean4Lean.AddInductive.DeclareConstructorInfoListRun.map_wf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms AddInductive.DeclareConstructorInfoListRun.map_wf

/--
info: 'Lean4Lean.AddInductive.DeclareConstructorInfoListRun.preserve_map_lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms AddInductive.DeclareConstructorInfoListRun.preserve_map_lookup

/--
info: 'Lean4Lean.AddInductive.DeclareConstructorInfoListRun.map_lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms AddInductive.DeclareConstructorInfoListRun.map_lookup

/--
info: 'Lean4Lean.AddInductive.DeclareConstructorInfoListRun.constant_lookup_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms AddInductive.DeclareConstructorInfoListRun.constant_lookup_cases

/--
info: 'Lean4Lean.AddInductive.DeclareConstructorInfoListRun.map_lookup_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms AddInductive.DeclareConstructorInfoListRun.map_lookup_cases

/-- Replay the retained constructor declaration equation using only semantic
metadata translations and the weaker `Aligned` name-domain invariant.  This
is valid after a primitive family insertion even though `TrEnv'` is not yet
available for that incomplete block. -/
noncomputable def constructorDeclarationInsertion
    {allowPrimitive : Bool} {kernelEnv finalKernelEnv : Environment}
    {infos : List ConstructorVal} {typeEnv : VEnv}
    {raws : List VConstVal}
    (declare : AddInductive.declareConstructorInfoList allowPrimitive infos
      kernelEnv = .ok finalKernelEnv)
    (evidence : List.Forall₂
      (fun info raw => TrConstVal .safe typeEnv (.ctorInfo info) raw)
      infos raws)
    (pre : Aligned safety kernelEnv.constants typeEnv) :
    ConstructorDeclarationInsertionRun allowPrimitive kernelEnv
      finalKernelEnv infos typeEnv raws := by
  induction infos generalizing kernelEnv finalKernelEnv typeEnv raws with
  | nil =>
      cases raws with
      | nil =>
          simp only [AddInductive.declareConstructorInfoList,
            Except.ok.injEq] at declare
          subst finalKernelEnv
          exact { ctorEnv := typeEnv, kernelTrace := .nil, addCtors := .nil }
      | cons raw raws =>
          have impossible : False := by cases evidence
          exact impossible.elim
  | cons info infos ih =>
      cases raws with
      | nil =>
          have impossible : False := by cases evidence
          exact impossible.elim
      | cons raw raws =>
          have related := constructor_forall₂_cons_iff.mp evidence
          cases hcheck : kernelEnv.checkName info.name allowPrimitive with
          | error error =>
              have impossible : False := by
                simp only [AddInductive.declareConstructorInfoList] at declare
                rw [hcheck] at declare
                contradiction
              exact impossible.elim
          | ok value =>
              have value_eq : value = () := Subsingleton.elim _ _
              subst value
              have tailDeclare :
                  AddInductive.declareConstructorInfoList allowPrimitive infos
                    (kernelEnv.add (.ctorInfo info)) = .ok finalKernelEnv := by
                simpa only [AddInductive.declareConstructorInfoList, hcheck,
                  Bind.bind, Except.bind] using declare
              have mapFresh : kernelEnv.constants.find? raw.name = none := by
                rw [← related.1.2]
                simpa [ConstantInfo.toConstantVal, ConstantInfo.name] using
                  checkName_constants_fresh hcheck
              have envFresh : typeEnv.constants raw.name = none := by
                cases found : typeEnv.constants raw.name with
                | none => rfl
                | some ci =>
                    obtain ⟨kernelInfo, kernelFound, _⟩ :=
                      pre.find?_iff.mpr ⟨ci, found⟩
                    rw [mapFresh] at kernelFound
                    contradiction
              let nextEnv : VEnv := {
                typeEnv with
                constants := fun name =>
                  if raw.name = name then some raw.toVConstant
                  else typeEnv.constants name }
              have added : typeEnv.addConst raw.name raw.toVConstant =
                  some nextEnv := by
                simp [VEnv.addConst, envFresh, nextEnv]
              let add : AddInductConstant .ctor kernelEnv.constants typeEnv raw
                  (kernelEnv.add (.ctorInfo info)).constants nextEnv := {
                info := .ctorInfo info
                kind_eq := trivial
                tr := related.1
                map_fresh := mapFresh
                env_add := added
                map_add := by
                  rw [← related.1.2]
                  rfl }
              have le : typeEnv ≤ nextEnv := VEnv.addConst_le added
              have tailEvidence : List.Forall₂
                  (fun info raw =>
                    TrConstVal .safe nextEnv (.ctorInfo info) raw)
                  infos raws :=
                Lean4Lean.List.Forall₂.imp (h := related.2)
                  (fun _ _ relation => relation.mono le)
              let tailResult := ih tailDeclare tailEvidence
                (pre.addInductConstant add)
              exact {
                ctorEnv := tailResult.ctorEnv
                kernelTrace := .cons hcheck tailResult.kernelTrace
                addCtors := .cons add tailResult.addCtors }

/-- A source-ordered constructor declaration interpreted simultaneously in
the retained kernel environment and its Theory model.  The final Theory
environment is constructed by this interpreter; it is not supplied by a
fixture or a second metadata inventory. -/
structure ConstructorDeclarationStagingRun
    (allowPrimitive : Bool) (kernelEnv finalKernelEnv : Environment)
    (infos : List ConstructorVal) (typeEnv : VEnv)
    (raws : List VConstVal) (Q : Bool) where
  ctorEnv : VEnv
  kernelTrace : AddInductive.DeclareConstructorInfoListRun
    allowPrimitive kernelEnv infos finalKernelEnv
  addCtors : AddInductConstants .ctor kernelEnv.constants typeEnv raws
    finalKernelEnv.constants ctorEnv
  trenv : TrEnv' .safe finalKernelEnv.constants Q ctorEnv

/-- Interpret the ordinary constructor-declaration equation itself.  Every
successful `checkName` becomes both implementation-map freshness and, via
the incoming environment translation, Theory freshness.  Constructor typing
and translations are transported through the resulting deterministic fold. -/
noncomputable def constructorDeclarationStaging
    {allowPrimitive : Bool} {kernelEnv finalKernelEnv : Environment}
    {infos : List ConstructorVal} {typeEnv : VEnv}
    {raws : List VConstVal} {Q : Bool}
    (declare : AddInductive.declareConstructorInfoList allowPrimitive infos
      kernelEnv = .ok finalKernelEnv)
    (evidence : List.Forall₂
      (fun info raw => TrConstVal .safe typeEnv (.ctorInfo info) raw)
      infos raws)
    (rawsWF : ∀ raw ∈ raws, raw.toVConstant.WF typeEnv)
    (pre : TrEnv' .safe kernelEnv.constants Q typeEnv) :
    ConstructorDeclarationStagingRun allowPrimitive kernelEnv finalKernelEnv
      infos typeEnv raws Q := by
  let insertion := constructorDeclarationInsertion declare evidence pre.aligned
  exact {
    ctorEnv := insertion.ctorEnv
    kernelTrace := insertion.kernelTrace
    addCtors := insertion.addCtors
    trenv := insertion.addCtors.trEnvStaging rawsWF pre }

/-- The semantic fields exposed by full executable equality of two generated
recursor records.  Expression equality deliberately remains `Expr.eqv`:
Lean's recursor `BEq` ignores binder annotations, and translation is invariant
under precisely that equivalence. -/
theorem recursorVal_beq_translation_fields
    {actual expected : RecursorVal} (h : actual == expected) :
    actual.name = expected.name ∧
      actual.levelParams = expected.levelParams ∧
      actual.type == expected.type ∧
      actual.isUnsafe = expected.isUnsafe := by
  cases actual with
  | mk actualConstant actualAll actualNumParams actualNumIndices
      actualNumMotives actualNumMinors actualRules actualK actualUnsafe =>
    cases actualConstant with
    | mk actualName actualLevels actualType =>
      cases expected with
      | mk expectedConstant expectedAll expectedNumParams expectedNumIndices
          expectedNumMotives expectedNumMinors expectedRules expectedK
          expectedUnsafe =>
        cases expectedConstant with
        | mk expectedName expectedLevels expectedType =>
          change Lean.instBEqRecursorVal.beq
            { name := actualName, levelParams := actualLevels,
              type := actualType, all := actualAll,
              numParams := actualNumParams,
              numIndices := actualNumIndices,
              numMotives := actualNumMotives,
              numMinors := actualNumMinors, rules := actualRules,
              k := actualK, isUnsafe := actualUnsafe }
            { name := expectedName, levelParams := expectedLevels,
              type := expectedType, all := expectedAll,
              numParams := expectedNumParams,
              numIndices := expectedNumIndices,
              numMotives := expectedNumMotives,
              numMinors := expectedNumMinors, rules := expectedRules,
              k := expectedK, isUnsafe := expectedUnsafe } = true at h
          simp only [Lean.instBEqRecursorVal.beq,
            Bool.and_eq_true] at h
          have hconstant := h.1
          change Lean.instBEqConstantVal.beq
            { name := actualName, levelParams := actualLevels,
              type := actualType }
            { name := expectedName, levelParams := expectedLevels,
              type := expectedType } = true at hconstant
          simp only [Lean.instBEqConstantVal.beq,
            Bool.and_eq_true] at hconstant
          have hname : actualName = expectedName := by
            simpa using hconstant.1
          have hlevels : actualLevels = expectedLevels := by
            simpa using hconstant.2.1
          have hunsafe : actualUnsafe = expectedUnsafe := by
            simpa using h.2.2.2.2.2.2.2.2
          exact ⟨hname, hlevels, hconstant.2.2, hunsafe⟩

/-- Transport a constant translation across exactly the four metadata header
fields observed by `TrConstVal`.  The expression boundary is
alpha-equivalence; role-specific metadata remains unconstrained. -/
theorem trConstVal_of_translation_header
    {actual expected : ConstantInfo}
    {safety : DefinitionSafety} {env : VEnv} {raw : VConstVal}
    (safety_eq : actual.safety = expected.safety)
    (levels_eq : actual.levelParams = expected.levelParams)
    (type_eqv : actual.type.eqv expected.type)
    (name_eq : actual.name = expected.name)
    (tr : TrConstVal safety env expected raw) :
    TrConstVal safety env actual raw := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · simpa [safety_eq] using tr.1.1
  · simpa [levels_eq] using tr.1.2.1
  · simpa [levels_eq] using tr.1.2.2.eqv (BEq.symm type_eqv)
  · exact name_eq.trans tr.2

/-- One restored metadata insertion interpreted simultaneously in the kernel
map and Theory environment.  Unlike the phase-specific list interpreters,
this accepts any inductive role and therefore follows the mixed operational
order of nested restoration. -/
structure RestoredConstantDeclarationStagingRun
    (kind : InductConstantKind) (allowPrimitive : Bool)
    (kernelEnv : Environment) (info : ConstantInfo)
    (env : VEnv) (raw : VConstVal) (finalEnv : VEnv) (Q : Bool) where
  add : AddInductConstant kind kernelEnv.constants env raw
    (kernelEnv.add info).constants finalEnv
  trenv : TrEnv' .safe (kernelEnv.add info).constants Q finalEnv

/-- Interpret one successful check-and-insert step from the exact nested
restoration trace. -/
def restoredConstantDeclarationStaging
    {kind : InductConstantKind} {allowPrimitive : Bool}
    {kernelEnv : Environment} {info : ConstantInfo}
    {env : VEnv} {raw : VConstVal} {finalEnv : VEnv} {Q : Bool}
    (check : kernelEnv.checkName info.name allowPrimitive = .ok ())
    (kind_eq : kind.Matches info)
    (tr : TrConstVal .safe env info raw)
    (rawWF : raw.toVConstant.WF env)
    (env_add : env.addConst raw.name raw.toVConstant = some finalEnv)
    (pre : TrEnv' .safe kernelEnv.constants Q env) :
    RestoredConstantDeclarationStagingRun kind allowPrimitive kernelEnv info
      env raw finalEnv Q := by
  have mapFresh : kernelEnv.constants.find? raw.name = none := by
    rw [← tr.2]
    exact checkName_constants_fresh check
  let add : AddInductConstant kind kernelEnv.constants env raw
      (kernelEnv.add info).constants finalEnv := {
    info
    kind_eq
    tr
    map_fresh := mapFresh
    env_add
    map_add := by rw [← tr.2]; rfl }
  exact { add, trenv := .inductStaging add rawWF pre }

/-- Transport a recursor-constant translation from a stored kernel record to
the executable producer's `BEq`-matching record.  This uses expression
equivalence, not an unavailable propositional equality for `RecursorVal`. -/
theorem recursorInfoTranslation_of_beq
    {actual expected : RecursorVal}
    {safety : DefinitionSafety} {env : VEnv} {raw : VConstVal}
    (h : actual == expected)
    (tr : TrConstVal safety env (.recInfo expected) raw) :
    TrConstVal safety env (.recInfo actual) raw := by
  obtain ⟨hname, hlevels, htype, hunsafe⟩ :=
    recursorVal_beq_translation_fields h
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · simpa [ConstantInfo.safety, ConstantInfo.isUnsafe,
      ConstantInfo.isPartial, hunsafe] using tr.1.1
  · simpa [ConstantInfo.levelParams, ConstantInfo.toConstantVal,
      hlevels] using tr.1.2.1
  · simpa [ConstantInfo.levelParams, ConstantInfo.type,
      ConstantInfo.toConstantVal, hlevels] using
        tr.1.2.2.eqv (BEq.symm htype)
  · simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using
      hname.trans tr.2

/-- Lift complete record parity to source-ordered semantic translation.  The
`Option` wrapper matches kernel metadata extraction, where non-recursor
records remain observable as `none`; successful parity therefore also proves
that no position changed kind or disappeared. -/
theorem recursorInfoTranslationList_of_option_beq
    {actual expected : List RecursorVal} {raws : List VConstVal}
    {env : VEnv}
    (parity : List.beq (actual.map some) (expected.map some) = true)
    (evidence : List.Forall₂
      (fun info raw => TrConstVal .safe env (.recInfo info) raw)
      expected raws) :
    List.Forall₂
      (fun info raw => TrConstVal .safe env (.recInfo info) raw)
      actual raws := by
  induction evidence generalizing actual with
  | nil =>
      cases actual with
      | nil => exact .nil
      | cons info infos => simp at parity
  | cons head tail ih =>
      cases actual with
      | nil => simp at parity
      | cons info infos =>
          simp only [List.map, List.beq, Bool.and_eq_true] at parity
          exact .cons (recursorInfoTranslation_of_beq parity.1 head)
            (ih parity.2)

/-- Generated-recursor declaration preserves persistent-map
well-formedness. -/
theorem _root_.Lean4Lean.AddInductive.DeclareRecursorInfoListRun.map_wf
    (run : AddInductive.DeclareRecursorInfoListRun allowPrimitive env infos
      finalEnv) (wf : env.constants.WF) : finalEnv.constants.WF := by
  induction run with
  | nil => exact wf
  | cons checkName tail ih =>
      apply ih
      exact wf.insert _ _ (VInductDecl.checkName_constants_fresh checkName)

/-- Every generated recursor accepted by a declaration fold was absent from
the fold's complete input environment. -/
theorem _root_.Lean4Lean.AddInductive.DeclareRecursorInfoListRun.names_fresh
    (run : AddInductive.DeclareRecursorInfoListRun allowPrimitive env infos
      finalEnv) (wf : env.constants.WF) :
    ∀ info ∈ infos, env.constants.find? info.name = none := by
  induction run with
  | nil => intro info member; nomatch member
  | @cons infosTail finalEnvTail startEnv inserted checkName tail ih =>
      intro info member
      rcases List.mem_cons.mp member with rfl | member
      · exact VInductDecl.checkName_constants_fresh checkName
      · have insertedFresh :=
          VInductDecl.checkName_constants_fresh checkName
        have nextWF := wf.insert inserted.name (.recInfo inserted)
          insertedFresh
        have tailFresh := ih nextWF info member
        change (startEnv.constants.insert inserted.name
          (.recInfo inserted)).find? info.name = none at tailFresh
        rw [wf.find?_insert] at tailFresh
        split at tailFresh <;> simp_all

/-- Sequential recursor name checks make the exact generated inventory
pairwise distinct. -/
theorem _root_.Lean4Lean.AddInductive.DeclareRecursorInfoListRun.names_nodup
    (run : AddInductive.DeclareRecursorInfoListRun allowPrimitive env infos
      finalEnv) (wf : env.constants.WF) :
    (infos.map (·.name)).Nodup := by
  induction run with
  | nil => simp
  | @cons infosTail finalEnvTail startEnv inserted checkName tail ih =>
      rw [List.map_cons, List.nodup_cons]
      constructor
      · intro member
        obtain ⟨other, otherMember, nameEq⟩ := List.mem_map.1 member
        have insertedFresh :=
          VInductDecl.checkName_constants_fresh checkName
        have nextWF := wf.insert inserted.name (.recInfo inserted)
          insertedFresh
        have fresh := tail.names_fresh nextWF other otherMember
        change (startEnv.constants.insert inserted.name
          (.recInfo inserted)).find? other.name = none at fresh
        rw [nameEq, wf.find?_insert] at fresh
        simp at fresh
      · exact ih (wf.insert _ _
          (VInductDecl.checkName_constants_fresh checkName))

/-- Every generated recursor accepted by a nonprimitive declaration fold
avoids both the kernel primitive inventory and its reflected Theory subset. -/
theorem _root_.Lean4Lean.AddInductive.DeclareRecursorInfoListRun.names_not_primitive
    (run : AddInductive.DeclareRecursorInfoListRun false env infos finalEnv) :
    ∀ info ∈ infos,
      info.name ∉ VEnv.reflectedPrimitiveNames ∧
        Environment.primitives.contains info.name = false := by
  induction run with
  | nil => intro info member; nomatch member
  | cons checkName tail ih =>
      intro info member
      rcases List.mem_cons.mp member with rfl | member
      · have fresh := VInductDecl.checkName_primitives_fresh checkName
        exact ⟨VInductDecl.not_reflectedPrimitive_of_primitives_fresh fresh,
          fresh⟩
      · exact ih info member

/-- Generated-recursor declaration preserves every lookup already present in
its input map. -/
theorem _root_.Lean4Lean.AddInductive.DeclareRecursorInfoListRun.preserve_map_lookup
    (run : AddInductive.DeclareRecursorInfoListRun allowPrimitive env infos
      finalEnv) (wf : env.constants.WF)
    (old : env.constants.find? name = some found) :
    finalEnv.constants.find? name = some found := by
  induction run with
  | nil => exact old
  | @cons infos finalEnv env info checkName tail ih =>
      have fresh := VInductDecl.checkName_constants_fresh checkName
      have mid : (env.add (.recInfo info)).constants.find? name =
          some found := by
        change (env.constants.insert info.name (.recInfo info)).find? name = _
        rw [wf.find?_insert]
        split
        · rename_i equal
          have nameEq : info.name = name := LawfulBEq.eq_of_beq equal
          subst name
          rw [old] at fresh
          contradiction
        · exact old
      exact ih (wf.insert _ _ fresh) mid

/-- Every generated recursor remains at its name in the final declaration
map. -/
theorem _root_.Lean4Lean.AddInductive.DeclareRecursorInfoListRun.map_lookup
    (run : AddInductive.DeclareRecursorInfoListRun allowPrimitive env infos
      finalEnv) (wf : env.constants.WF) {info : RecursorVal}
    (member : info ∈ infos) :
    finalEnv.constants.find? info.name = some (.recInfo info) := by
  induction run with
  | nil => contradiction
  | @cons infosTail finalEnvTail startEnv inserted checkName tail ih =>
      rcases List.mem_cons.1 member with rfl | member
      · apply tail.preserve_map_lookup
          (wf.insert _ _ (VInductDecl.checkName_constants_fresh checkName))
        change SMap.find? (SMap.insert _ info.name
          (ConstantInfo.recInfo info)) info.name = _
        rw [wf.find?_insert]
        simp
      · exact ih (wf.insert _ _
          (VInductDecl.checkName_constants_fresh checkName)) member

/-- Classify an arbitrary constant lookup after the generated-recursor
declaration fold. The inserted branch retains both the exact recursor record
and the queried key. -/
theorem _root_.Lean4Lean.AddInductive.DeclareRecursorInfoListRun.constant_lookup_cases
    (run : AddInductive.DeclareRecursorInfoListRun allowPrimitive env infos
      finalEnv) (wf : env.constants.WF) {name : Name}
    {found : ConstantInfo}
    (lookup : finalEnv.constants.find? name = some found) :
    env.constants.find? name = some found ∨
      ∃ info ∈ infos, found = .recInfo info ∧ info.name = name := by
  induction run with
  | nil => exact .inl lookup
  | @cons infosTail finalEnvTail startEnv inserted checkName tail ih =>
      have fresh := VInductDecl.checkName_constants_fresh checkName
      rcases ih (wf.insert _ _ fresh) lookup with mid |
          ⟨info, member, tagged_eq, name_eq⟩
      · change (startEnv.constants.insert inserted.name
          (.recInfo inserted)).find? name = _ at mid
        rw [wf.find?_insert] at mid
        split at mid
        · rename_i name_equal
          exact .inr ⟨inserted, List.mem_cons_self,
            (Option.some.inj mid).symm, LawfulBEq.eq_of_beq name_equal⟩
        · exact .inl mid
      · exact .inr ⟨info, List.mem_cons_of_mem inserted member,
          tagged_eq, name_eq⟩

/-- Every recursor lookup in the output of the declaration fold is either an
unchanged input lookup or one of the records inserted by that fold. -/
theorem _root_.Lean4Lean.AddInductive.DeclareRecursorInfoListRun.map_lookup_cases
    (run : AddInductive.DeclareRecursorInfoListRun allowPrimitive env infos
      finalEnv) (wf : env.constants.WF) {name : Name}
    {info : RecursorVal}
    (found : finalEnv.constants.find? name = some (.recInfo info)) :
    env.constants.find? name = some (.recInfo info) ∨
      info ∈ infos ∧ info.name = name := by
  induction run with
  | nil => exact .inl found
  | @cons infosTail finalEnvTail startEnv inserted checkName tail ih =>
      have fresh := VInductDecl.checkName_constants_fresh checkName
      rcases ih (wf.insert _ _ fresh) found with mid | member
      · change (startEnv.constants.insert inserted.name
          (.recInfo inserted)).find? name = _ at mid
        rw [wf.find?_insert] at mid
        split at mid
        · rename_i name_equal
          have inserted_name_eq : inserted.name = name :=
            LawfulBEq.eq_of_beq name_equal
          have tagged_eq :
              (.recInfo inserted : ConstantInfo) = .recInfo info :=
            Option.some.inj mid
          have info_eq : inserted = info :=
            ConstantInfo.recInfo.inj tagged_eq
          exact .inr ⟨info_eq ▸ List.mem_cons_self,
            info_eq ▸ inserted_name_eq⟩
        · exact .inl mid
      · exact .inr ⟨List.mem_cons_of_mem inserted member.1, member.2⟩

/--
info: 'Lean4Lean.AddInductive.DeclareRecursorInfoListRun.map_lookup_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms AddInductive.DeclareRecursorInfoListRun.map_lookup_cases

/--
info: 'Lean4Lean.AddInductive.DeclareRecursorInfoListRun.constant_lookup_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms AddInductive.DeclareRecursorInfoListRun.constant_lookup_cases

/-- The three declaration phases of one retained ordinary execution reserve a
single collision-free family/constructor/recursor name inventory.  The proof
uses the real phase boundaries: each later trace checks freshness against the
environment containing every earlier phase. -/
theorem _root_.Lean4Lean.AddInductive.NormalizationRecursorExecution.declaredNames_nodup
    {nparams : Nat} {types : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    (execution : AddInductive.NormalizationRecursorExecution nparams types
      numNested isUnsafe context)
    (validationMapWF : execution.eliminationExecution.normalization
      |>.validationContext.env.constants.WF) :
    (execution.eliminationExecution.normalization.declaredInfos.map
        (·.name) ++
      execution.eliminationExecution.declaredConstructorInfos.map
        (·.name) ++
      execution.recursors.infos.map (·.name)).Nodup := by
  let familyTrace :=
    execution.eliminationExecution.normalization.declareTrace
  let constructorTrace :=
    execution.eliminationExecution.declareConstructorTrace
  let recursorTrace := execution.recursors.trace
  have familyMapWF := familyTrace.map_wf validationMapWF
  have constructorMapWF := constructorTrace.map_wf familyMapWF
  have recursorInitialMapWF :
      execution.recursors.initialEnv.constants.WF := by
    rw [execution.recursor_initialEnv_eq]
    exact constructorMapWF
  have familyNodup := familyTrace.names_nodup validationMapWF
  have constructorNodup := constructorTrace.names_nodup familyMapWF
  have recursorNodup := recursorTrace.names_nodup recursorInitialMapWF
  rw [List.nodup_append]
  refine ⟨?_, recursorNodup, ?_⟩
  · rw [List.nodup_append]
    refine ⟨familyNodup, constructorNodup, ?_⟩
    intro familyName familyMember constructorName constructorMember equal
    obtain ⟨familyInfo, familyInfoMember, rfl⟩ :=
      List.mem_map.1 familyMember
    obtain ⟨constructorInfo, constructorInfoMember, rfl⟩ :=
      List.mem_map.1 constructorMember
    have present := familyTrace.map_lookup validationMapWF familyInfoMember
    have fresh := constructorTrace.names_fresh familyMapWF constructorInfo
      constructorInfoMember
    rw [← equal, present] at fresh
    contradiction
  · intro oldName oldMember recursorName recursorMember equal
    obtain ⟨recursorInfo, recursorInfoMember, rfl⟩ :=
      List.mem_map.1 recursorMember
    have fresh := recursorTrace.names_fresh recursorInitialMapWF recursorInfo
      recursorInfoMember
    rcases List.mem_append.1 oldMember with familyMember | constructorMember
    · obtain ⟨familyInfo, familyInfoMember, rfl⟩ :=
        List.mem_map.1 familyMember
      have familyPresent := familyTrace.map_lookup validationMapWF
        familyInfoMember
      have constructorPresent := constructorTrace.preserve_map_lookup
        familyMapWF familyPresent
      have present : execution.recursors.initialEnv.constants.find?
          familyInfo.name = some (.inductInfo familyInfo) := by
        rw [execution.recursor_initialEnv_eq]
        exact constructorPresent
      rw [← equal, present] at fresh
      contradiction
    · obtain ⟨constructorInfo, constructorInfoMember, rfl⟩ :=
        List.mem_map.1 constructorMember
      have constructorPresent := constructorTrace.map_lookup familyMapWF
        constructorInfoMember
      have present : execution.recursors.initialEnv.constants.find?
          constructorInfo.name = some (.ctorInfo constructorInfo) := by
        rw [execution.recursor_initialEnv_eq]
        exact constructorPresent
      rw [← equal, present] at fresh
      contradiction

/-- The retained declaration inventory is not merely collision-free: its
three phases are exactly the family, family-major constructor, and canonical
recursor names of the ordinary source block. -/
theorem _root_.Lean4Lean.AddInductive.NormalizationRecursorExecution.declaredNames_eq_sources
    {nparams : Nat} {types : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    (execution : AddInductive.NormalizationRecursorExecution nparams types
      numNested isUnsafe context)
    (producedExecution :
      AddInductive.NormalizationRecursorExecution.buildExecution nparams
        types numNested isUnsafe context = .ok execution) :
    execution.eliminationExecution.normalization.declaredInfos.map
        (·.name) ++
      execution.eliminationExecution.declaredConstructorInfos.map
        (·.name) ++
      execution.recursors.infos.map (·.name) =
      types.map (·.name) ++
        types.flatMap (fun source => source.ctors.map (·.name)) ++
        types.map (fun source => (.str source.name "rec" : Name)) := by
  have normalizationProduced :=
    execution.normalization_run producedExecution
  have nindicesSize :=
    execution.eliminationExecution.normalization.validationNindicesSize_all
      normalizationProduced
  have familyNames :
      execution.eliminationExecution.normalization.declaredInfos.map
          (·.name) = types.map (·.name) := by
    simpa only [AddInductive.NormalizationCandidateExecution.declaredInfos,
      List.toList_toArray] using
      AddInductive.declaredInductiveInfos_names
        execution.eliminationExecution.normalization.stats nparams
        types.toArray numNested isUnsafe
        execution.eliminationExecution.normalization.validationContext
        (by simpa using nindicesSize)
  have constructorNames :
      execution.eliminationExecution.declaredConstructorInfos.map
          (·.name) =
        types.flatMap (fun source => source.ctors.map (·.name)) := by
    simpa only [
      AddInductive.NormalizationEliminationExecution.declaredConstructorInfos,
      List.toList_toArray] using
      AddInductive.declaredConstructorInfos_names
        execution.eliminationExecution.normalization.stats types.toArray
        isUnsafe execution.eliminationExecution.constructorContext
  have recursorNames : execution.recursors.infos.map (·.name) =
      types.map (fun source => (.str source.name "rec" : Name)) := by
    simpa only [List.toList_toArray, mkRecName] using
      AddInductive.declareRecursors_infos_names execution.recursorsRun
  rw [familyNames, constructorNames, recursorNames]

/--
info: 'Lean4Lean.AddInductive.NormalizationRecursorExecution.declaredNames_nodup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms AddInductive.NormalizationRecursorExecution.declaredNames_nodup

/--
info: 'Lean4Lean.AddInductive.NormalizationRecursorExecution.declaredNames_eq_sources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms AddInductive.NormalizationRecursorExecution.declaredNames_eq_sources

/-! ## Nested-restoration declaration provenance -/

/-- The mixed metadata fold used by nested restoration preserves
persistent-map well-formedness. -/
theorem _root_.Lean4Lean.DeclareRestoredInfoListRun.map_wf
    (run : DeclareRestoredInfoListRun allowPrimitive env infos
      finalEnv) (wf : env.constants.WF) : finalEnv.constants.WF := by
  induction run with
  | nil => exact wf
  | cons checkName tail ih =>
      apply ih
      exact wf.insert _ _ (VInductDecl.checkName_constants_fresh checkName)

/-- Nested restoration preserves every lookup already present in its input
map. -/
theorem _root_.Lean4Lean.DeclareRestoredInfoListRun.preserve_map_lookup
    (run : DeclareRestoredInfoListRun allowPrimitive env infos
      finalEnv) (wf : env.constants.WF)
    (old : env.constants.find? name = some found) :
    finalEnv.constants.find? name = some found := by
  induction run with
  | nil => exact old
  | @cons infosTail finalEnvTail startEnv inserted checkName tail ih =>
      have fresh := VInductDecl.checkName_constants_fresh checkName
      have mid : (startEnv.add inserted).constants.find? name =
          some found := by
        change (startEnv.constants.insert inserted.name inserted).find? name = _
        rw [wf.find?_insert]
        split
        · rename_i equal
          have nameEq : inserted.name = name := LawfulBEq.eq_of_beq equal
          subst name
          rw [old] at fresh
          contradiction
        · exact old
      exact ih (wf.insert _ _ fresh) mid

/-- Every restored metadata record remains at its own name after the complete
mixed declaration fold. -/
theorem _root_.Lean4Lean.DeclareRestoredInfoListRun.map_lookup
    (run : DeclareRestoredInfoListRun allowPrimitive env infos
      finalEnv) (wf : env.constants.WF) {info : ConstantInfo}
    (member : info ∈ infos) :
    finalEnv.constants.find? info.name = some info := by
  induction run with
  | nil => contradiction
  | @cons infosTail finalEnvTail startEnv inserted checkName tail ih =>
      rcases List.mem_cons.1 member with rfl | member
      · apply tail.preserve_map_lookup
          (wf.insert _ _ (VInductDecl.checkName_constants_fresh checkName))
        change (startEnv.constants.insert info.name info).find? info.name = _
        rw [wf.find?_insert]
        simp
      · exact ih (wf.insert _ _
          (VInductDecl.checkName_constants_fresh checkName)) member

/-- Every record restored by the mixed declaration fold was absent from the
input map at its own name. -/
theorem _root_.Lean4Lean.DeclareRestoredInfoListRun.map_fresh
    (run : DeclareRestoredInfoListRun allowPrimitive env infos finalEnv)
    (wf : env.constants.WF) {info : ConstantInfo}
    (member : info ∈ infos) :
    env.constants.find? info.name = none := by
  induction run with
  | nil => contradiction
  | @cons infosTail finalEnvTail startEnv inserted checkName tail ih =>
      rcases List.mem_cons.1 member with rfl | member
      · exact VInductDecl.checkName_constants_fresh checkName
      · have freshAfter := ih
          (wf.insert _ _ (VInductDecl.checkName_constants_fresh checkName))
          member
        change (startEnv.constants.insert inserted.name inserted).find?
          info.name = none at freshAfter
        rw [wf.find?_insert] at freshAfter
        split at freshAfter
        · contradiction
        · exact freshAfter

/-- Every record accepted by a nonprimitive mixed restoration fold avoids
both the kernel primitive inventory and its reflected Theory subset. -/
theorem _root_.Lean4Lean.DeclareRestoredInfoListRun.names_not_primitive
    (run : DeclareRestoredInfoListRun false env infos finalEnv) :
    ∀ info ∈ infos,
      info.name ∉ VEnv.reflectedPrimitiveNames ∧
        Environment.primitives.contains info.name = false := by
  induction run with
  | nil => intro info member; nomatch member
  | cons checkName tail ih =>
      intro info member
      rcases List.mem_cons.mp member with rfl | member
      · have fresh := VInductDecl.checkName_primitives_fresh checkName
        exact ⟨VInductDecl.not_reflectedPrimitive_of_primitives_fresh fresh,
          fresh⟩
      · exact ih info member

/-- Classify any final lookup after nested restoration as either unchanged
input metadata or the exact record selected from the retained restored
inventory. -/
theorem _root_.Lean4Lean.DeclareRestoredInfoListRun.map_lookup_cases
    (run : DeclareRestoredInfoListRun allowPrimitive env infos
      finalEnv) (wf : env.constants.WF) {name : Name}
    {found : ConstantInfo}
    (lookup : finalEnv.constants.find? name = some found) :
    env.constants.find? name = some found ∨
      found ∈ infos ∧ found.name = name := by
  induction run with
  | nil => exact .inl lookup
  | @cons infosTail finalEnvTail startEnv inserted checkName tail ih =>
      have fresh := VInductDecl.checkName_constants_fresh checkName
      rcases ih (wf.insert _ _ fresh) lookup with mid | member
      · change (startEnv.constants.insert inserted.name inserted).find? name = _
          at mid
        rw [wf.find?_insert] at mid
        split at mid
        · rename_i name_equal
          have inserted_eq : inserted = found := Option.some.inj mid
          exact .inr ⟨inserted_eq ▸ List.mem_cons_self,
            inserted_eq ▸ LawfulBEq.eq_of_beq name_equal⟩
        · exact .inl mid
      · exact .inr ⟨List.mem_cons_of_mem inserted member.1, member.2⟩

/-- A final restored family lookup is old or is the exact tagged family
record in the restoration inventory. -/
theorem _root_.Lean4Lean.DeclareRestoredInfoListRun.family_map_lookup_cases
    (run : DeclareRestoredInfoListRun allowPrimitive env infos
      finalEnv) (wf : env.constants.WF) {name : Name}
    {info : InductiveVal}
    (lookup : finalEnv.constants.find? name = some (.inductInfo info)) :
    env.constants.find? name = some (.inductInfo info) ∨
      (.inductInfo info : ConstantInfo) ∈ infos ∧ info.name = name := by
  simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using
    run.map_lookup_cases wf lookup

/-- A final restored constructor lookup is old or is the exact tagged
constructor record in the restoration inventory. -/
theorem _root_.Lean4Lean.DeclareRestoredInfoListRun.constructor_map_lookup_cases
    (run : DeclareRestoredInfoListRun allowPrimitive env infos
      finalEnv) (wf : env.constants.WF) {name : Name}
    {info : ConstructorVal}
    (lookup : finalEnv.constants.find? name = some (.ctorInfo info)) :
    env.constants.find? name = some (.ctorInfo info) ∨
      (.ctorInfo info : ConstantInfo) ∈ infos ∧ info.name = name := by
  simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using
    run.map_lookup_cases wf lookup

/-- A final restored recursor lookup is old or is the exact tagged recursor
record in the restoration inventory. -/
theorem _root_.Lean4Lean.DeclareRestoredInfoListRun.recursor_map_lookup_cases
    (run : DeclareRestoredInfoListRun allowPrimitive env infos
      finalEnv) (wf : env.constants.WF) {name : Name}
    {info : RecursorVal}
    (lookup : finalEnv.constants.find? name = some (.recInfo info)) :
    env.constants.find? name = some (.recInfo info) ∨
      (.recInfo info : ConstantInfo) ∈ infos ∧ info.name = name := by
  simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using
    run.map_lookup_cases wf lookup

/--
info: 'Lean4Lean.DeclareRestoredInfoListRun.map_lookup_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms DeclareRestoredInfoListRun.map_lookup_cases

/-- The generated-recursor declaration trace replayed as an exact Theory
insertion fold, including the implementation K-flag inventory but no
whole-history translation postcondition. -/
structure RecursorDeclarationInsertionRun
    (allowPrimitive : Bool) (kernelEnv finalKernelEnv : Environment)
    (infos : List RecursorVal) (ctorEnv : VEnv)
    (raws : List VConstVal) (kTarget : Bool) where
  recEnv : VEnv
  kernelTrace : AddInductive.DeclareRecursorInfoListRun
    allowPrimitive kernelEnv infos finalKernelEnv
  addRecs : AddInductConstants .recursor kernelEnv.constants ctorEnv raws
    finalKernelEnv.constants recEnv
  recK : RecursorMapKMatches finalKernelEnv.constants raws kTarget

/-- Replay a retained generated-recursor declaration equation from semantic
translations and `Aligned` name-domain correspondence.  The resulting K
witness is read from the exact inserted implementation records. -/
noncomputable def recursorDeclarationInsertion
    {allowPrimitive : Bool} {kernelEnv finalKernelEnv : Environment}
    {infos : List RecursorVal} {ctorEnv : VEnv}
    {raws : List VConstVal}
    (declare : AddInductive.declareRecursorInfoList allowPrimitive infos
      kernelEnv = .ok finalKernelEnv)
    (evidence : List.Forall₂
      (fun info raw => TrConstVal .safe ctorEnv (.recInfo info) raw)
      infos raws)
    (infosK : ∀ info ∈ infos, info.k = kTarget)
    (pre : Aligned safety kernelEnv.constants ctorEnv) :
    RecursorDeclarationInsertionRun allowPrimitive kernelEnv finalKernelEnv
      infos ctorEnv raws kTarget := by
  induction infos generalizing kernelEnv finalKernelEnv ctorEnv raws with
  | nil =>
      cases raws with
      | nil =>
          simp only [AddInductive.declareRecursorInfoList,
            Except.ok.injEq] at declare
          subst finalKernelEnv
          exact {
            recEnv := ctorEnv
            kernelTrace := .nil
            addRecs := .nil
            recK := by simp [RecursorMapKMatches] }
      | cons raw raws =>
          have impossible : False := by cases evidence
          exact impossible.elim
  | cons info infos ih =>
      cases raws with
      | nil =>
          have impossible : False := by cases evidence
          exact impossible.elim
      | cons raw raws =>
          have related := constructor_forall₂_cons_iff.mp evidence
          cases hcheck : kernelEnv.checkName info.name allowPrimitive with
          | error error =>
              have impossible : False := by
                simp only [AddInductive.declareRecursorInfoList] at declare
                rw [hcheck] at declare
                contradiction
              exact impossible.elim
          | ok value =>
              have value_eq : value = () := Subsingleton.elim _ _
              subst value
              have tailDeclare :
                  AddInductive.declareRecursorInfoList allowPrimitive infos
                    (kernelEnv.add (.recInfo info)) = .ok finalKernelEnv := by
                simpa only [AddInductive.declareRecursorInfoList, hcheck,
                  Bind.bind, Except.bind] using declare
              have mapFresh : kernelEnv.constants.find? raw.name = none := by
                rw [← related.1.2]
                simpa [ConstantInfo.toConstantVal, ConstantInfo.name] using
                  checkName_constants_fresh hcheck
              have envFresh : ctorEnv.constants raw.name = none := by
                cases found : ctorEnv.constants raw.name with
                | none => rfl
                | some ci =>
                    obtain ⟨kernelInfo, kernelFound, _⟩ :=
                      pre.find?_iff.mpr ⟨ci, found⟩
                    rw [mapFresh] at kernelFound
                    contradiction
              let nextEnv : VEnv := {
                ctorEnv with
                constants := fun name =>
                  if raw.name = name then some raw.toVConstant
                  else ctorEnv.constants name }
              have added : ctorEnv.addConst raw.name raw.toVConstant =
                  some nextEnv := by
                simp [VEnv.addConst, envFresh, nextEnv]
              let add : AddInductConstant .recursor kernelEnv.constants
                  ctorEnv raw (kernelEnv.add (.recInfo info)).constants
                  nextEnv := {
                info := .recInfo info
                kind_eq := trivial
                tr := related.1
                map_fresh := mapFresh
                env_add := added
                map_add := by
                  rw [← related.1.2]
                  rfl }
              have le : ctorEnv ≤ nextEnv := VEnv.addConst_le added
              have tailEvidence : List.Forall₂
                  (fun info raw =>
                    TrConstVal .safe nextEnv (.recInfo info) raw)
                  infos raws :=
                Lean4Lean.List.Forall₂.imp (h := related.2)
                  (fun _ _ relation => relation.mono le)
              have tailInfosK : ∀ other ∈ infos,
                  other.k = kTarget := by
                intro other member
                exact infosK other (.tail _ member)
              let tailResult := ih tailDeclare tailEvidence tailInfosK
                (pre.addInductConstant add)
              exact {
                recEnv := tailResult.recEnv
                kernelTrace := .cons hcheck tailResult.kernelTrace
                addRecs := .cons add tailResult.addRecs
                recK := by
                  intro candidate member
                  rcases List.mem_cons.mp member with rfl | member
                  · refine ⟨.recInfo info, ?_, ?_⟩
                    · simpa [add] using
                        tailResult.addRecs.preserve_map_lookup
                          (add.map_wf pre.map_wf)
                          (add.map_lookup pre.map_wf)
                    · exact infosK info (.head _)
                  · exact tailResult.recK candidate member }

/-- A source-ordered generated-recursor declaration interpreted
simultaneously in the retained kernel environment and its Theory model. -/
structure RecursorDeclarationStagingRun
    (allowPrimitive : Bool) (kernelEnv finalKernelEnv : Environment)
    (infos : List RecursorVal) (ctorEnv : VEnv)
    (raws : List VConstVal) (kTarget Q : Bool) where
  recEnv : VEnv
  kernelTrace : AddInductive.DeclareRecursorInfoListRun
    allowPrimitive kernelEnv infos finalKernelEnv
  addRecs : AddInductConstants .recursor kernelEnv.constants ctorEnv raws
    finalKernelEnv.constants recEnv
  recK : RecursorMapKMatches finalKernelEnv.constants raws kTarget
  trenv : TrEnv' .safe finalKernelEnv.constants Q recEnv

/-- Interpret the exact generated-recursor insertion trace.  Synthesis owns
the records and their rules; this interpreter consumes only their semantic
translation and Theory well-formedness, then constructs the matching Theory
fold and translated post-state. -/
noncomputable def recursorDeclarationStaging
    {allowPrimitive : Bool} {kernelEnv finalKernelEnv : Environment}
    {infos : List RecursorVal} {ctorEnv : VEnv}
    {raws : List VConstVal} {Q : Bool}
    (declare : AddInductive.declareRecursorInfoList allowPrimitive infos
      kernelEnv = .ok finalKernelEnv)
    (evidence : List.Forall₂
      (fun info raw => TrConstVal .safe ctorEnv (.recInfo info) raw)
      infos raws)
    (infosK : ∀ info ∈ infos, info.k = kTarget)
    (rawsWF : ∀ raw ∈ raws, raw.toVConstant.WF ctorEnv)
    (pre : TrEnv' .safe kernelEnv.constants Q ctorEnv) :
    RecursorDeclarationStagingRun allowPrimitive kernelEnv finalKernelEnv
      infos ctorEnv raws kTarget Q := by
  let insertion := recursorDeclarationInsertion declare evidence infosK
    pre.aligned
  exact {
    recEnv := insertion.recEnv
    kernelTrace := insertion.kernelTrace
    addRecs := insertion.addRecs
    recK := insertion.recK
    trenv := insertion.addRecs.trEnvStaging rawsWF pre }

/-! ## Primitive-name provenance for exact metadata staging -/

/-- In an exact nonprimitive family staging run, every raw Theory family name
inherits the primitive-name checks of its corresponding host insertion. -/
theorem FamilyDeclarationStagingRun.raw_names_not_primitive
    {allowPrimitive : Bool} {kernelEnv finalKernelEnv : Environment}
    {infos : List InductiveVal} {env finalEnv : VEnv}
    {raws : List VConstVal} {Q : Bool}
    (run : FamilyDeclarationStagingRun allowPrimitive kernelEnv
      finalKernelEnv infos env finalEnv raws Q)
    (allowPrimitive_eq : allowPrimitive = false)
    (mapWF : kernelEnv.constants.WF) :
    ∀ raw ∈ raws,
      raw.name ∉ VEnv.reflectedPrimitiveNames ∧
        Environment.primitives.contains raw.name = false := by
  subst allowPrimitive
  intro raw member
  obtain ⟨found, lookup, _, _⟩ :=
    run.addTypes.translated_lookup mapWF member
  rcases run.kernelTrace.constant_lookup_cases mapWF lookup with
    old | ⟨info, infoMember, _, nameEq⟩
  · have fresh := run.addTypes.map_fresh mapWF member
    rw [old] at fresh
    contradiction
  · have names := run.kernelTrace.names_not_primitive info infoMember
    simpa only [nameEq] using names

/-- In an exact nonprimitive constructor staging run, every raw Theory
constructor name inherits the primitive-name checks of its host insertion. -/
theorem ConstructorDeclarationStagingRun.raw_names_not_primitive
    {allowPrimitive : Bool} {kernelEnv finalKernelEnv : Environment}
    {infos : List ConstructorVal} {typeEnv : VEnv}
    {raws : List VConstVal} {Q : Bool}
    (run : ConstructorDeclarationStagingRun allowPrimitive kernelEnv
      finalKernelEnv infos typeEnv raws Q)
    (allowPrimitive_eq : allowPrimitive = false)
    (mapWF : kernelEnv.constants.WF) :
    ∀ raw ∈ raws,
      raw.name ∉ VEnv.reflectedPrimitiveNames ∧
        Environment.primitives.contains raw.name = false := by
  subst allowPrimitive
  intro raw member
  obtain ⟨found, lookup, _, _⟩ :=
    run.addCtors.translated_lookup mapWF member
  rcases run.kernelTrace.constant_lookup_cases mapWF lookup with
    old | ⟨info, infoMember, _, nameEq⟩
  · have fresh := run.addCtors.map_fresh mapWF member
    rw [old] at fresh
    contradiction
  · have names := run.kernelTrace.names_not_primitive info infoMember
    simpa only [nameEq] using names

/-- In an exact nonprimitive recursor staging run, every raw Theory recursor
name inherits the primitive-name checks of its host insertion. -/
theorem RecursorDeclarationStagingRun.raw_names_not_primitive
    {allowPrimitive : Bool} {kernelEnv finalKernelEnv : Environment}
    {infos : List RecursorVal} {ctorEnv : VEnv}
    {raws : List VConstVal} {kTarget Q : Bool}
    (run : RecursorDeclarationStagingRun allowPrimitive kernelEnv
      finalKernelEnv infos ctorEnv raws kTarget Q)
    (allowPrimitive_eq : allowPrimitive = false)
    (mapWF : kernelEnv.constants.WF) :
    ∀ raw ∈ raws,
      raw.name ∉ VEnv.reflectedPrimitiveNames ∧
        Environment.primitives.contains raw.name = false := by
  subst allowPrimitive
  intro raw member
  obtain ⟨found, lookup, _, _⟩ :=
    run.addRecs.translated_lookup mapWF member
  rcases run.kernelTrace.constant_lookup_cases mapWF lookup with
    old | ⟨info, infoMember, _, nameEq⟩
  · have fresh := run.addRecs.map_fresh mapWF member
    rw [old] at fresh
    contradiction
  · have names := run.kernelTrace.names_not_primitive info infoMember
    simpa only [nameEq] using names

/-- Every raw constructor constant selected by a complete block-generation
run is well formed in the shared post-family Theory environment. -/
theorem BlockGenerationRun.constructorConstantsWF
    {source : VInductDecl} {generation : BlockGenerationChecked source}
    {env blockEnv : VEnv}
    (run : BlockGenerationRun generation env blockEnv) :
    ∀ constructor ∈ source.blockConstructorConstants,
      constructor.toVConstant.WF blockEnv := by
  intro constructor member
  have member' : constructor ∈ generation.flatCtors.map (·.ctor.raw) := by
    rwa [generation.flatCtors_map_raw]
  obtain ⟨normalized, normalizedMember, rfl⟩ := List.mem_map.mp member'
  show blockEnv.IsType normalized.ctor.raw.uvars [] normalized.ctor.raw.type
  rw [generation.flatCtor_uvars normalizedMember]
  exact (run.constructors.get normalized normalizedMember).wf.rawDeclared_isType

/-- A complete block normalization/elimination execution together with the
same full generation-shape check used by the earlier normalization-only
producer.  Its embedded normalization execution erases definitionally to the
established producer boundary. -/
structure ProducedBlockEliminationShapeCandidate
    (source : VInductDecl) (kernelSources : List InductiveType)
    (numNested : Nat) (isUnsafe : Bool)
    (context : AddInductive.Context) where
  execution : AddInductive.NormalizationEliminationExecution source.nparams
    kernelSources numNested isUnsafe context
  producedExecution :
    AddInductive.NormalizationEliminationExecution.buildExecution
        source.nparams kernelSources numNested isUnsafe context = .ok execution
  shape : normalizationCandidateBlockGenerationShape source
    execution.candidate = true

theorem ProducedBlockEliminationShapeCandidate.eq_of_execution_eq
    (left right : ProducedBlockEliminationShapeCandidate source kernelSources
      numNested isUnsafe context)
    (execution_eq : left.execution = right.execution) : left = right := by
  cases left with
  | mk leftExecution leftProduced leftShape =>
      cases right with
      | mk rightExecution rightProduced rightShape =>
          simp only at execution_eq
          subst rightExecution
          rfl

/-- Erase the post-constructor decisions while retaining the exact earlier
block-generation producer. -/
def ProducedBlockEliminationShapeCandidate.base
    (produced : ProducedBlockEliminationShapeCandidate source kernelSources
      numNested isUnsafe context) :
    ProducedBlockGenerationShapeCandidate source kernelSources numNested
      isUnsafe context where
  execution := produced.execution.normalization
  producedExecution := produced.execution.normalization_run
    produced.producedExecution
  shape := produced.shape

def ProducedBlockEliminationShapeCandidate.candidate
    (produced : ProducedBlockEliminationShapeCandidate source kernelSources
      numNested isUnsafe context) :
    AddInductive.NormalizationCandidate kernelSources :=
  produced.execution.candidate

/-- Run the retained normalization pass through constructor declaration and
both elimination decisions, rejecting only a failure of that real execution
or of the existing complete generation-shape gate. -/
def produceBlockEliminationShapeCandidate
    (source : VInductDecl) (kernelSources : List InductiveType)
    (numNested : Nat) (isUnsafe : Bool)
    (context : AddInductive.Context) :
    Except Exception (ProducedBlockEliminationShapeCandidate source
      kernelSources numNested isUnsafe context) :=
  match producedExecution :
      AddInductive.NormalizationEliminationExecution.buildExecution
        source.nparams kernelSources numNested isUnsafe context with
  | .error error => .error error
  | .ok execution =>
      if shape : normalizationCandidateBlockGenerationShape source
          execution.candidate then
        .ok { execution, producedExecution, shape }
      else
        .error (.other
          "normalization/elimination candidate block does not preserve the generation spine")

private theorem produceBlockEliminationShapeCandidate_match_ok
    {source : VInductDecl} {kernelSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    (result : Except Exception
      (AddInductive.NormalizationEliminationExecution source.nparams
        kernelSources numNested isUnsafe context))
    (toProducedExecution : ∀ actual, result = .ok actual →
      AddInductive.NormalizationEliminationExecution.buildExecution
          source.nparams kernelSources numNested isUnsafe context = .ok actual)
    {execution : AddInductive.NormalizationEliminationExecution source.nparams
      kernelSources numNested isUnsafe context}
    (result_ok : result = .ok execution)
    (shape : normalizationCandidateBlockGenerationShape source
      execution.candidate = true) :
    (match result_eq : result with
    | .error error => Except.error error
    | .ok actual =>
      if actualShape : normalizationCandidateBlockGenerationShape source
          actual.candidate then
        Except.ok (show ProducedBlockEliminationShapeCandidate source
            kernelSources numNested isUnsafe context from {
          execution := actual
          producedExecution := toProducedExecution actual result_eq
          shape := actualShape })
      else
        Except.error (.other
          "normalization/elimination candidate block does not preserve the generation spine")) =
      Except.ok (show ProducedBlockEliminationShapeCandidate source
          kernelSources numNested isUnsafe context from {
        execution
        producedExecution := toProducedExecution execution result_ok
        shape }) := by
  subst result
  simp [shape]

theorem produceBlockEliminationShapeCandidate_eq_ok
    {source : VInductDecl} {kernelSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {execution : AddInductive.NormalizationEliminationExecution source.nparams
      kernelSources numNested isUnsafe context}
    (producedExecution :
      AddInductive.NormalizationEliminationExecution.buildExecution
          source.nparams kernelSources numNested isUnsafe context = .ok execution)
    (shape : normalizationCandidateBlockGenerationShape source
      execution.candidate = true) :
    produceBlockEliminationShapeCandidate source kernelSources numNested
        isUnsafe context = .ok { execution, producedExecution, shape } := by
  unfold produceBlockEliminationShapeCandidate
  exact produceBlockEliminationShapeCandidate_match_ok
    (result :=
      AddInductive.NormalizationEliminationExecution.buildExecution
        source.nparams kernelSources numNested isUnsafe context)
    (toProducedExecution := fun _ result_eq => result_eq)
    producedExecution shape

/-- A complete block-generation shape backed by the stronger ordinary
execution that has already synthesized and declared every recursor. -/
structure ProducedBlockRecursorShapeCandidate
    (source : VInductDecl) (kernelSources : List InductiveType)
    (numNested : Nat) (isUnsafe : Bool)
    (context : AddInductive.Context) where
  execution : AddInductive.NormalizationRecursorExecution source.nparams
    kernelSources numNested isUnsafe context
  producedExecution :
    AddInductive.NormalizationRecursorExecution.buildExecution source.nparams
        kernelSources numNested isUnsafe context = .ok execution
  shape : normalizationCandidateBlockGenerationShape source
    execution.candidate = true
  kernelSources_nonempty : kernelSources.isEmpty = false

theorem ProducedBlockRecursorShapeCandidate.eq_of_execution_eq
    (left right : ProducedBlockRecursorShapeCandidate source kernelSources
      numNested isUnsafe context)
    (execution_eq : left.execution = right.execution) : left = right := by
  cases left with
  | mk leftExecution leftProduced leftShape leftNonempty =>
      cases right with
      | mk rightExecution rightProduced rightShape rightNonempty =>
          simp only at execution_eq
          subst rightExecution
          rfl

/-- Erase the recursor phase while retaining the exact earlier block
normalization/elimination producer. -/
def ProducedBlockRecursorShapeCandidate.eliminationBase
    (produced : ProducedBlockRecursorShapeCandidate source kernelSources
      numNested isUnsafe context) :
    ProducedBlockEliminationShapeCandidate source kernelSources numNested
      isUnsafe context where
  execution := produced.execution.eliminationExecution
  producedExecution := produced.execution.prefix_run produced.producedExecution
  shape := produced.shape

def ProducedBlockRecursorShapeCandidate.candidate
    (produced : ProducedBlockRecursorShapeCandidate source kernelSources
      numNested isUnsafe context) :
    AddInductive.NormalizationCandidate kernelSources :=
  produced.execution.candidate

/-- The real declaration traces discharge the raw Theory block's generated-
name collision check.  Source-order equations on both sides ensure this is the
same inventory as the semantic hierarchy, not merely a setwise coincidence. -/
theorem ProducedBlockRecursorShapeCandidate.semanticGeneratedNames_nodup
    {source : VInductDecl} {kernelSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    (produced : ProducedBlockRecursorShapeCandidate source kernelSources
      numNested isUnsafe context)
    {env blockEnv : VEnv} {Us : List Name}
    (semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source)
    (validationMapWF : produced.execution.eliminationExecution.normalization
      |>.validationContext.env.constants.WF) :
    (blockGeneratedNames source.types).Nodup := by
  rw [semantic.blockGeneratedNames_eq_sources]
  rw [← produced.execution.declaredNames_eq_sources
    produced.producedExecution]
  exact produced.execution.declaredNames_nodup validationMapWF

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.semanticGeneratedNames_nodup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms ProducedBlockRecursorShapeCandidate.semanticGeneratedNames_nodup

/-- Header preservation transports the producer-derived collision proof to
the exact normalized view consumed by `CheckedBlock`. -/
theorem ProducedBlockRecursorShapeCandidate.semanticViewGeneratedNames_nodup
    {source : VInductDecl} {kernelSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    (produced : ProducedBlockRecursorShapeCandidate source kernelSources
      numNested isUnsafe context)
    {env blockEnv : VEnv} {Us : List Name}
    (semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source)
    (validationMapWF : produced.execution.eliminationExecution.normalization
      |>.validationContext.env.constants.WF) :
    (blockGeneratedNames semantic.families.views).Nodup := by
  rw [semantic.viewBlockGeneratedNames_eq_sources]
  rw [← produced.execution.declaredNames_eq_sources
    produced.producedExecution]
  exact produced.execution.declaredNames_nodup validationMapWF

private theorem list_eq_cons_of_isEmpty_false
    (sources : List α) (nonempty : sources.isEmpty = false) :
    ∃ source tail, sources = source :: tail := by
  cases sources with
  | nil => simp at nonempty
  | cons source tail => exact ⟨source, tail, rfl⟩

/-- The retained ordinary validator and generation-spine gate determine the
exact parameter-prefix length of the semantic normalized view. -/
theorem ProducedBlockRecursorShapeCandidate.semanticViewParams_length
    {source : VInductDecl} {kernelSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    (produced : ProducedBlockRecursorShapeCandidate source kernelSources
      numNested isUnsafe context)
    {env blockEnv : VEnv} {Us : List Name}
    (semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source)
    (context_lctx_eq : context.lctx = {}) :
    (blockParams semantic.normalization.view.nparams
      semantic.normalization.view.types).length =
        semantic.normalization.view.nparams := by
  have normalizationProduced := produced.execution.normalization_run
    produced.producedExecution
  obtain ⟨kernelSource, remainingSources, sources_eq⟩ :=
    list_eq_cons_of_isEmpty_false kernelSources
      produced.kernelSources_nonempty
  subst kernelSources
  exact semantic.viewParams_length_of_execution
    produced.execution.eliminationExecution.normalization
    normalizationProduced context_lctx_eq

/-- The exact outer producer fixes a canonical semantic view in which every
family and constructor uses the first normalized family's parameter
telescope syntactically.  This theorem establishes the analyzer-facing shape
only; semantic preservation of the rewritten prefixes must still be derived
from the retained kernel equality traces. -/
theorem
    ProducedBlockRecursorShapeCandidate.semanticCanonicalParameterSurfaces
    {source : VInductDecl} {kernelSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    (produced : ProducedBlockRecursorShapeCandidate source kernelSources
      numNested isUnsafe context)
    {env blockEnv : VEnv} {Us : List Name}
    (semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source)
    (context_lctx_eq : context.lctx = {})
    (familyMember : family ∈ semantic.canonicalNormalization.view.types) :
    VExpr.telN semantic.normalization.view.nparams family.type =
        blockParams semantic.normalization.view.nparams
          semantic.normalization.view.types ∧
      ∀ constructor ∈ family.ctors,
        VExpr.telN semantic.normalization.view.nparams constructor.type =
          blockParams semantic.normalization.view.nparams
            semantic.normalization.view.types :=
  semantic.canonicalParameterSurfaces
    (produced.semanticViewParams_length semantic context_lctx_eq)
    familyMember

/-- Canonicalization retains the exact producer-selected shared parameter
value, not merely a same-length telescope. -/
theorem ProducedBlockRecursorShapeCandidate.semanticCanonicalBlockParams
    {source : VInductDecl} {kernelSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    (produced : ProducedBlockRecursorShapeCandidate source kernelSources
      numNested isUnsafe context)
    {env blockEnv : VEnv} {Us : List Name}
    (semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source)
    (context_lctx_eq : context.lctx = {}) :
    blockParams semantic.canonicalNormalization.view.nparams
        semantic.canonicalNormalization.view.types =
      blockParams semantic.normalization.view.nparams
        semantic.normalization.view.types :=
  semantic.canonicalBlockParams
    (semantic.viewTypes_isEmpty_eq_sources.trans
      produced.kernelSources_nonempty)
    (produced.semanticViewParams_length semantic context_lctx_eq)

/-- Construct the verified reader context reached after the first family's
exact parameter/index traversal.

The operational producer proves that the retained family-validation context
is the terminal context of its first family candidate.  The dependent
semantic family head supplies the corresponding verified candidate run, so
the result is indexed by the validator's own comparison trace rather than by
a caller-selected local context. -/
theorem ProducedBlockRecursorShapeCandidate.semanticFirstFamilyContextRun
    {source : VInductDecl} {kernelSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    (produced : ProducedBlockRecursorShapeCandidate source kernelSources
      numNested isUnsafe context)
    {env blockEnv : VEnv} {Us : List Name}
    (semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source)
    (context_lctx_eq : context.lctx = {}) :
    ∃ contextRun : TypeChecker.CandidateContextRun
        (produced.execution.eliminationExecution.normalization
          |>.familyParameterComparisonTrace
            (produced.execution.normalization_run produced.producedExecution)
            produced.kernelSources_nonempty).firstContext,
      contextRun.context.venv = env ∧
      contextRun.context.lparams = Us := by
  have normalizationProduced :=
    produced.execution.normalization_run produced.producedExecution
  cases kernelSources with
  | nil =>
    have nonempty := produced.kernelSources_nonempty
    simp at nonempty
  | cons kernelSource remainingSources =>
    let normalization :=
      produced.execution.eliminationExecution.normalization
    have roots : CandidateBlockFamilySemanticListRun env blockEnv Us
        normalization.families.candidates source.types := by
      simpa only [ProducedBlockRecursorShapeCandidate.candidate,
        AddInductive.NormalizationRecursorExecution.candidate,
        AddInductive.NormalizationEliminationExecution.candidate,
        AddInductive.NormalizationCandidateExecution.candidate] using
        semantic.families
    cases hCandidates : normalization.families.candidates with
    | cons candidate candidates =>
      rw [hCandidates] at roots
      cases hRawTypes : source.types with
      | nil =>
        rw [hRawTypes] at roots
        nomatch roots
      | cons raw raws =>
        rw [hRawTypes] at roots
        cases roots with
        | cons head tail =>
          obtain ⟨inferred, recursive⟩ := head.type.recursive
          obtain ⟨terminalRun, terminalVenv, terminalLparams⟩ :=
            recursive.terminalContextRun head.type.contextRun
              head.type.venv_eq head.type.lparams_eq head.type.vlctx_eq
          have familyTypeEq :=
            produced.execution.eliminationExecution.normalization
              |>.families.produced.head_familyType
          rw [hCandidates] at familyTypeEq
          simp only [AddInductive.CandidateList.head] at familyTypeEq
          have familyContextEq := congrArg
            (fun familyType : AddInductive.CandidateFamilyType kernelSource =>
              familyType.type.trace.terminalContext) familyTypeEq
          have validationContextEq :=
            produced.execution.eliminationExecution.normalization
              |>.firstFamilyComparisonContext_eq normalizationProduced
                context_lctx_eq
          have contextEq := validationContextEq.trans familyContextEq.symm
          rw [contextEq]
          exact ⟨terminalRun, terminalVenv, terminalLparams⟩

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.semanticFirstFamilyContextRun' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.eqv_eq,
 Level.instLawfulBEqLevel,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms
  ProducedBlockRecursorShapeCandidate.semanticFirstFamilyContextRun

/-- Producer-owned raw/annotation telescope for the exact second family.

The raw-family equation fixes the second Theory source position.  The binder
count is the complete raw Pi spine selected by the block generation gate, and
the right telescope is selected solely by the recursive candidate equality
executions. -/
structure ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine
    {source : VInductDecl}
    {firstSource secondSource : InductiveType}
    {remainingSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    (produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: remainingSources) numNested isUnsafe
      context)
    {env blockEnv : VEnv} {Us : List Name}
    (semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source) where
  firstCandidate : AddInductive.CandidateFamily firstSource
  secondCandidate : AddInductive.CandidateFamily secondSource
  remainingCandidates : AddInductive.CandidateList
    AddInductive.CandidateFamily remainingSources
  candidates_eq : produced.candidate.families =
    .cons firstCandidate (.cons secondCandidate remainingCandidates)
  firstRaw : VInductiveType
  secondRaw : VInductiveType
  remainingRaws : List VInductiveType
  raws_eq : source.types = firstRaw :: secondRaw :: remainingRaws
  spineLength_eq :
    secondCandidate.familyType.type.trace.spineLength =
      (VInductDecl.ctorFields secondRaw.type).length
  storedBinders : List VExpr
  telescope : TypeChecker.TelDefEqEvidence env Us.length []
    (VExpr.telN (VInductDecl.ctorFields secondRaw.type).length secondRaw.type)
    storedBinders
  stored_length : storedBinders.length =
    (VInductDecl.ctorFields secondRaw.type).length
  terminalRun : TypeChecker.CandidateContextRun
    secondCandidate.familyType.type.trace.terminalContext
  terminal_venv : terminalRun.context.venv = env
  terminal_lparams : terminalRun.context.lparams = Us
  terminal_vlctx : terminalRun.context.vlctx.toCtx = storedBinders.reverse

/-- Select the exact second family's complete annotation-consumed telescope
from the same dependent semantic hierarchy used by outer validation. -/
theorem
    ProducedBlockRecursorShapeCandidate.semanticSecondFamilyAnnotationSpine
    {source : VInductDecl}
    {firstSource secondSource : InductiveType}
    {remainingSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    (produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: remainingSources) numNested isUnsafe
      context)
    {env blockEnv : VEnv} {Us : List Name}
    (semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source) :
    Nonempty (produced.SecondFamilyAnnotationSpine semantic) := by
  have roots := semantic.families
  have blockShape : candidateBlockFamilySemanticGenerationShape source
      produced.candidate.families source.types = true := by
    simpa only [ProducedBlockRecursorShapeCandidate.candidate,
      normalizationCandidateBlockGenerationShape] using produced.shape
  cases hCandidates : produced.candidate.families with
  | cons firstCandidate remainingCandidates =>
    rw [hCandidates] at roots blockShape
    cases remainingCandidates with
    | cons secondCandidate remainingCandidates =>
      cases hRawTypes : source.types with
      | nil =>
        rw [hRawTypes] at roots
        nomatch roots
      | cons firstRaw rawTypes =>
        rw [hRawTypes] at roots blockShape
        cases hRawTypesTail : rawTypes with
        | nil =>
          rw [hRawTypesTail] at roots
          cases roots with
          | cons firstRoot remainingRoots => nomatch remainingRoots
        | cons secondRaw remainingRaws =>
          rw [hRawTypesTail] at roots blockShape
          have shapes :=
            CandidateBlockFamilySemanticGenerationShapeList.ofCheck roots
              blockShape
          cases roots with
          | cons firstRoot remainingRoots =>
            cases shapes with
            | cons firstShape remainingShapes =>
              cases remainingRoots with
              | cons secondRoot remainingRoots =>
                cases remainingShapes with
                | cons secondShape remainingShapes =>
                  obtain ⟨terminalRun, storedBinders, terminalVenv,
                      terminalLparams, telescope, storedLength,
                      terminalVlctx⟩ :=
                    secondRoot.type.annotationSpineContext
                      secondShape.storedSpine
                  have spineLength :=
                    secondShape.spineLength_eq_ctorFields
                  rw [spineLength] at telescope storedLength
                  exact ⟨{
                    firstCandidate := firstCandidate
                    secondCandidate := secondCandidate
                    remainingCandidates := remainingCandidates
                    candidates_eq := hCandidates
                    firstRaw := firstRaw
                    secondRaw := secondRaw
                    remainingRaws := remainingRaws
                    raws_eq := by rw [hRawTypes, hRawTypesTail]
                    spineLength_eq := spineLength
                    storedBinders := storedBinders
                    telescope := telescope
                    stored_length := storedLength
                    terminalRun := terminalRun
                    terminal_venv := terminalVenv
                    terminal_lparams := terminalLparams
                    terminal_vlctx := terminalVlctx }⟩

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.semanticSecondFamilyAnnotationSpine' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms
  ProducedBlockRecursorShapeCandidate.semanticSecondFamilyAnnotationSpine

/-- The first two family candidates are normalized in the same exact
producer-owned reader context.

The ordinary producer normalizes every family type in one snapshotted reader
context.  This theorem retains that operational identity at the exact two
candidates selected by `SecondFamilyAnnotationSpine`; no name equality is
supplied by a semantic caller. -/
theorem ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.candidate_context_eq
    {source : VInductDecl}
    {firstSource secondSource : InductiveType}
    {remainingSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: remainingSources) numNested isUnsafe
      context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    (annotation : produced.SecondFamilyAnnotationSpine semantic) :
    annotation.firstCandidate.familyType.type.context =
      annotation.secondCandidate.familyType.type.context := by
  let normalization :=
    produced.execution.eliminationExecution.normalization
  have candidatesEq := annotation.candidates_eq
  change normalization.families.candidates =
    .cons annotation.firstCandidate
      (.cons annotation.secondCandidate annotation.remainingCandidates) at candidatesEq
  have familyTypesProduced := normalization.familyTypes.produced
  rw [← normalization.families.produced.familyTypes_eq] at familyTypesProduced
  rw [candidatesEq] at familyTypesProduced
  simp only [AddInductive.CandidateList.familyTypes] at familyTypesProduced
  have firstContextEq :=
    AddInductive.CandidateFamilyType.context_eq_of_normalize
      familyTypesProduced.head
  have secondContextEq :=
    AddInductive.CandidateFamilyType.context_eq_of_normalize
      familyTypesProduced.tail.head
  exact firstContextEq.trans secondContextEq.symm

/-- The exact common reader context in particular fixes every main-spine free
variable allocated by the first two family candidates. -/
theorem ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.candidate_ngen_eq
    {source : VInductDecl}
    {firstSource secondSource : InductiveType}
    {remainingSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: remainingSources) numNested isUnsafe
      context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    (annotation : produced.SecondFamilyAnnotationSpine semantic) :
    annotation.firstCandidate.familyType.type.context.ngen =
      annotation.secondCandidate.familyType.type.context.ngen :=
  congrArg AddInductive.Context.ngen annotation.candidate_context_eq

/-- The exact first candidate selected by the joint annotation package owns
the complete shared-parameter prefix accepted by the ordinary validator. -/
theorem ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.first_nparams_le_spineLength
    {source : VInductDecl}
    {firstSource secondSource : InductiveType}
    {remainingSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: remainingSources) numNested isUnsafe
      context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    (annotation : produced.SecondFamilyAnnotationSpine semantic)
    (context_lctx_eq : context.lctx = {}) :
    source.nparams ≤
      annotation.firstCandidate.familyType.type.trace.spineLength := by
  let normalization :=
    produced.execution.eliminationExecution.normalization
  have normalizationProduced :=
    produced.execution.normalization_run produced.producedExecution
  have bound := normalization.firstFamilyType_nparams_le_spineLength
    normalizationProduced context_lctx_eq
  have candidateBound : source.nparams ≤
      normalization.families.candidates.head.familyType.type.trace.spineLength := by
    rw [normalization.families.produced.head_familyType]
    exact bound
  have candidatesEq := annotation.candidates_eq
  change normalization.families.candidates =
    .cons annotation.firstCandidate
      (.cons annotation.secondCandidate
        annotation.remainingCandidates) at candidatesEq
  rw [candidatesEq] at candidateBound
  exact candidateBound

/-- The exact second candidate selected by the joint annotation package also
owns the complete declared parameter prefix.  Unlike the first-family bound,
this is read from the detailed producer's source-indexed parameter-spine gate;
it is not inferred from a caller-selected semantic telescope. -/
theorem ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.second_nparams_le_spineLength
    {source : VInductDecl}
    {firstSource secondSource : InductiveType}
    {remainingSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: remainingSources) numNested isUnsafe
      context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    (annotation : produced.SecondFamilyAnnotationSpine semantic) :
    source.nparams ≤
      annotation.secondCandidate.familyType.type.trace.spineLength := by
  let normalization :=
    produced.execution.eliminationExecution.normalization
  have bounds := normalization.familyParameterSpines
  have candidatesEq := annotation.candidates_eq
  change normalization.families.candidates =
    .cons annotation.firstCandidate
      (.cons annotation.secondCandidate
        annotation.remainingCandidates) at candidatesEq
  rw [candidatesEq] at bounds
  cases bounds with
    | cons firstBound tail =>
      cases tail with
      | cons secondBound tail => exact secondBound

/-- The source-declared shared-parameter prefix fits in the exact second raw
family telescope selected by the joint annotation package. -/
theorem ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.nparams_le_rawSpineLength
    {source : VInductDecl}
    {firstSource secondSource : InductiveType}
    {remainingSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: remainingSources) numNested isUnsafe
      context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    (annotation : produced.SecondFamilyAnnotationSpine semantic) :
    source.nparams ≤
      (VInductDecl.ctorFields annotation.secondRaw.type).length := by
  rw [← annotation.spineLength_eq]
  exact annotation.second_nparams_le_spineLength

private theorem telN_take_of_le (expression : VExpr) {count total : Nat}
    (count_le : count ≤ total) :
    (VExpr.telN total expression).take count =
      VExpr.telN count expression := by
  induction count generalizing total expression with
  | zero => rfl
  | succ count ih =>
      cases total with
      | zero => omega
      | succ total =>
          cases expression <;> simp_all [VExpr.telN]

private theorem telDefEqEvidence_takeDirect
    (run : TypeChecker.TelDefEqEvidence env U Γ As As') (count : Nat) :
    TypeChecker.TelDefEqEvidence env U Γ
      (As.take count) (As'.take count) := by
  induction run generalizing count with
  | nil =>
      cases count <;> exact .nil
  | cons head tail ih =>
      cases count with
      | zero => exact .nil
      | succ count => exact .cons head (ih count)

private theorem telDefEqEvidence_length_eqDirect
    (run : TypeChecker.TelDefEqEvidence env U Γ As As') :
    As.length = As'.length := by
  induction run with
  | nil => rfl
  | cons head tail ih => exact congrArg Nat.succ ih

private theorem telDefEqEvidence_dropDirect
    (run : TypeChecker.TelDefEqEvidence env U Γ As As') (count : Nat) :
    TypeChecker.TelDefEqEvidence env U
      ((As.take count).reverse ++ Γ)
      (As.drop count) (As'.drop count) := by
  induction run generalizing count with
  | nil =>
      cases count <;> exact .nil
  | cons head tail ih =>
      cases count with
      | zero => exact .cons head tail
      | succ count =>
          simpa [List.reverse_cons, List.append_assoc] using ih count

/-- Dropping a prefix within a literal `forallN` telescope retains exactly
the corresponding binder-list suffix. -/
private theorem dropN_forallN_of_le (count : Nat) :
    ∀ (binders : List VExpr) (result : VExpr),
      count ≤ binders.length →
      VExpr.dropN count (VExpr.forallN binders result) =
        VExpr.forallN (binders.drop count) result := by
  induction count with
  | zero =>
      intro binders result bound
      rfl
  | succ count ih =>
      intro binders result bound
      cases binders with
      | nil => simp at bound
      | cons binder binders =>
          simp only [List.length_cons, Nat.succ_le_succ_iff] at bound
          simp only [VExpr.forallN, VExpr.dropN, List.drop]
          exact ih binders result bound

/-- Exact parameter-prefix equality retained from the second family's full
raw/annotation telescope.  Both endpoints are producer-selected; callers do
not choose a parallel semantic telescope. -/
theorem ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.parameterTelescope
    {source : VInductDecl}
    {firstSource secondSource : InductiveType}
    {remainingSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: remainingSources) numNested isUnsafe
      context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    (annotation : produced.SecondFamilyAnnotationSpine semantic) :
    TypeChecker.TelDefEqEvidence env Us.length []
      (VExpr.telN source.nparams annotation.secondRaw.type)
      (annotation.storedBinders.take source.nparams) := by
  have parameterPrefix :=
    telDefEqEvidence_takeDirect annotation.telescope source.nparams
  rw [telN_take_of_le annotation.secondRaw.type
    annotation.nparams_le_rawSpineLength] at parameterPrefix
  exact parameterPrefix

/-- The exact post-parameter suffix of the second-family annotation
telescope.  Its base context is the raw shared-parameter telescope, matching
the convention required by dependent spine specialization. -/
theorem ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.indexTelescope
    {source : VInductDecl}
    {firstSource secondSource : InductiveType}
    {remainingSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: remainingSources) numNested isUnsafe
      context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    (annotation : produced.SecondFamilyAnnotationSpine semantic) :
    TypeChecker.TelDefEqEvidence env Us.length
      (VExpr.telN source.nparams annotation.secondRaw.type).reverse
      ((VExpr.telN
        (VInductDecl.ctorFields annotation.secondRaw.type).length
        annotation.secondRaw.type).drop source.nparams)
      (annotation.storedBinders.drop source.nparams) := by
  have indexSuffix :=
    telDefEqEvidence_dropDirect annotation.telescope source.nparams
  rw [telN_take_of_le annotation.secondRaw.type
    annotation.nparams_le_rawSpineLength] at indexSuffix
  simpa using indexSuffix

/-- The raw shared-parameter telescope selected by the second candidate has
exactly the source-declared parameter count. -/
theorem ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.rawParameterTelescope_length
    {source : VInductDecl}
    {firstSource secondSource : InductiveType}
    {remainingSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: remainingSources) numNested isUnsafe
      context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    (annotation : produced.SecondFamilyAnnotationSpine semantic) :
    (VExpr.telN source.nparams annotation.secondRaw.type).length =
      source.nparams := by
  have fullLength :
      (VExpr.telN
        (VInductDecl.ctorFields annotation.secondRaw.type).length
        annotation.secondRaw.type).length =
      (VInductDecl.ctorFields annotation.secondRaw.type).length :=
    (telDefEqEvidence_length_eqDirect annotation.telescope).trans
      annotation.stored_length
  rw [← telN_take_of_le annotation.secondRaw.type
    annotation.nparams_le_rawSpineLength]
  rw [List.length_take_of_le]
  rw [fullLength]
  exact annotation.nparams_le_rawSpineLength

/-- Exact first raw/annotation-consumed index node after the declared shared
parameter prefix.  The suffix equations retain its position in the complete
producer telescope. -/
structure ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.RawFirstIndexDomain
    {source : VInductDecl}
    {firstSource secondSource : InductiveType}
    {remainingSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: remainingSources) numNested isUnsafe
      context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    (annotation : produced.SecondFamilyAnnotationSpine semantic) where
  rawDomain : VExpr
  consumedDomain : VExpr
  rawTail : List VExpr
  consumedTail : List VExpr
  sort : VLevel
  raw_suffix_eq :
    (VExpr.telN
      (VInductDecl.ctorFields annotation.secondRaw.type).length
      annotation.secondRaw.type).drop source.nparams =
      rawDomain :: rawTail
  consumed_suffix_eq :
    annotation.storedBinders.drop source.nparams =
      consumedDomain :: consumedTail
  annotation_evidence : TypeChecker.DefEqEvidence env Us.length
    (VExpr.telN source.nparams annotation.secondRaw.type).reverse
    rawDomain consumedDomain (.sort sort)

/-- A genuine post-parameter raw binder selects the exact first index-domain
equality from the producer-owned annotation suffix. -/
theorem ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.rawFirstIndexDomain
    {source : VInductDecl}
    {firstSource secondSource : InductiveType}
    {remainingSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: remainingSources) numNested isUnsafe
      context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    (annotation : produced.SecondFamilyAnnotationSpine semantic)
    (hasIndex : source.nparams <
      (VInductDecl.ctorFields annotation.secondRaw.type).length) :
    Nonempty annotation.RawFirstIndexDomain := by
  have fullLength :
      (VExpr.telN
        (VInductDecl.ctorFields annotation.secondRaw.type).length
        annotation.secondRaw.type).length =
      (VInductDecl.ctorFields annotation.secondRaw.type).length :=
    (telDefEqEvidence_length_eqDirect annotation.telescope).trans
      annotation.stored_length
  have rawSuffixNonempty :
      (VExpr.telN
        (VInductDecl.ctorFields annotation.secondRaw.type).length
        annotation.secondRaw.type).drop source.nparams ≠ [] := by
    intro empty
    have emptyLength := congrArg List.length empty
    simp only [List.length_drop, List.length_nil] at emptyLength
    rw [fullLength] at emptyLength
    omega
  have indexSuffix := annotation.indexTelescope
  generalize rawSuffixEq :
      (VExpr.telN
        (VInductDecl.ctorFields annotation.secondRaw.type).length
        annotation.secondRaw.type).drop source.nparams = rawSuffix
      at indexSuffix rawSuffixNonempty
  generalize consumedSuffixEq :
      annotation.storedBinders.drop source.nparams = consumedSuffix
      at indexSuffix
  cases indexSuffix with
  | nil => exact (rawSuffixNonempty rfl).elim
  | @cons rawContext rawDomain consumedDomain sort rawTail consumedTail head
      tail =>
      exact ⟨{
        rawDomain := rawDomain
        consumedDomain := consumedDomain
        rawTail := rawTail
        consumedTail := consumedTail
        sort := sort
        raw_suffix_eq := rawSuffixEq
        consumed_suffix_eq := consumedSuffixEq
        annotation_evidence := head }⟩

/-- The raw post-parameter expression is literally the retained first index
domain followed by the remainder of the producer telescope. -/
theorem ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.RawFirstIndexDomain.raw_drop_eq
    {source : VInductDecl}
    {firstSource secondSource : InductiveType}
    {remainingSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: remainingSources) numNested isUnsafe
      context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    {annotation : produced.SecondFamilyAnnotationSpine semantic}
    (raw : annotation.RawFirstIndexDomain) :
    VExpr.dropN source.nparams annotation.secondRaw.type =
      .forallE raw.rawDomain
        (VExpr.forallN raw.rawTail
          (VExpr.dropN
            (VInductDecl.ctorFields annotation.secondRaw.type).length
            annotation.secondRaw.type)) := by
  let fullBinders := VExpr.telN
    (VInductDecl.ctorFields annotation.secondRaw.type).length
    annotation.secondRaw.type
  have fullLength : fullBinders.length =
      (VInductDecl.ctorFields annotation.secondRaw.type).length :=
    (telDefEqEvidence_length_eqDirect annotation.telescope).trans
      annotation.stored_length
  have prefixBound : source.nparams ≤ fullBinders.length := by
    rw [fullLength]
    exact annotation.nparams_le_rawSpineLength
  calc
    VExpr.dropN source.nparams annotation.secondRaw.type =
        VExpr.dropN source.nparams
          (VExpr.forallN fullBinders
            (VExpr.dropN
              (VInductDecl.ctorFields annotation.secondRaw.type).length
              annotation.secondRaw.type)) := by
      rw [VExpr.forallN_telN_dropN]
    _ = VExpr.forallN (fullBinders.drop source.nparams)
          (VExpr.dropN
            (VInductDecl.ctorFields annotation.secondRaw.type).length
            annotation.secondRaw.type) :=
      dropN_forallN_of_le source.nparams fullBinders _ prefixBound
    _ = .forallE raw.rawDomain
          (VExpr.forallN raw.rawTail
            (VExpr.dropN
              (VInductDecl.ctorFields annotation.secondRaw.type).length
              annotation.secondRaw.type)) := by
      rw [raw.raw_suffix_eq]
      rfl

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.RawFirstIndexDomain.raw_drop_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.RawFirstIndexDomain.raw_drop_eq

/-- The first two producer-selected candidates allocate the same exact shared
parameter free variables.  Both lower bounds and the root name-generator
identity are producer-owned. -/
theorem ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.parameterLists_eq
    {source : VInductDecl}
    {firstSource secondSource : InductiveType}
    {remainingSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: remainingSources) numNested isUnsafe
      context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    (annotation : produced.SecondFamilyAnnotationSpine semantic)
    (context_lctx_eq : context.lctx = {}) :
    annotation.firstCandidate.familyType.type.trace.parameterList
        source.nparams =
      annotation.secondCandidate.familyType.type.trace.parameterList
        source.nparams :=
  AddInductive.CandidateExprTrace.parameterList_eq_of_ngen_eq
    annotation.firstCandidate.familyType.type.trace
    annotation.secondCandidate.familyType.type.trace
    annotation.candidate_ngen_eq
    (annotation.first_nparams_le_spineLength context_lctx_eq)
    annotation.second_nparams_le_spineLength

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.candidate_context_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.candidate_context_eq

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.candidate_ngen_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.candidate_ngen_eq

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.first_nparams_le_spineLength' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.first_nparams_le_spineLength

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.second_nparams_le_spineLength' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.second_nparams_le_spineLength

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.nparams_le_rawSpineLength' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.nparams_le_rawSpineLength

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.parameterTelescope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.parameterTelescope

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.indexTelescope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.indexTelescope

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.rawParameterTelescope_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.rawParameterTelescope_length

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.rawFirstIndexDomain' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.rawFirstIndexDomain


/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.parameterLists_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.parameterLists_eq

private theorem candidateContextRun_cast_context
    {left right : AddInductive.Context}
    (h : left = right)
    (run : TypeChecker.CandidateContextRun left) :
    (h ▸ run).context = run.context := by
  cases h
  rfl

private theorem candidateExprTrace_cast_context_spineLength
    {left right : AddInductive.Context} {source : Expr}
    (h : left = right)
    (trace : AddInductive.CandidateExprTrace left source) :
    (h ▸ trace).spineLength = trace.spineLength := by
  cases h
  rfl

private theorem candidateExprTrace_cast_context_terminalResult
    {left right : AddInductive.Context} {source : Expr}
    (h : left = right)
    (trace : AddInductive.CandidateExprTrace left source) :
    (h ▸ trace).terminalResult = trace.terminalResult := by
  cases h
  rfl

private theorem candidateExprTrace_cast_context_parameterList
    {left right : AddInductive.Context} {source : Expr}
    (h : left = right)
    (trace : AddInductive.CandidateExprTrace left source) (count : Nat) :
    (h ▸ trace).parameterList count = trace.parameterList count := by
  cases h
  rfl

private theorem candidateExprTrace_cast_context_validationAnnotations
    {left right : AddInductive.Context} {source : Expr}
    (h : left = right)
    {trace : AddInductive.CandidateExprTrace left source}
    (annotations : trace.validationAnnotations) :
    (h ▸ trace).validationAnnotations := by
  cases h
  exact annotations

/-- Interpret the first later family's complete shared-parameter comparison
inventory in the exact context reached by the first family.

The two-family source prefix fixes every position.  The first-family context
owner is transported only along the equality selected by the retained outer
trace.  The dependent semantic second root is then weakened into that exact
context, its retained validator WHNF supplies the inner root translation, and
the local-state traversal supplies the genuine shared-parameter declarations.
The result exposes the producer's grouped comparison list as an exact
`[] :: second :: remaining` decomposition; neither the second family nor its
comparison inventory is selected by a caller.  It also returns the exact
translated index-only suffix selected from that same second outer node. -/
theorem ProducedBlockRecursorShapeCandidate.semanticSecondFamilyParameterComparisons
    {source : VInductDecl}
    {firstSource secondSource : InductiveType}
    {remainingSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    (produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: remainingSources) numNested isUnsafe
      context)
    {env blockEnv : VEnv} {Us : List Name}
    (semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source)
    (annotation : produced.SecondFamilyAnnotationSpine semantic)
    (context_lctx_eq : context.lctx = {}) :
    ∃ secondComparisons remainingComparisons,
      (produced.execution.eliminationExecution.normalization
        |>.familyParameterComparisonTrace
          (produced.execution.normalization_run produced.producedExecution)
          produced.kernelSources_nonempty).comparisons =
        [] :: secondComparisons :: remainingComparisons ∧
      (∀ step ∈ secondComparisons,
        TypeChecker.FamilyComparisonSemanticRun step) ∧
      ∃ position,
        (produced.execution.eliminationExecution.normalization
          |>.familyParameterComparisonTrace
            (produced.execution.normalization_run produced.producedExecution)
            produced.kernelSources_nonempty).secondTelescope? =
          some position ∧
        position.stats.params.size = source.nparams ∧
        position.i = 0 ∧
        position.nindices = 0 ∧
        ∃ currentRun : TypeChecker.CandidateContextRun position.context,
          currentRun.context.venv = env ∧
          currentRun.context.lparams = Us ∧
          ∃ parameterRoot : VExpr,
            ∃ boundary : TypeChecker.FamilyParameterIndexBoundary
                position.trace currentRun,
              currentRun.context.TrExprS position.source parameterRoot ∧
              currentRun.context.venv.IsDefEqU
                currentRun.context.lparams.length
                currentRun.context.vlctx.toCtx annotation.secondRaw.type
                parameterRoot ∧
              TypeChecker.FamilyParameterSemanticSpine
                currentRun.context.venv currentRun.context.lparams.length
                currentRun.context.vlctx.toCtx parameterRoot
                (boundary.parameters.map Prod.snd) boundary.source' := by
  let normalization :=
    produced.execution.eliminationExecution.normalization
  have normalizationProduced :=
    produced.execution.normalization_run produced.producedExecution
  let comparisonTrace :=
    normalization.familyParameterComparisonTrace normalizationProduced
      produced.kernelSources_nonempty
  change ∃ secondComparisons remainingComparisons,
    comparisonTrace.comparisons =
      [] :: secondComparisons :: remainingComparisons ∧
    (∀ step ∈ secondComparisons,
      TypeChecker.FamilyComparisonSemanticRun step) ∧
    ∃ position,
      comparisonTrace.secondTelescope? = some position ∧
      position.stats.params.size = source.nparams ∧
      position.i = 0 ∧
      position.nindices = 0 ∧
      ∃ currentRun : TypeChecker.CandidateContextRun position.context,
        currentRun.context.venv = env ∧
        currentRun.context.lparams = Us ∧
        ∃ parameterRoot : VExpr,
          ∃ boundary : TypeChecker.FamilyParameterIndexBoundary
              position.trace currentRun,
            currentRun.context.TrExprS position.source parameterRoot ∧
            currentRun.context.venv.IsDefEqU
              currentRun.context.lparams.length
              currentRun.context.vlctx.toCtx annotation.secondRaw.type
              parameterRoot ∧
            TypeChecker.FamilyParameterSemanticSpine
              currentRun.context.venv currentRun.context.lparams.length
              currentRun.context.vlctx.toCtx parameterRoot
              (boundary.parameters.map Prod.snd) boundary.source'
  have roots := semantic.families
  cases hCandidates : produced.candidate.families with
  | cons firstCandidate remainingCandidates =>
    rw [hCandidates] at roots
    cases remainingCandidates with
    | cons secondCandidate remainingCandidates =>
      cases hRawTypes : source.types with
      | nil =>
        rw [hRawTypes] at roots
        nomatch roots
      | cons firstRaw rawTypes =>
        rw [hRawTypes] at roots
        cases roots with
        | cons firstSemantic remainingSemantics =>
          cases hRawTypesTail : rawTypes with
          | nil =>
            rw [hRawTypesTail] at remainingSemantics
            nomatch remainingSemantics
          | cons secondRaw remainingRawTypes =>
            rw [hRawTypesTail] at remainingSemantics
            cases remainingSemantics with
            | cons secondSemantic remainingSemantics =>
              have annotationRawsEq := annotation.raws_eq
              rw [hRawTypes, hRawTypesTail] at annotationRawsEq
              simp only [List.cons.injEq] at annotationRawsEq
              have secondRawEq : secondRaw = annotation.secondRaw :=
                annotationRawsEq.2.1
              generalize comparisonTrace_eq : comparisonTrace = trace at ⊢
              cases trace with
              | firstFamily dIdx stats validationContext inBounds closed
                  inferred root checkType rootWhnf telescope sorted ensureSort
                  isFirst tail =>
                obtain ⟨firstContextRun, firstVenv, firstLparams⟩ :=
                  produced.semanticFirstFamilyContextRun semantic
                    context_lctx_eq
                have firstContextEq : comparisonTrace.firstContext =
                    telescope.result.context :=
                  congrArg
                    AddInductive.FamilyParameterComparisonBlockTrace.firstContext
                    comparisonTrace_eq
                let currentRun : TypeChecker.CandidateContextRun
                    telescope.result.context := firstContextEq ▸ firstContextRun
                have currentContextEq : currentRun.context =
                    firstContextRun.context :=
                  candidateContextRun_cast_context firstContextEq
                    firstContextRun
                have currentVenv : currentRun.context.venv = env := by
                  rw [currentContextEq]
                  exact firstVenv
                have currentLparams : currentRun.context.lparams = Us := by
                  rw [currentContextEq]
                  exact firstLparams
                have secondTranslation := currentRun.rootTranslation
                  currentVenv currentLparams secondSemantic.type.source_tr
                have firstComparisons :=
                  telescope.comparisons_eq_nil_of_firstFamily (by rfl)
                obtain ⟨firstLocal, firstParamsSize⟩ :=
                  TypeChecker.familyTypeParameterComparison_localResult_of_first
                    telescope (by rfl) (by rfl)
                      (TypeChecker.FamilyParameterLocalState.empty
                        context (context.lparams.map .param) context_lctx_eq)
                let nextStats : AddInductive.InductiveStats := {
                  telescope.result.stats with
                  lctx := telescope.result.context.lctx
                  resultLevel := sorted.sortLevel!
                  isNotZero := sorted.sortLevel!.isNeverZero
                  nindices := telescope.result.stats.nindices.push
                    telescope.result.nindices
                  indConsts := telescope.result.stats.indConsts.push
                    (.const
                      (firstSource :: secondSource ::
                        remainingSources).toArray[0].name
                      telescope.result.stats.levels) }
                cases tail with
                | @laterFamily dIdx stats secondContext inBounds closed
                    inferred secondRoot checkType secondRootWhnf
                    secondTelescope sorted ensureSort isLater
                    resultLevelCompatible tail =>
                  have statsLater : nextStats.indConsts.isEmpty = false := by
                    rw [secondTelescope.result_indConsts_eq] at isLater
                    simpa only [nextStats] using isLater
                  have paramsSize :
                      nextStats.params.size = source.nparams := by
                    simpa using firstParamsSize
                  have secondLocal :
                      TypeChecker.FamilyParameterLocalState nextStats
                        telescope.result.context := by
                    exact ⟨firstLocal.localContext, firstLocal.parameters⟩
                  have normalizationCandidatesEq := hCandidates
                  change normalization.families.candidates =
                    AddInductive.CandidateList.cons firstCandidate
                      (AddInductive.CandidateList.cons secondCandidate
                        remainingCandidates) at normalizationCandidatesEq
                  have familyTypesProduced :=
                    normalization.familyTypes.produced
                  rw [← normalization.families.produced.familyTypes_eq] at familyTypesProduced
                  rw [normalizationCandidatesEq] at familyTypesProduced
                  simp only [AddInductive.CandidateList.familyTypes] at familyTypesProduced
                  have secondProduced := familyTypesProduced.tail.head
                  have secondContextEq :=
                    AddInductive.CandidateFamilyType.context_eq_of_normalize
                      secondProduced
                  have whnfDepth :
                      telescope.result.context.fuel.recDepth =
                        secondSemantic.type.whnfFuel + 1 := by
                    calc
                      telescope.result.context.fuel.recDepth =
                          context.fuel.recDepth :=
                        congrArg (fun fuel => fuel.recDepth)
                          telescope.result_context_fuel
                      _ = secondCandidate.familyType.type.context.fuel.recDepth :=
                        (congrArg (fun candidateContext =>
                          candidateContext.fuel.recDepth)
                            secondContextEq).symm
                      _ = secondSemantic.type.whnfFuel + 1 :=
                        secondSemantic.type.whnfDepth
                  have secondSourceTranslation : currentRun.context.TrExprS
                      (firstSource :: secondSource ::
                        remainingSources).toArray[0 + 1].type
                      secondRaw.type := by
                    simpa using secondTranslation
                  obtain ⟨secondRoot', secondRootTranslation,
                      ⟨secondRootRun⟩⟩ :=
                    TypeChecker.WhnfRun.exists_ofCandidateStep
                      ⟨telescope.result.context,
                        (firstSource :: secondSource ::
                          remainingSources).toArray[0 + 1].type,
                        secondRoot⟩
                      secondRootWhnf currentRun secondRaw.type
                      secondSourceTranslation secondSemantic.type.whnfFuel
                      whnfDepth
                  obtain ⟨secondRuns, secondBoundary, parameterSpine⟩ :=
                    TypeChecker.familyTypeParameterComparison_semanticSpine_of_later
                      secondTelescope statsLater paramsSize secondLocal
                      currentRun secondRoot' secondRootTranslation
                      secondSemantic.type.whnfFuel whnfDepth
                  have rawRootDef := secondRootRun.isDefEqU
                  rw [secondRawEq] at rawRootDef
                  let secondPosition :
                      AddInductive.FamilyParameterComparisonBlockTrace.FamilyTelescopePosition
                        source.nparams := {
                    stats := nextStats
                    context := telescope.result.context
                    source := secondRoot
                    i := 0
                    nindices := 0
                    fuel := telescope.result.context.fuel.inductiveFuel
                    trace := secondTelescope }
                  refine ⟨secondTelescope.comparisons, tail.comparisons, ?_,
                    secondRuns, secondPosition, (by rfl), paramsSize,
                    (by rfl), (by rfl),
                    currentRun, currentVenv, currentLparams,
                    secondRoot', secondBoundary,
                    secondRootTranslation, rawRootDef, parameterSpine⟩
                  · simp only [
                      AddInductive.FamilyParameterComparisonBlockTrace.comparisons,
                      firstComparisons]
                | @firstFamily dIdx stats secondContext inBounds closed
                    inferred secondRoot checkType secondRootWhnf
                    secondTelescope sorted ensureSort isFirst tail =>
                  have notFirst :
                      secondTelescope.result.stats.indConsts.isEmpty = false := by
                    rw [secondTelescope.result_indConsts_eq]
                    simp
                  rw [notFirst] at isFirst
                  contradiction
                | @terminal dIdx stats secondContext outOfBounds =>
                  simp at outOfBounds
              | laterFamily dIdx stats validationContext inBounds closed
                  inferred root checkType rootWhnf telescope sorted ensureSort
                  isLater resultLevelCompatible tail =>
                have first :
                    telescope.result.stats.indConsts.isEmpty = true := by
                  rw [telescope.result_indConsts_eq]
                  rfl
                rw [first] at isLater
                contradiction
              | terminal dIdx stats validationContext outOfBounds =>
                simp at outOfBounds

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.semanticSecondFamilyParameterComparisons' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms
  ProducedBlockRecursorShapeCandidate.semanticSecondFamilyParameterComparisons

/-- Joint producer-owned staging for the exact second-family candidate
telescope and the validator suffix reached after its shared parameters.

Both components are selected from the same dependent candidate hierarchy and
outer family-validation trace.  Downstream index alignment therefore cannot
mix an annotation telescope with an independently chosen validator position. -/
structure ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging
    {source : VInductDecl}
    {firstSource secondSource : InductiveType}
    {remainingSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    (produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: remainingSources) numNested isUnsafe
      context)
    {env blockEnv : VEnv} {Us : List Name}
    (semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source) where
  annotation : produced.SecondFamilyAnnotationSpine semantic
  secondComparisons : List AddInductive.CandidateIsDefEqStep
  remainingComparisons : List (List AddInductive.CandidateIsDefEqStep)
  comparisons_eq :
    (produced.execution.eliminationExecution.normalization
      |>.familyParameterComparisonTrace
        (produced.execution.normalization_run produced.producedExecution)
        produced.kernelSources_nonempty).comparisons =
      [] :: secondComparisons :: remainingComparisons
  comparisonRuns : ∀ step ∈ secondComparisons,
    TypeChecker.FamilyComparisonSemanticRun step
  position :
    AddInductive.FamilyParameterComparisonBlockTrace.FamilyTelescopePosition
      source.nparams
  position_eq :
    (produced.execution.eliminationExecution.normalization
      |>.familyParameterComparisonTrace
        (produced.execution.normalization_run produced.producedExecution)
        produced.kernelSources_nonempty).secondTelescope? = some position
  position_params_size : position.stats.params.size = source.nparams
  position_i_eq : position.i = 0
  position_nindices_eq : position.nindices = 0
  currentRun : TypeChecker.CandidateContextRun position.context
  current_venv : currentRun.context.venv = env
  current_lparams : currentRun.context.lparams = Us
  parameterRoot : VExpr
  parameterRoot_tr : currentRun.context.TrExprS position.source parameterRoot
  rawRoot_def : currentRun.context.venv.IsDefEqU
    currentRun.context.lparams.length currentRun.context.vlctx.toCtx
    annotation.secondRaw.type parameterRoot
  boundary : TypeChecker.FamilyParameterIndexBoundary position.trace
    currentRun
  parameterSpine : TypeChecker.FamilyParameterSemanticSpine
    currentRun.context.venv currentRun.context.lparams.length
    currentRun.context.vlctx.toCtx parameterRoot
    (boundary.parameters.map Prod.snd) boundary.source'

/-- Select the joint second-family annotation/validator staging directly from
the retained producer and semantic hierarchy. -/
theorem ProducedBlockRecursorShapeCandidate.semanticSecondFamilyIndexStaging
    {source : VInductDecl}
    {firstSource secondSource : InductiveType}
    {remainingSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    (produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: remainingSources) numNested isUnsafe
      context)
    {env blockEnv : VEnv} {Us : List Name}
    (semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source)
    (context_lctx_eq : context.lctx = {}) :
    Nonempty (produced.SecondFamilyIndexStaging semantic) := by
  obtain ⟨annotation⟩ :=
    produced.semanticSecondFamilyAnnotationSpine semantic
  obtain ⟨secondComparisons, remainingComparisons, comparisonsEq,
      comparisonRuns, position, positionEq, positionParamsSize, positionIEq,
      positionNindicesEq, currentRun, currentVenv, currentLparams,
      parameterRoot, boundary,
      parameterRootTr, rawRootDef, parameterSpine⟩ :=
    produced.semanticSecondFamilyParameterComparisons semantic annotation
      context_lctx_eq
  exact ⟨{
    annotation := annotation
    secondComparisons := secondComparisons
    remainingComparisons := remainingComparisons
    comparisons_eq := comparisonsEq
    comparisonRuns := comparisonRuns
    position := position
    position_eq := positionEq
    position_params_size := positionParamsSize
    position_i_eq := positionIEq
    position_nindices_eq := positionNindicesEq
    currentRun := currentRun
    current_venv := currentVenv
    current_lparams := currentLparams
    parameterRoot := parameterRoot
    parameterRoot_tr := parameterRootTr
    rawRoot_def := rawRootDef
    boundary := boundary
    parameterSpine := parameterSpine }⟩

/-- The boundary's strict kernel/Theory parameter inventory covers the exact
declared shared-parameter prefix from initial position zero. -/
theorem ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.parameterPairs_length
    {source : VInductDecl}
    {firstSource secondSource : InductiveType}
    {remainingSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: remainingSources) numNested isUnsafe
      context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    (staging : produced.SecondFamilyIndexStaging semantic) :
    staging.boundary.parameters.length = source.nparams := by
  rw [staging.boundary.parameters_length, staging.position_i_eq,
    Nat.sub_zero]

/-- The kernel half of the retained parameter inventory is exactly the
validator position's producer-owned parameter array. -/
theorem ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.parameterSources_eq_positionParams
    {source : VInductDecl}
    {firstSource secondSource : InductiveType}
    {remainingSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: remainingSources) numNested isUnsafe
      context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    (staging : produced.SecondFamilyIndexStaging semantic) :
    staging.boundary.parameters.map Prod.fst =
      staging.position.stats.params.toList := by
  rw [staging.boundary.parameter_sources_eq, staging.position_i_eq,
    List.drop_zero]

/-- Saturating the exact second raw family with the boundary's retained
Theory parameter values reaches the validator's producer-owned index cursor
up to definitional equality. -/
theorem ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.rawParameterSuffix_def
    {source : VInductDecl}
    {firstSource secondSource : InductiveType}
    {remainingSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: remainingSources) numNested isUnsafe
      context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    (staging : produced.SecondFamilyIndexStaging semantic) :
    staging.currentRun.context.venv.IsDefEqU
      staging.currentRun.context.lparams.length
      staging.currentRun.context.vlctx.toCtx
      (VExpr.instRev
        (VExpr.dropN source.nparams staging.annotation.secondRaw.type)
        (staging.boundary.parameters.map Prod.snd))
      staging.boundary.source' := by
  refine staging.parameterSpine.rawTerminal_defeq
    (rawBinders :=
      VExpr.telN source.nparams staging.annotation.secondRaw.type)
    (rawTerminal :=
      VExpr.dropN source.nparams staging.annotation.secondRaw.type)
    staging.currentRun.context.Ewf staging.currentRun.context.Δwf.toCtx
    ?_ ?_
  · simpa only [VExpr.forallN_telN_dropN] using staging.rawRoot_def
  · simpa only [List.length_map, staging.parameterPairs_length] using
      staging.annotation.rawParameterTelescope_length.symm

/-- Specialize the producer's first raw/annotation index-domain equality by
the exact Theory values retained at the validator parameter boundary. -/
theorem ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.specializeRawFirstIndexAnnotation
    {source : VInductDecl}
    {firstSource secondSource : InductiveType}
    {remainingSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: remainingSources) numNested isUnsafe
      context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    (staging : produced.SecondFamilyIndexStaging semantic)
    (raw : staging.annotation.RawFirstIndexDomain) :
    staging.currentRun.context.venv.IsDefEq
      staging.currentRun.context.lparams.length
      staging.currentRun.context.vlctx.toCtx
      (VExpr.instRev raw.rawDomain
        (staging.boundary.parameters.map Prod.snd))
      (VExpr.instRev raw.consumedDomain
        (staging.boundary.parameters.map Prod.snd))
      (.sort raw.sort) := by
  let rawBinders :=
    VExpr.telN source.nparams staging.annotation.secondRaw.type
  let arguments := staging.boundary.parameters.map Prod.snd
  have henv : VEnv.WF env := by
    simpa only [staging.current_venv] using staging.currentRun.context.Ewf
  have hΓ : OnCtx staging.currentRun.context.vlctx.toCtx
      (env.IsType Us.length) := by
    simpa only [staging.current_venv, staging.current_lparams] using
      staging.currentRun.context.Δwf.toCtx
  have rootDef : env.IsDefEqU Us.length
      staging.currentRun.context.vlctx.toCtx
      (VExpr.forallN rawBinders
        (VExpr.dropN source.nparams staging.annotation.secondRaw.type))
      staging.parameterRoot := by
    simpa only [staging.current_venv, staging.current_lparams,
      rawBinders, VExpr.forallN_telN_dropN] using staging.rawRoot_def
  have parameterSpine : TypeChecker.FamilyParameterSemanticSpine
      env Us.length staging.currentRun.context.vlctx.toCtx
      staging.parameterRoot arguments staging.boundary.source' := by
    simpa only [staging.current_venv, staging.current_lparams, arguments] using
      staging.parameterSpine
  have argumentsLength : arguments.length = rawBinders.length := by
    simpa only [arguments, rawBinders, List.length_map,
      staging.parameterPairs_length] using
      staging.annotation.rawParameterTelescope_length.symm
  have rawOnTel := staging.annotation.parameterTelescope.telDefEq.raw_onTel
  have rawContext : OnCtx rawBinders.reverse (env.IsType Us.length) := by
    simpa only [rawBinders, List.append_nil] using
      rawOnTel.onCtx (show OnCtx ([] : List VExpr)
        (env.IsType Us.length) from trivial)
  have rawClosed := VEnv.CtxWF.closed henv.ordered rawContext
  have annotationDef : env.IsDefEq Us.length
      (rawBinders.reverse ++ staging.currentRun.context.vlctx.toCtx)
      raw.rawDomain raw.consumedDomain (.sort raw.sort) := by
    simpa only [rawBinders] using
      raw.annotation_evidence.isDefEq.weakR henv.ordered rawClosed
        staging.currentRun.context.vlctx.toCtx
  have specialized := parameterSpine.specializeTerminalDefEq henv hΓ
    rootDef argumentsLength annotationDef
  rw [VExpr.instRev_closedN arguments (C := .sort raw.sort) trivial]
    at specialized
  simpa only [staging.current_venv, staging.current_lparams, arguments] using
    specialized

/-- Joint first-index alignment between the raw candidate telescope and the
exact source-indexed validator Pi. -/
structure ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.RawFirstIndexSpecialization
    {source : VInductDecl}
    {firstSource secondSource : InductiveType}
    {remainingSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: remainingSources) numNested isUnsafe
      context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    (staging : produced.SecondFamilyIndexStaging semantic)
    (raw : staging.annotation.RawFirstIndexDomain) where
  translation : staging.boundary.IndexDomainTranslation
  raw_domain_def : staging.currentRun.context.venv.IsDefEqU
    staging.currentRun.context.lparams.length
    staging.currentRun.context.vlctx.toCtx
    (VExpr.instRev raw.rawDomain
      (staging.boundary.parameters.map Prod.snd))
    translation.domain'
  annotation_def : staging.currentRun.context.venv.IsDefEq
    staging.currentRun.context.lparams.length
    staging.currentRun.context.vlctx.toCtx
    (VExpr.instRev raw.rawDomain
      (staging.boundary.parameters.map Prod.snd))
    (VExpr.instRev raw.consumedDomain
      (staging.boundary.parameters.map Prod.snd))
    (.sort raw.sort)

/-- A nonterminal validator boundary and the matching raw first-index node
construct the exact joint specialization package. -/
theorem ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.rawFirstIndexSpecialization
    {source : VInductDecl}
    {firstSource secondSource : InductiveType}
    {remainingSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: remainingSources) numNested isUnsafe
      context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    (staging : produced.SecondFamilyIndexStaging semantic)
    (raw : staging.annotation.RawFirstIndexDomain)
    (isForall : staging.boundary.source.isForall = true) :
    Nonempty (staging.RawFirstIndexSpecialization raw) := by
  obtain ⟨translation⟩ :=
    staging.boundary.indexDomainTranslation_of_forall isForall
  have wholeDef := staging.rawParameterSuffix_def
  rw [raw.raw_drop_eq, VExpr.instRev_forallE_projection,
    translation.source'_eq] at wholeDef
  have rawDomainDef :=
    (VEnv.IsDefEqU.forallE_inv staging.currentRun.context.Ewf
      staging.currentRun.context.Δwf.toCtx wholeDef).1
  exact ⟨{
    translation := translation
    raw_domain_def := ⟨_, rawDomainDef.choose_spec⟩
    annotation_def := staging.specializeRawFirstIndexAnnotation raw }⟩

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.parameterPairs_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.parameterPairs_length

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.parameterSources_eq_positionParams' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.parameterSources_eq_positionParams

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.rawParameterSuffix_def' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.rawParameterSuffix_def

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.specializeRawFirstIndexAnnotation' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.specializeRawFirstIndexAnnotation

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.rawFirstIndexSpecialization' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.rawFirstIndexSpecialization

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.semanticSecondFamilyIndexStaging' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms
  ProducedBlockRecursorShapeCandidate.semanticSecondFamilyIndexStaging

/-- The shared-parameter array at the exact second-family validator position
is the first candidate's producer-allocated main-spine prefix.

This is stronger than the retained size invariant: it identifies every free
variable in source order.  The proof replays the first family's exact inner
trace against the exact first candidate selected by the annotation package;
the second outer position is then definitionally the statistics update that
preserves that array. -/
theorem ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.position_params_eq_firstParameterList
    {source : VInductDecl}
    {firstSource secondSource : InductiveType}
    {remainingSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: remainingSources) numNested isUnsafe
      context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    (staging : produced.SecondFamilyIndexStaging semantic)
    (context_lctx_eq : context.lctx = {}) :
    staging.position.stats.params.toList =
      staging.annotation.firstCandidate.familyType.type.trace.parameterList
        source.nparams := by
  let normalization :=
    produced.execution.eliminationExecution.normalization
  have normalizationProduced :=
    produced.execution.normalization_run produced.producedExecution
  have firstBound :=
    staging.annotation.first_nparams_le_spineLength context_lctx_eq
  have familyTypeFuel :=
    normalization.firstFamilyType_spineLength_lt_inductiveFuel
      normalizationProduced context_lctx_eq
  have firstFuel :
      staging.annotation.firstCandidate.familyType.type.trace.spineLength <
        context.fuel.inductiveFuel := by
    have candidateFuel :
        normalization.families.candidates.head.familyType.type.trace.spineLength <
          context.fuel.inductiveFuel := by
      rw [normalization.families.produced.head_familyType]
      exact familyTypeFuel
    have candidatesEq := staging.annotation.candidates_eq
    change normalization.families.candidates =
      .cons staging.annotation.firstCandidate
        (.cons staging.annotation.secondCandidate
          staging.annotation.remainingCandidates) at candidatesEq
    rw [candidatesEq] at candidateFuel
    exact candidateFuel
  have familyTypesProduced := normalization.familyTypes.produced
  rw [← normalization.families.produced.familyTypes_eq] at familyTypesProduced
  have candidatesEq := staging.annotation.candidates_eq
  change normalization.families.candidates =
    .cons staging.annotation.firstCandidate
      (.cons staging.annotation.secondCandidate
        staging.annotation.remainingCandidates) at candidatesEq
  rw [candidatesEq] at familyTypesProduced
  simp only [AddInductive.CandidateList.familyTypes] at familyTypesProduced
  have firstProduced := familyTypesProduced.head
  have candidateContextEq : { context with lctx := {} } = context := by
    cases context
    simp_all
  rw [candidateContextEq] at firstProduced
  have annotations :=
    staging.annotation.firstCandidate.familyType
      |>.validationAnnotations_of_normalize firstProduced
  have firstContextEq :=
    staging.annotation.firstCandidate.familyType
      |>.context_eq_of_normalize firstProduced
  let firstTrace : AddInductive.CandidateExprTrace context firstSource.type :=
    firstContextEq ▸
      staging.annotation.firstCandidate.familyType.type.trace
  have firstTraceSpine := candidateExprTrace_cast_context_spineLength
    firstContextEq staging.annotation.firstCandidate.familyType.type.trace
  have firstTraceBound : source.nparams ≤ firstTrace.spineLength := by
    rw [firstTraceSpine]
    exact firstBound
  have firstTraceFuel : firstTrace.spineLength <
      context.fuel.inductiveFuel := by
    rw [firstTraceSpine]
    exact firstFuel
  have firstTraceAnnotations : firstTrace.validationAnnotations := by
    simpa only [firstTrace] using
      (candidateExprTrace_cast_context_validationAnnotations
        firstContextEq annotations)
  have terminals := normalization.familyTerminals
  rw [← normalization.families.produced.familyTypes_eq] at terminals
  rw [candidatesEq] at terminals
  simp only [AddInductive.CandidateList.familyTypes] at terminals
  cases terminals with
  | cons firstTerminal remainingTerminals =>
    have firstTraceTerminal :=
      candidateExprTrace_cast_context_terminalResult firstContextEq
        staging.annotation.firstCandidate.familyType.type.trace
    have terminalForall :
        firstTrace.terminalResult.isForall = false := by
      rw [firstTraceTerminal, firstTerminal]
      rfl
    let comparisonTrace :=
      normalization.familyParameterComparisonTrace normalizationProduced
        produced.kernelSources_nonempty
    have positionEq := staging.position_eq
    change comparisonTrace.secondTelescope? = some staging.position at positionEq
    generalize comparisonTrace_eq : comparisonTrace = trace at positionEq
    cases trace with
    | firstFamily dIdx stats validationContext inBounds closed inferred root
        checkType rootWhnf telescope sorted ensureSort isFirst tail =>
      have candidateWhnf :=
        firstTrace.rootWhnf_valid
      have candidateWhnf' : AddInductive.CandidateWhnfStep.Valid
          ⟨context,
            firstSource.type,
            firstTrace.rootWhnf⟩ := candidateWhnf
      have rootWhnf' : AddInductive.CandidateWhnfStep.Valid
          ⟨context, firstSource.type, root⟩ := by
        simpa using rootWhnf
      have root_eq : root =
          firstTrace.rootWhnf :=
        Except.ok.inj (rootWhnf'.symm.trans candidateWhnf')
      subst root
      have resultEq :=
        AddInductive.FamilyTypeParameterComparisonTrace.result_eq_candidate
          (nparams := source.nparams) (i := 0) (nindices := 0)
          (fuel := context.fuel.inductiveFuel)
          (stats := AddInductive.InductiveStats.initial
            (context.lparams.map .param))
          (context := context)
          (candidate := firstTrace)
          (trace := telescope) (remaining := source.nparams)
          (hi := by simp) (hcount := firstTraceBound)
          (hfuel := firstTraceFuel) (hempty := rfl)
          (hannotations := firstTraceAnnotations)
          (hterminal := terminalForall)
      have paramsEq := congrArg
        (fun result : AddInductive.FamilyTypeParameterComparisonTrace.Result =>
          result.stats.params.toList) resultEq
      have paramsEq' : telescope.result.stats.params.toList =
          staging.annotation.firstCandidate.familyType.type.trace.parameterList
            source.nparams := by
        calc
          telescope.result.stats.params.toList =
              firstTrace.parameterList source.nparams := by
            simpa [AddInductive.InductiveStats.initial] using paramsEq
          _ = staging.annotation.firstCandidate.familyType.type.trace.parameterList
                source.nparams := by
            exact candidateExprTrace_cast_context_parameterList
              firstContextEq
              staging.annotation.firstCandidate.familyType.type.trace
              source.nparams
      cases tail with
      | firstFamily dIdx stats secondContext inBounds closed inferred
          secondRoot checkType secondRootWhnf secondTelescope secondSorted
          secondEnsureSort secondIsFirst secondTail =>
        simp only [AddInductive.FamilyParameterComparisonBlockTrace.secondTelescope?,
          AddInductive.FamilyParameterComparisonBlockTrace.headTelescope?]
            at positionEq
        have positionParamsEq :
            telescope.result.stats.params.toList =
              staging.position.stats.params.toList := by
          simpa using congrArg
            (fun position :
              AddInductive.FamilyParameterComparisonBlockTrace.FamilyTelescopePosition
                source.nparams => position.stats.params.toList)
            (Option.some.inj positionEq)
        exact positionParamsEq.symm.trans paramsEq'
      | laterFamily dIdx stats secondContext inBounds closed inferred
          secondRoot checkType secondRootWhnf secondTelescope secondSorted
          secondEnsureSort secondIsLater resultLevelCompatible secondTail =>
        simp only [AddInductive.FamilyParameterComparisonBlockTrace.secondTelescope?,
          AddInductive.FamilyParameterComparisonBlockTrace.headTelescope?]
            at positionEq
        have positionParamsEq :
            telescope.result.stats.params.toList =
              staging.position.stats.params.toList := by
          simpa using congrArg
            (fun position :
              AddInductive.FamilyParameterComparisonBlockTrace.FamilyTelescopePosition
                source.nparams => position.stats.params.toList)
            (Option.some.inj positionEq)
        exact positionParamsEq.symm.trans paramsEq'
      | terminal dIdx stats secondContext outOfBounds =>
        simp only [AddInductive.FamilyParameterComparisonBlockTrace.secondTelescope?,
          AddInductive.FamilyParameterComparisonBlockTrace.headTelescope?]
            at positionEq
        simp at positionEq
    | laterFamily dIdx stats validationContext inBounds closed inferred root
        checkType rootWhnf telescope sorted ensureSort isLater
        resultLevelCompatible tail =>
      have first : telescope.result.stats.indConsts.isEmpty = true := by
        rw [telescope.result_indConsts_eq]
        rfl
      rw [first] at isLater
      contradiction
    | terminal dIdx stats validationContext outOfBounds =>
      simp at outOfBounds

/-- Consequently, the producer-selected first candidate contributes exactly
`nparams` shared parameters to the second-family validator position. -/
theorem ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.firstParameterList_length
    {source : VInductDecl}
    {firstSource secondSource : InductiveType}
    {remainingSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: remainingSources) numNested isUnsafe
      context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    (staging : produced.SecondFamilyIndexStaging semantic)
    (context_lctx_eq : context.lctx = {}) :
    (staging.annotation.firstCandidate.familyType.type.trace.parameterList
      source.nparams).length = source.nparams := by
  calc
    (staging.annotation.firstCandidate.familyType.type.trace.parameterList
        source.nparams).length =
        staging.position.stats.params.toList.length :=
      congrArg List.length
        (staging.position_params_eq_firstParameterList context_lctx_eq).symm
    _ = staging.position.stats.params.size := by simp
    _ = source.nparams := staging.position_params_size

/-- The validator's exact shared-parameter array is also the second candidate's
producer-allocated main-spine prefix.  This is the joint alignment needed to
instantiate the annotation telescope at the computed index boundary. -/
theorem ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.position_params_eq_secondParameterList
    {source : VInductDecl}
    {firstSource secondSource : InductiveType}
    {remainingSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: remainingSources) numNested isUnsafe
      context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    (staging : produced.SecondFamilyIndexStaging semantic)
    (context_lctx_eq : context.lctx = {}) :
    staging.position.stats.params.toList =
      staging.annotation.secondCandidate.familyType.type.trace.parameterList
        source.nparams := by
  calc
    staging.position.stats.params.toList =
        staging.annotation.firstCandidate.familyType.type.trace.parameterList
          source.nparams :=
      staging.position_params_eq_firstParameterList context_lctx_eq
    _ = staging.annotation.secondCandidate.familyType.type.trace.parameterList
          source.nparams :=
      staging.annotation.parameterLists_eq context_lctx_eq

/-- The retained kernel inventory is the exact main-spine prefix of the
producer-selected second candidate. -/
theorem ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.parameterSources_eq_secondParameterList
    {source : VInductDecl}
    {firstSource secondSource : InductiveType}
    {remainingSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: remainingSources) numNested isUnsafe
      context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    (staging : produced.SecondFamilyIndexStaging semantic)
    (context_lctx_eq : context.lctx = {}) :
    staging.boundary.parameters.map Prod.fst =
      staging.annotation.secondCandidate.familyType.type.trace.parameterList
        source.nparams :=
  staging.parameterSources_eq_positionParams.trans
    (staging.position_params_eq_secondParameterList context_lctx_eq)

/-- Consequently, the exact second candidate parameter list also has the
validator-selected declared length. -/
theorem ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.secondParameterList_length
    {source : VInductDecl}
    {firstSource secondSource : InductiveType}
    {remainingSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: remainingSources) numNested isUnsafe
      context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    (staging : produced.SecondFamilyIndexStaging semantic)
    (context_lctx_eq : context.lctx = {}) :
    (staging.annotation.secondCandidate.familyType.type.trace.parameterList
      source.nparams).length = source.nparams := by
  calc
    (staging.annotation.secondCandidate.familyType.type.trace.parameterList
        source.nparams).length =
        staging.position.stats.params.toList.length :=
      congrArg List.length
        (staging.position_params_eq_secondParameterList context_lctx_eq).symm
    _ = staging.position.stats.params.size := by simp
    _ = source.nparams := staging.position_params_size

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.position_params_eq_secondParameterList' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.position_params_eq_secondParameterList

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.parameterSources_eq_secondParameterList' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.parameterSources_eq_secondParameterList

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.secondParameterList_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.secondParameterList_length

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.position_params_eq_firstParameterList' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.position_params_eq_firstParameterList

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.firstParameterList_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.firstParameterList_length

/-- The retained first-family validation and its exact semantic root determine
the Theory representation of the block's common result universe.  The value
is not selected by a caller: `VLevel.ofLevel` translates the precise kernel
level stored in the producer's final family statistics. -/
theorem ProducedBlockRecursorShapeCandidate.semanticCommonResultLevel
    {source : VInductDecl} {kernelSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    (produced : ProducedBlockRecursorShapeCandidate source kernelSources
      numNested isUnsafe context)
    {env blockEnv : VEnv} {Us : List Name}
    (semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source)
    (context_lctx_eq : context.lctx = {}) :
    ∃ resultLevel,
      VLevel.ofLevel Us
        produced.execution.eliminationExecution.normalization.stats.resultLevel =
          some resultLevel := by
  have normalizationProduced := produced.execution.normalization_run
    produced.producedExecution
  obtain ⟨kernelSource, remainingSources, sources_eq⟩ :=
    list_eq_cons_of_isEmpty_false kernelSources
      produced.kernelSources_nonempty
  subst kernelSources
  have terminals := produced.execution.eliminationExecution.normalization
    |>.familyTerminalSorts
  obtain ⟨kernelLevel, resultLevel, terminal, level_tr⟩ :=
    semantic.families.headResultLevel terminals
  have common_eq := produced.execution.eliminationExecution.normalization
    |>.firstFamily_resultLevel_eq normalizationProduced
      context_lctx_eq kernelLevel terminal
  rw [common_eq]
  exact ⟨resultLevel, level_tr⟩

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.semanticCommonResultLevel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ProducedBlockRecursorShapeCandidate.semanticCommonResultLevel

/-- Analyze the exact semantic family spine selected by the retained ordinary
producer and, on success, construct its complete checked block.  In
particular, callers do not select a dependent `CheckedFamilies` witness: the
Theory analyzer computes that witness from the producer's normalized view.

The remaining `Option` boundary is intentional.  Kernel validation compares
later-family parameter domains by definitional equality, whereas
`CheckedFamily.params_eq` requires syntactic equality with the first
normalized parameter telescope.  A later producer theorem must either prove
that exact equality or construct a semantically equivalent canonical view;
this function does not silently strengthen the kernel check. -/
def ProducedBlockRecursorShapeCandidate.semanticCheckedBlock?
    {source : VInductDecl} {kernelSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    (produced : ProducedBlockRecursorShapeCandidate source kernelSources
      numNested isUnsafe context)
    {env blockEnv : VEnv} {Us : List Name}
    (semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source)
    (validationMapWF : produced.execution.eliminationExecution.normalization
      |>.validationContext.env.constants.WF)
    (context_lctx_eq : context.lctx = {}) :
    Option semantic.normalization.view.CheckedBlock :=
  let view := semantic.normalization.view
  let params := blockParams view.nparams view.types
  match VInductDecl.checkedFamilies? view params 0 view.types with
  | none => none
  | some families => some {
      params
      params_eq := rfl
      params_length :=
        produced.semanticViewParams_length semantic context_lctx_eq
      families
      nonempty := semantic.viewTypes_isEmpty_eq_sources.trans
        produced.kernelSources_nonempty
      names := blockGeneratedNames view.types
      names_eq := rfl
      names_nodup :=
        produced.semanticViewGeneratedNames_nodup semantic validationMapWF }

/-- Compute the analyzer block and the validator-owned common result universe
as one semantic validation value.  Both data fields are fixed by the retained
ordinary execution: family analysis runs on its exact normalized view and the
level is the strict Theory translation of its stored kernel statistic. -/
def ProducedBlockRecursorShapeCandidate.semanticValidatedBlock?
    {source : VInductDecl} {kernelSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    (produced : ProducedBlockRecursorShapeCandidate source kernelSources
      numNested isUnsafe context)
    {env blockEnv : VEnv} {Us : List Name}
    (semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source)
    (validationMapWF : produced.execution.eliminationExecution.normalization
      |>.validationContext.env.constants.WF)
    (context_lctx_eq : context.lctx = {}) :
    Option (ValidatedBlock source) := do
  let checked ← produced.semanticCheckedBlock? semantic validationMapWF
    context_lctx_eq
  let resultLevel ← VLevel.ofLevel Us
    produced.execution.eliminationExecution.normalization.stats.resultLevel
  return {
    block := semantic.normalizedCheckedBlock checked
    resultLevel }

/-- Run the retained ordinary producer through recursor synthesis/declaration
and the unchanged complete generation-shape gate. -/
def produceBlockRecursorShapeCandidate
    (source : VInductDecl) (kernelSources : List InductiveType)
    (numNested : Nat) (isUnsafe : Bool)
    (context : AddInductive.Context)
    (kernelSources_nonempty : kernelSources.isEmpty = false) :
    Except Exception (ProducedBlockRecursorShapeCandidate source kernelSources
      numNested isUnsafe context) :=
  match producedExecution :
      AddInductive.NormalizationRecursorExecution.buildExecution source.nparams
        kernelSources numNested isUnsafe context with
  | .error error => .error error
  | .ok execution =>
      if shape : normalizationCandidateBlockGenerationShape source
          execution.candidate then
        .ok { execution, producedExecution, shape, kernelSources_nonempty }
      else
        .error (.other
          "recursor candidate block does not preserve the generation spine")

private theorem produceBlockRecursorShapeCandidate_match_ok
    {source : VInductDecl} {kernelSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    (result : Except Exception
      (AddInductive.NormalizationRecursorExecution source.nparams
        kernelSources numNested isUnsafe context))
    (toProducedExecution : ∀ actual, result = .ok actual →
      AddInductive.NormalizationRecursorExecution.buildExecution source.nparams
          kernelSources numNested isUnsafe context = .ok actual)
    {execution : AddInductive.NormalizationRecursorExecution source.nparams
      kernelSources numNested isUnsafe context}
    (result_ok : result = .ok execution)
    (shape : normalizationCandidateBlockGenerationShape source
      execution.candidate = true)
    (kernelSources_nonempty : kernelSources.isEmpty = false) :
    (match result_eq : result with
    | .error error => Except.error error
    | .ok actual =>
      if actualShape : normalizationCandidateBlockGenerationShape source
          actual.candidate then
        Except.ok (show ProducedBlockRecursorShapeCandidate source
            kernelSources numNested isUnsafe context from {
          execution := actual
          producedExecution := toProducedExecution actual result_eq
          shape := actualShape
          kernelSources_nonempty })
      else
        Except.error (.other
          "recursor candidate block does not preserve the generation spine")) =
      Except.ok (show ProducedBlockRecursorShapeCandidate source kernelSources
          numNested isUnsafe context from {
        execution
        producedExecution := toProducedExecution execution result_ok
        shape
        kernelSources_nonempty }) := by
  subst result
  simp [shape]

theorem produceBlockRecursorShapeCandidate_eq_ok
    {source : VInductDecl} {kernelSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {execution : AddInductive.NormalizationRecursorExecution source.nparams
      kernelSources numNested isUnsafe context}
    (producedExecution :
      AddInductive.NormalizationRecursorExecution.buildExecution source.nparams
          kernelSources numNested isUnsafe context = .ok execution)
    (shape : normalizationCandidateBlockGenerationShape source
      execution.candidate = true)
    (kernelSources_nonempty : kernelSources.isEmpty = false) :
    produceBlockRecursorShapeCandidate source kernelSources numNested isUnsafe
        context kernelSources_nonempty =
      .ok { execution, producedExecution, shape, kernelSources_nonempty } := by
  unfold produceBlockRecursorShapeCandidate
  exact produceBlockRecursorShapeCandidate_match_ok
    (result := AddInductive.NormalizationRecursorExecution.buildExecution
      source.nparams kernelSources numNested isUnsafe context)
    (toProducedExecution := fun _ result_eq => result_eq)
    producedExecution shape kernelSources_nonempty

/-- Reindex an already-retained ordinary recursor execution onto the exact
Theory source whose generation shape it satisfies.  The only transport is
the source parameter-count equality; the execution and its producer equation
remain the caller's original dependent values. -/
def ProducedBlockRecursorShapeCandidate.ofExecution
    {source : VInductDecl} {nparams : Nat}
    {kernelSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    (execution : AddInductive.NormalizationRecursorExecution nparams
      kernelSources numNested isUnsafe context)
    (producedExecution :
      AddInductive.NormalizationRecursorExecution.buildExecution nparams
        kernelSources numNested isUnsafe context = .ok execution)
    (kernelSources_nonempty : kernelSources.isEmpty = false)
    (nparams_eq : source.nparams = nparams)
    (shape : normalizationCandidateBlockGenerationShape source
      execution.candidate = true) :
    ProducedBlockRecursorShapeCandidate source kernelSources numNested
      isUnsafe context := by
  cases source with
  | mk uvars sourceNparams types =>
      simp only at nparams_eq ⊢
      subst nparams
      exact { execution, producedExecution, shape, kernelSources_nonempty }

/-- Exact semantic generation plus the post-constructor decisions that drove
the same ordinary kernel execution. -/
structure ExactProducedBlockEliminationRun
    {source : VInductDecl} {kernelSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    (env blockEnv : VEnv) (Us : List Name)
    (produced : ProducedBlockEliminationShapeCandidate source kernelSources
      numNested isUnsafe context)
    (generation : BlockGenerationChecked source) where
  block : ExactProducedBlockGenerationRun env blockEnv Us produced.base
    generation
  elimination : AddInductive.CheckerBlockEliminationRun generation
    produced.execution
  isUnsafe_eq : isUnsafe = false
  validation_lparams_eq :
    produced.execution.normalization.validationContext.lparams = Us

def ExactProducedBlockEliminationRun.blockGenerationRun
    {source : VInductDecl} {kernelSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {env blockEnv : VEnv} {Us : List Name}
    {produced : ProducedBlockEliminationShapeCandidate source kernelSources
      numNested isUnsafe context}
    {generation : BlockGenerationChecked source}
    (run : ExactProducedBlockEliminationRun env blockEnv Us produced
      generation) : BlockGenerationRun generation env blockEnv :=
  run.block.blockGenerationRun

def ExactProducedBlockEliminationRun.certificate
    {source : VInductDecl} {kernelSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {env blockEnv : VEnv} {Us : List Name}
    {produced : ProducedBlockEliminationShapeCandidate source kernelSources
      numNested isUnsafe context}
    {generation : BlockGenerationChecked source}
    (run : ExactProducedBlockEliminationRun env blockEnv Us produced
      generation) : BlockGenerationCertificate source env :=
  run.block.certificate

/-- Exact semantic generation indexed by the same ordinary execution that
continues through recursor synthesis and declaration. -/
structure ExactProducedBlockRecursorRun
    {source : VInductDecl} {kernelSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    (env blockEnv : VEnv) (Us : List Name)
    (produced : ProducedBlockRecursorShapeCandidate source kernelSources
      numNested isUnsafe context)
    (generation : BlockGenerationChecked source) where
  elimination : ExactProducedBlockEliminationRun env blockEnv Us
    produced.eliminationBase generation

def ExactProducedBlockRecursorRun.blockGenerationRun
    {source : VInductDecl} {kernelSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {env blockEnv : VEnv} {Us : List Name}
    {produced : ProducedBlockRecursorShapeCandidate source kernelSources
      numNested isUnsafe context}
    {generation : BlockGenerationChecked source}
    (run : ExactProducedBlockRecursorRun env blockEnv Us produced generation) :
    BlockGenerationRun generation env blockEnv :=
  run.elimination.blockGenerationRun

def ExactProducedBlockRecursorRun.certificate
    {source : VInductDecl} {kernelSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {env blockEnv : VEnv} {Us : List Name}
    {produced : ProducedBlockRecursorShapeCandidate source kernelSources
      numNested isUnsafe context}
    {generation : BlockGenerationChecked source}
    (run : ExactProducedBlockRecursorRun env blockEnv Us produced generation) :
    BlockGenerationCertificate source env :=
  run.elimination.certificate

/-- The final kernel environment retained here is the result of the real
ordinary inductive-add call. -/
theorem ProducedBlockRecursorShapeCandidate.addInductiveRun
    (produced : ProducedBlockRecursorShapeCandidate source kernelSources
      numNested isUnsafe context) :
    AddInductive.run source.nparams kernelSources numNested context =
      .ok produced.execution.recursors.env :=
  produced.execution.addInductiveRun produced.producedExecution

/-- Translate the exact constructor metadata list installed by the retained
ordinary declaration trace to the complete raw Theory constructor inventory. -/
theorem ExactProducedBlockEliminationRun.constructorDeclarationEvidence
    {source : VInductDecl} {kernelSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {env blockEnv : VEnv} {Us : List Name}
    {produced : ProducedBlockEliminationShapeCandidate source kernelSources
      numNested isUnsafe context}
    {generation : BlockGenerationChecked source}
    (run : ExactProducedBlockEliminationRun env blockEnv Us produced
      generation) :
    List.Forall₂
      (fun info raw => TrConstVal .safe blockEnv (.ctorInfo info) raw)
      produced.execution.declaredConstructorInfos
      source.blockConstructorConstants := by
  have evidence :=
    run.block.producedSemantic.semantic.families
      |>.constructorDeclarationEvidence
        produced.execution.normalization.stats isUnsafe
        produced.execution.constructorContext run.isUnsafe_eq (by
          simpa only [AddInductive.NormalizationEliminationExecution.constructorContext]
            using run.validation_lparams_eq)
  simpa only [AddInductive.NormalizationEliminationExecution.declaredConstructorInfos,
    AddInductive.declaredConstructorInfos_toArray,
    VInductDecl.blockConstructorConstants] using evidence

/-- Interpret the constructor phase retained by the stronger ordinary
execution.  The caller supplies only the already-derived post-family
environment translation; the exact metadata list, kernel checks, Theory
constructor fold, and final translated environment all come from `run`. -/
noncomputable def ExactProducedBlockEliminationRun.constructorDeclarationStaging
    {source : VInductDecl} {kernelSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {env blockEnv : VEnv} {Us : List Name}
    {produced : ProducedBlockEliminationShapeCandidate source kernelSources
      numNested isUnsafe context}
    {generation : BlockGenerationChecked source}
    (run : ExactProducedBlockEliminationRun env blockEnv Us produced
      generation)
    {Q : Bool}
    (pre : TrEnv' .safe
      produced.execution.normalization.familyEnv.constants Q blockEnv) :
    ConstructorDeclarationStagingRun
      produced.execution.constructorContext.allowPrimitive
      produced.execution.normalization.familyEnv
      produced.execution.constructorEnv
      produced.execution.declaredConstructorInfos
      blockEnv source.blockConstructorConstants Q := by
  apply _root_.Lean4Lean.VInductDecl.constructorDeclarationStaging
    (evidence := run.constructorDeclarationEvidence)
    (rawsWF := run.blockGenerationRun.constructorConstantsWF)
    (pre := pre)
  simpa only [AddInductive.declareConstructors,
    AddInductive.NormalizationEliminationExecution.constructorContext,
    AddInductive.NormalizationEliminationExecution.declaredConstructorInfos]
    using produced.execution.declareConstructorsRun

/-- The complete family-and-constructor declaration prefix selected by one
exact normalization/elimination execution.  Both kernel traces and both
Theory insertion folds share their phase boundary by construction. -/
structure ExactProducedBlockDeclarationRun
    {source : VInductDecl} {kernelSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {env blockEnv : VEnv} {Us : List Name}
    {produced : ProducedBlockEliminationShapeCandidate source kernelSources
      numNested isUnsafe context}
    {generation : BlockGenerationChecked source}
    (run : ExactProducedBlockEliminationRun env blockEnv Us produced
      generation) where
  families : FamilyDeclarationStagingRun
    produced.execution.normalization.validationContext.allowPrimitive
    produced.execution.normalization.validationContext.env
    produced.execution.normalization.familyEnv
    produced.execution.normalization.declaredInfos
    env blockEnv source.blockTypeConstants
    produced.execution.normalization.validationContext.env.quotInit
  constructors : ConstructorDeclarationStagingRun
    produced.execution.constructorContext.allowPrimitive
    produced.execution.normalization.familyEnv
    produced.execution.constructorEnv
    produced.execution.declaredConstructorInfos
    blockEnv source.blockConstructorConstants
    produced.execution.normalization.validationContext.env.quotInit

/-- Assemble the exact declaration prefix from a staging input indexed by the
normalization execution embedded in `run`. -/
noncomputable def ExactProducedBlockEliminationRun.declarationRun
    {source : VInductDecl} {kernelSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {env blockEnv : VEnv} {Us : List Name}
    {produced : ProducedBlockEliminationShapeCandidate source kernelSources
      numNested isUnsafe context}
    {generation : BlockGenerationChecked source}
    (run : ExactProducedBlockEliminationRun env blockEnv Us produced
      generation)
    (staging : NormalizationCandidateBlockStagingInput context
      produced.execution.normalization env blockEnv Us source) :
    ExactProducedBlockDeclarationRun run :=
  let families := staging.familyDeclaration
  let constructors := run.constructorDeclarationStaging families.trenv
  { families, constructors }

/-- The exact family, constructor, and generated-recursor declaration prefix
owned by one ordinary recursor execution.  Only the semantic alignment of the
newly synthesized recursor records remains an input. -/
structure ExactProducedBlockMetadataPrefixRun
    {source : VInductDecl} {kernelSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {env blockEnv : VEnv} {Us : List Name}
    {produced : ProducedBlockRecursorShapeCandidate source kernelSources
      numNested isUnsafe context}
    {generation : BlockGenerationChecked source}
    (run : ExactProducedBlockRecursorRun env blockEnv Us produced generation) where
  declarations : ExactProducedBlockDeclarationRun run.elimination
  recursors : RecursorDeclarationStagingRun
    produced.execution.recursors.allowPrimitive
    produced.execution.recursors.initialEnv
    produced.execution.recursors.env
    produced.execution.recursors.infos
    declarations.constructors.ctorEnv generation.recursors
    generation.kTarget
    produced.execution.eliminationExecution.normalization.validationContext.env.quotInit

/-- Extend the exact raw declaration prefix through the actual generated
recursor inventory.  The operational trace is fixed by `produced`; callers
provide its translation and typing against the constructed post-constructor
Theory environment. -/
noncomputable def ExactProducedBlockRecursorRun.metadataPrefix
    {source : VInductDecl} {kernelSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {env blockEnv : VEnv} {Us : List Name}
    {produced : ProducedBlockRecursorShapeCandidate source kernelSources
      numNested isUnsafe context}
    {generation : BlockGenerationChecked source}
    (run : ExactProducedBlockRecursorRun env blockEnv Us produced generation)
    (staging : NormalizationCandidateBlockStagingInput context
      produced.execution.eliminationExecution.normalization env blockEnv Us
        source)
    (evidence : List.Forall₂
      (fun info raw => TrConstVal .safe
        (run.elimination.declarationRun staging).constructors.ctorEnv
        (.recInfo info) raw)
      produced.execution.recursors.infos generation.recursors)
    (rawsWF : ∀ raw ∈ generation.recursors,
      raw.toVConstant.WF
        (run.elimination.declarationRun staging).constructors.ctorEnv) :
    ExactProducedBlockMetadataPrefixRun run := by
  let declarations := run.elimination.declarationRun staging
  have pre : TrEnv' .safe
      produced.execution.recursors.initialEnv.constants
      produced.execution.eliminationExecution.normalization.validationContext.env.quotInit
      declarations.constructors.ctorEnv := by
    rw [produced.execution.recursor_initialEnv_eq]
    exact declarations.constructors.trenv
  let recursors := recursorDeclarationStaging
    (kTarget := generation.kTarget)
    produced.execution.recursors.trace.run evidence (by
      intro info member
      rw [run.elimination.elimination.kTarget_eq]
      exact AddInductive.declareRecursors_infos_kTarget
        produced.execution.recursorsRun member) rawsWF pre
  exact { declarations, recursors }

/-- Complete the exact family/constructor/recursor prefix with the generated
Theory rule fold.  All implementation metadata maps and intermediate Theory
environments are fixed by the retained producer and its staging interpreter;
the rule fold is now the sole remaining transaction input. -/
def ExactProducedBlockMetadataPrefixRun.addInductBlockTrace
    {source : VInductDecl} {kernelSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {env blockEnv : VEnv} {Us : List Name}
    {produced : ProducedBlockRecursorShapeCandidate source kernelSources
      numNested isUnsafe context}
    {generation : BlockGenerationChecked source}
    {run : ExactProducedBlockRecursorRun env blockEnv Us produced generation}
    (metadata : ExactProducedBlockMetadataPrefixRun run)
    {env₂ : VEnv}
    (addRules : AddDefEqs metadata.recursors.recEnv
      generation.generatedRules env₂) :
    AddInductBlockTrace
      produced.execution.eliminationExecution.normalization.validationContext.env.constants
      env source produced.execution.recursors.env.constants env₂ where
  generation := generation
  blockEnv := blockEnv
  generation_wf := run.blockGenerationRun.wf
  typeMap := produced.execution.eliminationExecution.normalization.familyEnv.constants
  typeEnv := blockEnv
  ctorMap := produced.execution.eliminationExecution.constructorEnv.constants
  ctorEnv := metadata.declarations.constructors.ctorEnv
  recEnv := metadata.recursors.recEnv
  addTypes := metadata.declarations.families.addTypes
  addCtors := metadata.declarations.constructors.addCtors
  addRecs := by
    rw [← produced.execution.recursor_initialEnv_eq]
    exact metadata.recursors.addRecs
  recK := metadata.recursors.recK
  addRules := addRules

/-- Pair an exact flattened producer transaction with the matching restored
nested transaction.  The dependent indices force the ordinary producer's
raw block and generation descriptor to be exactly the nested analyzer's
flattened block and generation; no fixture-selected equality is accepted at
this boundary. -/
def ExactProducedBlockMetadataPrefixRun.nestedStagedCertificate
    {nestedSource : VInductDecl}
    {env blockEnv flatAfter after : VEnv} {Us : List Name}
    {kernelSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    (restored : nestedSource.NestedBlockCertificate env after)
    {produced : ProducedBlockRecursorShapeCandidate
      restored.nested.elim.flat kernelSources numNested isUnsafe context}
    {run : ExactProducedBlockRecursorRun env blockEnv Us produced
      restored.nested.generation}
    (metadata : ExactProducedBlockMetadataPrefixRun run)
    (addRules : AddDefEqs metadata.recursors.recEnv
      restored.nested.generation.generatedRules flatAfter) :
    nestedSource.NestedStagedCertificate env flatAfter after where
  restored := restored
  flatBlockEnv := blockEnv
  flatWF := run.blockGenerationRun.wf
  flatSuccess :=
    (metadata.addInductBlockTrace addRules).to_addInductBlockGeneration

/-- Attach the stronger exact producer to a matching concrete metadata
transaction. -/
def ExactProducedBlockEliminationRun.addInductBlockTrace
    {source : VInductDecl} {kernelSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {env blockEnv : VEnv} {Us : List Name}
    {produced : ProducedBlockEliminationShapeCandidate source kernelSources
      numNested isUnsafe context}
    {generation : BlockGenerationChecked source}
    (run : ExactProducedBlockEliminationRun env blockEnv Us produced
      generation)
    {m₁ m₂ : ConstMap} {env₂ : VEnv}
    (typeMap : ConstMap) (typeEnv : VEnv)
    (ctorMap : ConstMap) (ctorEnv recEnv : VEnv)
    (addTypes : AddInductConstants .induct m₁ env
      source.blockTypeConstants typeMap typeEnv)
    (addCtors : AddInductConstants .ctor typeMap typeEnv
      source.blockConstructorConstants ctorMap ctorEnv)
    (addRecs : AddInductConstants .recursor ctorMap ctorEnv
      generation.recursors m₂ recEnv)
    (recK : RecursorMapKMatches m₂ generation.recursors
      generation.kTarget)
    (addRules : AddDefEqs recEnv generation.generatedRules env₂) :
    AddInductBlockTrace m₁ env source m₂ env₂ :=
  run.block.addInductBlockTrace typeMap typeEnv ctorMap ctorEnv recEnv
    addTypes addCtors addRecs recK addRules

end VInductDecl
end Lean4Lean
