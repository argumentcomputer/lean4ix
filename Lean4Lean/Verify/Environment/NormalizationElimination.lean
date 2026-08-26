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
