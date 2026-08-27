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
  firstSemantic : CandidateBlockFamilySemanticRun env blockEnv Us
    firstCandidate firstRaw
  secondSemantic : CandidateBlockFamilySemanticRun env blockEnv Us
    secondCandidate secondRaw
  remainingSemantics : CandidateBlockFamilySemanticListRun env blockEnv Us
    remainingCandidates remainingRaws
  semantic_families : CandidateBlockFamilySemanticListRun.TwoHead env
    blockEnv Us semantic.families firstSemantic secondSemantic
      remainingSemantics
  firstShape : CandidateBlockFamilySemanticGenerationShape source env
    blockEnv Us firstSemantic
  secondShape : CandidateBlockFamilySemanticGenerationShape source env
    blockEnv Us secondSemantic
  remainingShapes : CandidateBlockFamilySemanticGenerationShapeList source
    env blockEnv Us remainingSemantics
  remainingValidationAnnotations :
    CandidateFamilyValidationAnnotationList { context with lctx := {} }
      remainingCandidates
  remainingParameterSpines :
    AddInductive.CandidateFamilyParameterSpineList source.nparams
      remainingCandidates
  firstSpineLength_eq :
    firstCandidate.familyType.type.trace.spineLength =
      (VInductDecl.ctorFields firstRaw.type).length
  firstStoredBinders : List VExpr
  firstTelescope : TypeChecker.TelDefEqEvidence env Us.length []
    (VExpr.telN (VInductDecl.ctorFields firstRaw.type).length firstRaw.type)
    firstStoredBinders
  firstStoredLength : firstStoredBinders.length =
    (VInductDecl.ctorFields firstRaw.type).length
  firstTerminalRun : TypeChecker.CandidateContextRun
    firstCandidate.familyType.type.trace.terminalContext
  first_stored_spine :
    firstCandidate.familyType.type.trace.storedSpine = true
  first_validation_annotations :
    firstCandidate.familyType.type.trace.validationAnnotations
  first_annotation_spine : TypeChecker.CandidateAnnotationSpine env Us
    firstCandidate.familyType.type.trace [] firstTerminalRun.context.vlctx
      firstStoredBinders
  first_terminal_venv : firstTerminalRun.context.venv = env
  first_terminal_lparams : firstTerminalRun.context.lparams = Us
  first_terminal_vlctx :
    firstTerminalRun.context.vlctx.toCtx = firstStoredBinders.reverse
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
  secondView : VExpr
  secondInferred : VExpr
  secondRun : TypeChecker.CandidateExprRun env Us
    secondCandidate.familyType.type.trace [] secondRaw.type
    secondView secondInferred
  stored_spine :
    secondCandidate.familyType.type.trace.storedSpine = true
  whnfFuel : Nat
  whnfDepth : secondCandidate.familyType.type.context.fuel.recDepth =
    whnfFuel + 1
  validation_annotations :
    secondCandidate.familyType.type.trace.validationAnnotations
  annotation_spine : TypeChecker.CandidateAnnotationSpine env Us
    secondCandidate.familyType.type.trace [] terminalRun.context.vlctx
      storedBinders
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
  have blockShape : candidateBlockFamilySemanticGenerationShape source
      produced.candidate.families source.types = true := by
    simpa only [ProducedBlockRecursorShapeCandidate.candidate,
      normalizationCandidateBlockGenerationShape] using produced.shape
  let firstCandidate := produced.candidate.families.head
  let secondCandidate := produced.candidate.families.tail.head
  let remainingCandidates := produced.candidate.families.tail.tail
  let firstPosition := semantic.families.headPosition
  let secondPosition := firstPosition.tail.headPosition
  have shapes := CandidateBlockFamilySemanticGenerationShapeList.ofCheck
    semantic.families blockShape
  let firstShape := shapes.head
  let secondShape := shapes.tail.head
  let remainingShapes := shapes.tail.tail
  let normalization :=
    produced.execution.eliminationExecution.normalization
  have candidatesEq : normalization.families.candidates =
      .cons firstCandidate (.cons secondCandidate remainingCandidates) := by
    change produced.candidate.families =
      .cons firstCandidate (.cons secondCandidate remainingCandidates)
    calc
      produced.candidate.families =
          .cons produced.candidate.families.head
            produced.candidate.families.tail :=
        AddInductive.CandidateList.cons_eta _
      _ = .cons firstCandidate
          (.cons secondCandidate remainingCandidates) := by
        rw [AddInductive.CandidateList.cons_eta
          produced.candidate.families.tail]
  have familyTypesProduced := normalization.familyTypes.produced
  rw [← normalization.families.produced.familyTypes_eq]
    at familyTypesProduced
  rw [candidatesEq] at familyTypesProduced
  simp only [AddInductive.CandidateList.familyTypes] at familyTypesProduced
  have secondProduced := familyTypesProduced.tail.head
  have secondAnnotations :=
    secondCandidate.familyType.validationAnnotations_of_normalize
      secondProduced
  have firstProduced := familyTypesProduced.head
  have firstAnnotations :=
    firstCandidate.familyType.validationAnnotations_of_normalize
      firstProduced
  have parameterSpines := normalization.familyParameterSpines
  rw [candidatesEq] at parameterSpines
  have familyTerminals := normalization.familyTerminals
  rw [← normalization.families.produced.familyTypes_eq]
    at familyTerminals
  rw [candidatesEq] at familyTerminals
  simp only [AddInductive.CandidateList.familyTypes] at familyTerminals
  obtain ⟨firstTerminalRun, firstStoredBinders,
      firstTerminalVenv, firstTerminalLparams,
      firstTelescope, firstStoredLength,
      firstTerminalVlctx, firstAnnotationSpine⟩ :=
    firstPosition.semantic.type.annotationSpineContext firstShape.storedSpine
  obtain ⟨secondInferred, secondRun⟩ :=
    secondPosition.semantic.type.recursive
  obtain ⟨terminalRun, storedBinders, terminalVenv,
      terminalLparams, telescope, storedLength,
      terminalVlctx, annotationSpine⟩ :=
    secondPosition.semantic.type.annotationSpineContext
      secondShape.storedSpine
  have spineLength := secondShape.spineLength_eq_ctorFields
  have firstSpineLength := firstShape.spineLength_eq_ctorFields
  rw [firstSpineLength] at firstTelescope firstStoredLength
  rw [spineLength] at telescope storedLength
  exact ⟨{
    firstCandidate := firstCandidate
    secondCandidate := secondCandidate
    remainingCandidates := remainingCandidates
    candidates_eq := by
      change produced.candidate.families = _
      exact candidatesEq
    firstRaw := firstPosition.raw
    secondRaw := secondPosition.raw
    remainingRaws := secondPosition.remainingRaws
    raws_eq := by
      calc
        source.types =
            firstPosition.raw :: firstPosition.remainingRaws :=
          firstPosition.raws_eq
        _ = firstPosition.raw :: secondPosition.raw ::
              secondPosition.remainingRaws :=
          congrArg (List.cons firstPosition.raw) secondPosition.raws_eq
    firstSemantic := firstPosition.semantic
    secondSemantic := secondPosition.semantic
    remainingSemantics := secondPosition.tail
    semantic_families := semantic.families.twoHeadPositions
    firstShape := firstShape
    secondShape := secondShape
    remainingShapes := remainingShapes
    remainingValidationAnnotations :=
      CandidateFamilyValidationAnnotationList.ofProduced
        remainingCandidates familyTypesProduced.tail.tail
        familyTerminals.tail.tail
    remainingParameterSpines := parameterSpines.tail.tail
    firstSpineLength_eq := firstSpineLength
    firstStoredBinders := firstStoredBinders
    firstTelescope := firstTelescope
    firstStoredLength := firstStoredLength
    firstTerminalRun := firstTerminalRun
    first_stored_spine := firstShape.storedSpine
    first_validation_annotations := firstAnnotations
    first_annotation_spine := firstAnnotationSpine
    first_terminal_venv := firstTerminalVenv
    first_terminal_lparams := firstTerminalLparams
    first_terminal_vlctx := firstTerminalVlctx
    spineLength_eq := spineLength
    storedBinders := storedBinders
    telescope := telescope
    stored_length := storedLength
    terminalRun := terminalRun
    secondView := secondPosition.semantic.type.view
    secondInferred := secondInferred
    secondRun := secondRun
    stored_spine := secondShape.storedSpine
    whnfFuel := secondPosition.semantic.type.whnfFuel
    whnfDepth := secondPosition.semantic.type.whnfDepth
    validation_annotations := secondAnnotations
    annotation_spine := annotationSpine
    terminal_venv := terminalVenv
    terminal_lparams := terminalLparams
    terminal_vlctx := terminalVlctx }⟩

/-- Erase the lightweight semantic-family decomposition certificate to the
exact normalized views selected in source order. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.semantic_views_eq
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
    semantic.families.views = annotation.firstSemantic.view ::
      annotation.secondSemantic.view :: annotation.remainingSemantics.views := by
  exact annotation.semantic_families.views_eq

/-- Forget the positional duplication in the two-family staging package and
recover the generic annotation owner for its exact second semantic family. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.familyAnnotationSpine
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
    Nonempty (CandidateBlockFamilyAnnotationSpine source env blockEnv Us
      annotation.secondSemantic annotation.secondShape) :=
  CandidateBlockFamilyAnnotationSpine.exists annotation.secondSemantic
    annotation.secondShape annotation.validation_annotations

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.familyAnnotationSpine' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.familyAnnotationSpine

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

/-- The exact second candidate was normalized in the producer's snapshotted
root reader context. -/
theorem ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.second_candidate_context_eq
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
    annotation.secondCandidate.familyType.type.context =
      { context with lctx := {} } := by
  let normalization :=
    produced.execution.eliminationExecution.normalization
  have candidatesEq := annotation.candidates_eq
  change normalization.families.candidates =
    .cons annotation.firstCandidate
      (.cons annotation.secondCandidate annotation.remainingCandidates)
    at candidatesEq
  have familyTypesProduced := normalization.familyTypes.produced
  rw [← normalization.families.produced.familyTypes_eq]
    at familyTypesProduced
  rw [candidatesEq] at familyTypesProduced
  simp only [AddInductive.CandidateList.familyTypes] at familyTypesProduced
  exact AddInductive.CandidateFamilyType.context_eq_of_normalize
    familyTypesProduced.tail.head

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

/-- The producer's exact first-index raw node selects the corresponding
annotation position on the same second-family candidate run. -/
theorem ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.RawFirstIndexDomain.annotationAt
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
    Nonempty
      (annotation.secondCandidate.familyType.type.trace.AnnotationAt
        source.nparams) := by
  let fullBinders := VExpr.telN
    (VInductDecl.ctorFields annotation.secondRaw.type).length
    annotation.secondRaw.type
  have fullLength : fullBinders.length =
      (VInductDecl.ctorFields annotation.secondRaw.type).length :=
    annotation.telescope.length_eq.trans annotation.stored_length
  have suffixLength : fullBinders.length - source.nparams =
      raw.rawTail.length + 1 := by
    simpa only [fullBinders, List.length_drop, List.length_cons] using
      congrArg List.length raw.raw_suffix_eq
  have count_lt : source.nparams <
      annotation.secondCandidate.familyType.type.trace.spineLength := by
    rw [annotation.spineLength_eq, ← fullLength]
    change source.nparams < fullBinders.length
    omega
  exact annotation.secondCandidate.familyType.type.trace.annotationAt
    annotation.validation_annotations count_lt

/-- Interpret the selected first-index annotation position through the exact
recursive semantic run retained by the second-family producer. -/
theorem ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.RawFirstIndexDomain.annotationSnapshot
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
    ∃ position : annotation.secondCandidate.familyType.type.trace.AnnotationAt
        source.nparams,
      ∃ snapshot : TypeChecker.CandidateAnnotationSnapshot env Us position.root,
        snapshot.consumed' = raw.consumedDomain ∧
          snapshot.Δ.toCtx =
            (annotation.storedBinders.take source.nparams).reverse ∧
          snapshot.Δ.fvars.map Expr.fvar =
            (annotation.secondCandidate.familyType.type.trace.parameterList
              source.nparams).reverse ∧
          VLCtx.FVLift' snapshot.Δ annotation.terminalRun.context.vlctx 0
            (.skipN .refl
              (annotation.storedBinders.drop source.nparams).length) 0 ∧
          snapshot.Δ.FVarLamOnly := by
  obtain ⟨position⟩ := raw.annotationAt
  obtain ⟨snapshot, tail, snapshotSuffixEq, snapshotContext,
      snapshotFVars, terminalLift, snapshotShape⟩ :=
    annotation.annotation_spine.snapshotAt_shaped .nil position
  have suffixEq : snapshot.consumed' :: tail =
      raw.consumedDomain :: raw.consumedTail :=
    snapshotSuffixEq.symm.trans raw.consumed_suffix_eq
  exact ⟨position, snapshot, (List.cons.inj suffixEq).1, by
      simpa only [VLCtx.toCtx, List.append_nil] using snapshotContext,
    by simpa [VLCtx.fvars] using
      snapshotFVars,
    terminalLift, snapshotShape⟩

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.RawFirstIndexDomain.annotationSnapshot' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.RawFirstIndexDomain.annotationSnapshot

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

/-- The first candidate's producer-owned annotation run exposes its exact
verified context at the shared-parameter boundary, including the embedding
into the complete first-family terminal context. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.firstParameterContext
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
    ∃ parameterΔ : VLCtx,
      parameterΔ.toCtx =
        (annotation.firstStoredBinders.take source.nparams).reverse ∧
      parameterΔ.fvars.map Expr.fvar =
        (annotation.firstCandidate.familyType.type.trace.parameterList
          source.nparams).reverse ∧
      VLCtx.FVLift' parameterΔ
        annotation.firstTerminalRun.context.vlctx 0
        (.skipN .refl
          (annotation.firstStoredBinders.drop source.nparams).length) 0 ∧
      parameterΔ.FVarLamOnly := by
  have parameterBound : source.nparams ≤
      annotation.firstStoredBinders.length := by
    rw [annotation.firstStoredLength, ← annotation.firstSpineLength_eq]
    exact annotation.first_nparams_le_spineLength context_lctx_eq
  obtain ⟨parameterΔ, parameterContext, parameterFVars, terminalLift,
      parameterShape⟩ :=
    annotation.first_annotation_spine.prefixContext_shaped .nil parameterBound
  exact ⟨parameterΔ, by
      simpa only [VLCtx.toCtx, List.append_nil] using parameterContext,
    by simpa [VLCtx.fvars] using parameterFVars,
    terminalLift, parameterShape⟩

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

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.firstParameterContext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.firstParameterContext

private theorem candidateContextRun_cast_context
    {left right : AddInductive.Context}
    (h : left = right)
    (run : TypeChecker.CandidateContextRun left) :
    (h ▸ run).context = run.context := by
  cases h
  rfl

private theorem list_map_fvar_injective :
    ∀ {left right : List FVarId},
      left.map Expr.fvar = right.map Expr.fvar → left = right := by
  intro left
  induction left with
  | nil =>
      intro right equality
      cases right
      · rfl
      · simp at equality
  | cons head tail ih =>
      intro right equality
      cases right with
      | nil => simp at equality
      | cons other rest =>
          simp only [List.map_cons, List.cons.injEq] at equality
          rw [Expr.fvar.inj equality.1, ih equality.2]

private theorem sharedParameterTelescopeDefEqAux
    {env : VEnv} {Us : List Name}
    {nparams : Nat}
    {stats : AddInductive.InductiveStats}
    {validatorContext : AddInductive.Context}
    {validatorSource : Expr} {i nindices fuel : Nat}
    {outer : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
      validatorContext validatorSource i nindices fuel}
    {suffixSource : Expr} {suffixFuel : Nat}
    {suffix : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
      validatorContext suffixSource nparams nindices suffixFuel}
    {parameters : List Expr}
    (path : AddInductive.FamilyTypeParameterComparisonTrace.SharedPrefixPath
      nparams outer suffix parameters)
    (paramsSize : stats.params.size = nparams)
    (localState : TypeChecker.FamilyParameterLocalState stats validatorContext)
    (currentRun : TypeChecker.CandidateContextRun validatorContext)
    (currentVenv : currentRun.context.venv = env)
    (currentLparams : currentRun.context.lparams = Us)
    {validatorSource' : VExpr}
    (validatorSourceTr : currentRun.context.TrExprS
      validatorSource validatorSource')
    (recursionFuel : Nat)
    (validatorDepth : validatorContext.fuel.recDepth = recursionFuel + 1)
    {firstContext : AddInductive.Context} {firstSource : Expr}
    {firstTrace : AddInductive.CandidateExprTrace firstContext firstSource}
    {firstΔ firstTerminalΔ : VLCtx} {firstDomains : List VExpr}
    (firstSpine : TypeChecker.CandidateAnnotationSpine env Us firstTrace
      firstΔ firstTerminalΔ firstDomains)
    (firstAnnotations : firstTrace.validationAnnotations)
    (firstLocalRun : TypeChecker.CandidateLocalContextRun firstContext)
    (firstTerminalFind : ∀ {fv : FVarId} {decl : LocalDecl},
      firstTrace.terminalContext.lctx.find? fv = some decl →
        validatorContext.lctx.find? fv = some decl)
    {secondContext : AddInductive.Context} {secondSource : Expr}
    {secondTrace : AddInductive.CandidateExprTrace secondContext secondSource}
    {secondΔ secondTerminalΔ : VLCtx} {secondDomains : List VExpr}
    (secondSpine : TypeChecker.CandidateAnnotationSpine env Us secondTrace
      secondΔ secondTerminalΔ secondDomains)
    (secondAnnotations : secondTrace.validationAnnotations)
    (secondPosition : secondTrace.MainSpineAt count)
    (secondAligned : secondTrace.storedSpine = true)
    (secondDepth : secondContext.fuel.recDepth = recursionFuel + 1)
    (validatorSecondRoot : 0 < count →
      validatorSource = secondTrace.rootWhnf)
    (parametersFirst : parameters = firstTrace.parameterList count)
    (parametersSecond : parameters = secondTrace.parameterList count)
    (contextRelation : VLCtx.IsDefEqFVars env Us.length firstΔ secondΔ)
    {reference : VLCtx} {firstReferenceLift : Lift}
    (firstTerminalReference : VLCtx.FVLift' firstTerminalΔ reference 0
      firstReferenceLift 0)
    (currentReference : VLCtx.IsDefEq env Us.length
      currentRun.context.vlctx reference) :
    TypeChecker.TelDefEqEvidence env Us.length firstΔ.toCtx
      (firstDomains.take count) (secondDomains.take count) := by
  have henv : VEnv.WF env := by
    simpa only [currentVenv] using currentRun.context.Ewf
  have currentWF : VLCtx.WF env Us.length currentRun.context.vlctx := by
    simpa only [currentVenv, currentLparams] using currentRun.context.Δwf
  have referenceWF : VLCtx.WF env Us.length reference :=
    (currentReference.symm henv.ordered).wf
  have firstTerminalWF : VLCtx.WF env Us.length firstTerminalΔ :=
    firstTerminalReference.wf henv referenceWF
  induction secondPosition generalizing stats validatorSource i fuel outer
      suffixSource suffixFuel suffix parameters validatorSource'
      firstContext firstSource firstTrace firstΔ firstDomains
      secondΔ secondDomains with
  | zero trace =>
      cases path with
      | done => exact .nil
      | shared =>
          simp only [AddInductive.CandidateExprTrace.parameterList]
            at parametersSecond
          contradiction
  | succ bodyCandidate secondPosition ih =>
      rename_i n secondCandidateContext secondCandidateSource
        secondInferred secondName secondDomain secondBody secondBinderInfo
        secondFresh secondAnnotationsNode secondAnnotationsEq secondChecked
        secondNormalized secondDomainCandidate
      simp only [AddInductive.CandidateExprTrace.storedSpine,
        Bool.and_eq_true] at secondAligned
      rcases secondAligned with ⟨secondSourceStored, secondBodyAligned⟩
      rcases secondAnnotations with
        ⟨secondAnnotationMatch, secondTailAnnotations⟩
      cases secondSpine with
      | forallE secondDomainCandidate' secondBodyCandidate secondStoredDomain
          secondStoredDomains secondHead secondTail =>
          cases firstSpine with
          | terminal =>
              simp only [AddInductive.CandidateExprTrace.parameterList]
                at parametersFirst parametersSecond
              simp_all
          | forallE firstDomainCandidate firstBodyCandidate firstStoredDomain
              firstStoredDomains firstHead firstTail =>
              rename_i firstDomain firstName firstBinderInfo firstBody
                firstInferred firstAnnotationsNode firstFresh
                firstAnnotationsEq firstChecked firstNormalized
              rcases firstAnnotations with
                ⟨firstAnnotationMatch, firstTailAnnotations⟩
              simp only [AddInductive.CandidateExprTrace.parameterList]
                at parametersFirst parametersSecond
              cases path with
              | done => simp_all
              | shared tail suffix parametersTail isParameter laterFamily
                  parameterTypeRun comparisonValid whnf pathTail =>
                  rename_i validatorView validatorFuel parameterType
                    validatorDomain validatorName validatorBody
                    validatorBinderInfo
                  have parameterFirst : stats.params[i]! =
                      firstContext.freshExpr :=
                    (List.cons.inj parametersFirst).1
                  have parameterSecond : stats.params[i]! =
                      secondCandidateContext.freshExpr :=
                    (List.cons.inj parametersSecond).1
                  have parametersFirstTail : parametersTail =
                      firstBodyCandidate.parameterList n :=
                    (List.cons.inj parametersFirst).2
                  have parametersSecondTail : parametersTail =
                      bodyCandidate.parameterList n :=
                    (List.cons.inj parametersSecond).2
                  have sourceParts := validatorSecondRoot (by omega)
                  simp only [AddInductive.CandidateExprTrace.rootWhnf,
                    Expr.forallE.injEq] at sourceParts
                  rcases sourceParts with
                    ⟨validatorNameEq, validatorDomainEq, validatorBodyEq,
                      validatorBinderInfoEq⟩
                  obtain ⟨firstSnapshot, firstSnapshotContext,
                      firstStoredEq⟩ := firstHead firstAnnotationMatch
                  subst firstSnapshotContext
                  obtain ⟨secondSnapshot, secondSnapshotContext,
                      secondStoredEq⟩ := secondHead secondAnnotationMatch
                  subst secondSnapshotContext
                  have firstRootParts := firstSnapshot.root_eq
                  simp only [Expr.forallE.injEq] at firstRootParts
                  rcases firstRootParts with
                    ⟨firstSnapshotNameEq, firstSnapshotDomainEq,
                      firstSnapshotBodyEq, firstSnapshotBinderInfoEq⟩
                  have secondRootParts := secondSnapshot.root_eq
                  simp only [Expr.forallE.injEq] at secondRootParts
                  rcases secondRootParts with
                    ⟨secondSnapshotNameEq, secondSnapshotDomainEq,
                      secondSnapshotBodyEq, secondSnapshotBinderInfoEq⟩
                  have validatorSnapshotDomainEq : validatorDomain =
                      secondSnapshot.domain :=
                    validatorDomainEq.trans secondSnapshotDomainEq
                  have firstConsumedSourceEq :
                      firstAnnotationsNode.consumed =
                        firstSnapshot.consumed := by
                    calc
                      firstAnnotationsNode.consumed =
                          AddInductive.consumeTypeAnnotations firstDomain :=
                        firstAnnotationMatch
                      _ = AddInductive.consumeTypeAnnotations
                            firstSnapshot.domain :=
                        congrArg AddInductive.consumeTypeAnnotations
                          firstSnapshotDomainEq
                      _ = firstSnapshot.consumed :=
                        firstSnapshot.annotation_match.symm
                  have firstParameterFind :=
                    TypeChecker.CandidateExprTrace.head_find_terminal
                      firstName firstBinderInfo firstAnnotationsNode
                      firstBodyCandidate firstLocalRun
                  have validatorParameterFind :=
                    firstTerminalFind firstParameterFind
                  have validatorFirstParameterTypeRun :
                      AddInductive.getType firstContext.freshExpr
                        validatorContext =
                          .ok firstAnnotationsNode.consumed := by
                    simpa [AddInductive.Context.freshExpr, LocalDecl.type]
                      using TypeChecker.getType_fvar_of_find
                        validatorParameterFind
                  have parameterTypeEq : parameterType =
                      firstAnnotationsNode.consumed := by
                    have validatorParameterTypeRun := parameterTypeRun
                    rw [parameterFirst] at validatorParameterTypeRun
                    exact Except.ok.inj
                      (validatorParameterTypeRun.symm.trans
                        validatorFirstParameterTypeRun)
                  have parameterSnapshotEq : parameterType =
                      firstSnapshot.consumed :=
                    parameterTypeEq.trans firstConsumedSourceEq
                  let @TrExprS.forallE _ _ validatorDomain'
                      validatorBody' _ _ _ _ _ validatorDomainType
                      validatorBodyType validatorDomainTr validatorBodyTr :=
                    validatorSourceTr
                  have parameterMember : stats.params[i]! ∈
                      stats.params.toList := by
                    rw [show stats.params[i]! = stats.params[i] by
                      simp [isParameter, paramsSize]]
                    exact List.getElem_mem (by
                      simpa only [Array.length_toList, paramsSize] using
                        isParameter)
                  obtain ⟨fv, decl, parameterEq, parameterFind⟩ :=
                    localState.parameters parameterMember
                  have parameterTypeRun' :
                      AddInductive.getType (.fvar fv) validatorContext =
                        .ok parameterType := by
                    rw [← parameterEq]
                    exact parameterTypeRun
                  obtain ⟨fvValue, parameterType', fvFind,
                      parameterTypeTr⟩ :=
                    currentRun.getTypeTranslation parameterFind
                      parameterTypeRun'
                  have fvTr : currentRun.context.TrExprS (.fvar fv)
                      fvValue := .fvar fvFind
                  let comparisonRun : TypeChecker.IsDefEqRun
                      currentRun.context.venv currentRun.context.lparams
                      currentRun.context.vlctx validatorDomain parameterType
                      validatorDomain' parameterType' :=
                    TypeChecker.IsDefEqRun.ofCandidateStep
                      ⟨validatorContext, validatorDomain, parameterType⟩
                      comparisonValid currentRun.context
                      currentRun.context_eq rfl rfl rfl
                      currentRun.state_wf validatorDomainTr parameterTypeTr
                      validatorContext.fuel.recDepth rfl
                  have currentEnvWF : VEnv.WF currentRun.context.venv :=
                    currentRun.context.Ewf
                  have currentCtxWF : OnCtx
                      currentRun.context.vlctx.toCtx
                      (currentRun.context.venv.IsType
                        currentRun.context.lparams.length) :=
                    currentRun.context.Δwf.toCtx
                  obtain ⟨validatorSort, validatorDomainHasType⟩ :=
                    validatorDomainType
                  have validatorDomainDef :
                      currentRun.context.venv.IsDefEq
                        currentRun.context.lparams.length
                        currentRun.context.vlctx.toCtx validatorDomain'
                        parameterType' (.sort validatorSort) :=
                    comparisonRun.isDefEqU.of_l currentEnvWF currentCtxWF
                      validatorDomainHasType
                  have fvHasParameterType :
                      currentRun.context.venv.HasType
                        currentRun.context.lparams.length
                        currentRun.context.vlctx.toCtx fvValue
                        parameterType' :=
                    currentRun.context.Δwf.find?_wf
                      currentRun.context.Ewf.ordered fvFind
                  have fvHasDomain : currentRun.context.venv.HasType
                      currentRun.context.lparams.length
                      currentRun.context.vlctx.toCtx fvValue
                      validatorDomain' :=
                    validatorDomainDef.symm.defeq fvHasParameterType
                  have bodyInstTr : currentRun.context.TrExprS
                      (validatorBody.instantiate1 (.fvar fv))
                      (validatorBody'.inst fvValue) := by
                    simpa only [Expr.instantiate1_eq] using
                      validatorBodyTr.inst currentRun.context.Ewf.ordered
                        fvHasDomain fvTr
                  have bodyInstTr' : currentRun.context.TrExprS
                      (validatorBody.instantiate1 stats.params[i]!)
                      (validatorBody'.inst fvValue) := by
                    rw [parameterEq]
                    exact bodyInstTr
                  obtain ⟨validatorView', validatorViewTr,
                      ⟨validatorViewRun⟩⟩ :=
                    TypeChecker.WhnfRun.exists_ofCandidateStep
                      ⟨validatorContext,
                        validatorBody.instantiate1 stats.params[i]!,
                        validatorView⟩ whnf currentRun
                      (validatorBody'.inst fvValue) bodyInstTr'
                      recursionFuel validatorDepth
                  have validatorDomainTrEnv : TrExprS env Us
                      currentRun.context.vlctx validatorDomain
                      validatorDomain' := by
                    simpa only [TypeChecker.VContext.TrExprS, currentVenv,
                      currentLparams] using validatorDomainTr
                  have parameterTypeTrEnv : TrExprS env Us
                      currentRun.context.vlctx parameterType
                      parameterType' := by
                    simpa only [TypeChecker.VContext.TrExprS, currentVenv,
                      currentLparams] using parameterTypeTr
                  have firstLift : VLCtx.FVLift' firstSnapshot.Δ
                      firstTerminalΔ 0
                      (.skipN .refl
                        (firstStoredDomain :: firstStoredDomains).length) 0 := by
                    have combined :=
                      (VLCtx.FVLift'.skip_fvar _ _
                        VLCtx.FVLift'.refl).comp
                        (TypeChecker.CandidateAnnotationSpine.terminalLift
                          firstTail)
                    simpa only [List.length_cons, Lift.comp_skipN,
                      Lift.comp, Lift.skipN_skipN, VLocalDecl.depth,
                      Nat.one_add] using combined
                  have firstReference : VLCtx.FVLift' firstSnapshot.Δ
                      reference 0
                      ((Lift.skipN Lift.refl
                        (firstStoredDomain ::
                          firstStoredDomains).length).comp
                        firstReferenceLift) 0 :=
                    firstLift.comp firstTerminalReference
                  have firstWF : VLCtx.WF env Us.length firstSnapshot.Δ :=
                    firstLift.wf henv firstTerminalWF
                  have validatorDomainClosed : Closed validatorDomain 0 := by
                    rw [validatorSnapshotDomainEq]
                    simpa only [secondSnapshot.context_noBV] using
                      secondSnapshot.domain_tr.closed
                  have validatorDomainFVars :
                      FVarsIn (· ∈ firstSnapshot.Δ.fvars)
                        validatorDomain := by
                    rw [validatorSnapshotDomainEq]
                    simpa only [contextRelation.fvars] using
                      secondSnapshot.domain_tr.fvarsIn
                  have parameterTypeClosed : Closed parameterType 0 := by
                    rw [parameterSnapshotEq]
                    simpa only [firstSnapshot.context_noBV] using
                      firstSnapshot.consumed_tr.closed
                  have parameterTypeFVars :
                      FVarsIn (· ∈ firstSnapshot.Δ.fvars)
                        parameterType := by
                    rw [parameterSnapshotEq]
                    exact firstSnapshot.consumed_tr.fvarsIn
                  obtain ⟨baseDomain, baseDomainTr⟩ :=
                    validatorDomainTrEnv.weakFV'_inv henv firstReference
                      currentReference validatorDomainClosed
                      validatorDomainFVars
                  obtain ⟨baseParameterType, baseParameterTypeTr⟩ :=
                    parameterTypeTrEnv.weakFV'_inv henv firstReference
                      currentReference parameterTypeClosed
                      parameterTypeFVars
                  have comparisonCurrent : env.IsDefEqU Us.length
                      currentRun.context.vlctx.toCtx validatorDomain'
                      parameterType' := by
                    simpa only [currentVenv, currentLparams] using
                      comparisonRun.isDefEqU
                  have baseDomainAtReference :=
                    baseDomainTr.weakFV' henv.ordered firstReference
                      referenceWF
                  have baseParameterTypeAtReference :=
                    baseParameterTypeTr.weakFV' henv.ordered firstReference
                      referenceWF
                  have currentDomainEq :=
                    validatorDomainTrEnv.uniq henv currentReference
                      baseDomainAtReference
                  have currentParameterTypeEq :=
                    parameterTypeTrEnv.uniq henv currentReference
                      baseParameterTypeAtReference
                  have comparisonAtReference :=
                    comparisonCurrent.defeqDFC henv.ordered
                      currentReference.defeqCtx
                  have currentDomainEqAtReference :=
                    currentDomainEq.defeqDFC henv.ordered
                      currentReference.defeqCtx
                  have currentParameterTypeEqAtReference :=
                    currentParameterTypeEq.defeqDFC henv.ordered
                      currentReference.defeqCtx
                  have liftedComparison : env.IsDefEqU Us.length
                      reference.toCtx
                      (baseDomain.lift'
                        (((Lift.skipN Lift.refl
                          (firstStoredDomain :: firstStoredDomains).length).comp
                            firstReferenceLift).consN 0))
                      (baseParameterType.lift'
                        (((Lift.skipN Lift.refl
                          (firstStoredDomain :: firstStoredDomains).length).comp
                            firstReferenceLift).consN 0)) :=
                    (currentDomainEqAtReference.symm.trans henv
                      referenceWF.toCtx comparisonAtReference).trans henv
                        referenceWF.toCtx
                        currentParameterTypeEqAtReference
                  have comparisonAtBase : env.IsDefEqU Us.length
                      firstSnapshot.Δ.toCtx baseDomain baseParameterType :=
                    (VEnv.IsDefEqU.weak'_iff henv referenceWF.toCtx
                      firstReference.toCtx).1 liftedComparison
                  have snapshotDomainTr : TrExprS env Us secondSnapshot.Δ
                      validatorDomain secondSnapshot.domain' := by
                    rw [validatorSnapshotDomainEq]
                    exact secondSnapshot.domain_tr
                  have baseDomainSnapshotEq : env.IsDefEqU Us.length
                      firstSnapshot.Δ.toCtx baseDomain
                      secondSnapshot.domain' :=
                    baseDomainTr.uniqFVars henv contextRelation firstWF
                      snapshotDomainTr
                  have snapshotParameterTypeTr : TrExprS env Us
                      firstSnapshot.Δ parameterType
                      firstSnapshot.consumed' := by
                    rw [parameterSnapshotEq]
                    exact firstSnapshot.consumed_tr
                  have baseParameterSnapshotEq : env.IsDefEqU Us.length
                      firstSnapshot.Δ.toCtx baseParameterType
                      firstSnapshot.consumed' :=
                    baseParameterTypeTr.uniq henv (.refl henv firstWF)
                      snapshotParameterTypeTr
                  have secondAnnotationAtFirst : env.IsDefEqU Us.length
                      firstSnapshot.Δ.toCtx secondSnapshot.domain'
                      secondSnapshot.consumed' :=
                    secondSnapshot.annotation_run.isDefEqU.defeqDFC
                      henv.ordered
                      (contextRelation.defeqCtx.symm henv.ordered)
                  have firstAnnotation :=
                    firstSnapshot.annotation_run.isDefEqU.of_l henv
                      firstWF.toCtx firstSnapshot.domain_type
                  have storedDomainsU : env.IsDefEqU Us.length
                      firstSnapshot.Δ.toCtx firstSnapshot.consumed'
                      secondSnapshot.consumed' :=
                    (((baseParameterSnapshotEq.symm.trans henv firstWF.toCtx
                      comparisonAtBase.symm).trans henv firstWF.toCtx
                        baseDomainSnapshotEq).trans henv firstWF.toCtx
                          secondAnnotationAtFirst)
                  have storedDomainsDef :=
                    storedDomainsU.of_l henv firstWF.toCtx
                      firstAnnotation.hasType.2
                  rw [firstStoredEq, secondStoredEq] at storedDomainsDef
                  cases n with
                  | zero =>
                      have combined :
                          TypeChecker.TelDefEqEvidence env Us.length
                            firstSnapshot.Δ.toCtx
                            (firstStoredDomain ::
                              firstStoredDomains.take 0)
                            (secondStoredDomain ::
                              secondStoredDomains.take 0) :=
                        .cons (.ofDefEq storedDomainsDef) .nil
                      simpa only [List.take_succ_cons] using combined
                  | succ n =>
                      have candidateTailIsForall :
                          (secondBody.instantiate1
                            secondCandidateContext.freshExpr).isForall =
                              true :=
                        secondPosition.traceSource_isForall (by omega)
                          secondBodyAligned
                      have candidateBodyEq :=
                        AddInductive.CandidateWhnfStep.result_eq_of_source_isForall
                          bodyCandidate.rootWhnf_valid recursionFuel (by
                            simpa [AddInductive.Context.pushLocalDecl] using
                              secondDepth) candidateTailIsForall
                      have validatorTailIsForall :
                          (validatorBody.instantiate1
                            stats.params[i]!).isForall = true := by
                        rw [parameterSecond, validatorBodyEq]
                        exact candidateTailIsForall
                      have validatorBodyWhnfEq :=
                        AddInductive.CandidateWhnfStep.result_eq_of_source_isForall
                          whnf recursionFuel validatorDepth
                          validatorTailIsForall
                      have nextSourceEq : validatorView =
                          bodyCandidate.rootWhnf :=
                        validatorBodyWhnfEq.trans (by
                          rw [parameterSecond, validatorBodyEq]
                          exact candidateBodyEq.symm)
                      have freshIdEq : firstContext.freshFVarId =
                          secondCandidateContext.freshFVarId := by
                        apply Expr.fvar.inj
                        exact parameterFirst.symm.trans parameterSecond
                      have nextRelation :
                          VLCtx.IsDefEqFVars env Us.length
                            ((some (firstContext.freshFVarId,
                                firstAnnotationsNode.consumed.fvarsList),
                              .vlam firstStoredDomain) :: firstSnapshot.Δ)
                            ((some (secondCandidateContext.freshFVarId,
                                secondAnnotationsNode.consumed.fvarsList),
                              .vlam secondStoredDomain) ::
                                secondSnapshot.Δ) := by
                        rw [← freshIdEq]
                        exact .cons_fvar contextRelation
                          (.vlam storedDomainsDef)
                      have tailEvidence := ih pathTail paramsSize localState
                        validatorViewTr firstTail firstTailAnnotations
                        (firstLocalRun.push firstName firstBinderInfo
                          firstAnnotationsNode.consumed)
                        (fun found => firstTerminalFind (by
                          simpa only [
                            AddInductive.CandidateExprTrace.terminalContext]
                            using found))
                        secondTail secondTailAnnotations secondBodyAligned
                        (by simpa [AddInductive.Context.pushLocalDecl] using
                          secondDepth)
                        (fun _ => nextSourceEq) parametersFirstTail
                        parametersSecondTail
                        nextRelation
                      have combined :
                          TypeChecker.TelDefEqEvidence env Us.length
                            firstSnapshot.Δ.toCtx
                            (firstStoredDomain ::
                              firstStoredDomains.take (n + 1))
                            (secondStoredDomain ::
                              secondStoredDomains.take (n + 1)) :=
                        .cons (.ofDefEq storedDomainsDef) tailEvidence
                      simpa only [List.take_succ_cons] using combined

/-- A selected second-family telescope starts in the exact reader context
reached after the first family's complete telescope. -/
private theorem secondTelescope_context_eq_firstContext
    {nparams dIdx : Nat} {indTypes : Array InductiveType}
    {stats : AddInductive.InductiveStats}
    {context : AddInductive.Context}
    (trace : AddInductive.FamilyParameterComparisonBlockTrace nparams
      indTypes dIdx stats context)
    (position :
      AddInductive.FamilyParameterComparisonBlockTrace.FamilyTelescopePosition
        nparams)
    (h : trace.secondTelescope? = some position) :
    position.context = trace.firstContext := by
  cases trace with
  | firstFamily dIdx stats context inBounds closed inferred root checkType
      rootWhnf telescope sorted ensureSort isFirst tail =>
      cases tail
      case firstFamily =>
        simp only [
          AddInductive.FamilyParameterComparisonBlockTrace.secondTelescope?,
          AddInductive.FamilyParameterComparisonBlockTrace.headTelescope?,
          AddInductive.FamilyParameterComparisonBlockTrace.firstContext]
            at h ⊢
        cases Option.some.inj h
        rfl
      case laterFamily =>
        simp only [
          AddInductive.FamilyParameterComparisonBlockTrace.secondTelescope?,
          AddInductive.FamilyParameterComparisonBlockTrace.headTelescope?,
          AddInductive.FamilyParameterComparisonBlockTrace.firstContext]
            at h ⊢
        cases Option.some.inj h
        rfl
      case terminal =>
        simp only [
          AddInductive.FamilyParameterComparisonBlockTrace.secondTelescope?,
          AddInductive.FamilyParameterComparisonBlockTrace.headTelescope?]
            at h
        contradiction
  | laterFamily dIdx stats context inBounds closed inferred root checkType
      rootWhnf telescope sorted ensureSort isLater compatible tail =>
      cases tail
      case firstFamily =>
        simp only [
          AddInductive.FamilyParameterComparisonBlockTrace.secondTelescope?,
          AddInductive.FamilyParameterComparisonBlockTrace.headTelescope?,
          AddInductive.FamilyParameterComparisonBlockTrace.firstContext]
            at h ⊢
        cases Option.some.inj h
        rfl
      case laterFamily =>
        simp only [
          AddInductive.FamilyParameterComparisonBlockTrace.secondTelescope?,
          AddInductive.FamilyParameterComparisonBlockTrace.headTelescope?,
          AddInductive.FamilyParameterComparisonBlockTrace.firstContext]
            at h ⊢
        cases Option.some.inj h
        rfl
      case terminal =>
        simp only [
          AddInductive.FamilyParameterComparisonBlockTrace.secondTelescope?,
          AddInductive.FamilyParameterComparisonBlockTrace.headTelescope?]
            at h
        contradiction
  | terminal =>
      simp only [
        AddInductive.FamilyParameterComparisonBlockTrace.secondTelescope?]
          at h
      contradiction

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
        position.stats.indConsts.isEmpty = false ∧
        position.stats.params.size = source.nparams ∧
        position.i = 0 ∧
        position.nindices = 0 ∧
        position.context.fuel = context.fuel ∧
        AddInductive.CandidateWhnfStep.Valid
          ⟨position.context, secondSource.type, position.source⟩ ∧
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
      position.stats.indConsts.isEmpty = false ∧
      position.stats.params.size = source.nparams ∧
      position.i = 0 ∧
      position.nindices = 0 ∧
      position.context.fuel = context.fuel ∧
      AddInductive.CandidateWhnfStep.Valid
        ⟨position.context, secondSource.type, position.source⟩ ∧
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
                    secondRuns, secondPosition, (by rfl), statsLater,
                    paramsSize,
                    (by rfl), (by rfl), telescope.result_context_fuel,
                    secondRootWhnf,
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
  position_later : position.stats.indConsts.isEmpty = false
  position_params_size : position.stats.params.size = source.nparams
  position_i_eq : position.i = 0
  position_nindices_eq : position.nindices = 0
  position_fuel_eq : position.context.fuel = context.fuel
  position_root_whnf : AddInductive.CandidateWhnfStep.Valid
    ⟨position.context, secondSource.type, position.source⟩
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

/-- The exact second family selected from the outer source traversal, retaining
the dependent tail that begins after its complete telescope. -/
structure
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.ValidationContinuation
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
    (staging : produced.SecondFamilyIndexStaging semantic) where
  continuation :
    AddInductive.FamilyParameterComparisonBlockTrace.FamilyContinuation
      source.nparams
      (firstSource :: secondSource :: remainingSources).toArray
  selected :
    (produced.execution.eliminationExecution.normalization
      |>.familyParameterComparisonTrace
        (produced.execution.normalization_run produced.producedExecution)
        produced.kernelSources_nonempty).secondContinuation? =
      some continuation
  position_eq : continuation.position = staging.position

/-- Recover the second family's dependent source-order continuation from the
position already owned by the joint producer/validator staging. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.validationContinuation
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
    Nonempty staging.ValidationContinuation := by
  obtain ⟨continuation, selected, positionEq⟩ :=
    AddInductive.FamilyParameterComparisonBlockTrace.exists_secondContinuation_of_secondTelescope
      staging.position_eq
  exact ⟨⟨continuation, selected, positionEq⟩⟩

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
      comparisonRuns, position, positionEq, positionLater,
      positionParamsSize, positionIEq,
      positionNindicesEq, positionFuelEq, positionRootWhnf, currentRun,
      currentVenv, currentLparams,
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
    position_later := positionLater
    position_params_size := positionParamsSize
    position_i_eq := positionIEq
    position_nindices_eq := positionNindicesEq
    position_fuel_eq := positionFuelEq
    position_root_whnf := positionRootWhnf
    currentRun := currentRun
    current_venv := currentVenv
    current_lparams := currentLparams
    parameterRoot := parameterRoot
    parameterRoot_tr := parameterRootTr
    rawRoot_def := rawRootDef
    boundary := boundary
    parameterSpine := parameterSpine }⟩

/-- The second-family validator starts in the exact terminal producer context
of the first candidate family. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.position_context_eq_firstTerminal
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
    staging.position.context =
      staging.annotation.firstCandidate.familyType.type.trace.terminalContext := by
  let normalization :=
    produced.execution.eliminationExecution.normalization
  have normalizationProduced :=
    produced.execution.normalization_run produced.producedExecution
  let comparisonTrace :=
    normalization.familyParameterComparisonTrace normalizationProduced
      produced.kernelSources_nonempty
  have positionEq := staging.position_eq
  change comparisonTrace.secondTelescope? = some staging.position at positionEq
  have positionContext :=
    secondTelescope_context_eq_firstContext comparisonTrace staging.position
      positionEq
  have firstContext :=
    normalization.firstFamilyComparisonContext_eq normalizationProduced
      context_lctx_eq
  have candidatesEq := staging.annotation.candidates_eq
  change normalization.families.candidates =
    .cons staging.annotation.firstCandidate
      (.cons staging.annotation.secondCandidate
        staging.annotation.remainingCandidates) at candidatesEq
  rw [← normalization.families.produced.familyTypes_eq] at firstContext
  rw [candidatesEq] at firstContext
  simp only [AddInductive.CandidateList.head] at firstContext
  exact positionContext.trans firstContext

/-- The validator's first-index context and the first candidate's producer
terminal context are ordinary definitionally equal verified translations of
the same kernel local context. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.current_firstTerminal_defeq
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
    VLCtx.IsDefEq env Us.length staging.currentRun.context.vlctx
      staging.annotation.firstTerminalRun.context.vlctx := by
  have contextEq := staging.position_context_eq_firstTerminal context_lctx_eq
  have currentTr := staging.currentRun.context.trlctx
  change TrLCtx staging.currentRun.context.venv
    staging.currentRun.context.lparams staging.currentRun.context.mlctx.lctx
    staging.currentRun.context.vlctx at currentTr
  rw [staging.current_venv, staging.current_lparams,
    staging.currentRun.context.lctx_eq,
    staging.currentRun.context_lctx] at currentTr
  have firstTr := staging.annotation.firstTerminalRun.context.trlctx
  change TrLCtx staging.annotation.firstTerminalRun.context.venv
    staging.annotation.firstTerminalRun.context.lparams
    staging.annotation.firstTerminalRun.context.mlctx.lctx
    staging.annotation.firstTerminalRun.context.vlctx at firstTr
  rw [staging.annotation.first_terminal_venv,
    staging.annotation.first_terminal_lparams,
    staging.annotation.firstTerminalRun.context.lctx_eq,
    staging.annotation.firstTerminalRun.context_lctx] at firstTr
  have lctxEq := congrArg AddInductive.Context.lctx contextEq
  rw [← lctxEq] at firstTr
  have henv : VEnv.WF env := by
    simpa only [staging.current_venv] using staging.currentRun.context.Ewf
  exact TrLCtx.isDefEq henv currentTr firstTr

/-- Free-variable-preserving projection of the exact validator/first-terminal
context equality. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.current_firstTerminal_defeqFVars
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
    VLCtx.IsDefEqFVars env Us.length staging.currentRun.context.vlctx
      staging.annotation.firstTerminalRun.context.vlctx :=
  (staging.current_firstTerminal_defeq context_lctx_eq).toFVars

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


/-- The validator's exact first-index source is literally the candidate
annotation root at the declared parameter position.

The proof follows the retained shared-parameter path, identifies the two
context-independent Pi WHNF observations, and retains the exact semantic
snapshot whose consumed endpoint is the producer's first stored index domain. -/
theorem ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.rawFirstIndexAnnotationAlignment
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
    (context_lctx_eq : context.lctx = {}) :
    ∃ position : staging.annotation.secondCandidate.familyType.type.trace.AnnotationAt
        source.nparams,
      ∃ snapshot : TypeChecker.CandidateAnnotationSnapshot env Us
          position.root,
        staging.boundary.source = position.root ∧
          snapshot.consumed' = raw.consumedDomain ∧
          snapshot.Δ.toCtx =
            (staging.annotation.storedBinders.take source.nparams).reverse ∧
          snapshot.Δ.fvars.map Expr.fvar =
            (staging.boundary.parameters.map Prod.fst).reverse ∧
          VLCtx.FVLift' snapshot.Δ
            staging.annotation.terminalRun.context.vlctx 0
            (.skipN .refl
              (staging.annotation.storedBinders.drop source.nparams).length)
            0 ∧
          snapshot.Δ.FVarLamOnly := by
  obtain ⟨position, snapshot, consumedEq, snapshotContext,
      snapshotFVars, terminalLift, snapshotShape⟩ := raw.annotationSnapshot
  have candidateIsForall :=
    position.traceSource_isForall staging.annotation.stored_spine
  have contextDepth : staging.position.context.fuel.recDepth =
      staging.annotation.whnfFuel + 1 := by
    calc
      staging.position.context.fuel.recDepth = context.fuel.recDepth :=
        congrArg (fun fuel => fuel.recDepth) staging.position_fuel_eq
      _ = ({ context with lctx := {} } : AddInductive.Context).fuel.recDepth :=
        rfl
      _ = staging.annotation.secondCandidate.familyType.type.context.fuel.recDepth :=
        (congrArg (fun candidateContext => candidateContext.fuel.recDepth)
          staging.annotation.second_candidate_context_eq).symm
      _ = staging.annotation.whnfFuel + 1 := staging.annotation.whnfDepth
  have candidateRootEq :
      staging.annotation.secondCandidate.familyType.type.trace.rootWhnf =
        secondSource.type :=
    AddInductive.CandidateWhnfStep.result_eq_of_source_isForall
      staging.annotation.secondCandidate.familyType.type.trace.rootWhnf_valid
      staging.annotation.whnfFuel staging.annotation.whnfDepth
      candidateIsForall
  have validatorRootEq : staging.position.source = secondSource.type :=
    AddInductive.CandidateWhnfStep.result_eq_of_source_isForall
      staging.position_root_whnf staging.annotation.whnfFuel contextDepth
      candidateIsForall
  have boundaryRootEq :=
    staging.boundary.prefix_path.annotationAt_root_eq
      (staging.parameterSources_eq_secondParameterList context_lctx_eq)
      position staging.annotation.stored_spine
      (validatorRootEq.trans candidateRootEq.symm)
      staging.annotation.whnfFuel contextDepth staging.annotation.whnfDepth
  exact ⟨position, snapshot, boundaryRootEq, consumedEq, snapshotContext, by
      rw [staging.parameterSources_eq_secondParameterList context_lctx_eq]
      exact snapshotFVars,
    terminalLift, snapshotShape⟩

/-- Joint inventory for the two producer-owned shared-parameter contexts used
at the first second-family index.

The first context is the prefix of the first candidate's terminal context;
the second is the exact annotation snapshot context.  Their free-variable
identifiers are already equal by construction.  The remaining semantic seam
is precisely definitional equality of their declarations. -/
structure
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.RawFirstIndexPrefixContexts
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
  position :
    staging.annotation.secondCandidate.familyType.type.trace.AnnotationAt
      source.nparams
  snapshot : TypeChecker.CandidateAnnotationSnapshot env Us position.root
  boundary_root_eq : staging.boundary.source = position.root
  snapshot_consumed_eq : snapshot.consumed' = raw.consumedDomain
  firstParameterΔ : VLCtx
  first_context : firstParameterΔ.toCtx =
    (staging.annotation.firstStoredBinders.take source.nparams).reverse
  snapshot_context : snapshot.Δ.toCtx =
    (staging.annotation.storedBinders.take source.nparams).reverse
  parameter_fvars_eq : firstParameterΔ.fvars = snapshot.Δ.fvars
  first_shape : firstParameterΔ.FVarLamOnly
  snapshot_shape : snapshot.Δ.FVarLamOnly
  first_fvars : firstParameterΔ.fvars.map Expr.fvar =
    (staging.annotation.firstCandidate.familyType.type.trace.parameterList
      source.nparams).reverse
  snapshot_fvars : snapshot.Δ.fvars.map Expr.fvar =
    (staging.boundary.parameters.map Prod.fst).reverse
  first_terminal_lift : VLCtx.FVLift' firstParameterΔ
    staging.annotation.firstTerminalRun.context.vlctx 0
    (.skipN .refl
      (staging.annotation.firstStoredBinders.drop source.nparams).length) 0
  snapshot_terminal_lift : VLCtx.FVLift' snapshot.Δ
    staging.annotation.terminalRun.context.vlctx 0
    (.skipN .refl
      (staging.annotation.storedBinders.drop source.nparams).length) 0
  current_firstTerminal_defeq : VLCtx.IsDefEq env Us.length
    staging.currentRun.context.vlctx
    staging.annotation.firstTerminalRun.context.vlctx

/-- Assemble the exact two-prefix inventory without asking a caller to select
either context or annotation position. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.rawFirstIndexPrefixContexts
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
    (context_lctx_eq : context.lctx = {}) :
    Nonempty (staging.RawFirstIndexPrefixContexts raw) := by
  obtain ⟨position, snapshot, boundaryRootEq, snapshotConsumedEq,
      snapshotContext, snapshotFVars, snapshotTerminalLift, snapshotShape⟩ :=
    staging.rawFirstIndexAnnotationAlignment raw context_lctx_eq
  obtain ⟨firstParameterΔ, firstContext, firstFVars,
      firstTerminalLift, firstShape⟩ :=
    staging.annotation.firstParameterContext context_lctx_eq
  have mappedFVars : firstParameterΔ.fvars.map Expr.fvar =
      snapshot.Δ.fvars.map Expr.fvar := by
    calc
      firstParameterΔ.fvars.map Expr.fvar =
          (staging.annotation.firstCandidate.familyType.type.trace
            |>.parameterList source.nparams).reverse := firstFVars
      _ = (staging.annotation.secondCandidate.familyType.type.trace
            |>.parameterList source.nparams).reverse :=
        congrArg List.reverse
          (staging.annotation.parameterLists_eq context_lctx_eq)
      _ = (staging.boundary.parameters.map Prod.fst).reverse :=
        congrArg List.reverse
          (staging.parameterSources_eq_secondParameterList
            context_lctx_eq).symm
      _ = snapshot.Δ.fvars.map Expr.fvar := snapshotFVars.symm
  exact ⟨{
    position := position
    snapshot := snapshot
    boundary_root_eq := boundaryRootEq
    snapshot_consumed_eq := snapshotConsumedEq
    firstParameterΔ := firstParameterΔ
    first_context := firstContext
    snapshot_context := snapshotContext
    parameter_fvars_eq := list_map_fvar_injective mappedFVars
    first_shape := firstShape
    snapshot_shape := snapshotShape
    first_fvars := firstFVars
    snapshot_fvars := snapshotFVars
    first_terminal_lift := firstTerminalLift
    snapshot_terminal_lift := snapshotTerminalLift
    current_firstTerminal_defeq :=
      staging.current_firstTerminal_defeq context_lctx_eq }⟩

/-- The retained shared-parameter validator constructs pointwise equality of
the first and second candidates' exact annotation-consumed parameter
telescopes. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.parameterTelescopeDefEq
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
    (prefixes : staging.RawFirstIndexPrefixContexts raw)
    (context_lctx_eq : context.lctx = {}) :
    env.TelDefEq Us.length []
      (staging.annotation.firstStoredBinders.take source.nparams)
      (staging.annotation.storedBinders.take source.nparams) := by
  have candidateIsForall :=
    prefixes.position.traceSource_isForall staging.annotation.stored_spine
  have validatorDepth : staging.position.context.fuel.recDepth =
      staging.annotation.whnfFuel + 1 := by
    calc
      staging.position.context.fuel.recDepth = context.fuel.recDepth :=
        congrArg (fun fuel => fuel.recDepth) staging.position_fuel_eq
      _ = ({ context with lctx := {} } : AddInductive.Context).fuel.recDepth :=
        rfl
      _ = staging.annotation.secondCandidate.familyType.type.context.fuel.recDepth :=
        (congrArg (fun candidateContext => candidateContext.fuel.recDepth)
          staging.annotation.second_candidate_context_eq).symm
      _ = staging.annotation.whnfFuel + 1 := staging.annotation.whnfDepth
  have candidateRootEq :
      staging.annotation.secondCandidate.familyType.type.trace.rootWhnf =
        secondSource.type :=
    AddInductive.CandidateWhnfStep.result_eq_of_source_isForall
      staging.annotation.secondCandidate.familyType.type.trace.rootWhnf_valid
      staging.annotation.whnfFuel staging.annotation.whnfDepth
      candidateIsForall
  have validatorRootEq : staging.position.source = secondSource.type :=
    AddInductive.CandidateWhnfStep.result_eq_of_source_isForall
      staging.position_root_whnf staging.annotation.whnfFuel validatorDepth
      candidateIsForall
  have validatorSecondRoot : staging.position.source =
      staging.annotation.secondCandidate.familyType.type.trace.rootWhnf :=
    validatorRootEq.trans candidateRootEq.symm
  have firstRootLctx :
      staging.annotation.firstCandidate.familyType.type.context.lctx =
        ({} : LocalContext) := by
    calc
      staging.annotation.firstCandidate.familyType.type.context.lctx =
          staging.annotation.secondCandidate.familyType.type.context.lctx :=
        congrArg AddInductive.Context.lctx
          staging.annotation.candidate_context_eq
      _ = ({ context with lctx := {} } : AddInductive.Context).lctx :=
        congrArg AddInductive.Context.lctx
          staging.annotation.second_candidate_context_eq
      _ = {} := rfl
  have parameterSourcesFirst :
      staging.boundary.parameters.map Prod.fst =
        staging.annotation.firstCandidate.familyType.type.trace.parameterList
          source.nparams :=
    staging.parameterSources_eq_positionParams.trans
      (staging.position_params_eq_firstParameterList context_lctx_eq)
  have parameterSourcesSecond :
      staging.boundary.parameters.map Prod.fst =
        staging.annotation.secondCandidate.familyType.type.trace.parameterList
          source.nparams :=
    staging.parameterSources_eq_secondParameterList context_lctx_eq
  have evidence := sharedParameterTelescopeDefEqAux
    staging.boundary.prefix_path staging.boundary.params_size
    staging.boundary.localState staging.currentRun staging.current_venv
    staging.current_lparams staging.parameterRoot_tr
    staging.annotation.whnfFuel validatorDepth
    staging.annotation.first_annotation_spine
    staging.annotation.first_validation_annotations
    (TypeChecker.CandidateLocalContextRun.empty _ firstRootLctx)
    (fun found => by
      rw [staging.position_context_eq_firstTerminal context_lctx_eq]
      exact found)
    staging.annotation.annotation_spine staging.annotation.validation_annotations
    prefixes.position.toMainSpineAt staging.annotation.stored_spine
    staging.annotation.whnfDepth (fun _ => validatorSecondRoot)
    parameterSourcesFirst
    parameterSourcesSecond (.nil) VLCtx.FVLift'.refl
    (staging.current_firstTerminal_defeq context_lctx_eq)
  simpa only [VLCtx.toCtx] using evidence.telDefEq

/-- Relocate the validator's first/second shared-parameter comparison from
the annotation-consumed binders onto both families' actual normalized views.
Each endpoint is connected through its exact raw telescope. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.viewParameterTelescopeDefEq
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
    (prefixes : staging.RawFirstIndexPrefixContexts raw)
    (context_lctx_eq : context.lctx = {}) :
    TypeChecker.TelDefEqEvidence env Us.length []
      (VExpr.telN source.nparams
        staging.annotation.firstSemantic.type.view)
      (VExpr.telN source.nparams
        staging.annotation.secondSemantic.type.view) := by
  have henv : VEnv.WF env := by
    simpa only [staging.current_venv] using staging.currentRun.context.Ewf
  have firstBound :=
    staging.annotation.first_nparams_le_spineLength context_lctx_eq
  have firstRawBound : source.nparams ≤
      (VInductDecl.ctorFields staging.annotation.firstRaw.type).length := by
    rw [← staging.annotation.firstSpineLength_eq]
    exact firstBound
  have firstRawStored :=
    staging.annotation.firstTelescope.take source.nparams
  rw [telN_take_of_le staging.annotation.firstRaw.type firstRawBound]
    at firstRawStored
  obtain ⟨firstInferred, firstRecursive⟩ :=
    staging.annotation.firstSemantic.type.recursive
  obtain ⟨firstResultType, firstFullView⟩ :=
    firstRecursive.spineEvidence staging.annotation.first_stored_spine
  have firstRawView := firstFullView.telescope.take source.nparams
  rw [telN_take_of_le staging.annotation.firstRaw.type firstBound,
    telN_take_of_le staging.annotation.firstSemantic.type.view firstBound]
    at firstRawView
  have firstStoredView : TypeChecker.TelDefEqEvidence env Us.length []
      (staging.annotation.firstStoredBinders.take source.nparams)
      (VExpr.telN source.nparams
        staging.annotation.firstSemantic.type.view) :=
    (firstRawStored.symm henv trivial).trans henv trivial firstRawView
  have secondRawStored := staging.annotation.parameterTelescope
  have secondBound := staging.annotation.second_nparams_le_spineLength
  obtain ⟨secondInferred, secondRecursive⟩ :=
    staging.annotation.secondSemantic.type.recursive
  obtain ⟨secondResultType, secondFullView⟩ :=
    secondRecursive.spineEvidence staging.annotation.stored_spine
  have secondRawView := secondFullView.telescope.take source.nparams
  rw [telN_take_of_le staging.annotation.secondRaw.type secondBound,
    telN_take_of_le staging.annotation.secondSemantic.type.view secondBound]
    at secondRawView
  have secondStoredView : TypeChecker.TelDefEqEvidence env Us.length []
      (staging.annotation.storedBinders.take source.nparams)
      (VExpr.telN source.nparams
        staging.annotation.secondSemantic.type.view) :=
    (secondRawStored.symm henv trivial).trans henv trivial secondRawView
  have storedParameters := TypeChecker.TelDefEqEvidence.ofTelDefEq
    (staging.parameterTelescopeDefEq raw prefixes context_lctx_eq)
  exact ((firstStoredView.symm henv trivial).trans henv trivial
      storedParameters).trans henv trivial secondStoredView

/-- Complete the validator's exact first index once the two producer-owned
shared-parameter contexts are known definitionally equal.

Both strict translations are first lowered from the validator context to the
first candidate's parameter prefix.  The candidate annotation equality is
transported from the second prefix to that common context, then weakened back
to the first terminal context and compared with the validator translations.
Thus the sole remaining seam is equality of the declarations stored under the
already-identical free-variable identifiers. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.firstIndexDomainRun_of_parameterContextDefEqFVars
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
    (prefixes : staging.RawFirstIndexPrefixContexts raw)
    (parameterContextDefEq : VLCtx.IsDefEqFVars env Us.length
      prefixes.firstParameterΔ prefixes.snapshot.Δ) :
    Nonempty staging.boundary.IndexDomainRun := by
  have henv : VEnv.WF env := by
    simpa only [staging.current_venv] using staging.currentRun.context.Ewf
  have currentWF : VLCtx.WF env Us.length
      staging.currentRun.context.vlctx := by
    simpa only [staging.current_venv, staging.current_lparams] using
      staging.currentRun.context.Δwf
  have firstTerminalWF : VLCtx.WF env Us.length
      staging.annotation.firstTerminalRun.context.vlctx := by
    simpa only [staging.annotation.first_terminal_venv,
      staging.annotation.first_terminal_lparams] using
      staging.annotation.firstTerminalRun.context.Δwf
  have firstParameterWF : VLCtx.WF env Us.length
      prefixes.firstParameterΔ :=
    prefixes.first_terminal_lift.wf henv firstTerminalWF
  have isForall : staging.boundary.source.isForall = true := by
    rw [prefixes.boundary_root_eq, prefixes.snapshot.root_eq]
    rfl
  obtain ⟨translation⟩ :=
    staging.boundary.indexDomainTranslation_of_forall isForall
  have rootEq :
      (Expr.forallE translation.name translation.domain translation.body
        translation.binderInfo) =
      (Expr.forallE prefixes.snapshot.name prefixes.snapshot.domain
        prefixes.snapshot.body prefixes.snapshot.binderInfo) :=
    translation.source_eq.symm.trans
      (prefixes.boundary_root_eq.trans prefixes.snapshot.root_eq)
  simp only [Expr.forallE.injEq] at rootEq
  obtain ⟨_nameEq, domainEq, _bodyEq, _binderEq⟩ := rootEq
  have consumedSourceEq :
      AddInductive.consumeTypeAnnotations translation.domain =
        prefixes.snapshot.consumed :=
    (congrArg AddInductive.consumeTypeAnnotations domainEq).trans
      prefixes.snapshot.annotation_match.symm
  have currentDomainTr : TrExprS env Us
      staging.currentRun.context.vlctx translation.domain
      translation.domain' := by
    simpa only [TypeChecker.VContext.TrExprS, staging.current_venv,
      staging.current_lparams] using
      translation.domain_tr
  have currentConsumedTr : TrExprS env Us
      staging.currentRun.context.vlctx
      (AddInductive.consumeTypeAnnotations translation.domain)
      translation.consumed' := by
    simpa only [TypeChecker.VContext.TrExprS, staging.current_venv,
      staging.current_lparams] using
      translation.consumed_tr
  have snapshotDomainTr : TrExprS env Us prefixes.snapshot.Δ
      translation.domain prefixes.snapshot.domain' := by
    rw [domainEq]
    exact prefixes.snapshot.domain_tr
  have snapshotConsumedTr : TrExprS env Us prefixes.snapshot.Δ
      (AddInductive.consumeTypeAnnotations translation.domain)
      prefixes.snapshot.consumed' := by
    rw [consumedSourceEq]
    exact prefixes.snapshot.consumed_tr
  have domainClosed : Closed translation.domain 0 := by
    rw [domainEq]
    simpa only [prefixes.snapshot.context_noBV] using
      prefixes.snapshot.domain_tr.closed
  have domainFVars : FVarsIn (· ∈ prefixes.firstParameterΔ.fvars)
      translation.domain := by
    rw [domainEq]
    simpa only [prefixes.parameter_fvars_eq] using
      prefixes.snapshot.domain_tr.fvarsIn
  have consumedClosed : Closed
      (AddInductive.consumeTypeAnnotations translation.domain) 0 := by
    rw [consumedSourceEq]
    simpa only [prefixes.snapshot.context_noBV] using
      prefixes.snapshot.consumed_tr.closed
  have consumedFVars : FVarsIn (· ∈ prefixes.firstParameterΔ.fvars)
      (AddInductive.consumeTypeAnnotations translation.domain) := by
    rw [consumedSourceEq]
    simpa only [prefixes.parameter_fvars_eq] using
      prefixes.snapshot.consumed_tr.fvarsIn
  obtain ⟨baseDomain, baseDomainTr⟩ :=
    currentDomainTr.weakFV'_inv henv prefixes.first_terminal_lift
      prefixes.current_firstTerminal_defeq domainClosed domainFVars
  obtain ⟨baseConsumed, baseConsumedTr⟩ :=
    currentConsumedTr.weakFV'_inv henv prefixes.first_terminal_lift
      prefixes.current_firstTerminal_defeq consumedClosed consumedFVars
  have baseDomainEq : env.IsDefEqU Us.length prefixes.firstParameterΔ.toCtx
      baseDomain prefixes.snapshot.domain' :=
    baseDomainTr.uniqFVars henv parameterContextDefEq firstParameterWF
      snapshotDomainTr
  have baseConsumedEq : env.IsDefEqU Us.length
      prefixes.firstParameterΔ.toCtx baseConsumed
      prefixes.snapshot.consumed' :=
    baseConsumedTr.uniqFVars henv parameterContextDefEq firstParameterWF
      snapshotConsumedTr
  have annotationAtFirst : env.IsDefEqU Us.length
      prefixes.firstParameterΔ.toCtx prefixes.snapshot.domain'
      prefixes.snapshot.consumed' :=
    prefixes.snapshot.annotation_run.isDefEqU.defeqDFC henv.ordered
      (parameterContextDefEq.defeqCtx.symm henv.ordered)
  have annotationAtPrefix : env.IsDefEqU Us.length
      prefixes.firstParameterΔ.toCtx baseDomain baseConsumed :=
    (baseDomainEq.trans henv firstParameterWF.toCtx
      annotationAtFirst).trans henv firstParameterWF.toCtx
        baseConsumedEq.symm
  have annotationAtFirstTerminal :=
    annotationAtPrefix.weak' henv.ordered prefixes.first_terminal_lift.toCtx
  have baseDomainAtFirstTerminal :=
    baseDomainTr.weakFV' henv.ordered prefixes.first_terminal_lift
      firstTerminalWF
  have baseConsumedAtFirstTerminal :=
    baseConsumedTr.weakFV' henv.ordered prefixes.first_terminal_lift
      firstTerminalWF
  have currentDomainEq :=
    currentDomainTr.uniq henv prefixes.current_firstTerminal_defeq
      baseDomainAtFirstTerminal
  have currentConsumedEq :=
    currentConsumedTr.uniq henv prefixes.current_firstTerminal_defeq
      baseConsumedAtFirstTerminal
  have annotationAtCurrent :=
    annotationAtFirstTerminal.defeqDFC henv.ordered
      ((prefixes.current_firstTerminal_defeq.symm henv.ordered).defeqCtx)
  have annotationU : env.IsDefEqU Us.length
      staging.currentRun.context.vlctx.toCtx translation.domain'
      translation.consumed' :=
    (currentDomainEq.trans henv currentWF.toCtx annotationAtCurrent).trans
      henv currentWF.toCtx currentConsumedEq.symm
  have domainType : env.IsType Us.length
      staging.currentRun.context.vlctx.toCtx translation.domain' := by
    simpa only [TypeChecker.VContext.IsType, staging.current_venv,
      staging.current_lparams] using
      translation.domain_type
  obtain ⟨sort, domainHasType⟩ := domainType
  have annotationDef := annotationU.of_l henv currentWF.toCtx domainHasType
  exact ⟨{
    translation := translation
    sort := sort
    annotation_def := by
      simpa only [staging.current_venv, staging.current_lparams] using
        annotationDef }⟩

/-- Theory telescope equality is sufficient to close the translator-facing
parameter-context seam.  The exact candidate shapes and free-variable names
stored in `prefixes` recover `IsDefEqFVars` without requiring dependency-list
identity. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.firstIndexDomainRun_of_parameterContextDefEq
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
    (prefixes : staging.RawFirstIndexPrefixContexts raw)
    (parameterContextDefEq : env.IsDefEqCtx Us.length []
      prefixes.firstParameterΔ.toCtx prefixes.snapshot.Δ.toCtx) :
    Nonempty staging.boundary.IndexDomainRun :=
  staging.firstIndexDomainRun_of_parameterContextDefEqFVars raw prefixes
    (VLCtx.IsDefEqFVars.of_defeqCtx prefixes.first_shape
      prefixes.snapshot_shape prefixes.parameter_fvars_eq
      parameterContextDefEq)

/-- Pointwise equality of the two annotation-consumed parameter telescopes
constructs the exact first validator index run. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.firstIndexDomainRun_of_parameterTelescopeDefEq
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
    (prefixes : staging.RawFirstIndexPrefixContexts raw)
    (parameterTelescopeDefEq : env.TelDefEq Us.length []
      (staging.annotation.firstStoredBinders.take source.nparams)
      (staging.annotation.storedBinders.take source.nparams)) :
    Nonempty staging.boundary.IndexDomainRun := by
  apply staging.firstIndexDomainRun_of_parameterContextDefEq raw prefixes
  simpa only [List.append_nil, prefixes.first_context,
    prefixes.snapshot_context] using parameterTelescopeDefEq.ctx

/-- Construct the exact first second-family index run entirely from the
retained producer and validator evidence. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.firstIndexDomainRun
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
    (context_lctx_eq : context.lctx = {}) :
    Nonempty staging.boundary.IndexDomainRun := by
  obtain ⟨prefixes⟩ :=
    staging.rawFirstIndexPrefixContexts raw context_lctx_eq
  exact staging.firstIndexDomainRun_of_parameterTelescopeDefEq raw prefixes
    (staging.parameterTelescopeDefEq raw prefixes context_lctx_eq)

/-- The second producer annotation spine retains the exact terminal sort
selected by the family normalization run. -/
theorem ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.terminal_sort
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
    ∃ resultLevel,
      annotation.secondCandidate.familyType.type.trace.terminalResult =
        .sort resultLevel := by
  let normalization :=
    produced.execution.eliminationExecution.normalization
  have terminals := normalization.familyTerminals
  rw [← normalization.families.produced.familyTypes_eq] at terminals
  have candidatesEq := annotation.candidates_eq
  change normalization.families.candidates =
    .cons annotation.firstCandidate
      (.cons annotation.secondCandidate annotation.remainingCandidates)
    at candidatesEq
  rw [candidatesEq] at terminals
  simp only [AddInductive.CandidateList.familyTypes] at terminals
  cases terminals with
  | cons firstTerminal remainingTerminals =>
    cases remainingTerminals with
    | cons secondTerminal remainingTerminals =>
      exact ⟨_, secondTerminal⟩

/-- The producer annotation spine stops at the same non-Pi result recorded by
the family normalization run. -/
theorem ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.terminal_notForall
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
    annotation.secondCandidate.familyType.type.trace.terminalResult.isForall =
      false := by
  let normalization :=
    produced.execution.eliminationExecution.normalization
  have terminals := normalization.familyTerminals
  rw [← normalization.families.produced.familyTypes_eq] at terminals
  have candidatesEq := annotation.candidates_eq
  change normalization.families.candidates =
    .cons annotation.firstCandidate
      (.cons annotation.secondCandidate annotation.remainingCandidates)
    at candidatesEq
  rw [candidatesEq] at terminals
  simp only [AddInductive.CandidateList.familyTypes] at terminals
  cases terminals with
  | cons firstTerminal remainingTerminals =>
    cases remainingTerminals with
    | cons secondTerminal remainingTerminals =>
      rw [secondTerminal]
      rfl

/-- Exact producer-owned endpoint package for the second-family index suffix.
The retained prefix context is the original shared-parameter base, while the
alignment records its embedding through every first- and second-family index
local present at the final validator boundary. -/
structure
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.IndexDomainCompletion
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
  prefixes : staging.RawFirstIndexPrefixContexts raw
  chain : staging.boundary.IndexDomainChain
  chain_length : chain.length =
    (staging.annotation.storedBinders.drop source.nparams).length
  alignment : chain.EndpointAlignment env Us
    staging.annotation.terminalRun.context.vlctx prefixes.firstParameterΔ
      staging.annotation.firstTerminalRun.context.vlctx

/-- A completed index chain whose retained endpoint is also the validator's
exact terminal node.  This is the source-order handoff consumed by the next
family. -/
structure
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion
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
    extends staging.IndexDomainCompletion raw where
  terminal : toIndexDomainCompletion.chain.endpoint.boundary.Terminal

/-- The exact verified context at the second family validator's continuation
point. -/
def
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.terminalRun
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
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    (completion : staging.TerminalIndexDomainCompletion raw) :
    TypeChecker.CandidateContextRun staging.position.trace.result.context :=
  completion.chain.endpointContextRun completion.terminal

/-- The exact continuation context retains the semantic environment. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.terminal_venv
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
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    (completion : staging.TerminalIndexDomainCompletion raw) :
    completion.terminalRun.context.venv = env := by
  exact (completion.chain.endpointContextRun_venv completion.terminal).trans
    staging.current_venv

/-- The exact continuation context retains the semantic universe parameters. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.terminal_lparams
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
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    (completion : staging.TerminalIndexDomainCompletion raw) :
    completion.terminalRun.context.lparams = Us := by
  exact
    (completion.chain.endpointContextRun_lparams completion.terminal).trans
      staging.current_lparams

/-- The endpoint alignment is retained after reindexing onto the outer
family continuation context. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.current_reference
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
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    (completion : staging.TerminalIndexDomainCompletion raw) :
    VLCtx.IsDefEq env Us.length completion.terminalRun.context.vlctx
      completion.alignment.reference := by
  have terminalContextEq : completion.terminalRun.context =
      completion.chain.endpoint.contextRun.context := by
    unfold terminalRun TypeChecker.FamilyParameterIndexBoundary.IndexDomainChain.endpointContextRun
    apply TypeChecker.CandidateContextRun.cast_context_context
  rw [terminalContextEq]
  exact completion.alignment.current_reference

/-- Reindex the terminal validator run onto the exact context at which the
retained outer source-order tail begins. -/
def
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.continuationRun
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
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    (completion : staging.TerminalIndexDomainCompletion raw)
    (validation : staging.ValidationContinuation) :
    TypeChecker.CandidateContextRun
      validation.continuation.telescope.result.context := by
  have resultContextEq : staging.position.trace.result.context =
      validation.continuation.telescope.result.context :=
    congrArg (fun position => position.trace.result.context)
      validation.position_eq.symm
  exact resultContextEq ▸ completion.terminalRun

/-- Transporting the run onto the outer tail changes only its dependent
context index. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.continuationRun_context
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
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    (completion : staging.TerminalIndexDomainCompletion raw)
    (validation : staging.ValidationContinuation) :
    (completion.continuationRun validation).context =
      completion.terminalRun.context := by
  unfold continuationRun
  apply TypeChecker.CandidateContextRun.cast_context_context

/-- The source-order continuation retains the semantic environment. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.continuation_venv
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
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    (completion : staging.TerminalIndexDomainCompletion raw)
    (validation : staging.ValidationContinuation) :
    (completion.continuationRun validation).context.venv = env := by
  rw [completion.continuationRun_context validation]
  exact completion.terminal_venv

/-- The source-order continuation retains the semantic universe parameters. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.continuation_lparams
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
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    (completion : staging.TerminalIndexDomainCompletion raw)
    (validation : staging.ValidationContinuation) :
    (completion.continuationRun validation).context.lparams = Us := by
  rw [completion.continuationRun_context validation]
  exact completion.terminal_lparams

/-- The aligned Theory endpoint is preserved at the exact next-family
boundary selected from the outer validation trace. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.continuation_reference
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
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    (completion : staging.TerminalIndexDomainCompletion raw)
    (validation : staging.ValidationContinuation) :
    VLCtx.IsDefEq env Us.length
      (completion.continuationRun validation).context.vlctx
      completion.alignment.reference := by
  rw [completion.continuationRun_context validation]
  exact completion.current_reference

/-- The exact suffix after the completed second family, pairing the retained
outer validator tail with the matching dependent semantic family tail and the
verified terminal context that connects them. -/
structure
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor
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
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    (completion : staging.TerminalIndexDomainCompletion raw) where
  validation : staging.ValidationContinuation
  cursor : CandidateBlockLaterFamilyValidationCursor env blockEnv Us
    source.nparams (firstSource :: secondSource :: remainingSources)
    staging.annotation.remainingCandidates
    staging.annotation.remainingRaws validation.continuation.tail
  semantics_eq : cursor.semantics =
    staging.annotation.remainingSemantics
  cursor_fuel_eq :
    validation.continuation.telescope.result.context.fuel = context.fuel
  parameterSources_eq_boundary : cursor.parameterSources =
    staging.boundary.parameters.map Prod.fst
  context_eq_terminal : cursor.contextRun.context =
    completion.terminalRun.context
  firstTerminal_find : ∀ {fv : FVarId} {decl : LocalDecl},
    staging.annotation.firstCandidate.familyType.type.trace.terminalContext.lctx.find?
          fv = some decl →
      validation.continuation.telescope.result.context.lctx.find? fv =
        some decl

/-- Construct the source-order cursor at the exact terminal context reached
after the second family's complete index telescope. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.remainingFamilyValidationCursor
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
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    (completion : staging.TerminalIndexDomainCompletion raw)
    (context_lctx_eq : context.lctx = {}) :
    Nonempty completion.RemainingFamilyValidationCursor := by
  obtain ⟨validation⟩ := staging.validationContinuation
  have dIdxEq :=
    AddInductive.FamilyParameterComparisonBlockTrace.secondContinuation?_dIdx
      validation.selected
  obtain ⟨_, _, secondSelected⟩ :=
    AddInductive.FamilyParameterComparisonBlockTrace.exists_predecessor_of_secondContinuation?
      validation.selected
  have continuationLater :
      validation.continuation.stats.indConsts.isEmpty = false := by
    calc
      validation.continuation.stats.indConsts.isEmpty =
          staging.position.stats.indConsts.isEmpty := by
        simpa only [
          AddInductive.FamilyParameterComparisonBlockTrace.FamilyContinuation.position]
          using congrArg
            (fun position => position.stats.indConsts.isEmpty)
            validation.position_eq
      _ = false := staging.position_later
  have continuationParams :
      validation.continuation.stats.params.size = source.nparams := by
    calc
      validation.continuation.stats.params.size =
          staging.position.stats.params.size := by
        simpa only [
          AddInductive.FamilyParameterComparisonBlockTrace.FamilyContinuation.position]
          using congrArg (fun position => position.stats.params.size)
            validation.position_eq
      _ = source.nparams := staging.position_params_size
  have continuationStatsEq : validation.continuation.stats =
      staging.position.stats := by
    simpa only [
      AddInductive.FamilyParameterComparisonBlockTrace.FamilyContinuation.position]
      using congrArg
        AddInductive.FamilyParameterComparisonBlockTrace.FamilyTelescopePosition.stats
        validation.position_eq
  have continuationContextEq : validation.continuation.context =
      staging.position.context := by
    simpa only [
      AddInductive.FamilyParameterComparisonBlockTrace.FamilyContinuation.position]
      using congrArg
        AddInductive.FamilyParameterComparisonBlockTrace.FamilyTelescopePosition.context
        validation.position_eq
  have continuationLocalState :
      TypeChecker.FamilyParameterLocalState validation.continuation.stats
        validation.continuation.context := by
    rw [continuationStatsEq, continuationContextEq]
    exact staging.boundary.localState
  have laterInvariant :=
    AddInductive.FamilyParameterComparisonBlockTrace.headContinuation?_laterInvariant
      secondSelected continuationLater continuationParams
  have continuationContextFuel : validation.continuation.context.fuel =
      staging.position.context.fuel := by
    simpa only [
      AddInductive.FamilyParameterComparisonBlockTrace.FamilyContinuation.position]
      using congrArg (fun position => position.context.fuel)
        validation.position_eq
  have validationResultContextEq : staging.position.trace.result.context =
      validation.continuation.telescope.result.context :=
    congrArg (fun position => position.trace.result.context)
      validation.position_eq.symm
  have positionFirstTerminal : staging.position.context =
      staging.annotation.firstCandidate.familyType.type.trace.terminalContext :=
    staging.position_context_eq_firstTerminal context_lctx_eq
  refine ⟨{
    validation := validation
    cursor := {
      sourceSuffix_eq := ?_
      semantics := staging.annotation.remainingSemantics
      contextRun := completion.continuationRun validation
      venv_eq := completion.continuation_venv validation
      lparams_eq := completion.continuation_lparams validation
      current_localState :=
        AddInductive.FamilyParameterComparisonBlockTrace.headContinuation?_nextLocalState
          secondSelected continuationLocalState continuationLater
          continuationParams
      parameterSources := staging.boundary.parameters.map Prod.fst
      current_parameterSources_eq := by
        calc
          validation.continuation.nextStats.params.toList =
              validation.continuation.stats.params.toList :=
            congrArg Array.toList
              (AddInductive.FamilyParameterComparisonBlockTrace.headContinuation?_nextParams_eq
                secondSelected continuationLater)
          _ = staging.position.stats.params.toList :=
            congrArg (fun currentStats => currentStats.params.toList)
              continuationStatsEq
          _ = staging.boundary.parameters.map Prod.fst :=
            staging.parameterSources_eq_positionParams.symm
      current_indConsts_nonempty :=
        laterInvariant.next_indConsts_nonempty
      current_params_size := laterInvariant.next_params_size }
    semantics_eq := rfl
    cursor_fuel_eq := by
      calc
        validation.continuation.telescope.result.context.fuel =
            validation.continuation.context.fuel :=
          validation.continuation.telescope.result_context_fuel
        _ = staging.position.context.fuel := continuationContextFuel
        _ = context.fuel := staging.position_fuel_eq
    parameterSources_eq_boundary := rfl
    context_eq_terminal :=
      completion.continuationRun_context validation
    firstTerminal_find := by
      intro fv decl found
      rw [← validationResultContextEq]
      exact staging.position.trace.result_findOld
        staging.boundary.localState.localContext (by
          rw [positionFirstTerminal]
          exact found) }⟩
  simp [dIdxEq]

/-- The cursor is based on the same verified context as the completed second
family endpoint; only its dependent outer-trace index has changed. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.contextRun_eq_terminal
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
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    {completion : staging.TerminalIndexDomainCompletion raw}
    (cursor : completion.RemainingFamilyValidationCursor) :
    cursor.cursor.contextRun.context = completion.terminalRun.context :=
  cursor.context_eq_terminal

/-- The verified context stored by the recursive cursor retains the original
producer fuel configuration. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.contextRun_fuel_eq
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
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    {completion : staging.TerminalIndexDomainCompletion raw}
    (cursor : completion.RemainingFamilyValidationCursor) :
    cursor.cursor.contextRun.context.fuel = context.fuel := by
  rw [TypeChecker.CandidateContextRun.context_fuel]
  exact cursor.cursor_fuel_eq

/-- The parameter source inventory retained by the completed second-family
boundary is exactly the producer-allocated prefix of the first family. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.parameterSources_eq_firstParameterList
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
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    (completion : staging.TerminalIndexDomainCompletion raw) :
    staging.boundary.parameters.map Prod.fst =
      staging.annotation.firstCandidate.familyType.type.trace.parameterList
        source.nparams := by
  have reversed : (staging.boundary.parameters.map Prod.fst).reverse =
      (staging.annotation.firstCandidate.familyType.type.trace.parameterList
        source.nparams).reverse := by
    calc
      (staging.boundary.parameters.map Prod.fst).reverse =
          completion.prefixes.snapshot.Δ.fvars.map Expr.fvar :=
        completion.prefixes.snapshot_fvars.symm
      _ = completion.prefixes.firstParameterΔ.fvars.map Expr.fvar :=
        congrArg (List.map Expr.fvar)
          completion.prefixes.parameter_fvars_eq.symm
      _ = (staging.annotation.firstCandidate.familyType.type.trace
            |>.parameterList source.nparams).reverse :=
        completion.prefixes.first_fvars
  exact List.reverse_inj.1 reversed

/-- Every remaining-family cursor keeps that same first-family parameter
source inventory across outer-family advancement. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.parameterSources_eq_firstParameterList
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
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    {completion : staging.TerminalIndexDomainCompletion raw}
    (cursor : completion.RemainingFamilyValidationCursor) :
    cursor.cursor.parameterSources =
      staging.annotation.firstCandidate.familyType.type.trace.parameterList
        source.nparams :=
  cursor.parameterSources_eq_boundary.trans
    completion.parameterSources_eq_firstParameterList

/-- Reindex the producer's complete generation-spine suffix onto the exact
semantic proof object stored in the recursive validation cursor. -/
def
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.generationShapes
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
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    {completion : staging.TerminalIndexDomainCompletion raw}
    (cursor : completion.RemainingFamilyValidationCursor) :
    CandidateBlockFamilySemanticGenerationShapeList source env blockEnv Us
      cursor.cursor.semantics := by
  rw [cursor.semantics_eq]
  exact staging.annotation.remainingShapes

/-- Construct the complete source-ordered annotation spine for every family
remaining after the second-family terminal handoff. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.annotationSpines
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
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    {completion : staging.TerminalIndexDomainCompletion raw}
    (cursor : completion.RemainingFamilyValidationCursor) :
    Nonempty (CandidateBlockFamilyAnnotationSpineList source env blockEnv Us
      cursor.cursor.semantics cursor.generationShapes) :=
  CandidateBlockFamilyAnnotationSpineList.exists cursor.cursor.semantics
    cursor.generationShapes
    staging.annotation.remainingValidationAnnotations

/-- Recursion-ready state for an arbitrary suffix of the later families.
Besides the dependent validator/semantic cursor, it retains every invariant
needed to interpret the next family without reselecting a context, candidate,
raw family, or shared-parameter reference. -/
structure
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.LaterFamilyIterationCursor
    {source : VInductDecl}
    {firstSource secondSource : InductiveType}
    {allLaterSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: allLaterSources) numNested isUnsafe
      context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    (completion : staging.TerminalIndexDomainCompletion raw)
    {remainingSources : List InductiveType}
    (candidates : AddInductive.CandidateList AddInductive.CandidateFamily
      remainingSources)
    (raws : List VInductiveType)
    {dIdx : Nat} {stats : AddInductive.InductiveStats}
    {candidateContext : AddInductive.Context}
    (trace : AddInductive.FamilyParameterComparisonBlockTrace source.nparams
      (firstSource :: secondSource :: allLaterSources).toArray dIdx stats
      candidateContext) where
  cursor : CandidateBlockLaterFamilyValidationCursor env blockEnv Us
    source.nparams (firstSource :: secondSource :: allLaterSources)
    candidates raws trace
  validation : CandidateFamilyValidationAnnotationList
    { context with lctx := {} } candidates
  parameterSpines : AddInductive.CandidateFamilyParameterSpineList
    source.nparams candidates
  generationShapes : CandidateBlockFamilySemanticGenerationShapeList source
    env blockEnv Us cursor.semantics
  annotations : CandidateBlockFamilyAnnotationSpineList source env blockEnv Us
    cursor.semantics generationShapes
  parameterSources_eq_firstParameterList : cursor.parameterSources =
    staging.annotation.firstCandidate.familyType.type.trace.parameterList
      source.nparams
  candidate_fuel_eq : candidateContext.fuel = context.fuel
  firstTerminal_find : ∀ {fv : FVarId} {decl : LocalDecl},
    staging.annotation.firstCandidate.familyType.type.trace.terminalContext.lctx.find?
          fv = some decl →
      candidateContext.lctx.find? fv = some decl
  reference : VLCtx
  rootLift : Lift
  originLift : Lift
  root_reference_lift : VLCtx.FVLift'
    completion.prefixes.firstParameterΔ reference 0 rootLift 0
  origin_reference_lift : VLCtx.FVLift'
    staging.annotation.firstTerminalRun.context.vlctx reference 0
      originLift 0
  current_reference : VLCtx.IsDefEq env Us.length
    cursor.contextRun.context.vlctx reference

/-- Assemble the initial later-family iteration state from one exact
annotation spine.  Keeping the constructor as data exposes the semantic
suffix selected by the completed second-family handoff. -/
def
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.iterationCursorExact
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
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    {completion : staging.TerminalIndexDomainCompletion raw}
    (cursor : completion.RemainingFamilyValidationCursor)
    (annotations : CandidateBlockFamilyAnnotationSpineList source env
      blockEnv Us cursor.cursor.semantics cursor.generationShapes) :
    completion.LaterFamilyIterationCursor
      staging.annotation.remainingCandidates staging.annotation.remainingRaws
      cursor.validation.continuation.tail :=
  {
    cursor := cursor.cursor
    validation := staging.annotation.remainingValidationAnnotations
    parameterSpines := staging.annotation.remainingParameterSpines
    generationShapes := cursor.generationShapes
    annotations := annotations
    parameterSources_eq_firstParameterList :=
      cursor.parameterSources_eq_firstParameterList
    candidate_fuel_eq := cursor.cursor_fuel_eq
    firstTerminal_find := cursor.firstTerminal_find
    reference := completion.alignment.reference
    rootLift := completion.alignment.rootLift
    originLift := completion.alignment.originLift
    root_reference_lift := completion.alignment.root_reference_lift
    origin_reference_lift := completion.alignment.origin_reference_lift
    current_reference := by
      rw [cursor.context_eq_terminal]
      exact completion.current_reference }

/-- The exact initial iteration state retains precisely the remaining semantic
suffix selected by the second-family annotation. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.iterationCursorExact_semantics
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
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    {completion : staging.TerminalIndexDomainCompletion raw}
    (cursor : completion.RemainingFamilyValidationCursor)
    (annotations : CandidateBlockFamilyAnnotationSpineList source env
      blockEnv Us cursor.cursor.semantics cursor.generationShapes) :
    (cursor.iterationCursorExact annotations).cursor.semantics =
      staging.annotation.remainingSemantics :=
  cursor.semantics_eq

/-- Package the exact suffix handed off by the completed second family as
the initial recursion-ready later-family state. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.iterationCursor
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
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    {completion : staging.TerminalIndexDomainCompletion raw}
    (cursor : completion.RemainingFamilyValidationCursor) :
    Nonempty (completion.LaterFamilyIterationCursor
      staging.annotation.remainingCandidates staging.annotation.remainingRaws
      cursor.validation.continuation.tail) := by
  obtain ⟨annotations⟩ := cursor.annotationSpines
  exact ⟨cursor.iterationCursorExact annotations⟩

namespace
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.LaterFamilyIterationCursor

variable {source : VInductDecl}
  {firstSource secondSource : InductiveType}
  {allLaterSources : List InductiveType}
  {numNested : Nat} {isUnsafe : Bool}
  {context : AddInductive.Context}
  {produced : ProducedBlockRecursorShapeCandidate source
    (firstSource :: secondSource :: allLaterSources) numNested isUnsafe
    context}
  {env blockEnv : VEnv} {Us : List Name}
  {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
    produced.candidate source}
  {staging : produced.SecondFamilyIndexStaging semantic}
  {raw : staging.annotation.RawFirstIndexDomain}
  {completion : staging.TerminalIndexDomainCompletion raw}
  {nextSource : InductiveType} {laterSources : List InductiveType}
  {candidates : AddInductive.CandidateList AddInductive.CandidateFamily
    (nextSource :: laterSources)}
  {raws : List VInductiveType}
  {dIdx : Nat} {stats : AddInductive.InductiveStats}
  {candidateContext : AddInductive.Context}
  {trace : AddInductive.FamilyParameterComparisonBlockTrace source.nparams
    (firstSource :: secondSource :: allLaterSources).toArray dIdx stats
    candidateContext}

/-- Canonical head staging for an arbitrary nonempty recursive later-family
state. -/
structure HeadStaging
    (iteration : completion.LaterFamilyIterationCursor candidates raws trace)
    where
  continuation :
    AddInductive.FamilyParameterComparisonBlockTrace.FamilyContinuation
      source.nparams
      (firstSource :: secondSource :: allLaterSources).toArray
  selected : trace.headContinuation? = some continuation
  invariant : continuation.LaterInvariant

/-- Select the exact head continuation of a nonempty recursive state. -/
theorem headStaging
    (iteration : completion.LaterFamilyIterationCursor candidates raws trace) :
    Nonempty iteration.HeadStaging := by
  obtain ⟨continuation, selected, invariant⟩ :=
    iteration.cursor.headContinuation (by simp)
  exact ⟨⟨continuation, selected, invariant⟩⟩

/-- Canonical semantic family at the recursive state head. -/
def HeadStaging.position
    {iteration : completion.LaterFamilyIterationCursor candidates raws trace}
    (_head : iteration.HeadStaging) :=
  iteration.cursor.semantics.headPosition

/-- Exact verified reader context at the recursive state head. -/
def HeadStaging.currentRun
    {iteration : completion.LaterFamilyIterationCursor candidates raws trace}
    (head : iteration.HeadStaging) :
    TypeChecker.CandidateContextRun head.continuation.context :=
  iteration.cursor.headContextRun head.continuation head.selected

/-- The recursive head reader context has the producer-recorded WHNF depth. -/
theorem HeadStaging.whnfDepth
    {iteration : completion.LaterFamilyIterationCursor candidates raws trace}
    (head : iteration.HeadStaging) :
    head.continuation.context.fuel.recDepth =
      head.position.semantic.type.whnfFuel + 1 := by
  calc
    head.continuation.context.fuel.recDepth =
        candidateContext.fuel.recDepth :=
      congrArg (fun currentContext => currentContext.fuel.recDepth)
        (AddInductive.FamilyParameterComparisonBlockTrace.headContinuation?_context
          head.selected)
    _ = context.fuel.recDepth :=
      congrArg (fun fuel => fuel.recDepth) iteration.candidate_fuel_eq
    _ = ({ context with lctx := {} } : AddInductive.Context).fuel.recDepth :=
      rfl
    _ = candidates.head.familyType.type.context.fuel.recDepth :=
      (congrArg (fun currentContext => currentContext.fuel.recDepth)
        iteration.validation.head_context_eq).symm
    _ = head.position.semantic.type.whnfFuel + 1 :=
      head.position.semantic.type.whnfDepth

/-- Execute the retained root WHNF observation for an arbitrary recursive
head. -/
theorem HeadStaging.rootWhnf
    {iteration : completion.LaterFamilyIterationCursor candidates raws trace}
    (head : iteration.HeadStaging) :
    let position := iteration.cursor.semantics.headPosition
    let currentRun := iteration.cursor.headContextRun head.continuation
      head.selected
    ∃ root', currentRun.context.TrExprS head.continuation.source root' ∧
      Nonempty (TypeChecker.WhnfRun currentRun.context.venv
        currentRun.context.lparams currentRun.context.vlctx nextSource.type
        head.continuation.source position.raw.type root') := by
  let position := iteration.cursor.semantics.headPosition
  let currentRun := iteration.cursor.headContextRun head.continuation
    head.selected
  have sourceTr : currentRun.context.TrExprS nextSource.type
      position.raw.type := by
    rw [iteration.cursor.headContextRun_context head.continuation
      head.selected]
    exact iteration.cursor.headSourceTranslation
  exact TypeChecker.WhnfRun.exists_ofCandidateStep
    ⟨head.continuation.context, nextSource.type, head.continuation.source⟩
    (iteration.cursor.headRootWhnf head.continuation head.selected)
    currentRun position.raw.type sourceTr position.semantic.type.whnfFuel
    head.whnfDepth

/-- Producer-owned shared-parameter boundary at an arbitrary recursive
head. -/
structure HeadParameterBoundary
    {iteration : completion.LaterFamilyIterationCursor candidates raws trace}
    (head : iteration.HeadStaging) where
  root : VExpr
  root_tr : head.currentRun.context.TrExprS head.continuation.source root
  rawRoot_def : head.currentRun.context.venv.IsDefEqU
    head.currentRun.context.lparams.length
    head.currentRun.context.vlctx.toCtx head.position.raw.type root
  comparisonRuns : ∀ step ∈ head.continuation.telescope.comparisons,
    TypeChecker.FamilyComparisonSemanticRun step
  boundary : TypeChecker.FamilyParameterIndexBoundary
    head.continuation.telescope head.currentRun
  parameterSpine : TypeChecker.FamilyParameterSemanticSpine
    head.currentRun.context.venv head.currentRun.context.lparams.length
    head.currentRun.context.vlctx.toCtx root
    (boundary.parameters.map Prod.snd) boundary.source'

/-- Interpret the exact shared-parameter prefix at an arbitrary recursive
head. -/
theorem HeadStaging.parameterBoundary
    {iteration : completion.LaterFamilyIterationCursor candidates raws trace}
    (head : iteration.HeadStaging) :
    Nonempty (HeadParameterBoundary head) := by
  obtain ⟨root, rootTr, ⟨rootRun⟩⟩ := head.rootWhnf
  obtain ⟨comparisonRuns, boundary, parameterSpine⟩ :=
    TypeChecker.familyTypeParameterComparison_semanticSpine_of_later
      head.continuation.telescope
      head.invariant.current_indConsts_nonempty
      head.invariant.current_params_size
      (iteration.cursor.headLocalState head.continuation head.selected)
      head.currentRun root rootTr head.position.semantic.type.whnfFuel
      head.whnfDepth
  exact ⟨{
    root := root
    root_tr := rootTr
    rawRoot_def := rootRun.isDefEqU
    comparisonRuns := comparisonRuns
    boundary := boundary
    parameterSpine := parameterSpine }⟩

/-- The recursive candidate exposes at least its complete parameter prefix. -/
theorem HeadStaging.nparams_le_spineLength
    {iteration : completion.LaterFamilyIterationCursor candidates raws trace}
    (_head : iteration.HeadStaging) :
    source.nparams ≤ candidates.head.familyType.type.trace.spineLength :=
  iteration.parameterSpines.head

/-- The first and current recursive candidates share the producer root
context. -/
theorem HeadStaging.firstCandidate_context_eq
    {iteration : completion.LaterFamilyIterationCursor candidates raws trace}
    (_head : iteration.HeadStaging) :
    staging.annotation.firstCandidate.familyType.type.context =
      candidates.head.familyType.type.context :=
  (staging.annotation.candidate_context_eq.trans
      staging.annotation.second_candidate_context_eq).trans
    iteration.validation.head_context_eq.symm

/-- Every recursive family allocates the first family's exact parameter free
variables. -/
theorem HeadStaging.parameterLists_eq
    {iteration : completion.LaterFamilyIterationCursor candidates raws trace}
    (head : iteration.HeadStaging)
    (context_lctx_eq : context.lctx = {}) :
    staging.annotation.firstCandidate.familyType.type.trace.parameterList
        source.nparams =
      candidates.head.familyType.type.trace.parameterList source.nparams :=
  AddInductive.CandidateExprTrace.parameterList_eq_of_ngen_eq
    staging.annotation.firstCandidate.familyType.type.trace
    candidates.head.familyType.type.trace
    (congrArg AddInductive.Context.ngen head.firstCandidate_context_eq)
    (staging.annotation.first_nparams_le_spineLength context_lctx_eq)
    head.nparams_le_spineLength

/-- The recursive validator boundary names the current candidate's exact
parameter prefix. -/
theorem HeadParameterBoundary.parameterSources_eq_candidateParameterList
    {iteration : completion.LaterFamilyIterationCursor candidates raws trace}
    {head : iteration.HeadStaging}
    (parameter : HeadParameterBoundary head)
    (context_lctx_eq : context.lctx = {}) :
    parameter.boundary.parameters.map Prod.fst =
      candidates.head.familyType.type.trace.parameterList source.nparams := by
  calc
    parameter.boundary.parameters.map Prod.fst =
        head.continuation.stats.params.toList := by
      simpa using parameter.boundary.parameter_sources_eq
    _ = iteration.cursor.parameterSources := by
      rw [AddInductive.FamilyParameterComparisonBlockTrace.headContinuation?_stats
        head.selected]
      exact iteration.cursor.current_parameterSources_eq
    _ = staging.annotation.firstCandidate.familyType.type.trace.parameterList
          source.nparams := iteration.parameterSources_eq_firstParameterList
    _ = candidates.head.familyType.type.trace.parameterList source.nparams :=
      head.parameterLists_eq context_lctx_eq

/-- The recursive validator boundary retains the first candidate's exact
parameter prefix. -/
theorem HeadParameterBoundary.parameterSources_eq_firstParameterList
    {iteration : completion.LaterFamilyIterationCursor candidates raws trace}
    {head : iteration.HeadStaging}
    (parameter : HeadParameterBoundary head) :
    parameter.boundary.parameters.map Prod.fst =
      staging.annotation.firstCandidate.familyType.type.trace.parameterList
        source.nparams := by
  calc
    parameter.boundary.parameters.map Prod.fst =
        head.continuation.stats.params.toList := by
      simpa using parameter.boundary.parameter_sources_eq
    _ = iteration.cursor.parameterSources := by
      rw [AddInductive.FamilyParameterComparisonBlockTrace.headContinuation?_stats
        head.selected]
      exact iteration.cursor.current_parameterSources_eq
    _ = staging.annotation.firstCandidate.familyType.type.trace.parameterList
          source.nparams := iteration.parameterSources_eq_firstParameterList

/-- Terminal-inclusive producer suffix at an arbitrary recursive parameter
boundary. -/
structure HeadCandidateParameterSuffix
    {iteration : completion.LaterFamilyIterationCursor candidates raws trace}
    (head : iteration.HeadStaging) where
  position : candidates.head.familyType.type.trace.MainSpineAt source.nparams
  suffix : iteration.annotations.head.annotation_spine.MainPositionSuffix
    position

/-- Select the recursive candidate's literal parameter-boundary suffix. -/
theorem HeadStaging.candidateParameterSuffix
    {iteration : completion.LaterFamilyIterationCursor candidates raws trace}
    (head : iteration.HeadStaging) :
    Nonempty (HeadCandidateParameterSuffix head) := by
  obtain ⟨position⟩ :=
    AddInductive.CandidateExprTrace.mainSpineAt
      head.nparams_le_spineLength
  obtain ⟨resultLevel, terminalEq⟩ := iteration.validation.head_terminal
  obtain ⟨suffix⟩ :=
    iteration.annotations.head.annotation_spine.mainPositionSuffix .nil
      iteration.generationShapes.head.storedSpine
      iteration.annotations.head.validation_annotations terminalEq position
  exact ⟨⟨position, suffix⟩⟩

/-- The retained recursive comparisons construct the exact shared-parameter
telescope equality against the first family. -/
theorem HeadStaging.parameterTelescopeDefEq
    {iteration : completion.LaterFamilyIterationCursor candidates raws trace}
    (head : iteration.HeadStaging)
    (parameter : HeadParameterBoundary head)
    (candidate : HeadCandidateParameterSuffix head)
    (context_lctx_eq : context.lctx = {}) :
    TypeChecker.TelDefEqEvidence env Us.length []
      (staging.annotation.firstStoredBinders.take source.nparams)
      (iteration.annotations.head.storedBinders.take source.nparams) := by
  have currentVenv : head.currentRun.context.venv = env :=
    iteration.cursor.headContextRun_venv head.continuation head.selected
  have currentLparams : head.currentRun.context.lparams = Us :=
    iteration.cursor.headContextRun_lparams head.continuation head.selected
  have firstRootLctx :
      staging.annotation.firstCandidate.familyType.type.context.lctx =
        ({} : LocalContext) := by
    calc
      staging.annotation.firstCandidate.familyType.type.context.lctx =
          candidates.head.familyType.type.context.lctx :=
        congrArg AddInductive.Context.lctx head.firstCandidate_context_eq
      _ = ({ context with lctx := {} } : AddInductive.Context).lctx :=
        congrArg AddInductive.Context.lctx
          iteration.validation.head_context_eq
      _ = {} := rfl
  have firstTerminalFind : ∀ {fv : FVarId} {decl : LocalDecl},
      staging.annotation.firstCandidate.familyType.type.trace.terminalContext.lctx.find?
          fv = some decl →
        head.continuation.context.lctx.find? fv = some decl := by
    intro fv decl found
    rw [AddInductive.FamilyParameterComparisonBlockTrace.headContinuation?_context
      head.selected]
    exact iteration.firstTerminal_find found
  have currentReference : VLCtx.IsDefEq env Us.length
      head.currentRun.context.vlctx iteration.reference := by
    change VLCtx.IsDefEq env Us.length
      (iteration.cursor.headContextRun head.continuation
        head.selected).context.vlctx iteration.reference
    rw [iteration.cursor.headContextRun_context head.continuation
      head.selected]
    exact iteration.current_reference
  have validatorCandidateRoot : 0 < source.nparams →
      head.continuation.source =
        candidates.head.familyType.type.trace.rootWhnf := by
    intro positive
    have candidateIsForall : nextSource.type.isForall = true :=
      candidate.position.traceSource_isForall positive
        iteration.generationShapes.head.storedSpine
    have validatorRootEq : head.continuation.source = nextSource.type :=
      AddInductive.CandidateWhnfStep.result_eq_of_source_isForall
        (iteration.cursor.headRootWhnf head.continuation head.selected)
        head.position.semantic.type.whnfFuel head.whnfDepth
        candidateIsForall
    have candidateRootEq : candidates.head.familyType.type.trace.rootWhnf =
        nextSource.type :=
      AddInductive.CandidateWhnfStep.result_eq_of_source_isForall
        candidates.head.familyType.type.trace.rootWhnf_valid
        head.position.semantic.type.whnfFuel
        head.position.semantic.type.whnfDepth candidateIsForall
    exact validatorRootEq.trans candidateRootEq.symm
  have evidence := sharedParameterTelescopeDefEqAux
    parameter.boundary.prefix_path parameter.boundary.params_size
    parameter.boundary.localState head.currentRun currentVenv currentLparams
    parameter.root_tr head.position.semantic.type.whnfFuel head.whnfDepth
    staging.annotation.first_annotation_spine
    staging.annotation.first_validation_annotations
    (TypeChecker.CandidateLocalContextRun.empty _ firstRootLctx)
    firstTerminalFind iteration.annotations.head.annotation_spine
    iteration.annotations.head.validation_annotations candidate.position
    iteration.generationShapes.head.storedSpine
    head.position.semantic.type.whnfDepth validatorCandidateRoot
    parameter.parameterSources_eq_firstParameterList
    (parameter.parameterSources_eq_candidateParameterList context_lctx_eq)
    (.nil) iteration.origin_reference_lift currentReference
  simpa only [VLCtx.toCtx] using evidence

/-- Relocate the annotation-consumed shared-parameter equality onto the
actual normalized views of the first family and an arbitrary recursive
family.  Both sides pass through their exact raw telescope; no kernel
definitional equality is reinterpreted as syntactic equality. -/
theorem HeadStaging.viewParameterTelescopeDefEq
    {iteration : completion.LaterFamilyIterationCursor candidates raws trace}
    (head : iteration.HeadStaging)
    (parameter : HeadParameterBoundary head)
    (candidate : HeadCandidateParameterSuffix head)
    (context_lctx_eq : context.lctx = {}) :
    TypeChecker.TelDefEqEvidence env Us.length []
      (VExpr.telN source.nparams
        staging.annotation.firstSemantic.type.view)
      (VExpr.telN source.nparams head.position.semantic.type.view) := by
  have currentVenv : head.currentRun.context.venv = env :=
    iteration.cursor.headContextRun_venv head.continuation head.selected
  have henv : VEnv.WF env := by
    simpa only [currentVenv] using head.currentRun.context.Ewf
  have firstBound :=
    staging.annotation.first_nparams_le_spineLength context_lctx_eq
  have firstRawBound : source.nparams ≤
      (VInductDecl.ctorFields staging.annotation.firstRaw.type).length := by
    rw [← staging.annotation.firstSpineLength_eq]
    exact firstBound
  have firstRawStored :=
    staging.annotation.firstTelescope.take source.nparams
  rw [telN_take_of_le staging.annotation.firstRaw.type firstRawBound]
    at firstRawStored
  obtain ⟨firstInferred, firstRecursive⟩ :=
    staging.annotation.firstSemantic.type.recursive
  obtain ⟨firstResultType, firstFullView⟩ :=
    firstRecursive.spineEvidence staging.annotation.first_stored_spine
  have firstRawView := firstFullView.telescope.take source.nparams
  rw [telN_take_of_le staging.annotation.firstRaw.type firstBound,
    telN_take_of_le staging.annotation.firstSemantic.type.view firstBound]
    at firstRawView
  have firstStoredView : TypeChecker.TelDefEqEvidence env Us.length []
      (staging.annotation.firstStoredBinders.take source.nparams)
      (VExpr.telN source.nparams
        staging.annotation.firstSemantic.type.view) :=
    (firstRawStored.symm henv trivial).trans henv trivial firstRawView
  have currentRawBound : source.nparams ≤
      (VInductDecl.ctorFields
        iteration.cursor.semantics.headPosition.raw.type).length := by
    rw [← iteration.generationShapes.head.spineLength_eq_ctorFields]
    exact head.nparams_le_spineLength
  have currentRawStored :=
    iteration.annotations.head.telescope.take source.nparams
  rw [telN_take_of_le
    iteration.cursor.semantics.headPosition.raw.type currentRawBound]
    at currentRawStored
  obtain ⟨currentResultType, currentFullView⟩ :=
    iteration.annotations.head.recursive.spineEvidence
      iteration.generationShapes.head.storedSpine
  have currentRawView := currentFullView.telescope.take source.nparams
  rw [telN_take_of_le iteration.cursor.semantics.headPosition.raw.type
      head.nparams_le_spineLength,
    telN_take_of_le iteration.cursor.semantics.headPosition.semantic.type.view
      head.nparams_le_spineLength] at currentRawView
  have currentStoredView : TypeChecker.TelDefEqEvidence env Us.length []
      (iteration.annotations.head.storedBinders.take source.nparams)
      (VExpr.telN source.nparams
        iteration.cursor.semantics.headPosition.semantic.type.view) :=
    (currentRawStored.symm henv trivial).trans henv trivial currentRawView
  have storedParameters :=
    head.parameterTelescopeDefEq parameter candidate context_lctx_eq
  change TypeChecker.TelDefEqEvidence env Us.length []
    (VExpr.telN source.nparams staging.annotation.firstSemantic.type.view)
    (VExpr.telN source.nparams
      iteration.cursor.semantics.headPosition.semantic.type.view)
  exact ((firstStoredView.symm henv trivial).trans henv trivial
      storedParameters).trans henv trivial currentStoredView

/-- Uniform completed index suffix at an arbitrary recursive family head. -/
structure HeadDomainCompletion
    {iteration : completion.LaterFamilyIterationCursor candidates raws trace}
    (head : iteration.HeadStaging)
    (parameter : HeadParameterBoundary head) where
  candidate : HeadCandidateParameterSuffix head
  chain : parameter.boundary.IndexDomainChain
  chain_length : chain.length =
    (iteration.annotations.head.storedBinders.drop source.nparams).length
  alignment : chain.EndpointAlignment env Us
    iteration.annotations.head.terminalRun.context.vlctx
    completion.prefixes.firstParameterΔ
    staging.annotation.firstTerminalRun.context.vlctx

/-- Complete an arbitrary recursive head, splitting faithfully between a
genuine first index and the parameter-terminal endpoint. -/
theorem HeadStaging.domainCompletion
    {iteration : completion.LaterFamilyIterationCursor candidates raws trace}
    (head : iteration.HeadStaging)
    (parameter : HeadParameterBoundary head)
    (context_lctx_eq : context.lctx = {}) :
    Nonempty (HeadDomainCompletion head parameter) := by
  obtain ⟨candidate⟩ := head.candidateParameterSuffix
  rcases Nat.lt_or_eq_of_le head.nparams_le_spineLength with hasIndex |
      noIndices
  · obtain ⟨position⟩ :=
      AddInductive.CandidateExprTrace.annotationAt
        iteration.annotations.head.validation_annotations hasIndex
    obtain ⟨resultLevel, terminalEq⟩ := iteration.validation.head_terminal
    obtain ⟨suffix⟩ :=
      iteration.annotations.head.annotation_spine.positionSuffix .nil
        iteration.generationShapes.head.storedSpine
        iteration.annotations.head.validation_annotations terminalEq position
    have currentVenv : head.currentRun.context.venv = env :=
      iteration.cursor.headContextRun_venv head.continuation head.selected
    have currentLparams : head.currentRun.context.lparams = Us :=
      iteration.cursor.headContextRun_lparams head.continuation head.selected
    have candidateIsForall : nextSource.type.isForall = true :=
      position.traceSource_isForall
        iteration.generationShapes.head.storedSpine
    have validatorRootEq : head.continuation.source = nextSource.type :=
      AddInductive.CandidateWhnfStep.result_eq_of_source_isForall
        (iteration.cursor.headRootWhnf head.continuation head.selected)
        head.position.semantic.type.whnfFuel head.whnfDepth candidateIsForall
    have candidateRootEq : candidates.head.familyType.type.trace.rootWhnf =
        nextSource.type :=
      AddInductive.CandidateWhnfStep.result_eq_of_source_isForall
        candidates.head.familyType.type.trace.rootWhnf_valid
        head.position.semantic.type.whnfFuel
        head.position.semantic.type.whnfDepth candidateIsForall
    have boundaryRootEq :=
      parameter.boundary.prefix_path.annotationAt_root_eq
        (parameter.parameterSources_eq_candidateParameterList context_lctx_eq)
        position iteration.generationShapes.head.storedSpine
        (validatorRootEq.trans candidateRootEq.symm)
        head.position.semantic.type.whnfFuel head.whnfDepth
        head.position.semantic.type.whnfDepth
    have cursorContext : suffix.cursor.Δ.toCtx =
        (iteration.annotations.head.storedBinders.take
          source.nparams).reverse := by
      simpa only [VLCtx.toCtx, List.append_nil] using suffix.context_eq
    have parameterTelescope :=
      head.parameterTelescopeDefEq parameter candidate context_lctx_eq
    have parameterContext : env.IsDefEqCtx Us.length []
        completion.prefixes.firstParameterΔ.toCtx suffix.cursor.Δ.toCtx := by
      simpa only [List.append_nil, completion.prefixes.first_context,
        cursorContext] using parameterTelescope.telDefEq.ctx
    have relation : VLCtx.FVarAlpha env Us.length
        completion.prefixes.firstParameterΔ suffix.cursor.Δ :=
      VLCtx.FVarAlpha.of_defeqCtx completion.prefixes.first_shape
        suffix.cursor.shape parameterContext
    have mappedFVars :
        completion.prefixes.firstParameterΔ.fvars.map Expr.fvar =
          suffix.cursor.Δ.fvars.map Expr.fvar := by
      calc
        completion.prefixes.firstParameterΔ.fvars.map Expr.fvar =
            (staging.annotation.firstCandidate.familyType.type.trace
              |>.parameterList source.nparams).reverse :=
          completion.prefixes.first_fvars
        _ = (parameter.boundary.parameters.map Prod.fst).reverse :=
          congrArg List.reverse
            parameter.parameterSources_eq_firstParameterList.symm
        _ = (candidates.head.familyType.type.trace.parameterList
              source.nparams).reverse :=
          congrArg List.reverse
            (parameter.parameterSources_eq_candidateParameterList
              context_lctx_eq)
        _ = suffix.cursor.Δ.fvars.map Expr.fvar := by
          have suffixFVars := suffix.fvars_eq
          change suffix.cursor.Δ.fvars.map Expr.fvar =
            (candidates.head.familyType.type.trace.parameterList
              source.nparams).reverse ++ [] at suffixFVars
          simpa only [List.append_nil] using suffixFVars.symm
    have cursorFVars : completion.prefixes.firstParameterΔ.fvars =
        suffix.cursor.Δ.fvars :=
      list_map_fvar_injective mappedFVars
    have currentReference : VLCtx.IsDefEq env Us.length
        head.currentRun.context.vlctx iteration.reference := by
      change VLCtx.IsDefEq env Us.length
        (iteration.cursor.headContextRun head.continuation
          head.selected).context.vlctx iteration.reference
      rw [iteration.cursor.headContextRun_context head.continuation
        head.selected]
      exact iteration.current_reference
    have sourceScope : parameter.boundary.source.FVarsIn
        (· ∈ completion.prefixes.firstParameterΔ.fvars) := by
      rw [boundaryRootEq, suffix.root_eq, cursorFVars]
      exact suffix.cursor.root_fvars
    have sourceAlpha :
        Lean.Expr.abstractFVars completion.prefixes.firstParameterΔ
            parameter.boundary.source =
          Lean.Expr.abstractFVars suffix.cursor.Δ
            suffix.cursor.trace.rootWhnf := by
      rw [boundaryRootEq, suffix.root_eq]
      simp only [Lean.Expr.abstractFVars, cursorFVars]
    have terminalWF : VLCtx.WF env Us.length
        iteration.annotations.head.terminalRun.context.vlctx := by
      simpa only [iteration.annotations.head.terminal_venv,
        iteration.annotations.head.terminal_lparams] using
        iteration.annotations.head.terminalRun.context.Δwf
    have candidateDepth : suffix.cursor.candidateContext.fuel.recDepth =
        head.position.semantic.type.whnfFuel + 1 := by
      calc
        suffix.cursor.candidateContext.fuel.recDepth =
            candidates.head.familyType.type.context.fuel.recDepth :=
          congrArg (fun fuel => fuel.recDepth) suffix.fuel_eq
        _ = head.position.semantic.type.whnfFuel + 1 :=
          head.position.semantic.type.whnfDepth
    obtain ⟨⟨chain, alignment⟩⟩ :=
      suffix.cursor.indexDomainChainAligned terminalWF parameter.boundary
        currentVenv currentLparams completion.prefixes.first_shape relation
        iteration.root_reference_lift iteration.root_reference_lift
        iteration.origin_reference_lift currentReference sourceScope
        sourceAlpha head.position.semantic.type.whnfFuel head.whnfDepth
        candidateDepth
    exact ⟨{
      candidate := candidate
      chain := chain
      chain_length := alignment.property.trans
        (congrArg List.length suffix.domains_eq)
      alignment := alignment.val }⟩
  · have currentVenv : head.currentRun.context.venv = env :=
      iteration.cursor.headContextRun_venv head.continuation head.selected
    have currentLparams : head.currentRun.context.lparams = Us :=
      iteration.cursor.headContextRun_lparams head.continuation head.selected
    have henv : VEnv.WF env := by
      simpa only [currentVenv] using head.currentRun.context.Ewf
    have currentWF : VLCtx.WF env Us.length
        head.currentRun.context.vlctx := by
      simpa only [currentVenv, currentLparams] using
        head.currentRun.context.Δwf
    have currentReference : VLCtx.IsDefEq env Us.length
        head.currentRun.context.vlctx iteration.reference := by
      change VLCtx.IsDefEq env Us.length
        (iteration.cursor.headContextRun head.continuation
          head.selected).context.vlctx iteration.reference
      rw [iteration.cursor.headContextRun_context head.continuation
        head.selected]
      exact iteration.current_reference
    have binderCount : source.nparams =
        (VInductDecl.ctorFields head.position.raw.type).length :=
      noIndices.trans
        iteration.generationShapes.head.spineLength_eq_ctorFields
    have storedLength : iteration.annotations.head.storedBinders.length =
        source.nparams := by
      calc
        iteration.annotations.head.storedBinders.length =
            (VInductDecl.ctorFields head.position.raw.type).length :=
          iteration.annotations.head.stored_length
        _ = source.nparams := binderCount.symm
    have takeAll :
        iteration.annotations.head.storedBinders.take source.nparams =
          iteration.annotations.head.storedBinders :=
      List.take_of_length_le (by omega)
    have parameterTelescope :=
      head.parameterTelescopeDefEq parameter candidate context_lctx_eq
    have terminalShape :
        iteration.annotations.head.terminalRun.context.vlctx.FVarLamOnly :=
      iteration.annotations.head.annotation_spine.terminalShape .nil
    have parameterContext : env.IsDefEqCtx Us.length []
        completion.prefixes.firstParameterΔ.toCtx
        iteration.annotations.head.terminalRun.context.vlctx.toCtx := by
      simpa only [List.append_nil, completion.prefixes.first_context,
        iteration.annotations.head.terminal_vlctx, takeAll] using
        parameterTelescope.telDefEq.ctx
    have relation : VLCtx.FVarAlpha env Us.length
        completion.prefixes.firstParameterΔ
        iteration.annotations.head.terminalRun.context.vlctx :=
      VLCtx.FVarAlpha.of_defeqCtx completion.prefixes.first_shape
        terminalShape parameterContext
    let rawBinders := VExpr.telN source.nparams head.position.raw.type
    let arguments := parameter.boundary.parameters.map Prod.snd
    have positionRawEq : head.position.raw.type =
        iteration.cursor.semantics.headPosition.raw.type := rfl
    have fullRawLength :
        (VExpr.telN (VInductDecl.ctorFields head.position.raw.type).length
          head.position.raw.type).length =
          (VInductDecl.ctorFields head.position.raw.type).length :=
      iteration.annotations.head.telescope.length_eq.trans
        iteration.annotations.head.stored_length
    have rawBindersLength : rawBinders.length = source.nparams := by
      simpa only [rawBinders, binderCount] using fullRawLength
    have argumentsLength : arguments.length = rawBinders.length := by
      calc
        arguments.length = parameter.boundary.parameters.length := by
          simp only [arguments, List.length_map]
        _ = source.nparams := by
          simpa only [Nat.sub_zero] using
            parameter.boundary.parameters_length
        _ = rawBinders.length := rawBindersLength.symm
    have rootDef : env.IsDefEqU Us.length head.currentRun.context.vlctx.toCtx
        (VExpr.forallN rawBinders
          (VExpr.dropN source.nparams head.position.raw.type))
        parameter.root := by
      simpa only [currentVenv, currentLparams, rawBinders,
        VExpr.forallN_telN_dropN] using parameter.rawRoot_def
    have parameterSpine : TypeChecker.FamilyParameterSemanticSpine env
        Us.length head.currentRun.context.vlctx.toCtx parameter.root arguments
        parameter.boundary.source' := by
      simpa only [currentVenv, currentLparams, arguments] using
        parameter.parameterSpine
    have rawOnTel := iteration.annotations.head.telescope.telDefEq.raw_onTel
    have rawContext : OnCtx rawBinders.reverse (env.IsType Us.length) := by
      simpa only [rawBinders, positionRawEq, binderCount, List.append_nil] using
        rawOnTel.onCtx
          (show OnCtx ([] : List VExpr) (env.IsType Us.length) from trivial)
    have rawClosed := VEnv.CtxWF.closed henv.ordered rawContext
    obtain ⟨resultLevel, terminalEq⟩ := iteration.validation.head_terminal
    obtain ⟨resultType, fullEvidence⟩ :=
      iteration.annotations.head.recursive.spineEvidence
        iteration.generationShapes.head.storedSpine
    obtain ⟨viewLevel, _levelTr, viewResultEq⟩ :=
      iteration.annotations.head.recursive.viewResult_of_terminalSort
        terminalEq
    have resultDef := fullEvidence.result.isDefEq
    rw [viewResultEq] at resultDef
    have resultDefAtRaw : env.IsDefEq Us.length rawBinders.reverse
        (VExpr.dropN source.nparams head.position.raw.type)
        (.sort viewLevel) resultType := by
      simpa only [rawBinders, positionRawEq, noIndices, VLCtx.toCtx,
        List.append_nil] using resultDef
    have terminalDef : env.IsDefEq Us.length
        (rawBinders.reverse ++ head.currentRun.context.vlctx.toCtx)
        (VExpr.dropN source.nparams head.position.raw.type)
        (.sort viewLevel) resultType :=
      resultDefAtRaw.weakR henv.ordered rawClosed
        head.currentRun.context.vlctx.toCtx
    have specialized := parameterSpine.specializeTerminalDefEq henv
      currentWF.toCtx rootDef argumentsLength terminalDef
    rw [VExpr.instRev_closedN arguments (C := .sort viewLevel) trivial]
      at specialized
    have rawToSort : env.IsDefEqU Us.length
        head.currentRun.context.vlctx.toCtx
        (VExpr.instRev
          (VExpr.dropN source.nparams head.position.raw.type) arguments)
        (.sort viewLevel) := specialized.toU
    have rawToBoundary := parameterSpine.rawTerminal_defeq henv
      currentWF.toCtx rootDef argumentsLength
    have endpointSort : env.IsDefEqU Us.length
        head.currentRun.context.vlctx.toCtx parameter.boundary.source'
        (.sort viewLevel) :=
      rawToBoundary.symm.trans henv currentWF.toCtx rawToSort
    let chain : parameter.boundary.IndexDomainChain := .done
    exact ⟨{
      candidate := candidate
      chain := chain
      chain_length := by
        simp only [chain,
          TypeChecker.FamilyParameterIndexBoundary.IndexDomainChain.length,
          List.length_drop, storedLength]
        omega
      alignment := {
        base := completion.prefixes.firstParameterΔ
        reference := iteration.reference
        lift := iteration.rootLift
        rootLift := iteration.rootLift
        originLift := iteration.originLift
        base_shape := completion.prefixes.first_shape
        terminal_shape := terminalShape
        relation := relation
        reference_lift := iteration.root_reference_lift
        root_reference_lift := iteration.root_reference_lift
        origin_reference_lift := iteration.origin_reference_lift
        current_reference := by
          simpa only [chain,
            TypeChecker.FamilyParameterIndexBoundary.IndexDomainChain.endpoint] using
            currentReference
        sort := viewLevel
        endpoint_sort := by
          simpa only [chain,
            TypeChecker.FamilyParameterIndexBoundary.IndexDomainChain.endpoint] using
            endpointSort } }⟩

/-- Generic recursive-head completion with its exact terminal witness. -/
structure TerminalHeadDomainCompletion
    {iteration : completion.LaterFamilyIterationCursor candidates raws trace}
    (head : iteration.HeadStaging)
    (parameter : HeadParameterBoundary head)
    extends HeadDomainCompletion head parameter where
  terminal : toHeadDomainCompletion.chain.endpoint.boundary.Terminal

/-- Attach the exact terminal constructor to a completed recursive head. -/
theorem HeadStaging.terminalDomainCompletion
    {iteration : completion.LaterFamilyIterationCursor candidates raws trace}
    (head : iteration.HeadStaging)
    (parameter : HeadParameterBoundary head)
    (context_lctx_eq : context.lctx = {}) :
    Nonempty (TerminalHeadDomainCompletion head parameter) := by
  obtain ⟨domain⟩ := head.domainCompletion parameter context_lctx_eq
  have currentVenv : head.currentRun.context.venv = env :=
    iteration.cursor.headContextRun_venv head.continuation head.selected
  have henv : VEnv.WF env := by
    simpa only [currentVenv] using head.currentRun.context.Ewf
  obtain ⟨terminal⟩ := domain.alignment.terminal henv
  exact ⟨{
    toHeadDomainCompletion := domain
    terminal := terminal }⟩

/-- Exact verified context reached after an arbitrary recursive head's
complete telescope. -/
def TerminalHeadDomainCompletion.terminalRun
    {iteration : completion.LaterFamilyIterationCursor candidates raws trace}
    {head : iteration.HeadStaging}
    {parameter : HeadParameterBoundary head}
    (domain : TerminalHeadDomainCompletion head parameter) :
    TypeChecker.CandidateContextRun head.continuation.telescope.result.context :=
  domain.chain.endpointContextRun domain.terminal

/-- A generic completed head retains the semantic environment. -/
theorem TerminalHeadDomainCompletion.terminal_venv
    {iteration : completion.LaterFamilyIterationCursor candidates raws trace}
    {head : iteration.HeadStaging}
    {parameter : HeadParameterBoundary head}
    (domain : TerminalHeadDomainCompletion head parameter) :
    domain.terminalRun.context.venv = env := by
  exact (domain.chain.endpointContextRun_venv domain.terminal).trans
    (iteration.cursor.headContextRun_venv head.continuation head.selected)

/-- A generic completed head retains the semantic universe parameters. -/
theorem TerminalHeadDomainCompletion.terminal_lparams
    {iteration : completion.LaterFamilyIterationCursor candidates raws trace}
    {head : iteration.HeadStaging}
    {parameter : HeadParameterBoundary head}
    (domain : TerminalHeadDomainCompletion head parameter) :
    domain.terminalRun.context.lparams = Us := by
  exact (domain.chain.endpointContextRun_lparams domain.terminal).trans
    (iteration.cursor.headContextRun_lparams head.continuation head.selected)

/-- Reindexing a generic aligned endpoint preserves its exact evolving
shared reference. -/
theorem TerminalHeadDomainCompletion.current_reference
    {iteration : completion.LaterFamilyIterationCursor candidates raws trace}
    {head : iteration.HeadStaging}
    {parameter : HeadParameterBoundary head}
    (domain : TerminalHeadDomainCompletion head parameter) :
    VLCtx.IsDefEq env Us.length domain.terminalRun.context.vlctx
      domain.alignment.reference := by
  have terminalContextEq : domain.terminalRun.context =
      domain.chain.endpoint.contextRun.context := by
    unfold terminalRun
      TypeChecker.FamilyParameterIndexBoundary.IndexDomainChain.endpointContextRun
    apply TypeChecker.CandidateContextRun.cast_context_context
  rw [terminalContextEq]
  exact domain.alignment.current_reference

/-- Advance the dependent validator and semantic cursor through an arbitrary
completed recursive head. -/
def TerminalHeadDomainCompletion.advance
    {iteration : completion.LaterFamilyIterationCursor candidates raws trace}
    {head : iteration.HeadStaging}
    {parameter : HeadParameterBoundary head}
    (domain : TerminalHeadDomainCompletion head parameter) :
    CandidateBlockLaterFamilyValidationCursor env blockEnv Us source.nparams
      (firstSource :: secondSource :: allLaterSources)
      candidates.tail raws.tail head.continuation.tail :=
  iteration.cursor.advanceHead head.continuation head.selected head.invariant
    domain.terminalRun domain.terminal_venv domain.terminal_lparams

/-- Thread every invariant through one arbitrary completed recursive family,
yielding the exact source-order state for the remaining suffix.  The record is
constructed directly so its semantic cursor remains transparent to dependent
source-order consumers. -/
def TerminalHeadDomainCompletion.advanceIterationCursorExact
    {iteration : completion.LaterFamilyIterationCursor candidates raws trace}
    {head : iteration.HeadStaging}
    {parameter : HeadParameterBoundary head}
    (domain : TerminalHeadDomainCompletion head parameter) :
    completion.LaterFamilyIterationCursor candidates.tail raws.tail
      head.continuation.tail := by
  have parameterSources : domain.advance.parameterSources =
      staging.annotation.firstCandidate.familyType.type.trace.parameterList
        source.nparams := by
    calc
      domain.advance.parameterSources = iteration.cursor.parameterSources := by
        unfold advance
        exact iteration.cursor.advanceHead_parameterSources head.continuation
          head.selected head.invariant domain.terminalRun
          domain.terminal_venv domain.terminal_lparams
      _ = staging.annotation.firstCandidate.familyType.type.trace.parameterList
            source.nparams := iteration.parameterSources_eq_firstParameterList
  have candidateFuel :
      head.continuation.telescope.result.context.fuel = context.fuel := by
    calc
      head.continuation.telescope.result.context.fuel =
          head.continuation.context.fuel :=
        head.continuation.telescope.result_context_fuel
      _ = candidateContext.fuel :=
        congrArg AddInductive.Context.fuel
          (AddInductive.FamilyParameterComparisonBlockTrace.headContinuation?_context
            head.selected)
      _ = context.fuel := iteration.candidate_fuel_eq
  have firstTerminalFind : ∀ {fv : FVarId} {decl : LocalDecl},
      staging.annotation.firstCandidate.familyType.type.trace.terminalContext.lctx.find?
            fv = some decl →
        head.continuation.telescope.result.context.lctx.find? fv =
          some decl := by
    intro fv decl found
    have currentFound : head.continuation.context.lctx.find? fv =
        some decl := by
      rw [AddInductive.FamilyParameterComparisonBlockTrace.headContinuation?_context
        head.selected]
      exact iteration.firstTerminal_find found
    have resultFound := parameter.boundary.trace.result_findOld
      parameter.boundary.localState.localContext currentFound
    simpa only [parameter.boundary.result_eq] using resultFound
  have currentReference : VLCtx.IsDefEq env Us.length
      domain.advance.contextRun.context.vlctx
      domain.alignment.reference := by
    unfold advance
    rw [iteration.cursor.advanceHead_context head.continuation head.selected
      head.invariant domain.terminalRun domain.terminal_venv
      domain.terminal_lparams]
    exact domain.current_reference
  have advanceSemantics : domain.advance.semantics =
      iteration.cursor.semantics.tailExact := by
    unfold advance
    exact iteration.cursor.advanceHead_semantics head.continuation head.selected
      head.invariant domain.terminalRun domain.terminal_venv
      domain.terminal_lparams
  let tailPackage : Sigma fun shapes =>
      CandidateBlockFamilyAnnotationSpineList source env blockEnv Us
        domain.advance.semantics shapes := by
    rw [advanceSemantics]
    exact ⟨iteration.generationShapes.tailExact,
      iteration.annotations.tailExact⟩
  exact {
    cursor := domain.advance
    validation := iteration.validation.tail
    parameterSpines := iteration.parameterSpines.tail
    generationShapes := tailPackage.1
    annotations := tailPackage.2
    parameterSources_eq_firstParameterList := parameterSources
    candidate_fuel_eq := candidateFuel
    firstTerminal_find := firstTerminalFind
    reference := domain.alignment.reference
    rootLift := domain.alignment.rootLift
    originLift := domain.alignment.originLift
    root_reference_lift := domain.alignment.root_reference_lift
    origin_reference_lift := domain.alignment.origin_reference_lift
    current_reference := currentReference }

/-- Proposition-level compatibility wrapper for consumers that need only
inhabitation of the exact advanced state. -/
theorem TerminalHeadDomainCompletion.advanceIterationCursor
    {iteration : completion.LaterFamilyIterationCursor candidates raws trace}
    {head : iteration.HeadStaging}
    {parameter : HeadParameterBoundary head}
    (domain : TerminalHeadDomainCompletion head parameter) :
    Nonempty (completion.LaterFamilyIterationCursor
      candidates.tail raws.tail head.continuation.tail) :=
  ⟨domain.advanceIterationCursorExact⟩

/-- Canonical recursion state selected from the exact one-head advancement
proof.  Keeping this choice named makes the tail of a completion spine
definitionally tied to the endpoint that produced it. -/
def TerminalHeadDomainCompletion.nextIteration
    {iteration : completion.LaterFamilyIterationCursor candidates raws trace}
    {head : iteration.HeadStaging}
    {parameter : HeadParameterBoundary head}
    (domain : TerminalHeadDomainCompletion head parameter) :
    completion.LaterFamilyIterationCursor candidates.tail raws.tail
      head.continuation.tail :=
  domain.advanceIterationCursorExact

/-- The direct recursive-tail state stores precisely the semantic suffix of
the completed head. -/
theorem TerminalHeadDomainCompletion.nextIteration_semantics
    {iteration : completion.LaterFamilyIterationCursor candidates raws trace}
    {head : iteration.HeadStaging}
    {parameter : HeadParameterBoundary head}
    (domain : TerminalHeadDomainCompletion head parameter) :
    domain.nextIteration.cursor.semantics =
      iteration.cursor.semantics.tailExact := by
  unfold nextIteration advanceIterationCursorExact
  exact iteration.cursor.advanceHead_semantics head.continuation head.selected
    head.invariant domain.terminalRun domain.terminal_venv
    domain.terminal_lparams

/-- Complete every family in an arbitrary later-family suffix in source
order.  Each recursive tail is the exact state produced by the preceding
terminal endpoint. -/
inductive CompletionSpine :
    {remainingSources : List InductiveType} →
    {candidates : AddInductive.CandidateList AddInductive.CandidateFamily
      remainingSources} →
    {raws : List VInductiveType} →
    {dIdx : Nat} →
    {stats : AddInductive.InductiveStats} →
    {candidateContext : AddInductive.Context} →
    {trace : AddInductive.FamilyParameterComparisonBlockTrace source.nparams
      (firstSource :: secondSource :: allLaterSources).toArray dIdx stats
      candidateContext} →
    completion.LaterFamilyIterationCursor candidates raws trace → Type where
  | nil
      {dIdx : Nat}
      {stats : AddInductive.InductiveStats}
      {candidateContext : AddInductive.Context}
      {trace : AddInductive.FamilyParameterComparisonBlockTrace source.nparams
        (firstSource :: secondSource :: allLaterSources).toArray dIdx stats
        candidateContext}
      (iteration : completion.LaterFamilyIterationCursor .nil [] trace) :
      CompletionSpine iteration
  | cons
      {nextSource : InductiveType}
      {laterSources : List InductiveType}
      {candidates : AddInductive.CandidateList AddInductive.CandidateFamily
        (nextSource :: laterSources)}
      {raws : List VInductiveType}
      {dIdx : Nat}
      {stats : AddInductive.InductiveStats}
      {candidateContext : AddInductive.Context}
      {trace : AddInductive.FamilyParameterComparisonBlockTrace source.nparams
        (firstSource :: secondSource :: allLaterSources).toArray dIdx stats
        candidateContext}
      {iteration : completion.LaterFamilyIterationCursor candidates raws trace}
      (head : iteration.HeadStaging)
      (parameter : HeadParameterBoundary head)
      (domain : TerminalHeadDomainCompletion head parameter)
      (tail : CompletionSpine domain.nextIteration) :
      CompletionSpine iteration

/-- The producer-owned recursive state admits a complete source-order spine
for its entire remaining family suffix. -/
theorem completionSpine
    {remainingSources : List InductiveType}
    {candidates : AddInductive.CandidateList AddInductive.CandidateFamily
      remainingSources}
    {raws : List VInductiveType}
    {dIdx : Nat} {stats : AddInductive.InductiveStats}
    {candidateContext : AddInductive.Context}
    {trace : AddInductive.FamilyParameterComparisonBlockTrace source.nparams
      (firstSource :: secondSource :: allLaterSources).toArray dIdx stats
      candidateContext}
    (iteration : completion.LaterFamilyIterationCursor candidates raws trace)
    (context_lctx_eq : context.lctx = {}) :
    Nonempty (CompletionSpine iteration) := by
  induction remainingSources generalizing raws dIdx stats
      candidateContext with
  | nil =>
      cases candidates with
      | nil =>
          cases iteration.cursor.semantics
          exact ⟨.nil iteration⟩
  | cons nextSource laterSources ih =>
      obtain ⟨head⟩ := iteration.headStaging
      obtain ⟨parameter⟩ := head.parameterBoundary
      obtain ⟨domain⟩ :=
        head.terminalDomainCompletion parameter context_lctx_eq
      obtain ⟨tail⟩ := ih domain.nextIteration
      exact ⟨.cons head parameter domain tail⟩

/-- Collect the normalized-view shared-parameter equalities from a completed
later-family traversal.  The result is indexed by the cursor's exact semantic
suffix, preserving family order and preventing evidence from being reused at
another source position. -/
theorem CompletionSpine.viewParameterTelescopeDefEqs
    {remainingSources : List InductiveType}
    {candidates : AddInductive.CandidateList AddInductive.CandidateFamily
      remainingSources}
    {raws : List VInductiveType}
    {dIdx : Nat} {stats : AddInductive.InductiveStats}
    {candidateContext : AddInductive.Context}
    {trace : AddInductive.FamilyParameterComparisonBlockTrace source.nparams
      (firstSource :: secondSource :: allLaterSources).toArray dIdx stats
      candidateContext}
    {iteration : completion.LaterFamilyIterationCursor candidates raws trace}
    (spine : CompletionSpine iteration)
    (context_lctx_eq : context.lctx = {}) :
    CandidateBlockFamilyViewParameterDefEqList env blockEnv Us source.nparams
      staging.annotation.firstSemantic.type.view
      iteration.cursor.semantics := by
  induction spine with
  | nil iteration =>
      cases iteration.cursor.semantics
      exact .nil
  | @cons nextSource laterSources candidates raws dIdx stats candidateContext
      trace iteration head parameter domain tail ih =>
      cases candidates with
      | cons candidate candidates =>
          cases raws with
          | nil => cases iteration.cursor.semantics
          | cons raw raws =>
              cases semanticEq : iteration.cursor.semantics with
              | cons semantic semantics =>
                  rw [domain.nextIteration_semantics, semanticEq] at ih
                  change CandidateBlockFamilyViewParameterDefEqList env
                    blockEnv Us source.nparams
                    staging.annotation.firstSemantic.type.view semantics at ih
                  have headViewEq : head.position.semantic.type.view =
                      semantic.type.view := by
                    calc
                      head.position.semantic.type.view =
                          iteration.cursor.semantics.headPosition.semantic.type.view :=
                        rfl
                      _ = (CandidateBlockFamilySemanticListRun.cons semantic
                            semantics).headPosition.semantic.type.view :=
                        congrArg (fun roots =>
                          roots.headPosition.semantic.type.view) semanticEq
                      _ = semantic.type.view :=
                        CandidateBlockFamilySemanticListRun.headPosition_cons_view
                          semantic semantics
                  have headEvidence :=
                    head.viewParameterTelescopeDefEq parameter
                      domain.candidate context_lctx_eq
                  rw [headViewEq] at headEvidence
                  exact .cons
                    headEvidence ih

/-- The completed traversal consumes every remaining family, so its final
verified context is a run of the exact terminal validation context recorded
by the whole-block result.  Family nodes are impossible at the endpoint: the
exhausted source suffix contradicts their in-bounds index. -/
theorem CompletionSpine.terminalValidationContextRun
    {remainingSources : List InductiveType}
    {candidates : AddInductive.CandidateList AddInductive.CandidateFamily
      remainingSources}
    {raws : List VInductiveType}
    {dIdx : Nat} {stats : AddInductive.InductiveStats}
    {candidateContext : AddInductive.Context}
    {trace : AddInductive.FamilyParameterComparisonBlockTrace source.nparams
      (firstSource :: secondSource :: allLaterSources).toArray dIdx stats
      candidateContext}
    {iteration : completion.LaterFamilyIterationCursor candidates raws trace}
    (spine : CompletionSpine iteration) :
    ∃ terminalRun : TypeChecker.CandidateContextRun
        trace.result.validationContext,
      terminalRun.context.venv = env ∧
      terminalRun.context.lparams = Us := by
  induction spine with
  | @nil dIdx stats candidateContext trace iteration =>
      have suffix := iteration.cursor.sourceSuffix_eq
      have lengthLe :
          (firstSource :: secondSource :: allLaterSources).toArray.size ≤
            dIdx := by
        have suffixLength := congrArg List.length suffix
        simp only [List.length_drop, List.length_nil] at suffixLength
        simp only [List.size_toArray]
        omega
      rw [AddInductive.FamilyParameterComparisonBlockTrace.result_validationContext_of_length_le
        trace lengthLe]
      exact ⟨iteration.cursor.contextRun, iteration.cursor.venv_eq,
        iteration.cursor.lparams_eq⟩
  | @cons nextSource laterSources candidates raws dIdx stats candidateContext
      trace iteration head parameter domain tail ih =>
      rw [←
        AddInductive.FamilyParameterComparisonBlockTrace.headContinuation?_result
          head.selected]
      exact ih

end
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.LaterFamilyIterationCursor

/-- The complete later-family traversal reaches the block validator's exact
terminal context: a verified context run exists at
`normalization.validationContext` itself, connected through the retained
whole-block result rather than an extensionally similar rebuild. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.blockValidationContextRun
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
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    (completion : staging.TerminalIndexDomainCompletion raw)
    (context_lctx_eq : context.lctx = {}) :
    ∃ terminalRun : TypeChecker.CandidateContextRun
        (produced.execution.eliminationExecution.normalization
          |>.validationContext),
      terminalRun.context.venv = env ∧
      terminalRun.context.lparams = Us := by
  obtain ⟨cursor⟩ :=
    completion.remainingFamilyValidationCursor context_lctx_eq
  obtain ⟨annotations⟩ := cursor.annotationSpines
  obtain ⟨spine⟩ :=
    (cursor.iterationCursorExact annotations).completionSpine context_lctx_eq
  have endpoint := spine.terminalValidationContextRun
  rw [AddInductive.FamilyParameterComparisonBlockTrace.secondContinuation?_result
    cursor.validation.selected] at endpoint
  have canonicalEq :
      ((produced.execution.eliminationExecution.normalization).familyParameterComparisonTrace
          (produced.execution.normalization_run produced.producedExecution)
          produced.kernelSources_nonempty).result =
        (produced.execution.eliminationExecution.normalization).familyValidationResult :=
    AddInductive.FamilyValidationBlockRun.parameterComparisonTrace_result _
  rw [canonicalEq] at endpoint
  exact endpoint

/-- The block validator's terminal context preserves the entry checker
safety mode: family validation only extends local state. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.blockValidationContext_safety
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
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    (_completion : staging.TerminalIndexDomainCompletion raw) :
    (produced.execution.eliminationExecution.normalization
      |>.validationContext).safety = context.safety := by
  have canonicalEq :
      ((produced.execution.eliminationExecution.normalization).familyParameterComparisonTrace
          (produced.execution.normalization_run produced.producedExecution)
          produced.kernelSources_nonempty).result =
        (produced.execution.eliminationExecution.normalization).familyValidationResult :=
    AddInductive.FamilyValidationBlockRun.parameterComparisonTrace_result _
  have safety :=
    ((produced.execution.eliminationExecution.normalization).familyParameterComparisonTrace
        (produced.execution.normalization_run produced.producedExecution)
        produced.kernelSources_nonempty).result_safety
  rw [canonicalEq] at safety
  exact safety

/-- The exact context in which the block's `checkConstructors` runs is
verified at the staged Theory environments: the traversal endpoint's context
run is rebased onto the post-family kernel/Theory pair while keeping the
validator's accumulated local telescope. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.constructorValidationContextRun
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
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    (completion : staging.TerminalIndexDomainCompletion raw)
    (context_lctx_eq : context.lctx = {})
    (stagingInput : NormalizationCandidateBlockStagingInput context
      produced.execution.eliminationExecution.normalization env blockEnv Us
      source) :
    ∃ validationRun : TypeChecker.CandidateContextRun
        { (produced.execution.eliminationExecution.normalization
            |>.validationContext) with
          env := produced.execution.eliminationExecution.normalization
            |>.familyEnv },
      validationRun.context.venv = blockEnv ∧
      validationRun.context.lparams = Us := by
  obtain ⟨terminalRun, terminalVenv, terminalLparams⟩ :=
    completion.blockValidationContextRun context_lctx_eq
  obtain ⟨validationRun, validationVenv, validationLparams, _⟩ :=
    stagingInput.validationContextRunFrom terminalRun terminalVenv
      terminalLparams completion.blockValidationContext_safety
  exact ⟨validationRun, validationVenv, validationLparams⟩

/-- Collect dependent shared-parameter equality for the exact semantic family
hierarchy.  The first family contributes reflexivity, the second uses the
validator's original comparison, and the terminal handoff supplies every
later family in source order. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.viewParameterTelescopeDefEqList
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
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    (completion : staging.TerminalIndexDomainCompletion raw)
    (context_lctx_eq : context.lctx = {}) :
    CandidateBlockFamilyViewParameterDefEqList env blockEnv Us
      source.nparams staging.annotation.firstSemantic.type.view
      semantic.families := by
  have firstSecond := staging.viewParameterTelescopeDefEq raw
    completion.prefixes context_lctx_eq
  have firstFirst : TypeChecker.TelDefEqEvidence env Us.length []
      (VExpr.telN source.nparams
        staging.annotation.firstSemantic.type.view)
      (VExpr.telN source.nparams
        staging.annotation.firstSemantic.type.view) :=
    .ofTelDefEq firstSecond.telDefEq.raw_onTel.telDefEq_refl
  obtain ⟨cursor⟩ :=
    completion.remainingFamilyValidationCursor context_lctx_eq
  obtain ⟨annotations⟩ := cursor.annotationSpines
  let iteration := cursor.iterationCursorExact annotations
  obtain ⟨spine⟩ := iteration.completionSpine context_lctx_eq
  have remaining :=
    spine.viewParameterTelescopeDefEqs context_lctx_eq
  change CandidateBlockFamilyViewParameterDefEqList env blockEnv Us
    source.nparams staging.annotation.firstSemantic.type.view
    (cursor.iterationCursorExact annotations).cursor.semantics at remaining
  rw [cursor.iterationCursorExact_semantics annotations] at remaining
  exact staging.annotation.semantic_families.parameterDefEqList
    firstFirst firstSecond remaining

/-- Erase the dependent family indices while retaining shared-parameter
equality for every normalized view in source order. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.viewParameterTelescopeDefEqs
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
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    (completion : staging.TerminalIndexDomainCompletion raw)
    (context_lctx_eq : context.lctx = {}) :
    List.All
      (fun family => TypeChecker.TelDefEqEvidence env Us.length []
        (VExpr.telN source.nparams
          staging.annotation.firstSemantic.type.view)
        (VExpr.telN source.nparams family.type))
      semantic.families.views :=
  (completion.viewParameterTelescopeDefEqList context_lctx_eq).forall_views

/-- Rebuild every normalized family type with the canonical first-family
parameter telescope.  This is the whole-family semantic half of the eventual
canonical `Normalization.BlockWF`; constructor payloads remain a separate
validator-owned obligation. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.canonicalFamilyTypeDefEqs
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
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    (completion : staging.TerminalIndexDomainCompletion raw)
    (context_lctx_eq : context.lctx = {}) :
    List.All
      (fun family => ∃ resultLevel,
        TypeChecker.DefEqEvidence env Us.length [] family.type
          (canonicalizeFamilyParams source.nparams
            (blockParams source.nparams semantic.families.views)
            family).type
          (.sort resultLevel))
      semantic.families.views := by
  have parameters :=
    completion.viewParameterTelescopeDefEqList context_lctx_eq
  have henv : VEnv.WF env := by
    simpa only [staging.annotation.firstSemantic.type.venv_eq] using
      staging.annotation.firstSemantic.type.contextRun.context.Ewf
  have terminals := produced.execution.eliminationExecution.normalization
    |>.familyTerminalSorts
  have canonical :=
    parameters.canonicalFamilyTypeDefEqs henv terminals
  have params_eq :
      blockParams source.nparams semantic.families.views =
        VExpr.telN source.nparams
          staging.annotation.firstSemantic.type.view := by
    rw [staging.annotation.semantic_views_eq]
    rfl
  rw [params_eq]
  exact canonical

/-- Compose the semantic normalization with the canonical prefix rewrite for
every raw family.  This discharges exactly the family-type component of the
canonical block normalization; constructor types are intentionally absent
from the conclusion. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.rawCanonicalFamilyTypeDefEqs
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
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    (completion : staging.TerminalIndexDomainCompletion raw)
    (context_lctx_eq : context.lctx = {}) :
    List.Forall₂
      (fun rawFamily canonicalFamily => ∃ resultType,
        TypeChecker.DefEqEvidence env Us.length [] rawFamily.type
          canonicalFamily.type resultType)
      source.types semantic.canonicalNormalization.view.types := by
  have henv : VEnv.WF env := by
    simpa only [staging.annotation.firstSemantic.type.venv_eq] using
      staging.annotation.firstSemantic.type.contextRun.context.Ewf
  have canonical := completion.canonicalFamilyTypeDefEqs context_lctx_eq
  have evidence :=
    semantic.families.canonicalFamilyEvidence henv canonical
  simpa only [
    NormalizationCandidateBlockSemanticRun.canonicalNormalization,
    Normalization.canonicalizeSharedParams,
    VInductDecl.canonicalizeSharedParams,
    NormalizationCandidateBlockSemanticRun.normalization,
    NormalizationCandidateBlockSemanticRun.viewDecl] using evidence

/-- Assemble the checker-valid canonical block normalization from the
completed family traversal.  The family-type relocations are discharged by
the canonical evidence above; the per-family constructor telescope inventory
and well-formedness of the staged constructor environment remain the
producer's outstanding obligations and are taken as explicit premises. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.canonicalNormalizationBlockRun
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
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    (completion : staging.TerminalIndexDomainCompletion raw)
    (context_lctx_eq : context.lctx = {})
    (hblockEnv : VEnv.WF blockEnv)
    (constructorParameters :
      CandidateBlockConstructorViewParameterDefEqLists env blockEnv Us
        source.nparams
        (blockParams source.nparams semantic.families.views)
        semantic.families) :
    NormalizationBlockRun semantic.canonicalNormalization env blockEnv := by
  have henv : VEnv.WF env := by
    simpa only [staging.annotation.firstSemantic.type.venv_eq] using
      staging.annotation.firstSemantic.type.contextRun.context.Ewf
  have canonical := completion.canonicalFamilyTypeDefEqs context_lctx_eq
  have paramsLength :=
    produced.semanticViewParams_length semantic context_lctx_eq
  exact semantic.canonicalNormalizationRun henv hblockEnv canonical
    constructorParameters paramsLength

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.semantic_views_eq' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.semantic_views_eq

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.viewParameterTelescopeDefEq' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.viewParameterTelescopeDefEq

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.iterationCursorExact' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.iterationCursorExact

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.iterationCursorExact_semantics' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.iterationCursorExact_semantics

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.LaterFamilyIterationCursor.TerminalHeadDomainCompletion.advanceIterationCursorExact' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.LaterFamilyIterationCursor.TerminalHeadDomainCompletion.advanceIterationCursorExact

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.LaterFamilyIterationCursor.TerminalHeadDomainCompletion.nextIteration_semantics' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.LaterFamilyIterationCursor.TerminalHeadDomainCompletion.nextIteration_semantics

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.LaterFamilyIterationCursor.CompletionSpine.viewParameterTelescopeDefEqs' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.LaterFamilyIterationCursor.CompletionSpine.viewParameterTelescopeDefEqs

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.viewParameterTelescopeDefEqList' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.viewParameterTelescopeDefEqList

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.viewParameterTelescopeDefEqs' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.viewParameterTelescopeDefEqs

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.canonicalFamilyTypeDefEqs' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.canonicalFamilyTypeDefEqs

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.rawCanonicalFamilyTypeDefEqs' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.rawCanonicalFamilyTypeDefEqs

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.canonicalNormalizationBlockRun' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.canonicalNormalizationBlockRun

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.LaterFamilyIterationCursor.CompletionSpine.terminalValidationContextRun' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.LaterFamilyIterationCursor.CompletionSpine.terminalValidationContextRun

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.blockValidationContextRun' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.blockValidationContextRun

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.blockValidationContext_safety' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.blockValidationContext_safety

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.constructorValidationContextRun' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.constructorValidationContextRun

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.iterationCursor' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.iterationCursor

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.LaterFamilyIterationCursor.HeadStaging.parameterTelescopeDefEq' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.LaterFamilyIterationCursor.HeadStaging.parameterTelescopeDefEq

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.LaterFamilyIterationCursor.HeadStaging.viewParameterTelescopeDefEq' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.LaterFamilyIterationCursor.HeadStaging.viewParameterTelescopeDefEq

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.LaterFamilyIterationCursor.HeadStaging.domainCompletion' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.LaterFamilyIterationCursor.HeadStaging.domainCompletion

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.LaterFamilyIterationCursor.TerminalHeadDomainCompletion.advanceIterationCursor' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.LaterFamilyIterationCursor.TerminalHeadDomainCompletion.advanceIterationCursor

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.LaterFamilyIterationCursor.completionSpine' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.LaterFamilyIterationCursor.completionSpine

/-- Joint source-order staging for the next later family.  The annotation
spine and outer continuation are both selected from the same recursive
cursor, so downstream semantic interpretation cannot pair a family root with
a validator node from another position. -/
structure
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging
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
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    {completion : staging.TerminalIndexDomainCompletion raw}
    (cursor : completion.RemainingFamilyValidationCursor) where
  annotations : CandidateBlockFamilyAnnotationSpineList source env blockEnv
    Us cursor.cursor.semantics cursor.generationShapes
  validation : CandidateFamilyValidationAnnotationList
    { context with lctx := {} } staging.annotation.remainingCandidates
  continuation :
    AddInductive.FamilyParameterComparisonBlockTrace.FamilyContinuation
      source.nparams
      (firstSource :: secondSource :: remainingSources).toArray
  selected : cursor.validation.continuation.tail.headContinuation? =
    some continuation
  invariant : continuation.LaterInvariant

/-- Select the next joint family staging whenever the remaining source suffix
is nonempty. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.nextFamilyStaging
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
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    {completion : staging.TerminalIndexDomainCompletion raw}
    (cursor : completion.RemainingFamilyValidationCursor)
    (nonempty : remainingSources.isEmpty = false) :
    Nonempty cursor.NextFamilyStaging := by
  obtain ⟨annotations⟩ := cursor.annotationSpines
  obtain ⟨continuation, selected, invariant⟩ :=
    cursor.cursor.headContinuation nonempty
  exact ⟨{
    annotations := annotations
    validation := staging.annotation.remainingValidationAnnotations
    continuation := continuation
    selected := selected
    invariant := invariant }⟩

/-- The canonical semantic head jointly selected by a nonempty recursive
family staging. -/
def
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.position
    {source : VInductDecl}
    {firstSource secondSource nextSource : InductiveType}
    {laterSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: nextSource :: laterSources) numNested
      isUnsafe context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    {completion : staging.TerminalIndexDomainCompletion raw}
    {cursor : completion.RemainingFamilyValidationCursor}
    (_next : cursor.NextFamilyStaging) :=
  cursor.cursor.semantics.headPosition

/-- The exact verified reader context at the canonical next-family head. -/
def
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.currentRun
    {source : VInductDecl}
    {firstSource secondSource nextSource : InductiveType}
    {laterSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: nextSource :: laterSources) numNested
      isUnsafe context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    {completion : staging.TerminalIndexDomainCompletion raw}
    {cursor : completion.RemainingFamilyValidationCursor}
    (next : cursor.NextFamilyStaging) :
    TypeChecker.CandidateContextRun next.continuation.context :=
  cursor.cursor.headContextRun next.continuation next.selected

/-- The canonical next-family reader context has exactly the WHNF depth
recorded by its producer-owned semantic head. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.whnfDepth
    {source : VInductDecl}
    {firstSource secondSource nextSource : InductiveType}
    {laterSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: nextSource :: laterSources) numNested
      isUnsafe context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    {completion : staging.TerminalIndexDomainCompletion raw}
    {cursor : completion.RemainingFamilyValidationCursor}
    (next : cursor.NextFamilyStaging) :
    next.continuation.context.fuel.recDepth =
      next.position.semantic.type.whnfFuel + 1 := by
  calc
    next.continuation.context.fuel.recDepth =
        cursor.validation.continuation.telescope.result.context.fuel.recDepth :=
      congrArg (fun candidateContext => candidateContext.fuel.recDepth)
        (AddInductive.FamilyParameterComparisonBlockTrace.headContinuation?_context
          next.selected)
    _ = context.fuel.recDepth :=
      congrArg (fun fuel => fuel.recDepth) cursor.cursor_fuel_eq
    _ = ({ context with lctx := {} } : AddInductive.Context).fuel.recDepth :=
      rfl
    _ = staging.annotation.remainingCandidates.head.familyType.type.context.fuel.recDepth :=
      (congrArg (fun candidateContext => candidateContext.fuel.recDepth)
        next.validation.head_context_eq).symm
    _ = next.position.semantic.type.whnfFuel + 1 :=
      next.position.semantic.type.whnfDepth

/-- Execute the validator's retained root WHNF observation for the exact next
semantic family selected by the recursive cursor.

The semantic head supplies the raw Theory source and WHNF budget; validation
provenance identifies its original candidate context; the cursor supplies the
current verified context, source-order array identity, and preserved fuel.
No positional source, raw family, or WHNF result is selected by the caller. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.rootWhnf
    {source : VInductDecl}
    {firstSource secondSource nextSource : InductiveType}
    {laterSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: nextSource :: laterSources) numNested
      isUnsafe context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    {completion : staging.TerminalIndexDomainCompletion raw}
    {cursor : completion.RemainingFamilyValidationCursor}
    (next : cursor.NextFamilyStaging) :
    let position := cursor.cursor.semantics.headPosition
    let currentRun := cursor.cursor.headContextRun next.continuation
      next.selected
    ∃ root', currentRun.context.TrExprS next.continuation.source root' ∧
      Nonempty (TypeChecker.WhnfRun currentRun.context.venv
        currentRun.context.lparams currentRun.context.vlctx nextSource.type
        next.continuation.source position.raw.type root') := by
  let position := cursor.cursor.semantics.headPosition
  let currentRun := cursor.cursor.headContextRun next.continuation
    next.selected
  have sourceTr : currentRun.context.TrExprS nextSource.type
      position.raw.type := by
    rw [cursor.cursor.headContextRun_context next.continuation next.selected]
    exact cursor.cursor.headSourceTranslation
  have depth : next.continuation.context.fuel.recDepth =
      position.semantic.type.whnfFuel + 1 := by
    exact next.whnfDepth
  exact TypeChecker.WhnfRun.exists_ofCandidateStep
    ⟨next.continuation.context, nextSource.type, next.continuation.source⟩
    (cursor.cursor.headRootWhnf next.continuation next.selected)
    currentRun position.raw.type sourceTr position.semantic.type.whnfFuel depth

/-- Producer-owned shared-parameter semantics at the canonical next-family
head.  Every field is indexed by the same semantic head, validator
continuation, and verified context selected by `NextFamilyStaging`. -/
structure
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyParameterBoundary
    {source : VInductDecl}
    {firstSource secondSource nextSource : InductiveType}
    {laterSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: nextSource :: laterSources) numNested
      isUnsafe context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    {completion : staging.TerminalIndexDomainCompletion raw}
    {cursor : completion.RemainingFamilyValidationCursor}
    (next : cursor.NextFamilyStaging) where
  root : VExpr
  root_tr : next.currentRun.context.TrExprS next.continuation.source root
  rawRoot_def : next.currentRun.context.venv.IsDefEqU
    next.currentRun.context.lparams.length
    next.currentRun.context.vlctx.toCtx next.position.raw.type root
  comparisonRuns : ∀ step ∈ next.continuation.telescope.comparisons,
    TypeChecker.FamilyComparisonSemanticRun step
  boundary : TypeChecker.FamilyParameterIndexBoundary
    next.continuation.telescope next.currentRun
  parameterSpine : TypeChecker.FamilyParameterSemanticSpine
    next.currentRun.context.venv next.currentRun.context.lparams.length
    next.currentRun.context.vlctx.toCtx root
    (boundary.parameters.map Prod.snd) boundary.source'

/-- Interpret the exact next family's complete shared-parameter prefix and
retain its source-indexed index boundary. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.parameterBoundary
    {source : VInductDecl}
    {firstSource secondSource nextSource : InductiveType}
    {laterSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: nextSource :: laterSources) numNested
      isUnsafe context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    {completion : staging.TerminalIndexDomainCompletion raw}
    {cursor : completion.RemainingFamilyValidationCursor}
    (next : cursor.NextFamilyStaging) :
    Nonempty (cursor.NextFamilyParameterBoundary next) := by
  obtain ⟨root, rootTr, ⟨rootRun⟩⟩ := next.rootWhnf
  obtain ⟨comparisonRuns, boundary, parameterSpine⟩ :=
    TypeChecker.familyTypeParameterComparison_semanticSpine_of_later
      next.continuation.telescope
      next.invariant.current_indConsts_nonempty
      next.invariant.current_params_size
      (cursor.cursor.headLocalState next.continuation next.selected)
      next.currentRun root rootTr next.position.semantic.type.whnfFuel
      next.whnfDepth
  exact ⟨{
    root := root
    root_tr := rootTr
    rawRoot_def := rootRun.isDefEqU
    comparisonRuns := comparisonRuns
    boundary := boundary
    parameterSpine := parameterSpine }⟩

/-- The producer's parameter-prefix gate applies to the exact candidate at
the canonical next-family head. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.nparams_le_spineLength
    {source : VInductDecl}
    {firstSource secondSource nextSource : InductiveType}
    {laterSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: nextSource :: laterSources) numNested
      isUnsafe context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    {completion : staging.TerminalIndexDomainCompletion raw}
    {cursor : completion.RemainingFamilyValidationCursor}
    (_next : cursor.NextFamilyStaging) :
    source.nparams ≤
      staging.annotation.remainingCandidates.head.familyType.type.trace.spineLength :=
  staging.annotation.remainingParameterSpines.head

/-- The first and canonical next family candidates were normalized in the
same producer-owned reader context. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.firstCandidate_context_eq
    {source : VInductDecl}
    {firstSource secondSource nextSource : InductiveType}
    {laterSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: nextSource :: laterSources) numNested
      isUnsafe context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    {completion : staging.TerminalIndexDomainCompletion raw}
    {cursor : completion.RemainingFamilyValidationCursor}
    (next : cursor.NextFamilyStaging) :
    staging.annotation.firstCandidate.familyType.type.context =
      staging.annotation.remainingCandidates.head.familyType.type.context :=
  (staging.annotation.candidate_context_eq.trans
      staging.annotation.second_candidate_context_eq).trans
    next.validation.head_context_eq.symm

/-- Every later family candidate allocates the same exact shared-parameter
free variables as the first producer family. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.parameterLists_eq
    {source : VInductDecl}
    {firstSource secondSource nextSource : InductiveType}
    {laterSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: nextSource :: laterSources) numNested
      isUnsafe context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    {completion : staging.TerminalIndexDomainCompletion raw}
    {cursor : completion.RemainingFamilyValidationCursor}
    (next : cursor.NextFamilyStaging)
    (context_lctx_eq : context.lctx = {}) :
    staging.annotation.firstCandidate.familyType.type.trace.parameterList
        source.nparams =
      staging.annotation.remainingCandidates.head.familyType.type.trace.parameterList
        source.nparams :=
  AddInductive.CandidateExprTrace.parameterList_eq_of_ngen_eq
    staging.annotation.firstCandidate.familyType.type.trace
    staging.annotation.remainingCandidates.head.familyType.type.trace
    (congrArg AddInductive.Context.ngen next.firstCandidate_context_eq)
    (staging.annotation.first_nparams_le_spineLength context_lctx_eq)
    next.nparams_le_spineLength

/-- The exact validator parameter boundary and the canonical next candidate
name the same producer-allocated kernel parameter prefix. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyParameterBoundary.parameterSources_eq_candidateParameterList
    {source : VInductDecl}
    {firstSource secondSource nextSource : InductiveType}
    {laterSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: nextSource :: laterSources) numNested
      isUnsafe context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    {completion : staging.TerminalIndexDomainCompletion raw}
    {cursor : completion.RemainingFamilyValidationCursor}
    {next : cursor.NextFamilyStaging}
    (parameter : cursor.NextFamilyParameterBoundary next)
    (context_lctx_eq : context.lctx = {}) :
    parameter.boundary.parameters.map Prod.fst =
      staging.annotation.remainingCandidates.head.familyType.type.trace.parameterList
        source.nparams := by
  calc
    parameter.boundary.parameters.map Prod.fst =
        next.continuation.stats.params.toList := by
      simpa using parameter.boundary.parameter_sources_eq
    _ = cursor.cursor.parameterSources := by
      rw [AddInductive.FamilyParameterComparisonBlockTrace.headContinuation?_stats
        next.selected]
      exact cursor.cursor.current_parameterSources_eq
    _ = staging.annotation.firstCandidate.familyType.type.trace.parameterList
          source.nparams := cursor.parameterSources_eq_firstParameterList
    _ = staging.annotation.remainingCandidates.head.familyType.type.trace.parameterList
          source.nparams :=
      next.parameterLists_eq context_lctx_eq

/-- The exact next-family parameter boundary retains the original first
candidate's producer-allocated shared-parameter inventory. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyParameterBoundary.parameterSources_eq_firstParameterList
    {source : VInductDecl}
    {firstSource secondSource nextSource : InductiveType}
    {laterSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: nextSource :: laterSources) numNested
      isUnsafe context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    {completion : staging.TerminalIndexDomainCompletion raw}
    {cursor : completion.RemainingFamilyValidationCursor}
    {next : cursor.NextFamilyStaging}
    (parameter : cursor.NextFamilyParameterBoundary next) :
    parameter.boundary.parameters.map Prod.fst =
      staging.annotation.firstCandidate.familyType.type.trace.parameterList
        source.nparams := by
  calc
    parameter.boundary.parameters.map Prod.fst =
        next.continuation.stats.params.toList := by
      simpa using parameter.boundary.parameter_sources_eq
    _ = cursor.cursor.parameterSources := by
      rw [AddInductive.FamilyParameterComparisonBlockTrace.headContinuation?_stats
        next.selected]
      exact cursor.cursor.current_parameterSources_eq
    _ = staging.annotation.firstCandidate.familyType.type.trace.parameterList
          source.nparams := cursor.parameterSources_eq_firstParameterList

/-- The exact producer annotation suffix at the canonical next family's
parameter boundary.  The terminal-inclusive position makes this package
available whether or not the family declares any indices. -/
structure
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyCandidateParameterSuffix
    {source : VInductDecl}
    {firstSource secondSource nextSource : InductiveType}
    {laterSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: nextSource :: laterSources) numNested
      isUnsafe context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    {completion : staging.TerminalIndexDomainCompletion raw}
    {cursor : completion.RemainingFamilyValidationCursor}
    (next : cursor.NextFamilyStaging) where
  position :
    staging.annotation.remainingCandidates.head.familyType.type.trace.MainSpineAt
      source.nparams
  suffix : next.annotations.head.annotation_spine.MainPositionSuffix position

/-- Select the next candidate's literal parameter-boundary cursor from its
producer-owned parameter bound, terminal sort, and annotation traversal. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.candidateParameterSuffix
    {source : VInductDecl}
    {firstSource secondSource nextSource : InductiveType}
    {laterSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: nextSource :: laterSources) numNested
      isUnsafe context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    {completion : staging.TerminalIndexDomainCompletion raw}
    {cursor : completion.RemainingFamilyValidationCursor}
    (next : cursor.NextFamilyStaging) :
    Nonempty (cursor.NextFamilyCandidateParameterSuffix next) := by
  obtain ⟨position⟩ :=
    AddInductive.CandidateExprTrace.mainSpineAt
      (next.nparams_le_spineLength)
  obtain ⟨resultLevel, terminalEq⟩ := next.validation.head_terminal
  obtain ⟨suffix⟩ :=
    next.annotations.head.annotation_spine.mainPositionSuffix .nil
      cursor.generationShapes.head.storedSpine
      next.annotations.head.validation_annotations terminalEq position
  exact ⟨{ position := position, suffix := suffix }⟩

/-- The validator's retained shared-parameter comparisons construct the
exact telescope equality between the first producer family and the canonical
next family.  The first-terminal origin lift permits arbitrary prior-family
indices in the current validator context. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.parameterTelescopeDefEq
    {source : VInductDecl}
    {firstSource secondSource nextSource : InductiveType}
    {laterSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: nextSource :: laterSources) numNested
      isUnsafe context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    {completion : staging.TerminalIndexDomainCompletion raw}
    {cursor : completion.RemainingFamilyValidationCursor}
    (next : cursor.NextFamilyStaging)
    (parameter : cursor.NextFamilyParameterBoundary next)
    (candidate : cursor.NextFamilyCandidateParameterSuffix next)
    (context_lctx_eq : context.lctx = {}) :
    TypeChecker.TelDefEqEvidence env Us.length []
      (staging.annotation.firstStoredBinders.take source.nparams)
      (next.annotations.head.storedBinders.take source.nparams) := by
  have currentVenv : next.currentRun.context.venv = env :=
    cursor.cursor.headContextRun_venv next.continuation next.selected
  have currentLparams : next.currentRun.context.lparams = Us :=
    cursor.cursor.headContextRun_lparams next.continuation next.selected
  have firstRootLctx :
      staging.annotation.firstCandidate.familyType.type.context.lctx =
        ({} : LocalContext) := by
    calc
      staging.annotation.firstCandidate.familyType.type.context.lctx =
          staging.annotation.remainingCandidates.head.familyType.type.context.lctx :=
        congrArg AddInductive.Context.lctx next.firstCandidate_context_eq
      _ = ({ context with lctx := {} } : AddInductive.Context).lctx :=
        congrArg AddInductive.Context.lctx
          next.validation.head_context_eq
      _ = {} := rfl
  have firstTerminalFind : ∀ {fv : FVarId} {decl : LocalDecl},
      staging.annotation.firstCandidate.familyType.type.trace.terminalContext.lctx.find?
          fv = some decl →
        next.continuation.context.lctx.find? fv = some decl := by
    intro fv decl found
    rw [AddInductive.FamilyParameterComparisonBlockTrace.headContinuation?_context
      next.selected]
    exact cursor.firstTerminal_find found
  have currentReference : VLCtx.IsDefEq env Us.length
      next.currentRun.context.vlctx completion.alignment.reference := by
    change VLCtx.IsDefEq env Us.length
      (cursor.cursor.headContextRun next.continuation next.selected).context.vlctx
        completion.alignment.reference
    rw [cursor.cursor.headContextRun_context next.continuation next.selected]
    rw [cursor.context_eq_terminal]
    exact completion.current_reference
  have validatorCandidateRoot : 0 < source.nparams →
      next.continuation.source =
        staging.annotation.remainingCandidates.head.familyType.type.trace.rootWhnf := by
    intro positive
    have candidateIsForall : nextSource.type.isForall = true :=
      candidate.position.traceSource_isForall positive
        cursor.generationShapes.head.storedSpine
    have validatorRootEq : next.continuation.source = nextSource.type :=
      AddInductive.CandidateWhnfStep.result_eq_of_source_isForall
        (cursor.cursor.headRootWhnf next.continuation next.selected)
        next.position.semantic.type.whnfFuel next.whnfDepth
        candidateIsForall
    have candidateRootEq :
        staging.annotation.remainingCandidates.head.familyType.type.trace.rootWhnf =
          nextSource.type :=
      AddInductive.CandidateWhnfStep.result_eq_of_source_isForall
        staging.annotation.remainingCandidates.head.familyType.type.trace.rootWhnf_valid
        next.position.semantic.type.whnfFuel
        next.position.semantic.type.whnfDepth candidateIsForall
    exact validatorRootEq.trans candidateRootEq.symm
  have evidence := sharedParameterTelescopeDefEqAux
    parameter.boundary.prefix_path parameter.boundary.params_size
    parameter.boundary.localState next.currentRun currentVenv currentLparams
    parameter.root_tr next.position.semantic.type.whnfFuel next.whnfDepth
    staging.annotation.first_annotation_spine
    staging.annotation.first_validation_annotations
    (TypeChecker.CandidateLocalContextRun.empty _ firstRootLctx)
    firstTerminalFind next.annotations.head.annotation_spine
    next.annotations.head.validation_annotations candidate.position
    cursor.generationShapes.head.storedSpine
    next.position.semantic.type.whnfDepth validatorCandidateRoot
    parameter.parameterSources_eq_firstParameterList
    (parameter.parameterSources_eq_candidateParameterList context_lctx_eq)
    (.nil) completion.alignment.origin_reference_lift currentReference
  simpa only [VLCtx.toCtx] using evidence

/-- Exact endpoint package for a later family whose parameter boundary is
followed by at least one index.  The retained root base is still the first
family's shared-parameter prefix, while the origin base records the complete
first-family terminal context across all intervening family indices. -/
structure
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyIndexDomainCompletion
    {source : VInductDecl}
    {firstSource secondSource nextSource : InductiveType}
    {laterSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: nextSource :: laterSources) numNested
      isUnsafe context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    {completion : staging.TerminalIndexDomainCompletion raw}
    {cursor : completion.RemainingFamilyValidationCursor}
    (next : cursor.NextFamilyStaging)
    (parameter : cursor.NextFamilyParameterBoundary next) where
  position :
    staging.annotation.remainingCandidates.head.familyType.type.trace.AnnotationAt
      source.nparams
  suffix : next.annotations.head.annotation_spine.PositionSuffix position
  chain : parameter.boundary.IndexDomainChain
  chain_length : chain.length =
    (next.annotations.head.storedBinders.drop source.nparams).length
  alignment : chain.EndpointAlignment env Us
    next.annotations.head.terminalRun.context.vlctx
    completion.prefixes.firstParameterΔ
    staging.annotation.firstTerminalRun.context.vlctx

/-- Consume the indexed suffix of the canonical next family through its exact
validator continuation.  All roots, contexts, and positional evidence are
selected from the same source-order staging. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.indexDomainCompletion
    {source : VInductDecl}
    {firstSource secondSource nextSource : InductiveType}
    {laterSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: nextSource :: laterSources) numNested
      isUnsafe context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    {completion : staging.TerminalIndexDomainCompletion raw}
    {cursor : completion.RemainingFamilyValidationCursor}
    (next : cursor.NextFamilyStaging)
    (parameter : cursor.NextFamilyParameterBoundary next)
    (candidate : cursor.NextFamilyCandidateParameterSuffix next)
    (context_lctx_eq : context.lctx = {})
    (hasIndex : source.nparams <
      staging.annotation.remainingCandidates.head.familyType.type.trace.spineLength) :
    Nonempty (cursor.NextFamilyIndexDomainCompletion next parameter) := by
  obtain ⟨position⟩ :=
    AddInductive.CandidateExprTrace.annotationAt
      next.annotations.head.validation_annotations hasIndex
  obtain ⟨resultLevel, terminalEq⟩ := next.validation.head_terminal
  obtain ⟨suffix⟩ :=
    next.annotations.head.annotation_spine.positionSuffix .nil
      cursor.generationShapes.head.storedSpine
      next.annotations.head.validation_annotations terminalEq position
  have currentVenv : next.currentRun.context.venv = env :=
    cursor.cursor.headContextRun_venv next.continuation next.selected
  have currentLparams : next.currentRun.context.lparams = Us :=
    cursor.cursor.headContextRun_lparams next.continuation next.selected
  have candidateIsForall : nextSource.type.isForall = true :=
    position.traceSource_isForall
      cursor.generationShapes.head.storedSpine
  have validatorRootEq : next.continuation.source = nextSource.type :=
    AddInductive.CandidateWhnfStep.result_eq_of_source_isForall
      (cursor.cursor.headRootWhnf next.continuation next.selected)
      next.position.semantic.type.whnfFuel next.whnfDepth candidateIsForall
  have candidateRootEq :
      staging.annotation.remainingCandidates.head.familyType.type.trace.rootWhnf =
        nextSource.type :=
    AddInductive.CandidateWhnfStep.result_eq_of_source_isForall
      staging.annotation.remainingCandidates.head.familyType.type.trace.rootWhnf_valid
      next.position.semantic.type.whnfFuel
      next.position.semantic.type.whnfDepth candidateIsForall
  have boundaryRootEq :=
    parameter.boundary.prefix_path.annotationAt_root_eq
      (parameter.parameterSources_eq_candidateParameterList context_lctx_eq)
      position cursor.generationShapes.head.storedSpine
      (validatorRootEq.trans candidateRootEq.symm)
      next.position.semantic.type.whnfFuel next.whnfDepth
      next.position.semantic.type.whnfDepth
  have cursorContext : suffix.cursor.Δ.toCtx =
      (next.annotations.head.storedBinders.take source.nparams).reverse := by
    simpa only [VLCtx.toCtx, List.append_nil] using suffix.context_eq
  have parameterTelescope :=
    next.parameterTelescopeDefEq parameter candidate context_lctx_eq
  have parameterContext : env.IsDefEqCtx Us.length []
      completion.prefixes.firstParameterΔ.toCtx suffix.cursor.Δ.toCtx := by
    simpa only [List.append_nil, completion.prefixes.first_context,
      cursorContext] using parameterTelescope.telDefEq.ctx
  have relation : VLCtx.FVarAlpha env Us.length
      completion.prefixes.firstParameterΔ suffix.cursor.Δ :=
    VLCtx.FVarAlpha.of_defeqCtx completion.prefixes.first_shape
      suffix.cursor.shape parameterContext
  have mappedFVars :
      completion.prefixes.firstParameterΔ.fvars.map Expr.fvar =
        suffix.cursor.Δ.fvars.map Expr.fvar := by
    calc
      completion.prefixes.firstParameterΔ.fvars.map Expr.fvar =
          (staging.annotation.firstCandidate.familyType.type.trace
            |>.parameterList source.nparams).reverse :=
        completion.prefixes.first_fvars
      _ = (parameter.boundary.parameters.map Prod.fst).reverse :=
        congrArg List.reverse
          parameter.parameterSources_eq_firstParameterList.symm
      _ = (staging.annotation.remainingCandidates.head.familyType.type.trace
            |>.parameterList source.nparams).reverse :=
        congrArg List.reverse
          (parameter.parameterSources_eq_candidateParameterList
            context_lctx_eq)
      _ = suffix.cursor.Δ.fvars.map Expr.fvar := by
        have suffixFVars := suffix.fvars_eq
        change suffix.cursor.Δ.fvars.map Expr.fvar =
          (staging.annotation.remainingCandidates.head.familyType.type.trace
            |>.parameterList source.nparams).reverse ++ [] at suffixFVars
        simpa only [List.append_nil] using suffixFVars.symm
  have cursorFVars : completion.prefixes.firstParameterΔ.fvars =
      suffix.cursor.Δ.fvars :=
    list_map_fvar_injective mappedFVars
  have currentReference : VLCtx.IsDefEq env Us.length
      next.currentRun.context.vlctx completion.alignment.reference := by
    change VLCtx.IsDefEq env Us.length
      (cursor.cursor.headContextRun next.continuation next.selected).context.vlctx
        completion.alignment.reference
    rw [cursor.cursor.headContextRun_context next.continuation next.selected]
    rw [cursor.context_eq_terminal]
    exact completion.current_reference
  have sourceScope : parameter.boundary.source.FVarsIn
      (· ∈ completion.prefixes.firstParameterΔ.fvars) := by
    rw [boundaryRootEq, suffix.root_eq, cursorFVars]
    exact suffix.cursor.root_fvars
  have sourceAlpha :
      Lean.Expr.abstractFVars completion.prefixes.firstParameterΔ
          parameter.boundary.source =
        Lean.Expr.abstractFVars suffix.cursor.Δ
          suffix.cursor.trace.rootWhnf := by
    rw [boundaryRootEq, suffix.root_eq]
    simp only [Lean.Expr.abstractFVars, cursorFVars]
  have terminalWF : VLCtx.WF env Us.length
      next.annotations.head.terminalRun.context.vlctx := by
    simpa only [next.annotations.head.terminal_venv,
      next.annotations.head.terminal_lparams] using
      next.annotations.head.terminalRun.context.Δwf
  have candidateDepth : suffix.cursor.candidateContext.fuel.recDepth =
      next.position.semantic.type.whnfFuel + 1 := by
    calc
      suffix.cursor.candidateContext.fuel.recDepth =
          staging.annotation.remainingCandidates.head.familyType.type.context.fuel.recDepth :=
        congrArg (fun fuel => fuel.recDepth) suffix.fuel_eq
      _ = next.position.semantic.type.whnfFuel + 1 :=
        next.position.semantic.type.whnfDepth
  obtain ⟨⟨chain, alignment⟩⟩ :=
    suffix.cursor.indexDomainChainAligned terminalWF parameter.boundary
      currentVenv currentLparams completion.prefixes.first_shape relation
      completion.alignment.root_reference_lift
      completion.alignment.root_reference_lift
      completion.alignment.origin_reference_lift currentReference sourceScope
      sourceAlpha next.position.semantic.type.whnfFuel next.whnfDepth
      candidateDepth
  exact ⟨{
    position := position
    suffix := suffix
    chain := chain
    chain_length := alignment.property.trans
      (congrArg List.length suffix.domains_eq)
    alignment := alignment.val }⟩

/-- Exact endpoint package for a later family whose complete telescope ends
at the shared-parameter boundary.  Its index chain is empty, but it carries
the same endpoint alignment as an indexed family. -/
structure
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyZeroIndexDomainCompletion
    {source : VInductDecl}
    {firstSource secondSource nextSource : InductiveType}
    {laterSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: nextSource :: laterSources) numNested
      isUnsafe context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    {completion : staging.TerminalIndexDomainCompletion raw}
    {cursor : completion.RemainingFamilyValidationCursor}
    (next : cursor.NextFamilyStaging)
    (parameter : cursor.NextFamilyParameterBoundary next)
    (candidate : cursor.NextFamilyCandidateParameterSuffix next) where
  no_indices : source.nparams =
    staging.annotation.remainingCandidates.head.familyType.type.trace.spineLength
  chain : parameter.boundary.IndexDomainChain
  chain_length : chain.length =
    (next.annotations.head.storedBinders.drop source.nparams).length
  alignment : chain.EndpointAlignment env Us
    next.annotations.head.terminalRun.context.vlctx
    completion.prefixes.firstParameterΔ
    staging.annotation.firstTerminalRun.context.vlctx

/-- Close a canonical later family directly at its terminal sort when it has
no indices.  The terminal equality is specialized along the validator's
producer-owned parameter spine, so this branch does not invent a Pi position
at the endpoint. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.zeroIndexDomainCompletion
    {source : VInductDecl}
    {firstSource secondSource nextSource : InductiveType}
    {laterSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: nextSource :: laterSources) numNested
      isUnsafe context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    {completion : staging.TerminalIndexDomainCompletion raw}
    {cursor : completion.RemainingFamilyValidationCursor}
    (next : cursor.NextFamilyStaging)
    (parameter : cursor.NextFamilyParameterBoundary next)
    (candidate : cursor.NextFamilyCandidateParameterSuffix next)
    (context_lctx_eq : context.lctx = {})
    (noIndices : source.nparams =
      staging.annotation.remainingCandidates.head.familyType.type.trace.spineLength) :
    Nonempty
      (cursor.NextFamilyZeroIndexDomainCompletion next parameter candidate) := by
  have currentVenv : next.currentRun.context.venv = env :=
    cursor.cursor.headContextRun_venv next.continuation next.selected
  have currentLparams : next.currentRun.context.lparams = Us :=
    cursor.cursor.headContextRun_lparams next.continuation next.selected
  have henv : VEnv.WF env := by
    simpa only [currentVenv] using next.currentRun.context.Ewf
  have currentWF : VLCtx.WF env Us.length
      next.currentRun.context.vlctx := by
    simpa only [currentVenv, currentLparams] using
      next.currentRun.context.Δwf
  have currentReference : VLCtx.IsDefEq env Us.length
      next.currentRun.context.vlctx completion.alignment.reference := by
    change VLCtx.IsDefEq env Us.length
      (cursor.cursor.headContextRun next.continuation next.selected).context.vlctx
        completion.alignment.reference
    rw [cursor.cursor.headContextRun_context next.continuation next.selected]
    rw [cursor.context_eq_terminal]
    exact completion.current_reference
  have binderCount : source.nparams =
      (VInductDecl.ctorFields next.position.raw.type).length :=
    noIndices.trans
      cursor.generationShapes.head.spineLength_eq_ctorFields
  have storedLength : next.annotations.head.storedBinders.length =
      source.nparams := by
    calc
      next.annotations.head.storedBinders.length =
          (VInductDecl.ctorFields next.position.raw.type).length :=
        next.annotations.head.stored_length
      _ = source.nparams := binderCount.symm
  have takeAll :
      next.annotations.head.storedBinders.take source.nparams =
        next.annotations.head.storedBinders :=
    List.take_of_length_le (by omega)
  have parameterTelescope :=
    next.parameterTelescopeDefEq parameter candidate context_lctx_eq
  have terminalShape :
      next.annotations.head.terminalRun.context.vlctx.FVarLamOnly :=
    next.annotations.head.annotation_spine.terminalShape .nil
  have parameterContext : env.IsDefEqCtx Us.length []
      completion.prefixes.firstParameterΔ.toCtx
      next.annotations.head.terminalRun.context.vlctx.toCtx := by
    simpa only [List.append_nil, completion.prefixes.first_context,
      next.annotations.head.terminal_vlctx, takeAll] using
      parameterTelescope.telDefEq.ctx
  have relation : VLCtx.FVarAlpha env Us.length
      completion.prefixes.firstParameterΔ
      next.annotations.head.terminalRun.context.vlctx :=
    VLCtx.FVarAlpha.of_defeqCtx completion.prefixes.first_shape
      terminalShape parameterContext
  let rawBinders := VExpr.telN source.nparams next.position.raw.type
  let arguments := parameter.boundary.parameters.map Prod.snd
  have positionRawEq : next.position.raw.type =
      cursor.cursor.semantics.headPosition.raw.type := rfl
  have fullRawLength :
      (VExpr.telN (VInductDecl.ctorFields next.position.raw.type).length
        next.position.raw.type).length =
        (VInductDecl.ctorFields next.position.raw.type).length :=
    next.annotations.head.telescope.length_eq.trans
      next.annotations.head.stored_length
  have rawBindersLength : rawBinders.length = source.nparams := by
    simpa only [rawBinders, binderCount] using fullRawLength
  have argumentsLength : arguments.length = rawBinders.length := by
    calc
      arguments.length = parameter.boundary.parameters.length := by
        simp only [arguments, List.length_map]
      _ = source.nparams := by
        simpa only [Nat.sub_zero] using
          parameter.boundary.parameters_length
      _ = rawBinders.length := rawBindersLength.symm
  have rootDef : env.IsDefEqU Us.length next.currentRun.context.vlctx.toCtx
      (VExpr.forallN rawBinders
        (VExpr.dropN source.nparams next.position.raw.type))
      parameter.root := by
    simpa only [currentVenv, currentLparams, rawBinders,
      VExpr.forallN_telN_dropN] using parameter.rawRoot_def
  have parameterSpine : TypeChecker.FamilyParameterSemanticSpine env
      Us.length next.currentRun.context.vlctx.toCtx parameter.root arguments
      parameter.boundary.source' := by
    simpa only [currentVenv, currentLparams, arguments] using
      parameter.parameterSpine
  have rawOnTel := next.annotations.head.telescope.telDefEq.raw_onTel
  have rawContext : OnCtx rawBinders.reverse (env.IsType Us.length) := by
    simpa only [rawBinders, positionRawEq, binderCount, List.append_nil] using
      rawOnTel.onCtx
        (show OnCtx ([] : List VExpr) (env.IsType Us.length) from trivial)
  have rawClosed := VEnv.CtxWF.closed henv.ordered rawContext
  obtain ⟨resultLevel, terminalEq⟩ := next.validation.head_terminal
  obtain ⟨resultType, fullEvidence⟩ :=
    next.annotations.head.recursive.spineEvidence
      cursor.generationShapes.head.storedSpine
  obtain ⟨viewLevel, _levelTr, viewResultEq⟩ :=
    next.annotations.head.recursive.viewResult_of_terminalSort terminalEq
  have resultDef := fullEvidence.result.isDefEq
  rw [viewResultEq] at resultDef
  have resultDefAtRaw : env.IsDefEq Us.length rawBinders.reverse
      (VExpr.dropN source.nparams next.position.raw.type)
      (.sort viewLevel) resultType := by
    simpa only [rawBinders, positionRawEq, noIndices, VLCtx.toCtx,
      List.append_nil] using resultDef
  have terminalDef : env.IsDefEq Us.length
      (rawBinders.reverse ++ next.currentRun.context.vlctx.toCtx)
      (VExpr.dropN source.nparams next.position.raw.type)
      (.sort viewLevel) resultType :=
    resultDefAtRaw.weakR henv.ordered rawClosed
      next.currentRun.context.vlctx.toCtx
  have specialized := parameterSpine.specializeTerminalDefEq henv
    currentWF.toCtx rootDef argumentsLength terminalDef
  rw [VExpr.instRev_closedN arguments (C := .sort viewLevel) trivial]
    at specialized
  have rawToSort : env.IsDefEqU Us.length
      next.currentRun.context.vlctx.toCtx
      (VExpr.instRev
        (VExpr.dropN source.nparams next.position.raw.type) arguments)
      (.sort viewLevel) := specialized.toU
  have rawToBoundary := parameterSpine.rawTerminal_defeq henv
    currentWF.toCtx rootDef argumentsLength
  have endpointSort : env.IsDefEqU Us.length
      next.currentRun.context.vlctx.toCtx parameter.boundary.source'
      (.sort viewLevel) :=
    rawToBoundary.symm.trans henv currentWF.toCtx rawToSort
  let chain : parameter.boundary.IndexDomainChain := .done
  exact ⟨{
    no_indices := noIndices
    chain := chain
    chain_length := by
      simp only [chain,
        TypeChecker.FamilyParameterIndexBoundary.IndexDomainChain.length,
        List.length_drop, storedLength]
      omega
    alignment := {
      base := completion.prefixes.firstParameterΔ
      reference := completion.alignment.reference
      lift := completion.alignment.rootLift
      rootLift := completion.alignment.rootLift
      originLift := completion.alignment.originLift
      base_shape := completion.prefixes.first_shape
      terminal_shape := terminalShape
      relation := relation
      reference_lift := completion.alignment.root_reference_lift
      root_reference_lift := completion.alignment.root_reference_lift
      origin_reference_lift := completion.alignment.origin_reference_lift
      current_reference := by
        simpa only [chain,
          TypeChecker.FamilyParameterIndexBoundary.IndexDomainChain.endpoint] using
          currentReference
      sort := viewLevel
      endpoint_sort := by
        simpa only [chain,
          TypeChecker.FamilyParameterIndexBoundary.IndexDomainChain.endpoint] using
          endpointSort } }⟩

/-- Uniform endpoint package for one canonical later family.  The stored
terminal-inclusive candidate suffix is shared by the indexed and zero-index
branches; downstream source-order iteration consumes only this interface. -/
structure
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyDomainCompletion
    {source : VInductDecl}
    {firstSource secondSource nextSource : InductiveType}
    {laterSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: nextSource :: laterSources) numNested
      isUnsafe context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    {completion : staging.TerminalIndexDomainCompletion raw}
    {cursor : completion.RemainingFamilyValidationCursor}
    (next : cursor.NextFamilyStaging)
    (parameter : cursor.NextFamilyParameterBoundary next) where
  candidate : cursor.NextFamilyCandidateParameterSuffix next
  chain : parameter.boundary.IndexDomainChain
  chain_length : chain.length =
    (next.annotations.head.storedBinders.drop source.nparams).length
  alignment : chain.EndpointAlignment env Us
    next.annotations.head.terminalRun.context.vlctx
    completion.prefixes.firstParameterΔ
    staging.annotation.firstTerminalRun.context.vlctx

/-- Complete the canonical later family regardless of whether its parameter
boundary exposes an index Pi or its terminal sort. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.domainCompletion
    {source : VInductDecl}
    {firstSource secondSource nextSource : InductiveType}
    {laterSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: nextSource :: laterSources) numNested
      isUnsafe context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    {completion : staging.TerminalIndexDomainCompletion raw}
    {cursor : completion.RemainingFamilyValidationCursor}
    (next : cursor.NextFamilyStaging)
    (parameter : cursor.NextFamilyParameterBoundary next)
    (context_lctx_eq : context.lctx = {}) :
    Nonempty (cursor.NextFamilyDomainCompletion next parameter) := by
  obtain ⟨candidate⟩ := next.candidateParameterSuffix
  rcases Nat.lt_or_eq_of_le next.nparams_le_spineLength with hasIndex |
      noIndices
  · obtain ⟨indexed⟩ := next.indexDomainCompletion parameter candidate
      context_lctx_eq hasIndex
    exact ⟨{
      candidate := candidate
      chain := indexed.chain
      chain_length := indexed.chain_length
      alignment := indexed.alignment }⟩
  · obtain ⟨zero⟩ := next.zeroIndexDomainCompletion parameter candidate
      context_lctx_eq noIndices
    exact ⟨{
      candidate := candidate
      chain := zero.chain
      chain_length := zero.chain_length
      alignment := zero.alignment }⟩

/-- The uniform later-family completion with its exact validator terminal
witness attached. -/
structure
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.TerminalDomainCompletion
    {source : VInductDecl}
    {firstSource secondSource nextSource : InductiveType}
    {laterSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: nextSource :: laterSources) numNested
      isUnsafe context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    {completion : staging.TerminalIndexDomainCompletion raw}
    {cursor : completion.RemainingFamilyValidationCursor}
    (next : cursor.NextFamilyStaging)
    (parameter : cursor.NextFamilyParameterBoundary next)
    extends cursor.NextFamilyDomainCompletion next parameter where
  terminal : toNextFamilyDomainCompletion.chain.endpoint.boundary.Terminal

/-- Attach the exact terminal constructor to a completed canonical later
family. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.terminalDomainCompletion
    {source : VInductDecl}
    {firstSource secondSource nextSource : InductiveType}
    {laterSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: nextSource :: laterSources) numNested
      isUnsafe context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    {completion : staging.TerminalIndexDomainCompletion raw}
    {cursor : completion.RemainingFamilyValidationCursor}
    (next : cursor.NextFamilyStaging)
    (parameter : cursor.NextFamilyParameterBoundary next)
    (context_lctx_eq : context.lctx = {}) :
    Nonempty (next.TerminalDomainCompletion parameter) := by
  obtain ⟨domain⟩ := next.domainCompletion parameter context_lctx_eq
  have henv : VEnv.WF env := by
    have currentVenv : next.currentRun.context.venv = env :=
      cursor.cursor.headContextRun_venv next.continuation next.selected
    simpa only [currentVenv] using next.currentRun.context.Ewf
  obtain ⟨terminal⟩ := domain.alignment.terminal henv
  exact ⟨{
    toNextFamilyDomainCompletion := domain
    terminal := terminal }⟩

/-- Exact verified context reached after the canonical later family's complete
telescope. -/
def
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.TerminalDomainCompletion.terminalRun
    {source : VInductDecl}
    {firstSource secondSource nextSource : InductiveType}
    {laterSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: nextSource :: laterSources) numNested
      isUnsafe context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    {completion : staging.TerminalIndexDomainCompletion raw}
    {cursor : completion.RemainingFamilyValidationCursor}
    {next : cursor.NextFamilyStaging}
    {parameter : cursor.NextFamilyParameterBoundary next}
    (domain : next.TerminalDomainCompletion parameter) :
    TypeChecker.CandidateContextRun next.continuation.telescope.result.context :=
  domain.chain.endpointContextRun domain.terminal

/-- The completed later-family endpoint retains the semantic environment. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.TerminalDomainCompletion.terminal_venv
    {source : VInductDecl}
    {firstSource secondSource nextSource : InductiveType}
    {laterSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: nextSource :: laterSources) numNested
      isUnsafe context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    {completion : staging.TerminalIndexDomainCompletion raw}
    {cursor : completion.RemainingFamilyValidationCursor}
    {next : cursor.NextFamilyStaging}
    {parameter : cursor.NextFamilyParameterBoundary next}
    (domain : next.TerminalDomainCompletion parameter) :
    domain.terminalRun.context.venv = env := by
  exact (domain.chain.endpointContextRun_venv domain.terminal).trans
    (cursor.cursor.headContextRun_venv next.continuation next.selected)

/-- The completed later-family endpoint retains the semantic universe
parameters. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.TerminalDomainCompletion.terminal_lparams
    {source : VInductDecl}
    {firstSource secondSource nextSource : InductiveType}
    {laterSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: nextSource :: laterSources) numNested
      isUnsafe context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    {completion : staging.TerminalIndexDomainCompletion raw}
    {cursor : completion.RemainingFamilyValidationCursor}
    {next : cursor.NextFamilyStaging}
    {parameter : cursor.NextFamilyParameterBoundary next}
    (domain : next.TerminalDomainCompletion parameter) :
    domain.terminalRun.context.lparams = Us := by
  exact (domain.chain.endpointContextRun_lparams domain.terminal).trans
    (cursor.cursor.headContextRun_lparams next.continuation next.selected)

/-- Reindexing the aligned endpoint onto the outer family result preserves
its exact shared reference. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.TerminalDomainCompletion.current_reference
    {source : VInductDecl}
    {firstSource secondSource nextSource : InductiveType}
    {laterSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: nextSource :: laterSources) numNested
      isUnsafe context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    {completion : staging.TerminalIndexDomainCompletion raw}
    {cursor : completion.RemainingFamilyValidationCursor}
    {next : cursor.NextFamilyStaging}
    {parameter : cursor.NextFamilyParameterBoundary next}
    (domain : next.TerminalDomainCompletion parameter) :
    VLCtx.IsDefEq env Us.length domain.terminalRun.context.vlctx
      domain.alignment.reference := by
  have terminalContextEq : domain.terminalRun.context =
      domain.chain.endpoint.contextRun.context := by
    unfold terminalRun
      TypeChecker.FamilyParameterIndexBoundary.IndexDomainChain.endpointContextRun
    apply TypeChecker.CandidateContextRun.cast_context_context
  rw [terminalContextEq]
  exact domain.alignment.current_reference

/-- Advance the source-order validator/semantic cursor through one completed
later family. -/
def
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.TerminalDomainCompletion.advance
    {source : VInductDecl}
    {firstSource secondSource nextSource : InductiveType}
    {laterSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: nextSource :: laterSources) numNested
      isUnsafe context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    {completion : staging.TerminalIndexDomainCompletion raw}
    {cursor : completion.RemainingFamilyValidationCursor}
    {next : cursor.NextFamilyStaging}
    {parameter : cursor.NextFamilyParameterBoundary next}
    (domain : next.TerminalDomainCompletion parameter) :
    CandidateBlockLaterFamilyValidationCursor env blockEnv Us source.nparams
      (firstSource :: secondSource :: nextSource :: laterSources)
      staging.annotation.remainingCandidates.tail
      staging.annotation.remainingRaws.tail next.continuation.tail :=
  cursor.cursor.advanceHead next.continuation next.selected next.invariant
    domain.terminalRun domain.terminal_venv domain.terminal_lparams

/-- Thread every recursion invariant through one completed later family and
produce the exact source-order state for the remaining suffix. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.TerminalDomainCompletion.advanceIterationCursor
    {source : VInductDecl}
    {firstSource secondSource nextSource : InductiveType}
    {laterSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {produced : ProducedBlockRecursorShapeCandidate source
      (firstSource :: secondSource :: nextSource :: laterSources) numNested
      isUnsafe context}
    {env blockEnv : VEnv} {Us : List Name}
    {semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      produced.candidate source}
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    {completion : staging.TerminalIndexDomainCompletion raw}
    {cursor : completion.RemainingFamilyValidationCursor}
    {next : cursor.NextFamilyStaging}
    {parameter : cursor.NextFamilyParameterBoundary next}
    (domain : next.TerminalDomainCompletion parameter) :
    Nonempty (completion.LaterFamilyIterationCursor
      staging.annotation.remainingCandidates.tail
      staging.annotation.remainingRaws.tail next.continuation.tail) := by
  have parameterSources : domain.advance.parameterSources =
      staging.annotation.firstCandidate.familyType.type.trace.parameterList
        source.nparams := by
    calc
      domain.advance.parameterSources = cursor.cursor.parameterSources := by
        unfold advance
        exact cursor.cursor.advanceHead_parameterSources next.continuation
          next.selected next.invariant domain.terminalRun
          domain.terminal_venv domain.terminal_lparams
      _ = staging.annotation.firstCandidate.familyType.type.trace.parameterList
            source.nparams := cursor.parameterSources_eq_firstParameterList
  have candidateFuel :
      next.continuation.telescope.result.context.fuel = context.fuel := by
    calc
      next.continuation.telescope.result.context.fuel =
          next.continuation.context.fuel :=
        next.continuation.telescope.result_context_fuel
      _ = cursor.validation.continuation.telescope.result.context.fuel :=
        congrArg AddInductive.Context.fuel
          (AddInductive.FamilyParameterComparisonBlockTrace.headContinuation?_context
            next.selected)
      _ = context.fuel := cursor.cursor_fuel_eq
  have firstTerminalFind : ∀ {fv : FVarId} {decl : LocalDecl},
      staging.annotation.firstCandidate.familyType.type.trace.terminalContext.lctx.find?
            fv = some decl →
        next.continuation.telescope.result.context.lctx.find? fv =
          some decl := by
    intro fv decl found
    have currentFound : next.continuation.context.lctx.find? fv =
        some decl := by
      rw [AddInductive.FamilyParameterComparisonBlockTrace.headContinuation?_context
        next.selected]
      exact cursor.firstTerminal_find found
    have resultFound := parameter.boundary.trace.result_findOld
      parameter.boundary.localState.localContext currentFound
    simpa only [parameter.boundary.result_eq] using resultFound
  have currentReference : VLCtx.IsDefEq env Us.length
      domain.advance.contextRun.context.vlctx
      domain.alignment.reference := by
    unfold advance
    rw [cursor.cursor.advanceHead_context next.continuation next.selected
      next.invariant domain.terminalRun domain.terminal_venv
      domain.terminal_lparams]
    exact domain.current_reference
  have advanceSemantics : domain.advance.semantics =
      cursor.cursor.semantics.tailExact := by
    unfold advance
    exact cursor.cursor.advanceHead_semantics next.continuation next.selected
      next.invariant domain.terminalRun domain.terminal_venv
      domain.terminal_lparams
  let tailPackage : Sigma fun shapes =>
      CandidateBlockFamilyAnnotationSpineList source env blockEnv Us
        domain.advance.semantics shapes := by
    rw [advanceSemantics]
    exact ⟨cursor.generationShapes.tailExact,
      next.annotations.tailExact⟩
  exact ⟨{
    cursor := domain.advance
    validation := next.validation.tail
    parameterSpines := staging.annotation.remainingParameterSpines.tail
    generationShapes := tailPackage.1
    annotations := tailPackage.2
    parameterSources_eq_firstParameterList := parameterSources
    candidate_fuel_eq := candidateFuel
    firstTerminal_find := firstTerminalFind
    reference := domain.alignment.reference
    rootLift := domain.alignment.rootLift
    originLift := domain.alignment.originLift
    root_reference_lift := domain.alignment.root_reference_lift
    origin_reference_lift := domain.alignment.origin_reference_lift
    current_reference := currentReference }⟩

/-- Every remaining source root is translated at the exact second-family
terminal context, rather than merely at an extensionally similar root
context. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.sourceTranslations
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
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    {completion : staging.TerminalIndexDomainCompletion raw}
    (cursor : completion.RemainingFamilyValidationCursor) :
    List.Forall₂
      (fun source raw =>
        completion.terminalRun.context.TrExprS source.type raw.type)
      remainingSources staging.annotation.remainingRaws := by
  have translated := cursor.cursor.sourceTranslations
  rw [cursor.context_eq_terminal] at translated
  exact translated

/-- The exact retained validator suffix contains one comparison group for
every semantic family still to be consumed. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.comparisons_length
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
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    {completion : staging.TerminalIndexDomainCompletion raw}
    (cursor : completion.RemainingFamilyValidationCursor) :
    cursor.validation.continuation.tail.comparisons.length =
      remainingSources.length :=
  cursor.cursor.toCandidateBlockFamilyValidationCursor.comparisons_length

/-- Whenever a remaining family exists, the cursor exposes its exact
dependent outer continuation and the invariant required by the following
tail. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.headContinuation
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
    {staging : produced.SecondFamilyIndexStaging semantic}
    {raw : staging.annotation.RawFirstIndexDomain}
    {completion : staging.TerminalIndexDomainCompletion raw}
    (cursor : completion.RemainingFamilyValidationCursor)
    (nonempty : remainingSources.isEmpty = false) :
    ∃ continuation,
      cursor.validation.continuation.tail.headContinuation? =
        some continuation ∧
      continuation.LaterInvariant :=
  cursor.cursor.headContinuation nonempty

/-- Consume the complete second-family producer index suffix through the
validator's retained trace.  The initial alpha cursor is recovered from the
shared parameter telescope and then maintained by `indexDomainChain`. -/
theorem ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.indexDomainCompletion
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
    (context_lctx_eq : context.lctx = {}) :
    Nonempty (staging.IndexDomainCompletion raw) := by
  obtain ⟨prefixes⟩ :=
    staging.rawFirstIndexPrefixContexts raw context_lctx_eq
  obtain ⟨resultLevel, terminalEq⟩ := staging.annotation.terminal_sort
  obtain ⟨suffix⟩ := staging.annotation.annotation_spine.positionSuffix
    .nil staging.annotation.stored_spine
    staging.annotation.validation_annotations terminalEq
    prefixes.position
  have cursorContext : suffix.cursor.Δ.toCtx =
      (staging.annotation.storedBinders.take source.nparams).reverse := by
    simpa only [VLCtx.toCtx, List.append_nil] using suffix.context_eq
  have parameterTelescope :=
    staging.parameterTelescopeDefEq raw prefixes context_lctx_eq
  have parameterContext : env.IsDefEqCtx Us.length []
      prefixes.firstParameterΔ.toCtx suffix.cursor.Δ.toCtx := by
    simpa only [List.append_nil, prefixes.first_context, cursorContext] using
      parameterTelescope.ctx
  have relation : VLCtx.FVarAlpha env Us.length
      prefixes.firstParameterΔ suffix.cursor.Δ :=
    VLCtx.FVarAlpha.of_defeqCtx prefixes.first_shape suffix.cursor.shape
      parameterContext
  have mappedFVars : prefixes.firstParameterΔ.fvars.map Expr.fvar =
      suffix.cursor.Δ.fvars.map Expr.fvar := by
    calc
      prefixes.firstParameterΔ.fvars.map Expr.fvar =
          (staging.annotation.firstCandidate.familyType.type.trace
            |>.parameterList source.nparams).reverse := prefixes.first_fvars
      _ = (staging.annotation.secondCandidate.familyType.type.trace
            |>.parameterList source.nparams).reverse :=
        congrArg List.reverse
          (staging.annotation.parameterLists_eq context_lctx_eq)
      _ = suffix.cursor.Δ.fvars.map Expr.fvar := by
        have suffixFVars := suffix.fvars_eq
        change suffix.cursor.Δ.fvars.map Expr.fvar =
          (staging.annotation.secondCandidate.familyType.type.trace
            |>.parameterList source.nparams).reverse ++ [] at suffixFVars
        simpa only [List.append_nil] using suffixFVars.symm
  have cursorFVars : prefixes.firstParameterΔ.fvars =
      suffix.cursor.Δ.fvars :=
    list_map_fvar_injective mappedFVars
  have sourceScope : staging.boundary.source.FVarsIn
      (· ∈ prefixes.firstParameterΔ.fvars) := by
    rw [prefixes.boundary_root_eq, prefixes.snapshot.root_eq]
    exact ⟨by
        simpa only [prefixes.parameter_fvars_eq] using
          prefixes.snapshot.domain_tr.fvarsIn,
      by
        simpa only [prefixes.parameter_fvars_eq] using
          prefixes.snapshot.body_fvars⟩
  have sourceAlpha : Lean.Expr.abstractFVars prefixes.firstParameterΔ
      staging.boundary.source =
      Lean.Expr.abstractFVars suffix.cursor.Δ
        suffix.cursor.trace.rootWhnf := by
    rw [prefixes.boundary_root_eq, suffix.root_eq]
    simp only [Lean.Expr.abstractFVars, cursorFVars]
  have terminalWF : VLCtx.WF env Us.length
      staging.annotation.terminalRun.context.vlctx := by
    simpa only [staging.annotation.terminal_venv,
      staging.annotation.terminal_lparams] using
      staging.annotation.terminalRun.context.Δwf
  have validatorDepth : staging.position.context.fuel.recDepth =
      staging.annotation.whnfFuel + 1 := by
    calc
      staging.position.context.fuel.recDepth = context.fuel.recDepth :=
        congrArg (fun fuel => fuel.recDepth) staging.position_fuel_eq
      _ = ({ context with lctx := {} } : AddInductive.Context).fuel.recDepth :=
        rfl
      _ = staging.annotation.secondCandidate.familyType.type.context.fuel.recDepth :=
        (congrArg (fun candidateContext => candidateContext.fuel.recDepth)
          staging.annotation.second_candidate_context_eq).symm
      _ = staging.annotation.whnfFuel + 1 := staging.annotation.whnfDepth
  have candidateDepth : suffix.cursor.candidateContext.fuel.recDepth =
      staging.annotation.whnfFuel + 1 := by
    calc
      suffix.cursor.candidateContext.fuel.recDepth =
          staging.annotation.secondCandidate.familyType.type.context.fuel.recDepth :=
        congrArg (fun fuel => fuel.recDepth) suffix.fuel_eq
      _ = staging.annotation.whnfFuel + 1 := staging.annotation.whnfDepth
  obtain ⟨⟨chain, alignment⟩⟩ :=
    suffix.cursor.indexDomainChainAligned terminalWF staging.boundary
      staging.current_venv staging.current_lparams prefixes.first_shape
      relation prefixes.first_terminal_lift prefixes.first_terminal_lift
      VLCtx.FVLift'.refl prefixes.current_firstTerminal_defeq sourceScope
      sourceAlpha
      staging.annotation.whnfFuel validatorDepth candidateDepth
  exact ⟨{
    prefixes := prefixes
    chain := chain
    chain_length := alignment.property.trans
      (congrArg List.length suffix.domains_eq)
    alignment := alignment.val }⟩

/-- The complete producer suffix reaches the validator's exact terminal node,
so the aligned endpoint is immediately usable as the source-order family
continuation. -/
theorem
    ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.terminalIndexDomainCompletion
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
    (context_lctx_eq : context.lctx = {}) :
    Nonempty (staging.TerminalIndexDomainCompletion raw) := by
  obtain ⟨completion⟩ :=
    staging.indexDomainCompletion raw context_lctx_eq
  have henv : VEnv.WF env := by
    simpa only [staging.current_venv] using staging.currentRun.context.Ewf
  obtain ⟨terminal⟩ := completion.alignment.terminal henv
  exact ⟨{
    toIndexDomainCompletion := completion
    terminal := terminal }⟩

/-- Compatibility projection of the endpoint-aligned second-family run. -/
theorem ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.indexDomainChain
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
    (context_lctx_eq : context.lctx = {}) :
    Nonempty staging.boundary.IndexDomainChain := by
  obtain ⟨completion⟩ := staging.indexDomainCompletion raw context_lctx_eq
  exact ⟨completion.chain⟩

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.terminal_sort' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.terminal_sort

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.terminal_notForall' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.terminal_notForall

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.indexDomainCompletion' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.indexDomainCompletion

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.terminalIndexDomainCompletion' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.terminalIndexDomainCompletion

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.indexDomainChain' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.indexDomainChain

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.validationContinuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.validationContinuation

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.continuation_reference' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.continuation_reference

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.remainingFamilyValidationCursor' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.remainingFamilyValidationCursor

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.contextRun_eq_terminal' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.contextRun_eq_terminal

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.contextRun_fuel_eq' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.contextRun_fuel_eq

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.parameterSources_eq_firstParameterList' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.parameterSources_eq_firstParameterList

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.generationShapes' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.generationShapes

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.annotationSpines' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.annotationSpines

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.nextFamilyStaging' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.nextFamilyStaging

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.rootWhnf' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.rootWhnf

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.whnfDepth' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.whnfDepth

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.parameterBoundary' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.parameterBoundary

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.nparams_le_spineLength' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.nparams_le_spineLength

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.firstCandidate_context_eq' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.firstCandidate_context_eq

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.parameterLists_eq' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.parameterLists_eq

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyParameterBoundary.parameterSources_eq_candidateParameterList' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyParameterBoundary.parameterSources_eq_candidateParameterList

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.sourceTranslations' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.sourceTranslations

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.comparisons_length' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.comparisons_length

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.headContinuation' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.headContinuation

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.parameterTelescopeDefEq' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.parameterTelescopeDefEq

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.indexDomainCompletion' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.indexDomainCompletion

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.zeroIndexDomainCompletion' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.zeroIndexDomainCompletion

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.domainCompletion' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.domainCompletion

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.terminalDomainCompletion' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.terminalDomainCompletion

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.TerminalDomainCompletion.terminalRun' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.TerminalDomainCompletion.terminalRun

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.TerminalDomainCompletion.advance' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.TerminalIndexDomainCompletion.RemainingFamilyValidationCursor.NextFamilyStaging.TerminalDomainCompletion.advance

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.parameterTelescopeDefEq' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.parameterTelescopeDefEq

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.firstIndexDomainRun' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.firstIndexDomainRun

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.second_candidate_context_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  ProducedBlockRecursorShapeCandidate.SecondFamilyAnnotationSpine.second_candidate_context_eq

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.rawFirstIndexAnnotationAlignment' depends on axioms: [propext,
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
  ProducedBlockRecursorShapeCandidate.SecondFamilyIndexStaging.rawFirstIndexAnnotationAlignment


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
