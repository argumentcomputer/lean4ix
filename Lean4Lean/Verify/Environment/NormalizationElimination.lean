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
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · simp [ConstantInfo.safety, ConstantInfo.isUnsafe,
      ConstantInfo.isPartial, AddInductive.declaredConstructorInfo, safe]
  · simpa [ConstantInfo.toConstantVal, ConstantInfo.levelParams,
      AddInductive.declaredConstructorInfo, lparams_eq] using
        run.uvars_eq.symm
  · simpa [ConstantInfo.toConstantVal, ConstantInfo.levelParams,
      ConstantInfo.type, AddInductive.declaredConstructorInfo,
      lparams_eq] using run.type.source_tr
  · simpa [ConstantInfo.toConstantVal, ConstantInfo.name,
      AddInductive.declaredConstructorInfo] using run.name_eq

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
  induction infos generalizing kernelEnv finalKernelEnv typeEnv raws with
  | nil =>
      cases raws with
      | nil =>
          simp only [AddInductive.declareConstructorInfoList,
            Except.ok.injEq] at declare
          subst finalKernelEnv
          exact {
            ctorEnv := typeEnv
            kernelTrace := .nil
            addCtors := .nil
            trenv := pre }
      | cons raw raws =>
          have impossible : False := by cases evidence
          exact impossible.elim
  | cons info infos ih =>
      cases raws with
      | nil =>
          have impossible : False := by cases evidence
          exact impossible.elim
      | cons raw raws =>
          have aligned := constructor_forall₂_cons_iff.mp evidence
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
                rw [← aligned.1.2]
                simpa [ConstantInfo.toConstantVal, ConstantInfo.name] using
                  checkName_constants_fresh hcheck
              have envFresh : typeEnv.constants raw.name = none := by
                cases found : typeEnv.constants raw.name with
                | none => rfl
                | some ci =>
                    obtain ⟨kernelInfo, kernelFound, _⟩ :=
                      pre.aligned.find?_iff.mpr ⟨ci, found⟩
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
              have add : AddInductConstant .ctor kernelEnv.constants typeEnv raw
                  (kernelEnv.add (.ctorInfo info)).constants nextEnv := {
                info := .ctorInfo info
                kind_eq := trivial
                tr := aligned.1
                map_fresh := mapFresh
                env_add := added
                map_add := by
                  rw [← aligned.1.2]
                  rfl }
              have headWF : raw.toVConstant.WF typeEnv :=
                rawsWF raw (.head _)
              have post : TrEnv' .safe
                  (kernelEnv.add (.ctorInfo info)).constants Q nextEnv :=
                .inductStaging add headWF pre
              have le : typeEnv ≤ nextEnv := VEnv.addConst_le added
              have tailEvidence : List.Forall₂
                  (fun info raw =>
                    TrConstVal .safe nextEnv (.ctorInfo info) raw)
                  infos raws :=
                Lean4Lean.List.Forall₂.imp (h := aligned.2)
                  (fun _ _ relation => relation.mono le)
              have tailWF : ∀ other ∈ raws,
                  other.toVConstant.WF nextEnv := by
                intro other member
                exact (rawsWF other (.tail _ member)).mono le
              let tailResult := ih tailDeclare tailEvidence tailWF post
              exact {
                ctorEnv := tailResult.ctorEnv
                kernelTrace := .cons hcheck tailResult.kernelTrace
                addCtors := .cons add tailResult.addCtors
                trenv := tailResult.trenv }

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
            recK := by simp [RecursorMapKMatches]
            trenv := pre }
      | cons raw raws =>
          have impossible : False := by cases evidence
          exact impossible.elim
  | cons info infos ih =>
      cases raws with
      | nil =>
          have impossible : False := by cases evidence
          exact impossible.elim
      | cons raw raws =>
          have aligned := constructor_forall₂_cons_iff.mp evidence
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
                rw [← aligned.1.2]
                simpa [ConstantInfo.toConstantVal, ConstantInfo.name] using
                  checkName_constants_fresh hcheck
              have envFresh : ctorEnv.constants raw.name = none := by
                cases found : ctorEnv.constants raw.name with
                | none => rfl
                | some ci =>
                    obtain ⟨kernelInfo, kernelFound, _⟩ :=
                      pre.aligned.find?_iff.mpr ⟨ci, found⟩
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
              let add : AddInductConstant .recursor kernelEnv.constants ctorEnv raw
                  (kernelEnv.add (.recInfo info)).constants nextEnv := {
                info := .recInfo info
                kind_eq := trivial
                tr := aligned.1
                map_fresh := mapFresh
                env_add := added
                map_add := by
                  rw [← aligned.1.2]
                  rfl }
              have headWF : raw.toVConstant.WF ctorEnv :=
                rawsWF raw (.head _)
              have post : TrEnv' .safe
                  (kernelEnv.add (.recInfo info)).constants Q nextEnv :=
                .inductStaging add headWF pre
              have le : ctorEnv ≤ nextEnv := VEnv.addConst_le added
              have tailEvidence : List.Forall₂
                  (fun info raw =>
                    TrConstVal .safe nextEnv (.recInfo info) raw)
                  infos raws :=
                Lean4Lean.List.Forall₂.imp (h := aligned.2)
                  (fun _ _ relation => relation.mono le)
              have tailWF : ∀ other ∈ raws,
                  other.toVConstant.WF nextEnv := by
                intro other member
                exact (rawsWF other (.tail _ member)).mono le
              have tailInfosK : ∀ other ∈ infos,
                  other.k = kTarget := by
                intro other member
                exact infosK other (.tail _ member)
              let tailResult := ih tailDeclare tailEvidence tailInfosK tailWF post
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
                    · simpa [RecursorKMatches] using
                        infosK info (.head _)
                  · exact tailResult.recK candidate member
                trenv := tailResult.trenv }

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

theorem ProducedBlockRecursorShapeCandidate.eq_of_execution_eq
    (left right : ProducedBlockRecursorShapeCandidate source kernelSources
      numNested isUnsafe context)
    (execution_eq : left.execution = right.execution) : left = right := by
  cases left with
  | mk leftExecution leftProduced leftShape =>
      cases right with
      | mk rightExecution rightProduced rightShape =>
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

/-- Run the retained ordinary producer through recursor synthesis/declaration
and the unchanged complete generation-shape gate. -/
def produceBlockRecursorShapeCandidate
    (source : VInductDecl) (kernelSources : List InductiveType)
    (numNested : Nat) (isUnsafe : Bool)
    (context : AddInductive.Context) :
    Except Exception (ProducedBlockRecursorShapeCandidate source kernelSources
      numNested isUnsafe context) :=
  match producedExecution :
      AddInductive.NormalizationRecursorExecution.buildExecution source.nparams
        kernelSources numNested isUnsafe context with
  | .error error => .error error
  | .ok execution =>
      if shape : normalizationCandidateBlockGenerationShape source
          execution.candidate then
        .ok { execution, producedExecution, shape }
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
      execution.candidate = true) :
    (match result_eq : result with
    | .error error => Except.error error
    | .ok actual =>
      if actualShape : normalizationCandidateBlockGenerationShape source
          actual.candidate then
        Except.ok (show ProducedBlockRecursorShapeCandidate source
            kernelSources numNested isUnsafe context from {
          execution := actual
          producedExecution := toProducedExecution actual result_eq
          shape := actualShape })
      else
        Except.error (.other
          "recursor candidate block does not preserve the generation spine")) =
      Except.ok (show ProducedBlockRecursorShapeCandidate source kernelSources
          numNested isUnsafe context from {
        execution
        producedExecution := toProducedExecution execution result_ok
        shape }) := by
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
      execution.candidate = true) :
    produceBlockRecursorShapeCandidate source kernelSources numNested isUnsafe
        context = .ok { execution, producedExecution, shape } := by
  unfold produceBlockRecursorShapeCandidate
  exact produceBlockRecursorShapeCandidate_match_ok
    (result := AddInductive.NormalizationRecursorExecution.buildExecution
      source.nparams kernelSources numNested isUnsafe context)
    (toProducedExecution := fun _ result_eq => result_eq)
    producedExecution shape

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
    (nparams_eq : source.nparams = nparams)
    (shape : normalizationCandidateBlockGenerationShape source
      execution.candidate = true) :
    ProducedBlockRecursorShapeCandidate source kernelSources numNested
      isUnsafe context := by
  cases source with
  | mk uvars sourceNparams types =>
      simp only at nparams_eq ⊢
      subst nparams
      exact { execution, producedExecution, shape }

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
