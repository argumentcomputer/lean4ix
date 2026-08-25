import Lean4Lean.Verify.Environment.Normalization
import Lean4Lean.Verify.Environment.Readiness

namespace Lean4Lean

open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

namespace VInductDecl

/-- A successful family-only declaration trace preserves projection and
structure-eta readiness when every inserted family has multiple constructors.
The exact Theory staging fold supplies both the monotone model extension and
the ordered intermediate environments used to transport registered eta
artifacts. -/
theorem declarationTraceMultiConstructorReadiness
    {allowPrimitive : Bool} {kernelEnv finalKernelEnv : Environment}
    {infos : List InductiveVal} {env blockEnv : VEnv}
    {raws : List VInductiveType}
    (declare : AddInductive.DeclareInductiveInfoListRun allowPrimitive
      kernelEnv infos finalKernelEnv)
    (stage : env.stageInductiveTypes raws = some blockEnv)
    (evidence : List.Forall₂
      (fun _ raw => raw.toVConstant.WF env) infos raws)
    (multi : ∀ info ∈ infos, info.ctors.length ≠ 1)
    (mapWF : kernelEnv.constants.WF)
    (preOrd : env.Ordered)
    (preProjection : ProjectionReady kernelEnv env)
    (preEta : StructureEtaReady kernelEnv env) :
    ProjectionReady finalKernelEnv blockEnv ∧
      StructureEtaReady finalKernelEnv blockEnv := by
  induction declare generalizing env blockEnv raws with
  | nil =>
      cases evidence
      change some env = some blockEnv at stage
      cases stage
      exact ⟨preProjection, preEta⟩
  | @cons infos finalKernelEnv kernelEnv info check tail ih =>
      cases evidence with
      | cons head rest =>
          rename_i raw raws
          simp only [VEnv.stageInductiveTypes, List.foldlM_cons] at stage
          obtain ⟨nextEnv, added, tailStage⟩ :=
            Option.bind_eq_some_iff.mp stage
          have checkWF := checkName.WF mapWF info.name allowPrimitive
          have fresh : kernelEnv.find? info.name = none :=
            (checkWF () check).1
          have nextMapWF :
              (kernelEnv.add (.inductInfo info)).constants.WF :=
            mapWF.insert _ _ (by
              change kernelEnv.constants.find? info.name = none
              rw [← mapWF.find?'_eq_find?]
              exact fresh)
          have le : env ≤ nextEnv := VEnv.addConst_le added
          have nextOrd : nextEnv.Ordered := .const preOrd head added
          have postProjection := preProjection.addInductInfo mapWF info
            fresh (multi info (.head _)) le
          have postEta := preEta.addInductInfo mapWF info fresh
            (multi info (.head _)) le nextOrd
          have rest' : List.Forall₂
              (fun _ raw => raw.toVConstant.WF nextEnv) infos raws :=
            Lean4Lean.List.Forall₂.imp (h := rest) fun _ _ h => h.mono le
          exact ih tailStage rest'
            (by
              intro other member
              exact multi other (.tail _ member))
            nextMapWF nextOrd postProjection postEta

/-- A successful family-only declaration trace preserves readiness for an
arbitrary block when every constructor named by newly staged family metadata
is still absent at the final family-only host endpoint.  Multi-constructor
families use the shape shortcut; singleton families use that exact absence to
show that no projection or structure-eta artifact has activated early. -/
theorem declarationTraceConstructorAbsentReadiness
    {allowPrimitive : Bool} {kernelEnv finalKernelEnv : Environment}
    {infos : List InductiveVal} {env blockEnv : VEnv}
    {raws : List VInductiveType}
    (declare : AddInductive.DeclareInductiveInfoListRun allowPrimitive
      kernelEnv infos finalKernelEnv)
    (stage : env.stageInductiveTypes raws = some blockEnv)
    (evidence : List.Forall₂
      (fun _ raw => raw.toVConstant.WF env) infos raws)
    (constructorsAbsent : ∀ info ∈ infos, ∀ ctor ∈ info.ctors,
      finalKernelEnv.find? ctor = none)
    (mapWF : kernelEnv.constants.WF)
    (preOrd : env.Ordered)
    (preProjection : ProjectionReady kernelEnv env)
    (preEta : StructureEtaReady kernelEnv env) :
    ProjectionReady finalKernelEnv blockEnv ∧
      StructureEtaReady finalKernelEnv blockEnv := by
  induction declare generalizing env blockEnv raws with
  | nil =>
      cases evidence
      change some env = some blockEnv at stage
      cases stage
      exact ⟨preProjection, preEta⟩
  | @cons infos finalKernelEnv kernelEnv info check tail ih =>
      cases evidence with
      | cons head rest =>
          rename_i raw raws
          simp only [VEnv.stageInductiveTypes, List.foldlM_cons] at stage
          obtain ⟨nextEnv, added, tailStage⟩ :=
            Option.bind_eq_some_iff.mp stage
          have checkWF := checkName.WF mapWF info.name allowPrimitive
          have fresh : kernelEnv.find? info.name = none :=
            (checkWF () check).1
          have nextMapWF :
              (kernelEnv.add (.inductInfo info)).constants.WF :=
            mapWF.insert _ _ (by
              change kernelEnv.constants.find? info.name = none
              rw [← mapWF.find?'_eq_find?]
              exact fresh)
          have finalMapWF :=
            (AddInductive.DeclareInductiveInfoListRun.cons check tail).map_wf
              mapWF
          have constructorAbsentAtInput : ∀ ctor ∈ info.ctors,
              kernelEnv.find? ctor = none := by
            intro ctor ctorMember
            cases oldFind : kernelEnv.find? ctor with
            | none => rfl
            | some found =>
                have oldMap : kernelEnv.constants.find? ctor = some found := by
                  change kernelEnv.constants.find?' ctor = _ at oldFind
                  rwa [mapWF.find?'_eq_find?] at oldFind
                have finalMap : finalKernelEnv.constants.find? ctor =
                    some found :=
                  (AddInductive.DeclareInductiveInfoListRun.cons check tail)
                    |>.preserve_map_lookup mapWF oldMap
                have finalFind : finalKernelEnv.find? ctor = some found := by
                  change finalKernelEnv.constants.find?' ctor = _
                  rw [finalMapWF.find?'_eq_find?]
                  exact finalMap
                rw [constructorsAbsent info (.head _) ctor ctorMember]
                  at finalFind
                contradiction
          have le : env ≤ nextEnv := VEnv.addConst_le added
          have nextOrd : nextEnv.Ordered := .const preOrd head added
          have postReadiness :
              ProjectionReady (kernelEnv.add (.inductInfo info)) nextEnv ∧
                StructureEtaReady (kernelEnv.add (.inductInfo info))
                  nextEnv := by
            by_cases singleton : info.ctors.length = 1
            · obtain ⟨ctor, hctors⟩ := List.length_eq_one_iff.mp singleton
              have ctorAbsent := constructorAbsentAtInput ctor (by
                rw [hctors]
                simp)
              exact ⟨preProjection.addInductInfo_of_ctor_absent mapWF info
                  fresh ctor hctors ctorAbsent le,
                preEta.addInductInfo_of_ctor_absent mapWF info fresh ctor
                  hctors ctorAbsent le nextOrd⟩
            · exact ⟨preProjection.addInductInfo mapWF info fresh singleton le,
                preEta.addInductInfo mapWF info fresh singleton le nextOrd⟩
          have rest' : List.Forall₂
              (fun _ raw => raw.toVConstant.WF nextEnv) infos raws :=
            Lean4Lean.List.Forall₂.imp (h := rest) fun _ _ h => h.mono le
          exact ih tailStage rest'
            (by
              intro other member ctor ctorMember
              exact constructorsAbsent other (.tail _ member) ctor
                ctorMember)
            nextMapWF nextOrd postReadiness.1 postReadiness.2

end VInductDecl

end Lean4Lean
