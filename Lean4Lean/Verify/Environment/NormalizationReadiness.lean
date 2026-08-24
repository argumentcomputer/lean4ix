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

end VInductDecl

end Lean4Lean
