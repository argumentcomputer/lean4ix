import Lean4Lean.Verify.Environment.Quotient
import Lean4Lean.Verify.Environment.NormalizationElimination
import Lean4Lean.Verify.Environment.PrimitiveRecursors

namespace Lean4Lean
open Lean4Lean
open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

theorem addAxiom.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env) (v : AxiomVal) :
    (addAxiom env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∃ ci' : VConstVal, ∀ safety,
        (ves.venv safety).AddConst safety (.axiomInfo v) ci'.toVConstant (ves'.venv safety) := by
  let checkSafety : DefinitionSafety := if v.isUnsafe then .unsafe else .safe
  have hsafety : checkSafety ≤ (ConstantInfo.axiomInfo v).safety := by
    cases v.isUnsafe <;> exact DefinitionSafety.le_rfl
  unfold addAxiom
  refine (checkConstantVal.WF wf (.axiomInfo v) false hsafety).run wf |>.bind fun _ h => ?_
  obtain ⟨ci', htr, hci, hn, hnonprim⟩ := h
  have ⟨ves', hwf, hstep⟩ := addConst.WF wf (.axiomInfo v) ci' checkSafety ?_ htr hci hn
    (by simp [Lean.ConstantInfo.ReadinessTransparent]) (hnonprim rfl)
    fun _ _ htr hci hadd old => ?_
  · exact .pure ⟨ves', hwf, ci', hstep⟩
  · intro safety _
    cases v.isUnsafe <;> cases safety <;> trivial
  · exact .axiom htr (by rwa [← old.map_wf.find?'_eq_find?]) hci hadd old

theorem addDefinition.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        (v.safety ≠ .unsafe → ∃ ci' : VDefVal, ∀ safety,
          (ves.venv safety).AddDef safety (.defnInfo v) ci' (ves'.venv safety)) := by
  unfold addDefinition; split
  · refine checkConstantVal.WF wf (.defnInfo v) false DefinitionSafety.unsafe_le
      |>.run wf |>.bind fun _ ⟨ci0, htr, hwfc, hn, hnonprim⟩ => ?_
    refine (checkNoMVarNoFVar.WF _ _ _).bind fun _ h => ?_
    have ⟨vesA, wfA, hstepA⟩ := addConst.WF wf (.axiomInfo { v with isUnsafe := true }) ci0
      .unsafe (fun _ => id) ⟨⟨DefinitionSafety.unsafe_le, htr.1.2.1, htr.1.2.2⟩, htr.2⟩
      hwfc hn (by simp [Lean.ConstantInfo.ReadinessTransparent]) (hnonprim rfl)
      fun _ _ htr' hci' hadd' old =>
        .axiom htr' (by rwa [← old.map_wf.find?'_eq_find?]) hci' hadd' old
    have hadd := (hstepA .unsafe).2.2
    refine checkBodyCore.WF (wfA.toVEnvAt .unsafe) (.defnDecl v)
      v.levelParams v.type v.value ci0.type (htr.1.2.2.mono (VEnv.addConst_le hadd)) h
      |>.run1 _ |>.bind fun _ h3 => ?_
    obtain ⟨value', hvalue, hvalueType⟩ := h3
    have hciWF : (⟨ci0, value'⟩ : VDefVal).WF (vesA.venv .unsafe) := by
      show (vesA.venv .unsafe).HasType ci0.uvars [] value' ci0.type
      rw [← htr.1.2.1]; exact hvalueType
    have ⟨ves', hwf', hmono'⟩ := addUnsafeDef.WF wf v ⟨ci0, value'⟩ (vesA.venv .unsafe)
      ‹_› htr hwfc hadd hvalue hciWF hn (hnonprim rfl)
    exact .pure ⟨ves', hwf', hmono', (nomatch · ‹_›)⟩
  refine (checkDefinition.WF wf v).run wf |>.bind
    fun _ ⟨allow, ci', hp, hu, ht, hname, hvalue, hci, hfresh, hnonprim⟩ => ?_
  have hle : v.safety ≤ .safe := DefinitionSafety.le_safe
  have hmono := wf.mono hle
  have htr : TrDefVal v.safety (ves.venv v.safety) (.defnInfo v) ci' := by
    refine ⟨⟨⟨?_, hu, ht.mono hmono⟩, hname⟩, hvalue.mono hmono⟩
    rw [ConstantInfo.defnInfo_safety]
    exact DefinitionSafety.le_rfl
  have ⟨ves', hwf, hstep⟩ := addDef.WF wf v ci' v.safety ?_ htr (hci.mono hmono) hfresh ?_ ?_
  · exact .pure ⟨ves', hwf, (hstep · |>.le), fun _ => ⟨ci', hstep⟩⟩
  · simp [ConstantInfo.defnInfo_safety]
  · intro hnamePrim; have := mt hnonprim; simp [hnamePrim] at this
    exact ⟨by rw [ConstantInfo.defnInfo_safety, hp.safe this], hp.no_level_params this⟩
  · intro safety base hvisible hadd
    have hs : safety ≤ v.safety := by simpa [ConstantInfo.defnInfo_safety] using hvisible
    have hsf : TrDefVal safety (ves.venv v.safety) (.defnInfo v) ci' :=
      ⟨⟨htr.1.1.sf_mono hs, htr.1.2⟩, htr.2⟩
    have hci' := hci.mono (hmono.trans (wf.mono hs))
    cases allow
    · exact (wf.hasPrimitives.addConst_of_not_primitive (hnonprim rfl) hadd).addDefEq
    · exact hp.preserves rfl (wf.mono DefinitionSafety.le_safe) wf.tr.wf wf.hasPrimitives
        (hsf.mono (wf.mono hs)) (hci.mono (hmono.trans (wf.mono hs))) hadd

theorem addTheorem.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env) (v : TheoremVal) :
    (addTheorem env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∃ ci' : VConstVal, ∀ safety,
        (ves.venv safety).AddConst safety (.thmInfo v) ci'.toVConstant (ves'.venv safety) := by
  refine (checkTheorem.WF wf v).run wf |>.bind fun _ h => ?_
  obtain ⟨ci', htr, hbody, hprop, hn, hnonprim⟩ := h
  have ⟨ves', hwf, hstep⟩ := addConst.WF wf (.thmInfo v) ci'.toVConstVal .safe
    (fun _ _ => DefinitionSafety.le_safe) htr.1 ⟨_, hprop⟩ hn
    (by simp [Lean.ConstantInfo.ReadinessTransparent]) hnonprim
    fun safety _ hheader _ hadd old => ?_
  · exact .pure ⟨ves', hwf, ci'.toVConstVal, hstep⟩
  have hle := wf.mono hheader.1
  have htr' : TrDefVal safety (ves.venv safety) (.thmInfo v) ci' :=
    ⟨⟨hheader, htr.1.2⟩, htr.2.mono hle⟩
  exact .thm htr' (by rwa [← old.map_wf.find?'_eq_find?]) (hbody.mono hle)
    (hprop.mono hle) hadd old

theorem addOpaque.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env) (v : OpaqueVal) :
    (addOpaque env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∃ ci' : VConstVal, ∀ safety,
        (ves.venv safety).AddConst safety (.opaqueInfo v) ci'.toVConstant (ves'.venv safety) := by
  let checkSafety : DefinitionSafety := if v.isUnsafe then .unsafe else .safe
  have hsafety : (ConstantInfo.opaqueInfo v).safety = checkSafety := by
    cases v.isUnsafe <;> rfl
  refine (checkOpaque.WF wf v).run wf |>.bind fun _ h => ?_
  obtain ⟨ci', hu, ht, hname, hvalue, hciC, hci, hfresh, hnonprim⟩ := h
  have hle : checkSafety ≤ .safe := DefinitionSafety.le_safe
  have hmono := wf.mono hle
  have htr : TrConstVal checkSafety (ves.venv checkSafety) (.opaqueInfo v) ci'.toVConstVal :=
    ⟨⟨hsafety.symm ▸ DefinitionSafety.le_rfl, hu, ht.mono hmono⟩, hname⟩
  have ⟨ves', hwf, hstep⟩ := addConst.WF wf (.opaqueInfo v) ci'.toVConstVal checkSafety ?_ htr
    (hciC.mono hmono) hfresh (by simp [Lean.ConstantInfo.ReadinessTransparent]) hnonprim
    fun safety _ htr hciW hadd old => ?_
  · exact .pure ⟨ves', hwf, ci'.toVConstVal, hstep⟩
  · intro safety hvisible
    rwa [hsafety] at hvisible
  · have hvis : safety ≤ checkSafety := hsafety ▸ htr.1
    have hto := hmono.trans (wf.mono hvis)
    exact .opaque (ci' := ci') ⟨⟨htr, hname⟩, hvalue.mono hto⟩
      (by rwa [← old.map_wf.find?'_eq_find?]) (hci.mono hto) hadd old

private theorem Except.WF.throw' {e : ε} {Q : α → Prop} : (throw e : Except ε α).WF Q :=
  fun _ h => nomatch h

private theorem Except.WF.throwBind {e : ε} {f : α → Except ε β} {Q : β → Prop} :
    ((throw e : Except ε α) >>= f).WF Q := fun _ h => nomatch h

theorem addMutual.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (vs : List DefinitionVal) :
    (addMutual env vs).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  unfold addMutual
  simp only [reduceIte]
  split <;> [rename_i _ v₀ rest; exact Except.WF.throw']
  split <;> [exact Except.WF.throwBind; skip]
  have hsf : v₀.safety ≤ (if v₀.safety == .unsafe then .unsafe else .safe) := by
    cases v₀.safety with
    | «partial» => exact DefinitionSafety.le_safe
    | _ => exact DefinitionSafety.le_rfl
  refine (TypeChecker.M.WF.run (Q := fun _ =>
    (∃ cis, (v₀ :: rest).Forall₂ (fun v ci =>
      TrMutualHeader v₀.safety (ves.venv v₀.safety) env v ci ∧
      v.safety = v₀.safety ∧ v.levelParams = v₀.levelParams) cis) ∧
    (((v₀ :: rest).map (·.name)).Nodup ∧
      ∀ v ∈ (v₀ :: rest), (∅ : NameSet).contains v.name = false)) wf ?_).bind fun _ h1 => ?_
  · refine (TypeChecker.M.WF.forInFresh fun v found s => ?_).bind fun _ _ _ h => .pure h
    split <;> [exact .bindThrow .throw; rename_i hsafety]
    split <;> [exact .bindThrow .throw; rename_i hlp]
    split <;> [exact .bindThrow .throw; rename_i hfound]
    simp at hsafety hlp hfound
    rw [← hlp]
    refine (checkConstantVal.WF wf (.defnInfo v) false ?_ s).bind ?_
    · rw [ConstantInfo.defnInfo_safety, hsafety]; exact DefinitionSafety.le_rfl
    refine fun _ _ _ ⟨ci', htr, hciw, hn, hnp⟩ => .pure ?_
    exact ⟨hfound, ⟨⟨ci', .bvar 0⟩, ⟨htr, hciw, hn, hnp rfl⟩, hsafety, rfl⟩, rfl⟩
  obtain ⟨⟨cis0, hQ0⟩, hnd, -⟩ := h1
  have hhdr := hQ0.imp fun _ _ h => h.1
  have hpull {P : DefinitionVal → VDefVal → Prop} (h : List.Forall₂ P (v₀ :: rest) cis0)
      {R : DefinitionVal → Prop} (H : ∀ v ci, P v ci → R v) : ∀ v ∈ v₀ :: rest, R v :=
    fun v hv => have ⟨ci, _, hp⟩ := h.forall_exists_l v hv; H v ci hp
  have hbs := hpull hQ0 fun _ _ h => h.2.1
  have hfresh := hpull hhdr fun _ _ h => h.2.2.1
  have hnonprim := hpull hhdr fun _ _ h => h.2.2.2
  have hnameeq : (v₀ :: rest).map (·.name) = cis0.map (·.name) := by
    rw [← List.forall₂_eq, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact hhdr.imp fun _ _ h => h.1.2
  have hpullr {P : DefinitionVal → VDefVal → Prop} (h : List.Forall₂ P (v₀ :: rest) cis0)
      {R : VDefVal → Prop} (H : ∀ v ci, P v ci → R ci) : ∀ ci ∈ cis0, R ci :=
    fun ci hc => have ⟨v, _, hp⟩ := h.forall_exists_r ci hc; H v ci hp
  obtain ⟨base, hbase0⟩ := (wf.tr (safety := v₀.safety)).exists_addConsts
    (hpullr hhdr fun _ _ h => h.1.2 ▸ h.2.2.1) (hnameeq ▸ hnd)
  have wfA := VEnvAt.addAxioms hsf (wf.toVEnvAt v₀.safety) hhdr hnd hbase0
  refine (TypeChecker.M.WF.run1 (Q := fun _ => ∃ cis',
    cis0.Forall₂ (fun (ci ci' : VDefVal) => ci.toVConstVal = ci'.toVConstVal) cis' ∧
    (v₀ :: rest).Forall₂ (fun v ci' => TrExprS base v.levelParams [] v.value ci'.value ∧
      ci'.WF base) cis') wfA ?_).bind fun _ h2 => ?_
  · refine (TypeChecker.M.WF.forInForall₂ (fun v ci s hd => ?_) hQ0).bind fun _ _ _ h => .pure h
    have hdecl := hd.1.1.1.2.2.mono (VEnv.addConsts_le hbase0)
    refine (TypeChecker.M.WF.liftExcept
      (checkNoMVarNoFVar.WF _ v.name v.value)).bind fun _ _ _ hclosed => ?_
    have hclosed' : v.value.FVarsIn
        (· ∈ (TypeChecker.VContext.mk1 wfA v.levelParams).vlctx.fvars) := by
      simpa [TypeChecker.VContext.mk1] using hclosed
    refine hd.2.2 ▸ (TypeChecker.checkType.WF hclosed').bind
      fun valType _ _ ⟨value', valType', _, hval, hvalTy, hhasType⟩ => ?_
    refine (TypeChecker.isDefEq.WF hvalTy hdecl).bind fun equal _ _ hequal => ?_
    split <;> [exact .bindThrow .throw; rename_i heq]
    refine .pure ⟨⟨⟨ci.toVConstVal, value'⟩, rfl, hval, ?_⟩, rfl⟩
    rw [VDefVal.WF, ← hd.1.1.1.2.1]
    exact hhasType.defeqU_r wfA.tr.wf (by trivial) (hequal (by simpa using heq))
  obtain ⟨cis, hRR, hbody⟩ := h2
  rw [VEnv.addConsts_congr hRR] at hbase0
  have : List.Forall₂ (TrMutualHeader v₀.safety (ves.venv v₀.safety) env) (v₀ :: rest) cis :=
    hhdr.trans (h₂ := hRR) fun v ci ci' h1 h2 => by
      have hc : ci.toVConstant = ci'.toVConstant := congrArg VConstVal.toVConstant h2
      exact ⟨h2 ▸ h1.1, hc ▸ h1.2.1, h1.2.2.1, h1.2.2.2⟩
  refine .pure <| addMutualBlock.WF wf v₀.safety (v₀ :: rest) cis base hbs hnd hfresh hnonprim
    (fun ci hc => ?_) hbase0 ((this.and hbody).imp (fun _ _ h => ⟨h.1.1, h.2.1⟩)) (fun ci hc => ?_)
  · obtain ⟨v, -, h⟩ := this.forall_exists_r ci hc; exact h.2.1
  · obtain ⟨v, -, h⟩ := hbody.forall_exists_r ci hc; exact h.2

/-- Semantic completion boundary for one retained inductive execution.  It
packages the exact safety-indexed model extension required by `VEnvs.WF`. -/
def AddInductive.EnvironmentInductiveExecution.PreservesVEnvs
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (_execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv)
    (ves : VEnvs) : Prop :=
  ∃ ves' : VEnvs, ves'.WF finalEnv ∧
    ∀ safety, ves.venv safety ≤ ves'.venv safety

/-- Pointwise semantic data needed to assemble preservation for one retained
inductive execution.  This separates transaction translation from primitive
and readiness preservation and from the cross-safety coherence of the output
models. -/
structure AddInductive.EnvironmentInductiveExecution.VEnvsExtension
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (_execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv)
    (ves : VEnvs) where
  output : VEnvs
  tr : ∀ safety, TrEnv safety finalEnv (output.venv safety)
  hasPrimitives : ∀ safety, VEnv.HasPrimitives (output.venv safety)
  safePrimitives : ∀ {n ci}, finalEnv.find? n = some ci →
    Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = []
  mono : ∀ {safety safety'}, safety ≤ safety' →
    output.venv safety' ≤ output.venv safety
  projectionReady : ∀ safety,
    ProjectionReady finalEnv (output.venv safety)
  structureEtaReady : ∀ safety,
    StructureEtaReady finalEnv (output.venv safety)
  old_le : ∀ safety, ves.venv safety ≤ output.venv safety

namespace AddInductive.EnvironmentInductiveExecution.VEnvsExtension

/-- Assemble the standard bundled environment invariant from its pointwise
components. -/
theorem wf
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv}
    {ves : VEnvs}
    (extension : AddInductive.EnvironmentInductiveExecution.VEnvsExtension
      execution ves) : extension.output.WF finalEnv where
  tr {safety} := extension.tr safety
  hasPrimitives {safety} := extension.hasPrimitives safety
  safePrimitives {n ci} := extension.safePrimitives (n := n) (ci := ci)
  mono {safety safety'} := extension.mono (safety := safety)
    (safety' := safety')
  projectionReady {safety} := extension.projectionReady safety
  structureEtaReady {safety} := extension.structureEtaReady safety

/-- Forget the decomposed fields back to the semantic completion boundary
consumed by the generic `addDecl` bridge. -/
theorem toPreservesVEnvs
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv}
    {ves : VEnvs}
    (extension : AddInductive.EnvironmentInductiveExecution.VEnvsExtension
      execution ves) : execution.PreservesVEnvs ves :=
  ⟨extension.output, extension.wf, extension.old_le⟩

end AddInductive.EnvironmentInductiveExecution.VEnvsExtension

/-- An exact ordinary or nested semantic transaction whose three constant
phases avoid every Theory name tracked by `VEnv.HasPrimitives`.  The actual
data-bearing trace is retained so restored nested recursor names are checked
after renaming, rather than approximated from the source declaration.  This
is the non-primitive branch; primitive-recognized declarations require their
dedicated reflection proof. -/
inductive AddInductive.EnvironmentInductiveExecution.PrimitivePreservingTransaction
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv)
    (source : VInductDecl) (input output : VEnv) : Prop where
  | ordinary
      (numNested_eq : execution.nested.aux2nested.size = 0)
      (trace : AddInductBlockTrace env.constants input source
        finalEnv.constants output)
      (typeNames : ∀ ci ∈ source.blockTypeConstants,
        ci.name ∉ VEnv.reflectedPrimitiveNames ∧
          Environment.primitives.contains ci.name = false)
      (ctorNames : ∀ ci ∈ source.blockConstructorConstants,
        ci.name ∉ VEnv.reflectedPrimitiveNames ∧
          Environment.primitives.contains ci.name = false)
      (recNames : ∀ ci ∈ trace.generation.recursors,
        ci.name ∉ VEnv.reflectedPrimitiveNames ∧
          Environment.primitives.contains ci.name = false) :
      execution.PrimitivePreservingTransaction source input output
  | nested
      (numNested_ne : execution.nested.aux2nested.size ≠ 0)
      (trace : AddInductNestedTrace env.constants input source
        finalEnv.constants output)
      (typeNames : ∀ ci ∈ source.blockTypeConstants,
        ci.name ∉ VEnv.reflectedPrimitiveNames ∧
          Environment.primitives.contains ci.name = false)
      (ctorNames : ∀ ci ∈ source.blockConstructorConstants,
        ci.name ∉ VEnv.reflectedPrimitiveNames ∧
          Environment.primitives.contains ci.name = false)
      (recNames : ∀ ci ∈ trace.nested.recursors,
        ci.name ∉ VEnv.reflectedPrimitiveNames ∧
          Environment.primitives.contains ci.name = false) :
      execution.PrimitivePreservingTransaction source input output

namespace AddInductive.EnvironmentInductiveExecution.PrimitivePreservingTransaction

/-- Forget name avoidance while retaining the exact branch transaction. -/
theorem toExact
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv}
    {source : VInductDecl} {input output : VEnv}
    (transaction : execution.PrimitivePreservingTransaction source input
      output) :
    execution.ExactSemanticTransaction source input output := by
  cases transaction with
  | ordinary numNested_eq trace _ _ _ =>
      exact .ordinary numNested_eq ⟨trace⟩
  | nested numNested_ne trace _ _ _ =>
      exact .nested numNested_ne ⟨trace⟩

/-- A name-avoiding exact transaction transports primitive reflection from
its input Theory environment to its output. -/
theorem hasPrimitives
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv}
    {source : VInductDecl} {input output : VEnv}
    (transaction : execution.PrimitivePreservingTransaction source input
      output) (pre : input.HasPrimitives) : output.HasPrimitives := by
  cases transaction with
  | ordinary _ trace typeNames ctorNames recNames =>
      exact trace.hasPrimitives pre
        (fun ci member => (typeNames ci member).1)
        (fun ci member => (ctorNames ci member).1)
        (fun ci member => (recNames ci member).1)
  | nested _ trace typeNames ctorNames recNames =>
      exact trace.hasPrimitives pre
        (fun ci member => (typeNames ci member).1)
        (fun ci member => (ctorNames ci member).1)
        (fun ci member => (recNames ci member).1)

/-- The same name-avoidance evidence transports the host primitive-safety
lookup invariant through the exact metadata map. -/
theorem safePrimitivesMap
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv}
    {source : VInductDecl} {input output : VEnv}
    (transaction : execution.PrimitivePreservingTransaction source input
      output) (mapWF : env.constants.WF)
    (pre : ConstMapSafePrimitives env.constants) :
    ConstMapSafePrimitives finalEnv.constants := by
  cases transaction with
  | ordinary _ trace typeNames ctorNames recNames =>
      exact trace.safePrimitivesMap mapWF pre
        (fun ci member => (typeNames ci member).2)
        (fun ci member => (ctorNames ci member).2)
        (fun ci member => (recNames ci member).2)
  | nested _ trace typeNames ctorNames recNames =>
      exact trace.safePrimitivesMap mapWF pre
        (fun ci member => (typeNames ci member).2)
        (fun ci member => (ctorNames ci member).2)
        (fun ci member => (recNames ci member).2)

end AddInductive.EnvironmentInductiveExecution.PrimitivePreservingTransaction

/-- A safety-indexed family of name-avoiding transactions which replays one
shared ordinary generation or one shared restored nested artifact.  Sharing
the artifact is the exact condition needed to transport the input
cross-safety ordering through all constant and rule folds. -/
inductive AddInductive.EnvironmentInductiveExecution.CoherentPrimitivePreservingTransactions
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv)
    (source : VInductDecl) (input output : VEnvs) : Prop where
  | ordinary
      (numNested_eq : execution.nested.aux2nested.size = 0)
      (generation : source.BlockGenerationChecked)
      (traces : ∀ safety, AddInductBlockTrace env.constants
        (input.venv safety) source finalEnv.constants (output.venv safety))
      (generation_eq : ∀ safety, (traces safety).generation = generation)
      (typeNames : ∀ ci ∈ source.blockTypeConstants,
        ci.name ∉ VEnv.reflectedPrimitiveNames ∧
          Environment.primitives.contains ci.name = false)
      (ctorNames : ∀ ci ∈ source.blockConstructorConstants,
        ci.name ∉ VEnv.reflectedPrimitiveNames ∧
          Environment.primitives.contains ci.name = false)
      (recNames : ∀ ci ∈ generation.recursors,
        ci.name ∉ VEnv.reflectedPrimitiveNames ∧
          Environment.primitives.contains ci.name = false) :
      execution.CoherentPrimitivePreservingTransactions source input output
  | nested
      (numNested_ne : execution.nested.aux2nested.size ≠ 0)
      (nestedArtifact : source.NestedBlockChecked)
      (traces : ∀ safety, AddInductNestedTrace env.constants
        (input.venv safety) source finalEnv.constants (output.venv safety))
      (nested_eq : ∀ safety, (traces safety).nested = nestedArtifact)
      (typeNames : ∀ ci ∈ source.blockTypeConstants,
        ci.name ∉ VEnv.reflectedPrimitiveNames ∧
          Environment.primitives.contains ci.name = false)
      (ctorNames : ∀ ci ∈ source.blockConstructorConstants,
        ci.name ∉ VEnv.reflectedPrimitiveNames ∧
          Environment.primitives.contains ci.name = false)
      (recNames : ∀ ci ∈ nestedArtifact.recursors,
        ci.name ∉ VEnv.reflectedPrimitiveNames ∧
          Environment.primitives.contains ci.name = false) :
      execution.CoherentPrimitivePreservingTransactions source input output

namespace AddInductive.EnvironmentInductiveExecution.CoherentPrimitivePreservingTransactions

/-- Select the exact name-avoiding transaction at one safety level. -/
theorem transaction
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv}
    {source : VInductDecl} {input output : VEnvs}
    (transactions : execution.CoherentPrimitivePreservingTransactions source
      input output) (safety : DefinitionSafety) :
    execution.PrimitivePreservingTransaction source (input.venv safety)
      (output.venv safety) := by
  cases transactions with
  | ordinary numNested_eq generation traces generation_eq typeNames ctorNames
      recNames =>
      exact .ordinary numNested_eq (traces safety) typeNames ctorNames
        (fun ci member => recNames ci (by
          simpa only [generation_eq safety] using member))
  | nested numNested_ne nestedArtifact traces nested_eq typeNames ctorNames
      recNames =>
      exact .nested numNested_ne (traces safety) typeNames ctorNames
        (fun ci member => recNames ci (by
          simpa only [nested_eq safety] using member))

/-- Shared-artifact replay transports the input cross-safety ordering to the
output family. -/
theorem mono
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv}
    {source : VInductDecl} {input output : VEnvs}
    (transactions : execution.CoherentPrimitivePreservingTransactions source
      input output)
    (pre : ∀ {safety safety'}, safety ≤ safety' →
      input.venv safety' ≤ input.venv safety)
    {safety safety' : DefinitionSafety} (hle : safety ≤ safety') :
    output.venv safety' ≤ output.venv safety := by
  cases transactions with
  | ordinary _ generation traces generation_eq _ _ _ =>
      exact (traces safety').mono (traces safety)
        ((generation_eq safety').trans (generation_eq safety).symm) (pre hle)
  | nested _ nestedArtifact traces nested_eq _ _ _ =>
      exact (traces safety').mono (traces safety)
        ((nested_eq safety').trans (nested_eq safety).symm) (pre hle)

end AddInductive.EnvironmentInductiveExecution.CoherentPrimitivePreservingTransactions

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.PrimitivePreservingTransaction.hasPrimitives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms AddInductive.EnvironmentInductiveExecution.PrimitivePreservingTransaction.hasPrimitives

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.PrimitivePreservingTransaction.safePrimitivesMap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms AddInductive.EnvironmentInductiveExecution.PrimitivePreservingTransaction.safePrimitivesMap

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.CoherentPrimitivePreservingTransactions.mono' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms AddInductive.EnvironmentInductiveExecution.CoherentPrimitivePreservingTransactions.mono

/-- A family of exact ordinary/nested transactions, one for each safety-indexed
input model.  Transaction replay supplies translation and monotone extension;
the remaining fields are precisely the primitive, coherence, and readiness
obligations not encoded by an `AddInductBlock`/`AddInductNested` trace. -/
structure AddInductive.EnvironmentInductiveExecution.TransactionalVEnvsExtension
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv)
    (ves : VEnvs) where
  source : VInductDecl
  output : VEnvs
  transaction : ∀ safety,
    execution.ExactSemanticTransaction source (ves.venv safety)
      (output.venv safety)
  hasPrimitives : ∀ safety, VEnv.HasPrimitives (output.venv safety)
  safePrimitives : ∀ {n ci}, finalEnv.find? n = some ci →
    Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = []
  mono : ∀ {safety safety'}, safety ≤ safety' →
    output.venv safety' ≤ output.venv safety
  projectionReady : ∀ safety,
    ProjectionReady finalEnv (output.venv safety)
  structureEtaReady : ∀ safety,
    StructureEtaReady finalEnv (output.venv safety)

namespace AddInductive.EnvironmentInductiveExecution.TransactionalVEnvsExtension

/-- Replay every exact transaction on the corresponding input translation and
obtain the pointwise component package. -/
def toVEnvsExtension
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv}
    {ves : VEnvs} (wf : ves.WF env)
    (extension :
      AddInductive.EnvironmentInductiveExecution.TransactionalVEnvsExtension
        execution ves) : execution.VEnvsExtension ves where
  output := extension.output
  tr safety := by
    unfold TrEnv
    exact (extension.transaction safety).trEnv (wf.tr (safety := safety))
  hasPrimitives := extension.hasPrimitives
  safePrimitives := extension.safePrimitives
  mono := extension.mono
  projectionReady := extension.projectionReady
  structureEtaReady := extension.structureEtaReady
  old_le safety := (extension.transaction safety).le

end AddInductive.EnvironmentInductiveExecution.TransactionalVEnvsExtension

/-- Primitive recognition selects the complete canonical Theory declaration
directly.  No independently supplied raw source or semantic normalization run
is needed on this closed Bool/Nat branch. -/
theorem VPrimitiveInductive.canonicalDecl_constants
    {types : List InductiveType} (shape : PrimitiveInductiveShape types) :
    (VPrimitiveInductive.canonicalDecl types).CanonicalPrimitiveConstants := by
  obtain ⟨type, rfl, type_type, primitive⟩ := shape
  cases primitive with
  | inl boolShape =>
      obtain ⟨type_name, constructors_eq⟩ := boolShape
      simp only [VPrimitiveInductive.canonicalDecl, type_name,
        beq_self_eq_true, List.any_cons, List.any_nil, Bool.or_false, if_true]
      exact .bool rfl rfl
  | inr natShape =>
      obtain ⟨type_name, binderName, binderInfo, constructors_eq⟩ := natShape
      simp only [VPrimitiveInductive.canonicalDecl, type_name, List.any_cons,
        List.any_nil, Bool.or_false]
      have nat_ne_bool : (``Nat : Name) ≠ ``Bool := by decide
      simp [nat_ne_bool]
      exact .nat rfl rfl

/--
info: 'Lean4Lean.VPrimitiveInductive.canonicalDecl_constants' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms VPrimitiveInductive.canonicalDecl_constants

/-- Primitive recognition and the retained public nested-elimination run
jointly prove that the canonical source list is unchanged and no auxiliary
family was generated. -/
theorem AddInductive.EnvironmentInductiveExecution.canonicalPrimitive_noop
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe true fuel finalEnv)
    (primitiveResult : PrimitiveInductiveResult lparams nparams types isUnsafe
      true) :
    execution.nested.types = types ∧
      execution.nested.aux2nested.size = 0 := by
  have recognized := primitiveResult.recognized rfl
  apply execution.nested.canonicalPrimitive_noop recognized.2.2.2
  simpa only [recognized.2.1, recognized.2.2.1] using execution.nestedRun

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.canonicalPrimitive_noop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.abstract_eq]
-/
#guard_msgs in
#print axioms AddInductive.EnvironmentInductiveExecution.canonicalPrimitive_noop

/-- The normalization prefix retained by an outer execution still starts from
the outer input environment.  Naming this equality lets semantic replay use the
actual family-declaration trace without exposing its internal reader context as
an independent input. -/
theorem AddInductive.EnvironmentInductiveExecution.flattenedValidationEnv_eq
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv) :
    execution.flattened.eliminationExecution.normalization.validationContext.env =
      env := by
  simpa only [AddInductive.Context.forInductive] using
    execution.flattened.eliminationExecution.normalization.validationContext_env_all
      (execution.flattened.normalization_run execution.flattenedRun)

/-- The normalization prefix also retains the outer universe-parameter list
exactly. -/
theorem AddInductive.EnvironmentInductiveExecution.flattenedValidationLparams_eq
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv) :
    execution.flattened.eliminationExecution.normalization.validationContext.lparams =
      lparams := by
  simpa only [AddInductive.Context.forInductive] using
    execution.flattened.eliminationExecution.normalization.validationContext_lparams_all
      (execution.flattened.normalization_run execution.flattenedRun)

/-- A recognized primitive execution's exact family metadata translates to
the canonical Theory family inventory.  The proof selects the sole retained
metadata record through the validator's source-aligned relation; no parallel
metadata list is reconstructed. -/
theorem AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveFamilyEvidence
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe true fuel finalEnv)
    (primitiveResult : PrimitiveInductiveResult lparams nparams types isUnsafe
      true) (input : VEnv) :
    List.Forall₂
      (fun info raw => TrConstVal .safe input (.inductInfo info) raw)
      execution.flattened.eliminationExecution.normalization.declaredInfos
      (VPrimitiveInductive.canonicalDecl types).blockTypeConstants := by
  have recognized := primitiveResult.recognized rfl
  obtain ⟨safe, lparamsEq, _, shape⟩ := recognized
  obtain ⟨type, typesEq, typeType, primitive⟩ := shape
  have noop := execution.canonicalPrimitive_noop primitiveResult
  have nestedTypesEq : execution.nested.types = [type] :=
    noop.1.trans typesEq
  have normalizationRun :=
    execution.flattened.normalization_run execution.flattenedRun
  have nonempty : execution.nested.types.isEmpty = false := by
    rw [nestedTypesEq]
    rfl
  have nindicesSize :
      execution.flattened.eliminationExecution.normalization.stats.nindices.size =
        execution.nested.types.length := by
    have sizes := execution.flattened.eliminationExecution.normalization
      |>.familyValidationResult.sizes_of_run nonempty
        (execution.flattened.eliminationExecution.normalization
          |>.familyValidationResult_run normalizationRun)
    simpa only [
      AddInductive.NormalizationCandidateExecution.familyValidationResult] using
      sizes.2.1
  have metadata : List.Forall₂
      (fun indType info => ∃ numIndices,
        info = AddInductive.declaredInductiveInfo
          execution.flattened.eliminationExecution.normalization.stats nparams
          execution.nested.types.toArray indType numIndices
          execution.nested.aux2nested.size isUnsafe
          execution.flattened.eliminationExecution.normalization.validationContext)
      execution.nested.types
      execution.flattened.eliminationExecution.normalization.declaredInfos := by
    simpa only [
      AddInductive.NormalizationCandidateExecution.declaredInfos,
      List.toList_toArray] using
      AddInductive.declaredInductiveInfos_matches
        execution.flattened.eliminationExecution.normalization.stats nparams
        execution.nested.types.toArray execution.nested.aux2nested.size
        isUnsafe
        execution.flattened.eliminationExecution.normalization.validationContext
        (by simpa using nindicesSize)
  have sourceGet : execution.nested.types[0]? = some type := by
    rw [nestedTypesEq]
    rfl
  obtain ⟨info, infoGet, alignment⟩ :=
    Lean4Lean.List.Forall₂.getElem?_left metadata sourceGet
  have declaredLength :
      execution.flattened.eliminationExecution.normalization.declaredInfos.length =
        1 := by
    calc
      _ = execution.nested.types.length :=
        (Lean4Lean.List.Forall₂.length_eq metadata).symm
      _ = [type].length := congrArg List.length nestedTypesEq
      _ = 1 := rfl
  obtain ⟨onlyInfo, declaredInfosEq⟩ :=
    List.length_eq_one_iff.mp declaredLength
  rw [declaredInfosEq] at infoGet
  simp only [List.getElem?_cons_zero, Option.some.injEq] at infoGet
  subst onlyInfo
  have validationLparams :
      execution.flattened.eliminationExecution.normalization.validationContext.lparams =
        [] := execution.flattenedValidationLparams_eq.trans lparamsEq
  cases primitive with
  | inl boolShape =>
      obtain ⟨typeName, _⟩ := boolShape
      have rawFamiliesEq :
          (VPrimitiveInductive.canonicalDecl types).blockTypeConstants =
            [VPrimitiveInductive.boolType.toVConstVal] := by
        simp [VPrimitiveInductive.canonicalDecl, typesEq, typeName,
          VInductDecl.blockTypeConstants, VPrimitiveInductive.boolDecl,
          VPrimitiveInductive.boolType]
      rw [declaredInfosEq, rawFamiliesEq]
      apply List.Forall₂.cons
      · apply VInductDecl.declaredInductiveInfo_tr
          (raw := VPrimitiveInductive.boolType) alignment safe
          validationLparams typeName
        · rfl
        · simpa [typeType, VPrimitiveInductive.boolType] using
            (show TrExprS input [] [] (.sort (.succ .zero))
                (.sort (.succ .zero)) from .sort rfl)
      · exact .nil
  | inr natShape =>
      obtain ⟨typeName, _, _, _⟩ := natShape
      have rawFamiliesEq :
          (VPrimitiveInductive.canonicalDecl types).blockTypeConstants =
            [VPrimitiveInductive.natType.toVConstVal] := by
        simp [VPrimitiveInductive.canonicalDecl, typesEq, typeName,
          VInductDecl.blockTypeConstants, VPrimitiveInductive.natDecl,
          VPrimitiveInductive.natType]
      rw [declaredInfosEq, rawFamiliesEq]
      apply List.Forall₂.cons
      · apply VInductDecl.declaredInductiveInfo_tr
          (raw := VPrimitiveInductive.natType) alignment safe
          validationLparams typeName
        · rfl
        · simpa [typeType, VPrimitiveInductive.natType] using
            (show TrExprS input [] [] (.sort (.succ .zero))
                (.sort (.succ .zero)) from .sort rfl)
      · exact .nil

/-- Replay the retained primitive family-declaration fold directly from its
canonical semantic evidence.  The input alignment is stated at the outer
environment and retargeted through the validator's preserved-environment
invariant. -/
noncomputable def AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveFamilyInsertion
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe true fuel finalEnv)
    (primitiveResult : PrimitiveInductiveResult lparams nparams types isUnsafe
      true) (input : VEnv)
    (pre : Aligned safety env.constants input) :
    VInductDecl.FamilyDeclarationInsertionRun
      execution.flattened.eliminationExecution.normalization.validationContext.allowPrimitive
      execution.flattened.eliminationExecution.normalization.validationContext.env
      execution.flattened.eliminationExecution.normalization.familyEnv
      execution.flattened.eliminationExecution.normalization.declaredInfos
      input (VPrimitiveInductive.canonicalDecl types).blockTypeConstants := by
  apply VInductDecl.familyDeclarationInsertion
  · simpa only [AddInductive.declareInductiveTypes,
      AddInductive.NormalizationCandidateExecution.declaredInfos] using
      execution.flattened.eliminationExecution.normalization.declareRun
  · exact execution.canonicalPrimitiveFamilyEvidence primitiveResult input
  · have initialEq := execution.flattenedValidationEnv_eq
    simpa only [initialEq] using pre

/-- The retained canonical family fold supplies the exact staging equation
needed to derive the complete Bool/Nat generation certificate.  No semantic
well-formedness premise remains on the primitive transaction boundary. -/
theorem AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveGenerationWF
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe true fuel finalEnv)
    (primitiveResult : PrimitiveInductiveResult lparams nparams types isUnsafe
      true) (input : VEnv)
    (families : VInductDecl.FamilyDeclarationInsertionRun
      execution.flattened.eliminationExecution.normalization.validationContext.allowPrimitive
      execution.flattened.eliminationExecution.normalization.validationContext.env
      execution.flattened.eliminationExecution.normalization.familyEnv
      execution.flattened.eliminationExecution.normalization.declaredInfos
      input (VPrimitiveInductive.canonicalDecl types).blockTypeConstants) :
    (VPrimitiveInductive.canonicalGeneration types).WF input
      families.blockEnv := by
  have recognized := primitiveResult.recognized rfl
  obtain ⟨_, _, _, shape⟩ := recognized
  obtain ⟨type, typesEq, _, primitive⟩ := shape
  subst types
  rcases type with ⟨sourceName, sourceType, sourceCtors⟩
  cases primitive with
  | inl boolShape =>
      obtain ⟨typeName, _⟩ := boolShape
      dsimp only [InductiveType.name] at typeName
      subst sourceName
      have rawFamiliesEq :
          VInductDecl.blockTypeConstants (VPrimitiveInductive.canonicalDecl
            [(⟨``Bool, sourceType, sourceCtors⟩ : InductiveType)]) =
            [VPrimitiveInductive.boolType.toVConstVal] := by
        simp [VPrimitiveInductive.canonicalDecl,
          VInductDecl.blockTypeConstants, VPrimitiveInductive.boolDecl,
          VPrimitiveInductive.boolType]
      have familyAdds : AddInductConstants .induct
          execution.flattened.eliminationExecution.normalization.validationContext.env.constants
          input [VPrimitiveInductive.boolType.toVConstVal]
          execution.flattened.eliminationExecution.normalization.familyEnv.constants
          families.blockEnv := by
        simpa only [rawFamiliesEq] using families.addTypes
      cases familyAdds with
      | cons familyAdd familyTail =>
          cases familyTail
          change VPrimitiveInductive.boolGeneration.WF input
            families.blockEnv
          exact VPrimitiveInductive.boolGeneration_wf familyAdd.env_add
  | inr natShape =>
      obtain ⟨typeName, _, _, _⟩ := natShape
      dsimp only [InductiveType.name] at typeName
      subst sourceName
      have rawFamiliesEq :
          VInductDecl.blockTypeConstants (VPrimitiveInductive.canonicalDecl
            [(⟨``Nat, sourceType, sourceCtors⟩ : InductiveType)]) =
            [VPrimitiveInductive.natType.toVConstVal] := by
        simp [VPrimitiveInductive.canonicalDecl,
          VInductDecl.blockTypeConstants, VPrimitiveInductive.natDecl,
          VPrimitiveInductive.natType]
      have familyAdds : AddInductConstants .induct
          execution.flattened.eliminationExecution.normalization.validationContext.env.constants
          input [VPrimitiveInductive.natType.toVConstVal]
          execution.flattened.eliminationExecution.normalization.familyEnv.constants
          families.blockEnv := by
        simpa only [rawFamiliesEq] using families.addTypes
      cases familyAdds with
      | cons familyAdd familyTail =>
          cases familyTail
          change VPrimitiveInductive.natGeneration.WF input
            families.blockEnv
          exact VPrimitiveInductive.natGeneration_wf familyAdd.env_add

/-- The exact constructor metadata retained by a recognized primitive
execution translates to the canonical Bool/Nat constructor inventory in the
Theory environment produced by its family insertion. -/
theorem AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveConstructorEvidence
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe true fuel finalEnv)
    (primitiveResult : PrimitiveInductiveResult lparams nparams types isUnsafe
      true) (input : VEnv)
    (families : VInductDecl.FamilyDeclarationInsertionRun
      execution.flattened.eliminationExecution.normalization.validationContext.allowPrimitive
      execution.flattened.eliminationExecution.normalization.validationContext.env
      execution.flattened.eliminationExecution.normalization.familyEnv
      execution.flattened.eliminationExecution.normalization.declaredInfos
      input (VPrimitiveInductive.canonicalDecl types).blockTypeConstants) :
    List.Forall₂
      (fun info raw => TrConstVal .safe families.blockEnv (.ctorInfo info) raw)
      execution.flattened.eliminationExecution.declaredConstructorInfos
      (VPrimitiveInductive.canonicalDecl types).blockConstructorConstants := by
  have recognized := primitiveResult.recognized rfl
  obtain ⟨safe, lparamsEq, _, shape⟩ := recognized
  obtain ⟨type, typesEq, _, primitive⟩ := shape
  have noop := execution.canonicalPrimitive_noop primitiveResult
  have nestedTypesEq : execution.nested.types = [type] :=
    noop.1.trans typesEq
  have declaredInfosEq :
      execution.flattened.eliminationExecution.declaredConstructorInfos =
        AddInductive.declaredConstructorInfosFor
          execution.flattened.eliminationExecution.normalization.stats
          type.name isUnsafe
          execution.flattened.eliminationExecution.constructorContext 0
          type.ctors := by
    simp only [
      AddInductive.NormalizationEliminationExecution.declaredConstructorInfos,
      AddInductive.declaredConstructorInfos_toArray, nestedTypesEq,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have constructorLparams :
      execution.flattened.eliminationExecution.constructorContext.lparams =
        [] := by
    simpa only [
      AddInductive.NormalizationEliminationExecution.constructorContext] using
      execution.flattenedValidationLparams_eq.trans lparamsEq
  cases primitive with
  | inl boolShape =>
      obtain ⟨typeName, constructorsEq⟩ := boolShape
      have rawFamiliesEq :
          (VPrimitiveInductive.canonicalDecl types).blockTypeConstants =
            [VPrimitiveInductive.boolType.toVConstVal] := by
        simp [VPrimitiveInductive.canonicalDecl, typesEq, typeName,
          VInductDecl.blockTypeConstants, VPrimitiveInductive.boolDecl,
          VPrimitiveInductive.boolType]
      have familyAdds : AddInductConstants .induct
          execution.flattened.eliminationExecution.normalization.validationContext.env.constants
          input [VPrimitiveInductive.boolType.toVConstVal]
          execution.flattened.eliminationExecution.normalization.familyEnv.constants
          families.blockEnv := by
        simpa only [rawFamiliesEq] using families.addTypes
      cases familyAdds with
      | cons familyAdd familyTail =>
          cases familyTail
          have familyLookup : families.blockEnv.constants ``Bool =
              some VPrimitiveInductive.boolType.toVConstant :=
            VEnv.addConst_self familyAdd.env_add
          have rawCtorsEq :
              (VPrimitiveInductive.canonicalDecl types).blockConstructorConstants =
                VPrimitiveInductive.boolType.ctors := by
            simp [VPrimitiveInductive.canonicalDecl, typesEq, typeName,
              VInductDecl.blockConstructorConstants,
              VPrimitiveInductive.boolDecl]
          rw [declaredInfosEq, constructorsEq, rawCtorsEq]
          simp only [AddInductive.declaredConstructorInfosFor,
            VPrimitiveInductive.boolType,
            VPrimitiveInductive.boolConstructors]
          apply List.Forall₂.cons
          · apply VInductDecl.declaredConstructorInfo_tr safe
              constructorLparams rfl rfl
            exact .const familyLookup rfl rfl
          · apply List.Forall₂.cons
            · apply VInductDecl.declaredConstructorInfo_tr safe
                constructorLparams rfl rfl
              exact .const familyLookup rfl rfl
            · exact .nil
  | inr natShape =>
      obtain ⟨typeName, binderName, binderInfo, constructorsEq⟩ := natShape
      have rawFamiliesEq :
          (VPrimitiveInductive.canonicalDecl types).blockTypeConstants =
            [VPrimitiveInductive.natType.toVConstVal] := by
        simp [VPrimitiveInductive.canonicalDecl, typesEq, typeName,
          VInductDecl.blockTypeConstants, VPrimitiveInductive.natDecl,
          VPrimitiveInductive.natType]
      have familyAdds : AddInductConstants .induct
          execution.flattened.eliminationExecution.normalization.validationContext.env.constants
          input [VPrimitiveInductive.natType.toVConstVal]
          execution.flattened.eliminationExecution.normalization.familyEnv.constants
          families.blockEnv := by
        simpa only [rawFamiliesEq] using families.addTypes
      cases familyAdds with
      | cons familyAdd familyTail =>
          cases familyTail
          have familyLookup : families.blockEnv.constants ``Nat =
              some VPrimitiveInductive.natType.toVConstant :=
            VEnv.addConst_self familyAdd.env_add
          have natIsType (context : List VExpr) :
              families.blockEnv.IsType 0 context .nat :=
            ⟨.succ .zero,
              VEnv.HasType.const familyLookup (by simp) rfl⟩
          have rawCtorsEq :
              (VPrimitiveInductive.canonicalDecl types).blockConstructorConstants =
                VPrimitiveInductive.natType.ctors := by
            simp [VPrimitiveInductive.canonicalDecl, typesEq, typeName,
              VInductDecl.blockConstructorConstants,
              VPrimitiveInductive.natDecl]
          rw [declaredInfosEq, constructorsEq, rawCtorsEq]
          simp only [AddInductive.declaredConstructorInfosFor,
            VPrimitiveInductive.natType,
            VPrimitiveInductive.natConstructors]
          apply List.Forall₂.cons
          · apply VInductDecl.declaredConstructorInfo_tr safe
              constructorLparams rfl rfl
            exact .const familyLookup rfl rfl
          · apply List.Forall₂.cons
            · apply VInductDecl.declaredConstructorInfo_tr safe
                constructorLparams rfl rfl
              exact .forallE (natIsType []) (natIsType [.nat])
                (.const familyLookup rfl rfl)
                (.const familyLookup rfl rfl)
            · exact .nil

/-- Replay the retained primitive constructor-declaration fold immediately
after its canonical family insertion. -/
noncomputable def AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveConstructorInsertion
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe true fuel finalEnv)
    (primitiveResult : PrimitiveInductiveResult lparams nparams types isUnsafe
      true) (input : VEnv)
    (pre : Aligned safety env.constants input)
    (families : VInductDecl.FamilyDeclarationInsertionRun
      execution.flattened.eliminationExecution.normalization.validationContext.allowPrimitive
      execution.flattened.eliminationExecution.normalization.validationContext.env
      execution.flattened.eliminationExecution.normalization.familyEnv
      execution.flattened.eliminationExecution.normalization.declaredInfos
      input (VPrimitiveInductive.canonicalDecl types).blockTypeConstants) :
    VInductDecl.ConstructorDeclarationInsertionRun
      execution.flattened.eliminationExecution.constructorContext.allowPrimitive
      execution.flattened.eliminationExecution.normalization.familyEnv
      execution.flattened.eliminationExecution.constructorEnv
      execution.flattened.eliminationExecution.declaredConstructorInfos
      families.blockEnv
      (VPrimitiveInductive.canonicalDecl types).blockConstructorConstants := by
  apply VInductDecl.constructorDeclarationInsertion
  · simpa only [AddInductive.declareConstructors,
      AddInductive.NormalizationEliminationExecution.constructorContext,
      AddInductive.NormalizationEliminationExecution.declaredConstructorInfos]
      using execution.flattened.eliminationExecution.declareConstructorsRun
  · exact execution.canonicalPrimitiveConstructorEvidence primitiveResult
      input families
  · have initialEq := execution.flattenedValidationEnv_eq
    have initialAligned : Aligned safety
        execution.flattened.eliminationExecution.normalization.validationContext.env.constants
        input := by
      simpa only [initialEq] using pre
    exact initialAligned.addInductConstants families.addTypes

namespace AddInductive.EnvironmentInductiveExecution

private theorem canonicalSingletonStatsAndFuelOfEq
    {context : AddInductive.Context} {indType : InductiveType}
    {types : List InductiveType} {numNested : Nat} {isUnsafe : Bool}
    {candidate : AddInductive.NormalizationCandidateExecution 0 types
      numNested isUnsafe context}
    (types_eq : types = [indType])
    (produced : AddInductive.buildNormalizationCandidateExecution 0 types
      numNested isUnsafe context = .ok candidate)
    (type_eq : indType.type = .sort (.succ .zero)) :
    candidate.stats =
        AddInductive.singletonInductiveStats context indType (.succ .zero) ∧
      candidate.validationContext = context ∧
      ∃ depth inductiveFuel,
        context.fuel.recDepth = depth + 1 ∧
          context.fuel.inductiveFuel = inductiveFuel + 1 := by
  subst types
  exact AddInductive.PrimitiveRecursorReplay.canonicalSingletonStatsAndFuel
    produced type_eq

private theorem boolLargeResultOfRun
    {stats : AddInductive.InductiveStats}
    {indTypes : List InductiveType} {context : AddInductive.Context}
    {result : Bool}
    (stats_eq : stats = AddInductive.PrimitiveRecursorReplay.boolStats)
    (types_eq : indTypes =
      [AddInductive.PrimitiveRecursorReplay.boolSource])
    (run : AddInductive.isLargeEliminator stats indTypes.toArray context =
      .ok result) : result = true := by
  subst stats
  subst indTypes
  simp [AddInductive.isLargeEliminator,
    AddInductive.PrimitiveRecursorReplay.boolStats,
    ReaderT.pure, Pure.pure, Except.pure] at run
  exact run

private theorem boolKTargetResultOfRun
    {stats : AddInductive.InductiveStats}
    {indTypes : List InductiveType} {context : AddInductive.Context}
    {result : Bool}
    (stats_eq : stats = AddInductive.PrimitiveRecursorReplay.boolStats)
    (types_eq : indTypes =
      [AddInductive.PrimitiveRecursorReplay.boolSource])
    (run : AddInductive.isKTarget stats indTypes.toArray context = .ok result) :
    result = false := by
  subst stats
  subst indTypes
  have expected : AddInductive.isKTarget
      AddInductive.PrimitiveRecursorReplay.boolStats
      #[AddInductive.PrimitiveRecursorReplay.boolSource] context =
      .ok false := by
    rfl
  exact Except.ok.inj (run.symm.trans expected)

private theorem natLargeResultOfRun
    {stats : AddInductive.InductiveStats}
    {indTypes : List InductiveType} {context : AddInductive.Context}
    {result : Bool} (binderName : Name) (binderInfo : BinderInfo)
    (stats_eq : stats = AddInductive.PrimitiveRecursorReplay.natStats)
    (types_eq : indTypes =
      [AddInductive.PrimitiveRecursorReplay.natSource binderName binderInfo])
    (run : AddInductive.isLargeEliminator stats indTypes.toArray context =
      .ok result) : result = true := by
  subst stats
  subst indTypes
  simp [AddInductive.isLargeEliminator,
    AddInductive.PrimitiveRecursorReplay.natStats,
    ReaderT.pure, Pure.pure, Except.pure] at run
  exact run

private theorem natKTargetResultOfRun
    {stats : AddInductive.InductiveStats}
    {indTypes : List InductiveType} {context : AddInductive.Context}
    {result : Bool} (binderName : Name) (binderInfo : BinderInfo)
    (stats_eq : stats = AddInductive.PrimitiveRecursorReplay.natStats)
    (types_eq : indTypes =
      [AddInductive.PrimitiveRecursorReplay.natSource binderName binderInfo])
    (run : AddInductive.isKTarget stats indTypes.toArray context = .ok result) :
    result = false := by
  subst stats
  subst indTypes
  have expected : AddInductive.isKTarget
      AddInductive.PrimitiveRecursorReplay.natStats
      #[AddInductive.PrimitiveRecursorReplay.natSource binderName binderInfo]
      context = .ok false := by
    rfl
  exact Except.ok.inj (run.symm.trans expected)

/-- Reconstruct the exact translation of every recursor record emitted by a
recognized primitive execution.  All operational choices are recovered from
the retained normalization/elimination run; alignment is used only to recover
the implementation family lookup needed by recursive Nat synthesis. -/
theorem canonicalPrimitiveRecursorEvidence
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe true fuel finalEnv)
    (primitiveResult : PrimitiveInductiveResult lparams nparams types isUnsafe
      true) (input : VEnv) (inputOrdered : input.Ordered)
    (pre : Aligned safety env.constants input)
    (families : VInductDecl.FamilyDeclarationInsertionRun
      execution.flattened.eliminationExecution.normalization.validationContext.allowPrimitive
      execution.flattened.eliminationExecution.normalization.validationContext.env
      execution.flattened.eliminationExecution.normalization.familyEnv
      execution.flattened.eliminationExecution.normalization.declaredInfos
      input (VPrimitiveInductive.canonicalDecl types).blockTypeConstants)
    (constructors : VInductDecl.ConstructorDeclarationInsertionRun
      execution.flattened.eliminationExecution.constructorContext.allowPrimitive
      execution.flattened.eliminationExecution.normalization.familyEnv
      execution.flattened.eliminationExecution.constructorEnv
      execution.flattened.eliminationExecution.declaredConstructorInfos
      families.blockEnv
      (VPrimitiveInductive.canonicalDecl types).blockConstructorConstants) :
    List.Forall₂
      (fun info raw => TrConstVal .safe constructors.ctorEnv
        (.recInfo info) raw)
      execution.flattened.recursors.infos
      (VPrimitiveInductive.canonicalGeneration types).recursors := by
  have noop := execution.canonicalPrimitive_noop primitiveResult
  have generationWF := execution.canonicalPrimitiveGenerationWF
    primitiveResult input families
  have generationEnv :=
    AddInductive.PrimitiveRecursorReplay.generationEnv_of_insertion
      inputOrdered generationWF families.addTypes constructors.addCtors
  have initialAligned : Aligned safety
      execution.flattened.eliminationExecution.normalization.validationContext.env.constants
      input := by
    simpa only [execution.flattenedValidationEnv_eq] using pre
  have familyMapWF := families.addTypes.map_wf initialAligned.map_wf
  have constructorMapWF := constructors.addCtors.map_wf familyMapWF
  have recognized := primitiveResult.recognized rfl
  obtain ⟨safe, lparamsEq, nparamsEq, shape⟩ := recognized
  obtain ⟨type, typesEq, typeType, primitive⟩ := shape
  cases primitive with
  | inl boolShape =>
      obtain ⟨typeName, constructorsEq⟩ := boolShape
      have typeEq : type =
          AddInductive.PrimitiveRecursorReplay.boolSource := by
        cases type
        subst typeName
        subst typeType
        subst constructorsEq
        rfl
      subst type
      subst types
      subst lparams
      subst nparams
      subst isUnsafe
      have nestedTypesEq : execution.nested.types =
          [AddInductive.PrimitiveRecursorReplay.boolSource] := noop.1
      have normalizationRun :=
        execution.flattened.normalization_run execution.flattenedRun
      obtain ⟨statsEq, validationEq, depth, inductiveFuel, depthEq,
          inductiveEq⟩ :=
        canonicalSingletonStatsAndFuelOfEq nestedTypesEq
          normalizationRun (by rfl)
      have boolStatsEq :
          execution.flattened.eliminationExecution.normalization.stats =
            AddInductive.PrimitiveRecursorReplay.boolStats := by
        rw [statsEq]
        rfl
      have validationEq' :
          execution.flattened.eliminationExecution.normalization.validationContext =
            AddInductive.Context.forInductive env [] false true fuel :=
        validationEq
      have largeResult :
          execution.flattened.eliminationExecution.elimination.large.result =
            true := by
        apply boolLargeResultOfRun boolStatsEq
        · exact nestedTypesEq
        · exact execution.flattened.eliminationExecution.elimination.large.run_eq
      have elimLevel :
          execution.flattened.eliminationExecution.elimination.level =
            .param `u := by
        rw [execution.flattened.eliminationExecution.elimination.level_eq_param
          largeResult]
        simp [validationEq', AddInductive.Context.forInductive,
          AddInductive.getFreshElimParam,
          AddInductive.getFreshElimParam.loop]
      have kTarget :
          execution.flattened.eliminationExecution.kTarget.result = false := by
        apply boolKTargetResultOfRun boolStatsEq
        · exact nestedTypesEq
        · exact execution.flattened.eliminationExecution.kTarget.run_eq
      let root : AddInductive.Context := {
        execution.flattened.eliminationExecution.normalization.validationContext with
        env := execution.flattened.eliminationExecution.constructorEnv }
      have rootEq : root = {
          AddInductive.Context.forInductive env [] false true fuel with
          env := execution.flattened.eliminationExecution.constructorEnv } := by
        simp only [root, validationEq']
      have rootRun : TypeChecker.CandidateLocalContextRun root := by
        apply TypeChecker.CandidateLocalContextRun.empty root
        simp [rootEq, AddInductive.Context.forInductive]
      have rootLparams : root.lparams = [] := by
        simp [rootEq, AddInductive.Context.forInductive]
      have rootSafety : root.safety = .safe := by
        simp [rootEq, AddInductive.Context.forInductive]
      have rootDepth : root.fuel.recDepth = depth + 1 := by
        simpa [rootEq, AddInductive.Context.forInductive] using depthEq
      have rootInductive : root.fuel.inductiveFuel = inductiveFuel + 1 := by
        simpa [rootEq, AddInductive.Context.forInductive] using inductiveEq
      have rootWhnf : TypeChecker.M.run root.env root.safety root.lctx
          root.lparams root.fuel
          (TypeChecker.whnf
            AddInductive.PrimitiveRecursorReplay.boolSource.type) =
            .ok (.sort (.succ .zero)) := by
        simpa [AddInductive.PrimitiveRecursorReplay.boolSource] using
          AddInductive.PrimitiveRecursorReplay.whnfSortOne root depth rootDepth
      have recursorsRun : AddInductive.declareRecursors
          AddInductive.PrimitiveRecursorReplay.boolStats
          #[AddInductive.PrimitiveRecursorReplay.boolSource]
          (.param `u) false root = .ok execution.flattened.recursors := by
        simpa only [root, boolStatsEq, nestedTypesEq, elimLevel, kTarget] using
          execution.flattened.recursorsRun
      have expected :=
        AddInductive.PrimitiveRecursorReplay.boolExpectedRecursorTranslation
          generationEnv
      have evidence :=
        AddInductive.PrimitiveRecursorReplay.declareRecursors_bool_evidence
          root rootRun rootLparams rootSafety rootWhnf rootInductive
          recursorsRun expected
      change List.Forall₂
        (fun info raw => TrConstVal .safe constructors.ctorEnv
          (.recInfo info) raw)
        execution.flattened.recursors.infos
        VPrimitiveInductive.boolGeneration.recursors
      rw [show VPrimitiveInductive.boolGeneration.recursors =
        [VPrimitiveInductive.boolGeneration.recursors[0]] by rfl]
      exact evidence
  | inr natShape =>
      obtain ⟨typeName, binderName, binderInfo, constructorsEq⟩ := natShape
      have typeEq : type =
          AddInductive.PrimitiveRecursorReplay.natSource
            binderName binderInfo := by
        cases type
        subst typeName
        subst typeType
        subst constructorsEq
        rfl
      subst type
      subst types
      subst lparams
      subst nparams
      subst isUnsafe
      have nestedTypesEq : execution.nested.types =
          [AddInductive.PrimitiveRecursorReplay.natSource
            binderName binderInfo] := noop.1
      have normalizationRun :=
        execution.flattened.normalization_run execution.flattenedRun
      obtain ⟨statsEq, validationEq, depth, inductiveFuel, depthEq,
          inductiveEq⟩ :=
        canonicalSingletonStatsAndFuelOfEq nestedTypesEq
          normalizationRun (by rfl)
      have natStatsEq :
          execution.flattened.eliminationExecution.normalization.stats =
            AddInductive.PrimitiveRecursorReplay.natStats := by
        rw [statsEq]
        rfl
      have validationEq' :
          execution.flattened.eliminationExecution.normalization.validationContext =
            AddInductive.Context.forInductive env [] false true fuel :=
        validationEq
      have largeResult :
          execution.flattened.eliminationExecution.elimination.large.result =
            true := by
        apply natLargeResultOfRun binderName binderInfo natStatsEq
        · exact nestedTypesEq
        · exact execution.flattened.eliminationExecution.elimination.large.run_eq
      have elimLevel :
          execution.flattened.eliminationExecution.elimination.level =
            .param `u := by
        rw [execution.flattened.eliminationExecution.elimination.level_eq_param
          largeResult]
        simp [validationEq', AddInductive.Context.forInductive,
          AddInductive.getFreshElimParam,
          AddInductive.getFreshElimParam.loop]
      have kTarget :
          execution.flattened.eliminationExecution.kTarget.result = false := by
        apply natKTargetResultOfRun binderName binderInfo natStatsEq
        · exact nestedTypesEq
        · exact execution.flattened.eliminationExecution.kTarget.run_eq
      let root : AddInductive.Context := {
        execution.flattened.eliminationExecution.normalization.validationContext with
        env := execution.flattened.eliminationExecution.constructorEnv }
      have rootEq : root = {
          AddInductive.Context.forInductive env [] false true fuel with
          env := execution.flattened.eliminationExecution.constructorEnv } := by
        simp only [root, validationEq']
      have rootRun : TypeChecker.CandidateLocalContextRun root := by
        apply TypeChecker.CandidateLocalContextRun.empty root
        simp [rootEq, AddInductive.Context.forInductive]
      have rootLparams : root.lparams = [] := by
        simp [rootEq, AddInductive.Context.forInductive]
      have rootSafety : root.safety = .safe := by
        simp [rootEq, AddInductive.Context.forInductive]
      have rootDepth : root.fuel.recDepth = depth + 1 := by
        simpa [rootEq, AddInductive.Context.forInductive] using depthEq
      have rootWhnf : TypeChecker.M.run root.env root.safety root.lctx
          root.lparams root.fuel
          (TypeChecker.whnf
            (AddInductive.PrimitiveRecursorReplay.natSource
              binderName binderInfo).type) =
            .ok (.sort (.succ .zero)) := by
        simpa [AddInductive.PrimitiveRecursorReplay.natSource] using
          AddInductive.PrimitiveRecursorReplay.whnfSortOne root depth rootDepth
      have recursorsRun : AddInductive.declareRecursors
          AddInductive.PrimitiveRecursorReplay.natStats
          #[AddInductive.PrimitiveRecursorReplay.natSource
            binderName binderInfo]
          (.param `u) false root = .ok execution.flattened.recursors := by
        simpa only [root, natStatsEq, nestedTypesEq, elimLevel, kTarget] using
          execution.flattened.recursorsRun
      have rootInductivePositive : root.fuel.inductiveFuel =
          inductiveFuel + 1 := by
        simpa [rootEq, AddInductive.Context.forInductive] using inductiveEq
      obtain ⟨rootWhnfFuel, rootInductive⟩ :=
        AddInductive.PrimitiveRecursorReplay.declareRecursors_nat_fuel
          root binderName binderInfo depth rootDepth inductiveFuel
          rootInductivePositive rootWhnf recursorsRun
      have natFamilyMember : VPrimitiveInductive.natType.toVConstVal ∈
          (VPrimitiveInductive.canonicalDecl
            [AddInductive.PrimitiveRecursorReplay.natSource
              binderName binderInfo]).blockTypeConstants := by
        simp [VPrimitiveInductive.canonicalDecl,
          VInductDecl.blockTypeConstants, VPrimitiveInductive.natDecl,
          VPrimitiveInductive.natType,
          AddInductive.PrimitiveRecursorReplay.natSource]
      obtain ⟨familyConstant, familyLookup, familyKind, _familyTranslation⟩ :=
        families.addTypes.translated_lookup initialAligned.map_wf
          natFamilyMember
      have familyLookup' := constructors.addCtors.preserve_map_lookup
        familyMapWF familyLookup
      have rootMapWF : root.env.constants.WF := by
        simpa only [root] using constructorMapWF
      have rootFindConstant : root.env.find? ``Nat = some familyConstant := by
        change root.env.constants.find?' ``Nat = some familyConstant
        rw [rootMapWF.find?'_eq_find?]
        simpa [root, VPrimitiveInductive.natType] using familyLookup'
      have familyLookupFinal : ∃ familyInfo,
          root.env.find? ``Nat = some (.inductInfo familyInfo) := by
        cases familyConstant <;>
          simp_all [InductConstantKind.Matches]
      obtain ⟨familyInfo, rootFind⟩ := familyLookupFinal
      obtain ⟨whnfFuel, rootWhnfFuel⟩ := rootWhnfFuel
      obtain ⟨recFuel, rootInductive⟩ := rootInductive
      have expected :=
        AddInductive.PrimitiveRecursorReplay.natExpectedRecursorTranslation
          generationEnv
      have evidence :=
        AddInductive.PrimitiveRecursorReplay.declareRecursors_nat_evidence
          root binderName binderInfo rootRun rootLparams rootSafety familyInfo
          rootFind rootWhnf rootDepth rootWhnfFuel rootInductive
          recursorsRun expected
      change List.Forall₂
        (fun info raw => TrConstVal .safe constructors.ctorEnv
          (.recInfo info) raw)
        execution.flattened.recursors.infos
        VPrimitiveInductive.natGeneration.recursors
      rw [show VPrimitiveInductive.natGeneration.recursors =
        [VPrimitiveInductive.natGeneration.recursors[0]] by rfl]
      exact evidence

/-- The K-like flag retained by primitive recursor declaration is the flag of
the recognizer-selected canonical generation. -/
theorem canonicalPrimitiveKTarget_eq
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe true fuel finalEnv)
    (primitiveResult : PrimitiveInductiveResult lparams nparams types isUnsafe
      true) :
    execution.flattened.recursors.kTarget =
      (VPrimitiveInductive.canonicalGeneration types).kTarget := by
  have noop := execution.canonicalPrimitive_noop primitiveResult
  have recognized := primitiveResult.recognized rfl
  obtain ⟨safe, lparamsEq, nparamsEq, shape⟩ := recognized
  obtain ⟨type, typesEq, typeType, primitive⟩ := shape
  cases primitive with
  | inl boolShape =>
      obtain ⟨typeName, constructorsEq⟩ := boolShape
      have typeEq : type =
          AddInductive.PrimitiveRecursorReplay.boolSource := by
        cases type
        subst typeName
        subst typeType
        subst constructorsEq
        rfl
      subst type
      subst types
      subst lparams
      subst nparams
      subst isUnsafe
      have nestedTypesEq : execution.nested.types =
          [AddInductive.PrimitiveRecursorReplay.boolSource] := noop.1
      have normalizationRun :=
        execution.flattened.normalization_run execution.flattenedRun
      have normalized := canonicalSingletonStatsAndFuelOfEq
        nestedTypesEq normalizationRun (by rfl)
      have statsEq :
          execution.flattened.eliminationExecution.normalization.stats =
            AddInductive.PrimitiveRecursorReplay.boolStats := by
        rw [normalized.1]
        rfl
      have resultFalse :
          execution.flattened.eliminationExecution.kTarget.result = false := by
        exact boolKTargetResultOfRun statsEq nestedTypesEq
          execution.flattened.eliminationExecution.kTarget.run_eq
      calc
        execution.flattened.recursors.kTarget =
            execution.flattened.eliminationExecution.kTarget.result :=
          AddInductive.declareRecursors_kTarget_eq
            execution.flattened.recursorsRun
        _ = false := resultFalse
        _ = (VPrimitiveInductive.canonicalGeneration
            [AddInductive.PrimitiveRecursorReplay.boolSource]).kTarget := by
          rfl
  | inr natShape =>
      obtain ⟨typeName, binderName, binderInfo, constructorsEq⟩ := natShape
      have typeEq : type =
          AddInductive.PrimitiveRecursorReplay.natSource
            binderName binderInfo := by
        cases type
        subst typeName
        subst typeType
        subst constructorsEq
        rfl
      subst type
      subst types
      subst lparams
      subst nparams
      subst isUnsafe
      have nestedTypesEq : execution.nested.types =
          [AddInductive.PrimitiveRecursorReplay.natSource
            binderName binderInfo] := noop.1
      have normalizationRun :=
        execution.flattened.normalization_run execution.flattenedRun
      have normalized := canonicalSingletonStatsAndFuelOfEq
        nestedTypesEq normalizationRun (by rfl)
      have statsEq :
          execution.flattened.eliminationExecution.normalization.stats =
            AddInductive.PrimitiveRecursorReplay.natStats := by
        rw [normalized.1]
        rfl
      have resultFalse :
          execution.flattened.eliminationExecution.kTarget.result = false := by
        exact natKTargetResultOfRun binderName binderInfo statsEq nestedTypesEq
          execution.flattened.eliminationExecution.kTarget.run_eq
      calc
        execution.flattened.recursors.kTarget =
            execution.flattened.eliminationExecution.kTarget.result :=
          AddInductive.declareRecursors_kTarget_eq
            execution.flattened.recursorsRun
        _ = false := resultFalse
        _ = (VPrimitiveInductive.canonicalGeneration
            [AddInductive.PrimitiveRecursorReplay.natSource
              binderName binderInfo]).kTarget := by
          rfl

/-- Interpret the retained primitive recursor declaration directly after the
canonical constructor insertion. -/
noncomputable def canonicalPrimitiveRecursorInsertion
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe true fuel finalEnv)
    (primitiveResult : PrimitiveInductiveResult lparams nparams types isUnsafe
      true) (input : VEnv) (inputOrdered : input.Ordered)
    (pre : Aligned safety env.constants input)
    (families : VInductDecl.FamilyDeclarationInsertionRun
      execution.flattened.eliminationExecution.normalization.validationContext.allowPrimitive
      execution.flattened.eliminationExecution.normalization.validationContext.env
      execution.flattened.eliminationExecution.normalization.familyEnv
      execution.flattened.eliminationExecution.normalization.declaredInfos
      input (VPrimitiveInductive.canonicalDecl types).blockTypeConstants)
    (constructors : VInductDecl.ConstructorDeclarationInsertionRun
      execution.flattened.eliminationExecution.constructorContext.allowPrimitive
      execution.flattened.eliminationExecution.normalization.familyEnv
      execution.flattened.eliminationExecution.constructorEnv
      execution.flattened.eliminationExecution.declaredConstructorInfos
      families.blockEnv
      (VPrimitiveInductive.canonicalDecl types).blockConstructorConstants) :
    VInductDecl.RecursorDeclarationInsertionRun
      execution.flattened.recursors.allowPrimitive
      execution.flattened.recursors.initialEnv
      execution.flattened.recursors.env execution.flattened.recursors.infos
      constructors.ctorEnv
      (VPrimitiveInductive.canonicalGeneration types).recursors
      (VPrimitiveInductive.canonicalGeneration types).kTarget := by
  apply VInductDecl.recursorDeclarationInsertion
  · exact execution.flattened.recursors.trace.run
  · exact execution.canonicalPrimitiveRecursorEvidence primitiveResult
      input inputOrdered pre families constructors
  · intro info member
    rw [← execution.canonicalPrimitiveKTarget_eq primitiveResult]
    exact execution.flattened.recursors.infos_kTarget info member
  · have initialAligned : Aligned safety
        execution.flattened.eliminationExecution.normalization.validationContext.env.constants
        input := by
      simpa only [execution.flattenedValidationEnv_eq] using pre
    have constructorAligned :=
      (initialAligned.addInductConstants families.addTypes).addInductConstants
        constructors.addCtors
    simpa only [execution.flattened.recursor_initialEnv_eq] using
      constructorAligned

/-- The canonical Theory environment after registering every generated
reduction rule.  Host rule metadata is already carried by the recursor record;
the Theory-side transaction is the deterministic `addDefEq` fold. -/
def canonicalPrimitiveRuleOutput (types : List InductiveType)
    (recEnv : VEnv) : VEnv :=
  (VPrimitiveInductive.canonicalGeneration types).generatedRules.foldl
    VEnv.addDefEq recEnv

/-- Witness the exact generated-rule tail of a canonical primitive
transaction. -/
theorem canonicalPrimitiveRuleInsertion
    (types : List InductiveType) (recEnv : VEnv) : AddDefEqs recEnv
      (VPrimitiveInductive.canonicalGeneration types).generatedRules
      (canonicalPrimitiveRuleOutput types recEnv) :=
  ⟨rfl⟩

end AddInductive.EnvironmentInductiveExecution

/-- In the ordinary branch, the environment produced by the retained recursor
declaration is definitionally the outer execution's final environment. -/
theorem AddInductive.EnvironmentInductiveExecution.flattenedEnv_eq_final
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv)
    (numNested_eq : execution.nested.aux2nested.size = 0) :
    execution.flattened.recursors.env = finalEnv := by
  cases execution with
  | mk inputCheck nested nestedRun flattened flattenedRun completion =>
      cases completion with
      | ordinary _ => rfl
      | nested numNested_ne restoration restorationRun =>
          exact (numNested_ne numNested_eq).elim

/-- Primitive-specific semantic replay of the exact metadata phases retained
by one ordinary outer execution.  This surface intentionally starts after
candidate interpretation: a primitive family by itself temporarily violates
`VEnv.HasPrimitives`, so the generic post-family checker context cannot be used
between the family and constructor phases.  It also retains only the insertion
folds needed by the public trace, rather than the generic staging records'
`TrEnv' .safe` postconditions; those postconditions would incorrectly exclude
partial and unsafe input models containing additional visible constants.  All
kernel-map endpoints and Theory inventories remain fixed by `execution` and the
canonical declaration, so no parallel host inventory or normalization run is
accepted. -/
structure AddInductive.EnvironmentInductiveExecution.CanonicalPrimitiveReplay
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe true fuel finalEnv)
    (input output : VEnv) where
  blockEnv : VEnv
  generation_wf : (VPrimitiveInductive.canonicalGeneration types).WF input
    blockEnv
  addTypes : AddInductConstants .induct
    execution.flattened.eliminationExecution.normalization.validationContext.env.constants
    input
    (VPrimitiveInductive.canonicalDecl types).blockTypeConstants
    execution.flattened.eliminationExecution.normalization.familyEnv.constants
    blockEnv
  ctorEnv : VEnv
  addCtors : AddInductConstants .ctor
    execution.flattened.eliminationExecution.normalization.familyEnv.constants
    blockEnv (VPrimitiveInductive.canonicalDecl types).blockConstructorConstants
    execution.flattened.eliminationExecution.constructorEnv.constants ctorEnv
  recEnv : VEnv
  addRecs : AddInductConstants .recursor
    execution.flattened.recursors.initialEnv.constants ctorEnv
    (VPrimitiveInductive.canonicalGeneration types).recursors
    execution.flattened.recursors.env.constants recEnv
  recK : RecursorMapKMatches execution.flattened.recursors.env.constants
    (VPrimitiveInductive.canonicalGeneration types).recursors
    (VPrimitiveInductive.canonicalGeneration types).kTarget
  addRules : AddDefEqs recEnv
    (VPrimitiveInductive.canonicalGeneration types).generatedRules output

namespace AddInductive.EnvironmentInductiveExecution.CanonicalPrimitiveReplay

/-- Assemble the primitive replay from the three lightweight metadata
insertion interpreters.  Their retained kernel traces and map endpoints are
fixed by `execution`; unlike the generic staging records, none carries an
intermediate `TrEnv' .safe` postcondition. -/
def ofInsertions
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe true fuel finalEnv}
    {input output : VEnv}
    (families : VInductDecl.FamilyDeclarationInsertionRun
      execution.flattened.eliminationExecution.normalization.validationContext.allowPrimitive
      execution.flattened.eliminationExecution.normalization.validationContext.env
      execution.flattened.eliminationExecution.normalization.familyEnv
      execution.flattened.eliminationExecution.normalization.declaredInfos
      input (VPrimitiveInductive.canonicalDecl types).blockTypeConstants)
    (primitiveResult : PrimitiveInductiveResult lparams nparams types isUnsafe
      true)
    (constructors : VInductDecl.ConstructorDeclarationInsertionRun
      execution.flattened.eliminationExecution.constructorContext.allowPrimitive
      execution.flattened.eliminationExecution.normalization.familyEnv
      execution.flattened.eliminationExecution.constructorEnv
      execution.flattened.eliminationExecution.declaredConstructorInfos
      families.blockEnv
      (VPrimitiveInductive.canonicalDecl types).blockConstructorConstants)
    (recursors : VInductDecl.RecursorDeclarationInsertionRun
      execution.flattened.recursors.allowPrimitive
      execution.flattened.recursors.initialEnv
      execution.flattened.recursors.env execution.flattened.recursors.infos
      constructors.ctorEnv
      (VPrimitiveInductive.canonicalGeneration types).recursors
      (VPrimitiveInductive.canonicalGeneration types).kTarget)
    (addRules : AddDefEqs recursors.recEnv
      (VPrimitiveInductive.canonicalGeneration types).generatedRules output) :
    execution.CanonicalPrimitiveReplay input output where
  blockEnv := families.blockEnv
  generation_wf := execution.canonicalPrimitiveGenerationWF
    primitiveResult input families
  addTypes := families.addTypes
  ctorEnv := constructors.ctorEnv
  addCtors := constructors.addCtors
  recEnv := recursors.recEnv
  addRecs := recursors.addRecs
  recK := recursors.recK
  addRules := addRules

/-- Assemble the exact ordinary trace at the retained normalization and
recursor map endpoints.  All intermediate maps and Theory environments are
the endpoints of the three execution-indexed insertion folds above. -/
def toFlattenedTrace
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe true fuel finalEnv}
    {input output : VEnv}
    (replay : execution.CanonicalPrimitiveReplay input output) :
    AddInductBlockTrace
      execution.flattened.eliminationExecution.normalization.validationContext.env.constants
      input (VPrimitiveInductive.canonicalDecl types)
      execution.flattened.recursors.env.constants output where
  generation := VPrimitiveInductive.canonicalGeneration types
  blockEnv := replay.blockEnv
  generation_wf := replay.generation_wf
  typeMap :=
    execution.flattened.eliminationExecution.normalization.familyEnv.constants
  typeEnv := replay.blockEnv
  ctorMap := execution.flattened.eliminationExecution.constructorEnv.constants
  ctorEnv := replay.ctorEnv
  recEnv := replay.recEnv
  addTypes := replay.addTypes
  addCtors := replay.addCtors
  addRecs := by
    simpa only [execution.flattened.recursor_initialEnv_eq] using
      replay.addRecs
  recK := replay.recK
  addRules := replay.addRules

/-- Retarget the insertion-fold replay to the public outer endpoints.  Primitive
recognition proves that nested elimination was a no-op, so the retained
recursor environment is the actual final environment. -/
def toTrace
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe true fuel finalEnv}
    {input output : VEnv}
    (replay : execution.CanonicalPrimitiveReplay input output)
    (primitiveResult : PrimitiveInductiveResult lparams nparams types isUnsafe
      true) :
    AddInductBlockTrace env.constants input
      (VPrimitiveInductive.canonicalDecl types) finalEnv.constants output := by
  have initialEq := execution.flattenedValidationEnv_eq
  have finalEq := execution.flattenedEnv_eq_final
    (execution.canonicalPrimitive_noop primitiveResult).2
  exact {
    generation := VPrimitiveInductive.canonicalGeneration types
    blockEnv := replay.blockEnv
    generation_wf := replay.generation_wf
    typeMap :=
      execution.flattened.eliminationExecution.normalization.familyEnv.constants
    typeEnv := replay.blockEnv
    ctorMap := execution.flattened.eliminationExecution.constructorEnv.constants
    ctorEnv := replay.ctorEnv
    recEnv := replay.recEnv
    addTypes := by simpa only [initialEq] using replay.addTypes
    addCtors := replay.addCtors
    addRecs := by
      simpa only [execution.flattened.recursor_initialEnv_eq, finalEq] using
        replay.addRecs
    recK := by simpa only [finalEq] using replay.recK
    addRules := replay.addRules }

end AddInductive.EnvironmentInductiveExecution.CanonicalPrimitiveReplay

/-- The pointwise output selected by replaying the retained family,
constructor, and recursor declarations and then folding the canonical
generated rules. -/
noncomputable def
    AddInductive.EnvironmentInductiveExecution.canonicalPrimitivePointwiseOutput
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe true fuel finalEnv)
    (primitiveResult : PrimitiveInductiveResult lparams nparams types isUnsafe
      true) (input : VEnv) (inputOrdered : input.Ordered)
    (pre : Aligned safety env.constants input) : VEnv :=
  let families :=
    execution.canonicalPrimitiveFamilyInsertion primitiveResult input pre
  let constructors :=
    execution.canonicalPrimitiveConstructorInsertion primitiveResult input pre
      families
  let recursors :=
    execution.canonicalPrimitiveRecursorInsertion primitiveResult input
      inputOrdered pre families constructors
  AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveRuleOutput
    types recursors.recEnv

/-- Construct the complete canonical primitive replay at one safety-indexed
input model directly from the retained outer execution. -/
noncomputable def
    AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveReplay
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe true fuel finalEnv)
    (primitiveResult : PrimitiveInductiveResult lparams nparams types isUnsafe
      true) (input : VEnv) (inputOrdered : input.Ordered)
    (pre : Aligned safety env.constants input) :
    execution.CanonicalPrimitiveReplay input
      (execution.canonicalPrimitivePointwiseOutput primitiveResult input
        inputOrdered pre) := by
  let families :=
    execution.canonicalPrimitiveFamilyInsertion primitiveResult input pre
  let constructors :=
    execution.canonicalPrimitiveConstructorInsertion primitiveResult input pre
      families
  let recursors :=
    execution.canonicalPrimitiveRecursorInsertion primitiveResult input
      inputOrdered pre families constructors
  exact CanonicalPrimitiveReplay.ofInsertions families primitiveResult
    constructors recursors
    (AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveRuleInsertion
      types recursors.recEnv)

/-- The fixed canonical generation replayed against every safety-indexed input
model.  Coherence is structural: every pointwise trace below is assembled from
that generation and the same retained kernel execution. -/
structure AddInductive.EnvironmentInductiveExecution.CoherentCanonicalPrimitiveReplay
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe true fuel finalEnv)
    (input : VEnvs) where
  output : VEnvs
  replays : ∀ safety, execution.CanonicalPrimitiveReplay
    (input.venv safety) (output.venv safety)

namespace AddInductive.EnvironmentInductiveExecution.CoherentCanonicalPrimitiveReplay

/-- Select the exact public trace at one safety level. -/
def trace
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe true fuel finalEnv}
    {input : VEnvs}
    (replay : execution.CoherentCanonicalPrimitiveReplay input)
    (primitiveResult : PrimitiveInductiveResult lparams nparams types isUnsafe
      true) (safety : DefinitionSafety) :
    AddInductBlockTrace env.constants (input.venv safety)
      (VPrimitiveInductive.canonicalDecl types) finalEnv.constants
      (replay.output.venv safety) :=
  (replay.replays safety).toTrace primitiveResult

@[simp] theorem trace_generation
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe true fuel finalEnv}
    {input : VEnvs}
    (replay : execution.CoherentCanonicalPrimitiveReplay input)
    (primitiveResult : PrimitiveInductiveResult lparams nparams types isUnsafe
      true) (safety : DefinitionSafety) :
    (replay.trace primitiveResult safety).generation =
      VPrimitiveInductive.canonicalGeneration types :=
  rfl

/-- Replay the exact primitive transaction after an existing translated input
history. -/
theorem trEnv
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe true fuel finalEnv}
    {input : VEnvs}
    (replay : execution.CoherentCanonicalPrimitiveReplay input)
    (primitiveResult : PrimitiveInductiveResult lparams nparams types isUnsafe
      true) (wf : input.WF env) (safety : DefinitionSafety) :
    TrEnv safety finalEnv (replay.output.venv safety) := by
  let transaction : execution.ExactSemanticTransaction
      (VPrimitiveInductive.canonicalDecl types)
      (input.venv safety) (replay.output.venv safety) :=
    .ordinary (execution.canonicalPrimitive_noop primitiveResult).2
      ⟨replay.trace primitiveResult safety⟩
  exact transaction.trEnv (wf.tr (safety := safety))

/-- The output selected by the canonical replay is a well-formed Theory
environment at every safety level. -/
theorem outputWF
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe true fuel finalEnv}
    {input : VEnvs}
    (replay : execution.CoherentCanonicalPrimitiveReplay input)
    (primitiveResult : PrimitiveInductiveResult lparams nparams types isUnsafe
      true) (wf : input.WF env) (safety : DefinitionSafety) :
    (replay.output.venv safety).WF :=
  (replay.trEnv primitiveResult wf safety).wf

/-- Every pointwise primitive replay monotonically extends its input model. -/
theorem old_le
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe true fuel finalEnv}
    {input : VEnvs}
    (replay : execution.CoherentCanonicalPrimitiveReplay input)
    (primitiveResult : PrimitiveInductiveResult lparams nparams types isUnsafe
      true) (safety : DefinitionSafety) :
    input.venv safety ≤ replay.output.venv safety :=
  (replay.trace primitiveResult safety).le

end AddInductive.EnvironmentInductiveExecution.CoherentCanonicalPrimitiveReplay

/-- Assemble the safety-indexed canonical primitive replay from an input
environment model.  Ordering and alignment at each safety level are projected
from the existing translation history. -/
noncomputable def
    AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveCoherentReplay
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe true fuel finalEnv)
    (primitiveResult : PrimitiveInductiveResult lparams nparams types isUnsafe
      true) (ves : VEnvs) (wf : ves.WF env) :
    execution.CoherentCanonicalPrimitiveReplay ves where
  output := ⟨fun safety =>
    execution.canonicalPrimitivePointwiseOutput primitiveResult
      (ves.venv safety) (wf.tr.wf.ordered) (wf.tr.aligned)⟩
  replays safety :=
    execution.canonicalPrimitiveReplay primitiveResult (ves.venv safety)
      (wf.tr.wf.ordered) (wf.tr.aligned)

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.flattenedValidationEnv_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms AddInductive.EnvironmentInductiveExecution.flattenedValidationEnv_eq

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.flattenedValidationLparams_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms AddInductive.EnvironmentInductiveExecution.flattenedValidationLparams_eq

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveFamilyEvidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.abstract_eq]
-/
#guard_msgs in
#print axioms AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveFamilyEvidence

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveFamilyInsertion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.abstract_eq,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveFamilyInsertion

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveGenerationWF' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveGenerationWF

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveConstructorEvidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.abstract_eq]
-/
#guard_msgs in
#print axioms AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveConstructorEvidence

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveConstructorInsertion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.abstract_eq,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveConstructorInsertion

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveRecursorEvidence' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveRecursorEvidence

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveKTarget_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.looseBVarRange_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Syntax.structEq_eq]
-/
#guard_msgs in
#print axioms AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveKTarget_eq

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveRecursorInsertion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveRecursorInsertion

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveRuleInsertion' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveRuleInsertion

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveReplay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveReplay

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveCoherentReplay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveCoherentReplay

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.flattenedEnv_eq_final' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms AddInductive.EnvironmentInductiveExecution.flattenedEnv_eq_final

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.CanonicalPrimitiveReplay.ofInsertions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms AddInductive.EnvironmentInductiveExecution.CanonicalPrimitiveReplay.ofInsertions

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.CanonicalPrimitiveReplay.toFlattenedTrace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms AddInductive.EnvironmentInductiveExecution.CanonicalPrimitiveReplay.toFlattenedTrace

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.CanonicalPrimitiveReplay.toTrace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.abstract_eq]
-/
#guard_msgs in
#print axioms AddInductive.EnvironmentInductiveExecution.CanonicalPrimitiveReplay.toTrace

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.CoherentCanonicalPrimitiveReplay.trace' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.abstract_eq]
-/
#guard_msgs in
#print axioms AddInductive.EnvironmentInductiveExecution.CoherentCanonicalPrimitiveReplay.trace

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.CoherentCanonicalPrimitiveReplay.trEnv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.abstract_eq]
-/
#guard_msgs in
#print axioms AddInductive.EnvironmentInductiveExecution.CoherentCanonicalPrimitiveReplay.trEnv

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.CoherentCanonicalPrimitiveReplay.outputWF' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.abstract_eq]
-/
#guard_msgs in
#print axioms AddInductive.EnvironmentInductiveExecution.CoherentCanonicalPrimitiveReplay.outputWF

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.CoherentCanonicalPrimitiveReplay.old_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.abstract_eq]
-/
#guard_msgs in
#print axioms AddInductive.EnvironmentInductiveExecution.CoherentCanonicalPrimitiveReplay.old_le

/-- A coherent ordinary replay of a canonical primitive-recognized block.
Unlike the nonprimitive transaction package, primitive preservation is
derived from the exact Bool/Nat generated inventory rather than name
avoidance. The raw Theory declaration is selected directly from the
recognizer's closed host syntax; producers do not choose a parallel source or
semantic normalization run. The fixed canonical generation is selected
internally and used at every safety level. The nested-pass facts are derived
from the retained execution and recognizer result rather than supplied as
transaction fields. -/
structure AddInductive.EnvironmentInductiveExecution.CanonicalPrimitiveTransactionalVEnvsExtension
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe true fuel finalEnv)
    (ves : VEnvs) where
  primitiveResult : PrimitiveInductiveResult lparams nparams types isUnsafe true
  replay : execution.CoherentCanonicalPrimitiveReplay ves
  projectionReady : ∀ safety,
    ProjectionReady finalEnv (replay.output.venv safety)
  structureEtaReady : ∀ safety,
    StructureEtaReady finalEnv (replay.output.venv safety)

namespace AddInductive.EnvironmentInductiveExecution.CanonicalPrimitiveTransactionalVEnvsExtension

abbrev output
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe true fuel finalEnv}
    {ves : VEnvs}
    (extension : execution.CanonicalPrimitiveTransactionalVEnvsExtension ves) :
    VEnvs :=
  extension.replay.output

abbrev generation
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe true fuel finalEnv}
    {ves : VEnvs}
    (_extension : execution.CanonicalPrimitiveTransactionalVEnvsExtension ves) :
    (VPrimitiveInductive.canonicalDecl types).BlockGenerationChecked :=
  VPrimitiveInductive.canonicalGeneration types

/-- Exact pointwise trace derived from the retained execution replay. -/
def traces
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe true fuel finalEnv}
    {ves : VEnvs}
    (extension : execution.CanonicalPrimitiveTransactionalVEnvsExtension ves)
    (safety : DefinitionSafety) :
    AddInductBlockTrace env.constants (ves.venv safety)
      (VPrimitiveInductive.canonicalDecl types) finalEnv.constants
      (extension.output.venv safety) :=
  extension.replay.trace extension.primitiveResult safety

@[simp] theorem generation_eq
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe true fuel finalEnv}
    {ves : VEnvs}
    (extension : execution.CanonicalPrimitiveTransactionalVEnvsExtension ves)
    (safety : DefinitionSafety) :
    (extension.traces safety).generation = extension.generation :=
  rfl

/-- Complete the public primitive transaction package from the staged replay
of the retained execution.  Projection and structure-eta readiness remain
separate because they concern the final environment rather than metadata
alignment. -/
def ofReplay
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe true fuel finalEnv}
    {ves : VEnvs}
    (primitiveResult : PrimitiveInductiveResult lparams nparams types isUnsafe
      true)
    (replay : execution.CoherentCanonicalPrimitiveReplay ves)
    (projectionReady : ∀ safety,
      ProjectionReady finalEnv (replay.output.venv safety))
    (structureEtaReady : ∀ safety,
      StructureEtaReady finalEnv (replay.output.venv safety)) :
    execution.CanonicalPrimitiveTransactionalVEnvsExtension ves where
  primitiveResult := primitiveResult
  replay := replay
  projectionReady := projectionReady
  structureEtaReady := structureEtaReady

/-- Construct the primitive transaction directly from the retained execution
and the input environment model.  The only remaining arguments are the two
final-environment readiness predicates; all metadata replay is derived. -/
noncomputable def ofExecution
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe true fuel finalEnv}
    {ves : VEnvs} (wf : ves.WF env)
    (primitiveResult : PrimitiveInductiveResult lparams nparams types isUnsafe
      true)
    (projectionReady : ∀ safety, ProjectionReady finalEnv
      ((execution.canonicalPrimitiveCoherentReplay primitiveResult ves wf).output.venv
        safety))
    (structureEtaReady : ∀ safety, StructureEtaReady finalEnv
      ((execution.canonicalPrimitiveCoherentReplay primitiveResult ves wf).output.venv
        safety)) :
    execution.CanonicalPrimitiveTransactionalVEnvsExtension ves :=
  .ofReplay primitiveResult
    (execution.canonicalPrimitiveCoherentReplay primitiveResult ves wf)
    projectionReady structureEtaReady

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.CanonicalPrimitiveTransactionalVEnvsExtension.ofExecution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms AddInductive.EnvironmentInductiveExecution.CanonicalPrimitiveTransactionalVEnvsExtension.ofExecution

/-- Recover the exact raw Theory constants from the recognizer-selected
canonical declaration. -/
theorem canonicalConstants
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe true fuel finalEnv}
    {ves : VEnvs}
    (_extension :
      execution.CanonicalPrimitiveTransactionalVEnvsExtension ves) :
    (VPrimitiveInductive.canonicalDecl types).CanonicalPrimitiveConstants :=
  VPrimitiveInductive.canonicalDecl_constants
    (_extension.primitiveResult.recognized rfl).2.2.2

/-- Checked generation supplies the recursor name, turning the selected
family/constructor constants into the complete canonical inventory. -/
theorem canonicalInventory
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe true fuel finalEnv}
    {ves : VEnvs}
    (extension :
      execution.CanonicalPrimitiveTransactionalVEnvsExtension ves) :
    (VPrimitiveInductive.canonicalDecl types).CanonicalPrimitiveInventory
      extension.generation :=
  extension.canonicalConstants.toInventory
    extension.generation

/-- Canonical inventory plus coherent exact replay derives every semantic
field of the generic transaction package, including both primitive
invariants and cross-safety monotonicity. -/
def toTransactionalVEnvsExtension
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe true fuel finalEnv}
    {ves : VEnvs} (wf : ves.WF env)
    (extension :
      execution.CanonicalPrimitiveTransactionalVEnvsExtension ves) :
    execution.TransactionalVEnvsExtension ves where
  source := VPrimitiveInductive.canonicalDecl types
  output := extension.output
  transaction safety :=
    .ordinary (execution.canonicalPrimitive_noop extension.primitiveResult).2
      ⟨extension.traces safety⟩
  hasPrimitives safety :=
    extension.canonicalInventory.hasPrimitives
      (extension.traces safety)
      (extension.generation_eq safety)
      (wf.hasPrimitives (safety := safety))
  safePrimitives := by
    intro n ci found primitive
    have preTr : TrEnv' .safe env.constants env.quotInit
        (ves.venv .safe) := by
      simpa only [TrEnv] using wf.tr (safety := .safe)
    have transaction : execution.ExactSemanticTransaction
        (VPrimitiveInductive.canonicalDecl types)
        (ves.venv .safe) (extension.output.venv .safe) :=
      .ordinary
        (execution.canonicalPrimitive_noop extension.primitiveResult).2
        ⟨extension.traces .safe⟩
    have finalTr := transaction.trEnv preTr
    have finalSafe : ConstMapSafePrimitives finalEnv.constants :=
      extension.canonicalInventory.safePrimitivesMap
        (extension.traces .safe)
        (extension.generation_eq .safe) preTr.map_wf
        (ConstMapSafePrimitives.ofEnvironment preTr.map_wf
          wf.safePrimitives)
    exact ConstMapSafePrimitives.toEnvironment finalSafe finalTr.map_wf
      found primitive
  mono hle :=
    (extension.traces _).mono (extension.traces _)
      ((extension.generation_eq _).trans
        (extension.generation_eq _).symm)
      (wf.mono hle)
  projectionReady := extension.projectionReady
  structureEtaReady := extension.structureEtaReady

end AddInductive.EnvironmentInductiveExecution.CanonicalPrimitiveTransactionalVEnvsExtension

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.CanonicalPrimitiveTransactionalVEnvsExtension.ofReplay' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms AddInductive.EnvironmentInductiveExecution.CanonicalPrimitiveTransactionalVEnvsExtension.ofReplay

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.CanonicalPrimitiveTransactionalVEnvsExtension.canonicalConstants' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms AddInductive.EnvironmentInductiveExecution.CanonicalPrimitiveTransactionalVEnvsExtension.canonicalConstants

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.CanonicalPrimitiveTransactionalVEnvsExtension.canonicalInventory' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms AddInductive.EnvironmentInductiveExecution.CanonicalPrimitiveTransactionalVEnvsExtension.canonicalInventory

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.CanonicalPrimitiveTransactionalVEnvsExtension.toTransactionalVEnvsExtension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.abstract_eq,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms AddInductive.EnvironmentInductiveExecution.CanonicalPrimitiveTransactionalVEnvsExtension.toTransactionalVEnvsExtension

/-- Safety-indexed non-primitive transactions.  Compared with
`TransactionalVEnvsExtension`, neither primitive contract nor cross-safety
coherence is an explicit field: they follow from shared name-avoiding
transactions and the input `VEnvs.WF`. -/
structure AddInductive.EnvironmentInductiveExecution.NonprimitiveTransactionalVEnvsExtension
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv)
    (ves : VEnvs) where
  source : VInductDecl
  output : VEnvs
  transaction :
    execution.CoherentPrimitivePreservingTransactions source ves output
  projectionReady : ∀ safety,
    ProjectionReady finalEnv (output.venv safety)
  structureEtaReady : ∀ safety,
    StructureEtaReady finalEnv (output.venv safety)

namespace AddInductive.EnvironmentInductiveExecution.NonprimitiveTransactionalVEnvsExtension

/-- Derive the ordinary transaction package, including primitive reflection,
from the stronger name-avoiding traces. -/
def toTransactionalVEnvsExtension
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv}
    {ves : VEnvs} (wf : ves.WF env)
    (extension : execution.NonprimitiveTransactionalVEnvsExtension ves) :
    execution.TransactionalVEnvsExtension ves where
  source := extension.source
  output := extension.output
  transaction safety := (extension.transaction.transaction safety).toExact
  hasPrimitives safety :=
    (extension.transaction.transaction safety).hasPrimitives
      (wf.hasPrimitives (safety := safety))
  safePrimitives := by
    intro n ci found primitive
    have preTr : TrEnv' .safe env.constants env.quotInit
        (ves.venv .safe) := by
      simpa only [TrEnv] using wf.tr (safety := .safe)
    have finalTr :=
      (extension.transaction.transaction .safe).toExact.trEnv preTr
    have finalSafe : ConstMapSafePrimitives finalEnv.constants :=
      ((extension.transaction.transaction .safe).safePrimitivesMap preTr.map_wf
        (ConstMapSafePrimitives.ofEnvironment preTr.map_wf
          wf.safePrimitives))
    exact ConstMapSafePrimitives.toEnvironment finalSafe finalTr.map_wf
      found primitive
  mono hle := extension.transaction.mono wf.mono hle
  projectionReady := extension.projectionReady
  structureEtaReady := extension.structureEtaReady

end AddInductive.EnvironmentInductiveExecution.NonprimitiveTransactionalVEnvsExtension

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.NonprimitiveTransactionalVEnvsExtension.toTransactionalVEnvsExtension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms AddInductive.EnvironmentInductiveExecution.NonprimitiveTransactionalVEnvsExtension.toTransactionalVEnvsExtension

/-- A non-primitive inductive transaction followed by a shared list of
Theory-only structure-eta registrations.  The exact metadata transaction
ends at `transactionOutput`; readiness completion may then enlarge only the
Theory model, leaving the host environment fixed.  Sharing `etaRules` across
all safety levels is the coherence condition needed for the final `VEnvs`
ordering. -/
structure AddInductive.EnvironmentInductiveExecution.ReadinessCompletedNonprimitiveVEnvsExtension
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv)
    (ves : VEnvs) where
  source : VInductDecl
  transactionOutput : VEnvs
  output : VEnvs
  transaction :
    execution.CoherentPrimitivePreservingTransactions source ves
      transactionOutput
  etaRules : List VStructEta
  completion : ∀ safety,
    VEnv.AddStructEtas (transactionOutput.venv safety) etaRules
      (output.venv safety)
  /-- Projection artifacts are constructed once all generated constants and
  iota rules exist; subsequent eta registration transports them monotonically. -/
  projectionReadyBase : ∀ safety,
    ProjectionReady finalEnv (transactionOutput.venv safety)
  /-- Every host nonrecursive structure is either already registered at the
  transaction boundary or is backed by an exact artifact in `etaRules`. -/
  structureEtaCoverage : ∀ safety,
    StructureEtaRegistrationCoverage finalEnv
      (transactionOutput.venv safety) etaRules

namespace AddInductive.EnvironmentInductiveExecution.ReadinessCompletedNonprimitiveVEnvsExtension

/-- Assemble the complete semantic extension.  Exact replay supplies the
host-facing translation and primitive invariants; checked eta registration
then preserves those facts and provides the larger readiness-complete model. -/
def toVEnvsExtension
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv}
    {ves : VEnvs} (wf : ves.WF env)
    (extension :
      execution.ReadinessCompletedNonprimitiveVEnvsExtension ves) :
    execution.VEnvsExtension ves where
  output := extension.output
  tr safety := by
    have base := (extension.transaction.transaction safety).toExact.trEnv
      (wf.tr (safety := safety))
    exact (extension.completion safety).trEnv base
  hasPrimitives safety :=
    (extension.completion safety).hasPrimitives
      ((extension.transaction.transaction safety).hasPrimitives
        (wf.hasPrimitives (safety := safety)))
  safePrimitives := by
    intro n ci found primitive
    have preTr : TrEnv' .safe env.constants env.quotInit
        (ves.venv .safe) := by
      simpa only [TrEnv] using wf.tr (safety := .safe)
    have baseTr :=
      (extension.transaction.transaction .safe).toExact.trEnv preTr
    have finalSafe : ConstMapSafePrimitives finalEnv.constants :=
      (extension.transaction.transaction .safe).safePrimitivesMap
        preTr.map_wf
        (ConstMapSafePrimitives.ofEnvironment preTr.map_wf
          wf.safePrimitives)
    have finalTr := (extension.completion .safe).trEnv baseTr
    exact ConstMapSafePrimitives.toEnvironment finalSafe finalTr.map_wf
      found primitive
  mono hle :=
    (extension.completion _).mono (extension.completion _)
      (extension.transaction.mono wf.mono hle)
  projectionReady safety :=
    (extension.projectionReadyBase safety).mono
      (extension.completion safety).le
  structureEtaReady safety :=
    (extension.structureEtaCoverage safety).toStructureEtaReady
      (extension.completion safety)
  old_le safety :=
    (extension.transaction.transaction safety).toExact.le.trans
      (extension.completion safety).le

end AddInductive.EnvironmentInductiveExecution.ReadinessCompletedNonprimitiveVEnvsExtension

namespace AddInductive.EnvironmentInductiveExecution.NonprimitiveTransactionalVEnvsExtension

/-- Regard an already readiness-complete exact transaction as a completion
with no additional structure-eta registrations. -/
def toReadinessCompleted
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv}
    {ves : VEnvs} (extension :
      execution.NonprimitiveTransactionalVEnvsExtension ves) :
    execution.ReadinessCompletedNonprimitiveVEnvsExtension ves where
  source := extension.source
  transactionOutput := extension.output
  output := extension.output
  transaction := extension.transaction
  etaRules := []
  completion _ := .nil
  projectionReadyBase := extension.projectionReady
  structureEtaCoverage safety := by
    intro familyName familyInfo constructorName constructorInfo
      hfamily hconstructor hnonrec
    exact .inl <| (extension.structureEtaReady safety).resolve
      familyName familyInfo constructorName constructorInfo
        hfamily hconstructor hnonrec

end AddInductive.EnvironmentInductiveExecution.NonprimitiveTransactionalVEnvsExtension

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.ReadinessCompletedNonprimitiveVEnvsExtension.toVEnvsExtension' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms AddInductive.EnvironmentInductiveExecution.ReadinessCompletedNonprimitiveVEnvsExtension.toVEnvsExtension

/-- The admitted inductive branch of `addDecl.WF` factors into exactly two
independent obligations: operational completeness of the retained execution
and semantic preservation for each retained execution.  Primitive recognition
only selects the Boolean index shared by those obligations. -/
theorem addDecl.inductDecl_WF_of_execution
    {env : Environment} {ves : VEnvs} (_wf : ves.WF env)
    (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (isUnsafe : Bool) (fuel : FuelConfig := {})
    (complete : ∀ allowPrimitive,
      Environment.checkPrimitiveInductive env lparams nparams types
          isUnsafe = .ok allowPrimitive →
        AddInductive.EnvironmentInductiveExecution.Complete env lparams
          nparams types isUnsafe allowPrimitive fuel)
    (preserves : ∀ allowPrimitive finalEnv
        (execution : AddInductive.EnvironmentInductiveExecution env lparams
          nparams types isUnsafe allowPrimitive fuel finalEnv),
      Environment.checkPrimitiveInductive env lparams nparams types
          isUnsafe = .ok allowPrimitive →
        execution.PreservesVEnvs ves) :
    (addDecl env (.inductDecl lparams nparams types isUnsafe)
      (check := true) (fuel := fuel)).WF fun finalEnv =>
      ∃ ves' : VEnvs, ves'.WF finalEnv ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  intro finalEnv success
  change (do
    let allowPrimitive ← Environment.checkPrimitiveInductive env lparams
      nparams types isUnsafe
    Environment.addInductive env lparams nparams types isUnsafe
      allowPrimitive fuel) = .ok finalEnv at success
  cases primitiveResult : Environment.checkPrimitiveInductive env lparams
      nparams types isUnsafe with
  | error error =>
      rw [primitiveResult] at success
      contradiction
  | ok allowPrimitive =>
      rw [primitiveResult] at success
      obtain ⟨execution⟩ :=
        complete allowPrimitive primitiveResult finalEnv success
      exact preserves allowPrimitive finalEnv execution primitiveResult

/-- Fully decomposed inductive-branch contract.  Operational completeness is
reduced to the one normalization observer boundary for each flattened result;
semantic completion is supplied as pointwise `VEnvs` components for the exact
retained outer execution. -/
theorem addDecl.inductDecl_WF_of_components
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (isUnsafe : Bool) (fuel : FuelConfig := {})
    (candidateObservers : ∀ allowPrimitive,
      Environment.checkPrimitiveInductive env lparams nparams types
          isUnsafe = .ok allowPrimitive →
        ∀ nested : ElimNestedInductive.Result,
          AddInductive.NormalizationCandidateExecution.CandidateObserversComplete
            nparams nested.types nested.aux2nested.size isUnsafe
              (AddInductive.Context.forInductive env lparams isUnsafe
                allowPrimitive fuel))
    (semantics : ∀ allowPrimitive finalEnv
        (execution : AddInductive.EnvironmentInductiveExecution env lparams
          nparams types isUnsafe allowPrimitive fuel finalEnv),
      Environment.checkPrimitiveInductive env lparams nparams types
          isUnsafe = .ok allowPrimitive →
        execution.VEnvsExtension ves) :
    (addDecl env (.inductDecl lparams nparams types isUnsafe)
      (check := true) (fuel := fuel)).WF fun finalEnv =>
      ∃ ves' : VEnvs, ves'.WF finalEnv ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  apply addDecl.inductDecl_WF_of_execution wf lparams nparams types isUnsafe fuel
  · intro allowPrimitive primitiveRun
    exact AddInductive.EnvironmentInductiveExecution.complete_of_candidateObservers
      (candidateObservers allowPrimitive primitiveRun)
  · intro allowPrimitive finalEnv execution primitiveRun
    exact (semantics allowPrimitive finalEnv execution primitiveRun).toPreservesVEnvs

/--
info: 'Lean4Lean.addDecl.inductDecl_WF_of_components' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms addDecl.inductDecl_WF_of_components

/-- Transaction-oriented form of the decomposed inductive branch.  Exact
ordinary/nested traces discharge both pointwise environment translation and
the required extension inequalities automatically. -/
theorem addDecl.inductDecl_WF_of_transactions
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (isUnsafe : Bool) (fuel : FuelConfig := {})
    (candidateObservers : ∀ allowPrimitive,
      Environment.checkPrimitiveInductive env lparams nparams types
          isUnsafe = .ok allowPrimitive →
        ∀ nested : ElimNestedInductive.Result,
          AddInductive.NormalizationCandidateExecution.CandidateObserversComplete
            nparams nested.types nested.aux2nested.size isUnsafe
              (AddInductive.Context.forInductive env lparams isUnsafe
                allowPrimitive fuel))
    (semantics : ∀ allowPrimitive finalEnv
        (execution : AddInductive.EnvironmentInductiveExecution env lparams
          nparams types isUnsafe allowPrimitive fuel finalEnv),
      Environment.checkPrimitiveInductive env lparams nparams types
          isUnsafe = .ok allowPrimitive →
        execution.TransactionalVEnvsExtension ves) :
    (addDecl env (.inductDecl lparams nparams types isUnsafe)
      (check := true) (fuel := fuel)).WF fun finalEnv =>
      ∃ ves' : VEnvs, ves'.WF finalEnv ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  apply addDecl.inductDecl_WF_of_components wf lparams nparams types isUnsafe
    fuel candidateObservers
  intro allowPrimitive finalEnv execution primitiveRun
  exact (semantics allowPrimitive finalEnv execution primitiveRun).toVEnvsExtension
    wf

/--
info: 'Lean4Lean.addDecl.inductDecl_WF_of_transactions' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms addDecl.inductDecl_WF_of_transactions

/-- Non-primitive transaction form of the inductive branch.  Exact retained
traces now discharge translation, extension, and Theory primitive reflection;
their host-map insertions also discharge kernel primitive safety, and a shared
generation/restoration artifact discharges cross-safety coherence.  Only
projection/structure-eta readiness remains explicit. -/
theorem addDecl.inductDecl_WF_of_nonprimitive_transactions
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (isUnsafe : Bool) (fuel : FuelConfig := {})
    (candidateObservers : ∀ allowPrimitive,
      Environment.checkPrimitiveInductive env lparams nparams types
          isUnsafe = .ok allowPrimitive →
        ∀ nested : ElimNestedInductive.Result,
          AddInductive.NormalizationCandidateExecution.CandidateObserversComplete
            nparams nested.types nested.aux2nested.size isUnsafe
              (AddInductive.Context.forInductive env lparams isUnsafe
                allowPrimitive fuel))
    (semantics : ∀ allowPrimitive finalEnv
        (execution : AddInductive.EnvironmentInductiveExecution env lparams
          nparams types isUnsafe allowPrimitive fuel finalEnv),
      Environment.checkPrimitiveInductive env lparams nparams types
          isUnsafe = .ok allowPrimitive →
        execution.NonprimitiveTransactionalVEnvsExtension ves) :
    (addDecl env (.inductDecl lparams nparams types isUnsafe)
      (check := true) (fuel := fuel)).WF fun finalEnv =>
      ∃ ves' : VEnvs, ves'.WF finalEnv ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  apply addDecl.inductDecl_WF_of_transactions wf lparams nparams types
    isUnsafe fuel candidateObservers
  intro allowPrimitive finalEnv execution primitiveRun
  exact (semantics allowPrimitive finalEnv execution primitiveRun)
    |>.toTransactionalVEnvsExtension wf

/--
info: 'Lean4Lean.addDecl.inductDecl_WF_of_nonprimitive_transactions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms addDecl.inductDecl_WF_of_nonprimitive_transactions

/-- Readiness-completed non-primitive form of the inductive branch.  This is
the transaction interface used by generated structure artifacts: the exact
ordinary/nested replay may be followed by checked Theory-only eta
registrations before the final readiness package is assembled. -/
theorem addDecl.inductDecl_WF_of_readiness_completed_nonprimitive_transactions
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (isUnsafe : Bool) (fuel : FuelConfig := {})
    (candidateObservers : ∀ allowPrimitive,
      Environment.checkPrimitiveInductive env lparams nparams types
          isUnsafe = .ok allowPrimitive →
        ∀ nested : ElimNestedInductive.Result,
          AddInductive.NormalizationCandidateExecution.CandidateObserversComplete
            nparams nested.types nested.aux2nested.size isUnsafe
              (AddInductive.Context.forInductive env lparams isUnsafe
                allowPrimitive fuel))
    (semantics : ∀ allowPrimitive finalEnv
        (execution : AddInductive.EnvironmentInductiveExecution env lparams
          nparams types isUnsafe allowPrimitive fuel finalEnv),
      Environment.checkPrimitiveInductive env lparams nparams types
          isUnsafe = .ok allowPrimitive →
        execution.ReadinessCompletedNonprimitiveVEnvsExtension ves) :
    (addDecl env (.inductDecl lparams nparams types isUnsafe)
      (check := true) (fuel := fuel)).WF fun finalEnv =>
      ∃ ves' : VEnvs, ves'.WF finalEnv ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  apply addDecl.inductDecl_WF_of_components wf lparams nparams types
    isUnsafe fuel candidateObservers
  intro allowPrimitive finalEnv execution primitiveRun
  exact (semantics allowPrimitive finalEnv execution primitiveRun)
    |>.toVEnvsExtension wf

/-- Primitive-aware transaction form of the inductive branch.  Ordinary
blocks use the readiness-completed, name-avoiding transaction path.  A
recognizer result of `true` is isolated into its own callback together with
the proved canonical `Bool`/`Nat` syntax certificate, so primitive reflection
never has to be approximated by the nonprimitive name-avoidance contract. -/
theorem addDecl.inductDecl_WF_of_split_primitive_transactions
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (isUnsafe : Bool) (fuel : FuelConfig := {})
    (candidateObservers : ∀ allowPrimitive,
      Environment.checkPrimitiveInductive env lparams nparams types
          isUnsafe = .ok allowPrimitive →
        ∀ nested : ElimNestedInductive.Result,
          AddInductive.NormalizationCandidateExecution.CandidateObserversComplete
            nparams nested.types nested.aux2nested.size isUnsafe
              (AddInductive.Context.forInductive env lparams isUnsafe
                allowPrimitive fuel))
    (nonprimitiveSemantics : ∀ finalEnv
        (execution : AddInductive.EnvironmentInductiveExecution env lparams
          nparams types isUnsafe false fuel finalEnv),
      Environment.checkPrimitiveInductive env lparams nparams types
          isUnsafe = .ok false →
        execution.ReadinessCompletedNonprimitiveVEnvsExtension ves)
    (primitiveSemantics : ∀ finalEnv
        (execution : AddInductive.EnvironmentInductiveExecution env lparams
          nparams types isUnsafe true fuel finalEnv),
      Environment.checkPrimitiveInductive env lparams nparams types
          isUnsafe = .ok true →
      PrimitiveInductiveResult lparams nparams types isUnsafe true →
        execution.CanonicalPrimitiveTransactionalVEnvsExtension ves) :
    (addDecl env (.inductDecl lparams nparams types isUnsafe)
      (check := true) (fuel := fuel)).WF fun finalEnv =>
      ∃ ves' : VEnvs, ves'.WF finalEnv ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  apply addDecl.inductDecl_WF_of_components wf lparams nparams types
    isUnsafe fuel candidateObservers
  intro allowPrimitive finalEnv execution primitiveRun
  cases allowPrimitive with
  | false =>
      exact (nonprimitiveSemantics finalEnv execution primitiveRun)
        |>.toVEnvsExtension wf
  | true =>
      have primitiveResult :
          PrimitiveInductiveResult lparams nparams types isUnsafe true :=
        checkPrimitiveInductive.WF env lparams nparams types isUnsafe
          true primitiveRun
      exact (primitiveSemantics finalEnv execution primitiveRun
        primitiveResult).toTransactionalVEnvsExtension wf
        |>.toVEnvsExtension wf

/--
info: 'Lean4Lean.addDecl.inductDecl_WF_of_readiness_completed_nonprimitive_transactions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms addDecl.inductDecl_WF_of_readiness_completed_nonprimitive_transactions

/--
info: 'Lean4Lean.addDecl.inductDecl_WF_of_split_primitive_transactions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Level.instLawfulBEqLevel,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms addDecl.inductDecl_WF_of_split_primitive_transactions

set_option warn.sorry false in
/-- Successful checked addition preserves well-formedness and extends every safety-indexed
abstract environment. The only declaration form still outstanding is inductives, which need a
constructive `AddInduct` model. -/
theorem addDecl.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env) (decl : Declaration) :
    (addDecl env decl (check := true) (fuel := {})).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  cases decl with
  | axiomDecl v => exact (addAxiom.WF wf v).mono fun _ ⟨ves', hwf, _, h⟩ => ⟨ves', hwf, (h · |>.le)⟩
  | thmDecl v => exact (addTheorem.WF wf v).mono fun _ ⟨ves', hwf, _, h⟩ => ⟨ves', hwf, (h · |>.le)⟩
  | defnDecl v => exact (addDefinition.WF wf v).mono fun _ ⟨ves', hwf, h, _⟩ => ⟨ves', hwf, h⟩
  | opaqueDecl v =>
    exact (addOpaque.WF wf v).mono fun _ ⟨ves', hwf, _, h⟩ => ⟨ves', hwf, (h · |>.le)⟩
  | quotDecl => exact addQuot.WF wf
  | mutualDefnDecl vs => exact addMutual.WF wf vs
  | inductDecl _ _ _ _ => sorry
