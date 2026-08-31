/-
This file is derived from lean4lean and has been modified by Argument Computer Corporation.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/

import Lean4Lean.Verify.Environment.Quotient
import Lean4Lean.Verify.Environment.NormalizationElimination
import Lean4Lean.Verify.Environment.NormalizationReadiness
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

/-- Fully proved safe `Nat.add` declaration path. Ordinary body checking,
recognizer equations, and preservation of primitive reflection are all
discharged by concrete certificates; the generic `checkPrimitiveDef.WF`
boundary is not used. -/
theorem addDefinition.WF_safe_natAdd
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.add)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        (v.safety ≠ .unsafe → ∃ ci' : VDefVal, ∀ safety,
          (ves.venv safety).AddDef safety (.defnInfo v) ci'
            (ves'.venv safety)) := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatAddDefinition.WF wf v hname hsafety).run wf |>.bind
    fun _ hchecked => ?_
  obtain ⟨ci', htrSafe, hciSafe, hfresh, hlevels, hnat,
    hty, hz, hs⟩ := hchecked
  have hle : v.safety ≤ .safe := DefinitionSafety.le_safe
  have hmono := wf.mono hle
  have htr : TrDefVal v.safety (ves.venv v.safety) (.defnInfo v) ci' := by
    refine ⟨⟨⟨?_, htrSafe.1.1.2.1, htrSafe.1.1.2.2.mono hmono⟩,
      htrSafe.1.2⟩, htrSafe.2.mono hmono⟩
    rw [ConstantInfo.defnInfo_safety]
    exact DefinitionSafety.le_rfl
  have ⟨ves', hwf, hstep⟩ := addDef.WF wf v ci' v.safety
    (fun _ h => by simpa [ConstantInfo.defnInfo_safety] using h)
    htr (hciSafe.mono hmono) hfresh ?_ ?_
  · refine .pure ⟨ves', hwf, ?_, ?_⟩
    · intro safety
      exact (hstep safety).le
    · exact ⟨ci', hstep⟩
  · intro _
    exact ⟨by rw [ConstantInfo.defnInfo_safety, hsafety], hlevels⟩
  · intro safety base hvisible hadd
    have hsafetyLe : safety ≤ v.safety := by
      simpa [ConstantInfo.defnInfo_safety] using hvisible
    have hmodelMono : ves.venv .safe ≤ ves.venv safety :=
      hmono.trans (wf.mono hsafetyLe)
    have hci : ci'.WF (ves.venv safety) :=
      hciSafe.mono hmodelMono
    have hbaseWF : (base.addDefEq ci'.toDefEq).WF := by
      obtain ⟨decls, henvWF⟩ := (wf.tr (safety := safety)).wf
      have haddCi : (ves.venv safety).addConst ci'.name ci'.toVConstant =
          some base := by
        have haddCi := hadd
        have hvname : v.name = ci'.name := htrSafe.1.2
        rw [hvname] at haddCi
        exact haddCi
      exact ⟨.def ci' :: decls, .decl (.def hci haddCi) henvWF⟩
    have hname' : ci'.name = ``Nat.add :=
      htrSafe.1.2.symm.trans hname
    have huvars : ci'.uvars = 0 := by
      calc
        ci'.uvars = v.levelParams.length := htrSafe.1.1.2.1.symm
        _ = 0 := by simp [hlevels]
    have hadd' : (ves.venv safety).addConst ``Nat.add ci'.toVConstant =
        some base := by
      simpa [hname] using hadd
    have hty' := hty.mono hmodelMono
    have hz' := hz.mono hmodelMono
    have hs' := hs.mono hmodelMono
    rw [hlevels] at hty' hz' hs'
    have hnat' : (ves.venv safety).contains ``Nat := by
      obtain ⟨natCi, hnatLookup⟩ := hnat
      exact ⟨natCi, hmodelMono.constants hnatLookup⟩
    exact (wf.hasPrimitives (safety := safety)).addNatAddDef
      hnat' hname' hadd' hbaseWF huvars hty' hz' hs'

/-- Fully proved safe `Nat.pred` declaration path. The checked unary
reflection is retained in `HasPrimitives`, making it available to the later
`Nat.sub` certificate. -/
theorem addDefinition.WF_safe_natPred
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.pred)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        (v.safety ≠ .unsafe → ∃ ci' : VDefVal, ∀ safety,
          (ves.venv safety).AddDef safety (.defnInfo v) ci'
            (ves'.venv safety)) := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatPredDefinition.WF wf v hname hsafety).run wf |>.bind
    fun _ hchecked => ?_
  obtain ⟨ci', htrSafe, hciSafe, hfresh, hlevels, hnat,
    hty, hz, hs⟩ := hchecked
  have hle : v.safety ≤ .safe := DefinitionSafety.le_safe
  have hmono := wf.mono hle
  have htr : TrDefVal v.safety (ves.venv v.safety) (.defnInfo v) ci' := by
    refine ⟨⟨⟨?_, htrSafe.1.1.2.1, htrSafe.1.1.2.2.mono hmono⟩,
      htrSafe.1.2⟩, htrSafe.2.mono hmono⟩
    rw [ConstantInfo.defnInfo_safety]
    exact DefinitionSafety.le_rfl
  have ⟨ves', hwf, hstep⟩ := addDef.WF wf v ci' v.safety
    (fun _ h => by simpa [ConstantInfo.defnInfo_safety] using h)
    htr (hciSafe.mono hmono) hfresh ?_ ?_
  · refine .pure ⟨ves', hwf, ?_, ?_⟩
    · intro safety
      exact (hstep safety).le
    · exact ⟨ci', hstep⟩
  · intro _
    exact ⟨by rw [ConstantInfo.defnInfo_safety, hsafety], hlevels⟩
  · intro safety base hvisible hadd
    have hsafetyLe : safety ≤ v.safety := by
      simpa [ConstantInfo.defnInfo_safety] using hvisible
    have hmodelMono : ves.venv .safe ≤ ves.venv safety :=
      hmono.trans (wf.mono hsafetyLe)
    have hci : ci'.WF (ves.venv safety) :=
      hciSafe.mono hmodelMono
    have hbaseWF : (base.addDefEq ci'.toDefEq).WF := by
      obtain ⟨decls, henvWF⟩ := (wf.tr (safety := safety)).wf
      have haddCi : (ves.venv safety).addConst ci'.name ci'.toVConstant =
          some base := by
        have haddCi := hadd
        have hvname : v.name = ci'.name := htrSafe.1.2
        rw [hvname] at haddCi
        exact haddCi
      exact ⟨.def ci' :: decls, .decl (.def hci haddCi) henvWF⟩
    have hname' : ci'.name = ``Nat.pred :=
      htrSafe.1.2.symm.trans hname
    have huvars : ci'.uvars = 0 := by
      calc
        ci'.uvars = v.levelParams.length := htrSafe.1.1.2.1.symm
        _ = 0 := by simp [hlevels]
    have hadd' : (ves.venv safety).addConst ``Nat.pred ci'.toVConstant =
        some base := by
      simpa [hname] using hadd
    have hty' := hty.mono hmodelMono
    have hz' := hz.mono hmodelMono
    have hs' := hs.mono hmodelMono
    rw [hlevels] at hty' hz' hs'
    have hnat' : (ves.venv safety).contains ``Nat := by
      obtain ⟨natCi, hnatLookup⟩ := hnat
      exact ⟨natCi, hmodelMono.constants hnatLookup⟩
    exact (wf.hasPrimitives (safety := safety)).addNatPredDef
      hnat' hname' hadd' hbaseWF huvars hty' hz' hs'

/-- Fully proved safe `Nat.sub` declaration path. Its recurrence step uses
the retained `Nat.pred` reflection installed by the preceding direct path. -/
theorem addDefinition.WF_safe_natSub
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.sub)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        (v.safety ≠ .unsafe → ∃ ci' : VDefVal, ∀ safety,
          (ves.venv safety).AddDef safety (.defnInfo v) ci'
            (ves'.venv safety)) := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatSubDefinition.WF wf v hname hsafety).run wf |>.bind
    fun _ hchecked => ?_
  obtain ⟨ci', htrSafe, hciSafe, hfresh, hlevels, hpred,
    hty, hz, hs⟩ := hchecked
  have hle : v.safety ≤ .safe := DefinitionSafety.le_safe
  have hmono := wf.mono hle
  have htr : TrDefVal v.safety (ves.venv v.safety) (.defnInfo v) ci' := by
    refine ⟨⟨⟨?_, htrSafe.1.1.2.1, htrSafe.1.1.2.2.mono hmono⟩,
      htrSafe.1.2⟩, htrSafe.2.mono hmono⟩
    rw [ConstantInfo.defnInfo_safety]
    exact DefinitionSafety.le_rfl
  have ⟨ves', hwf, hstep⟩ := addDef.WF wf v ci' v.safety
    (fun _ h => by simpa [ConstantInfo.defnInfo_safety] using h)
    htr (hciSafe.mono hmono) hfresh ?_ ?_
  · refine .pure ⟨ves', hwf, ?_, ?_⟩
    · intro safety
      exact (hstep safety).le
    · exact ⟨ci', hstep⟩
  · intro _
    exact ⟨by rw [ConstantInfo.defnInfo_safety, hsafety], hlevels⟩
  · intro safety base hvisible hadd
    have hsafetyLe : safety ≤ v.safety := by
      simpa [ConstantInfo.defnInfo_safety] using hvisible
    have hmodelMono : ves.venv .safe ≤ ves.venv safety :=
      hmono.trans (wf.mono hsafetyLe)
    have hci : ci'.WF (ves.venv safety) :=
      hciSafe.mono hmodelMono
    have hbaseWF : (base.addDefEq ci'.toDefEq).WF := by
      obtain ⟨decls, henvWF⟩ := (wf.tr (safety := safety)).wf
      have haddCi : (ves.venv safety).addConst ci'.name ci'.toVConstant =
          some base := by
        have haddCi := hadd
        have hvname : v.name = ci'.name := htrSafe.1.2
        rw [hvname] at haddCi
        exact haddCi
      exact ⟨.def ci' :: decls, .decl (.def hci haddCi) henvWF⟩
    have hname' : ci'.name = ``Nat.sub :=
      htrSafe.1.2.symm.trans hname
    have huvars : ci'.uvars = 0 := by
      calc
        ci'.uvars = v.levelParams.length := htrSafe.1.1.2.1.symm
        _ = 0 := by simp [hlevels]
    have hadd' : (ves.venv safety).addConst ``Nat.sub ci'.toVConstant =
        some base := by
      simpa [hname] using hadd
    have hty' := hty.mono hmodelMono
    have hz' := hz.mono hmodelMono
    have hs' := hs.mono hmodelMono
    rw [hlevels] at hty' hz' hs'
    have hpred' : (ves.venv safety).contains ``Nat.pred := by
      obtain ⟨predCi, hpredLookup⟩ := hpred
      exact ⟨predCi, hmodelMono.constants hpredLookup⟩
    exact (wf.hasPrimitives (safety := safety)).addNatSubDef
      (wf.tr (safety := safety)).wf hpred' hname' hadd' hbaseWF huvars
      hty' hz' hs'

/-- Fully proved safe `Nat.mul` declaration path. Its recurrence step uses
the retained typed `Nat.add` reflection installed by the first direct slice. -/
theorem addDefinition.WF_safe_natMul
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.mul)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        (v.safety ≠ .unsafe → ∃ ci' : VDefVal, ∀ safety,
          (ves.venv safety).AddDef safety (.defnInfo v) ci'
            (ves'.venv safety)) := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatMulDefinition.WF wf v hname hsafety).run wf |>.bind
    fun _ hchecked => ?_
  obtain ⟨ci', htrSafe, hciSafe, hfresh, hlevels, haddC,
    hty, hz, hs⟩ := hchecked
  have hle : v.safety ≤ .safe := DefinitionSafety.le_safe
  have hmono := wf.mono hle
  have htr : TrDefVal v.safety (ves.venv v.safety) (.defnInfo v) ci' := by
    refine ⟨⟨⟨?_, htrSafe.1.1.2.1, htrSafe.1.1.2.2.mono hmono⟩,
      htrSafe.1.2⟩, htrSafe.2.mono hmono⟩
    rw [ConstantInfo.defnInfo_safety]
    exact DefinitionSafety.le_rfl
  have ⟨ves', hwf, hstep⟩ := addDef.WF wf v ci' v.safety
    (fun _ h => by simpa [ConstantInfo.defnInfo_safety] using h)
    htr (hciSafe.mono hmono) hfresh ?_ ?_
  · refine .pure ⟨ves', hwf, ?_, ?_⟩
    · intro safety
      exact (hstep safety).le
    · exact ⟨ci', hstep⟩
  · intro _
    exact ⟨by rw [ConstantInfo.defnInfo_safety, hsafety], hlevels⟩
  · intro safety base hvisible hadd
    have hsafetyLe : safety ≤ v.safety := by
      simpa [ConstantInfo.defnInfo_safety] using hvisible
    have hmodelMono : ves.venv .safe ≤ ves.venv safety :=
      hmono.trans (wf.mono hsafetyLe)
    have hci : ci'.WF (ves.venv safety) :=
      hciSafe.mono hmodelMono
    have hbaseWF : (base.addDefEq ci'.toDefEq).WF := by
      obtain ⟨decls, henvWF⟩ := (wf.tr (safety := safety)).wf
      have haddCi : (ves.venv safety).addConst ci'.name ci'.toVConstant =
          some base := by
        have haddCi := hadd
        have hvname : v.name = ci'.name := htrSafe.1.2
        rw [hvname] at haddCi
        exact haddCi
      exact ⟨.def ci' :: decls, .decl (.def hci haddCi) henvWF⟩
    have hname' : ci'.name = ``Nat.mul :=
      htrSafe.1.2.symm.trans hname
    have huvars : ci'.uvars = 0 := by
      calc
        ci'.uvars = v.levelParams.length := htrSafe.1.1.2.1.symm
        _ = 0 := by simp [hlevels]
    have hadd' : (ves.venv safety).addConst ``Nat.mul ci'.toVConstant =
        some base := by
      simpa [hname] using hadd
    have hty' := hty.mono hmodelMono
    have hz' := hz.mono hmodelMono
    have hs' := hs.mono hmodelMono
    rw [hlevels] at hty' hz' hs'
    have haddC' : (ves.venv safety).contains ``Nat.add := by
      obtain ⟨addCi, haddLookup⟩ := haddC
      exact ⟨addCi, hmodelMono.constants haddLookup⟩
    exact (wf.hasPrimitives (safety := safety)).addNatMulDef
      (wf.tr (safety := safety)).wf haddC' hname' hadd' hbaseWF huvars
      hty' hz' hs'

/-- Fully proved safe `Nat.pow` declaration path. Its recurrence step uses
the retained typed `Nat.mul` reflection installed by the preceding slice. -/
theorem addDefinition.WF_safe_natPow
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.pow)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        (v.safety ≠ .unsafe → ∃ ci' : VDefVal, ∀ safety,
          (ves.venv safety).AddDef safety (.defnInfo v) ci'
            (ves'.venv safety)) := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatPowDefinition.WF wf v hname hsafety).run wf |>.bind
    fun _ hchecked => ?_
  obtain ⟨ci', htrSafe, hciSafe, hfresh, hlevels, hmulC,
    hty, hz, hs⟩ := hchecked
  have hle : v.safety ≤ .safe := DefinitionSafety.le_safe
  have hmono := wf.mono hle
  have htr : TrDefVal v.safety (ves.venv v.safety) (.defnInfo v) ci' := by
    refine ⟨⟨⟨?_, htrSafe.1.1.2.1, htrSafe.1.1.2.2.mono hmono⟩,
      htrSafe.1.2⟩, htrSafe.2.mono hmono⟩
    rw [ConstantInfo.defnInfo_safety]
    exact DefinitionSafety.le_rfl
  have ⟨ves', hwf, hstep⟩ := addDef.WF wf v ci' v.safety
    (fun _ h => by simpa [ConstantInfo.defnInfo_safety] using h)
    htr (hciSafe.mono hmono) hfresh ?_ ?_
  · refine .pure ⟨ves', hwf, ?_, ?_⟩
    · intro safety
      exact (hstep safety).le
    · exact ⟨ci', hstep⟩
  · intro _
    exact ⟨by rw [ConstantInfo.defnInfo_safety, hsafety], hlevels⟩
  · intro safety base hvisible hadd
    have hsafetyLe : safety ≤ v.safety := by
      simpa [ConstantInfo.defnInfo_safety] using hvisible
    have hmodelMono : ves.venv .safe ≤ ves.venv safety :=
      hmono.trans (wf.mono hsafetyLe)
    have hci : ci'.WF (ves.venv safety) :=
      hciSafe.mono hmodelMono
    have hbaseWF : (base.addDefEq ci'.toDefEq).WF := by
      obtain ⟨decls, henvWF⟩ := (wf.tr (safety := safety)).wf
      have haddCi : (ves.venv safety).addConst ci'.name ci'.toVConstant =
          some base := by
        have haddCi := hadd
        have hvname : v.name = ci'.name := htrSafe.1.2
        rw [hvname] at haddCi
        exact haddCi
      exact ⟨.def ci' :: decls, .decl (.def hci haddCi) henvWF⟩
    have hname' : ci'.name = ``Nat.pow :=
      htrSafe.1.2.symm.trans hname
    have huvars : ci'.uvars = 0 := by
      calc
        ci'.uvars = v.levelParams.length := htrSafe.1.1.2.1.symm
        _ = 0 := by simp [hlevels]
    have hadd' : (ves.venv safety).addConst ``Nat.pow ci'.toVConstant =
        some base := by
      simpa [hname] using hadd
    have hty' := hty.mono hmodelMono
    have hz' := hz.mono hmodelMono
    have hs' := hs.mono hmodelMono
    rw [hlevels] at hty' hz' hs'
    have hmulC' : (ves.venv safety).contains ``Nat.mul := by
      obtain ⟨mulCi, hmulLookup⟩ := hmulC
      exact ⟨mulCi, hmodelMono.constants hmulLookup⟩
    exact (wf.hasPrimitives (safety := safety)).addNatPowDef
      (wf.tr (safety := safety)).wf hmulC' hname' hadd' hbaseWF huvars
      hty' hz' hs'

/-- Fully proved safe `Nat.shiftLeft` declaration path. Its recursive input
step uses the retained typed `Nat.mul` reflection. -/
theorem addDefinition.WF_safe_natShiftLeft
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.shiftLeft)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        (v.safety ≠ .unsafe → ∃ ci' : VDefVal, ∀ safety,
          (ves.venv safety).AddDef safety (.defnInfo v) ci'
            (ves'.venv safety)) := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatShiftLeftDefinition.WF wf v hname hsafety).run wf
    |>.bind fun _ hchecked => ?_
  obtain ⟨ci', htrSafe, hciSafe, hfresh, hlevels, hmulC,
    hty, hz, hs⟩ := hchecked
  have hle : v.safety ≤ .safe := DefinitionSafety.le_safe
  have hmono := wf.mono hle
  have htr : TrDefVal v.safety (ves.venv v.safety) (.defnInfo v) ci' := by
    refine ⟨⟨⟨?_, htrSafe.1.1.2.1, htrSafe.1.1.2.2.mono hmono⟩,
      htrSafe.1.2⟩, htrSafe.2.mono hmono⟩
    rw [ConstantInfo.defnInfo_safety]
    exact DefinitionSafety.le_rfl
  have ⟨ves', hwf, hstep⟩ := addDef.WF wf v ci' v.safety
    (fun _ h => by simpa [ConstantInfo.defnInfo_safety] using h)
    htr (hciSafe.mono hmono) hfresh ?_ ?_
  · refine .pure ⟨ves', hwf, ?_, ?_⟩
    · intro safety
      exact (hstep safety).le
    · exact ⟨ci', hstep⟩
  · intro _
    exact ⟨by rw [ConstantInfo.defnInfo_safety, hsafety], hlevels⟩
  · intro safety base hvisible hadd
    have hsafetyLe : safety ≤ v.safety := by
      simpa [ConstantInfo.defnInfo_safety] using hvisible
    have hmodelMono : ves.venv .safe ≤ ves.venv safety :=
      hmono.trans (wf.mono hsafetyLe)
    have hci : ci'.WF (ves.venv safety) :=
      hciSafe.mono hmodelMono
    have hbaseWF : (base.addDefEq ci'.toDefEq).WF := by
      obtain ⟨decls, henvWF⟩ := (wf.tr (safety := safety)).wf
      have haddCi : (ves.venv safety).addConst ci'.name ci'.toVConstant =
          some base := by
        have haddCi := hadd
        have hvname : v.name = ci'.name := htrSafe.1.2
        rw [hvname] at haddCi
        exact haddCi
      exact ⟨.def ci' :: decls, .decl (.def hci haddCi) henvWF⟩
    have hname' : ci'.name = ``Nat.shiftLeft :=
      htrSafe.1.2.symm.trans hname
    have huvars : ci'.uvars = 0 := by
      calc
        ci'.uvars = v.levelParams.length := htrSafe.1.1.2.1.symm
        _ = 0 := by simp [hlevels]
    have hadd' : (ves.venv safety).addConst
        ``Nat.shiftLeft ci'.toVConstant = some base := by
      simpa [hname] using hadd
    have hty' := hty.mono hmodelMono
    have hz' := hz.mono hmodelMono
    have hs' := hs.mono hmodelMono
    rw [hlevels] at hty' hz' hs'
    have hmulC' : (ves.venv safety).contains ``Nat.mul := by
      obtain ⟨mulCi, hmulLookup⟩ := hmulC
      exact ⟨mulCi, hmodelMono.constants hmulLookup⟩
    exact (wf.hasPrimitives (safety := safety)).addNatShiftLeftDef
      (wf.tr (safety := safety)).wf hmulC' hname' hadd' hbaseWF huvars
      hty' hz' hs'

/-- Fully proved safe `Nat.shiftRight` declaration path. Its recursive output
step uses the retained typed `Nat.div` reflection. -/
theorem addDefinition.WF_safe_natShiftRight
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.shiftRight)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        (v.safety ≠ .unsafe → ∃ ci' : VDefVal, ∀ safety,
          (ves.venv safety).AddDef safety (.defnInfo v) ci'
            (ves'.venv safety)) := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatShiftRightDefinition.WF wf v hname hsafety).run wf
    |>.bind fun _ hchecked => ?_
  obtain ⟨ci', htrSafe, hciSafe, hfresh, hlevels, hdivC,
    hty, hz, hs⟩ := hchecked
  have hle : v.safety ≤ .safe := DefinitionSafety.le_safe
  have hmono := wf.mono hle
  have htr : TrDefVal v.safety (ves.venv v.safety) (.defnInfo v) ci' := by
    refine ⟨⟨⟨?_, htrSafe.1.1.2.1, htrSafe.1.1.2.2.mono hmono⟩,
      htrSafe.1.2⟩, htrSafe.2.mono hmono⟩
    rw [ConstantInfo.defnInfo_safety]
    exact DefinitionSafety.le_rfl
  have ⟨ves', hwf, hstep⟩ := addDef.WF wf v ci' v.safety
    (fun _ h => by simpa [ConstantInfo.defnInfo_safety] using h)
    htr (hciSafe.mono hmono) hfresh ?_ ?_
  · refine .pure ⟨ves', hwf, ?_, ?_⟩
    · intro safety
      exact (hstep safety).le
    · exact ⟨ci', hstep⟩
  · intro _
    exact ⟨by rw [ConstantInfo.defnInfo_safety, hsafety], hlevels⟩
  · intro safety base hvisible hadd
    have hsafetyLe : safety ≤ v.safety := by
      simpa [ConstantInfo.defnInfo_safety] using hvisible
    have hmodelMono : ves.venv .safe ≤ ves.venv safety :=
      hmono.trans (wf.mono hsafetyLe)
    have hci : ci'.WF (ves.venv safety) :=
      hciSafe.mono hmodelMono
    have hbaseWF : (base.addDefEq ci'.toDefEq).WF := by
      obtain ⟨decls, henvWF⟩ := (wf.tr (safety := safety)).wf
      have haddCi : (ves.venv safety).addConst ci'.name ci'.toVConstant =
          some base := by
        have haddCi := hadd
        have hvname : v.name = ci'.name := htrSafe.1.2
        rw [hvname] at haddCi
        exact haddCi
      exact ⟨.def ci' :: decls, .decl (.def hci haddCi) henvWF⟩
    have hname' : ci'.name = ``Nat.shiftRight :=
      htrSafe.1.2.symm.trans hname
    have huvars : ci'.uvars = 0 := by
      calc
        ci'.uvars = v.levelParams.length := htrSafe.1.1.2.1.symm
        _ = 0 := by simp [hlevels]
    have hadd' : (ves.venv safety).addConst
        ``Nat.shiftRight ci'.toVConstant = some base := by
      simpa [hname] using hadd
    have hty' := hty.mono hmodelMono
    have hz' := hz.mono hmodelMono
    have hs' := hs.mono hmodelMono
    rw [hlevels] at hty' hz' hs'
    have hdivC' : (ves.venv safety).contains ``Nat.div := by
      obtain ⟨divCi, hdivLookup⟩ := hdivC
      exact ⟨divCi, hmodelMono.constants hdivLookup⟩
    exact (wf.hasPrimitives (safety := safety)).addNatShiftRightDef
      (wf.tr (safety := safety)).wf hdivC' hname' hadd' hbaseWF huvars
      hty' hz' hs'

/-- Fully proved safe `Char.ofNat` declaration path. The installed
`HasPrimitives` field records canonical typing rather than requiring the
source declaration type to be syntactically canonical. -/
theorem addDefinition.WF_safe_charOfNat
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Char.ofNat)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        (v.safety ≠ .unsafe → ∃ ci' : VDefVal, ∀ safety,
          (ves.venv safety).AddDef safety (.defnInfo v) ci'
            (ves'.venv safety)) := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeCharOfNatDefinition.WF wf v hname hsafety).run wf
    |>.bind fun _ hchecked => ?_
  obtain ⟨ci', htrSafe, hciSafe, hfresh, hlevels, _, hty⟩ := hchecked
  have hle : v.safety ≤ .safe := DefinitionSafety.le_safe
  have hmono := wf.mono hle
  have htr : TrDefVal v.safety (ves.venv v.safety) (.defnInfo v) ci' := by
    refine ⟨⟨⟨?_, htrSafe.1.1.2.1, htrSafe.1.1.2.2.mono hmono⟩,
      htrSafe.1.2⟩, htrSafe.2.mono hmono⟩
    rw [ConstantInfo.defnInfo_safety]
    exact DefinitionSafety.le_rfl
  have ⟨ves', hwf, hstep⟩ := addDef.WF wf v ci' v.safety
    (fun _ h => by simpa [ConstantInfo.defnInfo_safety] using h)
    htr (hciSafe.mono hmono) hfresh ?_ ?_
  · refine .pure ⟨ves', hwf, ?_, ?_⟩
    · intro safety
      exact (hstep safety).le
    · exact ⟨ci', hstep⟩
  · intro _
    exact ⟨by rw [ConstantInfo.defnInfo_safety, hsafety], hlevels⟩
  · intro safety base hvisible hadd
    have hsafetyLe : safety ≤ v.safety := by
      simpa [ConstantInfo.defnInfo_safety] using hvisible
    have hmodelMono : ves.venv .safe ≤ ves.venv safety :=
      hmono.trans (wf.mono hsafetyLe)
    have hci : ci'.WF (ves.venv safety) :=
      hciSafe.mono hmodelMono
    have hbaseWF : (base.addDefEq ci'.toDefEq).WF := by
      obtain ⟨decls, henvWF⟩ := (wf.tr (safety := safety)).wf
      have haddCi : (ves.venv safety).addConst ci'.name ci'.toVConstant =
          some base := by
        have haddCi := hadd
        have hvname : v.name = ci'.name := htrSafe.1.2
        rw [hvname] at haddCi
        exact haddCi
      exact ⟨.def ci' :: decls, .decl (.def hci haddCi) henvWF⟩
    have huvars : ci'.uvars = 0 := by
      calc
        ci'.uvars = v.levelParams.length := htrSafe.1.1.2.1.symm
        _ = 0 := by simp [hlevels]
    have hadd' : (ves.venv safety).addConst
        ``Char.ofNat ci'.toVConstant = some base := by
      simpa [hname] using hadd
    have hty' := hty.mono hmodelMono
    rw [hlevels] at hty'
    exact (wf.hasPrimitives (safety := safety)).addCharOfNat
      hadd' hbaseWF huvars hty'

/-- Fully proved safe `String.ofList` declaration path. The installed
primitive contract records canonical typing for the declaration and the two
specialized list constructors used by literal translation. -/
theorem addDefinition.WF_safe_stringOfList
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``String.ofList)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        (v.safety ≠ .unsafe → ∃ ci' : VDefVal, ∀ safety,
          (ves.venv safety).AddDef safety (.defnInfo v) ci'
            (ves'.venv safety)) := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeStringOfListDefinition.WF wf v hname hsafety).run wf
    |>.bind fun _ hchecked => ?_
  obtain ⟨ci', htrSafe, hciSafe, hfresh, hlevels,
    hty, hnil, hcons⟩ := hchecked
  have hle : v.safety ≤ .safe := DefinitionSafety.le_safe
  have hmono := wf.mono hle
  have htr : TrDefVal v.safety (ves.venv v.safety) (.defnInfo v) ci' := by
    refine ⟨⟨⟨?_, htrSafe.1.1.2.1, htrSafe.1.1.2.2.mono hmono⟩,
      htrSafe.1.2⟩, htrSafe.2.mono hmono⟩
    rw [ConstantInfo.defnInfo_safety]
    exact DefinitionSafety.le_rfl
  have ⟨ves', hwf, hstep⟩ := addDef.WF wf v ci' v.safety
    (fun _ h => by simpa [ConstantInfo.defnInfo_safety] using h)
    htr (hciSafe.mono hmono) hfresh ?_ ?_
  · refine .pure ⟨ves', hwf, ?_, ?_⟩
    · intro safety
      exact (hstep safety).le
    · exact ⟨ci', hstep⟩
  · intro _
    exact ⟨by rw [ConstantInfo.defnInfo_safety, hsafety], hlevels⟩
  · intro safety base hvisible hadd
    have hsafetyLe : safety ≤ v.safety := by
      simpa [ConstantInfo.defnInfo_safety] using hvisible
    have hmodelMono : ves.venv .safe ≤ ves.venv safety :=
      hmono.trans (wf.mono hsafetyLe)
    have hci : ci'.WF (ves.venv safety) :=
      hciSafe.mono hmodelMono
    have hbaseWF : (base.addDefEq ci'.toDefEq).WF := by
      obtain ⟨decls, henvWF⟩ := (wf.tr (safety := safety)).wf
      have haddCi : (ves.venv safety).addConst ci'.name ci'.toVConstant =
          some base := by
        have haddCi := hadd
        have hvname : v.name = ci'.name := htrSafe.1.2
        rw [hvname] at haddCi
        exact haddCi
      exact ⟨.def ci' :: decls, .decl (.def hci haddCi) henvWF⟩
    have huvars : ci'.uvars = 0 := by
      calc
        ci'.uvars = v.levelParams.length := htrSafe.1.1.2.1.symm
        _ = 0 := by simp [hlevels]
    have hadd' : (ves.venv safety).addConst
        ``String.ofList ci'.toVConstant = some base := by
      simpa [hname] using hadd
    have hty' := hty.mono hmodelMono
    have hnil' := hnil.mono hmodelMono
    have hcons' := hcons.mono hmodelMono
    rw [hlevels] at hty' hnil' hcons'
    exact (wf.hasPrimitives (safety := safety)).addStringOfList
      hadd' hbaseWF huvars hty' hnil' hcons'

/-- Fully proved safe `Nat.beq` declaration path. The four checked constructor
equations install typed Boolean-valued literal reflection. -/
theorem addDefinition.WF_safe_natBEq
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.beq)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        (v.safety ≠ .unsafe → ∃ ci' : VDefVal, ∀ safety,
          (ves.venv safety).AddDef safety (.defnInfo v) ci'
            (ves'.venv safety)) := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatBEqDefinition.WF wf v hname hsafety).run wf |>.bind
    fun _ hchecked => ?_
  obtain ⟨ci', htrSafe, hciSafe, hfresh, hlevels, hnat, hbool,
    hty, h00, h0s, hs0, hss⟩ := hchecked
  have hle : v.safety ≤ .safe := DefinitionSafety.le_safe
  have hmono := wf.mono hle
  have htr : TrDefVal v.safety (ves.venv v.safety) (.defnInfo v) ci' := by
    refine ⟨⟨⟨?_, htrSafe.1.1.2.1, htrSafe.1.1.2.2.mono hmono⟩,
      htrSafe.1.2⟩, htrSafe.2.mono hmono⟩
    rw [ConstantInfo.defnInfo_safety]
    exact DefinitionSafety.le_rfl
  have ⟨ves', hwf, hstep⟩ := addDef.WF wf v ci' v.safety
    (fun _ h => by simpa [ConstantInfo.defnInfo_safety] using h)
    htr (hciSafe.mono hmono) hfresh ?_ ?_
  · refine .pure ⟨ves', hwf, ?_, ?_⟩
    · intro safety
      exact (hstep safety).le
    · exact ⟨ci', hstep⟩
  · intro _
    exact ⟨by rw [ConstantInfo.defnInfo_safety, hsafety], hlevels⟩
  · intro safety base hvisible hadd
    have hsafetyLe : safety ≤ v.safety := by
      simpa [ConstantInfo.defnInfo_safety] using hvisible
    have hmodelMono : ves.venv .safe ≤ ves.venv safety :=
      hmono.trans (wf.mono hsafetyLe)
    have hci : ci'.WF (ves.venv safety) :=
      hciSafe.mono hmodelMono
    have hbaseWF : (base.addDefEq ci'.toDefEq).WF := by
      obtain ⟨decls, henvWF⟩ := (wf.tr (safety := safety)).wf
      have haddCi : (ves.venv safety).addConst ci'.name ci'.toVConstant =
          some base := by
        have haddCi := hadd
        have hvname : v.name = ci'.name := htrSafe.1.2
        rw [hvname] at haddCi
        exact haddCi
      exact ⟨.def ci' :: decls, .decl (.def hci haddCi) henvWF⟩
    have hname' : ci'.name = ``Nat.beq :=
      htrSafe.1.2.symm.trans hname
    have huvars : ci'.uvars = 0 := by
      calc
        ci'.uvars = v.levelParams.length := htrSafe.1.1.2.1.symm
        _ = 0 := by simp [hlevels]
    have hadd' : (ves.venv safety).addConst ``Nat.beq ci'.toVConstant =
        some base := by
      simpa [hname] using hadd
    have hty' := hty.mono hmodelMono
    have h00' := h00.mono hmodelMono
    have h0s' := h0s.mono hmodelMono
    have hs0' := hs0.mono hmodelMono
    have hss' := hss.mono hmodelMono
    rw [hlevels] at hty' h00' h0s' hs0' hss'
    have hnat' : (ves.venv safety).contains ``Nat := by
      obtain ⟨natCi, hnatLookup⟩ := hnat
      exact ⟨natCi, hmodelMono.constants hnatLookup⟩
    have hbool' : (ves.venv safety).contains ``Bool := by
      obtain ⟨boolCi, hboolLookup⟩ := hbool
      exact ⟨boolCi, hmodelMono.constants hboolLookup⟩
    exact (wf.hasPrimitives (safety := safety)).addNatBEqDef
      hnat' hbool' hname' hadd' hbaseWF huvars hty' h00' h0s' hs0' hss'

/-- Fully proved safe `Nat.ble` declaration path. The four checked constructor
equations install typed Boolean-valued literal reflection. -/
theorem addDefinition.WF_safe_natBLE
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.ble)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        (v.safety ≠ .unsafe → ∃ ci' : VDefVal, ∀ safety,
          (ves.venv safety).AddDef safety (.defnInfo v) ci'
            (ves'.venv safety)) := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatBLEDefinition.WF wf v hname hsafety).run wf |>.bind
    fun _ hchecked => ?_
  obtain ⟨ci', htrSafe, hciSafe, hfresh, hlevels, hnat, hbool,
    hty, h00, h0s, hs0, hss⟩ := hchecked
  have hle : v.safety ≤ .safe := DefinitionSafety.le_safe
  have hmono := wf.mono hle
  have htr : TrDefVal v.safety (ves.venv v.safety) (.defnInfo v) ci' := by
    refine ⟨⟨⟨?_, htrSafe.1.1.2.1, htrSafe.1.1.2.2.mono hmono⟩,
      htrSafe.1.2⟩, htrSafe.2.mono hmono⟩
    rw [ConstantInfo.defnInfo_safety]
    exact DefinitionSafety.le_rfl
  have ⟨ves', hwf, hstep⟩ := addDef.WF wf v ci' v.safety
    (fun _ h => by simpa [ConstantInfo.defnInfo_safety] using h)
    htr (hciSafe.mono hmono) hfresh ?_ ?_
  · refine .pure ⟨ves', hwf, ?_, ?_⟩
    · intro safety
      exact (hstep safety).le
    · exact ⟨ci', hstep⟩
  · intro _
    exact ⟨by rw [ConstantInfo.defnInfo_safety, hsafety], hlevels⟩
  · intro safety base hvisible hadd
    have hsafetyLe : safety ≤ v.safety := by
      simpa [ConstantInfo.defnInfo_safety] using hvisible
    have hmodelMono : ves.venv .safe ≤ ves.venv safety :=
      hmono.trans (wf.mono hsafetyLe)
    have hci : ci'.WF (ves.venv safety) :=
      hciSafe.mono hmodelMono
    have hbaseWF : (base.addDefEq ci'.toDefEq).WF := by
      obtain ⟨decls, henvWF⟩ := (wf.tr (safety := safety)).wf
      have haddCi : (ves.venv safety).addConst ci'.name ci'.toVConstant =
          some base := by
        have haddCi := hadd
        have hvname : v.name = ci'.name := htrSafe.1.2
        rw [hvname] at haddCi
        exact haddCi
      exact ⟨.def ci' :: decls, .decl (.def hci haddCi) henvWF⟩
    have hname' : ci'.name = ``Nat.ble :=
      htrSafe.1.2.symm.trans hname
    have huvars : ci'.uvars = 0 := by
      calc
        ci'.uvars = v.levelParams.length := htrSafe.1.1.2.1.symm
        _ = 0 := by simp [hlevels]
    have hadd' : (ves.venv safety).addConst ``Nat.ble ci'.toVConstant =
        some base := by
      simpa [hname] using hadd
    have hty' := hty.mono hmodelMono
    have h00' := h00.mono hmodelMono
    have h0s' := h0s.mono hmodelMono
    have hs0' := hs0.mono hmodelMono
    have hss' := hss.mono hmodelMono
    rw [hlevels] at hty' h00' h0s' hs0' hss'
    have hnat' : (ves.venv safety).contains ``Nat := by
      obtain ⟨natCi, hnatLookup⟩ := hnat
      exact ⟨natCi, hmodelMono.constants hnatLookup⟩
    have hbool' : (ves.venv safety).contains ``Bool := by
      obtain ⟨boolCi, hboolLookup⟩ := hbool
      exact ⟨boolCi, hmodelMono.constants hboolLookup⟩
    exact (wf.hasPrimitives (safety := safety)).addNatBLEDef
      hnat' hbool' hname' hadd' hbaseWF huvars hty' h00' h0s' hs0' hss'

/-- Fully proved safe `Nat.gcd` declaration path. Its semantic certificate
is independent of the compiler-selected representation of recursive state. -/
theorem addDefinition.WF_safe_natGcd
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.gcd)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        (v.safety ≠ .unsafe → ∃ ci' : VDefVal, ∀ safety,
          (ves.venv safety).AddDef safety (.defnInfo v) ci'
            (ves'.venv safety)) := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatGcdDefinition.WF wf v hname hsafety).run wf |>.bind
    fun _ hchecked => ?_
  obtain ⟨ci', htrSafe, hciSafe, hfresh, hevidence⟩ := hchecked
  rcases hevidence with
    ⟨cert, hlevels, hnat, hbeqC, hmodC, hty, hvalid, hshape⟩
  have hle : v.safety ≤ .safe := DefinitionSafety.le_safe
  have hmono := wf.mono hle
  have htr : TrDefVal v.safety (ves.venv v.safety)
      (.defnInfo v) ci' := by
    refine ⟨⟨⟨?_, htrSafe.1.1.2.1,
      htrSafe.1.1.2.2.mono hmono⟩, htrSafe.1.2⟩,
      htrSafe.2.mono hmono⟩
    rw [ConstantInfo.defnInfo_safety]
    exact DefinitionSafety.le_rfl
  have ⟨ves', hwf, hstep⟩ := addDef.WF wf v ci' v.safety
    (fun _ h => by simpa [ConstantInfo.defnInfo_safety] using h)
    htr (hciSafe.mono hmono) hfresh ?_ ?_
  · refine .pure ⟨ves', hwf, ?_, ?_⟩
    · intro safety
      exact (hstep safety).le
    · exact ⟨ci', hstep⟩
  · intro _
    exact ⟨by rw [ConstantInfo.defnInfo_safety, hsafety], hlevels⟩
  · intro safety base hvisible hadd
    have hsafetyLe : safety ≤ v.safety := by
      simpa [ConstantInfo.defnInfo_safety] using hvisible
    have hmodelMono : ves.venv .safe ≤ ves.venv safety :=
      hmono.trans (wf.mono hsafetyLe)
    have hci : ci'.WF (ves.venv safety) :=
      hciSafe.mono hmodelMono
    have hbaseWF : (base.addDefEq ci'.toDefEq).WF := by
      obtain ⟨decls, henvWF⟩ := (wf.tr (safety := safety)).wf
      have haddCi :
          (ves.venv safety).addConst ci'.name ci'.toVConstant =
            some base := by
        have haddCi := hadd
        have hvname : v.name = ci'.name := htrSafe.1.2
        rw [hvname] at haddCi
        exact haddCi
      exact ⟨.def ci' :: decls, .decl (.def hci haddCi) henvWF⟩
    have hname' : ci'.name = ``Nat.gcd :=
      htrSafe.1.2.symm.trans hname
    have hadd' :
        (ves.venv safety).addConst ``Nat.gcd ci'.toVConstant =
          some base := by
      simpa [hname] using hadd
    exact Environment.NatGcdPrimitiveEvidence.conservesHasPrimitives
      (c := .mk' wf .safe v.levelParams)
      rfl rfl htrSafe.2 hname' htrSafe.1.1.2.1
      (wf.hasPrimitives (safety := safety)) hmodelMono hadd' hbaseWF
      ⟨cert, hlevels, hnat, hbeqC, hmodC, hty, hvalid, hshape⟩

/-- Fully proved safe `Nat.bitwise` declaration path. Its generic-state
certificate validates the public equations, recursive transition, Boolean
selector, and Nat-equality condition before installing Kripke reflection. -/
theorem addDefinition.WF_safe_natBitwise
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.bitwise)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        (v.safety ≠ .unsafe → ∃ ci' : VDefVal, ∀ safety,
          (ves.venv safety).AddDef safety (.defnInfo v) ci'
            (ves'.venv safety)) := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatBitwiseDefinition.WF wf v hname hsafety).run wf |>.bind
    fun _ hchecked => ?_
  obtain ⟨ci', htrSafe, hciSafe, hfresh, hevidence⟩ := hchecked
  rcases hevidence with
    ⟨cert, ite, decide, hlevels, hbool, hnat, hbeqC,
      haddC, hmodC, hdivC, hty, hcert,
      hiteS, hboolCert, hdecideS, hnatCert⟩
  have hle : v.safety ≤ .safe := DefinitionSafety.le_safe
  have hmono := wf.mono hle
  have htr : TrDefVal v.safety (ves.venv v.safety)
      (.defnInfo v) ci' := by
    refine ⟨⟨⟨?_, htrSafe.1.1.2.1,
      htrSafe.1.1.2.2.mono hmono⟩, htrSafe.1.2⟩,
      htrSafe.2.mono hmono⟩
    rw [ConstantInfo.defnInfo_safety]
    exact DefinitionSafety.le_rfl
  have ⟨ves', hwf, hstep⟩ := addDef.WF wf v ci' v.safety
    (fun _ h => by simpa [ConstantInfo.defnInfo_safety] using h)
    htr (hciSafe.mono hmono) hfresh ?_ ?_
  · refine .pure ⟨ves', hwf, ?_, ?_⟩
    · intro safety
      exact (hstep safety).le
    · exact ⟨ci', hstep⟩
  · intro _
    exact ⟨by rw [ConstantInfo.defnInfo_safety, hsafety], hlevels⟩
  · intro safety base hvisible hadd
    have hsafetyLe : safety ≤ v.safety := by
      simpa [ConstantInfo.defnInfo_safety] using hvisible
    have hmodelMono : ves.venv .safe ≤ ves.venv safety :=
      hmono.trans (wf.mono hsafetyLe)
    have hci : ci'.WF (ves.venv safety) :=
      hciSafe.mono hmodelMono
    have hbaseWF : (base.addDefEq ci'.toDefEq).WF := by
      obtain ⟨decls, henvWF⟩ := (wf.tr (safety := safety)).wf
      have haddCi :
          (ves.venv safety).addConst ci'.name ci'.toVConstant =
            some base := by
        have haddCi := hadd
        have hvname : v.name = ci'.name := htrSafe.1.2
        rw [hvname] at haddCi
        exact haddCi
      exact ⟨.def ci' :: decls, .decl (.def hci haddCi) henvWF⟩
    have hname' : ci'.name = ``Nat.bitwise :=
      htrSafe.1.2.symm.trans hname
    have hadd' :
        (ves.venv safety).addConst ``Nat.bitwise ci'.toVConstant =
          some base := by
      simpa [hname] using hadd
    exact Environment.NatBitwisePrimitiveEvidence.conservesHasPrimitives
      (c := .mk' wf .safe v.levelParams)
      rfl rfl htrSafe.2 hname' htrSafe.1.1.2.1
      (wf.hasPrimitives (safety := safety)) hmodelMono hadd' hbaseWF
      ⟨cert, ite, decide, hlevels, hbool, hnat, hbeqC,
        haddC, hmodC, hdivC, hty, hcert,
        hiteS, hboolCert, hdecideS, hnatCert⟩

/-- Shared readiness-aware transaction for a finite safe primitive whose
checker returns a compact, primitive-specific evidence tail. -/
theorem addDefinition.WF_safe_primitive
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) {n : Name} (hname : v.name = n)
    (hsafety : v.safety = .safe)
    {Q : VDefVal → Prop}
    (hcheck : ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ =>
        ∃ v' : VDefVal,
          TrDefVal .safe (ves.venv .safe) (.defnInfo v) v' ∧
          v'.WF (ves.venv .safe) ∧ env.find? v.name = none ∧
          v.levelParams = [] ∧ Q v')
    (hconserve : ∀ {v' : VDefVal} (safety : DefinitionSafety) {base : VEnv},
      Q v' →
      ves.venv .safe ≤ ves.venv safety →
      TrDefVal .safe (ves.venv .safe) (.defnInfo v) v' →
      v.levelParams = [] →
      v'.name = n →
      v.levelParams.length = v'.uvars →
      v'.uvars = 0 →
      (ves.venv safety).addConst n v'.toVConstant = some base →
      (base.addDefEq v'.toDefEq).WF →
      (base.addDefEq v'.toDefEq).HasPrimitives) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        (v.safety ≠ .unsafe → ∃ ci' : VDefVal, ∀ safety,
          (ves.venv safety).AddDef safety (.defnInfo v) ci'
            (ves'.venv safety)) := by
  unfold addDefinition
  simp [hsafety]
  refine hcheck.run wf |>.bind fun _ hchecked => ?_
  obtain ⟨ci', htrSafe, hciSafe, hfresh, hlevels, hQ⟩ := hchecked
  have hle : v.safety ≤ .safe := DefinitionSafety.le_safe
  have hmono := wf.mono hle
  have htr : TrDefVal v.safety (ves.venv v.safety)
      (.defnInfo v) ci' := by
    refine ⟨⟨⟨?_, htrSafe.1.1.2.1,
      htrSafe.1.1.2.2.mono hmono⟩, htrSafe.1.2⟩,
      htrSafe.2.mono hmono⟩
    rw [ConstantInfo.defnInfo_safety]
    exact DefinitionSafety.le_rfl
  have ⟨ves', hwf, hstep⟩ := addDef.WF wf v ci' v.safety
    (fun _ h => by simpa [ConstantInfo.defnInfo_safety] using h)
    htr (hciSafe.mono hmono) hfresh ?_ ?_
  · refine .pure ⟨ves', hwf, ?_, ?_⟩
    · intro safety
      exact (hstep safety).le
    · exact ⟨ci', hstep⟩
  · intro _
    exact ⟨by rw [ConstantInfo.defnInfo_safety, hsafety], hlevels⟩
  · intro safety base hvisible hadd
    have hsafetyLe : safety ≤ v.safety := by
      simpa [ConstantInfo.defnInfo_safety] using hvisible
    have hmodelMono : ves.venv .safe ≤ ves.venv safety :=
      hmono.trans (wf.mono hsafetyLe)
    have hci : ci'.WF (ves.venv safety) :=
      hciSafe.mono hmodelMono
    have hbaseWF : (base.addDefEq ci'.toDefEq).WF := by
      obtain ⟨decls, henvWF⟩ := (wf.tr (safety := safety)).wf
      have haddCi :
          (ves.venv safety).addConst ci'.name ci'.toVConstant =
            some base := by
        have haddCi := hadd
        have hvname : v.name = ci'.name := htrSafe.1.2
        rw [hvname] at haddCi
        exact haddCi
      exact ⟨.def ci' :: decls, .decl (.def hci haddCi) henvWF⟩
    have hname' : ci'.name = n := htrSafe.1.2.symm.trans hname
    have huvars : ci'.uvars = 0 := by
      calc
        ci'.uvars = v.levelParams.length := htrSafe.1.1.2.1.symm
        _ = 0 := by simp [hlevels]
    have hadd' : (ves.venv safety).addConst n ci'.toVConstant =
        some base := by
      simpa [hname] using hadd
    exact hconserve safety hQ hmodelMono htrSafe hlevels hname'
      htrSafe.1.1.2.1 huvars hadd' hbaseWF

/-- Fully proved safe `Nat.land` specialization path. -/
theorem addDefinition.WF_safe_natLand
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.land)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        (v.safety ≠ .unsafe → ∃ ci' : VDefVal, ∀ safety,
          (ves.venv safety).AddDef safety (.defnInfo v) ci'
            (ves'.venv safety)) := by
  refine addDefinition.WF_safe_primitive wf v hname hsafety
    (checkSafeNatLandDefinition.WF wf v hname hsafety) ?_
  intro v' safety base hQ hmono _ hlevels hname' _ huvars' hadd' hwf'
  obtain ⟨hnat, hbool, hbitwise, hty, op', hvalue, hopTy, hf, ht⟩ := hQ
  have hty' := hty.mono hmono
  have hopTy' := hopTy.mono hmono
  have hf' := hf.mono hmono
  have ht' := ht.mono hmono
  rw [hlevels] at hty' hopTy' hf' ht'
  exact (wf.hasPrimitives (safety := safety)).addNatLandDef
    (wf.tr (safety := safety)).wf (hmono.contains hnat)
    (hmono.contains hbool) (hmono.contains hbitwise)
    hname' hadd' hwf' huvars' hty' hvalue hopTy' hf' ht'

/-- Fully proved safe `Nat.lor` specialization path. -/
theorem addDefinition.WF_safe_natLor
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.lor)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        (v.safety ≠ .unsafe → ∃ ci' : VDefVal, ∀ safety,
          (ves.venv safety).AddDef safety (.defnInfo v) ci'
            (ves'.venv safety)) := by
  refine addDefinition.WF_safe_primitive wf v hname hsafety
    (checkSafeNatLorDefinition.WF wf v hname hsafety) ?_
  intro v' safety base hQ hmono _ hlevels hname' _ huvars' hadd' hwf'
  obtain ⟨hnat, hbool, hbitwise, hty, op', hvalue, hopTy, hf, ht⟩ := hQ
  have hty' := hty.mono hmono
  have hopTy' := hopTy.mono hmono
  have hf' := hf.mono hmono
  have ht' := ht.mono hmono
  rw [hlevels] at hty' hopTy' hf' ht'
  exact (wf.hasPrimitives (safety := safety)).addNatLorDef
    (wf.tr (safety := safety)).wf (hmono.contains hnat)
    (hmono.contains hbool) (hmono.contains hbitwise)
    hname' hadd' hwf' huvars' hty' hvalue hopTy' hf' ht'

/-- Fully proved safe `Nat.xor` specialization path. -/
theorem addDefinition.WF_safe_natXor
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.xor)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        (v.safety ≠ .unsafe → ∃ ci' : VDefVal, ∀ safety,
          (ves.venv safety).AddDef safety (.defnInfo v) ci'
            (ves'.venv safety)) := by
  refine addDefinition.WF_safe_primitive wf v hname hsafety
    (checkSafeNatXorDefinition.WF wf v hname hsafety) ?_
  intro v' safety base hQ hmono _ hlevels hname' _ huvars' hadd' hwf'
  obtain ⟨hnat, _, hbitwise, hty, op', hvalue,
    hopTy, hff, htf, hft, htt⟩ := hQ
  have hty' := hty.mono hmono
  have hopTy' := hopTy.mono hmono
  have hff' := hff.mono hmono
  have htf' := htf.mono hmono
  have hft' := hft.mono hmono
  have htt' := htt.mono hmono
  rw [hlevels] at hty' hopTy' hff' htf' hft' htt'
  exact (wf.hasPrimitives (safety := safety)).addNatXorDef
    (hmono.contains hnat) (hmono.contains hbitwise)
    hname' hadd' hwf' huvars' hty' hvalue hopTy'
    hff' htf' hft' htt'

/-- Fully proved safe `Nat.mod` declaration path. The checker retains the
selector and fuel-recursion evidence, and the semantic certificate installs
literal remainder reflection in every safety model receiving the definition. -/
theorem addDefinition.WF_safe_natMod
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.mod)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        (v.safety ≠ .unsafe → ∃ ci' : VDefVal, ∀ safety,
          (ves.venv safety).AddDef safety (.defnInfo v) ci'
            (ves'.venv safety)) := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatModDefinition.WF wf v hname hsafety).run wf |>.bind
    fun _ hchecked => ?_
  obtain ⟨ci', htrSafe, hciSafe, hfresh, hevidence⟩ := hchecked
  rcases hevidence with
    ⟨zeroL', zeroR', go', goTy', topL', topR', goL', goR',
      hzeroL, hzeroR, hgoS, hgoTyS, htopL, htopR, hgoL, hgoR,
      hlevels, hnat, hbool, hble, hsub, hty, hzeroEq,
      selector, hgoHas, htopEq, hgoEq⟩
  have hle : v.safety ≤ .safe := DefinitionSafety.le_safe
  have hmono := wf.mono hle
  have htr : TrDefVal v.safety (ves.venv v.safety) (.defnInfo v) ci' := by
    refine ⟨⟨⟨?_, htrSafe.1.1.2.1, htrSafe.1.1.2.2.mono hmono⟩,
      htrSafe.1.2⟩, htrSafe.2.mono hmono⟩
    rw [ConstantInfo.defnInfo_safety]
    exact DefinitionSafety.le_rfl
  have ⟨ves', hwf, hstep⟩ := addDef.WF wf v ci' v.safety
    (fun _ h => by simpa [ConstantInfo.defnInfo_safety] using h)
    htr (hciSafe.mono hmono) hfresh ?_ ?_
  · refine .pure ⟨ves', hwf, ?_, ?_⟩
    · intro safety
      exact (hstep safety).le
    · exact ⟨ci', hstep⟩
  · intro _
    exact ⟨by rw [ConstantInfo.defnInfo_safety, hsafety], hlevels⟩
  · intro safety base hvisible hadd
    have hsafetyLe : safety ≤ v.safety := by
      simpa [ConstantInfo.defnInfo_safety] using hvisible
    have hmodelMono : ves.venv .safe ≤ ves.venv safety :=
      hmono.trans (wf.mono hsafetyLe)
    have hci : ci'.WF (ves.venv safety) :=
      hciSafe.mono hmodelMono
    have hbaseWF : (base.addDefEq ci'.toDefEq).WF := by
      obtain ⟨decls, henvWF⟩ := (wf.tr (safety := safety)).wf
      have haddCi : (ves.venv safety).addConst ci'.name ci'.toVConstant =
          some base := by
        have haddCi := hadd
        have hvname : v.name = ci'.name := htrSafe.1.2
        rw [hvname] at haddCi
        exact haddCi
      exact ⟨.def ci' :: decls, .decl (.def hci haddCi) henvWF⟩
    have hname' : ci'.name = ``Nat.mod :=
      htrSafe.1.2.symm.trans hname
    have hadd' : (ves.venv safety).addConst ``Nat.mod ci'.toVConstant =
        some base := by
      simpa [hname] using hadd
    exact Environment.NatModPrimitiveEvidence.conservesHasPrimitives
      (c := .mk' wf .safe v.levelParams)
      rfl rfl htrSafe.2 hname' htrSafe.1.1.2.1
      (wf.hasPrimitives (safety := safety)) hmodelMono hadd' hbaseWF
      ⟨zeroL', zeroR', go', goTy', topL', topR', goL', goR',
        hzeroL, hzeroR, hgoS, hgoTyS, htopL, htopR, hgoL, hgoR,
        hlevels, hnat, hbool, hble, hsub, hty, hzeroEq,
        selector, hgoHas, htopEq, hgoEq⟩

/-- Fully proved safe `Nat.div` declaration path. The checker retains the
selector and fuel-recursion evidence, and the semantic certificate installs
literal quotient reflection in every safety model receiving the definition. -/
theorem addDefinition.WF_safe_natDiv
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hname : v.name = ``Nat.div)
    (hsafety : v.safety = .safe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        (v.safety ≠ .unsafe → ∃ ci' : VDefVal, ∀ safety,
          (ves.venv safety).AddDef safety (.defnInfo v) ci'
            (ves'.venv safety)) := by
  unfold addDefinition
  simp [hsafety]
  refine (checkSafeNatDivDefinition.WF wf v hname hsafety).run wf |>.bind
    fun _ hchecked => ?_
  obtain ⟨ci', htrSafe, hciSafe, hfresh, hevidence⟩ := hchecked
  rcases hevidence with
    ⟨go', goTy', topL', topR', goL', goR',
      hgoS, hgoTyS, htopL, htopR, hgoL, hgoR,
      hlevels, hnat, hbool, hble, hsub, hty,
      selector, hgoHas, htopEq, hgoEq⟩
  have hle : v.safety ≤ .safe := DefinitionSafety.le_safe
  have hmono := wf.mono hle
  have htr : TrDefVal v.safety (ves.venv v.safety) (.defnInfo v) ci' := by
    refine ⟨⟨⟨?_, htrSafe.1.1.2.1, htrSafe.1.1.2.2.mono hmono⟩,
      htrSafe.1.2⟩, htrSafe.2.mono hmono⟩
    rw [ConstantInfo.defnInfo_safety]
    exact DefinitionSafety.le_rfl
  have ⟨ves', hwf, hstep⟩ := addDef.WF wf v ci' v.safety
    (fun _ h => by simpa [ConstantInfo.defnInfo_safety] using h)
    htr (hciSafe.mono hmono) hfresh ?_ ?_
  · refine .pure ⟨ves', hwf, ?_, ?_⟩
    · intro safety
      exact (hstep safety).le
    · exact ⟨ci', hstep⟩
  · intro _
    exact ⟨by rw [ConstantInfo.defnInfo_safety, hsafety], hlevels⟩
  · intro safety base hvisible hadd
    have hsafetyLe : safety ≤ v.safety := by
      simpa [ConstantInfo.defnInfo_safety] using hvisible
    have hmodelMono : ves.venv .safe ≤ ves.venv safety :=
      hmono.trans (wf.mono hsafetyLe)
    have hci : ci'.WF (ves.venv safety) :=
      hciSafe.mono hmodelMono
    have hbaseWF : (base.addDefEq ci'.toDefEq).WF := by
      obtain ⟨decls, henvWF⟩ := (wf.tr (safety := safety)).wf
      have haddCi : (ves.venv safety).addConst ci'.name ci'.toVConstant =
          some base := by
        have haddCi := hadd
        have hvname : v.name = ci'.name := htrSafe.1.2
        rw [hvname] at haddCi
        exact haddCi
      exact ⟨.def ci' :: decls, .decl (.def hci haddCi) henvWF⟩
    have hname' : ci'.name = ``Nat.div :=
      htrSafe.1.2.symm.trans hname
    have hadd' : (ves.venv safety).addConst ``Nat.div ci'.toVConstant =
        some base := by
      simpa [hname] using hadd
    exact Environment.NatDivPrimitiveEvidence.conservesHasPrimitives
      (c := .mk' wf .safe v.levelParams)
      rfl rfl htrSafe.2 hname' htrSafe.1.1.2.1
      (wf.hasPrimitives (safety := safety)) hmodelMono hadd' hbaseWF
      ⟨go', goTy', topL', topR', goL', goR',
        hgoS, hgoTyS, htopL, htopR, hgoL, hgoR,
        hlevels, hnat, hbool, hble, hsub, hty,
        selector, hgoHas, htopEq, hgoEq⟩

/-- Fully proved residual safe-definition path for names outside the finite
primitive set. -/
theorem addDefinition.WF_safe_of_not_primitive
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hsafety : v.safety = .safe)
    (hn : Environment.primitives.contains v.name = false) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        (v.safety ≠ .unsafe → ∃ ci' : VDefVal, ∀ safety,
          (ves.venv safety).AddDef safety (.defnInfo v) ci'
            (ves'.venv safety)) := by
  unfold addDefinition
  simp [hsafety]
  refine (checkDefinition.WF_of_not_primitive wf v hn).run wf |>.bind
    fun _ hchecked => ?_
  obtain ⟨ci', hu, ht, hname, hvalue, hci, hfresh⟩ := hchecked
  have hle : v.safety ≤ .safe := DefinitionSafety.le_safe
  have hmono := wf.mono hle
  have htr : TrDefVal v.safety (ves.venv v.safety)
      (.defnInfo v) ci' := by
    refine ⟨⟨⟨?_, hu, ht.mono hmono⟩, hname⟩, hvalue.mono hmono⟩
    rw [ConstantInfo.defnInfo_safety]
    exact DefinitionSafety.le_rfl
  have ⟨ves', hwf, hstep⟩ := addDef.WF wf v ci' v.safety
    (fun _ h => by simpa [ConstantInfo.defnInfo_safety] using h)
    htr (hci.mono hmono) hfresh ?_ ?_
  · exact .pure ⟨ves', hwf, (hstep · |>.le), ⟨ci', hstep⟩⟩
  · intro hprimitive
    simp [hn] at hprimitive
  · intro safety base _ hadd
    exact ((wf.hasPrimitives (safety := safety)).addConst_of_not_primitive
      hn hadd).addDefEq

/-- Fully proved residual partial-definition path for names outside the
finite primitive set. -/
theorem addDefinition.WF_partial_of_not_primitive
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hsafety : v.safety = .partial)
    (hn : Environment.primitives.contains v.name = false) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        (v.safety ≠ .unsafe → ∃ ci' : VDefVal, ∀ safety,
          (ves.venv safety).AddDef safety (.defnInfo v) ci'
            (ves'.venv safety)) := by
  unfold addDefinition
  simp [hsafety]
  refine (checkDefinition.WF_of_not_primitive wf v hn).run wf |>.bind
    fun _ hchecked => ?_
  obtain ⟨ci', hu, ht, hname, hvalue, hci, hfresh⟩ := hchecked
  have hle : v.safety ≤ .safe := DefinitionSafety.le_safe
  have hmono := wf.mono hle
  have htr : TrDefVal v.safety (ves.venv v.safety)
      (.defnInfo v) ci' := by
    refine ⟨⟨⟨?_, hu, ht.mono hmono⟩, hname⟩, hvalue.mono hmono⟩
    rw [ConstantInfo.defnInfo_safety]
    exact DefinitionSafety.le_rfl
  have ⟨ves', hwf, hstep⟩ := addDef.WF wf v ci' v.safety
    (fun _ h => by simpa [ConstantInfo.defnInfo_safety] using h)
    htr (hci.mono hmono) hfresh ?_ ?_
  · exact .pure ⟨ves', hwf, (hstep · |>.le), ⟨ci', hstep⟩⟩
  · intro hprimitive
    simp [hn] at hprimitive
  · intro safety base _ hadd
    exact ((wf.hasPrimitives (safety := safety)).addConst_of_not_primitive
      hn hadd).addDefEq

/-- A safe definition cannot successfully claim one of the six primitive
inductive-family or constructor names. -/
theorem addDefinition.WF_safe_inductiveName
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hsafety : v.safety = .safe)
    (hname : v.name = ``Bool ∨ v.name = ``Bool.false ∨
      v.name = ``Bool.true ∨ v.name = ``Nat ∨
      v.name = ``Nat.zero ∨ v.name = ``Nat.succ) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        (v.safety ≠ .unsafe → ∃ ci' : VDefVal, ∀ safety,
          (ves.venv safety).AddDef safety (.defnInfo v) ci'
            (ves'.venv safety)) := by
  unfold addDefinition
  simp [hsafety]
  have hrun : ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ => False := by
    refine (checkDefinitionBody.WF wf v).bind fun _ state' _ _ => ?_
    refine (Environment.checkPrimitiveDef.WF_of_inductive_name
      (c := .mk' wf .safe v.levelParams) (s := state') (v := v) hname).bind
      fun allow _ _ hallow => ?_
    refine (TypeChecker.M.WF.liftExcept
      (checkName.WF (wf.tr (safety := .safe)).map_wf v.name allow)).mono
      fun _ _ _ hcheckedName => ?_
    subst allow
    have hnot := hcheckedName.2 rfl
    rcases hname with hname | hname | hname | hname | hname | hname
    all_goals
      simp [hname, Environment.primitives, NameSet.contains,
        NameSet.ofList] at hnot
  exact hrun.run wf |>.bind fun _ h => False.elim h

/-- A partial definition cannot successfully use any reserved primitive name:
the public primitive checker returns `false`, after which `checkName` rejects
the name. -/
theorem addDefinition.WF_partial_of_primitive
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hsafety : v.safety = .partial)
    (hp : Environment.primitives.contains v.name = true) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        (v.safety ≠ .unsafe → ∃ ci' : VDefVal, ∀ safety,
          (ves.venv safety).AddDef safety (.defnInfo v) ci'
            (ves'.venv safety)) := by
  unfold addDefinition
  simp [hsafety]
  have hrun : ((do
      checkDefinitionBody env v
      let allowPrimitive ← Environment.checkPrimitiveDef v
      Environment.checkName env v.name allowPrimitive) :
      TypeChecker.M Unit).WF (.mk' wf .safe v.levelParams) {} fun _ _ => False := by
    refine (checkDefinitionBody.WF wf v).bind fun _ state' _ _ => ?_
    refine (Environment.checkPrimitiveDef.WF_of_not_safe
      (c := .mk' wf .safe v.levelParams) (s := state') (v := v)
      (by simp [hsafety])).bind fun allow _ _ hallow => ?_
    subst allow
    refine (TypeChecker.M.WF.liftExcept
      (checkName.WF (wf.tr (safety := .safe)).map_wf v.name false)).mono
      fun _ _ _ hcheckedName => ?_
    have hnot := hcheckedName.2 rfl
    simp [hp] at hnot
  exact hrun.run wf |>.bind fun _ h => False.elim h

/-- Fully proved unsafe-definition transaction. Unsafe definitions are
checked recursively in a temporary axiom extension and cannot use reserved
primitive names. -/
theorem addDefinition.WF_unsafe
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) (hsafety : v.safety = .unsafe) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧
        (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        (v.safety ≠ .unsafe → ∃ ci' : VDefVal, ∀ safety,
          (ves.venv safety).AddDef safety (.defnInfo v) ci'
            (ves'.venv safety)) := by
  unfold addDefinition
  simp [hsafety]
  refine checkConstantVal.WF wf (.defnInfo v) false
      DefinitionSafety.unsafe_le
    |>.run wf |>.bind fun _ ⟨ci0, htr, hwfc, hn, hnonprim⟩ => ?_
  refine (checkNoMVarNoFVar.WF _ _ _).bind fun _ h => ?_
  have ⟨vesA, wfA, hstepA⟩ := addConst.WF wf
    (.axiomInfo { v with isUnsafe := true }) ci0 .unsafe
    (fun _ => id) ⟨⟨DefinitionSafety.unsafe_le, htr.1.2.1, htr.1.2.2⟩,
      htr.2⟩ hwfc hn (by simp [Lean.ConstantInfo.ReadinessTransparent])
    (hnonprim rfl)
    fun _ _ htr' hci' hadd' old =>
      .axiom htr' (by rwa [← old.map_wf.find?'_eq_find?]) hci' hadd' old
  have hadd := (hstepA .unsafe).2.2
  have hbodyRun := (checkBodyCore.WF (wfA.toVEnvAt .unsafe)
    (.defnDecl v) v.levelParams v.type v.value ci0.type
    (htr.1.2.2.mono (VEnv.addConst_le hadd)) h).run1
      (wfA.toVEnvAt .unsafe)
  simp only [Bool.not_eq_true'] at hbodyRun
  refine hbodyRun.map fun _ h3 => ?_
  obtain ⟨value', hvalue, hvalueType⟩ := h3
  have hciWF : (⟨ci0, value'⟩ : VDefVal).WF
      (vesA.venv .unsafe) := by
    show (vesA.venv .unsafe).HasType ci0.uvars [] value' ci0.type
    rw [← htr.1.2.1]
    exact hvalueType
  have ⟨ves', hwf', hmono'⟩ := addUnsafeDef.WF wf v ⟨ci0, value'⟩
    (vesA.venv .unsafe) ‹_› htr hwfc hadd hvalue hciWF hn (hnonprim rfl)
  exact ⟨ves', hwf', hmono'⟩

theorem addDefinition.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (v : DefinitionVal) :
    (addDefinition env v).WF fun env' =>
      ∃ ves' : VEnvs, ves'.WF env' ∧ (∀ safety, ves.venv safety ≤ ves'.venv safety) ∧
        (v.safety ≠ .unsafe → ∃ ci' : VDefVal, ∀ safety,
          (ves.venv safety).AddDef safety (.defnInfo v) ci' (ves'.venv safety)) := by
  cases hsafety : v.safety with
  | «unsafe» =>
    simpa only [hsafety] using addDefinition.WF_unsafe wf v hsafety
  | «partial» =>
    cases hp : Environment.primitives.contains v.name with
    | false =>
      simpa only [hsafety] using
        addDefinition.WF_partial_of_not_primitive wf v hsafety hp
    | true =>
      simpa only [hsafety] using
        addDefinition.WF_partial_of_primitive wf v hsafety hp
  | safe =>
    cases hp₀ : Environment.primitives.contains v.name with
    | false =>
      simpa only [hsafety] using
        addDefinition.WF_safe_of_not_primitive wf v hsafety hp₀
    | true =>
      have hp : v.name = ``Bool ∨ v.name = ``Bool.false ∨
          v.name = ``Bool.true ∨ v.name = ``Nat ∨
          v.name = ``Nat.zero ∨ v.name = ``Nat.succ ∨
          v.name = ``Nat.add ∨ v.name = ``Nat.pred ∨
          v.name = ``Nat.sub ∨ v.name = ``Nat.mul ∨
          v.name = ``Nat.pow ∨ v.name = ``Nat.gcd ∨
          v.name = ``Nat.mod ∨ v.name = ``Nat.div ∨
          v.name = ``Nat.beq ∨ v.name = ``Nat.ble ∨
          v.name = ``Nat.bitwise ∨ v.name = ``Nat.land ∨
          v.name = ``Nat.lor ∨ v.name = ``Nat.xor ∨
          v.name = ``Nat.shiftLeft ∨ v.name = ``Nat.shiftRight ∨
          v.name = ``String.ofList ∨ v.name = ``Char.ofNat := by
        simp [Environment.primitives, NameSet.contains, NameSet.ofList] at hp₀
        simpa only [eq_comm] using hp₀
      rcases hp with h | h | h | h | h | h | h | h | h | h | h | h | h |
        h | h | h | h | h | h | h | h | h | h | h
      iterate 6
        simpa only [hsafety] using
          addDefinition.WF_safe_inductiveName wf v hsafety (by simp [h])
      · simpa only [hsafety] using addDefinition.WF_safe_natAdd wf v h hsafety
      · simpa only [hsafety] using addDefinition.WF_safe_natPred wf v h hsafety
      · simpa only [hsafety] using addDefinition.WF_safe_natSub wf v h hsafety
      · simpa only [hsafety] using addDefinition.WF_safe_natMul wf v h hsafety
      · simpa only [hsafety] using addDefinition.WF_safe_natPow wf v h hsafety
      · simpa only [hsafety] using addDefinition.WF_safe_natGcd wf v h hsafety
      · simpa only [hsafety] using addDefinition.WF_safe_natMod wf v h hsafety
      · simpa only [hsafety] using addDefinition.WF_safe_natDiv wf v h hsafety
      · simpa only [hsafety] using addDefinition.WF_safe_natBEq wf v h hsafety
      · simpa only [hsafety] using addDefinition.WF_safe_natBLE wf v h hsafety
      · simpa only [hsafety] using
          addDefinition.WF_safe_natBitwise wf v h hsafety
      · simpa only [hsafety] using addDefinition.WF_safe_natLand wf v h hsafety
      · simpa only [hsafety] using addDefinition.WF_safe_natLor wf v h hsafety
      · simpa only [hsafety] using addDefinition.WF_safe_natXor wf v h hsafety
      · simpa only [hsafety] using
          addDefinition.WF_safe_natShiftLeft wf v h hsafety
      · simpa only [hsafety] using
          addDefinition.WF_safe_natShiftRight wf v h hsafety
      · simpa only [hsafety] using
          addDefinition.WF_safe_stringOfList wf v h hsafety
      · simpa only [hsafety] using
          addDefinition.WF_safe_charOfNat wf v h hsafety

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

/-! ## Retained inductive-input closedness -/

private theorem Except.WF.any (x : Except ε α) :
    x.WF fun _ => True := by
  intro _ _
  trivial

/-- A successful, yield-only `forIn` certifies a pointwise property of every
source element.  This is the small loop rule needed to project the family and
constructor closedness checks retained by `Environment.checkInductiveInput`. -/
private theorem Except.WF.forInYieldAll
    {xs : List α} {f : α → PUnit → Except ε (ForInStep PUnit)}
    {P : α → Prop}
    (body : ∀ x, (f x PUnit.unit).WF fun step =>
      P x ∧ step = .yield PUnit.unit) :
    (forIn xs PUnit.unit f).WF fun _ => ∀ x ∈ xs, P x := by
  induction xs with
  | nil => exact .pure (by simp)
  | cons head tail ih =>
      rw [List.forIn_cons]
      refine (body head).bind fun step hstep => ?_
      obtain ⟨headP, rfl⟩ := hstep
      exact ih.mono fun _ tailP x member => by
        rcases List.mem_cons.mp member with rfl | member
        · exact headP
        · exact tailP x member

/-- Closed family and constructor sources established by the public
inductive entry precheck, in their original source order. -/
def EnvironmentInductiveInputClosed (types : List InductiveType) : Prop :=
  ∀ indType ∈ types,
    indType.type.FVarsIn (fun _ => False) ∧
      ∀ ctor ∈ indType.ctors, ctor.type.FVarsIn (fun _ => False)

/-- Every original family and constructor head, and every original
constructor source, passed the public reserved-prefix precheck.  The property
deliberately names the transparent executable test, so it remains tied to the
exact host syntax consumed by nested elimination. -/
def EnvironmentInductiveInputNoNestedAux
  (types : List InductiveType) : Prop :=
  ∀ indType ∈ types,
    hasNestedAux (.const indType.name []) = false ∧
      ∀ ctor ∈ indType.ctors,
        hasNestedAux (.const ctor.name []) = false ∧
          hasNestedAux ctor.type = false

/-- Successful execution of the reserved-prefix check retains the exact
negative result of its transparent structural scan. -/
theorem checkNoNestedAux.WF (name : Name) (expression : Expr) :
    (checkNoNestedAux name expression).WF fun _ =>
      hasNestedAux expression = false := by
  unfold checkNoNestedAux
  split
  · exact Except.WF.throw
  · rename_i absent
    exact .pure (by simpa using absent)

/-- The retained public precheck supplies the syntactic free-variable premise
needed by the candidate interpreter, rather than leaving source translations
as a parallel semantic input. -/
theorem Environment.checkInductiveInput.WF
    (env : Environment) (types : List InductiveType) :
    (Environment.checkInductiveInput env types).WF fun _ =>
      EnvironmentInductiveInputClosed types := by
  unfold Environment.checkInductiveInput
  refine (Except.WF.forInYieldAll fun indType => ?_).bind fun _ closed =>
    .pure closed
  refine (Except.WF.any
    (checkNoNestedAux indType.name (.const indType.name []))).bind fun _ _ => ?_
  refine (checkNoMVarNoFVar.WF env indType.name indType.type).bind
    fun _ familyClosed => ?_
  refine (Except.WF.forInYieldAll fun ctor => ?_).bind
    fun _ constructorsClosed =>
      .pure ⟨⟨familyClosed, constructorsClosed⟩, rfl⟩
  refine (Except.WF.any
    (checkNoNestedAux ctor.name (.const ctor.name []))).bind fun _ _ => ?_
  refine (checkNoMVarNoFVar.WF env ctor.name ctor.type).bind
    fun _ constructorClosed => ?_
  refine (Except.WF.any (checkNoNestedAux ctor.name ctor.type)).bind
    fun _ _ => .pure ⟨constructorClosed, rfl⟩

/-- The retained public precheck also supplies reserved-prefix freedom for
every original family and constructor head and constructor source, without
rerunning or abstracting over the scan. -/
theorem Environment.checkInductiveInput.noNestedAux
    (env : Environment) (types : List InductiveType) :
    (Environment.checkInductiveInput env types).WF fun _ =>
      EnvironmentInductiveInputNoNestedAux types := by
  unfold Environment.checkInductiveInput
  refine (Except.WF.forInYieldAll fun indType => ?_).bind
    fun _ families => .pure families
  refine (checkNoNestedAux.WF
    indType.name (.const indType.name [])).bind fun _ familyNameAbsent => ?_
  refine (Except.WF.any
    (env.checkNoMVarNoFVar indType.name indType.type)).bind fun _ _ => ?_
  refine (Except.WF.forInYieldAll fun ctor => ?_).bind
    fun _ constructors => .pure ⟨⟨familyNameAbsent, constructors⟩, rfl⟩
  refine (checkNoNestedAux.WF
    ctor.name (.const ctor.name [])).bind fun _ constructorNameAbsent => ?_
  refine (Except.WF.any
    (env.checkNoMVarNoFVar ctor.name ctor.type)).bind fun _ _ => ?_
  refine (checkNoNestedAux.WF ctor.name ctor.type).bind fun _ absent => ?_
  exact .pure ⟨⟨constructorNameAbsent, absent⟩, rfl⟩

/-- Every constructor source in one retained list-validation trace is closed;
this interprets the exact `checkNoMVarNoFVar` equation stored at each source
position. -/
theorem AddInductive.ConstructorListValidationTrace.sources_closed
    {stats : AddInductive.InductiveStats} {isUnsafe : Bool}
    {familyIdx : Nat} {context : AddInductive.Context}
    {seen : NameSet} {constructors : List Constructor}
    (trace : AddInductive.ConstructorListValidationTrace stats isUnsafe
      familyIdx context seen constructors) :
    ∀ constructor ∈ constructors,
      constructor.type.FVarsIn (fun _ => False) := by
  induction trace with
  | nil =>
      intro constructor member
      nomatch member
  | cons seen head tail fresh closed rootCheck typeTrace tailTrace ih =>
      intro constructor member
      rcases List.mem_cons.mp member with rfl | member
      · exact checkNoMVarNoFVar.WF context.env constructor.name
          constructor.type () closed
      · exact ih constructor member

/-- The complete retained block trace exposes constructor-source closedness
for every family and constructor in source order. -/
theorem AddInductive.ConstructorBlockValidationTraces.sources_closed
    {stats : AddInductive.InductiveStats} {isUnsafe : Bool}
    {context : AddInductive.Context} {familyIdx : Nat}
    {types : List InductiveType}
    (traces : AddInductive.ConstructorBlockValidationTraces stats isUnsafe
      context familyIdx types) :
    ∀ source ∈ types, ∀ constructor ∈ source.ctors,
      constructor.type.FVarsIn (fun _ => False) := by
  induction traces with
  | nil =>
      intro source member
      nomatch member
  | cons head tail ih =>
      intro source member constructor constructorMember
      rcases List.mem_cons.mp member with rfl | member
      · exact head.sources_closed constructor constructorMember
      · exact ih source member constructor constructorMember

/-- Constructor-source closedness projected from the complete retained block
validation owner. -/
theorem AddInductive.ConstructorBlockValidationRun.sources_closed
    {types : List InductiveType} {stats : AddInductive.InductiveStats}
    {isUnsafe : Bool} {context : AddInductive.Context}
    (run : AddInductive.ConstructorBlockValidationRun types stats isUnsafe
      context) :
    ∀ source ∈ types, ∀ constructor ∈ source.ctors,
      constructor.type.FVarsIn (fun _ => False) :=
  run.traces.sources_closed

/-- The executable flattened-family closure gate reconstructs the exact
`FVarsIn False` fact consumed by source translation. -/
theorem AddInductive.FamilySourceClosedList.sources_closed
    (closed : AddInductive.FamilySourceClosedList sources) :
    ∀ source ∈ sources,
      source.type.FVarsIn (fun _ => False) := by
  induction closed with
  | nil =>
      intro source member
      nomatch member
  | cons noMVar noFVar tail ih =>
      intro source member
      rcases List.mem_cons.mp member with rfl | member
      · apply fvarsIn_iff.2
        refine ⟨?_, fvarsIn_iff_hasMVar noMVar⟩
        intro fv present
        rw [fvarsList_eq_nil noFVar] at present
        contradiction
      · exact ih source member

/-- The exact public precheck stored by an outer inductive execution retains
closedness of every original family and constructor source. -/
theorem AddInductive.EnvironmentInductiveExecution.inputClosed
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv) :
    EnvironmentInductiveInputClosed types :=
  Environment.checkInductiveInput.WF env types () execution.inputCheck

/-- The exact public precheck stored by an outer execution retains
reserved-prefix freedom of every original family and constructor head and
constructor source. -/
theorem AddInductive.EnvironmentInductiveExecution.inputNoNestedAux
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv) :
    EnvironmentInductiveInputNoNestedAux types :=
  Environment.checkInductiveInput.noNestedAux env types ()
    execution.inputCheck

/-- The retained ordinary normalization prefix certifies syntactic closure of
every flattened family source, including auxiliary families introduced by
genuine nested elimination. -/
theorem AddInductive.EnvironmentInductiveExecution.flattenedFamilySourcesClosed
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv) :
    ∀ source ∈ execution.nested.types,
      source.type.FVarsIn (fun _ => False) :=
  execution.flattened.eliminationExecution.normalization.familySourcesClosed
    |>.sources_closed

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
    ProjectionResolutionReady finalEnv (output.venv safety)
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

/-! ## Replaying one exact safe transaction across all safety models -/

/-- A metadata fold replayed from one Theory model into a larger aligned
model, while retaining the same raw inventory and exact host-map endpoints.
The output comparison is useful both for later phases and for transporting
semantic certificates selected by the original `.safe` replay. -/
structure AddInductConstants.Replay
    {kind : InductConstantKind} {C₁ C₂ : ConstMap}
    {env₁ env₂ : VEnv} {raws : List VConstVal}
    (original : AddInductConstants kind C₁ env₁ raws C₂ env₂)
    (safety : DefinitionSafety) (target : VEnv) where
  output : VEnv
  trace : AddInductConstants kind C₁ target raws C₂ output
  le : env₂ ≤ output
  aligned : Aligned safety C₂ output
  nestedConstsWF : VInductDecl.NestedConstsWF env₁ raws →
    VInductDecl.NestedConstsWF target raws

/-- Replay an exact metadata fold against any larger aligned input model.
Freshness is recovered from host/Theory name-domain alignment; translations
are transported monotonically from the original fold. -/
def AddInductConstants.replay
    {kind : InductConstantKind} {C₁ C₂ : ConstMap}
    {env₁ env₂ target : VEnv} {raws : List VConstVal}
    (original : AddInductConstants kind C₁ env₁ raws C₂ env₂)
    (input_le : env₁ ≤ target) (input_aligned : Aligned safety C₁ target) :
    original.Replay safety target :=
  match original with
  | .nil => {
      output := target
      trace := .nil
      le := input_le
      aligned := input_aligned
      nestedConstsWF := fun _ => trivial }
  | @AddInductConstants.cons _ C₁ env₁ raw Cmid envMid raws C₂ env₂ head tail => by
      have targetFresh : target.constants raw.name = none := by
        cases found : target.constants raw.name with
        | none => rfl
        | some value =>
            obtain ⟨info, hostFound, _⟩ :=
              input_aligned.find?_iff.mpr ⟨value, found⟩
            rw [head.map_fresh] at hostFound
            contradiction
      let next : VEnv := {
        target with
        constants := fun name =>
          if raw.name = name then some raw.toVConstant
          else target.constants name }
      have added : target.addConst raw.name raw.toVConstant = some next := by
        simp [VEnv.addConst, targetFresh, next]
      let replayedHead : AddInductConstant kind C₁ target raw Cmid next := {
        info := head.info
        kind_eq := head.kind_eq
        tr := head.tr.mono input_le
        map_fresh := head.map_fresh
        env_add := added
        map_add := head.map_add }
      have next_le : envMid ≤ next :=
        VEnv.addConst_mono input_le head.env_add added
      let replayedTail := replay tail next_le
        (input_aligned.addInductConstant replayedHead)
      exact {
        output := replayedTail.output
        trace := .cons replayedHead replayedTail.trace
        le := replayedTail.le
        aligned := replayedTail.aligned
        nestedConstsWF := fun wf =>
          ⟨wf.1.mono input_le, fun targetNext targetAdded => by
            have targetNext_eq :=
              Option.some.inj (targetAdded.symm.trans added)
            subst targetNext
            exact replayedTail.nestedConstsWF
              (wf.2 _ head.env_add)⟩ }

/-- Chained rule well-formedness is monotone when the same deterministic rule
list is folded over a larger starting model. -/
theorem VInductDecl.NestedRulesWF.mono
    {env₁ env₂ : VEnv} (input_le : env₁ ≤ env₂) :
    ∀ {rules : List VDefEq}, VInductDecl.NestedRulesWF env₁ rules →
      VInductDecl.NestedRulesWF env₂ rules
  | [], _ => trivial
  | _ :: _, wf => ⟨wf.1.mono input_le,
      VInductDecl.NestedRulesWF.mono
        (VEnv.addDefEq_mono input_le) wf.2⟩

/-- Folding one common list of Theory equations preserves an existing model
ordering. -/
theorem VEnv.addDefEqFold_mono (input_le : env₁ ≤ env₂) :
    ∀ rules : List VDefEq,
      rules.foldl VEnv.addDefEq env₁ ≤
        rules.foldl VEnv.addDefEq env₂
  | [] => input_le
  | _rule :: rules =>
      VEnv.addDefEqFold_mono (VEnv.addDefEq_mono input_le) rules

/-- A complete ordinary block trace replayed against a larger aligned input,
with the generation descriptor and host-map endpoints held fixed. -/
structure AddInductBlockTrace.Replay
    {C₁ C₂ : ConstMap} {env₁ env₂ : VEnv}
    {source : VInductDecl}
    (original : AddInductBlockTrace C₁ env₁ source C₂ env₂)
    (safety : DefinitionSafety) (target : VEnv) where
  output : VEnv
  trace : AddInductBlockTrace C₁ target source C₂ output
  le : env₂ ≤ output
  aligned : Aligned safety C₂ output

/-- Replay one exact ordinary `.safe` transaction in any larger safety model.
All three constant phases are rebuilt from the original translations, and
the generated-rule endpoint is the deterministic fold over the replayed
recursor environment. -/
def AddInductBlockTrace.replay
    {C₁ C₂ : ConstMap} {env₁ env₂ target : VEnv}
    {source : VInductDecl}
    (original : AddInductBlockTrace C₁ env₁ source C₂ env₂)
    (input_le : env₁ ≤ target) (input_aligned : Aligned safety C₁ target) :
    original.Replay safety target := by
  let types := original.addTypes.replay input_le input_aligned
  have originalStage : env₁.stageInductiveTypes source.types =
      some original.typeEnv := by
    rw [← VInductDecl.blockTypeConstants_foldlM_eq_stageInductiveTypes]
    exact original.addTypes.to_foldlM
  have blockEnv_eq : original.blockEnv = original.typeEnv := by
    exact Option.some.inj
      (original.generation_wf.blockWF.1.1.symm.trans originalStage)
  have targetStage : target.stageInductiveTypes source.types =
      some types.output := by
    rw [← VInductDecl.blockTypeConstants_foldlM_eq_stageInductiveTypes]
    exact types.trace.to_foldlM
  have blockEnv_le : original.blockEnv ≤ types.output := by
    rw [blockEnv_eq]
    exact types.le
  let ctors := original.addCtors.replay types.le types.aligned
  let recs := original.addRecs.replay ctors.le ctors.aligned
  let output := original.generation.generatedRules.foldl
    VEnv.addDefEq recs.output
  let replayed : AddInductBlockTrace C₁ target source C₂ output := {
    generation := original.generation
    blockEnv := types.output
    generation_wf := original.generation_wf.mono input_le blockEnv_le
      targetStage
    typeMap := original.typeMap
    typeEnv := types.output
    ctorMap := original.ctorMap
    ctorEnv := ctors.output
    recEnv := recs.output
    addTypes := types.trace
    addCtors := ctors.trace
    addRecs := recs.trace
    recK := original.recK
    addRules := ⟨rfl⟩ }
  have output_le : env₂ ≤ output := by
    rw [← original.addRules.fold_eq]
    exact VEnv.addDefEqFold_mono recs.le _
  exact {
    output := output
    trace := replayed
    le := output_le
    aligned := recs.aligned.addDefEqFold _ }

/-- A complete restored nested trace replayed against a larger aligned input,
again retaining one shared restored artifact and exact host-map endpoints. -/
structure AddInductNestedTrace.Replay
    {C₁ C₂ : ConstMap} {env₁ env₂ : VEnv}
    {source : VInductDecl}
    (original : AddInductNestedTrace C₁ env₁ source C₂ env₂)
    (safety : DefinitionSafety) (target : VEnv) where
  output : VEnv
  trace : AddInductNestedTrace C₁ target source C₂ output
  le : env₂ ≤ output
  aligned : Aligned safety C₂ output

/-- Replay one exact restored `.safe` transaction in a larger safety model.
The chained nested-WF package is reconstructed phase by phase from the paired
constant folds, then the common restored-rule list is folded deterministically. -/
noncomputable def AddInductNestedTrace.replay
    {C₁ C₂ : ConstMap} {env₁ env₂ target : VEnv}
    {source : VInductDecl}
    (original : AddInductNestedTrace C₁ env₁ source C₂ env₂)
    (input_le : env₁ ≤ target) (input_aligned : Aligned safety C₁ target) :
    original.Replay safety target := by
  let types := original.addTypes.replay input_le input_aligned
  let ctors := original.addCtors.replay types.le types.aligned
  let recs := original.addRecs.replay ctors.le ctors.aligned
  let nested_wf : original.nested.WF target := {
    types := types.nestedConstsWF original.nested_wf.types
    ctors := by
      intro targetTypeEnv targetTypes
      have targetTypeEnv_eq : targetTypeEnv = types.output :=
        Option.some.inj (targetTypes.symm.trans types.trace.to_foldlM)
      subst targetTypeEnv
      exact ctors.nestedConstsWF
        (original.nested_wf.ctors original.addTypes.to_foldlM)
    recs := by
      intro targetTypeEnv targetCtorEnv targetTypes targetCtors
      have targetTypeEnv_eq : targetTypeEnv = types.output :=
        Option.some.inj (targetTypes.symm.trans types.trace.to_foldlM)
      subst targetTypeEnv
      have targetCtorEnv_eq : targetCtorEnv = ctors.output :=
        Option.some.inj (targetCtors.symm.trans ctors.trace.to_foldlM)
      subst targetCtorEnv
      exact recs.nestedConstsWF
        (original.nested_wf.recs original.addTypes.to_foldlM
          original.addCtors.to_foldlM)
    rules := by
      intro targetTypeEnv targetCtorEnv targetRecEnv targetTypes targetCtors
        targetRecs
      have targetTypeEnv_eq : targetTypeEnv = types.output :=
        Option.some.inj (targetTypes.symm.trans types.trace.to_foldlM)
      subst targetTypeEnv
      have targetCtorEnv_eq : targetCtorEnv = ctors.output :=
        Option.some.inj (targetCtors.symm.trans ctors.trace.to_foldlM)
      subst targetCtorEnv
      have targetRecEnv_eq : targetRecEnv = recs.output :=
        Option.some.inj (targetRecs.symm.trans recs.trace.to_foldlM)
      subst targetRecEnv
      exact (original.nested_wf.rules original.addTypes.to_foldlM
        original.addCtors.to_foldlM original.addRecs.to_foldlM).mono recs.le }
  let output := original.nested.generatedRules.foldl VEnv.addDefEq recs.output
  let replayed : AddInductNestedTrace C₁ target source C₂ output := {
    nested := original.nested
    nested_wf := nested_wf
    typeMap := original.typeMap
    typeEnv := types.output
    ctorMap := original.ctorMap
    ctorEnv := ctors.output
    recEnv := recs.output
    addTypes := types.trace
    addCtors := ctors.trace
    addRecs := recs.trace
    recK := original.recK
    addRules := ⟨rfl⟩ }
  have output_le : env₂ ≤ output := by
    rw [← original.addRules.fold_eq]
    exact VEnv.addDefEqFold_mono recs.le _
  exact {
    output := output
    trace := replayed
    le := output_le
    aligned := recs.aligned.addDefEqFold _ }

/-- One exact `.safe` ordinary trace completed into a safety-indexed family.
The safe endpoint is retained definitionally, while the other two traces replay
the same checked generation in their larger aligned input models. -/
structure AddInductBlockTrace.CoherentReplay
    {C₁ C₂ : ConstMap} {input : VEnvs} {source : VInductDecl}
    {safeOutput : VEnv}
    (original : AddInductBlockTrace C₁ (input.venv .safe) source C₂
      safeOutput) where
  output : VEnvs
  traces : ∀ safety, AddInductBlockTrace C₁ (input.venv safety) source C₂
    (output.venv safety)
  generation_eq : ∀ safety, (traces safety).generation = original.generation
  safe_output_eq : output.venv .safe = safeOutput

/-- Replay an ordinary safe trace at `.partial` and `.unsafe`, retaining the
original trace itself at `.safe`. -/
def AddInductBlockTrace.coherentReplay
    {C₁ C₂ : ConstMap} {input : VEnvs} {source : VInductDecl}
    {safeOutput : VEnv}
    (original : AddInductBlockTrace C₁ (input.venv .safe) source C₂
      safeOutput)
    (input_le : ∀ safety, input.venv .safe ≤ input.venv safety)
    (input_aligned : ∀ safety, Aligned safety C₁ (input.venv safety)) :
    original.CoherentReplay := by
  let partialReplay := original.replay (input_le .partial) (input_aligned .partial)
  let unsafeReplay := original.replay (input_le .unsafe) (input_aligned .unsafe)
  let output : VEnvs := ⟨fun
    | .safe => safeOutput
    | .partial => partialReplay.output
    | .unsafe => unsafeReplay.output⟩
  refine {
    output := output
    traces := ?_
    generation_eq := ?_
    safe_output_eq := rfl }
  · intro safety
    cases safety with
    | safe => exact original
    | «partial» => exact partialReplay.trace
    | «unsafe» => exact unsafeReplay.trace
  · intro safety
    cases safety <;> rfl

/-- One exact `.safe` nested trace completed into a safety-indexed family, with
the restored artifact shared literally by all three traces. -/
structure AddInductNestedTrace.CoherentReplay
    {C₁ C₂ : ConstMap} {input : VEnvs} {source : VInductDecl}
    {safeOutput : VEnv}
    (original : AddInductNestedTrace C₁ (input.venv .safe) source C₂
      safeOutput) where
  output : VEnvs
  traces : ∀ safety, AddInductNestedTrace C₁ (input.venv safety) source C₂
    (output.venv safety)
  nested_eq : ∀ safety, (traces safety).nested = original.nested
  safe_output_eq : output.venv .safe = safeOutput

/-- Replay a nested safe trace at `.partial` and `.unsafe`, retaining the
original trace itself at `.safe`. -/
noncomputable def AddInductNestedTrace.coherentReplay
    {C₁ C₂ : ConstMap} {input : VEnvs} {source : VInductDecl}
    {safeOutput : VEnv}
    (original : AddInductNestedTrace C₁ (input.venv .safe) source C₂
      safeOutput)
    (input_le : ∀ safety, input.venv .safe ≤ input.venv safety)
    (input_aligned : ∀ safety, Aligned safety C₁ (input.venv safety)) :
    original.CoherentReplay := by
  let partialReplay := original.replay (input_le .partial) (input_aligned .partial)
  let unsafeReplay := original.replay (input_le .unsafe) (input_aligned .unsafe)
  let output : VEnvs := ⟨fun
    | .safe => safeOutput
    | .partial => partialReplay.output
    | .unsafe => unsafeReplay.output⟩
  refine {
    output := output
    traces := ?_
    nested_eq := ?_
    safe_output_eq := rfl }
  · intro safety
    cases safety with
    | safe => exact original
    | «partial» => exact partialReplay.trace
    | «unsafe» => exact unsafeReplay.trace
  · intro safety
    cases safety <;> rfl

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

/-- Completion of one exact safe nonprimitive trace into a coherent
safety-indexed transaction.  Retaining the safe endpoint explicitly lets the
subsequent readiness layer consume certificates proved at that exact model. -/
structure SafeReplay
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv)
    (source : VInductDecl) (input : VEnvs) (safeOutput : VEnv) where
  output : VEnvs
  safe_output_eq : output.venv .safe = safeOutput
  transactions : execution.CoherentPrimitivePreservingTransactions source
    input output

/-- An ordinary exact trace need only be constructed in the `.safe` model.
Input coherence and alignment replay it at the other safety levels while
preserving one shared checked generation. -/
def ofOrdinarySafeTrace
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv}
    {source : VInductDecl} {input : VEnvs} {safeOutput : VEnv}
    (wf : input.WF env)
    (numNested_eq : execution.nested.aux2nested.size = 0)
    (safeTrace : AddInductBlockTrace env.constants (input.venv .safe) source
      finalEnv.constants safeOutput)
    (typeNames : ∀ ci ∈ source.blockTypeConstants,
      ci.name ∉ VEnv.reflectedPrimitiveNames ∧
        Environment.primitives.contains ci.name = false)
    (ctorNames : ∀ ci ∈ source.blockConstructorConstants,
      ci.name ∉ VEnv.reflectedPrimitiveNames ∧
        Environment.primitives.contains ci.name = false)
    (recNames : ∀ ci ∈ safeTrace.generation.recursors,
      ci.name ∉ VEnv.reflectedPrimitiveNames ∧
        Environment.primitives.contains ci.name = false) :
    SafeReplay execution source input safeOutput := by
  let replay := safeTrace.coherentReplay
    (fun safety => wf.mono (safety := safety) (safety' := .safe)
      DefinitionSafety.le_safe)
    (fun safety => (wf.tr (safety := safety)).aligned)
  exact {
    output := replay.output
    safe_output_eq := replay.safe_output_eq
    transactions := .ordinary numNested_eq safeTrace.generation replay.traces
      replay.generation_eq typeNames ctorNames recNames }

/-- A restored nested trace likewise replays from `.safe`; all safety levels
retain the same checked restoration artifact and exact restored inventories. -/
noncomputable def ofNestedSafeTrace
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv}
    {source : VInductDecl} {input : VEnvs} {safeOutput : VEnv}
    (wf : input.WF env)
    (numNested_ne : execution.nested.aux2nested.size ≠ 0)
    (safeTrace : AddInductNestedTrace env.constants (input.venv .safe) source
      finalEnv.constants safeOutput)
    (typeNames : ∀ ci ∈ source.blockTypeConstants,
      ci.name ∉ VEnv.reflectedPrimitiveNames ∧
        Environment.primitives.contains ci.name = false)
    (ctorNames : ∀ ci ∈ source.blockConstructorConstants,
      ci.name ∉ VEnv.reflectedPrimitiveNames ∧
        Environment.primitives.contains ci.name = false)
    (recNames : ∀ ci ∈ safeTrace.nested.recursors,
      ci.name ∉ VEnv.reflectedPrimitiveNames ∧
        Environment.primitives.contains ci.name = false) :
    SafeReplay execution source input safeOutput := by
  let replay := safeTrace.coherentReplay
    (fun safety => wf.mono (safety := safety) (safety' := .safe)
      DefinitionSafety.le_safe)
    (fun safety => (wf.tr (safety := safety)).aligned)
  exact {
    output := replay.output
    safe_output_eq := replay.safe_output_eq
    transactions := .nested numNested_ne safeTrace.nested replay.traces
      replay.nested_eq typeNames ctorNames recNames }

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
    ProjectionResolutionReady finalEnv (output.venv safety)
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

/-- A registered view of a canonical Bool/Nat constructor with at least one
field cannot have consumed any parameters.  This is phrased over an arbitrary
future extension so downstream readiness proofs can reuse the exact block
trace without rebuilding the canonical declarations. -/
theorem VInductDecl.CanonicalPrimitiveConstants.constructorView_nparams_eq_zero
    {decl : VInductDecl}
    (constants : decl.CanonicalPrimitiveConstants)
    {m₁ m₂ : ConstMap} {input output future : VEnv}
    (trace : AddInductBlockTrace m₁ input decl m₂ output)
    (hle : output ≤ future) {view : VStructureView}
    (hview : view.WF future) (hfields : view.fields ≠ [])
    {raw : VConstVal} (member : raw ∈ decl.blockConstructorConstants)
    (nameEq : raw.name = view.constructorName) :
    view.nparams = 0 := by
  have rawLookup : output.constants raw.name = some raw.toVConstant :=
    trace.addRules.le.constants <|
      trace.addRecs.le.constants <| trace.addCtors.lookup raw member
  have futureLookup : future.constants raw.name = some raw.toVConstant :=
    hle.constants rawLookup
  have registered := hview.constructor
  rw [← nameEq, futureLookup] at registered
  have typeEq : view.constructor.raw.type = raw.type :=
    congrArg VConstant.type (Option.some.inj registered).symm
  cases constants with
  | bool _ constructorsEq =>
      rw [constructorsEq] at member
      simp [VPrimitiveInductive.boolConstructors] at member
      rcases member with rfl | rfl
      all_goals
        exfalso
        apply hfields
        cases hnp : view.nparams <;>
          simp [VStructureView.fields, VInductDecl.NormalizedCtor.rawFields,
            typeEq, hnp, VExpr.dropN, VInductDecl.ctorFields, VExpr.bool]
  | nat _ constructorsEq =>
      rw [constructorsEq] at member
      simp [VPrimitiveInductive.natConstructors] at member
      rcases member with rfl | rfl
      · exfalso
        apply hfields
        cases hnp : view.nparams <;>
          simp [VStructureView.fields, VInductDecl.NormalizedCtor.rawFields,
            typeEq, hnp, VExpr.dropN, VInductDecl.ctorFields, VExpr.nat]
      · cases hnp : view.nparams with
        | zero => rfl
        | succ n =>
            exfalso
            apply hfields
            cases n <;>
              simp [VStructureView.fields,
                VInductDecl.NormalizedCtor.rawFields, typeEq, hnp,
                VExpr.dropN, VInductDecl.ctorFields, VExpr.nat]

/--
info: 'Lean4Lean.VInductDecl.CanonicalPrimitiveConstants.constructorView_nparams_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms VInductDecl.CanonicalPrimitiveConstants.constructorView_nparams_eq_zero

/-- Every generated recursor retains the name of the source family whose
normalized generation record produced it. -/
theorem VInductDecl.BlockGenerationChecked.recursor_owner
    {source : VInductDecl} (generation : source.BlockGenerationChecked)
    {raw : VConstVal} (member : raw ∈ generation.recursors) :
    ∃ familyRaw ∈ source.blockTypeConstants,
      raw.name = mkRecName familyRaw.name := by
  simp only [VInductDecl.BlockGenerationChecked.recursors,
    List.mem_map] at member
  obtain ⟨family, familyMember, rfl⟩ := member
  refine ⟨family.raw.toVConstVal, ?_, rfl⟩
  rw [VInductDecl.blockTypeConstants]
  apply List.mem_map.2
  refine ⟨family.raw, ?_, rfl⟩
  rw [← generation.families_map_raw]
  exact List.mem_map.2 ⟨family, familyMember, rfl⟩

/-- Conversely, every source family owns an exact member of the generated
recursor inventory.  This is the source-indexed direction needed when a host
singleton-family observation must recover its final recursor lookup. -/
theorem VInductDecl.BlockGenerationChecked.recursor_of_family
    {source : VInductDecl} (generation : source.BlockGenerationChecked)
    {familyRaw : VConstVal}
    (member : familyRaw ∈ source.blockTypeConstants) :
    ∃ recursor ∈ generation.recursors,
      recursor.name = mkRecName familyRaw.name := by
  rw [VInductDecl.blockTypeConstants] at member
  obtain ⟨raw, raw_member, rfl⟩ := List.mem_map.mp member
  have normalized_member : raw ∈ generation.families.map (·.raw) := by
    rw [generation.families_map_raw]
    exact raw_member
  obtain ⟨family, family_member, family_raw_eq⟩ :=
    List.mem_map.mp normalized_member
  let recursor : VConstVal :=
    ⟨generation.generatedRecursor family, .str family.raw.name "rec"⟩
  refine ⟨recursor, ?_, ?_⟩
  · exact List.mem_map.mpr ⟨family, family_member, rfl⟩
  · simp [recursor, mkRecName, family_raw_eq]

/-- info: 'Lean4Lean.VInductDecl.BlockGenerationChecked.recursor_owner' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms VInductDecl.BlockGenerationChecked.recursor_owner

/-- info: 'Lean4Lean.VInductDecl.BlockGenerationChecked.recursor_of_family' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms VInductDecl.BlockGenerationChecked.recursor_of_family

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

/-- Primitive recognition plus the exact public nested-elimination equation
selects the canonical Bool/Nat candidate observers.  The input translation
supplies the host constant-map invariant needed to follow the real family
declaration fold. -/
theorem primitiveCandidateObserversOfNestedRun
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    {lparams : List Name} {nparams : Nat} {types : List InductiveType}
    {isUnsafe : Bool}
    (primitiveResult : PrimitiveInductiveResult lparams nparams types
      isUnsafe true)
    (nested : ElimNestedInductive.Result)
    (nestedRun : ElimNestedInductive.runAt env
      ({} : FuelConfig).inductiveFuel nparams lparams types = .ok nested) :
    AddInductive.NormalizationCandidateExecution.CandidateObserversComplete
      nparams nested.types nested.aux2nested.size isUnsafe
        (AddInductive.Context.forInductive env lparams isUnsafe true {}) := by
  have recognized := primitiveResult.recognized rfl
  obtain ⟨safe, lparamsEq, nparamsEq, shape⟩ := recognized
  have noop := nested.canonicalPrimitive_noop shape (by
    simpa only [lparamsEq, nparamsEq] using nestedRun)
  obtain ⟨type, typesEq, typeType, primitive⟩ := shape
  have mapWF : env.constants.WF :=
    (wf.tr (safety := .safe)).map_wf
  subst isUnsafe
  subst lparams
  subst nparams
  rw [noop.1, noop.2, typesEq]
  cases primitive with
  | inl boolShape =>
      obtain ⟨typeName, constructorsEq⟩ := boolShape
      have typeEq : type =
          AddInductive.PrimitiveRecursorReplay.boolSource := by
        cases type
        simp only at typeType typeName constructorsEq ⊢
        subst typeType
        subst typeName
        subst constructorsEq
        rfl
      rw [typeEq]
      exact AddInductive.PrimitiveRecursorReplay.boolCandidateObserversComplete
        env mapWF
  | inr natShape =>
      obtain ⟨typeName, binderName, binderInfo, constructorsEq⟩ := natShape
      have typeEq : type =
          AddInductive.PrimitiveRecursorReplay.natSource
            binderName binderInfo := by
        cases type
        simp only at typeType typeName constructorsEq ⊢
        subst typeType
        subst typeName
        subst constructorsEq
        rfl
      rw [typeEq]
      exact AddInductive.PrimitiveRecursorReplay.natCandidateObserversComplete
        env mapWF binderName binderInfo

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.canonicalPrimitive_noop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.abstract_eq]
-/
#guard_msgs in
#print axioms AddInductive.EnvironmentInductiveExecution.canonicalPrimitive_noop

/--
info: 'Lean4Lean.primitiveCandidateObserversOfNestedRun' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.instantiate1_eq,
 Expr.looseBVarRange_eq,
 Expr.mkData_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms primitiveCandidateObserversOfNestedRun

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

/-- The normalization prefix retains the primitive-admission mode selected by
the outer environment execution. -/
theorem AddInductive.EnvironmentInductiveExecution.flattenedValidationAllowPrimitive_eq
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv) :
    execution.flattened.eliminationExecution.normalization.validationContext.allowPrimitive =
      allowPrimitive := by
  simpa only [AddInductive.Context.forInductive] using
    execution.flattened.eliminationExecution.normalization.validationContext_allowPrimitive_all
      (execution.flattened.normalization_run execution.flattenedRun)

/-- Family-only Theory staging selected by a retained default-fuel safe
nonprimitive outer execution.  The declaration is still intentionally free of
constructors; the next dependent phase enriches it without changing the
computed family endpoint. -/
structure
    AddInductive.EnvironmentInductiveExecution.FlattenedFamilySourceStagingResult
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv)
    (ves : VEnvs) where
  familyDecl : VInductDecl
  nparams_eq : familyDecl.nparams = nparams
  staging : VInductDecl.NormalizationCandidateBlockFamilySourceStagingInput
    (AddInductive.Context.forInductive env lparams false false {})
    execution.flattened.eliminationExecution.normalization
    (ves.venv .safe) lparams familyDecl

/-- Constructor-source closedness read from the exact validation hierarchy
embedded in the flattened normalization execution. -/
theorem
    AddInductive.EnvironmentInductiveExecution.flattenedConstructorSourcesClosed
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv) :
    ∀ source ∈ execution.nested.types,
      ∀ constructor ∈ source.ctors,
        constructor.type.FVarsIn (fun _ => False) :=
  execution.flattened.eliminationExecution.normalization
    |>.constructorValidation.sources_closed

/-- Every constructor named by the retained family metadata is absent at the
family-only host endpoint.  The proof aligns that family record back to its
flattened source, locates the corresponding synthesized constructor record,
and reads freshness from the later constructor-declaration trace. -/
theorem
    AddInductive.EnvironmentInductiveExecution.flattenedFamilyConstructorsAbsent
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv)
    (inputMapWF : env.constants.WF) :
    ∀ info ∈
        execution.flattened.eliminationExecution.normalization.declaredInfos,
      ∀ ctor ∈ info.ctors,
        execution.flattened.eliminationExecution.normalization.familyEnv.find?
          ctor = none := by
  let normalization :=
    execution.flattened.eliminationExecution.normalization
  have normalizationRun :=
    execution.flattened.normalization_run execution.flattenedRun
  have nindicesSize : normalization.stats.nindices.size =
      execution.nested.types.length :=
    normalization.validationNindicesSize_all normalizationRun
  have metadata : List.Forall₂
      (fun source info => ∃ numIndices,
        info = AddInductive.declaredInductiveInfo normalization.stats nparams
          execution.nested.types.toArray source numIndices
          execution.nested.aux2nested.size isUnsafe
          normalization.validationContext)
      execution.nested.types normalization.declaredInfos := by
    simpa only [normalization,
      AddInductive.NormalizationCandidateExecution.declaredInfos,
      List.toList_toArray] using
      AddInductive.declaredInductiveInfos_matches normalization.stats nparams
        execution.nested.types.toArray execution.nested.aux2nested.size
        isUnsafe normalization.validationContext (by simpa using nindicesSize)
  have validationMapWF : normalization.validationContext.env.constants.WF := by
    simpa only [normalization, execution.flattenedValidationEnv_eq] using
      inputMapWF
  have familyMapWF := normalization.declareTrace.map_wf validationMapWF
  have constructorFresh :=
    execution.flattened.eliminationExecution.declareConstructorTrace
      |>.names_fresh familyMapWF
  intro info infoMember ctor ctorMember
  obtain ⟨source, sourceMember, numIndices, infoEq⟩ :=
    Lean4Lean.List.Forall₂.forall_exists_r metadata info infoMember
  rw [infoEq] at ctorMember
  change ctor ∈ source.ctors.map (·.name) at ctorMember
  obtain ⟨sourceCtor, sourceCtorMember, sourceCtorName⟩ :=
    List.mem_map.mp ctorMember
  obtain ⟨ctorInfo, ctorInfoMember, ctorInfoName⟩ :=
    AddInductive.declaredConstructorInfosFor_name normalization.stats
      source.name isUnsafe
      execution.flattened.eliminationExecution.constructorContext 0
      source.ctors sourceCtorMember
  have ctorInfoAllMember : ctorInfo ∈
      execution.flattened.eliminationExecution.declaredConstructorInfos := by
    simp only [
      AddInductive.NormalizationEliminationExecution.declaredConstructorInfos,
      AddInductive.declaredConstructorInfos_toArray, List.mem_flatMap]
    exact ⟨source, sourceMember, ctorInfoMember⟩
  have freshMap := constructorFresh ctorInfo ctorInfoAllMember
  have freshFind : normalization.familyEnv.find? ctorInfo.name = none := by
    change normalization.familyEnv.constants.find?' ctorInfo.name = none
    rw [familyMapWF.find?'_eq_find?]
    exact freshMap
  simpa only [ctorInfoName, sourceCtorName] using freshFind

/-- The exact family-only endpoint selected by outer staging inherits both
readiness capabilities from the input model.  Multi-constructor families are
inert by shape; singleton families are inert because the retained later
constructor trace proves their sole constructor has not been declared yet. -/
theorem
    AddInductive.EnvironmentInductiveExecution.FlattenedFamilySourceStagingResult.endpointReadiness
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    (family : execution.FlattenedFamilySourceStagingResult ves)
    (wf : ves.WF env) :
    ProjectionResolutionReady
        execution.flattened.eliminationExecution.normalization.familyEnv
        family.staging.familyInsertion.blockEnv ∧
      StructureEtaReady
        execution.flattened.eliminationExecution.normalization.familyEnv
        family.staging.familyInsertion.blockEnv := by
  have inputMapWF := (wf.tr (safety := .safe)).map_wf
  have validationMapWF :
      execution.flattened.eliminationExecution.normalization.validationContext.env.constants.WF := by
    simpa only [execution.flattenedValidationEnv_eq] using inputMapWF
  have evidence : List.Forall₂
      (fun _ raw => raw.toVConstant.WF (ves.venv .safe))
      execution.flattened.eliminationExecution.normalization.declaredInfos
      family.familyDecl.types :=
    Lean4Lean.List.Forall₂.imp
      (h := family.staging.declarationEvidence) fun _ _ related => related.2
  exact VInductDecl.declarationTraceConstructorAbsentReadiness
    family.staging.familyInsertion.kernelTrace family.staging.stage evidence
    (execution.flattenedFamilyConstructorsAbsent inputMapWF)
    validationMapWF (wf.tr (safety := .safe)).wf.ordered
    (by simpa only [execution.flattenedValidationEnv_eq] using
      wf.projectionReady (safety := .safe))
    (by simpa only [execution.flattenedValidationEnv_eq] using
      wf.structureEtaReady (safety := .safe))

/-- Enrich a family-only outer staging result with the exact retained
constructor traversals.  Constructor closedness comes from validation; only
readiness at the already-computed family endpoint remains explicit. -/
theorem
    AddInductive.EnvironmentInductiveExecution.FlattenedFamilySourceStagingResult.enrich
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    (family : execution.FlattenedFamilySourceStagingResult ves)
    (projectionReady : ProjectionResolutionReady
      execution.flattened.eliminationExecution.normalization.familyEnv
      family.staging.familyInsertion.blockEnv)
    (structureEtaReady : StructureEtaReady
      execution.flattened.eliminationExecution.normalization.familyEnv
      family.staging.familyInsertion.blockEnv) :
    Nonempty
      (VInductDecl.NormalizationCandidateBlockEnrichedStagingResult
        family.staging) :=
  family.staging.enrich projectionReady structureEtaReady
    execution.flattenedConstructorSourcesClosed

/-- Enrich the retained outer family stage without any caller-selected
readiness premise.  Both capabilities are reconstructed from the same input
well-formedness and the producer-owned family/constructor declaration traces. -/
theorem
    AddInductive.EnvironmentInductiveExecution.FlattenedFamilySourceStagingResult.enrich_of_wf
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    (family : execution.FlattenedFamilySourceStagingResult ves)
    (wf : ves.WF env) :
    Nonempty
      (VInductDecl.NormalizationCandidateBlockEnrichedStagingResult
        family.staging) := by
  have readiness := family.endpointReadiness wf
  exact family.enrich readiness.1 readiness.2

/-- Thread an already translated raw family list through the retained outer
execution.  Default safe nonprimitive execution fixes the candidate root's
fresh-name namespace, positive recursion depth, safety, and primitive mode, so
none remains a caller-selected semantic premise. -/
def
    AddInductive.EnvironmentInductiveExecution.flattenedFamilySourceStaging
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv)
    {ves : VEnvs} (wf : ves.WF env)
    {familyDecl : VInductDecl}
    (uvars_eq : familyDecl.uvars = lparams.length)
    (familySources : VInductDecl.CandidateBlockFamilyTypeSourceListInput
      (ves.venv .safe) lparams execution.nested.types familyDecl.types) :
    VInductDecl.NormalizationCandidateBlockFamilySourceStagingInput
      (AddInductive.Context.forInductive env lparams false false {})
      execution.flattened.eliminationExecution.normalization
      (ves.venv .safe) lparams familyDecl := by
  apply
    execution.flattened.eliminationExecution.normalization.familySourceStaging
      (execution.flattened.normalization_run execution.flattenedRun) wf
      (by simp [AddInductive.Context.forInductive])
      uvars_eq familySources
      (by simp [AddInductive.Context.forInductive])
      execution.flattened.eliminationExecution.normalization.familyTerminalSorts
  · rfl
  · rfl
  · rfl

/-- Recover and stage one family-only raw Theory declaration from the exact
pre-family candidate traversal retained by a default safe nonprimitive outer
execution.  Both source closedness and terminal-sort evidence are checked and
retained by the normalization prefix itself. -/
theorem
    AddInductive.EnvironmentInductiveExecution.exists_flattenedFamilySourceStaging
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv)
    {ves : VEnvs} (wf : ves.WF env) :
    Nonempty
      (execution.FlattenedFamilySourceStagingResult ves) := by
  let context := AddInductive.Context.forInductive env lparams false false {}
  let normalization :=
    execution.flattened.eliminationExecution.normalization
  let preFamily : TypeChecker.CandidateSemanticStage
      { context with lctx := {} } (ves.venv .safe) lparams :=
    TypeChecker.CandidateSemanticStage.root wf rfl (by
      simp [context, AddInductive.Context.forInductive])
  obtain ⟨⟨familyRaws, familySources⟩⟩ :=
    VInductDecl.CandidateBlockFamilyTypeSourceListInput.exists_ofProduced
      preFamily normalization.candidate.families
        normalization.familyTypesProduced
        execution.flattenedFamilySourcesClosed
  let familyDecl : VInductDecl := {
    uvars := lparams.length
    nparams := nparams
    types := familyRaws }
  exact ⟨{
    familyDecl
    nparams_eq := rfl
    staging := execution.flattenedFamilySourceStaging wf rfl
      familySources }⟩

/-- In the ordinary no-rewrite case, exact equality between the nested pass's
flattened sources and the public input is no longer needed for staging, but
this compatibility wrapper preserves the source-equality-indexed API. -/
theorem
    AddInductive.EnvironmentInductiveExecution.exists_flattenedFamilySourceStaging_of_types_eq
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv)
    {ves : VEnvs} (wf : ves.WF env)
    (_types_eq : execution.nested.types = types) :
    Nonempty
      (execution.FlattenedFamilySourceStagingResult ves) :=
  execution.exists_flattenedFamilySourceStaging wf

/-- A retained outer execution constructs the complete enriched
pre-generation hierarchy without any separately supplied candidate, source,
or endpoint evidence. -/
theorem
    AddInductive.EnvironmentInductiveExecution.exists_flattenedEnrichedStaging
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv)
    {ves : VEnvs} (wf : ves.WF env) :
    ∃ family : execution.FlattenedFamilySourceStagingResult ves,
      Nonempty
        (VInductDecl.NormalizationCandidateBlockEnrichedStagingResult
          family.staging) := by
  obtain ⟨family⟩ :=
    execution.exists_flattenedFamilySourceStaging wf
  exact ⟨family, family.enrich_of_wf wf⟩

/-- In the ordinary source-preserving case, the retained outer execution now
constructs the complete enriched pre-generation hierarchy directly from input
well-formedness.  Exact source equality is retained only as a compatibility
index for callers that already classify the no-rewrite branch. -/
theorem
    AddInductive.EnvironmentInductiveExecution.exists_flattenedEnrichedStaging_of_types_eq
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv)
    {ves : VEnvs} (wf : ves.WF env)
    (_types_eq : execution.nested.types = types) :
    ∃ family : execution.FlattenedFamilySourceStagingResult ves,
      Nonempty
        (VInductDecl.NormalizationCandidateBlockEnrichedStagingResult
          family.staging) :=
  execution.exists_flattenedEnrichedStaging wf

/-! ## Exact flattened generation transaction staging -/

/-- The family extraction and constructor enrichment selected by one retained
outer execution, packaged as a single dependent value.  Keeping the enriched
raw declaration attached to its family-only staging owner avoids choosing a
parallel Theory source when the analyzer and metadata phases are connected. -/
structure
    AddInductive.EnvironmentInductiveExecution.FlattenedEnrichedStagingResult
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv)
    (ves : VEnvs) where
  family : execution.FlattenedFamilySourceStagingResult ves
  enriched : VInductDecl.NormalizationCandidateBlockEnrichedStagingResult
    family.staging

/-- The complete raw Theory block selected by exact family extraction and
constructor enrichment. -/
def
    AddInductive.EnvironmentInductiveExecution.FlattenedEnrichedStagingResult.source
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    (staged : execution.FlattenedEnrichedStagingResult ves) : VInductDecl :=
  staged.enriched.enrichment.toRawDecl staged.family.familyDecl

/-- Constructor enrichment preserves the family declaration's parameter
count, so the selected raw block is indexed by the retained outer count. -/
theorem
    AddInductive.EnvironmentInductiveExecution.FlattenedEnrichedStagingResult.source_nparams_eq
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    (staged : execution.FlattenedEnrichedStagingResult ves) :
    staged.source.nparams = nparams := by
  simpa only [FlattenedEnrichedStagingResult.source,
    VInductDecl.CandidateBlockSourceListEnrichment.toRawDecl] using
    staged.family.nparams_eq

/-- Constructor enrichment preserves the family declaration's universe
count, so the selected raw block is indexed by the retained outer universe
parameter inventory. -/
theorem
    AddInductive.EnvironmentInductiveExecution.FlattenedEnrichedStagingResult.source_uvars_eq
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    (staged : execution.FlattenedEnrichedStagingResult ves) :
    staged.source.uvars = lparams.length := by
  simpa only [FlattenedEnrichedStagingResult.source,
    VInductDecl.CandidateBlockSourceListEnrichment.toRawDecl] using
    staged.family.staging.uvars_eq

/-- The complete semantic input carried by the enriched staging owner. -/
def
    AddInductive.EnvironmentInductiveExecution.FlattenedEnrichedStagingResult.semanticInput
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    (staged : execution.FlattenedEnrichedStagingResult ves) :
    VInductDecl.NormalizationCandidateBlockSemanticInput
      (ves.venv .safe) staged.enriched.blockEnv lparams
      execution.flattened.candidate staged.source :=
  staged.enriched.semantic.semanticInput

/-- Enriched outer staging owns the exact raw semantic block, while the
accepted normalization prefix owns complete generation-spine evidence for
the same dependent candidate.  Together they discharge generation's
executable layout check without an additional caller premise. -/
theorem
    AddInductive.EnvironmentInductiveExecution.FlattenedEnrichedStagingResult.generationShape
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    (staged : execution.FlattenedEnrichedStagingResult ves) :
    VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true := by
  exact staged.semanticInput.generationShape_of_generationSpines
    execution.flattened.eliminationExecution.normalization.generationSpines

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.FlattenedEnrichedStagingResult.generationShape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.eqv_eq,
 Expr.instantiate1_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms AddInductive.EnvironmentInductiveExecution.FlattenedEnrichedStagingResult.generationShape

/-- Reindex the retained ordinary recursor execution onto the enriched raw
Theory source.  The preceding theorem derives the required generation shape
from the outer producer and dependent staging owner. -/
def
    AddInductive.EnvironmentInductiveExecution.FlattenedEnrichedStagingResult.recursorShape
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    (staged : execution.FlattenedEnrichedStagingResult ves)
    (shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true) :
    VInductDecl.ProducedBlockRecursorShapeCandidate staged.source
      execution.nested.types execution.nested.aux2nested.size false
      (AddInductive.Context.forInductive env lparams false false {}) :=
  VInductDecl.ProducedBlockRecursorShapeCandidate.ofExecution execution.flattened
    execution.flattenedRun execution.nested.types_nonempty
      staged.source_nparams_eq shape

/-- The retained recursor producer passes the universe audit against the
exact enriched Theory source selected by this staging owner. -/
theorem
    AddInductive.EnvironmentInductiveExecution.FlattenedEnrichedStagingResult.recursorShape_recUniverseRun
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    (staged : execution.FlattenedEnrichedStagingResult ves)
    (shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true) :
    AddInductive.checkBlockRecursorUniverseSemantics staged.source.uvars
      (staged.recursorShape shape).execution.eliminationExecution = .ok () := by
  exact (staged.recursorShape shape).execution
    |>.checkBlockRecursorUniverseSemantics_eq_ok
      (staged.recursorShape shape).producedExecution
      (staged.recursorShape shape).kernelSources_nonempty
      (by
        simpa only [AddInductive.Context.forInductive] using
          staged.source_uvars_eq)

/-- The same retained producer supplies the positional source-universe gate
shared by both constructor Stage-3 audit variants. -/
theorem
    AddInductive.EnvironmentInductiveExecution.FlattenedEnrichedStagingResult.recursorShape_stage3LevelsTranslation
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    (staged : execution.FlattenedEnrichedStagingResult ves)
    (shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true) :
    (staged.recursorShape shape).execution.eliminationExecution.normalization.stats.levels.mapM
        (VLevel.ofLevel lparams) =
      some (VLevel.params staged.source.uvars) := by
  rw [staged.source_uvars_eq]
  exact (staged.recursorShape shape).execution.stage3LevelsTranslation
    (staged.recursorShape shape).producedExecution
    (staged.recursorShape shape).kernelSources_nonempty

/-- Reindexing the retained recursor producer along the source parameter-count
equality does not change its positional family index-count inventory.  This
nondependent projection is the useful boundary for consumers which relate the
semantic raw source back to host declaration metadata. -/
theorem
    AddInductive.EnvironmentInductiveExecution.FlattenedEnrichedStagingResult.recursorShape_nindices_eq
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    (staged : execution.FlattenedEnrichedStagingResult ves)
    (shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true) :
    (staged.recursorShape shape).execution.eliminationExecution.normalization.stats.nindices =
      execution.flattened.eliminationExecution.normalization.stats.nindices := by
  cases staged with
  | mk family enriched =>
      cases family with
      | mk familyDecl nparams_eq familyStaging =>
          cases familyDecl with
          | mk uvars familyNparams familyTypes =>
              simp only at nparams_eq
              subst familyNparams
              rfl

/-- Execute the strengthened constructor and recursor audits against the
exact recursor producer retained by this outer staging value.  The producer
itself is not recomputed, so a successful result can feed the canonical
semantic assembly without an equality transport between parallel runs. -/
def
    AddInductive.EnvironmentInductiveExecution.FlattenedEnrichedStagingResult.recursorAudit?
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    (staged : execution.FlattenedEnrichedStagingResult ves)
    (shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true) :
    Except Exception (VInductDecl.ProducedBlockRecursorStage3AuditRun
      (staged.recursorShape shape) lparams) :=
  (staged.recursorShape shape).auditStage3? lparams

/-- Execute the accepted-execution audit whose Stage-3 and pre-family
structural traces permit resolved projection syntax. -/
def
    AddInductive.EnvironmentInductiveExecution.FlattenedEnrichedStagingResult.recursorResolvedAudit?
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    (staged : execution.FlattenedEnrichedStagingResult ves)
    (shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true) :
    Except Exception (VInductDecl.ProducedBlockRecursorResolvedAuditRun
      (staged.recursorShape shape) lparams) :=
  (staged.recursorShape shape).auditResolved? lparams

/-- Execute only the projection-aware audit surface consumed by ordinary
semantic assembly.  The stronger raw-parameter checks remain separate for
nested restoration. -/
def
    AddInductive.EnvironmentInductiveExecution.FlattenedEnrichedStagingResult.recursorResolvedCoreAudit?
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    (staged : execution.FlattenedEnrichedStagingResult ves)
    (shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true) :
    Except Exception (VInductDecl.ProducedBlockRecursorResolvedCoreAuditRun
      (staged.recursorShape shape) lparams) :=
  (staged.recursorShape shape).auditResolvedCore? lparams

/-- Once the three structural constructor checks have been recovered from
retained staging, the constructor-universe field and successful core-audit
transaction require no additional premise.  Recursor-universe metadata is
derived directly from the retained execution at the elimination boundary. -/
theorem
    AddInductive.EnvironmentInductiveExecution.FlattenedEnrichedStagingResult.recursorResolvedCoreAudit?_success_of_structural
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    (staged : execution.FlattenedEnrichedStagingResult ves)
    (shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true)
    (alignmentRun :
      AddInductive.ConstructorBlockCandidateAlignmentTrace.check
        ((staged.recursorShape shape).execution.eliminationExecution.normalization
          |>.constructorValidation.traces)
        (staged.recursorShape shape).candidate.families = .ok ())
    (stage3Run :
      AddInductive.ConstructorBlockStage3ResolvedTraces.check
        (staged.recursorShape shape).execution.eliminationExecution.normalization.stats
        lparams staged.source.uvars
        (staged.recursorShape shape).candidate.families = .ok ())
    (preFamilyRun :
      AddInductive.checkConstructorMutualBlockResolvedPreFamilySafety
        (staged.recursorShape shape).execution.eliminationExecution.normalization.stats
        (staged.recursorShape shape).execution.eliminationExecution.normalization.validationContext
        (staged.recursorShape shape).candidate.families = .ok ()) :
    ∃ audit : VInductDecl.ProducedBlockRecursorResolvedCoreAuditRun
        (staged.recursorShape shape) lparams,
      staged.recursorResolvedCoreAudit? shape = .ok audit := by
  let produced := staged.recursorShape shape
  have universeRun := produced.constructorUniverseRun
  simpa only [FlattenedEnrichedStagingResult.recursorResolvedCoreAudit?,
    produced] using
    produced.auditResolvedCore?_success lparams alignmentRun stage3Run
      preFamilyRun universeRun

/-- Execute only the producer-owned raw host-parameter trace consumed by
nested restoration.  The result remains indexed by the exact reindexed
recursor producer retained by this outer staging value. -/
def
    AddInductive.EnvironmentInductiveExecution.FlattenedEnrichedStagingResult.recursorRawHostParameterAudit?
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    (staged : execution.FlattenedEnrichedStagingResult ves)
    (shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true) :
    Except Lean.Kernel.Exception
      (VInductDecl.ProducedBlockRawHostParameterAuditRun
        (staged.recursorShape shape)) :=
  (staged.recursorShape shape).rawHostParameterAudit?

/-- Project Stage-3 success through the outer staging reindexing to the exact
narrow raw-host executable.  The returned witness is indexed by
`staged.recursorShape shape`, so no equality to a parallel recursor producer
is needed downstream. -/
theorem
    AddInductive.EnvironmentInductiveExecution.FlattenedEnrichedStagingResult.recursorRawHostParameterAudit?_success
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    (staged : execution.FlattenedEnrichedStagingResult ves)
    (shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true)
    (audit : VInductDecl.ProducedBlockRecursorStage3AuditRun
      (staged.recursorShape shape) lparams) :
    ∃ rawAudit : VInductDecl.ProducedBlockRawHostParameterAuditRun
        (staged.recursorShape shape),
      staged.recursorRawHostParameterAudit? shape = .ok rawAudit := by
  exact audit.rawHostParameterAudit?_success

/-- The reindexed recursor producer retains the nonprimitive validation mode
of the safe outer execution. -/
theorem
    AddInductive.EnvironmentInductiveExecution.FlattenedEnrichedStagingResult.recursorShape_validationAllowPrimitive_eq
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    (staged : execution.FlattenedEnrichedStagingResult ves)
    (shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true) :
    (staged.recursorShape shape).execution.eliminationExecution.normalization.validationContext.allowPrimitive =
      false := by
  have run := (staged.recursorShape shape).execution.normalization_run
    (staged.recursorShape shape).producedExecution
  simpa only [AddInductive.Context.forInductive] using
    (staged.recursorShape shape).execution.eliminationExecution.normalization
      |>.validationContext_allowPrimitive_all run

/-- The complete family/constructor staging value reindexed to the recursor
shape owner above.  This is proof-only transport along the parameter-count
equality; no verifier phase is rerun. -/
def
    AddInductive.EnvironmentInductiveExecution.FlattenedEnrichedStagingResult.recursorStaging
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    (staged : execution.FlattenedEnrichedStagingResult ves)
    (shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true) :
    VInductDecl.NormalizationCandidateBlockStagingInput
      (AddInductive.Context.forInductive env lparams false false {})
      (staged.recursorShape shape).execution.eliminationExecution.normalization
      (ves.venv .safe) staged.enriched.blockEnv lparams
      staged.source := by
  cases staged with
  | mk family enriched =>
      cases family with
      | mk familyDecl nparams_eq familyStaging =>
          cases familyDecl with
          | mk uvars familyNparams familyTypes =>
              simp only at nparams_eq
              subst familyNparams
              exact enriched.staging

/-- The enriched semantic input reindexed to the same recursor-shape owner.
As with `recursorStaging`, this eliminates only the source-header equality and
does not repeat normalization or translation. -/
def
    AddInductive.EnvironmentInductiveExecution.FlattenedEnrichedStagingResult.recursorSemanticInput
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    (staged : execution.FlattenedEnrichedStagingResult ves)
    (shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true) :
    VInductDecl.NormalizationCandidateBlockSemanticInput
      (ves.venv .safe) staged.enriched.blockEnv lparams
      (staged.recursorShape shape).candidate staged.source := by
  cases staged with
  | mk family enriched =>
      cases family with
      | mk familyDecl nparams_eq familyStaging =>
          cases familyDecl with
          | mk uvars familyNparams familyTypes =>
              simp only at nparams_eq
              subst familyNparams
              exact enriched.semantic.semanticInput

/-- Package the existing existential enrichment theorem in a form whose raw
source remains directly projectable by later dependent phases. -/
theorem
    AddInductive.EnvironmentInductiveExecution.exists_flattenedEnrichedStagingResult
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv)
    {ves : VEnvs} (wf : ves.WF env) :
    Nonempty (execution.FlattenedEnrichedStagingResult ves) := by
  obtain ⟨family, ⟨enriched⟩⟩ :=
    execution.exists_flattenedEnrichedStaging wf
  exact ⟨{ family, enriched }⟩

/-- One exact semantic generation run attached to the enriched raw source,
the retained ordinary recursor execution, and their full declaration staging
input.  The dependent indices prevent any later phase from substituting a
parallel source or normalization candidate. -/
structure
    AddInductive.EnvironmentInductiveExecution.FlattenedExactRecursorStagingResult
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    (staged : execution.FlattenedEnrichedStagingResult ves)
    (generation : VInductDecl.BlockGenerationChecked staged.source)
    (shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true) where
  run : VInductDecl.ExactProducedBlockRecursorRun
    (ves.venv .safe) staged.enriched.blockEnv lparams
    (staged.recursorShape shape) generation

/-- Close the exact semantic-generation and post-constructor alignment phases
around the source and candidate already selected by enriched outer staging.
Identifying the generation block's normalization with each checker-selected
semantic owner derives the exact analyzer result internally.  Semantic WF and
checker/elimination correspondence remain indexed by the same dependent
execution. -/
theorem
    AddInductive.EnvironmentInductiveExecution.FlattenedEnrichedStagingResult.exists_exactRecursorStagingResult
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    (staged : execution.FlattenedEnrichedStagingResult ves)
    (generation : VInductDecl.BlockGenerationChecked staged.source)
    (shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true)
    (normalization_eq : ∀ semantic :
        VInductDecl.NormalizationCandidateBlockSemanticRun
          (ves.venv .safe)
          staged.enriched.blockEnv lparams
          (staged.recursorShape shape).candidate staged.source,
      generation.block.normalization = semantic.normalization)
    (checked : generation.block.checked.WF (ves.venv .safe)
      generation.validated.resultLevel)
    (resultLevelWF : generation.validated.resultLevel.WF staged.source.uvars)
    (generatedParamsTel : TypeChecker.TelDefEqEvidence (ves.venv .safe)
      staged.source.uvars [] generation.generatedParams
        generation.block.checked.params)
    (generatedIndicesTel : ∀ family ∈ generation.families,
      TypeChecker.TelDefEqEvidence (ves.venv .safe) staged.source.uvars
        generation.generatedParams.reverse
        (family.rawIndices staged.source.nparams)
        (generation.generatedIndices family))
    (generatedFieldsTel : ∀ constructor ∈ generation.flatCtors,
      TypeChecker.TelDefEqEvidence staged.enriched.blockEnv staged.source.uvars
        generation.generatedParams.reverse
        (constructor.ctor.rawFields staged.source.nparams)
        (generation.generatedFields constructor))
    (elimination : AddInductive.CheckerBlockEliminationRun generation
      (staged.recursorShape shape).execution.eliminationExecution) :
    Nonempty
      (execution.FlattenedExactRecursorStagingResult staged generation
        shape) := by
  let produced := staged.recursorShape shape
  have analysis : ∀ semantic :
      VInductDecl.NormalizationCandidateBlockSemanticRun
        (ves.venv .safe) staged.enriched.blockEnv lparams
        produced.candidate staged.source,
      semantic.normalization.checkBlock? = some generation.block := by
    intro semantic
    exact VInductDecl.Normalization.checkBlock?_eq_some_iff.mpr
      (normalization_eq semantic)
  obtain ⟨block⟩ :=
    produced.eliminationBase.base.exactBlockGenerationRun_nonempty
      (staged.recursorSemanticInput shape) generation analysis checked
      resultLevelWF generatedParamsTel generatedIndicesTel generatedFieldsTel
  exact ⟨{
    run := {
      elimination := {
        block
        elimination
        isUnsafe_eq := rfl
        validation_lparams_eq :=
          (staged.recursorStaging shape).validation_lparams_eq } } }⟩

/-- Extend the exact family/constructor declaration staging through the
actual recursor inventory retained by the outer execution.  Callers supply
only translation and typing of those synthesized recursor records in the
already-computed post-constructor Theory environment. -/
noncomputable def
    AddInductive.EnvironmentInductiveExecution.FlattenedExactRecursorStagingResult.metadataPrefix
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {generation : VInductDecl.BlockGenerationChecked staged.source}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    (result : execution.FlattenedExactRecursorStagingResult staged generation
      shape)
    (evidence : List.Forall₂
      (fun info raw => TrConstVal .safe
        (result.run.elimination.declarationRun
          (staged.recursorStaging shape)).constructors.ctorEnv
        (.recInfo info) raw)
      (staged.recursorShape shape).execution.recursors.infos
      generation.recursors)
    (rawsWF : ∀ raw ∈ generation.recursors,
      raw.toVConstant.WF
        (result.run.elimination.declarationRun
          (staged.recursorStaging shape)).constructors.ctorEnv) :
    VInductDecl.ExactProducedBlockMetadataPrefixRun result.run :=
  result.run.metadataPrefix (staged.recursorStaging shape) evidence rawsWF

/-- One canonical semantic generation run attached to the source and
normalization candidate retained by enriched outer staging.  Unlike
`FlattenedExactRecursorStagingResult`, this package permits the canonical
mixed raw/view block produced by the semantic analyzer; the generation is a
field owned by that run rather than a parallel index selected by a caller. -/
structure
    AddInductive.EnvironmentInductiveExecution.FlattenedSemanticRecursorStagingResult
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    (staged : execution.FlattenedEnrichedStagingResult ves)
    (shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true) where
  semantic : VInductDecl.NormalizationCandidateBlockSemanticRun
    (ves.venv .safe) staged.enriched.blockEnv lparams
    (staged.recursorShape shape).candidate staged.source
  generation : VInductDecl.BlockGenerationChecked staged.source
  run : VInductDecl.ProducedBlockSemanticEliminationRun
    (ves.venv .safe) staged.enriched.blockEnv lparams
    (staged.recursorShape shape).eliminationBase semantic generation

/-- Lift one producer-owned semantic recursor result into the retained outer
execution.  The source, candidate, semantic interpretation, generation, and
elimination proof are all fixed by dependent indices; this constructor does
not rerun analysis or accept a parallel generation witness. -/
def
    AddInductive.EnvironmentInductiveExecution.FlattenedSemanticRecursorStagingResult.ofProduced
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    {semantic : VInductDecl.NormalizationCandidateBlockSemanticRun
      (ves.venv .safe) staged.enriched.blockEnv lparams
      (staged.recursorShape shape).candidate staged.source}
    (producer : VInductDecl.ProducedBlockSemanticRecursorRun
      (ves.venv .safe) staged.enriched.blockEnv lparams
      (staged.recursorShape shape) semantic) :
    execution.FlattenedSemanticRecursorStagingResult staged shape where
  semantic := semantic
  generation := producer.generation
  run := producer.run

/-- Construct the canonical semantic recursor transaction selected by an
enriched outer execution and its exact Stage-3 audit.  The semantic
interpretation is obtained from the staging value itself; callers cannot
choose a parallel raw view, generation result, or recursor endpoint. -/
noncomputable def
    AddInductive.EnvironmentInductiveExecution.FlattenedEnrichedStagingResult.canonicalSemanticRecursorStagingResult
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    (staged : execution.FlattenedEnrichedStagingResult ves)
    (shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true)
    (audit : VInductDecl.ProducedBlockRecursorStage3AuditRun
      (staged.recursorShape shape) lparams) :
    execution.FlattenedSemanticRecursorStagingResult staged shape :=
  let semantic := Classical.choice (staged.recursorSemanticInput shape).exists
  .ofProduced <|
    (staged.recursorShape shape)
      |>.canonicalProducedBlockSemanticRecursorRunOfAudit semantic rfl
        (staged.recursorStaging shape) audit

/-- Construct the semantic recursor transaction selected by the
projection-aware accepted-execution audit.  Constructor semantics are chosen
internally from the construction-owned endpoint matrix. -/
noncomputable def
    AddInductive.EnvironmentInductiveExecution.FlattenedEnrichedStagingResult.canonicalResolvedSemanticRecursorStagingResult
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    (staged : execution.FlattenedEnrichedStagingResult ves)
    (shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true)
    (audit : VInductDecl.ProducedBlockRecursorResolvedCoreAuditRun
      (staged.recursorShape shape) lparams) :
    execution.FlattenedSemanticRecursorStagingResult staged shape :=
  let semantic := Classical.choice (staged.recursorSemanticInput shape).exists
  let selection := (staged.recursorShape shape)
    |>.canonicalProducedBlockSemanticRecursorSelectionOfResolvedAudit semantic
      rfl (staged.recursorStaging shape) audit
  .ofProduced selection.2

/-- Execute the proof-producing recursor representation check for the
canonical semantic generation owned by the outer staging result.  Success
returns the complete family/constructor/recursor metadata prefix at the
producer's exact endpoints. -/
noncomputable def
    AddInductive.EnvironmentInductiveExecution.FlattenedSemanticRecursorStagingResult.metadataPrefix?
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    (result : execution.FlattenedSemanticRecursorStagingResult staged shape) :
    Option (VInductDecl.ProducedBlockSemanticMetadataPrefixRun
      (staged.recursorShape shape) result.semantic result.generation
      result.run) :=
  (staged.recursorShape shape).semanticMetadataPrefix? result.semantic
    result.generation result.run (staged.recursorStaging shape)

/-- An original Theory declaration and checked nested artifact whose
flattened block is exactly the enriched source selected by the retained outer
execution.  The auxiliary-count equation ties the Theory transformation to
the genuine nested branch of that same host execution. -/
structure
    AddInductive.EnvironmentInductiveExecution.FlattenedNestedArtifact
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    (staged : execution.FlattenedEnrichedStagingResult ves) where
  source : VInductDecl
  nested : source.NestedBlockChecked
  flat_eq : nested.elim.flat = staged.source
  numNested_eq : nested.elim.numNested = execution.nested.aux2nested.size
  /-- The exact target-block copies consulted by the Theory elimination are
  the well-formed constants already present in the safe input model. -/
  targetsWF : VInductDecl.NestedTargetsWF (ves.venv .safe)
    nested.elim.targets

/-- The exact flattened generation is determined by the aligned nested
artifact; it is not another analyzer output supplied beside that artifact. -/
def
    AddInductive.EnvironmentInductiveExecution.FlattenedNestedArtifact.generation
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    (artifact : execution.FlattenedNestedArtifact staged) :
    VInductDecl.BlockGenerationChecked staged.source :=
  artifact.flat_eq ▸ artifact.nested.generation

/-- A definitionally aligned presentation of the checked nested artifact.
Only its stored flat field is re-presented; `flat_eq` proves that this value is
equal to the original artifact while making the exact flattened source and
generation reduce without casts in downstream dependent APIs. -/
def
    AddInductive.EnvironmentInductiveExecution.FlattenedNestedArtifact.alignedNested
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    (artifact : execution.FlattenedNestedArtifact staged) :
  artifact.source.NestedBlockChecked where
  elim := {
    targets := artifact.nested.elim.targets
    fuel := artifact.nested.elim.fuel
    state := artifact.nested.elim.state
    run_eq := artifact.nested.elim.run_eq
    flat := staged.source
    flat_eq := by
      rw [← artifact.flat_eq]
      exact artifact.nested.elim.flat_eq
    specs := artifact.nested.elim.specs
    specs_eq := artifact.nested.elim.specs_eq
    nparams_eq := by
      rw [← artifact.flat_eq]
      exact artifact.nested.elim.nparams_eq }
  generation := artifact.generation
  source_restore_safe := artifact.nested.source_restore_safe

/-- The aligned presentation is propositionally the exact checked artifact
supplied by the Theory nested analyzer. -/
theorem
    AddInductive.EnvironmentInductiveExecution.FlattenedNestedArtifact.alignedNested_eq
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    (artifact : execution.FlattenedNestedArtifact staged) :
    artifact.alignedNested = artifact.nested := by
  cases artifact with
  | mk source nested flat_eq numNested_eq targetsWF =>
      cases nested with
      | mk elim generation source_restore_safe =>
          cases elim with
          | mk targets fuel state run_eq flat flat_state_eq specs specs_eq
              nparams_eq =>
              cases flat_eq
              rfl

/-- The original Theory declaration aligned with a retained nested execution
has the exact shared parameter count supplied to the public host pipeline.
This now follows from the flattening invariant itself, rather than from an
extra caller-owned equality. -/
theorem
    AddInductive.EnvironmentInductiveExecution.FlattenedNestedArtifact.source_nparams_eq
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    (artifact : execution.FlattenedNestedArtifact staged) :
    artifact.source.nparams = nparams := by
  calc
    artifact.source.nparams = artifact.nested.elim.flat.nparams :=
      artifact.nested.elim.nparams_eq.symm
    _ = staged.source.nparams := congrArg VInductDecl.nparams artifact.flat_eq
    _ = nparams := staged.source_nparams_eq

/-- The execution-owned flattened declaration retains the complete original
nested source inventory as an exact header prefix.  This is the producer
alignment used to select a restored source family from the same generated
mutual block, rather than reconstructing a parallel family list. -/
theorem
    AddInductive.EnvironmentInductiveExecution.FlattenedNestedArtifact.source_headers_prefix
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    (artifact : execution.FlattenedNestedArtifact staged) :
    artifact.source.types.map VInductDecl.VInductiveType.nestedHeader <+:
      staged.source.types.map VInductDecl.VInductiveType.nestedHeader := by
  rw [← artifact.flat_eq]
  exact artifact.nested.elim.source_headers_prefix

/-- Select the flattened family at an exact original-source offset while
retaining equality of every restoration-stable header component. -/
theorem
    AddInductive.EnvironmentInductiveExecution.FlattenedNestedArtifact.flat_family_header_at
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    (artifact : execution.FlattenedNestedArtifact staged)
    {i : Nat} {sourceFamily : VInductiveType}
    (source_at : artifact.source.types[i]? = some sourceFamily) :
    ∃ flatFamily,
      staged.source.types[i]? = some flatFamily ∧
      VInductDecl.VInductiveType.nestedHeader flatFamily =
        VInductDecl.VInductiveType.nestedHeader sourceFamily := by
  obtain ⟨flatFamily, flat_at, header⟩ :=
    artifact.nested.elim.flat_family_header_at source_at
  exact ⟨flatFamily, by simpa only [artifact.flat_eq] using flat_at, header⟩

/-- Constructor offsets within an original source family select the exact
flattened producer constructor and preserve its name/universe header. -/
theorem
    AddInductive.EnvironmentInductiveExecution.FlattenedNestedArtifact.flat_constructor_header_at
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    (artifact : execution.FlattenedNestedArtifact staged)
    {familyIndex constructorIndex : Nat}
    {sourceFamily : VInductiveType} {sourceConstructor : VConstVal}
    (family_at : artifact.source.types[familyIndex]? = some sourceFamily)
    (constructor_at : sourceFamily.ctors[constructorIndex]? =
      some sourceConstructor) :
    ∃ flatFamily flatConstructor,
      staged.source.types[familyIndex]? = some flatFamily ∧
      flatFamily.ctors[constructorIndex]? = some flatConstructor ∧
      VInductDecl.VConstVal.nestedHeader flatConstructor =
        VInductDecl.VConstVal.nestedHeader sourceConstructor := by
  obtain ⟨flatFamily, flatConstructor, flat_at, constructor_at,
      header⟩ := artifact.nested.elim.flat_constructor_header_at family_at
        constructor_at
  exact ⟨flatFamily, flatConstructor,
    by simpa only [artifact.flat_eq] using flat_at, constructor_at, header⟩

/-- Select the exact normalized flattened producer for a structure-shaped
original family through the definitionally aligned nested artifact.  In this
presentation the selected generation is literally `artifact.generation` over
`staged.source`, while every restored source fact remains owned by the same
successful transformation run. -/
theorem
    AddInductive.EnvironmentInductiveExecution.FlattenedNestedArtifact.selectStructure
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    (artifact : execution.FlattenedNestedArtifact staged)
    {familyIndex : Nat} {sourceFamily : VInductiveType}
    {sourceConstructor : VConstVal}
    (source_at : artifact.source.types[familyIndex]? = some sourceFamily)
    (source_constructors_eq : sourceFamily.ctors = [sourceConstructor])
    (source_raw_indices_eq :
      VInductDecl.ctorFields
        (VExpr.dropN artifact.source.nparams sourceFamily.type) = []) :
    Nonempty (VInductDecl.NestedStructureSelection artifact.alignedNested
      familyIndex sourceFamily sourceConstructor) :=
  artifact.alignedNested.selectStructure source_at source_constructors_eq
    source_raw_indices_eq

/-- Exact Theory-side semantic restoration for the nested artifact attached
to one flattened staging owner.  Its deterministic transaction endpoint is
kept explicit so it can later be aligned with the host restoration map. -/
structure
    AddInductive.EnvironmentInductiveExecution.FlattenedNestedRestorationResult
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    (artifact : execution.FlattenedNestedArtifact staged)
    (after : VEnv) where
  nested_wf : artifact.alignedNested.WF (ves.venv .safe)
  success : (ves.venv .safe).addInductNested artifact.alignedNested = some after
  before_wf : (ves.venv .safe).WF

/-- Erase the execution-owned wrapper to the generic completed nested
certificate consumed by restored-rule transport. -/
def
    AddInductive.EnvironmentInductiveExecution.FlattenedNestedRestorationResult.certificate
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {after : VEnv}
    (restoration : execution.FlattenedNestedRestorationResult artifact after) :
    artifact.source.NestedBlockCertificate (ves.venv .safe) after where
  nested := artifact.alignedNested
  semantic := restoration.nested_wf
  success := restoration.success
  beforeWF := restoration.before_wf

/-- The exact execution-owned restoration closes every recursor-world
replacement entry.  Target-copy alignment is retained by the nested artifact,
so no projection consumer supplies a separate syntactic closure premise. -/
theorem
    AddInductive.EnvironmentInductiveExecution.FlattenedNestedRestorationResult.recEntriesClosed
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {after : VEnv}
    (restoration : execution.FlattenedNestedRestorationResult artifact after) :
    VInductDecl.RestoreEntriesClosed artifact.alignedNested.recEntries := by
  have targetsWF : VInductDecl.NestedTargetsWF (ves.venv .safe)
      artifact.alignedNested.elim.targets := by
    simpa [AddInductive.EnvironmentInductiveExecution.FlattenedNestedArtifact.alignedNested]
      using artifact.targetsWF
  exact restoration.certificate.recEntriesClosed targetsWF

/-- Pair the exact execution-owned flattened transaction with its exact
Theory nested restoration.  The flat rule endpoint is deterministic, and the
flat declaration and generation are both inherited from `artifact`; no
alignment equality is exposed to downstream certificate consumers. -/
def
    AddInductive.EnvironmentInductiveExecution.FlattenedExactRecursorStagingResult.nestedStagedCertificate
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    (result : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape)
    (metadata : VInductDecl.ExactProducedBlockMetadataPrefixRun result.run)
    {after : VEnv}
    (restoration : execution.FlattenedNestedRestorationResult artifact after) :
    artifact.source.NestedStagedCertificate (ves.venv .safe)
      (artifact.generation.generatedRules.foldl VEnv.addDefEq
        metadata.recursors.recEnv) after := by
  exact metadata.nestedStagedCertificate restoration.certificate ⟨rfl⟩

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

/-- Every host constructor metadata record retained by a recognized canonical
primitive execution carries the recognizer's zero parameter count.  This is
derived from the successful family-validation run and the exact constructor
inventory synthesized by the execution. -/
theorem AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveDeclaredConstructor_numParams
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe true fuel finalEnv)
    (primitiveResult : PrimitiveInductiveResult lparams nparams types isUnsafe
      true) {info : ConstructorVal}
    (member : info ∈
      execution.flattened.eliminationExecution.declaredConstructorInfos) :
    info.numParams = 0 := by
  have recognized := primitiveResult.recognized rfl
  obtain ⟨_, _, nparamsEq, shape⟩ := recognized
  obtain ⟨type, typesEq, _, _⟩ := shape
  have noop := execution.canonicalPrimitive_noop primitiveResult
  have nestedTypesEq : execution.nested.types = [type] :=
    noop.1.trans typesEq
  have nonempty : execution.nested.types.isEmpty = false := by
    rw [nestedTypesEq]
    rfl
  have normalizationRun :=
    execution.flattened.normalization_run execution.flattenedRun
  have sizes := execution.flattened.eliminationExecution.normalization
    |>.familyValidationResult.sizes_of_run nonempty
      (execution.flattened.eliminationExecution.normalization
        |>.familyValidationResult_run normalizationRun)
  have paramsSize :
      execution.flattened.eliminationExecution.normalization.stats.params.size =
        nparams := by
    simpa only [
      AddInductive.NormalizationCandidateExecution.familyValidationResult]
      using sizes.1
  calc
    info.numParams =
        execution.flattened.eliminationExecution.normalization.stats.params.size :=
      AddInductive.declaredConstructorInfos_numParams
        execution.flattened.eliminationExecution.normalization.stats
        execution.nested.types.toArray isUnsafe
        execution.flattened.eliminationExecution.constructorContext member
    _ = nparams := paramsSize
    _ = 0 := nparamsEq

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveDeclaredConstructor_numParams' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.abstract_eq]
-/
#guard_msgs in
#print axioms AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveDeclaredConstructor_numParams

/-- Every retained constructor metadata record in a recognized primitive
execution names the sole canonical Bool/Nat family as its owner. -/
theorem AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveDeclaredConstructor_induct
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe true fuel finalEnv)
    (primitiveResult : PrimitiveInductiveResult lparams nparams types isUnsafe
      true) {info : ConstructorVal}
    (member : info ∈
      execution.flattened.eliminationExecution.declaredConstructorInfos) :
    ∃ raw ∈ (VPrimitiveInductive.canonicalDecl types).blockTypeConstants,
      info.induct = raw.name := by
  obtain ⟨source, sourceMember, owner⟩ :=
    AddInductive.declaredConstructorInfos_induct
      execution.flattened.eliminationExecution.normalization.stats
      execution.nested.types.toArray isUnsafe
      execution.flattened.eliminationExecution.constructorContext member
  have recognized := primitiveResult.recognized rfl
  obtain ⟨_, _, _, shape⟩ := recognized
  obtain ⟨type, typesEq, _, primitive⟩ := shape
  have noop := execution.canonicalPrimitive_noop primitiveResult
  have nestedTypesEq : execution.nested.types = [type] :=
    noop.1.trans typesEq
  have sourceEq : source = type := by
    simpa only [List.toList_toArray, nestedTypesEq, List.mem_singleton] using
      sourceMember
  subst source
  cases primitive with
  | inl boolShape =>
      obtain ⟨typeName, _constructorsEq⟩ := boolShape
      refine ⟨VPrimitiveInductive.boolType.toVConstVal, ?_, ?_⟩
      · simp [VPrimitiveInductive.canonicalDecl, typesEq, typeName,
          VInductDecl.blockTypeConstants, VPrimitiveInductive.boolDecl]
      · simpa [VPrimitiveInductive.boolType] using owner.trans typeName
  | inr natShape =>
      obtain ⟨typeName, _, _, _constructorsEq⟩ := natShape
      refine ⟨VPrimitiveInductive.natType.toVConstVal, ?_, ?_⟩
      · simp [VPrimitiveInductive.canonicalDecl, typesEq, typeName,
          VInductDecl.blockTypeConstants, VPrimitiveInductive.natDecl]
      · simpa [VPrimitiveInductive.natType] using owner.trans typeName

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveDeclaredConstructor_induct' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.abstract_eq]
-/
#guard_msgs in
#print axioms AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveDeclaredConstructor_induct

/-- Every family metadata record retained by a recognized canonical primitive
execution has exactly the two Bool/Nat constructors fixed by the recognizer.
This fact is extracted from the validator's source-aligned metadata relation,
not reconstructed from the final environment map. -/
theorem AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveDeclaredInfo_ctors_length
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe true fuel finalEnv)
    (primitiveResult : PrimitiveInductiveResult lparams nparams types isUnsafe
      true) {info : InductiveVal}
    (member : info ∈
      execution.flattened.eliminationExecution.normalization.declaredInfos) :
    info.ctors.length = 2 := by
  have recognized := primitiveResult.recognized rfl
  obtain ⟨_, _, _, shape⟩ := recognized
  obtain ⟨type, typesEq, _, primitive⟩ := shape
  have noop := execution.canonicalPrimitive_noop primitiveResult
  have nestedTypesEq : execution.nested.types = [type] :=
    noop.1.trans typesEq
  have nonempty : execution.nested.types.isEmpty = false := by
    rw [nestedTypesEq]
    rfl
  have normalizationRun :=
    execution.flattened.normalization_run execution.flattenedRun
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
  obtain ⟨source, sourceMember, numIndices, infoEq⟩ :=
    Lean4Lean.List.Forall₂.forall_exists_r metadata info member
  have sourceEq : source = type := by
    rw [nestedTypesEq] at sourceMember
    simpa using sourceMember
  subst source
  rw [infoEq]
  unfold AddInductive.declaredInductiveInfo
  cases primitive with
  | inl boolShape =>
      obtain ⟨_, constructorsEq⟩ := boolShape
      simp [constructorsEq]
  | inr natShape =>
      obtain ⟨_, _, _, constructorsEq⟩ := natShape
      simp [constructorsEq]

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveDeclaredInfo_ctors_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.abstract_eq]
-/
#guard_msgs in
#print axioms AddInductive.EnvironmentInductiveExecution.canonicalPrimitiveDeclaredInfo_ctors_length

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
  | mk inputCheck _uniformityCheck nested nestedRun flattened flattenedRun completion =>
      cases completion with
      | ordinary _ => rfl
      | nested numNested_ne restoration restorationRun =>
          exact (numNested_ne numNested_eq).elim

/-- Select the exact host restoration object already retained by a genuinely
nested outer execution.  This removes restoration choice from all later
semantic staging interfaces. -/
noncomputable def
    AddInductive.EnvironmentInductiveExecution.selectedNestedRestoration
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv)
    (numNested_ne : execution.nested.aux2nested.size ≠ 0) :
    NestedRestorationResult execution.nested
      execution.flattened.recursors.env env types false .safe lparams {} :=
  Classical.choose (execution.restoration_of_numNested_ne numNested_ne)

/-- The selected restoration is the result of the actual restoration
program, not merely an extensionally matching inventory. -/
theorem
    AddInductive.EnvironmentInductiveExecution.selectedNestedRestoration_run
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv)
    (numNested_ne : execution.nested.aux2nested.size ≠ 0) :
    restoreNestedEnvironment execution.nested
        execution.flattened.recursors.env env types false .safe lparams {} =
      .ok (execution.selectedNestedRestoration numNested_ne) :=
  (Classical.choose_spec
    (execution.restoration_of_numNested_ne numNested_ne)).1

/-- The selected restoration's host endpoint is exactly the public final
environment of the retained outer execution. -/
theorem
    AddInductive.EnvironmentInductiveExecution.selectedNestedRestoration_finalEnv_eq
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv)
    (numNested_ne : execution.nested.aux2nested.size ≠ 0) :
    finalEnv = (execution.selectedNestedRestoration numNested_ne).env :=
  (Classical.choose_spec
    (execution.restoration_of_numNested_ne numNested_ne)).2

/-- A lookup that is fresh in the input but present after nonprimitive nested
restoration must come from the restoration inventory, whose declaration trace
has already checked both primitive-name side conditions. -/
theorem NestedRestorationResult.name_not_primitive_of_fresh_lookup
    {res : ElimNestedInductive.Result}
    {flatEnv initialEnv : Environment} {types : List InductiveType}
    {safety : DefinitionSafety} {lparams : List Name} {fuel : FuelConfig}
    (restoration : NestedRestorationResult res flatEnv initialEnv types false
      safety lparams fuel)
    (inputMapWF : initialEnv.constants.WF)
    {name : Name} {info : ConstantInfo}
    (inputFresh : initialEnv.constants.find? name = none)
    (restoredLookup : restoration.env.constants.find? name = some info) :
    name ∉ VEnv.reflectedPrimitiveNames ∧
      Environment.primitives.contains name = false := by
  rcases restoration.trace.map_lookup_cases inputMapWF restoredLookup with
    old | inserted
  · rw [inputFresh] at old
    contradiction
  · have names := restoration.trace.names_not_primitive info inserted.1
    simpa only [inserted.2] using names

/-- Restored family, constructor, and recursor metadata staging against the
actual host restoration object selected by a genuinely nested outer
execution.  This is the nested analogue of the exact flattened metadata
prefix: only the restored constant translations and K correspondence remain;
the restored rule endpoint is deterministic. -/
structure
    AddInductive.EnvironmentInductiveExecution.FlattenedNestedRestoredMetadataPrefixRun
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {after : VEnv}
    (restoration : execution.FlattenedNestedRestorationResult artifact after)
    (numNested_ne : execution.nested.aux2nested.size ≠ 0) where
  typeMap : ConstMap
  typeEnv : VEnv
  ctorMap : ConstMap
  ctorEnv : VEnv
  recEnv : VEnv
  addTypes : AddInductConstants .induct env.constants (ves.venv .safe)
    artifact.source.blockTypeConstants typeMap typeEnv
  addCtors : AddInductConstants .ctor typeMap typeEnv
    artifact.source.blockConstructorConstants ctorMap ctorEnv
  addRecs : AddInductConstants .recursor ctorMap ctorEnv
    artifact.alignedNested.recursors
    (execution.selectedNestedRestoration numNested_ne).env.constants recEnv
  recK : RecursorMapKMatches
    (execution.selectedNestedRestoration numNested_ne).env.constants
    artifact.alignedNested.recursors artifact.generation.kTarget

/-- Complete the actual restored metadata prefix with its deterministic rule
fold.  Uniqueness of `addInductNested` identifies that fold with the semantic
restoration endpoint, while the retained outer completion identifies the host
map with `finalEnv.constants`. -/
def
    AddInductive.EnvironmentInductiveExecution.FlattenedNestedRestoredMetadataPrefixRun.addInductNestedTrace
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {after : VEnv}
    {restoration : execution.FlattenedNestedRestorationResult artifact after}
    {numNested_ne : execution.nested.aux2nested.size ≠ 0}
    (restoredMetadata : execution.FlattenedNestedRestoredMetadataPrefixRun restoration
      numNested_ne) :
    AddInductNestedTrace env.constants (ves.venv .safe) artifact.source
      finalEnv.constants after := by
  let deterministic := artifact.alignedNested.generatedRules.foldl
    VEnv.addDefEq restoredMetadata.recEnv
  let hostTrace : AddInductNestedTrace env.constants (ves.venv .safe)
      artifact.source
      (execution.selectedNestedRestoration numNested_ne).env.constants
      deterministic := {
    nested := artifact.alignedNested
    nested_wf := restoration.nested_wf
    typeMap := restoredMetadata.typeMap
    typeEnv := restoredMetadata.typeEnv
    ctorMap := restoredMetadata.ctorMap
    ctorEnv := restoredMetadata.ctorEnv
    recEnv := restoredMetadata.recEnv
    addTypes := restoredMetadata.addTypes
    addCtors := restoredMetadata.addCtors
    addRecs := restoredMetadata.addRecs
    recK := restoredMetadata.recK
    addRules := ⟨rfl⟩ }
  have after_eq : after = deterministic := Option.some.inj
    (restoration.success.symm.trans hostTrace.to_addInductNested)
  rw [after_eq]
  have finalEnv_eq :=
    execution.selectedNestedRestoration_finalEnv_eq numNested_ne
  simpa only [finalEnv_eq] using hostTrace

/-- Complete dependent owner for both sides of a genuine nested transaction:
the exact flattened generation is retained beside the paired Theory
restoration certificate, while the restored metadata prefix produces a trace
whose host endpoint is the actual public restoration map. -/
structure
    AddInductive.EnvironmentInductiveExecution.FlattenedExactNestedTransactionResult
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    (flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape)
    (metadata : VInductDecl.ExactProducedBlockMetadataPrefixRun flat.run)
    {after : VEnv}
    (restoration : execution.FlattenedNestedRestorationResult artifact after)
    (numNested_ne : execution.nested.aux2nested.size ≠ 0)
    (restoredMetadata :
      execution.FlattenedNestedRestoredMetadataPrefixRun restoration
        numNested_ne) where
  stagedCertificate : artifact.source.NestedStagedCertificate
    (ves.venv .safe)
    (artifact.generation.generatedRules.foldl VEnv.addDefEq
      metadata.recursors.recEnv) after
  stagedCertificate_nested_eq :
    stagedCertificate.restored.nested = artifact.alignedNested
  safeTrace : AddInductNestedTrace env.constants (ves.venv .safe)
    artifact.source finalEnv.constants after

/-- Assemble the paired flat/restored certificate and the exact safe nested
trace from their two execution-indexed metadata prefixes. -/
def
    AddInductive.EnvironmentInductiveExecution.FlattenedExactRecursorStagingResult.nestedTransaction
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    (flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape)
    (metadata : VInductDecl.ExactProducedBlockMetadataPrefixRun flat.run)
    {after : VEnv}
    (restoration : execution.FlattenedNestedRestorationResult artifact after)
    (numNested_ne : execution.nested.aux2nested.size ≠ 0)
    (restoredMetadata :
      execution.FlattenedNestedRestoredMetadataPrefixRun restoration
        numNested_ne) :
    execution.FlattenedExactNestedTransactionResult flat metadata restoration
      numNested_ne restoredMetadata where
  stagedCertificate := flat.nestedStagedCertificate metadata restoration
  stagedCertificate_nested_eq := rfl
  safeTrace := restoredMetadata.addInductNestedTrace

/-- The exact nested transaction owns the sound canonical interpretation
from its common dependency model into its restored endpoint.  Target-copy
well-formedness comes from the aligned nested artifact itself, so consumers
do not reselect a restoration inventory or supply an interpretation witness.

This deliberately starts at the dependency boundary, not at the completed
flattened environment: generated flattened constants and rules require their
own operational restoration argument. -/
theorem
    AddInductive.EnvironmentInductiveExecution.FlattenedExactNestedTransactionResult.restoreInterpBeforeConstInterp
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    {flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape}
    {metadata : VInductDecl.ExactProducedBlockMetadataPrefixRun flat.run}
    {after : VEnv}
    {restoration : execution.FlattenedNestedRestorationResult artifact after}
    {numNested_ne : execution.nested.aux2nested.size ≠ 0}
    {restoredMetadata :
      execution.FlattenedNestedRestoredMetadataPrefixRun restoration
        numNested_ne}
    (transaction : execution.FlattenedExactNestedTransactionResult flat
      metadata restoration numNested_ne restoredMetadata) :
    VEnv.ConstInterp (ves.venv .safe) after
      artifact.alignedNested.restoreInterp := by
  have targetsWF : VInductDecl.NestedTargetsWF (ves.venv .safe)
      transaction.stagedCertificate.restored.nested.elim.targets := by
    rw [transaction.stagedCertificate_nested_eq, artifact.alignedNested_eq]
    exact artifact.targetsWF
  have transported :=
    transaction.stagedCertificate.restoreInterp_beforeConstInterp targetsWF
  rw [transaction.stagedCertificate_nested_eq] at transported
  exact transported

/-- The exact family fold and the actual nonprimitive restoration trace imply
    the primitive-name side conditions for every restored source family. -/
theorem
    AddInductive.EnvironmentInductiveExecution.FlattenedExactNestedTransactionResult.typeNames
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    {flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape}
    {metadata : VInductDecl.ExactProducedBlockMetadataPrefixRun flat.run}
    {after : VEnv}
    {restoration : execution.FlattenedNestedRestorationResult artifact after}
    {numNested_ne : execution.nested.aux2nested.size ≠ 0}
    {restoredMetadata :
      execution.FlattenedNestedRestoredMetadataPrefixRun restoration
        numNested_ne}
    (transaction : execution.FlattenedExactNestedTransactionResult flat
      metadata restoration numNested_ne restoredMetadata)
    (wf : ves.WF env) :
    ∀ ci ∈ artifact.source.blockTypeConstants,
      ci.name ∉ VEnv.reflectedPrimitiveNames ∧
        Environment.primitives.contains ci.name = false := by
  intro ci member
  have inputMapWF := (wf.tr (safety := .safe)).map_wf
  have typeMapWF := transaction.safeTrace.addTypes.map_wf inputMapWF
  have ctorMapWF := transaction.safeTrace.addCtors.map_wf typeMapWF
  obtain ⟨info, typeLookup, _, _⟩ :=
    transaction.safeTrace.addTypes.translated_lookup inputMapWF member
  have constructorLookup := transaction.safeTrace.addCtors.preserve_map_lookup
    typeMapWF typeLookup
  have finalLookup := transaction.safeTrace.addRecs.preserve_map_lookup
    ctorMapWF constructorLookup
  have restoredLookup :
      (execution.selectedNestedRestoration numNested_ne).env.constants.find?
        ci.name = some info := by
    simpa only [execution.selectedNestedRestoration_finalEnv_eq numNested_ne]
      using finalLookup
  exact (execution.selectedNestedRestoration numNested_ne)
    |>.name_not_primitive_of_fresh_lookup inputMapWF
      (transaction.safeTrace.addTypes.map_fresh inputMapWF member)
      restoredLookup

/-- Constructor-name avoidance is likewise forced by the constructor fold;
lookup preservation transports its evidence through the recursor fold and
backward freshness transports absence to the original host map. -/
theorem
    AddInductive.EnvironmentInductiveExecution.FlattenedExactNestedTransactionResult.ctorNames
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    {flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape}
    {metadata : VInductDecl.ExactProducedBlockMetadataPrefixRun flat.run}
    {after : VEnv}
    {restoration : execution.FlattenedNestedRestorationResult artifact after}
    {numNested_ne : execution.nested.aux2nested.size ≠ 0}
    {restoredMetadata :
      execution.FlattenedNestedRestoredMetadataPrefixRun restoration
        numNested_ne}
    (transaction : execution.FlattenedExactNestedTransactionResult flat
      metadata restoration numNested_ne restoredMetadata)
    (wf : ves.WF env) :
    ∀ ci ∈ artifact.source.blockConstructorConstants,
      ci.name ∉ VEnv.reflectedPrimitiveNames ∧
        Environment.primitives.contains ci.name = false := by
  intro ci member
  have inputMapWF := (wf.tr (safety := .safe)).map_wf
  have typeMapWF := transaction.safeTrace.addTypes.map_wf inputMapWF
  have ctorMapWF := transaction.safeTrace.addCtors.map_wf typeMapWF
  obtain ⟨info, constructorLookup, _, _⟩ :=
    transaction.safeTrace.addCtors.translated_lookup typeMapWF member
  have finalLookup := transaction.safeTrace.addRecs.preserve_map_lookup
    ctorMapWF constructorLookup
  have typeMapFresh := transaction.safeTrace.addCtors.map_fresh
    typeMapWF member
  have inputFresh :=
    transaction.safeTrace.addTypes.input_map_none_of_output_none inputMapWF
      typeMapFresh
  have restoredLookup :
      (execution.selectedNestedRestoration numNested_ne).env.constants.find?
        ci.name = some info := by
    simpa only [execution.selectedNestedRestoration_finalEnv_eq numNested_ne]
      using finalLookup
  exact (execution.selectedNestedRestoration numNested_ne)
    |>.name_not_primitive_of_fresh_lookup inputMapWF inputFresh restoredLookup

/-- Recursor-name avoidance is forced by the final exact metadata fold and
transported back through both earlier folds before consulting the actual
nonprimitive restoration trace. -/
theorem
    AddInductive.EnvironmentInductiveExecution.FlattenedExactNestedTransactionResult.recNames
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    {flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape}
    {metadata : VInductDecl.ExactProducedBlockMetadataPrefixRun flat.run}
    {after : VEnv}
    {restoration : execution.FlattenedNestedRestorationResult artifact after}
    {numNested_ne : execution.nested.aux2nested.size ≠ 0}
    {restoredMetadata :
      execution.FlattenedNestedRestoredMetadataPrefixRun restoration
        numNested_ne}
    (transaction : execution.FlattenedExactNestedTransactionResult flat
      metadata restoration numNested_ne restoredMetadata)
    (wf : ves.WF env) :
    ∀ ci ∈ transaction.safeTrace.nested.recursors,
      ci.name ∉ VEnv.reflectedPrimitiveNames ∧
        Environment.primitives.contains ci.name = false := by
  intro ci member
  have inputMapWF := (wf.tr (safety := .safe)).map_wf
  have typeMapWF := transaction.safeTrace.addTypes.map_wf inputMapWF
  have ctorMapWF := transaction.safeTrace.addCtors.map_wf typeMapWF
  obtain ⟨info, finalLookup, _, _⟩ :=
    transaction.safeTrace.addRecs.translated_lookup ctorMapWF member
  have ctorMapFresh := transaction.safeTrace.addRecs.map_fresh
    ctorMapWF member
  have typeMapFresh :=
    transaction.safeTrace.addCtors.input_map_none_of_output_none typeMapWF
      ctorMapFresh
  have inputFresh :=
    transaction.safeTrace.addTypes.input_map_none_of_output_none inputMapWF
      typeMapFresh
  have restoredLookup :
      (execution.selectedNestedRestoration numNested_ne).env.constants.find?
        ci.name = some info := by
    simpa only [execution.selectedNestedRestoration_finalEnv_eq numNested_ne]
      using finalLookup
  exact (execution.selectedNestedRestoration numNested_ne)
    |>.name_not_primitive_of_fresh_lookup inputMapWF inputFresh restoredLookup

/-- Replay the exact safe nested trace coherently at every safety level.  The
source, restoration artifact, endpoints, rule fold, and all primitive-name
side conditions are fixed by the dependent transaction above. -/
noncomputable def
    AddInductive.EnvironmentInductiveExecution.FlattenedExactNestedTransactionResult.safeReplay
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    {flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape}
    {metadata : VInductDecl.ExactProducedBlockMetadataPrefixRun flat.run}
    {after : VEnv}
    {restoration : execution.FlattenedNestedRestorationResult artifact after}
    {numNested_ne : execution.nested.aux2nested.size ≠ 0}
    {restoredMetadata :
      execution.FlattenedNestedRestoredMetadataPrefixRun restoration
        numNested_ne}
    (transaction : execution.FlattenedExactNestedTransactionResult flat
      metadata restoration numNested_ne restoredMetadata)
    (wf : ves.WF env) :
    CoherentPrimitivePreservingTransactions.SafeReplay execution
      artifact.source ves after :=
  CoherentPrimitivePreservingTransactions.ofNestedSafeTrace wf numNested_ne
    transaction.safeTrace (transaction.typeNames wf)
      (transaction.ctorNames wf) (transaction.recNames wf)

/-- In the ordinary branch, reindexing the retained recursor execution onto
the enriched Theory source does not change its host-environment endpoint. -/
theorem
    AddInductive.EnvironmentInductiveExecution.FlattenedEnrichedStagingResult.recursorEnv_eq_final
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    (staged : execution.FlattenedEnrichedStagingResult ves)
    (shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true)
    (numNested_eq : execution.nested.aux2nested.size = 0) :
    (staged.recursorShape shape).execution.recursors.env = finalEnv := by
  cases staged with
  | mk family enriched =>
      cases family with
      | mk familyDecl nparams_eq familyStaging =>
          cases familyDecl with
          | mk uvars familyNparams familyTypes =>
              simp only at nparams_eq
              subst familyNparams
              exact execution.flattenedEnv_eq_final numNested_eq

namespace AddInductive.EnvironmentInductiveExecution

/-- Close the ordinary exact transaction with its deterministic generated-rule
fold.  The trace starts at the public input constant map and ends at the public
host environment selected by the outer execution; no rule-output environment
remains caller chosen. -/
def FlattenedExactRecursorStagingResult.ordinaryAddInductBlockTrace
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {generation : VInductDecl.BlockGenerationChecked staged.source}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    (result : execution.FlattenedExactRecursorStagingResult staged generation
      shape)
    (metadata : VInductDecl.ExactProducedBlockMetadataPrefixRun result.run)
    (numNested_eq : execution.nested.aux2nested.size = 0) :
    AddInductBlockTrace env.constants (ves.venv .safe) staged.source
      finalEnv.constants
      (generation.generatedRules.foldl VEnv.addDefEq
        metadata.recursors.recEnv) := by
  let trace := metadata.addInductBlockTrace
    (env₂ := generation.generatedRules.foldl VEnv.addDefEq
      metadata.recursors.recEnv) ⟨rfl⟩
  have initialEnvEq :=
    (staged.recursorStaging shape).validation_env_eq
  have finalEnvEq := staged.recursorEnv_eq_final shape numNested_eq
  have traceGenerationEq : trace.generation = generation := by
    rfl
  exact {
    generation := generation
    blockEnv := trace.blockEnv
    generation_wf := by
      simpa only [traceGenerationEq] using trace.generation_wf
    typeMap := trace.typeMap
    typeEnv := trace.typeEnv
    ctorMap := trace.ctorMap
    ctorEnv := trace.ctorEnv
    recEnv := trace.recEnv
    addTypes := by
      simpa only [initialEnvEq, AddInductive.Context.forInductive] using
        trace.addTypes
    addCtors := trace.addCtors
    addRecs := by
      simpa only [finalEnvEq, traceGenerationEq] using trace.addRecs
    recK := by
      simpa only [finalEnvEq, traceGenerationEq] using trace.recK
    addRules := by
      simpa only [traceGenerationEq] using trace.addRules }

/-- Every family name in the exact ordinary Theory source inherits the
nonprimitive name checks performed by the retained host family declaration
trace. -/
theorem FlattenedExactRecursorStagingResult.ordinaryTypeNames
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {generation : VInductDecl.BlockGenerationChecked staged.source}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    (result : execution.FlattenedExactRecursorStagingResult staged generation
      shape)
    (metadata : VInductDecl.ExactProducedBlockMetadataPrefixRun result.run)
    (wf : ves.WF env) :
    ∀ ci ∈ staged.source.blockTypeConstants,
      ci.name ∉ VEnv.reflectedPrimitiveNames ∧
        Environment.primitives.contains ci.name = false := by
  have inputMapWF := (wf.tr (safety := .safe)).map_wf
  have initialEnvEq :=
    (staged.recursorStaging shape).validation_env_eq
  have validationMapWF :
      (staged.recursorShape shape).execution.eliminationExecution.normalization.validationContext.env.constants.WF := by
    simpa only [initialEnvEq, AddInductive.Context.forInductive] using
      inputMapWF
  have allowPrimitiveEq :
      (staged.recursorShape shape).execution.eliminationExecution.normalization.validationContext.allowPrimitive =
        false := staged.recursorShape_validationAllowPrimitive_eq shape
  exact metadata.declarations.families.raw_names_not_primitive
    allowPrimitiveEq validationMapWF

/-- Every constructor name in the exact ordinary Theory source inherits the
nonprimitive name checks performed by the retained host constructor trace. -/
theorem FlattenedExactRecursorStagingResult.ordinaryCtorNames
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {generation : VInductDecl.BlockGenerationChecked staged.source}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    (result : execution.FlattenedExactRecursorStagingResult staged generation
      shape)
    (metadata : VInductDecl.ExactProducedBlockMetadataPrefixRun result.run)
    (wf : ves.WF env) :
    ∀ ci ∈ staged.source.blockConstructorConstants,
      ci.name ∉ VEnv.reflectedPrimitiveNames ∧
        Environment.primitives.contains ci.name = false := by
  have inputMapWF := (wf.tr (safety := .safe)).map_wf
  have initialEnvEq :=
    (staged.recursorStaging shape).validation_env_eq
  have validationMapWF :
      (staged.recursorShape shape).execution.eliminationExecution.normalization.validationContext.env.constants.WF := by
    simpa only [initialEnvEq, AddInductive.Context.forInductive] using
      inputMapWF
  have familyMapWF :=
    metadata.declarations.families.kernelTrace.map_wf validationMapWF
  have allowPrimitiveEq :
      (staged.recursorShape shape).execution.eliminationExecution.constructorContext.allowPrimitive =
        false := by
    simpa only [AddInductive.NormalizationEliminationExecution.constructorContext]
      using staged.recursorShape_validationAllowPrimitive_eq shape
  exact metadata.declarations.constructors.raw_names_not_primitive
    allowPrimitiveEq familyMapWF

/-- Every generated recursor name in the exact ordinary transaction inherits
the nonprimitive name checks performed by the retained host recursor trace. -/
theorem FlattenedExactRecursorStagingResult.ordinaryRecNames
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {generation : VInductDecl.BlockGenerationChecked staged.source}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    (result : execution.FlattenedExactRecursorStagingResult staged generation
      shape)
    (metadata : VInductDecl.ExactProducedBlockMetadataPrefixRun result.run)
    (wf : ves.WF env) :
    ∀ ci ∈ generation.recursors,
      ci.name ∉ VEnv.reflectedPrimitiveNames ∧
        Environment.primitives.contains ci.name = false := by
  have inputMapWF := (wf.tr (safety := .safe)).map_wf
  have initialEnvEq :=
    (staged.recursorStaging shape).validation_env_eq
  have validationMapWF :
      (staged.recursorShape shape).execution.eliminationExecution.normalization.validationContext.env.constants.WF := by
    simpa only [initialEnvEq, AddInductive.Context.forInductive] using
      inputMapWF
  have familyMapWF :=
    metadata.declarations.families.kernelTrace.map_wf validationMapWF
  have constructorMapWF :=
    metadata.declarations.constructors.kernelTrace.map_wf familyMapWF
  have allowPrimitiveEq :
      (staged.recursorShape shape).execution.recursors.allowPrimitive =
        false := by
    exact (staged.recursorShape shape).execution.recursor_allowPrimitive_eq.trans
      (staged.recursorShape_validationAllowPrimitive_eq shape)
  have recursorInitialMapWF :
      (staged.recursorShape shape).execution.recursors.initialEnv.constants.WF := by
    rw [(staged.recursorShape shape).execution.recursor_initialEnv_eq]
    exact constructorMapWF
  exact metadata.recursors.raw_names_not_primitive allowPrimitiveEq
    recursorInitialMapWF

/-- Replay the exact ordinary safe transaction coherently at every safety
level.  The retained host declaration traces now supply every primitive-name
condition, so input `VEnvs.WF` is the only replay premise. -/
def FlattenedExactRecursorStagingResult.ordinarySafeReplay
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {generation : VInductDecl.BlockGenerationChecked staged.source}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    (result : execution.FlattenedExactRecursorStagingResult staged generation
      shape)
    (metadata : VInductDecl.ExactProducedBlockMetadataPrefixRun result.run)
    (numNested_eq : execution.nested.aux2nested.size = 0)
    (wf : ves.WF env) :
    CoherentPrimitivePreservingTransactions.SafeReplay execution
      staged.source ves
      (generation.generatedRules.foldl VEnv.addDefEq
        metadata.recursors.recEnv) := by
  let trace := result.ordinaryAddInductBlockTrace metadata numNested_eq
  apply CoherentPrimitivePreservingTransactions.ofOrdinarySafeTrace wf
    numNested_eq trace (result.ordinaryTypeNames metadata wf)
      (result.ordinaryCtorNames metadata wf)
  intro ci member
  apply result.ordinaryRecNames metadata wf ci
  exact member

/-- Retarget the canonical semantic transaction from its producer-owned
validation/recursor endpoints to the public input and final host maps of the
ordinary outer execution. -/
def
    FlattenedSemanticRecursorStagingResult.ordinaryAddInductBlockTrace
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    (result : execution.FlattenedSemanticRecursorStagingResult staged shape)
    (metadata : VInductDecl.ProducedBlockSemanticMetadataPrefixRun
      (staged.recursorShape shape) result.semantic result.generation
      result.run)
    (numNested_eq : execution.nested.aux2nested.size = 0) :
    AddInductBlockTrace env.constants (ves.venv .safe) staged.source
      finalEnv.constants
      (result.generation.generatedRules.foldl VEnv.addDefEq
        metadata.recursors.recEnv) := by
  let trace := metadata.addInductBlockTrace
  have initialEnvEq :=
    (staged.recursorStaging shape).validation_env_eq
  have finalEnvEq := staged.recursorEnv_eq_final shape numNested_eq
  have traceGenerationEq : trace.generation = result.generation := by
    rfl
  exact {
    generation := result.generation
    blockEnv := trace.blockEnv
    generation_wf := by
      simpa only [traceGenerationEq] using trace.generation_wf
    typeMap := trace.typeMap
    typeEnv := trace.typeEnv
    ctorMap := trace.ctorMap
    ctorEnv := trace.ctorEnv
    recEnv := trace.recEnv
    addTypes := by
      simpa only [initialEnvEq, AddInductive.Context.forInductive] using
        trace.addTypes
    addCtors := trace.addCtors
    addRecs := by
      simpa only [finalEnvEq, traceGenerationEq] using trace.addRecs
    recK := by
      simpa only [finalEnvEq, traceGenerationEq] using trace.recK
    addRules := by
      simpa only [traceGenerationEq] using trace.addRules }

/-- The semantic transaction inherits the exact nonprimitive family-name
checks from its retained host declaration fold. -/
theorem FlattenedSemanticRecursorStagingResult.ordinaryTypeNames
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    (result : execution.FlattenedSemanticRecursorStagingResult staged shape)
    (metadata : VInductDecl.ProducedBlockSemanticMetadataPrefixRun
      (staged.recursorShape shape) result.semantic result.generation
      result.run)
    (wf : ves.WF env) :
    ∀ ci ∈ staged.source.blockTypeConstants,
      ci.name ∉ VEnv.reflectedPrimitiveNames ∧
        Environment.primitives.contains ci.name = false := by
  have inputMapWF := (wf.tr (safety := .safe)).map_wf
  have initialEnvEq :=
    (staged.recursorStaging shape).validation_env_eq
  have validationMapWF :
      (staged.recursorShape shape).execution.eliminationExecution.normalization.validationContext.env.constants.WF := by
    simpa only [initialEnvEq, AddInductive.Context.forInductive] using
      inputMapWF
  have allowPrimitiveEq :
      (staged.recursorShape shape).execution.eliminationExecution.normalization.validationContext.allowPrimitive =
        false := staged.recursorShape_validationAllowPrimitive_eq shape
  exact metadata.declarations.families.raw_names_not_primitive
    allowPrimitiveEq validationMapWF

/-- The semantic transaction inherits the exact nonprimitive constructor-name
checks from its retained host declaration fold. -/
theorem FlattenedSemanticRecursorStagingResult.ordinaryCtorNames
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    (result : execution.FlattenedSemanticRecursorStagingResult staged shape)
    (metadata : VInductDecl.ProducedBlockSemanticMetadataPrefixRun
      (staged.recursorShape shape) result.semantic result.generation
      result.run)
    (wf : ves.WF env) :
    ∀ ci ∈ staged.source.blockConstructorConstants,
      ci.name ∉ VEnv.reflectedPrimitiveNames ∧
        Environment.primitives.contains ci.name = false := by
  have inputMapWF := (wf.tr (safety := .safe)).map_wf
  have initialEnvEq :=
    (staged.recursorStaging shape).validation_env_eq
  have validationMapWF :
      (staged.recursorShape shape).execution.eliminationExecution.normalization.validationContext.env.constants.WF := by
    simpa only [initialEnvEq, AddInductive.Context.forInductive] using
      inputMapWF
  have familyMapWF :=
    metadata.declarations.families.kernelTrace.map_wf validationMapWF
  have allowPrimitiveEq :
      (staged.recursorShape shape).execution.eliminationExecution.constructorContext.allowPrimitive =
        false := by
    simpa only [AddInductive.NormalizationEliminationExecution.constructorContext]
      using staged.recursorShape_validationAllowPrimitive_eq shape
  exact metadata.declarations.constructors.raw_names_not_primitive
    allowPrimitiveEq familyMapWF

/-- The semantic transaction inherits the exact nonprimitive recursor-name
checks from its retained host declaration fold. -/
theorem FlattenedSemanticRecursorStagingResult.ordinaryRecNames
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    (result : execution.FlattenedSemanticRecursorStagingResult staged shape)
    (metadata : VInductDecl.ProducedBlockSemanticMetadataPrefixRun
      (staged.recursorShape shape) result.semantic result.generation
      result.run)
    (wf : ves.WF env) :
    ∀ ci ∈ result.generation.recursors,
      ci.name ∉ VEnv.reflectedPrimitiveNames ∧
        Environment.primitives.contains ci.name = false := by
  have inputMapWF := (wf.tr (safety := .safe)).map_wf
  have initialEnvEq :=
    (staged.recursorStaging shape).validation_env_eq
  have validationMapWF :
      (staged.recursorShape shape).execution.eliminationExecution.normalization.validationContext.env.constants.WF := by
    simpa only [initialEnvEq, AddInductive.Context.forInductive] using
      inputMapWF
  have familyMapWF :=
    metadata.declarations.families.kernelTrace.map_wf validationMapWF
  have constructorMapWF :=
    metadata.declarations.constructors.kernelTrace.map_wf familyMapWF
  have allowPrimitiveEq :
      (staged.recursorShape shape).execution.recursors.allowPrimitive =
        false := by
    exact (staged.recursorShape shape).execution.recursor_allowPrimitive_eq.trans
      (staged.recursorShape_validationAllowPrimitive_eq shape)
  have recursorInitialMapWF :
      (staged.recursorShape shape).execution.recursors.initialEnv.constants.WF := by
    rw [(staged.recursorShape shape).execution.recursor_initialEnv_eq]
    exact constructorMapWF
  exact metadata.recursors.raw_names_not_primitive allowPrimitiveEq
    recursorInitialMapWF

/-- Replay the canonical semantic ordinary transaction coherently at every
safety level.  All source, generation, metadata, endpoint, and primitive-name
choices are projections of the retained dependent result. -/
def FlattenedSemanticRecursorStagingResult.ordinarySafeReplay
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    (result : execution.FlattenedSemanticRecursorStagingResult staged shape)
    (metadata : VInductDecl.ProducedBlockSemanticMetadataPrefixRun
      (staged.recursorShape shape) result.semantic result.generation
      result.run)
    (numNested_eq : execution.nested.aux2nested.size = 0)
    (wf : ves.WF env) :
    CoherentPrimitivePreservingTransactions.SafeReplay execution
      staged.source ves
      (result.generation.generatedRules.foldl VEnv.addDefEq
        metadata.recursors.recEnv) := by
  let trace := result.ordinaryAddInductBlockTrace metadata numNested_eq
  apply CoherentPrimitivePreservingTransactions.ofOrdinarySafeTrace wf
    numNested_eq trace (result.ordinaryTypeNames metadata wf)
      (result.ordinaryCtorNames metadata wf)
  intro ci member
  exact result.ordinaryRecNames metadata wf ci member

/-- The retained flattened family, constructor, and recursor folds preserve
constant-map well-formedness at their exact internal endpoint. -/
theorem flattenedFinalMapWF
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv)
    (inputMapWF : env.constants.WF) :
    execution.flattened.recursors.env.constants.WF := by
  have validationMapWF :
      execution.flattened.eliminationExecution.normalization.validationContext.env.constants.WF := by
    simpa only [execution.flattenedValidationEnv_eq] using inputMapWF
  have familyMapWF :=
    execution.flattened.eliminationExecution.normalization.declareTrace.map_wf
      validationMapWF
  have constructorMapWF :=
    execution.flattened.eliminationExecution.declareConstructorTrace.map_wf
      familyMapWF
  have recursorInitialMapWF :
      execution.flattened.recursors.initialEnv.constants.WF := by
    simpa only [execution.flattened.recursor_initialEnv_eq] using
      constructorMapWF
  have recursorMapWF :=
    execution.flattened.recursors.trace.map_wf recursorInitialMapWF
  exact recursorMapWF

/-- The retained ordinary declaration folds preserve constant-map
well-formedness through the public final environment. -/
theorem ordinaryFinalMapWF
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv)
    (numNested_eq : execution.nested.aux2nested.size = 0)
    (inputMapWF : env.constants.WF) : finalEnv.constants.WF := by
  have recursorMapWF := execution.flattenedFinalMapWF inputMapWF
  simpa only [execution.flattenedEnv_eq_final numNested_eq] using
    recursorMapWF

/-- Classify a family lookup at the exact flattened-block endpoint, before
the ordinary/nested outer branch chooses whether that endpoint is public or
is subsequently restored. -/
theorem flattenedFamilyLookupCases
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv)
    (inputMapWF : env.constants.WF) {name : Name} {info : InductiveVal}
    (found : execution.flattened.recursors.env.constants.find? name =
      some (.inductInfo info)) :
    env.constants.find? name = some (.inductInfo info) ∨
      info ∈ execution.flattened.eliminationExecution.normalization.declaredInfos ∧
        info.name = name := by
  have validationMapWF :
      execution.flattened.eliminationExecution.normalization.validationContext.env.constants.WF := by
    simpa only [execution.flattenedValidationEnv_eq] using inputMapWF
  have familyMapWF :=
    execution.flattened.eliminationExecution.normalization.declareTrace.map_wf
      validationMapWF
  have constructorMapWF :=
    execution.flattened.eliminationExecution.declareConstructorTrace.map_wf
      familyMapWF
  have recursorInitialMapWF :
      execution.flattened.recursors.initialEnv.constants.WF := by
    simpa only [execution.flattened.recursor_initialEnv_eq] using
      constructorMapWF
  rcases execution.flattened.recursors.trace.constant_lookup_cases
      recursorInitialMapWF found with recursorInput |
        ⟨_recursor, _member, taggedEq, _nameEq⟩
  · have constructorLookup :
        execution.flattened.eliminationExecution.constructorEnv.constants.find?
          name = some (.inductInfo info) := by
      simpa only [execution.flattened.recursor_initialEnv_eq] using
        recursorInput
    rcases execution.flattened.eliminationExecution.declareConstructorTrace
        |>.constant_lookup_cases familyMapWF constructorLookup with
      constructorInput | ⟨_constructor, _member, taggedEq, _nameEq⟩
    · rcases execution.flattened.eliminationExecution.normalization
          |>.declareTrace.map_lookup_cases validationMapWF constructorInput with
        old | inserted
      · exact .inl (by
          simpa only [execution.flattenedValidationEnv_eq] using old)
      · exact .inr inserted
    · cases taggedEq
  · cases taggedEq

/-- Classify a family record in an ordinary final environment using the exact
host declaration folds.  A new record retains both membership in the emitted
family inventory and the queried name. -/
theorem ordinaryFamilyLookupCases
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv)
    (numNested_eq : execution.nested.aux2nested.size = 0)
    (inputMapWF : env.constants.WF) {name : Name} {info : InductiveVal}
    (found : finalEnv.constants.find? name = some (.inductInfo info)) :
    env.constants.find? name = some (.inductInfo info) ∨
      info ∈ execution.flattened.eliminationExecution.normalization.declaredInfos ∧
        info.name = name := by
  have finalLookup : execution.flattened.recursors.env.constants.find? name =
      some (.inductInfo info) := by
    simpa only [execution.flattenedEnv_eq_final numNested_eq] using found
  exact execution.flattenedFamilyLookupCases inputMapWF finalLookup

/-- Classify a constructor record in an ordinary final environment using the
exact host declaration folds. -/
theorem ordinaryConstructorLookupCases
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv)
    (numNested_eq : execution.nested.aux2nested.size = 0)
    (inputMapWF : env.constants.WF) {name : Name} {info : ConstructorVal}
    (found : finalEnv.constants.find? name = some (.ctorInfo info)) :
    env.constants.find? name = some (.ctorInfo info) ∨
      info ∈ execution.flattened.eliminationExecution.declaredConstructorInfos ∧
        info.name = name := by
  have validationMapWF :
      execution.flattened.eliminationExecution.normalization.validationContext.env.constants.WF := by
    simpa only [execution.flattenedValidationEnv_eq] using inputMapWF
  have familyMapWF :=
    execution.flattened.eliminationExecution.normalization.declareTrace.map_wf
      validationMapWF
  have constructorMapWF :=
    execution.flattened.eliminationExecution.declareConstructorTrace.map_wf
      familyMapWF
  have recursorInitialMapWF :
      execution.flattened.recursors.initialEnv.constants.WF := by
    simpa only [execution.flattened.recursor_initialEnv_eq] using
      constructorMapWF
  have finalLookup : execution.flattened.recursors.env.constants.find? name =
      some (.ctorInfo info) := by
    simpa only [execution.flattenedEnv_eq_final numNested_eq] using found
  rcases execution.flattened.recursors.trace.constant_lookup_cases
      recursorInitialMapWF finalLookup with recursorInput |
        ⟨recursor, _member, taggedEq, _nameEq⟩
  · have constructorLookup :
        execution.flattened.eliminationExecution.constructorEnv.constants.find?
          name = some (.ctorInfo info) := by
      simpa only [execution.flattened.recursor_initialEnv_eq] using
        recursorInput
    rcases execution.flattened.eliminationExecution.declareConstructorTrace
        |>.map_lookup_cases familyMapWF constructorLookup with
      familyInput | inserted
    · rcases execution.flattened.eliminationExecution.normalization
          |>.declareTrace.constant_lookup_cases validationMapWF familyInput with
        old | ⟨family, _member, taggedEq, _nameEq⟩
      · exact .inl (by
          simpa only [execution.flattenedValidationEnv_eq] using old)
      · cases taggedEq
    · exact .inr inserted
  · cases taggedEq

/-- Classify a generated recursor record in an ordinary final environment
using the exact host declaration folds. -/
theorem ordinaryRecursorLookupCases
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv)
    (numNested_eq : execution.nested.aux2nested.size = 0)
    (inputMapWF : env.constants.WF) {name : Name} {info : RecursorVal}
    (found : finalEnv.constants.find? name = some (.recInfo info)) :
    env.constants.find? name = some (.recInfo info) ∨
      info ∈ execution.flattened.recursors.infos ∧ info.name = name := by
  have validationMapWF :
      execution.flattened.eliminationExecution.normalization.validationContext.env.constants.WF := by
    simpa only [execution.flattenedValidationEnv_eq] using inputMapWF
  have familyMapWF :=
    execution.flattened.eliminationExecution.normalization.declareTrace.map_wf
      validationMapWF
  have constructorMapWF :=
    execution.flattened.eliminationExecution.declareConstructorTrace.map_wf
      familyMapWF
  have recursorInitialMapWF :
      execution.flattened.recursors.initialEnv.constants.WF := by
    simpa only [execution.flattened.recursor_initialEnv_eq] using
      constructorMapWF
  have finalLookup : execution.flattened.recursors.env.constants.find? name =
      some (.recInfo info) := by
    simpa only [execution.flattenedEnv_eq_final numNested_eq] using found
  rcases execution.flattened.recursors.trace.map_lookup_cases
      recursorInitialMapWF finalLookup with recursorInput | inserted
  · have constructorLookup :
        execution.flattened.eliminationExecution.constructorEnv.constants.find?
          name = some (.recInfo info) := by
      simpa only [execution.flattened.recursor_initialEnv_eq] using
        recursorInput
    rcases execution.flattened.eliminationExecution.declareConstructorTrace
        |>.constant_lookup_cases familyMapWF constructorLookup with
      familyInput | ⟨constructor, _member, taggedEq, _nameEq⟩
    · rcases execution.flattened.eliminationExecution.normalization
          |>.declareTrace.constant_lookup_cases validationMapWF familyInput with
        old | ⟨family, _member, taggedEq, _nameEq⟩
      · exact .inl (by
          simpa only [execution.flattenedValidationEnv_eq] using old)
      · cases taggedEq
    · cases taggedEq
  · exact .inr inserted

/-- Every newly declared ordinary family record retains the name of one
flattened source family. -/
theorem ordinaryDeclaredFamilySource
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv)
    {info : InductiveVal}
    (member : info ∈
      execution.flattened.eliminationExecution.normalization.declaredInfos) :
    ∃ indType ∈ execution.nested.types, info.name = indType.name := by
  simpa only [AddInductive.NormalizationCandidateExecution.declaredInfos,
    List.toList_toArray] using
    AddInductive.declaredInductiveInfos_name
      execution.flattened.eliminationExecution.normalization.stats nparams
      execution.nested.types.toArray execution.nested.aux2nested.size isUnsafe
      execution.flattened.eliminationExecution.normalization.validationContext
      member

/-- Every source family traversed by a successful ordinary declaration was
absent from the public input map.  The proof follows the validator's exact
source-order metadata relation, rather than recovering a family from its
name after the declaration folds have completed. -/
theorem ordinarySourceFamilyFresh
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv)
    (inputMapWF : env.constants.WF) {indType : InductiveType}
    (member : indType ∈ execution.nested.types) :
    env.constants.find? indType.name = none := by
  have normalizationRun := execution.flattened.normalization_run
    execution.flattenedRun
  have familyRun :=
    execution.flattened.eliminationExecution.normalization
      |>.familyValidationResult_run normalizationRun
  have familySizes :=
    execution.flattened.eliminationExecution.normalization
      |>.familyValidationResult.sizes_of_run
        execution.nested.types_nonempty familyRun
  have paramsSize :
      execution.flattened.eliminationExecution.normalization.stats.params.size =
        nparams := by
    simpa only [
      AddInductive.NormalizationCandidateExecution.familyValidationResult] using
      familySizes.1
  have nindicesSize :
      execution.flattened.eliminationExecution.normalization.stats.nindices.size =
        execution.nested.types.length := by
    simpa only [
      AddInductive.NormalizationCandidateExecution.familyValidationResult] using
      familySizes.2.1
  have alignment : List.Forall₂
      (fun source info => ∃ numIndices,
        info = AddInductive.declaredInductiveInfo
          execution.flattened.eliminationExecution.normalization.stats nparams
          execution.nested.types.toArray source numIndices
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
  obtain ⟨offset, sourceAt⟩ := List.mem_iff_getElem?.1 member
  obtain ⟨info, infoAt, numIndices, infoEq⟩ :=
    Lean4Lean.List.Forall₂.getElem?_left alignment sourceAt
  have validationMapWF :
      execution.flattened.eliminationExecution.normalization.validationContext.env.constants.WF := by
    simpa only [execution.flattenedValidationEnv_eq] using inputMapWF
  have infoMember : info ∈
      execution.flattened.eliminationExecution.normalization.declaredInfos :=
    List.mem_iff_getElem?.2 ⟨offset, infoAt⟩
  have fresh :=
    execution.flattened.eliminationExecution.normalization.declareTrace
      |>.names_fresh validationMapWF info infoMember
  have infoName : info.name = indType.name := by
    rw [infoEq]
    rfl
  simpa only [execution.flattenedValidationEnv_eq, infoName] using fresh

/-- A projection-ready family whose complete observation was not already
present at the ordinary input is one of the exact family records emitted by
the retained validation fold.  Constructor ownership and canonical recursor
naming rule out activating an old family with a newly inserted artifact. -/
theorem ordinaryProjectionDeltaFamily
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv)
    (numNested_eq : execution.nested.aux2nested.size = 0)
    (inputMapWF : env.constants.WF) {name : Name} {info : InductiveVal}
    (found : finalEnv.find? name = some (.inductInfo info))
    (ready : finalEnv.isProjectionReadyStructure name = true)
    (notOld : ¬ (env.find? name = some (.inductInfo info) ∧
      env.isProjectionReadyStructure name = true)) :
    info ∈ execution.flattened.eliminationExecution.normalization.declaredInfos ∧
      info.name = name := by
  have finalMapWF := execution.ordinaryFinalMapWF numNested_eq inputMapWF
  have foundMap : finalEnv.constants.find? name =
      some (.inductInfo info) := by
    change finalEnv.constants.find?' name = _ at found
    rwa [finalMapWF.find?'_eq_find?] at found
  obtain ⟨constructorName, constructorInfo, recursorInfo, ctorsEq,
      numIndicesEq, constructorFound, recursorFound, owner, familyRecursor⟩ :=
    Kernel.Environment.isProjectionReadyStructure_info found ready
  have constructorFoundMap :
      finalEnv.constants.find? constructorName =
        some (.ctorInfo constructorInfo) := by
    change finalEnv.constants.find?' constructorName = _ at constructorFound
    rwa [finalMapWF.find?'_eq_find?] at constructorFound
  have recursorFoundMap :
      finalEnv.constants.find? (mkRecName name) =
        some (.recInfo recursorInfo) := by
    change finalEnv.constants.find?' (mkRecName name) = _ at recursorFound
    rwa [finalMapWF.find?'_eq_find?] at recursorFound
  have familyFoundMap :
      finalEnv.constants.find? name = some (.inductInfo info) := by
    change finalEnv.constants.find?' name = _ at found
    rwa [finalMapWF.find?'_eq_find?] at found
  rcases execution.ordinaryFamilyLookupCases numNested_eq inputMapWF foundMap
      with oldFamily | newFamily
  · rcases execution.ordinaryConstructorLookupCases numNested_eq inputMapWF
        constructorFoundMap with oldConstructor | newConstructor
    · rcases execution.ordinaryRecursorLookupCases numNested_eq inputMapWF
          recursorFoundMap with oldRecursor | newRecursor
      · have oldFamilyFind :
            env.find? name = some (.inductInfo info) := by
          change env.constants.find?' name = _
          rw [inputMapWF.find?'_eq_find?]
          exact oldFamily
        have oldConstructorFind :
            env.find? constructorName = some (.ctorInfo constructorInfo) := by
          change env.constants.find?' constructorName = _
          rw [inputMapWF.find?'_eq_find?]
          exact oldConstructor
        have oldRecursorFind :
            env.find? (mkRecName name) = some (.recInfo recursorInfo) := by
          change env.constants.find?' (mkRecName name) = _
          rw [inputMapWF.find?'_eq_find?]
          exact oldRecursor
        have oldReady : env.isProjectionReadyStructure name = true :=
          Kernel.Environment.isProjectionReadyStructure_of_info
            oldFamilyFind ctorsEq numIndicesEq oldConstructorFind
              oldRecursorFind owner familyRecursor
        exact (notOld ⟨oldFamilyFind, oldReady⟩).elim
      · have recursorNameMember : recursorInfo.name ∈
            execution.flattened.recursors.infos.map (·.name) :=
          List.mem_map.mpr ⟨recursorInfo, newRecursor.1, rfl⟩
        rw [AddInductive.declareRecursors_infos_names
          execution.flattened.recursorsRun] at recursorNameMember
        obtain ⟨indType, sourceMember, sourceRecursorNameEq⟩ :=
          List.mem_map.mp recursorNameMember
        have familyNameEq : indType.name = name := by
          have nameEq := sourceRecursorNameEq.trans newRecursor.2
          simpa [mkRecName] using nameEq
        have fresh := execution.ordinarySourceFamilyFresh inputMapWF
          sourceMember
        rw [familyNameEq, oldFamily] at fresh
        contradiction
    · obtain ⟨indType, sourceMember, constructorOwner⟩ := by
        simpa only [
          AddInductive.NormalizationEliminationExecution.declaredConstructorInfos,
          List.toList_toArray] using
          AddInductive.declaredConstructorInfos_induct
            execution.flattened.eliminationExecution.normalization.stats
            execution.nested.types.toArray isUnsafe
            execution.flattened.eliminationExecution.constructorContext
            newConstructor.1
      have familyNameEq : indType.name = name :=
        constructorOwner.symm.trans owner
      have fresh := execution.ordinarySourceFamilyFresh inputMapWF sourceMember
      rw [familyNameEq, oldFamily] at fresh
      contradiction
  · exact newFamily

/-- Every newly declared ordinary constructor record retains the name of one
flattened source family as its owner. -/
theorem ordinaryDeclaredConstructorSource
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv)
    {info : ConstructorVal}
    (member : info ∈
      execution.flattened.eliminationExecution.declaredConstructorInfos) :
    ∃ indType ∈ execution.nested.types, info.induct = indType.name := by
  simpa only [AddInductive.NormalizationEliminationExecution.declaredConstructorInfos,
    List.toList_toArray] using
    AddInductive.declaredConstructorInfos_induct
      execution.flattened.eliminationExecution.normalization.stats
      execution.nested.types.toArray isUnsafe
      execution.flattened.eliminationExecution.constructorContext member

/-- Every flattened source family has its canonical generated recursor in the
ordinary public final environment. -/
theorem ordinaryRecursorLookupOfSourceFamily
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv)
    (numNested_eq : execution.nested.aux2nested.size = 0)
    (inputMapWF : env.constants.WF) {indType : InductiveType}
    (member : indType ∈ execution.nested.types) :
    ∃ info, finalEnv.constants.find? (mkRecName indType.name) =
      some (.recInfo info) := by
  have validationMapWF :
      execution.flattened.eliminationExecution.normalization.validationContext.env.constants.WF := by
    simpa only [execution.flattenedValidationEnv_eq] using inputMapWF
  have familyMapWF :=
    execution.flattened.eliminationExecution.normalization.declareTrace.map_wf
      validationMapWF
  have constructorMapWF :=
    execution.flattened.eliminationExecution.declareConstructorTrace.map_wf
      familyMapWF
  have recursorInitialMapWF :
      execution.flattened.recursors.initialEnv.constants.WF := by
    simpa only [execution.flattened.recursor_initialEnv_eq] using
      constructorMapWF
  obtain ⟨info, infoMember, nameEq⟩ :=
    AddInductive.declareRecursors_info_of_family
      execution.flattened.recursorsRun (by simpa using member)
  have lookup := execution.flattened.recursors.trace.map_lookup
    recursorInitialMapWF infoMember
  refine ⟨info, ?_⟩
  simpa only [execution.flattenedEnv_eq_final numNested_eq, nameEq] using lookup

/-- The retained mixed restoration fold preserves constant-map
well-formedness through a genuinely nested public final environment. -/
theorem nestedFinalMapWF
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv)
    (numNested_ne : execution.nested.aux2nested.size ≠ 0)
    (inputMapWF : env.constants.WF) : finalEnv.constants.WF := by
  obtain ⟨restoration, _restorationRun, finalEq⟩ :=
    execution.restoration_of_numNested_ne numNested_ne
  have restoredMapWF := restoration.trace.map_wf inputMapWF
  simpa only [finalEq] using restoredMapWF

/-- Every original source-family name is fresh before a successful genuine
nested restoration.  The witness is the exact family record retained by the
restoration inventory, so this fact does not depend on reconstructing a
parallel name list. -/
theorem nestedSourceFamilyFresh
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv)
    (numNested_ne : execution.nested.aux2nested.size ≠ 0)
    (inputMapWF : env.constants.WF) {indType : InductiveType}
    (sourceMember : indType ∈ types) :
    env.constants.find? indType.name = none := by
  obtain ⟨restoration, _restorationRun, _finalEq⟩ :=
    execution.restoration_of_numNested_ne numNested_ne
  obtain ⟨info, inventoryMember, nameEq⟩ :=
    restoredNestedInfos_family_of_source
      (res := execution.nested)
      (flatEnv := execution.flattened.recursors.env) sourceMember
  have restorationMember : (.inductInfo info : ConstantInfo) ∈
      restoration.infos := by
    simpa only [restoration.infos_eq] using inventoryMember
  have fresh := restoration.trace.map_fresh inputMapWF restorationMember
  simpa only [ConstantInfo.name, ConstantInfo.toConstantVal, nameEq] using fresh

/-- Classify a family record in a genuinely nested final environment using
the exact mixed restoration inventory. -/
theorem nestedFamilyLookupCases
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv)
    (numNested_ne : execution.nested.aux2nested.size ≠ 0)
    (inputMapWF : env.constants.WF) {name : Name} {info : InductiveVal}
    (found : finalEnv.constants.find? name = some (.inductInfo info)) :
    env.constants.find? name = some (.inductInfo info) ∨
      (.inductInfo info : ConstantInfo) ∈
          restoredNestedInfos execution.nested
            execution.flattened.recursors.env types ∧
        info.name = name := by
  obtain ⟨restoration, _restorationRun, finalEq⟩ :=
    execution.restoration_of_numNested_ne numNested_ne
  have restoredFound : restoration.env.constants.find? name =
      some (.inductInfo info) := by
    simpa only [finalEq] using found
  rcases restoration.trace.family_map_lookup_cases inputMapWF restoredFound with
    old | inserted
  · exact .inl old
  · exact .inr ⟨by simpa only [restoration.infos_eq] using inserted.1,
      inserted.2⟩

/-- Classify a constructor record in a genuinely nested final environment
using the exact mixed restoration inventory. -/
theorem nestedConstructorLookupCases
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv)
    (numNested_ne : execution.nested.aux2nested.size ≠ 0)
    (inputMapWF : env.constants.WF) {name : Name} {info : ConstructorVal}
    (found : finalEnv.constants.find? name = some (.ctorInfo info)) :
    env.constants.find? name = some (.ctorInfo info) ∨
      (.ctorInfo info : ConstantInfo) ∈
          restoredNestedInfos execution.nested
            execution.flattened.recursors.env types ∧
        info.name = name := by
  obtain ⟨restoration, _restorationRun, finalEq⟩ :=
    execution.restoration_of_numNested_ne numNested_ne
  have restoredFound : restoration.env.constants.find? name =
      some (.ctorInfo info) := by
    simpa only [finalEq] using found
  rcases restoration.trace.constructor_map_lookup_cases inputMapWF
      restoredFound with old | inserted
  · exact .inl old
  · exact .inr ⟨by simpa only [restoration.infos_eq] using inserted.1,
      inserted.2⟩

/-- Classify a recursor record in a genuinely nested final environment using
the exact mixed restoration inventory. -/
theorem nestedRecursorLookupCases
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv)
    (numNested_ne : execution.nested.aux2nested.size ≠ 0)
    (inputMapWF : env.constants.WF) {name : Name} {info : RecursorVal}
    (found : finalEnv.constants.find? name = some (.recInfo info)) :
    env.constants.find? name = some (.recInfo info) ∨
      (.recInfo info : ConstantInfo) ∈
          restoredNestedInfos execution.nested
            execution.flattened.recursors.env types ∧
        info.name = name := by
  obtain ⟨restoration, _restorationRun, finalEq⟩ :=
    execution.restoration_of_numNested_ne numNested_ne
  have restoredFound : restoration.env.constants.find? name =
      some (.recInfo info) := by
    simpa only [finalEq] using found
  rcases restoration.trace.recursor_map_lookup_cases inputMapWF restoredFound with
    old | inserted
  · exact .inl old
  · exact .inr ⟨by simpa only [restoration.infos_eq] using inserted.1,
      inserted.2⟩

/-- A projection-ready family newly activated by a genuine nested
restoration is the exact restored family record of one source family.  The
constructor-owner check excludes activation by a restored constructor from
another family, while the recursor's `all` inventory excludes activation by
an unrelated restored auxiliary recursor. -/
theorem nestedProjectionDeltaFamily
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv)
    (numNested_ne : execution.nested.aux2nested.size ≠ 0)
    (inputMapWF : env.constants.WF) {name : Name} {info : InductiveVal}
    (found : finalEnv.find? name = some (.inductInfo info))
    (ready : finalEnv.isProjectionReadyStructure name = true)
    (notOld : ¬ (env.find? name = some (.inductInfo info) ∧
      env.isProjectionReadyStructure name = true)) :
    ∃ indType ∈ types,
      (.inductInfo info : ConstantInfo) ∈
        restoredNestedInfos execution.nested
          execution.flattened.recursors.env types ∧
      info.name = indType.name ∧ info.name = name := by
  have finalMapWF := execution.nestedFinalMapWF numNested_ne inputMapWF
  have foundMap : finalEnv.constants.find? name =
      some (.inductInfo info) := by
    change finalEnv.constants.find?' name = _ at found
    rwa [finalMapWF.find?'_eq_find?] at found
  obtain ⟨constructorName, constructorInfo, recursorInfo, ctorsEq,
      numIndicesEq, constructorFound, recursorFound, owner,
      familyRecursor⟩ :=
    Kernel.Environment.isProjectionReadyStructure_info found ready
  have constructorFoundMap :
      finalEnv.constants.find? constructorName =
        some (.ctorInfo constructorInfo) := by
    change finalEnv.constants.find?' constructorName = _ at constructorFound
    rwa [finalMapWF.find?'_eq_find?] at constructorFound
  have recursorFoundMap :
      finalEnv.constants.find? (mkRecName name) =
        some (.recInfo recursorInfo) := by
    change finalEnv.constants.find?' (mkRecName name) = _ at recursorFound
    rwa [finalMapWF.find?'_eq_find?] at recursorFound
  rcases execution.nestedFamilyLookupCases numNested_ne inputMapWF foundMap with
    oldFamily | newFamily
  · rcases execution.nestedConstructorLookupCases numNested_ne inputMapWF
        constructorFoundMap with oldConstructor | newConstructor
    · rcases execution.nestedRecursorLookupCases numNested_ne inputMapWF
          recursorFoundMap with oldRecursor | newRecursor
      · have oldFamilyFind :
            env.find? name = some (.inductInfo info) := by
          change env.constants.find?' name = _
          rw [inputMapWF.find?'_eq_find?]
          exact oldFamily
        have oldConstructorFind :
            env.find? constructorName = some (.ctorInfo constructorInfo) := by
          change env.constants.find?' constructorName = _
          rw [inputMapWF.find?'_eq_find?]
          exact oldConstructor
        have oldRecursorFind :
            env.find? (mkRecName name) = some (.recInfo recursorInfo) := by
          change env.constants.find?' (mkRecName name) = _
          rw [inputMapWF.find?'_eq_find?]
          exact oldRecursor
        have oldReady : env.isProjectionReadyStructure name = true :=
          Kernel.Environment.isProjectionReadyStructure_of_info
            oldFamilyFind ctorsEq numIndicesEq oldConstructorFind
              oldRecursorFind owner familyRecursor
        exact (notOld ⟨oldFamilyFind, oldReady⟩).elim
      · have allEq : recursorInfo.all = types.map (·.name) :=
          restoredNestedInfos_recursor_all newRecursor.1
        have sourceNameMember : name ∈ types.map (·.name) := by
          simpa only [allEq] using familyRecursor
        obtain ⟨indType, sourceMember, familyNameEq⟩ :=
          List.mem_map.mp sourceNameMember
        have fresh := execution.nestedSourceFamilyFresh numNested_ne inputMapWF
          sourceMember
        rw [familyNameEq, oldFamily] at fresh
        contradiction
    · obtain ⟨indType, sourceMember, constructorOwner⟩ :=
        restoredNestedInfos_constructor_cases newConstructor.1
      have familyNameEq : indType.name = name := constructorOwner.symm.trans owner
      have fresh := execution.nestedSourceFamilyFresh numNested_ne inputMapWF
        sourceMember
      rw [familyNameEq, oldFamily] at fresh
      contradiction
  · obtain ⟨indType, sourceMember, familyNameEq⟩ :=
      restoredNestedInfos_family_cases newFamily.1
    exact ⟨indType, sourceMember, newFamily.1, familyNameEq, newFamily.2⟩

/-- Every source family has its canonical main recursor in a genuinely
nested public final environment. -/
theorem nestedRecursorLookupOfSourceFamily
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv)
    (numNested_ne : execution.nested.aux2nested.size ≠ 0)
    (inputMapWF : env.constants.WF) {indType : InductiveType}
    (sourceMember : indType ∈ types) :
    ∃ info, finalEnv.constants.find? (mkRecName indType.name) =
      some (.recInfo info) := by
  obtain ⟨restoration, _restorationRun, finalEq⟩ :=
    execution.restoration_of_numNested_ne numNested_ne
  obtain ⟨info, inventoryMember, nameEq⟩ :=
    restoredNestedInfos_recursor_of_family
      (res := execution.nested)
      (flatEnv := execution.flattened.recursors.env) sourceMember
  have restorationMember : (.recInfo info : ConstantInfo) ∈
      restoration.infos := by
    simpa only [restoration.infos_eq] using inventoryMember
  have lookup := restoration.trace.map_lookup inputMapWF restorationMember
  have namedLookup : restoration.env.constants.find? info.name =
      some (.recInfo info) := by
    simpa [ConstantInfo.name, ConstantInfo.toConstantVal] using lookup
  rw [nameEq] at namedLookup
  refine ⟨info, ?_⟩
  simpa only [finalEq] using namedLookup

/-- Exact host-source ownership retained behind one restored projection
layout.  The public layout intentionally contains only metadata and Theory
family facts; this producer-side package additionally remembers the host
family/constructor positions audited before normalization and the exact
nested-restoration rewrite of the final constructor record. -/
structure RestoredProjectionParameterSource
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv)
    {ves : VEnvs}
    (staged : execution.FlattenedEnrichedStagingResult ves)
    (artifact : execution.FlattenedNestedArtifact staged)
    {name : Name} {info : InductiveVal} {after : VEnv}
    (layout : RestoredProjectionArtifactLayout finalEnv name info after) where
  source_eq : layout.view.source = artifact.source
  source_uvars_eq : layout.view.uvars = lparams.length
  nested_eq : HEq layout.view.nested artifact.alignedNested
  selection : Nonempty (VInductDecl.NestedStructureSelection
    artifact.alignedNested layout.view.familyIndex layout.view.sourceFamily
      layout.view.sourceConstructor)
  hostFamily : InductiveType
  hostFamily_at : execution.nested.types[layout.view.familyIndex]? =
    some hostFamily
  hostConstructor : Constructor
  hostConstructor_at : hostFamily.ctors[0]? = some hostConstructor
  rawConstructor : VConstVal
  sourceInput : VInductDecl.CandidateConstructorSourceInput
    staged.enriched.blockEnv lparams hostConstructor rawConstructor
  rawConstructor_eq : rawConstructor = layout.view.selection.flatConstructor
  restored_type_eq : layout.constructorInfo.type =
    execution.nested.restoreNested execution.flattened.recursors.env
      hostConstructor.type
  constructor_levelParams_eq : layout.constructorInfo.levelParams = lparams

/-- The exact raw host-source audit and completed shared-parameter basis
needed by restored projection construction.  This package is deliberately
indexed by the retained recursor producer and nested generation; it cannot
be paired with a parallel source, analyzer result, or parameter telescope. -/
structure RestoredProjectionParameterAuditSupport
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv)
    {ves : VEnvs}
    (staged : execution.FlattenedEnrichedStagingResult ves)
    (artifact : execution.FlattenedNestedArtifact staged)
    (shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true) where
  basis : VInductDecl.ConstructorRawPreFamilyParameterAuditBasis
    (ves.venv .safe) lparams
    (staged.recursorShape shape).execution.eliminationExecution.normalization.stats
    (staged.recursorShape shape).execution.eliminationExecution.normalization.validationContext
    staged.source.nparams artifact.generation.block.checked.params
  rawAudit : VInductDecl.ProducedBlockRawHostParameterAuditRun
    (staged.recursorShape shape)

/-- Assemble the restored parameter-audit handoff from a producer-owned,
shape-neutral basis and the single raw host-source audit owned by the same
recursor producer. -/
theorem
    RestoredProjectionParameterAuditSupport.nonempty_ofParameterAuditBasis
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    {flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape}
    (parameterBasis :
      flat.run.elimination.block.ParameterAuditBasisSupport)
    (rawAudit : VInductDecl.ProducedBlockRawHostParameterAuditRun
      (staged.recursorShape shape)) :
    Nonempty (execution.RestoredProjectionParameterAuditSupport staged
      artifact shape) :=
  ⟨{ basis := parameterBasis.basis, rawAudit := rawAudit }⟩

/-- Compatibility constructor for the currently implemented indexed-mutual
producer.  The restored handoff itself no longer exposes this source-list
restriction. -/
theorem
    RestoredProjectionParameterAuditSupport.nonempty_of_secondFamilyIndex
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    {flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape}
    (secondFamily :
      flat.run.elimination.block.HasSecondFamilyIndexSupport)
    (rawAudit : VInductDecl.ProducedBlockRawHostParameterAuditRun
      (staged.recursorShape shape)) :
    Nonempty (execution.RestoredProjectionParameterAuditSupport staged
      artifact shape) := by
  exact nonempty_ofParameterAuditBasis
    (.ofSecondFamilyIndex secondFamily (by rfl)) rawAudit

/-- Assemble restored parameter-layout support directly from a complete
audit of the retained recursor producer.  This proof-facing constructor does
not execute the raw-host builder again: it projects the exact dependent trace
already selected by `audit` and pairs it with the producer-owned canonical
parameter basis. -/
noncomputable def
    RestoredProjectionParameterAuditSupport.ofParameterAuditBasis
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    {flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape}
    (parameterBasis :
      flat.run.elimination.block.ParameterAuditBasisSupport)
    (audit : VInductDecl.ProducedBlockRecursorStage3AuditRun
      (staged.recursorShape shape) lparams) :
    execution.RestoredProjectionParameterAuditSupport staged artifact shape :=
  { basis := parameterBasis.basis
    rawAudit := audit.rawHostParameterAudit }

/-- Compatibility wrapper for the indexed-mutual producer. -/
noncomputable def
    RestoredProjectionParameterAuditSupport.ofSecondFamilyIndexAudit
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    {flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape}
    (secondFamily :
      flat.run.elimination.block.HasSecondFamilyIndexSupport)
    (audit : VInductDecl.ProducedBlockRecursorStage3AuditRun
      (staged.recursorShape shape) lparams) :
    execution.RestoredProjectionParameterAuditSupport staged artifact shape :=
  ofParameterAuditBasis
    (.ofSecondFamilyIndex secondFamily (by rfl)) audit

/-- Execute the remaining narrow raw-host audit and assemble the complete
restored parameter-layout support at the same producer.  The executable
result owns the exact source-indexed audit trace rather than exposing its
success equation as a consumer premise. -/
noncomputable def
    RestoredProjectionParameterAuditSupport.ofParameterAuditBasis?
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    {flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape}
    (parameterBasis :
      flat.run.elimination.block.ParameterAuditBasisSupport) :
    Except Lean.Kernel.Exception
      (execution.RestoredProjectionParameterAuditSupport staged artifact
        shape) :=
  match staged.recursorRawHostParameterAudit? shape with
  | .error error => .error error
  | .ok rawAudit =>
      .ok {
        basis := parameterBasis.basis
        rawAudit := rawAudit }

/-- Compatibility wrapper for the indexed-mutual producer. -/
noncomputable def
    RestoredProjectionParameterAuditSupport.ofSecondFamilyIndex?
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    {flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape}
    (secondFamily :
      flat.run.elimination.block.HasSecondFamilyIndexSupport) :
    Except Lean.Kernel.Exception
      (execution.RestoredProjectionParameterAuditSupport staged artifact
        shape) :=
  ofParameterAuditBasis? (.ofSecondFamilyIndex secondFamily (by rfl))

/-- A complete Stage-3 audit of the retained recursor producer guarantees
that the narrow restored-support executable succeeds.  Thus callers already
holding the canonical broad producer run never need to rerun or restate its
raw-host checker equation. -/
theorem
    RestoredProjectionParameterAuditSupport.ofParameterAuditBasis?_success
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    {flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape}
    (parameterBasis :
      flat.run.elimination.block.ParameterAuditBasisSupport)
    (audit : VInductDecl.ProducedBlockRecursorStage3AuditRun
      (staged.recursorShape shape) lparams) :
    ∃ support : execution.RestoredProjectionParameterAuditSupport staged
        artifact shape,
      RestoredProjectionParameterAuditSupport.ofParameterAuditBasis?
        parameterBasis = .ok support := by
  obtain ⟨rawAudit, auditRun⟩ :=
    staged.recursorRawHostParameterAudit?_success shape audit
  refine ⟨{
    basis := parameterBasis.basis
    rawAudit := rawAudit }, ?_⟩
  unfold RestoredProjectionParameterAuditSupport.ofParameterAuditBasis?
  rw [auditRun]

/-- Compatibility success theorem for the indexed-mutual producer. -/
theorem
    RestoredProjectionParameterAuditSupport.ofSecondFamilyIndex?_success
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    {flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape}
    (secondFamily :
      flat.run.elimination.block.HasSecondFamilyIndexSupport)
    (audit : VInductDecl.ProducedBlockRecursorStage3AuditRun
      (staged.recursorShape shape) lparams) :
    ∃ support : execution.RestoredProjectionParameterAuditSupport staged
        artifact shape,
      RestoredProjectionParameterAuditSupport.ofSecondFamilyIndex?
        secondFamily = .ok support := by
  simpa only [RestoredProjectionParameterAuditSupport.ofSecondFamilyIndex?]
    using ofParameterAuditBasis?_success
      (.ofSecondFamilyIndex secondFamily (by rfl)) audit

/-- Every exact flattened generation owns its canonical shared-parameter
audit basis.  The source-list case split is internal to the retained block
producer, so nested restoration cannot reselect a singleton or mutual
traversal. -/
noncomputable def
    FlattenedExactRecursorStagingResult.parameterAuditBasisSupport
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {generation : VInductDecl.BlockGenerationChecked staged.source}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    (flat : execution.FlattenedExactRecursorStagingResult staged generation
      shape) :
    flat.run.elimination.block.ParameterAuditBasisSupport :=
  flat.run.elimination.block.parameterAuditBasisSupport (by rfl)

/-- Exact nested replay together with the two producer-owned facts consumed
by restored constructor-parameter layout.  Keeping these witnesses beside
the transaction avoids reconstructing a parallel recursor producer after
the flattened and restored endpoints have already been fixed. -/
structure
    FlattenedExactNestedProjectionParameterRun
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    (flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape)
    (metadata : VInductDecl.ExactProducedBlockMetadataPrefixRun flat.run)
    {after : VEnv}
    (restoration : execution.FlattenedNestedRestorationResult artifact after)
    (numNested_ne : execution.nested.aux2nested.size ≠ 0)
    (restoredMetadata :
      execution.FlattenedNestedRestoredMetadataPrefixRun restoration
        numNested_ne) where
  transaction : execution.FlattenedExactNestedTransactionResult flat
    metadata restoration numNested_ne restoredMetadata
  parameterBasis :
    flat.run.elimination.block.ParameterAuditBasisSupport
  stage3Audit : VInductDecl.ProducedBlockRecursorStage3AuditRun
    (staged.recursorShape shape) lparams

/-- Assemble the projection-parameter owner from the exact nested
transaction and its producer audit.  Shared-parameter ownership is projected
from `flat`; callers no longer supply a traversal-dependent basis. -/
noncomputable def FlattenedExactNestedProjectionParameterRun.ofTransaction
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    {flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape}
    {metadata : VInductDecl.ExactProducedBlockMetadataPrefixRun flat.run}
    {after : VEnv}
    {restoration : execution.FlattenedNestedRestorationResult artifact after}
    {numNested_ne : execution.nested.aux2nested.size ≠ 0}
    {restoredMetadata :
      execution.FlattenedNestedRestoredMetadataPrefixRun restoration
        numNested_ne}
    (transaction : execution.FlattenedExactNestedTransactionResult flat
      metadata restoration numNested_ne restoredMetadata)
    (stage3Audit : VInductDecl.ProducedBlockRecursorStage3AuditRun
      (staged.recursorShape shape) lparams) :
    execution.FlattenedExactNestedProjectionParameterRun flat metadata
      restoration numNested_ne restoredMetadata where
  transaction := transaction
  parameterBasis := flat.parameterAuditBasisSupport
  stage3Audit := stage3Audit

/-- Project the complete restored parameter support from the witnesses
retained by one exact nested projection run. -/
noncomputable def
    FlattenedExactNestedProjectionParameterRun.parameterAuditSupport
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    {flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape}
    {metadata : VInductDecl.ExactProducedBlockMetadataPrefixRun flat.run}
    {after : VEnv}
    {restoration : execution.FlattenedNestedRestorationResult artifact after}
    {numNested_ne : execution.nested.aux2nested.size ≠ 0}
    {restoredMetadata :
      execution.FlattenedNestedRestoredMetadataPrefixRun restoration
        numNested_ne}
    (run : execution.FlattenedExactNestedProjectionParameterRun flat metadata
      restoration numNested_ne restoredMetadata) :
    execution.RestoredProjectionParameterAuditSupport staged artifact shape :=
  RestoredProjectionParameterAuditSupport.ofParameterAuditBasis
    run.parameterBasis run.stage3Audit

/-- Construct the exact restored metadata layout behind a newly
projection-ready family in a genuine nested transaction.  The host family is
first inverted through the mixed restoration inventory to its exact flattened
record.  The flattened declaration alignment then identifies one raw Theory
position; checked family-name uniqueness identifies that position with the
source family selected from the nested replay trace.  The same retained
constructor position aligns the restored cached metadata with the checked
flattened telescope, so every non-operational field of the projection artifact
is a producer fact rather than a projection-consumer premise. -/
theorem
    FlattenedExactNestedTransactionResult.restoredProjectionArtifactLayoutSource
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    {flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape}
    {metadata : VInductDecl.ExactProducedBlockMetadataPrefixRun flat.run}
    {after : VEnv}
    {restoration : execution.FlattenedNestedRestorationResult artifact after}
    {numNested_ne : execution.nested.aux2nested.size ≠ 0}
    {restoredMetadata :
      execution.FlattenedNestedRestoredMetadataPrefixRun restoration
        numNested_ne}
    (transaction : execution.FlattenedExactNestedTransactionResult flat
      metadata restoration numNested_ne restoredMetadata)
    (wf : ves.WF env) {name : Name} {info : InductiveVal}
    (found : finalEnv.find? name = some (.inductInfo info))
    (ready : finalEnv.isProjectionReadyStructure name = true)
    (notOld : ¬ (env.find? name = some (.inductInfo info) ∧
      env.isProjectionReadyStructure name = true)) :
    ∃ layout : RestoredProjectionArtifactLayout finalEnv name info after,
      Nonempty (RestoredProjectionParameterSource execution staged artifact
        layout) := by
  have inputMapWF := (wf.tr (safety := .safe)).map_wf
  have finalMapWF := execution.nestedFinalMapWF numNested_ne inputMapWF
  have foundMap : finalEnv.constants.find? name =
      some (.inductInfo info) := by
    change finalEnv.constants.find?' name = _ at found
    rwa [finalMapWF.find?'_eq_find?] at found
  obtain ⟨constructorName, constructorInfo, recursorInfo, ctorsEq,
      numIndicesEq, constructorFound, recursorFound, _owner,
      _familyRecursor⟩ :=
    Kernel.Environment.isProjectionReadyStructure_info found ready
  have constructorFoundMap :
      finalEnv.constants.find? constructorName =
        some (.ctorInfo constructorInfo) := by
    change finalEnv.constants.find?' constructorName = _ at constructorFound
    rwa [finalMapWF.find?'_eq_find?] at constructorFound
  have recursorFoundMap :
      finalEnv.constants.find? (mkRecName name) =
        some (.recInfo recursorInfo) := by
    change finalEnv.constants.find?' (mkRecName name) = _ at recursorFound
    rwa [finalMapWF.find?'_eq_find?] at recursorFound
  obtain ⟨_classifiedSource, _classifiedMember, restoredMember,
      _classifiedName, _infoName⟩ :=
    execution.nestedProjectionDeltaFamily numNested_ne inputMapWF found ready
      notOld
  obtain ⟨restoredSource, restoredSourceMember, infoRestoredEq⟩ :=
    restoredNestedInfos_family_exact restoredMember
  have restoredSourceName : restoredSource.name = name := by
    calc
      restoredSource.name = info.name := by
        rw [infoRestoredEq]
        rfl
      _ = name := by
        simpa only [infoRestoredEq] using _infoName
  have inputFresh : env.constants.find? name = none := by
    have fresh := execution.nestedSourceFamilyFresh numNested_ne inputMapWF
      restoredSourceMember
    simpa only [restoredSourceName] using fresh
  obtain ⟨sourceFamily, sourceFamilyMember, sourceFamilyName⟩ :=
    transaction.safeTrace.sourceFamily_of_fresh_final_lookup inputMapWF
      inputFresh foundMap
  obtain ⟨familyIndex, sourceFamilyAt⟩ :=
    List.mem_iff_getElem?.1 sourceFamilyMember

  have restoredCtorsEq :
      (execution.nested.restoreSourceInductiveInfo
        execution.flattened.recursors.env (types.map (·.name))
        restoredSource).ctors = [constructorName] := by
    rw [← infoRestoredEq]
    exact ctorsEq
  have restoredCtorsNonempty :
      (execution.nested.restoreSourceInductiveInfo
        execution.flattened.recursors.env (types.map (·.name))
        restoredSource).ctors ≠ [] := by
    rw [restoredCtorsEq]
    simp
  obtain ⟨flatInfo, flatFound, restoredRecordEq⟩ :=
    execution.nested.restoreSourceInductiveInfo_of_ctors_ne_nil
      execution.flattened.recursors.env (types.map (·.name))
      restoredSource restoredCtorsNonempty
  have infoFlatEq : info = {
      flatInfo with
      name := restoredSource.name
      all := types.map (·.name) } :=
    infoRestoredEq.trans restoredRecordEq
  have flatMapWF := execution.flattenedFinalMapWF inputMapWF
  have flatFoundMap :
      execution.flattened.recursors.env.constants.find? restoredSource.name =
        some (.inductInfo flatInfo) := by
    change execution.flattened.recursors.env.constants.find?'
      restoredSource.name = _ at flatFound
    rwa [flatMapWF.find?'_eq_find?] at flatFound
  have flatDeclared :
      flatInfo ∈
          execution.flattened.eliminationExecution.normalization.declaredInfos ∧
        flatInfo.name = restoredSource.name := by
    rcases execution.flattenedFamilyLookupCases inputMapWF flatFoundMap with
      old | declared
    · have fresh := execution.nestedSourceFamilyFresh numNested_ne inputMapWF
        restoredSourceMember
      rw [old] at fresh
      contradiction
    · exact declared

  have normalizationRun := execution.flattened.normalization_run
    execution.flattenedRun
  have familyRun :=
    execution.flattened.eliminationExecution.normalization
      |>.familyValidationResult_run normalizationRun
  have familySizes :=
    execution.flattened.eliminationExecution.normalization
      |>.familyValidationResult.sizes_of_run
        execution.nested.types_nonempty familyRun
  have nindicesSize :
      execution.flattened.eliminationExecution.normalization.stats.nindices.size =
        execution.nested.types.length := by
    simpa only [
      AddInductive.NormalizationCandidateExecution.familyValidationResult] using
      familySizes.2.1
  have paramsSize :
      execution.flattened.eliminationExecution.normalization.stats.params.size =
        nparams := by
    simpa only [
      AddInductive.NormalizationCandidateExecution.familyValidationResult] using
      familySizes.1
  have familyAlignment : List.Forall₂
      (fun source familyInfo => ∃ numIndices,
        familyInfo = AddInductive.declaredInductiveInfo
          execution.flattened.eliminationExecution.normalization.stats nparams
          execution.nested.types.toArray source numIndices
          execution.nested.aux2nested.size false
          execution.flattened.eliminationExecution.normalization.validationContext)
      execution.nested.types
      execution.flattened.eliminationExecution.normalization.declaredInfos := by
    simpa only [
      AddInductive.NormalizationCandidateExecution.declaredInfos,
      List.toList_toArray] using
      AddInductive.declaredInductiveInfos_matches
        execution.flattened.eliminationExecution.normalization.stats nparams
        execution.nested.types.toArray execution.nested.aux2nested.size false
        execution.flattened.eliminationExecution.normalization.validationContext
        (by simpa using nindicesSize)
  obtain ⟨offset, flatInfoAt⟩ := List.mem_iff_getElem?.1 flatDeclared.1
  obtain ⟨flatSource, flatSourceAt, _flatSourceAlignment⟩ :=
    Lean4Lean.List.Forall₂.getElem?_right familyAlignment flatInfoAt
  obtain ⟨rawFamily, rawFamilyAt, familySource, constructorSources⟩ :=
    staged.enriched.enrichment.input.getElem? flatSourceAt
  have stagedRawFamilyAt : staged.source.types[offset]? =
      some rawFamily := by
    simpa only [FlattenedEnrichedStagingResult.source,
      VInductDecl.CandidateBlockSourceListEnrichment.toRawDecl] using
      rawFamilyAt.down
  have rawCountAt := flat.run.rawIndexCounts.getElem? stagedRawFamilyAt
  change (staged.recursorShape shape).execution.eliminationExecution.normalization.stats.nindices[
    0 + offset]? = _ at rawCountAt
  rw [staged.recursorShape_nindices_eq shape] at rawCountAt
  have countAt :
      execution.flattened.eliminationExecution.normalization.stats.nindices[offset]? =
        some (VInductDecl.ctorFields
          (VExpr.dropN staged.source.nparams rawFamily.type)).length := by
    change
      execution.flattened.eliminationExecution.normalization.stats.nindices[
        0 + offset]? = _ at rawCountAt
    simpa only [Nat.zero_add] using rawCountAt
  have expectedFlatInfoAt :
      execution.flattened.eliminationExecution.normalization.declaredInfos[offset]? =
        some (AddInductive.declaredInductiveInfo
          execution.flattened.eliminationExecution.normalization.stats nparams
          execution.nested.types.toArray flatSource
          (VInductDecl.ctorFields
            (VExpr.dropN staged.source.nparams rawFamily.type)).length
          execution.nested.aux2nested.size false
          execution.flattened.eliminationExecution.normalization.validationContext) := by
    simpa only [
      AddInductive.NormalizationCandidateExecution.declaredInfos,
      List.toList_toArray] using
      AddInductive.declaredInductiveInfos_getElem?
        execution.flattened.eliminationExecution.normalization.stats nparams
        execution.nested.types.toArray execution.nested.aux2nested.size false
        execution.flattened.eliminationExecution.normalization.validationContext
        flatSourceAt countAt
  have flatInfoEq : flatInfo = AddInductive.declaredInductiveInfo
      execution.flattened.eliminationExecution.normalization.stats nparams
      execution.nested.types.toArray flatSource
      (VInductDecl.ctorFields
        (VExpr.dropN staged.source.nparams rawFamily.type)).length
      execution.nested.aux2nested.size false
      execution.flattened.eliminationExecution.normalization.validationContext :=
    Option.some.inj (flatInfoAt.symm.trans expectedFlatInfoAt)
  have flatNumIndicesEq : flatInfo.numIndices = 0 := by
    simpa only [infoFlatEq] using numIndicesEq
  have rawIndicesLength :
      (VInductDecl.ctorFields
        (VExpr.dropN staged.source.nparams rawFamily.type)).length = 0 := by
    rw [flatInfoEq] at flatNumIndicesEq
    simpa only [AddInductive.declaredInductiveInfo] using flatNumIndicesEq
  have rawIndicesEq :
      VInductDecl.ctorFields
        (VExpr.dropN staged.source.nparams rawFamily.type) = [] :=
    List.length_eq_zero_iff.mp rawIndicesLength
  have flatInfoCtorsEq : flatInfo.ctors = [constructorName] := by
    simpa only [infoFlatEq] using ctorsEq
  have flatSourceConstructorNames :
      flatSource.ctors.map (·.name) = [constructorName] := by
    rw [flatInfoEq] at flatInfoCtorsEq
    simpa only [AddInductive.declaredInductiveInfo] using flatInfoCtorsEq
  have flatSourceConstructorsLength : flatSource.ctors.length = 1 := by
    have lengths := congrArg List.length flatSourceConstructorNames
    simpa only [List.length_map, List.length_cons, List.length_nil] using lengths
  obtain ⟨flatSourceConstructor, flatSourceConstructorsEq⟩ :=
    List.length_eq_one_iff.mp flatSourceConstructorsLength
  have flatSourceConstructorName :
      flatSourceConstructor.name = constructorName := by
    have selected : flatSourceConstructor.name = constructorName ∧ True := by
      simpa only [flatSourceConstructorsEq, List.map_cons, List.map_nil,
        List.cons.injEq] using flatSourceConstructorNames
    exact selected.1
  have flatSourceConstructorAt : flatSource.ctors[0]? =
      some flatSourceConstructor := by
    simp only [flatSourceConstructorsEq, List.getElem?_cons_zero]
  obtain ⟨translatedConstructor, translatedConstructorAt,
      constructorSource⟩ := constructorSources.getElem? flatSourceConstructorAt
  have rawConstructorsLength : rawFamily.ctors.length = 1 := by
    rw [← constructorSources.length_eq]
    exact flatSourceConstructorsLength
  obtain ⟨rawConstructor, rawConstructorsEq⟩ :=
    List.length_eq_one_iff.mp rawConstructorsLength
  have translatedConstructorEq : translatedConstructor = rawConstructor := by
    rw [rawConstructorsEq] at translatedConstructorAt
    simpa only [List.getElem?_cons_zero, Option.some.injEq] using
      translatedConstructorAt.down.symm

  obtain ⟨sourceFlatFamily, sourceFlatFamilyAt, sourceFamilyHeader⟩ :=
    artifact.flat_family_header_at sourceFamilyAt
  have sourceFlatFamilyName : sourceFlatFamily.name = name := by
    have headerName := congrArg VInductDecl.NestedFamilyHeader.name
      sourceFamilyHeader
    have flatSourceName : sourceFlatFamily.name = sourceFamily.name := by
      simpa [VInductDecl.VInductiveType.nestedHeader] using headerName
    exact flatSourceName.trans sourceFamilyName
  have rawFamilyName : rawFamily.name = name := by
    calc
      rawFamily.name = flatSource.name := familySource.down.name_eq.symm
      _ = flatInfo.name := by
        simpa only [AddInductive.declaredInductiveInfo] using
          (congrArg (fun value : InductiveVal => value.name) flatInfoEq).symm
      _ = restoredSource.name := flatDeclared.2
      _ = name := restoredSourceName
  have stagedNamesNodup :
      (staged.source.types.map fun family => family.name).Nodup := by
    simpa only [artifact.flat_eq] using
      artifact.nested.flat_family_names_nodup
  have sourceNameAt :
      (staged.source.types.map fun family => family.name)[familyIndex]? =
        some name := by
    simp only [List.getElem?_map, sourceFlatFamilyAt, Option.map_some,
      sourceFlatFamilyName]
  have rawNameAt :
      (staged.source.types.map fun family => family.name)[offset]? =
        some name := by
    simp only [List.getElem?_map, stagedRawFamilyAt, Option.map_some,
      rawFamilyName]
  have sourceIndexUpper :
      familyIndex < (staged.source.types.map fun family => family.name).length := by
    simpa using (List.getElem?_eq_some_iff.1 sourceNameAt).1
  have indexEq : familyIndex = offset :=
    (List.getElem?_inj sourceIndexUpper stagedNamesNodup).1
      (sourceNameAt.trans rawNameAt.symm)
  subst offset
  have sourceFlatFamilyEq : sourceFlatFamily = rawFamily :=
    Option.some.inj (sourceFlatFamilyAt.symm.trans stagedRawFamilyAt)
  have sourceRawTypeEq : rawFamily.type = sourceFamily.type := by
    calc
      rawFamily.type = sourceFlatFamily.type :=
        congrArg (fun value : VInductiveType => value.type)
          sourceFlatFamilyEq.symm
      _ = sourceFamily.type := by
        simpa [VInductDecl.VInductiveType.nestedHeader] using
          congrArg VInductDecl.NestedFamilyHeader.type sourceFamilyHeader
  have sourceConstructorsLength : sourceFamily.ctors.length = 1 := by
    have headerLengths := congrArg
      (fun header : VInductDecl.NestedFamilyHeader =>
        header.constructors.length) sourceFamilyHeader
    have sourceFlatLength : sourceFlatFamily.ctors.length =
        sourceFamily.ctors.length := by
      simpa [VInductDecl.VInductiveType.nestedHeader] using headerLengths
    calc
      sourceFamily.ctors.length = sourceFlatFamily.ctors.length :=
        sourceFlatLength.symm
      _ = rawFamily.ctors.length :=
        congrArg (fun family : VInductiveType => family.ctors.length)
          sourceFlatFamilyEq
      _ = 1 := rawConstructorsLength
  obtain ⟨sourceConstructor, sourceConstructorsEq⟩ :=
    List.length_eq_one_iff.mp sourceConstructorsLength
  have constructorHeaderEq :
      VInductDecl.VConstVal.nestedHeader rawConstructor =
        VInductDecl.VConstVal.nestedHeader sourceConstructor := by
    have headers := congrArg VInductDecl.NestedFamilyHeader.constructors
      sourceFamilyHeader
    rw [sourceFlatFamilyEq] at headers
    simp only [VInductDecl.VInductiveType.nestedHeader] at headers
    rw [rawConstructorsEq, sourceConstructorsEq] at headers
    simp only [List.map_cons, List.map_nil, List.cons.injEq] at headers
    exact headers.1
  have sourceConstructorName : sourceConstructor.name = constructorName := by
    calc
      sourceConstructor.name = rawConstructor.name := by
        simpa [VInductDecl.VConstVal.nestedHeader] using
          congrArg VInductDecl.NestedCtorHeader.name constructorHeaderEq.symm
      _ = translatedConstructor.name :=
        congrArg VConstVal.name translatedConstructorEq.symm
      _ = flatSourceConstructor.name := constructorSource.down.name_eq.symm
      _ = constructorName := flatSourceConstructorName
  have sourceNparamsEq : artifact.source.nparams = staged.source.nparams :=
    artifact.source_nparams_eq.trans staged.source_nparams_eq.symm
  have sourceRawIndicesEq :
      VInductDecl.ctorFields
        (VExpr.dropN artifact.source.nparams sourceFamily.type) = [] := by
    rw [sourceNparamsEq, ← sourceRawTypeEq]
    exact rawIndicesEq
  obtain ⟨selection⟩ := artifact.selectStructure sourceFamilyAt
    sourceConstructorsEq sourceRawIndicesEq

  have sourceConstructorBlockMember : sourceConstructor ∈
      artifact.source.blockConstructorConstants := by
    simp only [VInductDecl.blockConstructorConstants, List.mem_flatMap]
    exact ⟨sourceFamily, sourceFamilyMember, by
      rw [sourceConstructorsEq]
      simp⟩
  have typeMapWF := transaction.safeTrace.addTypes.map_wf inputMapWF
  have sourceConstructorInputFresh :
      env.constants.find? sourceConstructor.name = none := by
    have typeFresh := transaction.safeTrace.addCtors.map_fresh typeMapWF
      sourceConstructorBlockMember
    exact transaction.safeTrace.addTypes.input_map_none_of_output_none
      inputMapWF typeFresh
  have restoredConstructor :
      (.ctorInfo constructorInfo : ConstantInfo) ∈
          restoredNestedInfos execution.nested
            execution.flattened.recursors.env types ∧
        constructorInfo.name = constructorName := by
    rcases execution.nestedConstructorLookupCases numNested_ne inputMapWF
        constructorFoundMap with old | inserted
    · have oldAtSource : env.constants.find? sourceConstructor.name =
          some (.ctorInfo constructorInfo) := by
        simpa only [sourceConstructorName] using old
      rw [oldAtSource] at sourceConstructorInputFresh
      contradiction
    · exact inserted

  let expectedFlatConstructorInfo := AddInductive.declaredConstructorInfo
    execution.flattened.eliminationExecution.normalization.stats
    flatSource.name flatSourceConstructor 0 false
    execution.flattened.eliminationExecution.constructorContext
  have expectedFlatConstructorMember : expectedFlatConstructorInfo ∈
      execution.flattened.eliminationExecution.declaredConstructorInfos := by
    simp only [
      AddInductive.NormalizationEliminationExecution.declaredConstructorInfos,
      AddInductive.declaredConstructorInfos_toArray, List.mem_flatMap]
    refine ⟨flatSource, List.mem_of_getElem? flatSourceAt, ?_⟩
    rw [flatSourceConstructorsEq]
    simp [expectedFlatConstructorInfo,
      AddInductive.declaredConstructorInfosFor]
  have validationMapWF :
      execution.flattened.eliminationExecution.normalization.validationContext
        |>.env.constants.WF := by
    simpa only [execution.flattenedValidationEnv_eq] using inputMapWF
  have hostFamilyMapWF :=
    execution.flattened.eliminationExecution.normalization.declareTrace.map_wf
      validationMapWF
  have hostConstructorMapWF :=
    execution.flattened.eliminationExecution.declareConstructorTrace.map_wf
      hostFamilyMapWF
  have recursorInitialMapWF :
      execution.flattened.recursors.initialEnv.constants.WF := by
    simpa only [execution.flattened.recursor_initialEnv_eq] using
      hostConstructorMapWF
  have expectedFlatConstructorLookup₀ :=
    execution.flattened.eliminationExecution.declareConstructorTrace.map_lookup
      hostFamilyMapWF expectedFlatConstructorMember
  have expectedFlatConstructorLookup₁ :
      execution.flattened.recursors.initialEnv.constants.find?
          expectedFlatConstructorInfo.name =
        some (.ctorInfo expectedFlatConstructorInfo) := by
    simpa only [execution.flattened.recursor_initialEnv_eq] using
      expectedFlatConstructorLookup₀
  have expectedFlatConstructorLookup :=
    execution.flattened.recursors.trace.preserve_map_lookup
      recursorInitialMapWF expectedFlatConstructorLookup₁
  have expectedFlatConstructorName :
      expectedFlatConstructorInfo.name = constructorName := by
    simp [expectedFlatConstructorInfo,
      AddInductive.declaredConstructorInfo, flatSourceConstructorName]
  have flatConstructorLookupMap :
      execution.flattened.recursors.env.constants.find? constructorInfo.name =
        some (.ctorInfo expectedFlatConstructorInfo) := by
    simpa only [restoredConstructor.2, expectedFlatConstructorName] using
      expectedFlatConstructorLookup
  have flatConstructorLookup :
      execution.flattened.recursors.env.find? constructorInfo.name =
        some (.ctorInfo expectedFlatConstructorInfo) := by
    change execution.flattened.recursors.env.constants.find?'
      constructorInfo.name = _
    rw [flatMapWF.find?'_eq_find?]
    exact flatConstructorLookupMap
  have restoredCachedFields : constructorInfo.numFields =
      expectedFlatConstructorInfo.numFields :=
    restoredNestedInfos_constructor_numFields_of_flat_lookup
      restoredConstructor.1 flatConstructorLookup

  have selectionFlatFamilyEq : selection.flatFamily = rawFamily :=
    Option.some.inj (selection.flat_at.symm.trans stagedRawFamilyAt)
  have selectionFlatConstructorEq :
      selection.flatConstructor = rawConstructor := by
    have constructorsEq := congrArg
      (fun family : VInductiveType => family.ctors) selectionFlatFamilyEq
    rw [selection.flat_constructors_eq, rawConstructorsEq] at constructorsEq
    have selected : selection.flatConstructor = rawConstructor ∧ True := by
      simpa only [List.cons.injEq] using constructorsEq
    exact selected.1
  have selectionConstructorRawEq :
      selection.constructor.raw = rawConstructor :=
    selection.constructor_raw_eq.trans selectionFlatConstructorEq
  have selectionFamilyMember : selection.family ∈
      artifact.generation.families :=
    List.mem_iff_getElem?.2 ⟨familyIndex, selection.family_at⟩
  have selectionConstructorMember : selection.constructor ∈
      selection.family.ctorPairs := by
    rw [selection.constructors_eq]
    simp
  have selectionConstructorParamLength :
      (VExpr.telN staged.source.nparams
        selection.constructor.raw.type).length = staged.source.nparams :=
    ((artifact.generation.shape.2.2.2.2 selection.family
      selectionFamilyMember).2.2.2.2.2.2 selection.constructor
        selectionConstructorMember).2.2.1
  have selectionConstructorAritySplit :
      staged.source.nparams +
          (selection.constructor.rawFields staged.source.nparams).length =
        (VInductDecl.ctorFields selection.constructor.raw.type).length := by
    simpa only [selectionConstructorParamLength,
      VInductDecl.NormalizedCtor.rawFields] using
      VExpr.telN_length_add_ctorFields_dropN_length
        staged.source.nparams selection.constructor.raw.type
  have rawConstructorAritySplit :
      (VInductDecl.ctorFields rawConstructor.type).length =
        staged.source.nparams +
          (selection.constructor.rawFields staged.source.nparams).length := by
    rw [← selectionConstructorRawEq]
    exact selectionConstructorAritySplit.symm
  have translatedConstructorAritySplit :
      (VInductDecl.ctorFields translatedConstructor.type).length =
        staged.source.nparams +
          (selection.constructor.rawFields staged.source.nparams).length := by
    simpa only [translatedConstructorEq] using rawConstructorAritySplit
  have flatSourceConstructorArity :
      AddInductive.constructorArity flatSourceConstructor.type 0 =
        staged.source.nparams +
          (selection.constructor.rawFields staged.source.nparams).length :=
    constructorSource.down.sourceArity_eq.trans
      translatedConstructorAritySplit
  have expectedFlatConstructorFields :
      expectedFlatConstructorInfo.numFields =
        (selection.constructor.rawFields staged.source.nparams).length := by
    simp [expectedFlatConstructorInfo,
      AddInductive.declaredConstructorInfo, paramsSize,
      flatSourceConstructorArity, staged.source_nparams_eq]

  let view := restoration.certificate.restoredStructureView selection
  have viewLayout : view.LayoutWF after :=
    restoration.certificate.restoredStructureView_layoutWF selection
  have selectionFamilyMember : selection.family ∈
      artifact.alignedNested.generation.families :=
    List.mem_iff_getElem?.2 ⟨familyIndex, selection.family_at⟩
  have selectionFamilyWF := transaction.stagedCertificate.flatWF.families
    selection.family (by
      rw [transaction.stagedCertificate_nested_eq]
      exact selectionFamilyMember)
  have selectionFamilyWFAfter := selectionFamilyWF.mono
    transaction.stagedCertificate.restored.envLE
  rw [transaction.stagedCertificate_nested_eq] at selectionFamilyWFAfter
  have viewFamilyLayout : view.FamilyLayoutWF after := {
    toLayoutWF := viewLayout
    familyWF := by
      simpa [view,
        VInductDecl.NestedBlockCertificate.restoredStructureView,
        AddInductive.EnvironmentInductiveExecution.FlattenedNestedRestorationResult.certificate] using
        selectionFamilyWFAfter }
  have viewName : view.name = name := by
    change sourceFamily.name = name
    exact sourceFamilyName
  have viewConstructorName : view.constructorName = constructorName := by
    change sourceConstructor.name = constructorName
    exact sourceConstructorName
  have viewRecursorName : view.recursorName = mkRecName name := by
    rw [VRestoredBlockStructureView.recursorName, viewName]
    simp only [mkRecName]
  have viewFieldsLength : view.fields.length =
      (selection.constructor.rawFields staged.source.nparams).length := by
    change (VInductDecl.ctorFields
      (VExpr.dropN artifact.source.nparams sourceConstructor.type)).length = _
    have alignedFlatNparams :
        artifact.alignedNested.elim.flat.nparams = staged.source.nparams := rfl
    simpa only [alignedFlatNparams] using
      selection.source_flat_fields_length_eq
  have constructorNumFields :
      constructorInfo.numFields = view.fields.length :=
    restoredCachedFields.trans <|
      expectedFlatConstructorFields.trans viewFieldsLength.symm
  have constructorNumParams :
      constructorInfo.numParams = artifact.source.nparams :=
    (restoredNestedInfos_constructor_numParams restoredConstructor.1).trans <|
      (ElimNestedInductive.runAt_nparams_eq execution.nestedRun).trans
        artifact.source_nparams_eq.symm
  have infoNumParams : info.numParams = artifact.source.nparams := by
    rw [infoFlatEq, flatInfoEq]
    simp only [AddInductive.declaredInductiveInfo]
    exact artifact.source_nparams_eq.symm

  obtain ⟨translatedFamily, translatedFamilyLookup,
      _translatedFamilyKind, translatedFamilyTr⟩ :=
    transaction.safeTrace.family_translated_lookup inputMapWF
      sourceFamilyMember
  have translatedFamilyLookup' :
      finalEnv.constants.find? name = some translatedFamily := by
    simpa only [sourceFamilyName] using translatedFamilyLookup
  have translatedFamilyEq : translatedFamily = .inductInfo info :=
    Option.some.inj (translatedFamilyLookup'.symm.trans foundMap)
  subst translatedFamily
  have infoLevelParamsLength :
      info.levelParams.length = artifact.source.uvars := by
    have translatedLength := translatedFamilyTr.1.2.1
    change info.levelParams.length = sourceFamily.uvars at translatedLength
    have familyUvars : sourceFamily.uvars = artifact.source.uvars := by
      simpa [view, VInductDecl.NestedBlockCertificate.restoredStructureView]
        using view.family_uvars_eq
    exact translatedLength.trans familyUvars

  have viewRecursorRestoredMember :
      view.recursor ∈ artifact.alignedNested.recursors := by
    exact view.recursor_mem
  have restoredTypeMapWF := restoredMetadata.addTypes.map_wf inputMapWF
  have restoredCtorMapWF := restoredMetadata.addCtors.map_wf
    restoredTypeMapWF
  obtain ⟨translatedRecursor, translatedRecursorLookup,
      _translatedRecursorKind, translatedRecursorTr⟩ :=
    restoredMetadata.addRecs.translated_lookup restoredCtorMapWF
      viewRecursorRestoredMember
  have viewRecursorValueName : view.recursor.name = mkRecName name := by
    simpa [VRestoredBlockStructureView.recursor] using viewRecursorName
  have translatedRecursorLookup' :
      finalEnv.constants.find? (mkRecName name) = some translatedRecursor := by
    simpa only [execution.selectedNestedRestoration_finalEnv_eq numNested_ne,
      viewRecursorValueName] using translatedRecursorLookup
  have translatedRecursorEq : translatedRecursor = .recInfo recursorInfo :=
    Option.some.inj (translatedRecursorLookup'.symm.trans recursorFoundMap)
  subst translatedRecursor
  have recursorLevelParamsLength :
      recursorInfo.levelParams.length = view.nested.generation.recUvars := by
    have translatedLength := translatedRecursorTr.1.2.1
    change recursorInfo.levelParams.length = view.recursor.uvars at translatedLength
    simpa [VRestoredBlockStructureView.recursor,
      VRestoredBlockStructureView.flatRecursor,
      VInductDecl.BlockGenerationChecked.generatedRecursor] using
        translatedLength

  let layout : RestoredProjectionArtifactLayout finalEnv name info after := {
    view := view
    name_eq := viewName
    viewWF := viewFamilyLayout
    constructorInfo := constructorInfo
    constructor_find := by
      simpa only [viewConstructorName] using constructorFound
    recursorInfo := recursorInfo
    recursor_find := by
      simpa only [viewRecursorName] using recursorFound
    recursor_levelParams_length := recursorLevelParamsLength
    constructor_numParams_eq := by
      simpa [view, VInductDecl.NestedBlockCertificate.restoredStructureView]
        using constructorNumParams
    constructor_numFields_eq := constructorNumFields
    levelParams_length := by
      simpa [view, VInductDecl.NestedBlockCertificate.restoredStructureView]
        using infoLevelParamsLength
    numParams_eq := by
      simpa [view, VInductDecl.NestedBlockCertificate.restoredStructureView]
        using infoNumParams
    numIndices_eq := numIndicesEq
    ctors_eq := by
      simpa only [viewConstructorName] using ctorsEq }
  have rawConstructorSource : VInductDecl.CandidateConstructorSourceInput
      staged.enriched.blockEnv lparams flatSourceConstructor rawConstructor := by
    simpa only [translatedConstructorEq] using constructorSource.down
  have stagedSourceUvars : staged.source.uvars = lparams.length := by
    simpa only [FlattenedEnrichedStagingResult.source,
      VInductDecl.CandidateBlockSourceListEnrichment.toRawDecl] using
      staged.family.staging.uvars_eq
  have restoredViewUvars : view.uvars = lparams.length := by
    change artifact.source.uvars = lparams.length
    calc
      artifact.source.uvars = artifact.alignedNested.elim.flat.uvars := by
        simpa using (congrArg VInductDecl.uvars
          artifact.alignedNested.elim.flat_eq).symm
      _ = staged.source.uvars := rfl
      _ = lparams.length := stagedSourceUvars
  have restoredConstructorType : constructorInfo.type =
      execution.nested.restoreNested execution.flattened.recursors.env
        flatSourceConstructor.type := by
    have restored := restoredNestedInfos_constructor_type_of_flat_lookup
      restoredConstructor.1 flatConstructorLookup
    simpa [expectedFlatConstructorInfo,
      AddInductive.declaredConstructorInfo] using restored
  have restoredConstructorLevelParams : constructorInfo.levelParams =
      lparams := by
    have restored :=
      restoredNestedInfos_constructor_levelParams_of_flat_lookup
        restoredConstructor.1 flatConstructorLookup
    calc
      constructorInfo.levelParams = expectedFlatConstructorInfo.levelParams :=
        restored
      _ = execution.flattened.eliminationExecution.constructorContext.lparams :=
        by rfl
      _ = lparams := by
        simpa only [
          AddInductive.NormalizationEliminationExecution.constructorContext]
          using execution.flattenedValidationLparams_eq
  refine ⟨layout, ⟨{
    source_eq := by
      change artifact.source = artifact.source
      rfl
    source_uvars_eq := by
      simpa [layout] using restoredViewUvars
    nested_eq := by
      change HEq view.nested artifact.alignedNested
      rfl
    selection := by
      change Nonempty (VInductDecl.NestedStructureSelection
        artifact.alignedNested familyIndex sourceFamily sourceConstructor)
      exact ⟨selection⟩
    hostFamily := flatSource
    hostFamily_at := by
      simpa [layout, view,
        VInductDecl.NestedBlockCertificate.restoredStructureView] using
        flatSourceAt
    hostConstructor := flatSourceConstructor
    hostConstructor_at := flatSourceConstructorAt
    rawConstructor := rawConstructor
    sourceInput := rawConstructorSource
    rawConstructor_eq := by
      simpa [layout, view,
        VInductDecl.NestedBlockCertificate.restoredStructureView] using
        selectionFlatConstructorEq.symm
    restored_type_eq := restoredConstructorType
    constructor_levelParams_eq := restoredConstructorLevelParams }⟩⟩

/-- The exact nested transaction translates the public restored constructor
record selected by a layout, at the layout's retained host universe names.
This fact is intentionally separated from parameter auditing and runtime
dependency support: it comes solely from the final constructor insertion
trace and uniqueness of the public host lookup. -/
theorem RestoredProjectionParameterSource.finalConstructorTr
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    {flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape}
    {metadata : VInductDecl.ExactProducedBlockMetadataPrefixRun flat.run}
    {after : VEnv}
    {restoration : execution.FlattenedNestedRestorationResult artifact after}
    {numNested_ne : execution.nested.aux2nested.size ≠ 0}
    {restoredMetadata :
      execution.FlattenedNestedRestoredMetadataPrefixRun restoration
        numNested_ne}
    (transaction : execution.FlattenedExactNestedTransactionResult flat
      metadata restoration numNested_ne restoredMetadata)
    (wf : ves.WF env)
    {name : Name} {info : InductiveVal}
    {layout : RestoredProjectionArtifactLayout finalEnv name info after}
    (source : execution.RestoredProjectionParameterSource staged artifact
      layout) :
    TrExprS after lparams [] layout.constructorInfo.type
      layout.view.sourceConstructor.type := by
  have sourceConstructorMember : layout.view.sourceConstructor ∈
      artifact.source.blockConstructorConstants := by
    have member : layout.view.sourceConstructor ∈
        layout.view.source.blockConstructorConstants := by
      simp only [VInductDecl.blockConstructorConstants, List.mem_flatMap]
      exact ⟨layout.view.sourceFamily, layout.view.sourceFamily_mem,
        layout.view.sourceConstructor_mem⟩
    simpa only [source.source_eq] using member
  have inputMapWF := (wf.tr (safety := .safe)).map_wf
  obtain ⟨translated, translatedLookup, _translatedKind, translatedTr⟩ :=
    transaction.safeTrace.constructor_translated_lookup inputMapWF
      sourceConstructorMember
  have finalMapWF := execution.nestedFinalMapWF numNested_ne inputMapWF
  have layoutConstructorLookup :
      finalEnv.constants.find? layout.view.constructorName =
        some (.ctorInfo layout.constructorInfo) := by
    have found := layout.constructor_find
    change finalEnv.constants.find?' layout.view.constructorName = _ at found
    rwa [finalMapWF.find?'_eq_find?] at found
  have translatedLookup' :
      finalEnv.constants.find? layout.view.constructorName =
        some translated :=
    translatedLookup
  have translatedEq : translated = .ctorInfo layout.constructorInfo :=
    Option.some.inj (translatedLookup'.symm.trans layoutConstructorLookup)
  subst translated
  have translatedTypeTr := translatedTr.1.2.2
  change TrExprS after layout.constructorInfo.levelParams []
    layout.constructorInfo.type layout.view.sourceConstructor.type at translatedTypeTr
  rw [source.constructor_levelParams_eq] at translatedTypeTr
  exact translatedTypeTr

/-- Retain the flattened projector algebra from the exact generation
transaction without claiming that its registrations survive at the restored
public endpoint.  The dependent transport aligns the layout-selected nested
descriptor with the producer-owned artifact before forgetting the staging
environment. -/
theorem RestoredProjectionParameterSource.flatOperationalCodeNaturality
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    {flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape}
    {metadata : VInductDecl.ExactProducedBlockMetadataPrefixRun flat.run}
    {after : VEnv}
    {restoration : execution.FlattenedNestedRestorationResult artifact after}
    {numNested_ne : execution.nested.aux2nested.size ≠ 0}
    {restoredMetadata :
      execution.FlattenedNestedRestoredMetadataPrefixRun restoration
        numNested_ne}
    (transaction : execution.FlattenedExactNestedTransactionResult flat
      metadata restoration numNested_ne restoredMetadata)
    {name : Name} {info : InductiveVal}
    {layout : RestoredProjectionArtifactLayout finalEnv name info after}
    (source : execution.RestoredProjectionParameterSource staged artifact
      layout) :
    layout.view.flatView.OperationalCodeNaturality := by
  let flatAfter := artifact.generation.generatedRules.foldl VEnv.addDefEq
    metadata.recursors.recEnv
  have pairEq :
      (⟨layout.view.source, layout.view.nested⟩ :
        Sigma VInductDecl.NestedBlockChecked) =
      ⟨artifact.source, artifact.alignedNested⟩ :=
    Sigma.ext source.source_eq source.nested_eq
  let GenerationEnvAt := fun
      pair : Sigma VInductDecl.NestedBlockChecked =>
    VInductDecl.BlockGenerationEnv pair.2.generation flatAfter
  have artifactGenerationEnv : GenerationEnvAt
      ⟨artifact.source, artifact.alignedNested⟩ := by
    change VInductDecl.BlockGenerationEnv
      artifact.alignedNested.generation flatAfter
    rw [← transaction.stagedCertificate_nested_eq]
    exact transaction.stagedCertificate.flatCertificate.generationEnv
  have viewGenerationEnv : GenerationEnvAt
      ⟨layout.view.source, layout.view.nested⟩ :=
    pairEq.symm ▸ artifactGenerationEnv
  let syntaxWF : layout.view.flatView.ProjectionSyntaxWF flatAfter := {
    generationEnv := by
      change VInductDecl.BlockGenerationEnv
        layout.view.nested.generation flatAfter
      exact viewGenerationEnv }
  exact syntaxWF.operationalCodeNaturality

/-- Fold the producer's exact raw constructor audit through nested
restoration and the final constructor translation.  The resulting telescope
equality is precisely the extra parameter-layout contract required by the
restored projection backend; no raw constructor, family position, or final
endpoint is reselected by the consumer. -/
theorem RestoredProjectionParameterSource.constructorParameterLayoutWF
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    {flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape}
    {metadata : VInductDecl.ExactProducedBlockMetadataPrefixRun flat.run}
    {after : VEnv}
    {restoration : execution.FlattenedNestedRestorationResult artifact after}
    {numNested_ne : execution.nested.aux2nested.size ≠ 0}
    {restoredMetadata :
      execution.FlattenedNestedRestoredMetadataPrefixRun restoration
        numNested_ne}
    (transaction : execution.FlattenedExactNestedTransactionResult flat
      metadata restoration numNested_ne restoredMetadata)
    (wf : ves.WF env)
    {name : Name} {info : InductiveVal}
    {layout : RestoredProjectionArtifactLayout finalEnv name info after}
    (source : execution.RestoredProjectionParameterSource staged artifact
      layout)
    (basis : VInductDecl.ConstructorRawPreFamilyParameterAuditBasis
      (ves.venv .safe) lparams
      (staged.recursorShape shape).execution.eliminationExecution.normalization.stats
      (staged.recursorShape shape).execution.eliminationExecution.normalization.validationContext
      staged.source.nparams artifact.generation.block.checked.params)
    (rawAudit : VInductDecl.ProducedBlockRawHostParameterAuditRun
      (staged.recursorShape shape)) :
    layout.view.ConstructorParameterLayoutWF after := by
  obtain ⟨blockSemantic⟩ := rawAudit.semanticRuns basis.contextRun
  obtain ⟨⟨constructorTrace, constructorSemantic⟩⟩ :=
    blockSemantic.constructor_getElem?_nonempty source.hostFamily_at
      source.hostConstructor_at
  have statsParamsEq :
      (staged.recursorShape shape).execution.eliminationExecution.normalization.stats.params.size =
        execution.nested.nparams :=
    basis.params_size.trans <|
      staged.source_nparams_eq.trans
        (ElimNestedInductive.runAt_nparams_eq execution.nestedRun).symm
  have flatShape := constructorTrace.forallPrefixEq_self basis.localState
  rw [statsParamsEq] at flatShape
  have hostConstructorFVars : source.hostConstructor.type.FVarsIn
      (fun _ => False) := by
    simpa using source.sourceInput.source_tr.fvarsIn
  have restoredShape := execution.nested.restoreNested_forallPrefixEq
    execution.flattened.recursors.env flatShape hostConstructorFVars
  rw [← source.restored_type_eq] at restoredShape
  have restoredShape' : AddInductive.ConstructorForallPrefixEq
      ((staged.recursorShape shape).execution.eliminationExecution.normalization.stats.params.size - 0)
      source.hostConstructor.type layout.constructorInfo.type := by
    simpa only [Nat.sub_zero, statsParamsEq] using restoredShape
  obtain ⟨⟨_restoredTrace, restoredSemantic⟩⟩ :=
    constructorSemantic.reindex_nonempty restoredShape'
  have finalConstructorTr := source.finalConstructorTr transaction wf
  have folded := basis.foldInTarget
    transaction.stagedCertificate.restored.envLE
    transaction.stagedCertificate.restored.afterWF finalConstructorTr
      restoredSemantic
  have viewNparamsEq : layout.view.nparams = staged.source.nparams := by
    exact (congrArg VInductDecl.nparams source.source_eq).trans <|
      artifact.source_nparams_eq.trans staged.source_nparams_eq.symm
  have pairEq :
      (⟨layout.view.source, layout.view.nested⟩ :
        Sigma VInductDecl.NestedBlockChecked) =
      ⟨artifact.source, artifact.alignedNested⟩ :=
    Sigma.ext source.source_eq source.nested_eq
  let flatAfter := artifact.generation.generatedRules.foldl VEnv.addDefEq
    metadata.recursors.recEnv
  let GenerationEnvAt := fun
      pair : Sigma VInductDecl.NestedBlockChecked =>
    VInductDecl.BlockGenerationEnv pair.2.generation flatAfter
  have artifactGenerationEnv : GenerationEnvAt
      ⟨artifact.source, artifact.alignedNested⟩ := by
    change VInductDecl.BlockGenerationEnv
      artifact.alignedNested.generation flatAfter
    rw [← transaction.stagedCertificate_nested_eq]
    exact transaction.stagedCertificate.flatCertificate.generationEnv
  have viewGenerationEnv : GenerationEnvAt
      ⟨layout.view.source, layout.view.nested⟩ :=
    pairEq.symm ▸ artifactGenerationEnv
  have viewRecEntriesClosed :
      VInductDecl.RestoreEntriesClosed layout.view.nested.recEntries := by
    have closed := restoration.recEntriesClosed
    have entriesEq := congrArg
      (fun packed : Sigma VInductDecl.NestedBlockChecked =>
        packed.2.recEntries) pairEq
    rw [entriesEq]
    exact closed
  have generationParamsEq :
      layout.view.nested.generation.block.checked.params =
        artifact.generation.block.checked.params := by
    have aligned := congrArg
      (fun pair : Sigma VInductDecl.NestedBlockChecked =>
        pair.2.generation.block.checked.params) pairEq
    exact aligned.trans (by rfl)
  apply layout.viewWF.withFlatConstructorParameters
  rw [layout.view.flatView_constructorParams,
    VRestoredBlockStructureView.constructorParams, source.source_uvars_eq,
    viewNparamsEq, generationParamsEq]
  exact folded.telDefEq
  exact layout.viewWF.restoredRecType_generated_defeq
    transaction.stagedCertificate.restored.afterWF (by
      change VInductDecl.BlockGenerationEnv
        layout.view.nested.generation flatAfter
      exact viewGenerationEnv) viewRecEntriesClosed

/-- Restore the Theory side of the exact flattened constructor dependency
witness retained by the producer.  This is the complete target-side runtime
handoff: its count is the public restored parameter/field boundary and its
target is the literal registered source constructor.  The host source remains
the flattened constructor type on purpose; transporting that source through
`ElimNestedInductive.Result.restoreNested` is the sole remaining operational
restoration obligation. -/
theorem RestoredProjectionParameterSource.flatHostProjectionSpineSupport
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    {flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape}
    {metadata : VInductDecl.ExactProducedBlockMetadataPrefixRun flat.run}
    {after : VEnv}
    {restoration : execution.FlattenedNestedRestorationResult artifact after}
    {numNested_ne : execution.nested.aux2nested.size ≠ 0}
    {restoredMetadata :
      execution.FlattenedNestedRestoredMetadataPrefixRun restoration
        numNested_ne}
    (transaction : execution.FlattenedExactNestedTransactionResult flat
      metadata restoration numNested_ne restoredMetadata)
    {name : Name} {info : InductiveVal}
    {layout : RestoredProjectionArtifactLayout finalEnv name info after}
    (source : execution.RestoredProjectionParameterSource staged artifact
      layout) :
    ProjectionSpineSupport
      (layout.view.nparams + layout.view.fields.length)
      source.hostConstructor.type layout.view.sourceConstructor.type := by
  have pairEq :
      (⟨layout.view.source, layout.view.nested⟩ :
        Sigma VInductDecl.NestedBlockChecked) =
      ⟨artifact.source, artifact.alignedNested⟩ :=
    Sigma.ext source.source_eq source.nested_eq
  let CertificateAt := fun
      pair : Sigma VInductDecl.NestedBlockChecked =>
    Sigma fun certificate : VInductDecl.NestedBlockCertificate pair.1
        (ves.venv .safe) after =>
      PLift (certificate.nested = pair.2)
  let artifactCertificate : CertificateAt
      ⟨artifact.source, artifact.alignedNested⟩ :=
    ⟨transaction.stagedCertificate.restored,
      ⟨transaction.stagedCertificate_nested_eq⟩⟩
  let viewCertificate : CertificateAt
      ⟨layout.view.source, layout.view.nested⟩ :=
    pairEq.symm ▸ artifactCertificate
  have viewCertificateNested :
      viewCertificate.1.nested = layout.view.nested := by
    simpa only using viewCertificate.2.down
  let certificate : VInductDecl.NestedBlockCertificate layout.view.source
      (ves.venv .safe) after := {
    nested := layout.view.nested
    semantic := by
      rw [← viewCertificateNested]
      exact viewCertificate.1.semantic
    success := by
      rw [← viewCertificateNested]
      exact viewCertificate.1.success
    beforeWF := viewCertificate.1.beforeWF }
  have flatSupport := source.sourceInput.spineSupport
  rw [source.rawConstructor_eq] at flatSupport
  let TargetsAt := fun pair : Sigma VInductDecl.NestedBlockChecked =>
    VInductDecl.NestedTargetsWF (ves.venv .safe) pair.2.elim.targets
  have artifactTargetsWF : TargetsAt
      ⟨artifact.source, artifact.alignedNested⟩ := by
    rw [artifact.alignedNested_eq]
    exact artifact.targetsWF
  have targetsWF : TargetsAt
      ⟨layout.view.source, layout.view.nested⟩ :=
    pairEq.symm ▸ artifactTargetsWF
  have restoredSupport :=
    certificate.restoreProjectionSpineSupport targetsWF
      layout.view.selection flatSupport
  have countEq :
      (VInductDecl.ctorFields
        layout.view.selection.flatConstructor.type).length =
        layout.view.nparams + layout.view.fields.length := by
    calc
      (VInductDecl.ctorFields
          layout.view.selection.flatConstructor.type).length =
          VInductDecl.VExpr.nestedArity
            layout.view.selection.flatConstructor.type :=
        (VInductDecl.VExpr.nestedArity_eq_ctorFields_length _).symm
      _ = VInductDecl.VExpr.nestedArity
          layout.view.sourceConstructor.type := by
        simpa [VInductDecl.VConstVal.nestedHeader] using
          congrArg VInductDecl.NestedCtorHeader.arity
            layout.view.selection.constructor_header_eq
      _ = (VInductDecl.ctorFields
          layout.view.sourceConstructor.type).length :=
        VInductDecl.VExpr.nestedArity_eq_ctorFields_length _
      _ = layout.view.nparams + layout.view.fields.length :=
        layout.view.constructorSpine_length.symm
  rw [countEq] at restoredSupport
  exact restoredSupport

/-- Producer-complete restored projection handoff immediately before the
host-source dependency transport.  Every selectable component is indexed by
the exact nested transaction: the public metadata layout, its audited raw
host constructor, the restored constructor parameter telescope, the final
strict constructor translation, and the dependency witness whose Theory
target has already been restored.  The only datum deliberately absent is a
`ProjectionFieldSpineSupport` witness with `layout.constructorInfo.type` as
its host source. -/
structure RestoredProjectionRuntimeHandoff
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    (execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv)
    {ves : VEnvs}
    (staged : execution.FlattenedEnrichedStagingResult ves)
    (artifact : execution.FlattenedNestedArtifact staged)
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    {flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape}
    {metadata : VInductDecl.ExactProducedBlockMetadataPrefixRun flat.run}
    {after : VEnv}
    {restoration : execution.FlattenedNestedRestorationResult artifact after}
    {numNested_ne : execution.nested.aux2nested.size ≠ 0}
    {restoredMetadata :
      execution.FlattenedNestedRestoredMetadataPrefixRun restoration
        numNested_ne}
    (transaction : execution.FlattenedExactNestedTransactionResult flat
      metadata restoration numNested_ne restoredMetadata)
    (name : Name) (info : InductiveVal) where
  layout : RestoredProjectionArtifactLayout finalEnv name info after
  source : execution.RestoredProjectionParameterSource staged artifact layout
  recEntriesClosed :
    VInductDecl.RestoreEntriesClosed layout.view.nested.recEntries
  codeNaturality : layout.view.flatView.OperationalCodeNaturality
  parameterLayout : layout.view.ConstructorParameterLayoutWF after
  finalConstructorTr : TrExprS after lparams [] layout.constructorInfo.type
    layout.view.sourceConstructor.type
  flatHostSpineSupport : ProjectionFieldSpineSupport
    layout.view.nparams layout.view.fields.length
    source.hostConstructor.type layout.view.sourceConstructor.type

/-- The sole missing producer transformation at a restored runtime handoff:
the host kernel's `restoreNested` rewrite must retain the common parameter Pi
shape and reflect field independence back to the flattened host constructor.
This structural contract contains exactly the information needed to
transport the already-restored Theory dependency witness. -/
def RestoredProjectionRuntimeHandoff.HostSourceDependencyTransport
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    {flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape}
    {metadata : VInductDecl.ExactProducedBlockMetadataPrefixRun flat.run}
    {after : VEnv}
    {restoration : execution.FlattenedNestedRestorationResult artifact after}
    {numNested_ne : execution.nested.aux2nested.size ≠ 0}
    {restoredMetadata :
      execution.FlattenedNestedRestoredMetadataPrefixRun restoration
        numNested_ne}
    {transaction : execution.FlattenedExactNestedTransactionResult flat
      metadata restoration numNested_ne restoredMetadata}
    {name : Name} {info : InductiveVal}
    (handoff : execution.RestoredProjectionRuntimeHandoff staged artifact
      transaction name info) : Prop :=
  ProjectionFieldSourceTransport
    handoff.layout.view.nparams handoff.layout.view.fields.length
    handoff.source.hostConstructor.type handoff.layout.constructorInfo.type

/-- Generator-facing form of the remaining restoration obligation.  Unlike
the derived telescope transport, this proposition follows the actual public
`restoreNested` execution: it opens the exact shared-parameter prefix with
the kernel's fresh FVars and requires dependency-reflecting callback nodes in
the terminal generated constructor body. -/
def RestoredProjectionRuntimeHandoff.HostSourceRestorationSafety
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    {flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape}
    {metadata : VInductDecl.ExactProducedBlockMetadataPrefixRun flat.run}
    {after : VEnv}
    {restoration : execution.FlattenedNestedRestorationResult artifact after}
    {numNested_ne : execution.nested.aux2nested.size ≠ 0}
    {restoredMetadata :
      execution.FlattenedNestedRestoredMetadataPrefixRun restoration
        numNested_ne}
    {transaction : execution.FlattenedExactNestedTransactionResult flat
      metadata restoration numNested_ne restoredMetadata}
    {name : Name} {info : InductiveVal}
    (handoff : execution.RestoredProjectionRuntimeHandoff staged artifact
      transaction name info) : Prop :=
  execution.nested.RestoreNestedDependencySafe
    execution.flattened.recursors.env handoff.source.hostConstructor.type

/-- Every transaction-indexed handoff inherits restoration safety from the
successful public nested-elimination execution.  The handoff's exact family
and constructor positions select the corresponding entry of the checked
emitted inventory; no additional generator premise remains. -/
theorem RestoredProjectionRuntimeHandoff.hostSourceRestorationSafety
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    {flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape}
    {metadata : VInductDecl.ExactProducedBlockMetadataPrefixRun flat.run}
    {after : VEnv}
    {restoration : execution.FlattenedNestedRestorationResult artifact after}
    {numNested_ne : execution.nested.aux2nested.size ≠ 0}
    {restoredMetadata :
      execution.FlattenedNestedRestoredMetadataPrefixRun restoration
        numNested_ne}
    {transaction : execution.FlattenedExactNestedTransactionResult flat
      metadata restoration numNested_ne restoredMetadata}
    {name : Name} {info : InductiveVal}
    (handoff : execution.RestoredProjectionRuntimeHandoff staged artifact
      transaction name info) :
    handoff.HostSourceRestorationSafety :=
  execution.nested.restoreNestedDependencySafe_ofInventoryCheck
    execution.flattened.recursors.env
    (ElimNestedInductive.runAt_restorationDependencyCheck execution.nestedRun)
    handoff.source.hostFamily_at handoff.source.hostConstructor_at

/-- The exact public restoration-safety trace constructs the handoff's sole
host-source transport field.  Parameter-count alignment comes from the same
nested execution and semantic source retained by the handoff; constructor
closedness comes from its exact strict source translation. -/
theorem RestoredProjectionRuntimeHandoff.hostSourceDependencyTransport_ofRestorationSafety
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    {flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape}
    {metadata : VInductDecl.ExactProducedBlockMetadataPrefixRun flat.run}
    {after : VEnv}
    {restoration : execution.FlattenedNestedRestorationResult artifact after}
    {numNested_ne : execution.nested.aux2nested.size ≠ 0}
    {restoredMetadata :
      execution.FlattenedNestedRestoredMetadataPrefixRun restoration
        numNested_ne}
    {transaction : execution.FlattenedExactNestedTransactionResult flat
      metadata restoration numNested_ne restoredMetadata}
    {name : Name} {info : InductiveVal}
    (handoff : execution.RestoredProjectionRuntimeHandoff staged artifact
      transaction name info)
    (safe : handoff.HostSourceRestorationSafety) :
    handoff.HostSourceDependencyTransport := by
  have viewNparamsEq :
      handoff.layout.view.nparams = execution.nested.nparams :=
    (congrArg VInductDecl.nparams handoff.source.source_eq).trans <|
      artifact.source_nparams_eq.trans
        (ElimNestedInductive.runAt_nparams_eq execution.nestedRun).symm
  have closed : handoff.source.hostConstructor.type.FVarsIn
      (fun _ => False) := by
    simpa using handoff.source.sourceInput.source_tr.fvarsIn
  have support : ProjectionFieldSpineSupport execution.nested.nparams
      handoff.layout.view.fields.length handoff.source.hostConstructor.type
      handoff.layout.view.sourceConstructor.type := by
    rw [← viewNparamsEq]
    exact handoff.flatHostSpineSupport
  have transport := execution.nested.restoreNested_fieldSourceTransport
    execution.flattened.recursors.env support closed safe
  rw [← handoff.source.restored_type_eq] at transport
  change ProjectionFieldSourceTransport handoff.layout.view.nparams
    handoff.layout.view.fields.length handoff.source.hostConstructor.type
    handoff.layout.constructorInfo.type
  rw [viewNparamsEq]
  exact transport

/-- Complete a transaction-indexed restored handoff once host nested
restoration is known to preserve the exact dependency spine.  This method
accepts no alternate layout, constructor, transaction, or endpoint. -/
def RestoredProjectionRuntimeHandoff.completeRuntime
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    {flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape}
    {metadata : VInductDecl.ExactProducedBlockMetadataPrefixRun flat.run}
    {after : VEnv}
    {restoration : execution.FlattenedNestedRestorationResult artifact after}
    {numNested_ne : execution.nested.aux2nested.size ≠ 0}
    {restoredMetadata :
      execution.FlattenedNestedRestoredMetadataPrefixRun restoration
        numNested_ne}
    {transaction : execution.FlattenedExactNestedTransactionResult flat
      metadata restoration numNested_ne restoredMetadata}
    {name : Name} {info : InductiveVal}
    (handoff : execution.RestoredProjectionRuntimeHandoff staged artifact
      transaction name info)
    (transport : handoff.HostSourceDependencyTransport) :
    RestoredProjectionArtifact finalEnv name info after :=
  RestoredProjectionArtifact.ofRuntime handoff.layout
    handoff.recEntriesClosed handoff.codeNaturality handoff.parameterLayout
      (handoff.flatHostSpineSupport.transportSource transport)

/-- Complete the restored runtime artifact directly from the executable
public-restoration safety trace.  The telescope transport consumed by the
runtime constructor is derived rather than exposed to the producer. -/
def RestoredProjectionRuntimeHandoff.completeRuntime_ofRestorationSafety
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    {flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape}
    {metadata : VInductDecl.ExactProducedBlockMetadataPrefixRun flat.run}
    {after : VEnv}
    {restoration : execution.FlattenedNestedRestorationResult artifact after}
    {numNested_ne : execution.nested.aux2nested.size ≠ 0}
    {restoredMetadata :
      execution.FlattenedNestedRestoredMetadataPrefixRun restoration
        numNested_ne}
    {transaction : execution.FlattenedExactNestedTransactionResult flat
      metadata restoration numNested_ne restoredMetadata}
    {name : Name} {info : InductiveVal}
    (handoff : execution.RestoredProjectionRuntimeHandoff staged artifact
      transaction name info)
    (safe : handoff.HostSourceRestorationSafety) :
    RestoredProjectionArtifact finalEnv name info after :=
  handoff.completeRuntime
    (handoff.hostSourceDependencyTransport_ofRestorationSafety safe)

/-- Complete a restored runtime handoff solely from its exact producer
execution and transaction indexes. -/
def RestoredProjectionRuntimeHandoff.completeRuntimeChecked
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    {flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape}
    {metadata : VInductDecl.ExactProducedBlockMetadataPrefixRun flat.run}
    {after : VEnv}
    {restoration : execution.FlattenedNestedRestorationResult artifact after}
    {numNested_ne : execution.nested.aux2nested.size ≠ 0}
    {restoredMetadata :
      execution.FlattenedNestedRestoredMetadataPrefixRun restoration
        numNested_ne}
    {transaction : execution.FlattenedExactNestedTransactionResult flat
      metadata restoration numNested_ne restoredMetadata}
    {name : Name} {info : InductiveVal}
    (handoff : execution.RestoredProjectionRuntimeHandoff staged artifact
      transaction name info) :
    RestoredProjectionArtifact finalEnv name info after :=
  handoff.completeRuntime_ofRestorationSafety
    handoff.hostSourceRestorationSafety

/-- Construct the restored metadata layout together with its exact
constructor-parameter telescope contract from one transaction-indexed audit
support package.  This is the producer-facing handoff immediately preceding
operational restored projector construction. -/
theorem
    FlattenedExactNestedTransactionResult.restoredProjectionArtifactParameterLayout
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    {flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape}
    {metadata : VInductDecl.ExactProducedBlockMetadataPrefixRun flat.run}
    {after : VEnv}
    {restoration : execution.FlattenedNestedRestorationResult artifact after}
    {numNested_ne : execution.nested.aux2nested.size ≠ 0}
    {restoredMetadata :
      execution.FlattenedNestedRestoredMetadataPrefixRun restoration
        numNested_ne}
    (transaction : execution.FlattenedExactNestedTransactionResult flat
      metadata restoration numNested_ne restoredMetadata)
    (support : execution.RestoredProjectionParameterAuditSupport staged
      artifact shape)
    (wf : ves.WF env) {name : Name} {info : InductiveVal}
    (found : finalEnv.find? name = some (.inductInfo info))
    (ready : finalEnv.isProjectionReadyStructure name = true)
    (notOld : ¬ (env.find? name = some (.inductInfo info) ∧
      env.isProjectionReadyStructure name = true)) :
    ∃ layout : RestoredProjectionArtifactLayout finalEnv name info after,
      Nonempty (execution.RestoredProjectionParameterSource staged artifact
        layout) ∧
      layout.view.ConstructorParameterLayoutWF after := by
  obtain ⟨layout, ⟨source⟩⟩ :=
    transaction.restoredProjectionArtifactLayoutSource wf found ready notOld
  have parameterLayout := source.constructorParameterLayoutWF transaction wf
    support.basis support.rawAudit
  exact ⟨layout, ⟨source⟩, parameterLayout⟩

/-- The projection-parameter wrapper feeds its retained producer witnesses
directly into restored layout construction.  No audit support value remains
as a caller-selectable argument at this handoff. -/
theorem
    FlattenedExactNestedProjectionParameterRun.restoredProjectionArtifactParameterLayout
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    {flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape}
    {metadata : VInductDecl.ExactProducedBlockMetadataPrefixRun flat.run}
    {after : VEnv}
    {restoration : execution.FlattenedNestedRestorationResult artifact after}
    {numNested_ne : execution.nested.aux2nested.size ≠ 0}
    {restoredMetadata :
      execution.FlattenedNestedRestoredMetadataPrefixRun restoration
        numNested_ne}
    (run : execution.FlattenedExactNestedProjectionParameterRun flat metadata
      restoration numNested_ne restoredMetadata)
    (wf : ves.WF env) {name : Name} {info : InductiveVal}
    (found : finalEnv.find? name = some (.inductInfo info))
    (ready : finalEnv.isProjectionReadyStructure name = true)
    (notOld : ¬ (env.find? name = some (.inductInfo info) ∧
      env.isProjectionReadyStructure name = true)) :
    ∃ layout : RestoredProjectionArtifactLayout finalEnv name info after,
      Nonempty (execution.RestoredProjectionParameterSource staged artifact
        layout) ∧
      layout.view.ConstructorParameterLayoutWF after :=
  run.transaction.restoredProjectionArtifactParameterLayout
    run.parameterAuditSupport wf found ready notOld

/-- A newly projection-ready source family in the exact nested replay
constructs the complete runtime handoff up to host-source dependency
transport.  In particular, the caller supplies only the final host lookup
facts used to identify a newly activated family; all layout, audit,
translation, and flattened-producer witnesses come from `run`. -/
theorem
    FlattenedExactNestedProjectionParameterRun.restoredProjectionRuntimeHandoff
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    {flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape}
    {metadata : VInductDecl.ExactProducedBlockMetadataPrefixRun flat.run}
    {after : VEnv}
    {restoration : execution.FlattenedNestedRestorationResult artifact after}
    {numNested_ne : execution.nested.aux2nested.size ≠ 0}
    {restoredMetadata :
      execution.FlattenedNestedRestoredMetadataPrefixRun restoration
        numNested_ne}
    (run : execution.FlattenedExactNestedProjectionParameterRun flat metadata
      restoration numNested_ne restoredMetadata)
    (wf : ves.WF env) {name : Name} {info : InductiveVal}
    (found : finalEnv.find? name = some (.inductInfo info))
    (ready : finalEnv.isProjectionReadyStructure name = true)
    (notOld : ¬ (env.find? name = some (.inductInfo info) ∧
      env.isProjectionReadyStructure name = true)) :
    Nonempty (execution.RestoredProjectionRuntimeHandoff staged artifact
      run.transaction name info) := by
  obtain ⟨layout, ⟨source⟩, parameterLayout⟩ :=
    run.restoredProjectionArtifactParameterLayout wf found ready notOld
  exact ⟨{
    layout := layout
    source := source
    recEntriesClosed := by
      have closed := restoration.recEntriesClosed
      let selected : Σ declaration : VInductDecl,
          declaration.NestedBlockChecked :=
        ⟨layout.view.source, layout.view.nested⟩
      let aligned : Σ declaration : VInductDecl,
          declaration.NestedBlockChecked :=
        ⟨artifact.source, artifact.alignedNested⟩
      have pairEq : selected = aligned :=
        Sigma.ext source.source_eq source.nested_eq
      have entriesEq := congrArg
        (fun packed : Σ declaration : VInductDecl,
          declaration.NestedBlockChecked => packed.2.recEntries) pairEq
      change VInductDecl.RestoreEntriesClosed selected.2.recEntries
      rw [entriesEq]
      exact closed
    codeNaturality := source.flatOperationalCodeNaturality run.transaction
    parameterLayout := parameterLayout
    finalConstructorTr := source.finalConstructorTr run.transaction wf
    flatHostSpineSupport :=
      (source.flatHostProjectionSpineSupport run.transaction)
        |>.toFieldSpineSupport }⟩

/-- The exact nested producer owns the complete runtime-handoff delta for
every newly activated projection-ready family. -/
theorem
    FlattenedExactNestedProjectionParameterRun.restoredProjectionRuntimeHandoffDeltaReady
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    {flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape}
    {metadata : VInductDecl.ExactProducedBlockMetadataPrefixRun flat.run}
    {after : VEnv}
    {restoration : execution.FlattenedNestedRestorationResult artifact after}
    {numNested_ne : execution.nested.aux2nested.size ≠ 0}
    {restoredMetadata :
      execution.FlattenedNestedRestoredMetadataPrefixRun restoration
        numNested_ne}
    (run : execution.FlattenedExactNestedProjectionParameterRun flat metadata
      restoration numNested_ne restoredMetadata)
    (wf : ves.WF env) :
    ∀ name info, finalEnv.find? name = some (.inductInfo info) →
      finalEnv.isProjectionReadyStructure name = true →
      ¬ (env.find? name = some (.inductInfo info) ∧
        env.isProjectionReadyStructure name = true) →
      Nonempty (execution.RestoredProjectionRuntimeHandoff staged artifact
        run.transaction name info) := by
  intro name info found ready notOld
  exact run.restoredProjectionRuntimeHandoff wf found ready notOld

/-- Once the single host-source dependency transformation is proved for
transaction-indexed handoffs, the exact nested producer constructs the
restored artifact delta required by resolution-aware readiness. -/
theorem
    FlattenedExactNestedProjectionParameterRun.restoredProjectionArtifactDeltaReady_ofHostSourceDependencyTransport
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    {flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape}
    {metadata : VInductDecl.ExactProducedBlockMetadataPrefixRun flat.run}
    {after : VEnv}
    {restoration : execution.FlattenedNestedRestorationResult artifact after}
    {numNested_ne : execution.nested.aux2nested.size ≠ 0}
    {restoredMetadata :
      execution.FlattenedNestedRestoredMetadataPrefixRun restoration
        numNested_ne}
    (run : execution.FlattenedExactNestedProjectionParameterRun flat metadata
      restoration numNested_ne restoredMetadata)
    (wf : ves.WF env)
    (transport : ∀ {name info}
      (handoff : execution.RestoredProjectionRuntimeHandoff staged artifact
        run.transaction name info),
      handoff.HostSourceDependencyTransport) :
    RestoredProjectionArtifactDeltaReady env finalEnv after := by
  intro name info found ready notOld
  obtain ⟨handoff⟩ :=
    run.restoredProjectionRuntimeHandoff wf found ready notOld
  exact ⟨handoff.completeRuntime (transport handoff)⟩

/-- The same transaction-indexed host-source transformation supplies the
consumer-facing migration delta directly.  This is the contract consumed by
resolution-aware projection inference: every newly ready family resolves to
the restored backend, without first being misclassified as an ordinary block
artifact at the public endpoint. -/
theorem
    FlattenedExactNestedProjectionParameterRun.projectionArtifactResolutionDeltaReady_ofHostSourceDependencyTransport
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    {flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape}
    {metadata : VInductDecl.ExactProducedBlockMetadataPrefixRun flat.run}
    {after : VEnv}
    {restoration : execution.FlattenedNestedRestorationResult artifact after}
    {numNested_ne : execution.nested.aux2nested.size ≠ 0}
    {restoredMetadata :
      execution.FlattenedNestedRestoredMetadataPrefixRun restoration
        numNested_ne}
    (run : execution.FlattenedExactNestedProjectionParameterRun flat metadata
      restoration numNested_ne restoredMetadata)
    (wf : ves.WF env)
    (transport : ∀ {name info}
      (handoff : execution.RestoredProjectionRuntimeHandoff staged artifact
        run.transaction name info),
      handoff.HostSourceDependencyTransport) :
    ProjectionArtifactResolutionDeltaReady env finalEnv after :=
  (run.restoredProjectionArtifactDeltaReady_ofHostSourceDependencyTransport
    wf transport).toResolution

/-- The exact nested producer constructs its restored artifact delta once its
generated constructor bodies satisfy the public `restoreNested` execution
trace.  No caller-provided telescope transport remains in this interface. -/
theorem
    FlattenedExactNestedProjectionParameterRun.restoredProjectionArtifactDeltaReady_ofHostSourceRestorationSafety
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    {flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape}
    {metadata : VInductDecl.ExactProducedBlockMetadataPrefixRun flat.run}
    {after : VEnv}
    {restoration : execution.FlattenedNestedRestorationResult artifact after}
    {numNested_ne : execution.nested.aux2nested.size ≠ 0}
    {restoredMetadata :
      execution.FlattenedNestedRestoredMetadataPrefixRun restoration
        numNested_ne}
    (run : execution.FlattenedExactNestedProjectionParameterRun flat metadata
      restoration numNested_ne restoredMetadata)
    (wf : ves.WF env)
    (safe : ∀ {name info}
      (handoff : execution.RestoredProjectionRuntimeHandoff staged artifact
        run.transaction name info),
      handoff.HostSourceRestorationSafety) :
    RestoredProjectionArtifactDeltaReady env finalEnv after := by
  intro name info found ready notOld
  obtain ⟨handoff⟩ :=
    run.restoredProjectionRuntimeHandoff wf found ready notOld
  exact ⟨handoff.completeRuntime_ofRestorationSafety (safe handoff)⟩

/-- Consumer-facing resolution delta derived from the same exact public
restoration-safety trace. -/
theorem
    FlattenedExactNestedProjectionParameterRun.projectionArtifactResolutionDeltaReady_ofHostSourceRestorationSafety
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    {flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape}
    {metadata : VInductDecl.ExactProducedBlockMetadataPrefixRun flat.run}
    {after : VEnv}
    {restoration : execution.FlattenedNestedRestorationResult artifact after}
    {numNested_ne : execution.nested.aux2nested.size ≠ 0}
    {restoredMetadata :
      execution.FlattenedNestedRestoredMetadataPrefixRun restoration
        numNested_ne}
    (run : execution.FlattenedExactNestedProjectionParameterRun flat metadata
      restoration numNested_ne restoredMetadata)
    (wf : ves.WF env)
    (safe : ∀ {name info}
      (handoff : execution.RestoredProjectionRuntimeHandoff staged artifact
        run.transaction name info),
      handoff.HostSourceRestorationSafety) :
    ProjectionArtifactResolutionDeltaReady env finalEnv after :=
  (run.restoredProjectionArtifactDeltaReady_ofHostSourceRestorationSafety
    wf safe).toResolution

/-- The exact nested producer unconditionally constructs the restored
artifact delta for every newly projection-ready family. -/
theorem
    FlattenedExactNestedProjectionParameterRun.restoredProjectionArtifactDeltaReady
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    {flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape}
    {metadata : VInductDecl.ExactProducedBlockMetadataPrefixRun flat.run}
    {after : VEnv}
    {restoration : execution.FlattenedNestedRestorationResult artifact after}
    {numNested_ne : execution.nested.aux2nested.size ≠ 0}
    {restoredMetadata :
      execution.FlattenedNestedRestoredMetadataPrefixRun restoration
        numNested_ne}
    (run : execution.FlattenedExactNestedProjectionParameterRun flat metadata
      restoration numNested_ne restoredMetadata)
    (wf : ves.WF env) :
    RestoredProjectionArtifactDeltaReady env finalEnv after :=
  run.restoredProjectionArtifactDeltaReady_ofHostSourceRestorationSafety wf
    fun handoff => handoff.hostSourceRestorationSafety

/-- Consumer-facing resolution delta supplied unconditionally by the exact
nested producer. -/
theorem
    FlattenedExactNestedProjectionParameterRun.projectionArtifactResolutionDeltaReady
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    {flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape}
    {metadata : VInductDecl.ExactProducedBlockMetadataPrefixRun flat.run}
    {after : VEnv}
    {restoration : execution.FlattenedNestedRestorationResult artifact after}
    {numNested_ne : execution.nested.aux2nested.size ≠ 0}
    {restoredMetadata :
      execution.FlattenedNestedRestoredMetadataPrefixRun restoration
        numNested_ne}
    (run : execution.FlattenedExactNestedProjectionParameterRun flat metadata
      restoration numNested_ne restoredMetadata)
    (wf : ves.WF env) :
    ProjectionArtifactResolutionDeltaReady env finalEnv after :=
  (run.restoredProjectionArtifactDeltaReady wf).toResolution

/-- Forget the exact host constructor/audit source while retaining the
metadata-only restored projection layout API. -/
theorem
    FlattenedExactNestedTransactionResult.restoredProjectionArtifactLayout
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    {flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape}
    {metadata : VInductDecl.ExactProducedBlockMetadataPrefixRun flat.run}
    {after : VEnv}
    {restoration : execution.FlattenedNestedRestorationResult artifact after}
    {numNested_ne : execution.nested.aux2nested.size ≠ 0}
    {restoredMetadata :
      execution.FlattenedNestedRestoredMetadataPrefixRun restoration
        numNested_ne}
    (transaction : execution.FlattenedExactNestedTransactionResult flat
      metadata restoration numNested_ne restoredMetadata)
    (wf : ves.WF env) {name : Name} {info : InductiveVal}
    (found : finalEnv.find? name = some (.inductInfo info))
    (ready : finalEnv.isProjectionReadyStructure name = true)
    (notOld : ¬ (env.find? name = some (.inductInfo info) ∧
      env.isProjectionReadyStructure name = true)) :
    ∃ layout : RestoredProjectionArtifactLayout finalEnv name info after,
      layout.view.source = artifact.source ∧
      HEq layout.view.nested artifact.alignedNested ∧
      Nonempty (VInductDecl.NestedStructureSelection artifact.alignedNested
        layout.view.familyIndex layout.view.sourceFamily
          layout.view.sourceConstructor) := by
  obtain ⟨layout, ⟨source⟩⟩ :=
    FlattenedExactNestedTransactionResult.restoredProjectionArtifactLayoutSource
      transaction wf found ready notOld
  exact ⟨layout, source.source_eq, source.nested_eq, source.selection⟩

/-- Forgetting the host metadata fields of the restored layout recovers the
exact source-family structure selection owned by the nested producer. -/
theorem
    AddInductive.EnvironmentInductiveExecution.FlattenedExactNestedTransactionResult.projectionStructureSelection
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    {flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape}
    {metadata : VInductDecl.ExactProducedBlockMetadataPrefixRun flat.run}
    {after : VEnv}
    {restoration : execution.FlattenedNestedRestorationResult artifact after}
    {numNested_ne : execution.nested.aux2nested.size ≠ 0}
    {restoredMetadata :
      execution.FlattenedNestedRestoredMetadataPrefixRun restoration
        numNested_ne}
    (transaction : execution.FlattenedExactNestedTransactionResult flat
      metadata restoration numNested_ne restoredMetadata)
    (wf : ves.WF env) {name : Name} {info : InductiveVal}
    (found : finalEnv.find? name = some (.inductInfo info))
    (ready : finalEnv.isProjectionReadyStructure name = true)
    (notOld : ¬ (env.find? name = some (.inductInfo info) ∧
      env.isProjectionReadyStructure name = true)) :
    ∃ familyIndex sourceFamily sourceConstructor,
      sourceFamily.name = name ∧
      info.ctors = [sourceConstructor.name] ∧
      Nonempty (VInductDecl.NestedStructureSelection
        artifact.alignedNested familyIndex sourceFamily sourceConstructor) := by
  obtain ⟨layout, _sourceEq, _nestedEq, selection⟩ :=
    FlattenedExactNestedTransactionResult.restoredProjectionArtifactLayout
      transaction wf found ready notOld
  exact ⟨layout.view.familyIndex, layout.view.sourceFamily,
    layout.view.sourceConstructor, layout.name_eq, layout.ctors_eq,
    selection⟩

/-- Construct the block-backed projection artifact for one newly emitted
ordinary family.  The selected family, constructor, validator index count,
source translation spine, host metadata, and final Theory endpoint all come
from one retained semantic producer. -/
def
    FlattenedSemanticRecursorStagingResult.projectionArtifactOfDeclaredFamily
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    (result : execution.FlattenedSemanticRecursorStagingResult staged shape)
    (metadata : VInductDecl.ProducedBlockSemanticMetadataPrefixRun
      (staged.recursorShape shape) result.semantic result.generation
      result.run)
    (numNested_eq : execution.nested.aux2nested.size = 0)
    (wf : ves.WF env) {name : Name} {info : InductiveVal}
    (found : finalEnv.find? name = some (.inductInfo info))
    (ready : finalEnv.isProjectionReadyStructure name = true)
    (declared : info ∈
      execution.flattened.eliminationExecution.normalization.declaredInfos ∧
      info.name = name) :
    ProjectionArtifact finalEnv name info
      (result.generation.generatedRules.foldl VEnv.addDefEq
        metadata.recursors.recEnv) := by
  have inputMapWF := (wf.tr (safety := .safe)).map_wf
  let trace := result.ordinaryAddInductBlockTrace metadata numNested_eq
  have typeMapWF := trace.addTypes.map_wf inputMapWF
  have ctorMapWF := trace.addCtors.map_wf typeMapWF
  have finalMapWF := trace.addRecs.map_wf ctorMapWF
  have hostDataSome :=
    Kernel.Environment.ProjectionReadyStructureObservationData.find?_isSome
      found ready
  let hostData :=
    (Kernel.Environment.ProjectionReadyStructureObservationData.find? finalEnv
      name).get
      hostDataSome
  have hostDataFound :
      Kernel.Environment.ProjectionReadyStructureObservationData.find? finalEnv
        name = some hostData :=
    (Option.some_get hostDataSome).symm
  let host :=
    Kernel.Environment.ProjectionReadyStructureObservationData.toObservation
      finalEnv name hostData hostDataFound
  obtain ⟨observedInfo, constructorName, constructorInfo, recursorInfo,
      observedFound, ctorsEq, numIndicesEq, constructorFound, recursorFound,
      owner, _familyRecursor⟩ := host
  have observedInfoEq : observedInfo = info := by
    have taggedEq : (.inductInfo observedInfo : ConstantInfo) =
        .inductInfo info :=
      Option.some.inj (observedFound.symm.trans found)
    exact ConstantInfo.inductInfo.inj taggedEq
  subst observedInfo
  have constructorFoundMap :
      finalEnv.constants.find? constructorName =
        some (.ctorInfo constructorInfo) := by
    change finalEnv.constants.find?' constructorName = _ at constructorFound
    rwa [finalMapWF.find?'_eq_find?] at constructorFound
  have recursorFoundMap :
      finalEnv.constants.find? (mkRecName name) =
        some (.recInfo recursorInfo) := by
    change finalEnv.constants.find?' (mkRecName name) = _ at recursorFound
    rwa [finalMapWF.find?'_eq_find?] at recursorFound
  have familyFoundMap :
      finalEnv.constants.find? name = some (.inductInfo info) := by
    change finalEnv.constants.find?' name = _ at found
    rwa [finalMapWF.find?'_eq_find?] at found
  have normalizationRun := execution.flattened.normalization_run
    execution.flattenedRun
  have familyRun :=
    execution.flattened.eliminationExecution.normalization
      |>.familyValidationResult_run normalizationRun
  have familySizes :=
    execution.flattened.eliminationExecution.normalization
      |>.familyValidationResult.sizes_of_run
        execution.nested.types_nonempty familyRun
  have paramsSize :
      execution.flattened.eliminationExecution.normalization.stats.params.size =
        nparams := by
    simpa only [
      AddInductive.NormalizationCandidateExecution.familyValidationResult] using
      familySizes.1
  have nindicesSize :
      execution.flattened.eliminationExecution.normalization.stats.nindices.size =
        execution.nested.types.length := by
    simpa only [
      AddInductive.NormalizationCandidateExecution.familyValidationResult] using
      familySizes.2.1
  have familyAlignment : List.Forall₂
      (fun source familyInfo => ∃ numIndices,
        familyInfo = AddInductive.declaredInductiveInfo
          execution.flattened.eliminationExecution.normalization.stats nparams
          execution.nested.types.toArray source numIndices
          execution.nested.aux2nested.size false
          execution.flattened.eliminationExecution.normalization.validationContext)
      execution.nested.types
      execution.flattened.eliminationExecution.normalization.declaredInfos := by
    simpa only [
      AddInductive.NormalizationCandidateExecution.declaredInfos,
      List.toList_toArray] using
      AddInductive.declaredInductiveInfos_matches
        execution.flattened.eliminationExecution.normalization.stats nparams
        execution.nested.types.toArray execution.nested.aux2nested.size false
        execution.flattened.eliminationExecution.normalization.validationContext
        (by simpa using nindicesSize)
  let declaredNames :=
    execution.flattened.eliminationExecution.normalization.declaredInfos.map
      (·.name)
  have declaredNameMem : name ∈ declaredNames := by
    exact List.mem_map.2 ⟨info, declared.1, declared.2⟩
  let offset := declaredNames.idxOf name
  have offsetNameBound : offset < declaredNames.length := by
    simpa only [offset] using List.idxOf_lt_length_iff.2 declaredNameMem
  have declaredNameAt : declaredNames[offset]? = some name := by
    rw [List.getElem?_eq_getElem offsetNameBound]
    exact congrArg some (by
      simpa only [offset] using List.getElem_idxOf offsetNameBound)
  have sourceOffsetBound : offset < execution.nested.types.length := by
    have lengths := Lean4Lean.List.Forall₂.length_eq familyAlignment
    have declaredOffsetBound : offset <
        execution.flattened.eliminationExecution.normalization.declaredInfos.length := by
      simpa only [declaredNames, List.length_map] using offsetNameBound
    omega
  let sourceFamily := execution.nested.types[offset]'sourceOffsetBound
  have sourceAt : execution.nested.types[offset]? = some sourceFamily :=
    List.getElem?_eq_getElem sourceOffsetBound
  obtain ⟨rawFamily, rawFamilyAt, _familySource, constructorSources⟩ :=
    staged.enriched.enrichment.input.getElem? sourceAt
  have sourceRawAt : staged.source.types[offset]? = some rawFamily := by
    simpa only [FlattenedEnrichedStagingResult.source,
      VInductDecl.CandidateBlockSourceListEnrichment.toRawDecl] using
      rawFamilyAt.down
  have rawCountAt := result.run.rawIndexCounts.getElem? sourceRawAt
  change (staged.recursorShape shape).execution.eliminationExecution.normalization.stats.nindices[
    0 + offset]? = _ at rawCountAt
  rw [staged.recursorShape_nindices_eq shape] at rawCountAt
  have countAt :
      execution.flattened.eliminationExecution.normalization.stats.nindices[offset]? =
        some (VInductDecl.ctorFields
          (VExpr.dropN staged.source.nparams rawFamily.type)).length := by
    change
      execution.flattened.eliminationExecution.normalization.stats.nindices[
        0 + offset]? = _ at rawCountAt
    simpa only [Nat.zero_add] using rawCountAt
  let expectedInfo := AddInductive.declaredInductiveInfo
    execution.flattened.eliminationExecution.normalization.stats nparams
    execution.nested.types.toArray sourceFamily
    (VInductDecl.ctorFields
      (VExpr.dropN staged.source.nparams rawFamily.type)).length
    execution.nested.aux2nested.size false
    execution.flattened.eliminationExecution.normalization.validationContext
  have expectedInfoAt :
      execution.flattened.eliminationExecution.normalization.declaredInfos[offset]? =
        some expectedInfo := by
    simpa only [
      AddInductive.NormalizationCandidateExecution.declaredInfos,
      List.toList_toArray, expectedInfo] using
      AddInductive.declaredInductiveInfos_getElem?
        execution.flattened.eliminationExecution.normalization.stats nparams
        execution.nested.types.toArray execution.nested.aux2nested.size false
        execution.flattened.eliminationExecution.normalization.validationContext
        sourceAt countAt
  have expectedInfoName : expectedInfo.name = name := by
    simpa only [declaredNames, List.getElem?_map, expectedInfoAt,
      Option.map_some, Option.some.injEq] using declaredNameAt
  have sourceFamilyName : sourceFamily.name = name := by
    simpa only [expectedInfo, AddInductive.declaredInductiveInfo] using
      expectedInfoName
  have validationMapWF :
      execution.flattened.eliminationExecution.normalization.validationContext
        |>.env.constants.WF := by
    simpa only [execution.flattenedValidationEnv_eq] using inputMapWF
  have expectedInfoMember : expectedInfo ∈
      execution.flattened.eliminationExecution.normalization.declaredInfos :=
    List.mem_of_getElem? expectedInfoAt
  have expectedInfoLookup₀ :=
    execution.flattened.eliminationExecution.normalization.declareTrace.map_lookup
      validationMapWF expectedInfoMember
  have expectedInfoFamilyMapWF :=
    execution.flattened.eliminationExecution.normalization.declareTrace.map_wf
      validationMapWF
  have expectedInfoLookup₁ :=
    execution.flattened.eliminationExecution.declareConstructorTrace
      |>.preserve_map_lookup expectedInfoFamilyMapWF expectedInfoLookup₀
  have expectedInfoConstructorMapWF :=
    execution.flattened.eliminationExecution.declareConstructorTrace.map_wf
      expectedInfoFamilyMapWF
  have expectedInfoRecursorInitialMapWF :
      execution.flattened.recursors.initialEnv.constants.WF := by
    simpa only [execution.flattened.recursor_initialEnv_eq] using
      expectedInfoConstructorMapWF
  have expectedInfoLookup₁' :
      execution.flattened.recursors.initialEnv.constants.find?
          expectedInfo.name = some (.inductInfo expectedInfo) := by
    simpa only [execution.flattened.recursor_initialEnv_eq] using
      expectedInfoLookup₁
  have expectedInfoLookup₂ :=
    execution.flattened.recursors.trace.preserve_map_lookup
      expectedInfoRecursorInitialMapWF expectedInfoLookup₁'
  have expectedInfoLookup :
      finalEnv.constants.find? name = some (.inductInfo expectedInfo) := by
    simpa only [execution.flattenedEnv_eq_final numNested_eq,
      expectedInfoName] using expectedInfoLookup₂
  have infoEq : info = expectedInfo := by
    have taggedEq : (.inductInfo info : ConstantInfo) =
        .inductInfo expectedInfo :=
      Option.some.inj (familyFoundMap.symm.trans expectedInfoLookup)
    exact ConstantInfo.inductInfo.inj taggedEq
  have rawIndicesLength :
      (VInductDecl.ctorFields
        (VExpr.dropN staged.source.nparams rawFamily.type)).length = 0 := by
    rw [infoEq] at numIndicesEq
    simpa only [expectedInfo, AddInductive.declaredInductiveInfo] using
      numIndicesEq
  have rawIndicesEq :
      VInductDecl.ctorFields
        (VExpr.dropN staged.source.nparams rawFamily.type) = [] :=
    List.length_eq_zero_iff.mp rawIndicesLength
  have sourceConstructorNames :
      sourceFamily.ctors.map (·.name) = [constructorName] := by
    rw [infoEq] at ctorsEq
    simpa only [expectedInfo, AddInductive.declaredInductiveInfo] using ctorsEq
  have sourceConstructorsLength : sourceFamily.ctors.length = 1 := by
    have lengths := congrArg List.length sourceConstructorNames
    simpa only [List.length_map, List.length_cons, List.length_nil] using lengths
  have sourceConstructorBound : 0 < sourceFamily.ctors.length := by omega
  let sourceConstructor :=
    sourceFamily.ctors[0]'sourceConstructorBound
  have sourceConstructorsEq : sourceFamily.ctors = [sourceConstructor] := by
    simpa only [sourceConstructor] using
      List.eq_getElem_of_length_eq_one sourceFamily.ctors
        sourceConstructorsLength
  have sourceConstructorName : sourceConstructor.name = constructorName := by
    have selected : sourceConstructor.name = constructorName ∧ True := by
      simpa only [sourceConstructorsEq, List.map_cons, List.map_nil,
        List.cons.injEq] using sourceConstructorNames
    exact selected.1
  have sourceConstructorAt : sourceFamily.ctors[0]? =
      some sourceConstructor :=
    List.getElem?_eq_getElem sourceConstructorBound
  obtain ⟨rawConstructor, rawConstructorAt, constructorSource⟩ :=
    constructorSources.getElem? sourceConstructorAt
  have rawConstructorsLength : rawFamily.ctors.length = 1 := by
    rw [← constructorSources.length_eq]
    exact sourceConstructorsLength
  have rawConstructorBound : 0 < rawFamily.ctors.length := by omega
  have rawConstructorHead : rawFamily.ctors[0]'rawConstructorBound =
      rawConstructor := by
    exact Option.some.inj ((List.getElem?_eq_getElem rawConstructorBound).symm.trans
      rawConstructorAt.down)
  have rawConstructorsEq : rawFamily.ctors = [rawConstructor] := by
    have singleton := List.eq_getElem_of_length_eq_one rawFamily.ctors
      rawConstructorsLength
    simpa only [rawConstructorHead] using singleton
  have familyOffsetBound : offset < result.generation.families.length := by
    have lengths := congrArg List.length result.generation.families_map_raw
    simp only [List.length_map] at lengths
    have rawBound := (List.getElem?_eq_some_iff.mp sourceRawAt).1
    omega
  let family := result.generation.families[offset]'familyOffsetBound
  have familyAt : result.generation.families[offset]? = some family :=
    List.getElem?_eq_getElem familyOffsetBound
  have familyMember : family ∈ result.generation.families :=
    List.mem_iff_getElem?.2 ⟨offset, familyAt⟩
  have familyRawEq : family.raw = rawFamily := by
    have mappedAt : (result.generation.families.map (·.raw))[offset]? =
        some family.raw := by
      simp only [List.getElem?_map, familyAt, Option.map_some]
    rw [result.generation.families_map_raw] at mappedAt
    exact Option.some.inj (mappedAt.symm.trans sourceRawAt)
  have familyRawAt : family.raw.ctors[0]? = some rawConstructor := by
    rw [familyRawEq, rawConstructorsEq]
    rfl
  have constructorPairsLength : family.ctorPairs.length = 1 := by
    calc
      family.ctorPairs.length = family.raw.ctors.length :=
        (result.generation.shape.2.2.2.2 family familyMember).2.2.2.2.1
      _ = rawFamily.ctors.length :=
        congrArg (fun raw => raw.ctors.length) familyRawEq
      _ = 1 := rawConstructorsLength
  have constructorBound : 0 < family.ctorPairs.length := by omega
  let constructor := family.ctorPairs[0]'constructorBound
  have constructorAt : family.ctorPairs[0]? = some constructor :=
    List.getElem?_eq_getElem constructorBound
  have constructorRawEq : constructor.raw = rawConstructor := by
    have mappedAt : (family.ctorPairs.map (·.raw))[0]? =
        some constructor.raw := by
      simp only [List.getElem?_map, constructorAt, Option.map_some]
    rw [family.ctorPairs_map_raw familyMember] at mappedAt
    exact Option.some.inj (mappedAt.symm.trans familyRawAt)
  have constructorPairsEq : family.ctorPairs = [constructor] := by
    simpa only [constructor] using
      List.eq_getElem_of_length_eq_one family.ctorPairs constructorPairsLength
  have checkedIndicesLength : family.view.indices.length = 0 := by
    rw [← (result.generation.shape.2.2.2.2 family familyMember).2.2.2.1]
    simpa only [VInductDecl.NormalizedFamily.rawIndices, familyRawEq] using
      rawIndicesLength
  have checkedIndicesEq : family.view.indices = [] :=
    List.length_eq_zero_iff.mp checkedIndicesLength
  let expectedConstructorInfo := AddInductive.declaredConstructorInfo
    execution.flattened.eliminationExecution.normalization.stats
    sourceFamily.name sourceConstructor 0 false
    execution.flattened.eliminationExecution.constructorContext
  have expectedConstructorMember : expectedConstructorInfo ∈
      execution.flattened.eliminationExecution.declaredConstructorInfos := by
    simp only [
      AddInductive.NormalizationEliminationExecution.declaredConstructorInfos,
      AddInductive.declaredConstructorInfos_toArray, List.mem_flatMap]
    refine ⟨sourceFamily, List.mem_of_getElem? sourceAt, ?_⟩
    rw [sourceConstructorsEq]
    simp [expectedConstructorInfo,
      AddInductive.declaredConstructorInfosFor]
  have validationMapWF :
      execution.flattened.eliminationExecution.normalization.validationContext
        |>.env.constants.WF := by
    simpa only [execution.flattenedValidationEnv_eq] using inputMapWF
  have hostFamilyMapWF :=
    execution.flattened.eliminationExecution.normalization.declareTrace.map_wf
      validationMapWF
  have hostConstructorMapWF :=
    execution.flattened.eliminationExecution.declareConstructorTrace.map_wf
      hostFamilyMapWF
  have recursorInitialMapWF :
      execution.flattened.recursors.initialEnv.constants.WF := by
    simpa only [execution.flattened.recursor_initialEnv_eq] using
      hostConstructorMapWF
  have expectedConstructorLookup₀ :=
    execution.flattened.eliminationExecution.declareConstructorTrace.map_lookup
      hostFamilyMapWF expectedConstructorMember
  have expectedConstructorLookup₁ :
      execution.flattened.recursors.initialEnv.constants.find?
          expectedConstructorInfo.name =
        some (.ctorInfo expectedConstructorInfo) := by
    simpa only [execution.flattened.recursor_initialEnv_eq] using
      expectedConstructorLookup₀
  have expectedConstructorLookup₂ :=
    execution.flattened.recursors.trace.preserve_map_lookup
      recursorInitialMapWF expectedConstructorLookup₁
  have expectedConstructorLookup :
      finalEnv.constants.find? expectedConstructorInfo.name =
        some (.ctorInfo expectedConstructorInfo) := by
    simpa only [execution.flattenedEnv_eq_final numNested_eq] using
      expectedConstructorLookup₂
  have expectedConstructorName :
      expectedConstructorInfo.name = constructorName := by
    simp [expectedConstructorInfo, AddInductive.declaredConstructorInfo,
      sourceConstructorName]
  have constructorInfoEq : constructorInfo = expectedConstructorInfo := by
    have taggedEq : (.ctorInfo constructorInfo : ConstantInfo) =
        .ctorInfo expectedConstructorInfo :=
      Option.some.inj (constructorFoundMap.symm.trans (by
        simpa only [expectedConstructorName] using expectedConstructorLookup))
    exact ConstantInfo.ctorInfo.inj taggedEq
  have familyName : family.raw.name = name := by
    calc
      family.raw.name = rawFamily.name :=
        congrArg (fun value : VInductiveType => value.name) familyRawEq
      _ = sourceFamily.name := _familySource.down.name_eq.symm
      _ = name := sourceFamilyName
  have selectedConstructorName : constructor.raw.name = constructorName := by
    calc
      constructor.raw.name = rawConstructor.name :=
        congrArg VConstVal.name constructorRawEq
      _ = sourceConstructor.name := constructorSource.down.name_eq.symm
      _ = constructorName := sourceConstructorName
  let expectedRecursor : VConstVal :=
    ⟨result.generation.generatedRecursor family,
      .str family.raw.name "rec"⟩
  have expectedRecursorMember :
      expectedRecursor ∈ result.generation.recursors := by
    rw [VInductDecl.BlockGenerationChecked.recursors]
    exact List.mem_map.2 ⟨family, familyMember, rfl⟩
  have expectedRecursorName : expectedRecursor.name = mkRecName name := by
    simp [expectedRecursor, mkRecName, familyName]
  have translatedRecursorTr : TrConstVal .safe
      (result.generation.generatedRules.foldl VEnv.addDefEq
        metadata.recursors.recEnv)
      (.recInfo recursorInfo) expectedRecursor := by
    obtain ⟨translatedRecursor, translatedRecursorLookup,
        _translatedRecursorKind, translatedRecursorTr⟩ :=
      trace.recursor_translated_lookup inputMapWF expectedRecursorMember
    have translatedRecursorLookup' :
        finalEnv.constants.find? (mkRecName name) = some translatedRecursor := by
      simpa only [expectedRecursorName] using translatedRecursorLookup
    have translatedRecursorEq :
        translatedRecursor = .recInfo recursorInfo :=
      Option.some.inj (translatedRecursorLookup'.symm.trans recursorFoundMap)
    subst translatedRecursor
    exact translatedRecursorTr
  have recursorLevelParamsLength :
      recursorInfo.levelParams.length = result.generation.recUvars := by
    have translatedLength := translatedRecursorTr.1.2.1
    change recursorInfo.levelParams.length = expectedRecursor.uvars at translatedLength
    simpa [expectedRecursor,
      VInductDecl.BlockGenerationChecked.generatedRecursor] using
        translatedLength
  have constructorMember : constructor ∈ family.ctorPairs := by
    rw [constructorPairsEq]
    simp
  let blockConstructor : VInductDecl.NormalizedBlockCtor := {
    owner := family.view.ordinal
    familyName := family.raw.name
    familyIndices := family.view.indices
    ctor := constructor }
  have blockConstructorMember :
      blockConstructor ∈ result.generation.flatCtors := by
    simp only [VInductDecl.BlockGenerationChecked.flatCtors,
      VInductDecl.NormalizedCheckedBlock.flatCtors, List.mem_flatMap]
    refine ⟨family, familyMember, ?_⟩
    simp only [VInductDecl.NormalizedFamily.blockCtors, List.mem_map]
    exact ⟨constructor, constructorMember, rfl⟩
  have sourceUvars : staged.source.uvars = lparams.length := by
    simpa only [FlattenedEnrichedStagingResult.source,
      VInductDecl.CandidateBlockSourceListEnrichment.toRawDecl] using
      staged.family.staging.uvars_eq
  have familyViewAt :
      result.generation.block.checked.families.data[offset]? =
        some family.view := by
    rw [← result.generation.families_map_view,
      List.getElem?_map, familyAt]
    rfl
  have familyConstructorsAt :
      result.generation.block.checked.families.constructors[offset]? =
        some family.view.constructors :=
    VInductDecl.CheckedFamilies.constructors_getElem?_of_data
      result.generation.block.checked.families familyViewAt
  have familyOffsetBound : offset < result.run.fieldSorts.length := by
    have leftBound := (List.getElem?_eq_some_iff.mp familyConstructorsAt).1
    have lengths := Lean4Lean.List.Forall₂.length_eq
      result.run.fieldSorts_telescopes
    omega
  let constructorSorts := result.run.fieldSorts[offset]'familyOffsetBound
  have constructorSortsAt : result.run.fieldSorts[offset]? =
      some constructorSorts :=
    List.getElem?_eq_getElem familyOffsetBound
  have constructorSortRelation : List.Forall₂
      (fun checkedConstructor sorts =>
        staged.enriched.blockEnv.OnSortTel lparams.length
          result.generation.block.checked.params.reverse
          checkedConstructor.fields sorts)
      family.view.constructors constructorSorts := by
    obtain ⟨constructors, constructorsAt, related⟩ :=
      Lean4Lean.List.Forall₂.getElem?_right
        result.run.fieldSorts_telescopes constructorSortsAt
    have constructorsEq : constructors = family.view.constructors :=
      Option.some.inj (constructorsAt.symm.trans familyConstructorsAt)
    subst constructors
    exact related
  have constructorViewsEq : family.ctorPairs.map (fun current => current.view) =
      family.view.constructors := by
    apply VInductDecl.pairNormalizedCtors_map_view
    exact (result.generation.shape.2.2.2.2 family familyMember).2.2.2.2.1.symm.trans
      (result.generation.shape.2.2.2.2 family familyMember).2.2.2.2.2.1
  have constructorViewAt : family.view.constructors[0]? =
      some constructor.view := by
    rw [← constructorViewsEq, List.getElem?_map, constructorAt]
    rfl
  have constructorOffsetBound : 0 < constructorSorts.length := by
    rw [← Lean4Lean.List.Forall₂.length_eq constructorSortRelation]
    exact (List.getElem?_eq_some_iff.mp constructorViewAt).1
  let fieldSorts := constructorSorts[0]'constructorOffsetBound
  have fieldSortsAt : constructorSorts[0]? = some fieldSorts :=
    List.getElem?_eq_getElem constructorOffsetBound
  have checkedFieldTelescope : staged.enriched.blockEnv.OnSortTel
      lparams.length result.generation.block.checked.params.reverse
      constructor.view.fields fieldSorts := by
    obtain ⟨checkedConstructor, checkedConstructorAt, related⟩ :=
      Lean4Lean.List.Forall₂.getElem?_right constructorSortRelation
        fieldSortsAt
    have checkedConstructorEq : checkedConstructor = constructor.view :=
      Option.some.inj (checkedConstructorAt.symm.trans constructorViewAt)
    subst checkedConstructor
    exact related
  have emittedDefEq :=
    (result.run.block.wf.constructors blockConstructor
      blockConstructorMember).emittedTel
  have rawViewFieldDefEq : staged.enriched.blockEnv.TelDefEq lparams.length
      result.generation.block.checked.params.reverse
      (constructor.rawFields staged.source.nparams)
      constructor.view.fields := by
    have dropped := emittedDefEq.drop
      result.generation.block.checked.params.length
    simpa [sourceUvars, blockConstructor,
      VInductDecl.NormalizedBlockCtor.emittedBinders,
      VInductDecl.NormalizedBlockCtor.viewBinders] using dropped
  have emittedOnTel := emittedDefEq.raw_onTel
  have parameterOnTel := (VEnv.OnTel.of_append
    (As := result.generation.block.checked.params) emittedOnTel).1
  have parameterCtx : OnCtx result.generation.block.checked.params.reverse
      (staged.enriched.blockEnv.IsType lparams.length) := by
    simpa [sourceUvars] using parameterOnTel.toOnCtx (by trivial)
  have rawFieldTelescope : staged.enriched.blockEnv.OnSortTel lparams.length
      result.generation.block.checked.params.reverse
      (constructor.rawFields staged.source.nparams) fieldSorts :=
    rawViewFieldDefEq.raw_onSortTel result.run.blockEnv_wf parameterCtx
      checkedFieldTelescope
  have traceGenerationEq : trace.generation = result.generation := rfl
  have generationWF : result.generation.WF (ves.venv .safe) trace.blockEnv := by
    simpa only [traceGenerationEq] using trace.generation_wf
  have generationTrace' : VEnv.AddInductBlockGenerationTrace
      (ves.venv .safe)
      (result.generation.generatedRules.foldl VEnv.addDefEq
        metadata.recursors.recEnv) result.generation := by
    simpa only [traceGenerationEq] using trace.toGenerationTrace
  have inputOrdered := (wf.tr (safety := .safe)).wf.ordered
  have blockEnvLe : staged.enriched.blockEnv ≤
      result.generation.generatedRules.foldl VEnv.addDefEq
        metadata.recursors.recEnv :=
    trace.addCtors.le.trans (trace.addRecs.le.trans trace.addRules.le)
  have fieldSortTelescope :
      (result.generation.generatedRules.foldl VEnv.addDefEq
        metadata.recursors.recEnv).OnSortTel staged.source.uvars
        result.generation.block.checked.params.reverse
        (constructor.rawFields staged.source.nparams) fieldSorts := by
    rw [sourceUvars]
    exact rawFieldTelescope.mono blockEnvLe
  let selected : VBlockStructureView := {
    source := staged.source
    generation := result.generation
    family := family
    family_mem := familyMember
    constructor := constructor
    constructor_eq := constructorPairsEq
    raw_indices_eq := by
      simpa only [VInductDecl.NormalizedFamily.rawIndices, familyRawEq] using
        rawIndicesEq
    checked_indices_eq := checkedIndicesEq
    fieldSorts := fieldSorts
    fieldSorts_length :=
      VEnv.OnSortTel.length_eq fieldSortTelescope |>.symm }
  have selectedLayout : selected.LayoutWF
      (result.generation.generatedRules.foldl VEnv.addDefEq
        metadata.recursors.recEnv) :=
    VBlockStructureView.LayoutWF.ofTrace inputOrdered generationWF
      generationTrace' (by
        simpa [selected, VBlockStructureView.fields] using fieldSortTelescope)
  have constructorParamLength :
      (VExpr.telN staged.source.nparams constructor.raw.type).length =
        staged.source.nparams :=
    ((result.generation.shape.2.2.2.2 family familyMember).2.2.2.2.2.2
      constructor constructorMember).2.2.1
  have constructorAritySplit :
      staged.source.nparams +
          (constructor.rawFields staged.source.nparams).length =
        (VInductDecl.ctorFields constructor.raw.type).length := by
    simpa only [constructorParamLength,
      VInductDecl.NormalizedCtor.rawFields] using
      VExpr.telN_length_add_ctorFields_dropN_length
        staged.source.nparams constructor.raw.type
  have rawConstructorAritySplit :
      (VInductDecl.ctorFields rawConstructor.type).length =
        staged.source.nparams +
          (constructor.rawFields staged.source.nparams).length := by
    rw [← constructorRawEq]
    exact constructorAritySplit.symm
  have sourceConstructorArity :
      AddInductive.constructorArity sourceConstructor.type 0 =
        staged.source.nparams +
          (constructor.rawFields staged.source.nparams).length :=
    constructorSource.down.sourceArity_eq.trans rawConstructorAritySplit
  have constructorSpineSupport : ProjectionSpineSupport
      (staged.source.nparams +
        (constructor.rawFields staged.source.nparams).length)
      constructorInfo.type constructor.raw.type := by
    have support := constructorSource.down.spineSupport
    rw [rawConstructorAritySplit] at support
    simpa [constructorInfoEq, expectedConstructorInfo,
      AddInductive.declaredConstructorInfo, constructorRawEq] using support
  have constructorNumParams :
      constructorInfo.numParams = staged.source.nparams := by
    simp [constructorInfoEq, expectedConstructorInfo,
      AddInductive.declaredConstructorInfo, paramsSize,
      staged.source_nparams_eq]
  have constructorNumFields :
      constructorInfo.numFields =
        (constructor.rawFields staged.source.nparams).length := by
    simp [constructorInfoEq, expectedConstructorInfo,
      AddInductive.declaredConstructorInfo, paramsSize,
      sourceConstructorArity, staged.source_nparams_eq]
  have infoLevelParamsLength :
      info.levelParams.length = staged.source.uvars := by
    rw [infoEq]
    simp only [expectedInfo, AddInductive.declaredInductiveInfo]
    rw [execution.flattenedValidationLparams_eq, sourceUvars]
  have infoNumParams : info.numParams = staged.source.nparams := by
    rw [infoEq]
    simp only [expectedInfo, AddInductive.declaredInductiveInfo]
    exact staged.source_nparams_eq.symm
  exact {
    view := .block selected
    name_eq := by
      simpa [VProjectionView.name, VProjectionView.familyRaw, selected] using
        familyName
    viewWF := VProjectionView.LayoutWF.ofBlock selectedLayout
    constructorInfo := constructorInfo
    constructor_find := by
      simpa [VProjectionView.constructorName, VProjectionView.constructor,
        selected, selectedConstructorName] using constructorFound
    recursorInfo := recursorInfo
    recursor_find := by
      simpa [VProjectionView.recursorName, VProjectionView.name,
        VProjectionView.familyRaw, selected, familyName, mkRecName] using
        recursorFound
    recursor_levelParams_length := by
      simpa [VProjectionView.recUvars, selected] using
        recursorLevelParamsLength
    constructor_numParams_eq := by
      simpa [VProjectionView.nparams, VProjectionView.source, selected] using
        constructorNumParams
    constructor_numFields_eq := by
      simpa [VProjectionView.fields, VProjectionView.constructor,
        VProjectionView.nparams, VProjectionView.source, selected] using
        constructorNumFields
    levelParams_length := by
      simpa [VProjectionView.uvars, VProjectionView.source, selected] using
        infoLevelParamsLength
    numParams_eq := by
      simpa [VProjectionView.nparams, VProjectionView.source, selected] using
        infoNumParams
    numIndices_eq := numIndicesEq
    ctors_eq := by
      simpa [VProjectionView.constructorName, VProjectionView.constructor,
        selected, selectedConstructorName] using ctorsEq
    programs := .runtimeBlock selected rfl (by
      simpa [selected, VBlockStructureView.fields] using
        constructorSpineSupport) }

/-- Data-bearing projection resolution for the exact ordinary source-family
inventory.  Source names are fresh in the input map, so every successful host
observation in this scan domain is discharged by the retained producer rather
than by propositionally inherited readiness. -/
def
    FlattenedSemanticRecursorStagingResult.projectionArtifactInventoryResolver
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    (result : execution.FlattenedSemanticRecursorStagingResult staged shape)
    (metadata : VInductDecl.ProducedBlockSemanticMetadataPrefixRun
      (staged.recursorShape shape) result.semantic result.generation
      result.run)
    (numNested_eq : execution.nested.aux2nested.size = 0)
    (wf : ves.WF env) :
    ProjectionArtifactInventoryResolver finalEnv
      (result.generation.generatedRules.foldl VEnv.addDefEq
        metadata.recursors.recEnv)
      (execution.nested.types.map (·.name)) where
  infer familyName familyMember info found ready := by
    have inputMapWF := (wf.tr (safety := .safe)).map_wf
    have familyFresh : env.find? familyName = none := by
      obtain ⟨sourceFamily, sourceMember, sourceName⟩ :=
        List.mem_map.mp familyMember
      have sourceFresh :=
        execution.ordinarySourceFamilyFresh inputMapWF sourceMember
      change env.constants.find?' familyName = none
      rw [inputMapWF.find?'_eq_find?]
      simpa only [sourceName] using sourceFresh
    have notOld : ¬ (env.find? familyName = some (.inductInfo info) ∧
        env.isProjectionReadyStructure familyName = true) := by
      intro old
      rw [familyFresh] at old
      simp at old
    exact .ordinary <| result.projectionArtifactOfDeclaredFamily metadata
      numNested_eq wf found ready
        (execution.ordinaryProjectionDeltaFamily numNested_eq inputMapWF found
          ready notOld)

/-- Newly projection-ready ordinary families inherit their complete runtime
artifact directly from the retained semantic producer. -/
theorem
    FlattenedSemanticRecursorStagingResult.projectionArtifactDeltaReady
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    (result : execution.FlattenedSemanticRecursorStagingResult staged shape)
    (metadata : VInductDecl.ProducedBlockSemanticMetadataPrefixRun
      (staged.recursorShape shape) result.semantic result.generation
      result.run)
    (numNested_eq : execution.nested.aux2nested.size = 0)
    (wf : ves.WF env) :
    ProjectionArtifactDeltaReady env finalEnv
      (result.generation.generatedRules.foldl VEnv.addDefEq
        metadata.recursors.recEnv) := by
  intro name info found ready notOld
  exact ⟨result.projectionArtifactOfDeclaredFamily metadata numNested_eq wf
    found ready
    (execution.ordinaryProjectionDeltaFamily numNested_eq
      (wf.tr (safety := .safe)).map_wf found ready notOld)⟩

end AddInductive.EnvironmentInductiveExecution

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
  familyEvidence : List.Forall₂
    (fun info raw => TrConstVal .safe input (.inductInfo info) raw)
    execution.flattened.eliminationExecution.normalization.declaredInfos
    (VPrimitiveInductive.canonicalDecl types).blockTypeConstants
  ctorEnv : VEnv
  addCtors : AddInductConstants .ctor
    execution.flattened.eliminationExecution.normalization.familyEnv.constants
    blockEnv (VPrimitiveInductive.canonicalDecl types).blockConstructorConstants
    execution.flattened.eliminationExecution.constructorEnv.constants ctorEnv
  constructorEvidence : List.Forall₂
    (fun info raw => TrConstVal .safe blockEnv (.ctorInfo info) raw)
    execution.flattened.eliminationExecution.declaredConstructorInfos
    (VPrimitiveInductive.canonicalDecl types).blockConstructorConstants
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
  familyEvidence :=
    execution.canonicalPrimitiveFamilyEvidence primitiveResult input
  ctorEnv := constructors.ctorEnv
  addCtors := constructors.addCtors
  constructorEvidence :=
    execution.canonicalPrimitiveConstructorEvidence primitiveResult input
      families
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

/-- Recover the exact host record for a canonical family at the final
transaction boundary.  Primitive recognition additionally fixes the retained
Bool/Nat family metadata to two constructors. -/
theorem canonicalFamilyMetadata
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe true fuel finalEnv}
    {input output : VEnv}
    (replay : execution.CanonicalPrimitiveReplay input output)
    (primitiveResult : PrimitiveInductiveResult lparams nparams types isUnsafe
      true) (mapWF : env.constants.WF) {raw : VConstVal}
    (member : raw ∈
      (VPrimitiveInductive.canonicalDecl types).blockTypeConstants) :
    ∃ info ∈
        execution.flattened.eliminationExecution.normalization.declaredInfos,
      finalEnv.constants.find? raw.name = some (.inductInfo info) ∧
        info.ctors.length = 2 := by
  let trace := replay.toTrace primitiveResult
  have wfTypes := trace.addTypes.map_wf mapWF
  have wfCtors := trace.addCtors.map_wf wfTypes
  obtain ⟨info, infoMember, related⟩ :=
    Lean4Lean.List.Forall₂.forall_exists_r replay.familyEvidence raw member
  have initialEq := execution.flattenedValidationEnv_eq
  have validationMapWF :
      execution.flattened.eliminationExecution.normalization.validationContext.env.constants.WF := by
    simpa only [initialEq] using mapWF
  have familyLookup :
      execution.flattened.eliminationExecution.normalization.familyEnv.constants.find?
          info.name = some (.inductInfo info) :=
    execution.flattened.eliminationExecution.normalization.declareTrace.map_lookup
      validationMapWF infoMember
  have constructorLookup :
      execution.flattened.eliminationExecution.constructorEnv.constants.find?
          info.name = some (.inductInfo info) :=
    trace.addCtors.preserve_map_lookup wfTypes familyLookup
  have finalLookup :
      finalEnv.constants.find? info.name = some (.inductInfo info) :=
    trace.addRecs.preserve_map_lookup wfCtors constructorLookup
  have nameEq : info.name = raw.name := related.2
  exact ⟨info, infoMember, nameEq ▸ finalLookup,
    execution.canonicalPrimitiveDeclaredInfo_ctors_length primitiveResult
      infoMember⟩

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.CanonicalPrimitiveReplay.canonicalFamilyMetadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.abstract_eq,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms AddInductive.EnvironmentInductiveExecution.CanonicalPrimitiveReplay.canonicalFamilyMetadata

/-- Classify any final family record of a primitive transaction.  Old records
retain the exact input lookup; every newly inserted Bool/Nat family has two
constructors. -/
theorem familyLookupCases
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe true fuel finalEnv}
    {input output : VEnv}
    (replay : execution.CanonicalPrimitiveReplay input output)
    (primitiveResult : PrimitiveInductiveResult lparams nparams types isUnsafe
      true) (mapWF : env.constants.WF) {name : Name} {info : InductiveVal}
    (found : finalEnv.constants.find? name = some (.inductInfo info)) :
    env.constants.find? name = some (.inductInfo info) ∨
      info.ctors.length = 2 ∧
        ∃ raw ∈
          (VPrimitiveInductive.canonicalDecl types).blockTypeConstants,
          raw.name = name := by
  let trace := replay.toTrace primitiveResult
  rcases trace.family_map_lookup_cases mapWF found with
    old | ⟨raw, member, nameEq⟩
  · exact .inl old
  · obtain ⟨hostInfo, _hostMember, hostLookup, hostLength⟩ :=
      replay.canonicalFamilyMetadata primitiveResult mapWF member
    have hostLookupAtName :
        finalEnv.constants.find? name = some (.inductInfo hostInfo) := by
      simpa only [nameEq] using hostLookup
    have infoEq : info = hostInfo := by
      have taggedEq : (.inductInfo info : ConstantInfo) = .inductInfo hostInfo :=
        Option.some.inj (found.symm.trans hostLookupAtName)
      cases taggedEq
      rfl
    subst info
    exact .inr ⟨hostLength, raw, member, nameEq⟩

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.CanonicalPrimitiveReplay.familyLookupCases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.abstract_eq,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms AddInductive.EnvironmentInductiveExecution.CanonicalPrimitiveReplay.familyLookupCases

/-- Recover the exact host record for a canonical constructor at the final
transaction boundary.  The retained source-aligned metadata pairing selects
the record, the executable constructor fold supplies its map lookup, and
primitive recognition fixes its cached parameter count to zero. -/
theorem canonicalConstructorMetadata
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe true fuel finalEnv}
    {input output : VEnv}
    (replay : execution.CanonicalPrimitiveReplay input output)
    (primitiveResult : PrimitiveInductiveResult lparams nparams types isUnsafe
      true) (mapWF : env.constants.WF) {raw : VConstVal}
    (member : raw ∈
      (VPrimitiveInductive.canonicalDecl types).blockConstructorConstants) :
    ∃ info ∈
        execution.flattened.eliminationExecution.declaredConstructorInfos,
      finalEnv.constants.find? raw.name = some (.ctorInfo info) ∧
        info.numParams = 0 ∧
          ∃ familyRaw ∈
            (VPrimitiveInductive.canonicalDecl types).blockTypeConstants,
            info.induct = familyRaw.name := by
  let trace := replay.toTrace primitiveResult
  have wfTypes := trace.addTypes.map_wf mapWF
  have wfCtors := trace.addCtors.map_wf wfTypes
  obtain ⟨info, infoMember, related⟩ :=
    Lean4Lean.List.Forall₂.forall_exists_r replay.constructorEvidence raw
      member
  have constructorLookup :
      execution.flattened.eliminationExecution.constructorEnv.constants.find?
          info.name = some (.ctorInfo info) :=
    execution.flattened.eliminationExecution.declareConstructorTrace.map_lookup
      wfTypes infoMember
  have finalLookup :
      finalEnv.constants.find? info.name = some (.ctorInfo info) :=
    trace.addRecs.preserve_map_lookup wfCtors constructorLookup
  have nameEq : info.name = raw.name := related.2
  exact ⟨info, infoMember, nameEq ▸ finalLookup,
    execution.canonicalPrimitiveDeclaredConstructor_numParams primitiveResult
      infoMember,
    execution.canonicalPrimitiveDeclaredConstructor_induct primitiveResult
      infoMember⟩

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.CanonicalPrimitiveReplay.canonicalConstructorMetadata' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.abstract_eq,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms AddInductive.EnvironmentInductiveExecution.CanonicalPrimitiveReplay.canonicalConstructorMetadata

/-- Classify any final constructor record of a primitive transaction.  Old
records retain the exact input lookup; every newly inserted record is one of
the canonical constructors and has cached parameter count zero. -/
theorem constructorLookupCases
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe true fuel finalEnv}
    {input output : VEnv}
    (replay : execution.CanonicalPrimitiveReplay input output)
    (primitiveResult : PrimitiveInductiveResult lparams nparams types isUnsafe
      true) (mapWF : env.constants.WF) {name : Name} {info : ConstructorVal}
    (found : finalEnv.constants.find? name = some (.ctorInfo info)) :
    env.constants.find? name = some (.ctorInfo info) ∨
      info.numParams = 0 ∧
        (∃ raw ∈
          (VPrimitiveInductive.canonicalDecl types).blockConstructorConstants,
          raw.name = name) ∧
        ∃ familyRaw ∈
          (VPrimitiveInductive.canonicalDecl types).blockTypeConstants,
          info.induct = familyRaw.name := by
  let trace := replay.toTrace primitiveResult
  rcases trace.constructor_map_lookup_cases mapWF found with
    old | ⟨raw, member, nameEq⟩
  · exact .inl old
  · obtain ⟨hostInfo, _hostMember, hostLookup, hostNumParams, hostOwner⟩ :=
      replay.canonicalConstructorMetadata primitiveResult mapWF member
    have hostLookupAtName :
        finalEnv.constants.find? name = some (.ctorInfo hostInfo) := by
      simpa only [nameEq] using hostLookup
    have infoEq : info = hostInfo := by
      have taggedEq : (.ctorInfo info : ConstantInfo) = .ctorInfo hostInfo :=
        Option.some.inj (found.symm.trans hostLookupAtName)
      cases taggedEq
      rfl
    subst info
    exact .inr ⟨hostNumParams, ⟨raw, member, nameEq⟩, hostOwner⟩

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.CanonicalPrimitiveReplay.constructorLookupCases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.abstract_eq,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms AddInductive.EnvironmentInductiveExecution.CanonicalPrimitiveReplay.constructorLookupCases

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

/-- Every constructor record visible after a canonical primitive replay has a
Theory constructor header.  Existing records reuse the input readiness
contract; newly inserted records are discharged by the exact canonical block
trace. -/
theorem constructorHead
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe true fuel finalEnv}
    {input : VEnvs}
    (replay : execution.CoherentCanonicalPrimitiveReplay input)
    (primitiveResult : PrimitiveInductiveResult lparams nparams types isUnsafe
      true) (wf : input.WF env) (safety : DefinitionSafety)
    {name : Name} {info : ConstructorVal}
    (found : finalEnv.find? name = some (.ctorInfo info)) :
    (replay.output.venv safety).ConstructorHeadArity name
      info.numParams := by
  have inputMapWF := (wf.tr (safety := safety)).map_wf
  let pointwise := replay.replays safety
  have finalMapWF :=
    (pointwise.toTrace primitiveResult).addRecs.map_wf <|
      (pointwise.toTrace primitiveResult).addCtors.map_wf <|
        (pointwise.toTrace primitiveResult).addTypes.map_wf inputMapWF
  have foundMap :
      finalEnv.constants.find? name = some (.ctorInfo info) := by
    change finalEnv.constants.find?' name = _ at found
    rwa [finalMapWF.find?'_eq_find?] at found
  rcases pointwise.constructorLookupCases primitiveResult inputMapWF foundMap
      with old | ⟨numParamsZero, ⟨raw, member, nameEq⟩, _owner⟩
  · have oldFind : env.find? name = some (.ctorInfo info) := by
      change env.constants.find?' name = _
      rw [inputMapWF.find?'_eq_find?]
      exact old
    exact (wf.projectionReady.constructorHead name info oldFind).mono
      (replay.old_le primitiveResult safety)
  · have head :=
      (show AddInductBlock env.constants (input.venv safety)
          (VPrimitiveInductive.canonicalDecl types) finalEnv.constants
          (replay.output.venv safety) from
        ⟨pointwise.toTrace primitiveResult⟩).constructorHeadArity
          (wf.tr (safety := safety)).wf member
    have canonicalNumParams :
        (VPrimitiveInductive.canonicalDecl types).nparams = 0 := by
      unfold VPrimitiveInductive.canonicalDecl
      split <;> rfl
    rw [nameEq, canonicalNumParams, ← numParamsZero] at head
    exact head

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.CoherentCanonicalPrimitiveReplay.constructorHead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.abstract_eq,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms AddInductive.EnvironmentInductiveExecution.CoherentCanonicalPrimitiveReplay.constructorHead

/-- Canonical primitive insertion preserves projection readiness.  A final
ready family cannot be newly inserted because Bool and Nat each have two
constructors.  For an old family, exact constructor and recursor provenance
rules out activation by a newly inserted artifact, after which the original
registered projection artifact is retargeted to the final host map. -/
theorem projectionReady
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe true fuel finalEnv}
    {input : VEnvs}
    (replay : execution.CoherentCanonicalPrimitiveReplay input)
    (primitiveResult : PrimitiveInductiveResult lparams nparams types isUnsafe
      true) (wf : input.WF env) (safety : DefinitionSafety) :
    ProjectionResolutionReady finalEnv (replay.output.venv safety) where
  infer name info found ready := by
    have inputMapWF := (wf.tr (safety := safety)).map_wf
    let pointwise := replay.replays safety
    let trace := pointwise.toTrace primitiveResult
    have wfTypes := trace.addTypes.map_wf inputMapWF
    have wfCtors := trace.addCtors.map_wf wfTypes
    have finalMapWF := trace.addRecs.map_wf wfCtors
    have foundMap :
        finalEnv.constants.find? name = some (.inductInfo info) := by
      change finalEnv.constants.find?' name = _ at found
      rwa [finalMapWF.find?'_eq_find?] at found
    obtain ⟨ctor, ctorInfo, recInfo, ctorsEq, numIndicesEq,
        ctorFound, recFound, ctorOwner, familyRecursor⟩ :=
      Kernel.Environment.isProjectionReadyStructure_info found ready
    have ctorFoundMap :
        finalEnv.constants.find? ctor = some (.ctorInfo ctorInfo) := by
      change finalEnv.constants.find?' ctor = _ at ctorFound
      rwa [finalMapWF.find?'_eq_find?] at ctorFound
    have recFoundMap :
        finalEnv.constants.find? (mkRecName name) = some (.recInfo recInfo) := by
      change finalEnv.constants.find?' (mkRecName name) = _ at recFound
      rwa [finalMapWF.find?'_eq_find?] at recFound
    rcases pointwise.familyLookupCases primitiveResult inputMapWF foundMap with
      oldFamily | ⟨familyLength, _familyRaw⟩
    · rcases pointwise.constructorLookupCases primitiveResult inputMapWF
          ctorFoundMap with
        oldCtor | ⟨_numParams, _ctorRaw, familyRaw, familyMember, owner⟩
      · rcases trace.recursor_map_lookup_cases inputMapWF recFoundMap with
          oldRec | ⟨rawRec, recMember, recName⟩
        · have oldFamilyFind :
              env.find? name = some (.inductInfo info) := by
            change env.constants.find?' name = _
            rw [inputMapWF.find?'_eq_find?]
            exact oldFamily
          have oldCtorFind :
              env.find? ctor = some (.ctorInfo ctorInfo) := by
            change env.constants.find?' ctor = _
            rw [inputMapWF.find?'_eq_find?]
            exact oldCtor
          have oldRecFind :
              env.find? (mkRecName name) = some (.recInfo recInfo) := by
            change env.constants.find?' (mkRecName name) = _
            rw [inputMapWF.find?'_eq_find?]
            exact oldRec
          have inputReady : env.isProjectionReadyStructure name = true := by
            exact Kernel.Environment.isProjectionReadyStructure_of_info
              oldFamilyFind ctorsEq numIndicesEq oldCtorFind oldRecFind
              ctorOwner familyRecursor
          obtain ⟨artifact⟩ :=
            (wf.projectionReady (safety := safety)).infer name info
              oldFamilyFind inputReady
          have preserveArtifactLookup {artifactName : Name}
              {artifactInfo : ConstantInfo}
              (artifactFind : env.find? artifactName = some artifactInfo) :
              finalEnv.find? artifactName = some artifactInfo := by
            have artifactInputMap :
                env.constants.find? artifactName = some artifactInfo := by
              change env.constants.find?' artifactName = _ at artifactFind
              rwa [inputMapWF.find?'_eq_find?] at artifactFind
            have artifactTypeMap :=
              trace.addTypes.preserve_map_lookup inputMapWF artifactInputMap
            have artifactCtorMap :=
              trace.addCtors.preserve_map_lookup wfTypes artifactTypeMap
            have artifactFinalMap :=
              trace.addRecs.preserve_map_lookup wfCtors artifactCtorMap
            change finalEnv.constants.find?' artifactName = _
            rw [finalMapWF.find?'_eq_find?]
            exact artifactFinalMap
          exact ⟨artifact.retarget_of_preserved
            (replay.old_le primitiveResult safety) preserveArtifactLookup
              preserveArtifactLookup⟩
        · obtain ⟨familyRaw, familyMember, recOwner⟩ :=
            trace.generation.recursor_owner recMember
          have recNames : mkRecName familyRaw.name = mkRecName name :=
            recOwner.symm.trans recName
          have familyNameEq : familyRaw.name = name := by
            simpa [mkRecName] using recNames
          have fresh := trace.addTypes.map_fresh inputMapWF familyMember
          rw [familyNameEq, oldFamily] at fresh
          contradiction
      · have familyNameEq : familyRaw.name = name :=
          owner.symm.trans ctorOwner
        have fresh := trace.addTypes.map_fresh inputMapWF familyMember
        rw [familyNameEq, oldFamily] at fresh
        contradiction
    · rw [ctorsEq] at familyLength
      simp at familyLength
  constructorHead name info found :=
    replay.constructorHead primitiveResult wf safety found

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.CoherentCanonicalPrimitiveReplay.projectionReady' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.abstract_eq,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms AddInductive.EnvironmentInductiveExecution.CoherentCanonicalPrimitiveReplay.projectionReady

/-- Canonical primitive insertion preserves structure-eta readiness.  The
new Bool/Nat family cannot pass the one-constructor test, while constructor
ownership and family-name freshness prevent a new canonical constructor from
being paired with an old family. -/
theorem structureEtaReady
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe true fuel finalEnv}
    {input : VEnvs}
    (replay : execution.CoherentCanonicalPrimitiveReplay input)
    (primitiveResult : PrimitiveInductiveResult lparams nparams types isUnsafe
      true) (wf : input.WF env) (safety : DefinitionSafety) :
    StructureEtaReady finalEnv (replay.output.venv safety) where
  resolve familyName familyInfo constructorName constructorInfo familyFound
      constructorFound ready := by
    have inputMapWF := (wf.tr (safety := safety)).map_wf
    let pointwise := replay.replays safety
    let trace := pointwise.toTrace primitiveResult
    have wfTypes := trace.addTypes.map_wf inputMapWF
    have wfCtors := trace.addCtors.map_wf wfTypes
    have finalMapWF := trace.addRecs.map_wf wfCtors
    have familyFoundMap :
        finalEnv.constants.find? familyName =
          some (.inductInfo familyInfo) := by
      change finalEnv.constants.find?' familyName = _ at familyFound
      rwa [finalMapWF.find?'_eq_find?] at familyFound
    have constructorFoundMap :
        finalEnv.constants.find? constructorName =
          some (.ctorInfo constructorInfo) := by
      change finalEnv.constants.find?' constructorName = _ at constructorFound
      rwa [finalMapWF.find?'_eq_find?] at constructorFound
    obtain ⟨recInfo, recFound, isRecEq, ctorsEq, numIndicesEq, owner,
        levelParamsLt, familyRecursor⟩ :=
      Kernel.Environment.isStructureEtaReadyConstructor_info familyFound
        constructorFound ready
    have recFoundMap :
        finalEnv.constants.find? (mkRecName familyName) =
          some (.recInfo recInfo) := by
      change finalEnv.constants.find?' (mkRecName familyName) = _ at recFound
      rwa [finalMapWF.find?'_eq_find?] at recFound
    rcases pointwise.familyLookupCases primitiveResult inputMapWF
        familyFoundMap with
      oldFamily | ⟨familyLength, _familyRaw⟩
    · rcases pointwise.constructorLookupCases primitiveResult inputMapWF
          constructorFoundMap with
        oldConstructor |
          ⟨_numParams, _constructorRaw, familyRaw, familyMember,
            constructorOwner⟩
      · rcases trace.recursor_map_lookup_cases inputMapWF recFoundMap with
          oldRecursor | ⟨rawRecursor, recursorMember, recursorNameEq⟩
        · have oldFamilyFind :
              env.find? familyName = some (.inductInfo familyInfo) := by
            change env.constants.find?' familyName = _
            rw [inputMapWF.find?'_eq_find?]
            exact oldFamily
          have oldConstructorFind :
              env.find? constructorName = some (.ctorInfo constructorInfo) := by
            change env.constants.find?' constructorName = _
            rw [inputMapWF.find?'_eq_find?]
            exact oldConstructor
          have oldRecursorFind :
              env.find? (mkRecName familyName) = some (.recInfo recInfo) := by
            change env.constants.find?' (mkRecName familyName) = _
            rw [inputMapWF.find?'_eq_find?]
            exact oldRecursor
          have inputReady :
              env.isStructureEtaReadyConstructor familyName constructorName =
                true :=
            Kernel.Environment.isStructureEtaReadyConstructor_of_info
              oldFamilyFind oldConstructorFind oldRecursorFind isRecEq ctorsEq
                numIndicesEq owner levelParamsLt familyRecursor
          obtain ⟨artifact⟩ :=
            (wf.structureEtaReady (safety := safety)).resolve familyName
              familyInfo constructorName constructorInfo oldFamilyFind
              oldConstructorFind inputReady
          have preserveArtifactLookup {artifactName : Name}
              {artifactInfo : ConstantInfo}
              (artifactFind : env.find? artifactName = some artifactInfo) :
              finalEnv.find? artifactName = some artifactInfo := by
            have artifactInputMap :
                env.constants.find? artifactName = some artifactInfo := by
              change env.constants.find?' artifactName = _ at artifactFind
              rwa [inputMapWF.find?'_eq_find?] at artifactFind
            have artifactTypeMap :=
              trace.addTypes.preserve_map_lookup inputMapWF artifactInputMap
            have artifactCtorMap :=
              trace.addCtors.preserve_map_lookup wfTypes artifactTypeMap
            have artifactFinalMap :=
              trace.addRecs.preserve_map_lookup wfCtors artifactCtorMap
            change finalEnv.constants.find?' artifactName = _
            rw [finalMapWF.find?'_eq_find?]
            exact artifactFinalMap
          exact ⟨artifact.retarget_of_preserved
            (replay.old_le primitiveResult safety)
            (replay.outputWF primitiveResult wf safety).ordered
            preserveArtifactLookup preserveArtifactLookup⟩
        · obtain ⟨familyRaw, familyMember, recursorOwner⟩ :=
            trace.generation.recursor_owner recursorMember
          have recursorNames :
              mkRecName familyRaw.name = mkRecName familyName :=
            recursorOwner.symm.trans recursorNameEq
          have familyNameEq : familyRaw.name = familyName := by
            simpa [mkRecName] using recursorNames
          have fresh := trace.addTypes.map_fresh inputMapWF familyMember
          rw [familyNameEq, oldFamily] at fresh
          contradiction
      · have familyNameEq : familyRaw.name = familyName :=
          constructorOwner.symm.trans owner
        have fresh := trace.addTypes.map_fresh inputMapWF familyMember
        rw [familyNameEq, oldFamily] at fresh
        contradiction
    · rw [ctorsEq] at familyLength
      simp at familyLength

/--
info: 'Lean4Lean.AddInductive.EnvironmentInductiveExecution.CoherentCanonicalPrimitiveReplay.structureEtaReady' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.abstract_eq,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms AddInductive.EnvironmentInductiveExecution.CoherentCanonicalPrimitiveReplay.structureEtaReady

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
 Expr.mkData_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
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
 Expr.mkData_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
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
 Expr.mkData_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
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
 Expr.mkData_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
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
 Quot.sound,
 Expr.abstract_eq]
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
    ProjectionResolutionReady finalEnv (replay.output.venv safety)
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

/-- Low-level assembly of the primitive transaction package from a staged
replay.  This helper keeps final-environment readiness explicit; the public
`ofExecution` constructor below derives both readiness fields from canonical
provenance. -/
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
      ProjectionResolutionReady finalEnv (replay.output.venv safety))
    (structureEtaReady : ∀ safety,
      StructureEtaReady finalEnv (replay.output.venv safety)) :
    execution.CanonicalPrimitiveTransactionalVEnvsExtension ves where
  primitiveResult := primitiveResult
  replay := replay
  projectionReady := projectionReady
  structureEtaReady := structureEtaReady

/-- Construct the complete primitive transaction directly from the retained
execution and input environment model.  Final projection and structure-eta
readiness are derived from exact canonical provenance rather than supplied by
the caller. -/
noncomputable def ofExecution
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe true fuel finalEnv}
    {ves : VEnvs} (wf : ves.WF env)
    (primitiveResult : PrimitiveInductiveResult lparams nparams types isUnsafe
      true) :
    execution.CanonicalPrimitiveTransactionalVEnvsExtension ves :=
  let replay :=
    execution.canonicalPrimitiveCoherentReplay primitiveResult ves wf
  .ofReplay primitiveResult replay
    (fun safety => replay.projectionReady primitiveResult wf safety)
    (fun safety => replay.structureEtaReady primitiveResult wf safety)

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
 Expr.mkData_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
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

namespace AddInductive.EnvironmentInductiveExecution.CoherentPrimitivePreservingTransactions

/-- Every final constructor in an ordinary coherent transaction carries a
completed Theory head with the host metadata's exact cached parameter count.
Old records reuse input readiness.  New records are identified by the exact
constructor fold; the retained family-validation counters align the host
count with the raw Theory source selected by outer staging. -/
theorem ordinaryConstructorHeadArity
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv}
    {source : VInductDecl} {input output : VEnvs}
    (transactions : execution.CoherentPrimitivePreservingTransactions source
      input output)
    (wf : input.WF env)
    (numNested_eq : execution.nested.aux2nested.size = 0)
    (source_nparams_eq : source.nparams = nparams) :
    ∀ name info, finalEnv.find? name = some (.ctorInfo info) →
      (output.venv .safe).ConstructorHeadArity name info.numParams := by
  intro name info found
  have inputMapWF := (wf.tr (safety := .safe)).map_wf
  let transaction := transactions.transaction .safe
  cases transaction with
  | nested numNested_ne _trace _typeNames _ctorNames _recNames =>
      exact (numNested_ne numNested_eq).elim
  | ordinary _traceNumNested trace _typeNames _ctorNames _recNames =>
      have typeMapWF := trace.addTypes.map_wf inputMapWF
      have ctorMapWF := trace.addCtors.map_wf typeMapWF
      have finalMapWF := trace.addRecs.map_wf ctorMapWF
      have foundMap :
          finalEnv.constants.find? name = some (.ctorInfo info) := by
        change finalEnv.constants.find?' name = _ at found
        rwa [finalMapWF.find?'_eq_find?] at found
      rcases trace.constructor_map_lookup_cases inputMapWF foundMap with
        old | ⟨raw, rawMember, rawName⟩
      · have oldFind : env.find? name = some (.ctorInfo info) := by
          change env.constants.find?' name = _
          rw [inputMapWF.find?'_eq_find?]
          exact old
        exact ((wf.projectionReady (safety := .safe)).constructorHead
          name info oldFind).mono trace.le
      · have rawInputFresh : env.constants.find? raw.name = none := by
          have typeFresh := trace.addCtors.map_fresh typeMapWF rawMember
          exact trace.addTypes.input_map_none_of_output_none inputMapWF
            typeFresh
        have infoParams : info.numParams =
            execution.flattened.eliminationExecution.normalization.stats.params.size := by
          rcases execution.ordinaryConstructorLookupCases numNested_eq
              inputMapWF foundMap with oldHost | inserted
          · rw [rawName, oldHost] at rawInputFresh
            contradiction
          · simpa only [
                AddInductive.NormalizationEliminationExecution.declaredConstructorInfos]
              using AddInductive.declaredConstructorInfos_numParams
                execution.flattened.eliminationExecution.normalization.stats
                execution.nested.types.toArray isUnsafe
                execution.flattened.eliminationExecution.constructorContext
                inserted.1
        have normalizationProduced := execution.flattened.normalization_run
          execution.flattenedRun
        have familyRun :=
          execution.flattened.eliminationExecution.normalization
            |>.familyValidationResult_run normalizationProduced
        have paramsSize :
            execution.flattened.eliminationExecution.normalization.stats.params.size =
              nparams :=
          (execution.flattened.eliminationExecution.normalization
            |>.familyValidationResult.sizes_of_run
              execution.nested.types_nonempty familyRun).1
        have hostSourceParams : info.numParams = source.nparams :=
          infoParams.trans (paramsSize.trans source_nparams_eq.symm)
        have sourceHead :=
          (show AddInductBlock env.constants (input.venv .safe) source
              finalEnv.constants (output.venv .safe) from ⟨trace⟩)
            |>.constructorHeadArity
              (wf.tr (safety := .safe)).wf rawMember
        simpa only [rawName, hostSourceParams] using sourceHead

/-- Every final constructor in a genuinely nested coherent transaction
carries a completed restored Theory head at the host metadata's exact cached
parameter count.  Restoration now owns that count directly, so the new case
does not depend on a caller-supplied metadata alignment. -/
theorem nestedConstructorHeadArity
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv}
    {source : VInductDecl} {input output : VEnvs}
    (transactions : execution.CoherentPrimitivePreservingTransactions source
      input output)
    (wf : input.WF env)
    (numNested_ne : execution.nested.aux2nested.size ≠ 0)
    (source_nparams_eq : source.nparams = nparams) :
    ∀ name info, finalEnv.find? name = some (.ctorInfo info) →
      (output.venv .safe).ConstructorHeadArity name info.numParams := by
  intro name info found
  have inputMapWF := (wf.tr (safety := .safe)).map_wf
  let transaction := transactions.transaction .safe
  cases transaction with
  | ordinary numNested_eq _trace _typeNames _ctorNames _recNames =>
      exact (numNested_ne numNested_eq).elim
  | nested _traceNumNested trace _typeNames _ctorNames _recNames =>
      have typeMapWF := trace.addTypes.map_wf inputMapWF
      have ctorMapWF := trace.addCtors.map_wf typeMapWF
      have finalMapWF := trace.addRecs.map_wf ctorMapWF
      have foundMap :
          finalEnv.constants.find? name = some (.ctorInfo info) := by
        change finalEnv.constants.find?' name = _ at found
        rwa [finalMapWF.find?'_eq_find?] at found
      rcases trace.constructor_map_lookup_cases inputMapWF foundMap with
        old | ⟨raw, rawMember, rawName⟩
      · have oldFind : env.find? name = some (.ctorInfo info) := by
          change env.constants.find?' name = _
          rw [inputMapWF.find?'_eq_find?]
          exact old
        exact ((wf.projectionReady (safety := .safe)).constructorHead
          name info oldFind).mono
            (show AddInductNested env.constants (input.venv .safe) source
                finalEnv.constants (output.venv .safe) from ⟨trace⟩).le
      · have rawInputFresh : env.constants.find? raw.name = none := by
          have typeFresh := trace.addCtors.map_fresh typeMapWF rawMember
          exact trace.addTypes.input_map_none_of_output_none inputMapWF
            typeFresh
        have restoredParams : info.numParams = execution.nested.nparams := by
          rcases execution.nestedConstructorLookupCases numNested_ne
              inputMapWF foundMap with oldHost | inserted
          · rw [rawName, oldHost] at rawInputFresh
            contradiction
          · exact restoredNestedInfos_constructor_numParams inserted.1
        have nestedParams : execution.nested.nparams = nparams :=
          ElimNestedInductive.runAt_nparams_eq execution.nestedRun
        have hostSourceParams : info.numParams = source.nparams :=
          restoredParams.trans (nestedParams.trans source_nparams_eq.symm)
        have sourceHead :=
          (show AddInductNested env.constants (input.venv .safe) source
              finalEnv.constants (output.venv .safe) from ⟨trace⟩)
            |>.constructorHeadArity
              (wf.tr (safety := .safe)).wf rawMember
        simpa only [rawName, hostSourceParams] using sourceHead

/-- Assemble projection readiness for an ordinary coherent transaction from
only the newly activated projection artifacts.  A family that was already
ready in the input model is retargeted through the exact family,
constructor, and recursor folds; constructor arity is supplied by
`ordinaryConstructorHeadArity`, not by the delta producer. -/
theorem ordinaryProjectionReady
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv}
    {source : VInductDecl} {input output : VEnvs}
    (transactions : execution.CoherentPrimitivePreservingTransactions source
      input output)
    (wf : input.WF env)
    (numNested_eq : execution.nested.aux2nested.size = 0)
    (source_nparams_eq : source.nparams = nparams)
    (delta : ProjectionArtifactDeltaReady env finalEnv
      (output.venv .safe)) :
    ProjectionResolutionReady finalEnv (output.venv .safe) where
  infer name info found ready := by
    by_cases old : env.find? name = some (.inductInfo info) ∧
        env.isProjectionReadyStructure name = true
    · obtain ⟨artifact⟩ :=
        (wf.projectionReady (safety := .safe)).infer name info old.1 old.2
      have inputMapWF := (wf.tr (safety := .safe)).map_wf
      let transaction := transactions.transaction .safe
      cases transaction with
      | nested numNested_ne _trace _typeNames _ctorNames _recNames =>
          exact (numNested_ne numNested_eq).elim
      | ordinary _traceNumNested trace _typeNames _ctorNames _recNames =>
          have typeMapWF := trace.addTypes.map_wf inputMapWF
          have ctorMapWF := trace.addCtors.map_wf typeMapWF
          have finalMapWF := trace.addRecs.map_wf ctorMapWF
          have preserveArtifactLookup {artifactName : Name}
              {artifactInfo : ConstantInfo}
              (artifactFind : env.find? artifactName = some artifactInfo) :
              finalEnv.find? artifactName = some artifactInfo := by
            have artifactInputMap :
                env.constants.find? artifactName = some artifactInfo := by
              change env.constants.find?' artifactName = _ at artifactFind
              rwa [inputMapWF.find?'_eq_find?] at artifactFind
            have artifactTypeMap :=
              trace.addTypes.preserve_map_lookup inputMapWF artifactInputMap
            have artifactCtorMap :=
              trace.addCtors.preserve_map_lookup typeMapWF artifactTypeMap
            have artifactFinalMap :=
              trace.addRecs.preserve_map_lookup ctorMapWF artifactCtorMap
            change finalEnv.constants.find?' artifactName = _
            rw [finalMapWF.find?'_eq_find?]
            exact artifactFinalMap
          exact ⟨artifact.retarget_of_preserved trace.le
            preserveArtifactLookup preserveArtifactLookup⟩
    · obtain ⟨artifact⟩ := delta name info found ready old
      exact ⟨.ordinary artifact⟩
  constructorHead name info found :=
    transactions.ordinaryConstructorHeadArity wf numNested_eq
      source_nparams_eq name info found

/-- The ordinary readiness transaction is also a resolution-aware transaction;
all of its newly produced artifacts select the ordinary backend. -/
theorem ordinaryProjectionResolutionReady
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv}
    {source : VInductDecl} {input output : VEnvs}
    (transactions : execution.CoherentPrimitivePreservingTransactions source
      input output)
    (wf : input.WF env)
    (numNested_eq : execution.nested.aux2nested.size = 0)
    (source_nparams_eq : source.nparams = nparams)
    (delta : ProjectionArtifactDeltaReady env finalEnv
      (output.venv .safe)) :
    ProjectionResolutionReady finalEnv (output.venv .safe) :=
  transactions.ordinaryProjectionReady wf numNested_eq source_nparams_eq delta

/-- Assemble projection readiness for a genuinely nested coherent
transaction from only newly activated family artifacts.  Old artifacts are
retargeted through the restored transaction, while exact constructor arity is
derived by `nestedConstructorHeadArity`. -/
theorem nestedProjectionReady
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv}
    {source : VInductDecl} {input output : VEnvs}
    (transactions : execution.CoherentPrimitivePreservingTransactions source
      input output)
    (wf : input.WF env)
    (numNested_ne : execution.nested.aux2nested.size ≠ 0)
    (source_nparams_eq : source.nparams = nparams)
    (delta : ProjectionArtifactDeltaReady env finalEnv
      (output.venv .safe)) :
    ProjectionResolutionReady finalEnv (output.venv .safe) where
  infer name info found ready := by
    by_cases old : env.find? name = some (.inductInfo info) ∧
        env.isProjectionReadyStructure name = true
    · obtain ⟨artifact⟩ :=
        (wf.projectionReady (safety := .safe)).infer name info old.1 old.2
      have inputMapWF := (wf.tr (safety := .safe)).map_wf
      let transaction := transactions.transaction .safe
      cases transaction with
      | ordinary numNested_eq _trace _typeNames _ctorNames _recNames =>
          exact (numNested_ne numNested_eq).elim
      | nested _traceNumNested trace _typeNames _ctorNames _recNames =>
          have typeMapWF := trace.addTypes.map_wf inputMapWF
          have ctorMapWF := trace.addCtors.map_wf typeMapWF
          have finalMapWF := trace.addRecs.map_wf ctorMapWF
          have preserveArtifactLookup {artifactName : Name}
              {artifactInfo : ConstantInfo}
              (artifactFind : env.find? artifactName = some artifactInfo) :
              finalEnv.find? artifactName = some artifactInfo := by
            have artifactInputMap :
                env.constants.find? artifactName = some artifactInfo := by
              change env.constants.find?' artifactName = _ at artifactFind
              rwa [inputMapWF.find?'_eq_find?] at artifactFind
            have artifactTypeMap :=
              trace.addTypes.preserve_map_lookup inputMapWF artifactInputMap
            have artifactCtorMap :=
              trace.addCtors.preserve_map_lookup typeMapWF artifactTypeMap
            have artifactFinalMap :=
              trace.addRecs.preserve_map_lookup ctorMapWF artifactCtorMap
            change finalEnv.constants.find?' artifactName = _
            rw [finalMapWF.find?'_eq_find?]
            exact artifactFinalMap
          exact ⟨artifact.retarget_of_preserved
            (show AddInductNested env.constants (input.venv .safe) source
                finalEnv.constants (output.venv .safe) from ⟨trace⟩).le
            preserveArtifactLookup preserveArtifactLookup⟩
    · obtain ⟨artifact⟩ := delta name info found ready old
      exact ⟨.ordinary artifact⟩
  constructorHead name info found :=
    transactions.nestedConstructorHeadArity wf numNested_ne
      source_nparams_eq name info found

/-- Assemble resolution-aware projection readiness for a genuinely nested
coherent transaction.  Input families retain their ordinary artifact through
the exact restored folds; a newly activated family is supplied by the
resolution delta and may therefore select the restored backend honestly. -/
theorem nestedProjectionResolutionReady
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv}
    {source : VInductDecl} {input output : VEnvs}
    (transactions : execution.CoherentPrimitivePreservingTransactions source
      input output)
    (wf : input.WF env)
    (numNested_ne : execution.nested.aux2nested.size ≠ 0)
    (source_nparams_eq : source.nparams = nparams)
    (delta : ProjectionArtifactResolutionDeltaReady env finalEnv
      (output.venv .safe)) :
    ProjectionResolutionReady finalEnv (output.venv .safe) where
  infer name info found ready := by
    by_cases old : env.find? name = some (.inductInfo info) ∧
        env.isProjectionReadyStructure name = true
    · obtain ⟨artifact⟩ :=
        (wf.projectionReady (safety := .safe)).infer name info old.1 old.2
      have inputMapWF := (wf.tr (safety := .safe)).map_wf
      let transaction := transactions.transaction .safe
      cases transaction with
      | ordinary numNested_eq _trace _typeNames _ctorNames _recNames =>
          exact (numNested_ne numNested_eq).elim
      | nested _traceNumNested trace _typeNames _ctorNames _recNames =>
          have typeMapWF := trace.addTypes.map_wf inputMapWF
          have ctorMapWF := trace.addCtors.map_wf typeMapWF
          have finalMapWF := trace.addRecs.map_wf ctorMapWF
          have preserveArtifactLookup {artifactName : Name}
              {artifactInfo : ConstantInfo}
              (artifactFind : env.find? artifactName = some artifactInfo) :
              finalEnv.find? artifactName = some artifactInfo := by
            have artifactInputMap :
                env.constants.find? artifactName = some artifactInfo := by
              change env.constants.find?' artifactName = _ at artifactFind
              rwa [inputMapWF.find?'_eq_find?] at artifactFind
            have artifactTypeMap :=
              trace.addTypes.preserve_map_lookup inputMapWF artifactInputMap
            have artifactCtorMap :=
              trace.addCtors.preserve_map_lookup typeMapWF artifactTypeMap
            have artifactFinalMap :=
              trace.addRecs.preserve_map_lookup ctorMapWF artifactCtorMap
            change finalEnv.constants.find?' artifactName = _
            rw [finalMapWF.find?'_eq_find?]
            exact artifactFinalMap
          exact ⟨artifact.retarget_of_preserved
            (show AddInductNested env.constants (input.venv .safe) source
                finalEnv.constants (output.venv .safe) from ⟨trace⟩).le
            preserveArtifactLookup preserveArtifactLookup⟩
    · exact delta name info found ready old
  constructorHead name info found :=
    transactions.nestedConstructorHeadArity wf numNested_ne
      source_nparams_eq name info found

/-- In an ordinary retained execution, the flattened host source-family list
is a complete finite scan domain for structure-eta registration.  An accepted
final structure whose family and constructor are both old is transported from
input readiness; otherwise retained declaration provenance identifies a
flattened source family and the recursor producer supplies its final lookup. -/
theorem ordinaryStructureEtaRegistrationCoverage
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv}
    {source : VInductDecl} {input output : VEnvs}
    (transactions : execution.CoherentPrimitivePreservingTransactions source
      input output)
    (wf : input.WF env)
    (numNested_eq : execution.nested.aux2nested.size = 0) :
    ∀ familyName familyInfo constructorName constructorInfo,
      finalEnv.find? familyName = some (.inductInfo familyInfo) →
      finalEnv.find? constructorName = some (.ctorInfo constructorInfo) →
      finalEnv.isStructureEtaReadyConstructor familyName constructorName =
        true →
      Nonempty (StructureEtaArtifactResolution finalEnv familyName familyInfo
        constructorName constructorInfo (output.venv .safe)) ∨
        familyName ∈ execution.nested.types.map (·.name) ∧
          ∃ recursorInfo, finalEnv.find? (mkRecName familyName) =
            some (.recInfo recursorInfo) := by
  intro familyName familyInfo constructorName constructorInfo familyFound
    constructorFound ready
  have inputMapWF := (wf.tr (safety := .safe)).map_wf
  have finalMapWF := execution.ordinaryFinalMapWF numNested_eq inputMapWF
  have familyFoundMap :
      finalEnv.constants.find? familyName =
        some (.inductInfo familyInfo) := by
    change finalEnv.constants.find?' familyName = _ at familyFound
    rwa [finalMapWF.find?'_eq_find?] at familyFound
  have constructorFoundMap :
      finalEnv.constants.find? constructorName =
        some (.ctorInfo constructorInfo) := by
    change finalEnv.constants.find?' constructorName = _ at constructorFound
    rwa [finalMapWF.find?'_eq_find?] at constructorFound
  obtain ⟨recursorInfo, recursorFound, isRecEq, ctorsEq, numIndicesEq, owner,
      levelParamsLt, familyRecursor⟩ :=
    Kernel.Environment.isStructureEtaReadyConstructor_info familyFound
      constructorFound ready
  have recursorFoundMap :
      finalEnv.constants.find? (mkRecName familyName) =
        some (.recInfo recursorInfo) := by
    change finalEnv.constants.find?' (mkRecName familyName) = _ at recursorFound
    rwa [finalMapWF.find?'_eq_find?] at recursorFound
  have registrationOfSource (indType : InductiveType)
      (sourceMember : indType ∈ execution.nested.types)
      (familyNameEq : indType.name = familyName) :
      familyName ∈ execution.nested.types.map (·.name) ∧
        ∃ recursorInfo, finalEnv.find? (mkRecName familyName) =
          some (.recInfo recursorInfo) := by
    refine ⟨List.mem_map.mpr ⟨indType, sourceMember, familyNameEq⟩, ?_⟩
    obtain ⟨recursorInfo, recursorLookup⟩ :=
      execution.ordinaryRecursorLookupOfSourceFamily numNested_eq inputMapWF
        sourceMember
    refine ⟨recursorInfo, ?_⟩
    change finalEnv.constants.find?' (mkRecName familyName) = _
    rw [finalMapWF.find?'_eq_find?]
    simpa only [familyNameEq] using recursorLookup
  rcases execution.ordinaryFamilyLookupCases numNested_eq inputMapWF
      familyFoundMap with oldFamily | newFamily
  · rcases execution.ordinaryConstructorLookupCases numNested_eq inputMapWF
        constructorFoundMap with oldConstructor | newConstructor
    · have oldFamilyFind :
          env.find? familyName = some (.inductInfo familyInfo) := by
        change env.constants.find?' familyName = _
        rw [inputMapWF.find?'_eq_find?]
        exact oldFamily
      have oldConstructorFind :
          env.find? constructorName = some (.ctorInfo constructorInfo) := by
        change env.constants.find?' constructorName = _
        rw [inputMapWF.find?'_eq_find?]
        exact oldConstructor
      rcases execution.ordinaryRecursorLookupCases numNested_eq inputMapWF
          recursorFoundMap with oldRecursor | newRecursor
      · have oldRecursorFind :
            env.find? (mkRecName familyName) =
              some (.recInfo recursorInfo) := by
          change env.constants.find?' (mkRecName familyName) = _
          rw [inputMapWF.find?'_eq_find?]
          exact oldRecursor
        have inputReady :
            env.isStructureEtaReadyConstructor familyName constructorName =
              true :=
          Kernel.Environment.isStructureEtaReadyConstructor_of_info
            oldFamilyFind oldConstructorFind oldRecursorFind isRecEq ctorsEq
              numIndicesEq owner levelParamsLt familyRecursor
        obtain ⟨artifact⟩ :=
          (wf.structureEtaReady (safety := .safe)).resolve familyName familyInfo
            constructorName constructorInfo oldFamilyFind oldConstructorFind
            inputReady
        have outputWF : (output.venv .safe).WF :=
          ((transactions.transaction .safe).toExact.trEnv
            (wf.tr (safety := .safe))).wf
        let transaction := transactions.transaction .safe
        cases transaction with
        | nested numNested_ne _trace _typeNames _ctorNames _recNames =>
            exact (numNested_ne numNested_eq).elim
        | ordinary _traceNumNested trace _typeNames _ctorNames _recNames =>
            have typeMapWF := trace.addTypes.map_wf inputMapWF
            have ctorMapWF := trace.addCtors.map_wf typeMapWF
            have finalMapWF := trace.addRecs.map_wf ctorMapWF
            have preserveArtifactLookup {artifactName : Name}
                {artifactInfo : ConstantInfo}
                (artifactFind : env.find? artifactName = some artifactInfo) :
                finalEnv.find? artifactName = some artifactInfo := by
              have artifactInputMap :
                  env.constants.find? artifactName = some artifactInfo := by
                change env.constants.find?' artifactName = _ at artifactFind
                rwa [inputMapWF.find?'_eq_find?] at artifactFind
              have artifactTypeMap :=
                trace.addTypes.preserve_map_lookup inputMapWF artifactInputMap
              have artifactCtorMap :=
                trace.addCtors.preserve_map_lookup typeMapWF artifactTypeMap
              have artifactFinalMap :=
                trace.addRecs.preserve_map_lookup ctorMapWF artifactCtorMap
              change finalEnv.constants.find?' artifactName = _
              rw [finalMapWF.find?'_eq_find?]
              exact artifactFinalMap
            exact .inl ⟨artifact.retarget_of_preserved trace.le
              outputWF.ordered preserveArtifactLookup preserveArtifactLookup⟩
      · have recursorNameMember : recursorInfo.name ∈
            execution.flattened.recursors.infos.map (·.name) :=
          List.mem_map.mpr ⟨recursorInfo, newRecursor.1, rfl⟩
        rw [AddInductive.declareRecursors_infos_names
          execution.flattened.recursorsRun] at recursorNameMember
        obtain ⟨indType, sourceMember, sourceRecursorNameEq⟩ :=
          List.mem_map.mp recursorNameMember
        have familyNameEq : indType.name = familyName := by
          have nameEq := sourceRecursorNameEq.trans newRecursor.2
          simpa [mkRecName] using nameEq
        exact .inr <| registrationOfSource indType (by simpa using sourceMember)
          familyNameEq
    · obtain ⟨indType, sourceMember, constructorOwner⟩ :=
        execution.ordinaryDeclaredConstructorSource newConstructor.1
      exact .inr <| registrationOfSource indType sourceMember
        (constructorOwner.symm.trans owner)
  · obtain ⟨indType, sourceMember, sourceName⟩ :=
      execution.ordinaryDeclaredFamilySource newFamily.1
    exact .inr <| registrationOfSource indType sourceMember
      (sourceName.symm.trans newFamily.2)

/-- In a genuinely nested retained execution, the completed constant map is
a finite scan domain for structure-eta registration.  This is intentionally
broader than the source-family list: restoring an auxiliary recursor can make
an otherwise old family pass the recursor-sensitive eta gate, and the exact
map inventory covers that case without assuming a string-level inverse for
Lean's auxiliary-recursion naming scheme. -/
theorem nestedStructureEtaRegistrationCoverage
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv}
    {source : VInductDecl} {input output : VEnvs}
    (_transactions : execution.CoherentPrimitivePreservingTransactions source
      input output)
    (wf : input.WF env)
    (numNested_ne : execution.nested.aux2nested.size ≠ 0) :
    ∀ familyName familyInfo constructorName constructorInfo,
      finalEnv.find? familyName = some (.inductInfo familyInfo) →
      finalEnv.find? constructorName = some (.ctorInfo constructorInfo) →
      finalEnv.isStructureEtaReadyConstructor familyName constructorName =
        true →
      Nonempty (StructureEtaArtifactResolution finalEnv familyName familyInfo
        constructorName constructorInfo (output.venv .safe)) ∨
        familyName ∈ finalEnv.constants.toList'.map Prod.fst ∧
          ∃ recursorInfo, finalEnv.find? (mkRecName familyName) =
            some (.recInfo recursorInfo) := by
  intro familyName familyInfo constructorName constructorInfo familyFound
    constructorFound ready
  have inputMapWF := (wf.tr (safety := .safe)).map_wf
  have finalMapWF := execution.nestedFinalMapWF numNested_ne inputMapWF
  have familyFoundMap :
      finalEnv.constants.find? familyName =
        some (.inductInfo familyInfo) := by
    change finalEnv.constants.find?' familyName = _ at familyFound
    rwa [finalMapWF.find?'_eq_find?] at familyFound
  have familyLookup : finalEnv.constants.toList'.lookup familyName =
      some (.inductInfo familyInfo) := by
    rw [← finalMapWF.find?_eq]
    exact familyFoundMap
  obtain ⟨front, back, listEq, _frontFresh⟩ :=
    List.lookup_eq_some_iff.mp familyLookup
  have familyMember :
      familyName ∈ finalEnv.constants.toList'.map Prod.fst := by
    rw [listEq]
    simp
  obtain ⟨recursorInfo, recursorFound, _isRecEq, _ctorsEq, _numIndicesEq,
      _owner, _levelParamsLt, _familyRecursor⟩ :=
    Kernel.Environment.isStructureEtaReadyConstructor_info familyFound
      constructorFound ready
  exact .inr ⟨familyMember, recursorInfo, recursorFound⟩

end AddInductive.EnvironmentInductiveExecution.CoherentPrimitivePreservingTransactions

/-- The exact nested producer closes resolution-aware projection readiness at
its public restored endpoint.  Old ordinary artifacts are replayed through the
transaction, while every newly ready family resolves to the restored artifact
constructed by the exact producer. -/
theorem
    AddInductive.EnvironmentInductiveExecution.FlattenedExactNestedProjectionParameterRun.projectionResolutionReady
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    {flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape}
    {metadata : VInductDecl.ExactProducedBlockMetadataPrefixRun flat.run}
    {after : VEnv}
    {restoration : execution.FlattenedNestedRestorationResult artifact after}
    {numNested_ne : execution.nested.aux2nested.size ≠ 0}
    {restoredMetadata :
      execution.FlattenedNestedRestoredMetadataPrefixRun restoration
        numNested_ne}
    (run : execution.FlattenedExactNestedProjectionParameterRun flat metadata
      restoration numNested_ne restoredMetadata)
    (wf : ves.WF env) :
    ProjectionResolutionReady finalEnv after := by
  let replay := run.transaction.safeReplay wf
  have delta : ProjectionArtifactResolutionDeltaReady env finalEnv
      (replay.output.venv .safe) := by
    simpa only [replay.safe_output_eq] using
      run.projectionArtifactResolutionDeltaReady wf
  have ready :=
    replay.transactions.nestedProjectionResolutionReady wf numNested_ne
      artifact.source_nparams_eq delta
  simpa only [replay.safe_output_eq] using ready

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
    ProjectionResolutionReady finalEnv (output.venv safety)
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
    ProjectionResolutionReady finalEnv (transactionOutput.venv safety)
  /-- Every host nonrecursive structure is either already registered at the
  transaction boundary or is backed by an exact artifact in `etaRules`. -/
  structureEtaCoverage : ∀ safety,
    StructureEtaRegistrationCoverage finalEnv
      (transactionOutput.venv safety) etaRules

namespace AddInductive.EnvironmentInductiveExecution.ReadinessCompletedNonprimitiveVEnvsExtension

/-- Construct the shared Theory-only completion from pointwise certificates
for one common rule list.  The safety-indexed output family is computed
internally as the exact registration fold; callers retain only the substantive
rule-WF and host-coverage obligations. -/
def ofRules
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv}
    {ves : VEnvs}
    (source : VInductDecl)
    (transactionOutput : VEnvs)
    (transaction : execution.CoherentPrimitivePreservingTransactions source
      ves transactionOutput)
    (etaRules : List VStructEta)
    (etaRulesWF : ∀ safety rule, rule ∈ etaRules →
      rule.WF (transactionOutput.venv safety))
    (projectionReadyBase : ∀ safety,
      ProjectionResolutionReady finalEnv (transactionOutput.venv safety))
    (structureEtaCoverage : ∀ safety,
      StructureEtaRegistrationCoverage finalEnv
        (transactionOutput.venv safety) etaRules) :
    execution.ReadinessCompletedNonprimitiveVEnvsExtension ves :=
  {
    source := source
    transactionOutput := transactionOutput
    output := ⟨fun safety =>
      etaRules.foldl VEnv.addStructEta (transactionOutput.venv safety)⟩
    transaction := transaction
    etaRules := etaRules
    completion := fun safety =>
      VEnv.AddStructEtas.of_forallWF (etaRulesWF safety)
    projectionReadyBase := projectionReadyBase
    structureEtaCoverage := structureEtaCoverage }

/-- A shared registration plan only needs to be certified in the smallest
`.safe` Theory model.  Coherent replay transports that model into every other
safety level, preserving both the rule certificates and the exact coverage
list; projection readiness is monotone along the same relation. -/
def ofSafeRules
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv}
    {ves : VEnvs}
    (wf : ves.WF env)
    (source : VInductDecl)
    (transactionOutput : VEnvs)
    (transaction : execution.CoherentPrimitivePreservingTransactions source
      ves transactionOutput)
    (etaRules : List VStructEta)
    (etaRulesWF : ∀ rule, rule ∈ etaRules →
      rule.WF (transactionOutput.venv .safe))
    (projectionReadySafe :
      ProjectionResolutionReady finalEnv (transactionOutput.venv .safe))
    (structureEtaCoverageSafe :
      StructureEtaRegistrationCoverage finalEnv
        (transactionOutput.venv .safe) etaRules) :
    execution.ReadinessCompletedNonprimitiveVEnvsExtension ves := by
  have output_le (safety : DefinitionSafety) :
      transactionOutput.venv .safe ≤ transactionOutput.venv safety :=
    transaction.mono wf.mono (safety := safety) (safety' := .safe)
      DefinitionSafety.le_safe
  have output_wf (safety : DefinitionSafety) :
      (transactionOutput.venv safety).WF :=
    ((transaction.transaction safety).toExact.trEnv
      (wf.tr (safety := safety))).wf
  exact ofRules source transactionOutput transaction etaRules
    (fun safety rule member =>
      (etaRulesWF rule member).mono (output_le safety))
    (fun safety => projectionReadySafe.mono (output_le safety))
    (fun safety => structureEtaCoverageSafe.mono (output_le safety)
      (output_wf safety))

/-- Complete a coherent nonprimitive replay from one finite safe-model
artifact plan.  Its common rule list, persistent rule certificates, and base
coverage are all projections of the plan rather than parallel inputs. -/
def ofSafePlan
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv}
    {ves : VEnvs}
    (wf : ves.WF env)
    (source : VInductDecl)
    (transactionOutput : VEnvs)
    (transaction : execution.CoherentPrimitivePreservingTransactions source
      ves transactionOutput)
    (projectionReadySafe :
      ProjectionResolutionReady finalEnv (transactionOutput.venv .safe))
    (plan : StructureEtaRegistrationPlan finalEnv
      (transactionOutput.venv .safe)) :
    execution.ReadinessCompletedNonprimitiveVEnvsExtension ves :=
  ofSafeRules wf source transactionOutput transaction plan.rules plan.rulesWF
    projectionReadySafe plan.toCoverage

/-- Complete a coherent nonprimitive replay directly from a finite
family-name inventory.  Host observations select the registration artifacts,
the plan derives their shared rule list, and safe-model transport supplies all
other safety levels. -/
noncomputable def ofSafeFamilyNames
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv}
    {ves : VEnvs}
    (wf : ves.WF env)
    (source : VInductDecl)
    (transactionOutput : VEnvs)
    (transaction : execution.CoherentPrimitivePreservingTransactions source
      ves transactionOutput)
    (projectionReadySafe :
      ProjectionResolutionReady finalEnv (transactionOutput.venv .safe))
    (familyNames : List Name)
    (coverage : ∀ familyName familyInfo constructorName constructorInfo,
      finalEnv.find? familyName = some (.inductInfo familyInfo) →
      finalEnv.find? constructorName = some (.ctorInfo constructorInfo) →
      finalEnv.isStructureEtaReadyConstructor familyName constructorName =
        true →
      Nonempty (StructureEtaArtifactResolution finalEnv familyName familyInfo
        constructorName constructorInfo (transactionOutput.venv .safe)) ∨
        familyName ∈ familyNames ∧
          ∃ recursorInfo, finalEnv.find? (mkRecName familyName) =
            some (.recInfo recursorInfo)) :
    execution.ReadinessCompletedNonprimitiveVEnvsExtension ves := by
  have output_wf : (transactionOutput.venv .safe).WF :=
    ((transaction.transaction .safe).toExact.trEnv
      (wf.tr (safety := .safe))).wf
  exact ofSafePlan wf source transactionOutput transaction
    projectionReadySafe
    (StructureEtaRegistrationPlan.ofFamilyNames projectionReadySafe output_wf
      familyNames coverage)

/-- Complete an ordinary coherent nonprimitive replay without a separately
supplied scan domain or coverage proof.  The retained flattened source-family
names are the finite domain, and exact host declaration provenance proves the
classification consumed by `ofSafeFamilyNames`. -/
noncomputable def ofOrdinaryTransaction
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv}
    {ves : VEnvs}
    (wf : ves.WF env)
    (source : VInductDecl)
    (transactionOutput : VEnvs)
    (transaction : execution.CoherentPrimitivePreservingTransactions source
      ves transactionOutput)
    (projectionReadySafe :
      ProjectionResolutionReady finalEnv (transactionOutput.venv .safe))
    (numNested_eq : execution.nested.aux2nested.size = 0) :
    execution.ReadinessCompletedNonprimitiveVEnvsExtension ves :=
  ofSafeFamilyNames wf source transactionOutput transaction
    projectionReadySafe (execution.nested.types.map (·.name))
    (transaction.ordinaryStructureEtaRegistrationCoverage wf numNested_eq)

/-- Complete a genuinely nested coherent nonprimitive replay without a
separately supplied scan domain or coverage proof.  The completed host map is
the finite domain, covering both restored source recursors and any
recursor-sensitive activation caused by the auxiliary restored inventory. -/
noncomputable def ofNestedTransaction
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv}
    {ves : VEnvs}
    (wf : ves.WF env)
    (source : VInductDecl)
    (transactionOutput : VEnvs)
    (transaction : execution.CoherentPrimitivePreservingTransactions source
      ves transactionOutput)
    (projectionReadySafe :
      ProjectionResolutionReady finalEnv (transactionOutput.venv .safe))
    (numNested_ne : execution.nested.aux2nested.size ≠ 0) :
    execution.ReadinessCompletedNonprimitiveVEnvsExtension ves :=
  ofSafeFamilyNames wf source transactionOutput transaction
    projectionReadySafe (finalEnv.constants.toList'.map Prod.fst)
    (transaction.nestedStructureEtaRegistrationCoverage wf numNested_ne)

/-- Complete either branch of a coherent nonprimitive replay directly from
its retained execution.  The branch test selects the flattened or restored
finite family inventory internally. -/
noncomputable def ofTransaction
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv}
    {ves : VEnvs}
    (wf : ves.WF env)
    (source : VInductDecl)
    (transactionOutput : VEnvs)
    (transaction : execution.CoherentPrimitivePreservingTransactions source
      ves transactionOutput)
    (projectionReadySafe :
      ProjectionResolutionReady finalEnv (transactionOutput.venv .safe)) :
    execution.ReadinessCompletedNonprimitiveVEnvsExtension ves := by
  by_cases numNested_eq : execution.nested.aux2nested.size = 0
  · exact ofOrdinaryTransaction wf source transactionOutput transaction
      projectionReadySafe numNested_eq
  · exact ofNestedTransaction wf source transactionOutput transaction
      projectionReadySafe numNested_eq

/-- Feed the endpoint retained by one exact safe replay directly into the
readiness-completion layer.  The replay owns the common safety-indexed
transaction family; callers only prove projection readiness at its named
`.safe` endpoint. -/
noncomputable def ofSafeReplay
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {isUnsafe allowPrimitive : Bool}
    {fuel : FuelConfig} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv}
    {ves : VEnvs} {source : VInductDecl} {safeOutput : VEnv}
    (wf : ves.WF env)
    (replay :
      AddInductive.EnvironmentInductiveExecution.CoherentPrimitivePreservingTransactions.SafeReplay
        execution source ves safeOutput)
    (projectionReadySafe : ProjectionResolutionReady finalEnv safeOutput) :
    execution.ReadinessCompletedNonprimitiveVEnvsExtension ves :=
  ofTransaction wf source replay.output replay.transactions (by
    simpa only [replay.safe_output_eq] using projectionReadySafe)

/-- Complete an exact ordinary flattened transaction at its named rule-fold
endpoint.  Exact replay transports old projection artifacts and derives
constructor-head arity, so the producer supplies only artifacts for families
whose projection-ready status is newly activated by this transaction. -/
noncomputable def ofExactOrdinary
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {generation : VInductDecl.BlockGenerationChecked staged.source}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    (result : execution.FlattenedExactRecursorStagingResult staged generation
      shape)
    (metadata : VInductDecl.ExactProducedBlockMetadataPrefixRun result.run)
    (numNested_eq : execution.nested.aux2nested.size = 0)
    (wf : ves.WF env)
    (projectionArtifactDeltaSafe : ProjectionArtifactDeltaReady env finalEnv
      (generation.generatedRules.foldl VEnv.addDefEq
        metadata.recursors.recEnv)) :
    execution.ReadinessCompletedNonprimitiveVEnvsExtension ves := by
  let replay := result.ordinarySafeReplay metadata numNested_eq wf
  have delta : ProjectionArtifactDeltaReady env finalEnv
      (replay.output.venv .safe) := by
    simpa only [replay.safe_output_eq] using projectionArtifactDeltaSafe
  have ready : ProjectionResolutionReady finalEnv
      (replay.output.venv .safe) :=
    replay.transactions.ordinaryProjectionReady wf numNested_eq
      staged.source_nparams_eq delta
  exact ofSafeReplay wf replay (by
    simpa only [replay.safe_output_eq] using ready)

/-- Complete a canonical semantic ordinary transaction at its named
rule-fold endpoint.  This is the outer V3.5 handoff for the mixed raw/view
generation route: coherent replay is derived from the dependent semantic
result, while the remaining projection input contains only newly activated
family artifacts at that exact computed endpoint. -/
def ofSemanticOrdinary
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    (result : execution.FlattenedSemanticRecursorStagingResult staged shape)
    (metadata : VInductDecl.ProducedBlockSemanticMetadataPrefixRun
      (staged.recursorShape shape) result.semantic result.generation
      result.run)
    (numNested_eq : execution.nested.aux2nested.size = 0)
    (wf : ves.WF env) :
    execution.ReadinessCompletedNonprimitiveVEnvsExtension ves := by
  let replay := result.ordinarySafeReplay metadata numNested_eq wf
  have projectionArtifactDeltaSafe :=
    result.projectionArtifactDeltaReady metadata numNested_eq wf
  have delta : ProjectionArtifactDeltaReady env finalEnv
      (replay.output.venv .safe) := by
    simpa only [replay.safe_output_eq] using projectionArtifactDeltaSafe
  have ready : ProjectionResolutionReady finalEnv
      (replay.output.venv .safe) :=
    replay.transactions.ordinaryProjectionReady wf numNested_eq
      staged.source_nparams_eq delta
  have resolver : ProjectionArtifactInventoryResolver finalEnv
      (replay.output.venv .safe)
      (execution.nested.types.map (·.name)) := by
    simpa only [replay.safe_output_eq] using
      result.projectionArtifactInventoryResolver metadata numNested_eq wf
  have outputWF : (replay.output.venv .safe).WF :=
    ((replay.transactions.transaction .safe).toExact.trEnv
      (wf.tr (safety := .safe))).wf
  let plan := StructureEtaRegistrationPlan.ofFamilyNamesWithInventoryResolver
    resolver outputWF
      (replay.transactions.ordinaryStructureEtaRegistrationCoverage wf
        numNested_eq)
  exact ofSafePlan wf staged.source replay.output replay.transactions ready plan

/-- Complete an exact genuinely nested transaction at its restored Theory
endpoint.  The aligned artifact, restoration, metadata, and cross-safety
replay are retained by the dependent transaction itself.  Exact restoration
retargets old projection artifacts and derives constructor-head arity, so the
remaining input contains only newly activated family artifacts. -/
noncomputable def ofExactNested
    {env : Environment} {lparams : List Name} {nparams : Nat}
    {types : List InductiveType} {finalEnv : Environment}
    {execution : AddInductive.EnvironmentInductiveExecution env lparams
      nparams types false false {} finalEnv}
    {ves : VEnvs}
    {staged : execution.FlattenedEnrichedStagingResult ves}
    {artifact : execution.FlattenedNestedArtifact staged}
    {shape : VInductDecl.normalizationCandidateBlockGenerationShape staged.source
      execution.flattened.candidate = true}
    {flat : execution.FlattenedExactRecursorStagingResult staged
      artifact.generation shape}
    {metadata : VInductDecl.ExactProducedBlockMetadataPrefixRun flat.run}
    {after : VEnv}
    {restoration : execution.FlattenedNestedRestorationResult artifact after}
    {numNested_ne : execution.nested.aux2nested.size ≠ 0}
    {restoredMetadata :
      execution.FlattenedNestedRestoredMetadataPrefixRun restoration
        numNested_ne}
    (run : execution.FlattenedExactNestedProjectionParameterRun flat
      metadata restoration numNested_ne restoredMetadata)
    (wf : ves.WF env) :
    execution.ReadinessCompletedNonprimitiveVEnvsExtension ves := by
  let replay := run.transaction.safeReplay wf
  have ready : ProjectionResolutionReady finalEnv
      (replay.output.venv .safe) := by
    simpa only [replay.safe_output_eq] using run.projectionResolutionReady wf
  exact ofSafeReplay wf replay (by
    simpa only [replay.safe_output_eq] using ready)

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
derived from the retained public normalization prefix; semantic completion is
supplied as pointwise `VEnvs` components for the exact outer execution. -/
theorem addDecl.inductDecl_WF_of_components
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (isUnsafe : Bool) (fuel : FuelConfig := {})
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
  · intro allowPrimitive _primitiveRun
    exact AddInductive.EnvironmentInductiveExecution.complete
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
    fuel
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
    isUnsafe fuel
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
    isUnsafe fuel
  intro allowPrimitive finalEnv execution primitiveRun
  exact (semantics allowPrimitive finalEnv execution primitiveRun)
    |>.toVEnvsExtension wf

/-- Primitive-aware transaction form of the inductive branch.  Ordinary
blocks use the readiness-completed, name-avoiding transaction path.  A
recognizer result of `true` selects the complete canonical `Bool`/`Nat`
transaction directly from the retained execution, so callers supply no
parallel primitive semantics and primitive reflection never has to be
approximated by the nonprimitive name-avoidance contract. -/
theorem addDecl.inductDecl_WF_of_split_primitive_transactions
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (isUnsafe : Bool) (fuel : FuelConfig := {})
    (nonprimitiveSemantics : ∀ finalEnv
        (execution : AddInductive.EnvironmentInductiveExecution env lparams
          nparams types isUnsafe false fuel finalEnv),
      Environment.checkPrimitiveInductive env lparams nparams types
          isUnsafe = .ok false →
        execution.ReadinessCompletedNonprimitiveVEnvsExtension ves) :
    (addDecl env (.inductDecl lparams nparams types isUnsafe)
      (check := true) (fuel := fuel)).WF fun finalEnv =>
      ∃ ves' : VEnvs, ves'.WF finalEnv ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  apply addDecl.inductDecl_WF_of_components wf lparams nparams types
    isUnsafe fuel
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
      exact
        (AddInductive.EnvironmentInductiveExecution.CanonicalPrimitiveTransactionalVEnvsExtension.ofExecution
            wf primitiveResult).toTransactionalVEnvsExtension wf
        |>.toVEnvsExtension wf

/-- Default-fuel primitive split.  The retained public normalization prefix
closes operational completeness in both recognizer branches; callers provide
only nonprimitive semantic completion. -/
theorem addDecl.inductDecl_WF_of_split_primitive_transactions_default
    {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (lparams : List Name) (nparams : Nat) (types : List InductiveType)
    (isUnsafe : Bool)
    (nonprimitiveSemantics : ∀ finalEnv
        (execution : AddInductive.EnvironmentInductiveExecution env lparams
          nparams types isUnsafe false {} finalEnv),
      Environment.checkPrimitiveInductive env lparams nparams types
          isUnsafe = .ok false →
        execution.ReadinessCompletedNonprimitiveVEnvsExtension ves) :
    (addDecl env (.inductDecl lparams nparams types isUnsafe)
      (check := true) (fuel := {})).WF fun finalEnv =>
      ∃ ves' : VEnvs, ves'.WF finalEnv ∧
        ∀ safety, ves.venv safety ≤ ves'.venv safety := by
  apply addDecl.inductDecl_WF_of_execution wf lparams nparams types
    isUnsafe {}
  · intro allowPrimitive _primitiveRun
    exact AddInductive.EnvironmentInductiveExecution.complete
  · intro allowPrimitive finalEnv execution primitiveRun
    cases allowPrimitive with
    | false =>
        exact (nonprimitiveSemantics finalEnv execution primitiveRun)
          |>.toVEnvsExtension wf
          |>.toPreservesVEnvs
    | true =>
        have primitiveResult :
            PrimitiveInductiveResult lparams nparams types isUnsafe true :=
          checkPrimitiveInductive.WF env lparams nparams types isUnsafe
            true primitiveRun
        exact
          (AddInductive.EnvironmentInductiveExecution.CanonicalPrimitiveTransactionalVEnvsExtension.ofExecution
              wf primitiveResult).toTransactionalVEnvsExtension wf
          |>.toVEnvsExtension wf
          |>.toPreservesVEnvs

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
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkData_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms addDecl.inductDecl_WF_of_split_primitive_transactions

/--
info: 'Lean4Lean.addDecl.inductDecl_WF_of_split_primitive_transactions_default' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkData_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms addDecl.inductDecl_WF_of_split_primitive_transactions_default

/-- The supported declaration class excludes unsafe inductive blocks while
leaving every other declaration form unchanged.  This matches the Theory
coverage contract: translated histories deliberately maintain the invariant
that every inductive metadata record is safe. -/
def DeclarationInductiveSafe : Declaration → Prop
  | .inductDecl _ _ _ isUnsafe => isUnsafe = false
  | _ => True

set_option warn.sorry false in
/-- Successful checked addition preserves well-formedness and extends every safety-indexed
abstract environment for the supported declaration class. The only declaration form still
outstanding is safe inductives, which need a constructive `AddInduct` model. -/
theorem addDecl.WF {env : Environment} {ves : VEnvs} (wf : ves.WF env)
    (decl : Declaration) (_inductiveSafe : DeclarationInductiveSafe decl) :
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
