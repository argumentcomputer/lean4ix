import Lean4Lean.Experimental.SExprParamsD2
import Lean4Lean.Experimental.SExprClassified

/-!
# L4L-16D2: registered equations for the mutual Tree block

This module discharges the five opened-body leaves isolated by
`ParamsD2.D2RegisteredBodyStep`.  The full lambda towers are closed by
`SExpr.closeTel_strong`; this file is responsible only for strongly typing
the canonical generated redexes and packaging their local actions.
-/

namespace Lean4Lean
namespace SExpr
namespace ParamsD2

open InductiveFixtures InductiveReplayFixtures VInductDecl
open MutualInductiveFixtures MutualInductiveReplayFixtures

/-- The parameter, two motives, and five minors shared by both mutual
recursors and by all five generated rules. -/
def d2CommonBindersV : List VExpr :=
  TreeGen.paramsTel ++ TreeGen.motiveTypes ++ TreeGen.minorTypes

def d2CommonBinders (ls : List (@SLevel (d2Params univs))) :
    List (@SExpr (d2Params univs)) :=
  letI : Params := d2Params univs
  d2CommonBindersV.map (SExpr.mkInst ls)

/-- The constructor-field suffix of one generated rule telescope. -/
def d2FieldBindersV (constructor : NormalizedBlockCtor) : List VExpr :=
  VExpr.liftTelN (TreeGen.familyCount + TreeGen.minorCount)
    (constructor.ctor.fieldsR treeDecl.uvars treeDecl.nparams
      TreeGen.elimination) 0

def d2FieldBinders (ls : List (@SLevel (d2Params univs)))
    (constructor : NormalizedBlockCtor) : List (@SExpr (d2Params univs)) :=
  letI : Params := d2Params univs
  (d2FieldBindersV constructor).map (SExpr.mkInst ls)

theorem d2RuleBinders_eq (ls : List (@SLevel (d2Params univs)))
    (constructor : NormalizedBlockCtor) :
    (TreeGen.ruleBinders constructor).map
        (@SExpr.mkInst (d2Params univs) ls) =
      d2CommonBinders ls ++ d2FieldBinders ls constructor := by
  letI : Params := d2Params univs
  simp only [VInductDecl.BlockGenerationChecked.ruleBinders,
    d2CommonBinders, d2CommonBindersV, d2FieldBinders, d2FieldBindersV,
    List.map_append, List.append_assoc]

theorem d2CommonBindersV_length : d2CommonBindersV.length = 8 := by
  native_decide

theorem d2CommonBinders_head (univs : Nat)
    (u l : @SLevel (d2Params univs)) :
    (d2CommonBinders [u, l]).head? =
      some (@SExpr.sort (d2Params univs)
        (@SLevel.succ (d2Params univs) l)) := by
  rfl

/-- The seven common binders following the type parameter. -/
def d2CommonAfterAlpha (univs : Nat)
    (u l : @SLevel (d2Params univs)) : List (@SExpr (d2Params univs)) :=
  (d2CommonBinders [u, l]).tail

theorem d2CommonBinders_cons (univs : Nat)
    (u l : @SLevel (d2Params univs)) :
    d2CommonBinders [u, l] =
      @SExpr.sort (d2Params univs) (@SLevel.succ (d2Params univs) l) ::
        d2CommonAfterAlpha univs u l := by
  rfl

theorem d2CommonAfterAlpha_length (univs : Nat)
    (u l : @SLevel (d2Params univs)) :
    (d2CommonAfterAlpha univs u l).length = 7 := by
  have h := congrArg List.length (d2CommonBinders_cons univs u l)
  have hc : (d2CommonBinders [u, l]).length = 8 := by
    simpa [d2CommonBinders] using d2CommonBindersV_length
  rw [hc] at h
  simp only [List.length_cons] at h
  omega

/-- The first motive, in the context containing only the parameter. -/
def d2TreeMotiveType (univs : Nat)
    (u l : @SLevel (d2Params univs)) : @SExpr (d2Params univs) :=
  @SExpr.forallE (d2Params univs)
    (@SExpr.app (d2Params univs)
      (@SExpr.const (d2Params univs) ``Tree [l])
      (@SExpr.bvar (d2Params univs) 0))
    (@SExpr.sort (d2Params univs) u)

/-- The six common binders following the `Tree` motive. -/
def d2CommonAfterTreeMotive (univs : Nat)
    (u l : @SLevel (d2Params univs)) : List (@SExpr (d2Params univs)) :=
  (d2CommonAfterAlpha univs u l).tail

theorem d2CommonAfterAlpha_cons (univs : Nat)
    (u l : @SLevel (d2Params univs)) :
    d2CommonAfterAlpha univs u l =
      d2TreeMotiveType univs u l ::
        d2CommonAfterTreeMotive univs u l := by
  rfl

theorem d2CommonAfterTreeMotive_length (univs : Nat)
    (u l : @SLevel (d2Params univs)) :
    (d2CommonAfterTreeMotive univs u l).length = 6 := by
  have h := congrArg List.length (d2CommonAfterAlpha_cons univs u l)
  rw [d2CommonAfterAlpha_length] at h
  simp only [List.length_cons] at h
  omega

/-- The second motive, in the context containing the first motive and the
parameter. -/
def d2TreeListMotiveType (univs : Nat)
    (u l : @SLevel (d2Params univs)) : @SExpr (d2Params univs) :=
  @SExpr.forallE (d2Params univs)
    (@SExpr.app (d2Params univs)
      (@SExpr.const (d2Params univs) ``TreeList [l])
      (@SExpr.bvar (d2Params univs) 1))
    (@SExpr.sort (d2Params univs) u)

/-- The five minor premises following both motives. -/
def d2CommonMinors (univs : Nat)
    (u l : @SLevel (d2Params univs)) : List (@SExpr (d2Params univs)) :=
  (d2CommonAfterTreeMotive univs u l).tail

theorem d2CommonAfterTreeMotive_cons (univs : Nat)
    (u l : @SLevel (d2Params univs)) :
    d2CommonAfterTreeMotive univs u l =
      d2TreeListMotiveType univs u l :: d2CommonMinors univs u l := by
  rfl

theorem d2CommonMinors_length (univs : Nat)
    (u l : @SLevel (d2Params univs)) :
    (d2CommonMinors univs u l).length = 5 := by
  have h := congrArg List.length
    (d2CommonAfterTreeMotive_cons univs u l)
  rw [d2CommonAfterTreeMotive_length] at h
  simp only [List.length_cons] at h
  omega

/-- The final major-argument tail of `Tree.rec`, after the eight common
binders have been introduced. -/
def d2TreeRecTailV : VExpr :=
  VExpr.forallE
    ((VExpr.const ``Tree [.param 1]).app (VExpr.bvar 7))
    ((VExpr.bvar 7).app (VExpr.bvar 0))

/-- The final major-argument tail of `TreeList.rec`. -/
def d2TreeListRecTailV : VExpr :=
  VExpr.forallE
    ((VExpr.const ``TreeList [.param 1]).app (VExpr.bvar 7))
    ((VExpr.bvar 6).app (VExpr.bvar 0))

theorem d2TreeRecTypeV_eq :
    TreeGen.recursors[0].type =
      VExpr.forallN d2CommonBindersV d2TreeRecTailV := by
  native_decide

theorem d2TreeListRecTypeV_eq :
    TreeGen.recursors[1].type =
      VExpr.forallN d2CommonBindersV d2TreeListRecTailV := by
  native_decide

/-- Split an instantiated generated-rule type at the eight binders shared
with its recursor.  This is the exact head shape consumed by the generic
`spinePrefixForallN` replay. -/
theorem d2RuleTypePrefixV_eq (i : Nat)
    (constructor : NormalizedBlockCtor) (vls : List VLevel) :
    (TreeGen.rule i constructor).type.instL vls =
      VExpr.forallN (d2CommonBindersV.map (VExpr.instL vls))
        ((VExpr.forallN (d2FieldBindersV constructor)
          (d2RuleResult constructor)).instL vls) := by
  rw [TreeGen.rule_type, VInductDecl.BlockGenerationChecked.ruleBinders,
    VExpr.forallN_append, VExpr.instL_forallN]
  rfl

/-- Replay the eight common arguments of a Tree/TreeList recursor spine as
the common prefix of any generated rule.  The old recursor tail is replaced
by the rule's constructor-field telescope; no field typing or parameter
equality is used yet. -/
theorem d2RuleCommonRawSpine (univs : Nat)
    (u l : @SLevel (d2Params univs)) (i : Nat)
    (constructor : NormalizedBlockCtor)
    {Gamma : List (@SExpr (d2Params univs))}
    {Head Res majorTerm : @SExpr (d2Params univs)}
    {recArgs : List (@SExpr (d2Params univs))} {oldTail : VExpr}
    (hGamma : D2ContextValid univs Gamma)
    (hHead : @TypesDefEq (d2Params univs) Gamma
      (@SExpr.mkInst (d2Params univs) [u, l]
        (VExpr.forallN d2CommonBindersV oldTail)) Head)
    (hspine : @SpineWF (d2Params univs) Gamma Head
      (recArgs.reverse ++ [majorTerm]) Res)
    (hlen : recArgs.length = 8) :
    letI : Params := d2Params univs
    SpineWF Gamma
      (SExpr.mkInst [u, l] (TreeGen.rule i constructor).type)
      recArgs.reverse
      (SExpr.mk
        (((VExpr.forallN (d2FieldBindersV constructor)
          (d2RuleResult constructor)).instL [u.reify, l.reify]).instRev
            (recArgs.reverse.map SExpr.reify))) := by
  letI : Params := d2Params univs
  let vls : List VLevel := [u.reify, l.reify]
  have hvls : ∀ level ∈ vls, level.WF univs := by
    intro level hlevel
    rcases List.mem_cons.mp hlevel with rfl | hlevel
    · exact SLevel.reify_wf u
    · have hlevel' := List.mem_singleton.mp hlevel
      subst level
      exact SLevel.reify_wf l
  have holdShape : SExpr.mk
      (VExpr.forallN (d2CommonBindersV.map (VExpr.instL vls))
        (oldTail.instL vls)) =
      SExpr.mkInst [u, l] (VExpr.forallN d2CommonBindersV oldTail) := by
    calc
      _ = SExpr.mk ((VExpr.forallN d2CommonBindersV oldTail).instL vls) := by
        rw [VExpr.instL_forallN]
      _ = _ := by
        simpa only [vls, List.map_cons, List.map_nil] using
          (@SExpr.mk_instL_map_reify (d2Params univs)
            (VExpr.forallN d2CommonBindersV oldTail) [u, l])
  have hlevel : (VExpr.forallN
      (d2CommonBindersV.map (VExpr.instL vls))
      (oldTail.instL vls)).LevelWF univs := by
    have H : ((VExpr.forallN d2CommonBindersV oldTail).instL vls).LevelWF
        univs := VExpr.LevelWF.instL hvls
    rwa [VExpr.instL_forallN] at H
  have hprefix := spinePrefixForallN (d2Replay univs) hGamma
    (n := 8)
    (binders := d2CommonBindersV.map (VExpr.instL vls))
    (oldResult := oldTail.instL vls)
    (newResult := (VExpr.forallN (d2FieldBindersV constructor)
      (d2RuleResult constructor)).instL vls)
    (args := recArgs.reverse) (suffix := [majorTerm])
    (by simpa using d2CommonBindersV_length)
    (by simp [hlen]) hlevel (holdShape ▸ hHead) hspine
  have hruleShape : SExpr.mk
      (VExpr.forallN (d2CommonBindersV.map (VExpr.instL vls))
        ((VExpr.forallN (d2FieldBindersV constructor)
          (d2RuleResult constructor)).instL vls)) =
      SExpr.mkInst [u, l] (TreeGen.rule i constructor).type := by
    calc
      _ = SExpr.mk ((TreeGen.rule i constructor).type.instL vls) :=
        congrArg SExpr.mk (d2RuleTypePrefixV_eq i constructor vls).symm
      _ = _ := by
        simpa only [vls, List.map_cons, List.map_nil] using
          (@SExpr.mk_instL_map_reify (d2Params univs)
            (TreeGen.rule i constructor).type [u, l])
  rw [hruleShape] at hprefix
  simpa only [vls] using hprefix

/-- Concrete `Tree.rec` head specialization of `d2RuleCommonRawSpine`. -/
theorem d2TreeRuleCommonRawSpine (univs : Nat)
    (u l : @SLevel (d2Params univs)) (i : Nat)
    (constructor : NormalizedBlockCtor)
    {Gamma : List (@SExpr (d2Params univs))}
    {A majorTerm : @SExpr (d2Params univs)}
    {ctorLs : List (@SLevel (d2Params univs))}
    {recArgs ctorArgs : List (@SExpr (d2Params univs))}
    (hGamma : D2ContextValid univs Gamma)
    (typing : @Pattern.IotaTyping (d2Params univs) Gamma ``Tree.rec
      constructor.ctor.raw.name [u, l] ctorLs recArgs ctorArgs majorTerm A)
    (hlen : recArgs.length = 8) :
    letI : Params := d2Params univs
    SpineWF Gamma
      (SExpr.mkInst [u, l] (TreeGen.rule i constructor).type)
      recArgs.reverse
      (SExpr.mk
        (((VExpr.forallN (d2FieldBindersV constructor)
          (d2RuleResult constructor)).instL [u.reify, l.reify]).instRev
            (recArgs.reverse.map SExpr.reify))) := by
  letI : Params := d2Params univs
  have hrec : IsDefEq Gamma (.const ``Tree.rec [u, l])
      (.const ``Tree.rec [u, l])
      (SExpr.mkInst [u, l] TreeGen.recursors[0].type) :=
    .const d2Env_treeRec_lookup rfl
  rw [d2TreeRecTypeV_eq] at hrec
  have hHead := typeUniq (d2Replay univs) hGamma hrec typing.recHead
  exact d2RuleCommonRawSpine univs u l i constructor hGamma hHead
    typing.recSpine hlen

/-- Concrete `TreeList.rec` head specialization of the same common-prefix
replay. -/
theorem d2TreeListRuleCommonRawSpine (univs : Nat)
    (u l : @SLevel (d2Params univs)) (i : Nat)
    (constructor : NormalizedBlockCtor)
    {Gamma : List (@SExpr (d2Params univs))}
    {A majorTerm : @SExpr (d2Params univs)}
    {ctorLs : List (@SLevel (d2Params univs))}
    {recArgs ctorArgs : List (@SExpr (d2Params univs))}
    (hGamma : D2ContextValid univs Gamma)
    (typing : @Pattern.IotaTyping (d2Params univs) Gamma ``TreeList.rec
      constructor.ctor.raw.name [u, l] ctorLs recArgs ctorArgs majorTerm A)
    (hlen : recArgs.length = 8) :
    letI : Params := d2Params univs
    SpineWF Gamma
      (SExpr.mkInst [u, l] (TreeGen.rule i constructor).type)
      recArgs.reverse
      (SExpr.mk
        (((VExpr.forallN (d2FieldBindersV constructor)
          (d2RuleResult constructor)).instL [u.reify, l.reify]).instRev
            (recArgs.reverse.map SExpr.reify))) := by
  letI : Params := d2Params univs
  have hrec : IsDefEq Gamma (.const ``TreeList.rec [u, l])
      (.const ``TreeList.rec [u, l])
      (SExpr.mkInst [u, l] TreeGen.recursors[1].type) :=
    .const d2Env_treeListRec_lookup rfl
  rw [d2TreeListRecTypeV_eq] at hrec
  have hHead := typeUniq (d2Replay univs) hGamma hrec typing.recHead
  exact d2RuleCommonRawSpine univs u l i constructor hGamma hHead
    typing.recSpine hlen

/-- The complete generated-rule telescope recovered from the registered
right tower's declared type. -/
theorem d2RuleTelescopeStrong (univs : Nat)
    {i : Nat} {constructor : NormalizedBlockCtor}
    {ls : List (@SLevel (d2Params univs))}
    {Gamma : List (@SExpr (d2Params univs))}
    (hRhs : @IsDefEqStrong (d2Params univs) Gamma
      (@SExpr.mkInst (d2Params univs) ls (TreeGen.rule i constructor).rhs)
      (@SExpr.mkInst (d2Params univs) ls (TreeGen.rule i constructor).rhs)
      (@SExpr.mkInst (d2Params univs) ls (TreeGen.rule i constructor).type)) :
    letI : Params := d2Params univs
    StrongTelescope Gamma
      ((TreeGen.ruleBinders constructor).map (SExpr.mkInst ls)) := by
  letI : Params := d2Params univs
  let As := (TreeGen.ruleBinders constructor).map (SExpr.mkInst ls)
  let B := SExpr.mkInst ls (d2RuleResult constructor)
  have htype : SExpr.mkInst ls (TreeGen.rule i constructor).type =
      As.foldr .forallE B := by
    rw [TreeGen.rule_type, SExpr.mkInst_forallN]
    rfl
  exact StrongTelescope.of_forall (htype ▸ hRhs.isType)

/-- The rule's own type validity exposes a valid common telescope. -/
theorem d2CommonTelescopeStrong (univs : Nat)
    {i : Nat} {constructor : NormalizedBlockCtor}
    {ls : List (@SLevel (d2Params univs))}
    {Gamma : List (@SExpr (d2Params univs))}
    (hRhs : @IsDefEqStrong (d2Params univs) Gamma
      (@SExpr.mkInst (d2Params univs) ls (TreeGen.rule i constructor).rhs)
      (@SExpr.mkInst (d2Params univs) ls (TreeGen.rule i constructor).rhs)
      (@SExpr.mkInst (d2Params univs) ls (TreeGen.rule i constructor).type)) :
    letI : Params := d2Params univs
    StrongTelescope Gamma (d2CommonBinders ls) := by
  letI : Params := d2Params univs
  have hAll := d2RuleTelescopeStrong univs hRhs
  change StrongTelescope Gamma
    ((TreeGen.ruleBinders constructor).map (SExpr.mkInst ls)) at hAll
  rw [d2RuleBinders_eq] at hAll
  exact hAll.prefix

/-- The constructor-field suffix is valid after opening the shared common
prefix. -/
theorem d2FieldTelescopeStrong (univs : Nat)
    {i : Nat} {constructor : NormalizedBlockCtor}
    {ls : List (@SLevel (d2Params univs))}
    {Gamma : List (@SExpr (d2Params univs))}
    (hRhs : @IsDefEqStrong (d2Params univs) Gamma
      (@SExpr.mkInst (d2Params univs) ls (TreeGen.rule i constructor).rhs)
      (@SExpr.mkInst (d2Params univs) ls (TreeGen.rule i constructor).rhs)
      (@SExpr.mkInst (d2Params univs) ls (TreeGen.rule i constructor).type)) :
    letI : Params := d2Params univs
    StrongTelescope ((d2CommonBinders ls).reverse ++ Gamma)
      (d2FieldBinders ls constructor) := by
  letI : Params := d2Params univs
  have hAll := d2RuleTelescopeStrong univs hRhs
  change StrongTelescope Gamma
    ((TreeGen.ruleBinders constructor).map (SExpr.mkInst ls)) at hAll
  rw [d2RuleBinders_eq] at hAll
  exact hAll.suffix

/-- The parameter variable in the fully opened common telescope. -/
theorem d2CommonAlphaStrong (univs : Nat)
    (u l : @SLevel (d2Params univs))
    {Gamma : List (@SExpr (d2Params univs))}
    (h : @StrongTelescope (d2Params univs) Gamma
      (d2CommonBinders [u, l])) :
    @IsDefEqStrong (d2Params univs)
      ((d2CommonBinders [u, l]).reverse ++ Gamma)
      (@SExpr.bvar (d2Params univs) 7)
      (@SExpr.bvar (d2Params univs) 7)
      (@SExpr.sort (d2Params univs)
        (@SLevel.succ (d2Params univs) l)) := by
  letI : Params := d2Params univs
  rw [d2CommonBinders_cons univs u l] at h ⊢
  have hb := h.head_bvar (fun W H => d2StrongWeak univs W H)
  simpa [d2CommonAfterAlpha_length, SExpr.lift] using hb

/-- The `Tree` motive variable in the fully opened common telescope. -/
theorem d2CommonTreeMotiveStrong (univs : Nat)
    (u l : @SLevel (d2Params univs))
    {Gamma : List (@SExpr (d2Params univs))}
    (h : @StrongTelescope (d2Params univs) Gamma
      (d2CommonBinders [u, l])) :
    @IsDefEqStrong (d2Params univs)
      ((d2CommonBinders [u, l]).reverse ++ Gamma)
      (@SExpr.bvar (d2Params univs) 6)
      (@SExpr.bvar (d2Params univs) 6)
      (@SExpr.forallE (d2Params univs)
        (@SExpr.app (d2Params univs)
          (@SExpr.const (d2Params univs) ``Tree [l])
          (@SExpr.bvar (d2Params univs) 7))
        (@SExpr.sort (d2Params univs) u)) := by
  letI : Params := d2Params univs
  rw [d2CommonBinders_cons univs u l,
    d2CommonAfterAlpha_cons univs u l] at h ⊢
  cases h with
  | cons _ h =>
    have hb := h.head_bvar (fun W H => d2StrongWeak univs W H)
    simpa [d2TreeMotiveType, d2CommonAfterTreeMotive_length,
      SExpr.lift, List.append_assoc] using hb

/-- The `TreeList` motive variable in the fully opened common telescope. -/
theorem d2CommonTreeListMotiveStrong (univs : Nat)
    (u l : @SLevel (d2Params univs))
    {Gamma : List (@SExpr (d2Params univs))}
    (h : @StrongTelescope (d2Params univs) Gamma
      (d2CommonBinders [u, l])) :
    @IsDefEqStrong (d2Params univs)
      ((d2CommonBinders [u, l]).reverse ++ Gamma)
      (@SExpr.bvar (d2Params univs) 5)
      (@SExpr.bvar (d2Params univs) 5)
      (@SExpr.forallE (d2Params univs)
        (@SExpr.app (d2Params univs)
          (@SExpr.const (d2Params univs) ``TreeList [l])
          (@SExpr.bvar (d2Params univs) 7))
        (@SExpr.sort (d2Params univs) u)) := by
  letI : Params := d2Params univs
  rw [d2CommonBinders_cons univs u l,
    d2CommonAfterAlpha_cons univs u l,
    d2CommonAfterTreeMotive_cons univs u l] at h ⊢
  cases h with
  | cons _ h =>
    cases h with
    | cons _ h =>
      have hb := h.head_bvar (fun W H => d2StrongWeak univs W H)
      simpa [d2TreeListMotiveType, d2CommonMinors_length,
        SExpr.lift, List.append_assoc] using hb

/-- The `Tree.rec` head applied to the eight canonical common variables,
leaving only its major argument. -/
theorem d2TreeRecCommonStrong (univs : Nat)
    (u l : @SLevel (d2Params univs))
    {Gamma : List (@SExpr (d2Params univs))}
    (hCommon : @StrongTelescope (d2Params univs) Gamma
      (d2CommonBinders [u, l])) :
    letI : Params := d2Params univs
    IsDefEqStrong ((d2CommonBinders [u, l]).reverse ++ Gamma)
      (applyTelVars (d2CommonBinders [u, l])
        (.const ``Tree.rec [u, l]))
      (applyTelVars (d2CommonBinders [u, l])
        (.const ``Tree.rec [u, l]))
      (SExpr.mkInst [u, l] d2TreeRecTailV) := by
  letI : Params := d2Params univs
  let Delta := (d2CommonBinders [u, l]).reverse ++ Gamma
  have hAlpha := d2CommonAlphaStrong univs u l hCommon
  have hMotive := d2CommonTreeMotiveStrong univs u l hCommon
  have hTree := d2TreeAppStrong univs l hAlpha
  let W : Ctx.Lift' (.skip .refl) Delta
      ((SExpr.const ``Tree [l]).app (.bvar 7) :: Delta) := .skip .refl
  have hTreeW := d2StrongWeak univs W hTree
  have hMotiveW := d2StrongWeak univs W hMotive
  have hMajor : IsDefEqStrong
      ((SExpr.const ``Tree [l]).app (.bvar 7) :: Delta)
      (.bvar 0) (.bvar 0)
      ((SExpr.const ``Tree [l]).app (.bvar 8)) := by
    exact .bvar .zero hTreeW
  have hResult : IsDefEqStrong
      ((SExpr.const ``Tree [l]).app (.bvar 7) :: Delta)
      ((SExpr.bvar 7).app (.bvar 0)) ((SExpr.bvar 7).app (.bvar 0))
      (.sort u) := by
    exact .appDF hTreeW (.sort) hMotiveW hMajor (.sort)
  have hTail : IsDefEqStrong Delta
      (SExpr.mkInst [u, l] d2TreeRecTailV)
      (SExpr.mkInst [u, l] d2TreeRecTailV)
      (.sort (.imax l.succ u)) := by
    exact .forallEDF hTree hResult hResult
  obtain ⟨q, hTy0⟩ := hCommon.close ⟨_, hTail⟩
  have hTy : IsDefEqStrong Gamma
      (SExpr.mkInst [u, l] TreeGen.recursors[0].type)
      (SExpr.mkInst [u, l] TreeGen.recursors[0].type)
      (.sort q) := by
    rw [d2TreeRecTypeV_eq, SExpr.mkInst_forallN]
    simpa only [d2CommonBinders] using hTy0
  have hConst := d2ConstStrong univs d2Env_treeRec_lookup rfl hTy
  exact applyTelVars_strong (fun W H => d2StrongWeak univs W H) hConst

/-- The `TreeList.rec` head applied to the same common variables. -/
theorem d2TreeListRecCommonStrong (univs : Nat)
    (u l : @SLevel (d2Params univs))
    {Gamma : List (@SExpr (d2Params univs))}
    (hCommon : @StrongTelescope (d2Params univs) Gamma
      (d2CommonBinders [u, l])) :
    letI : Params := d2Params univs
    IsDefEqStrong ((d2CommonBinders [u, l]).reverse ++ Gamma)
      (applyTelVars (d2CommonBinders [u, l])
        (.const ``TreeList.rec [u, l]))
      (applyTelVars (d2CommonBinders [u, l])
        (.const ``TreeList.rec [u, l]))
      (SExpr.mkInst [u, l] d2TreeListRecTailV) := by
  letI : Params := d2Params univs
  let Delta := (d2CommonBinders [u, l]).reverse ++ Gamma
  have hAlpha := d2CommonAlphaStrong univs u l hCommon
  have hMotive := d2CommonTreeListMotiveStrong univs u l hCommon
  have hTreeList := d2TreeListAppStrong univs l hAlpha
  let W : Ctx.Lift' (.skip .refl) Delta
      ((SExpr.const ``TreeList [l]).app (.bvar 7) :: Delta) := .skip .refl
  have hTreeListW := d2StrongWeak univs W hTreeList
  have hMotiveW := d2StrongWeak univs W hMotive
  have hMajor : IsDefEqStrong
      ((SExpr.const ``TreeList [l]).app (.bvar 7) :: Delta)
      (.bvar 0) (.bvar 0)
      ((SExpr.const ``TreeList [l]).app (.bvar 8)) := by
    exact .bvar .zero hTreeListW
  have hResult : IsDefEqStrong
      ((SExpr.const ``TreeList [l]).app (.bvar 7) :: Delta)
      ((SExpr.bvar 6).app (.bvar 0)) ((SExpr.bvar 6).app (.bvar 0))
      (.sort u) := by
    exact .appDF hTreeListW (.sort) hMotiveW hMajor (.sort)
  have hTail : IsDefEqStrong Delta
      (SExpr.mkInst [u, l] d2TreeListRecTailV)
      (SExpr.mkInst [u, l] d2TreeListRecTailV)
      (.sort (.imax l.succ u)) := by
    exact .forallEDF hTreeList hResult hResult
  obtain ⟨q, hTy0⟩ := hCommon.close ⟨_, hTail⟩
  have hTy : IsDefEqStrong Gamma
      (SExpr.mkInst [u, l] TreeGen.recursors[1].type)
      (SExpr.mkInst [u, l] TreeGen.recursors[1].type)
      (.sort q) := by
    rw [d2TreeListRecTypeV_eq, SExpr.mkInst_forallN]
    simpa only [d2CommonBinders] using hTy0
  have hConst := d2ConstStrong univs d2Env_treeListRec_lookup rfl hTy
  exact applyTelVars_strong (fun W H => d2StrongWeak univs W H) hConst

/-- Apply a strongly typed `Tree.rec` tail to one typed major premise. -/
theorem d2TreeRecApplyStrong (univs : Nat)
    (u l : @SLevel (d2Params univs))
    {Gamma : List (@SExpr (d2Params univs))}
    {alpha motive rec major : @SExpr (d2Params univs)}
    (hAlpha : @IsDefEqStrong (d2Params univs) Gamma alpha alpha
      (@SExpr.sort (d2Params univs) (@SLevel.succ (d2Params univs) l)))
    (hMotive : @IsDefEqStrong (d2Params univs) Gamma motive motive
      (@SExpr.forallE (d2Params univs)
        (@SExpr.app (d2Params univs)
          (@SExpr.const (d2Params univs) ``Tree [l]) alpha)
        (@SExpr.sort (d2Params univs) u)))
    (hRec : @IsDefEqStrong (d2Params univs) Gamma rec rec
      (@SExpr.forallE (d2Params univs)
        (@SExpr.app (d2Params univs)
          (@SExpr.const (d2Params univs) ``Tree [l]) alpha)
        (@SExpr.app (d2Params univs)
          (@SExpr.lift (d2Params univs) motive)
          (@SExpr.bvar (d2Params univs) 0))))
    (hMajor : @IsDefEqStrong (d2Params univs) Gamma major major
      (@SExpr.app (d2Params univs)
        (@SExpr.const (d2Params univs) ``Tree [l]) alpha)) :
    @IsDefEqStrong (d2Params univs) Gamma
      (@SExpr.app (d2Params univs) rec major)
      (@SExpr.app (d2Params univs) rec major)
      (@SExpr.app (d2Params univs) motive major) := by
  letI : Params := d2Params univs
  have hTree := d2TreeAppStrong univs l hAlpha
  let W : Ctx.Lift' (.skip .refl) Gamma
      ((SExpr.const ``Tree [l]).app alpha :: Gamma) := .skip .refl
  have hTreeW := d2StrongWeak univs W hTree
  have hMotiveW := d2StrongWeak univs W hMotive
  have hMajorVar : IsDefEqStrong
      ((SExpr.const ``Tree [l]).app alpha :: Gamma)
      (.bvar 0) (.bvar 0)
      ((SExpr.const ``Tree [l]).app alpha.lift) :=
    .bvar .zero hTreeW
  have hCod : IsDefEqStrong
      ((SExpr.const ``Tree [l]).app alpha :: Gamma)
      (motive.lift.app (.bvar 0)) (motive.lift.app (.bvar 0))
      (.sort u) :=
    .appDF hTreeW .sort hMotiveW hMajorVar .sort
  have hResult : IsDefEqStrong Gamma
      (motive.app major) (motive.app major) (.sort u) :=
    .appDF hTree .sort hMotive hMajor .sort
  have hResultExact : IsDefEqStrong Gamma
      ((motive.lift.app (.bvar 0)).inst major)
      ((motive.lift.app (.bvar 0)).inst major) (.sort u) := by
    simpa [SExpr.inst, SExpr.subst, Subst.one, Subst.cons, Subst.lift,
      SExpr.lift, lift_subst_cons] using hResult
  simpa [SExpr.inst, SExpr.subst, Subst.one, Subst.cons, Subst.lift,
    SExpr.lift, lift_subst_cons] using
    IsDefEqStrong.appDF hTree hCod hRec hMajor hResultExact

/-- Apply the analogous `TreeList.rec` tail to one typed major premise. -/
theorem d2TreeListRecApplyStrong (univs : Nat)
    (u l : @SLevel (d2Params univs))
    {Gamma : List (@SExpr (d2Params univs))}
    {alpha motive rec major : @SExpr (d2Params univs)}
    (hAlpha : @IsDefEqStrong (d2Params univs) Gamma alpha alpha
      (@SExpr.sort (d2Params univs) (@SLevel.succ (d2Params univs) l)))
    (hMotive : @IsDefEqStrong (d2Params univs) Gamma motive motive
      (@SExpr.forallE (d2Params univs)
        (@SExpr.app (d2Params univs)
          (@SExpr.const (d2Params univs) ``TreeList [l]) alpha)
        (@SExpr.sort (d2Params univs) u)))
    (hRec : @IsDefEqStrong (d2Params univs) Gamma rec rec
      (@SExpr.forallE (d2Params univs)
        (@SExpr.app (d2Params univs)
          (@SExpr.const (d2Params univs) ``TreeList [l]) alpha)
        (@SExpr.app (d2Params univs)
          (@SExpr.lift (d2Params univs) motive)
          (@SExpr.bvar (d2Params univs) 0))))
    (hMajor : @IsDefEqStrong (d2Params univs) Gamma major major
      (@SExpr.app (d2Params univs)
        (@SExpr.const (d2Params univs) ``TreeList [l]) alpha)) :
    @IsDefEqStrong (d2Params univs) Gamma
      (@SExpr.app (d2Params univs) rec major)
      (@SExpr.app (d2Params univs) rec major)
      (@SExpr.app (d2Params univs) motive major) := by
  letI : Params := d2Params univs
  have hTreeList := d2TreeListAppStrong univs l hAlpha
  let W : Ctx.Lift' (.skip .refl) Gamma
      ((SExpr.const ``TreeList [l]).app alpha :: Gamma) := .skip .refl
  have hTreeListW := d2StrongWeak univs W hTreeList
  have hMotiveW := d2StrongWeak univs W hMotive
  have hMajorVar : IsDefEqStrong
      ((SExpr.const ``TreeList [l]).app alpha :: Gamma)
      (.bvar 0) (.bvar 0)
      ((SExpr.const ``TreeList [l]).app alpha.lift) :=
    .bvar .zero hTreeListW
  have hCod : IsDefEqStrong
      ((SExpr.const ``TreeList [l]).app alpha :: Gamma)
      (motive.lift.app (.bvar 0)) (motive.lift.app (.bvar 0))
      (.sort u) :=
    .appDF hTreeListW .sort hMotiveW hMajorVar .sort
  have hResult : IsDefEqStrong Gamma
      (motive.app major) (motive.app major) (.sort u) :=
    .appDF hTreeList .sort hMotive hMajor .sort
  have hResultExact : IsDefEqStrong Gamma
      ((motive.lift.app (.bvar 0)).inst major)
      ((motive.lift.app (.bvar 0)).inst major) (.sort u) := by
    simpa [SExpr.inst, SExpr.subst, Subst.one, Subst.cons, Subst.lift,
      SExpr.lift, lift_subst_cons] using hResult
  simpa [SExpr.inst, SExpr.subst, Subst.one, Subst.cons, Subst.lift,
    SExpr.lift, lift_subst_cons] using
    IsDefEqStrong.appDF hTreeList hCod hRec hMajor hResultExact

/-- A constructor constant is strongly typed directly from its already
verified D2 constructor bundle. -/
theorem d2ConstructorConstStrong (univs : Nat)
    {c : Name} {ci : VConstant}
    {ls : List (@SLevel (d2Params univs))}
    {Gamma : List (@SExpr (d2Params univs))}
    (hreg : d2Env.constants c = some ci) (hlen : ls.length = ci.uvars)
    (cl : @CtorBundle.IsCtor (d2Params univs) c) :
    @IsDefEqStrong (d2Params univs) Gamma
      (@SExpr.const (d2Params univs) c ls)
      (@SExpr.const (d2Params univs) c ls)
      (@SExpr.mkInst (d2Params univs) ls ci.type) := by
  letI : Params := d2Params univs
  exact d2ConstStrong univs hreg hlen
    (d2Ctor univs (Gamma := Gamma) hreg hlen cl).2.hasType.1

/-- Strong typing of a fully applied `Tree.leaf` major premise. -/
theorem d2TreeLeafMajorStrong (univs : Nat)
    (l : @SLevel (d2Params univs))
    {Gamma : List (@SExpr (d2Params univs))}
    {alpha x : @SExpr (d2Params univs)}
    (hAlpha : @IsDefEqStrong (d2Params univs) Gamma alpha alpha
      (@SExpr.sort (d2Params univs) (@SLevel.succ (d2Params univs) l)))
    (hx : @IsDefEqStrong (d2Params univs) Gamma x x alpha) :
    @IsDefEqStrong (d2Params univs) Gamma
      (@SExpr.app (d2Params univs)
        (@SExpr.app (d2Params univs)
          (@SExpr.const (d2Params univs) ``Tree.leaf [l]) alpha) x)
      (@SExpr.app (d2Params univs)
        (@SExpr.app (d2Params univs)
          (@SExpr.const (d2Params univs) ``Tree.leaf [l]) alpha) x)
      (@SExpr.app (d2Params univs)
        (@SExpr.const (d2Params univs) ``Tree [l]) alpha) := by
  letI : Params := d2Params univs
  let cl : @CtorBundle.IsCtor (d2Params univs) ``Tree.leaf := by
    refine ⟨.ctor 2, ?_, by simp⟩
    change d2Classify ``Tree.leaf = some (.ctor 2)
    simp [d2Classify]
  have hConst := d2ConstructorConstStrong univs
    d2Env_treeLeaf_lookup rfl cl (ls := [l]) (Gamma := Gamma)
  change IsDefEqStrong Gamma (.const ``Tree.leaf [l])
    (.const ``Tree.leaf [l])
    (.forallE (.sort l.succ)
      (.forallE (.bvar 0) ((SExpr.const ``Tree [l]).app (.bvar 1)))) at hConst
  have hAlpha0 := d2AlphaStrong univs Gamma l
  have hTree1 : IsDefEqStrong
      (.bvar 0 :: .sort l.succ :: Gamma)
      ((SExpr.const ``Tree [l]).app (.bvar 1))
      ((SExpr.const ``Tree [l]).app (.bvar 1)) (.sort l.succ) :=
    d2TreeAppStrong univs l
      (d2BvarStrong univs (.succ .zero) (by exact IsDefEqStrong.sort))
  have hCod : IsDefEqStrong (.sort l.succ :: Gamma)
      (.forallE (.bvar 0) ((SExpr.const ``Tree [l]).app (.bvar 1)))
      (.forallE (.bvar 0) ((SExpr.const ``Tree [l]).app (.bvar 1)))
      (.sort (.imax l.succ l.succ)) :=
    .forallEDF hAlpha0 hTree1 hTree1
  let W : Ctx.Lift' (.skip .refl) Gamma (alpha :: Gamma) := .skip .refl
  have hTreeArg := d2TreeAppStrong univs l (d2StrongWeak univs W hAlpha)
  have hFirstType : IsDefEqStrong Gamma
      (.forallE alpha ((SExpr.const ``Tree [l]).app alpha.lift))
      (.forallE alpha ((SExpr.const ``Tree [l]).app alpha.lift))
      (.sort (.imax l.succ l.succ)) :=
    .forallEDF hAlpha hTreeArg hTreeArg
  have hFirst : IsDefEqStrong Gamma
      ((SExpr.const ``Tree.leaf [l]).app alpha)
      ((SExpr.const ``Tree.leaf [l]).app alpha)
      (.forallE alpha ((SExpr.const ``Tree [l]).app alpha.lift)) := by
    simpa [SExpr.inst, SExpr.subst, Subst.one, Subst.cons, Subst.lift,
      SExpr.lift] using
      IsDefEqStrong.appDF (.sort) hCod hConst hAlpha hFirstType
  have hTree := d2TreeAppStrong univs l hAlpha
  have hTreeExact : IsDefEqStrong Gamma
      (((SExpr.const ``Tree [l]).app alpha.lift).inst x)
      (((SExpr.const ``Tree [l]).app alpha.lift).inst x) (.sort l.succ) := by
    simpa [SExpr.inst, SExpr.subst, Subst.one, Subst.cons, Subst.lift,
      SExpr.lift, lift_subst_cons] using hTree
  simpa [SExpr.inst, SExpr.subst, Subst.one, Subst.cons, Subst.lift,
    SExpr.lift, lift_subst_cons] using
    IsDefEqStrong.appDF hAlpha hTreeArg hFirst hx hTreeExact

/-- Strong typing of a fully applied `Tree.node` major premise. -/
theorem d2TreeNodeMajorStrong (univs : Nat)
    (l : @SLevel (d2Params univs))
    {Gamma : List (@SExpr (d2Params univs))}
    {alpha xs : @SExpr (d2Params univs)}
    (hAlpha : @IsDefEqStrong (d2Params univs) Gamma alpha alpha
      (@SExpr.sort (d2Params univs) (@SLevel.succ (d2Params univs) l)))
    (hxs : @IsDefEqStrong (d2Params univs) Gamma xs xs
      (@SExpr.app (d2Params univs)
        (@SExpr.const (d2Params univs) ``TreeList [l]) alpha)) :
    @IsDefEqStrong (d2Params univs) Gamma
      (@SExpr.app (d2Params univs)
        (@SExpr.app (d2Params univs)
          (@SExpr.const (d2Params univs) ``Tree.node [l]) alpha) xs)
      (@SExpr.app (d2Params univs)
        (@SExpr.app (d2Params univs)
          (@SExpr.const (d2Params univs) ``Tree.node [l]) alpha) xs)
      (@SExpr.app (d2Params univs)
        (@SExpr.const (d2Params univs) ``Tree [l]) alpha) := by
  letI : Params := d2Params univs
  let cl : @CtorBundle.IsCtor (d2Params univs) ``Tree.node := by
    refine ⟨.ctor 2, ?_, by simp⟩
    change d2Classify ``Tree.node = some (.ctor 2)
    simp [d2Classify]
  have hConst := d2ConstructorConstStrong univs
    d2Env_treeNode_lookup rfl cl (ls := [l]) (Gamma := Gamma)
  change IsDefEqStrong Gamma (.const ``Tree.node [l])
    (.const ``Tree.node [l])
    (.forallE (.sort l.succ)
      (.forallE ((SExpr.const ``TreeList [l]).app (.bvar 0))
        ((SExpr.const ``Tree [l]).app (.bvar 1)))) at hConst
  have hAlpha0 := d2AlphaStrong univs Gamma l
  have hField0 := d2TreeListAppStrong univs l hAlpha0
  have hTree1 : IsDefEqStrong
      ((SExpr.const ``TreeList [l]).app (.bvar 0) ::
        .sort l.succ :: Gamma)
      ((SExpr.const ``Tree [l]).app (.bvar 1))
      ((SExpr.const ``Tree [l]).app (.bvar 1)) (.sort l.succ) :=
    d2TreeAppStrong univs l
      (d2BvarStrong univs (.succ .zero) (by exact IsDefEqStrong.sort))
  have hCod : IsDefEqStrong (.sort l.succ :: Gamma)
      (.forallE ((SExpr.const ``TreeList [l]).app (.bvar 0))
        ((SExpr.const ``Tree [l]).app (.bvar 1)))
      (.forallE ((SExpr.const ``TreeList [l]).app (.bvar 0))
        ((SExpr.const ``Tree [l]).app (.bvar 1)))
      (.sort (.imax l.succ l.succ)) :=
    .forallEDF hField0 hTree1 hTree1
  let W : Ctx.Lift' (.skip .refl) Gamma
      ((SExpr.const ``TreeList [l]).app alpha :: Gamma) := .skip .refl
  have hTreeArg := d2TreeAppStrong univs l (d2StrongWeak univs W hAlpha)
  have hFirstType : IsDefEqStrong Gamma
      (.forallE ((SExpr.const ``TreeList [l]).app alpha)
        ((SExpr.const ``Tree [l]).app alpha.lift))
      (.forallE ((SExpr.const ``TreeList [l]).app alpha)
        ((SExpr.const ``Tree [l]).app alpha.lift))
      (.sort (.imax l.succ l.succ)) :=
    .forallEDF (d2TreeListAppStrong univs l hAlpha) hTreeArg hTreeArg
  have hFirst : IsDefEqStrong Gamma
      ((SExpr.const ``Tree.node [l]).app alpha)
      ((SExpr.const ``Tree.node [l]).app alpha)
      (.forallE ((SExpr.const ``TreeList [l]).app alpha)
        ((SExpr.const ``Tree [l]).app alpha.lift)) := by
    simpa [SExpr.inst, SExpr.subst, Subst.one, Subst.cons, Subst.lift,
      SExpr.lift] using
      IsDefEqStrong.appDF (.sort) hCod hConst hAlpha hFirstType
  have hTree := d2TreeAppStrong univs l hAlpha
  have hTreeExact : IsDefEqStrong Gamma
      (((SExpr.const ``Tree [l]).app alpha.lift).inst xs)
      (((SExpr.const ``Tree [l]).app alpha.lift).inst xs) (.sort l.succ) := by
    simpa [SExpr.inst, SExpr.subst, Subst.one, Subst.cons, Subst.lift,
      SExpr.lift, lift_subst_cons] using hTree
  simpa [SExpr.inst, SExpr.subst, Subst.one, Subst.cons, Subst.lift,
    SExpr.lift, lift_subst_cons] using
    IsDefEqStrong.appDF (d2TreeListAppStrong univs l hAlpha)
      hTreeArg hFirst hxs hTreeExact

/-- Strong typing of the higher-order `Tree.branch` major premise. -/
theorem d2TreeBranchMajorStrong (univs : Nat)
    (l : @SLevel (d2Params univs))
    {Gamma : List (@SExpr (d2Params univs))}
    {alpha f : @SExpr (d2Params univs)}
    (hAlpha : @IsDefEqStrong (d2Params univs) Gamma alpha alpha
      (@SExpr.sort (d2Params univs) (@SLevel.succ (d2Params univs) l)))
    (hf : @IsDefEqStrong (d2Params univs) Gamma f f
      (@SExpr.forallE (d2Params univs) alpha
        (@SExpr.app (d2Params univs)
          (@SExpr.const (d2Params univs) ``TreeList [l])
          (@SExpr.lift (d2Params univs) alpha)))) :
    @IsDefEqStrong (d2Params univs) Gamma
      (@SExpr.app (d2Params univs)
        (@SExpr.app (d2Params univs)
          (@SExpr.const (d2Params univs) ``Tree.branch [l]) alpha) f)
      (@SExpr.app (d2Params univs)
        (@SExpr.app (d2Params univs)
          (@SExpr.const (d2Params univs) ``Tree.branch [l]) alpha) f)
      (@SExpr.app (d2Params univs)
        (@SExpr.const (d2Params univs) ``Tree [l]) alpha) := by
  letI : Params := d2Params univs
  let cl : @CtorBundle.IsCtor (d2Params univs) ``Tree.branch := by
    refine ⟨.ctor 2, ?_, by simp⟩
    change d2Classify ``Tree.branch = some (.ctor 2)
    simp [d2Classify]
  have hConst := d2ConstructorConstStrong univs
    d2Env_treeBranch_lookup rfl cl (ls := [l]) (Gamma := Gamma)
  change IsDefEqStrong Gamma (.const ``Tree.branch [l])
    (.const ``Tree.branch [l])
    (.forallE (.sort l.succ)
      (.forallE
        (.forallE (.bvar 0)
          ((SExpr.const ``TreeList [l]).app (.bvar 1)))
        ((SExpr.const ``Tree [l]).app (.bvar 1)))) at hConst
  have hAlpha0 := d2AlphaStrong univs Gamma l
  have hTreeList1 : IsDefEqStrong (.bvar 0 :: .sort l.succ :: Gamma)
      ((SExpr.const ``TreeList [l]).app (.bvar 1))
      ((SExpr.const ``TreeList [l]).app (.bvar 1)) (.sort l.succ) :=
    d2TreeListAppStrong univs l
      (d2BvarStrong univs (.succ .zero) (by exact IsDefEqStrong.sort))
  have hField0 : IsDefEqStrong (.sort l.succ :: Gamma)
      (.forallE (.bvar 0) ((SExpr.const ``TreeList [l]).app (.bvar 1)))
      (.forallE (.bvar 0) ((SExpr.const ``TreeList [l]).app (.bvar 1)))
      (.sort (.imax l.succ l.succ)) :=
    .forallEDF hAlpha0 hTreeList1 hTreeList1
  have hTree1 : IsDefEqStrong
      (.forallE (.bvar 0) ((SExpr.const ``TreeList [l]).app (.bvar 1)) ::
        .sort l.succ :: Gamma)
      ((SExpr.const ``Tree [l]).app (.bvar 1))
      ((SExpr.const ``Tree [l]).app (.bvar 1)) (.sort l.succ) :=
    d2TreeAppStrong univs l
      (d2BvarStrong univs (.succ .zero) (by exact IsDefEqStrong.sort))
  have hCod : IsDefEqStrong (.sort l.succ :: Gamma)
      (.forallE
        (.forallE (.bvar 0) ((SExpr.const ``TreeList [l]).app (.bvar 1)))
        ((SExpr.const ``Tree [l]).app (.bvar 1)))
      (.forallE
        (.forallE (.bvar 0) ((SExpr.const ``TreeList [l]).app (.bvar 1)))
        ((SExpr.const ``Tree [l]).app (.bvar 1)))
      (.sort (.imax (.imax l.succ l.succ) l.succ)) :=
    .forallEDF hField0 hTree1 hTree1
  let WA : Ctx.Lift' (.skip .refl) Gamma (alpha :: Gamma) := .skip .refl
  have hTreeListArg := d2TreeListAppStrong univs l
    (d2StrongWeak univs WA hAlpha)
  have hFieldType : IsDefEqStrong Gamma
      (.forallE alpha ((SExpr.const ``TreeList [l]).app alpha.lift))
      (.forallE alpha ((SExpr.const ``TreeList [l]).app alpha.lift))
      (.sort (.imax l.succ l.succ)) :=
    .forallEDF hAlpha hTreeListArg hTreeListArg
  let WF : Ctx.Lift' (.skip .refl) Gamma
      (.forallE alpha ((SExpr.const ``TreeList [l]).app alpha.lift) :: Gamma) :=
    .skip .refl
  have hTreeArg := d2TreeAppStrong univs l (d2StrongWeak univs WF hAlpha)
  have hFirstType : IsDefEqStrong Gamma
      (.forallE
        (.forallE alpha ((SExpr.const ``TreeList [l]).app alpha.lift))
        ((SExpr.const ``Tree [l]).app alpha.lift))
      (.forallE
        (.forallE alpha ((SExpr.const ``TreeList [l]).app alpha.lift))
        ((SExpr.const ``Tree [l]).app alpha.lift))
      (.sort (.imax (.imax l.succ l.succ) l.succ)) :=
    .forallEDF hFieldType hTreeArg hTreeArg
  have hFirst : IsDefEqStrong Gamma
      ((SExpr.const ``Tree.branch [l]).app alpha)
      ((SExpr.const ``Tree.branch [l]).app alpha)
      (.forallE
        (.forallE alpha ((SExpr.const ``TreeList [l]).app alpha.lift))
        ((SExpr.const ``Tree [l]).app alpha.lift)) := by
    simpa [SExpr.inst, SExpr.subst, Subst.one, Subst.cons, Subst.lift,
      SExpr.lift] using
      IsDefEqStrong.appDF (.sort) hCod hConst hAlpha hFirstType
  have hTree := d2TreeAppStrong univs l hAlpha
  have hTreeExact : IsDefEqStrong Gamma
      (((SExpr.const ``Tree [l]).app alpha.lift).inst f)
      (((SExpr.const ``Tree [l]).app alpha.lift).inst f) (.sort l.succ) := by
    simpa [SExpr.inst, SExpr.subst, Subst.one, Subst.cons, Subst.lift,
      SExpr.lift, lift_subst_cons] using hTree
  simpa [SExpr.inst, SExpr.subst, Subst.one, Subst.cons, Subst.lift,
    SExpr.lift, lift_subst_cons] using
    IsDefEqStrong.appDF hFieldType hTreeArg hFirst hf hTreeExact

/-- Strong typing of `TreeList.nil`, whose only explicit argument is the
shared type parameter. -/
theorem d2TreeListNilMajorStrong (univs : Nat)
    (l : @SLevel (d2Params univs))
    {Gamma : List (@SExpr (d2Params univs))}
    {alpha : @SExpr (d2Params univs)}
    (hAlpha : @IsDefEqStrong (d2Params univs) Gamma alpha alpha
      (@SExpr.sort (d2Params univs) (@SLevel.succ (d2Params univs) l))) :
    @IsDefEqStrong (d2Params univs) Gamma
      (@SExpr.app (d2Params univs)
        (@SExpr.const (d2Params univs) ``TreeList.nil [l]) alpha)
      (@SExpr.app (d2Params univs)
        (@SExpr.const (d2Params univs) ``TreeList.nil [l]) alpha)
      (@SExpr.app (d2Params univs)
        (@SExpr.const (d2Params univs) ``TreeList [l]) alpha) := by
  letI : Params := d2Params univs
  let cl : @CtorBundle.IsCtor (d2Params univs) ``TreeList.nil := by
    refine ⟨.ctor 1, ?_, by simp⟩
    change d2Classify ``TreeList.nil = some (.ctor 1)
    simp [d2Classify]
  have hConst := d2ConstructorConstStrong univs
    d2Env_treeListNil_lookup rfl cl (ls := [l]) (Gamma := Gamma)
  change IsDefEqStrong Gamma (.const ``TreeList.nil [l])
    (.const ``TreeList.nil [l])
    (.forallE (.sort l.succ)
      ((SExpr.const ``TreeList [l]).app (.bvar 0))) at hConst
  have hCod := d2TreeListAppStrong univs l (d2AlphaStrong univs Gamma l)
  have hResult := d2TreeListAppStrong univs l hAlpha
  simpa [SExpr.inst, SExpr.subst, Subst.one, Subst.cons, SExpr.lift] using
    IsDefEqStrong.appDF (.sort) hCod hConst hAlpha hResult

/-- Strong typing of a fully applied `TreeList.cons` major premise. -/
theorem d2TreeListConsMajorStrong (univs : Nat)
    (l : @SLevel (d2Params univs))
    {Gamma : List (@SExpr (d2Params univs))}
    {alpha t ts : @SExpr (d2Params univs)}
    (hAlpha : @IsDefEqStrong (d2Params univs) Gamma alpha alpha
      (@SExpr.sort (d2Params univs) (@SLevel.succ (d2Params univs) l)))
    (ht : @IsDefEqStrong (d2Params univs) Gamma t t
      (@SExpr.app (d2Params univs)
        (@SExpr.const (d2Params univs) ``Tree [l]) alpha))
    (hts : @IsDefEqStrong (d2Params univs) Gamma ts ts
      (@SExpr.app (d2Params univs)
        (@SExpr.const (d2Params univs) ``TreeList [l]) alpha)) :
    @IsDefEqStrong (d2Params univs) Gamma
      (@SExpr.app (d2Params univs)
        (@SExpr.app (d2Params univs)
          (@SExpr.app (d2Params univs)
            (@SExpr.const (d2Params univs) ``TreeList.cons [l]) alpha) t) ts)
      (@SExpr.app (d2Params univs)
        (@SExpr.app (d2Params univs)
          (@SExpr.app (d2Params univs)
            (@SExpr.const (d2Params univs) ``TreeList.cons [l]) alpha) t) ts)
      (@SExpr.app (d2Params univs)
        (@SExpr.const (d2Params univs) ``TreeList [l]) alpha) := by
  letI : Params := d2Params univs
  let cl : @CtorBundle.IsCtor (d2Params univs) ``TreeList.cons := by
    refine ⟨.ctor 3, ?_, by simp⟩
    change d2Classify ``TreeList.cons = some (.ctor 3)
    simp [d2Classify]
  have hConst := d2ConstructorConstStrong univs
    d2Env_treeListCons_lookup rfl cl (ls := [l]) (Gamma := Gamma)
  change IsDefEqStrong Gamma (.const ``TreeList.cons [l])
    (.const ``TreeList.cons [l])
    (.forallE (.sort l.succ)
      (.forallE ((SExpr.const ``Tree [l]).app (.bvar 0))
        (.forallE ((SExpr.const ``TreeList [l]).app (.bvar 1))
          ((SExpr.const ``TreeList [l]).app (.bvar 2))))) at hConst
  have hAlpha0 := d2AlphaStrong univs Gamma l
  have hTree0 := d2TreeAppStrong univs l hAlpha0
  have hTreeList1 : IsDefEqStrong
      ((SExpr.const ``Tree [l]).app (.bvar 0) :: .sort l.succ :: Gamma)
      ((SExpr.const ``TreeList [l]).app (.bvar 1))
      ((SExpr.const ``TreeList [l]).app (.bvar 1)) (.sort l.succ) :=
    d2TreeListAppStrong univs l
      (d2BvarStrong univs (.succ .zero) (by exact IsDefEqStrong.sort))
  have hTreeList2 : IsDefEqStrong
      ((SExpr.const ``TreeList [l]).app (.bvar 1) ::
        (SExpr.const ``Tree [l]).app (.bvar 0) :: .sort l.succ :: Gamma)
      ((SExpr.const ``TreeList [l]).app (.bvar 2))
      ((SExpr.const ``TreeList [l]).app (.bvar 2)) (.sort l.succ) :=
    d2TreeListAppStrong univs l
      (d2BvarStrong univs (.succ (.succ .zero))
        (by exact IsDefEqStrong.sort))
  have hInner0 : IsDefEqStrong
      ((SExpr.const ``Tree [l]).app (.bvar 0) :: .sort l.succ :: Gamma)
      (.forallE ((SExpr.const ``TreeList [l]).app (.bvar 1))
        ((SExpr.const ``TreeList [l]).app (.bvar 2)))
      (.forallE ((SExpr.const ``TreeList [l]).app (.bvar 1))
        ((SExpr.const ``TreeList [l]).app (.bvar 2)))
      (.sort (.imax l.succ l.succ)) :=
    .forallEDF hTreeList1 hTreeList2 hTreeList2
  have hCod : IsDefEqStrong (.sort l.succ :: Gamma)
      (.forallE ((SExpr.const ``Tree [l]).app (.bvar 0))
        (.forallE ((SExpr.const ``TreeList [l]).app (.bvar 1))
          ((SExpr.const ``TreeList [l]).app (.bvar 2))))
      (.forallE ((SExpr.const ``Tree [l]).app (.bvar 0))
        (.forallE ((SExpr.const ``TreeList [l]).app (.bvar 1))
          ((SExpr.const ``TreeList [l]).app (.bvar 2))))
      (.sort (.imax l.succ (.imax l.succ l.succ))) :=
    .forallEDF hTree0 hInner0 hInner0
  have hTree := d2TreeAppStrong univs l hAlpha
  let WT : Ctx.Lift' (.skip .refl) Gamma
      ((SExpr.const ``Tree [l]).app alpha :: Gamma) := .skip .refl
  have hTreeListUnderTree := d2TreeListAppStrong univs l
    (d2StrongWeak univs WT hAlpha)
  let WTT : Ctx.Lift' (.skipN .refl 2) Gamma
      (((SExpr.const ``TreeList [l]).app alpha.lift) ::
        ((SExpr.const ``Tree [l]).app alpha) :: Gamma) := by
    simpa using
      (Ctx.Lift'.skipAppend
        [((SExpr.const ``TreeList [l]).app alpha.lift),
          ((SExpr.const ``Tree [l]).app alpha)] :
        Ctx.Lift' (.skipN .refl 2) Gamma
          ([((SExpr.const ``TreeList [l]).app alpha.lift),
            ((SExpr.const ``Tree [l]).app alpha)] ++ Gamma))
  have hResultUnderBoth := d2TreeListAppStrong univs l
    (d2StrongWeak univs WTT hAlpha)
  have hResultUnderBoth' : IsDefEqStrong
      ((SExpr.const ``TreeList [l]).app alpha.lift ::
        (SExpr.const ``Tree [l]).app alpha :: Gamma)
      ((SExpr.const ``TreeList [l]).app alpha.lift.lift)
      ((SExpr.const ``TreeList [l]).app alpha.lift.lift) (.sort l.succ) := by
    simpa [SExpr.lift, ← SExpr.lift'_comp] using hResultUnderBoth
  have hInner : IsDefEqStrong
      ((SExpr.const ``Tree [l]).app alpha :: Gamma)
      (.forallE ((SExpr.const ``TreeList [l]).app alpha.lift)
        ((SExpr.const ``TreeList [l]).app alpha.lift.lift))
      (.forallE ((SExpr.const ``TreeList [l]).app alpha.lift)
        ((SExpr.const ``TreeList [l]).app alpha.lift.lift))
      (.sort (.imax l.succ l.succ)) :=
    .forallEDF hTreeListUnderTree hResultUnderBoth' hResultUnderBoth'
  have hFirstType : IsDefEqStrong Gamma
      (.forallE ((SExpr.const ``Tree [l]).app alpha)
        (.forallE ((SExpr.const ``TreeList [l]).app alpha.lift)
          ((SExpr.const ``TreeList [l]).app alpha.lift.lift)))
      (.forallE ((SExpr.const ``Tree [l]).app alpha)
        (.forallE ((SExpr.const ``TreeList [l]).app alpha.lift)
          ((SExpr.const ``TreeList [l]).app alpha.lift.lift)))
      (.sort (.imax l.succ (.imax l.succ l.succ))) :=
    .forallEDF hTree hInner hInner
  have hFirst : IsDefEqStrong Gamma
      ((SExpr.const ``TreeList.cons [l]).app alpha)
      ((SExpr.const ``TreeList.cons [l]).app alpha)
      (.forallE ((SExpr.const ``Tree [l]).app alpha)
        (.forallE ((SExpr.const ``TreeList [l]).app alpha.lift)
          ((SExpr.const ``TreeList [l]).app alpha.lift.lift))) := by
    simpa [SExpr.inst, SExpr.subst, Subst.one, Subst.cons, Subst.lift,
      SExpr.lift] using
      IsDefEqStrong.appDF (.sort) hCod hConst hAlpha hFirstType
  have hTreeList := d2TreeListAppStrong univs l hAlpha
  let WTS : Ctx.Lift' (.skip .refl) Gamma
      ((SExpr.const ``TreeList [l]).app alpha :: Gamma) := .skip .refl
  have hTreeListResult := d2TreeListAppStrong univs l
    (d2StrongWeak univs WTS hAlpha)
  have hSecondType : IsDefEqStrong Gamma
      (.forallE ((SExpr.const ``TreeList [l]).app alpha)
        ((SExpr.const ``TreeList [l]).app alpha.lift))
      (.forallE ((SExpr.const ``TreeList [l]).app alpha)
        ((SExpr.const ``TreeList [l]).app alpha.lift))
      (.sort (.imax l.succ l.succ)) :=
    .forallEDF hTreeList hTreeListResult hTreeListResult
  have hSecondTypeExact : IsDefEqStrong Gamma
      ((SExpr.forallE ((SExpr.const ``TreeList [l]).app alpha.lift)
        ((SExpr.const ``TreeList [l]).app alpha.lift.lift)).inst t)
      ((SExpr.forallE ((SExpr.const ``TreeList [l]).app alpha.lift)
        ((SExpr.const ``TreeList [l]).app alpha.lift.lift)).inst t)
      (.sort (.imax l.succ l.succ)) := by
    simpa [SExpr.inst, SExpr.subst, Subst.one, Subst.cons, Subst.lift,
      SExpr.lift, lift_subst_cons, ParamsD0.probeCancelUnderOne] using
      hSecondType
  have hSecond : IsDefEqStrong Gamma
      (((SExpr.const ``TreeList.cons [l]).app alpha).app t)
      (((SExpr.const ``TreeList.cons [l]).app alpha).app t)
      (.forallE ((SExpr.const ``TreeList [l]).app alpha)
        ((SExpr.const ``TreeList [l]).app alpha.lift)) := by
    simpa [SExpr.inst, SExpr.subst, Subst.one, Subst.cons, Subst.lift,
      SExpr.lift, lift_subst_cons, ParamsD0.probeCancelUnderOne] using
      IsDefEqStrong.appDF hTree hInner hFirst ht hSecondTypeExact
  have hResult : IsDefEqStrong Gamma
      (((SExpr.const ``TreeList [l]).app alpha.lift).inst ts)
      (((SExpr.const ``TreeList [l]).app alpha.lift).inst ts)
      (.sort l.succ) := by
    simpa [SExpr.inst, SExpr.subst, Subst.one, Subst.cons, Subst.lift,
      SExpr.lift, lift_subst_cons] using hTreeList
  simpa [SExpr.inst, SExpr.subst, Subst.one, Subst.cons, Subst.lift,
    SExpr.lift, lift_subst_cons] using
    IsDefEqStrong.appDF hTreeList hTreeListResult hSecond hts hResult

theorem d2LeafFieldBindersV_eq :
    d2FieldBindersV TreeGen.flatCtors[0] = [.bvar 7] := by
  native_decide

theorem d2InstVParamZero (univs : Nat)
    (u l : @SLevel (d2Params univs)) :
    @SLevel.instV (d2Params univs) [u, l] (.param 0) = u := by
  apply Subtype.ext
  rfl

theorem d2InstVParamOne (univs : Nat)
    (u l : @SLevel (d2Params univs)) :
    @SLevel.instV (d2Params univs) [u, l] (.param 1) = l := by
  apply Subtype.ext
  rfl

/-- The mutual fixture uses its second recursor universe as the sole source
universe of every Tree/TreeList constructor. -/
theorem d2TreeSourceLevels_eq :
    TreeGen.sourceLevels = [.param 1] := by
  rfl

/-- Concrete form of the canonical source-level side of
`D2TreeLevelAlignmentStep`. -/
theorem d2TreeSourceLevels_instV (univs : Nat)
    (u l : @SLevel (d2Params univs)) :
    TreeGen.sourceLevels.map (@SLevel.instV (d2Params univs) [u, l]) = [l] := by
  rw [d2TreeSourceLevels_eq]
  simp only [List.map_cons, List.map_nil, d2InstVParamOne]

/-- The canonical eight-variable specialization of the `Tree.rec` head. -/
def d2TreeRecCommonTerm (univs : Nat)
    (u l : @SLevel (d2Params univs)) : @SExpr (d2Params univs) :=
  letI : Params := d2Params univs
  ([.bvar 7, .bvar 6, .bvar 5, .bvar 4,
    .bvar 3, .bvar 2, .bvar 1, .bvar 0] : List SExpr).foldl
      (fun f a => f.app a) (.const ``Tree.rec [u, l])

theorem d2TreeRecCommonTerm_eq (univs : Nat)
    (u l : @SLevel (d2Params univs)) :
    letI : Params := d2Params univs
    applyTelVars (d2CommonBinders [u, l]) (.const ``Tree.rec [u, l]) =
      d2TreeRecCommonTerm univs u l := by
  letI : Params := d2Params univs
  rw [applyTelVars_eq_of_length (Bs := List.replicate 8 (.sort .zero))
    (by simpa [d2CommonBinders] using d2CommonBindersV_length)]
  rfl

/-- The analogous specialization of `TreeList.rec`. -/
def d2TreeListRecCommonTerm (univs : Nat)
    (u l : @SLevel (d2Params univs)) : @SExpr (d2Params univs) :=
  letI : Params := d2Params univs
  ([.bvar 7, .bvar 6, .bvar 5, .bvar 4,
    .bvar 3, .bvar 2, .bvar 1, .bvar 0] : List SExpr).foldl
      (fun f a => f.app a) (.const ``TreeList.rec [u, l])

theorem d2TreeListRecCommonTerm_eq (univs : Nat)
    (u l : @SLevel (d2Params univs)) :
    letI : Params := d2Params univs
    applyTelVars (d2CommonBinders [u, l]) (.const ``TreeList.rec [u, l]) =
      d2TreeListRecCommonTerm univs u l := by
  letI : Params := d2Params univs
  rw [applyTelVars_eq_of_length (Bs := List.replicate 8 (.sort .zero))
    (by simpa [d2CommonBinders] using d2CommonBindersV_length)]
  rfl

theorem d2LeafRuleLhsBodyV_eq :
    TreeGen.ruleLhsBody TreeGen.flatCtors[0] =
      VExpr.appN (.const ``Tree.rec [.param 0, .param 1])
        [.bvar 8, .bvar 7, .bvar 6, .bvar 5, .bvar 4,
          .bvar 3, .bvar 2, .bvar 1,
          ((VExpr.const ``Tree.leaf [.param 1]).app (.bvar 8)).app (.bvar 0)] := by
  native_decide

theorem d2LeafRuleResultV_eq :
    d2RuleResult TreeGen.flatCtors[0] =
      (VExpr.bvar 7).app
        (((VExpr.const ``Tree.leaf [.param 1]).app (.bvar 8)).app (.bvar 0)) := by
  native_decide

theorem d2NodeFieldBindersV_eq :
    d2FieldBindersV TreeGen.flatCtors[1] =
      [(VExpr.const ``TreeList [.param 1]).app (.bvar 7)] := by
  native_decide

theorem d2BranchFieldBindersV_eq :
    d2FieldBindersV TreeGen.flatCtors[2] =
      [(VExpr.bvar 7).forallE
        ((VExpr.const ``TreeList [.param 1]).app (.bvar 8))] := by
  native_decide

theorem d2NilFieldBindersV_eq :
    d2FieldBindersV TreeGen.flatCtors[3] = [] := by
  native_decide

theorem d2ConsFieldBindersV_eq :
    d2FieldBindersV TreeGen.flatCtors[4] =
      [(VExpr.const ``Tree [.param 1]).app (.bvar 7),
        (VExpr.const ``TreeList [.param 1]).app (.bvar 8)] := by
  native_decide

theorem d2NodeRuleLhsBodyV_eq :
    TreeGen.ruleLhsBody TreeGen.flatCtors[1] =
      VExpr.appN (.const ``Tree.rec [.param 0, .param 1])
        [.bvar 8, .bvar 7, .bvar 6, .bvar 5, .bvar 4,
          .bvar 3, .bvar 2, .bvar 1,
          ((VExpr.const ``Tree.node [.param 1]).app (.bvar 8)).app (.bvar 0)] := by
  native_decide

theorem d2NodeRuleResultV_eq :
    d2RuleResult TreeGen.flatCtors[1] =
      (VExpr.bvar 7).app
        (((VExpr.const ``Tree.node [.param 1]).app (.bvar 8)).app (.bvar 0)) := by
  native_decide

theorem d2BranchRuleLhsBodyV_eq :
    TreeGen.ruleLhsBody TreeGen.flatCtors[2] =
      VExpr.appN (.const ``Tree.rec [.param 0, .param 1])
        [.bvar 8, .bvar 7, .bvar 6, .bvar 5, .bvar 4,
          .bvar 3, .bvar 2, .bvar 1,
          ((VExpr.const ``Tree.branch [.param 1]).app (.bvar 8)).app (.bvar 0)] := by
  native_decide

theorem d2BranchRuleResultV_eq :
    d2RuleResult TreeGen.flatCtors[2] =
      (VExpr.bvar 7).app
        (((VExpr.const ``Tree.branch [.param 1]).app (.bvar 8)).app (.bvar 0)) := by
  native_decide

theorem d2NilRuleLhsBodyV_eq :
    TreeGen.ruleLhsBody TreeGen.flatCtors[3] =
      VExpr.appN (.const ``TreeList.rec [.param 0, .param 1])
        [.bvar 7, .bvar 6, .bvar 5, .bvar 4,
          .bvar 3, .bvar 2, .bvar 1, .bvar 0,
          (VExpr.const ``TreeList.nil [.param 1]).app (.bvar 7)] := by
  native_decide

theorem d2NilRuleResultV_eq :
    d2RuleResult TreeGen.flatCtors[3] =
      (VExpr.bvar 5).app
        ((VExpr.const ``TreeList.nil [.param 1]).app (.bvar 7)) := by
  native_decide

theorem d2ConsRuleLhsBodyV_eq :
    TreeGen.ruleLhsBody TreeGen.flatCtors[4] =
      VExpr.appN (.const ``TreeList.rec [.param 0, .param 1])
        [.bvar 9, .bvar 8, .bvar 7, .bvar 6,
          .bvar 5, .bvar 4, .bvar 3, .bvar 2,
          (((VExpr.const ``TreeList.cons [.param 1]).app (.bvar 9)).app
            (.bvar 1)).app (.bvar 0)] := by
  native_decide

theorem d2ConsRuleResultV_eq :
    d2RuleResult TreeGen.flatCtors[4] =
      (VExpr.bvar 7).app
        ((((VExpr.const ``TreeList.cons [.param 1]).app (.bvar 9)).app
          (.bvar 1)).app (.bvar 0)) := by
  native_decide

/-- Instantiate the generator's exact Theory match at arbitrary semantic
levels and translate it to the S-expression layer. -/
theorem d2RuleLhsBody_matchesS (univs : Nat)
    (u l : @SLevel (d2Params univs))
    (constructor : NormalizedBlockCtor) :
    letI : Params := d2Params univs
    ∃ mcap : ((TreeGen.rulePattern constructor).toPattern).Path → SExpr,
      ((TreeGen.rulePattern constructor).toPattern).MatchesS
        (SExpr.mkInst [u, l] (TreeGen.ruleLhsBody constructor)) [u, l] mcap := by
  letI : Params := d2Params univs
  obtain ⟨mcapV, hm⟩ := TreeGen.ruleLhsBody_matches constructor
  let vls : List VLevel := [u.reify, l.reify]
  have hmS := (hm.instL vls).mkS
  have hterm : SExpr.mk
      ((TreeGen.ruleLhsBody constructor).instL vls) =
      SExpr.mkInst [u, l] (TreeGen.ruleLhsBody constructor) := by
    simpa only [vls, List.map_cons, List.map_nil] using
      (@SExpr.mk_instL_map_reify (d2Params univs)
        (TreeGen.ruleLhsBody constructor) [u, l])
  have hlevels :
      (TreeGen.recLevels.map (VLevel.inst vls)).map SLevel.mk = [u, l] := by
    change [SLevel.mk u.reify, SLevel.mk l.reify] = [u, l]
    simp only [SLevel.mk_reify]
  rw [hterm, hlevels] at hmS
  refine ⟨fun path => SExpr.mk ((mcapV path).instL vls), ?_⟩
  exact hmS

/-- Read the ordered shared/field captures from a successful generated-rule
match. -/
theorem d2TreeCaptureValues (univs : Nat)
    {constructor : NormalizedBlockCtor}
    {recLs ctorLs : List (@SLevel (d2Params univs))}
    {recArgs ctorArgs : List (@SExpr (d2Params univs))}
    {mcap : ((TreeGen.rulePattern constructor).toPattern).Path →
      @SExpr (d2Params univs)}
    (H : @Pattern.MatchesS (d2Params univs)
      ((TreeGen.rulePattern constructor).toPattern)
      (@SExpr.app (d2Params univs)
        (recArgs.foldr (fun a f => @SExpr.app (d2Params univs) f a)
          (@SExpr.const (d2Params univs)
            (TreeGen.ruleRecName constructor) recLs))
        (ctorArgs.foldr (fun a f => @SExpr.app (d2Params univs) f a)
          (@SExpr.const (d2Params univs) constructor.ctor.raw.name ctorLs)))
      recLs mcap) :
    letI : Params := d2Params univs
    (treeCapturePaths constructor).map mcap =
      recArgs.reverse.take 8 ++ ctorArgs.reverse.drop 1 := by
  letI : Params := d2Params univs
  cases H with
  | app hrec hctor =>
    obtain ⟨-, -, hrecValues⟩ := ParamsD0.matchesS_varN_foldr hrec
    obtain ⟨-, -, hctorValues⟩ := ParamsD0.matchesS_varN_foldr hctor
    rename_i recCap ctorCap
    rw [treeCapturePaths, List.map_append, List.map_map, List.map_map]
    change
      List.map recCap
          (List.take 8 (Pattern.varNPaths
            (.const (TreeGen.ruleRecName constructor))
            (TreeGen.ruleMajorArity constructor))) ++
        List.map ctorCap
          (List.drop 1 (Pattern.varNPaths
            (.const constructor.ctor.raw.name)
            (TreeGen.ruleArgArity constructor))) = _
    rw [List.map_take, List.map_drop, hrecValues, hctorValues]

/-- Every entry of the concrete mutual block has the same eight common
recursor arguments. -/
theorem d2TreeRuleMajorArity_eq_eight {i : Nat}
    {constructor : NormalizedBlockCtor}
    (hentry : TreeGen.flatCtors[i]? = some constructor) :
    TreeGen.ruleMajorArity constructor = 8 := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hentry
    have : TreeGen.flatCtors.length = 5 := rfl
    omega
  rcases hi with rfl | rfl | rfl | rfl | rfl
  all_goals
    first
    | have hc := Option.some.inj
        ((show TreeGen.flatCtors[0]? = some TreeGen.flatCtors[0] from rfl).symm.trans
          hentry)
    | have hc := Option.some.inj
        ((show TreeGen.flatCtors[1]? = some TreeGen.flatCtors[1] from rfl).symm.trans
          hentry)
    | have hc := Option.some.inj
        ((show TreeGen.flatCtors[2]? = some TreeGen.flatCtors[2] from rfl).symm.trans
          hentry)
    | have hc := Option.some.inj
        ((show TreeGen.flatCtors[3]? = some TreeGen.flatCtors[3] from rfl).symm.trans
          hentry)
    | have hc := Option.some.inj
        ((show TreeGen.flatCtors[4]? = some TreeGen.flatCtors[4] from rfl).symm.trans
          hentry)
    subst constructor
    rfl

/-- Remove the now-known `take 8` from the generic match inventory.  The
capture list is exactly the eight common recursor arguments followed by the
constructor fields; its parameter is deliberately absent from the suffix. -/
theorem d2TreeCaptureValues_exact (univs : Nat)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (hentry : TreeGen.flatCtors[i]? = some constructor)
    {recLs ctorLs : List (@SLevel (d2Params univs))}
    {recArgs ctorArgs : List (@SExpr (d2Params univs))}
    {mcap : ((TreeGen.rulePattern constructor).toPattern).Path →
      @SExpr (d2Params univs)}
    (H : @Pattern.MatchesS (d2Params univs)
      ((TreeGen.rulePattern constructor).toPattern)
      (@SExpr.app (d2Params univs)
        (recArgs.foldr (fun a f => @SExpr.app (d2Params univs) f a)
          (@SExpr.const (d2Params univs)
            (TreeGen.ruleRecName constructor) recLs))
        (ctorArgs.foldr (fun a f => @SExpr.app (d2Params univs) f a)
          (@SExpr.const (d2Params univs) constructor.ctor.raw.name ctorLs)))
      recLs mcap) :
    letI : Params := d2Params univs
    (treeCapturePaths constructor).map mcap =
      recArgs.reverse ++ ctorArgs.reverse.drop 1 := by
  letI : Params := d2Params univs
  have hcaps := d2TreeCaptureValues univs H
  cases H with
  | app hrec _ =>
    obtain ⟨-, hrecLen, -⟩ := ParamsD0.matchesS_varN_foldr hrec
    have hmajor := d2TreeRuleMajorArity_eq_eight hentry
    have hlen : recArgs.reverse.length = 8 := by
      simpa [hmajor] using hrecLen
    rw [← hlen, List.take_length] at hcaps
    exact hcaps

theorem d2LeafCaptureValues (univs : Nat)
    (u l : @SLevel (d2Params univs))
    {mcap : ((TreeGen.rulePattern TreeGen.flatCtors[0]).toPattern).Path →
      @SExpr (d2Params univs)}
    (H : @Pattern.MatchesS (d2Params univs)
      ((TreeGen.rulePattern TreeGen.flatCtors[0]).toPattern)
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.ruleLhsBody TreeGen.flatCtors[0])) [u, l] mcap) :
    letI : Params := d2Params univs
    (treeCapturePaths TreeGen.flatCtors[0]).map mcap =
      [.bvar 8, .bvar 7, .bvar 6, .bvar 5, .bvar 4,
        .bvar 3, .bvar 2, .bvar 1, .bvar 0] := by
  letI : Params := d2Params univs
  have H' : ((TreeGen.rulePattern TreeGen.flatCtors[0]).toPattern).MatchesS
      ((([.bvar 1, .bvar 2, .bvar 3, .bvar 4,
          .bvar 5, .bvar 6, .bvar 7, .bvar 8] : List SExpr).foldr
          (fun (a f : SExpr) => f.app a) (SExpr.const ``Tree.rec [u, l])).app
        (([.bvar 0, .bvar 8] : List SExpr).foldr
          (fun (a f : SExpr) => f.app a) (SExpr.const ``Tree.leaf [l])))
        [u, l] mcap := by
    rw [d2LeafRuleLhsBodyV_eq] at H
    simpa [mkInst_appN, SExpr.mkInst, d2InstVParamZero,
      d2InstVParamOne] using H
  have hcaps := d2TreeCaptureValues univs H'
  simpa using hcaps

theorem d2LeafCheckShape (univs : Nat)
    (u l : @SLevel (d2Params univs))
    (mcap : ((TreeGen.rulePattern TreeGen.flatCtors[0]).toPattern).Path →
      @SExpr (d2Params univs)) :
    letI : Params := d2Params univs
    (TreeGen.ruleCheck treeRuleClosure
      (List.mem_of_getElem? (show TreeGen.flatCtors[0]? =
        some TreeGen.flatCtors[0] from rfl))).defeqsS [u, l] mcap =
      [(mcap (.inr (some none)),
        mcap (.inl (some (some (some (some (some (some (some none)))))))))] := by
  rfl

theorem d2LeafCheckDefeqs (univs : Nat)
    (u l : @SLevel (d2Params univs))
    {mcap : ((TreeGen.rulePattern TreeGen.flatCtors[0]).toPattern).Path →
      @SExpr (d2Params univs)}
    (H : @Pattern.MatchesS (d2Params univs)
      ((TreeGen.rulePattern TreeGen.flatCtors[0]).toPattern)
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.ruleLhsBody TreeGen.flatCtors[0])) [u, l] mcap) :
    letI : Params := d2Params univs
    (TreeGen.ruleCheck treeRuleClosure
      (List.mem_of_getElem? (show TreeGen.flatCtors[0]? =
        some TreeGen.flatCtors[0] from rfl))).defeqsS [u, l] mcap =
      [(.bvar 8, .bvar 8)] := by
  letI : Params := d2Params univs
  have H' : ((TreeGen.rulePattern TreeGen.flatCtors[0]).toPattern).MatchesS
      ((([.bvar 1, .bvar 2, .bvar 3, .bvar 4,
          .bvar 5, .bvar 6, .bvar 7, .bvar 8] : List SExpr).foldr
          (fun (a f : SExpr) => f.app a) (SExpr.const ``Tree.rec [u, l])).app
        (([.bvar 0, .bvar 8] : List SExpr).foldr
          (fun (a f : SExpr) => f.app a) (SExpr.const ``Tree.leaf [l])))
        [u, l] mcap := by
    rw [d2LeafRuleLhsBodyV_eq] at H
    simpa [mkInst_appN, SExpr.mkInst, d2InstVParamZero,
      d2InstVParamOne] using H
  cases H' with
  | app hrec hctor =>
    rename_i recCap ctorCap
    obtain ⟨-, -, hrecValues⟩ := ParamsD0.matchesS_varN_foldr hrec
    obtain ⟨-, -, hctorValues⟩ := ParamsD0.matchesS_varN_foldr hctor
    have hr := congrArg List.head? hrecValues
    have hc := congrArg List.head? hctorValues
    change some (_ : SExpr) = some (.bvar 8) at hr hc
    simp only [Option.some.injEq] at hr hc
    rw [d2LeafCheckShape]
    change [(ctorCap (some none),
      recCap (some (some (some (some (some (some (some none))))))))] = _
    rw [hc, hr]

theorem d2NodeCaptureValues (univs : Nat)
    (u l : @SLevel (d2Params univs))
    {mcap : ((TreeGen.rulePattern TreeGen.flatCtors[1]).toPattern).Path →
      @SExpr (d2Params univs)}
    (H : @Pattern.MatchesS (d2Params univs)
      ((TreeGen.rulePattern TreeGen.flatCtors[1]).toPattern)
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.ruleLhsBody TreeGen.flatCtors[1])) [u, l] mcap) :
    letI : Params := d2Params univs
    (treeCapturePaths TreeGen.flatCtors[1]).map mcap =
      [.bvar 8, .bvar 7, .bvar 6, .bvar 5, .bvar 4,
        .bvar 3, .bvar 2, .bvar 1, .bvar 0] := by
  letI : Params := d2Params univs
  have H' : ((TreeGen.rulePattern TreeGen.flatCtors[1]).toPattern).MatchesS
      ((([.bvar 1, .bvar 2, .bvar 3, .bvar 4,
          .bvar 5, .bvar 6, .bvar 7, .bvar 8] : List SExpr).foldr
          (fun (a f : SExpr) => f.app a) (SExpr.const ``Tree.rec [u, l])).app
        (([.bvar 0, .bvar 8] : List SExpr).foldr
          (fun (a f : SExpr) => f.app a) (SExpr.const ``Tree.node [l])))
        [u, l] mcap := by
    rw [d2NodeRuleLhsBodyV_eq] at H
    simpa [mkInst_appN, SExpr.mkInst, d2InstVParamZero,
      d2InstVParamOne] using H
  have hcaps := d2TreeCaptureValues univs H'
  simpa using hcaps

theorem d2NodeCheckShape (univs : Nat)
    (u l : @SLevel (d2Params univs))
    (mcap : ((TreeGen.rulePattern TreeGen.flatCtors[1]).toPattern).Path →
      @SExpr (d2Params univs)) :
    letI : Params := d2Params univs
    (TreeGen.ruleCheck treeRuleClosure
      (List.mem_of_getElem? (show TreeGen.flatCtors[1]? =
        some TreeGen.flatCtors[1] from rfl))).defeqsS [u, l] mcap =
      [(mcap (.inr (some none)),
        mcap (.inl (some (some (some (some (some (some (some none)))))))))] := by
  rfl

theorem d2NodeCheckDefeqs (univs : Nat)
    (u l : @SLevel (d2Params univs))
    {mcap : ((TreeGen.rulePattern TreeGen.flatCtors[1]).toPattern).Path →
      @SExpr (d2Params univs)}
    (H : @Pattern.MatchesS (d2Params univs)
      ((TreeGen.rulePattern TreeGen.flatCtors[1]).toPattern)
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.ruleLhsBody TreeGen.flatCtors[1])) [u, l] mcap) :
    letI : Params := d2Params univs
    (TreeGen.ruleCheck treeRuleClosure
      (List.mem_of_getElem? (show TreeGen.flatCtors[1]? =
        some TreeGen.flatCtors[1] from rfl))).defeqsS [u, l] mcap =
      [(.bvar 8, .bvar 8)] := by
  letI : Params := d2Params univs
  have H' : ((TreeGen.rulePattern TreeGen.flatCtors[1]).toPattern).MatchesS
      ((([.bvar 1, .bvar 2, .bvar 3, .bvar 4,
          .bvar 5, .bvar 6, .bvar 7, .bvar 8] : List SExpr).foldr
          (fun (a f : SExpr) => f.app a) (SExpr.const ``Tree.rec [u, l])).app
        (([.bvar 0, .bvar 8] : List SExpr).foldr
          (fun (a f : SExpr) => f.app a) (SExpr.const ``Tree.node [l])))
        [u, l] mcap := by
    rw [d2NodeRuleLhsBodyV_eq] at H
    simpa [mkInst_appN, SExpr.mkInst, d2InstVParamZero,
      d2InstVParamOne] using H
  cases H' with
  | app hrec hctor =>
    rename_i recCap ctorCap
    obtain ⟨-, -, hrecValues⟩ := ParamsD0.matchesS_varN_foldr hrec
    obtain ⟨-, -, hctorValues⟩ := ParamsD0.matchesS_varN_foldr hctor
    have hr := congrArg List.head? hrecValues
    have hc := congrArg List.head? hctorValues
    change some (_ : SExpr) = some (.bvar 8) at hr hc
    simp only [Option.some.injEq] at hr hc
    rw [d2NodeCheckShape]
    change [(ctorCap (some none),
      recCap (some (some (some (some (some (some (some none))))))))] = _
    rw [hc, hr]

theorem d2BranchCaptureValues (univs : Nat)
    (u l : @SLevel (d2Params univs))
    {mcap : ((TreeGen.rulePattern TreeGen.flatCtors[2]).toPattern).Path →
      @SExpr (d2Params univs)}
    (H : @Pattern.MatchesS (d2Params univs)
      ((TreeGen.rulePattern TreeGen.flatCtors[2]).toPattern)
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.ruleLhsBody TreeGen.flatCtors[2])) [u, l] mcap) :
    letI : Params := d2Params univs
    (treeCapturePaths TreeGen.flatCtors[2]).map mcap =
      [.bvar 8, .bvar 7, .bvar 6, .bvar 5, .bvar 4,
        .bvar 3, .bvar 2, .bvar 1, .bvar 0] := by
  letI : Params := d2Params univs
  have H' : ((TreeGen.rulePattern TreeGen.flatCtors[2]).toPattern).MatchesS
      ((([.bvar 1, .bvar 2, .bvar 3, .bvar 4,
          .bvar 5, .bvar 6, .bvar 7, .bvar 8] : List SExpr).foldr
          (fun (a f : SExpr) => f.app a) (SExpr.const ``Tree.rec [u, l])).app
        (([.bvar 0, .bvar 8] : List SExpr).foldr
          (fun (a f : SExpr) => f.app a) (SExpr.const ``Tree.branch [l])))
        [u, l] mcap := by
    rw [d2BranchRuleLhsBodyV_eq] at H
    simpa [mkInst_appN, SExpr.mkInst, d2InstVParamZero,
      d2InstVParamOne] using H
  have hcaps := d2TreeCaptureValues univs H'
  simpa using hcaps

theorem d2BranchCheckShape (univs : Nat)
    (u l : @SLevel (d2Params univs))
    (mcap : ((TreeGen.rulePattern TreeGen.flatCtors[2]).toPattern).Path →
      @SExpr (d2Params univs)) :
    letI : Params := d2Params univs
    (TreeGen.ruleCheck treeRuleClosure
      (List.mem_of_getElem? (show TreeGen.flatCtors[2]? =
        some TreeGen.flatCtors[2] from rfl))).defeqsS [u, l] mcap =
      [(mcap (.inr (some none)),
        mcap (.inl (some (some (some (some (some (some (some none)))))))))] := by
  rfl

theorem d2BranchCheckDefeqs (univs : Nat)
    (u l : @SLevel (d2Params univs))
    {mcap : ((TreeGen.rulePattern TreeGen.flatCtors[2]).toPattern).Path →
      @SExpr (d2Params univs)}
    (H : @Pattern.MatchesS (d2Params univs)
      ((TreeGen.rulePattern TreeGen.flatCtors[2]).toPattern)
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.ruleLhsBody TreeGen.flatCtors[2])) [u, l] mcap) :
    letI : Params := d2Params univs
    (TreeGen.ruleCheck treeRuleClosure
      (List.mem_of_getElem? (show TreeGen.flatCtors[2]? =
        some TreeGen.flatCtors[2] from rfl))).defeqsS [u, l] mcap =
      [(.bvar 8, .bvar 8)] := by
  letI : Params := d2Params univs
  have H' : ((TreeGen.rulePattern TreeGen.flatCtors[2]).toPattern).MatchesS
      ((([.bvar 1, .bvar 2, .bvar 3, .bvar 4,
          .bvar 5, .bvar 6, .bvar 7, .bvar 8] : List SExpr).foldr
          (fun (a f : SExpr) => f.app a) (SExpr.const ``Tree.rec [u, l])).app
        (([.bvar 0, .bvar 8] : List SExpr).foldr
          (fun (a f : SExpr) => f.app a) (SExpr.const ``Tree.branch [l])))
        [u, l] mcap := by
    rw [d2BranchRuleLhsBodyV_eq] at H
    simpa [mkInst_appN, SExpr.mkInst, d2InstVParamZero,
      d2InstVParamOne] using H
  cases H' with
  | app hrec hctor =>
    rename_i recCap ctorCap
    obtain ⟨-, -, hrecValues⟩ := ParamsD0.matchesS_varN_foldr hrec
    obtain ⟨-, -, hctorValues⟩ := ParamsD0.matchesS_varN_foldr hctor
    have hr := congrArg List.head? hrecValues
    have hc := congrArg List.head? hctorValues
    change some (_ : SExpr) = some (.bvar 8) at hr hc
    simp only [Option.some.injEq] at hr hc
    rw [d2BranchCheckShape]
    change [(ctorCap (some none),
      recCap (some (some (some (some (some (some (some none))))))))] = _
    rw [hc, hr]

theorem d2NilCaptureValues (univs : Nat)
    (u l : @SLevel (d2Params univs))
    {mcap : ((TreeGen.rulePattern TreeGen.flatCtors[3]).toPattern).Path →
      @SExpr (d2Params univs)}
    (H : @Pattern.MatchesS (d2Params univs)
      ((TreeGen.rulePattern TreeGen.flatCtors[3]).toPattern)
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.ruleLhsBody TreeGen.flatCtors[3])) [u, l] mcap) :
    letI : Params := d2Params univs
    (treeCapturePaths TreeGen.flatCtors[3]).map mcap =
      [.bvar 7, .bvar 6, .bvar 5, .bvar 4,
        .bvar 3, .bvar 2, .bvar 1, .bvar 0] := by
  letI : Params := d2Params univs
  have H' : ((TreeGen.rulePattern TreeGen.flatCtors[3]).toPattern).MatchesS
      ((([.bvar 0, .bvar 1, .bvar 2, .bvar 3,
          .bvar 4, .bvar 5, .bvar 6, .bvar 7] : List SExpr).foldr
          (fun (a f : SExpr) => f.app a)
          (SExpr.const ``TreeList.rec [u, l])).app
        (([.bvar 7] : List SExpr).foldr
          (fun (a f : SExpr) => f.app a) (SExpr.const ``TreeList.nil [l])))
        [u, l] mcap := by
    rw [d2NilRuleLhsBodyV_eq] at H
    simpa [mkInst_appN, SExpr.mkInst, d2InstVParamZero,
      d2InstVParamOne] using H
  have hcaps := d2TreeCaptureValues univs H'
  simpa using hcaps

theorem d2NilCheckShape (univs : Nat)
    (u l : @SLevel (d2Params univs))
    (mcap : ((TreeGen.rulePattern TreeGen.flatCtors[3]).toPattern).Path →
      @SExpr (d2Params univs)) :
    letI : Params := d2Params univs
    (TreeGen.ruleCheck treeRuleClosure
      (List.mem_of_getElem? (show TreeGen.flatCtors[3]? =
        some TreeGen.flatCtors[3] from rfl))).defeqsS [u, l] mcap =
      [(mcap (.inr none),
        mcap (.inl (some (some (some (some (some (some (some none)))))))))] := by
  rfl

theorem d2NilCheckDefeqs (univs : Nat)
    (u l : @SLevel (d2Params univs))
    {mcap : ((TreeGen.rulePattern TreeGen.flatCtors[3]).toPattern).Path →
      @SExpr (d2Params univs)}
    (H : @Pattern.MatchesS (d2Params univs)
      ((TreeGen.rulePattern TreeGen.flatCtors[3]).toPattern)
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.ruleLhsBody TreeGen.flatCtors[3])) [u, l] mcap) :
    letI : Params := d2Params univs
    (TreeGen.ruleCheck treeRuleClosure
      (List.mem_of_getElem? (show TreeGen.flatCtors[3]? =
        some TreeGen.flatCtors[3] from rfl))).defeqsS [u, l] mcap =
      [(.bvar 7, .bvar 7)] := by
  letI : Params := d2Params univs
  have H' : ((TreeGen.rulePattern TreeGen.flatCtors[3]).toPattern).MatchesS
      ((([.bvar 0, .bvar 1, .bvar 2, .bvar 3,
          .bvar 4, .bvar 5, .bvar 6, .bvar 7] : List SExpr).foldr
          (fun (a f : SExpr) => f.app a)
          (SExpr.const ``TreeList.rec [u, l])).app
        (([.bvar 7] : List SExpr).foldr
          (fun (a f : SExpr) => f.app a) (SExpr.const ``TreeList.nil [l])))
        [u, l] mcap := by
    rw [d2NilRuleLhsBodyV_eq] at H
    simpa [mkInst_appN, SExpr.mkInst, d2InstVParamZero,
      d2InstVParamOne] using H
  cases H' with
  | app hrec hctor =>
    rename_i recCap ctorCap
    obtain ⟨-, -, hrecValues⟩ := ParamsD0.matchesS_varN_foldr hrec
    obtain ⟨-, -, hctorValues⟩ := ParamsD0.matchesS_varN_foldr hctor
    have hr := congrArg List.head? hrecValues
    have hc := congrArg List.head? hctorValues
    change some (_ : SExpr) = some (.bvar 7) at hr hc
    simp only [Option.some.injEq] at hr hc
    rw [d2NilCheckShape]
    change [(ctorCap none,
      recCap (some (some (some (some (some (some (some none))))))))] = _
    rw [hc, hr]

theorem d2ConsCaptureValues (univs : Nat)
    (u l : @SLevel (d2Params univs))
    {mcap : ((TreeGen.rulePattern TreeGen.flatCtors[4]).toPattern).Path →
      @SExpr (d2Params univs)}
    (H : @Pattern.MatchesS (d2Params univs)
      ((TreeGen.rulePattern TreeGen.flatCtors[4]).toPattern)
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.ruleLhsBody TreeGen.flatCtors[4])) [u, l] mcap) :
    letI : Params := d2Params univs
    (treeCapturePaths TreeGen.flatCtors[4]).map mcap =
      [.bvar 9, .bvar 8, .bvar 7, .bvar 6, .bvar 5,
        .bvar 4, .bvar 3, .bvar 2, .bvar 1, .bvar 0] := by
  letI : Params := d2Params univs
  have H' : ((TreeGen.rulePattern TreeGen.flatCtors[4]).toPattern).MatchesS
      ((([.bvar 2, .bvar 3, .bvar 4, .bvar 5,
          .bvar 6, .bvar 7, .bvar 8, .bvar 9] : List SExpr).foldr
          (fun (a f : SExpr) => f.app a)
          (SExpr.const ``TreeList.rec [u, l])).app
        (([.bvar 0, .bvar 1, .bvar 9] : List SExpr).foldr
          (fun (a f : SExpr) => f.app a)
          (SExpr.const ``TreeList.cons [l]))) [u, l] mcap := by
    rw [d2ConsRuleLhsBodyV_eq] at H
    simpa [mkInst_appN, SExpr.mkInst, d2InstVParamZero,
      d2InstVParamOne] using H
  have hcaps := d2TreeCaptureValues univs H'
  simpa using hcaps

theorem d2ConsCheckShape (univs : Nat)
    (u l : @SLevel (d2Params univs))
    (mcap : ((TreeGen.rulePattern TreeGen.flatCtors[4]).toPattern).Path →
      @SExpr (d2Params univs)) :
    letI : Params := d2Params univs
    (TreeGen.ruleCheck treeRuleClosure
      (List.mem_of_getElem? (show TreeGen.flatCtors[4]? =
        some TreeGen.flatCtors[4] from rfl))).defeqsS [u, l] mcap =
      [(mcap (.inr (some (some none))),
        mcap (.inl (some (some (some (some (some (some (some none)))))))))] := by
  rfl

theorem d2ConsCheckDefeqs (univs : Nat)
    (u l : @SLevel (d2Params univs))
    {mcap : ((TreeGen.rulePattern TreeGen.flatCtors[4]).toPattern).Path →
      @SExpr (d2Params univs)}
    (H : @Pattern.MatchesS (d2Params univs)
      ((TreeGen.rulePattern TreeGen.flatCtors[4]).toPattern)
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.ruleLhsBody TreeGen.flatCtors[4])) [u, l] mcap) :
    letI : Params := d2Params univs
    (TreeGen.ruleCheck treeRuleClosure
      (List.mem_of_getElem? (show TreeGen.flatCtors[4]? =
        some TreeGen.flatCtors[4] from rfl))).defeqsS [u, l] mcap =
      [(.bvar 9, .bvar 9)] := by
  letI : Params := d2Params univs
  have H' : ((TreeGen.rulePattern TreeGen.flatCtors[4]).toPattern).MatchesS
      ((([.bvar 2, .bvar 3, .bvar 4, .bvar 5,
          .bvar 6, .bvar 7, .bvar 8, .bvar 9] : List SExpr).foldr
          (fun (a f : SExpr) => f.app a)
          (SExpr.const ``TreeList.rec [u, l])).app
        (([.bvar 0, .bvar 1, .bvar 9] : List SExpr).foldr
          (fun (a f : SExpr) => f.app a)
          (SExpr.const ``TreeList.cons [l]))) [u, l] mcap := by
    rw [d2ConsRuleLhsBodyV_eq] at H
    simpa [mkInst_appN, SExpr.mkInst, d2InstVParamZero,
      d2InstVParamOne] using H
  cases H' with
  | app hrec hctor =>
    rename_i recCap ctorCap
    obtain ⟨-, -, hrecValues⟩ := ParamsD0.matchesS_varN_foldr hrec
    obtain ⟨-, -, hctorValues⟩ := ParamsD0.matchesS_varN_foldr hctor
    have hr := congrArg List.head? hrecValues
    have hc := congrArg List.head? hctorValues
    change some (_ : SExpr) = some (.bvar 9) at hr hc
    simp only [Option.some.injEq] at hr hc
    rw [d2ConsCheckShape]
    change [(ctorCap (some (some none)),
      recCap (some (some (some (some (some (some (some none))))))))] = _
    rw [hc, hr]

/-- A canonical capture inventory applies the registered RHS tower exactly
as `applyTelVars`; closedness removes the otherwise visible head lift. -/
theorem d2RuleRhsApply_eq_applyTelVars (univs : Nat)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (hentry : TreeGen.flatCtors[i]? = some constructor)
    (u l : @SLevel (d2Params univs))
    {mcap : ((TreeGen.rulePattern constructor).toPattern).Path →
      @SExpr (d2Params univs)}
    (hcaps : letI : Params := d2Params univs
      (treeCapturePaths constructor).map mcap =
        telBvars (TreeGen.ruleBinders constructor).length) :
    letI : Params := d2Params univs
    (TreeGen.ruleRHS treeRuleClosure hentry).applyS [u, l] mcap =
      applyTelVars
        ((TreeGen.ruleBinders constructor).map (SExpr.mkInst [u, l]))
        (SExpr.mkInst [u, l] (TreeGen.rule i constructor).rhs) := by
  letI : Params := d2Params univs
  have hclosed := (treeRuleClosure.rhs_closed hentry).mkInstS (ls := [u, l])
  rw [treeRuleRHS_capture_tower hentry, Pattern.RHS.appN_applyS]
  rw [List.foldl_map]
  simp only [Pattern.RHS.applyS]
  rw [← List.foldl_map]
  rw [hcaps, applyTelVars_eq_foldl, List.length_map,
    hclosed.lift'_eq .zero]

/-- The shared parameter remains a typed canonical variable after opening
an arbitrary generated rule's constructor-field suffix. -/
theorem d2RuleAlphaStrong (univs : Nat)
    (u l : @SLevel (d2Params univs))
    {i : Nat} {constructor : NormalizedBlockCtor}
    {Gamma : List (@SExpr (d2Params univs))}
    (hRhs : @IsDefEqStrong (d2Params univs) Gamma
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.rule i constructor).rhs)
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.rule i constructor).rhs)
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.rule i constructor).type)) :
    letI : Params := d2Params univs
    let As := (TreeGen.ruleBinders constructor).map (SExpr.mkInst [u, l])
    IsDefEqStrong (As.reverse ++ Gamma)
      (.bvar (7 + (d2FieldBinders [u, l] constructor).length))
      (.bvar (7 + (d2FieldBinders [u, l] constructor).length))
      (.sort l.succ) := by
  letI : Params := d2Params univs
  let Common := d2CommonBinders [u, l]
  let Fields := d2FieldBinders [u, l] constructor
  let Delta := Common.reverse ++ Gamma
  have hCommon := d2CommonTelescopeStrong univs hRhs
  change StrongTelescope Gamma Common at hCommon
  have hAlpha := d2CommonAlphaStrong univs u l hCommon
  let W : Ctx.Lift' (.skipN .refl Fields.reverse.length) Delta
      (Fields.reverse ++ Delta) := Ctx.Lift'.skipAppend Fields.reverse
  have hAlpha' := d2StrongWeak univs W hAlpha
  rw [d2RuleBinders_eq]
  simpa [Common, Fields, Delta, List.reverse_append, List.append_assoc,
    Lift.liftVar_skipN, SExpr.lift'] using hAlpha'

/-- Package one literal generated body once its strong typing, canonical
match, capture order, and reflexive parameter check have been exposed. -/
theorem d2RegisteredLiteral (univs : Nat)
    {i alphaIndex : Nat} {constructor : NormalizedBlockCtor}
    (hentry : TreeGen.flatCtors[i]? = some constructor)
    (u l : @SLevel (d2Params univs))
    {Gamma : List (@SExpr (d2Params univs))}
    (hRhs : @IsDefEqStrong (d2Params univs) Gamma
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.rule i constructor).rhs)
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.rule i constructor).rhs)
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.rule i constructor).type))
    (hLeft : letI : Params := d2Params univs
      let As := (TreeGen.ruleBinders constructor).map (SExpr.mkInst [u, l])
      IsDefEqStrong (As.reverse ++ Gamma)
        (SExpr.mkInst [u, l] (TreeGen.ruleLhsBody constructor))
        (SExpr.mkInst [u, l] (TreeGen.ruleLhsBody constructor))
        (SExpr.mkInst [u, l] (d2RuleResult constructor)))
    {mcap : ((TreeGen.rulePattern constructor).toPattern).Path →
      @SExpr (d2Params univs)}
    (hmatch : @Pattern.MatchesS (d2Params univs)
      ((TreeGen.rulePattern constructor).toPattern)
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.ruleLhsBody constructor)) [u, l] mcap)
    (hcaps : letI : Params := d2Params univs
      (treeCapturePaths constructor).map mcap =
        telBvars (TreeGen.ruleBinders constructor).length)
    (hchecks : letI : Params := d2Params univs
      (TreeGen.ruleCheck treeRuleClosure
        (List.mem_of_getElem? hentry)).defeqsS [u, l] mcap =
          [(.bvar alphaIndex, .bvar alphaIndex)])
    (hAlpha : letI : Params := d2Params univs
      let As := (TreeGen.ruleBinders constructor).map (SExpr.mkInst [u, l])
      IsDefEqStrong (As.reverse ++ Gamma)
        (.bvar alphaIndex) (.bvar alphaIndex) (.sort l.succ)) :
    letI : Params := d2Params univs
    let As := (TreeGen.ruleBinders constructor).map (SExpr.mkInst [u, l])
    IsDefEqStrong (As.reverse ++ Gamma)
      (SExpr.mkInst [u, l] (TreeGen.ruleLhsBody constructor))
      (applyTelVars As (SExpr.mkInst [u, l]
        (TreeGen.rule i constructor).rhs))
      (SExpr.mkInst [u, l] (d2RuleResult constructor)) := by
  letI : Params := d2Params univs
  let As := (TreeGen.ruleBinders constructor).map (SExpr.mkInst [u, l])
  have hlhs : SExpr.mkInst [u, l] (TreeGen.rule i constructor).lhs =
      lamTel As (SExpr.mkInst [u, l]
        (TreeGen.ruleLhsBody constructor)) := by
    rw [TreeGen.rule_lhs, mkInst_lamN]
  have htype : SExpr.mkInst [u, l] (TreeGen.rule i constructor).type =
      As.foldr .forallE (SExpr.mkInst [u, l]
        (d2RuleResult constructor)) := by
    rw [TreeGen.rule_type, mkInst_forallN]
    rfl
  have happly := d2RuleRhsApply_eq_applyTelVars univs hentry u l hcaps
  apply registeredBody_strong (fun W H => d2StrongWeak univs W H)
    (treeRule_registered hentry) (by rfl) hlhs htype hRhs hLeft
    (d2Pat_block_rule hentry) hmatch happly
    [(.sort l.succ, .bvar alphaIndex, .bvar alphaIndex)]
  · simp [hchecks]
  · intro a b T hmem
    have heq := List.mem_singleton.mp hmem
    cases heq
    exact hAlpha.defeq

/-- The opened left body of the literal `Tree.leaf` rule is strongly typed. -/
theorem d2TreeLeafLhsBodyStrong (univs : Nat)
    (u l : @SLevel (d2Params univs))
    {Gamma : List (@SExpr (d2Params univs))}
    (hRhs : @IsDefEqStrong (d2Params univs) Gamma
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.rule 0 TreeGen.flatCtors[0]).rhs)
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.rule 0 TreeGen.flatCtors[0]).rhs)
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.rule 0 TreeGen.flatCtors[0]).type)) :
    letI : Params := d2Params univs
    let As := (TreeGen.ruleBinders TreeGen.flatCtors[0]).map
      (SExpr.mkInst [u, l])
    IsDefEqStrong (As.reverse ++ Gamma)
      (SExpr.mkInst [u, l] (TreeGen.ruleLhsBody TreeGen.flatCtors[0]))
      (SExpr.mkInst [u, l] (TreeGen.ruleLhsBody TreeGen.flatCtors[0]))
      (SExpr.mkInst [u, l] (d2RuleResult TreeGen.flatCtors[0])) := by
  letI : Params := d2Params univs
  let Common := d2CommonBinders [u, l]
  let Delta := Common.reverse ++ Gamma
  have hCommon := d2CommonTelescopeStrong univs hRhs
  change StrongTelescope Gamma Common at hCommon
  have hFields := d2FieldTelescopeStrong univs hRhs
  have hField : StrongTelescope Delta [SExpr.bvar 7] := by
    simpa [Delta, Common, d2FieldBinders, d2LeafFieldBindersV_eq,
      SExpr.mkInst] using hFields
  have hx0 := hField.head_bvar (fun W H => d2StrongWeak univs W H)
  have hx : IsDefEqStrong (SExpr.bvar 7 :: Delta)
      (.bvar 0) (.bvar 0) (.bvar 8) := by
    simpa [SExpr.lift] using hx0
  let W : Ctx.Lift' (.skip .refl) Delta (.bvar 7 :: Delta) := .skip .refl
  have hAlpha : IsDefEqStrong (.bvar 7 :: Delta)
      (.bvar 8) (.bvar 8) (.sort l.succ) := by
    simpa [SExpr.lift] using
      d2StrongWeak univs W (d2CommonAlphaStrong univs u l hCommon)
  have hMotive : IsDefEqStrong (.bvar 7 :: Delta)
      (.bvar 7) (.bvar 7)
      (.forallE ((SExpr.const ``Tree [l]).app (.bvar 8)) (.sort u)) := by
    simpa [SExpr.lift] using
      d2StrongWeak univs W (d2CommonTreeMotiveStrong univs u l hCommon)
  have hRec : IsDefEqStrong (.bvar 7 :: Delta)
      (applyTelVars Common (.const ``Tree.rec [u, l])).lift
      (applyTelVars Common (.const ``Tree.rec [u, l])).lift
      (.forallE ((SExpr.const ``Tree [l]).app (.bvar 8))
        ((SExpr.bvar 8).app (.bvar 0))) := by
    simpa [Delta, Common, d2TreeRecTailV, SExpr.mkInst,
      d2InstVParamOne, SExpr.lift, SExpr.lift'] using
      d2StrongWeak univs W (d2TreeRecCommonStrong univs u l hCommon)
  have hMajor := d2TreeLeafMajorStrong univs l hAlpha hx
  have hBody := d2TreeRecApplyStrong univs u l hAlpha hMotive hRec hMajor
  dsimp only [Common] at hBody
  rw [d2TreeRecCommonTerm_eq] at hBody
  rw [d2RuleBinders_eq, d2LeafRuleLhsBodyV_eq, d2LeafRuleResultV_eq]
  simpa [d2FieldBinders, d2LeafFieldBindersV_eq, Delta,
    d2TreeRecCommonTerm, mkInst_appN, SExpr.mkInst, d2InstVParamZero,
    d2InstVParamOne, SExpr.lift] using hBody

/-- The opened left body of the literal `Tree.node` rule is strongly typed. -/
theorem d2TreeNodeLhsBodyStrong (univs : Nat)
    (u l : @SLevel (d2Params univs))
    {Gamma : List (@SExpr (d2Params univs))}
    (hRhs : @IsDefEqStrong (d2Params univs) Gamma
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.rule 1 TreeGen.flatCtors[1]).rhs)
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.rule 1 TreeGen.flatCtors[1]).rhs)
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.rule 1 TreeGen.flatCtors[1]).type)) :
    letI : Params := d2Params univs
    let As := (TreeGen.ruleBinders TreeGen.flatCtors[1]).map
      (SExpr.mkInst [u, l])
    IsDefEqStrong (As.reverse ++ Gamma)
      (SExpr.mkInst [u, l] (TreeGen.ruleLhsBody TreeGen.flatCtors[1]))
      (SExpr.mkInst [u, l] (TreeGen.ruleLhsBody TreeGen.flatCtors[1]))
      (SExpr.mkInst [u, l] (d2RuleResult TreeGen.flatCtors[1])) := by
  letI : Params := d2Params univs
  let Common := d2CommonBinders [u, l]
  let Delta := Common.reverse ++ Gamma
  let Field := (SExpr.const ``TreeList [l]).app (.bvar 7)
  have hCommon := d2CommonTelescopeStrong univs hRhs
  change StrongTelescope Gamma Common at hCommon
  have hFields := d2FieldTelescopeStrong univs hRhs
  have hField : StrongTelescope Delta [Field] := by
    simpa [Delta, Common, Field, d2FieldBinders,
      d2NodeFieldBindersV_eq, SExpr.mkInst, d2InstVParamOne] using hFields
  have hxs0 := hField.head_bvar (fun W H => d2StrongWeak univs W H)
  have hxs : IsDefEqStrong (Field :: Delta)
      (.bvar 0) (.bvar 0)
      ((SExpr.const ``TreeList [l]).app (.bvar 8)) := by
    simpa [Field, SExpr.lift] using hxs0
  let W : Ctx.Lift' (.skip .refl) Delta (Field :: Delta) := .skip .refl
  have hAlpha : IsDefEqStrong (Field :: Delta)
      (.bvar 8) (.bvar 8) (.sort l.succ) := by
    simpa [Field, SExpr.lift] using
      d2StrongWeak univs W (d2CommonAlphaStrong univs u l hCommon)
  have hMotive : IsDefEqStrong (Field :: Delta)
      (.bvar 7) (.bvar 7)
      (.forallE ((SExpr.const ``Tree [l]).app (.bvar 8)) (.sort u)) := by
    simpa [Field, SExpr.lift] using
      d2StrongWeak univs W (d2CommonTreeMotiveStrong univs u l hCommon)
  have hRec : IsDefEqStrong (Field :: Delta)
      (applyTelVars Common (.const ``Tree.rec [u, l])).lift
      (applyTelVars Common (.const ``Tree.rec [u, l])).lift
      (.forallE ((SExpr.const ``Tree [l]).app (.bvar 8))
        ((SExpr.bvar 8).app (.bvar 0))) := by
    simpa [Delta, Common, Field, d2TreeRecTailV, SExpr.mkInst,
      d2InstVParamOne, SExpr.lift, SExpr.lift'] using
      d2StrongWeak univs W (d2TreeRecCommonStrong univs u l hCommon)
  have hMajor := d2TreeNodeMajorStrong univs l hAlpha hxs
  have hBody := d2TreeRecApplyStrong univs u l hAlpha hMotive hRec hMajor
  dsimp only [Common] at hBody
  rw [d2TreeRecCommonTerm_eq] at hBody
  rw [d2RuleBinders_eq, d2NodeRuleLhsBodyV_eq, d2NodeRuleResultV_eq]
  simpa [d2FieldBinders, d2NodeFieldBindersV_eq, Delta, Field,
    d2TreeRecCommonTerm, mkInst_appN, SExpr.mkInst, d2InstVParamZero,
    d2InstVParamOne, SExpr.lift] using hBody

/-- The opened left body of the higher-order `Tree.branch` rule. -/
theorem d2TreeBranchLhsBodyStrong (univs : Nat)
    (u l : @SLevel (d2Params univs))
    {Gamma : List (@SExpr (d2Params univs))}
    (hRhs : @IsDefEqStrong (d2Params univs) Gamma
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.rule 2 TreeGen.flatCtors[2]).rhs)
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.rule 2 TreeGen.flatCtors[2]).rhs)
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.rule 2 TreeGen.flatCtors[2]).type)) :
    letI : Params := d2Params univs
    let As := (TreeGen.ruleBinders TreeGen.flatCtors[2]).map
      (SExpr.mkInst [u, l])
    IsDefEqStrong (As.reverse ++ Gamma)
      (SExpr.mkInst [u, l] (TreeGen.ruleLhsBody TreeGen.flatCtors[2]))
      (SExpr.mkInst [u, l] (TreeGen.ruleLhsBody TreeGen.flatCtors[2]))
      (SExpr.mkInst [u, l] (d2RuleResult TreeGen.flatCtors[2])) := by
  letI : Params := d2Params univs
  let Common := d2CommonBinders [u, l]
  let Delta := Common.reverse ++ Gamma
  let Field := SExpr.forallE (.bvar 7)
    ((SExpr.const ``TreeList [l]).app (.bvar 8))
  have hCommon := d2CommonTelescopeStrong univs hRhs
  change StrongTelescope Gamma Common at hCommon
  have hFields := d2FieldTelescopeStrong univs hRhs
  have hField : StrongTelescope Delta [Field] := by
    simpa [Delta, Common, Field, d2FieldBinders,
      d2BranchFieldBindersV_eq, SExpr.mkInst, d2InstVParamOne] using hFields
  have hf0 := hField.head_bvar (fun W H => d2StrongWeak univs W H)
  have hf : IsDefEqStrong (Field :: Delta)
      (.bvar 0) (.bvar 0)
      (.forallE (.bvar 8)
        ((SExpr.const ``TreeList [l]).app (.bvar 9))) := by
    simpa [Field, SExpr.lift] using hf0
  let W : Ctx.Lift' (.skip .refl) Delta (Field :: Delta) := .skip .refl
  have hAlpha : IsDefEqStrong (Field :: Delta)
      (.bvar 8) (.bvar 8) (.sort l.succ) := by
    simpa [Field, SExpr.lift] using
      d2StrongWeak univs W (d2CommonAlphaStrong univs u l hCommon)
  have hMotive : IsDefEqStrong (Field :: Delta)
      (.bvar 7) (.bvar 7)
      (.forallE ((SExpr.const ``Tree [l]).app (.bvar 8)) (.sort u)) := by
    simpa [Field, SExpr.lift] using
      d2StrongWeak univs W (d2CommonTreeMotiveStrong univs u l hCommon)
  have hRec : IsDefEqStrong (Field :: Delta)
      (applyTelVars Common (.const ``Tree.rec [u, l])).lift
      (applyTelVars Common (.const ``Tree.rec [u, l])).lift
      (.forallE ((SExpr.const ``Tree [l]).app (.bvar 8))
        ((SExpr.bvar 8).app (.bvar 0))) := by
    simpa [Delta, Common, Field, d2TreeRecTailV, SExpr.mkInst,
      d2InstVParamOne, SExpr.lift, SExpr.lift'] using
      d2StrongWeak univs W (d2TreeRecCommonStrong univs u l hCommon)
  have hMajor := d2TreeBranchMajorStrong univs l hAlpha hf
  have hBody := d2TreeRecApplyStrong univs u l hAlpha hMotive hRec hMajor
  dsimp only [Common] at hBody
  rw [d2TreeRecCommonTerm_eq] at hBody
  rw [d2RuleBinders_eq, d2BranchRuleLhsBodyV_eq,
    d2BranchRuleResultV_eq]
  simpa [d2FieldBinders, d2BranchFieldBindersV_eq, Delta, Field,
    d2TreeRecCommonTerm, mkInst_appN, SExpr.mkInst, d2InstVParamZero,
    d2InstVParamOne, SExpr.lift] using hBody

/-- The opened left body of the nullary `TreeList.nil` rule. -/
theorem d2TreeListNilLhsBodyStrong (univs : Nat)
    (u l : @SLevel (d2Params univs))
    {Gamma : List (@SExpr (d2Params univs))}
    (hRhs : @IsDefEqStrong (d2Params univs) Gamma
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.rule 3 TreeGen.flatCtors[3]).rhs)
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.rule 3 TreeGen.flatCtors[3]).rhs)
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.rule 3 TreeGen.flatCtors[3]).type)) :
    letI : Params := d2Params univs
    let As := (TreeGen.ruleBinders TreeGen.flatCtors[3]).map
      (SExpr.mkInst [u, l])
    IsDefEqStrong (As.reverse ++ Gamma)
      (SExpr.mkInst [u, l] (TreeGen.ruleLhsBody TreeGen.flatCtors[3]))
      (SExpr.mkInst [u, l] (TreeGen.ruleLhsBody TreeGen.flatCtors[3]))
      (SExpr.mkInst [u, l] (d2RuleResult TreeGen.flatCtors[3])) := by
  letI : Params := d2Params univs
  let Common := d2CommonBinders [u, l]
  let Delta := Common.reverse ++ Gamma
  have hCommon := d2CommonTelescopeStrong univs hRhs
  change StrongTelescope Gamma Common at hCommon
  have hAlpha := d2CommonAlphaStrong univs u l hCommon
  have hMotive := d2CommonTreeListMotiveStrong univs u l hCommon
  have hRec : IsDefEqStrong Delta
      (applyTelVars Common (.const ``TreeList.rec [u, l]))
      (applyTelVars Common (.const ``TreeList.rec [u, l]))
      (.forallE ((SExpr.const ``TreeList [l]).app (.bvar 7))
        ((SExpr.bvar 6).app (.bvar 0))) := by
    simpa [Delta, Common, d2TreeListRecTailV, SExpr.mkInst,
      d2InstVParamOne] using
      d2TreeListRecCommonStrong univs u l hCommon
  have hMajor := d2TreeListNilMajorStrong univs l hAlpha
  have hBody := d2TreeListRecApplyStrong univs u l
    hAlpha hMotive hRec hMajor
  dsimp only [Common] at hBody
  rw [d2TreeListRecCommonTerm_eq] at hBody
  rw [d2RuleBinders_eq, d2NilRuleLhsBodyV_eq, d2NilRuleResultV_eq]
  simpa [d2FieldBinders, d2NilFieldBindersV_eq, Delta,
    d2TreeListRecCommonTerm, mkInst_appN, SExpr.mkInst,
    d2InstVParamZero, d2InstVParamOne] using hBody

/-- The opened left body of the two-field `TreeList.cons` rule. -/
theorem d2TreeListConsLhsBodyStrong (univs : Nat)
    (u l : @SLevel (d2Params univs))
    {Gamma : List (@SExpr (d2Params univs))}
    (hRhs : @IsDefEqStrong (d2Params univs) Gamma
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.rule 4 TreeGen.flatCtors[4]).rhs)
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.rule 4 TreeGen.flatCtors[4]).rhs)
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.rule 4 TreeGen.flatCtors[4]).type)) :
    letI : Params := d2Params univs
    let As := (TreeGen.ruleBinders TreeGen.flatCtors[4]).map
      (SExpr.mkInst [u, l])
    IsDefEqStrong (As.reverse ++ Gamma)
      (SExpr.mkInst [u, l] (TreeGen.ruleLhsBody TreeGen.flatCtors[4]))
      (SExpr.mkInst [u, l] (TreeGen.ruleLhsBody TreeGen.flatCtors[4]))
      (SExpr.mkInst [u, l] (d2RuleResult TreeGen.flatCtors[4])) := by
  letI : Params := d2Params univs
  let Common := d2CommonBinders [u, l]
  let Delta := Common.reverse ++ Gamma
  let First := (SExpr.const ``Tree [l]).app (.bvar 7)
  let Second := (SExpr.const ``TreeList [l]).app (.bvar 8)
  let Full := Second :: First :: Delta
  have hCommon := d2CommonTelescopeStrong univs hRhs
  change StrongTelescope Gamma Common at hCommon
  have hFields0 := d2FieldTelescopeStrong univs hRhs
  have hFields : StrongTelescope Delta [First, Second] := by
    simpa [Delta, Common, First, Second, d2FieldBinders,
      d2ConsFieldBindersV_eq, SExpr.mkInst, d2InstVParamOne] using hFields0
  have ht0 := hFields.head_bvar (fun W H => d2StrongWeak univs W H)
  have ht : IsDefEqStrong Full (.bvar 1) (.bvar 1)
      ((SExpr.const ``Tree [l]).app (.bvar 9)) := by
    simpa [Full, First, Second, SExpr.lift, ← SExpr.lift'_comp] using ht0
  have hTail : StrongTelescope (First :: Delta) [Second] := by
    cases hFields with
    | cons _ hTail => exact hTail
  have hts0 := hTail.head_bvar (fun W H => d2StrongWeak univs W H)
  have hts : IsDefEqStrong Full (.bvar 0) (.bvar 0)
      ((SExpr.const ``TreeList [l]).app (.bvar 9)) := by
    simpa [Full, First, Second, SExpr.lift] using hts0
  let W : Ctx.Lift' (.skipN .refl 2) Delta Full := by
    simpa [Full] using
      (Ctx.Lift'.skipAppend [Second, First] :
        Ctx.Lift' (.skipN .refl 2) Delta ([Second, First] ++ Delta))
  have hAlpha : IsDefEqStrong Full
      (.bvar 9) (.bvar 9) (.sort l.succ) := by
    simpa [Full, SExpr.lift] using
      d2StrongWeak univs W (d2CommonAlphaStrong univs u l hCommon)
  have hMotive : IsDefEqStrong Full
      (.bvar 7) (.bvar 7)
      (.forallE ((SExpr.const ``TreeList [l]).app (.bvar 9)) (.sort u)) := by
    simpa [Full, SExpr.lift] using
      d2StrongWeak univs W (d2CommonTreeListMotiveStrong univs u l hCommon)
  have hRec : IsDefEqStrong Full
      ((applyTelVars Common (.const ``TreeList.rec [u, l])).lift'
        (.skipN .refl 2))
      ((applyTelVars Common (.const ``TreeList.rec [u, l])).lift'
        (.skipN .refl 2))
      (.forallE ((SExpr.const ``TreeList [l]).app (.bvar 9))
        ((SExpr.bvar 8).app (.bvar 0))) := by
    simpa [Delta, Common, Full, d2TreeListRecTailV, SExpr.mkInst,
      d2InstVParamOne, SExpr.lift, SExpr.lift'] using
      d2StrongWeak univs W (d2TreeListRecCommonStrong univs u l hCommon)
  have hMajor := d2TreeListConsMajorStrong univs l hAlpha ht hts
  have hBody := d2TreeListRecApplyStrong univs u l
    hAlpha hMotive hRec hMajor
  dsimp only [Common] at hBody
  rw [d2TreeListRecCommonTerm_eq] at hBody
  rw [d2RuleBinders_eq, d2ConsRuleLhsBodyV_eq, d2ConsRuleResultV_eq]
  simpa [d2FieldBinders, d2ConsFieldBindersV_eq, Delta, Full,
    First, Second, d2TreeListRecCommonTerm, mkInst_appN, SExpr.mkInst,
    d2InstVParamZero, d2InstVParamOne, SExpr.lift,
    ← SExpr.lift'_comp] using hBody

/-- A list known to contain exactly two entries can be exposed without
carrying arithmetic into the five literal-rule cases. -/
theorem list_eq_pair_of_length {alpha : Type} {xs : List alpha}
    (h : xs.length = 2) : ∃ a b, xs = [a, b] := by
  cases xs with
  | nil => simp at h
  | cons a xs =>
    cases xs with
    | nil => simp at h
    | cons b xs =>
      cases xs with
      | nil => exact ⟨a, b, rfl⟩
      | cons c xs => simp at h

/-- The literal `Tree.leaf` body satisfies the registered-body contract. -/
theorem d2TreeLeafRegisteredBody (univs : Nat)
    (u l : @SLevel (d2Params univs))
    {Gamma : List (@SExpr (d2Params univs))}
    (hRhs : @IsDefEqStrong (d2Params univs) Gamma
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.rule 0 TreeGen.flatCtors[0]).rhs)
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.rule 0 TreeGen.flatCtors[0]).rhs)
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.rule 0 TreeGen.flatCtors[0]).type)) :
    letI : Params := d2Params univs
    let As := (TreeGen.ruleBinders TreeGen.flatCtors[0]).map
      (SExpr.mkInst [u, l])
    IsDefEqStrong (As.reverse ++ Gamma)
      (SExpr.mkInst [u, l] (TreeGen.ruleLhsBody TreeGen.flatCtors[0]))
      (applyTelVars As (SExpr.mkInst [u, l]
        (TreeGen.rule 0 TreeGen.flatCtors[0]).rhs))
      (SExpr.mkInst [u, l] (d2RuleResult TreeGen.flatCtors[0])) := by
  letI : Params := d2Params univs
  obtain ⟨mcap, hmatch⟩ :=
    d2RuleLhsBody_matchesS univs u l TreeGen.flatCtors[0]
  have hcaps : (treeCapturePaths TreeGen.flatCtors[0]).map mcap =
      telBvars (TreeGen.ruleBinders TreeGen.flatCtors[0]).length := by
    simpa [telBvars,
      (show (TreeGen.ruleBinders TreeGen.flatCtors[0]).length = 9 by
        decide)] using d2LeafCaptureValues univs u l hmatch
  have hchecks := d2LeafCheckDefeqs univs u l hmatch
  have hAlpha0 := d2RuleAlphaStrong univs u l hRhs
  have hAlpha : IsDefEqStrong
      (((TreeGen.ruleBinders TreeGen.flatCtors[0]).map
        (SExpr.mkInst [u, l])).reverse ++ Gamma)
      (.bvar 8) (.bvar 8) (.sort l.succ) := by
    simpa [d2FieldBinders, d2LeafFieldBindersV_eq] using hAlpha0
  exact d2RegisteredLiteral univs
    (show TreeGen.flatCtors[0]? = some TreeGen.flatCtors[0] from rfl)
    u l hRhs (d2TreeLeafLhsBodyStrong univs u l hRhs)
    hmatch hcaps hchecks hAlpha

/-- The literal `Tree.node` body satisfies the registered-body contract. -/
theorem d2TreeNodeRegisteredBody (univs : Nat)
    (u l : @SLevel (d2Params univs))
    {Gamma : List (@SExpr (d2Params univs))}
    (hRhs : @IsDefEqStrong (d2Params univs) Gamma
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.rule 1 TreeGen.flatCtors[1]).rhs)
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.rule 1 TreeGen.flatCtors[1]).rhs)
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.rule 1 TreeGen.flatCtors[1]).type)) :
    letI : Params := d2Params univs
    let As := (TreeGen.ruleBinders TreeGen.flatCtors[1]).map
      (SExpr.mkInst [u, l])
    IsDefEqStrong (As.reverse ++ Gamma)
      (SExpr.mkInst [u, l] (TreeGen.ruleLhsBody TreeGen.flatCtors[1]))
      (applyTelVars As (SExpr.mkInst [u, l]
        (TreeGen.rule 1 TreeGen.flatCtors[1]).rhs))
      (SExpr.mkInst [u, l] (d2RuleResult TreeGen.flatCtors[1])) := by
  letI : Params := d2Params univs
  obtain ⟨mcap, hmatch⟩ :=
    d2RuleLhsBody_matchesS univs u l TreeGen.flatCtors[1]
  have hcaps : (treeCapturePaths TreeGen.flatCtors[1]).map mcap =
      telBvars (TreeGen.ruleBinders TreeGen.flatCtors[1]).length := by
    simpa [telBvars,
      (show (TreeGen.ruleBinders TreeGen.flatCtors[1]).length = 9 by
        decide)] using d2NodeCaptureValues univs u l hmatch
  have hchecks := d2NodeCheckDefeqs univs u l hmatch
  have hAlpha0 := d2RuleAlphaStrong univs u l hRhs
  have hAlpha : IsDefEqStrong
      (((TreeGen.ruleBinders TreeGen.flatCtors[1]).map
        (SExpr.mkInst [u, l])).reverse ++ Gamma)
      (.bvar 8) (.bvar 8) (.sort l.succ) := by
    simpa [d2FieldBinders, d2NodeFieldBindersV_eq] using hAlpha0
  exact d2RegisteredLiteral univs
    (show TreeGen.flatCtors[1]? = some TreeGen.flatCtors[1] from rfl)
    u l hRhs (d2TreeNodeLhsBodyStrong univs u l hRhs)
    hmatch hcaps hchecks hAlpha

/-- The literal `Tree.branch` body satisfies the registered-body contract. -/
theorem d2TreeBranchRegisteredBody (univs : Nat)
    (u l : @SLevel (d2Params univs))
    {Gamma : List (@SExpr (d2Params univs))}
    (hRhs : @IsDefEqStrong (d2Params univs) Gamma
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.rule 2 TreeGen.flatCtors[2]).rhs)
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.rule 2 TreeGen.flatCtors[2]).rhs)
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.rule 2 TreeGen.flatCtors[2]).type)) :
    letI : Params := d2Params univs
    let As := (TreeGen.ruleBinders TreeGen.flatCtors[2]).map
      (SExpr.mkInst [u, l])
    IsDefEqStrong (As.reverse ++ Gamma)
      (SExpr.mkInst [u, l] (TreeGen.ruleLhsBody TreeGen.flatCtors[2]))
      (applyTelVars As (SExpr.mkInst [u, l]
        (TreeGen.rule 2 TreeGen.flatCtors[2]).rhs))
      (SExpr.mkInst [u, l] (d2RuleResult TreeGen.flatCtors[2])) := by
  letI : Params := d2Params univs
  obtain ⟨mcap, hmatch⟩ :=
    d2RuleLhsBody_matchesS univs u l TreeGen.flatCtors[2]
  have hcaps : (treeCapturePaths TreeGen.flatCtors[2]).map mcap =
      telBvars (TreeGen.ruleBinders TreeGen.flatCtors[2]).length := by
    simpa [telBvars,
      (show (TreeGen.ruleBinders TreeGen.flatCtors[2]).length = 9 by
        decide)] using d2BranchCaptureValues univs u l hmatch
  have hchecks := d2BranchCheckDefeqs univs u l hmatch
  have hAlpha0 := d2RuleAlphaStrong univs u l hRhs
  have hAlpha : IsDefEqStrong
      (((TreeGen.ruleBinders TreeGen.flatCtors[2]).map
        (SExpr.mkInst [u, l])).reverse ++ Gamma)
      (.bvar 8) (.bvar 8) (.sort l.succ) := by
    simpa [d2FieldBinders, d2BranchFieldBindersV_eq] using hAlpha0
  exact d2RegisteredLiteral univs
    (show TreeGen.flatCtors[2]? = some TreeGen.flatCtors[2] from rfl)
    u l hRhs (d2TreeBranchLhsBodyStrong univs u l hRhs)
    hmatch hcaps hchecks hAlpha

/-- The literal `TreeList.nil` body satisfies the registered-body contract. -/
theorem d2TreeListNilRegisteredBody (univs : Nat)
    (u l : @SLevel (d2Params univs))
    {Gamma : List (@SExpr (d2Params univs))}
    (hRhs : @IsDefEqStrong (d2Params univs) Gamma
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.rule 3 TreeGen.flatCtors[3]).rhs)
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.rule 3 TreeGen.flatCtors[3]).rhs)
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.rule 3 TreeGen.flatCtors[3]).type)) :
    letI : Params := d2Params univs
    let As := (TreeGen.ruleBinders TreeGen.flatCtors[3]).map
      (SExpr.mkInst [u, l])
    IsDefEqStrong (As.reverse ++ Gamma)
      (SExpr.mkInst [u, l] (TreeGen.ruleLhsBody TreeGen.flatCtors[3]))
      (applyTelVars As (SExpr.mkInst [u, l]
        (TreeGen.rule 3 TreeGen.flatCtors[3]).rhs))
      (SExpr.mkInst [u, l] (d2RuleResult TreeGen.flatCtors[3])) := by
  letI : Params := d2Params univs
  obtain ⟨mcap, hmatch⟩ :=
    d2RuleLhsBody_matchesS univs u l TreeGen.flatCtors[3]
  have hcaps : (treeCapturePaths TreeGen.flatCtors[3]).map mcap =
      telBvars (TreeGen.ruleBinders TreeGen.flatCtors[3]).length := by
    simpa [telBvars,
      (show (TreeGen.ruleBinders TreeGen.flatCtors[3]).length = 8 by
        decide)] using d2NilCaptureValues univs u l hmatch
  have hchecks := d2NilCheckDefeqs univs u l hmatch
  have hAlpha0 := d2RuleAlphaStrong univs u l hRhs
  have hAlpha : IsDefEqStrong
      (((TreeGen.ruleBinders TreeGen.flatCtors[3]).map
        (SExpr.mkInst [u, l])).reverse ++ Gamma)
      (.bvar 7) (.bvar 7) (.sort l.succ) := by
    simpa [d2FieldBinders, d2NilFieldBindersV_eq] using hAlpha0
  exact d2RegisteredLiteral univs
    (show TreeGen.flatCtors[3]? = some TreeGen.flatCtors[3] from rfl)
    u l hRhs (d2TreeListNilLhsBodyStrong univs u l hRhs)
    hmatch hcaps hchecks hAlpha

/-- The literal `TreeList.cons` body satisfies the registered-body contract. -/
theorem d2TreeListConsRegisteredBody (univs : Nat)
    (u l : @SLevel (d2Params univs))
    {Gamma : List (@SExpr (d2Params univs))}
    (hRhs : @IsDefEqStrong (d2Params univs) Gamma
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.rule 4 TreeGen.flatCtors[4]).rhs)
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.rule 4 TreeGen.flatCtors[4]).rhs)
      (@SExpr.mkInst (d2Params univs) [u, l]
        (TreeGen.rule 4 TreeGen.flatCtors[4]).type)) :
    letI : Params := d2Params univs
    let As := (TreeGen.ruleBinders TreeGen.flatCtors[4]).map
      (SExpr.mkInst [u, l])
    IsDefEqStrong (As.reverse ++ Gamma)
      (SExpr.mkInst [u, l] (TreeGen.ruleLhsBody TreeGen.flatCtors[4]))
      (applyTelVars As (SExpr.mkInst [u, l]
        (TreeGen.rule 4 TreeGen.flatCtors[4]).rhs))
      (SExpr.mkInst [u, l] (d2RuleResult TreeGen.flatCtors[4])) := by
  letI : Params := d2Params univs
  obtain ⟨mcap, hmatch⟩ :=
    d2RuleLhsBody_matchesS univs u l TreeGen.flatCtors[4]
  have hcaps : (treeCapturePaths TreeGen.flatCtors[4]).map mcap =
      telBvars (TreeGen.ruleBinders TreeGen.flatCtors[4]).length := by
    simpa [telBvars,
      (show (TreeGen.ruleBinders TreeGen.flatCtors[4]).length = 10 by
        decide)] using d2ConsCaptureValues univs u l hmatch
  have hchecks := d2ConsCheckDefeqs univs u l hmatch
  have hAlpha0 := d2RuleAlphaStrong univs u l hRhs
  have hAlpha : IsDefEqStrong
      (((TreeGen.ruleBinders TreeGen.flatCtors[4]).map
        (SExpr.mkInst [u, l])).reverse ++ Gamma)
      (.bvar 9) (.bvar 9) (.sort l.succ) := by
    simpa [d2FieldBinders, d2ConsFieldBindersV_eq] using hAlpha0
  exact d2RegisteredLiteral univs
    (show TreeGen.flatCtors[4]? = some TreeGen.flatCtors[4] from rfl)
    u l hRhs (d2TreeListConsLhsBodyStrong univs u l hRhs)
    hmatch hcaps hchecks hAlpha

/-- All five generated `Tree`/`TreeList` rules satisfy the opened-body
contract consumed by the generic registered-tower closer. -/
theorem d2RegisteredBody (univs : Nat) : D2RegisteredBodyStep univs := by
  letI : Params := d2Params univs
  intro i constructor hentry ls Gamma hlen hRhs
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hentry
    have : TreeGen.flatCtors.length = 5 := rfl
    omega
  rcases hi with rfl | rfl | rfl | rfl | rfl
  · have hc := Option.some.inj
      ((show TreeGen.flatCtors[0]? = some TreeGen.flatCtors[0] from rfl).symm.trans
        hentry)
    subst constructor
    change ls.length = 2 at hlen
    obtain ⟨u, l, rfl⟩ := list_eq_pair_of_length hlen
    exact d2TreeLeafRegisteredBody univs u l hRhs
  · have hc := Option.some.inj
      ((show TreeGen.flatCtors[1]? = some TreeGen.flatCtors[1] from rfl).symm.trans
        hentry)
    subst constructor
    change ls.length = 2 at hlen
    obtain ⟨u, l, rfl⟩ := list_eq_pair_of_length hlen
    exact d2TreeNodeRegisteredBody univs u l hRhs
  · have hc := Option.some.inj
      ((show TreeGen.flatCtors[2]? = some TreeGen.flatCtors[2] from rfl).symm.trans
        hentry)
    subst constructor
    change ls.length = 2 at hlen
    obtain ⟨u, l, rfl⟩ := list_eq_pair_of_length hlen
    exact d2TreeBranchRegisteredBody univs u l hRhs
  · have hc := Option.some.inj
      ((show TreeGen.flatCtors[3]? = some TreeGen.flatCtors[3] from rfl).symm.trans
        hentry)
    subst constructor
    change ls.length = 2 at hlen
    obtain ⟨u, l, rfl⟩ := list_eq_pair_of_length hlen
    exact d2TreeListNilRegisteredBody univs u l hRhs
  · have hc := Option.some.inj
      ((show TreeGen.flatCtors[4]? = some TreeGen.flatCtors[4] from rfl).symm.trans
        hentry)
    subst constructor
    change ls.length = 2 at hlen
    obtain ⟨u, l, rfl⟩ := list_eq_pair_of_length hlen
    exact d2TreeListConsRegisteredBody univs u l hRhs

/-- Assemble the preferred exact D2 bundle after the registered-body field
has been discharged by `d2RegisteredBody`.  The remaining arguments retain
the current unfactored Tree site boundary: the parameter check plus one
paired five-rule replay contract.  The two inherited Nat replays are now
discharged internally.  The Tree replay still subsumes the canonical source-
level and parameter alignment described by
`D2TreeLevelAlignmentStep`; only their finite replay after that alignment is
engineering. -/
theorem D2BlockStepExact.of_remaining (univs : Nat)
    (checked : D2TreeCheckedStep univs)
    (replay : D2TreeReplayStep univs) : D2BlockStepExact univs where
  checked := checked
  replay := replay
  registeredBody := d2RegisteredBody univs

end ParamsD2
end SExpr
end Lean4Lean
