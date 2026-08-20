import Lean4Lean.Experimental.ShapeLogRel
import Lean4Lean.Theory.Typing.InductivePattern

/-!
# L4L-16N0: classified semantic environments

This module starts the normalization boundary with the part that is already
forced by the generated-rule interface: an iota rule admitted to the
classified fragment must retain its certified block origin.  Merely knowing
that a `VDefEq` is registered is not enough for normalization -- an arbitrary
registered equation need not decrease.  `StructuralDescent` ties the exact
`Pattern.IotaRule.df` selected by the semantic bridge to a generated block
rule and records the strict constructor-field bound for every recursive
descriptor in that rule.

The certificate is proposition-valued.  Normalization proofs may eliminate
it to recover the block data and its inequalities, but it adds no evaluator,
oracle, or computational choice to `Params`.
-/

namespace Lean4Lean
namespace SExpr

open VInductDecl
variable [Params]

/-- Certified generated provenance for one semantic iota descriptor.

`rule_eq` connects the registered equation used by `Pattern.IotaRule` to the
generator's actual rule.  `recursive_lt` is the structural decrease exposed
by the generator: every recursive call is routed through a field strictly
inside the constructor's field telescope.  The latter is stated on the
declaration-level descriptors so it also covers recursion under a Pi; the
recursor-universe transport theorem below preserves the same field index. -/
structure _root_.Lean4Lean.Pattern.IotaRule.StructuralOrigin
    {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (rule : Pattern.IotaRule r) : Type where
  source : VInductDecl
  generation : source.BlockGenerationChecked
  ruleIndex : Nat
  constructor : NormalizedBlockCtor
  entry : generation.flatCtors[ruleIndex]? = some constructor
  rule_eq : rule.df = generation.rule ruleIndex constructor
  recursive_lt : ∀ recursive ∈ constructor.ctor.view.recursive,
    recursive.fieldIndex < (constructor.ctor.rawFields source.nparams).length

/-- Proposition-valued ownership of generated descent data.  `Nonempty`
keeps the origin available to proof consumers without adding a computational
selector to the semantic interface. -/
def _root_.Lean4Lean.Pattern.IotaRule.StructuralDescent
    {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (rule : Pattern.IotaRule r) : Prop :=
  Nonempty rule.StructuralOrigin

end SExpr

namespace Pattern.IotaRule.StructuralOrigin

open VInductDecl
variable [Params]

/-- The source constructor selected by a descent certificate is genuinely a
member of the generated block. -/
theorem constructor_mem
    {rule : Pattern.IotaRule r} (O : rule.StructuralOrigin) :
    O.constructor ∈ O.generation.flatCtors :=
  List.mem_of_getElem? O.entry

/-- Recursor-universe transport does not disturb the strict source-field
bound.  This is the form consumed by the generated RHS, whose recursive calls
use `NormalizedCtor.recArgsR` rather than the declaration-level list. -/
theorem recArgsR_fieldIndex_lt
    {rule : Pattern.IotaRule r} (O : rule.StructuralOrigin)
    {recursive : RecArg}
    (hrecursive : recursive ∈ O.constructor.ctor.recArgsR
      O.source.uvars O.generation.elimination) :
    recursive.fieldIndex <
      (O.constructor.ctor.rawFields O.source.nparams).length := by
  obtain ⟨recursive₀, hrecursive₀, rfl⟩ :=
    NormalizedCtor.recArgsR_mem hrecursive
  simpa [RecArg.instL] using O.recursive_lt recursive₀ hrecursive₀

/-- The transported recursive descriptor also lies strictly inside the
recursor rule's emitted field telescope. -/
theorem recArgsR_fieldsR_lt
    {rule : Pattern.IotaRule r} (O : rule.StructuralOrigin)
    {recursive : RecArg}
    (hrecursive : recursive ∈ O.constructor.ctor.recArgsR
      O.source.uvars O.generation.elimination) :
    recursive.fieldIndex <
      (O.constructor.ctor.fieldsR O.source.uvars O.source.nparams
        O.generation.elimination).length := by
  rw [NormalizedCtor.fieldsR_length]
  exact recArgsR_fieldIndex_lt O hrecursive

/-- Rewrite the semantic descriptor's registered equation to its certified
generated rule. -/
theorem df_eq
    {rule : Pattern.IotaRule r} (O : rule.StructuralOrigin) :
    rule.df = O.generation.rule O.ruleIndex O.constructor :=
  O.rule_eq

/-- Rebase generated provenance across a `Params` extension that keeps the
selected registered equation.  D0--D2 use this when an old generated rule is
re-registered in the larger environment; none of the structural data depend
on the semantic syntax instance. -/
def rebase {P₀ P₁ : Params}
    {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    (rule₀ : @Pattern.IotaRule P₀ rec major ctor arity r)
    (O : @Pattern.IotaRule.StructuralOrigin P₀ rec major ctor arity r rule₀)
    (rule₁ : @Pattern.IotaRule P₁ rec major ctor arity r)
    (hdf : @Pattern.IotaRule.df P₁ rec major ctor arity r rule₁ =
      @Pattern.IotaRule.df P₀ rec major ctor arity r rule₀) :
    @Pattern.IotaRule.StructuralOrigin P₁ rec major ctor arity r rule₁ := by
  rcases O with
    ⟨source, generation, ruleIndex, constructor, entry, rule_eq, recursive_lt⟩
  exact {
    source := source
    generation := generation
    ruleIndex := ruleIndex
    constructor := constructor
    entry := entry
    rule_eq := hdf.trans rule_eq
    recursive_lt := recursive_lt }

end Pattern.IotaRule.StructuralOrigin

namespace Pattern.IotaRule.StructuralDescent

/-- Proposition-level counterpart of `StructuralOrigin.rebase`. -/
theorem rebase {P₀ P₁ : Params}
    {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
    {r : (RecursorIotaPattern rec major ctor arity).RHS ×
      (RecursorIotaPattern rec major ctor arity).Check}
    {rule₀ : @Pattern.IotaRule P₀ rec major ctor arity r}
    (H : @Pattern.IotaRule.StructuralDescent P₀ rec major ctor arity r rule₀)
    (rule₁ : @Pattern.IotaRule P₁ rec major ctor arity r)
    (hdf : @Pattern.IotaRule.df P₁ rec major ctor arity r rule₁ =
      @Pattern.IotaRule.df P₀ rec major ctor arity r rule₀) :
    @Pattern.IotaRule.StructuralDescent P₁ rec major ctor arity r rule₁ := by
  obtain ⟨O⟩ := H
  exact ⟨@Pattern.IotaRule.StructuralOrigin.rebase P₀ P₁ rec major ctor arity r
    rule₀ O rule₁ hdf⟩

end Pattern.IotaRule.StructuralDescent

namespace SExpr

open Lean4Lean
variable [Params]

/-! ## The non-Prop pattern-head law

`Pattern.WF` classifies every non-top pattern head as an ordinary
constructor.  The shape interpretation can therefore rebuild a genuine
constructor observation for any strongly typed successful match.  Such an
observation cannot type at `Prop`: `WShape.HasType.proofIrrel` forces every
observation of a proof to bottom, while ordinary constructors are non-bottom.

This is the semantic content of the classified boundary.  In particular it
rules out the `Acc.rec`/large-elimination counterexample at the exact firing
site, and implies `PatArgProp` without an independent oracle. -/

/-- A successful non-top match of a strongly typed term has a non-bottom
constructor observation.  The proof factors the constructor realization
already performed inside `LE_Interp.build_spine` into a reusable head law. -/
theorem LE_Interp.nonTopMatch_nonbot
    {p : Pattern} {LHS A : SExpr} {ls : List SLevel}
    {m2 : p.Path → SExpr} {Gamma0 Gamma : List SExpr}
    {rho : Valuation}
    (matched : p.MatchesS LHS ls m2)
    (W : Valuation.Fits Gamma0 Gamma rho)
    (typed : StrongSound Gamma LHS A)
    (wf : p.WF Params.classify false) :
    ∃ out, ¬out ≤ TShape.bot ∧ LE_Interp rho out LHS := by
  obtain ⟨threshold, built⟩ :=
    LE_Interp.build_spine matched W typed wf
      (m1 := fun _ => TShape.bot) (fun _ => LE_Interp.bot)
  obtain ⟨c, rargs, mcap, args, shapeMatch, _capture,
    argsInterp, lhs_eq⟩ := built threshold (Nat.le_refl threshold)
  have headClass : Params.classify c = some (.ctor rargs.length) := by
    simpa using shapeMatch.head_wf_eq
      (cl := Params.classify) (top := false) (k := 0) wf
  have typedLhs := lhs_eq ▸ typed
  clear typed
  obtain ⟨ci, registered, levelsLength, I, binders, indices, u,
      bindersLength, classifyI, u_ne_zero, typeEq, targetTyped⟩ :
      ∃ ci, Params.env.constants c = some ci ∧ ls.length = ci.uvars ∧
        ∃ I binders indices u,
          binders.length = rargs.length ∧
          Params.classify I = some (.indTy indices.length) ∧ u ≠ .zero ∧
          let target := List.foldr SExpr.forallE
            (List.foldr (fun X result : SExpr => result.app X)
              (SExpr.const I ls) indices)
            binders
          SoundEq Gamma (SExpr.mkInst ls ci.type) target ∧
            StrongSound Gamma target (.sort u) := by
    clear argsInterp lhs_eq
    induction args generalizing A with
      obtain ⟨_, _, core, _⟩ := typedLhs
    | nil =>
      cases core with
      | const registered levelsLength bundles bundleEq bundleTyped =>
        let cl : CtorBundle.IsCtor c := ⟨_, headClass, rfl⟩
        unfold CtorBundle.rhs at bundleEq
        have arityEq := Option.some.inj <| cl.cl.2.1.symm.trans headClass
        exact ⟨_, registered, levelsLength, _, _, _, _,
          (arityEq ▸ (bundles cl).hlen :), (bundles cl).hclI,
          (bundles cl).hu0, bundleEq cl, bundleTyped cl⟩
    | cons arg rest ih =>
      cases core with
      | app _ funTyped _ => exact ih funTyped
  let out := (WShape.ctor' c rargs.reverse).T
  have outInterp : LE_Interp rho out LHS := by
    have argsLength := Lean4Lean.List.Forall₂.length_eq argsInterp
    rw [← lhs_eq]
    refine LE_Interp.apps_realize W (WShape.HasType.T_iff.2 .ctor')
      ?_ typedLhs argsInterp (.ctor headClass .rfl)
    refine LE_Interp.apps_realize_inv (k := 0) W registered typeEq
      (bindersLength.trans argsLength).symm typedLhs ?_
    let target : SExpr :=
      indices.foldr (fun X result : SExpr => result.app X) (.const I ls)
    have peelBinders {binders Gamma rho u}
        (W : Valuation.Fits Gamma0 Gamma rho) (hu : u ≠ .zero)
        (hTarget : StrongSound Gamma
          (List.foldr .forallE target binders) (.sort u)) :
        ∃ Gamma' u', u' ≠ .zero ∧
          (binders.length.repeatTR (·.push .bot) rho).Fits Gamma0 Gamma' ∧
          StrongSound Gamma' target (.sort u') := by
      induction binders generalizing Gamma rho u with
      | nil => exact ⟨_, _, hu, W, hTarget⟩
      | cons binder binders ih =>
        obtain ⟨_, _, core, resultEq⟩ := hTarget
        cases core with
        | forallE domainTyped bodyTyped =>
          rename_i uDomain uBody
          refine ih ?_ (mt (fun hzero => ?_) hu) bodyTyped
          · exact W.cons (InterpTyped.hsort (domainTyped.sound W))
              .bot (.bot' (.bot' .sort))
          · have zeroInterp : LE_Interp rho (.sort false)
                (.sort (uDomain.imax uBody)) :=
              .sort (by simp [TShape.LE.rfl, SLevel.imax_eq_zero, hzero])
            have hle := WShape.sort_le.1 <|
              WShape.LE.of_T ((resultEq W).1 zeroInterp).le_sort
            injection congrArg (·.1) hle with levelEq
            simpa using levelEq
    obtain ⟨Gamma', targetSort, targetSort_ne_zero, targetFits,
      targetTyped'⟩ := peelBinders W u_ne_zero targetTyped
    rw [← Nat.repeat_eq_repeatTR] at targetFits
    simp [← argsLength, ← bindersLength]
    refine LE_Interp.apps_realize
      (rargs := .replicate indices.length (.bot (n := threshold + 1)))
      targetFits (WShape.HasType.T_iff.2 .indTy) ?_ targetTyped' ?_ ?_
    · exact .sort (decide_eq_true targetSort_ne_zero ▸ TShape.sort_eqv.1)
    · clear classifyI targetTyped' targetTyped peelBinders typeEq
      induction indices with
      | nil => exact .nil
      | cons _ _ ih => exact .cons .bot ih
    · simpa only [List.map_replicate, WShape.lift_bot] using
        (LE_Interp.Const.indTy
          (rargs := .replicate indices.length (.bot (n := threshold)))
          (by simpa using classifyI) .rfl
          |>.lift (Nat.le_succ threshold) (fun hle h => h.mono hle))
  refine ⟨out, ?_, outInterp⟩
  intro outBot
  have outEq : out.2 = .bot := TShape.le_bot.mp outBot
  have notStruct : ¬IsStruct c := by simp [IsStruct, headClass]
  simp [out, WShape.ctor', notStruct] at outEq
  cases congrArg Subtype.val outEq

/-- Semantic proof irrelevance: every interpretation of a strongly typed
proof term lies below bottom. -/
theorem StrongSound.interp_le_bot_of_prop
    {Gamma0 Gamma : List SExpr} {rho : Valuation} {M A : SExpr}
    (termTyped : StrongSound Gamma M A)
    (typeProp : StrongSound Gamma A (.sort .zero))
    (W : Valuation.Fits Gamma0 Gamma rho)
    {m : TShape} (termInterp : LE_Interp rho m M) :
    m ≤ TShape.bot := by
  obtain ⟨termShape, typeShape, root_le, termInterp', typeInterp,
    termHasType⟩ := termTyped.sound W termInterp
  obtain ⟨typeShape', sortShape, type_le, typeInterp', sortInterp,
    typeHasType⟩ := typeProp.sound W typeInterp
  have typeHasProp : typeShape'.HasType (.sort false) :=
    TShape.HasType.mono_r (by simpa using sortInterp.le_sort) .sort typeHasType
  exact root_le.trans <|
    typeHasProp.proofIrrel (typeHasProp.mono_r type_le termHasType)

/-- A strongly typed successful match at a non-top pattern cannot inhabit a
`Prop`-typed type. -/
theorem _root_.Lean4Lean.Pattern.MatchesS.nonTop_not_prop
    {p : Pattern} {LHS A : SExpr} {ls : List SLevel}
    {m2 : p.Path → SExpr} {Gamma0 Gamma : List SExpr}
    {rho : Valuation}
    (matched : p.MatchesS LHS ls m2)
    (W : Valuation.Fits Gamma0 Gamma rho)
    (termTyped : StrongSound Gamma LHS A)
    (typeProp : StrongSound Gamma A (.sort .zero))
    (wf : p.WF Params.classify false) : False := by
  obtain ⟨out, outNonbot, outInterp⟩ :=
    LE_Interp.nonTopMatch_nonbot matched W termTyped wf
  exact outNonbot (termTyped.interp_le_bot_of_prop typeProp W outInterp)

/-- The nonzero-sort firing law for pattern arguments.  It is phrased at the
strong SExpr boundary so it needs neither context reconstruction nor an
injectivity theorem: a matched argument cannot itself have a `Prop` type. -/
def Params.PatternArgumentNonProp : Prop :=
  ∀ {Gamma : List SExpr} {p₁ p₂ : Pattern}
    {rr : (Pattern.app p₁ p₂).RHS × (Pattern.app p₁ p₂).Check}
    {f b : SExpr} {m₁ : List SLevel}
    {m₂ : (Pattern.app p₁ p₂).Path → SExpr} {A : SExpr},
    Params.Pat (.app p₁ p₂) rr →
    (Pattern.app p₁ p₂).MatchesS (.app f b) m₁ m₂ →
    IsDefEqStrong Gamma b b A →
    IsDefEqStrong Gamma A A (.sort .zero) → False

/-- `CtorBundle.hu0` plus the shape proof-irrelevance law derive the firing
boundary for every semantic instance; it is not fixture-specific data. -/
theorem Params.patternArgumentNonProp [Params.Semantic] :
    Params.PatternArgumentNonProp := by
  intro Gamma p₁ p₂ rr f b m₁ m₂ A hpat matched bTyped typeProp
  cases matched with
  | app _ matchedArg =>
    exact matchedArg.nonTop_not_prop .nil
      (LE_Interp.strongSound bTyped).left
      (LE_Interp.strongSound typeProp).left
      (Params.pat_wf hpat).2

/-- SExpr form of the Church--Rosser `PatArgProp` condition: if a registered
contraction fires with a `Prop`-typed argument, its result is `Prop`-typed.
For the classified fragment the antecedent is impossible. -/
def Params.PatArgProp : Prop :=
  ∀ {Gamma : List SExpr} {p₁ p₂ : Pattern}
    {rr : (Pattern.app p₁ p₂).RHS × (Pattern.app p₁ p₂).Check}
    {f b : SExpr} {m₁ : List SLevel}
    {m₂ : (Pattern.app p₁ p₂).Path → SExpr} {A B : SExpr},
    Params.Pat (.app p₁ p₂) rr →
    (Pattern.app p₁ p₂).MatchesS (.app f b) m₁ m₂ →
    IsDefEqStrong Gamma f f (.forallE A B) →
    IsDefEqStrong Gamma b b A →
    IsDefEqStrong Gamma A A (.sort .zero) →
    IsDefEqStrong (A :: Gamma) B B (.sort .zero)

/-- The non-Prop head law implies `PatArgProp` by contradiction. -/
theorem Params.PatternArgumentNonProp.patArgProp
    (H : Params.PatternArgumentNonProp) : Params.PatArgProp := by
  intro Gamma p₁ p₂ rr f b m₁ m₂ A B hpat matched _ bTyped typeProp
  exact (H hpat matched bTyped typeProp).elim

/-- The L4L-16 normalization fragment.  Semantic soundness supplies the
nonzero constructor bundles, `DeltaRank` supplies strict definition descent,
and this proposition-valued class adds the generated iota origin together
with the firing-site boundary forced by those bundles. -/
class Params.Classified [Params] [Params.Semantic] [Params.DeltaRank] : Prop where
  iotaDescent :
    ∀ {rec : Name} {major : Nat} {ctor : Name} {arity : Nat}
      {r : (RecursorIotaPattern rec major ctor arity).RHS ×
        (RecursorIotaPattern rec major ctor arity).Check},
      Params.Pat (RecursorIotaPattern rec major ctor arity) r →
      ∃ rule : Pattern.IotaRule r, rule.StructuralDescent
  argumentNonProp : Params.PatternArgumentNonProp

/-- The classified class exports the Church--Rosser side condition without a
second environment oracle. -/
theorem Params.Classified.patArgProp [Params.Semantic] [Params.DeltaRank]
    [Params.Classified] : Params.PatArgProp :=
  Params.Classified.argumentNonProp.patArgProp

/-- Translate an exact Theory pattern match through the semantic syntax map. -/
theorem _root_.Lean4Lean.Pattern.Matches.mkS
    (H : Pattern.Matches p e m₁ m₂) :
    Pattern.MatchesS p (SExpr.mk e) (m₁.map SLevel.mk)
      (fun path => SExpr.mk (m₂ path)) := by
  induction H with
  | @const c levels =>
    refine cast ?_ (Pattern.MatchesS.const
      (c := c) (ls := levels.map SLevel.mk))
    simp only [SExpr.mk]
    congr 1
    funext path
    exact Empty.elim path
  | @var f f' levels capture arg _ ih =>
    change Pattern.MatchesS (.var f) (.app (SExpr.mk f') (SExpr.mk arg))
      (levels.map SLevel.mk) (fun path => SExpr.mk (Option.elim path arg capture))
    have captureEq : (fun path => SExpr.mk (Option.elim path arg capture)) =
        (fun path => Option.elim path (SExpr.mk arg)
          (fun inner => SExpr.mk (capture inner))) := by
      funext path
      cases path <;> rfl
    rw [captureEq]
    exact ih.var
  | @app f f' levels capture a a' levels' capture' _ _ ihf iha =>
    change Pattern.MatchesS (.app f a) (.app (SExpr.mk f') (SExpr.mk a'))
      (levels.map SLevel.mk)
      (fun path => SExpr.mk (Sum.elim capture capture' path))
    have captureEq : (fun path => SExpr.mk (Sum.elim capture capture' path)) =
        Sum.elim (fun inner => SExpr.mk (capture inner))
          (fun inner => SExpr.mk (capture' inner)) := by
      funext path
      cases path <;> rfl
    rw [captureEq]
    exact ihf.app iha

/-- Theory-facing corollary.  The Church--Rosser caller already owns context
validity; translation to the strong SExpr boundary exposes the generic
non-Prop argument contradiction. -/
theorem Params.Classified.theoryPatArgProp [Params.Semantic]
    [Params.DeltaRank] [Params.Classified]
    {Gamma : List VExpr} {p₁ p₂ : Pattern}
    {rr : (Pattern.app p₁ p₂).RHS × (Pattern.app p₁ p₂).Check}
    {f b : VExpr} {m₁ m₂} {A B : VExpr}
    (hGamma : OnCtx Gamma (Params.env.IsType Params.univs))
    (hpat : Params.Pat (.app p₁ p₂) rr)
    (matched : (Pattern.app p₁ p₂).Matches (.app f b) m₁ m₂)
    (_fTyped : Params.env.HasType Params.univs Gamma f (.forallE A B))
    (bTyped : Params.env.HasType Params.univs Gamma b A)
    (typeProp : Params.env.HasType Params.univs Gamma A (.sort .zero)) :
    Params.env.HasType Params.univs (A :: Gamma) B (.sort .zero) := by
  exact False.elim <| Params.Classified.argumentNonProp hpat matched.mkS
    ((bTyped.strong Params.henv hGamma).mkS)
    ((typeProp.strong Params.henv hGamma).mkS)

end SExpr

/-! Axiom pins: generated provenance is structural and must stay on the
accepted Theory baseline. -/

/-- info: 'Lean4Lean.Pattern.IotaRule.StructuralOrigin.recArgsR_fieldIndex_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Pattern.IotaRule.StructuralOrigin.recArgsR_fieldIndex_lt

/-- info: 'Lean4Lean.Pattern.IotaRule.StructuralOrigin.recArgsR_fieldsR_lt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Pattern.IotaRule.StructuralOrigin.recArgsR_fieldsR_lt

/-- info: 'Lean4Lean.Pattern.IotaRule.StructuralDescent.rebase' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Pattern.IotaRule.StructuralDescent.rebase

/-- info: 'Lean4Lean.SExpr.Params.patternArgumentNonProp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SExpr.Params.patternArgumentNonProp

/-- info: 'Lean4Lean.SExpr.Params.Classified.theoryPatArgProp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SExpr.Params.Classified.theoryPatArgProp

end Lean4Lean
