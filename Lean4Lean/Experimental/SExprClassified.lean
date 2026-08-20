import Lean4Lean.Experimental.SExpr
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

end Lean4Lean
