import Lean4Lean.Theory.BlockProjection
import Lean4Lean.Theory.Meta

/-!
# Block-backed projection regression

This fixture pins the case that the singleton `VStructureView` cannot
represent: a structure-shaped family whose recursor is generated as part of
a genuine mutual block.  The selected family has one constructor and no
indices, while its companion family contributes two additional minors.
-/

namespace Lean4Lean.Tests.BlockProjection

open VInductDecl

universe u

mutual

inductive MutualBox (α : Type u) : Type u where
  | mk : α → MutualChain α → MutualBox α

inductive MutualChain (α : Type u) : Type u where
  | nil : MutualChain α
  | cons : MutualBox α → MutualChain α → MutualChain α

end

def mutualBoxType : VInductiveType where
  name := ``MutualBox
  uvars := 1
  type := vconst(type_of% @MutualBox).type
  ctors := [⟨vconst(type_of% @MutualBox.mk), ``MutualBox.mk⟩]

def mutualChainType : VInductiveType where
  name := ``MutualChain
  uvars := 1
  type := vconst(type_of% @MutualChain).type
  ctors := [⟨vconst(type_of% @MutualChain.nil), ``MutualChain.nil⟩,
    ⟨vconst(type_of% @MutualChain.cons), ``MutualChain.cons⟩]

def mutualBoxDecl : VInductDecl :=
  ⟨1, 1, [mutualBoxType, mutualChainType]⟩

def mutualBoxGeneration : mutualBoxDecl.BlockGenerationChecked :=
  mutualBoxDecl.identityBlockGeneration?.get (by decide)

/-- The first family is structure-shaped, but deliberately retains the full
two-family generation certificate. -/
def mutualBoxView : VBlockStructureView where
  source := mutualBoxDecl
  generation := mutualBoxGeneration
  family := mutualBoxGeneration.families[0]
  family_mem := .head _
  constructor := mutualBoxGeneration.families[0].ctorPairs[0]
  constructor_eq := rfl
  raw_indices_eq := by decide
  checked_indices_eq := by decide
  fieldSorts := [.succ (.param 0), .succ (.param 0)]
  fieldSorts_length := by decide

example : mutualBoxView.generation.familyCount = 2 := rfl
example : mutualBoxView.family.view.ordinal = 0 := rfl
example : mutualBoxView.name = ``MutualBox := rfl
example : mutualBoxView.constructorName = ``MutualBox.mk := rfl
example : mutualBoxView.recursorName = ``MutualBox.rec := rfl
example : mutualBoxView.generation.motiveTypes.length = 2 := rfl
example : mutualBoxView.generation.minorTypes.length = 3 := rfl
example : mutualBoxView.generation.recursors.map (·.name) =
    [``MutualBox.rec, ``MutualChain.rec] := rfl
example : mutualBoxView.fields.length = 2 := rfl
example : mutualBoxView.family.view.indices = [] := rfl

/-- The selected constructor is recovered from the flattened block inventory,
not from a fabricated singleton declaration. -/
example : mutualBoxView.blockConstructor ∈
    mutualBoxView.generation.flatCtors :=
  mutualBoxView.blockConstructor_mem

/-- Large elimination uses the block's common result universe and preserves
all source universe arguments expected by the actual mutual recursor. -/
example : mutualBoxView.projectionLevels (.succ (.param 0)) [.param 0] =
    [.succ (.param 0), .param 0] := rfl

def mutualBoxFirstCode : VStructureView.ProjectionCode :=
  (mutualBoxView.projectionCodes [.param 0] [.bvar 0])[0]

def mutualBoxFirstProjectorBody : VExpr :=
  match mutualBoxFirstCode.projector with
  | .lam _ body => body
  | other => other

/-- One parameter, two motives, three flattened minors, and the major are
passed to the actual mutual recursor. -/
example : (mutualBoxFirstProjectorBody.appArgs []).length = 7 := rfl
example : mutualBoxFirstProjectorBody.appHead =
    .const ``MutualBox.rec [.succ (.param 0), .param 0] := rfl

/-- The code retains the selected minor while its projector application also
contains the two companion-family rebuild minors. -/
example : (mutualBoxView.projectionMotives [.param 0] [.bvar 0]
    mutualBoxFirstCode.fieldSort mutualBoxFirstCode.typeFn).length = 2 := rfl
example : (mutualBoxView.projectionCodes [.param 0] [.bvar 0]).length = 2 := rfl

#check VEnv.AddInductBlockGenerationTrace.generationEnv
#check VBlockStructureView.Registered.ofTrace
#check VBlockStructureView.WF.ofTrace

end Lean4Lean.Tests.BlockProjection
