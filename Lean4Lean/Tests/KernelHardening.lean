/-
This file is derived from lean4lean and has been modified by Argument Computer Corporation.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/

import Lean4Lean.Environment
import Lean4Lean.Inductive.EliminationTrace

/-!
Executable regressions for the kernel hardening merged between Lean v4.32.2 and
v4.33.0-rc2.  The declarations are assembled manually so they exercise
`Lean4Lean.addDecl` and `Lean4Lean.TypeChecker` directly.
-/

namespace Lean4Lean.Tests.KernelHardening

open Lean Lean4Lean TypeChecker
open private Lean.Kernel.Environment.add from Lean.Environment

private def errorOf (r : Except Kernel.Exception α) : MetaM (Option String) := do
  match r with
  | .ok _ => return none
  | .error e => return some (← (e.toMessageData {}).toString)

private def mentions (pat s : String) : Bool := (s.splitOn pat).length > 1

private def expectError (label pat : String) (r : Except Kernel.Exception α) : MetaM Unit := do
  match ← errorOf r with
  | none => throwError "{label} was accepted"
  | some msg => unless mentions pat msg do throwError "{label} failed for the wrong reason: {msg}"

private def runM (r : Except Kernel.Exception α) : MetaM α := do
  match r with
  | .ok a => pure a
  | .error e => throwError "kernel operation failed: {← (e.toMessageData {}).toString}"

private def mkPartial (n : Name) (lparams : List Name) (type value : Expr) : DefinitionVal :=
  { name := n, levelParams := lparams, type, value, hints := .opaque, safety := .partial }

private def universeTy : Expr :=
  .forallE `x (.sort (.param `u)) (.sort (.param `u)) .default

private def universeVal : Expr :=
  .lam `x (.sort (.param `u)) (.bvar 0) .default

private def imaxProp : Expr := .sort (.imax (.succ .zero) .zero)

private def imaxDataDecl : Declaration :=
  .inductDecl [] 0 [{
    name := `L4LKIPData
    type := imaxProp
    ctors := [{
      name := `L4LKIPData.mk
      type := .forallE `b (.const ``Bool []) (.const `L4LKIPData []) .default }]
  }] false

/-- The auxiliary name the kernel generates for a nested `List` occurrence. -/
private def auxListName : Name := (`_nested ++ `List).appendIndexAfter 1

/-- lean4#14616.  `mk` nests `List L4LKNReal`, so eliminating it makes the kernel generate
`_nested.List_1`; `bad` then names that auxiliary.  This is the form that *discriminates*:
without the check the declaration is accepted, and `restoreNested` rewrites the stored type of
`bad` to `List L4LKNReal → L4LKNReal`, which the kernel never checked.  A declaration naming an
auxiliary that never exists is instead rejected as an unknown constant either way. -/
private def nestedAuxRealDecl : Declaration :=
  .inductDecl [] 0 [{
    name := `L4LKNReal
    type := .sort 1
    ctors := [
      { name := `L4LKNReal.mk
        type := .forallE `xs (.app (.const ``List [.zero]) (.const `L4LKNReal []))
          (.const `L4LKNReal []) .default },
      { name := `L4LKNReal.bad
        type := .forallE `y (.const auxListName []) (.const `L4LKNReal []) .default }]
  }] false

private def nestedAuxProjDecl : Declaration :=
  .inductDecl [] 0 [{
    name := `L4LKNProj
    type := .sort .zero
    ctors := [{
      name := `L4LKNProj.mk
      type := .forallE `x (.const ``Nat [])
        (.forallE `y (.proj `_nested.L4LHost_1 0 (.bvar 0))
          (.const `L4LKNProj []) .default) .default }]
  }] false

/-- Declaration heads are part of the restoration domain too.  Empty source
families make the family-head check observable independently of constructor
types. -/
private def nestedAuxFamilyHeadDecl : Declaration :=
  .inductDecl [] 0 [{
    name := `_nested.L4LFamilyHead
    type := .sort 1
    ctors := []
  }] false

/-- A reserved constructor head is observable independently of its ordinary
source type, which mentions only the non-reserved family head. -/
private def nestedAuxConstructorHeadDecl : Declaration :=
  .inductDecl [] 0 [{
    name := `L4LConstructorHead
    type := .sort 1
    ctors := [{
      name := `_nested.L4LConstructorHead
      type := .const `L4LConstructorHead [] }]
  }] false

private def nestedBadDecl (bad : Expr) (name : Name) : Declaration :=
  let ind := fun a => .app (.const name []) a
  .inductDecl [] 1 [{
    name
    type := .forallE `α (.sort 1) (.sort 1) .default
    ctors := [{
      name := name ++ `mk
      type := .forallE `α (.sort 1)
        (.forallE `xs (.app (.const ``Array [.zero]) (ind bad))
          (ind (.bvar 1)) .default) .default }]
  }] false

/-- lean4#14582: every recursive occurrence in an original constructor must
use the declaration's shared parameters.  This deliberately uses `Nat`
instead of the surrounding `α`; later normalization must not get a chance to
hide that non-uniform occurrence. -/
private def nonUniformOccurrenceDecl : Declaration :=
  let family := fun argument => .app (.const `L4LNonUniform []) argument
  .inductDecl [] 1 [{
    name := `L4LNonUniform
    type := .forallE `α (.sort 1) (.sort 1) .default
    ctors := [{
      name := `L4LNonUniform.mk
      type := .forallE `α (.sort 1)
        (.forallE `recursive (family (.const ``Nat []))
          (family (.bvar 1)) .default) .default }]
  }] false

/-- Small ordinary block used to exercise the generated-recursor guard through
the exact retained producer before corrupting one rule in an isolated test
environment. -/
private def generatedRecursorGuardTypes : List InductiveType := [{
  name := `L4LGeneratedRecursorGuard
  type := .sort 1
  ctors := [{
    name := `L4LGeneratedRecursorGuard.mk
    type := .const `L4LGeneratedRecursorGuard [] }]
}]

/-- lean4#14613: projecting the field back out of a `Sort (imax 1 0)` proof would break proof
irrelevance, so `inferProj` must reject it. -/
private def imaxLeakDecl : Declaration :=
  .defnDecl {
    name := `L4LKIPLeak
    levelParams := []
    type := .forallE `proof (.const `L4LKIPData []) (.const ``Bool []) .default
    value := .lam `proof (.const `L4LKIPData []) (.proj `L4LKIPData 0 (.bvar 0)) .default
    hints := .abbrev, safety := .safe }

structure L4LKC where b : Bool
inductive L4LKW : Type where | mk (p : Bool)
inductive L4LKL (α : Type) (b : Bool) : Type where | mk

/-- lean4#14576/#14577: the parametric arguments of a nested occurrence are dropped from the
auxiliary declaration, so they escape checking unless they are checked against the environment
that results from the declaration. Here `w.1.1` is ill typed. -/
private def nestedIllTypedParams : Declaration :=
  let w : Expr := .bvar 0
  let Ew : Expr := .app (.const `L4LKE []) w
  let b : Expr := .proj ``L4LKC 0 (.proj ``L4LKC 0 w)
  let l : Expr := mkApp2 (.const ``L4LKL []) Ew b
  .inductDecl [] 1 [{
    name := `L4LKE
    type := .forallE `w (.const ``L4LKW []) (.sort 1) .default
    ctors := [{
      name := `L4LKE.mk
      type := .forallE `w (.const ``L4LKW [])
        (.forallE `l l (.app (.const `L4LKE []) (.bvar 1)) .default) .default }]
  }] false

private partial def deepNat : Nat → Expr
  | 0 => .const ``Nat.zero []
  | n + 1 => .app (.const ``Nat.succ []) (deepNat n)

/-- Preserve a generated rule's argument telescope while replacing its
terminal reduct by a closed term of the wrong type. -/
private partial def malformedRuleRhs : Expr → Expr
  | .lam name type body binderInfo =>
      .lam name type (malformedRuleRhs body) binderInfo
  | .mdata data body => .mdata data (malformedRuleRhs body)
  | _ => .const ``Nat.zero []

structure ProjB where b : Nat

run_meta do
  let env := (← getEnv).toKernelEnv

  -- lean4#14608 and lean4#14632: mutual blocks share level parameters and names.
  expectError "mutual block with mismatched universe parameters"
    "same universe level parameters" <|
    Lean4Lean.addDecl env <| .mutualDefnDecl [
      mkPartial `L4LMutA [`u] universeTy universeVal,
      mkPartial `L4LMutB [] universeTy universeVal]
  expectError "mutual block with a duplicate name" "duplicate declaration name" <|
    Lean4Lean.addDecl env <| .mutualDefnDecl [
      mkPartial `L4LMutDup [] (.const ``Nat []) (mkRawNatLit 0),
      mkPartial `L4LMutDup [] (.const ``Bool []) (.const ``Bool.true [])]
  match Lean4Lean.addDecl env <| .mutualDefnDecl [
      mkPartial `L4LMutGoodA [] (.const ``Nat []) (mkRawNatLit 0),
      mkPartial `L4LMutGoodB [] (.const ``Bool []) (.const ``Bool.true [])] with
  | .error e => throwError "valid mutual block was rejected: {← (e.toMessageData {}).toString}"
  | .ok _ => pure ()

  -- lean4#14613/#14615: normalized `Prop` controls inductive classification and recursor levels.
  let env' ← match Lean4Lean.addDecl env imaxDataDecl with
    | .ok env' => pure env'
    | .error e => throwError "imax-Prop inductive was rejected: {← (e.toMessageData {}).toString}"
  let some (.recInfo recInfo) := env'.find? `L4LKIPData.rec
    | throwError "imax-Prop recursor was not generated"
  unless recInfo.levelParams.isEmpty do
    throwError "imax-Prop inductive received a large-elimination universe"
  -- ... but its field must not be projectable back out, or proof irrelevance equates
  -- `mk false` and `mk true`.
  expectError "projection out of an `imax`-`Prop` proof" "invalid projection" <|
    Lean4Lean.addDecl env' imaxLeakDecl

  -- lean4#14616: a constructor naming a `_nested` auxiliary the kernel really generated.
  expectError "constructor naming a generated nested auxiliary" "reserved prefix '_nested'" <|
    Lean4Lean.addDecl env nestedAuxRealDecl
  -- The `Expr.proj` form of the same scan.  Note this one names an auxiliary that never exists,
  -- so it pins the branch rather than the hole: without the check it is still rejected, as an
  -- unknown constant.
  expectError "constructor naming a nested auxiliary in a projection" "reserved prefix '_nested'" <|
    Lean4Lean.addDecl env nestedAuxProjDecl
  expectError "inductive family using a reserved nested head" "reserved prefix '_nested'" <|
    Lean4Lean.addDecl env nestedAuxFamilyHeadDecl
  expectError "constructor using a reserved nested head" "reserved prefix '_nested'" <|
    Lean4Lean.addDecl env nestedAuxConstructorHeadDecl

  -- lean4#14576/#14577: parametric arguments dropped from the auxiliary declaration.
  expectError "nested inductive with ill-typed dropped parameters" "invalid projection" <|
    Lean4Lean.addDecl env nestedIllTypedParams

  -- lean4#14607: validate original nested constructor types before elimination can hide them.
  expectError "nested inductive containing a free variable" "free variables" <|
    Lean4Lean.addDecl env <| nestedBadDecl (.fvar { name := `l4lBadFVar }) `L4LNestedFVar
  expectError "nested inductive containing a metavariable" "metavariables" <|
    Lean4Lean.addDecl env <| nestedBadDecl (.mvar { name := `l4lBadMVar }) `L4LNestedMVar

  -- lean4#14582: reject the source occurrence itself, before nested
  -- elimination or constructor normalization can alter what is inspected.
  expectError "inductive with a non-uniform recursive occurrence"
    "must be applied to the parameters and universe levels" <|
    Lean4Lean.addDecl env nonUniformOccurrenceDecl

  -- lean4#14808: generated computation rules must preserve the type inferred
  -- for the unreduced recursor application.  Start from one genuinely
  -- synthesized retained execution, then alter only the stored rule RHS in a
  -- private environment and rerun the public data-bearing guard.
  let generated ← runM <|
    AddInductive.EnvironmentInductiveExecution.buildExecution env [] 0
      generatedRecursorGuardTypes false false
  let generatedExecution := generated.2
  let checked := generatedExecution.flattened.recursorCheck
  let recName := mkRecName generatedRecursorGuardTypes.head!.name
  let some (.recInfo recursor) := checked.recursors.env.find? recName
    | throwError "generated-recursor fixture did not emit its recursor"
  let rule :: rules := recursor.rules
    | throwError "generated-recursor fixture did not emit a computation rule"
  let malformedRecursor : RecursorVal := {
    recursor with
    rules := { rule with rhs := malformedRuleRhs rule.rhs } :: rules }
  let malformedEnv := checked.recursors.env.add (.recInfo malformedRecursor)
  let malformedContext : AddInductive.Context := {
    checked.synthesis.synthesisContext with env := malformedEnv }
  expectError "generated recursor with a non-type-preserving rule"
    "is not type-preserving" <|
    AddInductive.checkGeneratedRecursorsAt
      generatedExecution.flattened.eliminationExecution.normalization.stats
      generatedExecution.nested.types.toArray
      generatedExecution.flattened.eliminationExecution.elimination.level
      (checked.synthesis.recInfos.map (·.motive))
      (checked.synthesis.recInfos.flatMap (·.minors)) 0 malformedContext

  -- lean4#14577: the final restored-artifact pass is itself rejecting, not
  -- merely a trace wrapper around unchecked expressions.
  expectError "restored constructor artifact with an unknown constant"
    "unknown constant" <|
    Lean4Lean.checkRestoredArtifactSources env .safe {} [{
      origin := .constructorType `L4LMalformedRestoredConstructor
      lparams := []
      expression := .const `L4LMissingRestoredType [] }]

  -- lean4#14632: projection indices are `Nat` throughout lean4lean, so an index past `2^32`
  -- is stuck rather than truncated.  The structure *name* is deliberately not compared here;
  -- see the projection entry in `divergences.md`.
  let b : Expr := .app (.const ``ProjB.mk []) (mkRawNatLit 7)
  let good : Expr := .proj ``ProjB 0 b
  let huge : Expr := .proj ``ProjB 4294967296 b
  let goodWhnf ← runM <| TypeChecker.M.run env (x := TypeChecker.whnf good)
  unless goodWhnf == mkRawNatLit 7 do throwError "valid projection did not reduce"
  let hugeWhnf ← runM <| TypeChecker.M.run env (x := TypeChecker.whnf huge)
  unless hugeWhnf == huge do throwError "large projection index was truncated during reduction"
  let same ← runM <| TypeChecker.M.run env (x := TypeChecker.isDefEq good good)
  unless same do throwError "identical projections were not definitionally equal"
  expectError "out-of-range large projection" "invalid projection" <|
    TypeChecker.M.run env (x := TypeChecker.checkType huge)

  -- lean4#13956: lean4lean's explicit fuel remains deterministic and configurable.
  -- This fork's syntactic `isDefEq` fast path (divergence D011) answers the
  -- app-argument checks of `checkType (deepNat 100)` without consuming
  -- recursion fuel, so the fuel probe reduces the term instead: `whnf`
  -- descends through the `Nat.succ` spine one method level at a time.
  expectError "deep term with low recursion fuel" "deep recursion" <|
    TypeChecker.M.run env (fuel := { recDepth := 1 }) (x := TypeChecker.whnf (deepNat 100))
  match TypeChecker.M.run env (fuel := { recDepth := 1000 })
      (x := TypeChecker.checkType (deepNat 100)) with
  | .error e => throwError "deep term with sufficient recursion fuel failed: {← (e.toMessageData {}).toString}"
  | .ok ty => unless ty.isConstOf ``Nat do throwError "deep term inferred an unexpected type"

end Lean4Lean.Tests.KernelHardening
