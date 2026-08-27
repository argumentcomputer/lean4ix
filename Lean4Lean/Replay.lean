/-
This file is derived from lean4lean and has been modified by Argument Computer Corporation.
Modifications Copyright (c) 2026 Argument Computer Corporation.
SPDX-License-Identifier: Apache-2.0 AND (MIT OR Apache-2.0)
-/

/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Lean.CoreM
import Lean.Util.FoldConsts
import Lean4Lean.Environment
import Lean4Lean.Theory.Inductive
import Lean4Lean.Theory.NestedInductive

namespace Lean

def HashMap.keyNameSet (m : Std.HashMap Name α) : NameSet :=
  m.fold (fun s n _ => s.insert n) {}

namespace Environment

def importsOf (env : Environment) (n : Name) : Array Import :=
  if n = env.header.mainModule then
    env.header.imports
  else match env.getModuleIdx? n with
    | .some idx => env.header.moduleData[idx.toNat]!.imports
    | .none => #[]

end Environment

/-- Like `Expr.getUsedConstants`, but produce a `NameSet`. -/
def Expr.getUsedConstants' (e : Expr) : NameSet :=
  e.foldConsts {} fun c cs => cs.insert c

namespace ConstantInfo

/-- Return all names appearing in the type or value of a `ConstantInfo`. -/
def getUsedConstants (c : ConstantInfo) : NameSet :=
  -- Replay needs dependencies from theorem proofs and opaque bodies even though
  -- `ConstantInfo.value?` hides both by default.
  c.type.getUsedConstants' ++ match c.value? (allowOpaque := true) with
  | some v => v.getUsedConstants'
  | none => match c with
    | .inductInfo val => .ofList val.ctors
    | .ctorInfo val => ({} : NameSet).insert val.name
    | .recInfo val => .ofList val.all
    | _ => {}

end ConstantInfo

end Lean

def Lean.Kernel.Exception.mapEnvM [Monad m]
    (ex : Exception) (f : Environment → m Environment) : m Exception := do
  match ex with
  | unknownConstant env c => return .unknownConstant (← f env) c
  | alreadyDeclared env c => return .alreadyDeclared (← f env) c
  | declTypeMismatch env d t => return .declTypeMismatch env d t
  | declHasMVars env c e => return declHasMVars (← f env) c e
  | declHasFVars env c e => return declHasFVars (← f env) c e
  | funExpected env lctx e => return funExpected (← f env) lctx e
  | typeExpected env lctx e => return typeExpected (← f env) lctx e
  | letTypeMismatch  env lctx n t1 t2 => return letTypeMismatch (← f env) lctx n t1 t2
  | exprTypeMismatch env lctx e t => return exprTypeMismatch (← f env) lctx e t
  | appTypeMismatch  env lctx e fn arg => return appTypeMismatch (← f env) lctx e fn arg
  | invalidProj env lctx e => return invalidProj (← f env) lctx e
  | thmTypeIsNotProp env c t => return thmTypeIsNotProp (← f env) c t
  | other _
  | deterministicTimeout
  | excessiveMemory
  | deepRecursion
  | interrupted => return ex

def Lean.Declaration.name : Declaration → String
  | .axiomDecl d => s!"axiomDecl {d.name}"
  | .defnDecl d => s!"defnDecl {d.name}"
  | .thmDecl d => s!"thmDecl {d.name}"
  | .opaqueDecl d => s!"opaqueDecl {d.name}"
  | .quotDecl => s!"quotDecl"
  | .mutualDefnDecl d => s!"mutualDefnDecl {d.map (·.name)}"
  | .inductDecl _ _ d _ => s!"inductDecl {d.map (·.name)}"

def Lean.Expr.hasStrLit (e : Expr) : Bool := (e.find? isStringLit).isSome

def Lean.ConstantInfo.hasStrLit (ci : ConstantInfo) : Bool :=
  ci.type.hasStrLit || (ci.value? (allowOpaque := true)).any (·.hasStrLit)

open Lean hiding Environment Exception
open Kernel

namespace Lean4Lean.Differential

/-- Stable identifier for the differential case/result wire format. -/
def schema : String := "lean4lean.differential"

/-- Current differential case/result wire-format version. -/
def schemaVersion : Nat := 1

/-- A stage at which a differential case can accept or reject. -/
inductive Phase where
  | selection
  | moduleLoad
  | elaboration
  | rawTranslation
  | normalization
  | theoryGeneration
  | kernelReplay
  | metadataComparison
  deriving Repr, Inhabited, BEq

def Phase.toString : Phase → String
  | .selection => "selection"
  | .moduleLoad => "module-load"
  | .elaboration => "elaboration"
  | .rawTranslation => "raw-translation"
  | .normalization => "normalization"
  | .theoryGeneration => "theory-generation"
  | .kernelReplay => "kernel-replay"
  | .metadataComparison => "metadata-comparison"

def Phase.ofString? : String → Option Phase
  | "selection" => some .selection
  | "module-load" => some .moduleLoad
  | "elaboration" => some .elaboration
  | "raw-translation" => some .rawTranslation
  | "normalization" => some .normalization
  | "theory-generation" => some .theoryGeneration
  | "kernel-replay" => some .kernelReplay
  | "metadata-comparison" => some .metadataComparison
  | _ => none

instance : Lean.ToJson Phase where
  toJson phase := Lean.toJson phase.toString

instance : Lean.FromJson Phase where
  fromJson? j := do
    let value ← j.getStr?
    let some phase := Phase.ofString? value
      | throw s!"unknown differential phase '{value}'"
    pure phase

/-- Whether the observed phase accepted or rejected the input. -/
inductive Outcome where
  | accepted
  | rejected
  deriving Repr, Inhabited, BEq

def Outcome.toString : Outcome → String
  | .accepted => "accepted"
  | .rejected => "rejected"

def Outcome.ofString? : String → Option Outcome
  | "accepted" => some .accepted
  | "rejected" => some .rejected
  | _ => none

instance : Lean.ToJson Outcome where
  toJson outcome := Lean.toJson outcome.toString

instance : Lean.FromJson Outcome where
  fromJson? j := do
    let value ← j.getStr?
    let some outcome := Outcome.ofString? value
      | throw s!"unknown differential outcome '{value}'"
    pure outcome

/-- Versioned input record for one independently replayable differential case. -/
structure Case where
  schema : String := Differential.schema
  version : Nat := Differential.schemaVersion
  id : String
  /-- Optional standalone source file to elaborate before loading `module`. -/
  source : Option String := none
  module : String
  declaration : String
  fresh : Bool := false
  expectedOutcome : Outcome
  expectedPhase : Phase
  deriving Repr, Lean.ToJson, Lean.FromJson

/-- Reject a case file whose schema identity or version is not understood. -/
def Case.validate (c : Case) : Except String Case := do
  unless c.schema == Differential.schema do
    throw s!"unsupported differential schema '{c.schema}' (expected '{Differential.schema}')"
  unless c.version == Differential.schemaVersion do
    throw s!"unsupported differential schema version {c.version} (expected {Differential.schemaVersion})"
  if c.id.isEmpty then throw "differential case id must not be empty"
  if c.source.any (·.isEmpty) then throw "differential case source path must not be empty"
  if c.module.isEmpty then throw "differential case module must not be empty"
  if c.declaration.isEmpty then throw "differential case declaration must not be empty"
  pure c

/-- The sole normalization applied to raw kernel expressions in version 1.

`Expr.mdata` carries elaborator/pretty-printer annotations and is ignored by
kernel checking. The structural codec otherwise preserves names (including
hygienic name structure), levels, binder information, literals, and every
expression node. This is the same boundary used by `Lean.Idbg.exprToJson`. -/
structure NormalizationPolicy where
  expressionCodec : String := "lean-expr-ast-v1"
  expressionMetadata : String := "strip-mdata"
  theoryExpressionCodec : String := "lean4lean-vexpr-ast-v1"
  theoryTranslation : String := "verify-tr-expr-s-closed-v1"
  deriving Repr, BEq, Lean.ToJson

/-- Exact `Name` serialization, including hygienic and numeric components.

Lean's general `ToJson Name` instance goes through `Name.toString`, which is
not injective for every name. This codec follows `Lean.Idbg.nameToJson`. -/
def nameToJson : Name → Lean.Json
  | .anonymous => .null
  | .str p s => .mkObj [("str", .arr #[nameToJson p, Lean.toJson s])]
  | .num p n => .mkObj [("num", .arr #[nameToJson p, Lean.toJson n])]

def namesToJson (names : List Name) : Lean.Json :=
  .arr <| names.toArray.map nameToJson

def binderInfoToJson : BinderInfo → Lean.Json
  | .default => Lean.toJson "default"
  | .implicit => Lean.toJson "implicit"
  | .strictImplicit => Lean.toJson "strictImplicit"
  | .instImplicit => Lean.toJson "instImplicit"

def literalToJson : Literal → Lean.Json
  | .natVal n => .mkObj [("natVal", Lean.toJson n)]
  | .strVal s => .mkObj [("strVal", Lean.toJson s)]

partial def levelToJson : Level → Lean.Json
  | .zero => .mkObj [("zero", .null)]
  | .succ level => .mkObj [("succ", levelToJson level)]
  | .max left right => .mkObj [("max", .arr #[levelToJson left, levelToJson right])]
  | .imax left right => .mkObj [("imax", .arr #[levelToJson left, levelToJson right])]
  | .param name => .mkObj [("param", nameToJson name)]
  | .mvar id => .mkObj [("mvar", nameToJson id.name)]

/-- Serialize a kernel expression after the documented `mdata` normalization. -/
partial def exprToJson : Expr → Lean.Json
  | .bvar idx => .mkObj [("bvar", Lean.toJson idx)]
  | .fvar id => .mkObj [("fvar", nameToJson id.name)]
  | .mvar id => .mkObj [("mvar", nameToJson id.name)]
  | .sort level => .mkObj [("sort", levelToJson level)]
  | .const name levels => .mkObj [
      ("const", nameToJson name),
      ("levels", .arr <| levels.toArray.map levelToJson)]
  | .app fn arg => .mkObj [("app", .arr #[exprToJson fn, exprToJson arg])]
  | .lam name type body binderInfo => .mkObj [("lam", .mkObj [
      ("name", nameToJson name),
      ("type", exprToJson type),
      ("body", exprToJson body),
      ("binderInfo", binderInfoToJson binderInfo)])]
  | .forallE name type body binderInfo => .mkObj [("forall", .mkObj [
      ("name", nameToJson name),
      ("type", exprToJson type),
      ("body", exprToJson body),
      ("binderInfo", binderInfoToJson binderInfo)])]
  | .letE name type value body nondep => .mkObj [("let", .mkObj [
      ("name", nameToJson name),
      ("type", exprToJson type),
      ("value", exprToJson value),
      ("body", exprToJson body),
      ("nondependent", Lean.toJson nondep)])]
  | .lit literal => .mkObj [("literal", literalToJson literal)]
  | .mdata _ expr => exprToJson expr
  | .proj typeName idx struct => .mkObj [("projection", .mkObj [
      ("typeName", nameToJson typeName),
      ("index", Lean.toJson idx),
      ("structure", exprToJson struct)])]

/-- Structural JSON for the consumer-neutral Theory universe syntax.  Level
parameter names have already been converted to declaration-local ordinals by
`VLevel.ofLevel`, so alpha-renamed universe binders compare exactly. -/
partial def vLevelToJson : VLevel → Lean.Json
  | .zero => .mkObj [("zero", .null)]
  | .succ level => .mkObj [("succ", vLevelToJson level)]
  | .max left right =>
      .mkObj [("max", .arr #[vLevelToJson left, vLevelToJson right])]
  | .imax left right =>
      .mkObj [("imax", .arr #[vLevelToJson left, vLevelToJson right])]
  | .param idx => .mkObj [("param", Lean.toJson idx)]

/-- Structural JSON for the binder-name-free Theory expression syntax. -/
partial def vExprToJson : VExpr → Lean.Json
  | .bvar idx => .mkObj [("bvar", Lean.toJson idx)]
  | .sort level => .mkObj [("sort", vLevelToJson level)]
  | .const name levels => .mkObj [
      ("const", nameToJson name),
      ("levels", .arr <| levels.toArray.map vLevelToJson)]
  | .app fn arg => .mkObj [("app", .arr #[vExprToJson fn, vExprToJson arg])]
  | .lam type body => .mkObj [("lam", .arr #[vExprToJson type, vExprToJson body])]
  | .forallE type body =>
      .mkObj [("forall", .arr #[vExprToJson type, vExprToJson body])]

def vConstValToJson (value : VConstVal) : Lean.Json :=
  .mkObj [
    ("name", nameToJson value.name),
    ("displayName", Lean.toJson value.name.toString),
    ("universeCount", Lean.toJson value.uvars),
    ("type", vExprToJson value.type)]

def vInductiveTypeToJson (value : VInductiveType) : Lean.Json :=
  .mkObj [
    ("name", nameToJson value.name),
    ("displayName", Lean.toJson value.name.toString),
    ("universeCount", Lean.toJson value.uvars),
    ("type", vExprToJson value.type),
    ("constructors", .arr <| value.ctors.toArray.map vConstValToJson)]

def vInductDeclToJson (value : VInductDecl) : Lean.Json :=
  .mkObj [
    ("universeCount", Lean.toJson value.uvars),
    ("parameterCount", Lean.toJson value.nparams),
    ("families", .arr <| value.types.toArray.map vInductiveTypeToJson)]

private structure TranslationBinding where
  value : VExpr
  /-- Lambdas contribute one retained Theory binder; lets contribute none. -/
  depth : Nat

private def lookupTranslationBinding : List TranslationBinding → Nat → Option VExpr
  | [], _ => none
  | binding :: _, 0 => some binding.value
  | binding :: bindings, idx + 1 =>
      (lookupTranslationBinding bindings idx).map (·.liftN binding.depth)

/-- Executable closed-expression fragment of Verify's deterministic
`trExprS?` translation, kept here so the CLI does not import Verify's proof
and axiom closure.  Its small binding environment is the closed-metadata
specialization of `VLCtx.find?`: retained lambdas lift outer values, while
erased lets do not.  Thus malformed loose variables reject just as they do in
Verify.  Free variables, metavariables, and projections remain outside this
fragment. -/
private partial def exprToVExprCore (levelParams : List Name)
    (bindings : List TranslationBinding) : Expr → Except String VExpr
  | .bvar idx =>
      match lookupTranslationBinding bindings idx with
      | some translated => pure translated
      | none => throw s!"loose bound variable {idx} in closed metadata"
  | .fvar id => throw s!"unexpected free variable {id.name} in closed metadata"
  | .mvar id => throw s!"unexpected metavariable {id.name} in closed metadata"
  | .sort level =>
      match VLevel.ofLevel levelParams level with
      | some translated => pure (.sort translated)
      | none => throw s!"untranslatable universe level {level}"
  | .const name levels => do
      let some translated := levels.mapM (VLevel.ofLevel levelParams)
        | throw s!"untranslatable universe argument of {name}"
      pure (.const name translated)
  | .app fn arg => do
      pure (.app (← exprToVExprCore levelParams bindings fn)
        (← exprToVExprCore levelParams bindings arg))
  | .lam _ type body _ => do
      let type ← exprToVExprCore levelParams bindings type
      let body ← exprToVExprCore levelParams
        ({ value := .bvar 0, depth := 1 } :: bindings) body
      pure (.lam type body)
  | .forallE _ type body _ => do
      let type ← exprToVExprCore levelParams bindings type
      let body ← exprToVExprCore levelParams
        ({ value := .bvar 0, depth := 1 } :: bindings) body
      pure (.forallE type body)
  | .letE _ _ value body _ => do
      let value ← exprToVExprCore levelParams bindings value
      exprToVExprCore levelParams ({ value, depth := 0 } :: bindings) body
  | .lit literal => exprToVExprCore levelParams bindings literal.toConstructor
  | .mdata _ expr => exprToVExprCore levelParams bindings expr
  | .proj typeName idx _ =>
      throw s!"projection {typeName}.{idx} is outside the strict closed translation fragment"

def exprToVExpr (levelParams : List Name) (expr : Expr) : Except String VExpr :=
  exprToVExprCore levelParams [] expr

def inductiveBlockToVExpr (levelParams : List Name) (parameterCount : Nat)
    (types : List InductiveType) : Except String VInductDecl := do
  let universeCount := levelParams.length
  let families ← types.mapM fun family => do
    let familyType ← exprToVExpr levelParams family.type
      |>.mapError fun error => s!"family {family.name}: {error}"
    let constructors ← family.ctors.mapM fun constructor => do
      let constructorType ← exprToVExpr levelParams constructor.type
        |>.mapError fun error => s!"constructor {constructor.name}: {error}"
      pure {
        name := constructor.name
        uvars := universeCount
        type := constructorType
      }
    pure {
      name := family.name
      uvars := universeCount
      type := familyType
      ctors := constructors
    }
  pure { uvars := universeCount, nparams := parameterCount, types := families }

def reducibilityHintsToJson : ReducibilityHints → Lean.Json
  | .opaque => Lean.toJson "opaque"
  | .abbrev => Lean.toJson "abbrev"
  | .regular height => .mkObj [("regular", Lean.toJson height.toNat)]

def definitionSafetyToJson : DefinitionSafety → Lean.Json
  | .unsafe => Lean.toJson "unsafe"
  | .safe => Lean.toJson "safe"
  | .partial => Lean.toJson "partial"

def quotientKindToJson : QuotKind → Lean.Json
  | .type => Lean.toJson "type"
  | .ctor => Lean.toJson "constructor"
  | .lift => Lean.toJson "lift"
  | .ind => Lean.toJson "induction"

def recursorRuleToJson (rule : RecursorRule) : Lean.Json :=
  .mkObj [
    ("constructor", nameToJson rule.ctor),
    ("fieldCount", Lean.toJson rule.nfields),
    ("rhs", exprToJson rule.rhs)]

/-- One iota rule after translation to the Theory syntax. -/
structure TheoryRuleSnapshot where
  constructor : Lean.Json
  displayConstructor : String
  fieldCount : Nat
  rhs : Lean.Json
  deriving BEq, Lean.ToJson

/-- Kernel-observable recursor metadata expressed in the Theory syntax. -/
structure TheoryRecursorSnapshot where
  name : Lean.Json
  displayName : String
  universeCount : Nat
  typeExpr : Lean.Json
  mutualNames : Lean.Json
  parameterCount : Nat
  indexCount : Nat
  motiveCount : Nat
  minorCount : Nat
  k : Bool
  isUnsafe : Bool
  rules : Array TheoryRuleSnapshot
  deriving BEq, Lean.ToJson

/-- One Theory-generated recursor paired with Lean's stored raw recursor. -/
structure TheoryRecursorComparison where
  name : Lean.Json
  displayName : String
  theory : TheoryRecursorSnapshot
  kernel : Option TheoryRecursorSnapshot
  normalizedEqual : Bool
  deriving BEq, Lean.ToJson

/-- Cross-phase observation for the exact selected inductive block. -/
structure TheoryBlockComparison where
  families : Lean.Json
  transformation : String
  auxiliaryFamilyCount : Nat
  kernelAuxiliaryFamilyCount : Nat
  source : Lean.Json
  normalized : Lean.Json
  normalizationChanged : Bool
  theoryRecursive : Bool
  kernelRecursive : Array Bool
  theoryReflexive : Bool
  kernelReflexive : Array Bool
  recursors : Array TheoryRecursorComparison
  normalizedEqual : Bool
  deriving BEq, Lean.ToJson

/-- A classified failure before cross-phase metadata comparison. -/
structure PhaseFailure where
  phase : Phase
  diagnostic : String
  deriving Repr, Inhabited

/-- A normalized, machine-comparable snapshot of one raw environment entry. -/
structure DeclarationSnapshot where
  name : Lean.Json
  displayName : String
  kind : String
  levelParameters : Lean.Json
  typeExpr : Lean.Json
  valueExpr : Option Lean.Json
  metadata : Lean.Json
  /-- Field ordinals are present for constructors. -/
  fieldPositions : Option (Array Nat) := none
  /-- Filled by the later translation/analyzer phase; raw `ConstantInfo` does not store it. -/
  recursivePositions : Option (Array Nat) := none
  deriving BEq, Lean.ToJson

def ConstantInfo.toDifferentialSnapshot (info : ConstantInfo)
    (recursivePositions : Option (Array Nat) := none) : DeclarationSnapshot :=
  let base : DeclarationSnapshot := {
    name := nameToJson info.name
    displayName := info.name.toString
    kind := ""
    levelParameters := namesToJson info.levelParams
    typeExpr := exprToJson info.type
    valueExpr := info.value? (allowOpaque := true) |>.map exprToJson
    metadata := .null
  }
  match info with
  | .axiomInfo val => { base with
      kind := "axiom"
      metadata := .mkObj [("unsafe", Lean.toJson val.isUnsafe)] }
  | .defnInfo val => { base with
      kind := "definition"
      metadata := .mkObj [
        ("reducibility", reducibilityHintsToJson val.hints),
        ("safety", definitionSafetyToJson val.safety),
        ("mutual", namesToJson val.all)] }
  | .thmInfo val => { base with
      kind := "theorem"
      metadata := .mkObj [("mutual", namesToJson val.all)] }
  | .opaqueInfo val => { base with
      kind := "opaque"
      metadata := .mkObj [
        ("unsafe", Lean.toJson val.isUnsafe),
        ("mutual", namesToJson val.all)] }
  | .quotInfo val => { base with
      kind := "quotient"
      metadata := .mkObj [("quotientKind", quotientKindToJson val.kind)] }
  | .inductInfo val => { base with
      kind := "inductive"
      metadata := .mkObj [
        ("parameterCount", Lean.toJson val.numParams),
        ("indexCount", Lean.toJson val.numIndices),
        ("mutual", namesToJson val.all),
        ("constructors", namesToJson val.ctors),
        ("nestedCount", Lean.toJson val.numNested),
        ("recursive", Lean.toJson val.isRec),
        ("unsafe", Lean.toJson val.isUnsafe),
        ("reflexive", Lean.toJson val.isReflexive)] }
  | .ctorInfo val => { base with
      kind := "constructor"
      metadata := .mkObj [
        ("inductive", nameToJson val.induct),
        ("constructorIndex", Lean.toJson val.cidx),
        ("parameterCount", Lean.toJson val.numParams),
        ("fieldCount", Lean.toJson val.numFields),
        ("unsafe", Lean.toJson val.isUnsafe)]
      fieldPositions := some <| List.range val.numFields |>.toArray
      recursivePositions }
  | .recInfo val => { base with
      kind := "recursor"
      metadata := .mkObj [
        ("mutual", namesToJson val.all),
        ("parameterCount", Lean.toJson val.numParams),
        ("indexCount", Lean.toJson val.numIndices),
        ("motiveCount", Lean.toJson val.numMotives),
        ("minorCount", Lean.toJson val.numMinors),
        ("k", Lean.toJson val.k),
        ("unsafe", Lean.toJson val.isUnsafe),
        ("ruleCount", Lean.toJson val.rules.length),
        ("rules", .arr <| val.rules.toArray.map recursorRuleToJson)] }

/-- Raw input metadata paired with the metadata produced by replay. -/
structure ConstantComparison where
  name : Lean.Json
  displayName : String
  source : DeclarationSnapshot
  /-- `none` records an expected generated entry that replay omitted entirely. -/
  replayed : Option DeclarationSnapshot
  normalizedEqual : Bool
  deriving BEq, Lean.ToJson

structure Input where
  source : Option String := none
  module : String
  declaration : String
  fresh : Bool
  deriving Repr, BEq, Lean.ToJson

/-- Machine-readable observation emitted for every differential invocation. -/
structure Result where
  schema : String := Differential.schema
  version : Nat := Differential.schemaVersion
  caseId : Option String := none
  input : Input
  outcome : Outcome
  phase : Phase
  checked : Nat := 0
  diagnostic : Option String := none
  metadataEqual : Option Bool := none
  normalization : NormalizationPolicy := {}
  generatedConstants : Array ConstantComparison := #[]
  theoryBlocks : Array TheoryBlockComparison := #[]
  deriving Lean.ToJson

def Result.rejected (input : Input) (phase : Phase) (diagnostic : String)
    (caseId : Option String := none) : Result := {
  caseId
  input
  outcome := .rejected
  phase
  diagnostic := some diagnostic
}

/-- A serialized result is safe to return after the compacted `.olean`
regions that supplied its metadata have been released. -/
structure Emission where
  json : String
  outcome : Outcome
  phase : Phase
  deriving Repr, Inhabited

def Result.fromComparisons (input : Input) (checked : Nat)
    (comparisons : Array ConstantComparison)
    (theoryBlocks : Array TheoryBlockComparison := #[])
    (analysisFailure : Option PhaseFailure := none)
    (caseId : Option String := none) : Result :=
  let mismatches := comparisons.filter (!·.normalizedEqual)
  let theoryMismatches := theoryBlocks.filter (!·.normalizedEqual)
  if let some failure := analysisFailure then {
    caseId
    input
    outcome := .rejected
    phase := failure.phase
    checked
    diagnostic := some failure.diagnostic
    metadataEqual := some mismatches.isEmpty
    generatedConstants := comparisons
    theoryBlocks
  } else if mismatches.isEmpty && theoryMismatches.isEmpty then {
    caseId
    input
    outcome := .accepted
    phase := .metadataComparison
    checked
    metadataEqual := some true
    generatedConstants := comparisons
    theoryBlocks
  } else {
    caseId
    input
    outcome := .rejected
    phase := .metadataComparison
    checked
    diagnostic := some <| String.intercalate "; " <| [
      if mismatches.isEmpty then none else some s!"kernel replay differs for: {
        String.intercalate ", " <| mismatches.toList.map (·.displayName)}",
      if theoryMismatches.isEmpty then none else some s!"Theory generation differs for: {
        String.intercalate ", " <| theoryMismatches.toList.map fun block =>
          (block.recursors.find? (!·.normalizedEqual)).map (·.displayName)
            |>.getD "[block metadata]"}"
    ].filterMap id
    metadataEqual := some false
    generatedConstants := comparisons
    theoryBlocks
  }

def Result.emit (result : Result) : Emission := {
  json := (Lean.toJson result).compress
  outcome := result.outcome
  phase := result.phase
}

end Lean4Lean.Differential

namespace Lean4Lean.Replay

structure Context where
  newConstants : Std.HashMap Name ConstantInfo
  verbose := false
  compare := false
  checkQuot := true
  fuel : Lean4Lean.FuelConfig := {}
  /-- Selected declaration whose pre-inductive environment is retained for
  differential normalization.  It is `none` during ordinary bulk replay. -/
  analysisDecl : Option Name := none

structure State where
  env : Environment
  remaining : NameSet := {}
  pending : NameSet := {}
  postponedConstructors : NameSet := {}
  postponedRecursors : NameSet := {}
  numAdded : Nat := 0
  hasStrings := false
  analysisBase : Option Environment := none

abbrev M := ReaderT Context <| StateRefT State IO

/-- Check if a `Name` still needs processing. If so, move it from `remaining` to `pending`. -/
def isTodo (name : Name) : M Bool := do
  let r := (← get).remaining
  if r.contains name then
    modify fun s => { s with remaining := s.remaining.erase name, pending := s.pending.insert name }
    return true
  else
    return false


/-- Use the current `Environment` to throw a `Kernel.Exception`. -/
def throwKernelException (ex : Exception) : M α := do
  let options := pp.match.set (pp.rawOnError.set {} true) false
  -- Note: because the environment we are using has no extension state,
  -- we cannot safely use it with lean functions like the pretty printer.
  -- Here we instead create a fresh environment, which is good enough to get
  -- basic pretty printing working.
  let env ← mkEmptyEnvironment
  let ex ← ex.mapEnvM fun _ => return env.toKernelEnv
  Prod.fst <$> (Lean.Core.CoreM.toIO · { fileName := "", options, fileMap := default } { env }) do
    Lean.throwKernelException ex


/-- Add a declaration, possibly throwing a `KernelException`. -/
def addDecl (d : Declaration) : M Unit := do
  if (← read).verbose then
    println! "adding {d.name}"
  let t1 ← IO.monoMsNow
  match Lean4Lean.addDecl (← get).env d true (fuel := (← read).fuel) with
  | .ok env =>
    let t2 ← IO.monoMsNow
    if t2 - t1 > 1000 then
      if (← read).compare then
        let t3 ← match (← get).env.addDecl {} d with
        | .ok _ => IO.monoMsNow
        | .error ex => Lean4Lean.Replay.throwKernelException ex
        if (t2 - t1) > 2 * (t3 - t2) then
          println!
            "{(← get).env.header.mainModule}:{d.name}: lean took {t3 - t2}, lean4lean took {t2 - t1}"
        else
          println! "{(← get).env.header.mainModule}:{d.name}: lean4lean took {t2 - t1}"
      else
        println! "{(← get).env.header.mainModule}:{d.name}: lean4lean took {t2 - t1}"
    modify fun s => { s with env, numAdded := s.numAdded + 1 }
  | .error ex =>
    throwKernelException ex

deriving instance BEq for ConstantVal
deriving instance BEq for ConstructorVal
deriving instance BEq for RecursorRule
deriving instance BEq for RecursorVal



mutual
/--
Check if a `Name` still needs to be processed (i.e. is in `remaining`).

If so, recursively replay any constants it refers to,
to ensure we add declarations in the right order.

The construct the `Declaration` from its stored `ConstantInfo`,
and add it to the environment.
-/
partial def replayConstant (name : Name) : M Unit := do
  if ← isTodo name then
    let some ci := (← read).newConstants[name]? | unreachable!
    let mut usedConstants := ci.getUsedConstants
    -- We want `String.ofList` to be available when encountering string literals.
    -- Presumably faster to first check if we already have it, before traversing
    -- the declaration
    unless (← get).hasStrings do
      if ci.hasStrLit then
        usedConstants := usedConstants.insert ``String.ofList
        usedConstants := usedConstants.insert ``Char.ofNat
        modify ({· with hasStrings := true })
    replayConstants usedConstants
    -- Check that this name is still pending: a mutual block may have taken care of it.
    if (← get).pending.contains name then
      let addDeclAt (d : Declaration) :=
        try addDecl d catch e => throw <| IO.userError s!"at {name}: {e.toString}"
      match ci with
      | .defnInfo   info => addDeclAt (.defnDecl   info)
      | .thmInfo    info => addDeclAt (.thmDecl    info)
      | .axiomInfo  info => addDeclAt (.axiomDecl  info)
      | .opaqueInfo info => addDeclAt (.opaqueDecl info)
      | .inductInfo info =>
        let lparams := info.levelParams
        let nparams := info.numParams
        let all ← info.all.mapM fun n => do pure <| (← read).newConstants[n]!
        for o in all do
          modify fun s =>
            { s with remaining := s.remaining.erase o.name, pending := s.pending.erase o.name }
        let ctorInfo ← all.mapM fun ci => do
          pure (ci, ← ci.inductiveVal!.ctors.mapM fun n => do
            pure (← read).newConstants[n]!)
        -- Make sure we are really finished with the constructors.
        for (_, ctors) in ctorInfo do
          for ctor in ctors do
            replayConstants ctor.getUsedConstants
        if (← read).analysisDecl.any (info.all.contains ·) then
          modify fun s => { s with analysisBase := some s.env }
        let types : List InductiveType := ctorInfo.map fun ⟨ci, ctors⟩ =>
          { name := ci.name
            type := ci.type
            ctors := ctors.map fun ci => { name := ci.name, type := ci.type } }
        addDeclAt (.inductDecl lparams nparams types false)
      -- We postpone checking constructors,
      -- and at the end make sure they are identical
      -- to the constructors generated when we replay the inductives.
      | .ctorInfo info =>
        modify fun s => { s with postponedConstructors := s.postponedConstructors.insert info.name }
      -- Similarly we postpone checking recursors.
      | .recInfo info =>
        modify fun s => { s with postponedRecursors := s.postponedRecursors.insert info.name }
      | .quotInfo _ =>
        replayConstant ``Eq
        addDeclAt .quotDecl
      modify fun s => { s with pending := s.pending.erase name }

/-- Replay a set of constants one at a time. -/
partial def replayConstants (names : NameSet) : M Unit := do
  for n in names do replayConstant n

end

/--
Check that all postponed constructors are identical to those generated
when we replayed the inductives.
-/
def checkPostponedConstructors : M Unit := do
  for ctor in (← get).postponedConstructors do
    match (← get).env.constants.find? ctor, (← read).newConstants[ctor]? with
    | some (.ctorInfo info), some (.ctorInfo info') =>
      unless info == info' do throw <| IO.userError s!"Invalid constructor {ctor}"
    | _, _ => throw <| IO.userError s!"No such constructor {ctor}"

/--
Check that all postponed recursors are identical to those generated
when we replayed the inductives.
-/
def checkPostponedRecursors : M Unit := do
  for ctor in (← get).postponedRecursors do
    match (← get).env.constants.find? ctor, (← read).newConstants[ctor]? with
    | some (.recInfo info), some (.recInfo info') =>
      unless info == info' do throw <| IO.userError s!"Invalid recursor {ctor}"
    | _, _ => throw <| IO.userError s!"No such recursor {ctor}"

/--
Check that at the end of (any) file, the quotient module is initialized by the end.
(It will already be initialized at the beginning, unless this is the very first file,
`Init.Core`, which is responsible for initializing it.)
This is needed because it is an assumption in `finalizeImport`.
-/
def checkQuotInit : M Unit := do
  unless (← get).env.quotInit do
    throw <| IO.userError s!"initial import (Init.Prelude) didn't initialize quotient module"

private def kernelRecursorTheorySnapshot (info : RecursorVal) :
    Except String Differential.TheoryRecursorSnapshot := do
  let typeExpr ← Differential.exprToVExpr info.levelParams info.type
    |>.mapError fun error => s!"recursor {info.name} type: {error}"
  let rules ← info.rules.mapM fun rule => do
    let rhs ← Differential.exprToVExpr info.levelParams rule.rhs
      |>.mapError fun error => s!"recursor {info.name}, rule {rule.ctor}: {error}"
    pure {
      constructor := Differential.nameToJson rule.ctor
      displayConstructor := rule.ctor.toString
      fieldCount := rule.nfields
      rhs := Differential.vExprToJson rhs
    }
  pure {
    name := Differential.nameToJson info.name
    displayName := info.name.toString
    universeCount := info.levelParams.length
    typeExpr := Differential.vExprToJson typeExpr
    mutualNames := Differential.namesToJson info.all
    parameterCount := info.numParams
    indexCount := info.numIndices
    motiveCount := info.numMotives
    minorCount := info.numMinors
    k := info.k
    isUnsafe := info.isUnsafe
    rules := rules.toArray
  }

private def kernelExceptionSummary : Exception → String
  | .unknownConstant _ name => s!"unknown constant {name}"
  | .alreadyDeclared _ name => s!"constant already declared: {name}"
  | .declTypeMismatch _ declaration _ => s!"declaration type mismatch: {declaration.name}"
  | .declHasMVars _ name _ => s!"declaration {name} contains metavariables"
  | .declHasFVars _ name _ => s!"declaration {name} contains free variables"
  | .funExpected .. => "function expected"
  | .typeExpected .. => "type expected"
  | .letTypeMismatch .. => "let type mismatch"
  | .exprTypeMismatch .. => "expression type mismatch"
  | .appTypeMismatch .. => "application type mismatch"
  | .invalidProj .. => "invalid projection"
  | .thmTypeIsNotProp _ name _ => s!"theorem {name} does not have a proposition type"
  | .other message => message
  | .deterministicTimeout => "deterministic timeout"
  | .excessiveMemory => "excessive memory"
  | .deepRecursion => "deep recursion"
  | .interrupted => "interrupted"

/-- Source records for one stored mutual block, reconstructed without trusting
the selected family to duplicate constructor payloads for its siblings. -/
private def sourceInductiveInfo (ctx : Context) (name : Name) :
    Except String InductiveVal :=
  match ctx.newConstants[name]? with
  | some (ConstantInfo.inductInfo family) => pure family
  | _ => throw s!"missing inductive family metadata for {name}"

private def sourceConstructorInfo (ctx : Context) (name : Name) :
    Except String ConstructorVal :=
  match ctx.newConstants[name]? with
  | some (ConstantInfo.ctorInfo constructor) => pure constructor
  | _ => throw s!"missing constructor metadata for {name}"

private def sourceInductiveBlock (ctx : Context) (selected : InductiveVal) :
    Except String (List InductiveType × List InductiveVal) := do
  let records : List (InductiveType × InductiveVal) ← selected.all.mapM fun familyName => do
    let family ← sourceInductiveInfo ctx familyName
    unless family.levelParams == selected.levelParams do
      throw s!"mutual family {familyName} has inconsistent universe parameters"
    unless family.numParams == selected.numParams do
      throw s!"mutual family {familyName} has inconsistent parameter count"
    unless family.all == selected.all do
      throw s!"mutual family {familyName} has an inconsistent family inventory"
    unless family.numNested == selected.numNested do
      throw s!"mutual family {familyName} has an inconsistent nested-family count"
    unless family.isUnsafe == selected.isUnsafe do
      throw s!"mutual family {familyName} has inconsistent safety metadata"
    let constructors ← family.ctors.mapM fun constructorName => do
      let constructor ← sourceConstructorInfo ctx constructorName
      unless constructor.induct == family.name do
        throw s!"constructor {constructorName} names {constructor.induct}, not {family.name}, as owner"
      pure ({ name := constructor.name, type := constructor.type } : Constructor)
    pure (({ name := family.name, type := family.type, ctors := constructors } : InductiveType),
      family)
  pure (records.map (·.1), records.map (·.2))

private def environmentInductiveBlock (env : Environment) (selected : InductiveVal) :
    Except String (List InductiveType) := do
  selected.all.mapM fun familyName => do
    let family ← match env.find? familyName with
      | some (ConstantInfo.inductInfo family) => pure family
      | _ => throw s!"missing nested-target family metadata for {familyName}"
    unless family.levelParams == selected.levelParams &&
        family.numParams == selected.numParams && family.all == selected.all do
      throw s!"nested-target mutual metadata is inconsistent at {familyName}"
    let constructors ← family.ctors.mapM fun constructorName => do
      let constructor ← match env.find? constructorName with
        | some (ConstantInfo.ctorInfo constructor) => pure constructor
        | _ => throw s!"missing nested-target constructor metadata for {constructorName}"
      unless constructor.induct == family.name do
        throw s!"nested-target constructor {constructorName} has inconsistent ownership"
      pure ({ name := constructor.name, type := constructor.type } : Constructor)
    pure ({ name := family.name, type := family.type, ctors := constructors } : InductiveType)

/-- Discover complete previously declared target blocks from constants used by
the source metadata.  Supplying a non-nested inductive is harmless: the Theory
transformer selects a target only when its parameter spine mentions the new
block. -/
private def nestedTargetBlocks (initial : Environment) (types : List InductiveType) :
    Except String (List VInductDecl.NestedTargetBlock) := do
  let mut used : NameSet := {}
  for family in types do
    used := used ++ family.type.getUsedConstants'
    for constructor in family.ctors do
      used := used ++ constructor.type.getUsedConstants'
  let mut seen : NameSet := {}
  let mut targets := []
  for name in used do
    match initial.find? name with
    | some (ConstantInfo.inductInfo target) =>
        if 0 < target.numParams && !seen.contains target.name then
          let raw ← environmentInductiveBlock initial target
          let translated ← Differential.inductiveBlockToVExpr target.levelParams
            target.numParams raw
          targets := targets ++ [{ nparams := target.numParams, families := translated.types }]
          seen := target.all.foldl NameSet.insert seen
    | _ => pure ()
  pure targets

structure AnalysisArtifacts where
  theoryBlocks : Array Differential.TheoryBlockComparison := #[]
  recursivePositions : Std.HashMap Name (Array Nat) := {}

private def restoredNestedConstructorName {source : VInductDecl}
    (nested : source.NestedBlockChecked) (name : Name) : Name :=
  match VInductDecl.findRestoreCtor nested.declEntries name with
  | some (entry, suffix) =>
      match VExpr.appHead entry.value with
      | .const target _ => target ++ suffix
      | _ => name
  | none => name

private def compareTheoryBlock {generationSource : VInductDecl}
    (ctx : Context) (selected : InductiveVal) (familyInfos : List InductiveVal)
    (source transformed : VInductDecl) (transformation : String)
    (auxiliaryFamilyCount : Nat)
    (generation : generationSource.BlockGenerationChecked)
    (generatedRecursors : List VConstVal) (generatedRules : List VDefEq)
    (ruleConstructorNames : List Name) :
    Except Differential.PhaseFailure AnalysisArtifacts := do
  unless generatedRecursors.length == generation.families.length do
    throw {
      phase := .theoryGeneration
      diagnostic := s!"Theory generated {generatedRecursors.length} recursors for {
        generation.families.length} families"
    }
  let flattenedConstructors := generation.flatCtors
  unless generatedRules.length == flattenedConstructors.length do
    throw {
      phase := .theoryGeneration
      diagnostic := s!"Theory generated {generatedRules.length} rules for {
        flattenedConstructors.length} constructors"
    }
  unless ruleConstructorNames.length == flattenedConstructors.length do
    throw {
      phase := .theoryGeneration
      diagnostic := s!"Theory retained {ruleConstructorNames.length} restored constructor names for {
        flattenedConstructors.length} rules"
    }
  let mut recursivePositions : Std.HashMap Name (Array Nat) := {}
  for constructor in flattenedConstructors do
    recursivePositions := recursivePositions.insert constructor.ctor.raw.name <|
      constructor.ctor.view.recursive.map (·.fieldIndex) |>.toArray
  let generatedRuleRows := (flattenedConstructors.zip generatedRules).zip ruleConstructorNames
  let mutualNames := source.types.map (·.name)
  let mut recursors := #[]
  for family in generation.families, generatedRecursor in generatedRecursors do
    let rules := generatedRuleRows.filterMap fun ((constructor, rule), constructorName) =>
      if constructor.owner == family.view.ordinal then some {
        constructor := Differential.nameToJson constructorName
        displayConstructor := constructorName.toString
        fieldCount := constructor.ctor.view.fields.length
        rhs := Differential.vExprToJson rule.rhs
      } else none
    let familyIsUnsafe := familyInfos[family.view.ordinal]? |>.map (·.isUnsafe)
      |>.getD selected.isUnsafe
    let theory : Differential.TheoryRecursorSnapshot := {
      name := Differential.nameToJson generatedRecursor.name
      displayName := generatedRecursor.name.toString
      universeCount := generatedRecursor.uvars
      typeExpr := Differential.vExprToJson generatedRecursor.type
      mutualNames := Differential.namesToJson mutualNames
      parameterCount := source.nparams
      indexCount := family.view.indices.length
      motiveCount := generation.familyCount
      minorCount := generation.minorCount
      k := generation.kTarget
      isUnsafe := familyIsUnsafe
      rules := rules.toArray
    }
    let kernel ← match ctx.newConstants[generatedRecursor.name]? with
      | some (.recInfo info) =>
          (kernelRecursorTheorySnapshot info).map some |>.mapError fun error => {
            phase := .rawTranslation
            diagnostic := error
          }
      | _ => pure none
    recursors := recursors.push {
      name := Differential.nameToJson generatedRecursor.name
      displayName := generatedRecursor.name.toString
      theory
      kernel
      normalizedEqual := kernel.any (theory == ·)
    }
  let kernelRecursive := familyInfos.toArray.map (·.isRec)
  let kernelReflexive := familyInfos.toArray.map (·.isReflexive)
  let recursiveEqual := kernelRecursive.size == source.types.length &&
    kernelRecursive.all (· == generation.isRec)
  let reflexiveEqual := kernelReflexive.size == source.types.length &&
    kernelReflexive.all (· == generation.isReflexive)
  let recursorsEqual := recursors.size == generation.familyCount &&
    recursors.all (·.normalizedEqual)
  let shapeEqual := generation.familyCount == source.types.length + auxiliaryFamilyCount
  let auxiliaryEqual := auxiliaryFamilyCount == selected.numNested
  let sourceJson := Differential.vInductDeclToJson source
  let normalizedJson := Differential.vInductDeclToJson transformed
  let comparison : Differential.TheoryBlockComparison := {
    families := Differential.namesToJson mutualNames
    transformation
    auxiliaryFamilyCount
    kernelAuxiliaryFamilyCount := selected.numNested
    source := sourceJson
    normalized := normalizedJson
    normalizationChanged := sourceJson != normalizedJson
    theoryRecursive := generation.isRec
    kernelRecursive
    theoryReflexive := generation.isReflexive
    kernelReflexive
    recursors
    normalizedEqual := shapeEqual && auxiliaryEqual && recursiveEqual &&
      reflexiveEqual && recursorsEqual
  }
  pure { theoryBlocks := #[comparison], recursivePositions }

private def analyzeInductiveBlock (ctx : Context) (initial : Environment)
    (selected : InductiveVal) :
    Except Differential.PhaseFailure AnalysisArtifacts := do
  let (types, familyInfos) ← sourceInductiveBlock ctx selected |>.mapError fun error => {
    phase := .rawTranslation
    diagnostic := error
  }
  let source ← Differential.inductiveBlockToVExpr selected.levelParams selected.numParams types
    |>.mapError fun error => {
      phase := .rawTranslation
      diagnostic := error
    }
  let allowPrimitive ←
    Lean4Lean.Environment.checkPrimitiveInductive initial selected.levelParams
      selected.numParams types selected.isUnsafe
    |>.mapError fun error => {
      phase := .normalization
      diagnostic := s!"primitive classification failed for {selected.name}: {
        kernelExceptionSummary error}"
    }
  let candidateContext : AddInductive.Context := {
    env := initial
    lparams := selected.levelParams
    safety := if selected.isUnsafe then .unsafe else .safe
    allowPrimitive
    fuel := ctx.fuel
  }
  if selected.numNested == 0 then
    let candidate ←
      AddInductive.buildNormalizationCandidate selected.numParams types 0
        selected.isUnsafe candidateContext
      |>.mapError fun error => {
        phase := .normalization
        diagnostic := s!"normalization candidate failed for {selected.name}: {
          kernelExceptionSummary error}"
      }
    let normalized ←
      Differential.inductiveBlockToVExpr selected.levelParams selected.numParams candidate.view
      |>.mapError fun error => {
        phase := .normalization
        diagnostic := s!"normalized view for {selected.name}: {error}"
      }
    let some block := VInductDecl.normalizedCheckedBlock? source normalized
      | throw {
          phase := .theoryGeneration
          diagnostic := s!"Theory rejected the normalized block containing {selected.name}"
        }
    let validated : source.ValidatedBlock := {
      block
      resultLevel := block.checked.firstResultLevel
    }
    let some generation := validated.generation?
      | throw {
          phase := .theoryGeneration
          diagnostic := s!"Theory generation-shape check rejected the block containing {selected.name}"
        }
    compareTheoryBlock ctx selected familyInfos source normalized "normalization" 0
      generation generation.recursors generation.generatedRules
      (generation.flatCtors.map (·.ctor.raw.name))
  else
    let targets ← nestedTargetBlocks initial types |>.mapError fun error => {
      phase := .rawTranslation
      diagnostic := s!"nested target translation for {selected.name}: {error}"
    }
    let some elimination := VInductDecl.nestedElimination? targets source ctx.fuel.inductiveFuel
      | throw {
          phase := .normalization
          diagnostic := s!"Theory nested elimination rejected the block containing {selected.name}"
        }
    let portNested ← ElimNestedInductive.runAt initial ctx.fuel.inductiveFuel
      selected.numParams selected.levelParams types
      |>.mapError fun error => {
        phase := .normalization
        diagnostic := s!"kernel-port nested elimination failed for {selected.name}: {
          kernelExceptionSummary error}"
      }
    let portFlat ← Differential.inductiveBlockToVExpr selected.levelParams
      selected.numParams portNested.types |>.mapError fun error => {
        phase := .normalization
        diagnostic := s!"kernel-port flattened view for {selected.name}: {error}"
      }
    unless Differential.vInductDeclToJson portFlat ==
        Differential.vInductDeclToJson elimination.flat do
      throw {
        phase := .normalization
        diagnostic := s!"Theory and kernel-port nested elimination differ for {selected.name}"
      }
    let candidate ←
      AddInductive.buildNormalizationCandidate selected.numParams portNested.types
        portNested.aux2nested.size selected.isUnsafe candidateContext
      |>.mapError fun error => {
        phase := .normalization
        diagnostic := s!"flattened normalization candidate failed for {selected.name}: {
          kernelExceptionSummary error}"
      }
    let normalized ← Differential.inductiveBlockToVExpr selected.levelParams
      selected.numParams candidate.view |>.mapError fun error => {
        phase := .normalization
        diagnostic := s!"normalized nested view for {selected.name}: {error}"
      }
    let some block := VInductDecl.normalizedCheckedBlock? elimination.flat normalized
      | throw {
          phase := .theoryGeneration
          diagnostic := s!"Theory rejected the normalized nested block containing {selected.name}"
        }
    let validated : elimination.flat.ValidatedBlock := {
      block
      resultLevel := block.checked.firstResultLevel
    }
    let some generation := validated.generation?
      | throw {
          phase := .theoryGeneration
          diagnostic := s!"Theory generation-shape check rejected the nested block containing {
            selected.name}"
        }
    if sourceRestoreSafe : source.nestedRestoreSafe elimination.specs = true then
      let nested : source.NestedBlockChecked := {
        elim := elimination
        generation
        source_restore_safe := sourceRestoreSafe }
      compareTheoryBlock ctx selected familyInfos source normalized
        "nested-elimination+normalization" elimination.numNested generation
        nested.recursors nested.generatedRules
        (generation.flatCtors.map fun constructor =>
          restoredNestedConstructorName nested constructor.ctor.raw.name)
    else
      throw {
        phase := .theoryGeneration
        diagnostic := s!"Theory restoration-safety check rejected the nested block containing {
          selected.name}"
      }

private def analyzeSelectedInductive (ctx : Context) (initial : Environment)
    (decl : Name) : Except Differential.PhaseFailure AnalysisArtifacts :=
  match ctx.newConstants[decl]? with
  | some (.inductInfo selected) => analyzeInductiveBlock ctx initial selected
  | _ => pure {}

/-- "Replay" some constants into an `Environment`, sending them to the kernel for checking. -/
structure DetailedResult where
  numAdded : Nat
  env : Environment
  comparisons : Array Differential.ConstantComparison := #[]
  theoryBlocks : Array Differential.TheoryBlockComparison := #[]
  analysisFailure : Option Differential.PhaseFailure := none

/-- Compare every source entry materialized by a successful replay with the
entry produced by the kernel. Imported entries already present in `initial`
are excluded, so this is also the exact generated-constant set for the run. -/
def compareGeneratedConstants (ctx : Context) (initial replayed : Environment)
    (recursivePositions : Std.HashMap Name (Array Nat) := {}) :
    Array Differential.ConstantComparison := Id.run do
  let entries := ctx.newConstants.toList.toArray.qsort fun left right =>
    Name.lt left.1 right.1
  let mut expected : NameSet := {}
  let mut materializedInductiveBlocks : Array (List Name) := #[]
  let mut quotientMaterialized := false
  for (name, sourceInfo) in entries do
    if (initial.constants.find? name).isNone && (replayed.constants.find? name).isSome then
      expected := expected.insert name
      match sourceInfo with
      | .inductInfo info =>
        materializedInductiveBlocks := materializedInductiveBlocks.push info.all
        expected := info.all.foldl NameSet.insert expected
        expected := info.ctors.foldl NameSet.insert expected
      | .quotInfo _ => quotientMaterialized := true
      | _ => pure ()
  -- Constructors are named by `InductiveVal`; recursors are related to their
  -- source block only through `RecursorVal.all`, so collect those explicitly.
  -- Quotient initialization similarly generates its four raw entries as one
  -- kernel declaration.
  for (name, sourceInfo) in entries do
    match sourceInfo with
    | .recInfo info =>
      if materializedInductiveBlocks.any (info.all == ·) then
        expected := expected.insert name
    | .quotInfo _ =>
      if quotientMaterialized then expected := expected.insert name
    | _ => pure ()
  let mut comparisons := #[]
  for (name, sourceInfo) in entries do
    if expected.contains name then
      let positions := recursivePositions[name]?
      let source := Differential.ConstantInfo.toDifferentialSnapshot sourceInfo positions
      let replayed := replayed.constants.find? name |>.map
        (Differential.ConstantInfo.toDifferentialSnapshot · positions)
      comparisons := comparisons.push {
        name := Differential.nameToJson name
        displayName := name.toString
        source
        replayed
        normalizedEqual := replayed.any (source == ·)
      }
  comparisons

/-- Replay declarations and optionally retain normalized source/replayed
metadata comparisons. Metadata capture is disabled for bulk operation because
serializing every expression is intentionally more expensive than checking it. -/
def replayDetailed (ctx : Context) (env : Environment) (decl : Option Name := none)
    (captureMetadata := false) : IO DetailedResult := do
  let ctx := { ctx with analysisDecl := if captureMetadata then decl else none }
  let mut remaining : NameSet := ∅
  for (n, ci) in ctx.newConstants.toList do
    -- We skip unsafe constants, and also partial constants.
    -- Later we may want to handle partial constants.
    if !ci.isUnsafe && !ci.isPartial then
      remaining := remaining.insert n
  let (_, s) ← StateRefT'.run (s := { env, remaining }) do
    ReaderT.run (r := ctx) do
      match decl with
      | some d =>
        unless ctx.newConstants.contains d do
          throw <| IO.userError s!"declaration {d} is not present in the selected replay set"
        unless remaining.contains d do
          throw <| IO.userError s!"declaration {d} is unsafe or partial and cannot be replayed"
        replayConstant d
      | none =>
        for n in remaining do
          replayConstant n
      checkPostponedConstructors
      checkPostponedRecursors
      if (← read).checkQuot then checkQuotInit
  let analysis :=
    if captureMetadata then
      match decl with
      | some selected => analyzeSelectedInductive ctx (s.analysisBase.getD env) selected
      | none => .ok {}
    else .ok {}
  let (artifacts, analysisFailure) := match analysis with
    | .ok artifacts => (artifacts, none)
    | .error failure => ({}, some failure)
  let comparisons := if captureMetadata then
    compareGeneratedConstants ctx env s.env artifacts.recursivePositions
  else #[]
  return {
    numAdded := s.numAdded
    env := s.env
    comparisons
    theoryBlocks := artifacts.theoryBlocks
    analysisFailure
  }

/-- "Replay" some constants into an `Environment`, sending them to the kernel for checking. -/
def replay (ctx : Context) (env : Environment) (decl : Option Name := none) :
    IO (Nat × Environment) := do
  let result ← replayDetailed ctx env decl
  pure (result.numAdded, result.env)

structure CapturedResult where
  numAdded : Nat
  emission : Option Differential.Emission := none

open private ImportedModule.mk from Lean.Environment in
private unsafe def replayFromImportsCore (module : Name) (verbose := false) (compare := false)
    (fuel : Lean4Lean.FuelConfig := {}) (decl : Option Name := none)
    (differentialInput : Option (Differential.Input × Option String) := none)
    (differentialPhase : Option (IO.Ref Differential.Phase) := none) :
    IO CapturedResult := do
  if let some phase := differentialPhase then
    phase.set .moduleLoad
  let mFile ← findOLean module
  unless (← mFile.pathExists) do
    throw <| IO.userError s!"object file '{mFile}' of module {module} does not exist"
  let mut fnames := #[mFile]
  let sFile := OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then
      fnames := fnames.push pFile
  let parts ← readModuleDataParts fnames
  let some (mod, _) := parts[parts.size - 1]? | unreachable! -- load private module data
  let (_, s) ← (importModulesCore mod.imports).run
  let env ← match Kernel.Environment.finalizeImport s mod.imports module 0 with
    | .ok env => pure env
    | .error e => throw <| .userError <| ← (e.toMessageData {}).toString
  let mut newConstants := {}
  for name in mod.constNames, ci in mod.constants do
    -- Multi-part oleans can materialize the same auto-generated lemma in
    -- several parts. `finalizeImport` has already deduplicated names supplied
    -- by imports, so replay only the constants genuinely new in this module.
    if (env.constants.find? name).isNone then
      newConstants := newConstants.insert name ci
  if let some phase := differentialPhase then
    phase.set .kernelReplay
  let { numAdded, env := replayedEnv, comparisons, theoryBlocks, analysisFailure } ←
    replayDetailed { newConstants, verbose, compare, fuel } env decl
    (captureMetadata := differentialInput.isSome)
  if let some phase := differentialPhase then
    phase.set .metadataComparison
  -- Serialize before releasing the compacted regions. JSON strings can point
  -- directly at strings in the source metadata until `compress` copies them.
  let emission := differentialInput.map fun (input, caseId) =>
    Differential.Result.fromComparisons input numAdded comparisons theoryBlocks
      analysisFailure (caseId := caseId) |>.emit
  (Environment.ofKernelEnv replayedEnv).freeRegions
  -- Project out the regions *before* freeing them: `CompactedRegion` is a `USize`, so the
  -- projected array holds no pointers into the regions, and `parts` -- whose `ModuleData`s
  -- live inside them -- is consumed by the `map` and dead by the time we free. Iterating
  -- `parts` directly would leave this frame's own locals dangling, and the decrefs on
  -- return would segfault.
  parts.map (·.2) |>.forM CompactedRegion.free
  pure { numAdded, emission }

unsafe def replayFromImports (module : Name) (verbose := false) (compare := false)
    (fuel : Lean4Lean.FuelConfig := {}) (decl : Option Name := none) : IO Nat := do
  return (← replayFromImportsCore module verbose compare fuel decl).numAdded

/-- Replay one exact declaration and emit a versioned source/generated metadata
comparison. The declaration's dependencies and kernel-generated constants are
included in deterministic name order. -/
unsafe def replayFromImportsDifferential (module decl : Name)
    (fuel : Lean4Lean.FuelConfig := {}) (caseId : Option String := none)
    (phase : Option (IO.Ref Differential.Phase) := none) :
    IO Differential.Emission := do
  let input : Differential.Input := {
    module := module.toString
    declaration := decl.toString
    fresh := false
  }
  let result ← replayFromImportsCore module false false fuel (some decl)
    (some (input, caseId)) phase
  let some emission := result.emission | unreachable!
  pure emission

private unsafe def replayFromFreshCore (module : Name)
    (verbose := false) (compare := false) (decl : Option Name := none)
    (fuel : Lean4Lean.FuelConfig := {})
    (differentialInput : Option (Differential.Input × Option String) := none)
    (differentialPhase : Option (IO.Ref Differential.Phase) := none) :
    IO CapturedResult := do
  if let some phase := differentialPhase then
    phase.set .moduleLoad
  Lean.withImportModules #[module] {} (trustLevel := 0) fun env => do
    if let some phase := differentialPhase then
      phase.set .kernelReplay
    let ctx := { newConstants := env.constants.map₁, verbose, compare, checkQuot := false, fuel }
    -- `stage₁ := false` is very important here: while a declaration is being added
    -- the environment is also held by the replay state, so the map is shared and `stage₁ := true`
    -- would lead to quadratic performance.
    let result ← replayDetailed ctx (.empty module (stage₁ := false)) decl
      (captureMetadata := differentialInput.isSome)
    if let some phase := differentialPhase then
      phase.set .metadataComparison
    let emission := differentialInput.map fun (input, caseId) =>
      Differential.Result.fromComparisons input result.numAdded result.comparisons
        result.theoryBlocks result.analysisFailure (caseId := caseId) |>.emit
    pure { numAdded := result.numAdded, emission }

unsafe def replayFromFresh (module : Name)
    (verbose := false) (compare := false) (decl : Option Name := none)
    (fuel : Lean4Lean.FuelConfig := {}) : IO Nat := do
  return (← replayFromFreshCore module verbose compare decl fuel).numAdded

unsafe def replayFromFreshDifferential (module decl : Name)
    (fuel : Lean4Lean.FuelConfig := {}) (caseId : Option String := none)
    (phase : Option (IO.Ref Differential.Phase) := none) :
    IO Differential.Emission := do
  let input : Differential.Input := {
    module := module.toString
    declaration := decl.toString
    fresh := true
  }
  let result ← replayFromFreshCore module false false (some decl) fuel
    (some (input, caseId)) phase
  let some emission := result.emission | unreachable!
  pure emission

end Lean4Lean.Replay
