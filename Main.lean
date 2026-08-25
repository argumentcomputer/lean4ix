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
import Lean4Lean.Replay
import Lake.Load.Manifest

open Lean hiding Environment Exception
open Kernel Lean4Lean.Replay

/-- Read the name of the main module from the `lake-manifest`. -/
-- This has been copied from `ImportGraph.getCurrentModule` in the
-- https://github.com/leanprover-community/import-graph repository.
def getCurrentModule : IO Name := do
  match (← Lake.Manifest.load? ⟨"lake-manifest.json"⟩) with
  | none =>
    -- TODO: should this be caught?
    pure .anonymous
  | some manifest =>
    -- The package name and its default `lean_lib` usually agree only up to
    -- case (`batteries`/`Batteries`, `lean4lean`/`Lean4Lean`), and not
    -- necessarily just in the first letter, so the caller matches this
    -- name case-insensitively rather than guessing a capitalization here.
    -- Would be better to read the `.defaultTargets` from the
    -- `← getRootPackage` from `Lake`, but I can't make that work with the monads involved.
    return manifest.name

/-- Case-insensitively test whether `target` is `mod` itself or a namespace
prefix of it. Used only for the module root inferred from the package name in
`lake-manifest.json` (e.g. package `lean4lean` vs library `Lean4Lean`, which
differ beyond capitalizing the first letter); explicit command-line targets
keep exact matching. -/
def isModulePrefixOfCI (target mod : Name) : Bool :=
  let t := target.toString.toLower
  let m := mod.toString.toLower
  m == t || (t ++ ".").isPrefixOf m

/-- Module paths contain only string components; numeric `Name` components
would make `Lean.modToFilePath` panic. -/
def isModuleName : Name → Bool
  | .anonymous => true
  | .str parent component => !component.isEmpty && isModuleName parent
  | .num .. => false

namespace Lean4Lean.FuelConfig

/-- Serialize `cfg` to its JSON object map, or panic — it's derived so it must be an object. -/
private def toObj (cfg : FuelConfig) : Std.TreeMap.Raw String Lean.Json compare :=
  match Lean.toJson cfg with
  | .obj m => m
  | _ => panic! "FuelConfig.toJson produced a non-object"

/-- Field names that `FuelConfig` accepts (derived from its JSON encoding). -/
private def fieldNames : List String :=
  (toObj {}).foldr (fun k _ acc => k :: acc) []

/-- Layer a JSON object over an existing `FuelConfig`.

Unknown fields are rejected up front (the derived `FromJson` silently ignores
them, which we don't want for a config file); known fields are overlaid on top
of the base config's own JSON serialization and the merged object is fed back
through `fromJson?`, so value validation stays entirely in the derived parser. -/
private def ofJson? (base : FuelConfig) (j : Lean.Json) : Except String FuelConfig := do
  let .obj m := j | throw "config JSON must be an object"
  let baseObj := toObj base
  m.foldlM (init := ()) fun _ k _ => do
    unless baseObj.contains k do
      throw s!"unknown field '{k}' in config JSON (valid: {fieldNames})"
  let merged := m.foldl (init := baseObj) (·.insert · ·)
  Lean.fromJson? (.obj merged)

/-- Read + parse a config file, layering over an existing base. -/
private def ofFile (base : FuelConfig) (path : System.FilePath) : IO FuelConfig := do
  let raw ← IO.FS.readFile path
  let j ← IO.ofExcept (Lean.Json.parse raw)
  IO.ofExcept (ofJson? base j)

/-- Apply a single `--config:field=value` override.

Value is parsed as JSON, then routed through `fuelConfigOfJson?` — so the CLI
path and the file path share the same parser (and produce the same error
messages for e.g. non-numeric values or unknown fields). -/
private def applyFlag (cfg : FuelConfig) (field value : String) :
    Except String FuelConfig := do
  let jval ← match Lean.Json.parse value with
    | .ok j => pure j
    | .error _ => throw s!"could not parse value '{value}' for --config:{field} as JSON"
  ofJson? cfg (.obj (Std.TreeMap.Raw.empty.insert field jval))
    |>.mapError (s!"in --config:{field}={value}: " ++ ·)

end Lean4Lean.FuelConfig

def Lean4Lean.Differential.Case.ofFile (path : System.FilePath) : IO Case := do
  let raw ← IO.FS.readFile path
  let json ← IO.ofExcept (Lean.Json.parse raw)
  let case : Case ← IO.ofExcept (Lean.fromJson? json)
  IO.ofExcept (Case.validate case)

namespace Lean4Lean.Differential

/-- Mutable observations retained outside `mainCore`, so even a failure before
the replay branch can emit the selected case and its exact phase. -/
structure CliState where
  phase : IO.Ref Phase
  caseSpec : IO.Ref (Option Case)
  input : IO.Ref (Option Input)
  /-- Prevent a cleanup failure after emission from producing a second JSON object. -/
  emitted : IO.Ref Bool

def expectedExitCode (caseSpec : Option Case) (outcome : Outcome) (phase : Phase) : UInt32 :=
  match caseSpec with
  | some case => if outcome == case.expectedOutcome && phase == case.expectedPhase then 0 else 1
  | none => if outcome == .accepted then 0 else 1

/-- Elaborate a standalone source file into a private module root. Copying the
source to its declared module path makes the compiler's module identity
independent of the caller's directory layout. -/
def elaborateSource (sysroot outputRoot : System.FilePath) (module : Name)
    (source : System.FilePath) : IO Unit := do
  let copiedSource := modToFilePath outputRoot module "lean"
  let olean := modToFilePath outputRoot module "olean"
  let ilean := modToFilePath outputRoot module "ilean"
  if let some parent := copiedSource.parent then
    IO.FS.createDirAll parent
  IO.FS.writeFile copiedSource (← IO.FS.readFile source)
  let leanPath := System.SearchPath.toString (← searchPathRef.get)
  let output ← IO.Process.output {
    cmd := (sysroot / "bin" / "lean").toString
    args := #["-R", outputRoot.toString, "-o", olean.toString,
      "-i", ilean.toString, copiedSource.toString]
    env := #[("LEAN_PATH", some leanPath)]
  }
  unless output.exitCode == 0 do
    let diagnostic :=
      if output.stderr.isEmpty then output.stdout
      else if output.stdout.isEmpty then output.stderr
      else output.stdout ++ "\n" ++ output.stderr
    throw <| IO.userError s!"source elaboration failed for {source}: {diagnostic.replace
      copiedSource.toString source.toString}"

end Lean4Lean.Differential

/--
Run as e.g. `lake exe lean4lean` to check everything in the current project.
or e.g. `lake exe lean4lean Mathlib.Data.Nat` to check everything with module name
starting with `Mathlib.Data.Nat`.

This will replay all the new declarations from the target file into the `Environment`
as it was at the beginning of the file, using the kernel to check them.

You can also use `lake exe lean4lean --fresh Mathlib.Data.Nat.Basic` to replay all the constants
(both imported and defined in that file) into a fresh environment,
but this can only be used on a single file.

Use `--decl=Foo.bar` to replay only that declaration and the dependencies
needed to check it. The selected module prefix must resolve to exactly one
module.

Add `--json` to that exact-declaration mode to emit the versioned differential
result, including normalized source/replayed metadata for every generated
constant. JSON mode always writes one result object, including on rejection.

Use `--case=case.json` to read the module, declaration, optional standalone
source path, fresh-mode flag, case identifier, and expected outcome/phase from
a versioned corpus case. Source cases are elaborated with the pinned compiler
in a private module root. A case run succeeds when the observed outcome and
phase match its expectation, including for an expected rejection.
-/
unsafe def mainCore (args : List String)
    (differentialState : Option Lean4Lean.Differential.CliState := none) : IO UInt32 := do
  if let some state := differentialState then
    state.phase.set .selection
  let sysroot ← findSysroot
  initSearchPath sysroot
  let (flags, args) := args.partition fun s => s.startsWith "-"
  let verbose := "-v" ∈ flags || "--verbose" ∈ flags
  let freshFlag : Bool := "--fresh" ∈ flags
  let mut fresh := freshFlag
  let compare : Bool := "--compare" ∈ flags
  let mut fuel : Lean4Lean.FuelConfig := {}
  let mut onlyDecl : Option Name := none
  let mut caseSpec : Option Lean4Lean.Differential.Case := none
  for flag in flags do
    if let some path := flag.dropPrefix? "--config=" then
      fuel ← Lean4Lean.FuelConfig.ofFile fuel ⟨path.toString⟩
    else if let some rest := flag.dropPrefix? "--config:" then
      let [field, value] := rest.toString.splitOn "="
        | throw <| IO.userError s!"malformed flag {flag}: expected --config:<field>=<value>"
      match fuel.applyFlag field value with
      | .ok f => fuel := f
      | .error e => throw <| IO.userError e
    else if let some rest := flag.dropPrefix? "--decl=" then
      let decl := rest.toString.toName
      if decl.isAnonymous then
        throw <| IO.userError s!"malformed flag {flag}: expected --decl=<declaration>"
      onlyDecl := some decl
    else if let some path := flag.dropPrefix? "--case=" then
      if caseSpec.isSome then
        throw <| IO.userError "at most one --case=<path> flag may be supplied"
      let case ← Lean4Lean.Differential.Case.ofFile ⟨path.toString⟩
      caseSpec := some case
      if let some state := differentialState then
        state.caseSpec.set (some case)
        state.input.set (some {
          source := case.source
          module := case.module
          declaration := case.declaration
          fresh := case.fresh
        })
  if let some case := caseSpec then
    if onlyDecl.isSome || freshFlag || !args.isEmpty then
      throw <| IO.userError
        "--case supplies its own module, declaration, and fresh mode; do not combine them"
    let decl := case.declaration.toName
    if decl.isAnonymous then
      throw <| IO.userError s!"case {case.id} has an invalid declaration name"
    onlyDecl := some decl
    fresh := case.fresh
  let json : Bool := "--json" ∈ flags || caseSpec.isSome
  let (targets, inferred) ← do
    match caseSpec with
    | some case =>
      let mod := case.module.toName
      if mod.isAnonymous || !isModuleName mod then
        throw <| IO.userError s!"case {case.id} has an invalid module name"
      pure ([mod], false)
    | none => match args with
      | [] => pure ([← getCurrentModule], true)
      | args => do
        let targets ← args.mapM fun arg => do
          let mod := arg.toName
          if mod.isAnonymous || !isModuleName mod then
            throw <| IO.userError s!"Could not resolve module: {arg}"
          else
            pure mod
        pure (targets, false)
  let runSelected : IO UInt32 := do
    if let some state := differentialState then
      state.phase.set .moduleLoad
    let mut targetModules := []
    let sp ← searchPathRef.get
    for target in targets do
      let mut found := false
      for path in (← SearchPath.findAllWithExt sp "olean") do
        if let some m := (← searchModuleNameOfFileName path sp) then
          if if inferred then isModulePrefixOfCI target m else target.isPrefixOf m then
            targetModules := targetModules.insert m
            found := true
      if not found then
        throw <| IO.userError <| if inferred then
          s!"Could not infer main module (tried {target}). \
            Use `lake exe lean4lean <target>` instead"
        else s!"Could not find any oleans for: {target}"
    if let some state := differentialState then
      state.phase.set .selection
    if onlyDecl.isSome && targetModules.length != 1 then
      throw <| IO.userError s!"--decl flag requires exactly one selected module, but matched \
        {targetModules.length}; pass the exact defining module"
    if json && onlyDecl.isNone then
      throw <| IO.userError "--json requires --decl=<declaration>"
    if json && (verbose || compare) then
      throw <| IO.userError "--json cannot be combined with --verbose or --compare"
    if json then
      let [module] := targetModules | unreachable!
      let some decl := onlyDecl | unreachable!
      let input : Lean4Lean.Differential.Input := {
        source := caseSpec.bind (·.source)
        module := module.toString
        declaration := decl.toString
        fresh
      }
      if let some state := differentialState then
        state.input.set (some input)
        state.phase.set .moduleLoad
      let phaseRef := differentialState.map (·.phase)
      try
        let emission ← if fresh then
          replayFromFreshDifferential module decl (fuel := fuel) (caseId := caseSpec.map (·.id))
            (phase := phaseRef)
        else
          replayFromImportsDifferential module decl (fuel := fuel) (caseId := caseSpec.map (·.id))
            (phase := phaseRef)
        IO.println emission.json
        if let some state := differentialState then
          state.emitted.set true
        return Lean4Lean.Differential.expectedExitCode caseSpec emission.outcome emission.phase
      catch e =>
        let phase ← match differentialState with
          | some state => state.phase.get
          | none => pure .kernelReplay
        let result := Lean4Lean.Differential.Result.rejected input phase e.toString
          (caseId := caseSpec.map (·.id))
        IO.println (Lean.toJson result).compress
        if let some state := differentialState then
          state.emitted.set true
        return Lean4Lean.Differential.expectedExitCode caseSpec .rejected phase
    let mut n := 0
    if fresh then
      if targetModules.length != 1 then
        throw <| IO.userError s!"--fresh flag is only valid when specifying a single module:\n\
          {targetModules}"
      for m in targetModules do
        if verbose then IO.println s!"replaying {m} with --fresh"
        n := n + (← replayFromFresh m verbose compare (decl := onlyDecl) (fuel := fuel))
    else
      let mut tasks := #[]
      for m in targetModules do
        tasks := tasks.push (m, ← IO.asTask
          (replayFromImports m verbose compare (fuel := fuel) (decl := onlyDecl)))
      let mut err := false
      for (m, t) in tasks do
        if verbose then IO.println s!"replaying {m}"
        match t.get with
        | .error e =>
          IO.eprintln s!"lean4lean found a problem in {m}:\n{e.toString}"
          err := true
        | .ok n' => n := n + n'
      if err then return 1
    println! "checked {n} declarations"
    return 0
  match caseSpec.bind (·.source) with
  | none => runSelected
  | some source =>
    let [module] := targets | unreachable!
    if let some state := differentialState then
      state.phase.set .elaboration
    IO.FS.withTempDir fun outputRoot => do
      Lean4Lean.Differential.elaborateSource sysroot outputRoot module ⟨source⟩
      let previousSearchPath ← searchPathRef.get
      searchPathRef.set (outputRoot :: previousSearchPath)
      try
        runSelected
      finally
        searchPathRef.set previousSearchPath

/-- Recover the requested input directly from argv so even flag parsing and
module-selection failures can be represented by the differential schema. -/
def differentialInputFromArgs (args : List String) : Lean4Lean.Differential.Input :=
  let module := (args.find? fun arg => !arg.startsWith "-").getD "[inferred]"
  let declaration := (args.findSome? fun arg =>
    arg.dropPrefix? "--decl=" |>.map (·.toString)).getD "[missing]"
  {
    module
    declaration
    fresh := "--fresh" ∈ args
  }

unsafe def main (args : List String) : IO UInt32 := do
  if "--json" ∈ args || args.any (·.startsWith "--case=") then
    let phase ← IO.mkRef Lean4Lean.Differential.Phase.selection
    let caseSpec ← IO.mkRef (none : Option Lean4Lean.Differential.Case)
    let input ← IO.mkRef (none : Option Lean4Lean.Differential.Input)
    let emitted ← IO.mkRef false
    let state : Lean4Lean.Differential.CliState := { phase, caseSpec, input, emitted }
    try mainCore args (some state)
    catch e =>
      if ← state.emitted.get then
        IO.eprintln s!"lean4lean failed after emitting its differential result: {e}"
        return 1
      let phase ← state.phase.get
      let caseSpec ← state.caseSpec.get
      let input := (← state.input.get).getD (differentialInputFromArgs args)
      let result := Lean4Lean.Differential.Result.rejected
        input phase e.toString (caseId := caseSpec.map (·.id))
      IO.println (Lean.toJson result).compress
      return Lean4Lean.Differential.expectedExitCode caseSpec .rejected phase
  else
    mainCore args
