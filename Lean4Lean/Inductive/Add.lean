import Batteries.Data.List.Basic
import Lean4Lean.Environment.Basic
import Lean4Lean.TypeChecker

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

namespace AddInductive
open TypeChecker

structure RecInfo where
  motive : Expr
  minors : Array Expr
  indices : Array Expr
  major : Expr
  deriving Inhabited

structure InductiveStats where
  lctx : LocalContext := {}
  levels : List Level
  resultLevel : Level
  nindices : Array Nat := #[]
  indConsts : Array Expr
  params : Array Expr
  isNotZero : Bool
  deriving Inhabited

structure Context where
  env : Environment
  lctx : LocalContext := {}
  lparams : List Name
  ngen : NameGenerator := { namePrefix := `_ind_fresh }
  safety : DefinitionSafety
  allowPrimitive : Bool
  fuel : FuelConfig := {}

/-- Checker context represented by an inductive-add context. Candidate traces
retain the latter so Verify can recover this exact former value. -/
def Context.toTypeChecker (context : Context) : TypeChecker.Context where
  env := context.env
  lctx := context.lctx
  safety := context.safety
  lparams := context.lparams
  fuel := context.fuel

/-- The exact free variable allocated by the next `withLocalDecl` in an
inductive-add context. -/
def Context.freshFVarId (context : Context) : FVarId :=
  ⟨context.ngen.curr⟩

def Context.freshExpr (context : Context) : Expr :=
  .fvar context.freshFVarId

/-- Context seen by the body of the next `withLocalDecl`.  Naming this update
lets candidate traces index a Pi body by the actual reader context used by the
producer, rather than retaining an unrelated context as unchecked data. -/
def Context.pushLocalDecl (context : Context)
    (name : Name) (binderInfo : BinderInfo) (type : Expr) : Context :=
  { context with
    lctx := context.lctx.mkLocalDecl context.freshFVarId name type binderInfo
    ngen := context.ngen.next }

abbrev M := ReaderT Context <| Except Exception

instance : MonadLocalNameGenerator M where
  withFreshId f c := f c.ngen.curr { c with ngen := c.ngen.next }

instance (priority := low) : MonadLift TypeChecker.M M where
  monadLift x c := x.run c.env c.safety c.lctx c.lparams (fuel := c.fuel)

@[simp] theorem liftTypeChecker_apply (x : TypeChecker.M α) (c : Context) :
    (liftM x : M α) c =
      x.run c.env c.safety c.lctx c.lparams (fuel := c.fuel) :=
  rfl

instance (priority := low+1) : MonadWithReaderOf LocalContext M where
  withReader f x := withReader (fun c => { c with lctx := f c.lctx }) x

instance : MonadLCtx M where
  getLCtx := return (← read).lctx

@[inline] def withEnv (env : Environment) (x : M α) : M α :=
  withReader (fun c => { c with env }) x

def getType (fvar : Expr) : M Expr :=
  return ((← getLCtx).get! fvar.fvarId!).type

def checkInductiveTypes
    (nparams : Nat) (indTypes : Array InductiveType)
    (k : InductiveStats → M α) : M α := do
  let rec loopInd dIdx stats : M α := do
    if _h : dIdx < indTypes.size then
      let indType := indTypes[dIdx]
      let env := (← read).env
      let type := indType.type
      env.checkNoMVarNoFVar indType.name type
      _ ← checkType type
      let rec loop stats type i nindices fuel k : M α := match fuel with
      | 0 => throw .deepRecursion
      | fuel+1 => do
        if let .forallE name dom body bi := type then
          if i < nparams then
            if stats.indConsts.isEmpty then
              withLocalDecl name bi dom.consumeTypeAnnotations fun param => do
                let stats := { stats with params := stats.params.push param }
                let type := body.instantiate1 param
                loop stats (← whnf type) (i + 1) nindices fuel k
            else
              let param := stats.params[i]!
              unless ← isDefEq dom (← getType param) do
                throw <| .other "parameters of all inductive datatypes must match"
              let type := body.instantiate1 param
              loop stats (← whnf type) (i + 1) nindices fuel k
          else
            withLocalDecl name bi dom.consumeTypeAnnotations fun arg => do
              let type := body.instantiate1 arg
              loop stats (← whnf type) i (nindices + 1) fuel k
        else
          if i != nparams then
            throw <| .other "number of parameters mismatch in inductive datatype declaration"
          k type stats nindices
      let fuel := (← readThe Context).fuel.inductiveFuel
      loop stats (← whnf type) 0 0 fuel fun type stats nindices => show M α from do
      let type ← ensureSort type
      let mut stats := stats
      let resultLevel := type.sortLevel!
      if stats.indConsts.isEmpty then
        let lctx := (← read).lctx
        stats := { stats with lctx, resultLevel, isNotZero := resultLevel.isNeverZero }
      else if !resultLevel.isEquiv' stats.resultLevel then
        throw <| .other "mutually inductive types must live in the same universe"
      stats := { stats with
        nindices := stats.nindices.push nindices
        indConsts := stats.indConsts.push (.const indType.name stats.levels) }
      loopInd (dIdx + 1) stats
    else
      k <|
        assert! stats.levels.length == (← read).lparams.length
        assert! stats.nindices.size == indTypes.size
        assert! stats.indConsts.size == indTypes.size
        assert! stats.params.size == nparams
        stats
  termination_by indTypes.size - dIdx
  loopInd 0 { (default : InductiveStats) with levels := (← read).lparams.map .param }

def hasIndOcc (indConsts : Array Expr) (t : Expr) : Bool :=
  (t.find? fun
    | .const e _ => indConsts.any fun I => I.constName! == e
    | _ => false).isSome

/-- Return true if declaration is recursive -/
def isRec (indTypes : Array InductiveType) (indConsts : Array Expr) : Bool :=
  let rec loop
    | .forallE _ dom body _ => hasIndOcc indConsts dom || loop body
    | _ => false
  indTypes.any fun indType => indType.ctors.any fun ctor => loop ctor.type

/-- Return true if the given declaration is reflexive.

Remark: We say an inductive type `T` is reflexive if it
contains at least one constructor that takes as an argument a
function returning `T'` where `T'` is another inductive datatype (possibly equal to `T`)
in the same mutual declaration. -/
def isReflexive (indTypes : Array InductiveType) (indConsts : Array Expr) : Bool :=
  let rec loop
    | .forallE _ dom body _ => dom.isForall && hasIndOcc indConsts dom || loop body
    | _ => false
  indTypes.any fun indType => indType.ctors.any fun ctor => loop ctor.type

def declareInductiveTypes (stats : InductiveStats) (numParams : Nat)
    (indTypes : Array InductiveType) (numNested : Nat) (isUnsafe : Bool) : M Environment :=
  fun c =>
  let all := indTypes.map (·.name) |>.toList
  let infos := indTypes.zipWith (bs := stats.nindices) fun indType numIndices =>
    { indType with
      numParams, numIndices, all, numNested, isUnsafe
      levelParams := c.lparams
      ctors := indType.ctors.map (·.name)
      isRec := isRec indTypes stats.indConsts
      isReflexive := isReflexive indTypes stats.indConsts }
  infos.foldlM (init := c.env) fun env info => do
    env.checkName info.name c.allowPrimitive
    return env.add (.inductInfo info)

def isValidIndAppIdx (stats : InductiveStats) (t : Expr) (i : Nat) : Bool :=
  t.withApp fun I args => Id.run do
  unless I == stats.indConsts[i]! && args.size == stats.params.size + stats.nindices[i]! do
    return false
  for i in [:stats.params.size] do
    if stats.params[i]! != args[i]! then return false
  for i in [stats.params.size:args.size] do
    if hasIndOcc stats.indConsts args[i]! then return false
  true

def isValidIndApp? (stats : InductiveStats) (t : Expr) : Option Nat := do
  for i in [:stats.indConsts.size] do
    if isValidIndAppIdx stats t i then
      return i
  none

def isRecArg (stats : InductiveStats) (t : Expr) : M (Option Nat) := do
  loop t (← readThe Context).fuel.inductiveFuel
where
  loop t
  | 0 => throw .deepRecursion
  | fuel+1 => do
    let t ← whnf t
    let .forallE name dom body bi := t | return isValidIndApp? stats t
    withLocalDecl name bi dom.consumeTypeAnnotations fun arg => do
    loop (body.instantiate1 arg) fuel

def checkPositivity (stats : InductiveStats) (t : Expr) (ctor : Name) (idx : Nat) :
    M Unit := do loop t (← readThe Context).fuel.inductiveFuel where
  loop t
  | 0 => throw .deepRecursion
  | fuel+1 => do
    let t ← whnf t
    if !hasIndOcc stats.indConsts t then return
    if let .forallE name dom body bi := t then
      if hasIndOcc stats.indConsts dom then
        throw <| .other s!"arg #{idx + 1} of '{ctor}' \
          has a non positive occurrence of the datatypes being declared"
      withLocalDecl name bi dom.consumeTypeAnnotations fun arg => do
      loop (body.instantiate1 arg) fuel
    else if let none := isValidIndApp? stats t then
      throw <| .other s!"arg #{idx + 1} of '{ctor}' \
        has a non valid occurrence of the datatypes being declared"

def checkConstructors (indTypes : Array InductiveType)
    (stats : InductiveStats) (isUnsafe : Bool) : M Unit := do
  let env ← getEnv
  for h : idx in [:indTypes.size] do
    let indType := indTypes[idx]
    let mut foundCtors : NameSet := {}
    for ctor in indType.ctors do
      let n := ctor.name
      if foundCtors.contains n then
        throw <| .other s!"duplicate constructor name '{n}'"
      foundCtors := foundCtors.insert n
      let t := ctor.type
      env.checkNoMVarNoFVar n t
      _ ← checkType t
      let rec loop t i
      | 0 => throw .deepRecursion
      | fuel+1 => do
        if let .forallE name dom body bi := t then
          if let some param := stats.params[i]? then
            unless ← isDefEq dom (← getType param) do
              throw <| .other
                s!"arg #{i + 1} of '{n}' does not match inductive datatype parameters"
            loop (body.instantiate1 param) (i + 1) fuel
          else
            let s ← ensureType dom
            unless stats.resultLevel.isZero || stats.resultLevel.geq' s.sortLevel! do
              throw <| .other s!"universe level of type_of(arg #{i + 1}) of '{n}' \
                is too big for the corresponding inductive datatype"
            if !isUnsafe then
              checkPositivity stats dom n i
            withLocalDecl name bi dom.consumeTypeAnnotations fun arg => do
              loop (body.instantiate1 arg) (i + 1) fuel
        else if !isValidIndAppIdx stats t idx then
          throw <| .other s!"invalid return type for '{n}'"
      loop t 0 (← readThe Context).fuel.inductiveFuel

/-- One observed WHNF node in the executable normalization-candidate pass.
The complete `AddInductive.Context` is retained because Verify must replay the
same environment, safety mode, local context, level parameters, transparency,
and checker fuel before the observation acquires semantic authority. -/
structure CandidateWhnfStep where
  context : Context
  source : Expr
  result : Expr

/-- Exact ordinary-checker execution represented by one retained step. -/
def CandidateWhnfStep.Valid (step : CandidateWhnfStep) : Prop :=
  TypeChecker.M.run step.context.env step.context.safety
      step.context.lctx step.context.lparams step.context.fuel
      (TypeChecker.whnf step.source) =
    .ok step.result

/-- The result of evaluating one WHNF step together with the equality that
certifies the observation. -/
structure CandidateWhnfObservation (context : Context) (source : Expr) where
  result : Expr
  valid : CandidateWhnfStep.Valid ⟨context, source, result⟩

def observeCandidateWhnf (context : Context) (source : Expr) :
    Except Exception (CandidateWhnfObservation context source) :=
  match hrun :
      TypeChecker.M.run context.env context.safety context.lctx
        context.lparams context.fuel (TypeChecker.whnf source) with
  | .error err => .error err
  | .ok result => .ok ⟨result, hrun⟩

theorem observeCandidateWhnf_of_run
    (context : Context) (source result : Expr)
    (hrun : CandidateWhnfStep.Valid ⟨context, source, result⟩) :
    observeCandidateWhnf context source = .ok ⟨result, hrun⟩ := by
  change
    TypeChecker.M.run context.env context.safety context.lctx
        context.lparams context.fuel (TypeChecker.whnf source) =
      .ok result at hrun
  unfold observeCandidateWhnf
  split
  · simp_all
  · rename_i observed hobserved
    have : observed = result := by simp_all
    subst observed
    rfl

/-- Recover the state-bearing recursive checker execution erased by
`TypeChecker.M.run`. This is the exact `WhnfRun.run_eq` boundary used by
Verify; no final state is guessed or chosen. -/
theorem CandidateWhnfStep.innerRun
    (step : CandidateWhnfStep) (recursionFuel : Nat)
    (hdepth : step.context.fuel.recDepth = recursionFuel + 1)
    (hvalid : step.Valid) :
    ∃ state : TypeChecker.State,
      TypeChecker.Inner.whnf' step.source
          (TypeChecker.Methods.withFuel recursionFuel)
          step.context.toTypeChecker
          ({} : TypeChecker.State) =
        .ok (step.result, state) := by
  unfold CandidateWhnfStep.Valid at hvalid
  unfold TypeChecker.M.run TypeChecker.whnf TypeChecker.RecM.run at hvalid
  simp [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, StateT.bind, Except.bind, Bind.bind,
    StateT.pure, Except.pure, Pure.pure,
    StateT.run', Functor.map, Except.map] at hvalid
  rw [hdepth] at hvalid
  simp only [TypeChecker.Methods.withFuel,
    TypeChecker.Inner.whnf] at hvalid
  cases hinner :
      TypeChecker.Inner.whnf' step.source
        (TypeChecker.Methods.withFuel recursionFuel)
        { env := step.context.env
          lctx := step.context.lctx
          safety := step.context.safety
          lparams := step.context.lparams
          fuel := step.context.fuel }
        ({} : TypeChecker.State) with
  | error err => simp [hinner] at hvalid
  | ok pair =>
    rcases pair with ⟨observed, state⟩
    have : observed = step.result := by
      simpa [hinner] using hvalid
    subst observed
    exact ⟨state, by
      simpa [Context.toTypeChecker] using hinner⟩

/-- One full, non-inference-only type-check observation retained by the
candidate producer. -/
structure CandidateCheckTypeStep where
  context : Context
  source : Expr
  inferred : Expr

def CandidateCheckTypeStep.Valid
    (step : CandidateCheckTypeStep) : Prop :=
  TypeChecker.M.run step.context.env step.context.safety
      step.context.lctx step.context.lparams step.context.fuel
      (TypeChecker.checkType step.source) =
    .ok step.inferred

structure CandidateCheckTypeObservation
    (context : Context) (source : Expr) where
  inferred : Expr
  valid : CandidateCheckTypeStep.Valid ⟨context, source, inferred⟩

def observeCandidateCheckType (context : Context) (source : Expr) :
    Except Exception (CandidateCheckTypeObservation context source) :=
  match hrun :
      TypeChecker.M.run context.env context.safety context.lctx
        context.lparams context.fuel (TypeChecker.checkType source) with
  | .error err => .error err
  | .ok inferred => .ok ⟨inferred, hrun⟩

theorem observeCandidateCheckType_of_run
    (context : Context) (source inferred : Expr)
    (hrun : CandidateCheckTypeStep.Valid
      ⟨context, source, inferred⟩) :
    observeCandidateCheckType context source =
      .ok ⟨inferred, hrun⟩ := by
  change
    TypeChecker.M.run context.env context.safety context.lctx
        context.lparams context.fuel (TypeChecker.checkType source) =
      .ok inferred at hrun
  unfold observeCandidateCheckType
  split
  · simp_all
  · rename_i observed hobserved
    have : observed = inferred := by simp_all
    subst observed
    rfl

/-- Recover the state-bearing full-check execution erased by `M.run`. -/
theorem CandidateCheckTypeStep.innerRun
    (step : CandidateCheckTypeStep) (recursionFuel : Nat)
    (hdepth : step.context.fuel.recDepth = recursionFuel)
    (hvalid : step.Valid) :
    ∃ state : TypeChecker.State,
      TypeChecker.Inner.inferType step.source false
          (TypeChecker.Methods.withFuel recursionFuel)
          step.context.toTypeChecker
          ({} : TypeChecker.State) =
        .ok (step.inferred, state) := by
  unfold CandidateCheckTypeStep.Valid at hvalid
  unfold TypeChecker.M.run TypeChecker.checkType
    TypeChecker.RecM.run at hvalid
  simp [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, StateT.bind, Except.bind, Bind.bind,
    StateT.pure, Except.pure, Pure.pure,
    StateT.run', Functor.map, Except.map] at hvalid
  rw [hdepth] at hvalid
  cases hinner :
      TypeChecker.Inner.inferType step.source false
        (TypeChecker.Methods.withFuel recursionFuel)
        { env := step.context.env
          lctx := step.context.lctx
          safety := step.context.safety
          lparams := step.context.lparams
          fuel := step.context.fuel }
        ({} : TypeChecker.State) with
  | error err => simp [hinner] at hvalid
  | ok pair =>
    rcases pair with ⟨observed, state⟩
    have : observed = step.inferred := by
      simpa [hinner] using hvalid
    subst observed
    exact ⟨state, by
      simpa [Context.toTypeChecker] using hinner⟩

/-- Source-indexed retained full-check execution. -/
structure CandidateCheckTypeRun (source : Expr) where
  step : CandidateCheckTypeStep
  source_eq : step.source = source
  valid : step.Valid

def buildCandidateCheckType
    (source : Expr) : M (CandidateCheckTypeRun source) := do
  let context ← readThe Context
  match observeCandidateCheckType context source with
  | .error err => throw err
  | .ok ⟨inferred, valid⟩ =>
    return ⟨⟨context, source, inferred⟩, rfl, valid⟩

/-- Context- and source-indexed tree underlying one candidate expression.
The recursive indices are important: a Pi-domain trace uses the exact parent
context, while its body trace uses precisely `Context.pushLocalDecl` and the
corresponding fresh free variable. Thus both expression position and checker
context provenance are enforced by the type rather than being invariants of
the producer alone. -/
inductive CandidateExprTrace : Context → Expr → Type where
  | terminal (context : Context) (source inferred result : Expr)
      (checked : CandidateCheckTypeStep.Valid
        ⟨context, source, inferred⟩)
      (valid : CandidateWhnfStep.Valid ⟨context, source, result⟩) :
      CandidateExprTrace context source
  | forallE (context : Context) (source : Expr)
      (inferred : Expr)
      (name : Name) (domain body : Expr)
      (binderInfo : BinderInfo)
      (checked : CandidateCheckTypeStep.Valid
        ⟨context, source, inferred⟩)
      (valid : CandidateWhnfStep.Valid
        ⟨context, source, .forallE name domain body binderInfo⟩)
      (domainCandidate : CandidateExprTrace context domain)
      (bodyCandidate : CandidateExprTrace
        (context.pushLocalDecl name binderInfo domain.consumeTypeAnnotations)
        (body.instantiate1 context.freshExpr)) :
      CandidateExprTrace context source

namespace CandidateExprTrace

/-- Candidate expression reconstructed from the traced WHNF/Pi tree. -/
def view : CandidateExprTrace context source → Expr
  | .terminal _ _ _ result _ _ => result
  | .forallE context _ _ name _ _ binderInfo _ _ domain body =>
    .forallE name domain.view
      (body.view.abstract #[context.freshExpr]) binderInfo

/-- Preorder list of all retained checker observations. -/
def steps : CandidateExprTrace context source → List CandidateWhnfStep
  | .terminal context source _ result _ _ => [{ context, source, result }]
  | .forallE context source _ name domain body binderInfo _ _
      domainCandidate bodyCandidate =>
    { context, source,
      result := .forallE name domain body binderInfo } ::
      domainCandidate.steps ++ bodyCandidate.steps

/-- Preorder list of all retained full-check observations. -/
def checkSteps : CandidateExprTrace context source → List CandidateCheckTypeStep
  | .terminal context source inferred _ _ _ =>
    [{ context, source, inferred }]
  | .forallE context source inferred _ _ _ _ _ _
      domainCandidate bodyCandidate =>
    { context, source, inferred } ::
      domainCandidate.checkSteps ++ bodyCandidate.checkSteps

/-- Every retained WHNF observation is an exact checker execution. -/
def allValid : (candidate : CandidateExprTrace context source) →
    ∀ step ∈ candidate.steps, step.Valid
  | .terminal context source _ result _ valid, step, h => by
    simp only [steps, List.mem_singleton] at h
    subst step
    exact valid
  | .forallE _ _ _ _ _ _ _ _ valid domain body, step, h => by
    simp only [steps, List.mem_cons, List.mem_append] at h
    rcases h with (rfl | h) | h
    · exact valid
    · exact domain.allValid step h
    · exact body.allValid step h

/-- Every retained full-check observation is an exact checker execution. -/
def allChecksValid : (candidate : CandidateExprTrace context source) →
    ∀ step ∈ candidate.checkSteps, step.Valid
  | .terminal context source inferred _ checked _, step, h => by
    simp only [checkSteps, List.mem_singleton] at h
    subst step
    exact checked
  | .forallE _ _ _ _ _ _ _ checked _ domain body, step, h => by
    simp only [checkSteps, List.mem_cons, List.mem_append] at h
    rcases h with (rfl | h) | h
    · exact checked
    · exact domain.allChecksValid step h
    · exact body.allChecksValid step h

end CandidateExprTrace

/-- Source-indexed trace for one candidate expression. The tree records the
full-check and WHNF observations at every inspected node and retains the exact
positional split through Pi domains and instantiated bodies. Every node
carries the exact checker-run equalities produced by
`observeCandidateCheckType` and `observeCandidateWhnf`; Theory translation and
semantic refinement are intentionally separate. -/
structure CandidateExpr (source : Expr) where
  context : Context
  trace : CandidateExprTrace context source

def CandidateExpr.view (candidate : CandidateExpr source) : Expr :=
  candidate.trace.view

def CandidateExpr.steps
    (candidate : CandidateExpr source) : List CandidateWhnfStep :=
  candidate.trace.steps

def CandidateExpr.checkSteps
    (candidate : CandidateExpr source) :
    List CandidateCheckTypeStep :=
  candidate.trace.checkSteps

theorem CandidateExpr.step_valid
    (candidate : CandidateExpr source)
    (hstep : step ∈ candidate.steps) :
    step.Valid :=
  candidate.trace.allValid step hstep

theorem CandidateExpr.checkStep_valid
    (candidate : CandidateExpr source)
    (hstep : step ∈ candidate.checkSteps) :
    step.Valid :=
  candidate.trace.allChecksValid step hstep

/-- Normalize exactly the expression positions inspected by inductive
analysis. Each node is fully checked and then exposed with the ordinary
checker `whnf`; Pi domains and bodies are traversed under the same raw local
declarations used by kernel checking. The recursion budget is the configured
inductive fuel, while every checker run uses the configured
transparency/fuel.

The returned trace is only a candidate analysis view and operational
provenance. It is not stored in the kernel environment and acquires semantic
authority only after Verify reconstructs and refines every retained checker
run. -/
def buildCandidateExpr (e : Expr) : M (CandidateExpr e) := do
  let context ← readThe Context
  return ⟨context, ← loop context e context.fuel.inductiveFuel⟩
where
  loop (context : Context) (e : Expr) :
      Nat → Except Exception (CandidateExprTrace context e)
    | 0 => throw .deepRecursion
    | fuel + 1 => do
      match observeCandidateCheckType context e with
      | .error err => throw err
      | .ok ⟨inferred, checked⟩ =>
        match observeCandidateWhnf context e with
        | .error err => throw err
        | .ok ⟨view, valid⟩ =>
          match view with
          | .forallE name domain body binderInfo =>
            let domainCandidate ← loop context domain fuel
            let bodyContext :=
              context.pushLocalDecl name binderInfo
                domain.consumeTypeAnnotations
            let bodyCandidate ← loop bodyContext
              (body.instantiate1 context.freshExpr) fuel
            return .forallE context e inferred name domain body
              binderInfo checked valid domainCandidate bodyCandidate
          | result =>
            return .terminal context e inferred result checked valid

/-- Erase the operational trace and retain only the analysis expression. -/
def normalizeCandidateExpr (e : Expr) : M Expr := do
  return (← buildCandidateExpr e).view

/-- A successful ordinary WHNF run to a non-Pi expression is exactly one
terminal step of the candidate traversal. This exposes the operational seam
used by Verify without duplicating the `ReaderT`/checker lift plumbing in
every certificate. -/
theorem buildCandidateExpr_of_whnf_nonForall
    (context : Context) (e inferred view : Expr)
    (hfuel : 0 < context.fuel.inductiveFuel)
    (hcheck :
      TypeChecker.M.run context.env context.safety context.lctx
          context.lparams context.fuel (TypeChecker.checkType e) =
        .ok inferred)
    (hrun :
      TypeChecker.M.run context.env context.safety context.lctx
          context.lparams context.fuel (TypeChecker.whnf e) =
        .ok view)
    (hview : view.isForall = false) :
    buildCandidateExpr e context =
      .ok ⟨context, .terminal context e inferred view hcheck hrun⟩ := by
  cases hf : context.fuel.inductiveFuel with
  | zero => omega
  | succ fuel =>
    cases hresult :
        TypeChecker.M.run context.env context.safety context.lctx
          context.lparams context.fuel (TypeChecker.whnf e) with
    | error err => simp [hresult] at hrun
    | ok result =>
      have : result = view := by simpa [hresult] using hrun
      subst result
      unfold buildCandidateExpr
      unfold buildCandidateExpr.loop
      simp [readThe, MonadReaderOf.read, ReaderT.read,
        ReaderT.bind, Bind.bind, Pure.pure, Except.bind, Except.pure,
        hf, observeCandidateCheckType_of_run context e inferred hcheck,
        observeCandidateWhnf_of_run context e view hrun]
      cases view <;>
        simp_all [ReaderT.pure, Pure.pure, Except.pure, Expr.isForall]

theorem normalizeCandidateExpr_of_whnf_nonForall
    (context : Context) (e inferred view : Expr)
    (hfuel : 0 < context.fuel.inductiveFuel)
    (hcheck :
      TypeChecker.M.run context.env context.safety context.lctx
          context.lparams context.fuel (TypeChecker.checkType e) =
        .ok inferred)
    (hrun :
      TypeChecker.M.run context.env context.safety context.lctx
          context.lparams context.fuel (TypeChecker.whnf e) =
        .ok view)
    (hview : view.isForall = false) :
    normalizeCandidateExpr e context = .ok view := by
  simp [normalizeCandidateExpr, ReaderT.bind, Bind.bind,
    ReaderT.pure, Pure.pure, Except.bind, Except.pure,
    CandidateExpr.view, CandidateExprTrace.view,
    buildCandidateExpr_of_whnf_nonForall context e inferred view
      hfuel hcheck hrun hview]

/-- A dependent list retains the exact source position of each candidate. -/
inductive CandidateList {α : Type} (F : α → Type) : List α → Type
  | nil : CandidateList F []
  | cons : F a → CandidateList F as → CandidateList F (a :: as)

namespace CandidateList

def toList (f : (a : α) → F a → β) :
    CandidateList F source → List β
  | .nil => []
  | .cons head tail => f _ head :: tail.toList f

end CandidateList

/-- Candidate for one constructor; its header is always taken from `source`. -/
structure CandidateConstructor (source : Constructor) where
  type : CandidateExpr source.type

def CandidateConstructor.view
    (candidate : CandidateConstructor source) : Constructor :=
  { source with type := candidate.type.view }

/-- Candidate for one family type, computed before raw family insertion. -/
structure CandidateFamilyType (source : InductiveType) where
  type : CandidateExpr source.type

/-- Complete candidate for one family, with constructor traces computed only
after raw family insertion. -/
structure CandidateFamily (source : InductiveType) where
  familyType : CandidateFamilyType source
  constructors :
    CandidateList CandidateConstructor source.ctors

def CandidateFamily.view (candidate : CandidateFamily source) : InductiveType :=
  { source with
    type := candidate.familyType.type.view
    ctors := candidate.constructors.toList fun _ ctor => ctor.view }

def normalizeCandidateConstructor
    (ctor : Constructor) : M (CandidateConstructor ctor) := do
  return ⟨← buildCandidateExpr ctor.type⟩

def normalizeCandidateFamilyType
    (indType : InductiveType) : M (CandidateFamilyType indType) := do
  return ⟨← buildCandidateExpr indType.type⟩

def normalizeCandidateConstructorList :
    (ctors : List Constructor) →
      M (CandidateList CandidateConstructor ctors)
  | [] => return .nil
  | ctor :: ctors => do
    return .cons (← normalizeCandidateConstructor ctor)
      (← normalizeCandidateConstructorList ctors)

def normalizeCandidateFamilyTypeList :
    (types : List InductiveType) →
      M (CandidateList CandidateFamilyType types)
  | [] => return .nil
  | indType :: types => do
    return .cons (← normalizeCandidateFamilyType indType)
      (← normalizeCandidateFamilyTypeList types)

def normalizeCandidateFamilyList :
    {types : List InductiveType} →
      CandidateList CandidateFamilyType types →
      M (CandidateList CandidateFamily types)
  | [], .nil => return .nil
  | indType :: _, .cons familyType tail => do
    return .cons
      { familyType,
        constructors := ←
          normalizeCandidateConstructorList indType.ctors }
      (← normalizeCandidateFamilyList tail)

/-- Shape-preserving output of the executable normalization-candidate pass.
The dependent family/constructor lists prevent positional provenance from
being silently reused for a different inductive request. Names, ordering, and
record headers come from the indexed source; only expression payloads are
reconstructed from candidate traces. -/
structure NormalizationCandidate (source : List InductiveType) where
  families : CandidateList CandidateFamily source

def NormalizationCandidate.view
    (candidate : NormalizationCandidate source) : List InductiveType :=
  candidate.families.toList fun _ family => family.view

/-- Run the generic one-pass candidate producer at the same two environments
as kernel inductive checking: family types in the input environment, then
constructor types after insertion of every raw family constant.

This repeats the ordinary family/constructor validity checks so a candidate
cannot be obtained from metadata already rejected at those stages. The Theory
analyzer and Verify semantic certificate remain separate downstream gates. -/
def buildNormalizationCandidate
    (nparams : Nat) (types : List InductiveType)
    (numNested : Nat) (isUnsafe : Bool) :
    M (NormalizationCandidate types) := do
  let indTypes := types.toArray
  checkInductiveTypes nparams indTypes fun stats => do
    let familyTypes ←
      withReader (fun c : Context => { c with lctx := {} }) do
        normalizeCandidateFamilyTypeList types
    let familyEnv ←
      declareInductiveTypes stats nparams indTypes numNested isUnsafe
    withEnv familyEnv do
      checkConstructors indTypes stats isUnsafe
      return ⟨← normalizeCandidateFamilyList familyTypes⟩

/--
info: 'Lean4Lean.AddInductive.buildCandidateExpr' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms buildCandidateExpr

/--
info: 'Lean4Lean.AddInductive.buildCandidateCheckType' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms buildCandidateCheckType

/--
info: 'Lean4Lean.AddInductive.buildNormalizationCandidate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms buildNormalizationCandidate

/--
info: 'Lean4Lean.AddInductive.CandidateExpr.step_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CandidateExpr.step_valid

/--
info: 'Lean4Lean.AddInductive.CandidateExpr.checkStep_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CandidateExpr.checkStep_valid

/--
info: 'Lean4Lean.AddInductive.CandidateWhnfStep.innerRun' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CandidateWhnfStep.innerRun

/--
info: 'Lean4Lean.AddInductive.CandidateCheckTypeStep.innerRun' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CandidateCheckTypeStep.innerRun

def declareConstructors (stats : InductiveStats)
    (indTypes : Array InductiveType) (isUnsafe : Bool) : M Environment :=
  fun c => indTypes.foldlM (init := c.env) fun env indType => do
    let (_, env) ← indType.ctors.foldlM (init := (0, env)) fun (cidx, env) ctor => do
      let type := ctor.type
      let rec arity i
        | .forallE _ _ body _ => arity (i+1) body
        | _ => i
      let arity := arity 0 type
      env.checkName ctor.name c.allowPrimitive
      pure (cidx + 1, env.add <| .ctorInfo {
        type, cidx, isUnsafe
        levelParams := c.lparams
        name := ctor.name
        induct := indType.name
        numParams := stats.params.size
        numFields := assert! arity ≥ stats.params.size; arity - stats.params.size
      })
    pure env

/-- Return true if recursor can map into any universe -/
def isLargeEliminator (stats : InductiveStats) (indTypes : Array InductiveType) : M Bool := do
  if stats.isNotZero then return true
  let #[indType] := indTypes | return false
  match indType.ctors with
  | [] => return true
  | [ctor] =>
    let rec loop type i toCheck
    | 0 => throw .deepRecursion
    | fuel+1 => do
      if let .forallE name dom body bi := type then
        withLocalDecl name bi dom.consumeTypeAnnotations fun arg => do
          let mut toCheck := toCheck
          if i ≥ stats.params.size then
            if !(← ensureType dom).sortLevel!.isZero then
              toCheck := toCheck.push arg
          loop (body.instantiate1 arg) (i + 1) toCheck fuel
      else
        return toCheck.all type.getAppArgs.contains
    loop ctor.type 0 #[] (← readThe Context).fuel.inductiveFuel
  | _ => return false

partial -- TODO: remove
def getElimLevel (stats : InductiveStats) (indTypes : Array InductiveType) :
    M Level := do
  unless ← isLargeEliminator stats indTypes do return .zero
  let {lparams, ..} ← read
  let rec loop u i := Id.run do
    unless lparams.contains u do return .param u
    loop ((`u).appendIndexAfter i) (i + 1)
  return loop `u 1

def isKTarget (stats : InductiveStats) (indTypes : Array InductiveType) : M Bool := do
  let #[indType] := indTypes | return false
  unless stats.resultLevel.isZero do return false
  let [ctor] := indType.ctors | return false
  let rec loop i
    | .forallE _ _ body _ => i < stats.params.size && loop (i + 1) body
    | _ => true
  return loop 0 ctor.type

@[inline] def getIIndices (stats : InductiveStats) (t : Expr) : Nat × Array Expr :=
  ((isValidIndApp? stats t).get!, t.getAppArgs[stats.params.size:])

-- FIXME: The function below has been exploded into nested loops as standalone functions
-- because I couldn't get them all to compile together as `let rec`s.
namespace mkRecInfos

def loopArgs1 (stats : InductiveStats) (type : Expr) (i : Nat) (indices : Array Expr)
    (fuel : Nat) (k : Array Expr → M α) : M α := match fuel with
  | 0 => throw .deepRecursion
  | fuel+1 => do
    if let .forallE name dom body bi := type then
      if i < stats.params.size then
        loopArgs1 stats (← whnf <| body.instantiate1 stats.params[i]!) (i + 1) indices fuel k
      else
        withLocalDecl name bi dom.consumeTypeAnnotations fun arg => do
        loopArgs1 stats (← whnf <| body.instantiate1 arg) i (indices.push arg) fuel k
    else
      k indices

variable (stats : InductiveStats) (indTypes : Array InductiveType) (elimLevel : Level) in
def loopInd1 (dIdx : Nat) (recInfos : Array RecInfo) (k : Array RecInfo → M α) : M α := do
  if _h : dIdx < indTypes.size then
    let ctx ← readThe Context
    loopArgs1 stats (← whnf indTypes[dIdx].type) 0 #[] ctx.fuel.inductiveFuel fun indices =>
    let tTy := mkAppN (mkAppN stats.indConsts[dIdx]! stats.params) indices
    withLocalDecl `t .default tTy.consumeTypeAnnotations fun major => do
    let lctx ← getLCtx
    let motiveTy := lctx.mkForall indices <| lctx.mkForall #[major] <| .sort elimLevel
    let name := if indTypes.size > 1 then (`motive).appendIndexAfter (dIdx+1) else `motive
    withLocalDecl name .default motiveTy.consumeTypeAnnotations fun motive => do
    loopInd1 (dIdx + 1) (recInfos.push { motive, minors := #[], indices, major }) k
  else
    k recInfos
termination_by indTypes.size - dIdx

variable (stats : InductiveStats) in
def loopCtorArgs (t : Expr) (k : Expr → Array Expr → Array Expr → M α) : M α := do
  loop t 0 #[] #[] (← readThe Context).fuel.inductiveFuel
where
  loop t i bu u
  | 0 => throw .deepRecursion
  | fuel+1 => do
    if let .forallE name dom body bi := t then
      if let some param := stats.params[i]? then
        loop (body.instantiate1 param) (i + 1) bu u fuel
      else
        withLocalDecl name bi dom.consumeTypeAnnotations fun arg => do
        let bu := bu.push arg
        let u := if (← isRecArg stats dom).isSome then u.push arg else u
        loop (body.instantiate1 arg) (i + 1) bu u fuel
    else k t bu u

def loopUArgs (ui : Expr) (k : Expr → Array Expr → M α) : M α := do
  loop (← whnf (← inferType ui)) #[] (← readThe Context).fuel.inductiveFuel
where
  loop uiTy xs
  | 0 => throw .deepRecursion
  | fuel+1 => do
    if let .forallE name dom body bi := uiTy then
      withLocalDecl name bi dom.consumeTypeAnnotations fun arg => do
      loop (← whnf <| body.instantiate1 arg) (xs.push arg) fuel
    else
      k uiTy xs

variable (stats : InductiveStats) (u : Array Expr) (recInfos : Array RecInfo) in
def loopU (i : Nat) (v : Array Expr) (k : Array Expr → M α) : M α := do
  if _h : i < u.size then
    let ui := u[i]
    let viTy ← loopUArgs ui fun uiTy xs => do
      let (itIdx, itIndices) := getIIndices stats uiTy
      return (← getLCtx).mkForall xs <|
        .app (mkAppN recInfos[itIdx]!.motive itIndices) (mkAppN ui xs)
    let vName := ((← getLCtx).get! ui.fvarId!).userName.appendAfter "_ih"
    withLocalDecl vName .default viTy.consumeTypeAnnotations fun vi => do
    loopU (i + 1) (v.push vi) k
  else
    k v
termination_by u.size - i

variable (stats : InductiveStats) (indTypeName : Name) (dIdx : Nat) in
def loopCtors (recInfos : Array RecInfo)
    (ctors : List Constructor) (k : Array RecInfo → M α) : M α := match ctors with
  | ctor::ctors =>
    loopCtorArgs stats ctor.type fun t bu u => do
    let (itIdx, itIndices) := getIIndices stats t
    let introApp := mkAppN (mkAppN (.const ctor.name stats.levels) stats.params) bu
    let motiveApp := Expr.app (mkAppN recInfos[itIdx]!.motive itIndices) introApp
    loopU stats u recInfos 0 #[] fun v => do
    let lctx ← getLCtx
    let minorTy := lctx.mkForall bu <| lctx.mkForall v motiveApp
    let minorName := ctor.name.replacePrefix indTypeName .anonymous
    withLocalDecl minorName .default minorTy.consumeTypeAnnotations fun minor => do
    let recInfos := recInfos.modify dIdx fun s => { s with minors := s.minors.push minor }
    loopCtors recInfos ctors k
  | [] => k recInfos

variable (stats : InductiveStats) (indTypes : Array InductiveType) in
def loopInd2 (dIdx : Nat) (recInfos : Array RecInfo) (k : Array RecInfo → M α) : M α := do
  if _h : dIdx < indTypes.size then
    let indType := indTypes[dIdx]
    let indTypeName := indType.name
    loopCtors stats indTypeName dIdx recInfos indType.ctors fun recInfos =>
    loopInd2 (dIdx + 1) recInfos k
  else
    k recInfos
termination_by indTypes.size - dIdx

end mkRecInfos

def mkRecInfos (stats : InductiveStats) (indTypes : Array InductiveType)
    (elimLevel : Level) (k : Array RecInfo → M α) : M α :=
  mkRecInfos.loopInd1 stats indTypes elimLevel 0 #[] fun recInfos =>
  mkRecInfos.loopInd2 stats indTypes 0 recInfos k

def getRecLevels (elimLevel : Level) (levels : List Level) : List Level :=
  if elimLevel.isParam then elimLevel :: levels else levels

def getRecLevelParams (elimLevel : Level) (lparams : List Name) : List Name :=
  if let .param u := elimLevel then u :: lparams else lparams

def mkRecRules (indTypes : Array InductiveType) (elimLevel : Level) (stats : InductiveStats)
    (dIdx : Nat) (motives : Array Expr) (minors : Array Expr) :
    StateT Nat M (List RecursorRule) := do
  let d := indTypes[dIdx]!
  let lvls := getRecLevels elimLevel stats.levels
  let mut rules := #[]
  for ctor in d.ctors do
    let rule ← fun minorIdx => mkRecInfos.loopCtorArgs stats ctor.type fun _ bu u =>
      let rec loopU i (v : Array Expr) k := do
        if _h : i < u.size then
          let ui := u[i]
          let val ← mkRecInfos.loopUArgs ui fun uiTy xs => do
            let (itIdx, itIndices) := getIIndices stats uiTy
            let val := .const (mkRecName indTypes[itIdx]!.name) lvls
            let val := mkAppN (mkAppN (mkAppN (mkAppN val stats.params) motives) minors) itIndices
            return (← getLCtx).mkLambda xs <| val.app (mkAppN ui xs)
          loopU (i + 1) (v.push val) k
        else
          k v
      termination_by u.size - i
      loopU 0 #[] fun v => do
      let lctx ← getLCtx
      let rule := {
        ctor := ctor.name
        nfields := bu.size
        rhs := lctx.mkLambda stats.params <| lctx.mkLambda motives <|
          lctx.mkLambda minors <| lctx.mkLambda bu <|
          mkAppN (mkAppN minors[minorIdx]! bu) v
      }
      return (rule, minorIdx + 1)
    rules := rules.push rule
  return rules.toList

def run (nparams : Nat) (types : List InductiveType) (numNested : Nat) : M Environment := do
  let isUnsafe := (← read).safety != .safe
  let indTypes := types.toArray
  let {lparams, ..} ← read
  Environment.checkDuplicatedUnivParams lparams
  checkInductiveTypes nparams indTypes fun stats => do
  withEnv (← declareInductiveTypes stats nparams indTypes numNested isUnsafe) do
  checkConstructors indTypes stats isUnsafe
  withEnv (← declareConstructors stats indTypes isUnsafe) do
  let elimLevel ← getElimLevel stats indTypes
  mkRecInfos stats indTypes elimLevel fun recInfos => do
  let motives := recInfos.map (·.motive)
  let minors := recInfos.flatMap (·.minors)
  let numMinors := minors.size
  let numMotives := motives.size
  let all := indTypes.map (·.name) |>.toList
  let lctx ← getLCtx
  let k ← isKTarget stats indTypes
  let isUnsafe := (← read).safety != .safe
  StateT.run' (s := 0) do
  let mut env ← getEnv
  let {allowPrimitive, ..} ← read
  for h : dIdx in [:indTypes.size] do
    let indType := indTypes[dIdx]
    let info := recInfos[dIdx]!
    let ty :=
      lctx.mkForall stats.params <|
      lctx.mkForall motives <|
      lctx.mkForall minors <|
      lctx.mkForall info.indices <|
      lctx.mkForall #[info.major] <|
      .app (mkAppN info.motive info.indices) info.major
    let rules ← mkRecRules indTypes elimLevel stats dIdx motives minors
    let name := mkRecName indType.name
    env.checkName name allowPrimitive
    env := env.add <| .recInfo {
      levelParams := getRecLevelParams elimLevel lparams
      type := ty.inferImplicit 1000 false -- note: flag has reversed polarity from C++
      numParams := stats.params.size
      numIndices := stats.nindices[dIdx]!
      name, all, numMotives, numMinors, rules, k, isUnsafe
    }
  pure env

end AddInductive

namespace ElimNestedInductive

structure Result where
  ngen : NameGenerator
  nparams : Nat
  lctx : LocalContext
  aux2nested : NameMap Expr -- exprs contain `nparams` loose bvars
  types : List InductiveType

instance [MonadStateOf NameGenerator m] : MonadNameGenerator m where
  getNGen := get
  setNGen := set

namespace Result

def getNestedIfAuxCtor (r : Result) (env' : Environment) (c : Name) : Option (Expr × Name) := do
  let .ctorInfo { induct, .. } ← env'.find? c | none
  return (← r.aux2nested.find? induct, induct)

def restoreCtorName (r : Result) (env' : Environment) (c : Name) : Name := Id.run do
  let (e, name) := (r.getNestedIfAuxCtor env' c).get!
  let .const I _ := e.getAppFn | unreachable!
  c.replacePrefix name I

def restoreNested (r : Result) (env' : Environment) (e : Expr)
    (auxRec : NameMap Name := {}) : Expr :=
  Id.run <| StateT.run' (s := { namePrefix := `_nested_fresh : NameGenerator }) do
  let pi := e.isForall
  let mut e := e
  let mut As := #[]
  let mut lctx : LocalContext := {}
  for _ in [:r.nparams] do
    match e with
    | .forallE name dom body bi | .lam name dom body bi =>
      let id := ⟨← mkFreshId⟩
      lctx := lctx.mkLocalDecl id name dom bi
      let arg := .fvar id
      e := body.instantiate1 arg
      As := As.push arg
    | _ => unreachable!
  e := e.replace fun t => do
    if let .const c ls := t then
      if let some recName := auxRec.find? c then
        return .const recName ls
    let .const c _ := t.getAppFn | none
    if let some nested := r.aux2nested.find? c then
      let args := t.getAppArgs
      assert! args.size ≥ r.nparams
      return mkAppRange (nested.instantiateRev As) r.nparams args.size args
    let (nested, auxI_name) ← r.getNestedIfAuxCtor env' c
    let args := t.getAppArgs
    assert! args.size ≥ r.nparams
    let nested' := nested.instantiateRev As
    nested'.withApp fun I I_args => do
    let .const I_c I_ls := I | unreachable!
    let c' := .const (c.replacePrefix auxI_name I_c) I_ls
    return mkAppRange (mkAppN c' I_args) r.nparams args.size args
  return if pi then lctx.mkForall As e else lctx.mkLambda As e

end Result

structure State where
  ngen : NameGenerator := { namePrefix := `_nested_fresh }
  nestedAux : Array (Expr × Name) := {}
  lvls : List Level
  newTypes : Array InductiveType
  nextIdx : Nat := 1
  deriving Inhabited

abbrev M := ReaderT Environment <| StateT State <| Except Exception

instance : MonadNameGenerator M where
  getNGen := return (← get).ngen
  setNGen ngen := modify fun s => { s with ngen }

-- TODO: remove partial
partial def mkUniqueName (n : Name) : M Name := fun env s =>
  let rec loop i :=
    let r := n.appendIndexAfter i
    if env.contains r then
      loop (i + 1)
    else
      pure (r, { s with nextIdx := i + 1 })
  loop s.nextIdx

def illFormed : Exception :=
  .other "invalid nested inductive datatype, ill-formed declaration"

def replaceParams (params : Array Expr) (e : Expr) (As : Array Expr) : M Expr := do
  assert! As.size == params.size
  return (e.abstract As).instantiateRev params

/-- IF `e` is of the form `I Ds is` where
  1) `I` is a nested inductive datatype (i.e., a previously declared inductive datatype),
  2) the parametric arguments `Ds` do not contain loose bound variables, and do contain inductive datatypes in `m_new_types`
THEN return the `inductive_val` in the `constant_info` associated with `I`.
Otherwise, return none. -/
def isNestedInductiveApp? (e : Expr) : M (Option InductiveVal) := do
  if !e.isApp then return none
  let .const fn _ := e.getAppFn | return none
  let env ← read
  let some (.inductInfo ci) := env.find? fn | return none
  let args := e.getAppArgs
  if ci.numParams > args.size then return none
  let mut isNested := false
  let mut looseBVars := false
  for i in [0:ci.numParams] do
    if args[i]!.hasLooseBVars then
      looseBVars := true
    let newTypes := (← get).newTypes
    if let some _ := args[i]!.find? fun
      | .const t _ => newTypes.any fun ty => t == ty.name
      | _ => false
    then
      isNested := true
  if !isNested then return none
  if looseBVars then
    throw <| .other s!"invalid nested inductive datatype '{fn}', \
      nested inductive datatypes parameters cannot contain local variables."
  return some ci

def instantiateForallParams (e : Expr) (hi : Nat) (params : Array Expr) :
    Except Exception Expr := do
  let mut e := e
  for _ in [:hi] do
    let .forallE _ _ body _ := e | throw illFormed
    e := body
  return e.instantiateRevRange 0 hi params

/-- If `e` is a nested occurrence `I Ds is`, return `Iaux As is` -/
def replaceIfNested (lctx : LocalContext) (params : Array Expr) (As : Array Expr) (e : Expr) :
    M (Option Expr) := do
  let some I_val ← isNestedInductiveApp? e | return none
  e.withApp fun fn args => do
  let .const I_name I_lvls := fn | unreachable!
  let I_nparams := I_val.numParams
  assert! I_nparams ≤ args.size
  let IAs := mkAppRange fn 0 I_nparams args -- `I As`
  let Iparams ← replaceParams params IAs As
  let st ← get
  if let some auxI_name := st.nestedAux.findSome? fun (e, n) =>
    if e == Iparams then some n else none
  then
    return mkAppRange (mkAppN (.const auxI_name st.lvls) As) I_nparams args.size args
  let mut result := none
  let env ← read
  for J_name in I_val.all do
    let .inductInfo J_info ← env.get J_name | unreachable!
    let J := .const J_name I_lvls
    let JAs := mkAppRange J 0 I_nparams args
    let auxJ_name ← mkUniqueName (`_nested ++ J_name)
    let auxJ_type := J_info.type.instantiateLevelParams J_info.levelParams I_lvls
    let auxJ_type := lctx.mkForall As <| ← instantiateForallParams auxJ_type I_nparams args
    let JAs' ← replaceParams params JAs As
    modify fun st => { st with nestedAux := st.nestedAux.push (JAs', auxJ_name) }
    if J_name == I_name then
      result := some <|
        mkAppRange (mkAppN (.const auxJ_name (← get).lvls) As) I_nparams args.size args
    let auxJ_ctors ← J_info.ctors.mapM fun J_ctor_name => do
      let J_ctor_info ← env.get J_ctor_name
      -- auxJ_cnstr_type still has references to `J`, this will be fixed later when we process it.
      let auxJ_ctor_name := J_ctor_name.replacePrefix J_name auxJ_name
      let auxJ_ctor_type := J_ctor_info.type.instantiateLevelParams J_ctor_info.levelParams I_lvls
      let auxJ_ctor_type ← instantiateForallParams auxJ_ctor_type I_nparams args
      return { name := auxJ_ctor_name, type := lctx.mkForall As auxJ_ctor_type }
    let newType := { name := auxJ_name, type := auxJ_type, ctors := auxJ_ctors }
    modify fun st => { st with newTypes := st.newTypes.push newType }
  assert! result.isSome
  return result

def replaceAllNested (lctx : LocalContext) (params : Array Expr) (As : Array Expr) (e : Expr) :
    M Expr := e.replaceM (replaceIfNested lctx params As)

def withParams (type : Expr) (nparams : Nat)
    (k : LocalContext → Expr → Array Expr → M α) : M α := loop {} type #[] nparams where
  loop lctx type params
  | 0 => k lctx type params
  | i+1 => do
    let .forallE name dom body bi := type
      | throw <| .other "invalid inductive datatype declaration, incorrect number of parameters"
    let id := ⟨← mkFreshId⟩
    let lctx := lctx.mkLocalDecl id name dom bi
    let arg := .fvar id
    loop lctx (body.instantiate1 arg) (params.push arg) i

def run (fuel nparams : Nat) (types : List InductiveType) : M Result := do
  let I :: _ := types
    | throw <| .other s!"invalid empty (mutual) inductive datatype declaration, \
        it must contain at least one inductive type."
  withParams I.type nparams fun lctx _ params => do
  let rec loop i
  | 0 => throw <| .other "deep recursion: ElimNestedInductive.run.loop"
  | fuel+1 => do
    let s ← get
    if _h : i < s.newTypes.size then
      let indType := s.newTypes[i]
      let ctors ← indType.ctors.mapM fun ctor => do
        withParams ctor.type nparams fun lctx ctorType As => do
        assert! As.size == nparams
        return { ctor with type := lctx.mkForall As (← replaceAllNested lctx params As ctorType) }
      modify fun s => { s with newTypes := s.newTypes.set! i { indType with ctors } }
      loop (i+1) fuel
    else
      let aux2nested := s.nestedAux.foldl (fun m (e, n) => m.insert n (e.abstract params)) {}
      return { s with nparams := params.size, lctx, aux2nested, types := s.newTypes.toList }
  loop 0 fuel
end ElimNestedInductive

def mkAuxRecNameMap (env' : Environment) (types : List InductiveType) :
    List Name × NameMap Name := Id.run do
  let mainType :: _ := types | unreachable!
  let ntypes := types.length
  let mainName := mainType.name
  let some (.inductInfo mainInfo) := env'.find? mainName | unreachable!
  let allNames := mainInfo.all
  assert! allNames.length > ntypes
  let mut oldRecNames := #[]
  let mut recMap : NameMap Name := {}
  let mut nextIdx := 1
  for indName in allNames.drop ntypes do
    let oldRecName := mkRecName indName
    let newRecName := (mkRecName mainName).appendIndexAfter nextIdx
    nextIdx := nextIdx + 1
    recMap := recMap.insert oldRecName newRecName
    oldRecNames := oldRecNames.push oldRecName
  return (oldRecNames.toList, recMap)

def Environment.addInductive (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe allowPrimitive : Bool) (fuel : FuelConfig := {}) :
    Except Exception Environment := do
  let res ← ElimNestedInductive.run fuel.inductiveFuel nparams types env
    |>.run' { lvls := lparams.map .param, newTypes := types.toArray }
  let numNested := res.aux2nested.size
  let safety := if isUnsafe then .unsafe else .safe
  let env' ← AddInductive.run nparams res.types numNested
    { env, allowPrimitive, lparams, fuel, safety }
  if numNested = 0 then return env'
  let allIndNames := types.map (·.name)
  let (recNames', recNameMap') := mkAuxRecNameMap env' types
  (·.2) <$> StateT.run (s := env) do
  let processRec recName := do
    let newRecName := recNameMap'.getD recName recName
    let some (.recInfo recInfo) := env'.find? recName | unreachable!
    let newRecType := res.restoreNested env' recInfo.type recNameMap'
    let newRules ← recInfo.rules.mapM fun rule => do
      let newRhs := res.restoreNested env' rule.rhs recNameMap'
      let newCtorName := if newRecName == recName then rule.ctor else
        res.restoreCtorName env' rule.ctor
      return { rule with ctor := newCtorName, rhs := newRhs }
    (← MonadState.get).checkName newRecName allowPrimitive
    modify (·.add <| .recInfo { recInfo with
      name := newRecName, type := newRecType, all := allIndNames, rules := newRules })
  for indType in types do
    let some (.inductInfo ind) := env'.find? indType.name | unreachable!
    (← get).checkName ind.name allowPrimitive
    modify (·.add <| .inductInfo { ind with all := allIndNames })
    for ctorName in ind.ctors do
      let some (.ctorInfo ctor) := env'.find? ctorName | unreachable!
      let newType := res.restoreNested env' ctor.type
      (← get).checkName ctor.name allowPrimitive
      modify (·.add <| .ctorInfo { ctor with type := newType })
    processRec (mkRecName indType.name)
  recNames'.forM processRec
  TypeChecker.M.run (← get) (safety := safety) (lctx := res.lctx)
      (lparams := lparams) (fuel := fuel) do
    res.aux2nested.forM fun _ e => do _ ← TypeChecker.checkType e
