import Lean4Lean.Inductive.ValidationTrace

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace AddInductive
open TypeChecker

/-- Exact successful traversal of the singleton-constructor branch of
`isLargeEliminator`. Non-parameter fields retain the precise `ensureType`
observation used to decide whether their local is relevant to the terminal
index-occurrence check. -/
inductive LargeEliminatorLoopTrace (stats : InductiveStats) :
    (context : Context) → (source : Expr) → (argIdx : Nat) →
      (toCheck : Array Expr) → (fuel : Nat) → (result : Bool) → Type where
  | parameter
      (context : Context) (fuel argIdx : Nat) (toCheck : Array Expr)
      (name : Name) (domain body : Expr) (binderInfo : BinderInfo)
      (isParameter : argIdx < stats.params.size)
      (tail : LargeEliminatorLoopTrace stats
        (context.pushLocalDecl name binderInfo
          (consumeTypeAnnotations domain))
        (body.instantiate1 context.freshExpr) (argIdx + 1) toCheck fuel result) :
      LargeEliminatorLoopTrace stats context
        (.forallE name domain body binderInfo) argIdx toCheck (fuel + 1) result
  | proofField
      (context : Context) (fuel argIdx : Nat) (toCheck : Array Expr)
      (name : Name) (domain body : Expr) (binderInfo : BinderInfo)
      (sortResult : Expr)
      (isField : argIdx ≥ stats.params.size)
      (ensureType : ConstructorEnsureTypeStep.Valid
        ⟨context.pushLocalDecl name binderInfo
          (consumeTypeAnnotations domain), domain, sortResult⟩)
      (isProp : sortResult.sortLevel!.isAlwaysZero = true)
      (tail : LargeEliminatorLoopTrace stats
        (context.pushLocalDecl name binderInfo
          (consumeTypeAnnotations domain))
        (body.instantiate1 context.freshExpr) (argIdx + 1) toCheck fuel result) :
      LargeEliminatorLoopTrace stats context
        (.forallE name domain body binderInfo) argIdx toCheck (fuel + 1) result
  | dataField
      (context : Context) (fuel argIdx : Nat) (toCheck : Array Expr)
      (name : Name) (domain body : Expr) (binderInfo : BinderInfo)
      (sortResult : Expr)
      (isField : argIdx ≥ stats.params.size)
      (ensureType : ConstructorEnsureTypeStep.Valid
        ⟨context.pushLocalDecl name binderInfo
          (consumeTypeAnnotations domain), domain, sortResult⟩)
      (isProp : sortResult.sortLevel!.isAlwaysZero = false)
      (tail : LargeEliminatorLoopTrace stats
        (context.pushLocalDecl name binderInfo
          (consumeTypeAnnotations domain))
        (body.instantiate1 context.freshExpr) (argIdx + 1)
        (toCheck.push context.freshExpr) fuel result) :
      LargeEliminatorLoopTrace stats context
        (.forallE name domain body binderInfo) argIdx toCheck (fuel + 1) result
  | terminal
      (context : Context) (source : Expr) (fuel argIdx : Nat)
      (toCheck : Array Expr) (notForall : source.isForall = false) :
      LargeEliminatorLoopTrace stats context source argIdx toCheck (fuel + 1)
        (toCheck.all source.getAppArgs.contains)

namespace LargeEliminatorLoopTrace

def parameterCount
    (trace : LargeEliminatorLoopTrace stats context source argIdx toCheck
      fuel result) : Nat :=
  match trace with
  | .parameter (tail := tail) .. => tail.parameterCount + 1
  | .proofField (tail := tail) .. => tail.parameterCount
  | .dataField (tail := tail) .. => tail.parameterCount
  | .terminal .. => 0

def proofFieldCount
    (trace : LargeEliminatorLoopTrace stats context source argIdx toCheck
      fuel result) : Nat :=
  match trace with
  | .parameter (tail := tail) .. => tail.proofFieldCount
  | .proofField (tail := tail) .. => tail.proofFieldCount + 1
  | .dataField (tail := tail) .. => tail.proofFieldCount
  | .terminal .. => 0

def dataFieldCount
    (trace : LargeEliminatorLoopTrace stats context source argIdx toCheck
      fuel result) : Nat :=
  match trace with
  | .parameter (tail := tail) .. => tail.dataFieldCount
  | .proofField (tail := tail) .. => tail.dataFieldCount
  | .dataField (tail := tail) .. => tail.dataFieldCount + 1
  | .terminal .. => 0

/-- Erasing the retained singleton trace replays the exact ordinary checker
loop, including every `ensureType` call and local declaration. -/
theorem run
    (trace : LargeEliminatorLoopTrace stats context source argIdx toCheck
      fuel result) :
    isLargeEliminator.loop stats source argIdx toCheck fuel context =
      .ok result := by
  induction trace with
  | parameter context fuel argIdx toCheck name domain body binderInfo
      isParameter tail ih =>
      rw [show fuel + 1 = Nat.succ fuel by omega]
      rw [isLargeEliminator.loop.eq_2, withLocalDecl_apply]
      have notField : ¬ argIdx ≥ stats.params.size :=
        Nat.not_le.mpr isParameter
      simp only [notField, if_false, Bind.bind]
      exact ih
  | proofField context fuel argIdx toCheck name domain body binderInfo
      sortResult isField ensureStep isProp tail ih =>
      rw [show fuel + 1 = Nat.succ fuel by omega]
      rw [isLargeEliminator.loop.eq_2, withLocalDecl_apply]
      simp only [isField, if_true, ReaderT.bind, Bind.bind,
        liftTypeChecker_apply]
      rw [ensureStep]
      simp only [Except.bind, isProp, Bool.not_true, Bool.false_eq_true, if_false]
      exact ih
  | dataField context fuel argIdx toCheck name domain body binderInfo
      sortResult isField ensureStep isProp tail ih =>
      rw [show fuel + 1 = Nat.succ fuel by omega]
      rw [isLargeEliminator.loop.eq_2, withLocalDecl_apply]
      simp only [isField, if_true, ReaderT.bind, Bind.bind,
        liftTypeChecker_apply]
      rw [ensureStep]
      simp only [Except.bind, isProp, Bool.not_false, if_true]
      exact ih
  | terminal context source fuel argIdx toCheck notForall =>
      cases source <;>
        simp_all [isLargeEliminator.loop, ReaderT.pure, Pure.pure,
          Except.pure, Expr.isForall]

/-- Execute the singleton branch once while retaining the exact branch and
checker observations that produced its Boolean result. -/
def buildExecution (stats : InductiveStats) (context : Context)
    (source : Expr) (argIdx : Nat) (toCheck : Array Expr) :
    (fuel : Nat) → Except Exception
      (Sigma fun result => LargeEliminatorLoopTrace stats context source
        argIdx toCheck fuel result)
  | 0 => .error .deepRecursion
  | fuel + 1 =>
      match hforall : source.isForall with
      | false => .ok ⟨toCheck.all source.getAppArgs.contains,
          .terminal context source fuel argIdx toCheck hforall⟩
      | true =>
        match source with
        | .forallE name domain body binderInfo =>
          let nextContext := context.pushLocalDecl name binderInfo
            (consumeTypeAnnotations domain)
          let nextSource := body.instantiate1 context.freshExpr
          if isParameter : argIdx < stats.params.size then
            match buildExecution stats nextContext nextSource (argIdx + 1)
                toCheck fuel with
            | .error error => .error error
            | .ok ⟨result, tail⟩ => .ok ⟨result,
                .parameter context fuel argIdx toCheck name domain body
                  binderInfo isParameter tail⟩
          else
            match hensure : TypeChecker.M.run nextContext.env nextContext.safety
                nextContext.lctx nextContext.lparams nextContext.fuel
                (TypeChecker.ensureType domain) with
            | .error error => .error error
            | .ok sortResult =>
                if isProp : sortResult.sortLevel!.isAlwaysZero then
                  match buildExecution stats nextContext nextSource
                      (argIdx + 1) toCheck fuel with
                  | .error error => .error error
                  | .ok ⟨result, tail⟩ => .ok ⟨result,
                      .proofField context fuel argIdx toCheck name domain body
                        binderInfo sortResult (Nat.le_of_not_gt isParameter)
                        hensure isProp tail⟩
                else
                  match buildExecution stats nextContext nextSource
                      (argIdx + 1) (toCheck.push context.freshExpr) fuel with
                  | .error error => .error error
                  | .ok ⟨result, tail⟩ => .ok ⟨result,
                      .dataField context fuel argIdx toCheck name domain body
                        binderInfo sortResult (Nat.le_of_not_gt isParameter)
                        hensure (by
                          cases h : sortResult.sortLevel!.isAlwaysZero <;> simp_all)
                        tail⟩
        | _ => .error <| .other
            "large-eliminator source shape disagrees with isForall"

end LargeEliminatorLoopTrace

/-- The source identity and exact loop retained when the singleton branch of
`isLargeEliminator` is selected. -/
structure LargeEliminatorSingletonExecution
    (stats : InductiveStats) (indTypes : Array InductiveType)
    (context : Context) (result : Bool) where
  indType : InductiveType
  indTypes_eq : indTypes = #[indType]
  ctor : Constructor
  ctors_eq : indType.ctors = [ctor]
  trace : LargeEliminatorLoopTrace stats context ctor.type 0 #[]
    context.fuel.inductiveFuel result

/-- One exact successful execution of `isLargeEliminator`. The ordinary
equation is always retained; the singleton payload additionally exposes all
field-sort observations made by the executable. -/
structure LargeEliminatorExecution
    (stats : InductiveStats) (indTypes : Array InductiveType)
    (context : Context) where
  result : Bool
  singleton : Option
    (LargeEliminatorSingletonExecution stats indTypes context result)
  run_eq : isLargeEliminator stats indTypes context = .ok result

namespace LargeEliminatorExecution

private def refineSingleton (stats : InductiveStats)
    (indTypes : Array InductiveType) (context : Context) (result : Bool) :
    Option (LargeEliminatorSingletonExecution stats indTypes context result) :=
  if stats.isNotZero then
    none
  else
    match _htypes : indTypes with
    | #[indType] =>
        match hctors : indType.ctors with
        | [ctor] =>
            match LargeEliminatorLoopTrace.buildExecution stats context
                ctor.type 0 #[] context.fuel.inductiveFuel with
            | .error _ => none
            | .ok ⟨traceResult, trace⟩ =>
                if hsame : traceResult = result then
                  some {
                      indType
                      indTypes_eq := rfl
                      ctor
                      ctors_eq := hctors
                      trace := hsame ▸ trace }
                else
                  none
        | _ => none
    | _ => none

private def refineResult (stats : InductiveStats)
    (indTypes : Array InductiveType) (context : Context) (result : Bool)
    (run : isLargeEliminator stats indTypes context = .ok result) :
    LargeEliminatorExecution stats indTypes context where
  result := result
  singleton := refineSingleton stats indTypes context result
  run_eq := run

@[simp] private theorem refineResult_result
    {result : Bool}
    (run : isLargeEliminator stats indTypes context = .ok result) :
    (refineResult stats indTypes context result run).result = result := by
  rfl

/-- Execute the ordinary decision and retain a transparent refinement of its
singleton traversal when that optional refinement is available. -/
def buildExecution (stats : InductiveStats) (indTypes : Array InductiveType)
    (context : Context) :
    Except Exception (LargeEliminatorExecution stats indTypes context) :=
  match hrun : isLargeEliminator stats indTypes context with
  | .error error => .error error
  | .ok result => .ok (refineResult stats indTypes context result hrun)

/-- Optional singleton tracing never narrows a successful ordinary
large-elimination decision. -/
theorem buildExecution_ok_of_run
    {result : Bool}
    (run : isLargeEliminator stats indTypes context = .ok result) :
    ∃ execution,
      buildExecution stats indTypes context = .ok execution ∧
        execution.result = result := by
  unfold buildExecution
  split
  · rename_i ordinaryRun
    rw [run] at ordinaryRun
    contradiction
  · rename_i actualResult ordinaryRun
    refine ⟨_, rfl, ?_⟩
    rw [refineResult_result]
    exact Except.ok.inj (ordinaryRun.symm.trans run)

end LargeEliminatorExecution

/-- Exact `getElimLevel` execution paired with the retained large-elimination
decision that controls it. `level_eq` exposes both the zero and fresh-parameter
branches without unfolding the monadic checker again. -/
structure ElimLevelExecution
    (stats : InductiveStats) (indTypes : Array InductiveType)
    (context : Context) where
  large : LargeEliminatorExecution stats indTypes context
  level : Level
  level_eq : level = if large.result then
    .param (getFreshElimParam context.lparams) else .zero
  run_eq : getElimLevel stats indTypes context = .ok level

namespace ElimLevelExecution

/-- Recompose `getElimLevel` from the retained exact large-elimination run. -/
theorem run_of_large
    (large : LargeEliminatorExecution stats indTypes context) :
    getElimLevel stats indTypes context = .ok
      (if large.result then .param (getFreshElimParam context.lparams)
        else .zero) := by
  unfold getElimLevel
  simp only [ReaderT.bind, Bind.bind]
  rw [large.run_eq]
  cases large.result <;> rfl

def buildExecution (stats : InductiveStats) (indTypes : Array InductiveType)
    (context : Context) :
    Except Exception (ElimLevelExecution stats indTypes context) := do
  let large ← LargeEliminatorExecution.buildExecution stats indTypes context
  let level := if large.result then
    .param (getFreshElimParam context.lparams) else .zero
  pure {
    large
    level
    level_eq := rfl
    run_eq := run_of_large large }

/-- The retained elimination-level execution is complete for every
successful public `getElimLevel` result. -/
theorem buildExecution_ok_of_run
    {level : Level}
    (run : getElimLevel stats indTypes context = .ok level) :
    ∃ execution,
      buildExecution stats indTypes context = .ok execution ∧
        execution.level = level := by
  have largeRun : ∃ result,
      isLargeEliminator stats indTypes context = .ok result := by
    have observed := run
    unfold getElimLevel at observed
    simp only [ReaderT.bind, Bind.bind] at observed
    cases hlarge : isLargeEliminator stats indTypes context with
    | error error =>
        rw [hlarge] at observed
        contradiction
    | ok result => exact ⟨result, rfl⟩
  obtain ⟨result, largeRun⟩ := largeRun
  obtain ⟨large, largeBuild, _⟩ :=
    LargeEliminatorExecution.buildExecution_ok_of_run largeRun
  unfold buildExecution
  rw [largeBuild]
  refine ⟨_, rfl, ?_⟩
  exact Except.ok.inj ((run_of_large large).symm.trans run)

theorem level_eq_zero (execution : ElimLevelExecution stats indTypes context)
    (small : execution.large.result = false) :
    execution.level = .zero := by
  rw [execution.level_eq, small]
  rfl

theorem level_eq_param
    (execution : ElimLevelExecution stats indTypes context)
    (large : execution.large.result = true) :
    execution.level = .param (getFreshElimParam context.lparams) := by
  rw [execution.level_eq, large]
  rfl

/-- A small eliminator preserves the source universe-level order in recursor
applications. -/
theorem recLevels_eq_small
    (execution : ElimLevelExecution stats indTypes context)
    (small : execution.large.result = false) (levels : List Level) :
    getRecLevels execution.level levels = levels := by
  rw [execution.level_eq_zero small]
  rfl

/-- A large eliminator prepends its fresh elimination level to every source
universe used by recursive calls. -/
theorem recLevels_eq_large
    (execution : ElimLevelExecution stats indTypes context)
    (large : execution.large.result = true) (levels : List Level) :
    getRecLevels execution.level levels =
      .param (getFreshElimParam context.lparams) :: levels := by
  rw [execution.level_eq_param large]
  rfl

/-- A small eliminator preserves the stored source level-parameter order. -/
theorem recLevelParams_eq_small
    (execution : ElimLevelExecution stats indTypes context)
    (small : execution.large.result = false) (lparams : List Name) :
    getRecLevelParams execution.level lparams = lparams := by
  rw [execution.level_eq_zero small]
  rfl

/-- A large eliminator stores the fresh elimination parameter before every
source level parameter. -/
theorem recLevelParams_eq_large
    (execution : ElimLevelExecution stats indTypes context)
    (large : execution.large.result = true) (lparams : List Name) :
    getRecLevelParams execution.level lparams =
      getFreshElimParam context.lparams :: lparams := by
  rw [execution.level_eq_param large]
  rfl

end ElimLevelExecution

/-- Exact traversal of the constructor-shape fragment of `isKTarget`. The
trace stops at the first visible non-parameter binder, just as the executable
does; it never treats K eligibility as evidence for large elimination. -/
inductive KTargetCtorTrace (nparams : Nat) :
    (source : Expr) → (argIdx : Nat) → (result : Bool) → Type where
  | parameter
      (argIdx : Nat) (name : Name) (domain body : Expr)
      (binderInfo : BinderInfo)
      (isParameter : argIdx < nparams)
      (tail : KTargetCtorTrace nparams body (argIdx + 1) result) :
      KTargetCtorTrace nparams (.forallE name domain body binderInfo)
        argIdx result
  | field
      (argIdx : Nat) (name : Name) (domain body : Expr)
      (binderInfo : BinderInfo)
      (isField : argIdx ≥ nparams) :
      KTargetCtorTrace nparams (.forallE name domain body binderInfo)
        argIdx false
  | terminal
      (source : Expr) (argIdx : Nat)
      (notForall : source.isForall = false) :
      KTargetCtorTrace nparams source argIdx true

namespace KTargetCtorTrace

def parameterCount
    (trace : KTargetCtorTrace nparams source argIdx result) : Nat :=
  match trace with
  | .parameter (tail := tail) .. => tail.parameterCount + 1
  | .field .. => 0
  | .terminal .. => 0

/-- The K-target walk stops at the first visible constructor field, so this
count is either zero or one. -/
def fieldCount
    (trace : KTargetCtorTrace nparams source argIdx result) : Nat :=
  match trace with
  | .parameter (tail := tail) .. => tail.fieldCount
  | .field .. => 1
  | .terminal .. => 0

/-- Erasing the retained constructor trace yields the exact Boolean consumed
by `isKTarget`. -/
theorem run
    (trace : KTargetCtorTrace nparams source argIdx result) :
    isKTargetCtor nparams argIdx source = result := by
  induction trace with
  | parameter argIdx name domain body binderInfo isParameter tail ih =>
      simp [isKTargetCtor, isParameter, ih]
  | field argIdx name domain body binderInfo isField =>
      have notParameter : ¬ argIdx < nparams := Nat.not_lt.mpr isField
      simp [isKTargetCtor, notParameter]
  | terminal source argIdx notForall =>
      cases source <;> simp_all [isKTargetCtor, Expr.isForall]

/-- Compute the K-target constructor branch while retaining the exact point
where the parameter prefix ends. -/
def buildExecution (nparams : Nat) :
    (source : Expr) → (argIdx : Nat) →
      Sigma fun result => KTargetCtorTrace nparams source argIdx result
  | .bvar i, argIdx => ⟨true, .terminal (.bvar i) argIdx rfl⟩
  | .fvar id, argIdx => ⟨true, .terminal (.fvar id) argIdx rfl⟩
  | .mvar id, argIdx => ⟨true, .terminal (.mvar id) argIdx rfl⟩
  | .sort level, argIdx => ⟨true, .terminal (.sort level) argIdx rfl⟩
  | .const name levels, argIdx =>
      ⟨true, .terminal (.const name levels) argIdx rfl⟩
  | .app fn arg, argIdx => ⟨true, .terminal (.app fn arg) argIdx rfl⟩
  | .lam name domain body binderInfo, argIdx =>
      ⟨true, .terminal (.lam name domain body binderInfo) argIdx rfl⟩
  | .forallE name domain body binderInfo, argIdx =>
      if isParameter : argIdx < nparams then
        let ⟨result, tail⟩ := buildExecution nparams body (argIdx + 1)
        ⟨result, .parameter argIdx name domain body binderInfo
          isParameter tail⟩
      else
        ⟨false, .field argIdx name domain body binderInfo
          (Nat.le_of_not_gt isParameter)⟩
  | .letE name type value body nondep, argIdx =>
      ⟨true, .terminal (.letE name type value body nondep) argIdx rfl⟩
  | .lit literal, argIdx => ⟨true, .terminal (.lit literal) argIdx rfl⟩
  | .mdata data expr, argIdx =>
      ⟨true, .terminal (.mdata data expr) argIdx rfl⟩
  | .proj typeName idx struct, argIdx =>
      ⟨true, .terminal (.proj typeName idx struct) argIdx rfl⟩

end KTargetCtorTrace

/-- The singleton-Prop branch data of one exact `isKTarget` execution. -/
structure KTargetSingletonExecution
    (stats : InductiveStats) (indTypes : Array InductiveType)
    (result : Bool) where
  indType : InductiveType
  indTypes_eq : indTypes = #[indType]
  resultLevelZero : stats.resultLevel.isAlwaysZero = true
  ctor : Constructor
  ctors_eq : indType.ctors = [ctor]
  trace : KTargetCtorTrace stats.params.size ctor.type 0 result

/-- One exact successful execution of `isKTarget`. The ordinary monadic
equation is always retained; a singleton candidate additionally exposes the
constructor-prefix trace that decided its flag. -/
structure KTargetExecution
    (stats : InductiveStats) (indTypes : Array InductiveType)
    (context : Context) where
  result : Bool
  singleton : Option (KTargetSingletonExecution stats indTypes result)
  run_eq : isKTarget stats indTypes context = .ok result

namespace KTargetExecution

private def refineSingleton (stats : InductiveStats)
    (indTypes : Array InductiveType) (result : Bool) :
    Option (KTargetSingletonExecution stats indTypes result) :=
  match _htypes : indTypes with
  | #[indType] =>
      if hzero : stats.resultLevel.isAlwaysZero then
        match hctors : indType.ctors with
        | [ctor] =>
            let ⟨traceResult, trace⟩ :=
              KTargetCtorTrace.buildExecution stats.params.size ctor.type 0
            if hsame : traceResult = result then
              some {
                  indType
                  indTypes_eq := rfl
                  resultLevelZero := hzero
                  ctor
                  ctors_eq := hctors
                  trace := hsame ▸ trace }
            else
              none
        | _ => none
      else
        none
  | _ => none

private def refineResult (stats : InductiveStats)
    (indTypes : Array InductiveType) (context : Context) (result : Bool)
    (run : isKTarget stats indTypes context = .ok result) :
    KTargetExecution stats indTypes context where
  result := result
  singleton := refineSingleton stats indTypes result
  run_eq := run

@[simp] private theorem refineResult_result
    {result : Bool}
    (run : isKTarget stats indTypes context = .ok result) :
    (refineResult stats indTypes context result run).result = result := by
  rfl

def buildExecution (stats : InductiveStats)
    (indTypes : Array InductiveType) (context : Context) :
    Except Exception (KTargetExecution stats indTypes context) :=
  match hrun : isKTarget stats indTypes context with
  | .error error => .error error
  | .ok result => .ok (refineResult stats indTypes context result hrun)

/-- Optional singleton tracing likewise never narrows a successful ordinary
K-target decision. -/
theorem buildExecution_ok_of_run
    {result : Bool}
    (run : isKTarget stats indTypes context = .ok result) :
    ∃ execution,
      buildExecution stats indTypes context = .ok execution ∧
        execution.result = result := by
  unfold buildExecution
  split
  · rename_i ordinaryRun
    rw [run] at ordinaryRun
    contradiction
  · rename_i actualResult ordinaryRun
    refine ⟨_, rfl, ?_⟩
    rw [refineResult_result]
    exact Except.ok.inj (ordinaryRun.symm.trans run)

end KTargetExecution

/-- The normalization/validation execution extended through constructor
declaration and the exact elimination-level and K-target decisions used by
`run`. This is an operational refinement only: erasing the added fields leaves the existing
normalization candidate and checker equations unchanged. -/
structure NormalizationEliminationExecution
    (nparams : Nat) (types : List InductiveType)
    (numNested : Nat) (isUnsafe : Bool) (candidateContext : Context) where
  normalization : NormalizationCandidateExecution nparams types numNested
    isUnsafe candidateContext
  constructorEnv : Environment
  declareConstructorsRun :
    declareConstructors normalization.stats types.toArray isUnsafe
      { normalization.validationContext with
        env := normalization.familyEnv } = .ok constructorEnv
  elimination : ElimLevelExecution normalization.stats types.toArray
    { normalization.validationContext with env := constructorEnv }
  kTarget : KTargetExecution normalization.stats types.toArray
    { normalization.validationContext with env := constructorEnv }

namespace NormalizationEliminationExecution

def candidate
    (execution : NormalizationEliminationExecution nparams types numNested
      isUnsafe candidateContext) : NormalizationCandidate types :=
  execution.normalization.candidate

/-- Reader context used by the constructor metadata declaration phase. -/
def constructorContext
    (execution : NormalizationEliminationExecution nparams types numNested
      isUnsafe candidateContext) : Context :=
  { execution.normalization.validationContext with
    env := execution.normalization.familyEnv }

/-- Exact family-major constructor metadata installed by this execution. -/
def declaredConstructorInfos
    (execution : NormalizationEliminationExecution nparams types numNested
      isUnsafe candidateContext) : List ConstructorVal :=
  AddInductive.declaredConstructorInfos execution.normalization.stats
    types.toArray isUnsafe execution.constructorContext

/-- Recover every constructor name check and insertion from the retained
ordinary declaration equation. -/
theorem declareConstructorTrace
    (execution : NormalizationEliminationExecution nparams types numNested
      isUnsafe candidateContext) :
    DeclareConstructorInfoListRun
      execution.constructorContext.allowPrimitive
      execution.normalization.familyEnv execution.declaredConstructorInfos
      execution.constructorEnv := by
  apply DeclareConstructorInfoListRun.of_run
  simpa only [declareConstructors, constructorContext,
    declaredConstructorInfos] using execution.declareConstructorsRun

/-- Execute the existing detailed candidate producer, declare the already
validated constructors, and retain both recursor decisions at precisely the
post-constructor context used by `run`. -/
def buildExecution
    (nparams : Nat) (types : List InductiveType)
    (numNested : Nat) (isUnsafe : Bool) (candidateContext : Context) :
    Except Exception (NormalizationEliminationExecution nparams types
      numNested isUnsafe candidateContext) := do
  let normalization ← buildNormalizationCandidateExecution nparams types
    numNested isUnsafe candidateContext
  let constructorContext : Context :=
    { normalization.validationContext with env := normalization.familyEnv }
  match hdeclare : declareConstructors normalization.stats types.toArray
      isUnsafe constructorContext with
  | .error error => .error error
  | .ok constructorEnv =>
      let eliminationContext : Context :=
        { normalization.validationContext with env := constructorEnv }
      match ElimLevelExecution.buildExecution normalization.stats
          types.toArray eliminationContext with
      | .error error => .error error
      | .ok elimination =>
          match KTargetExecution.buildExecution normalization.stats
              types.toArray eliminationContext with
          | .error error => .error error
          | .ok kTarget => .ok {
              normalization
              constructorEnv
              declareConstructorsRun := by
                simpa [constructorContext] using hdeclare
              elimination := by simpa [eliminationContext] using elimination
              kTarget := by simpa [eliminationContext] using kTarget }

/-- Compose successful public downstream equations with one retained
normalization execution.  Optional elimination/K refinements are complete,
so the resulting detailed post-constructor execution is exact. -/
theorem buildExecution_ok_of_runs
    {normalization : NormalizationCandidateExecution nparams types
      numNested isUnsafe candidateContext}
    (normalizationRun : buildNormalizationCandidateExecution nparams types
      numNested isUnsafe candidateContext = .ok normalization)
    {constructorEnv : Environment}
    (declareRun : declareConstructors normalization.stats types.toArray
      isUnsafe { normalization.validationContext with
        env := normalization.familyEnv } = .ok constructorEnv)
    {elimLevel : Level}
    (elimRun : getElimLevel normalization.stats types.toArray
      { normalization.validationContext with env := constructorEnv } =
        .ok elimLevel)
    {kTarget : Bool}
    (kRun : isKTarget normalization.stats types.toArray
      { normalization.validationContext with env := constructorEnv } =
        .ok kTarget) :
    ∃ execution,
      buildExecution nparams types numNested isUnsafe candidateContext =
          .ok execution ∧
        execution.normalization = normalization ∧
        execution.constructorEnv = constructorEnv ∧
        execution.elimination.level = elimLevel ∧
        execution.kTarget.result = kTarget := by
  let postContext : Context :=
    { normalization.validationContext with env := constructorEnv }
  obtain ⟨elimination, eliminationBuild, eliminationLevelEq⟩ :=
    ElimLevelExecution.buildExecution_ok_of_run (context := postContext)
      (by simpa only [postContext] using elimRun)
  obtain ⟨kExecution, kBuild, kResultEq⟩ :=
    KTargetExecution.buildExecution_ok_of_run (context := postContext)
      (by simpa only [postContext] using kRun)
  let execution : NormalizationEliminationExecution nparams types numNested
      isUnsafe candidateContext := {
    normalization
    constructorEnv
    declareConstructorsRun := declareRun
    elimination
    kTarget := kExecution }
  refine ⟨execution, ?_, rfl, rfl, eliminationLevelEq, kResultEq⟩
  unfold buildExecution
  rw [normalizationRun]
  simp only [Bind.bind, Except.bind]
  split
  · rename_i actualDeclare
    rw [declareRun] at actualDeclare
    contradiction
  · rename_i actualConstructorEnv actualDeclare
    have constructorEnvEq : actualConstructorEnv = constructorEnv :=
      Except.ok.inj (actualDeclare.symm.trans declareRun)
    subst actualConstructorEnv
    have eliminationBuild' : ElimLevelExecution.buildExecution
        normalization.stats types.toArray
        { normalization.validationContext with env := constructorEnv } =
          .ok elimination := by
      simpa only [postContext] using eliminationBuild
    rw [eliminationBuild']
    have kBuild' : KTargetExecution.buildExecution normalization.stats
        types.toArray
        { normalization.validationContext with env := constructorEnv } =
          .ok kExecution := by
      simpa only [postContext] using kBuild
    rw [kBuild']
    rfl

/-- Erase a retained post-constructor/elimination execution back to the exact
normalization execution selected at the start of the same call. -/
theorem normalization_run
    (execution : NormalizationEliminationExecution nparams types numNested
      isUnsafe candidateContext)
    (run : buildExecution nparams types numNested isUnsafe candidateContext =
      .ok execution) :
    buildNormalizationCandidateExecution nparams types numNested isUnsafe
        candidateContext = .ok execution.normalization := by
  unfold buildExecution at run
  cases hnormalization :
      buildNormalizationCandidateExecution nparams types numNested isUnsafe
        candidateContext with
  | error error =>
      rw [hnormalization] at run
      contradiction
  | ok normalization =>
      rw [hnormalization] at run
      simp only [Bind.bind, Except.bind] at run
      repeat' split at run
      all_goals
        first | contradiction | (cases run; rfl)

/-- The same erasure also recovers the public candidate producer equation. -/
theorem produces
    (execution : NormalizationEliminationExecution nparams types numNested
      isUnsafe candidateContext)
    (run : buildExecution nparams types numNested isUnsafe candidateContext =
      .ok execution) :
    buildNormalizationCandidate nparams types numNested isUnsafe
        candidateContext = .ok execution.candidate :=
  execution.normalization.producesFromBuildExecution
    (execution.normalization_run run)

/-- The level list supplied to generated recursive calls. -/
def recLevels
    (execution : NormalizationEliminationExecution nparams types numNested
      isUnsafe candidateContext) : List Level :=
  getRecLevels execution.elimination.level execution.normalization.stats.levels

/-- The level-parameter list stored in generated recursor metadata. -/
def recLevelParams
    (execution : NormalizationEliminationExecution nparams types numNested
      isUnsafe candidateContext) : List Name :=
  getRecLevelParams execution.elimination.level
    execution.normalization.validationContext.lparams

end NormalizationEliminationExecution

/-- The sole remaining observer-completeness boundary for a successful
ordinary inductive add: its family-validation and normalization prefix can be
retained by the detailed candidate producer.  Downstream constructor,
elimination, K-target, and recursor phases are composed from their real public
equations. -/
def NormalizationCandidateExecution.CompleteForRun
    (nparams : Nat) (types : List InductiveType)
    (numNested : Nat) (isUnsafe : Bool) (candidateContext : Context) : Prop :=
  ∀ finalEnv,
    AddInductive.run nparams types numNested candidateContext = .ok finalEnv →
      ∃ normalization : NormalizationCandidateExecution nparams types numNested
          isUnsafe candidateContext,
        buildNormalizationCandidateExecution nparams types numNested isUnsafe
          candidateContext = .ok normalization

/-- The pointwise recursive candidate observers are the whole residual of
normalization completeness.  Every validation, raw-family declaration, and
constructor-validation equation is recovered from the successful public run;
the observer contract contributes only calls absent from that public path. -/
theorem NormalizationCandidateExecution.completeForRun_of_candidateObservers
    (isUnsafeEq : isUnsafe = (candidateContext.safety != .safe))
    (observers : CandidateObserversComplete nparams types numNested isUnsafe
      candidateContext) :
    CompleteForRun nparams types numNested isUnsafe candidateContext := by
  subst isUnsafe
  intro finalEnv publicRun
  have publicRun' := publicRun
  unfold AddInductive.run at publicRun'
  simp only [readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, Pure.pure, Except.pure, liftExcept_apply,
    Except.bind] at publicRun'
  cases duplicatedRun : Environment.checkDuplicatedUnivParams
      candidateContext.lparams with
  | error error =>
      rw [duplicatedRun] at publicRun'
      contradiction
  | ok checked =>
      have checkedEq : checked = () := Subsingleton.elim _ _
      subst checked
      rw [duplicatedRun] at publicRun'
      rw [checkInductiveTypes_factor] at publicRun'
      cases validationRun :
          observeFamilyValidationBlock nparams types candidateContext with
      | error error =>
          rw [validationRun] at publicRun'
          contradiction
      | ok validation =>
          rw [validationRun] at publicRun'
          simp only [ReaderT.bind, Bind.bind, Except.bind] at publicRun'
          cases declareRun : declareInductiveTypes validation.stats nparams
              types.toArray numNested (candidateContext.safety != .safe)
              validation.validationContext with
          | error error =>
              rw [declareRun] at publicRun'
              contradiction
          | ok familyEnv =>
              rw [declareRun] at publicRun'
              unfold withEnv at publicRun'
              change (ReaderT.bind
                  (checkConstructors types.toArray validation.stats
                    (candidateContext.safety != .safe))
                  (fun _ => ReaderT.bind
                    (declareConstructors validation.stats types.toArray
                      (candidateContext.safety != .safe))
                    (fun constructorEnv => withReader
                      (fun c : Context => { c with env := constructorEnv })
                      (ReaderT.bind
                        (getElimLevel validation.stats types.toArray)
                        (fun elimLevel => ReaderT.bind
                          (isKTarget validation.stats types.toArray)
                          (fun k => ReaderT.bind
                            (declareRecursors validation.stats types.toArray
                              elimLevel k)
                            (fun recursors => pure recursors.env)))))))
                  ({ validation.validationContext with
                    env := familyEnv } : Context) =
                .ok finalEnv at publicRun'
              simp only [ReaderT.bind, Bind.bind] at publicRun'
              cases constructorRun : checkConstructors types.toArray
                  validation.stats (candidateContext.safety != .safe)
                  { validation.validationContext with env := familyEnv } with
              | error error =>
                  rw [constructorRun] at publicRun'
                  contradiction
              | ok checkedConstructors =>
                  have checkedConstructorsEq : checkedConstructors = () :=
                    Subsingleton.elim _ _
                  subst checkedConstructors
                  exact build_ok_of_candidateObservers observers validationRun
                    declareRun constructorRun

/-- The retained normalization/elimination prefix extended through the exact
recursor synthesis and declaration phase used by `run`.  `recursors.infos`
owns the actual generated kernel records in family order, including their
rules, while `recursors.trace` owns every name check and insertion. -/
structure NormalizationRecursorExecution
    (nparams : Nat) (types : List InductiveType)
    (numNested : Nat) (isUnsafe : Bool) (candidateContext : Context) where
  isUnsafe_eq : isUnsafe = (candidateContext.safety != .safe)
  duplicatedUnivParamsRun :
    Environment.checkDuplicatedUnivParams candidateContext.lparams = .ok ()
  eliminationExecution : NormalizationEliminationExecution nparams types numNested
    isUnsafe candidateContext
  recursors : RecursorDeclarationResult
  recursorsRun :
    declareRecursors eliminationExecution.normalization.stats types.toArray
      eliminationExecution.elimination.level eliminationExecution.kTarget.result
      { eliminationExecution.normalization.validationContext with
        env := eliminationExecution.constructorEnv } = .ok recursors

namespace NormalizationRecursorExecution

def candidate
    (execution : NormalizationRecursorExecution nparams types numNested
      isUnsafe candidateContext) : NormalizationCandidate types :=
  execution.eliminationExecution.candidate

/-- Reader context used by recursor synthesis and declaration. -/
def recursorContext
    (execution : NormalizationRecursorExecution nparams types numNested
      isUnsafe candidateContext) : Context :=
  { execution.eliminationExecution.normalization.validationContext with
    env := execution.eliminationExecution.constructorEnv }

theorem recursor_initialEnv_eq
    (execution : NormalizationRecursorExecution nparams types numNested
      isUnsafe candidateContext) :
    execution.recursors.initialEnv =
      execution.eliminationExecution.constructorEnv := by
  exact (declareRecursors_input_eq execution.recursorsRun).1

theorem recursor_allowPrimitive_eq
    (execution : NormalizationRecursorExecution nparams types numNested
      isUnsafe candidateContext) :
    execution.recursors.allowPrimitive =
      execution.eliminationExecution.normalization.validationContext.allowPrimitive := by
  exact (declareRecursors_input_eq execution.recursorsRun).2

/-- Execute the detailed normalization/elimination prefix and then the exact
ordinary recursor producer, retaining its complete data-bearing result. -/
def buildExecution
    (nparams : Nat) (types : List InductiveType)
    (numNested : Nat) (isUnsafe : Bool) (candidateContext : Context) :
    Except Exception (NormalizationRecursorExecution nparams types
      numNested isUnsafe candidateContext) :=
  if hisUnsafe : isUnsafe = (candidateContext.safety != .safe) then
    match hlevels : Environment.checkDuplicatedUnivParams
        candidateContext.lparams with
    | .error error => .error error
    | .ok () => do
      let eliminationExecution ←
        NormalizationEliminationExecution.buildExecution nparams types
          numNested isUnsafe candidateContext
      let recursorContext : Context :=
        { eliminationExecution.normalization.validationContext with
          env := eliminationExecution.constructorEnv }
      match hrecursors : declareRecursors
          eliminationExecution.normalization.stats types.toArray
          eliminationExecution.elimination.level
          eliminationExecution.kTarget.result recursorContext with
      | .error error => .error error
      | .ok recursors => .ok {
          isUnsafe_eq := hisUnsafe
          duplicatedUnivParamsRun := hlevels
          eliminationExecution
          recursors
          recursorsRun := by simpa [recursorContext] using hrecursors }
  else
    .error (.other "recursor execution safety disagrees with reader context")

/-- Compose the exact successful equations for every ordinary inductive phase
into one retained recursor execution. -/
theorem buildExecution_ok_of_runs
    (isUnsafeEq : isUnsafe = (candidateContext.safety != .safe))
    (duplicatedRun : Environment.checkDuplicatedUnivParams
      candidateContext.lparams = .ok ())
    {normalization : NormalizationCandidateExecution nparams types numNested
      isUnsafe candidateContext}
    (normalizationRun : buildNormalizationCandidateExecution nparams types
      numNested isUnsafe candidateContext = .ok normalization)
    {constructorEnv : Environment}
    (declareRun : declareConstructors normalization.stats types.toArray
      isUnsafe { normalization.validationContext with
        env := normalization.familyEnv } = .ok constructorEnv)
    {elimLevel : Level}
    (elimRun : getElimLevel normalization.stats types.toArray
      { normalization.validationContext with env := constructorEnv } =
        .ok elimLevel)
    {kTarget : Bool}
    (kRun : isKTarget normalization.stats types.toArray
      { normalization.validationContext with env := constructorEnv } =
        .ok kTarget)
    {recursors : RecursorDeclarationResult}
    (recursorsRun : declareRecursors normalization.stats types.toArray
      elimLevel kTarget
      { normalization.validationContext with env := constructorEnv } =
        .ok recursors) :
    ∃ execution : NormalizationRecursorExecution nparams types numNested
        isUnsafe candidateContext,
      buildExecution nparams types numNested isUnsafe candidateContext =
          .ok execution ∧
        execution.recursors = recursors := by
  obtain ⟨eliminationExecution, eliminationRun, normalizationEq,
      constructorEnvEq, elimLevelEq, kTargetEq⟩ :=
    NormalizationEliminationExecution.buildExecution_ok_of_runs
      normalizationRun declareRun elimRun kRun
  have recursorsRun' : declareRecursors
      eliminationExecution.normalization.stats types.toArray
      eliminationExecution.elimination.level
      eliminationExecution.kTarget.result
      { eliminationExecution.normalization.validationContext with
        env := eliminationExecution.constructorEnv } = .ok recursors := by
    simpa only [normalizationEq, constructorEnvEq, elimLevelEq, kTargetEq] using
      recursorsRun
  let execution : NormalizationRecursorExecution nparams types numNested
      isUnsafe candidateContext := {
    isUnsafe_eq := isUnsafeEq
    duplicatedUnivParamsRun := duplicatedRun
    eliminationExecution
    recursors
    recursorsRun := recursorsRun' }
  refine ⟨execution, ?_, rfl⟩
  unfold buildExecution
  rw [dif_pos isUnsafeEq]
  split
  · rename_i actualDuplicated
    rw [duplicatedRun] at actualDuplicated
    contradiction
  · rename_i actualDuplicated
    simp only [Bind.bind, Except.bind]
    rw [eliminationRun]
    simp only
    split
    · rename_i actualRecursors
      rw [recursorsRun'] at actualRecursors
      contradiction
    · rename_i actualResult actualRecursors
      have resultEq : actualResult = recursors :=
        Except.ok.inj (actualRecursors.symm.trans recursorsRun')
      subst actualResult
      rfl

/-- Operational completeness boundary for the flattened ordinary pipeline:
every successful `AddInductive.run` result is represented by a successful
detailed execution with the same final kernel environment. -/
def Complete (nparams : Nat) (types : List InductiveType)
    (numNested : Nat) (isUnsafe : Bool) (candidateContext : Context) : Prop :=
  ∀ finalEnv,
    AddInductive.run nparams types numNested candidateContext = .ok finalEnv →
      ∃ execution : NormalizationRecursorExecution nparams types numNested
          isUnsafe candidateContext,
        buildExecution nparams types numNested isUnsafe candidateContext =
            .ok execution ∧
          execution.recursors.env = finalEnv

/-- Once the family-validation/normalization observer retains a successful
prefix, every remaining phase is recovered from the same successful public
`run`; no additional downstream completeness hypothesis is needed. -/
theorem complete_of_normalization
    (isUnsafeEq : isUnsafe = (candidateContext.safety != .safe))
    (normalizationComplete :
      NormalizationCandidateExecution.CompleteForRun nparams types numNested
        isUnsafe candidateContext) :
    Complete nparams types numNested isUnsafe candidateContext := by
  subst isUnsafe
  intro finalEnv publicRun
  obtain ⟨normalization, normalizationRun⟩ :=
    normalizationComplete finalEnv publicRun
  have publicRun' := publicRun
  unfold AddInductive.run at publicRun'
  simp only [readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, Pure.pure, Except.pure, liftExcept_apply,
    Except.bind] at publicRun'
  cases duplicatedRun : Environment.checkDuplicatedUnivParams
      candidateContext.lparams with
  | error error =>
      rw [duplicatedRun] at publicRun'
      contradiction
  | ok checked =>
      have checkedEq : checked = () := Subsingleton.elim _ _
      subst checked
      rw [duplicatedRun] at publicRun'
      rw [normalization.familyValidation normalizationRun] at publicRun'
      simp only [ReaderT.bind, Bind.bind] at publicRun'
      rw [normalization.declareRun] at publicRun'
      simp only [Except.bind] at publicRun'
      unfold withEnv at publicRun'
      change (ReaderT.bind
          (checkConstructors types.toArray normalization.stats
            (candidateContext.safety != .safe))
          (fun _ => ReaderT.bind
            (declareConstructors normalization.stats types.toArray
              (candidateContext.safety != .safe))
            (fun constructorEnv => withReader
              (fun c : Context => { c with env := constructorEnv })
              (ReaderT.bind
                (getElimLevel normalization.stats types.toArray)
                (fun elimLevel => ReaderT.bind
                  (isKTarget normalization.stats types.toArray)
                  (fun k => ReaderT.bind
                    (declareRecursors normalization.stats types.toArray
                      elimLevel k)
                    (fun recursors => pure recursors.env)))))))
          ({ normalization.validationContext with
            env := normalization.familyEnv } : Context) =
        .ok finalEnv at publicRun'
      simp only [ReaderT.bind, Bind.bind] at publicRun'
      rw [normalization.constructorRun] at publicRun'
      simp only [Except.bind] at publicRun'
      cases declareRun : declareConstructors normalization.stats types.toArray
          (candidateContext.safety != .safe)
          { normalization.validationContext with
            env := normalization.familyEnv } with
      | error error =>
          rw [declareRun] at publicRun'
          contradiction
      | ok constructorEnv =>
          rw [declareRun] at publicRun'
          change (ReaderT.bind
              (getElimLevel normalization.stats types.toArray)
              (fun elimLevel => ReaderT.bind
                (isKTarget normalization.stats types.toArray)
                (fun k => ReaderT.bind
                  (declareRecursors normalization.stats types.toArray
                    elimLevel k)
                  (fun recursors => pure recursors.env))))
              ({ normalization.validationContext with
                env := constructorEnv } : Context) =
            .ok finalEnv at publicRun'
          simp only [ReaderT.bind, Bind.bind] at publicRun'
          cases elimRun : getElimLevel normalization.stats types.toArray
              { normalization.validationContext with
                env := constructorEnv } with
          | error error =>
              rw [elimRun] at publicRun'
              contradiction
          | ok elimLevel =>
              rw [elimRun] at publicRun'
              simp only [Except.bind] at publicRun'
              cases kRun : isKTarget normalization.stats types.toArray
                  { normalization.validationContext with
                    env := constructorEnv } with
              | error error =>
                  rw [kRun] at publicRun'
                  contradiction
              | ok kTarget =>
                  rw [kRun] at publicRun'
                  simp only at publicRun'
                  cases recursorsRun : declareRecursors normalization.stats
                      types.toArray elimLevel kTarget
                      { normalization.validationContext with
                        env := constructorEnv } with
                  | error error =>
                      rw [recursorsRun] at publicRun'
                      contradiction
                  | ok recursors =>
                      rw [recursorsRun] at publicRun'
                      simp only [Pure.pure] at publicRun'
                      have recursorEnvEq : recursors.env = finalEnv :=
                        Except.ok.inj publicRun'
                      obtain ⟨execution, executionRun, recursorsEq⟩ :=
                        buildExecution_ok_of_runs rfl duplicatedRun
                          normalizationRun declareRun elimRun kRun recursorsRun
                      refine ⟨execution, executionRun, ?_⟩
                      rw [recursorsEq]
                      exact recursorEnvEq

/-- Erase the recursor phase back to the exact retained
normalization/elimination prefix. -/
theorem prefix_run
    (execution : NormalizationRecursorExecution nparams types numNested
      isUnsafe candidateContext)
    (run : buildExecution nparams types numNested isUnsafe candidateContext =
      .ok execution) :
    NormalizationEliminationExecution.buildExecution nparams types numNested
        isUnsafe candidateContext = .ok execution.eliminationExecution := by
  unfold buildExecution at run
  split at run
  next =>
    split at run
    next => contradiction
    next =>
      simp only [Bind.bind, Except.bind] at run
      cases hprefix : NormalizationEliminationExecution.buildExecution nparams
          types numNested isUnsafe candidateContext with
      | error error =>
          rw [hprefix] at run
          contradiction
      | ok eliminationExecution =>
          rw [hprefix] at run
          repeat' split at run
          all_goals try contradiction
          all_goals simp_all
          exact congrArg
            (fun result : NormalizationRecursorExecution nparams types
                numNested isUnsafe candidateContext =>
              result.eliminationExecution) run
  next => contradiction

/-- Erase the stronger execution directly back to the detailed normalization
producer selected at the start of the same call. -/
theorem normalization_run
    (execution : NormalizationRecursorExecution nparams types numNested
      isUnsafe candidateContext)
    (run : buildExecution nparams types numNested isUnsafe candidateContext =
      .ok execution) :
    buildNormalizationCandidateExecution nparams types numNested isUnsafe
        candidateContext = .ok execution.eliminationExecution.normalization :=
  execution.eliminationExecution.normalization_run (execution.prefix_run run)

/-- Recompose the retained phases into the real ordinary inductive-add call.
This prevents the strengthened instrumentation from certifying a parallel
producer: its final environment is exactly the successful result of `run`. -/
theorem addInductiveRun
    (execution : NormalizationRecursorExecution nparams types numNested
      isUnsafe candidateContext)
    (produced : buildExecution nparams types numNested isUnsafe
      candidateContext = .ok execution) :
    AddInductive.run nparams types numNested candidateContext =
      .ok execution.recursors.env := by
  have hsafety := execution.isUnsafe_eq
  subst isUnsafe
  unfold AddInductive.run
  simp only [readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, Pure.pure, Except.pure, liftExcept_apply]
  simp only [Except.bind]
  rw [execution.duplicatedUnivParamsRun]
  rw [execution.eliminationExecution.normalization.familyValidation
    (execution.normalization_run produced)]
  simp only [ReaderT.bind, Bind.bind]
  rw [execution.eliminationExecution.normalization.declareRun]
  simp only [Except.bind]
  unfold withEnv
  change (ReaderT.bind
      (checkConstructors types.toArray
        execution.eliminationExecution.normalization.stats
          (candidateContext.safety != .safe))
      (fun _ => ReaderT.bind
        (declareConstructors execution.eliminationExecution.normalization.stats
          types.toArray (candidateContext.safety != .safe))
        (fun constructorEnv => withReader
          (fun c : Context => { c with env := constructorEnv })
          (ReaderT.bind
            (getElimLevel execution.eliminationExecution.normalization.stats
              types.toArray)
            (fun elimLevel => ReaderT.bind
              (isKTarget execution.eliminationExecution.normalization.stats
                types.toArray)
              (fun k => ReaderT.bind
                (declareRecursors
                  execution.eliminationExecution.normalization.stats
                  types.toArray elimLevel k)
                (fun recursors => pure recursors.env)))))))
      ({ execution.eliminationExecution.normalization.validationContext with
        env := execution.eliminationExecution.normalization.familyEnv } :
          Context) = _
  simp only [ReaderT.bind, Bind.bind]
  rw [execution.eliminationExecution.normalization.constructorRun]
  simp only [Except.bind]
  rw [execution.eliminationExecution.declareConstructorsRun]
  change (ReaderT.bind
      (getElimLevel execution.eliminationExecution.normalization.stats
        types.toArray)
      (fun elimLevel => ReaderT.bind
        (isKTarget execution.eliminationExecution.normalization.stats
          types.toArray)
        (fun k => ReaderT.bind
          (declareRecursors execution.eliminationExecution.normalization.stats
            types.toArray elimLevel k)
          (fun recursors => pure recursors.env))))
      ({ execution.eliminationExecution.normalization.validationContext with
        env := execution.eliminationExecution.constructorEnv } : Context) = _
  simp only [ReaderT.bind, Bind.bind]
  rw [execution.eliminationExecution.elimination.run_eq]
  simp only [Except.bind]
  rw [execution.eliminationExecution.kTarget.run_eq]
  change (declareRecursors
      execution.eliminationExecution.normalization.stats types.toArray
      execution.eliminationExecution.elimination.level
      execution.eliminationExecution.kTarget.result
      ({ execution.eliminationExecution.normalization.validationContext with
        env := execution.eliminationExecution.constructorEnv } : Context)).map
      (·.env) = .ok execution.recursors.env
  rw [execution.recursorsRun]
  rfl

/-- The complete ordinary inductive transaction preserves quotient
initialization from its input reader environment. -/
theorem quotInit_eq
    (execution : NormalizationRecursorExecution nparams types numNested
      isUnsafe candidateContext)
    (produced : buildExecution nparams types numNested isUnsafe
      candidateContext = .ok execution) :
    execution.recursors.env.quotInit = candidateContext.env.quotInit := by
  calc
    execution.recursors.env.quotInit =
        execution.recursors.initialEnv.quotInit :=
      execution.recursors.trace.quotInit
    _ = execution.eliminationExecution.constructorEnv.quotInit :=
      congrArg Environment.quotInit execution.recursor_initialEnv_eq
    _ = execution.eliminationExecution.normalization.familyEnv.quotInit :=
      execution.eliminationExecution.declareConstructorTrace.quotInit
    _ = execution.eliminationExecution.normalization.validationContext.env.quotInit :=
      execution.eliminationExecution.normalization.familyEnv_quotInit
    _ = candidateContext.env.quotInit := congrArg Environment.quotInit
      (execution.eliminationExecution.normalization.validationContext_env_all
        (execution.normalization_run produced))

end NormalizationRecursorExecution

/-- Final branch of a retained outer inductive-add execution.  The ordinary
case returns the flattened checker environment directly; the nested case owns
the complete restored inventory, declaration trace, and auxiliary-value
typecheck. -/
inductive EnvironmentInductiveCompletion
    (res : ElimNestedInductive.Result) (flatEnv initialEnv : Environment)
    (types : List InductiveType) (allowPrimitive : Bool)
    (safety : DefinitionSafety) (lparams : List Name) (fuel : FuelConfig) :
    Environment → Type where
  | ordinary (numNested_eq : res.aux2nested.size = 0) :
      EnvironmentInductiveCompletion res flatEnv initialEnv types
        allowPrimitive safety lparams fuel flatEnv
  | nested
      (numNested_ne : res.aux2nested.size ≠ 0)
      (restoration : NestedRestorationResult res flatEnv initialEnv types
        allowPrimitive safety lparams fuel)
      (restorationRun : restoreNestedEnvironment res flatEnv initialEnv types
        allowPrimitive safety lparams fuel = .ok restoration) :
      EnvironmentInductiveCompletion res flatEnv initialEnv types
        allowPrimitive safety lparams fuel restoration.env

/-- Exact execution of the complete `Environment.addInductive` pipeline,
from source prechecks through nested elimination and ordinary flattened-block
checking to either the direct or restored final environment. -/
structure EnvironmentInductiveExecution
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe allowPrimitive : Bool)
    (fuel : FuelConfig) (finalEnv : Environment) where
  inputCheck : Environment.checkInductiveInput env types = .ok ()
  nested : ElimNestedInductive.Result
  nestedRun : ElimNestedInductive.runAt env fuel.inductiveFuel nparams
    lparams types = .ok nested
  flattened : NormalizationRecursorExecution nparams nested.types
    nested.aux2nested.size isUnsafe
      (Context.forInductive env lparams isUnsafe allowPrimitive fuel)
  flattenedRun : NormalizationRecursorExecution.buildExecution nparams
    nested.types nested.aux2nested.size isUnsafe
      (Context.forInductive env lparams isUnsafe allowPrimitive fuel) =
        .ok flattened
  completion : EnvironmentInductiveCompletion nested
    flattened.recursors.env env types allowPrimitive
      (if isUnsafe then .unsafe else .safe) lparams fuel finalEnv

/-- Operational completeness boundary for the full public inductive path:
every successful result has a retained execution with the same final
environment. -/
def EnvironmentInductiveExecution.Complete
    (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe allowPrimitive : Bool)
    (fuel : FuelConfig) : Prop :=
  ∀ finalEnv,
    Environment.addInductive env lparams nparams types isUnsafe
        allowPrimitive fuel = .ok finalEnv →
      Nonempty (EnvironmentInductiveExecution env lparams nparams types
        isUnsafe allowPrimitive fuel finalEnv)

namespace EnvironmentInductiveExecution

/-- Execute the instrumented outer pipeline, retaining every successful phase
and the exact final branch. -/
def buildExecution (env : Environment) (lparams : List Name) (nparams : Nat)
    (types : List InductiveType) (isUnsafe allowPrimitive : Bool)
    (fuel : FuelConfig := {}) :
    Except Exception (Σ finalEnv, EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv) :=
  match hinput : Environment.checkInductiveInput env types with
  | .error error => .error error
  | .ok () =>
    match hnested : ElimNestedInductive.runAt env fuel.inductiveFuel nparams
        lparams types with
    | .error error => .error error
    | .ok nested =>
      let context := Context.forInductive env lparams isUnsafe allowPrimitive
        fuel
      match hflattened : NormalizationRecursorExecution.buildExecution nparams
          nested.types nested.aux2nested.size isUnsafe context with
      | .error error => .error error
      | .ok flattened =>
        if hzero : nested.aux2nested.size = 0 then
          .ok ⟨flattened.recursors.env, {
            inputCheck := hinput
            nested
            nestedRun := hnested
            flattened
            flattenedRun := hflattened
            completion := .ordinary hzero }⟩
        else
          match hrestore : restoreNestedEnvironment nested
              flattened.recursors.env env types allowPrimitive
              (if isUnsafe then .unsafe else .safe) lparams fuel with
          | .error error => .error error
          | .ok restoration => .ok ⟨restoration.env, {
              inputCheck := hinput
              nested
              nestedRun := hnested
              flattened
              flattenedRun := hflattened
              completion := .nested hzero restoration hrestore }⟩

/-- Completeness of the full outer pipeline reduces to completeness of the
flattened ordinary producer.  All surrounding phases are exact public calls,
so their successful equations and the restoration branch can be retained by
case analysis. -/
theorem complete_of_flattened
    (flattenedComplete : ∀ (nested : ElimNestedInductive.Result),
      NormalizationRecursorExecution.Complete nparams nested.types
        nested.aux2nested.size isUnsafe
          (Context.forInductive env lparams isUnsafe allowPrimitive fuel)) :
    EnvironmentInductiveExecution.Complete env lparams nparams types
      isUnsafe allowPrimitive fuel := by
  intro finalEnv success
  unfold Environment.addInductive at success
  cases hinput : Environment.checkInductiveInput env types with
  | error error =>
      rw [hinput] at success
      contradiction
  | ok _ =>
      rw [hinput] at success
      simp only [Bind.bind, Except.bind] at success
      cases hnested : ElimNestedInductive.runAt env fuel.inductiveFuel
          nparams lparams types with
      | error error =>
          rw [hnested] at success
          contradiction
      | ok nested =>
          rw [hnested] at success
          simp only at success
          let context := Context.forInductive env lparams isUnsafe
            allowPrimitive fuel
          cases hflattened : AddInductive.run nparams nested.types
              nested.aux2nested.size context with
          | error error =>
              rw [hflattened] at success
              contradiction
          | ok flatEnv =>
              rw [hflattened] at success
              simp only at success
              obtain ⟨flattened, flattenedRun, flatEnvEq⟩ :=
                flattenedComplete nested flatEnv (by
                  simpa only [context] using hflattened)
              subst flatEnv
              by_cases hzero : nested.aux2nested.size = 0
              · have finalEq : flattened.recursors.env = finalEnv := by
                  have resultEq := success
                  simp only [hzero, if_pos, Pure.pure, Except.pure] at resultEq
                  exact Except.ok.inj resultEq
                subst finalEnv
                exact ⟨{
                  inputCheck := hinput
                  nested
                  nestedRun := hnested
                  flattened
                  flattenedRun := by simpa only [context] using flattenedRun
                  completion := .ordinary hzero }⟩
              · cases hrestore : restoreNestedEnvironment nested
                    flattened.recursors.env env types allowPrimitive
                    (if isUnsafe then .unsafe else .safe) lparams fuel with
                | error error =>
                    simp [hzero, hrestore] at success
                | ok restoration =>
                    have finalEq : restoration.env = finalEnv := by
                      have resultEq := success
                      simp only [hzero, hrestore, Pure.pure, Except.pure]
                        at resultEq
                      exact Except.ok.inj resultEq
                    subst finalEnv
                    exact ⟨{
                      inputCheck := hinput
                      nested
                      nestedRun := hnested
                      flattened
                      flattenedRun := by
                        simpa only [context] using flattenedRun
                      completion := .nested hzero restoration hrestore }⟩

/-- Full nested-aware operational completeness now has a single observer
boundary: retaining the normalization prefix of each successful flattened
ordinary call.  The public outer phases and all ordinary downstream phases are
complete by exact case analysis. -/
theorem complete_of_normalization
    (normalizationComplete : ∀ (nested : ElimNestedInductive.Result),
      NormalizationCandidateExecution.CompleteForRun nparams nested.types
        nested.aux2nested.size isUnsafe
          (Context.forInductive env lparams isUnsafe allowPrimitive fuel)) :
    EnvironmentInductiveExecution.Complete env lparams nparams types
      isUnsafe allowPrimitive fuel :=
  complete_of_flattened fun nested =>
    NormalizationRecursorExecution.complete_of_normalization
      (by cases isUnsafe <;> rfl) (normalizationComplete nested)

/-- Full nested-aware operational completeness from the exact pointwise
candidate observers absent from each flattened public run. -/
theorem complete_of_candidateObservers
    (candidateObservers : ∀ (nested : ElimNestedInductive.Result),
      NormalizationCandidateExecution.CandidateObserversComplete nparams
        nested.types nested.aux2nested.size isUnsafe
          (Context.forInductive env lparams isUnsafe allowPrimitive fuel)) :
    EnvironmentInductiveExecution.Complete env lparams nparams types
      isUnsafe allowPrimitive fuel :=
  complete_of_normalization fun nested =>
    NormalizationCandidateExecution.completeForRun_of_candidateObservers
      (by cases isUnsafe <;> rfl) (candidateObservers nested)

/-- Recompose a retained outer execution into the exact public
`Environment.addInductive` equation. -/
theorem addInductiveRun
    (execution : EnvironmentInductiveExecution env lparams nparams types
      isUnsafe allowPrimitive fuel finalEnv) :
    Environment.addInductive env lparams nparams types isUnsafe
      allowPrimitive fuel = .ok finalEnv := by
  cases execution with
  | mk inputCheck nested nestedRun flattened flattenedRun completion =>
    unfold Environment.addInductive
    rw [inputCheck, nestedRun]
    simp only [Bind.bind, Except.bind]
    rw [flattened.addInductiveRun flattenedRun]
    cases completion with
    | ordinary hzero =>
        simp [hzero]
        rfl
    | nested hnonzero restoration hrestore =>
        simp [hnonzero, hrestore]
        rfl

/-- Every retained outer inductive execution preserves the input environment's
quotient-initialization flag, in both the direct and restored branches. -/
theorem quotInit_eq
    (execution : EnvironmentInductiveExecution env lparams nparams types
      isUnsafe allowPrimitive fuel finalEnv) :
    finalEnv.quotInit = env.quotInit := by
  cases execution with
  | mk inputCheck nested nestedRun flattened flattenedRun completion =>
      cases completion with
      | ordinary _ =>
          simpa [Context.forInductive] using flattened.quotInit_eq flattenedRun
      | nested _ restoration _ =>
          exact restoration.trace.quotInit

/-- Any successful instrumented outer build therefore certifies the exact
result of the public inductive entry point. -/
theorem buildExecution_addInductiveRun
    {produced : Σ finalEnv, EnvironmentInductiveExecution env lparams
      nparams types isUnsafe allowPrimitive fuel finalEnv}
    (_run : buildExecution env lparams nparams types isUnsafe allowPrimitive
      fuel = .ok produced) :
    Environment.addInductive env lparams nparams types isUnsafe
      allowPrimitive fuel = .ok produced.1 :=
  produced.2.addInductiveRun

/-- A nonzero auxiliary inventory forces the retained outer execution into
its restoration branch and exposes that exact result. -/
theorem restoration_of_numNested_ne
    (execution : EnvironmentInductiveExecution env lparams nparams types
      isUnsafe allowPrimitive fuel finalEnv)
    (nonzero : execution.nested.aux2nested.size ≠ 0) :
    ∃ restoration : NestedRestorationResult execution.nested
        execution.flattened.recursors.env env types allowPrimitive
        (if isUnsafe then .unsafe else .safe) lparams fuel,
      restoreNestedEnvironment execution.nested
          execution.flattened.recursors.env env types allowPrimitive
          (if isUnsafe then .unsafe else .safe) lparams fuel =
        .ok restoration ∧
      finalEnv = restoration.env := by
  cases execution with
  | mk inputCheck nested nestedRun flattened flattenedRun completion =>
    cases completion with
    | ordinary zero => contradiction
    | nested _ restoration restorationRun =>
        exact ⟨restoration, restorationRun, rfl⟩

end EnvironmentInductiveExecution

/--
info: 'Lean4Lean.AddInductive.KTargetCtorTrace.run' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms KTargetCtorTrace.run

/--
info: 'Lean4Lean.AddInductive.KTargetExecution.buildExecution' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms KTargetExecution.buildExecution

/--
info: 'Lean4Lean.AddInductive.LargeEliminatorLoopTrace.run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LargeEliminatorLoopTrace.run

/--
info: 'Lean4Lean.AddInductive.LargeEliminatorExecution.buildExecution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms LargeEliminatorExecution.buildExecution

/--
info: 'Lean4Lean.AddInductive.ElimLevelExecution.run_of_large' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ElimLevelExecution.run_of_large

/--
info: 'Lean4Lean.AddInductive.ElimLevelExecution.recLevelParams_eq_large' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ElimLevelExecution.recLevelParams_eq_large

end AddInductive
end Lean4Lean
