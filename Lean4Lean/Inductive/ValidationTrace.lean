import Lean4Lean.Inductive.Add

set_option linter.unusedSimpArgs false

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace AddInductive
open TypeChecker

/-- The constructor root check runs with no validation-local declarations,
while retaining every other field of the post-family checker context. -/
def Context.withEmptyLocalContext (context : Context) : Context :=
  { context with lctx := {} }

/-- One exact successful `ensureType` execution used for an ordinary
constructor field. -/
structure ConstructorEnsureTypeStep where
  context : Context
  source : Expr
  result : Expr

def ConstructorEnsureTypeStep.Valid
    (step : ConstructorEnsureTypeStep) : Prop :=
  TypeChecker.M.run step.context.env step.context.safety
      step.context.lctx step.context.lparams step.context.fuel
      (TypeChecker.ensureType step.source) =
    .ok step.result

/-- The two successful universe branches of `checkConstructors`: either the
transparent structural comparison succeeds, or the exact fallback comparison
does. Keeping the branch choice prevents a trace from silently replacing the
executable universe test with a stronger premise. -/
inductive ConstructorUniverseTrace (resultLevel fieldLevel : Level) : Type where
  | structural
      (valid : levelStructGe resultLevel fieldLevel = true) :
      ConstructorUniverseTrace resultLevel fieldLevel
  | fallback
      (structuralFailed : levelStructGe resultLevel fieldLevel = false)
      (valid : (resultLevel.isAlwaysZero || resultLevel.geq' fieldLevel) = true) :
      ConstructorUniverseTrace resultLevel fieldLevel

namespace ConstructorUniverseTrace

/-- A field rejected by both executable universe comparisons cannot have a
successful universe trace. -/
theorem not_nonempty_of_rejected
    (structuralRejected : levelStructGe resultLevel fieldLevel = false)
    (fallbackRejected :
      (resultLevel.isAlwaysZero || resultLevel.geq' fieldLevel) = false) :
    ¬ Nonempty (ConstructorUniverseTrace resultLevel fieldLevel) := by
  rintro ⟨trace⟩
  cases trace with
  | structural valid => simp_all
  | fallback _ valid => simp_all

end ConstructorUniverseTrace

/-- Complete successful traversal of `checkPositivity.loop`, indexed by the
exact source expression, checker context, and remaining fuel. The recursive
constructor records the precise local declaration used by the executable
traversal; the terminal constructor records the accepted recursive target. -/
inductive ConstructorPositivityTrace
    (stats : InductiveStats) (ctor : Name) (argIdx : Nat) :
    (context : Context) → (source : Expr) → (fuel : Nat) → Type where
  | absent
      (context : Context) (source result : Expr) (fuel : Nat)
      (whnf : CandidateWhnfStep.Valid ⟨context, source, result⟩)
      (occurs : hasIndOcc stats.indConsts result = false) :
      ConstructorPositivityTrace stats ctor argIdx context source (fuel + 1)
  | forallE
      (context : Context) (source : Expr) (fuel : Nat)
      (name : Name) (domain body : Expr) (binderInfo : BinderInfo)
      (whnf : CandidateWhnfStep.Valid
        ⟨context, source, .forallE name domain body binderInfo⟩)
      (occurs : hasIndOcc stats.indConsts
        (.forallE name domain body binderInfo) = true)
      (domainFree : hasIndOcc stats.indConsts domain = false)
      (tail : ConstructorPositivityTrace stats ctor argIdx
        (context.pushLocalDecl name binderInfo
          (consumeTypeAnnotations domain))
        (body.instantiate1 context.freshExpr) fuel) :
      ConstructorPositivityTrace stats ctor argIdx context source (fuel + 1)
  | target
      (context : Context) (source result : Expr) (fuel targetIdx : Nat)
      (whnf : CandidateWhnfStep.Valid ⟨context, source, result⟩)
      (occurs : hasIndOcc stats.indConsts result = true)
      (terminal : result.isForall = false)
      (valid : isValidIndApp? stats result = some targetIdx) :
      ConstructorPositivityTrace stats ctor argIdx context source (fuel + 1)

namespace ConstructorPositivityTrace

/-- Observable recursive-target data retained by the positivity traversal.
`binderDepth` counts positive Pi domains traversed before the terminal family
application. -/
structure Target where
  familyIdx : Nat
  binderDepth : Nat
  deriving DecidableEq, Repr

/-- Erase proof fields while retaining the exact sibling-family ordinal and
positive-Pi depth selected by the executable positivity run. -/
def target? :
    ConstructorPositivityTrace stats ctor argIdx context source fuel →
      Option Target
  | .absent _ _ _ _ _ _ => none
  | .forallE _ _ _ _ _ _ _ _ _ _ tail =>
      tail.target?.map fun target =>
        { target with binderDepth := target.binderDepth + 1 }
  | .target _ _ _ _ familyIdx _ _ _ _ =>
      some { familyIdx, binderDepth := 0 }

/-- Erasing a positivity trace replays the exact executable traversal. -/
theorem run
    (trace : ConstructorPositivityTrace stats ctor argIdx context source fuel) :
    checkPositivity.loop stats ctor argIdx source fuel context = .ok () := by
  induction trace with
  | absent context source result fuel whnf occurs =>
      unfold checkPositivity.loop
      simp only [ReaderT.bind, Bind.bind, liftTypeChecker_apply]
      rw [whnf]
      simp only [Except.bind]
      rw [occurs]
      rfl
  | forallE context source fuel name domain body binderInfo whnf occurs
      domainFree tail ih =>
      unfold checkPositivity.loop
      simp only [ReaderT.bind, Bind.bind, liftTypeChecker_apply]
      rw [whnf]
      simp only [Except.bind]
      rw [occurs]
      simp only [Bool.not_true, Bool.false_eq_true, if_false,
        ReaderT.pure, Pure.pure, ReaderT.bind, Bind.bind,
        Except.bind, Except.pure]
      rw [domainFree]
      simp only [Bool.false_eq_true, if_false, withLocalDecl_apply]
      exact ih
  | target context source result fuel targetIdx whnf occurs terminal valid =>
      unfold checkPositivity.loop
      simp only [ReaderT.bind, Bind.bind, liftTypeChecker_apply]
      rw [whnf]
      simp only [Except.bind]
      rw [occurs]
      simp only [Bool.not_true, Bool.false_eq_true, if_false,
        ReaderT.pure, Pure.pure, ReaderT.bind, Bind.bind,
        Except.bind, Except.pure]
      cases result <;>
        simp_all [Expr.isForall, ReaderT.pure, Pure.pure, Except.pure]

/-- Every successful executable positivity traversal decomposes into the
source-indexed trace above. -/
theorem exists_of_run
    (success : checkPositivity.loop stats ctor argIdx source fuel context =
      .ok ()) :
    Nonempty (ConstructorPositivityTrace stats ctor argIdx
      context source fuel) := by
  induction fuel generalizing context source with
  | zero =>
      rw [checkPositivity.loop.eq_1] at success
      change Except.error Exception.deepRecursion = Except.ok () at success
      contradiction
  | succ fuel ih =>
      rw [checkPositivity.loop.eq_2] at success
      simp only [ReaderT.bind, Bind.bind, liftTypeChecker_apply] at success
      cases hwhnf : TypeChecker.M.run context.env context.safety context.lctx
          context.lparams context.fuel (TypeChecker.whnf source) with
      | error err => simp_all [Except.bind]
      | ok result =>
          rw [hwhnf] at success
          simp only [Except.bind] at success
          cases hocc : hasIndOcc stats.indConsts result with
          | false => exact ⟨.absent context source result fuel hwhnf hocc⟩
          | true =>
            rw [hocc] at success
            simp only [Bool.not_true, Bool.false_eq_true, if_false,
              ReaderT.pure, Pure.pure, ReaderT.bind, Bind.bind,
              Except.bind, Except.pure] at success
            cases result
            case forallE name domain body binderInfo =>
                simp only at success
                cases hdomain : hasIndOcc stats.indConsts domain with
                | false =>
                  rw [hdomain] at success
                  simp only [Bool.false_eq_true, if_false,
                    withLocalDecl_apply] at success
                  obtain ⟨tail⟩ := ih success
                  exact ⟨.forallE context source fuel name domain body
                    binderInfo hwhnf hocc hdomain tail⟩
                | true =>
                  rw [hdomain] at success
                  change Except.error _ = Except.ok () at success
                  contradiction
            all_goals
              simp only at success
              cases hvalid : isValidIndApp? stats _ with
              | none =>
                  rw [hvalid] at success
                  change Except.error _ = Except.ok () at success
                  contradiction
              | some targetIdx =>
                  exact ⟨.target context source _ fuel targetIdx
                    hwhnf hocc rfl hvalid⟩

/-- Execute the positivity traversal while retaining its exact dependent
trace as data. Unlike `exists_of_run`, this decomposition is transparent and
therefore remains available to later executable alignment audits; erasing the
result with `run` recovers the ordinary checker execution. -/
def buildExecution (stats : InductiveStats) (ctor : Name) (argIdx : Nat)
    (context : Context) (source : Expr) :
    (fuel : Nat) → Except Exception
      (ConstructorPositivityTrace stats ctor argIdx context source fuel)
  | 0 => .error .deepRecursion
  | fuel + 1 =>
      match hwhnf : TypeChecker.M.run context.env context.safety context.lctx
          context.lparams context.fuel (TypeChecker.whnf source) with
      | .error error => .error error
      | .ok result =>
          match hoccurs : hasIndOcc stats.indConsts result with
          | false => .ok (.absent context source result fuel hwhnf hoccurs)
          | true =>
              match hforall : result.isForall with
              | true =>
                  match result with
                  | .forallE name domain body binderInfo =>
                      match hdomain : hasIndOcc stats.indConsts domain with
                      | true => .error <| .other
                          s!"arg #{argIdx + 1} of '{ctor}' has a non positive occurrence of the datatypes being declared"
                      | false =>
                          match buildExecution stats ctor argIdx
                              (context.pushLocalDecl name binderInfo
                                (consumeTypeAnnotations domain))
                              (body.instantiate1 context.freshExpr) fuel with
                          | .error error => .error error
                          | .ok tail => .ok (.forallE context source fuel name
                              domain body binderInfo hwhnf hoccurs hdomain tail)
                  | _ => .error <| .other
                      "positivity WHNF shape disagrees with isForall"
              | false =>
                  match hvalid : isValidIndApp? stats result with
                  | none => .error <| .other
                      s!"arg #{argIdx + 1} of '{ctor}' has a non valid occurrence of the datatypes being declared"
                  | some targetIdx => .ok (.target context source result fuel
                      targetIdx hwhnf hoccurs hforall hvalid)

/-- The transparent decomposition succeeds on every input accepted by the
executable positivity traversal, so retained-trace construction needs no
choice principle. -/
theorem buildExecution_ok_of_run
    (success : checkPositivity.loop stats ctor argIdx source fuel context =
      .ok ()) :
    ∃ trace, buildExecution stats ctor argIdx context source fuel =
      .ok trace := by
  induction fuel generalizing context source with
  | zero =>
      rw [checkPositivity.loop.eq_1] at success
      change Except.error Exception.deepRecursion = Except.ok () at success
      contradiction
  | succ fuel ih =>
      rw [checkPositivity.loop.eq_2] at success
      simp only [ReaderT.bind, Bind.bind, liftTypeChecker_apply] at success
      unfold buildExecution
      split
      next error heq =>
        rw [heq] at success
        simp [Except.bind] at success
      next result heq =>
        rw [heq] at success
        simp only [Except.bind] at success
        split
        next hoccurs => exact ⟨_, rfl⟩
        next hoccurs =>
          rw [hoccurs] at success
          simp only [Bool.not_true, Bool.false_eq_true, if_false,
            ReaderT.pure, Pure.pure, ReaderT.bind, Bind.bind,
            Except.bind, Except.pure] at success
          cases result <;> simp only [Expr.isForall] <;> simp only at success
          case forallE name domain body binderInfo =>
            split
            next hdomain =>
              rw [hdomain] at success
              change Except.error _ = Except.ok () at success
              contradiction
            next hdomain =>
              rw [hdomain] at success
              have tailSuccess :
                  checkPositivity.loop stats ctor argIdx
                    (body.instantiate1 context.freshExpr) fuel
                    (context.pushLocalDecl name binderInfo
                      (consumeTypeAnnotations domain)) = .ok () := success
              obtain ⟨tail, htail⟩ := ih tailSuccess
              rw [htail]
              exact ⟨_, rfl⟩
          all_goals
            split
            next hvalid =>
              rw [hvalid] at success
              change Except.error _ = Except.ok () at success
              contradiction
            next targetIdx hvalid => exact ⟨_, rfl⟩

/-- An exact positivity failure, including its diagnostic payload, excludes a
successful trace at precisely that source/context/fuel position. -/
theorem not_nonempty_of_error
    (failure : checkPositivity.loop stats ctor argIdx source fuel context =
      .error err) :
    ¬ Nonempty (ConstructorPositivityTrace stats ctor argIdx
      context source fuel) := by
  rintro ⟨trace⟩
  have success := trace.run
  rw [failure] at success
  contradiction

end ConstructorPositivityTrace

/-- Whether positivity was executed or skipped by the exact `isUnsafe`
branch of constructor validation. -/
inductive ConstructorPositivityModeTrace
    (stats : InductiveStats) (isUnsafe : Bool)
    (ctor : Name) (argIdx : Nat) (context : Context) (source : Expr) : Type where
  | skipped
      (isUnsafe_eq : isUnsafe = true) :
      ConstructorPositivityModeTrace stats isUnsafe ctor argIdx context source
  | safe
      (isUnsafe_eq : isUnsafe = false)
      (trace : ConstructorPositivityTrace stats ctor argIdx context source
        context.fuel.inductiveFuel) :
      ConstructorPositivityModeTrace stats isUnsafe ctor argIdx context source

namespace ConstructorPositivityModeTrace

/-- Observable recursive target for the exact safe/unsafe positivity branch.
Unsafe validation deliberately exposes no positivity claim. -/
def target? :
    ConstructorPositivityModeTrace
      stats isUnsafe ctor argIdx context source →
      Option ConstructorPositivityTrace.Target
  | .skipped _ => none
  | .safe _ trace => trace.target?

theorem run
    (trace : ConstructorPositivityModeTrace
      stats isUnsafe ctor argIdx context source) :
    (if !isUnsafe then checkPositivity stats source ctor argIdx else pure ())
        context = .ok () := by
  cases trace with
  | skipped h => simp [h, ReaderT.pure, Pure.pure, Except.pure]
  | safe h trace =>
      simp only [h, Bool.not_false, if_true]
      unfold checkPositivity
      simpa only [readThe, MonadReaderOf.read, ReaderT.read,
        ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
        Except.bind, Except.pure] using trace.run

/-- Execute the recorded positivity branch and then an exact continuation. -/
theorem bind_run
    (trace : ConstructorPositivityModeTrace
      stats isUnsafe ctor argIdx context source)
    (next : M α) (result : α)
    (nextRun : next context = .ok result) :
    (do
      if !isUnsafe then checkPositivity stats source ctor argIdx
      next) context = .ok result := by
  cases trace with
  | skipped h =>
      simp [h, nextRun, ReaderT.bind, Bind.bind,
        ReaderT.pure, Pure.pure, Except.bind, Except.pure]
  | safe h trace =>
      have positivityRun :
          checkPositivity stats source ctor argIdx context = .ok () := by
        unfold checkPositivity
        simpa only [readThe, MonadReaderOf.read, ReaderT.read,
          ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
          Except.bind, Except.pure] using trace.run
      simp [h, positivityRun, nextRun, ReaderT.bind, Bind.bind,
        ReaderT.pure, Pure.pure, Except.bind, Except.pure]

/-- A successful executable positivity branch determines whether validation
was skipped for an unsafe declaration or supplies the full safe trace. -/
theorem exists_of_run
    (success :
      (if !isUnsafe then checkPositivity stats source ctor argIdx else pure ())
        context = .ok ()) :
    Nonempty (ConstructorPositivityModeTrace
      stats isUnsafe ctor argIdx context source) := by
  cases hUnsafe : isUnsafe with
  | false =>
      simp only [hUnsafe, Bool.not_false, if_true] at success
      unfold checkPositivity at success
      simp only [readThe, MonadReaderOf.read, ReaderT.read,
        ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
        Except.bind, Except.pure] at success
      obtain ⟨trace⟩ := ConstructorPositivityTrace.exists_of_run success
      exact ⟨.safe rfl trace⟩
  | true => exact ⟨.skipped rfl⟩

/-- Transparently retain the exact safe/unsafe positivity branch selected by
constructor validation. -/
def buildExecution (stats : InductiveStats) (isUnsafe : Bool)
    (ctor : Name) (argIdx : Nat) (context : Context) (source : Expr) :
    Except Exception
      (ConstructorPositivityModeTrace stats isUnsafe ctor argIdx context source) :=
  match isUnsafe with
  | true => .ok (.skipped rfl)
  | false =>
      match ConstructorPositivityTrace.buildExecution stats ctor argIdx
          context source context.fuel.inductiveFuel with
      | .error error => .error error
      | .ok trace => .ok (.safe rfl trace)

/-- The retained safe/unsafe branch decomposition succeeds whenever the
executable positivity branch does. -/
theorem buildExecution_ok_of_run
    (success :
      (if !isUnsafe then checkPositivity stats source ctor argIdx else pure ())
        context = .ok ()) :
    ∃ trace, buildExecution stats isUnsafe ctor argIdx context source =
      .ok trace := by
  cases isUnsafe with
  | true => exact ⟨_, rfl⟩
  | false =>
      simp only [Bool.not_false, if_true] at success
      unfold checkPositivity at success
      simp only [readThe, MonadReaderOf.read, ReaderT.read,
        ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
        Except.bind, Except.pure] at success
      obtain ⟨trace, htrace⟩ :=
        ConstructorPositivityTrace.buildExecution_ok_of_run success
      unfold buildExecution
      rw [htrace]
      exact ⟨_, rfl⟩

/-- Failure of the exact safe/unsafe positivity branch excludes its retained
mode trace without changing the executable diagnostic. -/
theorem not_nonempty_of_error
    (failure :
      (if !isUnsafe then checkPositivity stats source ctor argIdx else pure ())
        context = .error err) :
    ¬ Nonempty (ConstructorPositivityModeTrace
      stats isUnsafe ctor argIdx context source) := by
  rintro ⟨trace⟩
  have success := trace.run
  rw [failure] at success
  contradiction

end ConstructorPositivityModeTrace

/-- Exact successful validation of one constructor type from its root through
its parameter prefix, ordinary fields, positivity checks, and terminal family
application. Every recursive index is selected by the executable traversal. -/
inductive ConstructorTypeValidationTrace
    (stats : InductiveStats) (isUnsafe : Bool)
    (familyIdx : Nat) (ctor : Name) :
    (context : Context) → (source : Expr) →
      (argIdx fuel : Nat) → Type where
  | parameter
      (context : Context) (fuel argIdx : Nat)
      (name : Name) (domain body : Expr) (binderInfo : BinderInfo)
      (param parameterType : Expr)
      (parameterAt : stats.params[argIdx]? = some param)
      (parameterTypeRun : getType param context = .ok parameterType)
      (defeq : CandidateIsDefEqStep.Valid
        ⟨context, domain, parameterType⟩)
      (tail : ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
        context (body.instantiate1 param) (argIdx + 1) fuel) :
      ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
        context (.forallE name domain body binderInfo) argIdx (fuel + 1)
  | ordinary
      (context : Context) (fuel argIdx : Nat)
      (name : Name) (domain body : Expr) (binderInfo : BinderInfo)
      (sortResult : Expr)
      (noParameter : stats.params[argIdx]? = none)
      (ensureType : ConstructorEnsureTypeStep.Valid
        ⟨context, domain, sortResult⟩)
      (universeTrace : ConstructorUniverseTrace
        stats.resultLevel sortResult.sortLevel!)
      (positivity : ConstructorPositivityModeTrace
        stats isUnsafe ctor argIdx context domain)
      (tail : ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
        (context.pushLocalDecl name binderInfo
          (consumeTypeAnnotations domain))
        (body.instantiate1 context.freshExpr) (argIdx + 1) fuel) :
      ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
        context (.forallE name domain body binderInfo) argIdx (fuel + 1)
  | terminal
      (context : Context) (source : Expr) (fuel argIdx : Nat)
      (terminal : source.isForall = false)
      (valid : isValidIndAppIdx stats source familyIdx = true) :
      ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
        context source argIdx (fuel + 1)

namespace ConstructorTypeValidationTrace

/-- Field-ordered recursive-target observations for one constructor. Parameter
binders are omitted; every ordinary constructor field contributes one slot. -/
def targets :
    ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
      context source argIdx fuel →
      List (Option ConstructorPositivityTrace.Target)
  | .parameter _ _ _ _ _ _ _ _ _ _ _ _ tail => tail.targets
  | .ordinary _ _ _ _ _ _ _ _ _ _ _ positivity tail =>
      positivity.target? :: tail.targets
  | .terminal _ _ _ _ _ _ => []

/-- Erasing one constructor-type trace replays the exact inner
`checkConstructorType.loop` execution. -/
theorem run
    (trace : ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
      context source argIdx fuel) :
    checkConstructorType.loop stats isUnsafe familyIdx ctor source argIdx fuel
        context = .ok () := by
  induction trace with
  | parameter context fuel argIdx name domain body binderInfo param
      parameterType parameterAt parameterTypeRun defeq tail ih =>
      rw [show fuel + 1 = Nat.succ fuel by omega]
      rw [checkConstructorType.loop.eq_2]
      rw [parameterAt]
      simp only [ReaderT.bind, Bind.bind]
      rw [parameterTypeRun]
      simp only [Except.bind, liftTypeChecker_apply]
      rw [defeq]
      simp only [if_true, ReaderT.pure, Pure.pure, ReaderT.bind, Bind.bind,
        Except.bind, Except.pure]
      exact ih
  | ordinary context fuel argIdx name domain body binderInfo sortResult noParameter
      ensureType universeTrace positivity tail ih =>
      rw [show fuel + 1 = Nat.succ fuel by omega]
      rw [checkConstructorType.loop.eq_2]
      rw [noParameter]
      simp only [ReaderT.bind, Bind.bind, liftTypeChecker_apply]
      rw [ensureType]
      simp only [Except.bind]
      let next : M PUnit :=
        withLocalDecl name binderInfo (consumeTypeAnnotations domain) fun arg =>
          checkConstructorType.loop stats isUnsafe familyIdx ctor
            (body.instantiate1 arg) (argIdx + 1) fuel
      have nextRun : next context = .ok () := by
        simp only [next, withLocalDecl_apply]
        exact ih
      have restRun :
          (do
            if !isUnsafe then checkPositivity stats domain ctor argIdx
            next) context = .ok () :=
        positivity.bind_run next () nextRun
      cases universeTrace with
      | structural valid =>
          rw [valid]
          simp only [if_true, ReaderT.pure, Pure.pure,
            ReaderT.bind, Bind.bind, Except.bind, Except.pure]
          exact restRun
      | fallback structuralFailed valid =>
          rw [structuralFailed, valid]
          simp only [Bool.true_eq_false, Bool.not_true, if_false,
            Bool.false_eq_true,
            ReaderT.pure, Pure.pure, ReaderT.bind, Bind.bind,
            Except.bind, Except.pure]
          exact restRun
  | terminal context source fuel argIdx terminal valid =>
      rw [show fuel + 1 = Nat.succ fuel by omega]
      cases source <;>
        simp_all [checkConstructorType.loop, Expr.isForall,
          ReaderT.pure, Pure.pure, Except.pure]

/-- Every successful one-constructor telescope traversal decomposes into the
exact parameter, field, universe, positivity, and terminal trace. -/
theorem exists_of_run
    (success :
      checkConstructorType.loop stats isUnsafe familyIdx ctor source argIdx fuel
        context = .ok ()) :
    Nonempty (ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
      context source argIdx fuel) := by
  induction fuel generalizing context source argIdx with
  | zero =>
      rw [checkConstructorType.loop.eq_1] at success
      change Except.error Exception.deepRecursion = Except.ok () at success
      contradiction
  | succ fuel ih =>
      rw [show fuel + 1 = Nat.succ fuel by omega] at success
      cases source
      case forallE name domain body binderInfo =>
        rw [checkConstructorType.loop.eq_2] at success
        simp only at success
        cases hparam : stats.params[argIdx]? with
        | some param =>
            rw [hparam] at success
            simp only [ReaderT.bind, Bind.bind] at success
            cases hget : getType param context with
            | error err => simp_all [Except.bind]
            | ok parameterType =>
                rw [hget] at success
                simp only [Except.bind, liftTypeChecker_apply] at success
                cases hdefeq : TypeChecker.M.run context.env context.safety
                    context.lctx context.lparams context.fuel
                    (TypeChecker.isDefEq domain parameterType) with
                | error err => simp_all [Except.bind]
                | ok equal =>
                    rw [hdefeq] at success
                    simp only [Except.bind] at success
                    cases equal with
                    | false =>
                        change Except.error _ = Except.ok () at success
                        contradiction
                    | true =>
                        simp only [if_true, ReaderT.pure, Pure.pure,
                          ReaderT.bind, Bind.bind, Except.bind,
                          Except.pure] at success
                        obtain ⟨tail⟩ := ih success
                        exact ⟨.parameter context fuel argIdx name domain body
                          binderInfo param parameterType hparam hget hdefeq tail⟩
        | none =>
            rw [hparam] at success
            simp only [ReaderT.bind, Bind.bind,
              liftTypeChecker_apply] at success
            cases hensure : TypeChecker.M.run context.env context.safety
                context.lctx context.lparams context.fuel
                (TypeChecker.ensureType domain) with
            | error err => simp_all [Except.bind]
            | ok sortResult =>
                rw [hensure] at success
                simp only [Except.bind] at success
                have finish
                    (universeTrace : ConstructorUniverseTrace
                      stats.resultLevel sortResult.sortLevel!)
                    (restSuccess :
                      (do
                        if !isUnsafe then
                          checkPositivity stats domain ctor argIdx
                        withLocalDecl name binderInfo
                            (consumeTypeAnnotations domain) fun arg =>
                          checkConstructorType.loop stats isUnsafe familyIdx ctor
                            (body.instantiate1 arg) (argIdx + 1) fuel)
                        context = .ok ()) :
                    Nonempty (ConstructorTypeValidationTrace stats isUnsafe
                      familyIdx ctor context
                      (.forallE name domain body binderInfo) argIdx (fuel + 1)) := by
                  cases isUnsafe with
                  | false =>
                      simp only [Bool.not_false, if_true,
                        ReaderT.bind, Bind.bind] at restSuccess
                      cases hpos : checkPositivity stats domain ctor argIdx context with
                      | error err => simp_all [Except.bind]
                      | ok typeUnit =>
                          cases typeUnit
                          rw [hpos] at restSuccess
                          simp only [Except.bind, withLocalDecl_apply] at restSuccess
                          have hposLoop :
                              checkPositivity.loop stats ctor argIdx domain
                                  context.fuel.inductiveFuel context = .ok () := by
                            unfold checkPositivity at hpos
                            simpa only [readThe, MonadReaderOf.read, ReaderT.read,
                              ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
                              Except.bind, Except.pure] using hpos
                          obtain ⟨positivityTrace⟩ :=
                            ConstructorPositivityTrace.exists_of_run hposLoop
                          obtain ⟨tail⟩ := ih restSuccess
                          exact ⟨.ordinary context fuel argIdx name domain body
                            binderInfo sortResult hparam hensure universeTrace
                            (.safe rfl positivityTrace) tail⟩
                  | true =>
                      simp only [Bool.not_true, if_false,
                        ReaderT.pure, Pure.pure, ReaderT.bind, Bind.bind,
                        Except.bind, Except.pure,
                        withLocalDecl_apply] at restSuccess
                      obtain ⟨tail⟩ := ih restSuccess
                      exact ⟨.ordinary context fuel argIdx name domain body
                        binderInfo sortResult hparam hensure universeTrace
                        (.skipped rfl) tail⟩
                cases hstruct : levelStructGe stats.resultLevel
                    sortResult.sortLevel! with
                | true =>
                    rw [hstruct] at success
                    simp only [if_true, ReaderT.pure, Pure.pure,
                      ReaderT.bind, Bind.bind, Except.bind,
                      Except.pure] at success
                    exact finish (.structural hstruct) success
                | false =>
                    rw [hstruct] at success
                    simp only [Bool.false_eq_true, if_false] at success
                    cases hfallback :
                        (stats.resultLevel.isAlwaysZero ||
                          stats.resultLevel.geq' sortResult.sortLevel!) with
                    | false =>
                        rw [hfallback] at success
                        change Except.error _ = Except.ok () at success
                        contradiction
                    | true =>
                        rw [hfallback] at success
                        simp only [Bool.true_eq_false, Bool.not_true, if_false,
                          ReaderT.pure, Pure.pure, ReaderT.bind, Bind.bind,
                          Except.bind, Except.pure] at success
                        exact finish (.fallback hstruct hfallback) success
      all_goals
        unfold checkConstructorType.loop at success
        simp only at success
        cases hvalid : isValidIndAppIdx stats _ familyIdx with
        | false =>
            rw [hvalid] at success
            change Except.error _ = Except.ok () at success
            contradiction
        | true =>
            exact ⟨.terminal context _ fuel argIdx rfl hvalid⟩

/-- Execute one constructor telescope while retaining the exact parameter,
universe, positivity, and terminal choices made by the ordinary validator.
The returned data is transparent, so later executable gates can inspect the
same trace without selecting it through `Classical.choice`. -/
def buildExecution (stats : InductiveStats) (isUnsafe : Bool)
    (familyIdx : Nat) (ctor : Name) (context : Context) (source : Expr)
    (argIdx : Nat) :
    (fuel : Nat) → Except Exception
      (ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
        context source argIdx fuel)
  | 0 => .error .deepRecursion
  | fuel + 1 =>
      match hforall : source.isForall with
      | false =>
          match hvalid : isValidIndAppIdx stats source familyIdx with
          | false => .error <| .other s!"invalid return type for '{ctor}'"
          | true => .ok (.terminal context source fuel argIdx hforall hvalid)
      | true =>
          match source with
          | .forallE name domain body binderInfo =>
              match hparam : stats.params[argIdx]? with
              | some param =>
                  match hget : getType param context with
                  | .error error => .error error
                  | .ok parameterType =>
                      match hdefeq : TypeChecker.M.run context.env
                          context.safety context.lctx context.lparams
                          context.fuel
                          (TypeChecker.isDefEq domain parameterType) with
                      | .error error => .error error
                      | .ok false => .error <| .other
                          s!"arg #{argIdx + 1} of '{ctor}' does not match inductive datatype parameters"
                      | .ok true =>
                          match buildExecution stats isUnsafe familyIdx ctor
                              context (body.instantiate1 param) (argIdx + 1)
                              fuel with
                          | .error error => .error error
                          | .ok tail => .ok (.parameter context fuel argIdx
                              name domain body binderInfo param parameterType
                              hparam hget hdefeq tail)
              | none =>
                  match hensure : TypeChecker.M.run context.env context.safety
                      context.lctx context.lparams context.fuel
                      (TypeChecker.ensureType domain) with
                  | .error error => .error error
                  | .ok sortResult =>
                      let finish (universeTrace : ConstructorUniverseTrace
                          stats.resultLevel sortResult.sortLevel!) :=
                        match ConstructorPositivityModeTrace.buildExecution
                            stats isUnsafe ctor argIdx context domain with
                        | .error error => .error error
                        | .ok positivity =>
                            match buildExecution stats isUnsafe familyIdx ctor
                                (context.pushLocalDecl name binderInfo
                                  (consumeTypeAnnotations domain))
                                (body.instantiate1 context.freshExpr)
                                (argIdx + 1) fuel with
                            | .error error => .error error
                            | .ok tail => .ok (.ordinary context fuel argIdx
                                name domain body binderInfo sortResult hparam
                                hensure universeTrace positivity tail)
                      match hstruct : levelStructGe stats.resultLevel
                          sortResult.sortLevel! with
                      | true => finish (.structural hstruct)
                      | false =>
                          match hfallback : stats.resultLevel.isAlwaysZero ||
                              stats.resultLevel.geq' sortResult.sortLevel! with
                          | false => .error <| .other
                              s!"universe level of type_of(arg #{argIdx + 1}) of '{ctor}' is too big for the corresponding inductive datatype"
                          | true => finish (.fallback hstruct hfallback)
          | _ => .error <| .other
              "constructor source shape disagrees with isForall"

/-- The transparent telescope decomposition succeeds on every constructor
type accepted by the inner executable validator. -/
theorem buildExecution_ok_of_run
    (success :
      checkConstructorType.loop stats isUnsafe familyIdx ctor source argIdx fuel
        context = .ok ()) :
    ∃ trace, buildExecution stats isUnsafe familyIdx ctor context source
      argIdx fuel = .ok trace := by
  induction fuel generalizing context source argIdx with
  | zero =>
      rw [checkConstructorType.loop.eq_1] at success
      change Except.error Exception.deepRecursion = Except.ok () at success
      contradiction
  | succ fuel ih =>
      rw [show fuel + 1 = Nat.succ fuel by omega] at success
      cases source
      case forallE name domain body binderInfo =>
        rw [checkConstructorType.loop.eq_2] at success
        simp only at success
        unfold buildExecution
        simp only [Expr.isForall]
        split
        next param hparam =>
          rw [hparam] at success
          simp only [ReaderT.bind, Bind.bind] at success
          split
          next error heq =>
            rw [heq] at success
            simp [Except.bind] at success
          next parameterType heq =>
            rw [heq] at success
            simp only [Except.bind, liftTypeChecker_apply] at success
            split
            next error heq2 =>
              rw [heq2] at success
              simp [Except.bind] at success
            next heq2 =>
              rw [heq2] at success
              simp only [Except.bind] at success
              change Except.error _ = Except.ok () at success
              contradiction
            next heq2 =>
              rw [heq2] at success
              simp only [Except.bind, if_true, ReaderT.pure, Pure.pure,
                ReaderT.bind, Bind.bind, Except.pure] at success
              obtain ⟨tail, htail⟩ := ih success
              rw [htail]
              exact ⟨_, rfl⟩
        next hparam =>
          rw [hparam] at success
          simp only [ReaderT.bind, Bind.bind, liftTypeChecker_apply] at success
          split
          next error heq =>
            rw [heq] at success
            simp [Except.bind] at success
          next sortResult heq =>
            rw [heq] at success
            simp only [Except.bind] at success
            have finish :
                (do
                  if !isUnsafe then checkPositivity stats domain ctor argIdx
                  withLocalDecl name binderInfo (consumeTypeAnnotations domain)
                      fun arg =>
                    checkConstructorType.loop stats isUnsafe familyIdx ctor
                      (body.instantiate1 arg) (argIdx + 1) fuel)
                    context = .ok () →
                (∃ positivity,
                  ConstructorPositivityModeTrace.buildExecution stats isUnsafe
                    ctor argIdx context domain = .ok positivity) ∧
                ∃ tail,
                  buildExecution stats isUnsafe familyIdx ctor
                    (context.pushLocalDecl name binderInfo
                      (consumeTypeAnnotations domain))
                    (body.instantiate1 context.freshExpr) (argIdx + 1) fuel =
                    .ok tail := by
              intro restSuccess
              cases isUnsafe with
              | false =>
                  simp only [Bool.not_false, if_true,
                    ReaderT.bind, Bind.bind] at restSuccess
                  cases hpos : checkPositivity stats domain ctor argIdx
                      context with
                  | error err => simp_all [Except.bind]
                  | ok posUnit =>
                      cases posUnit
                      rw [hpos] at restSuccess
                      simp only [Except.bind,
                        withLocalDecl_apply] at restSuccess
                      have hpmSuccess :
                          (if !false then
                            checkPositivity stats domain ctor argIdx
                          else pure ()) context = .ok () := by
                        simpa using hpos
                      exact ⟨ConstructorPositivityModeTrace.buildExecution_ok_of_run
                        hpmSuccess, ih restSuccess⟩
              | true =>
                  simp only [Bool.not_true, if_false,
                    ReaderT.pure, Pure.pure, ReaderT.bind, Bind.bind,
                    Except.bind, Except.pure,
                    withLocalDecl_apply] at restSuccess
                  have hpmSuccess :
                      (if !true then
                        checkPositivity stats domain ctor argIdx
                      else pure ()) context = .ok () := by
                    simp [ReaderT.pure, Pure.pure, Except.pure]
                  exact ⟨ConstructorPositivityModeTrace.buildExecution_ok_of_run
                    hpmSuccess, ih restSuccess⟩
            split
            next hstruct =>
              rw [hstruct] at success
              simp only [if_true, ReaderT.pure, Pure.pure,
                ReaderT.bind, Bind.bind, Except.bind, Except.pure] at success
              obtain ⟨⟨positivity, hpm⟩, tail, htail⟩ := finish success
              rw [hpm, htail]
              exact ⟨_, rfl⟩
            next hstruct =>
              rw [hstruct] at success
              simp only [Bool.false_eq_true, if_false] at success
              split
              next hfallback =>
                rw [hfallback] at success
                change Except.error _ = Except.ok () at success
                contradiction
              next hfallback =>
                rw [hfallback] at success
                simp only [Bool.true_eq_false, Bool.not_true, if_false,
                  ReaderT.pure, Pure.pure, ReaderT.bind, Bind.bind,
                  Except.bind, Except.pure] at success
                obtain ⟨⟨positivity, hpm⟩, tail, htail⟩ := finish success
                rw [hpm, htail]
                exact ⟨_, rfl⟩
      all_goals
        unfold checkConstructorType.loop at success
        simp only at success
        unfold buildExecution
        simp only [Expr.isForall]
        split
        next hvalid =>
          rw [hvalid] at success
          change Except.error _ = Except.ok () at success
          contradiction
        next hvalid => exact ⟨_, rfl⟩

/-- Erasing the inner trace also replays the public one-constructor checker,
including its exact context-fuel read. -/
theorem check_run
    (trace : ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
      context source 0 context.fuel.inductiveFuel) :
    checkConstructorType stats isUnsafe familyIdx ctor source context = .ok () := by
  unfold checkConstructorType
  simpa only [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
    Except.bind, Except.pure] using trace.run

/-- Any exact inner constructor-telescope failure excludes a trace at that
same parameter/field/terminal position and retains the original error value. -/
theorem not_nonempty_of_error
    (failure :
      checkConstructorType.loop stats isUnsafe familyIdx ctor source argIdx fuel
        context = .error err) :
    ¬ Nonempty (ConstructorTypeValidationTrace stats isUnsafe familyIdx ctor
      context source argIdx fuel) := by
  rintro ⟨trace⟩
  have success := trace.run
  rw [failure] at success
  contradiction

end ConstructorTypeValidationTrace

/-- Source-ordered validation of a constructor list. The `seen` index makes
duplicate-name checks part of the trace and prevents reordering or omission.
Root closedness and full type checking are retained before the recursive type
trace, exactly as in `checkConstructors`. -/
inductive ConstructorListValidationTrace
    (stats : InductiveStats) (isUnsafe : Bool)
    (familyIdx : Nat) (context : Context) :
    NameSet → List Constructor → Type where
  | nil (seen : NameSet) :
      ConstructorListValidationTrace stats isUnsafe familyIdx context seen []
  | cons
      (seen : NameSet) (head : Constructor) (tail : List Constructor)
      (fresh : seen.contains head.name = false)
      (closed : context.env.checkNoMVarNoFVar head.name head.type = .ok ())
      (rootCheck : CandidateCheckTypeObservation
        context.withEmptyLocalContext head.type)
      (typeTrace : ConstructorTypeValidationTrace
        stats isUnsafe familyIdx head.name context head.type 0
        context.fuel.inductiveFuel)
      (tailTrace : ConstructorListValidationTrace stats isUnsafe familyIdx
        context (seen.insert head.name) tail) :
      ConstructorListValidationTrace stats isUnsafe familyIdx context
        seen (head :: tail)

namespace ConstructorListValidationTrace

/-- Constructor-ordered positivity observations for one family. -/
def targets :
    ConstructorListValidationTrace stats isUnsafe familyIdx
      context seen constructors →
      List (List (Option ConstructorPositivityTrace.Target))
  | .nil _ => []
  | .cons _ _ _ _ _ _ typeTrace tailTrace =>
      typeTrace.targets :: tailTrace.targets

/-- Execute the source-ordered constructor fold while retaining its exact
dependent validation trace.  Every stored equation is obtained from the same
checker call made by `checkConstructorFold`; no semantic premise participates
in acceptance. -/
def buildExecution (stats : InductiveStats) (isUnsafe : Bool)
    (familyIdx : Nat) (context : Context) :
    (seen : NameSet) → (constructors : List Constructor) →
      Except Exception
        (ConstructorListValidationTrace stats isUnsafe familyIdx context
          seen constructors)
  | seen, [] => .ok (.nil seen)
  | seen, head :: tail =>
      match hfresh : seen.contains head.name with
      | true => .error <| .other s!"duplicate constructor name '{head.name}'"
      | false =>
          match hclosed : context.env.checkNoMVarNoFVar
              head.name head.type with
          | .error error => .error error
          | .ok () =>
              match hroot : TypeChecker.M.run context.env context.safety {}
                  context.lparams context.fuel
                  (TypeChecker.checkType head.type) with
              | .error error => .error error
              | .ok inferred =>
                  let rootCheck : CandidateCheckTypeObservation
                      context.withEmptyLocalContext head.type :=
                    ⟨inferred, by
                      simpa only [CandidateCheckTypeStep.Valid,
                        Context.withEmptyLocalContext] using hroot⟩
                  match ConstructorTypeValidationTrace.buildExecution stats
                      isUnsafe familyIdx head.name context head.type 0
                      context.fuel.inductiveFuel with
                  | .error error => .error error
                  | .ok typeTrace =>
                      match buildExecution stats isUnsafe familyIdx context
                          (seen.insert head.name) tail with
                      | .error error => .error error
                      | .ok tailTrace => .ok (.cons seen head tail hfresh
                          hclosed rootCheck typeTrace tailTrace)

end ConstructorListValidationTrace

/-- A transparent presentation of the constructor portion of the executable
validator, discarding only the final duplicate-name accumulator. -/
def checkConstructorList
    (stats : InductiveStats) (isUnsafe : Bool) (familyIdx : Nat)
    (context : Context) (seen : NameSet) (ctors : List Constructor) :
    Except Exception Unit := do
  _ ← checkConstructorFold context.env stats isUnsafe familyIdx seen ctors context
  pure ()

/-- For one family, the named list recursion is exactly the array/list shell
of the real constructor validator. -/
theorem checkConstructors_singleton_eq_checkConstructorList
    (indType : InductiveType) (stats : InductiveStats)
    (isUnsafe : Bool) (context : Context) :
    checkConstructors #[indType] stats isUnsafe context =
      checkConstructorList stats isUnsafe 0 context {} indType.ctors := by
  unfold checkConstructors
  simp only [ReaderT.bind, Bind.bind]
  rw [liftTypeChecker_apply]
  have hget :
      TypeChecker.M.run context.env context.safety context.lctx
          context.lparams context.fuel TypeChecker.getEnv =
        .ok context.env := by rfl
  rw [hget]
  simp only [Except.bind]
  simp only [checkConstructorsLoop]
  unfold checkConstructorList
  simp only [ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
    Except.bind, Except.pure]

namespace ConstructorListValidationTrace

def finalSeen : NameSet → List Constructor → NameSet
  | seen, [] => seen
  | seen, head :: tail => finalSeen (seen.insert head.name) tail

/-- Exact inversion for a nonempty source list. In particular the recursive
trace is indexed by the literal source tail and the accumulator obtained from
the literal source head, so omission, insertion, duplication, or reordering
cannot be hidden behind an unindexed traversal. -/
theorem nonempty_cons_iff_exact_source :
    Nonempty (ConstructorListValidationTrace stats isUnsafe familyIdx
      context seen (head :: tail)) ↔
      seen.contains head.name = false ∧
      context.env.checkNoMVarNoFVar head.name head.type = .ok () ∧
      Nonempty (CandidateCheckTypeObservation
        context.withEmptyLocalContext head.type) ∧
      Nonempty (ConstructorTypeValidationTrace stats isUnsafe familyIdx
        head.name context head.type 0 context.fuel.inductiveFuel) ∧
      Nonempty (ConstructorListValidationTrace stats isUnsafe familyIdx
        context (seen.insert head.name) tail) := by
  constructor
  · rintro ⟨trace⟩
    cases trace with
    | cons _ _ _ fresh closed rootCheck typeTrace tailTrace =>
        exact ⟨fresh, closed, ⟨rootCheck⟩, ⟨typeTrace⟩, ⟨tailTrace⟩⟩
  · rintro ⟨fresh, closed, ⟨rootCheck⟩, ⟨typeTrace⟩, ⟨tailTrace⟩⟩
    exact ⟨.cons seen head tail fresh closed rootCheck typeTrace tailTrace⟩

/-- A duplicate at the current source position fails before all later
constructor phases, exactly as in the executable fold. -/
theorem not_nonempty_of_duplicate
    (duplicate : seen.contains head.name = true) :
    ¬ Nonempty (ConstructorListValidationTrace stats isUnsafe familyIdx
      context seen (head :: tail)) := by
  intro trace
  have fresh := (nonempty_cons_iff_exact_source.mp trace).1
  simp_all

/-- A closedness error at the current source position excludes the trace before
the root type check or constructor telescope is entered. -/
theorem not_nonempty_of_closedness_error
    (failure : context.env.checkNoMVarNoFVar head.name head.type = .error err) :
    ¬ Nonempty (ConstructorListValidationTrace stats isUnsafe familyIdx
      context seen (head :: tail)) := by
  intro trace
  have closed := (nonempty_cons_iff_exact_source.mp trace).2.1
  rw [failure] at closed
  contradiction

/-- A closed-root `checkType` error excludes the trace at that exact source
constructor, before parameter and field validation. -/
theorem not_nonempty_of_root_error
    (failure : TypeChecker.M.run context.env context.safety {}
      context.lparams context.fuel (TypeChecker.checkType head.type) =
        .error err) :
    ¬ Nonempty (ConstructorListValidationTrace stats isUnsafe familyIdx
      context seen (head :: tail)) := by
  intro trace
  obtain ⟨rootCheck⟩ :=
    (nonempty_cons_iff_exact_source.mp trace).2.2.1
  have success := rootCheck.valid
  change TypeChecker.M.run context.withEmptyLocalContext.env
      context.withEmptyLocalContext.safety
      context.withEmptyLocalContext.lctx
      context.withEmptyLocalContext.lparams
      context.withEmptyLocalContext.fuel
      (TypeChecker.checkType head.type) = .ok rootCheck.inferred at success
  simp only [Context.withEmptyLocalContext] at success
  rw [failure] at success
  contradiction

/-- An inner parameter, field, universe, positivity, recursive-target, or
terminal-family error excludes the trace at the current constructor. -/
theorem not_nonempty_of_type_error
    (failure : checkConstructorType stats isUnsafe familyIdx
      head.name head.type context = .error err) :
    ¬ Nonempty (ConstructorListValidationTrace stats isUnsafe familyIdx
      context seen (head :: tail)) := by
  intro trace
  obtain ⟨typeTrace⟩ :=
    (nonempty_cons_iff_exact_source.mp trace).2.2.2.1
  have success := typeTrace.check_run
  rw [failure] at success
  contradiction

/-- Erasing an ordered trace replays the exact stateful constructor fold. -/
theorem fold_run
    (trace : ConstructorListValidationTrace stats isUnsafe familyIdx
      context seen ctors) :
    checkConstructorFold context.env stats isUnsafe familyIdx seen ctors context =
      .ok (finalSeen seen ctors) := by
  induction trace with
  | nil => rfl
  | cons seen head tail fresh closed rootCheck typeTrace tailTrace ih =>
      have hroot := rootCheck.valid
      change TypeChecker.M.run context.withEmptyLocalContext.env
          context.withEmptyLocalContext.safety
          context.withEmptyLocalContext.lctx
          context.withEmptyLocalContext.lparams
          context.withEmptyLocalContext.fuel
          (TypeChecker.checkType head.type) =
        .ok rootCheck.inferred at hroot
      simp only [Context.withEmptyLocalContext] at hroot
      unfold checkConstructorFold
      simp only
      rw [fresh]
      simp only [Bool.false_eq_true, if_false,
        ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
        Except.bind, Except.pure]
      rw [closed]
      simp only [ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
        Except.bind, Except.pure, liftExcept_apply]
      rw [withEmptyLocalContext_apply]
      rw [liftTypeChecker_apply]
      rw [hroot]
      simp only [Except.bind, readThe, MonadReaderOf.read, ReaderT.read,
        ReaderT.pure, Pure.pure, Except.pure]
      rw [typeTrace.check_run]
      change checkConstructorFold context.env stats isUnsafe familyIdx
        (seen.insert head.name) tail context =
          .ok (finalSeen (seen.insert head.name) tail)
      exact ih

/-- Any successful stateful constructor fold decomposes into the complete
source-ordered list trace; the final accumulator value itself is irrelevant. -/
theorem exists_of_fold_run
    (success : checkConstructorFold context.env stats isUnsafe familyIdx
      seen ctors context = .ok result) :
    Nonempty (ConstructorListValidationTrace stats isUnsafe familyIdx
      context seen ctors) := by
  induction ctors generalizing seen result with
  | nil => exact ⟨.nil seen⟩
  | cons head tail ih =>
      unfold checkConstructorFold at success
      simp only at success
      cases hfresh : seen.contains head.name with
      | true =>
          rw [hfresh] at success
          change Except.error _ = Except.ok result at success
          contradiction
      | false =>
          rw [hfresh] at success
          simp only [Bool.false_eq_true, if_false,
            ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
            Except.bind, Except.pure] at success
          cases hclosed : context.env.checkNoMVarNoFVar
              head.name head.type with
          | error err => simp_all [liftExcept_apply, Except.bind]
          | ok closedResult =>
              cases closedResult
              rw [hclosed] at success
              simp only [liftExcept_apply, Except.bind] at success
              rw [withEmptyLocalContext_apply, liftTypeChecker_apply] at success
              cases hroot : TypeChecker.M.run context.env context.safety {}
                  context.lparams context.fuel
                  (TypeChecker.checkType head.type) with
              | error err => simp_all [Except.bind]
              | ok inferred =>
                  rw [hroot] at success
                  simp only [Except.bind] at success
                  cases htype : checkConstructorType stats isUnsafe familyIdx
                      head.name head.type context with
                  | error err => simp_all [Except.bind]
                  | ok typeResult =>
                      cases typeResult
                      rw [htype] at success
                      simp only [Except.bind, ReaderT.pure, Pure.pure,
                        Except.pure] at success
                      have htypeLoop :
                          checkConstructorType.loop stats isUnsafe familyIdx
                              head.name head.type 0 context.fuel.inductiveFuel
                              context = .ok () := by
                        unfold checkConstructorType at htype
                        simpa only [readThe, MonadReaderOf.read, ReaderT.read,
                          ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
                          Except.bind, Except.pure] using htype
                      obtain ⟨typeTrace⟩ :=
                        ConstructorTypeValidationTrace.exists_of_run htypeLoop
                      have rootCheck : CandidateCheckTypeObservation
                          context.withEmptyLocalContext head.type :=
                        ⟨inferred, by
                          simpa only [CandidateCheckTypeStep.Valid,
                            Context.withEmptyLocalContext] using hroot⟩
                      change checkConstructorFold context.env stats isUnsafe
                        familyIdx (seen.insert head.name) tail context =
                          .ok result at success
                      obtain ⟨tailTrace⟩ := ih success
                      exact ⟨.cons seen head tail hfresh hclosed rootCheck
                        typeTrace tailTrace⟩

/-- The transparent list decomposition succeeds on every constructor list
accepted by the executable stateful fold. -/
theorem buildExecution_ok_of_fold_run
    (success : checkConstructorFold context.env stats isUnsafe familyIdx
      seen ctors context = .ok result) :
    ∃ trace, buildExecution stats isUnsafe familyIdx context seen ctors =
      .ok trace := by
  induction ctors generalizing seen result with
  | nil => exact ⟨_, rfl⟩
  | cons head tail ih =>
      unfold checkConstructorFold at success
      simp only at success
      unfold buildExecution
      split
      next hfresh =>
        rw [hfresh] at success
        change Except.error _ = Except.ok result at success
        contradiction
      next hfresh =>
        rw [hfresh] at success
        simp only [Bool.false_eq_true, if_false,
          ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
          Except.bind, Except.pure] at success
        split
        next error heq =>
          rw [heq] at success
          simp [liftExcept_apply, Except.bind] at success
        next heq =>
          rw [heq] at success
          simp only [liftExcept_apply, Except.bind] at success
          rw [withEmptyLocalContext_apply, liftTypeChecker_apply] at success
          split
          next error heq2 =>
            rw [heq2] at success
            simp [Except.bind] at success
          next inferred heq2 =>
            rw [heq2] at success
            simp only [Except.bind] at success
            cases htype : checkConstructorType stats isUnsafe familyIdx
                head.name head.type context with
            | error err => simp_all [Except.bind]
            | ok typeResult =>
                cases typeResult
                rw [htype] at success
                simp only [Except.bind, ReaderT.pure, Pure.pure,
                  Except.pure] at success
                have htypeLoop :
                    checkConstructorType.loop stats isUnsafe familyIdx
                        head.name head.type 0 context.fuel.inductiveFuel
                        context = .ok () := by
                  unfold checkConstructorType at htype
                  simpa only [readThe, MonadReaderOf.read, ReaderT.read,
                    ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
                    Except.bind, Except.pure] using htype
                obtain ⟨typeTrace, hT⟩ :=
                  ConstructorTypeValidationTrace.buildExecution_ok_of_run
                    htypeLoop
                rw [hT]
                change checkConstructorFold context.env stats isUnsafe
                  familyIdx (seen.insert head.name) tail context =
                    .ok result at success
                obtain ⟨tailTrace, htl⟩ := ih success
                rw [htl]
                exact ⟨_, rfl⟩

/-- The stateful list fold's exact error value excludes a complete trace for
that same source list and incoming duplicate-name accumulator. -/
theorem not_nonempty_of_fold_error
    (failure : checkConstructorFold context.env stats isUnsafe familyIdx
      seen ctors context = .error err) :
    ¬ Nonempty (ConstructorListValidationTrace stats isUnsafe familyIdx
      context seen ctors) := by
  rintro ⟨trace⟩
  have success := trace.fold_run
  rw [failure] at success
  contradiction

/-- Erasing an ordered list trace replays the transparent list validator. -/
theorem run
    (trace : ConstructorListValidationTrace stats isUnsafe familyIdx
      context seen ctors) :
    checkConstructorList stats isUnsafe familyIdx context seen ctors = .ok () := by
  unfold checkConstructorList
  rw [trace.fold_run]
  rfl

end ConstructorListValidationTrace

/-! ## Arbitrary mutual-block validation owners -/

/-- Exact successful traversal of one family-type telescope, retaining the
definitional-equality checks by which every later mutual family reuses the
first family's parameter declarations.

The trace deliberately records kernel equality executions rather than
syntactic domain equalities.  Its indices pin every comparison to the actual
source expression, statistics, reader context, counters, and remaining fuel
seen by `checkInductiveTypes.loopInd.loop`; a later semantic canonicalizer can
therefore translate these checks without strengthening what the kernel
accepted. -/
inductive FamilyTypeParameterComparisonTrace (nparams : Nat) :
    (stats : InductiveStats) → (context : Context) → (source : Expr) →
      (i nindices fuel : Nat) → Type where
  | freshParameter
      (stats : InductiveStats) (context : Context)
      (i nindices fuel : Nat)
      (name : Name) (domain body view : Expr) (binderInfo : BinderInfo)
      (isParameter : i < nparams)
      (firstFamily : stats.indConsts.isEmpty = true)
      (whnf : CandidateWhnfStep.Valid
        ⟨context.pushLocalDecl name binderInfo
            (consumeTypeAnnotations domain),
          body.instantiate1 context.freshExpr, view⟩)
      (tail : FamilyTypeParameterComparisonTrace nparams
        { stats with params := stats.params.push context.freshExpr }
        (context.pushLocalDecl name binderInfo
          (consumeTypeAnnotations domain))
        view (i + 1) nindices fuel) :
      FamilyTypeParameterComparisonTrace nparams stats context
        (.forallE name domain body binderInfo) i nindices (fuel + 1)
  | sharedParameter
      (stats : InductiveStats) (context : Context)
      (i nindices fuel : Nat)
      (name : Name) (domain body parameterType view : Expr)
      (binderInfo : BinderInfo)
      (isParameter : i < nparams)
      (laterFamily : stats.indConsts.isEmpty = false)
      (parameterTypeRun : getType stats.params[i]! context =
        .ok parameterType)
      (defeq : CandidateIsDefEqStep.Valid
        ⟨context, domain, parameterType⟩)
      (whnf : CandidateWhnfStep.Valid
        ⟨context, body.instantiate1 stats.params[i]!, view⟩)
      (tail : FamilyTypeParameterComparisonTrace nparams stats context
        view (i + 1) nindices fuel) :
      FamilyTypeParameterComparisonTrace nparams stats context
        (.forallE name domain body binderInfo) i nindices (fuel + 1)
  | index
      (stats : InductiveStats) (context : Context)
      (i nindices fuel : Nat)
      (name : Name) (domain body view : Expr) (binderInfo : BinderInfo)
      (notParameter : ¬i < nparams)
      (whnf : CandidateWhnfStep.Valid
        ⟨context.pushLocalDecl name binderInfo
            (consumeTypeAnnotations domain),
          body.instantiate1 context.freshExpr, view⟩)
      (tail : FamilyTypeParameterComparisonTrace nparams stats
        (context.pushLocalDecl name binderInfo
          (consumeTypeAnnotations domain))
        view i (nindices + 1) fuel) :
      FamilyTypeParameterComparisonTrace nparams stats context
        (.forallE name domain body binderInfo) i nindices (fuel + 1)
  | terminal
      (stats : InductiveStats) (context : Context) (source : Expr)
      (i nindices fuel : Nat)
      (notForall : source.isForall = false)
      (parametersComplete : i = nparams) :
      FamilyTypeParameterComparisonTrace nparams stats context source
        i nindices (fuel + 1)

namespace FamilyTypeParameterComparisonTrace

/-- Exact continuation payload reached after erasing a family telescope
comparison trace. -/
structure Result where
  type : Expr
  stats : InductiveStats
  nindices : Nat
  context : Context

/-- Follow the retained telescope path to its exact continuation payload. -/
def result :
    FamilyTypeParameterComparisonTrace nparams stats context source
      i nindices fuel → Result
  | .freshParameter _ _ _ _ _ _ _ _ _ _ _ _ _ tail => tail.result
  | .sharedParameter _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tail =>
    tail.result
  | .index _ _ _ _ _ _ _ _ _ _ _ _ tail => tail.result
  | .terminal stats context source _ nindices _ _ _ =>
    { type := source, stats, nindices, context }

/-- Family-telescope traversal changes local declarations and the fresh-name
counter only; it preserves the checker fuel configuration at the exact
continuation context. -/
theorem result_context_fuel
    (trace : FamilyTypeParameterComparisonTrace nparams stats context source
      i nindices fuel) :
    trace.result.context.fuel = context.fuel := by
  induction trace with
  | freshParameter stats context i nindices fuel name domain body view
      binderInfo isParameter firstFamily whnf tail ih =>
    simpa [result, Context.pushLocalDecl] using ih
  | sharedParameter stats context i nindices fuel name domain body
      parameterType view binderInfo isParameter laterFamily parameterTypeRun
      defeq whnf tail ih =>
    exact ih
  | index stats context i nindices fuel name domain body view binderInfo
      notParameter whnf tail ih =>
    simpa [result, Context.pushLocalDecl] using ih
  | terminal => rfl

/-- Family-telescope traversal changes local declarations and the fresh-name
counter only; it preserves the checker safety mode at the exact continuation
context. -/
theorem result_context_safety
    (trace : FamilyTypeParameterComparisonTrace nparams stats context source
      i nindices fuel) :
    trace.result.context.safety = context.safety := by
  induction trace with
  | freshParameter stats context i nindices fuel name domain body view
      binderInfo isParameter firstFamily whnf tail ih =>
    simpa [result, Context.pushLocalDecl] using ih
  | sharedParameter stats context i nindices fuel name domain body
      parameterType view binderInfo isParameter laterFamily parameterTypeRun
      defeq whnf tail ih =>
    exact ih
  | index stats context i nindices fuel name domain body view binderInfo
      notParameter whnf tail ih =>
    simpa [result, Context.pushLocalDecl] using ih
  | terminal => rfl

/-- Traversing one family telescope never changes the already-accepted
family-constant inventory. -/
theorem result_indConsts_eq
    (trace : FamilyTypeParameterComparisonTrace nparams stats context source
      i nindices fuel) :
    trace.result.stats.indConsts = stats.indConsts := by
  induction trace with
  | freshParameter stats context i nindices fuel name domain body view
      binderInfo isParameter firstFamily whnf tail ih =>
      simpa only [result] using ih
  | sharedParameter stats context i nindices fuel name domain body
      parameterType view binderInfo isParameter laterFamily parameterTypeRun
      defeq whnf tail ih =>
      simpa only [result] using ih
  | index stats context i nindices fuel name domain body view binderInfo
      notParameter whnf tail ih =>
      simpa only [result] using ih
  | terminal => rfl

/-- The counter at the root of any successful family-telescope suffix has
not passed the declared parameter boundary.

Shared and fresh parameter nodes advance the counter only under their exact
`i < nparams` branch.  Index nodes leave it unchanged, while the terminal
node records equality with `nparams`. -/
theorem startIndex_le_nparams
    (trace : FamilyTypeParameterComparisonTrace nparams stats context source
      i nindices fuel) :
    i ≤ nparams := by
  induction trace with
  | freshParameter stats context i nindices fuel name domain body view
      binderInfo isParameter firstFamily whnf tail ih =>
    omega
  | sharedParameter stats context i nindices fuel name domain body
      parameterType view binderInfo isParameter laterFamily parameterTypeRun
      defeq whnf tail ih =>
    omega
  | index stats context i nindices fuel name domain body view binderInfo
      notParameter whnf tail ih =>
    exact ih
  | terminal stats context source i nindices fuel notForall
      parametersComplete =>
    omega

/-- The exact later-family parameter comparisons, in telescope order.  Fresh
first-family parameters and ordinary indices contribute no comparison. -/
def comparisons :
    FamilyTypeParameterComparisonTrace nparams stats context source
      i nindices fuel → List CandidateIsDefEqStep
  | .freshParameter _ _ _ _ _ _ _ _ _ _ _ _ _ tail => tail.comparisons
  | .sharedParameter _ context _ _ _ _ domain _ parameterType _ _ _ _ _ _
      _ tail =>
    { context, lhs := domain, rhs := parameterType } :: tail.comparisons
  | .index _ _ _ _ _ _ _ _ _ _ _ _ tail => tail.comparisons
  | .terminal .. => []

/-- Every comparison exposed by the family telescope trace is the exact
successful `TypeChecker.isDefEq` execution retained at that node. -/
theorem comparison_valid
    (trace : FamilyTypeParameterComparisonTrace nparams stats context source
      i nindices fuel)
    (member : step ∈ trace.comparisons) : step.Valid := by
  induction trace with
  | freshParameter stats context i nindices fuel name domain body view
      binderInfo isParameter firstFamily whnf tail ih =>
      exact ih member
  | sharedParameter stats context i nindices fuel name domain body
      parameterType view binderInfo isParameter laterFamily parameterTypeRun
      defeq whnf tail ih =>
      simp only [comparisons, List.mem_cons] at member
      rcases member with rfl | member
      · exact defeq
      · exact ih member
  | index stats context i nindices fuel name domain body view binderInfo
      notParameter whnf tail ih =>
      exact ih member
  | terminal => simp only [comparisons, List.not_mem_nil] at member

/-- A later mutual family contributes exactly one retained comparison for
each still-unconsumed shared parameter.  Once `i` reaches `nparams`, all
remaining binders are indices and contribute no comparison. -/
theorem comparisons_length_of_laterFamily
    (trace : FamilyTypeParameterComparisonTrace nparams stats context source
      i nindices fuel)
    (laterFamily : stats.indConsts.isEmpty = false) :
    trace.comparisons.length = nparams - i := by
  induction trace with
  | freshParameter stats context i nindices fuel name domain body view
      binderInfo isParameter firstFamily whnf tail ih =>
      rw [laterFamily] at firstFamily
      contradiction
  | sharedParameter stats context i nindices fuel name domain body
      parameterType view binderInfo isParameter laterFamily'
      parameterTypeRun defeq whnf tail ih =>
      simp only [comparisons, List.length_cons]
      rw [ih laterFamily]
      omega
  | index stats context i nindices fuel name domain body view binderInfo
      notParameter whnf tail ih =>
      simp only [comparisons]
      rw [ih laterFamily]
  | terminal stats context source i nindices fuel notForall
      parametersComplete =>
      simp [comparisons, parametersComplete]

/-- The first family creates shared parameters rather than comparing them,
so its retained equality inventory is empty. -/
theorem comparisons_eq_nil_of_firstFamily
    (trace : FamilyTypeParameterComparisonTrace nparams stats context source
      i nindices fuel)
    (firstFamily : stats.indConsts.isEmpty = true) :
    trace.comparisons = [] := by
  induction trace with
  | freshParameter stats context i nindices fuel name domain body view
      binderInfo isParameter firstFamily' whnf tail ih =>
      simp only [comparisons]
      apply ih
      simpa only using firstFamily
  | sharedParameter stats context i nindices fuel name domain body
      parameterType view binderInfo isParameter laterFamily parameterTypeRun
      defeq whnf tail ih =>
      rw [firstFamily] at laterFamily
      contradiction
  | index stats context i nindices fuel name domain body view binderInfo
      notParameter whnf tail ih =>
      exact ih firstFamily
  | terminal => rfl

/-- Erasing a comparison trace factors the executable family telescope
through the exact continuation payload selected by that trace. -/
theorem factor
    (trace : FamilyTypeParameterComparisonTrace nparams stats context source
      i nindices fuel)
    (k : Expr → InductiveStats → Nat → M α) :
    checkInductiveTypes.loopInd.loop nparams stats source i nindices fuel k
        context =
      k trace.result.type trace.result.stats trace.result.nindices
        trace.result.context := by
  induction trace with
  | freshParameter stats context i nindices fuel name domain body view
      binderInfo isParameter firstFamily whnf tail ih =>
      simp only [checkInductiveTypes.loopInd.loop, isParameter, if_true,
        firstFamily, withLocalDecl_apply, ReaderT.bind, Bind.bind,
        liftTypeChecker_apply]
      rw [whnf]
      simp only [Except.bind, result]
      exact ih
  | sharedParameter stats context i nindices fuel name domain body
      parameterType view binderInfo isParameter laterFamily parameterTypeRun
      defeq whnf tail ih =>
      simp only [checkInductiveTypes.loopInd.loop, isParameter, if_true,
        laterFamily, Bool.false_eq_true, if_false, ReaderT.bind, Bind.bind,
        liftTypeChecker_apply]
      rw [parameterTypeRun]
      simp only [Except.bind]
      rw [defeq]
      simp only [if_true, ReaderT.pure, Pure.pure, Except.pure,
        ReaderT.bind, Bind.bind, Except.bind, liftTypeChecker_apply]
      rw [whnf]
      simp only [Except.bind, result]
      exact ih
  | index stats context i nindices fuel name domain body view binderInfo
      notParameter whnf tail ih =>
      simp only [checkInductiveTypes.loopInd.loop, notParameter, if_false,
        withLocalDecl_apply, ReaderT.bind, Bind.bind, liftTypeChecker_apply]
      rw [whnf]
      simp only [Except.bind, result]
      exact ih
  | terminal stats context source i nindices fuel notForall
      parametersComplete =>
      cases source <;> cases notForall <;>
        simp_all [checkInductiveTypes.loopInd.loop, result, Expr.isForall,
          ReaderT.bind, Bind.bind, Except.bind, throw, throwThe,
          MonadExceptOf.throw]

/-- A retained first-family telescope and the independently retained
normalization candidate reach the same terminal payload when they start from
the same root and replay the same fresh-parameter/index split.

Both proofs factor the unchanged executable loop.  Choosing the continuation
to return every argument therefore identifies the terminal type, statistics,
index count, and reader context at once; no reconstruction from local names is
needed. -/
theorem result_eq_candidate
    (candidate : CandidateExprTrace context candidateSource)
    (trace : FamilyTypeParameterComparisonTrace nparams stats context
      candidate.rootWhnf i nindices fuel)
    (remaining : Nat)
    (hi : i + remaining = nparams)
    (hcount : remaining ≤ candidate.spineLength)
    (hfuel : candidate.spineLength < fuel)
    (hempty : stats.indConsts.isEmpty = true)
    (hannotations : candidate.validationAnnotations)
    (hterminal : candidate.terminalResult.isForall = false) :
    trace.result = {
      type := candidate.terminalResult
      stats := { stats with
        params := stats.params ++
          (candidate.parameterList remaining).toArray }
      nindices := nindices + (candidate.spineLength - remaining)
      context := candidate.terminalContext } := by
  let k : Expr → InductiveStats → Nat → M Result :=
    fun type stats nindices => fun context =>
      .ok { type, stats, nindices, context }
  have factor := trace.factor k
  have replay := candidate.checkInductiveTypes_loop_of_candidate
    stats nparams i nindices fuel remaining k hi hcount hfuel hempty
      hannotations hterminal
  rw [replay] at factor
  exact (Except.ok.inj factor).symm

/-- Every successful executable family-telescope traversal determines the
source-indexed comparison trace above.  The continuation result is used only
to rule out failed branches; it is not stored as an independently selectable
premise. -/
theorem exists_of_run
    (success : checkInductiveTypes.loopInd.loop nparams stats source
      i nindices fuel k context = .ok output) :
    Nonempty (FamilyTypeParameterComparisonTrace nparams stats context source
      i nindices fuel) := by
  induction fuel generalizing stats context source i nindices with
  | zero =>
      simp [checkInductiveTypes.loopInd.loop] at success
  | succ fuel ih =>
      cases source
      case forallE name domain body binderInfo =>
        simp only [checkInductiveTypes.loopInd.loop] at success
        by_cases isParameter : i < nparams
        · simp only [isParameter, if_true] at success
          cases firstFamily : stats.indConsts.isEmpty with
          | true =>
              simp only [firstFamily, if_true, withLocalDecl_apply,
                ReaderT.bind, Bind.bind, liftTypeChecker_apply] at success
              let nextContext := context.pushLocalDecl name binderInfo
                (consumeTypeAnnotations domain)
              cases hwhnf : TypeChecker.M.run nextContext.env
                  nextContext.safety nextContext.lctx nextContext.lparams
                  nextContext.fuel
                  (TypeChecker.whnf
                    (body.instantiate1 context.freshExpr)) with
              | error error =>
                  rw [hwhnf] at success
                  cases success
              | ok view =>
                  rw [hwhnf] at success
                  simp only [Except.bind] at success
                  obtain ⟨tail⟩ := ih success
                  exact ⟨.freshParameter stats context i nindices fuel name
                    domain body view binderInfo isParameter firstFamily
                    hwhnf tail⟩
          | false =>
              simp only [firstFamily, Bool.false_eq_true, if_false,
                ReaderT.bind, Bind.bind, liftTypeChecker_apply] at success
              cases parameterTypeRun : getType stats.params[i]! context with
              | error error =>
                  rw [parameterTypeRun] at success
                  cases success
              | ok parameterType =>
                  rw [parameterTypeRun] at success
                  simp only [Except.bind] at success
                  cases defeq : TypeChecker.M.run context.env context.safety
                      context.lctx context.lparams context.fuel
                      (TypeChecker.isDefEq domain parameterType) with
                  | error error =>
                      rw [defeq] at success
                      cases success
                  | ok equal =>
                      rw [defeq] at success
                      simp only [Except.bind] at success
                      cases equal
                      · simp [ReaderT.bind, Bind.bind, liftExcept_apply,
                          Except.bind, throw, throwThe,
                          MonadExceptOf.throw] at success
                      · simp only [if_true] at success
                        cases hwhnf : TypeChecker.M.run context.env
                            context.safety context.lctx context.lparams
                            context.fuel
                            (TypeChecker.whnf
                              (body.instantiate1 stats.params[i]!)) with
                        | error error =>
                            simp only [ReaderT.bind, Bind.bind,
                              liftTypeChecker_apply] at success
                            rw [hwhnf] at success
                            cases success
                        | ok view =>
                            simp only [ReaderT.bind, Bind.bind,
                              liftTypeChecker_apply] at success
                            rw [hwhnf] at success
                            simp only [Except.bind] at success
                            obtain ⟨tail⟩ := ih success
                            exact ⟨.sharedParameter stats context i nindices
                              fuel name domain body parameterType view
                              binderInfo isParameter firstFamily
                              parameterTypeRun defeq hwhnf tail⟩
        · simp only [isParameter, if_false, withLocalDecl_apply,
            ReaderT.bind, Bind.bind, liftTypeChecker_apply] at success
          let nextContext := context.pushLocalDecl name binderInfo
            (consumeTypeAnnotations domain)
          cases hwhnf : TypeChecker.M.run nextContext.env nextContext.safety
              nextContext.lctx nextContext.lparams nextContext.fuel
              (TypeChecker.whnf
                (body.instantiate1 context.freshExpr)) with
          | error error =>
              rw [hwhnf] at success
              cases success
          | ok view =>
              rw [hwhnf] at success
              simp only [Except.bind] at success
              obtain ⟨tail⟩ := ih success
              exact ⟨.index stats context i nindices fuel name domain body
                view binderInfo isParameter hwhnf tail⟩
      all_goals
        simp only [checkInductiveTypes.loopInd.loop] at success
        by_cases parametersComplete : i = nparams
        · exact ⟨.terminal stats context _ i nindices fuel rfl
            parametersComplete⟩
        · simp [parametersComplete, ReaderT.bind, Bind.bind, Except.bind,
            throw, throwThe, MonadExceptOf.throw] at success

end FamilyTypeParameterComparisonTrace

/-- The exact result selected when the ordinary family validator reaches its
continuation.  Retaining the reader context matters: later constructor
validation uses the shared parameters and local declarations installed by
that very run. -/
structure FamilyValidationBlockResult where
  stats : InductiveStats
  validationContext : Context

/-- Observe the successful continuation of `checkInductiveTypes` without
changing any validation branch or error. -/
def observeFamilyValidationBlock (nparams : Nat)
    (indTypes : List InductiveType) (context : Context) :
    Except Exception FamilyValidationBlockResult :=
  checkInductiveTypes nparams indTypes.toArray
    (fun stats => fun validationContext =>
      .ok ⟨stats, validationContext⟩) context

/-- One exact successful `ensureSort` execution at the end of a family
telescope. -/
structure FamilyEnsureSortStep where
  context : Context
  source : Expr
  result : Expr

def FamilyEnsureSortStep.Valid (step : FamilyEnsureSortStep) : Prop :=
  TypeChecker.M.run step.context.env step.context.safety
      step.context.lctx step.context.lparams step.context.fuel
      (TypeChecker.ensureSort step.source) =
    .ok step.result

/-- Recover the state-bearing checker execution erased by the family
validator's terminal `ensureSort` observation. -/
theorem FamilyEnsureSortStep.innerRun
    (step : FamilyEnsureSortStep) (hvalid : step.Valid) :
    ∃ state : TypeChecker.State,
      (TypeChecker.ensureSort step.source) step.context.toTypeChecker
          ({} : TypeChecker.State) = .ok (step.result, state) := by
  unfold FamilyEnsureSortStep.Valid TypeChecker.M.run at hvalid
  cases hrun : (TypeChecker.ensureSort step.source)
      { env := step.context.env
        lctx := step.context.lctx
        safety := step.context.safety
        lparams := step.context.lparams
        fuel := step.context.fuel }
      ({} : TypeChecker.State) with
  | error err =>
      simp [StateT.run', Functor.map, Except.map, hrun] at hvalid
  | ok pair =>
      rcases pair with ⟨result, state⟩
      have result_eq : result = step.result := by
        simpa [StateT.run', Functor.map, Except.map, hrun] using hvalid
      subst result
      exact ⟨state, by simpa [Context.toTypeChecker] using hrun⟩

/-- The exact statistics value passed to the outer family-validation
continuation.  Keeping the nested assertions in this transparent helper
preserves even the executable's inhabited fallback behavior for an empty
block. -/
def familyValidationTerminalStats (nparams : Nat)
    (indTypes : Array InductiveType) (stats : InductiveStats)
    (context : Context) : InductiveStats :=
  assert! stats.levels.length == context.lparams.length
  assert! stats.nindices.size == indTypes.size
  assert! stats.indConsts.size == indTypes.size
  assert! stats.params.size == nparams
  stats

/-- Exact source-indexed traversal of the outer mutual-family validator.

Each family node retains the source closure and ordinary checker executions,
the complete inner parameter-comparison trace, the terminal sort check, and
the precise first/later-family statistics update.  The tail is indexed by
that exact update and by the reader context returned from the inner trace, so
neither family order nor validation state can be supplied independently. -/
inductive FamilyParameterComparisonBlockTrace (nparams : Nat)
    (indTypes : Array InductiveType) :
    (dIdx : Nat) → (stats : InductiveStats) → (context : Context) → Type where
  | firstFamily
      (dIdx : Nat) (stats : InductiveStats) (context : Context)
      (inBounds : dIdx < indTypes.size)
      (closed : context.env.checkNoMVarNoFVar indTypes[dIdx].name
        indTypes[dIdx].type = .ok ())
      (inferred root : Expr)
      (checkType : CandidateCheckTypeStep.Valid
        ⟨context, indTypes[dIdx].type, inferred⟩)
      (rootWhnf : CandidateWhnfStep.Valid
        ⟨context, indTypes[dIdx].type, root⟩)
      (telescope : FamilyTypeParameterComparisonTrace nparams stats context
        root 0 0 context.fuel.inductiveFuel)
      (sorted : Expr)
      (ensureSort : FamilyEnsureSortStep.Valid
        ⟨telescope.result.context, telescope.result.type, sorted⟩)
      (isFirst : telescope.result.stats.indConsts.isEmpty = true)
      (tail : FamilyParameterComparisonBlockTrace nparams indTypes
        (dIdx + 1)
        { telescope.result.stats with
          lctx := telescope.result.context.lctx
          resultLevel := sorted.sortLevel!
          isNotZero := sorted.sortLevel!.isNeverZero
          nindices := telescope.result.stats.nindices.push
            telescope.result.nindices
          indConsts := telescope.result.stats.indConsts.push
            (.const indTypes[dIdx].name telescope.result.stats.levels) }
        telescope.result.context) :
      FamilyParameterComparisonBlockTrace nparams indTypes dIdx stats context
  | laterFamily
      (dIdx : Nat) (stats : InductiveStats) (context : Context)
      (inBounds : dIdx < indTypes.size)
      (closed : context.env.checkNoMVarNoFVar indTypes[dIdx].name
        indTypes[dIdx].type = .ok ())
      (inferred root : Expr)
      (checkType : CandidateCheckTypeStep.Valid
        ⟨context, indTypes[dIdx].type, inferred⟩)
      (rootWhnf : CandidateWhnfStep.Valid
        ⟨context, indTypes[dIdx].type, root⟩)
      (telescope : FamilyTypeParameterComparisonTrace nparams stats context
        root 0 0 context.fuel.inductiveFuel)
      (sorted : Expr)
      (ensureSort : FamilyEnsureSortStep.Valid
        ⟨telescope.result.context, telescope.result.type, sorted⟩)
      (isLater : telescope.result.stats.indConsts.isEmpty = false)
      (resultLevelCompatible :
        (!sorted.sortLevel!.isEquiv
          telescope.result.stats.resultLevel) = false)
      (tail : FamilyParameterComparisonBlockTrace nparams indTypes
        (dIdx + 1)
        { telescope.result.stats with
          nindices := telescope.result.stats.nindices.push
            telescope.result.nindices
          indConsts := telescope.result.stats.indConsts.push
            (.const indTypes[dIdx].name telescope.result.stats.levels) }
        telescope.result.context) :
      FamilyParameterComparisonBlockTrace nparams indTypes dIdx stats context
  | terminal
      (dIdx : Nat) (stats : InductiveStats) (context : Context)
      (outOfBounds : ¬dIdx < indTypes.size) :
      FamilyParameterComparisonBlockTrace nparams indTypes dIdx stats context

namespace FamilyParameterComparisonBlockTrace

/-- Exact continuation payload reached after erasing the outer trace. -/
def result :
    FamilyParameterComparisonBlockTrace nparams indTypes dIdx stats context →
      FamilyValidationBlockResult
  | .firstFamily _ _ _ _ _ _ _ _ _ _ _ _ _ tail => tail.result
  | .laterFamily _ _ _ _ _ _ _ _ _ _ _ _ _ _ tail => tail.result
  | .terminal _ stats context _ =>
    { stats := familyValidationTerminalStats nparams indTypes stats context
      validationContext := context }

/-- Outer family validation extends local state only; the terminal reader
context retained by its result keeps the caller's checker safety mode. -/
theorem result_safety
    (trace : FamilyParameterComparisonBlockTrace nparams indTypes dIdx stats
      context) :
    trace.result.validationContext.safety = context.safety := by
  induction trace with
  | firstFamily dIdx stats context inBounds closed inferred root checkType
      rootWhnf telescope sorted ensureSort isFirst tail ih =>
    exact (show _ = telescope.result.context.safety from ih).trans
      telescope.result_context_safety
  | laterFamily dIdx stats context inBounds closed inferred root checkType
      rootWhnf telescope sorted ensureSort isLater resultLevelCompatible
      tail ih =>
    exact (show _ = telescope.result.context.safety from ih).trans
      telescope.result_context_safety
  | terminal dIdx stats context outOfBounds => rfl

/-- Outer family validation also preserves the checker fuel configuration in
its terminal reader context. -/
theorem result_fuel
    (trace : FamilyParameterComparisonBlockTrace nparams indTypes dIdx stats
      context) :
    trace.result.validationContext.fuel = context.fuel := by
  induction trace with
  | firstFamily dIdx stats context inBounds closed inferred root checkType
      rootWhnf telescope sorted ensureSort isFirst tail ih =>
    exact (show _ = telescope.result.context.fuel from ih).trans
      telescope.result_context_fuel
  | laterFamily dIdx stats context inBounds closed inferred root checkType
      rootWhnf telescope sorted ensureSort isLater resultLevelCompatible
      tail ih =>
    exact (show _ = telescope.result.context.fuel from ih).trans
      telescope.result_context_fuel
  | terminal dIdx stats context outOfBounds => rfl

/-- Reader context reached after the current family's complete telescope.

For an initial nonempty block this is the first-family terminal context.  The
later-family and terminal clauses keep the projection total for recursive
consumers; producer theorems rule those clauses out at the initial index. -/
def firstContext :
    FamilyParameterComparisonBlockTrace nparams indTypes dIdx stats context →
      Context
  | .firstFamily _ _ _ _ _ _ _ _ _ telescope _ _ _ _ =>
    telescope.result.context
  | .laterFamily _ _ _ _ _ _ _ _ _ telescope _ _ _ _ _ =>
    telescope.result.context
  | .terminal _ _ context _ => context

/-- Fully indexed payload for one family telescope selected from the outer
source traversal. -/
structure FamilyTelescopePosition (nparams : Nat) where
  stats : InductiveStats
  context : Context
  source : Expr
  i : Nat
  nindices : Nat
  fuel : Nat
  trace : FamilyTypeParameterComparisonTrace nparams stats context source
    i nindices fuel

/-- Select the exact telescope at the head of an outer-trace suffix. -/
def headTelescope? :
    FamilyParameterComparisonBlockTrace nparams indTypes dIdx stats context →
      Option (FamilyTelescopePosition nparams)
  | .firstFamily _ _ _ _ _ _ _ _ _ telescope _ _ _ _ =>
    some ⟨_, _, _, _, _, _, telescope⟩
  | .laterFamily _ _ _ _ _ _ _ _ _ telescope _ _ _ _ _ =>
    some ⟨_, _, _, _, _, _, telescope⟩
  | .terminal .. => none

/-- Select the exact second family telescope, if the retained source suffix
contains two family nodes.  The value is computed from the dependent outer
trace; consumers cannot reselect a telescope by matching only its counters or
comparison list. -/
def secondTelescope? :
    FamilyParameterComparisonBlockTrace nparams indTypes dIdx stats context →
      Option (FamilyTelescopePosition nparams)
  | .firstFamily _ _ _ _ _ _ _ _ _ _ _ _ _ tail => tail.headTelescope?
  | .laterFamily _ _ _ _ _ _ _ _ _ _ _ _ _ _ tail => tail.headTelescope?
  | .terminal .. => none

/-- Exact kernel parameter-comparison executions, grouped in source family
order.  The first family normally contributes an empty list; every later
family contributes one entry for each shared parameter. -/
def comparisons :
    FamilyParameterComparisonBlockTrace nparams indTypes dIdx stats context →
      List (List CandidateIsDefEqStep)
  | .firstFamily _ _ _ _ _ _ _ _ _ telescope _ _ _ tail =>
    telescope.comparisons :: tail.comparisons
  | .laterFamily _ _ _ _ _ _ _ _ _ telescope _ _ _ _ tail =>
    telescope.comparisons :: tail.comparisons
  | .terminal .. => []

/-- Every equality step exposed by the outer source-indexed trace is an exact
successful checker execution retained by its family's inner trace. -/
theorem comparison_valid
    (trace : FamilyParameterComparisonBlockTrace nparams indTypes dIdx stats
      context)
    (familyMember : familyComparisons ∈ trace.comparisons)
    (comparisonMember : comparison ∈ familyComparisons) :
    comparison.Valid := by
  induction trace with
  | firstFamily dIdx stats context inBounds closed inferred root checkType
      rootWhnf telescope sorted ensureSort isFirst tail ih =>
      simp only [comparisons, List.mem_cons] at familyMember
      rcases familyMember with rfl | familyMember
      · exact telescope.comparison_valid comparisonMember
      · exact ih familyMember
  | laterFamily dIdx stats context inBounds closed inferred root checkType
      rootWhnf telescope sorted ensureSort isLater resultLevelCompatible tail
      ih =>
      simp only [comparisons, List.mem_cons] at familyMember
      rcases familyMember with rfl | familyMember
      · exact telescope.comparison_valid comparisonMember
      · exact ih familyMember
  | terminal => simp only [comparisons, List.not_mem_nil] at familyMember

/-- The grouped comparison inventory has exactly one entry for each
remaining source family. -/
theorem comparisons_length
    (trace : FamilyParameterComparisonBlockTrace nparams indTypes dIdx stats
      context) :
    trace.comparisons.length = indTypes.size - dIdx := by
  induction trace with
  | firstFamily dIdx stats context inBounds closed inferred root checkType
      rootWhnf telescope sorted ensureSort isFirst tail ih =>
      simp only [comparisons, List.length_cons]
      rw [ih]
      omega
  | laterFamily dIdx stats context inBounds closed inferred root checkType
      rootWhnf telescope sorted ensureSort isLater resultLevelCompatible tail
      ih =>
      simp only [comparisons, List.length_cons]
      rw [ih]
      omega
  | terminal dIdx stats context outOfBounds =>
      simp only [comparisons, List.length_nil]
      omega

/-- Once a family has been accepted, every remaining source family compares
exactly all `nparams` shared parameters. -/
theorem comparison_lengths_of_later
    (trace : FamilyParameterComparisonBlockTrace nparams indTypes dIdx stats
      context)
    (later : stats.indConsts.isEmpty = false) :
    trace.comparisons.map List.length =
      List.replicate (indTypes.size - dIdx) nparams := by
  induction trace with
  | firstFamily dIdx stats context inBounds closed inferred root checkType
      rootWhnf telescope sorted ensureSort isFirst tail ih =>
      have preserved := telescope.result_indConsts_eq
      have resultLater : telescope.result.stats.indConsts.isEmpty = false := by
        rw [preserved, later]
      rw [resultLater] at isFirst
      contradiction
  | laterFamily dIdx stats context inBounds closed inferred root checkType
      rootWhnf telescope sorted ensureSort isLater resultLevelCompatible tail
      ih =>
      have headLength :=
        telescope.comparisons_length_of_laterFamily later
      have tailLater :
          (telescope.result.stats.indConsts.push
            (.const indTypes[dIdx].name
              telescope.result.stats.levels)).isEmpty = false := by
        simp
      simp only [comparisons, List.map_cons]
      rw [headLength, ih tailLater]
      simp only [Nat.sub_zero]
      have remaining :
          indTypes.size - dIdx =
            (indTypes.size - (dIdx + 1)) + 1 := by
        omega
      rw [remaining]
      rw [show indTypes.size - (dIdx + 1) + 1 =
        Nat.succ (indTypes.size - (dIdx + 1)) by omega]
      rw [List.replicate_succ]
  | terminal dIdx stats context outOfBounds =>
      have remaining : indTypes.size - dIdx = 0 := by omega
      simp [comparisons, remaining]

/-- From the validator's initial statistics, the first source family has no
comparisons and every later family has exactly `nparams` comparisons. -/
theorem comparison_lengths_of_initial
    (trace : FamilyParameterComparisonBlockTrace nparams indTypes 0
      (InductiveStats.initial (context.lparams.map .param)) context)
    (nonempty : 0 < indTypes.size) :
    trace.comparisons.map List.length =
      0 :: List.replicate (indTypes.size - 1) nparams := by
  cases trace with
  | firstFamily dIdx stats context inBounds closed inferred root checkType
      rootWhnf telescope sorted ensureSort isFirst tail =>
      have headEmpty :=
        telescope.comparisons_eq_nil_of_firstFamily (by rfl)
      have tailLater :
          (telescope.result.stats.indConsts.push
            (.const indTypes[0].name
              telescope.result.stats.levels)).isEmpty = false := by
        simp
      have tailLengths := tail.comparison_lengths_of_later tailLater
      simp only [comparisons, List.map_cons, headEmpty, List.length_nil]
      simpa using tailLengths
  | laterFamily dIdx stats context inBounds closed inferred root checkType
      rootWhnf telescope sorted ensureSort isLater resultLevelCompatible
      tail =>
      have preserved := telescope.result_indConsts_eq
      have resultFirst : telescope.result.stats.indConsts.isEmpty = true := by
        rw [preserved]
        rfl
      rw [resultFirst] at isLater
      contradiction
  | terminal dIdx stats context outOfBounds => omega

/-- Erasing the outer trace factors the unchanged mutual-family validator
through the exact terminal statistics and reader context selected by the
trace. -/
theorem factor
    (trace : FamilyParameterComparisonBlockTrace nparams indTypes dIdx stats
      context)
    (k : InductiveStats → M α) :
    checkInductiveTypes.loopInd nparams indTypes k dIdx stats context =
      k trace.result.stats trace.result.validationContext := by
  induction trace with
  | firstFamily dIdx stats context inBounds closed inferred root checkType
      rootWhnf telescope sorted ensureSort isFirst tail ih =>
      rw [checkInductiveTypes.loopInd.eq_1, dif_pos inBounds]
      simp only [ReaderT.bind, Bind.bind, liftTypeChecker_apply,
        readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
        ReaderT.pure, Pure.pure, Except.pure, liftExcept_apply,
        Except.bind]
      rw [closed, checkType, rootWhnf]
      simp only [Except.bind]
      rw [telescope.factor]
      simp only [ReaderT.bind, Bind.bind, liftTypeChecker_apply]
      rw [ensureSort]
      simp only [Except.bind, isFirst, if_true, ReaderT.pure, Pure.pure,
        Except.pure, result]
      exact ih
  | laterFamily dIdx stats context inBounds closed inferred root checkType
      rootWhnf telescope sorted ensureSort isLater resultLevelCompatible tail
      ih =>
      rw [checkInductiveTypes.loopInd.eq_1, dif_pos inBounds]
      simp only [ReaderT.bind, Bind.bind, liftTypeChecker_apply,
        readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
        ReaderT.pure, Pure.pure, Except.pure, liftExcept_apply,
        Except.bind]
      rw [closed, checkType, rootWhnf]
      simp only [Except.bind]
      rw [telescope.factor]
      simp only [ReaderT.bind, Bind.bind, liftTypeChecker_apply]
      rw [ensureSort]
      simp only [Except.bind, isLater, Bool.false_eq_true, if_false,
        resultLevelCompatible, result]
      exact ih
  | terminal dIdx stats context outOfBounds =>
      rw [checkInductiveTypes.loopInd.eq_1, dif_neg outOfBounds]
      rfl

/-- One-step decomposition used to keep reconstruction of the recursive
outer trace separate from inversion of the current executable branch. -/
private inductive Next
    (nparams : Nat) (indTypes : Array InductiveType)
    (dIdx : Nat) (stats : InductiveStats) (context : Context)
    (k : InductiveStats → M α) (output : α) : Type where
  | terminal
      (trace : FamilyParameterComparisonBlockTrace nparams indTypes dIdx
        stats context) :
      Next nparams indTypes dIdx stats context k output
  | step
      (inBounds : dIdx < indTypes.size)
      (nextStats : InductiveStats) (nextContext : Context)
      (success : checkInductiveTypes.loopInd nparams indTypes k (dIdx + 1)
        nextStats nextContext = .ok output)
      (prepend : FamilyParameterComparisonBlockTrace nparams indTypes
          (dIdx + 1) nextStats nextContext →
        FamilyParameterComparisonBlockTrace nparams indTypes dIdx stats
          context) :
      Next nparams indTypes dIdx stats context k output

/-- Invert exactly one successful outer-loop branch. -/
private theorem next_of_run
    (success : checkInductiveTypes.loopInd nparams indTypes k dIdx stats
      context = .ok output) :
    Nonempty (Next nparams indTypes dIdx stats context k output) := by
  rw [checkInductiveTypes.loopInd.eq_1] at success
  by_cases inBounds : dIdx < indTypes.size
  · rw [dif_pos inBounds] at success
    simp only [ReaderT.bind, Bind.bind, liftTypeChecker_apply,
      readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
      ReaderT.pure, Pure.pure, Except.pure, liftExcept_apply,
      Except.bind] at success
    cases hclosed : context.env.checkNoMVarNoFVar indTypes[dIdx].name
        indTypes[dIdx].type with
    | error error =>
        rw [hclosed] at success
        cases success
    | ok closedResult =>
      cases closedResult
      rw [hclosed] at success
      simp only [Except.bind] at success
      cases hcheck : TypeChecker.M.run context.env context.safety
          context.lctx context.lparams context.fuel
          (TypeChecker.checkType indTypes[dIdx].type) with
      | error error =>
          rw [hcheck] at success
          cases success
      | ok inferred =>
        rw [hcheck] at success
        simp only [Except.bind] at success
        cases hroot : TypeChecker.M.run context.env context.safety
            context.lctx context.lparams context.fuel
            (TypeChecker.whnf indTypes[dIdx].type) with
        | error error =>
            rw [hroot] at success
            cases success
        | ok root =>
          rw [hroot] at success
          simp only [Except.bind] at success
          obtain ⟨telescope⟩ :=
            FamilyTypeParameterComparisonTrace.exists_of_run success
          rw [telescope.factor] at success
          simp only [ReaderT.bind, Bind.bind,
            liftTypeChecker_apply] at success
          cases hsort : TypeChecker.M.run telescope.result.context.env
              telescope.result.context.safety
              telescope.result.context.lctx
              telescope.result.context.lparams
              telescope.result.context.fuel
              (TypeChecker.ensureSort telescope.result.type) with
          | error error =>
              rw [hsort] at success
              cases success
          | ok sorted =>
            rw [hsort] at success
            simp only [Except.bind] at success
            cases isFirst : telescope.result.stats.indConsts.isEmpty with
            | true =>
              rw [isFirst] at success
              simp only [if_true, ReaderT.bind, Bind.bind, ReaderT.pure,
                Pure.pure, Except.pure, Except.bind] at success
              exact ⟨Next.step inBounds _ _ success fun tail =>
                .firstFamily dIdx stats context inBounds hclosed inferred
                  root hcheck hroot telescope sorted hsort isFirst tail⟩
            | false =>
              rw [isFirst] at success
              simp only [Bool.false_eq_true, if_false] at success
              cases levelMismatch :
                  (!sorted.sortLevel!.isEquiv
                    telescope.result.stats.resultLevel) with
              | true =>
                rw [levelMismatch] at success
                simp [ReaderT.bind, Bind.bind, liftExcept_apply,
                  Except.bind, throw, throwThe,
                  MonadExceptOf.throw] at success
              | false =>
                rw [levelMismatch] at success
                simp only [Bool.false_eq_true, if_false] at success
                exact ⟨Next.step inBounds _ _ success fun tail =>
                  .laterFamily dIdx stats context inBounds hclosed inferred
                    root hcheck hroot telescope sorted hsort isFirst
                    levelMismatch tail⟩
  · exact ⟨Next.terminal (.terminal dIdx stats context inBounds)⟩

/-- Every successful suffix of the executable outer family loop reconstructs
the exact source-indexed trace above.  No counter invariant is needed here:
the terminal node records the executable assertion result itself. -/
theorem exists_of_run
    (success : checkInductiveTypes.loopInd nparams indTypes k dIdx stats
      context = .ok output) :
    Nonempty (FamilyParameterComparisonBlockTrace nparams indTypes dIdx stats
      context) := by
  obtain ⟨next⟩ := next_of_run success
  cases next with
  | terminal trace => exact ⟨trace⟩
  | step inBounds nextStats nextContext tailSuccess prepend =>
      obtain ⟨tail⟩ := exists_of_run tailSuccess
      exact ⟨prepend tail⟩
termination_by indTypes.size - dIdx
decreasing_by
  all_goals exact Nat.sub_lt_sub_left inBounds (Nat.lt_succ_self dIdx)

end FamilyParameterComparisonBlockTrace

/-- Terminal data selected by the inner family-telescope loop.  The reader
context is part of the result because `withLocalDecl` changes the context seen
by its continuation. -/
private structure FamilyValidationTelescopeResult where
  type : Expr
  stats : InductiveStats
  nindices : Nat
  context : Context

/-- Run the ordinary inner telescope loop with a continuation which records
all data supplied at its exact continuation boundary. -/
private def observeFamilyValidationTelescope (nparams : Nat)
    (stats : InductiveStats) (type : Expr) (i nindices fuel : Nat)
    (context : Context) :
    Except Exception FamilyValidationTelescopeResult :=
  checkInductiveTypes.loopInd.loop nparams stats type i nindices fuel
    (fun type stats nindices => fun context =>
      .ok { type, stats, nindices, context }) context

/-- Every continuation of the inner family-telescope validator factors
through the exact terminal expression, statistics, index count, and reader
context selected by that same execution. -/
private theorem checkInductiveTypes_telescope_factor
    (nparams : Nat) (stats : InductiveStats) (type : Expr)
    (i nindices fuel : Nat) (k : Expr → InductiveStats → Nat → M α)
    (context : Context) :
    checkInductiveTypes.loopInd.loop nparams stats type i nindices fuel k
        context =
      (observeFamilyValidationTelescope nparams stats type i nindices fuel
        context >>= fun result =>
          k result.type result.stats result.nindices result.context) := by
  induction fuel generalizing stats type i nindices context with
  | zero => rfl
  | succ fuel ih =>
      cases type
      case forallE name dom body bi =>
        simp only [observeFamilyValidationTelescope,
          checkInductiveTypes.loopInd.loop]
        by_cases hi : i < nparams
        · simp only [hi, if_true]
          by_cases hempty : stats.indConsts = #[]
          · simp only [hempty, Array.isEmpty_empty, if_true,
              withLocalDecl_apply, ReaderT.bind, Bind.bind,
              liftTypeChecker_apply]
            let nextContext := context.pushLocalDecl name bi
              (consumeTypeAnnotations dom)
            cases hwhnf : TypeChecker.M.run nextContext.env
                nextContext.safety nextContext.lctx nextContext.lparams
                nextContext.fuel
                (TypeChecker.whnf (body.instantiate1 context.freshExpr)) with
            | error error => rfl
            | ok view =>
                simpa only [observeFamilyValidationTelescope, nextContext,
                  hempty, Bind.bind, Except.bind] using
                  ih { stats with params :=
                    stats.params.push context.freshExpr }
                    view (i + 1) nindices nextContext
          · have hempty' : stats.indConsts.isEmpty = false := by
              simpa using hempty
            simp only [hempty', Bool.false_eq_true, if_false,
              ReaderT.bind, Bind.bind, liftTypeChecker_apply]
            cases hget : getType stats.params[i]! context with
            | error error => rfl
            | ok paramType =>
                simp only [hget, Except.bind]
                cases heq : TypeChecker.M.run context.env context.safety
                    context.lctx context.lparams context.fuel
                    (TypeChecker.isDefEq dom paramType) with
                | error error => rfl
                | ok equal =>
                    simp only [heq, Except.bind]
                    cases equal
                    · rfl
                    · simp only [if_true]
                      cases hwhnf : TypeChecker.M.run context.env
                          context.safety context.lctx context.lparams
                          context.fuel
                          (TypeChecker.whnf
                            (body.instantiate1 stats.params[i]!)) with
                      | error error =>
                          simp only [ReaderT.bind, Bind.bind,
                            liftTypeChecker_apply, hwhnf, Except.bind]
                      | ok view =>
                          simp only [ReaderT.bind, Bind.bind,
                            liftTypeChecker_apply, hwhnf, Except.bind]
                          simpa only [observeFamilyValidationTelescope,
                            Bind.bind, Except.bind] using
                            ih stats view (i + 1) nindices context
        · simp only [hi, if_false, withLocalDecl_apply, ReaderT.bind,
            Bind.bind, liftTypeChecker_apply]
          let nextContext := context.pushLocalDecl name bi
            (consumeTypeAnnotations dom)
          cases hwhnf : TypeChecker.M.run nextContext.env
              nextContext.safety nextContext.lctx nextContext.lparams
              nextContext.fuel
              (TypeChecker.whnf (body.instantiate1 context.freshExpr)) with
          | error error => rfl
          | ok view =>
              simpa only [observeFamilyValidationTelescope, nextContext,
                Bind.bind, Except.bind] using
                ih stats view i (nindices + 1) nextContext
      all_goals
        simp only [observeFamilyValidationTelescope,
          checkInductiveTypes.loopInd.loop]
        by_cases hi : i = nparams <;>
          simp [hi, ReaderT.bind, Bind.bind, Except.bind, throw, throwThe,
            MonadExceptOf.throw]

/-- Counter invariant threaded through the inner family telescope.  The first
family grows the shared parameter array until `i = nparams`; every later
family reuses that already-complete array. -/
private def familyValidationTelescopeStatsInvariant
    (nparams i : Nat) (stats : InductiveStats) : Prop :=
  i ≤ nparams ∧
    if stats.indConsts.isEmpty then
      stats.params.size + (nparams - i) = nparams
    else
      stats.params.size = nparams

/-- A successful inner telescope run changes only the shared parameter array,
leaving the block-wide index and family-constant counters untouched, and its
terminal parameter count is exact. -/
private theorem familyValidationTelescope_sizes_of_run
    (nparams : Nat) (stats : InductiveStats) (type : Expr)
    (i nindices fuel : Nat) (context : Context)
    (result : FamilyValidationTelescopeResult)
    (invariant : familyValidationTelescopeStatsInvariant nparams i stats)
    (success : observeFamilyValidationTelescope nparams stats type i nindices
      fuel context = .ok result) :
    result.stats.nindices = stats.nindices ∧
    result.stats.indConsts = stats.indConsts ∧
    result.stats.levels = stats.levels ∧
      result.stats.resultLevel = stats.resultLevel ∧
      result.stats.isNotZero = stats.isNotZero ∧
      result.stats.params.size = nparams ∧
      result.context.lparams = context.lparams ∧
      result.context.env = context.env ∧
      result.context.allowPrimitive = context.allowPrimitive := by
  induction fuel generalizing stats type i nindices context result with
  | zero =>
      simp [observeFamilyValidationTelescope,
        checkInductiveTypes.loopInd.loop] at success
  | succ fuel ih =>
      cases type
      case forallE name dom body bi =>
        simp only [observeFamilyValidationTelescope,
          checkInductiveTypes.loopInd.loop] at success
        by_cases hi : i < nparams
        · simp only [hi, if_true] at success
          by_cases hempty : stats.indConsts = #[]
          · simp only [hempty, Array.isEmpty_empty, if_true,
              withLocalDecl_apply, ReaderT.bind, Bind.bind,
              liftTypeChecker_apply] at success
            let nextContext := context.pushLocalDecl name bi
              (consumeTypeAnnotations dom)
            cases hwhnf : TypeChecker.M.run nextContext.env
                nextContext.safety nextContext.lctx nextContext.lparams
                nextContext.fuel
                (TypeChecker.whnf (body.instantiate1 context.freshExpr)) with
            | error error =>
                rw [hwhnf] at success
                cases success
            | ok view =>
                rw [hwhnf] at success
                simp only [Except.bind] at success
                let nextStats : InductiveStats :=
                  { stats with params :=
                    stats.params.push context.freshExpr }
                have nextInvariant :
                    familyValidationTelescopeStatsInvariant nparams (i + 1)
                      nextStats := by
                  simp only [nextStats]
                  unfold familyValidationTelescopeStatsInvariant at invariant ⊢
                  simp only [hempty, Array.isEmpty_empty, if_true,
                    Array.size_push]
                  constructor
                  · omega
                  · have := invariant.2
                    simp only [hempty, Array.isEmpty_empty, if_true] at this
                    omega
                apply ih (stats := nextStats) (type := view) (i := i + 1)
                  (nindices := nindices) (context := nextContext)
                  (result := result) nextInvariant
                simpa only [observeFamilyValidationTelescope, nextStats,
                  hempty] using success
          · have hempty' : stats.indConsts.isEmpty = false := by
              simpa using hempty
            simp only [hempty', Bool.false_eq_true, if_false,
              ReaderT.bind, Bind.bind, liftTypeChecker_apply] at success
            cases hget : getType stats.params[i]! context with
            | error error =>
                rw [hget] at success
                cases success
            | ok paramType =>
                rw [hget] at success
                simp only [Except.bind] at success
                cases heq : TypeChecker.M.run context.env context.safety
                    context.lctx context.lparams context.fuel
                    (TypeChecker.isDefEq dom paramType) with
                | error error =>
                    rw [heq] at success
                    cases success
                | ok equal =>
                    rw [heq] at success
                    simp only [Except.bind] at success
                    cases equal
                    · simp [ReaderT.bind, Bind.bind, liftExcept_apply,
                        Except.bind, throw, throwThe,
                        MonadExceptOf.throw] at success
                    · simp only [if_true] at success
                      cases hwhnf : TypeChecker.M.run context.env
                          context.safety context.lctx context.lparams
                          context.fuel
                          (TypeChecker.whnf
                            (body.instantiate1 stats.params[i]!)) with
                      | error error =>
                          simp only [ReaderT.bind, Bind.bind,
                            liftTypeChecker_apply] at success
                          rw [hwhnf] at success
                          cases success
                      | ok view =>
                          simp only [ReaderT.bind, Bind.bind,
                            liftTypeChecker_apply, hwhnf,
                            Except.bind] at success
                          have nextInvariant :
                              familyValidationTelescopeStatsInvariant nparams
                                (i + 1) stats := by
                            unfold familyValidationTelescopeStatsInvariant at invariant ⊢
                            simp only [hempty', Bool.false_eq_true, if_false]
                              at invariant ⊢
                            exact ⟨by omega, invariant.2⟩
                          apply ih (stats := stats) (type := view)
                            (i := i + 1) (nindices := nindices)
                            (context := context) (result := result)
                            nextInvariant
                          simpa only [observeFamilyValidationTelescope] using
                            success
        · simp only [hi, if_false, withLocalDecl_apply, ReaderT.bind,
            Bind.bind, liftTypeChecker_apply] at success
          let nextContext := context.pushLocalDecl name bi
            (consumeTypeAnnotations dom)
          cases hwhnf : TypeChecker.M.run nextContext.env
              nextContext.safety nextContext.lctx nextContext.lparams
              nextContext.fuel
              (TypeChecker.whnf (body.instantiate1 context.freshExpr)) with
          | error error =>
              rw [hwhnf] at success
              cases success
          | ok view =>
              rw [hwhnf] at success
              simp only [Except.bind] at success
              apply ih (stats := stats) (type := view) (i := i)
                (nindices := nindices + 1) (context := nextContext)
                (result := result) invariant
              simpa only [observeFamilyValidationTelescope] using success
      all_goals
        simp only [observeFamilyValidationTelescope,
          checkInductiveTypes.loopInd.loop] at success
        by_cases hi : i = nparams
        · subst i
          simp [ReaderT.bind, Bind.bind, Except.bind, throw, throwThe,
            MonadExceptOf.throw] at success
          subst result
          refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl⟩
          unfold familyValidationTelescopeStatsInvariant at invariant
          simpa using invariant.2
        · simp [hi, ReaderT.bind, Bind.bind, Except.bind, throw, throwThe,
            MonadExceptOf.throw] at success

/-- Lift a pointwise continuation factorization through the unchanged inner
family-telescope traversal. -/
private theorem checkInductiveTypes_telescope_factor_between
    (nparams : Nat) (stats : InductiveStats) (type : Expr)
    (i nindices fuel : Nat)
    (k₁ : Expr → InductiveStats → Nat → M α)
    (k₂ : Expr → InductiveStats → Nat → M β)
    (f : β → Except Exception α) (context : Context)
    (hk : ∀ type stats nindices context,
      k₁ type stats nindices context =
        (k₂ type stats nindices context >>= f)) :
    checkInductiveTypes.loopInd.loop nparams stats type i nindices fuel k₁
        context =
      (checkInductiveTypes.loopInd.loop nparams stats type i nindices fuel k₂
        context >>= f) := by
  rw [checkInductiveTypes_telescope_factor (k := k₁)]
  rw [checkInductiveTypes_telescope_factor (k := k₂)]
  cases hrun : observeFamilyValidationTelescope nparams stats type i nindices
      fuel context with
  | error error => rfl
  | ok result =>
      simp only [hrun, Bind.bind, Except.bind]
      exact hk result.type result.stats result.nindices result.context

/-- Observe the outer mutual-family loop from an arbitrary intermediate
family ordinal and statistics value. -/
private def observeFamilyValidationOuterLoop (nparams : Nat)
    (indTypes : Array InductiveType) (dIdx : Nat) (stats : InductiveStats)
    (context : Context) : Except Exception FamilyValidationBlockResult :=
  checkInductiveTypes.loopInd nparams indTypes
    (fun stats => fun context =>
      .ok { stats, validationContext := context }) dIdx stats context

/-- Every continuation of the outer mutual-family loop factors through the
exact statistics and reader context selected by that same loop. -/
private theorem checkInductiveTypes_outerLoop_factor
    (nparams : Nat) (indTypes : Array InductiveType)
    (dIdx : Nat) (stats : InductiveStats) (k : InductiveStats → M α)
    (context : Context) :
    checkInductiveTypes.loopInd nparams indTypes k dIdx stats context =
      (observeFamilyValidationOuterLoop nparams indTypes dIdx stats context >>=
        fun result => k result.stats result.validationContext) := by
  rw [checkInductiveTypes.loopInd.eq_1]
  unfold observeFamilyValidationOuterLoop
  rw [checkInductiveTypes.loopInd.eq_1]
  by_cases hdIdx : dIdx < indTypes.size
  · rw [dif_pos hdIdx, dif_pos hdIdx]
    simp only [ReaderT.bind, Bind.bind, liftTypeChecker_apply,
      readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
      ReaderT.pure, Pure.pure, Except.pure, liftExcept_apply,
      Except.bind]
    cases hclosed : context.env.checkNoMVarNoFVar indTypes[dIdx].name
        indTypes[dIdx].type with
    | error error => rfl
    | ok _ =>
        cases hcheck : TypeChecker.M.run context.env context.safety
            context.lctx context.lparams context.fuel
            (TypeChecker.checkType indTypes[dIdx].type) with
        | error error => rfl
        | ok _ =>
            cases hwhnf : TypeChecker.M.run context.env context.safety
                context.lctx context.lparams context.fuel
                (TypeChecker.whnf indTypes[dIdx].type) with
            | error error => rfl
            | ok root =>
                apply checkInductiveTypes_telescope_factor_between
                intro type nextStats nindices nextContext
                simp only [ReaderT.bind, Bind.bind,
                  liftTypeChecker_apply]
                cases hsort : TypeChecker.M.run nextContext.env
                    nextContext.safety nextContext.lctx nextContext.lparams
                    nextContext.fuel (TypeChecker.ensureSort type) with
                | error error => rfl
                | ok sorted =>
                    simp only [Except.bind]
                    by_cases hempty : nextStats.indConsts.isEmpty = true
                    · simp only [hempty, if_true, ReaderT.bind, Bind.bind,
                        ReaderT.pure, Pure.pure, Except.pure, Except.bind]
                      simpa only [observeFamilyValidationOuterLoop,
                        Bind.bind, Except.bind] using
                        checkInductiveTypes_outerLoop_factor nparams indTypes
                          (dIdx + 1)
                          { nextStats with
                            lctx := nextContext.lctx
                            resultLevel := sorted.sortLevel!
                            isNotZero := sorted.sortLevel!.isNeverZero
                            nindices := nextStats.nindices.push nindices
                            indConsts := nextStats.indConsts.push
                              (.const indTypes[dIdx].name nextStats.levels) }
                          k nextContext
                    · simp only [hempty, Bool.false_eq_true, if_false]
                      by_cases hlevel :
                          (!sorted.sortLevel!.isEquiv nextStats.resultLevel) =
                            true
                      · simp [hlevel, ReaderT.bind, Bind.bind,
                          liftExcept_apply, Except.bind, throw, throwThe,
                          MonadExceptOf.throw]
                      · simp only [hlevel, Bool.false_eq_true, if_false]
                        simpa only [observeFamilyValidationOuterLoop,
                          Bind.bind, Except.bind] using
                          checkInductiveTypes_outerLoop_factor nparams
                            indTypes (dIdx + 1)
                            { nextStats with
                              nindices := nextStats.nindices.push nindices
                              indConsts := nextStats.indConsts.push
                                (.const indTypes[dIdx].name nextStats.levels) }
                            k nextContext
  · rw [dif_neg hdIdx, dif_neg hdIdx]
    rfl
termination_by indTypes.size - dIdx
decreasing_by
  all_goals exact Nat.sub_lt_sub_left hdIdx (Nat.lt_succ_self dIdx)

/-- Block-counter invariant at an intermediate outer-family ordinal. -/
private def familyValidationOuterStatsInvariant
    (nparams : Nat) (indTypes : Array InductiveType) (dIdx : Nat)
    (stats : InductiveStats) (context : Context) : Prop :=
  dIdx ≤ indTypes.size ∧
    stats.nindices.size = dIdx ∧
    stats.indConsts.size = dIdx ∧
    stats.levels.length = context.lparams.length ∧
    (if dIdx = 0 then stats.params.size = 0
    else stats.params.size = nparams) ∧
    ∀ familyIdx, familyIdx < dIdx →
      stats.indConsts[familyIdx]? =
        some (.const indTypes[familyIdx]!.name stats.levels)

/-- A successful outer-family observer reaches the exact terminal block
counts.  Nonemptiness is essential: the implementation's terminal `assert!`
uses an inhabited fallback for an empty block with nonzero `nparams`. -/
private theorem familyValidationOuter_sizes_of_run
    (nparams : Nat) (indTypes : Array InductiveType)
    (dIdx : Nat) (stats : InductiveStats) (context : Context)
    (result : FamilyValidationBlockResult)
    (nonempty : 0 < indTypes.size)
    (invariant : familyValidationOuterStatsInvariant nparams indTypes dIdx
      stats context)
    (success : observeFamilyValidationOuterLoop nparams indTypes dIdx stats
      context = .ok result) :
    result.stats.nindices.size = indTypes.size ∧
      result.stats.indConsts.size = indTypes.size ∧
    result.stats.params.size = nparams ∧
      result.validationContext.env = context.env ∧
      result.validationContext.lparams = context.lparams ∧
      result.validationContext.allowPrimitive = context.allowPrimitive ∧
      (∀ familyIdx, familyIdx < indTypes.size →
        result.stats.indConsts[familyIdx]? = some
          (.const indTypes[familyIdx]!.name result.stats.levels)) ∧
      result.stats.levels = stats.levels := by
  unfold observeFamilyValidationOuterLoop at success
  rw [checkInductiveTypes.loopInd.eq_1] at success
  by_cases hdIdx : dIdx < indTypes.size
  · rw [dif_pos hdIdx] at success
    simp only [ReaderT.bind, Bind.bind, liftTypeChecker_apply,
      readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
      ReaderT.pure, Pure.pure, Except.pure, liftExcept_apply,
      Except.bind] at success
    cases hclosed : context.env.checkNoMVarNoFVar indTypes[dIdx].name
        indTypes[dIdx].type with
    | error error =>
        rw [hclosed] at success
        cases success
    | ok _ =>
        rw [hclosed] at success
        simp only [Except.bind] at success
        cases hcheck : TypeChecker.M.run context.env context.safety
            context.lctx context.lparams context.fuel
            (TypeChecker.checkType indTypes[dIdx].type) with
        | error error =>
            rw [hcheck] at success
            cases success
        | ok _ =>
            rw [hcheck] at success
            simp only [Except.bind] at success
            cases hwhnf : TypeChecker.M.run context.env context.safety
                context.lctx context.lparams context.fuel
                (TypeChecker.whnf indTypes[dIdx].type) with
            | error error =>
                rw [hwhnf] at success
                cases success
            | ok root =>
                rw [hwhnf] at success
                simp only [Except.bind] at success
                rw [checkInductiveTypes_telescope_factor] at success
                cases htelescope : observeFamilyValidationTelescope nparams
                    stats root 0 0 context.fuel.inductiveFuel context with
                | error error =>
                    rw [htelescope] at success
                    cases success
                | ok telescopeResult =>
                    rw [htelescope] at success
                    simp only [Bind.bind, Except.bind] at success
                    have telescopeInvariant :
                        familyValidationTelescopeStatsInvariant nparams 0
                          stats := by
                      unfold familyValidationOuterStatsInvariant at invariant
                      unfold familyValidationTelescopeStatsInvariant
                      refine ⟨Nat.zero_le _, ?_⟩
                      by_cases hempty : stats.indConsts = #[]
                      · have hdIdx_zero : dIdx = 0 := by
                          have hsize := invariant.2.2.1
                          rw [hempty] at hsize
                          simp only [Array.size_empty] at hsize
                          omega
                        have hparams : stats.params.size = 0 := by
                          simpa only [hdIdx_zero, if_true] using
                            invariant.2.2.2.2.1
                        simp [hempty, hparams]
                      · have hdIdx_ne : dIdx ≠ 0 := by
                          intro hdIdx_zero
                          have hsize : stats.indConsts.size = 0 := by
                            simpa only [hdIdx_zero] using invariant.2.2.1
                          exact hempty (Array.size_eq_zero_iff.mp hsize)
                        have hparams : stats.params.size = nparams := by
                          simpa only [hdIdx_ne, if_false] using
                            invariant.2.2.2.2.1
                        have hempty' : stats.indConsts.isEmpty = false := by
                          cases h : stats.indConsts.isEmpty with
                          | false => rfl
                          | true =>
                              exact absurd (Array.isEmpty_iff.mp h) hempty
                        simp only [hempty', Bool.false_eq_true, if_false,
                          hparams]
                    obtain ⟨hnindices, hindConsts, hlevels, _hresultLevel,
                        _hisNotZero, hparams, hlparams, henv,
                        hallowPrimitive⟩ :=
                      familyValidationTelescope_sizes_of_run nparams stats
                        root 0 0 context.fuel.inductiveFuel context
                        telescopeResult telescopeInvariant htelescope
                    simp only [ReaderT.bind, Bind.bind,
                      liftTypeChecker_apply] at success
                    cases hsort : TypeChecker.M.run telescopeResult.context.env
                        telescopeResult.context.safety
                        telescopeResult.context.lctx
                        telescopeResult.context.lparams
                        telescopeResult.context.fuel
                        (TypeChecker.ensureSort telescopeResult.type) with
                    | error error =>
                        rw [hsort] at success
                        cases success
                    | ok sorted =>
                        rw [hsort] at success
                        simp only [Except.bind] at success
                        by_cases hempty :
                            telescopeResult.stats.indConsts.isEmpty = true
                        · simp only [hempty, if_true, ReaderT.bind,
                            Bind.bind, ReaderT.pure, Pure.pure, Except.pure,
                            Except.bind] at success
                          let nextStats : InductiveStats :=
                            { telescopeResult.stats with
                              lctx := telescopeResult.context.lctx
                              resultLevel := sorted.sortLevel!
                              isNotZero := sorted.sortLevel!.isNeverZero
                              nindices :=
                                telescopeResult.stats.nindices.push
                                  telescopeResult.nindices
                              indConsts :=
                                telescopeResult.stats.indConsts.push
                                  (.const indTypes[dIdx].name
                                    telescopeResult.stats.levels) }
                          have nextInvariant :
                              familyValidationOuterStatsInvariant nparams
                                indTypes (dIdx + 1) nextStats
                                telescopeResult.context := by
                            unfold familyValidationOuterStatsInvariant at invariant ⊢
                            refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
                            · simp only [nextStats, Array.size_push]
                              rw [hnindices, invariant.2.1]
                            · simp only [nextStats, Array.size_push]
                              rw [hindConsts, invariant.2.2.1]
                            · simp only [nextStats]
                              rw [hlevels, hlparams]
                              exact invariant.2.2.2.1
                            · simp only [show dIdx + 1 ≠ 0 by omega,
                                if_false, nextStats]
                              exact hparams
                            · intro familyIdx familyIdxLt
                              simp only [nextStats, Array.getElem?_push]
                              have oldSize :
                                  telescopeResult.stats.indConsts.size =
                                    dIdx := by
                                rw [hindConsts, invariant.2.2.1]
                              by_cases current : familyIdx = dIdx
                              · subst familyIdx
                                simp [oldSize, hdIdx]
                              · rw [if_neg (by omega)]
                                rw [hindConsts, hlevels]
                                exact invariant.2.2.2.2.2 _ (by omega)
                          rw [← henv, ← hlparams, ← hallowPrimitive,
                            ← hlevels]
                          apply familyValidationOuter_sizes_of_run nparams
                            indTypes (dIdx + 1) nextStats
                            telescopeResult.context result nonempty nextInvariant
                          simpa only [observeFamilyValidationOuterLoop,
                            nextStats] using success
                        · simp only [hempty, if_false] at success
                          by_cases hlevel :
                              (!sorted.sortLevel!.isEquiv
                                telescopeResult.stats.resultLevel) = true
                          · simp [hlevel, ReaderT.bind, Bind.bind,
                              liftExcept_apply, Except.bind, throw, throwThe,
                              MonadExceptOf.throw] at success
                          · simp only [hlevel, Bool.false_eq_true,
                              if_false] at success
                            let nextStats : InductiveStats :=
                              { telescopeResult.stats with
                                nindices :=
                                  telescopeResult.stats.nindices.push
                                    telescopeResult.nindices
                                indConsts :=
                                  telescopeResult.stats.indConsts.push
                                    (.const indTypes[dIdx].name
                                      telescopeResult.stats.levels) }
                            have nextInvariant :
                                familyValidationOuterStatsInvariant nparams
                                  indTypes (dIdx + 1) nextStats
                                  telescopeResult.context := by
                              unfold familyValidationOuterStatsInvariant at invariant ⊢
                              refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
                              · simp only [nextStats, Array.size_push]
                                rw [hnindices, invariant.2.1]
                              · simp only [nextStats, Array.size_push]
                                rw [hindConsts, invariant.2.2.1]
                              · simp only [nextStats]
                                rw [hlevels, hlparams]
                                exact invariant.2.2.2.1
                              · simp only [show dIdx + 1 ≠ 0 by omega,
                                  if_false, nextStats]
                                exact hparams
                              · intro familyIdx familyIdxLt
                                simp only [nextStats, Array.getElem?_push]
                                have oldSize :
                                    telescopeResult.stats.indConsts.size =
                                      dIdx := by
                                  rw [hindConsts, invariant.2.2.1]
                                by_cases current : familyIdx = dIdx
                                · subst familyIdx
                                  simp [oldSize, hdIdx]
                                · rw [if_neg (by omega)]
                                  rw [hindConsts, hlevels]
                                  exact invariant.2.2.2.2.2 _ (by omega)
                            rw [← henv, ← hlparams, ← hallowPrimitive,
                              ← hlevels]
                            apply familyValidationOuter_sizes_of_run nparams
                              indTypes (dIdx + 1) nextStats
                              telescopeResult.context result nonempty
                              nextInvariant
                            simpa only [observeFamilyValidationOuterLoop,
                              nextStats] using success
  · rw [dif_neg hdIdx] at success
    unfold familyValidationOuterStatsInvariant at invariant
    have hdIdx_eq : dIdx = indTypes.size := by omega
    have hparams : stats.params.size = nparams := by
      have hdIdx_ne : dIdx ≠ 0 := by omega
      simpa only [hdIdx_ne, if_false] using invariant.2.2.2.2.1
    have hnindices : stats.nindices.size = indTypes.size := by
      omega
    have hindConsts : stats.indConsts.size = indTypes.size := by
      omega
    have hlevels : stats.levels.length = context.lparams.length :=
      invariant.2.2.2.1
    simp only [readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
      ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure, Except.pure,
      Except.bind] at success
    simp [hlevels, hnindices, hindConsts, hparams] at success
    subst result
    exact ⟨hnindices, hindConsts, hparams, rfl, rfl, rfl,
      fun familyIdx familyIdxLt =>
        invariant.2.2.2.2.2 familyIdx (by omega), rfl⟩
termination_by indTypes.size - dIdx
decreasing_by
  all_goals exact Nat.sub_lt_sub_left hdIdx (Nat.lt_succ_self dIdx)

/-- Once at least one family has been accepted, the outer mutual-family loop
never replaces either the common result level or its cached nonzero decision
selected by that first family.  Every later family may only pass the
executable `isEquiv` comparison against the common level.  The counter
invariant is retained so the terminal `assert!` values are known to be the
actual statistics rather than their inhabited fallbacks. -/
private theorem familyValidationOuter_resultState_of_run
    (nparams : Nat) (indTypes : Array InductiveType)
    (dIdx : Nat) (stats : InductiveStats) (context : Context)
    (result : FamilyValidationBlockResult)
    (dIdx_ne : dIdx ≠ 0)
    (invariant : familyValidationOuterStatsInvariant nparams indTypes dIdx
      stats context)
    (success : observeFamilyValidationOuterLoop nparams indTypes dIdx stats
      context = .ok result) :
    result.stats.resultLevel = stats.resultLevel ∧
      result.stats.isNotZero = stats.isNotZero := by
  unfold observeFamilyValidationOuterLoop at success
  rw [checkInductiveTypes.loopInd.eq_1] at success
  by_cases hdIdx : dIdx < indTypes.size
  · rw [dif_pos hdIdx] at success
    simp only [ReaderT.bind, Bind.bind, liftTypeChecker_apply,
      readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
      ReaderT.pure, Pure.pure, Except.pure, liftExcept_apply,
      Except.bind] at success
    cases hclosed : context.env.checkNoMVarNoFVar indTypes[dIdx].name
        indTypes[dIdx].type with
    | error error =>
        rw [hclosed] at success
        cases success
    | ok _ =>
        rw [hclosed] at success
        simp only [Except.bind] at success
        cases hcheck : TypeChecker.M.run context.env context.safety
            context.lctx context.lparams context.fuel
            (TypeChecker.checkType indTypes[dIdx].type) with
        | error error =>
            rw [hcheck] at success
            cases success
        | ok _ =>
            rw [hcheck] at success
            simp only [Except.bind] at success
            cases hwhnf : TypeChecker.M.run context.env context.safety
                context.lctx context.lparams context.fuel
                (TypeChecker.whnf indTypes[dIdx].type) with
            | error error =>
                rw [hwhnf] at success
                cases success
            | ok root =>
                rw [hwhnf] at success
                simp only [Except.bind] at success
                rw [checkInductiveTypes_telescope_factor] at success
                cases htelescope : observeFamilyValidationTelescope nparams
                    stats root 0 0 context.fuel.inductiveFuel context with
                | error error =>
                    rw [htelescope] at success
                    cases success
                | ok telescopeResult =>
                    rw [htelescope] at success
                    simp only [Bind.bind, Except.bind] at success
                    have statsEmpty : stats.indConsts.isEmpty = false := by
                      cases hempty : stats.indConsts.isEmpty with
                      | false => rfl
                      | true =>
                          have empty := Array.isEmpty_iff.mp hempty
                          have size : stats.indConsts.size = dIdx :=
                            invariant.2.2.1
                          rw [empty] at size
                          simp only [Array.size_empty] at size
                          omega
                    have paramsSize : stats.params.size = nparams := by
                      simpa only [dIdx_ne, if_false] using
                            invariant.2.2.2.2.1
                    have telescopeInvariant :
                        familyValidationTelescopeStatsInvariant nparams 0
                          stats := by
                      unfold familyValidationTelescopeStatsInvariant
                      simp only [Nat.zero_le, statsEmpty, Bool.false_eq_true,
                        if_false, paramsSize, and_self]
                    obtain ⟨hnindices, hindConsts, hlevels, hresultLevel,
                        hisNotZero, hparams, hlparams, henv,
                        hallowPrimitive⟩ :=
                      familyValidationTelescope_sizes_of_run nparams stats
                        root 0 0 context.fuel.inductiveFuel context
                        telescopeResult telescopeInvariant htelescope
                    simp only [ReaderT.bind, Bind.bind,
                      liftTypeChecker_apply] at success
                    cases hsort : TypeChecker.M.run telescopeResult.context.env
                        telescopeResult.context.safety
                        telescopeResult.context.lctx
                        telescopeResult.context.lparams
                        telescopeResult.context.fuel
                        (TypeChecker.ensureSort telescopeResult.type) with
                    | error error =>
                        rw [hsort] at success
                        cases success
                    | ok sorted =>
                        rw [hsort] at success
                        simp only [Except.bind] at success
                        have telescopeNotEmpty :
                            telescopeResult.stats.indConsts.isEmpty = false := by
                          rw [hindConsts, statsEmpty]
                        rw [telescopeNotEmpty] at success
                        simp only [Bool.false_eq_true, if_false] at success
                        by_cases hlevel :
                            (!sorted.sortLevel!.isEquiv
                              telescopeResult.stats.resultLevel) = true
                        · simp [hlevel, ReaderT.bind, Bind.bind,
                            liftExcept_apply, Except.bind, throw, throwThe,
                            MonadExceptOf.throw] at success
                        · simp only [hlevel, Bool.false_eq_true,
                            if_false] at success
                          let nextStats : InductiveStats :=
                            { telescopeResult.stats with
                              nindices :=
                                telescopeResult.stats.nindices.push
                                  telescopeResult.nindices
                              indConsts :=
                                telescopeResult.stats.indConsts.push
                                  (.const indTypes[dIdx].name
                                    telescopeResult.stats.levels) }
                          have nextInvariant :
                              familyValidationOuterStatsInvariant nparams
                                indTypes (dIdx + 1) nextStats
                                telescopeResult.context := by
                            unfold familyValidationOuterStatsInvariant
                              at invariant ⊢
                            refine ⟨by omega, ?_, ?_, ?_, ?_, ?_⟩
                            · simp only [nextStats, Array.size_push]
                              rw [hnindices, invariant.2.1]
                            · simp only [nextStats, Array.size_push]
                              rw [hindConsts, invariant.2.2.1]
                            · simp only [nextStats]
                              rw [hlevels, hlparams]
                              exact invariant.2.2.2.1
                            · simp only [show dIdx + 1 ≠ 0 by omega,
                                if_false, nextStats]
                              exact hparams
                            · intro familyIdx familyIdxLt
                              simp only [nextStats, Array.getElem?_push]
                              have oldSize :
                                  telescopeResult.stats.indConsts.size =
                                    dIdx := by
                                rw [hindConsts, invariant.2.2.1]
                              by_cases current : familyIdx = dIdx
                              · subst familyIdx
                                simp [oldSize, hdIdx]
                              · rw [if_neg (by omega)]
                                rw [hindConsts, hlevels]
                                exact invariant.2.2.2.2.2 _ (by omega)
                          have tail := familyValidationOuter_resultState_of_run
                            nparams indTypes (dIdx + 1) nextStats
                            telescopeResult.context result (by omega)
                            nextInvariant (by
                              simpa only [observeFamilyValidationOuterLoop,
                                nextStats] using success)
                          exact ⟨tail.1.trans hresultLevel,
                            tail.2.trans hisNotZero⟩
  · rw [dif_neg hdIdx] at success
    unfold familyValidationOuterStatsInvariant at invariant
    have hdIdx_eq : dIdx = indTypes.size := by omega
    have hparams : stats.params.size = nparams := by
      simpa only [dIdx_ne, if_false] using invariant.2.2.2.2.1
    have hnindices : stats.nindices.size = indTypes.size := by omega
    have hindConsts : stats.indConsts.size = indTypes.size := by omega
    have hlevels : stats.levels.length = context.lparams.length :=
      invariant.2.2.2.1
    simp only [readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
      ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure, Except.pure,
      Except.bind] at success
    simp [hlevels, hnindices, hindConsts, hparams] at success
    subst result
    exact ⟨rfl, rfl⟩
termination_by indTypes.size - dIdx
decreasing_by
  all_goals exact Nat.sub_lt_sub_left hdIdx (Nat.lt_succ_self dIdx)

/-- Exact continuation factorization for an arbitrary mutual-family
validation run.  In particular, changing the continuation cannot change the
statistics or local reader context selected before that continuation. -/
theorem checkInductiveTypes_factor
    (nparams : Nat) (indTypes : List InductiveType)
    (k : InductiveStats → M α) (context : Context) :
    checkInductiveTypes nparams indTypes.toArray k context =
      (observeFamilyValidationBlock nparams indTypes context >>= fun result =>
        k result.stats result.validationContext) := by
  unfold observeFamilyValidationBlock checkInductiveTypes
  simp only [readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure, Except.pure,
    Except.bind]
  simpa only [observeFamilyValidationOuterLoop, Bind.bind, Except.bind] using
    checkInductiveTypes_outerLoop_factor nparams indTypes.toArray 0
      (InductiveStats.initial (context.lparams.map .param)) k context

/-- Legacy pointwise observer contract after ordinary family validation, raw
family declaration, and constructor validation have succeeded.  It records
the recursive candidate-expression traversals for family types in the input
environment and constructor types in the post-family environment.

`AddInductive.run` now executes the retained normalization prefix directly,
so this contract is useful for independent reconstruction lemmas but is no
longer an operational-completeness premise.

The constructor equation is intentionally part of the antecedent.  Besides
being available from every successful public run, it carries the structural
fuel information needed to replay recursive constructor types (for example
the field of `Nat.succ`). -/
def NormalizationCandidateExecution.CandidateObserversComplete
    (nparams : Nat) (types : List InductiveType)
    (numNested : Nat) (isUnsafe : Bool)
    (candidateContext : Context) : Prop :=
  ∀ (validation : FamilyValidationBlockResult),
    observeFamilyValidationBlock nparams types candidateContext =
        .ok validation →
    ∀ (familyEnv : Environment),
      declareInductiveTypes validation.stats nparams types.toArray
          numNested isUnsafe validation.validationContext = .ok familyEnv →
      checkConstructors types.toArray validation.stats isUnsafe
          { validation.validationContext with env := familyEnv } = .ok () →
      CandidateFamilyTypeListObservable
          { candidateContext with lctx := {} } types ∧
        CandidateFamilyConstructorListsObservable
          { candidateContext with env := familyEnv, lctx := {} } types

/-- Successful pointwise candidate observers, source closure, stored-spine
and parameter-prefix evidence, and the ordinary
validation/declaration/constructor equations
reconstruct the complete retained normalization execution.  The public
builder obtains both structural facts from executable gates; this theorem
remains a compatibility bridge for callers that reconstruct a run from the
weaker legacy observer contract. -/
theorem NormalizationCandidateExecution.build_ok_of_candidateObservers
    (observers : CandidateObserversComplete nparams types numNested isUnsafe
      candidateContext)
    (sourcesClosed : FamilySourceClosedList types)
    {validation : FamilyValidationBlockResult}
    (validationRun :
      observeFamilyValidationBlock nparams types candidateContext =
        .ok validation)
    {familyEnv : Environment}
    (declareRun : declareInductiveTypes validation.stats nparams types.toArray
      numNested isUnsafe validation.validationContext = .ok familyEnv)
    (constructorRun : checkConstructors types.toArray validation.stats isUnsafe
      { validation.validationContext with env := familyEnv } = .ok ())
    (generationSpines :
      ∀ (familyTypes : CandidateFamilyTypeListExecution
          { candidateContext with lctx := {} } types)
        (families : CandidateFamilyListExecution
          { candidateContext with env := familyEnv, lctx := {} }
          familyTypes.candidates),
        executeCandidateFamilyTypeList
            { candidateContext with lctx := {} } types = .ok familyTypes →
          executeCandidateFamilyList
              { candidateContext with env := familyEnv, lctx := {} }
              familyTypes.candidates = .ok families →
            CandidateFamilyGenerationSpineList families.candidates)
    (parameterSpines :
      ∀ (familyTypes : CandidateFamilyTypeListExecution
          { candidateContext with lctx := {} } types)
        (families : CandidateFamilyListExecution
          { candidateContext with env := familyEnv, lctx := {} }
          familyTypes.candidates),
        executeCandidateFamilyTypeList
            { candidateContext with lctx := {} } types = .ok familyTypes →
          executeCandidateFamilyList
              { candidateContext with env := familyEnv, lctx := {} }
              familyTypes.candidates = .ok families →
            CandidateFamilyParameterSpineList nparams families.candidates)
    (indexCounts :
      ∀ (familyTypes : CandidateFamilyTypeListExecution
          { candidateContext with lctx := {} } types)
        (families : CandidateFamilyListExecution
          { candidateContext with env := familyEnv, lctx := {} }
          familyTypes.candidates),
        executeCandidateFamilyTypeList
            { candidateContext with lctx := {} } types = .ok familyTypes →
          executeCandidateFamilyList
              { candidateContext with env := familyEnv, lctx := {} }
              familyTypes.candidates = .ok families →
            CandidateFamilyIndexCountList validation.stats nparams 0
              families.candidates) :
    ∃ execution : NormalizationCandidateExecution nparams types numNested
        isUnsafe candidateContext,
      buildNormalizationCandidateExecution nparams types numNested isUnsafe
        candidateContext = .ok execution := by
  obtain ⟨familyTypeObservers, constructorObservers⟩ :=
    observers validation validationRun familyEnv declareRun constructorRun
  obtain ⟨familyTypes, familyTypesRun, familyTerminals⟩ :=
    executeCandidateFamilyTypeList_ok_with_terminals_of_observable
      familyTypeObservers
  unfold buildNormalizationCandidateExecution
  rw [checkInductiveTypes_factor, validationRun]
  simp only [Bind.bind, Except.bind]
  unfold buildNormalizationCandidateExecutionAfterValidation
  split
  next error actual =>
    rw [declareRun] at actual
    contradiction
  next actualFamilyEnv actualDeclareRun =>
    have familyEnvEq : actualFamilyEnv = familyEnv :=
      Except.ok.inj (actualDeclareRun.symm.trans declareRun)
    subst actualFamilyEnv
    split
    next error actual =>
      rw [constructorRun] at actual
      contradiction
    next actualConstructorRun =>
      split
      next error actual =>
        rw [familyTypesRun] at actual
        contradiction
      next actualFamilyTypes actualFamilyTypesRun =>
        have familyTypesEq : actualFamilyTypes = familyTypes :=
          Except.ok.inj (actualFamilyTypesRun.symm.trans familyTypesRun)
        subst actualFamilyTypes
        split
        next _ =>
          split
          next _ =>
            obtain ⟨families, familiesRun⟩ :=
              executeCandidateFamilyList_ok_of_observable
                familyTypes.candidates constructorObservers
            split
            next error actual =>
              rw [familiesRun] at actual
              contradiction
            next actualFamilies actualFamiliesRun =>
              have familiesEq : actualFamilies = families :=
                Except.ok.inj (actualFamiliesRun.symm.trans familiesRun)
              subst actualFamilies
              split
              next _ =>
                split
                next _ =>
                  split
                  next _ => exact ⟨_, rfl⟩
                  next notCounts =>
                    exact (notCounts
                      (indexCounts familyTypes families familyTypesRun
                        familiesRun).check_eq_true).elim
                next notParameters =>
                  exact (notParameters
                    (parameterSpines familyTypes families familyTypesRun
                      familiesRun).check_eq_true).elim
              next notSpines =>
                exact (notSpines
                  (generationSpines familyTypes families familyTypesRun
                    familiesRun).check_eq_true).elim
          next notTerminals =>
            exact (notTerminals familyTerminals.check_eq_true).elim
        next notSources =>
          exact (notSources sourcesClosed.check_eq_true).elim

/-- Terminal counters and the preserved kernel environment exposed by any
successful nonempty arbitrary-block family-validation run. -/
theorem FamilyValidationBlockResult.invariants_of_run
    (result : FamilyValidationBlockResult)
    (nonempty : indTypes.isEmpty = false)
    (run : observeFamilyValidationBlock nparams indTypes context =
      .ok result) :
    result.stats.params.size = nparams ∧
      result.stats.nindices.size = indTypes.length ∧
    result.stats.indConsts.size = indTypes.length ∧
      result.validationContext.env = context.env ∧
      result.validationContext.lparams = context.lparams ∧
      result.validationContext.allowPrimitive = context.allowPrimitive ∧
      (∀ familyIdx, familyIdx < indTypes.length →
        result.stats.indConsts[familyIdx]? = some
          (.const indTypes[familyIdx]!.name result.stats.levels)) ∧
      result.stats.levels = context.lparams.map .param := by
  have indTypes_ne : indTypes ≠ [] := by
    intro hempty
    subst indTypes
    simp at nonempty
  have size_pos : 0 < indTypes.toArray.size := by
    have length_ne : indTypes.length ≠ 0 := by
      simpa using indTypes_ne
    have : 0 < indTypes.length := by omega
    simpa using this
  have initialInvariant :
      familyValidationOuterStatsInvariant nparams indTypes.toArray 0
        (InductiveStats.initial (context.lparams.map .param)) context := by
    simp [familyValidationOuterStatsInvariant, InductiveStats.initial]
  have outerRun :
      observeFamilyValidationOuterLoop nparams indTypes.toArray 0
          (InductiveStats.initial (context.lparams.map .param)) context =
        .ok result := by
    unfold observeFamilyValidationBlock checkInductiveTypes at run
    simp only [readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
      ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure, Except.pure,
      Except.bind] at run
    simpa only [observeFamilyValidationOuterLoop] using run
  have sizes := familyValidationOuter_sizes_of_run nparams indTypes.toArray 0
    (InductiveStats.initial (context.lparams.map .param)) context result
    size_pos initialInvariant outerRun
  exact ⟨sizes.2.2.1, by simpa using sizes.1,
    by simpa using sizes.2.1, sizes.2.2.2.1, sizes.2.2.2.2.1,
    sizes.2.2.2.2.2.1, by simpa using sizes.2.2.2.2.2.2.1,
    by simpa [InductiveStats.initial] using sizes.2.2.2.2.2.2.2⟩

/-- Terminal counter invariants exposed by any successful nonempty arbitrary-
block family-validation run. -/
theorem FamilyValidationBlockResult.sizes_of_run
    (result : FamilyValidationBlockResult)
    (nonempty : indTypes.isEmpty = false)
    (run : observeFamilyValidationBlock nparams indTypes context =
      .ok result) :
    result.stats.params.size = nparams ∧
      result.stats.nindices.size = indTypes.length ∧
      result.stats.indConsts.size = indTypes.length := by
  have invariants := result.invariants_of_run nonempty run
  exact ⟨invariants.1, invariants.2.1, invariants.2.2.1⟩

/-- Family validation only extends its local telescope; it preserves the
kernel environment supplied by the caller. -/
theorem FamilyValidationBlockResult.validationContext_env_of_run
    (result : FamilyValidationBlockResult)
    (nonempty : indTypes.isEmpty = false)
    (run : observeFamilyValidationBlock nparams indTypes context =
      .ok result) :
    result.validationContext.env = context.env :=
  (result.invariants_of_run nonempty run).2.2.2.1

/-- Family validation preserves the universe-parameter list in its terminal
reader context. -/
theorem FamilyValidationBlockResult.validationContext_lparams_of_run
    (result : FamilyValidationBlockResult)
    (nonempty : indTypes.isEmpty = false)
    (run : observeFamilyValidationBlock nparams indTypes context =
      .ok result) :
    result.validationContext.lparams = context.lparams :=
  (result.invariants_of_run nonempty run).2.2.2.2.1

/-- Family validation preserves the primitive-name mode in its terminal
reader context. -/
theorem FamilyValidationBlockResult.validationContext_allowPrimitive_of_run
    (result : FamilyValidationBlockResult)
    (nonempty : indTypes.isEmpty = false)
    (run : observeFamilyValidationBlock nparams indTypes context =
      .ok result) :
    result.validationContext.allowPrimitive = context.allowPrimitive :=
  (result.invariants_of_run nonempty run).2.2.2.2.2.1

/-- Every terminal family-constant slot is exactly the corresponding source
family constant at the validator's retained declaration universes. -/
theorem FamilyValidationBlockResult.indConsts_getElem?_of_run
    (result : FamilyValidationBlockResult)
    (nonempty : indTypes.isEmpty = false)
    (run : observeFamilyValidationBlock nparams indTypes context =
      .ok result)
    (familyIdxLt : familyIdx < indTypes.length) :
    result.stats.indConsts[familyIdx]? = some
      (.const indTypes[familyIdx]!.name result.stats.levels) :=
  (result.invariants_of_run nonempty run).2.2.2.2.2.2.1
    familyIdx familyIdxLt

/-- The validator's terminal family statistics retain the caller's exact
universe-parameter list, not just its length. -/
theorem FamilyValidationBlockResult.stats_levels_of_run
    (result : FamilyValidationBlockResult)
    (nonempty : indTypes.isEmpty = false)
    (run : observeFamilyValidationBlock nparams indTypes context =
      .ok result) :
    result.stats.levels = context.lparams.map .param :=
  (result.invariants_of_run nonempty run).2.2.2.2.2.2.2

/-- Family validation never changes the kernel environment in its reader
context.  The empty block is handled directly; nonempty blocks use the retained
outer-loop invariant. -/
theorem FamilyValidationBlockResult.validationContext_env_of_run_all
    (result : FamilyValidationBlockResult)
    (run : observeFamilyValidationBlock nparams indTypes context =
      .ok result) :
    result.validationContext.env = context.env := by
  cases indTypes with
  | nil =>
      unfold observeFamilyValidationBlock checkInductiveTypes at run
      simp only [readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
        ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure, Except.pure,
        Except.bind] at run
      rw [checkInductiveTypes.loopInd.eq_1] at run
      simp [InductiveStats.initial, readThe, MonadReader.read,
        MonadReaderOf.read, ReaderT.read, ReaderT.bind, Bind.bind,
        ReaderT.pure, Pure.pure, Except.pure, Except.bind] at run
      subst result
      rfl
  | cons head tail =>
      exact result.validationContext_env_of_run (by simp) run

/-- Family validation preserves universe parameters for both empty and
nonempty blocks. -/
theorem FamilyValidationBlockResult.validationContext_lparams_of_run_all
    (result : FamilyValidationBlockResult)
    (run : observeFamilyValidationBlock nparams indTypes context =
      .ok result) :
    result.validationContext.lparams = context.lparams := by
  cases indTypes with
  | nil =>
      unfold observeFamilyValidationBlock checkInductiveTypes at run
      simp only [readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
        ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure, Except.pure,
        Except.bind] at run
      rw [checkInductiveTypes.loopInd.eq_1] at run
      simp [InductiveStats.initial, readThe, MonadReader.read,
        MonadReaderOf.read, ReaderT.read, ReaderT.bind, Bind.bind,
        ReaderT.pure, Pure.pure, Except.pure, Except.bind] at run
      subst result
      rfl
  | cons head tail =>
      exact result.validationContext_lparams_of_run (by simp) run

/-- Family validation preserves the primitive-name mode for both empty and
nonempty blocks. -/
theorem
    FamilyValidationBlockResult.validationContext_allowPrimitive_of_run_all
    (result : FamilyValidationBlockResult)
    (run : observeFamilyValidationBlock nparams indTypes context =
      .ok result) :
    result.validationContext.allowPrimitive = context.allowPrimitive := by
  cases indTypes with
  | nil =>
      unfold observeFamilyValidationBlock checkInductiveTypes at run
      simp only [readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
        ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure, Except.pure,
        Except.bind] at run
      rw [checkInductiveTypes.loopInd.eq_1] at run
      simp [InductiveStats.initial, readThe, MonadReader.read,
        MonadReaderOf.read, ReaderT.read, ReaderT.bind, Bind.bind,
        ReaderT.pure, Pure.pure, Except.pure, Except.bind] at run
      subst result
      rfl
  | cons head tail =>
      exact result.validationContext_allowPrimitive_of_run (by simp) run

/-- Family validation establishes the index-array size invariant for both
empty and nonempty blocks.  Unlike the parameter-array invariant, this remains
true in the empty block even when the internal assertion takes its default
fallback. -/
theorem FamilyValidationBlockResult.nindices_size_of_run_all
    (result : FamilyValidationBlockResult)
    (run : observeFamilyValidationBlock nparams indTypes context =
      .ok result) :
    result.stats.nindices.size = indTypes.length := by
  cases indTypes with
  | nil =>
      unfold observeFamilyValidationBlock checkInductiveTypes at run
      simp only [readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
        ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure, Except.pure,
        Except.bind] at run
      rw [checkInductiveTypes.loopInd.eq_1] at run
      simp [InductiveStats.initial, readThe, MonadReader.read,
        MonadReaderOf.read, ReaderT.read, ReaderT.bind, Bind.bind,
        ReaderT.pure, Pure.pure, Except.pure, Except.bind] at run
      subst result
      split <;> rfl
  | cons head tail =>
      exact (result.sizes_of_run (by simp) run).2.1

/-- The family-validation result stored by a detailed normalization
execution. -/
def NormalizationCandidateExecution.familyValidationResult
    (execution : NormalizationCandidateExecution nparams indTypes numNested
      isUnsafe context) : FamilyValidationBlockResult :=
  { stats := execution.stats
    validationContext := execution.validationContext }

/-- A successful detailed normalization execution owns the exact result of
the family-validation pass which invoked its post-validation half. -/
theorem NormalizationCandidateExecution.familyValidationResult_run
    (execution : NormalizationCandidateExecution nparams indTypes numNested
      isUnsafe context)
    (produced : buildNormalizationCandidateExecution nparams indTypes
      numNested isUnsafe context = .ok execution) :
    observeFamilyValidationBlock nparams indTypes context =
      .ok execution.familyValidationResult := by
  unfold buildNormalizationCandidateExecution at produced
  rw [checkInductiveTypes_factor] at produced
  cases hrun : observeFamilyValidationBlock nparams indTypes context with
  | error error => simp_all [Bind.bind, Except.bind]
  | ok result =>
      simp only [hrun, Bind.bind, Except.bind] at produced
      obtain ⟨hstats, hcontext⟩ :=
        execution.fields_of_afterValidation result.stats
          result.validationContext produced
      cases result with
      | mk resultStats resultContext =>
          simp only [familyValidationResult] at hstats hcontext ⊢
          simp only [hstats, hcontext]

/-- The validation context retained by a successful nonempty detailed
execution has the exact input kernel environment. -/
theorem NormalizationCandidateExecution.validationContext_env
    (execution : NormalizationCandidateExecution nparams indTypes numNested
      isUnsafe context)
    (produced : buildNormalizationCandidateExecution nparams indTypes
      numNested isUnsafe context = .ok execution)
    (nonempty : indTypes.isEmpty = false) :
    execution.validationContext.env = context.env := by
  simpa only [NormalizationCandidateExecution.familyValidationResult] using
    execution.familyValidationResult.validationContext_env_of_run nonempty
      (execution.familyValidationResult_run produced)

/-- A successful detailed normalization execution retains the input kernel
environment even for the degenerate empty-block continuation. -/
theorem NormalizationCandidateExecution.validationContext_env_all
    (execution : NormalizationCandidateExecution nparams indTypes numNested
      isUnsafe context)
    (produced : buildNormalizationCandidateExecution nparams indTypes
      numNested isUnsafe context = .ok execution) :
    execution.validationContext.env = context.env := by
  simpa only [NormalizationCandidateExecution.familyValidationResult] using
    execution.familyValidationResult.validationContext_env_of_run_all
      (execution.familyValidationResult_run produced)

/-- A successful detailed normalization execution retains the input universe
parameters in its terminal validation context. -/
theorem NormalizationCandidateExecution.validationContext_lparams_all
    (execution : NormalizationCandidateExecution nparams indTypes numNested
      isUnsafe context)
    (produced : buildNormalizationCandidateExecution nparams indTypes
      numNested isUnsafe context = .ok execution) :
    execution.validationContext.lparams = context.lparams := by
  simpa only [NormalizationCandidateExecution.familyValidationResult] using
    execution.familyValidationResult.validationContext_lparams_of_run_all
      (execution.familyValidationResult_run produced)

/-- A successful detailed execution retains the input primitive-name mode in
its terminal validation context. -/
theorem NormalizationCandidateExecution.validationContext_allowPrimitive_all
    (execution : NormalizationCandidateExecution nparams indTypes numNested
      isUnsafe context)
    (produced : buildNormalizationCandidateExecution nparams indTypes
      numNested isUnsafe context = .ok execution) :
    execution.validationContext.allowPrimitive = context.allowPrimitive := by
  simpa only [NormalizationCandidateExecution.familyValidationResult] using
    execution.familyValidationResult
      |>.validationContext_allowPrimitive_of_run_all
        (execution.familyValidationResult_run produced)

/-- A successful detailed execution retains the family index-array size even
for the degenerate empty-block continuation. -/
theorem NormalizationCandidateExecution.validationNindicesSize_all
    (execution : NormalizationCandidateExecution nparams indTypes numNested
      isUnsafe context)
    (produced : buildNormalizationCandidateExecution nparams indTypes
      numNested isUnsafe context = .ok execution) :
    execution.stats.nindices.size = indTypes.length := by
  simpa only [NormalizationCandidateExecution.familyValidationResult] using
    execution.familyValidationResult.nindices_size_of_run_all
      (execution.familyValidationResult_run produced)

/-- Recover the universally quantified family-validation continuation
equation from one successful detailed execution. -/
theorem NormalizationCandidateExecution.familyValidation
    (execution : NormalizationCandidateExecution nparams indTypes numNested
      isUnsafe context)
    (produced : buildNormalizationCandidateExecution nparams indTypes
      numNested isUnsafe context = .ok execution) :
    ∀ {α} (k : InductiveStats → M α),
      checkInductiveTypes nparams indTypes.toArray k context =
        k execution.stats execution.validationContext := by
  intro α k
  rw [checkInductiveTypes_factor,
    execution.familyValidationResult_run produced]
  rfl

/-- The first family-type candidate retained by a successful nonempty
normalization execution contains the complete validator-selected parameter
prefix.  The public producer runs candidate observation from an empty local
context; the explicit context equality records that this is also the actual
family-validation entry context. -/
theorem NormalizationCandidateExecution.firstFamilyType_nparams_le_spineLength
    {source : InductiveType} {sources : List InductiveType}
    (execution : NormalizationCandidateExecution nparams
      (source :: sources) numNested isUnsafe context)
    (produced : buildNormalizationCandidateExecution nparams
      (source :: sources) numNested isUnsafe context = .ok execution)
    (context_lctx_eq : context.lctx = {}) :
    nparams ≤ execution.familyTypes.candidates.head.type.trace.spineLength := by
  have candidateContext_eq : { context with lctx := {} } = context := by
    cases context
    simp_all
  have validation : checkInductiveTypes nparams
      (source :: sources).toArray (fun _ => pure ()) context = .ok () := by
    simpa [ReaderT.pure, Pure.pure, Except.pure] using
      execution.familyValidation produced (fun _ => pure ())
  cases hCandidates : execution.familyTypes.candidates with
  | cons candidate candidates =>
      have producedFamilies := execution.familyTypes.produced
      rw [hCandidates] at producedFamilies
      have candidateRun := producedFamilies.head
      rw [candidateContext_eq] at candidateRun
      have terminals := execution.familyTerminals
      rw [hCandidates] at terminals
      cases terminals with
      | cons terminal tail =>
          have bound :=
            candidate.nparams_le_spineLength_of_firstFamilyValidation
              candidateRun terminal validation
          change nparams ≤ candidate.type.trace.spineLength
          exact bound

/-- The first family candidate retained by a successful normalization run
also fits strictly inside the family validator's own telescope-fuel budget.
Candidate construction may use the larger recursion-depth budget, so this
bound is recovered from the real validation success rather than inferred from
the candidate producer. -/
theorem
    NormalizationCandidateExecution.firstFamilyType_spineLength_lt_inductiveFuel
    {source : InductiveType} {sources : List InductiveType}
    (execution : NormalizationCandidateExecution nparams
      (source :: sources) numNested isUnsafe context)
    (produced : buildNormalizationCandidateExecution nparams
      (source :: sources) numNested isUnsafe context = .ok execution)
    (context_lctx_eq : context.lctx = {}) :
    execution.familyTypes.candidates.head.type.trace.spineLength <
      context.fuel.inductiveFuel := by
  have candidateContext_eq : { context with lctx := {} } = context := by
    cases context
    simp_all
  have validation : checkInductiveTypes nparams
      (source :: sources).toArray (fun _ => pure ()) context = .ok () := by
    simpa [ReaderT.pure, Pure.pure, Except.pure] using
      execution.familyValidation produced (fun _ => pure ())
  cases hCandidates : execution.familyTypes.candidates with
  | cons candidate candidates =>
      have producedFamilies := execution.familyTypes.produced
      rw [hCandidates] at producedFamilies
      have candidateRun := producedFamilies.head
      rw [candidateContext_eq] at candidateRun
      have annotations :=
        candidate.validationAnnotations_of_normalize candidateRun
      have candidate_context :=
        candidate.context_eq_of_normalize candidateRun
      subst context
      change candidate.type.trace.spineLength <
        candidate.type.context.fuel.inductiveFuel
      apply Classical.byContradiction
      intro hbound
      have fuel_le : candidate.type.context.fuel.inductiveFuel ≤
          candidate.type.trace.spineLength := by omega
      have hcheck := candidate.type.trace.rootCheck.valid
      have hwhnf := candidate.type.trace.rootWhnf_valid
      change TypeChecker.M.run candidate.type.context.env
          candidate.type.context.safety candidate.type.context.lctx
          candidate.type.context.lparams candidate.type.context.fuel
          (TypeChecker.checkType source.type) =
        .ok candidate.type.trace.rootCheck.inferred at hcheck
      change TypeChecker.M.run candidate.type.context.env
          candidate.type.context.safety candidate.type.context.lctx
          candidate.type.context.lparams candidate.type.context.fuel
          (TypeChecker.whnf source.type) =
        .ok candidate.type.trace.rootWhnf at hwhnf
      unfold checkInductiveTypes at validation
      simp only [readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
        ReaderT.bind, Bind.bind, Pure.pure, Except.pure, Except.bind]
        at validation
      rw [checkInductiveTypes.loopInd.eq_1] at validation
      have hsize : 0 < (source :: sources).toArray.size := by simp
      rw [dif_pos hsize] at validation
      rw [show (source :: sources).toArray[0] = source by rfl] at validation
      simp only [readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
        ReaderT.bind, Bind.bind, Pure.pure, Except.pure, Except.bind,
        liftExcept_apply, liftTypeChecker_apply] at validation
      cases hclosed : candidate.type.context.env.checkNoMVarNoFVar
          source.name source.type with
      | error error =>
          rw [hclosed] at validation
          contradiction
      | ok _ =>
          rw [hclosed, hcheck, hwhnf] at validation
          exact candidate.type.trace
            |>.checkInductiveTypes_loop_not_ok_of_candidate_fuel
              (stats := InductiveStats.initial
                (candidate.type.context.lparams.map .param))
              (nparams := nparams) (i := 0) (nindices := 0)
              (fuel := candidate.type.context.fuel.inductiveFuel) _ fuel_le
              rfl annotations () validation

/-- The common result universe and its cached nonzero decision retained by a
successful nonempty block are exactly the terminal sort and syntactic
`isNeverZero` decision selected by its first source-indexed family candidate.
Later families only compare their levels against this value, and the outer
validation loop preserves both fields to the final statistics record. -/
theorem NormalizationCandidateExecution.firstFamilyType_resultState_eq
    {source : InductiveType} {sources : List InductiveType}
    (execution : NormalizationCandidateExecution nparams
      (source :: sources) numNested isUnsafe context)
    (produced : buildNormalizationCandidateExecution nparams
      (source :: sources) numNested isUnsafe context = .ok execution)
    (context_lctx_eq : context.lctx = {})
    (resultLevel : Level)
    (terminal : execution.familyTypes.candidates.head.type.trace.terminalResult =
      .sort resultLevel) :
    execution.stats.resultLevel = resultLevel ∧
      execution.stats.isNotZero = resultLevel.isNeverZero := by
  have hcount := execution.firstFamilyType_nparams_le_spineLength produced
    context_lctx_eq
  have hfuel :=
    execution.firstFamilyType_spineLength_lt_inductiveFuel produced
      context_lctx_eq
  have validation := execution.familyValidationResult_run produced
  have candidateContext_eq : { context with lctx := {} } = context := by
    cases context
    simp_all
  cases hCandidates : execution.familyTypes.candidates with
  | cons candidate candidates =>
      rw [hCandidates] at hcount hfuel terminal
      change nparams ≤ candidate.type.trace.spineLength at hcount
      change candidate.type.trace.spineLength < context.fuel.inductiveFuel
        at hfuel
      change candidate.type.trace.terminalResult = .sort resultLevel
        at terminal
      have producedFamilies := execution.familyTypes.produced
      rw [hCandidates] at producedFamilies
      have candidateRun := producedFamilies.head
      rw [candidateContext_eq] at candidateRun
      have annotations :=
        candidate.validationAnnotations_of_normalize candidateRun
      have candidate_context :=
        candidate.context_eq_of_normalize candidateRun
      subst context
      have hcheck := candidate.type.trace.rootCheck.valid
      have hwhnf := candidate.type.trace.rootWhnf_valid
      change TypeChecker.M.run candidate.type.context.env
          candidate.type.context.safety candidate.type.context.lctx
          candidate.type.context.lparams candidate.type.context.fuel
          (TypeChecker.checkType source.type) =
        .ok candidate.type.trace.rootCheck.inferred at hcheck
      change TypeChecker.M.run candidate.type.context.env
          candidate.type.context.safety candidate.type.context.lctx
          candidate.type.context.lparams candidate.type.context.fuel
          (TypeChecker.whnf source.type) =
        .ok candidate.type.trace.rootWhnf at hwhnf
      have terminalForall :
          candidate.type.trace.terminalResult.isForall = false := by
        rw [terminal]
        rfl
      unfold observeFamilyValidationBlock checkInductiveTypes at validation
      simp only [readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
        ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure, Except.pure,
        Except.bind] at validation
      rw [checkInductiveTypes.loopInd.eq_1] at validation
      have hsize : 0 < (source :: sources).toArray.size := by simp
      rw [dif_pos hsize] at validation
      rw [show (source :: sources).toArray[0] = source by rfl] at validation
      simp only [readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
        ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure, Except.pure,
        Except.bind, liftExcept_apply, liftTypeChecker_apply] at validation
      cases hclosed : candidate.type.context.env.checkNoMVarNoFVar
          source.name source.type with
      | error error =>
          rw [hclosed] at validation
          contradiction
      | ok _ =>
          rw [hclosed, hcheck, hwhnf] at validation
          simp only [Except.bind] at validation
          rw [candidate.type.trace.checkInductiveTypes_loop_of_candidate
            (stats := InductiveStats.initial
              (candidate.type.context.lparams.map .param))
            (nparams := nparams) (i := 0) (nindices := 0)
            (fuel := candidate.type.context.fuel.inductiveFuel)
            (remaining := nparams) (hi := Nat.zero_add nparams)
            (hcount := hcount) (hfuel := hfuel) (hempty := rfl)
            (hannotations := annotations) (hterminal := terminalForall)]
            at validation
          rw [terminal] at validation
          have hensure : TypeChecker.M.run
              candidate.type.trace.terminalContext.env
              candidate.type.trace.terminalContext.safety
              candidate.type.trace.terminalContext.lctx
              candidate.type.trace.terminalContext.lparams
              candidate.type.trace.terminalContext.fuel
              (TypeChecker.ensureSort (.sort resultLevel)) =
            .ok (.sort resultLevel) := by rfl
          simp only [ReaderT.bind, Bind.bind, liftTypeChecker_apply]
            at validation
          rw [hensure] at validation
          simp only [Except.bind] at validation
          rw [if_pos (show ((InductiveStats.initial
              (candidate.type.context.lparams.map .param)).indConsts).isEmpty =
                true from rfl)] at validation
          simp only [Expr.sortLevel!, InductiveStats.initial, Nat.zero_add,
            ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure, Except.pure,
            Except.bind] at validation
          let firstStats : InductiveStats := {
            lctx := candidate.type.trace.terminalContext.lctx
            levels := candidate.type.context.lparams.map .param
            resultLevel
            nindices := #[candidate.type.trace.spineLength - nparams]
            indConsts := #[.const source.name
              (candidate.type.context.lparams.map .param)]
            params := (candidate.type.trace.parameterList nparams).toArray
            isNotZero := resultLevel.isNeverZero }
          have validation' : observeFamilyValidationOuterLoop nparams
              (source :: sources).toArray 1 firstStats
              candidate.type.trace.terminalContext =
            .ok execution.familyValidationResult := by
            simpa [observeFamilyValidationOuterLoop, firstStats] using
              validation
          have terminalLparams :=
            candidate.type.trace.terminalContext_lparams
          have parameterLength :=
            candidate.type.trace.parameterList_length hcount
          have firstInvariant :
              familyValidationOuterStatsInvariant nparams
                (source :: sources).toArray 1 firstStats
                candidate.type.trace.terminalContext := by
            unfold familyValidationOuterStatsInvariant
            simp [firstStats, terminalLparams, parameterLength]
          have finalState := familyValidationOuter_resultState_of_run
            nparams (source :: sources).toArray 1 firstStats
            candidate.type.trace.terminalContext
            execution.familyValidationResult (by omega) firstInvariant
            validation'
          exact ⟨
            by
              simpa only [
                NormalizationCandidateExecution.familyValidationResult,
                firstStats] using finalState.1,
            by
              simpa only [
                NormalizationCandidateExecution.familyValidationResult,
                firstStats] using finalState.2⟩

/-- Result-level projection of `firstFamilyType_resultState_eq`. -/
theorem NormalizationCandidateExecution.firstFamilyType_resultLevel_eq
    {source : InductiveType} {sources : List InductiveType}
    (execution : NormalizationCandidateExecution nparams
      (source :: sources) numNested isUnsafe context)
    (produced : buildNormalizationCandidateExecution nparams
      (source :: sources) numNested isUnsafe context = .ok execution)
    (context_lctx_eq : context.lctx = {})
    (resultLevel : Level)
    (terminal : execution.familyTypes.candidates.head.type.trace.terminalResult =
      .sort resultLevel) :
    execution.stats.resultLevel = resultLevel :=
  (execution.firstFamilyType_resultState_eq produced context_lctx_eq
    resultLevel terminal).1

/-- Reindex the first-family result-state theorem onto the complete assembled
candidate stored by the detailed execution. -/
theorem NormalizationCandidateExecution.firstFamily_resultState_eq
    {source : InductiveType} {sources : List InductiveType}
    (execution : NormalizationCandidateExecution nparams
      (source :: sources) numNested isUnsafe context)
    (produced : buildNormalizationCandidateExecution nparams
      (source :: sources) numNested isUnsafe context = .ok execution)
    (context_lctx_eq : context.lctx = {})
    (resultLevel : Level)
    (terminal : execution.candidate.families.head.familyType.type.trace.terminalResult =
      .sort resultLevel) :
    execution.stats.resultLevel = resultLevel ∧
      execution.stats.isNotZero = resultLevel.isNeverZero := by
  apply execution.firstFamilyType_resultState_eq produced context_lctx_eq
    resultLevel
  change execution.families.candidates.head.familyType.type.trace.terminalResult =
    .sort resultLevel at terminal
  rw [execution.families.produced.head_familyType] at terminal
  exact terminal

/-- Result-level projection of `firstFamily_resultState_eq`. -/
theorem NormalizationCandidateExecution.firstFamily_resultLevel_eq
    {source : InductiveType} {sources : List InductiveType}
    (execution : NormalizationCandidateExecution nparams
      (source :: sources) numNested isUnsafe context)
    (produced : buildNormalizationCandidateExecution nparams
      (source :: sources) numNested isUnsafe context = .ok execution)
    (context_lctx_eq : context.lctx = {})
    (resultLevel : Level)
    (terminal : execution.candidate.families.head.familyType.type.trace.terminalResult =
      .sort resultLevel) :
    execution.stats.resultLevel = resultLevel :=
  (execution.firstFamily_resultState_eq produced context_lctx_eq resultLevel
    terminal).1

/-- Cached nonzero-decision projection of `firstFamily_resultState_eq`. -/
theorem NormalizationCandidateExecution.firstFamily_isNotZero_eq
    {source : InductiveType} {sources : List InductiveType}
    (execution : NormalizationCandidateExecution nparams
      (source :: sources) numNested isUnsafe context)
    (produced : buildNormalizationCandidateExecution nparams
      (source :: sources) numNested isUnsafe context = .ok execution)
    (context_lctx_eq : context.lctx = {})
    (resultLevel : Level)
    (terminal : execution.candidate.families.head.familyType.type.trace.terminalResult =
      .sort resultLevel) :
    execution.stats.isNotZero = resultLevel.isNeverZero :=
  (execution.firstFamily_resultState_eq produced context_lctx_eq resultLevel
    terminal).2

/-- Erase a successful detailed execution back to the ordinary candidate
producer without rerunning or independently selecting family validation. -/
theorem NormalizationCandidateExecution.producesFromBuildExecution
    (execution : NormalizationCandidateExecution nparams indTypes numNested
      isUnsafe context)
    (produced : buildNormalizationCandidateExecution nparams indTypes
      numNested isUnsafe context = .ok execution) :
    buildNormalizationCandidate nparams indTypes numNested isUnsafe context =
      .ok execution.candidate :=
  execution.produces (execution.familyValidation produced)

/-- Complete retained family-validation run for an arbitrary source-ordered
block.

`run` is the real validator execution, so every later family has already
passed the kernel's definitional parameter comparison and result-level
equivalence phase.  The remaining equations expose the terminal invariants
which Lean asserts before invoking the continuation. -/
structure FamilyValidationBlockRun (nparams : Nat)
    (indTypes : List InductiveType) (context : Context) where
  result : FamilyValidationBlockResult
  run : observeFamilyValidationBlock nparams indTypes context = .ok result
  params_size : result.stats.params.size = nparams
  nindices_size : result.stats.nindices.size = indTypes.length
  indConsts_size : result.stats.indConsts.size = indTypes.length

namespace FamilyValidationBlockRun

/-- Execute and retain the ordinary family validator.  The explicit terminal
checks mirror its internal assertions and make malformed instrumentation fail
instead of yielding a weaker certificate. -/
def buildExecution (nparams : Nat) (indTypes : List InductiveType)
    (context : Context) :
    Except Exception (FamilyValidationBlockRun nparams indTypes context) :=
  match hrun : observeFamilyValidationBlock nparams indTypes context with
  | .error error => .error error
  | .ok result =>
    if hparams : result.stats.params.size = nparams then
      if hnindices : result.stats.nindices.size = indTypes.length then
        if hconsts : result.stats.indConsts.size = indTypes.length then
          .ok {
            result
            run := hrun
            params_size := hparams
            nindices_size := hnindices
            indConsts_size := hconsts }
        else .error (.other "family-validation constant-count invariant failed")
      else .error (.other "family-validation index-count invariant failed")
    else .error (.other "family-validation parameter-count invariant failed")

/-- Package one successful nonempty arbitrary-block family run with the exact
terminal counter invariants proved from that execution. -/
def of_run
    (nonempty : indTypes.isEmpty = false)
    (result : FamilyValidationBlockResult)
    (run : observeFamilyValidationBlock nparams indTypes context =
      .ok result) :
    FamilyValidationBlockRun nparams indTypes context := by
  have sizes := result.sizes_of_run nonempty run
  exact {
    result
    run
    params_size := sizes.1
    nindices_size := sizes.2.1
    indConsts_size := sizes.2.2 }

/-- Shared parameters selected by the first family and definitionally checked
against every later family. -/
def parameters (run : FamilyValidationBlockRun nparams indTypes context) :
    Array Expr :=
  run.result.stats.params

/-- Common result universe selected by the first family and equivalence-
checked against every later family. -/
def resultLevel (run : FamilyValidationBlockRun nparams indTypes context) :
    Level :=
  run.result.stats.resultLevel

/-- The exact outer-loop execution underlying this retained block run. -/
theorem outerLoop_run
    (run : FamilyValidationBlockRun nparams indTypes context) :
    checkInductiveTypes.loopInd nparams indTypes.toArray
        (fun stats => fun validationContext =>
          .ok ⟨stats, validationContext⟩)
        0 (InductiveStats.initial (context.lparams.map .param)) context =
      .ok run.result := by
  have hrun := run.run
  unfold observeFamilyValidationBlock checkInductiveTypes at hrun
  simp only [readThe, MonadReader.read, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure, Except.pure,
    Except.bind] at hrun
  exact hrun

/-- Producer-owned source-indexed parameter-comparison trace.  The choice is
only the proof representation reconstructed from `run`; its executable
statistics, contexts, and comparison steps are fixed by `outerLoop_run`. -/
noncomputable def parameterComparisonTrace
    (run : FamilyValidationBlockRun nparams indTypes context) :
    FamilyParameterComparisonBlockTrace nparams indTypes.toArray 0
      (InductiveStats.initial (context.lparams.map .param)) context :=
  Classical.choice
    (FamilyParameterComparisonBlockTrace.exists_of_run run.outerLoop_run)

/-- The reconstructed trace reaches the exact result already retained by the
family block run. -/
theorem parameterComparisonTrace_result
    (run : FamilyValidationBlockRun nparams indTypes context) :
    run.parameterComparisonTrace.result = run.result := by
  have factor := run.parameterComparisonTrace.factor
    (fun stats => fun validationContext =>
      .ok (⟨stats, validationContext⟩ : FamilyValidationBlockResult))
  rw [run.outerLoop_run] at factor
  exact (Except.ok.inj factor).symm

/-- Grouped parameter comparisons in exact source-family order. -/
noncomputable def parameterComparisons
    (run : FamilyValidationBlockRun nparams indTypes context) :
    List (List CandidateIsDefEqStep) :=
  run.parameterComparisonTrace.comparisons

/-- The retained comparison groups are indexed by every source family,
without truncation or an independently supplied list. -/
theorem parameterComparisons_length
    (run : FamilyValidationBlockRun nparams indTypes context) :
    run.parameterComparisons.length = indTypes.length := by
  simpa [parameterComparisons] using
    run.parameterComparisonTrace.comparisons_length

/-- Exact per-family comparison counts for a nonempty retained block: zero
for the first family and `nparams` for every later family. -/
theorem parameterComparison_lengths_shape
    (run : FamilyValidationBlockRun nparams indTypes context)
    (nonempty : indTypes.isEmpty = false) :
    run.parameterComparisons.map List.length =
      0 :: List.replicate (indTypes.length - 1) nparams := by
  have size_pos : 0 < indTypes.toArray.size := by
    cases indTypes with
    | nil => simp at nonempty
    | cons head tail => simp
  simpa [parameterComparisons] using
    run.parameterComparisonTrace.comparison_lengths_of_initial size_pos

/-- Every comparison exposed by a retained block run is the exact successful
kernel execution from the corresponding family telescope. -/
theorem parameterComparison_valid
    (run : FamilyValidationBlockRun nparams indTypes context)
    (familyMember : familyComparisons ∈ run.parameterComparisons)
    (comparisonMember : comparison ∈ familyComparisons) :
    comparison.Valid :=
  run.parameterComparisonTrace.comparison_valid familyMember
    comparisonMember

end FamilyValidationBlockRun

/-- Project the complete proof-carrying family-validation owner from the same
successful detailed normalization execution. -/
def NormalizationCandidateExecution.familyValidationBlockRun
    (execution : NormalizationCandidateExecution nparams indTypes numNested
      isUnsafe context)
    (produced : buildNormalizationCandidateExecution nparams indTypes
      numNested isUnsafe context = .ok execution)
    (nonempty : indTypes.isEmpty = false) :
    FamilyValidationBlockRun nparams indTypes context :=
  FamilyValidationBlockRun.of_run nonempty execution.familyValidationResult
    (execution.familyValidationResult_run produced)

/-- Project the exact source-indexed family parameter-comparison trace from
the retained detailed normalization execution. -/
noncomputable def NormalizationCandidateExecution.familyParameterComparisonTrace
    (execution : NormalizationCandidateExecution nparams indTypes numNested
      isUnsafe context)
    (produced : buildNormalizationCandidateExecution nparams indTypes
      numNested isUnsafe context = .ok execution)
    (nonempty : indTypes.isEmpty = false) :
    FamilyParameterComparisonBlockTrace nparams indTypes.toArray 0
      (InductiveStats.initial (context.lparams.map .param)) context :=
  (execution.familyValidationBlockRun produced nonempty).parameterComparisonTrace

/-- The first family validator and the first family normalization candidate
reach the same exact terminal reader context.

The detailed producer independently retains both traversals.  Root WHNF
determinism aligns their starting expressions, and
`FamilyTypeParameterComparisonTrace.result_eq_candidate` then aligns the
whole parameter/index telescope in one step. -/
theorem NormalizationCandidateExecution.firstFamilyComparisonContext_eq
    {source : InductiveType} {sources : List InductiveType}
    (execution : NormalizationCandidateExecution nparams
      (source :: sources) numNested isUnsafe context)
    (produced : buildNormalizationCandidateExecution nparams
      (source :: sources) numNested isUnsafe context = .ok execution)
    (context_lctx_eq : context.lctx = {}) :
    (execution.familyParameterComparisonTrace produced (by simp)).firstContext =
      execution.familyTypes.candidates.head.type.trace.terminalContext := by
  have hcount := execution.firstFamilyType_nparams_le_spineLength produced
    context_lctx_eq
  have hfuel := execution.firstFamilyType_spineLength_lt_inductiveFuel
    produced context_lctx_eq
  cases hCandidates : execution.familyTypes.candidates with
  | cons candidate candidates =>
      rw [hCandidates] at hcount hfuel
      simp only [CandidateList.head] at hcount hfuel
      simp only [CandidateList.head]
      have producedFamilies := execution.familyTypes.produced
      rw [hCandidates] at producedFamilies
      have candidateRun := producedFamilies.head
      have candidateContext_eq : { context with lctx := {} } = context := by
        cases context
        simp_all
      rw [candidateContext_eq] at candidateRun
      have annotations :=
        candidate.validationAnnotations_of_normalize candidateRun
      have candidate_context :=
        candidate.context_eq_of_normalize candidateRun
      subst context
      have terminals := execution.familyTerminals
      rw [hCandidates] at terminals
      cases terminals with
      | cons terminal tail =>
          have terminalForall :
              candidate.type.trace.terminalResult.isForall = false := by
            rw [terminal]
            rfl
          generalize execution.familyParameterComparisonTrace produced
            (by simp) = trace
          cases trace with
          | firstFamily dIdx stats validationContext inBounds closed inferred
              root checkType rootWhnf telescope sorted ensureSort isFirst tail =>
              have candidateWhnf := candidate.type.trace.rootWhnf_valid
              have candidateWhnf' : CandidateWhnfStep.Valid
                  ⟨candidate.type.context,
                    (source :: sources).toArray[0].type,
                    candidate.type.trace.rootWhnf⟩ := by
                simpa using candidateWhnf
              have root_eq : root = candidate.type.trace.rootWhnf :=
                Except.ok.inj (rootWhnf.symm.trans candidateWhnf')
              subst root
              have result_eq :=
                FamilyTypeParameterComparisonTrace.result_eq_candidate
                  candidate.type.trace telescope nparams (by omega) hcount
                  hfuel rfl annotations terminalForall
              exact congrArg FamilyTypeParameterComparisonTrace.Result.context
                result_eq
          | laterFamily dIdx stats validationContext inBounds closed inferred
              root checkType rootWhnf telescope sorted ensureSort isLater
              resultLevelCompatible tail =>
              have first : telescope.result.stats.indConsts.isEmpty = true := by
                rw [telescope.result_indConsts_eq]
                rfl
              rw [first] at isLater
              contradiction
          | terminal dIdx stats validationContext outOfBounds =>
              simp at outOfBounds

/-- Kernel equality executions grouped by source family, projected directly
from the normalization producer. -/
noncomputable def NormalizationCandidateExecution.familyParameterComparisons
    (execution : NormalizationCandidateExecution nparams indTypes numNested
      isUnsafe context)
    (produced : buildNormalizationCandidateExecution nparams indTypes
      numNested isUnsafe context = .ok execution)
    (nonempty : indTypes.isEmpty = false) :
    List (List CandidateIsDefEqStep) :=
  (execution.familyValidationBlockRun produced nonempty).parameterComparisons

/-- The producer's grouped comparison inventory has the exact first/later
family shape selected by validation. -/
theorem NormalizationCandidateExecution.familyParameterComparison_lengths
    (execution : NormalizationCandidateExecution nparams indTypes numNested
      isUnsafe context)
    (produced : buildNormalizationCandidateExecution nparams indTypes
      numNested isUnsafe context = .ok execution)
    (nonempty : indTypes.isEmpty = false) :
    (execution.familyParameterComparisons produced nonempty).map List.length =
      0 :: List.replicate (indTypes.length - 1) nparams :=
  (execution.familyValidationBlockRun produced nonempty)
    |>.parameterComparison_lengths_shape nonempty

/-- Source-indexed constructor traces for every family in a block.  The
natural index advances with the source list, so a trace for one family cannot
be reused at another family ordinal. -/
inductive ConstructorBlockValidationTraces
    (stats : InductiveStats) (isUnsafe : Bool) (context : Context) :
    Nat → List InductiveType → Type where
  | nil {familyIdx : Nat} :
      ConstructorBlockValidationTraces stats isUnsafe context familyIdx []
  | cons {familyIdx : Nat} {type : InductiveType}
      {types : List InductiveType}
      (head : ConstructorListValidationTrace stats isUnsafe familyIdx
        context {} type.ctors)
      (tail : ConstructorBlockValidationTraces stats isUnsafe context
        (familyIdx + 1) types) :
      ConstructorBlockValidationTraces stats isUnsafe context familyIdx
        (type :: types)

namespace ConstructorBlockValidationTraces

/-- Family-, constructor-, and field-ordered recursive-target matrix selected
by the executable arbitrary-block validator. -/
def targets :
    ConstructorBlockValidationTraces stats isUnsafe context familyIdx types →
      List (List (List (Option ConstructorPositivityTrace.Target)))
  | .nil => []
  | .cons head tail => head.targets :: tail.targets

/-- Execute each source-indexed list trace in the one shared post-family
context. -/
def buildExecution (stats : InductiveStats) (isUnsafe : Bool)
    (context : Context) :
    (familyIdx : Nat) → (types : List InductiveType) →
      Except Exception
        (ConstructorBlockValidationTraces stats isUnsafe context
          familyIdx types)
  | _, [] => .ok .nil
  | familyIdx, type :: types =>
    match ConstructorListValidationTrace.buildExecution stats isUnsafe
        familyIdx context {} type.ctors with
    | .error error => .error error
    | .ok head =>
      match buildExecution stats isUnsafe context (familyIdx + 1) types with
      | .error error => .error error
      | .ok tail => .ok (.cons head tail)

/-- Successful execution of the real named family loop admits the complete
source-indexed block trace decomposition.  The proof follows the same family
recursion and uses the already-transparent constructor-list decomposition at
each head. -/
theorem buildExecution_ok_of_loop_run
    (success : checkConstructorsLoop context.env stats isUnsafe familyIdx
      types context = .ok ()) :
    ∃ traces, buildExecution stats isUnsafe context familyIdx types =
      .ok traces := by
  induction types generalizing familyIdx with
  | nil => exact ⟨.nil, rfl⟩
  | cons type types ih =>
      unfold checkConstructorsLoop at success
      simp only [ReaderT.bind, Bind.bind] at success
      cases hhead : checkConstructorFold context.env stats isUnsafe familyIdx
          {} type.ctors context with
      | error error => simp_all [Except.bind]
      | ok seen =>
          rw [hhead] at success
          simp only [Except.bind] at success
          obtain ⟨head, headBuild⟩ :=
            ConstructorListValidationTrace.buildExecution_ok_of_fold_run
              hhead
          obtain ⟨tail, tailBuild⟩ := ih success
          unfold buildExecution
          rw [headBuild, tailBuild]
          exact ⟨.cons head tail, rfl⟩

end ConstructorBlockValidationTraces

/-- Complete operational constructor-validation owner for an arbitrary
mutual block.  `run` is the actual block call; `traces` retains every
family/constructor/field branch, including cross-family target ordinals and
recursive-Pi paths. -/
structure ConstructorBlockValidationRun
    (indTypes : List InductiveType) (stats : InductiveStats)
    (isUnsafe : Bool) (context : Context) where
  traces : ConstructorBlockValidationTraces stats isUnsafe context 0 indTypes
  run : checkConstructors indTypes.toArray stats isUnsafe context = .ok ()

namespace ConstructorBlockValidationRun

/-- Execute the real block validator and retain the exact dependent trace
hierarchy for that same source list. -/
def buildExecution (indTypes : List InductiveType)
    (stats : InductiveStats) (isUnsafe : Bool) (context : Context) :
    Except Exception
      (ConstructorBlockValidationRun indTypes stats isUnsafe context) :=
  match hrun : checkConstructors indTypes.toArray stats isUnsafe context with
  | .error error => .error error
  | .ok () =>
    match ConstructorBlockValidationTraces.buildExecution stats isUnsafe
        context 0 indTypes with
    | .error error => .error error
    | .ok traces => .ok ⟨traces, hrun⟩

private theorem buildExecution_match_ok
    {indTypes : List InductiveType} {stats : InductiveStats}
    {isUnsafe : Bool} {context : Context}
    (result : Except Exception Unit)
    (toRun : result = .ok () →
      checkConstructors indTypes.toArray stats isUnsafe context = .ok ())
    (result_ok : result = .ok ())
    (traces : ConstructorBlockValidationTraces stats isUnsafe context 0
      indTypes)
    (tracesBuild : ConstructorBlockValidationTraces.buildExecution stats
      isUnsafe context 0 indTypes = .ok traces) :
    (match hrun : result with
    | .error error => Except.error error
    | .ok () =>
      match ConstructorBlockValidationTraces.buildExecution stats isUnsafe
          context 0 indTypes with
      | .error error => Except.error error
      | .ok actual =>
        Except.ok (show ConstructorBlockValidationRun indTypes stats
            isUnsafe context from {
          traces := actual
          run := toRun hrun })) =
      .ok (show ConstructorBlockValidationRun indTypes stats isUnsafe
          context from {
        traces
        run := toRun result_ok }) := by
  subst result
  simp [tracesBuild]

/-- Every arbitrary mutual block accepted by the real constructor validator
has a transparently computed, complete family/constructor/field trace. -/
theorem buildExecution_ok_of_run
    (success : checkConstructors indTypes.toArray stats isUnsafe context =
      .ok ()) :
    ∃ validation, buildExecution indTypes stats isUnsafe context =
      .ok validation := by
  have loopSuccess : checkConstructorsLoop context.env stats isUnsafe 0
      indTypes context = .ok () := by
    unfold checkConstructors at success
    simp only [ReaderT.bind, Bind.bind] at success
    rw [liftTypeChecker_apply] at success
    have hget :
        TypeChecker.M.run context.env context.safety context.lctx
            context.lparams context.fuel TypeChecker.getEnv =
          .ok context.env := by
      rfl
    rw [hget] at success
    simpa only [Except.bind] using success
  obtain ⟨traces, tracesBuild⟩ :=
    ConstructorBlockValidationTraces.buildExecution_ok_of_loop_run
      loopSuccess
  refine ⟨⟨traces, success⟩, ?_⟩
  unfold buildExecution
  exact buildExecution_match_ok
    (result := checkConstructors indTypes.toArray stats isUnsafe context)
    (toRun := fun result_ok => result_ok) success traces tracesBuild

/-- Compute the complete arbitrary-block validation trace selected by one
successful real constructor-validation equation. -/
def of_run
    (success : checkConstructors indTypes.toArray stats isUnsafe context =
      .ok ()) :
    ConstructorBlockValidationRun indTypes stats isUnsafe context :=
  match h : buildExecution indTypes stats isUnsafe context with
  | .ok validation => validation
  | .error _ => absurd (buildExecution_ok_of_run success) (by simp [h])

/-- Exact arbitrary-block decomposition/recomposition contract for
constructor validation. -/
theorem nonempty_iff_checkConstructors_ok :
    Nonempty (ConstructorBlockValidationRun indTypes stats isUnsafe context) ↔
      checkConstructors indTypes.toArray stats isUnsafe context = .ok () := by
  constructor
  · rintro ⟨validation⟩
    exact validation.run
  · intro success
    exact ⟨of_run success⟩

end ConstructorBlockValidationRun

/-- Project the complete arbitrary-block constructor trace directly from the
exact successful constructor phase retained by a normalization execution. -/
def NormalizationCandidateExecution.constructorValidation
    (execution : NormalizationCandidateExecution nparams indTypes numNested
      isUnsafe context) :
    ConstructorBlockValidationRun indTypes execution.stats isUnsafe
      { execution.validationContext with env := execution.familyEnv } :=
  ConstructorBlockValidationRun.of_run execution.constructorRun

/-- The complete retained operational constructor-validation run for one
singleton family. -/
structure ConstructorValidationRun
    (indType : InductiveType) (stats : InductiveStats)
    (isUnsafe : Bool) (context : Context) where
  trace : ConstructorListValidationTrace stats isUnsafe 0 context {}
    indType.ctors

namespace ConstructorValidationRun

/-- Transparent decomposition of the ordinary singleton constructor
validator.  Successful output is executable data rather than a
`Classical.choice`, which lets subsequent D2/D3 audits compute over the exact
retained branch structure. -/
def buildExecution (indType : InductiveType) (stats : InductiveStats)
    (isUnsafe : Bool) (context : Context) :
    Except Exception
      (ConstructorValidationRun indType stats isUnsafe context) :=
  match ConstructorListValidationTrace.buildExecution stats isUnsafe 0
      context {} indType.ctors with
  | .error error => .error error
  | .ok trace => .ok ⟨trace⟩

/-- The transparent singleton decomposition succeeds on every source family
accepted by the real constructor validator. -/
theorem buildExecution_ok_of_run
    (success : checkConstructors #[indType] stats isUnsafe context = .ok ()) :
    ∃ validation, buildExecution indType stats isUnsafe context =
      .ok validation := by
  rw [checkConstructors_singleton_eq_checkConstructorList] at success
  unfold checkConstructorList at success
  cases hfold : checkConstructorFold context.env stats isUnsafe 0 {}
      indType.ctors context with
  | error err => simp_all [Functor.map, Except.map]
  | ok result =>
      obtain ⟨trace, htrace⟩ :=
        ConstructorListValidationTrace.buildExecution_ok_of_fold_run hfold
      unfold buildExecution
      rw [htrace]
      exact ⟨_, rfl⟩

/-- Recomposition: retained operational evidence replays the real singleton
`checkConstructors` execution exactly. -/
theorem run
    (validation : ConstructorValidationRun indType stats isUnsafe context) :
    checkConstructors #[indType] stats isUnsafe context = .ok () := by
  rw [checkConstructors_singleton_eq_checkConstructorList]
  exact validation.trace.run

/-- Decomposition: every successful real singleton `checkConstructors` run
has complete retained operational evidence. -/
theorem nonempty_of_run
    (success : checkConstructors #[indType] stats isUnsafe context = .ok ()) :
    Nonempty (ConstructorValidationRun indType stats isUnsafe context) := by
  rw [checkConstructors_singleton_eq_checkConstructorList] at success
  unfold checkConstructorList at success
  cases hfold : checkConstructorFold context.env stats isUnsafe 0 {}
      indType.ctors context with
  | error err =>
      simp_all [Functor.map, Except.map]
  | ok result =>
      obtain ⟨trace⟩ :=
        ConstructorListValidationTrace.exists_of_fold_run hfold
      exact ⟨⟨trace⟩⟩

/-- Choose the operational shape supplied by a successful run by replaying
the transparent decomposition.  The success premise only discharges the
impossible error branch, so the retained evidence is computed by
`buildExecution` rather than selected through `Classical.choice`. -/
def of_run
    (success : checkConstructors #[indType] stats isUnsafe context = .ok ()) :
    ConstructorValidationRun indType stats isUnsafe context :=
  match h : buildExecution indType stats isUnsafe context with
  | .ok validation => validation
  | .error _ => absurd (buildExecution_ok_of_run success) (by simp [h])

/-- Exact decomposition/recomposition contract for singleton constructor
validation. -/
theorem nonempty_iff_checkConstructors_ok :
    Nonempty (ConstructorValidationRun indType stats isUnsafe context) ↔
      checkConstructors #[indType] stats isUnsafe context = .ok () := by
  constructor
  · rintro ⟨validation⟩
    exact validation.run
  · exact nonempty_of_run

/-- Any phase-specific executable error excludes a successful retained run. -/
theorem not_nonempty_of_error
    (failure : checkConstructors #[indType] stats isUnsafe context = .error err) :
    ¬ Nonempty (ConstructorValidationRun indType stats isUnsafe context) := by
  intro validation
  have success := nonempty_iff_checkConstructors_ok.mp validation
  rw [failure] at success
  contradiction

end ConstructorValidationRun

/--
info: 'Lean4Lean.AddInductive.FamilyTypeParameterComparisonTrace.result_context_fuel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms FamilyTypeParameterComparisonTrace.result_context_fuel

/--
info: 'Lean4Lean.AddInductive.FamilyTypeParameterComparisonTrace.result_context_safety' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms FamilyTypeParameterComparisonTrace.result_context_safety

/--
info: 'Lean4Lean.AddInductive.FamilyParameterComparisonBlockTrace.result_safety' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms FamilyParameterComparisonBlockTrace.result_safety

/--
info: 'Lean4Lean.AddInductive.FamilyTypeParameterComparisonTrace.startIndex_le_nparams' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms FamilyTypeParameterComparisonTrace.startIndex_le_nparams

/--
info: 'Lean4Lean.AddInductive.FamilyTypeParameterComparisonTrace.comparison_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms FamilyTypeParameterComparisonTrace.comparison_valid

/--
info: 'Lean4Lean.AddInductive.FamilyTypeParameterComparisonTrace.comparisons_length_of_laterFamily' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms FamilyTypeParameterComparisonTrace.comparisons_length_of_laterFamily

/--
info: 'Lean4Lean.AddInductive.FamilyTypeParameterComparisonTrace.factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms FamilyTypeParameterComparisonTrace.factor

/--
info: 'Lean4Lean.AddInductive.FamilyTypeParameterComparisonTrace.result_eq_candidate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms FamilyTypeParameterComparisonTrace.result_eq_candidate

/--
info: 'Lean4Lean.AddInductive.FamilyTypeParameterComparisonTrace.exists_of_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms FamilyTypeParameterComparisonTrace.exists_of_run

/--
info: 'Lean4Lean.AddInductive.FamilyTypeParameterComparisonTrace.comparisons_eq_nil_of_firstFamily' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms FamilyTypeParameterComparisonTrace.comparisons_eq_nil_of_firstFamily

/--
info: 'Lean4Lean.AddInductive.FamilyParameterComparisonBlockTrace.comparison_valid' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms FamilyParameterComparisonBlockTrace.comparison_valid

/--
info: 'Lean4Lean.AddInductive.FamilyParameterComparisonBlockTrace.comparison_lengths_of_initial' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms FamilyParameterComparisonBlockTrace.comparison_lengths_of_initial

/--
info: 'Lean4Lean.AddInductive.FamilyParameterComparisonBlockTrace.factor' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms FamilyParameterComparisonBlockTrace.factor

/--
info: 'Lean4Lean.AddInductive.NormalizationCandidateExecution.firstFamilyComparisonContext_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NormalizationCandidateExecution.firstFamilyComparisonContext_eq

/--
info: 'Lean4Lean.AddInductive.FamilyParameterComparisonBlockTrace.exists_of_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms FamilyParameterComparisonBlockTrace.exists_of_run

/--
info: 'Lean4Lean.AddInductive.FamilyValidationBlockRun.parameterComparisonTrace_result' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms FamilyValidationBlockRun.parameterComparisonTrace_result

/--
info: 'Lean4Lean.AddInductive.FamilyValidationBlockRun.parameterComparison_lengths_shape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms FamilyValidationBlockRun.parameterComparison_lengths_shape

/--
info: 'Lean4Lean.AddInductive.NormalizationCandidateExecution.familyParameterComparison_lengths' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NormalizationCandidateExecution.familyParameterComparison_lengths

/--
info: 'Lean4Lean.AddInductive.checkInductiveTypes_factor' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms checkInductiveTypes_factor

/--
info: 'Lean4Lean.AddInductive.NormalizationCandidateExecution.build_ok_of_candidateObservers' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NormalizationCandidateExecution.build_ok_of_candidateObservers

/--
info: 'Lean4Lean.AddInductive.NormalizationCandidateExecution.familyValidationResult' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NormalizationCandidateExecution.familyValidationResult

/--
info: 'Lean4Lean.AddInductive.NormalizationCandidateExecution.familyValidationResult_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NormalizationCandidateExecution.familyValidationResult_run

/--
info: 'Lean4Lean.AddInductive.NormalizationCandidateExecution.validationContext_lparams_all' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NormalizationCandidateExecution.validationContext_lparams_all

/--
info: 'Lean4Lean.AddInductive.NormalizationCandidateExecution.familyValidation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NormalizationCandidateExecution.familyValidation

/--
info: 'Lean4Lean.AddInductive.NormalizationCandidateExecution.firstFamilyType_nparams_le_spineLength' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NormalizationCandidateExecution.firstFamilyType_nparams_le_spineLength

/--
info: 'Lean4Lean.AddInductive.NormalizationCandidateExecution.firstFamilyType_spineLength_lt_inductiveFuel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NormalizationCandidateExecution.firstFamilyType_spineLength_lt_inductiveFuel

/--
info: 'Lean4Lean.AddInductive.NormalizationCandidateExecution.firstFamilyType_resultLevel_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NormalizationCandidateExecution.firstFamilyType_resultLevel_eq

/--
info: 'Lean4Lean.AddInductive.NormalizationCandidateExecution.firstFamily_resultLevel_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NormalizationCandidateExecution.firstFamily_resultLevel_eq

/--
info: 'Lean4Lean.AddInductive.NormalizationCandidateExecution.producesFromBuildExecution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NormalizationCandidateExecution.producesFromBuildExecution

/--
info: 'Lean4Lean.AddInductive.FamilyValidationBlockResult.sizes_of_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms FamilyValidationBlockResult.sizes_of_run

/--
info: 'Lean4Lean.AddInductive.FamilyValidationBlockRun.of_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms FamilyValidationBlockRun.of_run

/--
info: 'Lean4Lean.AddInductive.NormalizationCandidateExecution.familyValidationBlockRun' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NormalizationCandidateExecution.familyValidationBlockRun

/--
info: 'Lean4Lean.AddInductive.FamilyValidationBlockRun.buildExecution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms FamilyValidationBlockRun.buildExecution

/--
info: 'Lean4Lean.AddInductive.ConstructorBlockValidationRun.buildExecution' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ConstructorBlockValidationRun.buildExecution

/--
info: 'Lean4Lean.AddInductive.ConstructorBlockValidationTraces.buildExecution_ok_of_loop_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ConstructorBlockValidationTraces.buildExecution_ok_of_loop_run

/--
info: 'Lean4Lean.AddInductive.ConstructorBlockValidationRun.buildExecution_ok_of_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ConstructorBlockValidationRun.buildExecution_ok_of_run

/--
info: 'Lean4Lean.AddInductive.ConstructorBlockValidationRun.of_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConstructorBlockValidationRun.of_run

/--
info: 'Lean4Lean.AddInductive.ConstructorBlockValidationRun.nonempty_iff_checkConstructors_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ConstructorBlockValidationRun.nonempty_iff_checkConstructors_ok

/--
info: 'Lean4Lean.AddInductive.NormalizationCandidateExecution.constructorValidation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NormalizationCandidateExecution.constructorValidation

/--
info: 'Lean4Lean.AddInductive.ConstructorListValidationTrace.nonempty_cons_iff_exact_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ConstructorListValidationTrace.nonempty_cons_iff_exact_source

/--
info: 'Lean4Lean.AddInductive.ConstructorValidationRun.run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConstructorValidationRun.run

/--
info: 'Lean4Lean.AddInductive.ConstructorValidationRun.nonempty_of_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ConstructorValidationRun.nonempty_of_run

/--
info: 'Lean4Lean.AddInductive.ConstructorValidationRun.of_run' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ConstructorValidationRun.of_run

/--
info: 'Lean4Lean.AddInductive.ConstructorValidationRun.nonempty_iff_checkConstructors_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ConstructorValidationRun.nonempty_iff_checkConstructors_ok

/--
info: 'Lean4Lean.AddInductive.ConstructorValidationRun.not_nonempty_of_error' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ConstructorValidationRun.not_nonempty_of_error

end AddInductive
end Lean4Lean
