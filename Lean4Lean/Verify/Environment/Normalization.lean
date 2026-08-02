import Lean4Lean.Verify.TypeChecker
import Lean4Lean.Inductive.Add

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

namespace TypeChecker

/-- The primitive constants whose Theory reflections are required by the
verified checker. `Nat.pred` and `Nat.bitwise` are kernel primitive names too,
but they have no dedicated fields in `VEnv.HasPrimitives`. -/
def reflectedPrimitiveNames : List Name := [
  ``Bool, ``Bool.false, ``Bool.true,
  ``Nat, ``Nat.zero, ``Nat.succ,
  ``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.pow,
  ``Nat.gcd, ``Nat.mod, ``Nat.div, ``Nat.beq, ``Nat.ble,
  ``Nat.land, ``Nat.lor, ``Nat.xor,
  ``Nat.shiftLeft, ``Nat.shiftRight,
  ``Char.ofNat, ``String.ofList]

/-- A small Theory environment that contains none of Lean's hard-coded
primitive names satisfies the primitive-reflection contract vacuously. This is
useful for isolated staged checker contexts. -/
theorem VEnv.HasPrimitives.of_avoids
    {env : VEnv}
    (h : ∀ n ∈ reflectedPrimitiveNames, env.constants n = none) :
    env.HasPrimitives := by
  have noContains (n) (hn : n ∈ reflectedPrimitiveNames) :
      ¬env.contains n := by
    rintro ⟨ci, hci⟩
    rw [h n hn] at hci
    contradiction
  have noLookup (n) (hn : n ∈ reflectedPrimitiveNames)
      {ci} (hci : env.constants n = some ci) : False := by
    rw [h n hn] at hci
    contradiction
  exact {
    bool := fun hc =>
      (noContains ``Bool (by simp [reflectedPrimitiveNames]) hc).elim
    boolFalse := fun hci =>
      (noLookup ``Bool.false (by simp [reflectedPrimitiveNames]) hci).elim
    boolTrue := fun hci =>
      (noLookup ``Bool.true (by simp [reflectedPrimitiveNames]) hci).elim
    nat := fun hc =>
      (noContains ``Nat (by simp [reflectedPrimitiveNames]) hc).elim
    natZero := fun hci =>
      (noLookup ``Nat.zero (by simp [reflectedPrimitiveNames]) hci).elim
    natSucc := fun hci =>
      (noLookup ``Nat.succ (by simp [reflectedPrimitiveNames]) hci).elim
    natAdd := fun hc =>
      (noContains ``Nat.add (by simp [reflectedPrimitiveNames]) hc).elim
    natSub := fun hc =>
      (noContains ``Nat.sub (by simp [reflectedPrimitiveNames]) hc).elim
    natMul := fun hc =>
      (noContains ``Nat.mul (by simp [reflectedPrimitiveNames]) hc).elim
    natPow := fun hc =>
      (noContains ``Nat.pow (by simp [reflectedPrimitiveNames]) hc).elim
    natGcd := fun hc =>
      (noContains ``Nat.gcd (by simp [reflectedPrimitiveNames]) hc).elim
    natMod := fun hc =>
      (noContains ``Nat.mod (by simp [reflectedPrimitiveNames]) hc).elim
    natDiv := fun hc =>
      (noContains ``Nat.div (by simp [reflectedPrimitiveNames]) hc).elim
    natBEq := fun hc =>
      (noContains ``Nat.beq (by simp [reflectedPrimitiveNames]) hc).elim
    natBLE := fun hc =>
      (noContains ``Nat.ble (by simp [reflectedPrimitiveNames]) hc).elim
    natLAnd := fun hc =>
      (noContains ``Nat.land (by simp [reflectedPrimitiveNames]) hc).elim
    natLOr := fun hc =>
      (noContains ``Nat.lor (by simp [reflectedPrimitiveNames]) hc).elim
    natXor := fun hc =>
      (noContains ``Nat.xor (by simp [reflectedPrimitiveNames]) hc).elim
    natShiftLeft := fun hc =>
      (noContains ``Nat.shiftLeft
        (by simp [reflectedPrimitiveNames]) hc).elim
    natShiftRight := fun hc =>
      (noContains ``Nat.shiftRight
        (by simp [reflectedPrimitiveNames]) hc).elim
    charOfNat := fun hci =>
      (noLookup ``Char.ofNat (by simp [reflectedPrimitiveNames]) hci).elim
    stringOfList := fun hci =>
      (noLookup ``String.ofList
        (by simp [reflectedPrimitiveNames]) hci).elim }

/-- Kernel-side counterpart of `VEnv.HasPrimitives.of_avoids`: if an isolated
constant map contains no hard-coded primitive name, the safety premise needed
by `VContext` is vacuous. -/
theorem safePrimitives_of_avoids
    {env : Environment} {n : Name} {ci : ConstantInfo}
    (h : ∀ n, Environment.primitives.contains n → env.find? n = none) :
    env.find? n = some ci →
      Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = [] := by
  intro hfind hprim
  rw [h n hprim] at hfind
  contradiction

/-- Evidence that Verify's recursive WHNF procedure returned an exact kernel
expression, together with strict translations of the input and output into one
Theory context.

The result is not trusted merely because it is supplied by a caller:
`run_eq` records the concrete checker execution, while `rhs_tr` identifies its
Theory meaning. -/
structure WhnfRun (env : VEnv) (Us : List Name) (Δ : VLCtx)
    (lhs rhs : Expr) (lhs' rhs' : VExpr) where
  context : VContext
  venv_eq : context.venv = env
  lparams_eq : context.lparams = Us
  vlctx_eq : context.vlctx = Δ
  state_wf : VState.WF context {}
  lhs_tr : TrExprS env Us Δ lhs lhs'
  rhs_tr : TrExpr env Us Δ rhs rhs'
  recursionFuel : Nat
  run_eq : ∃ state : State,
    Inner.whnf' lhs (Methods.withFuel recursionFuel)
      context.toContext ({} : State) = .ok (rhs, state)

/-- Turn one operationally certified candidate step into the existing
state-bearing Verify certificate once the caller supplies the strict
kernel/Theory translations and the corresponding verified context.

The adapter recovers the final checker state from the stored `M.run` equality;
it does not rerun normalization, choose a result, or assert a semantic
equality. -/
def WhnfRun.ofCandidateStep
    (step : AddInductive.CandidateWhnfStep)
    (hvalid : step.Valid)
    (context : VContext)
    (context_eq :
      context.toContext = step.context.toTypeChecker)
    (venv_eq : context.venv = env)
    (lparams_eq : context.lparams = Us)
    (vlctx_eq : context.vlctx = Δ)
    (state_wf : VState.WF context {})
    (lhs_tr : TrExprS env Us Δ step.source lhs')
    (rhs_tr : TrExpr env Us Δ step.result rhs')
    (recursionFuel : Nat)
    (hdepth : step.context.fuel.recDepth = recursionFuel + 1) :
    WhnfRun env Us Δ step.source step.result lhs' rhs' where
  context := context
  venv_eq := venv_eq
  lparams_eq := lparams_eq
  vlctx_eq := vlctx_eq
  state_wf := state_wf
  lhs_tr := lhs_tr
  rhs_tr := rhs_tr
  recursionFuel := recursionFuel
  run_eq := by
    rw [context_eq]
    exact step.innerRun recursionFuel hdepth hvalid

/-- The strict input translation already supplies the Theory well-formedness
needed to type an exact WHNF equality. In particular, a certificate producer
does not need to borrow a typing fact from the normalized declaration it is
trying to construct. -/
theorem WhnfRun.lhs_wf
    (run : WhnfRun env Us Δ lhs rhs lhs' rhs') :
    lhs'.WF env Us.length Δ.toCtx := by
  have hlhs : run.context.TrExprS lhs lhs' := by
    simpa only [VContext.TrExprS, run.venv_eq, run.lparams_eq,
      run.vlctx_eq] using run.lhs_tr
  have hwf := hlhs.wf run.context.Ewf.ordered run.context.Δwf
  simpa only [run.venv_eq, run.lparams_eq, run.vlctx_eq] using hwf

/-- An exact successful verified WHNF execution is an ordinary Theory
definitional equality. The proof consumes the existing checker-refinement
contract and uses representation uniqueness to identify the translated
result. -/
theorem WhnfRun.isDefEqU
    (run : WhnfRun env Us Δ lhs rhs lhs' rhs') :
    env.IsDefEqU Us.length Δ.toCtx lhs' rhs' := by
  have hlhs : run.context.TrExprS lhs lhs' := by
    simpa only [VContext.TrExprS, run.venv_eq, run.lparams_eq,
      run.vlctx_eq] using run.lhs_tr
  have hrhs : run.context.TrExpr rhs rhs' := by
    simpa only [VContext.TrExpr, run.venv_eq, run.lparams_eq,
      run.vlctx_eq] using run.rhs_tr
  obtain ⟨state, hrun⟩ := run.run_eq
  obtain ⟨_, _, _, _, _, htr⟩ :=
    (TypeChecker.Inner.whnf'.WF hlhs
      (Methods.withFuel run.recursionFuel) Methods.withFuel.WF)
      run.state_wf rhs state hrun
  have hdefeq :=
    htr.uniq run.context.Ewf
      (.refl run.context.Ewf run.context.Δwf) hrhs
  simpa only [VContext.IsDefEqU, run.venv_eq, run.lparams_eq,
    run.vlctx_eq] using hdefeq

/-- Typed form of `WhnfRun.isDefEqU`. A known type for the input fixes the
otherwise existential type in the WHNF refinement result. -/
theorem WhnfRun.isDefEq
    (run : WhnfRun env Us Δ lhs rhs lhs' rhs')
    (hlhs : env.HasType Us.length Δ.toCtx lhs' A) :
    env.IsDefEq Us.length Δ.toCtx lhs' rhs' A := by
  have henv : VEnv.WF env := by
    simpa only [run.venv_eq] using run.context.Ewf
  have hΔ : OnCtx Δ.toCtx (env.IsType Us.length) := by
    simpa only [run.venv_eq, run.lparams_eq, run.vlctx_eq] using
      run.context.Δwf.toCtx
  exact run.isDefEqU.of_l henv hΔ hlhs

/-- Evidence that Verify's full type-checking path inferred an exact kernel
type, with strict Theory translations of both the checked expression and the
returned type.

`inferOnly := false` is important here: the recorded run checks the expression
rather than trusting a caller-provided `TrExprS` derivation as an inference
cache hit. -/
structure CheckTypeRun (env : VEnv) (Us : List Name) (Δ : VLCtx)
    (expr inferred : Expr) (expr' inferred' : VExpr) where
  context : VContext
  venv_eq : context.venv = env
  lparams_eq : context.lparams = Us
  vlctx_eq : context.vlctx = Δ
  state_wf : VState.WF context {}
  expr_tr : TrExprS env Us Δ expr expr'
  inferred_tr : TrExprS env Us Δ inferred inferred'
  recursionFuel : Nat
  run_eq : ∃ state : State,
    Inner.inferType expr false (Methods.withFuel recursionFuel)
      context.toContext ({} : State) = .ok (inferred, state)

/-- Candidate-step adapter for full checking. As with
`WhnfRun.ofCandidateStep`, the operational result and final state come from
the producer; this boundary only attaches an already verified context and
strict translations. -/
def CheckTypeRun.ofCandidateStep
    (step : AddInductive.CandidateCheckTypeStep)
    (hvalid : step.Valid)
    (context : VContext)
    (context_eq :
      context.toContext = step.context.toTypeChecker)
    (venv_eq : context.venv = env)
    (lparams_eq : context.lparams = Us)
    (vlctx_eq : context.vlctx = Δ)
    (state_wf : VState.WF context {})
    (expr_tr : TrExprS env Us Δ step.source expr')
    (inferred_tr : TrExprS env Us Δ step.inferred inferred')
    (recursionFuel : Nat)
    (hdepth : step.context.fuel.recDepth = recursionFuel) :
    CheckTypeRun env Us Δ step.source step.inferred expr' inferred' where
  context := context
  venv_eq := venv_eq
  lparams_eq := lparams_eq
  vlctx_eq := vlctx_eq
  state_wf := state_wf
  expr_tr := expr_tr
  inferred_tr := inferred_tr
  recursionFuel := recursionFuel
  run_eq := by
    rw [context_eq]
    exact step.innerRun recursionFuel hdepth hvalid

/-- Recover the strict Theory translations and typing judgment supplied by an
exact retained full-check observation.

This is the proof-producing counterpart of `CheckTypeRun.ofCandidateStep` for
callers that do not yet have named translations.  The only source-side premise
is the free-variable condition required by the verified checker refinement. -/
theorem candidateCheckTypeStep_exists_translation
    (step : AddInductive.CandidateCheckTypeStep)
    (hvalid : step.Valid)
    (context : VContext)
    (context_eq : context.toContext = step.context.toTypeChecker)
    (state_wf : VState.WF context {})
    (source_fvars :
      step.source.FVarsIn (· ∈ context.vlctx.fvars))
    (recursionFuel : Nat)
    (hdepth : step.context.fuel.recDepth = recursionFuel) :
    ∃ source' inferred',
      context.TrExprS step.source source' ∧
      context.TrExprS step.inferred inferred' ∧
      context.HasType source' inferred' := by
  obtain ⟨state, run⟩ :=
    step.innerRun recursionFuel hdepth hvalid
  rw [← context_eq] at run
  obtain ⟨_, _, _, _, source', inferred', typing⟩ :=
    (Inner.checkType.WF source_fvars
      (Methods.withFuel recursionFuel) Methods.withFuel.WF)
      state_wf step.inferred state run
  exact ⟨source', inferred', typing.2.1, typing.2.2.1,
    typing.2.2.2⟩

/-- An exact successful `checkType` execution supplies the corresponding
Theory typing judgment. Translation uniqueness transports the verifier's
existential result to the precise translations named by the certificate. -/
theorem CheckTypeRun.hasType
    (run : CheckTypeRun env Us Δ expr inferred expr' inferred') :
    env.HasType Us.length Δ.toCtx expr' inferred' := by
  have hexpr : run.context.TrExprS expr expr' := by
    simpa only [VContext.TrExprS, run.venv_eq, run.lparams_eq,
      run.vlctx_eq] using run.expr_tr
  have hinferred : run.context.TrExprS inferred inferred' := by
    simpa only [VContext.TrExprS, run.venv_eq, run.lparams_eq,
      run.vlctx_eq] using run.inferred_tr
  obtain ⟨state, hrun⟩ := run.run_eq
  obtain ⟨_, _, _, _, e, ty, htyping⟩ :=
    (TypeChecker.Inner.checkType.WF hexpr.fvarsIn
      (Methods.withFuel run.recursionFuel) Methods.withFuel.WF)
      run.state_wf inferred state hrun
  rcases htyping with ⟨_, he, hty, hhasType⟩
  have heq :=
    he.uniq run.context.Ewf
      (.refl run.context.Ewf run.context.Δwf) hexpr
  have htyeq :=
    hty.uniq run.context.Ewf
      (.refl run.context.Ewf run.context.Δwf) hinferred
  have hout :=
    (hhasType.defeqU_l run.context.Ewf run.context.Δwf heq).defeqU_r
      run.context.Ewf run.context.Δwf htyeq
  simpa only [run.venv_eq, run.lparams_eq, run.vlctx_eq] using hout

/-- A checked expression whose inferred type translates to a sort is a Theory
type. This is the insertion premise needed for raw family and constructor
constants. -/
theorem CheckTypeRun.isType
    (run : CheckTypeRun env Us Δ expr inferred expr' (.sort u)) :
    env.IsType Us.length Δ.toCtx expr' :=
  ⟨u, run.hasType⟩

/-- If `checkType` returns a type expression whose own verified WHNF is a
sort, the checked expression is a Theory type. This is the common alias case:
the checker may infer a reducible type constant before `ensureSort` exposes its
sort WHNF. -/
theorem CheckTypeRun.isType_of_whnf
    (run : CheckTypeRun env Us Δ expr inferred expr' inferred')
    (typeRun : WhnfRun env Us Δ inferred reduced inferred' (.sort u)) :
    env.IsType Us.length Δ.toCtx expr' := by
  have henv : VEnv.WF env := by
    simpa only [run.venv_eq] using run.context.Ewf
  have hΔ : OnCtx Δ.toCtx (env.IsType Us.length) := by
    simpa only [run.venv_eq, run.lparams_eq, run.vlctx_eq] using
      run.context.Δwf.toCtx
  exact ⟨u, run.hasType.defeqU_r henv hΔ typeRun.isDefEqU⟩

/-- Evidence for one exact successful checker definitional-equality run, with
strict translations of both kernel endpoints in the same Theory context. -/
structure IsDefEqRun (env : VEnv) (Us : List Name) (Δ : VLCtx)
    (lhs rhs : Expr) (lhs' rhs' : VExpr) where
  context : VContext
  venv_eq : context.venv = env
  lparams_eq : context.lparams = Us
  vlctx_eq : context.vlctx = Δ
  state_wf : VState.WF context {}
  lhs_tr : TrExprS env Us Δ lhs lhs'
  rhs_tr : TrExprS env Us Δ rhs rhs'
  recursionFuel : Nat
  run_eq : ∃ state : State,
    Inner.isDefEq lhs rhs (Methods.withFuel recursionFuel)
      context.toContext ({} : State) = .ok (true, state)

/-- Convert the retained candidate equality observation to a state-bearing
Verify certificate. -/
def IsDefEqRun.ofCandidateStep
    (step : AddInductive.CandidateIsDefEqStep)
    (hvalid : step.Valid)
    (context : VContext)
    (context_eq : context.toContext = step.context.toTypeChecker)
    (venv_eq : context.venv = env)
    (lparams_eq : context.lparams = Us)
    (vlctx_eq : context.vlctx = Δ)
    (state_wf : VState.WF context {})
    (lhs_tr : TrExprS env Us Δ step.lhs lhs')
    (rhs_tr : TrExprS env Us Δ step.rhs rhs')
    (recursionFuel : Nat)
    (hdepth : step.context.fuel.recDepth = recursionFuel) :
    IsDefEqRun env Us Δ step.lhs step.rhs lhs' rhs' where
  context := context
  venv_eq := venv_eq
  lparams_eq := lparams_eq
  vlctx_eq := vlctx_eq
  state_wf := state_wf
  lhs_tr := lhs_tr
  rhs_tr := rhs_tr
  recursionFuel := recursionFuel
  run_eq := by
    rw [context_eq]
    exact step.innerRun recursionFuel hdepth hvalid

/-- A successful verified equality run supplies ordinary Theory
definitional equality. -/
theorem IsDefEqRun.isDefEqU
    (run : IsDefEqRun env Us Δ lhs rhs lhs' rhs') :
    env.IsDefEqU Us.length Δ.toCtx lhs' rhs' := by
  have hlhs : run.context.TrExprS lhs lhs' := by
    simpa only [VContext.TrExprS, run.venv_eq, run.lparams_eq,
      run.vlctx_eq] using run.lhs_tr
  have hrhs : run.context.TrExprS rhs rhs' := by
    simpa only [VContext.TrExprS, run.venv_eq, run.lparams_eq,
      run.vlctx_eq] using run.rhs_tr
  obtain ⟨state, hrun⟩ := run.run_eq
  obtain ⟨_, _, _, _, hdefeq⟩ :=
    (TypeChecker.Inner.isDefEq.WF hlhs hrhs
      (Methods.withFuel run.recursionFuel) Methods.withFuel.WF)
      run.state_wf true state hrun
  simpa only [VContext.IsDefEqU, run.venv_eq, run.lparams_eq,
    run.vlctx_eq] using hdefeq (by simp)

/-- Consuming a certified annotation path cannot introduce a free variable or
level metavariable. -/
theorem candidateTypeAnnotation_fvarsIn
    (trace : AddInductive.CandidateTypeAnnotationTrace source consumed)
    (h : source.FVarsIn fvars) : consumed.FVarsIn fvars := by
  induction trace with
  | identity => exact h
  | outParam _ _ _ ih => exact ih h.2
  | semiOutParam _ _ _ ih => exact ih h.2
  | optParam _ _ _ _ ih => exact ih h.1.2
  | autoParam _ _ _ _ ih => exact ih h.1.2

/-- Extract a strict translation of the consumed annotation argument from the
strict translation of the raw wrapper application. -/
theorem candidateTypeAnnotation_exists_translation
    (trace : AddInductive.CandidateTypeAnnotationTrace source consumed)
    (source_tr : TrExprS env Us Δ source source') :
    ∃ consumed', TrExprS env Us Δ consumed consumed' := by
  induction trace generalizing source' with
  | identity => exact ⟨source', source_tr⟩
  | outParam _ _ _ ih =>
    let .app _ _ _ type_tr := source_tr
    exact ih type_tr
  | semiOutParam _ _ _ ih =>
    let .app _ _ _ type_tr := source_tr
    exact ih type_tr
  | optParam _ _ _ _ ih =>
    let .app _ _ fn_tr _ := source_tr
    let .app _ _ _ type_tr := fn_tr
    exact ih type_tr
  | autoParam _ _ _ _ ih =>
    let .app _ _ fn_tr _ := source_tr
    let .app _ _ _ type_tr := fn_tr
    exact ih type_tr

/-- The empty executable checker state is well formed for any verified
context whose free-variable names are already reserved by the kernel name
generator.  `VState.WF.empty` is the empty-local-context specialization;
candidate normalization needs this slightly more general form after entering
raw Pi binders. -/
theorem VState.WF.empty_of_reserves
    (context : VContext)
    (reserved : ∀ fv ∈ context.vlctx.fvars,
      (({} : VState).ngen).Reserves fv) :
    VState.WF context {} where
  trctx := context.trlctx
  ngen_wf := reserved
  ectx := ⟨context.vlctx, .refl, context.Δwf, .refl, .empty, reserved⟩
  inferTypeI_wf := .empty
  inferTypeC_wf := .empty
  whnfCore_wf := .empty
  whnf_wf := .empty
  unfold_wf _ := by simp

/-- Positional verified context for an executable normalization candidate.

The equality pins every checker-visible field (environment, local context,
safety, level parameters, and fuel) to the `AddInductive.Context` retained by
the candidate trace.  The state certificate is kept with it because every
retained full-check and WHNF observation starts from the empty checker state. -/
structure CandidateContextRun
    (candidateContext : AddInductive.Context) where
  context : VContext
  context_eq : context.toContext = candidateContext.toTypeChecker
  state_wf : VState.WF context {}
  namePrefix_ne : candidateContext.ngen.namePrefix ≠
    (({} : VState).ngen).namePrefix

/-- Candidate binders and the kernel checker's own temporary names use
different prefixes, so every candidate binder is reserved by a freshly
initialized kernel checker state. -/
theorem candidateFreshFVarId_reserved
    (candidateContext : AddInductive.Context)
    (namePrefix_ne : candidateContext.ngen.namePrefix ≠
      (({} : VState).ngen).namePrefix) :
    (({} : VState).ngen).Reserves candidateContext.freshFVarId := by
  simp [NameGenerator.Reserves, AddInductive.Context.freshFVarId]
  intro i h
  apply namePrefix_ne
  simpa using congrArg Name.getPrefix h

/-- Package an already verified checker context at a candidate position. -/
def CandidateContextRun.ofVContext
    (candidateContext : AddInductive.Context)
    (context : VContext)
    (context_eq : context.toContext = candidateContext.toTypeChecker)
    (state_wf : VState.WF context {})
    (namePrefix_ne : candidateContext.ngen.namePrefix ≠
      (({} : VState).ngen).namePrefix) :
    CandidateContextRun candidateContext :=
  ⟨context, context_eq, state_wf, namePrefix_ne⟩

/-- Construct the root certificate used by family and constructor candidates.
Their candidate traversal deliberately resets the local context to empty. -/
def CandidateContextRun.root
    {ves : VEnvs} (wf : ves.WF candidateContext.env)
    (lctx_eq : candidateContext.lctx = {})
    (namePrefix_ne : candidateContext.ngen.namePrefix ≠
      (({} : VState).ngen).namePrefix) :
    CandidateContextRun candidateContext := by
  let context := VContext.mk' wf candidateContext.safety
    candidateContext.lparams candidateContext.fuel
  refine ⟨context, ?_, ?_, namePrefix_ne⟩
  · simp [context, VContext.mk', MLCtx.lctx,
      AddInductive.Context.toTypeChecker, lctx_eq]
  · exact VState.WF.empty

/-- Extend a verified candidate context by precisely the raw local declaration
used by `AddInductive.Context.pushLocalDecl`.

The caller supplies the strict Theory translation and typing of the *stored*
local-domain expression.  Freshness comes from the trace index; reservation is
the independent fact needed to restart each retained checker observation from
the empty kernel checker state. -/
def CandidateContextRun.pushLocalDecl
    (run : CandidateContextRun candidateContext)
    (name : Name) (binderInfo : BinderInfo) (domain : Expr)
    (fresh : candidateContext.lctx.find?
      candidateContext.freshFVarId = none)
    (domain' : VExpr)
    (domain_tr : run.context.TrExprS domain domain')
    (domain_type : run.context.IsType domain') :
    CandidateContextRun
      (candidateContext.pushLocalDecl name binderInfo domain) := by
  let mlctx := run.context.mlctx.vlam candidateContext.freshFVarId
    name domain domain' binderInfo
  have lctx_eq : run.context.mlctx.lctx = candidateContext.lctx := by
    calc
      run.context.mlctx.lctx = run.context.lctx := run.context.lctx_eq
      _ = candidateContext.lctx := by
        have h := congrArg (fun c : TypeChecker.Context => c.lctx)
          run.context_eq
        simpa [AddInductive.Context.toTypeChecker] using h
  have fresh' : run.context.mlctx.lctx.find?
      candidateContext.freshFVarId = none := by
    rw [lctx_eq]
    exact fresh
  have mlctx_wf : mlctx.WF run.context.venv run.context.lparams :=
    ⟨run.context.mlctx_wf, fresh', domain_tr, domain_type⟩
  let context := run.context.withMLC mlctx (wf := ⟨mlctx_wf⟩)
  have context_eq : context.toContext =
      (candidateContext.pushLocalDecl name binderInfo domain).toTypeChecker := by
    change { run.context.toContext with
        lctx := run.context.mlctx.lctx.mkLocalDecl
          candidateContext.freshFVarId name domain binderInfo } = _
    rw [run.context_eq, lctx_eq]
    rfl
  refine ⟨context, context_eq, VState.WF.empty_of_reserves context ?_, ?_⟩
  intro fv hfv
  change fv ∈ candidateContext.freshFVarId ::
    run.context.vlctx.fvars at hfv
  simp only [List.mem_cons] at hfv
  rcases hfv with rfl | hfv
  · exact candidateFreshFVarId_reserved candidateContext run.namePrefix_ne
  · exact run.state_wf.ngen_wf fv hfv
  simpa [AddInductive.Context.pushLocalDecl] using run.namePrefix_ne

@[simp] theorem CandidateContextRun.pushLocalDecl_venv
    (run : CandidateContextRun candidateContext)
    (domain_tr : run.context.TrExprS domain domain')
    (domain_type : run.context.IsType domain') :
    (run.pushLocalDecl name binderInfo domain fresh domain' domain_tr
      domain_type).context.venv = run.context.venv :=
  rfl

@[simp] theorem CandidateContextRun.pushLocalDecl_lparams
    (run : CandidateContextRun candidateContext)
    (domain_tr : run.context.TrExprS domain domain')
    (domain_type : run.context.IsType domain') :
    (run.pushLocalDecl name binderInfo domain fresh domain' domain_tr
      domain_type).context.lparams = run.context.lparams :=
  rfl

@[simp] theorem CandidateContextRun.pushLocalDecl_vlctx
    (run : CandidateContextRun candidateContext)
    (domain_tr : run.context.TrExprS domain domain')
    (domain_type : run.context.IsType domain') :
    (run.pushLocalDecl name binderInfo domain fresh domain' domain_tr
      domain_type).context.vlctx =
      (some (candidateContext.freshFVarId, domain.fvarsList),
        .vlam domain') :: run.context.vlctx :=
  rfl

/-- The two exact verifier runs attached to one retained candidate node.

The indices force both runs to use the node's kernel source and observed
results and to agree on its Theory source.  This is the atomic input to the
recursive candidate interpreter below: a successful full check supplies the
type at which the successful WHNF execution is interpreted. -/
structure CandidateNodeRun (env : VEnv) (Us : List Name) (Δ : VLCtx)
    (context : AddInductive.Context)
    (source inferred result : Expr)
    (source' result' inferred' : VExpr) where
  check : CheckTypeRun env Us Δ source inferred source' inferred'
  whnf : WhnfRun env Us Δ source result source' result'

/-- Construct an atomic semantic node directly from the two proof-carrying
observations retained by `CandidateExprTrace`.  The caller supplies only the
verified context and translations; the operational equalities and erased
checker states come from the candidate observations themselves. -/
def CandidateNodeRun.ofCandidate
    (candidateContext : AddInductive.Context)
    (source inferred result : Expr)
    (checked : AddInductive.CandidateCheckTypeStep.Valid
      ⟨candidateContext, source, inferred⟩)
    (normalized : AddInductive.CandidateWhnfStep.Valid
      ⟨candidateContext, source, result⟩)
    (context : VContext)
    (context_eq : context.toContext = candidateContext.toTypeChecker)
    (venv_eq : context.venv = env)
    (lparams_eq : context.lparams = Us)
    (vlctx_eq : context.vlctx = Δ)
    (state_wf : VState.WF context {})
    (source_tr : TrExprS env Us Δ source source')
    (inferred_tr : TrExprS env Us Δ inferred inferred')
    (result_tr : TrExpr env Us Δ result result')
    (checkFuel whnfFuel : Nat)
    (checkDepth : candidateContext.fuel.recDepth = checkFuel)
    (whnfDepth : candidateContext.fuel.recDepth = whnfFuel + 1) :
    CandidateNodeRun env Us Δ candidateContext source inferred result
      source' result' inferred' where
  check := CheckTypeRun.ofCandidateStep
    ⟨candidateContext, source, inferred⟩ checked context context_eq
    venv_eq lparams_eq vlctx_eq state_wf source_tr inferred_tr
    checkFuel checkDepth
  whnf := WhnfRun.ofCandidateStep
    ⟨candidateContext, source, result⟩ normalized context context_eq
    venv_eq lparams_eq vlctx_eq state_wf source_tr result_tr
    whnfFuel whnfDepth

/-- Recover all output translations for one retained candidate node from the
verified checker refinements themselves.

Unlike `ofCandidate`, this theorem does not ask the caller to identify the
kernel expressions returned by `checkType` and `whnf` with preselected Theory
terms.  It extracts strict translations of both results from the two exact
executions, then packages those witnesses in the ordinary paired-node API.
Only the root source translation and matching verified context remain input. -/
theorem CandidateNodeRun.exists_ofCandidate
    (candidateContext : AddInductive.Context)
    (source inferred result : Expr)
    (checked : AddInductive.CandidateCheckTypeStep.Valid
      ⟨candidateContext, source, inferred⟩)
    (normalized : AddInductive.CandidateWhnfStep.Valid
      ⟨candidateContext, source, result⟩)
    (context : VContext)
    (context_eq : context.toContext = candidateContext.toTypeChecker)
    (state_wf : VState.WF context {})
    (source' : VExpr) (source_tr : context.TrExprS source source')
    (checkFuel whnfFuel : Nat)
    (checkDepth : candidateContext.fuel.recDepth = checkFuel)
    (whnfDepth : candidateContext.fuel.recDepth = whnfFuel + 1) :
    ∃ inferred' result',
      context.TrExprS inferred inferred' ∧
      context.TrExprS result result' ∧
      Nonempty (CandidateNodeRun context.venv context.lparams context.vlctx
        candidateContext source inferred result source' result' inferred') := by
  obtain ⟨checkState, checkRun⟩ :=
    AddInductive.CandidateCheckTypeStep.innerRun
      ⟨candidateContext, source, inferred⟩ checkFuel checkDepth checked
  rw [← context_eq] at checkRun
  obtain ⟨_, _, _, _, checkedSource', inferred', checkedTyping⟩ :=
    (Inner.checkType.WF source_tr.fvarsIn
      (Methods.withFuel checkFuel) Methods.withFuel.WF)
      state_wf inferred checkState checkRun
  obtain ⟨whnfState, whnfRun⟩ :=
    AddInductive.CandidateWhnfStep.innerRun
      ⟨candidateContext, source, result⟩ whnfFuel whnfDepth normalized
  rw [← context_eq] at whnfRun
  obtain ⟨_, _, _, _, _, resultTranslation⟩ :=
    (Inner.whnf'.WF source_tr
      (Methods.withFuel whnfFuel) Methods.withFuel.WF)
      state_wf result whnfState whnfRun
  obtain ⟨result', result_tr, _⟩ := resultTranslation
  refine ⟨inferred', result', checkedTyping.2.2.1, result_tr, ⟨?_⟩⟩
  exact CandidateNodeRun.ofCandidate
    candidateContext source inferred result checked normalized
    context context_eq rfl rfl rfl state_wf source_tr
    checkedTyping.2.2.1
    (result_tr.trExpr context.Ewf context.Δwf)
    checkFuel whnfFuel checkDepth whnfDepth

/-- Construct a paired candidate node with a caller-selected Theory endpoint
for the retained WHNF result. The exact full-check execution still selects
and strictly translates its inferred type; only the already translated WHNF
endpoint is fixed by the caller. -/
theorem CandidateNodeRun.exists_ofCandidateAtResult
    (candidateContext : AddInductive.Context)
    (source inferred result : Expr)
    (checked : AddInductive.CandidateCheckTypeStep.Valid
      ⟨candidateContext, source, inferred⟩)
    (normalized : AddInductive.CandidateWhnfStep.Valid
      ⟨candidateContext, source, result⟩)
    (context : VContext)
    (context_eq : context.toContext = candidateContext.toTypeChecker)
    (state_wf : VState.WF context {})
    (source' result' : VExpr)
    (source_tr : context.TrExprS source source')
    (result_tr : context.TrExpr result result')
    (checkFuel whnfFuel : Nat)
    (checkDepth : candidateContext.fuel.recDepth = checkFuel)
    (whnfDepth : candidateContext.fuel.recDepth = whnfFuel + 1) :
    ∃ inferred', Nonempty
      (CandidateNodeRun context.venv context.lparams context.vlctx
        candidateContext source inferred result source' result' inferred') := by
  obtain ⟨_, inferred', _, inferred_tr, _⟩ :=
    candidateCheckTypeStep_exists_translation
      ⟨candidateContext, source, inferred⟩ checked
      context context_eq state_wf source_tr.fvarsIn checkFuel checkDepth
  exact ⟨inferred', ⟨CandidateNodeRun.ofCandidate
    candidateContext source inferred result checked normalized
    context context_eq rfl rfl rfl state_wf source_tr inferred_tr
    result_tr checkFuel whnfFuel checkDepth whnfDepth⟩⟩

/-- Compositional evidence for a normalization comparison.

Leaves are either reflexive, already typed syntax or exact verified WHNF
executions. `forallE` lifts such evidence through the raw binder context,
which is the constructor-type case needed by the first non-identity replay. -/
inductive DefEqEvidence (env : VEnv) :
    Nat → List VExpr → VExpr → VExpr → VExpr → Prop where
  | refl (h : env.HasType U Γ e A) :
      DefEqEvidence env U Γ e e A
  | whnf (run : WhnfRun env Us Δ lhs rhs lhs' rhs')
      (h : env.HasType Us.length Δ.toCtx lhs' A) :
      DefEqEvidence env Us.length Δ.toCtx lhs' rhs' A
  | app
      (fn : DefEqEvidence env U Γ f f' (.forallE A B))
      (arg : DefEqEvidence env U Γ a a' A) :
      DefEqEvidence env U Γ (.app f a) (.app f' a') (B.inst a)
  | beta
      (body : env.HasType U (A :: Γ) e B)
      (arg : env.HasType U Γ e' A) :
      DefEqEvidence env U Γ
        (.app (.lam A e) e') (e.inst e') (B.inst e')
  | trans
      (left : DefEqEvidence env U Γ lhs mid A)
      (right : DefEqEvidence env U Γ mid rhs A) :
      DefEqEvidence env U Γ lhs rhs A
  | change
      (type : env.IsDefEq U Γ A B (.sort u))
      (term : DefEqEvidence env U Γ lhs rhs A) :
      DefEqEvidence env U Γ lhs rhs B
  | ofDefEq (proof : env.IsDefEq U Γ lhs rhs A) :
      DefEqEvidence env U Γ lhs rhs A
  | forallE
      (domain : DefEqEvidence env U Γ A A' (.sort u))
      (body : DefEqEvidence env U (A :: Γ) B B' (.sort v)) :
      DefEqEvidence env U Γ
        (.forallE A B) (.forallE A' B') (.sort (.imax u v))

/-- Interpret compositional normalization evidence as Theory definitional
equality at its recorded type. -/
theorem DefEqEvidence.isDefEq :
    DefEqEvidence env U Γ lhs rhs A →
      env.IsDefEq U Γ lhs rhs A
  | .refl h => h
  | .whnf run h => run.isDefEq h
  | .app fn arg => .appDF fn.isDefEq arg.isDefEq
  | .beta body arg => .beta body arg
  | .trans left right => .trans left.isDefEq right.isDefEq
  | .change type term => .defeqDF type term.isDefEq
  | .ofDefEq proof => proof
  | .forallE domain body =>
      .forallEDF domain.isDefEq body.isDefEq

/-- Interpret one paired candidate node as typed definitional equality. -/
def CandidateNodeRun.evidence
    (run : CandidateNodeRun env Us Δ context source inferred result
      source' result' inferred') :
    DefEqEvidence env Us.length Δ.toCtx source' result' inferred' :=
  .whnf run.whnf run.check.hasType

/-- Recursive semantic interpretation of a source-indexed candidate trace.

At a Pi node the raw domain and the annotation-consumed local domain may have
different strict Theory translations. The retained equality run relates them;
the body is checked in the consumed-domain context and transported back to the
raw Pi context only when forming congruence evidence. -/
inductive CandidateExprRun (env : VEnv) (Us : List Name) :
    {candidateContext : AddInductive.Context} → {source : Expr} →
      AddInductive.CandidateExprTrace candidateContext source →
      (Δ : VLCtx) → VExpr → VExpr → VExpr → Prop where
  | terminal
      (node : CandidateNodeRun env Us Δ context source inferred result
        source' result' inferred') :
      CandidateExprRun env Us
        (.terminal context source inferred result checked normalized)
        Δ source' result' inferred'
  | forallE
      (annotations : AddInductive.CandidateTypeAnnotations domain)
      (annotationsEq : AddInductive.CandidateIsDefEqStep.Valid
        ⟨context, domain, annotations.consumed⟩)
      (domainCandidate : AddInductive.CandidateExprTrace context domain)
      (bodyCandidate : AddInductive.CandidateExprTrace
        (context.pushLocalDecl name binderInfo annotations.consumed)
        (body.instantiate1 context.freshExpr))
      (node : CandidateNodeRun env Us Δ context source inferred
        (.forallE name domain body binderInfo)
        source' (.forallE domain' body') inferred')
      (domainRun : CandidateExprRun env Us domainCandidate Δ
        domain' domainView' domainInferred')
      (annotationsRun : IsDefEqRun env Us Δ
        domain annotations.consumed domain' storedDomain')
      (bodyRun : CandidateExprRun env Us bodyCandidate bodyΔ
        storedBody' bodyView' bodyInferred')
      (domainType : env.HasType Us.length Δ.toCtx domain' (.sort u))
      (bodyType : env.HasType Us.length
        (domain' :: Δ.toCtx) body' (.sort v))
      (bodySource : env.IsDefEq Us.length (domain' :: Δ.toCtx)
        body' storedBody' (.sort v))
      (bodyContext :
        bodyΔ =
          (some (context.freshFVarId, annotations.consumed.fvarsList),
            .vlam storedDomain') :: Δ) :
      CandidateExprRun env Us
        (.forallE context source inferred name domain body binderInfo fresh
          annotations annotationsEq checked normalized
          domainCandidate bodyCandidate)
        Δ source' (.forallE domainView' bodyView') inferred'

/-- Structural witness that a retained candidate trace is syntactically
identity-normalizing at every inspected node.

The witness is deliberately recursive rather than a single root equality:
generation consumes the exposed Pi spine positionally. At Pi nodes it also
records that annotation processing kept the binder domain unchanged. -/
inductive CandidateExprIdentity :
    {candidateContext : AddInductive.Context} → {source : Expr} →
      AddInductive.CandidateExprTrace candidateContext source → Prop where
  | terminal
      (result_eq : result = source) :
      CandidateExprIdentity
        (.terminal context source inferred result checked normalized)
  | forallE
      (domainCandidate : AddInductive.CandidateExprTrace context domain)
      (bodyCandidate : AddInductive.CandidateExprTrace
        (context.pushLocalDecl name binderInfo annotations.consumed)
        (body.instantiate1 context.freshExpr))
      (source_eq : source = .forallE name domain body binderInfo)
      (consumed_eq : annotations.consumed = domain)
      (domainIdentity : CandidateExprIdentity domainCandidate)
      (bodyIdentity : CandidateExprIdentity bodyCandidate) :
      CandidateExprIdentity
        (.forallE context source inferred name domain body binderInfo fresh
          annotations annotationsEq checked normalized
          domainCandidate bodyCandidate)

/-- Exact component inversion for a strict translation of a kernel Pi. -/
theorem TrExprS.forallE_components
    (run : TrExprS env Us Δ (.forallE name domain body binderInfo) source') :
    ∃ domain' body',
      source' = .forallE domain' body' ∧
      env.IsType Us.length Δ.toCtx domain' ∧
      env.IsType Us.length (domain' :: Δ.toCtx) body' ∧
      TrExprS env Us Δ domain domain' ∧
      TrExprS env Us ((none, .vlam domain') :: Δ) body body' := by
  cases run with
  | forallE domainType bodyType domain_tr body_tr =>
    exact ⟨_, _, rfl, domainType, bodyType, domain_tr, body_tr⟩

/-- Recursively turn every retained candidate observation into verified
normalization evidence, constructing and transporting the exact verified
binder context at each Pi node. -/
theorem CandidateExprRun.exists_ofCandidate
    (trace : AddInductive.CandidateExprTrace candidateContext source)
    (candidateRun : CandidateContextRun candidateContext)
    (source' : VExpr)
    (source_tr : candidateRun.context.TrExprS source source')
    (whnfFuel : Nat)
    (whnfDepth : candidateContext.fuel.recDepth = whnfFuel + 1) :
    ∃ view' inferred',
      Nonempty (CandidateExprRun candidateRun.context.venv
        candidateRun.context.lparams trace candidateRun.context.vlctx
        source' view' inferred') := by
  induction trace generalizing source' with
  | terminal context source inferred result checked normalized =>
    obtain ⟨inferred', result', _, _, ⟨node⟩⟩ :=
      CandidateNodeRun.exists_ofCandidate context source inferred result
        checked normalized candidateRun.context candidateRun.context_eq
        candidateRun.state_wf source' source_tr
        context.fuel.recDepth whnfFuel rfl whnfDepth
    exact ⟨result', inferred', ⟨.terminal node⟩⟩
  | forallE context source inferred name domain body binderInfo fresh
      annotations annotationsEq checked normalized
      domainCandidate bodyCandidate domainIH bodyIH =>
    obtain ⟨inferred', result', _, result_tr, ⟨node⟩⟩ :=
      CandidateNodeRun.exists_ofCandidate context source inferred
        (.forallE name domain body binderInfo) checked normalized
        candidateRun.context candidateRun.context_eq candidateRun.state_wf
        source' source_tr context.fuel.recDepth whnfFuel rfl whnfDepth
    let .forallE domainType bodyType domain_tr body_tr := result_tr
    obtain ⟨u, domainTypeHasType⟩ := domainType
    obtain ⟨v, bodyTypeHasType⟩ := bodyType
    obtain ⟨domainView', domainInferred', ⟨domainRun⟩⟩ :=
      domainIH candidateRun _ domain_tr whnfDepth
    obtain ⟨storedDomain', storedDomain_tr⟩ :=
      candidateTypeAnnotation_exists_translation annotations.trace domain_tr
    let annotationsRun := IsDefEqRun.ofCandidateStep
      ⟨context, domain, annotations.consumed⟩ annotationsEq
      candidateRun.context candidateRun.context_eq rfl rfl rfl
      candidateRun.state_wf domain_tr storedDomain_tr
      context.fuel.recDepth rfl
    have henv : VEnv.WF candidateRun.context.venv :=
      candidateRun.context.Ewf
    have hΔ : OnCtx candidateRun.context.vlctx.toCtx
        (candidateRun.context.venv.IsType
          candidateRun.context.lparams.length) :=
      candidateRun.context.Δwf.toCtx
    have annotationDef :=
      annotationsRun.isDefEqU.of_l henv hΔ domainTypeHasType
    let bodyCandidateRun := candidateRun.pushLocalDecl name binderInfo
      annotations.consumed fresh storedDomain' storedDomain_tr
        ⟨u, annotationDef.hasType.2⟩
    have bodyVenv : bodyCandidateRun.context.venv =
        candidateRun.context.venv := rfl
    have bodyLparams : bodyCandidateRun.context.lparams =
        candidateRun.context.lparams := rfl
    have bodyVlctx : bodyCandidateRun.context.vlctx =
        (some (context.freshFVarId, annotations.consumed.fvarsList),
          .vlam storedDomain') :: candidateRun.context.vlctx := rfl
    have bodyDepth :
        (context.pushLocalDecl name binderInfo
          annotations.consumed).fuel.recDepth = whnfFuel + 1 := by
      simpa [AddInductive.Context.pushLocalDecl] using whnfDepth
    have domainContext : VLCtx.IsDefEq
        candidateRun.context.venv candidateRun.context.lparams.length
        ((none, .vlam _) :: candidateRun.context.vlctx)
        ((none, .vlam storedDomain') :: candidateRun.context.vlctx) :=
      .cons (.refl henv candidateRun.context.Δwf) (by nofun)
        (.vlam annotationDef)
    obtain ⟨storedBody', storedBody_tr⟩ :=
      body_tr.defeqDFC henv domainContext
    have hRawBody : OnCtx
        (_ :: candidateRun.context.vlctx.toCtx)
        (candidateRun.context.venv.IsType
          candidateRun.context.lparams.length) :=
      ⟨hΔ, ⟨u, domainTypeHasType⟩⟩
    have bodySource :=
      (body_tr.uniq henv domainContext storedBody_tr).of_l
        henv hRawBody bodyTypeHasType
    have bodyΔwf := bodyCandidateRun.context.Δwf
    rw [bodyVenv, bodyLparams, bodyVlctx] at bodyΔwf
    have instantiatedBody_tr :=
      storedBody_tr.inst_fvar henv.ordered bodyΔwf
    obtain ⟨bodyView', bodyInferred', ⟨bodyRun⟩⟩ :=
      bodyIH bodyCandidateRun _ (by
        change TrExprS bodyCandidateRun.context.venv
          bodyCandidateRun.context.lparams bodyCandidateRun.context.vlctx
          (body.instantiate1 context.freshExpr) _
        rw [bodyVenv, bodyLparams, bodyVlctx]
        simpa only [AddInductive.Context.freshExpr,
          Expr.instantiate1_eq] using instantiatedBody_tr)
        bodyDepth
    refine ⟨.forallE domainView' bodyView', inferred', ⟨?_⟩⟩
    exact .forallE annotations annotationsEq domainCandidate bodyCandidate node
      domainRun annotationsRun bodyRun domainTypeHasType bodyTypeHasType
      bodySource bodyVlctx

/-- Interpret a recursively identity-normalizing candidate at the exact
strict Theory translation of its source.

Unlike `exists_ofCandidate`, whose verified executions select an existential
Theory endpoint, this theorem retains `source'` as the endpoint at every
recursive position. That stronger conclusion is what the generation spine
assembler needs for declarations whose executable normalization is
syntactically the identity. -/
theorem CandidateExprRun.exists_ofIdentity
    (trace : AddInductive.CandidateExprTrace candidateContext source)
    (identity : CandidateExprIdentity trace)
    (candidateRun : CandidateContextRun candidateContext)
    (source' : VExpr)
    (source_tr : candidateRun.context.TrExprS source source')
    (whnfFuel : Nat)
    (whnfDepth : candidateContext.fuel.recDepth = whnfFuel + 1) :
    ∃ inferred', Nonempty
      (CandidateExprRun candidateRun.context.venv
        candidateRun.context.lparams trace candidateRun.context.vlctx
        source' source' inferred') := by
  induction identity generalizing source' with
  | @terminal result source context inferred checked normalized result_eq =>
    subst result
    have result_tr : candidateRun.context.TrExpr source source' :=
      source_tr.trExpr candidateRun.context.Ewf candidateRun.context.Δwf
    obtain ⟨inferred', ⟨node⟩⟩ :=
      CandidateNodeRun.exists_ofCandidateAtResult
        context source inferred source checked normalized
        candidateRun.context candidateRun.context_eq candidateRun.state_wf
        source' source' source_tr result_tr
        context.fuel.recDepth whnfFuel rfl whnfDepth
    exact ⟨inferred', ⟨.terminal node⟩⟩
  | @forallE context domain name binderInfo source inferred body fresh
      annotations annotationsEq checked normalized domainCandidate
      bodyCandidate source_eq consumed_eq domainIdentity bodyIdentity
      domainIH bodyIH =>
    subst source
    obtain ⟨domain', body', rfl, domainWF, bodyWF, domain_tr, body_tr⟩ :=
      TypeChecker.TrExprS.forallE_components source_tr
    obtain ⟨u, domainType⟩ := domainWF
    obtain ⟨v, bodyType⟩ := bodyWF
    have result_tr : candidateRun.context.TrExpr
        (.forallE name domain body binderInfo)
          (.forallE domain' body') :=
      source_tr.trExpr candidateRun.context.Ewf candidateRun.context.Δwf
    obtain ⟨inferred', ⟨node⟩⟩ :=
      CandidateNodeRun.exists_ofCandidateAtResult
        context (.forallE name domain body binderInfo) inferred
        (.forallE name domain body binderInfo) checked normalized
        candidateRun.context candidateRun.context_eq candidateRun.state_wf
        (.forallE domain' body') (.forallE domain' body')
        source_tr result_tr
        context.fuel.recDepth whnfFuel rfl whnfDepth
    obtain ⟨domainInferred', ⟨domainRun⟩⟩ :=
      domainIH candidateRun domain' domain_tr whnfDepth
    have consumed_tr : candidateRun.context.TrExprS
        annotations.consumed domain' := by
      rw [consumed_eq]
      exact domain_tr
    let annotationsRun := IsDefEqRun.ofCandidateStep
      ⟨context, domain, annotations.consumed⟩ annotationsEq
      candidateRun.context candidateRun.context_eq rfl rfl rfl
      candidateRun.state_wf domain_tr consumed_tr
      context.fuel.recDepth rfl
    let bodyCandidateRun := candidateRun.pushLocalDecl name binderInfo
      annotations.consumed fresh domain' consumed_tr ⟨u, domainType⟩
    have bodyVenv : bodyCandidateRun.context.venv =
        candidateRun.context.venv := rfl
    have bodyLparams : bodyCandidateRun.context.lparams =
        candidateRun.context.lparams := rfl
    have bodyVlctx : bodyCandidateRun.context.vlctx =
        (some (context.freshFVarId, annotations.consumed.fvarsList),
          .vlam domain') :: candidateRun.context.vlctx := rfl
    have bodyDepth :
        (context.pushLocalDecl name binderInfo
          annotations.consumed).fuel.recDepth =
          whnfFuel + 1 := by
      simpa [AddInductive.Context.pushLocalDecl] using whnfDepth
    have instantiatedBody_tr :=
      body_tr.inst_fvar candidateRun.context.Ewf.ordered
        bodyCandidateRun.context.Δwf
    obtain ⟨bodyInferred', ⟨bodyRun⟩⟩ :=
      bodyIH bodyCandidateRun body' (by
        change TrExprS bodyCandidateRun.context.venv
          bodyCandidateRun.context.lparams bodyCandidateRun.context.vlctx
          (body.instantiate1 context.freshExpr) body'
        rw [bodyVenv, bodyLparams, bodyVlctx]
        simpa only [AddInductive.Context.freshExpr,
          Expr.instantiate1_eq] using instantiatedBody_tr)
        bodyDepth
    refine ⟨inferred', ⟨?_⟩⟩
    exact .forallE annotations annotationsEq domainCandidate bodyCandidate
      node domainRun annotationsRun bodyRun domainType bodyType bodyType rfl

/-- Recover a trace root's strict source translation from its retained full
check.  Unlike recursive child nodes, whose source translations are obtained
from the parent Pi translation, a root needs only the checker's syntactic
free-variable premise. -/
theorem candidateExprTrace_exists_source_translation
    (trace : AddInductive.CandidateExprTrace candidateContext source)
    (candidateRun : CandidateContextRun candidateContext)
    (source_fvars :
      source.FVarsIn (· ∈ candidateRun.context.vlctx.fvars)) :
    ∃ source', candidateRun.context.TrExprS source source' := by
  let checked := trace.rootCheck
  obtain ⟨source', _, source_tr, _, _⟩ :=
    candidateCheckTypeStep_exists_translation
      ⟨candidateContext, source, checked.inferred⟩ checked.valid
      candidateRun.context candidateRun.context_eq candidateRun.state_wf
      source_fvars candidateContext.fuel.recDepth rfl
  exact ⟨source', source_tr⟩

/-- Recursively certify an annotation-complete candidate trace without asking
the caller for any Theory expression. The retained root full check chooses the
source translation; all output and child translations then come from verified
checker executions, structural annotation traces, and Pi decomposition. -/
theorem CandidateExprRun.exists_ofCandidateFVars
    (trace : AddInductive.CandidateExprTrace candidateContext source)
    (candidateRun : CandidateContextRun candidateContext)
    (source_fvars :
      source.FVarsIn (· ∈ candidateRun.context.vlctx.fvars))
    (whnfFuel : Nat)
    (whnfDepth : candidateContext.fuel.recDepth = whnfFuel + 1) :
    ∃ source' view' inferred',
      candidateRun.context.TrExprS source source' ∧
      Nonempty (CandidateExprRun candidateRun.context.venv
        candidateRun.context.lparams trace candidateRun.context.vlctx
        source' view' inferred') := by
  obtain ⟨source', source_tr⟩ :=
    candidateExprTrace_exists_source_translation trace candidateRun
      source_fvars
  obtain ⟨view', inferred', run⟩ :=
    CandidateExprRun.exists_ofCandidate trace candidateRun source'
      source_tr whnfFuel whnfDepth
  exact ⟨source', view', inferred', source_tr, run⟩

/-- Fold a complete candidate trace into the compositional equality language
consumed by `NormalizationRun` and `GenerationRun`. -/
def CandidateExprRun.evidence
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {Δ : VLCtx} {source' view' inferred' : VExpr} :
    CandidateExprRun env Us trace Δ source' view' inferred' →
      DefEqEvidence env Us.length Δ.toCtx source' view' inferred'
  | .terminal node => node.evidence
  | .forallE _ _ _ _ node domainRun annotationsRun bodyRun domainType
      bodyType bodySource bodyContext => by
    have henv : VEnv.WF env := by
      simpa only [node.check.venv_eq] using node.check.context.Ewf
    have hΔ : VLCtx.WF env Us.length Δ := by
      simpa only [node.check.venv_eq, node.check.lparams_eq,
        node.check.vlctx_eq] using node.check.context.Δwf
    have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := hΔ.toCtx
    have domainEvidence := domainRun.evidence
    obtain ⟨_, domainTypeEq⟩ :=
      domainType.uniq henv hΓ domainEvidence.isDefEq
    have domainAtSort : DefEqEvidence env Us.length Δ.toCtx
        _ _ (.sort _) :=
      .change domainTypeEq.symm domainEvidence
    have annotationDef :=
      annotationsRun.isDefEqU.of_l henv hΓ domainType
    have domainContext : VLCtx.IsDefEq env Us.length
        ((none, .vlam _) :: Δ) ((none, .vlam _) :: Δ) :=
      .cons (.refl henv hΔ) (by nofun) (.vlam annotationDef)
    have bodyEvidence := bodyRun.evidence
    rw [bodyContext] at bodyEvidence
    simp only [VLCtx.toCtx] at bodyEvidence
    have bodyStoredType :=
      bodySource.hasType.2.defeqDFC henv domainContext.defeqCtx
    have hBodyΓ : OnCtx (_ :: Δ.toCtx) (env.IsType Us.length) :=
      ⟨hΓ, ⟨_, annotationDef.hasType.2⟩⟩
    obtain ⟨_, bodyTypeEq⟩ :=
      bodyStoredType.uniq henv hBodyΓ bodyEvidence.isDefEq
    have bodyAtSortStored : DefEqEvidence env Us.length
        (_ :: Δ.toCtx) _ _ (.sort _) :=
      .change bodyTypeEq.symm bodyEvidence
    have bodyAtSortRaw :=
      bodyAtSortStored.isDefEq.defeqDFC henv
        (domainContext.symm henv).defeqCtx
    have bodyFinal := bodySource.trans bodyAtSortRaw
    have piEvidence := DefEqEvidence.forallE domainAtSort
      (DefEqEvidence.ofDefEq bodyFinal)
    obtain ⟨_, nodeTypeEq⟩ :=
      node.evidence.isDefEq.uniq henv hΓ (domainType.forallE bodyType)
    exact .trans node.evidence (.change nodeTypeEq.symm piEvidence)

/-- The raw root of a recursively interpreted trace has the strict Theory
translation retained by its paired full-check run. -/
theorem CandidateExprRun.source_tr
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {Δ : VLCtx} {source' view' inferred' : VExpr}
    (run : CandidateExprRun env Us trace Δ source' view' inferred') :
    TrExprS env Us Δ source source' := by
  cases run with
  | terminal node => exact node.check.expr_tr
  | forallE _ _ _ _ node => exact node.check.expr_tr

/-- Move a weak expression translation between definitionally equal verified
local contexts while retaining its named Theory meaning. -/
private theorem candidateTrExpr_moveCtx
    (henv : VEnv.WF env)
    (hctx : VLCtx.IsDefEq env Us.length Δ₁ Δ₂)
    (H : TrExpr env Us Δ₁ e e') :
    TrExpr env Us Δ₂ e e' := by
  obtain ⟨e₂, he₂, hdef⟩ := H
  have moved : TrExpr env Us Δ₂ e e₂ :=
    he₂.defeqDFC' henv hctx
  exact moved.defeq henv (hctx.symm henv).wf.toCtx
    (hdef.defeqDFC henv hctx.defeqCtx)

/-- The recursively reconstructed kernel candidate view translates to the
Theory view named by `CandidateExprRun`.

At Pi nodes the instantiated child body is first abstracted from its exact
free-variable context and then transported from the raw-domain context to the
definitionally equal normalized-domain context.  This closes the provenance
loop: the emitted Theory equality is not only between two well-typed terms;
both endpoints are translations of the source-indexed candidate syntax. -/
theorem CandidateExprRun.view_tr
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {Δ : VLCtx} {source' view' inferred' : VExpr}
    (run : CandidateExprRun env Us trace Δ source' view' inferred') :
    TrExpr env Us Δ trace.view view' := by
  induction run with
  | terminal node => exact node.whnf.rhs_tr
  | @forallE domain context name binderInfo Δ source inferred body
      source' domain' body' inferred' domainView' domainInferred'
      storedDomain' bodyΔ storedBody' bodyView' bodyInferred' u v fresh
      checked normalized annotations annotationsEq domainCandidate
      bodyCandidate node domainRun annotationsRun bodyRun domainType bodyType
      bodySource bodyContext domainIH bodyIH =>
    have henv : VEnv.WF env := by
      simpa only [node.check.venv_eq] using node.check.context.Ewf
    have hΔ : VLCtx.WF env Us.length Δ := by
      simpa only [node.check.venv_eq, node.check.lparams_eq,
        node.check.vlctx_eq] using node.check.context.Δwf
    obtain ⟨_, domainTypeEq⟩ :=
      domainType.uniq henv hΔ.toCtx domainRun.evidence.isDefEq
    have domainDef : env.IsDefEq Us.length Δ.toCtx
        domain' domainView' (.sort u) :=
      (DefEqEvidence.change domainTypeEq.symm domainRun.evidence).isDefEq
    have annotationDef :=
      annotationsRun.isDefEqU.of_l henv hΔ.toCtx domainType
    have storedToView : env.IsDefEq Us.length Δ.toCtx
        storedDomain' domainView' (.sort u) :=
      annotationDef.symm.trans domainDef
    have bodyIH' : TrExpr env Us
        ((some (context.freshFVarId,
          annotations.consumed.fvarsList), .vlam storedDomain') :: Δ)
        bodyCandidate.view bodyView' := by
      simpa only [bodyContext] using bodyIH
    have bodyAbstract := bodyIH'.abstract VLCtx.Abstract.zero
    have hctx : VLCtx.IsDefEq env Us.length
        ((none, .vlam storedDomain') :: Δ)
        ((none, .vlam domainView') :: Δ) :=
      .cons (.refl henv hΔ) (by nofun)
        (.vlam storedToView)
    have bodyMoved := candidateTrExpr_moveCtx henv hctx bodyAbstract
    have bodyEvidence := bodyRun.evidence
    rw [bodyContext] at bodyEvidence
    simp only [VLCtx.toCtx] at bodyEvidence
    have annotationContext : VLCtx.IsDefEq env Us.length
        ((none, .vlam domain') :: Δ)
        ((none, .vlam storedDomain') :: Δ) :=
      .cons (.refl henv hΔ) (by nofun) (.vlam annotationDef)
    have bodyStoredType :=
      bodySource.hasType.2.defeqDFC henv annotationContext.defeqCtx
    have hBodyΓ : OnCtx (storedDomain' :: Δ.toCtx)
        (env.IsType Us.length) :=
      ⟨hΔ.toCtx, ⟨_, annotationDef.hasType.2⟩⟩
    obtain ⟨_, bodyTypeEq⟩ :=
      bodyStoredType.uniq henv hBodyΓ bodyEvidence.isDefEq
    have bodyDefStored : env.IsDefEq Us.length
        (storedDomain' :: Δ.toCtx) storedBody' bodyView' (.sort v) :=
      (DefEqEvidence.change bodyTypeEq.symm bodyEvidence).isDefEq
    have bodyDefMoved :=
      bodyDefStored.defeqDFC henv hctx.defeqCtx
    have habstract :
        bodyCandidate.view.abstract #[context.freshExpr] =
          Expr.abstract1 context.freshFVarId bodyCandidate.view := by
      rw [show #[context.freshExpr] =
        ⟨[context.freshFVarId].map Expr.fvar⟩ by rfl]
      simp only [Expr.abstract_eq, Expr.abstractList]
    apply TrExpr.forallE henv hΔ
    · exact ⟨_, domainDef.hasType.2⟩
    · exact ⟨_, bodyDefMoved.hasType.2⟩
    · exact domainIH
    · simpa only [AddInductive.CandidateExprTrace.view,
        habstract] using bodyMoved

/-- Root-level verified context and translations for an exact executable
candidate expression and an explicitly named Theory view.

The raw endpoint is a strict translation of the stored kernel source. The
view endpoint translates the exact reconstructed candidate syntax; allowing
the ordinary `TrExpr` relation here accounts for the definitional transport
performed while recursively rebuilding Pi bodies. -/
structure CandidateExprRootRun (env : VEnv) (Us : List Name)
    {source : Expr} (candidate : AddInductive.CandidateExpr source)
    (source' view' : VExpr) where
  contextRun : CandidateContextRun candidate.context
  venv_eq : contextRun.context.venv = env
  lparams_eq : contextRun.context.lparams = Us
  vlctx_eq : contextRun.context.vlctx = []
  source_tr : TrExprS env Us [] source source'
  view_tr : TrExpr env Us [] candidate.view view'
  whnfFuel : Nat
  whnfDepth : candidate.context.fuel.recDepth = whnfFuel + 1

/-- Interpret a root candidate against its explicitly translated endpoints.
The candidate view is not selected from a proof-only existential: the caller
names it and proves that it translates the exact executable view, while the
verified recursive run supplies the equality to the strict raw endpoint. -/
theorem CandidateExprRootRun.evidence
    {env : VEnv} {Us : List Name} {source : Expr}
    {candidate : AddInductive.CandidateExpr source}
    {source' view' : VExpr}
    (run : CandidateExprRootRun env Us candidate source' view') :
    ∃ A, DefEqEvidence env Us.length [] source' view' A := by
  have source_tr : run.contextRun.context.TrExprS source source' := by
    simpa only [VContext.TrExprS, run.venv_eq, run.lparams_eq,
      run.vlctx_eq] using run.source_tr
  obtain ⟨candidateView', inferred', ⟨candidateRun⟩⟩ :=
    CandidateExprRun.exists_ofCandidate candidate.trace run.contextRun
      source' source_tr run.whnfFuel run.whnfDepth
  have henv : VEnv.WF env := by
    simpa only [run.venv_eq] using run.contextRun.context.Ewf
  have hΔ : VLCtx.WF env Us.length [] := by
    simpa only [run.venv_eq, run.lparams_eq, run.vlctx_eq] using
      run.contextRun.context.Δwf
  have candidateView_tr :
      TrExpr env Us [] candidate.view candidateView' := by
    simpa only [run.venv_eq, run.lparams_eq, run.vlctx_eq] using
      candidateRun.view_tr
  have viewDef : env.IsDefEqU Us.length [] candidateView' view' :=
    candidateView_tr.uniq henv (.refl henv hΔ) run.view_tr
  have sourceDef : env.IsDefEqU Us.length [] source' candidateView' := by
    simpa only [run.venv_eq, run.lparams_eq, run.vlctx_eq] using
      candidateRun.evidence.isDefEq.toU
  obtain ⟨A, hfinal⟩ := sourceDef.trans henv hΔ.toCtx viewDef
  exact ⟨A, .ofDefEq hfinal⟩

/-- Pointwise checker-produced equality for a pair of binder telescopes. The
tail is checked in the context extended by the raw binder, exactly matching
`VEnv.TelDefEq` and the mixed generator's raw-binder discipline. -/
inductive TelDefEqEvidence (env : VEnv) (U : Nat) :
    List VExpr → List VExpr → List VExpr → Prop where
  | nil : TelDefEqEvidence env U Γ [] []
  | cons
      (head : DefEqEvidence env U Γ A A' (.sort u))
      (tail : TelDefEqEvidence env U (A :: Γ) As As') :
      TelDefEqEvidence env U Γ (A :: As) (A' :: As')

/-- Interpret pointwise checker evidence as the Theory telescope equality
consumed by `GenerationChecked.WF`. -/
theorem TelDefEqEvidence.telDefEq :
    TelDefEqEvidence env U Γ As As' →
      env.TelDefEq U Γ As As'
  | .nil => trivial
  | .cons head tail => ⟨⟨_, head.isDefEq⟩, tail.telDefEq⟩

/-- Pointwise telescope equality followed by equality of the terminal result.

Keeping these witnesses in one inductive preserves the raw-binder context at
every recursive step.  In particular, the result is checked in
`rawBinders.reverse ++ Γ`, exactly the context used by mixed generation. -/
inductive TelResultDefEqEvidence (env : VEnv) (U : Nat) :
    (Γ : List VExpr) → (rawBinders viewBinders : List VExpr) →
      (rawResult viewResult resultType : VExpr) → Prop where
  | terminal
      (result : DefEqEvidence env U Γ rawResult viewResult resultType) :
      TelResultDefEqEvidence env U Γ [] [] rawResult viewResult resultType
  | forallE
      (domain : DefEqEvidence env U Γ rawDomain viewDomain (.sort u))
      (tail : TelResultDefEqEvidence env U (rawDomain :: Γ)
        rawBinders viewBinders rawResult viewResult resultType) :
      TelResultDefEqEvidence env U Γ
        (rawDomain :: rawBinders) (viewDomain :: viewBinders)
        rawResult viewResult resultType

/-- Telescope component of a combined spine/result certificate. -/
def TelResultDefEqEvidence.telescope :
    TelResultDefEqEvidence env U Γ rawBinders viewBinders
      rawResult viewResult resultType →
      TelDefEqEvidence env U Γ rawBinders viewBinders
  | .terminal _ => .nil
  | .forallE domain tail => .cons domain tail.telescope

/-- Terminal component, in the context generated by all raw binders. -/
def TelResultDefEqEvidence.result :
    TelResultDefEqEvidence env U Γ rawBinders viewBinders
      rawResult viewResult resultType →
      DefEqEvidence env U (rawBinders.reverse ++ Γ)
        rawResult viewResult resultType
  | .terminal result => by simpa using result
  | .forallE _ tail => by
      simpa [List.reverse_cons, List.append_assoc] using tail.result

theorem TelResultDefEqEvidence.length_eq :
    TelResultDefEqEvidence env U Γ rawBinders viewBinders
      rawResult viewResult resultType →
      rawBinders.length = viewBinders.length
  | .terminal _ => rfl
  | .forallE _ tail => congrArg Nat.succ tail.length_eq

/-- Reify a Theory telescope equality as explicit checker-produced evidence.
This direction is useful after telescope operations such as `take`, `drop`,
and context transport have rearranged a candidate certificate. -/
def TelDefEqEvidence.ofTelDefEq :
    ∀ {Γ As As'}, env.TelDefEq U Γ As As' →
      TelDefEqEvidence env U Γ As As'
  | _, [], [], _ => .nil
  | _, _ :: _, _ :: _, ⟨⟨_, head⟩, tail⟩ =>
    .cons (.ofDefEq head) (TelDefEqEvidence.ofTelDefEq tail)

/-- Retain an exact prefix of a checker-produced telescope certificate. -/
def TelDefEqEvidence.take
    (run : TelDefEqEvidence env U Γ As As') (n : Nat) :
    TelDefEqEvidence env U Γ (As.take n) (As'.take n) :=
  .ofTelDefEq (run.telDefEq.take n)

/-- Transport a checker-produced telescope certificate through environment
growth. -/
def TelDefEqEvidence.mono
    (run : TelDefEqEvidence env U Γ As As') (henv : env ≤ env') :
    TelDefEqEvidence env' U Γ As As' :=
  .ofTelDefEq (run.telDefEq.mono henv)

/-- Combine an independently transformed telescope certificate with its
terminal result certificate. -/
def TelResultDefEqEvidence.ofTelescopeResult
    (tel : TelDefEqEvidence env U Γ rawBinders viewBinders)
    (result : DefEqEvidence env U (rawBinders.reverse ++ Γ)
      rawResult viewResult resultType) :
    TelResultDefEqEvidence env U Γ rawBinders viewBinders
      rawResult viewResult resultType := by
  induction tel with
  | nil => exact .terminal (by simpa using result)
  | cons head tail ih =>
    exact .forallE head (ih (by
      simpa [List.reverse_cons, List.append_assoc] using result))

private theorem candidateDefEqCtx_trans (henv : VEnv.WF env) :
    ∀ {Γ₁ Γ₂ Γ₃},
      env.IsDefEqCtx U [] Γ₁ Γ₂ →
      env.IsDefEqCtx U [] Γ₂ Γ₃ →
      env.IsDefEqCtx U [] Γ₁ Γ₃
  | _, _, _, .zero, h₂₃ => h₂₃
  | _, _, _, .succ h₁₂ head₁₂, .succ h₂₃ head₂₃ => by
    have tail := candidateDefEqCtx_trans henv h₁₂ h₂₃
    have head₂₃' := head₂₃.defeqDFC henv (h₁₂.symm henv)
    exact .succ tail (VEnv.IsDefEq.trans_l henv h₁₂.isType
      head₁₂ head₂₃')

private theorem candidateTelDefEq_defeqDFC (henv : VEnv.WF env)
    (hctx : env.IsDefEqCtx U [] Γ₁ Γ₂) :
    ∀ {As As'}, env.TelDefEq U Γ₁ As As' →
      env.TelDefEq U Γ₂ As As'
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨⟨u, head⟩, tail⟩ =>
    ⟨⟨u, head.defeqDFC henv hctx⟩,
      candidateTelDefEq_defeqDFC henv
        (.succ hctx head.hasType.1) tail⟩

private theorem candidateTelDefEq_append
    {env : VEnv} {U : Nat} {Γ : List VExpr} :
    ∀ {As As' Bs Bs'}, env.TelDefEq U Γ As As' →
      env.TelDefEq U (As.reverse ++ Γ) Bs Bs' →
      env.TelDefEq U Γ (As ++ Bs) (As' ++ Bs')
  | [], [], _, _, _, suffix => by simpa using suffix
  | _ :: As, _ :: As', Bs, Bs', ⟨head, tail⟩, suffix => by
    exact ⟨head, candidateTelDefEq_append tail (by
      simpa [List.reverse_cons, List.append_assoc] using suffix)⟩

/-- Replace a constructor candidate's stored parameter prefix by the family's
raw parameter prefix.

The two raw prefixes need not be syntactically equal: both are related to the
same checked view prefix. The field telescope and terminal result are then
transported through the induced context equality, yielding exactly the mixed
raw/view context emitted by generation. -/
def TelResultDefEqEvidence.replacePrefix
    (henv : VEnv.WF env)
    (newPrefix : TelDefEqEvidence env U [] newRawPrefix viewPrefix)
    (run : TelResultDefEqEvidence env U []
      (oldRawPrefix ++ rawSuffix) (viewPrefix ++ viewSuffix)
      rawResult viewResult resultType)
    (prefixLength : oldRawPrefix.length = viewPrefix.length) :
    TelResultDefEqEvidence env U []
      (newRawPrefix ++ rawSuffix) (viewPrefix ++ viewSuffix)
      rawResult viewResult resultType := by
  have declaredTel := run.telescope.telDefEq
  have oldPrefix : env.TelDefEq U [] oldRawPrefix viewPrefix := by
    have hprefix := declaredTel.take oldRawPrefix.length
    simpa [prefixLength] using hprefix
  have oldSuffix : env.TelDefEq U oldRawPrefix.reverse
      rawSuffix viewSuffix := by
    have suffix := declaredTel.drop oldRawPrefix.length
    simpa [prefixLength] using suffix
  have newPrefixTheory := newPrefix.telDefEq
  have newPrefixContext : env.IsDefEqCtx U []
      newRawPrefix.reverse viewPrefix.reverse := by
    simpa using newPrefixTheory.ctx
  have oldPrefixContext : env.IsDefEqCtx U []
      oldRawPrefix.reverse viewPrefix.reverse := by
    simpa using oldPrefix.ctx
  have prefixContext : env.IsDefEqCtx U []
      newRawPrefix.reverse oldRawPrefix.reverse :=
    candidateDefEqCtx_trans henv newPrefixContext
      (oldPrefixContext.symm henv)
  have newSuffix : env.TelDefEq U newRawPrefix.reverse
      rawSuffix viewSuffix :=
    candidateTelDefEq_defeqDFC henv (prefixContext.symm henv) oldSuffix
  have emittedTel : env.TelDefEq U []
      (newRawPrefix ++ rawSuffix) (viewPrefix ++ viewSuffix) :=
    candidateTelDefEq_append newPrefixTheory (by simpa using newSuffix)
  have fullContext : env.IsDefEqCtx U []
      ((newRawPrefix ++ rawSuffix).reverse)
      ((oldRawPrefix ++ rawSuffix).reverse) := by
    have extended := newSuffix.raw_onTel.extendDefEqCtx prefixContext
    simpa [List.reverse_append] using extended
  have oldResult : DefEqEvidence env U
      (oldRawPrefix ++ rawSuffix).reverse
      rawResult viewResult resultType := by
    simpa using run.result
  have emittedResult : DefEqEvidence env U
      (newRawPrefix ++ rawSuffix).reverse
      rawResult viewResult resultType :=
    .ofDefEq (oldResult.isDefEq.defeqDFC henv
      (fullContext.symm henv))
  exact TelResultDefEqEvidence.ofTelescopeResult
    (.ofTelDefEq emittedTel) (by simpa using emittedResult)

/-- Every recursive candidate run carries the well-formed local context used
by its root checker observation. -/
theorem CandidateExprRun.context_wf
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {Δ : VLCtx} {source' view' inferred' : VExpr}
    (run : CandidateExprRun env Us trace Δ source' view' inferred') :
    VLCtx.WF env Us.length Δ := by
  cases run with
  | terminal node =>
    simpa only [node.check.venv_eq, node.check.lparams_eq,
      node.check.vlctx_eq] using node.check.context.Δwf
  | forallE _ _ _ _ node =>
    simpa only [node.check.venv_eq, node.check.lparams_eq,
      node.check.vlctx_eq] using node.check.context.Δwf

private theorem candidateTelN_forallN_length :
    ∀ (As : List VExpr) (B : VExpr),
      VExpr.telN As.length (VExpr.forallN As B) = As
  | [], _ => rfl
  | _ :: As, B => by
    simp only [List.length_cons, VExpr.forallN, VExpr.telN,
      candidateTelN_forallN_length As B]

private theorem candidateDropN_forallN_length :
    ∀ (As : List VExpr) (B : VExpr),
      VExpr.dropN As.length (VExpr.forallN As B) = B
  | [], _ => rfl
  | _ :: As, B => by
    simp only [List.length_cons, VExpr.forallN, VExpr.dropN,
      candidateDropN_forallN_length As B]

/-- Recursive worker for candidate spine extraction.

`rawΔ` follows the contexts generated by the stored raw binders, while `Δ`
is the annotation-consumed context in which the candidate body was checked.
The explicit context equality transports each retained checker judgment back
to the raw side before it is added to the telescope certificate. -/
private theorem CandidateExprRun.spineEvidenceAux
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {Δ : VLCtx} {source' view' inferred' : VExpr}
    (run : CandidateExprRun env Us trace Δ source' view' inferred')
    (aligned : trace.storedSpine = true)
    {rawΔ : VLCtx} {rawSource' : VExpr}
    (contextEq : VLCtx.IsDefEq env Us.length rawΔ Δ)
    (rawSource_tr : TrExprS env Us rawΔ source rawSource') :
    ∃ rawBinders viewBinders rawResult viewResult resultType,
      rawSource' = VExpr.forallN rawBinders rawResult ∧
      view' = VExpr.forallN viewBinders viewResult ∧
      TelResultDefEqEvidence env Us.length rawΔ.toCtx
        rawBinders viewBinders rawResult viewResult resultType ∧
      rawBinders.length = trace.spineLength := by
  induction run generalizing rawΔ rawSource' with
  | terminal node =>
    have henv : VEnv.WF env := by
      simpa only [node.check.venv_eq] using node.check.context.Ewf
    have hRawΔ := contextEq.wf
    have rawToSource : env.IsDefEqU Us.length rawΔ.toCtx
        rawSource' _ :=
      rawSource_tr.uniq henv contextEq node.check.expr_tr
    have sourceToView :=
      node.evidence.isDefEq.defeqDFC henv
        (contextEq.symm henv).defeqCtx
    have final := VEnv.IsDefEq.transU_r henv hRawΔ.toCtx
      rawToSource sourceToView
    exact ⟨[], [], rawSource', _, _, rfl, rfl,
      .terminal (.ofDefEq final), rfl⟩
  | @forallE domain context name binderInfo Δ source inferred body
      source' domain' body' inferred' domainView' domainInferred'
      storedDomain' bodyΔ storedBody' bodyView' bodyInferred' u v fresh
      checked normalized annotations annotationsEq domainCandidate
      bodyCandidate node domainRun annotationsRun bodyRun domainType bodyType
      bodySource bodyContext domainIH bodyIH =>
    simp only [AddInductive.CandidateExprTrace.storedSpine,
      Bool.and_eq_true] at aligned
    obtain ⟨sourceEq, bodyAligned⟩ := aligned
    have alignedSource_tr : TrExprS env Us rawΔ
        (.forallE name domain body binderInfo) rawSource' :=
      rawSource_tr.eqv sourceEq
    let @TrExprS.forallE _ _ rawDomain rawBody _ _ _ _ _
        rawDomainType rawBodyType rawDomain_tr rawBody_tr := alignedSource_tr
    have henv : VEnv.WF env := by
      simpa only [node.check.venv_eq] using node.check.context.Ewf
    have hΔ : VLCtx.WF env Us.length Δ := by
      simpa only [node.check.venv_eq, node.check.lparams_eq,
        node.check.vlctx_eq] using node.check.context.Δwf
    have hRawΔ := contextEq.wf
    have rawToDomainU :=
      rawDomain_tr.uniq henv contextEq domainRun.source_tr
    have domainTypeRaw :=
      domainType.defeqDFC henv (contextEq.symm henv).defeqCtx
    have rawToDomain :=
      rawToDomainU.of_r henv hRawΔ.toCtx domainTypeRaw
    have domainToView :=
      domainRun.evidence.isDefEq.toU.of_l henv hΔ.toCtx domainType
    have domainToViewRaw :=
      domainToView.defeqDFC henv (contextEq.symm henv).defeqCtx
    have head : DefEqEvidence env Us.length rawΔ.toCtx
        _ domainView' (.sort u) :=
      .ofDefEq (rawToDomain.trans domainToViewRaw)
    have annotationDef :=
      annotationsRun.isDefEqU.of_l henv hΔ.toCtx domainType
    have annotationDefRaw :=
      annotationDef.defeqDFC henv (contextEq.symm henv).defeqCtx
    have rawToStored := rawToDomain.trans annotationDefRaw
    have bodyWF := bodyRun.context_wf
    rw [bodyContext] at bodyWF
    have rawFresh :
        ∀ fv deps,
          some (context.freshFVarId, annotations.consumed.fvarsList) =
              some (fv, deps) →
            fv ∉ rawΔ.fvars ∧ deps ⊆ rawΔ.fvars := by
      intro fv deps heq
      cases heq
      have hfresh := bodyWF.2.1 _ _ rfl
      simpa only [contextEq.fvars] using hfresh
    let rawBodyΔ : VLCtx :=
      (some (context.freshFVarId, annotations.consumed.fvarsList),
        .vlam rawDomain) :: rawΔ
    have bodyContextEqConcrete : VLCtx.IsDefEq env Us.length rawBodyΔ
        ((some (context.freshFVarId, annotations.consumed.fvarsList),
          .vlam storedDomain') :: Δ) :=
      .cons contextEq rawFresh (.vlam rawToStored)
    have bodyContextEq : VLCtx.IsDefEq env Us.length rawBodyΔ bodyΔ := by
      simpa only [bodyContext] using bodyContextEqConcrete
    have rawBodyΔwf := bodyContextEq.wf
    have rawBodyInst_tr : TrExprS env Us rawBodyΔ
        (body.instantiate1 context.freshExpr) rawBody := by
      simpa only [AddInductive.Context.freshExpr,
        Expr.instantiate1_eq] using
        rawBody_tr.inst_fvar henv.ordered rawBodyΔwf
    obtain ⟨rawBinders, viewBinders, rawResult, viewResult,
        resultType, rawBodyEq, viewBodyEq, tail, tailLength⟩ :=
      bodyIH bodyAligned bodyContextEq rawBodyInst_tr
    refine ⟨rawDomain :: rawBinders,
      domainView' :: viewBinders, rawResult, viewResult, resultType,
      ?_, ?_, ?_, ?_⟩
    · simp only [VExpr.forallN, rawBodyEq]
    · simp only [VExpr.forallN, viewBodyEq]
    · exact .forallE head (by
        simpa only [rawBodyΔ, VLCtx.toCtx] using tail)
    · simpa only [List.length_cons,
        AddInductive.CandidateExprTrace.spineLength] using
        congrArg Nat.succ tailLength

/-- Extract exact raw/view telescopes and terminal results from a recursive
candidate run whose WHNF traversal preserved the stored Pi spine.

The binder count is computed from the source-indexed trace, and `telN`/
`dropN` name the exact stored raw and reconstructed-view components.  This
avoids recovering binder equality from whole-Pi definitional equality and so
does not use the unfinished forall-injectivity theorem. -/
theorem CandidateExprRun.spineEvidence
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {Δ : VLCtx} {source' view' inferred' : VExpr}
    (run : CandidateExprRun env Us trace Δ source' view' inferred')
    (aligned : trace.storedSpine = true) :
    ∃ resultType,
      TelResultDefEqEvidence env Us.length Δ.toCtx
        (VExpr.telN trace.spineLength source')
        (VExpr.telN trace.spineLength view')
        (VExpr.dropN trace.spineLength source')
        (VExpr.dropN trace.spineLength view') resultType := by
  have henv : VEnv.WF env := by
    cases run with
    | terminal node =>
      simpa only [node.check.venv_eq] using node.check.context.Ewf
    | forallE _ _ _ _ node =>
      simpa only [node.check.venv_eq] using node.check.context.Ewf
  obtain ⟨rawBinders, viewBinders, rawResult, viewResult,
      resultType, rawEq, viewEq, evidence, rawLength⟩ :=
    run.spineEvidenceAux aligned
      (.refl henv run.context_wf) run.source_tr
  have viewLength : viewBinders.length = trace.spineLength :=
    evidence.length_eq ▸ rawLength
  have rawTel : VExpr.telN trace.spineLength source' = rawBinders := by
    rw [rawEq, ← rawLength]
    exact candidateTelN_forallN_length rawBinders rawResult
  have viewTel : VExpr.telN trace.spineLength view' = viewBinders := by
    rw [viewEq, ← viewLength]
    exact candidateTelN_forallN_length viewBinders viewResult
  have rawResultEq :
      VExpr.dropN trace.spineLength source' = rawResult := by
    rw [rawEq, ← rawLength]
    exact candidateDropN_forallN_length rawBinders rawResult
  have viewResultEq :
      VExpr.dropN trace.spineLength view' = viewResult := by
    rw [viewEq, ← viewLength]
    exact candidateDropN_forallN_length viewBinders viewResult
  simpa only [rawTel, viewTel, rawResultEq, viewResultEq] using
    ⟨resultType, evidence⟩

/-- Replace only the terminal typing index of a combined certificate. The
telescope and both result endpoints remain definitionally unchanged. -/
def TelResultDefEqEvidence.withResult
    (run : TelResultDefEqEvidence env U Γ rawBinders viewBinders
      rawResult viewResult resultType)
    (result : DefEqEvidence env U (rawBinders.reverse ++ Γ)
      rawResult viewResult resultType') :
    TelResultDefEqEvidence env U Γ rawBinders viewBinders
      rawResult viewResult resultType' := by
  induction run with
  | terminal _ => exact .terminal (by simpa using result)
  | forallE domain tail ih =>
    exact .forallE domain (ih (by
      simpa [List.reverse_cons, List.append_assoc] using result))

/-- Fix a candidate terminal equality at a known type of its right endpoint.
This is the bridge from the candidate's checker-inferred type to the precise
sort required by dependent inductive analysis. -/
def TelResultDefEqEvidence.ofRightType
    (henv : VEnv.WF env) (hΓ : OnCtx Γ (env.IsType U))
    (run : TelResultDefEqEvidence env U Γ rawBinders viewBinders
      rawResult viewResult resultType)
    (rightType : env.HasType U (rawBinders.reverse ++ Γ)
      viewResult expectedType) :
    TelResultDefEqEvidence env U Γ rawBinders viewBinders
      rawResult viewResult expectedType := by
  have hctx : OnCtx (rawBinders.reverse ++ Γ) (env.IsType U) :=
    (run.telescope.telDefEq.extendCtx (.refl hΓ)).isType
  exact run.withResult (.ofDefEq
    (run.result.isDefEq.toU.of_r henv hctx rightType))

theorem CandidateExprRun.env_wf
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {Δ : VLCtx} {source' view' inferred' : VExpr}
    (run : CandidateExprRun env Us trace Δ source' view' inferred') :
    VEnv.WF env := by
  cases run with
  | terminal node =>
    simpa only [node.check.venv_eq] using node.check.context.Ewf
  | forallE _ _ _ _ node =>
    simpa only [node.check.venv_eq] using node.check.context.Ewf

/-- An exact recursive run whose executable main spine preserves the stored
binders. Unlike a whole-expression root equality, this package is strong
enough to expose generation's pointwise binder and terminal-result evidence. -/
def CandidateExprSpineRun (env : VEnv) (Us : List Name)
    {source : Expr} (candidate : AddInductive.CandidateExpr source)
    (raw view : VExpr) : Prop :=
  candidate.trace.storedSpine = true ∧
    ∃ inferred, CandidateExprRun env Us candidate.trace [] raw view inferred

theorem CandidateExprSpineRun.evidence
    (run : CandidateExprSpineRun env Us candidate raw view) :
    ∃ resultType,
      TelResultDefEqEvidence env Us.length []
        (VExpr.telN candidate.trace.spineLength raw)
        (VExpr.telN candidate.trace.spineLength view)
        (VExpr.dropN candidate.trace.spineLength raw)
        (VExpr.dropN candidate.trace.spineLength view) resultType := by
  obtain ⟨aligned, _, recursive⟩ := run
  exact recursive.spineEvidence aligned

/-- Align extracted candidate components with named raw/view telescope and
result data, then fix the terminal type from a checked right-endpoint typing
judgment. All four alignment premises are syntactic equations. -/
theorem CandidateExprSpineRun.evidenceAt
    (run : CandidateExprSpineRun env Us candidate raw view)
    (rawTel : VExpr.telN candidate.trace.spineLength raw = rawBinders)
    (viewTel : VExpr.telN candidate.trace.spineLength view = viewBinders)
    (rawResult_eq :
      VExpr.dropN candidate.trace.spineLength raw = rawResult)
    (viewResult_eq :
      VExpr.dropN candidate.trace.spineLength view = viewResult)
    (rightType : env.HasType Us.length rawBinders.reverse
      viewResult expectedType) :
    TelResultDefEqEvidence env Us.length [] rawBinders viewBinders
      rawResult viewResult expectedType := by
  obtain ⟨aligned, _, recursive⟩ := run
  obtain ⟨resultType, evidence⟩ := recursive.spineEvidence aligned
  have exactEvidence : TelResultDefEqEvidence env Us.length []
      rawBinders viewBinders rawResult viewResult resultType := by
    simpa only [rawTel, viewTel, rawResult_eq, viewResult_eq] using evidence
  exact exactEvidence.ofRightType recursive.env_wf trivial (by
    simpa using rightType)

end TypeChecker

namespace VInductDecl

/-- A one-family normalization candidate validated by compositional verified
normalization evidence at the kernel's two declaration stages.

The family comparison runs in `env`. Constructor comparisons run in the exact
`typeEnv` obtained by inserting the raw family constant. The positional
`Forall₂` prevents a shorter checker-result list from certifying a declaration.
-/
structure NormalizationRun {source : VInductDecl}
    (norm : Normalization source) (env : VEnv) where
  raw : VInductiveType
  view : VInductiveType
  source_types_eq : source.types = [raw]
  view_types_eq : norm.view.types = [view]
  family : ∃ A,
    TypeChecker.DefEqEvidence env source.uvars []
      raw.type view.type A
  typeEnv : VEnv
  addType :
    env.addConst raw.name raw.toVConstant = some typeEnv
  constructors : List.Forall₂
    (fun rawCtor viewCtor =>
      ∃ A, TypeChecker.DefEqEvidence typeEnv source.uvars []
        rawCtor.type viewCtor.type A)
    raw.ctors view.ctors

/-- Checker-validated family and constructor comparisons establish the
semantic part of the raw/view normalization boundary. -/
theorem NormalizationRun.wf
    (run : NormalizationRun norm env) : norm.WF env := by
  refine ⟨run.raw, run.view, run.source_types_eq, run.view_types_eq, ?_, ?_⟩
  · obtain ⟨_, hfamily⟩ := run.family
    exact hfamily.isDefEq.toU
  · intro envT hadd
    have henv : envT = run.typeEnv := by
      have : some envT = some run.typeEnv := hadd.symm.trans run.addType
      exact Option.some.inj this
    subst envT
    exact run.constructors.imp fun _ _ h => by
      obtain ⟨_, hctor⟩ := h
      exact hctor.isDefEq.toU

/-- One constructor candidate tied to the corresponding raw Theory constant.
Its expression payload may normalize, but its name, universe arity, and exact
source position remain fixed. -/
structure CandidateConstructorRun (env : VEnv) (Us : List Name)
    {source : Constructor}
    (candidate : AddInductive.CandidateConstructor source)
    (raw : VConstVal) where
  name_eq : source.name = raw.name
  uvars_eq : raw.uvars = Us.length
  viewType : VExpr
  typeRun : TypeChecker.CandidateExprRootRun env Us candidate.type
    raw.type viewType

/-- Replace only the expression payload certified by the constructor run. -/
def CandidateConstructorRun.view
    (run : CandidateConstructorRun env Us candidate raw) : VConstVal :=
  { raw with type := run.viewType }

/-- Exact positional certification for a source-indexed constructor list and
the raw Theory constructor list. Unlike `zip`, this type cannot truncate a
longer side or reuse evidence at a different source position. -/
inductive CandidateConstructorListRun (env : VEnv) (Us : List Name) :
    {sources : List Constructor} →
      AddInductive.CandidateList AddInductive.CandidateConstructor sources →
      List VConstVal → Type where
  | nil : CandidateConstructorListRun env Us .nil []
  | cons
      (head : CandidateConstructorRun env Us candidate raw)
      (tail : CandidateConstructorListRun env Us candidates raws) :
      CandidateConstructorListRun env Us
        (.cons candidate candidates) (raw :: raws)

/-- The exact normalized constructor list retained by a positional run. -/
def CandidateConstructorListRun.views :
    CandidateConstructorListRun env Us candidates raws → List VConstVal
  | .nil => []
  | .cons head tail => head.view :: tail.views

/-- Positional certification preserves every constructor header. -/
theorem CandidateConstructorListRun.sameHeaders
    (run : CandidateConstructorListRun env Us candidates raws) :
    sameCtorHeaders raws run.views = true := by
  induction run with
  | nil => rfl
  | cons head tail ih =>
    simp [CandidateConstructorListRun.views,
      CandidateConstructorRun.view, sameCtorHeaders, ih]

/-- Collect the exact checker-produced equality for every positional raw/view
constructor pair. -/
theorem CandidateConstructorListRun.evidence
    (run : CandidateConstructorListRun env Us candidates raws) :
    List.Forall₂
      (fun raw view => ∃ A,
        TypeChecker.DefEqEvidence env Us.length []
          raw.type view.type A)
      raws run.views := by
  induction run with
  | nil => exact .nil
  | cons head tail ih =>
    exact .cons head.typeRun.evidence ih

/-- One family candidate certified in the input environment, together with
all of its constructors certified in the exact environment obtained by
inserting the raw family constant. -/
structure CandidateFamilyRun (env : VEnv) (Us : List Name)
    {source : InductiveType}
    (candidate : AddInductive.CandidateFamily source)
    (raw : VInductiveType) where
  name_eq : source.name = raw.name
  uvars_eq : raw.uvars = Us.length
  viewType : VExpr
  typeRun : TypeChecker.CandidateExprRootRun env Us
    candidate.familyType.type raw.type viewType
  typeEnv : VEnv
  addType : env.addConst raw.name raw.toVConstant = some typeEnv
  constructors : CandidateConstructorListRun typeEnv Us
    candidate.constructors raw.ctors

/-- Replace only the family and constructor expression payloads named by the
certified candidate runs. -/
def CandidateFamilyRun.view
    (run : CandidateFamilyRun env Us candidate raw) : VInductiveType :=
  { raw with
    type := run.viewType
    ctors := run.constructors.views }

/-- Exact singleton candidate-list certification against one raw Theory
declaration. The singleton kernel-source index rules out partial selection of
a family candidate, and `raw_types_eq` rules out partial selection of a Theory
family. Mutual blocks remain an explicit later generalization. -/
structure NormalizationCandidateRun (env : VEnv) (Us : List Name)
    {source : InductiveType}
    (candidate : AddInductive.NormalizationCandidate [source])
    (rawDecl : VInductDecl) where
  raw : VInductiveType
  raw_types_eq : rawDecl.types = [raw]
  uvars_eq : rawDecl.uvars = Us.length
  family : CandidateFamilyRun env Us candidate.families.singleton raw

/-- The Theory declaration obtained from the exact singleton candidate. -/
def NormalizationCandidateRun.viewDecl
    (run : NormalizationCandidateRun env Us candidate rawDecl) :
    VInductDecl :=
  { rawDecl with types := [run.family.view] }

/-- Candidate-list shape evidence is sufficient to construct the Theory
normalization boundary without `head!`, unchecked `zip`, or an arbitrary view
declaration supplied separately from the candidate. -/
def NormalizationCandidateRun.normalization
    (run : NormalizationCandidateRun env Us candidate rawDecl) :
    Normalization rawDecl where
  view := run.viewDecl
  shape_eq := by
    simp only [normalizationShape, NormalizationCandidateRun.viewDecl,
      run.raw_types_eq, beq_self_eq_true, Bool.true_and, sameTypeHeaders,
      CandidateFamilyRun.view]
    simp [run.family.constructors.sameHeaders]

/-- Assemble the existing semantic normalization certificate from the exact
family and constructor candidate runs. -/
def NormalizationCandidateRun.normalizationRun
    (run : NormalizationCandidateRun env Us candidate rawDecl) :
    NormalizationRun run.normalization env where
  raw := run.raw
  view := run.family.view
  source_types_eq := run.raw_types_eq
  view_types_eq := rfl
  family := by
    simpa only [run.uvars_eq] using run.family.typeRun.evidence
  typeEnv := run.family.typeEnv
  addType := run.family.addType
  constructors := by
    simpa only [run.uvars_eq] using run.family.constructors.evidence

/-- Checker-produced semantic evidence for one positional raw/view
constructor pair. This has the same four-way declared/emitted split as
`NormalizedCtor.WF`, but keeps every equality in compositional evidence form
until the final Theory boundary. -/
structure NormalizedCtorRun {source : VInductDecl}
    (block : NormalizedChecked source) (ctor : NormalizedCtor)
    (env : VEnv) where
  declaredTel : TypeChecker.TelDefEqEvidence env source.uvars []
    (ctor.declaredBinders source.nparams) (ctor.viewBinders block)
  declaredResult : TypeChecker.DefEqEvidence env source.uvars
    (ctor.declaredBinders source.nparams).reverse
    (ctor.rawResult source.nparams) (ctor.resultTarget block)
    (.sort block.checked.resultLevel)
  emittedTel : TypeChecker.TelDefEqEvidence env source.uvars []
    (ctor.emittedBinders block) (ctor.viewBinders block)
  emittedResult : TypeChecker.DefEqEvidence env source.uvars
    (ctor.emittedBinders block).reverse
    (ctor.rawResult source.nparams) (ctor.resultTarget block)
    (.sort block.checked.resultLevel)

theorem NormalizedCtorRun.wf
    (run : NormalizedCtorRun block ctor env) :
    ctor.WF block env where
  declaredTel := run.declaredTel.telDefEq
  declaredResult := run.declaredResult.isDefEq
  emittedTel := run.emittedTel.telDefEq
  emittedResult := run.emittedResult.isDefEq

/-- Complete checker-side assembler for a generation-ready candidate.

The exact family insertion state is named once. This lets a producer check
constructor evidence in that state and lets `.wf` discharge the universally
quantified post-family environment in `GenerationChecked.WF` by equality,
without an oracle or an assumed transaction. -/
structure GenerationRun {source : VInductDecl}
    (generation : GenerationChecked source) (env : VEnv) where
  normalization : NormalizationRun generation.block.normalization env
  checked : generation.block.checked.WF env
  familyTel : TypeChecker.TelDefEqEvidence env source.uvars []
    (generation.block.rawParams ++ generation.block.rawIndices)
    (generation.block.checked.params ++ generation.block.checked.indices)
  familyResult : TypeChecker.DefEqEvidence env source.uvars
    (generation.block.rawParams ++ generation.block.rawIndices).reverse
    generation.block.rawResult (.sort generation.block.checked.resultLevel)
    (.sort (.succ generation.block.checked.resultLevel))
  typeEnv : VEnv
  addType : env.addConst generation.block.sourceType.name
    generation.block.sourceType.toVConstant = some typeEnv
  constructors :
    ∀ ctor ∈ generation.block.ctorPairs,
      NormalizedCtorRun generation.block ctor typeEnv

/-- Assemble the complete Theory generation certificate from exact
checker-produced normalization, telescope, result, and constructor evidence. -/
theorem GenerationRun.wf
    (run : GenerationRun generation env) :
    generation.WF env := by
  refine {
    blockWF := ⟨run.normalization.wf, run.checked⟩
    familyTel := run.familyTel.telDefEq
    familyResult := run.familyResult.isDefEq
    ctors := ?_ }
  intro envT hadd ctor hctor
  have henv : envT = run.typeEnv := by
    have : some envT = some run.typeEnv := hadd.symm.trans run.addType
    exact Option.some.inj this
  subst envT
  exact (run.constructors ctor hctor).wf

/-- Exact family-spine evidence extracted from the source-indexed singleton
normalization candidate and aligned with the components retained by dependent
inductive analysis. -/
structure CandidateFamilyGenerationRun
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    (normalization : NormalizationCandidateRun env Us candidate source)
    (generation : GenerationChecked source) where
  spine : TypeChecker.CandidateExprSpineRun env Us
    candidate.families.singleton.familyType.type
    normalization.raw.type normalization.family.viewType
  rawTel : VExpr.telN
      candidate.families.singleton.familyType.type.trace.spineLength
      normalization.raw.type =
    generation.block.rawParams ++ generation.block.rawIndices
  viewTel : VExpr.telN
      candidate.families.singleton.familyType.type.trace.spineLength
      normalization.family.viewType =
    generation.block.checked.params ++ generation.block.checked.indices
  rawResult : VExpr.dropN
      candidate.families.singleton.familyType.type.trace.spineLength
      normalization.raw.type = generation.block.rawResult
  viewResult : VExpr.dropN
      candidate.families.singleton.familyType.type.trace.spineLength
      normalization.family.viewType =
    .sort generation.block.checked.resultLevel
  rightType : env.HasType Us.length
    (generation.block.rawParams ++ generation.block.rawIndices).reverse
    (.sort generation.block.checked.resultLevel)
    (.sort (.succ generation.block.checked.resultLevel))

/-- Extract the complete family telescope/result certificate at the exact
components consumed by `GenerationRun`. -/
def CandidateFamilyGenerationRun.evidence
    {env : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    {normalization : NormalizationCandidateRun env Us candidate source}
    {generation : GenerationChecked source}
    (run : CandidateFamilyGenerationRun normalization generation) :
    TypeChecker.TelResultDefEqEvidence env Us.length []
      (generation.block.rawParams ++ generation.block.rawIndices)
      (generation.block.checked.params ++ generation.block.checked.indices)
      generation.block.rawResult
      (.sort generation.block.checked.resultLevel)
      (.sort (.succ generation.block.checked.resultLevel)) :=
  run.spine.evidenceAt run.rawTel run.viewTel
    run.rawResult run.viewResult run.rightType

/-- One positional constructor candidate aligned with the raw/view
constructor pair retained by dependent analysis.

The spine certificate covers the exact stored constructor type. Its declared
telescope will later be transformed into the mixed emitted telescope by
replacing only the constructor's parameter prefix. -/
structure CandidateNormalizedCtorRun {source : VInductDecl}
    (block : NormalizedChecked source) (env : VEnv) (Us : List Name)
    {kernelSource : Constructor}
    {candidate : AddInductive.CandidateConstructor kernelSource}
    {raw : VConstVal}
    (root : CandidateConstructorRun env Us candidate raw)
    (ctor : NormalizedCtor) where
  raw_eq : ctor.raw = raw
  view_eq : ctor.view.value = root.view
  spine : TypeChecker.CandidateExprSpineRun env Us candidate.type
    raw.type root.viewType
  rawTel : VExpr.telN candidate.type.trace.spineLength raw.type =
    ctor.declaredBinders source.nparams
  viewTel : VExpr.telN candidate.type.trace.spineLength root.viewType =
    ctor.viewBinders block
  rawResult : VExpr.dropN candidate.type.trace.spineLength raw.type =
    ctor.rawResult source.nparams
  viewResult : VExpr.dropN candidate.type.trace.spineLength root.viewType =
    ctor.resultTarget block
  rightType : env.HasType Us.length
    (ctor.declaredBinders source.nparams).reverse
    (ctor.resultTarget block) (.sort block.checked.resultLevel)

/-- Extract the stored constructor's declared telescope/result evidence. -/
def CandidateNormalizedCtorRun.declaredEvidence
    {source : VInductDecl} {block : NormalizedChecked source}
    {env : VEnv} {Us : List Name}
    {kernelSource : Constructor}
    {candidate : AddInductive.CandidateConstructor kernelSource}
    {raw : VConstVal}
    {root : CandidateConstructorRun env Us candidate raw}
    {ctor : NormalizedCtor}
    (run : CandidateNormalizedCtorRun block env Us root ctor) :
    TypeChecker.TelResultDefEqEvidence env Us.length []
      (ctor.declaredBinders source.nparams) (ctor.viewBinders block)
      (ctor.rawResult source.nparams) (ctor.resultTarget block)
      (.sort block.checked.resultLevel) :=
  run.spine.evidenceAt run.rawTel run.viewTel
    run.rawResult run.viewResult run.rightType

/-- Produce both constructor paths required by `NormalizedCtorRun`.

The declared path comes directly from the constructor candidate. The emitted
path replaces the stored constructor parameter prefix by the raw family
parameter prefix, transporting fields and result through the induced
definitionally equal context. -/
def CandidateNormalizedCtorRun.normalizedCtorRun
    {source : VInductDecl} {block : NormalizedChecked source}
    {env : VEnv} {Us : List Name}
    {kernelSource : Constructor}
    {candidate : AddInductive.CandidateConstructor kernelSource}
    {raw : VConstVal}
    {root : CandidateConstructorRun env Us candidate raw}
    {ctor : NormalizedCtor}
    (run : CandidateNormalizedCtorRun block env Us root ctor)
    (henv : VEnv.WF env) (uvars_eq : source.uvars = Us.length)
    (familyParams : TypeChecker.TelDefEqEvidence env Us.length []
      block.rawParams block.checked.params)
    (prefixLength :
      (VExpr.telN source.nparams ctor.raw.type).length =
        block.checked.params.length) :
    NormalizedCtorRun block ctor env := by
  have declared := run.declaredEvidence
  have declaredSplit : TypeChecker.TelResultDefEqEvidence env Us.length []
      (VExpr.telN source.nparams ctor.raw.type ++
        ctor.rawFields source.nparams)
      (block.checked.params ++ ctor.view.fields)
      (ctor.rawResult source.nparams) (ctor.resultTarget block)
      (.sort block.checked.resultLevel) := by
    simpa only [NormalizedCtor.declaredBinders,
      NormalizedCtor.viewBinders] using declared
  have emitted := declaredSplit.replacePrefix henv familyParams prefixLength
  exact {
    declaredTel := by
      simpa only [uvars_eq] using declared.telescope
    declaredResult := by
      simpa only [uvars_eq, List.append_nil] using declared.result
    emittedTel := by
      simpa only [uvars_eq, NormalizedCtor.emittedBinders,
        NormalizedCtor.viewBinders] using emitted.telescope
    emittedResult := by
      simpa only [uvars_eq, NormalizedCtor.emittedBinders,
        List.append_nil] using emitted.result }

/-- Dependent positional alignment between every constructor candidate run
and every normalized constructor pair. The indices make unequal lengths,
reordering, and evidence reuse at a different source position impossible. -/
inductive CandidateNormalizedCtorListRun {source : VInductDecl}
    (block : NormalizedChecked source) (env : VEnv) (Us : List Name) :
    {kernelSources : List Constructor} →
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor kernelSources} →
    {raws : List VConstVal} →
    (roots : CandidateConstructorListRun env Us candidates raws) →
    List NormalizedCtor → Type where
  | nil : CandidateNormalizedCtorListRun block env Us .nil []
  | cons
      (head : CandidateNormalizedCtorRun block env Us root ctor)
      (tail : CandidateNormalizedCtorListRun block env Us roots ctors) :
      CandidateNormalizedCtorListRun block env Us
        (.cons root roots) (ctor :: ctors)

/-- Assemble a `NormalizedCtorRun` for every constructor in an exact
dependent positional list. -/
theorem CandidateNormalizedCtorListRun.normalizedCtorRuns
    {source : VInductDecl} {block : NormalizedChecked source}
    {env : VEnv} {Us : List Name}
    {kernelSources : List Constructor}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor kernelSources}
    {raws : List VConstVal}
    {roots : CandidateConstructorListRun env Us candidates raws}
    {ctors : List NormalizedCtor}
    (run : CandidateNormalizedCtorListRun block env Us roots ctors)
    (henv : VEnv.WF env) (uvars_eq : source.uvars = Us.length)
    (familyParams : TypeChecker.TelDefEqEvidence env Us.length []
      block.rawParams block.checked.params)
    (prefixLengths : ∀ ctor ∈ ctors,
      (VExpr.telN source.nparams ctor.raw.type).length =
        block.checked.params.length) :
    ∀ ctor ∈ ctors, NormalizedCtorRun block ctor env := by
  induction run with
  | nil => intro ctor hctor; simp at hctor
  | cons head tail ih =>
    intro ctor hctor
    simp only [List.mem_cons] at hctor
    rcases hctor with rfl | hctor
    · exact head.normalizedCtorRun henv uvars_eq familyParams
        (prefixLengths _ (.head _))
    · exact ih
        (fun ctor hctor => prefixLengths ctor (.tail _ hctor))
        ctor hctor

/-- Complete source-indexed candidate certificate for one generation-ready
singleton inductive declaration.

`normalization_eq` ties the retained analyzer block to the candidate-derived
normalization. `constructors` then aligns every post-family candidate run with
the corresponding dependent analyzer pair. -/
structure GenerationCandidateRun
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    (normalization : NormalizationCandidateRun env Us candidate source)
    (generation : GenerationChecked source) where
  normalization_eq :
    generation.block.normalization = normalization.normalization
  checked : generation.block.checked.WF env
  family : CandidateFamilyGenerationRun normalization generation
  typeEnv_wf : VEnv.WF normalization.family.typeEnv
  constructors : CandidateNormalizedCtorListRun generation.block
    normalization.family.typeEnv Us normalization.family.constructors
    generation.block.ctorPairs

/-- Assemble the existing checker-side `GenerationRun` entirely from the
source-indexed normalization candidate and its exact spine certificates. -/
def GenerationCandidateRun.generationRun
    {env : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    {normalization : NormalizationCandidateRun env Us candidate source}
    {generation : GenerationChecked source}
    (run : GenerationCandidateRun normalization generation) :
    GenerationRun generation env := by
  have familyEvidence := run.family.evidence
  have familyParams : TypeChecker.TelDefEqEvidence env Us.length []
      generation.block.rawParams generation.block.checked.params := by
    apply TypeChecker.TelDefEqEvidence.ofTelDefEq
    simpa [generation.shape.2.1] using
      familyEvidence.telescope.telDefEq.take
        generation.block.rawParams.length
  have familyParamsTypeEnv := familyParams.mono
    (VEnv.addConst_le normalization.family.addType)
  have sourceType_eq : generation.block.sourceType = normalization.raw := by
    have h : [generation.block.sourceType] = [normalization.raw] :=
      generation.block.source_types_eq.symm.trans normalization.raw_types_eq
    injection h
  refine {
    normalization := by
      simpa only [run.normalization_eq] using
        normalization.normalizationRun
    checked := run.checked
    familyTel := by
      simpa only [normalization.uvars_eq] using familyEvidence.telescope
    familyResult := by
      simpa only [normalization.uvars_eq, List.append_nil] using
        familyEvidence.result
    typeEnv := normalization.family.typeEnv
    addType := by
      simpa only [sourceType_eq] using normalization.family.addType
    constructors := ?_ }
  apply run.constructors.normalizedCtorRuns run.typeEnv_wf
    normalization.uvars_eq familyParamsTypeEnv
  intro ctor hctor
  exact (generation.shape.2.2.2.2.2 ctor hctor).2.2.1.trans
    (generation.shape.1.symm.trans generation.shape.2.1)

/-- Public Theory boundary for a complete source-indexed generation
candidate. -/
theorem GenerationCandidateRun.wf
    {env : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    {normalization : NormalizationCandidateRun env Us candidate source}
    {generation : GenerationChecked source}
    (run : GenerationCandidateRun normalization generation) :
    generation.WF env :=
  run.generationRun.wf

/-- Complete dependent semantic package for one Verify-side singleton
candidate.

`kernelSource` and `candidate` retain the exact implementation metadata and
source-indexed operational trace. `normalization` ties that trace to the raw
Theory declaration and its reconstructed view. `generation` is the successful
dependent analysis, and `run` proves that this exact candidate supplies every
semantic obligation consumed by mixed artifact generation. No independently
chosen view can be inserted into this package. -/
structure GenerationCandidatePackage (env : VEnv) (Us : List Name) where
  kernelSource : InductiveType
  source : VInductDecl
  candidate : AddInductive.NormalizationCandidate [kernelSource]
  normalization : NormalizationCandidateRun env Us candidate source
  generation : GenerationChecked source
  run : GenerationCandidateRun normalization generation

/-- Package an already assembled source-indexed candidate run without
repeating any of its dependent indices at a call site. -/
def GenerationCandidateRun.package
    {env : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    {normalization : NormalizationCandidateRun env Us candidate source}
    {generation : GenerationChecked source}
    (run : GenerationCandidateRun normalization generation) :
    GenerationCandidatePackage env Us where
  kernelSource := kernelSource
  source := source
  candidate := candidate
  normalization := normalization
  generation := generation
  run := run

/-- Erase checker and candidate provenance at the consumer boundary. The
result contains only the Theory generation value and its ordinary semantic
certificate, which is the complete input of `VEnv.addInductCertified`. -/
def GenerationCandidatePackage.certificate
    (package : GenerationCandidatePackage env Us) :
    package.source.GenerationCertificate env where
  generation := package.generation
  wf := package.run.wf

/-- Build the general Verify metadata replay from a candidate package and the
ordinary implementation-to-Theory insertion witnesses.

The generation value and its semantic proof are not independent inputs: both
are projected from `package`. The remaining arguments concern only constant
map alignment and the exact successful transaction states, so a caller cannot
pair metadata replay with an unrelated normalized view. -/
def GenerationCandidatePackage.addInductTrace
    (package : GenerationCandidatePackage env Us)
    {m₁ m₂ : ConstMap} {env₂ : VEnv}
    (typeMap : ConstMap) (typeEnv : VEnv)
    (ctorMap : ConstMap) (ctorEnv recEnv : VEnv)
    (addType : AddInductConstant .induct m₁ env
      package.generation.block.sourceType.toVConstVal typeMap typeEnv)
    (addCtors : AddInductConstants .ctor typeMap typeEnv
      package.generation.block.sourceType.ctors ctorMap ctorEnv)
    (addRec : AddInductConstant .recursor ctorMap ctorEnv
      (inductGenerationRecVal package.generation) m₂ recEnv)
    (addRules : AddDefEqs recEnv
      package.generation.generatedRules env₂) :
    AddInductTrace m₁ env package.source m₂ env₂ where
  generation := package.generation
  generation_wf := package.certificate.wf
  typeMap := typeMap
  typeEnv := typeEnv
  ctorMap := ctorMap
  ctorEnv := ctorEnv
  recEnv := recEnv
  addType := addType
  addCtors := addCtors
  addRec := addRec
  addRules := addRules

/-- Optional outer provenance for packages obtained by the executable
metadata pass itself. Keeping the exact producer equation separate from the
semantic package makes the trust boundary explicit: computation selects the
candidate, while `GenerationCandidateRun` alone grants it Theory meaning. -/
structure ProducedGenerationCandidatePackage
    (env : VEnv) (Us : List Name) where
  package : GenerationCandidatePackage env Us
  context : AddInductive.Context
  nparams : Nat
  numNested : Nat
  isUnsafe : Bool
  produced :
    AddInductive.buildNormalizationCandidate nparams
        [package.kernelSource] numNested isUnsafe context =
      .ok package.candidate

/-
The evidence types mention exact verifier executions, so these semantic
interpretation roots intentionally inherit the same transitional Verify
closure as `WhnfRun.isDefEq`. Exact guards ensure that the generic assembler
does not silently widen it.
-/
/--
info: 'Lean4Lean.TypeChecker.VState.WF.empty_of_reserves' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Expr.eqv_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 Syntax.structEq_eq,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms TypeChecker.VState.WF.empty_of_reserves

/--
info: 'Lean4Lean.TypeChecker.candidateFreshFVarId_reserved' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms TypeChecker.candidateFreshFVarId_reserved

/--
info: 'Lean4Lean.TypeChecker.CandidateContextRun.root' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Expr.eqv_eq,
 Level.instLawfulBEqLevel,
 Syntax.structEq_eq]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateContextRun.root

/--
info: 'Lean4Lean.TypeChecker.CandidateContextRun.pushLocalDecl' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Expr.eqv_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 Syntax.structEq_eq,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateContextRun.pushLocalDecl

/--
info: 'Lean4Lean.TypeChecker.candidateCheckTypeStep_exists_translation' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLevelParam_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 Std.TreeMap.all_eq_all_toList,
 Expr.mkAppRangeAux.eq_def,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms TypeChecker.candidateCheckTypeStep_exists_translation

/--
info: 'Lean4Lean.TypeChecker.IsDefEqRun.ofCandidateStep' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms TypeChecker.IsDefEqRun.ofCandidateStep

/--
info: 'Lean4Lean.TypeChecker.IsDefEqRun.isDefEqU' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLevelParam_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 Std.TreeMap.all_eq_all_toList,
 Expr.mkAppRangeAux.eq_def,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms TypeChecker.IsDefEqRun.isDefEqU

/--
info: 'Lean4Lean.TypeChecker.candidateTypeAnnotation_fvarsIn' does not depend on any axioms
-/
#guard_msgs in
#print axioms TypeChecker.candidateTypeAnnotation_fvarsIn

/--
info: 'Lean4Lean.TypeChecker.candidateTypeAnnotation_exists_translation' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms TypeChecker.candidateTypeAnnotation_exists_translation

/--
info: 'Lean4Lean.TypeChecker.CandidateExprRun.exists_ofCandidate' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLevelParam_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 Std.TreeMap.all_eq_all_toList,
 Expr.mkAppRangeAux.eq_def,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateExprRun.exists_ofCandidate

/--
info: 'Lean4Lean.TypeChecker.CandidateExprRun.exists_ofCandidateFVars' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLevelParam_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 Std.TreeMap.all_eq_all_toList,
 Expr.mkAppRangeAux.eq_def,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateExprRun.exists_ofCandidateFVars

/--
info: 'Lean4Lean.TypeChecker.WhnfRun.ofCandidateStep' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms TypeChecker.WhnfRun.ofCandidateStep

/--
info: 'Lean4Lean.TypeChecker.CheckTypeRun.ofCandidateStep' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms TypeChecker.CheckTypeRun.ofCandidateStep

/--
info: 'Lean4Lean.TypeChecker.CandidateNodeRun.ofCandidate' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateNodeRun.ofCandidate

/--
info: 'Lean4Lean.TypeChecker.CandidateNodeRun.exists_ofCandidate' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLevelParam_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 Std.TreeMap.all_eq_all_toList,
 Expr.mkAppRangeAux.eq_def,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateNodeRun.exists_ofCandidate

/--
info: 'Lean4Lean.TypeChecker.CandidateNodeRun.evidence' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLevelParam_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 Std.TreeMap.all_eq_all_toList,
 Expr.mkAppRangeAux.eq_def,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateNodeRun.evidence

/--
info: 'Lean4Lean.TypeChecker.CandidateExprRun.evidence' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLevelParam_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 Std.TreeMap.all_eq_all_toList,
 Expr.mkAppRangeAux.eq_def,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateExprRun.evidence

/--
info: 'Lean4Lean.TypeChecker.CandidateExprRun.source_tr' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateExprRun.source_tr

/--
info: 'Lean4Lean.TypeChecker.CandidateExprRun.view_tr' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLevelParam_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 Std.TreeMap.all_eq_all_toList,
 Expr.mkAppRangeAux.eq_def,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateExprRun.view_tr

/--
info: 'Lean4Lean.TypeChecker.CandidateExprRootRun.evidence' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLevelParam_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 Std.TreeMap.all_eq_all_toList,
 Expr.mkAppRangeAux.eq_def,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateExprRootRun.evidence

/--
info: 'Lean4Lean.TypeChecker.TelDefEqEvidence.telDefEq' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLevelParam_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 Std.TreeMap.all_eq_all_toList,
 Expr.mkAppRangeAux.eq_def,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms TypeChecker.TelDefEqEvidence.telDefEq

/--
info: 'Lean4Lean.TypeChecker.TelDefEqEvidence.ofTelDefEq' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms TypeChecker.TelDefEqEvidence.ofTelDefEq

/--
info: 'Lean4Lean.TypeChecker.TelResultDefEqEvidence.replacePrefix' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLevelParam_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 Std.TreeMap.all_eq_all_toList,
 Expr.mkAppRangeAux.eq_def,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms TypeChecker.TelResultDefEqEvidence.replacePrefix

/--
info: 'Lean4Lean.TypeChecker.CandidateExprRun.spineEvidence' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLevelParam_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 Std.TreeMap.all_eq_all_toList,
 Expr.mkAppRangeAux.eq_def,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateExprRun.spineEvidence

/--
info: 'Lean4Lean.TypeChecker.CandidateExprSpineRun.evidenceAt' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLevelParam_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 Std.TreeMap.all_eq_all_toList,
 Expr.mkAppRangeAux.eq_def,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateExprSpineRun.evidenceAt

/--
info: 'Lean4Lean.VInductDecl.CandidateNormalizedCtorRun.normalizedCtorRun' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLevelParam_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 Std.TreeMap.all_eq_all_toList,
 Expr.mkAppRangeAux.eq_def,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms CandidateNormalizedCtorRun.normalizedCtorRun

/--
info: 'Lean4Lean.VInductDecl.GenerationCandidateRun.wf' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLevelParam_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 Std.TreeMap.all_eq_all_toList,
 Expr.mkAppRangeAux.eq_def,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms GenerationCandidateRun.wf

/--
info: 'Lean4Lean.VInductDecl.CandidateConstructorListRun.sameHeaders' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CandidateConstructorListRun.sameHeaders

/--
info: 'Lean4Lean.VInductDecl.CandidateConstructorListRun.evidence' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLevelParam_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 Std.TreeMap.all_eq_all_toList,
 Expr.mkAppRangeAux.eq_def,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms CandidateConstructorListRun.evidence

/--
info: 'Lean4Lean.VInductDecl.NormalizationCandidateRun.normalization' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NormalizationCandidateRun.normalization

/--
info: 'Lean4Lean.VInductDecl.NormalizationCandidateRun.normalizationRun' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLevelParam_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 Std.TreeMap.all_eq_all_toList,
 Expr.mkAppRangeAux.eq_def,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms NormalizationCandidateRun.normalizationRun

/--
info: 'Lean4Lean.VInductDecl.NormalizedCtorRun.wf' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLevelParam_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 Std.TreeMap.all_eq_all_toList,
 Expr.mkAppRangeAux.eq_def,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms NormalizedCtorRun.wf

/--
info: 'Lean4Lean.VInductDecl.GenerationRun.wf' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLevelParam_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 Std.TreeMap.all_eq_all_toList,
 Expr.mkAppRangeAux.eq_def,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms GenerationRun.wf

/--
info: 'Lean4Lean.VInductDecl.GenerationCandidateRun.package' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms GenerationCandidateRun.package

/--
info: 'Lean4Lean.VInductDecl.GenerationCandidatePackage.certificate' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLevelParam_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 Std.TreeMap.all_eq_all_toList,
 Expr.mkAppRangeAux.eq_def,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms GenerationCandidatePackage.certificate

/--
info: 'Lean4Lean.VInductDecl.GenerationCandidatePackage.addInductTrace' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLevelParam_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.looseBVarRange_eq,
 Expr.lowerLooseBVars_eq,
 Expr.replace_eq,
 Level.hasMVar_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.toList'_push,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 Std.TreeMap.all_eq_all_toList,
 Expr.mkAppRangeAux.eq_def,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms GenerationCandidatePackage.addInductTrace

end VInductDecl

end Lean4Lean
