import Lean4Lean.Verify.TypeChecker
import Lean4Lean.Inductive.ValidationTrace
import Std.Data.TreeSet.Lemmas

namespace Lean4Lean
open Lean hiding Environment Exception
open Kernel

open private Lean.Kernel.Environment.add from Lean.Environment

namespace TypeChecker

/-- Compatibility name for the consumer-neutral reflected-primitive list. -/
@[deprecated Lean4Lean.VEnv.reflectedPrimitiveNames (since := "2026-08-11")]
abbrev reflectedPrimitiveNames : List Name :=
  Lean4Lean.VEnv.reflectedPrimitiveNames

/-- Compatibility shim for the consumer-neutral Theory theorem. -/
@[deprecated Lean4Lean.VEnv.HasPrimitives.of_avoids (since := "2026-08-11")]
theorem VEnv.HasPrimitives.of_avoids
    {env : VEnv}
    (h : ∀ n ∈ reflectedPrimitiveNames, env.constants n = none) :
    env.HasPrimitives :=
  Lean4Lean.VEnv.HasPrimitives.of_avoids h

/-- Compatibility shim for the consumer-neutral Theory theorem. -/
@[deprecated Lean4Lean.VEnv.addConst_other (since := "2026-08-11")]
theorem VEnv.addConst_other
    {env env' : VEnv} {name other : Name} {ci : VConstant}
    (hadd : env.addConst name ci = some env')
    (hne : name ≠ other) :
    env'.constants other = env.constants other :=
  Lean4Lean.VEnv.addConst_other hadd hne

/-- Compatibility shim for the consumer-neutral Theory theorem. -/
@[deprecated Lean4Lean.VEnv.HasPrimitives.addConst (since := "2026-08-11")]
theorem VEnv.HasPrimitives.addConst
    {env env' : VEnv} {name : Name} {ci : VConstant}
    (H : env.HasPrimitives)
    (hname : name ∉ reflectedPrimitiveNames)
    (hadd : env.addConst name ci = some env') :
    env'.HasPrimitives :=
  Lean4Lean.VEnv.HasPrimitives.addConst H hname hadd

/-- A verified implementation local context remains verified when the Theory
environment grows.  Kernel local declarations and their free-variable names
are unchanged; only their translations and typing derivations are transported
monotonically. -/
theorem MLCtx.WF.mono
    {env env' : VEnv} (henv : env ≤ env') :
    ∀ {context : MLCtx} {Us : List Name},
      context.WF env Us → context.WF env' Us
  | .nil, _, _ => trivial
  | .vlam _ _ _ _ _ _, _,
      ⟨tailWF, fresh, type_tr, typeWF⟩ =>
    ⟨tailWF.mono henv, fresh, type_tr.mono henv, typeWF.mono henv⟩
  | .vlet _ _ _ _ _ _ _, _,
      ⟨tailWF, fresh, type_tr, value_tr, valueWF⟩ =>
    ⟨tailWF.mono henv, fresh, type_tr.mono henv,
      value_tr.mono henv, valueWF.mono henv⟩

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

/-- Staging one fresh non-primitive inductive family preserves the kernel-side
primitive safety contract. All old lookups are inherited from the input map;
the only new lookup cannot be primitive by hypothesis. -/
theorem AddInductConstant.safePrimitives
    {pre post : Environment} {env typeEnv : VEnv} {raw : VConstVal}
    (stage : AddInductConstant .induct pre.constants env raw
      post.constants typeEnv)
    (preMapWF : pre.constants.WF)
    (H : pre.find? n = some ci →
      Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = [])
    (hname : Environment.primitives.contains raw.name = false) :
    post.find? n = some ci →
      Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = [] := by
  intro hfind hprim
  have postMapWF := stage.map_wf preMapWF
  change post.constants.find?' n = some ci at hfind
  rw [postMapWF.find?'_eq_find?, stage.map_add,
    preMapWF.find?_insert] at hfind
  split at hfind
  · rename_i heq
    have : raw.name = n := by simpa using heq
    subst n
    rw [hname] at hprim
    contradiction
  · apply H
    change pre.constants.find?' n = some ci
    rw [preMapWF.find?'_eq_find?]
    exact hfind
    exact hprim

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
  rhs_tr : TrExprS env Us Δ rhs rhs'
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
    (rhs_tr : TrExprS env Us Δ step.result rhs')
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
    have strict : run.context.TrExprS rhs rhs' := by
      simpa only [VContext.TrExprS, run.venv_eq, run.lparams_eq,
        run.vlctx_eq] using run.rhs_tr
    exact strict.trExpr run.context.Ewf run.context.Δwf
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

/-- The validator's exact annotation-consumed kernel expression has a strict
Theory translation whenever its raw source does.

The target remains existential and is selected by the source-indexed
annotation trace.  In particular, this theorem does not claim that annotation
peeling is a function of the already translated raw endpoint: strict
translation may erase transparent kernel forms above the annotation wrapper. -/
theorem consumeTypeAnnotations_exists_translation
    (source_tr : TrExprS env Us Δ source source') :
    ∃ consumed',
      TrExprS env Us Δ (AddInductive.consumeTypeAnnotations source)
        consumed' := by
  cases htrace : AddInductive.CandidateTypeAnnotationTrace.build source with
  | mk consumed trace =>
    have consumed_eq : consumed =
        AddInductive.consumeTypeAnnotations source := by
      simpa only [htrace] using
        AddInductive.CandidateTypeAnnotationTrace.build_consumed source
    obtain ⟨consumed', consumed_tr⟩ :=
      candidateTypeAnnotation_exists_translation trace source_tr
    exact ⟨consumed', by simpa only [← consumed_eq] using consumed_tr⟩

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

/-- A fresh local declaration is found at its generated identifier. -/
theorem localContextFindNew
    (lctx : LocalContext) (id : FVarId) (name : Name)
    (type : Expr) (bi : BinderInfo) (kind : LocalDeclKind)
    (hwf : lctx.WF) (hfresh : lctx.find? id = none) :
    (lctx.mkLocalDecl id name type bi kind).find? id =
      some (.cdecl lctx.decls.size id name type bi kind) := by
  have hwf' := LocalContext.WF.mkLocalDecl
    (name := name) (ty := type) (bi := bi) (kind := kind) hwf hfresh
  rw [hwf'.find?_eq_find?_toList]
  rw [LocalContext.mkLocalDecl_toList hwf.decls_wf]
  simp [LocalDecl.fvarId]

/-- The empty local context contains no free-variable declaration. -/
theorem emptyLocalContextFindNone (id : FVarId) :
    (⟨.empty, .empty, .empty⟩ : LocalContext).find? id = none := by
  have h := LocalContext.WF.find?_eq_find?_toList
    (fv := id) LocalContext.WF.nil
  rw [h]
  simp [LocalContext.toList]

/-- Extending a well-formed local context at a fresh identifier preserves
every lookup at an older identifier. -/
theorem localContextFindOld
    (lctx : LocalContext) (oldId newId : FVarId)
    (name : Name) (type : Expr) (bi : BinderInfo)
    (kind : LocalDeclKind) (decl : LocalDecl)
    (hwf : lctx.WF) (hfresh : lctx.find? newId = none)
    (hfind : lctx.find? oldId = some decl) :
    (lctx.mkLocalDecl newId name type bi kind).find? oldId = some decl := by
  have hwf' := LocalContext.WF.mkLocalDecl
    (name := name) (ty := type) (bi := bi) (kind := kind) hwf hfresh
  rw [hwf'.find?_eq_find?_toList]
  rw [LocalContext.mkLocalDecl_toList hwf.decls_wf]
  have hne : oldId ≠ newId := by
    intro heq
    rw [heq, hfresh] at hfind
    contradiction
  simp only [List.find?_cons, LocalDecl.fvarId]
  rw [show (oldId == newId) = false by simp [hne]]
  simpa only [hwf.find?_eq_find?_toList, LocalDecl.fvarId] using hfind

/-- A candidate local context built entirely from fresh ordinary
declarations, with the name-generator invariant needed by structural replay. -/
structure CandidateLocalContextRun
    (context : AddInductive.Context) : Prop where
  wf : context.lctx.WF
  reserves : ∀ decl ∈ context.lctx.toList,
    context.ngen.Reserves decl.fvarId

namespace CandidateLocalContextRun

theorem empty (context : AddInductive.Context)
    (h : context.lctx = ({} : LocalContext)) :
    CandidateLocalContextRun context where
  wf := by rw [h]; exact LocalContext.WF.nil
  reserves := by
    intro decl membership
    rw [h] at membership
    rw [show ({} : LocalContext).toList = [] by rfl] at membership
    contradiction

theorem fresh (run : CandidateLocalContextRun context) :
    context.lctx.find? context.freshFVarId = none := by
  rw [run.wf.find?_eq_find?_toList, List.find?_eq_none]
  intro decl membership equal
  have reserved := run.reserves decl membership
  have idEq : context.freshFVarId = decl.fvarId :=
    beq_iff_eq.mp equal
  rw [← idEq] at reserved
  exact NameGenerator.not_reserves_self (by
    simpa [AddInductive.Context.freshFVarId] using reserved)

theorem push (run : CandidateLocalContextRun context)
    (name : Name) (binderInfo : BinderInfo) (type : Expr) :
    CandidateLocalContextRun
      (context.pushLocalDecl name binderInfo type) where
  wf := by
    simpa [AddInductive.Context.pushLocalDecl] using
      LocalContext.WF.mkLocalDecl run.wf run.fresh
  reserves := by
    intro decl membership
    simp only [AddInductive.Context.pushLocalDecl,
      LocalContext.mkLocalDecl_toList run.wf.decls_wf,
      List.mem_cons] at membership ⊢
    rcases membership with rfl | membership
    · simpa [LocalDecl.fvarId, AddInductive.Context.freshFVarId] using
        (NameGenerator.next_reserves_self (ngen := context.ngen))
    · exact NameGenerator.Reserves.mono NameGenerator.LE.next
        (run.reserves decl membership)

theorem push_findNew (run : CandidateLocalContextRun context)
    (name : Name) (binderInfo : BinderInfo) (type : Expr) :
    (context.pushLocalDecl name binderInfo type).lctx.find?
        context.freshFVarId =
      some (.cdecl context.lctx.decls.size context.freshFVarId
        name type binderInfo .default) := by
  simpa [AddInductive.Context.pushLocalDecl] using
    localContextFindNew context.lctx context.freshFVarId name type
      binderInfo .default run.wf run.fresh

theorem push_findOld (run : CandidateLocalContextRun context)
    (name : Name) (binderInfo : BinderInfo) (type : Expr)
    {id : FVarId} {decl : LocalDecl}
    (hfind : context.lctx.find? id = some decl) :
    (context.pushLocalDecl name binderInfo type).lctx.find? id =
      some decl := by
  simpa [AddInductive.Context.pushLocalDecl] using
    localContextFindOld context.lctx id context.freshFVarId
      name type binderInfo .default decl run.wf run.fresh hfind

end CandidateLocalContextRun

/-- Every local declaration already present at a candidate node remains at
the exact terminal context reached through its main Pi spine. -/
theorem CandidateExprTrace.terminal_findOld
    {context : AddInductive.Context} {source : Expr}
    (trace : AddInductive.CandidateExprTrace context source)
    (localRun : CandidateLocalContextRun context)
    {fv : FVarId} {decl : LocalDecl}
    (found : context.lctx.find? fv = some decl) :
    trace.terminalContext.lctx.find? fv = some decl := by
  induction trace with
  | terminal => exact found
  | forallE context source inferred name domain body binderInfo fresh
      annotations annotationsEq checked normalized domainCandidate
      bodyCandidate domainIH bodyIH =>
      exact bodyIH (localRun.push name binderInfo annotations.consumed)
        (localRun.push_findOld name binderInfo annotations.consumed found)

/-- The fresh free variable allocated for a candidate Pi retains the exact
annotation-consumed kernel domain at the candidate's terminal context. -/
theorem CandidateExprTrace.head_getType_terminal
    {context : AddInductive.Context} (name : Name)
    (binderInfo : BinderInfo) {domain bodySource : Expr}
    (annotations : AddInductive.CandidateTypeAnnotations domain)
    (bodyCandidate : AddInductive.CandidateExprTrace
      (context.pushLocalDecl name binderInfo annotations.consumed) bodySource)
    (localRun : CandidateLocalContextRun context) :
    AddInductive.getType context.freshExpr bodyCandidate.terminalContext =
      .ok annotations.consumed := by
  have foundAtBody := localRun.push_findNew name binderInfo annotations.consumed
  have foundAtTerminal := terminal_findOld bodyCandidate
    (localRun.push name binderInfo annotations.consumed) foundAtBody
  unfold AddInductive.getType
  simp only [getLCtx, ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
    Except.bind, Except.pure]
  change Except.ok ((bodyCandidate.terminalContext.lctx.get!
    context.freshFVarId).type) = _
  simp [LocalContext.get!, foundAtTerminal, LocalDecl.type]

/-- The terminal context retains the literal local declaration allocated by
the head candidate binder. -/
theorem CandidateExprTrace.head_find_terminal
    {context : AddInductive.Context} (name : Name)
    (binderInfo : BinderInfo) {domain bodySource : Expr}
    (annotations : AddInductive.CandidateTypeAnnotations domain)
    (bodyCandidate : AddInductive.CandidateExprTrace
      (context.pushLocalDecl name binderInfo annotations.consumed) bodySource)
    (localRun : CandidateLocalContextRun context) :
    bodyCandidate.terminalContext.lctx.find? context.freshFVarId =
      some (.cdecl context.lctx.decls.size context.freshFVarId
        name annotations.consumed binderInfo .default) := by
  exact CandidateExprTrace.terminal_findOld bodyCandidate
    (localRun.push name binderInfo annotations.consumed)
    (localRun.push_findNew name binderInfo annotations.consumed)

/-- A literal local-context lookup determines the executable free-variable
type query without any additional context reconstruction. -/
theorem getType_fvar_of_find
    {context : AddInductive.Context} {fv : FVarId} {decl : LocalDecl}
    (found : context.lctx.find? fv = some decl) :
    AddInductive.getType (.fvar fv) context = .ok decl.type := by
  unfold AddInductive.getType
  simp only [ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
    Except.bind, Except.pure, getLCtx]
  change Except.ok ((context.lctx.get! fv).type) = .ok decl.type
  simp [LocalContext.get!, found]

/-- Every pre-existing local declaration survives a complete family
telescope traversal.  Only fresh-parameter and index constructors extend the
reader context; shared parameters leave it unchanged. -/
theorem _root_.Lean4Lean.AddInductive.FamilyTypeParameterComparisonTrace.result_findOld
    (trace : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
      context source i nindices fuel)
    (localRun : CandidateLocalContextRun context)
    {fv : FVarId} {decl : LocalDecl}
    (found : context.lctx.find? fv = some decl) :
    trace.result.context.lctx.find? fv = some decl := by
  induction trace with
  | freshParameter stats context i nindices fuel name domain body view
      binderInfo isParameter firstFamily whnf tail ih =>
      exact ih (localRun.push name binderInfo
        (AddInductive.consumeTypeAnnotations domain))
        (localRun.push_findOld name binderInfo
          (AddInductive.consumeTypeAnnotations domain) found)
  | sharedParameter stats context i nindices fuel name domain body
      parameterType view binderInfo isParameter laterFamily parameterTypeRun
      defeq whnf tail ih =>
      exact ih localRun found
  | index stats context i nindices fuel name domain body view binderInfo
      notParameter whnf tail ih =>
      exact ih (localRun.push name binderInfo
        (AddInductive.consumeTypeAnnotations domain))
        (localRun.push_findOld name binderInfo
          (AddInductive.consumeTypeAnnotations domain) found)
  | terminal => exact found

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
  simpa only [NameGenerator.curr, Name.getPrefix] using
    congrArg Name.getPrefix h

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

/-- Casting the implementation context index does not change the retained
verified `VContext`. -/
theorem CandidateContextRun.cast_context_context
    {left right : AddInductive.Context}
    (h : left = right) (run : CandidateContextRun left) :
    (h ▸ run).context = run.context := by
  cases h
  rfl

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
  · simp [context, VContext.mk', VContext.mk1, MLCtx.lctx,
      AddInductive.Context.toTypeChecker, lctx_eq]
  · exact VState.WF.empty

@[simp] theorem CandidateContextRun.context_env
    (run : CandidateContextRun candidateContext) :
    run.context.env = candidateContext.env := by
  have h := congrArg (fun c : TypeChecker.Context => c.env) run.context_eq
  simpa only [AddInductive.Context.toTypeChecker] using h

@[simp] theorem CandidateContextRun.context_lctx
    (run : CandidateContextRun candidateContext) :
    run.context.lctx = candidateContext.lctx := by
  have h := congrArg (fun c : TypeChecker.Context => c.lctx) run.context_eq
  simpa only [AddInductive.Context.toTypeChecker] using h

@[simp] theorem CandidateContextRun.context_safety
    (run : CandidateContextRun candidateContext) :
    run.context.safety = candidateContext.safety := by
  have h := congrArg (fun c : TypeChecker.Context => c.safety) run.context_eq
  simpa only [AddInductive.Context.toTypeChecker] using h

@[simp] theorem CandidateContextRun.context_lparams
    (run : CandidateContextRun candidateContext) :
    run.context.lparams = candidateContext.lparams := by
  have h := congrArg (fun c : TypeChecker.Context => c.lparams) run.context_eq
  simpa only [AddInductive.Context.toTypeChecker] using h

@[simp] theorem CandidateContextRun.context_fuel
    (run : CandidateContextRun candidateContext) :
    run.context.fuel = candidateContext.fuel := by
  have h := congrArg (fun c : TypeChecker.Context => c.fuel) run.context_eq
  simpa only [AddInductive.Context.toTypeChecker] using h

/-- Reuse a strict translation established at the empty producer root in any
verified candidate context with the same Theory environment and level
parameters.

Candidate validation contexts contain only free-variable declarations.  The
translated root is well typed, hence closed, so free-variable weakening leaves
its Theory syntax definitionally unchanged. -/
theorem CandidateContextRun.rootTranslation
    (run : CandidateContextRun candidateContext)
    (venv_eq : run.context.venv = env)
    (lparams_eq : run.context.lparams = Us)
    (source_tr : TrExprS env Us [] source source') :
    run.context.TrExprS source source' := by
  have henv : VEnv.WF env := by
    simpa only [venv_eq] using run.context.Ewf
  have sourceClosed : source'.Closed :=
    (source_tr.wf henv.ordered (by trivial)).closedN henv.ordered
      (by trivial)
  have targetWF : run.context.vlctx.WF env Us.length := by
    simpa only [venv_eq, lparams_eq] using run.context.Δwf
  have lifted := source_tr.weakFV henv.ordered
    (.from_nil run.context.mlctx.noBV) targetWF
  rw [sourceClosed.liftN_eq (Nat.zero_le _)] at lifted
  simpa only [VContext.TrExprS, venv_eq, lparams_eq] using lifted

/-- Translate the exact type returned by `AddInductive.getType` for a known
candidate-local declaration.

The explicit lookup premise is essential: `LocalContext.get!` has an
inhabited fallback, so a successful `getType` equation alone does not prove
that the requested free variable belongs to the local context.  Once the
lookup is owned by the producer, `TrLCtx.find?_of_mem` supplies both the
corresponding Theory lookup and a strict translation of its stored type. -/
theorem CandidateContextRun.getTypeTranslation
    (run : CandidateContextRun candidateContext)
    (hfind : candidateContext.lctx.find? fv = some decl)
    (hget : AddInductive.getType (.fvar fv) candidateContext =
      .ok parameterType) :
    ∃ value' parameterType',
      run.context.vlctx.find? (.inr fv) =
        some (value', parameterType') ∧
      run.context.TrExprS parameterType parameterType' := by
  have hfind' : run.context.lctx.find? fv = some decl := by
    simpa only [run.context_lctx] using hfind
  have hfindML : run.context.mlctx.lctx.find? fv = some decl := by
    rw [run.context.lctx_eq]
    exact hfind'
  have hfindList : run.context.mlctx.lctx.toList.find?
      (fv == ·.fvarId) = some decl := by
    rw [← run.context.trlctx.1.find?_eq_find?_toList]
    exact hfindML
  have fvEq : fv = decl.fvarId := by
    simpa using List.find?_some hfindList
  obtain ⟨value', parameterType', valueFind, _, _, _, typeTr⟩ :=
    run.context.trlctx.find?_of_mem run.context.Ewf
      (List.mem_of_find?_eq_some hfindList)
  have parameterTypeEq : decl.type = parameterType := by
    unfold AddInductive.getType at hget
    simp only [AddInductive.getLCtx_apply, ReaderT.bind, Bind.bind,
      ReaderT.pure, Pure.pure, Except.bind, Except.pure] at hget
    change Except.ok ((candidateContext.lctx.get! fv).type) =
      Except.ok parameterType at hget
    simpa [LocalContext.get!, hfind] using Except.ok.inj hget
  subst parameterType
  exact ⟨value', parameterType', by simpa only [fvEq] using valueFind,
    typeTr⟩

/-- Every shared parameter expression is a free variable whose declaration
is still present in the current validation context. -/
structure FamilyParameterLocalState
    (stats : AddInductive.InductiveStats)
    (context : AddInductive.Context) : Prop where
  localContext : CandidateLocalContextRun context
  parameters : ∀ {parameter : Expr}, parameter ∈ stats.params.toList →
    ∃ fv decl, parameter = .fvar fv ∧
      context.lctx.find? fv = some decl

namespace FamilyParameterLocalState

theorem empty (context : AddInductive.Context) (levels : List Level)
    (h : context.lctx = ({} : LocalContext)) :
    FamilyParameterLocalState
      (AddInductive.InductiveStats.initial levels) context where
  localContext := CandidateLocalContextRun.empty context h
  parameters := by simp [AddInductive.InductiveStats.initial]

theorem pushLocal (run : FamilyParameterLocalState stats context)
    (name : Name) (binderInfo : BinderInfo) (type : Expr) :
    FamilyParameterLocalState stats
      (context.pushLocalDecl name binderInfo type) where
  localContext := run.localContext.push name binderInfo type
  parameters := by
    intro parameter member
    obtain ⟨fv, decl, rfl, hfind⟩ := run.parameters member
    exact ⟨fv, decl, rfl,
      run.localContext.push_findOld name binderInfo type hfind⟩

theorem pushParameter (run : FamilyParameterLocalState stats context)
    (name : Name) (binderInfo : BinderInfo) (type : Expr) :
    FamilyParameterLocalState
      { stats with params := stats.params.push context.freshExpr }
      (context.pushLocalDecl name binderInfo type) where
  localContext := run.localContext.push name binderInfo type
  parameters := by
    intro parameter member
    simp only [Array.toList_push, List.mem_append, List.mem_singleton] at member
    rcases member with member | rfl
    · obtain ⟨fv, decl, rfl, hfind⟩ := run.parameters member
      exact ⟨fv, decl, rfl,
        run.localContext.push_findOld name binderInfo type hfind⟩
    · exact ⟨context.freshFVarId,
        .cdecl context.lctx.decls.size context.freshFVarId
          name type binderInfo .default,
        rfl, run.localContext.push_findNew name binderInfo type⟩

end FamilyParameterLocalState

/-- A retained comparison RHS was read from a genuine local parameter. -/
def FamilyComparisonRhsLocal
    (step : AddInductive.CandidateIsDefEqStep) : Prop :=
  ∃ fv decl, step.context.lctx.find? fv = some decl ∧
    AddInductive.getType (.fvar fv) step.context = .ok step.rhs

/-- Recover the strict Theory translation of a comparison RHS from its
producer-owned local declaration. -/
theorem FamilyComparisonRhsLocal.translation
    (rhsLocal : FamilyComparisonRhsLocal step)
    (contextRun : CandidateContextRun step.context) :
    ∃ rhs', contextRun.context.TrExprS step.rhs rhs' := by
  obtain ⟨fv, decl, hfind, hget⟩ := rhsLocal
  obtain ⟨_, rhs', _, rhsTr⟩ :=
    contextRun.getTypeTranslation hfind hget
  exact ⟨rhs', rhsTr⟩

/-- Interpret one retained family-parameter comparison once the current
family domain has been translated.  The RHS translation is recovered from
the validator's local inventory rather than supplied independently. -/
theorem FamilyComparisonRhsLocal.isDefEqRun
    (rhsLocal : FamilyComparisonRhsLocal step)
    (valid : step.Valid)
    (contextRun : CandidateContextRun step.context)
    (lhs' : VExpr)
    (lhsTr : contextRun.context.TrExprS step.lhs lhs') :
    ∃ rhs', Nonempty
      (IsDefEqRun contextRun.context.venv contextRun.context.lparams
        contextRun.context.vlctx step.lhs step.rhs lhs' rhs') := by
  obtain ⟨rhs', rhsTr⟩ := rhsLocal.translation contextRun
  exact ⟨rhs', ⟨IsDefEqRun.ofCandidateStep step valid
    contextRun.context contextRun.context_eq rfl rfl rfl
    contextRun.state_wf lhsTr rhsTr step.context.fuel.recDepth rfl⟩⟩

/-- Complete semantic ownership of one retained family-parameter comparison.

The verified context and both Theory endpoints are selected by the exact
validator execution.  In particular, the LHS is not supplied independently
after the comparison has been interpreted. -/
def FamilyComparisonSemanticRun
    (step : AddInductive.CandidateIsDefEqStep) : Prop :=
  ∃ (contextRun : CandidateContextRun step.context) (lhs' rhs' : VExpr),
    Nonempty
      (IsDefEqRun contextRun.context.venv contextRun.context.lparams
        contextRun.context.vlctx step.lhs step.rhs lhs' rhs')

/-- Package one retained WHNF observation and keep the strict Theory
translation selected for its exact kernel result. -/
theorem WhnfRun.exists_ofCandidateStep
    (step : AddInductive.CandidateWhnfStep)
    (hvalid : step.Valid)
    (contextRun : CandidateContextRun step.context)
    (source' : VExpr)
    (source_tr : contextRun.context.TrExprS step.source source')
    (recursionFuel : Nat)
    (hdepth : step.context.fuel.recDepth = recursionFuel + 1) :
    ∃ result', contextRun.context.TrExprS step.result result' ∧
      Nonempty (WhnfRun contextRun.context.venv
        contextRun.context.lparams contextRun.context.vlctx
        step.source step.result source' result') := by
  obtain ⟨state, run⟩ := step.innerRun recursionFuel hdepth hvalid
  rw [← contextRun.context_eq] at run
  obtain ⟨_, _, _, _, _, resultTranslation⟩ :=
    (Inner.whnf'.WF source_tr
      (Methods.withFuel recursionFuel) Methods.withFuel.WF)
      contextRun.state_wf step.result state run
  obtain ⟨result', result_tr, _⟩ := resultTranslation
  exact ⟨result', result_tr, ⟨WhnfRun.ofCandidateStep step hvalid
    contextRun.context contextRun.context_eq rfl rfl rfl
    contextRun.state_wf source_tr result_tr
    recursionFuel hdepth⟩⟩

/-- A producer-owned dependent argument spine through the validator's exact
Theory WHNF cursors.

Each argument is typed at the raw domain exposed by the current translated
Pi.  The instantiated body is related to the next cursor by the retained
WHNF execution, rather than by a syntactic equality invented downstream. -/
inductive FamilyParameterSemanticSpine (env : VEnv) (U : Nat)
    (Γ : List VExpr) : VExpr → List VExpr → VExpr → Prop where
  | nil (source : VExpr) :
      FamilyParameterSemanticSpine env U Γ source [] source
  | cons
      (argument_type : env.HasType U Γ argument domain)
      (step : env.IsDefEqU U Γ (body.inst argument) next)
      (tail : FamilyParameterSemanticSpine env U Γ next arguments result) :
      FamilyParameterSemanticSpine env U Γ (.forallE domain body)
        (argument :: arguments) result

/-- Saturating a raw telescope along the operational parameter spine reaches
the validator's retained boundary up to definitional equality.

Pi injectivity is used only to retarget each producer-owned argument from the
validator cursor to the corresponding raw telescope domain.  Successive
cursors themselves remain connected by the exact WHNF equalities stored in
the spine. -/
theorem FamilyParameterSemanticSpine.rawTerminal_defeq
    (spine : FamilyParameterSemanticSpine env U Γ root arguments result)
    (henv : VEnv.WF env)
    (hΓ : OnCtx Γ (env.IsType U))
    (root_def : env.IsDefEqU U Γ
      (VExpr.forallN rawBinders rawTerminal) root)
    (length_eq : arguments.length = rawBinders.length) :
    env.IsDefEqU U Γ (VExpr.instRev rawTerminal arguments) result := by
  induction spine generalizing rawBinders rawTerminal with
  | nil source =>
      have rawBinders_eq : rawBinders = [] :=
        List.length_eq_zero_iff.mp length_eq.symm
      subst rawBinders
      simpa only [VExpr.forallN, VExpr.instRev] using root_def
  | @cons argument domain next arguments result body argumentType step tail ih =>
      cases rawBinders with
      | nil => simp at length_eq
      | cons rawDomain rawBinders =>
          simp only [VExpr.forallN] at root_def
          obtain ⟨⟨_, domain_def⟩, ⟨_, body_def⟩⟩ :=
            VEnv.IsDefEqU.forallE_inv henv hΓ root_def
          have argumentRaw : env.HasType U Γ argument rawDomain :=
            domain_def.symm.defeq argumentType
          have bodyInst := body_def.instN henv argumentRaw .zero
          have next_def : env.IsDefEqU U Γ
              ((VExpr.forallN rawBinders rawTerminal).inst argument) next :=
            VEnv.IsDefEqU.trans henv hΓ ⟨_, bodyInst⟩ step
          have remainingLength : arguments.length = rawBinders.length := by
            simpa using length_eq
          rw [VExpr.instN_forallN, Nat.zero_add] at next_def
          have tail_def := ih next_def (by
            rw [VExpr.instTelN_length]
            exact remainingLength)
          simpa only [VExpr.instRev, remainingLength, Nat.add_zero] using
            tail_def

/-- Specialize an equality living under the raw parameter telescope along
the validator's exact operational argument spine.

Unlike a syntactic `SpineWF` replay, the induction follows every retained
WHNF cursor.  The terminal equality is instantiated only after Pi
injectivity has retargeted the current producer-owned argument to the exact
raw binder domain. -/
theorem FamilyParameterSemanticSpine.specializeTerminalDefEq
    (spine : FamilyParameterSemanticSpine env U Γ root arguments result)
    (henv : VEnv.WF env)
    (hΓ : OnCtx Γ (env.IsType U))
    (root_def : env.IsDefEqU U Γ
      (VExpr.forallN rawBinders rawResult) root)
    (length_eq : arguments.length = rawBinders.length)
    (terminal_def : env.IsDefEq U (rawBinders.reverse ++ Γ)
      rawTerminal storedTerminal terminalType) :
    env.IsDefEq U Γ
      (VExpr.instRev rawTerminal arguments)
      (VExpr.instRev storedTerminal arguments)
      (VExpr.instRev terminalType arguments) := by
  induction spine generalizing rawBinders rawResult rawTerminal
      storedTerminal terminalType with
  | nil source =>
      have rawBinders_eq : rawBinders = [] :=
        List.length_eq_zero_iff.mp length_eq.symm
      subst rawBinders
      simpa only [List.reverse_nil, List.nil_append, VExpr.instRev] using
        terminal_def
  | @cons argument domain next arguments result body argumentType step tail ih =>
      cases rawBinders with
      | nil => simp at length_eq
      | cons rawDomain rawBinders =>
          simp only [VExpr.forallN] at root_def
          obtain ⟨⟨_, domain_def⟩, ⟨_, body_def⟩⟩ :=
            VEnv.IsDefEqU.forallE_inv henv hΓ root_def
          have argumentRaw : env.HasType U Γ argument rawDomain :=
            domain_def.symm.defeq argumentType
          have bodyInst := body_def.instN henv argumentRaw .zero
          have next_def : env.IsDefEqU U Γ
              ((VExpr.forallN rawBinders rawResult).inst argument) next :=
            VEnv.IsDefEqU.trans henv hΓ ⟨_, bodyInst⟩ step
          have remainingLength : arguments.length = rawBinders.length := by
            simpa using length_eq
          have terminal_def' : env.IsDefEq U
              (rawBinders.reverse ++ rawDomain :: Γ)
              rawTerminal storedTerminal terminalType := by
            simpa only [List.reverse_cons, List.singleton_append,
              List.append_assoc] using terminal_def
          let substitution := Ctx.InstN.consTel
            (Γ₀ := Γ) (e₀ := argument) (A₀ := rawDomain)
            rawBinders .zero
          have instantiatedTerminal :=
            terminal_def'.instN henv argumentRaw substitution
          rw [VExpr.instN_forallN, Nat.zero_add] at next_def
          have tail_def := ih next_def (by
            rw [VExpr.instTelN_length]
            exact remainingLength) instantiatedTerminal
          simpa only [VExpr.instRev, remainingLength, Nat.add_zero] using
            tail_def

/-- Transparent structural equality with a Pi exposes a genuine Pi source.
This small shape lemma lets retained WHNF observations be compared across
reader contexts without treating `Expr.structuralEq` as propositional
equality. -/
theorem _root_.Lean4Lean.AddInductive.CandidateWhnfStep.isForall_of_structuralEq_forall
    {source : Expr}
    (h : Expr.structuralEq source
      (.forallE name domain body binderInfo) = true) :
    source.isForall = true := by
  have eqv := Expr.structuralEq_eqv h
  simp only [(· == ·), Expr.eqv_eq] at eqv
  cases source <;> simp_all [Expr.isForall, Expr.eqv']

/-- A successful retained WHNF observation of a syntactic Pi returns that Pi
literally.  The proof evaluates the checker at the producer-owned positive
recursion depth, so it is independent of the local reader context. -/
theorem _root_.Lean4Lean.AddInductive.CandidateWhnfStep.result_eq_of_source_isForall
    {context : AddInductive.Context} {source result : Expr}
    (run : AddInductive.CandidateWhnfStep.Valid ⟨context, source, result⟩)
    (recursionFuel : Nat)
    (hdepth : context.fuel.recDepth = recursionFuel + 1)
    (isForall : source.isForall = true) :
    result = source := by
  have selfRun : AddInductive.CandidateWhnfStep.Valid
      ⟨context, source, source⟩ := by
    cases source <;> simp_all [Expr.isForall]
    unfold AddInductive.CandidateWhnfStep.Valid TypeChecker.M.run
      TypeChecker.whnf TypeChecker.RecM.run
    simp [readThe, MonadReaderOf.read, ReaderT.read,
      ReaderT.bind, StateT.bind, Except.bind, Bind.bind,
      StateT.pure, Except.pure, Pure.pure,
      StateT.run', Functor.map, Except.map]
    rw [hdepth]
    rfl
  exact Except.ok.inj (run.symm.trans selfRun)

/-- Exact shared-parameter path from a later-family telescope to its retained
`i = nparams` suffix.

Unlike a counter or result equality, this proof records every actual
`sharedParameter` constructor and therefore preserves the kernel source path
needed to align candidate annotations with validator index nodes. -/
inductive _root_.Lean4Lean.AddInductive.FamilyTypeParameterComparisonTrace.SharedPrefixPath
    (nparams : Nat) :
    {stats : AddInductive.InductiveStats} →
      {context : AddInductive.Context} → {source : Expr} →
      {i nindices fuel : Nat} →
      (outer : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
        context source i nindices fuel) →
      {suffixSource : Expr} → {suffixFuel : Nat} →
      (suffix : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
        context suffixSource nparams nindices suffixFuel) →
      List Expr → Prop where
  | done
      (trace : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
        context source nparams nindices fuel) :
      SharedPrefixPath nparams trace trace []
  | shared
      (tail : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
        context view (i + 1) nindices fuel)
      (suffix : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
        context suffixSource nparams nindices suffixFuel)
      (parameters : List Expr)
      (isParameter : i < nparams)
      (laterFamily : stats.indConsts.isEmpty = false)
      (parameterTypeRun : AddInductive.getType stats.params[i]! context =
        .ok parameterType)
      (defeq : AddInductive.CandidateIsDefEqStep.Valid
        ⟨context, domain, parameterType⟩)
      (whnf : AddInductive.CandidateWhnfStep.Valid
        ⟨context, body.instantiate1 stats.params[i]!, view⟩)
      (path : SharedPrefixPath nparams tail suffix parameters) :
      SharedPrefixPath nparams
        (.sharedParameter stats context i nindices fuel name domain body
          parameterType view binderInfo isParameter laterFamily
          parameterTypeRun defeq whnf tail)
        suffix (stats.params[i]! :: parameters)

/-- Exact index-only suffix reached after interpreting a later family's
shared-parameter prefix.

The boundary retains the producer's original trace object, terminal-result
identity, and strict translation at the unchanged validator context.  In
particular, a consumer cannot select another source expression or reconstruct
an index suffix from a comparison count. -/
structure FamilyParameterIndexBoundary
    (outer : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
      context source i nindices fuel)
    (contextRun : CandidateContextRun context) where
  source : Expr
  fuel : Nat
  trace : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
    context source nparams nindices fuel
  source' : VExpr
  source_tr : contextRun.context.TrExprS source source'
  parameters : List (Expr × VExpr)
  parameter_tr : ∀ parameter ∈ parameters,
    contextRun.context.TrExprS parameter.1 parameter.2
  parameters_length : parameters.length = nparams - i
  params_size : stats.params.size = nparams
  parameter_sources_eq : parameters.map Prod.fst =
    stats.params.toList.drop i
  prefix_path :
    AddInductive.FamilyTypeParameterComparisonTrace.SharedPrefixPath nparams
      outer trace (parameters.map Prod.fst)
  localState : FamilyParameterLocalState stats context
  result_eq : trace.result = outer.result
  comparisons_eq_nil : trace.comparisons = []

/-- Interpret a later family's exact shared-parameter prefix and expose the
retained suffix at the first index position.

Besides the semantic run for every comparison, this strengthens the former
comparison-only result with the exact translated source from which index
context ownership must continue.  Shared parameters do not alter the reader
context, statistics, or index count, so the boundary remains indexed by all
three original values. -/
theorem familyTypeParameterComparison_semanticSpine_of_later
    (trace : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
      context source i nindices fuel)
    (later : stats.indConsts.isEmpty = false)
    (paramsSize : stats.params.size = nparams)
    (localState : FamilyParameterLocalState stats context)
    (contextRun : CandidateContextRun context)
    (source' : VExpr)
    (source_tr : contextRun.context.TrExprS source source')
    (whnfFuel : Nat)
    (whnfDepth : context.fuel.recDepth = whnfFuel + 1) :
    (∀ step ∈ trace.comparisons, FamilyComparisonSemanticRun step) ∧
      ∃ boundary : FamilyParameterIndexBoundary trace contextRun,
        FamilyParameterSemanticSpine contextRun.context.venv
          contextRun.context.lparams.length contextRun.context.vlctx.toCtx
          source' (boundary.parameters.map Prod.snd) boundary.source' := by
  induction trace generalizing source' with
  | freshParameter stats context i nindices fuel name domain body view
      binderInfo isParameter firstFamily whnf tail ih =>
      rw [later] at firstFamily
      contradiction
  | sharedParameter stats context i nindices fuel name domain body
      parameterType view binderInfo isParameter laterFamily parameterTypeRun
      defeq whnf tail ih =>
      let @TrExprS.forallE _ _ domain' body' _ _ _ _ _
          domainType bodyType domain_tr body_tr := source_tr
      have parameterMember : stats.params[i]! ∈ stats.params.toList := by
        rw [show stats.params[i]! = stats.params[i] by
          simp [isParameter, paramsSize]]
        exact List.getElem_mem (by
          simpa only [Array.length_toList, paramsSize] using isParameter)
      obtain ⟨fv, decl, parameterEq, parameterFind⟩ :=
        localState.parameters parameterMember
      have parameterTypeRun' : AddInductive.getType (.fvar fv) context =
          .ok parameterType := by
        rw [← parameterEq]
        exact parameterTypeRun
      obtain ⟨fvValue, parameterType', fvFind, parameterType_tr⟩ :=
        contextRun.getTypeTranslation parameterFind parameterTypeRun'
      have fv_tr : contextRun.context.TrExprS (.fvar fv) fvValue :=
        .fvar fvFind
      let comparisonRun : IsDefEqRun contextRun.context.venv
          contextRun.context.lparams contextRun.context.vlctx domain
          parameterType _ _ :=
        IsDefEqRun.ofCandidateStep ⟨context, domain, parameterType⟩ defeq
          contextRun.context contextRun.context_eq rfl rfl rfl
          contextRun.state_wf domain_tr parameterType_tr
          context.fuel.recDepth rfl
      have henv : VEnv.WF contextRun.context.venv := contextRun.context.Ewf
      have hctx : OnCtx contextRun.context.vlctx.toCtx
          (contextRun.context.venv.IsType
            contextRun.context.lparams.length) :=
        contextRun.context.Δwf.toCtx
      obtain ⟨u, domainHasType⟩ := domainType
      have domainDef : contextRun.context.venv.IsDefEq
          contextRun.context.lparams.length contextRun.context.vlctx.toCtx
          _ _ (.sort u) :=
        comparisonRun.isDefEqU.of_l henv hctx domainHasType
      have fvHasParameterType : contextRun.context.venv.HasType
          contextRun.context.lparams.length contextRun.context.vlctx.toCtx
          fvValue parameterType' :=
        contextRun.context.Δwf.find?_wf contextRun.context.Ewf.ordered fvFind
      have fvHasDomain : contextRun.context.venv.HasType
          contextRun.context.lparams.length contextRun.context.vlctx.toCtx
          fvValue _ :=
        domainDef.symm.defeq fvHasParameterType
      have bodyInst_tr : contextRun.context.TrExprS
          (body.instantiate1 (.fvar fv)) (body'.inst fvValue) := by
        simpa only [Expr.instantiate1_eq] using
          body_tr.inst contextRun.context.Ewf.ordered fvHasDomain fv_tr
      have bodyInst_tr' : contextRun.context.TrExprS
          (body.instantiate1 stats.params[i]!) (body'.inst fvValue) := by
        rw [parameterEq]
        exact bodyInst_tr
      obtain ⟨view', view_tr, ⟨viewRun⟩⟩ :=
        WhnfRun.exists_ofCandidateStep ⟨context,
          body.instantiate1 stats.params[i]!, view⟩ whnf contextRun
          (body'.inst fvValue) bodyInst_tr' whnfFuel whnfDepth
      obtain ⟨tailRuns, boundary, parameterSpine⟩ :=
        ih later paramsSize localState contextRun view' view_tr whnfDepth
      constructor
      · intro step member
        simp only [
          AddInductive.FamilyTypeParameterComparisonTrace.comparisons,
          List.mem_cons] at member
        rcases member with rfl | member
        · exact ⟨contextRun, _, _, ⟨comparisonRun⟩⟩
        · exact tailRuns step member
      · refine ⟨{
          source := boundary.source
          fuel := boundary.fuel
          trace := boundary.trace
          source' := boundary.source'
          source_tr := boundary.source_tr
          parameters :=
            (stats.params[i]!, fvValue) :: boundary.parameters
          parameter_tr := by
            intro parameter member
            simp only [List.mem_cons] at member
            rcases member with rfl | member
            · rw [parameterEq]
              exact fv_tr
            · exact boundary.parameter_tr parameter member
          parameters_length := by
            simp only [List.length_cons, boundary.parameters_length]
            omega
          params_size := paramsSize
          parameter_sources_eq := by
            simp only [List.map_cons, boundary.parameter_sources_eq]
            have indexBound : i < stats.params.size := by
              simpa only [paramsSize] using isParameter
            have listIndexBound : i < stats.params.toList.length := by
              simpa using indexBound
            rw [List.drop_eq_getElem_cons listIndexBound]
            congr 1
            simp [indexBound]
          prefix_path := .shared tail boundary.trace
            (boundary.parameters.map Prod.fst) isParameter laterFamily
              parameterTypeRun defeq whnf boundary.prefix_path
          localState := boundary.localState
          result_eq := by
            simpa only [
              AddInductive.FamilyTypeParameterComparisonTrace.result] using
              boundary.result_eq
          comparisons_eq_nil := boundary.comparisons_eq_nil }, ?_⟩
        simp only [List.map_cons]
        exact .cons fvHasDomain viewRun.isDefEqU parameterSpine
  | index stats context i nindices fuel name domain body view binderInfo
      notParameter whnf tail ih =>
      have i_le : i ≤ nparams :=
        (AddInductive.FamilyTypeParameterComparisonTrace.index stats context
          i nindices fuel name domain body view binderInfo notParameter whnf
          tail).startIndex_le_nparams
      have nparams_le : nparams ≤ i := Nat.le_of_not_gt notParameter
      have i_eq : i = nparams := Nat.le_antisymm i_le nparams_le
      subst i
      let current :=
        AddInductive.FamilyTypeParameterComparisonTrace.index stats context
          nparams nindices fuel name domain body view binderInfo notParameter
          whnf tail
      have currentLength : current.comparisons.length = 0 := by
        simpa only [current, Nat.sub_self] using
          current.comparisons_length_of_laterFamily later
      have currentEmpty : current.comparisons = [] := by
        cases hcomparisons : current.comparisons with
        | nil => rfl
        | cons head tail =>
          rw [hcomparisons] at currentLength
          simp at currentLength
      constructor
      · intro step member
        rw [currentEmpty] at member
        simp at member
      · refine ⟨{
          source := .forallE name domain body binderInfo
          fuel := fuel + 1
          trace := current
          source' := source'
          source_tr := source_tr
          parameters := []
          parameter_tr := by
            intro parameter member
            simp at member
          parameters_length := by simp
          params_size := paramsSize
          parameter_sources_eq := by
            simp only [List.map_nil]
            symm
            apply List.drop_of_length_le
            simpa using Nat.le_of_eq paramsSize
          prefix_path := .done current
          localState := localState
          result_eq := rfl
          comparisons_eq_nil := currentEmpty }, ?_⟩
        simp only [List.map_nil]
        exact .nil source'
  | terminal stats context source i nindices fuel notForall
      parametersComplete =>
      subst i
      let current :=
        AddInductive.FamilyTypeParameterComparisonTrace.terminal stats
          context source nparams nindices fuel notForall rfl
      constructor
      · intro step member
        simp only [
          AddInductive.FamilyTypeParameterComparisonTrace.comparisons,
          List.not_mem_nil] at member
      · refine ⟨{
          source := source
          fuel := fuel + 1
          trace := current
          source' := source'
          source_tr := source_tr
          parameters := []
          parameter_tr := by
            intro parameter member
            simp at member
          parameters_length := by simp
          params_size := paramsSize
          parameter_sources_eq := by
            simp only [List.map_nil]
            symm
            apply List.drop_of_length_le
            simpa using Nat.le_of_eq paramsSize
          prefix_path := .done current
          localState := localState
          result_eq := rfl
          comparisons_eq_nil := rfl }, ?_⟩
        simp only [List.map_nil]
        exact .nil source'

/-- Compatibility projection of the operational semantic spine to the
source-indexed boundary used by existing consumers. -/
theorem familyTypeParameterComparison_semanticPrefix_of_later
    (trace : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
      context source i nindices fuel)
    (later : stats.indConsts.isEmpty = false)
    (paramsSize : stats.params.size = nparams)
    (localState : FamilyParameterLocalState stats context)
    (contextRun : CandidateContextRun context)
    (source' : VExpr)
    (source_tr : contextRun.context.TrExprS source source')
    (whnfFuel : Nat)
    (whnfDepth : context.fuel.recDepth = whnfFuel + 1) :
    (∀ step ∈ trace.comparisons, FamilyComparisonSemanticRun step) ∧
      Nonempty (FamilyParameterIndexBoundary trace contextRun) := by
  obtain ⟨runs, boundary, _⟩ :=
    familyTypeParameterComparison_semanticSpine_of_later trace later
      paramsSize localState contextRun source' source_tr whnfFuel whnfDepth
  exact ⟨runs, ⟨boundary⟩⟩

/-- Interpret every shared-parameter comparison in one later-family
telescope from the strict translation of its exact validator root.

At a shared parameter, the producer-owned local lookup translates both the
stored parameter type and the free variable used to instantiate the remaining
family body.  The retained equality execution then retargets that free
variable to the current raw domain, so the exact retained WHNF step supplies
the next source translation.  Once the parameter boundary is reached, the
comparison list is empty and ordinary index binders require no interpretation
here. -/
theorem familyTypeParameterComparison_semanticRuns_of_later
    (trace : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
      context source i nindices fuel)
    (later : stats.indConsts.isEmpty = false)
    (paramsSize : stats.params.size = nparams)
    (localState : FamilyParameterLocalState stats context)
    (contextRun : CandidateContextRun context)
    (source' : VExpr)
    (source_tr : contextRun.context.TrExprS source source')
    (whnfFuel : Nat)
    (whnfDepth : context.fuel.recDepth = whnfFuel + 1) :
    ∀ step ∈ trace.comparisons, FamilyComparisonSemanticRun step := by
  exact (familyTypeParameterComparison_semanticPrefix_of_later trace later
    paramsSize localState contextRun source' source_tr whnfFuel whnfDepth).1

private def FamilyParameterCountInvariant (nparams i : Nat)
    (stats : AddInductive.InductiveStats) : Prop :=
  i ≤ nparams ∧
    if stats.indConsts.isEmpty then
      stats.params.size + (nparams - i) = nparams
    else
      stats.params.size = nparams

/-- Interpret the local-parameter inventory through one exact family
telescope.  Besides preserving every real lookup, this proves that each
exposed comparison RHS came from its retained `getType` read. -/
private theorem familyTypeParameterComparison_localResult
    (trace : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
      context source i nindices fuel)
    (localState : FamilyParameterLocalState stats context)
    (count : FamilyParameterCountInvariant nparams i stats) :
    FamilyParameterLocalState trace.result.stats trace.result.context ∧
      trace.result.stats.params.size = nparams ∧
      ∀ step ∈ trace.comparisons, FamilyComparisonRhsLocal step := by
  induction trace with
  | freshParameter stats context i nindices fuel name domain body view
      binderInfo isParameter firstFamily whnf tail ih =>
      let nextLocal := localState.pushParameter name binderInfo
        (AddInductive.consumeTypeAnnotations domain)
      have nextCount : FamilyParameterCountInvariant nparams (i + 1)
          { stats with params := stats.params.push context.freshExpr } := by
        unfold FamilyParameterCountInvariant at count ⊢
        simp only [firstFamily, if_true, Array.size_push] at count ⊢
        omega
      simpa only [AddInductive.FamilyTypeParameterComparisonTrace.result,
        AddInductive.FamilyTypeParameterComparisonTrace.comparisons] using
        ih nextLocal nextCount
  | sharedParameter stats context i nindices fuel name domain body
      parameterType view binderInfo isParameter laterFamily parameterTypeRun
      defeq whnf tail ih =>
      have paramsSize : stats.params.size = nparams := by
        unfold FamilyParameterCountInvariant at count
        simpa only [laterFamily, Bool.false_eq_true, if_false] using count.2
      have parameterMember : stats.params[i]! ∈ stats.params.toList := by
        rw [show stats.params[i]! = stats.params[i] by simp [isParameter,
          paramsSize]]
        exact List.getElem_mem (by simpa only [Array.length_toList,
          paramsSize] using isParameter)
      obtain ⟨fv, decl, parameterEq, parameterFind⟩ :=
        localState.parameters parameterMember
      have parameterTypeRun' : AddInductive.getType (.fvar fv) context =
          .ok parameterType := by
        rw [← parameterEq]
        exact parameterTypeRun
      have nextCount : FamilyParameterCountInvariant nparams (i + 1)
          stats := by
        unfold FamilyParameterCountInvariant at count ⊢
        simp only [laterFamily, Bool.false_eq_true, if_false] at count ⊢
        exact ⟨by omega, count.2⟩
      obtain ⟨terminalLocal, terminalSize, comparisons⟩ :=
        ih localState nextCount
      refine ⟨terminalLocal, terminalSize, ?_⟩
      intro step member
      simp only [AddInductive.FamilyTypeParameterComparisonTrace.comparisons,
        List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨fv, decl, parameterFind, parameterTypeRun'⟩
      · exact comparisons step member
  | index stats context i nindices fuel name domain body view binderInfo
      notParameter whnf tail ih =>
      let nextLocal := localState.pushLocal name binderInfo
        (AddInductive.consumeTypeAnnotations domain)
      simpa only [AddInductive.FamilyTypeParameterComparisonTrace.result,
        AddInductive.FamilyTypeParameterComparisonTrace.comparisons] using
        ih nextLocal count
  | terminal stats context source i nindices fuel notForall
      parametersComplete =>
      have paramsSize : stats.params.size = nparams := by
        unfold FamilyParameterCountInvariant at count
        subst i
        split at count <;> omega
      exact ⟨localState, paramsSize, by
        intro step member
        simp only [AddInductive.FamilyTypeParameterComparisonTrace.comparisons,
          List.not_mem_nil] at member⟩

/-- Thread the producer-owned local inventory through a first-family
telescope that starts before any shared parameter has been allocated.

The result exposes exactly the two facts needed at the next source position:
all retained parameter free variables are still genuine local declarations,
and their array has reached the validator's complete `nparams` length. -/
theorem familyTypeParameterComparison_localResult_of_first
    (trace : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
      context source 0 nindices fuel)
    (first : stats.indConsts.isEmpty = true)
    (paramsEmpty : stats.params.size = 0)
    (localState : FamilyParameterLocalState stats context) :
    FamilyParameterLocalState trace.result.stats trace.result.context ∧
      trace.result.stats.params.size = nparams := by
  have result := familyTypeParameterComparison_localResult trace localState (by
    unfold FamilyParameterCountInvariant
    simp only [Nat.zero_le, first, if_true, paramsEmpty, Nat.zero_add,
      Nat.sub_zero, and_self])
  exact ⟨result.1, result.2.1⟩

/-- Thread the producer-owned local inventory through a later-family
telescope whose shared-parameter array is already complete.

Unlike the first-family specialization, no fresh parameter is allocated:
shared-parameter nodes preserve the inventory and index nodes extend only
the local context.  The result therefore owns the exact local state at the
family telescope's terminal reader context. -/
theorem familyTypeParameterComparison_localResult_of_later
    (trace : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
      context source 0 nindices fuel)
    (later : stats.indConsts.isEmpty = false)
    (paramsSize : stats.params.size = nparams)
    (localState : FamilyParameterLocalState stats context) :
    FamilyParameterLocalState trace.result.stats trace.result.context ∧
      trace.result.stats.params.size = nparams := by
  have result := familyTypeParameterComparison_localResult trace localState (by
    unfold FamilyParameterCountInvariant
    simp only [Nat.zero_le, later, Bool.false_eq_true, if_false, paramsSize,
      and_self])
  exact ⟨result.1, result.2.1⟩

private def FamilyBlockParameterLocalInvariant (nparams : Nat)
    (stats : AddInductive.InductiveStats)
    (context : AddInductive.Context) : Prop :=
  FamilyParameterLocalState stats context ∧
    if stats.indConsts.isEmpty then stats.params.size = 0
    else stats.params.size = nparams

/-- Thread the local-parameter inventory through the complete source-indexed
family block and attach a genuine local RHS to every retained comparison. -/
private theorem familyParameterComparisonBlock_comparisonRhsLocal
    (trace : AddInductive.FamilyParameterComparisonBlockTrace nparams
      indTypes dIdx stats context)
    (invariant : FamilyBlockParameterLocalInvariant nparams stats context) :
    ∀ familyComparisons ∈ trace.comparisons,
      ∀ step ∈ familyComparisons, FamilyComparisonRhsLocal step := by
  induction trace with
  | firstFamily dIdx stats context inBounds closed inferred root checkType
      rootWhnf telescope sorted ensureSort isFirst tail ih =>
      have statsFirst : stats.indConsts.isEmpty = true := by
        rw [telescope.result_indConsts_eq] at isFirst
        exact isFirst
      have paramsEmpty : stats.params.size = 0 := by
        simpa only [statsFirst, if_true] using invariant.2
      have count : FamilyParameterCountInvariant nparams 0 stats := by
        unfold FamilyParameterCountInvariant
        simp only [Nat.zero_le, statsFirst, if_true, paramsEmpty,
          Nat.zero_add, Nat.sub_zero, and_self]
      obtain ⟨resultLocal, resultSize, headLocal⟩ :=
        familyTypeParameterComparison_localResult telescope invariant.1 count
      have tailLocal : FamilyParameterLocalState
          { telescope.result.stats with
            lctx := telescope.result.context.lctx
            resultLevel := sorted.sortLevel!
            isNotZero := sorted.sortLevel!.isNeverZero
            nindices := telescope.result.stats.nindices.push
              telescope.result.nindices
            indConsts := telescope.result.stats.indConsts.push
              (.const indTypes[dIdx].name telescope.result.stats.levels) }
          telescope.result.context := by
        exact ⟨resultLocal.localContext, resultLocal.parameters⟩
      have tailInvariant : FamilyBlockParameterLocalInvariant nparams
          { telescope.result.stats with
            lctx := telescope.result.context.lctx
            resultLevel := sorted.sortLevel!
            isNotZero := sorted.sortLevel!.isNeverZero
            nindices := telescope.result.stats.nindices.push
              telescope.result.nindices
            indConsts := telescope.result.stats.indConsts.push
              (.const indTypes[dIdx].name telescope.result.stats.levels) }
          telescope.result.context := by
        refine ⟨tailLocal, ?_⟩
        simp only [Array.isEmpty_push, Bool.false_eq_true, if_false]
        exact resultSize
      have tailResult := ih tailInvariant
      intro familyComparisons familyMember step stepMember
      simp only [AddInductive.FamilyParameterComparisonBlockTrace.comparisons,
        List.mem_cons] at familyMember
      rcases familyMember with rfl | familyMember
      · exact headLocal step stepMember
      · exact tailResult familyComparisons familyMember step stepMember
  | laterFamily dIdx stats context inBounds closed inferred root checkType
      rootWhnf telescope sorted ensureSort isLater resultLevelCompatible tail
      ih =>
      have statsLater : stats.indConsts.isEmpty = false := by
        rw [telescope.result_indConsts_eq] at isLater
        exact isLater
      have paramsSize : stats.params.size = nparams := by
        simpa only [statsLater, Bool.false_eq_true, if_false] using invariant.2
      have count : FamilyParameterCountInvariant nparams 0 stats := by
        unfold FamilyParameterCountInvariant
        simp only [Nat.zero_le, statsLater, Bool.false_eq_true, if_false,
          paramsSize, and_self]
      obtain ⟨resultLocal, resultSize, headLocal⟩ :=
        familyTypeParameterComparison_localResult telescope invariant.1 count
      have tailLocal : FamilyParameterLocalState
          { telescope.result.stats with
            nindices := telescope.result.stats.nindices.push
              telescope.result.nindices
            indConsts := telescope.result.stats.indConsts.push
              (.const indTypes[dIdx].name telescope.result.stats.levels) }
          telescope.result.context := by
        exact ⟨resultLocal.localContext, resultLocal.parameters⟩
      have tailInvariant : FamilyBlockParameterLocalInvariant nparams
          { telescope.result.stats with
            nindices := telescope.result.stats.nindices.push
              telescope.result.nindices
            indConsts := telescope.result.stats.indConsts.push
              (.const indTypes[dIdx].name telescope.result.stats.levels) }
          telescope.result.context := by
        refine ⟨tailLocal, ?_⟩
        simp only [Array.isEmpty_push, Bool.false_eq_true, if_false]
        exact resultSize
      have tailResult := ih tailInvariant
      intro familyComparisons familyMember step stepMember
      simp only [AddInductive.FamilyParameterComparisonBlockTrace.comparisons,
        List.mem_cons] at familyMember
      rcases familyMember with rfl | familyMember
      · exact headLocal step stepMember
      · exact tailResult familyComparisons familyMember step stepMember
  | terminal dIdx stats context outOfBounds =>
      intro familyComparisons familyMember
      simp only [AddInductive.FamilyParameterComparisonBlockTrace.comparisons,
        List.not_mem_nil] at familyMember

/-- Initial-block specialization: empty entry locals and the empty initial
parameter array suffice to derive the local RHS certificate for every family
comparison. -/
theorem familyParameterComparisonBlock_comparisonRhsLocal_ofInitial
    (trace : AddInductive.FamilyParameterComparisonBlockTrace nparams
      indTypes 0
      (AddInductive.InductiveStats.initial (context.lparams.map .param))
      context)
    (lctxEmpty : context.lctx = ({} : LocalContext)) :
    ∀ familyComparisons ∈ trace.comparisons,
      ∀ step ∈ familyComparisons, FamilyComparisonRhsLocal step := by
  apply familyParameterComparisonBlock_comparisonRhsLocal trace
  refine ⟨FamilyParameterLocalState.empty context
    (context.lparams.map .param) lctxEmpty, ?_⟩
  simp [AddInductive.InductiveStats.initial]

/-- Every comparison exposed by a retained family-validation run owns the
local declaration from which its RHS type was read. -/
theorem _root_.Lean4Lean.AddInductive.FamilyValidationBlockRun.parameterComparisonRhsLocal
    (run : AddInductive.FamilyValidationBlockRun nparams indTypes context)
    (lctxEmpty : context.lctx = ({} : LocalContext))
    (familyMember : familyComparisons ∈ run.parameterComparisons)
    (comparisonMember : comparison ∈ familyComparisons) :
    TypeChecker.FamilyComparisonRhsLocal comparison := by
  apply TypeChecker.familyParameterComparisonBlock_comparisonRhsLocal_ofInitial
    run.parameterComparisonTrace lctxEmpty familyComparisons
  · simpa only [AddInductive.FamilyValidationBlockRun.parameterComparisons]
      using familyMember
  · exact comparisonMember

/-- Producer-level projection of the retained local-RHS certificate. -/
theorem _root_.Lean4Lean.AddInductive.NormalizationCandidateExecution.familyParameterComparisonRhsLocal
    (execution : AddInductive.NormalizationCandidateExecution nparams indTypes
      numNested isUnsafe context)
    (produced : AddInductive.buildNormalizationCandidateExecution nparams
      indTypes numNested isUnsafe context = .ok execution)
    (nonempty : indTypes.isEmpty = false)
    (lctxEmpty : context.lctx = ({} : LocalContext))
    (familyMember : familyComparisons ∈
      execution.familyParameterComparisons produced nonempty)
    (comparisonMember : comparison ∈ familyComparisons) :
    TypeChecker.FamilyComparisonRhsLocal comparison :=
  (execution.familyValidationBlockRun produced nonempty)
    |>.parameterComparisonRhsLocal lctxEmpty familyMember comparisonMember

/-- Reset only the implementation and Theory local contexts while retaining
the exact environment, safety mode, level parameters, fuel, and name
generator owned by a candidate context.  Constructor root `checkType` uses
precisely this context before the validation telescope re-enters the retained
family locals. -/
def CandidateContextRun.withEmptyLocalContext
    (run : CandidateContextRun candidateContext) :
    CandidateContextRun candidateContext.withEmptyLocalContext := by
  let context : VContext :=
    { run.context with
      lctx := {}
      mlctx := .nil
      mlctx_wf := trivial
      lctx_eq := rfl }
  have context_eq : context.toContext =
      candidateContext.withEmptyLocalContext.toTypeChecker := by
    change { run.context.toContext with lctx := {} } =
      candidateContext.withEmptyLocalContext.toTypeChecker
    rw [run.context_eq]
    rfl
  refine ⟨context, context_eq, ?_, run.namePrefix_ne⟩
  exact VState.WF.empty_of_reserves context (by
    intro fv hfv
    change fv ∈ VLCtx.fvars ([] : VLCtx) at hfv
    simp at hfv)

/-- Package a retained full-check observation at an already named strict
Theory source.  The verified execution still chooses the inferred Theory
type; the duplicate source translation returned by refinement is discarded,
not identified by syntactic equality. -/
theorem CheckTypeRun.exists_ofCandidateStep
    (step : AddInductive.CandidateCheckTypeStep)
    (hvalid : step.Valid)
    (contextRun : CandidateContextRun step.context)
    (source' : VExpr)
    (source_tr : contextRun.context.TrExprS step.source source') :
    ∃ inferred', Nonempty
      (CheckTypeRun contextRun.context.venv contextRun.context.lparams
        contextRun.context.vlctx step.source step.inferred source' inferred') := by
  obtain ⟨_, inferred', _, inferred_tr, _⟩ :=
    candidateCheckTypeStep_exists_translation step hvalid
      contextRun.context contextRun.context_eq contextRun.state_wf
      source_tr.fvarsIn step.context.fuel.recDepth rfl
  exact ⟨inferred', ⟨CheckTypeRun.ofCandidateStep step hvalid
    contextRun.context contextRun.context_eq rfl rfl rfl
    contextRun.state_wf source_tr inferred_tr
    step.context.fuel.recDepth rfl⟩⟩

/-- Full-check packaging when only the checker's syntactic free-variable
premise is known.  Both strict Theory endpoints are then selected by the
verified refinement of the retained execution. -/
theorem CheckTypeRun.exists_ofCandidateStepFVars
    (step : AddInductive.CandidateCheckTypeStep)
    (hvalid : step.Valid)
    (contextRun : CandidateContextRun step.context)
    (source_fvars :
      step.source.FVarsIn (· ∈ contextRun.context.vlctx.fvars)) :
    ∃ source' inferred', Nonempty
      (CheckTypeRun contextRun.context.venv contextRun.context.lparams
        contextRun.context.vlctx step.source step.inferred source' inferred') := by
  obtain ⟨source', inferred', source_tr, inferred_tr, _⟩ :=
    candidateCheckTypeStep_exists_translation step hvalid
      contextRun.context contextRun.context_eq contextRun.state_wf
      source_fvars step.context.fuel.recDepth rfl
  exact ⟨source', inferred', ⟨CheckTypeRun.ofCandidateStep step hvalid
    contextRun.context contextRun.context_eq rfl rfl rfl
    contextRun.state_wf source_tr inferred_tr
    step.context.fuel.recDepth rfl⟩⟩

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
        simp
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
  simpa [AddInductive.Context.pushLocalDecl, NameGenerator.next] using
    run.namePrefix_ne

@[simp] theorem CandidateContextRun.pushLocalDecl_venv
    (run : CandidateContextRun candidateContext)
    (domain_tr : run.context.TrExprS domain domain')
    (domain_type : run.context.IsType domain') :
    (run.pushLocalDecl name binderInfo domain fresh domain' domain_tr
      domain_type).context.venv = run.context.venv := by
  simp [CandidateContextRun.pushLocalDecl, VContext.withMLC]

@[simp] theorem CandidateContextRun.pushLocalDecl_lparams
    (run : CandidateContextRun candidateContext)
    (domain_tr : run.context.TrExprS domain domain')
    (domain_type : run.context.IsType domain') :
    (run.pushLocalDecl name binderInfo domain fresh domain' domain_tr
      domain_type).context.lparams = run.context.lparams := by
  simp [CandidateContextRun.pushLocalDecl, VContext.withMLC]

@[simp] theorem CandidateContextRun.pushLocalDecl_vlctx
    (run : CandidateContextRun candidateContext)
    (domain_tr : run.context.TrExprS domain domain')
    (domain_type : run.context.IsType domain') :
    (run.pushLocalDecl name binderInfo domain fresh domain' domain_tr
      domain_type).context.vlctx =
      (some (candidateContext.freshFVarId, domain.fvarsList),
        .vlam domain') :: run.context.vlctx := by
  simp [CandidateContextRun.pushLocalDecl, VContext.withMLC]

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
    (result_tr : TrExprS env Us Δ result result')
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
    result_tr
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
    (result_tr : context.TrExprS result result')
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
theorem CandidateNodeRun.evidence
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

private def candidateExprIdentityBinderInfoEq :
    Lean.BinderInfo → Lean.BinderInfo → Bool
  | .default, .default
  | .implicit, .implicit
  | .strictImplicit, .strictImplicit
  | .instImplicit, .instImplicit => true
  | _, _ => false

private theorem candidateExprIdentityBinderInfoEq_sound
    (left right : Lean.BinderInfo)
    (h : candidateExprIdentityBinderInfoEq left right = true) :
    left = right := by
  cases left <;> cases right <;>
    simp_all [candidateExprIdentityBinderInfoEq]

/-- Transparent structural equality sufficient for identity-normalizing
candidate traces.  Metadata nodes are conservatively rejected: the retained
generation spine never needs an opaque metadata equality to justify source
identity. -/
private def candidateExprIdentityExprEq : Lean.Expr → Lean.Expr → Bool
  | .bvar i, .bvar j => i == j
  | .fvar i, .fvar j => i == j
  | .mvar i, .mvar j => i == j
  | .sort u, .sort v => u == v
  | .const n us, .const n' us' => n == n' && us == us'
  | .app f a, .app f' a' =>
      candidateExprIdentityExprEq f f' &&
        candidateExprIdentityExprEq a a'
  | .lam n t b bi, .lam n' t' b' bi' =>
      n == n' && candidateExprIdentityExprEq t t' &&
        candidateExprIdentityExprEq b b' &&
          candidateExprIdentityBinderInfoEq bi bi'
  | .forallE n t b bi, .forallE n' t' b' bi' =>
      n == n' && candidateExprIdentityExprEq t t' &&
        candidateExprIdentityExprEq b b' &&
          candidateExprIdentityBinderInfoEq bi bi'
  | .letE n t v b nd, .letE n' t' v' b' nd' =>
      n == n' && candidateExprIdentityExprEq t t' &&
        candidateExprIdentityExprEq v v' &&
          candidateExprIdentityExprEq b b' && nd == nd'
  | .lit a, .lit b => a == b
  | .proj n i s, .proj n' i' s' =>
      n == n' && i == i' && candidateExprIdentityExprEq s s'
  | _, _ => false

private theorem candidateExprIdentityExprEq_sound :
    ∀ (left right : Lean.Expr),
      candidateExprIdentityExprEq left right = true → left = right := by
  intro left right h
  induction left generalizing right with
  | bvar i =>
      cases right <;>
        simp_all [candidateExprIdentityExprEq, beq_iff_eq]
  | fvar i =>
      cases right <;>
        simp_all [candidateExprIdentityExprEq, beq_iff_eq]
  | mvar i =>
      cases right <;>
        simp_all [candidateExprIdentityExprEq, beq_iff_eq]
  | sort u =>
      cases right <;>
        simp_all [candidateExprIdentityExprEq, beq_iff_eq]
  | const n us =>
      cases right <;>
        simp_all [candidateExprIdentityExprEq, beq_iff_eq]
  | app fn arg fnIH argIH =>
      cases right with
      | app fn' arg' =>
          simp only [candidateExprIdentityExprEq,
            Bool.and_eq_true] at h
          rw [fnIH fn' h.1, argIH arg' h.2]
      | _ => simp_all [candidateExprIdentityExprEq]
  | lam name type body binderInfo typeIH bodyIH =>
      cases right with
      | lam name' type' body' binderInfo' =>
          simp only [candidateExprIdentityExprEq, Bool.and_eq_true,
            beq_iff_eq] at h
          rw [h.1.1.1, typeIH type' h.1.1.2,
            bodyIH body' h.1.2,
            candidateExprIdentityBinderInfoEq_sound _ _ h.2]
      | _ => simp_all [candidateExprIdentityExprEq]
  | forallE name type body binderInfo typeIH bodyIH =>
      cases right with
      | forallE name' type' body' binderInfo' =>
          simp only [candidateExprIdentityExprEq, Bool.and_eq_true,
            beq_iff_eq] at h
          rw [h.1.1.1, typeIH type' h.1.1.2,
            bodyIH body' h.1.2,
            candidateExprIdentityBinderInfoEq_sound _ _ h.2]
      | _ => simp_all [candidateExprIdentityExprEq]
  | letE name type value body nondep typeIH valueIH bodyIH =>
      cases right with
      | letE name' type' value' body' nondep' =>
          simp only [candidateExprIdentityExprEq, Bool.and_eq_true,
            beq_iff_eq] at h
          rw [h.1.1.1.1, typeIH type' h.1.1.1.2,
            valueIH value' h.1.1.2, bodyIH body' h.1.2, h.2]
      | _ => simp_all [candidateExprIdentityExprEq]
  | lit literal =>
      cases right <;>
        simp_all [candidateExprIdentityExprEq, beq_iff_eq]
  | mdata data expr exprIH =>
      cases right <;> simp_all [candidateExprIdentityExprEq]
  | proj typeName idx struct structIH =>
      cases right with
      | proj typeName' idx' struct' =>
          simp only [candidateExprIdentityExprEq, Bool.and_eq_true,
            beq_iff_eq] at h
          rw [h.1.1, h.1.2, structIH struct' h.2]
      | _ => simp_all [candidateExprIdentityExprEq]

/-- Executable sufficient check for the recursive identity witness consumed
by generation.  Unlike a root-only equality, it checks every retained domain,
body, annotation result, and terminal node. -/
def CandidateExprIdentity.check :
    {candidateContext : AddInductive.Context} → {source : Lean.Expr} →
      AddInductive.CandidateExprTrace candidateContext source → Bool
  | _, _, .terminal _ source _ result _ _ =>
      candidateExprIdentityExprEq result source
  | _, _, .forallE _ source _ name domain body binderInfo _ annotations _ _ _
      domainCandidate bodyCandidate =>
    candidateExprIdentityExprEq source
        (.forallE name domain body binderInfo) &&
      candidateExprIdentityExprEq annotations.consumed domain &&
        CandidateExprIdentity.check domainCandidate &&
          CandidateExprIdentity.check bodyCandidate

/-- Executable sufficient equality check for the terminal expression selected
by a candidate trace.  This is useful when the family validator must name its
result universe without unfolding the proof-carrying trace. -/
def CandidateExprIdentity.terminalCheck
    (trace : AddInductive.CandidateExprTrace candidateContext source)
    (expected : Lean.Expr) : Bool :=
  candidateExprIdentityExprEq trace.terminalResult expected

theorem CandidateExprIdentity.terminalResult_eq_of_check
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {expected : Lean.Expr}
    (h : CandidateExprIdentity.terminalCheck trace expected = true) :
    trace.terminalResult = expected :=
  candidateExprIdentityExprEq_sound _ _ h

/-- A successful structural check yields the full recursive identity witness;
the Boolean contributes no semantic authority beyond these proved equalities. -/
theorem CandidateExprIdentity.of_check
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    (h : CandidateExprIdentity.check trace = true) :
    CandidateExprIdentity trace := by
  induction trace with
  | terminal context source inferred result checked normalized =>
      simp only [CandidateExprIdentity.check] at h
      exact .terminal (candidateExprIdentityExprEq_sound result source h)
  | forallE context source inferred name domain body binderInfo fresh
      annotations annotationsEq checked normalized domainCandidate
      bodyCandidate domainIH bodyIH =>
      simp only [CandidateExprIdentity.check, Bool.and_eq_true] at h
      exact .forallE domainCandidate bodyCandidate
        (candidateExprIdentityExprEq_sound _ _ h.1.1.1)
        (candidateExprIdentityExprEq_sound _ _ h.1.1.2)
        (domainIH h.1.2) (bodyIH h.2)

/-- An identity-normalizing trace necessarily preserves the stored main Pi
spine. This turns the recursive identity witness into the Boolean gate used
by the generation assembler. -/
theorem CandidateExprIdentity.storedSpine
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    (identity : CandidateExprIdentity trace) :
    trace.storedSpine = true := by
  induction identity with
  | terminal => rfl
  | forallE _ _ source_eq _ _ _ _ bodyIH =>
    simp [AddInductive.CandidateExprTrace.storedSpine,
      source_eq, Expr.structuralEq_refl, bodyIH]

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

/-- At a nonterminal index boundary, translate both the raw binder domain and
the exact annotation-consumed kernel domain selected by validation.

The result is source-indexed: the raw `forallE` syntax is recovered from the
boundary itself, and annotation peeling follows that kernel domain's retained
structural trace.  No translated-endpoint peeling function is assumed. -/
structure FamilyParameterIndexBoundary.IndexDomainTranslation
    (boundary : FamilyParameterIndexBoundary outer contextRun) : Type where
  name : Name
  domain : Expr
  body : Expr
  binderInfo : BinderInfo
  domain' : VExpr
  body' : VExpr
  consumed' : VExpr
  source_eq : boundary.source = .forallE name domain body binderInfo
  source'_eq : boundary.source' = .forallE domain' body'
  domain_type : contextRun.context.IsType domain'
  body_type : contextRun.context.venv.IsType
    contextRun.context.lparams.length
    (domain' :: contextRun.context.vlctx.toCtx) body'
  domain_tr : contextRun.context.TrExprS domain domain'
  body_tr : TrExprS contextRun.context.venv contextRun.context.lparams
    ((none, .vlam domain') :: contextRun.context.vlctx) body body'
  consumed_tr : contextRun.context.TrExprS
    (AddInductive.consumeTypeAnnotations domain) consumed'

/-- Construct the complete source-indexed translation package for the next
index domain. -/
theorem FamilyParameterIndexBoundary.indexDomainTranslation_of_forall
    (boundary : FamilyParameterIndexBoundary outer contextRun)
    (isForall : boundary.source.isForall = true) :
    Nonempty boundary.IndexDomainTranslation := by
  cases hsource : boundary.source with
  | forallE name domain body binderInfo =>
    have source_tr := boundary.source_tr
    rw [hsource] at source_tr
    obtain ⟨domain', body', source'_eq, domainType, bodyType,
        domain_tr, body_tr⟩ := TrExprS.forallE_components source_tr
    obtain ⟨consumed', consumed_tr⟩ :=
      consumeTypeAnnotations_exists_translation domain_tr
    exact ⟨{
      name := name
      domain := domain
      body := body
      binderInfo := binderInfo
      domain' := domain'
      body' := body'
      consumed' := consumed'
      source_eq := hsource
      source'_eq := source'_eq
      domain_type := domainType
      body_type := bodyType
      domain_tr := domain_tr
      body_tr := body_tr
      consumed_tr := consumed_tr }⟩
  | _ => simp_all [Expr.isForall]

/-- Compatibility projection retaining the earlier existential surface. -/
theorem FamilyParameterIndexBoundary.annotationTranslation_of_forall
    (boundary : FamilyParameterIndexBoundary outer contextRun)
    (isForall : boundary.source.isForall = true) :
    ∃ name domain body binderInfo domain' body' consumed',
      boundary.source = .forallE name domain body binderInfo ∧
      boundary.source' = .forallE domain' body' ∧
      contextRun.context.TrExprS domain domain' ∧
      contextRun.context.TrExprS
        (AddInductive.consumeTypeAnnotations domain) consumed' := by
  obtain ⟨run⟩ := boundary.indexDomainTranslation_of_forall isForall
  exact ⟨run.name, run.domain, run.body, run.binderInfo, run.domain',
    run.body', run.consumed', run.source_eq, run.source'_eq, run.domain_tr,
    run.consumed_tr⟩

/-- Semantic completion of one translated index domain.  The single new fact
is the raw/annotation-consumed definitional equality at the exact Theory
endpoints selected above; the candidate telescope is responsible for
constructing this field. -/
structure FamilyParameterIndexBoundary.IndexDomainRun
    (boundary : FamilyParameterIndexBoundary outer contextRun) : Type where
  translation : boundary.IndexDomainTranslation
  sort : VLevel
  annotation_def : contextRun.context.venv.IsDefEq
    contextRun.context.lparams.length contextRun.context.vlctx.toCtx
    translation.domain' translation.consumed' (.sort sort)

/-- The completed annotation equality types the exact local domain used by
validation. -/
theorem FamilyParameterIndexBoundary.IndexDomainRun.consumed_type
    {outer : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
      context rootSource i nindices rootFuel}
    {contextRun : CandidateContextRun context}
    {boundary : FamilyParameterIndexBoundary outer contextRun}
    (run : FamilyParameterIndexBoundary.IndexDomainRun boundary) :
    contextRun.context.IsType run.translation.consumed' :=
  ⟨run.sort, run.annotation_def.hasType.2⟩

/-- Push the exact validator local declaration selected by a completed index
domain.  Freshness is derived from the boundary's retained local-context
inventory. -/
def FamilyParameterIndexBoundary.IndexDomainRun.pushContext
    {outer : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
      context rootSource i nindices rootFuel}
    {contextRun : CandidateContextRun context}
    {boundary : FamilyParameterIndexBoundary outer contextRun}
    (run : FamilyParameterIndexBoundary.IndexDomainRun boundary) :
    CandidateContextRun
      (context.pushLocalDecl run.translation.name
        run.translation.binderInfo
        (AddInductive.consumeTypeAnnotations run.translation.domain)) :=
  contextRun.pushLocalDecl run.translation.name run.translation.binderInfo
    (AddInductive.consumeTypeAnnotations run.translation.domain)
    boundary.localState.localContext.fresh run.translation.consumed'
    run.translation.consumed_tr run.consumed_type

/-- Relocate the retained raw-body translation across the exact
raw/annotation-consumed domain equality before instantiating the validator's
fresh free variable. -/
theorem FamilyParameterIndexBoundary.IndexDomainRun.bodyTranslation
    {outer : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
      context rootSource i nindices rootFuel}
    {contextRun : CandidateContextRun context}
    {boundary : FamilyParameterIndexBoundary outer contextRun}
    (run : FamilyParameterIndexBoundary.IndexDomainRun boundary) :
    ∃ body'', TrExprS contextRun.context.venv contextRun.context.lparams
      ((none, .vlam run.translation.consumed') ::
        contextRun.context.vlctx) run.translation.body body'' := by
  have henv : VEnv.WF contextRun.context.venv := contextRun.context.Ewf
  let domainContext : VLCtx.IsDefEq contextRun.context.venv
      contextRun.context.lparams.length
      ((none, .vlam run.translation.domain') :: contextRun.context.vlctx)
      ((none, .vlam run.translation.consumed') ::
        contextRun.context.vlctx) :=
    .cons (.refl henv contextRun.context.Δwf) (by nofun)
      (.vlam run.annotation_def)
  exact run.translation.body_tr.defeqDFC henv domainContext

/-- Instantiate the relocated body translation with the exact fresh free
variable allocated by validation's pushed context. -/
theorem
    FamilyParameterIndexBoundary.IndexDomainRun.instantiatedBodyTranslation
    {outer : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
      context rootSource i nindices rootFuel}
    {contextRun : CandidateContextRun context}
    {boundary : FamilyParameterIndexBoundary outer contextRun}
    (run : FamilyParameterIndexBoundary.IndexDomainRun boundary) :
    ∃ body'', run.pushContext.context.TrExprS
      (run.translation.body.instantiate1 context.freshExpr) body'' := by
  obtain ⟨storedBody', storedBody_tr⟩ := run.bodyTranslation
  let nextContextRun := run.pushContext
  have bodyVenv : nextContextRun.context.venv =
      contextRun.context.venv := rfl
  have bodyLparams : nextContextRun.context.lparams =
      contextRun.context.lparams := rfl
  have bodyVlctx : nextContextRun.context.vlctx =
      (some (context.freshFVarId,
          (AddInductive.consumeTypeAnnotations
            run.translation.domain).fvarsList),
        .vlam run.translation.consumed') ::
        contextRun.context.vlctx := rfl
  have bodyΔwf := nextContextRun.context.Δwf
  rw [bodyVenv, bodyLparams, bodyVlctx] at bodyΔwf
  have instantiatedBody_tr :=
    storedBody_tr.inst_fvar contextRun.context.Ewf.ordered bodyΔwf
  refine ⟨storedBody', ?_⟩
  change TrExprS nextContextRun.context.venv
    nextContextRun.context.lparams nextContextRun.context.vlctx
    (run.translation.body.instantiate1 context.freshExpr) storedBody'
  rw [bodyVenv, bodyLparams, bodyVlctx]
  simpa only [AddInductive.Context.freshExpr, Expr.instantiate1_eq] using
    instantiatedBody_tr

/-- Exact producer-owned continuation after consuming one index binder.

The record retains both sides of the WHNF observation and the validator's
actual tail trace.  Its result equality continues to point at the original
outer family trace, while `toBoundary` below exposes the tail as the next
source-indexed boundary. -/
structure FamilyParameterIndexBoundary.IndexDomainAdvance
    {outer : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
      context rootSource i nindices rootFuel}
    {contextRun : CandidateContextRun context}
    {boundary : FamilyParameterIndexBoundary outer contextRun}
    (run : FamilyParameterIndexBoundary.IndexDomainRun boundary) : Type where
  body' : VExpr
  body_tr : run.pushContext.context.TrExprS
    (run.translation.body.instantiate1 context.freshExpr) body'
  view : Expr
  fuel : Nat
  tail : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
    (context.pushLocalDecl run.translation.name
      run.translation.binderInfo
      (AddInductive.consumeTypeAnnotations run.translation.domain))
    view nparams (nindices + 1) fuel
  view' : VExpr
  view_tr : run.pushContext.context.TrExprS view view'
  whnf_valid : AddInductive.CandidateWhnfStep.Valid
    ⟨context.pushLocalDecl run.translation.name
        run.translation.binderInfo
        (AddInductive.consumeTypeAnnotations run.translation.domain),
      run.translation.body.instantiate1 context.freshExpr, view⟩
  whnf : Nonempty (WhnfRun run.pushContext.context.venv
    run.pushContext.context.lparams run.pushContext.context.vlctx
    (run.translation.body.instantiate1 context.freshExpr) view body' view')
  localState : FamilyParameterLocalState stats
    (context.pushLocalDecl run.translation.name
      run.translation.binderInfo
      (AddInductive.consumeTypeAnnotations run.translation.domain))
  result_eq : tail.result = outer.result
  comparisons_eq_nil : tail.comparisons = []

/-- Re-index an exact one-step continuation as the next index boundary. -/
def FamilyParameterIndexBoundary.IndexDomainAdvance.toBoundary
    {outer : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
      context rootSource i nindices rootFuel}
    {contextRun : CandidateContextRun context}
    {boundary : FamilyParameterIndexBoundary outer contextRun}
    {run : FamilyParameterIndexBoundary.IndexDomainRun boundary}
    (advance : FamilyParameterIndexBoundary.IndexDomainAdvance run) :
    FamilyParameterIndexBoundary advance.tail run.pushContext where
  source := advance.view
  fuel := advance.fuel
  trace := advance.tail
  source' := advance.view'
  source_tr := advance.view_tr
  parameters := []
  parameter_tr := by
    intro parameter member
    simp at member
  parameters_length := by simp
  params_size := boundary.params_size
  parameter_sources_eq := by
    simp only [List.map_nil]
    symm
    apply List.drop_of_length_le
    simpa using Nat.le_of_eq boundary.params_size
  prefix_path := .done advance.tail
  localState := advance.localState
  result_eq := rfl
  comparisons_eq_nil := advance.comparisons_eq_nil

/-- The re-indexed boundary still reaches the original family result. -/
theorem FamilyParameterIndexBoundary.IndexDomainAdvance.result_eq_outer
    {outer : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
      context rootSource i nindices rootFuel}
    {contextRun : CandidateContextRun context}
    {boundary : FamilyParameterIndexBoundary outer contextRun}
    {run : FamilyParameterIndexBoundary.IndexDomainRun boundary}
    (advance : FamilyParameterIndexBoundary.IndexDomainAdvance run) :
    advance.toBoundary.trace.result = outer.result := by
  exact advance.result_eq

/-- Consume the validator's exact `index` constructor, replay its retained
WHNF step in the pushed verified context, and expose its exact tail.

The completed `IndexDomainRun` is the only semantic input: it supplies the
raw/annotation-consumed Theory equality at the source-indexed domain chosen
by validation. -/
theorem FamilyParameterIndexBoundary.IndexDomainRun.advance
    {outer : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
      context rootSource i nindices rootFuel}
    {contextRun : CandidateContextRun context}
    {boundary : FamilyParameterIndexBoundary outer contextRun}
    (run : FamilyParameterIndexBoundary.IndexDomainRun boundary)
    (whnfFuel : Nat)
    (whnfDepth : context.fuel.recDepth = whnfFuel + 1) :
    Nonempty (FamilyParameterIndexBoundary.IndexDomainAdvance run) := by
  obtain ⟨body', body_tr⟩ := run.instantiatedBodyTranslation
  rcases boundary with
    ⟨boundarySource, boundaryFuel, boundaryTrace, boundarySource',
      boundarySourceTr, boundaryParameters, boundaryParameterTr,
      boundaryParametersLength, boundaryParamsSize,
      boundaryParameterSourcesEq, boundaryPrefixPath, boundaryLocalState,
      boundaryResultEq, boundaryComparisons⟩
  cases boundaryTrace with
  | freshParameter stats context i nindices fuel name domain body view
      binderInfo isParameter firstFamily whnf tail =>
    omega
  | sharedParameter stats context i nindices fuel name domain body
      parameterType view binderInfo isParameter laterFamily parameterTypeRun
      defeq whnf tail =>
    omega
  | index stats context i nindices fuel name domain body view binderInfo
      notParameter whnf tail =>
    have source_eq := run.translation.source_eq
    simp only [Expr.forallE.injEq] at source_eq
    rcases source_eq with
      ⟨name_eq, domain_eq, body_eq, binderInfo_eq⟩
    have whnf' : AddInductive.CandidateWhnfStep.Valid
        ⟨context.pushLocalDecl run.translation.name
            run.translation.binderInfo
            (AddInductive.consumeTypeAnnotations run.translation.domain),
          run.translation.body.instantiate1 context.freshExpr, view⟩ := by
      simpa only [← name_eq, ← domain_eq, ← body_eq,
        ← binderInfo_eq] using whnf
    have tail_result_eq : tail.result = outer.result := by
      simpa only [AddInductive.FamilyTypeParameterComparisonTrace.result]
        using boundaryResultEq
    have tail_comparisons : tail.comparisons = [] := by
      simpa only [
        AddInductive.FamilyTypeParameterComparisonTrace.comparisons]
        using boundaryComparisons
    have transportTail :
        ∀ (translatedName : Name) (translatedDomain : Expr)
            (translatedBinderInfo : BinderInfo),
          name = translatedName → domain = translatedDomain →
          binderInfo = translatedBinderInfo →
          ∃ tail' :
              AddInductive.FamilyTypeParameterComparisonTrace nparams stats
                (context.pushLocalDecl translatedName translatedBinderInfo
                  (AddInductive.consumeTypeAnnotations translatedDomain))
                view nparams (nindices + 1) fuel,
            tail'.result = outer.result ∧ tail'.comparisons = [] := by
      intro translatedName translatedDomain translatedBinderInfo
        translatedName_eq translatedDomain_eq translatedBinderInfo_eq
      subst translatedName
      subst translatedDomain
      subst translatedBinderInfo
      exact ⟨tail, tail_result_eq, tail_comparisons⟩
    obtain ⟨tail', tailResultEq, tailComparisons⟩ :=
      transportTail run.translation.name run.translation.domain
        run.translation.binderInfo name_eq domain_eq binderInfo_eq
    have nextDepth :
        (context.pushLocalDecl run.translation.name
          run.translation.binderInfo
          (AddInductive.consumeTypeAnnotations
            run.translation.domain)).fuel.recDepth = whnfFuel + 1 := by
      simpa [AddInductive.Context.pushLocalDecl] using whnfDepth
    obtain ⟨view', view_tr, whnfRun⟩ :=
      WhnfRun.exists_ofCandidateStep
        ⟨context.pushLocalDecl run.translation.name
            run.translation.binderInfo
            (AddInductive.consumeTypeAnnotations run.translation.domain),
          run.translation.body.instantiate1 context.freshExpr, view⟩
        whnf' run.pushContext body' body_tr whnfFuel nextDepth
    exact ⟨{
      body' := body'
      body_tr := body_tr
      view := view
      fuel := fuel
      tail := tail'
      view' := view'
      view_tr := view_tr
      whnf_valid := whnf'
      whnf := whnfRun
      localState := boundaryLocalState.pushLocal run.translation.name
        run.translation.binderInfo
        (AddInductive.consumeTypeAnnotations run.translation.domain)
      result_eq := by
        exact tailResultEq
      comparisons_eq_nil := tailComparisons }⟩
  | terminal stats context source i nindices fuel notForall
      parametersComplete =>
    have source_eq := run.translation.source_eq
    change boundarySource = .forallE run.translation.name
      run.translation.domain run.translation.body
        run.translation.binderInfo at source_eq
    rw [source_eq] at notForall
    contradiction

/-- Exact terminal witness for an index boundary which has no remaining Pi
node.  The boundary itself continues to retain the complete dependent result
equation back to the outer family trace. -/
structure FamilyParameterIndexBoundary.Terminal
    (boundary : FamilyParameterIndexBoundary outer contextRun) : Type where
  notForall : boundary.source.isForall = false

/-- The family telescope's index counter is monotone.  Shared parameters do
not change it, while every index constructor advances it exactly once. -/
theorem _root_.Lean4Lean.AddInductive.FamilyTypeParameterComparisonTrace.result_nindices_ge
    (trace : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
      context source i nindices fuel) :
    nindices ≤ trace.result.nindices := by
  induction trace with
  | freshParameter stats context i nindices fuel name domain body view
      binderInfo isParameter firstFamily whnf tail ih =>
    exact ih
  | sharedParameter stats context i nindices fuel name domain body
      parameterType view binderInfo isParameter laterFamily parameterTypeRun
      defeq whnf tail ih =>
    exact ih
  | index stats context i nindices fuel name domain body view binderInfo
      notParameter whnf tail ih =>
    simp only [AddInductive.FamilyTypeParameterComparisonTrace.result]
    omega
  | terminal => exact Nat.le_refl _

/-- A terminal index boundary is already at the reader context stored by its
trace result.  The dependent counter rules out parameter constructors, and
the non-Pi witness rules out an index constructor. -/
theorem FamilyParameterIndexBoundary.Terminal.result_context_eq
    {nparams : Nat} {stats : AddInductive.InductiveStats}
    {context : AddInductive.Context} {rootSource : Lean.Expr}
    {i nindices rootFuel : Nat}
    {outer : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
      context rootSource i nindices rootFuel}
    {contextRun : CandidateContextRun context}
    {boundary : FamilyParameterIndexBoundary outer contextRun}
    (terminal : boundary.Terminal) :
    boundary.trace.result.context = context := by
  have boundaryNotForall := terminal.notForall
  rcases boundary with
    ⟨boundarySource, boundaryFuel, boundaryTrace, boundarySource',
      boundarySourceTr, boundaryParameters, boundaryParameterTr,
      boundaryParametersLength, boundaryParamsSize,
      boundaryParameterSourcesEq, boundaryPrefixPath, boundaryLocalState,
      boundaryResultEq, boundaryComparisons⟩
  cases boundaryTrace with
  | freshParameter stats context i nindices fuel name domain body view
      binderInfo isParameter firstFamily whnf tail => omega
  | sharedParameter stats context i nindices fuel name domain body
      parameterType view binderInfo isParameter laterFamily parameterTypeRun
      defeq whnf tail => omega
  | index stats context i nindices fuel name domain body view binderInfo
      notParameter whnf tail =>
    simp only [Lean.Expr.isForall] at boundaryNotForall
    contradiction
  | terminal => rfl

/-- If an index-only suffix reaches the same index counter at its final
result, it is already terminal.  An `index` constructor would force the
counter to grow, while parameter constructors are impossible at the retained
`i = nparams` boundary. -/
theorem FamilyParameterIndexBoundary.terminal_of_result_nindices_eq
    {nparams : Nat} {stats : AddInductive.InductiveStats}
    {context : AddInductive.Context} {rootSource : Lean.Expr}
    {i nindices rootFuel : Nat}
    {outer : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
      context rootSource i nindices rootFuel}
    {contextRun : CandidateContextRun context}
    (boundary : FamilyParameterIndexBoundary outer contextRun)
    (complete : boundary.trace.result.nindices = nindices) :
    Nonempty boundary.Terminal := by
  rcases boundary with
    ⟨boundarySource, boundaryFuel, boundaryTrace, boundarySource',
      boundarySourceTr, boundaryParameters, boundaryParameterTr,
      boundaryParametersLength, boundaryParamsSize,
      boundaryParameterSourcesEq, boundaryPrefixPath, boundaryLocalState,
      boundaryResultEq, boundaryComparisons⟩
  cases boundaryTrace with
  | freshParameter stats context i nindices fuel name domain body view
      binderInfo isParameter firstFamily whnf tail =>
    omega
  | sharedParameter stats context i nindices fuel name domain body
      parameterType view binderInfo isParameter laterFamily parameterTypeRun
      defeq whnf tail =>
    omega
  | index stats context i nindices fuel name domain body view binderInfo
      notParameter whnf tail =>
    have tailBound := tail.result_nindices_ge
    simp only [AddInductive.FamilyTypeParameterComparisonTrace.result]
      at complete
    omega
  | terminal stats context source i nindices fuel notForall
      parametersComplete =>
    exact ⟨{ notForall := notForall }⟩

/-- At `i = nparams`, the retained family trace is either the next exact index
Pi or its exact terminal continuation.  Fresh/shared-parameter constructors
are excluded by their dependent counter premise. -/
theorem FamilyParameterIndexBoundary.progress
    (boundary : FamilyParameterIndexBoundary outer contextRun) :
    boundary.source.isForall = true ∨ Nonempty boundary.Terminal := by
  rcases boundary with
    ⟨boundarySource, boundaryFuel, boundaryTrace, boundarySource',
      boundarySourceTr, boundaryParameters, boundaryParameterTr,
      boundaryParametersLength, boundaryParamsSize,
      boundaryParameterSourcesEq, boundaryPrefixPath, boundaryLocalState,
      boundaryResultEq, boundaryComparisons⟩
  cases boundaryTrace with
  | freshParameter stats context i nindices fuel name domain body view
      binderInfo isParameter firstFamily whnf tail =>
    omega
  | sharedParameter stats context i nindices fuel name domain body
      parameterType view binderInfo isParameter laterFamily parameterTypeRun
      defeq whnf tail =>
    omega
  | index stats context i nindices fuel name domain body view binderInfo
      notParameter whnf tail =>
    exact .inl rfl
  | terminal stats context source i nindices fuel notForall
      parametersComplete =>
    exact .inr ⟨{ notForall := notForall }⟩

/-- One source-indexed elimination step at the exact parameter/index
boundary.  A remaining Pi exposes the validator's raw and
annotation-consumed domain translations; otherwise the exact terminal payload
is returned. -/
theorem FamilyParameterIndexBoundary.annotationTranslation_or_terminal
    (boundary : FamilyParameterIndexBoundary outer contextRun) :
    (∃ name domain body binderInfo domain' body' consumed',
      boundary.source = .forallE name domain body binderInfo ∧
      boundary.source' = .forallE domain' body' ∧
      contextRun.context.TrExprS domain domain' ∧
      contextRun.context.TrExprS
        (AddInductive.consumeTypeAnnotations domain) consumed') ∨
      Nonempty boundary.Terminal := by
  rcases boundary.progress with isForall | terminal
  · exact .inl (boundary.annotationTranslation_of_forall isForall)
  · exact .inr terminal

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
    obtain ⟨inferred', ⟨node⟩⟩ :=
      CandidateNodeRun.exists_ofCandidateAtResult
        context source inferred source checked normalized
        candidateRun.context candidateRun.context_eq candidateRun.state_wf
        source' source' source_tr source_tr
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
    obtain ⟨inferred', ⟨node⟩⟩ :=
      CandidateNodeRun.exists_ofCandidateAtResult
        context (.forallE name domain body binderInfo) inferred
        (.forallE name domain body binderInfo) checked normalized
        candidateRun.context candidateRun.context_eq candidateRun.state_wf
        (.forallE domain' body') (.forallE domain' body')
        source_tr source_tr
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
    have bodyDeltaWF := bodyCandidateRun.context.Δwf
    rw [bodyVenv, bodyLparams, bodyVlctx] at bodyDeltaWF
    have instantiatedBody_tr :=
      body_tr.inst_fvar candidateRun.context.Ewf.ordered
        bodyDeltaWF
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
theorem CandidateExprRun.evidence
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
  | @terminal Δ context source inferred result source' result' inferred'
      checked normalized node =>
      have henv : VEnv.WF env := by
        simpa only [node.whnf.venv_eq] using node.whnf.context.Ewf
      have hΔ : VLCtx.WF env Us.length Δ := by
        simpa only [node.whnf.venv_eq, node.whnf.lparams_eq,
          node.whnf.vlctx_eq] using node.whnf.context.Δwf
      simpa only [AddInductive.CandidateExprTrace.view] using
        node.whnf.rhs_tr.trExpr henv hΔ
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
      have hnoBV : Δ.NoBV := by
        rw [← node.check.vlctx_eq]
        exact node.check.context.mlctx.noBV
      have hclosed : bodyCandidate.view.looseBVarRange' = 0 :=
        ((show VLCtx.bvars ((some (context.freshFVarId,
            annotations.consumed.fvarsList), VLocalDecl.vlam storedDomain') :: Δ) = 0 by
            exact hnoBV) ▸ bodyIH'.closed).looseBVarRange_zero
      rw [show #[context.freshExpr] =
        ⟨[context.freshFVarId].map Expr.fvar⟩ by rfl]
      rw [Expr.abstract_eq _ _ (.inr hclosed) (by simp)]
      rfl
    apply TrExpr.forallE henv hΔ
    · exact ⟨_, domainDef.hasType.2⟩
    · exact ⟨_, bodyDefMoved.hasType.2⟩
    · exact domainIH
    · simpa only [AddInductive.CandidateExprTrace.view,
        habstract] using bodyMoved

/-- Exact-translation uniqueness for every expression that contributes to a
candidate view.  The abstracted-body clause names the syntax stored by
`CandidateExprTrace.view`, while the recursive body clause supports the next
candidate node.  Projections are intentionally excluded: their verified
Theory relation is only unique up to definitional equality. -/
def CandidateExprTraceViewIsUnique :
    {context : AddInductive.Context} → {source : Expr} →
      AddInductive.CandidateExprTrace context source → Prop
  | _, _, .terminal _ _ _ result _ _ => TrExprS.IsUnique result
  | _, _, .forallE context _ _ _ _ _ _ _ _ _ _ _ domain body =>
      CandidateExprTraceViewIsUnique domain ∧
        CandidateExprTraceViewIsUnique body ∧
        TrExprS.IsUnique (body.view.abstract #[context.freshExpr])

/-- The recursive uniqueness certificate in particular covers the complete
view reconstructed at this candidate node. -/
theorem CandidateExprTraceViewIsUnique.view
    {context : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace context source}
    (unique : CandidateExprTraceViewIsUnique trace) :
    TrExprS.IsUnique trace.view := by
  induction trace with
  | terminal => exact unique
  | forallE context source inferred name domain body binderInfo fresh
      annotations annotationsEq checked normalized domainCandidate bodyCandidate
      domainIH bodyIH =>
    exact ⟨domainIH unique.1, unique.2.2⟩

/-- A projection-free candidate view retains the strict Theory translation
selected componentwise by its recursive semantic run.

The ordinary `view_tr` theorem must use weak translation because a projection
endpoint is only definitionally determined.  Under the explicit uniqueness
condition, recursive abstraction and context transport select the exact
analyzer-owned expression instead. -/
theorem CandidateExprRun.view_tr_strict
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {Δ : VLCtx} {source' view' inferred' : VExpr}
    (run : CandidateExprRun env Us trace Δ source' view' inferred')
    (unique : CandidateExprTraceViewIsUnique trace) :
    TrExprS env Us Δ trace.view view' := by
  induction run with
  | terminal node =>
      simpa only [AddInductive.CandidateExprTrace.view] using
        node.whnf.rhs_tr
  | @forallE domain context name binderInfo Δ source inferred body
      source' domain' body' inferred' domainView' domainInferred'
      storedDomain' bodyΔ storedBody' bodyView' bodyInferred' u v fresh
      checked normalized annotations annotationsEq domainCandidate
      bodyCandidate node domainRun annotationsRun bodyRun domainType bodyType
      bodySource bodyContext domainIH bodyIH =>
    rcases unique with ⟨domainUnique, bodyUnique, abstractUnique⟩
    have domainStrict := domainIH domainUnique
    have bodyStrict : TrExprS env Us
        ((some (context.freshFVarId,
          annotations.consumed.fvarsList), .vlam storedDomain') :: Δ)
        bodyCandidate.view bodyView' := by
      simpa only [bodyContext] using bodyIH bodyUnique
    have bodyAbstract := bodyStrict.abstract VLCtx.Abstract.zero
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
    have hctx : VLCtx.IsDefEq env Us.length
        ((none, .vlam storedDomain') :: Δ)
        ((none, .vlam domainView') :: Δ) :=
      .cons (.refl henv hΔ) (by nofun) (.vlam storedToView)
    obtain ⟨bodyMoved', bodyMoved⟩ :=
      bodyAbstract.defeqDFC henv hctx
    have habstract :
        bodyCandidate.view.abstract #[context.freshExpr] =
          Expr.abstract1 context.freshFVarId bodyCandidate.view := by
      have hnoBV : Δ.NoBV := by
        rw [← node.check.vlctx_eq]
        exact node.check.context.mlctx.noBV
      have hclosed : bodyCandidate.view.looseBVarRange' = 0 :=
        ((show VLCtx.bvars ((some (context.freshFVarId,
            annotations.consumed.fvarsList), VLocalDecl.vlam storedDomain') :: Δ) = 0 by
            exact hnoBV) ▸ bodyStrict.closed).looseBVarRange_zero
      rw [show #[context.freshExpr] =
        ⟨[context.freshFVarId].map Expr.fvar⟩ by rfl]
      rw [Expr.abstract_eq _ _ (.inr hclosed) (by simp)]
      rfl
    have bodyAbstractArray : TrExprS env Us
        ((none, .vlam storedDomain') :: Δ)
        (bodyCandidate.view.abstract #[context.freshExpr]) bodyView' := by
      simpa only [habstract] using bodyAbstract
    have bodyMovedArray : TrExprS env Us
        ((none, .vlam domainView') :: Δ)
        (bodyCandidate.view.abstract #[context.freshExpr]) bodyMoved' := by
      simpa only [habstract] using bodyMoved
    have bodyMoved_eq : bodyMoved' = bodyView' := by
      exact (bodyAbstractArray.unique'
        (.cons .base .vlam) abstractUnique bodyMovedArray).symm
    subst bodyMoved'
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
    simpa only [AddInductive.CandidateExprTrace.view, habstract] using
      TrExprS.forallE
        (⟨u, domainDef.hasType.2⟩ :
          env.IsType Us.length Δ.toCtx domainView')
        (⟨v, bodyDefMoved.hasType.2⟩ :
          env.IsType Us.length (domainView' :: Δ.toCtx) bodyView')
        domainStrict bodyMoved

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
    simpa only [AddInductive.CandidateExpr.view, run.venv_eq,
      run.lparams_eq, run.vlctx_eq] using
      candidateRun.view_tr
  have viewDef : env.IsDefEqU Us.length [] candidateView' view' :=
    candidateView_tr.uniq henv (.refl henv hΔ) run.view_tr
  have sourceDef : env.IsDefEqU Us.length [] source' candidateView' := by
    simpa only [run.venv_eq, run.lparams_eq, run.vlctx_eq,
      VLCtx.toCtx] using
      candidateRun.evidence.isDefEq.toU
  obtain ⟨A, hfinal⟩ := sourceDef.trans henv hΔ.toCtx viewDef
  exact ⟨A, .ofDefEq hfinal⟩

/-- A root candidate together with the exact recursively interpreted semantic
run selected by its retained checker executions.

Unlike `CandidateExprRootRun`, this bundle does not stop at whole-expression
equality: it retains the exact inferred type and reconstructed Theory view at
every recursive candidate position. Consequently the same value can supply
both normalization evidence and, when the executable trace preserves its main
Pi spine, the positional telescope/result evidence required by generation.
The view is selected by the verified run rather than supplied independently by
a caller. -/
structure CandidateExprSemanticRootRun (env : VEnv) (Us : List Name)
    {source : Expr} (candidate : AddInductive.CandidateExpr source)
    (source' : VExpr) where
  contextRun : CandidateContextRun candidate.context
  venv_eq : contextRun.context.venv = env
  lparams_eq : contextRun.context.lparams = Us
  vlctx_eq : contextRun.context.vlctx = []
  source_tr : TrExprS env Us [] source source'
  whnfFuel : Nat
  whnfDepth : candidate.context.fuel.recDepth = whnfFuel + 1
  view : VExpr
  recursive : ∃ inferred, CandidateExprRun env Us candidate.trace []
    source' view inferred

/-- Forget the retained recursive run and expose the existing root semantic
interface. The reconstructed view translation is derived from that same run,
so it cannot name an unrelated endpoint. -/
def CandidateExprSemanticRootRun.root
    (run : CandidateExprSemanticRootRun env Us candidate source') :
    CandidateExprRootRun env Us candidate source' run.view where
  contextRun := run.contextRun
  venv_eq := run.venv_eq
  lparams_eq := run.lparams_eq
  vlctx_eq := run.vlctx_eq
  source_tr := run.source_tr
  view_tr := by
    obtain ⟨_, recursive⟩ := run.recursive
    simpa only [AddInductive.CandidateExpr.view] using
      recursive.view_tr
  whnfFuel := run.whnfFuel
  whnfDepth := run.whnfDepth

/-- Automatically construct the retained root semantics from an exact
verified candidate context and strict translation of the stored kernel
source.

The checker run selects the Theory view and inferred type existentially; the
result records those exact selections. No caller-selected normalization view,
erasure equality, or whole-Pi injectivity principle is used. -/
theorem CandidateExprSemanticRootRun.exists_ofCandidate
    {env : VEnv} {Us : List Name} {source : Expr}
    {candidate : AddInductive.CandidateExpr source} {source' : VExpr}
    (contextRun : CandidateContextRun candidate.context)
    (venv_eq : contextRun.context.venv = env)
    (lparams_eq : contextRun.context.lparams = Us)
    (vlctx_eq : contextRun.context.vlctx = [])
    (source_tr : TrExprS env Us [] source source')
    (whnfFuel : Nat)
    (whnfDepth : candidate.context.fuel.recDepth = whnfFuel + 1) :
    Nonempty (CandidateExprSemanticRootRun env Us candidate source') := by
  have contextualSource :
      contextRun.context.TrExprS source source' := by
    simpa only [VContext.TrExprS, venv_eq, lparams_eq, vlctx_eq] using
      source_tr
  obtain ⟨view, inferred, ⟨recursive⟩⟩ :=
    CandidateExprRun.exists_ofCandidate candidate.trace contextRun source'
      contextualSource whnfFuel whnfDepth
  refine ⟨{
    contextRun := contextRun
    venv_eq := venv_eq
    lparams_eq := lparams_eq
    vlctx_eq := vlctx_eq
    source_tr := source_tr
    whnfFuel := whnfFuel
    whnfDepth := whnfDepth
    view := view
    recursive := ⟨inferred, ?_⟩ }⟩
  simpa only [venv_eq, lparams_eq, vlctx_eq] using recursive

/-- The exact pre-run evidence needed to interpret one candidate root without
asking a caller to choose its normalized Theory view.

This bundle deliberately stops before the recursive semantic run.  It contains
only the verified implementation context, its alignment with the requested
Theory environment, the strict translation of the stored source, and the fuel
relation consumed by `CandidateExprRun.exists_ofCandidate`. -/
structure CandidateExprSemanticRootInput (env : VEnv) (Us : List Name)
    {source : Expr} (candidate : AddInductive.CandidateExpr source)
    (source' : VExpr) where
  contextRun : CandidateContextRun candidate.context
  venv_eq : contextRun.context.venv = env
  lparams_eq : contextRun.context.lparams = Us
  vlctx_eq : contextRun.context.vlctx = []
  source_tr : TrExprS env Us [] source source'
  whnfFuel : Nat
  whnfDepth : candidate.context.fuel.recDepth = whnfFuel + 1

/-- Run the retained checker interpreter on an exact root input.  The result is
`Nonempty` because the checker-selected Theory view is semantic evidence rather
than executable metadata; no choice operator or caller-supplied endpoint is
introduced by this boundary. -/
theorem CandidateExprSemanticRootInput.exists
    (input : CandidateExprSemanticRootInput env Us candidate source') :
    Nonempty (CandidateExprSemanticRootRun env Us candidate source') :=
  CandidateExprSemanticRootRun.exists_ofCandidate input.contextRun
    input.venv_eq input.lparams_eq input.vlctx_eq input.source_tr
    input.whnfFuel input.whnfDepth

/-- Interpret an identity-normalizing staged root at the strict Theory
translation already owned by its source input.  This keeps the endpoint
definitionally fixed without caller-supplied WHNF data or a
`Classical.choice` over the general semantic interpreter. -/
def CandidateExprSemanticRootInput.semanticOfIdentity
    {env : VEnv} {Us : List Name} {source : Expr}
    {candidate : AddInductive.CandidateExpr source} {source' : VExpr}
    (input : CandidateExprSemanticRootInput env Us candidate source')
    (identity : CandidateExprIdentity candidate.trace) :
    CandidateExprSemanticRootRun env Us candidate source' where
  contextRun := input.contextRun
  venv_eq := input.venv_eq
  lparams_eq := input.lparams_eq
  vlctx_eq := input.vlctx_eq
  source_tr := input.source_tr
  whnfFuel := input.whnfFuel
  whnfDepth := input.whnfDepth
  view := source'
  recursive := by
    have source_tr : input.contextRun.context.TrExprS source source' := by
      simpa only [VContext.TrExprS, input.venv_eq, input.lparams_eq,
        input.vlctx_eq] using input.source_tr
    obtain ⟨inferred, ⟨recursive⟩⟩ :=
      CandidateExprRun.exists_ofIdentity candidate.trace identity
        input.contextRun source' source_tr input.whnfFuel input.whnfDepth
    refine ⟨inferred, ?_⟩
    simpa only [input.venv_eq, input.lparams_eq, input.vlctx_eq] using
      recursive

/-- Interpret a staged root at the deterministic translation of its
checker-selected view.  For a projection-free view the recursive semantic
run's endpoint is pinned by strict-translation agreement
(`CandidateExprRun.view_tr_strict` plus `TrExprS.trExprS?_eq`), so the
retained `view` field is computed by `trExprS?` and the `Nonempty`
interpretation is transferred onto it; no choice operator selects data.
Unlike `semanticOfIdentity` this covers non-identity normalizations, at the
cost of the executable view-uniqueness certificate. -/
def CandidateExprSemanticRootInput.semanticOfUnique
    {env : VEnv} {Us : List Name} {source : Expr}
    {candidate : AddInductive.CandidateExpr source} {source' : VExpr}
    (input : CandidateExprSemanticRootInput env Us candidate source')
    (unique : CandidateExprTraceViewIsUnique candidate.trace) :
    CandidateExprSemanticRootRun env Us candidate source' :=
  match hview : trExprS? Us [] candidate.trace.view with
  | some view =>
    { contextRun := input.contextRun
      venv_eq := input.venv_eq
      lparams_eq := input.lparams_eq
      vlctx_eq := input.vlctx_eq
      source_tr := input.source_tr
      whnfFuel := input.whnfFuel
      whnfDepth := input.whnfDepth
      view := view
      recursive := by
        obtain ⟨w⟩ := input.exists
        obtain ⟨inferred, run⟩ := w.recursive
        cases Option.some.inj
          (((run.view_tr_strict unique).trExprS?_eq unique.view).symm.trans
            hview)
        exact ⟨inferred, run⟩ }
  | none =>
      absurd
        (show (trExprS? Us [] candidate.trace.view).isSome by
          obtain ⟨w⟩ := input.exists
          obtain ⟨inferred, run⟩ := w.recursive
          exact TrExprS.trExprS?_isSome
            ⟨w.view, run.view_tr_strict unique⟩ unique.view)
        (by simp [hview])

/-- One explicitly verified root stage shared by every candidate expression
interpreted before or after family insertion.

The stage owns the implementation/Theory context alignment once. Individual
source positions retain only their strict translation, fuel relation, and the
equality identifying the candidate's stored context with this stage. This is
the reusable boundary between staged environment validation and the retained
recursive candidate interpreter. -/
structure CandidateSemanticStage
    (candidateContext : AddInductive.Context) (env : VEnv) (Us : List Name)
    where
  contextRun : CandidateContextRun candidateContext
  venv_eq : contextRun.context.venv = env
  lparams_eq : contextRun.context.lparams = Us
  vlctx_eq : contextRun.context.vlctx = []

/-- Construct the shared root semantic stage directly from a verified
safety-indexed environment.  Candidate family and constructor traversals
start with an empty local context, so no fixture-specific record assembly is
needed at this boundary. -/
def CandidateSemanticStage.root
    {candidateContext : AddInductive.Context} {ves : VEnvs}
    (wf : ves.WF candidateContext.env)
    (lctx_eq : candidateContext.lctx = {})
    (namePrefix_ne : candidateContext.ngen.namePrefix ≠
      (({} : VState).ngen).namePrefix) :
    CandidateSemanticStage candidateContext
      (ves.venv candidateContext.safety) candidateContext.lparams where
  contextRun := CandidateContextRun.root wf lctx_eq namePrefix_ne
  venv_eq := rfl
  lparams_eq := rfl
  vlctx_eq := rfl

/-- The recursive candidate interpreter consumes the predecessor of the
checker recursion depth. -/
def _root_.Lean4Lean.AddInductive.Context.candidateWhnfFuel
    (context : AddInductive.Context) : Nat :=
  context.fuel.recDepth - 1

/-- A positive checker recursion depth is exactly one step beyond its
candidate WHNF budget. -/
theorem _root_.Lean4Lean.AddInductive.Context.candidateWhnfDepth
    (context : AddInductive.Context)
    (nonzero : context.fuel.recDepth ≠ 0) :
    context.fuel.recDepth = context.candidateWhnfFuel + 1 := by
  simp only [AddInductive.Context.candidateWhnfFuel]
  omega

/-- Source-position evidence interpreted in one shared candidate stage.

`context_eq` prevents a verified stage for another producer position from
being reused. The normalized Theory endpoint is deliberately absent: it is
selected only by `CandidateExprSemanticRootInput.exists`. -/
structure CandidateExprStagedInput
    {candidateContext : AddInductive.Context} {env : VEnv} {Us : List Name}
    (stage : CandidateSemanticStage candidateContext env Us)
    {source : Expr} (candidate : AddInductive.CandidateExpr source)
    (source' : VExpr) where
  context_eq : candidateContext = candidate.context
  source_tr : TrExprS env Us [] source source'
  whnfFuel : Nat
  whnfDepth : candidate.context.fuel.recDepth = whnfFuel + 1

/-- Specialize a shared verified stage to one exact source-indexed candidate
root. This is a pure dependent transport; it neither runs the checker nor
chooses the semantic view. -/
def CandidateExprStagedInput.rootInput
    {candidateContext : AddInductive.Context} {env : VEnv} {Us : List Name}
    {source : Expr} {candidate : AddInductive.CandidateExpr source}
    {source' : VExpr}
    {stage : CandidateSemanticStage candidateContext env Us}
    (input : CandidateExprStagedInput stage candidate source') :
    CandidateExprSemanticRootInput env Us candidate source' := by
  cases input.context_eq
  exact {
    contextRun := stage.contextRun
    venv_eq := stage.venv_eq
    lparams_eq := stage.lparams_eq
    vlctx_eq := stage.vlctx_eq
    source_tr := input.source_tr
    whnfFuel := input.whnfFuel
    whnfDepth := input.whnfDepth }

end TypeChecker

namespace AddInductive.FamilyTypeParameterComparisonTrace

/-- A later-family telescope preserves the already completed shared-parameter
array.  Fresh-parameter nodes are impossible once the family inventory is
nonempty; shared-parameter and index nodes leave the statistics unchanged. -/
theorem result_params_size_of_later
    (trace : FamilyTypeParameterComparisonTrace nparams stats context source
      i nindices fuel)
    (later : stats.indConsts.isEmpty = false)
    (paramsSize : stats.params.size = nparams) :
    trace.result.stats.params.size = nparams := by
  induction trace with
  | freshParameter stats context i nindices fuel name domain body view
      binderInfo isParameter firstFamily whnf tail ih =>
    rw [later] at firstFamily
    contradiction
  | sharedParameter stats context i nindices fuel name domain body
      parameterType view binderInfo isParameter laterFamily parameterTypeRun
      defeq whnf tail ih =>
    exact ih later paramsSize
  | index stats context i nindices fuel name domain body view binderInfo
      notParameter whnf tail ih =>
    exact ih later paramsSize
  | terminal =>
    exact paramsSize

/-- A later-family telescope preserves the literal shared-parameter array,
not merely its size. -/
theorem result_params_eq_of_later
    (trace : FamilyTypeParameterComparisonTrace nparams stats context source
      i nindices fuel)
    (later : stats.indConsts.isEmpty = false) :
    trace.result.stats.params = stats.params := by
  induction trace with
  | freshParameter stats context i nindices fuel name domain body view
      binderInfo isParameter firstFamily whnf tail ih =>
    rw [later] at firstFamily
    contradiction
  | sharedParameter stats context i nindices fuel name domain body
      parameterType view binderInfo isParameter laterFamily parameterTypeRun
      defeq whnf tail ih =>
    exact ih later
  | index stats context i nindices fuel name domain body view binderInfo
      notParameter whnf tail ih =>
    exact ih later
  | terminal =>
    rfl

end AddInductive.FamilyTypeParameterComparisonTrace

namespace AddInductive.FamilyParameterComparisonBlockTrace

/-- One exact source-order family node together with the dependent outer
trace that follows its completed telescope.  Unlike `FamilyTelescopePosition`,
this payload retains the continuation, so consumers can hand the terminal
context directly to the next family without reselecting it by counters. -/
structure FamilyContinuation (nparams : Nat)
    (indTypes : Array InductiveType) where
  dIdx : Nat
  stats : InductiveStats
  context : Context
  inBounds : dIdx < indTypes.size
  inferred : Expr
  source : Expr
  checkType : CandidateCheckTypeStep.Valid
    ⟨context, indTypes[dIdx].type, inferred⟩
  rootWhnf : CandidateWhnfStep.Valid
    ⟨context, indTypes[dIdx].type, source⟩
  telescope : FamilyTypeParameterComparisonTrace nparams stats context
    source 0 0 context.fuel.inductiveFuel
  sorted : Expr
  ensureSort : FamilyEnsureSortStep.Valid
    ⟨telescope.result.context, telescope.result.type, sorted⟩
  nextStats : InductiveStats
  tail : FamilyParameterComparisonBlockTrace nparams indTypes (dIdx + 1)
    nextStats telescope.result.context

/-- Stable later-family state owned by one exact outer continuation.  The
second pair is the induction invariant for the tail after this family. -/
structure FamilyContinuation.LaterInvariant
    (continuation : FamilyContinuation nparams indTypes) where
  current_indConsts_nonempty :
    continuation.stats.indConsts.isEmpty = false
  current_params_size : continuation.stats.params.size = nparams
  next_indConsts_nonempty :
    continuation.nextStats.indConsts.isEmpty = false
  next_params_size : continuation.nextStats.params.size = nparams

/-- Forget the retained outer tail while preserving the exact dependent
telescope position. -/
def FamilyContinuation.position
    (continuation : FamilyContinuation nparams indTypes) :
    FamilyTelescopePosition nparams :=
  ⟨continuation.stats, continuation.context, continuation.source, 0, 0,
    continuation.context.fuel.inductiveFuel, continuation.telescope⟩

/-- Select the first source family together with its exact remaining outer
trace. -/
def headContinuation? :
    FamilyParameterComparisonBlockTrace nparams indTypes dIdx stats context →
      Option (FamilyContinuation nparams indTypes)
  | .firstFamily dIdx stats context inBounds _ inferred root checkType
      rootWhnf telescope sorted ensureSort _ tail =>
      some {
        dIdx, stats, context, inBounds, inferred, source := root,
        checkType, rootWhnf, telescope, sorted, ensureSort,
        nextStats := _, tail }
  | .laterFamily dIdx stats context inBounds _ inferred root checkType
      rootWhnf telescope sorted ensureSort _ _ tail =>
      some {
        dIdx, stats, context, inBounds, inferred, source := root,
        checkType, rootWhnf, telescope, sorted, ensureSort,
        nextStats := _, tail }
  | .terminal .. => none

/-- A selected head continuation retains the outer suffix's exact source
index. -/
theorem headContinuation?_dIdx
    {trace : FamilyParameterComparisonBlockTrace nparams indTypes dIdx stats
      context}
    {continuation : FamilyContinuation nparams indTypes}
    (selected : trace.headContinuation? = some continuation) :
    continuation.dIdx = dIdx := by
  cases trace with
  | firstFamily dIdx stats context inBounds closed inferred root checkType
      rootWhnf telescope sorted ensureSort isFirst tail =>
    simp only [headContinuation?] at selected
    have selected' := Option.some.inj selected
    exact (congrArg FamilyContinuation.dIdx selected').symm
  | laterFamily dIdx stats context inBounds closed inferred root checkType
      rootWhnf telescope sorted ensureSort isLater resultLevelCompatible tail =>
    simp only [headContinuation?] at selected
    have selected' := Option.some.inj selected
    exact (congrArg FamilyContinuation.dIdx selected').symm
  | terminal =>
    simp only [headContinuation?] at selected
    contradiction

/-- A selected head continuation retains the exact reader context at which
the outer suffix begins. -/
theorem headContinuation?_context
    {trace : FamilyParameterComparisonBlockTrace nparams indTypes dIdx stats
      context}
    {continuation : FamilyContinuation nparams indTypes}
    (selected : trace.headContinuation? = some continuation) :
    continuation.context = context := by
  cases trace with
  | firstFamily dIdx stats context inBounds closed inferred root checkType
      rootWhnf telescope sorted ensureSort isFirst tail =>
    simp only [headContinuation?] at selected
    have selected' := Option.some.inj selected
    exact (congrArg FamilyContinuation.context selected').symm
  | laterFamily dIdx stats context inBounds closed inferred root checkType
      rootWhnf telescope sorted ensureSort isLater resultLevelCompatible tail =>
    simp only [headContinuation?] at selected
    have selected' := Option.some.inj selected
    exact (congrArg FamilyContinuation.context selected').symm
  | terminal =>
    simp only [headContinuation?] at selected
    contradiction

/-- A selected head continuation retains the exact statistics at which the
outer suffix begins. -/
theorem headContinuation?_stats
    {trace : FamilyParameterComparisonBlockTrace nparams indTypes dIdx stats
      context}
    {continuation : FamilyContinuation nparams indTypes}
    (selected : trace.headContinuation? = some continuation) :
    continuation.stats = stats := by
  cases trace with
  | firstFamily dIdx stats context inBounds closed inferred root checkType
      rootWhnf telescope sorted ensureSort isFirst tail =>
    simp only [headContinuation?] at selected
    have selected' := Option.some.inj selected
    exact (congrArg FamilyContinuation.stats selected').symm
  | laterFamily dIdx stats context inBounds closed inferred root checkType
      rootWhnf telescope sorted ensureSort isLater resultLevelCompatible tail =>
    simp only [headContinuation?] at selected
    have selected' := Option.some.inj selected
    exact (congrArg FamilyContinuation.stats selected').symm
  | terminal =>
    simp only [headContinuation?] at selected
    contradiction

/-- Selecting a later-family head preserves both stable validation counters
for the exact outer tail. -/
theorem headContinuation?_laterInvariant
    {trace : FamilyParameterComparisonBlockTrace nparams indTypes dIdx stats
      context}
    {continuation : FamilyContinuation nparams indTypes}
    (selected : trace.headContinuation? = some continuation)
    (later : continuation.stats.indConsts.isEmpty = false)
    (paramsSize : continuation.stats.params.size = nparams) :
    continuation.LaterInvariant := by
  cases trace with
  | firstFamily dIdx stats context inBounds closed inferred root checkType
      rootWhnf telescope sorted ensureSort isFirst tail =>
    simp only [headContinuation?] at selected
    have selected' := Option.some.inj selected
    cases selected'
    have first : stats.indConsts.isEmpty = true := by
      rw [← telescope.result_indConsts_eq]
      exact isFirst
    rw [first] at later
    contradiction
  | laterFamily dIdx stats context inBounds closed inferred root checkType
      rootWhnf telescope sorted ensureSort isLater resultLevelCompatible tail =>
    simp only [headContinuation?] at selected
    have selected' := Option.some.inj selected
    cases selected'
    refine ⟨later, paramsSize, ?_, ?_⟩
    · simp
    · exact telescope.result_params_size_of_later later paramsSize
  | terminal =>
    simp only [headContinuation?] at selected
    contradiction

/-- Completing a selected later-family telescope produces the genuine local
inventory expected by its dependent outer tail.  The block update changes
family statistics but preserves the completed parameter array. -/
theorem headContinuation?_nextLocalState
    {trace : FamilyParameterComparisonBlockTrace nparams indTypes dIdx stats
      context}
    {continuation : FamilyContinuation nparams indTypes}
    (selected : trace.headContinuation? = some continuation)
    (localState : TypeChecker.FamilyParameterLocalState continuation.stats
      continuation.context)
    (later : continuation.stats.indConsts.isEmpty = false)
    (paramsSize : continuation.stats.params.size = nparams) :
    TypeChecker.FamilyParameterLocalState continuation.nextStats
      continuation.telescope.result.context := by
  cases trace with
  | firstFamily dIdx stats context inBounds closed inferred root checkType
      rootWhnf telescope sorted ensureSort isFirst tail =>
    simp only [headContinuation?] at selected
    have selected' := Option.some.inj selected
    cases selected'
    have first : stats.indConsts.isEmpty = true := by
      rw [← telescope.result_indConsts_eq]
      exact isFirst
    rw [first] at later
    contradiction
  | laterFamily dIdx stats context inBounds closed inferred root checkType
      rootWhnf telescope sorted ensureSort isLater resultLevelCompatible tail =>
    simp only [headContinuation?] at selected
    have selected' := Option.some.inj selected
    cases selected'
    obtain ⟨terminalLocal, _⟩ :=
      TypeChecker.familyTypeParameterComparison_localResult_of_later
        telescope later paramsSize localState
    exact ⟨terminalLocal.localContext, terminalLocal.parameters⟩
  | terminal =>
    simp only [headContinuation?] at selected
    contradiction

/-- The dependent outer tail after a selected later family retains the
literal shared-parameter array from that family's input statistics. -/
theorem headContinuation?_nextParams_eq
    {trace : FamilyParameterComparisonBlockTrace nparams indTypes dIdx stats
      context}
    {continuation : FamilyContinuation nparams indTypes}
    (selected : trace.headContinuation? = some continuation)
    (later : continuation.stats.indConsts.isEmpty = false) :
    continuation.nextStats.params = continuation.stats.params := by
  cases trace with
  | firstFamily dIdx stats context inBounds closed inferred root checkType
      rootWhnf telescope sorted ensureSort isFirst tail =>
    simp only [headContinuation?] at selected
    have selected' := Option.some.inj selected
    cases selected'
    have first : stats.indConsts.isEmpty = true := by
      rw [← telescope.result_indConsts_eq]
      exact isFirst
    rw [first] at later
    contradiction
  | laterFamily dIdx stats context inBounds closed inferred root checkType
      rootWhnf telescope sorted ensureSort isLater resultLevelCompatible tail =>
    simp only [headContinuation?] at selected
    have selected' := Option.some.inj selected
    cases selected'
    exact telescope.result_params_eq_of_later later
  | terminal =>
    simp only [headContinuation?] at selected
    contradiction

/-- Select the second source family together with the exact outer trace that
starts after its telescope. -/
def secondContinuation?
    (trace : FamilyParameterComparisonBlockTrace nparams indTypes dIdx stats
      context) : Option (FamilyContinuation nparams indTypes) :=
  match trace.headContinuation? with
  | some first => first.tail.headContinuation?
  | none => none

/-- A successful second-position selection exposes its exact first
continuation and the head selection on that continuation's dependent tail. -/
theorem exists_predecessor_of_secondContinuation?
    {trace : FamilyParameterComparisonBlockTrace nparams indTypes dIdx stats
      context}
    {continuation : FamilyContinuation nparams indTypes}
    (selected : trace.secondContinuation? = some continuation) :
    ∃ first, trace.headContinuation? = some first ∧
      first.tail.headContinuation? = some continuation := by
  unfold secondContinuation? at selected
  cases firstEq : trace.headContinuation? with
  | none => simp [firstEq] at selected
  | some first =>
    simp only [firstEq] at selected
    exact ⟨first, rfl, selected⟩

/-- The continuation selected at the second source position retains that
exact outer index.  This is the counter fact needed to identify the suffix
after its telescope with the source list after two elements. -/
theorem secondContinuation?_dIdx
    {trace : FamilyParameterComparisonBlockTrace nparams indTypes dIdx stats
      context}
    {continuation : FamilyContinuation nparams indTypes}
    (selected : trace.secondContinuation? = some continuation) :
    continuation.dIdx = dIdx + 1 := by
  cases trace with
  | firstFamily dIdx stats context inBounds closed inferred root checkType
      rootWhnf telescope sorted ensureSort isFirst tail =>
    cases tail
    case firstFamily =>
      simp only [secondContinuation?, headContinuation?] at selected
      have selected' := Option.some.inj selected
      exact (congrArg FamilyContinuation.dIdx selected').symm
    case laterFamily =>
      simp only [secondContinuation?, headContinuation?] at selected
      have selected' := Option.some.inj selected
      exact (congrArg FamilyContinuation.dIdx selected').symm
    case terminal =>
      simp only [secondContinuation?, headContinuation?] at selected
      contradiction
  | laterFamily dIdx stats context inBounds closed inferred root checkType
      rootWhnf telescope sorted ensureSort isLater resultLevelCompatible tail =>
    cases tail
    case firstFamily =>
      simp only [secondContinuation?, headContinuation?] at selected
      have selected' := Option.some.inj selected
      exact (congrArg FamilyContinuation.dIdx selected').symm
    case laterFamily =>
      simp only [secondContinuation?, headContinuation?] at selected
      have selected' := Option.some.inj selected
      exact (congrArg FamilyContinuation.dIdx selected').symm
    case terminal =>
      simp only [secondContinuation?, headContinuation?] at selected
      contradiction
  | terminal =>
    simp_all [secondContinuation?, headContinuation?]

/-- Forgetting the second continuation produces exactly the existing second
telescope selector. -/
theorem secondTelescope?_eq_map_position
    (trace : FamilyParameterComparisonBlockTrace nparams indTypes dIdx stats
      context) :
    trace.secondTelescope? =
      trace.secondContinuation?.map FamilyContinuation.position := by
  cases trace with
  | firstFamily dIdx stats context inBounds closed inferred root checkType
      rootWhnf telescope sorted ensureSort isFirst tail =>
    cases tail <;> rfl
  | laterFamily dIdx stats context inBounds closed inferred root checkType
      rootWhnf telescope sorted ensureSort isLater resultLevelCompatible tail =>
    cases tail <;> rfl
  | terminal => rfl

/-- A selected continuation forgets to the same selected telescope position. -/
theorem secondContinuation?_position
    {trace : FamilyParameterComparisonBlockTrace nparams indTypes dIdx stats
      context}
    {continuation : FamilyContinuation nparams indTypes}
    (selected : trace.secondContinuation? = some continuation) :
    trace.secondTelescope? = some continuation.position := by
  rw [trace.secondTelescope?_eq_map_position, selected]
  rfl

/-- Recover the exact dependent continuation from any successful selection of
the second telescope. -/
theorem exists_secondContinuation_of_secondTelescope
    {trace : FamilyParameterComparisonBlockTrace nparams indTypes dIdx stats
      context}
    {position : FamilyTelescopePosition nparams}
    (selected : trace.secondTelescope? = some position) :
    ∃ continuation, trace.secondContinuation? = some continuation ∧
      continuation.position = position := by
  rw [trace.secondTelescope?_eq_map_position] at selected
  cases continuationEq : trace.secondContinuation? with
  | none => simp [continuationEq] at selected
  | some continuation =>
      refine ⟨continuation, rfl, ?_⟩
      rw [continuationEq] at selected
      exact Option.some.inj selected

end AddInductive.FamilyParameterComparisonBlockTrace

namespace AddInductive.CandidateExprTrace

/-- A source-indexed path to one exact annotation node on a candidate's main
Pi spine.  The path follows the recursively retained body candidate; its
zero constructor owns the annotation provenance at the selected node. -/
inductive AnnotationAt :
    {candidateContext : AddInductive.Context} → {source : Expr} →
      (trace : AddInductive.CandidateExprTrace candidateContext source) →
      Nat → Type where
  | zero
      (annotation_match : annotations.Matches) :
      AnnotationAt
        (.forallE context source inferred name domain body binderInfo fresh
          annotations annotationsEq checked normalized domainCandidate
          bodyCandidate) 0
  | succ
      (bodyCandidate : AddInductive.CandidateExprTrace
        (context.pushLocalDecl name binderInfo annotations.consumed)
        (body.instantiate1 context.freshExpr))
      (tail : @AnnotationAt
        (context.pushLocalDecl name binderInfo annotations.consumed)
        (body.instantiate1 context.freshExpr) bodyCandidate n) :
      AnnotationAt
        (.forallE context source inferred name domain body binderInfo fresh
          annotations annotationsEq checked normalized domainCandidate
          bodyCandidate) (n + 1)

/-- Every in-bounds main-spine position has the exact annotation provenance
retained by the candidate producer. -/
theorem annotationAt
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    (annotations : trace.validationAnnotations)
    (count_lt : count < trace.spineLength) :
    Nonempty (AnnotationAt trace count) := by
  induction trace generalizing count with
  | terminal =>
      simp [AddInductive.CandidateExprTrace.spineLength] at count_lt
  | forallE context source inferred name domain body binderInfo fresh
      annotationsNode annotationsEq checked normalized domainCandidate
      bodyCandidate domainIH bodyIH =>
    rcases annotations with ⟨annotationMatch, tailAnnotations⟩
    cases count with
    | zero => exact ⟨.zero annotationMatch⟩
    | succ count =>
        obtain ⟨tailAt⟩ := bodyIH tailAnnotations (by
          simpa [AddInductive.CandidateExprTrace.spineLength] using count_lt)
        exact ⟨.succ bodyCandidate tailAt⟩

/-- A source-indexed position on a candidate's main Pi spine, including the
terminal position just after its final binder.  Unlike `AnnotationAt`, the
zero constructor does not require a Pi node, so a parameter boundary can name
a family with no indices. -/
inductive MainSpineAt :
    {candidateContext : AddInductive.Context} → {source : Expr} →
      (trace : AddInductive.CandidateExprTrace candidateContext source) →
      Nat → Type where
  | zero
      (trace : AddInductive.CandidateExprTrace candidateContext source) :
      MainSpineAt trace 0
  | succ
      (bodyCandidate : AddInductive.CandidateExprTrace
        (context.pushLocalDecl name binderInfo annotations.consumed)
        (body.instantiate1 context.freshExpr))
      (tail : MainSpineAt bodyCandidate n) :
      MainSpineAt
        (.forallE context source inferred name domain body binderInfo fresh
          annotations annotationsEq checked normalized domainCandidate
          bodyCandidate) (n + 1)

/-- Every main-spine position through the terminal endpoint has an exact
source-indexed path in the candidate tree. -/
theorem mainSpineAt
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    (count_le : count ≤ trace.spineLength) :
    Nonempty (MainSpineAt trace count) := by
  induction trace generalizing count with
  | terminal =>
      simp only [AddInductive.CandidateExprTrace.spineLength] at count_le
      have count_eq : count = 0 := Nat.eq_zero_of_le_zero count_le
      subst count
      exact ⟨.zero _⟩
  | forallE context source inferred name domain body binderInfo fresh
      annotations annotationsEq checked normalized domainCandidate
      bodyCandidate domainIH bodyIH =>
    cases count with
    | zero => exact ⟨.zero _⟩
    | succ count =>
        obtain ⟨tailAt⟩ := bodyIH (by
          simpa [AddInductive.CandidateExprTrace.spineLength] using count_le)
        exact ⟨.succ bodyCandidate tailAt⟩

/-- The dependent candidate trace selected by a terminal-inclusive main-spine
position. -/
structure MainSpinePosition where
  candidateContext : AddInductive.Context
  source : Expr
  trace : AddInductive.CandidateExprTrace candidateContext source

/-- Forget the path prefix while retaining its exact selected candidate
suffix. -/
def MainSpineAt.position :
    {candidateContext : AddInductive.Context} → {source : Expr} →
      {trace : AddInductive.CandidateExprTrace candidateContext source} →
      {count : Nat} → MainSpineAt trace count → MainSpinePosition
  | _, _, _, _, .zero trace => ⟨_, _, trace⟩
  | _, _, _, _, .succ _ tail => tail.position

/-- Forget the annotation witness while retaining the same exact main-spine
path. -/
def AnnotationAt.toMainSpineAt :
    {candidateContext : AddInductive.Context} → {source : Expr} →
      {trace : AddInductive.CandidateExprTrace candidateContext source} →
      {count : Nat} → AnnotationAt trace count → MainSpineAt trace count
  | _, _, _, _, .zero _ => .zero _
  | _, _, _, _, .succ bodyCandidate tail =>
      .succ bodyCandidate tail.toMainSpineAt

/-- A positive terminal-inclusive position still certifies that the current
candidate source is a genuine stored Pi. -/
theorem MainSpineAt.traceSource_isForall
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {count : Nat}
    (position : trace.MainSpineAt count)
    (positive : 0 < count)
    (aligned : trace.storedSpine = true) :
    source.isForall = true := by
  cases position with
  | zero => omega
  | succ bodyCandidate tail =>
      simp only [AddInductive.CandidateExprTrace.storedSpine,
        Bool.and_eq_true] at aligned
      exact AddInductive.CandidateWhnfStep.isForall_of_structuralEq_forall
        aligned.1

/-- The exact kernel Pi exposed at a selected annotation position. -/
def AnnotationAt.root :
    {candidateContext : AddInductive.Context} → {source : Expr} →
      {trace : AddInductive.CandidateExprTrace candidateContext source} →
      {count : Nat} → AnnotationAt trace count → Expr
  | _, _, _, _, .zero (name := name) (domain := domain) (body := body)
      (binderInfo := binderInfo) _ =>
    .forallE name domain body binderInfo
  | _, _, _, _, .succ _ tail => tail.root

/-- Raw kernel domain at the selected annotation position. -/
def AnnotationAt.domain :
    {candidateContext : AddInductive.Context} → {source : Expr} →
      {trace : AddInductive.CandidateExprTrace candidateContext source} →
      {count : Nat} → AnnotationAt trace count → Expr
  | _, _, _, _, .zero (domain := domain) _ => domain
  | _, _, _, _, .succ _ tail => tail.domain

/-- Candidate-selected annotation-consumed kernel domain at the selected
position. -/
def AnnotationAt.consumed :
    {candidateContext : AddInductive.Context} → {source : Expr} →
      {trace : AddInductive.CandidateExprTrace candidateContext source} →
      {count : Nat} → AnnotationAt trace count → Expr
  | _, _, _, _, .zero (annotations := annotations) _ => annotations.consumed
  | _, _, _, _, .succ _ tail => tail.consumed

/-- The selected candidate annotation is exactly the transparent peeling
used by ordinary family validation. -/
theorem AnnotationAt.consumed_eq
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {count : Nat}
    (position : AnnotationAt trace count) :
    position.consumed = AddInductive.consumeTypeAnnotations position.domain := by
  cases position with
  | zero annotationMatch => exact annotationMatch
  | succ bodyCandidate tail => exact tail.consumed_eq

/-- Any candidate trace carrying an annotation position starts at a genuine Pi
source once the stored-spine gate is known. -/
theorem AnnotationAt.traceSource_isForall
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    (position : trace.AnnotationAt count)
    (aligned : trace.storedSpine = true) :
    source.isForall = true := by
  cases position <;>
    simp only [AddInductive.CandidateExprTrace.storedSpine,
      Bool.and_eq_true] at aligned <;>
    exact AddInductive.CandidateWhnfStep.isForall_of_structuralEq_forall
      aligned.1

end AddInductive.CandidateExprTrace

namespace AddInductive.FamilyTypeParameterComparisonTrace.SharedPrefixPath

/-- Synchronize an exact later-family shared-parameter path with the same
candidate's producer-owned annotation position.

Both retained WHNF observations see the identical instantiated kernel body.
Since the generation gate says that body is already a Pi, WHNF returns it
literally in both reader contexts.  Recursing over the actual path therefore
identifies the validator suffix root with the candidate annotation root,
without a determinism or endpoint-uniqueness premise. -/
theorem annotationAt_root_eq
    {candidateContext : AddInductive.Context} {candidateSource : Expr}
    {candidate : AddInductive.CandidateExprTrace candidateContext
      candidateSource}
    {stats : AddInductive.InductiveStats}
    {context : AddInductive.Context} {source : Expr}
    {i nindices fuel : Nat}
    {outer : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
      context source i nindices fuel}
    {suffixSource : Expr} {suffixFuel : Nat}
    {suffix : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
      context suffixSource nparams nindices suffixFuel}
    {parameters : List Expr}
    (path : SharedPrefixPath nparams outer suffix parameters)
    (parameters_eq : parameters = candidate.parameterList count)
    (position : candidate.AnnotationAt count)
    (aligned : candidate.storedSpine = true)
    (source_eq : source = candidate.rootWhnf)
    (recursionFuel : Nat)
    (contextDepth : context.fuel.recDepth = recursionFuel + 1)
    (candidateDepth : candidateContext.fuel.recDepth = recursionFuel + 1) :
    suffixSource = position.root := by
  induction candidate generalizing count stats context source i nindices fuel
      outer suffixSource suffixFuel suffix parameters with
  | terminal => cases position
  | forallE candidateContext candidateSource inferred candidateName
      candidateDomain candidateBody candidateBinderInfo candidateFresh
      candidateAnnotations candidateAnnotationsEq candidateChecked
      candidateNormalized candidateDomainCandidate candidateBodyCandidate
      domainIH bodyIH =>
    simp only [AddInductive.CandidateExprTrace.storedSpine,
      Bool.and_eq_true] at aligned
    obtain ⟨candidateSourceEq, bodyAligned⟩ := aligned
    cases count with
    | zero =>
        cases position with
        | zero annotationMatch =>
            cases path with
            | done trace => exact source_eq
            | shared =>
                simp [AddInductive.CandidateExprTrace.parameterList]
                  at parameters_eq
    | succ count =>
        cases position with
        | succ _ position =>
            cases path with
            | done trace =>
                simp [AddInductive.CandidateExprTrace.parameterList]
                  at parameters_eq
            | @shared validatorView validatorI validatorNindices
                validatorFuel validatorSuffixSource validatorSuffixFuel
                parameterType validatorDomain validatorName validatorBody
                validatorBinderInfo tail suffix parameters isParameter
                laterFamily parameterTypeRun defeq whnf path =>
                simp only [AddInductive.CandidateExprTrace.parameterList,
                  List.cons.injEq] at parameters_eq
                have candidateIsForall :
                    (candidateBody.instantiate1
                      candidateContext.freshExpr).isForall = true :=
                  position.traceSource_isForall bodyAligned
                have candidateBodyEq :=
                  AddInductive.CandidateWhnfStep.result_eq_of_source_isForall
                    candidateBodyCandidate.rootWhnf_valid recursionFuel (by
                      simpa [AddInductive.Context.pushLocalDecl] using
                        candidateDepth) candidateIsForall
                have sourceParts := source_eq
                simp only [AddInductive.CandidateExprTrace.rootWhnf,
                  Expr.forallE.injEq] at sourceParts
                rcases sourceParts with
                  ⟨nameEq, domainEq, bodyEq, binderInfoEq⟩
                have parameterEq : stats.params[i]! =
                    candidateContext.freshExpr := parameters_eq.1
                have validatorSourceIsForall :
                    (validatorBody.instantiate1
                      stats.params[i]!).isForall = true := by
                  rw [parameterEq, bodyEq]
                  exact candidateIsForall
                have validatorBodyEq :=
                  AddInductive.CandidateWhnfStep.result_eq_of_source_isForall
                    whnf recursionFuel contextDepth validatorSourceIsForall
                apply bodyIH path parameters_eq.2 position bodyAligned
                · exact validatorBodyEq.trans (by
                    rw [parameterEq, bodyEq]
                    exact candidateBodyEq.symm)
                · exact contextDepth
                · simpa [AddInductive.Context.pushLocalDecl] using
                    candidateDepth

end AddInductive.FamilyTypeParameterComparisonTrace.SharedPrefixPath

/--
info: 'Lean4Lean.AddInductive.CandidateWhnfStep.isForall_of_structuralEq_forall' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.eqv_eq,
 Level.instLawfulBEqLevel]
-/
#guard_msgs in
#print axioms AddInductive.CandidateWhnfStep.isForall_of_structuralEq_forall

/--
info: 'Lean4Lean.AddInductive.CandidateWhnfStep.result_eq_of_source_isForall' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms AddInductive.CandidateWhnfStep.result_eq_of_source_isForall

/--
info: 'Lean4Lean.AddInductive.CandidateExprTrace.AnnotationAt.traceSource_isForall' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.eqv_eq,
 Level.instLawfulBEqLevel]
-/
#guard_msgs in
#print axioms AddInductive.CandidateExprTrace.AnnotationAt.traceSource_isForall

/--
info: 'Lean4Lean.AddInductive.FamilyTypeParameterComparisonTrace.SharedPrefixPath.annotationAt_root_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.eqv_eq,
 Level.instLawfulBEqLevel]
-/
#guard_msgs in
#print axioms
  AddInductive.FamilyTypeParameterComparisonTrace.SharedPrefixPath.annotationAt_root_eq

/-- A verified local context containing exactly producer-allocated
free-variable assumptions: no bound-variable entries and no hidden lets. -/
inductive VLCtx.FVarLamOnly : VLCtx → Prop where
  | nil : FVarLamOnly []
  | cons : FVarLamOnly Δ →
      FVarLamOnly ((some (fv, deps), .vlam type) :: Δ)

/-- A verified local context containing only bound assumptions.  This is the
common alpha-normal form of two `FVarLamOnly` contexts whose producer-owned
free-variable identifiers may differ. -/
inductive VLCtx.BVarLamOnly : VLCtx → Prop where
  | nil : BVarLamOnly []
  | cons : BVarLamOnly Δ → BVarLamOnly ((none, .vlam type) :: Δ)

/-- Forget only the kernel free-variable metadata of a verified context.
Theory declarations and their de Bruijn positions remain unchanged. -/
def VLCtx.bvarize : VLCtx → VLCtx
  | [] => []
  | (_, declaration) :: Δ =>
      (none, declaration) :: VLCtx.bvarize Δ

/-- Abstract a source-ordered sequence of kernel free variables, starting at
the supplied loose-bound-variable depth. -/
def _root_.Lean.Expr.abstractFVarsAux :
    Nat → List Lean.FVarId → Lean.Expr → Lean.Expr
  | _, [], expression => expression
  | depth, fv :: fvs, expression =>
      Lean.Expr.abstractFVarsAux (depth + 1) fvs
        (Lean.Expr.abstract1 fv expression depth)

/-- Abstract every free-variable slot represented by a verified context.
The head slot becomes bound variable zero and older slots follow beneath it. -/
def _root_.Lean.Expr.abstractFVars (Δ : VLCtx)
    (expression : Lean.Expr) : Lean.Expr :=
  Lean.Expr.abstractFVarsAux 0 Δ.fvars expression

theorem _root_.Lean.Expr.abstractFVarsAux_forallE
    (depth : Nat) (fvars : List Lean.FVarId)
    (name : Name) (domain body : Lean.Expr)
    (binderInfo : Lean.BinderInfo) :
    Lean.Expr.abstractFVarsAux depth fvars
        (.forallE name domain body binderInfo) =
      .forallE name
        (Lean.Expr.abstractFVarsAux depth fvars domain)
        (Lean.Expr.abstractFVarsAux (depth + 1) fvars body) binderInfo := by
  induction fvars generalizing depth domain body with
  | nil => rfl
  | cons fv fvars ih =>
      simp only [Lean.Expr.abstractFVarsAux, Lean.Expr.abstract1]
      rw [ih]

theorem _root_.Lean.Expr.abstractFVars_forallE
    (Δ : VLCtx) (name : Name) (domain body : Lean.Expr)
    (binderInfo : Lean.BinderInfo) :
    Lean.Expr.abstractFVars Δ (.forallE name domain body binderInfo) =
      .forallE name (Lean.Expr.abstractFVars Δ domain)
        (Lean.Expr.abstractFVarsAux 1 Δ.fvars body) binderInfo := by
  exact Lean.Expr.abstractFVarsAux_forallE 0 Δ.fvars name domain body
    binderInfo

/-- Abstracting free variables preserves the outer Pi/non-Pi shape. -/
theorem _root_.Lean.Expr.abstract1_isForall
    (fv : Lean.FVarId) (expression : Lean.Expr) (depth : Nat) :
    (expression.abstract1 fv depth).isForall = expression.isForall := by
  cases expression <;> try rfl
  case fvar =>
    simp only [Lean.Expr.abstract1]
    split <;> rfl

theorem _root_.Lean.Expr.abstractFVarsAux_isForall
    (depth : Nat) (fvars : List Lean.FVarId) (expression : Lean.Expr) :
    (Lean.Expr.abstractFVarsAux depth fvars expression).isForall =
      expression.isForall := by
  induction fvars generalizing depth expression with
  | nil => rfl
  | cons fv fvars ih =>
      simp only [Lean.Expr.abstractFVarsAux, ih,
        Lean.Expr.abstract1_isForall]

theorem _root_.Lean.Expr.abstractFVars_isForall
    (Δ : VLCtx) (expression : Lean.Expr) :
    (Lean.Expr.abstractFVars Δ expression).isForall = expression.isForall := by
  exact Lean.Expr.abstractFVarsAux_isForall 0 Δ.fvars expression

/-- Adding a fresh free-assumption slot and immediately instantiating it is
the positional successor step of alpha normalization. -/
theorem _root_.Lean.Expr.abstractFVars_cons_instantiate1
    {Δ : VLCtx} {fv : Lean.FVarId} {deps : List Lean.FVarId}
    {declaration : VLocalDecl} {body : Lean.Expr}
    (avoid : body.FVarsIn (· ≠ fv)) :
    Lean.Expr.abstractFVars ((some (fv, deps), declaration) :: Δ)
        (body.instantiate1 (.fvar fv)) =
      Lean.Expr.abstractFVarsAux 1 Δ.fvars body := by
  simp only [Lean.Expr.abstractFVars, Lean.Expr.instantiate1_eq]
  change Lean.Expr.abstractFVarsAux 0 (fv :: Δ.fvars)
      (body.instantiate1' (.fvar fv)) = _
  rw [Lean.Expr.abstractFVarsAux]
  rw [avoid.abstract_instantiate1 (k := 0)]

/-- Transparent annotation peeling commutes with abstracting one kernel free
variable. -/
theorem AddInductive.consumeTypeAnnotations_abstract1
    (source : Lean.Expr) (fv : Lean.FVarId) (depth : Nat) :
    AddInductive.consumeTypeAnnotations
        (Lean.Expr.abstract1 fv source depth) =
      Lean.Expr.abstract1 fv
        (AddInductive.consumeTypeAnnotations source) depth := by
  fun_induction AddInductive.consumeTypeAnnotations source <;>
    simp_all [AddInductive.consumeTypeAnnotations, Lean.Expr.abstract1]
  case case7 source _ _ =>
    cases source <;>
      simp_all [AddInductive.consumeTypeAnnotations, Lean.Expr.abstract1]
    case fvar =>
      split <;> unfold AddInductive.consumeTypeAnnotations <;> rfl
    case app =>
      rename_i fn arg hNotApp hNotConst
      cases fn <;>
        simp_all [AddInductive.consumeTypeAnnotations, Lean.Expr.abstract1]
      case app fn type =>
        cases fn <;>
          simp_all [AddInductive.consumeTypeAnnotations,
            Lean.Expr.abstract1]
        case fvar =>
          split <;> unfold AddInductive.consumeTypeAnnotations <;> rfl
      all_goals
        split <;> unfold AddInductive.consumeTypeAnnotations <;> rfl

theorem AddInductive.consumeTypeAnnotations_abstractFVarsAux
    (depth : Nat) (fvars : List Lean.FVarId) (source : Lean.Expr) :
    AddInductive.consumeTypeAnnotations
        (Lean.Expr.abstractFVarsAux depth fvars source) =
      Lean.Expr.abstractFVarsAux depth fvars
        (AddInductive.consumeTypeAnnotations source) := by
  induction fvars generalizing depth source with
  | nil => rfl
  | cons fv fvars ih =>
      simp only [Lean.Expr.abstractFVarsAux, ih,
        AddInductive.consumeTypeAnnotations_abstract1]

theorem AddInductive.consumeTypeAnnotations_abstractFVars
    (Δ : VLCtx) (source : Lean.Expr) :
    AddInductive.consumeTypeAnnotations
        (Lean.Expr.abstractFVars Δ source) =
      Lean.Expr.abstractFVars Δ
        (AddInductive.consumeTypeAnnotations source) := by
  exact AddInductive.consumeTypeAnnotations_abstractFVarsAux
    0 Δ.fvars source

theorem VLCtx.BVarLamOnly.snoc
    {pre : VLCtx} {type : VExpr}
    (shape : pre.BVarLamOnly) :
    (pre ++ [(none, VLocalDecl.vlam type)]).BVarLamOnly := by
  induction shape with
  | nil => exact .cons .nil
  | cons shape ih => exact .cons ih

private theorem VLCtx.Abstract.underBVarLams
    {pre base : VLCtx} {fv : Lean.FVarId}
    {deps : List Lean.FVarId} {type : VExpr}
    (shape : pre.BVarLamOnly) :
    VLCtx.Abstract base fv (VLocalDecl.vlam type) pre.length pre.length
      (pre ++ (some (fv, deps), VLocalDecl.vlam type) :: base)
      (pre ++ (none, VLocalDecl.vlam type) :: base) := by
  induction shape with
  | nil => exact .zero
  | @cons preTail preType shape ih =>
      simpa only [List.length_cons, List.cons_append,
        VLocalDecl.depth, Nat.add_comm] using
        VLCtx.Abstract.succ (d := VLocalDecl.vlam preType) ih

private theorem TrExprS.abstractFVarsAux
    {env : VEnv} {Us : List Name}
    {pre suffix : VLCtx} {source : Lean.Expr} {target : VExpr}
    (preShape : pre.BVarLamOnly)
    (suffixShape : suffix.FVarLamOnly)
    (run : TrExprS env Us (pre ++ suffix) source target) :
    TrExprS env Us (pre ++ VLCtx.bvarize suffix)
      (Lean.Expr.abstractFVarsAux pre.length suffix.fvars source) target := by
  induction suffixShape generalizing pre source with
  | nil =>
      simpa [VLCtx.bvarize, Lean.Expr.abstractFVarsAux] using run
  | @cons suffix fv deps type suffixShape ih =>
      have abstracted := run.abstract
        (VLCtx.Abstract.underBVarLams preShape)
      have tail := ih (preShape.snoc (type := type)) (by
        simpa only [List.append_assoc, List.singleton_append] using
          abstracted)
      simpa [VLCtx.bvarize, VLCtx.fvars, Lean.Expr.abstractFVarsAux,
        List.length_append] using tail

/-- Strict translation is invariant under alpha-normalizing every producer
free-variable slot into its corresponding bound-variable position. -/
theorem TrExprS.abstractFVars
    {env : VEnv} {Us : List Name}
    {Δ : VLCtx} {source : Lean.Expr} {target : VExpr}
    (shape : Δ.FVarLamOnly)
    (run : TrExprS env Us Δ source target) :
    TrExprS env Us (VLCtx.bvarize Δ)
      (Lean.Expr.abstractFVars Δ source) target := by
  simpa [Lean.Expr.abstractFVars] using
    TrExprS.abstractFVarsAux VLCtx.BVarLamOnly.nil shape run

theorem VLCtx.bvarize_toCtx (Δ : VLCtx) :
    (VLCtx.bvarize Δ).toCtx = Δ.toCtx := by
  induction Δ with
  | nil => rfl
  | cons head Δ ih =>
      rcases head with ⟨metadata, declaration⟩
      cases declaration <;>
        simp_all [VLCtx.bvarize, VLCtx.toCtx]

/-- Pointwise definitional equality of free-assumption contexts, allowing
the kernel free-variable identifiers and dependency metadata to differ. -/
inductive VLCtx.FVarAlpha (env : VEnv) (U : Nat) :
    VLCtx → VLCtx → Prop
  | nil : FVarAlpha env U [] []
  | cons :
      FVarAlpha env U left right →
      VLocalDecl.IsDefEq env U left.toCtx leftDecl rightDecl →
      FVarAlpha env U
        ((some (leftFVar, leftDeps), leftDecl) :: left)
        ((some (rightFVar, rightDeps), rightDecl) :: right)

theorem VLCtx.FVarAlpha.bvarize :
    VLCtx.FVarAlpha env U left right →
      VLCtx.IsDefEq env U (VLCtx.bvarize left) (VLCtx.bvarize right)
  | .nil => .nil
  | .cons relation declaration => by
      exact .cons relation.bvarize (by nofun) (by
        simpa only [VLCtx.bvarize_toCtx] using declaration)

theorem VLCtx.FVarAlpha.defeqCtx
    (relation : VLCtx.FVarAlpha env U left right) :
    env.IsDefEqCtx U [] left.toCtx right.toCtx := by
  simpa only [VLCtx.bvarize_toCtx] using relation.bvarize.defeqCtx

/-- Corresponding free-assumption contexts are alpha-related whenever their
Theory declarations are pointwise definitionally equal. -/
theorem _root_.Lean4Lean.VLCtx.FVarAlpha.of_defeqCtx
    (leftShape : left.FVarLamOnly)
    (rightShape : right.FVarLamOnly)
    (contextEq : env.IsDefEqCtx U [] left.toCtx right.toCtx) :
    VLCtx.FVarAlpha env U left right := by
  induction leftShape generalizing right with
  | nil =>
      cases rightShape with
      | nil => exact .nil
      | cons rightShape => cases contextEq
  | @cons left fv deps type leftShape ih =>
      cases rightShape with
      | nil => cases contextEq
      | @cons right fv' deps' type' rightShape =>
          cases contextEq with
          | succ tailContextEq headDefEq =>
              exact .cons (ih rightShape tailContextEq) (.vlam headDefEq)

/-- Translation congruence for alpha-equivalent kernel expressions under
pointwise corresponding free-assumption contexts. -/
theorem TrExprS.uniqAlpha
    {env : VEnv} {Us : List Name}
    {left right : VLCtx} {leftSource rightSource : Lean.Expr}
    {leftTarget rightTarget : VExpr}
    (henv : VEnv.WF env)
    (relation : VLCtx.FVarAlpha env Us.length left right)
    (leftShape : left.FVarLamOnly)
    (rightShape : right.FVarLamOnly)
    (leftRun : TrExprS env Us left leftSource leftTarget)
    (rightRun : TrExprS env Us right rightSource rightTarget)
    (sourceAlpha : Lean.Expr.abstractFVars left leftSource =
      Lean.Expr.abstractFVars right rightSource) :
    env.IsDefEqU Us.length left.toCtx leftTarget rightTarget := by
  have leftAbstract := leftRun.abstractFVars leftShape
  have rightAbstract := rightRun.abstractFVars rightShape
  rw [← sourceAlpha] at rightAbstract
  have result := leftAbstract.uniq henv relation.bvarize rightAbstract
  simpa only [VLCtx.bvarize_toCtx] using result

/--
info: 'Lean4Lean.TrExprS.abstractFVars' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms TrExprS.abstractFVars

/--
info: 'Lean4Lean.TrExprS.uniqAlpha' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms TrExprS.uniqAlpha

/-- Lift an ordinary Theory context equality back to the translator's
free-variable-preserving context relation when both implementations contain
only corresponding free-variable assumptions.  Dependency lists may differ;
they are deliberately absent from `IsDefEqCtx`. -/
theorem VLCtx.IsDefEqFVars.of_defeqCtx
    (leftShape : left.FVarLamOnly)
    (rightShape : right.FVarLamOnly)
    (fvarsEq : left.fvars = right.fvars)
    (contextEq : env.IsDefEqCtx U [] left.toCtx right.toCtx) :
    VLCtx.IsDefEqFVars env U left right := by
  induction leftShape generalizing right with
  | nil =>
      cases rightShape with
      | nil => exact .nil
      | cons rightShape => simp at fvarsEq
  | @cons left fv deps type leftShape ih =>
      cases rightShape with
      | nil => simp at fvarsEq
      | @cons right fv' deps' type' rightShape =>
          simp only [VLCtx.fvars_cons_some, List.cons.injEq] at fvarsEq
          obtain ⟨rfl, tailFvarsEq⟩ := fvarsEq
          cases contextEq with
          | succ tailContextEq headDefEq =>
              exact .cons_fvar
                (ih rightShape tailFvarsEq tailContextEq)
                (.vlam headDefEq)

/--
info: 'Lean4Lean.VLCtx.IsDefEqFVars.of_defeqCtx' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms VLCtx.IsDefEqFVars.of_defeqCtx

/-- Free-variable-preserving context equality retains the exact identifier
sequence even when dependency metadata differs. -/
theorem VLCtx.IsDefEqFVars.fvars :
    VLCtx.IsDefEqFVars env U left right → left.fvars = right.fvars
  | .nil => rfl
  | .cons_bvar relation _ => relation.fvars
  | .cons_fvar relation _ =>
      congrArg (fun tail => _ :: tail) relation.fvars

/-- Two verified translations of the same kernel local-context inventory use
the same metadata slots and definitionally equal local declarations. -/
private theorem trLCtx_isDefEq_aux
    (henv : VEnv.WF env)
    (hds : (ds.map (·.fvarId)).Nodup)
    (left : TrLCtx' env Us ds Δ₁)
    (right : TrLCtx' env Us ds Δ₂) :
    VLCtx.IsDefEq env Us.length Δ₁ Δ₂ := by
  induction left generalizing Δ₂ with
  | nil =>
      cases right
      exact .nil
  | @cons ds Δ₁ d d₁ left declaration ih =>
      cases right with
      | @cons _ Δ₂ _ d₂ right declaration₂ =>
          have tailNodup : (ds.map (·.fvarId)).Nodup := by
            change (d.fvarId :: ds.map (·.fvarId)).Nodup at hds
            exact hds.tail
          have tailEq := ih tailNodup right
          have tailWF := left.wf tailNodup
          have metadata : ∀ fv deps,
              some (d.fvarId, d.deps) = some (fv, deps) →
                fv ∉ Δ₁.fvars ∧ deps ⊆ Δ₁.fvars := by
            intro fv deps metadataEq
            simp only [Option.some.injEq, Prod.mk.injEq] at metadataEq
            rcases metadataEq with ⟨rfl, rfl⟩
            constructor
            · intro member
              have freshKernel : d.fvarId ∉ ds.map (·.fvarId) :=
                (List.nodup_cons.mp hds).1
              rw [← left.fvars_eq] at member
              exact freshKernel member
            · exact declaration.deps_wf
          cases declaration with
          | vlam typeTr typeType =>
              cases declaration₂ with
              | vlam typeTr₂ typeType₂ =>
                  obtain ⟨u, typeHas⟩ := typeType
                  have typeEq :=
                    (typeTr.uniq henv tailEq typeTr₂).of_l
                      henv tailWF.toCtx typeHas
                  exact .cons tailEq metadata (.vlam typeEq)
          | vlet typeTr valueTr valueType =>
              cases declaration₂ with
              | vlet typeTr₂ valueTr₂ valueType₂ =>
                  obtain ⟨u, typeHas⟩ :=
                    valueType.isType henv tailWF.toCtx
                  have typeEq :=
                    (typeTr.uniq henv tailEq typeTr₂).of_l
                      henv tailWF.toCtx typeHas
                  have valueEq :=
                    (valueTr.uniq henv tailEq valueTr₂).of_l
                      henv tailWF.toCtx valueType
                  exact .cons tailEq metadata (.vlet valueEq typeEq)

/-- Verified implementations of one exact kernel `LocalContext` are unique
up to ordinary verified-context definitional equality.  In particular, the
kernel-owned dependency metadata is retained literally on both sides. -/
theorem _root_.Lean4Lean.TrLCtx.isDefEq
    (henv : VEnv.WF env)
    (left : TrLCtx env Us lctx Δ₁)
    (right : TrLCtx env Us lctx Δ₂) :
    VLCtx.IsDefEq env Us.length Δ₁ Δ₂ :=
  trLCtx_isDefEq_aux henv left.1.nodup left.2 right.2

/-- Verified implementations of one exact kernel `LocalContext` are unique
up to definitional equality while retaining its free-variable identifiers. -/
theorem _root_.Lean4Lean.TrLCtx.isDefEqFVars
    (henv : VEnv.WF env)
    (left : TrLCtx env Us lctx Δ₁)
    (right : TrLCtx env Us lctx Δ₂) :
    VLCtx.IsDefEqFVars env Us.length Δ₁ Δ₂ :=
  (left.isDefEq henv right).toFVars

/--
info: 'Lean4Lean.TrLCtx.isDefEq' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms TrLCtx.isDefEq

/--
info: 'Lean4Lean.TrLCtx.isDefEqFVars' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms TrLCtx.isDefEqFVars

namespace TypeChecker

/-- Semantic snapshot of one exact candidate annotation node.  The kernel
root remains indexed by the structural path, while both strict translations
and the actual checker equality retain the precise recursive Theory context. -/
structure CandidateAnnotationSnapshot (env : VEnv) (Us : List Name)
    (root : Expr) where
  Δ : VLCtx
  name : Name
  domain : Expr
  body : Expr
  binderInfo : BinderInfo
  consumed : Expr
  domain' : VExpr
  consumed' : VExpr
  sort : VLevel
  root_eq : root = .forallE name domain body binderInfo
  annotation_match : consumed = AddInductive.consumeTypeAnnotations domain
  domain_tr : TrExprS env Us Δ domain domain'
  body_fvars : body.FVarsIn (· ∈ Δ.fvars)
  consumed_tr : TrExprS env Us Δ consumed consumed'
  domain_type : env.HasType Us.length Δ.toCtx domain' (.sort sort)
  annotation_run : IsDefEqRun env Us Δ domain consumed domain' consumed'

/-- The recursive checker execution owns a well-formed context for every
retained annotation snapshot. -/
theorem CandidateAnnotationSnapshot.context_wf
    (snapshot : CandidateAnnotationSnapshot env Us root) :
    VLCtx.WF env Us.length snapshot.Δ := by
  simpa only [snapshot.annotation_run.venv_eq,
    snapshot.annotation_run.lparams_eq,
    snapshot.annotation_run.vlctx_eq] using
    snapshot.annotation_run.context.Δwf

/-- Candidate annotation contexts contain only the free-variable declarations
allocated by the producer's local-context traversal. -/
theorem CandidateAnnotationSnapshot.context_noBV
    (snapshot : CandidateAnnotationSnapshot env Us root) :
    snapshot.Δ.NoBV := by
  have noBV := snapshot.annotation_run.context.mlctx.noBV
  change snapshot.annotation_run.context.vlctx.NoBV at noBV
  rw [snapshot.annotation_run.vlctx_eq] at noBV
  exact noBV

/-- Interpret a structural annotation position through the same recursive
semantic run that produced the candidate telescope. -/
theorem CandidateExprRun.annotationSnapshot
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {Δ : VLCtx} {source' view' inferred' : VExpr}
    (run : CandidateExprRun env Us trace Δ source' view' inferred')
    (position : trace.AnnotationAt count) :
    Nonempty (CandidateAnnotationSnapshot env Us position.root) := by
  induction position generalizing Δ source' view' inferred' with
  | zero annotationMatch =>
      cases run with
      | forallE annotations annotationsEq domainCandidate bodyCandidate node
          domainRun annotationsRun bodyRun domainType bodyType bodySource
          bodyContext =>
        exact ⟨{
          Δ := Δ
          name := _
          domain := _
          body := _
          binderInfo := _
          consumed := _
          domain' := _
          consumed' := _
          sort := _
          root_eq := rfl
          annotation_match := annotationMatch
          domain_tr := domainRun.source_tr
          body_fvars := node.whnf.rhs_tr.fvarsIn.2
          consumed_tr := annotationsRun.rhs_tr
          domain_type := domainType
          annotation_run := annotationsRun }⟩
  | succ bodyCandidate tail ih =>
      cases run with
      | forallE annotations annotationsEq domainCandidate bodyCandidate node
          domainRun annotationsRun bodyRun domainType bodyType bodySource
          bodyContext =>
        exact ih bodyRun

/-- Position-by-position semantic provenance for an annotation-consumed
candidate telescope.

The list index is the exact sequence of strict Theory translations selected
by the candidate's annotation equality runs.  A head certificate is exposed
only after supplying the producer's `Matches` witness, so this relation can be
built from a semantic run before structural validation annotations are
projected from the normalization execution. -/
inductive CandidateAnnotationSpine (env : VEnv) (Us : List Name) :
    {candidateContext : AddInductive.Context} → {source : Expr} →
      AddInductive.CandidateExprTrace candidateContext source →
      VLCtx → VLCtx → List VExpr → Prop where
  | terminal
      (node : CandidateNodeRun env Us Δ context source inferred result
        source' result' inferred') : CandidateAnnotationSpine env Us
      (.terminal context source inferred result checked normalized) Δ Δ []
  | forallE
      (domainCandidate : AddInductive.CandidateExprTrace context domain)
      (bodyCandidate : AddInductive.CandidateExprTrace
        (context.pushLocalDecl name binderInfo annotations.consumed)
        (body.instantiate1 context.freshExpr))
      (storedDomain' : VExpr) (domains : List VExpr)
      (head : annotations.Matches →
        ∃ snapshot : CandidateAnnotationSnapshot env Us
            (.forallE name domain body binderInfo),
          snapshot.Δ = Δ ∧ snapshot.consumed' = storedDomain')
      (tail : CandidateAnnotationSpine env Us bodyCandidate
        ((some (context.freshFVarId, annotations.consumed.fvarsList),
          .vlam storedDomain') :: Δ) terminalΔ domains) :
      CandidateAnnotationSpine env Us
        (.forallE context source inferred name domain body binderInfo fresh
          annotations annotationsEq checked normalized domainCandidate
          bodyCandidate)
        Δ terminalΔ (storedDomain' :: domains)

/-- An exact producer-owned suffix of an annotation spine.  The cursor owns
the literal recursive trace and verified context reached at that position. -/
structure CandidateAnnotationCursor (env : VEnv) (Us : List Name)
    (terminalΔ : VLCtx) where
  candidateContext : AddInductive.Context
  source : Expr
  trace : AddInductive.CandidateExprTrace candidateContext source
  Δ : VLCtx
  domains : List VExpr
  spine : CandidateAnnotationSpine env Us trace Δ terminalΔ domains
  shape : Δ.FVarLamOnly
  stored : trace.storedSpine = true
  annotations : trace.validationAnnotations
  resultLevel : Level
  terminal_eq : trace.terminalResult = .sort resultLevel
  terminal_notForall : trace.terminalResult.isForall = false

/-- The exact suffix selected by a structural annotation position, together
with its prefix context, free-variable inventory, and unchanged fuel. -/
structure CandidateAnnotationSpine.PositionSuffix
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {Δ terminalΔ : VLCtx} {domains : List VExpr}
    (spine : CandidateAnnotationSpine env Us trace Δ terminalΔ domains)
    {count : Nat} (position : trace.AnnotationAt count) where
  cursor : CandidateAnnotationCursor env Us terminalΔ
  root_eq : position.root = cursor.trace.rootWhnf
  context_eq : cursor.Δ.toCtx =
    (domains.take count).reverse ++ Δ.toCtx
  domains_eq : cursor.domains = domains.drop count
  fvars_eq : cursor.Δ.fvars.map Expr.fvar =
    (trace.parameterList count).reverse ++ Δ.fvars.map Expr.fvar
  fuel_eq : cursor.candidateContext.fuel = candidateContext.fuel

/-- A terminal-inclusive annotation-spine suffix.  The selected structural
position may be either a Pi node or the terminal candidate reached after all
binders. -/
structure CandidateAnnotationSpine.MainPositionSuffix
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {Δ terminalΔ : VLCtx} {domains : List VExpr}
    (spine : CandidateAnnotationSpine env Us trace Δ terminalΔ domains)
    {count : Nat} (position : trace.MainSpineAt count) where
  cursor : CandidateAnnotationCursor env Us terminalΔ
  root_eq : position.position.trace.rootWhnf = cursor.trace.rootWhnf
  context_eq : cursor.Δ.toCtx =
    (domains.take count).reverse ++ Δ.toCtx
  domains_eq : cursor.domains = domains.drop count
  fvars_eq : cursor.Δ.fvars.map Expr.fvar =
    (trace.parameterList count).reverse ++ Δ.fvars.map Expr.fvar
  fuel_eq : cursor.candidateContext.fuel = candidateContext.fuel

/-- Follow an annotation path into the literal recursive spine.  No suffix
trace, context, or semantic snapshot is independently reselected. -/
theorem CandidateAnnotationSpine.positionSuffix
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {Δ terminalΔ : VLCtx} {domains : List VExpr}
    (spine : CandidateAnnotationSpine env Us trace Δ terminalΔ domains)
    (initialShape : Δ.FVarLamOnly)
    (stored : trace.storedSpine = true)
    (annotations : trace.validationAnnotations)
    (terminalEq : trace.terminalResult = .sort resultLevel)
    {count : Nat} (position : trace.AnnotationAt count) :
    Nonempty (spine.PositionSuffix position) := by
  induction position generalizing Δ terminalΔ domains with
  | zero annotationMatch =>
      exact ⟨{
        cursor := {
          candidateContext := _
          source := _
          trace := _
          Δ := Δ
          domains := domains
          spine := spine
          shape := initialShape
          stored := stored
          annotations := annotations
          resultLevel := resultLevel
          terminal_eq := terminalEq
          terminal_notForall := by rw [terminalEq]; rfl }
        root_eq := rfl
        context_eq := rfl
        domains_eq := rfl
        fvars_eq := rfl
        fuel_eq := rfl }⟩
  | succ bodyCandidate position ih =>
      cases spine with
      | forallE domainCandidate bodyCandidate storedDomain domains head tail =>
          simp only [AddInductive.CandidateExprTrace.storedSpine,
            Bool.and_eq_true] at stored
          rcases annotations with ⟨annotationMatch, tailAnnotations⟩
          obtain ⟨suffix⟩ := ih tail (.cons initialShape) stored.2
            tailAnnotations terminalEq
          exact ⟨{
            cursor := suffix.cursor
            root_eq := suffix.root_eq
            context_eq := by
              simpa only [List.take_succ_cons, List.reverse_cons,
                List.singleton_append, List.append_assoc, VLCtx.toCtx] using
                suffix.context_eq
            domains_eq := by
              simpa only [List.drop_succ_cons] using suffix.domains_eq
            fvars_eq := by
              simpa [VLCtx.fvars, List.append_assoc,
                AddInductive.Context.freshExpr,
                AddInductive.CandidateExprTrace.parameterList] using
                suffix.fvars_eq
            fuel_eq := by
              simpa [AddInductive.Context.pushLocalDecl] using
                suffix.fuel_eq }⟩

/-- Follow a terminal-inclusive main-spine path into the literal recursive
annotation spine.  In particular, selecting the complete spine length yields
the terminal candidate cursor with an empty domain suffix. -/
theorem CandidateAnnotationSpine.mainPositionSuffix
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {Δ terminalΔ : VLCtx} {domains : List VExpr}
    (spine : CandidateAnnotationSpine env Us trace Δ terminalΔ domains)
    (initialShape : Δ.FVarLamOnly)
    (stored : trace.storedSpine = true)
    (annotations : trace.validationAnnotations)
    (terminalEq : trace.terminalResult = .sort resultLevel)
    {count : Nat} (position : trace.MainSpineAt count) :
    Nonempty (spine.MainPositionSuffix position) := by
  induction position generalizing Δ terminalΔ domains with
  | zero trace =>
      exact ⟨{
        cursor := {
          candidateContext := _
          source := _
          trace := trace
          Δ := Δ
          domains := domains
          spine := spine
          shape := initialShape
          stored := stored
          annotations := annotations
          resultLevel := resultLevel
          terminal_eq := terminalEq
          terminal_notForall := by rw [terminalEq]; rfl }
        root_eq := rfl
        context_eq := rfl
        domains_eq := rfl
        fvars_eq := rfl
        fuel_eq := rfl }⟩
  | succ bodyCandidate position ih =>
      cases spine with
      | forallE domainCandidate bodyCandidate storedDomain domains head tail =>
          simp only [AddInductive.CandidateExprTrace.storedSpine,
            Bool.and_eq_true] at stored
          rcases annotations with ⟨annotationMatch, tailAnnotations⟩
          obtain ⟨suffix⟩ := ih tail (.cons initialShape) stored.2
            tailAnnotations terminalEq
          exact ⟨{
            cursor := suffix.cursor
            root_eq := suffix.root_eq
            context_eq := by
              simpa only [List.take_succ_cons, List.reverse_cons,
                List.singleton_append, List.append_assoc, VLCtx.toCtx] using
                suffix.context_eq
            domains_eq := by
              simpa only [List.drop_succ_cons] using suffix.domains_eq
            fvars_eq := by
              simpa [VLCtx.fvars, List.append_assoc,
                AddInductive.Context.freshExpr,
                AddInductive.CandidateExprTrace.parameterList] using
                suffix.fvars_eq
            fuel_eq := by
              simpa [AddInductive.Context.pushLocalDecl] using
                suffix.fuel_eq }⟩

/-- The WHNF root selected by an annotation spine mentions only the free
variables in that spine's exact initial verified context. -/
theorem CandidateAnnotationSpine.root_fvars
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {Δ terminalΔ : VLCtx} {domains : List VExpr}
    (spine : CandidateAnnotationSpine env Us trace Δ terminalΔ domains)
    (annotations : trace.validationAnnotations) :
    trace.rootWhnf.FVarsIn (· ∈ Δ.fvars) := by
  cases spine with
  | terminal node =>
      simpa only [AddInductive.CandidateExprTrace.rootWhnf] using
        node.whnf.rhs_tr.fvarsIn
  | forallE domainCandidate bodyCandidate storedDomain domains head tail =>
      rename_i candidateDomain candidateName candidateBinderInfo candidateBody
        candidateInferred candidateAnnotations candidateFresh
        candidateAnnotationsEq candidateChecked candidateNormalized
      rcases annotations with ⟨annotationMatch, tailAnnotations⟩
      obtain ⟨snapshot, snapshotContext, snapshotStored⟩ :=
        head annotationMatch
      subst Δ
      have rootParts := snapshot.root_eq
      simp only [Expr.forallE.injEq] at rootParts
      rcases rootParts with
        ⟨_nameEq, domainEq, bodyEq, _binderInfoEq⟩
      have domainFVars : candidateDomain.FVarsIn
          (· ∈ snapshot.Δ.fvars) :=
        (congrArg (fun expression =>
          expression.FVarsIn (· ∈ snapshot.Δ.fvars)) domainEq).mpr
            snapshot.domain_tr.fvarsIn
      have bodyFVars : candidateBody.FVarsIn (· ∈ snapshot.Δ.fvars) :=
        (congrArg (fun expression =>
          expression.FVarsIn (· ∈ snapshot.Δ.fvars)) bodyEq).mpr
            snapshot.body_fvars
      simp only [AddInductive.CandidateExprTrace.rootWhnf]
      exact ⟨domainFVars, bodyFVars⟩

/-- The WHNF root selected by any producer annotation cursor mentions only
the free variables in that cursor's exact verified context. -/
theorem CandidateAnnotationCursor.root_fvars
    {env : VEnv} {Us : List Name} {terminalΔ : VLCtx}
    (cursor : CandidateAnnotationCursor env Us terminalΔ) :
    cursor.trace.rootWhnf.FVarsIn (· ∈ cursor.Δ.fvars) :=
  cursor.spine.root_fvars cursor.annotations

/--
info: 'Lean4Lean.TypeChecker.CandidateAnnotationSpine.positionSuffix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateAnnotationSpine.positionSuffix

/-- The exact annotation prefix context embeds into the exact terminal
context by skipping precisely the remaining producer-owned binder slots. -/
theorem CandidateAnnotationSpine.terminalLift
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {Δ terminalΔ : VLCtx} {domains : List VExpr}
    (spine : CandidateAnnotationSpine env Us trace Δ terminalΔ domains) :
    VLCtx.FVLift' Δ terminalΔ 0
      (.skipN .refl domains.length) 0 := by
  induction spine with
  | terminal => exact .refl
  | forallE domainCandidate bodyCandidate storedDomain' domains head tail ih =>
      have combined :=
        (VLCtx.FVLift'.skip_fvar _ _
          VLCtx.FVLift'.refl).comp ih
      simpa only [List.length_cons, Lift.comp_skipN, Lift.comp,
        Lift.skipN_skipN, VLocalDecl.depth, Nat.one_add] using combined

/-- A producer annotation telescope that starts with only free assumptions
also ends with only free assumptions.  Each traversed Pi contributes exactly
one free lambda declaration to the verified terminal context. -/
theorem CandidateAnnotationSpine.terminalShape
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {Δ terminalΔ : VLCtx} {domains : List VExpr}
    (spine : CandidateAnnotationSpine env Us trace Δ terminalΔ domains)
    (initialShape : Δ.FVarLamOnly) : terminalΔ.FVarLamOnly := by
  induction spine with
  | terminal => exact initialShape
  | forallE domainCandidate bodyCandidate storedDomain domains head tail ih =>
      exact ih (.cons initialShape)

/-- Recover the exact verified context after any bounded prefix of a
producer-owned annotation telescope.

Unlike `snapshotAt`, this projection is also available at the terminal
position.  It therefore exposes the shared-parameter boundary even when the
candidate has no following index annotation. -/
theorem CandidateAnnotationSpine.prefixContext
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {Δ terminalΔ : VLCtx} {domains : List VExpr}
    (spine : CandidateAnnotationSpine env Us trace Δ terminalΔ domains)
    (hcount : count ≤ domains.length) :
    ∃ prefixΔ : VLCtx,
      prefixΔ.toCtx = (domains.take count).reverse ++ Δ.toCtx ∧
      prefixΔ.fvars.map Expr.fvar =
        (trace.parameterList count).reverse ++ Δ.fvars.map Expr.fvar ∧
      VLCtx.FVLift' prefixΔ terminalΔ 0
        (.skipN .refl (domains.drop count).length) 0 := by
  induction spine generalizing count with
  | terminal =>
      have countEq : count = 0 := by simpa using hcount
      subst count
      exact ⟨_, rfl, rfl, VLCtx.FVLift'.refl⟩
  | forallE domainCandidate bodyCandidate storedDomain' domains head tail ih =>
      cases count with
      | zero =>
          have combined :=
            (VLCtx.FVLift'.skip_fvar _ _
              VLCtx.FVLift'.refl).comp tail.terminalLift
          refine ⟨_, rfl, rfl, ?_⟩
          simpa only [List.drop_zero, List.length_cons,
            Lift.comp_skipN, Lift.comp, Lift.skipN_skipN,
            VLocalDecl.depth, Nat.one_add] using combined
      | succ count =>
          have tailBound : count ≤ domains.length := by
            simpa only [List.length_cons, Nat.succ_le_succ_iff] using hcount
          obtain ⟨prefixΔ, contextEq, fvarsEq, terminalLift⟩ :=
            ih tailBound
          refine ⟨prefixΔ, ?_, ?_, ?_⟩
          · simpa only [List.take_succ_cons, List.reverse_cons,
              List.singleton_append, List.append_assoc, VLCtx.toCtx] using
              contextEq
          · simpa [VLCtx.fvars, List.append_assoc,
              AddInductive.Context.freshExpr,
              AddInductive.CandidateExprTrace.parameterList] using fvarsEq
          · simpa only [List.drop_succ_cons] using terminalLift

/-- Shape-refining version of `prefixContext` for candidate traversals that
start in a context containing only producer-allocated free assumptions.

The extra result rules out invisible let declarations, which `toCtx` and the
free-variable list cannot exclude on their own. -/
theorem CandidateAnnotationSpine.prefixContext_shaped
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {Δ terminalΔ : VLCtx} {domains : List VExpr}
    (spine : CandidateAnnotationSpine env Us trace Δ terminalΔ domains)
    (initialShape : Δ.FVarLamOnly)
    (hcount : count ≤ domains.length) :
    ∃ prefixΔ : VLCtx,
      prefixΔ.toCtx = (domains.take count).reverse ++ Δ.toCtx ∧
      prefixΔ.fvars.map Expr.fvar =
        (trace.parameterList count).reverse ++ Δ.fvars.map Expr.fvar ∧
      VLCtx.FVLift' prefixΔ terminalΔ 0
        (.skipN .refl (domains.drop count).length) 0 ∧
      prefixΔ.FVarLamOnly := by
  induction spine generalizing count with
  | terminal =>
      have countEq : count = 0 := by simpa using hcount
      subst count
      exact ⟨_, rfl, rfl, VLCtx.FVLift'.refl, initialShape⟩
  | forallE domainCandidate bodyCandidate storedDomain' domains head tail ih =>
      cases count with
      | zero =>
          have combined :=
            (VLCtx.FVLift'.skip_fvar _ _
              VLCtx.FVLift'.refl).comp tail.terminalLift
          refine ⟨_, rfl, rfl, ?_, initialShape⟩
          simpa only [List.drop_zero, List.length_cons,
            Lift.comp_skipN, Lift.comp, Lift.skipN_skipN,
            VLocalDecl.depth, Nat.one_add] using combined
      | succ count =>
          have tailBound : count ≤ domains.length := by
            simpa only [List.length_cons, Nat.succ_le_succ_iff] using hcount
          obtain ⟨prefixΔ, contextEq, fvarsEq, terminalLift, shape⟩ :=
            ih (.cons initialShape) tailBound
          refine ⟨prefixΔ, ?_, ?_, ?_, shape⟩
          · simpa only [List.take_succ_cons, List.reverse_cons,
              List.singleton_append, List.append_assoc, VLCtx.toCtx] using
              contextEq
          · simpa [VLCtx.fvars, List.append_assoc,
              AddInductive.Context.freshExpr,
              AddInductive.CandidateExprTrace.parameterList] using fvarsEq
          · simpa only [List.drop_succ_cons] using terminalLift

/-- Select the semantic snapshot and exact stored-domain suffix at one
producer-owned structural annotation position.

The same induction also retains the precise verified prefix context: its
Theory declarations are the reverse of the consumed domains before the
position, and its kernel free variables are the reverse of the trace's
producer-allocated parameter list. -/
theorem CandidateAnnotationSpine.snapshotAt
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {Δ terminalΔ : VLCtx} {domains : List VExpr}
    (spine : CandidateAnnotationSpine env Us trace Δ terminalΔ domains)
    (position : trace.AnnotationAt count) :
    ∃ snapshot : CandidateAnnotationSnapshot env Us position.root,
      ∃ tail, domains.drop count = snapshot.consumed' :: tail ∧
        snapshot.Δ.toCtx =
          (domains.take count).reverse ++ Δ.toCtx ∧
        snapshot.Δ.fvars.map Expr.fvar =
          (trace.parameterList count).reverse ++ Δ.fvars.map Expr.fvar ∧
        VLCtx.FVLift' snapshot.Δ terminalΔ 0
          (.skipN .refl (domains.drop count).length) 0 := by
  induction position generalizing Δ terminalΔ domains with
  | zero annotationMatch =>
      cases spine with
      | forallE domainCandidate bodyCandidate storedDomain' domains head tail =>
          obtain ⟨snapshot, snapshotContext, snapshotEq⟩ :=
            head annotationMatch
          subst snapshotContext
          refine ⟨snapshot, domains, ?_, ?_, ?_, ?_⟩
          · simp only [List.drop_zero, snapshotEq]
          · rfl
          · rfl
          · have combined :=
              (VLCtx.FVLift'.skip_fvar _ _
                VLCtx.FVLift'.refl).comp tail.terminalLift
            simpa only [List.drop_zero, List.length_cons,
              Lift.comp_skipN, Lift.comp, Lift.skipN_skipN,
              VLocalDecl.depth, Nat.one_add] using combined
  | succ bodyCandidate position ih =>
      cases spine with
      | forallE domainCandidate bodyCandidate storedDomain' domains head tail =>
          obtain ⟨snapshot, suffix, suffixEq, contextEq, fvarsEq,
              terminalLift⟩ :=
            ih tail
          refine ⟨snapshot, suffix, ?_, ?_, ?_, ?_⟩
          · simpa only [List.drop_succ_cons,
              AddInductive.CandidateExprTrace.AnnotationAt.root] using
              suffixEq
          · simpa only [List.take_succ_cons, List.reverse_cons,
              List.singleton_append, List.append_assoc, VLCtx.toCtx,
              AddInductive.CandidateExprTrace.AnnotationAt.root] using
              contextEq
          · simpa [VLCtx.fvars, List.append_assoc,
              AddInductive.Context.freshExpr,
              AddInductive.CandidateExprTrace.parameterList,
              AddInductive.CandidateExprTrace.AnnotationAt.root] using
              fvarsEq
          · simpa only [List.drop_succ_cons,
              AddInductive.CandidateExprTrace.AnnotationAt.root] using
              terminalLift

/-- Shape-refining annotation selection for a producer telescope rooted in a
free-variable-only verified context. -/
theorem CandidateAnnotationSpine.snapshotAt_shaped
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {Δ terminalΔ : VLCtx} {domains : List VExpr}
    (spine : CandidateAnnotationSpine env Us trace Δ terminalΔ domains)
    (initialShape : Δ.FVarLamOnly)
    (position : trace.AnnotationAt count) :
    ∃ snapshot : CandidateAnnotationSnapshot env Us position.root,
      ∃ tail, domains.drop count = snapshot.consumed' :: tail ∧
        snapshot.Δ.toCtx =
          (domains.take count).reverse ++ Δ.toCtx ∧
        snapshot.Δ.fvars.map Expr.fvar =
          (trace.parameterList count).reverse ++ Δ.fvars.map Expr.fvar ∧
        VLCtx.FVLift' snapshot.Δ terminalΔ 0
          (.skipN .refl (domains.drop count).length) 0 ∧
        snapshot.Δ.FVarLamOnly := by
  induction position generalizing Δ terminalΔ domains with
  | zero annotationMatch =>
      cases spine with
      | forallE domainCandidate bodyCandidate storedDomain' domains head tail =>
          obtain ⟨snapshot, snapshotContext, snapshotEq⟩ :=
            head annotationMatch
          subst snapshotContext
          refine ⟨snapshot, domains, ?_, ?_, ?_, ?_, initialShape⟩
          · simp only [List.drop_zero, snapshotEq]
          · rfl
          · rfl
          · have combined :=
              (VLCtx.FVLift'.skip_fvar _ _
                VLCtx.FVLift'.refl).comp tail.terminalLift
            simpa only [List.drop_zero, List.length_cons,
              Lift.comp_skipN, Lift.comp, Lift.skipN_skipN,
              VLocalDecl.depth, Nat.one_add] using combined
  | succ bodyCandidate position ih =>
      cases spine with
      | forallE domainCandidate bodyCandidate storedDomain' domains head tail =>
          obtain ⟨snapshot, suffix, suffixEq, contextEq, fvarsEq,
              terminalLift, shape⟩ :=
            ih tail (.cons initialShape)
          refine ⟨snapshot, suffix, ?_, ?_, ?_, ?_, shape⟩
          · simpa only [List.drop_succ_cons,
              AddInductive.CandidateExprTrace.AnnotationAt.root] using
              suffixEq
          · simpa only [List.take_succ_cons, List.reverse_cons,
              List.singleton_append, List.append_assoc, VLCtx.toCtx,
              AddInductive.CandidateExprTrace.AnnotationAt.root] using
              contextEq
          · simpa [VLCtx.fvars, List.append_assoc,
              AddInductive.Context.freshExpr,
              AddInductive.CandidateExprTrace.parameterList,
              AddInductive.CandidateExprTrace.AnnotationAt.root] using
              fvarsEq
          · simpa only [List.drop_succ_cons,
              AddInductive.CandidateExprTrace.AnnotationAt.root] using
              terminalLift

/--
info: 'Lean4Lean.TypeChecker.CandidateAnnotationSpine.prefixContext_shaped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateAnnotationSpine.prefixContext_shaped

/--
info: 'Lean4Lean.TypeChecker.CandidateAnnotationSpine.snapshotAt_shaped' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateAnnotationSpine.snapshotAt_shaped

/-- Construct one exact validator index domain from an alpha-equivalent
candidate annotation snapshot.

The validator context may contain unrelated producer locals between the
shared parameter prefix and its newly allocated index locals.  `base` removes
those slots, `reference` re-inserts them through the exact lift, and
`FVarAlpha` compares the resulting kernel expression with the candidate after
both free-variable inventories are abstracted to one positional telescope. -/
theorem FamilyParameterIndexBoundary.indexDomainRun_of_alpha
    {nparams : Nat} {stats : AddInductive.InductiveStats}
    {context : AddInductive.Context} {rootSource : Lean.Expr}
    {i nindices rootFuel : Nat}
    {outer : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
      context rootSource i nindices rootFuel}
    {contextRun : CandidateContextRun context}
    {boundary : FamilyParameterIndexBoundary outer contextRun}
    {env : VEnv} {Us : List Name} {candidateRoot : Lean.Expr}
    (candidate : CandidateAnnotationSnapshot env Us candidateRoot)
    (venv_eq : contextRun.context.venv = env)
    (lparams_eq : contextRun.context.lparams = Us)
    {base reference : VLCtx} {lift : Lift}
    (baseShape : base.FVarLamOnly)
    (candidateShape : candidate.Δ.FVarLamOnly)
    (relation : VLCtx.FVarAlpha env Us.length base candidate.Δ)
    (referenceLift : VLCtx.FVLift' base reference 0 lift 0)
    (currentReference : VLCtx.IsDefEq env Us.length
      contextRun.context.vlctx reference)
    (sourceScope : boundary.source.FVarsIn (· ∈ base.fvars))
    (sourceAlpha : Lean.Expr.abstractFVars base boundary.source =
      Lean.Expr.abstractFVars candidate.Δ candidateRoot)
    (isForall : boundary.source.isForall = true) :
    Nonempty boundary.IndexDomainRun := by
  have henv : VEnv.WF env := by
    simpa only [venv_eq] using contextRun.context.Ewf
  have currentWF : VLCtx.WF env Us.length contextRun.context.vlctx := by
    simpa only [venv_eq, lparams_eq] using contextRun.context.Δwf
  have referenceWF : VLCtx.WF env Us.length reference :=
    (currentReference.symm henv.ordered).wf
  have baseWF : VLCtx.WF env Us.length base :=
    referenceLift.wf henv referenceWF
  obtain ⟨translation⟩ :=
    boundary.indexDomainTranslation_of_forall isForall
  have rootAlpha : Lean.Expr.abstractFVars base
      (.forallE translation.name translation.domain translation.body
        translation.binderInfo) =
      Lean.Expr.abstractFVars candidate.Δ
        (.forallE candidate.name candidate.domain candidate.body
          candidate.binderInfo) := by
    calc
      Lean.Expr.abstractFVars base
          (.forallE translation.name translation.domain translation.body
            translation.binderInfo) =
          Lean.Expr.abstractFVars base boundary.source :=
        congrArg (Lean.Expr.abstractFVars base)
          translation.source_eq.symm
      _ = Lean.Expr.abstractFVars candidate.Δ candidateRoot := sourceAlpha
      _ = Lean.Expr.abstractFVars candidate.Δ
          (.forallE candidate.name candidate.domain candidate.body
            candidate.binderInfo) :=
        congrArg (Lean.Expr.abstractFVars candidate.Δ) candidate.root_eq
  rw [Lean.Expr.abstractFVars_forallE,
    Lean.Expr.abstractFVars_forallE] at rootAlpha
  simp only [Lean.Expr.forallE.injEq] at rootAlpha
  obtain ⟨_nameAlpha, domainAlpha, _bodyAlpha, _binderAlpha⟩ := rootAlpha
  have consumedAlpha : Lean.Expr.abstractFVars base
      (AddInductive.consumeTypeAnnotations translation.domain) =
      Lean.Expr.abstractFVars candidate.Δ candidate.consumed := by
    calc
      Lean.Expr.abstractFVars base
          (AddInductive.consumeTypeAnnotations translation.domain) =
          AddInductive.consumeTypeAnnotations
            (Lean.Expr.abstractFVars base translation.domain) :=
        (AddInductive.consumeTypeAnnotations_abstractFVars
          base translation.domain).symm
      _ = AddInductive.consumeTypeAnnotations
            (Lean.Expr.abstractFVars candidate.Δ candidate.domain) :=
        congrArg AddInductive.consumeTypeAnnotations domainAlpha
      _ = Lean.Expr.abstractFVars candidate.Δ
            (AddInductive.consumeTypeAnnotations candidate.domain) :=
        AddInductive.consumeTypeAnnotations_abstractFVars
          candidate.Δ candidate.domain
      _ = Lean.Expr.abstractFVars candidate.Δ candidate.consumed :=
        congrArg (Lean.Expr.abstractFVars candidate.Δ)
          candidate.annotation_match.symm
  have sourceScope' := sourceScope
  rw [translation.source_eq] at sourceScope'
  have domainScope : translation.domain.FVarsIn (· ∈ base.fvars) :=
    sourceScope'.1
  have consumedScope :
      (AddInductive.consumeTypeAnnotations translation.domain).FVarsIn
        (· ∈ base.fvars) := by
    cases htrace : AddInductive.CandidateTypeAnnotationTrace.build
        translation.domain with
    | mk consumed trace =>
        have consumed_eq : consumed =
            AddInductive.consumeTypeAnnotations translation.domain := by
          simpa only [htrace] using
            AddInductive.CandidateTypeAnnotationTrace.build_consumed
              translation.domain
        simpa only [← consumed_eq] using
          candidateTypeAnnotation_fvarsIn trace domainScope
  have currentNoBV : contextRun.context.vlctx.NoBV := by
    exact contextRun.context.mlctx.noBV
  have domainClosed : Closed translation.domain 0 := by
    simpa only [currentNoBV] using translation.domain_tr.closed
  have consumedClosed :
      Closed (AddInductive.consumeTypeAnnotations translation.domain) 0 := by
    simpa only [currentNoBV] using translation.consumed_tr.closed
  have currentDomainTr : TrExprS env Us contextRun.context.vlctx
      translation.domain translation.domain' := by
    simpa only [VContext.TrExprS, venv_eq, lparams_eq] using
      translation.domain_tr
  have currentConsumedTr : TrExprS env Us contextRun.context.vlctx
      (AddInductive.consumeTypeAnnotations translation.domain)
      translation.consumed' := by
    simpa only [VContext.TrExprS, venv_eq, lparams_eq] using
      translation.consumed_tr
  obtain ⟨baseDomain, baseDomainTr⟩ :=
    currentDomainTr.weakFV'_inv henv referenceLift currentReference
      domainClosed domainScope
  obtain ⟨baseConsumed, baseConsumedTr⟩ :=
    currentConsumedTr.weakFV'_inv henv referenceLift currentReference
      consumedClosed consumedScope
  have baseDomainEq : env.IsDefEqU Us.length base.toCtx
      baseDomain candidate.domain' :=
    baseDomainTr.uniqAlpha henv relation baseShape candidateShape
      candidate.domain_tr domainAlpha
  have baseConsumedEq : env.IsDefEqU Us.length base.toCtx
      baseConsumed candidate.consumed' :=
    baseConsumedTr.uniqAlpha henv relation baseShape candidateShape
      candidate.consumed_tr consumedAlpha
  have annotationAtCandidate : env.IsDefEqU Us.length
      candidate.Δ.toCtx candidate.domain' candidate.consumed' :=
    candidate.annotation_run.isDefEqU
  have annotationAtBase : env.IsDefEqU Us.length base.toCtx
      baseDomain baseConsumed := by
    have candidateAtBase := annotationAtCandidate.defeqDFC henv.ordered
      (relation.defeqCtx.symm henv.ordered)
    exact (baseDomainEq.trans henv baseWF.toCtx candidateAtBase).trans
      henv baseWF.toCtx baseConsumedEq.symm
  have annotationAtReference :=
    annotationAtBase.weak' henv.ordered referenceLift.toCtx
  have baseDomainAtReference :=
    baseDomainTr.weakFV' henv.ordered referenceLift referenceWF
  have baseConsumedAtReference :=
    baseConsumedTr.weakFV' henv.ordered referenceLift referenceWF
  have currentDomainEq :=
    currentDomainTr.uniq henv currentReference baseDomainAtReference
  have currentConsumedEq :=
    currentConsumedTr.uniq henv currentReference baseConsumedAtReference
  have annotationAtCurrent :=
    annotationAtReference.defeqDFC henv.ordered
      ((currentReference.symm henv.ordered).defeqCtx)
  have annotationU : env.IsDefEqU Us.length
      contextRun.context.vlctx.toCtx translation.domain'
      translation.consumed' :=
    (currentDomainEq.trans henv currentWF.toCtx annotationAtCurrent).trans
      henv currentWF.toCtx currentConsumedEq.symm
  have domainType : env.IsType Us.length contextRun.context.vlctx.toCtx
      translation.domain' := by
    simpa only [VContext.IsType, venv_eq, lparams_eq] using
      translation.domain_type
  obtain ⟨sort, domainHasType⟩ := domainType
  have annotationDef := annotationU.of_l henv currentWF.toCtx domainHasType
  exact ⟨{
    translation := translation
    sort := sort
    annotation_def := by
      simpa only [venv_eq, lparams_eq] using annotationDef }⟩

/-- Exact validator-owned chain consuming a producer annotation suffix.
Every step stores the completed domain run and the literal retained advance;
`done` marks exhaustion of the producer annotation spine. -/
inductive FamilyParameterIndexBoundary.IndexDomainChain :
    {nparams : Nat} → {stats : AddInductive.InductiveStats} →
    {context : AddInductive.Context} → {rootSource : Lean.Expr} →
    {i nindices rootFuel : Nat} →
    {outer : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
      context rootSource i nindices rootFuel} →
    {contextRun : CandidateContextRun context} →
    (boundary : FamilyParameterIndexBoundary outer contextRun) → Type where
  | done
      {boundary : FamilyParameterIndexBoundary outer contextRun} :
      FamilyParameterIndexBoundary.IndexDomainChain boundary
  | step
      {boundary : FamilyParameterIndexBoundary outer contextRun}
      (run : boundary.IndexDomainRun)
      (advance : FamilyParameterIndexBoundary.IndexDomainAdvance run)
      (tail : FamilyParameterIndexBoundary.IndexDomainChain
        advance.toBoundary) :
      FamilyParameterIndexBoundary.IndexDomainChain boundary

/-- The exact boundary at which a producer-owned index chain stops.
Packaging every dependent trace index prevents a consumer from replacing the
final reader context or source after traversing the chain. -/
structure FamilyParameterIndexBoundary.IndexDomainEndpoint
    (nparams : Nat) (stats : AddInductive.InductiveStats) where
  context : AddInductive.Context
  rootSource : Lean.Expr
  i : Nat
  nindices : Nat
  rootFuel : Nat
  outer : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
    context rootSource i nindices rootFuel
  contextRun : CandidateContextRun context
  boundary : FamilyParameterIndexBoundary outer contextRun

/-- Follow a completed chain to its literal final boundary. -/
def FamilyParameterIndexBoundary.IndexDomainChain.endpoint
    {nparams : Nat} {stats : AddInductive.InductiveStats}
    {context : AddInductive.Context} {rootSource : Lean.Expr}
    {i nindices rootFuel : Nat}
    {outer : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
      context rootSource i nindices rootFuel}
    {contextRun : CandidateContextRun context}
    {boundary : FamilyParameterIndexBoundary outer contextRun} :
    boundary.IndexDomainChain →
      FamilyParameterIndexBoundary.IndexDomainEndpoint nparams stats
  | .done => {
      context := context
      rootSource := rootSource
      i := i
      nindices := nindices
      rootFuel := rootFuel
      outer := outer
      contextRun := contextRun
      boundary := boundary }
  | .step _ _ tail => tail.endpoint

/-- Number of exact validator index constructors consumed by a chain. -/
def FamilyParameterIndexBoundary.IndexDomainChain.length
    {nparams : Nat} {stats : AddInductive.InductiveStats}
    {context : AddInductive.Context} {rootSource : Lean.Expr}
    {i nindices rootFuel : Nat}
    {outer : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
      context rootSource i nindices rootFuel}
    {contextRun : CandidateContextRun context}
    {boundary : FamilyParameterIndexBoundary outer contextRun} :
    boundary.IndexDomainChain → Nat
  | .done => 0
  | .step _ _ tail => tail.length + 1

/-- The endpoint counter is the initial counter plus the exact number of
consumed validator index constructors. -/
theorem FamilyParameterIndexBoundary.IndexDomainChain.endpoint_nindices
    {nparams : Nat} {stats : AddInductive.InductiveStats}
    {context : AddInductive.Context} {rootSource : Lean.Expr}
    {i nindices rootFuel : Nat}
    {outer : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
      context rootSource i nindices rootFuel}
    {contextRun : CandidateContextRun context}
    {boundary : FamilyParameterIndexBoundary outer contextRun}
    (chain : boundary.IndexDomainChain) :
    chain.endpoint.nindices = nindices + chain.length := by
  induction chain with
  | done => rfl
  | step run advance tail ih =>
    simp only [FamilyParameterIndexBoundary.IndexDomainChain.endpoint,
      FamilyParameterIndexBoundary.IndexDomainChain.length]
    omega

/-- Index traversal preserves the semantic environment stored by the initial
verified context. -/
theorem FamilyParameterIndexBoundary.IndexDomainChain.endpoint_venv
    {nparams : Nat} {stats : AddInductive.InductiveStats}
    {context : AddInductive.Context} {rootSource : Lean.Expr}
    {i nindices rootFuel : Nat}
    {outer : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
      context rootSource i nindices rootFuel}
    {contextRun : CandidateContextRun context}
    {boundary : FamilyParameterIndexBoundary outer contextRun}
    (chain : boundary.IndexDomainChain) :
    chain.endpoint.contextRun.context.venv = contextRun.context.venv := by
  induction chain with
  | done => rfl
  | step run advance tail ih => exact ih

/-- Index traversal preserves the universe-parameter list stored by the
initial verified context. -/
theorem FamilyParameterIndexBoundary.IndexDomainChain.endpoint_lparams
    {nparams : Nat} {stats : AddInductive.InductiveStats}
    {context : AddInductive.Context} {rootSource : Lean.Expr}
    {i nindices rootFuel : Nat}
    {outer : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
      context rootSource i nindices rootFuel}
    {contextRun : CandidateContextRun context}
    {boundary : FamilyParameterIndexBoundary outer contextRun}
    (chain : boundary.IndexDomainChain) :
    chain.endpoint.contextRun.context.lparams =
      contextRun.context.lparams := by
  induction chain with
  | done => rfl
  | step run advance tail ih => exact ih

/-- The final boundary still reaches the exact result payload of the original
later-family telescope. -/
theorem FamilyParameterIndexBoundary.IndexDomainChain.endpoint_result_eq
    {nparams : Nat} {stats : AddInductive.InductiveStats}
    {context : AddInductive.Context} {rootSource : Lean.Expr}
    {i nindices rootFuel : Nat}
    {outer : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
      context rootSource i nindices rootFuel}
    {contextRun : CandidateContextRun context}
    {boundary : FamilyParameterIndexBoundary outer contextRun}
    (chain : boundary.IndexDomainChain) :
    chain.endpoint.boundary.trace.result = outer.result := by
  induction chain with
  | @done context rootSource i nindices rootFuel outer contextRun boundary =>
      simpa only [FamilyParameterIndexBoundary.IndexDomainChain.endpoint] using
        boundary.result_eq
  | step run advance tail ih => exact ih.trans advance.result_eq

/-- A chain which accounts for the outer telescope's complete final index
counter has reached the exact terminal boundary.  This turns endpoint shape
into a purely arithmetic producer obligation. -/
theorem
    FamilyParameterIndexBoundary.IndexDomainChain.endpoint_terminal_of_result_nindices_eq
    {nparams : Nat} {stats : AddInductive.InductiveStats}
    {context : AddInductive.Context} {rootSource : Lean.Expr}
    {i nindices rootFuel : Nat}
    {outer : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
      context rootSource i nindices rootFuel}
    {contextRun : CandidateContextRun context}
    {boundary : FamilyParameterIndexBoundary outer contextRun}
    (chain : boundary.IndexDomainChain)
    (complete : outer.result.nindices = nindices + chain.length) :
    Nonempty chain.endpoint.boundary.Terminal := by
  apply chain.endpoint.boundary.terminal_of_result_nindices_eq
  rw [chain.endpoint_result_eq, chain.endpoint_nindices]
  exact complete

/-- Reindex the endpoint's verified context onto the original family
telescope result once the exact endpoint has been shown terminal. -/
def FamilyParameterIndexBoundary.IndexDomainChain.endpointContextRun
    {nparams : Nat} {stats : AddInductive.InductiveStats}
    {context : AddInductive.Context} {rootSource : Lean.Expr}
    {i nindices rootFuel : Nat}
    {outer : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
      context rootSource i nindices rootFuel}
    {contextRun : CandidateContextRun context}
    {boundary : FamilyParameterIndexBoundary outer contextRun}
    (chain : boundary.IndexDomainChain)
    (terminal : chain.endpoint.boundary.Terminal) :
    CandidateContextRun outer.result.context := by
  have endpointContextEq :
      chain.endpoint.boundary.trace.result.context =
        chain.endpoint.context := terminal.result_context_eq
  have outerContextEq : chain.endpoint.context = outer.result.context := by
    rw [← endpointContextEq]
    exact congrArg
      AddInductive.FamilyTypeParameterComparisonTrace.Result.context
      chain.endpoint_result_eq
  exact outerContextEq ▸ chain.endpoint.contextRun

/-- The transported terminal run retains the initial semantic environment. -/
theorem
    FamilyParameterIndexBoundary.IndexDomainChain.endpointContextRun_venv
    {nparams : Nat} {stats : AddInductive.InductiveStats}
    {context : AddInductive.Context} {rootSource : Lean.Expr}
    {i nindices rootFuel : Nat}
    {outer : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
      context rootSource i nindices rootFuel}
    {contextRun : CandidateContextRun context}
    {boundary : FamilyParameterIndexBoundary outer contextRun}
    (chain : boundary.IndexDomainChain)
    (terminal : chain.endpoint.boundary.Terminal) :
    (chain.endpointContextRun terminal).context.venv =
      contextRun.context.venv := by
  unfold endpointContextRun
  rw [CandidateContextRun.cast_context_context]
  exact chain.endpoint_venv

/-- The transported terminal run retains the initial universe parameters. -/
theorem
    FamilyParameterIndexBoundary.IndexDomainChain.endpointContextRun_lparams
    {nparams : Nat} {stats : AddInductive.InductiveStats}
    {context : AddInductive.Context} {rootSource : Lean.Expr}
    {i nindices rootFuel : Nat}
    {outer : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
      context rootSource i nindices rootFuel}
    {contextRun : CandidateContextRun context}
    {boundary : FamilyParameterIndexBoundary outer contextRun}
    (chain : boundary.IndexDomainChain)
    (terminal : chain.endpoint.boundary.Terminal) :
    (chain.endpointContextRun terminal).context.lparams =
      contextRun.context.lparams := by
  unfold endpointContextRun
  rw [CandidateContextRun.cast_context_context]
  exact chain.endpoint_lparams

/-- Semantic state retained at the exact endpoint of an index chain.

`root_reference_lift` deliberately skips each family-specific index while
`reference_lift` follows it on both sides.  The former is the invariant needed
to reuse the original shared-parameter base at the next source family; the
latter keeps the current producer terminal context aligned. -/
structure FamilyParameterIndexBoundary.IndexDomainChain.EndpointAlignment
    {nparams : Nat} {stats : AddInductive.InductiveStats}
    {context : AddInductive.Context} {rootSource : Lean.Expr}
    {i nindices rootFuel : Nat}
    {outer : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
      context rootSource i nindices rootFuel}
    {contextRun : CandidateContextRun context}
    {boundary : FamilyParameterIndexBoundary outer contextRun}
    (chain : boundary.IndexDomainChain)
    (env : VEnv) (Us : List Name)
    (terminalΔ rootBase originBase : VLCtx) where
  base : VLCtx
  reference : VLCtx
  lift : Lift
  rootLift : Lift
  originLift : Lift
  base_shape : base.FVarLamOnly
  terminal_shape : terminalΔ.FVarLamOnly
  relation : VLCtx.FVarAlpha env Us.length base terminalΔ
  reference_lift : VLCtx.FVLift' base reference 0 lift 0
  root_reference_lift : VLCtx.FVLift' rootBase reference 0 rootLift 0
  origin_reference_lift :
    VLCtx.FVLift' originBase reference 0 originLift 0
  current_reference : VLCtx.IsDefEq env Us.length
    chain.endpoint.contextRun.context.vlctx reference
  sort : VLevel
  endpoint_sort : env.IsDefEqU Us.length
    chain.endpoint.contextRun.context.vlctx.toCtx
    chain.endpoint.boundary.source' (.sort sort)

/-- A Theory endpoint definitionally equal to a sort cannot translate a
remaining kernel Pi.  Hence the aligned chain has reached the exact terminal
constructor of the validator's retained index suffix. -/
theorem
    FamilyParameterIndexBoundary.IndexDomainChain.EndpointAlignment.terminal
    {nparams : Nat} {stats : AddInductive.InductiveStats}
    {context : AddInductive.Context} {rootSource : Lean.Expr}
    {i nindices rootFuel : Nat}
    {outer : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
      context rootSource i nindices rootFuel}
    {contextRun : CandidateContextRun context}
    {boundary : FamilyParameterIndexBoundary outer contextRun}
    {chain : boundary.IndexDomainChain}
    {env : VEnv} {Us : List Name}
    {terminalΔ rootBase originBase : VLCtx}
    (alignment : chain.EndpointAlignment env Us terminalΔ rootBase
      originBase)
    (henv : VEnv.WF env) :
    Nonempty chain.endpoint.boundary.Terminal := by
  rcases chain.endpoint.boundary.progress with sourceForall | terminal
  · obtain ⟨translation⟩ :=
      chain.endpoint.boundary.indexDomainTranslation_of_forall sourceForall
    have impossible : env.IsDefEqU Us.length
        chain.endpoint.contextRun.context.vlctx.toCtx
        (.sort alignment.sort)
        (.forallE translation.domain' translation.body') := by
      rw [← translation.source'_eq]
      exact alignment.endpoint_sort.symm
    exact (VEnv.IsDefEqU.sort_forallE_inv henv
      alignment.current_reference.wf.toCtx impossible).elim
  · exact terminal

/-- Lowered data needed to extend an alpha cursor after one exact domain. -/
structure FamilyParameterIndexBoundary.IndexDomainAlphaPreparation
    {nparams : Nat} {stats : AddInductive.InductiveStats}
    {context : AddInductive.Context} {rootSource : Lean.Expr}
    {i nindices rootFuel : Nat}
    {outer : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
      context rootSource i nindices rootFuel}
    {contextRun : CandidateContextRun context}
    (boundary : FamilyParameterIndexBoundary outer contextRun)
    {env : VEnv} {Us : List Name} {candidateRoot : Lean.Expr}
    (candidate : CandidateAnnotationSnapshot env Us candidateRoot)
    {base reference : VLCtx} {lift : Lift}
    (referenceLift : VLCtx.FVLift' base reference 0 lift 0)
    (run : boundary.IndexDomainRun) where
  baseConsumed : VExpr
  base_consumed_tr : TrExprS env Us base
    (AddInductive.consumeTypeAnnotations run.translation.domain) baseConsumed
  base_consumed_candidate : env.IsDefEq Us.length base.toCtx
    baseConsumed candidate.consumed' (.sort candidate.sort)
  current_consumed_reference : env.IsDefEq Us.length
    contextRun.context.vlctx.toCtx run.translation.consumed'
    (baseConsumed.lift' lift) (.sort run.sort)

/-- Recover the exact lowered consumed domain and both equalities required to
extend the base/reference alpha invariant after a completed domain run. -/
theorem FamilyParameterIndexBoundary.IndexDomainRun.alphaPreparation
    {nparams : Nat} {stats : AddInductive.InductiveStats}
    {context : AddInductive.Context} {rootSource : Lean.Expr}
    {i nindices rootFuel : Nat}
    {outer : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
      context rootSource i nindices rootFuel}
    {contextRun : CandidateContextRun context}
    {boundary : FamilyParameterIndexBoundary outer contextRun}
    (run : boundary.IndexDomainRun)
    {env : VEnv} {Us : List Name} {candidateRoot : Lean.Expr}
    (candidate : CandidateAnnotationSnapshot env Us candidateRoot)
    (venv_eq : contextRun.context.venv = env)
    (lparams_eq : contextRun.context.lparams = Us)
    {base reference : VLCtx} {lift : Lift}
    (baseShape : base.FVarLamOnly)
    (candidateShape : candidate.Δ.FVarLamOnly)
    (relation : VLCtx.FVarAlpha env Us.length base candidate.Δ)
    (referenceLift : VLCtx.FVLift' base reference 0 lift 0)
    (currentReference : VLCtx.IsDefEq env Us.length
      contextRun.context.vlctx reference)
    (sourceScope : boundary.source.FVarsIn (· ∈ base.fvars))
    (sourceAlpha : Lean.Expr.abstractFVars base boundary.source =
      Lean.Expr.abstractFVars candidate.Δ candidateRoot) :
    Nonempty (boundary.IndexDomainAlphaPreparation candidate referenceLift
      run) := by
  have henv : VEnv.WF env := by
    simpa only [venv_eq] using contextRun.context.Ewf
  have currentWF : VLCtx.WF env Us.length contextRun.context.vlctx := by
    simpa only [venv_eq, lparams_eq] using contextRun.context.Δwf
  have referenceWF : VLCtx.WF env Us.length reference :=
    (currentReference.symm henv.ordered).wf
  have baseWF : VLCtx.WF env Us.length base :=
    referenceLift.wf henv referenceWF
  have rootAlpha : Lean.Expr.abstractFVars base
      (.forallE run.translation.name run.translation.domain
        run.translation.body run.translation.binderInfo) =
      Lean.Expr.abstractFVars candidate.Δ
        (.forallE candidate.name candidate.domain candidate.body
          candidate.binderInfo) := by
    calc
      Lean.Expr.abstractFVars base
          (.forallE run.translation.name run.translation.domain
            run.translation.body run.translation.binderInfo) =
          Lean.Expr.abstractFVars base boundary.source :=
        congrArg (Lean.Expr.abstractFVars base)
          run.translation.source_eq.symm
      _ = Lean.Expr.abstractFVars candidate.Δ candidateRoot := sourceAlpha
      _ = Lean.Expr.abstractFVars candidate.Δ
          (.forallE candidate.name candidate.domain candidate.body
            candidate.binderInfo) :=
        congrArg (Lean.Expr.abstractFVars candidate.Δ) candidate.root_eq
  rw [Lean.Expr.abstractFVars_forallE,
    Lean.Expr.abstractFVars_forallE] at rootAlpha
  simp only [Lean.Expr.forallE.injEq] at rootAlpha
  obtain ⟨_nameAlpha, domainAlpha, _bodyAlpha, _binderAlpha⟩ := rootAlpha
  have consumedAlpha : Lean.Expr.abstractFVars base
      (AddInductive.consumeTypeAnnotations run.translation.domain) =
      Lean.Expr.abstractFVars candidate.Δ candidate.consumed := by
    calc
      Lean.Expr.abstractFVars base
          (AddInductive.consumeTypeAnnotations run.translation.domain) =
          AddInductive.consumeTypeAnnotations
            (Lean.Expr.abstractFVars base run.translation.domain) :=
        (AddInductive.consumeTypeAnnotations_abstractFVars
          base run.translation.domain).symm
      _ = AddInductive.consumeTypeAnnotations
            (Lean.Expr.abstractFVars candidate.Δ candidate.domain) :=
        congrArg AddInductive.consumeTypeAnnotations domainAlpha
      _ = Lean.Expr.abstractFVars candidate.Δ
            (AddInductive.consumeTypeAnnotations candidate.domain) :=
        AddInductive.consumeTypeAnnotations_abstractFVars
          candidate.Δ candidate.domain
      _ = Lean.Expr.abstractFVars candidate.Δ candidate.consumed :=
        congrArg (Lean.Expr.abstractFVars candidate.Δ)
          candidate.annotation_match.symm
  have sourceScope' := sourceScope
  rw [run.translation.source_eq] at sourceScope'
  have domainScope : run.translation.domain.FVarsIn (· ∈ base.fvars) :=
    sourceScope'.1
  have consumedScope :
      (AddInductive.consumeTypeAnnotations run.translation.domain).FVarsIn
        (· ∈ base.fvars) := by
    cases htrace : AddInductive.CandidateTypeAnnotationTrace.build
        run.translation.domain with
    | mk consumed trace =>
        have consumed_eq : consumed =
            AddInductive.consumeTypeAnnotations run.translation.domain := by
          simpa only [htrace] using
            AddInductive.CandidateTypeAnnotationTrace.build_consumed
              run.translation.domain
        simpa only [← consumed_eq] using
          candidateTypeAnnotation_fvarsIn trace domainScope
  have currentNoBV : contextRun.context.vlctx.NoBV :=
    contextRun.context.mlctx.noBV
  have consumedClosed :
      Closed (AddInductive.consumeTypeAnnotations run.translation.domain) 0 := by
    simpa only [currentNoBV] using run.translation.consumed_tr.closed
  have currentConsumedTr : TrExprS env Us contextRun.context.vlctx
      (AddInductive.consumeTypeAnnotations run.translation.domain)
      run.translation.consumed' := by
    simpa only [VContext.TrExprS, venv_eq, lparams_eq] using
      run.translation.consumed_tr
  obtain ⟨baseConsumed, baseConsumedTr⟩ :=
    currentConsumedTr.weakFV'_inv henv referenceLift currentReference
      consumedClosed consumedScope
  have baseConsumedEq : env.IsDefEqU Us.length base.toCtx
      baseConsumed candidate.consumed' :=
    baseConsumedTr.uniqAlpha henv relation baseShape candidateShape
      candidate.consumed_tr consumedAlpha
  have candidateAnnotation := candidate.annotation_run.isDefEqU.of_l
    henv candidate.context_wf.toCtx candidate.domain_type
  have candidateConsumedAtBase : env.HasType Us.length base.toCtx
      candidate.consumed' (.sort candidate.sort) :=
    candidateAnnotation.hasType.2.defeqDFC henv.ordered
      (relation.defeqCtx.symm henv.ordered)
  have baseConsumedCandidate := baseConsumedEq.of_r henv baseWF.toCtx
    candidateConsumedAtBase
  have baseConsumedAtReference :=
    baseConsumedTr.weakFV' henv.ordered referenceLift referenceWF
  have currentConsumedEq :=
    currentConsumedTr.uniq henv currentReference baseConsumedAtReference
  have currentConsumedType : env.HasType Us.length
      contextRun.context.vlctx.toCtx run.translation.consumed'
      (.sort run.sort) := by
    simpa only [venv_eq, lparams_eq] using run.annotation_def.hasType.2
  have currentConsumedReference' := currentConsumedEq.of_l henv
    currentWF.toCtx currentConsumedType
  have currentConsumedReference : env.IsDefEq Us.length
      contextRun.context.vlctx.toCtx run.translation.consumed'
      (baseConsumed.lift' lift) (.sort run.sort) := by
    simpa using currentConsumedReference'
  exact ⟨{
    baseConsumed := baseConsumed
    base_consumed_tr := baseConsumedTr
    base_consumed_candidate := baseConsumedCandidate
    current_consumed_reference := currentConsumedReference }⟩

/-- Compare strict translations of alpha-aligned kernel expressions after
lowering the validator expression to the shared base and re-inserting the
validator-owned reference locals. -/
private theorem alphaLift
    {env : VEnv} {Us : List Name}
    {current base reference candidate : VLCtx} {lift : Lift}
    {currentSource candidateSource : Lean.Expr}
    {currentTarget candidateTarget : VExpr}
    (henv : VEnv.WF env)
    (currentWF : VLCtx.WF env Us.length current)
    (currentNoBV : current.NoBV)
    (currentTr : TrExprS env Us current currentSource currentTarget)
    (baseShape : base.FVarLamOnly)
    (candidateShape : candidate.FVarLamOnly)
    (relation : VLCtx.FVarAlpha env Us.length base candidate)
    (referenceLift : VLCtx.FVLift' base reference 0 lift 0)
    (currentReference : VLCtx.IsDefEq env Us.length current reference)
    (sourceScope : currentSource.FVarsIn (· ∈ base.fvars))
    (candidateTr : TrExprS env Us candidate candidateSource candidateTarget)
    (sourceAlpha : Lean.Expr.abstractFVars base currentSource =
      Lean.Expr.abstractFVars candidate candidateSource) :
    env.IsDefEqU Us.length current.toCtx currentTarget
      (candidateTarget.lift' lift) := by
  have referenceWF : VLCtx.WF env Us.length reference :=
    (currentReference.symm henv.ordered).wf
  have sourceClosed : Closed currentSource 0 := by
    simpa only [currentNoBV] using currentTr.closed
  obtain ⟨baseTarget, baseTr⟩ :=
    currentTr.weakFV'_inv henv referenceLift currentReference sourceClosed
      sourceScope
  have baseCandidate : env.IsDefEqU Us.length base.toCtx
      baseTarget candidateTarget :=
    baseTr.uniqAlpha henv relation baseShape candidateShape candidateTr
      sourceAlpha
  have baseAtReference :=
    baseTr.weakFV' henv.ordered referenceLift referenceWF
  have currentBase := currentTr.uniq henv currentReference baseAtReference
  have candidateAtReference :=
    baseCandidate.weak' henv.ordered referenceLift.toCtx
  have candidateAtCurrent := candidateAtReference.defeqDFC henv.ordered
    ((currentReference.symm henv.ordered).defeqCtx)
  exact currentBase.trans henv currentWF.toCtx (by
    simpa using candidateAtCurrent)

/-- Transport a Theory equality from the producer's alpha context through
the same base/reference embedding into the current validator context. -/
private theorem transportAlphaLift
    {env : VEnv} {Us : List Name}
    {current base reference candidate : VLCtx} {lift : Lift}
    {left right : VExpr}
    (henv : VEnv.WF env)
    (relation : VLCtx.FVarAlpha env Us.length base candidate)
    (referenceLift : VLCtx.FVLift' base reference 0 lift 0)
    (currentReference : VLCtx.IsDefEq env Us.length current reference)
    (proof : env.IsDefEqU Us.length candidate.toCtx left right) :
    env.IsDefEqU Us.length current.toCtx
      (left.lift' lift) (right.lift' lift) := by
  have atBase := proof.defeqDFC henv.ordered
    (relation.defeqCtx.symm henv.ordered)
  have atReference := atBase.weak' henv.ordered referenceLift.toCtx
  exact atReference.defeqDFC henv.ordered
    ((currentReference.symm henv.ordered).defeqCtx)

/-- Consume every Pi node in an exact producer annotation cursor through the
validator's retained index trace.

The base context removes unrelated earlier-family locals, while `reference`
re-inserts them.  After each exact `advance`, both contexts and the positional
alpha relation are extended with the consumed domain chosen at that node. -/
theorem CandidateAnnotationCursor.indexDomainChainAligned
    {env : VEnv} {Us : List Name} {terminalΔ : VLCtx}
    (cursor : CandidateAnnotationCursor env Us terminalΔ)
    (terminalWF : VLCtx.WF env Us.length terminalΔ)
    {nparams : Nat} {stats : AddInductive.InductiveStats}
    {context : AddInductive.Context} {rootSource : Lean.Expr}
    {i nindices rootFuel : Nat}
    {outer : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
      context rootSource i nindices rootFuel}
    {contextRun : CandidateContextRun context}
    (boundary : FamilyParameterIndexBoundary outer contextRun)
    (venv_eq : contextRun.context.venv = env)
    (lparams_eq : contextRun.context.lparams = Us)
    {base reference : VLCtx} {lift : Lift}
    (baseShape : base.FVarLamOnly)
    (relation : VLCtx.FVarAlpha env Us.length base cursor.Δ)
    (referenceLift : VLCtx.FVLift' base reference 0 lift 0)
    {rootBase : VLCtx} {rootLift : Lift}
    (rootReferenceLift : VLCtx.FVLift' rootBase reference 0 rootLift 0)
    {originBase : VLCtx} {originLift : Lift}
    (originReferenceLift :
      VLCtx.FVLift' originBase reference 0 originLift 0)
    (currentReference : VLCtx.IsDefEq env Us.length
      contextRun.context.vlctx reference)
    (sourceScope : boundary.source.FVarsIn (· ∈ base.fvars))
    (sourceAlpha : Lean.Expr.abstractFVars base boundary.source =
      Lean.Expr.abstractFVars cursor.Δ cursor.trace.rootWhnf)
    (whnfFuel : Nat)
    (validatorDepth : context.fuel.recDepth = whnfFuel + 1)
    (candidateDepth : cursor.candidateContext.fuel.recDepth =
      whnfFuel + 1) :
    Nonempty (Sigma fun chain : boundary.IndexDomainChain =>
      { _alignment : chain.EndpointAlignment env Us terminalΔ rootBase
          originBase //
        chain.length = cursor.domains.length }) := by
  rcases cursor with ⟨candidateContext, candidateSource, candidateTrace,
    candidateΔ, candidateDomains, spine, candidateShape, stored,
    annotations, resultLevel, terminalEq, terminalNotForall⟩
  induction spine generalizing nparams stats context rootSource i nindices
      rootFuel outer contextRun boundary base reference lift rootLift
      originLift with
  | terminal node =>
      have henv : VEnv.WF env := by
        simpa only [venv_eq] using contextRun.context.Ewf
      have currentWF : VLCtx.WF env Us.length
          contextRun.context.vlctx := by
        simpa only [venv_eq, lparams_eq] using contextRun.context.Δwf
      have currentNoBV : contextRun.context.vlctx.NoBV :=
        contextRun.context.mlctx.noBV
      have currentSourceTr : TrExprS env Us contextRun.context.vlctx
          boundary.source boundary.source' := by
        simpa only [VContext.TrExprS, venv_eq, lparams_eq] using
          boundary.source_tr
      have candidateResultTr := node.whnf.rhs_tr
      simp only [AddInductive.CandidateExprTrace.terminalResult]
        at terminalEq
      rw [terminalEq] at candidateResultTr
      cases candidateResultTr with
      | sort level_tr =>
        have endpointSort := alphaLift henv currentWF currentNoBV
          currentSourceTr baseShape candidateShape relation referenceLift
          currentReference sourceScope (by exact node.whnf.rhs_tr) (by
            simpa only [AddInductive.CandidateExprTrace.rootWhnf] using
              sourceAlpha)
        let chain : boundary.IndexDomainChain := .done
        exact ⟨⟨chain, {
          base := base
          reference := reference
          lift := lift
          rootLift := rootLift
          originLift := originLift
          base_shape := baseShape
          terminal_shape := candidateShape
          relation := relation
          reference_lift := referenceLift
          root_reference_lift := rootReferenceLift
          origin_reference_lift := originReferenceLift
          current_reference := by
            simpa only [chain,
              FamilyParameterIndexBoundary.IndexDomainChain.endpoint] using
              currentReference
          sort := _
          endpoint_sort := by
            simpa only [chain,
              FamilyParameterIndexBoundary.IndexDomainChain.endpoint,
              VExpr.lift'] using endpointSort }, rfl⟩⟩
  | @forallE candidateContext candidateDomain candidateName
      candidateBinderInfo candidateBody candidateΔ terminalΔ candidateSource
      candidateInferred candidateFresh annotationsNode annotationsEq
      candidateChecked candidateNormalized domainCandidate bodyCandidate
      storedDomain candidateDomains head tail ih =>
      simp only [AddInductive.CandidateExprTrace.storedSpine,
        Bool.and_eq_true] at stored
      rcases annotations with ⟨annotationMatch, tailAnnotations⟩
      obtain ⟨snapshot, snapshotContext, snapshotStored⟩ :=
        head annotationMatch
      subst candidateΔ
      have boundaryForall : boundary.source.isForall = true := by
        have rootShape := congrArg Lean.Expr.isForall sourceAlpha
        rw [Lean.Expr.abstractFVars_isForall,
          Lean.Expr.abstractFVars_isForall] at rootShape
        simpa only [AddInductive.CandidateExprTrace.rootWhnf,
          Lean.Expr.isForall] using rootShape
      obtain ⟨run⟩ := boundary.indexDomainRun_of_alpha snapshot venv_eq
        lparams_eq baseShape candidateShape relation referenceLift
        currentReference sourceScope sourceAlpha boundaryForall
      obtain ⟨preparation⟩ := run.alphaPreparation snapshot venv_eq
        lparams_eq baseShape candidateShape relation referenceLift
        currentReference sourceScope sourceAlpha
      obtain ⟨advance⟩ := run.advance whnfFuel validatorDepth
      have henv : VEnv.WF env := by
        simpa only [venv_eq] using contextRun.context.Ewf
      have candidateTailWF := tail.terminalLift.wf henv terminalWF
      let candidateTailTrace := bodyCandidate
      have currentWF : VLCtx.WF env Us.length
          contextRun.context.vlctx := by
        simpa only [venv_eq, lparams_eq] using contextRun.context.Δwf
      have referenceWF : VLCtx.WF env Us.length reference :=
        (currentReference.symm henv.ordered).wf
      let deps := (AddInductive.consumeTypeAnnotations
        run.translation.domain).fvarsList
      let nextBase : VLCtx :=
        (some (context.freshFVarId, deps),
          .vlam preparation.baseConsumed) :: base
      let nextReference : VLCtx :=
        (some (context.freshFVarId, deps),
          .vlam (preparation.baseConsumed.lift' lift)) :: reference
      have depsSubset : deps ⊆ base.fvars := by
        exact (fvarsIn_iff.mp preparation.base_consumed_tr.fvarsIn).1
      have nextReferenceLift : VLCtx.FVLift' nextBase nextReference 0
          (.consN lift 1) 0 := by
        simpa only [nextBase, nextReference, VLocalDecl.lift',
          VLocalDecl.depth] using referenceLift.cons_fvar
            (context.freshFVarId, deps) (.vlam preparation.baseConsumed)
            depsSubset
      have nextRootReferenceLift : VLCtx.FVLift' rootBase nextReference 0
          (.skipN rootLift 1) 0 := by
        simpa only [nextReference, VLocalDecl.depth] using
          rootReferenceLift.skip_fvar (context.freshFVarId, deps)
            (.vlam (preparation.baseConsumed.lift' lift))
      have nextOriginReferenceLift :
          VLCtx.FVLift' originBase nextReference 0
            (.skipN originLift 1) 0 := by
        simpa only [nextReference, VLocalDecl.depth] using
          originReferenceLift.skip_fvar (context.freshFVarId, deps)
            (.vlam (preparation.baseConsumed.lift' lift))
      have pushedVenv : run.pushContext.context.venv = env := by
        change contextRun.context.venv = env
        exact venv_eq
      have pushedLparams : run.pushContext.context.lparams = Us := by
        change contextRun.context.lparams = Us
        exact lparams_eq
      have pushedWF : VLCtx.WF env Us.length
          run.pushContext.context.vlctx := by
        simpa only [pushedVenv, pushedLparams] using
          run.pushContext.context.Δwf
      have nextCurrentReference : VLCtx.IsDefEq env Us.length
          run.pushContext.context.vlctx nextReference := by
        have concrete : VLCtx.IsDefEq env Us.length
            ((some (context.freshFVarId, deps),
                .vlam run.translation.consumed') ::
              contextRun.context.vlctx)
            nextReference := by
          exact .cons currentReference pushedWF.2.1
            (.vlam preparation.current_consumed_reference)
        change VLCtx.IsDefEq env Us.length
          ((some (context.freshFVarId, deps),
              .vlam run.translation.consumed') ::
            contextRun.context.vlctx) nextReference
        exact concrete
      have nextRelation : VLCtx.FVarAlpha env Us.length nextBase
          ((some (candidateContext.freshFVarId,
              annotationsNode.consumed.fvarsList),
            .vlam storedDomain) :: snapshot.Δ) := by
        rw [← snapshotStored]
        exact .cons relation (.vlam
          preparation.base_consumed_candidate)
      have nextBaseShape : nextBase.FVarLamOnly := by
        exact .cons baseShape
      have nextCandidateShape : VLCtx.FVarLamOnly
          ((some (candidateContext.freshFVarId,
              annotationsNode.consumed.fvarsList),
            VLocalDecl.vlam storedDomain) :: snapshot.Δ) := by
        exact .cons candidateShape
      have currentSourceScope := sourceScope
      rw [run.translation.source_eq] at currentSourceScope
      have validatorBodyScope : run.translation.body.FVarsIn
          (· ∈ base.fvars) := currentSourceScope.2
      have freshBase : context.freshFVarId ∉ base.fvars := by
        intro present
        have presentReference : context.freshFVarId ∈ reference.fvars :=
          referenceLift.fvars_sublist.subset present
        have presentCurrent : context.freshFVarId ∈
            contextRun.context.vlctx.fvars := by
          rw [currentReference.fvars]
          exact presentReference
        exact (pushedWF.2.1 _ _ rfl).1 presentCurrent
      have validatorBodyAvoid : run.translation.body.FVarsIn
          (· ≠ context.freshFVarId) := by
        exact validatorBodyScope.mono (by
          intro fv member equal
          subst fv
          exact freshBase member)
      have freshCandidate : candidateContext.freshFVarId ∉
          snapshot.Δ.fvars := by
        exact (candidateTailWF.2.1 _ _ rfl).1
      have snapshotRoot := snapshot.root_eq
      simp only [Lean.Expr.forallE.injEq] at snapshotRoot
      obtain ⟨_snapshotName, _snapshotDomain, snapshotBody,
        _snapshotBinder⟩ := snapshotRoot
      have candidateBodyScope : candidateBody.FVarsIn
          (· ∈ snapshot.Δ.fvars) := by
        simpa only [snapshotBody] using snapshot.body_fvars
      have candidateBodyAvoid : candidateBody.FVarsIn
          (· ≠ candidateContext.freshFVarId) := by
        exact candidateBodyScope.mono (by
          intro fv member equal
          subst fv
          exact freshCandidate member)
      have rootAlpha : Lean.Expr.abstractFVars base
          (.forallE run.translation.name run.translation.domain
            run.translation.body run.translation.binderInfo) =
          Lean.Expr.abstractFVars snapshot.Δ
            (.forallE candidateName candidateDomain candidateBody
              candidateBinderInfo) := by
        calc
          _ = Lean.Expr.abstractFVars base boundary.source :=
            congrArg (Lean.Expr.abstractFVars base)
              run.translation.source_eq.symm
          _ = Lean.Expr.abstractFVars snapshot.Δ
              (AddInductive.CandidateExprTrace.forallE candidateContext
                candidateSource candidateInferred candidateName
                candidateDomain candidateBody candidateBinderInfo
                candidateFresh annotationsNode annotationsEq
                candidateChecked candidateNormalized domainCandidate
                candidateTailTrace).rootWhnf := sourceAlpha
          _ = _ := rfl
      rw [Lean.Expr.abstractFVars_forallE,
        Lean.Expr.abstractFVars_forallE] at rootAlpha
      simp only [Lean.Expr.forallE.injEq] at rootAlpha
      obtain ⟨_alphaName, _alphaDomain, bodyAlpha,
        _alphaBinder⟩ := rootAlpha
      have preWhnfAlpha : Lean.Expr.abstractFVars nextBase
          (run.translation.body.instantiate1 context.freshExpr) =
          Lean.Expr.abstractFVars
            ((some (candidateContext.freshFVarId,
              annotationsNode.consumed.fvarsList),
              .vlam storedDomain) :: snapshot.Δ)
            (candidateBody.instantiate1 candidateContext.freshExpr) := by
        calc
          _ = Lean.Expr.abstractFVarsAux 1 base.fvars
              run.translation.body := by
            exact Lean.Expr.abstractFVars_cons_instantiate1
              validatorBodyAvoid
          _ = Lean.Expr.abstractFVarsAux 1 snapshot.Δ.fvars
              candidateBody := bodyAlpha
          _ = _ := (Lean.Expr.abstractFVars_cons_instantiate1
            candidateBodyAvoid).symm
      cases tail with
      | terminal node =>
          have validatorInputScope :
              (run.translation.body.instantiate1
                context.freshExpr).FVarsIn (· ∈ nextBase.fvars) := by
            have bodyScope : run.translation.body.FVarsIn
                (· ∈ nextBase.fvars) :=
              validatorBodyScope.mono (by
                intro fv member
                simp only [nextBase, VLCtx.fvars]
                exact .tail _ member)
            have freshScope : context.freshExpr.FVarsIn
                (· ∈ nextBase.fvars) := by
              simp [AddInductive.Context.freshExpr, nextBase, VLCtx.fvars,
                FVarsIn]
            simpa only [Lean.Expr.instantiate1_eq] using
              bodyScope.instantiate1 freshScope
          have validatorInputTr : TrExprS env Us
              run.pushContext.context.vlctx
              (run.translation.body.instantiate1 context.freshExpr)
              advance.body' := by
            simpa only [VContext.TrExprS, pushedVenv, pushedLparams] using
              advance.body_tr
          have currentNoBV : run.pushContext.context.vlctx.NoBV :=
            run.pushContext.context.mlctx.noBV
          have inputAlpha := alphaLift henv pushedWF currentNoBV
            validatorInputTr nextBaseShape nextCandidateShape nextRelation
            nextReferenceLift nextCurrentReference validatorInputScope
            node.whnf.lhs_tr preWhnfAlpha
          obtain ⟨validatorWhnf⟩ := advance.whnf
          have candidateResultTr := node.whnf.rhs_tr
          simp only [AddInductive.CandidateExprTrace.terminalResult]
            at terminalEq
          rw [terminalEq] at candidateResultTr
          cases candidateResultTr with
          | sort level_tr =>
            have candidateWhnf := transportAlphaLift henv nextRelation
              nextReferenceLift nextCurrentReference node.whnf.isDefEqU
            have inputToSort := inputAlpha.trans henv pushedWF.toCtx
              candidateWhnf
            have validatorWhnfDef : env.IsDefEqU Us.length
                run.pushContext.context.vlctx.toCtx advance.body'
                advance.view' := by
              simpa only [pushedVenv, pushedLparams] using
                validatorWhnf.isDefEqU
            have viewToSort := validatorWhnfDef.symm.trans henv
              pushedWF.toCtx inputToSort
            let tailChain : advance.toBoundary.IndexDomainChain := .done
            let chain : boundary.IndexDomainChain :=
              .step run advance tailChain
            exact ⟨⟨chain, {
              base := nextBase
              reference := nextReference
              lift := .consN lift 1
              rootLift := .skipN rootLift 1
              originLift := .skipN originLift 1
              base_shape := nextBaseShape
              terminal_shape := nextCandidateShape
              relation := nextRelation
              reference_lift := nextReferenceLift
              root_reference_lift := nextRootReferenceLift
              origin_reference_lift := nextOriginReferenceLift
              current_reference := by
                simpa only [chain, tailChain,
                  FamilyParameterIndexBoundary.IndexDomainChain.endpoint] using
                  nextCurrentReference
              sort := _
              endpoint_sort := by
                simpa only [chain, tailChain,
                  FamilyParameterIndexBoundary.IndexDomainChain.endpoint,
                  FamilyParameterIndexBoundary.IndexDomainAdvance.toBoundary,
                  VExpr.lift'] using viewToSort }, rfl⟩⟩
      | forallE nextDomainCandidate nextBodyCandidate nextStoredDomain
          nextDomains nextHead nextTail =>
          have tailStored := stored.2
          simp only [AddInductive.CandidateExprTrace.storedSpine,
            Bool.and_eq_true] at tailStored
          have candidateInputForall :
              (candidateBody.instantiate1
                candidateContext.freshExpr).isForall = true :=
            AddInductive.CandidateWhnfStep.isForall_of_structuralEq_forall
              tailStored.1
          have validatorInputForall :
              (run.translation.body.instantiate1
                context.freshExpr).isForall = true := by
            have shapeEq := congrArg Lean.Expr.isForall preWhnfAlpha
            simpa only [Lean.Expr.abstractFVars_isForall,
              candidateInputForall] using shapeEq
          have nextValidatorDepth :
              (context.pushLocalDecl run.translation.name
                run.translation.binderInfo
                (AddInductive.consumeTypeAnnotations
                  run.translation.domain)).fuel.recDepth = whnfFuel + 1 := by
            simpa [AddInductive.Context.pushLocalDecl] using validatorDepth
          have validatorViewEq : advance.view =
              run.translation.body.instantiate1 context.freshExpr :=
            AddInductive.CandidateWhnfStep.result_eq_of_source_isForall
              advance.whnf_valid whnfFuel nextValidatorDepth
              validatorInputForall
          have nextCandidateDepth :
              (candidateContext.pushLocalDecl candidateName
                candidateBinderInfo annotationsNode.consumed).fuel.recDepth =
                whnfFuel + 1 := by
            simpa [AddInductive.Context.pushLocalDecl] using candidateDepth
          have candidateViewEq : candidateTailTrace.rootWhnf =
              candidateBody.instantiate1 candidateContext.freshExpr :=
            AddInductive.CandidateWhnfStep.result_eq_of_source_isForall
              candidateTailTrace.rootWhnf_valid whnfFuel nextCandidateDepth
              candidateInputForall
          have nextSourceAlpha : Lean.Expr.abstractFVars nextBase
              advance.toBoundary.source =
              Lean.Expr.abstractFVars
                ((some (candidateContext.freshFVarId,
                  annotationsNode.consumed.fvarsList),
                  .vlam storedDomain) :: snapshot.Δ)
                candidateTailTrace.rootWhnf := by
            rw [show advance.toBoundary.source = advance.view by rfl,
              validatorViewEq, candidateViewEq]
            exact preWhnfAlpha
          have nextSourceScope : advance.toBoundary.source.FVarsIn
              (· ∈ nextBase.fvars) := by
            rw [show advance.toBoundary.source = advance.view by rfl,
              validatorViewEq]
            have bodyScope : run.translation.body.FVarsIn
                (· ∈ nextBase.fvars) :=
              validatorBodyScope.mono (by
                intro fv member
                simp only [nextBase, VLCtx.fvars]
                exact .tail _ member)
            have freshScope : context.freshExpr.FVarsIn
                (· ∈ nextBase.fvars) := by
              simp [AddInductive.Context.freshExpr, nextBase, VLCtx.fvars,
                FVarsIn]
            simpa only [Lean.Expr.instantiate1_eq] using
              bodyScope.instantiate1 freshScope
          have nextValidatorVenv :
              run.pushContext.context.venv = env := pushedVenv
          have nextValidatorLparams :
              run.pushContext.context.lparams = Us := pushedLparams
          obtain ⟨⟨tailChain, tailAlignment, tailLength⟩⟩ :=
            ih terminalWF advance.toBoundary
            nextValidatorVenv nextValidatorLparams nextBaseShape
            nextReferenceLift nextRootReferenceLift nextOriginReferenceLift
            nextCurrentReference
            nextSourceScope
            nextValidatorDepth nextCandidateShape stored.2 tailAnnotations
            terminalEq terminalNotForall nextRelation nextSourceAlpha
            nextCandidateDepth
          let chain : boundary.IndexDomainChain :=
            .step run advance tailChain
          exact ⟨⟨chain, {
            base := tailAlignment.base
            reference := tailAlignment.reference
            lift := tailAlignment.lift
            rootLift := tailAlignment.rootLift
            originLift := tailAlignment.originLift
            base_shape := tailAlignment.base_shape
            terminal_shape := tailAlignment.terminal_shape
            relation := tailAlignment.relation
            reference_lift := tailAlignment.reference_lift
            root_reference_lift := tailAlignment.root_reference_lift
            origin_reference_lift := tailAlignment.origin_reference_lift
            current_reference := by
              simpa only [chain,
                FamilyParameterIndexBoundary.IndexDomainChain.endpoint] using
                tailAlignment.current_reference
            sort := tailAlignment.sort
            endpoint_sort := by
              simpa only [chain,
                FamilyParameterIndexBoundary.IndexDomainChain.endpoint] using
                tailAlignment.endpoint_sort }, by
              simpa only [chain,
                FamilyParameterIndexBoundary.IndexDomainChain.length,
                List.length_cons] using
                congrArg (fun length => length + 1) tailLength⟩⟩

/-- Compatibility projection of the endpoint-aligned traversal. -/
theorem CandidateAnnotationCursor.indexDomainChain
    {env : VEnv} {Us : List Name} {terminalΔ : VLCtx}
    (cursor : CandidateAnnotationCursor env Us terminalΔ)
    (terminalWF : VLCtx.WF env Us.length terminalΔ)
    {nparams : Nat} {stats : AddInductive.InductiveStats}
    {context : AddInductive.Context} {rootSource : Lean.Expr}
    {i nindices rootFuel : Nat}
    {outer : AddInductive.FamilyTypeParameterComparisonTrace nparams stats
      context rootSource i nindices rootFuel}
    {contextRun : CandidateContextRun context}
    (boundary : FamilyParameterIndexBoundary outer contextRun)
    (venv_eq : contextRun.context.venv = env)
    (lparams_eq : contextRun.context.lparams = Us)
    {base reference : VLCtx} {lift : Lift}
    (baseShape : base.FVarLamOnly)
    (relation : VLCtx.FVarAlpha env Us.length base cursor.Δ)
    (referenceLift : VLCtx.FVLift' base reference 0 lift 0)
    (currentReference : VLCtx.IsDefEq env Us.length
      contextRun.context.vlctx reference)
    (sourceScope : boundary.source.FVarsIn (· ∈ base.fvars))
    (sourceAlpha : Lean.Expr.abstractFVars base boundary.source =
      Lean.Expr.abstractFVars cursor.Δ cursor.trace.rootWhnf)
    (whnfFuel : Nat)
    (validatorDepth : context.fuel.recDepth = whnfFuel + 1)
    (candidateDepth : cursor.candidateContext.fuel.recDepth =
      whnfFuel + 1) :
    Nonempty boundary.IndexDomainChain := by
  obtain ⟨⟨chain, _alignment, _length⟩⟩ :=
    cursor.indexDomainChainAligned terminalWF boundary venv_eq lparams_eq
      baseShape relation referenceLift referenceLift referenceLift
      currentReference
      sourceScope sourceAlpha whnfFuel validatorDepth candidateDepth
  exact ⟨chain⟩

/--
info: 'Lean4Lean.TypeChecker.FamilyParameterIndexBoundary.IndexDomainRun.alphaPreparation' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms
  TypeChecker.FamilyParameterIndexBoundary.IndexDomainRun.alphaPreparation

/--
info: 'Lean4Lean.TypeChecker.CandidateAnnotationCursor.indexDomainChainAligned' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateAnnotationCursor.indexDomainChainAligned

/--
info: 'Lean4Lean.TypeChecker.CandidateAnnotationCursor.indexDomainChain' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateAnnotationCursor.indexDomainChain

/--
info: 'Lean4Lean.TypeChecker.FamilyParameterIndexBoundary.IndexDomainChain.EndpointAlignment.terminal' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Expr.eqv_eq,
 Level.instLawfulBEqLevel,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms
  TypeChecker.FamilyParameterIndexBoundary.IndexDomainChain.EndpointAlignment.terminal

/--
info: 'Lean4Lean.TypeChecker.FamilyParameterIndexBoundary.indexDomainRun_of_alpha' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms
  TypeChecker.FamilyParameterIndexBoundary.indexDomainRun_of_alpha

/--
info: 'Lean4Lean.TypeChecker.CandidateAnnotationSpine.snapshotAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateAnnotationSpine.snapshotAt

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

/-- A checker-produced telescope certificate has the same number of raw and
stored binders. -/
theorem TelDefEqEvidence.length_eq
    (run : TelDefEqEvidence env U Γ As As') :
    As.length = As'.length :=
  run.telDefEq.length_eq

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
theorem TelResultDefEqEvidence.telescope :
    TelResultDefEqEvidence env U Γ rawBinders viewBinders
      rawResult viewResult resultType →
      TelDefEqEvidence env U Γ rawBinders viewBinders
  | .terminal _ => .nil
  | .forallE domain tail => .cons domain tail.telescope

/-- Terminal component, in the context generated by all raw binders. -/
theorem TelResultDefEqEvidence.result :
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
theorem TelDefEqEvidence.ofTelDefEq :
    ∀ {Γ As As'}, env.TelDefEq U Γ As As' →
      TelDefEqEvidence env U Γ As As'
  | _, [], [], _ => .nil
  | _, _ :: _, _ :: _, ⟨⟨_, head⟩, tail⟩ =>
    .cons (.ofDefEq head) (TelDefEqEvidence.ofTelDefEq tail)

/-- Retain an exact prefix of a checker-produced telescope certificate. -/
theorem TelDefEqEvidence.take
    (run : TelDefEqEvidence env U Γ As As') (n : Nat) :
    TelDefEqEvidence env U Γ (As.take n) (As'.take n) :=
  .ofTelDefEq (run.telDefEq.take n)

/-- Drop an aligned prefix while retaining the raw telescope context selected
by the checker. -/
theorem TelDefEqEvidence.drop
    (run : TelDefEqEvidence env U Γ As As') (n : Nat) :
    TelDefEqEvidence env U ((As.take n).reverse ++ Γ)
      (As.drop n) (As'.drop n) :=
  .ofTelDefEq (run.telDefEq.drop n)

/-- Weakening reifies a transported Theory telescope back into explicit
pointwise evidence. -/
theorem TelDefEqEvidence.weakN
    (run : TelDefEqEvidence env U Γ As As')
    (ord : env.Ordered) (W : Ctx.LiftN n k Γ Γ') :
    TelDefEqEvidence env U Γ'
      (VExpr.liftTelN n As k) (VExpr.liftTelN n As' k) :=
  .ofTelDefEq (run.telDefEq.weakN ord W)

/-- Substitute one typed term through both surfaces of a checker-produced
telescope certificate. -/
theorem TelDefEqEvidence.instN
    (run : TelDefEqEvidence env U Γ₁ As As')
    (ord : env.Ordered)
    (term : env.HasType U Γ₀ e₀ A₀)
    (context : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ) :
    TelDefEqEvidence env U Γ
      (VExpr.instTelN e₀ As k) (VExpr.instTelN e₀ As' k) :=
  .ofTelDefEq (run.telDefEq.instN ord term context)

/-- Move a checker-produced telescope between definitionally equal base
contexts without changing either telescope surface. -/
theorem TelDefEqEvidence.defeqDFC
    (run : TelDefEqEvidence env U Γ₁ As As')
    (ord : env.Ordered)
    (context : env.IsDefEqCtx U Γ₀ Γ₁ Γ₂) :
    TelDefEqEvidence env U Γ₂ As As' :=
  .ofTelDefEq (run.telDefEq.defeqDFC ord context)

/-- Transport a checker-produced telescope certificate through environment
growth. -/
theorem TelDefEqEvidence.mono
    (run : TelDefEqEvidence env U Γ As As') (henv : env ≤ env') :
    TelDefEqEvidence env' U Γ As As' :=
  .ofTelDefEq (run.telDefEq.mono henv)

/-- Transport a complete telescope/result certificate through environment
growth without changing any of its syntactic endpoints. -/
theorem TelResultDefEqEvidence.mono
    (run : TelResultDefEqEvidence env U Γ rawBinders viewBinders
      rawResult viewResult resultType)
    (henv : env ≤ env') :
    TelResultDefEqEvidence env' U Γ rawBinders viewBinders
      rawResult viewResult resultType := by
  induction run with
  | terminal result =>
      exact .terminal (.ofDefEq (result.isDefEq.mono henv))
  | forallE domain tail ih =>
      exact .forallE (.ofDefEq (domain.isDefEq.mono henv)) ih

/-- Combine an independently transformed telescope certificate with its
terminal result certificate. -/
theorem TelResultDefEqEvidence.ofTelescopeResult
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

/-- Transport a telescope/result certificate between semantically equivalent
terminal sort levels.  The binder evidence is unchanged; both the right-hand
sort and the type of the terminal equality move together. -/
theorem TelResultDefEqEvidence.resultSortEquiv
    (run : TelResultDefEqEvidence env U Γ rawBinders viewBinders
      rawResult (.sort left) (.sort (.succ left)))
    (leftWF : left.WF U) (rightWF : right.WF U)
    (levelEq : left ≈ right) :
    TelResultDefEqEvidence env U Γ rawBinders viewBinders
      rawResult (.sort right) (.sort (.succ right)) := by
  apply TelResultDefEqEvidence.ofTelescopeResult run.telescope
  apply DefEqEvidence.ofDefEq
  have typeEq : env.IsDefEq U (rawBinders.reverse ++ Γ)
      (.sort (.succ left)) (.sort (.succ right))
      (.sort (.succ (.succ left))) :=
    .sortDF leftWF rightWF (VLevel.succ_congr levelEq)
  have rawToLeft : env.IsDefEq U (rawBinders.reverse ++ Γ)
      rawResult (.sort left) (.sort (.succ right)) :=
    .defeqDF typeEq run.result.isDefEq
  have leftToRight : env.IsDefEq U (rawBinders.reverse ++ Γ)
      (.sort left) (.sort right) (.sort (.succ right)) :=
    .defeqDF typeEq (.sortDF leftWF rightWF levelEq)
  exact rawToLeft.trans leftToRight

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
    (hctx : env.IsDefEqCtx U Γ₀ Γ₁ Γ₂) :
    ∀ {As As'}, env.TelDefEq U Γ₁ As As' →
      env.TelDefEq U Γ₂ As As'
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨⟨u, head⟩, tail⟩ =>
    ⟨⟨u, head.defeqDFC henv hctx⟩,
      candidateTelDefEq_defeqDFC henv
        (.succ hctx head.hasType.1) tail⟩

private theorem candidateTelDefEq_symm (henv : VEnv.WF env) :
    ∀ {Γ As As'}, OnCtx Γ (env.IsType U) →
      env.TelDefEq U Γ As As' → env.TelDefEq U Γ As' As
  | _, [], [], _, _ => trivial
  | Γ, A :: As, A' :: As', contextWF,
      ⟨⟨u, head⟩, tail⟩ => by
    have headContext : env.IsDefEqCtx U Γ
        (A :: Γ) (A' :: Γ) :=
      .succ .zero head
    have tailAtView : env.TelDefEq U (A' :: Γ) As As' :=
      candidateTelDefEq_defeqDFC henv headContext tail
    exact ⟨⟨u, head.symm⟩,
      candidateTelDefEq_symm henv
        ⟨contextWF, u, head.hasType.2⟩ tailAtView⟩

private theorem candidateTelDefEq_trans (henv : VEnv.WF env) :
    ∀ {Γ As Bs Cs}, OnCtx Γ (env.IsType U) →
      env.TelDefEq U Γ As Bs → env.TelDefEq U Γ Bs Cs →
        env.TelDefEq U Γ As Cs
  | _, [], [], [], _, _, _ => trivial
  | Γ, A :: As, B :: Bs, C :: Cs, contextWF,
      ⟨⟨uAB, headAB⟩, tailAB⟩,
      ⟨⟨uBC, headBC⟩, tailBC⟩ => by
    have headContext : env.IsDefEqCtx U Γ
        (A :: Γ) (B :: Γ) :=
      .succ .zero headAB
    have tailBCAtRaw : env.TelDefEq U (A :: Γ) Bs Cs :=
      candidateTelDefEq_defeqDFC henv (headContext.symm henv) tailBC
    have headAC : env.IsDefEq U Γ A C (.sort uAB) :=
      VEnv.IsDefEq.trans_l henv contextWF headAB headBC
    exact ⟨⟨uAB, headAC⟩,
      candidateTelDefEq_trans henv
        ⟨contextWF, uAB, headAB.hasType.1⟩ tailAB tailBCAtRaw⟩

/-- Reverse a checker-produced dependent telescope equality, transporting
each recursive tail into the preceding view context. -/
theorem TelDefEqEvidence.symm
    (run : TelDefEqEvidence env U Γ As As')
    (henv : VEnv.WF env) (contextWF : OnCtx Γ (env.IsType U)) :
    TelDefEqEvidence env U Γ As' As :=
  .ofTelDefEq (candidateTelDefEq_symm henv contextWF run.telDefEq)

/-- Compose checker-produced dependent telescope equalities.  The middle
telescope is eliminated only after its recursive context has been
transported to the first equality's raw side. -/
theorem TelDefEqEvidence.trans
    (left : TelDefEqEvidence env U Γ As Bs)
    (henv : VEnv.WF env) (contextWF : OnCtx Γ (env.IsType U))
    (right : TelDefEqEvidence env U Γ Bs Cs) :
    TelDefEqEvidence env U Γ As Cs :=
  .ofTelDefEq
    (candidateTelDefEq_trans henv contextWF left.telDefEq right.telDefEq)

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
theorem TelResultDefEqEvidence.replacePrefix
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
  | @terminal Δ context source inferred result source' result' inferred'
      checked normalized node =>
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

/-- Any prefix of a syntactically complete telescope has the requested
length. -/
private theorem candidateTelN_prefix_length
    (source : VExpr) {count total : Nat}
    (count_le : count ≤ total)
    (full : (VExpr.telN total source).length = total) :
    (VExpr.telN count source).length = count := by
  induction count generalizing total source with
  | zero => rfl
  | succ count ih =>
      cases total with
      | zero => omega
      | succ total =>
          cases source <;> simp_all [VExpr.telN]
          exact ih _ count_le full

/-- Syntactic terminal marker used only to recover a telescope from a known
`dropN` endpoint. -/
private def CandidateTerminal : VExpr → Prop
  | .forallE _ _ => False
  | _ => True

/-- The terminal fragment admitted by the executable generation-spine gate
has a non-Pi strict Theory translation.  This is structural: let and metadata
translation recurse to their bodies, while context-selected roots were
excluded by the gate in `AddInductive`. -/
private theorem candidateTerminal_of_generationSource
    (run : TrExprS env Us Δ source source')
    (terminal :
      AddInductive.CandidateExprTrace.generationTerminalSource source = true) :
    CandidateTerminal source' := by
  induction run <;>
    simp_all [AddInductive.CandidateExprTrace.generationTerminalSource,
      CandidateTerminal]

/-- A fresh kernel local is absent from the corresponding explicit local
inventory. -/
private theorem localContextFresh_not_mem_fvars
    {lctx : LocalContext} {fv : FVarId}
    (wf : lctx.WF) (fresh : lctx.find? fv = none) :
    fv ∉ lctx.fvars := by
  rw [wf.find?_eq_find?_toList, List.find?_eq_none] at fresh
  intro member
  obtain ⟨decl, declMember, idEq⟩ := List.mem_map.mp member
  have absent := fresh decl declMember
  rw [idEq] at absent
  simp at absent

/-- Strict source translation and the complete syntactic generation gate
determine the full Theory Pi-telescope length without interpreting WHNF or
definitional equality.

The kernel local context is tracked only through its free-variable inventory.
At a stored Pi, annotation peeling cannot introduce free variables, so the
raw Theory domain can be used to extend the translation context even when the
candidate checker stored a definitionally equal annotation-consumed domain. -/
private theorem candidateGenerationSpineLengthAux
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    (trace : AddInductive.CandidateExprTrace candidateContext source)
    {rawΔ : VLCtx} {rawSource' : VExpr}
    (henv : VEnv.WF env)
    (rawWF : VLCtx.WF env Us.length rawΔ)
    (lctxWF : candidateContext.lctx.WF)
    (lctxFVars : candidateContext.lctx.fvars = rawΔ.fvars)
    (rawSource_tr : TrExprS env Us rawΔ source rawSource')
    (generation : trace.generationSpine = true) :
    trace.spineLength = (VInductDecl.ctorFields rawSource').length := by
  induction trace generalizing rawΔ rawSource' with
  | @terminal context terminalSourceExpr inferred result checked normalized =>
      have terminalSource :
          AddInductive.CandidateExprTrace.generationTerminalSource
              terminalSourceExpr = true := by
        simpa only [AddInductive.CandidateExprTrace.generationSpine] using
          generation
      have terminal := candidateTerminal_of_generationSource rawSource_tr
        terminalSource
      cases rawSource' <;>
        simp_all [AddInductive.CandidateExprTrace.spineLength,
          CandidateTerminal, VInductDecl.ctorFields]
  | @forallE context source inferred name domain body binderInfo fresh
      annotations annotationsEq checked normalized domainCandidate
      bodyCandidate domainIH bodyIH =>
    simp only [AddInductive.CandidateExprTrace.generationSpine,
      Bool.and_eq_true] at generation
    obtain ⟨sourceEq, bodyGeneration⟩ := generation
    have alignedSource_tr : TrExprS env Us rawΔ
        (.forallE name domain body binderInfo) rawSource' :=
      rawSource_tr.eqv (Expr.structuralEq_eqv sourceEq)
    let @TrExprS.forallE _ _ rawDomain rawBody _ _ _ _ _
        rawDomainType rawBodyType rawDomain_tr rawBody_tr := alignedSource_tr
    have freshRaw : context.freshFVarId ∉ rawΔ.fvars := by
      rw [← lctxFVars]
      exact localContextFresh_not_mem_fvars lctxWF fresh
    have consumedFVars :
        annotations.consumed.fvarsList ⊆ rawΔ.fvars :=
      (fvarsIn_iff.mp
        (candidateTypeAnnotation_fvarsIn annotations.trace
          rawDomain_tr.fvarsIn)).1
    have rawFresh :
        ∀ fv deps,
          some (context.freshFVarId, annotations.consumed.fvarsList) =
              some (fv, deps) →
            fv ∉ rawΔ.fvars ∧ deps ⊆ rawΔ.fvars := by
      intro fv deps heq
      cases heq
      exact ⟨freshRaw, consumedFVars⟩
    let rawBodyΔ : VLCtx :=
      (some (context.freshFVarId, annotations.consumed.fvarsList),
        .vlam rawDomain) :: rawΔ
    have rawBodyWF : VLCtx.WF env Us.length rawBodyΔ :=
      ⟨rawWF, rawFresh, rawDomainType⟩
    have nextLctxWF :
        (context.pushLocalDecl name binderInfo annotations.consumed).lctx.WF := by
      simpa only [AddInductive.Context.pushLocalDecl] using
        LocalContext.WF.mkLocalDecl lctxWF fresh
    have nextLctxFVars :
        (context.pushLocalDecl name binderInfo
            annotations.consumed).lctx.fvars = rawBodyΔ.fvars := by
      simpa only [AddInductive.Context.pushLocalDecl, LocalContext.fvars,
        LocalContext.mkLocalDecl_toList lctxWF.decls_wf, List.map_cons,
        LocalDecl.fvarId, rawBodyΔ, VLCtx.fvars_cons_some] using
        congrArg (List.cons context.freshFVarId) lctxFVars
    have rawBodyInst_tr : TrExprS env Us rawBodyΔ
        (body.instantiate1 context.freshExpr) rawBody := by
      simpa only [AddInductive.Context.freshExpr,
        Expr.instantiate1_eq] using
        rawBody_tr.inst_fvar henv.ordered rawBodyWF
    have tailLength := bodyIH rawBodyWF nextLctxWF nextLctxFVars
      rawBodyInst_tr bodyGeneration
    simpa only [AddInductive.CandidateExprTrace.spineLength,
      VInductDecl.ctorFields, List.length_cons, Nat.succ.injEq] using
      tailLength

/-- If dropping `n` binders from a telescope reaches its non-forall terminal,
then taking `n` binders recovers the entire telescope. -/
private theorem candidateTelN_of_dropN_terminal
    {B : VExpr} (hB : CandidateTerminal B) :
    ∀ (As : List VExpr) (n : Nat),
      VExpr.dropN n (VExpr.forallN As B) = B →
      VExpr.telN n (VExpr.forallN As B) = As
  | [], n, _ => by
    cases B <;> cases n <;> simp_all [CandidateTerminal,
      VExpr.forallN, VExpr.dropN, VExpr.telN]
  | A :: As, 0, h => by
    cases B <;> simp_all [CandidateTerminal,
      VExpr.forallN, VExpr.dropN]
  | A :: As, n + 1, h => by
    simp only [VExpr.forallN, VExpr.telN,
      List.cons.injEq, true_and]
    exact candidateTelN_of_dropN_terminal hB As n (by
      simpa only [VExpr.forallN, VExpr.dropN] using h)

private theorem candidateTerminal_appN_app (f a : VExpr) :
    ∀ args, CandidateTerminal (VExpr.appN (.app f a) args)
  | [] => trivial
  | b :: args => candidateTerminal_appN_app (.app f a) b args

private theorem candidateTerminal_appN_const
    (name : Name) (levels : List VLevel) :
    ∀ args, CandidateTerminal (VExpr.appN (.const name levels) args)
  | [] => trivial
  | a :: args => candidateTerminal_appN_app (.const name levels) a args

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
    ∃ rawBinders storedBinders viewBinders rawResult viewResult resultType,
      rawSource' = VExpr.forallN rawBinders rawResult ∧
      view' = VExpr.forallN viewBinders viewResult ∧
      TelDefEqEvidence env Us.length rawΔ.toCtx
        rawBinders storedBinders ∧
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
    exact ⟨[], [], [], rawSource', _, _, rfl, rfl, .nil,
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
      rawSource_tr.eqv (Expr.structuralEq_eqv sourceEq)
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
    obtain ⟨rawBinders, storedBinders, viewBinders, rawResult, viewResult,
        resultType, rawBodyEq, viewBodyEq, storedTail, tail, tailLength⟩ :=
      bodyIH bodyAligned bodyContextEq rawBodyInst_tr
    refine ⟨rawDomain :: rawBinders, storedDomain' :: storedBinders,
      domainView' :: viewBinders, rawResult, viewResult, resultType,
      ?_, ?_, ?_, ?_, ?_⟩
    · simp only [VExpr.forallN, rawBodyEq]
    · simp only [VExpr.forallN, viewBodyEq]
    · exact .cons (.ofDefEq rawToStored) (by
        simpa only [rawBodyΔ, VLCtx.toCtx] using storedTail)
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
  obtain ⟨rawBinders, storedBinders, viewBinders, rawResult, viewResult,
      resultType, rawEq, viewEq, _storedEvidence, evidence, rawLength⟩ :=
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

/-- Extract the annotation-consumed telescope selected by the candidate's
retained equality executions.

Unlike the normalized view telescope, this surface is exactly the sequence
of local-domain translations used by `Context.pushLocalDecl`.  The raw side
remains the source-indexed Pi telescope, so consumers may `take`, `drop`,
instantiate, or relocate the certificate without identifying an annotated
kernel domain with its consumed syntax. -/
theorem CandidateExprRun.annotationSpineEvidence
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {Δ : VLCtx} {source' view' inferred' : VExpr}
    (run : CandidateExprRun env Us trace Δ source' view' inferred')
    (aligned : trace.storedSpine = true) :
    ∃ storedBinders,
      TelDefEqEvidence env Us.length Δ.toCtx
          (VExpr.telN trace.spineLength source') storedBinders ∧
        storedBinders.length = trace.spineLength := by
  have henv : VEnv.WF env := by
    cases run with
    | terminal node =>
      simpa only [node.check.venv_eq] using node.check.context.Ewf
    | forallE _ _ _ _ node =>
      simpa only [node.check.venv_eq] using node.check.context.Ewf
  obtain ⟨rawBinders, storedBinders, viewBinders, rawResult, viewResult,
      resultType, rawEq, viewEq, storedEvidence, evidence, rawLength⟩ :=
    run.spineEvidenceAux aligned
      (.refl henv run.context_wf) run.source_tr
  have rawTel : VExpr.telN trace.spineLength source' = rawBinders := by
    rw [rawEq, ← rawLength]
    exact candidateTelN_forallN_length rawBinders rawResult
  have storedLength : storedBinders.length = trace.spineLength :=
    storedEvidence.length_eq.symm.trans rawLength
  exact ⟨storedBinders, by simpa only [rawTel] using storedEvidence,
    storedLength⟩

/-- Recursive worker joining the annotation-consumed telescope to the exact
verified terminal context built from those same stored domains. -/
private theorem CandidateExprRun.annotationSpineContextAux
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {Δ : VLCtx} {source' view' inferred' : VExpr}
    (run : CandidateExprRun env Us trace Δ source' view' inferred')
    (aligned : trace.storedSpine = true)
    (contextRun : CandidateContextRun candidateContext)
    (venv_eq : contextRun.context.venv = env)
    (lparams_eq : contextRun.context.lparams = Us)
    (vlctx_eq : contextRun.context.vlctx = Δ)
    {rawΔ : VLCtx} {rawSource' : VExpr}
    (contextEq : VLCtx.IsDefEq env Us.length rawΔ Δ)
    (rawSource_tr : TrExprS env Us rawΔ source rawSource') :
    ∃ (rawBinders storedBinders : List VExpr) (rawResult : VExpr)
        (terminalRun : CandidateContextRun trace.terminalContext),
      rawSource' = VExpr.forallN rawBinders rawResult ∧
      TelDefEqEvidence env Us.length rawΔ.toCtx
        rawBinders storedBinders ∧
      rawBinders.length = trace.spineLength ∧
      terminalRun.context.venv = env ∧
      terminalRun.context.lparams = Us ∧
      terminalRun.context.vlctx.toCtx =
        storedBinders.reverse ++ Δ.toCtx ∧
      CandidateAnnotationSpine env Us trace Δ
        terminalRun.context.vlctx storedBinders := by
  induction run generalizing rawΔ rawSource' with
  | @terminal Δ context source inferred result source' result' inferred'
      checked normalized node =>
    let terminalRun : CandidateContextRun
        (AddInductive.CandidateExprTrace.terminal
          context source inferred result checked normalized).terminalContext := by
      simpa only [AddInductive.CandidateExprTrace.terminalContext] using
        contextRun
    have terminalVlctx : terminalRun.context.vlctx = Δ := by
      change contextRun.context.vlctx = Δ
      exact vlctx_eq
    refine ⟨[], [], rawSource', terminalRun, rfl, .nil, rfl,
      venv_eq, lparams_eq, ?_, ?_⟩
    change contextRun.context.vlctx.toCtx = Δ.toCtx
    rw [vlctx_eq]
    rw [terminalVlctx]
    exact .terminal node
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
      rawSource_tr.eqv (Expr.structuralEq_eqv sourceEq)
    let @TrExprS.forallE _ _ rawDomain rawBody _ _ _ _ _
        rawDomainType rawBodyType rawDomain_tr rawBody_tr := alignedSource_tr
    have henv : VEnv.WF env := by
      simpa only [venv_eq] using contextRun.context.Ewf
    have hΔ : VLCtx.WF env Us.length Δ := by
      simpa only [venv_eq, lparams_eq, vlctx_eq] using
        contextRun.context.Δwf
    have hRawΔ := contextEq.wf
    have rawToDomainU :=
      rawDomain_tr.uniq henv contextEq domainRun.source_tr
    have domainTypeRaw :=
      domainType.defeqDFC henv (contextEq.symm henv).defeqCtx
    have rawToDomain :=
      rawToDomainU.of_r henv hRawΔ.toCtx domainTypeRaw
    have annotationDef :=
      annotationsRun.isDefEqU.of_l henv hΔ.toCtx domainType
    have annotationDefRaw :=
      annotationDef.defeqDFC henv (contextEq.symm henv).defeqCtx
    have rawToStored := rawToDomain.trans annotationDefRaw
    have storedDomain_tr : contextRun.context.TrExprS
        annotations.consumed storedDomain' := by
      simpa only [VContext.TrExprS, venv_eq, lparams_eq, vlctx_eq] using
        annotationsRun.rhs_tr
    let nextContextRun := contextRun.pushLocalDecl name binderInfo
      annotations.consumed fresh storedDomain' storedDomain_tr (by
        change contextRun.context.venv.IsType
          contextRun.context.lparams.length
          contextRun.context.vlctx.toCtx storedDomain'
        rw [venv_eq, lparams_eq, vlctx_eq]
        exact ⟨u, annotationDef.hasType.2⟩)
    have nextVenv : nextContextRun.context.venv = env := by
      simp only [nextContextRun, CandidateContextRun.pushLocalDecl_venv,
        venv_eq]
    have nextLparams : nextContextRun.context.lparams = Us := by
      simp only [nextContextRun, CandidateContextRun.pushLocalDecl_lparams,
        lparams_eq]
    have nextVlctx : nextContextRun.context.vlctx = bodyΔ := by
      simp only [nextContextRun, CandidateContextRun.pushLocalDecl_vlctx]
      rw [vlctx_eq, bodyContext]
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
    obtain ⟨rawBinders, storedBinders, rawResult, terminalRun,
        rawBodyEq, storedTail, tailLength, terminalVenv,
        terminalLparams, terminalContextEq, annotationTail⟩ :=
      bodyIH bodyAligned nextContextRun nextVenv nextLparams nextVlctx
        bodyContextEq rawBodyInst_tr
    have annotationHead : annotations.Matches →
        ∃ snapshot : CandidateAnnotationSnapshot env Us
            (.forallE name domain body binderInfo),
          snapshot.Δ = Δ ∧ snapshot.consumed' = storedDomain' := by
      intro annotationMatch
      exact ⟨{
        Δ := Δ
        name := name
        domain := domain
        body := body
        binderInfo := binderInfo
        consumed := annotations.consumed
        domain' := domain'
        consumed' := storedDomain'
        sort := u
        root_eq := rfl
        annotation_match := annotationMatch
        domain_tr := domainRun.source_tr
        body_fvars := node.whnf.rhs_tr.fvarsIn.2
        consumed_tr := annotationsRun.rhs_tr
        domain_type := domainType
        annotation_run := annotationsRun }, rfl, rfl⟩
    have annotationTail' : CandidateAnnotationSpine env Us bodyCandidate
        ((some (context.freshFVarId, annotations.consumed.fvarsList),
          .vlam storedDomain') :: Δ) terminalRun.context.vlctx
        storedBinders := by
      rw [← bodyContext]
      exact annotationTail
    refine ⟨rawDomain :: rawBinders, storedDomain' :: storedBinders,
      rawResult, terminalRun, ?_, ?_, ?_, terminalVenv, terminalLparams,
      ?_, .forallE domainCandidate bodyCandidate storedDomain' storedBinders
        annotationHead annotationTail'⟩
    · simp only [VExpr.forallN, rawBodyEq]
    · exact .cons (.ofDefEq rawToStored) (by
        simpa only [rawBodyΔ, VLCtx.toCtx] using storedTail)
    · simpa only [List.length_cons,
        AddInductive.CandidateExprTrace.spineLength] using
        congrArg Nat.succ tailLength
    · calc
        terminalRun.context.vlctx.toCtx =
            storedBinders.reverse ++ bodyΔ.toCtx := terminalContextEq
        _ = storedBinders.reverse ++ storedDomain' :: Δ.toCtx := by
          rw [bodyContext]
          rfl
        _ = (storedDomain' :: storedBinders).reverse ++ Δ.toCtx := by
          simp only [List.reverse_cons, List.singleton_append,
            List.append_assoc]

/-- The annotation-consumed candidate telescope and the exact verified
terminal context are selected jointly by one recursive semantic run.

In particular, the returned context is not reconstructed from names: its
Theory declarations are definitionally the reverse of the stored telescope
chosen by the candidate's retained annotation equalities. -/
theorem CandidateExprRun.annotationSpineContext
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {Δ : VLCtx} {source' view' inferred' : VExpr}
    (run : CandidateExprRun env Us trace Δ source' view' inferred')
    (aligned : trace.storedSpine = true)
    (contextRun : CandidateContextRun candidateContext)
    (venv_eq : contextRun.context.venv = env)
    (lparams_eq : contextRun.context.lparams = Us)
    (vlctx_eq : contextRun.context.vlctx = Δ) :
    ∃ (terminalRun : CandidateContextRun trace.terminalContext)
        (storedBinders : List VExpr),
      terminalRun.context.venv = env ∧
      terminalRun.context.lparams = Us ∧
      TelDefEqEvidence env Us.length Δ.toCtx
        (VExpr.telN trace.spineLength source') storedBinders ∧
      storedBinders.length = trace.spineLength ∧
      terminalRun.context.vlctx.toCtx =
        storedBinders.reverse ++ Δ.toCtx ∧
      CandidateAnnotationSpine env Us trace Δ
        terminalRun.context.vlctx storedBinders := by
  have henv : VEnv.WF env := by
    simpa only [venv_eq] using contextRun.context.Ewf
  obtain ⟨rawBinders, storedBinders, rawResult, terminalRun,
      rawEq, telescope, rawLength, terminalVenv, terminalLparams,
      terminalContextEq, annotationSpine⟩ :=
    run.annotationSpineContextAux aligned contextRun venv_eq lparams_eq
      vlctx_eq (.refl henv run.context_wf) run.source_tr
  have rawTel : VExpr.telN trace.spineLength source' = rawBinders := by
    rw [rawEq, ← rawLength]
    exact candidateTelN_forallN_length rawBinders rawResult
  have storedLength : storedBinders.length = trace.spineLength :=
    telescope.length_eq.symm.trans rawLength
  exact ⟨terminalRun, storedBinders, terminalVenv, terminalLparams,
    by simpa only [rawTel] using telescope, storedLength,
    terminalContextEq, annotationSpine⟩

/-- A stored candidate spine fixes the exact number of raw and reconstructed
view binders, independently of the terminal result typing witness. -/
theorem CandidateExprRun.spineLengths
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {Δ : VLCtx} {source' view' inferred' : VExpr}
    (run : CandidateExprRun env Us trace Δ source' view' inferred')
    (aligned : trace.storedSpine = true) :
    (VExpr.telN trace.spineLength source').length = trace.spineLength ∧
      (VExpr.telN trace.spineLength view').length = trace.spineLength := by
  have henv : VEnv.WF env := by
    cases run with
    | terminal node =>
      simpa only [node.check.venv_eq] using node.check.context.Ewf
    | forallE _ _ _ _ node =>
      simpa only [node.check.venv_eq] using node.check.context.Ewf
  obtain ⟨rawBinders, storedBinders, viewBinders, rawResult, viewResult,
      resultType, rawEq, viewEq, _storedEvidence, evidence, rawLength⟩ :=
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
  exact ⟨by rw [rawTel, rawLength], by rw [viewTel, viewLength]⟩

/-- Every validator-selected prefix of a stored candidate view contains
exactly the requested number of binders. -/
theorem CandidateExprRun.viewTelN_length_of_le
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {Δ : VLCtx} {source' view' inferred' : VExpr}
    (run : CandidateExprRun env Us trace Δ source' view' inferred')
    (aligned : trace.storedSpine = true)
    (count_le : count ≤ trace.spineLength) :
    (VExpr.telN count view').length = count :=
  candidateTelN_prefix_length view' count_le (run.spineLengths aligned).2

/-- Splitting a Theory expression after any prefix partitions its complete
stored Pi telescope. -/
private theorem candidateCtorFields_split :
    ∀ (count : Nat) (source : VExpr),
      VInductDecl.ctorFields source =
        VExpr.telN count source ++
          VInductDecl.ctorFields (VExpr.dropN count source)
  | 0, _ => rfl
  | _ + 1, .forallE domain body => by
      simp only [VInductDecl.ctorFields, VExpr.telN, VExpr.dropN,
        List.cons_append, List.cons.injEq, true_and]
      exact candidateCtorFields_split _ body
  | _ + 1, .bvar _ | _ + 1, .sort _ | _ + 1, .const _ _ |
      _ + 1, .app _ _ | _ + 1, .lam _ _ => rfl

/-- Structural worker for complete-spine length.

The translated context may replace local declaration types while retaining
the same free-variable inventory.  No definitional-equality uniqueness is
needed: strict translation of each stored Pi exposes one Theory Pi directly,
and the terminal gate excludes a final translated Pi syntactically. -/
private theorem CandidateExprRun.generationSpineLengthAux
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {Δ : VLCtx} {source' view' inferred' : VExpr}
    (run : CandidateExprRun env Us trace Δ source' view' inferred')
    {rawΔ : VLCtx} {rawSource' : VExpr}
    (rawWF : VLCtx.WF env Us.length rawΔ)
    (rawFVars : rawΔ.fvars = Δ.fvars)
    (rawSource_tr : TrExprS env Us rawΔ source rawSource')
    (generation : trace.generationSpine = true) :
    trace.spineLength = (VInductDecl.ctorFields rawSource').length := by
  induction run generalizing rawΔ rawSource' with
  | @terminal Δ context terminalSourceExpr inferred result source' result'
      inferred' checked normalized node =>
      have terminalSource :
          AddInductive.CandidateExprTrace.generationTerminalSource
              terminalSourceExpr = true := by
        simpa only [AddInductive.CandidateExprTrace.generationSpine] using
          generation
      have terminal := candidateTerminal_of_generationSource rawSource_tr
        terminalSource
      cases rawSource' <;>
        simp_all [AddInductive.CandidateExprTrace.spineLength,
          CandidateTerminal, VInductDecl.ctorFields]
  | @forallE domain context name binderInfo Δ source inferred body
      source' domain' body' inferred' domainView' domainInferred'
      storedDomain' bodyΔ storedBody' bodyView' bodyInferred' u v fresh
      checked normalized annotations annotationsEq domainCandidate
      bodyCandidate node domainRun annotationsRun bodyRun domainType bodyType
      bodySource bodyContext domainIH bodyIH =>
    simp only [AddInductive.CandidateExprTrace.generationSpine,
      Bool.and_eq_true] at generation
    obtain ⟨sourceEq, bodyGeneration⟩ := generation
    have alignedSource_tr : TrExprS env Us rawΔ
        (.forallE name domain body binderInfo) rawSource' :=
      rawSource_tr.eqv (Expr.structuralEq_eqv sourceEq)
    let @TrExprS.forallE _ _ rawDomain rawBody _ _ _ _ _
        rawDomainType rawBodyType rawDomain_tr rawBody_tr := alignedSource_tr
    have henv : VEnv.WF env := by
      simpa only [node.check.venv_eq] using node.check.context.Ewf
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
      simpa only [rawFVars] using hfresh
    let rawBodyΔ : VLCtx :=
      (some (context.freshFVarId, annotations.consumed.fvarsList),
        .vlam rawDomain) :: rawΔ
    have rawBodyWF : VLCtx.WF env Us.length rawBodyΔ :=
      ⟨rawWF, rawFresh, rawDomainType⟩
    have rawBodyFVars : rawBodyΔ.fvars = bodyΔ.fvars := by
      rw [bodyContext]
      simp only [rawBodyΔ, VLCtx.fvars_cons_some, rawFVars]
    have rawBodyInst_tr : TrExprS env Us rawBodyΔ
        (body.instantiate1 context.freshExpr) rawBody := by
      simpa only [AddInductive.Context.freshExpr,
        Expr.instantiate1_eq] using
        rawBody_tr.inst_fvar henv.ordered rawBodyWF
    have tailLength := bodyIH rawBodyWF rawBodyFVars rawBodyInst_tr
      bodyGeneration
    simpa only [AddInductive.CandidateExprTrace.spineLength,
      VInductDecl.ctorFields, List.length_cons, Nat.succ.injEq] using
      tailLength

/-- The complete generation-spine gate fixes the candidate count to the full
stored Pi telescope of its strict Theory source. -/
theorem CandidateExprRun.generationSpineLength
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {Δ : VLCtx} {source' view' inferred' : VExpr}
    (run : CandidateExprRun env Us trace Δ source' view' inferred')
    (generation : trace.generationSpine = true) :
    trace.spineLength = (VInductDecl.ctorFields source').length := by
  exact run.generationSpineLengthAux run.context_wf rfl run.source_tr
    generation

/-- The same count is generation's parameter-prefix/remaining-field length
at every requested parameter split. -/
theorem CandidateExprRun.generationSpineLengthAt
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {Δ : VLCtx} {source' view' inferred' : VExpr}
    (run : CandidateExprRun env Us trace Δ source' view' inferred')
    (generation : trace.generationSpine = true) (count : Nat) :
    trace.spineLength =
      (VExpr.telN count source' ++
        VInductDecl.ctorFields (VExpr.dropN count source')).length := by
  rw [← candidateCtorFields_split count source']
  exact run.generationSpineLength generation

/-- The pre-run root input already contains enough strict source and context
translation evidence to determine the complete generation-spine length.  In
particular, this route does not construct the checker-selected semantic view. -/
theorem CandidateExprSemanticRootInput.generationSpineLength
    {env : VEnv} {Us : List Name}
    {source : Expr} {candidate : AddInductive.CandidateExpr source}
    {source' : VExpr}
    (input : CandidateExprSemanticRootInput env Us candidate source')
    (generation : candidate.trace.generationSpine = true) :
    candidate.trace.spineLength =
      (VInductDecl.ctorFields source').length := by
  have contextTr : TrLCtx env Us candidate.context.lctx [] := by
    simpa only [input.venv_eq, input.lparams_eq, input.vlctx_eq,
      input.contextRun.context_lctx,
      input.contextRun.context.lctx_eq] using
      input.contextRun.context.trlctx
  exact candidateGenerationSpineLengthAux candidate.trace
    (by simpa only [input.venv_eq] using input.contextRun.context.Ewf)
    contextTr.wf contextTr.1 contextTr.fvars_eq input.source_tr generation

/-- The source-input form of complete-spine length at an arbitrary parameter
split. -/
theorem CandidateExprSemanticRootInput.generationSpineLengthAt
    {env : VEnv} {Us : List Name}
    {source : Expr} {candidate : AddInductive.CandidateExpr source}
    {source' : VExpr}
    (input : CandidateExprSemanticRootInput env Us candidate source')
    (generation : candidate.trace.generationSpine = true) (count : Nat) :
    candidate.trace.spineLength =
      (VExpr.telN count source' ++
        VInductDecl.ctorFields (VExpr.dropN count source')).length := by
  rw [← candidateCtorFields_split count source']
  exact input.generationSpineLength generation

/--
info: 'Lean4Lean.TypeChecker.CandidateExprSemanticRootInput.generationSpineLengthAt' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.eqv_eq,
 Expr.instantiate1_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms CandidateExprSemanticRootInput.generationSpineLengthAt

/-- Replace only the terminal typing index of a combined certificate. The
telescope and both result endpoints remain definitionally unchanged. -/
theorem TelResultDefEqEvidence.withResult
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
theorem TelResultDefEqEvidence.ofRightType
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

/-- Recover the exact verified candidate context reached at the end of the
main Pi spine.

`CandidateExprRun` retains the semantic context at every recursive node, but
its public indices deliberately mention only the translated local context.
Constructor validation, on the other hand, resumes in the implementation
`Context` returned by the family traversal.  This projection reconnects the
two without reconstructing a local context from names: starting from the
root `CandidateContextRun`, each Pi case repeats the already-certified
annotation equality and the exact `pushLocalDecl` used by the candidate. -/
theorem CandidateExprRun.terminalContextRun
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {Δ : VLCtx} {source' view' inferred' : VExpr}
    (run : CandidateExprRun env Us trace Δ source' view' inferred')
    (contextRun : CandidateContextRun candidateContext)
    (venv_eq : contextRun.context.venv = env)
    (lparams_eq : contextRun.context.lparams = Us)
    (vlctx_eq : contextRun.context.vlctx = Δ) :
    ∃ terminalRun : CandidateContextRun trace.terminalContext,
      terminalRun.context.venv = env ∧
      terminalRun.context.lparams = Us := by
  induction run with
  | terminal node =>
      exact ⟨by
          simpa only [AddInductive.CandidateExprTrace.terminalContext] using
            contextRun,
        venv_eq, lparams_eq⟩
  | @forallE domain context name binderInfo Δ source inferred body
      source' domain' body' inferred' domainView' domainInferred'
      storedDomain' bodyΔ storedBody' bodyView' bodyInferred' u v fresh
      checked normalized annotations annotationsEq domainCandidate
      bodyCandidate node domainRun annotationsRun bodyRun domainType bodyType
      bodySource bodyContext domainIH bodyIH =>
    have storedDomain_tr : contextRun.context.TrExprS
        annotations.consumed storedDomain' := by
      simpa only [VContext.TrExprS, venv_eq, lparams_eq, vlctx_eq] using
        annotationsRun.rhs_tr
    have storedDomain_type : env.IsType Us.length Δ.toCtx storedDomain' := by
      have bodyWF := bodyRun.context_wf
      rw [bodyContext] at bodyWF
      exact bodyWF.2.2
    let nextContextRun := contextRun.pushLocalDecl name binderInfo
      annotations.consumed fresh storedDomain' storedDomain_tr (by
        change contextRun.context.venv.IsType
          contextRun.context.lparams.length
          contextRun.context.vlctx.toCtx storedDomain'
        rw [venv_eq, lparams_eq, vlctx_eq]
        exact storedDomain_type)
    have nextVenv : nextContextRun.context.venv = env := by
      simp only [nextContextRun, CandidateContextRun.pushLocalDecl_venv,
        venv_eq]
    have nextLparams : nextContextRun.context.lparams = Us := by
      simp only [nextContextRun, CandidateContextRun.pushLocalDecl_lparams,
        lparams_eq]
    have nextVlctx : nextContextRun.context.vlctx = bodyΔ := by
      simp only [nextContextRun, CandidateContextRun.pushLocalDecl_vlctx]
      rw [vlctx_eq, bodyContext]
    obtain ⟨terminalRun, terminalVenv, terminalLparams⟩ :=
      bodyIH nextContextRun nextVenv nextLparams nextVlctx
    exact ⟨by
        simpa only [AddInductive.CandidateExprTrace.terminalContext] using
          terminalRun,
      terminalVenv, terminalLparams⟩

/--
info: 'Lean4Lean.TypeChecker.CandidateExprRun.terminalContextRun' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.eqv_eq,
 Level.instLawfulBEqLevel,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms CandidateExprRun.terminalContextRun

private theorem candidateFVLift'_comp
    (left : VLCtx.FVLift' Δ₁ Δ₂ 0 (.skipN .refl n₁) 0)
    (right : VLCtx.FVLift' Δ₂ Δ₃ 0 (.skipN .refl n₂) 0) :
    VLCtx.FVLift' Δ₁ Δ₃ 0 (.skipN .refl (n₁ + n₂)) 0 := by
  simpa only [Lift.comp_skipN, Lift.comp, Lift.skipN_skipN] using
    left.comp right

/-- Recover the terminal implementation context together with the exact
candidate-view telescope occupying the same local positions.

The two `VLCtx`s keep the identical free-variable metadata and declaration
kinds.  Their declaration types may differ, but strict translation uniqueness
only needs this positional relation.  The view-side `toCtx` is definitionally
the reversed telescope selected by the recursive semantic run, followed by
the caller's view-side base context. -/
theorem CandidateExprRun.terminalContextRunView
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {Δ : VLCtx} {source' view' inferred' : VExpr}
    (run : CandidateExprRun env Us trace Δ source' view' inferred')
    (contextRun : CandidateContextRun candidateContext)
    (venv_eq : contextRun.context.venv = env)
    (lparams_eq : contextRun.context.lparams = Us)
    (vlctx_eq : contextRun.context.vlctx = Δ)
    {viewΔ : VLCtx}
    (viewDefEq : VLCtx.IsDefEq env Us.length Δ viewΔ)
    (viewContext : TrExprS.IsUniqueCtx Δ viewΔ) :
    ∃ (terminalRun : CandidateContextRun trace.terminalContext)
        (viewTerminal : VLCtx),
      terminalRun.context.venv = env ∧
      terminalRun.context.lparams = Us ∧
      VLCtx.IsDefEq env Us.length terminalRun.context.vlctx viewTerminal ∧
      TrExprS.IsUniqueCtx terminalRun.context.vlctx viewTerminal ∧
      VLCtx.FVLift' viewΔ viewTerminal 0
        (.skipN .refl trace.spineLength) 0 ∧
      viewTerminal.toCtx =
        (VExpr.telN trace.spineLength view').reverse ++ viewΔ.toCtx := by
  induction run generalizing viewΔ with
  | @terminal Δ context source inferred result source' result' inferred'
      checked normalized node =>
      let terminalRun : CandidateContextRun
          (AddInductive.CandidateExprTrace.terminal
            context source inferred result checked normalized).terminalContext := by
        simpa only [AddInductive.CandidateExprTrace.terminalContext] using
          contextRun
      refine ⟨terminalRun, viewΔ, venv_eq, lparams_eq, ?_, ?_, .refl, ?_⟩
      · change VLCtx.IsDefEq env Us.length contextRun.context.vlctx viewΔ
        rw [vlctx_eq]
        exact viewDefEq
      · change TrExprS.IsUniqueCtx contextRun.context.vlctx viewΔ
        rw [vlctx_eq]
        exact viewContext
      · simp only [AddInductive.CandidateExprTrace.spineLength,
          VExpr.telN, List.reverse_nil, List.nil_append]
  | @forallE domain context name binderInfo Δ source inferred body
      source' domain' body' inferred' domainView' domainInferred'
      storedDomain' bodyΔ storedBody' bodyView' bodyInferred' u v fresh
      checked normalized annotations annotationsEq domainCandidate
      bodyCandidate node domainRun annotationsRun bodyRun domainType bodyType
      bodySource bodyContext domainIH bodyIH =>
    have storedDomain_tr : contextRun.context.TrExprS
        annotations.consumed storedDomain' := by
      simpa only [VContext.TrExprS, venv_eq, lparams_eq, vlctx_eq] using
        annotationsRun.rhs_tr
    have henv : VEnv.WF env := by
      simpa only [venv_eq] using contextRun.context.Ewf
    have hΔ : OnCtx Δ.toCtx (env.IsType Us.length) := by
      simpa only [venv_eq, lparams_eq, vlctx_eq] using
        contextRun.context.Δwf.toCtx
    have storedDomain_type : env.IsType Us.length Δ.toCtx storedDomain' := by
      have annotationDef := annotationsRun.isDefEqU.of_l henv hΔ domainType
      exact ⟨u, annotationDef.hasType.2⟩
    have domainDef : env.IsDefEq Us.length Δ.toCtx
        domain' domainView' (.sort u) :=
      domainRun.evidence.isDefEq.toU.of_l henv hΔ domainType
    have annotationDef : env.IsDefEq Us.length Δ.toCtx
        domain' storedDomain' (.sort u) :=
      annotationsRun.isDefEqU.of_l henv hΔ domainType
    have storedToView : env.IsDefEq Us.length Δ.toCtx
        storedDomain' domainView' (.sort u) :=
      annotationDef.symm.trans domainDef
    let nextContextRun := contextRun.pushLocalDecl name binderInfo
      annotations.consumed fresh storedDomain' storedDomain_tr (by
        change contextRun.context.venv.IsType
          contextRun.context.lparams.length
          contextRun.context.vlctx.toCtx storedDomain'
        rw [venv_eq, lparams_eq, vlctx_eq]
        exact storedDomain_type)
    have nextVenv : nextContextRun.context.venv = env := by
      simp only [nextContextRun, CandidateContextRun.pushLocalDecl_venv,
        venv_eq]
    have nextLparams : nextContextRun.context.lparams = Us := by
      simp only [nextContextRun, CandidateContextRun.pushLocalDecl_lparams,
        lparams_eq]
    have nextVlctx : nextContextRun.context.vlctx = bodyΔ := by
      simp only [nextContextRun, CandidateContextRun.pushLocalDecl_vlctx]
      rw [vlctx_eq, bodyContext]
    let viewBodyΔ : VLCtx :=
      (some (context.freshFVarId, annotations.consumed.fvarsList),
        .vlam domainView') :: viewΔ
    have bodyWF := bodyRun.context_wf
    rw [bodyContext] at bodyWF
    have bodyViewDefEq : VLCtx.IsDefEq env Us.length bodyΔ viewBodyΔ := by
      rw [bodyContext]
      exact .cons viewDefEq bodyWF.2.1 (.vlam storedToView)
    have bodyViewContext : TrExprS.IsUniqueCtx bodyΔ viewBodyΔ := by
      rw [bodyContext]
      exact viewContext.cons .vlam
    obtain ⟨terminalRun, viewTerminal, terminalVenv, terminalLparams,
        terminalViewDefEq, terminalViewContext, terminalViewLift,
        terminalViewEq⟩ :=
      bodyIH nextContextRun nextVenv nextLparams nextVlctx bodyViewDefEq
        bodyViewContext
    refine ⟨by
        simpa only [AddInductive.CandidateExprTrace.terminalContext] using
          terminalRun,
      viewTerminal, terminalVenv, terminalLparams, terminalViewDefEq,
      terminalViewContext, ?_, ?_⟩
    · have headLift : VLCtx.FVLift' viewΔ viewBodyΔ 0
          (.skipN .refl 1) 0 := by
        exact VLCtx.FVLift'.skip_fvar
          (context.freshFVarId, annotations.consumed.fvarsList)
          (.vlam domainView') (.refl :
            VLCtx.FVLift' viewΔ viewΔ 0 .refl 0)
      simpa only [AddInductive.CandidateExprTrace.spineLength,
        Nat.add_comm 1] using
        candidateFVLift'_comp headLift terminalViewLift
    simpa only [AddInductive.CandidateExprTrace.spineLength,
      VExpr.telN, List.reverse_cons, List.singleton_append,
      List.append_assoc, viewBodyΔ, VLCtx.toCtx] using terminalViewEq

/-- Interpret the terminal-sort fact retained by family validation.

At a terminal node the verified WHNF result translates the exact kernel sort.
At a Pi node the recursively interpreted body is transported from the
annotation-consumed binder context to the candidate-view binder context. Thus
the complete checker-selected candidate view is a Theory type without using a
checked inductive declaration or a caller-supplied view-WF proof. -/
theorem CandidateExprRun.view_isType_of_terminalSort
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {Δ : VLCtx} {source' view' inferred' : VExpr}
    (run : CandidateExprRun env Us trace Δ source' view' inferred')
    (terminal : trace.terminalResult = .sort resultLevel) :
    env.IsType Us.length Δ.toCtx view' := by
  induction run with
  | terminal node =>
    simp only [AddInductive.CandidateExprTrace.terminalResult] at terminal
    rw [terminal] at node
    cases node.whnf.rhs_tr with
    | sort level_tr =>
      exact ⟨_, .sort (VLevel.WF.of_ofLevel level_tr)⟩
  | @forallE domain context name binderInfo Δ source inferred body
      source' domain' body' inferred' domainView' domainInferred'
      storedDomain' bodyΔ storedBody' bodyView' bodyInferred' u v fresh
      checked normalized annotations annotationsEq domainCandidate
      bodyCandidate node domainRun annotationsRun bodyRun domainType bodyType
      bodySource bodyContext domainIH bodyIH =>
    simp only [AddInductive.CandidateExprTrace.terminalResult] at terminal
    have henv : VEnv.WF env := by
      simpa only [node.check.venv_eq] using node.check.context.Ewf
    have hΔ : VLCtx.WF env Us.length Δ := by
      simpa only [node.check.venv_eq, node.check.lparams_eq,
        node.check.vlctx_eq] using node.check.context.Δwf
    have domainDef : env.IsDefEq Us.length Δ.toCtx
        domain' domainView' (.sort u) :=
      domainRun.evidence.isDefEq.toU.of_l henv hΔ.toCtx domainType
    have domainViewType : env.IsType Us.length Δ.toCtx domainView' :=
      ⟨u, domainDef.hasType.2⟩
    have annotationDef : env.IsDefEq Us.length Δ.toCtx
        domain' storedDomain' (.sort u) :=
      annotationsRun.isDefEqU.of_l henv hΔ.toCtx domainType
    have storedToView : env.IsDefEq Us.length Δ.toCtx
        storedDomain' domainView' (.sort u) :=
      annotationDef.symm.trans domainDef
    have bodyContextEq : env.IsDefEqCtx Us.length []
        (storedDomain' :: Δ.toCtx) (domainView' :: Δ.toCtx) :=
      (VLCtx.IsDefEq.cons (.refl henv hΔ) (ofv := none)
        (by nofun) (.vlam storedToView)).defeqCtx
    have bodyViewTypeStored : env.IsType Us.length
        (storedDomain' :: Δ.toCtx) bodyView' := by
      simpa only [bodyContext, VLCtx.toCtx] using bodyIH terminal
    have bodyViewType : env.IsType Us.length
        (domainView' :: Δ.toCtx) bodyView' := by
      exact bodyViewTypeStored.defeqDFC henv.ordered bodyContextEq
    exact domainViewType.forallE bodyViewType

/-- The exact terminal sort retained by family validation is also the final
result of the recursively reconstructed Theory view.  Besides typing, this
keeps the concrete `VLevel.ofLevel` equation needed to identify the
validator-owned common block universe. -/
theorem CandidateExprRun.viewResult_of_terminalSort
    {env : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace candidateContext source}
    {Δ : VLCtx} {source' view' inferred' : VExpr}
    (run : CandidateExprRun env Us trace Δ source' view' inferred')
    (terminal : trace.terminalResult = .sort resultLevel) :
    ∃ viewLevel,
      VLevel.ofLevel Us resultLevel = some viewLevel ∧
        VExpr.dropN trace.spineLength view' = .sort viewLevel := by
  induction run with
  | terminal node =>
      simp only [AddInductive.CandidateExprTrace.terminalResult] at terminal
      rw [terminal] at node
      cases node.whnf.rhs_tr with
      | sort level_tr =>
          exact ⟨_, level_tr, rfl⟩
  | @forallE domain context name binderInfo Δ source inferred body
      source' domain' body' inferred' domainView' domainInferred'
      storedDomain' bodyΔ storedBody' bodyView' bodyInferred' u v fresh
      checked normalized annotations annotationsEq domainCandidate
      bodyCandidate node domainRun annotationsRun bodyRun domainType bodyType
      bodySource bodyContext domainIH bodyIH =>
      simp only [AddInductive.CandidateExprTrace.terminalResult] at terminal
      obtain ⟨viewLevel, level_tr, result_eq⟩ := bodyIH terminal
      exact ⟨viewLevel, level_tr, by
        simpa only [AddInductive.CandidateExprTrace.spineLength,
          VExpr.dropN, Nat.add_comm 1] using result_eq⟩

/-- Family validation types the checker-selected view first; the retained
candidate equality then transports that fact back to the exact raw Theory
source. This is the declaration-WF fact needed before raw-family insertion. -/
theorem CandidateExprSemanticRootRun.source_isType_of_terminalSort
    {env : VEnv} {Us : List Name} {source : Expr}
    {candidate : AddInductive.CandidateExpr source} {source' : VExpr}
    (run : CandidateExprSemanticRootRun env Us candidate source')
    (terminal : candidate.trace.terminalResult = .sort resultLevel) :
    env.IsType Us.length [] source' := by
  obtain ⟨_, recursive⟩ := run.recursive
  have hview := recursive.view_isType_of_terminalSort terminal
  have henv : VEnv.WF env := by
    simpa only [run.venv_eq] using run.contextRun.context.Ewf
  exact hview.defeqU_l henv trivial recursive.evidence.isDefEq.toU.symm

/-- Root-level projection of the exact terminal-sort translation. -/
theorem CandidateExprSemanticRootRun.viewResult_of_terminalSort
    {env : VEnv} {Us : List Name} {source : Expr}
    {candidate : AddInductive.CandidateExpr source} {source' : VExpr}
    (run : CandidateExprSemanticRootRun env Us candidate source')
    (terminal : candidate.trace.terminalResult = .sort resultLevel) :
    ∃ viewLevel,
      VLevel.ofLevel Us resultLevel = some viewLevel ∧
        VExpr.dropN candidate.trace.spineLength run.view = .sort viewLevel := by
  obtain ⟨_, recursive⟩ := run.recursive
  exact recursive.viewResult_of_terminalSort terminal

/-- Candidate-view parameter binders selected by an exact singleton family
validation run. The split is computed from the retained candidate spine. -/
def CandidateExprSemanticRootRun.viewParameters
    {indType : InductiveType}
    {candidate : AddInductive.CandidateExpr indType.type}
    (run : CandidateExprSemanticRootRun env Us candidate source')
    (validation : AddInductive.CandidateExprTrace.FamilyValidationRun
      indType candidate.trace) : List VExpr :=
  (VExpr.telN candidate.trace.spineLength run.view).take
    validation.nparams

/-- Candidate-view index binders following the validator-selected parameter
prefix. -/
def CandidateExprSemanticRootRun.viewIndices
    {indType : InductiveType}
    {candidate : AddInductive.CandidateExpr indType.type}
    (run : CandidateExprSemanticRootRun env Us candidate source')
    (validation : AddInductive.CandidateExprTrace.FamilyValidationRun
      indType candidate.trace) : List VExpr :=
  (VExpr.telN candidate.trace.spineLength run.view).drop
    validation.nparams

/-- An exact recursive run whose executable main spine preserves the stored
binders. Unlike a whole-expression root equality, this package is strong
enough to expose generation's pointwise binder and terminal-result evidence. -/
def CandidateExprSpineRun (env : VEnv) (Us : List Name)
    {source : Expr} (candidate : AddInductive.CandidateExpr source)
    (raw view : VExpr) : Prop :=
  candidate.trace.storedSpine = true ∧
    ∃ inferred, CandidateExprRun env Us candidate.trace [] raw view inferred

/-- Retaining the recursive semantic root makes the generation spine a direct
projection once the executable structural gate has succeeded. -/
theorem CandidateExprSemanticRootRun.spine
    (run : CandidateExprSemanticRootRun env Us candidate source')
    (storedSpine : candidate.trace.storedSpine = true) :
    CandidateExprSpineRun env Us candidate source' run.view :=
  ⟨storedSpine, run.recursive⟩

/-- Root-level projection of the exact annotation-consumed telescope retained
by the recursive semantic run. -/
theorem CandidateExprSemanticRootRun.annotationSpineEvidence
    (run : CandidateExprSemanticRootRun env Us candidate source')
    (storedSpine : candidate.trace.storedSpine = true) :
    ∃ storedBinders,
      TelDefEqEvidence env Us.length []
          (VExpr.telN candidate.trace.spineLength source') storedBinders ∧
        storedBinders.length = candidate.trace.spineLength := by
  obtain ⟨inferred, recursive⟩ := run.recursive
  exact recursive.annotationSpineEvidence storedSpine

/-- Root-level projection joining the candidate's annotation-consumed
telescope to its exact verified terminal reader context. -/
theorem CandidateExprSemanticRootRun.annotationSpineContext
    (run : CandidateExprSemanticRootRun env Us candidate source')
    (storedSpine : candidate.trace.storedSpine = true) :
    ∃ (terminalRun : CandidateContextRun candidate.trace.terminalContext)
        (storedBinders : List VExpr),
      terminalRun.context.venv = env ∧
      terminalRun.context.lparams = Us ∧
      TelDefEqEvidence env Us.length []
        (VExpr.telN candidate.trace.spineLength source') storedBinders ∧
      storedBinders.length = candidate.trace.spineLength ∧
      terminalRun.context.vlctx.toCtx = storedBinders.reverse ∧
      CandidateAnnotationSpine env Us candidate.trace []
        terminalRun.context.vlctx storedBinders := by
  obtain ⟨inferred, recursive⟩ := run.recursive
  obtain ⟨terminalRun, storedBinders, terminalVenv, terminalLparams,
      telescope, storedLength, terminalContextEq, annotationSpine⟩ :=
    recursive.annotationSpineContext storedSpine run.contextRun run.venv_eq
      run.lparams_eq run.vlctx_eq
  exact ⟨terminalRun, storedBinders, terminalVenv, terminalLparams,
    telescope, storedLength, by
      simpa only [VLCtx.toCtx, List.append_nil] using terminalContextEq,
    annotationSpine⟩

/-- Turn an exact root translation and a recursive identity witness into the
generation-ready spine package. The root equalities transport the recursive
run out of the verifier's reconstructed context without choosing a different
semantic endpoint. -/
theorem CandidateExprRootRun.spineOfIdentity
    {env : VEnv} {Us : List Name} {source : Expr}
    {candidate : AddInductive.CandidateExpr source} {source' : VExpr}
    (run : CandidateExprRootRun env Us candidate source' source')
    (identity : CandidateExprIdentity candidate.trace) :
    CandidateExprSpineRun env Us candidate source' source' := by
  refine ⟨identity.storedSpine, ?_⟩
  have source_tr : run.contextRun.context.TrExprS source source' := by
    simpa only [VContext.TrExprS, run.venv_eq, run.lparams_eq,
      run.vlctx_eq] using run.source_tr
  obtain ⟨inferred', ⟨recursive⟩⟩ :=
    CandidateExprRun.exists_ofIdentity candidate.trace identity
      run.contextRun source' source_tr run.whnfFuel run.whnfDepth
  refine ⟨inferred', ?_⟩
  simpa only [run.venv_eq, run.lparams_eq, run.vlctx_eq] using recursive

/-- Retain the exact recursive run selected by an identity-normalizing root.

All data fields are inherited from the named root and its fixed Theory
endpoint. The existential inferred type remains proof-only, so this constructor
does not use classical choice and does not turn identity into an executable or
semantic oracle. -/
def CandidateExprRootRun.semanticOfIdentity
    {env : VEnv} {Us : List Name} {source : Expr}
    {candidate : AddInductive.CandidateExpr source} {source' : VExpr}
    (run : CandidateExprRootRun env Us candidate source' source')
    (identity : CandidateExprIdentity candidate.trace) :
    CandidateExprSemanticRootRun env Us candidate source' where
  contextRun := run.contextRun
  venv_eq := run.venv_eq
  lparams_eq := run.lparams_eq
  vlctx_eq := run.vlctx_eq
  source_tr := run.source_tr
  whnfFuel := run.whnfFuel
  whnfDepth := run.whnfDepth
  view := source'
  recursive := by
    have source_tr : run.contextRun.context.TrExprS source source' := by
      simpa only [VContext.TrExprS, run.venv_eq, run.lparams_eq,
        run.vlctx_eq] using run.source_tr
    obtain ⟨inferred, ⟨recursive⟩⟩ :=
      CandidateExprRun.exists_ofIdentity candidate.trace identity
        run.contextRun source' source_tr run.whnfFuel run.whnfDepth
    refine ⟨inferred, ?_⟩
    simpa only [run.venv_eq, run.lparams_eq, run.vlctx_eq] using recursive

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
    simpa only [rawTel, viewTel, rawResult_eq, viewResult_eq,
      VLCtx.toCtx] using evidence
  exact exactEvidence.ofRightType recursive.env_wf trivial (by
    simpa using rightType)

end TypeChecker

namespace VInductDecl

/-- One source-aligned record from the executable family-metadata inventory
translates to the corresponding raw Theory family constant.  Only the fields
observed by `TrConstVal` are projected; the retained record still owns all
generated mutual metadata. -/
theorem declaredInductiveInfo_tr
    {stats : AddInductive.InductiveStats} {numParams : Nat}
    {indTypes : Array InductiveType} {indType : InductiveType}
    {info : InductiveVal} {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context} {env : VEnv} {Us : List Name}
    {raw : VInductiveType}
    (alignment : ∃ numIndices,
      info = AddInductive.declaredInductiveInfo stats numParams indTypes
        indType numIndices numNested isUnsafe context)
    (safe : isUnsafe = false)
    (lparams_eq : context.lparams = Us)
    (name_eq : indType.name = raw.name)
    (uvars_eq : raw.uvars = Us.length)
    (type_tr : TrExprS env Us [] indType.type raw.type) :
    TrConstVal .safe env (.inductInfo info) raw.toVConstVal := by
  obtain ⟨numIndices, rfl⟩ := alignment
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · simp [ConstantInfo.safety, ConstantInfo.isUnsafe,
      ConstantInfo.isPartial, AddInductive.declaredInductiveInfo, safe]
  · simpa [ConstantInfo.toConstantVal, ConstantInfo.levelParams,
      AddInductive.declaredInductiveInfo, lparams_eq] using uvars_eq.symm
  · simpa [ConstantInfo.toConstantVal, ConstantInfo.levelParams,
      ConstantInfo.type, AddInductive.declaredInductiveInfo,
      lparams_eq] using type_tr
  · simpa [ConstantInfo.toConstantVal, ConstantInfo.name,
      AddInductive.declaredInductiveInfo] using name_eq

theorem checkName_constants_fresh
    {env : Environment} {name : Name} {allowPrimitive : Bool}
    (check : env.checkName name allowPrimitive = .ok ()) :
    env.constants.find? name = none := by
  have contains : env.contains name = false := by
    cases h : env.contains name
    · rfl
    · simp [Kernel.Environment.checkName, h, Bind.bind, Except.bind] at check
  change env.constants.contains name = false at contains
  rw [SMap.find?_isSome] at contains
  cases hfind : env.constants.find? name <;> simp_all

/-- A successful nonprimitive name check excludes every hard-coded kernel
primitive name. -/
theorem checkName_primitives_fresh
    {env : Environment} {name : Name}
    (check : env.checkName name false = .ok ()) :
    Environment.primitives.contains name = false := by
  cases hc : env.contains name <;>
    cases hp : Environment.primitives.contains name <;>
      simp [Kernel.Environment.checkName, hc, hp, Bind.bind, Except.bind]
        at check ⊢

/-- Every primitive reflected by the Theory environment is among the
kernel's hard-coded primitive names. -/
theorem reflectedPrimitiveNames_mem_primitives
    {name : Name} (member : name ∈ VEnv.reflectedPrimitiveNames) :
    Environment.primitives.contains name = true := by
  simp [VEnv.reflectedPrimitiveNames] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [Environment.primitives, NameSet.ofList, NameSet.contains]

/-- Excluding kernel primitives also excludes the smaller reflected
primitive inventory. -/
theorem not_reflectedPrimitive_of_primitives_fresh
    {name : Name}
    (fresh : Environment.primitives.contains name = false) :
    name ∉ VEnv.reflectedPrimitiveNames := by
  intro member
  rw [reflectedPrimitiveNames_mem_primitives member] at fresh
  contradiction

/-- Verify-layer projection that the producer's family-only declaration trace
preserves persistent-map well-formedness. -/
theorem declarationTraceConstantsWF
    (run : AddInductive.DeclareInductiveInfoListRun allowPrimitive
      env infos finalEnv)
    (mapWF : env.constants.WF) :
    finalEnv.constants.WF := by
  induction run with
  | nil => exact mapWF
  | cons check tail ih =>
      apply ih
      exact mapWF.insert _ _ (checkName_constants_fresh check)

/-- Family declaration preserves persistent-map well-formedness. -/
theorem _root_.Lean4Lean.AddInductive.DeclareInductiveInfoListRun.map_wf
    (run : AddInductive.DeclareInductiveInfoListRun allowPrimitive env infos
      finalEnv) (wf : env.constants.WF) : finalEnv.constants.WF :=
  VInductDecl.declarationTraceConstantsWF run wf

/-- Every family accepted by a declaration fold was absent from the fold's
input environment.  Freshness of later records reflects backwards across all
earlier successful insertions. -/
theorem _root_.Lean4Lean.AddInductive.DeclareInductiveInfoListRun.names_fresh
    (run : AddInductive.DeclareInductiveInfoListRun allowPrimitive env infos
      finalEnv) (wf : env.constants.WF) :
    ∀ info ∈ infos, env.constants.find? info.name = none := by
  induction run with
  | nil => intro info member; nomatch member
  | @cons infosTail finalEnvTail startEnv inserted checkName tail ih =>
      intro info member
      rcases List.mem_cons.mp member with rfl | member
      · exact VInductDecl.checkName_constants_fresh checkName
      · have insertedFresh :=
          VInductDecl.checkName_constants_fresh checkName
        have nextWF := wf.insert inserted.name (.inductInfo inserted)
          insertedFresh
        have tailFresh := ih nextWF info member
        change (startEnv.constants.insert inserted.name
          (.inductInfo inserted)).find? info.name = none at tailFresh
        rw [wf.find?_insert] at tailFresh
        split at tailFresh <;> simp_all

/-- Sequential family name checks make the exact declaration inventory
pairwise distinct. -/
theorem _root_.Lean4Lean.AddInductive.DeclareInductiveInfoListRun.names_nodup
    (run : AddInductive.DeclareInductiveInfoListRun allowPrimitive env infos
      finalEnv) (wf : env.constants.WF) :
    (infos.map (·.name)).Nodup := by
  induction run with
  | nil => simp
  | @cons infosTail finalEnvTail startEnv inserted checkName tail ih =>
      rw [List.map_cons, List.nodup_cons]
      constructor
      · intro member
        obtain ⟨other, otherMember, nameEq⟩ := List.mem_map.1 member
        have insertedFresh :=
          VInductDecl.checkName_constants_fresh checkName
        have nextWF := wf.insert inserted.name (.inductInfo inserted)
          insertedFresh
        have fresh := tail.names_fresh nextWF other otherMember
        change (startEnv.constants.insert inserted.name
          (.inductInfo inserted)).find? other.name = none at fresh
        rw [nameEq, wf.find?_insert] at fresh
        simp at fresh
      · exact ih (wf.insert _ _
          (VInductDecl.checkName_constants_fresh checkName))

/-- Every family name accepted by a nonprimitive declaration trace avoids
both the kernel and Theory primitive inventories. -/
theorem _root_.Lean4Lean.AddInductive.DeclareInductiveInfoListRun.names_not_primitive
    (run : AddInductive.DeclareInductiveInfoListRun false env infos
      finalEnv) :
    ∀ info ∈ infos,
      info.name ∉ VEnv.reflectedPrimitiveNames ∧
        Environment.primitives.contains info.name = false := by
  induction run with
  | nil => intro info member; nomatch member
  | cons check tail ih =>
      intro info member
      rcases List.mem_cons.mp member with rfl | member
      · have fresh := VInductDecl.checkName_primitives_fresh check
        exact ⟨VInductDecl.not_reflectedPrimitive_of_primitives_fresh fresh,
          fresh⟩
      · exact ih info member

/-- Family declaration preserves every lookup already present in its input
map. -/
theorem _root_.Lean4Lean.AddInductive.DeclareInductiveInfoListRun.preserve_map_lookup
    (run : AddInductive.DeclareInductiveInfoListRun allowPrimitive env infos
      finalEnv) (wf : env.constants.WF)
    (old : env.constants.find? name = some found) :
    finalEnv.constants.find? name = some found := by
  induction run with
  | nil => exact old
  | @cons infos finalEnv env info checkName tail ih =>
      have fresh := VInductDecl.checkName_constants_fresh checkName
      have mid : (env.add (.inductInfo info)).constants.find? name =
          some found := by
        change (env.constants.insert info.name (.inductInfo info)).find? name = _
        rw [wf.find?_insert]
        split
        · rename_i equal
          have nameEq : info.name = name := LawfulBEq.eq_of_beq equal
          subst name
          rw [old] at fresh
          contradiction
        · exact old
      exact ih (wf.insert _ _ fresh) mid

/-- Every synthesized family record remains at its name in the final
family-declaration map. -/
theorem _root_.Lean4Lean.AddInductive.DeclareInductiveInfoListRun.map_lookup
    (run : AddInductive.DeclareInductiveInfoListRun allowPrimitive env infos
      finalEnv) (wf : env.constants.WF) {info : InductiveVal}
    (member : info ∈ infos) :
    finalEnv.constants.find? info.name = some (.inductInfo info) := by
  induction run with
  | nil => contradiction
  | @cons infosTail finalEnvTail startEnv inserted checkName tail ih =>
      rcases List.mem_cons.1 member with rfl | member
      · apply tail.preserve_map_lookup
          (wf.insert _ _ (VInductDecl.checkName_constants_fresh checkName))
        change SMap.find? (SMap.insert _ info.name
          (ConstantInfo.inductInfo info)) info.name = _
        rw [wf.find?_insert]
        simp
      · exact ih (wf.insert _ _
          (VInductDecl.checkName_constants_fresh checkName)) member

/-- Classify an arbitrary constant lookup after the family declaration fold.
The inserted branch retains the exact family record and queried key, so
consumers can eliminate impossible constant kinds without an ambient map
integrity assumption. -/
theorem _root_.Lean4Lean.AddInductive.DeclareInductiveInfoListRun.constant_lookup_cases
    (run : AddInductive.DeclareInductiveInfoListRun allowPrimitive env infos
      finalEnv) (wf : env.constants.WF) {name : Name}
    {found : ConstantInfo}
    (lookup : finalEnv.constants.find? name = some found) :
    env.constants.find? name = some found ∨
      ∃ info ∈ infos, found = .inductInfo info ∧ info.name = name := by
  induction run with
  | nil => exact .inl lookup
  | @cons infosTail finalEnvTail startEnv inserted checkName tail ih =>
      have fresh := VInductDecl.checkName_constants_fresh checkName
      rcases ih (wf.insert _ _ fresh) lookup with mid |
          ⟨info, member, tagged_eq, name_eq⟩
      · change (startEnv.constants.insert inserted.name
          (.inductInfo inserted)).find? name = _ at mid
        rw [wf.find?_insert] at mid
        split at mid
        · rename_i name_equal
          exact .inr ⟨inserted, List.mem_cons_self,
            (Option.some.inj mid).symm, LawfulBEq.eq_of_beq name_equal⟩
        · exact .inl mid
      · exact .inr ⟨info, List.mem_cons_of_mem inserted member,
          tagged_eq, name_eq⟩

/-- Every family lookup in the output of the declaration fold is either an
unchanged input lookup or one of the records inserted by that fold. -/
theorem _root_.Lean4Lean.AddInductive.DeclareInductiveInfoListRun.map_lookup_cases
    (run : AddInductive.DeclareInductiveInfoListRun allowPrimitive env infos
      finalEnv) (wf : env.constants.WF) {name : Name}
    {info : InductiveVal}
    (found : finalEnv.constants.find? name = some (.inductInfo info)) :
    env.constants.find? name = some (.inductInfo info) ∨
      info ∈ infos ∧ info.name = name := by
  induction run with
  | nil => exact .inl found
  | @cons infosTail finalEnvTail startEnv inserted checkName tail ih =>
      have fresh := VInductDecl.checkName_constants_fresh checkName
      rcases ih (wf.insert _ _ fresh) found with mid | member
      · change (startEnv.constants.insert inserted.name
          (.inductInfo inserted)).find? name = _ at mid
        rw [wf.find?_insert] at mid
        split at mid
        · rename_i name_equal
          have inserted_name_eq : inserted.name = name :=
            LawfulBEq.eq_of_beq name_equal
          have tagged_eq :
              (.inductInfo inserted : ConstantInfo) = .inductInfo info :=
            Option.some.inj mid
          have info_eq : inserted = info :=
            ConstantInfo.inductInfo.inj tagged_eq
          exact .inr ⟨info_eq ▸ List.mem_cons_self,
            info_eq ▸ inserted_name_eq⟩
        · exact .inl mid
      · exact .inr ⟨List.mem_cons_of_mem inserted member.1, member.2⟩

/--
info: 'Lean4Lean.AddInductive.DeclareInductiveInfoListRun.map_wf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms AddInductive.DeclareInductiveInfoListRun.map_wf

/--
info: 'Lean4Lean.AddInductive.DeclareInductiveInfoListRun.preserve_map_lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms AddInductive.DeclareInductiveInfoListRun.preserve_map_lookup

/--
info: 'Lean4Lean.AddInductive.DeclareInductiveInfoListRun.map_lookup' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms AddInductive.DeclareInductiveInfoListRun.map_lookup

/--
info: 'Lean4Lean.AddInductive.DeclareInductiveInfoListRun.constant_lookup_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms AddInductive.DeclareInductiveInfoListRun.constant_lookup_cases

/--
info: 'Lean4Lean.AddInductive.DeclareInductiveInfoListRun.map_lookup_cases' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms AddInductive.DeclareInductiveInfoListRun.map_lookup_cases

/-- Family-only declaration cannot synthesize constructor metadata absent
from the input map. -/
theorem declarationTraceNoCtorInfo
    (run : AddInductive.DeclareInductiveInfoListRun allowPrimitive
      env infos finalEnv)
    (mapWF : env.constants.WF)
    (initial : ∀ name info,
      env.constants.find? name ≠ some (.ctorInfo info)) :
    ∀ name info, finalEnv.constants.find? name ≠
      some (.ctorInfo info) := by
  induction run with
  | nil => exact initial
  | @cons infos finalEnv env info check tail ih =>
      apply ih (mapWF.insert _ _ (checkName_constants_fresh check))
      intro name ctor found
      change (env.constants.insert info.name (.inductInfo info)).find? name =
        some (.ctorInfo ctor) at found
      rw [mapWF.find?_insert] at found
      split at found
      · simp at found
      · exact initial name ctor found

/-- Interpret the exact kernel family-declaration trace against the matching
Theory family-staging fold.  Each step is a real `TrEnv'.inductStaging`
extension; translations and raw-family typing are transported monotonically
for the remaining source-ordered tail. -/
theorem declarationTraceTrEnv
    {allowPrimitive : Bool} {kernelEnv finalKernelEnv : Environment}
    {infos : List InductiveVal} {env blockEnv : VEnv}
    {raws : List VInductiveType} {Q : Bool}
    (declare : AddInductive.DeclareInductiveInfoListRun allowPrimitive
      kernelEnv infos finalKernelEnv)
    (stage : env.stageInductiveTypes raws = some blockEnv)
    (evidence : List.Forall₂
      (fun info raw =>
        TrConstVal .safe env (.inductInfo info) raw.toVConstVal ∧
        raw.toVConstant.WF env)
      infos raws)
    (pre : TrEnv' .safe kernelEnv.constants Q env) :
    TrEnv' .safe finalKernelEnv.constants Q blockEnv := by
  induction declare generalizing env blockEnv raws with
  | nil =>
      cases evidence
      change some env = some blockEnv at stage
      cases stage
      exact pre
  | @cons infos finalKernelEnv kernelEnv info check tail ih =>
      cases evidence with
      | cons head rest =>
          rename_i raw raws
          simp only [VEnv.stageInductiveTypes, List.foldlM_cons] at stage
          obtain ⟨nextEnv, added, tailStage⟩ :=
            Option.bind_eq_some_iff.mp stage
          have add : AddInductConstant .induct kernelEnv.constants env
              raw.toVConstVal
              (kernelEnv.add (.inductInfo info)).constants nextEnv := {
            info := .inductInfo info
            kind_eq := trivial
            tr := head.1
            map_fresh := by
              rw [← head.1.2]
              simpa [ConstantInfo.toConstantVal, ConstantInfo.name] using
                checkName_constants_fresh check
            env_add := added
            map_add := by
              rw [← head.1.2]
              rfl }
          have post : TrEnv' .safe
              (kernelEnv.add (.inductInfo info)).constants Q nextEnv :=
            .inductStaging add head.2 pre
          have le : env ≤ nextEnv := VEnv.addConst_le added
          have rest' : List.Forall₂
              (fun info raw =>
                TrConstVal .safe nextEnv (.inductInfo info)
                    raw.toVConstVal ∧
                  raw.toVConstant.WF nextEnv)
              infos raws := by
            exact Lean4Lean.List.Forall₂.imp (h := rest) fun _ _ h =>
              ⟨⟨⟨h.1.1.1, h.1.1.2.1, h.1.1.2.2.mono le⟩,
                h.1.2⟩, h.2.mono le⟩
          exact ih tailStage rest' post

private theorem family_forall₂_cons_iff
    {R : α → β → Prop} {a : α} {as : List α} {b : β} {bs : List β} :
    List.Forall₂ R (a :: as) (b :: bs) ↔
      R a b ∧ List.Forall₂ R as bs := by
  constructor
  · intro relation
    cases relation with
    | cons head tail => exact ⟨head, tail⟩
  · rintro ⟨head, tail⟩
    exact .cons head tail

/-- The exact family-declaration trace replayed only as a Theory insertion
fold.  Unlike `FamilyDeclarationStagingRun`, this boundary deliberately
contains no `TrEnv'` postcondition, so it remains usable while a recognized
primitive family has been inserted but its constructors have not. -/
structure FamilyDeclarationInsertionRun
    (allowPrimitive : Bool) (kernelEnv finalKernelEnv : Environment)
    (infos : List InductiveVal) (env : VEnv) (raws : List VConstVal) where
  blockEnv : VEnv
  kernelTrace : AddInductive.DeclareInductiveInfoListRun
    allowPrimitive kernelEnv infos finalKernelEnv
  addTypes : AddInductConstants .induct kernelEnv.constants env raws
    finalKernelEnv.constants blockEnv

/-- Replay a retained family metadata trace against any aligned Theory model.
`Aligned` supplies only name-domain correspondence; semantic translations are
transported through earlier insertions, and no whole-history translation is
constructed at the family-only boundary. -/
noncomputable def familyDeclarationInsertion
    {allowPrimitive : Bool} {kernelEnv finalKernelEnv : Environment}
    {infos : List InductiveVal} {env : VEnv} {raws : List VConstVal}
    (declare : AddInductive.declareInductiveInfoList allowPrimitive infos
      kernelEnv = .ok finalKernelEnv)
    (evidence : List.Forall₂
      (fun info raw => TrConstVal .safe env (.inductInfo info) raw)
      infos raws)
    (pre : Aligned safety kernelEnv.constants env) :
    FamilyDeclarationInsertionRun allowPrimitive kernelEnv finalKernelEnv
      infos env raws := by
  induction infos generalizing kernelEnv finalKernelEnv env raws with
  | nil =>
      cases raws with
      | nil =>
          simp only [AddInductive.declareInductiveInfoList,
            Except.ok.injEq] at declare
          subst finalKernelEnv
          exact { blockEnv := env, kernelTrace := .nil, addTypes := .nil }
      | cons raw raws =>
          have impossible : False := by cases evidence
          exact impossible.elim
  | cons info infos ih =>
      cases raws with
      | nil =>
          have impossible : False := by cases evidence
          exact impossible.elim
      | cons raw raws =>
          have related := family_forall₂_cons_iff.mp evidence
          cases hcheck : kernelEnv.checkName info.name allowPrimitive with
          | error error =>
              have impossible : False := by
                simp only [AddInductive.declareInductiveInfoList] at declare
                rw [hcheck] at declare
                contradiction
              exact impossible.elim
          | ok value =>
              have value_eq : value = () := Subsingleton.elim _ _
              subst value
              have tailDeclare :
                  AddInductive.declareInductiveInfoList allowPrimitive infos
                    (kernelEnv.add (.inductInfo info)) =
                      .ok finalKernelEnv := by
                simpa only [AddInductive.declareInductiveInfoList, hcheck,
                  Bind.bind, Except.bind] using declare
              have mapFresh : kernelEnv.constants.find? raw.name = none := by
                rw [← related.1.2]
                simpa [ConstantInfo.toConstantVal, ConstantInfo.name] using
                  checkName_constants_fresh hcheck
              have envFresh : env.constants raw.name = none := by
                cases found : env.constants raw.name with
                | none => rfl
                | some ci =>
                    obtain ⟨kernelInfo, kernelFound, _⟩ :=
                      pre.find?_iff.mpr ⟨ci, found⟩
                    rw [mapFresh] at kernelFound
                    contradiction
              let nextEnv : VEnv := {
                env with
                constants := fun name =>
                  if raw.name = name then some raw.toVConstant
                  else env.constants name }
              have added : env.addConst raw.name raw.toVConstant =
                  some nextEnv := by
                simp [VEnv.addConst, envFresh, nextEnv]
              let add : AddInductConstant .induct kernelEnv.constants env raw
                  (kernelEnv.add (.inductInfo info)).constants nextEnv := {
                info := .inductInfo info
                kind_eq := trivial
                tr := related.1
                map_fresh := mapFresh
                env_add := added
                map_add := by
                  rw [← related.1.2]
                  rfl }
              have le : env ≤ nextEnv := VEnv.addConst_le added
              have tailEvidence : List.Forall₂
                  (fun info raw =>
                    TrConstVal .safe nextEnv (.inductInfo info) raw)
                  infos raws :=
                Lean4Lean.List.Forall₂.imp (h := related.2)
                  (fun _ _ relation => relation.mono le)
              let tailResult := ih tailDeclare tailEvidence
                (pre.addInductConstant add)
              exact {
                blockEnv := tailResult.blockEnv
                kernelTrace := .cons hcheck tailResult.kernelTrace
                addTypes := .cons add tailResult.addTypes }

/-- A source-ordered family declaration interpreted simultaneously in the
retained kernel environment and the exact Theory staging fold. -/
structure FamilyDeclarationStagingRun
    (allowPrimitive : Bool) (kernelEnv finalKernelEnv : Environment)
    (infos : List InductiveVal) (env finalEnv : VEnv)
    (raws : List VConstVal) (Q : Bool) where
  kernelTrace : AddInductive.DeclareInductiveInfoListRun
    allowPrimitive kernelEnv infos finalKernelEnv
  addTypes : AddInductConstants .induct kernelEnv.constants env raws
    finalKernelEnv.constants finalEnv
  trenv : TrEnv' .safe finalKernelEnv.constants Q finalEnv

/-- Convert the real family-declaration equation and the matching Theory
staging equation into one data-bearing alignment run.  Both folds are
traversed in source order, so no parallel family inventory or intermediate
environment can be selected by a caller. -/
noncomputable def familyDeclarationStaging
    {allowPrimitive : Bool} {kernelEnv finalKernelEnv : Environment}
    {infos : List InductiveVal} {env finalEnv : VEnv}
    {raws : List VConstVal} {Q : Bool}
    (declare : AddInductive.declareInductiveInfoList allowPrimitive infos
      kernelEnv = .ok finalKernelEnv)
    (stage : raws.foldlM
      (fun env raw => env.addConst raw.name raw.toVConstant) env =
        some finalEnv)
    (evidence : List.Forall₂
      (fun info raw =>
        TrConstVal .safe env (.inductInfo info) raw ∧
          raw.toVConstant.WF env)
      infos raws)
    (pre : TrEnv' .safe kernelEnv.constants Q env) :
    FamilyDeclarationStagingRun allowPrimitive kernelEnv finalKernelEnv
      infos env finalEnv raws Q := by
  induction infos generalizing kernelEnv finalKernelEnv env finalEnv raws with
  | nil =>
      cases raws with
      | nil =>
          simp only [AddInductive.declareInductiveInfoList,
            Except.ok.injEq] at declare
          subst finalKernelEnv
          change some env = some finalEnv at stage
          cases stage
          exact { kernelTrace := .nil, addTypes := .nil, trenv := pre }
      | cons raw raws =>
          have impossible : False := by cases evidence
          exact impossible.elim
  | cons info infos ih =>
      cases raws with
      | nil =>
          have impossible : False := by cases evidence
          exact impossible.elim
      | cons raw raws =>
          have aligned := family_forall₂_cons_iff.mp evidence
          cases hcheck : kernelEnv.checkName info.name allowPrimitive with
          | error error =>
              have impossible : False := by
                simp only [AddInductive.declareInductiveInfoList] at declare
                rw [hcheck] at declare
                contradiction
              exact impossible.elim
          | ok value =>
              have value_eq : value = () := Subsingleton.elim _ _
              subst value
              have tailDeclare :
                  AddInductive.declareInductiveInfoList allowPrimitive infos
                    (kernelEnv.add (.inductInfo info)) = .ok finalKernelEnv := by
                simpa only [AddInductive.declareInductiveInfoList, hcheck,
                  Bind.bind, Except.bind] using declare
              cases hadded : env.addConst raw.name raw.toVConstant with
              | none =>
                  have impossible : False := by
                    simp only [List.foldlM_cons, hadded, Bind.bind,
                      Option.bind] at stage
                    contradiction
                  exact impossible.elim
              | some nextEnv =>
                  have tailStage : raws.foldlM
                      (fun env raw =>
                        env.addConst raw.name raw.toVConstant) nextEnv =
                        some finalEnv := by
                    simpa only [List.foldlM_cons, hadded, Bind.bind,
                      Option.bind] using stage
                  have mapFresh : kernelEnv.constants.find? raw.name = none := by
                    rw [← aligned.1.1.2]
                    simpa [ConstantInfo.toConstantVal, ConstantInfo.name] using
                      checkName_constants_fresh hcheck
                  have add : AddInductConstant .induct kernelEnv.constants env raw
                      (kernelEnv.add (.inductInfo info)).constants nextEnv := {
                    info := .inductInfo info
                    kind_eq := trivial
                    tr := aligned.1.1
                    map_fresh := mapFresh
                    env_add := hadded
                    map_add := by
                      rw [← aligned.1.1.2]
                      rfl }
                  have post : TrEnv' .safe
                      (kernelEnv.add (.inductInfo info)).constants Q nextEnv :=
                    .inductStaging add aligned.1.2 pre
                  have le : env ≤ nextEnv := VEnv.addConst_le hadded
                  have tailEvidence : List.Forall₂
                      (fun info raw =>
                        TrConstVal .safe nextEnv (.inductInfo info) raw ∧
                          raw.toVConstant.WF nextEnv)
                      infos raws :=
                    Lean4Lean.List.Forall₂.imp (h := aligned.2)
                      (fun _ _ relation =>
                        ⟨relation.1.mono le, relation.2.mono le⟩)
                  let tailResult := ih tailDeclare tailStage tailEvidence post
                  exact {
                    kernelTrace := .cons hcheck tailResult.kernelTrace
                    addTypes := .cons add tailResult.addTypes
                    trenv := tailResult.trenv }

/-- The complete verifier contracts transported through a successful raw
family staging fold. -/
structure DeclarationTraceStagingResult (finalKernelEnv : Environment)
    (blockEnv : VEnv) (Q : Bool) where
  trenv : TrEnv' .safe finalKernelEnv.constants Q blockEnv
  hasPrimitives : blockEnv.HasPrimitives
  safePrimitives : ∀ {n ci}, finalKernelEnv.find? n = some ci →
    Environment.primitives.contains n →
    ci.safety = .safe ∧ ci.levelParams = []

/-- Strengthen `declarationTraceTrEnv` with the primitive contracts needed by
the derived checker context.  Fresh safe family metadata cannot create a
primitive lookup, while the matching Theory insertions preserve reflected
primitive availability. -/
theorem declarationTraceStaging
    {allowPrimitive : Bool} {kernelEnv finalKernelEnv : Environment}
    {infos : List InductiveVal} {env blockEnv : VEnv}
    {raws : List VInductiveType} {Q : Bool}
    (declare : AddInductive.DeclareInductiveInfoListRun allowPrimitive
      kernelEnv infos finalKernelEnv)
    (stage : env.stageInductiveTypes raws = some blockEnv)
    (evidence : List.Forall₂
      (fun info raw =>
        TrConstVal .safe env (.inductInfo info) raw.toVConstVal ∧
        raw.toVConstant.WF env)
      infos raws)
    (names : ∀ raw ∈ raws,
      raw.name ∉ VEnv.reflectedPrimitiveNames ∧
      Environment.primitives.contains raw.name = false)
    (mapWF : kernelEnv.constants.WF)
    (preTr : TrEnv' .safe kernelEnv.constants Q env)
    (preHas : env.HasPrimitives)
    (preSafe : ∀ {n ci}, kernelEnv.find? n = some ci →
      Environment.primitives.contains n →
      ci.safety = .safe ∧ ci.levelParams = []) :
    DeclarationTraceStagingResult finalKernelEnv blockEnv Q := by
  induction declare generalizing env blockEnv raws with
  | nil =>
      cases evidence
      change some env = some blockEnv at stage
      cases stage
      exact ⟨preTr, preHas, preSafe⟩
  | @cons infos finalKernelEnv kernelEnv info check tail ih =>
      cases evidence with
      | cons head rest =>
          rename_i raw raws
          have rawName := names raw (.head _)
          have restNames : ∀ other ∈ raws,
              other.name ∉ VEnv.reflectedPrimitiveNames ∧
                Environment.primitives.contains other.name = false := by
            intro other member
            exact names other (.tail _ member)
          simp only [VEnv.stageInductiveTypes, List.foldlM_cons] at stage
          obtain ⟨nextEnv, added, tailStage⟩ :=
            Option.bind_eq_some_iff.mp stage
          have add : AddInductConstant .induct kernelEnv.constants env
              raw.toVConstVal
              (kernelEnv.add (.inductInfo info)).constants nextEnv := {
            info := .inductInfo info
            kind_eq := trivial
            tr := head.1
            map_fresh := by
              rw [← head.1.2]
              simpa [ConstantInfo.toConstantVal, ConstantInfo.name] using
                checkName_constants_fresh check
            env_add := added
            map_add := by
              rw [← head.1.2]
              rfl }
          have postTr : TrEnv' .safe
              (kernelEnv.add (.inductInfo info)).constants Q nextEnv :=
            .inductStaging add head.2 preTr
          have postHas : nextEnv.HasPrimitives :=
            VEnv.HasPrimitives.addConst preHas rawName.1 added
          have postSafe : ∀ {n ci},
              (kernelEnv.add (.inductInfo info)).find? n = some ci →
                Environment.primitives.contains n →
                ci.safety = .safe ∧ ci.levelParams = [] :=
            TypeChecker.AddInductConstant.safePrimitives add mapWF preSafe
              rawName.2
          have nextMapWF :
              (kernelEnv.add (.inductInfo info)).constants.WF := by
            rw [add.map_add]
            exact mapWF.insert _ _ add.map_fresh
          have le : env ≤ nextEnv := VEnv.addConst_le added
          have rest' : List.Forall₂
              (fun info raw =>
                TrConstVal .safe nextEnv (.inductInfo info)
                    raw.toVConstVal ∧
                  raw.toVConstant.WF nextEnv)
              infos raws := by
            exact Lean4Lean.List.Forall₂.imp (h := rest) fun _ _ h =>
              ⟨⟨⟨h.1.1.1, h.1.1.2.1, h.1.1.2.2.mono le⟩,
                h.1.2⟩, h.2.mono le⟩
          exact ih tailStage rest' restNames nextMapWF postTr postHas
            postSafe

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
    exact Lean4Lean.List.Forall₂.imp (h := run.constructors) fun _ _ h => by
      obtain ⟨_, hctor⟩ := h
      exact hctor.isDefEq.toU

/-- Checker-validated normalization for an arbitrary mutual block.

Family equalities are interpreted in the common pre-family environment.  The
raw family constants are then staged as one exact source-ordered fold, and
all constructor equalities are interpreted in the resulting shared block
environment. -/
structure NormalizationBlockRun {source : VInductDecl}
    (norm : Normalization source) (env blockEnv : VEnv) where
  stage : env.stageInductiveTypes source.types = some blockEnv
  families : List.Forall₂
    (fun raw view =>
      (∃ A, TypeChecker.DefEqEvidence env source.uvars []
        raw.type view.type A) ∧
      List.Forall₂
        (fun rawCtor viewCtor =>
          ∃ A, TypeChecker.DefEqEvidence blockEnv source.uvars []
            rawCtor.type viewCtor.type A)
        raw.ctors view.ctors)
    source.types norm.view.types

/-- The verified checker interpretation discharges the complete Theory
mutual-normalization contract without a singleton projection. -/
theorem NormalizationBlockRun.wf
    (run : NormalizationBlockRun norm env blockEnv) :
    norm.BlockWF env blockEnv := by
  refine ⟨run.stage, ?_⟩
  exact Lean4Lean.List.Forall₂.imp (h := run.families) fun _ _ h => by
    refine ⟨h.1.choose_spec.isDefEq.toU, ?_⟩
    exact Lean4Lean.List.Forall₂.imp (h := h.2) fun _ _ hctor =>
      hctor.choose_spec.isDefEq.toU

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
    simpa only [run.uvars_eq, CandidateFamilyRun.view] using
      run.family.typeRun.evidence
  typeEnv := run.family.typeEnv
  addType := run.family.addType
  constructors := by
    simpa only [run.uvars_eq, CandidateFamilyRun.view] using
      run.family.constructors.evidence

/-- One constructor whose exact recursive candidate semantics are retained,
rather than reconstructed separately for normalization and generation.

The header remains indexed by the kernel source and raw Theory constant. The
semantic root owns the checker-selected view, its inferred type, and the
recursive run used by both downstream phases. -/
structure CandidateConstructorSemanticRun (env : VEnv) (Us : List Name)
    {source : Constructor}
    (candidate : AddInductive.CandidateConstructor source)
    (raw : VConstVal) where
  name_eq : source.name = raw.name
  uvars_eq : raw.uvars = Us.length
  type : TypeChecker.CandidateExprSemanticRootRun env Us candidate.type
    raw.type

/-- Project the normalization-facing constructor root without losing its
source or position indices. -/
def CandidateConstructorSemanticRun.root
    (run : CandidateConstructorSemanticRun env Us candidate raw) :
    CandidateConstructorRun env Us candidate raw where
  name_eq := run.name_eq
  uvars_eq := run.uvars_eq
  viewType := run.type.view
  typeRun := run.type.root

/-- Exact positional semantic ownership for an arbitrary constructor list.
Every element retains the recursive run selected at that source position; the
list cannot truncate, reorder, or reuse a run for another constructor. -/
inductive CandidateConstructorSemanticListRun
    (env : VEnv) (Us : List Name) :
    {sources : List Constructor} →
      AddInductive.CandidateList AddInductive.CandidateConstructor sources →
      List VConstVal → Type where
  | nil : CandidateConstructorSemanticListRun env Us .nil []
  | cons
      (head : CandidateConstructorSemanticRun env Us candidate raw)
      (tail : CandidateConstructorSemanticListRun env Us candidates raws) :
      CandidateConstructorSemanticListRun env Us
        (.cons candidate candidates) (raw :: raws)

/-- Forget only the retained recursive-run payload and recover the existing
normalization-facing positional list. -/
def CandidateConstructorSemanticListRun.roots :
    CandidateConstructorSemanticListRun env Us candidates raws →
      CandidateConstructorListRun env Us candidates raws
  | .nil => .nil
  | .cons head tail => .cons head.root tail.roots

/-- The raw Theory constructor inventory carried by a semantic list preserves
the complete kernel source-name order. -/
theorem CandidateConstructorSemanticListRun.rawNames
    {kernelSources : List Constructor}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor kernelSources}
    {raws : List VConstVal}
    (run : CandidateConstructorSemanticListRun env Us candidates raws) :
    raws.map (·.name) = kernelSources.map (·.name) := by
  induction run with
  | nil => rfl
  | cons head tail ih =>
      simp only [List.map_cons, ← head.name_eq, ih]

/-- Replacing constructor expression payloads leaves the exact source-order
name inventory unchanged. -/
theorem CandidateConstructorSemanticListRun.viewNames
    {kernelSources : List Constructor}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor kernelSources}
    {raws : List VConstVal}
    (run : CandidateConstructorSemanticListRun env Us candidates raws) :
    run.roots.views.map (·.name) = kernelSources.map (·.name) := by
  induction run with
  | nil => rfl
  | cons head tail ih =>
      simp only [CandidateConstructorSemanticListRun.roots,
        CandidateConstructorListRun.views, List.map_cons,
        CandidateConstructorSemanticRun.root, CandidateConstructorRun.view,
        ← head.name_eq, ih]

/-- One family in a mutual normalization candidate.  Its type is interpreted
in the common pre-family environment, while every constructor is interpreted
in the single environment obtained after staging the complete raw family
block. -/
structure CandidateBlockFamilySemanticRun
    (env blockEnv : VEnv) (Us : List Name)
    {source : InductiveType}
    (candidate : AddInductive.CandidateFamily source)
    (raw : VInductiveType) where
  name_eq : source.name = raw.name
  uvars_eq : raw.uvars = Us.length
  type : TypeChecker.CandidateExprSemanticRootRun env Us
    candidate.familyType.type raw.type
  constructors : CandidateConstructorSemanticListRun blockEnv Us
    candidate.constructors raw.ctors

/-- Replace only the expression payloads selected by the retained checker
runs; all family and constructor headers remain raw and source-indexed. -/
def CandidateBlockFamilySemanticRun.view
    (run : CandidateBlockFamilySemanticRun env blockEnv Us candidate raw) :
    VInductiveType :=
  { raw with
    type := run.type.view
    ctors := run.constructors.roots.views }

/-- Exact source-order semantic ownership for every family in an arbitrary
block.  Both the kernel candidate list and raw Theory list are indices, so
family reordering and truncation are unrepresentable. -/
inductive CandidateBlockFamilySemanticListRun
    (env blockEnv : VEnv) (Us : List Name) :
    {sources : List InductiveType} →
      AddInductive.CandidateList AddInductive.CandidateFamily sources →
      List VInductiveType → Type where
  | nil : CandidateBlockFamilySemanticListRun env blockEnv Us .nil []
  | cons
      (head : CandidateBlockFamilySemanticRun env blockEnv Us candidate raw)
      (tail : CandidateBlockFamilySemanticListRun env blockEnv Us
        candidates raws) :
      CandidateBlockFamilySemanticListRun env blockEnv Us
        (.cons candidate candidates) (raw :: raws)

/-- Total tail projection for a source-indexed nonempty candidate list. -/
def _root_.Lean4Lean.AddInductive.CandidateList.tail
    (candidates : AddInductive.CandidateList F (source :: sources)) :
    AddInductive.CandidateList F sources := by
  cases candidates with
  | cons head tail => exact tail

/-- Eta law for a source-indexed nonempty candidate list. -/
theorem _root_.Lean4Lean.AddInductive.CandidateList.cons_eta
    (candidates : AddInductive.CandidateList F (source :: sources)) :
    candidates = .cons candidates.head candidates.tail := by
  cases candidates
  rfl

/-- Parameter-prefix evidence at the head of a nonempty family candidate
list. -/
theorem _root_.Lean4Lean.AddInductive.CandidateFamilyParameterSpineList.head
    {nparams : Nat} {source : InductiveType}
    {sources : List InductiveType}
    {candidates : AddInductive.CandidateList AddInductive.CandidateFamily
      (source :: sources)}
    (run : AddInductive.CandidateFamilyParameterSpineList nparams
      candidates) :
    nparams ≤ candidates.head.familyType.type.trace.spineLength := by
  cases run with
  | cons family tail => exact family

/-- Parameter-prefix evidence after the head of a nonempty family candidate
list. -/
theorem _root_.Lean4Lean.AddInductive.CandidateFamilyParameterSpineList.tail
    {nparams : Nat} {source : InductiveType}
    {sources : List InductiveType}
    {candidates : AddInductive.CandidateList AddInductive.CandidateFamily
      (source :: sources)}
    (run : AddInductive.CandidateFamilyParameterSpineList nparams
      candidates) :
    AddInductive.CandidateFamilyParameterSpineList nparams
      candidates.tail := by
  cases run with
  | cons family tail => exact tail

/-- Terminal-sort evidence at the head of a nonempty family-type candidate
list. -/
theorem _root_.Lean4Lean.AddInductive.CandidateFamilyTypeTerminalSortList.head
    {source : InductiveType} {sources : List InductiveType}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateFamilyType (source :: sources)}
    (run : AddInductive.CandidateFamilyTypeTerminalSortList candidates) :
    ∃ resultLevel,
      candidates.head.type.trace.terminalResult = .sort resultLevel := by
  cases run with
  | cons terminal tail => exact ⟨_, terminal⟩

/-- Terminal-sort evidence after the head of a nonempty family-type
candidate list. -/
theorem _root_.Lean4Lean.AddInductive.CandidateFamilyTypeTerminalSortList.tail
    {source : InductiveType} {sources : List InductiveType}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateFamilyType (source :: sources)}
    (run : AddInductive.CandidateFamilyTypeTerminalSortList candidates) :
    AddInductive.CandidateFamilyTypeTerminalSortList candidates.tail := by
  cases run with
  | cons terminal tail => exact tail

/-- Exact validator annotation provenance for every family candidate in
source order. -/
inductive CandidateFamilyValidationAnnotationList
    (candidateContext : AddInductive.Context) :
    {sources : List InductiveType} →
      AddInductive.CandidateList AddInductive.CandidateFamily sources →
      Prop where
  | nil : CandidateFamilyValidationAnnotationList candidateContext .nil
  | cons
      (head : candidate.familyType.type.trace.validationAnnotations)
      (context_eq : candidate.familyType.type.context = candidateContext)
      (resultLevel : Level)
      (terminal_eq : candidate.familyType.type.trace.terminalResult =
        .sort resultLevel)
      (tail : CandidateFamilyValidationAnnotationList candidateContext
        candidates) :
      CandidateFamilyValidationAnnotationList candidateContext
        (.cons candidate candidates)

/-- Project the exact validation annotations from the retained family-type
normalization traversal. -/
theorem CandidateFamilyValidationAnnotationList.ofProduced
    {candidateContext : AddInductive.Context}
    {sources : List InductiveType}
    (candidates : AddInductive.CandidateList
      AddInductive.CandidateFamily sources)
    (produced : AddInductive.CandidateFamilyTypeListProduced candidateContext
      candidates.familyTypes)
    (terminals : AddInductive.CandidateFamilyTypeTerminalSortList
      candidates.familyTypes) :
    CandidateFamilyValidationAnnotationList candidateContext candidates := by
  induction candidates with
  | nil => exact .nil
  | cons candidate candidates ih =>
    obtain ⟨resultLevel, terminalEq⟩ := terminals.head
    exact .cons
      (candidate.familyType.validationAnnotations_of_normalize produced.head)
      (candidate.familyType.context_eq_of_normalize produced.head)
      resultLevel terminalEq
      (ih produced.tail terminals.tail)

/-- Annotation provenance at the head of a nonempty family candidate list. -/
theorem CandidateFamilyValidationAnnotationList.head
    (run : CandidateFamilyValidationAnnotationList candidateContext
      (candidates : AddInductive.CandidateList AddInductive.CandidateFamily
        (source :: sources))) :
    candidates.head.familyType.type.trace.validationAnnotations := by
  cases run with
  | cons head contextEq resultLevel terminalEq tail => exact head

/-- The exact producer context stored by the head family candidate. -/
theorem CandidateFamilyValidationAnnotationList.head_context_eq
    (run : CandidateFamilyValidationAnnotationList candidateContext
      (candidates : AddInductive.CandidateList AddInductive.CandidateFamily
        (source :: sources))) :
    candidates.head.familyType.type.context = candidateContext := by
  cases run with
  | cons head contextEq resultLevel terminalEq tail => exact contextEq

/-- The exact terminal sort retained by the head family candidate. -/
theorem CandidateFamilyValidationAnnotationList.head_terminal
    (run : CandidateFamilyValidationAnnotationList candidateContext
      (candidates : AddInductive.CandidateList AddInductive.CandidateFamily
        (source :: sources))) :
    ∃ resultLevel,
      candidates.head.familyType.type.trace.terminalResult =
        .sort resultLevel := by
  cases run with
  | cons head contextEq resultLevel terminalEq tail =>
    exact ⟨resultLevel, terminalEq⟩

/-- Validation provenance after the head family. -/
theorem CandidateFamilyValidationAnnotationList.tail
    (run : CandidateFamilyValidationAnnotationList candidateContext
      (candidates : AddInductive.CandidateList AddInductive.CandidateFamily
        (source :: sources))) :
    CandidateFamilyValidationAnnotationList candidateContext
      candidates.tail := by
  cases run with
  | cons head contextEq resultLevel terminalEq tail => exact tail

/-- Exact semantic family at the head of a nonempty dependent list. -/
def CandidateBlockFamilySemanticListRun.head
    (run : CandidateBlockFamilySemanticListRun env blockEnv Us
      (.cons candidate candidates) (raw :: raws)) :
    CandidateBlockFamilySemanticRun env blockEnv Us candidate raw := by
  cases run with
  | cons head tail => exact head

/-- Exact semantic suffix after the head of a nonempty dependent list. -/
def CandidateBlockFamilySemanticListRun.tail
    (run : CandidateBlockFamilySemanticListRun env blockEnv Us
      (.cons candidate candidates) (raw :: raws)) :
    CandidateBlockFamilySemanticListRun env blockEnv Us candidates raws := by
  cases run with
  | cons head tail => exact tail

/-- Canonical dependent decomposition of a semantic family list whose kernel
source index is nonempty.  The raw-list equation and candidate-list eta law
make the extracted head and tail exact, even though the raw list itself is not
length-indexed. -/
structure CandidateBlockFamilySemanticListRun.Head
    {kernelSource : InductiveType}
    {remainingSources : List InductiveType}
    {candidates : AddInductive.CandidateList AddInductive.CandidateFamily
      (kernelSource :: remainingSources)}
    {raws : List VInductiveType}
    (run : CandidateBlockFamilySemanticListRun env blockEnv Us candidates
      raws) where
  raw : VInductiveType
  remainingRaws : List VInductiveType
  raws_eq : raws = raw :: remainingRaws
  semantic : CandidateBlockFamilySemanticRun env blockEnv Us candidates.head
    raw
  tail : CandidateBlockFamilySemanticListRun env blockEnv Us candidates.tail
    remainingRaws

/-- Extract the canonical semantic head/tail decomposition of a nonempty
source-indexed family list. -/
def CandidateBlockFamilySemanticListRun.headPosition
    {kernelSource : InductiveType}
    {remainingSources : List InductiveType}
    {candidates : AddInductive.CandidateList AddInductive.CandidateFamily
      (kernelSource :: remainingSources)}
    {raws : List VInductiveType}
    (run : CandidateBlockFamilySemanticListRun env blockEnv Us candidates
      raws) : run.Head := by
  cases run with
  | cons head tail =>
    exact {
      raw := _
      remainingRaws := _
      raws_eq := rfl
      semantic := head
      tail := tail }

/-- The canonical head projection of a concrete semantic cons returns that
cons cell's exact normalized family view. -/
theorem CandidateBlockFamilySemanticListRun.headPosition_cons_view
    (semantic : CandidateBlockFamilySemanticRun env blockEnv Us candidate raw)
    (semantics : CandidateBlockFamilySemanticListRun env blockEnv Us
      candidates raws) :
    (CandidateBlockFamilySemanticListRun.cons semantic semantics
      |>.headPosition.semantic.type.view) = semantic.type.view := by
  rfl

/-- Lightweight evidence that one semantic hierarchy consists of two exact
heads followed by one exact dependent suffix.  The relation retains all
source, candidate, and raw indices without placing a computed erasure in
downstream structure types. -/
inductive CandidateBlockFamilySemanticListRun.TwoHead
    (env blockEnv : VEnv) (Us : List Name) :
    {sources : List InductiveType} →
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateFamily sources} →
    {raws : List VInductiveType} →
    CandidateBlockFamilySemanticListRun env blockEnv Us candidates raws →
    {firstSource : InductiveType} →
    {firstCandidate : AddInductive.CandidateFamily firstSource} →
    {firstRaw : VInductiveType} →
    CandidateBlockFamilySemanticRun env blockEnv Us firstCandidate firstRaw →
    {secondSource : InductiveType} →
    {secondCandidate : AddInductive.CandidateFamily secondSource} →
    {secondRaw : VInductiveType} →
    CandidateBlockFamilySemanticRun env blockEnv Us secondCandidate secondRaw →
    {remainingSources : List InductiveType} →
    {remainingCandidates : AddInductive.CandidateList
      AddInductive.CandidateFamily remainingSources} →
    {remainingRaws : List VInductiveType} →
    CandidateBlockFamilySemanticListRun env blockEnv Us remainingCandidates
      remainingRaws → Prop where
  | cons
      (first : CandidateBlockFamilySemanticRun env blockEnv Us
        firstCandidate firstRaw)
      (second : CandidateBlockFamilySemanticRun env blockEnv Us
        secondCandidate secondRaw)
      (remaining : CandidateBlockFamilySemanticListRun env blockEnv Us
        remainingCandidates remainingRaws) :
      CandidateBlockFamilySemanticListRun.TwoHead env blockEnv Us
        (CandidateBlockFamilySemanticListRun.cons first
          (CandidateBlockFamilySemanticListRun.cons second remaining))
        first second remaining

/-- Select the lightweight two-head decomposition at the canonical first and
second positions of any semantic hierarchy with at least two sources. -/
theorem CandidateBlockFamilySemanticListRun.twoHeadPositions
    {firstSource secondSource : InductiveType}
    {remainingSources : List InductiveType}
    {candidates : AddInductive.CandidateList AddInductive.CandidateFamily
      (firstSource :: secondSource :: remainingSources)}
    {raws : List VInductiveType}
    (run : CandidateBlockFamilySemanticListRun env blockEnv Us candidates
      raws) :
    CandidateBlockFamilySemanticListRun.TwoHead env blockEnv Us run
      run.headPosition.semantic
      run.headPosition.tail.headPosition.semantic
      run.headPosition.tail.headPosition.tail := by
  cases run with
  | cons first tail =>
    cases tail with
    | cons second remaining => exact .cons first second remaining

/-- Projection-friendly semantic tail for a source-indexed nonempty list.
The semantic proof rules out an empty raw list internally. -/
def CandidateBlockFamilySemanticListRun.tailExact
    {kernelSource : InductiveType}
    {remainingSources : List InductiveType}
    {candidates : AddInductive.CandidateList AddInductive.CandidateFamily
      (kernelSource :: remainingSources)}
    {raws : List VInductiveType}
    (run : CandidateBlockFamilySemanticListRun env blockEnv Us candidates
      raws) :
    CandidateBlockFamilySemanticListRun env blockEnv Us candidates.tail
      raws.tail := by
  cases candidates with
  | cons candidate candidates =>
      cases raws with
      | nil => cases run
      | cons raw raws => exact run.tail

/-- Translate the exact raw family selected by the canonical semantic head at
an arbitrary verified validation context. -/
theorem CandidateBlockFamilySemanticListRun.headSourceTranslation
    {kernelSource : InductiveType}
    {remainingSources : List InductiveType}
    {candidates : AddInductive.CandidateList AddInductive.CandidateFamily
      (kernelSource :: remainingSources)}
    {raws : List VInductiveType}
    (run : CandidateBlockFamilySemanticListRun env blockEnv Us candidates
      raws)
    (contextRun : TypeChecker.CandidateContextRun context)
    (venv_eq : contextRun.context.venv = env)
    (lparams_eq : contextRun.context.lparams = Us) :
    contextRun.context.TrExprS kernelSource.type
      run.headPosition.raw.type := by
  cases run with
  | cons head tail =>
    exact contextRun.rootTranslation venv_eq lparams_eq head.type.source_tr

/-- Exact normalized family views in source order. -/
def CandidateBlockFamilySemanticListRun.views :
    CandidateBlockFamilySemanticListRun env blockEnv Us candidates raws →
      List VInductiveType
  | .nil => []
  | .cons head tail => head.view :: tail.views

/-- Erasing a lightweight two-head decomposition yields the corresponding
normalized family views in exact source order. -/
theorem CandidateBlockFamilySemanticListRun.TwoHead.views_eq
    {run : CandidateBlockFamilySemanticListRun env blockEnv Us candidates raws}
    {first : CandidateBlockFamilySemanticRun env blockEnv Us
      firstCandidate firstRaw}
    {second : CandidateBlockFamilySemanticRun env blockEnv Us
      secondCandidate secondRaw}
    {remaining : CandidateBlockFamilySemanticListRun env blockEnv Us
      remainingCandidates remainingRaws}
    (decomposition : CandidateBlockFamilySemanticListRun.TwoHead env
      blockEnv Us run first second remaining) :
    run.views = first.view :: second.view :: remaining.views := by
  cases decomposition
  rfl

/-- Exact source-order evidence that every family view uses a parameter
telescope definitionally equal to one distinguished family view.  The
semantic list is an index, so entries cannot be reordered, truncated, or
paired with a view from another candidate position. -/
inductive CandidateBlockFamilyViewParameterDefEqList
    (env blockEnv : VEnv) (Us : List Name) (nparams : Nat)
    (firstView : VExpr) :
    {sources : List InductiveType} →
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateFamily sources} →
    {raws : List VInductiveType} →
    CandidateBlockFamilySemanticListRun env blockEnv Us candidates raws →
      Prop where
  | nil : CandidateBlockFamilyViewParameterDefEqList env blockEnv Us
      nparams firstView .nil
  | cons
      (head : TypeChecker.TelDefEqEvidence env Us.length []
        (VExpr.telN nparams firstView)
        (VExpr.telN nparams semantic.type.view))
      (tail : CandidateBlockFamilyViewParameterDefEqList env blockEnv Us
        nparams firstView semantics) :
      CandidateBlockFamilyViewParameterDefEqList env blockEnv Us nparams
        firstView (.cons semantic semantics)

/-- Erase the dependent semantic indices while retaining exact source-order
parameter-telescope equality for every normalized family view. -/
theorem CandidateBlockFamilyViewParameterDefEqList.forall_views
    {nparams : Nat} {firstView : VExpr}
    {semantics : CandidateBlockFamilySemanticListRun env blockEnv Us
      candidates raws}
    (evidence : CandidateBlockFamilyViewParameterDefEqList env blockEnv Us
      nparams firstView semantics) :
    List.All
      (fun family => TypeChecker.TelDefEqEvidence env Us.length []
        (VExpr.telN nparams firstView)
        (VExpr.telN nparams family.type))
      semantics.views := by
  induction evidence with
  | nil => trivial
  | cons head tail ih =>
    exact ⟨by
      simpa only [CandidateBlockFamilySemanticRun.view] using head, ih⟩

/-- Translate every stored family source at one arbitrary verified validation
context with the same Theory environment and level parameters.

The dependent semantic list fixes source and raw-family order.  Root
translations were originally certified at the producer's empty local context;
`CandidateContextRun.rootTranslation` weakens each closed Theory root into the
validator's accumulated free-variable context without changing its syntax. -/
theorem CandidateBlockFamilySemanticListRun.sourceTranslations
    {kernelSources : List InductiveType}
    {candidates : AddInductive.CandidateList AddInductive.CandidateFamily
      kernelSources}
    {raws : List VInductiveType}
    (run : CandidateBlockFamilySemanticListRun env blockEnv Us candidates
      raws)
    (contextRun : TypeChecker.CandidateContextRun context)
    (venv_eq : contextRun.context.venv = env)
    (lparams_eq : contextRun.context.lparams = Us) :
    List.Forall₂
      (fun source raw =>
        contextRun.context.TrExprS source.type raw.type)
      kernelSources raws := by
  induction run with
  | nil => exact .nil
  | cons head tail ih =>
      exact .cons
        (contextRun.rootTranslation venv_eq lparams_eq
          head.type.source_tr)
        ih

/-- A source-order cursor pairing one exact suffix of the outer family
validator with the matching suffix of the dependent semantic family list.

The `drop` equation prevents a terminal context from being attached to a
different family position.  The verified context is indexed by the reader
context at which the retained outer trace resumes, so recursive consumers can
advance through the trace without selecting another context or semantic
family list. -/
structure CandidateBlockFamilyValidationCursor
    (env blockEnv : VEnv) (Us : List Name)
    (nparams : Nat) (fullSources : List InductiveType)
    {remainingSources : List InductiveType}
    (candidates : AddInductive.CandidateList
      AddInductive.CandidateFamily remainingSources)
    (raws : List VInductiveType)
    {dIdx : Nat} {stats : AddInductive.InductiveStats}
    {candidateContext : AddInductive.Context}
    (trace : AddInductive.FamilyParameterComparisonBlockTrace nparams
      fullSources.toArray dIdx stats candidateContext) where
  sourceSuffix_eq : fullSources.drop dIdx = remainingSources
  semantics : CandidateBlockFamilySemanticListRun env blockEnv Us
    candidates raws
  contextRun : TypeChecker.CandidateContextRun candidateContext
  venv_eq : contextRun.context.venv = env
  lparams_eq : contextRun.context.lparams = Us

/-- A family-validation cursor whose current statistics are already in the
later-family phase.  These two counters are precisely the invariant preserved
by `FamilyContinuation.LaterInvariant` when the cursor advances. -/
structure CandidateBlockLaterFamilyValidationCursor
    (env blockEnv : VEnv) (Us : List Name)
    (nparams : Nat) (fullSources : List InductiveType)
    {remainingSources : List InductiveType}
    (candidates : AddInductive.CandidateList
      AddInductive.CandidateFamily remainingSources)
    (raws : List VInductiveType)
    {dIdx : Nat} {stats : AddInductive.InductiveStats}
    {candidateContext : AddInductive.Context}
    (trace : AddInductive.FamilyParameterComparisonBlockTrace nparams
      fullSources.toArray dIdx stats candidateContext)
    extends CandidateBlockFamilyValidationCursor env blockEnv Us nparams
      fullSources candidates raws trace where
  current_localState : TypeChecker.FamilyParameterLocalState stats
    candidateContext
  parameterSources : List Expr
  current_parameterSources_eq : stats.params.toList = parameterSources
  current_indConsts_nonempty : stats.indConsts.isEmpty = false
  current_params_size : stats.params.size = nparams

/-- A nonempty later-family cursor exposes the exact outer continuation at its
semantic head, together with the stable counters required by its dependent
tail. -/
theorem CandidateBlockLaterFamilyValidationCursor.headContinuation
    {env blockEnv : VEnv} {Us : List Name} {nparams : Nat}
    {fullSources : List InductiveType}
    {remainingSources : List InductiveType}
    {candidates : AddInductive.CandidateList AddInductive.CandidateFamily
      remainingSources}
    {raws : List VInductiveType}
    {dIdx : Nat} {stats : AddInductive.InductiveStats}
    {candidateContext : AddInductive.Context}
    {trace : AddInductive.FamilyParameterComparisonBlockTrace nparams
      fullSources.toArray dIdx stats candidateContext}
    (cursor : CandidateBlockLaterFamilyValidationCursor env blockEnv Us
      nparams fullSources candidates raws trace)
    (nonempty : remainingSources.isEmpty = false) :
    ∃ continuation, trace.headContinuation? = some continuation ∧
      continuation.LaterInvariant := by
  have remainingLengthPos : 0 < remainingSources.length := by
    cases remainingSources with
    | nil => simp at nonempty
    | cons => simp
  cases trace with
  | firstFamily dIdx stats context inBounds closed inferred root checkType
      rootWhnf telescope sorted ensureSort isFirst tail =>
    refine ⟨_, rfl, ?_⟩
    have first : stats.indConsts.isEmpty = true := by
      rw [← telescope.result_indConsts_eq]
      exact isFirst
    have later := cursor.current_indConsts_nonempty
    rw [first] at later
    contradiction
  | laterFamily dIdx stats context inBounds closed inferred root checkType
      rootWhnf telescope sorted ensureSort isLater resultLevelCompatible tail =>
    refine ⟨_, rfl, ?_⟩
    refine ⟨cursor.current_indConsts_nonempty, cursor.current_params_size,
      ?_, ?_⟩
    · simp
    · exact telescope.result_params_size_of_later
        cursor.current_indConsts_nonempty cursor.current_params_size
  | terminal dIdx stats context outOfBounds =>
    have sourceLength := congrArg List.length cursor.sourceSuffix_eq
    have lengthLe : fullSources.length ≤ dIdx := by
      apply Nat.le_of_not_gt
      simpa using outOfBounds
    simp only [List.length_drop] at sourceLength
    omega

/-- Reindex the cursor's genuine shared-parameter inventory onto the exact
reader state stored by its selected head continuation. -/
theorem CandidateBlockLaterFamilyValidationCursor.headLocalState
    {env blockEnv : VEnv} {Us : List Name} {nparams : Nat}
    {fullSources remainingSources : List InductiveType}
    {candidates : AddInductive.CandidateList AddInductive.CandidateFamily
      remainingSources}
    {raws : List VInductiveType}
    {dIdx : Nat} {stats : AddInductive.InductiveStats}
    {candidateContext : AddInductive.Context}
    {trace : AddInductive.FamilyParameterComparisonBlockTrace nparams
      fullSources.toArray dIdx stats candidateContext}
    (cursor : CandidateBlockLaterFamilyValidationCursor env blockEnv Us
      nparams fullSources candidates raws trace)
    (continuation :
      AddInductive.FamilyParameterComparisonBlockTrace.FamilyContinuation
        nparams fullSources.toArray)
    (selected : trace.headContinuation? = some continuation) :
    TypeChecker.FamilyParameterLocalState continuation.stats
      continuation.context := by
  rw [AddInductive.FamilyParameterComparisonBlockTrace.headContinuation?_stats
    selected]
  rw [AddInductive.FamilyParameterComparisonBlockTrace.headContinuation?_context
    selected]
  exact cursor.current_localState

/-- Advance one nonempty later-family cursor after the caller has constructed
the verified context at that family's exact telescope endpoint.

The selected continuation fixes the next outer trace.  Taking one source
from the cursor's `drop` equation fixes the dependent semantic tail, while
the continuation invariant supplies the two counters for the recursive
cursor.  Thus neither the next source list nor the next validator state can
be chosen independently. -/
def CandidateBlockLaterFamilyValidationCursor.advance
    {env blockEnv : VEnv} {Us : List Name} {nparams : Nat}
    {fullSources : List InductiveType}
    {source : InductiveType} {remainingSources : List InductiveType}
    {candidate : AddInductive.CandidateFamily source}
    {candidates : AddInductive.CandidateList AddInductive.CandidateFamily
      remainingSources}
    {raw : VInductiveType} {raws : List VInductiveType}
    {dIdx : Nat} {stats : AddInductive.InductiveStats}
    {candidateContext : AddInductive.Context}
    {trace : AddInductive.FamilyParameterComparisonBlockTrace nparams
      fullSources.toArray dIdx stats candidateContext}
    (cursor : CandidateBlockLaterFamilyValidationCursor env blockEnv Us
      nparams fullSources (.cons candidate candidates) (raw :: raws) trace)
    (continuation :
      AddInductive.FamilyParameterComparisonBlockTrace.FamilyContinuation
        nparams fullSources.toArray)
    (selected : trace.headContinuation? = some continuation)
    (invariant : continuation.LaterInvariant)
    (nextRun : TypeChecker.CandidateContextRun
      continuation.telescope.result.context)
    (next_venv : nextRun.context.venv = env)
    (next_lparams : nextRun.context.lparams = Us) :
    CandidateBlockLaterFamilyValidationCursor env blockEnv Us nparams
      fullSources candidates raws continuation.tail := by
  have dIdxEq :=
    AddInductive.FamilyParameterComparisonBlockTrace.headContinuation?_dIdx
      selected
  refine {
    sourceSuffix_eq := ?_
    semantics := cursor.semantics.tail
    contextRun := nextRun
    venv_eq := next_venv
    lparams_eq := next_lparams
    current_localState :=
      AddInductive.FamilyParameterComparisonBlockTrace.headContinuation?_nextLocalState
        selected (cursor.headLocalState continuation selected)
        invariant.current_indConsts_nonempty invariant.current_params_size
    parameterSources := cursor.parameterSources
    current_parameterSources_eq := by
      calc
        continuation.nextStats.params.toList =
            continuation.stats.params.toList :=
          congrArg Array.toList
            (AddInductive.FamilyParameterComparisonBlockTrace.headContinuation?_nextParams_eq
              selected invariant.current_indConsts_nonempty)
        _ = stats.params.toList :=
          congrArg (fun currentStats => currentStats.params.toList)
            (AddInductive.FamilyParameterComparisonBlockTrace.headContinuation?_stats
              selected)
        _ = cursor.parameterSources := cursor.current_parameterSources_eq
    current_indConsts_nonempty := invariant.next_indConsts_nonempty
    current_params_size := invariant.next_params_size }
  have suffixEq := congrArg (List.drop 1) cursor.sourceSuffix_eq
  simpa [List.drop_drop, dIdxEq] using suffixEq

/-- Projection-friendly form of `advance` for a source-indexed nonempty
cursor.  The semantic list rules out an empty raw list and supplies the
dependent candidate/raw head decomposition internally. -/
def CandidateBlockLaterFamilyValidationCursor.advanceHead
    {env blockEnv : VEnv} {Us : List Name} {nparams : Nat}
    {fullSources : List InductiveType}
    {source : InductiveType} {remainingSources : List InductiveType}
    {candidates : AddInductive.CandidateList AddInductive.CandidateFamily
      (source :: remainingSources)}
    {raws : List VInductiveType}
    {dIdx : Nat} {stats : AddInductive.InductiveStats}
    {candidateContext : AddInductive.Context}
    {trace : AddInductive.FamilyParameterComparisonBlockTrace nparams
      fullSources.toArray dIdx stats candidateContext}
    (cursor : CandidateBlockLaterFamilyValidationCursor env blockEnv Us
      nparams fullSources candidates raws trace)
    (continuation :
      AddInductive.FamilyParameterComparisonBlockTrace.FamilyContinuation
        nparams fullSources.toArray)
    (selected : trace.headContinuation? = some continuation)
    (invariant : continuation.LaterInvariant)
    (nextRun : TypeChecker.CandidateContextRun
      continuation.telescope.result.context)
    (next_venv : nextRun.context.venv = env)
    (next_lparams : nextRun.context.lparams = Us) :
    CandidateBlockLaterFamilyValidationCursor env blockEnv Us nparams
      fullSources candidates.tail raws.tail continuation.tail := by
  cases candidates with
  | cons candidate candidates =>
      cases raws with
      | nil => cases cursor.semantics
      | cons raw raws =>
          exact cursor.advance continuation selected invariant nextRun
            next_venv next_lparams

/-- The projection-friendly advance stores exactly the supplied endpoint
run. -/
theorem CandidateBlockLaterFamilyValidationCursor.advanceHead_context
    {env blockEnv : VEnv} {Us : List Name} {nparams : Nat}
    {fullSources : List InductiveType}
    {source : InductiveType} {remainingSources : List InductiveType}
    {candidates : AddInductive.CandidateList AddInductive.CandidateFamily
      (source :: remainingSources)}
    {raws : List VInductiveType}
    {dIdx : Nat} {stats : AddInductive.InductiveStats}
    {candidateContext : AddInductive.Context}
    {trace : AddInductive.FamilyParameterComparisonBlockTrace nparams
      fullSources.toArray dIdx stats candidateContext}
    (cursor : CandidateBlockLaterFamilyValidationCursor env blockEnv Us
      nparams fullSources candidates raws trace)
    (continuation :
      AddInductive.FamilyParameterComparisonBlockTrace.FamilyContinuation
        nparams fullSources.toArray)
    (selected : trace.headContinuation? = some continuation)
    (invariant : continuation.LaterInvariant)
    (nextRun : TypeChecker.CandidateContextRun
      continuation.telescope.result.context)
    (next_venv : nextRun.context.venv = env)
    (next_lparams : nextRun.context.lparams = Us) :
    (cursor.advanceHead continuation selected invariant nextRun next_venv
      next_lparams).contextRun.context = nextRun.context := by
  cases candidates with
  | cons candidate candidates =>
      cases raws with
      | nil => cases cursor.semantics
      | cons raw raws => rfl

/-- Source-order advancement preserves the literal shared-parameter source
inventory. -/
theorem CandidateBlockLaterFamilyValidationCursor.advanceHead_parameterSources
    {env blockEnv : VEnv} {Us : List Name} {nparams : Nat}
    {fullSources : List InductiveType}
    {source : InductiveType} {remainingSources : List InductiveType}
    {candidates : AddInductive.CandidateList AddInductive.CandidateFamily
      (source :: remainingSources)}
    {raws : List VInductiveType}
    {dIdx : Nat} {stats : AddInductive.InductiveStats}
    {candidateContext : AddInductive.Context}
    {trace : AddInductive.FamilyParameterComparisonBlockTrace nparams
      fullSources.toArray dIdx stats candidateContext}
    (cursor : CandidateBlockLaterFamilyValidationCursor env blockEnv Us
      nparams fullSources candidates raws trace)
    (continuation :
      AddInductive.FamilyParameterComparisonBlockTrace.FamilyContinuation
        nparams fullSources.toArray)
    (selected : trace.headContinuation? = some continuation)
    (invariant : continuation.LaterInvariant)
    (nextRun : TypeChecker.CandidateContextRun
      continuation.telescope.result.context)
    (next_venv : nextRun.context.venv = env)
    (next_lparams : nextRun.context.lparams = Us) :
    (cursor.advanceHead continuation selected invariant nextRun next_venv
      next_lparams).parameterSources = cursor.parameterSources := by
  cases candidates with
  | cons candidate candidates =>
      cases raws with
      | nil => cases cursor.semantics
      | cons raw raws => rfl

/-- Source-order advancement stores exactly the dependent semantic tail. -/
theorem CandidateBlockLaterFamilyValidationCursor.advanceHead_semantics
    {env blockEnv : VEnv} {Us : List Name} {nparams : Nat}
    {fullSources : List InductiveType}
    {source : InductiveType} {remainingSources : List InductiveType}
    {candidates : AddInductive.CandidateList AddInductive.CandidateFamily
      (source :: remainingSources)}
    {raws : List VInductiveType}
    {dIdx : Nat} {stats : AddInductive.InductiveStats}
    {candidateContext : AddInductive.Context}
    {trace : AddInductive.FamilyParameterComparisonBlockTrace nparams
      fullSources.toArray dIdx stats candidateContext}
    (cursor : CandidateBlockLaterFamilyValidationCursor env blockEnv Us
      nparams fullSources candidates raws trace)
    (continuation :
      AddInductive.FamilyParameterComparisonBlockTrace.FamilyContinuation
        nparams fullSources.toArray)
    (selected : trace.headContinuation? = some continuation)
    (invariant : continuation.LaterInvariant)
    (nextRun : TypeChecker.CandidateContextRun
      continuation.telescope.result.context)
    (next_venv : nextRun.context.venv = env)
    (next_lparams : nextRun.context.lparams = Us) :
    (cursor.advanceHead continuation selected invariant nextRun next_venv
      next_lparams).semantics = cursor.semantics.tailExact := by
  cases candidates with
  | cons candidate candidates =>
      cases raws with
      | nil => cases cursor.semantics
      | cons raw raws => rfl

/-- The semantic raw family at a nonempty cursor head is translated in the
cursor's exact verified validator context. -/
theorem CandidateBlockLaterFamilyValidationCursor.headSourceTranslation
    {env blockEnv : VEnv} {Us : List Name} {nparams : Nat}
    {fullSources : List InductiveType}
    {source : InductiveType} {remainingSources : List InductiveType}
    {candidates : AddInductive.CandidateList AddInductive.CandidateFamily
      (source :: remainingSources)}
    {raws : List VInductiveType}
    {dIdx : Nat} {stats : AddInductive.InductiveStats}
    {candidateContext : AddInductive.Context}
    {trace : AddInductive.FamilyParameterComparisonBlockTrace nparams
      fullSources.toArray dIdx stats candidateContext}
    (cursor : CandidateBlockLaterFamilyValidationCursor env blockEnv Us
      nparams fullSources candidates raws trace) :
    cursor.contextRun.context.TrExprS source.type
      cursor.semantics.headPosition.raw.type :=
  cursor.semantics.headSourceTranslation cursor.contextRun cursor.venv_eq
    cursor.lparams_eq

/-- The validator WHNF retained by a selected cursor head is indexed by that
same source family's kernel type.  The proof uses the cursor's source-suffix
equation, not a separate array lookup premise. -/
theorem CandidateBlockLaterFamilyValidationCursor.headRootWhnf
    {env blockEnv : VEnv} {Us : List Name} {nparams : Nat}
    {fullSources : List InductiveType}
    {source : InductiveType} {remainingSources : List InductiveType}
    {candidates : AddInductive.CandidateList AddInductive.CandidateFamily
      (source :: remainingSources)}
    {raws : List VInductiveType}
    {dIdx : Nat} {stats : AddInductive.InductiveStats}
    {candidateContext : AddInductive.Context}
    {trace : AddInductive.FamilyParameterComparisonBlockTrace nparams
      fullSources.toArray dIdx stats candidateContext}
    (cursor : CandidateBlockLaterFamilyValidationCursor env blockEnv Us
      nparams fullSources candidates raws trace)
    (continuation :
      AddInductive.FamilyParameterComparisonBlockTrace.FamilyContinuation
        nparams fullSources.toArray)
    (selected : trace.headContinuation? = some continuation) :
    AddInductive.CandidateWhnfStep.Valid
      ⟨continuation.context, source.type, continuation.source⟩ := by
  have dIdxEq :=
    AddInductive.FamilyParameterComparisonBlockTrace.headContinuation?_dIdx
      selected
  subst dIdx
  have dIdxBound : continuation.dIdx < fullSources.length := by
    simpa using continuation.inBounds
  have sourceEq : fullSources[continuation.dIdx] = source := by
    have suffixEq := cursor.sourceSuffix_eq
    rw [List.drop_eq_getElem_cons dIdxBound] at suffixEq
    exact (List.cons.inj suffixEq).1
  have arraySourceEq :
      fullSources.toArray[continuation.dIdx]'continuation.inBounds = source := by
    simpa using sourceEq
  have rootWhnf := continuation.rootWhnf
  rw [arraySourceEq] at rootWhnf
  exact rootWhnf

/-- Reindex the cursor's verified context onto the exact reader context stored
by its selected head continuation. -/
def CandidateBlockLaterFamilyValidationCursor.headContextRun
    {env blockEnv : VEnv} {Us : List Name} {nparams : Nat}
    {fullSources remainingSources : List InductiveType}
    {candidates : AddInductive.CandidateList AddInductive.CandidateFamily
      remainingSources}
    {raws : List VInductiveType}
    {dIdx : Nat} {stats : AddInductive.InductiveStats}
    {candidateContext : AddInductive.Context}
    {trace : AddInductive.FamilyParameterComparisonBlockTrace nparams
      fullSources.toArray dIdx stats candidateContext}
    (cursor : CandidateBlockLaterFamilyValidationCursor env blockEnv Us
      nparams fullSources candidates raws trace)
    (continuation :
      AddInductive.FamilyParameterComparisonBlockTrace.FamilyContinuation
        nparams fullSources.toArray)
    (selected : trace.headContinuation? = some continuation) :
    TypeChecker.CandidateContextRun continuation.context := by
  have contextEq :=
    AddInductive.FamilyParameterComparisonBlockTrace.headContinuation?_context
      selected
  exact contextEq.symm ▸ cursor.contextRun

/-- Transporting the verified cursor context onto its selected continuation
changes only the dependent implementation-context index. -/
theorem CandidateBlockLaterFamilyValidationCursor.headContextRun_context
    {env blockEnv : VEnv} {Us : List Name} {nparams : Nat}
    {fullSources remainingSources : List InductiveType}
    {candidates : AddInductive.CandidateList AddInductive.CandidateFamily
      remainingSources}
    {raws : List VInductiveType}
    {dIdx : Nat} {stats : AddInductive.InductiveStats}
    {candidateContext : AddInductive.Context}
    {trace : AddInductive.FamilyParameterComparisonBlockTrace nparams
      fullSources.toArray dIdx stats candidateContext}
    (cursor : CandidateBlockLaterFamilyValidationCursor env blockEnv Us
      nparams fullSources candidates raws trace)
    (continuation :
      AddInductive.FamilyParameterComparisonBlockTrace.FamilyContinuation
        nparams fullSources.toArray)
    (selected : trace.headContinuation? = some continuation) :
    (cursor.headContextRun continuation selected).context =
      cursor.contextRun.context := by
  unfold headContextRun
  apply TypeChecker.CandidateContextRun.cast_context_context

/-- Reindexing the cursor context onto its head continuation preserves the
semantic environment. -/
theorem CandidateBlockLaterFamilyValidationCursor.headContextRun_venv
    {env blockEnv : VEnv} {Us : List Name} {nparams : Nat}
    {fullSources remainingSources : List InductiveType}
    {candidates : AddInductive.CandidateList AddInductive.CandidateFamily
      remainingSources}
    {raws : List VInductiveType}
    {dIdx : Nat} {stats : AddInductive.InductiveStats}
    {candidateContext : AddInductive.Context}
    {trace : AddInductive.FamilyParameterComparisonBlockTrace nparams
      fullSources.toArray dIdx stats candidateContext}
    (cursor : CandidateBlockLaterFamilyValidationCursor env blockEnv Us
      nparams fullSources candidates raws trace)
    (continuation :
      AddInductive.FamilyParameterComparisonBlockTrace.FamilyContinuation
        nparams fullSources.toArray)
    (selected : trace.headContinuation? = some continuation) :
    (cursor.headContextRun continuation selected).context.venv = env := by
  have contextEq : (cursor.headContextRun continuation selected).context =
      cursor.contextRun.context := cursor.headContextRun_context continuation
        selected
  rw [contextEq]
  exact cursor.venv_eq

/-- Reindexing the cursor context onto its head continuation preserves the
semantic universe parameters. -/
theorem CandidateBlockLaterFamilyValidationCursor.headContextRun_lparams
    {env blockEnv : VEnv} {Us : List Name} {nparams : Nat}
    {fullSources remainingSources : List InductiveType}
    {candidates : AddInductive.CandidateList AddInductive.CandidateFamily
      remainingSources}
    {raws : List VInductiveType}
    {dIdx : Nat} {stats : AddInductive.InductiveStats}
    {candidateContext : AddInductive.Context}
    {trace : AddInductive.FamilyParameterComparisonBlockTrace nparams
      fullSources.toArray dIdx stats candidateContext}
    (cursor : CandidateBlockLaterFamilyValidationCursor env blockEnv Us
      nparams fullSources candidates raws trace)
    (continuation :
      AddInductive.FamilyParameterComparisonBlockTrace.FamilyContinuation
        nparams fullSources.toArray)
    (selected : trace.headContinuation? = some continuation) :
    (cursor.headContextRun continuation selected).context.lparams = Us := by
  have contextEq : (cursor.headContextRun continuation selected).context =
      cursor.contextRun.context := cursor.headContextRun_context continuation
        selected
  rw [contextEq]
  exact cursor.lparams_eq

/-- Every remaining semantic family root translates in the cursor's exact
validator context. -/
theorem CandidateBlockFamilyValidationCursor.sourceTranslations
    {env blockEnv : VEnv} {Us : List Name} {nparams : Nat}
    {fullSources : List InductiveType}
    {remainingSources : List InductiveType}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateFamily remainingSources}
    {raws : List VInductiveType}
    {dIdx : Nat} {stats : AddInductive.InductiveStats}
    {candidateContext : AddInductive.Context}
    {trace : AddInductive.FamilyParameterComparisonBlockTrace nparams
      fullSources.toArray dIdx stats candidateContext}
    (cursor : CandidateBlockFamilyValidationCursor env blockEnv Us nparams
      fullSources candidates raws trace) :
    List.Forall₂
      (fun source raw =>
        cursor.contextRun.context.TrExprS source.type raw.type)
      remainingSources raws :=
  cursor.semantics.sourceTranslations cursor.contextRun cursor.venv_eq
    cursor.lparams_eq

/-- The retained outer comparison suffix has exactly one group per semantic
family remaining at the cursor. -/
theorem CandidateBlockFamilyValidationCursor.comparisons_length
    {env blockEnv : VEnv} {Us : List Name} {nparams : Nat}
    {fullSources : List InductiveType}
    {remainingSources : List InductiveType}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateFamily remainingSources}
    {raws : List VInductiveType}
    {dIdx : Nat} {stats : AddInductive.InductiveStats}
    {candidateContext : AddInductive.Context}
    {trace : AddInductive.FamilyParameterComparisonBlockTrace nparams
      fullSources.toArray dIdx stats candidateContext}
    (cursor : CandidateBlockFamilyValidationCursor env blockEnv Us nparams
      fullSources candidates raws trace) :
    trace.comparisons.length = remainingSources.length := by
  calc
    trace.comparisons.length = fullSources.length - dIdx := by
      simpa using trace.comparisons_length
    _ = (fullSources.drop dIdx).length := by simp
    _ = remainingSources.length := congrArg List.length cursor.sourceSuffix_eq

/-- Replace one constructor's parameter prefix by an explicitly shared
telescope while retaining its terminal fields/result and every declaration
header.  This operation is syntactic only: semantic authority for replacing
the prefix must be supplied separately by the validator's retained equality
executions. -/
def canonicalizeConstructorParams (nparams : Nat) (params : List VExpr)
    (constructor : VConstVal) : VConstVal :=
  { constructor with
    type := VExpr.forallN params
      (VExpr.dropN nparams constructor.type) }

/-- Replace one family's and all of its constructors' parameter prefixes by
the same explicit telescope.  Family/constructor identities, universe
arities, and all post-parameter syntax remain unchanged. -/
def canonicalizeFamilyParams (nparams : Nat) (params : List VExpr)
    (family : VInductiveType) : VInductiveType :=
  { family with
    type := VExpr.forallN params (VExpr.dropN nparams family.type)
    ctors := family.ctors.map
      (canonicalizeConstructorParams nparams params) }

/-- Canonicalize every family in source order against one shared parameter
telescope. -/
def canonicalizeFamilyParamsList (nparams : Nat) (params : List VExpr)
    (families : List VInductiveType) : List VInductiveType :=
  families.map (canonicalizeFamilyParams nparams params)

/-- Canonical block view whose shared parameter telescope is selected from
the first family exactly as `blockParams` selects it for analysis. -/
def canonicalizeSharedParams (view : VInductDecl) : VInductDecl :=
  let params := blockParams view.nparams view.types
  { view with
    types := canonicalizeFamilyParamsList view.nparams params view.types }

private theorem canonicalTelN_forallN_length :
    ∀ (params : List VExpr) (result : VExpr),
      VExpr.telN params.length (VExpr.forallN params result) = params
  | [], _ => rfl
  | _ :: params, result => by
      simp only [List.length_cons, VExpr.forallN, VExpr.telN,
        canonicalTelN_forallN_length params result]

private theorem canonicalDropN_forallN_length :
    ∀ (params : List VExpr) (result : VExpr),
      VExpr.dropN params.length (VExpr.forallN params result) = result
  | [], _ => rfl
  | _ :: params, result => by
      simp only [List.length_cons, VExpr.forallN, VExpr.dropN,
        canonicalDropN_forallN_length params result]

/-- A canonical constructor has the requested parameter telescope whenever
that telescope has the declaration's exact parameter length. -/
theorem canonicalizeConstructorParams_telN
    {nparams : Nat} {params : List VExpr} {constructor : VConstVal}
    (paramsLength : params.length = nparams) :
    VExpr.telN nparams
        (canonicalizeConstructorParams nparams params constructor).type =
      params := by
  change VExpr.telN nparams
      (VExpr.forallN params (VExpr.dropN nparams constructor.type)) = params
  rw [← paramsLength]
  exact canonicalTelN_forallN_length params _

/-- Canonicalization retains the exact post-parameter constructor suffix. -/
theorem canonicalizeConstructorParams_dropN
    {nparams : Nat} {params : List VExpr} {constructor : VConstVal}
    (paramsLength : params.length = nparams) :
    VExpr.dropN nparams
        (canonicalizeConstructorParams nparams params constructor).type =
      VExpr.dropN nparams constructor.type := by
  change VExpr.dropN nparams
      (VExpr.forallN params (VExpr.dropN nparams constructor.type)) = _
  rw [← paramsLength]
  exact canonicalDropN_forallN_length params _

/-- A canonical family has the requested shared parameter telescope. -/
theorem canonicalizeFamilyParams_telN
    {nparams : Nat} {params : List VExpr} {family : VInductiveType}
    (paramsLength : params.length = nparams) :
    VExpr.telN nparams
        (canonicalizeFamilyParams nparams params family).type = params := by
  change VExpr.telN nparams
      (VExpr.forallN params (VExpr.dropN nparams family.type)) = params
  rw [← paramsLength]
  exact canonicalTelN_forallN_length params _

/-- Canonicalization retains the exact post-parameter family suffix. -/
theorem canonicalizeFamilyParams_dropN
    {nparams : Nat} {params : List VExpr} {family : VInductiveType}
    (paramsLength : params.length = nparams) :
    VExpr.dropN nparams
        (canonicalizeFamilyParams nparams params family).type =
      VExpr.dropN nparams family.type := by
  change VExpr.dropN nparams
      (VExpr.forallN params (VExpr.dropN nparams family.type)) = _
  rw [← paramsLength]
  exact canonicalDropN_forallN_length params _

/-- Replacing constructor expression payloads by canonical parameter prefixes
does not change header comparison against any source list. -/
theorem sameCtorHeaders_canonicalizeParams_right
    (nparams : Nat) (params : List VExpr) :
    ∀ (raws views : List VConstVal),
      sameCtorHeaders raws
          (views.map (canonicalizeConstructorParams nparams params)) =
        sameCtorHeaders raws views
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | raw :: raws, view :: views => by
      simp only [List.map_cons, sameCtorHeaders,
        canonicalizeConstructorParams]
      rw [sameCtorHeaders_canonicalizeParams_right nparams params raws views]

/-- Replacing every family/constructor parameter prefix preserves the exact
block header comparison against any source list. -/
theorem sameTypeHeaders_canonicalizeParams_right
    (nparams : Nat) (params : List VExpr) :
    ∀ (raws views : List VInductiveType),
      sameTypeHeaders raws
          (canonicalizeFamilyParamsList nparams params views) =
        sameTypeHeaders raws views
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | raw :: raws, view :: views => by
      simp only [canonicalizeFamilyParamsList, List.map_cons,
        sameTypeHeaders, canonicalizeFamilyParams]
      rw [sameCtorHeaders_canonicalizeParams_right]
      have tail :=
        sameTypeHeaders_canonicalizeParams_right nparams params raws views
      simp only [canonicalizeFamilyParamsList] at tail
      rw [tail]

/-- The canonical family list gives every family and every constructor the
same exact syntactic parameter telescope. -/
theorem canonicalizeFamilyParamsList_parameterSurfaces
    {nparams : Nat} {params : List VExpr}
    {families : List VInductiveType} {family : VInductiveType}
    (paramsLength : params.length = nparams)
    (familyMember : family ∈
      canonicalizeFamilyParamsList nparams params families) :
    VExpr.telN nparams family.type = params ∧
      ∀ constructor ∈ family.ctors,
        VExpr.telN nparams constructor.type = params := by
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp familyMember
  refine ⟨canonicalizeFamilyParams_telN paramsLength, ?_⟩
  intro constructor constructorMember
  simp only [canonicalizeFamilyParams] at constructorMember
  obtain ⟨originalConstructor, originalConstructorMember, rfl⟩ :=
    List.mem_map.mp constructorMember
  exact canonicalizeConstructorParams_telN paramsLength

/-- The block-wide canonical view has exact shared family and constructor
parameter surfaces, conditional only on the producer-owned prefix length. -/
theorem canonicalizeSharedParams_parameterSurfaces
    {view : VInductDecl} {family : VInductiveType}
    (paramsLength :
      (blockParams view.nparams view.types).length = view.nparams)
    (familyMember : family ∈ (canonicalizeSharedParams view).types) :
    VExpr.telN view.nparams family.type =
        blockParams view.nparams view.types ∧
      ∀ constructor ∈ family.ctors,
        VExpr.telN view.nparams constructor.type =
          blockParams view.nparams view.types := by
  exact canonicalizeFamilyParamsList_parameterSurfaces paramsLength
    familyMember

/-- For a nonempty block, canonicalization retains the first family's
selected parameter list exactly. -/
theorem canonicalizeSharedParams_blockParams
    {view : VInductDecl}
    (nonempty : view.types.isEmpty = false)
    (paramsLength :
      (blockParams view.nparams view.types).length = view.nparams) :
    blockParams view.nparams (canonicalizeSharedParams view).types =
      blockParams view.nparams view.types := by
  cases view with
  | mk uvars nparams types =>
      cases types with
      | nil => simp at nonempty
      | cons family families =>
          simpa only [canonicalizeSharedParams,
            canonicalizeFamilyParamsList, List.map_cons, blockParams] using
            (canonicalizeFamilyParams_telN paramsLength)

/-- Canonicalizing parameter prefixes changes no family or constructor
header, even when the left side is a distinct raw declaration. -/
theorem canonicalizeSharedParams_sameTypeHeaders (raws : List VInductiveType)
    (view : VInductDecl) :
    sameTypeHeaders raws (canonicalizeSharedParams view).types =
      sameTypeHeaders raws view.types := by
  exact sameTypeHeaders_canonicalizeParams_right view.nparams
    (blockParams view.nparams view.types) raws view.types

/-- Retarget an existing normalization to the syntactically shared-parameter
view.  This constructor establishes header coherence only; semantic
`Normalization.BlockWF` for the retargeted expression payloads remains a
separate obligation. -/
def Normalization.canonicalizeSharedParams
    {source : VInductDecl} (normalization : Normalization source) :
    Normalization source where
  view := VInductDecl.canonicalizeSharedParams normalization.view
  shape_eq := by
    change (source.uvars == normalization.view.uvars &&
      source.nparams == normalization.view.nparams &&
      sameTypeHeaders source.types
        (canonicalizeFamilyParamsList normalization.view.nparams
          (blockParams normalization.view.nparams normalization.view.types)
          normalization.view.types)) = true
    rw [sameTypeHeaders_canonicalizeParams_right]
    exact normalization.shape_eq

/-- The raw semantic family inventory is empty exactly when its source-indexed
kernel family inventory is empty. -/
theorem CandidateBlockFamilySemanticListRun.raws_isEmpty_eq_sources
    {kernelSources : List InductiveType}
    {candidates : AddInductive.CandidateList AddInductive.CandidateFamily
      kernelSources}
    {raws : List VInductiveType}
    (run : CandidateBlockFamilySemanticListRun env blockEnv Us candidates
      raws) :
    raws.isEmpty = kernelSources.isEmpty := by
  cases run <;> rfl

/--
info: 'Lean4Lean.VInductDecl.CandidateBlockFamilySemanticListRun.raws_isEmpty_eq_sources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CandidateBlockFamilySemanticListRun.raws_isEmpty_eq_sources

/-- Replacing family expression payloads preserves emptiness as well as the
complete source order. -/
theorem CandidateBlockFamilySemanticListRun.views_isEmpty_eq_sources
    {kernelSources : List InductiveType}
    {candidates : AddInductive.CandidateList AddInductive.CandidateFamily
      kernelSources}
    {raws : List VInductiveType}
    (run : CandidateBlockFamilySemanticListRun env blockEnv Us candidates
      raws) :
    run.views.isEmpty = kernelSources.isEmpty := by
  cases run <;> rfl

/-- A complete stored family spine and the validator-selected head-prefix
bound determine the exact shared-parameter length in the semantic view. -/
theorem CandidateBlockFamilySemanticListRun.blockParams_length
    {source : InductiveType} {sources : List InductiveType}
    {nparams : Nat}
    {candidates : AddInductive.CandidateList AddInductive.CandidateFamily
      (source :: sources)}
    {raws : List VInductiveType}
    (run : CandidateBlockFamilySemanticListRun env blockEnv Us candidates
      raws)
    (bound : nparams ≤
      candidates.head.familyType.type.trace.spineLength)
    (spines : AddInductive.CandidateFamilyGenerationSpineList candidates) :
    (blockParams nparams run.views).length = nparams := by
  cases run with
  | cons head tail =>
      cases spines with
      | cons familySpine constructorSpines tailSpines =>
          obtain ⟨inferred, recursive⟩ := head.type.recursive
          have length := recursive.viewTelN_length_of_le
            (AddInductive.CandidateExprTrace.generationSpine_storedSpine
              _ familySpine)
            bound
          simpa only [CandidateBlockFamilySemanticListRun.views,
            CandidateBlockFamilySemanticRun.view, blockParams] using length

/-- A complete block semantic hierarchy preserves both family names and the
family-major constructor-name inventory of its kernel sources. -/
theorem CandidateBlockFamilySemanticListRun.rawHeaderNames
    {kernelSources : List InductiveType}
    {candidates : AddInductive.CandidateList AddInductive.CandidateFamily
      kernelSources}
    {raws : List VInductiveType}
    (run : CandidateBlockFamilySemanticListRun env blockEnv Us
      candidates raws) :
    raws.map (·.name) = kernelSources.map (·.name) ∧
      raws.flatMap (fun raw => raw.ctors.map (·.name)) =
        kernelSources.flatMap (fun source => source.ctors.map (·.name)) := by
  induction run with
  | nil => exact ⟨rfl, rfl⟩
  | cons head tail ih =>
      exact ⟨by simp only [List.map_cons, ← head.name_eq, ih.1], by
        simp only [List.flatMap_cons, head.constructors.rawNames, ih.2]⟩

/-- The normalized semantic views preserve the source family's and every
source constructor's exact name order. -/
theorem CandidateBlockFamilySemanticListRun.viewHeaderNames
    {kernelSources : List InductiveType}
    {candidates : AddInductive.CandidateList AddInductive.CandidateFamily
      kernelSources}
    {raws : List VInductiveType}
    (run : CandidateBlockFamilySemanticListRun env blockEnv Us
      candidates raws) :
    run.views.map (·.name) = kernelSources.map (·.name) ∧
      run.views.flatMap (fun view => view.ctors.map (·.name)) =
        kernelSources.flatMap (fun source => source.ctors.map (·.name)) := by
  induction run with
  | nil => exact ⟨rfl, rfl⟩
  | cons head tail ih =>
      exact ⟨by
        simp only [CandidateBlockFamilySemanticListRun.views, List.map_cons,
          CandidateBlockFamilySemanticRun.view, ← head.name_eq, ih.1], by
        simp only [CandidateBlockFamilySemanticListRun.views,
          List.flatMap_cons, CandidateBlockFamilySemanticRun.view,
          head.constructors.viewNames, ih.2]⟩

/-- Block semantic runs preserve every family and constructor header. -/
theorem CandidateBlockFamilySemanticListRun.sameHeaders
    (run : CandidateBlockFamilySemanticListRun env blockEnv Us
      candidates raws) :
    sameTypeHeaders raws run.views = true := by
  induction run with
  | nil => rfl
  | cons head tail ih =>
    simp [CandidateBlockFamilySemanticListRun.views,
      CandidateBlockFamilySemanticRun.view, sameTypeHeaders,
      head.constructors.roots.sameHeaders, ih]

/-- Collect the exact family/constructor definitional equalities selected by
the retained semantic checker hierarchy. -/
theorem CandidateBlockFamilySemanticListRun.evidence
    (run : CandidateBlockFamilySemanticListRun env blockEnv Us
      candidates raws) :
    List.Forall₂
      (fun raw view =>
        (∃ A, TypeChecker.DefEqEvidence env Us.length []
          raw.type view.type A) ∧
        List.Forall₂
          (fun rawCtor viewCtor =>
            ∃ A, TypeChecker.DefEqEvidence blockEnv Us.length []
              rawCtor.type viewCtor.type A)
          raw.ctors view.ctors)
      raws run.views := by
  induction run with
  | nil => exact .nil
  | cons head tail ih =>
    exact .cons
      ⟨head.type.root.evidence, head.constructors.roots.evidence⟩ ih

/-- Complete semantic ownership for an arbitrary normalization candidate.
The raw staging equation and dependent family list share the same exact raw
declaration; no independently supplied normalized declaration is accepted. -/
structure NormalizationCandidateBlockSemanticRun
    (env blockEnv : VEnv) (Us : List Name)
    {sources : List InductiveType}
    (candidate : AddInductive.NormalizationCandidate sources)
    (rawDecl : VInductDecl) where
  uvars_eq : rawDecl.uvars = Us.length
  stage : env.stageInductiveTypes rawDecl.types = some blockEnv
  families : CandidateBlockFamilySemanticListRun env blockEnv Us
    candidate.families rawDecl.types

/-- The raw Theory block carried by a semantic hierarchy has exactly the
family, constructor, and canonical recursor names of its kernel source list. -/
theorem NormalizationCandidateBlockSemanticRun.blockGeneratedNames_eq_sources
    {sources : List InductiveType}
    {candidate : AddInductive.NormalizationCandidate sources}
    {rawDecl : VInductDecl}
    (run : NormalizationCandidateBlockSemanticRun env blockEnv Us
      candidate rawDecl) :
    blockGeneratedNames rawDecl.types =
      sources.map (·.name) ++
        sources.flatMap (fun source => source.ctors.map (·.name)) ++
        sources.map (fun source => (.str source.name "rec" : Name)) := by
  obtain ⟨familyNames, constructorNames⟩ := run.families.rawHeaderNames
  have recursorNames := congrArg
    (List.map (fun name => (.str name "rec" : Name))) familyNames
  have recursorNames' :
      rawDecl.types.map (fun raw => (.str raw.name "rec" : Name)) =
        sources.map (fun source => (.str source.name "rec" : Name)) := by
    simpa only [List.map_map, Function.comp_def] using recursorNames
  simp only [blockGeneratedNames, familyNames, constructorNames,
    recursorNames']

/--
info: 'Lean4Lean.VInductDecl.NormalizationCandidateBlockSemanticRun.blockGeneratedNames_eq_sources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NormalizationCandidateBlockSemanticRun.blockGeneratedNames_eq_sources

/-- Theory declaration selected by the exact block semantic hierarchy. -/
def NormalizationCandidateBlockSemanticRun.viewDecl
    (run : NormalizationCandidateBlockSemanticRun env blockEnv Us
      candidate rawDecl) : VInductDecl :=
  { rawDecl with types := run.families.views }

/-- Construct the header-preserving Theory normalization boundary selected by
the candidate semantic hierarchy. -/
def NormalizationCandidateBlockSemanticRun.normalization
    (run : NormalizationCandidateBlockSemanticRun env blockEnv Us
      candidate rawDecl) : Normalization rawDecl where
  view := run.viewDecl
  shape_eq := by
    simp only [normalizationShape,
      NormalizationCandidateBlockSemanticRun.viewDecl,
      beq_self_eq_true, Bool.true_and]
    exact run.families.sameHeaders

/-- The canonical normalization target selected from this exact semantic
hierarchy.  Its expression payloads are not yet claimed semantically valid:
that later proof must consume the validator's retained family/constructor
parameter comparisons. -/
def NormalizationCandidateBlockSemanticRun.canonicalNormalization
    (run : NormalizationCandidateBlockSemanticRun env blockEnv Us
      candidate rawDecl) : Normalization rawDecl :=
  run.normalization.canonicalizeSharedParams

/-- Once the producer has established the shared-prefix length, every family
and constructor in the canonical semantic view has that exact first-family
parameter telescope by construction. -/
theorem
    NormalizationCandidateBlockSemanticRun.canonicalParameterSurfaces
    (run : NormalizationCandidateBlockSemanticRun env blockEnv Us
      candidate rawDecl)
    (paramsLength :
      (blockParams run.normalization.view.nparams
        run.normalization.view.types).length =
          run.normalization.view.nparams)
    (familyMember : family ∈ run.canonicalNormalization.view.types) :
    VExpr.telN run.normalization.view.nparams family.type =
        blockParams run.normalization.view.nparams
          run.normalization.view.types ∧
      ∀ constructor ∈ family.ctors,
        VExpr.telN run.normalization.view.nparams constructor.type =
          blockParams run.normalization.view.nparams
            run.normalization.view.types := by
  simpa only [NormalizationCandidateBlockSemanticRun.canonicalNormalization,
    Normalization.canonicalizeSharedParams] using
    (canonicalizeSharedParams_parameterSurfaces paramsLength familyMember)

/-- For a nonempty semantic family spine, canonicalization does not change
the block parameter value selected from its head. -/
theorem NormalizationCandidateBlockSemanticRun.canonicalBlockParams
    (run : NormalizationCandidateBlockSemanticRun env blockEnv Us
      candidate rawDecl)
    (nonempty : run.normalization.view.types.isEmpty = false)
    (paramsLength :
      (blockParams run.normalization.view.nparams
        run.normalization.view.types).length =
          run.normalization.view.nparams) :
    blockParams run.canonicalNormalization.view.nparams
        run.canonicalNormalization.view.types =
      blockParams run.normalization.view.nparams
        run.normalization.view.types := by
  simpa only [NormalizationCandidateBlockSemanticRun.canonicalNormalization,
    Normalization.canonicalizeSharedParams,
    VInductDecl.canonicalizeSharedParams] using
    (canonicalizeSharedParams_blockParams nonempty paramsLength)

/-- The exact normalized declaration selected by a semantic hierarchy is
nonempty precisely when the source-indexed kernel block is nonempty. -/
theorem NormalizationCandidateBlockSemanticRun.viewTypes_isEmpty_eq_sources
    {sources : List InductiveType}
    {candidate : AddInductive.NormalizationCandidate sources}
    {rawDecl : VInductDecl}
    (run : NormalizationCandidateBlockSemanticRun env blockEnv Us
      candidate rawDecl) :
    run.normalization.view.types.isEmpty = sources.isEmpty := by
  simpa only [NormalizationCandidateBlockSemanticRun.normalization,
    NormalizationCandidateBlockSemanticRun.viewDecl] using
    run.families.views_isEmpty_eq_sources

/-- For a nonempty ordinary normalization execution, the semantic view's
first-family parameter telescope has exactly the validator-selected length.
Both the lower bound and the complete stored spine come from the retained
producer execution. -/
theorem NormalizationCandidateBlockSemanticRun.viewParams_length_of_execution
    {source : InductiveType} {sources : List InductiveType}
    {nparams numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    (execution : AddInductive.NormalizationCandidateExecution nparams
      (source :: sources) numNested isUnsafe context)
    (produced : AddInductive.buildNormalizationCandidateExecution nparams
      (source :: sources) numNested isUnsafe context = .ok execution)
    {env blockEnv : VEnv} {Us : List Name} {rawDecl : VInductDecl}
    (semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
      execution.candidate rawDecl)
    (context_lctx_eq : context.lctx = {}) :
    (blockParams nparams semantic.normalization.view.types).length =
      nparams := by
  have bound := execution.firstFamilyType_nparams_le_spineLength produced
    context_lctx_eq
  have candidateBound : nparams ≤
      execution.candidate.families.head.familyType.type.trace.spineLength := by
    change nparams ≤
      execution.families.candidates.head.familyType.type.trace.spineLength
    rw [execution.families.produced.head_familyType]
    exact bound
  have length := semantic.families.blockParams_length candidateBound
    execution.generationSpines
  simpa only [NormalizationCandidateBlockSemanticRun.normalization,
    NormalizationCandidateBlockSemanticRun.viewDecl] using length

/-- The exact normalized view has the same source-derived generated-name
inventory as the raw semantic block. -/
theorem
    NormalizationCandidateBlockSemanticRun.viewBlockGeneratedNames_eq_sources
    {sources : List InductiveType}
    {candidate : AddInductive.NormalizationCandidate sources}
    {rawDecl : VInductDecl}
    (run : NormalizationCandidateBlockSemanticRun env blockEnv Us
      candidate rawDecl) :
    blockGeneratedNames run.families.views =
      sources.map (·.name) ++
        sources.flatMap (fun source => source.ctors.map (·.name)) ++
        sources.map (fun source => (.str source.name "rec" : Name)) := by
  obtain ⟨familyNames, constructorNames⟩ := run.families.viewHeaderNames
  have recursorNames := congrArg
    (List.map (fun name => (.str name "rec" : Name))) familyNames
  have recursorNames' :
      run.families.views.map (fun view => (.str view.name "rec" : Name)) =
        sources.map (fun source => (.str source.name "rec" : Name)) := by
    simpa only [List.map_map, Function.comp_def] using recursorNames
  simp only [blockGeneratedNames, familyNames, constructorNames,
    recursorNames']

/-- Project the generic verified normalization run for the same raw block and
shared staged environment. -/
theorem NormalizationCandidateBlockSemanticRun.normalizationRun
    (run : NormalizationCandidateBlockSemanticRun env blockEnv Us
      candidate rawDecl) :
    NormalizationBlockRun run.normalization env blockEnv where
  stage := run.stage
  families := by
    simpa only [run.uvars_eq,
      NormalizationCandidateBlockSemanticRun.normalization,
      NormalizationCandidateBlockSemanticRun.viewDecl] using
      run.families.evidence

/-- Construct the exact analyzer-owned block at a retained semantic
normalization.  The checked dependent spine is the only structural input;
its replay theorem supplies the inner analyzer equation without selecting a
parallel normalization or restating an `Option` result. -/
def NormalizationCandidateBlockSemanticRun.normalizedCheckedBlock
    (run : NormalizationCandidateBlockSemanticRun env blockEnv Us
      candidate rawDecl)
    (checked : run.normalization.view.CheckedBlock) :
    NormalizedCheckedBlock rawDecl where
  normalization := run.normalization
  checked := checked
  checked_eq := checked.checkedBlock?

/-- The semantic block constructed from a checked view has exactly the
normalization selected by the retained recursive checker hierarchy. -/
@[simp] theorem
    NormalizationCandidateBlockSemanticRun.normalizedCheckedBlock_normalization
    (run : NormalizationCandidateBlockSemanticRun env blockEnv Us
      candidate rawDecl)
    (checked : run.normalization.view.CheckedBlock) :
    (run.normalizedCheckedBlock checked).normalization = run.normalization :=
  rfl

/-- Analyzer replay for the semantic block is now constructional: no
normalization-identification premise or semantic choice is required. -/
theorem
    NormalizationCandidateBlockSemanticRun.normalizedCheckedBlock_checkBlock?
    (run : NormalizationCandidateBlockSemanticRun env blockEnv Us
      candidate rawDecl)
    (checked : run.normalization.view.CheckedBlock) :
    run.normalization.checkBlock? =
      some (run.normalizedCheckedBlock checked) :=
  (run.normalizedCheckedBlock checked).checkBlock?

/-- Package a semantic analyzer result for block generation once the
validator-owned common result level and the mixed raw/view layout proof are
available.  In particular, this constructor cannot be pointed at an
independently normalized block. -/
def NormalizationCandidateBlockSemanticRun.blockGenerationChecked
    (run : NormalizationCandidateBlockSemanticRun env blockEnv Us
      candidate rawDecl)
    (checked : run.normalization.view.CheckedBlock)
    (resultLevel : VLevel)
    (shape : (run.normalizedCheckedBlock checked).blockGenerationShape = true) :
    BlockGenerationChecked rawDecl where
  validated := {
    block := run.normalizedCheckedBlock checked
    resultLevel := resultLevel }
  shape_eq := shape

/-- The generation package constructed from a semantic analyzer result
replays through that same semantic normalization exactly. -/
theorem
    NormalizationCandidateBlockSemanticRun.blockGenerationChecked_analysis
    (run : NormalizationCandidateBlockSemanticRun env blockEnv Us
      candidate rawDecl)
    (checked : run.normalization.view.CheckedBlock)
    (resultLevel : VLevel)
    (shape : (run.normalizedCheckedBlock checked).blockGenerationShape = true) :
    run.normalization.checkBlock? =
      some (run.blockGenerationChecked checked resultLevel shape).block :=
  run.normalizedCheckedBlock_checkBlock? checked

/-- A singleton-family semantic hierarchy spanning the pre-family candidate,
the exact raw-family insertion, and every post-family constructor candidate.
The normalized expression payloads are selected by retained recursive checker
runs, not by a parallel caller-supplied declaration. -/
structure CandidateFamilySemanticRun (env : VEnv) (Us : List Name)
    {source : InductiveType}
    (candidate : AddInductive.CandidateFamily source)
    (raw : VInductiveType) where
  name_eq : source.name = raw.name
  uvars_eq : raw.uvars = Us.length
  type : TypeChecker.CandidateExprSemanticRootRun env Us
    candidate.familyType.type raw.type
  typeEnv : VEnv
  addType : env.addConst raw.name raw.toVConstant = some typeEnv
  constructors : CandidateConstructorSemanticListRun typeEnv Us
    candidate.constructors raw.ctors

/-- Project the existing normalization-facing family run from the retained
semantic hierarchy. -/
def CandidateFamilySemanticRun.root
    (run : CandidateFamilySemanticRun env Us candidate raw) :
    CandidateFamilyRun env Us candidate raw where
  name_eq := run.name_eq
  uvars_eq := run.uvars_eq
  viewType := run.type.view
  typeRun := run.type.root
  typeEnv := run.typeEnv
  addType := run.addType
  constructors := run.constructors.roots

/-- Complete retained semantic ownership for one source-indexed singleton
normalization candidate. This is the generic bridge from translated family and
constructor candidates to `NormalizationCandidateRun`; mutual blocks remain a
later indexed generalization. -/
structure NormalizationCandidateSemanticRun (env : VEnv) (Us : List Name)
    {source : InductiveType}
    (candidate : AddInductive.NormalizationCandidate [source])
    (rawDecl : VInductDecl) where
  raw : VInductiveType
  raw_types_eq : rawDecl.types = [raw]
  uvars_eq : rawDecl.uvars = Us.length
  family : CandidateFamilySemanticRun env Us candidate.families.singleton raw

/-- Recover the existing normalization candidate from the retained semantic
hierarchy. -/
def NormalizationCandidateSemanticRun.root
    (run : NormalizationCandidateSemanticRun env Us candidate rawDecl) :
    NormalizationCandidateRun env Us candidate rawDecl where
  raw := run.raw
  raw_types_eq := run.raw_types_eq
  uvars_eq := run.uvars_eq
  family := run.family.root

/-- Pre-run semantic evidence for one source-indexed constructor.  Its header
is aligned with the raw Theory constant, while the expression input contains
only the verified context and strict source translation needed to let the
retained checker choose the view. -/
structure CandidateConstructorSemanticInput (env : VEnv) (Us : List Name)
    {source : Constructor}
    (candidate : AddInductive.CandidateConstructor source)
    (raw : VConstVal) where
  name_eq : source.name = raw.name
  uvars_eq : raw.uvars = Us.length
  type : TypeChecker.CandidateExprSemanticRootInput env Us candidate.type
    raw.type

/-- Interpret one constructor input without selecting its view at the call
site. -/
theorem CandidateConstructorSemanticInput.exists
    (input : CandidateConstructorSemanticInput env Us candidate raw) :
    Nonempty (CandidateConstructorSemanticRun env Us candidate raw) := by
  obtain ⟨type⟩ := input.type.exists
  exact ⟨{
    name_eq := input.name_eq
    uvars_eq := input.uvars_eq
    type := type }⟩

/-- Exact source-order semantic inputs for an arbitrary constructor list.
Unlike a pointwise predicate over erased lists, these indices prevent an input
from being reused at another constructor or from silently truncating either
side. -/
inductive CandidateConstructorSemanticListInput
    (env : VEnv) (Us : List Name) :
    {sources : List Constructor} →
      AddInductive.CandidateList AddInductive.CandidateConstructor sources →
      List VConstVal → Type where
  | nil : CandidateConstructorSemanticListInput env Us .nil []
  | cons
      (head : CandidateConstructorSemanticInput env Us candidate raw)
      (tail : CandidateConstructorSemanticListInput env Us candidates raws) :
      CandidateConstructorSemanticListInput env Us
        (.cons candidate candidates) (raw :: raws)

/-- Recursively interpret every source-indexed constructor input. -/
theorem CandidateConstructorSemanticListInput.exists
    (input : CandidateConstructorSemanticListInput env Us candidates raws) :
    Nonempty (CandidateConstructorSemanticListRun env Us candidates raws) := by
  induction input with
  | nil => exact ⟨.nil⟩
  | cons head tail ih =>
    obtain ⟨headRun⟩ := head.exists
    obtain ⟨tailRun⟩ := ih
    exact ⟨.cons headRun tailRun⟩

/-- Pre-run semantic evidence for one family in a shared mutual stage.
Family types use `env`; all constructor types use the same `blockEnv` after
every raw family has been staged. -/
structure CandidateBlockFamilySemanticInput
    (env blockEnv : VEnv) (Us : List Name)
    {source : InductiveType}
    (candidate : AddInductive.CandidateFamily source)
    (raw : VInductiveType) where
  name_eq : source.name = raw.name
  uvars_eq : raw.uvars = Us.length
  type : TypeChecker.CandidateExprSemanticRootInput env Us
    candidate.familyType.type raw.type
  constructors : CandidateConstructorSemanticListInput blockEnv Us
    candidate.constructors raw.ctors

/-- Interpret one family and its complete constructor list without selecting
a normalized expression at the call site. -/
theorem CandidateBlockFamilySemanticInput.exists
    (input : CandidateBlockFamilySemanticInput env blockEnv Us
      candidate raw) :
    Nonempty (CandidateBlockFamilySemanticRun env blockEnv Us
      candidate raw) := by
  obtain ⟨type⟩ := input.type.exists
  obtain ⟨constructors⟩ := input.constructors.exists
  exact ⟨{
    name_eq := input.name_eq
    uvars_eq := input.uvars_eq
    type
    constructors }⟩

/-- Exact source-order semantic inputs for every family in a mutual block. -/
inductive CandidateBlockFamilySemanticListInput
    (env blockEnv : VEnv) (Us : List Name) :
    {sources : List InductiveType} →
      AddInductive.CandidateList AddInductive.CandidateFamily sources →
      List VInductiveType → Type where
  | nil : CandidateBlockFamilySemanticListInput env blockEnv Us .nil []
  | cons
      (head : CandidateBlockFamilySemanticInput env blockEnv Us candidate raw)
      (tail : CandidateBlockFamilySemanticListInput env blockEnv Us
        candidates raws) :
      CandidateBlockFamilySemanticListInput env blockEnv Us
        (.cons candidate candidates) (raw :: raws)

/-- Source-indexed terminal sorts retained for every family candidate in an
arbitrary block.  This is the semantic fragment of family validation needed
to type each raw family before the shared staging fold. -/
inductive CandidateBlockFamilyTerminalSortList :
    {sources : List InductiveType} →
      AddInductive.CandidateList AddInductive.CandidateFamily sources → Prop where
  | nil : CandidateBlockFamilyTerminalSortList .nil
  | cons
      (terminal : candidate.familyType.type.trace.terminalResult =
        .sort resultLevel)
      (tail : CandidateBlockFamilyTerminalSortList candidates) :
      CandidateBlockFamilyTerminalSortList (.cons candidate candidates)

/-- Lift the terminal witnesses retained before raw family insertion onto the
same family-type payload inside the assembled candidate list. -/
theorem CandidateBlockFamilyTerminalSortList.of_familyTypes :
    (candidates : AddInductive.CandidateList
      AddInductive.CandidateFamily sources) →
    AddInductive.CandidateFamilyTypeTerminalSortList candidates.familyTypes →
      CandidateBlockFamilyTerminalSortList candidates
  | .nil, terminals => by
      cases terminals
      exact .nil
  | .cons candidate candidates, terminals => by
      have terminals' : AddInductive.CandidateFamilyTypeTerminalSortList
          (.cons candidate.familyType candidates.familyTypes) := by
        simpa only [AddInductive.CandidateList.familyTypes] using terminals
      cases terminals' with
      | cons terminal tail =>
          exact .cons terminal
            (CandidateBlockFamilyTerminalSortList.of_familyTypes candidates tail)

/-- The first semantic family root translates the exact terminal level
retained at the same source-indexed candidate position.  Abstracting the
dependent candidate list here lets downstream block producers consume the
head fact without an unchecked `head!` or a parallel list equation. -/
theorem CandidateBlockFamilySemanticListRun.headResultLevel
    {env blockEnv : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {kernelSources : List InductiveType}
    {candidates : AddInductive.CandidateList AddInductive.CandidateFamily
      (kernelSource :: kernelSources)}
    {raws : List VInductiveType}
    (run : CandidateBlockFamilySemanticListRun env blockEnv Us candidates
      raws)
    (terminals : CandidateBlockFamilyTerminalSortList candidates) :
    ∃ kernelLevel viewLevel,
      candidates.head.familyType.type.trace.terminalResult =
          .sort kernelLevel ∧
        VLevel.ofLevel Us kernelLevel = some viewLevel := by
  cases run with
  | cons head tail =>
      cases terminals with
      | cons terminal terminalTail =>
          obtain ⟨viewLevel, level_tr, _viewResult⟩ :=
            head.type.viewResult_of_terminalSort terminal
          exact ⟨_, viewLevel, terminal, level_tr⟩

/-- Executable shape check for the terminal-sort evidence of a complete
source-indexed family list.  The result universe remains owned by each exact
candidate trace; the check only recognizes its terminal constructor. -/
def CandidateBlockFamilyTerminalSortList.check :
    {sources : List InductiveType} →
      (candidates : AddInductive.CandidateList
        AddInductive.CandidateFamily sources) → Bool
  | [], .nil => true
  | _ :: _, .cons candidate candidates =>
      match candidate.familyType.type.trace.terminalResult with
      | .sort _ => CandidateBlockFamilyTerminalSortList.check candidates
      | _ => false

/-- A successful terminal-shape check reconstructs the exact dependent proof
without unfolding or replacing the producer's candidate list. -/
theorem CandidateBlockFamilyTerminalSortList.of_check :
    (candidates : AddInductive.CandidateList
      AddInductive.CandidateFamily sources) →
      CandidateBlockFamilyTerminalSortList.check candidates = true →
        CandidateBlockFamilyTerminalSortList candidates
  | .nil, _ => .nil
  | .cons candidate candidates, checked => by
      cases terminal_eq : candidate.familyType.type.trace.terminalResult <;>
        simp [CandidateBlockFamilyTerminalSortList.check, terminal_eq]
          at checked
      case sort resultLevel =>
        exact .cons terminal_eq
          (CandidateBlockFamilyTerminalSortList.of_check candidates checked)

/-- A family semantic root whose retained validator endpoint is a sort proves
the exact raw Theory family constant well formed in the pre-family
environment. -/
theorem CandidateBlockFamilySemanticInput.rawWF
    (input : CandidateBlockFamilySemanticInput env blockEnv Us candidate raw)
    (terminal : candidate.familyType.type.trace.terminalResult =
      .sort resultLevel) :
    raw.toVConstant.WF env := by
  obtain ⟨semantic⟩ := input.type.exists
  change env.IsType raw.uvars [] raw.type
  simpa only [input.uvars_eq] using
    semantic.source_isType_of_terminalSort terminal

/-- Join source-indexed semantic roots, validator terminal sorts, and the
producer's exact metadata alignment into the evidence consumed by
`declarationTraceTrEnv`.  The three dependent lists cannot truncate, reorder,
or exchange family owners. -/
theorem CandidateBlockFamilySemanticListInput.declarationEvidence
    {stats : AddInductive.InductiveStats} {numParams : Nat}
    {indTypes : Array InductiveType} {numNested : Nat}
    {isUnsafe : Bool} {context : AddInductive.Context}
    {env blockEnv : VEnv} {Us : List Name}
    {sources : List InductiveType}
    {candidates : AddInductive.CandidateList AddInductive.CandidateFamily
      sources}
    {raws : List VInductiveType} {infos : List InductiveVal}
    (input : CandidateBlockFamilySemanticListInput env blockEnv Us
      candidates raws)
    (metadata : List.Forall₂
      (fun indType info => ∃ numIndices,
        info = AddInductive.declaredInductiveInfo stats numParams indTypes
          indType numIndices numNested isUnsafe context)
      sources infos)
    (terminals : CandidateBlockFamilyTerminalSortList candidates)
    (safe : isUnsafe = false)
    (lparams_eq : context.lparams = Us) :
    List.Forall₂
      (fun info raw =>
        TrConstVal .safe env (.inductInfo info) raw.toVConstVal ∧
          raw.toVConstant.WF env)
      infos raws := by
  induction input generalizing infos with
  | nil =>
      cases metadata
      exact .nil
  | cons head tail ih =>
      cases metadata with
      | cons metadataHead metadataTail =>
          cases terminals with
          | cons terminal terminalTail =>
              apply List.Forall₂.cons
              · constructor
                · exact declaredInductiveInfo_tr metadataHead safe
                    lparams_eq head.name_eq head.uvars_eq head.type.source_tr
                · exact head.rawWF terminal
              · exact ih metadataTail terminalTail

/-- Pre-family staged evidence for one source-indexed family type.  Unlike the
complete block semantic input, this fragment is independent of the derived
post-family constructor stage and can therefore be used to construct it. -/
structure CandidateBlockFamilyTypeStagedInput
    {familyContext : AddInductive.Context} {env : VEnv} {Us : List Name}
    (preFamily : TypeChecker.CandidateSemanticStage familyContext env Us)
    {source : InductiveType}
    (candidate : AddInductive.CandidateFamily source)
    (raw : VInductiveType) where
  name_eq : source.name = raw.name
  uvars_eq : raw.uvars = Us.length
  type : TypeChecker.CandidateExprStagedInput preFamily
    candidate.familyType.type raw.type

/-- Executable recursive-identity check for one staged family-type root. -/
def CandidateBlockFamilyTypeStagedInput.identityCheck
    {familyContext : AddInductive.Context} {env : VEnv} {Us : List Name}
    {preFamily : TypeChecker.CandidateSemanticStage familyContext env Us}
    {source : InductiveType}
    {candidate : AddInductive.CandidateFamily source}
    {raw : VInductiveType}
    (_input : CandidateBlockFamilyTypeStagedInput preFamily candidate raw) :
    Bool :=
  TypeChecker.CandidateExprIdentity.check candidate.familyType.type.trace

/-- The retained family endpoint proves the raw constant well formed before
any family in the block is staged. -/
theorem CandidateBlockFamilyTypeStagedInput.rawWF
    {familyContext : AddInductive.Context} {env : VEnv} {Us : List Name}
    {source : InductiveType}
    {candidate : AddInductive.CandidateFamily source}
    {raw : VInductiveType}
    {preFamily : TypeChecker.CandidateSemanticStage familyContext env Us}
    (input : CandidateBlockFamilyTypeStagedInput preFamily candidate raw)
    (terminal : candidate.familyType.type.trace.terminalResult =
      .sort resultLevel) :
    raw.toVConstant.WF env := by
  obtain ⟨semantic⟩ := input.type.rootInput.exists
  change env.IsType raw.uvars [] raw.type
  simpa only [input.uvars_eq] using
    semantic.source_isType_of_terminalSort terminal

/-- Exact pre-family roots for every source family, kept separate from the
constructor half so the common post-family stage can be derived first. -/
inductive CandidateBlockFamilyTypeStagedListInput
    {familyContext : AddInductive.Context} {env : VEnv} {Us : List Name}
    (preFamily : TypeChecker.CandidateSemanticStage familyContext env Us) :
    {sources : List InductiveType} →
      AddInductive.CandidateList AddInductive.CandidateFamily sources →
      List VInductiveType → Type where
  | nil : CandidateBlockFamilyTypeStagedListInput preFamily .nil []
  | cons
      (head : CandidateBlockFamilyTypeStagedInput preFamily candidate raw)
      (tail : CandidateBlockFamilyTypeStagedListInput preFamily
        candidates raws) :
      CandidateBlockFamilyTypeStagedListInput preFamily
        (.cons candidate candidates) (raw :: raws)

/-- Candidate-independent source translation for one raw family type.  It can
be prepared before inspecting the opaque proof-carrying candidate list. -/
structure CandidateBlockFamilyTypeSourceInput (env : VEnv) (Us : List Name)
    (source : InductiveType) (raw : VInductiveType) where
  name_eq : source.name = raw.name
  uvars_eq : raw.uvars = Us.length
  source_tr : TrExprS env Us [] source.type raw.type

/-- Exact source/raw family translations, independent of the executable
candidate payload but still indexed by the complete source order. -/
inductive CandidateBlockFamilyTypeSourceListInput
    (env : VEnv) (Us : List Name) :
    List InductiveType → List VInductiveType → Type where
  | nil : CandidateBlockFamilyTypeSourceListInput env Us [] []
  | cons
      (head : CandidateBlockFamilyTypeSourceInput env Us source raw)
      (tail : CandidateBlockFamilyTypeSourceListInput env Us sources raws) :
      CandidateBlockFamilyTypeSourceListInput env Us
        (source :: sources) (raw :: raws)

/-- Transfer a name-only property from an aligned implementation family
inventory to the corresponding raw Theory families. -/
theorem CandidateBlockFamilyTypeSourceListInput.forall_names_of_declared
    {env : VEnv} {Us : List Name}
    {sources : List InductiveType} {raws : List VInductiveType}
    {P : Name → Prop}
    (input : CandidateBlockFamilyTypeSourceListInput env Us sources raws)
    {infos : List InductiveVal}
    (declared : List.Forall₂
      (fun source info => info.name = source.name) sources infos)
    (property : ∀ info ∈ infos, P info.name) :
    ∀ raw ∈ raws, P raw.name := by
  induction input generalizing infos with
  | nil =>
      cases declared
      intro raw member
      nomatch member
  | cons head tail ih =>
      cases declared with
      | cons declaredHead declaredTail =>
          intro raw' member
          rcases List.mem_cons.mp member with rfl | member
          · have name_eq := declaredHead.trans head.name_eq
            simpa only [name_eq] using property _ (.head _)
          · exact ih declaredTail
              (fun other otherMember =>
                property other (.tail _ otherMember)) raw' member

/-- Recover candidate-independent raw family types from the exact successful
ordinary family traversal.  Closed source types can be translated in the
retained root candidate context, whose semantic stage discharges the empty
local-context transport. -/
theorem CandidateBlockFamilyTypeSourceListInput.exists_ofProduced
    {familyContext : AddInductive.Context} {env : VEnv} {Us : List Name}
    {sources : List InductiveType}
    (stage : TypeChecker.CandidateSemanticStage familyContext env Us)
    (families : AddInductive.CandidateList
      AddInductive.CandidateFamily sources)
    (produced : AddInductive.CandidateFamilyTypeListProduced familyContext
      families.familyTypes)
    (closed : ∀ source ∈ sources,
      source.type.FVarsIn (fun _ => False)) :
    Nonempty (Σ raws,
      CandidateBlockFamilyTypeSourceListInput env Us sources raws) := by
  induction families with
  | nil => exact ⟨⟨[], .nil⟩⟩
  | @cons source sources family families ih =>
      have contextEq : family.familyType.type.context = familyContext :=
        AddInductive.CandidateFamilyType.context_eq_of_normalize produced.head
      cases contextEq
      let candidateRun : TypeChecker.CandidateContextRun
          family.familyType.type.context := stage.contextRun
      have sourceFVars : source.type.FVarsIn
          (· ∈ candidateRun.context.vlctx.fvars) :=
        (closed source (.head _)).mono fun _ impossible => impossible.elim
      obtain ⟨sourceType, contextualTr⟩ :=
        TypeChecker.candidateExprTrace_exists_source_translation
          family.familyType.type.trace candidateRun sourceFVars
      have candidateVenv : candidateRun.context.venv = env := by
        simpa only [candidateRun] using stage.venv_eq
      have candidateLparams : candidateRun.context.lparams = Us := by
        simpa only [candidateRun] using stage.lparams_eq
      have candidateVlctx : candidateRun.context.vlctx = [] := by
        simpa only [candidateRun] using stage.vlctx_eq
      have sourceTr : TrExprS env Us [] source.type sourceType := by
        change TrExprS candidateRun.context.venv
          candidateRun.context.lparams candidateRun.context.vlctx
          source.type sourceType at contextualTr
        simpa only [candidateVenv, candidateLparams, candidateVlctx] using
          contextualTr
      obtain ⟨⟨raws, tailInput⟩⟩ := ih produced.tail (fun tail member =>
        closed tail (.tail _ member))
      let raw : VInductiveType := {
        uvars := Us.length
        type := sourceType
        name := source.name
        ctors := [] }
      exact ⟨⟨raw :: raws, .cons {
        name_eq := rfl
        uvars_eq := rfl
        source_tr := sourceTr } tailInput⟩⟩

/-- Reindex source translations at the exact family candidate list retained
by the ordinary producer.  Recursion is over that data list; the
proposition-valued producer trace supplies only the root-context equations. -/
def CandidateBlockFamilyTypeSourceListInput.staged
    {familyContext : AddInductive.Context}
    {preFamily : TypeChecker.CandidateSemanticStage familyContext env Us}
    {sources : List InductiveType} {raws : List VInductiveType} :
    (input : CandidateBlockFamilyTypeSourceListInput env Us sources raws) →
    (families : AddInductive.CandidateList
      AddInductive.CandidateFamily sources) →
    AddInductive.CandidateFamilyTypeListProduced familyContext
      families.familyTypes →
    (whnfFuel : Nat) →
    familyContext.fuel.recDepth = whnfFuel + 1 →
    CandidateBlockFamilyTypeStagedListInput preFamily families raws
  | .nil, .nil, _, _, _ => .nil
  | .cons head tail, .cons family families, produced, whnfFuel, whnfDepth =>
      .cons {
          name_eq := head.name_eq
          uvars_eq := head.uvars_eq
          type := {
            context_eq :=
              (AddInductive.CandidateFamilyType.context_eq_of_normalize
                produced.head).symm
            source_tr := head.source_tr
            whnfFuel
            whnfDepth := by
              rw [AddInductive.CandidateFamilyType.context_eq_of_normalize
                produced.head]
              exact whnfDepth } }
        (tail.staged families produced.tail whnfFuel whnfDepth)

/-- Assemble the exact metadata translations and raw-family typing evidence
needed by the declaration trace, before any constructor semantic input is
mentioned. -/
theorem CandidateBlockFamilyTypeStagedListInput.declarationEvidence
    {stats : AddInductive.InductiveStats} {numParams : Nat}
    {indTypes : Array InductiveType} {numNested : Nat}
    {isUnsafe : Bool} {context : AddInductive.Context}
    {familyContext : AddInductive.Context}
    {env : VEnv} {Us : List Name}
    {sources : List InductiveType}
    {candidates : AddInductive.CandidateList AddInductive.CandidateFamily
      sources}
    {raws : List VInductiveType} {infos : List InductiveVal}
    {preFamily : TypeChecker.CandidateSemanticStage familyContext env Us}
    (input : CandidateBlockFamilyTypeStagedListInput preFamily
      candidates raws)
    (metadata : List.Forall₂
      (fun indType info => ∃ numIndices,
        info = AddInductive.declaredInductiveInfo stats numParams indTypes
          indType numIndices numNested isUnsafe context)
      sources infos)
    (terminals : CandidateBlockFamilyTerminalSortList candidates)
    (safe : isUnsafe = false)
    (lparams_eq : context.lparams = Us) :
    List.Forall₂
      (fun info raw =>
        TrConstVal .safe env (.inductInfo info) raw.toVConstVal ∧
          raw.toVConstant.WF env)
      infos raws := by
  induction input generalizing infos with
  | nil =>
      cases metadata
      exact .nil
  | cons head tail ih =>
      cases metadata with
      | cons metadataHead metadataTail =>
          cases terminals with
          | cons terminal terminalTail =>
              exact .cons
                ⟨declaredInductiveInfo_tr metadataHead safe lparams_eq
                    head.name_eq head.uvars_eq head.type.source_tr,
                  head.rawWF terminal⟩
                (ih metadataTail terminalTail)

/-- Complete owner of the derived shared post-family verifier stage for an
arbitrary block.  The kernel map comes from the retained declaration trace;
the Theory environment comes from the exact raw-family staging fold. -/
structure NormalizationCandidateBlockStagingInput
    {nparams : Nat} {sources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    (context : AddInductive.Context)
    (execution : AddInductive.NormalizationCandidateExecution nparams
      sources numNested isUnsafe context)
    (env blockEnv : VEnv) (Us : List Name) (rawDecl : VInductDecl) where
  uvars_eq : rawDecl.uvars = Us.length
  preFamily : TypeChecker.CandidateSemanticStage
    { context with lctx := {} } env Us
  familyTypes : CandidateBlockFamilyTypeStagedListInput preFamily
    execution.candidate.families rawDecl.types
  terminals : CandidateBlockFamilyTerminalSortList
    execution.candidate.families
  stage : env.stageInductiveTypes rawDecl.types = some blockEnv
  nindices_size : execution.stats.nindices.size = sources.length
  validation_env_eq : execution.validationContext.env = context.env
  validation_lparams_eq : execution.validationContext.lparams = Us
  context_safety_eq : context.safety = .safe
  isUnsafe_eq : isUnsafe = false
  preMapWF : context.env.constants.WF
  names_not_primitive : ∀ raw ∈ rawDecl.types,
    raw.name ∉ VEnv.reflectedPrimitiveNames ∧
      Environment.primitives.contains raw.name = false
  projectionReady : ProjectionReady execution.familyEnv blockEnv
  structureEtaReady : StructureEtaReady execution.familyEnv blockEnv

/-- Exact implementation metadata correspondence used by the retained
family-declaration fold. -/
theorem NormalizationCandidateBlockStagingInput.declarationMetadata
    {nparams : Nat} {sources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {execution : AddInductive.NormalizationCandidateExecution nparams
      sources numNested isUnsafe context}
    {env blockEnv : VEnv} {Us : List Name} {rawDecl : VInductDecl}
    (input : NormalizationCandidateBlockStagingInput context execution
      env blockEnv Us rawDecl) :
    List.Forall₂
      (fun indType info => ∃ numIndices,
        info = AddInductive.declaredInductiveInfo execution.stats nparams
          sources.toArray indType numIndices numNested isUnsafe
            execution.validationContext)
      sources execution.declaredInfos := by
  simpa only [AddInductive.NormalizationCandidateExecution.declaredInfos,
    List.toList_toArray] using
    AddInductive.declaredInductiveInfos_matches execution.stats nparams
      sources.toArray numNested isUnsafe execution.validationContext
      (by simpa using input.nindices_size)

/-- Source-ordered translations and Theory typing for every exact family
metadata record installed by the retained execution. -/
theorem NormalizationCandidateBlockStagingInput.declarationEvidence
    {nparams : Nat} {sources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {execution : AddInductive.NormalizationCandidateExecution nparams
      sources numNested isUnsafe context}
    {env blockEnv : VEnv} {Us : List Name} {rawDecl : VInductDecl}
    (input : NormalizationCandidateBlockStagingInput context execution
      env blockEnv Us rawDecl) :
    List.Forall₂
      (fun info raw =>
        TrConstVal .safe env (.inductInfo info) raw.toVConstVal ∧
          raw.toVConstant.WF env)
      execution.declaredInfos rawDecl.types :=
  input.familyTypes.declarationEvidence input.declarationMetadata
    input.terminals input.isUnsafe_eq input.validation_lparams_eq

/-- Translation history at the exact pre-family reader environment. -/
theorem NormalizationCandidateBlockStagingInput.preTr
    {nparams : Nat} {sources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {execution : AddInductive.NormalizationCandidateExecution nparams
      sources numNested isUnsafe context}
    {env blockEnv : VEnv} {Us : List Name} {rawDecl : VInductDecl}
    (input : NormalizationCandidateBlockStagingInput context execution
      env blockEnv Us rawDecl) :
    TrEnv' .safe execution.validationContext.env.constants
      execution.validationContext.env.quotInit env := by
  have base : TrEnv' context.safety context.env.constants
      context.env.quotInit env := by
    simpa only [TrEnv,
      TypeChecker.CandidateContextRun.context_safety,
      TypeChecker.CandidateContextRun.context_env,
      input.preFamily.venv_eq] using
      input.preFamily.contextRun.context.trenv
  rw [input.context_safety_eq] at base
  simpa only [input.validation_env_eq] using base

/-- Data-bearing family insertion run derived from the same staging input
that constructs the shared constructor checker context. -/
noncomputable def NormalizationCandidateBlockStagingInput.familyDeclaration
    {nparams : Nat} {sources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {execution : AddInductive.NormalizationCandidateExecution nparams
      sources numNested isUnsafe context}
    {env blockEnv : VEnv} {Us : List Name} {rawDecl : VInductDecl}
    (input : NormalizationCandidateBlockStagingInput context execution
      env blockEnv Us rawDecl) :
    FamilyDeclarationStagingRun
      execution.validationContext.allowPrimitive
      execution.validationContext.env execution.familyEnv
      execution.declaredInfos env blockEnv rawDecl.blockTypeConstants
      execution.validationContext.env.quotInit := by
  apply familyDeclarationStaging
    (evidence := by
      unfold VInductDecl.blockTypeConstants
      rw [List.forall₂_map_right_iff]
      exact input.declarationEvidence)
    (pre := input.preTr)
  · simpa only [AddInductive.declareInductiveTypes,
      AddInductive.NormalizationCandidateExecution.declaredInfos] using
      execution.declareRun
  · rw [blockTypeConstants_foldlM_eq_stageInductiveTypes]
    exact input.stage

/-- All environment-translation and primitive contracts derived from the
same declaration trace and family staging fold. -/
theorem NormalizationCandidateBlockStagingInput.stagingResult
    {nparams : Nat} {sources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {execution : AddInductive.NormalizationCandidateExecution nparams
      sources numNested isUnsafe context}
    {env blockEnv : VEnv} {Us : List Name} {rawDecl : VInductDecl}
    (input : NormalizationCandidateBlockStagingInput context execution
      env blockEnv Us rawDecl) :
    DeclarationTraceStagingResult execution.familyEnv blockEnv
      execution.validationContext.env.quotInit := by
  have metadata : List.Forall₂
      (fun indType info => ∃ numIndices,
        info = AddInductive.declaredInductiveInfo execution.stats nparams
          sources.toArray indType numIndices numNested isUnsafe
            execution.validationContext)
      sources execution.declaredInfos := by
    simpa only [AddInductive.NormalizationCandidateExecution.declaredInfos,
      List.toList_toArray] using
      AddInductive.declaredInductiveInfos_matches execution.stats nparams
        sources.toArray numNested isUnsafe execution.validationContext
        (by simpa using input.nindices_size)
  have evidence := input.familyTypes.declarationEvidence metadata
    input.terminals input.isUnsafe_eq input.validation_lparams_eq
  have preTr : TrEnv' .safe execution.validationContext.env.constants
      execution.validationContext.env.quotInit env := by
    have base : TrEnv' context.safety context.env.constants
        context.env.quotInit env := by
      simpa only [TrEnv,
        TypeChecker.CandidateContextRun.context_safety,
        TypeChecker.CandidateContextRun.context_env,
        input.preFamily.venv_eq] using
        input.preFamily.contextRun.context.trenv
    rw [input.context_safety_eq] at base
    simpa only [input.validation_env_eq] using base
  have preHas : env.HasPrimitives := by
    simpa only [input.preFamily.venv_eq] using
      input.preFamily.contextRun.context.hasPrimitives
  have preSafe : ∀ {n ci},
      execution.validationContext.env.find? n = some ci →
        Environment.primitives.contains n →
        ci.safety = .safe ∧ ci.levelParams = [] := by
    intro n ci found primitive
    apply input.preFamily.contextRun.context.safePrimitives
    · simpa only [TypeChecker.CandidateContextRun.context_env,
        input.validation_env_eq] using found
    · exact primitive
  exact declarationTraceStaging execution.declareTrace input.stage evidence
    input.names_not_primitive
    (by simpa only [input.validation_env_eq] using input.preMapWF)
    preTr preHas preSafe

/-- Verified checker context at the exact environment shared by every
constructor candidate after all raw families have been inserted. -/
def NormalizationCandidateBlockStagingInput.postContext
    {nparams : Nat} {sources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {execution : AddInductive.NormalizationCandidateExecution nparams
      sources numNested isUnsafe context}
    {env blockEnv : VEnv} {Us : List Name} {rawDecl : VInductDecl}
    (input : NormalizationCandidateBlockStagingInput context execution
      env blockEnv Us rawDecl) :
    TypeChecker.VContext where
  env := execution.familyEnv
  lctx := {}
  lparams := context.lparams
  safety := context.safety
  fuel := context.fuel
  venv := blockEnv
  hasPrimitives := input.stagingResult.hasPrimitives
  safePrimitives := input.stagingResult.safePrimitives
  trenv := by
    unfold TrEnv
    rw [input.context_safety_eq, execution.familyEnv_quotInit]
    exact input.stagingResult.trenv
  projectionReady := input.projectionReady
  structureEtaReady := input.structureEtaReady
  mlctx := .nil
  mlctx_wf := trivial
  lctx_eq := rfl

/-- Candidate-context certificate for the derived shared constructor stage. -/
def NormalizationCandidateBlockStagingInput.postContextRun
    {nparams : Nat} {sources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {execution : AddInductive.NormalizationCandidateExecution nparams
      sources numNested isUnsafe context}
    {env blockEnv : VEnv} {Us : List Name} {rawDecl : VInductDecl}
    (input : NormalizationCandidateBlockStagingInput context execution
      env blockEnv Us rawDecl) :
    TypeChecker.CandidateContextRun
      { context with env := execution.familyEnv, lctx := {} } :=
  TypeChecker.CandidateContextRun.ofVContext _ input.postContext (by rfl)
    (TypeChecker.VState.WF.empty_of_reserves input.postContext (by
      intro fv hfv
      change fv ∈ VLCtx.fvars ([] : VLCtx) at hfv
      simp at hfv))
    (by simpa using input.preFamily.contextRun.namePrefix_ne)

/-- Shared semantic stage consumed by every constructor in every family. -/
def NormalizationCandidateBlockStagingInput.postFamily
    {nparams : Nat} {sources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {execution : AddInductive.NormalizationCandidateExecution nparams
      sources numNested isUnsafe context}
    {env blockEnv : VEnv} {Us : List Name} {rawDecl : VInductDecl}
    (input : NormalizationCandidateBlockStagingInput context execution
      env blockEnv Us rawDecl) :
    TypeChecker.CandidateSemanticStage
      { context with env := execution.familyEnv, lctx := {} } blockEnv Us where
  contextRun := input.postContextRun
  venv_eq := rfl
  lparams_eq := by
    rw [TypeChecker.CandidateContextRun.context_lparams]
    calc
      context.lparams = input.preFamily.contextRun.context.lparams := by
        rw [TypeChecker.CandidateContextRun.context_lparams]
      _ = Us := input.preFamily.lparams_eq
  vlctx_eq := rfl

/-- Interpret every family and constructor input in lockstep. -/
theorem CandidateBlockFamilySemanticListInput.exists
    (input : CandidateBlockFamilySemanticListInput env blockEnv Us
      candidates raws) :
    Nonempty (CandidateBlockFamilySemanticListRun env blockEnv Us
      candidates raws) := by
  induction input with
  | nil => exact ⟨.nil⟩
  | cons head tail ih =>
    obtain ⟨headRun⟩ := head.exists
    obtain ⟨tailRun⟩ := ih
    exact ⟨.cons headRun tailRun⟩

/-- Complete verified semantic input for an arbitrary normalization
candidate.  The exact raw family list owns both the all-family staging fold and
the dependent family interpretation, ruling out a reordered staging witness. -/
structure NormalizationCandidateBlockSemanticInput
    (env blockEnv : VEnv) (Us : List Name)
    {sources : List InductiveType}
    (candidate : AddInductive.NormalizationCandidate sources)
    (rawDecl : VInductDecl) where
  uvars_eq : rawDecl.uvars = Us.length
  stage : env.stageInductiveTypes rawDecl.types = some blockEnv
  families : CandidateBlockFamilySemanticListInput env blockEnv Us
    candidate.families rawDecl.types

/-- Automatically interpret the complete mutual semantic hierarchy. -/
theorem NormalizationCandidateBlockSemanticInput.exists
    (input : NormalizationCandidateBlockSemanticInput env blockEnv Us
      candidate rawDecl) :
    Nonempty (NormalizationCandidateBlockSemanticRun env blockEnv Us
      candidate rawDecl) := by
  obtain ⟨families⟩ := input.families.exists
  exact ⟨{
    uvars_eq := input.uvars_eq
    stage := input.stage
    families }⟩

/-- A mutual semantic hierarchy paired with the exact arbitrary-length
producer traversals that selected the same dependent candidate. -/
structure ProducedNormalizationCandidateBlockSemanticRun
    (familyContext constructorContext : AddInductive.Context)
    (env blockEnv : VEnv) (Us : List Name)
    {sources : List InductiveType}
    (candidate : AddInductive.NormalizationCandidate sources)
    (rawDecl : VInductDecl) where
  semantic : NormalizationCandidateBlockSemanticRun env blockEnv Us
    candidate rawDecl
  familyTypesProduced : AddInductive.CandidateFamilyTypeListProduced
    familyContext candidate.families.familyTypes
  familiesProduced : AddInductive.CandidateFamilyListProduced
    constructorContext candidate.families.familyTypes candidate.families

/-- Combine verified semantic inputs with exact producer provenance for the
same source-indexed mutual candidate. -/
theorem NormalizationCandidateBlockSemanticInput.exists_ofProduced
    (input : NormalizationCandidateBlockSemanticInput env blockEnv Us
      candidate rawDecl)
    (familyTypesProduced : AddInductive.CandidateFamilyTypeListProduced
      familyContext candidate.families.familyTypes)
    (familiesProduced : AddInductive.CandidateFamilyListProduced
      constructorContext candidate.families.familyTypes candidate.families) :
    Nonempty (ProducedNormalizationCandidateBlockSemanticRun
      familyContext constructorContext env blockEnv Us candidate rawDecl) := by
  obtain ⟨semantic⟩ := input.exists
  exact ⟨{
    semantic
    familyTypesProduced
    familiesProduced }⟩

/-- One validated singleton family stage derived from a verified entry
candidate context and the exact kernel/Theory family insertion.

The family validator selects the parameter/index split and terminal sort. The
retained candidate semantics then prove the raw family constant well formed;
that proof extends the entry `TrEnv` and constructs the post-family verifier
context. No independently verified post-family `VEnvs` is an input. -/
structure CandidateFamilyStagedInput
    (familyContext constructorContext : AddInductive.Context)
    (env : VEnv) (Us : List Name)
    {source : InductiveType}
    (candidate : AddInductive.CandidateFamilyType source)
    (raw : VInductiveType)
    (preFamily : TypeChecker.CandidateSemanticStage familyContext env Us)
    where
  name_eq : source.name = raw.name
  uvars_eq : raw.uvars = Us.length
  type : TypeChecker.CandidateExprStagedInput preFamily
    candidate.type raw.type
  validation : AddInductive.CandidateExprTrace.FamilyValidationRun
    source candidate.type.trace
  typeEnv : VEnv
  addInduct : AddInductConstant .induct familyContext.env.constants env
    raw.toVConstVal constructorContext.env.constants typeEnv
  /-- The staged family environment has not yet completed a new projection
  artifact; any already-complete host structure remains backed by a registered
  Theory view. -/
  projectionReady : ProjectionReady constructorContext.env typeEnv
  structureEtaReady : StructureEtaReady constructorContext.env typeEnv
  family_lctx_eq : familyContext.lctx = {}
  constructorContext_eq : constructorContext =
    { familyContext with env := constructorContext.env }
  quotInit_eq : constructorContext.env.quotInit =
    familyContext.env.quotInit
  name_not_reflected : raw.name ∉ VEnv.reflectedPrimitiveNames
  name_not_primitive :
    Environment.primitives.contains raw.name = false

/-- Family validation plus retained candidate semantics prove the exact raw
Theory constant suitable for insertion. The semantic view remains hidden
under `Nonempty`; elimination is only into this proposition. -/
theorem CandidateFamilyStagedInput.rawWF
    (input : CandidateFamilyStagedInput familyContext constructorContext
      env Us candidate raw preFamily) :
    raw.toVConstant.WF env := by
  obtain ⟨semantic⟩ := input.type.rootInput.exists
  show env.IsType raw.uvars [] raw.type
  simpa only [input.uvars_eq] using
    semantic.source_isType_of_terminalSort input.validation.terminal_eq

/-- The verifier context after inserting the validated raw family constant.
Primitive reflection and safety are preserved because the new family name is
not a kernel or reflected primitive. -/
def CandidateFamilyStagedInput.postContext
    (input : CandidateFamilyStagedInput familyContext constructorContext
      env Us candidate raw preFamily) : TypeChecker.VContext where
  env := constructorContext.env
  lctx := constructorContext.lctx
  lparams := constructorContext.lparams
  safety := constructorContext.safety
  fuel := constructorContext.fuel
  venv := input.typeEnv
  hasPrimitives := by
    have H : env.HasPrimitives := by
      simpa only [preFamily.venv_eq] using
        preFamily.contextRun.context.hasPrimitives
    exact VEnv.HasPrimitives.addConst H
      input.name_not_reflected input.addInduct.env_add
  safePrimitives := by
    intro n ci
    have preMapWF : familyContext.env.constants.WF := by
      simpa only [preFamily.contextRun.context_env] using
        preFamily.contextRun.context.trenv.map_wf
    exact TypeChecker.AddInductConstant.safePrimitives input.addInduct
      (n := n) (ci := ci) preMapWF (fun hfind hprim => by
        apply preFamily.contextRun.context.safePrimitives
        · simpa only [preFamily.contextRun.context_env] using hfind
        · exact hprim)
      input.name_not_primitive
  trenv := by
    have preTr : TrEnv' familyContext.safety familyContext.env.constants
        familyContext.env.quotInit env := by
      simpa only [TrEnv, preFamily.contextRun.context_safety,
        preFamily.contextRun.context_env, preFamily.venv_eq] using
        preFamily.contextRun.context.trenv
    have postTr := TrEnv'.inductStaging input.addInduct input.rawWF preTr
    change TrEnv' constructorContext.safety constructorContext.env.constants
      constructorContext.env.quotInit input.typeEnv
    rw [show constructorContext.safety = familyContext.safety by
      rw [input.constructorContext_eq]]
    rw [input.quotInit_eq]
    exact postTr
  projectionReady := input.projectionReady
  structureEtaReady := input.structureEtaReady
  mlctx := .nil
  mlctx_wf := trivial
  lctx_eq := by
    change ({} : LocalContext) = constructorContext.lctx
    rw [input.constructorContext_eq, input.family_lctx_eq]

/-- The exact post-family candidate context constructed from family
validation, rather than supplied by a second verifier setup. -/
def CandidateFamilyStagedInput.postContextRun
    (input : CandidateFamilyStagedInput familyContext constructorContext
      env Us candidate raw preFamily) :
    TypeChecker.CandidateContextRun constructorContext :=
  TypeChecker.CandidateContextRun.ofVContext constructorContext
    input.postContext (by rfl)
    (TypeChecker.VState.WF.empty_of_reserves input.postContext (by
      intro fv hfv
      change fv ∈ VLCtx.fvars ([] : VLCtx) at hfv
      simp at hfv))
    (by
      rw [input.constructorContext_eq]
      exact preFamily.contextRun.namePrefix_ne)

/-- Shared post-family semantic stage consumed by every constructor position.
Its implementation and Theory environments are fixed by the exact family
insertion above. -/
def CandidateFamilyStagedInput.postFamily
    (input : CandidateFamilyStagedInput familyContext constructorContext
      env Us candidate raw preFamily) :
    TypeChecker.CandidateSemanticStage constructorContext input.typeEnv Us where
  contextRun := input.postContextRun
  venv_eq := rfl
  lparams_eq := by
    rw [TypeChecker.CandidateContextRun.context_lparams]
    calc
      constructorContext.lparams = familyContext.lparams := by
        rw [input.constructorContext_eq]
      _ = preFamily.contextRun.context.lparams :=
        preFamily.contextRun.context_lparams.symm
      _ = Us := preFamily.lparams_eq
  vlctx_eq := rfl

/-- Recover the exact verified pre-family context at the end of the family
telescope.

Constructor validation starts from this local telescope after changing only
the kernel/Theory environment to the staged post-family pair.  D3 reuses the
pre-change context to replay family-free constructor checks; no local
declaration or fresh identifier is reconstructed. -/
theorem CandidateFamilyStagedInput.preValidationContextRun
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name} {source : InductiveType}
    {candidate : AddInductive.CandidateFamilyType source}
    {raw : VInductiveType}
    {preFamily : TypeChecker.CandidateSemanticStage familyContext env Us}
    (_input : CandidateFamilyStagedInput familyContext constructorContext
      env Us candidate raw preFamily)
    (semantic : TypeChecker.CandidateExprSemanticRootRun env Us
      candidate.type raw.type) :
    ∃ preRun : TypeChecker.CandidateContextRun
        candidate.type.trace.terminalContext,
      preRun.context.venv = env ∧
      preRun.context.lparams = Us := by
  obtain ⟨inferred, recursive⟩ := semantic.recursive
  exact recursive.terminalContextRun semantic.contextRun semantic.venv_eq
    semantic.lparams_eq semantic.vlctx_eq

/-- Rebuild the verified constructor-validation context from the exact
pre-family terminal context run.

The returned run preserves the implementation local context definitionally;
only the kernel/Theory environment and the primitive evidence are changed to
the staged post-family pair. -/
theorem CandidateFamilyStagedInput.validationContextRunFromPre
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name} {source : InductiveType}
    {candidate : AddInductive.CandidateFamilyType source}
    {raw : VInductiveType}
    {preFamily : TypeChecker.CandidateSemanticStage familyContext env Us}
    (input : CandidateFamilyStagedInput familyContext constructorContext
      env Us candidate raw preFamily)
    (terminalRun : TypeChecker.CandidateContextRun
      candidate.type.trace.terminalContext)
    (terminalVenv : terminalRun.context.venv = env)
    (terminalLparams : terminalRun.context.lparams = Us) :
    ∃ validationRun : TypeChecker.CandidateContextRun
        { candidate.type.trace.terminalContext with
          env := constructorContext.env },
      validationRun.context.venv = input.typeEnv ∧
      validationRun.context.lparams = Us ∧
      validationRun.context.vlctx = terminalRun.context.vlctx := by
  have terminalMLWF : terminalRun.context.mlctx.WF env Us := by
    simpa only [terminalVenv, terminalLparams] using
      terminalRun.context.mlctx_wf
  have postMLWF : terminalRun.context.mlctx.WF input.typeEnv Us :=
    terminalMLWF.mono (VEnv.addConst_le input.addInduct.env_add)
  have validationSafety : terminalRun.context.safety =
      input.postContext.safety := by
    calc
      terminalRun.context.safety =
          candidate.type.trace.terminalContext.safety :=
        terminalRun.context_safety
      _ = candidate.type.context.safety :=
        candidate.type.trace.terminalContext_safety
      _ = familyContext.safety := by rw [input.type.context_eq]
      _ = constructorContext.safety := by rw [input.constructorContext_eq]
      _ = input.postContext.safety := rfl
  let validationContext : TypeChecker.VContext :=
    { terminalRun.context with
      env := constructorContext.env
      venv := input.typeEnv
      hasPrimitives := input.postContext.hasPrimitives
      safePrimitives := input.postContext.safePrimitives
      trenv := by
        have postEnv : input.postContext.env = constructorContext.env := rfl
        have postVenv : input.postContext.venv = input.typeEnv := rfl
        simpa only [validationSafety, postEnv, postVenv] using
          input.postContext.trenv
      projectionReady := input.postContext.projectionReady
      structureEtaReady := input.postContext.structureEtaReady
      mlctx_wf := by
        simpa only [terminalLparams] using postMLWF }
  have validationContextEq : validationContext.toContext =
      ({ candidate.type.trace.terminalContext with
        env := constructorContext.env } : AddInductive.Context).toTypeChecker := by
    calc
      validationContext.toContext =
          { terminalRun.context.toContext with
            env := constructorContext.env } := rfl
      _ = { candidate.type.trace.terminalContext.toTypeChecker with
            env := constructorContext.env } :=
        congrArg (fun c : TypeChecker.Context =>
          { c with env := constructorContext.env }) terminalRun.context_eq
      _ = ({ candidate.type.trace.terminalContext with
          env := constructorContext.env } : AddInductive.Context).toTypeChecker :=
        rfl
  let validationRun : TypeChecker.CandidateContextRun
      { candidate.type.trace.terminalContext with
        env := constructorContext.env } :=
    TypeChecker.CandidateContextRun.ofVContext _ validationContext
      validationContextEq
      (TypeChecker.VState.WF.empty_of_reserves validationContext (by
        intro fv hfv
        exact terminalRun.state_wf.ngen_wf fv (by
          simpa only [validationContext] using hfv)))
      terminalRun.namePrefix_ne
  exact ⟨validationRun, rfl, terminalLparams, rfl⟩

/-- Rebuild the verified context in which constructor validation actually
runs.

Family candidates are interpreted before the raw family is inserted, so the
recursive run reaches the correct local telescope in the pre-family Theory
environment.  Constructor validation keeps that exact implementation local
context while replacing only the kernel/Theory environment with the staged
post-family pair.  Monotonicity of local-context verification justifies that
replacement; no local declaration, free-variable identifier, or binder order
is regenerated. -/
theorem CandidateFamilyStagedInput.validationContextRun
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name} {source : InductiveType}
    {candidate : AddInductive.CandidateFamilyType source}
    {raw : VInductiveType}
    {preFamily : TypeChecker.CandidateSemanticStage familyContext env Us}
    (input : CandidateFamilyStagedInput familyContext constructorContext
      env Us candidate raw preFamily)
    (semantic : TypeChecker.CandidateExprSemanticRootRun env Us
      candidate.type raw.type) :
    ∃ validationRun : TypeChecker.CandidateContextRun
        { candidate.type.trace.terminalContext with
          env := constructorContext.env },
      validationRun.context.venv = input.typeEnv ∧
      validationRun.context.lparams = Us := by
  obtain ⟨terminalRun, terminalVenv, terminalLparams⟩ :=
    input.preValidationContextRun semantic
  obtain ⟨validationRun, validationVenv, validationLparams, _⟩ :=
    input.validationContextRunFromPre terminalRun terminalVenv terminalLparams
  exact ⟨validationRun, validationVenv, validationLparams⟩

/-- One source-indexed constructor interpreted in the shared post-family
stage. Header equality and universe alignment stay attached to the exact raw
constructor position; the expression payload contains no independently
verified context and no caller-selected semantic view. -/
structure CandidateConstructorStagedInput
    {candidateContext : AddInductive.Context} {env : VEnv} {Us : List Name}
    (stage : TypeChecker.CandidateSemanticStage candidateContext env Us)
    {source : Constructor}
    (candidate : AddInductive.CandidateConstructor source)
    (raw : VConstVal) where
  name_eq : source.name = raw.name
  uvars_eq : raw.uvars = Us.length
  type : TypeChecker.CandidateExprStagedInput stage candidate.type raw.type

/-- Forget only the shared-stage presentation and recover the established
constructor semantic input. -/
def CandidateConstructorStagedInput.semanticInput
    {candidateContext : AddInductive.Context} {env : VEnv} {Us : List Name}
    {source : Constructor}
    {candidate : AddInductive.CandidateConstructor source}
    {raw : VConstVal}
    {stage : TypeChecker.CandidateSemanticStage candidateContext env Us}
    (input : CandidateConstructorStagedInput stage candidate raw) :
    CandidateConstructorSemanticInput env Us candidate raw where
  name_eq := input.name_eq
  uvars_eq := input.uvars_eq
  type := input.type.rootInput

/-- Executable recursive-identity check for one staged constructor root. -/
def CandidateConstructorStagedInput.identityCheck
    {candidateContext : AddInductive.Context} {env : VEnv} {Us : List Name}
    {source : Constructor}
    {candidate : AddInductive.CandidateConstructor source}
    {raw : VConstVal}
    {stage : TypeChecker.CandidateSemanticStage candidateContext env Us}
    (_input : CandidateConstructorStagedInput stage candidate raw) : Bool :=
  TypeChecker.CandidateExprIdentity.check candidate.type.trace

/-- Exact source-order translations for every constructor in one shared
post-family stage. The dependent indices enforce length, order, source, raw
header, and candidate alignment without `zip` or list lookup. -/
inductive CandidateConstructorStagedListInput
    {candidateContext : AddInductive.Context} {env : VEnv} {Us : List Name}
    (stage : TypeChecker.CandidateSemanticStage candidateContext env Us) :
    {sources : List Constructor} →
      AddInductive.CandidateList AddInductive.CandidateConstructor sources →
      List VConstVal → Type where
  | nil : CandidateConstructorStagedListInput stage .nil []
  | cons
      (head : CandidateConstructorStagedInput stage candidate raw)
      (tail : CandidateConstructorStagedListInput stage candidates raws) :
      CandidateConstructorStagedListInput stage
        (.cons candidate candidates) (raw :: raws)

/-- Candidate-independent translation of one raw constructor source in the
shared post-family Theory environment. -/
structure CandidateConstructorSourceInput (env : VEnv) (Us : List Name)
    (source : Constructor) (raw : VConstVal) where
  name_eq : source.name = raw.name
  uvars_eq : raw.uvars = Us.length
  source_tr : TrExprS env Us [] source.type raw.type

/-- Complete source/raw translations for one constructor list, before the
opaque executable candidate payload is inspected. -/
inductive CandidateConstructorSourceListInput (env : VEnv) (Us : List Name) :
    List Constructor → List VConstVal → Type where
  | nil : CandidateConstructorSourceListInput env Us [] []
  | cons
      (head : CandidateConstructorSourceInput env Us source raw)
      (tail : CandidateConstructorSourceListInput env Us sources raws) :
      CandidateConstructorSourceListInput env Us
        (source :: sources) (raw :: raws)

/-- Recover candidate-independent raw constructors from one exact successful
constructor traversal.  Closed source types translate in the retained shared
post-family context, and the semantic stage transports that context back to
the empty Theory local context. -/
theorem CandidateConstructorSourceListInput.exists_ofProduced
    {candidateContext : AddInductive.Context} {env : VEnv} {Us : List Name}
    {sources : List Constructor}
    (stage : TypeChecker.CandidateSemanticStage candidateContext env Us)
    (candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor sources)
    (produced : AddInductive.CandidateConstructorListProduced candidateContext
      candidates)
    (closed : ∀ source ∈ sources,
      source.type.FVarsIn (fun _ => False)) :
    Nonempty (Σ raws,
      CandidateConstructorSourceListInput env Us sources raws) := by
  induction candidates with
  | nil => exact ⟨⟨[], .nil⟩⟩
  | @cons source sources candidate candidates ih =>
      have contextEq : candidate.type.context = candidateContext :=
        AddInductive.CandidateConstructor.context_eq_of_normalize produced.head
      cases contextEq
      let candidateRun : TypeChecker.CandidateContextRun
          candidate.type.context := stage.contextRun
      have sourceFVars : source.type.FVarsIn
          (· ∈ candidateRun.context.vlctx.fvars) :=
        (closed source (.head _)).mono fun _ impossible => impossible.elim
      obtain ⟨sourceType, contextualTr⟩ :=
        TypeChecker.candidateExprTrace_exists_source_translation
          candidate.type.trace candidateRun sourceFVars
      have candidateVenv : candidateRun.context.venv = env := by
        simpa only [candidateRun] using stage.venv_eq
      have candidateLparams : candidateRun.context.lparams = Us := by
        simpa only [candidateRun] using stage.lparams_eq
      have candidateVlctx : candidateRun.context.vlctx = [] := by
        simpa only [candidateRun] using stage.vlctx_eq
      have sourceTr : TrExprS env Us [] source.type sourceType := by
        change TrExprS candidateRun.context.venv
          candidateRun.context.lparams candidateRun.context.vlctx
          source.type sourceType at contextualTr
        simpa only [candidateVenv, candidateLparams, candidateVlctx] using
          contextualTr
      obtain ⟨⟨raws, tailInput⟩⟩ := ih produced.tail (fun tail member =>
        closed tail (.tail _ member))
      let raw : VConstVal := {
        uvars := Us.length
        type := sourceType
        name := source.name }
      exact ⟨⟨raw :: raws, .cons {
        name_eq := rfl
        uvars_eq := rfl
        source_tr := sourceTr } tailInput⟩⟩

/-- Reindex constructor source translations at the exact candidate list
retained by the ordinary producer. -/
def CandidateConstructorSourceListInput.staged
    {candidateContext : AddInductive.Context}
    {stage : TypeChecker.CandidateSemanticStage candidateContext env Us}
    {sources : List Constructor} {raws : List VConstVal} :
    (input : CandidateConstructorSourceListInput env Us sources raws) →
    (candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor sources) →
    AddInductive.CandidateConstructorListProduced candidateContext candidates →
    (whnfFuel : Nat) →
    candidateContext.fuel.recDepth = whnfFuel + 1 →
    CandidateConstructorStagedListInput stage candidates raws
  | .nil, .nil, _, _, _ => .nil
  | .cons head tail, .cons candidate candidates, produced, whnfFuel,
      whnfDepth =>
      .cons {
          name_eq := head.name_eq
          uvars_eq := head.uvars_eq
          type := {
            context_eq :=
              (AddInductive.CandidateConstructor.context_eq_of_normalize
                produced.head).symm
            source_tr := head.source_tr
            whnfFuel
            whnfDepth := by
              rw [AddInductive.CandidateConstructor.context_eq_of_normalize
                produced.head]
              exact whnfDepth } }
        (tail.staged candidates produced.tail whnfFuel whnfDepth)

/-- Convert the staged, source-indexed constructor translations to the
existing recursive semantic-input representation. -/
def CandidateConstructorStagedListInput.semanticInput
    {candidateContext : AddInductive.Context} {env : VEnv} {Us : List Name}
    {stage : TypeChecker.CandidateSemanticStage candidateContext env Us}
    {sources : List Constructor}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor sources}
    {raws : List VConstVal}
    (input : CandidateConstructorStagedListInput stage candidates raws) :
    CandidateConstructorSemanticListInput env Us candidates raws :=
  match input with
  | .nil => CandidateConstructorSemanticListInput.nil
  | .cons head tail =>
    CandidateConstructorSemanticListInput.cons
      head.semanticInput tail.semanticInput

/-- Executable recursive-identity check for every exact constructor root in
one staged list. -/
def CandidateConstructorStagedListInput.identityCheck
    {candidateContext : AddInductive.Context} {env : VEnv}
    {Us : List Name}
    {stage : TypeChecker.CandidateSemanticStage candidateContext env Us}
    {sources : List Constructor}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor sources}
    {raws : List VConstVal} :
    CandidateConstructorStagedListInput stage candidates raws → Bool
  | .nil => true
  | .cons head tail =>
      head.identityCheck && tail.identityCheck

/-- The recursive identity condition carried by a constructor candidate
spine, with every semantic-stage index erased.  This is the closed executable
form used when a staged input is parameterized by proof-only readiness data. -/
def candidateConstructorListIdentityCheck :
    {sources : List Constructor} →
      AddInductive.CandidateList AddInductive.CandidateConstructor sources →
      Bool
  | [], .nil => true
  | _ :: _, .cons head tail =>
      TypeChecker.CandidateExprIdentity.check head.type.trace &&
        candidateConstructorListIdentityCheck tail

/-- Erasing the shared semantic stage does not change the constructor
identity check. -/
theorem CandidateConstructorStagedListInput.identityCheck_eq_candidate
    {candidateContext : AddInductive.Context} {env : VEnv}
    {Us : List Name}
    {stage : TypeChecker.CandidateSemanticStage candidateContext env Us}
    {sources : List Constructor}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor sources}
    {raws : List VConstVal}
    (input : CandidateConstructorStagedListInput stage candidates raws) :
    input.identityCheck = candidateConstructorListIdentityCheck candidates := by
  induction input with
  | nil => rfl
  | cons head tail ih =>
      simp only [CandidateConstructorStagedListInput.identityCheck,
        CandidateConstructorStagedInput.identityCheck,
        candidateConstructorListIdentityCheck]
      rw [ih]

/-- Interpret an exact staged constructor list at its raw Theory endpoints
when every retained trace is recursively identity-normalizing. -/
def CandidateConstructorStagedListInput.semanticRunOfIdentity
    {candidateContext : AddInductive.Context} {env : VEnv}
    {Us : List Name}
    {stage : TypeChecker.CandidateSemanticStage candidateContext env Us}
    {sources : List Constructor}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor sources}
    {raws : List VConstVal} :
    (input : CandidateConstructorStagedListInput stage candidates raws) →
    input.identityCheck = true →
      CandidateConstructorSemanticListRun env Us candidates raws
  | .nil, _ => .nil
  | .cons head tail, checked => by
      simp only [CandidateConstructorStagedListInput.identityCheck,
        Bool.and_eq_true] at checked
      exact .cons {
          name_eq := head.name_eq
          uvars_eq := head.uvars_eq
          type := head.type.rootInput.semanticOfIdentity
            (TypeChecker.CandidateExprIdentity.of_check checked.1) }
        (tail.semanticRunOfIdentity checked.2)

/-- Identity interpretation changes no raw constructor payload. -/
theorem CandidateConstructorStagedListInput.semanticRunOfIdentity_views
    {candidateContext : AddInductive.Context} {env : VEnv}
    {Us : List Name}
    {stage : TypeChecker.CandidateSemanticStage candidateContext env Us}
    {sources : List Constructor}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor sources}
    {raws : List VConstVal}
    (input : CandidateConstructorStagedListInput stage candidates raws)
    (checked : input.identityCheck = true) :
    (input.semanticRunOfIdentity checked).roots.views = raws := by
  induction input with
  | nil => rfl
  | @cons source sources candidate candidates raw raws head tail ih =>
      simp only [CandidateConstructorStagedListInput.identityCheck,
        Bool.and_eq_true] at checked
      simp only [CandidateConstructorStagedListInput.semanticRunOfIdentity,
        CandidateConstructorSemanticListRun.roots,
        CandidateConstructorListRun.views,
        CandidateConstructorSemanticRun.root,
        CandidateConstructorRun.view,
        TypeChecker.CandidateExprSemanticRootInput.semanticOfIdentity]
      rw [ih checked.2]

/-- Constructor roots for every family in the one shared post-family stage.
The outer dependent list retains family order; each inner staged list retains
constructor order and source ownership. -/
inductive CandidateBlockConstructorStagedListInput
    {candidateContext : AddInductive.Context} {env : VEnv} {Us : List Name}
    (postFamily : TypeChecker.CandidateSemanticStage candidateContext env Us) :
    {sources : List InductiveType} →
      AddInductive.CandidateList AddInductive.CandidateFamily sources →
      List VInductiveType → Type where
  | nil : CandidateBlockConstructorStagedListInput postFamily .nil []
  | cons
      (head : CandidateConstructorStagedListInput postFamily
        candidate.constructors raw.ctors)
      (tail : CandidateBlockConstructorStagedListInput postFamily
        candidates raws) :
      CandidateBlockConstructorStagedListInput postFamily
        (.cons candidate candidates) (raw :: raws)

/-- Candidate-independent constructor translations for every family in a
source-ordered block. -/
inductive CandidateBlockConstructorSourceListInput
    (env : VEnv) (Us : List Name) :
    List InductiveType → List VInductiveType → Type where
  | nil : CandidateBlockConstructorSourceListInput env Us [] []
  | cons
      (head : CandidateConstructorSourceListInput env Us source.ctors raw.ctors)
      (tail : CandidateBlockConstructorSourceListInput env Us sources raws) :
      CandidateBlockConstructorSourceListInput env Us
        (source :: sources) (raw :: raws)

/-- Candidate-independent translations for both phases of one raw block.
Family types live in the entry Theory environment; constructor types live in
the shared environment obtained after staging all raw families. -/
structure CandidateBlockSourceListInput
    (preEnv postEnv : VEnv) (Us : List Name)
    (sources : List InductiveType) (raws : List VInductiveType) where
  familyTypes : CandidateBlockFamilyTypeSourceListInput preEnv Us sources raws
  constructors : CandidateBlockConstructorSourceListInput postEnv Us sources raws

/-- Reindex the exact pre-family traversal at the family list retained by the
complete ordinary execution. -/
theorem _root_.Lean4Lean.AddInductive.NormalizationCandidateExecution.familyTypesProduced
    {nparams : Nat} {sources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    (execution : AddInductive.NormalizationCandidateExecution nparams
      sources numNested isUnsafe context) :
    AddInductive.CandidateFamilyTypeListProduced
      { context with lctx := {} }
      execution.candidate.families.familyTypes := by
  rw [AddInductive.NormalizationCandidateExecution.candidate,
    execution.families.produced.familyTypes_eq]
  exact execution.familyTypes.produced

/-- Every retained ordinary execution exports the exact terminal sort checked
for each assembled family candidate. -/
theorem _root_.Lean4Lean.AddInductive.NormalizationCandidateExecution.familyTerminalSorts
    {nparams : Nat} {sources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    (execution : AddInductive.NormalizationCandidateExecution nparams
      sources numNested isUnsafe context) :
    CandidateBlockFamilyTerminalSortList
      execution.candidate.families := by
  apply CandidateBlockFamilyTerminalSortList.of_familyTypes
  rw [AddInductive.NormalizationCandidateExecution.candidate,
    execution.families.produced.familyTypes_eq]
  exact execution.familyTerminals

/-- Forget only the family-type assembly index of the exact post-family
traversal, retaining every constructor list in source order. -/
theorem _root_.Lean4Lean.AddInductive.NormalizationCandidateExecution.constructorListsProduced
    {nparams : Nat} {sources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    (execution : AddInductive.NormalizationCandidateExecution nparams
      sources numNested isUnsafe context) :
    AddInductive.CandidateBlockConstructorListProduced
      { context with env := execution.familyEnv, lctx := {} }
      execution.candidate.families := by
  exact execution.families.produced.constructorLists

/-- Family-only source staging for one retained ordinary execution.

Unlike `NormalizationCandidateBlockStagingInput`, this owner does not accept
a Theory block endpoint. The retained kernel declaration trace and exact raw
family translations compute that endpoint below; only readiness at the
computed endpoint remains a later input. -/
structure NormalizationCandidateBlockFamilySourceStagingInput
    {nparams : Nat} {sources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    (context : AddInductive.Context)
    (execution : AddInductive.NormalizationCandidateExecution nparams
      sources numNested isUnsafe context)
    (env : VEnv) (Us : List Name) (rawDecl : VInductDecl) where
  uvars_eq : rawDecl.uvars = Us.length
  preFamily : TypeChecker.CandidateSemanticStage
    { context with lctx := {} } env Us
  familySources : CandidateBlockFamilyTypeSourceListInput env Us sources
    rawDecl.types
  whnfFuel : Nat
  whnfDepth : context.fuel.recDepth = whnfFuel + 1
  terminals : CandidateBlockFamilyTerminalSortList
    execution.candidate.families
  nindices_size : execution.stats.nindices.size = sources.length
  validation_env_eq : execution.validationContext.env = context.env
  validation_lparams_eq : execution.validationContext.lparams = Us
  context_safety_eq : context.safety = .safe
  isUnsafe_eq : isUnsafe = false
  preMapWF : context.env.constants.WF
  names_not_primitive : ∀ raw ∈ rawDecl.types,
    raw.name ∉ VEnv.reflectedPrimitiveNames ∧
      Environment.primitives.contains raw.name = false

/-- Reindex every family source translation at the exact pre-family producer
trace. -/
def NormalizationCandidateBlockFamilySourceStagingInput.familyTypes
    {nparams : Nat} {sources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {execution : AddInductive.NormalizationCandidateExecution nparams
      sources numNested isUnsafe context}
    {env : VEnv} {Us : List Name} {rawDecl : VInductDecl}
    (input : NormalizationCandidateBlockFamilySourceStagingInput context
      execution env Us rawDecl) :
    CandidateBlockFamilyTypeStagedListInput input.preFamily
      execution.candidate.families rawDecl.types :=
  input.familySources.staged execution.candidate.families
    execution.familyTypesProduced input.whnfFuel (by
      simpa using input.whnfDepth)

/-- Exact family metadata translations and raw-family typing derived before
the Theory family fold is chosen. -/
theorem
    NormalizationCandidateBlockFamilySourceStagingInput.declarationEvidence
    {nparams : Nat} {sources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {execution : AddInductive.NormalizationCandidateExecution nparams
      sources numNested isUnsafe context}
    {env : VEnv} {Us : List Name} {rawDecl : VInductDecl}
    (input : NormalizationCandidateBlockFamilySourceStagingInput context
      execution env Us rawDecl) :
    List.Forall₂
      (fun info raw =>
        TrConstVal .safe env (.inductInfo info) raw.toVConstVal ∧
          raw.toVConstant.WF env)
      execution.declaredInfos rawDecl.types := by
  have metadata : List.Forall₂
      (fun indType info => ∃ numIndices,
        info = AddInductive.declaredInductiveInfo execution.stats nparams
          sources.toArray indType numIndices numNested isUnsafe
            execution.validationContext)
      sources execution.declaredInfos := by
    simpa only [AddInductive.NormalizationCandidateExecution.declaredInfos,
      List.toList_toArray] using
      AddInductive.declaredInductiveInfos_matches execution.stats nparams
        sources.toArray numNested isUnsafe execution.validationContext
        (by simpa using input.nindices_size)
  exact input.familyTypes.declarationEvidence metadata input.terminals
    input.isUnsafe_eq input.validation_lparams_eq

/-- Entry translation history at the validator context selected by the same
retained execution. -/
theorem NormalizationCandidateBlockFamilySourceStagingInput.preTr
    {nparams : Nat} {sources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {execution : AddInductive.NormalizationCandidateExecution nparams
      sources numNested isUnsafe context}
    {env : VEnv} {Us : List Name} {rawDecl : VInductDecl}
    (input : NormalizationCandidateBlockFamilySourceStagingInput context
      execution env Us rawDecl) :
    TrEnv' .safe execution.validationContext.env.constants
      execution.validationContext.env.quotInit env := by
  have base : TrEnv' context.safety context.env.constants
      context.env.quotInit env := by
    simpa only [TrEnv,
      TypeChecker.CandidateContextRun.context_safety,
      TypeChecker.CandidateContextRun.context_env,
      input.preFamily.venv_eq] using
      input.preFamily.contextRun.context.trenv
  rw [input.context_safety_eq] at base
  simpa only [input.validation_env_eq] using base

/-- Replay the retained kernel family declaration against the exact raw
family translations. Its `blockEnv` is constructed, not selected. -/
noncomputable def
    NormalizationCandidateBlockFamilySourceStagingInput.familyInsertion
    {nparams : Nat} {sources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {execution : AddInductive.NormalizationCandidateExecution nparams
      sources numNested isUnsafe context}
    {env : VEnv} {Us : List Name} {rawDecl : VInductDecl}
    (input : NormalizationCandidateBlockFamilySourceStagingInput context
      execution env Us rawDecl) :
    FamilyDeclarationInsertionRun
      execution.validationContext.allowPrimitive
      execution.validationContext.env execution.familyEnv
      execution.declaredInfos env rawDecl.blockTypeConstants := by
  apply familyDeclarationInsertion (safety := .safe)
    (evidence := by
      unfold VInductDecl.blockTypeConstants
      rw [List.forall₂_map_right_iff]
      exact Lean4Lean.List.Forall₂.imp (h := input.declarationEvidence)
        fun _ _ evidence => evidence.1)
    (pre := input.preTr.aligned)
  simpa only [AddInductive.declareInductiveTypes,
    AddInductive.NormalizationCandidateExecution.declaredInfos] using
    execution.declareRun

/-- The automatically interpreted family insertion is the complete Theory
staging fold for the source-indexed family-only declaration. -/
theorem NormalizationCandidateBlockFamilySourceStagingInput.stage
    {nparams : Nat} {sources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {execution : AddInductive.NormalizationCandidateExecution nparams
      sources numNested isUnsafe context}
    {env : VEnv} {Us : List Name} {rawDecl : VInductDecl}
    (input : NormalizationCandidateBlockFamilySourceStagingInput context
      execution env Us rawDecl) :
    env.stageInductiveTypes rawDecl.types =
      some input.familyInsertion.blockEnv := by
  rw [← blockTypeConstants_foldlM_eq_stageInductiveTypes]
  exact input.familyInsertion.addTypes.to_foldlM

/-- Complete the automatically chosen family stage once readiness has been
proved at its exact kernel/Theory endpoint. -/
noncomputable def
    NormalizationCandidateBlockFamilySourceStagingInput.staging
    {nparams : Nat} {sources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {execution : AddInductive.NormalizationCandidateExecution nparams
      sources numNested isUnsafe context}
    {env : VEnv} {Us : List Name} {rawDecl : VInductDecl}
    (input : NormalizationCandidateBlockFamilySourceStagingInput context
      execution env Us rawDecl)
    (projectionReady : ProjectionReady execution.familyEnv
      input.familyInsertion.blockEnv)
    (structureEtaReady : StructureEtaReady execution.familyEnv
      input.familyInsertion.blockEnv) :
    NormalizationCandidateBlockStagingInput context execution env
      input.familyInsertion.blockEnv Us rawDecl where
  uvars_eq := input.uvars_eq
  preFamily := input.preFamily
  familyTypes := input.familyTypes
  terminals := input.terminals
  stage := input.stage
  nindices_size := input.nindices_size
  validation_env_eq := input.validation_env_eq
  validation_lparams_eq := input.validation_lparams_eq
  context_safety_eq := input.context_safety_eq
  isUnsafe_eq := input.isUnsafe_eq
  preMapWF := input.preMapWF
  names_not_primitive := input.names_not_primitive
  projectionReady := projectionReady
  structureEtaReady := structureEtaReady

/-- Staging observes only the inherited family constant payload, so changing
the constructor inventory of every raw family leaves the complete
source-ordered staging fold unchanged. -/
theorem _root_.Lean4Lean.VEnv.stageInductiveTypes_congr_familyConstants
    : ∀ (env : VEnv) {left right : List VInductiveType},
      List.Forall₂
        (fun left right => left.toVConstVal = right.toVConstVal)
        left right →
      env.stageInductiveTypes left = env.stageInductiveTypes right
  | _, _, _, .nil => rfl
  | env, _, _, .cons head tail => by
      simp only [VEnv.stageInductiveTypes, List.foldlM_cons]
      have name_eq := congrArg VConstVal.name head
      have constant_eq := congrArg VConstVal.toVConstant head
      rw [name_eq, constant_eq]
      apply Option.bind_congr
      intro next _
      exact VEnv.stageInductiveTypes_congr_familyConstants next tail

/-- A complete translated block obtained by enriching a family-only raw list.
The positional relation records that only constructor fields changed. -/
structure CandidateBlockSourceListEnrichment
    (preEnv postEnv : VEnv) (Us : List Name)
    (sources : List InductiveType) (familyRaws : List VInductiveType) where
  raws : List VInductiveType
  input : CandidateBlockSourceListInput preEnv postEnv Us sources raws
  familyConstants : List.Forall₂
    (fun raw familyRaw => raw.toVConstVal = familyRaw.toVConstVal)
    raws familyRaws

/-- Constructor enrichment preserves the exact Theory endpoint chosen by the
family-only staging fold. -/
theorem CandidateBlockSourceListEnrichment.stage_eq
    {preEnv postEnv : VEnv} {Us : List Name}
    {sources : List InductiveType} {familyRaws : List VInductiveType}
    (enrichment : CandidateBlockSourceListEnrichment preEnv postEnv Us
      sources familyRaws) (env : VEnv) :
    env.stageInductiveTypes enrichment.raws =
      env.stageInductiveTypes familyRaws :=
  VEnv.stageInductiveTypes_congr_familyConstants env
    enrichment.familyConstants

/-- Replace the family-only raw list of a declaration by its enriched common
raw list while preserving the declaration header. -/
def CandidateBlockSourceListEnrichment.toRawDecl
    {preEnv postEnv : VEnv} {Us : List Name}
    {sources : List InductiveType} {familyRaws : List VInductiveType}
    (enrichment : CandidateBlockSourceListEnrichment preEnv postEnv Us
      sources familyRaws) (familyDecl : VInductDecl) : VInductDecl :=
  { familyDecl with types := enrichment.raws }

/-- Any name-only property of the family-only raw list survives constructor
enrichment. -/
theorem CandidateBlockSourceListEnrichment.forall_names
    {preEnv postEnv : VEnv} {Us : List Name}
    {sources : List InductiveType} {familyRaws : List VInductiveType}
    (enrichment : CandidateBlockSourceListEnrichment preEnv postEnv Us
      sources familyRaws)
    (P : Name → Prop)
    (family : ∀ raw ∈ familyRaws, P raw.name) :
    ∀ raw ∈ enrichment.raws, P raw.name := by
  have transfer : ∀ {raws familyRaws : List VInductiveType},
      List.Forall₂
        (fun raw familyRaw => raw.toVConstVal = familyRaw.toVConstVal)
        raws familyRaws →
      (∀ familyRaw ∈ familyRaws, P familyRaw.name) →
      ∀ raw ∈ raws, P raw.name := by
    intro raws familyRaws relation
    induction relation with
    | nil => intro _ raw member; nomatch member
    | @cons raw familyRaw raws familyRaws head tail ih =>
        intro families raw' member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · have name_eq := congrArg VConstVal.name head
          rw [name_eq]
          exact families familyRaw (.head _)
        · exact ih (fun other otherMember =>
            families other (.tail _ otherMember)) raw' member
  exact transfer enrichment.familyConstants family

/-- Rebuild the exact block staging owner over the enriched raw declaration.
The endpoint and readiness certificates are reused because the family
constant fold is unchanged. -/
noncomputable def
    NormalizationCandidateBlockFamilySourceStagingInput.enrichedStaging
    {nparams : Nat} {sources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {execution : AddInductive.NormalizationCandidateExecution nparams
      sources numNested isUnsafe context}
    {env : VEnv} {Us : List Name} {familyDecl : VInductDecl}
    (input : NormalizationCandidateBlockFamilySourceStagingInput context
      execution env Us familyDecl)
    (enrichment : CandidateBlockSourceListEnrichment env
      input.familyInsertion.blockEnv Us sources familyDecl.types)
    (projectionReady : ProjectionReady execution.familyEnv
      input.familyInsertion.blockEnv)
    (structureEtaReady : StructureEtaReady execution.familyEnv
      input.familyInsertion.blockEnv) :
    NormalizationCandidateBlockStagingInput context execution env
      input.familyInsertion.blockEnv Us
      (enrichment.toRawDecl familyDecl) where
  uvars_eq := input.uvars_eq
  preFamily := input.preFamily
  familyTypes := enrichment.input.familyTypes.staged
    execution.candidate.families execution.familyTypesProduced input.whnfFuel
      (by simpa using input.whnfDepth)
  terminals := input.terminals
  stage := (enrichment.stage_eq env).trans input.stage
  nindices_size := input.nindices_size
  validation_env_eq := input.validation_env_eq
  validation_lparams_eq := input.validation_lparams_eq
  context_safety_eq := input.context_safety_eq
  isUnsafe_eq := input.isUnsafe_eq
  preMapWF := input.preMapWF
  names_not_primitive := by
    simpa only [CandidateBlockSourceListEnrichment.toRawDecl] using
      enrichment.forall_names
        (fun name => name ∉ VEnv.reflectedPrimitiveNames ∧
          Environment.primitives.contains name = false)
        input.names_not_primitive
  projectionReady := projectionReady
  structureEtaReady := structureEtaReady

/-- Enrich the family-only raw list while retaining the positional proof that
every staged family constant is unchanged. -/
theorem
    CandidateBlockFamilyTypeSourceListInput.withConstructorsEnrichment
    {preEnv postEnv : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context}
    {sources : List InductiveType} {familyRaws : List VInductiveType}
    (familyInput : CandidateBlockFamilyTypeSourceListInput preEnv Us
      sources familyRaws)
    (postFamily : TypeChecker.CandidateSemanticStage candidateContext
      postEnv Us)
    (families : AddInductive.CandidateList
      AddInductive.CandidateFamily sources)
    (produced : AddInductive.CandidateBlockConstructorListProduced
      candidateContext families)
    (closed : ∀ source ∈ sources, ∀ ctor ∈ source.ctors,
      ctor.type.FVarsIn (fun _ => False)) :
    Nonempty (CandidateBlockSourceListEnrichment preEnv postEnv Us
      sources familyRaws) := by
  induction familyInput with
  | nil =>
      cases families
      exact ⟨{
        raws := []
        input := { familyTypes := .nil, constructors := .nil }
        familyConstants := .nil }⟩
  | @cons source familyRaw sources familyRaws familyHead familyTail ih =>
      cases families with
      | cons family families =>
          obtain ⟨⟨ctorRaws, constructorInput⟩⟩ :=
            CandidateConstructorSourceListInput.exists_ofProduced postFamily
              family.constructors produced.head (fun ctor member =>
                closed source (.head _) ctor member)
          obtain ⟨tail⟩ := ih families produced.tail
            (fun tail tailMember ctor ctorMember =>
              closed tail (.tail _ tailMember) ctor ctorMember)
          let raw : VInductiveType := { familyRaw with ctors := ctorRaws }
          exact ⟨{
            raws := raw :: tail.raws
            input := {
              familyTypes := .cons {
                name_eq := familyHead.name_eq
                uvars_eq := familyHead.uvars_eq
                source_tr := familyHead.source_tr } tail.input.familyTypes
              constructors := .cons constructorInput tail.input.constructors }
            familyConstants := .cons rfl tail.familyConstants }⟩

/-- Enrich already translated family raws with the exact constructor raws
recovered from the retained post-family traversals.  Updating `ctors` leaves
each family constant payload unchanged, so all pre-family translations are
preserved while the two source-indexed phases acquire one common raw list. -/
theorem CandidateBlockFamilyTypeSourceListInput.withConstructors
    {preEnv postEnv : VEnv} {Us : List Name}
    {candidateContext : AddInductive.Context}
    {sources : List InductiveType} {familyRaws : List VInductiveType}
    (familyInput : CandidateBlockFamilyTypeSourceListInput preEnv Us
      sources familyRaws)
    (postFamily : TypeChecker.CandidateSemanticStage candidateContext
      postEnv Us)
    (families : AddInductive.CandidateList
      AddInductive.CandidateFamily sources)
    (produced : AddInductive.CandidateBlockConstructorListProduced
      candidateContext families)
    (closed : ∀ source ∈ sources, ∀ ctor ∈ source.ctors,
      ctor.type.FVarsIn (fun _ => False)) :
    Nonempty (Σ raws,
      CandidateBlockSourceListInput preEnv postEnv Us sources raws) := by
  obtain ⟨enrichment⟩ := familyInput.withConstructorsEnrichment
    postFamily families produced closed
  exact ⟨⟨enrichment.raws, enrichment.input⟩⟩

/-- Recover one complete raw Theory block directly from the exact two-phase
ordinary producer.  Family translations are chosen in the entry stage and
then enriched, without changing their constant payloads, by constructor
translations chosen in the shared post-family stage. -/
theorem CandidateBlockSourceListInput.exists_ofProduced
    {preEnv postEnv : VEnv} {Us : List Name}
    {familyContext constructorContext : AddInductive.Context}
    {sources : List InductiveType}
    (preFamily : TypeChecker.CandidateSemanticStage familyContext preEnv Us)
    (postFamily : TypeChecker.CandidateSemanticStage constructorContext
      postEnv Us)
    (families : AddInductive.CandidateList
      AddInductive.CandidateFamily sources)
    (familyTypesProduced : AddInductive.CandidateFamilyTypeListProduced
      familyContext families.familyTypes)
    (constructorsProduced :
      AddInductive.CandidateBlockConstructorListProduced constructorContext
        families)
    (closed : ∀ source ∈ sources,
      source.type.FVarsIn (fun _ => False) ∧
        ∀ ctor ∈ source.ctors,
          ctor.type.FVarsIn (fun _ => False)) :
    Nonempty (Σ raws,
      CandidateBlockSourceListInput preEnv postEnv Us sources raws) := by
  obtain ⟨⟨familyRaws, familyInput⟩⟩ :=
    CandidateBlockFamilyTypeSourceListInput.exists_ofProduced preFamily
      families familyTypesProduced (fun source member =>
        (closed source member).1)
  exact familyInput.withConstructors postFamily families constructorsProduced
    (fun source member => (closed source member).2)

/-- Reindex all block constructor translations at the exact nested candidate
lists and constructor traversal traces retained by one ordinary execution. -/
def CandidateBlockConstructorSourceListInput.staged
    {candidateContext : AddInductive.Context}
    {postFamily : TypeChecker.CandidateSemanticStage candidateContext env Us}
    {sources : List InductiveType} {raws : List VInductiveType} :
    (input : CandidateBlockConstructorSourceListInput env Us sources raws) →
    (families : AddInductive.CandidateList
      AddInductive.CandidateFamily sources) →
    AddInductive.CandidateBlockConstructorListProduced candidateContext
      families →
    (whnfFuel : Nat) →
    candidateContext.fuel.recDepth = whnfFuel + 1 →
    CandidateBlockConstructorStagedListInput postFamily families raws
  | .nil, .nil, _, _, _ => .nil
  | .cons head tail, .cons family families, produced, whnfFuel, whnfDepth =>
      .cons
        (head.staged family.constructors produced.head whnfFuel whnfDepth)
        (tail.staged families produced.tail whnfFuel whnfDepth)

/-- Join the independently staged family-type and constructor halves into the
existing complete arbitrary-block semantic input. -/
def CandidateBlockFamilyTypeStagedListInput.semanticInput
    {familyContext constructorContext : AddInductive.Context}
    {env blockEnv : VEnv} {Us : List Name}
    {preFamily : TypeChecker.CandidateSemanticStage familyContext env Us}
    {postFamily : TypeChecker.CandidateSemanticStage constructorContext
      blockEnv Us}
    {sources : List InductiveType}
    {candidates : AddInductive.CandidateList AddInductive.CandidateFamily
      sources}
    {raws : List VInductiveType}
    (familyTypes : CandidateBlockFamilyTypeStagedListInput preFamily
      candidates raws)
    (constructors : CandidateBlockConstructorStagedListInput postFamily
      candidates raws) :
    CandidateBlockFamilySemanticListInput env blockEnv Us candidates raws :=
  match familyTypes, constructors with
  | .nil, .nil => .nil
  | .cons family families, .cons constructorList constructorLists =>
    .cons {
      name_eq := family.name_eq
      uvars_eq := family.uvars_eq
      type := family.type.rootInput
      constructors := constructorList.semanticInput }
      (families.semanticInput constructorLists)

/-- One executable recursive-identity check for every family and constructor
root in the exact staged block. -/
def CandidateBlockFamilyTypeStagedListInput.identityCheck
    {familyContext constructorContext : AddInductive.Context}
    {env blockEnv : VEnv} {Us : List Name}
    {preFamily : TypeChecker.CandidateSemanticStage familyContext env Us}
    {postFamily : TypeChecker.CandidateSemanticStage constructorContext
      blockEnv Us}
    {sources : List InductiveType}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateFamily sources}
    {raws : List VInductiveType} :
    (familyTypes : CandidateBlockFamilyTypeStagedListInput preFamily
      candidates raws) →
    CandidateBlockConstructorStagedListInput postFamily candidates raws → Bool
  | .nil, .nil => true
  | .cons family families, .cons constructorList constructorLists =>
      family.identityCheck && constructorList.identityCheck &&
        families.identityCheck constructorLists

/-- The complete family/constructor identity condition retained by a block
candidate, independent of either proof-carrying semantic stage. -/
def candidateBlockIdentityCheck :
    {sources : List InductiveType} →
      AddInductive.CandidateList AddInductive.CandidateFamily sources → Bool
  | [], .nil => true
  | _ :: _, .cons head tail =>
      TypeChecker.CandidateExprIdentity.check head.familyType.type.trace &&
        candidateConstructorListIdentityCheck head.constructors &&
        candidateBlockIdentityCheck tail

/-- The staged block check is exactly its closed candidate-only Boolean.
This permits native evaluation even when the staging owner depends on an
open readiness certificate. -/
theorem CandidateBlockFamilyTypeStagedListInput.identityCheck_eq_candidate
    {familyContext constructorContext : AddInductive.Context}
    {env blockEnv : VEnv} {Us : List Name}
    {preFamily : TypeChecker.CandidateSemanticStage familyContext env Us}
    {postFamily : TypeChecker.CandidateSemanticStage constructorContext
      blockEnv Us}
    {sources : List InductiveType}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateFamily sources}
    {raws : List VInductiveType}
    (familyTypes : CandidateBlockFamilyTypeStagedListInput preFamily
      candidates raws)
    (constructors : CandidateBlockConstructorStagedListInput postFamily
      candidates raws) :
    familyTypes.identityCheck constructors =
      candidateBlockIdentityCheck candidates := by
  induction familyTypes with
  | nil =>
      cases constructors
      rfl
  | cons family families ih =>
      cases constructors with
      | cons constructorList constructorLists =>
          simp only [CandidateBlockFamilyTypeStagedListInput.identityCheck,
            CandidateBlockFamilyTypeStagedInput.identityCheck,
            candidateBlockIdentityCheck]
          rw [constructorList.identityCheck_eq_candidate,
            ih constructorLists]

/-- Interpret a complete staged block at its raw Theory endpoints when every
retained family and constructor trace is recursively identity-normalizing. -/
def CandidateBlockFamilyTypeStagedListInput.semanticRunOfIdentity
    {familyContext constructorContext : AddInductive.Context}
    {env blockEnv : VEnv} {Us : List Name}
    {preFamily : TypeChecker.CandidateSemanticStage familyContext env Us}
    {postFamily : TypeChecker.CandidateSemanticStage constructorContext
      blockEnv Us}
    {sources : List InductiveType}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateFamily sources}
    {raws : List VInductiveType} :
    (familyTypes : CandidateBlockFamilyTypeStagedListInput preFamily
      candidates raws) →
    (constructors : CandidateBlockConstructorStagedListInput postFamily
      candidates raws) →
    familyTypes.identityCheck constructors = true →
      CandidateBlockFamilySemanticListRun env blockEnv Us candidates raws
  | .nil, .nil, _ => .nil
  | .cons family families, .cons constructorList constructorLists,
      checked => by
      simp only [CandidateBlockFamilyTypeStagedListInput.identityCheck,
        Bool.and_eq_true] at checked
      exact .cons {
          name_eq := family.name_eq
          uvars_eq := family.uvars_eq
          type := family.type.rootInput.semanticOfIdentity
            (TypeChecker.CandidateExprIdentity.of_check checked.1.1)
          constructors := constructorList.semanticRunOfIdentity checked.1.2 }
        (families.semanticRunOfIdentity constructorLists checked.2)

/-- Identity interpretation changes no family or constructor payload in the
complete staged block. -/
theorem CandidateBlockFamilyTypeStagedListInput.semanticRunOfIdentity_views
    {familyContext constructorContext : AddInductive.Context}
    {env blockEnv : VEnv} {Us : List Name}
    {preFamily : TypeChecker.CandidateSemanticStage familyContext env Us}
    {postFamily : TypeChecker.CandidateSemanticStage constructorContext
      blockEnv Us}
    {sources : List InductiveType}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateFamily sources}
    {raws : List VInductiveType}
    (familyTypes : CandidateBlockFamilyTypeStagedListInput preFamily
      candidates raws)
    (constructors : CandidateBlockConstructorStagedListInput postFamily
      candidates raws)
    (checked : familyTypes.identityCheck constructors = true) :
    (familyTypes.semanticRunOfIdentity constructors checked).views = raws := by
  induction familyTypes with
  | nil =>
      cases constructors
      rfl
  | @cons source sources candidate candidates raw raws family families ih =>
      cases constructors with
      | cons constructorList constructorLists =>
          simp only [CandidateBlockFamilyTypeStagedListInput.identityCheck,
            Bool.and_eq_true] at checked
          simp only [
            CandidateBlockFamilyTypeStagedListInput.semanticRunOfIdentity,
            CandidateBlockFamilySemanticListRun.views,
            CandidateBlockFamilySemanticRun.view,
            TypeChecker.CandidateExprSemanticRootInput.semanticOfIdentity]
          rw [constructorList.semanticRunOfIdentity_views checked.1.2,
            ih constructorLists checked.2]

/-- Complete staged semantic owner for an arbitrary normalization execution.
Family roots construct the exact shared post-family stage first; every
constructor root is then checked in that derived stage. -/
structure StagedNormalizationCandidateBlockSemanticInput
    {nparams : Nat} {sources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {execution : AddInductive.NormalizationCandidateExecution nparams
      sources numNested isUnsafe context}
    {env blockEnv : VEnv} {Us : List Name} {rawDecl : VInductDecl}
    (staging : NormalizationCandidateBlockStagingInput context execution
      env blockEnv Us rawDecl) where
  postFamily : TypeChecker.CandidateSemanticStage
    { context with env := execution.familyEnv, lctx := {} } blockEnv Us
  constructors : CandidateBlockConstructorStagedListInput postFamily
    execution.candidate.families rawDecl.types

/-- Reindex the retained post-family constructor traversals at an already
staged common raw block. Family translations are owned by `staging`; this
projection contributes exactly the constructor half. -/
def CandidateBlockSourceListInput.staged
    {nparams : Nat} {sources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {execution : AddInductive.NormalizationCandidateExecution nparams
      sources numNested isUnsafe context}
    {env blockEnv : VEnv} {Us : List Name} {rawDecl : VInductDecl}
    {staging : NormalizationCandidateBlockStagingInput context execution
      env blockEnv Us rawDecl}
    (input : CandidateBlockSourceListInput env blockEnv Us sources
      rawDecl.types)
    (constructorsProduced :
      AddInductive.CandidateBlockConstructorListProduced
        { context with env := execution.familyEnv, lctx := {} }
        execution.candidate.families)
    (whnfFuel : Nat)
    (whnfDepth : context.fuel.recDepth = whnfFuel + 1) :
    StagedNormalizationCandidateBlockSemanticInput staging where
  postFamily := staging.postFamily
  constructors := input.constructors.staged execution.candidate.families
    constructorsProduced whnfFuel (by simpa using whnfDepth)

/-- One dependent output containing the constructor-enriched raw declaration,
its exact family staging, and the complete staged semantic hierarchy. -/
structure NormalizationCandidateBlockEnrichedStagingResult
    {nparams : Nat} {sources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {execution : AddInductive.NormalizationCandidateExecution nparams
      sources numNested isUnsafe context}
    {env : VEnv} {Us : List Name} {familyDecl : VInductDecl}
    (input : NormalizationCandidateBlockFamilySourceStagingInput context
      execution env Us familyDecl) where
  blockEnv : VEnv
  enrichment : CandidateBlockSourceListEnrichment env blockEnv Us sources
    familyDecl.types
  staging : NormalizationCandidateBlockStagingInput context execution env
    blockEnv Us (enrichment.toRawDecl familyDecl)
  semantic : StagedNormalizationCandidateBlockSemanticInput staging

/-- Select the final common raw block from the two exact producer phases and
stage it at the endpoint computed by the retained family declaration trace.
The only post-family assumptions are readiness at that exact endpoint. -/
theorem NormalizationCandidateBlockFamilySourceStagingInput.enrich
    {nparams : Nat} {sources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {execution : AddInductive.NormalizationCandidateExecution nparams
      sources numNested isUnsafe context}
    {env : VEnv} {Us : List Name} {familyDecl : VInductDecl}
    (input : NormalizationCandidateBlockFamilySourceStagingInput context
      execution env Us familyDecl)
    (projectionReady : ProjectionReady execution.familyEnv
      input.familyInsertion.blockEnv)
    (structureEtaReady : StructureEtaReady execution.familyEnv
      input.familyInsertion.blockEnv)
    (closed : ∀ source ∈ sources, ∀ ctor ∈ source.ctors,
      ctor.type.FVarsIn (fun _ => False)) :
    Nonempty (NormalizationCandidateBlockEnrichedStagingResult input) := by
  let familyStaging := input.staging projectionReady structureEtaReady
  obtain ⟨enrichment⟩ := input.familySources.withConstructorsEnrichment
    familyStaging.postFamily execution.candidate.families
      execution.constructorListsProduced closed
  let staging := input.enrichedStaging enrichment projectionReady
    structureEtaReady
  exact ⟨{
    blockEnv := input.familyInsertion.blockEnv
    enrichment
    staging
    semantic := enrichment.input.staged execution.constructorListsProduced
      input.whnfFuel input.whnfDepth }⟩

/-- Project the established block semantic-input hierarchy from the
consolidated two-stage owner. -/
def StagedNormalizationCandidateBlockSemanticInput.semanticInput
    {nparams : Nat} {sources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {execution : AddInductive.NormalizationCandidateExecution nparams
      sources numNested isUnsafe context}
    {env blockEnv : VEnv} {Us : List Name} {rawDecl : VInductDecl}
    {staging : NormalizationCandidateBlockStagingInput context execution
      env blockEnv Us rawDecl}
    (input : StagedNormalizationCandidateBlockSemanticInput staging) :
    NormalizationCandidateBlockSemanticInput env blockEnv Us
      execution.candidate rawDecl where
  uvars_eq := staging.uvars_eq
  stage := staging.stage
  families := staging.familyTypes.semanticInput input.constructors

/-- Executable identity check for the complete consolidated staged owner. -/
def StagedNormalizationCandidateBlockSemanticInput.identityCheck
    {nparams : Nat} {sources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {execution : AddInductive.NormalizationCandidateExecution nparams
      sources numNested isUnsafe context}
    {env blockEnv : VEnv} {Us : List Name} {rawDecl : VInductDecl}
    {staging : NormalizationCandidateBlockStagingInput context execution
      env blockEnv Us rawDecl}
    (input : StagedNormalizationCandidateBlockSemanticInput staging) : Bool :=
  staging.familyTypes.identityCheck input.constructors

/-- Interpret the consolidated staged owner at the exact raw Theory block
when every retained expression trace is recursively identity-normalizing. -/
def StagedNormalizationCandidateBlockSemanticInput.semanticRunOfIdentity
    {nparams : Nat} {sources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {execution : AddInductive.NormalizationCandidateExecution nparams
      sources numNested isUnsafe context}
    {env blockEnv : VEnv} {Us : List Name} {rawDecl : VInductDecl}
    {staging : NormalizationCandidateBlockStagingInput context execution
      env blockEnv Us rawDecl}
    (input : StagedNormalizationCandidateBlockSemanticInput staging)
    (identity : input.identityCheck = true) :
    NormalizationCandidateBlockSemanticRun env blockEnv Us
      execution.candidate rawDecl where
  uvars_eq := staging.uvars_eq
  stage := staging.stage
  families := staging.familyTypes.semanticRunOfIdentity input.constructors
    identity

/-- The identity-specialized consolidated run retains the exact raw family
list. -/
theorem StagedNormalizationCandidateBlockSemanticInput.semanticRunOfIdentity_views
    {nparams : Nat} {sources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {execution : AddInductive.NormalizationCandidateExecution nparams
      sources numNested isUnsafe context}
    {env blockEnv : VEnv} {Us : List Name} {rawDecl : VInductDecl}
    {staging : NormalizationCandidateBlockStagingInput context execution
      env blockEnv Us rawDecl}
    (input : StagedNormalizationCandidateBlockSemanticInput staging)
    (identity : input.identityCheck = true) :
    (input.semanticRunOfIdentity identity).families.views = rawDecl.types := by
  exact staging.familyTypes.semanticRunOfIdentity_views input.constructors
    identity

/-- Identity-specialized staged interpretation induces exactly Theory's
identity normalization, independently of the opaque producer payload. -/
theorem StagedNormalizationCandidateBlockSemanticInput.semanticRunOfIdentity_normalization
    {nparams : Nat} {sources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {execution : AddInductive.NormalizationCandidateExecution nparams
      sources numNested isUnsafe context}
    {env blockEnv : VEnv} {Us : List Name} {rawDecl : VInductDecl}
    {staging : NormalizationCandidateBlockStagingInput context execution
      env blockEnv Us rawDecl}
    (input : StagedNormalizationCandidateBlockSemanticInput staging)
    (identity : input.identityCheck = true) :
    (input.semanticRunOfIdentity identity).normalization =
      Normalization.identity rawDecl := by
  apply (show ∀ {left right : Normalization rawDecl},
      left.view = right.view → left = right from by
    intro left right view_eq
    cases left
    cases right
    simp only [VInductDecl.Normalization.mk.injEq] at *
    exact view_eq)
  change { rawDecl with types :=
    (input.semanticRunOfIdentity identity).families.views } = rawDecl
  rw [input.semanticRunOfIdentity_views identity]

/-- Pre-run semantic evidence for a complete singleton family position.  The
family type is interpreted in the input environment and its constructor list
in the exact environment obtained by inserting the raw family constant. -/
structure CandidateFamilySemanticInput (env : VEnv) (Us : List Name)
    {source : InductiveType}
    (candidate : AddInductive.CandidateFamily source)
    (raw : VInductiveType) where
  name_eq : source.name = raw.name
  uvars_eq : raw.uvars = Us.length
  type : TypeChecker.CandidateExprSemanticRootInput env Us
    candidate.familyType.type raw.type
  typeEnv : VEnv
  addType : env.addConst raw.name raw.toVConstant = some typeEnv
  constructors : CandidateConstructorSemanticListInput typeEnv Us
    candidate.constructors raw.ctors

/-- Interpret the family root and all post-insertion constructor roots from
their exact pre-run inputs. -/
theorem CandidateFamilySemanticInput.exists
    (input : CandidateFamilySemanticInput env Us candidate raw) :
    Nonempty (CandidateFamilySemanticRun env Us candidate raw) := by
  obtain ⟨type⟩ := input.type.exists
  obtain ⟨constructors⟩ := input.constructors.exists
  exact ⟨{
    name_eq := input.name_eq
    uvars_eq := input.uvars_eq
    type := type
    typeEnv := input.typeEnv
    addType := input.addType
    constructors := constructors }⟩

/-- Pre-run semantic evidence for one source-indexed singleton normalization
candidate.  The source declaration and candidate list indices rule out an
unrelated raw family or a partial constructor list. -/
structure NormalizationCandidateSemanticInput (env : VEnv) (Us : List Name)
    {source : InductiveType}
    (candidate : AddInductive.NormalizationCandidate [source])
    (rawDecl : VInductDecl) where
  raw : VInductiveType
  raw_types_eq : rawDecl.types = [raw]
  uvars_eq : rawDecl.uvars = Us.length
  family : CandidateFamilySemanticInput env Us
    candidate.families.singleton raw

/-- Automatically interpret the complete singleton semantic hierarchy from
its verified, source-indexed inputs. -/
theorem NormalizationCandidateSemanticInput.exists
    (input : NormalizationCandidateSemanticInput env Us candidate rawDecl) :
    Nonempty (NormalizationCandidateSemanticRun env Us candidate rawDecl) := by
  obtain ⟨family⟩ := input.family.exists
  exact ⟨{
    raw := input.raw
    raw_types_eq := input.raw_types_eq
    uvars_eq := input.uvars_eq
    family := family }⟩

/-- The automatic semantic hierarchy paired with the exact executable
family-type and constructor-list traversals that selected the same dependent
candidate.  The two producer contexts are explicit because family types are
checked before raw-family insertion and constructors after it. -/
structure ProducedNormalizationCandidateSemanticRun
    (familyContext constructorContext : AddInductive.Context)
    (env : VEnv) (Us : List Name)
    {source : InductiveType}
    (candidate : AddInductive.NormalizationCandidate [source])
    (rawDecl : VInductDecl) where
  semantic : NormalizationCandidateSemanticRun env Us candidate rawDecl
  familyTypesProduced : AddInductive.CandidateFamilyTypeListProduced
    familyContext
    (.cons candidate.families.singleton.familyType .nil)
  familiesProduced : AddInductive.CandidateFamilyListProduced
    constructorContext
    (.cons candidate.families.singleton.familyType .nil)
    candidate.families

/-- Combine exact arbitrary-length producer witnesses with verified semantic
inputs for the same source-indexed singleton candidate.  Operational evidence
selects the candidate; only the retained checker interpreter supplies Theory
meaning. -/
theorem NormalizationCandidateSemanticInput.exists_ofProduced
    (input : NormalizationCandidateSemanticInput env Us candidate rawDecl)
    (familyTypesProduced : AddInductive.CandidateFamilyTypeListProduced
      familyContext
      (.cons candidate.families.singleton.familyType .nil))
    (familiesProduced : AddInductive.CandidateFamilyListProduced
      constructorContext
      (.cons candidate.families.singleton.familyType .nil)
      candidate.families) :
    Nonempty (ProducedNormalizationCandidateSemanticRun
      familyContext constructorContext env Us candidate rawDecl) := by
  obtain ⟨semantic⟩ := input.exists
  exact ⟨{
    semantic := semantic
    familyTypesProduced := familyTypesProduced
    familiesProduced := familiesProduced }⟩

/-- The complete family-validated semantic input for a produced singleton
candidate.

Only the entry verifier alignment is supplied. The exact singleton family
validation and raw-family insertion derive the post-family verified stage;
constructor positions then supply strict translations and fuel equalities in
that derived stage. No normalized view, post-family `VEnvs.WF`, semantic run,
declaration-WF proof, or generation package is an input. -/
structure StagedNormalizationCandidateSemanticInput
    (familyContext constructorContext : AddInductive.Context)
    (env : VEnv) (Us : List Name)
    {source : InductiveType}
    (candidate : AddInductive.NormalizationCandidate [source])
    (rawDecl : VInductDecl) where
  raw : VInductiveType
  raw_types_eq : rawDecl.types = [raw]
  declaration_uvars_eq : rawDecl.uvars = Us.length
  preFamily : TypeChecker.CandidateSemanticStage familyContext env Us
  family : CandidateFamilyStagedInput familyContext constructorContext env Us
    candidate.families.singleton.familyType raw preFamily
  validation_nparams_eq : family.validation.nparams = rawDecl.nparams
  constructorValidation : AddInductive.ConstructorValidationRun
    source family.validation.stats false
      { candidate.families.singleton.familyType.type.trace.terminalContext with
        env := constructorContext.env }
  constructors : CandidateConstructorStagedListInput family.postFamily
    candidate.families.singleton.constructors raw.ctors
  familyTypesProduced : AddInductive.CandidateFamilyTypeListProduced
    familyContext
    (.cons candidate.families.singleton.familyType .nil)
  familiesProduced : AddInductive.CandidateFamilyListProduced
    constructorContext
    (.cons candidate.families.singleton.familyType .nil)
    candidate.families

/-- The staged owner retains exactly the successful executable constructor
validation that selected its source-indexed constructor list. -/
theorem StagedNormalizationCandidateSemanticInput.constructorValidation_run
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name} {source : InductiveType}
    {candidate : AddInductive.NormalizationCandidate [source]}
    {rawDecl : VInductDecl}
    (input : StagedNormalizationCandidateSemanticInput familyContext
      constructorContext env Us candidate rawDecl) :
    AddInductive.checkConstructors #[source] input.family.validation.stats
        false
        { candidate.families.singleton.familyType.type.trace.terminalContext with
          env := constructorContext.env } = .ok () :=
  input.constructorValidation.run

/-- Project the established semantic-input hierarchy from the consolidated
two-stage owner. This projection remains data-free with respect to checker
semantics: it only rearranges verified stage and translation evidence. -/
def StagedNormalizationCandidateSemanticInput.semanticInput
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name} {source : InductiveType}
    {candidate : AddInductive.NormalizationCandidate [source]}
    {rawDecl : VInductDecl}
    (input : StagedNormalizationCandidateSemanticInput familyContext
      constructorContext env Us candidate rawDecl) :
    NormalizationCandidateSemanticInput env Us candidate rawDecl where
  raw := input.raw
  raw_types_eq := input.raw_types_eq
  uvars_eq := input.declaration_uvars_eq
  family := {
    name_eq := input.family.name_eq
    uvars_eq := input.family.uvars_eq
    type := input.family.type.rootInput
    typeEnv := input.family.typeEnv
    addType := input.family.addInduct.env_add
    constructors := input.constructors.semanticInput }

/-- Interpret a complete produced singleton candidate from its entry stage and
derived family-validation stage. The result stays in `Nonempty`; in particular, this theorem
does not use choice to expose a semantic run as executable data. -/
theorem StagedNormalizationCandidateSemanticInput.exists
    {familyContext constructorContext : AddInductive.Context}
    {env : VEnv} {Us : List Name} {source : InductiveType}
    {candidate : AddInductive.NormalizationCandidate [source]}
    {rawDecl : VInductDecl}
    (input : StagedNormalizationCandidateSemanticInput familyContext
      constructorContext env Us candidate rawDecl) :
    Nonempty (ProducedNormalizationCandidateSemanticRun
      familyContext constructorContext env Us candidate rawDecl) :=
  input.semanticInput.exists_ofProduced input.familyTypesProduced
    input.familiesProduced

/-- Forget executable list provenance and expose the existing normalization
root selected by the automatic semantic hierarchy. -/
def ProducedNormalizationCandidateSemanticRun.root
    (run : ProducedNormalizationCandidateSemanticRun
      familyContext constructorContext env Us candidate rawDecl) :
    NormalizationCandidateRun env Us candidate rawDecl :=
  run.semantic.root

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

/-! ### Arbitrary-block semantic assembly -/

/-- Compositional checker evidence for one source-indexed family in an
arbitrary generation-ready block.  Both the complete raw/view telescope and
its terminal result equality are retained until the Theory boundary. -/
structure NormalizedFamilyRun {source : VInductDecl}
    (generation : BlockGenerationChecked source)
    (family : NormalizedFamily) (env : VEnv) where
  familyTel : TypeChecker.TelDefEqEvidence env source.uvars []
    (family.rawParams source.nparams ++ family.rawIndices source.nparams)
    (generation.block.checked.params ++ family.view.indices)
  familyResult : TypeChecker.DefEqEvidence env source.uvars
    (family.rawParams source.nparams ++
      family.rawIndices source.nparams).reverse
    (family.rawResult source.nparams)
    (.sort generation.validated.resultLevel)
    (.sort (.succ generation.validated.resultLevel))

/-- Interpret one compositional family run as the consumer-neutral Theory
certificate used by block artifact preservation. -/
theorem NormalizedFamilyRun.wf
    (run : NormalizedFamilyRun generation family env) :
    family.WF generation env where
  familyTel := run.familyTel.telDefEq
  familyResult := run.familyResult.isDefEq

/-- Exact source-order ownership of every normalized-family run.  The family
list is an index, so a shorter, reordered, or independently selected proof
inventory cannot inhabit this boundary. -/
inductive NormalizedFamilyRunList {source : VInductDecl}
    (generation : BlockGenerationChecked source) (env : VEnv) :
    List NormalizedFamily → Type where
  | nil : NormalizedFamilyRunList generation env []
  | cons
      (head : NormalizedFamilyRun generation family env)
      (tail : NormalizedFamilyRunList generation env families) :
      NormalizedFamilyRunList generation env (family :: families)

/-- Recover the run at any member of the exact dependent family list. -/
theorem NormalizedFamilyRunList.get :
    (runs : NormalizedFamilyRunList generation env families) →
      ∀ family ∈ families, NormalizedFamilyRun generation family env
  | .nil, _, member => nomatch member
  | .cons head _, _, .head _ => head
  | .cons _ tail, family, .tail _ member => tail.get family member

/-- Analyzer semantics retained at one exact member of the dependent checked
family spine.  Constructor facts use the analyzer's positional
`recursiveAt` list and the complete block-wide family-index inventory. -/
structure CheckedBlockFamilyRun
    {source : VInductDecl} {params : List VExpr}
    {ordinal : Nat} {type : VInductiveType}
    (family : CheckedFamily source params ordinal type)
    (env : VEnv) (resultLevel : VLevel)
    (familyIndices : List (List VExpr)) where
  resultLevelEq : family.resultLevel ≈ resultLevel
  familyOnTel : env.OnTel source.uvars [] (params ++ family.indices)
  constructors : ∀ constructor ∈ family.constructors,
    checkedBlockFieldsWF env source.uvars resultLevel familyIndices
        constructor.fields constructor.recursiveAt params.reverse 0 ∧
      env.SpineWF source.uvars
        (constructor.fields.reverse ++ params.reverse)
        (VExpr.forallN
          (VExpr.liftTelN constructor.fields.length family.indices 0)
          (.sort resultLevel))
        constructor.resultIndices (.sort resultLevel)

/-- Exact dependent analyzer semantics for every checked family in source
order. -/
inductive CheckedBlockFamilyRunList
    {source : VInductDecl} {params : List VExpr}
    (env : VEnv) (resultLevel : VLevel)
    (familyIndices : List (List VExpr)) :
    {ordinal : Nat} → {types : List VInductiveType} →
    CheckedFamilies source params ordinal types → Type where
  | nil : CheckedBlockFamilyRunList env resultLevel familyIndices .nil
  | cons
      (head : CheckedBlockFamilyRun family env resultLevel familyIndices)
      (tail : CheckedBlockFamilyRunList env resultLevel familyIndices
        families) :
      CheckedBlockFamilyRunList env resultLevel familyIndices
        (.cons family families)

/-- Reindex the erased `CheckedBlock.WF` fold onto its exact dependent family
spine. -/
def CheckedBlockFamilyRunList.ofListsWF
    {source : VInductDecl} {params : List VExpr}
    {env : VEnv} {resultLevel : VLevel}
    {familyIndices : List (List VExpr)} :
    {ordinal : Nat} → {types : List VInductiveType} →
    (families : CheckedFamilies source params ordinal types) →
    checkedFamilyListsWF source params env resultLevel familyIndices
      families.resultLevels families.indices families.constructors →
    CheckedBlockFamilyRunList env resultLevel familyIndices families
  | _, _, .nil, _ => .nil
  | _, _, .cons _head tail, familyWF =>
      .cons {
        resultLevelEq := familyWF.1
        familyOnTel := familyWF.2.1
        constructors := familyWF.2.2.1 }
        (CheckedBlockFamilyRunList.ofListsWF tail familyWF.2.2.2)

/-- The exact dependent family semantics owned by one checked block. -/
def CheckedBlock.WF.familyRuns
    {source : VInductDecl} {checked : CheckedBlock source}
    {env : VEnv} {resultLevel : VLevel}
    (wf : checked.WF env resultLevel) :
    CheckedBlockFamilyRunList env resultLevel checked.families.indices
      checked.families :=
  CheckedBlockFamilyRunList.ofListsWF checked.families wf

/-- Compositional checker evidence for one flattened mutual constructor.
The four definitional-equality paths remain executable evidence; analyzer-
owned family identity, recursion, and result-spine facts are retained at the
same exact constructor index. -/
structure NormalizedBlockCtorRun {source : VInductDecl}
    (generation : BlockGenerationChecked source)
    (constructor : NormalizedBlockCtor) (env : VEnv) where
  declaredTel : TypeChecker.TelDefEqEvidence env source.uvars []
    (NormalizedBlockCtor.declaredBinders (source := source) constructor)
    (NormalizedBlockCtor.viewBinders generation constructor)
  declaredResult : TypeChecker.DefEqEvidence env source.uvars
    (NormalizedBlockCtor.declaredBinders
      (source := source) constructor).reverse
    (NormalizedBlockCtor.rawResult (source := source) constructor)
    (NormalizedBlockCtor.resultTarget generation constructor)
    (.sort generation.validated.resultLevel)
  emittedTel : TypeChecker.TelDefEqEvidence env source.uvars []
    (NormalizedBlockCtor.emittedBinders generation constructor)
    (NormalizedBlockCtor.viewBinders generation constructor)
  emittedResult : TypeChecker.DefEqEvidence env source.uvars
    (NormalizedBlockCtor.emittedBinders generation constructor).reverse
    (NormalizedBlockCtor.rawResult (source := source) constructor)
    (NormalizedBlockCtor.resultTarget generation constructor)
    (.sort generation.validated.resultLevel)
  owner : ∃ family ∈ generation.families,
    family.view.ordinal = constructor.owner ∧
      family.raw.name = constructor.familyName ∧
      family.view.indices = constructor.familyIndices
  recursive : ∀ recursive ∈ constructor.ctor.view.recursive,
    ∃ family ∈ generation.families,
      family.view.ordinal = recursive.targetType ∧
        (∃ B,
          constructor.ctor.view.fields[recursive.fieldIndex]? = some B ∧
            B = VExpr.forallN recursive.binders
              (VExpr.appN
                (.const family.raw.name (VLevel.params source.uvars))
                (VExpr.bvarRevRange
                    (recursive.fieldIndex + recursive.binders.length)
                    source.nparams ++ recursive.indices))) ∧
        recursive.WF source.uvars env generation.validated.resultLevel
          family.view.indices
          ((constructor.ctor.view.fields.take recursive.fieldIndex).reverse ++
            generation.block.checked.params.reverse)
  resultSpine :
    env.SpineWF source.uvars
      (constructor.ctor.view.fields.reverse ++
        generation.block.checked.params.reverse)
      (VExpr.forallN
        (VExpr.liftTelN constructor.ctor.view.fields.length
          constructor.familyIndices 0)
        (.sort generation.validated.resultLevel))
      constructor.ctor.view.resultIndices
      (.sort generation.validated.resultLevel)

/-- Interpret one compositional flattened-constructor run as its Theory
certificate. -/
theorem NormalizedBlockCtorRun.wf
    (run : NormalizedBlockCtorRun generation constructor env) :
    NormalizedBlockCtor.WF generation constructor env where
  declaredTel := run.declaredTel.telDefEq
  declaredResult := run.declaredResult.isDefEq
  emittedTel := run.emittedTel.telDefEq
  emittedResult := run.emittedResult.isDefEq
  owner := run.owner
  recursive := run.recursive
  resultSpine := run.resultSpine

/-- Exact flattened source order for every mutual-constructor run.  Its list
index is definitionally the generation inventory consumed by block artifact
preservation. -/
inductive NormalizedBlockCtorRunList {source : VInductDecl}
    (generation : BlockGenerationChecked source) (env : VEnv) :
    List NormalizedBlockCtor → Type where
  | nil : NormalizedBlockCtorRunList generation env []
  | cons
      (head : NormalizedBlockCtorRun generation constructor env)
      (tail : NormalizedBlockCtorRunList generation env constructors) :
      NormalizedBlockCtorRunList generation env
        (constructor :: constructors)

/-- Recover the run at any member of the exact flattened constructor list. -/
theorem NormalizedBlockCtorRunList.get :
    (runs : NormalizedBlockCtorRunList generation env constructors) →
      ∀ constructor ∈ constructors,
        NormalizedBlockCtorRun generation constructor env
  | .nil, _, member => nomatch member
  | .cons head _, _, .head _ => head
  | .cons _ tail, constructor, .tail _ member =>
      tail.get constructor member

/-- Complete Verify-side semantic assembler for one arbitrary generation-
ready block.  The normalization stage, analyzer certificate, family runs, and
flattened constructor runs all share the exact dependent generation value;
no fixture-selected positional list is accepted by this boundary. -/
structure BlockGenerationRun {source : VInductDecl}
    (generation : BlockGenerationChecked source)
    (env blockEnv : VEnv) where
  normalization : NormalizationBlockRun generation.block.normalization
    env blockEnv
  checked : generation.block.checked.WF env
    generation.validated.resultLevel
  resultLevelWF : generation.validated.resultLevel.WF source.uvars
  paramsTel : TypeChecker.TelDefEqEvidence env source.uvars []
    generation.block.rawParams generation.block.checked.params
  families : NormalizedFamilyRunList generation env generation.families
  constructors : NormalizedBlockCtorRunList generation blockEnv
    generation.flatCtors

/-- Assemble the complete consumer-neutral mutual-generation certificate
from exact checker-owned block evidence. -/
theorem BlockGenerationRun.wf
    (run : BlockGenerationRun generation env blockEnv) :
    generation.WF env blockEnv where
  blockWF := ⟨run.normalization.wf, run.checked⟩
  resultLevelWF := run.resultLevelWF
  paramsTel := run.paramsTel.telDefEq
  families := fun family member => (run.families.get family member).wf
  constructors := fun constructor member =>
    (run.constructors.get constructor member).wf

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
  rawResult : VExpr.dropN
      candidate.families.singleton.familyType.type.trace.spineLength
      normalization.raw.type = generation.block.rawResult
  viewResult : VExpr.dropN
      candidate.families.singleton.familyType.type.trace.spineLength
      normalization.family.viewType =
    .sort generation.block.checked.resultLevel

/-- Extract the complete family telescope/result certificate at the exact
components consumed by `GenerationRun`. -/
theorem CandidateFamilyGenerationRun.evidence
    {env : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    {normalization : NormalizationCandidateRun env Us candidate source}
    {generation : GenerationChecked source}
    (run : CandidateFamilyGenerationRun normalization generation)
    (viewType_eq : normalization.family.viewType =
      generation.block.checked.type.type) :
    TypeChecker.TelResultDefEqEvidence env Us.length []
      (generation.block.rawParams ++ generation.block.rawIndices)
      (generation.block.checked.params ++ generation.block.checked.indices)
      generation.block.rawResult
      (.sort generation.block.checked.resultLevel)
      (.sort (.succ generation.block.checked.resultLevel)) :=
  run.spine.evidenceAt run.rawTel (by
    rw [viewType_eq, generation.block.checked.type_eq,
      ← VExpr.forallN_append]
    apply TypeChecker.candidateTelN_of_dropN_terminal (B :=
      .sort generation.block.checked.resultLevel) trivial
    simpa only [viewType_eq, generation.block.checked.type_eq,
      ← VExpr.forallN_append] using run.viewResult)
    run.rawResult run.viewResult (by
      apply VEnv.HasType.sort
      simpa only [← generation.block.uvars_eq,
        normalization.uvars_eq] using
        generation.block.checked.direct_anatomy.2.2.1)

/-- Family generation alignment whose spine is projected directly from the
retained semantic hierarchy.  Callers provide only the executable structural
gate and the component equations required by `GenerationChecked`; they cannot
substitute a second recursive run or a different normalized view. -/
structure CandidateFamilySemanticGenerationRun
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    (normalization : NormalizationCandidateSemanticRun env Us candidate source)
    (generation : GenerationChecked source) where
  storedSpine :
    candidate.families.singleton.familyType.type.trace.storedSpine = true
  rawTel : VExpr.telN
      candidate.families.singleton.familyType.type.trace.spineLength
      normalization.raw.type =
    generation.block.rawParams ++ generation.block.rawIndices
  rawResult : VExpr.dropN
      candidate.families.singleton.familyType.type.trace.spineLength
      normalization.raw.type = generation.block.rawResult
  viewResult : VExpr.dropN
      candidate.families.singleton.familyType.type.trace.spineLength
      normalization.family.type.view =
    .sort generation.block.checked.resultLevel

/-- Minimal structural input for family generation.  The retained semantic
root already owns the recursive checker run, while dependent analysis fixes
the raw and checked components.  A caller therefore supplies only the
executable stored-spine gate and the total number of binders traversed by that
spine; all telescope and terminal equations are derived below. -/
structure CandidateFamilySemanticGenerationShape
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    (normalization : NormalizationCandidateSemanticRun env Us candidate source)
    (generation : GenerationChecked source) where
  storedSpine :
    candidate.families.singleton.familyType.type.trace.storedSpine = true
  spineLength_eq :
    candidate.families.singleton.familyType.type.trace.spineLength =
      (generation.block.rawParams ++ generation.block.rawIndices).length

/-- Recover the existing family-generation run from the single retained
semantic owner. -/
theorem CandidateFamilySemanticGenerationRun.run
    (run : CandidateFamilySemanticGenerationRun normalization generation) :
    CandidateFamilyGenerationRun normalization.root generation where
  spine := normalization.family.type.spine run.storedSpine
  rawTel := run.rawTel
  rawResult := run.rawResult
  viewResult := run.viewResult

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
  rawResult : VExpr.dropN candidate.type.trace.spineLength raw.type =
    ctor.rawResult source.nparams
  viewResult : VExpr.dropN candidate.type.trace.spineLength root.viewType =
    ctor.resultTarget block

/-- Constructor generation alignment owned by the same retained semantic root
used for normalization.  The only spine premise is the Boolean structural gate
computed by the candidate trace; the recursive semantic run and view are
projected from `root`. -/
structure CandidateSemanticNormalizedCtorRun {source : VInductDecl}
    (block : NormalizedChecked source) (env : VEnv) (Us : List Name)
    {kernelSource : Constructor}
    {candidate : AddInductive.CandidateConstructor kernelSource}
    {raw : VConstVal}
    (root : CandidateConstructorSemanticRun env Us candidate raw)
    (ctor : NormalizedCtor) where
  raw_eq : ctor.raw = raw
  view_eq : ctor.view.value = root.root.view
  storedSpine : candidate.type.trace.storedSpine = true
  rawTel : VExpr.telN candidate.type.trace.spineLength raw.type =
    ctor.declaredBinders source.nparams
  rawResult : VExpr.dropN candidate.type.trace.spineLength raw.type =
    ctor.rawResult source.nparams
  viewResult : VExpr.dropN candidate.type.trace.spineLength root.type.view =
    ctor.resultTarget block

/-- Minimal structural input for one retained constructor root.  It is
independent of a caller-selected normalized pair: positional raw/view pairing
is recovered from the successful dependent analysis, and the full component
equations follow from this total stored-binder count. -/
structure CandidateConstructorSemanticGenerationShape
    {source : VInductDecl} (env : VEnv) (Us : List Name)
    {kernelSource : Constructor}
    {candidate : AddInductive.CandidateConstructor kernelSource}
    {raw : VConstVal}
    (root : CandidateConstructorSemanticRun env Us candidate raw) where
  storedSpine : candidate.type.trace.storedSpine = true
  spineLength_eq : candidate.type.trace.spineLength =
    (VExpr.telN source.nparams raw.type ++
      ctorFields (VExpr.dropN source.nparams raw.type)).length

/-- Project the compatibility constructor run without rebuilding or choosing
semantic evidence. -/
theorem CandidateSemanticNormalizedCtorRun.run
    (run : CandidateSemanticNormalizedCtorRun block env Us root ctor) :
    CandidateNormalizedCtorRun block env Us root.root ctor where
  raw_eq := run.raw_eq
  view_eq := run.view_eq
  spine := root.type.spine run.storedSpine
  rawTel := run.rawTel
  rawResult := run.rawResult
  viewResult := run.viewResult

/-- The terminal alignment and the analyzer's exact constructor shape force
the candidate trace to expose the entire checked binder telescope. -/
theorem CandidateNormalizedCtorRun.viewTel_eq
    {source : VInductDecl} {generation : GenerationChecked source}
    {env : VEnv} {Us : List Name}
    {kernelSource : Constructor}
    {candidate : AddInductive.CandidateConstructor kernelSource}
    {raw : VConstVal}
    {root : CandidateConstructorRun env Us candidate raw}
    {ctor : NormalizedCtor}
    (run : CandidateNormalizedCtorRun generation.block env Us root ctor)
    (hctor : ctor ∈ generation.block.ctorPairs) :
    VExpr.telN candidate.type.trace.spineLength root.viewType =
      ctor.viewBinders generation.block := by
  have viewType_eq : root.viewType = ctor.view.value.type := by
    simpa only [CandidateConstructorRun.view] using
      (congrArg (fun value : VConstVal => value.type) run.view_eq).symm
  have hterminal :
      TypeChecker.CandidateTerminal (ctor.resultTarget generation.block) := by
    exact TypeChecker.candidateTerminal_appN_const _ _ _
  rw [viewType_eq, generation.viewCtorType_eq hctor]
  apply TypeChecker.candidateTelN_of_dropN_terminal hterminal
  simpa only [viewType_eq, generation.viewCtorType_eq hctor] using
    run.viewResult

/-- Extract the stored constructor's declared telescope/result evidence. -/
theorem CandidateNormalizedCtorRun.declaredEvidence
    {source : VInductDecl} {generation : GenerationChecked source}
    {env : VEnv} {Us : List Name}
    {kernelSource : Constructor}
    {candidate : AddInductive.CandidateConstructor kernelSource}
    {raw : VConstVal}
    {root : CandidateConstructorRun env Us candidate raw}
    {ctor : NormalizedCtor}
    (run : CandidateNormalizedCtorRun generation.block env Us root ctor)
    (hctor : ctor ∈ generation.block.ctorPairs)
    (rightType : env.HasType Us.length
      (ctor.declaredBinders source.nparams).reverse
      (ctor.resultTarget generation.block)
      (.sort generation.block.checked.resultLevel)) :
    TypeChecker.TelResultDefEqEvidence env Us.length []
      (ctor.declaredBinders source.nparams)
      (ctor.viewBinders generation.block)
      (ctor.rawResult source.nparams) (ctor.resultTarget generation.block)
      (.sort generation.block.checked.resultLevel) := by
  apply run.spine.evidenceAt run.rawTel (run.viewTel_eq hctor)
    run.rawResult run.viewResult rightType

/-- The checked result spine and the candidate-certified binder telescope
determine a constructor's terminal typing judgment.  The family constant is
typed once for the whole block; individual constructor fixtures supply no
additional semantic result oracle. -/
theorem CandidateNormalizedCtorRun.rightType_ofChecked
    {source : VInductDecl} {generation : GenerationChecked source}
    {env : VEnv} {Us : List Name}
    {kernelSource : Constructor}
    {candidate : AddInductive.CandidateConstructor kernelSource}
    {raw : VConstVal}
    {root : CandidateConstructorRun env Us candidate raw}
    {ctor : NormalizedCtor}
    (run : CandidateNormalizedCtorRun generation.block env Us root ctor)
    (henv : VEnv.WF env) (uvars_eq : source.uvars = Us.length)
    (checked : generation.block.checked.WF env)
    (familyConst : env.HasType source.uvars []
      (.const generation.block.sourceType.name
        (VLevel.params source.uvars))
      generation.block.checked.type.type)
    (hctor : ctor ∈ generation.block.ctorPairs) :
    env.HasType Us.length
      (ctor.declaredBinders source.nparams).reverse
      (ctor.resultTarget generation.block)
      (.sort generation.block.checked.resultLevel) := by
  obtain ⟨_, evidence⟩ := run.spine.evidence
  have telescope : TypeChecker.TelDefEqEvidence env Us.length []
      (ctor.declaredBinders source.nparams)
      (ctor.viewBinders generation.block) := by
    simpa only [run.rawTel, run.viewTel_eq hctor] using evidence.telescope
  have hview := generation.checkedResultTarget_hasType
    henv.ordered checked familyConst hctor
  have hview' : env.HasType Us.length
      (ctor.viewBinders generation.block).reverse
      (ctor.resultTarget generation.block)
      (.sort generation.block.checked.resultLevel) := by
    simpa only [uvars_eq] using hview
  have hctx : env.IsDefEqCtx Us.length []
      (ctor.declaredBinders source.nparams).reverse
      (ctor.viewBinders generation.block).reverse := by
    simpa using telescope.telDefEq.ctx
  exact hview'.defeqDFC henv.ordered (hctx.symm henv.ordered)

/-- Produce both constructor paths required by `NormalizedCtorRun`.

The declared path comes directly from the constructor candidate. The emitted
path replaces the stored constructor parameter prefix by the checked family
parameter prefix used by Lean's recursor generator, transporting fields and
result through the induced definitionally equal context. -/
theorem CandidateNormalizedCtorRun.normalizedCtorRun
    {source : VInductDecl} {generation : GenerationChecked source}
    {env : VEnv} {Us : List Name}
    {kernelSource : Constructor}
    {candidate : AddInductive.CandidateConstructor kernelSource}
    {raw : VConstVal}
    {root : CandidateConstructorRun env Us candidate raw}
    {ctor : NormalizedCtor}
    (run : CandidateNormalizedCtorRun generation.block env Us root ctor)
    (henv : VEnv.WF env) (uvars_eq : source.uvars = Us.length)
    (familyParams : TypeChecker.TelDefEqEvidence env Us.length []
      generation.block.rawParams generation.block.checked.params)
    (prefixLength :
      (VExpr.telN source.nparams ctor.raw.type).length =
        generation.block.checked.params.length)
    (hctor : ctor ∈ generation.block.ctorPairs)
    (rightType : env.HasType Us.length
      (ctor.declaredBinders source.nparams).reverse
      (ctor.resultTarget generation.block)
      (.sort generation.block.checked.resultLevel)) :
    NormalizedCtorRun generation.block ctor env := by
  have declared := run.declaredEvidence hctor rightType
  have declaredSplit : TypeChecker.TelResultDefEqEvidence env Us.length []
      (VExpr.telN source.nparams ctor.raw.type ++
        ctor.rawFields source.nparams)
      (generation.block.checked.params ++ ctor.view.fields)
      (ctor.rawResult source.nparams) (ctor.resultTarget generation.block)
      (.sort generation.block.checked.resultLevel) := by
    simpa only [NormalizedCtor.declaredBinders,
      NormalizedCtor.viewBinders] using declared
  have checkedParams : TypeChecker.TelDefEqEvidence env Us.length []
      generation.block.checked.params generation.block.checked.params :=
    .ofTelDefEq <| (familyParams.telDefEq.view_onTel henv.ordered).telDefEq_refl
  have emitted := declaredSplit.replacePrefix henv checkedParams prefixLength
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

/-- Dependent positional generation alignment over the retained constructor
semantic list.  Its projection below is definitionally tied to
`roots.roots`, so source order and the exact normalization views cannot drift
between phases. -/
inductive CandidateSemanticNormalizedCtorListRun {source : VInductDecl}
    (block : NormalizedChecked source) (env : VEnv) (Us : List Name) :
    {kernelSources : List Constructor} →
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor kernelSources} →
    {raws : List VConstVal} →
    (roots : CandidateConstructorSemanticListRun env Us candidates raws) →
    List NormalizedCtor → Type where
  | nil : CandidateSemanticNormalizedCtorListRun block env Us .nil []
  | cons
      (head : CandidateSemanticNormalizedCtorRun block env Us root ctor)
      (tail : CandidateSemanticNormalizedCtorListRun block env Us roots ctors) :
      CandidateSemanticNormalizedCtorListRun block env Us
        (.cons root roots) (ctor :: ctors)

/-- Source-indexed structural generation inputs for every retained semantic
constructor root.  No normalized constructor list occurs in this type, so a
caller cannot choose, reorder, truncate, or duplicate the analyzer's pairs. -/
inductive CandidateConstructorSemanticGenerationShapeList
    (source : VInductDecl) (env : VEnv) (Us : List Name) :
    {kernelSources : List Constructor} →
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor kernelSources} →
    {raws : List VConstVal} →
    (roots : CandidateConstructorSemanticListRun env Us candidates raws) →
    Type where
  | nil : CandidateConstructorSemanticGenerationShapeList source env Us .nil
  | cons
      (head : CandidateConstructorSemanticGenerationShape
        (source := source) env Us root)
      (tail : CandidateConstructorSemanticGenerationShapeList
        source env Us roots) :
      CandidateConstructorSemanticGenerationShapeList source env Us
        (.cons root roots)

/-- Executable generation-layout check for a complete source-indexed
constructor candidate list.

The check is intentionally stated against the raw Theory constants retained
by the semantic hierarchy.  It accepts exactly when every candidate WHNF trace
preserves the stored main Pi spine and traverses the complete raw constructor
telescope.  List-length mismatches are rejected explicitly; no `zip` or
positional lookup can silently truncate either side. -/
def candidateConstructorSemanticGenerationShape
    (source : VInductDecl) :
    {kernelSources : List Constructor} →
    AddInductive.CandidateList AddInductive.CandidateConstructor
      kernelSources →
    List VConstVal → Bool
  | _, .nil, [] => true
  | _, .nil, _ :: _ => false
  | _, .cons _ _, [] => false
  | _, .cons candidate candidates, raw :: raws =>
    candidate.type.trace.storedSpine &&
      candidate.type.trace.spineLength ==
        (VExpr.telN source.nparams raw.type ++
          ctorFields (VExpr.dropN source.nparams raw.type)).length &&
      candidateConstructorSemanticGenerationShape source candidates raws

/-- Executable generation-layout check for a complete singleton
normalization candidate and its raw Theory family.

This definition is independent of semantic proofs.  It checks only the
source-indexed candidate traces against the raw family/constructor telescope
layout that generation would emit.  Verify's retained semantic hierarchy
later reindexes the same Boolean onto its exact raw family. -/
def normalizationCandidateGenerationShape
    {kernelSource : InductiveType}
    (source : VInductDecl) (raw : VInductiveType)
    (candidate : AddInductive.NormalizationCandidate [kernelSource]) : Bool :=
  let familyTrace :=
    candidate.families.singleton.familyType.type.trace
  (familyTrace.storedSpine &&
      familyTrace.spineLength ==
        (VExpr.telN source.nparams raw.type ++
          ctorFields (VExpr.dropN source.nparams raw.type)).length) &&
    candidateConstructorSemanticGenerationShape source
      candidate.families.singleton.constructors raw.ctors

/-- Executable generation-layout check for every family in a source-indexed
normalization candidate.

The family and constructor lists are traversed dependently and the raw Theory
families are consumed in lockstep.  Thus a short raw block, an extra raw
family, or a constructor-list length mismatch is rejected explicitly.  As in
the singleton gate above, this computation checks only the stored-spine
layout; semantic translation and header alignment remain the responsibility
of the retained block semantic hierarchy. -/
def candidateBlockFamilySemanticGenerationShape
    (source : VInductDecl) :
    {kernelSources : List InductiveType} →
    AddInductive.CandidateList AddInductive.CandidateFamily kernelSources →
    List VInductiveType → Bool
  | _, .nil, [] => true
  | _, .nil, _ :: _ => false
  | _, .cons _ _, [] => false
  | _, .cons candidate candidates, raw :: raws =>
    let familyTrace := candidate.familyType.type.trace
    familyTrace.storedSpine &&
      familyTrace.spineLength ==
        (VExpr.telN source.nparams raw.type ++
          ctorFields (VExpr.dropN source.nparams raw.type)).length &&
      candidateConstructorSemanticGenerationShape source
        candidate.constructors raw.ctors &&
      candidateBlockFamilySemanticGenerationShape source candidates raws

/-- One total structural gate for an arbitrary singleton or mutual
normalization candidate.

Unlike `normalizationCandidateGenerationShape`, no singleton projection or
caller-selected raw family occurs in this API: the candidate and the complete
raw Theory block are traversed in source order. -/
def normalizationCandidateBlockGenerationShape
    {kernelSources : List InductiveType}
    (source : VInductDecl)
    (candidate : AddInductive.NormalizationCandidate kernelSources) : Bool :=
  candidateBlockFamilySemanticGenerationShape source candidate.families
    source.types

/-- Complete generation-spine evidence determines the executable constructor
shape check directly from the retained pre-run semantic inputs. -/
theorem CandidateConstructorSemanticListInput.generationShape_of_generationSpines
    {source : VInductDecl} {env : VEnv} {Us : List Name}
    {kernelSources : List Constructor}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor kernelSources}
    {raws : List VConstVal} :
    (roots : CandidateConstructorSemanticListInput env Us candidates raws) →
      AddInductive.CandidateConstructorGenerationSpineList candidates →
        candidateConstructorSemanticGenerationShape source candidates raws =
          true
  | .nil, .nil => rfl
  | .cons head tail, .cons generation generations => by
      simp only [candidateConstructorSemanticGenerationShape,
        Bool.and_eq_true, beq_iff_eq]
      exact ⟨⟨
          AddInductive.CandidateExprTrace.generationSpine_storedSpine _
            generation,
          head.type.generationSpineLengthAt generation source.nparams⟩,
        tail.generationShape_of_generationSpines generations⟩

/-- Complete family and constructor generation-spine evidence determines the
block shape check directly from the exact pre-run family hierarchy. -/
theorem CandidateBlockFamilySemanticListInput.generationShape_of_generationSpines
    {source : VInductDecl} {env blockEnv : VEnv} {Us : List Name}
    {kernelSources : List InductiveType}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateFamily kernelSources}
    {raws : List VInductiveType} :
    (roots : CandidateBlockFamilySemanticListInput env blockEnv Us candidates
      raws) →
      AddInductive.CandidateFamilyGenerationSpineList candidates →
        candidateBlockFamilySemanticGenerationShape source candidates raws =
          true
  | .nil, .nil => rfl
  | .cons head tail, .cons family constructors families => by
      simp only [candidateBlockFamilySemanticGenerationShape,
        Bool.and_eq_true, beq_iff_eq]
      exact ⟨⟨⟨
            AddInductive.CandidateExprTrace.generationSpine_storedSpine _
              family,
            head.type.generationSpineLengthAt family source.nparams⟩,
          head.constructors.generationShape_of_generationSpines constructors⟩,
        tail.generationShape_of_generationSpines families⟩

/-- The accepted producer's structural spine certificate discharges the
complete block shape check without constructing any semantic run. -/
theorem NormalizationCandidateBlockSemanticInput.generationShape_of_generationSpines
    {env blockEnv : VEnv} {Us : List Name}
    {kernelSources : List InductiveType} {rawDecl : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate kernelSources}
    (input : NormalizationCandidateBlockSemanticInput env blockEnv Us
      candidate rawDecl)
    (spines : AddInductive.CandidateFamilyGenerationSpineList
      candidate.families) :
    normalizationCandidateBlockGenerationShape rawDecl candidate = true := by
  exact input.families.generationShape_of_generationSpines spines

/--
info: 'Lean4Lean.VInductDecl.NormalizationCandidateBlockSemanticInput.generationShape_of_generationSpines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.eqv_eq,
 Expr.instantiate1_eq,
 Level.instLawfulBEqLevel,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms NormalizationCandidateBlockSemanticInput.generationShape_of_generationSpines

/-- Complete generation-spine evidence determines the executable shape check
for every constructor retained by the exact semantic hierarchy. -/
theorem CandidateConstructorSemanticListRun.generationShape_of_generationSpines
    {source : VInductDecl} {env : VEnv} {Us : List Name}
    {kernelSources : List Constructor}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor kernelSources}
    {raws : List VConstVal} :
    (roots : CandidateConstructorSemanticListRun env Us candidates raws) →
      AddInductive.CandidateConstructorGenerationSpineList candidates →
        candidateConstructorSemanticGenerationShape source candidates raws =
          true
  | .nil, .nil => rfl
  | .cons head tail, .cons generation generations => by
      obtain ⟨_, semantic⟩ := head.type.recursive
      simp only [candidateConstructorSemanticGenerationShape,
        Bool.and_eq_true, beq_iff_eq]
      exact ⟨⟨
          AddInductive.CandidateExprTrace.generationSpine_storedSpine _
            generation,
          semantic.generationSpineLengthAt generation source.nparams⟩,
        tail.generationShape_of_generationSpines generations⟩

/-- Complete family and constructor generation-spine evidence determines the
executable shape check for the exact raw block owned by semantic staging. -/
theorem CandidateBlockFamilySemanticListRun.generationShape_of_generationSpines
    {source : VInductDecl} {env blockEnv : VEnv} {Us : List Name}
    {kernelSources : List InductiveType}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateFamily kernelSources}
    {raws : List VInductiveType} :
    (roots : CandidateBlockFamilySemanticListRun env blockEnv Us candidates
      raws) →
      AddInductive.CandidateFamilyGenerationSpineList candidates →
        candidateBlockFamilySemanticGenerationShape source candidates raws =
          true
  | .nil, .nil => rfl
  | .cons head tail, .cons family constructors families => by
      obtain ⟨_, semantic⟩ := head.type.recursive
      simp only [candidateBlockFamilySemanticGenerationShape,
        Bool.and_eq_true, beq_iff_eq]
      exact ⟨⟨⟨
            AddInductive.CandidateExprTrace.generationSpine_storedSpine _
              family,
            semantic.generationSpineLengthAt family source.nparams⟩,
          head.constructors.generationShape_of_generationSpines constructors⟩,
        tail.generationShape_of_generationSpines families⟩

/-- The structural gate retained by the accepted normalization producer
discharges the complete executable generation-shape check on its exact
semantic raw block. -/
theorem NormalizationCandidateBlockSemanticRun.generationShape_of_generationSpines
    {env blockEnv : VEnv} {Us : List Name}
    {kernelSources : List InductiveType} {rawDecl : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate kernelSources}
    (normalization : NormalizationCandidateBlockSemanticRun env blockEnv Us
      candidate rawDecl)
    (spines : AddInductive.CandidateFamilyGenerationSpineList
      candidate.families) :
    normalizationCandidateBlockGenerationShape rawDecl candidate = true := by
  exact normalization.families.generationShape_of_generationSpines spines

/-- Per-family structural generation evidence projected from the block gate.
The constructor evidence remains indexed by the exact semantic roots owned by
that family. -/
structure CandidateBlockFamilySemanticGenerationShape
    (source : VInductDecl) (env blockEnv : VEnv) (Us : List Name)
    {kernelSource : InductiveType}
    {candidate : AddInductive.CandidateFamily kernelSource}
    {raw : VInductiveType}
    (root : CandidateBlockFamilySemanticRun env blockEnv Us candidate raw)
    where
  storedSpine : candidate.familyType.type.trace.storedSpine = true
  spineLength_eq : candidate.familyType.type.trace.spineLength =
    (VExpr.telN source.nparams raw.type ++
      ctorFields (VExpr.dropN source.nparams raw.type)).length
  constructors : CandidateConstructorSemanticGenerationShapeList source
    blockEnv Us root.constructors

/-- The family component of the block gate covers the complete raw Pi
telescope, independently of the analyzer's parameter/index split. -/
theorem CandidateBlockFamilySemanticGenerationShape.spineLength_eq_ctorFields
    {kernelSource : InductiveType}
    {candidate : AddInductive.CandidateFamily kernelSource}
    {raw : VInductiveType}
    {root : CandidateBlockFamilySemanticRun env blockEnv Us candidate raw}
    (shape : CandidateBlockFamilySemanticGenerationShape source env blockEnv
      Us root) :
    candidate.familyType.type.trace.spineLength =
      (ctorFields raw.type).length := by
  rw [shape.spineLength_eq]
  exact congrArg List.length
    (TypeChecker.candidateCtorFields_split source.nparams raw.type).symm

/-- Generic annotation-consumed telescope ownership for one exact semantic
family position.

The source-indexed semantic root fixes the raw Theory family and recursive
checker run, while the matching generation-shape witness proves that the
stored candidate spine covers the complete raw Pi telescope.  This package is
independent of the family's ordinal position and can therefore be threaded by
the later-family validation cursor. -/
structure CandidateBlockFamilyAnnotationSpine
    (source : VInductDecl) (env blockEnv : VEnv) (Us : List Name)
    {kernelSource : InductiveType}
    {candidate : AddInductive.CandidateFamily kernelSource}
    {raw : VInductiveType}
    (root : CandidateBlockFamilySemanticRun env blockEnv Us candidate raw)
    (shape : CandidateBlockFamilySemanticGenerationShape source env blockEnv
      Us root) where
  validation_annotations :
    candidate.familyType.type.trace.validationAnnotations
  storedBinders : List VExpr
  telescope : TypeChecker.TelDefEqEvidence env Us.length []
    (VExpr.telN (ctorFields raw.type).length raw.type) storedBinders
  stored_length : storedBinders.length = (ctorFields raw.type).length
  terminalRun : TypeChecker.CandidateContextRun
    candidate.familyType.type.trace.terminalContext
  terminal_venv : terminalRun.context.venv = env
  terminal_lparams : terminalRun.context.lparams = Us
  terminal_vlctx : terminalRun.context.vlctx.toCtx = storedBinders.reverse
  inferred : VExpr
  recursive : TypeChecker.CandidateExprRun env Us
    candidate.familyType.type.trace [] raw.type root.type.view inferred
  annotation_spine : TypeChecker.CandidateAnnotationSpine env Us
    candidate.familyType.type.trace [] terminalRun.context.vlctx
      storedBinders

/-- Construct the generic annotation owner directly from a semantic family,
its exact generation-shape position, and the validator-produced annotation
provenance for that candidate. -/
theorem CandidateBlockFamilyAnnotationSpine.exists
    {source : VInductDecl} {env blockEnv : VEnv} {Us : List Name}
    {kernelSource : InductiveType}
    {candidate : AddInductive.CandidateFamily kernelSource}
    {raw : VInductiveType}
    (root : CandidateBlockFamilySemanticRun env blockEnv Us candidate raw)
    (shape : CandidateBlockFamilySemanticGenerationShape source env blockEnv
      Us root)
    (validationAnnotations :
      candidate.familyType.type.trace.validationAnnotations) :
    Nonempty (CandidateBlockFamilyAnnotationSpine source env blockEnv Us root
      shape) := by
  obtain ⟨inferred, recursive⟩ := root.type.recursive
  obtain ⟨terminalRun, storedBinders, terminalVenv, terminalLparams,
      telescope, storedLength, terminalVlctx, annotationSpine⟩ :=
    root.type.annotationSpineContext shape.storedSpine
  have spineLength := shape.spineLength_eq_ctorFields
  rw [spineLength] at telescope storedLength
  exact ⟨{
    validation_annotations := validationAnnotations
    storedBinders := storedBinders
    telescope := telescope
    stored_length := storedLength
    terminalRun := terminalRun
    terminal_venv := terminalVenv
    terminal_lparams := terminalLparams
    terminal_vlctx := terminalVlctx
    inferred := inferred
    recursive := recursive
    annotation_spine := annotationSpine }⟩

/-- Exact source-order structural generation evidence for every family in a
retained mutual semantic hierarchy. -/
inductive CandidateBlockFamilySemanticGenerationShapeList
    (source : VInductDecl) (env blockEnv : VEnv) (Us : List Name) :
    {kernelSources : List InductiveType} →
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateFamily kernelSources} →
    {raws : List VInductiveType} →
    (roots : CandidateBlockFamilySemanticListRun env blockEnv Us
      candidates raws) → Type where
  | nil : CandidateBlockFamilySemanticGenerationShapeList source env
      blockEnv Us .nil
  | cons
      (head : CandidateBlockFamilySemanticGenerationShape source env
        blockEnv Us root)
      (tail : CandidateBlockFamilySemanticGenerationShapeList source env
        blockEnv Us roots) :
      CandidateBlockFamilySemanticGenerationShapeList source env blockEnv Us
        (.cons root roots)

/-- Structural generation evidence at the canonical semantic head of a
nonempty source-indexed list. -/
def CandidateBlockFamilySemanticGenerationShapeList.head
    {kernelSource : InductiveType}
    {remainingSources : List InductiveType}
    {candidates : AddInductive.CandidateList AddInductive.CandidateFamily
      (kernelSource :: remainingSources)}
    {raws : List VInductiveType}
    {roots : CandidateBlockFamilySemanticListRun env blockEnv Us candidates
      raws}
    (shapes : CandidateBlockFamilySemanticGenerationShapeList source env
      blockEnv Us roots) :
    CandidateBlockFamilySemanticGenerationShape source env blockEnv Us
      roots.headPosition.semantic := by
  cases roots with
  | cons root roots =>
    cases shapes with
    | cons shape shapes => exact shape

/-- Structural generation evidence after the canonical semantic head. -/
def CandidateBlockFamilySemanticGenerationShapeList.tail
    {kernelSource : InductiveType}
    {remainingSources : List InductiveType}
    {candidates : AddInductive.CandidateList AddInductive.CandidateFamily
      (kernelSource :: remainingSources)}
    {raws : List VInductiveType}
    {roots : CandidateBlockFamilySemanticListRun env blockEnv Us candidates
      raws}
    (shapes : CandidateBlockFamilySemanticGenerationShapeList source env
      blockEnv Us roots) :
    CandidateBlockFamilySemanticGenerationShapeList source env blockEnv Us
      roots.headPosition.tail := by
  cases roots with
  | cons root roots =>
    cases shapes with
    | cons shape shapes => exact shapes

/-- Projection-friendly structural-shape tail aligned with the exact raw-list
tail. -/
def CandidateBlockFamilySemanticGenerationShapeList.tailExact
    {kernelSource : InductiveType}
    {remainingSources : List InductiveType}
    {candidates : AddInductive.CandidateList AddInductive.CandidateFamily
      (kernelSource :: remainingSources)}
    {raws : List VInductiveType}
    {roots : CandidateBlockFamilySemanticListRun env blockEnv Us candidates
      raws}
    (shapes : CandidateBlockFamilySemanticGenerationShapeList source env
      blockEnv Us roots) :
    CandidateBlockFamilySemanticGenerationShapeList source env blockEnv Us
      roots.tailExact := by
  cases candidates with
  | cons candidate candidates =>
      cases raws with
      | nil => cases roots
      | cons raw raws =>
          cases roots with
          | cons root roots =>
              cases shapes with
              | cons shape shapes => exact shapes

/-- Exact source-order annotation ownership for every semantic family in a
generation-shape spine. -/
inductive CandidateBlockFamilyAnnotationSpineList
    (source : VInductDecl) (env blockEnv : VEnv) (Us : List Name) :
    {kernelSources : List InductiveType} →
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateFamily kernelSources} →
    {raws : List VInductiveType} →
    (roots : CandidateBlockFamilySemanticListRun env blockEnv Us
      candidates raws) →
    CandidateBlockFamilySemanticGenerationShapeList source env blockEnv Us
      roots → Type where
  | nil : CandidateBlockFamilyAnnotationSpineList source env blockEnv Us
      .nil .nil
  | cons
      (head : CandidateBlockFamilyAnnotationSpine source env blockEnv Us
        root shape)
      (tail : CandidateBlockFamilyAnnotationSpineList source env blockEnv Us
        roots shapes) :
      CandidateBlockFamilyAnnotationSpineList source env blockEnv Us
        (.cons root roots) (.cons shape shapes)

/-- Generic annotation owner at the head of a nonempty source-order spine. -/
def CandidateBlockFamilyAnnotationSpineList.head
    {kernelSource : InductiveType}
    {remainingSources : List InductiveType}
    {candidates : AddInductive.CandidateList AddInductive.CandidateFamily
      (kernelSource :: remainingSources)}
    {raws : List VInductiveType}
    {roots : CandidateBlockFamilySemanticListRun env blockEnv Us candidates
      raws}
    {shapes : CandidateBlockFamilySemanticGenerationShapeList source env
      blockEnv Us roots}
    (run : CandidateBlockFamilyAnnotationSpineList source env blockEnv Us
      roots shapes) :
    CandidateBlockFamilyAnnotationSpine source env blockEnv Us
      roots.headPosition.semantic shapes.head := by
  cases roots with
  | cons root roots =>
    cases shapes with
    | cons shape shapes =>
      cases run with
      | cons head tail => exact head

/-- Generic annotation spine after the head of a nonempty source-order
spine. -/
def CandidateBlockFamilyAnnotationSpineList.tail
    {kernelSource : InductiveType}
    {remainingSources : List InductiveType}
    {candidates : AddInductive.CandidateList AddInductive.CandidateFamily
      (kernelSource :: remainingSources)}
    {raws : List VInductiveType}
    {roots : CandidateBlockFamilySemanticListRun env blockEnv Us candidates
      raws}
    {shapes : CandidateBlockFamilySemanticGenerationShapeList source env
      blockEnv Us roots}
    (run : CandidateBlockFamilyAnnotationSpineList source env blockEnv Us
      roots shapes) :
    CandidateBlockFamilyAnnotationSpineList source env blockEnv Us
      roots.headPosition.tail shapes.tail := by
  cases roots with
  | cons root roots =>
    cases shapes with
    | cons shape shapes =>
      cases run with
      | cons head tail => exact tail

/-- Projection-friendly annotation tail aligned with `tailExact` semantic and
shape projections. -/
def CandidateBlockFamilyAnnotationSpineList.tailExact
    {kernelSource : InductiveType}
    {remainingSources : List InductiveType}
    {candidates : AddInductive.CandidateList AddInductive.CandidateFamily
      (kernelSource :: remainingSources)}
    {raws : List VInductiveType}
    {roots : CandidateBlockFamilySemanticListRun env blockEnv Us candidates
      raws}
    {shapes : CandidateBlockFamilySemanticGenerationShapeList source env
      blockEnv Us roots}
    (run : CandidateBlockFamilyAnnotationSpineList source env blockEnv Us
      roots shapes) :
    CandidateBlockFamilyAnnotationSpineList source env blockEnv Us
      roots.tailExact shapes.tailExact := by
  cases candidates with
  | cons candidate candidates =>
      cases raws with
      | nil => cases roots
      | cons raw raws =>
          cases roots with
          | cons root roots =>
              cases shapes with
              | cons shape shapes =>
                  cases run with
                  | cons head tail => exact tail

/-- Build the complete generic annotation spine from the semantic roots,
their source-indexed generation shapes, and the validator's exact annotation
provenance list. -/
theorem CandidateBlockFamilyAnnotationSpineList.exists
    {source : VInductDecl} {env blockEnv : VEnv} {Us : List Name}
    {kernelSources : List InductiveType}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateFamily kernelSources}
    {raws : List VInductiveType}
    (roots : CandidateBlockFamilySemanticListRun env blockEnv Us
      candidates raws)
    (shapes : CandidateBlockFamilySemanticGenerationShapeList source env
      blockEnv Us roots)
    {candidateContext : AddInductive.Context}
    (annotations : CandidateFamilyValidationAnnotationList candidateContext
      candidates) :
    Nonempty (CandidateBlockFamilyAnnotationSpineList source env blockEnv Us
      roots shapes) := by
  induction roots with
  | nil =>
    cases shapes
    exact ⟨.nil⟩
  | @cons kernelSource kernelSources candidate candidates raw raws root roots
      ih =>
    cases shapes with
    | cons shape shapes =>
      cases annotations with
      | cons validationAnnotation contextEq resultLevel terminalEq annotations =>
        obtain ⟨head⟩ := CandidateBlockFamilyAnnotationSpine.exists root shape
          validationAnnotation
        obtain ⟨tail⟩ := ih shapes annotations
        exact ⟨.cons head tail⟩

/-- One executable constructor-list shape check determines every dependent
per-position shape record required by semantic generation. -/
def CandidateConstructorSemanticGenerationShapeList.ofCheck
    {source : VInductDecl} {env : VEnv} {Us : List Name}
    {kernelSources : List Constructor}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor kernelSources}
    {raws : List VConstVal}
    (roots : CandidateConstructorSemanticListRun env Us candidates raws)
    (shape : candidateConstructorSemanticGenerationShape
      source candidates raws = true) :
    CandidateConstructorSemanticGenerationShapeList source env Us roots :=
  match roots with
  | .nil => .nil
  | .cons head tail => by
      simp only [candidateConstructorSemanticGenerationShape,
        Bool.and_eq_true, beq_iff_eq] at shape
      exact .cons {
        storedSpine := shape.1.1
        spineLength_eq := shape.1.2 }
        (CandidateConstructorSemanticGenerationShapeList.ofCheck
          tail shape.2)
termination_by sizeOf roots

/-- One executable block-shape check determines the dependent structural
evidence for every retained family and constructor, in exact source order. -/
def CandidateBlockFamilySemanticGenerationShapeList.ofCheck
    {source : VInductDecl} {env blockEnv : VEnv} {Us : List Name}
    {kernelSources : List InductiveType}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateFamily kernelSources}
    {raws : List VInductiveType}
    (roots : CandidateBlockFamilySemanticListRun env blockEnv Us
      candidates raws)
    (shape : candidateBlockFamilySemanticGenerationShape
      source candidates raws = true) :
    CandidateBlockFamilySemanticGenerationShapeList source env blockEnv Us
      roots :=
  match roots with
  | .nil => .nil
  | .cons head tail => by
      simp only [candidateBlockFamilySemanticGenerationShape,
        Bool.and_eq_true, beq_iff_eq] at shape
      exact .cons {
        storedSpine := shape.1.1.1
        spineLength_eq := shape.1.1.2
        constructors :=
          CandidateConstructorSemanticGenerationShapeList.ofCheck
            head.constructors shape.1.2 }
        (CandidateBlockFamilySemanticGenerationShapeList.ofCheck
          tail shape.2)
termination_by sizeOf roots

/-- The complete mutual semantic hierarchy exposes one executable generation
shape gate, with no caller-selected family or constructor sublist. -/
def NormalizationCandidateBlockSemanticRun.generationShape
    {env blockEnv : VEnv} {Us : List Name}
    {kernelSources : List InductiveType} {rawDecl : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate kernelSources}
    (_normalization : NormalizationCandidateBlockSemanticRun env blockEnv Us
      candidate rawDecl) : Bool :=
  normalizationCandidateBlockGenerationShape rawDecl candidate

/-- Reindex a successful executable block gate onto the exact semantic roots
owned by the retained normalization hierarchy. -/
def NormalizationCandidateBlockSemanticRun.generationShapes
    {env blockEnv : VEnv} {Us : List Name}
    {kernelSources : List InductiveType} {rawDecl : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate kernelSources}
    (normalization : NormalizationCandidateBlockSemanticRun env blockEnv Us
      candidate rawDecl)
    (shape : normalization.generationShape = true) :
    CandidateBlockFamilySemanticGenerationShapeList rawDecl env blockEnv Us
      normalization.families := by
  simp only [NormalizationCandidateBlockSemanticRun.generationShape,
    normalizationCandidateBlockGenerationShape] at shape
  exact CandidateBlockFamilySemanticGenerationShapeList.ofCheck
    normalization.families shape

/-- Forget only retained semantic ownership and recover the existing
generation-facing positional list. -/
def CandidateSemanticNormalizedCtorListRun.run :
    (semantic : CandidateSemanticNormalizedCtorListRun
      block env Us roots ctors) →
      CandidateNormalizedCtorListRun block env Us roots.roots ctors
  | .nil => .nil
  | .cons head tail => .cons head.run tail.run

/-- Assemble a `NormalizedCtorRun` for every constructor in an exact
dependent positional list. -/
theorem CandidateNormalizedCtorListRun.normalizedCtorRuns
    {source : VInductDecl} {generation : GenerationChecked source}
    {env : VEnv} {Us : List Name}
    {kernelSources : List Constructor}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor kernelSources}
    {raws : List VConstVal}
    {roots : CandidateConstructorListRun env Us candidates raws}
    {ctors : List NormalizedCtor}
    (run : CandidateNormalizedCtorListRun generation.block env Us roots ctors)
    (henv : VEnv.WF env) (uvars_eq : source.uvars = Us.length)
    (familyParams : TypeChecker.TelDefEqEvidence env Us.length []
      generation.block.rawParams generation.block.checked.params)
    (checked : generation.block.checked.WF env)
    (familyConst : env.HasType source.uvars []
      (.const generation.block.sourceType.name
        (VLevel.params source.uvars))
      generation.block.checked.type.type)
    (pairMembership : ∀ ctor ∈ ctors,
      ctor ∈ generation.block.ctorPairs)
    (prefixLengths : ∀ ctor ∈ ctors,
      (VExpr.telN source.nparams ctor.raw.type).length =
        generation.block.checked.params.length) :
    ∀ ctor ∈ ctors, NormalizedCtorRun generation.block ctor env := by
  induction run with
  | nil => intro ctor hctor; simp at hctor
  | cons head tail ih =>
    intro ctor hctor
    simp only [List.mem_cons] at hctor
    rcases hctor with rfl | hctor
    · exact head.normalizedCtorRun henv uvars_eq familyParams
        (prefixLengths _ (.head _))
        (pairMembership _ (.head _))
        (head.rightType_ofChecked henv uvars_eq checked familyConst
          (pairMembership _ (.head _)))
    · exact ih
        (fun ctor hctor => pairMembership ctor (.tail _ hctor))
        (fun ctor hctor => prefixLengths ctor (.tail _ hctor))
        ctor hctor

/-- Complete source-indexed candidate certificate for one generation-ready
singleton inductive declaration.

`analysis` records that the candidate-derived normalization produced this exact
dependent generation result. `constructors` then aligns every post-family
candidate run with the corresponding dependent analyzer pair. -/
structure GenerationCandidateRun
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    (normalization : NormalizationCandidateRun env Us candidate source)
    (generation : GenerationChecked source) where
  analysis : normalization.normalization.generation? = some generation
  checked : generation.block.checked.WF env
  family : CandidateFamilyGenerationRun normalization generation
  constructors : CandidateNormalizedCtorListRun generation.block
    normalization.family.typeEnv Us normalization.family.constructors
    generation.block.ctorPairs

/-- Complete generation assembly owned by one retained semantic hierarchy.

This is the no-parallel-run form of `GenerationCandidateRun`: family and
constructor spines are projections of `normalization`, while `analysis` retains
the exact dependent analyzer result consumed by Theory generation. -/
structure GenerationCandidateSemanticRun
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    (normalization : NormalizationCandidateSemanticRun env Us candidate source)
    (generation : GenerationChecked source) where
  analysis : normalization.root.normalization.generation? = some generation
  checked : generation.block.checked.WF env
  family : CandidateFamilySemanticGenerationRun normalization generation
  constructors : CandidateSemanticNormalizedCtorListRun generation.block
    normalization.family.typeEnv Us normalization.family.constructors
    generation.block.ctorPairs

/-- Complete semantic-generation input with all analyzer-determined component
equations erased.  Compared with `GenerationCandidateSemanticRun`, this form
retains only checked semantics plus the executable stored-spine/length shape
for each source-indexed root.  Its projection below reconstructs the exact
family and dependent constructor alignment from `analysis`. -/
structure GenerationCandidateSemanticShapeRun
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    (normalization : NormalizationCandidateSemanticRun env Us candidate source)
    (generation : GenerationChecked source) where
  analysis : normalization.root.normalization.generation? = some generation
  checked : generation.block.checked.WF env
  family : CandidateFamilySemanticGenerationShape normalization generation
  constructors : CandidateConstructorSemanticGenerationShapeList source
    normalization.family.typeEnv Us normalization.family.constructors

/-- One executable structural gate for the complete retained singleton
candidate hierarchy.

The family check uses the complete raw parameter/index telescope.  The
constructor check traverses the source-indexed candidate and raw lists
dependently.  This consolidates the former per-fixture family and constructor
proof records into one computation while remaining separate from semantic
authority and dependent analysis. -/
def NormalizationCandidateSemanticRun.generationShape
    {env : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    (normalization : NormalizationCandidateSemanticRun env Us candidate source) :
    Bool :=
  normalizationCandidateGenerationShape source normalization.raw candidate

/-- One successful outer candidate together with the executable structural
gate required before mixed raw/view generation.

The record carries the exact ordinary producer equation, so the shape check
cannot be reused for a different candidate.  It remains operational evidence:
semantic authority is supplied only after Verify interprets the retained
checker executions. -/
structure ProducedGenerationShapeCandidate
    (source : VInductDecl) (raw : VInductiveType)
    (kernelSource : InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (context : AddInductive.Context) where
  candidate : AddInductive.NormalizationCandidate [kernelSource]
  produced :
    AddInductive.buildNormalizationCandidate source.nparams
        [kernelSource] numNested isUnsafe context = .ok candidate
  shape : normalizationCandidateGenerationShape source raw candidate = true

/-- Run the ordinary outer producer and immediately reject candidates whose
retained traces cannot support mixed generation of the supplied raw Theory
family.  The successful result retains both exact producer provenance and the
single complete shape proof. -/
def produceGenerationShapeCandidate
    (source : VInductDecl) (raw : VInductiveType)
    (kernelSource : InductiveType) (numNested : Nat) (isUnsafe : Bool)
    (context : AddInductive.Context) :
    Except Exception (ProducedGenerationShapeCandidate source raw kernelSource
      numNested isUnsafe context) :=
  match produced : AddInductive.buildNormalizationCandidate source.nparams
      [kernelSource] numNested isUnsafe context with
  | .error error => .error error
  | .ok candidate =>
    if shape : normalizationCandidateGenerationShape source raw candidate then
      .ok { candidate, produced, shape }
    else
      .error (.other
        "normalization candidate does not preserve the generation spine")

private theorem produceGenerationShapeCandidate_match_ok
    {source : VInductDecl} {raw : VInductiveType}
    {kernelSource : InductiveType} {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    (result : Except Exception
      (AddInductive.NormalizationCandidate [kernelSource]))
    (toProduced : ∀ actual, result = .ok actual →
      AddInductive.buildNormalizationCandidate source.nparams
          [kernelSource] numNested isUnsafe context = .ok actual)
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    (result_ok : result = .ok candidate)
    (shape : normalizationCandidateGenerationShape source raw candidate = true) :
    (match result_eq : result with
    | .error error => Except.error error
    | .ok actual =>
      if actualShape : normalizationCandidateGenerationShape source raw actual then
        Except.ok (show ProducedGenerationShapeCandidate source raw kernelSource
            numNested isUnsafe context from {
          candidate := actual
          produced := toProduced actual result_eq
          shape := actualShape })
      else
        Except.error (.other
          "normalization candidate does not preserve the generation spine")) =
      Except.ok (show ProducedGenerationShapeCandidate source raw kernelSource
          numNested isUnsafe context from {
        candidate
        produced := toProduced candidate result_ok
        shape }) := by
  subst result
  simp [shape]

/-- A successful ordinary producer equation and successful hierarchy-shape
check determine the exact successful result of the strengthened producer.

Keeping this dependent-match elimination here avoids repeating proof-carrying
`Except` reasoning in clients. -/
theorem produceGenerationShapeCandidate_eq_ok
    {source : VInductDecl} {raw : VInductiveType}
    {kernelSource : InductiveType} {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    (produced :
      AddInductive.buildNormalizationCandidate source.nparams
          [kernelSource] numNested isUnsafe context = .ok candidate)
    (shape : normalizationCandidateGenerationShape source raw candidate = true) :
    produceGenerationShapeCandidate source raw kernelSource numNested isUnsafe
        context =
      .ok { candidate, produced, shape } := by
  unfold produceGenerationShapeCandidate
  exact produceGenerationShapeCandidate_match_ok
    (result := AddInductive.buildNormalizationCandidate source.nparams
      [kernelSource] numNested isUnsafe context)
    (toProduced := fun _ result_eq => result_eq) produced shape

/-- One arbitrary-length normalization candidate together with the detailed
execution which selected it and the complete executable block-generation
shape gate.  Family and constructor validation can therefore be projected
from this same run instead of repeated beside an erased candidate equation. -/
structure ProducedBlockGenerationShapeCandidate
    (source : VInductDecl) (kernelSources : List InductiveType)
    (numNested : Nat) (isUnsafe : Bool)
    (context : AddInductive.Context) where
  execution : AddInductive.NormalizationCandidateExecution source.nparams
    kernelSources numNested isUnsafe context
  producedExecution :
    AddInductive.buildNormalizationCandidateExecution source.nparams
        kernelSources numNested isUnsafe context = .ok execution
  shape : normalizationCandidateBlockGenerationShape source
    execution.candidate = true

/-- Two proof-carrying block producers are equal once their retained detailed
executions are equal; the remaining fields are propositions and hence proof
irrelevant. -/
theorem ProducedBlockGenerationShapeCandidate.eq_of_execution_eq
    (left right : ProducedBlockGenerationShapeCandidate source kernelSources
      numNested isUnsafe context)
    (execution_eq : left.execution = right.execution) : left = right := by
  cases left with
  | mk leftExecution leftProduced leftShape =>
      cases right with
      | mk rightExecution rightProduced rightShape =>
          simp only at execution_eq
          subst rightExecution
          rfl

/-- Candidate erased from the retained detailed execution. -/
def ProducedBlockGenerationShapeCandidate.candidate
    (produced : ProducedBlockGenerationShapeCandidate source kernelSources
      numNested isUnsafe context) :
    AddInductive.NormalizationCandidate kernelSources :=
  produced.execution.candidate

/-- Exact ordinary producer equation derived from the retained detailed
execution and its execution-owned family-validation boundary. -/
theorem ProducedBlockGenerationShapeCandidate.produced
    (produced : ProducedBlockGenerationShapeCandidate source kernelSources
      numNested isUnsafe context) :
    AddInductive.buildNormalizationCandidate source.nparams kernelSources
        numNested isUnsafe context = .ok produced.candidate :=
  produced.execution.producesFromBuildExecution produced.producedExecution

/-- Exact family-validation result owned by the retained execution. -/
def ProducedBlockGenerationShapeCandidate.familyValidationResult
    (produced : ProducedBlockGenerationShapeCandidate source kernelSources
      numNested isUnsafe context) : AddInductive.FamilyValidationBlockResult :=
  produced.execution.familyValidationResult

/-- The retained family result comes from the same detailed execution used by
the block-shape producer. -/
theorem ProducedBlockGenerationShapeCandidate.familyValidationResult_run
    (produced : ProducedBlockGenerationShapeCandidate source kernelSources
      numNested isUnsafe context) :
    AddInductive.observeFamilyValidationBlock source.nparams kernelSources
        context = .ok produced.familyValidationResult :=
  produced.execution.familyValidationResult_run produced.producedExecution

/-- Complete proof-carrying family-validation run projected from the same
detailed execution.  Nonemptiness discharges the validator's terminal
parameter-count assertion. -/
def ProducedBlockGenerationShapeCandidate.familyValidation
    (produced : ProducedBlockGenerationShapeCandidate source kernelSources
      numNested isUnsafe context)
    (nonempty : kernelSources.isEmpty = false) :
    AddInductive.FamilyValidationBlockRun source.nparams kernelSources
      context :=
  produced.execution.familyValidationBlockRun produced.producedExecution
    nonempty

/-- Complete constructor-validation trace projected from the same detailed
execution. -/
def ProducedBlockGenerationShapeCandidate.constructorValidation
    (produced : ProducedBlockGenerationShapeCandidate source kernelSources
      numNested isUnsafe context) :
    AddInductive.ConstructorBlockValidationRun kernelSources
      produced.execution.stats isUnsafe
      { produced.execution.validationContext with
        env := produced.execution.familyEnv } :=
  produced.execution.constructorValidation

/-- Assemble the family-only staging owner directly from a retained detailed
execution.  This deliberately precedes the full raw-block shape gate: the raw
family list can therefore be chosen and staged before constructor enrichment
determines the final common source declaration. -/
noncomputable def
    _root_.Lean4Lean.AddInductive.NormalizationCandidateExecution.familySourceStaging
    {nparams : Nat} {kernelSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    (execution : AddInductive.NormalizationCandidateExecution nparams
      kernelSources numNested isUnsafe context)
    (producedExecution :
      AddInductive.buildNormalizationCandidateExecution nparams kernelSources
        numNested isUnsafe context = .ok execution)
    {ves : VEnvs} (wf : ves.WF context.env)
    (namePrefix_ne : context.ngen.namePrefix ≠
      (({} : TypeChecker.VState).ngen).namePrefix)
    {familyDecl : VInductDecl}
    (uvars_eq : familyDecl.uvars = context.lparams.length)
    (familySources : CandidateBlockFamilyTypeSourceListInput
      (ves.venv context.safety) context.lparams kernelSources
      familyDecl.types)
    (recDepth_ne : context.fuel.recDepth ≠ 0)
    (terminals : CandidateBlockFamilyTerminalSortList
      execution.candidate.families)
    (context_safety_eq : context.safety = .safe)
    (isUnsafe_eq : isUnsafe = false)
    (context_allowPrimitive_eq : context.allowPrimitive = false) :
    NormalizationCandidateBlockFamilySourceStagingInput context
      execution (ves.venv context.safety) context.lparams
      familyDecl := by
  have nindices_size : execution.stats.nindices.size =
      kernelSources.length :=
    execution.validationNindicesSize_all producedExecution
  have metadata : List.Forall₂
      (fun indType info => ∃ numIndices,
        info = AddInductive.declaredInductiveInfo
          execution.stats nparams kernelSources.toArray
          indType numIndices numNested isUnsafe
            execution.validationContext)
      kernelSources execution.declaredInfos := by
    simpa only [AddInductive.NormalizationCandidateExecution.declaredInfos,
      List.toList_toArray] using
      AddInductive.declaredInductiveInfos_matches
        execution.stats nparams kernelSources.toArray
          numNested isUnsafe execution.validationContext
          (by simpa using nindices_size)
  have declaredNames : List.Forall₂
      (fun source info => info.name = source.name)
      kernelSources execution.declaredInfos :=
    Lean4Lean.List.Forall₂.imp (h := metadata) fun source info relation => by
      obtain ⟨numIndices, rfl⟩ := relation
      rfl
  have declarationTrace := execution.declareTrace
  have allowPrimitive_eq :
      execution.validationContext.allowPrimitive = false :=
    (execution.validationContext_allowPrimitive_all
      producedExecution).trans context_allowPrimitive_eq
  rw [allowPrimitive_eq] at declarationTrace
  have traceNames : ∀ info ∈ execution.declaredInfos,
      info.name ∉ VEnv.reflectedPrimitiveNames ∧
        Environment.primitives.contains info.name = false := by
    simpa only [AddInductive.NormalizationCandidateExecution.declaredInfos]
      using declarationTrace.names_not_primitive
  exact {
    uvars_eq := uvars_eq
    preFamily := TypeChecker.CandidateSemanticStage.root wf rfl namePrefix_ne
    familySources := familySources
    whnfFuel := context.candidateWhnfFuel
    whnfDepth := context.candidateWhnfDepth recDepth_ne
    terminals := terminals
    nindices_size := nindices_size
    validation_env_eq :=
      execution.validationContext_env_all producedExecution
    validation_lparams_eq :=
      execution.validationContext_lparams_all producedExecution
    context_safety_eq := context_safety_eq
    isUnsafe_eq := isUnsafe_eq
    preMapWF := (wf.tr (safety := context.safety)).aligned.map_wf
    names_not_primitive :=
      familySources.forall_names_of_declared
        (P := fun name => name ∉ VEnv.reflectedPrimitiveNames ∧
          Environment.primitives.contains name = false)
        declaredNames traceNames }

/-- Reindex direct family staging through a proof-carrying generation-shape
producer when the final raw source is already known. -/
noncomputable def ProducedBlockGenerationShapeCandidate.familySourceStaging
    {source : VInductDecl} {kernelSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    (produced : ProducedBlockGenerationShapeCandidate source kernelSources
      numNested isUnsafe context)
    {ves : VEnvs} (wf : ves.WF context.env)
    (namePrefix_ne : context.ngen.namePrefix ≠
      (({} : TypeChecker.VState).ngen).namePrefix)
    {familyDecl : VInductDecl}
    (uvars_eq : familyDecl.uvars = context.lparams.length)
    (familySources : CandidateBlockFamilyTypeSourceListInput
      (ves.venv context.safety) context.lparams kernelSources
      familyDecl.types)
    (recDepth_ne : context.fuel.recDepth ≠ 0)
    (terminals : CandidateBlockFamilyTerminalSortList
      produced.candidate.families)
    (context_safety_eq : context.safety = .safe)
    (isUnsafe_eq : isUnsafe = false)
    (context_allowPrimitive_eq : context.allowPrimitive = false) :
    NormalizationCandidateBlockFamilySourceStagingInput context
      produced.execution (ves.venv context.safety) context.lparams
      familyDecl := by
  apply produced.execution.familySourceStaging produced.producedExecution wf
    namePrefix_ne uvars_eq familySources recDepth_ne
  · simpa only [ProducedBlockGenerationShapeCandidate.candidate] using terminals
  · exact context_safety_eq
  · exact isUnsafe_eq
  · exact context_allowPrimitive_eq

/-- Run the ordinary arbitrary-block producer and reject any candidate whose
retained traces cannot support generation of the complete raw Theory block. -/
def produceBlockGenerationShapeCandidate
    (source : VInductDecl) (kernelSources : List InductiveType)
    (numNested : Nat) (isUnsafe : Bool)
  (context : AddInductive.Context) :
    Except Exception (ProducedBlockGenerationShapeCandidate source
      kernelSources numNested isUnsafe context) :=
  match producedExecution :
      AddInductive.buildNormalizationCandidateExecution source.nparams
        kernelSources numNested isUnsafe context with
  | .error error => .error error
  | .ok execution =>
    if shape : normalizationCandidateBlockGenerationShape source
        execution.candidate then
      .ok { execution, producedExecution, shape }
    else
      .error (.other
        "normalization candidate block does not preserve the generation spine")

private theorem produceBlockGenerationShapeCandidate_match_ok
    {source : VInductDecl} {kernelSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    (result : Except Exception
      (AddInductive.NormalizationCandidateExecution source.nparams
        kernelSources numNested isUnsafe context))
    (toProducedExecution : ∀ actual, result = .ok actual →
      AddInductive.buildNormalizationCandidateExecution source.nparams
          kernelSources numNested isUnsafe context = .ok actual)
    {execution : AddInductive.NormalizationCandidateExecution source.nparams
      kernelSources numNested isUnsafe context}
    (result_ok : result = .ok execution)
    (shape : normalizationCandidateBlockGenerationShape source
      execution.candidate = true) :
    (match result_eq : result with
    | .error error => Except.error error
    | .ok actual =>
      if actualShape :
          normalizationCandidateBlockGenerationShape source
            actual.candidate then
        Except.ok (show ProducedBlockGenerationShapeCandidate source
            kernelSources numNested isUnsafe context from {
          execution := actual
          producedExecution := toProducedExecution actual result_eq
          shape := actualShape })
      else
        Except.error (.other
          "normalization candidate block does not preserve the generation spine")) =
      Except.ok (show ProducedBlockGenerationShapeCandidate source
          kernelSources numNested isUnsafe context from {
        execution
        producedExecution := toProducedExecution execution result_ok
        shape }) := by
  subst result
  simp [shape]

/-- A successful detailed arbitrary-block execution and complete shape check
determine the exact strengthened producer result. -/
theorem produceBlockGenerationShapeCandidate_eq_ok
    {source : VInductDecl} {kernelSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {execution : AddInductive.NormalizationCandidateExecution source.nparams
      kernelSources numNested isUnsafe context}
    (producedExecution :
      AddInductive.buildNormalizationCandidateExecution source.nparams
          kernelSources numNested isUnsafe context = .ok execution)
    (shape : normalizationCandidateBlockGenerationShape source
      execution.candidate = true) :
    produceBlockGenerationShapeCandidate source kernelSources numNested
        isUnsafe context =
      .ok { execution, producedExecution, shape } := by
  unfold produceBlockGenerationShapeCandidate
  exact produceBlockGenerationShapeCandidate_match_ok
    (result := AddInductive.buildNormalizationCandidateExecution
      source.nparams kernelSources numNested isUnsafe context)
    (toProducedExecution := fun _ result_eq => result_eq)
    producedExecution shape

/-- Project the established generation assembler.  Every normalization root,
view, and recursive spine remains definitionally tied to the semantic owner. -/
def GenerationCandidateSemanticRun.run
    (run : GenerationCandidateSemanticRun normalization generation) :
    GenerationCandidateRun normalization.root generation where
  analysis := run.analysis
  checked := run.checked
  family := run.family.run
  constructors := run.constructors.run

/-- A retained analyzer result necessarily contains the normalization that was
analyzed.  This is derived from `analysis`, rather than supplied by fixtures. -/
theorem GenerationCandidateRun.normalization_eq
    {env : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    {normalization : NormalizationCandidateRun env Us candidate source}
    {generation : GenerationChecked source}
    (run : GenerationCandidateRun normalization generation) :
    generation.block.normalization = normalization.normalization :=
  Normalization.generation?_normalization run.analysis

/-- The source-indexed singleton declarations force the analyzer's raw family
to be the exact family retained by a normalization candidate. -/
theorem NormalizationCandidateRun.sourceType_eq
    {env : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    (normalization : NormalizationCandidateRun env Us candidate source)
    (generation : GenerationChecked source) :
    generation.block.sourceType = normalization.raw := by
  have h : [generation.block.sourceType] = [normalization.raw] :=
    generation.block.source_types_eq.symm.trans normalization.raw_types_eq
  injection h

/-- Exact dependent analysis selects the reconstructed family view, including
its constructor list, not merely an expression payload with the same type. -/
theorem NormalizationCandidateRun.familyViewType_eq
    {env : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    {normalization : NormalizationCandidateRun env Us candidate source}
    {generation : GenerationChecked source}
    (analysis : normalization.normalization.generation? = some generation) :
    generation.block.checked.type = normalization.family.view := by
  have normalization_eq : generation.block.normalization =
      normalization.normalization :=
    Normalization.generation?_normalization analysis
  have hviews := congrArg (fun norm : Normalization source => norm.view.types)
    normalization_eq
  have htypes : [generation.block.checked.type] =
      [normalization.family.view] := by
    calc
      [generation.block.checked.type] =
          generation.block.normalization.view.types :=
        generation.block.checked.types_eq.symm
      _ = normalization.normalization.view.types := hviews
      _ = [normalization.family.view] := rfl
  injection htypes

/-- The retained dependent analysis necessarily checks the exact family view
selected by the normalization candidate.  This equation is a consequence of
the two singleton declaration indices and `normalization_eq`, not a separate
fixture alignment premise. -/
theorem GenerationCandidateRun.familyView_eq
    {env : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    {normalization : NormalizationCandidateRun env Us candidate source}
    {generation : GenerationChecked source}
    (run : GenerationCandidateRun normalization generation) :
    normalization.family.viewType = generation.block.checked.type.type := by
  exact (congrArg (fun ty : VInductiveType => ty.type)
    (normalization.familyViewType_eq run.analysis)).symm

/-- Taking the exact length of the complete stored telescope recovers both
its binder list and its non-forall result.  This is the structural bridge from
one numeric trace invariant to generation's named raw components. -/
private theorem generationTelNForallNLength :
    ∀ (As : List VExpr) (B : VExpr),
      VExpr.telN As.length (VExpr.forallN As B) = As
  | [], _ => rfl
  | _ :: As, B => by
    simp only [List.length_cons, VExpr.forallN, VExpr.telN,
      generationTelNForallNLength As B]

private theorem generationDropNForallNLength :
    ∀ (As : List VExpr) (B : VExpr),
      VExpr.dropN As.length (VExpr.forallN As B) = B
  | [], _ => rfl
  | _ :: As, B => by
    simp only [List.length_cons, VExpr.forallN, VExpr.dropN,
      generationDropNForallNLength As B]

private theorem candidateFullTelComponents (np n : Nat) (e : VExpr)
    (h : n =
      (VExpr.telN np e ++ ctorFields (VExpr.dropN np e)).length) :
    VExpr.telN n e =
        VExpr.telN np e ++ ctorFields (VExpr.dropN np e) ∧
      VExpr.dropN n e = VExpr.resultOf (VExpr.dropN np e) := by
  let As := VExpr.telN np e ++ ctorFields (VExpr.dropN np e)
  have he :
      VExpr.forallN As (VExpr.resultOf (VExpr.dropN np e)) = e := by
    simp only [As, VExpr.forallN_append,
      forallN_ctorFields_resultOf, VExpr.forallN_telN_dropN]
  let B := VExpr.resultOf (VExpr.dropN np e)
  have hAs : n = As.length := h
  change VExpr.telN n e = As ∧ VExpr.dropN n e = B
  rw [hAs, ← he]
  exact ⟨generationTelNForallNLength _ _,
    generationDropNForallNLength _ _⟩

/-- One retained block-family semantic root aligned with the exact normalized
family selected by dependent block analysis.  All component equations are at
the candidate trace's own stored-spine length; no family can be substituted
without transporting these dependent indices. -/
structure CandidateBlockNormalizedFamilyRun
    {source : VInductDecl}
    (generation : BlockGenerationChecked source)
    {env blockEnv : VEnv} {Us : List Name}
    {kernelSource : InductiveType}
    {candidate : AddInductive.CandidateFamily kernelSource}
    {raw : VInductiveType}
    (root : CandidateBlockFamilySemanticRun env blockEnv Us candidate raw)
    (family : NormalizedFamily) where
  uvars_eq : source.uvars = Us.length
  raw_eq : family.raw = raw
  view_eq : family.view.value = root.view
  storedSpine : candidate.familyType.type.trace.storedSpine = true
  rawTel : VExpr.telN candidate.familyType.type.trace.spineLength raw.type =
    family.rawParams source.nparams ++ family.rawIndices source.nparams
  rawResult : VExpr.dropN candidate.familyType.type.trace.spineLength
    raw.type = family.rawResult source.nparams
  viewTel : VExpr.telN candidate.familyType.type.trace.spineLength
    root.type.view = generation.block.checked.params ++ family.view.indices
  viewResult : VExpr.dropN candidate.familyType.type.trace.spineLength
    root.type.view = .sort family.view.resultLevel
  resultLevelWF : family.view.resultLevel.WF source.uvars
  resultLevelEq : family.view.resultLevel ≈
    generation.validated.resultLevel
  familyOnTel : env.OnTel source.uvars []
    (generation.block.checked.params ++ family.view.indices)
  constructors : ∀ constructor ∈ family.view.constructors,
    checkedBlockFieldsWF env source.uvars
        generation.validated.resultLevel
        generation.block.checked.families.indices constructor.fields
        constructor.recursiveAt generation.block.checked.params.reverse 0 ∧
      env.SpineWF source.uvars
        (constructor.fields.reverse ++
          generation.block.checked.params.reverse)
        (VExpr.forallN
          (VExpr.liftTelN constructor.fields.length family.view.indices 0)
          (.sort generation.validated.resultLevel))
        constructor.resultIndices
        (.sort generation.validated.resultLevel)
  constructorShapes : CandidateConstructorSemanticGenerationShapeList source
    blockEnv Us root.constructors

/-- Preserve the complete family telescope/result evidence while transporting
its terminal sort to the validator-owned common block universe. -/
theorem CandidateBlockNormalizedFamilyRun.evidence
    {source : VInductDecl}
    {generation : BlockGenerationChecked source}
    {env blockEnv : VEnv} {Us : List Name}
    {kernelSource : InductiveType}
    {candidate : AddInductive.CandidateFamily kernelSource}
    {raw : VInductiveType}
    {root : CandidateBlockFamilySemanticRun env blockEnv Us candidate raw}
    {family : NormalizedFamily}
    (run : CandidateBlockNormalizedFamilyRun generation root family)
    (commonResultLevelWF :
      generation.validated.resultLevel.WF source.uvars) :
    TypeChecker.TelResultDefEqEvidence env source.uvars []
      (family.rawParams source.nparams ++
        family.rawIndices source.nparams)
      (generation.block.checked.params ++ family.view.indices)
      (family.rawResult source.nparams)
      (.sort generation.validated.resultLevel)
      (.sort (.succ generation.validated.resultLevel)) := by
  rw [run.uvars_eq] at commonResultLevelWF ⊢
  have rightType : env.HasType Us.length
      (family.rawParams source.nparams ++
        family.rawIndices source.nparams).reverse
      (.sort family.view.resultLevel)
      (.sort (.succ family.view.resultLevel)) := by
    apply VEnv.HasType.sort
    simpa only [run.uvars_eq] using run.resultLevelWF
  have evidence : TypeChecker.TelResultDefEqEvidence env Us.length []
      (family.rawParams source.nparams ++
        family.rawIndices source.nparams)
      (generation.block.checked.params ++ family.view.indices)
      (family.rawResult source.nparams)
      (.sort family.view.resultLevel)
      (.sort (.succ family.view.resultLevel)) :=
    (root.type.spine run.storedSpine).evidenceAt run.rawTel run.viewTel
      run.rawResult run.viewResult rightType
  exact evidence.resultSortEquiv
    (by simpa only [run.uvars_eq] using run.resultLevelWF)
    commonResultLevelWF run.resultLevelEq

/-- Interpret one exactly aligned block-family root as the compositional run
consumed by `BlockGenerationRun`. -/
theorem CandidateBlockNormalizedFamilyRun.normalizedFamilyRun
    {source : VInductDecl}
    {generation : BlockGenerationChecked source}
    {env blockEnv : VEnv} {Us : List Name}
    {kernelSource : InductiveType}
    {candidate : AddInductive.CandidateFamily kernelSource}
    {raw : VInductiveType}
    {root : CandidateBlockFamilySemanticRun env blockEnv Us candidate raw}
    {family : NormalizedFamily}
    (run : CandidateBlockNormalizedFamilyRun generation root family)
    (commonResultLevelWF :
      generation.validated.resultLevel.WF source.uvars) :
    NormalizedFamilyRun generation family env := by
  have commonEvidence := run.evidence commonResultLevelWF
  exact {
    familyTel := commonEvidence.telescope
    familyResult := by
      simpa only [List.append_nil] using commonEvidence.result }

/-- Type a staged raw family constant at the common normalized family type
selected jointly by candidate evidence and block validation. -/
theorem CandidateBlockNormalizedFamilyRun.familyConstCommon_hasType
    {source : VInductDecl}
    {generation : BlockGenerationChecked source}
    {env blockEnv : VEnv} {Us : List Name}
    {kernelSource : InductiveType}
    {candidate : AddInductive.CandidateFamily kernelSource}
    {raw : VInductiveType}
    {root : CandidateBlockFamilySemanticRun env blockEnv Us candidate raw}
    {family : NormalizedFamily}
    (run : CandidateBlockNormalizedFamilyRun generation root family)
    (normalization : NormalizationBlockRun
      generation.block.normalization env blockEnv)
    (commonResultLevelWF :
      generation.validated.resultLevel.WF source.uvars)
    (familyMember : family ∈ generation.families)
    (blockWF : VEnv.WF blockEnv) :
    blockEnv.HasType source.uvars []
      (.const family.raw.name (VLevel.params source.uvars))
      (VExpr.forallN generation.block.checked.params
        (VExpr.forallN family.view.indices
          (.sort generation.validated.resultLevel))) := by
  have rawMember : family.raw ∈ source.types := by
    rw [← generation.families_map_raw]
    exact List.mem_map.mpr ⟨family, familyMember, rfl⟩
  have lookup := VEnv.stageInductiveTypes_constants normalization.stage
    family.raw rawMember
  have rawConst := VEnv.HasType.const0 lookup
    (blockWF.ordered.constWF lookup)
  have rawConst' : blockEnv.HasType source.uvars []
      (.const family.raw.name (VLevel.params source.uvars)) family.raw.type := by
    simpa only [generation.family_uvars familyMember] using rawConst
  have familyEvidence := (run.evidence commonResultLevelWF).mono
    (VEnv.stageInductiveTypes_le normalization.stage)
  obtain ⟨_, fullEq⟩ :=
    familyEvidence.telescope.telDefEq.forallN_defeq
      familyEvidence.result.isDefEq
  have rawConstFull : blockEnv.HasType source.uvars []
      (.const family.raw.name (VLevel.params source.uvars))
      (VExpr.forallN
        (family.rawParams source.nparams ++ family.rawIndices source.nparams)
        (family.rawResult source.nparams)) := by
    rw [family.rawType_eq] at rawConst'
    simpa only [VExpr.forallN_append] using rawConst'
  simpa only [VExpr.forallN_append] using fullEq.defeq rawConstFull

/-- Build one exact family alignment from the block shape, its source-indexed
semantic root, and the dependent `CheckedFamily` selected at the same
position.  The only semantic cross-family premise is the validator-owned
common-result-level equivalence. -/
def CandidateBlockFamilySemanticGenerationShape.alignedRun
    {source : VInductDecl}
    {generation : BlockGenerationChecked source}
    {env blockEnv : VEnv} {Us : List Name}
    {kernelSource : InductiveType}
    {candidate : AddInductive.CandidateFamily kernelSource}
    {raw : VInductiveType}
    {root : CandidateBlockFamilySemanticRun env blockEnv Us candidate raw}
    (input : CandidateBlockFamilySemanticGenerationShape source env blockEnv
      Us root)
    (family : NormalizedFamily) (hfamily : family ∈ generation.families)
    {viewTypes : List VInductiveType} {params : List VExpr}
    {ordinal : Nat}
    (checked : CheckedFamily { source with types := viewTypes }
      params ordinal root.view)
    (checkedRun : CheckedBlockFamilyRun checked env
      generation.validated.resultLevel
      generation.block.checked.families.indices)
    (raw_eq : family.raw = raw)
    (view_eq : family.view = checked.data)
    (params_eq : generation.block.checked.params = params)
    (uvars_eq : source.uvars = Us.length) :
    CandidateBlockNormalizedFamilyRun generation root family := by
  have familyShape := generation.shape.2.2.2.2 family hfamily
  have fullLength : candidate.familyType.type.trace.spineLength =
      (generation.block.checked.params ++ family.view.indices).length := by
    calc
      candidate.familyType.type.trace.spineLength =
          (VExpr.telN source.nparams raw.type ++
            ctorFields (VExpr.dropN source.nparams raw.type)).length :=
        input.spineLength_eq
      _ = (family.rawParams source.nparams ++
          family.rawIndices source.nparams).length := by
        simp only [NormalizedFamily.rawParams,
          NormalizedFamily.rawIndices, raw_eq]
      _ = source.nparams + family.view.indices.length := by
        simp only [List.length_append]
        rw [familyShape.2.2.1, familyShape.2.2.2.1]
      _ = generation.block.checked.params.length +
          family.view.indices.length := by
        rw [← generation.shape.1, generation.shape.2.1]
      _ = (generation.block.checked.params ++
          family.view.indices).length := by
        simp only [List.length_append]
  have viewType : root.type.view =
      VExpr.forallN generation.block.checked.params
        (VExpr.forallN family.view.indices
          (.sort family.view.resultLevel)) := by
    simpa only [CandidateBlockFamilySemanticRun.view, params_eq, view_eq,
      CheckedFamily.data] using checked.type_eq
  refine {
    uvars_eq
    raw_eq
    view_eq := by simp only [view_eq, CheckedFamily.data,
      CheckedFamily.value]
    storedSpine := input.storedSpine
    rawTel := ?_
    rawResult := ?_
    viewTel := ?_
    viewResult := ?_
    resultLevelWF := ?_
    resultLevelEq := ?_
    familyOnTel := ?_
    constructors := ?_
    constructorShapes := input.constructors }
  · have components := candidateFullTelComponents source.nparams
      candidate.familyType.type.trace.spineLength raw.type
        input.spineLength_eq
    simpa only [NormalizedFamily.rawParams,
      NormalizedFamily.rawIndices, raw_eq] using components.1
  · have components := candidateFullTelComponents source.nparams
      candidate.familyType.type.trace.spineLength raw.type
        input.spineLength_eq
    simpa only [NormalizedFamily.rawResult, raw_eq] using components.2
  · rw [viewType, fullLength]
    simpa only [VExpr.forallN_append] using
      generationTelNForallNLength
        (generation.block.checked.params ++ family.view.indices)
        (.sort family.view.resultLevel)
  · rw [viewType, fullLength]
    simpa only [VExpr.forallN_append] using
      generationDropNForallNLength
        (generation.block.checked.params ++ family.view.indices)
        (.sort family.view.resultLevel)
  · simpa only [view_eq, CheckedFamily.data] using checked.resultLevel_wf
  · simpa only [view_eq, CheckedFamily.data] using checkedRun.resultLevelEq
  · simpa only [view_eq, CheckedFamily.data, params_eq] using
      checkedRun.familyOnTel
  · intro constructor member
    have semantics := checkedRun.constructors constructor (by
      simpa only [view_eq, CheckedFamily.data] using member)
    simpa only [view_eq, CheckedFamily.data, params_eq] using semantics

/-- One retained constructor semantic root aligned with its exact normalized
pair inside a particular mutual family. -/
structure CandidateBlockNormalizedCtorRun
    {source : VInductDecl}
    (generation : BlockGenerationChecked source)
    {env : VEnv} {Us : List Name}
    {kernelSource : Constructor}
    {candidate : AddInductive.CandidateConstructor kernelSource}
    {raw : VConstVal}
    (root : CandidateConstructorSemanticRun env Us candidate raw)
    (family : NormalizedFamily) (constructor : NormalizedCtor) where
  raw_eq : constructor.raw = raw
  view_eq : constructor.view.value = root.root.view
  storedSpine : candidate.type.trace.storedSpine = true
  rawTel : VExpr.telN candidate.type.trace.spineLength raw.type =
    constructor.declaredBinders source.nparams
  rawResult : VExpr.dropN candidate.type.trace.spineLength raw.type =
    constructor.rawResult source.nparams
  viewTel : VExpr.telN candidate.type.trace.spineLength root.type.view =
    generation.block.checked.params ++ constructor.view.fields
  viewResult : VExpr.dropN candidate.type.trace.spineLength root.type.view =
    VExpr.appN
      (.const family.raw.name (VLevel.params source.uvars))
      (VExpr.bvarRevRange
          (constructor.rawFields source.nparams).length source.nparams ++
        constructor.view.resultIndices)

/-- Derive every component equation for one exact family-local constructor
pair from its source-indexed structural shape and dependent block analysis. -/
private theorem CandidateConstructorSemanticGenerationShape.blockRun
    {source : VInductDecl}
    {generation : BlockGenerationChecked source}
    {env : VEnv} {Us : List Name}
    {kernelSource : Constructor}
    {candidate : AddInductive.CandidateConstructor kernelSource}
    {raw : VConstVal}
    {root : CandidateConstructorSemanticRun env Us candidate raw}
    (input : CandidateConstructorSemanticGenerationShape
      (source := source) env Us root)
    (family : NormalizedFamily) (familyMember : family ∈ generation.families)
    (constructor : NormalizedCtor)
    (constructorMember : constructor ∈ family.ctorPairs)
    (raw_eq : constructor.raw = raw)
    (view_eq : constructor.view.value = root.root.view) :
    CandidateBlockNormalizedCtorRun generation root family constructor := by
  let As := generation.block.checked.params ++ constructor.view.fields
  let result := VExpr.appN
    (.const family.raw.name (VLevel.params source.uvars))
    (VExpr.bvarRevRange
        (constructor.rawFields source.nparams).length source.nparams ++
      constructor.view.resultIndices)
  have prefixLength : generation.block.checked.params.length =
      source.nparams :=
    generation.shape.2.1.symm.trans generation.shape.1
  have constructorShape :=
    (generation.shape.2.2.2.2 family familyMember).2.2.2.2.2.2
      constructor constructorMember
  have fullLength : candidate.type.trace.spineLength = As.length := by
    rw [input.spineLength_eq]
    simp only [As, List.length_append]
    rw [← raw_eq]
    simp only [NormalizedCtor.rawFields] at constructorShape
    rw [constructorShape.2.2.1, constructorShape.2.2.2, prefixLength]
  have viewType : root.type.view = VExpr.forallN As result := by
    have rootEq : root.type.view = constructor.view.value.type :=
      (congrArg (fun value : VConstVal => value.type) view_eq).symm
    rw [rootEq, generation.viewCtorType_eq familyMember constructorMember]
    simp only [As, result, VExpr.forallN_append]
    rw [constructorShape.2.2.2]
  refine {
    raw_eq
    view_eq
    storedSpine := input.storedSpine
    rawTel := ?_
    rawResult := ?_
    viewTel := ?_
    viewResult := ?_ }
  · have components := candidateFullTelComponents source.nparams
      candidate.type.trace.spineLength raw.type input.spineLength_eq
    simpa only [NormalizedCtor.declaredBinders,
      NormalizedCtor.rawFields, raw_eq] using components.1
  · have components := candidateFullTelComponents source.nparams
      candidate.type.trace.spineLength raw.type input.spineLength_eq
    simpa only [NormalizedCtor.rawResult, raw_eq] using components.2
  · rw [viewType, fullLength]
    exact generationTelNForallNLength As result
  · rw [viewType, fullLength]
    exact generationDropNForallNLength As result

/-- Apply the staged owning-family constant to the checked parameter spine,
then consume the analyzer-owned result-index spine. -/
theorem CandidateBlockNormalizedFamilyRun.constructorResult_hasType
    {source : VInductDecl}
    {generation : BlockGenerationChecked source}
    {env blockEnv : VEnv} {Us : List Name}
    {kernelSource : InductiveType}
    {candidate : AddInductive.CandidateFamily kernelSource}
    {raw : VInductiveType}
    {root : CandidateBlockFamilySemanticRun env blockEnv Us candidate raw}
    {family : NormalizedFamily}
    (run : CandidateBlockNormalizedFamilyRun generation root family)
    (normalization : NormalizationBlockRun
      generation.block.normalization env blockEnv)
    (commonResultLevelWF :
      generation.validated.resultLevel.WF source.uvars)
    (familyMember : family ∈ generation.families)
    (blockWF : VEnv.WF blockEnv)
    (constructor : NormalizedCtor)
    (constructorMember : constructor ∈ family.ctorPairs) :
    blockEnv.HasType source.uvars
      (generation.block.checked.params ++ constructor.view.fields).reverse
      (VExpr.appN
        (.const family.raw.name (VLevel.params source.uvars))
        (VExpr.bvarRevRange
            (constructor.rawFields source.nparams).length source.nparams ++
          constructor.view.resultIndices))
      (.sort generation.validated.resultLevel) := by
  have familyConst := run.familyConstCommon_hasType normalization
    commonResultLevelWF familyMember blockWF
  have familyConstClosed :
      (VExpr.forallN generation.block.checked.params
        (VExpr.forallN family.view.indices
          (.sort generation.validated.resultLevel))).ClosedN 0 :=
    (familyConst.closedN' blockWF.ordered.closed trivial).2.2
  have familyConstWeak := familyConst.weak0 blockWF.ordered
    (Γ := constructor.view.fields.reverse ++
      generation.block.checked.params.reverse)
  have familyApp := VEnv.HasType.appN_selfSpine'
    (As := generation.block.checked.params)
    (B := VExpr.forallN family.view.indices
      (.sort generation.validated.resultLevel))
    (Δ := constructor.view.fields.reverse) (Γ := [])
    familyConstClosed (by simpa using familyConstWeak)
  rw [List.length_reverse, VExpr.liftN_forallN] at familyApp
  have familyApp' : blockEnv.HasType source.uvars
      (constructor.view.fields.reverse ++
        generation.block.checked.params.reverse)
      (VExpr.appN
        (.const family.raw.name (VLevel.params source.uvars))
        (VExpr.bvarRevRange constructor.view.fields.length
          generation.block.checked.params.length))
      (VExpr.forallN
        (VExpr.liftTelN constructor.view.fields.length
          family.view.indices 0)
        (.sort generation.validated.resultLevel)) := by
    simpa [VExpr.liftN] using familyApp
  have familyShape := generation.shape.2.2.2.2 family familyMember
  have viewsEq : family.ctorPairs.map (fun ctor => ctor.view) =
      family.view.constructors := by
    apply pairNormalizedCtors_map_view
    exact familyShape.2.2.2.2.1.symm.trans familyShape.2.2.2.2.2.1
  have viewMember : constructor.view ∈ family.view.constructors := by
    rw [← viewsEq]
    exact List.mem_map.mpr ⟨constructor, constructorMember, rfl⟩
  have resultSpine := (run.constructors constructor.view viewMember).2.mono
    (VEnv.stageInductiveTypes_le normalization.stage)
  have resultType := resultSpine.hasType_appN familyApp'
  rw [← VExpr.appN_append] at resultType
  have paramsLength : generation.block.checked.params.length =
      source.nparams := generation.shape.2.1.symm.trans generation.shape.1
  have fieldsLength := (familyShape.2.2.2.2.2.2
    constructor constructorMember).2.2.2
  simpa only [List.reverse_append, paramsLength, ← fieldsLength] using
    resultType

/-- Transport the checked constructor-result typing judgment from its view
context to the exact stored declared telescope. -/
theorem CandidateBlockNormalizedCtorRun.rightType
    {source : VInductDecl}
    {generation : BlockGenerationChecked source}
    {env blockEnv : VEnv} {Us : List Name}
    {familyKernelSource : InductiveType}
    {familyCandidate : AddInductive.CandidateFamily familyKernelSource}
    {familyRaw : VInductiveType}
    {familyRoot : CandidateBlockFamilySemanticRun env blockEnv Us
      familyCandidate familyRaw}
    {family : NormalizedFamily}
    (familyRun : CandidateBlockNormalizedFamilyRun generation familyRoot family)
    {kernelSource : Constructor}
    {candidate : AddInductive.CandidateConstructor kernelSource}
    {raw : VConstVal}
    {root : CandidateConstructorSemanticRun blockEnv Us candidate raw}
    {constructor : NormalizedCtor}
    (run : CandidateBlockNormalizedCtorRun generation root family constructor)
    (normalization : NormalizationBlockRun
      generation.block.normalization env blockEnv)
    (commonResultLevelWF :
      generation.validated.resultLevel.WF source.uvars)
    (familyMember : family ∈ generation.families)
    (constructorMember : constructor ∈ family.ctorPairs)
    (blockWF : VEnv.WF blockEnv) :
    blockEnv.HasType source.uvars
      (constructor.declaredBinders source.nparams).reverse
      (VExpr.appN
        (.const family.raw.name (VLevel.params source.uvars))
        (VExpr.bvarRevRange
            (constructor.rawFields source.nparams).length source.nparams ++
          constructor.view.resultIndices))
      (.sort generation.validated.resultLevel) := by
  have viewRight := familyRun.constructorResult_hasType normalization
    commonResultLevelWF familyMember blockWF constructor constructorMember
  obtain ⟨_, preliminary⟩ := (root.type.spine run.storedSpine).evidence
  have telescope : TypeChecker.TelDefEqEvidence blockEnv Us.length []
      (constructor.declaredBinders source.nparams)
      (generation.block.checked.params ++ constructor.view.fields) := by
    simpa only [run.rawTel, run.viewTel] using preliminary.telescope
  have viewRight' : blockEnv.HasType Us.length
      (generation.block.checked.params ++ constructor.view.fields).reverse
      (VExpr.appN
        (.const family.raw.name (VLevel.params source.uvars))
        (VExpr.bvarRevRange
            (constructor.rawFields source.nparams).length source.nparams ++
          constructor.view.resultIndices))
      (.sort generation.validated.resultLevel) := by
    simpa only [← familyRun.uvars_eq] using viewRight
  have context : blockEnv.IsDefEqCtx Us.length []
      (constructor.declaredBinders source.nparams).reverse
      (generation.block.checked.params ++ constructor.view.fields).reverse := by
    simpa using telescope.telDefEq.ctx
  have transported := viewRight'.defeqDFC blockWF.ordered
    (context.symm blockWF.ordered)
  simpa only [familyRun.uvars_eq] using transported

/-- Exact declared telescope/result evidence for one aligned mutual
constructor candidate. -/
theorem CandidateBlockNormalizedCtorRun.declaredEvidence
    {source : VInductDecl}
    {generation : BlockGenerationChecked source}
    {env blockEnv : VEnv} {Us : List Name}
    {familyKernelSource : InductiveType}
    {familyCandidate : AddInductive.CandidateFamily familyKernelSource}
    {familyRaw : VInductiveType}
    {familyRoot : CandidateBlockFamilySemanticRun env blockEnv Us
      familyCandidate familyRaw}
    {family : NormalizedFamily}
    (familyRun : CandidateBlockNormalizedFamilyRun generation familyRoot family)
    {kernelSource : Constructor}
    {candidate : AddInductive.CandidateConstructor kernelSource}
    {raw : VConstVal}
    {root : CandidateConstructorSemanticRun blockEnv Us candidate raw}
    {constructor : NormalizedCtor}
    (run : CandidateBlockNormalizedCtorRun generation root family constructor)
    (normalization : NormalizationBlockRun
      generation.block.normalization env blockEnv)
    (commonResultLevelWF :
      generation.validated.resultLevel.WF source.uvars)
    (familyMember : family ∈ generation.families)
    (constructorMember : constructor ∈ family.ctorPairs)
    (blockWF : VEnv.WF blockEnv) :
    TypeChecker.TelResultDefEqEvidence blockEnv source.uvars []
      (constructor.declaredBinders source.nparams)
      (generation.block.checked.params ++ constructor.view.fields)
      (constructor.rawResult source.nparams)
      (VExpr.appN
        (.const family.raw.name (VLevel.params source.uvars))
        (VExpr.bvarRevRange
            (constructor.rawFields source.nparams).length source.nparams ++
          constructor.view.resultIndices))
      (.sort generation.validated.resultLevel) := by
  have rightType := run.rightType familyRun normalization
    commonResultLevelWF familyMember constructorMember blockWF
  have rightType' : blockEnv.HasType Us.length
      (constructor.declaredBinders source.nparams).reverse
      (VExpr.appN
        (.const family.raw.name (VLevel.params source.uvars))
        (VExpr.bvarRevRange
            (constructor.rawFields source.nparams).length source.nparams ++
          constructor.view.resultIndices))
      (.sort generation.validated.resultLevel) := by
    simpa only [← familyRun.uvars_eq] using rightType
  have evidence := (root.type.spine run.storedSpine).evidenceAt
    run.rawTel run.viewTel run.rawResult run.viewResult rightType'
  simpa only [familyRun.uvars_eq] using evidence

/-- Recursive descriptors retain their exact target family, source field,
and staged semantic certificate. -/
theorem CandidateBlockNormalizedFamilyRun.recursive
    {source : VInductDecl}
    {generation : BlockGenerationChecked source}
    {env blockEnv : VEnv} {Us : List Name}
    {kernelSource : InductiveType}
    {candidate : AddInductive.CandidateFamily kernelSource}
    {raw : VInductiveType}
    {root : CandidateBlockFamilySemanticRun env blockEnv Us candidate raw}
    {family : NormalizedFamily}
    (run : CandidateBlockNormalizedFamilyRun generation root family)
    (normalization : NormalizationBlockRun
      generation.block.normalization env blockEnv)
    (familyMember : family ∈ generation.families)
    (constructor : NormalizedCtor)
    (constructorMember : constructor ∈ family.ctorPairs) :
    ∀ recursive ∈ constructor.view.recursive,
      ∃ targetFamily ∈ generation.families,
        targetFamily.view.ordinal = recursive.targetType ∧
          (∃ field,
            constructor.view.fields[recursive.fieldIndex]? = some field ∧
              field = VExpr.forallN recursive.binders
                (VExpr.appN
                  (.const targetFamily.raw.name
                    (VLevel.params source.uvars))
                  (VExpr.bvarRevRange
                      (recursive.fieldIndex + recursive.binders.length)
                      source.nparams ++ recursive.indices))) ∧
          recursive.WF source.uvars blockEnv
            generation.validated.resultLevel targetFamily.view.indices
            ((constructor.view.fields.take recursive.fieldIndex).reverse ++
              generation.block.checked.params.reverse) := by
  intro recursive recursiveMember
  have familyShape := generation.shape.2.2.2.2 family familyMember
  have viewsEq : family.ctorPairs.map (fun ctor => ctor.view) =
      family.view.constructors := by
    apply pairNormalizedCtors_map_view
    exact familyShape.2.2.2.2.1.symm.trans familyShape.2.2.2.2.2.1
  have viewMember : constructor.view ∈ family.view.constructors := by
    rw [← viewsEq]
    exact List.mem_map.mpr ⟨constructor, constructorMember, rfl⟩
  have analyzerEq :=
    generation.viewCtor_ofBlock familyMember constructorMember
  have analyzerMember : recursive ∈
      (CheckedCtor.ofBlock generation.block.normalization.view
        constructor.view.value).recursive := by
    simpa only [← analyzerEq] using recursiveMember
  obtain ⟨field, analyzerFieldAt, analyzed⟩ :=
    CheckedCtor.ofBlock_recursive_field analyzerMember
  have fieldAt : constructor.view.fields[recursive.fieldIndex]? =
      some field := by
    simpa only [← analyzerEq] using analyzerFieldAt
  obtain ⟨_, header, headerAt, fieldShape⟩ :=
    blockRecArg?_eq_some analyzed
  have positionalAnalyzer :=
    CheckedCtor.ofBlock_recursive_mem_recursiveAt analyzerMember
  have positional : some recursive ∈ constructor.view.recursiveAt := by
    simpa only [← analyzerEq] using positionalAnalyzer
  obtain ⟨k, semanticField, indices, fieldIndex, semanticFieldAt,
      targetAt, recursiveWF⟩ :=
    checkedBlockFieldsWF_some_mem
      (run.constructors constructor.view viewMember).1 positional
  have kEq : k = recursive.fieldIndex := by omega
  subst k
  obtain ⟨targetFamily, targetMember, targetOrdinal, targetIndices⟩ :=
    generation.exists_family_of_indices_get? targetAt
  have headerAt' :
      (familyHeaders generation.block.normalization.view.nparams
        generation.block.normalization.view.types)[targetFamily.view.ordinal]? =
          some header := by
    simpa only [targetOrdinal] using headerAt
  have headerName := generation.familyHeader_name targetMember headerAt'
  have exactFieldShape : field = VExpr.forallN recursive.binders
      (VExpr.appN
        (.const targetFamily.raw.name (VLevel.params source.uvars))
        (VExpr.bvarRevRange
            (recursive.fieldIndex + recursive.binders.length)
            source.nparams ++ recursive.indices)) := by
    simpa only [← generation.block.normalization.shape.1,
      ← generation.block.normalization.shape.2.1, headerName] using fieldShape
  refine ⟨targetFamily, targetMember, targetOrdinal, ⟨field, fieldAt,
    exactFieldShape⟩, ?_⟩
  have recursiveWF' := recursiveWF.mono
    (VEnv.stageInductiveTypes_le normalization.stage)
  simpa only [targetIndices] using recursiveWF'

/-- Assemble all four declared/emitted constructor paths together with the
analyzer-owned owner, recursion, and result-spine facts. -/
theorem CandidateBlockNormalizedCtorRun.normalizedRun
    {source : VInductDecl}
    {generation : BlockGenerationChecked source}
    {env blockEnv : VEnv} {Us : List Name}
    {familyKernelSource : InductiveType}
    {familyCandidate : AddInductive.CandidateFamily familyKernelSource}
    {familyRaw : VInductiveType}
    {familyRoot : CandidateBlockFamilySemanticRun env blockEnv Us
      familyCandidate familyRaw}
    {family : NormalizedFamily}
    (familyRun : CandidateBlockNormalizedFamilyRun generation familyRoot family)
    {kernelSource : Constructor}
    {candidate : AddInductive.CandidateConstructor kernelSource}
    {raw : VConstVal}
    {root : CandidateConstructorSemanticRun blockEnv Us candidate raw}
    {constructor : NormalizedCtor}
    (run : CandidateBlockNormalizedCtorRun generation root family constructor)
    (normalization : NormalizationBlockRun
      generation.block.normalization env blockEnv)
    (commonResultLevelWF :
      generation.validated.resultLevel.WF source.uvars)
    (paramsTel : TypeChecker.TelDefEqEvidence env source.uvars []
      generation.block.rawParams generation.block.checked.params)
    (familyMember : family ∈ generation.families)
    (constructorMember : constructor ∈ family.ctorPairs) :
    NormalizedBlockCtorRun generation
      { owner := family.view.ordinal
        familyName := family.raw.name
        familyIndices := family.view.indices
        ctor := constructor }
      blockEnv := by
  have blockWF : VEnv.WF blockEnv := by
    obtain ⟨_, recursive⟩ := root.type.recursive
    exact recursive.env_wf
  have declared := run.declaredEvidence familyRun normalization
    commonResultLevelWF familyMember constructorMember blockWF
  have declaredSplit : TypeChecker.TelResultDefEqEvidence blockEnv
      source.uvars []
      (VExpr.telN source.nparams constructor.raw.type ++
        constructor.rawFields source.nparams)
      (generation.block.checked.params ++ constructor.view.fields)
      (constructor.rawResult source.nparams)
      (VExpr.appN
        (.const family.raw.name (VLevel.params source.uvars))
        (VExpr.bvarRevRange
            (constructor.rawFields source.nparams).length source.nparams ++
          constructor.view.resultIndices))
      (.sort generation.validated.resultLevel) := by
    simpa only [NormalizedCtor.declaredBinders] using declared
  have paramsTelBlock := paramsTel.mono
    (VEnv.stageInductiveTypes_le normalization.stage)
  have checkedParams : TypeChecker.TelDefEqEvidence blockEnv source.uvars []
      generation.block.checked.params generation.block.checked.params :=
    .ofTelDefEq <|
      (paramsTelBlock.telDefEq.view_onTel blockWF.ordered).telDefEq_refl
  have familyShape := generation.shape.2.2.2.2 family familyMember
  have prefixLength : (VExpr.telN source.nparams constructor.raw.type).length =
      generation.block.checked.params.length :=
    (familyShape.2.2.2.2.2.2 constructor constructorMember).2.2.1.trans
      (generation.shape.1.symm.trans generation.shape.2.1)
  have emitted := declaredSplit.replacePrefix blockWF checkedParams prefixLength
  have viewsEq : family.ctorPairs.map (fun ctor => ctor.view) =
      family.view.constructors := by
    apply pairNormalizedCtors_map_view
    exact familyShape.2.2.2.2.1.symm.trans familyShape.2.2.2.2.2.1
  have viewMember : constructor.view ∈ family.view.constructors := by
    rw [← viewsEq]
    exact List.mem_map.mpr ⟨constructor, constructorMember, rfl⟩
  exact {
    declaredTel := by
      simpa only [NormalizedBlockCtor.declaredBinders,
        NormalizedBlockCtor.viewBinders] using declared.telescope
    declaredResult := by
      simpa only [NormalizedBlockCtor.declaredBinders,
        NormalizedBlockCtor.rawResult, NormalizedBlockCtor.resultTarget,
        List.append_nil] using declared.result
    emittedTel := by
      simpa only [NormalizedBlockCtor.emittedBinders,
        NormalizedBlockCtor.viewBinders] using emitted.telescope
    emittedResult := by
      simpa only [NormalizedBlockCtor.emittedBinders,
        NormalizedBlockCtor.rawResult, NormalizedBlockCtor.resultTarget,
        List.append_nil] using emitted.result
    owner := ⟨family, familyMember, rfl, rfl, rfl⟩
    recursive := familyRun.recursive normalization familyMember
      constructor constructorMember
    resultSpine := (familyRun.constructors constructor.view viewMember).2.mono
      (VEnv.stageInductiveTypes_le normalization.stage) }

/-- Exact source-order alignment between every retained block-family root and
the normalized-family list selected by generation analysis. -/
inductive CandidateBlockNormalizedFamilyRunList
    {source : VInductDecl}
    (generation : BlockGenerationChecked source)
    (env blockEnv : VEnv) (Us : List Name) :
    {kernelSources : List InductiveType} →
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateFamily kernelSources} →
    {raws : List VInductiveType} →
    (roots : CandidateBlockFamilySemanticListRun env blockEnv Us
      candidates raws) →
    List NormalizedFamily → Type where
  | nil : CandidateBlockNormalizedFamilyRunList generation env blockEnv Us
      .nil []
  | cons
      (head : CandidateBlockNormalizedFamilyRun generation root family)
      (tail : CandidateBlockNormalizedFamilyRunList generation env blockEnv
        Us roots families) :
      CandidateBlockNormalizedFamilyRunList generation env blockEnv Us
        (.cons root roots) (family :: families)

/-- Erase semantic-root alignment while preserving the exact normalized
family-list index consumed by `BlockGenerationRun`. -/
def CandidateBlockNormalizedFamilyRunList.normalizedFamilyRuns
    {source : VInductDecl}
    {generation : BlockGenerationChecked source}
    {env blockEnv : VEnv} {Us : List Name}
    {kernelSources : List InductiveType}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateFamily kernelSources}
    {raws : List VInductiveType}
    {roots : CandidateBlockFamilySemanticListRun env blockEnv Us
      candidates raws}
    {families : List NormalizedFamily}
    (runs : CandidateBlockNormalizedFamilyRunList generation env blockEnv Us
      roots families)
    (commonResultLevelWF :
      generation.validated.resultLevel.WF source.uvars) :
    NormalizedFamilyRunList generation env families :=
  match runs with
  | .nil => .nil
  | .cons head tail =>
      .cons (head.normalizedFamilyRun commonResultLevelWF)
        (tail.normalizedFamilyRuns commonResultLevelWF)

/-- The first exact family alignment owns the shared raw/checker parameter
telescope.  The empty branch is impossible because dependent block analysis
retains a nonempty normalized view. -/
theorem CandidateBlockNormalizedFamilyRunList.paramsTel
    {source : VInductDecl}
    {generation : BlockGenerationChecked source}
    {env blockEnv : VEnv} {Us : List Name}
    {kernelSources : List InductiveType}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateFamily kernelSources}
    {raws : List VInductiveType}
    {roots : CandidateBlockFamilySemanticListRun env blockEnv Us
      candidates raws}
    (runs : CandidateBlockNormalizedFamilyRunList generation env blockEnv Us
      roots generation.families)
    (commonResultLevelWF :
      generation.validated.resultLevel.WF source.uvars) :
    TypeChecker.TelDefEqEvidence env source.uvars []
      generation.block.rawParams generation.block.checked.params := by
  generalize hfamilies : generation.families = families at runs
  cases runs with
  | nil =>
      have hlen : source.types.length = 0 := by
        calc
          source.types.length = generation.families.length :=
            generation.shape.2.2.1.symm
          _ = 0 := by simp [hfamilies]
      have hviewLen : generation.block.normalization.view.types.length = 0 :=
        (Lean4Lean.List.Forall₂.length_eq
          generation.block.normalization.shape.2.2).symm.trans hlen
      have hviewEmpty : generation.block.normalization.view.types = [] :=
        List.eq_nil_of_length_eq_zero hviewLen
      have hnonempty := generation.block.checked.nonempty
      simp [hviewEmpty] at hnonempty
  | @cons _ _ _ _ family _ _ _ _ families head tail =>
      have evidence := (head.evidence commonResultLevelWF).telescope.take
        source.nparams
      have hrawLen : (family.rawParams source.nparams).length =
          source.nparams :=
        (generation.shape.2.2.2.2 family (by
          rw [hfamilies]
          exact .head _)).2.2.1
      have hviewLen : generation.block.checked.params.length =
          source.nparams :=
        generation.shape.2.1.symm.trans generation.shape.1
      have hraw :
          (family.rawParams source.nparams ++
              family.rawIndices source.nparams).take source.nparams =
            family.rawParams source.nparams := by
        let Ps := family.rawParams source.nparams
        let Is := family.rawIndices source.nparams
        have hlen : Ps.length = source.nparams := by
          simpa only [Ps] using hrawLen
        change (Ps ++ Is).take source.nparams = Ps
        rw [← hlen, List.take_append, List.take_length]
        simp
      have hview :
          (generation.block.checked.params ++ family.view.indices).take
              source.nparams = generation.block.checked.params := by
        rw [← hviewLen, List.take_append, List.take_length]
        simp
      have sourceTypes :
          source.types = family.raw :: families.map (·.raw) := by
        rw [← generation.families_map_raw, hfamilies]
        rfl
      have hblock : generation.block.rawParams =
          family.rawParams source.nparams := by
        simp only [NormalizedCheckedBlock.rawParams,
          sourceTypes, blockParams, NormalizedFamily.rawParams]
      rw [hraw, hview] at evidence
      simpa only [hblock] using evidence

/-- Recursively align one family's semantic constructor roots with its exact
normalized pairs and immediately interpret each position as a block run. -/
private def CandidateConstructorSemanticGenerationShapeList.blockRuns
    {source : VInductDecl}
    {generation : BlockGenerationChecked source}
    {env blockEnv : VEnv} {Us : List Name}
    {familyKernelSource : InductiveType}
    {familyCandidate : AddInductive.CandidateFamily familyKernelSource}
    {familyRaw : VInductiveType}
    {familyRoot : CandidateBlockFamilySemanticRun env blockEnv Us
      familyCandidate familyRaw}
    {family : NormalizedFamily}
    (familyRun : CandidateBlockNormalizedFamilyRun generation familyRoot family)
    (normalization : NormalizationBlockRun
      generation.block.normalization env blockEnv)
    (commonResultLevelWF :
      generation.validated.resultLevel.WF source.uvars)
    (paramsTel : TypeChecker.TelDefEqEvidence env source.uvars []
      generation.block.rawParams generation.block.checked.params)
    (familyMember : family ∈ generation.families)
    {kernelSources : List Constructor}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor kernelSources}
    {raws : List VConstVal}
    {roots : CandidateConstructorSemanticListRun blockEnv Us candidates raws} :
    (input : CandidateConstructorSemanticGenerationShapeList
      source blockEnv Us roots) →
    (constructors : List NormalizedCtor) →
    (raws_eq : constructors.map (fun constructor => constructor.raw) = raws) →
    (views_eq : constructors.map (fun constructor => constructor.view.value) =
      roots.roots.views) →
    (membership : ∀ constructor ∈ constructors,
      constructor ∈ family.ctorPairs) →
    NormalizedBlockCtorRunList generation blockEnv
      (constructors.map fun constructor =>
        { owner := family.view.ordinal
          familyName := family.raw.name
          familyIndices := family.view.indices
          ctor := constructor })
  | .nil, [], _, _, _ => .nil
  | .nil, _ :: _, raws_eq, _, _ => by simp at raws_eq
  | .cons _ _, [], raws_eq, _, _ => by simp at raws_eq
  | .cons head tail, constructor :: constructors, raws_eq, views_eq,
      membership => by
    simp only [List.map_cons, List.cons.injEq] at raws_eq
    simp only [List.map_cons,
      CandidateConstructorSemanticListRun.roots,
      CandidateConstructorListRun.views, List.cons.injEq] at views_eq
    exact .cons
      ((head.blockRun family familyMember constructor
          (membership constructor (.head _)) raws_eq.1 views_eq.1).normalizedRun
        familyRun normalization commonResultLevelWF paramsTel familyMember
        (membership constructor (.head _)))
      (tail.blockRuns familyRun normalization commonResultLevelWF
        paramsTel familyMember constructors raws_eq.2 views_eq.2
        (fun constructor member =>
          membership constructor (.tail _ member)))

/-- Assemble the exact constructor-run list owned by one aligned family. -/
def CandidateBlockNormalizedFamilyRun.constructorRuns
    {source : VInductDecl}
    {generation : BlockGenerationChecked source}
    {env blockEnv : VEnv} {Us : List Name}
    {kernelSource : InductiveType}
    {candidate : AddInductive.CandidateFamily kernelSource}
    {raw : VInductiveType}
    {root : CandidateBlockFamilySemanticRun env blockEnv Us candidate raw}
    {family : NormalizedFamily}
    (run : CandidateBlockNormalizedFamilyRun generation root family)
    (normalization : NormalizationBlockRun
      generation.block.normalization env blockEnv)
    (commonResultLevelWF :
      generation.validated.resultLevel.WF source.uvars)
    (paramsTel : TypeChecker.TelDefEqEvidence env source.uvars []
      generation.block.rawParams generation.block.checked.params)
    (familyMember : family ∈ generation.families) :
    NormalizedBlockCtorRunList generation blockEnv family.blockCtors := by
  apply run.constructorShapes.blockRuns run normalization
    commonResultLevelWF paramsTel familyMember family.ctorPairs
  · simpa only [run.raw_eq] using family.ctorPairs_map_raw familyMember
  · calc
      family.ctorPairs.map (fun constructor => constructor.view.value) =
          family.view.value.ctors :=
        family.ctorPairs_map_view_value familyMember
      _ = root.view.ctors := by rw [run.view_eq]
      _ = root.constructors.roots.views := rfl
  · exact fun _ member => member

/-- Concatenate exact constructor-run lists without erasing their list index. -/
def NormalizedBlockCtorRunList.append
    (left : NormalizedBlockCtorRunList generation env leftConstructors)
    (right : NormalizedBlockCtorRunList generation env rightConstructors) :
    NormalizedBlockCtorRunList generation env
      (leftConstructors ++ rightConstructors) :=
  match left with
  | .nil => right
  | .cons head tail => .cons head (tail.append right)

private def CandidateBlockNormalizedFamilyRunList.constructorRunsAux
    {source : VInductDecl}
    {generation : BlockGenerationChecked source}
    {env blockEnv : VEnv} {Us : List Name}
    {kernelSources : List InductiveType}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateFamily kernelSources}
    {raws : List VInductiveType}
    {roots : CandidateBlockFamilySemanticListRun env blockEnv Us
      candidates raws}
    {families : List NormalizedFamily}
    (runs : CandidateBlockNormalizedFamilyRunList generation env blockEnv Us
      roots families)
    (normalization : NormalizationBlockRun
      generation.block.normalization env blockEnv)
    (commonResultLevelWF :
      generation.validated.resultLevel.WF source.uvars)
    (paramsTel : TypeChecker.TelDefEqEvidence env source.uvars []
      generation.block.rawParams generation.block.checked.params)
    (membership : ∀ family ∈ families,
      family ∈ generation.families) :
    NormalizedBlockCtorRunList generation blockEnv
      (families.flatMap (fun family => family.blockCtors)) :=
  match runs with
  | .nil => .nil
  | .cons head tail =>
      (head.constructorRuns normalization commonResultLevelWF paramsTel
          (membership _ (.head _))).append
        (tail.constructorRunsAux normalization commonResultLevelWF
          paramsTel (fun family member =>
            membership family (.tail _ member)))

/-- Flatten every exact family-local constructor run in generation order. -/
def CandidateBlockNormalizedFamilyRunList.constructorRuns
    {source : VInductDecl}
    {generation : BlockGenerationChecked source}
    {env blockEnv : VEnv} {Us : List Name}
    {kernelSources : List InductiveType}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateFamily kernelSources}
    {raws : List VInductiveType}
    {roots : CandidateBlockFamilySemanticListRun env blockEnv Us
      candidates raws}
    (runs : CandidateBlockNormalizedFamilyRunList generation env blockEnv Us
      roots generation.families)
    (normalization : NormalizationBlockRun
      generation.block.normalization env blockEnv)
    (commonResultLevelWF :
      generation.validated.resultLevel.WF source.uvars)
    (paramsTel : TypeChecker.TelDefEqEvidence env source.uvars []
      generation.block.rawParams generation.block.checked.params) :
    NormalizedBlockCtorRunList generation blockEnv generation.flatCtors := by
  have result := runs.constructorRunsAux normalization
    commonResultLevelWF paramsTel (fun _ member => member)
  simpa only [BlockGenerationChecked.flatCtors,
    NormalizedCheckedBlock.flatCtors,
    NormalizedCheckedBlock.familyPairs,
    BlockGenerationChecked.families] using result

/-- Recursively align the retained semantic family roots with the exact
dependent checked-family spine.  The membership map is only a transport from
the definitionally paired list to the generation-owned list; it cannot pick
or reorder a family. -/
private def CandidateBlockNormalizedFamilyRunList.ofCheckedAux
    {source : VInductDecl}
    {generation : BlockGenerationChecked source}
    {env blockEnv : VEnv} {Us : List Name}
    {kernelSources : List InductiveType}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateFamily kernelSources}
    {raws : List VInductiveType}
    {roots : CandidateBlockFamilySemanticListRun env blockEnv Us
      candidates raws}
    {viewTypes : List VInductiveType} {params : List VExpr}
    {ordinal : Nat}
    (input : CandidateBlockFamilySemanticGenerationShapeList source env
      blockEnv Us roots)
    (checked : CheckedFamilies { source with types := viewTypes }
      params ordinal roots.views)
    (checkedRuns : CheckedBlockFamilyRunList env
      generation.validated.resultLevel
      generation.block.checked.families.indices checked)
    (params_eq : generation.block.checked.params = params)
    (uvars_eq : source.uvars = Us.length)
    (membership : ∀ family ∈ pairNormalizedFamilies raws checked.data,
      family ∈ generation.families) :
    CandidateBlockNormalizedFamilyRunList generation env blockEnv Us roots
      (pairNormalizedFamilies raws checked.data) := by
  cases roots with
  | nil =>
      cases input
      cases checked
      cases checkedRuns
      exact .nil
  | cons root roots =>
      cases input with
      | cons head tail =>
          cases checked with
          | cons checkedHead checkedTail =>
              cases checkedRuns with
              | cons checkedHeadRun checkedTailRuns =>
                  exact .cons
                    (head.alignedRun
                      { raw := _
                        view := checkedHead.data }
                      (membership _ (.head _)) checkedHead checkedHeadRun rfl
                      rfl params_eq uvars_eq)
                    (CandidateBlockNormalizedFamilyRunList.ofCheckedAux tail
                      checkedTail checkedTailRuns params_eq uvars_eq
                      (fun family member =>
                        membership family (.tail _ member)))
termination_by raws.length

/-- Align the retained semantic family hierarchy with the exact dependent
checked-family spine selected by block analysis.  This shared witness owns the
constructor shapes as well as the normalized family evidence. -/
def NormalizationCandidateBlockSemanticRun.alignedFamilyRuns
    {source : VInductDecl} {env blockEnv : VEnv} {Us : List Name}
    {kernelSources : List InductiveType}
    {candidate : AddInductive.NormalizationCandidate kernelSources}
    (normalization : NormalizationCandidateBlockSemanticRun env blockEnv Us
      candidate source)
    (generation : BlockGenerationChecked source)
    (analysis : normalization.normalization.checkBlock? =
      some generation.block)
    (shape : normalization.generationShape = true)
    (checkedWF : generation.block.checked.WF env
      generation.validated.resultLevel) :
    CandidateBlockNormalizedFamilyRunList generation env blockEnv Us
      normalization.families generation.families := by
  cases generation with
  | mk validated generationShape =>
      cases validated with
      | mk block commonResultLevel =>
          cases block with
          | mk generationNormalization checked checked_eq =>
              have normalization_eq : generationNormalization =
                  normalization.normalization :=
                Normalization.checkBlock?_normalization analysis
              subst generationNormalization
              have shapes := normalization.generationShapes shape
              have aligned :=
                CandidateBlockNormalizedFamilyRunList.ofCheckedAux shapes
                  checked.families checkedWF.familyRuns rfl
                  normalization.uvars_eq (fun _ member => member)
              exact aligned

/-- Derive the complete generation-indexed family-run list from one retained
block semantic hierarchy and the exact dependent block analysis.  No family
membership proof or positional equation is supplied by the caller. -/
def NormalizationCandidateBlockSemanticRun.familyRuns
    {source : VInductDecl} {env blockEnv : VEnv} {Us : List Name}
    {kernelSources : List InductiveType}
    {candidate : AddInductive.NormalizationCandidate kernelSources}
    (normalization : NormalizationCandidateBlockSemanticRun env blockEnv Us
      candidate source)
    (generation : BlockGenerationChecked source)
    (analysis : normalization.normalization.checkBlock? =
      some generation.block)
    (shape : normalization.generationShape = true)
    (checkedWF : generation.block.checked.WF env
      generation.validated.resultLevel)
    (commonResultLevelWF :
      generation.validated.resultLevel.WF source.uvars) :
    NormalizedFamilyRunList generation env generation.families :=
  CandidateBlockNormalizedFamilyRunList.normalizedFamilyRuns
    (normalization.alignedFamilyRuns generation analysis shape checkedWF)
    commonResultLevelWF

/-- Derive the exact family-major flattened constructor-run list from the
same retained hierarchy and dependent block analysis. -/
def NormalizationCandidateBlockSemanticRun.constructorRuns
    {source : VInductDecl} {env blockEnv : VEnv} {Us : List Name}
    {kernelSources : List InductiveType}
    {candidate : AddInductive.NormalizationCandidate kernelSources}
    (normalization : NormalizationCandidateBlockSemanticRun env blockEnv Us
      candidate source)
    (generation : BlockGenerationChecked source)
    (analysis : normalization.normalization.checkBlock? =
      some generation.block)
    (shape : normalization.generationShape = true)
    (checkedWF : generation.block.checked.WF env
      generation.validated.resultLevel)
    (commonResultLevelWF :
      generation.validated.resultLevel.WF source.uvars) :
    NormalizedBlockCtorRunList generation blockEnv generation.flatCtors := by
  have normalizationRun : NormalizationBlockRun
      generation.block.normalization env blockEnv := by
    have normalization_eq :=
      Normalization.checkBlock?_normalization analysis
    simpa only [normalization_eq] using normalization.normalizationRun
  let aligned := normalization.alignedFamilyRuns generation analysis shape
    checkedWF
  exact aligned.constructorRuns normalizationRun commonResultLevelWF
    (aligned.paramsTel commonResultLevelWF)

/-- Assemble the complete generic block-generation run from one retained
semantic hierarchy and the exact dependent analyzer result. -/
def NormalizationCandidateBlockSemanticRun.blockGenerationRun
    {source : VInductDecl} {env blockEnv : VEnv} {Us : List Name}
    {kernelSources : List InductiveType}
    {candidate : AddInductive.NormalizationCandidate kernelSources}
    (normalization : NormalizationCandidateBlockSemanticRun env blockEnv Us
      candidate source)
    (generation : BlockGenerationChecked source)
    (analysis : normalization.normalization.checkBlock? =
      some generation.block)
    (shape : normalization.generationShape = true)
    (checkedWF : generation.block.checked.WF env
      generation.validated.resultLevel)
    (commonResultLevelWF :
      generation.validated.resultLevel.WF source.uvars) :
    BlockGenerationRun generation env blockEnv := by
  have normalizationRun : NormalizationBlockRun
      generation.block.normalization env blockEnv := by
    have normalization_eq :=
      Normalization.checkBlock?_normalization analysis
    simpa only [normalization_eq] using normalization.normalizationRun
  let aligned := normalization.alignedFamilyRuns generation analysis shape
    checkedWF
  let paramsTel := aligned.paramsTel commonResultLevelWF
  exact {
    normalization := normalizationRun
    checked := checkedWF
    resultLevelWF := commonResultLevelWF
    paramsTel := paramsTel
    families := aligned.normalizedFamilyRuns commonResultLevelWF
    constructors := aligned.constructorRuns normalizationRun
      commonResultLevelWF paramsTel }

/-- Public Theory boundary for arbitrary source-indexed mutual generation. -/
theorem NormalizationCandidateBlockSemanticRun.generationWF
    {source : VInductDecl} {env blockEnv : VEnv} {Us : List Name}
    {kernelSources : List InductiveType}
    {candidate : AddInductive.NormalizationCandidate kernelSources}
    (normalization : NormalizationCandidateBlockSemanticRun env blockEnv Us
      candidate source)
    (generation : BlockGenerationChecked source)
    (analysis : normalization.normalization.checkBlock? =
      some generation.block)
    (shape : normalization.generationShape = true)
    (checkedWF : generation.block.checked.WF env
      generation.validated.resultLevel)
    (commonResultLevelWF :
      generation.validated.resultLevel.WF source.uvars) :
    generation.WF env blockEnv :=
  (normalization.blockGenerationRun generation analysis shape checkedWF
    commonResultLevelWF).wf

/-- Exact dependent closure of one retained arbitrary-block producer result.
The semantic hierarchy is indexed by the candidate stored in that execution,
while the analyzer equation fixes the precise Theory generation descriptor. -/
structure ExactProducedBlockGenerationRun
    {source : VInductDecl} {kernelSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    (env blockEnv : VEnv) (Us : List Name)
    (producedCandidate : ProducedBlockGenerationShapeCandidate source
      kernelSources numNested isUnsafe context)
    (generation : BlockGenerationChecked source) where
  producedSemantic : ProducedNormalizationCandidateBlockSemanticRun
    { context with lctx := {} }
    { context with env := producedCandidate.execution.familyEnv, lctx := {} }
    env blockEnv Us producedCandidate.candidate source
  analysis : producedSemantic.semantic.normalization.checkBlock? =
    some generation.block
  checked : generation.block.checked.WF env
    generation.validated.resultLevel
  resultLevelWF : generation.validated.resultLevel.WF source.uvars

/-- Assemble the complete generic generation run retained by an exact outer
producer closure. -/
def ExactProducedBlockGenerationRun.blockGenerationRun
    (run : ExactProducedBlockGenerationRun env blockEnv Us
      producedCandidate generation) :
    BlockGenerationRun generation env blockEnv :=
  run.producedSemantic.semantic.blockGenerationRun generation run.analysis (by
    simpa only [NormalizationCandidateBlockSemanticRun.generationShape,
      ProducedBlockGenerationShapeCandidate.candidate] using
        producedCandidate.shape) run.checked run.resultLevelWF

/-- Erase checker provenance to the consumer-facing Theory certificate. -/
def ExactProducedBlockGenerationRun.certificate
    {source : VInductDecl} {kernelSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {env blockEnv : VEnv} {Us : List Name}
    {producedCandidate : ProducedBlockGenerationShapeCandidate source
      kernelSources numNested isUnsafe context}
    {generation : BlockGenerationChecked source}
    (run : ExactProducedBlockGenerationRun env blockEnv Us
      producedCandidate generation) :
    BlockGenerationCertificate source env where
  generation := generation
  blockEnv := blockEnv
  wf := run.blockGenerationRun.wf

/-- Combine one exact checker-produced block generation with the concrete
kernel/Theory metadata transaction for that same generation.  Every metadata
phase remains indexed by `generation`; the semantic `WF` field can therefore
no longer be supplied by an unrelated fixture proof. -/
def ExactProducedBlockGenerationRun.addInductBlockTrace
    {source : VInductDecl} {kernelSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {env blockEnv : VEnv} {Us : List Name}
    {producedCandidate : ProducedBlockGenerationShapeCandidate source
      kernelSources numNested isUnsafe context}
    {generation : BlockGenerationChecked source}
    (run : ExactProducedBlockGenerationRun env blockEnv Us
      producedCandidate generation)
    {m₁ m₂ : ConstMap} {env₂ : VEnv}
    (typeMap : ConstMap) (typeEnv : VEnv)
    (ctorMap : ConstMap) (ctorEnv recEnv : VEnv)
    (addTypes : AddInductConstants .induct m₁ env
      source.blockTypeConstants typeMap typeEnv)
    (addCtors : AddInductConstants .ctor typeMap typeEnv
      source.blockConstructorConstants ctorMap ctorEnv)
    (addRecs : AddInductConstants .recursor ctorMap ctorEnv
      generation.recursors m₂ recEnv)
    (recK : RecursorMapKMatches m₂ generation.recursors
      generation.kTarget)
    (addRules : AddDefEqs recEnv generation.generatedRules env₂) :
    AddInductBlockTrace m₁ env source m₂ env₂ where
  generation := generation
  blockEnv := blockEnv
  generation_wf := run.blockGenerationRun.wf
  typeMap := typeMap
  typeEnv := typeEnv
  ctorMap := ctorMap
  ctorEnv := ctorEnv
  recEnv := recEnv
  addTypes := addTypes
  addCtors := addCtors
  addRecs := addRecs
  recK := recK
  addRules := addRules

/-- Close one successful arbitrary-block producer without selecting a
parallel family or constructor list.  The semantic input is indexed by the
candidate retained in the detailed execution, and the universal analyzer
equation is specialized only after that hierarchy has been interpreted. -/
theorem ProducedBlockGenerationShapeCandidate.exactBlockGenerationRun_nonempty
    {source : VInductDecl} {kernelSources : List InductiveType}
    {numNested : Nat} {isUnsafe : Bool}
    {context : AddInductive.Context}
    {env blockEnv : VEnv} {Us : List Name}
    (producedCandidate : ProducedBlockGenerationShapeCandidate source
      kernelSources numNested isUnsafe context)
    (input : NormalizationCandidateBlockSemanticInput env blockEnv Us
      producedCandidate.candidate source)
    (generation : BlockGenerationChecked source)
    (analysis : ∀ semantic : NormalizationCandidateBlockSemanticRun env
        blockEnv Us producedCandidate.candidate source,
      semantic.normalization.checkBlock? = some generation.block)
    (checked : generation.block.checked.WF env
      generation.validated.resultLevel)
    (resultLevelWF : generation.validated.resultLevel.WF source.uvars) :
    Nonempty (ExactProducedBlockGenerationRun env blockEnv Us
      producedCandidate generation) := by
  have familyTypesProduced :
      AddInductive.CandidateFamilyTypeListProduced
        { context with lctx := {} }
        producedCandidate.candidate.families.familyTypes := by
    rw [ProducedBlockGenerationShapeCandidate.candidate,
      AddInductive.NormalizationCandidateExecution.candidate,
      producedCandidate.execution.families.produced.familyTypes_eq]
    exact producedCandidate.execution.familyTypes.produced
  obtain ⟨producedSemantic⟩ := input.exists_ofProduced
    familyTypesProduced
    producedCandidate.execution.families.produced.reindex
  exact ⟨{
    producedSemantic
    analysis := analysis producedSemantic.semantic
    checked
    resultLevelWF }⟩

/-- Derive every family component equation from the minimal structural shape
and the exact dependent analyzer result. -/
private theorem CandidateFamilySemanticGenerationShape.generationRun
    {env : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    {normalization : NormalizationCandidateSemanticRun env Us candidate source}
    {generation : GenerationChecked source}
    (input : CandidateFamilySemanticGenerationShape
      normalization generation)
    (analysis : normalization.root.normalization.generation? =
      some generation) :
    CandidateFamilySemanticGenerationRun normalization generation where
  storedSpine := input.storedSpine
  rawTel := by
    have components := candidateFullTelComponents source.nparams
      candidate.families.singleton.familyType.type.trace.spineLength
      normalization.raw.type (by
        simpa only [NormalizedChecked.rawParams,
          NormalizedChecked.rawIndices,
          NormalizationCandidateSemanticRun.root,
          normalization.root.sourceType_eq generation] using
          input.spineLength_eq)
    simpa only [NormalizedChecked.rawParams,
      NormalizedChecked.rawIndices,
      NormalizationCandidateSemanticRun.root,
      normalization.root.sourceType_eq generation] using components.1
  rawResult := by
    have components := candidateFullTelComponents source.nparams
      candidate.families.singleton.familyType.type.trace.spineLength
      normalization.raw.type (by
        simpa only [NormalizedChecked.rawParams,
          NormalizedChecked.rawIndices,
          NormalizationCandidateSemanticRun.root,
          normalization.root.sourceType_eq generation] using
          input.spineLength_eq)
    simpa only [NormalizedChecked.rawResult,
      NormalizationCandidateSemanticRun.root,
      normalization.root.sourceType_eq generation] using components.2
  viewResult := by
    let As := generation.block.checked.params ++
      generation.block.checked.indices
    have hlength :
        candidate.families.singleton.familyType.type.trace.spineLength =
          As.length := by
      rw [input.spineLength_eq]
      simp only [As, List.length_append]
      rw [generation.shape.2.1, generation.shape.2.2.1]
    have hview : normalization.family.type.view =
        generation.block.checked.type.type := by
      simpa only [NormalizationCandidateSemanticRun.root,
        CandidateFamilySemanticRun.root, CandidateFamilyRun.view] using
        (congrArg (fun ty : VInductiveType => ty.type)
          (normalization.root.familyViewType_eq analysis)).symm
    rw [hview, generation.block.checked.type_eq, hlength]
    simpa only [As, VExpr.forallN_append] using
      generationDropNForallNLength As
        (.sort generation.block.checked.resultLevel)

/-- Derive one normalized constructor alignment after its positional raw/view
equalities have been recovered from the analyzer-owned pair list. -/
private theorem CandidateConstructorSemanticGenerationShape.generationRun
    {source : VInductDecl} {generation : GenerationChecked source}
    {env : VEnv} {Us : List Name}
    {kernelSource : Constructor}
    {candidate : AddInductive.CandidateConstructor kernelSource}
    {raw : VConstVal}
    {root : CandidateConstructorSemanticRun env Us candidate raw}
    {ctor : NormalizedCtor}
    (input : CandidateConstructorSemanticGenerationShape
      (source := source) env Us root)
    (raw_eq : ctor.raw = raw)
    (view_eq : ctor.view.value = root.root.view)
    (hctor : ctor ∈ generation.block.ctorPairs) :
    CandidateSemanticNormalizedCtorRun generation.block env Us root ctor where
  raw_eq := raw_eq
  view_eq := view_eq
  storedSpine := input.storedSpine
  rawTel := by
    have components := candidateFullTelComponents source.nparams
      candidate.type.trace.spineLength raw.type input.spineLength_eq
    simpa only [NormalizedCtor.declaredBinders,
      NormalizedCtor.rawFields, raw_eq] using components.1
  rawResult := by
    have components := candidateFullTelComponents source.nparams
      candidate.type.trace.spineLength raw.type input.spineLength_eq
    simpa only [NormalizedCtor.rawResult, raw_eq] using components.2
  viewResult := by
    let As := generation.block.checked.params ++ ctor.view.fields
    have hlength : candidate.type.trace.spineLength = As.length := by
      rw [input.spineLength_eq]
      simp only [As, List.length_append]
      rw [← raw_eq]
      have hshape := generation.shape.2.2.2.2.2 ctor hctor
      simp only [NormalizedCtor.rawFields] at hshape
      rw [hshape.2.2.1, hshape.2.2.2,
        generation.shape.1.symm.trans generation.shape.2.1]
    have viewType_eq : root.type.view = ctor.view.value.type := by
      exact (congrArg (fun value : VConstVal => value.type) view_eq).symm
    rw [viewType_eq, generation.viewCtorType_eq hctor, hlength]
    exact generationDropNForallNLength As _

/-- Recursively align structural constructor inputs with a pair list whose raw
and checked-value projections are already fixed. -/
private def
    CandidateConstructorSemanticGenerationShapeList.generationRuns
    {source : VInductDecl} {generation : GenerationChecked source}
    {env : VEnv} {Us : List Name}
    {kernelSources : List Constructor}
    {candidates : AddInductive.CandidateList
      AddInductive.CandidateConstructor kernelSources}
    {raws : List VConstVal}
    {roots : CandidateConstructorSemanticListRun env Us candidates raws} :
    (input : CandidateConstructorSemanticGenerationShapeList
      source env Us roots) →
    (ctors : List NormalizedCtor) →
    (raws_eq : ctors.map (·.raw) = raws) →
    (views_eq : ctors.map (fun ctor => ctor.view.value) =
      roots.roots.views) →
    (membership : ∀ ctor ∈ ctors,
      ctor ∈ generation.block.ctorPairs) →
    CandidateSemanticNormalizedCtorListRun generation.block env Us roots ctors
  | .nil, [], _, _, _ => .nil
  | .nil, _ :: _, raws_eq, _, _ => by simp at raws_eq
  | .cons _ _, [], raws_eq, _, _ => by simp at raws_eq
  | .cons head tail, ctor :: ctors, raws_eq, views_eq, membership => by
      simp only [List.map_cons, List.cons.injEq] at raws_eq
      simp only [List.map_cons,
        CandidateConstructorSemanticListRun.roots,
        CandidateConstructorListRun.views, List.cons.injEq] at views_eq
      exact .cons
        (head.generationRun raws_eq.1 views_eq.1
          (membership ctor (.head _)))
        (tail.generationRuns ctors raws_eq.2 views_eq.2
          (fun ctor hctor => membership ctor (.tail _ hctor)))

/-- Exact analysis determines the complete dependent normalized-constructor
list from source-indexed semantic roots and their minimal structural shapes. -/
private def
    CandidateConstructorSemanticGenerationShapeList.ofAnalysis
    {env : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    {normalization : NormalizationCandidateSemanticRun env Us candidate source}
    {generation : GenerationChecked source}
    (input : CandidateConstructorSemanticGenerationShapeList source
      normalization.family.typeEnv Us normalization.family.constructors)
    (analysis : normalization.root.normalization.generation? =
      some generation) :
    CandidateSemanticNormalizedCtorListRun generation.block
      normalization.family.typeEnv Us normalization.family.constructors
      generation.block.ctorPairs := by
  apply input.generationRuns
  · simpa only [NormalizationCandidateSemanticRun.root,
      normalization.root.sourceType_eq generation] using
      generation.rawCtors_eq
  · have viewType_eq := normalization.root.familyViewType_eq analysis
    calc
      generation.block.ctorPairs.map (fun ctor => ctor.view.value) =
          generation.block.checked.constructors.map (·.value) := by
        simpa only [List.map_map, Function.comp_def] using
          congrArg (List.map (·.value)) generation.viewCtors_eq
      _ = generation.block.checked.type.ctors := by
        rw [generation.block.checked.constructors_eq, List.map_map]
        change generation.block.checked.type.ctors.map (fun c => c) = _
        exact List.map_id' generation.block.checked.type.ctors
      _ = normalization.family.root.view.ctors := by
        simpa only [NormalizationCandidateSemanticRun.root] using
          congrArg (fun ty : VInductiveType => ty.ctors) viewType_eq
      _ = normalization.family.constructors.roots.views := rfl
  · exact fun _ hctor => hctor

/-- Recover every analyzer-owned constructor pairing from the retained
semantic hierarchy, dependent analysis, and executable structural gate.

This projection deliberately does not require `Checked.WF`: it exposes only
the exact source/candidate/raw/view alignment needed to derive that semantic
fact in the constructor-validation layer. -/
def NormalizationCandidateSemanticRun.constructorGenerationRuns
    {env : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    (normalization : NormalizationCandidateSemanticRun env Us candidate source)
    (generation : GenerationChecked source)
    (analysis : normalization.root.normalization.generation? =
      some generation)
    (shape : normalization.generationShape = true) :
    CandidateSemanticNormalizedCtorListRun generation.block
      normalization.family.typeEnv Us normalization.family.constructors
      generation.block.ctorPairs := by
  simp only [NormalizationCandidateSemanticRun.generationShape,
    normalizationCandidateGenerationShape, Bool.and_eq_true,
    beq_iff_eq] at shape
  exact (CandidateConstructorSemanticGenerationShapeList.ofCheck
    normalization.family.constructors shape.2).ofAnalysis analysis

/-- Reconstruct the established semantic-generation run from the reduced
shape boundary.  No raw/view pair or component equation is supplied here. -/
def GenerationCandidateSemanticShapeRun.run
    {env : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    {normalization : NormalizationCandidateSemanticRun env Us candidate source}
    {generation : GenerationChecked source}
    (input : GenerationCandidateSemanticShapeRun normalization generation) :
    GenerationCandidateSemanticRun normalization generation where
  analysis := input.analysis
  checked := input.checked
  family := input.family.generationRun input.analysis
  constructors := input.constructors.ofAnalysis input.analysis

/-- Reconstruct well-formedness of the post-family environment from the
retained pre-family context, candidate raw/view equality, checked family view,
and exact raw-family insertion.  Fixtures therefore do not supply this semantic
consequence independently. -/
theorem GenerationCandidateRun.typeEnv_wf
    {env : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    {normalization : NormalizationCandidateRun env Us candidate source}
    {generation : GenerationChecked source}
    (run : GenerationCandidateRun normalization generation) :
    VEnv.WF normalization.family.typeEnv := by
  have henv : VEnv.WF env := by
    simpa only [normalization.family.typeRun.venv_eq] using
      normalization.family.typeRun.contextRun.context.Ewf
  obtain ⟨_, hfamily⟩ := normalization.family.typeRun.evidence
  have hview : env.IsType Us.length [] normalization.family.viewType := by
    simpa only [← generation.block.uvars_eq, normalization.uvars_eq,
      run.familyView_eq] using run.checked.family_isType
  have hraw : env.IsType Us.length [] normalization.raw.type :=
    VEnv.IsType.defeqU_l henv trivial hfamily.isDefEq.toU.symm hview
  have hrawWF : normalization.raw.toVConstant.WF env := by
    show env.IsType normalization.raw.uvars [] normalization.raw.type
    simpa only [normalization.family.uvars_eq] using hraw
  obtain ⟨ds, hds⟩ := henv
  exact ⟨.axiom normalization.raw.toVConstVal :: ds,
    .decl (.axiom hrawWF normalization.family.addType) hds⟩

/-- Type the raw family constant at the analyzer-selected family view in the
post-family environment.  The proof combines the exact raw insertion, the
candidate's whole-family equality, and checked family well-formedness once;
constructors can then share this result. -/
theorem GenerationCandidateRun.familyConst_hasType
    {env : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    {normalization : NormalizationCandidateRun env Us candidate source}
    {generation : GenerationChecked source}
    (run : GenerationCandidateRun normalization generation) :
    normalization.family.typeEnv.HasType source.uvars []
      (.const generation.block.sourceType.name
        (VLevel.params source.uvars))
      generation.block.checked.type.type := by
  have sourceType_eq : generation.block.sourceType = normalization.raw := by
    have h : [generation.block.sourceType] = [normalization.raw] :=
      generation.block.source_types_eq.symm.trans normalization.raw_types_eq
    injection h
  have hlookup : normalization.family.typeEnv.constants
      normalization.raw.name = some normalization.raw.toVConstant :=
    VEnv.addConst_self normalization.family.addType
  have hconstRaw := VEnv.HasType.const0 hlookup
    (run.typeEnv_wf.ordered.constWF hlookup)
  have hconstRaw' : normalization.family.typeEnv.HasType Us.length []
      (.const normalization.raw.name (VLevel.params Us.length))
      normalization.raw.type := by
    simpa only [normalization.family.uvars_eq] using hconstRaw
  obtain ⟨_, hfamily⟩ := normalization.family.typeRun.evidence
  have hchecked := run.checked.mono
    (VEnv.addConst_le normalization.family.addType)
  have hviewType : normalization.family.typeEnv.IsType Us.length []
      normalization.family.viewType := by
    simpa only [← generation.block.uvars_eq, normalization.uvars_eq,
      run.familyView_eq] using hchecked.family_isType
  obtain ⟨_, hviewType⟩ := hviewType
  have hfamilyExact :=
    (hfamily.isDefEq.toU.mono
      (VEnv.addConst_le normalization.family.addType)).of_r
        run.typeEnv_wf trivial hviewType
  have hconstView : normalization.family.typeEnv.HasType Us.length []
      (.const normalization.raw.name (VLevel.params Us.length))
      normalization.family.viewType :=
    hfamilyExact.defeq hconstRaw'
  simpa only [normalization.uvars_eq, sourceType_eq,
    run.familyView_eq] using hconstView

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
  have familyEvidence := run.family.evidence run.familyView_eq
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
    (run.checked.mono (VEnv.addConst_le normalization.family.addType))
    run.familyConst_hasType (fun _ hctor => hctor)
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
    (recK : RecursorKMatches addRec.info package.generation.kTarget)
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
  recK := recK
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

/-- Attach exact executable provenance to an already verified singleton
generation run.

Both premises are indexed by the same kernel source and dependent candidate:
the executable equation therefore cannot be reused for a different semantic
run, reordered constructor list, or caller-selected view.  Conversely, the
equation supplies no semantic authority by itself; all Theory meaning remains
in `run`. -/
def GenerationCandidateRun.producedPackage
    {env : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    {normalization : NormalizationCandidateRun env Us candidate source}
    {generation : GenerationChecked source}
    (run : GenerationCandidateRun normalization generation)
    (context : AddInductive.Context)
    (nparams numNested : Nat) (isUnsafe : Bool)
    (produced :
      AddInductive.buildNormalizationCandidate nparams
          [kernelSource] numNested isUnsafe context = .ok candidate) :
    ProducedGenerationCandidatePackage env Us where
  package := run.package
  context := context
  nparams := nparams
  numNested := numNested
  isUnsafe := isUnsafe
  produced := produced

/-- Package the no-parallel-run semantic assembler at the existing public
boundary. -/
def GenerationCandidateSemanticRun.package
    {env : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    {normalization : NormalizationCandidateSemanticRun env Us candidate source}
    {generation : GenerationChecked source}
    (run : GenerationCandidateSemanticRun normalization generation) :
    GenerationCandidatePackage env Us :=
  run.run.package

/-- Attach the exact successful outer metadata call directly to a retained
semantic-generation owner. -/
def GenerationCandidateSemanticRun.producedPackage
    {env : VEnv} {Us : List Name}
    {kernelSource : InductiveType} {source : VInductDecl}
    {candidate : AddInductive.NormalizationCandidate [kernelSource]}
    {normalization : NormalizationCandidateSemanticRun env Us candidate source}
    {generation : GenerationChecked source}
    (run : GenerationCandidateSemanticRun normalization generation)
    (context : AddInductive.Context)
    (nparams numNested : Nat) (isUnsafe : Bool)
    (produced :
      AddInductive.buildNormalizationCandidate nparams
          [kernelSource] numNested isUnsafe context = .ok candidate) :
    ProducedGenerationCandidatePackage env Us :=
  run.run.producedPackage context nparams numNested isUnsafe produced

/-
The evidence types mention exact verifier executions, so the semantic
interpretation roots below intentionally inherit the same transitional Verify
closure as `WhnfRun.isDefEq`. Exact guards ensure that the generic assembler
does not silently widen it. Theory-only helper closures are guarded by
`Tests.TheoryConsumerSurface` without importing Verify.
-/

/--
info: 'Lean4Lean.TypeChecker.AddInductConstant.safePrimitives' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentHashMap.findAux_isSome,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms TypeChecker.AddInductConstant.safePrimitives

/--
info: 'Lean4Lean.TypeChecker.CandidateContextRun.context_env' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateContextRun.context_env

/--
info: 'Lean4Lean.TypeChecker.CandidateContextRun.context_lctx' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateContextRun.context_lctx

/--
info: 'Lean4Lean.TypeChecker.CandidateContextRun.context_safety' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateContextRun.context_safety

/--
info: 'Lean4Lean.TypeChecker.CandidateContextRun.context_lparams' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateContextRun.context_lparams

/--
info: 'Lean4Lean.TypeChecker.CandidateContextRun.context_fuel' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateContextRun.context_fuel

/--
info: 'Lean4Lean.TypeChecker.CandidateExprRun.view_isType_of_terminalSort' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateExprRun.view_isType_of_terminalSort

/--
info: 'Lean4Lean.TypeChecker.CandidateExprSemanticRootRun.source_isType_of_terminalSort' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateExprSemanticRootRun.source_isType_of_terminalSort

/--
info: 'Lean4Lean.TypeChecker.CandidateExprRun.viewResult_of_terminalSort' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateExprRun.viewResult_of_terminalSort

/--
info: 'Lean4Lean.TypeChecker.CandidateExprSemanticRootRun.viewResult_of_terminalSort' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateExprSemanticRootRun.viewResult_of_terminalSort

/--
info: 'Lean4Lean.TypeChecker.CandidateExprSemanticRootRun.viewParameters' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateExprSemanticRootRun.viewParameters

/--
info: 'Lean4Lean.TypeChecker.CandidateExprSemanticRootRun.viewIndices' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateExprSemanticRootRun.viewIndices

/--
info: 'Lean4Lean.VInductDecl.CandidateFamilyStagedInput' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CandidateFamilyStagedInput

/--
info: 'Lean4Lean.VInductDecl.CandidateFamilyStagedInput.rawWF' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms CandidateFamilyStagedInput.rawWF

/--
info: 'Lean4Lean.VInductDecl.CandidateFamilyStagedInput.postContext' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms CandidateFamilyStagedInput.postContext

/--
info: 'Lean4Lean.VInductDecl.CandidateFamilyStagedInput.postContextRun' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms CandidateFamilyStagedInput.postContextRun

/--
info: 'Lean4Lean.VInductDecl.CandidateFamilyStagedInput.postFamily' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms CandidateFamilyStagedInput.postFamily


/--
info: 'Lean4Lean.TypeChecker.CandidateExprSemanticRootInput.exists' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateExprSemanticRootInput.exists

/--
info: 'Lean4Lean.VInductDecl.CandidateConstructorSemanticListInput.exists' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms CandidateConstructorSemanticListInput.exists

/--
info: 'Lean4Lean.VInductDecl.NormalizationCandidateSemanticInput.exists_ofProduced' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms NormalizationCandidateSemanticInput.exists_ofProduced

/--
info: 'Lean4Lean.VInductDecl.StagedNormalizationCandidateSemanticInput.exists' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms StagedNormalizationCandidateSemanticInput.exists

/--
info: 'Lean4Lean.VInductDecl.CandidateFamilySemanticGenerationRun.run' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms CandidateFamilySemanticGenerationRun.run

/--
info: 'Lean4Lean.VInductDecl.CandidateSemanticNormalizedCtorListRun.run' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms CandidateSemanticNormalizedCtorListRun.run

/--
info: 'Lean4Lean.VInductDecl.GenerationCandidateSemanticRun.run' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms GenerationCandidateSemanticRun.run

/--
info: 'Lean4Lean.VInductDecl.GenerationCandidateSemanticShapeRun.run' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms GenerationCandidateSemanticShapeRun.run

/--
info: 'Lean4Lean.VInductDecl.candidateConstructorSemanticGenerationShape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms candidateConstructorSemanticGenerationShape

/--
info: 'Lean4Lean.VInductDecl.normalizationCandidateGenerationShape' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms normalizationCandidateGenerationShape

/--
info: 'Lean4Lean.VInductDecl.CandidateConstructorSemanticGenerationShapeList.ofCheck' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CandidateConstructorSemanticGenerationShapeList.ofCheck

/--
info: 'Lean4Lean.VInductDecl.NormalizationCandidateSemanticRun.generationShape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NormalizationCandidateSemanticRun.generationShape

/--
info: 'Lean4Lean.VInductDecl.produceGenerationShapeCandidate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms produceGenerationShapeCandidate

/--
info: 'Lean4Lean.VInductDecl.produceGenerationShapeCandidate_eq_ok' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms produceGenerationShapeCandidate_eq_ok

/--
info: 'Lean4Lean.VInductDecl.candidateBlockFamilySemanticGenerationShape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms candidateBlockFamilySemanticGenerationShape

/--
info: 'Lean4Lean.VInductDecl.normalizationCandidateBlockGenerationShape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms normalizationCandidateBlockGenerationShape

/--
info: 'Lean4Lean.VInductDecl.CandidateBlockFamilySemanticGenerationShapeList.ofCheck' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CandidateBlockFamilySemanticGenerationShapeList.ofCheck

/--
info: 'Lean4Lean.VInductDecl.NormalizationCandidateBlockSemanticRun.generationShape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NormalizationCandidateBlockSemanticRun.generationShape

/--
info: 'Lean4Lean.VInductDecl.NormalizationCandidateBlockSemanticRun.generationShapes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NormalizationCandidateBlockSemanticRun.generationShapes

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockGenerationShapeCandidate.candidate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ProducedBlockGenerationShapeCandidate.candidate

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockGenerationShapeCandidate.produced' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ProducedBlockGenerationShapeCandidate.produced

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockGenerationShapeCandidate.familyValidationResult' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ProducedBlockGenerationShapeCandidate.familyValidationResult

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockGenerationShapeCandidate.familyValidationResult_run' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ProducedBlockGenerationShapeCandidate.familyValidationResult_run

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockGenerationShapeCandidate.familyValidation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ProducedBlockGenerationShapeCandidate.familyValidation

/--
info: 'Lean4Lean.VInductDecl.ProducedBlockGenerationShapeCandidate.constructorValidation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms ProducedBlockGenerationShapeCandidate.constructorValidation

/--
info: 'Lean4Lean.VInductDecl.produceBlockGenerationShapeCandidate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms produceBlockGenerationShapeCandidate

/--
info: 'Lean4Lean.VInductDecl.produceBlockGenerationShapeCandidate_eq_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms produceBlockGenerationShapeCandidate_eq_ok
/--
info: 'Lean4Lean.VInductDecl.GenerationCandidateSemanticRun.package' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms GenerationCandidateSemanticRun.package

/--
info: 'Lean4Lean.VInductDecl.GenerationCandidateSemanticRun.producedPackage' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms GenerationCandidateSemanticRun.producedPackage

/--
info: 'Lean4Lean.TypeChecker.VState.WF.empty_of_reserves' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.eqv_eq,
 Level.instLawfulBEqLevel,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
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
info: 'Lean4Lean.TypeChecker.CandidateLocalContextRun.push' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateLocalContextRun.push

/--
info: 'Lean4Lean.TypeChecker.CandidateContextRun.rootTranslation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateContextRun.rootTranslation

/--
info: 'Lean4Lean.TypeChecker.CandidateContextRun.getTypeTranslation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateContextRun.getTypeTranslation

/--
info: 'Lean4Lean.TypeChecker.FamilyComparisonRhsLocal.isDefEqRun' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms TypeChecker.FamilyComparisonRhsLocal.isDefEqRun

/--
info: 'Lean4Lean.TypeChecker.familyTypeParameterComparison_localResult_of_first' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms TypeChecker.familyTypeParameterComparison_localResult_of_first

/--
info: 'Lean4Lean.TypeChecker.FamilyParameterSemanticSpine.rawTerminal_defeq' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms TypeChecker.FamilyParameterSemanticSpine.rawTerminal_defeq

/--
info: 'Lean4Lean.TypeChecker.FamilyParameterSemanticSpine.specializeTerminalDefEq' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms TypeChecker.FamilyParameterSemanticSpine.specializeTerminalDefEq

/--
info: 'Lean4Lean.TypeChecker.familyTypeParameterComparison_semanticSpine_of_later' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms TypeChecker.familyTypeParameterComparison_semanticSpine_of_later

/--
info: 'Lean4Lean.TypeChecker.familyTypeParameterComparison_semanticPrefix_of_later' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms TypeChecker.familyTypeParameterComparison_semanticPrefix_of_later

/--
info: 'Lean4Lean.TypeChecker.familyTypeParameterComparison_semanticRuns_of_later' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms TypeChecker.familyTypeParameterComparison_semanticRuns_of_later

/--
info: 'Lean4Lean.AddInductive.NormalizationCandidateExecution.familyParameterComparisonRhsLocal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms AddInductive.NormalizationCandidateExecution.familyParameterComparisonRhsLocal

/--
info: 'Lean4Lean.TypeChecker.CandidateContextRun.root' depends on axioms: [propext,
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
 Classical.choice,
 Quot.sound,
 Expr.eqv_eq,
 Level.instLawfulBEqLevel,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
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
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms TypeChecker.candidateCheckTypeStep_exists_translation

/--
info: 'Lean4Lean.TypeChecker.IsDefEqRun.ofCandidateStep' depends on axioms: [propext, Classical.choice, Quot.sound]
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
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
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
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms TypeChecker.candidateTypeAnnotation_exists_translation

/--
info: 'Lean4Lean.TypeChecker.consumeTypeAnnotations_exists_translation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms TypeChecker.consumeTypeAnnotations_exists_translation

/--
info: 'Lean4Lean.TypeChecker.FamilyParameterIndexBoundary.indexDomainTranslation_of_forall' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  TypeChecker.FamilyParameterIndexBoundary.indexDomainTranslation_of_forall

/--
info: 'Lean4Lean.TypeChecker.FamilyParameterIndexBoundary.annotationTranslation_of_forall' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  TypeChecker.FamilyParameterIndexBoundary.annotationTranslation_of_forall

/--
info: 'Lean4Lean.TypeChecker.FamilyParameterIndexBoundary.IndexDomainRun.consumed_type' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  TypeChecker.FamilyParameterIndexBoundary.IndexDomainRun.consumed_type

/--
info: 'Lean4Lean.TypeChecker.FamilyParameterIndexBoundary.IndexDomainRun.pushContext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.eqv_eq,
 Level.instLawfulBEqLevel,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms
  TypeChecker.FamilyParameterIndexBoundary.IndexDomainRun.pushContext

/--
info: 'Lean4Lean.TypeChecker.FamilyParameterIndexBoundary.IndexDomainRun.bodyTranslation' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms
  TypeChecker.FamilyParameterIndexBoundary.IndexDomainRun.bodyTranslation

/--
info: 'Lean4Lean.TypeChecker.FamilyParameterIndexBoundary.IndexDomainRun.instantiatedBodyTranslation' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound,
 Expr.eqv_eq,
 Expr.instantiate1_eq,
 Level.instLawfulBEqLevel,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms
  TypeChecker.FamilyParameterIndexBoundary.IndexDomainRun.instantiatedBodyTranslation

/--
info: 'Lean4Lean.TypeChecker.FamilyParameterIndexBoundary.IndexDomainAdvance.toBoundary' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.eqv_eq,
 Level.instLawfulBEqLevel,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms
  TypeChecker.FamilyParameterIndexBoundary.IndexDomainAdvance.toBoundary

/--
info: 'Lean4Lean.TypeChecker.FamilyParameterIndexBoundary.IndexDomainAdvance.result_eq_outer' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.eqv_eq,
 Level.instLawfulBEqLevel,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms
  TypeChecker.FamilyParameterIndexBoundary.IndexDomainAdvance.result_eq_outer

/--
info: 'Lean4Lean.TypeChecker.FamilyParameterIndexBoundary.IndexDomainRun.advance' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms
  TypeChecker.FamilyParameterIndexBoundary.IndexDomainRun.advance

/--
info: 'Lean4Lean.TypeChecker.FamilyParameterIndexBoundary.progress' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms TypeChecker.FamilyParameterIndexBoundary.progress

/--
info: 'Lean4Lean.TypeChecker.FamilyParameterIndexBoundary.annotationTranslation_or_terminal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  TypeChecker.FamilyParameterIndexBoundary.annotationTranslation_or_terminal

/--
info: 'Lean4Lean.AddInductive.FamilyParameterComparisonBlockTrace.exists_secondContinuation_of_secondTelescope' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  AddInductive.FamilyParameterComparisonBlockTrace.exists_secondContinuation_of_secondTelescope

/--
info: 'Lean4Lean.AddInductive.FamilyParameterComparisonBlockTrace.secondContinuation?_dIdx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  AddInductive.FamilyParameterComparisonBlockTrace.secondContinuation?_dIdx

/--
info: 'Lean4Lean.AddInductive.FamilyParameterComparisonBlockTrace.headContinuation?_dIdx' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  AddInductive.FamilyParameterComparisonBlockTrace.headContinuation?_dIdx

/--
info: 'Lean4Lean.AddInductive.FamilyTypeParameterComparisonTrace.result_params_size_of_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  AddInductive.FamilyTypeParameterComparisonTrace.result_params_size_of_later

/--
info: 'Lean4Lean.AddInductive.FamilyParameterComparisonBlockTrace.headContinuation?_laterInvariant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  AddInductive.FamilyParameterComparisonBlockTrace.headContinuation?_laterInvariant

/--
info: 'Lean4Lean.AddInductive.FamilyParameterComparisonBlockTrace.exists_predecessor_of_secondContinuation?' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms
  AddInductive.FamilyParameterComparisonBlockTrace.exists_predecessor_of_secondContinuation?

/--
info: 'Lean4Lean.TypeChecker.FamilyParameterIndexBoundary.IndexDomainChain.endpointContextRun' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.eqv_eq,
 Level.instLawfulBEqLevel,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms
  TypeChecker.FamilyParameterIndexBoundary.IndexDomainChain.endpointContextRun

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
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
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
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateExprRun.exists_ofCandidateFVars

/--
info: 'Lean4Lean.TypeChecker.WhnfRun.ofCandidateStep' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms TypeChecker.WhnfRun.ofCandidateStep

/--
info: 'Lean4Lean.TypeChecker.CheckTypeRun.ofCandidateStep' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms TypeChecker.CheckTypeRun.ofCandidateStep

/--
info: 'Lean4Lean.TypeChecker.CandidateNodeRun.ofCandidate' depends on axioms: [propext, Classical.choice, Quot.sound]
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
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
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
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
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
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateExprRun.evidence

/--
info: 'Lean4Lean.TypeChecker.CandidateExprRun.source_tr' depends on axioms: [propext, Classical.choice, Quot.sound]
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
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
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
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
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
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms TypeChecker.TelDefEqEvidence.telDefEq

/--
info: 'Lean4Lean.TypeChecker.TelDefEqEvidence.ofTelDefEq' depends on axioms: [propext, Classical.choice, Quot.sound]
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
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
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
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateExprRun.spineEvidence

/--
info: 'Lean4Lean.TypeChecker.CandidateExprRun.annotationSpineEvidence' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateExprRun.annotationSpineEvidence

/--
info: 'Lean4Lean.TypeChecker.CandidateExprRun.annotationSpineContext' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateExprRun.annotationSpineContext

/--
info: 'Lean4Lean.TypeChecker.CandidateExprSemanticRootRun.annotationSpineEvidence' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms
  TypeChecker.CandidateExprSemanticRootRun.annotationSpineEvidence

/--
info: 'Lean4Lean.TypeChecker.CandidateExprSemanticRootRun.annotationSpineContext' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms
  TypeChecker.CandidateExprSemanticRootRun.annotationSpineContext

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
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateExprSpineRun.evidenceAt

/--
info: 'Lean4Lean.VInductDecl.GenerationCandidateRun.normalization_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms GenerationCandidateRun.normalization_eq

/--
info: 'Lean4Lean.VInductDecl.NormalizationCandidateRun.sourceType_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NormalizationCandidateRun.sourceType_eq

/--
info: 'Lean4Lean.VInductDecl.NormalizationCandidateRun.familyViewType_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms NormalizationCandidateRun.familyViewType_eq

/--
info: 'Lean4Lean.VInductDecl.GenerationCandidateRun.familyView_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms GenerationCandidateRun.familyView_eq

/--
info: 'Lean4Lean.VInductDecl.GenerationCandidateRun.typeEnv_wf' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms GenerationCandidateRun.typeEnv_wf

/--
info: 'Lean4Lean.VInductDecl.GenerationCandidateRun.familyConst_hasType' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms GenerationCandidateRun.familyConst_hasType

/--
info: 'Lean4Lean.VInductDecl.CandidateNormalizedCtorRun.rightType_ofChecked' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms CandidateNormalizedCtorRun.rightType_ofChecked

/--
info: 'Lean4Lean.VInductDecl.CandidateNormalizedCtorRun.viewTel_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms CandidateNormalizedCtorRun.viewTel_eq

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
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
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
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms GenerationCandidateRun.wf

/--
info: 'Lean4Lean.VInductDecl.CandidateConstructorListRun.sameHeaders' depends on axioms: [propext,
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
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms CandidateConstructorListRun.evidence

/--
info: 'Lean4Lean.VInductDecl.NormalizationCandidateRun.normalization' depends on axioms: [propext,
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
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
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
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
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
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms GenerationRun.wf

/--
info: 'Lean4Lean.VInductDecl.NormalizedFamilyRun.wf' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms NormalizedFamilyRun.wf

/--
info: 'Lean4Lean.VInductDecl.NormalizedBlockCtorRun.wf' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms NormalizedBlockCtorRun.wf

/--
info: 'Lean4Lean.VInductDecl.BlockGenerationRun.wf' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms BlockGenerationRun.wf


/--
info: 'Lean4Lean.VInductDecl.GenerationCandidateRun.package' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms GenerationCandidateRun.package

/--
info: 'Lean4Lean.VInductDecl.GenerationCandidateRun.producedPackage' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms GenerationCandidateRun.producedPackage

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
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
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
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms GenerationCandidatePackage.addInductTrace

/--
info: 'Lean4Lean.VInductDecl.StagedNormalizationCandidateSemanticInput.constructorValidation_run' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms StagedNormalizationCandidateSemanticInput.constructorValidation_run

/--
info: 'Lean4Lean.VInductDecl.NormalizationBlockRun.wf' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms NormalizationBlockRun.wf

/--
info: 'Lean4Lean.VInductDecl.CandidateBlockFamilySemanticListRun.sameHeaders' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms CandidateBlockFamilySemanticListRun.sameHeaders

/--
info: 'Lean4Lean.VInductDecl.CandidateBlockFamilySemanticListRun.sourceTranslations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms CandidateBlockFamilySemanticListRun.sourceTranslations

/--
info: 'Lean4Lean.VInductDecl.CandidateBlockFamilySemanticListRun.headResultLevel' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CandidateBlockFamilySemanticListRun.headResultLevel

/--
info: 'Lean4Lean.VInductDecl.CandidateBlockFamilySemanticListRun.evidence' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms CandidateBlockFamilySemanticListRun.evidence

/--
info: 'Lean4Lean.VInductDecl.CandidateBlockFamilySemanticInput.exists' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms CandidateBlockFamilySemanticInput.exists

/--
info: 'Lean4Lean.VInductDecl.CandidateBlockFamilySemanticListInput.exists' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms CandidateBlockFamilySemanticListInput.exists

/--
info: 'Lean4Lean.VInductDecl.NormalizationCandidateBlockSemanticInput.exists' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms NormalizationCandidateBlockSemanticInput.exists

/--
info: 'Lean4Lean.VInductDecl.NormalizationCandidateBlockSemanticInput.exists_ofProduced' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms NormalizationCandidateBlockSemanticInput.exists_ofProduced

/--
info: 'Lean4Lean.VInductDecl.canonicalizeConstructorParams_telN' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms canonicalizeConstructorParams_telN

/--
info: 'Lean4Lean.VInductDecl.canonicalizeFamilyParamsList_parameterSurfaces' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms canonicalizeFamilyParamsList_parameterSurfaces

/--
info: 'Lean4Lean.VInductDecl.sameTypeHeaders_canonicalizeParams_right' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms sameTypeHeaders_canonicalizeParams_right

/--
info: 'Lean4Lean.VInductDecl.Normalization.canonicalizeSharedParams' depends on axioms: [propext]
-/
#guard_msgs in
#print axioms Normalization.canonicalizeSharedParams

/--
info: 'Lean4Lean.TypeChecker.familyTypeParameterComparison_localResult_of_later' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms TypeChecker.familyTypeParameterComparison_localResult_of_later

/--
info: 'Lean4Lean.AddInductive.FamilyParameterComparisonBlockTrace.headContinuation?_nextLocalState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms AddInductive.FamilyParameterComparisonBlockTrace.headContinuation?_nextLocalState

/--
info: 'Lean4Lean.AddInductive.FamilyParameterComparisonBlockTrace.headContinuation?_nextParams_eq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms AddInductive.FamilyParameterComparisonBlockTrace.headContinuation?_nextParams_eq

/--
info: 'Lean4Lean.AddInductive.FamilyParameterComparisonBlockTrace.headContinuation?_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms AddInductive.FamilyParameterComparisonBlockTrace.headContinuation?_context

/--
info: 'Lean4Lean.VInductDecl.CandidateBlockFamilySemanticListRun.headSourceTranslation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms CandidateBlockFamilySemanticListRun.headSourceTranslation

/--
info: 'Lean4Lean.VInductDecl.CandidateBlockLaterFamilyValidationCursor.headSourceTranslation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms CandidateBlockLaterFamilyValidationCursor.headSourceTranslation

/--
info: 'Lean4Lean.VInductDecl.CandidateBlockLaterFamilyValidationCursor.headRootWhnf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CandidateBlockLaterFamilyValidationCursor.headRootWhnf

/--
info: 'Lean4Lean.VInductDecl.CandidateBlockLaterFamilyValidationCursor.headContextRun_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CandidateBlockLaterFamilyValidationCursor.headContextRun_context

/--
info: 'Lean4Lean.VInductDecl.CandidateBlockLaterFamilyValidationCursor.headLocalState' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CandidateBlockLaterFamilyValidationCursor.headLocalState

/--
info: 'Lean4Lean.VInductDecl.CandidateBlockFamilyValidationCursor.sourceTranslations' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms CandidateBlockFamilyValidationCursor.sourceTranslations

/--
info: 'Lean4Lean.VInductDecl.CandidateBlockFamilyValidationCursor.comparisons_length' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CandidateBlockFamilyValidationCursor.comparisons_length

/--
info: 'Lean4Lean.VInductDecl.CandidateBlockLaterFamilyValidationCursor.headContinuation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CandidateBlockLaterFamilyValidationCursor.headContinuation

/--
info: 'Lean4Lean.VInductDecl.CandidateBlockLaterFamilyValidationCursor.advance' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms CandidateBlockLaterFamilyValidationCursor.advance

/--
info: 'Lean4Lean.TypeChecker.CandidateExprTrace.head_find_terminal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateExprTrace.head_find_terminal

/--
info: 'Lean4Lean.TypeChecker.getType_fvar_of_find' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms TypeChecker.getType_fvar_of_find

/--
info: 'Lean4Lean.AddInductive.FamilyTypeParameterComparisonTrace.result_findOld' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms AddInductive.FamilyTypeParameterComparisonTrace.result_findOld

/--
info: 'Lean4Lean.TypeChecker.CandidateAnnotationSpine.root_fvars' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateAnnotationSpine.root_fvars

/--
info: 'Lean4Lean.TypeChecker.CandidateAnnotationCursor.root_fvars' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateAnnotationCursor.root_fvars

/--
info: 'Lean4Lean.TypeChecker.CandidateAnnotationSpine.terminalShape' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateAnnotationSpine.terminalShape

/--
info: 'Lean4Lean.VInductDecl.CandidateBlockLaterFamilyValidationCursor.advanceHead' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms CandidateBlockLaterFamilyValidationCursor.advanceHead

/--
info: 'Lean4Lean.VInductDecl.CandidateFamilyValidationAnnotationList.ofProduced' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CandidateFamilyValidationAnnotationList.ofProduced

/--
info: 'Lean4Lean.VInductDecl.CandidateBlockFamilyAnnotationSpineList.exists' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms CandidateBlockFamilyAnnotationSpineList.exists

/--
info: 'Lean4Lean.AddInductive.CandidateExprTrace.mainSpineAt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms AddInductive.CandidateExprTrace.mainSpineAt

/--
info: 'Lean4Lean.AddInductive.CandidateExprTrace.MainSpineAt.position' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms AddInductive.CandidateExprTrace.MainSpineAt.position

/--
info: 'Lean4Lean.TypeChecker.CandidateAnnotationSpine.mainPositionSuffix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms TypeChecker.CandidateAnnotationSpine.mainPositionSuffix

/--
info: 'Lean4Lean.VInductDecl.CandidateFamilyValidationAnnotationList.head_terminal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CandidateFamilyValidationAnnotationList.head_terminal

/--
info: 'Lean4Lean.VInductDecl.CandidateBlockFamilySemanticListRun.tailExact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CandidateBlockFamilySemanticListRun.tailExact

/--
info: 'Lean4Lean.VInductDecl.CandidateBlockLaterFamilyValidationCursor.advanceHead_context' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms CandidateBlockLaterFamilyValidationCursor.advanceHead_context

/--
info: 'Lean4Lean.VInductDecl.CandidateBlockLaterFamilyValidationCursor.advanceHead_parameterSources' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms CandidateBlockLaterFamilyValidationCursor.advanceHead_parameterSources

/--
info: 'Lean4Lean.VInductDecl.CandidateBlockLaterFamilyValidationCursor.advanceHead_semantics' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms CandidateBlockLaterFamilyValidationCursor.advanceHead_semantics

/--
info: 'Lean4Lean.VInductDecl.CandidateBlockFamilySemanticGenerationShapeList.tailExact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CandidateBlockFamilySemanticGenerationShapeList.tailExact

/--
info: 'Lean4Lean.VInductDecl.CandidateBlockFamilyAnnotationSpineList.tailExact' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CandidateBlockFamilyAnnotationSpineList.tailExact

/--
info: 'Lean4Lean.TypeChecker.TelDefEqEvidence.symm' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms TypeChecker.TelDefEqEvidence.symm

/--
info: 'Lean4Lean.TypeChecker.TelDefEqEvidence.trans' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms TypeChecker.TelDefEqEvidence.trans

/--
info: 'Lean4Lean.VInductDecl.CandidateBlockFamilySemanticListRun.headPosition_cons_view' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CandidateBlockFamilySemanticListRun.headPosition_cons_view

/--
info: 'Lean4Lean.VInductDecl.CandidateBlockFamilySemanticListRun.twoHeadPositions' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms CandidateBlockFamilySemanticListRun.twoHeadPositions

/--
info: 'Lean4Lean.VInductDecl.CandidateBlockFamilySemanticListRun.TwoHead.views_eq' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms CandidateBlockFamilySemanticListRun.TwoHead.views_eq

/--
info: 'Lean4Lean.VInductDecl.CandidateBlockFamilyViewParameterDefEqList.forall_views' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 ptrEqConstantInfo_eq,
 ptrEqExpr_eq,
 Quot.sound,
 Expr.abstractRange_eq,
 Expr.abstract_eq,
 Expr.eqv_eq,
 Expr.hasLooseBVar_eq,
 Expr.instantiate1_eq,
 Expr.instantiateRange_eq,
 Expr.instantiateRevRange_eq,
 Expr.instantiateRev_eq,
 Expr.instantiate_eq,
 Expr.lowerLooseBVars_eq,
 Expr.mkAppData_eq,
 Expr.mkData_eq,
 Expr.replace_eq,
 Level.hasParam_eq,
 Level.instLawfulBEqLevel,
 Level.isExplicitSubsumedAux_eq,
 Level.normalize_eq,
 PersistentHashMap.findAux_isSome,
 Syntax.structEq_eq,
 PersistentArray.WF.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms CandidateBlockFamilyViewParameterDefEqList.forall_views


end VInductDecl

end Lean4Lean
