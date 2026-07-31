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
  | .forallE domain body =>
      .forallEDF domain.isDefEq body.isDefEq

/-- Interpret one paired candidate node as typed definitional equality. -/
def CandidateNodeRun.evidence
    (run : CandidateNodeRun env Us Δ context source inferred result
      source' result' inferred') :
    DefEqEvidence env Us.length Δ.toCtx source' result' inferred' :=
  .whnf run.whnf run.check.hasType

/-- Recursive semantic interpretation of a source-indexed candidate trace.

For a terminal node the exact full-check/WHNF pair is sufficient.  For an
exposed Pi, the root WHNF reaches the raw Pi, while recursively interpreted
domain and instantiated-body traces provide congruence from that raw Pi to
the candidate view.  The body context equation makes the raw-binder discipline
explicit and prevents evidence checked under a different telescope from being
reused here. -/
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
      (domainCandidate : AddInductive.CandidateExprTrace context domain)
      (bodyCandidate : AddInductive.CandidateExprTrace
        (context.pushLocalDecl name binderInfo domain.consumeTypeAnnotations)
        (body.instantiate1 context.freshExpr))
      (node : CandidateNodeRun env Us Δ context source inferred
        (.forallE name domain body binderInfo)
        source' (.forallE domain' body') inferred')
      (domainRun : CandidateExprRun env Us domainCandidate Δ
        domain' domainView' domainInferred')
      (bodyRun : CandidateExprRun env Us bodyCandidate bodyΔ
        body' bodyView' bodyInferred')
      (domainType : env.HasType Us.length Δ.toCtx domain' (.sort u))
      (bodyType : env.HasType Us.length
        (domain' :: Δ.toCtx) body' (.sort v))
      (bodyContext :
        bodyΔ =
          (some (context.freshFVarId,
            domain.consumeTypeAnnotations.fvarsList),
            .vlam domain') :: Δ) :
      CandidateExprRun env Us
        (.forallE context source inferred name domain body binderInfo
          checked normalized domainCandidate bodyCandidate)
        Δ source' (.forallE domainView' bodyView') inferred'

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
  | .forallE _ _ node domainRun bodyRun domainType bodyType bodyContext => by
    have henv : VEnv.WF env := by
      simpa only [node.check.venv_eq] using node.check.context.Ewf
    have hΓ : OnCtx Δ.toCtx (env.IsType Us.length) := by
      simpa only [node.check.venv_eq, node.check.lparams_eq,
        node.check.vlctx_eq] using node.check.context.Δwf.toCtx
    have domainEvidence := domainRun.evidence
    obtain ⟨_, domainTypeEq⟩ :=
      domainType.uniq henv hΓ domainEvidence.isDefEq
    have domainAtSort : DefEqEvidence env Us.length Δ.toCtx
        _ _ (.sort _) :=
      .change domainTypeEq.symm domainEvidence
    have bodyEvidence := bodyRun.evidence
    rw [bodyContext] at bodyEvidence
    simp only [VLCtx.toCtx] at bodyEvidence
    have hBodyΓ : OnCtx (_ :: Δ.toCtx) (env.IsType Us.length) :=
      ⟨hΓ, ⟨_, domainType⟩⟩
    obtain ⟨_, bodyTypeEq⟩ :=
      bodyType.uniq henv hBodyΓ bodyEvidence.isDefEq
    have bodyAtSort : DefEqEvidence env Us.length
        (_ :: Δ.toCtx) _ _ (.sort _) :=
      .change bodyTypeEq.symm bodyEvidence
    have piEvidence := DefEqEvidence.forallE domainAtSort bodyAtSort
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
  | forallE _ _ node => exact node.check.expr_tr

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
  | @forallE context domain name binderInfo Δ source inferred body
      source' domain' body' inferred' domainView' domainInferred' bodyΔ
      bodyView' bodyInferred' u v
      checked normalized domainCandidate bodyCandidate node domainRun bodyRun
      domainType bodyType bodyContext domainIH bodyIH =>
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
    have bodyIH' : TrExpr env Us
        ((some (context.freshFVarId,
          domain.consumeTypeAnnotations.fvarsList), .vlam domain') :: Δ)
        bodyCandidate.view bodyView' := by
      simpa only [bodyContext] using bodyIH
    have bodyAbstract := bodyIH'.abstract VLCtx.Abstract.zero
    have hctx : VLCtx.IsDefEq env Us.length
        ((none, .vlam domain') :: Δ)
        ((none, .vlam domainView') :: Δ) :=
      .cons (.refl henv hΔ) (by nofun)
        (.vlam domainDef)
    have bodyMoved := candidateTrExpr_moveCtx henv hctx bodyAbstract
    have bodyEvidence := bodyRun.evidence
    rw [bodyContext] at bodyEvidence
    simp only [VLCtx.toCtx] at bodyEvidence
    have hBodyΓ : OnCtx (domain' :: Δ.toCtx)
        (env.IsType Us.length) := ⟨hΔ.toCtx, ⟨_, domainType⟩⟩
    obtain ⟨_, bodyTypeEq⟩ :=
      bodyType.uniq henv hBodyΓ bodyEvidence.isDefEq
    have bodyDefRaw : env.IsDefEq Us.length
        (domain' :: Δ.toCtx) body' bodyView' (.sort v) :=
      (DefEqEvidence.change bodyTypeEq.symm bodyEvidence).isDefEq
    have bodyDefMoved :=
      bodyDefRaw.defeqDFC henv hctx.defeqCtx
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

/-
The evidence types mention exact verifier executions, so these semantic
interpretation roots intentionally inherit the same transitional Verify
closure as `WhnfRun.isDefEq`. Exact guards ensure that the generic assembler
does not silently widen it.
-/
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

end VInductDecl

end Lean4Lean
