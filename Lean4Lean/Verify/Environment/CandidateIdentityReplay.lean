import Lean4Lean.Verify.Environment.Normalization
import Std.Data.HashMap.Lemmas

/-!
# Structural identity replay for normalization candidates

This module proves identity normalization from the ordinary producer's exact
recursive executions.  The replay description is structural: it supplies the
WHNF behavior of each source node and the transparent annotation build, then
recovers the producer-owned `CandidateExprTrace`.  It does not evaluate a
proof-only Boolean with `native_decide`.
-/

namespace Lean4Lean.TypeChecker

open Lean Meta
open Lean4Lean

theorem localContextFindNew
    (lctx : LocalContext) (id : FVarId) (name : Name)
    (type : Expr) (bi : BinderInfo) (kind : LocalDeclKind)
    (hwf : lctx.WF) (hfresh : lctx.find? id = none) :
    (lctx.mkLocalDecl id name type bi kind).find? id =
      some (.cdecl lctx.decls.size id name type bi kind) := by
  have hwf' := LocalContext.WF.mkLocalDecl
    (name := name) (ty := type) (bi := bi) (kind := kind) hwf hfresh
  rw [hwf'.find?_eq_find?_toList]
  rw [LocalContext.mkLocalDecl_toList]
  simp [LocalDecl.fvarId]

theorem emptyLocalContextFindNone (id : FVarId) :
    (⟨.empty, .empty, .empty⟩ : LocalContext).find? id = none := by
  have h := LocalContext.WF.find?_eq_find?_toList
    (fv := id) LocalContext.WF.nil
  rw [h]
  simp [LocalContext.toList]

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
  rw [LocalContext.mkLocalDecl_toList]
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
      LocalContext.mkLocalDecl_toList, List.mem_cons] at membership ⊢
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

/-- A recursively identity-normalizing candidate reconstructs its exact stored
kernel expression when every source free variable belongs to the candidate's
fresh-local context.

The scope premise is operational: it is the same implementation-context
condition retained by candidate checking.  `CandidateLocalContextRun` proves
that each generated identifier is fresh, so abstracting the instantiated body
recovers the original stored binder body rather than merely an alpha-equivalent
expression. -/
theorem CandidateExprIdentity.view_eq_source
    {context : AddInductive.Context} {source : Expr}
    {trace : AddInductive.CandidateExprTrace context source}
    (identity : CandidateExprIdentity trace)
    (localRun : CandidateLocalContextRun context)
    (scope : source.FVarsIn
      (fun fv => (context.lctx.find? fv).isSome = true)) :
    trace.view = source := by
  induction identity with
  | terminal result_eq =>
      simpa [AddInductive.CandidateExprTrace.view] using result_eq
  | forallE domainCandidate bodyCandidate source_eq consumed_eq
      domainIdentity bodyIdentity domainIH bodyIH =>
      rename_i traceContext domain name binderInfo traceSource inferred body
        fresh annotations annotationsEq checked normalized
      rw [source_eq] at scope
      simp only [FVarsIn] at scope
      have domainEq := domainIH localRun scope.1
      let pushedRun := localRun.push name binderInfo annotations.consumed
      have oldScope : body.FVarsIn (fun fv =>
          ((traceContext.pushLocalDecl name binderInfo
            annotations.consumed).lctx.find? fv).isSome = true) := by
        apply scope.2.mono
        intro fv present
        obtain ⟨decl, find⟩ := Option.isSome_iff_exists.mp present
        apply Option.isSome_iff_exists.mpr
        exact ⟨decl, localRun.push_findOld name binderInfo
          annotations.consumed find⟩
      have freshScope : traceContext.freshExpr.FVarsIn (fun fv =>
          ((traceContext.pushLocalDecl name binderInfo
            annotations.consumed).lctx.find? fv).isSome = true) := by
        simp only [AddInductive.Context.freshExpr, FVarsIn]
        rw [localRun.push_findNew name binderInfo annotations.consumed]
        rfl
      have bodyScope := oldScope.instantiate1 freshScope
      have bodyScope' : (body.instantiate1 traceContext.freshExpr).FVarsIn
          (fun fv => ((traceContext.pushLocalDecl name binderInfo
            annotations.consumed).lctx.find? fv).isSome = true) := by
        simpa only [Expr.instantiate1_eq] using bodyScope
      have bodyEq := bodyIH pushedRun bodyScope'
      have bodyAvoid : body.FVarsIn (· ≠ traceContext.freshFVarId) := by
        apply scope.2.mono
        intro fv present equal
        subst fv
        rw [localRun.fresh] at present
        contradiction
      calc
        (AddInductive.CandidateExprTrace.forallE traceContext traceSource
          inferred name domain body binderInfo fresh annotations annotationsEq
          checked normalized domainCandidate bodyCandidate).view =
            .forallE name domainCandidate.view
              (bodyCandidate.view.abstract #[traceContext.freshExpr])
              binderInfo := rfl
        _ = .forallE name domain body binderInfo := by
          rw [domainEq, bodyEq]
          congr 1
          rw [show #[traceContext.freshExpr] =
            ⟨[traceContext.freshFVarId].map Expr.fvar⟩ by rfl]
          rw [Expr.abstract_eq]
          change (body.instantiate1 traceContext.freshExpr).abstract1
            traceContext.freshFVarId = body
          simpa only [Expr.instantiate1_eq,
            AddInductive.Context.freshExpr] using
            (bodyAvoid.abstract_instantiate1 (k := 0))
        _ = traceSource := source_eq.symm

/- The structural reconstruction bridge has only the expected standard and
kernel-expression infrastructure closure; in particular, it does not depend
on a fixture computation oracle. -/
/--
info: 'Lean4Lean.TypeChecker.CandidateExprIdentity.view_eq_source' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 Expr.abstract_eq,
 Expr.instantiate1_eq,
 PersistentArray.toList'_push,
 PersistentHashMap.WF.find?_eq,
 PersistentHashMap.WF.toList'_insert]
-/
#guard_msgs in
#print axioms CandidateExprIdentity.view_eq_source

@[simp] theorem candidateLiftLooseBVarsFVar
    (id : FVarId) (s d : Nat) :
    (Expr.fvar id).liftLooseBVars' s d = .fvar id := by
  rfl

@[simp] theorem candidateInstantiateFVar
    (id : FVarId) (a : Expr) (k : Nat) :
    (Expr.fvar id).instantiate1' a k = .fvar id := by
  rfl

theorem candidateWhnfFVar_refl
    (context : AddInductive.Context) (id : FVarId)
    (recursionFuel : Nat)
    (hdepth : context.fuel.recDepth = recursionFuel + 1)
    (hnotlet : TypeChecker.Inner.isLetFVar context.lctx id = false) :
    AddInductive.CandidateWhnfStep.Valid
      ⟨context, .fvar id, .fvar id⟩ := by
  unfold AddInductive.CandidateWhnfStep.Valid
  change TypeChecker.M.run context.env context.safety context.lctx
    context.lparams context.fuel (TypeChecker.whnf (.fvar id)) =
      .ok (.fvar id)
  unfold TypeChecker.M.run TypeChecker.whnf TypeChecker.RecM.run
  simp [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, StateT.bind, Except.bind, Bind.bind,
    StateT.pure, Except.pure, Pure.pure,
    StateT.run', Functor.map, Except.map]
  rw [hdepth]
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.whnf' (.fvar id)
      (TypeChecker.Methods.withFuel recursionFuel)
      context.toTypeChecker ({} : TypeChecker.State)) =
        .ok (.fvar id)
  unfold TypeChecker.Inner.whnf'
  simp only [ReaderT.bind, StateT.bind, Except.bind, Bind.bind]
  rw [show (getLCtx : TypeChecker.RecM LocalContext)
      (TypeChecker.Methods.withFuel recursionFuel)
      context.toTypeChecker ({} : TypeChecker.State) =
        .ok (context.lctx, ({} : TypeChecker.State)) by rfl]
  simp [hnotlet, ReaderT.pure, StateT.pure,
    Except.pure, Pure.pure, Except.map]

theorem candidateWhnfPushedFVar_refl
    (context : AddInductive.Context) (name : Name) (type : Expr)
    (binderInfo : BinderInfo) (recursionFuel : Nat)
    (hdepth : context.fuel.recDepth = recursionFuel + 1)
    (hwf : context.lctx.WF)
    (hfresh : context.lctx.find? context.freshFVarId = none) :
    AddInductive.CandidateWhnfStep.Valid
      ⟨context.pushLocalDecl name binderInfo type,
        context.freshExpr, context.freshExpr⟩ := by
  apply candidateWhnfFVar_refl _ context.freshFVarId recursionFuel
  · simpa [AddInductive.Context.pushLocalDecl] using hdepth
  · unfold TypeChecker.Inner.isLetFVar
    simp only [AddInductive.Context.pushLocalDecl]
    rw [localContextFindNew context.lctx context.freshFVarId
      name type binderInfo .default hwf hfresh]

private theorem candidateWhnfCoreFVar_refl
    (context : AddInductive.Context) (id : FVarId)
    (state : TypeChecker.State)
    (hnotlet : TypeChecker.Inner.isLetFVar context.lctx id = false) :
    TypeChecker.Inner.whnfCore (.fvar id) false
        (TypeChecker.Methods.withFuel 9999)
        context.toTypeChecker state =
      .ok (.fvar id, state) := by
  change TypeChecker.Inner.whnfCore' (.fvar id) false
      (TypeChecker.Methods.withFuel 9998)
      context.toTypeChecker state =
    .ok (.fvar id, state)
  unfold TypeChecker.Inner.whnfCore'
  simp only [ReaderT.bind, StateT.bind, Except.bind, Bind.bind]
  rw [show (getLCtx : TypeChecker.RecM LocalContext)
      (TypeChecker.Methods.withFuel 9998)
      context.toTypeChecker state =
        .ok (context.lctx, state) by rfl]
  simp [hnotlet, ReaderT.pure, StateT.pure,
    Except.pure, Pure.pure]

private theorem candidateReduceRecursorFVarApp_none
    (context : AddInductive.Context) (fnId argId : FVarId)
    (state : TypeChecker.State)
    (hquot : context.env.quotInit = false) :
    TypeChecker.Inner.reduceRecursor
        (.app (.fvar fnId) (.fvar argId))
        (TypeChecker.Methods.withFuel 9999)
        context.toTypeChecker state =
      .ok (none, state) := by
  unfold TypeChecker.Inner.reduceRecursor
  simp only [ReaderT.bind, StateT.bind, Except.bind, Bind.bind]
  rw [show (liftM TypeChecker.getEnv :
      TypeChecker.RecM Lean.Kernel.Environment)
      (TypeChecker.Methods.withFuel 9999)
      context.toTypeChecker state =
        .ok (context.env, state) by rfl]
  simp only []
  rw [hquot]
  have hfn : (.app (.fvar fnId) (.fvar argId) : Expr).getAppFn =
      .fvar fnId := by rfl
  simp [inductiveReduceRec, hfn, ReaderT.bind, StateT.bind,
    Except.bind, Bind.bind, ReaderT.pure, StateT.pure,
    Except.pure, Pure.pure]

private theorem candidateWhnfCoreFVarAppFVar_refl
    (context : AddInductive.Context) (fnId argId : FVarId)
    (hquot : context.env.quotInit = false)
    (hnotlet : TypeChecker.Inner.isLetFVar context.lctx fnId = false) :
    TypeChecker.Inner.whnfCore'
        (.app (.fvar fnId) (.fvar argId)) false
        (TypeChecker.Methods.withFuel 9999)
        context.toTypeChecker ({} : TypeChecker.State) =
      .ok (.app (.fvar fnId) (.fvar argId),
        ({} : TypeChecker.State)) := by
  unfold TypeChecker.Inner.whnfCore'
  simp [ReaderT.bind, StateT.bind, Except.bind, Bind.bind, Pure.pure]
  rw [show (get : TypeChecker.RecM TypeChecker.State)
      (TypeChecker.Methods.withFuel 9999)
      context.toTypeChecker ({} : TypeChecker.State) =
        .ok (({} : TypeChecker.State), ({} : TypeChecker.State)) by rfl]
  simp only [Std.HashMap.getElem?_empty]
  simp [ReaderT.bind, StateT.bind, Except.bind, Bind.bind]
  have hfn : (.app (.fvar fnId) (.fvar argId) : Expr).getAppFn =
      .fvar fnId := by rfl
  have hargs : (.app (.fvar fnId) (.fvar argId) : Expr).getAppRevArgs =
      #[.fvar argId] := by rfl
  rw [hfn, hargs]
  rw [candidateWhnfCoreFVar_refl context fnId
    ({} : TypeChecker.State) hnotlet]
  simp [candidateReduceRecursorFVarApp_none context fnId argId
      ({} : TypeChecker.State) hquot,
    Expr.structuralEq, ReaderT.bind, StateT.bind, Except.bind, Bind.bind,
    ReaderT.pure, StateT.pure, Except.pure, Pure.pure]

private theorem candidateReduceNativeFVarAppFVar_none
    (context : AddInductive.Context) (fnId argId : FVarId)
    (state : TypeChecker.State) :
    (liftM (TypeChecker.Inner.reduceNative context.env
      (.app (.fvar fnId) (.fvar argId))) :
        TypeChecker.RecM (Option Expr))
      (TypeChecker.Methods.withFuel 9999)
      context.toTypeChecker state = .ok (none, state) := by
  rfl

private theorem candidateReduceNatFVarAppFVar_none
    (context : AddInductive.Context) (fnId argId : FVarId)
    (state : TypeChecker.State) :
    TypeChecker.Inner.reduceNat (.app (.fvar fnId) (.fvar argId))
        (TypeChecker.Methods.withFuel 9999)
      context.toTypeChecker state = .ok (none, state) := by
  unfold TypeChecker.Inner.reduceNat
  have hnargs : (.app (.fvar fnId) (.fvar argId) : Expr).getAppNumArgs =
      1 := by rfl
  have hfn : (.app (.fvar fnId) (.fvar argId) : Expr).appFn! =
      .fvar fnId := by rfl
  rw [hnargs, hfn]
  simp only [show (1 == 1) = true by decide, if_true]
  rw [show Expr.structuralEq (.fvar fnId) (.const ``Nat.succ []) = false by
    rfl]
  rfl

private theorem candidateUnfoldDefinitionFVarAppFVar_none
    (context : AddInductive.Context) (fnId argId : FVarId)
    (state : TypeChecker.State) :
    TypeChecker.Inner.unfoldDefinition
        (.app (.fvar fnId) (.fvar argId))
        (TypeChecker.Methods.withFuel 9999)
      context.toTypeChecker state = .ok (none, state) := by
  unfold TypeChecker.Inner.unfoldDefinition
  have hisApp : (.app (.fvar fnId) (.fvar argId) : Expr).isApp = true :=
    rfl
  have hfn : (.app (.fvar fnId) (.fvar argId) : Expr).getAppFn =
      .fvar fnId := by rfl
  rw [hisApp, hfn]
  simp [TypeChecker.Inner.unfoldDefinitionCore,
    ReaderT.bind, StateT.bind, Except.bind, Bind.bind,
    ReaderT.pure, StateT.pure, Except.pure, Pure.pure]

private theorem candidateWhnfLoopFVarAppFVar_refl
    (context : AddInductive.Context) (fnId argId : FVarId)
    (hquot : context.env.quotInit = false)
    (hnotlet : TypeChecker.Inner.isLetFVar context.lctx fnId = false) :
    TypeChecker.Inner.whnf'.loop
        (.app (.fvar fnId) (.fvar argId)) 100000
        (TypeChecker.Methods.withFuel 9999)
        context.toTypeChecker ({} : TypeChecker.State) =
      .ok (.app (.fvar fnId) (.fvar argId),
        ({} : TypeChecker.State)) := by
  rw [show 100000 = 99999 + 1 by rfl]
  unfold TypeChecker.Inner.whnf'.loop
  simp only [ReaderT.bind, StateT.bind, Except.bind, Bind.bind]
  rw [show (liftM TypeChecker.getEnv :
      TypeChecker.RecM Lean.Kernel.Environment)
      (TypeChecker.Methods.withFuel 9999)
      context.toTypeChecker ({} : TypeChecker.State) =
        .ok (context.env, ({} : TypeChecker.State)) by rfl]
  simp only []
  rw [candidateWhnfCoreFVarAppFVar_refl context fnId argId
    hquot hnotlet]
  simp only []
  rw [candidateReduceNativeFVarAppFVar_none context fnId argId
    ({} : TypeChecker.State)]
  simp [ReaderT.bind, StateT.bind, Except.bind, Bind.bind, Pure.pure]
  rw [candidateReduceNatFVarAppFVar_none context fnId argId
    ({} : TypeChecker.State)]
  simp [ReaderT.bind, StateT.bind, Except.bind, Bind.bind]
  rw [candidateUnfoldDefinitionFVarAppFVar_none context fnId argId
    ({} : TypeChecker.State)]
  rfl

set_option maxRecDepth 10000 in
theorem candidateWhnfFVarAppFVar_refl
    (context : AddInductive.Context) (fnId argId : FVarId)
    (hdepth : context.fuel.recDepth = 10000)
    (hwhnf : context.fuel.whnf = 100000)
    (hquot : context.env.quotInit = false)
    (hnotlet : TypeChecker.Inner.isLetFVar context.lctx fnId = false) :
    AddInductive.CandidateWhnfStep.Valid
      ⟨context, .app (.fvar fnId) (.fvar argId),
        .app (.fvar fnId) (.fvar argId)⟩ := by
  unfold AddInductive.CandidateWhnfStep.Valid
  unfold TypeChecker.M.run TypeChecker.whnf TypeChecker.RecM.run
  simp [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, StateT.bind, Except.bind, Bind.bind,
    StateT.pure, Except.pure, Pure.pure,
    StateT.run', Functor.map, Except.map]
  rw [hdepth]
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.whnf'
      (.app (.fvar fnId) (.fvar argId))
      (TypeChecker.Methods.withFuel 9999)
      context.toTypeChecker ({} : TypeChecker.State)) =
        .ok (.app (.fvar fnId) (.fvar argId))
  unfold TypeChecker.Inner.whnf'
  simp only [ReaderT.bind, StateT.bind, Except.bind, Bind.bind, Pure.pure]
  rw [show (get : TypeChecker.RecM TypeChecker.State)
      (TypeChecker.Methods.withFuel 9999)
      context.toTypeChecker ({} : TypeChecker.State) =
        .ok (({} : TypeChecker.State), ({} : TypeChecker.State)) by rfl]
  simp only [Std.HashMap.getElem?_empty]
  simp only [readThe, MonadReaderOf.read, ReaderT.bind, StateT.bind, Except.bind, Bind.bind,
    ReaderT.pure, StateT.pure, Except.pure, Pure.pure]
  rw [show (liftM read : TypeChecker.RecM TypeChecker.Context)
      (TypeChecker.Methods.withFuel 9999)
      context.toTypeChecker ({} : TypeChecker.State) =
        .ok (context.toTypeChecker, ({} : TypeChecker.State)) by rfl]
  simp only []
  rw [show context.toTypeChecker.eagerReduce = false by rfl]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [show context.toTypeChecker.fuel.whnf = 100000 by
    simpa [AddInductive.Context.toTypeChecker] using hwhnf]
  rw [candidateWhnfLoopFVarAppFVar_refl context fnId argId
    hquot hnotlet]
  rfl

private theorem candidateWhnfCoreConst_refl
    (context : AddInductive.Context) (constName : Name)
    (levels : List Level) (state : TypeChecker.State) :
    TypeChecker.Inner.whnfCore (.const constName levels) false
        (TypeChecker.Methods.withFuel 9999)
        context.toTypeChecker state =
      .ok (.const constName levels, state) := by
  rfl

private theorem candidateReduceRecursorConstFVarFVar_none
    (context : AddInductive.Context) (constName : Name)
    (levels : List Level) (arg1 arg2 : FVarId)
    (state : TypeChecker.State) (info : InductiveVal)
    (hquot : context.env.quotInit = false)
    (hfind : context.env.find? constName = some (.inductInfo info)) :
    TypeChecker.Inner.reduceRecursor
        (.app (.app (.const constName levels) (.fvar arg1)) (.fvar arg2))
        (TypeChecker.Methods.withFuel 9999)
        context.toTypeChecker state = .ok (none, state) := by
  unfold TypeChecker.Inner.reduceRecursor
  simp only [ReaderT.bind, StateT.bind, Except.bind, Bind.bind]
  rw [show (liftM TypeChecker.getEnv :
      TypeChecker.RecM Lean.Kernel.Environment)
      (TypeChecker.Methods.withFuel 9999)
      context.toTypeChecker state =
        .ok (context.env, state) by rfl]
  simp only []
  rw [hquot]
  have hfn :
      (.app (.app (.const constName levels) (.fvar arg1))
        (.fvar arg2) : Expr).getAppFn = .const constName levels := by
    rfl
  simp [inductiveReduceRec, hfn, hfind,
    ReaderT.bind, StateT.bind, Except.bind, Bind.bind,
    ReaderT.pure, StateT.pure, Except.pure, Pure.pure]

private theorem candidateWhnfCoreConstFVarFVar_refl
    (context : AddInductive.Context) (constName : Name)
    (levels : List Level) (arg1 arg2 : FVarId)
    (info : InductiveVal)
    (hquot : context.env.quotInit = false)
    (hfind : context.env.find? constName = some (.inductInfo info)) :
    TypeChecker.Inner.whnfCore'
        (.app (.app (.const constName levels) (.fvar arg1)) (.fvar arg2))
        false (TypeChecker.Methods.withFuel 9999)
        context.toTypeChecker ({} : TypeChecker.State) =
      .ok (.app (.app (.const constName levels) (.fvar arg1))
        (.fvar arg2), ({} : TypeChecker.State)) := by
  unfold TypeChecker.Inner.whnfCore'
  simp [ReaderT.bind, StateT.bind, Except.bind, Bind.bind, Pure.pure]
  rw [show (get : TypeChecker.RecM TypeChecker.State)
      (TypeChecker.Methods.withFuel 9999)
      context.toTypeChecker ({} : TypeChecker.State) =
        .ok (({} : TypeChecker.State), ({} : TypeChecker.State)) by rfl]
  simp only [Std.HashMap.getElem?_empty]
  simp [ReaderT.bind, StateT.bind, Except.bind, Bind.bind]
  have hfn :
      (.app (.app (.const constName levels) (.fvar arg1))
        (.fvar arg2) : Expr).getAppFn = .const constName levels := by
    rfl
  have hargs :
      (.app (.app (.const constName levels) (.fvar arg1))
        (.fvar arg2) : Expr).getAppRevArgs =
      #[.fvar arg2, .fvar arg1] := by
    rfl
  rw [hfn, hargs]
  rw [candidateWhnfCoreConst_refl context constName levels
    ({} : TypeChecker.State)]
  simp [candidateReduceRecursorConstFVarFVar_none context constName levels
      arg1 arg2 ({} : TypeChecker.State) info hquot hfind,
    Expr.structuralEq_refl, ReaderT.bind, StateT.bind, Except.bind,
    Bind.bind, ReaderT.pure, StateT.pure, Except.pure, Pure.pure]

private theorem candidateReduceNativeConstFVarFVar_none
    (context : AddInductive.Context) (constName : Name)
    (levels : List Level) (arg1 arg2 : FVarId)
    (state : TypeChecker.State) :
    (liftM (TypeChecker.Inner.reduceNative context.env
      (.app (.app (.const constName levels) (.fvar arg1)) (.fvar arg2))) :
        TypeChecker.RecM (Option Expr))
      (TypeChecker.Methods.withFuel 9999)
      context.toTypeChecker state = .ok (none, state) := by
  rfl

private theorem candidateUnfoldDefinitionCoreConst_none
    (context : AddInductive.Context) (constName : Name)
    (levels : List Level) (state : TypeChecker.State)
    (info : InductiveVal)
    (hfind : context.env.find? constName = some (.inductInfo info)) :
    TypeChecker.Inner.unfoldDefinitionCore (.const constName levels)
        (TypeChecker.Methods.withFuel 9999)
        context.toTypeChecker state = .ok (none, state) := by
  unfold TypeChecker.Inner.unfoldDefinitionCore
  simp only [ReaderT.bind, StateT.bind, Except.bind, Bind.bind]
  rw [show (liftM TypeChecker.getEnv :
      TypeChecker.RecM Lean.Kernel.Environment)
      (TypeChecker.Methods.withFuel 9999)
      context.toTypeChecker state =
        .ok (context.env, state) by rfl]
  simp only []
  unfold TypeChecker.Inner.isDelta
  rw [show (Expr.const constName levels).getAppFn =
    .const constName levels by rfl]
  simp only
  rw [hfind]
  rfl

private theorem candidateUnfoldDefinitionConstFVarFVar_none
    (context : AddInductive.Context) (constName : Name)
    (levels : List Level) (arg1 arg2 : FVarId)
    (state : TypeChecker.State) (info : InductiveVal)
    (hfind : context.env.find? constName = some (.inductInfo info)) :
    TypeChecker.Inner.unfoldDefinition
        (.app (.app (.const constName levels) (.fvar arg1)) (.fvar arg2))
        (TypeChecker.Methods.withFuel 9999)
        context.toTypeChecker state = .ok (none, state) := by
  unfold TypeChecker.Inner.unfoldDefinition
  have hisApp :
      (.app (.app (.const constName levels) (.fvar arg1))
        (.fvar arg2) : Expr).isApp = true := by
    rfl
  have hfn :
      (.app (.app (.const constName levels) (.fvar arg1))
        (.fvar arg2) : Expr).getAppFn = .const constName levels := by
    rfl
  rw [hisApp, hfn]
  simp only [if_true, ReaderT.bind, StateT.bind, Except.bind, Bind.bind]
  rw [candidateUnfoldDefinitionCoreConst_none context constName levels
    state info hfind]
  simp [ReaderT.pure, StateT.pure, Except.pure, Pure.pure]

private theorem candidateWhnfLoopConstFVarFVar_refl
    (context : AddInductive.Context) (constName : Name)
    (levels : List Level) (arg1 arg2 : FVarId)
    (info : InductiveVal)
    (hquot : context.env.quotInit = false)
    (hfind : context.env.find? constName = some (.inductInfo info))
    (hreduceNat : TypeChecker.Inner.reduceNat
        (.app (.app (.const constName levels) (.fvar arg1)) (.fvar arg2))
        (TypeChecker.Methods.withFuel 9999)
        context.toTypeChecker ({} : TypeChecker.State) =
      .ok (none, ({} : TypeChecker.State))) :
    TypeChecker.Inner.whnf'.loop
        (.app (.app (.const constName levels) (.fvar arg1)) (.fvar arg2))
        100000 (TypeChecker.Methods.withFuel 9999)
        context.toTypeChecker ({} : TypeChecker.State) =
      .ok (.app (.app (.const constName levels) (.fvar arg1))
        (.fvar arg2), ({} : TypeChecker.State)) := by
  rw [show 100000 = 99999 + 1 by rfl]
  unfold TypeChecker.Inner.whnf'.loop
  simp only [ReaderT.bind, StateT.bind, Except.bind, Bind.bind]
  rw [show (liftM TypeChecker.getEnv :
      TypeChecker.RecM Lean.Kernel.Environment)
      (TypeChecker.Methods.withFuel 9999)
      context.toTypeChecker ({} : TypeChecker.State) =
        .ok (context.env, ({} : TypeChecker.State)) by rfl]
  simp only []
  rw [candidateWhnfCoreConstFVarFVar_refl context constName levels
    arg1 arg2 info hquot hfind]
  simp only []
  rw [candidateReduceNativeConstFVarFVar_none context constName levels
    arg1 arg2 ({} : TypeChecker.State)]
  simp [ReaderT.bind, StateT.bind, Except.bind, Bind.bind, Pure.pure]
  rw [hreduceNat]
  simp [ReaderT.bind, StateT.bind, Except.bind, Bind.bind]
  rw [candidateUnfoldDefinitionConstFVarFVar_none context constName levels
    arg1 arg2 ({} : TypeChecker.State) info hfind]
  rfl

set_option maxRecDepth 10000 in
theorem candidateWhnfConstFVarFVar_refl
    (context : AddInductive.Context) (constName : Name)
    (levels : List Level) (arg1 arg2 : FVarId)
    (info : InductiveVal)
    (hdepth : context.fuel.recDepth = 10000)
    (hwhnf : context.fuel.whnf = 100000)
    (hquot : context.env.quotInit = false)
    (hfind : context.env.find? constName = some (.inductInfo info))
    (hreduceNat : TypeChecker.Inner.reduceNat
        (.app (.app (.const constName levels) (.fvar arg1)) (.fvar arg2))
        (TypeChecker.Methods.withFuel 9999)
        context.toTypeChecker ({} : TypeChecker.State) =
      .ok (none, ({} : TypeChecker.State))) :
    AddInductive.CandidateWhnfStep.Valid
      ⟨context,
        .app (.app (.const constName levels) (.fvar arg1)) (.fvar arg2),
        .app (.app (.const constName levels) (.fvar arg1)) (.fvar arg2)⟩ := by
  unfold AddInductive.CandidateWhnfStep.Valid
  unfold TypeChecker.M.run TypeChecker.whnf TypeChecker.RecM.run
  simp [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, StateT.bind, Except.bind, Bind.bind,
    StateT.pure, Except.pure, Pure.pure,
    StateT.run', Functor.map, Except.map]
  rw [hdepth]
  change Except.map (fun x : Expr × TypeChecker.State => x.1)
    (TypeChecker.Inner.whnf'
      (.app (.app (.const constName levels) (.fvar arg1)) (.fvar arg2))
      (TypeChecker.Methods.withFuel 9999)
      context.toTypeChecker ({} : TypeChecker.State)) =
        .ok (.app (.app (.const constName levels) (.fvar arg1))
          (.fvar arg2))
  unfold TypeChecker.Inner.whnf'
  simp only [ReaderT.bind, StateT.bind, Except.bind, Bind.bind, Pure.pure]
  rw [show (get : TypeChecker.RecM TypeChecker.State)
      (TypeChecker.Methods.withFuel 9999)
      context.toTypeChecker ({} : TypeChecker.State) =
        .ok (({} : TypeChecker.State), ({} : TypeChecker.State)) by rfl]
  simp only [Std.HashMap.getElem?_empty]
  simp only [readThe, MonadReaderOf.read, ReaderT.bind, StateT.bind, Except.bind, Bind.bind,
    ReaderT.pure, StateT.pure, Except.pure, Pure.pure]
  rw [show (liftM read : TypeChecker.RecM TypeChecker.Context)
      (TypeChecker.Methods.withFuel 9999)
      context.toTypeChecker ({} : TypeChecker.State) =
        .ok (context.toTypeChecker, ({} : TypeChecker.State)) by rfl]
  simp only []
  rw [show context.toTypeChecker.eagerReduce = false by rfl]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [show context.toTypeChecker.fuel.whnf = 100000 by
    simpa [AddInductive.Context.toTypeChecker] using hwhnf]
  rw [candidateWhnfLoopConstFVarFVar_refl context constName levels
    arg1 arg2 info hquot hfind hreduceNat]
  rfl

/-- A syntactic identity-WHNF tree for every node inspected by the ordinary
candidate producer. -/
inductive CandidateExprIdentityReplay :
    (context : AddInductive.Context) → (source : Expr) → Type where
  | terminal (context : AddInductive.Context) (source : Expr)
      (whnf : AddInductive.CandidateWhnfStep.Valid
        ⟨context, source, source⟩)
      (notForall : source.isForall = false) :
      CandidateExprIdentityReplay context source
  | forallE (context : AddInductive.Context)
      (name : Name) (domain body : Expr) (binderInfo : BinderInfo)
      (whnf : AddInductive.CandidateWhnfStep.Valid
        ⟨context, .forallE name domain body binderInfo,
          .forallE name domain body binderInfo⟩)
      (annotations : AddInductive.CandidateTypeAnnotations domain)
      (annotationsBuild :
        AddInductive.buildCandidateTypeAnnotations domain = .ok annotations)
      (consume : AddInductive.consumeTypeAnnotations domain = domain)
      (domainReplay : CandidateExprIdentityReplay context domain)
      (bodyReplay : CandidateExprIdentityReplay
        (context.pushLocalDecl name binderInfo annotations.consumed)
        (body.instantiate1 context.freshExpr)) :
      CandidateExprIdentityReplay context
        (.forallE name domain body binderInfo)

namespace CandidateExprIdentityReplay

def spineLength : CandidateExprIdentityReplay context source → Nat
  | .terminal .. => 0
  | .forallE _ _ _ _ _ _ _ _ _ _ bodyReplay => bodyReplay.spineLength + 1

def terminalSource : CandidateExprIdentityReplay context source → Expr
  | .terminal _ source _ _ => source
  | .forallE _ _ _ _ _ _ _ _ _ _ bodyReplay => bodyReplay.terminalSource

/-- A replay tree packaged with the exact main-spine length and terminal
source. -/
structure Shaped
    (context : AddInductive.Context) (source : Expr)
    (expectedSpineLength : Nat) (expectedTerminalSource : Expr) where
  replay : CandidateExprIdentityReplay context source
  spineLength_eq : replay.spineLength = expectedSpineLength
  terminalSource_eq : replay.terminalSource = expectedTerminalSource

namespace Shaped

def terminal
    (context : AddInductive.Context) (source : Expr)
    (whnf : AddInductive.CandidateWhnfStep.Valid
      ⟨context, source, source⟩)
    (notForall : source.isForall = false) :
    Shaped context source 0 source :=
  ⟨CandidateExprIdentityReplay.terminal context source whnf notForall,
    rfl, rfl⟩

def forallE
    (context : AddInductive.Context) (name : Name)
    (domain body : Expr) (binderInfo : BinderInfo)
    (whnf : AddInductive.CandidateWhnfStep.Valid
      ⟨context, .forallE name domain body binderInfo,
        .forallE name domain body binderInfo⟩)
    (annotations : AddInductive.CandidateTypeAnnotations domain)
    (annotationsBuild :
      AddInductive.buildCandidateTypeAnnotations domain = .ok annotations)
    (consume : AddInductive.consumeTypeAnnotations domain = domain)
    (domainReplay : CandidateExprIdentityReplay context domain)
    (bodyReplay : Shaped
      (context.pushLocalDecl name binderInfo annotations.consumed)
      (body.instantiate1 context.freshExpr)
      expectedSpineLength expectedTerminalSource) :
    Shaped context (.forallE name domain body binderInfo)
      (expectedSpineLength + 1) expectedTerminalSource := by
  refine ⟨CandidateExprIdentityReplay.forallE context name domain body
    binderInfo whnf annotations annotationsBuild consume domainReplay
    bodyReplay.replay, ?_, ?_⟩
  · simpa [CandidateExprIdentityReplay.spineLength] using
      bodyReplay.spineLength_eq
  · simpa [CandidateExprIdentityReplay.terminalSource] using
      bodyReplay.terminalSource_eq

def forallEBuilt
    (context : AddInductive.Context) (name : Name)
    (domain body : Expr) (binderInfo : BinderInfo)
    (whnf : AddInductive.CandidateWhnfStep.Valid
      ⟨context, .forallE name domain body binderInfo,
        .forallE name domain body binderInfo⟩)
    (consume : AddInductive.consumeTypeAnnotations domain = domain)
    (domainReplay : CandidateExprIdentityReplay context domain)
    (bodyReplay : Shaped
      (context.pushLocalDecl name binderInfo domain)
      (body.instantiate1 context.freshExpr)
      expectedSpineLength expectedTerminalSource) :
    Shaped context (.forallE name domain body binderInfo)
      (expectedSpineLength + 1) expectedTerminalSource := by
  let annotations : AddInductive.CandidateTypeAnnotations domain :=
    let ⟨consumed, trace⟩ :=
      AddInductive.CandidateTypeAnnotationTrace.build domain
    ⟨consumed, trace⟩
  have annotationsBuild :
      AddInductive.buildCandidateTypeAnnotations domain =
        .ok annotations := by
    rfl
  have annotationsConsumed : annotations.consumed = domain :=
    (AddInductive.CandidateTypeAnnotations.matches_of_build annotations
      annotationsBuild).trans consume
  have bodyReplay' : Shaped
      (context.pushLocalDecl name binderInfo annotations.consumed)
      (body.instantiate1 context.freshExpr)
      expectedSpineLength expectedTerminalSource := by
    rw [annotationsConsumed]
    exact bodyReplay
  exact Shaped.forallE context name domain body binderInfo whnf annotations
    annotationsBuild consume domainReplay bodyReplay'

theorem expr_eq_forallE_of_isForall
    (source : Expr) (h : source.isForall = true) :
    source = .forallE source.bindingName! source.bindingDomain!
      source.bindingBody! source.bindingInfo! := by
  cases source <;> simp_all [Expr.isForall, Expr.bindingName!,
    Expr.bindingDomain!, Expr.bindingBody!, Expr.bindingInfo!]

theorem candidateWhnfForallSource_refl
    (context : AddInductive.Context) (source : Expr)
    (recursionFuel : Nat)
    (hdepth : context.fuel.recDepth = recursionFuel + 1)
    (h : source.isForall = true) :
    AddInductive.CandidateWhnfStep.Valid ⟨context, source, source⟩ := by
  rw [expr_eq_forallE_of_isForall source h]
  unfold AddInductive.CandidateWhnfStep.Valid
  change TypeChecker.M.run context.env context.safety context.lctx
    context.lparams context.fuel
      (TypeChecker.whnf (.forallE source.bindingName!
        source.bindingDomain! source.bindingBody! source.bindingInfo!)) =
    .ok (.forallE source.bindingName! source.bindingDomain!
      source.bindingBody! source.bindingInfo!)
  unfold TypeChecker.M.run TypeChecker.whnf TypeChecker.RecM.run
  simp [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, StateT.bind, Except.bind, Bind.bind,
    StateT.pure, Except.pure, Pure.pure,
    StateT.run', Functor.map, Except.map]
  rw [hdepth]
  rfl

def forallEBuiltOfSource
    (context : AddInductive.Context) (source : Expr)
    (isForall : source.isForall = true)
    (whnf : AddInductive.CandidateWhnfStep.Valid
      ⟨context, source, source⟩)
    (consume : AddInductive.consumeTypeAnnotations
      source.bindingDomain! = source.bindingDomain!)
    (domainReplay : CandidateExprIdentityReplay context
      source.bindingDomain!)
    (bodyReplay : Shaped
      (context.pushLocalDecl source.bindingName! source.bindingInfo!
        source.bindingDomain!)
      (source.bindingBody!.instantiate1 context.freshExpr)
      expectedSpineLength expectedTerminalSource) :
    Shaped context source (expectedSpineLength + 1)
      expectedTerminalSource := by
  rw [expr_eq_forallE_of_isForall source isForall] at whnf ⊢
  exact forallEBuilt context source.bindingName! source.bindingDomain!
    source.bindingBody! source.bindingInfo! whnf consume domainReplay
    bodyReplay

end Shaped

structure Evidence
    (replay : CandidateExprIdentityReplay context source)
    (trace : AddInductive.CandidateExprTrace traceContext source) : Prop where
  identity : CandidateExprIdentity trace
  spineLength_eq : trace.spineLength = replay.spineLength
  terminalResult_eq : trace.terminalResult = replay.terminalSource

theorem evidence_of_loop
    (replay : CandidateExprIdentityReplay context source)
    (run : AddInductive.buildCandidateExpr.loop context source fuel =
      .ok candidateTrace) : Evidence replay candidateTrace := by
  induction replay generalizing fuel with
  | terminal context source whnf notForall =>
      cases fuel with
      | zero =>
          simp [AddInductive.buildCandidateExpr.loop] at run
      | succ fuel =>
          have inspected := run
          unfold AddInductive.buildCandidateExpr.loop at inspected
          cases hcheck : AddInductive.observeCandidateCheckType context source with
          | error error => simp [hcheck] at inspected
          | ok observation =>
              rcases observation with ⟨inferred, checked⟩
              have expected :=
                AddInductive.buildCandidateExpr_loop_of_whnf_nonForall
                  context source inferred source fuel checked whnf notForall
              rw [expected] at run
              cases run
              exact ⟨.terminal rfl, rfl, rfl⟩
  | forallE context name domain body binderInfo whnf annotations
      annotationsBuild consume domainReplay bodyReplay domainIH bodyIH =>
      cases fuel with
      | zero =>
          simp [AddInductive.buildCandidateExpr.loop] at run
      | succ fuel =>
          unfold AddInductive.buildCandidateExpr.loop at run
          cases hcheck : AddInductive.observeCandidateCheckType context
              (.forallE name domain body binderInfo) with
          | error error => simp [hcheck] at run
          | ok observation =>
              rcases observation with ⟨inferred, checked⟩
              simp only [hcheck, Bind.bind, Except.bind] at run
              simp only [AddInductive.observeCandidateWhnf_of_run context
                (.forallE name domain body binderInfo)
                (.forallE name domain body binderInfo) whnf] at run
              simp only [annotationsBuild] at run
              repeat' split at run
              all_goals try simp_all [Pure.pure, Except.pure]
              rename_i freshEq isDefEqResult isDefEqObservation hisDefEq
                domainResult domainTrace hdomain bodyResult bodyTrace hbody
              cases run
              have domainEvidence := domainIH hdomain
              have bodyEvidence := bodyIH hbody
              have annotationsConsumed : annotations.consumed = domain :=
                (AddInductive.CandidateTypeAnnotations.matches_of_build
                  annotations annotationsBuild).trans consume
              refine ⟨.forallE domainTrace bodyTrace rfl annotationsConsumed
                domainEvidence.identity bodyEvidence.identity, ?_, ?_⟩
              · simpa [AddInductive.CandidateExprTrace.spineLength,
                  spineLength] using bodyEvidence.spineLength_eq
              · simpa [AddInductive.CandidateExprTrace.terminalResult,
                  terminalSource] using bodyEvidence.terminalResult_eq

theorem evidence_of_build
    (replay : CandidateExprIdentityReplay context source)
    (run : AddInductive.buildCandidateExpr source context = .ok candidate) :
    Evidence replay candidate.trace := by
  unfold AddInductive.buildCandidateExpr at run
  simp only [readThe, MonadReaderOf.read, ReaderT.read,
    ReaderT.bind, Bind.bind, ReaderT.pure, Pure.pure,
    Except.bind, Except.pure] at run
  cases hloop : AddInductive.buildCandidateExpr.loop context source
      context.fuel.recDepth with
  | error error => simp [hloop] at run
  | ok trace =>
      simp [hloop] at run
      subst candidate
      exact replay.evidence_of_loop hloop

theorem identity_of_build
    (replay : CandidateExprIdentityReplay context source)
    (run : AddInductive.buildCandidateExpr source context = .ok candidate) :
    CandidateExprIdentity candidate.trace :=
  (replay.evidence_of_build run).identity

end CandidateExprIdentityReplay
end Lean4Lean.TypeChecker

namespace Lean4Lean.AddInductive

def builtCandidateTypeAnnotations (source : Lean.Expr) :
    CandidateTypeAnnotations source :=
  let ⟨consumed, trace⟩ := CandidateTypeAnnotationTrace.build source
  ⟨consumed, trace⟩

theorem buildCandidateTypeAnnotations_built (source : Lean.Expr) :
    buildCandidateTypeAnnotations source =
      .ok (builtCandidateTypeAnnotations source) := by
  rfl

theorem CandidateFamilyTypeListProduced.singleton_build
    {context : Context} {source : Lean.InductiveType}
    {candidates : CandidateList CandidateFamilyType [source]}
    (run : CandidateFamilyTypeListProduced context candidates) :
    buildCandidateExpr source.type context =
      .ok candidates.singleton.type := by
  cases run with
  | cons head tail =>
      cases tail
      unfold normalizeCandidateFamilyType at head
      simp only [ReaderT.bind, Bind.bind] at head
      cases hbuild : buildCandidateExpr source.type context with
      | error error => simp [Except.bind, hbuild] at head
      | ok candidate =>
          simp [Except.bind, hbuild, ReaderT.pure,
            Pure.pure, Except.pure] at head
          cases head
          rfl

theorem CandidateConstructorListProduced.singleton_build
    {context : Context} {source : Lean.Constructor}
    {candidates : CandidateList CandidateConstructor [source]}
    (run : CandidateConstructorListProduced context candidates) :
    buildCandidateExpr source.type context =
      .ok candidates.singleton.type := by
  cases run with
  | cons head tail =>
      cases tail
      unfold normalizeCandidateConstructor at head
      simp only [ReaderT.bind, Bind.bind] at head
      cases hbuild : buildCandidateExpr source.type context with
      | error error => simp [Except.bind, hbuild] at head
      | ok candidate =>
          simp [Except.bind, hbuild, ReaderT.pure,
            Pure.pure, Except.pure] at head
          cases head
          rfl

end Lean4Lean.AddInductive
