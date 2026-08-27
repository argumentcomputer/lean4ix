import Lean4Lean.Theory.Projection

/-!
# Block-backed structure projections

`VStructureView` is the compatibility surface for a declaration generated as
one singleton inductive family.  A family inside a mutual or flattened nested
block can have the same one-constructor, unindexed host shape, but its recursor
and iota rules still belong to the complete block.  This file introduces the
corresponding family restriction without fabricating a singleton generation
certificate.

The restriction deliberately retains `BlockGenerationChecked`, the exact
source-ordered family member, and that family's checked ordinal.  Later
projector programs can therefore supply all block motives and minors and use
the actual registered family recursor.
-/

namespace Lean4Lean

open VInductDecl

/-- Instantiating above a complete reverse-variable range leaves that range
unchanged. -/
theorem VExpr.bvarRevRange_instN_high : ∀ (m off : Nat)
    (argument : VExpr) (k : Nat), off + m ≤ k →
    (VExpr.bvarRevRange off m).map (fun expression =>
      expression.inst argument k) =
      VExpr.bvarRevRange off m
  | 0, _, _, _, _ => rfl
  | m + 1, off, argument, k, bound => by
      show (VExpr.bvar (off + m)).inst argument k ::
          (VExpr.bvarRevRange off m).map (fun expression =>
            expression.inst argument k) =
        VExpr.bvar (off + m) :: VExpr.bvarRevRange off m
      rw [VExpr.bvarRevRange_instN_high m off argument k (by omega)]
      simp [VExpr.inst, VExpr.instVar, show off + m < k from by omega]

/-- Substituting ambient arguments underneath a freshly inserted binder
segment commutes with that insertion. -/
theorem VExpr.liftN_instRevAt_same (expression : VExpr)
    (arguments : List VExpr) (count : Nat) :
    (expression.liftN count).instRevAt arguments count =
      (expression.instRev arguments).liftN count := by
  induction arguments generalizing expression with
  | nil => rfl
  | cons argument arguments ih =>
      simp only [VExpr.instRevAt, VExpr.instRev]
      rw [← VExpr.liftN_instN_lo count expression argument
        arguments.length 0 (Nat.zero_le _)]
      exact ih (expression.inst argument arguments.length)

/-- The same commutation with an existing retained binder offset. -/
theorem VExpr.liftN_instRevAt_shift (expression : VExpr)
    (arguments : List VExpr) (offset count : Nat) :
    (expression.liftN count).instRevAt arguments (offset + count) =
      (expression.instRevAt arguments offset).liftN count := by
  induction arguments generalizing expression with
  | nil => rfl
  | cons argument arguments ih =>
      simp only [VExpr.instRevAt]
      rw [show offset + count + arguments.length =
          count + (offset + arguments.length) by omega,
        ← VExpr.liftN_instN_lo count expression argument
          (offset + arguments.length) 0 (Nat.zero_le _)]
      exact ih (expression.inst argument (offset + arguments.length))

theorem VExpr.liftN_succ_inst_top (expression argument : VExpr)
    (count : Nat) :
    (expression.liftN (count + 1)).inst argument count =
      expression.liftN count := by
  rw [← VExpr.liftN'_liftN' (e := expression) (n1 := count) (n2 := 1)
    (k1 := 0) (k2 := count) (Nat.zero_le _) (by omega)]
  exact VExpr.inst_liftN1 (expression.liftN count) argument count

/-- Reverse substitution at a retained-binder offset selects an argument in
outermost-first order and weakens it beneath the retained binders. -/
theorem VExpr.instRevAt_bvar_rev_getElem?
    (arguments : List VExpr) {index : Nat} {argument : VExpr}
    (hargument : arguments[index]? = some argument) (offset : Nat) :
    (VExpr.bvar (offset + (arguments.length - 1 - index))).instRevAt
        arguments offset =
      argument.liftN offset := by
  obtain ⟨hindex, hget⟩ := List.getElem?_eq_some_iff.1 hargument
  have hbvar : VExpr.bvar (offset + (arguments.length - 1 - index)) =
      (VExpr.bvar (arguments.length - 1 - index)).liftN offset := by
    simp [VExpr.liftN, liftVar, show
      0 ≤ arguments.length - 1 - index from Nat.zero_le _]
  rw [hbvar, VExpr.liftN_instRevAt_same,
    VExpr.instRev_bvar_lt arguments (by omega)]
  have hrevidx : arguments.length - 1 -
      (arguments.length - 1 - index) = index := by omega
  simpa only [hrevidx] using
    congrArg (fun expression => expression.liftN offset) hget

theorem VExpr.bvarRevRange_getElem?_local
    (offset count index : Nat) (hindex : index < count) :
    (VExpr.bvarRevRange offset count)[index]? =
      some (.bvar (offset + (count - 1 - index))) := by
  induction count generalizing index with
  | zero => omega
  | succ count ih =>
      cases index with
      | zero => simp [VExpr.bvarRevRange]
      | succ index =>
          simp only [VExpr.bvarRevRange, List.getElem?_cons_succ]
          rw [ih index (by omega)]
          congr 3
          omega

private theorem List.Forall₂.of_getElem?_local {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β},
      xs.length = ys.length →
      (∀ {i : Nat} {x : α} {y : β},
        xs[i]? = some x → ys[i]? = some y → R x y) →
      List.Forall₂ R xs ys
  | [], [], _, _ => .nil
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen
  | x :: xs, y :: ys, hlen, h => by
      refine .cons (h (i := 0) rfl rfl) ?_
      apply List.Forall₂.of_getElem?_local (Nat.succ.inj hlen)
      intro i x' y' hx hy
      exact h (i := i + 1) (by simpa using hx) (by simpa using hy)

private theorem List.Forall₂.getElem?_local {R : α → β → Prop}
    {xs : List α} {ys : List β} (h : List.Forall₂ R xs ys) :
    ∀ {i : Nat} {x : α} {y : β},
      xs[i]? = some x → ys[i]? = some y → R x y := by
  induction h with
  | nil =>
      intro i x y hx _
      simp at hx
  | cons hxy hrest ih =>
      intro i x y hx hy
      cases i with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hy
          subst x
          subst y
          exact hxy
      | succ i =>
          exact ih (by simpa using hx) (by simpa using hy)

/-- Substituting an outer argument prefix above a retained suffix selects
exactly that prefix, weakened beneath the retained binders. -/
theorem VExpr.map_instRevAt_bvarRevRange_prefix
    (arguments suffix : List VExpr) (offset : Nat) :
    (VExpr.bvarRevRange (offset + suffix.length) arguments.length).map
        (fun expression =>
          expression.instRevAt (arguments ++ suffix) offset) =
      arguments.map (VExpr.liftN offset) := by
  apply List.ext_getElem?
  intro index
  simp only [List.getElem?_map]
  by_cases hindex : index < arguments.length
  · let argument := arguments[index]
    have hargument : arguments[index]? = some argument :=
      List.getElem?_eq_getElem hindex
    have hcombined : (arguments ++ suffix)[index]? = some argument := by
      rw [List.getElem?_append_left hindex, hargument]
    rw [VExpr.bvarRevRange_getElem?_local _ _ _ hindex, hargument]
    simp only [Option.map_some]
    have hout := VExpr.instRevAt_bvar_rev_getElem?
      (arguments ++ suffix) hcombined offset
    have hposition :
        offset + suffix.length + (arguments.length - 1 - index) =
          offset + ((arguments ++ suffix).length - 1 - index) := by
      simp only [List.length_append]
      omega
    rw [hposition, hout]
  · have hargument : arguments[index]? = none :=
      List.getElem?_eq_none_iff.2 (by omega)
    have hrange :
        (VExpr.bvarRevRange (offset + suffix.length)
          arguments.length)[index]? = none := by
      apply List.getElem?_eq_none_iff.2
      simpa only [VExpr.bvarRevRange_length] using
        (show arguments.length ≤ index by omega)
    rw [hrange, hargument]
    rfl

private theorem VExpr.dropN_add_local (first second : Nat)
    (expression : VExpr) :
    VExpr.dropN second (VExpr.dropN first expression) =
      VExpr.dropN (first + second) expression := by
  induction first generalizing expression with
  | zero => simp [VExpr.dropN]
  | succ first ih =>
      cases expression <;> cases second <;>
        simp [VExpr.dropN, ih, Nat.succ_add, Nat.add_assoc]

private def progressiveTypesAux : List VExpr → Nat → List VExpr
  | [], _ => []
  | type :: types, index =>
      type.liftN index :: progressiveTypesAux types (index + 1)

@[simp] private theorem progressiveTypesAux_length
    (types : List VExpr) (index : Nat) :
    (progressiveTypesAux types index).length = types.length := by
  induction types generalizing index with
  | nil => rfl
  | cons type types ih => simp [progressiveTypesAux, ih]

private theorem progressiveTypesAux_eq_zipIdx
    (types : List VExpr) (index : Nat) :
    progressiveTypesAux types index =
      (types.zipIdx index).map fun entry => entry.1.liftN entry.2 := by
  induction types generalizing index with
  | nil => rfl
  | cons type types ih =>
      simp only [progressiveTypesAux, List.zipIdx, List.map_cons]
      rw [ih]

private theorem progressiveTypesAux_instTelN
    (types : List VExpr) (argument : VExpr) (index : Nat) :
    VExpr.instTelN argument (progressiveTypesAux types (index + 1)) index =
      progressiveTypesAux types index := by
  induction types generalizing index with
  | nil => rfl
  | cons type types ih =>
      simp only [progressiveTypesAux, VExpr.instTelN]
      rw [VExpr.liftN_succ_inst_top, ih]

private theorem List.Forall₂.length_eq'
    {R : α → β → Prop} : ∀ {left : List α} {right : List β},
    List.Forall₂ R left right → left.length = right.length
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons _ rest => by
      simp [List.Forall₂.length_eq' rest]

/-- A pointwise-typed concrete argument list consumes the corresponding
progressively weakened telescope. -/
private theorem VEnv.SpineWF.of_progressive
    {env : VEnv} {U : Nat} {Γ : List VExpr} :
    ∀ {types arguments : List VExpr} {tail : VExpr},
      List.Forall₂ (fun argument type =>
        env.HasType U Γ argument type) arguments types →
      env.SpineWF U Γ
        (VExpr.forallN (progressiveTypesAux types 0) tail)
        arguments (tail.instRev arguments)
  | [], [], _, .nil => .nil
  | type :: types, argument :: arguments, tail,
      .cons hargument hrest => by
      refine VEnv.SpineWF.cons (A₁ := type.liftN 0) ?_ ?_
      · change env.IsDefEq U Γ argument argument type at hargument
        simpa only [VExpr.liftN_zero] using hargument
      rw [VExpr.instN_forallN,
        progressiveTypesAux_instTelN]
      simp only [progressiveTypesAux_length, Nat.zero_add]
      have ih := VEnv.SpineWF.of_progressive
        (tail := tail.inst argument types.length) hrest
      have hlength : arguments.length = types.length :=
        List.Forall₂.length_eq' hrest
      simpa [VExpr.instRev, hlength] using ih

/-- A pointwise-typed concrete argument list consumes the corresponding
`zipIdx` presentation of a progressively weakened telescope. -/
theorem VEnv.SpineWF.of_forall₂_progressive
    {env : VEnv} {U : Nat} {context : List VExpr}
    {types arguments : List VExpr} {tail : VExpr}
    (typed : List.Forall₂ (fun argument type =>
      env.HasType U context argument type) arguments types) :
    env.SpineWF U context
      (VExpr.forallN
        (types.zipIdx.map fun entry => entry.1.liftN entry.2) tail)
      arguments (tail.instRev arguments) := by
  rw [← progressiveTypesAux_eq_zipIdx]
  exact VEnv.SpineWF.of_progressive typed

/-- A sort-annotated pi cursor.  Unlike `OnSortTel`, this presentation keeps
the residual pi expression explicit, which lets projection generation consume
some binders by typing their arguments and remove syntactically irrelevant
binders by strengthening. -/
inductive VEnv.SortCursor (env : VEnv) (U : Nat) :
    List VExpr → VExpr → List VLevel → Prop where
  | nil (tail : VExpr) : SortCursor env U Γ tail []
  | cons (head : env.HasType U Γ A (.sort u))
      (tail : SortCursor env U (A :: Γ) body us) :
      SortCursor env U Γ (.forallE A body) (u :: us)

theorem VEnv.OnSortTel.toSortCursor {env : VEnv} {U : Nat} :
    ∀ {Γ As us}, env.OnSortTel U Γ As us → ∀ tail,
      env.SortCursor U Γ (VExpr.forallN As tail) us
  | _, [], [], .nil, tail => .nil tail
  | _, _ :: _, _ :: _, .cons hA hrest, tail =>
      .cons hA (hrest.toSortCursor tail)

/-- Invert a context insertion through a sort cursor when the entire cursor
syntactically skips the inserted binders. -/
theorem VEnv.SortCursor.weakN_inv {env : VEnv} {U n k : Nat}
    {base lifted : List VExpr} (henv : env.ConversionRegular)
    (hlifted : OnCtx lifted (env.IsType U))
    (W : Ctx.LiftN n k base lifted) :
    ∀ {cursor sorts}, env.SortCursor U lifted cursor sorts →
      cursor.Skips n k →
      ∃ baseCursor, cursor = baseCursor.liftN n k ∧
        env.SortCursor U base baseCursor sorts
  | _, [], .nil tail, hskip => by
      obtain ⟨baseTail, htail⟩ := VExpr.skips_iff_exists.1 hskip
      exact ⟨baseTail, htail, .nil baseTail⟩
  | _, _ :: _, .cons (A := A) (body := body) (u := u) hA hbody,
      hskip => by
      have hparts := VExpr.skips_iff.1 hskip
      change A.Skips' n k ∧ body.Skips' n (k + 1) at hparts
      have hAskips : A.Skips n k := VExpr.skips_iff.2 hparts.1
      have hbodySkips : body.Skips n (k + 1) :=
        VExpr.skips_iff.2 hparts.2
      obtain ⟨baseA, hAeq⟩ := VExpr.skips_iff_exists.1 hAskips
      subst A
      have hbaseA : env.HasType U base baseA (.sort u) := by
        apply (VEnv.HasType.weakN_iff henv hlifted W).1
        change env.HasType U lifted (baseA.liftN n k) (.sort u)
        exact hA
      have hliftedBody : OnCtx (baseA.liftN n k :: lifted)
          (env.IsType U) := ⟨hlifted, u, hA⟩
      obtain ⟨baseBody, hBodyEq, hbaseBody⟩ :=
        hbody.weakN_inv henv hliftedBody W.succ hbodySkips
      refine ⟨.forallE baseA baseBody, ?_, .cons hbaseA hbaseBody⟩
      simp [VExpr.liftN, hBodyEq]

/-- Substitute a typed context entry throughout a sort cursor. -/
theorem VEnv.SortCursor.instN {env : VEnv} {U k : Nat}
    {base source target : List VExpr} {argument domain : VExpr}
    (henv : env.Ordered)
    (W : Ctx.InstN base argument domain k source target)
    (hargument : env.HasType U base argument domain) :
    ∀ {cursor sorts}, env.SortCursor U source cursor sorts →
      env.SortCursor U target (cursor.inst argument k) sorts
  | _, [], .nil tail => .nil _
  | _, _ :: _, .cons hA hbody => by
      simp only [VExpr.inst]
      exact .cons (hA.instN henv W hargument)
        (hbody.instN henv W.succ hargument)

/-- An application cursor in which an unused binder may be consumed without
typing its syntactically irrelevant argument.  This is the semantic shape of
the runtime projection loop: dependent fields use a real projector, while a
closed remaining telescope removes the binder without inventing a value. -/
inductive VEnv.SparseSpineWF (env : VEnv) (U : Nat) (Γ : List VExpr) :
    VExpr → List VExpr → VExpr → Prop where
  | nil : SparseSpineWF env U Γ cursor [] cursor
  | typed (argument : env.HasType U Γ arg domain)
      (rest : SparseSpineWF env U Γ (body.inst arg) args cursor) :
      SparseSpineWF env U Γ (.forallE domain body) (arg :: args) cursor
  | skip (irrelevant : body.Skips 1 0)
      (rest : SparseSpineWF env U Γ (body.inst arg) args cursor) :
      SparseSpineWF env U Γ (.forallE domain body) (arg :: args) cursor

/-- Pointwise equality evidence for the arguments which a sparse spine
actually types.  A skipped argument deliberately contributes no equality
obligation. -/
inductive VEnv.SparseSpineWF.PointwiseDefEq
    {env : VEnv} {U : Nat} {Γ : List VExpr} :
    {source : VExpr} → {args : List VExpr} → {cursor : VExpr} →
      VEnv.SparseSpineWF env U Γ source args cursor →
      List VExpr → Prop where
  | nil (cursor : VExpr) : PointwiseDefEq (.nil :
      VEnv.SparseSpineWF env U Γ cursor [] cursor) []
  | typed (domain body argument cursor right : VExpr)
      (args rights : List VExpr)
      (argumentType : env.HasType U Γ argument domain)
      (rest : env.SparseSpineWF U Γ (body.inst argument) args cursor)
      (argumentEq : env.IsDefEqU U Γ argument right)
      (restEq : PointwiseDefEq rest rights) :
      PointwiseDefEq (.typed argumentType rest) (right :: rights)
  | skip (body argument cursor right : VExpr)
      (args rights : List VExpr)
      (irrelevant : body.Skips 1 0)
      (rest : env.SparseSpineWF U Γ (body.inst argument) args cursor)
      (restEq : PointwiseDefEq rest rights) :
      PointwiseDefEq (.skip irrelevant rest) (right :: rights)

/-- Instantiating a syntactically skipped binder is independent of the term
placed in that binder. -/
theorem VExpr.Skips.inst_eq {body : VExpr} (self : body.Skips 1 0)
    (left right : VExpr) : body.inst left = body.inst right := by
  obtain ⟨base, hbody⟩ := VExpr.skips_iff_exists.1 self
  rw [hbody]
  rw [VExpr.inst_liftN, VExpr.inst_liftN]

/-- Sparse dependent-spine congruence.  The right spine is fully typed.  At
a typed left step the arguments are definitionally equal; at a skipped step
the right argument is converted to the left domain and the left residual
cursor is unchanged by `Skips`.  Thus no typing witness is ever fabricated
for a skipped left argument. -/
theorem VEnv.SparseSpineWF.PointwiseDefEq.cursor_defeq
    {env : VEnv} (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    {source leftCursor : VExpr}
    {leftArgsList rightArgs : List VExpr}
    {sparse : env.SparseSpineWF U Γ source leftArgsList leftCursor}
    (self : sparse.PointwiseDefEq rightArgs) :
    ∀ {rightSource rightCursor : VExpr},
      env.SpineWF U Γ rightSource rightArgs rightCursor →
      env.IsDefEqU U Γ source rightSource →
      env.IsDefEqU U Γ leftCursor rightCursor := by
  induction self with
  | nil cursor =>
      intro rightSource rightCursor hright hsource
      cases hright
      exact hsource
  | typed domain body argument cursor right args rights argumentType rest
      argumentEq restEq ih =>
      intro rightSource rightCursor hright hsource
      cases hright with
      | cons rightArgumentType rightRest =>
          obtain ⟨_, hbodyEq⟩ :=
            (henv.forallE_inv hΓ hsource).2
          have hargumentEq :=
            henv.isDefEqU_of_l hΓ argumentEq argumentType
          have hnextEq := VEnv.IsDefEq.instDF henv.ordered hΓ
            hbodyEq hargumentEq
          exact ih rightRest ⟨_, hnextEq⟩
  | skip body argument cursor right args rights irrelevant rest
      restEq ih =>
      intro rightSource rightCursor hright hsource
      cases hright with
      | cons rightArgumentType rightRest =>
          obtain ⟨_, hdomainEq⟩ :=
            (henv.forallE_inv hΓ hsource).1
          obtain ⟨_, hbodyEq⟩ :=
            (henv.forallE_inv hΓ hsource).2
          have hrightAtLeft :=
            henv.hasType_defeqU_r hΓ
              ⟨_, hdomainEq.symm⟩ rightArgumentType
          have hnextEq := VEnv.IsDefEq.instDF henv.ordered hΓ
            hbodyEq hrightAtLeft
          rw [← irrelevant.inst_eq argument right] at hnextEq
          exact ih rightRest ⟨_, hnextEq⟩

theorem VEnv.SparseSpineWF.consumeForalls_eq
    (self : VEnv.SparseSpineWF env U Γ source args cursor) :
    source.consumeForalls? args = some cursor := by
  induction self with
  | nil => rfl
  | typed _ _ ih | skip _ _ ih =>
      exact ih

theorem VEnv.SpineWF.toSparse :
    ∀ {source args cursor}, VEnv.SpineWF env U Γ source args cursor →
      VEnv.SparseSpineWF env U Γ source args cursor
  | _, [], _, .nil => .nil
  | _, _ :: _, _, .cons harg hrest =>
    .typed harg (VEnv.SpineWF.toSparse hrest)

/-- A fully typed spine with pointwise definitional equalities supplies the
masked equality evidence expected by its all-typed sparse shadow. -/
theorem VEnv.SpineWF.toSparse_pointwiseDefEq
    {env : VEnv} {U : Nat} {Γ : List VExpr} :
    ∀ {source args cursor rights},
      (self : env.SpineWF U Γ source args cursor) →
      List.Forall₂
        (fun left right => left = right ∨ env.IsDefEqU U Γ left right)
        args rights →
      self.toSparse.PointwiseDefEq rights
  | _, [], _, [], .nil, .nil => .nil _
  | _, left :: lefts, _, right :: rights, .cons hleft hrest,
      .cons heq heqs => by
    refine .typed _ _ _ _ _ _ _ hleft hrest.toSparse ?_ ?_
    · cases heq with
      | inl heq =>
          subst right
          exact ⟨_, hleft⟩
      | inr heq => exact heq
    · exact hrest.toSparse_pointwiseDefEq heqs

/-- Concatenate two mixed typed/strengthened application traces. -/
theorem VEnv.SparseSpineWF.append
    {env : VEnv} {U : Nat} {Γ : List VExpr} :
    ∀ {source leftArgs middle rightArgs cursor},
      env.SparseSpineWF U Γ source leftArgs middle →
      env.SparseSpineWF U Γ middle rightArgs cursor →
      env.SparseSpineWF U Γ source (leftArgs ++ rightArgs) cursor
  | _, [], _, _, _, .nil, right => right
  | _, _ :: _, _, _, _, .typed argument rest, right =>
      .typed argument (rest.append right)
  | _, _ :: _, _, _, _, .skip irrelevant rest, right =>
      .skip irrelevant (rest.append right)

/-- Extend a sparse application trace by one typed argument. -/
theorem VEnv.SparseSpineWF.snocTyped
    {env : VEnv} {U : Nat} {Γ : List VExpr}
    {source domain body argument : VExpr} {args : List VExpr}
    (self : env.SparseSpineWF U Γ source args (.forallE domain body))
    (argumentType : env.HasType U Γ argument domain) :
    env.SparseSpineWF U Γ source (args ++ [argument])
      (body.inst argument) :=
  self.append (.typed argumentType .nil)

/-- Extend a sparse application trace by one syntactically irrelevant
argument. -/
theorem VEnv.SparseSpineWF.snocSkip
    {env : VEnv} {U : Nat} {Γ : List VExpr}
    {source domain body argument : VExpr} {args : List VExpr}
    (self : env.SparseSpineWF U Γ source args (.forallE domain body))
    (irrelevant : body.Skips 1 0) :
    env.SparseSpineWF U Γ source (args ++ [argument])
      (body.inst argument) :=
  self.append (.skip irrelevant .nil)

/-- Pointwise equality evidence composes along concatenated sparse traces. -/
theorem VEnv.SparseSpineWF.PointwiseDefEq.append
    {env : VEnv} {U : Nat} {Γ : List VExpr} :
    ∀ {source leftArgs middle rightArgs cursor leftRights rightRights}
      {left : env.SparseSpineWF U Γ source leftArgs middle}
      {right : env.SparseSpineWF U Γ middle rightArgs cursor},
      left.PointwiseDefEq leftRights →
      right.PointwiseDefEq rightRights →
      (left.append right).PointwiseDefEq (leftRights ++ rightRights) := by
  intro source leftArgs middle rightArgs cursor leftRights rightRights
    left right leftEq rightEq
  induction leftEq with
  | nil => exact rightEq
  | typed domain body argument middle rightArgument leftArgs leftRights
      argumentType rest argumentEq restEq ih =>
    exact .typed domain body argument cursor rightArgument
      (leftArgs ++ rightArgs) (leftRights ++ rightRights)
      argumentType (rest.append right) argumentEq (ih rightEq)
  | skip body argument middle rightArgument leftArgs leftRights irrelevant
      rest restEq ih =>
    exact .skip body argument cursor rightArgument
      (leftArgs ++ rightArgs) (leftRights ++ rightRights)
      irrelevant (rest.append right) (ih rightEq)

/-- Extend pointwise sparse equality by one typed argument. -/
theorem VEnv.SparseSpineWF.PointwiseDefEq.snocTyped
    {env : VEnv} {U : Nat} {Γ : List VExpr}
    {source domain body argument right : VExpr} {args : List VExpr}
    {sparse : env.SparseSpineWF U Γ source args (.forallE domain body)}
    {rights : List VExpr}
    (self : sparse.PointwiseDefEq rights)
    (argumentType : env.HasType U Γ argument domain)
    (argumentEq : env.IsDefEqU U Γ argument right) :
    (sparse.snocTyped argumentType).PointwiseDefEq (rights ++ [right]) :=
  self.append (.typed _ _ _ _ _ _ _ argumentType .nil argumentEq
    (.nil _))

/-- Extend pointwise sparse equality by one skipped argument. -/
theorem VEnv.SparseSpineWF.PointwiseDefEq.snocSkip
    {env : VEnv} {U : Nat} {Γ : List VExpr}
    {source domain body argument right : VExpr} {args : List VExpr}
    {sparse : env.SparseSpineWF U Γ source args (.forallE domain body)}
    {rights : List VExpr}
    (self : sparse.PointwiseDefEq rights)
    (irrelevant : body.Skips 1 0) :
    (sparse.snocSkip (argument := argument) irrelevant).PointwiseDefEq
      (rights ++ [right]) :=
  self.append (.skip _ _ _ _ _ _ irrelevant .nil (.nil _))

/-- Synchronize a sort cursor with a mixed typed/strengthened application
trace and recover the exact next domain and its retained sort annotation. -/
theorem VEnv.SortCursor.next_of_sparse {env : VEnv}
    (henv : env.ConversionRegular)
    {U : Nat} {base : List VExpr} (hbase : OnCtx base (env.IsType U)) :
    ∀ {source sorts args cursor}, env.SortCursor U base source sorts →
      env.SparseSpineWF U base source args cursor →
      args.length < sorts.length →
      ∃ domain sort body,
        cursor = .forallE domain body ∧
        env.HasType U base domain (.sort sort) ∧
        sorts[args.length]? = some sort
  | _, [], [], _, .nil tail, .nil, hlt => by simp at hlt
  | _, _ :: _, [], _, .cons hA hrest, .nil, _ =>
      ⟨_, _, _, rfl, hA, rfl⟩
  | _, [], _ :: _, _, .nil tail, sparse, hlt => by simp at hlt
  | _, _ :: _, _ :: _, _, .cons hA htail,
      .typed harg hrest, hlt => by
      have htail' := htail.instN henv.ordered Ctx.InstN.zero harg
      obtain ⟨domain, sort, body, hcursor, hdomain, hsort⟩ :=
        htail'.next_of_sparse henv hbase hrest (by simpa using hlt)
      exact ⟨domain, sort, body, hcursor, hdomain, by simpa using hsort⟩
  | _, u :: us, arg :: args, cursor, .cons hA htail,
      .skip hskip hrest, hlt => by
      have hext : OnCtx (_ :: base) (env.IsType U) := ⟨hbase, _, hA⟩
      obtain ⟨baseBody, hbody, htail'⟩ :=
        htail.weakN_inv henv hext (Ctx.LiftN.one (A := _)) hskip
      have hrest' : env.SparseSpineWF U base baseBody args cursor := by
        rw [hbody] at hrest
        simpa only [VExpr.inst_liftN] using hrest
      obtain ⟨domain, sort, body, hcursor, hdomain, hsort⟩ :=
        htail'.next_of_sparse henv hbase hrest' (by simpa using hlt)
      exact ⟨domain, sort, body, hcursor, hdomain, by simpa using hsort⟩

/-- A one-constructor, unindexed family selected from a complete generated
block.  All identities and positions come from the block certificate; only
the field-sort inventory remains projection-specific semantic data. -/
structure VBlockStructureView where
  source : VInductDecl
  generation : source.BlockGenerationChecked
  family : NormalizedFamily
  family_mem : family ∈ generation.families
  constructor : NormalizedCtor
  constructor_eq : family.ctorPairs = [constructor]
  raw_indices_eq : family.rawIndices source.nparams = []
  checked_indices_eq : family.view.indices = []
  fieldSorts : List VLevel
  fieldSorts_length :
    fieldSorts.length = (constructor.rawFields source.nparams).length

namespace VBlockStructureView

abbrev name (view : VBlockStructureView) : Name :=
  view.family.raw.name

abbrev constructorName (view : VBlockStructureView) : Name :=
  view.constructor.raw.name

def recursorName (view : VBlockStructureView) : Name :=
  .str view.name "rec"

abbrev uvars (view : VBlockStructureView) : Nat := view.source.uvars

abbrev nparams (view : VBlockStructureView) : Nat := view.source.nparams

abbrev rawFamilyType (view : VBlockStructureView) : VExpr :=
  view.family.raw.type

abbrev resultLevel (view : VBlockStructureView) : VLevel :=
  view.generation.validated.resultLevel

/-- Projection-facing family type.  Registration keeps `rawFamilyType`, while
the selected family's checked result supplies this syntactic terminal sort. -/
def familyType (view : VBlockStructureView) : VExpr :=
  VExpr.forallN (view.family.rawParams view.nparams)
    (.sort view.resultLevel)

def constructorParams (view : VBlockStructureView) : List VExpr :=
  VExpr.telN view.nparams view.constructor.raw.type

def fields (view : VBlockStructureView) : List VExpr :=
  view.constructor.rawFields view.nparams

def structureType (view : VBlockStructureView)
    (levels : List VLevel) (params : List VExpr) : VExpr :=
  VExpr.appN (.const view.name levels) params

def specializedFields (view : VBlockStructureView)
    (levels : List VLevel) (params : List VExpr) : List VExpr :=
  view.fields.zipIdx.map fun (field, i) =>
    VExpr.instRevAt (field.instL levels) params i

/-- The selected constructor as a member of the flattened block inventory.
Its owner and family identity are inherited from the selected family rather
than reconstructed from a name lookup. -/
def blockConstructor (view : VBlockStructureView) : NormalizedBlockCtor :=
  { owner := view.family.view.ordinal
    familyName := view.family.raw.name
    familyIndices := view.family.view.indices
    ctor := view.constructor }

theorem constructor_mem (view : VBlockStructureView) :
    view.constructor ∈ view.family.ctorPairs := by
  rw [view.constructor_eq]
  simp

theorem blockConstructor_mem (view : VBlockStructureView) :
    view.blockConstructor ∈ view.generation.flatCtors := by
  simp only [BlockGenerationChecked.flatCtors,
    NormalizedCheckedBlock.flatCtors, List.mem_flatMap]
  refine ⟨view.family, view.family_mem, ?_⟩
  simp only [NormalizedFamily.blockCtors, List.mem_map]
  exact ⟨view.constructor, view.constructor_mem, rfl⟩

/-- The selected family contributes exactly its retained singleton
constructor to the flattened block inventory. -/
theorem eq_blockConstructor_of_owner
    (view : VBlockStructureView) {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ view.generation.flatCtors)
    (howner : constructor.owner = view.family.view.ordinal) :
    constructor = view.blockConstructor := by
  obtain ⟨ordinal, family, hfamilyAt, hordinal, hname, hindices,
      hctor⟩ := view.generation.flatCtors_anatomy hconstructor
  have hselectedAt :=
    view.generation.family_getElem?_ordinal view.family_mem
  have hord : ordinal = view.family.view.ordinal := by
    omega
  have hfamily : family = view.family := by
    rw [hord] at hfamilyAt
    exact Option.some.inj (hfamilyAt.symm.trans hselectedAt)
  subst family
  have hctorEq : constructor.ctor = view.constructor := by
    rw [view.constructor_eq] at hctor
    simpa using hctor
  cases constructor
  simp_all [blockConstructor]

theorem family_name_eq (view : VBlockStructureView) :
    view.family.raw.name = view.family.view.value.name :=
  (view.generation.shape.2.2.2.2 view.family view.family_mem).1

theorem family_uvars_eq (view : VBlockStructureView) :
    view.family.raw.uvars = view.uvars :=
  view.generation.family_uvars view.family_mem

theorem constructor_uvars_eq (view : VBlockStructureView) :
    view.constructor.raw.uvars = view.uvars :=
  view.generation.ctor_uvars view.family_mem view.constructor_mem

theorem checked_params_length (view : VBlockStructureView) :
    view.generation.block.checked.params.length = view.nparams :=
  view.generation.shape.2.1.symm.trans view.generation.shape.1

theorem raw_params_length (view : VBlockStructureView) :
    (view.family.rawParams view.nparams).length = view.nparams :=
  (view.generation.shape.2.2.2.2 view.family view.family_mem).2.2.1

/-- The selected raw constructor retains the complete shared-parameter Pi
prefix checked by the block analyzer. -/
theorem constructor_params_length (view : VBlockStructureView) :
    view.constructorParams.length = view.nparams := by
  exact (view.generation.shape.2.2.2.2 view.family
    view.family_mem).2.2.2.2.2.2 view.constructor view.constructor_mem |>.2.2.1

theorem fields_length (view : VBlockStructureView) :
    view.fields.length = view.constructor.view.fields.length := by
  simpa only [fields] using
    (view.generation.shape.2.2.2.2 view.family view.family_mem).2.2.2.2.2.2
      view.constructor view.constructor_mem |>.2.2.2

/-- The selected family ordinal is a valid position in the retained mutual
family inventory. -/
theorem family_ordinal_lt (view : VBlockStructureView) :
    view.family.view.ordinal < view.generation.familyCount :=
  view.generation.family_ordinal_lt view.family_mem

@[simp] theorem familyNameAt_ordinal (view : VBlockStructureView) :
    view.generation.familyNameAt view.family.view.ordinal = view.name :=
  view.generation.familyNameAt_ordinal view.family_mem

/-- The complete registered raw family telescope determines the selected
family's parameter count. -/
theorem nparams_eq_rawFamilyArity (view : VBlockStructureView) :
    view.nparams = (ctorFields view.rawFamilyType).length := by
  have split := VExpr.telN_length_add_ctorFields_dropN_length
    view.nparams view.rawFamilyType
  have paramsLength :
      (VExpr.telN view.nparams view.rawFamilyType).length = view.nparams := by
    simpa only [rawFamilyType, NormalizedFamily.rawParams] using
      view.raw_params_length
  have noIndices :
      ctorFields (VExpr.dropN view.nparams view.rawFamilyType) = [] := by
    simpa only [rawFamilyType, NormalizedFamily.rawIndices] using
      view.raw_indices_eq
  rw [paramsLength, noIndices, List.length_nil, Nat.add_zero] at split
  exact split

/-- The sort-normalized projection-facing family type has the same raw
parameter arity. -/
theorem nparams_eq_familyArity (view : VBlockStructureView) :
    view.nparams = (ctorFields view.familyType).length := by
  have fields_eq : ctorFields view.familyType =
      view.family.rawParams view.nparams := by
    change ctorFields (VExpr.forallN
      (view.family.rawParams view.nparams) (.sort view.resultLevel)) = _
    induction (view.family.rawParams view.nparams) with
    | nil => rfl
    | cons _ params ih => simp only [VExpr.forallN, ctorFields, ih]
  rw [fields_eq, view.raw_params_length]

/-- Universe arguments for the actual block recursor.  Large elimination is
instantiated at the selected field universe.  Nonselected mutual families use
the universe-polymorphic `PUnit` dummy motive, so they impose no family-result
universe constraint on the projection. -/
def projectionLevels (view : VBlockStructureView)
    (fieldSort : VLevel) (levels : List VLevel) : List VLevel :=
  match view.generation.elimination with
  | .large => fieldSort :: levels
  | .small => levels

@[simp] theorem projectionLevels_length (view : VBlockStructureView)
    (fieldSort : VLevel) (levels : List VLevel)
    (hlevels : levels.length = view.uvars) :
    (view.projectionLevels fieldSort levels).length =
      view.generation.recUvars := by
  cases hmode : view.generation.elimination <;>
    simp [projectionLevels, BlockGenerationChecked.recUvars,
      ElimMode.recUvars, ElimMode.offset, hmode, hlevels]

private theorem projectionLevels_wf (view : VBlockStructureView)
    {U : Nat} (fieldSort : VLevel) (levels : List VLevel)
    (hfieldSort : fieldSort.WF U)
    (hlevels : ∀ level ∈ levels, level.WF U) :
    ∀ level ∈ view.projectionLevels fieldSort levels, level.WF U := by
  unfold projectionLevels
  cases view.generation.elimination <;> simp_all

/-- Instantiating the declaration-universe slots embedded in the generated
recursor world at the operational projection universe spine recovers exactly
the caller's declaration universe levels. -/
theorem sourceLevels_projectionLevels (view : VBlockStructureView)
    (fieldSort : VLevel) (levels : List VLevel)
    (hlevels : levels.length = view.uvars) :
    view.generation.sourceLevels.map
        (VLevel.inst (view.projectionLevels fieldSort levels)) = levels := by
  unfold BlockGenerationChecked.sourceLevels
  unfold ElimMode.sourceLevels projectionLevels
  cases hmode : view.generation.elimination
  · change (VLevel.params' view.uvars 1).map
      (VLevel.inst (fieldSort :: levels)) = levels
    have hshift :
        (VLevel.params' view.uvars 1).map
            (VLevel.inst (fieldSort :: levels)) =
          (VLevel.params view.uvars).map (VLevel.inst levels) := by
      simp [VLevel.params', VLevel.params, List.map_map,
        Function.comp_def, VLevel.inst,
        List.getD_eq_getElem?_getD]
    rw [hshift]
    exact VLevel.inst_map_id hlevels
  · change (VLevel.params' view.uvars 0).map
      (VLevel.inst levels) = levels
    have hzero : VLevel.params' view.uvars 0 =
        VLevel.params view.uvars := by
      simp [VLevel.params', VLevel.params]
    rw [hzero]
    exact VLevel.inst_map_id hlevels

/-! ## Mutual projector syntax -/

/-- Constructor fields specialized at source universes and shared block
parameters.  This is the family-independent counterpart of
`specializedFields`. -/
def specializedCtorFields (view : VBlockStructureView)
    (constructor : NormalizedBlockCtor)
    (levels : List VLevel) (params : List VExpr) : List VExpr :=
  (constructor.ctor.rawFields view.nparams).zipIdx.map fun (field, i) =>
    VExpr.instRevAt (field.instL levels) params i

/-- One family's raw index telescope specialized at source universes and
shared parameters. -/
def specializedIndices (view : VBlockStructureView)
    (family : NormalizedFamily)
    (levels : List VLevel) (params : List VExpr) : List VExpr :=
  (family.rawIndices view.nparams).zipIdx.map fun (index, i) =>
    VExpr.instRevAt (index.instL levels) params i

/-- The selected structure family has no specialized indices. -/
@[simp] theorem specializedIndices_selected
    (view : VBlockStructureView) (levels : List VLevel)
    (params : List VExpr) :
    view.specializedIndices view.family levels params = [] := by
  simp [specializedIndices, view.raw_indices_eq]

/-- The dummy motive used for every nonselected mutual family.  It ignores
indices and the major premise and returns `PUnit` at the selected field
universe.  This permits heterogeneous mutual-family and field universes. -/
def identityMotive (view : VBlockStructureView)
    (family : NormalizedFamily)
    (fieldSort : VLevel) (levels : List VLevel)
    (params : List VExpr) : VExpr :=
  let indices := view.specializedIndices family levels params
  let familyApp := VExpr.appN (.const family.raw.name levels)
    (params.map (VExpr.liftN indices.length) ++
      VExpr.bvarRevRange 0 indices.length)
  VExpr.lamN indices (.lam familyApp (.const ``PUnit [fieldSort]))

/-- All motives supplied to the real mutual recursor.  The selected ordinal
receives the dependent field motive; every other ordinal receives its
identity motive. -/
def projectionMotives (view : VBlockStructureView)
    (levels : List VLevel) (params : List VExpr)
    (fieldSort : VLevel) (typeFn : VExpr) : List VExpr :=
  view.generation.families.map fun family =>
    if family.view.ordinal = view.family.view.ordinal then typeFn
    else view.identityMotive family fieldSort levels params

/-- The specialized type expected of one actual mutual motive. -/
def projectionMotiveType (view : VBlockStructureView)
    (family : NormalizedFamily) (fieldSort : VLevel)
    (levels : List VLevel) (params : List VExpr) : VExpr :=
  let indices := view.specializedIndices family levels params
  let familyApp := VExpr.appN (.const family.raw.name levels)
    (params.map (VExpr.liftN indices.length) ++
      VExpr.bvarRevRange 0 indices.length)
  VExpr.forallN indices (.forallE familyApp (.sort fieldSort))

/-- Specialized mutual-motive domains in family order. -/
def projectionMotiveTypes (view : VBlockStructureView)
    (fieldSort : VLevel) (levels : List VLevel)
    (params : List VExpr) : List VExpr :=
  view.generation.families.map fun family =>
    view.projectionMotiveType family fieldSort levels params

@[simp] theorem projectionMotiveTypes_length (view : VBlockStructureView)
    (fieldSort : VLevel) (levels : List VLevel)
    (params : List VExpr) :
    (view.projectionMotiveTypes fieldSort levels params).length =
      view.generation.familyCount := by
  simp [projectionMotiveTypes]

/-- Specializing one generated mutual-motive domain at the actual recursor
universes and shared parameters yields the corresponding projection domain. -/
private theorem motiveType_specialize (view : VBlockStructureView)
    (family : NormalizedFamily) (fieldSort : VLevel)
    (levels : List VLevel) (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (hmotiveLevel : view.generation.motiveLevel.inst
      (view.projectionLevels fieldSort levels) = fieldSort) :
    (((view.generation.motiveType family).instL
      (view.projectionLevels fieldSort levels)).instRev params) =
      view.projectionMotiveType family fieldSort levels params := by
  let recLevels := view.projectionLevels fieldSort levels
  let rawIndices := family.rawIndices view.nparams
  let indicesL := (view.generation.idxTel family).map
    (VExpr.instL recLevels)
  let indices := view.specializedIndices family levels params
  have hsource := view.sourceLevels_projectionLevels fieldSort levels
    hlevelsLength
  have hindicesL : indicesL = rawIndices.map (VExpr.instL levels) := by
    simp only [indicesL, rawIndices, BlockGenerationChecked.idxTel,
      List.map_map, Function.comp_def, VExpr.instL_instL]
    rw [hsource]
  have hindices :
      (indicesL.zipIdx.map fun entry =>
        entry.1.instRevAt params entry.2) = indices := by
    rw [hindicesL, VExpr.instRevAt_map_instL_zipIdx]
    rfl
  have hindicesLength : indicesL.length = indices.length := by
    rw [hindicesL]
    simp [rawIndices, indices, specializedIndices]
  have hparamsRange :
      (VExpr.bvarRevRange indices.length view.nparams).map
          (fun expression => expression.instRevAt params indices.length) =
        params.map (VExpr.liftN indices.length) := by
    have hout := VExpr.map_instRevAt_bvarRevRange params indices.length
    rw [hparamsLength] at hout
    exact hout
  unfold BlockGenerationChecked.motiveType
  rw [VExpr.instL_forallN]
  simp only [VExpr.instL]
  rw [VExpr.instRev_forallN_projection, hindices]
  simp only [projectionMotiveType]
  change VExpr.forallN indices _ = VExpr.forallN indices _
  congr 1
  rw [VExpr.instRevAt_forallE_projection]
  rw [hmotiveLevel]
  congr 1
  · rw [VExpr.instL_appN, VExpr.instRevAt_appN_projection]
    rw [VExpr.instRevAt_closedN params (by trivial)]
    simp only [VExpr.instL]
    rw [hsource]
    rw [List.map_append, VExpr.bvarRevRange_map_instL,
      VExpr.bvarRevRange_map_instL]
    rw [show (view.generation.idxTel family).length = indices.length by
      rw [← hindicesLength]
      simp [indicesL]]
    rw [show (view.generation.idxTel family |>.map
        (VExpr.instL recLevels)).length = indices.length by
      simpa [indicesL] using hindicesLength]
    change VExpr.appN (.const family.raw.name levels) _ =
      VExpr.appN (.const family.raw.name levels)
        (params.map (VExpr.liftN indices.length) ++
          VExpr.bvarRevRange 0 indices.length)
    rw [List.map_append]
    rw [hparamsRange]
    -- Each retained index variable lies below the parameter substitution.
    have hvars' :
        (VExpr.bvarRevRange 0 indices.length).map
            (fun expression => expression.instRevAt params indices.length) =
          VExpr.bvarRevRange 0 indices.length := by
      calc
        _ = (VExpr.bvarRevRange 0 indices.length).map id := by
          apply List.map_congr_left
          intro expression hexpression
          obtain ⟨i, rfl, -, hi⟩ := VExpr.mem_bvarRevRange hexpression
          have hvar : ∀ (arguments : List VExpr),
              (VExpr.bvar i).instRevAt arguments indices.length = .bvar i := by
            intro arguments
            induction arguments with
            | nil => rfl
            | cons argument arguments ih =>
                simp only [VExpr.instRevAt]
                rw [show (VExpr.bvar i).inst argument
                    (indices.length + arguments.length) = .bvar i by
                  simp [VExpr.inst, VExpr.instVar, show
                    i < indices.length + arguments.length from by omega]]
                exact ih
          exact hvar params
        _ = _ := by simp
    rw [hvars']
  · exact VExpr.instRevAt_closedN params (by trivial)

/-- Public producer-facing form of the exact motive-domain specialization
identity.  Restored projection programs use this equality before applying
nested restoration, while the formal parameter variables are still inert. -/
theorem motiveType_specialize_exact (view : VBlockStructureView)
    (family : NormalizedFamily) (fieldSort : VLevel)
    (levels : List VLevel) (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (hmotiveLevel : view.generation.motiveLevel.inst
      (view.projectionLevels fieldSort levels) = fieldSort) :
    (((view.generation.motiveType family).instL
      (view.projectionLevels fieldSort levels)).instRev params) =
      view.projectionMotiveType family fieldSort levels params :=
  view.motiveType_specialize family fieldSort levels hlevelsLength params
    hparamsLength hmotiveLevel

private theorem motiveType_lift_specialize (view : VBlockStructureView)
    (family : NormalizedFamily) (fieldSort : VLevel)
    (levels : List VLevel) (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (hmotiveLevel : view.generation.motiveLevel.inst
      (view.projectionLevels fieldSort levels) = fieldSort)
    (index : Nat) :
    ((((view.generation.motiveType family).liftN index).instL
        (view.projectionLevels fieldSort levels)).instRevAt params index) =
      (view.projectionMotiveType family fieldSort levels params).liftN index := by
  rw [VExpr.instL_liftN, VExpr.liftN_instRevAt_same]
  rw [view.motiveType_specialize family fieldSort levels hlevelsLength
    params hparamsLength hmotiveLevel]

/-- After the shared parameters are consumed, the generated progressive
motive telescope is the progressive lifting of the concrete projection
motive domains. -/
private theorem motiveTypes_specialize (view : VBlockStructureView)
    (fieldSort : VLevel) (levels : List VLevel)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (hmotiveLevel : view.generation.motiveLevel.inst
      (view.projectionLevels fieldSort levels) = fieldSort) :
    (((view.generation.motiveTypes.map
        (VExpr.instL (view.projectionLevels fieldSort levels))).zipIdx.map
      fun entry => entry.1.instRevAt params entry.2)) =
      ((view.projectionMotiveTypes fieldSort levels params).zipIdx.map
        fun entry => entry.1.liftN entry.2) := by
  apply List.ext_getElem?
  intro index
  simp only [List.getElem?_map, List.getElem?_zipIdx]
  rw [show view.generation.motiveTypes =
      view.generation.motiveTypesAux view.generation.families 0 from rfl,
    view.generation.motiveTypesAux_getElem?]
  simp only [projectionMotiveTypes, List.getElem?_map]
  cases hfamily : view.generation.families[index]? with
  | none => simp [hfamily]
  | some family =>
      simp only [hfamily, Option.map_some]
      exact congrArg some <| by
        simpa using view.motiveType_lift_specialize family fieldSort levels
          hlevelsLength params hparamsLength hmotiveLevel index

@[simp] theorem projectionMotives_length (view : VBlockStructureView)
    (levels : List VLevel) (params : List VExpr) (fieldSort : VLevel)
    (typeFn : VExpr) :
    (view.projectionMotives levels params fieldSort typeFn).length =
      view.generation.familyCount := by
  simp [projectionMotives]

theorem projectionMotives_getElem?_ordinal
    (view : VBlockStructureView) (family : NormalizedFamily)
    (hfamily : family ∈ view.generation.families)
    (levels : List VLevel) (params : List VExpr)
    (fieldSort : VLevel) (typeFn : VExpr) :
    (view.projectionMotives levels params fieldSort typeFn)[family.view.ordinal]? =
      some (if family.view.ordinal = view.family.view.ordinal then typeFn
        else view.identityMotive family fieldSort levels params) := by
  rw [projectionMotives, List.getElem?_map,
    view.generation.family_getElem?_ordinal hfamily]
  rfl

/-- The exact generated block-minor domain after specializing recursor
universes, block parameters, and all mutual motives. -/
def generatedProjectionMinorType (view : VBlockStructureView)
    (constructor : NormalizedBlockCtor)
    (fieldSort : VLevel) (levels : List VLevel) (params : List VExpr)
    (motives : List VExpr) : VExpr :=
  (((view.generation.minorType constructor).instL
      (view.projectionLevels fieldSort levels)).instRevAt params
        view.generation.familyCount).instRev motives

/-- The terminal arguments supplied to a constructor owner's motive after
the exact mutual minor telescope is specialized. -/
def generatedProjectionMinorArguments
    (view : VBlockStructureView) (constructor : NormalizedBlockCtor)
    (fieldSort : VLevel) (levels : List VLevel)
    (params motives : List VExpr) : List VExpr :=
  let d := view.generation.familyCount
  let rawFields := constructor.ctor.fieldsR view.uvars view.nparams
    view.generation.elimination
  let m := rawFields.length
  let recArgs := constructor.ctor.recArgsR view.uvars
    view.generation.elimination
  let r := recArgs.length
  let recLevels := view.projectionLevels fieldSort levels
  let rawArguments :=
      (constructor.ctor.resultIndicesR view.uvars
        view.generation.elimination |>.map fun expression =>
          (expression.liftN d m).liftN r) ++
        [VExpr.appN
          (.const constructor.ctor.raw.name view.generation.sourceLevels)
          (VExpr.bvarRevRange (r + m + d) view.nparams ++
            VExpr.bvarRevRange r m)]
  (rawArguments.map (VExpr.instL recLevels)).map
    (fun expression => expression.instRevAt (params ++ motives) (m + r))

/-- Fully specialized flattened mutual-minor domains. -/
def projectionMinorTypes (view : VBlockStructureView)
    (fieldSort : VLevel) (levels : List VLevel)
    (params motives : List VExpr) : List VExpr :=
  view.generation.flatCtors.map fun constructor =>
    view.generatedProjectionMinorType constructor fieldSort levels
      params motives

@[simp] theorem projectionMinorTypes_length (view : VBlockStructureView)
    (fieldSort : VLevel) (levels : List VLevel)
    (params motives : List VExpr) :
    (view.projectionMinorTypes fieldSort levels params motives).length =
      view.generation.minorCount := by
  simp [projectionMinorTypes]

/-- A progressively weakened generated minor, after the shared parameters
and complete motive inventory are consumed, is the corresponding concrete
projection-minor domain weakened past the earlier minors. -/
private theorem generatedProjectionMinorType_lift_specialize
    (view : VBlockStructureView) (constructor : NormalizedBlockCtor)
    (fieldSort : VLevel) (levels : List VLevel) (params motives : List VExpr)
    (index : Nat) :
    (((((view.generation.minorType constructor).liftN index).instL
          (view.projectionLevels fieldSort levels)).instRevAt params
            (view.generation.familyCount + index)).instRevAt motives index) =
      (view.generatedProjectionMinorType constructor fieldSort levels params
        motives).liftN index := by
  rw [VExpr.instL_liftN,
    VExpr.liftN_instRevAt_shift,
    VExpr.liftN_instRevAt_same]
  rfl

/-- After the shared parameters and every motive are consumed, the generated
flattened-minor telescope is the progressive lifting of the exact concrete
minor domains supplied by a projection program. -/
private theorem minorTypes_specialize
    (view : VBlockStructureView) (fieldSort : VLevel)
    (levels : List VLevel) (params motives : List VExpr) :
    (((((view.generation.minorTypes.map
        (VExpr.instL (view.projectionLevels fieldSort levels))).zipIdx
          view.generation.familyCount |>.map
          fun entry => entry.1.instRevAt params entry.2)).zipIdx.map
          fun entry => entry.1.instRevAt motives entry.2)) =
      ((view.projectionMinorTypes fieldSort levels params motives).zipIdx.map
        fun entry => entry.1.liftN entry.2) := by
  apply List.ext_getElem?
  intro index
  simp only [List.getElem?_map, List.getElem?_zipIdx]
  rw [show view.generation.minorTypes =
      view.generation.minorTypesAux view.generation.flatCtors 0 from rfl,
    view.generation.minorTypesAux_getElem?]
  simp only [projectionMinorTypes, List.getElem?_map]
  cases hconstructor : view.generation.flatCtors[index]? with
  | none => simp [hconstructor]
  | some constructor =>
      simp only [hconstructor, Option.map_some]
      exact congrArg some <| by
        simpa using view.generatedProjectionMinorType_lift_specialize
          constructor fieldSort levels params motives index

/-- The selected constructor's mutual induction-hypothesis telescope after
the exact block minor has been specialized. -/
def projectionIHTypes (view : VBlockStructureView)
    (fieldSort : VLevel) (levels : List VLevel) (params : List VExpr)
    (motives : List VExpr) : List VExpr :=
  VExpr.telN view.constructor.view.recursive.length <|
    VExpr.dropN (view.specializedFields levels params).length <|
      view.generatedProjectionMinorType view.blockConstructor fieldSort
        levels params motives

/-- Return the canonical `PUnit` inhabitant after all fields and generated
mutual induction hypotheses of a nonselected constructor are introduced. -/
def identityMinor (view : VBlockStructureView)
    (constructor : NormalizedBlockCtor)
    (fieldSort : VLevel) (levels : List VLevel) (params : List VExpr)
    (motives : List VExpr) : VExpr :=
  let fields := view.specializedCtorFields constructor levels params
  let exactMinor := view.generatedProjectionMinorType constructor
    fieldSort levels params motives
  let binderCount := fields.length + constructor.ctor.view.recursive.length
  let binders := VExpr.telN binderCount exactMinor
  VExpr.lamN binders (.const ``PUnit.unit [fieldSort])

/-! ### Prelude-free operational dummy payloads

The persistent layout API cannot assume that an unrelated `PUnit`
declaration is present.  Operational mutual projectors instead manufacture
an inhabited carrier underneath their major binder.  The following
parameterized syntax is deliberately separate from the legacy closed
`PUnit` presentation above while the typing proofs are migrated. -/

/-- A dummy motive returning an arbitrary ambient type.  `dummyType` lives
in the context outside the generated index and family-major binders. -/
def identityMotiveWith (view : VBlockStructureView)
    (family : NormalizedFamily) (levels : List VLevel)
    (params : List VExpr) (dummyType : VExpr) : VExpr :=
  let indices := view.specializedIndices family levels params
  let familyApp := VExpr.appN (.const family.raw.name levels)
    (params.map (VExpr.liftN indices.length) ++
      VExpr.bvarRevRange 0 indices.length)
  VExpr.lamN indices <|
    .lam familyApp (dummyType.liftN (indices.length + 1))

/-- Mutual motives with a caller-supplied inhabited dummy carrier for every
nonselected family. -/
def projectionMotivesWith (view : VBlockStructureView)
    (levels : List VLevel) (params : List VExpr)
    (typeFn dummyType : VExpr) : List VExpr :=
  view.generation.families.map fun family =>
    if family.view.ordinal = view.family.view.ordinal then typeFn
    else view.identityMotiveWith family levels params dummyType

@[simp] theorem projectionMotivesWith_length (view : VBlockStructureView)
    (levels : List VLevel) (params : List VExpr)
    (typeFn dummyType : VExpr) :
    (view.projectionMotivesWith levels params typeFn dummyType).length =
      view.generation.familyCount := by
  simp [projectionMotivesWith]

theorem projectionMotivesWith_getElem?_ordinal
    (view : VBlockStructureView) (family : NormalizedFamily)
    (hfamily : family ∈ view.generation.families)
    (levels : List VLevel) (params : List VExpr)
    (typeFn dummyType : VExpr) :
    (view.projectionMotivesWith levels params typeFn dummyType)[family.view.ordinal]? =
      some (if family.view.ordinal = view.family.view.ordinal then typeFn
        else view.identityMotiveWith family levels params dummyType) := by
  rw [projectionMotivesWith, List.getElem?_map,
    view.generation.family_getElem?_ordinal hfamily]
  rfl

/-- A dummy minor returning an arbitrary ambient inhabitant. -/
def identityMinorWith (view : VBlockStructureView)
    (constructor : NormalizedBlockCtor)
    (fieldSort : VLevel) (levels : List VLevel) (params : List VExpr)
    (motives : List VExpr) (dummyValue : VExpr) : VExpr :=
  let fields := view.specializedCtorFields constructor levels params
  let exactMinor := view.generatedProjectionMinorType constructor
    fieldSort levels params motives
  let binderCount := fields.length + constructor.ctor.view.recursive.length
  let binders := VExpr.telN binderCount exactMinor
  VExpr.lamN binders (dummyValue.liftN binders.length)

/-- One flattened minor using the supplied dummy inhabitant away from the
selected family. -/
def projectionMinorWith (view : VBlockStructureView)
    (constructor : NormalizedBlockCtor)
    (fieldSort : VLevel) (levels : List VLevel)
    (params allFields motives : List VExpr) (fieldIndex : Nat)
    (dummyValue : VExpr) : VExpr :=
  if constructor.owner = view.family.view.ordinal then
    VExpr.selectFieldMinor allFields
      (view.projectionIHTypes fieldSort levels params motives) fieldIndex
  else
    view.identityMinorWith constructor fieldSort levels params motives
      dummyValue

/-- The carrier `F → F`, where `F := typeFn major`, available beneath a
projector's major binder at precisely the selected field universe. -/
def majorDummyType (typeFn major : VExpr) : VExpr :=
  let carrier := .app typeFn major
  .forallE carrier carrier.lift

/-- The identity inhabitant of `majorDummyType`. -/
def majorDummyValue (typeFn major : VExpr) : VExpr :=
  let carrier := .app typeFn major
  .lam carrier (.bvar 0)

/-- The major-local identity carrier lives in the same universe as the
selected projection field. -/
theorem majorDummyType_hasType {env : VEnv} (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} {typeFn major : VExpr}
    {fieldSort : VLevel}
    (hfieldSort : fieldSort.WF U)
    (hcarrierType : env.HasType U Γ (VExpr.app typeFn major)
      (.sort fieldSort)) :
    env.HasType U Γ (majorDummyType typeFn major) (.sort fieldSort) := by
  have hcarrierWeak : env.HasType U (VExpr.app typeFn major :: Γ)
      (VExpr.app typeFn major).lift (.sort fieldSort) := by
    change env.IsDefEq U (VExpr.app typeFn major :: Γ)
      (VExpr.app typeFn major).lift (VExpr.app typeFn major).lift
      (.sort fieldSort)
    simpa only [VExpr.liftN] using
      hcarrierType.weak (B := VExpr.app typeFn major) henv
  have hraw := hcarrierType.forallE hcarrierWeak
  apply VEnv.IsDefEq.defeq
    (VEnv.IsDefEq.sortDF (by exact ⟨hfieldSort, hfieldSort⟩)
      hfieldSort VLevel.imax_self)
  simpa [majorDummyType] using hraw

/-- The identity function inhabits the major-local dummy carrier. -/
theorem majorDummyValue_hasType {env : VEnv} (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} {typeFn major : VExpr}
    {fieldSort : VLevel}
    (hcarrierType : env.HasType U Γ (VExpr.app typeFn major)
      (.sort fieldSort)) :
    env.HasType U Γ (majorDummyValue typeFn major)
      (majorDummyType typeFn major) := by
  have hbody : env.HasType U (VExpr.app typeFn major :: Γ) (.bvar 0)
      (VExpr.app typeFn major).lift := .bvar .zero
  simpa [majorDummyType, majorDummyValue] using hcarrierType.lam hbody

/-- One argument in the complete flattened mutual minor spine.  The selected
family's unique constructor gets the field selector; all other constructors
get identity rebuilds. -/
def projectionMinor (view : VBlockStructureView)
    (constructor : NormalizedBlockCtor)
    (fieldSort : VLevel) (levels : List VLevel)
    (params allFields : List VExpr)
    (motives : List VExpr) (fieldIndex : Nat) : VExpr :=
  if constructor.owner = view.family.view.ordinal then
    VExpr.selectFieldMinor allFields
      (view.projectionIHTypes fieldSort levels params motives) fieldIndex
  else
    view.identityMinor constructor fieldSort levels params motives

private def projectionCode (view : VBlockStructureView)
    (levels : List VLevel) (params allFields : List VExpr)
    (structType field : VExpr) (fieldSort : VLevel) (fieldIndex : Nat)
    (previous : List VStructureView.ProjectionCode) :
    VStructureView.ProjectionCode :=
  let previousAtMajor := previous.map fun code =>
    .app code.projector.lift (.bvar 0)
  let motiveBody := VExpr.instRevAt
    (field.liftN 1 fieldIndex) previousAtMajor 0
  let typeFn := .lam structType motiveBody
  let motives := view.projectionMotives levels params fieldSort typeFn
  let minors := view.generation.flatCtors.map fun constructor =>
    view.projectionMinor constructor fieldSort levels params allFields
      motives fieldIndex
  let minor := view.projectionMinor view.blockConstructor fieldSort levels params
    allFields motives fieldIndex
  let recursor :=
    .const view.recursorName (view.projectionLevels fieldSort levels)
  let projector := .lam structType <| VExpr.appN recursor <|
    params.map (VExpr.liftN 1) ++ motives.map (VExpr.liftN 1) ++
      minors.map (VExpr.liftN 1) ++ [.bvar 0]
  { fieldSort, typeFn, minor, projector }

/-- The actual prelude-free mutual recursor program under its selected-major
binder. -/
def operationalProjector (view : VBlockStructureView)
    (levels : List VLevel) (params allFields : List VExpr)
    (structType : VExpr) (fieldSort : VLevel) (fieldIndex : Nat)
    (typeFn : VExpr) : VExpr :=
  let paramsMajor := params.map (VExpr.liftN 1)
  let allFieldsMajor := VExpr.liftTelN 1 allFields 0
  let typeFnMajor := typeFn.lift
  let major := VExpr.bvar 0
  let dummyType := majorDummyType typeFnMajor major
  let dummyValue := majorDummyValue typeFnMajor major
  let motives := view.projectionMotivesWith levels paramsMajor
    typeFnMajor dummyType
  let minors := view.generation.flatCtors.map fun constructor =>
    view.projectionMinorWith constructor fieldSort levels paramsMajor
      allFieldsMajor motives fieldIndex dummyValue
  let recursor :=
    .const view.recursorName (view.projectionLevels fieldSort levels)
  .lam structType <| VExpr.appN recursor <|
    paramsMajor ++ motives ++ minors ++ [major]

/-- Small elimination erases the requested motive universe from the
operational projector syntax. -/
theorem operationalProjector_eq_of_small
    (view : VBlockStructureView)
    (hsmall : view.generation.elimination = .small)
    (levels : List VLevel) (params allFields : List VExpr)
    (structType : VExpr) (left right : VLevel) (fieldIndex : Nat)
    (typeFn : VExpr) :
    view.operationalProjector levels params allFields structType left
        fieldIndex typeFn =
      view.operationalProjector levels params allFields structType right
        fieldIndex typeFn := by
  simp [operationalProjector, projectionMinorWith, identityMinorWith,
    projectionIHTypes, generatedProjectionMinorType, projectionLevels,
    hsmall]

/-- A block projector whose nonselected mutual motives and minors obtain
their dummy payload from the selected major itself.  The auxiliary `minor`
slot is intentionally set to `typeFn`; operational proofs inspect the local
minor inventory retained in `projector`, while generic consumers use only
`fieldSort`, `typeFn`, and `projector`. -/
private def operationalProjectionCode (view : VBlockStructureView)
    (levels : List VLevel) (params allFields : List VExpr)
    (structType field : VExpr) (fieldSort : VLevel) (fieldIndex : Nat)
    (previous : List VStructureView.ProjectionCode) :
    VStructureView.ProjectionCode :=
  let previousAtMajor := previous.map fun code =>
    .app code.projector.lift (.bvar 0)
  let motiveBody := VExpr.instRevAt
    (field.liftN 1 fieldIndex) previousAtMajor 0
  let typeFn := .lam structType motiveBody
  let projector := view.operationalProjector levels params allFields
    structType fieldSort fieldIndex typeFn
  { fieldSort, typeFn, minor := typeFn, projector }

private def projectionCodes.go (view : VBlockStructureView)
    (levels : List VLevel) (params allFields : List VExpr)
    (structType : VExpr) :
    List VExpr → List VLevel → Nat →
      List VStructureView.ProjectionCode →
      List VStructureView.ProjectionCode
  | field :: fields, fieldSort :: fieldSorts, fieldIndex, previous =>
      let code := view.projectionCode levels params allFields structType
        field fieldSort fieldIndex previous
      code :: projectionCodes.go view levels params allFields structType
        fields fieldSorts (fieldIndex + 1) (previous ++ [code])
  | _, _, _, _ => []

private def operationalProjectionCodes.go (view : VBlockStructureView)
    (levels : List VLevel) (params allFields : List VExpr)
    (structType : VExpr) :
    List VExpr → List VLevel → Nat →
      List VStructureView.ProjectionCode →
      List VStructureView.ProjectionCode
  | field :: fields, fieldSort :: fieldSorts, fieldIndex, previous =>
      let code := view.operationalProjectionCode levels params allFields
        structType field fieldSort fieldIndex previous
      code :: operationalProjectionCodes.go view levels params allFields
        structType fields fieldSorts (fieldIndex + 1) (previous ++ [code])
  | _, _, _, _ => []

/-- Prelude-free mutual projector programs. -/
def operationalProjectionCodes (view : VBlockStructureView)
    (levels : List VLevel) (params : List VExpr) :
    List VStructureView.ProjectionCode :=
  let fields := view.specializedFields levels params
  operationalProjectionCodes.go view levels params fields
    (view.structureType levels params) fields
      (view.fieldSorts.map (VLevel.inst levels)) 0 []

private theorem operationalProjectionCodes.go_length
    (view : VBlockStructureView) (levels : List VLevel)
    (params allFields : List VExpr) (structType : VExpr) :
    ∀ (fields : List VExpr) (fieldSorts : List VLevel)
      (fieldIndex : Nat) (previous : List VStructureView.ProjectionCode),
      fields.length = fieldSorts.length →
      (operationalProjectionCodes.go view levels params allFields structType
        fields fieldSorts fieldIndex previous).length = fields.length
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | _ :: fields, _ :: fieldSorts, fieldIndex, previous, h => by
      simp only [List.length_cons] at h ⊢
      simp only [operationalProjectionCodes.go, List.length_cons]
      exact congrArg Nat.succ <|
        operationalProjectionCodes.go_length view levels params allFields
          structType fields fieldSorts (fieldIndex + 1) (_ ++ [_])
          (Nat.succ.inj h)

@[simp] theorem operationalProjectionCodes_length
    (view : VBlockStructureView) (levels : List VLevel)
    (params : List VExpr) :
    (view.operationalProjectionCodes levels params).length =
      (view.specializedFields levels params).length := by
  apply operationalProjectionCodes.go_length
  simp [specializedFields, fields, view.fieldSorts_length]

private theorem operationalProjectionCodes.go_get?_typeFn
    (view : VBlockStructureView)
    (levels : List VLevel) (params allFields : List VExpr)
    (structType : VExpr) :
    ∀ {fields : List VExpr} {fieldSorts : List VLevel}
      {fieldIndex : Nat} {previous : List VStructureView.ProjectionCode}
      {offset : Nat} {code : VStructureView.ProjectionCode},
      (operationalProjectionCodes.go view levels params allFields structType
        fields fieldSorts fieldIndex previous)[offset]? = some code →
      ∃ field,
        fields[offset]? = some field ∧
        code.typeFn = .lam structType
          ((field.liftN 1 (fieldIndex + offset)).instRevAt
            ((previous ++
              (operationalProjectionCodes.go view levels params allFields
                structType fields fieldSorts fieldIndex previous).take
                  offset).map
              fun prior => .app prior.projector.lift (.bvar 0)) 0) := by
  intro fields
  induction fields with
  | nil =>
      intro fieldSorts fieldIndex previous offset code h
      cases fieldSorts <;>
        simp [operationalProjectionCodes.go] at h
  | cons field fields ih =>
      intro fieldSorts fieldIndex previous offset code h
      cases fieldSorts with
      | nil => simp [operationalProjectionCodes.go] at h
      | cons fieldSort fieldSorts =>
          let head := operationalProjectionCode view levels params allFields
            structType field fieldSort fieldIndex previous
          cases offset with
          | zero =>
              change some head = some code at h
              injection h with hcode
              subst code
              refine ⟨field, rfl, ?_⟩
              simp [head, operationalProjectionCode]
          | succ offset =>
              simp only [operationalProjectionCodes.go,
                List.getElem?_cons_succ] at h
              obtain ⟨tailField, htailField, htypeFn⟩ :=
                ih (fieldSorts := fieldSorts)
                  (fieldIndex := fieldIndex + 1)
                  (previous := previous ++ [head]) h
              refine ⟨tailField, by simpa using htailField, ?_⟩
              have hpref :
                  previous ++
                    (operationalProjectionCodes.go view levels params
                      allFields structType (field :: fields)
                      (fieldSort :: fieldSorts) fieldIndex previous).take
                        (offset + 1) =
                    (previous ++ [head]) ++
                      (operationalProjectionCodes.go view levels params
                        allFields structType fields fieldSorts
                        (fieldIndex + 1) (previous ++ [head])).take offset := by
                simp [head, operationalProjectionCodes.go,
                  List.append_assoc]
              rw [hpref]
              simpa only [Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using htypeFn

theorem operationalProjectionCodes_get?_typeFn
    (view : VBlockStructureView) (levels : List VLevel)
    (params : List VExpr) {idx : Nat}
    {code : VStructureView.ProjectionCode}
    (hcode : (view.operationalProjectionCodes levels params)[idx]? =
      some code) :
    ∃ field,
      (view.specializedFields levels params)[idx]? = some field ∧
      code.typeFn = .lam (view.structureType levels params)
        ((field.liftN 1 idx).instRevAt
          ((view.operationalProjectionCodes levels params).take idx |>.map
            fun prior => .app prior.projector.lift (.bvar 0)) 0) := by
  unfold operationalProjectionCodes at hcode ⊢
  simpa using operationalProjectionCodes.go_get?_typeFn view levels params
    (view.specializedFields levels params)
    (view.structureType levels params) hcode

private theorem operationalProjectionCodes.go_get?_program_shape
    (view : VBlockStructureView) (levels : List VLevel)
    (params allFields : List VExpr) (structType : VExpr) :
    ∀ {fields : List VExpr} {fieldSorts : List VLevel}
      {fieldIndex : Nat} {previous : List VStructureView.ProjectionCode}
      {offset : Nat} {code : VStructureView.ProjectionCode},
      (operationalProjectionCodes.go view levels params allFields structType
        fields fieldSorts fieldIndex previous)[offset]? = some code →
      ∃ fieldSort,
        fieldSorts[offset]? = some fieldSort ∧
        code.fieldSort = fieldSort ∧
        code.minor = code.typeFn ∧
        code.projector = view.operationalProjector levels params allFields
          structType fieldSort (fieldIndex + offset) code.typeFn := by
  intro fields
  induction fields with
  | nil =>
      intro fieldSorts fieldIndex previous offset code h
      cases fieldSorts <;>
        simp [operationalProjectionCodes.go] at h
  | cons field fields ih =>
      intro fieldSorts fieldIndex previous offset code h
      cases fieldSorts with
      | nil => simp [operationalProjectionCodes.go] at h
      | cons fieldSort fieldSorts =>
          let head := operationalProjectionCode view levels params allFields
            structType field fieldSort fieldIndex previous
          cases offset with
          | zero =>
              change some head = some code at h
              injection h with hcode
              subst code
              simp [head, operationalProjectionCode]
          | succ offset =>
              simp only [operationalProjectionCodes.go,
                List.getElem?_cons_succ] at h
              have hout := ih (fieldSorts := fieldSorts)
                (fieldIndex := fieldIndex + 1)
                (previous := previous ++ [head]) h
              simpa only [List.getElem?_cons_succ, Nat.add_assoc,
                Nat.add_comm, Nat.add_left_comm] using hout

theorem operationalProjectionCodes_get?_program_shape
    (view : VBlockStructureView) (levels : List VLevel)
    (params : List VExpr) {idx : Nat}
    {code : VStructureView.ProjectionCode}
    (hcode : (view.operationalProjectionCodes levels params)[idx]? =
      some code) :
    ∃ fieldSort,
      (view.fieldSorts.map (VLevel.inst levels))[idx]? = some fieldSort ∧
      code.fieldSort = fieldSort ∧
      code.minor = code.typeFn ∧
      code.projector = view.operationalProjector levels params
        (view.specializedFields levels params)
        (view.structureType levels params) fieldSort idx code.typeFn := by
  unfold operationalProjectionCodes at hcode
  simpa using operationalProjectionCodes.go_get?_program_shape view levels
    params (view.specializedFields levels params)
    (view.structureType levels params) hcode

/-- All block-backed field projectors in constructor-field order.  Every
projector applies the actual selected mutual recursor to the complete motive
and flattened-minor inventories. -/
def projectionCodes (view : VBlockStructureView)
    (levels : List VLevel) (params : List VExpr) :
    List VStructureView.ProjectionCode :=
  let fields := view.specializedFields levels params
  projectionCodes.go view levels params fields
    (view.structureType levels params) fields
      (view.fieldSorts.map (VLevel.inst levels)) 0 []

/-- Semantic arguments substituted while walking to a later dependent
block-backed projection field. -/
def projectionArgs (view : VBlockStructureView) (levels : List VLevel)
    (params : List VExpr) (count : Nat) (major : VExpr) : List VExpr :=
  (view.projectionCodes levels params).take count |>.map fun code =>
    .app code.projector major

/-- Semantic arguments obtained from the prelude-free operational projector
prefix. -/
def operationalProjectionArgs (view : VBlockStructureView)
    (levels : List VLevel) (params : List VExpr) (count : Nat)
    (major : VExpr) : List VExpr :=
  (view.operationalProjectionCodes levels params).take count |>.map fun code =>
    .app code.projector major

/-- The selected constructor applied to the canonical parameter and field
variables in the complete field context. -/
def projectionConstructorApp (view : VBlockStructureView)
    (levels : List VLevel) (params fields : List VExpr) : VExpr :=
  VExpr.appN (.const view.constructorName levels)
    (params.map (VExpr.liftN fields.length) ++
      VExpr.bvarRevRange 0 fields.length)

/-- Rebuild the selected family value from all block-backed canonical
projections. -/
def etaRebuild (view : VBlockStructureView) (levels : List VLevel)
    (params : List VExpr) (major : VExpr) : VExpr :=
  VExpr.appN (.const view.constructorName levels)
    (params ++ view.projectionArgs levels params
      (view.specializedFields levels params).length major)

/-- Rebuild the selected family value from the prelude-free operational
projection programs. -/
def operationalEtaRebuild (view : VBlockStructureView)
    (levels : List VLevel) (params : List VExpr) (major : VExpr) : VExpr :=
  VExpr.appN (.const view.constructorName levels)
    (params ++ view.operationalProjectionArgs levels params
      (view.specializedFields levels params).length major)

@[simp] theorem projectionLevels_instL (view : VBlockStructureView)
    (fieldSort : VLevel) (levels ls : List VLevel) :
    (view.projectionLevels fieldSort levels).map (VLevel.inst ls) =
      view.projectionLevels (fieldSort.inst ls)
        (levels.map (VLevel.inst ls)) := by
  unfold projectionLevels
  split <;> simp [VLevel.inst_inst]

@[simp] theorem structureType_instL (view : VBlockStructureView)
    (levels : List VLevel) (params : List VExpr) (ls : List VLevel) :
    (view.structureType levels params).instL ls =
      view.structureType (levels.map (VLevel.inst ls))
        (params.map (VExpr.instL ls)) := by
  simp [structureType, VExpr.instL_appN, VExpr.instL]

@[simp] theorem structureType_liftN (view : VBlockStructureView)
    (levels : List VLevel) (params : List VExpr) (n k : Nat) :
    (view.structureType levels params).liftN n k =
      view.structureType levels
        (params.map fun param => param.liftN n k) := by
  simp [structureType, VExpr.liftN_appN, VExpr.liftN]

@[simp] theorem structureType_instN (view : VBlockStructureView)
    (levels : List VLevel) (params : List VExpr) (a : VExpr) (k : Nat) :
    (view.structureType levels params).inst a k =
      view.structureType levels
        (params.map fun param => param.inst a k) := by
  simp [structureType, VExpr.instN_appN, VExpr.inst]

@[simp] theorem specializedFields_instL (view : VBlockStructureView)
    (levels : List VLevel) (params : List VExpr) (ls : List VLevel) :
    (view.specializedFields levels params).map (VExpr.instL ls) =
      view.specializedFields (levels.map (VLevel.inst ls))
        (params.map (VExpr.instL ls)) := by
  simp [specializedFields, VExpr.instL_instRevAt,
    VExpr.instL_instL, Function.comp_def]

@[simp] theorem specializedCtorFields_instL (view : VBlockStructureView)
    (constructor : NormalizedBlockCtor)
    (levels : List VLevel) (params : List VExpr) (ls : List VLevel) :
    (view.specializedCtorFields constructor levels params).map
        (VExpr.instL ls) =
      view.specializedCtorFields constructor
        (levels.map (VLevel.inst ls))
        (params.map (VExpr.instL ls)) := by
  simp [specializedCtorFields, VExpr.instL_instRevAt,
    VExpr.instL_instL, Function.comp_def]

@[simp] theorem specializedIndices_instL (view : VBlockStructureView)
    (family : NormalizedFamily)
    (levels : List VLevel) (params : List VExpr) (ls : List VLevel) :
    (view.specializedIndices family levels params).map (VExpr.instL ls) =
      view.specializedIndices family (levels.map (VLevel.inst ls))
        (params.map (VExpr.instL ls)) := by
  simp [specializedIndices, VExpr.instL_instRevAt,
    VExpr.instL_instL, Function.comp_def]

@[simp] theorem identityMotive_instL (view : VBlockStructureView)
    (family : NormalizedFamily)
    (fieldSort : VLevel) (levels : List VLevel)
    (params : List VExpr) (ls : List VLevel) :
    (view.identityMotive family fieldSort levels params).instL ls =
      view.identityMotive family (fieldSort.inst ls)
        (levels.map (VLevel.inst ls))
        (params.map (VExpr.instL ls)) := by
  have hindices :
      (view.specializedIndices family levels params).length =
        (view.specializedIndices family (levels.map (VLevel.inst ls))
          (params.map (VExpr.instL ls))).length := by
    simp [specializedIndices]
  simp only [identityMotive]
  rw [VExpr.instL_lamN, specializedIndices_instL, hindices]
  simp [VExpr.instL, VExpr.instL_appN, VExpr.instL_liftN,
    VExpr.bvarRevRange_map_instL,
    List.map_append, List.map_map, Function.comp_def]

@[simp] theorem identityMotiveWith_instL (view : VBlockStructureView)
    (family : NormalizedFamily) (levels : List VLevel)
    (params : List VExpr) (dummyType : VExpr) (ls : List VLevel) :
    (view.identityMotiveWith family levels params dummyType).instL ls =
      view.identityMotiveWith family (levels.map (VLevel.inst ls))
        (params.map (VExpr.instL ls)) (dummyType.instL ls) := by
  have hindices :
      (view.specializedIndices family levels params).length =
        (view.specializedIndices family (levels.map (VLevel.inst ls))
          (params.map (VExpr.instL ls))).length := by
    simp [specializedIndices]
  simp only [identityMotiveWith]
  rw [VExpr.instL_lamN, specializedIndices_instL, hindices]
  simp [VExpr.instL, VExpr.instL_appN, VExpr.instL_liftN,
    VExpr.bvarRevRange_map_instL, List.map_append, List.map_map,
    Function.comp_def]

@[simp] theorem projectionMotives_instL (view : VBlockStructureView)
    (levels : List VLevel) (params : List VExpr)
    (fieldSort : VLevel) (typeFn : VExpr) (ls : List VLevel) :
    (view.projectionMotives levels params fieldSort typeFn).map
        (VExpr.instL ls) =
      view.projectionMotives (levels.map (VLevel.inst ls))
        (params.map (VExpr.instL ls)) (fieldSort.inst ls)
        (typeFn.instL ls) := by
  simp only [projectionMotives, List.map_map]
  apply List.map_congr_left
  intro family _
  by_cases selected : family.view.ordinal = view.family.view.ordinal
  · simp [selected]
  · simp [selected]

@[simp] theorem projectionMotivesWith_instL (view : VBlockStructureView)
    (levels : List VLevel) (params : List VExpr)
    (typeFn dummyType : VExpr) (ls : List VLevel) :
    (view.projectionMotivesWith levels params typeFn dummyType).map
        (VExpr.instL ls) =
      view.projectionMotivesWith (levels.map (VLevel.inst ls))
        (params.map (VExpr.instL ls)) (typeFn.instL ls)
        (dummyType.instL ls) := by
  simp only [projectionMotivesWith, List.map_map]
  apply List.map_congr_left
  intro family _
  by_cases selected : family.view.ordinal = view.family.view.ordinal
  · simp [selected]
  · simp [selected]

@[simp] theorem generatedProjectionMinorType_instL
    (view : VBlockStructureView) (constructor : NormalizedBlockCtor)
    (fieldSort : VLevel) (levels : List VLevel)
    (params motives : List VExpr)
    (ls : List VLevel) :
    (view.generatedProjectionMinorType constructor fieldSort levels params
      motives).instL ls =
      view.generatedProjectionMinorType constructor (fieldSort.inst ls)
        (levels.map (VLevel.inst ls))
        (params.map (VExpr.instL ls))
        (motives.map (VExpr.instL ls)) := by
  unfold generatedProjectionMinorType
  rw [← VExpr.instRevAt_zero, VExpr.instL_instRevAt,
    VExpr.instRevAt_zero, VExpr.instL_instRevAt,
    VExpr.instL_instL, projectionLevels_instL]

/-- The outer telescope of a fully specialized mutual minor is exactly the
source-order constructor-field telescope. -/
theorem generatedProjectionMinorType_fields
    (view : VBlockStructureView) (constructor : NormalizedBlockCtor)
    (fieldSort : VLevel) (levels : List VLevel)
    (hlevels : levels.length = view.uvars)
    (params motives : List VExpr)
    (hmotives : motives.length = view.generation.familyCount) :
    VExpr.telN
        (view.specializedCtorFields constructor levels params).length
        (view.generatedProjectionMinorType constructor fieldSort levels params
          motives) =
      view.specializedCtorFields constructor levels params := by
  let rawFields := constructor.ctor.rawFields view.nparams
  let recFields := constructor.ctor.fieldsR view.uvars view.nparams
    view.generation.elimination
  let recLevels := view.projectionLevels fieldSort levels
  have hsource :=
    view.sourceLevels_projectionLevels fieldSort levels hlevels
  have hsource' :
      (VLevel.params' view.uvars view.generation.elimination.offset).map
          (VLevel.inst recLevels) = levels := by
    simpa [BlockGenerationChecked.sourceLevels, recLevels] using hsource
  have hrecFields :
      recFields.map (VExpr.instL recLevels) =
        rawFields.map (VExpr.instL levels) := by
    simp only [recFields, rawFields, NormalizedCtor.fieldsR,
      List.map_map, Function.comp_def, VExpr.instL_instL]
    rw [hsource']
  have hfieldBinders := VExpr.map_liftTelN_instRevAt_append
    (rawFields.map (VExpr.instL levels)) params motives 0
  rw [hmotives] at hfieldBinders
  rw [VExpr.instRevAt_map_instL_zipIdx] at hfieldBinders
  have hfieldBinders' :
      ((VExpr.liftTelN view.generation.familyCount
        (rawFields.map (VExpr.instL levels)) 0).zipIdx |>.map
          fun entry => entry.1.instRevAt (params ++ motives) entry.2) =
        view.specializedCtorFields constructor levels params := by
    simpa [specializedCtorFields, rawFields] using hfieldBinders
  have hcombine :
      (((view.generation.minorType constructor).instL recLevels).instRevAt
          params view.generation.familyCount).instRev motives =
        ((view.generation.minorType constructor).instL recLevels).instRev
          (params ++ motives) := by
    simpa [VExpr.instRevAt_zero, hmotives] using
      (VExpr.instRevAt_append
        ((view.generation.minorType constructor).instL recLevels)
        params motives 0).symm
  unfold generatedProjectionMinorType
  change VExpr.telN _
      ((((view.generation.minorType constructor).instL recLevels).instRevAt
        params view.generation.familyCount).instRev motives) = _
  rw [hcombine]
  simp only [BlockGenerationChecked.minorType, VExpr.instL_forallN,
    VExpr.instRev_forallN_projection, VExpr.liftTelN_instL]
  rw [hrecFields, hfieldBinders']
  exact VExpr.telN_forallN_length _ _

/-- Every fully specialized mutual minor retains the generated two-stage
field/IH Pi shape, independently of which family owns its constructor. -/
private theorem generatedProjectionMinorType_telescope_shape
    (view : VBlockStructureView) (constructor : NormalizedBlockCtor)
    (fieldSort : VLevel) (levels : List VLevel)
    (params motives : List VExpr)
    (hmotives : motives.length = view.generation.familyCount) :
    ∃ fieldBinders ihBinders body,
      fieldBinders.length =
        (view.specializedCtorFields constructor levels params).length ∧
      ihBinders.length = constructor.ctor.view.recursive.length ∧
      view.generatedProjectionMinorType constructor fieldSort levels params
          motives =
        VExpr.forallN fieldBinders (VExpr.forallN ihBinders body) := by
  let recLevels := view.projectionLevels fieldSort levels
  let rawFields := constructor.ctor.fieldsR view.uvars view.nparams
    view.generation.elimination
  let rawIHs := BlockGenerationChecked.blockIHsFromRecArgs
    view.generation.familyCount rawFields.length
      (constructor.ctor.recArgsR view.uvars
        view.generation.elimination) 0
  let fieldsL := (VExpr.liftTelN view.generation.familyCount rawFields 0).map
    (VExpr.instL recLevels)
  let ihsL := rawIHs.map (VExpr.instL recLevels)
  let fieldBinders := fieldsL.zipIdx.map fun entry =>
    entry.1.instRevAt (params ++ motives) entry.2
  let ihBinders := ihsL.zipIdx
      (VExpr.liftTelN view.generation.familyCount rawFields 0).length |>.map
    fun entry => entry.1.instRevAt (params ++ motives) entry.2
  have hcombine :
      (((view.generation.minorType constructor).instL recLevels).instRevAt
          params view.generation.familyCount).instRev motives =
        ((view.generation.minorType constructor).instL recLevels).instRev
          (params ++ motives) := by
    simpa [VExpr.instRevAt_zero, hmotives] using
      (VExpr.instRevAt_append
        ((view.generation.minorType constructor).instL recLevels)
        params motives 0).symm
  have hshape : ∃ body,
      ((view.generation.minorType constructor).instL recLevels).instRev
          (params ++ motives) =
        VExpr.forallN fieldBinders (VExpr.forallN ihBinders body) := by
    simp [fieldBinders, ihBinders, fieldsL, ihsL, rawFields, rawIHs,
      BlockGenerationChecked.minorType, VExpr.instL_forallN,
      VExpr.instRev_forallN_projection,
      VExpr.instRevAt_forallN_projection]
    refine ⟨_, rfl⟩
  have hfieldBindersLength : fieldBinders.length =
      (view.specializedCtorFields constructor levels params).length := by
    calc
      fieldBinders.length = fieldsL.length := by simp [fieldBinders]
      _ = rawFields.length := by
        dsimp only [fieldsL]
        rw [List.length_map, VExpr.liftTelN_length]
      _ = (constructor.ctor.rawFields view.nparams).length := by
        simp [rawFields, NormalizedCtor.fieldsR]
      _ = (view.specializedCtorFields constructor levels params).length := by
        simp [specializedCtorFields]
  have hihBindersLength : ihBinders.length =
      constructor.ctor.view.recursive.length := by
    calc
      ihBinders.length = ihsL.length := by simp [ihBinders]
      _ = rawIHs.length := by simp [ihsL]
      _ = (constructor.ctor.recArgsR view.uvars
          view.generation.elimination).length := by
        simp [rawIHs,
          BlockGenerationChecked.blockIHsFromRecArgs_length]
      _ = constructor.ctor.view.recursive.length := by
        simp [NormalizedCtor.recArgsR]
  obtain ⟨body, hshape⟩ := hshape
  exact ⟨fieldBinders, ihBinders, body, hfieldBindersLength,
    hihBindersLength, hcombine.trans hshape⟩

theorem generatedProjectionMinorResult_motive
    (view : VBlockStructureView) (constructor : NormalizedBlockCtor)
    (family : NormalizedFamily)
    (howner : family.view.ordinal = constructor.owner)
    (hresultLength : constructor.ctor.view.resultIndices.length =
      family.view.indices.length)
    (fieldSort : VLevel) (levels : List VLevel)
    (params motives : List VExpr) (motive : VExpr)
    (hmotives : motives.length = view.generation.familyCount)
    (hmotive : motives[family.view.ordinal]? = some motive) :
    (view.generatedProjectionMinorArguments constructor fieldSort levels
        params motives).length = family.view.indices.length + 1 ∧
      VExpr.dropN
        ((view.specializedCtorFields constructor levels params).length +
          constructor.ctor.view.recursive.length)
        (view.generatedProjectionMinorType constructor fieldSort levels params
          motives) =
      VExpr.appN
        (motive.liftN
          ((view.specializedCtorFields constructor levels params).length +
            constructor.ctor.view.recursive.length))
          (view.generatedProjectionMinorArguments constructor fieldSort levels
            params motives) := by
  let d := view.generation.familyCount
  let rawFields := constructor.ctor.fieldsR view.uvars view.nparams
    view.generation.elimination
  let m := rawFields.length
  let recArgs := constructor.ctor.recArgsR view.uvars
    view.generation.elimination
  let rawIHs := BlockGenerationChecked.blockIHsFromRecArgs d m recArgs 0
  let r := recArgs.length
  let recLevels := view.projectionLevels fieldSort levels
  let fieldsL := (VExpr.liftTelN d rawFields 0).map
    (VExpr.instL recLevels)
  let ihsL := rawIHs.map (VExpr.instL recLevels)
  let fieldBinders := fieldsL.zipIdx.map fun entry =>
    entry.1.instRevAt (params ++ motives) entry.2
  let ihBinders := ihsL.zipIdx fieldsL.length |>.map fun entry =>
    entry.1.instRevAt (params ++ motives) entry.2
  let rawArguments :=
      (constructor.ctor.resultIndicesR view.uvars
        view.generation.elimination |>.map fun expression =>
          (expression.liftN d m).liftN r) ++
        [VExpr.appN
          (.const constructor.ctor.raw.name view.generation.sourceLevels)
          (VExpr.bvarRevRange (r + m + d) view.nparams ++
            VExpr.bvarRevRange r m)]
  let rawBody :=
    VExpr.appN (.bvar (d - 1 - constructor.owner + m + r))
      rawArguments
  let body := (rawBody.instL recLevels).instRevAt
    (params ++ motives) (m + r)
  have hfieldLength :
      (view.specializedCtorFields constructor levels params).length = m := by
    simp [specializedCtorFields, m, rawFields, NormalizedCtor.fieldsR]
  have hrecursiveLength : constructor.ctor.view.recursive.length = r := by
    simp [r, recArgs, NormalizedCtor.recArgsR]
  have hmotivesIndex : family.view.ordinal < motives.length :=
    (List.getElem?_eq_some_iff.1 hmotive).1
  have hcombine :
      (((view.generation.minorType constructor).instL recLevels).instRevAt
          params d).instRev motives =
        ((view.generation.minorType constructor).instL recLevels).instRev
          (params ++ motives) := by
    simpa [VExpr.instRevAt_zero, hmotives, d] using
      (VExpr.instRevAt_append
        ((view.generation.minorType constructor).instL recLevels)
        params motives 0).symm
  have hshape :
      view.generatedProjectionMinorType constructor fieldSort levels params
          motives =
        VExpr.forallN fieldBinders (VExpr.forallN ihBinders body) := by
    unfold generatedProjectionMinorType
    change (((view.generation.minorType constructor).instL recLevels).instRevAt
      params d).instRev motives = _
    rw [hcombine]
    simp [fieldBinders, ihBinders, fieldsL, ihsL, rawFields, rawIHs,
      rawBody, rawArguments, body, r, recArgs, m, d,
      BlockGenerationChecked.minorType, VExpr.instL_forallN,
      VExpr.instRev_forallN_projection,
      VExpr.instRevAt_forallN_projection, VExpr.liftTelN_length,
      BlockGenerationChecked.blockIHsFromRecArgs_length]
  have hfieldBindersLength : fieldBinders.length = m := by
    simp [fieldBinders, fieldsL, rawFields, m, VExpr.liftTelN_length]
  have hihBindersLength : ihBinders.length = r := by
    simp [ihBinders, ihsL, rawIHs, r,
      BlockGenerationChecked.blockIHsFromRecArgs_length]
  rw [hshape, hfieldLength, hrecursiveLength,
    ← hfieldBindersLength, ← hihBindersLength,
    ← VExpr.forallN_append]
  rw [show fieldBinders.length + ihBinders.length =
      (fieldBinders ++ ihBinders).length by simp,
    VExpr.dropN_forallN_length]
  unfold body rawBody
  simp only [VExpr.instL_appN, VExpr.instRevAt_appN_projection]
  have hbindersLength : (fieldBinders ++ ihBinders).length = m + r := by
    simp [hfieldBindersLength, hihBindersLength]
  rw [hbindersLength]
  change
    ((rawArguments.map (VExpr.instL recLevels)).map
      (fun expression => expression.instRevAt
        (params ++ motives) (m + r))).length =
        family.view.indices.length + 1 ∧
      _ = VExpr.appN _
        ((rawArguments.map (VExpr.instL recLevels)).map
          (fun expression => expression.instRevAt
            (params ++ motives) (m + r)))
  constructor
  · simp [rawArguments, NormalizedCtor.resultIndicesR, hresultLength]
  congr 1
  simp only [VExpr.instL]
  have hmotiveAppend :
      (params ++ motives)[params.length + family.view.ordinal]? =
        some motive := by
    rw [List.getElem?_append_right (by omega)]
    simpa using hmotive
  rw [show d - 1 - constructor.owner + m + r =
      (m + r) + ((params ++ motives).length - 1 -
        (params.length + family.view.ordinal)) by
        simp only [List.length_append]
        rw [hmotives, howner]
        omega]
  exact VExpr.instRevAt_bvar_rev_getElem?
    (params ++ motives) hmotiveAppend (m + r)

/-- The complete generated binder prefix of any specialized mutual minor
has the expected field-plus-IH arity. -/
theorem generatedProjectionMinorBinders_length
    (view : VBlockStructureView) (constructor : NormalizedBlockCtor)
    (fieldSort : VLevel) (levels : List VLevel)
    (params motives : List VExpr)
    (hmotives : motives.length = view.generation.familyCount) :
    (VExpr.telN
      ((view.specializedCtorFields constructor levels params).length +
        constructor.ctor.view.recursive.length)
      (view.generatedProjectionMinorType constructor fieldSort levels params
        motives)
    ).length =
      (view.specializedCtorFields constructor levels params).length +
        constructor.ctor.view.recursive.length := by
  obtain ⟨fieldBinders, ihBinders, body, hfields, hihs, hshape⟩ :=
    view.generatedProjectionMinorType_telescope_shape constructor fieldSort
      levels params motives hmotives
  rw [hshape, ← VExpr.forallN_append]
  rw [show (view.specializedCtorFields constructor levels params).length +
      constructor.ctor.view.recursive.length =
        (fieldBinders ++ ihBinders).length by simp [hfields, hihs]]
  rw [VExpr.telN_forallN_length]

/-- The specialized selected minor retains exactly one generated IH binder
for every recursive argument recorded by the selected constructor view. -/
@[simp] theorem projectionIHTypes_length
    (view : VBlockStructureView) (fieldSort : VLevel)
    (levels : List VLevel)
    (_hlevels : levels.length = view.uvars) (params motives : List VExpr)
    (hmotives : motives.length = view.generation.familyCount) :
    (view.projectionIHTypes fieldSort levels params motives).length =
      view.constructor.view.recursive.length := by
  let recLevels := view.projectionLevels fieldSort levels
  have hcombine :
      (((view.generation.minorType view.blockConstructor).instL
        recLevels).instRevAt params view.generation.familyCount).instRev
          motives =
        ((view.generation.minorType view.blockConstructor).instL
          recLevels).instRev (params ++ motives) := by
    simpa [VExpr.instRevAt_zero, hmotives] using
      (VExpr.instRevAt_append
        ((view.generation.minorType view.blockConstructor).instL recLevels)
        params motives 0).symm
  let rawFields := view.blockConstructor.ctor.fieldsR view.uvars view.nparams
    view.generation.elimination
  let rawIHs := BlockGenerationChecked.blockIHsFromRecArgs
    view.generation.familyCount rawFields.length
      (view.blockConstructor.ctor.recArgsR view.uvars
        view.generation.elimination) 0
  let fieldsL := (VExpr.liftTelN view.generation.familyCount rawFields 0).map
    (VExpr.instL recLevels)
  let ihsL := rawIHs.map (VExpr.instL recLevels)
  let fieldBinders := fieldsL.zipIdx.map fun entry =>
    entry.1.instRevAt (params ++ motives) entry.2
  let ihBinders := ihsL.zipIdx
      (VExpr.liftTelN view.generation.familyCount rawFields 0).length |>.map
    fun entry => entry.1.instRevAt (params ++ motives) entry.2
  have hshape : ∃ body,
      ((view.generation.minorType view.blockConstructor).instL
          recLevels).instRev (params ++ motives) =
        VExpr.forallN fieldBinders (VExpr.forallN ihBinders body) := by
    simp [fieldBinders, ihBinders, fieldsL, ihsL, rawFields, rawIHs,
      blockConstructor, BlockGenerationChecked.minorType,
      VExpr.instL_forallN,
      VExpr.instRev_forallN_projection,
      VExpr.instRevAt_forallN_projection]
    refine ⟨_, rfl⟩
  have hfieldBindersLength : fieldBinders.length =
      (view.specializedFields levels params).length := by
    calc
      fieldBinders.length = fieldsL.length := by simp [fieldBinders]
      _ = rawFields.length := by
        dsimp only [fieldsL]
        rw [List.length_map, VExpr.liftTelN_length]
      _ = (view.constructor.rawFields view.nparams).length := by
        simp [rawFields, NormalizedCtor.fieldsR, blockConstructor]
      _ = (view.specializedFields levels params).length := by
        simp [specializedFields, fields]
  have hihBindersLength : ihBinders.length =
      view.constructor.view.recursive.length := by
    calc
      ihBinders.length = ihsL.length := by simp [ihBinders]
      _ = rawIHs.length := by simp [ihsL]
      _ = (view.blockConstructor.ctor.recArgsR view.uvars
          view.generation.elimination).length := by
        simp [rawIHs,
          BlockGenerationChecked.blockIHsFromRecArgs_length]
      _ = view.constructor.view.recursive.length := by
        simp [NormalizedCtor.recArgsR, blockConstructor]
  obtain ⟨body, hshape⟩ := hshape
  unfold projectionIHTypes generatedProjectionMinorType
  change (VExpr.telN view.constructor.view.recursive.length
    (VExpr.dropN (view.specializedFields levels params).length
      ((((view.generation.minorType view.blockConstructor).instL
        recLevels).instRevAt params view.generation.familyCount).instRev
          motives))).length = _
  rw [hcombine, hshape, ← hfieldBindersLength,
    VExpr.dropN_forallN_length, ← hihBindersLength,
    VExpr.telN_forallN_length, hihBindersLength]

/-- The selected mutual minor decomposes into its specialized fields, exact
generated IH telescope, and terminal selected-motive application. -/
theorem projectionMinorType_decompose
    (view : VBlockStructureView) (fieldSort : VLevel)
    (levels : List VLevel)
    (hlevels : levels.length = view.uvars) (params motives : List VExpr)
    (hmotives : motives.length = view.generation.familyCount) :
    view.generatedProjectionMinorType view.blockConstructor fieldSort levels
        params motives =
      VExpr.forallN (view.specializedFields levels params)
        (VExpr.forallN
          (view.projectionIHTypes fieldSort levels params motives)
          (VExpr.dropN view.constructor.view.recursive.length
            (VExpr.dropN (view.specializedFields levels params).length
              (view.generatedProjectionMinorType view.blockConstructor
                fieldSort levels params motives)))) := by
  let exactMinor := view.generatedProjectionMinorType view.blockConstructor
    fieldSort levels params motives
  let fields := view.specializedFields levels params
  let cursor := VExpr.dropN fields.length exactMinor
  let ihs := view.projectionIHTypes fieldSort levels params motives
  have hfields : VExpr.telN fields.length exactMinor = fields := by
    simpa [fields, exactMinor, specializedCtorFields, specializedFields,
      VBlockStructureView.fields, blockConstructor] using
      view.generatedProjectionMinorType_fields view.blockConstructor fieldSort
        levels hlevels params motives hmotives
  have hihsLength : ihs.length =
      view.constructor.view.recursive.length := by
    simpa [ihs] using
      view.projectionIHTypes_length fieldSort levels hlevels params motives
        hmotives
  have hihs :
      VExpr.telN view.constructor.view.recursive.length cursor = ihs := by
    rfl
  calc
    exactMinor = VExpr.forallN (VExpr.telN fields.length exactMinor)
        cursor := (VExpr.forallN_telN_dropN fields.length exactMinor).symm
    _ = VExpr.forallN fields cursor := by rw [hfields]
    _ = VExpr.forallN fields
        (VExpr.forallN (VExpr.telN ihs.length cursor)
          (VExpr.dropN ihs.length cursor)) := by
      rw [VExpr.forallN_telN_dropN]
    _ = VExpr.forallN fields
        (VExpr.forallN ihs
          (VExpr.dropN view.constructor.view.recursive.length cursor)) := by
      rw [hihsLength, hihs]
    _ = _ := rfl

@[simp] theorem projectionIHTypes_instL (view : VBlockStructureView)
    (fieldSort : VLevel) (levels : List VLevel)
    (params motives : List VExpr)
    (ls : List VLevel) :
    (view.projectionIHTypes fieldSort levels params motives).map
        (VExpr.instL ls) =
      view.projectionIHTypes (fieldSort.inst ls)
        (levels.map (VLevel.inst ls))
        (params.map (VExpr.instL ls))
        (motives.map (VExpr.instL ls)) := by
  unfold projectionIHTypes
  rw [← VExpr.telN_instL, ← VExpr.dropN_instL,
    generatedProjectionMinorType_instL]
  have hfields := view.specializedFields_instL levels params ls
  have hfieldsLength := congrArg List.length hfields
  simp only [List.length_map] at hfieldsLength
  rw [hfieldsLength]

@[simp] theorem identityMinor_instL (view : VBlockStructureView)
    (constructor : NormalizedBlockCtor)
    (fieldSort : VLevel) (levels : List VLevel)
    (params motives : List VExpr)
    (ls : List VLevel) :
    (view.identityMinor constructor fieldSort levels params motives).instL
        ls =
      view.identityMinor constructor (fieldSort.inst ls)
        (levels.map (VLevel.inst ls))
        (params.map (VExpr.instL ls))
        (motives.map (VExpr.instL ls)) := by
  have hfields :
      (view.specializedCtorFields constructor levels params).length =
        (view.specializedCtorFields constructor
          (levels.map (VLevel.inst ls))
          (params.map (VExpr.instL ls))).length := by
    simp [specializedCtorFields]
  simp only [identityMinor]
  rw [VExpr.instL_lamN, ← VExpr.telN_instL,
    generatedProjectionMinorType_instL, hfields]
  simp [VExpr.instL, VExpr.instL_appN, VExpr.instL_liftN,
    VExpr.bvarRevRange_map_instL,
    List.map_append, List.map_map, Function.comp_def]

@[simp] theorem identityMinorWith_instL (view : VBlockStructureView)
    (constructor : NormalizedBlockCtor)
    (fieldSort : VLevel) (levels : List VLevel)
    (params motives : List VExpr) (dummyValue : VExpr)
    (ls : List VLevel) :
    (view.identityMinorWith constructor fieldSort levels params motives
        dummyValue).instL ls =
      view.identityMinorWith constructor (fieldSort.inst ls)
        (levels.map (VLevel.inst ls))
        (params.map (VExpr.instL ls))
        (motives.map (VExpr.instL ls)) (dummyValue.instL ls) := by
  let fields := view.specializedCtorFields constructor levels params
  let fields' := view.specializedCtorFields constructor
    (levels.map (VLevel.inst ls)) (params.map (VExpr.instL ls))
  let exactMinor := view.generatedProjectionMinorType constructor fieldSort
    levels params motives
  let exactMinor' := view.generatedProjectionMinorType constructor
    (fieldSort.inst ls) (levels.map (VLevel.inst ls))
    (params.map (VExpr.instL ls)) (motives.map (VExpr.instL ls))
  let binders := VExpr.telN
    (fields.length + constructor.ctor.view.recursive.length) exactMinor
  let binders' := VExpr.telN
    (fields'.length + constructor.ctor.view.recursive.length) exactMinor'
  have hfields : fields.length = fields'.length := by
    simp [fields, fields', specializedCtorFields]
  have hbinders : binders.map (VExpr.instL ls) = binders' := by
    simp [binders, binders', exactMinor, exactMinor', hfields,
      ← VExpr.telN_instL]
  have hbindersLength : binders.length = binders'.length := by
    have := congrArg List.length hbinders
    simpa using this
  unfold identityMinorWith
  change (VExpr.lamN binders
      (dummyValue.liftN binders.length)).instL ls =
    VExpr.lamN binders'
      ((dummyValue.instL ls).liftN binders'.length)
  rw [VExpr.instL_lamN, hbinders, VExpr.instL_liftN, hbindersLength]

@[simp] theorem projectionMinor_instL (view : VBlockStructureView)
    (constructor : NormalizedBlockCtor)
    (fieldSort : VLevel) (levels : List VLevel)
    (params allFields motives : List VExpr)
    (fieldIndex : Nat) (ls : List VLevel) :
    (view.projectionMinor constructor fieldSort levels params allFields motives
        fieldIndex).instL ls =
      view.projectionMinor constructor (fieldSort.inst ls)
        (levels.map (VLevel.inst ls))
        (params.map (VExpr.instL ls))
        (allFields.map (VExpr.instL ls))
        (motives.map (VExpr.instL ls)) fieldIndex := by
  unfold projectionMinor
  split
  · simp [VExpr.selectFieldMinor_instL]
  · simp

@[simp] theorem projectionMinorWith_instL (view : VBlockStructureView)
    (constructor : NormalizedBlockCtor)
    (fieldSort : VLevel) (levels : List VLevel)
    (params allFields motives : List VExpr) (fieldIndex : Nat)
    (dummyValue : VExpr) (ls : List VLevel) :
    (view.projectionMinorWith constructor fieldSort levels params allFields
        motives fieldIndex dummyValue).instL ls =
      view.projectionMinorWith constructor (fieldSort.inst ls)
        (levels.map (VLevel.inst ls))
        (params.map (VExpr.instL ls))
        (allFields.map (VExpr.instL ls))
        (motives.map (VExpr.instL ls)) fieldIndex
        (dummyValue.instL ls) := by
  unfold projectionMinorWith
  split
  · simp [VExpr.selectFieldMinor_instL]
  · simp

@[simp] theorem majorDummyType_instL (typeFn major : VExpr)
    (ls : List VLevel) :
    (majorDummyType typeFn major).instL ls =
      majorDummyType (typeFn.instL ls) (major.instL ls) := by
  simp [majorDummyType, VExpr.instL]

@[simp] theorem majorDummyValue_instL (typeFn major : VExpr)
    (ls : List VLevel) :
    (majorDummyValue typeFn major).instL ls =
      majorDummyValue (typeFn.instL ls) (major.instL ls) := by
  simp [majorDummyValue, VExpr.instL]

@[simp] theorem operationalProjector_instL (view : VBlockStructureView)
    (levels : List VLevel) (params allFields : List VExpr)
    (structType : VExpr) (fieldSort : VLevel) (fieldIndex : Nat)
    (typeFn : VExpr) (ls : List VLevel) :
    (view.operationalProjector levels params allFields structType fieldSort
        fieldIndex typeFn).instL ls =
      view.operationalProjector (levels.map (VLevel.inst ls))
        (params.map (VExpr.instL ls))
        (allFields.map (VExpr.instL ls)) (structType.instL ls)
        (fieldSort.inst ls) fieldIndex (typeFn.instL ls) := by
  unfold operationalProjector
  simp [VExpr.instL, VExpr.instL_appN, VExpr.instL_liftN,
    VExpr.liftTelN_instL, List.map_append, List.map_map,
    Function.comp_def]

private theorem operationalProjectionCode_instL
    (view : VBlockStructureView)
    (levels : List VLevel) (params allFields : List VExpr)
    (structType field : VExpr) (fieldSort : VLevel) (fieldIndex : Nat)
    (previous : List VStructureView.ProjectionCode) (ls : List VLevel) :
    (operationalProjectionCode view levels params allFields structType field
      fieldSort fieldIndex previous).instL ls =
    operationalProjectionCode view (levels.map (VLevel.inst ls))
      (params.map (VExpr.instL ls)) (allFields.map (VExpr.instL ls))
      (structType.instL ls) (field.instL ls) (fieldSort.inst ls) fieldIndex
      (previous.map fun code => code.instL ls) := by
  let previousAtMajor := previous.map fun code =>
    VExpr.app code.projector.lift (.bvar 0)
  let previous' := previous.map fun code => code.instL ls
  let previousAtMajor' := previous'.map fun code =>
    VExpr.app code.projector.lift (.bvar 0)
  have hprevious : previousAtMajor.map (VExpr.instL ls) =
      previousAtMajor' := by
    simp [previousAtMajor, previousAtMajor', previous',
      VStructureView.ProjectionCode.instL, VExpr.instL,
      VExpr.instL_liftN, List.map_map, Function.comp_def]
  let motiveBody :=
    (field.liftN 1 fieldIndex).instRevAt previousAtMajor 0
  let motiveBody' :=
    ((field.instL ls).liftN 1 fieldIndex).instRevAt previousAtMajor' 0
  have hmotiveBody : motiveBody.instL ls = motiveBody' := by
    simp only [motiveBody, motiveBody', VExpr.instL_instRevAt,
      VExpr.instL_liftN]
    rw [hprevious]
  let typeFn := VExpr.lam structType motiveBody
  let typeFn' := VExpr.lam (structType.instL ls) motiveBody'
  have htypeFn : typeFn.instL ls = typeFn' := by
    simp [typeFn, typeFn', VExpr.instL, hmotiveBody]
  have hprojector := operationalProjector_instL view levels params allFields
    structType fieldSort fieldIndex typeFn ls
  rw [htypeFn] at hprojector
  unfold operationalProjectionCode VStructureView.ProjectionCode.instL
  dsimp only
  apply VStructureView.ProjectionCode.ext
  · rfl
  · exact htypeFn
  · exact htypeFn
  · exact hprojector

private theorem projectionCode_instL (view : VBlockStructureView)
    (levels : List VLevel) (params allFields : List VExpr)
    (structType field : VExpr) (fieldSort : VLevel) (fieldIndex : Nat)
    (previous : List VStructureView.ProjectionCode) (ls : List VLevel) :
    (projectionCode view levels params allFields structType field
      fieldSort fieldIndex previous).instL ls =
    projectionCode view (levels.map (VLevel.inst ls))
      (params.map (VExpr.instL ls)) (allFields.map (VExpr.instL ls))
      (structType.instL ls) (field.instL ls) (fieldSort.inst ls) fieldIndex
      (previous.map fun code => code.instL ls) := by
  let previousAtMajor := previous.map fun code =>
    VExpr.app code.projector.lift (.bvar 0)
  let previous' := previous.map fun code => code.instL ls
  let previousAtMajor' := previous'.map fun code =>
    VExpr.app code.projector.lift (.bvar 0)
  have hprevious : previousAtMajor.map (VExpr.instL ls) =
      previousAtMajor' := by
    simp [previousAtMajor, previousAtMajor', previous',
      VStructureView.ProjectionCode.instL, VExpr.instL,
      VExpr.instL_liftN, List.map_map, Function.comp_def]
  let motiveBody :=
    (field.liftN 1 fieldIndex).instRevAt previousAtMajor 0
  let motiveBody' :=
    ((field.instL ls).liftN 1 fieldIndex).instRevAt previousAtMajor' 0
  have hmotiveBody : motiveBody.instL ls = motiveBody' := by
    simp only [motiveBody, motiveBody', VExpr.instL_instRevAt,
      VExpr.instL_liftN]
    rw [hprevious]
  let typeFn := VExpr.lam structType motiveBody
  let typeFn' := VExpr.lam (structType.instL ls) motiveBody'
  have htypeFn : typeFn.instL ls = typeFn' := by
    simp [typeFn, typeFn', VExpr.instL, hmotiveBody]
  let motives := view.projectionMotives levels params fieldSort typeFn
  let motives' := view.projectionMotives
    (levels.map (VLevel.inst ls)) (params.map (VExpr.instL ls))
    (fieldSort.inst ls) typeFn'
  have hmotives : motives.map (VExpr.instL ls) = motives' := by
    simpa only [motives, motives', htypeFn] using
      view.projectionMotives_instL levels params fieldSort typeFn ls
  let minors := view.generation.flatCtors.map fun constructor =>
    view.projectionMinor constructor fieldSort levels params allFields motives
      fieldIndex
  let minors' := view.generation.flatCtors.map fun constructor =>
    view.projectionMinor constructor (fieldSort.inst ls)
      (levels.map (VLevel.inst ls))
      (params.map (VExpr.instL ls)) (allFields.map (VExpr.instL ls))
      motives' fieldIndex
  have hminors : minors.map (VExpr.instL ls) = minors' := by
    simp only [minors, minors', List.map_map]
    apply List.map_congr_left
    intro constructor _
    change VExpr.instL ls
        (view.projectionMinor constructor fieldSort levels params allFields
          motives
          fieldIndex) = _
    rw [view.projectionMinor_instL constructor fieldSort levels params
      allFields motives fieldIndex ls, hmotives]
  have hmotivesLift :
      (motives.map (VExpr.liftN 1)).map (VExpr.instL ls) =
        motives'.map (VExpr.liftN 1) := by
    simpa only [List.map_map, Function.comp_def, VExpr.instL_liftN] using
      congrArg (List.map (VExpr.liftN 1)) hmotives
  have hminorsLift :
      (minors.map (VExpr.liftN 1)).map (VExpr.instL ls) =
        minors'.map (VExpr.liftN 1) := by
    simpa only [List.map_map, Function.comp_def, VExpr.instL_liftN] using
      congrArg (List.map (VExpr.liftN 1)) hminors
  have hparamsLift :
      (params.map (VExpr.liftN 1)).map (VExpr.instL ls) =
        (params.map (VExpr.instL ls)).map (VExpr.liftN 1) := by
    simp [List.map_map, Function.comp_def, VExpr.instL_liftN]
  unfold projectionCode VStructureView.ProjectionCode.instL
  dsimp only
  apply VStructureView.ProjectionCode.ext
  all_goals dsimp only
  · exact htypeFn
  · change VExpr.instL ls
        (view.projectionMinor view.blockConstructor fieldSort levels params
          allFields motives fieldIndex) =
      view.projectionMinor view.blockConstructor
        (fieldSort.inst ls) (levels.map (VLevel.inst ls))
        (params.map (VExpr.instL ls))
        (allFields.map (VExpr.instL ls)) motives' fieldIndex
    exact (view.projectionMinor_instL view.blockConstructor fieldSort levels
      params allFields motives fieldIndex ls).trans (by rw [hmotives])
  · change VExpr.instL ls
        (.lam structType <| VExpr.appN
          (.const view.recursorName
            (view.projectionLevels fieldSort levels))
          (params.map (VExpr.liftN 1) ++ motives.map (VExpr.liftN 1) ++
            minors.map (VExpr.liftN 1) ++ [.bvar 0])) =
      .lam (structType.instL ls) (VExpr.appN
        (.const view.recursorName
          (view.projectionLevels (fieldSort.inst ls)
            (levels.map (VLevel.inst ls))))
        ((params.map (VExpr.instL ls)).map (VExpr.liftN 1) ++
          motives'.map (VExpr.liftN 1) ++
          minors'.map (VExpr.liftN 1) ++ [.bvar 0]))
    simp only [VExpr.instL, VExpr.instL_appN, List.map_append,
      List.map_singleton, projectionLevels_instL, hparamsLift,
      hmotivesLift, hminorsLift]

private theorem projectionCodes.go_instL (view : VBlockStructureView)
    (levels : List VLevel) (params allFields : List VExpr)
    (structType : VExpr) (fields : List VExpr)
    (fieldSorts : List VLevel) (fieldIndex : Nat)
    (previous : List VStructureView.ProjectionCode) (ls : List VLevel) :
    (projectionCodes.go view levels params allFields structType
        fields fieldSorts fieldIndex previous).map
      (fun code => code.instL ls) =
    projectionCodes.go view (levels.map (VLevel.inst ls))
      (params.map (VExpr.instL ls)) (allFields.map (VExpr.instL ls))
      (structType.instL ls) (fields.map (VExpr.instL ls))
      (fieldSorts.map (VLevel.inst ls)) fieldIndex
      (previous.map fun code => code.instL ls) := by
  induction fields generalizing fieldSorts fieldIndex previous with
  | nil => simp [projectionCodes.go]
  | cons field fields ih =>
      cases fieldSorts with
      | nil => simp [projectionCodes.go]
      | cons fieldSort fieldSorts =>
          simp only [projectionCodes.go, List.map_cons,
            projectionCode_instL]
          congr 1
          simpa only [List.map_append, List.map_singleton,
            projectionCode_instL] using
            ih fieldSorts (fieldIndex + 1)
              (previous ++ [projectionCode view levels params allFields
                structType field fieldSort fieldIndex previous])

@[simp] theorem projectionCodes_instL (view : VBlockStructureView)
    (levels : List VLevel) (params : List VExpr) (ls : List VLevel) :
    (view.projectionCodes levels params).map
        (fun code => code.instL ls) =
      view.projectionCodes (levels.map (VLevel.inst ls))
        (params.map (VExpr.instL ls)) := by
  simp [projectionCodes, projectionCodes.go_instL,
    VLevel.inst_inst, List.map_map, Function.comp_def]

private theorem operationalProjectionCodes.go_instL
    (view : VBlockStructureView)
    (levels : List VLevel) (params allFields : List VExpr)
    (structType : VExpr) (fields : List VExpr)
    (fieldSorts : List VLevel) (fieldIndex : Nat)
    (previous : List VStructureView.ProjectionCode) (ls : List VLevel) :
    (operationalProjectionCodes.go view levels params allFields structType
        fields fieldSorts fieldIndex previous).map
      (fun code => code.instL ls) =
    operationalProjectionCodes.go view (levels.map (VLevel.inst ls))
      (params.map (VExpr.instL ls)) (allFields.map (VExpr.instL ls))
      (structType.instL ls) (fields.map (VExpr.instL ls))
      (fieldSorts.map (VLevel.inst ls)) fieldIndex
      (previous.map fun code => code.instL ls) := by
  induction fields generalizing fieldSorts fieldIndex previous with
  | nil => simp [operationalProjectionCodes.go]
  | cons field fields ih =>
      cases fieldSorts with
      | nil => simp [operationalProjectionCodes.go]
      | cons fieldSort fieldSorts =>
          simp only [operationalProjectionCodes.go, List.map_cons,
            operationalProjectionCode_instL]
          congr 1
          simpa only [List.map_append, List.map_singleton,
            operationalProjectionCode_instL] using
            ih fieldSorts (fieldIndex + 1)
              (previous ++ [operationalProjectionCode view levels params
                allFields structType field fieldSort fieldIndex previous])

@[simp] theorem operationalProjectionCodes_instL
    (view : VBlockStructureView)
    (levels : List VLevel) (params : List VExpr) (ls : List VLevel) :
    (view.operationalProjectionCodes levels params).map
        (fun code => code.instL ls) =
      view.operationalProjectionCodes (levels.map (VLevel.inst ls))
        (params.map (VExpr.instL ls)) := by
  simp [operationalProjectionCodes, operationalProjectionCodes.go_instL,
    VLevel.inst_inst, List.map_map, Function.comp_def]

private theorem projectionCodes.go_length (view : VBlockStructureView)
    (levels : List VLevel) (params allFields : List VExpr)
    (structType : VExpr) :
    ∀ (fields : List VExpr) (fieldSorts : List VLevel)
      (fieldIndex : Nat) (previous : List VStructureView.ProjectionCode),
      fields.length = fieldSorts.length →
      (projectionCodes.go view levels params allFields structType
        fields fieldSorts fieldIndex previous).length = fields.length
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h
  | _ :: fields, _ :: fieldSorts, fieldIndex, previous, h => by
      simp only [List.length_cons] at h ⊢
      simp only [projectionCodes.go, List.length_cons]
      exact congrArg Nat.succ <|
        projectionCodes.go_length view levels params allFields structType
          fields fieldSorts (fieldIndex + 1) (_ ++ [_]) (Nat.succ.inj h)

@[simp] theorem projectionCodes_length (view : VBlockStructureView)
    (levels : List VLevel) (params : List VExpr) :
    (view.projectionCodes levels params).length =
      (view.specializedFields levels params).length := by
  apply projectionCodes.go_length
  simp [specializedFields, fields, view.fieldSorts_length]

@[simp] theorem projectionArgs_length (view : VBlockStructureView)
    (levels : List VLevel) (params : List VExpr) (count : Nat)
    (major : VExpr)
    (hcount : count ≤ (view.projectionCodes levels params).length) :
    (view.projectionArgs levels params count major).length = count := by
  simp only [projectionArgs, List.length_map, List.length_take]
  exact Nat.min_eq_left hcount

theorem projectionArgs_succ (view : VBlockStructureView)
    (levels : List VLevel) (params : List VExpr) (count : Nat)
    (major : VExpr) {code : VStructureView.ProjectionCode}
    (hcode : (view.projectionCodes levels params)[count]? = some code) :
    view.projectionArgs levels params (count + 1) major =
      view.projectionArgs levels params count major ++
        [.app code.projector major] := by
  simp only [projectionArgs, List.take_add_one, hcode, Option.toList_some,
    List.map_append, List.map_singleton]

@[simp] theorem operationalProjectionArgs_length
    (view : VBlockStructureView) (levels : List VLevel)
    (params : List VExpr) (count : Nat) (major : VExpr)
    (hcount : count ≤
      (view.operationalProjectionCodes levels params).length) :
    (view.operationalProjectionArgs levels params count major).length =
      count := by
  simp only [operationalProjectionArgs, List.length_map, List.length_take]
  exact Nat.min_eq_left hcount

theorem operationalProjectionArgs_succ (view : VBlockStructureView)
    (levels : List VLevel) (params : List VExpr) (count : Nat)
    (major : VExpr) {code : VStructureView.ProjectionCode}
    (hcode : (view.operationalProjectionCodes levels params)[count]? =
      some code) :
    view.operationalProjectionArgs levels params (count + 1) major =
      view.operationalProjectionArgs levels params count major ++
        [.app code.projector major] := by
  simp only [operationalProjectionArgs, List.take_add_one, hcode,
    Option.toList_some, List.map_append, List.map_singleton]

private theorem projectionCodes.go_get?_typeFn
    (view : VBlockStructureView)
    (levels : List VLevel) (params allFields : List VExpr)
    (structType : VExpr) :
    ∀ {fields : List VExpr} {fieldSorts : List VLevel}
      {fieldIndex : Nat} {previous : List VStructureView.ProjectionCode}
      {offset : Nat} {code : VStructureView.ProjectionCode},
      (projectionCodes.go view levels params allFields structType
        fields fieldSorts fieldIndex previous)[offset]? = some code →
      ∃ field,
        fields[offset]? = some field ∧
        code.typeFn = .lam structType
          ((field.liftN 1 (fieldIndex + offset)).instRevAt
            ((previous ++
              (projectionCodes.go view levels params allFields structType
                fields fieldSorts fieldIndex previous).take offset).map
              fun prior => .app prior.projector.lift (.bvar 0)) 0) := by
  intro fields
  induction fields with
  | nil =>
      intro fieldSorts fieldIndex previous offset code h
      cases fieldSorts <;> simp [projectionCodes.go] at h
  | cons field fields ih =>
      intro fieldSorts fieldIndex previous offset code h
      cases fieldSorts with
      | nil => simp [projectionCodes.go] at h
      | cons fieldSort fieldSorts =>
          let head := projectionCode view levels params allFields structType
            field fieldSort fieldIndex previous
          cases offset with
          | zero =>
              change some head = some code at h
              injection h with hcode
              subst code
              refine ⟨field, rfl, ?_⟩
              simp [head, projectionCode]
          | succ offset =>
              simp only [projectionCodes.go, List.getElem?_cons_succ] at h
              obtain ⟨tailField, htailField, htypeFn⟩ :=
                ih (fieldSorts := fieldSorts)
                  (fieldIndex := fieldIndex + 1)
                  (previous := previous ++ [head]) h
              refine ⟨tailField, by simpa using htailField, ?_⟩
              have hpref :
                  previous ++
                    (projectionCodes.go view levels params allFields structType
                      (field :: fields) (fieldSort :: fieldSorts)
                      fieldIndex previous).take (offset + 1) =
                    (previous ++ [head]) ++
                      (projectionCodes.go view levels params allFields
                        structType fields fieldSorts (fieldIndex + 1)
                        (previous ++ [head])).take offset := by
                simp [head, projectionCodes.go, List.append_assoc]
              rw [hpref]
              simpa only [Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using htypeFn

/-- The generated type function at one block-backed projection index is the
corresponding specialized field with all earlier projectors substituted at
the major premise. -/
theorem projectionCodes_get?_typeFn (view : VBlockStructureView)
    (levels : List VLevel) (params : List VExpr) {idx : Nat}
    {code : VStructureView.ProjectionCode}
    (hcode : (view.projectionCodes levels params)[idx]? = some code) :
    ∃ field,
      (view.specializedFields levels params)[idx]? = some field ∧
      code.typeFn = .lam (view.structureType levels params)
        ((field.liftN 1 idx).instRevAt
          ((view.projectionCodes levels params).take idx |>.map fun prior =>
            .app prior.projector.lift (.bvar 0)) 0) := by
  unfold projectionCodes at hcode ⊢
  simpa using projectionCodes.go_get?_typeFn view levels params
    (view.specializedFields levels params)
    (view.structureType levels params) hcode

private theorem projectionCodes.go_get?_program_shape
    (view : VBlockStructureView) (levels : List VLevel)
    (params allFields : List VExpr) (structType : VExpr) :
    ∀ {fields : List VExpr} {fieldSorts : List VLevel}
      {fieldIndex : Nat} {previous : List VStructureView.ProjectionCode}
      {offset : Nat} {code : VStructureView.ProjectionCode},
      (projectionCodes.go view levels params allFields structType
        fields fieldSorts fieldIndex previous)[offset]? = some code →
      ∃ fieldSort,
        fieldSorts[offset]? = some fieldSort ∧
        code.fieldSort = fieldSort ∧
        let motives := view.projectionMotives levels params fieldSort code.typeFn
        let minors := view.generation.flatCtors.map fun constructor =>
          view.projectionMinor constructor fieldSort levels params allFields motives
            (fieldIndex + offset)
        code.minor = view.projectionMinor view.blockConstructor fieldSort levels
            params allFields motives (fieldIndex + offset) ∧
          code.projector = .lam structType
            (VExpr.appN
              (.const view.recursorName
                (view.projectionLevels fieldSort levels))
              (params.map (VExpr.liftN 1) ++
                motives.map (VExpr.liftN 1) ++
                minors.map (VExpr.liftN 1) ++ [.bvar 0])) := by
  intro fields
  induction fields with
  | nil =>
      intro fieldSorts fieldIndex previous offset code h
      cases fieldSorts <;> simp [projectionCodes.go] at h
  | cons field fields ih =>
      intro fieldSorts fieldIndex previous offset code h
      cases fieldSorts with
      | nil => simp [projectionCodes.go] at h
      | cons fieldSort fieldSorts =>
          let head := projectionCode view levels params allFields structType
            field fieldSort fieldIndex previous
          cases offset with
          | zero =>
              change some head = some code at h
              injection h with hcode
              subst code
              simp [head, projectionCode]
          | succ offset =>
              simp only [projectionCodes.go, List.getElem?_cons_succ] at h
              have hout := ih (fieldSorts := fieldSorts)
                (fieldIndex := fieldIndex + 1)
                (previous := previous ++ [head]) h
              simpa only [List.getElem?_cons_succ, Nat.add_assoc,
                Nat.add_comm, Nat.add_left_comm] using hout

/-- A selected block-backed projection code retains its exact selected minor
and the full actual mutual recursor program. -/
theorem projectionCodes_get?_program_shape (view : VBlockStructureView)
    (levels : List VLevel) (params : List VExpr) {idx : Nat}
    {code : VStructureView.ProjectionCode}
    (hcode : (view.projectionCodes levels params)[idx]? = some code) :
    ∃ fieldSort,
      (view.fieldSorts.map (VLevel.inst levels))[idx]? = some fieldSort ∧
      code.fieldSort = fieldSort ∧
      let motives := view.projectionMotives levels params fieldSort code.typeFn
      let minors := view.generation.flatCtors.map fun constructor =>
        view.projectionMinor constructor fieldSort levels params
          (view.specializedFields levels params) motives idx
      code.minor = view.projectionMinor view.blockConstructor fieldSort levels
          params (view.specializedFields levels params) motives idx ∧
        code.projector = .lam (view.structureType levels params)
          (VExpr.appN
            (.const view.recursorName
              (view.projectionLevels fieldSort levels))
            (params.map (VExpr.liftN 1) ++
              motives.map (VExpr.liftN 1) ++
              minors.map (VExpr.liftN 1) ++ [.bvar 0])) := by
  unfold projectionCodes at hcode
  simpa using projectionCodes.go_get?_program_shape view levels params
    (view.specializedFields levels params)
    (view.structureType levels params) hcode

/-- Applying a block-backed projection type function to its major substitutes
that major into every earlier projector. -/
theorem projectionCodes_get?_typeFn_beta (view : VBlockStructureView)
    (levels : List VLevel) (params : List VExpr) {idx : Nat}
    {code : VStructureView.ProjectionCode}
    (hcode : (view.projectionCodes levels params)[idx]? = some code)
    (major : VExpr) :
    ∃ field typeBody,
      (view.specializedFields levels params)[idx]? = some field ∧
      code.typeFn = .lam (view.structureType levels params) typeBody ∧
      typeBody.inst major =
        field.instRevAt
          ((view.projectionCodes levels params).take idx |>.map fun prior =>
            .app prior.projector major) 0 := by
  obtain ⟨field, hfield, htypeFn⟩ :=
    view.projectionCodes_get?_typeFn levels params hcode
  let codes := view.projectionCodes levels params
  have hidx : idx < codes.length :=
    (List.getElem?_eq_some_iff.1 hcode).1
  have htake : (codes.take idx).length = idx := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hidx)]
  have htake' :
      ((view.projectionCodes levels params).take idx).length = idx := by
    simpa [codes] using htake
  refine ⟨field, _, hfield, htypeFn, ?_⟩
  rw [VExpr.instN_instRevAt]
  rw [List.length_map, htake']
  simp only [Nat.zero_add, VExpr.inst_liftN1]
  congr 1
  induction (view.projectionCodes levels params).take idx with
  | nil => rfl
  | cons prior previous ih =>
      simp only [List.map_cons]
      rw [ih]
      simp only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero]

/-- Applying an operational projection type function to its major substitutes
that major into every earlier operational projector. -/
theorem operationalProjectionCodes_get?_typeFn_beta
    (view : VBlockStructureView) (levels : List VLevel)
    (params : List VExpr) {idx : Nat}
    {code : VStructureView.ProjectionCode}
    (hcode : (view.operationalProjectionCodes levels params)[idx]? =
      some code) (major : VExpr) :
    ∃ field typeBody,
      (view.specializedFields levels params)[idx]? = some field ∧
      code.typeFn = .lam (view.structureType levels params) typeBody ∧
      typeBody.inst major =
        field.instRevAt
          (view.operationalProjectionArgs levels params idx major) 0 := by
  obtain ⟨field, hfield, htypeFn⟩ :=
    view.operationalProjectionCodes_get?_typeFn levels params hcode
  let codes := view.operationalProjectionCodes levels params
  have hidx : idx < codes.length :=
    (List.getElem?_eq_some_iff.1 hcode).1
  have htake : (codes.take idx).length = idx := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hidx)]
  have htake' :
      ((view.operationalProjectionCodes levels params).take idx).length =
        idx := by
    simpa [codes] using htake
  refine ⟨field, _, hfield, htypeFn, ?_⟩
  rw [VExpr.instN_instRevAt]
  rw [List.length_map, htake']
  simp only [Nat.zero_add, VExpr.inst_liftN1]
  unfold operationalProjectionArgs
  congr 1
  induction (view.operationalProjectionCodes levels params).take idx with
  | nil => rfl
  | cons prior previous ih =>
      simp only [List.map_cons]
      rw [ih]
      simp only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero]

/-- The dependent result type of block-backed projection `idx`, applied to
`major`. -/
def projectionType? (view : VBlockStructureView)
    (levels : List VLevel) (params : List VExpr)
    (idx : Nat) (major : VExpr) : Option VExpr := do
  let code ← (view.projectionCodes levels params)[idx]?
  return .app code.typeFn major

/-- The mutual-recursor encoding of block-backed projection `idx`, applied
to `major`. -/
def project? (view : VBlockStructureView)
    (levels : List VLevel) (params : List VExpr)
    (idx : Nat) (major : VExpr) : Option VExpr := do
  let code ← (view.projectionCodes levels params)[idx]?
  return .app code.projector major

/-- Semantic typing contract for every block-backed projector program. -/
def ProgramsWF (view : VBlockStructureView) (env : VEnv) : Prop :=
  ∀ {U : Nat} {Γ : List VExpr} {levels : List VLevel}
      {params : List VExpr} {idx : Nat}
      {code : VStructureView.ProjectionCode},
    OnCtx Γ (env.IsType U) →
    (∀ level ∈ levels, level.WF U) →
    levels.length = view.uvars →
    params.length = view.nparams →
    (∃ resultLevel, env.SpineWF U Γ (view.familyType.instL levels)
      params (.sort resultLevel)) →
    (view.projectionCodes levels params)[idx]? = some code →
    env.HasType U Γ code.projector
      (.forallE (view.structureType levels params)
        (.app code.typeFn.lift (.bvar 0)))

/-- The block-backed projector contract restricted to source-order indices
below `limit`, for strong induction over dependent fields. -/
def ProgramsWFPrefix (view : VBlockStructureView) (env : VEnv)
    (limit : Nat) : Prop :=
  ∀ {U : Nat} {Γ : List VExpr} {levels : List VLevel}
      {params : List VExpr} {idx : Nat}
      {code : VStructureView.ProjectionCode},
    idx < limit →
    OnCtx Γ (env.IsType U) →
    (∀ level ∈ levels, level.WF U) →
    levels.length = view.uvars →
    params.length = view.nparams →
    (∃ resultLevel, env.SpineWF U Γ (view.familyType.instL levels)
      params (.sort resultLevel)) →
    (view.projectionCodes levels params)[idx]? = some code →
    env.HasType U Γ code.projector
      (.forallE (view.structureType levels params)
        (.app code.typeFn.lift (.bvar 0)))

/-- Typing of a source-order prefix of the prelude-free operational
projectors.  Elimination admissibility is intentionally not bundled here;
the producer theorem below asks for it at exactly the indices whose programs
are used. -/
def OperationalProgramsWFPrefix (view : VBlockStructureView) (env : VEnv)
    (limit : Nat) : Prop :=
  ∀ {U : Nat} {Γ : List VExpr} {levels : List VLevel}
      {params : List VExpr} {idx : Nat}
      {code : VStructureView.ProjectionCode},
    idx < limit →
    OnCtx Γ (env.IsType U) →
    (∀ level ∈ levels, level.WF U) →
    levels.length = view.uvars →
    params.length = view.nparams →
    (∃ resultLevel, env.SpineWF U Γ (view.familyType.instL levels)
      params (.sort resultLevel)) →
    (view.operationalProjectionCodes levels params)[idx]? = some code →
    env.HasType U Γ code.projector
      (.forallE (view.structureType levels params)
        (.app code.typeFn.lift (.bvar 0)))

/-- Every prelude-free operational projector is well typed. -/
def OperationalProgramsWF (view : VBlockStructureView) (env : VEnv) : Prop :=
  ∀ {U : Nat} {Γ : List VExpr} {levels : List VLevel}
      {params : List VExpr} {idx : Nat}
      {code : VStructureView.ProjectionCode},
    OnCtx Γ (env.IsType U) →
    (∀ level ∈ levels, level.WF U) →
    levels.length = view.uvars →
    params.length = view.nparams →
    (∃ resultLevel, env.SpineWF U Γ (view.familyType.instL levels)
      params (.sort resultLevel)) →
    (view.operationalProjectionCodes levels params)[idx]? = some code →
    env.HasType U Γ code.projector
      (.forallE (view.structureType levels params)
        (.app code.typeFn.lift (.bvar 0)))

/-- Elimination is admissible for every operational projector in a
source-order prefix.  This is deliberately separate from host structure
readiness: small elimination may reject an individual non-`Prop` field even
when the host recognizes the declaration as a structure. -/
def OperationalMotiveAdmissiblePrefix (view : VBlockStructureView)
    (limit : Nat) : Prop :=
  ∀ {levels : List VLevel} {params : List VExpr} {idx : Nat}
      {code : VStructureView.ProjectionCode},
    idx < limit →
    (view.operationalProjectionCodes levels params)[idx]? = some code →
    view.generation.motiveLevel.inst
      (view.projectionLevels code.fieldSort levels) = code.fieldSort

/-- Elimination is admissible for every operational projector. -/
def OperationalMotiveAdmissible (view : VBlockStructureView) : Prop :=
  ∀ {levels : List VLevel} {params : List VExpr} {idx : Nat}
      {code : VStructureView.ProjectionCode},
    (view.operationalProjectionCodes levels params)[idx]? = some code →
    view.generation.motiveLevel.inst
      (view.projectionLevels code.fieldSort levels) = code.fieldSort

/-- The selected field minor in every block-backed projection code has the
exact domain generated for the selected constructor.  The remaining mutual
minors are deterministic `PUnit` inhabitants and are reconstructed from this
smaller certificate. -/
def MinorsWF (view : VBlockStructureView) (env : VEnv) : Prop :=
  ∀ {U : Nat} {Γ : List VExpr} {levels : List VLevel}
      {params : List VExpr} {idx : Nat}
      {code : VStructureView.ProjectionCode},
    OnCtx Γ (env.IsType U) →
    (∀ level ∈ levels, level.WF U) →
    levels.length = view.uvars →
    params.length = view.nparams →
    (∃ resultLevel, env.SpineWF U Γ (view.familyType.instL levels)
      params (.sort resultLevel)) →
    (view.projectionCodes levels params)[idx]? = some code →
    env.HasType U Γ code.minor
      (view.generatedProjectionMinorType view.blockConstructor
        code.fieldSort levels params
        (view.projectionMotives levels params code.fieldSort code.typeFn))

/-- The selected-minor contract restricted to projection indices below a
source-order bound. -/
def MinorsWFPrefix (view : VBlockStructureView) (env : VEnv)
    (limit : Nat) : Prop :=
  ∀ {U : Nat} {Γ : List VExpr} {levels : List VLevel}
      {params : List VExpr} {idx : Nat}
      {code : VStructureView.ProjectionCode},
    idx < limit →
    OnCtx Γ (env.IsType U) →
    (∀ level ∈ levels, level.WF U) →
    levels.length = view.uvars →
    params.length = view.nparams →
    (∃ resultLevel, env.SpineWF U Γ (view.familyType.instL levels)
      params (.sort resultLevel)) →
    (view.projectionCodes levels params)[idx]? = some code →
    env.HasType U Γ code.minor
      (view.generatedProjectionMinorType view.blockConstructor
        code.fieldSort levels params
        (view.projectionMotives levels params code.fieldSort code.typeFn))

/-- Exact computation of a bounded projector prefix on the selected
constructor.  The context contains all selected-family fields in canonical
reverse order. -/
def ConstructorProjectorsExactPrefix
    (view : VBlockStructureView) (env : VEnv) (limit : Nat) : Prop :=
  ∀ {U : Nat} {Γ : List VExpr} {levels : List VLevel}
      {params : List VExpr} {count : Nat},
    count ≤ limit →
    OnCtx Γ (env.IsType U) →
    (∀ level ∈ levels, level.WF U) →
    levels.length = view.uvars →
    params.length = view.nparams →
    (∃ resultLevel, env.SpineWF U Γ (view.familyType.instL levels)
      params (.sort resultLevel)) →
    count ≤ (view.projectionCodes levels params).length →
    let fields := view.specializedFields levels params
    List.Forall₂
      (fun projected selected => projected = selected ∨
        env.IsDefEqU U (fields.reverse ++ Γ) projected selected)
      (((view.projectionCodes levels params).take count).map fun prior =>
        .app (prior.projector.liftN fields.length)
          (view.projectionConstructorApp levels params fields))
      (VExpr.bvarRevRange (fields.length - count) count)

/-- Exact selected-constructor computation for an operational projector
prefix. -/
def OperationalConstructorProjectorsExactPrefix
    (view : VBlockStructureView) (env : VEnv) (limit : Nat) : Prop :=
  ∀ {U : Nat} {Γ : List VExpr} {levels : List VLevel}
      {params : List VExpr} {count : Nat},
    count ≤ limit →
    OnCtx Γ (env.IsType U) →
    (∀ level ∈ levels, level.WF U) →
    levels.length = view.uvars →
    params.length = view.nparams →
    (∃ resultLevel, env.SpineWF U Γ (view.familyType.instL levels)
      params (.sort resultLevel)) →
    count ≤ (view.operationalProjectionCodes levels params).length →
    let fields := view.specializedFields levels params
    List.Forall₂
      (fun projected selected => projected = selected ∨
        env.IsDefEqU U (fields.reverse ++ Γ) projected selected)
      (((view.operationalProjectionCodes levels params).take count).map
        fun prior =>
          .app (prior.projector.liftN fields.length)
            (view.projectionConstructorApp levels params fields))
      (VExpr.bvarRevRange (fields.length - count) count)

/-- The runtime-relevant part of a canonical operational prefix.  Projector
applications are typed only at dependency-relevant positions; skipped
positions carry syntactic strengthening evidence.  Exactness is required at
the typed positions only. -/
def OperationalSparseConstructorPrefix
    (view : VBlockStructureView) (env : VEnv) (U : Nat)
    (Γ : List VExpr) (levels : List VLevel) (params : List VExpr)
    (limit : Nat) : Prop :=
  let fields := view.specializedFields levels params
  let m := fields.length
  let source := VExpr.forallN (VExpr.liftTelN m fields 0) (.sort .zero)
  let leftArgs :=
    ((view.operationalProjectionCodes levels params).take limit).map
      fun prior =>
        VExpr.app (prior.projector.liftN m)
          (view.projectionConstructorApp levels params fields)
  let rightArgs := VExpr.bvarRevRange (m - limit) limit
  ∃ cursor, ∃ sparse : env.SparseSpineWF U (fields.reverse ++ Γ)
      source leftArgs cursor,
    sparse.PointwiseDefEq rightArgs

/-- The exact telescope fact needed to type the selected minor at one field:
substituting the operational prefix into the lifted current field agrees with
the canonical field variable context. -/
def OperationalConstructorFieldAligned
    (view : VBlockStructureView) (env : VEnv) (U : Nat)
    (Γ : List VExpr) (levels : List VLevel) (params : List VExpr)
    (limit : Nat) : Prop :=
  ∀ {field : VExpr},
    (view.specializedFields levels params)[limit]? = some field →
    let fields := view.specializedFields levels params
    let m := fields.length
    env.IsDefEqU U (fields.reverse ++ Γ)
      ((field.liftN m limit).instRev
        (((view.operationalProjectionCodes levels params).take limit).map
          fun prior =>
            .app (prior.projector.liftN m)
              (view.projectionConstructorApp levels params fields)))
      (field.liftN (m - limit))

/-- The two sparse traces consumed by the runtime projection loop.  The
major-local trace establishes the next dependent type function; the
canonical-constructor trace records exactly the selected-field equality used
by the generated minor. -/
def OperationalRuntimePrefix
    (view : VBlockStructureView) (env : VEnv) (U : Nat)
    (Γ : List VExpr) (levels : List VLevel) (params : List VExpr)
    (limit : Nat) : Prop :=
  (∃ cursor,
    env.SparseSpineWF U (view.structureType levels params :: Γ)
      (VExpr.forallN
        (view.specializedFields levels (params.map (VExpr.liftN 1)))
        (.sort .zero))
      (view.operationalProjectionArgs levels
        (params.map (VExpr.liftN 1)) limit (.bvar 0)) cursor) ∧
  view.OperationalSparseConstructorPrefix env U Γ levels params limit

/-- Typed canonical captures for the selected constructor's generated mutual
iota rule.  The rule position is retained explicitly because flattened
constructor positions, unlike the singleton case, need not be zero. -/
def ConstructorRuleCapturesPrefix
    (view : VBlockStructureView) (env : VEnv) (limit : Nat) : Prop :=
  ∀ {U : Nat} {Γ : List VExpr} {levels : List VLevel}
      {params : List VExpr} {idx : Nat}
      {code : VStructureView.ProjectionCode},
    idx < limit →
    OnCtx Γ (env.IsType U) →
    (∀ level ∈ levels, level.WF U) →
    levels.length = view.uvars →
    params.length = view.nparams →
    (∃ resultLevel, env.SpineWF U Γ (view.familyType.instL levels)
      params (.sort resultLevel)) →
    (view.projectionCodes levels params)[idx]? = some code →
    let fields := view.specializedFields levels params
    let m := fields.length
    let motives := view.projectionMotives levels params code.fieldSort code.typeFn
    let minors := view.generation.flatCtors.map fun constructor =>
      view.projectionMinor constructor code.fieldSort levels params fields
        motives idx
    ∃ ruleIndex B,
      view.generation.ruleEntry ruleIndex view.blockConstructor ∧
      env.SpineWF U (fields.reverse ++ Γ)
        ((view.generation.rule ruleIndex view.blockConstructor).type.instL
          (view.projectionLevels code.fieldSort levels))
        (params.map (VExpr.liftN m) ++ motives.map (VExpr.liftN m) ++
          minors.map (VExpr.liftN m) ++ VExpr.bvarRevRange 0 m) B

/-- Rule-independent reconstruction typing for the block-backed descriptor. -/
def RebuildWF (view : VBlockStructureView) (env : VEnv) : Prop :=
  ∀ {U : Nat} {Γ : List VExpr} {levels : List VLevel}
      {params : List VExpr} {major : VExpr},
    OnCtx Γ (env.IsType U) →
    (∀ level ∈ levels, level.WF U) →
    levels.length = view.uvars →
    params.length = view.nparams →
    (∃ resultLevel, env.SpineWF U Γ (view.familyType.instL levels)
      params (.sort resultLevel)) →
    env.HasType U Γ major (view.structureType levels params) →
    env.HasType U Γ (view.etaRebuild levels params major)
      (view.structureType levels params)

/-- One typed block-backed projector computes the exact dependent field type
selected by its generated type function. -/
theorem projector_hasType_field_of_type
    {view : VBlockStructureView} {env : VEnv}
    (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} {levels : List VLevel}
    {params : List VExpr} {idx : Nat}
    {code : VStructureView.ProjectionCode}
    (hΓ : OnCtx Γ (env.IsType U))
    (hcode : (view.projectionCodes levels params)[idx]? = some code)
    (hprojector : env.HasType U Γ code.projector
      (.forallE (view.structureType levels params)
        (.app code.typeFn.lift (.bvar 0))))
    {major : VExpr}
    (hmajor : env.HasType U Γ major (view.structureType levels params)) :
    ∃ field typeBody,
      (view.specializedFields levels params)[idx]? = some field ∧
      code.typeFn = .lam (view.structureType levels params) typeBody ∧
      env.HasType U Γ (.app code.projector major)
        (field.instRevAt (view.projectionArgs levels params idx major) 0) := by
  obtain ⟨field, typeBody, hfield, htypeFn, htypeBody⟩ :=
    view.projectionCodes_get?_typeFn_beta levels params hcode major
  have happ : env.HasType U Γ (.app code.projector major)
      (.app code.typeFn major) := by
    simpa only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero] using
      hprojector.app hmajor
  rw [htypeFn] at happ
  obtain ⟨sortLevel, hredexType⟩ := happ.isType henv hΓ
  obtain ⟨A, B, hlam, harg⟩ := hredexType.app_inv henv hΓ
  obtain ⟨⟨_, hstructType⟩, _, hbodyType⟩ :=
    hlam.lam_inv henv hΓ
  have hfunTypeEq := henv.hasType_uniqU hΓ hlam
    (hstructType.lam hbodyType)
  obtain ⟨⟨_, hdomainEq⟩, _⟩ :=
    henv.forallE_inv hΓ hfunTypeEq
  have harg' := henv.hasType_defeqU_r hΓ ⟨_, hdomainEq⟩ harg
  have hbeta : env.IsDefEqU U Γ
      (.app (.lam (view.structureType levels params) typeBody) major)
      (typeBody.inst major) :=
    ⟨_, VEnv.IsDefEq.beta hbodyType harg'⟩
  have hout := henv.hasType_defeqU_r hΓ hbeta happ
  rw [htypeBody] at hout
  refine ⟨field, typeBody, hfield, htypeFn, ?_⟩
  simpa [projectionArgs] using hout

/-- One typed operational projector computes the dependent field type
selected by its generated type function. -/
theorem operationalProjector_hasType_field_of_type
    {view : VBlockStructureView} {env : VEnv}
    (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} {levels : List VLevel}
    {params : List VExpr} {idx : Nat}
    {code : VStructureView.ProjectionCode}
    (hΓ : OnCtx Γ (env.IsType U))
    (hcode : (view.operationalProjectionCodes levels params)[idx]? =
      some code)
    (hprojector : env.HasType U Γ code.projector
      (.forallE (view.structureType levels params)
        (.app code.typeFn.lift (.bvar 0))))
    {major : VExpr}
    (hmajor : env.HasType U Γ major
      (view.structureType levels params)) :
    ∃ field typeBody,
      (view.specializedFields levels params)[idx]? = some field ∧
      code.typeFn = .lam (view.structureType levels params) typeBody ∧
      env.HasType U Γ (.app code.projector major)
        (field.instRevAt
          (view.operationalProjectionArgs levels params idx major) 0) := by
  obtain ⟨field, typeBody, hfield, htypeFn, htypeBody⟩ :=
    view.operationalProjectionCodes_get?_typeFn_beta levels params hcode
      major
  have happ : env.HasType U Γ (.app code.projector major)
      (.app code.typeFn major) := by
    simpa only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero] using
      hprojector.app hmajor
  rw [htypeFn] at happ
  obtain ⟨sortLevel, hredexType⟩ := happ.isType henv hΓ
  obtain ⟨A, B, hlam, harg⟩ := hredexType.app_inv henv hΓ
  obtain ⟨⟨_, hstructType⟩, _, hbodyType⟩ :=
    hlam.lam_inv henv hΓ
  have hfunTypeEq := henv.hasType_uniqU hΓ hlam
    (hstructType.lam hbodyType)
  obtain ⟨⟨_, hdomainEq⟩, _⟩ :=
    henv.forallE_inv hΓ hfunTypeEq
  have harg' := henv.hasType_defeqU_r hΓ ⟨_, hdomainEq⟩ harg
  have hbeta : env.IsDefEqU U Γ
      (.app (.lam (view.structureType levels params) typeBody) major)
      (typeBody.inst major) :=
    ⟨_, VEnv.IsDefEq.beta hbodyType harg'⟩
  have hout := henv.hasType_defeqU_r hΓ hbeta happ
  rw [htypeBody] at hout
  exact ⟨field, typeBody, hfield, htypeFn, hout⟩

/-- A source-ordered prefix of typed block-backed projectors forms the
corresponding dependent field spine. -/
theorem projectionArgsSpineAux_of_prefix
    {view : VBlockStructureView} {env : VEnv}
    (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} {levels : List VLevel}
    {params : List VExpr} {major : VExpr} {limit : Nat}
    (hΓ : OnCtx Γ (env.IsType U))
    (hmajor : env.HasType U Γ major (view.structureType levels params))
    (programs : ∀ {idx : Nat}
      {code : VStructureView.ProjectionCode}, idx < limit →
      (view.projectionCodes levels params)[idx]? = some code →
      env.HasType U Γ code.projector
        (.forallE (view.structureType levels params)
          (.app code.typeFn.lift (.bvar 0))))
    (tailResult : VExpr) :
    ∀ {count : Nat}, count ≤ limit →
      count ≤ (view.specializedFields levels params).length →
      ∃ cursor,
        VExpr.consumeForalls?
            (VExpr.forallN (view.specializedFields levels params) tailResult)
            (view.projectionArgs levels params count major) = some cursor ∧
          env.SpineWF U Γ
            (VExpr.forallN (view.specializedFields levels params) tailResult)
            (view.projectionArgs levels params count major) cursor := by
  intro count hlimit hcount
  induction count with
  | zero => exact ⟨_, rfl, .nil⟩
  | succ count ih =>
      have hcountLt : count <
          (view.specializedFields levels params).length := by omega
      have hcodeIdx : count <
          (view.projectionCodes levels params).length := by
        simpa using hcountLt
      let code := (view.projectionCodes levels params)[count]
      have hcode :
          (view.projectionCodes levels params)[count]? = some code :=
        List.getElem?_eq_getElem hcodeIdx
      have hargsLength :
          (view.projectionArgs levels params count major).length = count :=
        view.projectionArgs_length levels params count major
          (Nat.le_of_lt hcodeIdx)
      obtain ⟨cursor, hconsume, hspine⟩ :=
        ih (Nat.le_of_lt (Nat.lt_of_succ_le hlimit))
          (Nat.le_of_lt hcountLt)
      obtain ⟨field, semanticBody, hfield, hconsumeDomain⟩ :=
        VExpr.consumeForalls?_forallN_domain
          (view.specializedFields levels params) tailResult
          (view.projectionArgs levels params count major)
          (by simpa [hargsLength] using hcountLt)
      have hcursorShape : cursor =
          .forallE
            (field.instRevAt
              (view.projectionArgs levels params count major) 0)
            semanticBody :=
        Option.some.inj (hconsume.symm.trans hconsumeDomain)
      subst cursor
      have hprojector := programs (Nat.lt_of_succ_le hlimit) hcode
      obtain ⟨field', _, hfield', _, hprojectorField⟩ :=
        projector_hasType_field_of_type henv hΓ hcode hprojector hmajor
      have hfieldEq : field' = field :=
        Option.some.inj
          (hfield'.symm.trans (by simpa [hargsLength] using hfield))
      subst field'
      refine ⟨semanticBody.inst (.app code.projector major), ?_, ?_⟩
      · rw [view.projectionArgs_succ levels params count major hcode]
        rw [VExpr.consumeForalls?_append, hconsumeDomain]
        rfl
      · rw [view.projectionArgs_succ levels params count major hcode]
        exact hspine.snoc hprojectorField

/-- A typed operational projector prefix forms the corresponding dependent
field spine. -/
theorem operationalProjectionArgsSpineAux_of_prefix
    {view : VBlockStructureView} {env : VEnv}
    (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} {levels : List VLevel}
    {params : List VExpr} {major : VExpr} {limit : Nat}
    (hΓ : OnCtx Γ (env.IsType U))
    (hmajor : env.HasType U Γ major
      (view.structureType levels params))
    (programs : ∀ {idx : Nat}
      {code : VStructureView.ProjectionCode}, idx < limit →
      (view.operationalProjectionCodes levels params)[idx]? = some code →
      env.HasType U Γ code.projector
        (.forallE (view.structureType levels params)
          (.app code.typeFn.lift (.bvar 0))))
    (tailResult : VExpr) :
    ∀ {count : Nat}, count ≤ limit →
      count ≤ (view.specializedFields levels params).length →
      ∃ cursor,
        VExpr.consumeForalls?
            (VExpr.forallN (view.specializedFields levels params) tailResult)
            (view.operationalProjectionArgs levels params count major) =
              some cursor ∧
          env.SpineWF U Γ
            (VExpr.forallN (view.specializedFields levels params) tailResult)
            (view.operationalProjectionArgs levels params count major)
            cursor := by
  intro count hlimit hcount
  induction count with
  | zero => exact ⟨_, rfl, .nil⟩
  | succ count ih =>
      have hcountLt : count <
          (view.specializedFields levels params).length := by omega
      have hcodeIdx : count <
          (view.operationalProjectionCodes levels params).length := by
        simpa using hcountLt
      let code := (view.operationalProjectionCodes levels params)[count]
      have hcode :
          (view.operationalProjectionCodes levels params)[count]? =
            some code := List.getElem?_eq_getElem hcodeIdx
      have hargsLength :
          (view.operationalProjectionArgs levels params count major).length =
            count :=
        view.operationalProjectionArgs_length levels params count major
          (Nat.le_of_lt hcodeIdx)
      obtain ⟨cursor, hconsume, hspine⟩ :=
        ih (Nat.le_of_lt (Nat.lt_of_succ_le hlimit))
          (Nat.le_of_lt hcountLt)
      obtain ⟨field, semanticBody, hfield, hconsumeDomain⟩ :=
        VExpr.consumeForalls?_forallN_domain
          (view.specializedFields levels params) tailResult
          (view.operationalProjectionArgs levels params count major)
          (by simpa [hargsLength] using hcountLt)
      have hcursorShape : cursor =
          .forallE
            (field.instRevAt
              (view.operationalProjectionArgs levels params count major) 0)
            semanticBody :=
        Option.some.inj (hconsume.symm.trans hconsumeDomain)
      subst cursor
      have hprojector := programs (Nat.lt_of_succ_le hlimit) hcode
      obtain ⟨field', _, hfield', _, hprojectorField⟩ :=
        operationalProjector_hasType_field_of_type henv hΓ hcode hprojector
          hmajor
      have hfieldEq : field' = field :=
        Option.some.inj
          (hfield'.symm.trans (by simpa [hargsLength] using hfield))
      subst field'
      refine ⟨semanticBody.inst (.app code.projector major), ?_, ?_⟩
      · rw [view.operationalProjectionArgs_succ levels params count major
          hcode]
        rw [VExpr.consumeForalls?_append, hconsumeDomain]
        rfl
      · rw [view.operationalProjectionArgs_succ levels params count major
          hcode]
        exact hspine.snoc hprojectorField

/-- All typed prelude-free projectors of a typed major form the complete
dependent selected-field spine. -/
theorem OperationalProgramsWF.operationalProjectionArgsSpine
    {view : VBlockStructureView} {env : VEnv}
    (self : view.OperationalProgramsWF env)
    (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} {levels : List VLevel}
    {params : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U))
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    {major : VExpr}
    (hmajor : env.HasType U Γ major (view.structureType levels params))
    (tailResult : VExpr) :
    env.SpineWF U Γ
      (VExpr.forallN (view.specializedFields levels params) tailResult)
      (view.operationalProjectionArgs levels params
        (view.specializedFields levels params).length major)
      (VExpr.instRev tailResult
        (view.operationalProjectionArgs levels params
          (view.specializedFields levels params).length major)) := by
  have programs : ∀ {idx : Nat}
      {code : VStructureView.ProjectionCode},
      idx < (view.specializedFields levels params).length →
      (view.operationalProjectionCodes levels params)[idx]? = some code →
      env.HasType U Γ code.projector
        (.forallE (view.structureType levels params)
          (.app code.typeFn.lift (.bvar 0))) := by
    intro idx code hidx hcode
    exact self hΓ hlevels hlevelsLength hparamsLength hparamsSpine hcode
  obtain ⟨_, _, hspine⟩ := operationalProjectionArgsSpineAux_of_prefix
    henv hΓ hmajor programs tailResult (Nat.le_refl _) (Nat.le_refl _)
  apply hspine.retarget
  exact view.operationalProjectionArgs_length levels params
    (view.specializedFields levels params).length major (by simp)

/-- Applying the complete prelude-free projection spine to a typed selected
constructor prefix rebuilds a value of the selected family. -/
theorem OperationalProgramsWF.operationalEtaRebuild_hasType_of_constructorPrefix
    {view : VBlockStructureView} {env : VEnv}
    (self : view.OperationalProgramsWF env)
    (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} {levels : List VLevel}
    {params : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U))
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    {major : VExpr}
    (hmajor : env.HasType U Γ major (view.structureType levels params))
    (hconstructorPrefix : env.HasType U Γ
      (VExpr.appN (.const view.constructorName levels) params)
      (VExpr.forallN (view.specializedFields levels params)
        ((view.structureType levels params).liftN
          (view.specializedFields levels params).length))) :
    env.HasType U Γ (view.operationalEtaRebuild levels params major)
      (view.structureType levels params) := by
  have hfields := self.operationalProjectionArgsSpine henv hΓ hlevels
    hlevelsLength hparamsLength hparamsSpine hmajor
    ((view.structureType levels params).liftN
      (view.specializedFields levels params).length)
  have hrebuild := hfields.hasType_appN hconstructorPrefix
  let args := view.operationalProjectionArgs levels params
    (view.specializedFields levels params).length major
  have hargsLength :
      args.length = (view.specializedFields levels params).length :=
    view.operationalProjectionArgs_length levels params
      (view.specializedFields levels params).length major (by simp)
  have hlift :
      (view.structureType levels params).liftN
          (view.specializedFields levels params).length =
        (view.structureType levels params).liftN args.length :=
    congrArg (view.structureType levels params).liftN hargsLength.symm
  have hresult :
      VExpr.instRev
        ((view.structureType levels params).liftN
          (view.specializedFields levels params).length) args =
        view.structureType levels params := by
    calc
      _ = VExpr.instRev
          ((view.structureType levels params).liftN args.length) args :=
        congrArg (VExpr.instRev · args) hlift
      _ = view.structureType levels params :=
        VExpr.instRev_liftN_len args _
  rw [hresult] at hrebuild
  simpa [operationalEtaRebuild, VExpr.appN_append] using hrebuild

private theorem ProgramsWF.projectionArgsSpineAux
    {view : VBlockStructureView} {env : VEnv}
    (self : view.ProgramsWF env) (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} {levels : List VLevel}
    {params : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U))
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    {major : VExpr}
    (hmajor : env.HasType U Γ major (view.structureType levels params))
    (tailResult : VExpr) :
    ∀ {count : Nat},
      count ≤ (view.specializedFields levels params).length →
      ∃ cursor,
        VExpr.consumeForalls?
            (VExpr.forallN (view.specializedFields levels params) tailResult)
            (view.projectionArgs levels params count major) = some cursor ∧
          env.SpineWF U Γ
            (VExpr.forallN (view.specializedFields levels params) tailResult)
            (view.projectionArgs levels params count major) cursor := by
  intro count hcount
  induction count with
  | zero => exact ⟨_, rfl, .nil⟩
  | succ count ih =>
      have hcountLt : count <
          (view.specializedFields levels params).length := by omega
      have hcodeIdx : count <
          (view.projectionCodes levels params).length := by
        simpa using hcountLt
      let code := (view.projectionCodes levels params)[count]
      have hcode :
          (view.projectionCodes levels params)[count]? = some code :=
        List.getElem?_eq_getElem hcodeIdx
      have hargsLength :
          (view.projectionArgs levels params count major).length = count :=
        view.projectionArgs_length levels params count major
          (Nat.le_of_lt hcodeIdx)
      obtain ⟨cursor, hconsume, hspine⟩ :=
        ih (Nat.le_of_lt hcountLt)
      obtain ⟨field, semanticBody, hfield, hconsumeDomain⟩ :=
        VExpr.consumeForalls?_forallN_domain
          (view.specializedFields levels params) tailResult
          (view.projectionArgs levels params count major)
          (by simpa [hargsLength] using hcountLt)
      have hcursorShape : cursor =
          .forallE
            (field.instRevAt
              (view.projectionArgs levels params count major) 0)
            semanticBody :=
        Option.some.inj (hconsume.symm.trans hconsumeDomain)
      subst cursor
      have hprojector := self hΓ hlevels hlevelsLength hparamsLength
        hparamsSpine hcode
      obtain ⟨field', _, hfield', _, hprojectorField⟩ :=
        projector_hasType_field_of_type henv hΓ hcode hprojector hmajor
      have hfieldEq : field' = field :=
        Option.some.inj
          (hfield'.symm.trans (by simpa [hargsLength] using hfield))
      subst field'
      refine ⟨semanticBody.inst (.app code.projector major), ?_, ?_⟩
      · rw [view.projectionArgs_succ levels params count major hcode]
        rw [VExpr.consumeForalls?_append, hconsumeDomain]
        rfl
      · rw [view.projectionArgs_succ levels params count major hcode]
        exact hspine.snoc hprojectorField

/-- All block-backed projections of a typed major form the dependent field
spine expected by the selected constructor. -/
theorem ProgramsWF.projectionArgsSpine
    {view : VBlockStructureView} {env : VEnv}
    (self : view.ProgramsWF env) (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} {levels : List VLevel}
    {params : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U))
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    {major : VExpr}
    (hmajor : env.HasType U Γ major (view.structureType levels params))
    (tailResult : VExpr) :
    env.SpineWF U Γ
      (VExpr.forallN (view.specializedFields levels params) tailResult)
      (view.projectionArgs levels params
        (view.specializedFields levels params).length major)
      (VExpr.instRev tailResult
        (view.projectionArgs levels params
          (view.specializedFields levels params).length major)) := by
  obtain ⟨_, _, hspine⟩ := self.projectionArgsSpineAux henv hΓ hlevels
    hlevelsLength hparamsLength hparamsSpine hmajor tailResult
    (Nat.le_refl _)
  apply hspine.retarget
  exact view.projectionArgs_length levels params
    (view.specializedFields levels params).length major (by simp)

/-- Applying the complete block-backed projection spine to a typed selected
constructor prefix rebuilds a value of the selected family. -/
theorem ProgramsWF.etaRebuild_hasType_of_constructorPrefix
    {view : VBlockStructureView} {env : VEnv}
    (self : view.ProgramsWF env) (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} {levels : List VLevel}
    {params : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U))
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    {major : VExpr}
    (hmajor : env.HasType U Γ major (view.structureType levels params))
    (hconstructorPrefix : env.HasType U Γ
      (VExpr.appN (.const view.constructorName levels) params)
      (VExpr.forallN (view.specializedFields levels params)
        ((view.structureType levels params).liftN
          (view.specializedFields levels params).length))) :
    env.HasType U Γ (view.etaRebuild levels params major)
      (view.structureType levels params) := by
  have hfields := self.projectionArgsSpine henv hΓ hlevels hlevelsLength
    hparamsLength hparamsSpine hmajor
    ((view.structureType levels params).liftN
      (view.specializedFields levels params).length)
  have hrebuild := hfields.hasType_appN hconstructorPrefix
  let args := view.projectionArgs levels params
    (view.specializedFields levels params).length major
  have hargsLength :
      args.length = (view.specializedFields levels params).length :=
    view.projectionArgs_length levels params
      (view.specializedFields levels params).length major (by simp)
  have hlift :
      (view.structureType levels params).liftN
          (view.specializedFields levels params).length =
        (view.structureType levels params).liftN args.length :=
    congrArg (view.structureType levels params).liftN hargsLength.symm
  have hresult :
      VExpr.instRev
        ((view.structureType levels params).liftN
          (view.specializedFields levels params).length) args =
        view.structureType levels params := by
    calc
      _ = VExpr.instRev
          ((view.structureType levels params).liftN args.length) args :=
        congrArg (VExpr.instRev · args) hlift
      _ = view.structureType levels params :=
        VExpr.instRev_liftN_len args _
  rw [hresult] at hrebuild
  simpa [etaRebuild, VExpr.appN_append] using hrebuild

/-- Exact registration of the selected family and constructor together with
the complete block recursor/rule inventory. -/
structure Registered (view : VBlockStructureView) (env : VEnv) : Prop where
  family : env.constants view.name = some view.family.raw.toVConstant
  constructor : env.constants view.constructorName =
    some view.constructor.raw.toVConstant
  recursor : env.constants view.recursorName =
    some (view.generation.generatedRecursor view.family)
  rules : ∀ rule ∈ view.generation.generatedRules, env.defeqs rule

theorem Registered.mono {view : VBlockStructureView} {env env' : VEnv}
    (hle : env ≤ env') (self : view.Registered env) :
    view.Registered env' where
  family := hle.constants self.family
  constructor := hle.constants self.constructor
  recursor := hle.constants self.recursor
  rules := fun rule member => hle.defeqs (self.rules rule member)

/-- The syntax-closure fragment of a checked block generation.  Projector
code naturality depends on the producer's generated family/constructor
telescopes, but not on final constant registration or on the selected field
sort annotation.  Keeping this fragment separate lets a nested producer
retain the algebra before its flattened endpoint is restored away. -/
structure ProjectionSyntaxWF (view : VBlockStructureView)
    (env : VEnv) : Prop where
  generationEnv : BlockGenerationEnv view.generation env

/-- A successful complete block transaction registers the exact selected
family artifacts; no singleton generation is reconstructed. -/
theorem Registered.ofTrace
    {view : VBlockStructureView} {pre env : VEnv}
    (trace : VEnv.AddInductBlockGenerationTrace pre env view.generation) :
    view.Registered env where
  family := by
    apply trace.family_lookup
    rw [← view.generation.families_map_raw]
    exact List.mem_map.2 ⟨view.family, view.family_mem, rfl⟩
  constructor := by
    apply trace.ctor_lookup
    rw [← view.generation.flatCtors_map_raw]
    exact List.mem_map.2 ⟨view.blockConstructor,
      view.blockConstructor_mem, rfl⟩
  recursor := by
    let recursor : VConstVal :=
      ⟨view.generation.generatedRecursor view.family, view.recursorName⟩
    have hrecursor : recursor ∈ view.generation.recursors := by
      simp only [BlockGenerationChecked.recursors, List.mem_map]
      exact ⟨view.family, view.family_mem, rfl⟩
    simpa [recursor] using trace.rec_lookup hrecursor
  rules := fun rule member => trace.rule_mem member

/-- Exact registration of the universe-polymorphic dummy family used by
nonselected mutual motives.  This is ordinary environment evidence, kept
separate from the generated block because `PUnit` belongs to the prelude. -/
structure PUnitRegistered (env : VEnv) : Prop where
  type : env.constants ``PUnit =
    some { uvars := 1, type := .sort (.param 0) }
  unit : env.constants ``PUnit.unit =
    some { uvars := 1, type := .const ``PUnit [.param 0] }

theorem PUnitRegistered.mono {env env' : VEnv}
    (hle : env ≤ env') (self : PUnitRegistered env) :
    PUnitRegistered env' where
  type := hle.constants self.type
  unit := hle.constants self.unit

/-- Producer-owned layout data for a block-backed structure restriction.
The complete block generation invariant and selected field telescope are
available for every retained family.  No unrelated primitive registration
or small-elimination projector claim is part of this layer. -/
structure LayoutWF (view : VBlockStructureView) (env : VEnv) : Prop
    extends VBlockStructureView.Registered view env where
  generationEnv : BlockGenerationEnv view.generation env
  fieldTelescope : env.OnSortTel view.uvars
    view.generation.block.checked.params.reverse view.fields view.fieldSorts

/-- Forget registration and selected-sort evidence while retaining exactly
the generation closure used by projector syntax. -/
theorem LayoutWF.toProjectionSyntaxWF
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) : view.ProjectionSyntaxWF env where
  generationEnv := self.generationEnv

instance {view : VBlockStructureView} {env : VEnv} :
    Coe (view.LayoutWF env) (view.ProjectionSyntaxWF env) where
  coe := LayoutWF.toProjectionSyntaxWF

/-- Full generated-projector well-formedness for a mutual-block view. -/
structure WF (view : VBlockStructureView) (env : VEnv) : Prop
    extends VBlockStructureView.LayoutWF view env where
  punitRegistered : PUnitRegistered env
  smallFields : view.generation.elimination = .small →
    ∀ level ∈ view.fieldSorts, level = .zero

/-- The registered raw family type is definitionally equal to the selected
family's projection-facing type with its validated result sort. -/
theorem LayoutWF.rawFamilyType_defeq_familyType
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) :
    ∃ sortLevel, env.IsDefEq view.uvars []
      view.rawFamilyType view.familyType (.sort sortLevel) := by
  have hfamilyWF := self.generationEnv.familyWF view.family view.family_mem
  have htel := hfamilyWF.familyTel.raw_onTel.telDefEq_refl
  have hresult : env.IsDefEq view.uvars
      ((view.family.rawParams view.nparams ++
        view.family.rawIndices view.nparams).reverse ++ [])
      (view.family.rawResult view.nparams)
      (.sort view.resultLevel) (.sort (.succ view.resultLevel)) := by
    simpa [VBlockStructureView.resultLevel] using hfamilyWF.familyResult
  obtain ⟨sortLevel, hforall⟩ := htel.forallN_defeq hresult
  refine ⟨sortLevel, ?_⟩
  have hrawType := VInductDecl.NormalizedFamily.rawType_eq
    (source := view.source) view.family
  simpa [VBlockStructureView.rawFamilyType,
    VBlockStructureView.familyType, hrawType, view.raw_indices_eq,
    VExpr.forallN_append, VExpr.forallN] using hforall

/-- Type the selected registered family constant at its projection-facing
sort-normalized type. -/
theorem LayoutWF.familyConst_hasType
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars) :
    env.HasType U Γ (.const view.name levels)
      (view.familyType.instL levels) := by
  obtain ⟨_, htype⟩ := self.rawFamilyType_defeq_familyType
  have htypeLevels := htype.instL hlevels
  have hraw : env.HasType U [] (.const view.name levels)
      (view.rawFamilyType.instL levels) := by
    apply VEnv.HasType.const self.family hlevels
    simpa using hlevelsLength.trans view.family_uvars_eq.symm
  exact (htypeLevels.defeq hraw).weak0 henv

/-- The projection-facing family type is syntactically closed. -/
theorem LayoutWF.familyType_closed
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.Ordered) :
    view.familyType.ClosedN := by
  obtain ⟨_, htype⟩ := self.rawFamilyType_defeq_familyType
  exact (htype.closedN' henv.closed trivial).2.1

abbrev WF.familyConst_hasType
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) := self.toLayoutWF.familyConst_hasType

abbrev WF.familyType_closed
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) := self.toLayoutWF.familyType_closed

theorem LayoutWF.mono {view : VBlockStructureView} {env env' : VEnv}
    (hle : env ≤ env') (ordered : env'.Ordered)
    (self : view.LayoutWF env) : view.LayoutWF env' where
  toRegistered := self.toRegistered.mono hle
  generationEnv := self.generationEnv.mono hle ordered
  fieldTelescope := self.fieldTelescope.mono hle

theorem WF.mono {view : VBlockStructureView} {env env' : VEnv}
    (hle : env ≤ env') (ordered : env'.Ordered) (self : view.WF env) :
    view.WF env' where
  toLayoutWF := self.toLayoutWF.mono hle ordered
  punitRegistered := self.punitRegistered.mono hle
  smallFields := self.smallFields

/-- The selected unindexed family exposes exactly the shared checked block
parameters as its emitted telescope. -/
theorem WF.parameters {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) :
    env.OnTel view.uvars []
      view.generation.block.checked.params := by
  have familyTel :=
    self.generationEnv.emittedFamily_onTel view.family_mem
  simpa [view.raw_indices_eq] using familyTel

theorem LayoutWF.parameters {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) :
    env.OnTel view.uvars []
      view.generation.block.checked.params := by
  have familyTel :=
    self.generationEnv.emittedFamily_onTel view.family_mem
  simpa [view.raw_indices_eq] using familyTel

/-- Generation closure alone exposes the shared checked parameter
telescope; selected registration is irrelevant to this syntax fact. -/
theorem ProjectionSyntaxWF.parameters
    {view : VBlockStructureView} {env : VEnv}
    (self : view.ProjectionSyntaxWF env) :
    env.OnTel view.uvars []
      view.generation.block.checked.params := by
  have familyTel :=
    self.generationEnv.emittedFamily_onTel view.family_mem
  simpa [view.raw_indices_eq] using familyTel

private theorem motiveLevel_projectionLevels (view : VBlockStructureView)
    (fieldSort : VLevel) (levels : List VLevel) :
    view.generation.motiveLevel.inst
        (view.projectionLevels fieldSort levels) =
      match view.generation.elimination with
      | .large => fieldSort
      | .small => .zero := by
  unfold BlockGenerationChecked.motiveLevel
  unfold ElimMode.motiveLevel projectionLevels
  cases view.generation.elimination <;> rfl

/-- Large elimination preserves the selected field universe in the generated
projection motive.  Exposed for runtime projection consumers, which only know
the checked block layout and the elimination branch chosen by execution. -/
theorem motiveLevel_projectionLevels_of_large (view : VBlockStructureView)
    (large : view.generation.elimination = .large)
    (fieldSort : VLevel) (levels : List VLevel) :
    view.generation.motiveLevel.inst
        (view.projectionLevels fieldSort levels) = fieldSort := by
  rw [motiveLevel_projectionLevels, large]

private theorem WF.motiveLevel_projectionLevels
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env)
    (fieldSort : VLevel) (hfieldSort : fieldSort ∈ view.fieldSorts)
    (levels : List VLevel) :
    view.generation.motiveLevel.inst
        (view.projectionLevels (fieldSort.inst levels) levels) =
      fieldSort.inst levels := by
  rw [VBlockStructureView.motiveLevel_projectionLevels]
  cases hmode : view.generation.elimination with
  | large => rfl
  | small =>
      rw [self.smallFields hmode fieldSort hfieldSort]
      rfl

/-- Parameters accepted by the selected family consume the common checked
block-parameter prefix used by every emitted mutual constructor. -/
theorem LayoutWF.checkedParamsSpine
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (_hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (target : VExpr) :
    env.SpineWF U Γ
      (VExpr.forallN
        (view.generation.block.checked.params.map (VExpr.instL levels))
        target) params (VExpr.instRev target params) := by
  obtain ⟨resultLevel, hspine⟩ := paramsSpine
  have hrawLength :
      (view.family.rawParams view.nparams).length = view.nparams :=
    (view.generation.shape.2.2.2.2 view.family view.family_mem).2.2.1
  have hspineShape : env.SpineWF U Γ
      (VExpr.forallN
        ((view.family.rawParams view.nparams).map (VExpr.instL levels))
        (.sort (view.resultLevel.inst levels)))
      params (.sort resultLevel) := by
    simpa [VBlockStructureView.familyType, VExpr.instL_forallN,
      VExpr.instL] using hspine
  have hparamsRaw : env.SpineWF U Γ
      (VExpr.forallN
        ((view.family.rawParams view.nparams).map (VExpr.instL levels))
        (.sort .zero)) params (.sort .zero) := by
    have hout := hspineShape.retarget
      (by simpa [hrawLength] using hparamsLength) (.sort .zero)
    rw [VExpr.instRev_closedN params (by trivial)] at hout
    exact hout
  have hfamilyDefEq :=
    (self.generationEnv.rawParams_defeq view.family_mem).instL hlevels
  have hrawLift : VExpr.liftTelN Γ.length
      ((view.family.rawParams view.nparams).map (VExpr.instL levels)) 0 =
      (view.family.rawParams view.nparams).map (VExpr.instL levels) := by
    simpa using VEnv.OnTel.liftTelN_eq henv
      hfamilyDefEq.raw_onTel (by trivial) Γ.length
  have hcheckedLift : VExpr.liftTelN Γ.length
      (view.generation.block.checked.params.map (VExpr.instL levels)) 0 =
      view.generation.block.checked.params.map (VExpr.instL levels) := by
    simpa using VEnv.OnTel.liftTelN_eq henv
      (hfamilyDefEq.view_onTel henv) (by trivial) Γ.length
  have hfamilyDefEqΓ := hfamilyDefEq.weakN henv
    (Ctx.LiftN.zero (n := Γ.length) (Γ := []) Γ)
  rw [hrawLift, hcheckedLift] at hfamilyDefEqΓ
  simp only [List.append_nil] at hfamilyDefEqΓ
  have hparamsChecked : env.SpineWF U Γ
      (VExpr.forallN
        (view.generation.block.checked.params.map (VExpr.instL levels))
        (.sort .zero)) params (.sort .zero) :=
    VEnv.TelDefEq.spine_sort_view henv hfamilyDefEqΓ hparamsRaw
      (by simpa [hrawLength] using hparamsLength)
  have hcheckedLength : params.length =
      (view.generation.block.checked.params.map
        (VExpr.instL levels)).length := by
    simpa [view.checked_params_length] using hparamsLength
  exact hparamsChecked.retarget hcheckedLength target

abbrev WF.checkedParamsSpine
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) := self.toLayoutWF.checkedParamsSpine

/-- Parameters accepted by the selected family also consume the stored raw
constructor parameter prefix.  For a mutual block this follows from the
producer-owned declared-constructor telescope: its first `nparams` entries
are definitionally equal to the common checked parameter telescope. -/
theorem LayoutWF.constructorParamsSpine
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (target : VExpr) :
    env.SpineWF U Γ
      (VExpr.forallN
        (view.constructorParams.map (VExpr.instL levels))
        target) params (VExpr.instRev target params) := by
  have hparamsChecked := self.checkedParamsSpine henv levels hlevels
    hlevelsLength params hparamsLength paramsSpine (.sort .zero)
  rw [VExpr.instRev_closedN params (by trivial)] at hparamsChecked
  have hconstructorShape :=
    (view.generation.shape.2.2.2.2 view.family view.family_mem).2.2.2.2.2.2
      view.constructor view.constructor_mem
  have hconstructorDefEq₀ :=
    ((self.generationEnv.ctorWF view.blockConstructor
      view.blockConstructor_mem).declaredTel.take view.nparams).instL hlevels
  have hconstructorDefEq : env.TelDefEq U []
      (view.constructorParams.map (VExpr.instL levels))
      (view.generation.block.checked.params.map (VExpr.instL levels)) := by
    simpa [VBlockStructureView.constructorParams,
      VBlockStructureView.blockConstructor,
      NormalizedBlockCtor.declaredBinders,
      NormalizedBlockCtor.viewBinders,
      VInductDecl.NormalizedCtor.declaredBinders,
      hconstructorShape.2.2.1, view.checked_params_length] using
        hconstructorDefEq₀
  have hconstructorRawLift : VExpr.liftTelN Γ.length
      (view.constructorParams.map (VExpr.instL levels)) 0 =
      view.constructorParams.map (VExpr.instL levels) := by
    simpa using VEnv.OnTel.liftTelN_eq henv
      hconstructorDefEq.raw_onTel (by trivial) Γ.length
  have hconstructorCheckedLift : VExpr.liftTelN Γ.length
      (view.generation.block.checked.params.map (VExpr.instL levels)) 0 =
      view.generation.block.checked.params.map (VExpr.instL levels) := by
    simpa using VEnv.OnTel.liftTelN_eq henv
      (hconstructorDefEq.view_onTel henv) (by trivial) Γ.length
  have hconstructorDefEqΓ := hconstructorDefEq.weakN henv
    (Ctx.LiftN.zero (n := Γ.length) (Γ := []) Γ)
  rw [hconstructorRawLift, hconstructorCheckedLift] at hconstructorDefEqΓ
  simp only [List.append_nil] at hconstructorDefEqΓ
  have hconstructorLength : params.length =
      (view.constructorParams.map (VExpr.instL levels)).length := by
    simpa [VBlockStructureView.constructorParams] using
      hparamsLength.trans hconstructorShape.2.2.1.symm
  have hout := VEnv.TelDefEq.spine_sort henv hconstructorDefEqΓ
    hparamsChecked hconstructorLength
  exact hout.retarget hconstructorLength target

abbrev WF.constructorParamsSpine
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) := self.toLayoutWF.constructorParamsSpine

/-- Recover the selected family parameter spine from a raw constructor
parameter prefix.  The two raw surfaces meet through the common checked
block-parameter telescope retained by the producer. -/
theorem LayoutWF.familyParamsSpine_of_constructor
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (_hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    {target cursor : VExpr}
    (constructorSpine : env.SpineWF U Γ
      (VExpr.forallN
        (view.constructorParams.map (VExpr.instL levels)) target)
      params cursor) :
    env.SpineWF U Γ (view.familyType.instL levels) params
      (.sort (view.resultLevel.inst levels)) := by
  have hrawLength := view.raw_params_length
  have hconstructorShape :=
    (view.generation.shape.2.2.2.2 view.family view.family_mem).2.2.2.2.2.2
      view.constructor view.constructor_mem
  have hconstructorLength : params.length =
      (view.constructorParams.map (VExpr.instL levels)).length := by
    simpa [VBlockStructureView.constructorParams] using
      hparamsLength.trans hconstructorShape.2.2.1.symm
  have hparamsConstructor : env.SpineWF U Γ
      (VExpr.forallN
        (view.constructorParams.map (VExpr.instL levels)) (.sort .zero))
      params (.sort .zero) := by
    have hout := constructorSpine.retarget hconstructorLength (.sort .zero)
    rw [VExpr.instRev_closedN params (by trivial)] at hout
    exact hout
  have hfamilyDefEq :=
    (self.generationEnv.rawParams_defeq view.family_mem).instL hlevels
  have hrawLift : VExpr.liftTelN Γ.length
      ((view.family.rawParams view.nparams).map (VExpr.instL levels)) 0 =
      (view.family.rawParams view.nparams).map (VExpr.instL levels) := by
    simpa using VEnv.OnTel.liftTelN_eq henv
      hfamilyDefEq.raw_onTel (by trivial) Γ.length
  have hcheckedLift : VExpr.liftTelN Γ.length
      (view.generation.block.checked.params.map (VExpr.instL levels)) 0 =
      view.generation.block.checked.params.map (VExpr.instL levels) := by
    simpa using VEnv.OnTel.liftTelN_eq henv
      (hfamilyDefEq.view_onTel henv) (by trivial) Γ.length
  have hfamilyDefEqΓ := hfamilyDefEq.weakN henv
    (Ctx.LiftN.zero (n := Γ.length) (Γ := []) Γ)
  rw [hrawLift, hcheckedLift] at hfamilyDefEqΓ
  simp only [List.append_nil] at hfamilyDefEqΓ
  have hconstructorDefEq₀ :=
    ((self.generationEnv.ctorWF view.blockConstructor
      view.blockConstructor_mem).declaredTel.take view.nparams).instL hlevels
  have hconstructorDefEq : env.TelDefEq U []
      (view.constructorParams.map (VExpr.instL levels))
      (view.generation.block.checked.params.map (VExpr.instL levels)) := by
    simpa [VBlockStructureView.constructorParams,
      VBlockStructureView.blockConstructor,
      NormalizedBlockCtor.declaredBinders,
      NormalizedBlockCtor.viewBinders,
      VInductDecl.NormalizedCtor.declaredBinders,
      hconstructorShape.2.2.1, view.checked_params_length] using
        hconstructorDefEq₀
  have hconstructorRawLift : VExpr.liftTelN Γ.length
      (view.constructorParams.map (VExpr.instL levels)) 0 =
      view.constructorParams.map (VExpr.instL levels) := by
    simpa using VEnv.OnTel.liftTelN_eq henv
      hconstructorDefEq.raw_onTel (by trivial) Γ.length
  have hconstructorDefEqΓ := hconstructorDefEq.weakN henv
    (Ctx.LiftN.zero (n := Γ.length) (Γ := []) Γ)
  rw [hconstructorRawLift, hcheckedLift] at hconstructorDefEqΓ
  simp only [List.append_nil] at hconstructorDefEqΓ
  have hparamsChecked : env.SpineWF U Γ
      (VExpr.forallN
        (view.generation.block.checked.params.map (VExpr.instL levels))
        (.sort .zero)) params (.sort .zero) :=
    VEnv.TelDefEq.spine_sort_view henv hconstructorDefEqΓ
      hparamsConstructor hconstructorLength
  have hrawParamsLength : params.length =
      ((view.family.rawParams view.nparams).map
        (VExpr.instL levels)).length := by
    simpa [hrawLength] using hparamsLength
  have hparamsRaw : env.SpineWF U Γ
      (VExpr.forallN
        ((view.family.rawParams view.nparams).map (VExpr.instL levels))
        (.sort .zero)) params (.sort .zero) :=
    VEnv.TelDefEq.spine_sort henv hfamilyDefEqΓ hparamsChecked
      hrawParamsLength
  have hout := hparamsRaw.retarget hrawParamsLength
    (.sort (view.resultLevel.inst levels))
  rw [VExpr.instRev_closedN params (by trivial)] at hout
  simpa [VBlockStructureView.familyType, VExpr.instL_forallN,
    VExpr.forallN, VExpr.instL] using hout

abbrev WF.familyParamsSpine_of_constructor
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) :=
  self.toLayoutWF.familyParamsSpine_of_constructor

/-- The concrete parameter arguments also consume the exact parameter
telescope emitted in the mutual recursor type. -/
private theorem LayoutWF.generationParamsSpine
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (fieldSort : VLevel) :
    env.SpineWF U Γ
      (VExpr.forallN
        (view.generation.paramsTel.map
          (VExpr.instL
            (view.projectionLevels fieldSort levels)))
        (.sort fieldSort)) params (.sort fieldSort) := by
  have hparamsChecked := self.checkedParamsSpine henv levels hlevels
    hlevelsLength params hparamsLength paramsSpine (.sort fieldSort)
  rw [VExpr.instRev_closedN params (by trivial)] at hparamsChecked
  have hparamsChecked' : env.SpineWF U Γ
      (VExpr.forallN
        (view.generation.block.checked.params.map (VExpr.instL levels))
        (.sort fieldSort)) params (.sort fieldSort) := by
    exact hparamsChecked
  have hgenerationChecked :=
    self.generationEnv.generationParams_defeq.instL hlevels
  have hgenerationLift : VExpr.liftTelN Γ.length
      (view.generation.generatedParams.map (VExpr.instL levels)) 0 =
      view.generation.generatedParams.map (VExpr.instL levels) := by
    simpa using VEnv.OnTel.liftTelN_eq henv
      hgenerationChecked.raw_onTel (by trivial) Γ.length
  have hcheckedLift : VExpr.liftTelN Γ.length
      (view.generation.block.checked.params.map
        (VExpr.instL levels)) 0 =
      view.generation.block.checked.params.map
        (VExpr.instL levels) := by
    simpa using VEnv.OnTel.liftTelN_eq henv
      (hgenerationChecked.view_onTel henv) (by trivial) Γ.length
  have hgenerationCheckedΓ := hgenerationChecked.weakN henv
    (Ctx.LiftN.zero (n := Γ.length) (Γ := []) Γ)
  rw [hgenerationLift, hcheckedLift] at hgenerationCheckedΓ
  simp only [List.append_nil] at hgenerationCheckedΓ
  have hparamsGeneration := VEnv.TelDefEq.spine_sort henv
    hgenerationCheckedΓ hparamsChecked'
    (by simpa [self.generationEnv.generationParams_length] using
      hparamsLength)
  have hsource := view.sourceLevels_projectionLevels fieldSort levels
    hlevelsLength
  have hparamsTel :
      view.generation.paramsTel.map
          (VExpr.instL (view.projectionLevels fieldSort levels)) =
        view.generation.generatedParams.map (VExpr.instL levels) := by
    simp [BlockGenerationChecked.paramsTel, List.map_map,
      Function.comp_def, VExpr.instL_instL, hsource]
  rw [hparamsTel]
  exact hparamsGeneration

private abbrev WF.generationParamsSpine
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) := self.toLayoutWF.generationParamsSpine

/-- Specializing the selected constructor's exact field telescope at a
well-typed family parameter spine preserves its recorded field sorts. -/
theorem LayoutWF.specializedFields_onSortTel
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel)) :
    env.OnSortTel U Γ (view.specializedFields levels params)
      (view.fieldSorts.map (VLevel.inst levels)) := by
  obtain ⟨resultLevel, hspine⟩ := paramsSpine
  have hparams := self.checkedParamsSpine henv levels hlevels
    hlevelsLength params hparamsLength ⟨resultLevel, hspine⟩
    (.sort resultLevel)
  rw [VExpr.instRev_closedN params (by trivial)] at hparams
  have hfields := self.fieldTelescope.instL hlevels
  have hcheckedParams := self.parameters.instL hlevels
  have hcheckedLift : VExpr.liftTelN Γ.length
      (view.generation.block.checked.params.map (VExpr.instL levels)) 0 =
      view.generation.block.checked.params.map (VExpr.instL levels) := by
    simpa using VEnv.OnTel.liftTelN_eq henv hcheckedParams
      (by trivial) Γ.length
  have Wparams := Ctx.LiftN.consTel
    (view.generation.block.checked.params.map (VExpr.instL levels))
    (Ctx.LiftN.zero (n := Γ.length) (Γ := []) Γ)
  rw [hcheckedLift] at Wparams
  have hcheckedCtx : OnCtx
      (view.generation.block.checked.params.reverse.map
        (VExpr.instL levels)) (env.IsType U) := by
    simpa [List.map_reverse] using
      VEnv.OnTel.toOnCtx hcheckedParams (by trivial)
  have hfieldLift := VEnv.OnSortTel.liftTelN_eq henv hfields
    (VEnv.CtxWF.closed henv hcheckedCtx) Γ.length
  have hfieldsΓ := VEnv.OnSortTel.weakN henv
    (by simpa [List.map_reverse] using Wparams) hfields
  simp only [List.length_reverse, List.length_map] at hfieldLift
  rw [hfieldLift] at hfieldsΓ
  have hspecialized := VEnv.OnSortTel.instRevParams henv hparams
    (by simpa [view.checked_params_length] using hparamsLength)
    (by simpa [List.map_reverse] using hfieldsΓ)
  rw [VExpr.instRevAt_map_instL_zipIdx] at hspecialized
  simpa [specializedFields, fields] using hspecialized

abbrev WF.specializedFields_onSortTel
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) := self.toLayoutWF.specializedFields_onSortTel

/-- A mutual family's raw index telescope remains well formed after source
universe and shared-parameter specialization. -/
theorem LayoutWF.specializedIndices_onTel
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} (family : NormalizedFamily)
    (hfamily : family ∈ view.generation.families)
    (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel)) :
    env.OnTel U Γ (view.specializedIndices family levels params) := by
  have hparams := self.checkedParamsSpine henv levels hlevels
    hlevelsLength params hparamsLength paramsSpine (.sort .zero)
  rw [VExpr.instRev_closedN params (by trivial)] at hparams
  have hfamilyTel :=
    (self.generationEnv.emittedFamily_onTel hfamily).instL hlevels
  have hfamilyTel' : env.OnTel U []
      (view.generation.block.checked.params.map (VExpr.instL levels) ++
        (family.rawIndices view.nparams).map (VExpr.instL levels)) := by
    simpa [List.map_append] using hfamilyTel
  have hindices : env.OnTel U
      (view.generation.block.checked.params.map
        (VExpr.instL levels)).reverse
      ((family.rawIndices view.nparams).map (VExpr.instL levels)) := by
    simpa using (VEnv.OnTel.of_append hfamilyTel').2
  have hcheckedParams := self.parameters.instL hlevels
  have hcheckedLift : VExpr.liftTelN Γ.length
      (view.generation.block.checked.params.map (VExpr.instL levels)) 0 =
      view.generation.block.checked.params.map (VExpr.instL levels) := by
    simpa using VEnv.OnTel.liftTelN_eq henv hcheckedParams
      (by trivial) Γ.length
  have Wparams := Ctx.LiftN.consTel
    (view.generation.block.checked.params.map (VExpr.instL levels))
    (Ctx.LiftN.zero (n := Γ.length) (Γ := []) Γ)
  rw [hcheckedLift] at Wparams
  have hcheckedCtx : OnCtx
      (view.generation.block.checked.params.map
        (VExpr.instL levels)).reverse (env.IsType U) := by
    simpa [List.map_reverse] using
      VEnv.OnTel.toOnCtx hcheckedParams (by trivial)
  have hindicesLift := VEnv.OnTel.liftTelN_eq henv hindices
    (VEnv.CtxWF.closed henv hcheckedCtx) Γ.length
  have hindicesΓ := VEnv.OnTel.weakN henv
    (by simpa [List.map_reverse] using Wparams) hindices
  simp only [List.length_reverse, List.length_map] at hindicesLift
  rw [hindicesLift] at hindicesΓ
  have hspecialized := VEnv.OnTel.instRevParams henv hparams
    (by simpa [view.checked_params_length] using hparamsLength)
    (by simpa [List.map_reverse] using hindicesΓ)
  rw [VExpr.instRevAt_map_instL_zipIdx] at hspecialized
  simpa [specializedIndices] using hspecialized

abbrev WF.specializedIndices_onTel
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) := self.toLayoutWF.specializedIndices_onTel

/-- After the exact shared parameter prefix, every mutual family exposes its
specialized raw-index telescope and the common validated result sort. -/
theorem LayoutWF.familyPrefix_hasType
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} (family : NormalizedFamily)
    (hfamily : family ∈ view.generation.families)
    (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel)) :
    env.HasType U Γ
      (VExpr.appN (.const family.raw.name levels) params)
      (VExpr.forallN (view.specializedIndices family levels params)
        (.sort (view.resultLevel.inst levels))) := by
  let indices :=
    (family.rawIndices view.nparams).map (VExpr.instL levels)
  let rawResult := (family.rawResult view.nparams).instL levels
  let commonLevel := view.resultLevel.inst levels
  have hc₀ := self.generationEnv.familyConst_emitted_decl hfamily
  have hc := hc₀.instL (U' := U) hlevels
  have hlevelIdentity :
      (VLevel.params view.uvars).map (VLevel.inst levels) = levels :=
    VLevel.inst_map_id hlevelsLength
  have hcΓ : env.HasType U Γ
      (.const family.raw.name levels)
      (VExpr.forallN
        (view.generation.block.checked.params.map (VExpr.instL levels))
        (VExpr.forallN indices rawResult)) := by
    have hc' : env.HasType U []
        (.const family.raw.name levels)
        ((VExpr.forallN
          (view.generation.block.checked.params ++
            family.rawIndices view.nparams)
          (family.rawResult view.nparams)).instL levels) := by
      simpa [VExpr.instL, hlevelIdentity] using hc
    have hc'Γ : env.HasType U Γ
        (.const family.raw.name levels)
        ((VExpr.forallN
          (view.generation.block.checked.params ++
            family.rawIndices view.nparams)
          (family.rawResult view.nparams)).instL levels) :=
      hc'.weak0 henv
    simpa [indices, rawResult, VExpr.instL_forallN,
      VExpr.forallN_append, List.map_append] using hc'Γ
  have hparams := self.checkedParamsSpine henv levels hlevels
    hlevelsLength params hparamsLength paramsSpine
    (VExpr.forallN indices rawResult)
  have hprefixRaw := hparams.hasType_appN hcΓ
  have hfamilyTel :=
    (self.generationEnv.emittedFamily_onTel hfamily).instL hlevels
  have hfamilyTel' : env.OnTel U []
      (view.generation.block.checked.params.map (VExpr.instL levels) ++
        indices) := by
    simpa [indices, List.map_append] using hfamilyTel
  have hindices : env.OnTel U
      (view.generation.block.checked.params.map
        (VExpr.instL levels)).reverse indices :=
    by simpa using (VEnv.OnTel.of_append hfamilyTel').2
  have hresult₀ :=
    (self.generationEnv.familyWF family hfamily).familyResult.instL hlevels
  have hctx :=
    ((self.generationEnv.emittedFamilyTel hfamily).instL hlevels).ctx
  simp only [List.map_nil, List.map_append,
    List.append_nil] at hctx
  simp only [List.map_reverse, List.map_append, VExpr.instL] at hresult₀
  change env.IsDefEq U
      ((family.rawParams view.nparams).map (VExpr.instL levels) ++
        indices).reverse
      rawResult (.sort commonLevel) (.sort (.succ commonLevel)) at hresult₀
  change env.IsDefEqCtx U []
      ((family.rawParams view.nparams).map (VExpr.instL levels) ++
        indices).reverse
      (view.generation.block.checked.params.map (VExpr.instL levels) ++
        indices).reverse at hctx
  have hresult : env.IsDefEq U
      (indices.reverse ++
        (view.generation.block.checked.params.map
          (VExpr.instL levels)).reverse)
      rawResult (.sort commonLevel) (.sort (.succ commonLevel)) := by
    have hout := hresult₀.defeqDFC henv hctx
    simpa [indices, rawResult, commonLevel, List.map_append,
      List.map_reverse, List.reverse_append] using hout
  obtain ⟨forallSort, hforall⟩ :=
    hindices.telDefEq_refl.forallN_defeq hresult
  have hcheckedOnTel : env.OnTel U []
      (view.generation.block.checked.params.map (VExpr.instL levels)) :=
    (VEnv.OnTel.of_append hfamilyTel').1
  have hcheckedCtx : OnCtx
      (view.generation.block.checked.params.map
        (VExpr.instL levels)).reverse (env.IsType U) :=
    by simpa using VEnv.OnTel.toOnCtx hcheckedOnTel (by trivial)
  have hforallΓ := hforall.weakR henv
    (VEnv.CtxWF.closed henv hcheckedCtx) Γ
  have hparamsLength' : params.length =
      (view.generation.block.checked.params.map
        (VExpr.instL levels)).length := by
    simpa [view.checked_params_length] using hparamsLength
  have hspecializedDefEq := VEnv.SpineWF.instRev_defeq henv hparams
    hparamsLength' hforallΓ
  have hsortInst : (VExpr.sort forallSort).instRev params =
      .sort forallSort := VExpr.instRev_closedN params (by trivial)
  rw [hsortInst] at hspecializedDefEq
  have hspecializedDefEq' : env.IsDefEq U Γ
      ((VExpr.forallN indices rawResult).instRev params)
      ((VExpr.forallN indices (.sort commonLevel)).instRev params)
      (.sort forallSort) := by
    simpa using hspecializedDefEq
  have hprefix := hspecializedDefEq'.defeq hprefixRaw
  rw [VExpr.instRev_forallN_projection] at hprefix
  rw [VExpr.instRevAt_closedN params (by trivial)] at hprefix
  simpa [indices, commonLevel, specializedIndices,
    VExpr.instRev_forallN_projection,
    VExpr.instRevAt_map_instL_zipIdx] using hprefix

abbrev WF.familyPrefix_hasType
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) := self.toLayoutWF.familyPrefix_hasType

/-- A nonselected-family dummy motive has the exact mutual motive type at
the selected field universe. -/
theorem WF.identityMotive_hasType
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} (family : NormalizedFamily)
    (hfamily : family ∈ view.generation.families)
    (fieldSort : VLevel) (hfieldSort : fieldSort.WF U)
    (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel)) :
    env.HasType U Γ (view.identityMotive family fieldSort levels params)
      (VExpr.forallN (view.specializedIndices family levels params)
        (.forallE
          (VExpr.appN (.const family.raw.name levels)
            (params.map (VExpr.liftN
              (view.specializedIndices family levels params).length) ++
              VExpr.bvarRevRange 0
                (view.specializedIndices family levels params).length))
          (.sort fieldSort))) := by
  let indices := view.specializedIndices family levels params
  let m := indices.length
  let familyApp := VExpr.appN (.const family.raw.name levels)
    (params.map (VExpr.liftN m) ++ VExpr.bvarRevRange 0 m)
  have hindices := self.specializedIndices_onTel henv family hfamily
    levels hlevels hlevelsLength params hparamsLength paramsSpine
  have hprefix := self.familyPrefix_hasType henv family hfamily levels
    hlevels hlevelsLength params hparamsLength paramsSpine
  have hprefixWeak := hprefix.weakN henv
    (Ctx.LiftN.zero (n := m) (Γ := Γ) indices.reverse
      (h := by simp [m]))
  have hprefixSelf : env.HasType U
      (([] : List VExpr) ++ indices.reverse ++ Γ)
      ((VExpr.appN (.const family.raw.name levels) params).liftN m)
      ((VExpr.forallN indices (.sort (view.resultLevel.inst levels))).liftN
        (([] : List VExpr).length + indices.length)) := by
    simpa [m, indices] using hprefixWeak
  have hfamilyApp₀ := VEnv.HasType.appN_selfSpine
    (env := env) (U := U) (As := indices)
    (B := .sort (view.resultLevel.inst levels))
    (Δ := []) (Γ := Γ)
    (f := (VExpr.appN (.const family.raw.name levels) params).liftN m)
    hprefixSelf
  have hfamilyApp : env.HasType U (indices.reverse ++ Γ)
      familyApp (.sort (view.resultLevel.inst levels)) := by
    simpa [familyApp, m, VExpr.liftN_appN, VExpr.appN_append,
      List.map_map, Function.comp_def, VExpr.liftN] using hfamilyApp₀
  have hpunit : env.HasType U
      (familyApp :: indices.reverse ++ Γ)
      (.const ``PUnit [fieldSort]) (.sort fieldSort) := by
    have hout := VEnv.HasType.const
      (Γ := familyApp :: indices.reverse ++ Γ)
      (c := ``PUnit) (ls := [fieldSort])
      (self.punitRegistered.type) (by simpa) (by simp)
    simpa [VExpr.instL, VLevel.inst,
      List.getD_eq_getElem?_getD] using (hout : env.HasType U
      (familyApp :: indices.reverse ++ Γ)
      (.const ``PUnit [fieldSort]) _)
  have hidentityBody : env.HasType U (indices.reverse ++ Γ)
      (.lam familyApp (.const ``PUnit [fieldSort]))
      (.forallE familyApp (.sort fieldSort)) :=
    hfamilyApp.lam hpunit
  have hout := VEnv.HasType.lamN hindices hidentityBody
  simpa [identityMotive, indices, m, familyApp] using hout

/-- A nonselected-family motive can use any ambient type at the selected
field universe; no prelude declaration is required. -/
theorem LayoutWF.identityMotiveWith_hasType
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} (family : NormalizedFamily)
    (hfamily : family ∈ view.generation.families)
    (fieldSort : VLevel) (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (dummyType : VExpr)
    (dummyTypeType : env.HasType U Γ dummyType (.sort fieldSort)) :
    env.HasType U Γ
      (view.identityMotiveWith family levels params dummyType)
      (VExpr.forallN (view.specializedIndices family levels params)
        (.forallE
          (VExpr.appN (.const family.raw.name levels)
            (params.map (VExpr.liftN
              (view.specializedIndices family levels params).length) ++
              VExpr.bvarRevRange 0
                (view.specializedIndices family levels params).length))
          (.sort fieldSort))) := by
  let indices := view.specializedIndices family levels params
  let m := indices.length
  let familyApp := VExpr.appN (.const family.raw.name levels)
    (params.map (VExpr.liftN m) ++ VExpr.bvarRevRange 0 m)
  have hindices := self.specializedIndices_onTel henv family hfamily
    levels hlevels hlevelsLength params hparamsLength paramsSpine
  have hprefix := self.familyPrefix_hasType henv family hfamily levels
    hlevels hlevelsLength params hparamsLength paramsSpine
  have hprefixWeak := hprefix.weakN henv
    (Ctx.LiftN.zero (n := m) (Γ := Γ) indices.reverse
      (h := by simp [m]))
  have hprefixSelf : env.HasType U
      (([] : List VExpr) ++ indices.reverse ++ Γ)
      ((VExpr.appN (.const family.raw.name levels) params).liftN m)
      ((VExpr.forallN indices (.sort (view.resultLevel.inst levels))).liftN
        (([] : List VExpr).length + indices.length)) := by
    simpa [m, indices] using hprefixWeak
  have hfamilyApp₀ := VEnv.HasType.appN_selfSpine
    (env := env) (U := U) (As := indices)
    (B := .sort (view.resultLevel.inst levels))
    (Δ := []) (Γ := Γ)
    (f := (VExpr.appN (.const family.raw.name levels) params).liftN m)
    hprefixSelf
  have hfamilyApp : env.HasType U (indices.reverse ++ Γ)
      familyApp (.sort (view.resultLevel.inst levels)) := by
    simpa [familyApp, m, VExpr.liftN_appN, VExpr.appN_append,
      List.map_map, Function.comp_def, VExpr.liftN] using hfamilyApp₀
  have hdummy : env.HasType U (familyApp :: indices.reverse ++ Γ)
      (dummyType.liftN (m + 1)) (.sort fieldSort) := by
    have hout := dummyTypeType.weakN henv
      (Ctx.LiftN.zero (n := m + 1) (Γ := Γ)
        (familyApp :: indices.reverse) (h := by simp [m]))
    simpa [m, VExpr.liftN] using hout
  have hidentityBody : env.HasType U (indices.reverse ++ Γ)
      (.lam familyApp (dummyType.liftN (m + 1)))
      (.forallE familyApp (.sort fieldSort)) :=
    hfamilyApp.lam hdummy
  have hout := VEnv.HasType.lamN hindices hidentityBody
  simpa [identityMotiveWith, indices, m, familyApp] using hout

/-- Every family-order motive supplied to the block recursor has its exact
specialized generated motive domain. -/
theorem WF.projectionMotive_hasType
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} (family : NormalizedFamily)
    (hfamily : family ∈ view.generation.families)
    (fieldSort : VLevel) (hfieldSort : fieldSort.WF U)
    (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (typeFn : VExpr)
    (typeFnType : env.HasType U Γ typeFn
      (.forallE (view.structureType levels params) (.sort fieldSort))) :
    env.HasType U Γ
      (if family.view.ordinal = view.family.view.ordinal then typeFn
        else view.identityMotive family fieldSort levels params)
      (view.projectionMotiveType family fieldSort levels params) := by
  by_cases selected : family.view.ordinal = view.family.view.ordinal
  · have hfamilyAt := view.generation.family_getElem?_ordinal hfamily
    rw [selected] at hfamilyAt
    have hviewAt :=
      view.generation.family_getElem?_ordinal view.family_mem
    have familyEq : family = view.family :=
      Option.some.inj (hfamilyAt.symm.trans hviewAt)
    subst family
    simpa [selected, projectionMotiveType, structureType,
      VExpr.forallN, VExpr.bvarRevRange] using typeFnType
  · simp only [selected, ↓reduceIte]
    simpa [projectionMotiveType] using
      self.identityMotive_hasType henv family hfamily fieldSort hfieldSort
        levels hlevels hlevelsLength params hparamsLength paramsSpine

private theorem WF.projectionMotives_forall₂_hasType
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr}
    (fieldSort : VLevel) (hfieldSort : fieldSort.WF U)
    (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (typeFn : VExpr)
    (typeFnType : env.HasType U Γ typeFn
      (.forallE (view.structureType levels params) (.sort fieldSort))) :
    List.Forall₂ (fun motive motiveType =>
      env.HasType U Γ motive motiveType)
      (view.projectionMotives levels params fieldSort typeFn)
      (view.projectionMotiveTypes fieldSort levels params) := by
  unfold projectionMotives projectionMotiveTypes
  have aux : ∀ (families : List NormalizedFamily),
      (∀ family ∈ families, family ∈ view.generation.families) →
      List.Forall₂ (fun motive motiveType =>
        env.HasType U Γ motive motiveType)
        (families.map fun family =>
          if family.view.ordinal = view.family.view.ordinal then typeFn
          else view.identityMotive family fieldSort levels params)
        (families.map fun family =>
          view.projectionMotiveType family fieldSort levels params) := by
    intro families hsub
    induction families with
    | nil => exact .nil
    | cons family families ih =>
        exact .cons
          (self.projectionMotive_hasType henv family
            (hsub family (.head _)) fieldSort hfieldSort levels hlevels
            hlevelsLength params hparamsLength paramsSpine typeFn typeFnType)
          (ih (fun family hfamily => hsub family (.tail _ hfamily)))
  exact aux view.generation.families (fun _ member => member)

/-- The concrete mutual motives consume their fully specialized generated
telescope, leaving the supplied tail specialized by all motives. -/
private theorem WF.projectionMotivesSpine
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr}
    (fieldSort : VLevel) (hfieldSort : fieldSort.WF U)
    (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (typeFn : VExpr)
    (typeFnType : env.HasType U Γ typeFn
      (.forallE (view.structureType levels params) (.sort fieldSort)))
    (tail : VExpr) :
    env.SpineWF U Γ
      (VExpr.forallN
        ((view.projectionMotiveTypes fieldSort levels params).zipIdx.map
          fun entry => entry.1.liftN entry.2) tail)
      (view.projectionMotives levels params fieldSort typeFn)
      (tail.instRev
        (view.projectionMotives levels params fieldSort typeFn)) := by
  rw [← progressiveTypesAux_eq_zipIdx]
  exact VEnv.SpineWF.of_progressive
    (self.projectionMotives_forall₂_hasType henv fieldSort hfieldSort
      levels hlevels hlevelsLength params hparamsLength paramsSpine
      typeFn typeFnType)

/-- Applying the registered mutual recursor through its parameters and every
concrete motive exposes the exact progressive flattened-minor telescope.
The final family-major cursor is intentionally existential here: minor
well-formedness depends only on the telescope domains. -/
private theorem WF.projectionMotivesRecursorSpine
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr}
    (fieldSort : VLevel) (hfieldSort : fieldSort.WF U)
    (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (typeFn : VExpr)
    (typeFnType : env.HasType U Γ typeFn
      (.forallE (view.structureType levels params) (.sort fieldSort)))
    (hmotiveLevel : view.generation.motiveLevel.inst
      (view.projectionLevels fieldSort levels) = fieldSort) :
    ∃ tail, env.SpineWF U Γ
      ((view.generation.recType view.family).instL
        (view.projectionLevels fieldSort levels))
      (params ++ view.projectionMotives levels params fieldSort typeFn)
      (VExpr.forallN
        ((view.projectionMinorTypes fieldSort levels params
          (view.projectionMotives levels params fieldSort typeFn)).zipIdx.map
            fun entry => entry.1.liftN entry.2)
        tail) := by
  let gen := view.generation
  let pLevels := view.projectionLevels fieldSort levels
  let d := gen.familyCount
  let k := gen.minorCount
  let indices := gen.idxTel view.family
  let ni := indices.length
  let majorTail : VExpr :=
    VExpr.forallN (VExpr.liftTelN (d + k) indices 0) <|
      .forallE
        (VExpr.appN (.const view.family.raw.name gen.sourceLevels)
          (VExpr.bvarRevRange (ni + d + k) view.nparams ++
            VExpr.bvarRevRange 0 ni))
        (.app
          (VExpr.appN
            (.bvar (d - 1 - view.family.view.ordinal + k + ni + 1))
            (VExpr.bvarRevRange 1 ni))
          (.bvar 0))
  let minorTail := VExpr.forallN gen.minorTypes majorTail
  let motiveTail := VExpr.forallN gen.motiveTypes minorTail
  have hparams := self.generationParamsSpine henv levels hlevels
    hlevelsLength params hparamsLength paramsSpine fieldSort
  have hparamsTelLength : params.length =
      (gen.paramsTel.map (VExpr.instL pLevels)).length := by
    simp [gen, pLevels, BlockGenerationChecked.paramsTel,
      self.generationEnv.generationParams_length, hparamsLength]
  have hparamsFull₀ := hparams.retarget hparamsTelLength
    (motiveTail.instL pLevels)
  have hrecShape : gen.recType view.family =
      VExpr.forallN gen.paramsTel motiveTail := by
    rfl
  have hparamsFull : env.SpineWF U Γ
      ((gen.recType view.family).instL pLevels) params
      ((motiveTail.instL pLevels).instRev params) := by
    rw [hrecShape]
    simpa [VExpr.instL_forallN] using hparamsFull₀
  let afterParams := (minorTail.instL pLevels).instRevAt params d
  have hmotiveShape :
      (motiveTail.instL pLevels).instRev params =
        VExpr.forallN
          ((view.projectionMotiveTypes fieldSort levels params).zipIdx.map
            fun entry => entry.1.liftN entry.2)
          afterParams := by
    simp only [motiveTail, VExpr.instL_forallN,
      VExpr.instRev_forallN_projection]
    rw [view.motiveTypes_specialize fieldSort levels hlevelsLength params
      hparamsLength hmotiveLevel]
    simp [afterParams, d, gen, view.generation.motiveTypes_length]
  rw [hmotiveShape] at hparamsFull
  have hmotives := self.projectionMotivesSpine henv fieldSort hfieldSort
    levels hlevels hlevelsLength params hparamsLength paramsSpine typeFn
    typeFnType afterParams
  have hfull := hparamsFull.append hmotives
  unfold afterParams minorTail at hfull
  simp only [VExpr.instL_forallN,
    VExpr.instRevAt_forallN_projection,
    VExpr.instRev_forallN_projection] at hfull
  rw [view.minorTypes_specialize fieldSort levels params
    (view.projectionMotives levels params fieldSort typeFn)] at hfull
  exact ⟨_, by simpa [gen, pLevels, List.append_assoc] using hfull⟩

/-- Each family-order motive is well typed when nonselected families share
an explicit ambient dummy type. -/
theorem LayoutWF.projectionMotiveWith_hasType
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} (family : NormalizedFamily)
    (hfamily : family ∈ view.generation.families)
    (fieldSort : VLevel) (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (typeFn dummyType : VExpr)
    (typeFnType : env.HasType U Γ typeFn
      (.forallE (view.structureType levels params) (.sort fieldSort)))
    (dummyTypeType : env.HasType U Γ dummyType (.sort fieldSort)) :
    env.HasType U Γ
      (if family.view.ordinal = view.family.view.ordinal then typeFn
        else view.identityMotiveWith family levels params dummyType)
      (view.projectionMotiveType family fieldSort levels params) := by
  by_cases selected : family.view.ordinal = view.family.view.ordinal
  · have hfamilyAt := view.generation.family_getElem?_ordinal hfamily
    rw [selected] at hfamilyAt
    have hviewAt :=
      view.generation.family_getElem?_ordinal view.family_mem
    have familyEq : family = view.family :=
      Option.some.inj (hfamilyAt.symm.trans hviewAt)
    subst family
    simpa [selected, projectionMotiveType, structureType,
      VExpr.forallN, VExpr.bvarRevRange] using typeFnType
  · simp only [selected, ↓reduceIte]
    simpa [projectionMotiveType] using
      self.identityMotiveWith_hasType henv family hfamily fieldSort levels
        hlevels hlevelsLength params hparamsLength paramsSpine dummyType
        dummyTypeType

private theorem LayoutWF.projectionMotivesWith_forall₂_hasType
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr}
    (fieldSort : VLevel) (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (typeFn dummyType : VExpr)
    (typeFnType : env.HasType U Γ typeFn
      (.forallE (view.structureType levels params) (.sort fieldSort)))
    (dummyTypeType : env.HasType U Γ dummyType (.sort fieldSort)) :
    List.Forall₂ (fun motive motiveType =>
      env.HasType U Γ motive motiveType)
      (view.projectionMotivesWith levels params typeFn dummyType)
      (view.projectionMotiveTypes fieldSort levels params) := by
  unfold projectionMotivesWith projectionMotiveTypes
  have aux : ∀ (families : List NormalizedFamily),
      (∀ family ∈ families, family ∈ view.generation.families) →
      List.Forall₂ (fun motive motiveType =>
        env.HasType U Γ motive motiveType)
        (families.map fun family =>
          if family.view.ordinal = view.family.view.ordinal then typeFn
          else view.identityMotiveWith family levels params dummyType)
        (families.map fun family =>
          view.projectionMotiveType family fieldSort levels params) := by
    intro families hsub
    induction families with
    | nil => exact .nil
    | cons family families ih =>
        exact .cons
          (self.projectionMotiveWith_hasType henv family
            (hsub family (.head _)) fieldSort levels hlevels
            hlevelsLength params hparamsLength paramsSpine typeFn dummyType
            typeFnType dummyTypeType)
          (ih (fun family hfamily => hsub family (.tail _ hfamily)))
  exact aux view.generation.families (fun _ member => member)

private theorem LayoutWF.projectionMotivesWithSpine
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr}
    (fieldSort : VLevel) (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (typeFn dummyType : VExpr)
    (typeFnType : env.HasType U Γ typeFn
      (.forallE (view.structureType levels params) (.sort fieldSort)))
    (dummyTypeType : env.HasType U Γ dummyType (.sort fieldSort))
    (tail : VExpr) :
    env.SpineWF U Γ
      (VExpr.forallN
        ((view.projectionMotiveTypes fieldSort levels params).zipIdx.map
          fun entry => entry.1.liftN entry.2) tail)
      (view.projectionMotivesWith levels params typeFn dummyType)
      (tail.instRev
        (view.projectionMotivesWith levels params typeFn dummyType)) := by
  rw [← progressiveTypesAux_eq_zipIdx]
  exact VEnv.SpineWF.of_progressive
    (self.projectionMotivesWith_forall₂_hasType henv fieldSort levels
      hlevels hlevelsLength params hparamsLength paramsSpine typeFn
      dummyType typeFnType dummyTypeType)

private theorem LayoutWF.projectionMotivesWithRecursorSpine
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr}
    (fieldSort : VLevel) (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (typeFn dummyType : VExpr)
    (typeFnType : env.HasType U Γ typeFn
      (.forallE (view.structureType levels params) (.sort fieldSort)))
    (dummyTypeType : env.HasType U Γ dummyType (.sort fieldSort))
    (hmotiveLevel : view.generation.motiveLevel.inst
      (view.projectionLevels fieldSort levels) = fieldSort) :
    ∃ tail, env.SpineWF U Γ
      ((view.generation.recType view.family).instL
        (view.projectionLevels fieldSort levels))
      (params ++ view.projectionMotivesWith levels params typeFn dummyType)
      (VExpr.forallN
        ((view.projectionMinorTypes fieldSort levels params
          (view.projectionMotivesWith levels params typeFn dummyType)).zipIdx.map
            fun entry => entry.1.liftN entry.2)
        tail) := by
  let gen := view.generation
  let pLevels := view.projectionLevels fieldSort levels
  let d := gen.familyCount
  let k := gen.minorCount
  let indices := gen.idxTel view.family
  let ni := indices.length
  let majorTail : VExpr :=
    VExpr.forallN (VExpr.liftTelN (d + k) indices 0) <|
      .forallE
        (VExpr.appN (.const view.family.raw.name gen.sourceLevels)
          (VExpr.bvarRevRange (ni + d + k) view.nparams ++
            VExpr.bvarRevRange 0 ni))
        (.app
          (VExpr.appN
            (.bvar (d - 1 - view.family.view.ordinal + k + ni + 1))
            (VExpr.bvarRevRange 1 ni))
          (.bvar 0))
  let minorTail := VExpr.forallN gen.minorTypes majorTail
  let motiveTail := VExpr.forallN gen.motiveTypes minorTail
  have hparams := self.generationParamsSpine henv levels hlevels
    hlevelsLength params hparamsLength paramsSpine fieldSort
  have hparamsTelLength : params.length =
      (gen.paramsTel.map (VExpr.instL pLevels)).length := by
    simp [gen, pLevels, BlockGenerationChecked.paramsTel,
      self.generationEnv.generationParams_length, hparamsLength]
  have hparamsFull₀ := hparams.retarget hparamsTelLength
    (motiveTail.instL pLevels)
  have hrecShape : gen.recType view.family =
      VExpr.forallN gen.paramsTel motiveTail := by
    rfl
  have hparamsFull : env.SpineWF U Γ
      ((gen.recType view.family).instL pLevels) params
      ((motiveTail.instL pLevels).instRev params) := by
    rw [hrecShape]
    simpa [VExpr.instL_forallN] using hparamsFull₀
  let afterParams := (minorTail.instL pLevels).instRevAt params d
  have hmotiveShape :
      (motiveTail.instL pLevels).instRev params =
        VExpr.forallN
          ((view.projectionMotiveTypes fieldSort levels params).zipIdx.map
            fun entry => entry.1.liftN entry.2)
          afterParams := by
    simp only [motiveTail, VExpr.instL_forallN,
      VExpr.instRev_forallN_projection]
    rw [view.motiveTypes_specialize fieldSort levels hlevelsLength params
      hparamsLength hmotiveLevel]
    simp [afterParams, d, gen, view.generation.motiveTypes_length]
  rw [hmotiveShape] at hparamsFull
  have hmotives := self.projectionMotivesWithSpine henv fieldSort levels
    hlevels hlevelsLength params hparamsLength paramsSpine typeFn dummyType
    typeFnType dummyTypeType afterParams
  have hfull := hparamsFull.append hmotives
  unfold afterParams minorTail at hfull
  simp only [VExpr.instL_forallN,
    VExpr.instRevAt_forallN_projection,
    VExpr.instRev_forallN_projection] at hfull
  rw [view.minorTypes_specialize fieldSort levels params
    (view.projectionMotivesWith levels params typeFn dummyType)] at hfull
  exact ⟨_, by simpa [gen, pLevels, List.append_assoc] using hfull⟩

/-- The selected mutual constructor, after the exact common parameter
prefix, has the canonical specialized field telescope and returns the
selected family application. -/
theorem LayoutWF.constructorPrefix_hasType
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel)) :
    env.HasType U Γ
      (VExpr.appN (.const view.constructorName levels) params)
      (VExpr.forallN (view.specializedFields levels params)
        ((view.structureType levels params).liftN
          (view.specializedFields levels params).length)) := by
  let constructor := view.blockConstructor
  let E := NormalizedBlockCtor.emittedBinders view.generation constructor
  have hcE₀ := self.generationEnv.ctorConst_emitted_decl
    view.blockConstructor_mem
  have hcE := hcE₀.instL (U' := U) hlevels
  have hlevelIdentity :
      (VLevel.params view.uvars).map (VLevel.inst levels) = levels :=
    VLevel.inst_map_id hlevelsLength
  have hcE' : env.HasType U []
      (.const view.constructorName levels)
      ((VExpr.forallN E
        (NormalizedBlockCtor.resultTarget view.generation constructor)).instL
          levels) := by
    simpa [constructor, E, blockConstructor, VExpr.instL,
      hlevelIdentity] using hcE
  have hcEΓ : env.HasType U Γ
      (.const view.constructorName levels)
      ((VExpr.forallN E
        (NormalizedBlockCtor.resultTarget view.generation constructor)).instL
          levels) :=
    hcE'.weak0 henv
  let htarget : VExpr :=
    VExpr.forallN
      (view.fields.map (VExpr.instL levels))
      ((NormalizedBlockCtor.resultTarget view.generation constructor).instL
        levels)
  have hparams := self.checkedParamsSpine henv levels hlevels
    hlevelsLength params hparamsLength paramsSpine htarget
  have hcEΓ' : env.HasType U Γ
      (.const view.constructorName levels)
      (VExpr.forallN
        (view.generation.block.checked.params.map (VExpr.instL levels))
        htarget) := by
    simpa [E, htarget, constructor, fields, blockConstructor,
      NormalizedBlockCtor.emittedBinders, VExpr.instL_forallN,
      VExpr.forallN_append, List.map_append] using hcEΓ
  have hprefix := hparams.hasType_appN hcEΓ'
  have hprefix' : env.HasType U Γ
      (VExpr.appN (.const view.constructorName levels) params)
      (VExpr.forallN (view.specializedFields levels params)
        ((NormalizedBlockCtor.resultTarget view.generation constructor).instL
          levels |>.instRevAt params view.fields.length)) := by
    simpa [htarget, VExpr.instRev_forallN_projection,
      specializedFields, VExpr.instRevAt_map_instL_zipIdx] using hprefix
  have hparamsRange :
      (VExpr.bvarRevRange view.fields.length view.nparams).map
          (fun expression => expression.instRevAt params view.fields.length) =
        params.map (VExpr.liftN view.fields.length) := by
    have h := VExpr.map_instRevAt_bvarRevRange params view.fields.length
    rw [hparamsLength] at h
    exact h
  have hresultIndices : view.constructor.view.resultIndices = [] := by
    apply List.length_eq_zero_iff.1
    have hlength : view.constructor.view.resultIndices.length =
        view.family.view.indices.length := by
      simpa [blockConstructor] using
        self.generationEnv.viewResultIndices_length
          view.blockConstructor_mem
    rw [hlength, view.checked_indices_eq]
    rfl
  have htail :
      ((NormalizedBlockCtor.resultTarget view.generation constructor).instL
        levels |>.instRevAt params view.fields.length) =
        (view.structureType levels params).liftN view.fields.length := by
    rw [NormalizedBlockCtor.resultTarget, VExpr.instL_appN,
      VExpr.instRevAt_appN_projection]
    rw [VExpr.instRevAt_closedN params (by trivial)]
    dsimp only [constructor, blockConstructor]
    rw [hresultIndices]
    simp only [List.append_nil, VExpr.instL]
    rw [hlevelIdentity]
    rw [VExpr.bvarRevRange_map_instL]
    rw [structureType, VExpr.liftN_appN]
    simp only [VExpr.liftN]
    change VExpr.appN (.const view.name levels)
        ((VExpr.bvarRevRange view.fields.length view.nparams).map
          (fun expression =>
            expression.instRevAt params view.fields.length)) =
      VExpr.appN (.const view.name levels)
        (params.map (VExpr.liftN view.fields.length))
    rw [hparamsRange]
  rw [htail] at hprefix'
  simpa [specializedFields, fields] using hprefix'

abbrev WF.constructorPrefix_hasType
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) := self.toLayoutWF.constructorPrefix_hasType

/-- Checked mutual-constructor generation and certified block-backed
projector programs derive the rule-independent reconstruction obligation. -/
theorem WF.toRebuildWF_of_programs
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) (henv : env.ConversionRegular)
    (programs : view.ProgramsWF env) : view.RebuildWF env := by
  intro U Γ levels params major hΓ hlevels hlevelsLength
    hparamsLength hparamsSpine hmajor
  exact programs.etaRebuild_hasType_of_constructorPrefix henv hΓ hlevels
    hlevelsLength hparamsLength hparamsSpine hmajor
    (self.constructorPrefix_hasType henv.ordered levels hlevels
      hlevelsLength params hparamsLength hparamsSpine)

/-- Every selected raw field is closed at its exact parameter-and-field
position. -/
theorem LayoutWF.field_closed {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) {i : Nat} {field : VExpr}
    (hfield : view.fields[i]? = some field) :
    field.ClosedN (view.nparams + i) := by
  have hparamsCtx : OnCtx
      view.generation.block.checked.params.reverse
      (env.IsType view.uvars) :=
    by simpa using VEnv.OnTel.toOnCtx self.parameters (by trivial)
  have hclosed := VEnv.OnSortTel.closedAt self.generationEnv.ord
    self.fieldTelescope
    (VEnv.CtxWF.closed self.generationEnv.ord hparamsCtx) hfield
  simpa [view.checked_params_length] using hclosed

/-- Every raw index binder of every retained block family is closed at its
exact shared-parameter-and-index position. -/
theorem ProjectionSyntaxWF.familyIndex_closed
    {view : VBlockStructureView} {env : VEnv}
    (self : view.ProjectionSyntaxWF env) {family : NormalizedFamily}
    (hfamily : family ∈ view.generation.families)
    {i : Nat} {index : VExpr}
    (hindex : (family.rawIndices view.nparams)[i]? = some index) :
    index.ClosedN (view.nparams + i) := by
  have htel := self.generationEnv.rawFamily_onTel hfamily
  have hparams := (VEnv.OnTel.of_append
    (As := family.rawParams view.nparams) htel).1
  have hindices := (VEnv.OnTel.of_append
    (As := family.rawParams view.nparams) htel).2
  have hparamsCtx : OnCtx
      (family.rawParams view.nparams).reverse
      (env.IsType view.uvars) :=
    by simpa using VEnv.OnTel.toOnCtx hparams (by trivial)
  have hclosed := VEnv.OnTel.closedAt self.generationEnv.ord hindices
    (by simpa using
      VEnv.CtxWF.closed self.generationEnv.ord hparamsCtx) hindex
  have hparamsLength :
      (family.rawParams view.nparams).length = view.nparams :=
    (view.generation.shape.2.2.2.2 family hfamily).2.2.1
  simpa [hparamsLength] using hclosed

/-- Every raw field binder of every retained flattened constructor is closed
at its exact shared-parameter-and-field position. -/
theorem ProjectionSyntaxWF.constructorField_closed
    {view : VBlockStructureView} {env : VEnv}
    (self : view.ProjectionSyntaxWF env) {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ view.generation.flatCtors)
    {i : Nat} {field : VExpr}
    (hfield : (constructor.ctor.rawFields view.nparams)[i]? = some field) :
    field.ClosedN (view.nparams + i) := by
  have hemitted : env.OnTel view.uvars []
      (view.generation.block.checked.params ++
        constructor.ctor.rawFields view.nparams) := by
    simpa [NormalizedBlockCtor.emittedBinders] using
      (self.generationEnv.ctorWF constructor hconstructor).rawEmitted_onTel
  have hfields := (VEnv.OnTel.of_append
    (As := view.generation.block.checked.params) hemitted).2
  have hparamsCtx : OnCtx
      view.generation.block.checked.params.reverse
      (env.IsType view.uvars) :=
    by simpa using VEnv.OnTel.toOnCtx self.parameters (by trivial)
  have hclosed := VEnv.OnTel.closedAt self.generationEnv.ord hfields
    (by simpa using
      VEnv.CtxWF.closed self.generationEnv.ord hparamsCtx) hfield
  simpa [view.checked_params_length] using hclosed

theorem ProjectionSyntaxWF.specializedFields_liftN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.ProjectionSyntaxWF env) (levels : List VLevel)
    (params : List VExpr)
    (hparams : params.length = view.nparams) (n k : Nat) :
    view.specializedFields levels
        (params.map fun param => param.liftN n k) =
      VExpr.liftTelN n (view.specializedFields levels params) k := by
  simpa [specializedFields] using
    VStructureView.specializedFieldsAux_liftN view.fields levels params
      view.nparams 0 n k hparams
      (fun j field hfield => by
        simpa [VBlockStructureView.fields, blockConstructor] using
          self.constructorField_closed view.blockConstructor_mem hfield)

theorem ProjectionSyntaxWF.specializedFields_instN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.ProjectionSyntaxWF env) (levels : List VLevel)
    (params : List VExpr)
    (hparams : params.length = view.nparams) (a : VExpr) (k : Nat) :
    view.specializedFields levels
        (params.map fun param => param.inst a k) =
      VExpr.instTelN a (view.specializedFields levels params) k := by
  simpa [specializedFields] using
    VStructureView.specializedFieldsAux_instN view.fields levels params
      view.nparams 0 k a hparams
      (fun j field hfield => by
        simpa [VBlockStructureView.fields, blockConstructor] using
          self.constructorField_closed view.blockConstructor_mem hfield)

theorem ProjectionSyntaxWF.specializedIndices_liftN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.ProjectionSyntaxWF env) {family : NormalizedFamily}
    (hfamily : family ∈ view.generation.families)
    (levels : List VLevel) (params : List VExpr)
    (hparams : params.length = view.nparams) (n k : Nat) :
    view.specializedIndices family levels
        (params.map fun param => param.liftN n k) =
      VExpr.liftTelN n (view.specializedIndices family levels params) k := by
  simpa [specializedIndices] using
    VStructureView.specializedFieldsAux_liftN
      (family.rawIndices view.nparams) levels params view.nparams
      0 n k hparams
      (fun j index hindex => by
        simpa using self.familyIndex_closed hfamily hindex)

theorem ProjectionSyntaxWF.specializedIndices_instN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.ProjectionSyntaxWF env) {family : NormalizedFamily}
    (hfamily : family ∈ view.generation.families)
    (levels : List VLevel) (params : List VExpr)
    (hparams : params.length = view.nparams) (a : VExpr) (k : Nat) :
    view.specializedIndices family levels
        (params.map fun param => param.inst a k) =
      VExpr.instTelN a (view.specializedIndices family levels params) k := by
  simpa [specializedIndices] using
    VStructureView.specializedFieldsAux_instN
      (family.rawIndices view.nparams) levels params view.nparams
      0 k a hparams
      (fun j index hindex => by
        simpa using self.familyIndex_closed hfamily hindex)

theorem ProjectionSyntaxWF.specializedCtorFields_liftN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.ProjectionSyntaxWF env) {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ view.generation.flatCtors)
    (levels : List VLevel) (params : List VExpr)
    (hparams : params.length = view.nparams) (n k : Nat) :
    view.specializedCtorFields constructor levels
        (params.map fun param => param.liftN n k) =
      VExpr.liftTelN n
        (view.specializedCtorFields constructor levels params) k := by
  simpa [specializedCtorFields] using
    VStructureView.specializedFieldsAux_liftN
      (constructor.ctor.rawFields view.nparams) levels params view.nparams
      0 n k hparams
      (fun j field hfield => by
        simpa using self.constructorField_closed hconstructor hfield)

theorem ProjectionSyntaxWF.specializedCtorFields_instN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.ProjectionSyntaxWF env) {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ view.generation.flatCtors)
    (levels : List VLevel) (params : List VExpr)
    (hparams : params.length = view.nparams) (a : VExpr) (k : Nat) :
    view.specializedCtorFields constructor levels
        (params.map fun param => param.inst a k) =
      VExpr.instTelN a
        (view.specializedCtorFields constructor levels params) k := by
  simpa [specializedCtorFields] using
    VStructureView.specializedFieldsAux_instN
      (constructor.ctor.rawFields view.nparams) levels params view.nparams
      0 k a hparams
      (fun j field hfield => by
        simpa using self.constructorField_closed hconstructor hfield)

/- Compatibility projections for semantic layouts.  The code equations now
live on `ProjectionSyntaxWF`; existing typing proofs retain their familiar
layout-facing method names. -/
abbrev LayoutWF.familyIndex_closed
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) {family : NormalizedFamily}
    (hfamily : family ∈ view.generation.families)
    {i : Nat} {index : VExpr}
    (hindex : (family.rawIndices view.nparams)[i]? = some index) :
    index.ClosedN (view.nparams + i) :=
  self.toProjectionSyntaxWF.familyIndex_closed hfamily hindex

abbrev LayoutWF.constructorField_closed
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ view.generation.flatCtors)
    {i : Nat} {field : VExpr}
    (hfield : (constructor.ctor.rawFields view.nparams)[i]? = some field) :
    field.ClosedN (view.nparams + i) :=
  self.toProjectionSyntaxWF.constructorField_closed hconstructor hfield

abbrev LayoutWF.specializedFields_liftN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) :=
  self.toProjectionSyntaxWF.specializedFields_liftN

abbrev LayoutWF.specializedFields_instN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) :=
  self.toProjectionSyntaxWF.specializedFields_instN

abbrev LayoutWF.specializedIndices_liftN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) {family : NormalizedFamily}
    (hfamily : family ∈ view.generation.families)
    (levels : List VLevel) (params : List VExpr)
    (hparams : params.length = view.nparams) (n k : Nat) :
    view.specializedIndices family levels
        (params.map fun param => param.liftN n k) =
      VExpr.liftTelN n (view.specializedIndices family levels params) k :=
  self.toProjectionSyntaxWF.specializedIndices_liftN hfamily levels params
    hparams n k

abbrev LayoutWF.specializedIndices_instN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) {family : NormalizedFamily}
    (hfamily : family ∈ view.generation.families)
    (levels : List VLevel) (params : List VExpr)
    (hparams : params.length = view.nparams) (a : VExpr) (k : Nat) :
    view.specializedIndices family levels
        (params.map fun param => param.inst a k) =
      VExpr.instTelN a (view.specializedIndices family levels params) k :=
  self.toProjectionSyntaxWF.specializedIndices_instN hfamily levels params
    hparams a k

abbrev LayoutWF.specializedCtorFields_liftN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ view.generation.flatCtors)
    (levels : List VLevel) (params : List VExpr)
    (hparams : params.length = view.nparams) (n k : Nat) :
    view.specializedCtorFields constructor levels
        (params.map fun param => param.liftN n k) =
      VExpr.liftTelN n
        (view.specializedCtorFields constructor levels params) k :=
  self.toProjectionSyntaxWF.specializedCtorFields_liftN hconstructor levels
    params hparams n k

abbrev LayoutWF.specializedCtorFields_instN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ view.generation.flatCtors)
    (levels : List VLevel) (params : List VExpr)
    (hparams : params.length = view.nparams) (a : VExpr) (k : Nat) :
    view.specializedCtorFields constructor levels
        (params.map fun param => param.inst a k) =
      VExpr.instTelN a
        (view.specializedCtorFields constructor levels params) k :=
  self.toProjectionSyntaxWF.specializedCtorFields_instN hconstructor levels
    params hparams a k

abbrev WF.specializedFields_liftN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) := self.toLayoutWF.specializedFields_liftN

abbrev WF.specializedFields_instN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) := self.toLayoutWF.specializedFields_instN

@[simp] theorem ProjectionSyntaxWF.identityMotive_liftN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.ProjectionSyntaxWF env) {family : NormalizedFamily}
    (hfamily : family ∈ view.generation.families)
    (fieldSort : VLevel) (levels : List VLevel) (params : List VExpr)
    (hparams : params.length = view.nparams) (n k : Nat) :
    (view.identityMotive family fieldSort levels params).liftN n k =
      view.identityMotive family fieldSort levels
        (params.map fun param => param.liftN n k) := by
  let indices := view.specializedIndices family levels params
  let params' := params.map fun param => param.liftN n k
  let indices' := view.specializedIndices family levels params'
  have hindices : indices' = VExpr.liftTelN n indices k := by
    simpa [indices, indices', params'] using
      self.specializedIndices_liftN hfamily levels params hparams n k
  have hindicesLength : indices'.length = indices.length := by
    rw [hindices, VExpr.liftTelN_length]
  let familyApp := VExpr.appN (.const family.raw.name levels)
    (params.map (VExpr.liftN indices.length) ++
      VExpr.bvarRevRange 0 indices.length)
  let familyApp' := VExpr.appN (.const family.raw.name levels)
    (params'.map (VExpr.liftN indices'.length) ++
      VExpr.bvarRevRange 0 indices'.length)
  have hfamilyApp : familyApp.liftN n (k + indices.length) = familyApp' := by
    simp only [familyApp, familyApp', VExpr.liftN_appN, VExpr.liftN,
      List.map_append, List.map_map, Function.comp_def]
    rw [hindicesLength]
    simp only [params']
    rw [List.map_map]
    congr 2
    · apply List.map_congr_left
      intro param _
      exact (VExpr.liftN_liftN_comm param indices.length n 0 k
        (Nat.zero_le _)).symm
    · exact VExpr.bvarRevRange_liftN_high _ _ _ _ (by omega)
  simp only [identityMotive]
  change (VExpr.lamN indices
      (.lam familyApp (.const ``PUnit [fieldSort]))).liftN n k =
    VExpr.lamN indices' (.lam familyApp' (.const ``PUnit [fieldSort]))
  rw [VExpr.liftN_lamN_projection, ← hindices]
  simp only [VExpr.liftN, hfamilyApp]

@[simp] theorem ProjectionSyntaxWF.identityMotive_instN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.ProjectionSyntaxWF env) {family : NormalizedFamily}
    (hfamily : family ∈ view.generation.families)
    (fieldSort : VLevel) (levels : List VLevel) (params : List VExpr)
    (hparams : params.length = view.nparams) (a : VExpr) (k : Nat) :
    (view.identityMotive family fieldSort levels params).inst a k =
      view.identityMotive family fieldSort levels
        (params.map fun param => param.inst a k) := by
  let indices := view.specializedIndices family levels params
  let params' := params.map fun param => param.inst a k
  let indices' := view.specializedIndices family levels params'
  have hindices : indices' = VExpr.instTelN a indices k := by
    simpa [indices, indices', params'] using
      self.specializedIndices_instN hfamily levels params hparams a k
  have hindicesLength : indices'.length = indices.length := by
    rw [hindices, VExpr.instTelN_length]
  let familyApp := VExpr.appN (.const family.raw.name levels)
    (params.map (VExpr.liftN indices.length) ++
      VExpr.bvarRevRange 0 indices.length)
  let familyApp' := VExpr.appN (.const family.raw.name levels)
    (params'.map (VExpr.liftN indices'.length) ++
      VExpr.bvarRevRange 0 indices'.length)
  have hfamilyApp : familyApp.inst a (k + indices.length) = familyApp' := by
    simp only [familyApp, familyApp', VExpr.instN_appN, VExpr.inst,
      List.map_append, List.map_map, Function.comp_def]
    rw [hindicesLength]
    simp only [params']
    rw [List.map_map]
    congr 2
    · apply List.map_congr_left
      intro param _
      simpa only [Nat.add_comm, Function.comp_def] using
        (VExpr.liftN_instN_lo indices.length param a k 0
          (Nat.zero_le _)).symm
    · exact VExpr.bvarRevRange_instN_high _ _ _ _ (by omega)
  simp only [identityMotive]
  change (VExpr.lamN indices
      (.lam familyApp (.const ``PUnit [fieldSort]))).inst a k =
    VExpr.lamN indices' (.lam familyApp' (.const ``PUnit [fieldSort]))
  rw [VExpr.instN_lamN_projection, ← hindices]
  simp only [VExpr.inst, hfamilyApp]

@[simp] theorem ProjectionSyntaxWF.identityMotiveWith_liftN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.ProjectionSyntaxWF env) {family : NormalizedFamily}
    (hfamily : family ∈ view.generation.families)
    (levels : List VLevel) (params : List VExpr)
    (dummyType : VExpr) (hparams : params.length = view.nparams)
    (n k : Nat) :
    (view.identityMotiveWith family levels params dummyType).liftN n k =
      view.identityMotiveWith family levels
        (params.map fun param => param.liftN n k)
        (dummyType.liftN n k) := by
  let indices := view.specializedIndices family levels params
  let params' := params.map fun param => param.liftN n k
  let indices' := view.specializedIndices family levels params'
  have hindices : indices' = VExpr.liftTelN n indices k := by
    simpa [indices, indices', params'] using
      self.specializedIndices_liftN hfamily levels params hparams n k
  have hindicesLength : indices'.length = indices.length := by
    rw [hindices, VExpr.liftTelN_length]
  let familyApp := VExpr.appN (.const family.raw.name levels)
    (params.map (VExpr.liftN indices.length) ++
      VExpr.bvarRevRange 0 indices.length)
  let familyApp' := VExpr.appN (.const family.raw.name levels)
    (params'.map (VExpr.liftN indices'.length) ++
      VExpr.bvarRevRange 0 indices'.length)
  have hfamilyApp : familyApp.liftN n (k + indices.length) = familyApp' := by
    simp only [familyApp, familyApp', VExpr.liftN_appN, VExpr.liftN,
      List.map_append, List.map_map, Function.comp_def]
    rw [hindicesLength]
    simp only [params']
    rw [List.map_map]
    congr 2
    · apply List.map_congr_left
      intro param _
      exact (VExpr.liftN_liftN_comm param indices.length n 0 k
        (Nat.zero_le _)).symm
    · exact VExpr.bvarRevRange_liftN_high _ _ _ _ (by omega)
  have hdummy :
      (dummyType.liftN (indices.length + 1)).liftN n
          (k + indices.length + 1) =
        (dummyType.liftN n k).liftN (indices'.length + 1) := by
    rw [hindicesLength]
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (VExpr.liftN_liftN_comm dummyType (indices.length + 1) n 0 k
        (Nat.zero_le _)).symm
  simp only [identityMotiveWith]
  change (VExpr.lamN indices
      (.lam familyApp (dummyType.liftN (indices.length + 1)))).liftN n k =
    VExpr.lamN indices'
      (.lam familyApp'
        ((dummyType.liftN n k).liftN (indices'.length + 1)))
  rw [VExpr.liftN_lamN_projection, ← hindices]
  simp only [VExpr.liftN, hfamilyApp, hdummy]

@[simp] theorem ProjectionSyntaxWF.identityMotiveWith_instN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.ProjectionSyntaxWF env) {family : NormalizedFamily}
    (hfamily : family ∈ view.generation.families)
    (levels : List VLevel) (params : List VExpr)
    (dummyType : VExpr) (hparams : params.length = view.nparams)
    (a : VExpr) (k : Nat) :
    (view.identityMotiveWith family levels params dummyType).inst a k =
      view.identityMotiveWith family levels
        (params.map fun param => param.inst a k) (dummyType.inst a k) := by
  let indices := view.specializedIndices family levels params
  let params' := params.map fun param => param.inst a k
  let indices' := view.specializedIndices family levels params'
  have hindices : indices' = VExpr.instTelN a indices k := by
    simpa [indices, indices', params'] using
      self.specializedIndices_instN hfamily levels params hparams a k
  have hindicesLength : indices'.length = indices.length := by
    rw [hindices, VExpr.instTelN_length]
  let familyApp := VExpr.appN (.const family.raw.name levels)
    (params.map (VExpr.liftN indices.length) ++
      VExpr.bvarRevRange 0 indices.length)
  let familyApp' := VExpr.appN (.const family.raw.name levels)
    (params'.map (VExpr.liftN indices'.length) ++
      VExpr.bvarRevRange 0 indices'.length)
  have hfamilyApp : familyApp.inst a (k + indices.length) = familyApp' := by
    simp only [familyApp, familyApp', VExpr.instN_appN, VExpr.inst,
      List.map_append, List.map_map, Function.comp_def]
    rw [hindicesLength]
    simp only [params']
    rw [List.map_map]
    congr 2
    · apply List.map_congr_left
      intro param _
      simpa only [Nat.add_comm, Function.comp_def] using
        (VExpr.liftN_instN_lo indices.length param a k 0
          (Nat.zero_le _)).symm
    · exact VExpr.bvarRevRange_instN_high _ _ _ _ (by omega)
  have hdummy :
      (dummyType.liftN (indices.length + 1)).inst a
          (k + indices.length + 1) =
        (dummyType.inst a k).liftN (indices'.length + 1) := by
    rw [hindicesLength]
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (VExpr.liftN_instN_lo (indices.length + 1) dummyType a k 0
        (Nat.zero_le _)).symm
  simp only [identityMotiveWith]
  change (VExpr.lamN indices
      (.lam familyApp (dummyType.liftN (indices.length + 1)))).inst a k =
    VExpr.lamN indices'
      (.lam familyApp'
        ((dummyType.inst a k).liftN (indices'.length + 1)))
  rw [VExpr.instN_lamN_projection, ← hindices]
  simp only [VExpr.inst, hfamilyApp, hdummy]

@[simp] theorem ProjectionSyntaxWF.projectionMotivesWith_liftN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.ProjectionSyntaxWF env) (levels : List VLevel)
    (params : List VExpr) (hparams : params.length = view.nparams)
    (typeFn dummyType : VExpr) (n k : Nat) :
    (view.projectionMotivesWith levels params typeFn dummyType).map
        (fun motive => motive.liftN n k) =
      view.projectionMotivesWith levels
        (params.map fun param => param.liftN n k)
        (typeFn.liftN n k) (dummyType.liftN n k) := by
  simp only [projectionMotivesWith, List.map_map]
  apply List.map_congr_left
  intro family hfamily
  by_cases selected : family.view.ordinal = view.family.view.ordinal
  · simp [selected]
  · simp [selected, self.identityMotiveWith_liftN hfamily levels params
      dummyType hparams n k]

@[simp] theorem ProjectionSyntaxWF.projectionMotivesWith_instN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.ProjectionSyntaxWF env) (levels : List VLevel)
    (params : List VExpr) (hparams : params.length = view.nparams)
    (typeFn dummyType a : VExpr) (k : Nat) :
    (view.projectionMotivesWith levels params typeFn dummyType).map
        (fun motive => motive.inst a k) =
      view.projectionMotivesWith levels
        (params.map fun param => param.inst a k)
        (typeFn.inst a k) (dummyType.inst a k) := by
  simp only [projectionMotivesWith, List.map_map]
  apply List.map_congr_left
  intro family hfamily
  by_cases selected : family.view.ordinal = view.family.view.ordinal
  · simp [selected]
  · simp [selected, self.identityMotiveWith_instN hfamily levels params
      dummyType hparams a k]

@[simp] theorem ProjectionSyntaxWF.projectionMotives_liftN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.ProjectionSyntaxWF env) (fieldSort : VLevel)
    (levels : List VLevel) (params : List VExpr)
    (hparams : params.length = view.nparams) (typeFn : VExpr)
    (n k : Nat) :
    (view.projectionMotives levels params fieldSort typeFn).map
        (fun motive => motive.liftN n k) =
      view.projectionMotives levels
        (params.map fun param => param.liftN n k)
        fieldSort (typeFn.liftN n k) := by
  simp only [projectionMotives, List.map_map]
  apply List.map_congr_left
  intro family hfamily
  by_cases selected : family.view.ordinal = view.family.view.ordinal
  · simp [selected]
  · simp [selected, self.identityMotive_liftN hfamily fieldSort levels params
      hparams n k]

@[simp] theorem ProjectionSyntaxWF.projectionMotives_instN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.ProjectionSyntaxWF env) (fieldSort : VLevel)
    (levels : List VLevel) (params : List VExpr)
    (hparams : params.length = view.nparams) (typeFn a : VExpr)
    (k : Nat) :
    (view.projectionMotives levels params fieldSort typeFn).map
        (fun motive => motive.inst a k) =
      view.projectionMotives levels
        (params.map fun param => param.inst a k)
        fieldSort (typeFn.inst a k) := by
  simp only [projectionMotives, List.map_map]
  apply List.map_congr_left
  intro family hfamily
  by_cases selected : family.view.ordinal = view.family.view.ordinal
  · simp [selected]
  · simp [selected, self.identityMotive_instN hfamily fieldSort levels params
      hparams a k]

@[simp] theorem ProjectionSyntaxWF.generatedProjectionMinorType_liftN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.ProjectionSyntaxWF env) {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ view.generation.flatCtors)
    (fieldSort : VLevel) (levels : List VLevel)
    (params motives : List VExpr)
    (hparams : params.length = view.nparams)
    (hmotives : motives.length = view.generation.familyCount)
    (n k : Nat) :
    (view.generatedProjectionMinorType constructor fieldSort levels params
        motives).liftN n k =
      view.generatedProjectionMinorType constructor fieldSort levels
        (params.map fun param => param.liftN n k)
        (motives.map fun motive => motive.liftN n k) := by
  have hclosed :
      ((view.generation.minorType constructor).instL
        (view.projectionLevels fieldSort levels)).ClosedN
          (view.nparams + view.generation.familyCount) :=
    VExpr.ClosedN.instL
      (self.generationEnv.minorType_closedN hconstructor)
  unfold generatedProjectionMinorType
  rw [← VExpr.instRevAt_zero]
  conv => lhs; rw [show k = k + 0 by omega, VExpr.liftN_instRevAt]
  rw [hmotives, VExpr.liftN_instRevAt]
  rw [hclosed.liftN_eq (by rw [hparams]; omega)]
  simp [VExpr.instRevAt_zero]

@[simp] theorem ProjectionSyntaxWF.generatedProjectionMinorType_instN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.ProjectionSyntaxWF env) {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ view.generation.flatCtors)
    (fieldSort : VLevel) (levels : List VLevel)
    (params motives : List VExpr)
    (hparams : params.length = view.nparams)
    (hmotives : motives.length = view.generation.familyCount)
    (a : VExpr) (k : Nat) :
    (view.generatedProjectionMinorType constructor fieldSort levels params
        motives).inst a k =
      view.generatedProjectionMinorType constructor fieldSort levels
        (params.map fun param => param.inst a k)
        (motives.map fun motive => motive.inst a k) := by
  have hclosed :
      ((view.generation.minorType constructor).instL
        (view.projectionLevels fieldSort levels)).ClosedN
          (view.nparams + view.generation.familyCount) :=
    VExpr.ClosedN.instL
      (self.generationEnv.minorType_closedN hconstructor)
  unfold generatedProjectionMinorType
  rw [← VExpr.instRevAt_zero]
  conv => lhs; rw [show k = k + 0 by omega, VExpr.instN_instRevAt]
  rw [hmotives, VExpr.instN_instRevAt]
  rw [hclosed.instN_eq (by rw [hparams]; omega)]
  simp [VExpr.instRevAt_zero]

/-- Lifting the complete field/IH binder prefix of a generated mutual minor
is the same as regenerating that prefix from the lifted block arguments. -/
@[simp] theorem ProjectionSyntaxWF.generatedProjectionMinorBinders_liftN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.ProjectionSyntaxWF env) {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ view.generation.flatCtors)
    (fieldSort : VLevel) (levels : List VLevel)
    (params motives : List VExpr)
    (hparams : params.length = view.nparams)
    (hmotives : motives.length = view.generation.familyCount)
    (n k : Nat) :
    VExpr.liftTelN n
        (VExpr.telN
          ((view.specializedCtorFields constructor levels params).length +
            constructor.ctor.view.recursive.length)
          (view.generatedProjectionMinorType constructor fieldSort levels
            params motives))
        k =
      VExpr.telN
        ((view.specializedCtorFields constructor levels
            (params.map fun param => param.liftN n k)).length +
          constructor.ctor.view.recursive.length)
        (view.generatedProjectionMinorType constructor fieldSort levels
          (params.map fun param => param.liftN n k)
          (motives.map fun motive => motive.liftN n k)) := by
  have hfields := self.specializedCtorFields_liftN hconstructor levels params
    hparams n k
  have hfieldsLength := congrArg List.length hfields
  simp only [VExpr.liftTelN_length] at hfieldsLength
  rw [hfieldsLength]
  rw [← self.generatedProjectionMinorType_liftN hconstructor fieldSort levels params
    motives hparams hmotives n k]
  rw [VExpr.telN_liftN]

/-- Instantiating the complete field/IH binder prefix of a generated mutual
minor is the same as regenerating that prefix from the instantiated block
arguments.  The known generated Pi shape is essential here: arbitrary term
instantiation need not preserve an otherwise unknown telescope head. -/
@[simp] theorem ProjectionSyntaxWF.generatedProjectionMinorBinders_instN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.ProjectionSyntaxWF env) {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ view.generation.flatCtors)
    (fieldSort : VLevel) (levels : List VLevel)
    (params motives : List VExpr)
    (hparams : params.length = view.nparams)
    (hmotives : motives.length = view.generation.familyCount)
    (a : VExpr) (k : Nat) :
    VExpr.instTelN a
        (VExpr.telN
          ((view.specializedCtorFields constructor levels params).length +
            constructor.ctor.view.recursive.length)
          (view.generatedProjectionMinorType constructor fieldSort levels
            params motives))
        k =
      VExpr.telN
        ((view.specializedCtorFields constructor levels
            (params.map fun param => param.inst a k)).length +
          constructor.ctor.view.recursive.length)
        (view.generatedProjectionMinorType constructor fieldSort levels
          (params.map fun param => param.inst a k)
          (motives.map fun motive => motive.inst a k)) := by
  let count :=
    (view.specializedCtorFields constructor levels params).length +
      constructor.ctor.view.recursive.length
  let exactMinor :=
    view.generatedProjectionMinorType constructor fieldSort levels params motives
  let binders := VExpr.telN count exactMinor
  let body := VExpr.dropN count exactMinor
  have hbindersLength : binders.length = count := by
    simpa [binders, count, exactMinor] using
      view.generatedProjectionMinorBinders_length constructor fieldSort levels params
        motives hmotives
  have hshape : exactMinor = VExpr.forallN binders body := by
    exact (VExpr.forallN_telN_dropN count exactMinor).symm
  have hfields := self.specializedCtorFields_instN hconstructor levels params
    hparams a k
  have hfieldsLength := congrArg List.length hfields
  simp only [VExpr.instTelN_length] at hfieldsLength
  rw [hfieldsLength]
  rw [← self.generatedProjectionMinorType_instN hconstructor fieldSort levels params
    motives hparams hmotives a k]
  change VExpr.instTelN a binders k = VExpr.telN count (exactMinor.inst a k)
  rw [hshape, VExpr.instN_forallN]
  rw [show count = (VExpr.instTelN a binders k).length by
    rw [VExpr.instTelN_length, hbindersLength]]
  rw [VExpr.telN_forallN_length]

/-- Dummy unit minors commute with ambient lifting. -/
@[simp] theorem ProjectionSyntaxWF.identityMinor_liftN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.ProjectionSyntaxWF env) {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ view.generation.flatCtors)
    (fieldSort : VLevel) (levels : List VLevel)
    (params motives : List VExpr)
    (hparams : params.length = view.nparams)
    (hmotives : motives.length = view.generation.familyCount)
    (n k : Nat) :
    (view.identityMinor constructor fieldSort levels params motives).liftN n k =
      view.identityMinor constructor fieldSort levels
        (params.map fun param => param.liftN n k)
        (motives.map fun motive => motive.liftN n k) := by
  let fields := view.specializedCtorFields constructor levels params
  let params' := params.map fun param => param.liftN n k
  let motives' := motives.map fun motive => motive.liftN n k
  let fields' := view.specializedCtorFields constructor levels params'
  let count := fields.length + constructor.ctor.view.recursive.length
  let count' := fields'.length + constructor.ctor.view.recursive.length
  let exactMinor :=
    view.generatedProjectionMinorType constructor fieldSort levels params motives
  let exactMinor' :=
    view.generatedProjectionMinorType constructor fieldSort levels params' motives'
  let binders := VExpr.telN count exactMinor
  let binders' := VExpr.telN count' exactMinor'
  have hbinders : VExpr.liftTelN n binders k = binders' := by
    simpa [binders, binders', count, count', exactMinor, exactMinor', fields,
      fields', params', motives'] using
      self.generatedProjectionMinorBinders_liftN hconstructor fieldSort levels
        params motives hparams hmotives n k
  unfold identityMinor
  change (VExpr.lamN binders (.const ``PUnit.unit [fieldSort])).liftN n k =
    VExpr.lamN binders' (.const ``PUnit.unit [fieldSort])
  rw [VExpr.liftN_lamN_projection, hbinders]
  rfl

/-- Dummy unit minors commute with ambient term instantiation. -/
@[simp] theorem ProjectionSyntaxWF.identityMinor_instN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.ProjectionSyntaxWF env) {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ view.generation.flatCtors)
    (fieldSort : VLevel) (levels : List VLevel)
    (params motives : List VExpr)
    (hparams : params.length = view.nparams)
    (hmotives : motives.length = view.generation.familyCount)
    (a : VExpr) (k : Nat) :
    (view.identityMinor constructor fieldSort levels params motives).inst a k =
      view.identityMinor constructor fieldSort levels
        (params.map fun param => param.inst a k)
        (motives.map fun motive => motive.inst a k) := by
  let fields := view.specializedCtorFields constructor levels params
  let params' := params.map fun param => param.inst a k
  let motives' := motives.map fun motive => motive.inst a k
  let fields' := view.specializedCtorFields constructor levels params'
  let count := fields.length + constructor.ctor.view.recursive.length
  let count' := fields'.length + constructor.ctor.view.recursive.length
  let exactMinor :=
    view.generatedProjectionMinorType constructor fieldSort levels params motives
  let exactMinor' :=
    view.generatedProjectionMinorType constructor fieldSort levels params' motives'
  let binders := VExpr.telN count exactMinor
  let binders' := VExpr.telN count' exactMinor'
  have hbinders : VExpr.instTelN a binders k = binders' := by
    simpa [binders, binders', count, count', exactMinor, exactMinor', fields,
      fields', params', motives'] using
      self.generatedProjectionMinorBinders_instN hconstructor fieldSort levels
        params motives hparams hmotives a k
  unfold identityMinor
  change (VExpr.lamN binders (.const ``PUnit.unit [fieldSort])).inst a k =
    VExpr.lamN binders' (.const ``PUnit.unit [fieldSort])
  rw [VExpr.instN_lamN_projection, hbinders]
  rfl

@[simp] theorem ProjectionSyntaxWF.identityMinorWith_liftN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.ProjectionSyntaxWF env) {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ view.generation.flatCtors)
    (fieldSort : VLevel) (levels : List VLevel)
    (params motives : List VExpr) (dummyValue : VExpr)
    (hparams : params.length = view.nparams)
    (hmotives : motives.length = view.generation.familyCount)
    (n k : Nat) :
    (view.identityMinorWith constructor fieldSort levels params motives
        dummyValue).liftN n k =
      view.identityMinorWith constructor fieldSort levels
        (params.map fun param => param.liftN n k)
        (motives.map fun motive => motive.liftN n k)
        (dummyValue.liftN n k) := by
  let fields := view.specializedCtorFields constructor levels params
  let params' := params.map fun param => param.liftN n k
  let motives' := motives.map fun motive => motive.liftN n k
  let fields' := view.specializedCtorFields constructor levels params'
  let count := fields.length + constructor.ctor.view.recursive.length
  let count' := fields'.length + constructor.ctor.view.recursive.length
  let exactMinor :=
    view.generatedProjectionMinorType constructor fieldSort levels params motives
  let exactMinor' :=
    view.generatedProjectionMinorType constructor fieldSort levels params' motives'
  let binders := VExpr.telN count exactMinor
  let binders' := VExpr.telN count' exactMinor'
  have hbinders : VExpr.liftTelN n binders k = binders' := by
    simpa [binders, binders', count, count', exactMinor, exactMinor', fields,
      fields', params', motives'] using
      self.generatedProjectionMinorBinders_liftN hconstructor fieldSort levels
        params motives hparams hmotives n k
  have hbindersLength : binders'.length = binders.length := by
    rw [← hbinders, VExpr.liftTelN_length]
  have hdummy :
      (dummyValue.liftN binders.length).liftN n
          (k + binders.length) =
        (dummyValue.liftN n k).liftN binders'.length := by
    rw [hbindersLength]
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (VExpr.liftN_liftN_comm dummyValue binders.length n 0 k
        (Nat.zero_le _)).symm
  unfold identityMinorWith
  change (VExpr.lamN binders
      (dummyValue.liftN binders.length)).liftN n k =
    VExpr.lamN binders'
      ((dummyValue.liftN n k).liftN binders'.length)
  rw [VExpr.liftN_lamN_projection, hbinders, hdummy]

@[simp] theorem ProjectionSyntaxWF.identityMinorWith_instN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.ProjectionSyntaxWF env) {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ view.generation.flatCtors)
    (fieldSort : VLevel) (levels : List VLevel)
    (params motives : List VExpr) (dummyValue : VExpr)
    (hparams : params.length = view.nparams)
    (hmotives : motives.length = view.generation.familyCount)
    (a : VExpr) (k : Nat) :
    (view.identityMinorWith constructor fieldSort levels params motives
        dummyValue).inst a k =
      view.identityMinorWith constructor fieldSort levels
        (params.map fun param => param.inst a k)
        (motives.map fun motive => motive.inst a k)
        (dummyValue.inst a k) := by
  let fields := view.specializedCtorFields constructor levels params
  let params' := params.map fun param => param.inst a k
  let motives' := motives.map fun motive => motive.inst a k
  let fields' := view.specializedCtorFields constructor levels params'
  let count := fields.length + constructor.ctor.view.recursive.length
  let count' := fields'.length + constructor.ctor.view.recursive.length
  let exactMinor :=
    view.generatedProjectionMinorType constructor fieldSort levels params motives
  let exactMinor' :=
    view.generatedProjectionMinorType constructor fieldSort levels params' motives'
  let binders := VExpr.telN count exactMinor
  let binders' := VExpr.telN count' exactMinor'
  have hbinders : VExpr.instTelN a binders k = binders' := by
    simpa [binders, binders', count, count', exactMinor, exactMinor', fields,
      fields', params', motives'] using
      self.generatedProjectionMinorBinders_instN hconstructor fieldSort levels
        params motives hparams hmotives a k
  have hbindersLength : binders'.length = binders.length := by
    rw [← hbinders, VExpr.instTelN_length]
  have hdummy :
      (dummyValue.liftN binders.length).inst a (k + binders.length) =
        (dummyValue.inst a k).liftN binders'.length := by
    rw [hbindersLength]
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (VExpr.liftN_instN_lo binders.length dummyValue a k 0
        (Nat.zero_le _)).symm
  unfold identityMinorWith
  change (VExpr.lamN binders
      (dummyValue.liftN binders.length)).inst a k =
    VExpr.lamN binders'
      ((dummyValue.inst a k).liftN binders'.length)
  rw [VExpr.instN_lamN_projection, hbinders, hdummy]

/-- Once regularity exposes one exact generated minor domain as a type, a
nonselected constructor's canonical `PUnit.unit` minor inhabits it.  The
terminal generated motive application is collapsed by typed beta rather
than by a syntactic equality oracle. -/
private theorem WF.identityMinor_hasType_of_isType
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ view.generation.flatCtors)
    (hnotSelected : constructor.owner ≠ view.family.view.ordinal)
    (fieldSort : VLevel) (hfieldSort : fieldSort.WF U)
    (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (typeFn : VExpr)
    (minorIsType : env.IsType U Γ
      (view.generatedProjectionMinorType constructor fieldSort levels params
        (view.projectionMotives levels params fieldSort typeFn))) :
    env.HasType U Γ
      (view.identityMinor constructor fieldSort levels params
        (view.projectionMotives levels params fieldSort typeFn))
      (view.generatedProjectionMinorType constructor fieldSort levels params
        (view.projectionMotives levels params fieldSort typeFn)) := by
  let motives := view.projectionMotives levels params fieldSort typeFn
  let exactMinor := view.generatedProjectionMinorType constructor fieldSort
    levels params motives
  let count := (view.specializedCtorFields constructor levels params).length +
    constructor.ctor.view.recursive.length
  let binders := VExpr.telN count exactMinor
  let result := VExpr.dropN count exactMinor
  obtain ⟨family, hfamily, howner, _hname, hindices⟩ :=
    (self.generationEnv.ctorWF constructor hconstructor).owner
  have hfamilyNotSelected :
      family.view.ordinal ≠ view.family.view.ordinal := by
    intro selected
    exact hnotSelected (howner ▸ selected)
  have hmotivesLength : motives.length = view.generation.familyCount := by
    simp [motives]
  have hmotive : motives[family.view.ordinal]? =
      some (view.identityMotive family fieldSort levels params) := by
    simpa [motives, hfamilyNotSelected] using
      view.projectionMotives_getElem?_ordinal family hfamily levels params
        fieldSort typeFn
  have hresultLength : constructor.ctor.view.resultIndices.length =
      family.view.indices.length := by
    exact (self.generationEnv.viewResultIndices_length hconstructor).trans
      (congrArg List.length hindices).symm
  let arguments := view.generatedProjectionMinorArguments constructor
    fieldSort levels params motives
  obtain ⟨hargumentsLength, hresultShape⟩ :=
    view.generatedProjectionMinorResult_motive constructor family howner
      hresultLength fieldSort levels params motives
      (view.identityMotive family fieldSort levels params)
      hmotivesLength hmotive
  have hbindersLength : binders.length = count := by
    simpa [binders, count, exactMinor] using
      view.generatedProjectionMinorBinders_length constructor fieldSort levels
        params motives hmotivesLength
  have hexactShape : exactMinor = VExpr.forallN binders result :=
    (VExpr.forallN_telN_dropN count exactMinor).symm
  obtain ⟨minorLevel, hminorType⟩ := minorIsType
  change env.HasType U Γ exactMinor (.sort minorLevel) at hminorType
  rw [hexactShape] at hminorType
  obtain ⟨hbinders, _resultLevel, hresultType⟩ :=
    VEnv.HasType.forallN_wf henv.ordered hminorType
  have hterminalCtx : OnCtx (binders.reverse ++ Γ) (env.IsType U) :=
    hbinders.toOnCtx hΓ
  let indices := view.specializedIndices family levels params
  let familyApp := VExpr.appN (.const family.raw.name levels)
    (params.map (VExpr.liftN indices.length) ++
      VExpr.bvarRevRange 0 indices.length)
  let motiveBinders := indices ++ [familyApp]
  have hmotiveTypeShape :
      view.projectionMotiveType family fieldSort levels params =
        VExpr.forallN motiveBinders (.sort fieldSort) := by
    simp [projectionMotiveType, motiveBinders, indices, familyApp,
      VExpr.forallN_append, VExpr.forallN]
  have hidentity := self.identityMotive_hasType henv.ordered family hfamily
    fieldSort hfieldSort levels hlevels hlevelsLength params hparamsLength
    paramsSpine
  change env.HasType U Γ
    (view.identityMotive family fieldSort levels params)
    (view.projectionMotiveType family fieldSort levels params) at hidentity
  rw [hmotiveTypeShape] at hidentity
  have hidentityWeak := hidentity.weakN henv.ordered
    (Ctx.LiftN.zero (n := count) (Γ := Γ) binders.reverse
      (h := by simp [hbindersLength]))
  have hidentityWeak' : env.HasType U (binders.reverse ++ Γ)
      (VExpr.liftN count
        (view.identityMotive family fieldSort levels params))
      (VExpr.forallN (VExpr.liftTelN count motiveBinders 0)
        (.sort fieldSort)) := by
    rw [VExpr.liftN_forallN] at hidentityWeak
    change env.HasType U (binders.reverse ++ Γ)
      (VExpr.liftN count
        (view.identityMotive family fieldSort levels params))
      (VExpr.forallN (VExpr.liftTelN count motiveBinders 0)
        (.sort fieldSort)) at hidentityWeak
    exact hidentityWeak
  have hidentitySyntax :
      VExpr.liftN count
          (view.identityMotive family fieldSort levels params) =
        VExpr.lamN (VExpr.liftTelN count motiveBinders 0)
          (.const ``PUnit [fieldSort]) := by
    change (VExpr.lamN indices
      (VExpr.lamN [familyApp] (.const ``PUnit [fieldSort]))).liftN count = _
    rw [← VExpr.lamN_append indices [familyApp]
      (.const ``PUnit [fieldSort])]
    rw [VExpr.liftN_lamN_projection]
    simp [motiveBinders, VExpr.liftN]
  rw [hidentitySyntax] at hidentityWeak'
  obtain ⟨hmotiveBinders, _motiveResult, _hpunitType⟩ :=
    VEnv.HasType.lamN_wf henv.ordered hterminalCtx hidentityWeak'
  have hindicesLength : indices.length = family.view.indices.length := by
    simpa [indices, specializedIndices] using
      (view.generation.shape.2.2.2.2 family hfamily).2.2.2.1
  have hmotiveBindersLength :
      (VExpr.liftTelN count motiveBinders 0).length = arguments.length := by
    rw [VExpr.liftTelN_length, hargumentsLength]
    simp [motiveBinders, hindicesLength]
  have hresultType' : env.HasType U (binders.reverse ++ Γ)
      (VExpr.appN
        (VExpr.liftN count
          (view.identityMotive family fieldSort levels params))
        arguments) _resultLevel := by
    rw [← hresultShape]
    simpa [result, count, exactMinor, hbindersLength] using hresultType
  rw [hidentitySyntax] at hresultType'
  have hmotiveSpine := VEnv.HasType.spineWF_of_appN henv hterminalCtx
    hidentityWeak' hresultType' hmotiveBindersLength.symm
  have hpunitType : env.HasType U
      ((VExpr.liftTelN count motiveBinders 0).reverse ++
        (binders.reverse ++ Γ))
      (.const ``PUnit [fieldSort]) (.sort fieldSort) := by
    have hout := VEnv.HasType.const
      (Γ := (VExpr.liftTelN count motiveBinders 0).reverse ++
        (binders.reverse ++ Γ))
      (c := ``PUnit) (ls := [fieldSort]) self.punitRegistered.type
      (by simpa) (by simp)
    simpa [VExpr.instL, VLevel.inst,
      List.getD_eq_getElem?_getD] using hout
  have hcollapse := VEnv.IsDefEq.appN_lamN henv.ordered hmotiveBinders
    hpunitType hmotiveSpine hmotiveBindersLength.symm
  rw [VExpr.instRev_closedN arguments
      (C := .const ``PUnit [fieldSort]) (by trivial),
    VExpr.instRev_closedN arguments
      (C := .sort fieldSort) (by trivial)] at hcollapse
  have hunit : env.HasType U (binders.reverse ++ Γ)
      (.const ``PUnit.unit [fieldSort]) (.const ``PUnit [fieldSort]) := by
    have hout := VEnv.HasType.const
      (Γ := binders.reverse ++ Γ) (c := ``PUnit.unit) (ls := [fieldSort])
      self.punitRegistered.unit (by simpa) (by simp)
    simpa [VExpr.instL, VLevel.inst,
      List.getD_eq_getElem?_getD] using hout
  have hcollapseU : env.IsDefEqU U (binders.reverse ++ Γ)
      (VExpr.appN
        (VExpr.liftN count
          (view.identityMotive family fieldSort levels params))
        arguments) (.const ``PUnit [fieldSort]) := by
    rw [hidentitySyntax]
    exact ⟨.sort fieldSort, by simpa using hcollapse⟩
  have hunitResult : env.HasType U (binders.reverse ++ Γ)
      (.const ``PUnit.unit [fieldSort]) result := by
    change env.HasType U (binders.reverse ++ Γ)
      (.const ``PUnit.unit [fieldSort])
      (VExpr.dropN
        ((view.specializedCtorFields constructor levels params).length +
          constructor.ctor.view.recursive.length)
        (view.generatedProjectionMinorType constructor fieldSort levels params
          motives))
    rw [hresultShape]
    exact henv.hasType_defeqU_r hterminalCtx hcollapseU.symm hunit
  have hout := VEnv.HasType.lamN hbinders hunitResult
  rw [← hexactShape] at hout
  simpa [identityMinor, binders, result, count, exactMinor, motives] using hout

/-- A nonselected constructor minor can return any supplied inhabitant of
the explicit dummy motive carrier. -/
private theorem LayoutWF.identityMinorWith_hasType_of_isType
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ view.generation.flatCtors)
    (hnotSelected : constructor.owner ≠ view.family.view.ordinal)
    (fieldSort : VLevel) (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (typeFn dummyType dummyValue : VExpr)
    (dummyTypeType : env.HasType U Γ dummyType (.sort fieldSort))
    (dummyValueType : env.HasType U Γ dummyValue dummyType)
    (minorIsType : env.IsType U Γ
      (view.generatedProjectionMinorType constructor fieldSort levels params
        (view.projectionMotivesWith levels params typeFn dummyType))) :
    env.HasType U Γ
      (view.identityMinorWith constructor fieldSort levels params
        (view.projectionMotivesWith levels params typeFn dummyType)
        dummyValue)
      (view.generatedProjectionMinorType constructor fieldSort levels params
        (view.projectionMotivesWith levels params typeFn dummyType)) := by
  let motives := view.projectionMotivesWith levels params typeFn dummyType
  let exactMinor := view.generatedProjectionMinorType constructor fieldSort
    levels params motives
  let count := (view.specializedCtorFields constructor levels params).length +
    constructor.ctor.view.recursive.length
  let binders := VExpr.telN count exactMinor
  let result := VExpr.dropN count exactMinor
  obtain ⟨family, hfamily, howner, _hname, hindices⟩ :=
    (self.generationEnv.ctorWF constructor hconstructor).owner
  have hfamilyNotSelected :
      family.view.ordinal ≠ view.family.view.ordinal := by
    intro selected
    exact hnotSelected (howner ▸ selected)
  have hmotivesLength : motives.length = view.generation.familyCount := by
    simp [motives]
  have hmotive : motives[family.view.ordinal]? =
      some (view.identityMotiveWith family levels params dummyType) := by
    simpa [motives, hfamilyNotSelected] using
      view.projectionMotivesWith_getElem?_ordinal family hfamily levels params
        typeFn dummyType
  have hresultLength : constructor.ctor.view.resultIndices.length =
      family.view.indices.length := by
    exact (self.generationEnv.viewResultIndices_length hconstructor).trans
      (congrArg List.length hindices).symm
  let arguments := view.generatedProjectionMinorArguments constructor
    fieldSort levels params motives
  obtain ⟨hargumentsLength, hresultShape⟩ :=
    view.generatedProjectionMinorResult_motive constructor family howner
      hresultLength fieldSort levels params motives
      (view.identityMotiveWith family levels params dummyType)
      hmotivesLength hmotive
  have hbindersLength : binders.length = count := by
    simpa [binders, count, exactMinor] using
      view.generatedProjectionMinorBinders_length constructor fieldSort levels
        params motives hmotivesLength
  have hexactShape : exactMinor = VExpr.forallN binders result :=
    (VExpr.forallN_telN_dropN count exactMinor).symm
  obtain ⟨minorLevel, hminorType⟩ := minorIsType
  change env.HasType U Γ exactMinor (.sort minorLevel) at hminorType
  rw [hexactShape] at hminorType
  obtain ⟨hbinders, _resultLevel, hresultType⟩ :=
    VEnv.HasType.forallN_wf henv.ordered hminorType
  have hterminalCtx : OnCtx (binders.reverse ++ Γ) (env.IsType U) :=
    hbinders.toOnCtx hΓ
  let indices := view.specializedIndices family levels params
  let familyApp := VExpr.appN (.const family.raw.name levels)
    (params.map (VExpr.liftN indices.length) ++
      VExpr.bvarRevRange 0 indices.length)
  let motiveBinders := indices ++ [familyApp]
  have hmotiveTypeShape :
      view.projectionMotiveType family fieldSort levels params =
        VExpr.forallN motiveBinders (.sort fieldSort) := by
    simp [projectionMotiveType, motiveBinders, indices, familyApp,
      VExpr.forallN_append, VExpr.forallN]
  have hidentity := self.identityMotiveWith_hasType henv.ordered family
    hfamily fieldSort levels hlevels hlevelsLength params hparamsLength
    paramsSpine dummyType dummyTypeType
  change env.HasType U Γ
    (view.identityMotiveWith family levels params dummyType)
    (view.projectionMotiveType family fieldSort levels params) at hidentity
  rw [hmotiveTypeShape] at hidentity
  have hidentityWeak := hidentity.weakN henv.ordered
    (Ctx.LiftN.zero (n := count) (Γ := Γ) binders.reverse
      (h := by simp [hbindersLength]))
  have hidentityWeak' : env.HasType U (binders.reverse ++ Γ)
      (VExpr.liftN count
        (view.identityMotiveWith family levels params dummyType))
      (VExpr.forallN (VExpr.liftTelN count motiveBinders 0)
        (.sort fieldSort)) := by
    rw [VExpr.liftN_forallN] at hidentityWeak
    change env.HasType U (binders.reverse ++ Γ)
      (VExpr.liftN count
        (view.identityMotiveWith family levels params dummyType))
      (VExpr.forallN (VExpr.liftTelN count motiveBinders 0)
        (.sort fieldSort)) at hidentityWeak
    exact hidentityWeak
  have hidentitySyntax :
      VExpr.liftN count
          (view.identityMotiveWith family levels params dummyType) =
        VExpr.lamN (VExpr.liftTelN count motiveBinders 0)
          ((dummyType.liftN count).liftN motiveBinders.length) := by
    change (VExpr.lamN indices
      (VExpr.lamN [familyApp]
        (dummyType.liftN (indices.length + 1)))).liftN count = _
    rw [← VExpr.lamN_append indices [familyApp]
      (dummyType.liftN (indices.length + 1))]
    rw [VExpr.liftN_lamN_projection]
    have hmotiveBindersLength : motiveBinders.length = indices.length + 1 := by
      simp [motiveBinders]
    rw [hmotiveBindersLength]
    congr 1
    simpa only [Nat.zero_add] using
      (calc
        (dummyType.liftN (indices.length + 1)).liftN count
            (indices.length + 1) =
          dummyType.liftN (indices.length + 1 + count) := by
            exact VExpr.liftN'_liftN'
              (e := dummyType) (n1 := indices.length + 1) (n2 := count)
              (k1 := 0) (k2 := indices.length + 1)
              (Nat.zero_le _) (Nat.le_refl _)
        _ = dummyType.liftN (count + (indices.length + 1)) := by
          rw [Nat.add_comm]
        _ = (dummyType.liftN count).liftN (indices.length + 1) := by
          exact (VExpr.liftN_liftN dummyType count
            (indices.length + 1)).symm)
  rw [hidentitySyntax] at hidentityWeak'
  obtain ⟨hmotiveBinders, _motiveResult, _hdummyTypeDeep⟩ :=
    VEnv.HasType.lamN_wf henv.ordered hterminalCtx hidentityWeak'
  have hindicesLength : indices.length = family.view.indices.length := by
    simpa [indices, specializedIndices] using
      (view.generation.shape.2.2.2.2 family hfamily).2.2.2.1
  have hmotiveBindersLength :
      (VExpr.liftTelN count motiveBinders 0).length = arguments.length := by
    rw [VExpr.liftTelN_length, hargumentsLength]
    simp [motiveBinders, hindicesLength]
  have hresultType' : env.HasType U (binders.reverse ++ Γ)
      (VExpr.appN
        (VExpr.liftN count
          (view.identityMotiveWith family levels params dummyType))
        arguments) _resultLevel := by
    rw [← hresultShape]
    simpa [result, count, exactMinor, hbindersLength] using hresultType
  rw [hidentitySyntax] at hresultType'
  have hmotiveSpine := VEnv.HasType.spineWF_of_appN henv hterminalCtx
    hidentityWeak' hresultType' hmotiveBindersLength.symm
  have hdummyTypeDeep : env.HasType U
      ((VExpr.liftTelN count motiveBinders 0).reverse ++
        (binders.reverse ++ Γ))
      ((dummyType.liftN count).liftN motiveBinders.length)
      (.sort fieldSort) := by
    have hout := dummyTypeType.weakN henv.ordered
      (Ctx.LiftN.zero (n := count + motiveBinders.length) (Γ := Γ)
        ((VExpr.liftTelN count motiveBinders 0).reverse ++ binders.reverse)
        (h := by
          simp [VExpr.liftTelN_length, hbindersLength]
          omega))
    simpa [VExpr.liftN_liftN, VExpr.liftN, List.append_assoc] using hout
  have hcollapse := VEnv.IsDefEq.appN_lamN henv.ordered hmotiveBinders
    hdummyTypeDeep hmotiveSpine hmotiveBindersLength.symm
  have hmotiveBindersLength' : motiveBinders.length = arguments.length := by
    simpa [VExpr.liftTelN_length] using hmotiveBindersLength
  rw [hmotiveBindersLength', VExpr.instRev_liftN_len,
    VExpr.instRev_closedN arguments
      (C := .sort fieldSort) (by trivial)] at hcollapse
  have hdummyValue : env.HasType U (binders.reverse ++ Γ)
      (dummyValue.liftN count) (dummyType.liftN count) := by
    have hout := dummyValueType.weakN henv.ordered
      (Ctx.LiftN.zero (n := count) (Γ := Γ) binders.reverse
        (h := by simp [hbindersLength]))
    simpa using hout
  have hcollapseU : env.IsDefEqU U (binders.reverse ++ Γ)
      (VExpr.appN
        (VExpr.liftN count
          (view.identityMotiveWith family levels params dummyType))
        arguments) (dummyType.liftN count) := by
    refine ⟨.sort fieldSort, ?_⟩
    rw [hidentitySyntax, hmotiveBindersLength']
    simpa using hcollapse
  have hdummyResult : env.HasType U (binders.reverse ++ Γ)
      (dummyValue.liftN count) result := by
    change env.HasType U (binders.reverse ++ Γ)
      (dummyValue.liftN count)
      (VExpr.dropN
        ((view.specializedCtorFields constructor levels params).length +
          constructor.ctor.view.recursive.length)
        (view.generatedProjectionMinorType constructor fieldSort levels params
          motives))
    rw [hresultShape]
    exact henv.hasType_defeqU_r hterminalCtx hcollapseU.symm hdummyValue
  have hout := VEnv.HasType.lamN hbinders hdummyResult
  rw [← hexactShape] at hout
  unfold identityMinorWith
  change env.HasType U Γ
    (VExpr.lamN binders (dummyValue.liftN binders.length)) exactMinor
  rw [hbindersLength]
  exact hout

/-- Walk a suffix of the flattened minor telescope until the selected
constructor is reached.  Regularity exposes each exact domain; canonical
identity minors consume every preceding nonselected domain. -/
private theorem WF.selectedMinorType_isTypeAux
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    (fieldSort : VLevel) (hfieldSort : fieldSort.WF U)
    (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (typeFn : VExpr) :
    ∀ (constructors : List NormalizedBlockCtor) (f tail : VExpr),
      (∀ constructor ∈ constructors,
        constructor ∈ view.generation.flatCtors) →
      view.blockConstructor ∈ constructors →
      env.HasType U Γ f
        (VExpr.forallN
          (progressiveTypesAux
            (constructors.map fun constructor =>
              view.generatedProjectionMinorType constructor fieldSort levels
                params
                (view.projectionMotives levels params fieldSort typeFn)) 0)
          tail) →
      env.IsType U Γ
        (view.generatedProjectionMinorType view.blockConstructor fieldSort
          levels params
          (view.projectionMotives levels params fieldSort typeFn))
  | [], _, _, _, hselected, _ => by simp at hselected
  | constructor :: constructors, f, tail, hsub, hselected, hf => by
      let motives := view.projectionMotives levels params fieldSort typeFn
      let exactMinor := view.generatedProjectionMinorType constructor
        fieldSort levels params motives
      have hcursor := hf.isType henv hΓ
      have hminorIsType : env.IsType U Γ exactMinor := by
        have hout := (hcursor.forallE_inv henv.ordered).1
        simpa [progressiveTypesAux, exactMinor, motives] using hout
      by_cases selected : constructor.owner = view.family.view.ordinal
      · have hconstructorEq := view.eq_blockConstructor_of_owner
          (hsub constructor (.head _)) selected
        subst constructor
        simpa [exactMinor, motives] using hminorIsType
      · have hidentity := self.identityMinor_hasType_of_isType henv hΓ
          (hsub constructor (.head _)) selected fieldSort hfieldSort levels
          hlevels hlevelsLength params hparamsLength paramsSpine typeFn
          (by simpa [exactMinor, motives] using hminorIsType)
        have hidentity' : env.HasType U Γ
            (view.identityMinor constructor fieldSort levels params motives)
            (exactMinor.liftN 0) := by
          simpa [exactMinor, motives] using hidentity
        have hnext := hf.app hidentity'
        simp only [List.map_cons, progressiveTypesAux,
          VExpr.instN_forallN] at hnext
        rw [progressiveTypesAux_instTelN] at hnext
        have hselectedTail : view.blockConstructor ∈ constructors := by
          rcases List.mem_cons.1 hselected with hhead | htail
          · subst constructor
            exact (selected rfl).elim
          · exact htail
        have hnext' : env.HasType U Γ
            (.app f
              (view.identityMinor constructor fieldSort levels params motives))
            (VExpr.forallN
              (progressiveTypesAux
                (constructors.map fun constructor =>
                  view.generatedProjectionMinorType constructor fieldSort
                    levels params motives) 0)
              (tail.inst
                (view.identityMinor constructor fieldSort levels params motives)
                constructors.length)) := by
          simpa [motives] using hnext
        exact self.selectedMinorType_isTypeAux henv hΓ fieldSort hfieldSort
          levels hlevels hlevelsLength params hparamsLength paramsSpine typeFn
          constructors
          (.app f
            (view.identityMinor constructor fieldSort levels params motives))
          (tail.inst
            (view.identityMinor constructor fieldSort levels params motives)
            constructors.length)
          (fun constructor hconstructor =>
            hsub constructor (.tail _ hconstructor)) hselectedTail
          (by simpa [motives] using hnext')

/-- The selected exact block-minor domain is a type.  Earlier flattened
constructors are consumed with their canonical dummy minors, so no
singleton-family recursor is fabricated. -/
theorem WF.projectionMinorType_isType
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (fieldSort : VLevel) (hfieldSort : fieldSort.WF U)
    (hmotiveLevel : view.generation.motiveLevel.inst
      (view.projectionLevels fieldSort levels) = fieldSort)
    {typeFn : VExpr}
    (typeFnType : env.HasType U Γ typeFn
      (.forallE (view.structureType levels params) (.sort fieldSort))) :
    env.IsType U Γ
      (view.generatedProjectionMinorType view.blockConstructor fieldSort
        levels params
        (view.projectionMotives levels params fieldSort typeFn)) := by
  let pLevels := view.projectionLevels fieldSort levels
  have hpLevelsWF : ∀ level ∈ pLevels, level.WF U :=
    view.projectionLevels_wf fieldSort levels hfieldSort hlevels
  have hpLevelsLength : pLevels.length = view.generation.recUvars :=
    view.projectionLevels_length fieldSort levels hlevelsLength
  have hrec := self.generationEnv.recursor_hasType_instL view.family_mem
    self.recursor pLevels hpLevelsWF hpLevelsLength (Γ := Γ)
  obtain ⟨tail, hspine⟩ := self.projectionMotivesRecursorSpine henv.ordered
    fieldSort hfieldSort levels hlevels hlevelsLength params hparamsLength
    paramsSpine typeFn typeFnType hmotiveLevel
  have happ := hspine.hasType_appN hrec
  rw [← progressiveTypesAux_eq_zipIdx] at happ
  apply self.selectedMinorType_isTypeAux henv hΓ fieldSort hfieldSort levels
    hlevels hlevelsLength params hparamsLength paramsSpine typeFn
    view.generation.flatCtors
    (VExpr.appN (.const view.recursorName pLevels)
      (params ++ view.projectionMotives levels params fieldSort typeFn)) tail
  · exact fun _ member => member
  · exact view.blockConstructor_mem
  · simpa [projectionMinorTypes, pLevels, recursorName] using happ

private theorem LayoutWF.selectedMinorWithType_isTypeAux
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    (fieldSort : VLevel) (hfieldSort : fieldSort.WF U)
    (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (typeFn dummyType dummyValue : VExpr)
    (dummyTypeType : env.HasType U Γ dummyType (.sort fieldSort))
    (dummyValueType : env.HasType U Γ dummyValue dummyType) :
    ∀ (constructors : List NormalizedBlockCtor) (f tail : VExpr),
      (∀ constructor ∈ constructors,
        constructor ∈ view.generation.flatCtors) →
      view.blockConstructor ∈ constructors →
      env.HasType U Γ f
        (VExpr.forallN
          (progressiveTypesAux
            (constructors.map fun constructor =>
              view.generatedProjectionMinorType constructor fieldSort levels
                params
                (view.projectionMotivesWith levels params typeFn
                  dummyType)) 0)
          tail) →
      env.IsType U Γ
        (view.generatedProjectionMinorType view.blockConstructor fieldSort
          levels params
          (view.projectionMotivesWith levels params typeFn dummyType))
  | [], _, _, _, hselected, _ => by simp at hselected
  | constructor :: constructors, f, tail, hsub, hselected, hf => by
      let motives := view.projectionMotivesWith levels params typeFn dummyType
      let exactMinor := view.generatedProjectionMinorType constructor
        fieldSort levels params motives
      have hcursor := hf.isType henv hΓ
      have hminorIsType : env.IsType U Γ exactMinor := by
        have hout := (hcursor.forallE_inv henv.ordered).1
        simpa [progressiveTypesAux, exactMinor, motives] using hout
      by_cases selected : constructor.owner = view.family.view.ordinal
      · have hconstructorEq := view.eq_blockConstructor_of_owner
          (hsub constructor (.head _)) selected
        subst constructor
        simpa [exactMinor, motives] using hminorIsType
      · have hidentity := self.identityMinorWith_hasType_of_isType henv hΓ
          (hsub constructor (.head _)) selected fieldSort levels hlevels
          hlevelsLength params hparamsLength paramsSpine typeFn dummyType
          dummyValue dummyTypeType dummyValueType
          (by simpa [exactMinor, motives] using hminorIsType)
        have hidentity' : env.HasType U Γ
            (view.identityMinorWith constructor fieldSort levels params
              motives dummyValue)
            (exactMinor.liftN 0) := by
          simpa [exactMinor, motives] using hidentity
        have hnext := hf.app hidentity'
        simp only [List.map_cons, progressiveTypesAux,
          VExpr.instN_forallN] at hnext
        rw [progressiveTypesAux_instTelN] at hnext
        have hselectedTail : view.blockConstructor ∈ constructors := by
          rcases List.mem_cons.1 hselected with hhead | htail
          · subst constructor
            exact (selected rfl).elim
          · exact htail
        have hnext' : env.HasType U Γ
            (.app f
              (view.identityMinorWith constructor fieldSort levels params
                motives dummyValue))
            (VExpr.forallN
              (progressiveTypesAux
                (constructors.map fun constructor =>
                  view.generatedProjectionMinorType constructor fieldSort
                    levels params motives) 0)
              (tail.inst
                (view.identityMinorWith constructor fieldSort levels params
                  motives dummyValue)
                constructors.length)) := by
          simpa [motives] using hnext
        exact self.selectedMinorWithType_isTypeAux henv hΓ fieldSort
          hfieldSort levels hlevels hlevelsLength params hparamsLength
          paramsSpine typeFn dummyType dummyValue dummyTypeType
          dummyValueType constructors
          (.app f
            (view.identityMinorWith constructor fieldSort levels params
              motives dummyValue))
          (tail.inst
            (view.identityMinorWith constructor fieldSort levels params
              motives dummyValue)
            constructors.length)
          (fun constructor hconstructor =>
            hsub constructor (.tail _ hconstructor)) hselectedTail
          (by simpa [motives] using hnext')

theorem LayoutWF.projectionMinorWithType_isType
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (fieldSort : VLevel) (hfieldSort : fieldSort.WF U)
    (hmotiveLevel : view.generation.motiveLevel.inst
      (view.projectionLevels fieldSort levels) = fieldSort)
    {typeFn dummyType dummyValue : VExpr}
    (typeFnType : env.HasType U Γ typeFn
      (.forallE (view.structureType levels params) (.sort fieldSort)))
    (dummyTypeType : env.HasType U Γ dummyType (.sort fieldSort))
    (dummyValueType : env.HasType U Γ dummyValue dummyType) :
    env.IsType U Γ
      (view.generatedProjectionMinorType view.blockConstructor fieldSort
        levels params
        (view.projectionMotivesWith levels params typeFn dummyType)) := by
  let pLevels := view.projectionLevels fieldSort levels
  have hpLevelsWF : ∀ level ∈ pLevels, level.WF U :=
    view.projectionLevels_wf fieldSort levels hfieldSort hlevels
  have hpLevelsLength : pLevels.length = view.generation.recUvars :=
    view.projectionLevels_length fieldSort levels hlevelsLength
  have hrec := self.generationEnv.recursor_hasType_instL view.family_mem
    self.recursor pLevels hpLevelsWF hpLevelsLength (Γ := Γ)
  obtain ⟨tail, hspine⟩ := self.projectionMotivesWithRecursorSpine
    henv.ordered fieldSort levels hlevels hlevelsLength params hparamsLength
    paramsSpine typeFn dummyType typeFnType dummyTypeType hmotiveLevel
  have happ := hspine.hasType_appN hrec
  rw [← progressiveTypesAux_eq_zipIdx] at happ
  apply self.selectedMinorWithType_isTypeAux henv hΓ fieldSort hfieldSort
    levels hlevels hlevelsLength params hparamsLength paramsSpine typeFn
    dummyType dummyValue dummyTypeType dummyValueType
    view.generation.flatCtors
    (VExpr.appN (.const view.recursorName pLevels)
      (params ++ view.projectionMotivesWith levels params typeFn dummyType))
    tail
  · exact fun _ member => member
  · exact view.blockConstructor_mem
  · simpa [projectionMinorTypes, pLevels, recursorName] using happ

/-- Traverse the complete flattened constructor inventory, assigning the
selected field minor to the selected constructor and canonical identity
minors everywhere else.  The progressive generated telescope itself supplies
the well-formedness proof for each exact minor domain. -/
private theorem WF.projectionMinors_forall₂_hasTypeAux
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    (fieldSort : VLevel) (hfieldSort : fieldSort.WF U)
    (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (typeFn : VExpr) (fieldIndex : Nat)
    (selectedMinorType : env.HasType U Γ
      (view.projectionMinor view.blockConstructor fieldSort levels params
        (view.specializedFields levels params)
        (view.projectionMotives levels params fieldSort typeFn) fieldIndex)
      (view.generatedProjectionMinorType view.blockConstructor fieldSort
        levels params
        (view.projectionMotives levels params fieldSort typeFn))) :
    ∀ (constructors : List NormalizedBlockCtor) (f tail : VExpr),
      (∀ constructor ∈ constructors,
        constructor ∈ view.generation.flatCtors) →
      env.HasType U Γ f
        (VExpr.forallN
          (progressiveTypesAux
            (constructors.map fun constructor =>
              view.generatedProjectionMinorType constructor fieldSort levels
                params
                (view.projectionMotives levels params fieldSort typeFn)) 0)
          tail) →
      List.Forall₂ (fun argument type => env.HasType U Γ argument type)
        (constructors.map fun constructor =>
          view.projectionMinor constructor fieldSort levels params
            (view.specializedFields levels params)
            (view.projectionMotives levels params fieldSort typeFn) fieldIndex)
        (constructors.map fun constructor =>
          view.generatedProjectionMinorType constructor fieldSort levels params
            (view.projectionMotives levels params fieldSort typeFn))
  | [], _, _, _, _ => .nil
  | constructor :: constructors, f, tail, hsub, hf => by
      let motives := view.projectionMotives levels params fieldSort typeFn
      let exactMinor := view.generatedProjectionMinorType constructor
        fieldSort levels params motives
      let argument := view.projectionMinor constructor fieldSort levels params
        (view.specializedFields levels params) motives fieldIndex
      have hcursor := hf.isType henv hΓ
      have hminorIsType : env.IsType U Γ exactMinor := by
        have hout := (hcursor.forallE_inv henv.ordered).1
        simpa [progressiveTypesAux, exactMinor, motives] using hout
      have hargument : env.HasType U Γ argument exactMinor := by
        by_cases selected : constructor.owner = view.family.view.ordinal
        · have hconstructorEq := view.eq_blockConstructor_of_owner
            (hsub constructor (.head _)) selected
          subst constructor
          simpa [argument, exactMinor, motives, projectionMinor] using
            selectedMinorType
        · have hidentity := self.identityMinor_hasType_of_isType henv hΓ
            (hsub constructor (.head _)) selected fieldSort hfieldSort levels
            hlevels hlevelsLength params hparamsLength paramsSpine typeFn
            (by simpa [exactMinor, motives] using hminorIsType)
          simpa [argument, exactMinor, motives, projectionMinor, selected] using
            hidentity
      have hargument' : env.HasType U Γ argument (exactMinor.liftN 0) := by
        simpa [exactMinor] using hargument
      have hnext := hf.app hargument'
      simp only [List.map_cons, progressiveTypesAux,
        VExpr.instN_forallN] at hnext
      rw [progressiveTypesAux_instTelN] at hnext
      have hnext' : env.HasType U Γ (.app f argument)
          (VExpr.forallN
            (progressiveTypesAux
              (constructors.map fun constructor =>
                view.generatedProjectionMinorType constructor fieldSort levels
                  params motives) 0)
            (tail.inst argument constructors.length)) := by
        simpa [argument, exactMinor, motives] using hnext
      exact .cons (by simpa [argument, exactMinor, motives] using hargument)
        (self.projectionMinors_forall₂_hasTypeAux henv hΓ fieldSort
          hfieldSort levels hlevels hlevelsLength params hparamsLength
          paramsSpine typeFn fieldIndex selectedMinorType constructors
          (.app f argument) (tail.inst argument constructors.length)
          (fun constructor hconstructor =>
            hsub constructor (.tail _ hconstructor))
          (by simpa [motives] using hnext'))

/-- The exact complete mutual-minor list used by one block-backed projector
is pointwise well typed. -/
private theorem WF.projectionMinors_forall₂_hasType
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    (fieldSort : VLevel) (hfieldSort : fieldSort.WF U)
    (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (typeFn : VExpr) (fieldIndex : Nat)
    (typeFnType : env.HasType U Γ typeFn
      (.forallE (view.structureType levels params) (.sort fieldSort)))
    (hmotiveLevel : view.generation.motiveLevel.inst
      (view.projectionLevels fieldSort levels) = fieldSort)
    (selectedMinorType : env.HasType U Γ
      (view.projectionMinor view.blockConstructor fieldSort levels params
        (view.specializedFields levels params)
        (view.projectionMotives levels params fieldSort typeFn) fieldIndex)
      (view.generatedProjectionMinorType view.blockConstructor fieldSort
        levels params
        (view.projectionMotives levels params fieldSort typeFn))) :
    List.Forall₂ (fun argument type => env.HasType U Γ argument type)
      (view.generation.flatCtors.map fun constructor =>
        view.projectionMinor constructor fieldSort levels params
          (view.specializedFields levels params)
          (view.projectionMotives levels params fieldSort typeFn) fieldIndex)
      (view.projectionMinorTypes fieldSort levels params
        (view.projectionMotives levels params fieldSort typeFn)) := by
  let pLevels := view.projectionLevels fieldSort levels
  have hpLevelsWF : ∀ level ∈ pLevels, level.WF U :=
    view.projectionLevels_wf fieldSort levels hfieldSort hlevels
  have hpLevelsLength : pLevels.length = view.generation.recUvars :=
    view.projectionLevels_length fieldSort levels hlevelsLength
  have hrec := self.generationEnv.recursor_hasType_instL view.family_mem
    self.recursor pLevels hpLevelsWF hpLevelsLength (Γ := Γ)
  obtain ⟨tail, hspine⟩ := self.projectionMotivesRecursorSpine henv.ordered
    fieldSort hfieldSort levels hlevels hlevelsLength params hparamsLength
    paramsSpine typeFn typeFnType hmotiveLevel
  have happ := hspine.hasType_appN hrec
  rw [← progressiveTypesAux_eq_zipIdx] at happ
  exact self.projectionMinors_forall₂_hasTypeAux henv hΓ fieldSort
    hfieldSort levels hlevels hlevelsLength params hparamsLength paramsSpine
    typeFn fieldIndex selectedMinorType view.generation.flatCtors
    (VExpr.appN (.const view.recursorName pLevels)
      (params ++ view.projectionMotives levels params fieldSort typeFn)) tail
    (fun _ member => member)
    (by simpa [projectionMinorTypes, pLevels, recursorName] using happ)

private theorem LayoutWF.projectionMinorsWith_forall₂_hasTypeAux
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    (fieldSort : VLevel) (hfieldSort : fieldSort.WF U)
    (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (typeFn dummyType dummyValue : VExpr) (fieldIndex : Nat)
    (dummyTypeType : env.HasType U Γ dummyType (.sort fieldSort))
    (dummyValueType : env.HasType U Γ dummyValue dummyType)
    (selectedMinorType : env.HasType U Γ
      (view.projectionMinorWith view.blockConstructor fieldSort levels params
        (view.specializedFields levels params)
        (view.projectionMotivesWith levels params typeFn dummyType)
        fieldIndex dummyValue)
      (view.generatedProjectionMinorType view.blockConstructor fieldSort
        levels params
        (view.projectionMotivesWith levels params typeFn dummyType))) :
    ∀ (constructors : List NormalizedBlockCtor) (f tail : VExpr),
      (∀ constructor ∈ constructors,
        constructor ∈ view.generation.flatCtors) →
      env.HasType U Γ f
        (VExpr.forallN
          (progressiveTypesAux
            (constructors.map fun constructor =>
              view.generatedProjectionMinorType constructor fieldSort levels
                params
                (view.projectionMotivesWith levels params typeFn
                  dummyType)) 0)
          tail) →
      List.Forall₂ (fun argument type => env.HasType U Γ argument type)
        (constructors.map fun constructor =>
          view.projectionMinorWith constructor fieldSort levels params
            (view.specializedFields levels params)
            (view.projectionMotivesWith levels params typeFn dummyType)
            fieldIndex dummyValue)
        (constructors.map fun constructor =>
          view.generatedProjectionMinorType constructor fieldSort levels params
            (view.projectionMotivesWith levels params typeFn dummyType))
  | [], _, _, _, _ => .nil
  | constructor :: constructors, f, tail, hsub, hf => by
      let motives := view.projectionMotivesWith levels params typeFn dummyType
      let exactMinor := view.generatedProjectionMinorType constructor
        fieldSort levels params motives
      let argument := view.projectionMinorWith constructor fieldSort levels
        params (view.specializedFields levels params) motives fieldIndex
        dummyValue
      have hcursor := hf.isType henv hΓ
      have hminorIsType : env.IsType U Γ exactMinor := by
        have hout := (hcursor.forallE_inv henv.ordered).1
        simpa [progressiveTypesAux, exactMinor, motives] using hout
      have hargument : env.HasType U Γ argument exactMinor := by
        by_cases selected : constructor.owner = view.family.view.ordinal
        · have hconstructorEq := view.eq_blockConstructor_of_owner
            (hsub constructor (.head _)) selected
          subst constructor
          simpa [argument, exactMinor, motives, projectionMinorWith] using
            selectedMinorType
        · have hidentity := self.identityMinorWith_hasType_of_isType henv
            hΓ (hsub constructor (.head _)) selected fieldSort levels
            hlevels hlevelsLength params hparamsLength paramsSpine typeFn
            dummyType dummyValue dummyTypeType dummyValueType
            (by simpa [exactMinor, motives] using hminorIsType)
          simpa [argument, exactMinor, motives, projectionMinorWith,
            selected] using hidentity
      have hargument' : env.HasType U Γ argument (exactMinor.liftN 0) := by
        simpa [exactMinor] using hargument
      have hnext := hf.app hargument'
      simp only [List.map_cons, progressiveTypesAux,
        VExpr.instN_forallN] at hnext
      rw [progressiveTypesAux_instTelN] at hnext
      have hnext' : env.HasType U Γ (.app f argument)
          (VExpr.forallN
            (progressiveTypesAux
              (constructors.map fun constructor =>
                view.generatedProjectionMinorType constructor fieldSort levels
                  params motives) 0)
            (tail.inst argument constructors.length)) := by
        simpa [argument, exactMinor, motives] using hnext
      exact .cons (by simpa [argument, exactMinor, motives] using hargument)
        (self.projectionMinorsWith_forall₂_hasTypeAux henv hΓ fieldSort
          hfieldSort levels hlevels hlevelsLength params hparamsLength
          paramsSpine typeFn dummyType dummyValue fieldIndex dummyTypeType
          dummyValueType selectedMinorType constructors (.app f argument)
          (tail.inst argument constructors.length)
          (fun constructor hconstructor =>
            hsub constructor (.tail _ hconstructor))
          (by simpa [motives] using hnext'))

private theorem LayoutWF.projectionMinorsWith_forall₂_hasType
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    (fieldSort : VLevel) (hfieldSort : fieldSort.WF U)
    (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (typeFn dummyType dummyValue : VExpr) (fieldIndex : Nat)
    (typeFnType : env.HasType U Γ typeFn
      (.forallE (view.structureType levels params) (.sort fieldSort)))
    (dummyTypeType : env.HasType U Γ dummyType (.sort fieldSort))
    (dummyValueType : env.HasType U Γ dummyValue dummyType)
    (hmotiveLevel : view.generation.motiveLevel.inst
      (view.projectionLevels fieldSort levels) = fieldSort)
    (selectedMinorType : env.HasType U Γ
      (view.projectionMinorWith view.blockConstructor fieldSort levels params
        (view.specializedFields levels params)
        (view.projectionMotivesWith levels params typeFn dummyType)
        fieldIndex dummyValue)
      (view.generatedProjectionMinorType view.blockConstructor fieldSort
        levels params
        (view.projectionMotivesWith levels params typeFn dummyType))) :
    List.Forall₂ (fun argument type => env.HasType U Γ argument type)
      (view.generation.flatCtors.map fun constructor =>
        view.projectionMinorWith constructor fieldSort levels params
          (view.specializedFields levels params)
          (view.projectionMotivesWith levels params typeFn dummyType)
          fieldIndex dummyValue)
      (view.projectionMinorTypes fieldSort levels params
        (view.projectionMotivesWith levels params typeFn dummyType)) := by
  let pLevels := view.projectionLevels fieldSort levels
  have hpLevelsWF : ∀ level ∈ pLevels, level.WF U :=
    view.projectionLevels_wf fieldSort levels hfieldSort hlevels
  have hpLevelsLength : pLevels.length = view.generation.recUvars :=
    view.projectionLevels_length fieldSort levels hlevelsLength
  have hrec := self.generationEnv.recursor_hasType_instL view.family_mem
    self.recursor pLevels hpLevelsWF hpLevelsLength (Γ := Γ)
  obtain ⟨tail, hspine⟩ := self.projectionMotivesWithRecursorSpine
    henv.ordered fieldSort levels hlevels hlevelsLength params hparamsLength
    paramsSpine typeFn dummyType typeFnType dummyTypeType hmotiveLevel
  have happ := hspine.hasType_appN hrec
  rw [← progressiveTypesAux_eq_zipIdx] at happ
  exact self.projectionMinorsWith_forall₂_hasTypeAux henv hΓ fieldSort
    hfieldSort levels hlevels hlevelsLength params hparamsLength paramsSpine
    typeFn dummyType dummyValue fieldIndex dummyTypeType dummyValueType
    selectedMinorType view.generation.flatCtors
    (VExpr.appN (.const view.recursorName pLevels)
      (params ++ view.projectionMotivesWith levels params typeFn dummyType))
    tail (fun _ member => member)
    (by simpa [projectionMinorTypes, pLevels, recursorName] using happ)

/-- Parameters, all mutual motives, and all flattened minors consume the
complete common prefix of the actual selected-family recursor. -/
private theorem WF.projectionCommonSpine
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    (fieldSort : VLevel) (hfieldSort : fieldSort.WF U)
    (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (typeFn : VExpr) (fieldIndex : Nat)
    (typeFnType : env.HasType U Γ typeFn
      (.forallE (view.structureType levels params) (.sort fieldSort)))
    (hmotiveLevel : view.generation.motiveLevel.inst
      (view.projectionLevels fieldSort levels) = fieldSort)
    (selectedMinorType : env.HasType U Γ
      (view.projectionMinor view.blockConstructor fieldSort levels params
        (view.specializedFields levels params)
        (view.projectionMotives levels params fieldSort typeFn) fieldIndex)
      (view.generatedProjectionMinorType view.blockConstructor fieldSort
        levels params
        (view.projectionMotives levels params fieldSort typeFn))) :
    let motives := view.projectionMotives levels params fieldSort typeFn
    let minors := view.generation.flatCtors.map fun constructor =>
      view.projectionMinor constructor fieldSort levels params
        (view.specializedFields levels params) motives fieldIndex
    env.SpineWF U Γ
      ((view.generation.recType view.family).instL
        (view.projectionLevels fieldSort levels))
      (params ++ motives ++ minors)
      (.forallE (view.structureType levels params)
        (.app typeFn.lift (.bvar 0))) := by
  let gen := view.generation
  let pLevels := view.projectionLevels fieldSort levels
  let motives := view.projectionMotives levels params fieldSort typeFn
  let minors := gen.flatCtors.map fun constructor =>
    view.projectionMinor constructor fieldSort levels params
      (view.specializedFields levels params) motives fieldIndex
  obtain ⟨tail, hmotives⟩ := self.projectionMotivesRecursorSpine
    henv.ordered fieldSort hfieldSort levels hlevels hlevelsLength params
    hparamsLength paramsSpine typeFn typeFnType hmotiveLevel
  have hminorTypes := self.projectionMinors_forall₂_hasType henv hΓ
    fieldSort hfieldSort levels hlevels hlevelsLength params hparamsLength
    paramsSpine typeFn fieldIndex typeFnType hmotiveLevel selectedMinorType
  have hminorSpine := VEnv.SpineWF.of_progressive
    (tail := tail) hminorTypes
  rw [progressiveTypesAux_eq_zipIdx] at hminorSpine
  have hcombined := hmotives.append hminorSpine
  have hcommonLength : (params ++ motives ++ minors).length =
      (gen.ruleCommonBinders.map (VExpr.instL pLevels)).length := by
    simp [motives, minors, gen, hparamsLength,
      view.generation.ruleCommonBinders_length,
      BlockGenerationChecked.minorCount]
    change view.source.nparams +
        (view.generation.familyCount + view.generation.flatCtors.length) =
      view.source.nparams + view.generation.familyCount +
        view.generation.flatCtors.length
    omega
  have hgeneric := hcombined
  rw [gen.recType_instL_common] at hgeneric
  have hretarget := hgeneric.retarget hcommonLength
    (VExpr.forallN
      ((gen.recIndexBinders view.family).map (VExpr.instL pLevels))
      (.forallE ((gen.recMajorDomain view.family).instL pLevels)
        ((gen.recMotiveResult view.family).instL pLevels)))
  have hidxTel : gen.idxTel view.family = [] := by
    simp [BlockGenerationChecked.idxTel, view.raw_indices_eq]
  have hindices : gen.recIndexBinders view.family = [] := by
    unfold BlockGenerationChecked.recIndexBinders
    rw [hidxTel]
    rfl
  have hsource := view.sourceLevels_projectionLevels fieldSort levels
    hlevelsLength
  let commonArgs := params ++ motives ++ minors
  have hparamsSource : params.length = view.source.nparams := by
    change params.length = view.source.nparams
    exact hparamsLength
  have hcommonArity : commonArgs.length =
      view.source.nparams + gen.familyCount + gen.minorCount := by
    simp [commonArgs, motives, minors, gen, hparamsLength,
      BlockGenerationChecked.minorCount]
    change view.source.nparams +
        (view.generation.familyCount + view.generation.flatCtors.length) =
      view.source.nparams + view.generation.familyCount +
        view.generation.flatCtors.length
    omega
  have hcommonArity' : commonArgs.length =
      params.length + gen.familyCount + gen.minorCount := by
    rw [hcommonArity, hparamsSource]
  have hmajorDomain :
      VExpr.instRev ((gen.recMajorDomain view.family).instL pLevels)
          commonArgs =
        view.structureType levels params := by
    rw [gen.recMajorDomain_instL_instRev view.family pLevels commonArgs
      (by simpa [hidxTel] using hcommonArity)]
    rw [hsource]
    have htake : commonArgs.take view.source.nparams = params := by
      rw [← hparamsSource]
      simp [commonArgs]
    have hdrop : commonArgs.drop
        (view.source.nparams + gen.familyCount + gen.minorCount) = [] :=
      List.drop_eq_nil_iff.2 (Nat.le_of_eq hcommonArity)
    rw [htake, hdrop, List.append_nil]
    rfl
  have hmotiveAt : motives[view.family.view.ordinal]? = some typeFn := by
    simpa [motives] using view.projectionMotives_getElem?_ordinal
      view.family view.family_mem levels params fieldSort typeFn
  have hmotiveAppend :
      commonArgs[params.length + view.family.view.ordinal]? = some typeFn := by
    dsimp only [commonArgs]
    rw [getElem?_stack_mid params motives minors (by omega)
      (by simpa [motives] using view.family_ordinal_lt)]
    rw [Nat.add_sub_cancel_left, hmotiveAt]
  have hbvarIndex :
      gen.familyCount - 1 - view.family.view.ordinal + gen.minorCount +
          (gen.idxTel view.family).length + 1 =
        1 + (commonArgs.length - 1 -
          (params.length + view.family.view.ordinal)) := by
    rw [hidxTel]
    simp only [List.length_nil, Nat.add_zero]
    have hord : view.family.view.ordinal < gen.familyCount := by
      simpa [gen] using view.family_ordinal_lt
    have hremaining : commonArgs.length - 1 -
        (params.length + view.family.view.ordinal) =
      gen.familyCount + gen.minorCount - 1 -
        view.family.view.ordinal := by
      rw [hcommonArity']
      omega
    rw [hremaining]
    omega
  have hmotiveHead :
      (VExpr.bvar
        (gen.familyCount - 1 - view.family.view.ordinal + gen.minorCount +
          (gen.idxTel view.family).length + 1)).instRevAt commonArgs 1 =
        typeFn.lift := by
    rw [hbvarIndex]
    exact VExpr.instRevAt_bvar_rev_getElem? commonArgs hmotiveAppend 1
  have hmotiveResult :
      ((gen.recMotiveResult view.family).instL pLevels).instRevAt
          commonArgs 1 =
        .app typeFn.lift (.bvar 0) := by
    unfold BlockGenerationChecked.recMotiveResult
    rw [hidxTel]
    change (VExpr.appN (VExpr.bvar
        (gen.familyCount - 1 - view.family.view.ordinal + gen.minorCount +
          0 + 1)) [] |>.app (.bvar 0) |>.instL pLevels).instRevAt
            commonArgs 1 = _
    simp only [VExpr.appN, Nat.add_zero, VExpr.instL]
    change (VExpr.appN (VExpr.bvar
        (gen.familyCount - 1 - view.family.view.ordinal + gen.minorCount + 1))
          [.bvar 0]).instRevAt commonArgs 1 = _
    have hmotiveHead' :
        (VExpr.bvar (gen.familyCount - 1 - view.family.view.ordinal +
          gen.minorCount + 1)).instRevAt commonArgs 1 = typeFn.lift := by
      simpa [hidxTel] using hmotiveHead
    rw [VExpr.instRevAt_appN_projection, hmotiveHead']
    simp only [List.map_singleton]
    rw [VExpr.instRevAt_closedN commonArgs
      (C := .bvar 0) (k := 1) (by trivial)]
    rfl
  have hresult :
      (VExpr.forallN
        ((gen.recIndexBinders view.family).map (VExpr.instL pLevels))
        (.forallE ((gen.recMajorDomain view.family).instL pLevels)
          ((gen.recMotiveResult view.family).instL pLevels))).instRev
          commonArgs =
        .forallE (view.structureType levels params)
          (.app typeFn.lift (.bvar 0)) := by
    rw [hindices]
    simp only [List.map_nil, VExpr.forallN,
      VExpr.instRev_forallE_projection]
    rw [hmajorDomain, hmotiveResult]
  rw [gen.recType_instL_common]
  rw [hindices]
  rw [hresult] at hretarget
  simpa [commonArgs, motives, minors, hindices] using hretarget

/-- The actual mutual recursor, supplied with every dummy and selecting
minor, implements one dependent selected-family projection. -/
theorem WF.recursorProjection_hasType
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    (fieldSort : VLevel) (hfieldSort : fieldSort.WF U)
    (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (typeFn : VExpr) (fieldIndex : Nat)
    (typeFnType : env.HasType U Γ typeFn
      (.forallE (view.structureType levels params) (.sort fieldSort)))
    (hmotiveLevel : view.generation.motiveLevel.inst
      (view.projectionLevels fieldSort levels) = fieldSort)
    (selectedMinorType : env.HasType U Γ
      (view.projectionMinor view.blockConstructor fieldSort levels params
        (view.specializedFields levels params)
        (view.projectionMotives levels params fieldSort typeFn) fieldIndex)
      (view.generatedProjectionMinorType view.blockConstructor fieldSort
        levels params
        (view.projectionMotives levels params fieldSort typeFn)))
    {major : VExpr}
    (majorType : env.HasType U Γ major
      (view.structureType levels params)) :
    let motives := view.projectionMotives levels params fieldSort typeFn
    let minors := view.generation.flatCtors.map fun constructor =>
      view.projectionMinor constructor fieldSort levels params
        (view.specializedFields levels params) motives fieldIndex
    env.HasType U Γ
      (VExpr.appN (.const view.recursorName
        (view.projectionLevels fieldSort levels))
        (params ++ motives ++ minors ++ [major]))
      (.app typeFn major) := by
  let motives := view.projectionMotives levels params fieldSort typeFn
  let minors := view.generation.flatCtors.map fun constructor =>
    view.projectionMinor constructor fieldSort levels params
      (view.specializedFields levels params) motives fieldIndex
  let pLevels := view.projectionLevels fieldSort levels
  have hpLevelsWF : ∀ level ∈ pLevels, level.WF U :=
    view.projectionLevels_wf fieldSort levels hfieldSort hlevels
  have hpLevelsLength : pLevels.length = view.generation.recUvars :=
    view.projectionLevels_length fieldSort levels hlevelsLength
  have hrec := self.generationEnv.recursor_hasType_instL view.family_mem
    self.recursor pLevels hpLevelsWF hpLevelsLength (Γ := Γ)
  have hcommon := self.projectionCommonSpine henv hΓ fieldSort hfieldSort
    levels hlevels hlevelsLength params hparamsLength paramsSpine typeFn
    fieldIndex typeFnType hmotiveLevel selectedMinorType
  have hfull := hcommon.snoc majorType
  have hfull' : env.SpineWF U Γ
      ((view.generation.recType view.family).instL pLevels)
      (params ++ motives ++ minors ++ [major]) (.app typeFn major) := by
    simpa [motives, minors, pLevels, List.append_assoc, VExpr.inst,
      VExpr.inst_lift, VExpr.instVar_zero] using hfull
  simpa [recursorName, pLevels] using hfull'.hasType_appN hrec

private theorem LayoutWF.projectionCommonWithSpine
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    (fieldSort : VLevel) (hfieldSort : fieldSort.WF U)
    (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (typeFn dummyType dummyValue : VExpr) (fieldIndex : Nat)
    (typeFnType : env.HasType U Γ typeFn
      (.forallE (view.structureType levels params) (.sort fieldSort)))
    (dummyTypeType : env.HasType U Γ dummyType (.sort fieldSort))
    (dummyValueType : env.HasType U Γ dummyValue dummyType)
    (hmotiveLevel : view.generation.motiveLevel.inst
      (view.projectionLevels fieldSort levels) = fieldSort)
    (selectedMinorType : env.HasType U Γ
      (view.projectionMinorWith view.blockConstructor fieldSort levels params
        (view.specializedFields levels params)
        (view.projectionMotivesWith levels params typeFn dummyType)
        fieldIndex dummyValue)
      (view.generatedProjectionMinorType view.blockConstructor fieldSort
        levels params
        (view.projectionMotivesWith levels params typeFn dummyType))) :
    let motives := view.projectionMotivesWith levels params typeFn dummyType
    let minors := view.generation.flatCtors.map fun constructor =>
      view.projectionMinorWith constructor fieldSort levels params
        (view.specializedFields levels params) motives fieldIndex dummyValue
    env.SpineWF U Γ
      ((view.generation.recType view.family).instL
        (view.projectionLevels fieldSort levels))
      (params ++ motives ++ minors)
      (.forallE (view.structureType levels params)
        (.app typeFn.lift (.bvar 0))) := by
  let gen := view.generation
  let pLevels := view.projectionLevels fieldSort levels
  let motives := view.projectionMotivesWith levels params typeFn dummyType
  let minors := gen.flatCtors.map fun constructor =>
    view.projectionMinorWith constructor fieldSort levels params
      (view.specializedFields levels params) motives fieldIndex dummyValue
  obtain ⟨tail, hmotives⟩ := self.projectionMotivesWithRecursorSpine
    henv.ordered fieldSort levels hlevels hlevelsLength params hparamsLength
    paramsSpine typeFn dummyType typeFnType dummyTypeType hmotiveLevel
  have hminorTypes := self.projectionMinorsWith_forall₂_hasType henv hΓ
    fieldSort hfieldSort levels hlevels hlevelsLength params hparamsLength
    paramsSpine typeFn dummyType dummyValue fieldIndex typeFnType
    dummyTypeType dummyValueType hmotiveLevel selectedMinorType
  have hminorSpine := VEnv.SpineWF.of_progressive
    (tail := tail) hminorTypes
  rw [progressiveTypesAux_eq_zipIdx] at hminorSpine
  have hcombined := hmotives.append hminorSpine
  have hcommonLength : (params ++ motives ++ minors).length =
      (gen.ruleCommonBinders.map (VExpr.instL pLevels)).length := by
    simp [motives, minors, gen, hparamsLength,
      view.generation.ruleCommonBinders_length,
      BlockGenerationChecked.minorCount]
    change view.source.nparams +
        (view.generation.familyCount + view.generation.flatCtors.length) =
      view.source.nparams + view.generation.familyCount +
        view.generation.flatCtors.length
    omega
  have hgeneric := hcombined
  rw [gen.recType_instL_common] at hgeneric
  have hretarget := hgeneric.retarget hcommonLength
    (VExpr.forallN
      ((gen.recIndexBinders view.family).map (VExpr.instL pLevels))
      (.forallE ((gen.recMajorDomain view.family).instL pLevels)
        ((gen.recMotiveResult view.family).instL pLevels)))
  have hidxTel : gen.idxTel view.family = [] := by
    simp [BlockGenerationChecked.idxTel, view.raw_indices_eq]
  have hindices : gen.recIndexBinders view.family = [] := by
    unfold BlockGenerationChecked.recIndexBinders
    rw [hidxTel]
    rfl
  have hsource := view.sourceLevels_projectionLevels fieldSort levels
    hlevelsLength
  let commonArgs := params ++ motives ++ minors
  have hparamsSource : params.length = view.source.nparams := by
    change params.length = view.source.nparams
    exact hparamsLength
  have hcommonArity : commonArgs.length =
      view.source.nparams + gen.familyCount + gen.minorCount := by
    simp [commonArgs, motives, minors, gen, hparamsLength,
      BlockGenerationChecked.minorCount]
    change view.source.nparams +
        (view.generation.familyCount + view.generation.flatCtors.length) =
      view.source.nparams + view.generation.familyCount +
        view.generation.flatCtors.length
    omega
  have hcommonArity' : commonArgs.length =
      params.length + gen.familyCount + gen.minorCount := by
    rw [hcommonArity, hparamsSource]
  have hmajorDomain :
      VExpr.instRev ((gen.recMajorDomain view.family).instL pLevels)
          commonArgs =
        view.structureType levels params := by
    rw [gen.recMajorDomain_instL_instRev view.family pLevels commonArgs
      (by simpa [hidxTel] using hcommonArity)]
    rw [hsource]
    have htake : commonArgs.take view.source.nparams = params := by
      rw [← hparamsSource]
      simp [commonArgs]
    have hdrop : commonArgs.drop
        (view.source.nparams + gen.familyCount + gen.minorCount) = [] :=
      List.drop_eq_nil_iff.2 (Nat.le_of_eq hcommonArity)
    rw [htake, hdrop, List.append_nil]
    rfl
  have hmotiveAt : motives[view.family.view.ordinal]? = some typeFn := by
    simpa [motives] using view.projectionMotivesWith_getElem?_ordinal
      view.family view.family_mem levels params typeFn dummyType
  have hmotiveAppend :
      commonArgs[params.length + view.family.view.ordinal]? = some typeFn := by
    dsimp only [commonArgs]
    rw [getElem?_stack_mid params motives minors (by omega)
      (by simpa [motives] using view.family_ordinal_lt)]
    rw [Nat.add_sub_cancel_left, hmotiveAt]
  have hbvarIndex :
      gen.familyCount - 1 - view.family.view.ordinal + gen.minorCount +
          (gen.idxTel view.family).length + 1 =
        1 + (commonArgs.length - 1 -
          (params.length + view.family.view.ordinal)) := by
    rw [hidxTel]
    simp only [List.length_nil, Nat.add_zero]
    have hord : view.family.view.ordinal < gen.familyCount := by
      simpa [gen] using view.family_ordinal_lt
    have hremaining : commonArgs.length - 1 -
        (params.length + view.family.view.ordinal) =
      gen.familyCount + gen.minorCount - 1 -
        view.family.view.ordinal := by
      rw [hcommonArity']
      omega
    rw [hremaining]
    omega
  have hmotiveHead :
      (VExpr.bvar
        (gen.familyCount - 1 - view.family.view.ordinal + gen.minorCount +
          (gen.idxTel view.family).length + 1)).instRevAt commonArgs 1 =
        typeFn.lift := by
    rw [hbvarIndex]
    exact VExpr.instRevAt_bvar_rev_getElem? commonArgs hmotiveAppend 1
  have hmotiveResult :
      ((gen.recMotiveResult view.family).instL pLevels).instRevAt
          commonArgs 1 =
        .app typeFn.lift (.bvar 0) := by
    unfold BlockGenerationChecked.recMotiveResult
    rw [hidxTel]
    change (VExpr.appN (VExpr.bvar
        (gen.familyCount - 1 - view.family.view.ordinal + gen.minorCount +
          0 + 1)) [] |>.app (.bvar 0) |>.instL pLevels).instRevAt
            commonArgs 1 = _
    simp only [VExpr.appN, Nat.add_zero, VExpr.instL]
    change (VExpr.appN (VExpr.bvar
        (gen.familyCount - 1 - view.family.view.ordinal +
          gen.minorCount + 1)) [.bvar 0]).instRevAt commonArgs 1 = _
    have hmotiveHead' :
        (VExpr.bvar (gen.familyCount - 1 - view.family.view.ordinal +
          gen.minorCount + 1)).instRevAt commonArgs 1 = typeFn.lift := by
      simpa [hidxTel] using hmotiveHead
    rw [VExpr.instRevAt_appN_projection, hmotiveHead']
    simp only [List.map_singleton]
    rw [VExpr.instRevAt_closedN commonArgs
      (C := .bvar 0) (k := 1) (by trivial)]
    rfl
  have hresult :
      (VExpr.forallN
        ((gen.recIndexBinders view.family).map (VExpr.instL pLevels))
        (.forallE ((gen.recMajorDomain view.family).instL pLevels)
          ((gen.recMotiveResult view.family).instL pLevels))).instRev
          commonArgs =
        .forallE (view.structureType levels params)
          (.app typeFn.lift (.bvar 0)) := by
    rw [hindices]
    simp only [List.map_nil, VExpr.forallN,
      VExpr.instRev_forallE_projection]
    rw [hmajorDomain, hmotiveResult]
  rw [gen.recType_instL_common]
  rw [hindices]
  rw [hresult] at hretarget
  simpa [commonArgs, motives, minors, hindices] using hretarget

/-- The prelude-free mutual recursor program implements one dependent
selected-family projection. -/
theorem LayoutWF.recursorProjectionWith_hasType
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    (fieldSort : VLevel) (hfieldSort : fieldSort.WF U)
    (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (typeFn dummyType dummyValue : VExpr) (fieldIndex : Nat)
    (typeFnType : env.HasType U Γ typeFn
      (.forallE (view.structureType levels params) (.sort fieldSort)))
    (dummyTypeType : env.HasType U Γ dummyType (.sort fieldSort))
    (dummyValueType : env.HasType U Γ dummyValue dummyType)
    (hmotiveLevel : view.generation.motiveLevel.inst
      (view.projectionLevels fieldSort levels) = fieldSort)
    (selectedMinorType : env.HasType U Γ
      (view.projectionMinorWith view.blockConstructor fieldSort levels params
        (view.specializedFields levels params)
        (view.projectionMotivesWith levels params typeFn dummyType)
        fieldIndex dummyValue)
      (view.generatedProjectionMinorType view.blockConstructor fieldSort
        levels params
        (view.projectionMotivesWith levels params typeFn dummyType)))
    {major : VExpr}
    (majorType : env.HasType U Γ major
      (view.structureType levels params)) :
    let motives := view.projectionMotivesWith levels params typeFn dummyType
    let minors := view.generation.flatCtors.map fun constructor =>
      view.projectionMinorWith constructor fieldSort levels params
        (view.specializedFields levels params) motives fieldIndex dummyValue
    env.HasType U Γ
      (VExpr.appN (.const view.recursorName
        (view.projectionLevels fieldSort levels))
        (params ++ motives ++ minors ++ [major]))
      (.app typeFn major) := by
  let motives := view.projectionMotivesWith levels params typeFn dummyType
  let minors := view.generation.flatCtors.map fun constructor =>
    view.projectionMinorWith constructor fieldSort levels params
      (view.specializedFields levels params) motives fieldIndex dummyValue
  let pLevels := view.projectionLevels fieldSort levels
  have hpLevelsWF : ∀ level ∈ pLevels, level.WF U :=
    view.projectionLevels_wf fieldSort levels hfieldSort hlevels
  have hpLevelsLength : pLevels.length = view.generation.recUvars :=
    view.projectionLevels_length fieldSort levels hlevelsLength
  have hrec := self.generationEnv.recursor_hasType_instL view.family_mem
    self.recursor pLevels hpLevelsWF hpLevelsLength (Γ := Γ)
  have hcommon := self.projectionCommonWithSpine henv hΓ fieldSort
    hfieldSort levels hlevels hlevelsLength params hparamsLength paramsSpine
    typeFn dummyType dummyValue fieldIndex typeFnType dummyTypeType
    dummyValueType hmotiveLevel selectedMinorType
  have hfull := hcommon.snoc majorType
  have hfull' : env.SpineWF U Γ
      ((view.generation.recType view.family).instL pLevels)
      (params ++ motives ++ minors ++ [major]) (.app typeFn major) := by
    simpa [motives, minors, pLevels, List.append_assoc, VExpr.inst,
      VExpr.inst_lift, VExpr.instVar_zero] using hfull
  simpa [recursorName, pLevels] using hfull'.hasType_appN hrec

/-- The selected constructor's exact generated recursive-IH telescope is
well formed after its specialized field telescope. -/
theorem LayoutWF.projectionIHTypesWith_onTel
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (fieldSort : VLevel) (hfieldSort : fieldSort.WF U)
    (hmotiveLevel : view.generation.motiveLevel.inst
      (view.projectionLevels fieldSort levels) = fieldSort)
    {typeFn dummyType dummyValue : VExpr}
    (typeFnType : env.HasType U Γ typeFn
      (.forallE (view.structureType levels params) (.sort fieldSort)))
    (dummyTypeType : env.HasType U Γ dummyType (.sort fieldSort))
    (dummyValueType : env.HasType U Γ dummyValue dummyType) :
    env.OnTel U ((view.specializedFields levels params).reverse ++ Γ)
      (view.projectionIHTypes fieldSort levels params
        (view.projectionMotivesWith levels params typeFn dummyType)) := by
  let motives := view.projectionMotivesWith levels params typeFn dummyType
  obtain ⟨minorSort, hminor⟩ := self.projectionMinorWithType_isType henv hΓ
    levels hlevels hlevelsLength params hparamsLength paramsSpine fieldSort
    hfieldSort hmotiveLevel typeFnType dummyTypeType dummyValueType
  rw [view.projectionMinorType_decompose fieldSort levels hlevelsLength
    params motives (by simp [motives])] at hminor
  obtain ⟨_, _afterFieldsSort, hafterFields⟩ :=
    VEnv.HasType.forallN_wf henv.ordered hminor
  obtain ⟨hihs, _, _⟩ :=
    VEnv.HasType.forallN_wf henv.ordered hafterFields
  exact hihs

/-- The selected constructor's exact generated recursive-IH telescope is
well formed for the legacy closed-dummy presentation. -/
theorem WF.projectionIHTypes_onTel
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (fieldSort : VLevel) (hfieldSort : fieldSort.WF U)
    (hmotiveLevel : view.generation.motiveLevel.inst
      (view.projectionLevels fieldSort levels) = fieldSort)
    {typeFn : VExpr}
    (typeFnType : env.HasType U Γ typeFn
      (.forallE (view.structureType levels params) (.sort fieldSort))) :
    env.OnTel U ((view.specializedFields levels params).reverse ++ Γ)
      (view.projectionIHTypes fieldSort levels params
        (view.projectionMotives levels params fieldSort typeFn)) := by
  let motives := view.projectionMotives levels params fieldSort typeFn
  obtain ⟨minorSort, hminor⟩ := self.projectionMinorType_isType henv hΓ
    levels hlevels hlevelsLength params hparamsLength paramsSpine fieldSort
    hfieldSort hmotiveLevel typeFnType
  rw [view.projectionMinorType_decompose fieldSort levels hlevelsLength
    params motives (by simp [motives])] at hminor
  obtain ⟨_, _afterFieldsSort, hafterFields⟩ :=
    VEnv.HasType.forallN_wf henv.ordered hminor
  obtain ⟨hihs, _, _⟩ :=
    VEnv.HasType.forallN_wf henv.ordered hafterFields
  exact hihs

/-- For the selected unindexed family, the terminal generated-minor
argument list is exactly the selected constructor application, weakened
beneath the generated recursive-IH telescope. -/
private theorem LayoutWF.generatedProjectionMinorArguments_selected
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (fieldSort : VLevel)
    (levels : List VLevel) (hlevelsLength : levels.length = view.uvars)
    (params motives : List VExpr)
    (hparamsLength : params.length = view.nparams)
    (hmotives : motives.length = view.generation.familyCount) :
    view.generatedProjectionMinorArguments view.blockConstructor fieldSort
        levels params motives =
      [(view.projectionConstructorApp levels params
          (view.specializedFields levels params)).liftN
        (view.projectionIHTypes fieldSort levels params motives).length] := by
  let fields := view.specializedFields levels params
  let m := fields.length
  let r := view.constructor.view.recursive.length
  have hrawFieldsLength :
      (view.blockConstructor.ctor.fieldsR view.uvars view.nparams
        view.generation.elimination).length = m := by
    simp [fields, m, specializedFields, VBlockStructureView.fields,
      blockConstructor, NormalizedCtor.fieldsR]
  have hrecArgsLength :
      (view.blockConstructor.ctor.recArgsR view.uvars
        view.generation.elimination).length = r := by
    simp [r, blockConstructor, NormalizedCtor.recArgsR]
  have hihsLength :
      (view.projectionIHTypes fieldSort levels params motives).length = r := by
    simpa [r] using view.projectionIHTypes_length fieldSort levels
      hlevelsLength params motives hmotives
  have hresultIndices : view.constructor.view.resultIndices = [] := by
    apply List.length_eq_zero_iff.1
    have hlength : view.constructor.view.resultIndices.length =
        view.family.view.indices.length := by
      simpa [blockConstructor] using
        self.generationEnv.viewResultIndices_length
          view.blockConstructor_mem
    rw [hlength, view.checked_indices_eq]
    rfl
  have hsource := view.sourceLevels_projectionLevels fieldSort levels
    hlevelsLength
  have hparamsRange :
      (VExpr.bvarRevRange (r + m + view.generation.familyCount)
          view.nparams).map
        (fun expression => expression.instRevAt (params ++ motives) (m + r)) =
      params.map (VExpr.liftN (m + r)) := by
    have hout := VExpr.map_instRevAt_bvarRevRange_prefix
      params motives (m + r)
    rw [hparamsLength, hmotives] at hout
    rw [show r + m + view.generation.familyCount =
      m + r + view.generation.familyCount by omega]
    exact hout
  have hfieldsRange :
      (VExpr.bvarRevRange r m).map
        (fun expression => expression.instRevAt (params ++ motives) (m + r)) =
      VExpr.bvarRevRange r m := by
    calc
      _ = (VExpr.bvarRevRange r m).map id := by
        apply List.map_congr_left
        intro expression hexpression
        apply VExpr.instRevAt_closedN
        exact bvarRevRange_closedN m r (m + r) (by omega)
          expression hexpression
      _ = _ := by simp
  unfold generatedProjectionMinorArguments
  dsimp only
  rw [hrawFieldsLength, hrecArgsLength]
  simp only [blockConstructor, NormalizedCtor.resultIndicesR,
    hresultIndices, List.map_nil, List.nil_append, List.map_singleton,
    VExpr.instL_appN, VExpr.instL, List.map_append,
    VExpr.bvarRevRange_map_instL]
  rw [hsource, VExpr.instRevAt_appN_projection,
    VExpr.instRevAt_closedN (params ++ motives) (by trivial),
    List.map_append, hparamsRange, hfieldsRange]
  rw [hihsLength]
  simp only [projectionConstructorApp, fields, m, r, VExpr.liftN,
    VExpr.liftN_appN, VExpr.bvarRevRange_liftN_low,
    List.map_append, List.map_map, Function.comp_def]
  rw [Nat.add_zero]
  congr 1
  apply congrArg (VExpr.appN (.const view.constructorName levels))
  congr 1
  apply List.map_congr_left
  intro param _
  rw [VExpr.liftN_liftN]

private theorem LayoutWF.projectionMinorResult_eq_lift_of_motive
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (fieldSort : VLevel)
    (levels : List VLevel) (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (motives : List VExpr) (typeFn : VExpr)
    (hmotives : motives.length = view.generation.familyCount)
    (hmotive : motives[view.family.view.ordinal]? = some typeFn) :
    let fields := view.specializedFields levels params
    let ihs := view.projectionIHTypes fieldSort levels params motives
    VExpr.dropN ihs.length (VExpr.dropN fields.length
      (view.generatedProjectionMinorType view.blockConstructor fieldSort
        levels params motives)) =
      (VExpr.app (typeFn.liftN fields.length)
        (view.projectionConstructorApp levels params fields)).liftN
          ihs.length := by
  let fields := view.specializedFields levels params
  let ihs := view.projectionIHTypes fieldSort levels params motives
  have hresultLength : view.constructor.view.resultIndices.length =
      view.family.view.indices.length := by
    simpa [blockConstructor] using
      self.generationEnv.viewResultIndices_length view.blockConstructor_mem
  have hresult := view.generatedProjectionMinorResult_motive
    view.blockConstructor view.family rfl hresultLength fieldSort levels
    params motives typeFn hmotives hmotive |>.2
  have hfieldsLength :
      (view.specializedCtorFields view.blockConstructor levels params).length =
        fields.length := by
    simp [specializedCtorFields, specializedFields, fields,
      VBlockStructureView.fields, blockConstructor]
  have hihsLength : ihs.length = view.constructor.view.recursive.length := by
    simpa [ihs] using view.projectionIHTypes_length fieldSort levels
      hlevelsLength params motives hmotives
  have hblockRecursive :
      view.blockConstructor.ctor.view.recursive.length =
        view.constructor.view.recursive.length := rfl
  rw [hfieldsLength, hblockRecursive, ← hihsLength] at hresult
  dsimp only
  rw [VExpr.dropN_add_local]
  rw [hresult]
  rw [self.generatedProjectionMinorArguments_selected fieldSort levels
    hlevelsLength params motives hparamsLength hmotives]
  simp only [VExpr.appN, VExpr.liftN, VExpr.liftN_liftN]
  simpa only [fields, ihs]

/-- The selected generated-minor result is the field-context motive result
weakened beneath every exact recursive-IH binder. -/
theorem LayoutWF.projectionMinorResult_eq_lift
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (fieldSort : VLevel)
    (levels : List VLevel) (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (typeFn : VExpr) :
    let motives := view.projectionMotives levels params fieldSort typeFn
    let fields := view.specializedFields levels params
    let ihs := view.projectionIHTypes fieldSort levels params motives
    VExpr.dropN ihs.length (VExpr.dropN fields.length
      (view.generatedProjectionMinorType view.blockConstructor fieldSort
        levels params motives)) =
      (VExpr.app (typeFn.liftN fields.length)
        (view.projectionConstructorApp levels params fields)).liftN
          ihs.length := by
  let motives := view.projectionMotives levels params fieldSort typeFn
  apply self.projectionMinorResult_eq_lift_of_motive fieldSort levels
    hlevelsLength params hparamsLength motives typeFn
  · simp [motives]
  · simpa [motives] using view.projectionMotives_getElem?_ordinal
      view.family view.family_mem levels params fieldSort typeFn

/-- The same selected-result equation for motives using the major-local
operational dummy carrier. -/
theorem LayoutWF.projectionMinorWithResult_eq_lift
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (fieldSort : VLevel)
    (levels : List VLevel) (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (typeFn dummyType : VExpr) :
    let motives := view.projectionMotivesWith levels params typeFn dummyType
    let fields := view.specializedFields levels params
    let ihs := view.projectionIHTypes fieldSort levels params motives
    VExpr.dropN ihs.length (VExpr.dropN fields.length
      (view.generatedProjectionMinorType view.blockConstructor fieldSort
        levels params motives)) =
      (VExpr.app (typeFn.liftN fields.length)
        (view.projectionConstructorApp levels params fields)).liftN
          ihs.length := by
  let motives := view.projectionMotivesWith levels params typeFn dummyType
  apply self.projectionMinorResult_eq_lift_of_motive fieldSort levels
    hlevelsLength params hparamsLength motives typeFn
  · simp [motives]
  · simpa [motives] using view.projectionMotivesWith_getElem?_ordinal
      view.family view.family_mem levels params typeFn dummyType

private theorem ProjectionSyntaxWF.projectionIHTypes_liftN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.ProjectionSyntaxWF env) (fieldSort : VLevel)
    (levels : List VLevel)
    (params motives : List VExpr)
    (hparams : params.length = view.nparams)
    (hmotives : motives.length = view.generation.familyCount)
    (n k : Nat) :
    VExpr.liftTelN n (view.projectionIHTypes fieldSort levels params motives)
        (k + (view.specializedFields levels params).length) =
      view.projectionIHTypes fieldSort levels
        (params.map fun param => param.liftN n k)
        (motives.map fun motive => motive.liftN n k) := by
  let fields := view.specializedFields levels params
  let params' := params.map fun param => param.liftN n k
  let motives' := motives.map fun motive => motive.liftN n k
  let fields' := view.specializedFields levels params'
  let exactMinor := view.generatedProjectionMinorType view.blockConstructor
    fieldSort levels params motives
  have hfields : fields' = VExpr.liftTelN n fields k := by
    simpa [fields, fields', params'] using
      self.specializedFields_liftN levels params hparams n k
  have hfieldsLength : fields'.length = fields.length := by
    rw [hfields, VExpr.liftTelN_length]
  have hminor : exactMinor.liftN n k =
      view.generatedProjectionMinorType view.blockConstructor fieldSort levels
        params' motives' := by
    simpa [exactMinor, params', motives'] using
      self.generatedProjectionMinorType_liftN view.blockConstructor_mem
        fieldSort levels params motives hparams hmotives n k
  obtain ⟨fieldBinders, ihBinders, body, hfieldBinders, _hihBinders,
      hexactShape⟩ :=
    view.generatedProjectionMinorType_telescope_shape view.blockConstructor
      fieldSort levels params motives hmotives
  have hexactShape' : exactMinor =
      VExpr.forallN fieldBinders (VExpr.forallN ihBinders body) := by
    simpa [exactMinor] using hexactShape
  have hfieldBindersLength : fieldBinders.length = fields.length := by
    simpa [fields, specializedCtorFields, specializedFields,
      VBlockStructureView.fields, blockConstructor] using hfieldBinders
  have houterLength :
      (VExpr.telN fields.length exactMinor).length = fields.length := by
    rw [hexactShape', ← hfieldBindersLength,
      VExpr.telN_forallN_length, hfieldBindersLength]
  unfold projectionIHTypes
  change VExpr.liftTelN n
      (VExpr.telN view.constructor.view.recursive.length
        (VExpr.dropN fields.length exactMinor)) (k + fields.length) =
    VExpr.telN view.constructor.view.recursive.length
      (VExpr.dropN fields'.length
        (view.generatedProjectionMinorType view.blockConstructor fieldSort levels
          params' motives'))
  rw [← hminor, hfieldsLength]
  rw [VExpr.dropN_liftN, houterLength, VExpr.telN_liftN]

private theorem ProjectionSyntaxWF.projectionIHTypes_instN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.ProjectionSyntaxWF env) (fieldSort : VLevel)
    (levels : List VLevel)
    (params motives : List VExpr)
    (hparams : params.length = view.nparams)
    (hmotives : motives.length = view.generation.familyCount)
    (a : VExpr) (k : Nat) :
    VExpr.instTelN a (view.projectionIHTypes fieldSort levels params motives)
        (k + (view.specializedFields levels params).length) =
      view.projectionIHTypes fieldSort levels
        (params.map fun param => param.inst a k)
        (motives.map fun motive => motive.inst a k) := by
  let fields := view.specializedFields levels params
  let params' := params.map fun param => param.inst a k
  let motives' := motives.map fun motive => motive.inst a k
  let fields' := view.specializedFields levels params'
  let exactMinor := view.generatedProjectionMinorType view.blockConstructor
    fieldSort levels params motives
  have hfields : fields' = VExpr.instTelN a fields k := by
    simpa [fields, fields', params'] using
      self.specializedFields_instN levels params hparams a k
  have hfieldsLength : fields'.length = fields.length := by
    rw [hfields, VExpr.instTelN_length]
  have hminor : exactMinor.inst a k =
      view.generatedProjectionMinorType view.blockConstructor fieldSort levels
        params' motives' := by
    simpa [exactMinor, params', motives'] using
      self.generatedProjectionMinorType_instN view.blockConstructor_mem
        fieldSort levels params motives hparams hmotives a k
  obtain ⟨fieldBinders, ihBinders, body, hfieldBinders, hihBinders,
      hexactShape⟩ :=
    view.generatedProjectionMinorType_telescope_shape view.blockConstructor
      fieldSort levels params motives hmotives
  have hexactShape' : exactMinor =
      VExpr.forallN fieldBinders (VExpr.forallN ihBinders body) := by
    simpa [exactMinor] using hexactShape
  have hfieldBindersLength : fieldBinders.length = fields.length := by
    simpa [fields, specializedCtorFields, specializedFields,
      VBlockStructureView.fields, blockConstructor] using hfieldBinders
  have hihBindersLength : ihBinders.length =
      view.constructor.view.recursive.length := by
    simpa [blockConstructor] using hihBinders
  have hihs :
      view.projectionIHTypes fieldSort levels params motives = ihBinders := by
    unfold projectionIHTypes
    change VExpr.telN view.constructor.view.recursive.length
      (VExpr.dropN fields.length exactMinor) = ihBinders
    rw [hexactShape', ← hfieldBindersLength,
      VExpr.dropN_forallN_length, ← hihBindersLength,
      VExpr.telN_forallN_length]
  rw [hihs]
  change VExpr.instTelN a ihBinders (k + fields.length) =
    VExpr.telN view.constructor.view.recursive.length
      (VExpr.dropN fields'.length
        (view.generatedProjectionMinorType view.blockConstructor fieldSort levels
          params' motives'))
  rw [← hminor, hfieldsLength]
  rw [hexactShape', VExpr.instN_forallN]
  rw [← hfieldBindersLength]
  rw [show fieldBinders.length =
      (VExpr.instTelN a fieldBinders k).length by
    rw [VExpr.instTelN_length]]
  rw [VExpr.dropN_forallN_length, VExpr.instN_forallN]
  simp only [VExpr.instTelN_length]
  rw [← hihBindersLength]
  rw [show ihBinders.length =
      (VExpr.instTelN a ihBinders (k + fieldBinders.length)).length by
    rw [VExpr.instTelN_length]]
  rw [VExpr.telN_forallN_length]

/-- Every minor in the complete flattened mutual spine commutes with ambient
lifting.  For the selected constructor this is field selection over the
exact generated IH telescope; all other constructors use identity rebuilds. -/
@[simp] theorem ProjectionSyntaxWF.projectionMinor_liftN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.ProjectionSyntaxWF env) {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ view.generation.flatCtors)
    (fieldSort : VLevel) (levels : List VLevel)
    (params allFields motives : List VExpr)
    (hparams : params.length = view.nparams)
    (hallFields : allFields = view.specializedFields levels params)
    (hmotives : motives.length = view.generation.familyCount)
    (fieldIndex : Nat) (hfieldIndex : fieldIndex < allFields.length)
    (n k : Nat) :
    (view.projectionMinor constructor fieldSort levels params allFields motives
        fieldIndex).liftN n k =
      view.projectionMinor constructor fieldSort levels
        (params.map fun param => param.liftN n k)
        (VExpr.liftTelN n allFields k)
        (motives.map fun motive => motive.liftN n k) fieldIndex := by
  subst allFields
  by_cases selected : constructor.owner = view.family.view.ordinal
  · simp only [projectionMinor, selected, ↓reduceIte]
    rw [VExpr.selectFieldMinor_liftN _ _ _ n k hfieldIndex]
    rw [self.projectionIHTypes_liftN fieldSort levels params motives hparams
      hmotives n k]
  · simp only [projectionMinor, selected, ↓reduceIte]
    exact self.identityMinor_liftN hconstructor fieldSort levels params motives
      hparams hmotives n k

/-- Every minor in the complete flattened mutual spine commutes with ambient
term instantiation. -/
@[simp] theorem ProjectionSyntaxWF.projectionMinor_instN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.ProjectionSyntaxWF env) {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ view.generation.flatCtors)
    (fieldSort : VLevel) (levels : List VLevel)
    (params allFields motives : List VExpr)
    (hparams : params.length = view.nparams)
    (hallFields : allFields = view.specializedFields levels params)
    (hmotives : motives.length = view.generation.familyCount)
    (fieldIndex : Nat) (hfieldIndex : fieldIndex < allFields.length)
    (a : VExpr) (k : Nat) :
    (view.projectionMinor constructor fieldSort levels params allFields motives
        fieldIndex).inst a k =
      view.projectionMinor constructor fieldSort levels
        (params.map fun param => param.inst a k)
        (VExpr.instTelN a allFields k)
        (motives.map fun motive => motive.inst a k) fieldIndex := by
  subst allFields
  by_cases selected : constructor.owner = view.family.view.ordinal
  · simp only [projectionMinor, selected, ↓reduceIte]
    rw [VExpr.selectFieldMinor_instN _ _ _ k a hfieldIndex]
    rw [self.projectionIHTypes_instN fieldSort levels params motives hparams
      hmotives a k]
  · simp only [projectionMinor, selected, ↓reduceIte]
    exact self.identityMinor_instN hconstructor fieldSort levels params motives
      hparams hmotives a k

/-- Prelude-free mutual minors commute with ambient lifting when their
explicit dummy inhabitant does. -/
@[simp] theorem ProjectionSyntaxWF.projectionMinorWith_liftN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.ProjectionSyntaxWF env) {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ view.generation.flatCtors)
    (fieldSort : VLevel) (levels : List VLevel)
    (params allFields motives : List VExpr) (fieldIndex : Nat)
    (dummyValue : VExpr)
    (hparams : params.length = view.nparams)
    (hallFields : allFields = view.specializedFields levels params)
    (hmotives : motives.length = view.generation.familyCount)
    (hfieldIndex : fieldIndex < allFields.length)
    (n k : Nat) :
    (view.projectionMinorWith constructor fieldSort levels params allFields
        motives fieldIndex dummyValue).liftN n k =
      view.projectionMinorWith constructor fieldSort levels
        (params.map fun param => param.liftN n k)
        (VExpr.liftTelN n allFields k)
        (motives.map fun motive => motive.liftN n k) fieldIndex
        (dummyValue.liftN n k) := by
  subst allFields
  by_cases selected : constructor.owner = view.family.view.ordinal
  · simp only [projectionMinorWith, selected, ↓reduceIte]
    rw [VExpr.selectFieldMinor_liftN _ _ _ n k hfieldIndex]
    rw [self.projectionIHTypes_liftN fieldSort levels params motives hparams
      hmotives n k]
  · simp only [projectionMinorWith, selected, ↓reduceIte]
    exact self.identityMinorWith_liftN hconstructor fieldSort levels params
      motives dummyValue hparams hmotives n k

/-- Prelude-free mutual minors commute with ambient instantiation when their
explicit dummy inhabitant does. -/
@[simp] theorem ProjectionSyntaxWF.projectionMinorWith_instN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.ProjectionSyntaxWF env) {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ view.generation.flatCtors)
    (fieldSort : VLevel) (levels : List VLevel)
    (params allFields motives : List VExpr) (fieldIndex : Nat)
    (dummyValue : VExpr)
    (hparams : params.length = view.nparams)
    (hallFields : allFields = view.specializedFields levels params)
    (hmotives : motives.length = view.generation.familyCount)
    (hfieldIndex : fieldIndex < allFields.length)
    (a : VExpr) (k : Nat) :
    (view.projectionMinorWith constructor fieldSort levels params allFields
        motives fieldIndex dummyValue).inst a k =
      view.projectionMinorWith constructor fieldSort levels
        (params.map fun param => param.inst a k)
        (VExpr.instTelN a allFields k)
        (motives.map fun motive => motive.inst a k) fieldIndex
        (dummyValue.inst a k) := by
  subst allFields
  by_cases selected : constructor.owner = view.family.view.ordinal
  · simp only [projectionMinorWith, selected, ↓reduceIte]
    rw [VExpr.selectFieldMinor_instN _ _ _ k a hfieldIndex]
    rw [self.projectionIHTypes_instN fieldSort levels params motives hparams
      hmotives a k]
  · simp only [projectionMinorWith, selected, ↓reduceIte]
    exact self.identityMinorWith_instN hconstructor fieldSort levels params
      motives dummyValue hparams hmotives a k

private theorem VExpr.operational_liftTelN_liftAt_projection
    (expressions : List VExpr) (n k i : Nat) :
    VExpr.liftTelN n (VExpr.liftTelN 1 expressions i) (k + 1 + i) =
      VExpr.liftTelN 1 (VExpr.liftTelN n expressions (k + i)) i := by
  induction expressions generalizing i with
  | nil => rfl
  | cons expression expressions ih =>
      simp only [VExpr.liftTelN]
      rw [VExpr.liftN_liftAt_projection]
      congr 1
      simpa only [Nat.add_assoc] using ih (i + 1)

private theorem VExpr.operational_liftTelN_lift_projection
    (expressions : List VExpr) (n k : Nat) :
    VExpr.liftTelN n (VExpr.liftTelN 1 expressions 0) (k + 1) =
      VExpr.liftTelN 1 (VExpr.liftTelN n expressions k) 0 := by
  simpa using
    VExpr.operational_liftTelN_liftAt_projection expressions n k 0

private theorem VExpr.operational_instTelN_liftAt_projection
    (expressions : List VExpr) (a : VExpr) (k i : Nat) :
    VExpr.instTelN a (VExpr.liftTelN 1 expressions i) (k + 1 + i) =
      VExpr.liftTelN 1 (VExpr.instTelN a expressions (k + i)) i := by
  induction expressions generalizing i with
  | nil => rfl
  | cons expression expressions ih =>
      simp only [VExpr.liftTelN, VExpr.instTelN]
      rw [VExpr.instN_liftAt_projection]
      congr 1
      simpa only [Nat.add_assoc] using ih (i + 1)

private theorem VExpr.operational_instTelN_lift_projection
    (expressions : List VExpr) (a : VExpr) (k : Nat) :
    VExpr.instTelN a (VExpr.liftTelN 1 expressions 0) (k + 1) =
      VExpr.liftTelN 1 (VExpr.instTelN a expressions k) 0 := by
  simpa using
    VExpr.operational_instTelN_liftAt_projection expressions a k 0

@[simp] theorem majorDummyType_liftN (typeFn : VExpr) (n k : Nat) :
    (majorDummyType typeFn.lift (.bvar 0)).liftN n (k + 1) =
      majorDummyType (typeFn.liftN n k).lift (.bvar 0) := by
  simp [majorDummyType, VExpr.liftN, VExpr.liftN_lift_projection]

@[simp] theorem majorDummyType_instN (typeFn a : VExpr) (k : Nat) :
    (majorDummyType typeFn.lift (.bvar 0)).inst a (k + 1) =
      majorDummyType (typeFn.inst a k).lift (.bvar 0) := by
  simp [majorDummyType, VExpr.inst, VExpr.instVar,
    ← VExpr.lift_instN_lo]

@[simp] theorem majorDummyValue_liftN (typeFn : VExpr) (n k : Nat) :
    (majorDummyValue typeFn.lift (.bvar 0)).liftN n (k + 1) =
      majorDummyValue (typeFn.liftN n k).lift (.bvar 0) := by
  simp [majorDummyValue, VExpr.liftN, VExpr.liftN_lift_projection]

@[simp] theorem majorDummyValue_instN (typeFn a : VExpr) (k : Nat) :
    (majorDummyValue typeFn.lift (.bvar 0)).inst a (k + 1) =
      majorDummyValue (typeFn.inst a k).lift (.bvar 0) := by
  simp [majorDummyValue, VExpr.inst, VExpr.instVar,
    ← VExpr.lift_instN_lo]

@[simp] theorem ProjectionSyntaxWF.operationalProjector_liftN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.ProjectionSyntaxWF env) (levels : List VLevel)
    (params allFields : List VExpr) (structType : VExpr)
    (fieldSort : VLevel) (fieldIndex : Nat) (typeFn : VExpr)
    (hparams : params.length = view.nparams)
    (hallFields : allFields = view.specializedFields levels params)
    (hfieldIndex : fieldIndex < allFields.length)
    (n k : Nat) :
    (view.operationalProjector levels params allFields structType fieldSort
        fieldIndex typeFn).liftN n k =
      view.operationalProjector levels
        (params.map fun param => param.liftN n k)
        (VExpr.liftTelN n allFields k) (structType.liftN n k) fieldSort
        fieldIndex (typeFn.liftN n k) := by
  let params' := params.map fun param => param.liftN n k
  let allFields' := VExpr.liftTelN n allFields k
  let typeFn' := typeFn.liftN n k
  let paramsMajor := params.map (VExpr.liftN 1)
  let paramsMajor' := params'.map (VExpr.liftN 1)
  let allFieldsMajor := VExpr.liftTelN 1 allFields 0
  let allFieldsMajor' := VExpr.liftTelN 1 allFields' 0
  let typeFnMajor := typeFn.lift
  let typeFnMajor' := typeFn'.lift
  let major := VExpr.bvar 0
  let dummyType := majorDummyType typeFnMajor major
  let dummyType' := majorDummyType typeFnMajor' major
  let dummyValue := majorDummyValue typeFnMajor major
  let dummyValue' := majorDummyValue typeFnMajor' major
  let motives := view.projectionMotivesWith levels paramsMajor typeFnMajor
    dummyType
  let motives' := view.projectionMotivesWith levels paramsMajor' typeFnMajor'
    dummyType'
  let minors := view.generation.flatCtors.map fun constructor =>
    view.projectionMinorWith constructor fieldSort levels paramsMajor
      allFieldsMajor motives fieldIndex dummyValue
  let minors' := view.generation.flatCtors.map fun constructor =>
    view.projectionMinorWith constructor fieldSort levels paramsMajor'
      allFieldsMajor' motives' fieldIndex dummyValue'
  have hparamsMajor :
      paramsMajor.map (fun expression => expression.liftN n (k + 1)) =
        paramsMajor' := by
    simp [paramsMajor, paramsMajor', params', List.map_map,
      Function.comp_def, VExpr.liftN_lift_projection]
  have htypeFnMajor : typeFnMajor.liftN n (k + 1) = typeFnMajor' := by
    exact VExpr.liftN_lift_projection typeFn n k
  have hallFieldsMajor :
      allFieldsMajor = view.specializedFields levels paramsMajor := by
    simpa [allFieldsMajor, paramsMajor, hallFields] using
      (self.specializedFields_liftN levels params hparams 1 0).symm
  have hallFieldsMajorLift :
      VExpr.liftTelN n allFieldsMajor (k + 1) = allFieldsMajor' := by
    simpa [allFieldsMajor, allFieldsMajor', allFields'] using
      VExpr.operational_liftTelN_lift_projection allFields n k
  have hparamsMajorLength : paramsMajor.length = view.nparams := by
    simpa [paramsMajor] using hparams
  have hfieldIndexMajor : fieldIndex < allFieldsMajor.length := by
    simpa [allFieldsMajor, VExpr.liftTelN_length] using hfieldIndex
  have hdummyType : dummyType.liftN n (k + 1) = dummyType' := by
    simpa [dummyType, dummyType', typeFnMajor, typeFnMajor', typeFn', major]
  have hdummyValue : dummyValue.liftN n (k + 1) = dummyValue' := by
    simpa [dummyValue, dummyValue', typeFnMajor, typeFnMajor', typeFn', major]
  have hmotivesLength :
      motives.length = view.generation.familyCount := by
    simp [motives, projectionMotivesWith, BlockGenerationChecked.familyCount]
  have hmotives :
      motives.map (fun motive => motive.liftN n (k + 1)) = motives' := by
    have hout := self.projectionMotivesWith_liftN levels paramsMajor
      hparamsMajorLength typeFnMajor dummyType n (k + 1)
    rw [hparamsMajor, htypeFnMajor, hdummyType] at hout
    exact hout
  have hminors :
      minors.map (fun minor => minor.liftN n (k + 1)) = minors' := by
    simp only [minors, minors', List.map_map]
    apply List.map_congr_left
    intro constructor hconstructor
    have hout := self.projectionMinorWith_liftN hconstructor fieldSort levels
      paramsMajor allFieldsMajor motives fieldIndex dummyValue
      hparamsMajorLength hallFieldsMajor hmotivesLength hfieldIndexMajor
      n (k + 1)
    rw [hparamsMajor, hallFieldsMajorLift, hmotives, hdummyValue] at hout
    exact hout
  unfold operationalProjector
  change
    (VExpr.lam structType (VExpr.appN
      (.const view.recursorName (view.projectionLevels fieldSort levels))
      (paramsMajor ++ motives ++ minors ++ [major]))).liftN n k =
    VExpr.lam (structType.liftN n k) (VExpr.appN
      (.const view.recursorName (view.projectionLevels fieldSort levels))
      (paramsMajor' ++ motives' ++ minors' ++ [major]))
  simp only [VExpr.liftN, VExpr.liftN_appN, List.map_append,
    List.map_singleton, hparamsMajor, hmotives, hminors]
  simp [major, VExpr.liftN, liftVar]

@[simp] theorem ProjectionSyntaxWF.operationalProjector_instN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.ProjectionSyntaxWF env) (levels : List VLevel)
    (params allFields : List VExpr) (structType : VExpr)
    (fieldSort : VLevel) (fieldIndex : Nat) (typeFn : VExpr)
    (hparams : params.length = view.nparams)
    (hallFields : allFields = view.specializedFields levels params)
    (hfieldIndex : fieldIndex < allFields.length)
    (a : VExpr) (k : Nat) :
    (view.operationalProjector levels params allFields structType fieldSort
        fieldIndex typeFn).inst a k =
      view.operationalProjector levels
        (params.map fun param => param.inst a k)
        (VExpr.instTelN a allFields k) (structType.inst a k) fieldSort
        fieldIndex (typeFn.inst a k) := by
  let params' := params.map fun param => param.inst a k
  let allFields' := VExpr.instTelN a allFields k
  let typeFn' := typeFn.inst a k
  let paramsMajor := params.map (VExpr.liftN 1)
  let paramsMajor' := params'.map (VExpr.liftN 1)
  let allFieldsMajor := VExpr.liftTelN 1 allFields 0
  let allFieldsMajor' := VExpr.liftTelN 1 allFields' 0
  let typeFnMajor := typeFn.lift
  let typeFnMajor' := typeFn'.lift
  let major := VExpr.bvar 0
  let dummyType := majorDummyType typeFnMajor major
  let dummyType' := majorDummyType typeFnMajor' major
  let dummyValue := majorDummyValue typeFnMajor major
  let dummyValue' := majorDummyValue typeFnMajor' major
  let motives := view.projectionMotivesWith levels paramsMajor typeFnMajor
    dummyType
  let motives' := view.projectionMotivesWith levels paramsMajor' typeFnMajor'
    dummyType'
  let minors := view.generation.flatCtors.map fun constructor =>
    view.projectionMinorWith constructor fieldSort levels paramsMajor
      allFieldsMajor motives fieldIndex dummyValue
  let minors' := view.generation.flatCtors.map fun constructor =>
    view.projectionMinorWith constructor fieldSort levels paramsMajor'
      allFieldsMajor' motives' fieldIndex dummyValue'
  have hparamsMajor :
      paramsMajor.map (fun expression => expression.inst a (k + 1)) =
        paramsMajor' := by
    simp [paramsMajor, paramsMajor', params', List.map_map,
      Function.comp_def, ← VExpr.lift_instN_lo]
  have htypeFnMajor : typeFnMajor.inst a (k + 1) = typeFnMajor' := by
    simpa [typeFnMajor, typeFnMajor', typeFn'] using
      (VExpr.lift_instN_lo typeFn a (k := k)).symm
  have hallFieldsMajor :
      allFieldsMajor = view.specializedFields levels paramsMajor := by
    simpa [allFieldsMajor, paramsMajor, hallFields] using
      (self.specializedFields_liftN levels params hparams 1 0).symm
  have hallFieldsMajorInst :
      VExpr.instTelN a allFieldsMajor (k + 1) = allFieldsMajor' := by
    simpa [allFieldsMajor, allFieldsMajor', allFields'] using
      VExpr.operational_instTelN_lift_projection allFields a k
  have hparamsMajorLength : paramsMajor.length = view.nparams := by
    simpa [paramsMajor] using hparams
  have hfieldIndexMajor : fieldIndex < allFieldsMajor.length := by
    simpa [allFieldsMajor, VExpr.liftTelN_length] using hfieldIndex
  have hdummyType : dummyType.inst a (k + 1) = dummyType' := by
    simpa [dummyType, dummyType', typeFnMajor, typeFnMajor', typeFn', major]
  have hdummyValue : dummyValue.inst a (k + 1) = dummyValue' := by
    simpa [dummyValue, dummyValue', typeFnMajor, typeFnMajor', typeFn', major]
  have hmotivesLength :
      motives.length = view.generation.familyCount := by
    simp [motives, projectionMotivesWith, BlockGenerationChecked.familyCount]
  have hmotives :
      motives.map (fun motive => motive.inst a (k + 1)) = motives' := by
    have hout := self.projectionMotivesWith_instN levels paramsMajor
      hparamsMajorLength typeFnMajor dummyType a (k + 1)
    rw [hparamsMajor, htypeFnMajor, hdummyType] at hout
    exact hout
  have hminors :
      minors.map (fun minor => minor.inst a (k + 1)) = minors' := by
    simp only [minors, minors', List.map_map]
    apply List.map_congr_left
    intro constructor hconstructor
    have hout := self.projectionMinorWith_instN hconstructor fieldSort levels
      paramsMajor allFieldsMajor motives fieldIndex dummyValue
      hparamsMajorLength hallFieldsMajor hmotivesLength hfieldIndexMajor
      a (k + 1)
    rw [hparamsMajor, hallFieldsMajorInst, hmotives, hdummyValue] at hout
    exact hout
  unfold operationalProjector
  change
    (VExpr.lam structType (VExpr.appN
      (.const view.recursorName (view.projectionLevels fieldSort levels))
      (paramsMajor ++ motives ++ minors ++ [major]))).inst a k =
    VExpr.lam (structType.inst a k) (VExpr.appN
      (.const view.recursorName (view.projectionLevels fieldSort levels))
      (paramsMajor' ++ motives' ++ minors' ++ [major]))
  simp only [VExpr.inst, VExpr.instN_appN, List.map_append,
    List.map_singleton, hparamsMajor, hmotives, hminors, VExpr.instVar]
  simp [major, VExpr.inst]

private theorem ProjectionSyntaxWF.operationalProjectionCode_liftN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.ProjectionSyntaxWF env) (levels : List VLevel)
    (params allFields : List VExpr) (structType field : VExpr)
    (fieldSort : VLevel) (fieldIndex : Nat)
    (previous : List VStructureView.ProjectionCode)
    (hparams : params.length = view.nparams)
    (hallFields : allFields = view.specializedFields levels params)
    (hprevious : previous.length = fieldIndex)
    (hfieldIndex : fieldIndex < allFields.length)
    (n k : Nat) :
    (operationalProjectionCode view levels params allFields structType field
      fieldSort fieldIndex previous).liftN n k =
    operationalProjectionCode view levels
      (params.map fun param => param.liftN n k)
      (VExpr.liftTelN n allFields k)
      (structType.liftN n k) (field.liftN n (k + fieldIndex))
      fieldSort fieldIndex
      (previous.map fun code => code.liftN n k) := by
  let previousAtMajor := previous.map fun code =>
    VExpr.app code.projector.lift (.bvar 0)
  let previous' := previous.map fun code => code.liftN n k
  let previousAtMajor' := previous'.map fun code =>
    VExpr.app code.projector.lift (.bvar 0)
  have hfieldLift :
      (field.liftN 1 fieldIndex).liftN n (k + 1 + fieldIndex) =
        (field.liftN n (k + fieldIndex)).liftN 1 fieldIndex :=
    VExpr.liftN_liftAt_projection field n k fieldIndex
  have hpreviousLift :
      previousAtMajor.map (fun expression => expression.liftN n (k + 1)) =
        previousAtMajor' := by
    simp [previousAtMajor, previousAtMajor', previous',
      VStructureView.ProjectionCode.liftN, VExpr.liftN,
      VExpr.liftN_lift_projection, List.map_map, Function.comp_def]
  let motiveBody :=
    (field.liftN 1 fieldIndex).instRevAt previousAtMajor 0
  let motiveBody' :=
    ((field.liftN n (k + fieldIndex)).liftN 1 fieldIndex).instRevAt
      previousAtMajor' 0
  have hmotiveBody : motiveBody.liftN n (k + 1) = motiveBody' := by
    simp only [motiveBody, motiveBody', VExpr.liftN_instRevAt]
    rw [List.length_map, hprevious, hfieldLift, hpreviousLift]
  let typeFn := VExpr.lam structType motiveBody
  let typeFn' := VExpr.lam (structType.liftN n k) motiveBody'
  have htypeFn : typeFn.liftN n k = typeFn' := by
    simp [typeFn, typeFn', VExpr.liftN, hmotiveBody]
  have hprojector := self.operationalProjector_liftN levels params allFields
    structType fieldSort fieldIndex typeFn hparams hallFields hfieldIndex n k
  rw [htypeFn] at hprojector
  unfold operationalProjectionCode VStructureView.ProjectionCode.liftN
  dsimp only
  apply VStructureView.ProjectionCode.ext
  · rfl
  · exact htypeFn
  · exact htypeFn
  · exact hprojector

private theorem ProjectionSyntaxWF.operationalProjectionCode_instN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.ProjectionSyntaxWF env) (levels : List VLevel)
    (params allFields : List VExpr) (structType field : VExpr)
    (fieldSort : VLevel) (fieldIndex : Nat)
    (previous : List VStructureView.ProjectionCode)
    (hparams : params.length = view.nparams)
    (hallFields : allFields = view.specializedFields levels params)
    (hprevious : previous.length = fieldIndex)
    (hfieldIndex : fieldIndex < allFields.length)
    (a : VExpr) (k : Nat) :
    (operationalProjectionCode view levels params allFields structType field
      fieldSort fieldIndex previous).instN a k =
    operationalProjectionCode view levels
      (params.map fun param => param.inst a k)
      (VExpr.instTelN a allFields k)
      (structType.inst a k) (field.inst a (k + fieldIndex))
      fieldSort fieldIndex
      (previous.map fun code => code.instN a k) := by
  let previousAtMajor := previous.map fun code =>
    VExpr.app code.projector.lift (.bvar 0)
  let previous' := previous.map fun code => code.instN a k
  let previousAtMajor' := previous'.map fun code =>
    VExpr.app code.projector.lift (.bvar 0)
  have hfieldInst :
      (field.liftN 1 fieldIndex).inst a (k + 1 + fieldIndex) =
        (field.inst a (k + fieldIndex)).liftN 1 fieldIndex :=
    VExpr.instN_liftAt_projection field a k fieldIndex
  have hpreviousInst :
      previousAtMajor.map (fun expression => expression.inst a (k + 1)) =
        previousAtMajor' := by
    simp [previousAtMajor, previousAtMajor', previous',
      VStructureView.ProjectionCode.instN, VExpr.inst, VExpr.instVar,
      ← VExpr.lift_instN_lo, List.map_map, Function.comp_def]
  let motiveBody :=
    (field.liftN 1 fieldIndex).instRevAt previousAtMajor 0
  let motiveBody' :=
    ((field.inst a (k + fieldIndex)).liftN 1 fieldIndex).instRevAt
      previousAtMajor' 0
  have hmotiveBody : motiveBody.inst a (k + 1) = motiveBody' := by
    simp only [motiveBody, motiveBody', VExpr.instN_instRevAt]
    rw [List.length_map, hprevious, hfieldInst, hpreviousInst]
  let typeFn := VExpr.lam structType motiveBody
  let typeFn' := VExpr.lam (structType.inst a k) motiveBody'
  have htypeFn : typeFn.inst a k = typeFn' := by
    simp [typeFn, typeFn', VExpr.inst, hmotiveBody]
  have hprojector := self.operationalProjector_instN levels params allFields
    structType fieldSort fieldIndex typeFn hparams hallFields hfieldIndex a k
  rw [htypeFn] at hprojector
  unfold operationalProjectionCode VStructureView.ProjectionCode.instN
  dsimp only
  apply VStructureView.ProjectionCode.ext
  · rfl
  · exact htypeFn
  · exact htypeFn
  · exact hprojector

private theorem LayoutWF.projectionCode_liftN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (levels : List VLevel)
    (params allFields : List VExpr) (structType field : VExpr)
    (fieldSort : VLevel) (fieldIndex : Nat)
    (previous : List VStructureView.ProjectionCode)
    (hparams : params.length = view.nparams)
    (hallFields : allFields = view.specializedFields levels params)
    (hprevious : previous.length = fieldIndex)
    (hfieldIndex : fieldIndex < allFields.length)
    (n k : Nat) :
    (projectionCode view levels params allFields structType field
      fieldSort fieldIndex previous).liftN n k =
    projectionCode view levels
      (params.map fun param => param.liftN n k)
      (VExpr.liftTelN n allFields k)
      (structType.liftN n k) (field.liftN n (k + fieldIndex))
      fieldSort fieldIndex
      (previous.map fun code => code.liftN n k) := by
  let previousAtMajor := previous.map fun code =>
    VExpr.app code.projector.lift (.bvar 0)
  let previous' := previous.map fun code => code.liftN n k
  let previousAtMajor' := previous'.map fun code =>
    VExpr.app code.projector.lift (.bvar 0)
  have hfieldLift :
      (field.liftN 1 fieldIndex).liftN n (k + 1 + fieldIndex) =
        (field.liftN n (k + fieldIndex)).liftN 1 fieldIndex :=
    VExpr.liftN_liftAt_projection field n k fieldIndex
  have hpreviousLift :
      previousAtMajor.map (fun expression => expression.liftN n (k + 1)) =
        previousAtMajor' := by
    simp [previousAtMajor, previousAtMajor', previous',
      VStructureView.ProjectionCode.liftN, VExpr.liftN,
      VExpr.liftN_lift_projection, List.map_map, Function.comp_def]
  let motiveBody :=
    (field.liftN 1 fieldIndex).instRevAt previousAtMajor 0
  let motiveBody' :=
    ((field.liftN n (k + fieldIndex)).liftN 1 fieldIndex).instRevAt
      previousAtMajor' 0
  have hmotiveBody : motiveBody.liftN n (k + 1) = motiveBody' := by
    simp only [motiveBody, motiveBody', VExpr.liftN_instRevAt]
    rw [List.length_map, hprevious, hfieldLift, hpreviousLift]
  let typeFn := VExpr.lam structType motiveBody
  let typeFn' := VExpr.lam (structType.liftN n k) motiveBody'
  have htypeFn : typeFn.liftN n k = typeFn' := by
    simp [typeFn, typeFn', VExpr.liftN, hmotiveBody]
  let motives := view.projectionMotives levels params fieldSort typeFn
  let motives' := view.projectionMotives levels
    (params.map fun param => param.liftN n k) fieldSort typeFn'
  have hmotivesLength :
      motives.length = view.generation.familyCount := by
    simp [motives]
  have hmotives :
      motives.map (fun motive => motive.liftN n k) = motives' := by
    simpa only [motives, motives', htypeFn] using
      self.toProjectionSyntaxWF.projectionMotives_liftN
        fieldSort levels params hparams typeFn n k
  let minors := view.generation.flatCtors.map fun constructor =>
    view.projectionMinor constructor fieldSort levels params allFields motives
      fieldIndex
  let minors' := view.generation.flatCtors.map fun constructor =>
    view.projectionMinor constructor fieldSort levels
      (params.map fun param => param.liftN n k)
      (VExpr.liftTelN n allFields k) motives' fieldIndex
  have hminors :
      minors.map (fun minor => minor.liftN n k) = minors' := by
    simp only [minors, minors', List.map_map]
    apply List.map_congr_left
    intro constructor hconstructor
    change (view.projectionMinor constructor fieldSort levels params allFields motives
        fieldIndex).liftN n k = _
    exact (self.toProjectionSyntaxWF.projectionMinor_liftN
      hconstructor fieldSort levels params
      allFields motives hparams hallFields hmotivesLength fieldIndex
      hfieldIndex n k).trans (by rw [hmotives])
  have hminor :
      (view.projectionMinor view.blockConstructor fieldSort levels params allFields
          motives fieldIndex).liftN n k =
        view.projectionMinor view.blockConstructor fieldSort levels
          (params.map fun param => param.liftN n k)
          (VExpr.liftTelN n allFields k) motives' fieldIndex :=
    (self.toProjectionSyntaxWF.projectionMinor_liftN
      view.blockConstructor_mem fieldSort levels
      params allFields motives hparams hallFields hmotivesLength fieldIndex
      hfieldIndex n k).trans (by rw [hmotives])
  have hparamsLift :
      (params.map (VExpr.liftN 1)).map
          (fun expression => expression.liftN n (k + 1)) =
        (params.map fun param => param.liftN n k).map (VExpr.liftN 1) := by
    simp [List.map_map, Function.comp_def, VExpr.liftN_lift_projection]
  have hmotivesLift :
      (motives.map (VExpr.liftN 1)).map
          (fun expression => expression.liftN n (k + 1)) =
        motives'.map (VExpr.liftN 1) := by
    simpa only [List.map_map, Function.comp_def,
      VExpr.liftN_lift_projection] using
      congrArg (List.map (VExpr.liftN 1)) hmotives
  have hminorsLift :
      (minors.map (VExpr.liftN 1)).map
          (fun expression => expression.liftN n (k + 1)) =
        minors'.map (VExpr.liftN 1) := by
    simpa only [List.map_map, Function.comp_def,
      VExpr.liftN_lift_projection] using
      congrArg (List.map (VExpr.liftN 1)) hminors
  unfold projectionCode VStructureView.ProjectionCode.liftN
  dsimp only
  apply VStructureView.ProjectionCode.ext
  · rfl
  · exact htypeFn
  · exact hminor
  · change
      (VExpr.lam structType <| VExpr.appN
        (.const view.recursorName (view.projectionLevels fieldSort levels))
        (params.map (VExpr.liftN 1) ++ motives.map (VExpr.liftN 1) ++
          minors.map (VExpr.liftN 1) ++ [.bvar 0])).liftN n k =
      VExpr.lam (structType.liftN n k) (VExpr.appN
        (.const view.recursorName (view.projectionLevels fieldSort levels))
        ((params.map fun param => param.liftN n k).map (VExpr.liftN 1) ++
          motives'.map (VExpr.liftN 1) ++
          minors'.map (VExpr.liftN 1) ++ [.bvar 0]))
    simp only [VExpr.liftN, VExpr.liftN_appN, List.map_append,
      List.map_singleton, hparamsLift, hmotivesLift, hminorsLift]
    rw [liftVar_lt (by omega)]

private theorem LayoutWF.projectionCode_instN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (levels : List VLevel)
    (params allFields : List VExpr) (structType field : VExpr)
    (fieldSort : VLevel) (fieldIndex : Nat)
    (previous : List VStructureView.ProjectionCode)
    (hparams : params.length = view.nparams)
    (hallFields : allFields = view.specializedFields levels params)
    (hprevious : previous.length = fieldIndex)
    (hfieldIndex : fieldIndex < allFields.length)
    (a : VExpr) (k : Nat) :
    (projectionCode view levels params allFields structType field
      fieldSort fieldIndex previous).instN a k =
    projectionCode view levels
      (params.map fun param => param.inst a k)
      (VExpr.instTelN a allFields k)
      (structType.inst a k) (field.inst a (k + fieldIndex))
      fieldSort fieldIndex
      (previous.map fun code => code.instN a k) := by
  let previousAtMajor := previous.map fun code =>
    VExpr.app code.projector.lift (.bvar 0)
  let previous' := previous.map fun code => code.instN a k
  let previousAtMajor' := previous'.map fun code =>
    VExpr.app code.projector.lift (.bvar 0)
  have hfieldInst :
      (field.liftN 1 fieldIndex).inst a (k + 1 + fieldIndex) =
        (field.inst a (k + fieldIndex)).liftN 1 fieldIndex :=
    VExpr.instN_liftAt_projection field a k fieldIndex
  have hpreviousInst :
      previousAtMajor.map (fun expression => expression.inst a (k + 1)) =
        previousAtMajor' := by
    simp [previousAtMajor, previousAtMajor', previous',
      VStructureView.ProjectionCode.instN, VExpr.inst, VExpr.instVar,
      ← VExpr.lift_instN_lo, List.map_map, Function.comp_def]
  let motiveBody :=
    (field.liftN 1 fieldIndex).instRevAt previousAtMajor 0
  let motiveBody' :=
    ((field.inst a (k + fieldIndex)).liftN 1 fieldIndex).instRevAt
      previousAtMajor' 0
  have hmotiveBody : motiveBody.inst a (k + 1) = motiveBody' := by
    simp only [motiveBody, motiveBody', VExpr.instN_instRevAt]
    rw [List.length_map, hprevious, hfieldInst, hpreviousInst]
  let typeFn := VExpr.lam structType motiveBody
  let typeFn' := VExpr.lam (structType.inst a k) motiveBody'
  have htypeFn : typeFn.inst a k = typeFn' := by
    simp [typeFn, typeFn', VExpr.inst, hmotiveBody]
  let motives := view.projectionMotives levels params fieldSort typeFn
  let motives' := view.projectionMotives levels
    (params.map fun param => param.inst a k) fieldSort typeFn'
  have hmotivesLength :
      motives.length = view.generation.familyCount := by
    simp [motives]
  have hmotives :
      motives.map (fun motive => motive.inst a k) = motives' := by
    simpa only [motives, motives', htypeFn] using
      self.toProjectionSyntaxWF.projectionMotives_instN
        fieldSort levels params hparams typeFn a k
  let minors := view.generation.flatCtors.map fun constructor =>
    view.projectionMinor constructor fieldSort levels params allFields motives
      fieldIndex
  let minors' := view.generation.flatCtors.map fun constructor =>
    view.projectionMinor constructor fieldSort levels
      (params.map fun param => param.inst a k)
      (VExpr.instTelN a allFields k) motives' fieldIndex
  have hminors :
      minors.map (fun minor => minor.inst a k) = minors' := by
    simp only [minors, minors', List.map_map]
    apply List.map_congr_left
    intro constructor hconstructor
    change (view.projectionMinor constructor fieldSort levels params allFields motives
        fieldIndex).inst a k = _
    exact (self.toProjectionSyntaxWF.projectionMinor_instN
      hconstructor fieldSort levels params
      allFields motives hparams hallFields hmotivesLength fieldIndex
      hfieldIndex a k).trans (by rw [hmotives])
  have hminor :
      (view.projectionMinor view.blockConstructor fieldSort levels params allFields
          motives fieldIndex).inst a k =
        view.projectionMinor view.blockConstructor fieldSort levels
          (params.map fun param => param.inst a k)
          (VExpr.instTelN a allFields k) motives' fieldIndex :=
    (self.toProjectionSyntaxWF.projectionMinor_instN
      view.blockConstructor_mem fieldSort levels
      params allFields motives hparams hallFields hmotivesLength fieldIndex
      hfieldIndex a k).trans (by rw [hmotives])
  have hparamsInst :
      (params.map (VExpr.liftN 1)).map
          (fun expression => expression.inst a (k + 1)) =
        (params.map fun param => param.inst a k).map (VExpr.liftN 1) := by
    simp [List.map_map, Function.comp_def, ← VExpr.lift_instN_lo]
  have hmotivesInst :
      (motives.map (VExpr.liftN 1)).map
          (fun expression => expression.inst a (k + 1)) =
        motives'.map (VExpr.liftN 1) := by
    simpa only [List.map_map, Function.comp_def,
      ← VExpr.lift_instN_lo] using
      congrArg (List.map (VExpr.liftN 1)) hmotives
  have hminorsInst :
      (minors.map (VExpr.liftN 1)).map
          (fun expression => expression.inst a (k + 1)) =
        minors'.map (VExpr.liftN 1) := by
    simpa only [List.map_map, Function.comp_def,
      ← VExpr.lift_instN_lo] using
      congrArg (List.map (VExpr.liftN 1)) hminors
  unfold projectionCode VStructureView.ProjectionCode.instN
  dsimp only
  apply VStructureView.ProjectionCode.ext
  · rfl
  · exact htypeFn
  · exact hminor
  · change
      (VExpr.lam structType <| VExpr.appN
        (.const view.recursorName (view.projectionLevels fieldSort levels))
        (params.map (VExpr.liftN 1) ++ motives.map (VExpr.liftN 1) ++
          minors.map (VExpr.liftN 1) ++ [.bvar 0])).inst a k =
      VExpr.lam (structType.inst a k) (VExpr.appN
        (.const view.recursorName (view.projectionLevels fieldSort levels))
        ((params.map fun param => param.inst a k).map (VExpr.liftN 1) ++
          motives'.map (VExpr.liftN 1) ++
          minors'.map (VExpr.liftN 1) ++ [.bvar 0]))
    simp only [VExpr.inst, VExpr.instN_appN, List.map_append,
      List.map_singleton, hparamsInst, hmotivesInst, hminorsInst,
      VExpr.instVar]
    simp

private theorem LayoutWF.projectionCodes_go_liftN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (levels : List VLevel)
    (params allFields : List VExpr) (structType : VExpr)
    (fields : List VExpr) (fieldSorts : List VLevel)
    (fieldIndex : Nat) (previous : List VStructureView.ProjectionCode)
    (hparams : params.length = view.nparams)
    (hallFields : allFields = view.specializedFields levels params)
    (hprevious : previous.length = fieldIndex)
    (hfields : fieldIndex + fields.length = allFields.length)
    (n k : Nat) :
    (projectionCodes.go view levels params allFields structType
        fields fieldSorts fieldIndex previous).map
      (fun code => code.liftN n k) =
    projectionCodes.go view levels
      (params.map fun param => param.liftN n k)
      (VExpr.liftTelN n allFields k) (structType.liftN n k)
      (VExpr.liftTelN n fields (k + fieldIndex)) fieldSorts fieldIndex
      (previous.map fun code => code.liftN n k) := by
  induction fields generalizing fieldSorts fieldIndex previous with
  | nil =>
      cases fieldSorts <;> simp [projectionCodes.go, VExpr.liftTelN]
  | cons field fields ih =>
      cases fieldSorts with
      | nil => simp [projectionCodes.go]
      | cons fieldSort fieldSorts =>
          have hfieldIndex' : fieldIndex < allFields.length := by
            simp only [List.length_cons] at hfields
            omega
          have hcode := self.projectionCode_liftN levels params
            allFields structType field fieldSort fieldIndex previous hparams
            hallFields hprevious hfieldIndex' n k
          simp only [projectionCodes.go, List.map_cons, VExpr.liftTelN]
          rw [hcode]
          congr 1
          have hprevious' :
              (previous ++ [projectionCode view levels params allFields
                structType field fieldSort fieldIndex previous]).length =
                fieldIndex + 1 := by
            simp [hprevious]
          have hfields' :
              fieldIndex + 1 + fields.length = allFields.length := by
            simp only [List.length_cons] at hfields
            omega
          simpa only [List.map_append, List.map_singleton, hcode,
            Nat.add_assoc] using
            ih fieldSorts (fieldIndex + 1)
              (previous ++ [projectionCode view levels params allFields
                structType field fieldSort fieldIndex previous])
              hprevious' hfields'

private theorem LayoutWF.projectionCodes_go_instN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (levels : List VLevel)
    (params allFields : List VExpr) (structType : VExpr)
    (fields : List VExpr) (fieldSorts : List VLevel)
    (fieldIndex : Nat) (previous : List VStructureView.ProjectionCode)
    (hparams : params.length = view.nparams)
    (hallFields : allFields = view.specializedFields levels params)
    (hprevious : previous.length = fieldIndex)
    (hfields : fieldIndex + fields.length = allFields.length)
    (a : VExpr) (k : Nat) :
    (projectionCodes.go view levels params allFields structType
        fields fieldSorts fieldIndex previous).map
      (fun code => code.instN a k) =
    projectionCodes.go view levels
      (params.map fun param => param.inst a k)
      (VExpr.instTelN a allFields k) (structType.inst a k)
      (VExpr.instTelN a fields (k + fieldIndex)) fieldSorts fieldIndex
      (previous.map fun code => code.instN a k) := by
  induction fields generalizing fieldSorts fieldIndex previous with
  | nil =>
      cases fieldSorts <;> simp [projectionCodes.go, VExpr.instTelN]
  | cons field fields ih =>
      cases fieldSorts with
      | nil => simp [projectionCodes.go]
      | cons fieldSort fieldSorts =>
          have hfieldIndex' : fieldIndex < allFields.length := by
            simp only [List.length_cons] at hfields
            omega
          have hcode := self.projectionCode_instN levels params
            allFields structType field fieldSort fieldIndex previous hparams
            hallFields hprevious hfieldIndex' a k
          simp only [projectionCodes.go, List.map_cons, VExpr.instTelN]
          rw [hcode]
          congr 1
          have hprevious' :
              (previous ++ [projectionCode view levels params allFields
                structType field fieldSort fieldIndex previous]).length =
                fieldIndex + 1 := by
            simp [hprevious]
          have hfields' :
              fieldIndex + 1 + fields.length = allFields.length := by
            simp only [List.length_cons] at hfields
            omega
          simpa only [List.map_append, List.map_singleton, hcode,
            Nat.add_assoc] using
            ih fieldSorts (fieldIndex + 1)
              (previous ++ [projectionCode view levels params allFields
                structType field fieldSort fieldIndex previous])
              hprevious' hfields'

/-- The complete block-backed projection program list commutes with ambient
lifting. -/
@[simp] theorem LayoutWF.projectionCodes_liftN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (levels : List VLevel)
    (params : List VExpr) (hparams : params.length = view.nparams)
    (n k : Nat) :
    (view.projectionCodes levels params).map
        (fun code => code.liftN n k) =
      view.projectionCodes levels
        (params.map fun param => param.liftN n k) := by
  unfold projectionCodes
  rw [self.specializedFields_liftN levels params hparams n k]
  rw [← structureType_liftN]
  apply self.projectionCodes_go_liftN levels params
  · exact hparams
  · rfl
  · rfl
  · simp

/-- The complete block-backed projection program list commutes with ambient
term instantiation. -/
@[simp] theorem LayoutWF.projectionCodes_instN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (levels : List VLevel)
    (params : List VExpr) (hparams : params.length = view.nparams)
    (a : VExpr) (k : Nat) :
    (view.projectionCodes levels params).map
        (fun code => code.instN a k) =
      view.projectionCodes levels
        (params.map fun param => param.inst a k) := by
  unfold projectionCodes
  rw [self.specializedFields_instN levels params hparams a k]
  rw [← structureType_instN]
  apply self.projectionCodes_go_instN levels params
  · exact hparams
  · rfl
  · rfl
  · simp

private theorem ProjectionSyntaxWF.operationalProjectionCodes_go_liftN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.ProjectionSyntaxWF env) (levels : List VLevel)
    (params allFields : List VExpr) (structType : VExpr)
    (fields : List VExpr) (fieldSorts : List VLevel)
    (fieldIndex : Nat) (previous : List VStructureView.ProjectionCode)
    (hparams : params.length = view.nparams)
    (hallFields : allFields = view.specializedFields levels params)
    (hprevious : previous.length = fieldIndex)
    (hfields : fieldIndex + fields.length = allFields.length)
    (n k : Nat) :
    (operationalProjectionCodes.go view levels params allFields structType
        fields fieldSorts fieldIndex previous).map
      (fun code => code.liftN n k) =
    operationalProjectionCodes.go view levels
      (params.map fun param => param.liftN n k)
      (VExpr.liftTelN n allFields k) (structType.liftN n k)
      (VExpr.liftTelN n fields (k + fieldIndex)) fieldSorts fieldIndex
      (previous.map fun code => code.liftN n k) := by
  induction fields generalizing fieldSorts fieldIndex previous with
  | nil =>
      cases fieldSorts <;>
        simp [operationalProjectionCodes.go, VExpr.liftTelN]
  | cons field fields ih =>
      cases fieldSorts with
      | nil => simp [operationalProjectionCodes.go]
      | cons fieldSort fieldSorts =>
          have hfieldIndex' : fieldIndex < allFields.length := by
            simp only [List.length_cons] at hfields
            omega
          have hcode := self.operationalProjectionCode_liftN levels params
            allFields structType field fieldSort fieldIndex previous hparams
            hallFields hprevious hfieldIndex' n k
          simp only [operationalProjectionCodes.go, List.map_cons,
            VExpr.liftTelN]
          rw [hcode]
          congr 1
          have hprevious' :
              (previous ++ [operationalProjectionCode view levels params
                allFields structType field fieldSort fieldIndex
                previous]).length = fieldIndex + 1 := by
            simp [hprevious]
          have hfields' :
              fieldIndex + 1 + fields.length = allFields.length := by
            simp only [List.length_cons] at hfields
            omega
          simpa only [List.map_append, List.map_singleton, hcode,
            Nat.add_assoc] using
            ih fieldSorts (fieldIndex + 1)
              (previous ++ [operationalProjectionCode view levels params
                allFields structType field fieldSort fieldIndex previous])
              hprevious' hfields'

private theorem ProjectionSyntaxWF.operationalProjectionCodes_go_instN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.ProjectionSyntaxWF env) (levels : List VLevel)
    (params allFields : List VExpr) (structType : VExpr)
    (fields : List VExpr) (fieldSorts : List VLevel)
    (fieldIndex : Nat) (previous : List VStructureView.ProjectionCode)
    (hparams : params.length = view.nparams)
    (hallFields : allFields = view.specializedFields levels params)
    (hprevious : previous.length = fieldIndex)
    (hfields : fieldIndex + fields.length = allFields.length)
    (a : VExpr) (k : Nat) :
    (operationalProjectionCodes.go view levels params allFields structType
        fields fieldSorts fieldIndex previous).map
      (fun code => code.instN a k) =
    operationalProjectionCodes.go view levels
      (params.map fun param => param.inst a k)
      (VExpr.instTelN a allFields k) (structType.inst a k)
      (VExpr.instTelN a fields (k + fieldIndex)) fieldSorts fieldIndex
      (previous.map fun code => code.instN a k) := by
  induction fields generalizing fieldSorts fieldIndex previous with
  | nil =>
      cases fieldSorts <;>
        simp [operationalProjectionCodes.go, VExpr.instTelN]
  | cons field fields ih =>
      cases fieldSorts with
      | nil => simp [operationalProjectionCodes.go]
      | cons fieldSort fieldSorts =>
          have hfieldIndex' : fieldIndex < allFields.length := by
            simp only [List.length_cons] at hfields
            omega
          have hcode := self.operationalProjectionCode_instN levels params
            allFields structType field fieldSort fieldIndex previous hparams
            hallFields hprevious hfieldIndex' a k
          simp only [operationalProjectionCodes.go, List.map_cons,
            VExpr.instTelN]
          rw [hcode]
          congr 1
          have hprevious' :
              (previous ++ [operationalProjectionCode view levels params
                allFields structType field fieldSort fieldIndex
                previous]).length = fieldIndex + 1 := by
            simp [hprevious]
          have hfields' :
              fieldIndex + 1 + fields.length = allFields.length := by
            simp only [List.length_cons] at hfields
            omega
          simpa only [List.map_append, List.map_singleton, hcode,
            Nat.add_assoc] using
            ih fieldSorts (fieldIndex + 1)
              (previous ++ [operationalProjectionCode view levels params
                allFields structType field fieldSort fieldIndex previous])
              hprevious' hfields'

/-- The complete prelude-free block projection program list commutes with
ambient lifting. -/
@[simp] theorem ProjectionSyntaxWF.operationalProjectionCodes_liftN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.ProjectionSyntaxWF env) (levels : List VLevel)
    (params : List VExpr) (hparams : params.length = view.nparams)
    (n k : Nat) :
    (view.operationalProjectionCodes levels params).map
        (fun code => code.liftN n k) =
      view.operationalProjectionCodes levels
        (params.map fun param => param.liftN n k) := by
  unfold operationalProjectionCodes
  rw [self.specializedFields_liftN levels params hparams n k]
  rw [← structureType_liftN]
  apply self.operationalProjectionCodes_go_liftN levels params
  · exact hparams
  · rfl
  · rfl
  · simp

/-- The complete prelude-free block projection program list commutes with
ambient term instantiation. -/
@[simp] theorem ProjectionSyntaxWF.operationalProjectionCodes_instN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.ProjectionSyntaxWF env) (levels : List VLevel)
    (params : List VExpr) (hparams : params.length = view.nparams)
    (a : VExpr) (k : Nat) :
    (view.operationalProjectionCodes levels params).map
        (fun code => code.instN a k) =
      view.operationalProjectionCodes levels
        (params.map fun param => param.inst a k) := by
  unfold operationalProjectionCodes
  rw [self.specializedFields_instN levels params hparams a k]
  rw [← structureType_instN]
  apply self.operationalProjectionCodes_go_instN levels params
  · exact hparams
  · rfl
  · rfl
  · simp

/-- The complete prelude-free block projection program list commutes with an
outermost-first telescope instantiation. -/
@[simp] theorem ProjectionSyntaxWF.operationalProjectionCodes_instRevAt
    {view : VBlockStructureView} {env : VEnv}
    (self : view.ProjectionSyntaxWF env) (levels : List VLevel)
    (params : List VExpr) (hparams : params.length = view.nparams)
    (arguments : List VExpr) (offset : Nat) :
    (view.operationalProjectionCodes levels params).map
        (fun code => code.instRevAt arguments offset) =
      view.operationalProjectionCodes levels
        (params.map fun param => param.instRevAt arguments offset) := by
  induction arguments generalizing params with
  | nil =>
      simp [VStructureView.ProjectionCode.instRevAt_nil,
        VExpr.instRevAt, List.map_id']
  | cons argument arguments ih =>
      calc
        (view.operationalProjectionCodes levels params).map
              (fun code => code.instRevAt
                (argument :: arguments) offset) =
            ((view.operationalProjectionCodes levels params).map
              (fun code => code.instN argument
                (offset + arguments.length))).map
              (fun code => code.instRevAt arguments offset) := by
                simp only [List.map_map,
                  VStructureView.ProjectionCode.instRevAt_cons,
                  Function.comp_def]
        _ = (view.operationalProjectionCodes levels
              (params.map fun param => param.inst argument
                (offset + arguments.length))).map
              (fun code => code.instRevAt arguments offset) := by
                rw [self.operationalProjectionCodes_instN levels params
                  hparams argument (offset + arguments.length)]
        _ = view.operationalProjectionCodes levels
              ((params.map fun param => param.inst argument
                (offset + arguments.length)).map fun param =>
                  param.instRevAt arguments offset) := by
                apply ih
                simpa using hparams
        _ = view.operationalProjectionCodes levels
              (params.map fun param => param.instRevAt
                (argument :: arguments) offset) := by
                congr 1
                simp only [List.map_map, VExpr.instRevAt,
                  Function.comp_def]

/-- Environment-free weakening and substitution laws for the complete
prelude-free projector inventory.  A producer can retain this contract when
the environment in which the flattened block was generated is no longer the
public semantic endpoint. -/
structure OperationalCodeNaturality (view : VBlockStructureView) : Prop where
  fieldsLiftN : ∀ (levels : List VLevel) (params : List VExpr),
    params.length = view.nparams → ∀ (count cutoff : Nat),
      view.specializedFields levels
          (params.map fun param => param.liftN count cutoff) =
        VExpr.liftTelN count (view.specializedFields levels params) cutoff
  liftN : ∀ (levels : List VLevel) (params : List VExpr),
    params.length = view.nparams → ∀ (count cutoff : Nat),
      (view.operationalProjectionCodes levels params).map
          (fun code => code.liftN count cutoff) =
        view.operationalProjectionCodes levels
          (params.map fun param => param.liftN count cutoff)
  instN : ∀ (levels : List VLevel) (params : List VExpr),
    params.length = view.nparams → ∀ (argument : VExpr) (cutoff : Nat),
      (view.operationalProjectionCodes levels params).map
          (fun code => code.instN argument cutoff) =
        view.operationalProjectionCodes levels
          (params.map fun param => param.inst argument cutoff)

/-- Checked generated syntax supplies its complete environment-free
operational naturality contract. -/
theorem ProjectionSyntaxWF.operationalCodeNaturality
    {view : VBlockStructureView} {env : VEnv}
    (self : view.ProjectionSyntaxWF env) : view.OperationalCodeNaturality where
  fieldsLiftN := self.specializedFields_liftN
  liftN := self.operationalProjectionCodes_liftN
  instN := self.operationalProjectionCodes_instN

/- Compatibility projections for semantic layouts.  Operational program
naturality itself only needs the generated syntax closure retained above. -/
abbrev LayoutWF.operationalProjectionCodes_liftN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) :=
  self.toProjectionSyntaxWF.operationalProjectionCodes_liftN

abbrev LayoutWF.operationalProjectionCodes_instN
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) :=
  self.toProjectionSyntaxWF.operationalProjectionCodes_instN

abbrev LayoutWF.operationalProjectionCodes_instRevAt
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) :=
  self.toProjectionSyntaxWF.operationalProjectionCodes_instRevAt

/-- Specializing the canonical bound-variable parameter template recovers
the exact runtime-parametric flattened projection inventory. -/
theorem LayoutWF.operationalProjectionCodes_bvarRevRange_instRevAt
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (levels : List VLevel)
    (params : List VExpr) (hparams : params.length = view.nparams) :
    (view.operationalProjectionCodes levels
        (VExpr.bvarRevRange 0 view.nparams)).map
          (fun code => code.instRevAt params 0) =
      view.operationalProjectionCodes levels params := by
  rw [self.operationalProjectionCodes_instRevAt]
  · rw [← hparams, VExpr.map_instRevAt_bvarRevRange]
    simp
  · simp

/-- Earlier block-backed projector programs determine the dependent motive
for the next source-order selected field. -/
theorem WF.projectionTypeFn_hasType_of_programsPrefix
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} {levels : List VLevel}
    {params : List VExpr} {idx : Nat}
    {code : VStructureView.ProjectionCode}
    (programs : view.ProgramsWFPrefix env idx)
    (hΓ : OnCtx Γ (env.IsType U))
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (hcode : (view.projectionCodes levels params)[idx]? = some code) :
    env.HasType U Γ code.typeFn
      (.forallE (view.structureType levels params) (.sort code.fieldSort)) := by
  obtain ⟨resultLevel, hparamsSpine₀⟩ := hparamsSpine
  have hfamily : env.HasType U Γ (.const view.name levels)
      (view.familyType.instL levels) := by
    exact self.familyConst_hasType henv.ordered levels hlevels hlevelsLength
  have hstruct : env.HasType U Γ
      (view.structureType levels params) (.sort resultLevel) := by
    simpa [structureType] using hparamsSpine₀.hasType_appN hfamily
  have hidx : idx < (view.projectionCodes levels params).length :=
    (List.getElem?_eq_some_iff.1 hcode).1
  obtain ⟨fieldSort, hfieldSort, hcodeSort, -, -⟩ :=
    view.projectionCodes_get?_program_shape levels params hcode
  have hfamilyClosed : (view.familyType.instL levels).ClosedN 0 := by
    simpa using (self.familyType_closed henv.ordered).instL
  let paramsLift := params.map (VExpr.liftN 1)
  have hparamsLengthLift : paramsLift.length = view.nparams := by
    simpa [paramsLift] using hparamsLength
  have hparamsSpineLift : env.SpineWF U
      (view.structureType levels params :: Γ)
      (view.familyType.instL levels) paramsLift (.sort resultLevel) := by
    have h := hparamsSpine₀.weakN henv.ordered
      (Ctx.LiftN.one (A := view.structureType levels params))
    rw [hfamilyClosed.liftN_eq (Nat.zero_le _)] at h
    simpa [paramsLift, VExpr.liftN] using h
  have hstructLift : view.structureType levels paramsLift =
      (view.structureType levels params).lift := by
    change view.structureType levels
        (params.map fun param => param.liftN 1 0) =
      (view.structureType levels params).liftN 1 0
    exact (view.structureType_liftN levels params 1 0).symm
  have hΓLift : OnCtx (view.structureType levels params :: Γ)
      (env.IsType U) := ⟨hΓ, resultLevel, hstruct⟩
  have hmajorLift : env.HasType U
      (view.structureType levels params :: Γ) (.bvar 0)
      (view.structureType levels paramsLift) := by
    rw [hstructLift]
    exact .bvar .zero
  have hcodesLift := self.projectionCodes_liftN
    levels params hparamsLength 1 0
  have hidxLift : idx <
      (view.projectionCodes levels paramsLift).length := by
    rw [← hcodesLift]
    simpa using hidx
  have hargsLength :
      (view.projectionArgs levels paramsLift idx (.bvar 0)).length = idx :=
    view.projectionArgs_length levels paramsLift idx (.bvar 0)
      (Nat.le_of_lt hidxLift)
  have hsortTelLift := self.specializedFields_onSortTel henv.ordered
    levels hlevels hlevelsLength paramsLift hparamsLengthLift
    ⟨resultLevel, hparamsSpineLift⟩
  have hprior : ∀ {j : Nat}
      {prior : VStructureView.ProjectionCode}, j < idx →
      (view.projectionCodes levels paramsLift)[j]? = some prior →
      env.HasType U (view.structureType levels params :: Γ)
        prior.projector
        (.forallE (view.structureType levels paramsLift)
          (.app prior.typeFn.lift (.bvar 0))) := by
    intro j prior hj hpriorCode
    exact programs hj hΓLift hlevels hlevelsLength hparamsLengthLift
      ⟨resultLevel, hparamsSpineLift⟩ hpriorCode
  obtain ⟨cursor, hconsume, hprefix⟩ :=
    projectionArgsSpineAux_of_prefix henv hΓLift hmajorLift hprior
      (.sort .zero) (Nat.le_refl idx)
        (Nat.le_of_lt (by simpa using hidxLift))
  obtain ⟨next, nextSort, cursorBody, hcursor, hnextType,
      hnextSort⟩ :=
    hsortTelLift.next_of_spine henv.ordered hprefix
      (by simpa [hargsLength] using hidxLift)
  obtain ⟨field, hfield, htypeFnShape⟩ :=
    view.projectionCodes_get?_typeFn levels params hcode
  have hfieldLift :
      (view.specializedFields levels paramsLift)[idx]? =
        some (field.liftN 1 idx) := by
    rw [self.specializedFields_liftN levels params
      hparamsLength 1 0, VExpr.liftTelN_getElem?, hfield]
    simp
  have hargsLift :
      view.projectionArgs levels paramsLift idx (.bvar 0) =
        ((view.projectionCodes levels params).take idx).map fun prior =>
          .app prior.projector.lift (.bvar 0) := by
    unfold projectionArgs
    rw [← hcodesLift]
    simp [List.map_take, List.map_map,
      VStructureView.ProjectionCode.liftN, Function.comp_def]
  obtain ⟨field', semanticBody, hfield', hconsumeDomain⟩ :=
    VExpr.consumeForalls?_forallN_domain
      (view.specializedFields levels paramsLift) (.sort .zero)
      (view.projectionArgs levels paramsLift idx (.bvar 0))
      (by simpa [hargsLength] using hidxLift)
  have hfieldEq : field' = field.liftN 1 idx :=
    Option.some.inj
      (hfield'.symm.trans (by simpa [hargsLength] using hfieldLift))
  subst field'
  have hcursorDomain : cursor =
      .forallE
        ((field.liftN 1 idx).instRevAt
          (view.projectionArgs levels paramsLift idx (.bvar 0)) 0)
        semanticBody :=
    Option.some.inj (hconsume.symm.trans hconsumeDomain)
  have hnextEq : next =
      (field.liftN 1 idx).instRevAt
        (view.projectionArgs levels paramsLift idx (.bvar 0)) 0 := by
    have hforall := hcursor.symm.trans hcursorDomain
    injection hforall
  have hsortEq : nextSort = code.fieldSort := by
    rw [hargsLength] at hnextSort
    have hnextField : nextSort = fieldSort :=
      Option.some.inj (hnextSort.symm.trans hfieldSort)
    exact hnextField.trans hcodeSort.symm
  have htypeBody : env.HasType U
      (view.structureType levels params :: Γ)
      ((field.liftN 1 idx).instRevAt
        (((view.projectionCodes levels params).take idx).map fun prior =>
          .app prior.projector.lift (.bvar 0)) 0)
      (.sort code.fieldSort) := by
    rw [← hargsLift, ← hnextEq, ← hsortEq]
    exact hnextType
  rw [htypeFnShape]
  exact hstruct.lam htypeBody

/-- Earlier operational projector programs determine the dependent motive
for the next source-order field. -/
theorem LayoutWF.operationalProjectionTypeFn_hasType_of_programsPrefix
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} {levels : List VLevel}
    {params : List VExpr} {idx : Nat}
    {code : VStructureView.ProjectionCode}
    (programs : view.OperationalProgramsWFPrefix env idx)
    (hΓ : OnCtx Γ (env.IsType U))
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (hcode : (view.operationalProjectionCodes levels params)[idx]? =
      some code) :
    env.HasType U Γ code.typeFn
      (.forallE (view.structureType levels params) (.sort code.fieldSort)) := by
  obtain ⟨resultLevel, hparamsSpine₀⟩ := hparamsSpine
  have hfamily : env.HasType U Γ (.const view.name levels)
      (view.familyType.instL levels) := by
    exact self.familyConst_hasType henv.ordered levels hlevels hlevelsLength
  have hstruct : env.HasType U Γ
      (view.structureType levels params) (.sort resultLevel) := by
    simpa [structureType] using hparamsSpine₀.hasType_appN hfamily
  have hidx : idx <
      (view.operationalProjectionCodes levels params).length :=
    (List.getElem?_eq_some_iff.1 hcode).1
  obtain ⟨fieldSort, hfieldSort, hcodeSort, -, -⟩ :=
    view.operationalProjectionCodes_get?_program_shape levels params hcode
  have hfamilyClosed : (view.familyType.instL levels).ClosedN 0 := by
    simpa using (self.familyType_closed henv.ordered).instL
  let paramsLift := params.map (VExpr.liftN 1)
  have hparamsLengthLift : paramsLift.length = view.nparams := by
    simpa [paramsLift] using hparamsLength
  have hparamsSpineLift : env.SpineWF U
      (view.structureType levels params :: Γ)
      (view.familyType.instL levels) paramsLift (.sort resultLevel) := by
    have h := hparamsSpine₀.weakN henv.ordered
      (Ctx.LiftN.one (A := view.structureType levels params))
    rw [hfamilyClosed.liftN_eq (Nat.zero_le _)] at h
    simpa [paramsLift, VExpr.liftN] using h
  have hstructLift : view.structureType levels paramsLift =
      (view.structureType levels params).lift := by
    change view.structureType levels
        (params.map fun param => param.liftN 1 0) =
      (view.structureType levels params).liftN 1 0
    exact (view.structureType_liftN levels params 1 0).symm
  have hΓLift : OnCtx (view.structureType levels params :: Γ)
      (env.IsType U) := ⟨hΓ, resultLevel, hstruct⟩
  have hmajorLift : env.HasType U
      (view.structureType levels params :: Γ) (.bvar 0)
      (view.structureType levels paramsLift) := by
    rw [hstructLift]
    exact .bvar .zero
  have hcodesLift := self.operationalProjectionCodes_liftN
    levels params hparamsLength 1 0
  have hidxLift : idx <
      (view.operationalProjectionCodes levels paramsLift).length := by
    rw [← hcodesLift]
    simpa using hidx
  have hargsLength :
      (view.operationalProjectionArgs levels paramsLift idx
        (.bvar 0)).length = idx :=
    view.operationalProjectionArgs_length levels paramsLift idx (.bvar 0)
      (Nat.le_of_lt hidxLift)
  have hsortTelLift := self.specializedFields_onSortTel henv.ordered
    levels hlevels hlevelsLength paramsLift hparamsLengthLift
    ⟨resultLevel, hparamsSpineLift⟩
  have hprior : ∀ {j : Nat}
      {prior : VStructureView.ProjectionCode}, j < idx →
      (view.operationalProjectionCodes levels paramsLift)[j]? = some prior →
      env.HasType U (view.structureType levels params :: Γ)
        prior.projector
        (.forallE (view.structureType levels paramsLift)
          (.app prior.typeFn.lift (.bvar 0))) := by
    intro j prior hj hpriorCode
    exact programs hj hΓLift hlevels hlevelsLength hparamsLengthLift
      ⟨resultLevel, hparamsSpineLift⟩ hpriorCode
  obtain ⟨cursor, hconsume, hprefix⟩ :=
    operationalProjectionArgsSpineAux_of_prefix henv hΓLift hmajorLift
      hprior (.sort .zero) (Nat.le_refl idx)
        (Nat.le_of_lt (by simpa using hidxLift))
  obtain ⟨next, nextSort, cursorBody, hcursor, hnextType,
      hnextSort⟩ :=
    hsortTelLift.next_of_spine henv.ordered hprefix
      (by simpa [hargsLength] using hidxLift)
  obtain ⟨field, hfield, htypeFnShape⟩ :=
    view.operationalProjectionCodes_get?_typeFn levels params hcode
  have hfieldLift :
      (view.specializedFields levels paramsLift)[idx]? =
        some (field.liftN 1 idx) := by
    rw [self.specializedFields_liftN levels params
      hparamsLength 1 0, VExpr.liftTelN_getElem?, hfield]
    simp
  have hargsLift :
      view.operationalProjectionArgs levels paramsLift idx (.bvar 0) =
        ((view.operationalProjectionCodes levels params).take idx).map
          fun prior => .app prior.projector.lift (.bvar 0) := by
    unfold operationalProjectionArgs
    rw [← hcodesLift]
    simp [List.map_take, List.map_map,
      VStructureView.ProjectionCode.liftN, Function.comp_def]
  obtain ⟨field', semanticBody, hfield', hconsumeDomain⟩ :=
    VExpr.consumeForalls?_forallN_domain
      (view.specializedFields levels paramsLift) (.sort .zero)
      (view.operationalProjectionArgs levels paramsLift idx (.bvar 0))
      (by simpa [hargsLength] using hidxLift)
  have hfieldEq : field' = field.liftN 1 idx :=
    Option.some.inj
      (hfield'.symm.trans (by simpa [hargsLength] using hfieldLift))
  subst field'
  have hcursorDomain : cursor =
      .forallE
        ((field.liftN 1 idx).instRevAt
          (view.operationalProjectionArgs levels paramsLift idx
            (.bvar 0)) 0)
        semanticBody :=
    Option.some.inj (hconsume.symm.trans hconsumeDomain)
  have hnextEq : next =
      (field.liftN 1 idx).instRevAt
        (view.operationalProjectionArgs levels paramsLift idx (.bvar 0)) 0 := by
    have hforall := hcursor.symm.trans hcursorDomain
    injection hforall
  have hsortEq : nextSort = code.fieldSort := by
    rw [hargsLength] at hnextSort
    have hnextField : nextSort = fieldSort :=
      Option.some.inj (hnextSort.symm.trans hfieldSort)
    exact hnextField.trans hcodeSort.symm
  have htypeBody : env.HasType U
      (view.structureType levels params :: Γ)
      ((field.liftN 1 idx).instRevAt
        (((view.operationalProjectionCodes levels params).take idx).map
          fun prior => .app prior.projector.lift (.bvar 0)) 0)
      (.sort code.fieldSort) := by
    rw [← hargsLift, ← hnextEq, ← hsortEq]
    exact hnextType
  rw [htypeFnShape]
  exact hstruct.lam htypeBody

/-- A mixed typed/strengthened operational prefix determines the dependent
motive for the next field.  This is the runtime-aligned counterpart of
`operationalProjectionTypeFn_hasType_of_programsPrefix`: an earlier projector
is required only when the residual telescope actually mentions its binder. -/
theorem LayoutWF.operationalProjectionTypeFn_hasType_of_sparse
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.WF)
    {U : Nat} {Γ : List VExpr} {levels : List VLevel}
    {params : List VExpr} {idx : Nat}
    {code : VStructureView.ProjectionCode}
    (hΓ : OnCtx Γ (env.IsType U))
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (hcode : (view.operationalProjectionCodes levels params)[idx]? =
      some code)
    (sparse : ∃ cursor,
      env.SparseSpineWF U (view.structureType levels params :: Γ)
        (VExpr.forallN
          (view.specializedFields levels
            (params.map (VExpr.liftN 1)))
          (.sort .zero))
        (view.operationalProjectionArgs levels
          (params.map (VExpr.liftN 1)) idx (.bvar 0)) cursor) :
    env.HasType U Γ code.typeFn
      (.forallE (view.structureType levels params) (.sort code.fieldSort)) := by
  obtain ⟨resultLevel, hparamsSpine₀⟩ := hparamsSpine
  have hfamily : env.HasType U Γ (.const view.name levels)
      (view.familyType.instL levels) := by
    exact self.familyConst_hasType henv.ordered levels hlevels hlevelsLength
  have hstruct : env.HasType U Γ
      (view.structureType levels params) (.sort resultLevel) := by
    simpa [structureType] using hparamsSpine₀.hasType_appN hfamily
  have hidx : idx <
      (view.operationalProjectionCodes levels params).length :=
    (List.getElem?_eq_some_iff.1 hcode).1
  obtain ⟨fieldSort, hfieldSort, hcodeSort, -, -⟩ :=
    view.operationalProjectionCodes_get?_program_shape levels params hcode
  have hfamilyClosed : (view.familyType.instL levels).ClosedN 0 := by
    simpa using (self.familyType_closed henv.ordered).instL
  let paramsLift := params.map (VExpr.liftN 1)
  have hparamsLengthLift : paramsLift.length = view.nparams := by
    simpa [paramsLift] using hparamsLength
  have hparamsSpineLift : env.SpineWF U
      (view.structureType levels params :: Γ)
      (view.familyType.instL levels) paramsLift (.sort resultLevel) := by
    have h := hparamsSpine₀.weakN henv.ordered
      (Ctx.LiftN.one (A := view.structureType levels params))
    rw [hfamilyClosed.liftN_eq (Nat.zero_le _)] at h
    simpa [paramsLift, VExpr.liftN] using h
  have hstructLift : view.structureType levels paramsLift =
      (view.structureType levels params).lift := by
    change view.structureType levels
        (params.map fun param => param.liftN 1 0) =
      (view.structureType levels params).liftN 1 0
    exact (view.structureType_liftN levels params 1 0).symm
  have hΓLift : OnCtx (view.structureType levels params :: Γ)
      (env.IsType U) := ⟨hΓ, resultLevel, hstruct⟩
  have hcodesLift := self.operationalProjectionCodes_liftN
    levels params hparamsLength 1 0
  have hidxLift : idx <
      (view.operationalProjectionCodes levels paramsLift).length := by
    rw [← hcodesLift]
    simpa using hidx
  have hargsLength :
      (view.operationalProjectionArgs levels paramsLift idx
        (.bvar 0)).length = idx :=
    view.operationalProjectionArgs_length levels paramsLift idx (.bvar 0)
      (Nat.le_of_lt hidxLift)
  have hsortBound :
      idx < (view.fieldSorts.map (VLevel.inst levels)).length := by
    simpa [specializedFields, fields, view.fieldSorts_length] using hidxLift
  have hsortTelLift := self.specializedFields_onSortTel henv.ordered
    levels hlevels hlevelsLength paramsLift hparamsLengthLift
    ⟨resultLevel, hparamsSpineLift⟩
  obtain ⟨cursor, hsparse⟩ := sparse
  change env.SparseSpineWF U
    (view.structureType levels params :: Γ)
    (VExpr.forallN (view.specializedFields levels paramsLift) (.sort .zero))
    (view.operationalProjectionArgs levels paramsLift idx (.bvar 0)) cursor
    at hsparse
  have hconsume := hsparse.consumeForalls_eq
  have hsortCursor := hsortTelLift.toSortCursor (.sort .zero)
  obtain ⟨next, nextSort, cursorBody, hcursor, hnextType,
      hnextSort⟩ :=
    hsortCursor.next_of_sparse henv hΓLift hsparse
      (by simpa [hargsLength] using hsortBound)
  obtain ⟨field, hfield, htypeFnShape⟩ :=
    view.operationalProjectionCodes_get?_typeFn levels params hcode
  have hfieldLift :
      (view.specializedFields levels paramsLift)[idx]? =
        some (field.liftN 1 idx) := by
    rw [self.specializedFields_liftN levels params
      hparamsLength 1 0, VExpr.liftTelN_getElem?, hfield]
    simp
  have hargsLift :
      view.operationalProjectionArgs levels paramsLift idx (.bvar 0) =
        ((view.operationalProjectionCodes levels params).take idx).map
          fun prior => .app prior.projector.lift (.bvar 0) := by
    unfold operationalProjectionArgs
    rw [← hcodesLift]
    simp [List.map_take, List.map_map,
      VStructureView.ProjectionCode.liftN, Function.comp_def]
  obtain ⟨field', semanticBody, hfield', hconsumeDomain⟩ :=
    VExpr.consumeForalls?_forallN_domain
      (view.specializedFields levels paramsLift) (.sort .zero)
      (view.operationalProjectionArgs levels paramsLift idx (.bvar 0))
      (by simpa [hargsLength] using hidxLift)
  have hfieldEq : field' = field.liftN 1 idx :=
    Option.some.inj
      (hfield'.symm.trans (by simpa [hargsLength] using hfieldLift))
  subst field'
  have hcursorDomain : cursor =
      .forallE
        ((field.liftN 1 idx).instRevAt
          (view.operationalProjectionArgs levels paramsLift idx
            (.bvar 0)) 0)
        semanticBody :=
    Option.some.inj (hconsume.symm.trans hconsumeDomain)
  have hnextEq : next =
      (field.liftN 1 idx).instRevAt
        (view.operationalProjectionArgs levels paramsLift idx (.bvar 0)) 0 := by
    have hforall := hcursor.symm.trans hcursorDomain
    injection hforall
  have hsortEq : nextSort = code.fieldSort := by
    rw [hargsLength] at hnextSort
    have hnextField : nextSort = fieldSort :=
      Option.some.inj (hnextSort.symm.trans hfieldSort)
    exact hnextField.trans hcodeSort.symm
  have htypeBody : env.HasType U
      (view.structureType levels params :: Γ)
      ((field.liftN 1 idx).instRevAt
        (((view.operationalProjectionCodes levels params).take idx).map
          fun prior => .app prior.projector.lift (.bvar 0)) 0)
      (.sort code.fieldSort) := by
    rw [← hargsLift, ← hnextEq, ← hsortEq]
    exact hnextType
  rw [htypeFnShape]
  exact hstruct.lam htypeBody

/-- A typed selected-minor prefix determines the corresponding prefix of
actual mutual-recursor projector programs. -/
theorem WF.toProgramsWFPrefix_of_minorsWFPrefix
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) (henv : env.ConversionRegular)
    {limit : Nat} (minorsWF : view.MinorsWFPrefix env limit) :
    view.ProgramsWFPrefix env limit := by
  intro U Γ levels params idx code hlimit hΓ hlevels hlevelsLength
    hparamsLength hparamsSpine hcode
  induction idx using Nat.strongRecOn generalizing U Γ levels params code with
  | _ idx ih =>
    obtain ⟨resultLevel, hparamsSpine₀⟩ := hparamsSpine
    have hfamily : env.HasType U Γ (.const view.name levels)
        (view.familyType.instL levels) := by
      exact self.familyConst_hasType henv.ordered levels hlevels hlevelsLength
    have hstruct : env.HasType U Γ
        (view.structureType levels params) (.sort resultLevel) := by
      simpa [structureType] using hparamsSpine₀.hasType_appN hfamily
    have hidx : idx < (view.projectionCodes levels params).length :=
      (List.getElem?_eq_some_iff.1 hcode).1
    obtain ⟨fieldSort, hfieldSort, hcodeSort, -, hprojectorShape⟩ :=
      view.projectionCodes_get?_program_shape levels params hcode
    have hsortTel := self.specializedFields_onSortTel henv.ordered levels
      hlevels hlevelsLength params hparamsLength
      ⟨resultLevel, hparamsSpine₀⟩
    have hfieldSortWF : code.fieldSort.WF U := by
      rw [hcodeSort]
      exact hsortTel.sortWF hΓ hfieldSort
    have hmotiveLevel : view.generation.motiveLevel.inst
        (view.projectionLevels code.fieldSort levels) = code.fieldSort := by
      rw [hcodeSort]
      rw [List.getElem?_map] at hfieldSort
      obtain ⟨rawSort, hrawSort, rfl⟩ := Option.map_eq_some_iff.1 hfieldSort
      exact self.motiveLevel_projectionLevels rawSort
        (List.mem_iff_getElem?.2 ⟨idx, hrawSort⟩) levels
    subst fieldSort
    have programsBefore : view.ProgramsWFPrefix env idx := by
      intro U' Γ' levels' params' j prior hj hΓ' hlevels'
        hlevelsLength' hparamsLength' hparamsSpine' hprior
      exact ih j hj (Nat.lt_trans hj hlimit) hΓ' hlevels'
        hlevelsLength' hparamsLength' hparamsSpine' hprior
    have htypeFn := self.projectionTypeFn_hasType_of_programsPrefix henv
      programsBefore hΓ hlevels hlevelsLength hparamsLength
      ⟨resultLevel, hparamsSpine₀⟩ hcode
    have hfamilyClosed : (view.familyType.instL levels).ClosedN 0 := by
      simpa using (self.familyType_closed henv.ordered).instL
    let paramsLift := params.map (VExpr.liftN 1)
    have hparamsLengthLift : paramsLift.length = view.nparams := by
      simpa [paramsLift] using hparamsLength
    have hparamsSpineLift : env.SpineWF U
        (view.structureType levels params :: Γ)
        (view.familyType.instL levels) paramsLift (.sort resultLevel) := by
      have h := hparamsSpine₀.weakN henv.ordered
        (Ctx.LiftN.one (A := view.structureType levels params))
      rw [hfamilyClosed.liftN_eq (Nat.zero_le _)] at h
      simpa [paramsLift, VExpr.liftN] using h
    have hstructLift : view.structureType levels paramsLift =
        (view.structureType levels params).lift := by
      change view.structureType levels
          (params.map fun param => param.liftN 1 0) =
        (view.structureType levels params).liftN 1 0
      exact (view.structureType_liftN levels params 1 0).symm
    have hΓLift : OnCtx (view.structureType levels params :: Γ)
        (env.IsType U) := ⟨hΓ, resultLevel, hstruct⟩
    have hmajorLift : env.HasType U
        (view.structureType levels params :: Γ) (.bvar 0)
        (view.structureType levels paramsLift) := by
      rw [hstructLift]
      exact .bvar .zero
    have hcodesLift := self.projectionCodes_liftN levels params
      hparamsLength 1 0
    have hcodeLift :
        (view.projectionCodes levels paramsLift)[idx]? =
          some (code.liftN 1 0) := by
      rw [← hcodesLift, List.getElem?_map, hcode]
      rfl
    have htypeFnLift : env.HasType U
        (view.structureType levels params :: Γ) (code.liftN 1 0).typeFn
        (.forallE (view.structureType levels paramsLift)
          (.sort code.fieldSort)) := by
      have h := htypeFn.weakN henv.ordered
        (Ctx.LiftN.one (A := view.structureType levels params))
      simpa [VStructureView.ProjectionCode.liftN, hstructLift,
        VExpr.liftN] using h
    have hminorLift := minorsWF hlimit hΓLift hlevels hlevelsLength
      hparamsLengthLift ⟨resultLevel, hparamsSpineLift⟩ hcodeLift
    obtain ⟨fieldSortLift, _, hcodeSortLift, hminorLiftShape,
        _hprojectorLiftShape⟩ :=
      view.projectionCodes_get?_program_shape levels paramsLift hcodeLift
    have hfieldSortLiftEq : fieldSortLift = code.fieldSort := by
      simpa [VStructureView.ProjectionCode.liftN] using hcodeSortLift.symm
    subst fieldSortLift
    rw [hminorLiftShape] at hminorLift
    have hbody := self.recursorProjection_hasType henv hΓLift
      code.fieldSort hfieldSortWF levels hlevels hlevelsLength paramsLift
      hparamsLengthLift ⟨resultLevel, hparamsSpineLift⟩
      (code.liftN 1 0).typeFn idx htypeFnLift hmotiveLevel hminorLift
      hmajorLift
    let motives := view.projectionMotives levels params code.fieldSort
      code.typeFn
    let originalMinors := view.generation.flatCtors.map fun constructor =>
      view.projectionMinor constructor code.fieldSort levels params
        (view.specializedFields levels params) motives idx
    have hmotivesLength : motives.length = view.generation.familyCount := by
      simp [motives]
    have hmotivesLift : motives.map (VExpr.liftN 1) =
        view.projectionMotives levels paramsLift code.fieldSort
          (code.liftN 1 0).typeFn := by
      simpa [motives, paramsLift, VStructureView.ProjectionCode.liftN] using
        self.toLayoutWF.toProjectionSyntaxWF.projectionMotives_liftN
          code.fieldSort levels params
          hparamsLength code.typeFn 1 0
    have hfieldsLift := self.specializedFields_liftN levels params
      hparamsLength 1 0
    have hfieldIndex : idx <
        (view.specializedFields levels params).length := by
      simpa using hidx
    have hminorsLift : originalMinors.map (VExpr.liftN 1) =
        view.generation.flatCtors.map fun constructor =>
          view.projectionMinor constructor code.fieldSort levels paramsLift
            (view.specializedFields levels paramsLift)
            (view.projectionMotives levels paramsLift code.fieldSort
              (code.liftN 1 0).typeFn) idx := by
      simp only [originalMinors, List.map_map]
      apply List.map_congr_left
      intro constructor hconstructor
      have hout := self.toLayoutWF.toProjectionSyntaxWF.projectionMinor_liftN
        hconstructor code.fieldSort
        levels params (view.specializedFields levels params) motives
        hparamsLength rfl hmotivesLength idx hfieldIndex 1 0
      rw [← hfieldsLift, hmotivesLift] at hout
      exact hout
    rw [hprojectorShape]
    apply hstruct.lam
    simpa [paramsLift, motives, originalMinors,
      VStructureView.ProjectionCode.liftN, VExpr.liftN,
      hmotivesLift, hminorsLift] using hbody

/-- A complete selected-minor certificate determines every block-backed
projector program. -/
theorem WF.toProgramsWF_of_minors
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) (henv : env.ConversionRegular)
    (minorsWF : view.MinorsWF env) : view.ProgramsWF env := by
  intro U Γ levels params idx code hΓ hlevels hlevelsLength
    hparamsLength hparamsSpine hcode
  exact self.toProgramsWFPrefix_of_minorsWFPrefix henv
    (limit := idx + 1)
    (fun _ hΓ hlevels hlevelsLength hparamsLength hparamsSpine hcode =>
      minorsWF hΓ hlevels hlevelsLength hparamsLength hparamsSpine hcode)
    (Nat.lt_succ_self idx) hΓ hlevels hlevelsLength hparamsLength
    hparamsSpine hcode

/-- Specializing the selected generated rule's field binders by an arbitrary
complete common prefix yields the corresponding selected field telescope. -/
private theorem LayoutWF.ruleFieldBinders_specializeDirect
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (fieldSort : VLevel)
    (levels : List VLevel) (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (motives minors : List VExpr)
    (hmotives : motives.length = view.generation.familyCount)
    (hminors : minors.length = view.generation.minorCount) :
    (((view.generation.ruleFieldBinders view.blockConstructor).map
        (VExpr.instL (view.projectionLevels fieldSort levels))).zipIdx.map
      fun entry => entry.1.instRevAt
        (params ++ motives ++ minors) entry.2) =
      view.specializedFields levels params := by
  let rawFields := view.constructor.rawFields view.nparams
  let recFields := view.blockConstructor.ctor.fieldsR view.uvars view.nparams
    view.generation.elimination
  let pLevels := view.projectionLevels fieldSort levels
  let after := motives ++ minors
  have hsource := view.sourceLevels_projectionLevels fieldSort levels
    hlevelsLength
  have hrecFields : recFields.map (VExpr.instL pLevels) =
      rawFields.map (VExpr.instL levels) := by
    simp only [recFields, rawFields, NormalizedCtor.fieldsR,
      List.map_map, Function.comp_def, VExpr.instL_instL]
    rw [show (VLevel.params' view.uvars
        view.generation.elimination.offset).map (VLevel.inst pLevels) =
          levels by
      simpa [BlockGenerationChecked.sourceLevels, pLevels] using hsource]
    rfl
  have hafterLength : after.length =
      view.generation.familyCount + view.generation.minorCount := by
    simp [after, hmotives, hminors]
  have hfieldBinders := VExpr.map_liftTelN_instRevAt_append
    (rawFields.map (VExpr.instL levels)) params after 0
  rw [hafterLength] at hfieldBinders
  rw [VExpr.instRevAt_map_instL_zipIdx] at hfieldBinders
  change (((VExpr.liftTelN
      (view.generation.familyCount + view.generation.minorCount)
      recFields 0).map (VExpr.instL pLevels)).zipIdx.map fun entry =>
        entry.1.instRevAt
          (params ++ motives ++ minors) entry.2) = _
  rw [VExpr.liftTelN_instL, hrecFields]
  rw [show params ++ motives ++ minors = params ++ after by
    simp [after, List.append_assoc]]
  rw [hfieldBinders]
  rfl

/-- Convert a typed full recursor application and a concrete selected-field
spine into the exact registered capture of the selected generated rule. -/
private theorem LayoutWF.projectionRuleCaptureSpineLocal
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env)
    {U : Nat} {Γ : List VExpr}
    (fieldSort : VLevel) (levels : List VLevel)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (motives minors : List VExpr)
    (hmotives : motives.length = view.generation.familyCount)
    (hminors : minors.length = view.generation.minorCount)
    {fieldArgs suffix : List VExpr} (hfieldArgsLength :
      fieldArgs.length = (view.specializedFields levels params).length)
    {sourceResult : VExpr}
    (hsource : env.SpineWF U Γ
      ((view.generation.recType view.family).instL
        (view.projectionLevels fieldSort levels))
      ((params ++ motives ++ minors) ++ suffix) sourceResult)
    (hfields : env.SpineWF U Γ
      (VExpr.forallN (view.specializedFields levels params) (.sort .zero))
      fieldArgs (.sort .zero)) :
    ∃ ruleIndex B,
      view.generation.ruleEntry ruleIndex view.blockConstructor ∧
      env.SpineWF U Γ
        ((view.generation.rule ruleIndex view.blockConstructor).type.instL
          (view.projectionLevels fieldSort levels))
        ((params ++ motives ++ minors) ++ fieldArgs) B := by
  let gen := view.generation
  let c := view.blockConstructor
  let pLevels := view.projectionLevels fieldSort levels
  let fields := view.specializedFields levels params
  let m := fields.length
  let commonArgs := params ++ motives ++ minors
  let ruleContinuation := VExpr.instRev
    (VExpr.forallN
      ((gen.ruleFieldBinders c).map (VExpr.instL pLevels))
      ((gen.ruleResult c).instL pLevels)) commonArgs
  have hdomains := self.ruleFieldBinders_specializeDirect fieldSort levels
    hlevelsLength params hparamsLength motives minors hmotives hminors
  have htel : VExpr.telN m ruleContinuation = fields := by
    unfold ruleContinuation
    rw [VExpr.instRev_forallN_projection]
    rw [show (((gen.ruleFieldBinders c).map
        (VExpr.instL pLevels)).zipIdx.map fun entry =>
          entry.1.instRevAt commonArgs entry.2) = fields by
      simpa [gen, c, pLevels, fields, commonArgs] using hdomains]
    simpa [m] using VExpr.telN_forallN_length fields
      ((gen.ruleResult c).instL pLevels |>.instRevAt commonArgs
        (gen.ruleFieldBinders c |>.map (VExpr.instL pLevels) |>.length))
  let residual := VExpr.dropN m ruleContinuation
  have hcontinuation : ruleContinuation = VExpr.forallN fields residual := by
    calc
      ruleContinuation = VExpr.forallN (VExpr.telN m ruleContinuation)
          (VExpr.dropN m ruleContinuation) :=
        (VExpr.forallN_telN_dropN m ruleContinuation).symm
      _ = _ := by rw [htel]
  have hfieldsRule : env.SpineWF U Γ ruleContinuation fieldArgs
      (residual.instRev fieldArgs) := by
    have h := hfields.retarget (by simpa [fields, m] using hfieldArgsLength)
      residual
    rw [← hcontinuation] at h
    exact h
  obtain ⟨ruleIndex, hentry⟩ :=
    List.mem_iff_getElem?.1 view.blockConstructor_mem
  have hresultIndices : view.constructor.view.resultIndices = [] := by
    apply List.length_eq_zero_iff.1
    have hlength : view.constructor.view.resultIndices.length =
        view.family.view.indices.length := by
      simpa [c, blockConstructor] using
        self.generationEnv.viewResultIndices_length view.blockConstructor_mem
    rw [hlength, view.checked_indices_eq]
    rfl
  have hruleIdx : gen.ruleIdx c = [] := by
    simp [gen, c, BlockGenerationChecked.ruleIdx, blockConstructor,
      NormalizedCtor.resultIndicesR, hresultIndices]
  have hparamsSource : params.length = view.source.nparams := by
    change params.length = view.source.nparams
    exact hparamsLength
  have hcommonLength : commonArgs.length =
      view.source.nparams + gen.familyCount + gen.minorCount := by
    simp only [commonArgs, List.length_append]
    rw [hparamsSource, hmotives, hminors]
  have hcResultIndices : c.ctor.view.resultIndices = [] := by
    simpa [c, blockConstructor] using hresultIndices
  have hfArgsLength : commonArgs.length = gen.ruleMajorArity c := by
    rw [hcommonLength]
    simp [BlockGenerationChecked.ruleMajorArity,
      NormalizedCtor.resultIndicesR, hcResultIndices]
  have htake : commonArgs.take
      (view.source.nparams + gen.familyCount + gen.minorCount) =
        commonArgs :=
    List.take_of_length_le (Nat.le_of_eq hcommonLength)
  have hdrop : (params ++ fieldArgs).drop view.source.nparams =
      fieldArgs := by
    rw [← hparamsSource, List.drop_left]
  have hsource' : env.SpineWF U Γ
      (VExpr.forallN (gen.ruleCommonBinders.map (VExpr.instL pLevels))
        (VExpr.forallN
          ((gen.recIndexBinders view.family).map (VExpr.instL pLevels))
          (.forallE ((gen.recMajorDomain view.family).instL pLevels)
            ((gen.recMotiveResult view.family).instL pLevels))))
      (commonArgs ++ suffix) sourceResult := by
    have h := hsource
    rw [gen.recType_instL_common] at h
    simpa [gen, pLevels, commonArgs, List.append_assoc] using h
  have hfieldsForRule : env.SpineWF U Γ
      (VExpr.instRev
        (VExpr.forallN
          ((gen.ruleFieldBinders c).map (VExpr.instL pLevels))
          ((gen.ruleResult c).instL pLevels))
        (commonArgs.take
          (view.source.nparams + gen.familyCount + gen.minorCount)))
      ((params ++ fieldArgs).drop view.source.nparams)
      (residual.instRev fieldArgs) := by
    rw [htake, hdrop]
    exact hfieldsRule
  have hcapture := gen.ruleCaptureSpine_of_prefix_fields
    (fArgs := commonArgs) (aArgs := params ++ fieldArgs)
    (suffix := suffix) ruleIndex c pLevels hfArgsLength hsource'
      hfieldsForRule
  refine ⟨ruleIndex, residual.instRev fieldArgs, hentry, ?_⟩
  unfold BlockGenerationChecked.ruleCaptureValues at hcapture
  rw [htake, hdrop] at hcapture
  simpa [gen, c, pLevels, commonArgs, List.append_assoc] using hcapture

/-- Specializing the selected rule's generated field binders by the complete
lifted common capture prefix yields the canonical lifted selected fields. -/
private theorem LayoutWF.ruleFieldBinders_specialize
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (fieldSort : VLevel)
    (levels : List VLevel) (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (motives minors : List VExpr)
    (hmotives : motives.length = view.generation.familyCount)
    (hminors : minors.length = view.generation.minorCount) :
    let fields := view.specializedFields levels params
    let m := fields.length
    let commonArgs := params.map (VExpr.liftN m) ++
      motives.map (VExpr.liftN m) ++ minors.map (VExpr.liftN m)
    (((view.generation.ruleFieldBinders view.blockConstructor).map
        (VExpr.instL (view.projectionLevels fieldSort levels))).zipIdx.map
      fun entry => entry.1.instRevAt commonArgs entry.2) =
      VExpr.liftTelN m fields 0 := by
  let fields := view.specializedFields levels params
  let m := fields.length
  let paramsLift := params.map (VExpr.liftN m)
  let motivesLift := motives.map (VExpr.liftN m)
  let minorsLift := minors.map (VExpr.liftN m)
  let after := motivesLift ++ minorsLift
  let commonArgs := paramsLift ++ after
  let rawFields := view.constructor.rawFields view.nparams
  let recFields := view.blockConstructor.ctor.fieldsR view.uvars view.nparams
    view.generation.elimination
  let pLevels := view.projectionLevels fieldSort levels
  have hsource := view.sourceLevels_projectionLevels fieldSort levels
    hlevelsLength
  have hrecFields : recFields.map (VExpr.instL pLevels) =
      rawFields.map (VExpr.instL levels) := by
    simp only [recFields, rawFields, NormalizedCtor.fieldsR,
      List.map_map, Function.comp_def, VExpr.instL_instL]
    rw [show (VLevel.params' view.uvars
        view.generation.elimination.offset).map (VLevel.inst pLevels) =
          levels by
      simpa [BlockGenerationChecked.sourceLevels, pLevels] using hsource]
    rfl
  have hafterLength : after.length =
      view.generation.familyCount + view.generation.minorCount := by
    simp [after, motivesLift, minorsLift, hmotives, hminors]
  have hfieldBinders := VExpr.map_liftTelN_instRevAt_append
    (rawFields.map (VExpr.instL levels)) paramsLift after 0
  rw [hafterLength] at hfieldBinders
  rw [VExpr.instRevAt_map_instL_zipIdx] at hfieldBinders
  have hspecialized : view.specializedFields levels paramsLift =
      VExpr.liftTelN m fields 0 := by
    simpa [paramsLift, fields, m] using
      self.specializedFields_liftN levels params hparamsLength m 0
  dsimp only
  change (((VExpr.liftTelN
      (view.generation.familyCount + view.generation.minorCount)
      recFields 0).map (VExpr.instL pLevels)).zipIdx.map fun entry =>
        entry.1.instRevAt
          (paramsLift ++ motivesLift ++ minorsLift) entry.2) = _
  rw [VExpr.liftTelN_instL, hrecFields]
  rw [show paramsLift ++ motivesLift ++ minorsLift =
      paramsLift ++ after by simp [after, List.append_assoc]]
  rw [hfieldBinders]
  rw [← hspecialized]
  rfl

/-- The lifted parameters, complete motive/minor inventories, and canonical
field variables form the exact capture spine of the selected generated rule. -/
theorem WF.projectionRuleCaptureSpine
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    (fieldSort : VLevel) (hfieldSort : fieldSort.WF U)
    (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (typeFn : VExpr) (fieldIndex : Nat)
    (typeFnType : env.HasType U Γ typeFn
      (.forallE (view.structureType levels params) (.sort fieldSort)))
    (hmotiveLevel : view.generation.motiveLevel.inst
      (view.projectionLevels fieldSort levels) = fieldSort)
    (selectedMinorType : env.HasType U Γ
      (view.projectionMinor view.blockConstructor fieldSort levels params
        (view.specializedFields levels params)
        (view.projectionMotives levels params fieldSort typeFn) fieldIndex)
      (view.generatedProjectionMinorType view.blockConstructor fieldSort
        levels params
        (view.projectionMotives levels params fieldSort typeFn))) :
    let fields := view.specializedFields levels params
    let m := fields.length
    let motives := view.projectionMotives levels params fieldSort typeFn
    let minors := view.generation.flatCtors.map fun constructor =>
      view.projectionMinor constructor fieldSort levels params fields motives
        fieldIndex
    ∃ ruleIndex B,
      view.generation.ruleEntry ruleIndex view.blockConstructor ∧
      env.SpineWF U (fields.reverse ++ Γ)
        ((view.generation.rule ruleIndex view.blockConstructor).type.instL
          (view.projectionLevels fieldSort levels))
        (params.map (VExpr.liftN m) ++ motives.map (VExpr.liftN m) ++
          minors.map (VExpr.liftN m) ++ VExpr.bvarRevRange 0 m) B := by
  let gen := view.generation
  let pLevels := view.projectionLevels fieldSort levels
  let fields := view.specializedFields levels params
  let m := fields.length
  let motives := view.projectionMotives levels params fieldSort typeFn
  let minors := gen.flatCtors.map fun constructor =>
    view.projectionMinor constructor fieldSort levels params fields motives
      fieldIndex
  let commonArgs := params.map (VExpr.liftN m) ++
    motives.map (VExpr.liftN m) ++ minors.map (VExpr.liftN m)
  have hmotivesLength : motives.length = gen.familyCount := by
    simp [motives, gen]
  have hminorsLength : minors.length = gen.minorCount := by
    simp [minors, gen, BlockGenerationChecked.minorCount]
  have hfieldsOnTel : env.OnTel U Γ fields := by
    simpa [fields] using
      (self.specializedFields_onSortTel henv.ordered levels hlevels
        hlevelsLength params hparamsLength paramsSpine).toOnTel
  have hfieldsCtx : OnCtx (fields.reverse ++ Γ) (env.IsType U) :=
    hfieldsOnTel.toOnCtx hΓ
  have hcommon := self.projectionCommonSpine henv hΓ fieldSort hfieldSort
    levels hlevels hlevelsLength params hparamsLength paramsSpine typeFn
    fieldIndex typeFnType hmotiveLevel selectedMinorType
  have hcommonWeak := hcommon.weakN henv.ordered
    (Ctx.LiftN.zero (n := m) (Γ := Γ) fields.reverse
      (h := by simp [m]))
  have hrecTypeClosed :
      ((gen.recType view.family).instL pLevels).ClosedN 0 := by
    simpa [gen, pLevels] using
      (self.generationEnv.recType_closedN view.family_mem).instL
  rw [hrecTypeClosed.liftN_eq (Nat.zero_le _)] at hcommonWeak
  have hcommonArgsMap :
      (params ++ motives ++ minors).map (VExpr.liftN m) = commonArgs := by
    simp [commonArgs, List.map_append]
  rw [hcommonArgsMap] at hcommonWeak
  rw [gen.recType_instL_common] at hcommonWeak
  let oldResult := VExpr.forallN
    ((gen.recIndexBinders view.family).map (VExpr.instL pLevels))
    (.forallE ((gen.recMajorDomain view.family).instL pLevels)
      ((gen.recMotiveResult view.family).instL pLevels))
  have hsource : env.SpineWF U (fields.reverse ++ Γ)
      (VExpr.forallN (gen.ruleCommonBinders.map (VExpr.instL pLevels))
        oldResult) (commonArgs ++ [])
      ((VExpr.forallE (view.structureType levels params)
        (.app typeFn.lift (.bvar 0))).liftN m) := by
    simpa [oldResult, commonArgs, fields, m] using hcommonWeak
  have hfieldBase := hfieldsOnTel.selfSpineWF
    (B := .sort .zero) (Δ := ([] : List VExpr))
  have hfieldBase' : env.SpineWF U (fields.reverse ++ Γ)
      (VExpr.forallN (VExpr.liftTelN m fields 0) (.sort .zero))
      (VExpr.bvarRevRange 0 m) (.sort .zero) := by
    simpa [m, VExpr.liftN_forallN, VExpr.liftN] using hfieldBase
  let ruleContinuation := VExpr.instRev
    (VExpr.forallN
      ((gen.ruleFieldBinders view.blockConstructor).map
        (VExpr.instL pLevels))
      ((gen.ruleResult view.blockConstructor).instL pLevels)) commonArgs
  have hdomains := self.ruleFieldBinders_specialize fieldSort levels
    hlevelsLength params hparamsLength motives minors hmotivesLength
    hminorsLength
  have htel : VExpr.telN m ruleContinuation =
      VExpr.liftTelN m fields 0 := by
    unfold ruleContinuation
    rw [VExpr.instRev_forallN_projection]
    rw [hdomains]
    simpa only [VExpr.liftTelN_length] using
      VExpr.telN_forallN_length
      (VExpr.liftTelN m fields 0)
      ((gen.ruleResult view.blockConstructor).instL pLevels |>.instRevAt
        commonArgs (gen.ruleFieldBinders view.blockConstructor |>.map
          (VExpr.instL pLevels) |>.length))
  let residual := VExpr.dropN m ruleContinuation
  have hcontinuation : ruleContinuation =
      VExpr.forallN (VExpr.liftTelN m fields 0) residual := by
    calc
      ruleContinuation = VExpr.forallN (VExpr.telN m ruleContinuation)
          (VExpr.dropN m ruleContinuation) :=
        (VExpr.forallN_telN_dropN m ruleContinuation).symm
      _ = _ := by rw [htel]
  have hfieldLength : (VExpr.bvarRevRange 0 m).length =
      (VExpr.liftTelN m fields 0).length := by
    rw [VExpr.bvarRevRange_length, VExpr.liftTelN_length]
  have hfieldsSpine := hfieldBase'.retarget hfieldLength residual
  rw [← hcontinuation] at hfieldsSpine
  obtain ⟨ruleIndex, hentry⟩ :=
    List.mem_iff_getElem?.1 view.blockConstructor_mem
  let fArgs := commonArgs
  let aArgs := params.map (VExpr.liftN m) ++ VExpr.bvarRevRange 0 m
  have hresultIndices : view.constructor.view.resultIndices = [] := by
    apply List.length_eq_zero_iff.1
    have hlength : view.constructor.view.resultIndices.length =
        view.family.view.indices.length := by
      simpa [blockConstructor] using
        self.generationEnv.viewResultIndices_length
          view.blockConstructor_mem
    rw [hlength, view.checked_indices_eq]
    rfl
  have hruleIdx : gen.ruleIdx view.blockConstructor = [] := by
    simp [BlockGenerationChecked.ruleIdx, blockConstructor,
      NormalizedCtor.resultIndicesR, hresultIndices]
  have hfArgsLength : fArgs.length =
      gen.ruleMajorArity view.blockConstructor := by
    simp [fArgs, commonArgs, BlockGenerationChecked.ruleMajorArity,
      hmotivesLength, hminorsLength, hparamsLength, hruleIdx,
      BlockGenerationChecked.ruleIdx, blockConstructor,
      NormalizedCtor.resultIndicesR, hresultIndices]
    change view.source.nparams + (gen.familyCount + gen.minorCount) =
      view.source.nparams + gen.familyCount + gen.minorCount
    omega
  have hparamsSource : params.length = view.source.nparams := by
    change params.length = view.source.nparams
    exact hparamsLength
  have hfArgsCommon : fArgs.length =
      view.source.nparams + gen.familyCount + gen.minorCount := by
    simp [fArgs, commonArgs, hparamsLength, hmotivesLength,
      hminorsLength]
    omega
  have htake : fArgs.take
      (view.source.nparams + gen.familyCount + gen.minorCount) =
      commonArgs := by
    change commonArgs.take
      (view.source.nparams + gen.familyCount + gen.minorCount) = commonArgs
    exact List.take_of_length_le (Nat.le_of_eq hfArgsCommon)
  have hdrop : aArgs.drop view.source.nparams =
      VExpr.bvarRevRange 0 m := by
    dsimp only [aArgs]
    rw [← hparamsSource]
    have hmapLength : (params.map (VExpr.liftN m)).length =
        params.length := by simp
    rw [← hmapLength, List.drop_left]
  have hfieldsForRule : env.SpineWF U (fields.reverse ++ Γ)
      (VExpr.instRev
        (VExpr.forallN
          ((gen.ruleFieldBinders view.blockConstructor).map
            (VExpr.instL pLevels))
          ((gen.ruleResult view.blockConstructor).instL pLevels))
        (fArgs.take
          (view.source.nparams + gen.familyCount + gen.minorCount)))
      (aArgs.drop view.source.nparams)
      (residual.instRev (VExpr.bvarRevRange 0 m)) := by
    rw [htake, hdrop]
    exact hfieldsSpine
  have hcapture := gen.ruleCaptureSpine_of_prefix_fields
    (fArgs := fArgs) (aArgs := aArgs) (suffix := []) ruleIndex
    view.blockConstructor pLevels hfArgsLength hsource hfieldsForRule
  refine ⟨ruleIndex,
    residual.instRev (VExpr.bvarRevRange 0 m), hentry, ?_⟩
  unfold BlockGenerationChecked.ruleCaptureValues at hcapture
  rw [htake, hdrop] at hcapture
  change env.SpineWF U (fields.reverse ++ Γ)
    ((gen.rule ruleIndex view.blockConstructor).type.instL pLevels)
    (params.map (VExpr.liftN m) ++ motives.map (VExpr.liftN m) ++
      minors.map (VExpr.liftN m) ++ VExpr.bvarRevRange 0 m)
    (residual.instRev (VExpr.bvarRevRange 0 m))
  have hcanonical :
      params.map (VExpr.liftN m) ++ motives.map (VExpr.liftN m) ++
          minors.map (VExpr.liftN m) ++ VExpr.bvarRevRange 0 m =
        commonArgs ++ VExpr.bvarRevRange 0 m := by
    simp only [commonArgs, List.append_assoc]
  rw [hcanonical]
  exact hcapture

/-- The lifted operational motive/minor inventories and canonical field
variables form the exact selected-rule capture spine. -/
theorem LayoutWF.projectionRuleCaptureSpineWith
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    (fieldSort : VLevel) (hfieldSort : fieldSort.WF U)
    (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (params : List VExpr) (hparamsLength : params.length = view.nparams)
    (paramsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (typeFn dummyType dummyValue : VExpr) (fieldIndex : Nat)
    (typeFnType : env.HasType U Γ typeFn
      (.forallE (view.structureType levels params) (.sort fieldSort)))
    (dummyTypeType : env.HasType U Γ dummyType (.sort fieldSort))
    (dummyValueType : env.HasType U Γ dummyValue dummyType)
    (hmotiveLevel : view.generation.motiveLevel.inst
      (view.projectionLevels fieldSort levels) = fieldSort)
    (selectedMinorType : env.HasType U Γ
      (view.projectionMinorWith view.blockConstructor fieldSort levels params
        (view.specializedFields levels params)
        (view.projectionMotivesWith levels params typeFn dummyType)
        fieldIndex dummyValue)
      (view.generatedProjectionMinorType view.blockConstructor fieldSort
        levels params
        (view.projectionMotivesWith levels params typeFn dummyType))) :
    let fields := view.specializedFields levels params
    let m := fields.length
    let motives := view.projectionMotivesWith levels params typeFn dummyType
    let minors := view.generation.flatCtors.map fun constructor =>
      view.projectionMinorWith constructor fieldSort levels params fields
        motives fieldIndex dummyValue
    ∃ ruleIndex B,
      view.generation.ruleEntry ruleIndex view.blockConstructor ∧
      env.SpineWF U (fields.reverse ++ Γ)
        ((view.generation.rule ruleIndex view.blockConstructor).type.instL
          (view.projectionLevels fieldSort levels))
        (params.map (VExpr.liftN m) ++ motives.map (VExpr.liftN m) ++
          minors.map (VExpr.liftN m) ++ VExpr.bvarRevRange 0 m) B := by
  let gen := view.generation
  let pLevels := view.projectionLevels fieldSort levels
  let fields := view.specializedFields levels params
  let m := fields.length
  let motives := view.projectionMotivesWith levels params typeFn dummyType
  let minors := gen.flatCtors.map fun constructor =>
    view.projectionMinorWith constructor fieldSort levels params fields
      motives fieldIndex dummyValue
  let commonArgs := params.map (VExpr.liftN m) ++
    motives.map (VExpr.liftN m) ++ minors.map (VExpr.liftN m)
  have hmotivesLength : motives.length = gen.familyCount := by
    simp [motives, gen]
  have hminorsLength : minors.length = gen.minorCount := by
    simp [minors, gen, BlockGenerationChecked.minorCount]
  have hfieldsOnTel : env.OnTel U Γ fields := by
    simpa [fields] using
      (self.specializedFields_onSortTel henv.ordered levels hlevels
        hlevelsLength params hparamsLength paramsSpine).toOnTel
  have hcommon := self.projectionCommonWithSpine henv hΓ fieldSort
    hfieldSort levels hlevels hlevelsLength params hparamsLength paramsSpine
    typeFn dummyType dummyValue fieldIndex typeFnType dummyTypeType
    dummyValueType hmotiveLevel selectedMinorType
  have hcommonWeak := hcommon.weakN henv.ordered
    (Ctx.LiftN.zero (n := m) (Γ := Γ) fields.reverse
      (h := by simp [m]))
  have hrecTypeClosed :
      ((gen.recType view.family).instL pLevels).ClosedN 0 := by
    simpa [gen, pLevels] using
      (self.generationEnv.recType_closedN view.family_mem).instL
  rw [hrecTypeClosed.liftN_eq (Nat.zero_le _)] at hcommonWeak
  have hcommonArgsMap :
      (params ++ motives ++ minors).map (VExpr.liftN m) = commonArgs := by
    simp [commonArgs, List.map_append]
  rw [hcommonArgsMap] at hcommonWeak
  rw [gen.recType_instL_common] at hcommonWeak
  let oldResult := VExpr.forallN
    ((gen.recIndexBinders view.family).map (VExpr.instL pLevels))
    (.forallE ((gen.recMajorDomain view.family).instL pLevels)
      ((gen.recMotiveResult view.family).instL pLevels))
  have hsource : env.SpineWF U (fields.reverse ++ Γ)
      (VExpr.forallN (gen.ruleCommonBinders.map (VExpr.instL pLevels))
        oldResult) (commonArgs ++ [])
      ((VExpr.forallE (view.structureType levels params)
        (.app typeFn.lift (.bvar 0))).liftN m) := by
    simpa [oldResult, commonArgs, fields, m] using hcommonWeak
  have hfieldBase := hfieldsOnTel.selfSpineWF
    (B := .sort .zero) (Δ := ([] : List VExpr))
  have hfieldBase' : env.SpineWF U (fields.reverse ++ Γ)
      (VExpr.forallN (VExpr.liftTelN m fields 0) (.sort .zero))
      (VExpr.bvarRevRange 0 m) (.sort .zero) := by
    simpa [m, VExpr.liftN_forallN, VExpr.liftN] using hfieldBase
  let ruleContinuation := VExpr.instRev
    (VExpr.forallN
      ((gen.ruleFieldBinders view.blockConstructor).map
        (VExpr.instL pLevels))
      ((gen.ruleResult view.blockConstructor).instL pLevels)) commonArgs
  have hdomains := self.ruleFieldBinders_specialize fieldSort levels
    hlevelsLength params hparamsLength motives minors hmotivesLength
    hminorsLength
  have htel : VExpr.telN m ruleContinuation =
      VExpr.liftTelN m fields 0 := by
    unfold ruleContinuation
    rw [VExpr.instRev_forallN_projection]
    rw [hdomains]
    simpa only [VExpr.liftTelN_length] using
      VExpr.telN_forallN_length
      (VExpr.liftTelN m fields 0)
      ((gen.ruleResult view.blockConstructor).instL pLevels |>.instRevAt
        commonArgs (gen.ruleFieldBinders view.blockConstructor |>.map
          (VExpr.instL pLevels) |>.length))
  let residual := VExpr.dropN m ruleContinuation
  have hcontinuation : ruleContinuation =
      VExpr.forallN (VExpr.liftTelN m fields 0) residual := by
    calc
      ruleContinuation = VExpr.forallN (VExpr.telN m ruleContinuation)
          (VExpr.dropN m ruleContinuation) :=
        (VExpr.forallN_telN_dropN m ruleContinuation).symm
      _ = _ := by rw [htel]
  have hfieldLength : (VExpr.bvarRevRange 0 m).length =
      (VExpr.liftTelN m fields 0).length := by
    rw [VExpr.bvarRevRange_length, VExpr.liftTelN_length]
  have hfieldsSpine := hfieldBase'.retarget hfieldLength residual
  rw [← hcontinuation] at hfieldsSpine
  obtain ⟨ruleIndex, hentry⟩ :=
    List.mem_iff_getElem?.1 view.blockConstructor_mem
  let fArgs := commonArgs
  let aArgs := params.map (VExpr.liftN m) ++ VExpr.bvarRevRange 0 m
  have hresultIndices : view.constructor.view.resultIndices = [] := by
    apply List.length_eq_zero_iff.1
    have hlength : view.constructor.view.resultIndices.length =
        view.family.view.indices.length := by
      simpa [blockConstructor] using
        self.generationEnv.viewResultIndices_length
          view.blockConstructor_mem
    rw [hlength, view.checked_indices_eq]
    rfl
  have hruleIdx : gen.ruleIdx view.blockConstructor = [] := by
    simp [BlockGenerationChecked.ruleIdx, blockConstructor,
      NormalizedCtor.resultIndicesR, hresultIndices]
  have hfArgsLength : fArgs.length =
      gen.ruleMajorArity view.blockConstructor := by
    simp [fArgs, commonArgs, BlockGenerationChecked.ruleMajorArity,
      hmotivesLength, hminorsLength, hparamsLength, hruleIdx,
      BlockGenerationChecked.ruleIdx, blockConstructor,
      NormalizedCtor.resultIndicesR, hresultIndices]
    change view.source.nparams + (gen.familyCount + gen.minorCount) =
      view.source.nparams + gen.familyCount + gen.minorCount
    omega
  have hparamsSource : params.length = view.source.nparams := by
    change params.length = view.source.nparams
    exact hparamsLength
  have hfArgsCommon : fArgs.length =
      view.source.nparams + gen.familyCount + gen.minorCount := by
    simp [fArgs, commonArgs, hparamsLength, hmotivesLength,
      hminorsLength]
    omega
  have htake : fArgs.take
      (view.source.nparams + gen.familyCount + gen.minorCount) =
      commonArgs := by
    change commonArgs.take
      (view.source.nparams + gen.familyCount + gen.minorCount) = commonArgs
    exact List.take_of_length_le (Nat.le_of_eq hfArgsCommon)
  have hdrop : aArgs.drop view.source.nparams =
      VExpr.bvarRevRange 0 m := by
    dsimp only [aArgs]
    rw [← hparamsSource]
    have hmapLength : (params.map (VExpr.liftN m)).length =
        params.length := by simp
    rw [← hmapLength, List.drop_left]
  have hfieldsForRule : env.SpineWF U (fields.reverse ++ Γ)
      (VExpr.instRev
        (VExpr.forallN
          ((gen.ruleFieldBinders view.blockConstructor).map
            (VExpr.instL pLevels))
          ((gen.ruleResult view.blockConstructor).instL pLevels))
        (fArgs.take
          (view.source.nparams + gen.familyCount + gen.minorCount)))
      (aArgs.drop view.source.nparams)
      (residual.instRev (VExpr.bvarRevRange 0 m)) := by
    rw [htake, hdrop]
    exact hfieldsSpine
  have hcapture := gen.ruleCaptureSpine_of_prefix_fields
    (fArgs := fArgs) (aArgs := aArgs) (suffix := []) ruleIndex
    view.blockConstructor pLevels hfArgsLength hsource hfieldsForRule
  refine ⟨ruleIndex,
    residual.instRev (VExpr.bvarRevRange 0 m), hentry, ?_⟩
  unfold BlockGenerationChecked.ruleCaptureValues at hcapture
  rw [htake, hdrop] at hcapture
  change env.SpineWF U (fields.reverse ++ Γ)
    ((gen.rule ruleIndex view.blockConstructor).type.instL pLevels)
    (params.map (VExpr.liftN m) ++ motives.map (VExpr.liftN m) ++
      minors.map (VExpr.liftN m) ++ VExpr.bvarRevRange 0 m)
    (residual.instRev (VExpr.bvarRevRange 0 m))
  have hcanonical :
      params.map (VExpr.liftN m) ++ motives.map (VExpr.liftN m) ++
          minors.map (VExpr.liftN m) ++ VExpr.bvarRevRange 0 m =
        commonArgs ++ VExpr.bvarRevRange 0 m := by
    simp only [commonArgs, List.append_assoc]
  rw [hcanonical]
  exact hcapture

/-- A typed selected-minor prefix supplies the canonical generated-rule
capture for every projector in that prefix. -/
theorem WF.toConstructorRuleCapturesPrefix_of_minorsWFPrefix
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) (henv : env.ConversionRegular)
    {limit : Nat} (minorsWF : view.MinorsWFPrefix env limit) :
    view.ConstructorRuleCapturesPrefix env limit := by
  intro U Γ levels params idx code hlimit hΓ hlevels hlevelsLength
    hparamsLength hparamsSpine hcode
  obtain ⟨resultLevel, hparamsSpine₀⟩ := hparamsSpine
  have hidx : idx < (view.projectionCodes levels params).length :=
    (List.getElem?_eq_some_iff.1 hcode).1
  obtain ⟨fieldSort, hfieldSort, hcodeSort, hminorShape, -⟩ :=
    view.projectionCodes_get?_program_shape levels params hcode
  have hsortTel := self.specializedFields_onSortTel henv.ordered levels
    hlevels hlevelsLength params hparamsLength
      ⟨resultLevel, hparamsSpine₀⟩
  have hfieldSortWF : code.fieldSort.WF U := by
    rw [hcodeSort]
    exact hsortTel.sortWF hΓ hfieldSort
  have hmotiveLevel : view.generation.motiveLevel.inst
      (view.projectionLevels code.fieldSort levels) = code.fieldSort := by
    rw [hcodeSort]
    rw [List.getElem?_map] at hfieldSort
    obtain ⟨rawSort, hrawSort, rfl⟩ := Option.map_eq_some_iff.1 hfieldSort
    exact self.motiveLevel_projectionLevels rawSort
      (List.mem_iff_getElem?.2 ⟨idx, hrawSort⟩) levels
  subst fieldSort
  have minorsBefore : view.MinorsWFPrefix env idx := by
    intro U' Γ' levels' params' priorIdx prior hprior hΓ' hlevels'
      hlevelsLength' hparamsLength' hparamsSpine' hpriorCode
    exact minorsWF (Nat.lt_trans hprior hlimit) hΓ' hlevels'
      hlevelsLength' hparamsLength' hparamsSpine' hpriorCode
  have programsBefore : view.ProgramsWFPrefix env idx :=
    self.toProgramsWFPrefix_of_minorsWFPrefix henv minorsBefore
  have htypeFn := self.projectionTypeFn_hasType_of_programsPrefix henv
    programsBefore hΓ hlevels hlevelsLength hparamsLength
      ⟨resultLevel, hparamsSpine₀⟩ hcode
  have hminor := minorsWF hlimit hΓ hlevels hlevelsLength
    hparamsLength ⟨resultLevel, hparamsSpine₀⟩ hcode
  rw [hminorShape] at hminor
  exact self.projectionRuleCaptureSpine henv hΓ code.fieldSort
    hfieldSortWF levels hlevels hlevelsLength params hparamsLength
    ⟨resultLevel, hparamsSpine₀⟩ code.typeFn idx htypeFn
    hmotiveLevel hminor

/-- Registered mutual iota rules turn canonical block capture spines into
the exact selected-field equations required by dependent minor induction. -/
theorem WF.toConstructorProjectorsExactPrefix_of_ruleCaptures
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) (henv : env.ConversionRegular) {limit : Nat}
    (minorsWF : view.MinorsWFPrefix env limit)
    (captures : view.ConstructorRuleCapturesPrefix env limit) :
    view.ConstructorProjectorsExactPrefix env limit := by
  intro U Γ levels params count hcount hΓ hlevels hlevelsLength
    hparamsLength hparamsSpine hcountCodes
  obtain ⟨resultLevel, hparamsSpine₀⟩ := hparamsSpine
  let fields := view.specializedFields levels params
  let m := fields.length
  have hcountFields : count ≤ m := by
    simpa [fields, m] using hcountCodes
  have hsortTel := self.specializedFields_onSortTel henv.ordered
    levels hlevels hlevelsLength params hparamsLength
      ⟨resultLevel, hparamsSpine₀⟩
  have hfieldsOnTel : env.OnTel U Γ fields := by
    simpa [fields] using hsortTel.toOnTel
  have hfieldsCtx : OnCtx (fields.reverse ++ Γ) (env.IsType U) :=
    hfieldsOnTel.toOnCtx hΓ
  have hfamily : env.HasType U Γ (.const view.name levels)
      (view.familyType.instL levels) := by
    exact self.familyConst_hasType henv.ordered levels hlevels hlevelsLength
  have hstruct : env.HasType U Γ
      (view.structureType levels params) (.sort resultLevel) := by
    simpa [structureType] using hparamsSpine₀.hasType_appN hfamily
  have hconstructorPrefix := self.constructorPrefix_hasType henv.ordered
    levels hlevels hlevelsLength params hparamsLength
      ⟨resultLevel, hparamsSpine₀⟩
  have hconstructorPrefixWeak := hconstructorPrefix.weakN henv.ordered
    (Ctx.LiftN.zero (n := m) (Γ := Γ) fields.reverse
      (h := by simp [m]))
  have hconstructorPrefixSelf : env.HasType U
      (([] : List VExpr) ++ fields.reverse ++ Γ)
      ((VExpr.appN (.const view.constructorName levels) params).liftN m)
      ((VExpr.forallN fields
        ((view.structureType levels params).liftN m)).liftN
          (([] : List VExpr).length + fields.length)) := by
    simpa [fields, m] using hconstructorPrefixWeak
  have hmajor₀ := VEnv.HasType.appN_selfSpine
    (env := env) (U := U) (As := fields)
    (B := (view.structureType levels params).liftN m)
    (Δ := []) (Γ := Γ)
    (f := (VExpr.appN (.const view.constructorName levels) params).liftN m)
    hconstructorPrefixSelf
  have hmajor : env.HasType U (fields.reverse ++ Γ)
      (view.projectionConstructorApp levels params fields)
      ((view.structureType levels params).liftN m) := by
    simpa [fields, m, projectionConstructorApp,
      VExpr.liftN, VExpr.liftN_appN, VExpr.appN_append, List.map_map,
      Function.comp_def] using hmajor₀
  let paramsLift := params.map (VExpr.liftN m)
  have hparamsLengthLift : paramsLift.length = view.nparams := by
    simpa [paramsLift] using hparamsLength
  have hfamilyClosed : (view.familyType.instL levels).ClosedN 0 := by
    simpa using (self.familyType_closed henv.ordered).instL
  have hparamsSpineLift : env.SpineWF U (fields.reverse ++ Γ)
      (view.familyType.instL levels) paramsLift (.sort resultLevel) := by
    have h := hparamsSpine₀.weakN henv.ordered
      (Ctx.LiftN.zero (n := m) (Γ := Γ) fields.reverse
        (h := by simp [m]))
    rw [hfamilyClosed.liftN_eq (Nat.zero_le _)] at h
    simpa [paramsLift, m, VExpr.liftN] using h
  have hstructLift : view.structureType levels paramsLift =
      (view.structureType levels params).liftN m := by
    simp [paramsLift]
  have hmajorLift : env.HasType U (fields.reverse ++ Γ)
      (view.projectionConstructorApp levels params fields)
      (view.structureType levels paramsLift) := by
    rwa [hstructLift]
  have hcodesLift := self.projectionCodes_liftN levels params
    hparamsLength m 0
  have hspecializedLift :
      view.specializedFields levels paramsLift =
        VExpr.liftTelN m fields 0 := by
    simpa [paramsLift, fields] using
      self.specializedFields_liftN levels params hparamsLength m 0
  have programs : view.ProgramsWFPrefix env limit :=
    self.toProgramsWFPrefix_of_minorsWFPrefix henv minorsWF
  apply List.Forall₂.of_getElem?_local
  · rw [List.length_map, List.length_take,
      VExpr.bvarRevRange_length, Nat.min_eq_left hcountCodes]
  intro i projected selected hprojected hselected
  have hiCount : i < count := by
    have hi := (List.getElem?_eq_some_iff.1 hprojected).1
    simp only [List.length_map] at hi
    rw [List.length_take, Nat.min_eq_left hcountCodes] at hi
    exact hi
  rw [List.getElem?_map,
    List.getElem?_take_of_lt hiCount] at hprojected
  obtain ⟨prior, hpriorCode, hprojectedEq⟩ :=
    Option.map_eq_some_iff.1 hprojected
  subst projected
  have hselectedCanonical :=
    VExpr.bvarRevRange_getElem?_local (m - count) count i hiCount
  have hselectedEq : selected = .bvar (m - 1 - i) := by
    have heq := Option.some.inj (hselected.symm.trans hselectedCanonical)
    rw [show m - count + (count - 1 - i) = m - 1 - i by omega] at heq
    exact heq
  subst selected
  have hiLimit : i < limit := Nat.lt_of_lt_of_le hiCount hcount
  have hiM : i < m := Nat.lt_of_lt_of_le hiCount hcountFields
  have hcodeLift :
      (view.projectionCodes levels paramsLift)[i]? =
        some (prior.liftN m 0) := by
    rw [← hcodesLift, List.getElem?_map, hpriorCode]
    rfl
  have hprojector := programs hiLimit hfieldsCtx hlevels hlevelsLength
    hparamsLengthLift ⟨resultLevel, hparamsSpineLift⟩ hcodeLift
  obtain ⟨fieldSort, hfieldSort, hcodeSort, hminorShape,
      _hprojectorShape⟩ :=
    view.projectionCodes_get?_program_shape levels params hpriorCode
  have hfieldSortWF : prior.fieldSort.WF U := by
    rw [hcodeSort]
    exact hsortTel.sortWF hΓ hfieldSort
  subst fieldSort
  obtain ⟨fieldSortLift, _hfieldSortLift, hcodeSortLift,
      hminorShapeLift, hprojectorShapeLift⟩ :=
    view.projectionCodes_get?_program_shape levels paramsLift hcodeLift
  have hfieldSortLiftEq : fieldSortLift = prior.fieldSort := by
    simpa [VStructureView.ProjectionCode.liftN] using hcodeSortLift.symm
  subst fieldSortLift
  rw [hfieldSortLiftEq] at hminorShapeLift hprojectorShapeLift
  let codeLift := prior.liftN m 0
  let gen := view.generation
  let c := view.blockConstructor
  let pLevels := view.projectionLevels prior.fieldSort levels
  let motives := view.projectionMotives levels params prior.fieldSort
    prior.typeFn
  let originalMinors := gen.flatCtors.map fun constructor =>
    view.projectionMinor constructor prior.fieldSort levels params fields
      motives i
  let motivesLift := view.projectionMotives levels paramsLift
    prior.fieldSort codeLift.typeFn
  let liftedMinors := gen.flatCtors.map fun constructor =>
    view.projectionMinor constructor prior.fieldSort levels paramsLift
      (view.specializedFields levels paramsLift) motivesLift i
  let commonArgs := paramsLift ++ motivesLift ++ liftedMinors
  let fieldArgs := VExpr.bvarRevRange 0 m
  have hpLevelsWF : ∀ level ∈ pLevels, level.WF U :=
    view.projectionLevels_wf prior.fieldSort levels hfieldSortWF hlevels
  have hpLevelsLength : pLevels.length = gen.recUvars :=
    view.projectionLevels_length prior.fieldSort levels hlevelsLength
  have hmotivesLength : motives.length = gen.familyCount := by
    simp [motives, gen]
  have hmotivesLiftLength : motivesLift.length = gen.familyCount := by
    simp [motivesLift, gen]
  have horiginalMinorsLength : originalMinors.length = gen.minorCount := by
    simp [originalMinors, gen, BlockGenerationChecked.minorCount]
  have hliftedMinorsLength : liftedMinors.length = gen.minorCount := by
    simp [liftedMinors, gen, BlockGenerationChecked.minorCount]
  have hmotivesLift : motives.map (VExpr.liftN m) = motivesLift := by
    simpa [motives, motivesLift, paramsLift, codeLift,
      VStructureView.ProjectionCode.liftN] using
      self.toLayoutWF.toProjectionSyntaxWF.projectionMotives_liftN
        prior.fieldSort levels params
        hparamsLength prior.typeFn m 0
  have hminorsLift : originalMinors.map (VExpr.liftN m) =
      liftedMinors := by
    simp only [originalMinors, liftedMinors, List.map_map]
    apply List.map_congr_left
    intro constructor hconstructor
    have hout := self.toLayoutWF.toProjectionSyntaxWF.projectionMinor_liftN
      hconstructor prior.fieldSort
      levels params fields motives hparamsLength rfl hmotivesLength i hiM m 0
    rw [← hspecializedLift, hmotivesLift] at hout
    simpa [paramsLift] using hout
  have hprojectorShapeLift' : codeLift.projector =
      .lam (view.structureType levels paramsLift)
        (VExpr.appN (.const view.recursorName pLevels)
          (paramsLift.map (VExpr.liftN 1) ++
            motivesLift.map (VExpr.liftN 1) ++
            liftedMinors.map (VExpr.liftN 1) ++ [.bvar 0])) := by
    simpa [codeLift, pLevels, motivesLift, liftedMinors, gen] using
      hprojectorShapeLift
  change env.HasType U (fields.reverse ++ Γ) codeLift.projector
      (.forallE (view.structureType levels paramsLift)
        (.app codeLift.typeFn.lift (.bvar 0))) at hprojector
  rw [hprojectorShapeLift'] at hprojector
  obtain ⟨_, ⟨projectorBodyType, hprojectorBody⟩⟩ :=
    hprojector.lam_inv henv.ordered hfieldsCtx
  have hprojectorBeta := VEnv.IsDefEq.beta hprojectorBody hmajorLift
  have hprojectorToRule : env.IsDefEqU U (fields.reverse ++ Γ)
      (.app codeLift.projector
        (view.projectionConstructorApp levels params fields))
      (VExpr.appN (.const view.recursorName pLevels)
        (commonArgs ++
          [view.projectionConstructorApp levels params fields])) := by
    refine ⟨projectorBodyType.inst
      (view.projectionConstructorApp levels params fields), ?_⟩
    rw [hprojectorShapeLift']
    simpa [commonArgs, VExpr.inst, VExpr.instN_appN,
      VExpr.inst_lift, VExpr.instVar_zero, List.map_append,
      List.map_map, Function.comp_def] using hprojectorBeta
  obtain ⟨ruleIndex, captureType, hentry, hcapturesRaw⟩ :=
    captures hiLimit hΓ hlevels hlevelsLength hparamsLength
      ⟨resultLevel, hparamsSpine₀⟩ hpriorCode
  have hcapturesOriginal : env.SpineWF U (fields.reverse ++ Γ)
      ((gen.rule ruleIndex c).type.instL pLevels)
      (paramsLift ++ motives.map (VExpr.liftN m) ++
        originalMinors.map (VExpr.liftN m) ++ fieldArgs) captureType := by
    simpa [gen, c, pLevels, paramsLift, motives, originalMinors,
      fields, m, fieldArgs, List.append_assoc] using hcapturesRaw
  rw [hmotivesLift, hminorsLift] at hcapturesOriginal
  have hcaptures : env.SpineWF U (fields.reverse ++ Γ)
      ((gen.rule ruleIndex c).type.instL pLevels)
      (commonArgs ++ fieldArgs) captureType := by
    simpa [commonArgs, List.append_assoc] using hcapturesOriginal
  have hcommonLength : commonArgs.length =
      view.source.nparams + gen.familyCount + gen.minorCount := by
    simp only [commonArgs, List.length_append]
    rw [show paramsLift.length = view.source.nparams by
      simpa [paramsLift] using hparamsLength,
      show motivesLift.length = gen.familyCount from hmotivesLiftLength,
      show liftedMinors.length = gen.minorCount from hliftedMinorsLength]
  have hfieldCount : gen.ruleFieldCount c = m := by
    simp [gen, c, m, fields, BlockGenerationChecked.ruleFieldCount,
      specializedFields, VBlockStructureView.fields, blockConstructor,
      NormalizedCtor.fieldsR]
  have hfieldArgsLength : fieldArgs.length = gen.ruleFieldCount c := by
    rw [show fieldArgs.length = m by simp [fieldArgs], hfieldCount]
  have hcapturesLength : (commonArgs ++ fieldArgs).length =
      (gen.ruleBinders c).length := by
    rw [List.length_append, hcommonLength, hfieldArgsLength,
      gen.ruleBinders_length]
  have hruleMem : gen.rule ruleIndex c ∈ gen.generatedRules := by
    apply List.mem_map.2
    refine ⟨(c, ruleIndex), ?_, rfl⟩
    apply List.mem_of_getElem? (i := ruleIndex)
    rw [List.getElem?_zipIdx, hentry, Option.map_some, Nat.zero_add]
  have hregistered : env.defeqs (gen.rule ruleIndex c) :=
    self.rules _ (by simpa [gen, c] using hruleMem)
  have hiotaBodies := gen.ruleBodies_defeq_of_capture henv hfieldsCtx
    hpLevelsWF hpLevelsLength hregistered hcaptures hcapturesLength
  have hresultIndices : view.constructor.view.resultIndices = [] := by
    apply List.length_eq_zero_iff.1
    have hlength : view.constructor.view.resultIndices.length =
        view.family.view.indices.length := by
      simpa [c, blockConstructor] using
        self.generationEnv.viewResultIndices_length view.blockConstructor_mem
    rw [hlength, view.checked_indices_eq]
    rfl
  have hruleIdx : gen.ruleIdx c = [] := by
    simp [gen, c, BlockGenerationChecked.ruleIdx, blockConstructor,
      NormalizedCtor.resultIndicesR, hresultIndices]
  have hsourceLevels := view.sourceLevels_projectionLevels
    prior.fieldSort levels hlevelsLength
  have hcommonParams : commonArgs.take view.source.nparams = paramsLift := by
    rw [show view.source.nparams = paramsLift.length by
      simpa [paramsLift] using hparamsLength.symm]
    simp [commonArgs]
  have hleftShape :
      VExpr.instRev ((gen.ruleLhsBody c).instL pLevels)
          (commonArgs ++ fieldArgs) =
        VExpr.appN (.const view.recursorName pLevels)
          (commonArgs ++
            [view.projectionConstructorApp levels params fields]) := by
    have hout := gen.ruleLhsBody_instL_instRev_common_fields_of_unindexed
      c pLevels hpLevelsLength hruleIdx commonArgs fieldArgs
      hcommonLength hfieldArgsLength
    rw [hout]
    have hruleRecName : gen.ruleRecName c = view.recursorName := by
      simp [gen, c, BlockGenerationChecked.ruleRecName,
        blockConstructor, recursorName]
    have hconstructorName : c.ctor.raw.name = view.constructorName := rfl
    rw [hruleRecName, hconstructorName, hsourceLevels, hcommonParams]
    simp [projectionConstructorApp, paramsLift, fieldArgs, m]
  have hiRule : ruleIndex < gen.minorCount := by
    rw [BlockGenerationChecked.minorCount]
    exact (List.getElem?_eq_some_iff.1 hentry).1
  have hselectedMinor : liftedMinors[ruleIndex]? = some codeLift.minor := by
    have hbase : originalMinors[ruleIndex]? = some prior.minor := by
      simp [originalMinors, hentry, hminorShape, motives, fields, gen, c]
    rw [← hminorsLift, List.getElem?_map, hbase]
    rfl
  have hcommonMinor :
      commonArgs[view.source.nparams + gen.familyCount + ruleIndex]? =
        some codeLift.minor := by
    have hcommonShape : commonArgs =
        (paramsLift ++ motivesLift) ++ liftedMinors := by
      simp [commonArgs, List.append_assoc]
    rw [hcommonShape, List.getElem?_append_right (by
      simp only [List.length_append]
      rw [show paramsLift.length = view.source.nparams by
        simpa [paramsLift] using hparamsLength,
        show motivesLift.length = gen.familyCount from hmotivesLiftLength]
      omega)]
    have hoff : view.source.nparams + gen.familyCount + ruleIndex -
        (paramsLift ++ motivesLift).length = ruleIndex := by
      simp only [List.length_append]
      rw [show paramsLift.length = view.source.nparams by
        simpa [paramsLift] using hparamsLength,
        show motivesLift.length = gen.familyCount from hmotivesLiftLength]
      omega
    rw [hoff]
    exact hselectedMinor
  let recursiveArgs := c.ctor.recArgsR view.source.uvars gen.elimination
  let ihs := recursiveArgs.map fun recursive =>
    BlockGenerationChecked.blockRuleCall
      (gen.familyCount + gen.minorCount)
      (gen.ruleFieldCount c)
      (gen.recBase (gen.ruleFieldCount c) recursive.targetType) recursive
  let capturedIHs := ihs.map fun expression =>
    VExpr.instRev (expression.instL pLevels) (commonArgs ++ fieldArgs)
  have hrightShape :
      VExpr.instRev ((gen.ruleRhsBody ruleIndex c).instL pLevels)
          (commonArgs ++ fieldArgs) =
        VExpr.appN codeLift.minor (fieldArgs ++ capturedIHs) := by
    simpa [recursiveArgs, ihs, capturedIHs] using
      gen.ruleRhsBody_instL_instRev_common_fields ruleIndex c pLevels
        commonArgs fieldArgs hcommonLength hfieldArgsLength hcommonMinor hiRule
  rw [hleftShape, hrightShape] at hiotaBodies
  let formalFields := view.specializedFields levels paramsLift
  let formalIHs := view.projectionIHTypes prior.fieldSort levels paramsLift
    motivesLift
  let selectorBinders := formalFields ++ formalIHs
  let selectorBody :=
    VExpr.bvar (formalIHs.length + formalFields.length - 1 - i)
  let allArgs := fieldArgs ++ capturedIHs
  have hminorLamShape : codeLift.minor =
      VExpr.lamN selectorBinders selectorBody := by
    rw [hminorShapeLift]
    simp only [projectionMinor, blockConstructor, ↓reduceIte]
    unfold VExpr.selectFieldMinor
    change VExpr.lamN formalFields (VExpr.lamN formalIHs selectorBody) =
      VExpr.lamN (formalFields ++ formalIHs) selectorBody
    exact (VExpr.lamN_append formalFields formalIHs selectorBody).symm
  have hminorType := minorsWF hiLimit hfieldsCtx hlevels hlevelsLength
    hparamsLengthLift ⟨resultLevel, hparamsSpineLift⟩ hcodeLift
  change env.HasType U (fields.reverse ++ Γ) codeLift.minor
      (view.generatedProjectionMinorType view.blockConstructor
        prior.fieldSort levels paramsLift motivesLift) at hminorType
  rw [view.projectionMinorType_decompose prior.fieldSort levels
    hlevelsLength paramsLift motivesLift hmotivesLiftLength,
    ← VExpr.forallN_append] at hminorType
  change env.HasType U (fields.reverse ++ Γ) codeLift.minor
      (VExpr.forallN selectorBinders _) at hminorType
  rw [hminorLamShape] at hminorType
  obtain ⟨hselectorTel, selectorResultType, hselectorBody⟩ :=
    VEnv.HasType.lamN_wf henv.ordered hfieldsCtx hminorType
  have hiotaBodies' := hiotaBodies
  obtain ⟨_, hiotaTyped⟩ := hiotaBodies'
  have hminorAppType := hiotaTyped.hasType.2
  rw [hminorLamShape] at hminorAppType
  change env.HasType U (fields.reverse ++ Γ)
      (VExpr.appN (VExpr.lamN selectorBinders selectorBody) allArgs) _
      at hminorAppType
  have hcapturedIHsLength : capturedIHs.length = formalIHs.length := by
    calc
      capturedIHs.length = ihs.length := by simp [capturedIHs]
      _ = recursiveArgs.length := by simp [ihs]
      _ = view.constructor.view.recursive.length := by
        simp [recursiveArgs, c, blockConstructor,
          NormalizedCtor.recArgsR]
      _ = formalIHs.length := by
        symm
        simpa [formalIHs] using
          view.projectionIHTypes_length prior.fieldSort levels hlevelsLength
            paramsLift motivesLift hmotivesLiftLength
  have hformalFieldsLength : formalFields.length = m := by
    rw [show formalFields = VExpr.liftTelN m fields 0 by
      simpa [formalFields] using hspecializedLift,
      VExpr.liftTelN_length]
  have hallArgsLength : allArgs.length = selectorBinders.length := by
    simp only [allArgs, selectorBinders, List.length_append]
    rw [show fieldArgs.length = m by simp [fieldArgs],
      hformalFieldsLength, hcapturedIHsLength]
  have hminorSpine := VEnv.HasType.spineWF_of_appN henv hfieldsCtx
    (VEnv.HasType.lamN hselectorTel hselectorBody) hminorAppType
      hallArgsLength
  have hminorBetaRaw := VEnv.IsDefEq.appN_lamN henv.ordered
    hselectorTel hselectorBody hminorSpine hallArgsLength
  have hfieldArg : fieldArgs[i]? = some (.bvar (m - 1 - i)) := by
    simpa [fieldArgs] using
      VExpr.bvarRevRange_getElem?_local 0 m i hiM
  have hfieldAll : allArgs[i]? = some (.bvar (m - 1 - i)) := by
    rw [show allArgs = fieldArgs ++ capturedIHs by rfl,
      List.getElem?_append_left (by simpa [fieldArgs] using hiM), hfieldArg]
  obtain ⟨hidxAll, hfieldGetAll⟩ :=
    List.getElem?_eq_some_iff.1 hfieldAll
  have hselectorBodyLt :
      formalIHs.length + formalFields.length - 1 - i < allArgs.length := by
    rw [hallArgsLength]
    simp only [selectorBinders, List.length_append]
    rw [hformalFieldsLength]
    omega
  have hfieldInst : VExpr.instRev selectorBody allArgs =
      .bvar (m - 1 - i) := by
    unfold selectorBody
    rw [VExpr.instRev_bvar_lt allArgs hselectorBodyLt]
    have hposition : allArgs.length - 1 -
        (formalIHs.length + formalFields.length - 1 - i) = i := by
      rw [hallArgsLength]
      simp only [selectorBinders, List.length_append]
      omega
    simpa only [hposition] using hfieldGetAll
  change VExpr.instRev selectorBody (fieldArgs ++ capturedIHs) =
      .bvar (m - 1 - i) at hfieldInst
  have hminorBeta : env.IsDefEqU U (fields.reverse ++ Γ)
      (VExpr.appN codeLift.minor (fieldArgs ++ capturedIHs))
      (.bvar (m - 1 - i)) := by
    refine ⟨VExpr.instRev selectorResultType allArgs, ?_⟩
    rw [hminorLamShape]
    simpa only [allArgs, hfieldInst] using hminorBetaRaw
  exact .inr (by
    change env.IsDefEqU U (fields.reverse ++ Γ)
      (.app codeLift.projector
        (view.projectionConstructorApp levels params fields))
      (.bvar (m - 1 - i))
    exact henv.isDefEqU_trans hfieldsCtx hprojectorToRule
      (henv.isDefEqU_trans hfieldsCtx hiotaBodies hminorBeta))

/-- Current-field alignment is stable when an ambient binder is inserted
beneath the complete selected-family field telescope. -/
theorem LayoutWF.operationalConstructorFieldAligned_weak
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.Ordered)
    {U : Nat} {Γ : List VExpr} {levels : List VLevel}
    {params : List VExpr} {limit : Nat}
    (hparamsLength : params.length = view.nparams)
    (aligned : view.OperationalConstructorFieldAligned env U Γ
      levels params limit) (A : VExpr) :
    view.OperationalConstructorFieldAligned env U (A :: Γ) levels
      (params.map (VExpr.liftN 1)) limit := by
  intro liftedField hliftedField
  let fields := view.specializedFields levels params
  let m := fields.length
  let paramsLift := params.map (VExpr.liftN 1)
  have hfieldsLift : view.specializedFields levels paramsLift =
      VExpr.liftTelN 1 fields 0 := by
    simpa [paramsLift, fields] using
      self.specializedFields_liftN levels params hparamsLength 1 0
  rw [hfieldsLift, VExpr.liftTelN_getElem?] at hliftedField
  obtain ⟨field, hfield, rfl⟩ := Option.map_eq_some_iff.1 hliftedField
  have hbase := aligned hfield
  have hweak := hbase.weakN henv
    (Ctx.LiftN.consTel fields (Ctx.LiftN.one (A := A)))
  have hcodesLift := self.operationalProjectionCodes_liftN
    levels params hparamsLength 1 0
  have hlimit : limit < fields.length := by
    simpa [fields] using (List.getElem?_eq_some_iff.1 hfield).1
  have hconstructorLift :
      view.projectionConstructorApp levels paramsLift
          (VExpr.liftTelN 1 fields 0) =
        (view.projectionConstructorApp levels params fields).liftN 1 m := by
    simp [VBlockStructureView.projectionConstructorApp, paramsLift, m,
      VExpr.liftN_appN, VExpr.liftN, VExpr.liftTelN_length,
      List.map_append, List.map_map, Function.comp_def,
      VExpr.liftN'_liftN', VExpr.bvarRevRange_liftN_high, Nat.add_comm]
  let args :=
    ((view.operationalProjectionCodes levels params).take limit).map
      fun prior => VExpr.app (prior.projector.liftN m)
        (view.projectionConstructorApp levels params fields)
  change env.IsDefEqU U ((VExpr.liftTelN 1 fields 0).reverse ++ A :: Γ)
    (((field.liftN m limit).instRev args).liftN 1 m)
    ((field.liftN (m - limit)).liftN 1 m) at hweak
  rw [hfieldsLift]
  dsimp only [m] at hweak ⊢
  rw [← hcodesLift]
  simp only [List.map_take, List.map_map,
    VStructureView.ProjectionCode.liftN, Function.comp_def]
  rw [hconstructorLift]
  have hargsLength : args.length = limit := by
    simp [args, List.length_take, Nat.min_eq_left,
      view.operationalProjectionCodes_length, fields, Nat.le_of_lt hlimit]
  rw [← VExpr.instRevAt_zero] at hweak
  have hliftInst := VExpr.liftN_instRevAt
    (field.liftN fields.length limit) args 0 fields.length 1
  simp only [Nat.add_zero] at hliftInst
  rw [hliftInst] at hweak
  rw [hargsLength] at hweak
  have hfieldCompose :
      (field.liftN fields.length limit).liftN 1
          (fields.length + limit) =
        (field.liftN 1 limit).liftN fields.length limit := by
    rw [VExpr.liftN'_liftN'
      (e := field) (n1 := fields.length) (n2 := 1)
      (k1 := limit) (k2 := fields.length + limit)
      (by omega) (by omega)]
    rw [VExpr.liftN'_liftN_hi]
    simp only [Nat.add_comm]
  have hargsLift :
      args.map (fun argument => argument.liftN 1 fields.length) =
        ((view.operationalProjectionCodes levels params).take limit).map
          fun prior =>
            VExpr.app ((prior.liftN 1 0).projector.liftN fields.length)
              ((view.projectionConstructorApp levels params fields).liftN
                1 fields.length) := by
    simp [args, m, VStructureView.ProjectionCode.liftN, VExpr.liftN,
      List.map_take, List.map_map, Function.comp_def,
      VExpr.liftN'_liftN', Nat.add_comm]
  have hrightCompose :
      (field.liftN (fields.length - limit)).liftN 1 fields.length =
        (field.liftN 1 limit).liftN (fields.length - limit) := by
    have h := VExpr.liftN_liftN_comm field
      (fields.length - limit) 1 0 limit (Nat.zero_le _)
    rw [Nat.add_sub_of_le (Nat.le_of_lt hlimit)] at h
    exact h.symm
  rw [hfieldCompose, hargsLift, hrightCompose,
    VExpr.instRevAt_zero] at hweak
  simpa only [VExpr.liftTelN_length, Nat.zero_add, List.map_take,
    VStructureView.ProjectionCode.liftN, m] using hweak

/-- A sparse canonical prefix determines the exact current-field substitution
needed by the selected minor. -/
theorem LayoutWF.operationalConstructorFieldAligned_of_sparse
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.WF)
    {U : Nat} {Γ : List VExpr} {levels : List VLevel}
    {params : List VExpr} {limit : Nat}
    (hΓ : OnCtx Γ (env.IsType U))
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (sparseExact : view.OperationalSparseConstructorPrefix env U Γ
      levels params limit) :
    view.OperationalConstructorFieldAligned env U Γ levels params limit := by
  intro field hfield
  let fields := view.specializedFields levels params
  let m := fields.length
  have hidx : limit < fields.length := by
    simpa [fields] using (List.getElem?_eq_some_iff.1 hfield).1
  have hsortTel := self.specializedFields_onSortTel henv.ordered
    levels hlevels hlevelsLength params hparamsLength hparamsSpine
  have hfieldsOnTel : env.OnTel U Γ fields := by
    simpa [fields] using hsortTel.toOnTel
  have hfieldsCtx : OnCtx (fields.reverse ++ Γ) (env.IsType U) :=
    hfieldsOnTel.toOnCtx hΓ
  have hsplit : env.OnTel U Γ (fields.take limit ++ fields.drop limit) := by
    simpa only [List.take_append_drop] using hfieldsOnTel
  obtain ⟨hprefixOriginal, -⟩ := hsplit.of_append
  have hsortTelFull := hsortTel.weakN henv.ordered
    (Ctx.LiftN.zero (n := m) (Γ := Γ) fields.reverse
      (h := by simp [m]))
  have hfullTel : env.OnTel U (fields.reverse ++ Γ)
      (VExpr.liftTelN m fields 0) := by
    simpa [fields] using hsortTelFull.toOnTel
  let source := VExpr.forallN (VExpr.liftTelN m fields 0) (.sort .zero)
  let leftArgs :=
    ((view.operationalProjectionCodes levels params).take limit).map
      fun prior =>
        VExpr.app (prior.projector.liftN m)
          (view.projectionConstructorApp levels params fields)
  let rightArgs := VExpr.bvarRevRange (m - limit) limit
  change ∃ cursor, ∃ sparse : env.SparseSpineWF U
      (fields.reverse ++ Γ) source leftArgs cursor,
    sparse.PointwiseDefEq rightArgs at sparseExact
  obtain ⟨leftCursor, hleftSparse, hpoint⟩ := sparseExact
  have htakeLength : (fields.take limit).length = limit := by
    rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hidx)]
  have hdropLength : (fields.drop limit).length = m - limit := by
    simp [m]
  have htotalLength :
      (fields.drop limit).length + (fields.take limit).length = m := by
    rw [hdropLength, htakeLength]
    dsimp only [m]
    omega
  let rightCursor :=
    (VExpr.forallN (fields.drop limit) (.sort .zero)).liftN (m - limit)
  have hrightRaw := hprefixOriginal.selfSpineWF
    (B := VExpr.forallN (fields.drop limit) (.sort .zero))
    (Δ := (fields.drop limit).reverse)
  have hright : env.SpineWF U (fields.reverse ++ Γ)
      source rightArgs rightCursor := by
    have hcontext : (fields.drop limit).reverse ++
        (fields.take limit).reverse ++ Γ = fields.reverse ++ Γ := by
      rw [← List.reverse_append, List.take_append_drop]
    rw [hcontext] at hrightRaw
    simp only [List.length_reverse] at hrightRaw
    rw [htotalLength, hdropLength, htakeLength] at hrightRaw
    have hsource :
        (VExpr.forallN (fields.take limit)
          (VExpr.forallN (fields.drop limit) (.sort .zero))).liftN m =
          source := by
      rw [← VExpr.forallN_append, List.take_append_drop,
        VExpr.liftN_forallN]
      rfl
    rw [hsource] at hrightRaw
    simpa [rightArgs, rightCursor] using hrightRaw
  have hsourceType : env.IsType U (fields.reverse ++ Γ) source := by
    apply VEnv.IsType.forallN hfullTel
    exact ⟨_, .sort (by trivial)⟩
  obtain ⟨sourceSort, hsourceHasType⟩ := hsourceType
  have hcursors := hpoint.cursor_defeq henv hfieldsCtx hright
    (show env.IsDefEqU U (fields.reverse ++ Γ) source source from
      ⟨.sort sourceSort, hsourceHasType⟩)
  have hfieldLift :
      (VExpr.liftTelN m fields 0)[limit]? =
        some (field.liftN m limit) := by
    rw [VExpr.liftTelN_getElem?]
    simp [fields, hfield]
  have hleftLength : leftArgs.length = limit := by
    simp [leftArgs, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt (by simpa [fields] using hidx))]
  have hrightLength : rightArgs.length = limit := by
    simp [rightArgs]
  obtain ⟨leftField, leftBody, hleftField, hleftConsume⟩ :=
    VExpr.consumeForalls?_forallN_domain
      (VExpr.liftTelN m fields 0) (.sort .zero) leftArgs
      (by rw [hleftLength, VExpr.liftTelN_length]; exact hidx)
  have hleftFieldEq : leftField = field.liftN m limit :=
    Option.some.inj (hleftField.symm.trans (by
      simpa [hleftLength] using hfieldLift))
  subst leftField
  have hleftCursor : leftCursor =
      .forallE ((field.liftN m limit).instRevAt leftArgs 0) leftBody :=
    Option.some.inj (hleftSparse.consumeForalls_eq.symm.trans hleftConsume)
  obtain ⟨rightField, rightBody, hrightField, hrightConsume⟩ :=
    VExpr.consumeForalls?_forallN_domain
      (VExpr.liftTelN m fields 0) (.sort .zero) rightArgs
      (by rw [hrightLength, VExpr.liftTelN_length]; exact hidx)
  have hrightFieldEq : rightField = field.liftN m limit :=
    Option.some.inj (hrightField.symm.trans (by
      simpa [hrightLength] using hfieldLift))
  subst rightField
  have hrightCursorShape : rightCursor =
      .forallE ((field.liftN m limit).instRevAt rightArgs 0) rightBody :=
    Option.some.inj (hright.toSparse.consumeForalls_eq.symm.trans hrightConsume)
  rw [hleftCursor, hrightCursorShape] at hcursors
  obtain ⟨domainSort, hdomains⟩ :=
    (VEnv.IsDefEqU.forallE_inv henv hfieldsCtx hcursors).1
  have hrightContract :
      (field.liftN m limit).instRev rightArgs =
        field.liftN (m - limit) := by
    simpa [rightArgs] using
      VExpr.instRev_liftN_bvarRevRange field m limit
        (Nat.le_of_lt hidx)
  change env.IsDefEqU U (fields.reverse ++ Γ)
    ((field.liftN m limit).instRev leftArgs)
    (field.liftN (m - limit))
  rw [← hrightContract]
  exact ⟨.sort domainSort, by
    simpa only [VExpr.instRevAt_zero] using hdomains⟩

/-- The selected minor for the next operational projector is well typed from
the current type-function typing and the exact current-field substitution.
How the earlier prefix establishes those two facts is deliberately abstracted
away here. -/
theorem LayoutWF.operationalSelectedMinor_hasType_of_typeFn_aligned_atSort
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.ConversionRegular)
    {limit : Nat}
    {U : Nat} {Γ : List VExpr} {params : List VExpr}
    {levelValues : List VLevel}
    {programSort : VLevel}
    {code : VStructureView.ProjectionCode}
    (hΓ : OnCtx Γ (env.IsType U))
    (hlevels : ∀ level ∈ levelValues, level.WF U)
    (hlevelsLength : levelValues.length = view.uvars)
    (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levelValues)
        params (.sort resultLevel))
    (hcode : (view.operationalProjectionCodes levelValues params)[limit]? =
      some code)
    (hprogramSortWF : programSort.WF U)
    (htypeFn : env.HasType U Γ code.typeFn
      (.forallE (view.structureType levelValues params)
        (.sort programSort)))
    (aligned : view.OperationalConstructorFieldAligned env U Γ
      levelValues params limit)
    (hmotiveLevel : view.generation.motiveLevel.inst
      (view.projectionLevels programSort levelValues) = programSort)
    {dummyType dummyValue : VExpr}
    (dummyTypeType : env.HasType U Γ dummyType (.sort programSort))
    (dummyValueType : env.HasType U Γ dummyValue dummyType) :
    env.HasType U Γ
      (view.projectionMinorWith view.blockConstructor programSort
        levelValues params (view.specializedFields levelValues params)
        (view.projectionMotivesWith levelValues params code.typeFn dummyType)
        limit dummyValue)
      (view.generatedProjectionMinorType view.blockConstructor
        programSort levelValues params
        (view.projectionMotivesWith levelValues params code.typeFn
          dummyType)) := by
  obtain ⟨resultLevel, hparamsSpine₀⟩ := hparamsSpine
  let fields := view.specializedFields levelValues params
  let m := fields.length
  have hidx : limit < fields.length := by
    have := (List.getElem?_eq_some_iff.1 hcode).1
    simpa [fields] using this
  obtain ⟨fieldSort, hfieldSort, hcodeSort, -, -⟩ :=
    view.operationalProjectionCodes_get?_program_shape levelValues params
      hcode
  obtain ⟨field, hfield, -⟩ :=
    view.operationalProjectionCodes_get?_typeFn levelValues params hcode
  have hsortTel := self.specializedFields_onSortTel henv.ordered
    levelValues hlevels hlevelsLength params hparamsLength
    ⟨resultLevel, hparamsSpine₀⟩
  have hfieldsOnTel : env.OnTel U Γ fields := by
    simpa [fields] using hsortTel.toOnTel
  have hfieldsCtx : OnCtx (fields.reverse ++ Γ) (env.IsType U) :=
    hfieldsOnTel.toOnCtx hΓ
  have hfamily : env.HasType U Γ (.const view.name levelValues)
      (view.familyType.instL levelValues) := by
    exact self.familyConst_hasType henv.ordered levelValues hlevels
      hlevelsLength
  have hstruct : env.HasType U Γ
      (view.structureType levelValues params) (.sort resultLevel) := by
    simpa [structureType] using hparamsSpine₀.hasType_appN hfamily
  have hconstructorPrefix := self.constructorPrefix_hasType henv.ordered
    levelValues hlevels hlevelsLength params hparamsLength
    ⟨resultLevel, hparamsSpine₀⟩
  have hconstructorPrefixWeak := hconstructorPrefix.weakN henv.ordered
    (Ctx.LiftN.zero (n := m) (Γ := Γ) fields.reverse
      (h := by simp [m]))
  have hconstructorPrefixSelf : env.HasType U
      (([] : List VExpr) ++ fields.reverse ++ Γ)
      ((VExpr.appN (.const view.constructorName levelValues) params).liftN m)
      ((VExpr.forallN fields
        ((view.structureType levelValues params).liftN m)).liftN
          (([] : List VExpr).length + fields.length)) := by
    simpa [fields, m] using hconstructorPrefixWeak
  have hmajor₀ := VEnv.HasType.appN_selfSpine
    (env := env) (U := U) (As := fields)
    (B := (view.structureType levelValues params).liftN m)
    (Δ := []) (Γ := Γ)
    (f := (VExpr.appN (.const view.constructorName levelValues) params).liftN m)
    hconstructorPrefixSelf
  have hmajor : env.HasType U (fields.reverse ++ Γ)
      (view.projectionConstructorApp levelValues params fields)
      ((view.structureType levelValues params).liftN m) := by
    simpa [fields, m, projectionConstructorApp,
      VExpr.liftN, VExpr.liftN_appN, VExpr.appN_append, List.map_map,
      Function.comp_def] using hmajor₀
  let motives := view.projectionMotivesWith levelValues params code.typeFn
    dummyType
  let ihs := view.projectionIHTypes programSort levelValues params motives
  have hmotivesLength : motives.length = view.generation.familyCount := by
    simp [motives]
  have hihsLength : ihs.length = view.constructor.view.recursive.length := by
    simpa [ihs] using view.projectionIHTypes_length programSort levelValues
      hlevelsLength params motives hmotivesLength
  have hihsOnTel : env.OnTel U (fields.reverse ++ Γ) ihs := by
    simpa [fields, motives, ihs] using
      self.projectionIHTypesWith_onTel henv hΓ levelValues hlevels
        hlevelsLength params hparamsLength
        ⟨resultLevel, hparamsSpine₀⟩ programSort hprogramSortWF
        hmotiveLevel htypeFn dummyTypeType dummyValueType

  have hfieldLiftGet :
      (VExpr.liftTelN m fields 0)[limit]? =
        some (field.liftN m limit) := by
    rw [VExpr.liftTelN_getElem?]
    simp [fields, hfield]
  let paramsLift := params.map (VExpr.liftN m)
  have hparamsLengthLift : paramsLift.length = view.nparams := by
    simpa [paramsLift] using hparamsLength
  have hfamilyClosed : (view.familyType.instL levelValues).ClosedN 0 := by
    simpa using (self.familyType_closed henv.ordered).instL
  have hparamsSpineLift : env.SpineWF U (fields.reverse ++ Γ)
      (view.familyType.instL levelValues) paramsLift
      (.sort resultLevel) := by
    have h := hparamsSpine₀.weakN henv.ordered
      (Ctx.LiftN.zero (n := m) (Γ := Γ) fields.reverse
        (h := by simp [m]))
    rw [hfamilyClosed.liftN_eq (Nat.zero_le _)] at h
    simpa [paramsLift, m, VExpr.liftN] using h
  have hstructLift : view.structureType levelValues paramsLift =
      (view.structureType levelValues params).liftN m := by
    simp [paramsLift]
  have hmajorLift : env.HasType U (fields.reverse ++ Γ)
      (view.projectionConstructorApp levelValues params fields)
      (view.structureType levelValues paramsLift) := by
    rwa [hstructLift]
  have hcodesLift := self.operationalProjectionCodes_liftN
    levelValues params hparamsLength m 0
  have hspecializedLift :
      view.specializedFields levelValues paramsLift =
        VExpr.liftTelN m fields 0 := by
    simpa [paramsLift, fields] using
      self.specializedFields_liftN levelValues params
        hparamsLength m 0
  have hleftArgs :
      view.operationalProjectionArgs levelValues paramsLift limit
          (view.projectionConstructorApp levelValues params fields) =
        ((view.operationalProjectionCodes levelValues params).take limit).map
          fun prior =>
            .app (prior.projector.liftN m)
              (view.projectionConstructorApp levelValues params fields) := by
    unfold operationalProjectionArgs
    rw [← hcodesLift]
    simp [List.map_take, List.map_map,
      VStructureView.ProjectionCode.liftN, Function.comp_def]
  have hinstEq : env.IsDefEqU U (fields.reverse ++ Γ)
      ((field.liftN m limit).instRev
        (((view.operationalProjectionCodes levelValues params).take limit).map
          fun prior => VExpr.app (prior.projector.liftN m)
            (view.projectionConstructorApp levelValues params fields)))
      (field.liftN (m - limit)) := by
    simpa only [fields, m] using aligned hfield

  have hcodeLift :
      (view.operationalProjectionCodes levelValues paramsLift)[limit]? =
        some (code.liftN m 0) := by
    rw [← hcodesLift, List.getElem?_map, hcode]
    rfl
  have hfieldLiftCode :
      (view.specializedFields levelValues paramsLift)[limit]? =
        some (field.liftN m limit) := by
    rw [hspecializedLift]
    exact hfieldLiftGet
  obtain ⟨fieldLift, typeBody, hfieldLiftCode', htypeFnLiftShape,
      htypeBodyContract⟩ :=
    view.operationalProjectionCodes_get?_typeFn_beta levelValues paramsLift
      hcodeLift (view.projectionConstructorApp levelValues params fields)
  have hfieldLiftEq : fieldLift = field.liftN m limit :=
    Option.some.inj (hfieldLiftCode'.symm.trans hfieldLiftCode)
  subst fieldLift
  have htypeFnFull := htypeFn.weakN henv.ordered
    (Ctx.LiftN.zero (n := m) (Γ := Γ) fields.reverse
      (h := by simp [m]))
  have htypeFnLift : env.HasType U (fields.reverse ++ Γ)
      (code.liftN m 0).typeFn
      (.forallE (view.structureType levelValues paramsLift)
        (.sort programSort)) := by
    simpa [VStructureView.ProjectionCode.liftN, hstructLift,
      VExpr.liftN] using htypeFnFull
  rw [htypeFnLiftShape] at htypeFnLift
  obtain ⟨_, ⟨typeBodyType, htypeBody⟩⟩ :=
    htypeFnLift.lam_inv henv.ordered hfieldsCtx
  have hbetaRaw := VEnv.IsDefEq.beta htypeBody hmajorLift
  have hleftArgsRaw :
      ((view.operationalProjectionCodes levelValues paramsLift).take
          limit).map
          (fun prior => VExpr.app prior.projector
            (view.projectionConstructorApp levelValues params fields)) =
        ((view.operationalProjectionCodes levelValues params).take limit).map
          fun prior => VExpr.app (prior.projector.liftN m)
            (view.projectionConstructorApp levelValues params fields) := by
    simpa [operationalProjectionArgs] using hleftArgs
  rw [htypeBodyContract, VExpr.instRevAt_zero, hleftArgs,
    ← htypeFnLiftShape] at hbetaRaw
  have hbeta : env.IsDefEqU U (fields.reverse ++ Γ)
      (.app (code.typeFn.liftN m)
        (view.projectionConstructorApp levelValues params fields))
      ((field.liftN m limit).instRev
        (((view.operationalProjectionCodes levelValues params).take
          limit).map fun prior => .app (prior.projector.liftN m)
            (view.projectionConstructorApp levelValues params fields))) := by
    exact ⟨_, by simpa [VStructureView.ProjectionCode.liftN] using hbetaRaw⟩
  have hmotiveEq : env.IsDefEqU U (fields.reverse ++ Γ)
      (.app (code.typeFn.liftN m)
        (view.projectionConstructorApp levelValues params fields))
      (field.liftN (m - limit)) := by
    exact henv.isDefEqU_trans hfieldsCtx hbeta hinstEq

  let q := m - 1 - limit
  have hqLt : q < fields.length := by
    dsimp only [q, m]
    omega
  have hfieldOriginal : fields[limit]? = some field := by
    simpa [fields] using hfield
  have hfieldReverse : fields.reverse[q]? = some field := by
    rw [List.getElem?_reverse hqLt,
      show fields.length - 1 - q = limit by
        dsimp only [q, m]
        omega,
      hfieldOriginal]
  have hfieldCtx : (fields.reverse ++ Γ)[q]? = some field := by
    rw [List.getElem?_append_left (by simpa using hqLt), hfieldReverse]
  have hbody : env.HasType U (fields.reverse ++ Γ) (.bvar q)
      (field.liftN (m - limit)) := by
    have hlookup := VEnv.HasType.bvar (env := env) (U := U)
      (Lookup.of_getElem? hfieldCtx)
    have hqSucc : q + 1 = m - limit := by
      dsimp only [q, m]
      omega
    rwa [hqSucc] at hlookup
  have hbodyExpected : env.HasType U (fields.reverse ++ Γ) (.bvar q)
      (.app (code.typeFn.liftN m)
        (view.projectionConstructorApp levelValues params fields)) :=
    henv.hasType_defeqU_r hfieldsCtx hmotiveEq.symm hbody
  have hminor := VEnv.HasType.selectFieldMinor_of_weak henv.ordered
    (i := limit) hfieldsOnTel hihsOnTel hidx
      (by simpa [q, m] using hbodyExpected)
  rw [view.projectionMinorType_decompose programSort levelValues
    hlevelsLength params motives hmotivesLength]
  rw [← hihsLength]
  rw [self.projectionMinorWithResult_eq_lift programSort levelValues
    hlevelsLength params hparamsLength code.typeFn dummyType]
  simpa [projectionMinorWith, blockConstructor, fields, motives, ihs, m, q]
    using hminor

/-- The ordinary operational selected minor uses the field universe recorded
in the generated projection code. -/
theorem LayoutWF.operationalSelectedMinor_hasType_of_typeFn_aligned
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.ConversionRegular)
    {limit : Nat}
    {U : Nat} {Γ : List VExpr} {params : List VExpr}
    {levelValues : List VLevel}
    {code : VStructureView.ProjectionCode}
    (hΓ : OnCtx Γ (env.IsType U))
    (hlevels : ∀ level ∈ levelValues, level.WF U)
    (hlevelsLength : levelValues.length = view.uvars)
    (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levelValues)
        params (.sort resultLevel))
    (hcode : (view.operationalProjectionCodes levelValues params)[limit]? =
      some code)
    (htypeFn : env.HasType U Γ code.typeFn
      (.forallE (view.structureType levelValues params)
        (.sort code.fieldSort)))
    (aligned : view.OperationalConstructorFieldAligned env U Γ
      levelValues params limit)
    (hmotiveLevel : view.generation.motiveLevel.inst
      (view.projectionLevels code.fieldSort levelValues) = code.fieldSort)
    {dummyType dummyValue : VExpr}
    (dummyTypeType : env.HasType U Γ dummyType (.sort code.fieldSort))
    (dummyValueType : env.HasType U Γ dummyValue dummyType) :
    env.HasType U Γ
      (view.projectionMinorWith view.blockConstructor code.fieldSort
        levelValues params (view.specializedFields levelValues params)
        (view.projectionMotivesWith levelValues params code.typeFn dummyType)
        limit dummyValue)
      (view.generatedProjectionMinorType view.blockConstructor
        code.fieldSort levelValues params
        (view.projectionMotivesWith levelValues params code.typeFn
          dummyType)) := by
  obtain ⟨resultLevel, hparamsSpine₀⟩ := hparamsSpine
  obtain ⟨fieldSort, hfieldSort, hcodeSort, -, -⟩ :=
    view.operationalProjectionCodes_get?_program_shape levelValues params
      hcode
  have hsortTel := self.specializedFields_onSortTel henv.ordered
    levelValues hlevels hlevelsLength params hparamsLength
    ⟨resultLevel, hparamsSpine₀⟩
  have hfieldSortWF : code.fieldSort.WF U := by
    rw [hcodeSort]
    exact hsortTel.sortWF hΓ hfieldSort
  exact self.operationalSelectedMinor_hasType_of_typeFn_aligned_atSort henv
    hΓ hlevels hlevelsLength hparamsLength
    ⟨resultLevel, hparamsSpine₀⟩ hcode hfieldSortWF htypeFn aligned
      hmotiveLevel dummyTypeType dummyValueType

/-- A fully typed and exact operational prefix supplies the current-field
alignment used by the factored selected-minor theorem. -/
theorem LayoutWF.operationalConstructorFieldAligned_of_exactPrefix
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.ConversionRegular)
    {limit : Nat}
    (programs : view.OperationalProgramsWFPrefix env limit)
    (exact : view.OperationalConstructorProjectorsExactPrefix env limit)
    {U : Nat} {Γ : List VExpr} {levels : List VLevel}
    {params : List VExpr} {code : VStructureView.ProjectionCode}
    (hΓ : OnCtx Γ (env.IsType U))
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (hcode : (view.operationalProjectionCodes levels params)[limit]? =
      some code) :
    view.OperationalConstructorFieldAligned env U Γ levels params limit := by
  intro field hfield
  obtain ⟨resultLevel, hparamsSpine₀⟩ := hparamsSpine
  let fields := view.specializedFields levels params
  let m := fields.length
  have hidx : limit < fields.length := by
    simpa [fields] using (List.getElem?_eq_some_iff.1 hfield).1
  obtain ⟨fieldSort, hfieldSort, hcodeSort, -, -⟩ :=
    view.operationalProjectionCodes_get?_program_shape levels params hcode
  have hsortTel := self.specializedFields_onSortTel henv.ordered
    levels hlevels hlevelsLength params hparamsLength
    ⟨resultLevel, hparamsSpine₀⟩
  have hfieldsOnTel : env.OnTel U Γ fields := by
    simpa [fields] using hsortTel.toOnTel
  have hfieldsCtx : OnCtx (fields.reverse ++ Γ) (env.IsType U) :=
    hfieldsOnTel.toOnCtx hΓ
  have hsortAt :
      (view.fieldSorts.map (VLevel.inst levels))[limit]? =
        some code.fieldSort := by
    simpa [hcodeSort] using hfieldSort
  obtain ⟨hprefixOriginal, -⟩ :=
    hsortTel.prefix_getElem? hfield hsortAt
  have hsortTelFull := hsortTel.weakN henv.ordered
    (Ctx.LiftN.zero (n := m) (Γ := Γ) fields.reverse
      (h := by simp [m]))
  have hfieldLiftGet :
      (VExpr.liftTelN m fields 0)[limit]? =
        some (field.liftN m limit) := by
    rw [VExpr.liftTelN_getElem?]
    simp [fields, hfield]
  have hsortTelFull' : env.OnSortTel U (fields.reverse ++ Γ)
      (VExpr.liftTelN m fields 0)
      (view.fieldSorts.map (VLevel.inst levels)) := by
    simpa [fields] using hsortTelFull
  obtain ⟨hprefixLift, hfieldLiftType⟩ :=
    hsortTelFull'.prefix_getElem? hfieldLiftGet hsortAt
  have hfamily : env.HasType U Γ (.const view.name levels)
      (view.familyType.instL levels) := by
    exact self.familyConst_hasType henv.ordered levels hlevels hlevelsLength
  have hstruct : env.HasType U Γ
      (view.structureType levels params) (.sort resultLevel) := by
    simpa [structureType] using hparamsSpine₀.hasType_appN hfamily
  have hconstructorPrefix := self.constructorPrefix_hasType henv.ordered
    levels hlevels hlevelsLength params hparamsLength
    ⟨resultLevel, hparamsSpine₀⟩
  have hconstructorPrefixWeak := hconstructorPrefix.weakN henv.ordered
    (Ctx.LiftN.zero (n := m) (Γ := Γ) fields.reverse
      (h := by simp [m]))
  have hconstructorPrefixSelf : env.HasType U
      (([] : List VExpr) ++ fields.reverse ++ Γ)
      ((VExpr.appN (.const view.constructorName levels) params).liftN m)
      ((VExpr.forallN fields
        ((view.structureType levels params).liftN m)).liftN
          (([] : List VExpr).length + fields.length)) := by
    simpa [fields, m] using hconstructorPrefixWeak
  have hmajor₀ := VEnv.HasType.appN_selfSpine
    (env := env) (U := U) (As := fields)
    (B := (view.structureType levels params).liftN m)
    (Δ := []) (Γ := Γ)
    (f := (VExpr.appN (.const view.constructorName levels) params).liftN m)
    hconstructorPrefixSelf
  have hmajor : env.HasType U (fields.reverse ++ Γ)
      (view.projectionConstructorApp levels params fields)
      ((view.structureType levels params).liftN m) := by
    simpa [fields, m, projectionConstructorApp,
      VExpr.liftN, VExpr.liftN_appN, VExpr.appN_append, List.map_map,
      Function.comp_def] using hmajor₀
  let paramsLift := params.map (VExpr.liftN m)
  have hparamsLengthLift : paramsLift.length = view.nparams := by
    simpa [paramsLift] using hparamsLength
  have hfamilyClosed : (view.familyType.instL levels).ClosedN 0 := by
    simpa using (self.familyType_closed henv.ordered).instL
  have hparamsSpineLift : env.SpineWF U (fields.reverse ++ Γ)
      (view.familyType.instL levels) paramsLift (.sort resultLevel) := by
    have h := hparamsSpine₀.weakN henv.ordered
      (Ctx.LiftN.zero (n := m) (Γ := Γ) fields.reverse
        (h := by simp [m]))
    rw [hfamilyClosed.liftN_eq (Nat.zero_le _)] at h
    simpa [paramsLift, m, VExpr.liftN] using h
  have hstructLift : view.structureType levels paramsLift =
      (view.structureType levels params).liftN m := by
    simp [paramsLift]
  have hmajorLift : env.HasType U (fields.reverse ++ Γ)
      (view.projectionConstructorApp levels params fields)
      (view.structureType levels paramsLift) := by
    rwa [hstructLift]
  have hcodesLift := self.operationalProjectionCodes_liftN
    levels params hparamsLength m 0
  have hidxLift : limit <
      (view.operationalProjectionCodes levels paramsLift).length := by
    rw [← hcodesLift]
    simpa using (List.getElem?_eq_some_iff.1 hcode).1
  have hprior : ∀ {j : Nat}
      {prior : VStructureView.ProjectionCode}, j < limit →
      (view.operationalProjectionCodes levels paramsLift)[j]? = some prior →
      env.HasType U (fields.reverse ++ Γ) prior.projector
        (.forallE (view.structureType levels paramsLift)
          (.app prior.typeFn.lift (.bvar 0))) := by
    intro j prior hj hpriorCode
    exact programs hj hfieldsCtx hlevels hlevelsLength hparamsLengthLift
      ⟨resultLevel, hparamsSpineLift⟩ hpriorCode
  have hargsLength :
      (view.operationalProjectionArgs levels paramsLift limit
        (view.projectionConstructorApp levels params fields)).length = limit :=
    view.operationalProjectionArgs_length levels paramsLift limit
      (view.projectionConstructorApp levels params fields)
      (Nat.le_of_lt hidxLift)
  obtain ⟨_, _, hleftFull⟩ :=
    operationalProjectionArgsSpineAux_of_prefix henv hfieldsCtx hmajorLift
      hprior (.sort .zero) (Nat.le_refl limit)
        (Nat.le_of_lt (by simpa using hidxLift))
  have hspecializedLift : view.specializedFields levels paramsLift =
      VExpr.liftTelN m fields 0 := by
    simpa [paramsLift, fields] using
      self.specializedFields_liftN levels params hparamsLength m 0
  rw [hspecializedLift] at hleftFull
  rw [← List.take_append_drop limit (VExpr.liftTelN m fields 0),
    VExpr.forallN_append] at hleftFull
  have hprefixLength :
      (VExpr.liftTelN m fields 0 |>.take limit).length = limit := by
    rw [List.length_take, VExpr.liftTelN_length,
      Nat.min_eq_left (Nat.le_of_lt hidx)]
  have hleftPrefix := hleftFull.retarget
    (by simpa [hprefixLength] using hargsLength) (.sort code.fieldSort)
  have hrightPrefix₀ := hprefixOriginal.selfSpineWF
    (B := .sort code.fieldSort) (Δ := (fields.drop limit).reverse)
  have hrightPrefix : env.SpineWF U (fields.reverse ++ Γ)
      (VExpr.forallN (VExpr.liftTelN m fields 0 |>.take limit)
        (.sort code.fieldSort))
      (VExpr.bvarRevRange (m - limit) limit) (.sort code.fieldSort) := by
    have htakeLength : (fields.take limit).length = limit := by
      rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hidx)]
    have hdropLength : (fields.drop limit).length = m - limit := by
      simp [m]
    have htotalLength :
        (fields.drop limit).length + (fields.take limit).length = m := by
      rw [hdropLength, htakeLength]
      dsimp only [m]
      omega
    have hcontext : (fields.drop limit).reverse ++
        (fields.take limit).reverse ++ Γ = fields.reverse ++ Γ := by
      rw [← List.reverse_append, List.take_append_drop]
    rw [hcontext] at hrightPrefix₀
    simp only [List.length_reverse] at hrightPrefix₀
    rw [htotalLength, hdropLength, htakeLength] at hrightPrefix₀
    have hsource :
        (VExpr.forallN (fields.take limit) (.sort code.fieldSort)).liftN m =
          VExpr.forallN (VExpr.liftTelN m fields 0 |>.take limit)
            (.sort code.fieldSort) := by
      rw [VExpr.liftN_forallN, ← VExpr.liftTelN_take]
      rfl
    rw [hsource] at hrightPrefix₀
    simpa [VExpr.liftN] using hrightPrefix₀
  have hleftArgs :
      view.operationalProjectionArgs levels paramsLift limit
          (view.projectionConstructorApp levels params fields) =
        ((view.operationalProjectionCodes levels params).take limit).map
          fun prior => VExpr.app (prior.projector.liftN m)
            (view.projectionConstructorApp levels params fields) := by
    unfold operationalProjectionArgs
    rw [← hcodesLift]
    simp [List.map_take, List.map_map,
      VStructureView.ProjectionCode.liftN, Function.comp_def]
  have hleftPrefix' : env.SpineWF U (fields.reverse ++ Γ)
      (VExpr.forallN (VExpr.liftTelN m fields 0 |>.take limit)
        (.sort code.fieldSort))
      (((view.operationalProjectionCodes levels params).take limit).map
        fun prior => VExpr.app (prior.projector.liftN m)
          (view.projectionConstructorApp levels params fields))
      (.sort code.fieldSort) := by
    rw [hleftArgs] at hleftPrefix
    have hsortInst : (VExpr.sort code.fieldSort).instRev
        (((view.operationalProjectionCodes levels params).take limit).map
          fun prior => VExpr.app (prior.projector.liftN m)
            (view.projectionConstructorApp levels params fields)) =
          .sort code.fieldSort := VExpr.instRev_closedN _ (by trivial)
    rw [hsortInst] at hleftPrefix
    exact hleftPrefix
  have hpoint := exact (Nat.le_refl limit) hΓ hlevels hlevelsLength
    hparamsLength ⟨resultLevel, hparamsSpine₀⟩
    (Nat.le_of_lt (by simpa [fields] using hidx))
  have hpoint' : List.Forall₂
      (fun projected selected => projected = selected ∨
        env.IsDefEqU U (fields.reverse ++ Γ) projected selected)
      (((view.operationalProjectionCodes levels params).take limit).map
        fun prior => VExpr.app (prior.projector.liftN m)
          (view.projectionConstructorApp levels params fields))
      (VExpr.bvarRevRange (m - limit) limit) := by
    simpa only [fields, m] using hpoint
  have hleftLength :
      (((view.operationalProjectionCodes levels params).take limit).map
        fun prior => VExpr.app (prior.projector.liftN m)
          (view.projectionConstructorApp levels params fields)).length =
        (VExpr.liftTelN m fields 0 |>.take limit).length := by
    simp [hprefixLength, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt (by simpa [fields] using hidx))]
  have hinstEq := hprefixLift.instRev_defeq_of_spines henv hfieldsCtx
    hfieldLiftType hleftPrefix' hrightPrefix hleftLength hpoint'
  have hrightContract :
      (field.liftN m limit).instRev
          (VExpr.bvarRevRange (m - limit) limit) =
        field.liftN (m - limit) :=
    VExpr.instRev_liftN_bvarRevRange field m limit
      (Nat.le_of_lt hidx)
  change env.IsDefEqU U (fields.reverse ++ Γ)
    ((field.liftN m limit).instRev
      (((view.operationalProjectionCodes levels params).take limit).map
        fun prior => VExpr.app (prior.projector.liftN m)
          (view.projectionConstructorApp levels params fields)))
    (field.liftN (m - limit))
  rwa [hrightContract] at hinstEq

/-- The selected minor for the next operational projector is well typed once
the already generated operational prefix is typed and computes exactly on the
canonical selected constructor. -/
theorem LayoutWF.operationalSelectedMinor_hasType_of_exactPrefix
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.ConversionRegular)
    {limit : Nat}
    (programs : view.OperationalProgramsWFPrefix env limit)
    (exact : view.OperationalConstructorProjectorsExactPrefix env limit)
    {U : Nat} {Γ : List VExpr} {params : List VExpr}
    {levelValues : List VLevel}
    {code : VStructureView.ProjectionCode}
    (hΓ : OnCtx Γ (env.IsType U))
    (hlevels : ∀ level ∈ levelValues, level.WF U)
    (hlevelsLength : levelValues.length = view.uvars)
    (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levelValues)
        params (.sort resultLevel))
    (hcode : (view.operationalProjectionCodes levelValues params)[limit]? =
      some code)
    (hmotiveLevel : view.generation.motiveLevel.inst
      (view.projectionLevels code.fieldSort levelValues) = code.fieldSort)
    {dummyType dummyValue : VExpr}
    (dummyTypeType : env.HasType U Γ dummyType (.sort code.fieldSort))
    (dummyValueType : env.HasType U Γ dummyValue dummyType) :
    env.HasType U Γ
      (view.projectionMinorWith view.blockConstructor code.fieldSort
        levelValues params (view.specializedFields levelValues params)
        (view.projectionMotivesWith levelValues params code.typeFn dummyType)
        limit dummyValue)
      (view.generatedProjectionMinorType view.blockConstructor
        code.fieldSort levelValues params
        (view.projectionMotivesWith levelValues params code.typeFn
          dummyType)) := by
  have htypeFn :=
    self.operationalProjectionTypeFn_hasType_of_programsPrefix henv programs
      hΓ hlevels hlevelsLength hparamsLength hparamsSpine hcode
  have aligned : view.OperationalConstructorFieldAligned env U Γ
      levelValues params limit :=
    self.operationalConstructorFieldAligned_of_exactPrefix
    henv programs exact hΓ hlevels hlevelsLength hparamsLength hparamsSpine
      hcode
  exact self.operationalSelectedMinor_hasType_of_typeFn_aligned henv
    hΓ hlevels hlevelsLength hparamsLength hparamsSpine hcode htypeFn
      aligned hmotiveLevel dummyTypeType dummyValueType

/-- One admissible operational projector is generated once its dependent
type function and selected-constructor field substitution are available. -/
theorem LayoutWF.operationalProgram_hasType_of_typeFn_aligned_atSort
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.ConversionRegular)
    {limit : Nat}
    {U : Nat} {Γ : List VExpr} {levels : List VLevel}
    {params : List VExpr} {programSort : VLevel}
    {code : VStructureView.ProjectionCode}
    (hΓ : OnCtx Γ (env.IsType U))
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (hcode : (view.operationalProjectionCodes levels params)[limit]? =
      some code)
    (hprogramSortWF : programSort.WF U)
    (htypeFn : env.HasType U Γ code.typeFn
      (.forallE (view.structureType levels params) (.sort programSort)))
    (aligned : view.OperationalConstructorFieldAligned env U Γ
      levels params limit)
    (hmotiveLevel : view.generation.motiveLevel.inst
      (view.projectionLevels programSort levels) = programSort) :
    env.HasType U Γ
      (view.operationalProjector levels params
        (view.specializedFields levels params)
        (view.structureType levels params) programSort limit code.typeFn)
      (.forallE (view.structureType levels params)
        (.app code.typeFn.lift (.bvar 0))) := by
  obtain ⟨resultLevel, hparamsSpine₀⟩ := hparamsSpine
  have hfamily : env.HasType U Γ (.const view.name levels)
      (view.familyType.instL levels) := by
    exact self.familyConst_hasType henv.ordered levels hlevels hlevelsLength
  have hstruct : env.HasType U Γ
      (view.structureType levels params) (.sort resultLevel) := by
    simpa [structureType] using hparamsSpine₀.hasType_appN hfamily
  have hfamilyClosed : (view.familyType.instL levels).ClosedN 0 := by
    simpa using (self.familyType_closed henv.ordered).instL
  let paramsLift := params.map (VExpr.liftN 1)
  have hparamsLengthLift : paramsLift.length = view.nparams := by
    simpa [paramsLift] using hparamsLength
  have hparamsSpineLift : env.SpineWF U
      (view.structureType levels params :: Γ)
      (view.familyType.instL levels) paramsLift (.sort resultLevel) := by
    have h := hparamsSpine₀.weakN henv.ordered
      (Ctx.LiftN.one (A := view.structureType levels params))
    rw [hfamilyClosed.liftN_eq (Nat.zero_le _)] at h
    simpa [paramsLift, VExpr.liftN] using h
  have hstructLift : view.structureType levels paramsLift =
      (view.structureType levels params).lift := by
    change view.structureType levels
        (params.map fun param => param.liftN 1 0) =
      (view.structureType levels params).liftN 1 0
    exact (view.structureType_liftN levels params 1 0).symm
  have hΓLift : OnCtx (view.structureType levels params :: Γ)
      (env.IsType U) := ⟨hΓ, resultLevel, hstruct⟩
  have hmajorLift : env.HasType U
      (view.structureType levels params :: Γ) (.bvar 0)
      (view.structureType levels paramsLift) := by
    rw [hstructLift]
    exact .bvar .zero
  have hcodesLift := self.operationalProjectionCodes_liftN
    levels params hparamsLength 1 0
  have hcodeLift :
      (view.operationalProjectionCodes levels paramsLift)[limit]? =
        some (code.liftN 1 0) := by
    rw [← hcodesLift, List.getElem?_map, hcode]
    rfl
  have htypeFnLift : env.HasType U
      (view.structureType levels params :: Γ) (code.liftN 1 0).typeFn
      (.forallE (view.structureType levels paramsLift)
        (.sort programSort)) := by
    have h := htypeFn.weakN henv.ordered
      (Ctx.LiftN.one (A := view.structureType levels params))
    simpa [VStructureView.ProjectionCode.liftN, hstructLift,
      VExpr.liftN] using h
  have hcarrierType : env.HasType U
      (view.structureType levels params :: Γ)
      (.app (code.liftN 1 0).typeFn (.bvar 0))
      (.sort programSort) := by
    simpa only [VExpr.inst, VExpr.inst_lift, VExpr.instVar_zero] using
      htypeFnLift.app hmajorLift
  let dummyType := majorDummyType (code.liftN 1 0).typeFn (.bvar 0)
  let dummyValue := majorDummyValue (code.liftN 1 0).typeFn (.bvar 0)
  have hdummyType : env.HasType U
      (view.structureType levels params :: Γ) dummyType
      (.sort programSort) := by
    exact majorDummyType_hasType henv.ordered hprogramSortWF hcarrierType
  have hdummyValue : env.HasType U
      (view.structureType levels params :: Γ) dummyValue dummyType := by
    exact majorDummyValue_hasType henv.ordered hcarrierType
  have alignedLift : view.OperationalConstructorFieldAligned env U
      (view.structureType levels params :: Γ) levels paramsLift limit := by
    exact self.operationalConstructorFieldAligned_weak henv.ordered
      hparamsLength aligned (view.structureType levels params)
  have hselected :=
    self.operationalSelectedMinor_hasType_of_typeFn_aligned_atSort
      henv hΓLift hlevels hlevelsLength hparamsLengthLift
      ⟨resultLevel, hparamsSpineLift⟩ hcodeLift hprogramSortWF htypeFnLift
      alignedLift hmotiveLevel hdummyType hdummyValue
  have hbody := self.recursorProjectionWith_hasType henv hΓLift
    programSort hprogramSortWF levels hlevels hlevelsLength paramsLift
    hparamsLengthLift ⟨resultLevel, hparamsSpineLift⟩
    (code.liftN 1 0).typeFn dummyType dummyValue limit htypeFnLift
    hdummyType hdummyValue hmotiveLevel hselected hmajorLift
  have hfieldsLift : view.specializedFields levels paramsLift =
      VExpr.liftTelN 1 (view.specializedFields levels params) 0 := by
    simpa [paramsLift] using
      self.specializedFields_liftN levels params hparamsLength 1 0
  rw [hfieldsLift] at hbody
  apply hstruct.lam
  simpa [operationalProjector, paramsLift, dummyType, dummyValue,
    VStructureView.ProjectionCode.liftN, VExpr.liftN] using hbody

/-- The ordinary operational program is generated at the field universe
recorded in its projection code. -/
theorem LayoutWF.operationalProgram_hasType_of_typeFn_aligned
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.ConversionRegular)
    {limit : Nat}
    {U : Nat} {Γ : List VExpr} {levels : List VLevel}
    {params : List VExpr} {code : VStructureView.ProjectionCode}
    (hΓ : OnCtx Γ (env.IsType U))
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (hcode : (view.operationalProjectionCodes levels params)[limit]? =
      some code)
    (htypeFn : env.HasType U Γ code.typeFn
      (.forallE (view.structureType levels params) (.sort code.fieldSort)))
    (aligned : view.OperationalConstructorFieldAligned env U Γ
      levels params limit)
    (hmotiveLevel : view.generation.motiveLevel.inst
      (view.projectionLevels code.fieldSort levels) = code.fieldSort) :
    env.HasType U Γ code.projector
      (.forallE (view.structureType levels params)
        (.app code.typeFn.lift (.bvar 0))) := by
  obtain ⟨resultLevel, hparamsSpine₀⟩ := hparamsSpine
  obtain ⟨fieldSort, hfieldSort, hcodeSort, -, hprojectorShape⟩ :=
    view.operationalProjectionCodes_get?_program_shape levels params hcode
  have hsortTel := self.specializedFields_onSortTel henv.ordered levels
    hlevels hlevelsLength params hparamsLength
    ⟨resultLevel, hparamsSpine₀⟩
  have hfieldSortWF : code.fieldSort.WF U := by
    rw [hcodeSort]
    exact hsortTel.sortWF hΓ hfieldSort
  subst fieldSort
  rw [hprojectorShape]
  exact self.operationalProgram_hasType_of_typeFn_aligned_atSort henv
    hΓ hlevels hlevelsLength hparamsLength
    ⟨resultLevel, hparamsSpine₀⟩ hcode hfieldSortWF htypeFn aligned
      hmotiveLevel

/-- One admissible operational projector is generated from the already typed
and exact source-order prefix. -/
theorem LayoutWF.operationalProgram_hasType_of_prefix
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.ConversionRegular)
    {limit : Nat}
    (programs : view.OperationalProgramsWFPrefix env limit)
    (exact : view.OperationalConstructorProjectorsExactPrefix env limit)
    {U : Nat} {Γ : List VExpr} {levels : List VLevel}
    {params : List VExpr} {code : VStructureView.ProjectionCode}
    (hΓ : OnCtx Γ (env.IsType U))
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (hcode : (view.operationalProjectionCodes levels params)[limit]? =
      some code)
    (hmotiveLevel : view.generation.motiveLevel.inst
      (view.projectionLevels code.fieldSort levels) = code.fieldSort) :
    env.HasType U Γ code.projector
      (.forallE (view.structureType levels params)
        (.app code.typeFn.lift (.bvar 0))) := by
  have htypeFn :=
    self.operationalProjectionTypeFn_hasType_of_programsPrefix henv programs
      hΓ hlevels hlevelsLength hparamsLength hparamsSpine hcode
  have aligned : view.OperationalConstructorFieldAligned env U Γ
      levels params limit :=
    self.operationalConstructorFieldAligned_of_exactPrefix
      henv programs exact hΓ hlevels hlevelsLength hparamsLength hparamsSpine
        hcode
  exact self.operationalProgram_hasType_of_typeFn_aligned henv hΓ hlevels
    hlevelsLength hparamsLength hparamsSpine hcode htypeFn aligned
      hmotiveLevel

/-- The runtime's mixed typed/strengthened prefix is sufficient to type the
next operational projector. -/
theorem LayoutWF.operationalProgram_hasType_of_runtimePrefix
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.WF)
    {limit : Nat} {U : Nat} {Γ : List VExpr} {levels : List VLevel}
    {params : List VExpr} {code : VStructureView.ProjectionCode}
    (runtime : view.OperationalRuntimePrefix env U Γ levels params limit)
    (hΓ : OnCtx Γ (env.IsType U))
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (hcode : (view.operationalProjectionCodes levels params)[limit]? =
      some code)
    (hmotiveLevel : view.generation.motiveLevel.inst
      (view.projectionLevels code.fieldSort levels) = code.fieldSort) :
    env.HasType U Γ code.projector
      (.forallE (view.structureType levels params)
        (.app code.typeFn.lift (.bvar 0))) := by
  obtain ⟨typePrefix, constructorPrefix⟩ := runtime
  have htypeFn := self.operationalProjectionTypeFn_hasType_of_sparse
    henv hΓ hlevels hlevelsLength hparamsLength hparamsSpine hcode typePrefix
  have aligned : view.OperationalConstructorFieldAligned env U Γ
      levels params limit :=
    self.operationalConstructorFieldAligned_of_sparse
      henv hΓ hlevels hlevelsLength hparamsLength hparamsSpine
        constructorPrefix
  exact self.operationalProgram_hasType_of_typeFn_aligned henv hΓ hlevels
    hlevelsLength hparamsLength hparamsSpine hcode htypeFn aligned
      hmotiveLevel

/-- A runtime-proven Prop field is admissible for small elimination even
when its normalized universe is only semantically, rather than syntactically,
zero.  Small recursor syntax does not retain that universe argument. -/
theorem LayoutWF.operationalProgram_hasType_of_runtimePrefix_small
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.WF)
    {limit : Nat} {U : Nat} {Γ : List VExpr} {levels : List VLevel}
    {params : List VExpr} {code : VStructureView.ProjectionCode}
    (runtime : view.OperationalRuntimePrefix env U Γ levels params limit)
    (hsmall : view.generation.elimination = .small)
    (hfieldSortZero : code.fieldSort ≈ .zero)
    (hΓ : OnCtx Γ (env.IsType U))
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    (hcode : (view.operationalProjectionCodes levels params)[limit]? =
      some code) :
    env.HasType U Γ code.projector
      (.forallE (view.structureType levels params)
        (.app code.typeFn.lift (.bvar 0))) := by
  obtain ⟨resultLevel, hparamsSpine₀⟩ := hparamsSpine
  obtain ⟨typePrefix, constructorPrefix⟩ := runtime
  have htypeFn := self.operationalProjectionTypeFn_hasType_of_sparse
    henv hΓ hlevels hlevelsLength hparamsLength
      ⟨resultLevel, hparamsSpine₀⟩ hcode typePrefix
  obtain ⟨fieldSort, hfieldSort, hcodeSort, -, hprojectorShape⟩ :=
    view.operationalProjectionCodes_get?_program_shape levels params hcode
  have hsortTel := self.specializedFields_onSortTel henv.ordered levels
    hlevels hlevelsLength params hparamsLength
    ⟨resultLevel, hparamsSpine₀⟩
  have hfieldSortWF : code.fieldSort.WF U := by
    rw [hcodeSort]
    exact hsortTel.sortWF hΓ hfieldSort
  have hfamily : env.HasType U Γ (.const view.name levels)
      (view.familyType.instL levels) := by
    exact self.familyConst_hasType henv.ordered levels hlevels hlevelsLength
  have hstruct : env.HasType U Γ
      (view.structureType levels params) (.sort resultLevel) := by
    simpa [structureType] using hparamsSpine₀.hasType_appN hfamily
  have hsortEq : env.IsDefEq U
      (view.structureType levels params :: Γ)
      (.sort code.fieldSort) (.sort .zero) (.sort (.succ code.fieldSort)) :=
    .sortDF hfieldSortWF (by trivial) hfieldSortZero
  have htypeEq : env.IsDefEqU U Γ
      (.forallE (view.structureType levels params) (.sort code.fieldSort))
      (.forallE (view.structureType levels params) (.sort .zero)) :=
    ⟨_, .forallEDF hstruct hsortEq⟩
  have htypeFnZero : env.HasType U Γ code.typeFn
      (.forallE (view.structureType levels params) (.sort .zero)) :=
    htypeFn.defeqU_r henv hΓ htypeEq
  have aligned : view.OperationalConstructorFieldAligned env U Γ
      levels params limit :=
    self.operationalConstructorFieldAligned_of_sparse
      henv hΓ hlevels hlevelsLength hparamsLength
        ⟨resultLevel, hparamsSpine₀⟩ constructorPrefix
  have hmotiveLevel : view.generation.motiveLevel.inst
      (view.projectionLevels .zero levels) = .zero := by
    rw [view.motiveLevel_projectionLevels, hsmall]
  have hprogram := self.operationalProgram_hasType_of_typeFn_aligned_atSort
    henv hΓ hlevels hlevelsLength hparamsLength
      ⟨resultLevel, hparamsSpine₀⟩ hcode (by trivial) htypeFnZero aligned
        hmotiveLevel
  subst fieldSort
  rw [hprojectorShape]
  rw [view.operationalProjector_eq_of_small hsmall levels params
    (view.specializedFields levels params) (view.structureType levels params)
    code.fieldSort .zero limit code.typeFn]
  exact hprogram

/-- Extend a source-ordered block selecting-minor prefix by one field once
the already-generated projectors compute exactly on the canonical selected
constructor.  Earlier minor typing supplies those projectors; exactness is
used only to reconcile dependent field substitutions. -/
theorem WF.toMinorsWFPrefix_succ_of_constructorProjectorsExactPrefix
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) (henv : env.ConversionRegular) {limit : Nat}
    (minors : view.MinorsWFPrefix env limit)
    (exact : view.ConstructorProjectorsExactPrefix env limit) :
    view.MinorsWFPrefix env (limit + 1) := by
  intro U Γ levels params idx code hlimit hΓ hlevels hlevelsLength
    hparamsLength hparamsSpine hcode
  by_cases hbefore : idx < limit
  · exact minors hbefore hΓ hlevels hlevelsLength hparamsLength
      hparamsSpine hcode
  have hidxEq : idx = limit := by omega
  subst idx
  obtain ⟨resultLevel, hparamsSpine₀⟩ := hparamsSpine
  let fields := view.specializedFields levels params
  let m := fields.length
  have hidx : limit < fields.length := by
    have := (List.getElem?_eq_some_iff.1 hcode).1
    simpa [fields] using this
  obtain ⟨fieldSort, hfieldSort, hcodeSort, hminorShape, -⟩ :=
    view.projectionCodes_get?_program_shape levels params hcode
  obtain ⟨field, hfield, -⟩ :=
    view.projectionCodes_get?_typeFn levels params hcode
  have hsortTel := self.specializedFields_onSortTel henv.ordered
    levels hlevels hlevelsLength params hparamsLength
    ⟨resultLevel, hparamsSpine₀⟩
  have hfieldsOnTel : env.OnTel U Γ fields := by
    simpa [fields] using hsortTel.toOnTel
  have hfieldsCtx : OnCtx (fields.reverse ++ Γ) (env.IsType U) :=
    hfieldsOnTel.toOnCtx hΓ
  have hfamily : env.HasType U Γ (.const view.name levels)
      (view.familyType.instL levels) := by
    exact self.familyConst_hasType henv.ordered levels hlevels hlevelsLength
  have hstruct : env.HasType U Γ
      (view.structureType levels params) (.sort resultLevel) := by
    simpa [structureType] using hparamsSpine₀.hasType_appN hfamily
  have hconstructorPrefix := self.constructorPrefix_hasType henv.ordered
    levels hlevels hlevelsLength params hparamsLength
    ⟨resultLevel, hparamsSpine₀⟩
  have hconstructorPrefixWeak := hconstructorPrefix.weakN henv.ordered
    (Ctx.LiftN.zero (n := m) (Γ := Γ) fields.reverse
      (h := by simp [m]))
  have hconstructorPrefixSelf : env.HasType U
      (([] : List VExpr) ++ fields.reverse ++ Γ)
      ((VExpr.appN (.const view.constructorName levels) params).liftN m)
      ((VExpr.forallN fields
        ((view.structureType levels params).liftN m)).liftN
          (([] : List VExpr).length + fields.length)) := by
    simpa [fields, m] using hconstructorPrefixWeak
  have hmajor₀ := VEnv.HasType.appN_selfSpine
    (env := env) (U := U) (As := fields)
    (B := (view.structureType levels params).liftN m)
    (Δ := []) (Γ := Γ)
    (f := (VExpr.appN (.const view.constructorName levels) params).liftN m)
    hconstructorPrefixSelf
  have hmajor : env.HasType U (fields.reverse ++ Γ)
      (view.projectionConstructorApp levels params fields)
      ((view.structureType levels params).liftN m) := by
    simpa [fields, m, projectionConstructorApp,
      VExpr.liftN, VExpr.liftN_appN, VExpr.appN_append, List.map_map,
      Function.comp_def] using hmajor₀
  have programs : view.ProgramsWFPrefix env limit :=
    self.toProgramsWFPrefix_of_minorsWFPrefix henv minors
  have htypeFn := self.projectionTypeFn_hasType_of_programsPrefix henv
    programs hΓ hlevels hlevelsLength hparamsLength
    ⟨resultLevel, hparamsSpine₀⟩ hcode
  have hfieldSortWF : code.fieldSort.WF U := by
    rw [hcodeSort]
    exact hsortTel.sortWF hΓ hfieldSort
  have hmotiveLevel :
      view.generation.motiveLevel.inst
        (view.projectionLevels code.fieldSort levels) = code.fieldSort := by
    rw [hcodeSort]
    have hfieldSort' := hfieldSort
    rw [List.getElem?_map] at hfieldSort'
    obtain ⟨rawSort, hrawSort, rfl⟩ :=
      Option.map_eq_some_iff.1 hfieldSort'
    have hrawSortMem : rawSort ∈ view.fieldSorts :=
      List.mem_iff_getElem?.2 ⟨limit, hrawSort⟩
    exact self.motiveLevel_projectionLevels rawSort hrawSortMem levels
  rw [← hcodeSort] at hminorShape
  let motives := view.projectionMotives levels params code.fieldSort
    code.typeFn
  let ihs := view.projectionIHTypes code.fieldSort levels params motives
  have hmotivesLength : motives.length = view.generation.familyCount := by
    simp [motives]
  have hihsLength : ihs.length = view.constructor.view.recursive.length := by
    simpa [ihs] using view.projectionIHTypes_length code.fieldSort levels
      hlevelsLength params motives hmotivesLength
  have hihsOnTel : env.OnTel U (fields.reverse ++ Γ) ihs := by
    simpa [fields, motives, ihs] using
      self.projectionIHTypes_onTel henv hΓ levels hlevels
        hlevelsLength params hparamsLength
        ⟨resultLevel, hparamsSpine₀⟩ code.fieldSort hfieldSortWF
        hmotiveLevel htypeFn

  have hsortAt :
      (view.fieldSorts.map (VLevel.inst levels))[limit]? =
        some code.fieldSort := by
    simpa [hcodeSort] using hfieldSort
  obtain ⟨hprefixOriginal, -⟩ :=
    hsortTel.prefix_getElem? hfield hsortAt
  have hsortTelFull := hsortTel.weakN henv.ordered
    (Ctx.LiftN.zero (n := m) (Γ := Γ) fields.reverse
      (h := by simp [m]))
  have hfieldLiftGet :
      (VExpr.liftTelN m fields 0)[limit]? =
        some (field.liftN m limit) := by
    rw [VExpr.liftTelN_getElem?]
    simp [fields, hfield]
  have hsortTelFull' : env.OnSortTel U (fields.reverse ++ Γ)
      (VExpr.liftTelN m fields 0)
      (view.fieldSorts.map (VLevel.inst levels)) := by
    simpa [fields] using hsortTelFull
  obtain ⟨hprefixLift, hfieldLiftType⟩ :=
    hsortTelFull'.prefix_getElem? hfieldLiftGet hsortAt

  let paramsLift := params.map (VExpr.liftN m)
  have hparamsLengthLift : paramsLift.length = view.nparams := by
    simpa [paramsLift] using hparamsLength
  have hfamilyClosed : (view.familyType.instL levels).ClosedN 0 := by
    simpa using (self.familyType_closed henv.ordered).instL
  have hparamsSpineLift : env.SpineWF U (fields.reverse ++ Γ)
      (view.familyType.instL levels) paramsLift (.sort resultLevel) := by
    have h := hparamsSpine₀.weakN henv.ordered
      (Ctx.LiftN.zero (n := m) (Γ := Γ) fields.reverse
        (h := by simp [m]))
    rw [hfamilyClosed.liftN_eq (Nat.zero_le _)] at h
    simpa [paramsLift, m, VExpr.liftN] using h
  have hstructLift : view.structureType levels paramsLift =
      (view.structureType levels params).liftN m := by
    simp [paramsLift]
  have hmajorLift : env.HasType U (fields.reverse ++ Γ)
      (view.projectionConstructorApp levels params fields)
      (view.structureType levels paramsLift) := by
    rwa [hstructLift]
  have hΓLift : OnCtx (fields.reverse ++ Γ) (env.IsType U) :=
    hfieldsCtx
  have hcodesLift := self.projectionCodes_liftN
    levels params hparamsLength m 0
  have hidxLift : limit <
      (view.projectionCodes levels paramsLift).length := by
    rw [← hcodesLift]
    simpa using (List.getElem?_eq_some_iff.1 hcode).1
  have hprior : ∀ {j : Nat}
      {prior : VStructureView.ProjectionCode}, j < limit →
      (view.projectionCodes levels paramsLift)[j]? = some prior →
      env.HasType U (fields.reverse ++ Γ) prior.projector
        (.forallE (view.structureType levels paramsLift)
          (.app prior.typeFn.lift (.bvar 0))) := by
    intro j prior hj hpriorCode
    exact programs hj hΓLift hlevels hlevelsLength hparamsLengthLift
      ⟨resultLevel, hparamsSpineLift⟩ hpriorCode
  have hargsLength :
      (view.projectionArgs levels paramsLift limit
        (view.projectionConstructorApp levels params fields)).length =
          limit :=
    view.projectionArgs_length levels paramsLift limit
      (view.projectionConstructorApp levels params fields)
      (Nat.le_of_lt hidxLift)
  obtain ⟨_, _, hleftFull⟩ :=
    projectionArgsSpineAux_of_prefix henv hΓLift hmajorLift hprior
      (.sort .zero) (Nat.le_refl limit)
        (Nat.le_of_lt (by simpa using hidxLift))
  have hspecializedLift :
      view.specializedFields levels paramsLift =
        VExpr.liftTelN m fields 0 := by
    simpa [paramsLift, fields] using
      self.specializedFields_liftN levels params
        hparamsLength m 0
  rw [hspecializedLift] at hleftFull
  rw [← List.take_append_drop limit (VExpr.liftTelN m fields 0),
    VExpr.forallN_append] at hleftFull
  have hprefixLength :
      (VExpr.liftTelN m fields 0 |>.take limit).length = limit := by
    rw [List.length_take, VExpr.liftTelN_length,
      Nat.min_eq_left (Nat.le_of_lt hidx)]
  have hleftPrefix := hleftFull.retarget
    (by simpa [hprefixLength] using hargsLength) (.sort code.fieldSort)

  have hrightPrefix₀ := hprefixOriginal.selfSpineWF
    (B := .sort code.fieldSort) (Δ := (fields.drop limit).reverse)
  have hrightPrefix : env.SpineWF U (fields.reverse ++ Γ)
      (VExpr.forallN (VExpr.liftTelN m fields 0 |>.take limit)
        (.sort code.fieldSort))
      (VExpr.bvarRevRange (m - limit) limit) (.sort code.fieldSort) := by
    have htakeLength : (fields.take limit).length = limit := by
      rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hidx)]
    have hdropLength : (fields.drop limit).length = m - limit := by
      simp [m]
    have htotalLength :
        (fields.drop limit).length + (fields.take limit).length = m := by
      rw [hdropLength, htakeLength]
      dsimp only [m]
      omega
    have hcontext : (fields.drop limit).reverse ++
        (fields.take limit).reverse ++ Γ = fields.reverse ++ Γ := by
      rw [← List.reverse_append, List.take_append_drop]
    rw [hcontext] at hrightPrefix₀
    simp only [List.length_reverse] at hrightPrefix₀
    rw [htotalLength, hdropLength, htakeLength] at hrightPrefix₀
    have hsource :
        (VExpr.forallN (fields.take limit) (.sort code.fieldSort)).liftN m =
          VExpr.forallN (VExpr.liftTelN m fields 0 |>.take limit)
            (.sort code.fieldSort) := by
      rw [VExpr.liftN_forallN, ← VExpr.liftTelN_take]
      rfl
    rw [hsource] at hrightPrefix₀
    simpa [VExpr.liftN] using hrightPrefix₀

  have hleftArgs :
      view.projectionArgs levels paramsLift limit
          (view.projectionConstructorApp levels params fields) =
        ((view.projectionCodes levels params).take limit).map fun prior =>
          .app (prior.projector.liftN m)
            (view.projectionConstructorApp levels params fields) := by
    unfold projectionArgs
    rw [← hcodesLift]
    simp [List.map_take, List.map_map,
      VStructureView.ProjectionCode.liftN, Function.comp_def]
  have hleftPrefix' : env.SpineWF U (fields.reverse ++ Γ)
      (VExpr.forallN (VExpr.liftTelN m fields 0 |>.take limit)
        (.sort code.fieldSort))
      (((view.projectionCodes levels params).take limit).map fun prior =>
        .app (prior.projector.liftN m)
          (view.projectionConstructorApp levels params fields))
      (.sort code.fieldSort) := by
    rw [hleftArgs] at hleftPrefix
    have hsortInst : (VExpr.sort code.fieldSort).instRev
        (((view.projectionCodes levels params).take limit).map fun prior =>
          .app (prior.projector.liftN m)
            (view.projectionConstructorApp levels params fields)) =
          .sort code.fieldSort :=
      VExpr.instRev_closedN _ (by trivial)
    rw [hsortInst] at hleftPrefix
    exact hleftPrefix
  have hpoint := exact (Nat.le_refl limit) hΓ hlevels hlevelsLength
    hparamsLength ⟨resultLevel, hparamsSpine₀⟩
    (Nat.le_of_lt (by simpa [fields] using hidx))
  have hpoint' : List.Forall₂
      (fun projected selected => projected = selected ∨
        env.IsDefEqU U (fields.reverse ++ Γ) projected selected)
      (((view.projectionCodes levels params).take limit).map fun prior =>
        VExpr.app (prior.projector.liftN m)
          (view.projectionConstructorApp levels params fields))
      (VExpr.bvarRevRange (m - limit) limit) := by
    simpa only [fields, m] using hpoint
  have hleftLength :
      (((view.projectionCodes levels params).take limit).map fun prior =>
        VExpr.app (prior.projector.liftN m)
          (view.projectionConstructorApp levels params fields)).length =
        (VExpr.liftTelN m fields 0 |>.take limit).length := by
    simp [hprefixLength, List.length_take,
      Nat.min_eq_left (Nat.le_of_lt (by simpa [fields] using hidx))]
  have hinstEq := hprefixLift.instRev_defeq_of_spines henv hfieldsCtx
    hfieldLiftType hleftPrefix' hrightPrefix hleftLength hpoint'
  have hrightContract :
      (field.liftN m limit).instRev
          (VExpr.bvarRevRange (m - limit) limit) =
        field.liftN (m - limit) :=
    VExpr.instRev_liftN_bvarRevRange field m limit
      (Nat.le_of_lt hidx)

  have hcodeLift :
      (view.projectionCodes levels paramsLift)[limit]? =
        some (code.liftN m 0) := by
    rw [← hcodesLift, List.getElem?_map, hcode]
    rfl
  have hfieldLiftCode :
      (view.specializedFields levels paramsLift)[limit]? =
        some (field.liftN m limit) := by
    rw [hspecializedLift]
    exact hfieldLiftGet
  obtain ⟨fieldLift, typeBody, hfieldLiftCode', htypeFnLiftShape,
      htypeBodyContract⟩ :=
    view.projectionCodes_get?_typeFn_beta levels paramsLift hcodeLift
      (view.projectionConstructorApp levels params fields)
  have hfieldLiftEq : fieldLift = field.liftN m limit :=
    Option.some.inj (hfieldLiftCode'.symm.trans hfieldLiftCode)
  subst fieldLift
  have htypeFnFull := htypeFn.weakN henv.ordered
    (Ctx.LiftN.zero (n := m) (Γ := Γ) fields.reverse
      (h := by simp [m]))
  have htypeFnLift : env.HasType U (fields.reverse ++ Γ)
      (code.liftN m 0).typeFn
      (.forallE (view.structureType levels paramsLift)
        (.sort code.fieldSort)) := by
    simpa [VStructureView.ProjectionCode.liftN, hstructLift,
      VExpr.liftN] using htypeFnFull
  rw [htypeFnLiftShape] at htypeFnLift
  obtain ⟨_, ⟨typeBodyType, htypeBody⟩⟩ :=
    htypeFnLift.lam_inv henv.ordered hfieldsCtx
  have hbetaRaw := VEnv.IsDefEq.beta htypeBody hmajorLift
  have hleftArgsRaw :
      ((view.projectionCodes levels paramsLift).take limit).map
          (fun prior => VExpr.app prior.projector
            (view.projectionConstructorApp levels params fields)) =
        ((view.projectionCodes levels params).take limit).map fun prior =>
          VExpr.app (prior.projector.liftN m)
            (view.projectionConstructorApp levels params fields) := by
    simpa [projectionArgs] using hleftArgs
  rw [htypeBodyContract, VExpr.instRevAt_zero, hleftArgsRaw,
    ← htypeFnLiftShape] at hbetaRaw
  have hbeta : env.IsDefEqU U (fields.reverse ++ Γ)
      (.app (code.typeFn.liftN m)
        (view.projectionConstructorApp levels params fields))
      ((field.liftN m limit).instRev
        (((view.projectionCodes levels params).take limit).map fun prior =>
          .app (prior.projector.liftN m)
            (view.projectionConstructorApp levels params fields))) := by
    exact ⟨_, by simpa [VStructureView.ProjectionCode.liftN] using hbetaRaw⟩
  have hmotiveEq : env.IsDefEqU U (fields.reverse ++ Γ)
      (.app (code.typeFn.liftN m)
        (view.projectionConstructorApp levels params fields))
      (field.liftN (m - limit)) := by
    have h := henv.isDefEqU_trans hfieldsCtx hbeta hinstEq
    rwa [hrightContract] at h

  let q := m - 1 - limit
  have hqLt : q < fields.length := by
    dsimp only [q, m]
    omega
  have hfieldOriginal : fields[limit]? = some field := by
    simpa [fields] using hfield
  have hfieldReverse : fields.reverse[q]? = some field := by
    rw [List.getElem?_reverse hqLt,
      show fields.length - 1 - q = limit by
        dsimp only [q, m]
        omega,
      hfieldOriginal]
  have hfieldCtx : (fields.reverse ++ Γ)[q]? = some field := by
    rw [List.getElem?_append_left (by simpa using hqLt), hfieldReverse]
  have hbody : env.HasType U (fields.reverse ++ Γ) (.bvar q)
      (field.liftN (m - limit)) := by
    have hlookup := VEnv.HasType.bvar (env := env) (U := U)
      (Lookup.of_getElem? hfieldCtx)
    have hqSucc : q + 1 = m - limit := by
      dsimp only [q, m]
      omega
    rwa [hqSucc] at hlookup
  have hbodyExpected : env.HasType U (fields.reverse ++ Γ) (.bvar q)
      (.app (code.typeFn.liftN m)
        (view.projectionConstructorApp levels params fields)) :=
    henv.hasType_defeqU_r hfieldsCtx hmotiveEq.symm hbody
  have hminor := VEnv.HasType.selectFieldMinor_of_weak henv.ordered
    (i := limit) hfieldsOnTel hihsOnTel hidx
      (by simpa [q, m] using hbodyExpected)
  rw [hminorShape]
  rw [view.projectionMinorType_decompose code.fieldSort levels
    hlevelsLength params motives hmotivesLength]
  rw [← hihsLength]
  rw [self.projectionMinorResult_eq_lift code.fieldSort levels
    hlevelsLength params hparamsLength code.typeFn]
  simpa [projectionMinor, blockConstructor, fields, motives, ihs, m, q]
    using hminor

/-- Advance the block selecting-minor prefix using only its already proven
source-order segment.  Canonical rule captures and exact earlier-projector
iota are derived internally from checked mutual generation. -/
theorem WF.toMinorsWFPrefix_succ
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) (henv : env.ConversionRegular) {limit : Nat}
    (minors : view.MinorsWFPrefix env limit) :
    view.MinorsWFPrefix env (limit + 1) := by
  have captures : view.ConstructorRuleCapturesPrefix env limit :=
    self.toConstructorRuleCapturesPrefix_of_minorsWFPrefix henv
      (limit := limit) minors
  have exact : view.ConstructorProjectorsExactPrefix env limit :=
    self.toConstructorProjectorsExactPrefix_of_ruleCaptures
      henv (limit := limit) minors captures
  apply self.toMinorsWFPrefix_succ_of_constructorProjectorsExactPrefix
    henv (limit := limit)
  · exact minors
  · exact exact

/-- Every selected mutual-block projection minor is well typed.  The proof
iterates in source-field order, so dependent fields consume only projector
programs already established by the prefix invariant. -/
theorem WF.toMinorsWF
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) (henv : env.ConversionRegular) :
    view.MinorsWF env := by
  have prefixes : ∀ limit, view.MinorsWFPrefix env limit := by
    intro limit
    induction limit with
    | zero =>
        intro U Γ levels params idx code hidx
        omega
    | succ limit ih =>
        exact self.toMinorsWFPrefix_succ henv (limit := limit) ih
  intro U Γ levels params idx code hΓ hlevels hlevelsLength
    hparamsLength hparamsSpine hcode
  exact prefixes (idx + 1) (Nat.lt_succ_self idx) hΓ hlevels
    hlevelsLength hparamsLength hparamsSpine hcode

/-- Checked mutual generation determines every block-backed projector
program; selected-minor typing is no longer an external premise. -/
theorem WF.toProgramsWF
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) (henv : env.ConversionRegular) :
    view.ProgramsWF env :=
  self.toProgramsWF_of_minors henv (self.toMinorsWF henv)

/-- A block-backed projector computes on an arbitrary well-typed application
of the selected constructor once the exact mutual-rule capture spine has been
checked.  Constructor-head alignment remains external; this theorem owns the
actual registered iota step. -/
theorem LayoutWF.projector_constructor_exact
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    {levels : List VLevel} (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    {params : List VExpr} (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    {idx : Nat} {code : VStructureView.ProjectionCode}
    (hcode : (view.projectionCodes levels params)[idx]? = some code)
    (hprojector : env.HasType U Γ code.projector
      (.forallE (view.structureType levels params)
        (.app code.typeFn.lift (.bvar 0))))
    {fields : List VExpr} (hfieldsLength :
      fields.length = (view.specializedFields levels params).length)
    {field : VExpr} (hfield : fields[idx]? = some field)
    (hctorType : env.HasType U Γ
      (VExpr.appN (.const view.constructorName levels) (params ++ fields))
      (view.structureType levels params))
    (hfieldsSpine : env.SpineWF U Γ
      (VExpr.forallN (view.specializedFields levels params) (.sort .zero))
      fields (.sort .zero))
    {ruleIndex : Nat} {B : VExpr}
    (hentry : view.generation.ruleEntry ruleIndex view.blockConstructor)
    (hcaps : env.SpineWF U Γ
      ((view.generation.rule ruleIndex view.blockConstructor).type.instL
        (view.projectionLevels code.fieldSort levels))
      (params ++
        view.projectionMotives levels params code.fieldSort code.typeFn ++
        (view.generation.flatCtors.map fun constructor =>
          view.projectionMinor constructor code.fieldSort levels params
            (view.specializedFields levels params)
            (view.projectionMotives levels params code.fieldSort code.typeFn)
            idx) ++ fields) B) :
    env.IsDefEqU U Γ
      (.app code.projector
        (VExpr.appN (.const view.constructorName levels) (params ++ fields)))
      field := by
  obtain ⟨resultLevel, hparamsSpine₀⟩ := hparamsSpine
  obtain ⟨fieldSort, hfieldSort, hcodeSort, hminorShape,
      hprojectorShape⟩ :=
    view.projectionCodes_get?_program_shape levels params hcode
  have hsortTel := self.specializedFields_onSortTel henv.ordered
    levels hlevels hlevelsLength params hparamsLength
      ⟨resultLevel, hparamsSpine₀⟩
  have hfieldSortWF : code.fieldSort.WF U := by
    rw [hcodeSort]
    exact hsortTel.sortWF hΓ hfieldSort
  subst fieldSort
  let gen := view.generation
  let c := view.blockConstructor
  let pLevels := view.projectionLevels code.fieldSort levels
  let motives := view.projectionMotives levels params code.fieldSort code.typeFn
  let minors := gen.flatCtors.map fun constructor =>
    view.projectionMinor constructor code.fieldSort levels params
      (view.specializedFields levels params) motives idx
  let commonArgs := params ++ motives ++ minors
  have hpLevelsWF : ∀ level ∈ pLevels, level.WF U :=
    view.projectionLevels_wf code.fieldSort levels hfieldSortWF hlevels
  have hpLevelsLength : pLevels.length = gen.recUvars :=
    view.projectionLevels_length code.fieldSort levels hlevelsLength
  have hmotivesLength : motives.length = gen.familyCount := by
    simp [motives, gen]
  have hminorsLength : minors.length = gen.minorCount := by
    simp [minors, gen, BlockGenerationChecked.minorCount]
  rw [hprojectorShape] at hprojector
  obtain ⟨_, ⟨projectorBodyType, hprojectorBody⟩⟩ :=
    hprojector.lam_inv henv.ordered hΓ
  have hprojectorBeta := VEnv.IsDefEq.beta hprojectorBody hctorType
  have hprojectorToRule : env.IsDefEqU U Γ
      (.app code.projector
        (VExpr.appN (.const view.constructorName levels) (params ++ fields)))
      (VExpr.appN (.const view.recursorName pLevels)
        (commonArgs ++
          [VExpr.appN (.const view.constructorName levels)
            (params ++ fields)])) := by
    refine ⟨projectorBodyType.inst
      (VExpr.appN (.const view.constructorName levels) (params ++ fields)), ?_⟩
    rw [hprojectorShape]
    simpa [commonArgs, motives, minors, pLevels, gen,
      VExpr.inst, VExpr.instN_appN, VExpr.inst_lift,
      VExpr.instVar_zero, List.map_append, List.map_map,
      Function.comp_def] using hprojectorBeta
  have hcaptures : env.SpineWF U Γ
      ((gen.rule ruleIndex c).type.instL pLevels)
      (commonArgs ++ fields) B := by
    simpa [gen, c, pLevels, commonArgs, motives, minors,
      List.append_assoc] using hcaps
  have hcommonLength : commonArgs.length =
      view.source.nparams + gen.familyCount + gen.minorCount := by
    simp only [commonArgs, List.length_append]
    rw [show params.length = view.source.nparams by
        simpa using hparamsLength,
      hmotivesLength, hminorsLength]
  have hfieldCount : gen.ruleFieldCount c =
      (view.specializedFields levels params).length := by
    simp [gen, c, BlockGenerationChecked.ruleFieldCount,
      specializedFields, VBlockStructureView.fields, blockConstructor,
      NormalizedCtor.fieldsR]
  have hfieldsRuleLength : fields.length = gen.ruleFieldCount c :=
    hfieldsLength.trans hfieldCount.symm
  have hcapturesLength : (commonArgs ++ fields).length =
      (gen.ruleBinders c).length := by
    rw [List.length_append, hcommonLength, hfieldsRuleLength,
      gen.ruleBinders_length]
  have hruleMem : gen.rule ruleIndex c ∈ gen.generatedRules := by
    apply List.mem_map.2
    refine ⟨(c, ruleIndex), ?_, rfl⟩
    apply List.mem_of_getElem? (i := ruleIndex)
    rw [List.getElem?_zipIdx, hentry, Option.map_some, Nat.zero_add]
  have hregistered : env.defeqs (gen.rule ruleIndex c) :=
    self.rules _ (by simpa [gen, c] using hruleMem)
  have hiotaBodies := gen.ruleBodies_defeq_of_capture henv hΓ
    hpLevelsWF hpLevelsLength hregistered hcaptures hcapturesLength
  have hresultIndices : view.constructor.view.resultIndices = [] := by
    apply List.length_eq_zero_iff.1
    have hlength : view.constructor.view.resultIndices.length =
        view.family.view.indices.length := by
      simpa [c, blockConstructor] using
        self.generationEnv.viewResultIndices_length view.blockConstructor_mem
    rw [hlength, view.checked_indices_eq]
    rfl
  have hruleIdx : gen.ruleIdx c = [] := by
    simp [gen, c, BlockGenerationChecked.ruleIdx, blockConstructor,
      NormalizedCtor.resultIndicesR, hresultIndices]
  have hsourceLevels := view.sourceLevels_projectionLevels
    code.fieldSort levels hlevelsLength
  have hcommonParams : commonArgs.take view.source.nparams = params := by
    rw [show view.source.nparams = params.length by
      simpa using hparamsLength.symm]
    simp [commonArgs]
  have hleftShape :
      VExpr.instRev ((gen.ruleLhsBody c).instL pLevels)
          (commonArgs ++ fields) =
        VExpr.appN (.const view.recursorName pLevels)
          (commonArgs ++
            [VExpr.appN (.const view.constructorName levels)
              (params ++ fields)]) := by
    have hout := gen.ruleLhsBody_instL_instRev_common_fields_of_unindexed
      c pLevels hpLevelsLength hruleIdx commonArgs fields
      hcommonLength hfieldsRuleLength
    rw [hout]
    have hruleRecName : gen.ruleRecName c = view.recursorName := by
      simp [gen, c, BlockGenerationChecked.ruleRecName,
        blockConstructor, recursorName]
    have hconstructorName : c.ctor.raw.name = view.constructorName := rfl
    rw [hruleRecName, hconstructorName, hsourceLevels, hcommonParams]
  have hiRule : ruleIndex < gen.minorCount := by
    rw [BlockGenerationChecked.minorCount]
    exact (List.getElem?_eq_some_iff.1 hentry).1
  have hselectedMinor : minors[ruleIndex]? = some code.minor := by
    simp [minors, hentry, hminorShape, motives, gen, c]
  have hcommonMinor :
      commonArgs[view.source.nparams + gen.familyCount + ruleIndex]? =
        some code.minor := by
    have hcommonShape : commonArgs = (params ++ motives) ++ minors := by
      simp [commonArgs, List.append_assoc]
    rw [hcommonShape, List.getElem?_append_right (by
      simp only [List.length_append]
      rw [show params.length = view.source.nparams by
          simpa using hparamsLength,
        hmotivesLength]
      omega)]
    have hoff : view.source.nparams + gen.familyCount + ruleIndex -
        (params ++ motives).length = ruleIndex := by
      simp only [List.length_append]
      rw [show params.length = view.source.nparams by
          simpa using hparamsLength,
        hmotivesLength]
      omega
    rw [hoff]
    exact hselectedMinor
  let recursiveArgs := c.ctor.recArgsR view.source.uvars gen.elimination
  let ihs := recursiveArgs.map fun recursive =>
    BlockGenerationChecked.blockRuleCall
      (gen.familyCount + gen.minorCount)
      (gen.ruleFieldCount c)
      (gen.recBase (gen.ruleFieldCount c) recursive.targetType) recursive
  let capturedIHs := ihs.map fun expression =>
    VExpr.instRev (expression.instL pLevels) (commonArgs ++ fields)
  have hrightShape :
      VExpr.instRev ((gen.ruleRhsBody ruleIndex c).instL pLevels)
          (commonArgs ++ fields) =
        VExpr.appN code.minor (fields ++ capturedIHs) := by
    simpa [recursiveArgs, ihs, capturedIHs] using
      gen.ruleRhsBody_instL_instRev_common_fields ruleIndex c pLevels
        commonArgs fields hcommonLength hfieldsRuleLength hcommonMinor hiRule
  rw [hleftShape, hrightShape] at hiotaBodies
  let formalFields := view.specializedFields levels params
  let formalIHs := view.projectionIHTypes code.fieldSort levels params motives
  let selectorBinders := formalFields ++ formalIHs
  let selectorBody :=
    VExpr.bvar (formalIHs.length + formalFields.length - 1 - idx)
  have hminorLamShape : code.minor =
      VExpr.lamN selectorBinders selectorBody := by
    rw [hminorShape]
    simp only [projectionMinor, blockConstructor, ↓reduceIte]
    unfold VExpr.selectFieldMinor
    change VExpr.lamN formalFields (VExpr.lamN formalIHs selectorBody) =
      VExpr.lamN (formalFields ++ formalIHs) selectorBody
    exact (VExpr.lamN_append formalFields formalIHs selectorBody).symm
  have hminorMem : code.minor ∈ commonArgs ++ fields :=
    List.mem_append_left fields (List.mem_of_getElem? hcommonMinor)
  obtain ⟨_, hminorType⟩ :=
    VEnv.SpineWF.arg_hasType hcaps hminorMem
  rw [hminorLamShape] at hminorType
  obtain ⟨hselectorTel, selectorResultType, hselectorBody⟩ :=
    VEnv.HasType.lamN_wf henv.ordered hΓ hminorType
  have hiotaBodies' := hiotaBodies
  obtain ⟨_, hiotaTyped⟩ := hiotaBodies'
  have hminorAppType := hiotaTyped.hasType.2
  rw [hminorLamShape] at hminorAppType
  let allArgs := fields ++ capturedIHs
  change env.HasType U Γ
      (VExpr.appN (VExpr.lamN selectorBinders selectorBody) allArgs) _
      at hminorAppType
  have hcapturedIHsLength : capturedIHs.length = formalIHs.length := by
    calc
      capturedIHs.length = ihs.length := by simp [capturedIHs]
      _ = recursiveArgs.length := by simp [ihs]
      _ = view.constructor.view.recursive.length := by
        simp [recursiveArgs, c, blockConstructor,
          NormalizedCtor.recArgsR]
      _ = formalIHs.length := by
        symm
        simpa [formalIHs] using
          view.projectionIHTypes_length code.fieldSort levels hlevelsLength
            params motives hmotivesLength
  have hformalFieldsLength : formalFields.length = fields.length := by
    exact hfieldsLength.symm
  have hallArgsLength : allArgs.length = selectorBinders.length := by
    simp only [allArgs, selectorBinders, List.length_append]
    rw [hformalFieldsLength, hcapturedIHsLength]
  have hminorSpine := VEnv.HasType.spineWF_of_appN henv hΓ
    (VEnv.HasType.lamN hselectorTel hselectorBody) hminorAppType
      hallArgsLength
  have hminorBetaRaw := VEnv.IsDefEq.appN_lamN henv.ordered
    hselectorTel hselectorBody hminorSpine hallArgsLength
  have hiFields : idx < fields.length :=
    (List.getElem?_eq_some_iff.1 hfield).1
  have hfieldAll : allArgs[idx]? = some field := by
    rw [show allArgs = fields ++ capturedIHs by rfl,
      List.getElem?_append_left hiFields, hfield]
  obtain ⟨hidxAll, hfieldGetAll⟩ :=
    List.getElem?_eq_some_iff.1 hfieldAll
  have hselectorBodyLt :
      formalIHs.length + formalFields.length - 1 - idx < allArgs.length := by
    rw [hallArgsLength]
    simp only [selectorBinders, List.length_append]
    rw [hformalFieldsLength]
    omega
  have hfieldInst : VExpr.instRev selectorBody allArgs = field := by
    unfold selectorBody
    rw [VExpr.instRev_bvar_lt allArgs hselectorBodyLt]
    have hposition : allArgs.length - 1 -
        (formalIHs.length + formalFields.length - 1 - idx) = idx := by
      rw [hallArgsLength]
      simp only [selectorBinders, List.length_append]
      rw [hformalFieldsLength]
      omega
    simpa only [hposition] using hfieldGetAll
  change VExpr.instRev selectorBody (fields ++ capturedIHs) = field at hfieldInst
  have hminorBeta : env.IsDefEqU U Γ
      (VExpr.appN code.minor (fields ++ capturedIHs)) field := by
    refine ⟨VExpr.instRev selectorResultType allArgs, ?_⟩
    rw [hminorLamShape]
    simpa only [allArgs, hfieldInst] using hminorBetaRaw
  exact henv.isDefEqU_trans hΓ hprojectorToRule
    (henv.isDefEqU_trans hΓ hiotaBodies hminorBeta)

/-- A prelude-free block-backed projector computes on an arbitrary well-typed
application of the selected constructor once the exact operational mutual-rule
capture spine has been checked. -/
theorem LayoutWF.operationalProjector_constructor_exact
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.ConversionRegular)
    {U : Nat} {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    {levels : List VLevel} (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    {params : List VExpr} (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    {idx : Nat} {code : VStructureView.ProjectionCode}
    (hcode : (view.operationalProjectionCodes levels params)[idx]? = some code)
    (hprojector : env.HasType U Γ code.projector
      (.forallE (view.structureType levels params)
        (.app code.typeFn.lift (.bvar 0))))
    {fields : List VExpr} (hfieldsLength :
      fields.length = (view.specializedFields levels params).length)
    {field : VExpr} (hfield : fields[idx]? = some field)
    (hctorType : env.HasType U Γ
      (VExpr.appN (.const view.constructorName levels) (params ++ fields))
      (view.structureType levels params))
    (hfieldsSpine : env.SpineWF U Γ
      (VExpr.forallN (view.specializedFields levels params) (.sort .zero))
      fields (.sort .zero))
    :
    env.IsDefEqU U Γ
      (.app code.projector
        (VExpr.appN (.const view.constructorName levels) (params ++ fields)))
      field := by
  obtain ⟨resultLevel, hparamsSpine₀⟩ := hparamsSpine
  obtain ⟨fieldSort, hfieldSort, hcodeSort, -, hprojectorShape⟩ :=
    view.operationalProjectionCodes_get?_program_shape levels params hcode
  have hsortTel := self.specializedFields_onSortTel henv.ordered
    levels hlevels hlevelsLength params hparamsLength
      ⟨resultLevel, hparamsSpine₀⟩
  have hfieldSortWF : code.fieldSort.WF U := by
    rw [hcodeSort]
    exact hsortTel.sortWF hΓ hfieldSort
  subst fieldSort
  let gen := view.generation
  let c := view.blockConstructor
  let pLevels := view.projectionLevels code.fieldSort levels
  let major := VExpr.appN (.const view.constructorName levels)
    (params ++ fields)
  let dummyType := majorDummyType code.typeFn major
  let dummyValue := majorDummyValue code.typeFn major
  let motives := view.projectionMotivesWith levels params code.typeFn dummyType
  let minors := gen.flatCtors.map fun constructor =>
    view.projectionMinorWith constructor code.fieldSort levels params
      (view.specializedFields levels params) motives idx dummyValue
  let selectedMinor := view.projectionMinorWith c code.fieldSort levels params
    (view.specializedFields levels params) motives idx dummyValue
  let commonArgs := params ++ motives ++ minors
  have hpLevelsWF : ∀ level ∈ pLevels, level.WF U :=
    view.projectionLevels_wf code.fieldSort levels hfieldSortWF hlevels
  have hpLevelsLength : pLevels.length = gen.recUvars :=
    view.projectionLevels_length code.fieldSort levels hlevelsLength
  have hmotivesLength : motives.length = gen.familyCount := by
    simp [motives, gen]
  have hminorsLength : minors.length = gen.minorCount := by
    simp [minors, gen, BlockGenerationChecked.minorCount]
  have hidx : idx < (view.specializedFields levels params).length := by
    have hcodeIdx := (List.getElem?_eq_some_iff.1 hcode).1
    simpa using hcodeIdx
  let paramsMajor := params.map (VExpr.liftN 1)
  let allFieldsMajor :=
    VExpr.liftTelN 1 (view.specializedFields levels params) 0
  let typeFnMajor := code.typeFn.lift
  let majorBinder := VExpr.bvar 0
  let dummyTypeMajor := majorDummyType typeFnMajor majorBinder
  let dummyValueMajor := majorDummyValue typeFnMajor majorBinder
  let motivesMajor := view.projectionMotivesWith levels paramsMajor
    typeFnMajor dummyTypeMajor
  let minorsMajor := gen.flatCtors.map fun constructor =>
    view.projectionMinorWith constructor code.fieldSort levels paramsMajor
      allFieldsMajor motivesMajor idx dummyValueMajor
  have hparamsMajorLength : paramsMajor.length = view.nparams := by
    simpa [paramsMajor] using hparamsLength
  have hparamsBeta :
      paramsMajor.map (fun expression => expression.inst major 0) = params := by
    simp [paramsMajor, List.map_map, Function.comp_def, VExpr.inst_liftN]
  have htypeFnBeta : typeFnMajor.inst major 0 = code.typeFn := by
    exact VExpr.inst_lift code.typeFn major
  have hdummyTypeBeta : dummyTypeMajor.inst major 0 = dummyType := by
    simp [dummyTypeMajor, dummyType, typeFnMajor, majorBinder,
      majorDummyType, VExpr.inst, VExpr.instVar, VExpr.inst_lift,
      ← VExpr.lift_instN_lo]
  have hdummyValueBeta : dummyValueMajor.inst major 0 = dummyValue := by
    simp [dummyValueMajor, dummyValue, typeFnMajor, majorBinder,
      majorDummyValue, VExpr.inst, VExpr.instVar, VExpr.inst_lift,
      ← VExpr.lift_instN_lo]
  have hallFieldsMajor : allFieldsMajor =
      view.specializedFields levels paramsMajor := by
    simpa [allFieldsMajor, paramsMajor] using
      (self.specializedFields_liftN levels params hparamsLength 1 0).symm
  have hallFieldsBeta : VExpr.instTelN major allFieldsMajor 0 =
      view.specializedFields levels params := by
    calc
      VExpr.instTelN major allFieldsMajor 0 =
          view.specializedFields levels
            (paramsMajor.map fun expression => expression.inst major 0) := by
        rw [hallFieldsMajor]
        exact (self.specializedFields_instN levels paramsMajor
          hparamsMajorLength major 0).symm
      _ = view.specializedFields levels params := by rw [hparamsBeta]
  have hidxMajor : idx < allFieldsMajor.length := by
    simpa [allFieldsMajor, VExpr.liftTelN_length] using hidx
  have hmotivesMajorLength :
      motivesMajor.length = gen.familyCount := by
    simp [motivesMajor, gen]
  have hmotivesBeta :
      motivesMajor.map (fun motive => motive.inst major 0) = motives := by
    have hout := self.toProjectionSyntaxWF.projectionMotivesWith_instN
      levels paramsMajor
      hparamsMajorLength typeFnMajor dummyTypeMajor major 0
    rw [hparamsBeta, htypeFnBeta, hdummyTypeBeta] at hout
    exact hout
  have hminorsBeta :
      minorsMajor.map (fun minor => minor.inst major 0) = minors := by
    simp only [minorsMajor, minors, List.map_map]
    apply List.map_congr_left
    intro constructor hconstructor
    have hout := self.toProjectionSyntaxWF.projectionMinorWith_instN
      hconstructor code.fieldSort
      levels paramsMajor allFieldsMajor motivesMajor idx dummyValueMajor
      hparamsMajorLength hallFieldsMajor hmotivesMajorLength hidxMajor major 0
    rw [hparamsBeta, hallFieldsBeta, hmotivesBeta, hdummyValueBeta] at hout
    exact hout
  rw [hprojectorShape] at hprojector
  obtain ⟨_, ⟨projectorBodyType, hprojectorBody⟩⟩ :=
    hprojector.lam_inv henv.ordered hΓ
  have hprojectorBeta := VEnv.IsDefEq.beta hprojectorBody hctorType
  have hprojectorToRule : env.IsDefEqU U Γ
      (.app code.projector
        (VExpr.appN (.const view.constructorName levels) (params ++ fields)))
      (VExpr.appN (.const view.recursorName pLevels)
        (commonArgs ++
          [VExpr.appN (.const view.constructorName levels)
            (params ++ fields)])) := by
    refine ⟨projectorBodyType.inst
      (VExpr.appN (.const view.constructorName levels) (params ++ fields)), ?_⟩
    rw [hprojectorShape]
    simpa [operationalProjector, commonArgs, motives, minors, pLevels, gen,
      major, dummyType, dummyValue, paramsMajor, allFieldsMajor, typeFnMajor,
      majorBinder, dummyTypeMajor, dummyValueMajor, motivesMajor, minorsMajor,
      hparamsBeta, hmotivesBeta, hminorsBeta,
      VExpr.inst, VExpr.instN_appN, VExpr.inst_lift,
      VExpr.instVar_zero, List.map_append, List.map_map,
      Function.comp_def] using hprojectorBeta
  have hcommonLength : commonArgs.length =
      view.source.nparams + gen.familyCount + gen.minorCount := by
    simp only [commonArgs, List.length_append]
    rw [show params.length = view.source.nparams by
        simpa using hparamsLength,
      hmotivesLength, hminorsLength]
  let fullArgs := commonArgs ++ [major]
  let recType := (gen.recType view.family).instL pLevels
  have hidxTel : gen.idxTel view.family = [] := by
    simp [BlockGenerationChecked.idxTel, view.raw_indices_eq]
  have hindices : gen.recIndexBinders view.family = [] := by
    unfold BlockGenerationChecked.recIndexBinders
    rw [hidxTel]
    rfl
  let recCommon := gen.ruleCommonBinders.map (VExpr.instL pLevels)
  let recMajor := (gen.recMajorDomain view.family).instL pLevels
  let recResult := (gen.recMotiveResult view.family).instL pLevels
  let recBinders := recCommon ++ [recMajor]
  have hrecTypeShape : recType =
      VExpr.forallN recBinders recResult := by
    unfold recType recBinders recCommon recMajor recResult
    rw [gen.recType_instL_common, hindices]
    simp only [List.map_nil, VExpr.forallN]
    rw [VExpr.forallN_append]
    rfl
  have hrec : env.HasType U Γ (.const view.recursorName pLevels) recType := by
    simpa [recType, gen, recursorName] using
      self.generationEnv.recursor_hasType_instL view.family_mem self.recursor
        pLevels hpLevelsWF hpLevelsLength (Γ := Γ)
  have hrecTel : env.HasType U Γ (.const view.recursorName pLevels)
      (VExpr.forallN recBinders recResult) := by
    rw [← hrecTypeShape]
    exact hrec
  have hrecBindersLength : fullArgs.length = recBinders.length := by
    simp [fullArgs, recBinders, recCommon, hcommonLength,
      gen.ruleCommonBinders_length]
  have hprojectorToRule' := hprojectorToRule
  obtain ⟨ruleAppType, hprojectorToRuleRaw⟩ := hprojectorToRule'
  have happ : env.HasType U Γ
      (VExpr.appN (.const view.recursorName pLevels) fullArgs)
      ruleAppType := by
    simpa [fullArgs, major] using hprojectorToRuleRaw.hasType.2
  have hfullRaw := VEnv.HasType.spineWF_of_appN henv hΓ hrecTel happ
    hrecBindersLength
  have hfull : env.SpineWF U Γ recType fullArgs
      (recResult.instRev fullArgs) := by
    rw [hrecTypeShape]
    exact hfullRaw
  obtain ⟨ruleIndex, captureType, hentry, hcapturesRaw⟩ :=
    self.projectionRuleCaptureSpineLocal code.fieldSort levels
      hlevelsLength params hparamsLength motives minors hmotivesLength
      hminorsLength hfieldsLength hfull hfieldsSpine
  have hcaptures : env.SpineWF U Γ
      ((gen.rule ruleIndex c).type.instL pLevels)
      (commonArgs ++ fields) captureType := by
    simpa [gen, c, pLevels, commonArgs, fullArgs, recType, motives,
      minors, List.append_assoc] using hcapturesRaw
  have hfieldCount : gen.ruleFieldCount c =
      (view.specializedFields levels params).length := by
    simp [gen, c, BlockGenerationChecked.ruleFieldCount,
      specializedFields, VBlockStructureView.fields, blockConstructor,
      NormalizedCtor.fieldsR]
  have hfieldsRuleLength : fields.length = gen.ruleFieldCount c :=
    hfieldsLength.trans hfieldCount.symm
  have hcapturesLength : (commonArgs ++ fields).length =
      (gen.ruleBinders c).length := by
    rw [List.length_append, hcommonLength, hfieldsRuleLength,
      gen.ruleBinders_length]
  have hruleMem : gen.rule ruleIndex c ∈ gen.generatedRules := by
    apply List.mem_map.2
    refine ⟨(c, ruleIndex), ?_, rfl⟩
    apply List.mem_of_getElem? (i := ruleIndex)
    rw [List.getElem?_zipIdx, hentry, Option.map_some, Nat.zero_add]
  have hregistered : env.defeqs (gen.rule ruleIndex c) :=
    self.rules _ (by simpa [gen, c] using hruleMem)
  have hiotaBodies := gen.ruleBodies_defeq_of_capture henv hΓ
    hpLevelsWF hpLevelsLength hregistered hcaptures hcapturesLength
  have hresultIndices : view.constructor.view.resultIndices = [] := by
    apply List.length_eq_zero_iff.1
    have hlength : view.constructor.view.resultIndices.length =
        view.family.view.indices.length := by
      simpa [c, blockConstructor] using
        self.generationEnv.viewResultIndices_length view.blockConstructor_mem
    rw [hlength, view.checked_indices_eq]
    rfl
  have hruleIdx : gen.ruleIdx c = [] := by
    simp [gen, c, BlockGenerationChecked.ruleIdx, blockConstructor,
      NormalizedCtor.resultIndicesR, hresultIndices]
  have hsourceLevels := view.sourceLevels_projectionLevels
    code.fieldSort levels hlevelsLength
  have hcommonParams : commonArgs.take view.source.nparams = params := by
    rw [show view.source.nparams = params.length by
      simpa using hparamsLength.symm]
    simp [commonArgs]
  have hleftShape :
      VExpr.instRev ((gen.ruleLhsBody c).instL pLevels)
          (commonArgs ++ fields) =
        VExpr.appN (.const view.recursorName pLevels)
          (commonArgs ++
            [VExpr.appN (.const view.constructorName levels)
              (params ++ fields)]) := by
    have hout := gen.ruleLhsBody_instL_instRev_common_fields_of_unindexed
      c pLevels hpLevelsLength hruleIdx commonArgs fields
      hcommonLength hfieldsRuleLength
    rw [hout]
    have hruleRecName : gen.ruleRecName c = view.recursorName := by
      simp [gen, c, BlockGenerationChecked.ruleRecName,
        blockConstructor, recursorName]
    have hconstructorName : c.ctor.raw.name = view.constructorName := rfl
    rw [hruleRecName, hconstructorName, hsourceLevels, hcommonParams]
  have hiRule : ruleIndex < gen.minorCount := by
    rw [BlockGenerationChecked.minorCount]
    exact (List.getElem?_eq_some_iff.1 hentry).1
  have hselectedMinor : minors[ruleIndex]? = some selectedMinor := by
    simp [minors, selectedMinor, hentry, gen, c]
  have hcommonMinor :
      commonArgs[view.source.nparams + gen.familyCount + ruleIndex]? =
        some selectedMinor := by
    have hcommonShape : commonArgs = (params ++ motives) ++ minors := by
      simp [commonArgs, List.append_assoc]
    rw [hcommonShape, List.getElem?_append_right (by
      simp only [List.length_append]
      rw [show params.length = view.source.nparams by
          simpa using hparamsLength,
        hmotivesLength]
      omega)]
    have hoff : view.source.nparams + gen.familyCount + ruleIndex -
        (params ++ motives).length = ruleIndex := by
      simp only [List.length_append]
      rw [show params.length = view.source.nparams by
          simpa using hparamsLength,
        hmotivesLength]
      omega
    rw [hoff]
    exact hselectedMinor
  let recursiveArgs := c.ctor.recArgsR view.source.uvars gen.elimination
  let ihs := recursiveArgs.map fun recursive =>
    BlockGenerationChecked.blockRuleCall
      (gen.familyCount + gen.minorCount)
      (gen.ruleFieldCount c)
      (gen.recBase (gen.ruleFieldCount c) recursive.targetType) recursive
  let capturedIHs := ihs.map fun expression =>
    VExpr.instRev (expression.instL pLevels) (commonArgs ++ fields)
  have hrightShape :
      VExpr.instRev ((gen.ruleRhsBody ruleIndex c).instL pLevels)
          (commonArgs ++ fields) =
        VExpr.appN selectedMinor (fields ++ capturedIHs) := by
    simpa [recursiveArgs, ihs, capturedIHs] using
      gen.ruleRhsBody_instL_instRev_common_fields ruleIndex c pLevels
        commonArgs fields hcommonLength hfieldsRuleLength hcommonMinor hiRule
  rw [hleftShape, hrightShape] at hiotaBodies
  let formalFields := view.specializedFields levels params
  let formalIHs := view.projectionIHTypes code.fieldSort levels params motives
  let selectorBinders := formalFields ++ formalIHs
  let selectorBody :=
    VExpr.bvar (formalIHs.length + formalFields.length - 1 - idx)
  have hminorLamShape : selectedMinor =
      VExpr.lamN selectorBinders selectorBody := by
    simp only [selectedMinor, projectionMinorWith, c, blockConstructor,
      ↓reduceIte]
    unfold VExpr.selectFieldMinor
    change VExpr.lamN formalFields (VExpr.lamN formalIHs selectorBody) =
      VExpr.lamN (formalFields ++ formalIHs) selectorBody
    exact (VExpr.lamN_append formalFields formalIHs selectorBody).symm
  have hminorMem : selectedMinor ∈ commonArgs ++ fields :=
    List.mem_append_left fields (List.mem_of_getElem? hcommonMinor)
  obtain ⟨_, hminorType⟩ :=
    VEnv.SpineWF.arg_hasType hcaptures hminorMem
  rw [hminorLamShape] at hminorType
  obtain ⟨hselectorTel, selectorResultType, hselectorBody⟩ :=
    VEnv.HasType.lamN_wf henv.ordered hΓ hminorType
  have hiotaBodies' := hiotaBodies
  obtain ⟨_, hiotaTyped⟩ := hiotaBodies'
  have hminorAppType := hiotaTyped.hasType.2
  rw [hminorLamShape] at hminorAppType
  let allArgs := fields ++ capturedIHs
  change env.HasType U Γ
      (VExpr.appN (VExpr.lamN selectorBinders selectorBody) allArgs) _
      at hminorAppType
  have hcapturedIHsLength : capturedIHs.length = formalIHs.length := by
    calc
      capturedIHs.length = ihs.length := by simp [capturedIHs]
      _ = recursiveArgs.length := by simp [ihs]
      _ = view.constructor.view.recursive.length := by
        simp [recursiveArgs, c, blockConstructor,
          NormalizedCtor.recArgsR]
      _ = formalIHs.length := by
        symm
        simpa [formalIHs] using
          view.projectionIHTypes_length code.fieldSort levels hlevelsLength
            params motives hmotivesLength
  have hformalFieldsLength : formalFields.length = fields.length := by
    exact hfieldsLength.symm
  have hallArgsLength : allArgs.length = selectorBinders.length := by
    simp only [allArgs, selectorBinders, List.length_append]
    rw [hformalFieldsLength, hcapturedIHsLength]
  have hminorSpine := VEnv.HasType.spineWF_of_appN henv hΓ
    (VEnv.HasType.lamN hselectorTel hselectorBody) hminorAppType
      hallArgsLength
  have hminorBetaRaw := VEnv.IsDefEq.appN_lamN henv.ordered
    hselectorTel hselectorBody hminorSpine hallArgsLength
  have hiFields : idx < fields.length :=
    (List.getElem?_eq_some_iff.1 hfield).1
  have hfieldAll : allArgs[idx]? = some field := by
    rw [show allArgs = fields ++ capturedIHs by rfl,
      List.getElem?_append_left hiFields, hfield]
  obtain ⟨hidxAll, hfieldGetAll⟩ :=
    List.getElem?_eq_some_iff.1 hfieldAll
  have hselectorBodyLt :
      formalIHs.length + formalFields.length - 1 - idx < allArgs.length := by
    rw [hallArgsLength]
    simp only [selectorBinders, List.length_append]
    rw [hformalFieldsLength]
    omega
  have hfieldInst : VExpr.instRev selectorBody allArgs = field := by
    unfold selectorBody
    rw [VExpr.instRev_bvar_lt allArgs hselectorBodyLt]
    have hposition : allArgs.length - 1 -
        (formalIHs.length + formalFields.length - 1 - idx) = idx := by
      rw [hallArgsLength]
      simp only [selectorBinders, List.length_append]
      rw [hformalFieldsLength]
      omega
    simpa only [hposition] using hfieldGetAll
  change VExpr.instRev selectorBody (fields ++ capturedIHs) = field at hfieldInst
  have hminorBeta : env.IsDefEqU U Γ
      (VExpr.appN selectedMinor (fields ++ capturedIHs)) field := by
    refine ⟨VExpr.instRev selectorResultType allArgs, ?_⟩
    rw [hminorLamShape]
    simpa only [allArgs, hfieldInst] using hminorBetaRaw
  exact henv.isDefEqU_trans hΓ hprojectorToRule
    (henv.isDefEqU_trans hΓ hiotaBodies hminorBeta)

/-- A currently typed operational projector computes exactly on the
canonical selected constructor.  Earlier-prefix construction is deliberately
absent from this statement so runtime sparse-prefix consumers can supply the
program they have just justified. -/
theorem LayoutWF.operationalProjector_constructor_exact_of_program
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.ConversionRegular)
    {idx : Nat}
    {U : Nat} {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    {levels : List VLevel} (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    {params : List VExpr} (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    {code : VStructureView.ProjectionCode}
    (hcode : (view.operationalProjectionCodes levels params)[idx]? =
      some code)
    (hprojector : env.HasType U Γ code.projector
      (.forallE (view.structureType levels params)
        (.app code.typeFn.lift (.bvar 0)))) :
    let fields := view.specializedFields levels params
    env.IsDefEqU U (fields.reverse ++ Γ)
      (.app (code.projector.liftN fields.length)
        (view.projectionConstructorApp levels params fields))
      (.bvar (fields.length - 1 - idx)) := by
  obtain ⟨resultLevel, hparamsSpine₀⟩ := hparamsSpine
  let fields := view.specializedFields levels params
  let m := fields.length
  let fieldArgs := VExpr.bvarRevRange 0 m
  have hidx : idx < m := by
    have h := (List.getElem?_eq_some_iff.1 hcode).1
    simpa [m, fields] using h
  have hsortTel := self.specializedFields_onSortTel henv.ordered
    levels hlevels hlevelsLength params hparamsLength
      ⟨resultLevel, hparamsSpine₀⟩
  have hfieldsOnTel : env.OnTel U Γ fields := by
    simpa [fields] using hsortTel.toOnTel
  have hfieldsCtx : OnCtx (fields.reverse ++ Γ) (env.IsType U) :=
    hfieldsOnTel.toOnCtx hΓ
  have hconstructorPrefix := self.constructorPrefix_hasType henv.ordered
    levels hlevels hlevelsLength params hparamsLength
      ⟨resultLevel, hparamsSpine₀⟩
  have hconstructorPrefixWeak := hconstructorPrefix.weakN henv.ordered
    (Ctx.LiftN.zero (n := m) (Γ := Γ) fields.reverse
      (h := by simp [m]))
  have hconstructorPrefixSelf : env.HasType U
      (([] : List VExpr) ++ fields.reverse ++ Γ)
      ((VExpr.appN (.const view.constructorName levels) params).liftN m)
      ((VExpr.forallN fields
        ((view.structureType levels params).liftN m)).liftN
          (([] : List VExpr).length + fields.length)) := by
    simpa [fields, m] using hconstructorPrefixWeak
  have hmajor₀ := VEnv.HasType.appN_selfSpine
    (env := env) (U := U) (As := fields)
    (B := (view.structureType levels params).liftN m)
    (Δ := []) (Γ := Γ)
    (f := (VExpr.appN (.const view.constructorName levels) params).liftN m)
    hconstructorPrefixSelf
  have hmajor : env.HasType U (fields.reverse ++ Γ)
      (view.projectionConstructorApp levels params fields)
      ((view.structureType levels params).liftN m) := by
    simpa [fields, m, projectionConstructorApp,
      VExpr.liftN, VExpr.liftN_appN, VExpr.appN_append, List.map_map,
      Function.comp_def] using hmajor₀
  let paramsLift := params.map (VExpr.liftN m)
  have hparamsLengthLift : paramsLift.length = view.nparams := by
    simpa [paramsLift] using hparamsLength
  have hfamilyClosed : (view.familyType.instL levels).ClosedN 0 := by
    simpa using (self.familyType_closed henv.ordered).instL
  have hparamsSpineLift : env.SpineWF U (fields.reverse ++ Γ)
      (view.familyType.instL levels) paramsLift (.sort resultLevel) := by
    have h := hparamsSpine₀.weakN henv.ordered
      (Ctx.LiftN.zero (n := m) (Γ := Γ) fields.reverse
        (h := by simp [m]))
    rw [hfamilyClosed.liftN_eq (Nat.zero_le _)] at h
    simpa [paramsLift, m, VExpr.liftN] using h
  have hstructLift : view.structureType levels paramsLift =
      (view.structureType levels params).liftN m := by
    simp [paramsLift]
  have hmajorLift : env.HasType U (fields.reverse ++ Γ)
      (view.projectionConstructorApp levels params fields)
      (view.structureType levels paramsLift) := by
    rwa [hstructLift]
  have hcodesLift := self.operationalProjectionCodes_liftN
    levels params hparamsLength m 0
  have hcodeLift :
      (view.operationalProjectionCodes levels paramsLift)[idx]? =
        some (code.liftN m 0) := by
    rw [← hcodesLift, List.getElem?_map, hcode]
    rfl
  have hspecializedLift : view.specializedFields levels paramsLift =
      VExpr.liftTelN m fields 0 := by
    simpa [paramsLift, fields] using
      self.specializedFields_liftN levels params hparamsLength m 0
  have hfieldBase := hfieldsOnTel.selfSpineWF
    (B := .sort .zero) (Δ := ([] : List VExpr))
  have hfieldsSpine : env.SpineWF U (fields.reverse ++ Γ)
      (VExpr.forallN (view.specializedFields levels paramsLift)
        (.sort .zero)) fieldArgs (.sort .zero) := by
    rw [hspecializedLift]
    simpa [m, fieldArgs, VExpr.liftN_forallN, VExpr.liftN]
      using hfieldBase
  have hfieldArg : fieldArgs[idx]? =
      some (.bvar (m - 1 - idx)) := by
    simpa [fieldArgs] using
      VExpr.bvarRevRange_getElem?_local 0 m idx hidx
  have hctorLift : env.HasType U (fields.reverse ++ Γ)
      (VExpr.appN (.const view.constructorName levels)
        (paramsLift ++ fieldArgs))
      (view.structureType levels paramsLift) := by
    simpa [projectionConstructorApp, paramsLift, fieldArgs, m]
      using hmajorLift
  have hprojectorWeak := hprojector.weakN henv.ordered
    (Ctx.LiftN.zero (n := m) (Γ := Γ) fields.reverse
      (h := by simp [m]))
  have hprojectorLift : env.HasType U (fields.reverse ++ Γ)
      (code.liftN m 0).projector
      (.forallE (view.structureType levels paramsLift)
        (.app (code.liftN m 0).typeFn.lift (.bvar 0))) := by
    simpa [VStructureView.ProjectionCode.liftN, hstructLift,
      VExpr.liftN, VExpr.liftN_lift_projection] using hprojectorWeak
  have hiota := self.operationalProjector_constructor_exact henv hfieldsCtx
    hlevels hlevelsLength hparamsLengthLift
    ⟨resultLevel, hparamsSpineLift⟩ hcodeLift hprojectorLift
    (by rw [hspecializedLift, VExpr.liftTelN_length]
        simp [fieldArgs, m])
    hfieldArg hctorLift hfieldsSpine
  simpa [fields, m, fieldArgs, paramsLift,
    VStructureView.ProjectionCode.liftN, projectionConstructorApp]
    using hiota

/-- The next admissible operational projector computes exactly on the
canonical selected constructor, using only the typed and exact earlier
source-order prefix. -/
theorem LayoutWF.operationalProjector_constructor_exact_of_prefix
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.ConversionRegular)
    {idx : Nat}
    (programs : view.OperationalProgramsWFPrefix env idx)
    (exact : view.OperationalConstructorProjectorsExactPrefix env idx)
    {U : Nat} {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U))
    {levels : List VLevel} (hlevels : ∀ level ∈ levels, level.WF U)
    (hlevelsLength : levels.length = view.uvars)
    {params : List VExpr} (hparamsLength : params.length = view.nparams)
    (hparamsSpine : ∃ resultLevel,
      env.SpineWF U Γ (view.familyType.instL levels)
        params (.sort resultLevel))
    {code : VStructureView.ProjectionCode}
    (hcode : (view.operationalProjectionCodes levels params)[idx]? =
      some code)
    (hmotiveLevel : view.generation.motiveLevel.inst
      (view.projectionLevels code.fieldSort levels) = code.fieldSort) :
    let fields := view.specializedFields levels params
    env.IsDefEqU U (fields.reverse ++ Γ)
      (.app (code.projector.liftN fields.length)
        (view.projectionConstructorApp levels params fields))
      (.bvar (fields.length - 1 - idx)) := by
  have hprojector := self.operationalProgram_hasType_of_prefix henv
    programs exact hΓ hlevels hlevelsLength hparamsLength hparamsSpine hcode
      hmotiveLevel
  exact self.operationalProjector_constructor_exact_of_program henv hΓ
    hlevels hlevelsLength hparamsLength hparamsSpine hcode hprojector

/-- Extend operational projector typing by one admissible program. -/
theorem LayoutWF.operationalProgramsWFPrefix_succ
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.ConversionRegular)
    {limit : Nat}
    (programs : view.OperationalProgramsWFPrefix env limit)
    (exact : view.OperationalConstructorProjectorsExactPrefix env limit)
    (admissible : ∀ {levels : List VLevel} {params : List VExpr}
        {code : VStructureView.ProjectionCode},
      (view.operationalProjectionCodes levels params)[limit]? = some code →
      view.generation.motiveLevel.inst
        (view.projectionLevels code.fieldSort levels) = code.fieldSort) :
    view.OperationalProgramsWFPrefix env (limit + 1) := by
  intro U Γ levels params idx code hidx hΓ hlevels hlevelsLength
    hparamsLength hparamsSpine hcode
  by_cases hiLimit : idx < limit
  · exact programs hiLimit hΓ hlevels hlevelsLength hparamsLength
      hparamsSpine hcode
  · have hiEq : idx = limit := by omega
    subst idx
    exact self.operationalProgram_hasType_of_prefix henv programs exact
      hΓ hlevels hlevelsLength hparamsLength hparamsSpine hcode
        (admissible hcode)

/-- Extend exact canonical constructor computation by one admissible
operational projector. -/
theorem LayoutWF.operationalConstructorProjectorsExactPrefix_succ
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.ConversionRegular)
    {limit : Nat}
    (programs : view.OperationalProgramsWFPrefix env limit)
    (exact : view.OperationalConstructorProjectorsExactPrefix env limit)
    (admissible : ∀ {levels : List VLevel} {params : List VExpr}
        {code : VStructureView.ProjectionCode},
      (view.operationalProjectionCodes levels params)[limit]? = some code →
      view.generation.motiveLevel.inst
        (view.projectionLevels code.fieldSort levels) = code.fieldSort) :
    view.OperationalConstructorProjectorsExactPrefix env (limit + 1) := by
  intro U Γ levels params count hcount hΓ hlevels hlevelsLength
    hparamsLength hparamsSpine hcountCodes
  let fields := view.specializedFields levels params
  let m := fields.length
  have hcountFields : count ≤ m := by
    simpa [fields, m] using hcountCodes
  apply List.Forall₂.of_getElem?_local
  · rw [List.length_map, List.length_take,
      VExpr.bvarRevRange_length, Nat.min_eq_left hcountCodes]
  intro i projected selected hprojected hselected
  have hiCount : i < count := by
    have hi := (List.getElem?_eq_some_iff.1 hprojected).1
    simp only [List.length_map] at hi
    rw [List.length_take, Nat.min_eq_left hcountCodes] at hi
    exact hi
  rw [List.getElem?_map,
    List.getElem?_take_of_lt hiCount] at hprojected
  obtain ⟨code, hcode, hprojectedEq⟩ :=
    Option.map_eq_some_iff.1 hprojected
  subst projected
  have hselectedCanonical :=
    VExpr.bvarRevRange_getElem?_local (m - count) count i hiCount
  have hselectedEq : selected = .bvar (m - 1 - i) := by
    have heq := Option.some.inj (hselected.symm.trans hselectedCanonical)
    rw [show m - count + (count - 1 - i) = m - 1 - i by omega] at heq
    exact heq
  subst selected
  by_cases hiLimit : i < limit
  · have hcodeBound : i + 1 ≤
        (view.operationalProjectionCodes levels params).length := by
      exact Nat.succ_le_of_lt (List.getElem?_eq_some_iff.1 hcode).1
    have hold := exact (count := i + 1) (by omega) hΓ hlevels
      hlevelsLength hparamsLength hparamsSpine hcodeBound
    have hiM : i < m := Nat.lt_of_lt_of_le hiCount hcountFields
    have hleftOld :
        (((view.operationalProjectionCodes levels params).take (i + 1)).map
          fun prior =>
            VExpr.app (prior.projector.liftN m)
              (view.projectionConstructorApp levels params fields))[i]? =
          some (VExpr.app (code.projector.liftN m)
            (view.projectionConstructorApp levels params fields)) := by
      rw [List.getElem?_map, List.getElem?_take_of_lt (by omega), hcode]
      rfl
    have hrightOld :
        (VExpr.bvarRevRange (m - (i + 1)) (i + 1))[i]? =
          some (.bvar (m - 1 - i)) := by
      have hout := VExpr.bvarRevRange_getElem?_local
        (m - (i + 1)) (i + 1) i (by omega)
      simpa only [show m - (i + 1) + (i + 1 - 1 - i) =
          m - 1 - i by omega] using hout
    exact List.Forall₂.getElem?_local hold hleftOld hrightOld
  · have hiEq : i = limit := by omega
    subst i
    have hmotiveLevel := admissible hcode
    exact .inr (by
      simpa [fields, m] using
        self.operationalProjector_constructor_exact_of_prefix henv
          programs exact hΓ hlevels hlevelsLength hparamsLength
          hparamsSpine hcode hmotiveLevel)

/-- Admissible operational projector generation is typed and computes
canonically on the selected constructor, prefix by prefix. -/
theorem LayoutWF.operationalProgramsExactPrefix_of_admissible
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.ConversionRegular)
    {limit : Nat}
    (admissible : view.OperationalMotiveAdmissiblePrefix limit) :
    view.OperationalProgramsWFPrefix env limit ∧
      view.OperationalConstructorProjectorsExactPrefix env limit := by
  induction limit with
  | zero =>
      constructor
      · intro U Γ levels params idx code hidx
        omega
      · intro U Γ levels params count hcount hΓ hlevels hlevelsLength
          hparamsLength hparamsSpine hcountCodes
        have hcountEq : count = 0 := by omega
        subst count
        change List.Forall₂ _ [] (VExpr.bvarRevRange _ 0)
        exact .nil
  | succ limit ih =>
      have admissiblePrefix : view.OperationalMotiveAdmissiblePrefix limit := by
        intro levels params idx code hidx hcode
        exact admissible (by omega) hcode
      obtain ⟨programs, exact⟩ := ih admissiblePrefix
      have admissibleAt : ∀ {levels : List VLevel} {params : List VExpr}
          {code : VStructureView.ProjectionCode},
          (view.operationalProjectionCodes levels params)[limit]? =
            some code →
          view.generation.motiveLevel.inst
            (view.projectionLevels code.fieldSort levels) =
              code.fieldSort := by
        intro levels params code hcode
        exact admissible (Nat.lt_succ_self limit) hcode
      constructor
      · exact self.operationalProgramsWFPrefix_succ henv programs exact
          admissibleAt
      · exact self.operationalConstructorProjectorsExactPrefix_succ henv
          programs exact admissibleAt

/-- Universal operational elimination admissibility supplies typed projector
programs. -/
theorem LayoutWF.operationalProgramsWF_of_admissible
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) (henv : env.ConversionRegular)
    (admissible : view.OperationalMotiveAdmissible) :
    view.OperationalProgramsWF env := by
  intro U Γ levels params idx code hΓ hlevels hlevelsLength
    hparamsLength hparamsSpine hcode
  have admissiblePrefix :
      view.OperationalMotiveAdmissiblePrefix (idx + 1) := by
    intro levels' params' j code' hj hcode'
    exact admissible hcode'
  have programs : view.OperationalProgramsWFPrefix env (idx + 1) :=
    (self.operationalProgramsExactPrefix_of_admissible henv
      (limit := idx + 1) admissiblePrefix).1
  exact programs (by omega) hΓ hlevels hlevelsLength hparamsLength
    hparamsSpine hcode

/-- The strong block projection invariant makes every field admissible for
the operational recursor. -/
theorem WF.operationalMotiveAdmissible
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) : view.OperationalMotiveAdmissible := by
  intro levels params idx code hcode
  obtain ⟨fieldSort, hfieldSort, hcodeSort, -, -⟩ :=
    view.operationalProjectionCodes_get?_program_shape levels params hcode
  rw [hcodeSort]
  rw [List.getElem?_map] at hfieldSort
  obtain ⟨rawSort, hrawSort, rfl⟩ :=
    Option.map_eq_some_iff.1 hfieldSort
  exact self.motiveLevel_projectionLevels rawSort
    (List.mem_iff_getElem?.2 ⟨idx, hrawSort⟩) levels

/-- Strong block projection well-formedness supplies every operational
projector program. -/
theorem WF.toOperationalProgramsWF
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) (henv : env.ConversionRegular) :
    view.OperationalProgramsWF env :=
  self.toLayoutWF.operationalProgramsWF_of_admissible henv
    self.operationalMotiveAdmissible

/-- Strong block projection well-formedness supplies typed and exact
operational prefixes at every source-order bound. -/
theorem WF.toOperationalProgramsExactPrefix
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) (henv : env.ConversionRegular) (limit : Nat) :
    view.OperationalProgramsWFPrefix env limit ∧
      view.OperationalConstructorProjectorsExactPrefix env limit := by
  apply self.toLayoutWF.operationalProgramsExactPrefix_of_admissible henv
  intro levels params idx code hidx hcode
  exact self.operationalMotiveAdmissible hcode

/-- Checked mutual generation determines canonical reconstruction typing
for the retained unindexed family. -/
theorem WF.toRebuildWF
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) (henv : env.ConversionRegular) :
    view.RebuildWF env :=
  self.toRebuildWF_of_programs henv (self.toProgramsWF henv)


/-- The exact lower-layer structure-eta descriptor generated by a retained
family inside a mutual block.  Its projectors apply the actual mutual
recursor with every block motive and flattened minor. -/
def LayoutWF.toStructEta
    {view : VBlockStructureView} {env : VEnv}
    (self : view.LayoutWF env) : VStructEta where
  uvars := view.uvars
  nparams := view.nparams
  nfields := view.fields.length
  familyName := view.name
  familyType := view.familyType
  constructorName := view.constructorName
  projectors := fun levels params =>
    (view.projectionCodes levels params).map (·.projector)
  projectors_length := by
    intro levels params _ _
    simp [specializedFields, fields]
  projectors_liftN := by
    intro levels params n k hparams
    have h := self.projectionCodes_liftN levels params hparams n k
    simpa [List.map_map, VStructureView.ProjectionCode.liftN,
      Function.comp_def] using
      congrArg (List.map (·.projector)) h
  projectors_instN := by
    intro levels params a k hparams
    have h := self.projectionCodes_instN levels params hparams a k
    simpa [List.map_map, VStructureView.ProjectionCode.instN,
      Function.comp_def] using
      congrArg (List.map (·.projector)) h
  projectors_instL := by
    intro levels params ls
    have h := projectionCodes_instL view levels params ls
    simpa [List.map_map, VStructureView.ProjectionCode.instL,
      Function.comp_def] using
      congrArg (List.map (·.projector)) h

abbrev WF.toStructEta
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) := self.toLayoutWF.toStructEta

@[simp] theorem WF.toStructEta_structureType
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) (levels : List VLevel) (params : List VExpr) :
    self.toStructEta.structureType levels params =
      view.structureType levels params := rfl

@[simp] theorem WF.toStructEta_rebuild
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) (levels : List VLevel) (params : List VExpr)
    (major : VExpr) :
    self.toStructEta.rebuild levels params major =
      view.etaRebuild levels params major := by
  simp only [VStructEta.rebuild, VStructEta.projectionArgs, WF.toStructEta,
    LayoutWF.toStructEta, etaRebuild, projectionArgs]
  rw [← view.projectionCodes_length levels params, List.take_length]
  simp [List.map_map, Function.comp_def]

/-- A persistent family of rule-independent reconstruction proofs packages
the block-backed descriptor as a registry-valid `VStructEta.WF`. -/
theorem WF.toStructEtaWF_of_rebuilds
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) (henv : env.Ordered)
    (rebuilds : ∀ {env' : VEnv}, env ≤ env' →
      env'.ConversionRegular → view.RebuildWF env') :
    self.toStructEta.WF env where
  familyType_closed := by
    change view.familyType.ClosedN
    exact self.familyType_closed henv
  rebuild_hasType := by
    intro env' hle hregular U Γ levels params major hΓ hlevels hlevelsLength
      hparamsLength hparamsSpine hmajor
    simpa using rebuilds hle hregular hΓ hlevels hlevelsLength hparamsLength
      hparamsSpine hmajor

/-- Checked block generation supplies the persistent lower-layer
structure-eta certificate.  The registered inventory may grow through raw
`VEnv.LE`; each typing target supplies its own conversion-regularity laws. -/
theorem WF.toStructEtaWF
    {view : VBlockStructureView} {env : VEnv}
    (self : view.WF env) (henv : env.WF) :
    self.toStructEta.WF env :=
  self.toStructEtaWF_of_rebuilds henv.ordered fun hle hregular =>
    (self.mono hle hregular.ordered).toRebuildWF hregular

/-- Assemble the producer layout at the exact output of a complete block
transaction.  Unlike `WF.ofTrace`, this theorem needs neither a prelude
dummy nor a global small-field hypothesis. -/
theorem LayoutWF.ofTrace
    {view : VBlockStructureView} {pre blockEnv env : VEnv}
    (ordered : pre.Ordered)
    (generationWF : view.generation.WF pre blockEnv)
    (trace : VEnv.AddInductBlockGenerationTrace pre env view.generation)
    (fieldTelescope : env.OnSortTel view.uvars
      view.generation.block.checked.params.reverse view.fields
        view.fieldSorts) :
    view.LayoutWF env where
  toRegistered := Registered.ofTrace trace
  generationEnv := trace.generationEnv ordered generationWF
  fieldTelescope := fieldTelescope

/-- Assemble the restriction invariant at the exact output of a complete
block transaction.  The block-wide generation semantics and registrations
are producer-owned; only the exact field-sort telescope and its small-
elimination consequence remain inputs to the projection-program layer. -/
theorem WF.ofTrace
    {view : VBlockStructureView} {pre blockEnv env : VEnv}
    (ordered : pre.Ordered)
    (generationWF : view.generation.WF pre blockEnv)
    (trace : VEnv.AddInductBlockGenerationTrace pre env view.generation)
    (punitRegistered : PUnitRegistered env)
    (fieldTelescope : env.OnSortTel view.uvars
      view.generation.block.checked.params.reverse view.fields view.fieldSorts)
    (smallFields : view.generation.elimination = .small →
      ∀ level ∈ view.fieldSorts, level = .zero) :
    view.WF env where
  toRegistered := Registered.ofTrace trace
  punitRegistered := punitRegistered
  generationEnv := trace.generationEnv ordered generationWF
  fieldTelescope := fieldTelescope
  smallFields := smallFields

end VBlockStructureView

end Lean4Lean
