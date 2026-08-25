import Lean4Lean.Theory.Typing.InductivePattern
import Lean4Lean.Theory.Typing.UniqueTyping

/-! # Pattern soundness for generated iota rules

The typed β-collapse layer for L4L-10B: applying a lambda tower to a
well-typed argument spine is definitionally equal to the iterated
instantiation of its body (`IsDefEq.appN_lamN`), applications are
congruent along spines (`IsDefEq.appN_congr`, `IsDefEq.appN_defEq` over
`SpineDefEq`), and a matched pattern's captures are exactly the spine
arguments (`varN_matches_paths`). `pat_wf` then proves that a successful
match whose checks hold is definitionally equal to its RHS template — by
applying the registered `addInduct` rule tower to the captured arguments
and β-collapsing both readings. -/

namespace Lean4Lean

open VExpr

namespace VExpr

/-- Instantiation pushes under a lambda telescope, mirroring
`instN_forallN`. -/
theorem instN_lamN (a : VExpr) : ∀ (tel : List VExpr) (X : VExpr) (k : Nat),
    (lamN tel X).inst a k = lamN (instTelN a tel k) (X.inst a (k + tel.length))
  | [], _, _ => rfl
  | A :: tel, X, k => by
    show VExpr.lam _ _ = VExpr.lam _ _
    rw [instN_lamN a tel X (k+1),
      show k+1+tel.length = k+(tel.length+1) from by omega]
    rfl

/-- Universe instantiation pushes under a lambda telescope. -/
theorem instL_lamN (ls : List VLevel) : ∀ (As : List VExpr) (e : VExpr),
    (lamN As e).instL ls = lamN (As.map (instL ls)) (e.instL ls)
  | [], _ => rfl
  | A :: As, e => by
    show VExpr.lam _ _ = VExpr.lam _ _
    rw [instL_lamN ls As e]

end VExpr

/-- Matching a constant `varN` tower captures exactly the spine arguments:
the `varNPaths` read back the argument list. -/
theorem Pattern.varN_matches_paths {c : Name} {m1 : List VLevel} :
    ∀ (n : Nat) (as : List VExpr) {f : VExpr} {m2},
      (Pattern.varN (.const c) n).Matches (VExpr.appN f as) m1 m2 →
      as.length = n →
      (Pattern.varNPaths (.const c) n).map m2 = as := by
  intro n
  induction n with
  | zero =>
    intro as f m2 H hlen
    obtain rfl : as = [] := List.length_eq_zero_iff.1 hlen
    rfl
  | succ n ih =>
    intro as f m2 H hlen
    have hne : as ≠ [] := by rintro rfl; simp at hlen
    obtain ⟨as', a, rfl⟩ : ∃ as' a, as = as' ++ [a] :=
      ⟨as.dropLast, as.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
    rw [VExpr.appN_append] at H
    have has : as'.length = n := by simpa using hlen
    cases H with
    | var h =>
      show ((Pattern.varNPaths (.const c) n).map some ++ [none]).map _ =
        as' ++ [a]
      rw [List.map_append, List.map_map]
      exact congrArg (· ++ [a]) (ih as' h has)

/-- Applying an RHS template spine computes to the applied template
values. -/
theorem Pattern.RHS.appN_apply {p : Pattern} (m1 : List VLevel)
    (m2 : p.Path → VExpr) :
    ∀ (f : p.RHS) (as : List (p.RHS)),
      (Pattern.RHS.appN f as).apply m1 m2 =
        VExpr.appN (f.apply m1 m2) (as.map (Pattern.RHS.apply m1 m2))
  | _, [] => rfl
  | f, a :: as => by
    show (Pattern.RHS.appN (.app f a) as).apply m1 m2 = _
    rw [Pattern.RHS.appN_apply m1 m2 (.app f a) as]
    rfl

/-- A `HeadConstN` spine names its argument list. -/
theorem HeadConstN.exists_appN {c : Name} {ls : List VLevel} :
    ∀ {n : Nat} {e : VExpr}, HeadConstN c ls n e →
      ∃ as : List VExpr, e = VExpr.appN (.const c ls) as ∧ as.length = n
  | _, _, .const => ⟨[], rfl, rfl⟩
  | _, _, .app (a := a) h =>
    let ⟨as, he, hl⟩ := h.exists_appN
    ⟨as ++ [a], by rw [VExpr.appN_append, ← he]; rfl, by simp [hl]⟩

namespace VExpr

/-- The value of a bound variable under iterated instantiation: the spine
argument at its reverse position. -/
theorem instRev_bvar_lt : ∀ (es : List VExpr) {i : Nat} (h : i < es.length),
    instRev (.bvar i) es = es[es.length - 1 - i]'(by omega)
  | e :: es, i, h => by
    rcases Nat.lt_or_ge i es.length with h' | h'
    · rw [show instRev (.bvar i) (e :: es) = instRev (.bvar i) es from
        instRev_bvar_lt_cons es e h', instRev_bvar_lt es h']
      simp only [show (e :: es).length - 1 - i = (es.length - 1 - i) + 1 from by
        simp only [List.length_cons]; omega, List.getElem_cons_succ]
    · obtain rfl : i = es.length := by
        simp only [List.length_cons] at h; omega
      show instRev (instVar es.length e es.length) es = _
      rw [show instVar es.length e es.length = liftN es.length e from by
        simp [instVar]]
      rw [instRev_liftN_len]
      simp only [show (e :: es).length - 1 - es.length = 0 from by
        simp only [List.length_cons]; omega, List.getElem_cons_zero]

/-- Iterated instantiation of a reverse bound-variable segment reads back
the corresponding spine segment. -/
theorem map_instRev_bvarRevRange_seg (es : List VExpr) :
    ∀ (q off : Nat), off + q ≤ es.length →
    (bvarRevRange off q).map (instRev · es) =
      (es.drop (es.length - off - q)).take q := by
  intro q
  induction q with
  | zero => intro off h; simp [VExpr.bvarRevRange]
  | succ q ih =>
    intro off h
    show instRev (.bvar (off + q)) es :: (bvarRevRange off q).map (instRev · es) = _
    rw [instRev_bvar_lt es (by omega), ih off (by omega)]
    have hd : es.length - off - (q + 1) < es.length := by omega
    simp only [show es.length - 1 - (off + q) = es.length - off - (q + 1) from by
      omega, show es.length - off - q = (es.length - off - (q + 1)) + 1 from by
      omega]
    rw [List.drop_eq_getElem_cons hd, List.take_succ_cons]

end VExpr

/-! ## Typed β-collapse of applied telescopes -/

/-- Instantiating below a reversed telescope, mirroring
`Ctx.LiftN.consTel`. -/
theorem Ctx.InstN.consTel {Γ₀ : List VExpr} {e₀ A₀ : VExpr} :
    ∀ (As : List VExpr) {k : Nat} {Γ Γ' : List VExpr},
      Ctx.InstN Γ₀ e₀ A₀ k Γ Γ' →
      Ctx.InstN Γ₀ e₀ A₀ (As.length + k) (As.reverse ++ Γ)
        ((VExpr.instTelN e₀ As k).reverse ++ Γ')
  | [], k, Γ, Γ', W => by simpa [VExpr.instTelN] using W
  | A :: As, k, Γ, Γ', W => by
    have h := Ctx.InstN.consTel As (Ctx.InstN.succ (A := A) W)
    rw [show As.length + (k+1) = (A :: As).length + k from by simp; omega] at h
    simpa [VExpr.instTelN, List.append_assoc] using h

/-- Instantiating a telescope's context. -/
theorem VEnv.OnTel.instN {env : VEnv} (henv : env.Ordered) {U : Nat}
    {Γ₀ : List VExpr} {e₀ A₀ : VExpr} (h₀ : env.HasType U Γ₀ e₀ A₀) :
    ∀ {As : List VExpr} {k : Nat} {Γ Γ' : List VExpr},
      Ctx.InstN Γ₀ e₀ A₀ k Γ Γ' → VEnv.OnTel env U Γ As →
      VEnv.OnTel env U Γ' (VExpr.instTelN e₀ As k)
  | [], _, _, _, _, _ => trivial
  | _ :: _, _, _, _, W, ⟨⟨u, hA⟩, hT⟩ =>
    ⟨⟨u, hA.instN henv W h₀⟩, VEnv.OnTel.instN henv h₀ W.succ hT⟩

/-- Extending the closed base of a well-formed telescope on the right leaves
its binder expressions unchanged. -/
theorem VEnv.OnTel.weakR {env : VEnv} (henv : env.Ordered)
    {U : Nat} {Γ Γ' : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ {As : List VExpr}, VEnv.OnTel env U Γ As →
      VEnv.OnTel env U (Γ ++ Γ') As
  | [], _ => trivial
  | A :: As, ⟨hA, hAs⟩ => by
      obtain ⟨u, hA⟩ := hA
      refine ⟨⟨u, hA.weakR henv (VEnv.CtxWF.closed henv hΓ) Γ'⟩, ?_⟩
      have hΓA : OnCtx (A :: Γ) (env.IsType U) :=
        ⟨hΓ, ⟨u, hA⟩⟩
      simpa using VEnv.OnTel.weakR henv (Γ := A :: Γ) (Γ' := Γ')
        hΓA hAs

/-- Pi injectivity turns equality of two iterated-Pi sorts into structural
telescope equality.  This is the consumer-side inverse of
`TelDefEq.forallN_defeq`. -/
theorem VEnv.TelDefEq.of_forallN_sort_defeq
    {env : VEnv} (henv : env.WF) {U : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ {As As' : List VExpr} {u u' : VLevel},
      env.IsDefEqU U Γ
        (VExpr.forallN As (.sort u))
        (VExpr.forallN As' (.sort u')) →
      env.TelDefEq U Γ As As'
  | [], [], _, _, _ => trivial
  | [], _ :: _, _, _, h =>
      (VEnv.IsDefEqU.sort_forallE_inv henv hΓ h).elim
  | _ :: _, [], _, _, h =>
      (VEnv.IsDefEqU.sort_forallE_inv henv hΓ h.symm).elim
  | A :: As, A' :: As', _, _, h => by
      obtain ⟨⟨uA, hA⟩, ⟨uB, hB⟩⟩ :=
        VEnv.IsDefEqU.forallE_inv henv hΓ h
      refine ⟨⟨uA, hA⟩, ?_⟩
      exact VEnv.TelDefEq.of_forallN_sort_defeq henv (Γ := A :: Γ)
        ⟨hΓ, ⟨uA, hA.hasType.1⟩⟩ ⟨.sort uB, hB⟩

/-- Pi injectivity recovers structural telescope equality from arbitrary
iterated-Pi codomains when the caller already knows the two telescope
arities agree.  Unlike `of_forallN_sort_defeq`, no terminal sort/Pi
disjointness is needed. -/
theorem VEnv.TelDefEq.of_forallN_defeq_of_length
    {env : VEnv} (henv : env.WF) {U : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ {As As' : List VExpr} {C C' : VExpr},
      As.length = As'.length →
      env.IsDefEqU U Γ (VExpr.forallN As C) (VExpr.forallN As' C') →
      env.TelDefEq U Γ As As'
  | [], [], _, _, _, _ => trivial
  | [], _ :: _, _, _, hlen, _ => by simp at hlen
  | _ :: _, [], _, _, hlen, _ => by simp at hlen
  | A :: As, A' :: As', _, _, hlen, h => by
      obtain ⟨⟨uA, hA⟩, ⟨uB, hB⟩⟩ :=
        VEnv.IsDefEqU.forallE_inv henv hΓ h
      refine ⟨⟨uA, hA⟩, ?_⟩
      exact VEnv.TelDefEq.of_forallN_defeq_of_length henv
        (Γ := A :: Γ) ⟨hΓ, ⟨uA, hA.hasType.1⟩⟩
        (by simpa using hlen) ⟨.sort uB, hB⟩

/-- Definitionally equal substitutions into a well-formed dependent
telescope produce structurally equal instantiated telescopes. -/
theorem VEnv.OnTel.telDefEq_instDF
    {env : VEnv} (henv : env.WF) {U : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U))
    {A a a' : VExpr}
    (ha : env.IsDefEq U Γ a a' A)
    {As : List VExpr}
    (hAs : VEnv.OnTel env U (A :: Γ) As) :
    env.TelDefEq U Γ
      (VExpr.instTelN a As 0)
      (VExpr.instTelN a' As 0) := by
  have hsort : env.IsType U (As.reverse ++ A :: Γ) (.sort .zero) :=
    ⟨.succ .zero, VEnv.HasType.sort trivial⟩
  obtain ⟨u, htower⟩ := VEnv.IsType.forallN hAs hsort
  have hinst := VEnv.IsDefEq.instDF henv.ordered hΓ htower ha
  apply VEnv.TelDefEq.of_forallN_sort_defeq henv hΓ
  refine ⟨.sort u, ?_⟩
  simpa [VExpr.instN_forallN, VExpr.inst] using hinst

/-- Pointwise defeq of two application spines against a peeled pi type. -/
inductive VEnv.SpineDefEq (env : VEnv) (U : Nat) (Γ : List VExpr) :
    VExpr → List VExpr → List VExpr → VExpr → Prop where
  | nil : VEnv.SpineDefEq env U Γ A [] [] A
  | cons : env.IsDefEq U Γ a a' A₁ →
      VEnv.SpineDefEq env U Γ (A₂.inst a) es es' B →
      VEnv.SpineDefEq env U Γ (.forallE A₁ A₂) (a :: es) (a' :: es') B

/-- Iterated application congruence along a pointwise defeq spine. -/
theorem VEnv.IsDefEq.appN_defEq {env : VEnv} {U : Nat} {Γ : List VExpr} :
    ∀ {es es' : List VExpr} {F B X Y : VExpr},
      env.IsDefEq U Γ X Y F → VEnv.SpineDefEq env U Γ F es es' B →
      env.IsDefEq U Γ (VExpr.appN X es) (VExpr.appN Y es') B
  | [], _, _, _, _, _, h, .nil => h
  | a :: _, a' :: _, _, _, X, Y, h, .cons ha hrest =>
    VEnv.IsDefEq.appN_defEq (X := X.app a) (Y := Y.app a') (h.appDF ha) hrest

/-- A well-typed spine is a reflexive defeq spine. -/
theorem VEnv.SpineWF.toSpineDefEq {env : VEnv} {U : Nat} {Γ : List VExpr} :
    ∀ {es : List VExpr} {F B : VExpr}, env.SpineWF U Γ F es B →
      VEnv.SpineDefEq env U Γ F es es B
  | [], _, _, .nil => .nil
  | _ :: _, _, _, .cons ha hrest => .cons ha hrest.toSpineDefEq

/-- Iterated application congruence in the function position. -/
theorem VEnv.IsDefEq.appN_congr {env : VEnv} {U : Nat} {Γ : List VExpr}
    {es : List VExpr} {F B X Y : VExpr}
    (h : env.IsDefEq U Γ X Y F) (hs : env.SpineWF U Γ F es B) :
    env.IsDefEq U Γ (VExpr.appN X es) (VExpr.appN Y es) B :=
  h.appN_defEq hs.toSpineDefEq

/-- A registered equation remains available after environment growth.

This is the primitive transport operation for consumer-certified extension
rules: `VEnv.LE` transports registration, while the core `.extra` constructor
still requires the exact universe instantiation side conditions. -/
theorem VEnv.LE.extra {env env' : VEnv} (henv : env ≤ env') {U : Nat}
    {Γ : List VExpr} {df : VDefEq} {ls : List VLevel}
    (hreg : env.defeqs df) (hlevels : ∀ l ∈ ls, l.WF U)
    (hlevelsLength : ls.length = df.uvars) :
    env'.IsDefEq U Γ (df.lhs.instL ls) (df.rhs.instL ls)
      (df.type.instL ls) :=
  .extra (henv.defeqs hreg) hlevels hlevelsLength

/-- Transport a registered equation through environment growth and then
apply it to a well-typed spine. This is the beta-tower consumer boundary:
registration supplies only the tower equality; application congruence and
spine typing remain explicit proof obligations. -/
theorem VEnv.LE.extra_appN {env env' : VEnv} (henv : env ≤ env') {U : Nat}
    {Γ : List VExpr} {df : VDefEq} {ls : List VLevel} {args : List VExpr}
    {B : VExpr} (hreg : env.defeqs df)
    (hlevels : ∀ l ∈ ls, l.WF U) (hlevelsLength : ls.length = df.uvars)
    (hspine : env.SpineWF U Γ (df.type.instL ls) args B) :
    env'.IsDefEq U Γ
      (VExpr.appN (df.lhs.instL ls) args)
      (VExpr.appN (df.rhs.instL ls) args) B :=
  (henv.extra hreg hlevels hlevelsLength).appN_congr (hspine.mono henv)

/-- The symmetric applied transport is derived, not a second trusted
extension direction. -/
theorem VEnv.LE.extra_appN_symm {env env' : VEnv} (henv : env ≤ env')
    {U : Nat} {Γ : List VExpr} {df : VDefEq} {ls : List VLevel}
    {args : List VExpr} {B : VExpr} (hreg : env.defeqs df)
    (hlevels : ∀ l ∈ ls, l.WF U) (hlevelsLength : ls.length = df.uvars)
    (hspine : env.SpineWF U Γ (df.type.instL ls) args B) :
    env'.IsDefEq U Γ
      (VExpr.appN (df.rhs.instL ls) args)
      (VExpr.appN (df.lhs.instL ls) args) B :=
  (henv.extra_appN hreg hlevels hlevelsLength hspine).symm

/-- Applying a lambda telescope to a full well-typed spine collapses to the
iterated instantiation of its body. -/
theorem VEnv.IsDefEq.appN_lamN {env : VEnv} (henv : env.Ordered) {U : Nat} :
    ∀ {As : List VExpr} {Γ : List VExpr} {body T B : VExpr} {es : List VExpr},
      VEnv.OnTel env U Γ As →
      env.HasType U (As.reverse ++ Γ) body T →
      env.SpineWF U Γ (VExpr.forallN As T) es B →
      es.length = As.length →
      env.IsDefEq U Γ (VExpr.appN (VExpr.lamN As body) es)
        (VExpr.instRev body es) B
  | [], Γ, body, T, B, es, _, hb, hs, hlen => by
    obtain rfl : es = [] := List.length_eq_zero_iff.1 hlen
    obtain rfl : T = B := hs.nil_inv
    exact hb
  | A :: As, Γ, body, T, B, e :: es, ⟨⟨u, hA⟩, hT⟩, hb,
      .cons he hrest, hlen => by
    have hb' : env.HasType U (As.reverse ++ (A :: Γ)) body T := by
      simpa [List.append_assoc] using hb
    have hlam : env.HasType U (A :: Γ) (VExpr.lamN As body)
        (VExpr.forallN As T) := VEnv.HasType.lamN hT hb'
    have hbeta := VEnv.IsDefEq.beta hlam he
    rw [VExpr.instN_lamN, Nat.zero_add] at hbeta
    have hlen2 : es.length = As.length := by simpa using hlen
    have hT' : VEnv.OnTel env U Γ (VExpr.instTelN e As 0) :=
      VEnv.OnTel.instN henv he .zero hT
    have hb'' : env.HasType U ((VExpr.instTelN e As 0).reverse ++ Γ)
        (body.inst e As.length) (T.inst e As.length) := by
      have W := Ctx.InstN.consTel (Γ₀ := Γ) (e₀ := e) (A₀ := A) As .zero
      have := hb'.instN henv W he
      simpa using this
    have hrest' : env.SpineWF U Γ
        (VExpr.forallN (VExpr.instTelN e As 0) (T.inst e As.length)) es B := by
      rw [VExpr.instN_forallN] at hrest
      simpa using hrest
    have hlen' : es.length = (VExpr.instTelN e As 0).length := by
      rw [VExpr.instTelN_length]; exact hlen2
    have IH := VEnv.IsDefEq.appN_lamN henv hT' hb'' hrest' hlen'
    have hstep := VEnv.IsDefEq.appN_congr hbeta hrest
    show env.IsDefEq U Γ
      (VExpr.appN ((VExpr.lam A (VExpr.lamN As body)).app e) es)
      (VExpr.instRev (body.inst e es.length) es) B
    rw [hlen2]
    exact hstep.trans IH

/-- Instantiate a terminal definitional equality through a saturated telescope spine. -/
theorem VEnv.SpineWF.instRev_defeq
    {env : VEnv} (henv : env.Ordered) {U : Nat} {Γ : List VExpr} :
    ∀ {As : List VExpr} {C C' T : VExpr} {es : List VExpr} {B : VExpr},
      env.SpineWF U Γ (VExpr.forallN As C) es B →
      es.length = As.length →
      env.IsDefEq U (As.reverse ++ Γ) C C' T →
      env.IsDefEq U Γ (VExpr.instRev C es) (VExpr.instRev C' es)
        (VExpr.instRev T es)
  | [], C, C', T, [], B, hspine, _, hterminal => by
      simpa [VExpr.instRev] using hterminal
  | [], _, _, _, _ :: _, _, _, hlen, _ => by simp at hlen
  | _ :: _, _, _, _, [], _, _, hlen, _ => by simp at hlen
  | A :: As, C, C', T, e :: es, B,
      .cons he hrest, hlen, hterminal => by
      have hlen' : es.length = As.length := by simpa using hlen
      have W := Ctx.InstN.consTel (Γ₀ := Γ) (e₀ := e) (A₀ := A) As .zero
      have hterminal₀ : env.IsDefEq U (As.reverse ++ A :: Γ) C C' T := by
        simpa [List.reverse_cons, List.append_assoc] using hterminal
      have hterminal' := hterminal₀.instN henv he W
      have hrest' : env.SpineWF U Γ
          (VExpr.forallN (VExpr.instTelN e As 0)
            (C.inst e As.length)) es B := by
        rw [VExpr.instN_forallN] at hrest
        simpa using hrest
      have hout := VEnv.SpineWF.instRev_defeq henv hrest'
        (by simpa [VExpr.instTelN_length] using hlen') hterminal'
      simpa [VExpr.instRev, hlen'] using hout

/-- Replay a saturated leading telescope from a longer application spine,
replacing the suffix-facing result by an arbitrary new codomain.  Generated
iota rules use this to retain the recursor's parameter/motive/minor prefix
while replacing its index-and-major tail with constructor fields. -/
theorem VEnv.SpineWF.prefixForallN
    {env : VEnv} {U : Nat} {Γ : List VExpr}
    {binders : List VExpr} {oldResult newResult : VExpr}
    {args suffix : List VExpr} {B : VExpr}
    (h : env.SpineWF U Γ (VExpr.forallN binders oldResult)
      (args ++ suffix) B)
    (hlen : args.length = binders.length) :
    env.SpineWF U Γ (VExpr.forallN binders newResult) args
      (VExpr.instRev newResult args) := by
  obtain ⟨_, hprefix, _⟩ := h.split
  exact hprefix.retarget hlen newResult

/-- Retain the exact suffix of a spine after consuming a saturated leading
telescope.  Unlike `SpineWF.split`, the result names the suffix cursor as the
iterated instantiation of the original codomain. -/
theorem VEnv.SpineWF.suffixForallN
    {env : VEnv} {U : Nat} {Γ : List VExpr} :
    ∀ {binders args : List VExpr} {result B : VExpr}
      {suffix : List VExpr},
      env.SpineWF U Γ (VExpr.forallN binders result)
        (args ++ suffix) B →
      args.length = binders.length →
      env.SpineWF U Γ (VExpr.instRev result args) suffix B
  | [], args, result, B, suffix, h, hlen => by
      obtain rfl : args = [] := List.length_eq_zero_iff.1 hlen
      change env.SpineWF U Γ result suffix B at h
      exact h
  | _ :: binders, [], result, B, suffix, _h, hlen => by
      simp at hlen
  | D :: binders, e :: args, result, B, suffix, h, hlen => by
      cases h with
      | cons _ hrest =>
        rw [VExpr.instN_forallN] at hrest
        have hlen' : args.length = binders.length := by simpa using hlen
        have hlen'' : args.length =
            (VExpr.instTelN e binders 0).length := by
          rw [VExpr.instTelN_length]
          exact hlen'
        have hout := VEnv.SpineWF.suffixForallN hrest hlen''
        simpa [VExpr.instRev, hlen'] using hout

/-- Assemble a generated capture spine from a saturated common prefix and a
field spine.  The source spine may continue with an unrelated suffix (for an
iota site, indices and the major premise); only its common prefix is replayed
against the new field-facing codomain. -/
theorem VEnv.SpineWF.prefixAppendForallN
    {env : VEnv} {U : Nat} {Γ : List VExpr}
    {common fields : List VExpr} {oldResult result : VExpr}
    {commonArgs suffix fieldArgs : List VExpr} {sourceResult B : VExpr}
    (hsource : env.SpineWF U Γ (VExpr.forallN common oldResult)
      (commonArgs ++ suffix) sourceResult)
    (hlen : commonArgs.length = common.length)
    (hfields : env.SpineWF U Γ
      (VExpr.instRev (VExpr.forallN fields result) commonArgs)
      fieldArgs B) :
    env.SpineWF U Γ (VExpr.forallN (common ++ fields) result)
      (commonArgs ++ fieldArgs) B := by
  rw [VExpr.forallN_append]
  exact (hsource.prefixForallN hlen).append hfields

/-- Extract the final argument typing after a saturated leading telescope.
Unlike a split through an existential cursor, this structural inversion
retains the exact iterated instantiation of the final Pi domain. -/
theorem VEnv.SpineWF.lastForallN
    {env : VEnv} {U : Nat} {Γ : List VExpr} :
    ∀ {binders args : List VExpr} {A C a B : VExpr},
      env.SpineWF U Γ (VExpr.forallN binders (.forallE A C))
        (args ++ [a]) B →
      args.length = binders.length →
      env.HasType U Γ a (VExpr.instRev A args)
  | [], args, A, C, a, B, h, hlen => by
      obtain rfl : args = [] := List.length_eq_zero_iff.1 hlen
      cases h with
      | cons ha _ => exact ha
  | _ :: binders, [], A, C, a, B, h, hlen => by simp at hlen
  | D :: binders, e :: args, A, C, a, B, h, hlen => by
      cases h with
      | cons _ hrest =>
        rw [VExpr.instN_forallN] at hrest
        have hlen' : args.length = binders.length := by simpa using hlen
        have hlen'' : args.length =
            (VExpr.instTelN e binders 0).length := by
          rw [VExpr.instTelN_length]
          exact hlen'
        have hout := VEnv.SpineWF.lastForallN hrest hlen''
        simpa [VExpr.instRev, hlen'] using hout

/-- Iterated inversion of a lambda tower's typing: the telescope is
well-formed and the body is typed under it. -/
theorem VEnv.HasType.lamN_wf {env : VEnv} {U : Nat} (henv : env.Ordered) :
    ∀ {As : List VExpr} {Γ : List VExpr} {body V : VExpr},
      OnCtx Γ (env.IsType U) →
      env.HasType U Γ (VExpr.lamN As body) V →
      VEnv.OnTel env U Γ As ∧
        ∃ T₀, env.HasType U (As.reverse ++ Γ) body T₀
  | [], Γ, body, V, _, H => ⟨trivial, V, H⟩
  | A :: As, Γ, body, V, hΓ, H => by
    obtain ⟨⟨u, hA⟩, W, hrest⟩ := VEnv.HasType.lam_inv henv hΓ H
    obtain ⟨hT, T₀, hbody⟩ :=
      VEnv.HasType.lamN_wf henv (As := As) (Γ := A :: Γ) ⟨hΓ, u, hA⟩ hrest
    exact ⟨⟨⟨u, hA⟩, hT⟩, T₀, by simpa [List.append_assoc] using hbody⟩

/-- The levels of a `HeadConstN` spine are unique. -/
theorem HeadConstN.levels_uniq {c : Name} :
    ∀ {n : Nat} {e : VExpr} {ls ls' : List VLevel},
      HeadConstN c ls n e → HeadConstN c ls' n e → ls = ls'
  | _, _, _, _, .const, .const => rfl
  | _, _, _, _, .app h, .app h' => h.levels_uniq h'

/-- Zip a well-typed spine with pointwise defeqs into a defeq spine.
Reflexive entries need no defeq evidence. -/
theorem VEnv.SpineWF.defEq_of_pointwise {env : VEnv} (henv : env.WF)
    {U : Nat} {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ {es es' : List VExpr} {F B : VExpr},
      env.SpineWF U Γ F es B →
      List.Forall₂ (fun a a' => a = a' ∨ env.IsDefEqU U Γ a a') es es' →
      VEnv.SpineDefEq env U Γ F es es' B
  | [], [], _, _, .nil, .nil => .nil
  | _ :: _, _ :: _, _, _, .cons he hrest, .cons hd htl => by
    refine .cons ?_ (hrest.defEq_of_pointwise henv hΓ htl)
    rcases hd with rfl | hd
    · exact he
    · exact VEnv.IsDefEqU.of_l henv hΓ hd he

/-- Pointwise equal saturated spines instantiate a well-typed dependent
body to definitionally equal results.  The shared telescope controls the
dependent argument types; no syntactic substitution congruence is assumed. -/
theorem VEnv.OnTel.instRev_defeq_of_spines
    {env : VEnv} (henv : env.WF) {U : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (env.IsType U))
    {As : List VExpr} (hAs : env.OnTel U Γ As)
    {body : VExpr} {u : VLevel}
    (hbody : env.HasType U (As.reverse ++ Γ) body (.sort u))
    {left right : List VExpr}
    (hleft : env.SpineWF U Γ
      (VExpr.forallN As (.sort u)) left (.sort u))
    (hright : env.SpineWF U Γ
      (VExpr.forallN As (.sort u)) right (.sort u))
    (hlen : left.length = As.length)
    (hpoint : List.Forall₂
      (fun a a' => a = a' ∨ env.IsDefEqU U Γ a a') left right) :
    env.IsDefEqU U Γ (body.instRev left) (body.instRev right) := by
  have hspine := hleft.defEq_of_pointwise henv hΓ hpoint
  have hlam := VEnv.HasType.lamN hAs hbody
  have happ := VEnv.IsDefEq.appN_defEq hlam hspine
  have hleftBeta := VEnv.IsDefEq.appN_lamN henv.ordered
    hAs hbody hleft hlen
  have hrightLen : right.length = As.length := by
    rw [← Lean4Lean.List.Forall₂.length_eq hpoint, hlen]
  have hrightBeta := VEnv.IsDefEq.appN_lamN henv.ordered
    hAs hbody hright hrightLen
  exact ⟨.sort u, hleftBeta.symm.trans (happ.trans hrightBeta)⟩

/-- Unfold the `OK` predicate through a folded list of defeq checks. -/
theorem Pattern.Check.OK.of_foldr {p : Pattern} {α : Type _}
    {df : VExpr → VExpr → Prop} {m1 : List VLevel} {m2 : p.Path → VExpr}
    (f g : α → p.RHS) :
    ∀ {xs : List α} {rest : p.Check},
      ((xs.foldr (fun x acc => Pattern.Check.defeq (f x) (g x) acc)
        rest).OK df m1 m2) →
      (∀ x ∈ xs, df ((f x).apply m1 m2) ((g x).apply m1 m2)) ∧
        rest.OK df m1 m2
  | [], _, h => ⟨nofun, h⟩
  | _ :: xs, rest, h => by
    obtain ⟨h1, h2⟩ := h
    obtain ⟨h3, h4⟩ := Pattern.Check.OK.of_foldr f g (xs := xs) h2
    refine ⟨fun x hx => ?_, h4⟩
    rcases List.mem_cons.1 hx with rfl | hx
    · exact h1
    · exact h3 x hx

/-- Build the `OK` predicate for a folded list of defeq checks from one
pointwise fact per list entry and an already-valid tail. -/
theorem Pattern.Check.OK.foldr {p : Pattern} {α : Type _}
    {df : VExpr → VExpr → Prop} {m1 : List VLevel} {m2 : p.Path → VExpr}
    (f g : α → p.RHS) :
    ∀ (xs : List α) {rest : p.Check},
      (∀ x ∈ xs, df ((f x).apply m1 m2) ((g x).apply m1 m2)) →
      rest.OK df m1 m2 →
      (xs.foldr (fun x acc => Pattern.Check.defeq (f x) (g x) acc)
        rest).OK df m1 m2
  | [], _, _, hrest => hrest
  | x :: xs, _rest, hall, hrest =>
    ⟨hall x (.head _), Pattern.Check.OK.foldr f g xs
      (fun y hy => hall y (.tail _ hy)) hrest⟩

/-- Read a pointwise relation on two mapped lists at every position selected
by the zip of their source lists. -/
private theorem forall₂_map_zip {α β : Type _}
    {R : VExpr → VExpr → Prop} (f : α → VExpr) (g : β → VExpr) :
    ∀ (xs : List α) (ys : List β),
      List.Forall₂ R (xs.map f) (ys.map g) →
      ∀ pair ∈ xs.zip ys, R (f pair.1) (g pair.2)
  | [], _, _ => by simp
  | _ :: _, [], h => by cases h
  | x :: xs, y :: ys, .cons h hrest => by
    intro pair hpair
    rcases List.mem_cons.1 hpair with rfl | hpair
    · exact h
    · exact forall₂_map_zip f g xs ys hrest pair hpair

/-- The swapped form of `forall₂_map_zip`, matching the generated index
check's `(expected index, recursor path)` zip orientation. -/
private theorem forall₂_map_zip_swap {α β : Type _}
    {R : VExpr → VExpr → Prop} (f : α → VExpr) (g : β → VExpr) :
    ∀ (xs : List α) (ys : List β),
      List.Forall₂ R (ys.map g) (xs.map f) →
      ∀ pair ∈ xs.zip ys, R (g pair.2) (f pair.1)
  | [], [], _ => by simp
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h
  | x :: xs, y :: ys, .cons h hrest => by
    intro pair hpair
    rcases List.mem_cons.1 hpair with rfl | hpair
    · exact h
    · exact forall₂_map_zip_swap f g xs ys hrest pair hpair

/-- Build a pointwise relation between two mapped lists from their zip. -/
private theorem forall₂_zip_map {α β : Type _} (F : α → VExpr) (G : β → VExpr)
    (R : VExpr → VExpr → Prop) :
    ∀ (xs : List α) (ys : List β), xs.length = ys.length →
      (∀ p ∈ xs.zip ys, R (F p.1) (G p.2)) →
      List.Forall₂ R (xs.map F) (ys.map G)
  | [], [], _, _ => .nil
  | x :: xs, y :: ys, hlen, hall =>
    .cons (hall (x, y) (.head _))
      (forall₂_zip_map F G R xs ys (by simpa using hlen)
        fun p hp => hall p (.tail _ hp))
  | [], _ :: _, hlen, _ => by simp at hlen
  | _ :: _, [], hlen, _ => by simp at hlen

/-- Universe instantiation fixes a reverse bound-variable range. -/
theorem VExpr.bvarRevRange_map_instL (ls : List VLevel) :
    ∀ (off m : Nat),
      (VExpr.bvarRevRange off m).map (VExpr.instL ls) =
        VExpr.bvarRevRange off m
  | _, 0 => rfl
  | off, m+1 => by
    simp only [VExpr.bvarRevRange, List.map_cons, VExpr.instL,
      VExpr.bvarRevRange_map_instL ls off m]

/-- A well-formed telescope extends a well-formed context. -/
theorem VEnv.OnTel.onCtx {env : VEnv} {U : Nat} :
    ∀ {As Γ : List VExpr}, OnCtx Γ (env.IsType U) →
      VEnv.OnTel env U Γ As → OnCtx (As.reverse ++ Γ) (env.IsType U)
  | [], _, hΓ, _ => hΓ
  | A :: As, Γ, hΓ, ⟨hA, hT⟩ => by
    simpa [List.append_assoc] using
      VEnv.OnTel.onCtx (As := As) (Γ := A :: Γ) ⟨hΓ, hA⟩ hT

/-- Every argument of a well-typed application spine is well-typed. -/
theorem VEnv.HasType.appN_args_wf {env : VEnv} (henv : env.WF) {U : Nat}
    {Γ : List VExpr} (hΓ : OnCtx Γ (env.IsType U)) :
    ∀ (n : Nat) (es : List VExpr), es.length = n → ∀ {f B : VExpr},
      env.HasType U Γ (VExpr.appN f es) B →
      ∀ e ∈ es, ∃ T, env.HasType U Γ e T := by
  intro n
  induction n with
  | zero =>
    intro es hlen f B H e he
    obtain rfl := List.length_eq_zero_iff.1 hlen
    cases he
  | succ n ih =>
    intro es hlen f B H e he
    have hne : es ≠ [] := by rintro rfl; simp at hlen
    obtain ⟨es', a, rfl⟩ : ∃ es' a, es = es' ++ [a] :=
      ⟨es.dropLast, es.getLast hne, (List.dropLast_concat_getLast hne).symm⟩
    rw [VExpr.appN_append] at H
    have H' : env.HasType U Γ ((VExpr.appN f es').app a) B := H
    obtain ⟨A₁, B₁, hf, ha⟩ := H'.app_inv henv hΓ
    rcases List.mem_append.1 he with he' | he'
    · exact ih es' (by simpa using hlen) hf e he'
    · obtain rfl : e = a := by simpa using he'
      exact ⟨A₁, ha⟩

/-- Iterated inversion of a pi tower's typing: the telescope is well formed
and the body is typed under it. -/
theorem VEnv.HasType.forallN_wf {env : VEnv} {U : Nat} (henv : env.Ordered) :
    ∀ {As : List VExpr} {Γ : List VExpr} {body V : VExpr},
      env.HasType U Γ (VExpr.forallN As body) V →
      VEnv.OnTel env U Γ As ∧ ∃ V', env.HasType U (As.reverse ++ Γ) body V'
  | [], _, _, V, H => ⟨trivial, V, H⟩
  | A :: As, Γ, body, V, H => by
    obtain ⟨⟨u, hA⟩, v, hB⟩ := VEnv.HasType.forallE_inv henv H
    obtain ⟨hT, V', hbody⟩ := VEnv.HasType.forallN_wf henv (As := As) hB
    exact ⟨⟨⟨u, hA⟩, hT⟩, V', by simpa [List.append_assoc] using hbody⟩

private theorem forall₂_refl_or {R : VExpr → VExpr → Prop} :
    ∀ (l : List VExpr), List.Forall₂ (fun a a' => a = a' ∨ R a a') l l
  | [] => .nil
  | _ :: l => .cons (Or.inl rfl) (forall₂_refl_or l)

private theorem forall₂_append {R : VExpr → VExpr → Prop} :
    ∀ {l₁ l₂ l₁' l₂' : List VExpr}, List.Forall₂ R l₁ l₂ →
      List.Forall₂ R l₁' l₂' → List.Forall₂ R (l₁ ++ l₁') (l₂ ++ l₂')
  | [], [], _, _, .nil, h => h
  | _ :: _, _ :: _, _, _, .cons hd htl, h => .cons hd (forall₂_append htl h)

namespace VInductDecl

namespace BlockGenerationEnv

variable {source : VInductDecl} {gen : BlockGenerationChecked source}
  {env : VEnv} (S : BlockGenerationEnv gen env)
include S

/-- At recursor universes, a generated constructor head exposes the exact
generation-parameter and field telescope and ends in its normalized owner
family application.  This transports the source-level emitted head across
the generation/checked parameter telescope equality. -/
theorem ctorConst_emitted_rec
    {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ gen.flatCtors)
    {family : NormalizedFamily}
    (hname : family.raw.name = constructor.familyName) :
    env.HasType gen.recUvars []
      (.const constructor.ctor.raw.name gen.sourceLevels)
      (VExpr.forallN
        (gen.paramsTel ++
          constructor.ctor.fieldsR source.uvars source.nparams
            gen.elimination)
        (gen.ruleCtorType constructor)) := by
  let fields := constructor.ctor.fieldsR source.uvars source.nparams
    gen.elimination
  have hchecked := (S.ctorConst_emitted_decl hconstructor).instL
    (U' := gen.recUvars) gen.sourceLevels_wf
  have hparams := S.generationParams_defeq.instL
    (U' := gen.recUvars) gen.sourceLevels_wf
  have hparams' : env.TelDefEq gen.recUvars [] gen.paramsTel
      (gen.block.checked.params.map (VExpr.instL gen.sourceLevels)) := by
    simpa [BlockGenerationChecked.paramsTel] using hparams
  have htel : env.TelDefEq gen.recUvars []
      (gen.paramsTel ++ fields)
      (gen.block.checked.params.map (VExpr.instL gen.sourceLevels) ++
        fields) := by
    exact hparams'.append_refl
      (by simpa only [List.append_nil] using
        S.generationFields_onTel_rec hconstructor)
  have happ := S.ctorApp_emitted_rec hconstructor hname
  have hctx : OnCtx (fields.reverse ++ gen.paramsTel.reverse)
      (env.IsType gen.recUvars) := by
    have hall := VEnv.OnTel.append S.paramsTel_onTel
      (by simpa [List.append_nil] using
        S.generationFields_onTel_rec hconstructor)
    simpa [fields] using
      (VEnv.OnTel.onCtx (env := env) (U := gen.recUvars)
        (As := gen.paramsTel ++ fields) (Γ := []) (by trivial) hall)
  obtain ⟨u, hterminal⟩ := happ.isType S.ord hctx
  have hterminal' : env.IsDefEq gen.recUvars
      ((gen.paramsTel ++ fields).reverse ++ [])
      (gen.ruleCtorType constructor)
      (gen.ruleCtorType constructor) (.sort u) := by
    simpa [fields, BlockGenerationChecked.ruleCtorType, hname,
      BlockGenerationChecked.ruleFieldCount, VEnv.HasType] using hterminal
  obtain ⟨_, htypes⟩ := htel.forallN_defeq hterminal'
  apply htypes.defeq'
  have hresultEq :
      (NormalizedBlockCtor.resultTarget gen constructor).instL
        gen.sourceLevels = gen.ruleCtorType constructor := by
    simp [NormalizedBlockCtor.resultTarget,
      BlockGenerationChecked.ruleCtorType,
      BlockGenerationChecked.ruleFieldCount,
      NormalizedCtor.resultIndicesR, NormalizedCtor.fieldsR_length,
      VExpr.instL_appN, List.map_append, bvarRevRange_instL, VExpr.instL,
      VLevel.params_map_inst_params']
  rw [VExpr.instL_forallN, hresultEq] at hchecked
  simpa [fields, NormalizedBlockCtor.emittedBinders,
    NormalizedCtor.fieldsR, List.map_append,
    VExpr.instL_forallN, VExpr.instL,
    VLevel.params_map_inst_params'] using hchecked

/-- A selected constructor's generated result-index arity is exactly the
index arity of its certified owner family. -/
theorem ruleIdx_length_eq_recIndexBinders
    {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ gen.flatCtors)
    {family : NormalizedFamily} (hfamily : family ∈ gen.families)
    (hindices : family.view.indices = constructor.familyIndices) :
    (gen.ruleIdx constructor).length =
      (gen.recIndexBinders family).length := by
  have hsp := S.result_transport hconstructor hfamily hindices
    [] (g := 0) rfl [] (d := 0) rfl
  have hlen := hsp.forallN_sort_length
  simpa only [BlockGenerationChecked.ruleIdx, List.length_map,
    BlockGenerationChecked.recIndexBinders,
    VExpr.liftTelN_length] using hlen

/-- Instantiate a generated recursor lookup at arbitrary runtime universe
levels and weaken it into an arbitrary local context. -/
theorem recursor_hasType_instL
    {family : NormalizedFamily} (hfamily : family ∈ gen.families)
    (hrec : env.constants (.str family.raw.name "rec") =
      some (gen.recursor family))
    {U : Nat} (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U)
    (hlen : levels.length = gen.recUvars) {Γ : List VExpr} :
    env.HasType U Γ
      (.const (.str family.raw.name "rec") levels)
      ((gen.recType family).instL levels) := by
  have h := (S.recursor_hasType hfamily hrec
    (Γ := [])).instL hlevels
  simp only [VExpr.instL, List.map_nil] at h
  rw [show gen.recLevels.map (VLevel.inst levels) = levels from
    VLevel.inst_map_id hlen] at h
  exact h.weak0 S.ord

/-- Instantiate the normalized emitted constructor-head type at arbitrary
runtime recursor levels and weaken it into an arbitrary local context. -/
theorem ctorConst_emitted_instL
    {constructor : NormalizedBlockCtor}
    (hconstructor : constructor ∈ gen.flatCtors)
    {family : NormalizedFamily}
    (hname : family.raw.name = constructor.familyName)
    {U : Nat} (levels : List VLevel)
    (hlevels : ∀ level ∈ levels, level.WF U) {Γ : List VExpr} :
    env.HasType U Γ
      (.const constructor.ctor.raw.name
        (gen.sourceLevels.map (VLevel.inst levels)))
      (VExpr.forallN
        ((gen.paramsTel ++
          constructor.ctor.fieldsR source.uvars source.nparams
            gen.elimination).map (VExpr.instL levels))
        ((gen.ruleCtorType constructor).instL levels)) := by
  have h := (S.ctorConst_emitted_rec hconstructor hname).instL hlevels
  rw [VExpr.instL_forallN] at h
  exact h.weak0 S.ord

end BlockGenerationEnv

namespace BlockGenerationChecked

variable {source : VInductDecl} (gen : source.BlockGenerationChecked)

/-! ## Named shapes of one generated rule -/

theorem rule_type (i : Nat) (c : NormalizedBlockCtor) :
    (gen.rule i c).type =
      VExpr.forallN (gen.ruleBinders c)
        (VExpr.appN
          (.bvar (gen.familyCount - 1 - c.owner + gen.minorCount +
            gen.ruleFieldCount c))
          (gen.ruleIdx c ++ [gen.ruleCtorApp c])) := rfl

theorem rule_uvars (i : Nat) (c : NormalizedBlockCtor) :
    (gen.rule i c).uvars = gen.recUvars := rfl

theorem paramsTel_length : gen.paramsTel.length = source.nparams := by
  show ((generationParams gen.block.rawParams gen.block.checked.params).map
    (VExpr.instL gen.sourceLevels)).length = _
  rw [List.length_map]
  exact (generationParams_length_of_eq gen.shape.2.1).trans gen.shape.1

theorem ruleBinders_length (c : NormalizedBlockCtor) :
    (gen.ruleBinders c).length =
      source.nparams + gen.familyCount + gen.minorCount +
        gen.ruleFieldCount c := by
  simp only [ruleBinders, List.length_append, gen.paramsTel_length,
    motiveTypes, gen.motiveTypesAux_length, minorTypes,
    gen.minorTypesAux_length, VExpr.liftTelN_length, ruleFieldCount]
  try omega

/-- Completed recursor and constructor spine arities make the canonical
capture list exactly as long as the generated rule telescope. -/
theorem ruleCaptureValues_length (c : NormalizedBlockCtor)
    {fArgs aArgs : List VExpr}
    (hMlen : fArgs.length = gen.ruleMajorArity c)
    (hNlen : aArgs.length = gen.ruleArgArity c) :
    (gen.ruleCaptureValues c fArgs aArgs).length =
      (gen.ruleBinders c).length := by
  rw [ruleCaptureValues, List.length_append, List.length_take,
    List.length_drop, hMlen, hNlen, gen.ruleBinders_length]
  simp only [ruleMajorArity, ruleArgArity]
  omega

/-- Pointwise expression transport commutes with the generator's two
canonical capture slices. -/
theorem ruleCaptureValues_map (c : NormalizedBlockCtor)
    (f : VExpr → VExpr) (fArgs aArgs : List VExpr) :
    (gen.ruleCaptureValues c fArgs aArgs).map f =
      gen.ruleCaptureValues c (fArgs.map f) (aArgs.map f) := by
  simp [ruleCaptureValues, List.map_take, List.map_drop]

/-- Canonical captures inspect only the pre-major common prefix, so first
truncating a full recursor argument list at the generated major index does
not change them. -/
theorem ruleCaptureValues_take_major (c : NormalizedBlockCtor)
    (fArgs aArgs : List VExpr) :
    gen.ruleCaptureValues c (fArgs.take (gen.ruleMajorArity c)) aArgs =
      gen.ruleCaptureValues c fArgs aArgs := by
  unfold ruleCaptureValues
  rw [List.take_take, Nat.min_eq_left]
  simp only [ruleMajorArity]
  omega

/-- The generated binder telescope is the shared parameter/motive/minor
prefix followed by the selected constructor's field telescope. -/
theorem ruleBinders_eq_common_append_fields (c : NormalizedBlockCtor) :
    gen.ruleBinders c = gen.ruleCommonBinders ++ gen.ruleFieldBinders c := by
  rfl

theorem ruleCommonBinders_length :
    gen.ruleCommonBinders.length =
      source.nparams + gen.familyCount + gen.minorCount := by
  simp only [ruleCommonBinders, List.length_append, gen.paramsTel_length,
    gen.motiveTypes_length, gen.minorTypes_length]

/-- A generated recursor type consists of the rule-common prefix followed by
the selected family's indices, major domain, and motive result. -/
theorem recType_eq_common (family : NormalizedFamily) :
    gen.recType family =
      VExpr.forallN gen.ruleCommonBinders
        (VExpr.forallN (gen.recIndexBinders family)
          (.forallE (gen.recMajorDomain family)
            (gen.recMotiveResult family))) := by
  simp only [BlockGenerationChecked.recType, ruleCommonBinders,
    recIndexBinders, recMajorDomain, recMotiveResult]
  rw [VExpr.forallN_append, VExpr.forallN_append]

/-- Universe-instantiated form of `recType_eq_common`, suitable for an exact
runtime recursor-head spine. -/
theorem recType_instL_common (family : NormalizedFamily)
    (levels : List VLevel) :
    (gen.recType family).instL levels =
      VExpr.forallN (gen.ruleCommonBinders.map (VExpr.instL levels))
        (VExpr.forallN
          ((gen.recIndexBinders family).map (VExpr.instL levels))
          (.forallE ((gen.recMajorDomain family).instL levels)
            ((gen.recMotiveResult family).instL levels))) := by
  rw [gen.recType_eq_common, VExpr.instL_forallN,
    VExpr.instL_forallN]
  rfl

/-- Saturating a generated recursor's major domain reads back the recursor
parameter slice and its explicit index suffix. -/
theorem recMajorDomain_instL_instRev
    (family : NormalizedFamily) (levels : List VLevel)
    (args : List VExpr)
    (hlen : args.length = source.nparams + gen.familyCount +
      gen.minorCount + (gen.idxTel family).length) :
    VExpr.instRev ((gen.recMajorDomain family).instL levels) args =
      VExpr.appN
        (.const family.raw.name
          (gen.sourceLevels.map (VLevel.inst levels)))
        (args.take source.nparams ++
          args.drop (source.nparams + gen.familyCount +
            gen.minorCount)) := by
  rw [BlockGenerationChecked.recMajorDomain, VExpr.instL_appN]
  simp only [VExpr.instL]
  rw [VExpr.instRev_appN]
  rw [VExpr.instRev_closedN _ (C := .const family.raw.name
    (gen.sourceLevels.map (VLevel.inst levels))) trivial]
  simp only [List.map_append]
  rw [VExpr.bvarRevRange_map_instL, VExpr.bvarRevRange_map_instL]
  rw [VExpr.map_instRev_bvarRevRange_seg _ source.nparams _ (by omega),
    VExpr.map_instRev_bvarRevRange_seg _ (gen.idxTel family).length 0
      (by omega)]
  rw [show args.length -
      ((gen.idxTel family).length + gen.familyCount + gen.minorCount) -
      source.nparams = 0 by omega, List.drop_zero]
  have hdropLen :
      (args.drop (source.nparams + gen.familyCount + gen.minorCount)).length =
        (gen.idxTel family).length := by
    rw [List.length_drop, hlen]
    omega
  rw [show args.length - 0 - (gen.idxTel family).length =
      source.nparams + gen.familyCount + gen.minorCount by omega]
  rw [List.take_of_length_le (Nat.le_of_eq hdropLen)]

/-- For an unindexed generated rule, saturating the constructor's normalized
owner-family result reads back exactly its parameter prefix. -/
theorem ruleCtorType_instL_instRev_of_unindexed
    (constructor : NormalizedBlockCtor) (levels : List VLevel)
    (args : List VExpr)
    (hidx : gen.ruleIdx constructor = [])
    (hlen : args.length = gen.ruleArgArity constructor) :
    VExpr.instRev ((gen.ruleCtorType constructor).instL levels) args =
      VExpr.appN
        (.const constructor.familyName
          (gen.sourceLevels.map (VLevel.inst levels)))
        (args.take source.nparams) := by
  have hidxRaw :
      constructor.ctor.resultIndicesR source.uvars gen.elimination = [] := by
    simpa only [BlockGenerationChecked.ruleIdx, List.map_eq_nil_iff]
      using hidx
  rw [BlockGenerationChecked.ruleCtorType, hidxRaw, List.append_nil,
    VExpr.instL_appN]
  simp only [VExpr.instL]
  rw [VExpr.instRev_appN]
  rw [VExpr.instRev_closedN _ (C := .const constructor.familyName
    (gen.sourceLevels.map (VLevel.inst levels))) trivial]
  rw [VExpr.bvarRevRange_map_instL]
  rw [VExpr.map_instRev_bvarRevRange_seg _ source.nparams _ (by
    rw [hlen]
    simp only [BlockGenerationChecked.ruleArgArity]
    omega)]
  rw [show args.length - gen.ruleFieldCount constructor - source.nparams = 0
    by
      rw [hlen]
      simp only [BlockGenerationChecked.ruleArgArity]
      omega, List.drop_zero]

/-- Universe instantiation exposes a generated rule type as its common
prefix, then its constructor-field continuation. -/
theorem rule_type_instL_split (i : Nat) (c : NormalizedBlockCtor)
    (levels : List VLevel) :
    (gen.rule i c).type.instL levels =
      VExpr.forallN
        (gen.ruleCommonBinders.map (VExpr.instL levels))
        (VExpr.forallN
          ((gen.ruleFieldBinders c).map (VExpr.instL levels))
          ((gen.ruleResult c).instL levels)) := by
  rw [gen.rule_type, gen.ruleBinders_eq_common_append_fields,
    VExpr.instL_forallN, List.map_append, VExpr.forallN_append]
  rfl

/-- Split an exact normalized constructor spine after its generated parameter
prefix.  The resulting cursor is the constructor-field telescope instantiated
by the constructor's own runtime parameters. -/
theorem ruleConstructorFieldSpine
    (constructor : NormalizedBlockCtor)
    {env : VEnv} {U : Nat} {Γ : List VExpr} {levels : List VLevel}
    {args : List VExpr}
    (hlen : args.length = gen.ruleArgArity constructor)
    {B : VExpr}
    (hspine : env.SpineWF U Γ
      (VExpr.forallN
        ((gen.paramsTel ++
          constructor.ctor.fieldsR source.uvars source.nparams
            gen.elimination).map (VExpr.instL levels))
        ((gen.ruleCtorType constructor).instL levels))
      args B) :
    env.SpineWF U Γ
      (VExpr.instRev
        (VExpr.forallN
          ((constructor.ctor.fieldsR source.uvars source.nparams
            gen.elimination).map (VExpr.instL levels))
          ((gen.ruleCtorType constructor).instL levels))
        (args.take source.nparams))
      (args.drop source.nparams) B := by
  have hparamsLen : (args.take source.nparams).length =
      (gen.paramsTel.map (VExpr.instL levels)).length := by
    rw [List.length_take, List.length_map, gen.paramsTel_length, hlen]
    simp only [BlockGenerationChecked.ruleArgArity]
    omega
  have hspine' := hspine
  rw [List.map_append, VExpr.forallN_append] at hspine'
  rw [← List.take_append_drop source.nparams args] at hspine'
  exact hspine'.suffixForallN hparamsLen

/-- A generated rule with no constructor fields has its complete field
continuation by reflexivity. -/
theorem ruleFieldSpine_of_no_fields
    (constructor : NormalizedBlockCtor)
    (hzero : gen.ruleFieldCount constructor = 0)
    {env : VEnv} {U : Nat} {Γ : List VExpr} {levels : List VLevel}
    {fArgs aArgs : List VExpr}
    (hNlen : aArgs.length = gen.ruleArgArity constructor) :
    env.SpineWF U Γ
      (VExpr.instRev
        (VExpr.forallN
          ((gen.ruleFieldBinders constructor).map (VExpr.instL levels))
          ((gen.ruleResult constructor).instL levels))
        (fArgs.take
          (source.nparams + gen.familyCount + gen.minorCount)))
      (aArgs.drop source.nparams)
      (VExpr.instRev
        (VExpr.forallN
          ((gen.ruleFieldBinders constructor).map (VExpr.instL levels))
          ((gen.ruleResult constructor).instL levels))
        (fArgs.take
          (source.nparams + gen.familyCount + gen.minorCount))) := by
  have hbinders : gen.ruleFieldBinders constructor = [] := by
    have hraw :
        constructor.ctor.fieldsR source.uvars source.nparams
          gen.elimination = [] := by
      apply List.length_eq_zero_iff.1
      simpa only [BlockGenerationChecked.ruleFieldCount] using hzero
    rw [BlockGenerationChecked.ruleFieldBinders, hraw]
    rfl
  have hargs : aArgs.drop source.nparams = [] := by
    apply List.length_eq_zero_iff.1
    rw [List.length_drop, hNlen]
    simp only [BlockGenerationChecked.ruleArgArity]
    omega
  rw [hbinders, List.map_nil, hargs]
  exact .nil

/-- Build the canonical generated-rule capture spine from a typed common
recursor prefix and the remaining constructor-field continuation.  The full
recursor spine may continue with indices, the major premise, and trailing
arguments; only the saturated common prefix is replayed. -/
theorem ruleCaptureSpine_of_prefix_fields
    {env : VEnv} {U : Nat} {Γ : List VExpr}
    (i : Nat) (c : NormalizedBlockCtor) (levels : List VLevel)
    {fArgs aArgs suffix : List VExpr}
    {oldResult sourceResult B : VExpr}
    (hMlen : fArgs.length = gen.ruleMajorArity c)
    (hsource : env.SpineWF U Γ
      (VExpr.forallN
        (gen.ruleCommonBinders.map (VExpr.instL levels)) oldResult)
      (fArgs ++ suffix) sourceResult)
    (hfields : env.SpineWF U Γ
      (VExpr.instRev
        (VExpr.forallN
          ((gen.ruleFieldBinders c).map (VExpr.instL levels))
          ((gen.ruleResult c).instL levels))
        (fArgs.take
          (source.nparams + gen.familyCount + gen.minorCount)))
      (aArgs.drop source.nparams) B) :
    env.SpineWF U Γ ((gen.rule i c).type.instL levels)
      (gen.ruleCaptureValues c fArgs aArgs) B := by
  rw [gen.rule_type_instL_split, ruleCaptureValues]
  have hsource' : env.SpineWF U Γ
      (VExpr.forallN
        (gen.ruleCommonBinders.map (VExpr.instL levels)) oldResult)
      (fArgs.take (source.nparams + gen.familyCount + gen.minorCount) ++
        (fArgs.drop (source.nparams + gen.familyCount + gen.minorCount) ++
          suffix)) sourceResult := by
    simpa only [← List.append_assoc, List.take_append_drop] using hsource
  have hcommonLength :
      (fArgs.take
        (source.nparams + gen.familyCount + gen.minorCount)).length =
        (gen.ruleCommonBinders.map (VExpr.instL levels)).length := by
    rw [List.length_take, hMlen, List.length_map,
      gen.ruleCommonBinders_length]
    simp only [ruleMajorArity]
    omega
  simpa only [VExpr.forallN_append] using
    hsource'.prefixAppendForallN hcommonLength hfields

/-- The instantiated left body as one flattened application spine. -/
theorem ruleLhsBody_instL (c : NormalizedBlockCtor) {m1 : List VLevel}
    (hlen1 : m1.length = gen.recUvars) :
    (gen.ruleLhsBody c).instL m1 =
      VExpr.appN (.const (gen.ruleRecName c) m1)
        (VExpr.bvarRevRange (gen.ruleFieldCount c)
            (source.nparams + gen.familyCount + gen.minorCount) ++
          (gen.ruleIdx c).map (VExpr.instL m1) ++
          [(gen.ruleCtorApp c).instL m1]) := by
  show (VExpr.appN
      (VExpr.appN (.const (gen.ruleRecName c) gen.recLevels)
        (VExpr.bvarRevRange (gen.ruleFieldCount c)
          (source.nparams + gen.familyCount + gen.minorCount)))
      (gen.ruleIdx c ++ [gen.ruleCtorApp c])).instL m1 = _
  rw [← VExpr.appN_append, VExpr.instL_appN]
  show VExpr.appN (.const (gen.ruleRecName c)
      (gen.recLevels.map (VLevel.inst m1))) _ = _
  rw [show gen.recLevels.map (VLevel.inst m1) = m1 from
    VLevel.inst_map_id hlen1]
  rw [List.map_append, List.map_append, VExpr.bvarRevRange_map_instL,
    List.append_assoc]
  rfl

/-- The instantiated major premise of the rule body. -/
theorem ruleCtorApp_instL (c : NormalizedBlockCtor) (m1 : List VLevel) :
    (gen.ruleCtorApp c).instL m1 =
      VExpr.appN (.const c.ctor.raw.name
          (gen.sourceLevels.map (VLevel.inst m1)))
        (VExpr.bvarRevRange
            (gen.ruleFieldCount c + (gen.familyCount + gen.minorCount))
            source.nparams ++
          VExpr.bvarRevRange 0 (gen.ruleFieldCount c)) := by
  show (VExpr.appN (.const c.ctor.raw.name gen.sourceLevels) _).instL m1 = _
  rw [VExpr.instL_appN, List.map_append, VExpr.bvarRevRange_map_instL,
    VExpr.bvarRevRange_map_instL]
  rfl

/-- The captured template values are exactly the shared prefix of the
recursor spine and the field suffix of the major premise. -/
theorem captureArgs_apply {c : NormalizedBlockCtor} {m1 : List VLevel}
    {g1 : Pattern.Path
      (Pattern.varN (.const (gen.ruleRecName c)) (gen.ruleMajorArity c)) → VExpr}
    {g2 : Pattern.Path
      (Pattern.varN (.const c.ctor.raw.name) (gen.ruleArgArity c)) → VExpr}
    {fArgs aArgs : List VExpr}
    (hg1 : (Pattern.varNPaths (.const (gen.ruleRecName c))
      (gen.ruleMajorArity c)).map g1 = fArgs)
    (hg2 : (Pattern.varNPaths (.const c.ctor.raw.name)
      (gen.ruleArgArity c)).map g2 = aArgs) :
    (gen.captureArgs c).map
      (Pattern.RHS.apply (p := (gen.rulePattern c).toPattern) m1
        (Sum.elim g1 g2)) =
      fArgs.take (source.nparams + gen.familyCount + gen.minorCount) ++
        aArgs.drop source.nparams := by
  rw [captureArgs, List.map_append, List.map_map, List.map_map]
  show List.map g1 (List.take
      (source.nparams + gen.familyCount + gen.minorCount)
      (Pattern.varNPaths (.const (gen.ruleRecName c))
        (gen.ruleMajorArity c))) ++
    List.map g2 (List.drop source.nparams
      (Pattern.varNPaths (.const c.ctor.raw.name)
        (gen.ruleArgArity c))) = _
  rw [List.map_take, List.map_drop, hg1, hg2]

/-- A matched generated RHS computes to the registered rule's right tower
applied to the canonical runtime captures.  In particular, the result is
independent of the internal pattern-path representation of the match. -/
theorem ruleRHS_apply_eq_of_match
    {i : Nat} {c : NormalizedBlockCtor} {m1 : List VLevel}
    {m2 : ((gen.rulePattern c).toPattern).Path → VExpr}
    {fArgs aArgs : List VExpr}
    (hMlen : fArgs.length = gen.ruleMajorArity c)
    (hNlen : aArgs.length = gen.ruleArgArity c)
    (hm : ((gen.rulePattern c).toPattern).Matches
      (.app (VExpr.appN (.const (gen.ruleRecName c) m1) fArgs)
        (VExpr.appN (.const c.ctor.raw.name
          (gen.sourceLevels.map (VLevel.inst m1))) aArgs)) m1 m2)
    (hcl : gen.RuleClosure) (h : gen.ruleEntry i c) :
    (gen.ruleRHS hcl h).apply m1 m2 =
      VExpr.appN ((gen.rule i c).rhs.instL m1)
        (gen.ruleCaptureValues c fArgs aArgs) := by
  cases hm with
  | @app _ _ _ g1 _ _ _ g2 hrec hctor =>
    have hg1 : (Pattern.varNPaths (.const (gen.ruleRecName c))
        (gen.ruleMajorArity c)).map g1 = fArgs :=
      Pattern.varN_matches_paths _ fArgs hrec hMlen
    have hg2 : (Pattern.varNPaths (.const c.ctor.raw.name)
        (gen.ruleArgArity c)).map g2 = aArgs :=
      Pattern.varN_matches_paths _ aArgs hctor hNlen
    rw [ruleRHS]
    simp only [Pattern.RHS.appN_apply, gen.captureArgs_apply hg1 hg2,
      ruleCaptureValues]
    rfl

/-- The generated checks are exactly the two semantic relations visible at a
runtime iota site: constructor parameters agree with recursor parameters, and
the recursor's explicit indices agree with the constructor-computed index
towers instantiated at the canonical capture spine. -/
theorem ruleCheck_ok_of_spines {c : NormalizedBlockCtor} {m1 : List VLevel}
    {m2 : ((gen.rulePattern c).toPattern).Path → VExpr}
    {fArgs aArgs : List VExpr}
    (hMlen : fArgs.length = gen.ruleMajorArity c)
    (hNlen : aArgs.length = gen.ruleArgArity c)
    (hm : ((gen.rulePattern c).toPattern).Matches
      (.app (VExpr.appN (.const (gen.ruleRecName c) m1) fArgs)
        (VExpr.appN (.const c.ctor.raw.name
          (gen.sourceLevels.map (VLevel.inst m1))) aArgs)) m1 m2)
    {df : VExpr → VExpr → Prop}
    (hparams : List.Forall₂ df
      (aArgs.take source.nparams) (fArgs.take source.nparams))
    (hindices : List.Forall₂ df
      (fArgs.drop (source.nparams + gen.familyCount + gen.minorCount))
      (gen.ruleIndexTargets c m1 fArgs aArgs))
    (hcl : gen.RuleClosure) (hc : c ∈ gen.flatCtors) :
    (gen.ruleCheck hcl hc).OK df m1 m2 := by
  cases hm with
  | @app _ _ _ g1 _ _ _ g2 hrec hctor =>
    have hg1 : (Pattern.varNPaths (.const (gen.ruleRecName c))
        (gen.ruleMajorArity c)).map g1 = fArgs :=
      Pattern.varN_matches_paths _ fArgs hrec hMlen
    have hg2 : (Pattern.varNPaths (.const c.ctor.raw.name)
        (gen.ruleArgArity c)).map g2 = aArgs :=
      Pattern.varN_matches_paths _ aArgs hctor hNlen
    have hparams' : List.Forall₂ df
        ((Pattern.varNPaths (.const c.ctor.raw.name)
          (gen.ruleArgArity c)).take source.nparams |>.map g2)
        ((Pattern.varNPaths (.const (gen.ruleRecName c))
          (gen.ruleMajorArity c)).take source.nparams |>.map g1) := by
      simpa only [List.map_take, hg1, hg2] using hparams
    have hindices' : List.Forall₂ df
        ((Pattern.varNPaths (.const (gen.ruleRecName c))
          (gen.ruleMajorArity c)).drop
            (source.nparams + gen.familyCount + gen.minorCount) |>.map g1)
        ((gen.ruleIdx c).attach.map fun index =>
          VExpr.appN
            ((VExpr.lamN (gen.ruleBinders c) index.1).instL m1)
            (gen.ruleCaptureValues c fArgs aArgs)) := by
      simpa only [List.map_drop, hg1, ruleIndexTargets] using hindices
    have hcaptures := gen.captureArgs_apply (m1 := m1) hg1 hg2
    unfold ruleCheck
    apply Pattern.Check.OK.foldr
    · intro pair hpair
      exact forall₂_map_zip _ _ _ _ hparams' pair hpair
    · apply Pattern.Check.OK.foldr
      · intro pair hpair
        have hpair' := forall₂_map_zip_swap _ _ _ _ hindices' pair hpair
        simpa only [Pattern.RHS.apply, Pattern.RHS.appN_apply, hcaptures,
          Sum.elim_inl, ruleCaptureValues] using hpair'
      · trivial

/-- An unindexed generated rule has empty explicit and computed index lists at
every completed recursor spine. -/
theorem ruleIndexTargets_aligned_of_unindexed
    {c : NormalizedBlockCtor} {m1 : List VLevel}
    {fArgs aArgs : List VExpr} {df : VExpr → VExpr → Prop}
    (hidx : gen.ruleIdx c = [])
    (hMlen : fArgs.length = gen.ruleMajorArity c) :
    List.Forall₂ df
      (fArgs.drop (source.nparams + gen.familyCount + gen.minorCount))
      (gen.ruleIndexTargets c m1 fArgs aArgs) := by
  have hidxlen : (c.ctor.resultIndicesR source.uvars gen.elimination).length = 0 := by
    have := congrArg List.length hidx
    simpa only [ruleIdx, List.length_map, List.length_nil] using this
  have hcommon : fArgs.length =
      source.nparams + gen.familyCount + gen.minorCount := by
    rw [hMlen]
    simp only [ruleMajorArity, hidxlen, Nat.add_zero]
  have hdrop : fArgs.drop
      (source.nparams + gen.familyCount + gen.minorCount) = [] := by
    apply List.length_eq_zero_iff.1
    rw [List.length_drop, hcommon]
    omega
  rw [hdrop]
  change List.Forall₂ df []
    ((gen.ruleIdx c).attach.map fun index =>
      VExpr.appN
        ((VExpr.lamN (gen.ruleBinders c) index.1).instL m1)
        (gen.ruleCaptureValues c fArgs aArgs))
  rw [hidx]
  exact .nil

/-- For an unindexed family, the generated check has no computed-index
component.  Completed spine lengths therefore reduce `Check.OK` to parameter
agreement alone. -/
theorem ruleCheck_ok_of_unindexed_spines
    {c : NormalizedBlockCtor} {m1 : List VLevel}
    {m2 : ((gen.rulePattern c).toPattern).Path → VExpr}
    {fArgs aArgs : List VExpr}
    (hidx : gen.ruleIdx c = [])
    (hMlen : fArgs.length = gen.ruleMajorArity c)
    (hNlen : aArgs.length = gen.ruleArgArity c)
    (hm : ((gen.rulePattern c).toPattern).Matches
      (.app (VExpr.appN (.const (gen.ruleRecName c) m1) fArgs)
        (VExpr.appN (.const c.ctor.raw.name
          (gen.sourceLevels.map (VLevel.inst m1))) aArgs)) m1 m2)
    {df : VExpr → VExpr → Prop}
    (hparams : List.Forall₂ df
      (aArgs.take source.nparams) (fArgs.take source.nparams))
    (hcl : gen.RuleClosure) (hc : c ∈ gen.flatCtors) :
    (gen.ruleCheck hcl hc).OK df m1 m2 := by
  apply gen.ruleCheck_ok_of_spines hMlen hNlen hm hparams
    (hcl := hcl) (hc := hc)
  exact gen.ruleIndexTargets_aligned_of_unindexed hidx hMlen

/-- Pattern soundness for one certified block (`pat_wf`): a successful match
of a rule's pattern whose checks hold is definitionally equal to the
instantiated RHS template, derived from the rule defeq registered by
`addInduct` via typed β-collapse. The redex arrives decomposed into its
recursor and constructor spines with spine-form typing, and the major
premise's levels pinned to the rule's source levels; both are exactly what
a verified reduction site holds. -/
theorem pat_wf {env : VEnv} (henv : env.WF) {univs : Nat} {Γ : List VExpr}
    (hΓ : OnCtx Γ (env.IsType univs))
    (hcl : gen.RuleClosure)
    {i : Nat} {c : NormalizedBlockCtor} (h : gen.ruleEntry i c)
    (hreg : env.defeqs (gen.rule i c))
    (hwf : (gen.rule i c).WF env)
    {m1 : List VLevel} {m2}
    (hm1 : ∀ l ∈ m1, l.WF univs) (hlen1 : m1.length = gen.recUvars)
    {fArgs aArgs : List VExpr}
    (hMlen : fArgs.length = gen.ruleMajorArity c)
    (hNlen : aArgs.length = gen.ruleArgArity c)
    (hm : ((gen.rulePattern c).toPattern).Matches
      (.app (VExpr.appN (.const (gen.ruleRecName c) m1) fArgs)
        (VExpr.appN (.const c.ctor.raw.name
          (gen.sourceLevels.map (VLevel.inst m1))) aArgs)) m1 m2)
    (hck : (gen.ruleCheck hcl (List.mem_of_getElem? h)).OK
      (env.IsDefEqU univs Γ) m1 m2)
    {Frec Ae : VExpr}
    (hehead : env.HasType univs Γ (.const (gen.ruleRecName c) m1) Frec)
    (hespine : env.SpineWF univs Γ Frec
      (fArgs ++ [VExpr.appN (.const c.ctor.raw.name
        (gen.sourceLevels.map (VLevel.inst m1))) aArgs]) Ae)
    {Fctor Actor : VExpr}
    (hctorhead : env.HasType univs Γ
      (.const c.ctor.raw.name (gen.sourceLevels.map (VLevel.inst m1))) Fctor)
    (hctorspine : env.SpineWF univs Γ Fctor aArgs Actor)
    {B : VExpr}
    (hcaps : env.SpineWF univs Γ ((gen.rule i c).type.instL m1)
      (fArgs.take (source.nparams + gen.familyCount + gen.minorCount) ++
        aArgs.drop source.nparams) B) :
    env.IsDefEqU univs Γ
      (.app (VExpr.appN (.const (gen.ruleRecName c) m1) fArgs)
        (VExpr.appN (.const c.ctor.raw.name
          (gen.sourceLevels.map (VLevel.inst m1))) aArgs))
      ((gen.ruleRHS hcl h).apply m1 m2) := by
  have henvo := henv.ordered
  have hc := List.mem_of_getElem? h
  cases hm with
  | @app _ _ _ g1 _ _ f2 g2 h1 h2 =>
  -- canonical captures
  have hg1 : (Pattern.varNPaths (.const (gen.ruleRecName c))
      (gen.ruleMajorArity c)).map g1 = fArgs :=
    Pattern.varN_matches_paths _ fArgs h1 hMlen
  have hg2 : (Pattern.varNPaths (.const c.ctor.raw.name)
      (gen.ruleArgArity c)).map g2 = aArgs :=
    Pattern.varN_matches_paths _ aArgs h2 hNlen
  have hcapsVals := gen.captureArgs_apply (m1 := m1) hg1 hg2
  -- length bookkeeping
  have hcommon_le : source.nparams + gen.familyCount + gen.minorCount ≤
      gen.ruleMajorArity c := Nat.le_add_right _ _
  have hnp_le : source.nparams ≤ gen.ruleArgArity c := Nat.le_add_right _ _
  have htakelen : (fArgs.take (source.nparams + gen.familyCount +
      gen.minorCount)).length =
      source.nparams + gen.familyCount + gen.minorCount := by
    rw [List.length_take, hMlen]; omega
  have hdroplen : (aArgs.drop source.nparams).length =
      gen.ruleFieldCount c := by
    rw [List.length_drop, hNlen]
    show gen.ruleArgArity c - source.nparams = _
    simp only [ruleArgArity]; omega
  have hcapslen : (fArgs.take (source.nparams + gen.familyCount +
      gen.minorCount) ++ aArgs.drop source.nparams).length =
      ((gen.ruleBinders c).map (VExpr.instL m1)).length := by
    rw [List.length_append, htakelen, hdroplen, List.length_map,
      gen.ruleBinders_length]
  -- tower shapes
  have htype' : (gen.rule i c).type.instL m1 =
      VExpr.forallN ((gen.ruleBinders c).map (VExpr.instL m1))
        ((VExpr.appN
          (.bvar (gen.familyCount - 1 - c.owner + gen.minorCount +
            gen.ruleFieldCount c))
          (gen.ruleIdx c ++ [gen.ruleCtorApp c])).instL m1) := by
    rw [gen.rule_type, VExpr.instL_forallN]
  have hlhs' : (gen.rule i c).lhs.instL m1 =
      VExpr.lamN ((gen.ruleBinders c).map (VExpr.instL m1))
        ((gen.ruleLhsBody c).instL m1) := by
    rw [gen.rule_lhs, VExpr.instL_lamN]
  -- tower typing at the working context
  have hlhsT : env.HasType univs Γ
      (VExpr.lamN ((gen.ruleBinders c).map (VExpr.instL m1))
        ((gen.ruleLhsBody c).instL m1))
      ((gen.rule i c).type.instL m1) := by
    rw [← hlhs']
    exact (hwf.1.instL hm1).weak0 henvo
  obtain ⟨hTel, T₀, hbody⟩ := VEnv.HasType.lamN_wf henvo hΓ hlhsT
  -- β-collapse of the applied left tower
  have hcapsF : env.SpineWF univs Γ
      (VExpr.forallN ((gen.ruleBinders c).map (VExpr.instL m1))
        ((VExpr.appN
          (.bvar (gen.familyCount - 1 - c.owner + gen.minorCount +
            gen.ruleFieldCount c))
          (gen.ruleIdx c ++ [gen.ruleCtorApp c])).instL m1))
      (fArgs.take (source.nparams + gen.familyCount + gen.minorCount) ++
        aArgs.drop source.nparams) B := htype' ▸ hcaps
  have hretT0 := (VEnv.SpineWF.retarget hcapsF hcapslen) T₀
  have hcollapseL := VEnv.IsDefEq.appN_lamN henvo hTel hbody hretT0 hcapslen
  -- the registered defeq, applied
  have hex : env.IsDefEq univs Γ ((gen.rule i c).lhs.instL m1)
      ((gen.rule i c).rhs.instL m1) ((gen.rule i c).type.instL m1) :=
    .extra hreg hm1 hlen1
  rw [hlhs'] at hex
  have happlied := VEnv.IsDefEq.appN_congr hex hcaps
  -- conclusion-side template computation
  have hRHS : Pattern.RHS.apply (p := (gen.rulePattern c).toPattern) m1
      (Sum.elim g1 g2) (gen.ruleRHS hcl h) =
      VExpr.appN ((gen.rule i c).rhs.instL m1)
        (fArgs.take (source.nparams + gen.familyCount + gen.minorCount) ++
          aArgs.drop source.nparams) := by
    rw [ruleRHS]
    simp only [Pattern.RHS.appN_apply, hcapsVals]
    rfl
  -- typing of the rule type's index spine
  obtain ⟨u₀, htypeT⟩ := hlhsT.isType henvo hΓ
  rw [htype'] at htypeT
  obtain ⟨-, V', htypeBody⟩ := VEnv.HasType.forallN_wf henvo htypeT
  have hCtxTel : OnCtx (((gen.ruleBinders c).map (VExpr.instL m1)).reverse ++ Γ)
      (env.IsType univs) := VEnv.OnTel.onCtx hΓ hTel
  rw [show ((VExpr.appN
      (.bvar (gen.familyCount - 1 - c.owner + gen.minorCount +
        gen.ruleFieldCount c))
      (gen.ruleIdx c ++ [gen.ruleCtorApp c])).instL m1) =
    VExpr.appN (.bvar (gen.familyCount - 1 - c.owner + gen.minorCount +
        gen.ruleFieldCount c))
      ((gen.ruleIdx c ++ [gen.ruleCtorApp c]).map (VExpr.instL m1)) from by
      rw [VExpr.instL_appN]; rfl] at htypeBody
  have hargsWF := VEnv.HasType.appN_args_wf henv hCtxTel _ _ rfl htypeBody
  -- check extraction
  unfold ruleCheck at hck
  obtain ⟨hparams, hidxOK⟩ := Pattern.Check.OK.of_foldr _ _ hck
  obtain ⟨hidxs, -⟩ := Pattern.Check.OK.of_foldr _ _ hidxOK
  -- per-index tower collapse and check composition
  have hidxLink : ∀ x ∈ (gen.ruleIdx c).attach.zip
      ((Pattern.varNPaths (.const (gen.ruleRecName c))
        (gen.ruleMajorArity c)).drop
        (source.nparams + gen.familyCount + gen.minorCount)),
      env.IsDefEqU univs Γ (Sum.elim g1 g2 (Sum.inl x.2))
        (VExpr.instRev (x.1.1.instL m1)
          (fArgs.take (source.nparams + gen.familyCount + gen.minorCount) ++
            aArgs.drop source.nparams)) := by
    intro x hx
    have hfact := hidxs x hx
    simp only [Pattern.RHS.appN_apply, hcapsVals] at hfact
    have htower : Pattern.RHS.apply (p := (gen.rulePattern c).toPattern) m1
        (Sum.elim g1 g2)
        (.fixed (VExpr.lamN (gen.ruleBinders c) x.1.1)
          (hcl.idxTower_closed hc x.1.1 x.1.2)) =
        VExpr.lamN ((gen.ruleBinders c).map (VExpr.instL m1))
          (x.1.1.instL m1) := by
      show (VExpr.lamN (gen.ruleBinders c) x.1.1).instL m1 = _
      rw [VExpr.instL_lamN]
    rw [htower] at hfact
    obtain ⟨Tx, hTx⟩ := hargsWF (x.1.1.instL m1)
      (by
        rw [List.map_append]
        exact List.mem_append.2 (.inl (List.mem_map_of_mem x.1.2)))
    have hretTx := (VEnv.SpineWF.retarget hcapsF hcapslen) Tx
    have hcollapseX := VEnv.IsDefEq.appN_lamN henvo hTel hTx hretTx hcapslen
    exact VEnv.IsDefEqU.trans henv hΓ hfact ⟨_, hcollapseX⟩
  -- major premise: constructor spine against its rebuilt form
  have hparamsF₂ : List.Forall₂
      (fun a a' => a = a' ∨ env.IsDefEqU univs Γ a a')
      aArgs
      (fArgs.take source.nparams ++ aArgs.drop source.nparams) := by
    have hb := forall₂_zip_map (α := Pattern.Path
        (Pattern.varN (.const c.ctor.raw.name) (gen.ruleArgArity c)))
      (β := Pattern.Path
        (Pattern.varN (.const (gen.ruleRecName c)) (gen.ruleMajorArity c)))
      g2 g1 (fun a a' => a = a' ∨ env.IsDefEqU univs Γ a a')
      ((Pattern.varNPaths (.const c.ctor.raw.name)
        (gen.ruleArgArity c)).take source.nparams)
      ((Pattern.varNPaths (.const (gen.ruleRecName c))
        (gen.ruleMajorArity c)).take source.nparams)
      (by
        rw [List.length_take, List.length_take,
          Pattern.varNPaths_length, Pattern.varNPaths_length]
        omega)
      (fun p hp => Or.inr (hparams p hp))
    rw [List.map_take, List.map_take, hg1, hg2] at hb
    have hall := forall₂_append hb
      (forall₂_refl_or (R := env.IsDefEqU univs Γ)
        (aArgs.drop source.nparams))
    rwa [List.take_append_drop] at hall
  have hmajorLink : env.IsDefEqU univs Γ
      (VExpr.appN (.const c.ctor.raw.name
        (gen.sourceLevels.map (VLevel.inst m1))) aArgs)
      (VExpr.appN (.const c.ctor.raw.name
        (gen.sourceLevels.map (VLevel.inst m1)))
        (fArgs.take source.nparams ++ aArgs.drop source.nparams)) :=
    ⟨_, VEnv.IsDefEq.appN_defEq hctorhead
      (VEnv.SpineWF.defEq_of_pointwise henv hΓ hctorspine hparamsF₂)⟩
  -- the collapsed left spine, computed
  have hL : (fArgs.take (source.nparams + gen.familyCount + gen.minorCount) ++
      aArgs.drop source.nparams).length =
      gen.ruleFieldCount c +
        (source.nparams + gen.familyCount + gen.minorCount) := by
    rw [List.length_append, htakelen, hdroplen]; omega
  have hcapsTake : (fArgs.take (source.nparams + gen.familyCount +
      gen.minorCount) ++ aArgs.drop source.nparams).take
      (source.nparams + gen.familyCount + gen.minorCount) =
      fArgs.take (source.nparams + gen.familyCount + gen.minorCount) := by
    rw [List.take_append_of_le_length (by omega : _ ≤ (fArgs.take
      (source.nparams + gen.familyCount + gen.minorCount)).length)]
    exact List.take_of_length_le (Nat.le_of_eq htakelen)
  have hcapsTakeNp : (fArgs.take (source.nparams + gen.familyCount +
      gen.minorCount) ++ aArgs.drop source.nparams).take source.nparams =
      fArgs.take source.nparams := by
    rw [List.take_append_of_le_length (by omega : _ ≤ (fArgs.take
      (source.nparams + gen.familyCount + gen.minorCount)).length)]
    rw [List.take_take]
    congr 1
    omega
  have hcapsDrop : (fArgs.take (source.nparams + gen.familyCount +
      gen.minorCount) ++ aArgs.drop source.nparams).drop
      (source.nparams + gen.familyCount + gen.minorCount) =
      aArgs.drop source.nparams := by
    have hdl := List.drop_left (l₁ := fArgs.take (source.nparams + gen.familyCount + gen.minorCount)) (l₂ := aArgs.drop source.nparams)
    rwa [htakelen] at hdl
  have hsegNp : (VExpr.bvarRevRange
      (gen.ruleFieldCount c + (gen.familyCount + gen.minorCount))
      source.nparams).map (VExpr.instRev ·
        (fArgs.take (source.nparams + gen.familyCount + gen.minorCount) ++
          aArgs.drop source.nparams)) = fArgs.take source.nparams := by
    rw [VExpr.map_instRev_bvarRevRange_seg _ source.nparams _ (by omega)]
    rw [show (fArgs.take (source.nparams + gen.familyCount +
        gen.minorCount) ++ aArgs.drop source.nparams).length -
        (gen.ruleFieldCount c + (gen.familyCount + gen.minorCount)) -
        source.nparams = 0 from by omega, List.drop_zero]
    exact hcapsTakeNp
  have hsegFld : (VExpr.bvarRevRange 0 (gen.ruleFieldCount c)).map
      (VExpr.instRev ·
        (fArgs.take (source.nparams + gen.familyCount + gen.minorCount) ++
          aArgs.drop source.nparams)) = aArgs.drop source.nparams := by
    rw [VExpr.map_instRev_bvarRevRange_seg _ (gen.ruleFieldCount c) 0
      (by omega)]
    rw [show (fArgs.take (source.nparams + gen.familyCount +
        gen.minorCount) ++ aArgs.drop source.nparams).length - 0 -
        gen.ruleFieldCount c =
        source.nparams + gen.familyCount + gen.minorCount from by omega]
    rw [hcapsDrop]
    exact List.take_of_length_le (Nat.le_of_eq hdroplen)
  have hsegCommon : (VExpr.bvarRevRange (gen.ruleFieldCount c)
      (source.nparams + gen.familyCount + gen.minorCount)).map
      (VExpr.instRev ·
        (fArgs.take (source.nparams + gen.familyCount + gen.minorCount) ++
          aArgs.drop source.nparams)) =
      fArgs.take (source.nparams + gen.familyCount + gen.minorCount) := by
    rw [VExpr.map_instRev_bvarRevRange_seg _
      (source.nparams + gen.familyCount + gen.minorCount)
      (gen.ruleFieldCount c) (by omega)]
    rw [show (fArgs.take (source.nparams + gen.familyCount +
        gen.minorCount) ++ aArgs.drop source.nparams).length -
        gen.ruleFieldCount c -
        (source.nparams + gen.familyCount + gen.minorCount) = 0 from by
        omega, List.drop_zero]
    exact hcapsTake
  have hctorImg : VExpr.instRev ((gen.ruleCtorApp c).instL m1)
      (fArgs.take (source.nparams + gen.familyCount + gen.minorCount) ++
        aArgs.drop source.nparams) =
      VExpr.appN (.const c.ctor.raw.name
          (gen.sourceLevels.map (VLevel.inst m1)))
        (fArgs.take source.nparams ++ aArgs.drop source.nparams) := by
    rw [gen.ruleCtorApp_instL, VExpr.instRev_appN,
      VExpr.instRev_closedN (C := .const c.ctor.raw.name
        (gen.sourceLevels.map (VLevel.inst m1))) _ trivial, List.map_append,
      hsegNp, hsegFld]
  have hcollapsedEq : VExpr.instRev ((gen.ruleLhsBody c).instL m1)
      (fArgs.take (source.nparams + gen.familyCount + gen.minorCount) ++
        aArgs.drop source.nparams) =
      VExpr.appN (.const (gen.ruleRecName c) m1)
        (fArgs.take (source.nparams + gen.familyCount + gen.minorCount) ++
          ((gen.ruleIdx c).map (fun x => VExpr.instRev (x.instL m1)
            (fArgs.take (source.nparams + gen.familyCount +
              gen.minorCount) ++ aArgs.drop source.nparams)) ++
          [VExpr.appN (.const c.ctor.raw.name
              (gen.sourceLevels.map (VLevel.inst m1)))
            (fArgs.take source.nparams ++ aArgs.drop source.nparams)])) := by
    rw [gen.ruleLhsBody_instL c hlen1, VExpr.instRev_appN,
      VExpr.instRev_closedN (C := .const (gen.ruleRecName c) m1) _ trivial,
      List.map_append, List.map_append, hsegCommon, List.map_map]
    rw [show ((gen.ruleCtorApp c).instL m1 ::
        ([] : List VExpr)).map (VExpr.instRev ·
          (fArgs.take (source.nparams + gen.familyCount +
            gen.minorCount) ++ aArgs.drop source.nparams)) =
        [VExpr.instRev ((gen.ruleCtorApp c).instL m1)
          (fArgs.take (source.nparams + gen.familyCount +
            gen.minorCount) ++ aArgs.drop source.nparams)] from rfl]
    rw [hctorImg]
    simp only [Function.comp_def]
    rw [List.append_assoc]
  -- pointwise defeq between the redex spine and the collapsed spine
  have hidxF₂ : List.Forall₂ (fun a a' => a = a' ∨ env.IsDefEqU univs Γ a a')
      (fArgs.drop (source.nparams + gen.familyCount + gen.minorCount))
      ((gen.ruleIdx c).map (fun x => VExpr.instRev (x.instL m1)
        (fArgs.take (source.nparams + gen.familyCount + gen.minorCount) ++
          aArgs.drop source.nparams))) := by
    have hb := forall₂_zip_map
      (α := {x // x ∈ gen.ruleIdx c})
      (β := Pattern.Path (Pattern.varN (.const (gen.ruleRecName c))
        (gen.ruleMajorArity c)))
      (fun s => VExpr.instRev (s.1.instL m1)
        (fArgs.take (source.nparams + gen.familyCount + gen.minorCount) ++
          aArgs.drop source.nparams))
      (fun p => Sum.elim g1 g2 (Sum.inl p))
      (fun t v => v = t ∨ env.IsDefEqU univs Γ v t)
      (gen.ruleIdx c).attach
      ((Pattern.varNPaths (.const (gen.ruleRecName c))
        (gen.ruleMajorArity c)).drop
        (source.nparams + gen.familyCount + gen.minorCount))
      (by
        rw [List.length_attach, List.length_drop, Pattern.varNPaths_length]
        show (gen.ruleIdx c).length = gen.ruleMajorArity c - _
        simp only [ruleIdx, ruleMajorArity, List.length_map]
        omega)
      (fun p hp => Or.inr (hidxLink p hp))
    have hflip := List.Forall₂.flip hb
    have hmapG : ((Pattern.varNPaths (.const (gen.ruleRecName c))
        (gen.ruleMajorArity c)).drop
        (source.nparams + gen.familyCount + gen.minorCount)).map
        (fun p => Sum.elim g1 g2 (Sum.inl p)) =
        fArgs.drop (source.nparams + gen.familyCount + gen.minorCount) := by
      show ((Pattern.varNPaths (.const (gen.ruleRecName c))
        (gen.ruleMajorArity c)).drop
        (source.nparams + gen.familyCount + gen.minorCount)).map g1 = _
      rw [List.map_drop, hg1]
    have hmapF : ((gen.ruleIdx c).attach).map
        (fun s => VExpr.instRev (s.1.instL m1)
          (fArgs.take (source.nparams + gen.familyCount + gen.minorCount) ++
            aArgs.drop source.nparams)) =
        (gen.ruleIdx c).map (fun x => VExpr.instRev (x.instL m1)
          (fArgs.take (source.nparams + gen.familyCount + gen.minorCount) ++
            aArgs.drop source.nparams)) := by
      exact List.attach_map_val
        (f := fun x : VExpr => VExpr.instRev (x.instL m1)
          (fArgs.take (source.nparams + gen.familyCount + gen.minorCount) ++
            aArgs.drop source.nparams)) ..
    rw [hmapG, hmapF] at hflip
    exact hflip
  have hbigF₂ : List.Forall₂ (fun a a' => a = a' ∨ env.IsDefEqU univs Γ a a')
      (fArgs ++ [VExpr.appN (.const c.ctor.raw.name
        (gen.sourceLevels.map (VLevel.inst m1))) aArgs])
      (fArgs.take (source.nparams + gen.familyCount + gen.minorCount) ++
        ((gen.ruleIdx c).map (fun x => VExpr.instRev (x.instL m1)
          (fArgs.take (source.nparams + gen.familyCount + gen.minorCount) ++
            aArgs.drop source.nparams)) ++
        [VExpr.appN (.const c.ctor.raw.name
            (gen.sourceLevels.map (VLevel.inst m1)))
          (fArgs.take source.nparams ++ aArgs.drop source.nparams)])) := by
    have hres := forall₂_append
      (forall₂_refl_or (R := env.IsDefEqU univs Γ)
        (fArgs.take (source.nparams + gen.familyCount + gen.minorCount)))
      (forall₂_append hidxF₂ (.cons (Or.inr hmajorLink) .nil))
    rwa [← List.append_assoc, List.take_append_drop] at hres
  -- the redex is defeq to the collapsed left spine
  have hE := VEnv.IsDefEq.appN_defEq hehead
    (VEnv.SpineWF.defEq_of_pointwise henv hΓ hespine hbigF₂)
  rw [← hcollapsedEq, VExpr.appN_append] at hE
  -- assemble
  rw [hRHS]
  exact VEnv.IsDefEqU.trans henv hΓ ⟨_, hE⟩
    (VEnv.IsDefEqU.trans henv hΓ ⟨_, hcollapseL.symm⟩ ⟨_, happlied⟩)

end BlockGenerationChecked

end VInductDecl

end Lean4Lean

/-! ## Axiom closures

The typed β-collapse layer is sorry-free. `pat_wf` composes typed defeqs
through `IsDefEqU.of_l`/`IsDefEqU.trans` and therefore carries exactly the
transitional unique-typing closure the Church–Rosser development itself
carries; it sheds `sorryAx` automatically when the L4L-16/17 inversion
milestones land, with no restatement. -/

/-- info: 'Lean4Lean.VEnv.IsDefEq.appN_lamN' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VEnv.IsDefEq.appN_lamN

/-- info: 'Lean4Lean.VEnv.IsDefEq.appN_defEq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Lean4Lean.VEnv.IsDefEq.appN_defEq

/-- info: 'Lean4Lean.VEnv.SpineWF.prefixForallN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VEnv.SpineWF.prefixForallN

/-- info: 'Lean4Lean.VEnv.SpineWF.suffixForallN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VEnv.SpineWF.suffixForallN

/-- info: 'Lean4Lean.VEnv.OnTel.weakR' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VEnv.OnTel.weakR

/-- info: 'Lean4Lean.VEnv.TelDefEq.of_forallN_sort_defeq' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VEnv.TelDefEq.of_forallN_sort_defeq

/-- info: 'Lean4Lean.VEnv.TelDefEq.of_forallN_defeq_of_length' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VEnv.TelDefEq.of_forallN_defeq_of_length

/-- info: 'Lean4Lean.VEnv.OnTel.telDefEq_instDF' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VEnv.OnTel.telDefEq_instDF

/-- info: 'Lean4Lean.VEnv.SpineWF.prefixAppendForallN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VEnv.SpineWF.prefixAppendForallN

/-- info: 'Lean4Lean.VEnv.SpineWF.lastForallN' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VEnv.SpineWF.lastForallN

/-- info: 'Lean4Lean.VInductDecl.BlockGenerationEnv.ctorConst_emitted_rec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockGenerationEnv.ctorConst_emitted_rec

/-- info: 'Lean4Lean.VInductDecl.BlockGenerationEnv.ruleIdx_length_eq_recIndexBinders' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockGenerationEnv.ruleIdx_length_eq_recIndexBinders

/--
info: 'Lean4Lean.VInductDecl.BlockGenerationEnv.recursor_hasType_instL' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockGenerationEnv.recursor_hasType_instL

/-- info: 'Lean4Lean.VInductDecl.BlockGenerationEnv.ctorConst_emitted_instL' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockGenerationEnv.ctorConst_emitted_instL

/--
info: 'Lean4Lean.VInductDecl.BlockGenerationChecked.ruleBinders_eq_common_append_fields' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockGenerationChecked.ruleBinders_eq_common_append_fields

/-- info: 'Lean4Lean.VInductDecl.BlockGenerationChecked.ruleCaptureValues_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockGenerationChecked.ruleCaptureValues_length

/-- info: 'Lean4Lean.VInductDecl.BlockGenerationChecked.ruleCaptureValues_map' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockGenerationChecked.ruleCaptureValues_map

/-- info: 'Lean4Lean.VInductDecl.BlockGenerationChecked.ruleCaptureValues_take_major' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockGenerationChecked.ruleCaptureValues_take_major

/-- info: 'Lean4Lean.VInductDecl.BlockGenerationChecked.ruleCommonBinders_length' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockGenerationChecked.ruleCommonBinders_length

/-- info: 'Lean4Lean.VInductDecl.BlockGenerationChecked.recType_eq_common' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockGenerationChecked.recType_eq_common

/-- info: 'Lean4Lean.VInductDecl.BlockGenerationChecked.recType_instL_common' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockGenerationChecked.recType_instL_common

/-- info: 'Lean4Lean.VInductDecl.BlockGenerationChecked.recMajorDomain_instL_instRev' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockGenerationChecked.recMajorDomain_instL_instRev

/--
info: 'Lean4Lean.VInductDecl.BlockGenerationChecked.ruleCtorType_instL_instRev_of_unindexed' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockGenerationChecked.ruleCtorType_instL_instRev_of_unindexed

/-- info: 'Lean4Lean.VInductDecl.BlockGenerationChecked.rule_type_instL_split' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockGenerationChecked.rule_type_instL_split

/--
info: 'Lean4Lean.VInductDecl.BlockGenerationChecked.ruleConstructorFieldSpine' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockGenerationChecked.ruleConstructorFieldSpine

/-- info: 'Lean4Lean.VInductDecl.BlockGenerationChecked.ruleFieldSpine_of_no_fields' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockGenerationChecked.ruleFieldSpine_of_no_fields

/--
info: 'Lean4Lean.VInductDecl.BlockGenerationChecked.ruleCaptureSpine_of_prefix_fields' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockGenerationChecked.ruleCaptureSpine_of_prefix_fields

/-- info: 'Lean4Lean.VEnv.LE.extra' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Lean4Lean.VEnv.LE.extra

/-- info: 'Lean4Lean.VEnv.LE.extra_appN' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Lean4Lean.VEnv.LE.extra_appN

/-- info: 'Lean4Lean.VEnv.LE.extra_appN_symm' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Lean4Lean.VEnv.LE.extra_appN_symm

/-- info: 'Lean4Lean.Pattern.varN_matches_paths' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.Pattern.varN_matches_paths

/-- info: 'Lean4Lean.Pattern.Check.OK.foldr' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Lean4Lean.Pattern.Check.OK.foldr

/-- info: 'Lean4Lean.VInductDecl.BlockGenerationChecked.captureArgs_apply' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockGenerationChecked.captureArgs_apply

/--
info: 'Lean4Lean.VInductDecl.BlockGenerationChecked.ruleCheck_ok_of_spines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockGenerationChecked.ruleCheck_ok_of_spines

/--
info: 'Lean4Lean.VInductDecl.BlockGenerationChecked.ruleRHS_apply_eq_of_match' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockGenerationChecked.ruleRHS_apply_eq_of_match

/--
info: 'Lean4Lean.VInductDecl.BlockGenerationChecked.ruleIndexTargets_aligned_of_unindexed' depends on axioms: [propext,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockGenerationChecked.ruleIndexTargets_aligned_of_unindexed

/--
info: 'Lean4Lean.VInductDecl.BlockGenerationChecked.ruleCheck_ok_of_unindexed_spines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockGenerationChecked.ruleCheck_ok_of_unindexed_spines

/--
info: 'Lean4Lean.VInductDecl.BlockGenerationChecked.pat_wf' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockGenerationChecked.pat_wf
