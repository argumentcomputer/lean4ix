import Lean4Lean.Theory.Typing.InductivePatternWF

/-! # The block-local pattern environment assembler

`assembleEnv` builds an environment whose defeq set consists of exactly one
certified block's generated iota rules plus separately certified extension
rules over a defeq-free constant base. The exposed helpers are the ones
Church–Rosser instantiation and downstream consumers need:

* `assembleEnv_defeqs` inverts the assembled defeq set exactly: a registered
  defeq is a generated rule, an extension, or a base defeq — nothing else.
* `assembleEnv_WF` preserves ordering through the block phases and the
  extension fold, given the block's semantic package and each extension's
  well-formedness.
* `AssembledPat` is the union pattern set. The block half carries the full
  L4L-10A obligations and `pat_wf`; the extension half carries each
  certificate's own pattern payload. `CertifiedExtension.covers` records
  the match at the beta-collapsed body of a registered lambda tower, never
  at the closed tower itself. No open-environment `Params` instance is
  installed. -/

namespace Lean4Lean

namespace VExpr

/-- Remove the leading lambda tower from an expression.  This is the
syntactic point at which first-order reduction patterns are matched; a
closed lambda tower itself is deliberately not a `Pattern`. -/
def stripLams : VExpr → VExpr
  | .lam _ body => stripLams body
  | e => e

@[simp] theorem stripLams_lamN (binders : List VExpr) (body : VExpr) :
    stripLams (lamN binders body) = stripLams body := by
  induction binders with
  | nil => rfl
  | cons _ binders ih => exact ih

/-- Universe instantiation commutes with exposing the body of a lambda
tower. -/
theorem stripLams_instL (e : VExpr) (ls : List VLevel) :
    stripLams (e.instL ls) = (stripLams e).instL ls := by
  induction e with
  | lam _ _ _ ih => exact ih
  | _ => rfl

end VExpr

/-! ## Pattern shape helpers and head separation

Side-condition-free shape facts about `Pattern.inter`, `Subpattern`, and
constant towers, followed by the head inventory of a `SimplePattern` and the
two separation predicates the union-level non-overlap laws consume.
`HeadSep.inter_subpattern_none` is the cross-term engine: under head
separation one simple pattern's pattern intersects no subpattern of the
other's.  `HeadSep.app_l_uniq` and `HeadSep.app_uniq` are its two `app`-level
companions, exported because a fixture whose `Params` spans several blocks
must discharge its cross-block cases from them by hand. -/

namespace Pattern

/-- An application pattern never meets a bare constant. -/
theorem app_inter_const {f a : Pattern} {c : Name} :
    (Pattern.app f a).inter (.const c) = none := rfl

/-- A bare constant never meets an application pattern. -/
theorem const_inter_app {f a : Pattern} {c : Name} :
    (Pattern.const c).inter (.app f a) = none := rfl

/-- A bare constant never meets a `.var` pattern. -/
theorem const_inter_var {f : Pattern} {c : Name} :
    (Pattern.const c).inter (.var f) = none := rfl

/-- Distinct bare constants never meet. -/
theorem const_inter_const_of_ne {c c' : Name} (h : c ≠ c') :
    (Pattern.const c).inter (.const c') = none := by
  simp [Pattern.inter, h]

/-- A bare constant meets a constant tower only at height zero with the
same name. -/
theorem const_inter_varN_of_ne {c c' : Name} (h : c ≠ c') :
    ∀ j, (Pattern.const c).inter (Pattern.varN (.const c') j) = none
  | 0 => const_inter_const_of_ne h
  | _+1 => const_inter_var

end Pattern

/-- The only subpattern of a bare constant pattern is itself. -/
theorem Subpattern.const_inv {p : Pattern} {c : Name}
    (H : Subpattern p (.const c)) : p = .const c := by
  cases H; rfl

/-- A `.var`-shaped subpattern of a constant tower is a strictly shorter
tower. -/
theorem Subpattern.var_varN_const_le {c : Name} {M : Nat} {q : Pattern}
    (h : Subpattern (.var q) (Pattern.varN (.const c) M)) :
    ∃ j, j + 1 ≤ M ∧ q = Pattern.varN (.const c) j := by
  obtain ⟨j, hj, heq⟩ := h.varN_const_le
  cases j with
  | zero => exact absurd heq (by simp [Pattern.varN])
  | succ j'' =>
    rw [show Pattern.varN (.const c) (j'' + 1) =
        .var (Pattern.varN (.const c) j'') from rfl] at heq
    injection heq with heq'
    exact ⟨j'', hj, heq'⟩

namespace SimplePattern

/-- The defined-symbol head of a simple pattern: the unfolded constant of a
`defn` rule, the recursor of an `iota` rule. -/
def symbHead : SimplePattern → Name
  | .defn h => h
  | .iota r _ _ _ => r

/-- The constructor head of an `iota` rule's major premise. -/
def ctorHead? : SimplePattern → Option Name
  | .defn _ => none
  | .iota _ _ c _ => some c

@[simp] theorem symbHead_defn {h : Name} : symbHead (.defn h) = h := rfl
@[simp] theorem symbHead_iota {r c : Name} {m n : Nat} :
    symbHead (.iota r m c n) = r := rfl
@[simp] theorem ctorHead?_defn {h : Name} : ctorHead? (.defn h) = none := rfl
@[simp] theorem ctorHead?_iota {r c : Name} {m n : Nat} :
    ctorHead? (.iota r m c n) = some c := rfl

/-- Internal head-distinctness of one simple pattern: an `iota` rule's
recursor head is not its constructor head.  Block rules get this from
`recName_ne_ctorName`; a certified extension must supply it. -/
def SelfSeparated : SimplePattern → Prop
  | .defn _ => True
  | .iota r _ c _ => r ≠ c

/-- Head separation between two simple patterns: symb heads differ, and
each side's symb head differs from the other side's constructor head.
Constructor-vs-constructor collisions are deliberately NOT excluded — they
never produce an intersection. -/
structure HeadSep (sp sp' : SimplePattern) : Prop where
  symb_ne_symb : sp.symbHead ≠ sp'.symbHead
  symb_ne_ctor : ∀ c' ∈ sp'.ctorHead?, sp.symbHead ≠ c'
  ctor_ne_symb : ∀ c ∈ sp.ctorHead?, c ≠ sp'.symbHead

/-- Head separation is symmetric. -/
theorem HeadSep.symm {sp sp' : SimplePattern} (h : HeadSep sp sp') :
    HeadSep sp' sp where
  symb_ne_symb := h.symb_ne_symb.symm
  symb_ne_ctor := fun c hc => (h.ctor_ne_symb c hc).symm
  ctor_ne_symb := fun c' hc' => (h.symb_ne_ctor c' hc').symm

/-- Constructor form for two iota patterns from the three required name
disequalities. -/
theorem HeadSep.iota_iota {r c r' c' : Name} {m n m' n' : Nat}
    (h1 : r ≠ r') (h2 : r ≠ c') (h3 : c ≠ r') :
    HeadSep (.iota r m c n) (.iota r' m' c' n') where
  symb_ne_symb := h1
  symb_ne_ctor := fun x hx => by cases hx; exact h2
  ctor_ne_symb := fun x hx => by cases hx; exact h3

/-- The cross-term engine: under head separation, `sp'`'s pattern
intersects NO subpattern of `sp`'s pattern.  This is the single new
combinatorial fact the union-level laws need. -/
theorem HeadSep.inter_subpattern_none {sp sp' : SimplePattern}
    (hsep : sp.HeadSep sp') {p₃ : Pattern}
    (hsub : Subpattern p₃ sp.toPattern) :
    sp'.toPattern.inter p₃ = none := by
  cases sp with
  | defn h =>
    obtain rfl := Subpattern.const_inv hsub
    cases sp' with
    | defn h' => exact Pattern.const_inter_const_of_ne hsep.symb_ne_symb.symm
    | iota r' m' c' n' => exact Pattern.app_inter_const
  | iota r m c n =>
    have hcs : c ≠ sp'.symbHead := hsep.ctor_ne_symb c rfl
    rcases RecursorIotaPattern.subpattern_inv hsub with
      rfl | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · -- p₃ is the whole iota pattern
      cases sp' with
      | defn h' => exact Pattern.const_inter_app
      | iota r' m' c' n' =>
        cases e : (SimplePattern.iota r' m' c' n').toPattern.inter
            (RecursorIotaPattern r m c n) with
        | none => rfl
        | some q =>
          exact absurd (RecursorIotaPattern.inter_some e).1.symm
            hsep.symb_ne_symb
    · -- p₃ is a tower of the recursor head r
      cases sp' with
      | defn h' =>
        exact Pattern.const_inter_varN_of_ne hsep.symb_ne_symb.symm j
      | iota r' m' c' n' =>
        cases e : (SimplePattern.iota r' m' c' n').toPattern.inter
            (Pattern.varN (.const r) j) with
        | none => rfl
        | some q =>
          exact absurd (RecursorIotaPattern.inter_varN_const_some e).1
            hsep.symb_ne_symb
    · -- p₃ is a tower of the constructor head c
      cases sp' with
      | defn h' => exact Pattern.const_inter_varN_of_ne hcs.symm j
      | iota r' m' c' n' =>
        cases e : (SimplePattern.iota r' m' c' n').toPattern.inter
            (Pattern.varN (.const c) j) with
        | none => rfl
        | some q =>
          exact absurd (RecursorIotaPattern.inter_varN_const_some e).1 hcs

/-- Self-overlap engine: any self-intersecting subpattern of a
self-separated simple pattern is the whole pattern. -/
theorem SelfSeparated.subpattern_inter_eq {sp : SimplePattern}
    (hself : sp.SelfSeparated) {p₃ p₄ : Pattern}
    (hsub : Subpattern p₃ sp.toPattern)
    (hint : sp.toPattern.inter p₃ = some p₄) :
    p₃ = sp.toPattern := by
  cases sp with
  | defn h => exact Subpattern.const_inv hsub
  | iota r m c n =>
    rcases RecursorIotaPattern.subpattern_inv hsub with
      rfl | ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · rfl
    · obtain ⟨-, h2⟩ := RecursorIotaPattern.inter_varN_const_some hint
      exact absurd h2 (by omega)
    · exact absurd (RecursorIotaPattern.inter_varN_const_some hint).1.symm
        hself

/-- `pat_app_l` is side-condition-free for ANY simple pattern. -/
theorem toPattern_app_l {sp : SimplePattern} {p₁ p₂ p₃ p₄ : Pattern}
    (h : Subpattern (.app p₁ p₂) sp.toPattern) :
    ¬Subpattern (.app p₃ p₄) p₁ := by
  cases sp with
  | defn head =>
    intro _
    exact absurd (Subpattern.const_inv h) (by simp)
  | iota r m c n =>
    obtain ⟨rfl, -⟩ := RecursorIotaPattern.app_subpattern h
    intro hsub
    obtain ⟨j', -, heq'⟩ := hsub.varN_const_le
    cases j' <;> exact absurd heq' (by simp [Pattern.varN])

/-- The `pat_app_l_uniq` shape fact for two head-separated simple patterns:
`sp'`'s left spine never meets a `.var` subpattern of `sp`'s left spine,
because head separation keeps the two recursor towers' names apart.  The
union law `AssembledPat.pat_app_l_uniq` is this lemma at every mixed pair;
a `Params` spanning several blocks calls it directly for the cross-block
pairs. -/
theorem HeadSep.app_l_uniq {sp sp' : SimplePattern}
    {p₁ p₂ p₁' p₂' p₃ : Pattern} (hsep : sp.HeadSep sp')
    (h : Subpattern (.app p₁ p₂) sp.toPattern)
    (h' : Subpattern (.app p₁' p₂') sp'.toPattern)
    (h₃ : Subpattern (.var p₃) p₁) : p₁'.inter p₃ = none := by
  cases sp with
  | defn head => exact absurd (Subpattern.const_inv h) (by simp)
  | iota R M C N =>
    obtain ⟨rfl, -⟩ := RecursorIotaPattern.app_subpattern h
    obtain ⟨j, -, rfl⟩ := Subpattern.var_varN_const_le h₃
    cases sp' with
    | defn head' => exact absurd (Subpattern.const_inv h') (by simp)
    | iota R' M' C' N' =>
      obtain ⟨rfl, -⟩ := RecursorIotaPattern.app_subpattern h'
      exact Pattern.varN_const_inter_of_ne_name hsep.symb_ne_symb.symm _ _

/-- The `pat_app_uniq` shape fact for two head-separated simple patterns: a
subpattern of `sp`'s left spine never meets a subpattern of `sp'`'s right
spine, because head separation keeps `sp`'s symb head apart from `sp'`'s
constructor head.  Companion of `HeadSep.app_l_uniq`, with the same role in
`AssembledPat.pat_app_uniq` and in multi-block fixtures. -/
theorem HeadSep.app_uniq {sp sp' : SimplePattern}
    {p₁ p₂ p₁' p₂' p₃ p₃' : Pattern} (hsep : sp.HeadSep sp')
    (h : Subpattern (.app p₁ p₂) sp.toPattern)
    (h' : Subpattern (.app p₁' p₂') sp'.toPattern)
    (h₃ : Subpattern p₃ p₁) (h₃' : Subpattern p₃' p₂') :
    p₃.inter p₃' = none := by
  cases sp with
  | defn head => exact absurd (Subpattern.const_inv h) (by simp)
  | iota R M C N =>
    obtain ⟨rfl, -⟩ := RecursorIotaPattern.app_subpattern h
    obtain ⟨j, -, rfl⟩ := h₃.varN_const_le
    cases sp' with
    | defn head' => exact absurd (Subpattern.const_inv h') (by simp)
    | iota R' M' C' N' =>
      obtain ⟨-, rfl⟩ := RecursorIotaPattern.app_subpattern h'
      obtain ⟨j', -, rfl⟩ := h₃'.varN_const_le
      exact Pattern.varN_const_inter_of_ne_name (hsep.symb_ne_ctor C' rfl) _ _

end SimplePattern

namespace VInductDecl

/-- One separately certified extension rule for an assembled environment:
its registered defeq, a simple pattern, and the pattern payload. Coverage is
stated at `VExpr.stripLams (df.lhs.instL ls)`, the beta-collapsed pattern
site, rather than at `df.lhs.instL ls`, which is generally a closed lambda
tower. Check obligations and the typed equality from the matched redex to
the RHS are discharged by the consumer at the reduction site and are
carried by `ParRed.extra`; this certificate does not make either fact true
by registration alone. -/
structure CertifiedExtension where
  df : VDefEq
  pat : SimplePattern
  rhs : (pat.toPattern).RHS
  check : (pat.toPattern).Check
  covers : ∀ (ls : List VLevel), ls.length = df.uvars →
    ∃ m1 m2, (pat.toPattern).Matches
      (VExpr.stripLams (df.lhs.instL ls)) m1 m2

namespace CertifiedExtension

/-- The first-order pattern exposed by the body of `quotDefEq`: five
arguments to `Quot.lift`, followed by a three-argument `Quot.mk` major. -/
def quotPattern : SimplePattern :=
  .iota ``Quot.lift 5 ``Quot.mk 3

private def quotRecPaths :=
  Pattern.varNPaths (.const ``Quot.lift) 5

private def quotCtorPaths :=
  Pattern.varNPaths (.const ``Quot.mk) 3

/-- The six arguments of the registered quotient tower: all five lift
arguments followed by the quotient representative. -/
def quotCaptureArgs : List (quotPattern.toPattern.RHS) :=
  quotRecPaths.map (fun path => .var (.inl path)) ++
    (quotCtorPaths.drop 2).map (fun path => .var (.inr path))

/-- The registered right tower applied to the captures selected by the
collapsed quotient pattern. -/
def quotRHS : quotPattern.toPattern.RHS :=
  Pattern.RHS.appN (.fixed quotDefEq.rhs (by decide)) quotCaptureArgs

/-- The constructor-side `α` and relation arguments must agree with the
corresponding `Quot.lift` arguments. -/
def quotCheck : quotPattern.toPattern.Check :=
  ((quotCtorPaths.take 2).zip (quotRecPaths.take 2)).foldr
    (fun paths rest => .defeq (.var (.inr paths.1))
      (.var (.inl paths.2)) rest) .true

/-- Exact non-lambda body of the registered quotient equation. -/
def quotLhsBody : VExpr :=
  .app
    (VExpr.appN (.const ``Quot.lift [.param 0, .param 1])
      [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 1])
    (VExpr.appN (.const ``Quot.mk [.param 0])
      [.bvar 5, .bvar 4, .bvar 0])

theorem quotDefEq_lhsBody :
    VExpr.stripLams quotDefEq.lhs = quotLhsBody := rfl

/-- `quotDefEq` satisfies the same beta-collapsed registration contract as
generated iota rules.  This is a kernel proof of pattern coverage, not a
project axiom and not an operational equality oracle. -/
def quot : CertifiedExtension where
  df := quotDefEq
  pat := quotPattern
  rhs := quotRHS
  check := quotCheck
  covers := by
    intro ls hlen
    have hlen' : ls.length = 2 := by simpa [quotDefEq] using hlen
    have hlevels : [.param 0, .param 1].map (VLevel.inst ls) = ls :=
      VLevel.inst_map_id hlen'
    let mkLevels := [.param 0].map (VLevel.inst ls)
    have hleft : HeadConstN ``Quot.lift ls 5
        (VExpr.appN (.const ``Quot.lift ls)
          [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 1]) := by
      have h0 : HeadConstN ``Quot.lift ls 0 (.const ``Quot.lift ls) := .const
      simpa using h0.appN
        [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 1]
    have hright : HeadConstN ``Quot.mk mkLevels 3
        (VExpr.appN (.const ``Quot.mk mkLevels)
          [.bvar 5, .bvar 4, .bvar 0]) := by
      have h0 : HeadConstN ``Quot.mk mkLevels 0 (.const ``Quot.mk mkLevels) := .const
      simpa using h0.appN [.bvar 5, .bvar 4, .bvar 0]
    obtain ⟨m2, hm⟩ := RecursorIotaPattern.matches_of hleft hright
    refine ⟨ls, m2, ?_⟩
    rw [VExpr.stripLams_instL, quotDefEq_lhsBody]
    have hbody : quotLhsBody.instL ls =
        .app
          (VExpr.appN (.const ``Quot.lift ls)
            [.bvar 5, .bvar 4, .bvar 3, .bvar 2, .bvar 1])
          (VExpr.appN (.const ``Quot.mk mkLevels)
            [.bvar 5, .bvar 4, .bvar 0]) := by
      simp [quotLhsBody, VExpr.instL, VExpr.instL_appN, hlevels, mkLevels]
    rw [hbody]
    exact hm

end CertifiedExtension

namespace BlockGenerationChecked

variable {source : VInductDecl} (gen : source.BlockGenerationChecked)

/-- Every generated iota rule satisfies the beta-collapsed extension shape.
The witness is derived from the generated rule body and is independent of
the rule's semantic soundness proof (`pat_wf`). -/
def iotaExtension (hcl : gen.RuleClosure) {i : Nat}
    {constructor : NormalizedBlockCtor} (h : gen.ruleEntry i constructor) :
    CertifiedExtension where
  df := gen.rule i constructor
  pat := gen.rulePattern constructor
  rhs := gen.ruleRHS hcl h
  check := gen.ruleCheck hcl (List.mem_of_getElem? h)
  covers := by
    intro ls hlen
    obtain ⟨m2, hm⟩ := gen.ruleLhsBody_matches constructor
    have hm := hm.instL ls
    have hlevels : gen.recLevels.map (VLevel.inst ls) = ls :=
      VLevel.inst_map_id (hlen.trans (gen.rule_uvars i constructor))
    rw [hlevels] at hm
    refine ⟨ls, (fun x => (m2 x).instL ls), ?_⟩
    rw [gen.rule_lhs, VExpr.instL_lamN, VExpr.stripLams_lamN]
    have hbody : gen.ruleLhsBody constructor =
        .app (VExpr.appN
          (gen.recBase (gen.ruleFieldCount constructor) constructor.owner)
          (gen.ruleIdx constructor)) (gen.ruleCtorApp constructor) := by
      rw [ruleLhsBody, VExpr.appN_append]
      rfl
    have hstrip : VExpr.stripLams ((gen.ruleLhsBody constructor).instL ls) =
        (gen.ruleLhsBody constructor).instL ls := by
      rw [hbody]
      rfl
    rw [hstrip]
    exact hm

/-- The assembled block-local environment: dependency constants from the
base, the block's four insertion phases, and the certified extension
defeqs. -/
def assembleEnv (base : VEnv) (exts : List CertifiedExtension) :
    Option VEnv := do
  let env ← base.addInductBlockGeneration gen
  return exts.foldl (fun env ext => env.addDefEq ext.df) env

/-! ## Defeq-set inversion -/

private theorem addConst_defeqs {env env' : VEnv} {n : Name} {ci : VConstant}
    (h : env.addConst n ci = some env') {df : VDefEq} :
    env'.defeqs df ↔ env.defeqs df := by
  unfold VEnv.addConst at h
  split at h
  · cases h
  · cases h
    exact Iff.rfl

private theorem foldlM_addConst_defeqs {α : Type _} (name : α → Name)
    (ci : α → VConstant) :
    ∀ (xs : List α) {env env' : VEnv},
      xs.foldlM (fun env x => env.addConst (name x) (ci x)) env = some env' →
      ∀ {df : VDefEq}, (env'.defeqs df ↔ env.defeqs df)
  | [], env, env', h, df => by cases h; exact Iff.rfl
  | x :: xs, env, env', h, df => by
    rw [List.foldlM_cons] at h
    rcases Option.bind_eq_some_iff.1 h with ⟨envx, hx, hrest⟩
    exact (foldlM_addConst_defeqs name ci xs hrest).trans (addConst_defeqs hx)

private theorem foldl_addDefEq_defeqs :
    ∀ (dfs : List VDefEq) (env : VEnv) (df : VDefEq),
      ((dfs.foldl VEnv.addDefEq env).defeqs df ↔ df ∈ dfs ∨ env.defeqs df)
  | [], env, df => by simp
  | d :: dfs, env, df => by
    rw [List.foldl_cons, foldl_addDefEq_defeqs dfs (env.addDefEq d) df]
    show _ ∨ (df = d ∨ _) ↔ _
    rw [List.mem_cons]
    constructor
    · rintro (h | h | h)
      · exact .inl (.inr h)
      · exact .inl (.inl h)
      · exact .inr h
    · rintro ((h | h) | h)
      · exact .inr (.inl h)
      · exact .inl h
      · exact .inr (.inr h)

/-- Registered defeqs of a completed block transaction are exactly the
generated rules over the base's. -/
theorem addInductBlockGeneration_defeqs {base env₁ : VEnv}
    (hadd : base.addInductBlockGeneration gen = some env₁) (df : VDefEq) :
    env₁.defeqs df ↔ df ∈ gen.generatedRules ∨ base.defeqs df := by
  rcases VEnv.addInductBlockGeneration_trace hadd with ⟨H⟩
  rw [← H.addRules, foldl_addDefEq_defeqs]
  refine or_congr Iff.rfl ?_
  exact ((foldlM_addConst_defeqs _ _ _ H.addRecs).trans
    ((foldlM_addConst_defeqs _ _ _ H.addCtors).trans
      (foldlM_addConst_defeqs _ _ _ H.addTypes)))

/-- The assembled defeq set, inverted exactly. -/
theorem assembleEnv_defeqs {base env' : VEnv}
    {exts : List CertifiedExtension}
    (hadd : gen.assembleEnv base exts = some env') (df : VDefEq) :
    env'.defeqs df ↔
      df ∈ gen.generatedRules ∨ (∃ ext ∈ exts, df = ext.df) ∨
        base.defeqs df := by
  unfold assembleEnv at hadd
  rcases Option.bind_eq_some_iff.1 hadd with ⟨env₁, h₁, h₂⟩
  cases Option.some.inj h₂
  have hfold : ∀ (es : List CertifiedExtension) (env : VEnv),
      ((es.foldl (fun env ext => env.addDefEq ext.df) env).defeqs df ↔
        (∃ ext ∈ es, df = ext.df) ∨ env.defeqs df) := by
    intro es
    induction es with
    | nil => intro env; simp
    | cons e es ih =>
      intro env
      rw [List.foldl_cons, ih (env.addDefEq e.df)]
      show _ ∨ (df = e.df ∨ _) ↔ _
      constructor
      · rintro (⟨ext, hm, rfl⟩ | rfl | hbase)
        · exact .inl ⟨ext, .tail _ hm, rfl⟩
        · exact .inl ⟨e, .head _, rfl⟩
        · exact .inr hbase
      · rintro (⟨ext, hm, rfl⟩ | hbase)
        · rcases List.mem_cons.1 hm with rfl | hm
          · exact .inr (.inl rfl)
          · exact .inl ⟨ext, hm, rfl⟩
        · exact .inr (.inr hbase)
  rw [hfold, gen.addInductBlockGeneration_defeqs h₁]
  constructor
  · rintro (h | h | h)
    · exact .inr (.inl h)
    · exact .inl h
    · exact .inr (.inr h)
  · rintro (h | h | h)
    · exact .inr (.inl h)
    · exact .inl h
    · exact .inr (.inr h)

/-- A defeq-free base makes the assembled defeq set exactly the generated
rules plus the certified extensions. -/
theorem assembleEnv_defeq_cases {base env' : VEnv}
    {exts : List CertifiedExtension}
    (hadd : gen.assembleEnv base exts = some env')
    (hbase : ∀ df, ¬base.defeqs df) {df : VDefEq}
    (hdf : env'.defeqs df) :
    df ∈ gen.generatedRules ∨ ∃ ext ∈ exts, df = ext.df := by
  rcases (gen.assembleEnv_defeqs hadd df).1 hdf with h | h | h
  · exact .inl h
  · exact .inr h
  · exact absurd h (hbase df)

/-! ## Ordering -/

/-- The assembled environment is ordered: the block transaction preserves
ordering through its four phases, and each certified extension is well
formed over the post-block environment. -/
theorem assembleEnv_WF {base : VEnv} (henv : base.Ordered)
    {blockEnv : VEnv} (hgen : gen.WF base blockEnv)
    {exts : List CertifiedExtension} {env₁ : VEnv}
    (hadd₁ : base.addInductBlockGeneration gen = some env₁)
    (hexts : ∀ ext ∈ exts, ext.df.WF env₁) :
    ∃ env', gen.assembleEnv base exts = some env' ∧ env'.Ordered := by
  refine ⟨exts.foldl (fun env ext => env.addDefEq ext.df) env₁, ?_, ?_⟩
  · unfold assembleEnv
    rw [hadd₁]
    rfl
  · have hord₁ : env₁.Ordered :=
      VEnv.addInductBlockGeneration_WF henv hgen hadd₁
    have hmap : exts.foldl (fun env ext => env.addDefEq ext.df) env₁ =
        (exts.map (·.df)).foldl VEnv.addDefEq env₁ := by
      rw [List.foldl_map]
    rw [hmap]
    exact VInductDecl.rulesFold_WF _ hord₁
      (fun df hdf => by
        rcases List.mem_map.1 hdf with ⟨ext, hm, rfl⟩
        exact hexts ext hm)

/-! ## The union pattern set -/

/-- The assembled pattern set: the block's iota patterns with their L4L-10A
payloads, plus each certified extension's pattern payload. -/
inductive AssembledPat (hcl : gen.RuleClosure)
    (exts : List CertifiedExtension) :
    (p : Pattern) → p.RHS × p.Check → Prop where
  | rule {p : Pattern} {r : p.RHS × p.Check} :
      gen.IotaPat hcl p r → AssembledPat hcl exts p r
  | ext (ext : CertifiedExtension) (hmem : ext ∈ exts) :
      AssembledPat hcl exts (ext.pat.toPattern) (ext.rhs, ext.check)

/-- `Params.pat_simple` for the assembled set. -/
theorem AssembledPat.pat_simple {hcl : gen.RuleClosure}
    {exts : List CertifiedExtension} {p : Pattern} {r : p.RHS × p.Check}
    (H : gen.AssembledPat hcl exts p r) :
    ∃ sp : SimplePattern, p = sp.toPattern := by
  cases H with
  | rule h => exact h.pat_simple
  | ext ext hmem => exact ⟨ext.pat, rfl⟩

/-- Inversion for the assembled set, the `AssembledPat` counterpart of
`IotaPat.recover`: an assembled pattern is either a block rule at a
recoverable flattened position or one of the certified extensions, with its
payload recovered up to `HEq` in both cases.  A consumer needs this because
`cases` cannot destructure `AssembledPat` at a *concrete* iota pattern —
the block half's index `(gen.rulePattern constructor).toPattern` is a stuck
`varN` tower, so dependent elimination fails — whereas this lemma's
conclusion is index-free and applies at any `p`. -/
theorem AssembledPat.recover {hcl : gen.RuleClosure}
    {exts : List CertifiedExtension} {p : Pattern} {r : p.RHS × p.Check}
    (H : gen.AssembledPat hcl exts p r) :
    (∃ (i : Nat) (constructor : NormalizedBlockCtor)
        (h : gen.ruleEntry i constructor),
        p = (gen.rulePattern constructor).toPattern ∧
          r ≍ (gen.ruleRHS hcl h,
            gen.ruleCheck hcl (List.mem_of_getElem? h))) ∨
      (∃ ext ∈ exts, p = ext.pat.toPattern ∧ r ≍ (ext.rhs, ext.check)) := by
  cases H with
  | rule h =>
    cases h with
    | @mk i constructor hentry =>
      exact .inl ⟨i, constructor, hentry, rfl, HEq.rfl⟩
  | ext ext hmem => exact .inr ⟨ext, hmem, rfl, HEq.rfl⟩

/-- Extension defeqs of the assembled set expose their pattern at the
beta-collapsed body of the registered lambda tower. -/
theorem AssembledPat.ext_covers {hcl : gen.RuleClosure}
    {exts : List CertifiedExtension} {ext : CertifiedExtension}
    (hmem : ext ∈ exts) {ls : List VLevel} (hls : ls.length = ext.df.uvars) :
    ∃ p r m1 m2, gen.AssembledPat hcl exts p r ∧
      p.Matches (VExpr.stripLams (ext.df.lhs.instL ls)) m1 m2 := by
  obtain ⟨m1, m2, hmatch⟩ := ext.covers ls hls
  exact ⟨ext.pat.toPattern, (ext.rhs, ext.check), m1, m2,
    .ext ext hmem, hmatch⟩

/-! ## Union-level non-overlap

The four block-local `IotaPat` non-overlap laws lift to the assembled
union exactly under a head-freshness certificate for the extension list;
`separation_is_necessary` below pins that the naive statements are
false. -/

/-- The head-freshness certificate a fixture must supply for its extension
list.  This is the corrected hypothesis inventory: without it the union
laws below are false (see `separation_is_necessary`). -/
structure ExtSeparation (exts : List CertifiedExtension) : Prop where
  self_sep : ∀ ext ∈ exts, ext.pat.SelfSeparated
  block_sep : ∀ ext ∈ exts, ∀ ⦃constructor : NormalizedBlockCtor⦄,
    constructor ∈ gen.flatCtors →
      ext.pat.HeadSep (gen.rulePattern constructor)
  ext_uniq : ∀ ext₁ ∈ exts, ∀ ext₂ ∈ exts,
    ext₁.pat = ext₂.pat → ext₁ = ext₂
  ext_sep : ∀ ext₁ ∈ exts, ∀ ext₂ ∈ exts,
    ext₁.pat ≠ ext₂.pat → ext₁.pat.HeadSep ext₂.pat

/-! ### Scope: one `AssembledPat` covers exactly one block

`ExtSeparation.ext_sep` demands pairwise `HeadSep` between any two
extensions with distinct patterns, and `HeadSep.symb_ne_symb` requires their
symb heads to differ.  Two iota rules of the *same* block share a recursor
name, so `symb_ne_symb` is false for them and no `ExtSeparation` can list
them together: the extension list is not a place to park a second block's
rules.  Covering a whole block at once is the job of the block half of
`AssembledPat`, and that half is fixed to the single `gen` the certificate
carries — every mutually inductive type of one `VInductDecl` transaction,
and nothing else.  Intra-block non-overlap is settled by `IotaPat`'s
constructor-name injectivity rather than by head separation, which is
exactly why the block half needs no `HeadSep` among its own rules.

So a fixture whose `Params` must range over two or more blocks does not
enlarge one `AssembledPat`.  It takes the N-way sum of the per-block pattern
sets — one `AssembledPat` per block, each with its own `gen`, `RuleClosure`,
and extension list — and hand-writes the cross-block cases of the four
non-overlap obligations, N(N-1) ordered pairs of blocks per obligation.
Those cases are mechanical.  Reduce each side to its `SimplePattern`
inventory (`AssembledPat.pat_simple`, plus a per-fixture lemma naming the
finitely many patterns a block contributes), prove `HeadSep` once for every
cross-block pair of simple patterns — `decide` on the names suffices — and
then apply `SimplePattern.HeadSep.inter_subpattern_none` for `pat_uniq`,
`SimplePattern.HeadSep.app_l_uniq` for `pat_app_l_uniq`, and
`SimplePattern.HeadSep.app_uniq` for `pat_app_uniq`.  `pat_app_l` needs no
separation at all: it follows from `pat_simple` and
`SimplePattern.toPattern_app_l` uniformly across blocks. -/

/-- `Params.pat_uniq` for the assembled union, under `ExtSeparation`; the
(rule, rule) case delegates to `IotaPat.pat_uniq`. -/
theorem AssembledPat.pat_uniq {hcl : gen.RuleClosure}
    {exts : List CertifiedExtension} (hsep : gen.ExtSeparation exts)
    {p₁ p₂ p₃ p₄ : Pattern} {r : p₁.RHS × p₁.Check} {r' : p₂.RHS × p₂.Check}
    (H1 : gen.AssembledPat hcl exts p₁ r)
    (H2 : gen.AssembledPat hcl exts p₂ r')
    (H3 : Subpattern p₃ p₁) (H4 : p₂.inter p₃ = some p₄) :
    p₁ = p₂ ∧ p₂ = p₃ ∧ r ≍ r' := by
  cases H1 with
  | rule h1 =>
    cases H2 with
    | rule h2 => exact IotaPat.pat_uniq gen h1 h2 H3 H4
    | ext ext2 hm2 =>
      cases h1 with | @mk i c hentry =>
      rw [((hsep.block_sep ext2 hm2
        (List.mem_of_getElem? hentry)).symm).inter_subpattern_none H3] at H4
      cases H4
  | ext ext1 hm1 =>
    cases H2 with
    | rule h2 =>
      cases h2 with | @mk i c hentry =>
      rw [(hsep.block_sep ext1 hm1
        (List.mem_of_getElem? hentry)).inter_subpattern_none H3] at H4
      cases H4
    | ext ext2 hm2 =>
      rcases Decidable.em (ext1.pat = ext2.pat) with hpq | hpq
      · obtain rfl := hsep.ext_uniq ext1 hm1 ext2 hm2 hpq
        exact ⟨rfl,
          ((hsep.self_sep ext1 hm1).subpattern_inter_eq H3 H4).symm, HEq.rfl⟩
      · rw [(hsep.ext_sep ext1 hm1 ext2 hm2 hpq).inter_subpattern_none H3]
          at H4
        cases H4

/-- `Params.pat_app_l` for the assembled union — no separation needed:
every assembled pattern is simple, and simple patterns are `app`-flat on
the left. -/
theorem AssembledPat.pat_app_l {hcl : gen.RuleClosure}
    {exts : List CertifiedExtension}
    {p : Pattern} {r : p.RHS × p.Check} {p₁ p₂ p₃ p₄ : Pattern}
    (H : gen.AssembledPat hcl exts p r) (h : Subpattern (.app p₁ p₂) p) :
    ¬Subpattern (.app p₃ p₄) p₁ := by
  obtain ⟨sp, rfl⟩ := H.pat_simple
  exact SimplePattern.toPattern_app_l h

/-- `Params.pat_app_l_uniq` for the assembled union, under
`ExtSeparation`; the (rule, rule) case delegates to
`IotaPat.pat_app_l_uniq`. -/
theorem AssembledPat.pat_app_l_uniq {hcl : gen.RuleClosure}
    {exts : List CertifiedExtension} (hsep : gen.ExtSeparation exts)
    {p p' : Pattern} {r : p.RHS × p.Check} {r' : p'.RHS × p'.Check}
    {p₁ p₂ p₁' p₂' p₃ : Pattern}
    (H : gen.AssembledPat hcl exts p r)
    (H' : gen.AssembledPat hcl exts p' r')
    (h : Subpattern (.app p₁ p₂) p) (h' : Subpattern (.app p₁' p₂') p')
    (h₃ : Subpattern (.var p₃) p₁) : p₁'.inter p₃ = none := by
  cases H with
  | rule h1 =>
    cases H' with
    | rule h2 => exact IotaPat.pat_app_l_uniq gen h1 h2 h h' h₃
    | ext ext2 hm2 =>
      cases h1 with | @mk i c hentry =>
      exact ((hsep.block_sep ext2 hm2
        (List.mem_of_getElem? hentry)).symm).app_l_uniq h h' h₃
  | ext ext1 hm1 =>
    cases H' with
    | rule h2 =>
      cases h2 with | @mk i c hentry =>
      exact (hsep.block_sep ext1 hm1
        (List.mem_of_getElem? hentry)).app_l_uniq h h' h₃
    | ext ext2 hm2 =>
      rcases Decidable.em (ext1.pat = ext2.pat) with hpq | hpq
      · -- Equal patterns: separation cannot apply, but the two towers then
        -- differ in arity, `h₃` being a strictly shorter left spine.
        cases hsp1 : ext1.pat with
        | defn hd =>
          rw [hsp1] at h
          exact absurd (Subpattern.const_inv h) (by simp)
        | iota R1 M1 C1 N1 =>
          rw [hsp1] at h
          obtain ⟨rfl, -⟩ := RecursorIotaPattern.app_subpattern h
          obtain ⟨j, hj, rfl⟩ := Subpattern.var_varN_const_le h₃
          rw [← hpq, hsp1] at h'
          obtain ⟨rfl, -⟩ := RecursorIotaPattern.app_subpattern h'
          exact Pattern.varN_const_inter_of_ne_arity (by omega) _ _
      · exact (hsep.ext_sep ext1 hm1 ext2 hm2 hpq).app_l_uniq h h' h₃

/-- `Params.pat_app_uniq` for the assembled union, under `ExtSeparation`;
the (rule, rule) case delegates to `IotaPat.pat_app_uniq`. -/
theorem AssembledPat.pat_app_uniq {hcl : gen.RuleClosure}
    {exts : List CertifiedExtension} (hsep : gen.ExtSeparation exts)
    {p p' : Pattern} {r : p.RHS × p.Check} {r' : p'.RHS × p'.Check}
    {p₁ p₂ p₁' p₂' p₃ p₃' : Pattern}
    (H : gen.AssembledPat hcl exts p r)
    (H' : gen.AssembledPat hcl exts p' r')
    (h : Subpattern (.app p₁ p₂) p) (h' : Subpattern (.app p₁' p₂') p')
    (h₃ : Subpattern p₃ p₁) (h₃' : Subpattern p₃' p₂') :
    p₃.inter p₃' = none := by
  cases H with
  | rule h1 =>
    cases H' with
    | rule h2 => exact IotaPat.pat_app_uniq gen h1 h2 h h' h₃ h₃'
    | ext ext2 hm2 =>
      cases h1 with | @mk i c hentry =>
      exact ((hsep.block_sep ext2 hm2
        (List.mem_of_getElem? hentry)).symm).app_uniq h h' h₃ h₃'
  | ext ext1 hm1 =>
    cases H' with
    | rule h2 =>
      cases h2 with | @mk i c hentry =>
      exact (hsep.block_sep ext1 hm1
        (List.mem_of_getElem? hentry)).app_uniq h h' h₃ h₃'
    | ext ext2 hm2 =>
      rcases Decidable.em (ext1.pat = ext2.pat) with hpq | hpq
      · -- Equal patterns: separation cannot apply, but `SelfSeparated` keeps
        -- the shared pattern's own two heads apart.
        cases hsp1 : ext1.pat with
        | defn hd =>
          rw [hsp1] at h
          exact absurd (Subpattern.const_inv h) (by simp)
        | iota R1 M1 C1 N1 =>
          rw [hsp1] at h
          obtain ⟨rfl, -⟩ := RecursorIotaPattern.app_subpattern h
          obtain ⟨j, -, rfl⟩ := h₃.varN_const_le
          rw [← hpq, hsp1] at h'
          obtain ⟨-, rfl⟩ := RecursorIotaPattern.app_subpattern h'
          obtain ⟨j', -, rfl⟩ := h₃'.varN_const_le
          have hself := hsep.self_sep ext1 hm1
          rw [hsp1] at hself
          exact Pattern.varN_const_inter_of_ne_name hself _ _
      · exact (hsep.ext_sep ext1 hm1 ext2 hm2 hpq).app_uniq h h' h₃ h₃'

end BlockGenerationChecked

end VInductDecl

/-! ## Necessity of the separation hypotheses

If a defn extension's head equals a block rule's recursor name `R`, the
extension's bare-constant pattern intersects the height-0 subtower of the
rule pattern while the two patterns differ — so the naive union `pat_uniq`
(whose conclusion forces the patterns equal) is false.  The same collision
breaks the naive statement for any head in the block inventory. -/

/-- Refutes the certificate-free union `pat_uniq`: a `defn` extension named
after a rule's recursor meets a proper subpattern of the rule pattern while
the two patterns differ. -/
theorem separation_is_necessary (R C : Name) :
    Subpattern (.const R) ((SimplePattern.iota R 6 C 3).toPattern) ∧
      ((SimplePattern.defn R).toPattern).inter (.const R) =
        some (.const R) ∧
      (SimplePattern.iota R 6 C 3).toPattern ≠
        (SimplePattern.defn R).toPattern := by
  refine ⟨Subpattern.appL (Subpattern.varN .refl), by simp [Pattern.inter],
    fun h => absurd h (by simp [SimplePattern.toPattern])⟩

end Lean4Lean

/-! ## Axiom closures -/

/-- info: 'Lean4Lean.Pattern.Matches.instL' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.Pattern.Matches.instL

/-- info: 'Lean4Lean.VInductDecl.CertifiedExtension.quot' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.CertifiedExtension.quot

/-- info: 'Lean4Lean.VInductDecl.BlockGenerationChecked.iotaExtension' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockGenerationChecked.iotaExtension

/-- info: 'Lean4Lean.VInductDecl.BlockGenerationChecked.assembleEnv_defeqs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockGenerationChecked.assembleEnv_defeqs

/-- info: 'Lean4Lean.VInductDecl.BlockGenerationChecked.assembleEnv_WF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockGenerationChecked.assembleEnv_WF

/-- info: 'Lean4Lean.VInductDecl.BlockGenerationChecked.AssembledPat.pat_simple' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockGenerationChecked.AssembledPat.pat_simple

/-- info: 'Lean4Lean.VInductDecl.BlockGenerationChecked.AssembledPat.recover' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockGenerationChecked.AssembledPat.recover

/-- info: 'Lean4Lean.VInductDecl.BlockGenerationChecked.AssembledPat.ext_covers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockGenerationChecked.AssembledPat.ext_covers

/-- info: 'Lean4Lean.SimplePattern.HeadSep.inter_subpattern_none' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.SimplePattern.HeadSep.inter_subpattern_none

/-- info: 'Lean4Lean.SimplePattern.HeadSep.app_l_uniq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.SimplePattern.HeadSep.app_l_uniq

/-- info: 'Lean4Lean.SimplePattern.HeadSep.app_uniq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.SimplePattern.HeadSep.app_uniq

/--
info: 'Lean4Lean.VInductDecl.BlockGenerationChecked.AssembledPat.pat_uniq' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockGenerationChecked.AssembledPat.pat_uniq

/-- info: 'Lean4Lean.VInductDecl.BlockGenerationChecked.AssembledPat.pat_app_l' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockGenerationChecked.AssembledPat.pat_app_l

/-- info: 'Lean4Lean.VInductDecl.BlockGenerationChecked.AssembledPat.pat_app_l_uniq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockGenerationChecked.AssembledPat.pat_app_l_uniq

/-- info: 'Lean4Lean.VInductDecl.BlockGenerationChecked.AssembledPat.pat_app_uniq' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockGenerationChecked.AssembledPat.pat_app_uniq

/-- info: 'Lean4Lean.separation_is_necessary' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.separation_is_necessary
