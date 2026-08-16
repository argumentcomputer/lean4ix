import Lean4Lean.Experimental.SExpr

/-!
# L4L-16 R1: generic syntax transport between `Params` instances

`SExpr` retains its complete `Params` value as an inductive parameter, so a
declaration-history induction cannot keep one syntax type across rungs.  D0
and D1 each hand-roll a four-way transport functor
(`natToD0Expr`/`d0ToNatExpr`, `d0ToD1Expr`/`d1ToD0Expr`) together with its
roundtrip and commutation lemmas — about 1200 lines of per-rung boilerplate.
Everything in that layer depends only on the two instances agreeing on
`univs`, so it is provable once, generically.  This module is that generic
layer, promoted from the banked probe
(`plans/probes/probeG-generic-instance.lean` §G1).

Contents: `transportLevel`/`transportExpr` (the functor), the constructor
congruence simp set, both roundtrips, level-operator commutation
(`succ`/`imax`/`instV`), substitution transport (`lift'`, `subst`, `inst`,
`mkInst`), pattern payload commutation (`applyS`, `defeqsS`), syntactic
match transport (`MatchesS`), context lookup transport, and the
context/level-list roundtrips.

Deliberately *not* here: judgment transport (`IsDefEq`, `IsDefEqStrong`,
`Pattern.Action`).  Those consume per-rung facts — environment inclusion,
`Pat` inclusion, classifier agreement — and stay with the rung that owns
them (`d0StrongToD1`, `d1StrongToD2`, …).  Refactoring D0/D1 onto this
module is a recorded follow-up; this module is additive.
-/

namespace Lean4Lean
namespace SExpr

variable {P₀ P₁ : Params}

/-! ## The transport functor -/

/-- Level transport between any two instances agreeing on `univs`.  The
carrier of `SLevel` is `Params`-independent; only the well-formedness
witness moves. -/
def transportLevel (h : @Params.univs P₀ = @Params.univs P₁)
    (l : @SLevel P₀) : @SLevel P₁ :=
  ⟨l.1, by
    obtain ⟨u, hu, heval⟩ := l.2
    exact ⟨u, h ▸ hu, heval⟩⟩

/-- Expression transport, by the `SExpr` recursor. -/
noncomputable def transportExpr (h : @Params.univs P₀ = @Params.univs P₁)
    (e : @SExpr P₀) : @SExpr P₁ :=
  @SExpr.rec P₀ (motive := fun _ => @SExpr P₁)
    (fun i => @SExpr.bvar P₁ i)
    (fun u => @SExpr.sort P₁ (transportLevel h u))
    (fun c ls => @SExpr.const P₁ c (ls.map (transportLevel h)))
    (fun _ _ f a => @SExpr.app P₁ f a)
    (fun _ _ A body => @SExpr.lam P₁ A body)
    (fun _ _ A B => @SExpr.forallE P₁ A B)
    e

/-! ## Roundtrips -/

@[simp] theorem transportLevel_transportLevel
    (h : @Params.univs P₀ = @Params.univs P₁) (l : @SLevel P₀) :
    transportLevel h.symm (transportLevel h l) = l := by
  apply Subtype.ext
  rfl

/-! ## Constructor congruences

One parametric direction; the reverse direction is the same lemma at
`h.symm`, so this six-lemma set replaces each rung's twelve. -/

@[simp] theorem transportExpr_bvar (h : @Params.univs P₀ = @Params.univs P₁)
    (i : Nat) :
    transportExpr h (@SExpr.bvar P₀ i) = @SExpr.bvar P₁ i := rfl

@[simp] theorem transportExpr_sort (h : @Params.univs P₀ = @Params.univs P₁)
    (u : @SLevel P₀) :
    transportExpr h (@SExpr.sort P₀ u) =
      @SExpr.sort P₁ (transportLevel h u) := rfl

@[simp] theorem transportExpr_const (h : @Params.univs P₀ = @Params.univs P₁)
    (c : Name) (ls : List (@SLevel P₀)) :
    transportExpr h (@SExpr.const P₀ c ls) =
      @SExpr.const P₁ c (ls.map (transportLevel h)) := rfl

@[simp] theorem transportExpr_app (h : @Params.univs P₀ = @Params.univs P₁)
    (f a : @SExpr P₀) :
    transportExpr h (@SExpr.app P₀ f a) =
      @SExpr.app P₁ (transportExpr h f) (transportExpr h a) := rfl

@[simp] theorem transportExpr_lam (h : @Params.univs P₀ = @Params.univs P₁)
    (A e : @SExpr P₀) :
    transportExpr h (@SExpr.lam P₀ A e) =
      @SExpr.lam P₁ (transportExpr h A) (transportExpr h e) := rfl

@[simp] theorem transportExpr_forallE
    (h : @Params.univs P₀ = @Params.univs P₁) (A B : @SExpr P₀) :
    transportExpr h (@SExpr.forallE P₀ A B) =
      @SExpr.forallE P₁ (transportExpr h A) (transportExpr h B) := rfl

@[simp] theorem transportExpr_transportExpr
    (h : @Params.univs P₀ = @Params.univs P₁) (e : @SExpr P₀) :
    transportExpr h.symm (transportExpr h e) = e := by
  induction e <;> simp [List.map_map, Function.comp_def, *]

/-! ## Level-operator commutation -/

@[simp] theorem transportLevel_zero (h : @Params.univs P₀ = @Params.univs P₁) :
    transportLevel h (@SLevel.zero P₀) = @SLevel.zero P₁ := by
  apply Subtype.ext
  rfl

@[simp] theorem transportLevel_succ (h : @Params.univs P₀ = @Params.univs P₁)
    (u : @SLevel P₀) :
    transportLevel h (@SLevel.succ P₀ u) =
      @SLevel.succ P₁ (transportLevel h u) := by
  apply Subtype.ext
  rfl

@[simp] theorem transportLevel_imax (h : @Params.univs P₀ = @Params.univs P₁)
    (u v : @SLevel P₀) :
    transportLevel h (@SLevel.imax P₀ u v) =
      @SLevel.imax P₁ (transportLevel h u) (transportLevel h v) := by
  apply Subtype.ext
  rfl

@[simp] theorem transportLevel_max (h : @Params.univs P₀ = @Params.univs P₁)
    (u v : @SLevel P₀) :
    transportLevel h (@SLevel.max P₀ u v) =
      @SLevel.max P₁ (transportLevel h u) (transportLevel h v) := by
  apply Subtype.ext
  rfl

@[simp] theorem transportLevel_instV (h : @Params.univs P₀ = @Params.univs P₁)
    (ls : List (@SLevel P₀)) (u : VLevel) :
    transportLevel h (@SLevel.instV P₀ ls u) =
      @SLevel.instV P₁ (ls.map (transportLevel h)) u := by
  apply Subtype.ext
  funext v
  change u.eval (ls.map fun l => l.1 v) =
    u.eval ((ls.map (transportLevel h)).map fun l => l.1 v)
  congr 1
  simp [List.map_map, Function.comp_def, transportLevel]

/-! ## Substitution transport -/

/-- Substitution transport, pointwise. -/
noncomputable def transportSubst (h : @Params.univs P₀ = @Params.univs P₁)
    (σ : @Subst P₀) : @Subst P₁ := fun i => transportExpr h (σ i)

@[simp] theorem transportExpr_lift' (h : @Params.univs P₀ = @Params.univs P₁)
    (e : @SExpr P₀) (ρ : Lift) :
    transportExpr h (@SExpr.lift' P₀ e ρ) =
      @SExpr.lift' P₁ (transportExpr h e) ρ := by
  induction e generalizing ρ <;> simp [SExpr.lift', *]

@[simp] theorem transportSubst_lift (h : @Params.univs P₀ = @Params.univs P₁)
    (σ : @Subst P₀) :
    transportSubst h (@Subst.lift P₀ σ) =
      @Subst.lift P₁ (transportSubst h σ) := by
  funext i
  cases i <;> simp [transportSubst, Subst.lift, transportExpr_lift']

@[simp] theorem transportExpr_subst (h : @Params.univs P₀ = @Params.univs P₁)
    (e : @SExpr P₀) (σ : @Subst P₀) :
    transportExpr h (@SExpr.subst P₀ e σ) =
      @SExpr.subst P₁ (transportExpr h e) (transportSubst h σ) := by
  induction e generalizing σ <;> simp [SExpr.subst, transportSubst, *]

@[simp] theorem transportExpr_inst (h : @Params.univs P₀ = @Params.univs P₁)
    (e a : @SExpr P₀) :
    transportExpr h (@SExpr.inst P₀ e a) =
      @SExpr.inst P₁ (transportExpr h e) (transportExpr h a) := by
  change transportExpr h
      (@SExpr.subst P₀ e (@Subst.one P₀ a)) =
    @SExpr.subst P₁ (transportExpr h e)
      (@Subst.one P₁ (transportExpr h a))
  rw [transportExpr_subst]
  congr 1
  funext i
  cases i <;> rfl

@[simp] theorem transportExpr_mkInst (h : @Params.univs P₀ = @Params.univs P₁)
    (ls : List (@SLevel P₀)) (e : VExpr) :
    transportExpr h (@SExpr.mkInst P₀ ls e) =
      @SExpr.mkInst P₁ (ls.map (transportLevel h)) e := by
  induction e <;> simp [SExpr.mkInst, List.map_map, Function.comp_def, *]

/-! ## Iterated binder/application towers -/

theorem transportExpr_foldr_forallE (h : @Params.univs P₀ = @Params.univs P₁)
    (Ts : List (@SExpr P₀)) (e : @SExpr P₀) :
    transportExpr h (Ts.foldr (fun A B => @SExpr.forallE P₀ A B) e) =
      (Ts.map (transportExpr h)).foldr
        (fun A B => @SExpr.forallE P₁ A B) (transportExpr h e) := by
  induction Ts <;> simp [*]

theorem transportExpr_foldr_app (h : @Params.univs P₀ = @Params.univs P₁)
    (args : List (@SExpr P₀)) (e : @SExpr P₀) :
    transportExpr h (args.foldr (fun A acc => @SExpr.app P₀ acc A) e) =
      (args.map (transportExpr h)).foldr
        (fun A acc => @SExpr.app P₁ acc A) (transportExpr h e) := by
  induction args <;> simp [*]

theorem transportExpr_foldl_app (h : @Params.univs P₀ = @Params.univs P₁)
    (args : List (@SExpr P₀)) (e : @SExpr P₀) :
    transportExpr h (args.foldl (fun acc A => @SExpr.app P₀ acc A) e) =
      (args.map (transportExpr h)).foldl
        (fun acc A => @SExpr.app P₁ acc A) (transportExpr h e) := by
  induction args generalizing e <;> simp [*]

/-! ## Pattern payload commutation

`Pattern.RHS`/`Pattern.Check` are `Params`-independent (`.fixed` carries a
`VExpr`), so payloads need no transport at all; only their `applyS`
computation commutes with the functor. -/

@[simp] theorem transportExpr_rhs_applyS
    (h : @Params.univs P₀ = @Params.univs P₁) {p : Pattern}
    (r : p.RHS) (m₁ : List (@SLevel P₀)) (m₂ : p.Path → @SExpr P₀) :
    transportExpr h (@Pattern.RHS.applyS P₀ p m₁ m₂ r) =
      @Pattern.RHS.applyS P₁ p (m₁.map (transportLevel h))
        (fun path => transportExpr h (m₂ path)) r := by
  induction r with
  | fixed e closed => exact transportExpr_mkInst h m₁ e
  | var path => rfl
  | app f a ihf iha =>
    simp only [Pattern.RHS.applyS, transportExpr_app, ihf, iha]

theorem transport_defeqsS (h : @Params.univs P₀ = @Params.univs P₁)
    {p : Pattern} (ck : p.Check) (m₁ : List (@SLevel P₀))
    (m₂ : p.Path → @SExpr P₀) :
    (@Pattern.Check.defeqsS P₀ p m₁ m₂ ck).map
        (fun ab => (transportExpr h ab.1, transportExpr h ab.2)) =
      @Pattern.Check.defeqsS P₁ p (m₁.map (transportLevel h))
        (fun path => transportExpr h (m₂ path)) ck := by
  induction ck with
  | true => rfl
  | defeq a b rest ih =>
    simp only [Pattern.Check.defeqsS, List.map_cons, ih,
      transportExpr_rhs_applyS]

/-- Transport a triple list of local check evidence. -/
noncomputable def transportDfs (h : @Params.univs P₀ = @Params.univs P₁)
    (dfs : List (@SExpr P₀ × @SExpr P₀ × @SExpr P₀)) :
    List (@SExpr P₁ × @SExpr P₁ × @SExpr P₁) :=
  dfs.map fun (B, a, b) =>
    (transportExpr h B, transportExpr h a, transportExpr h b)

theorem transportDfs_map_snd (h : @Params.univs P₀ = @Params.univs P₁)
    (dfs : List (@SExpr P₀ × @SExpr P₀ × @SExpr P₀)) :
    (transportDfs h dfs).map (fun x => x.2) =
      (dfs.map fun x => x.2).map fun ab =>
        (transportExpr h ab.1, transportExpr h ab.2) := by
  simp [transportDfs, List.map_map, Function.comp_def]

/-! ## Syntactic match transport -/

theorem transportMatchesS (h : @Params.univs P₀ = @Params.univs P₁)
    {p : Pattern} {e : @SExpr P₀} {m₁ : List (@SLevel P₀)}
    {m₂ : p.Path → @SExpr P₀}
    (H : @Pattern.MatchesS P₀ p e m₁ m₂) :
    @Pattern.MatchesS P₁ p (transportExpr h e)
      (m₁.map (transportLevel h))
      (fun path => transportExpr h (m₂ path)) := by
  induction H with
  | @const c ls =>
    rw [transportExpr_const]
    refine cast ?_ (@Pattern.MatchesS.const P₁ c (ls.map (transportLevel h)))
    congr 1
    funext path
    exact Empty.elim path
  | @var f f' f₁ g₁ a' _ ih =>
    change @Pattern.MatchesS P₁ (.var f)
      (.app (transportExpr h f') (transportExpr h a'))
      (f₁.map (transportLevel h))
      (fun path => transportExpr h (Option.elim path a' g₁))
    have heq : (fun path => transportExpr h (Option.elim path a' g₁)) =
        (fun path => Option.elim path (transportExpr h a')
          (fun path => transportExpr h (g₁ path))) := by
      funext path
      cases path <;> rfl
    rw [heq]
    exact ih.var
  | @app f f' f₁ g₁ a a' f₂ g₂ _ _ ihf iha =>
    change @Pattern.MatchesS P₁ (.app f a)
      (@SExpr.app P₁ (transportExpr h f') (transportExpr h a'))
      (f₁.map (transportLevel h))
      (fun path => transportExpr h (Sum.elim g₁ g₂ path))
    have heq : (fun path => transportExpr h (Sum.elim g₁ g₂ path)) =
        Sum.elim (fun path => transportExpr h (g₁ path))
          (fun path => transportExpr h (g₂ path)) := by
      funext path
      cases path <;> rfl
    rw [heq]
    exact ihf.app iha

/-! ## Context lookup transport -/

theorem transportLookup (h : @Params.univs P₀ = @Params.univs P₁)
    {Γ : List (@SExpr P₀)} {i : Nat} {A : @SExpr P₀}
    (H : @Lookup P₀ Γ i A) :
    @Lookup P₁ (Γ.map (transportExpr h)) i (transportExpr h A) := by
  induction H with
  | zero =>
    rw [transportExpr_lift']
    exact .zero
  | succ _ ih =>
    rw [transportExpr_lift']
    exact .succ ih

/-! ## List roundtrips -/

@[simp] theorem transport_context_roundtrip
    (h : @Params.univs P₀ = @Params.univs P₁) (Γ : List (@SExpr P₁)) :
    (Γ.map (transportExpr h.symm)).map (transportExpr h) = Γ := by
  rw [List.map_map]
  refine List.map_id''' Γ fun e _ => ?_
  show transportExpr h (transportExpr h.symm e) = e
  simp [transportExpr_transportExpr h.symm e]

@[simp] theorem transport_level_list_roundtrip
    (h : @Params.univs P₀ = @Params.univs P₁) (ls : List (@SLevel P₁)) :
    (ls.map (transportLevel h.symm)).map (transportLevel h) = ls := by
  rw [List.map_map]
  refine List.map_id''' ls fun l _ => ?_
  show transportLevel h (transportLevel h.symm l) = l
  simp [transportLevel_transportLevel h.symm l]


/-! ## Axiom closures

The whole transport layer is proof-complete: it is pure syntax, so it
carries neither `Classical.choice` (the functor is defined by the `SExpr`
recursor, not chosen) nor any admission. -/

/-- info: 'Lean4Lean.SExpr.transportLevel' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms transportLevel

/-- info: 'Lean4Lean.SExpr.transportExpr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms transportExpr

/-- info: 'Lean4Lean.SExpr.transportExpr_transportExpr' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms transportExpr_transportExpr

/-- info: 'Lean4Lean.SExpr.transportExpr_mkInst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms transportExpr_mkInst

/-- info: 'Lean4Lean.SExpr.transportMatchesS' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms transportMatchesS

/-- info: 'Lean4Lean.SExpr.transport_context_roundtrip' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms transport_context_roundtrip
end SExpr
end Lean4Lean
