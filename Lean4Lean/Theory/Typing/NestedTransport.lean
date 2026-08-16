import Lean4Lean.Theory.Typing.NestedInductiveLemmas
import Lean4Lean.Theory.Typing.Strong

/-!
# Constant-interpretation substitution (L4L-09C transport, part 1)

The clean compositional substitution σ̂ underlying nested restoration:
each interpreted constant is replaced by a closed value, level-instantiated
per occurrence.  The spine-collapsed artifact substitution `restoreExpr`
is the β-image of σ̂ at fully applied auxiliary heads; the typed transport
built on σ̂ is the route from the flattened block's staged semantic
certificate to restored-artifact well-formedness recorded in the L4L-09A
design note.

This file establishes σ̂, its commutation calculus with lifting,
instantiation, and level instantiation, context-lookup transport, the
`ConstInterp` environment morphism, and the typed transport
`IsDefEq.substConst` with its `HasType`/`IsType`/`VConstant.WF`/
`VDefEq.WF` corollaries.  The β-collapse bridge from σ̂ to the
spine-collapsed artifact substitution and the per-phase morphism
construction for a staged flattened block are the remaining transport
obligations.
-/

namespace Lean4Lean

/-- σ̂: replace each interpreted constant by its closed value at the
occurrence's levels. -/
def VExpr.substConst (interp : Name → Option VExpr) : VExpr → VExpr
  | .bvar i => .bvar i
  | .sort l => .sort l
  | .const c ls =>
    match interp c with
    | some v => v.instL ls
    | none => .const c ls
  | .app f a => .app (f.substConst interp) (a.substConst interp)
  | .lam ty body => .lam (ty.substConst interp) (body.substConst interp)
  | .forallE ty body => .forallE (ty.substConst interp) (body.substConst interp)

/-- Every interpreted value is closed. -/
def InterpClosed (interp : Name → Option VExpr) : Prop :=
  ∀ c v, interp c = some v → v.ClosedN 0

namespace VExpr

variable {interp : Name → Option VExpr}

theorem substConst_liftN (hc : InterpClosed interp) :
    ∀ (e : VExpr) (k : Nat),
      (e.liftN n k).substConst interp = (e.substConst interp).liftN n k
  | .bvar _, _ => rfl
  | .sort _, _ => rfl
  | .const c ls, k => by
    simp only [liftN, substConst]
    cases h : interp c with
    | none => simp [liftN]
    | some v =>
      exact (((hc c v h).instL (ls := ls)).liftN_eq (Nat.zero_le k)).symm
  | .app f a, k => by
    simp only [liftN, substConst, substConst_liftN hc f k,
      substConst_liftN hc a k]
  | .lam ty body, k => by
    simp only [liftN, substConst, substConst_liftN hc ty k,
      substConst_liftN hc body (k+1)]
  | .forallE ty body, k => by
    simp only [liftN, substConst, substConst_liftN hc ty k,
      substConst_liftN hc body (k+1)]

theorem substConst_lift (hc : InterpClosed interp) (e : VExpr) :
    (e.lift).substConst interp = (e.substConst interp).lift :=
  substConst_liftN hc e 0

theorem substConst_instN (hc : InterpClosed interp) :
    ∀ (e a : VExpr) (k : Nat),
      (e.inst a k).substConst interp =
        (e.substConst interp).inst (a.substConst interp) k
  | .bvar i, a, k => by
    simp only [inst, substConst]
    unfold instVar
    split
    · simp [substConst]
    · split
      · exact (substConst_liftN hc a 0).symm ▸ rfl
      · simp [substConst]
  | .sort _, _, _ => rfl
  | .const c ls, a, k => by
    simp only [inst, substConst]
    cases h : interp c with
    | none => simp [inst]
    | some v =>
      exact (((hc c v h).instL (ls := ls)).instN_eq (Nat.zero_le k)).symm
  | .app f b, a, k => by
    simp only [inst, substConst, substConst_instN hc f a k,
      substConst_instN hc b a k]
  | .lam ty body, a, k => by
    simp only [inst, substConst, substConst_instN hc ty a k,
      substConst_instN hc body a (k+1)]
  | .forallE ty body, a, k => by
    simp only [inst, substConst, substConst_instN hc ty a k,
      substConst_instN hc body a (k+1)]

theorem substConst_inst (hc : InterpClosed interp) (e a : VExpr) :
    (e.inst a).substConst interp =
      (e.substConst interp).inst (a.substConst interp) :=
  substConst_instN hc e a 0

theorem substConst_instL :
    ∀ (e : VExpr),
      (e.instL ls).substConst interp = ((e.substConst interp).instL ls : VExpr)
  | .bvar _ => rfl
  | .sort _ => by simp [instL, substConst]
  | .const c ls' => by
    simp only [instL, substConst]
    cases interp c with
    | none => simp [instL]
    | some v => exact (instL_instL).symm
  | .app f a => by
    simp only [instL, substConst, substConst_instL f, substConst_instL a]
  | .lam ty body => by
    simp only [instL, substConst, substConst_instL ty, substConst_instL body]
  | .forallE ty body => by
    simp only [instL, substConst, substConst_instL ty, substConst_instL body]

end VExpr

/-- Context-lookup transport along σ̂. -/
theorem Lookup.substConst {interp : Name → Option VExpr}
    (hc : InterpClosed interp) :
    ∀ {Γ i A}, Lookup Γ i A →
      Lookup (Γ.map (VExpr.substConst interp)) i (A.substConst interp)
  | _, _, _, .zero => by
    rw [List.map_cons, VExpr.substConst_lift hc]
    exact .zero
  | _, _, _, .succ h => by
    rw [List.map_cons, VExpr.substConst_lift hc]
    exact .succ (h.substConst hc)

namespace VEnv

/-- Environment morphism along a constant interpretation: interpreted
constants become closed values typed at their σ̂-image types in the target
environment; surviving constants and registered defeqs are σ̂-imaged.  The
staged flattened environments of a nested block and their restored
counterparts form exactly such a morphism, with the auxiliary families,
constructors, and recursors interpreted by their restoration closures. -/
structure ConstInterp (E E' : VEnv) (interp : Name → Option VExpr) : Prop where
  ordered' : VEnv.Ordered E'
  closed : InterpClosed interp
  value : ∀ {c ci v}, E.constants c = some ci → interp c = some v →
    E'.HasType ci.uvars [] v (ci.type.substConst interp)
  keep : ∀ {c ci}, E.constants c = some ci → interp c = none →
    E'.constants c = some ⟨ci.uvars, ci.type.substConst interp⟩
  defeq : ∀ {df}, E.defeqs df →
    E'.defeqs ⟨df.uvars, df.lhs.substConst interp,
      df.rhs.substConst interp, df.type.substConst interp⟩
  structEta : ∀ {rule}, E.structEtas rule → E'.structEtas rule
  structEta_familyType : ∀ {rule}, E.structEtas rule →
    ∀ levels,
      (rule.familyType.instL levels).substConst interp =
        rule.familyType.instL levels
  structEta_structureType : ∀ {rule}, E.structEtas rule →
    ∀ levels params,
      (rule.structureType levels params).substConst interp =
        rule.structureType levels (params.map (VExpr.substConst interp))
  structEta_rebuild : ∀ {rule}, E.structEtas rule →
    ∀ levels params major,
      (rule.rebuild levels params major).substConst interp =
        rule.rebuild levels (params.map (VExpr.substConst interp))
          (major.substConst interp)

/-- Typed transport along a constant interpretation: every Theory judgment
of the interpreted environment holds of the σ̂-images in the target
environment. -/
theorem IsDefEq.substConst {E E' : VEnv} {interp : Name → Option VExpr}
    (hi : ConstInterp E E' interp) (H : E.IsDefEq U Γ e1 e2 A) :
    E'.IsDefEq U (Γ.map (VExpr.substConst interp))
      (e1.substConst interp) (e2.substConst interp)
      (A.substConst interp) := by
  induction H using IsDefEq.rec
      (motive_2 := fun Γ A es B _ =>
        E'.SpineWF U (Γ.map (VExpr.substConst interp))
          (A.substConst interp) (es.map (VExpr.substConst interp))
          (B.substConst interp)) with
  | bvar h => exact .bvar (h.substConst hi.closed)
  | symm _ ih => exact .symm ih
  | trans _ _ ih1 ih2 => exact .trans ih1 ih2
  | sortDF h1 h2 h3 => exact .sortDF h1 h2 h3
  | @constDF c ci ls ls' _ h1 h2 h3 h4 h5 =>
    rw [VExpr.substConst_instL (e := ci.type)]
    simp only [VExpr.substConst]
    cases hv : interp c with
    | none => exact .constDF (hi.keep h1 hv) h2 h3 h4 h5
    | some v =>
      have hval := hi.value h1 hv
      have hnil : OnCtx ([] : List VExpr) (E'.IsType ci.uvars) := trivial
      have hcore := hval.instL_r hi.ordered' hnil h2 h3 h5
      exact hcore.weak0 hi.ordered'
  | appDF _ _ ih1 ih2 =>
    exact (VExpr.substConst_inst hi.closed ..).symm ▸ .appDF ih1 ih2
  | lamDF _ _ ih1 ih2 => exact .lamDF ih1 ih2
  | forallEDF _ _ ih1 ih2 => exact .forallEDF ih1 ih2
  | defeqDF _ _ ih1 ih2 => exact .defeqDF ih1 ih2
  | beta _ _ ih1 ih2 =>
    simpa [VExpr.substConst, VExpr.substConst_inst hi.closed] using
      VEnv.IsDefEq.beta ih1 ih2
  | eta _ ih =>
    simpa [VExpr.substConst, VExpr.substConst_lift hi.closed] using
      VEnv.IsDefEq.eta ih
  | structEta hreg hlevels hlevelsLength hparamsLength _ _ _
      ihSpine ihMajor ihRebuild =>
    rw [hi.structEta_familyType hreg] at ihSpine
    rw [hi.structEta_structureType hreg] at ihMajor
    rw [hi.structEta_rebuild hreg,
      hi.structEta_structureType hreg] at ihRebuild
    have hout := VEnv.IsDefEq.structEta (hi.structEta hreg) hlevels
      hlevelsLength (by simpa using hparamsLength)
      (by simpa [VExpr.substConst] using ihSpine)
      ihMajor ihRebuild
    simpa only [hi.structEta_rebuild hreg,
      hi.structEta_structureType hreg] using hout
  | proofIrrel _ _ _ ih1 ih2 ih3 => exact .proofIrrel ih1 ih2 ih3
  | extra h1 h2 h3 =>
    simpa [VExpr.substConst_instL] using
      VEnv.IsDefEq.extra (env := E') (hi.defeq h1) h2 (by simpa using h3)
  | nil => exact .nil
  | cons _ _ ihType ihRest =>
    exact .cons ihType (by
      simpa only [VExpr.substConst_inst hi.closed] using ihRest)

theorem HasType.substConst {E E' : VEnv} {interp : Name → Option VExpr}
    (hi : ConstInterp E E' interp) (H : E.HasType U Γ e A) :
    E'.HasType U (Γ.map (VExpr.substConst interp))
      (e.substConst interp) (A.substConst interp) :=
  IsDefEq.substConst hi H

theorem IsType.substConst {E E' : VEnv} {interp : Name → Option VExpr}
    (hi : ConstInterp E E' interp) (H : E.IsType U Γ A) :
    E'.IsType U (Γ.map (VExpr.substConst interp)) (A.substConst interp) :=
  let ⟨_, h⟩ := H; ⟨_, IsDefEq.substConst hi h⟩

end VEnv

/-- Constant well-formedness transports to the σ̂-image constant. -/
theorem VConstant.WF.substConst {E E' : VEnv} {interp : Name → Option VExpr}
    {ci : VConstant} (hi : VEnv.ConstInterp E E' interp) (H : ci.WF E) :
    VConstant.WF E' ⟨ci.uvars, ci.type.substConst interp⟩ :=
  VEnv.IsType.substConst hi H

/-- Rule well-formedness transports to the σ̂-image rule. -/
theorem VDefEq.WF.substConst {E E' : VEnv} {interp : Name → Option VExpr}
    {df : VDefEq} (hi : VEnv.ConstInterp E E' interp) (H : df.WF E) :
    VDefEq.WF E' ⟨df.uvars, df.lhs.substConst interp,
      df.rhs.substConst interp, df.type.substConst interp⟩ :=
  ⟨VEnv.IsDefEq.substConst hi H.1, VEnv.IsDefEq.substConst hi H.2⟩

end Lean4Lean
