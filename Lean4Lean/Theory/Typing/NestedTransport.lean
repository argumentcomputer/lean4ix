import Lean4Lean.Theory.Typing.NestedInductiveLemmas
import Lean4Lean.Theory.Typing.InductivePatternWF
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
`VDefEq.WF` corollaries.  It also proves exact syntactic and typed
β-collapse at auxiliary-family and auxiliary-constructor heads, including
bare zero-parameter heads and arbitrary trailing arguments once the restored
head is inert, and syntactic agreement for recursor renaming across a complete
application spine.  Instantiating the explicit lookup, disjointness, and
typing premises from a checked nested block, plus constructing its per-phase
morphisms, are the remaining transport obligations.
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

/-- Constant substitution distributes over an application spine. -/
theorem VExpr.substConst_appN {interp : Name → Option VExpr}
    (f : VExpr) (args : List VExpr) :
    (f.appN args).substConst interp =
      (f.substConst interp).appN (args.map (VExpr.substConst interp)) := by
  induction args generalizing f with
  | nil => rfl
  | cons arg args ih =>
    simpa [VExpr.appN, VExpr.substConst] using ih (f.app arg)

/-- Constant substitution distributes through an iterated Pi telescope. -/
theorem VExpr.substConst_forallN {interp : Name → Option VExpr}
    (As : List VExpr) (C : VExpr) :
    (VExpr.forallN As C).substConst interp =
      VExpr.forallN (As.map (VExpr.substConst interp))
        (C.substConst interp) := by
  induction As with
  | nil => rfl
  | cons A As ih =>
    simp only [VExpr.forallN, VExpr.substConst, List.map_cons, ih]

/-- Nested restoration distributes structurally through an iterated Pi
telescope; spine collapse can only fire inside its component expressions. -/
theorem VInductDecl.restoreExpr_forallN
    (entries : List VInductDecl.RestoreEntry)
    (recMap : List (Name × Name)) (As : List VExpr) (C : VExpr) :
    VInductDecl.restoreExpr entries recMap (VExpr.forallN As C) =
      VExpr.forallN
        (As.map (VInductDecl.restoreExpr entries recMap))
        (VInductDecl.restoreExpr entries recMap C) := by
  induction As with
  | nil => rfl
  | cons A As ih =>
    simp only [VExpr.forallN, VInductDecl.restoreExpr, List.map_cons, ih]

/-- The analogous structural law for generated lambda telescopes. -/
theorem VInductDecl.restoreExpr_lamN
    (entries : List VInductDecl.RestoreEntry)
    (recMap : List (Name × Name)) (As : List VExpr) (C : VExpr) :
    VInductDecl.restoreExpr entries recMap (VExpr.lamN As C) =
      VExpr.lamN
        (As.map (VInductDecl.restoreExpr entries recMap))
        (VInductDecl.restoreExpr entries recMap C) := by
  induction As with
  | nil => rfl
  | cons A As ih =>
    simp only [VExpr.lamN, VInductDecl.restoreExpr, List.map_cons, ih]

/-- Every interpreted value is closed. -/
def InterpClosed (interp : Name → Option VExpr) : Prop :=
  ∀ c v, interp c = some v → v.ClosedN 0

/-- Nested restoration's simultaneous parameter instantiation is exactly
the generic telescope-body instantiation used by the typed beta-collapse
API. -/
theorem VInductDecl.instRevParams_eq_instRev
    (body : VExpr) (args : List VExpr) :
    VInductDecl.instRevParams body args = body.instRev args := by
  induction args generalizing body with
  | nil => rfl
  | cons arg args ih =>
    exact ih (body.inst arg args.length)

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

/-- Constant substitution commutes with the outermost-first simultaneous
instantiation used by generated rule bodies and telescope codomains. -/
theorem substConst_instRev (hc : InterpClosed interp)
    (body : VExpr) (args : List VExpr) :
    (body.instRev args).substConst interp =
      (body.substConst interp).instRev
        (args.map (VExpr.substConst interp)) := by
  induction args generalizing body with
  | nil => rfl
  | cons arg args ih =>
    simp only [VExpr.instRev, List.map_cons]
    rw [ih, VExpr.substConst_instN hc]
    simp only [List.length_map]

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

namespace VInductDecl

private theorem restoreExpr_const_of_pos
    {entries : List RestoreEntry} {recMap : List (Name × Name)}
    {entry : RestoreEntry} {ls : List VLevel}
    (hrec : recMap.find? (·.1 == entry.aux) = none)
    (hentry : entries.find? (·.aux == entry.aux) = some entry)
    (hnp : 0 < entry.np) :
    restoreExpr entries recMap (.const entry.aux ls) =
      .const entry.aux ls := by
  have hs : restoreExpr.restoreSpine entries recMap
      (.const entry.aux ls) = none := by
    unfold restoreExpr.restoreSpine
    simp only [VExpr.appHead, VExpr.appArgs]
    rw [hrec, hentry]
    simp [show ¬ 0 = entry.np by omega]
  simp [restoreExpr, hs]

private theorem restoreExpr_aux_reverse_prefix
    {entries : List RestoreEntry} {recMap : List (Name × Name)}
    {entry : RestoreEntry} {ls : List VLevel}
    (hrec : recMap.find? (·.1 == entry.aux) = none)
    (hentry : entries.find? (·.aux == entry.aux) = some entry) :
    ∀ revArgs : List VExpr, revArgs.length < entry.np →
      restoreExpr entries recMap
          ((VExpr.const entry.aux ls).appN revArgs.reverse) =
        (VExpr.const entry.aux ls).appN
          (revArgs.reverse.map (restoreExpr entries recMap)) := by
  intro revArgs hlt
  induction revArgs with
  | nil =>
      change restoreExpr entries recMap (VExpr.const entry.aux ls) =
        VExpr.const entry.aux ls
      exact restoreExpr_const_of_pos hrec hentry (by simpa using hlt)
  | cons arg revArgs ih =>
      have hprefix : revArgs.length < entry.np := by
        simpa using Nat.lt_trans (Nat.lt_succ_self _) hlt
      have hfull : revArgs.length + 1 < entry.np := by simpa using hlt
      rw [List.reverse_cons, VExpr.appN_append]
      change restoreExpr entries recMap
        (((VExpr.const entry.aux ls).appN revArgs.reverse).app arg) = _
      change (restoreExpr.restoreSpine entries recMap
        ((restoreExpr entries recMap
          ((VExpr.const entry.aux ls).appN revArgs.reverse)).app
            (restoreExpr entries recMap arg))).getD _ = _
      rw [ih hprefix]
      have hs : restoreExpr.restoreSpine entries recMap
          (((VExpr.const entry.aux ls).appN
            (revArgs.reverse.map (restoreExpr entries recMap))).app
              (restoreExpr entries recMap arg)) = none := by
        have hhead : ((((VExpr.const entry.aux ls).appN
            (revArgs.reverse.map (restoreExpr entries recMap))).app
              (restoreExpr entries recMap arg))).appHead =
            VExpr.const entry.aux ls := by
          simp [VExpr.appHead, VExpr.appHead_appN]
        have hargs : ((((VExpr.const entry.aux ls).appN
            (revArgs.reverse.map (restoreExpr entries recMap))).app
              (restoreExpr entries recMap arg))).appArgs [] =
            revArgs.reverse.map (restoreExpr entries recMap) ++
              [restoreExpr entries recMap arg] := by
          simp [VExpr.appArgs, VExpr.appArgs_appN]
        unfold restoreExpr.restoreSpine
        rw [hhead, hargs]
        simp only
        rw [hrec, hentry]
        simp only [List.length_append, List.length_map,
          List.length_reverse, List.length_cons, List.length_nil]
        simp [Nat.ne_of_lt hfull]
      rw [hs]
      simp [List.map_append, List.map_reverse, VExpr.appN_append]
      rfl

private theorem restoreExpr_aux_prefix
    {entries : List RestoreEntry} {recMap : List (Name × Name)}
    {entry : RestoreEntry} {ls : List VLevel} {args : List VExpr}
    (hrec : recMap.find? (·.1 == entry.aux) = none)
    (hentry : entries.find? (·.aux == entry.aux) = some entry)
    (hlt : args.length < entry.np) :
    restoreExpr entries recMap ((VExpr.const entry.aux ls).appN args) =
      (VExpr.const entry.aux ls).appN
        (args.map (restoreExpr entries recMap)) := by
  simpa using restoreExpr_aux_reverse_prefix hrec hentry args.reverse
    (by simpa using hlt)

/-- At an exact auxiliary spine, nested restoration is precisely simultaneous
parameter instantiation of the entry's replacement value. This includes the
zero-parameter case, where restoration happens at the bare auxiliary head. -/
theorem restoreExpr_aux_appN
    {entries : List RestoreEntry} {recMap : List (Name × Name)}
    {entry : RestoreEntry} {ls : List VLevel} {args : List VExpr}
    (hrec : recMap.find? (·.1 == entry.aux) = none)
    (hentry : entries.find? (·.aux == entry.aux) = some entry)
    (hlen : args.length = entry.np) :
    restoreExpr entries recMap ((VExpr.const entry.aux ls).appN args) =
      instRevParams entry.value
        (args.map (restoreExpr entries recMap)) := by
  cases hrev : args.reverse with
  | nil =>
      have : args = [] := by
        have := congrArg List.reverse hrev
        simpa using this
      subst args
      have hnp : entry.np = 0 := by simpa using hlen.symm
      change (restoreExpr.restoreSpine entries recMap
        (VExpr.const entry.aux ls)).getD _ = _
      have hs : restoreExpr.restoreSpine entries recMap
          (VExpr.const entry.aux ls) =
          some (instRevParams entry.value []) := by
        unfold restoreExpr.restoreSpine
        simp only [VExpr.appHead, VExpr.appArgs]
        rw [hrec, hentry]
        simp [hnp]
      rw [hs]
      rfl
  | cons arg revArgs =>
      have hargs : args = revArgs.reverse ++ [arg] := by
        have := congrArg List.reverse hrev
        simpa using this
      have hprefix' : revArgs.length < entry.np := by
        rw [hargs] at hlen
        simp only [List.length_append, List.length_reverse,
          List.length_cons, List.length_nil] at hlen
        omega
      have hprefix : revArgs.reverse.length < entry.np := by
        simpa using hprefix'
      rw [hargs, VExpr.appN_append]
      change (restoreExpr.restoreSpine entries recMap
        ((restoreExpr entries recMap
          ((VExpr.const entry.aux ls).appN revArgs.reverse)).app
            (restoreExpr entries recMap arg))).getD _ = _
      rw [restoreExpr_aux_prefix hrec hentry hprefix]
      have hs : restoreExpr.restoreSpine entries recMap
          (((VExpr.const entry.aux ls).appN
            (revArgs.reverse.map (restoreExpr entries recMap))).app
              (restoreExpr entries recMap arg)) =
          some (instRevParams entry.value
            (revArgs.reverse.map (restoreExpr entries recMap) ++
              [restoreExpr entries recMap arg])) := by
        have hhead : ((((VExpr.const entry.aux ls).appN
            (revArgs.reverse.map (restoreExpr entries recMap))).app
              (restoreExpr entries recMap arg))).appHead =
            VExpr.const entry.aux ls := by
          simp [VExpr.appHead, VExpr.appHead_appN]
        have hargs' : ((((VExpr.const entry.aux ls).appN
            (revArgs.reverse.map (restoreExpr entries recMap))).app
              (restoreExpr entries recMap arg))).appArgs [] =
            revArgs.reverse.map (restoreExpr entries recMap) ++
              [restoreExpr entries recMap arg] := by
          simp [VExpr.appArgs, VExpr.appArgs_appN]
        unfold restoreExpr.restoreSpine
        rw [hhead, hargs']
        simp only
        rw [hrec, hentry]
        have hsaturated :
            (revArgs.reverse.map (restoreExpr entries recMap) ++
              [restoreExpr entries recMap arg]).length = entry.np := by
          simpa [hargs] using hlen
        have hfull : revArgs.length + 1 = entry.np := by
          simpa using hsaturated
        simp [hfull]
      rw [hs]
      simp [List.map_append]

private theorem restoreExpr_rec_reverse
    {entries : List RestoreEntry} {recMap : List (Name × Name)}
    {oldName newName : Name} {ls : List VLevel}
    (hold : recMap.find? (·.1 == oldName) = some (oldName, newName))
    (hnewRec : recMap.find? (·.1 == newName) = none)
    (hnewEntry : entries.find? (·.aux == newName) = none)
    (hnewCtor : findRestoreCtor entries newName = none) :
    ∀ revArgs : List VExpr,
      restoreExpr entries recMap
          ((VExpr.const oldName ls).appN revArgs.reverse) =
        (VExpr.const newName ls).appN
          (revArgs.reverse.map (restoreExpr entries recMap)) := by
  intro revArgs
  induction revArgs with
  | nil =>
      change restoreExpr entries recMap (VExpr.const oldName ls) =
        VExpr.const newName ls
      change (restoreExpr.restoreSpine entries recMap
        (VExpr.const oldName ls)).getD _ = _
      have hs : restoreExpr.restoreSpine entries recMap
          (VExpr.const oldName ls) = some (VExpr.const newName ls) := by
        unfold restoreExpr.restoreSpine
        simp only [VExpr.appHead, VExpr.appArgs]
        rw [hold]
        rfl
      rw [hs]
      rfl
  | cons arg revArgs ih =>
      rw [List.reverse_cons, VExpr.appN_append]
      change restoreExpr entries recMap
        (((VExpr.const oldName ls).appN revArgs.reverse).app arg) = _
      change (restoreExpr.restoreSpine entries recMap
        ((restoreExpr entries recMap
          ((VExpr.const oldName ls).appN revArgs.reverse)).app
            (restoreExpr entries recMap arg))).getD _ = _
      rw [ih]
      have hs : restoreExpr.restoreSpine entries recMap
          (((VExpr.const newName ls).appN
            (revArgs.reverse.map (restoreExpr entries recMap))).app
              (restoreExpr entries recMap arg)) = none := by
        have hhead : ((((VExpr.const newName ls).appN
            (revArgs.reverse.map (restoreExpr entries recMap))).app
              (restoreExpr entries recMap arg))).appHead =
            VExpr.const newName ls := by
          simp [VExpr.appHead, VExpr.appHead_appN]
        unfold restoreExpr.restoreSpine
        rw [hhead]
        simp only
        rw [hnewRec, hnewEntry, hnewCtor]
      rw [hs]
      simp [List.map_append, List.map_reverse, VExpr.appN_append]
      rfl

/-- Recursor restoration renames the head and recursively restores every
argument, provided the restored name is outside all restoration domains. -/
theorem restoreExpr_rec_appN
    {entries : List RestoreEntry} {recMap : List (Name × Name)}
    {oldName newName : Name} {ls : List VLevel} {args : List VExpr}
    (hold : recMap.find? (·.1 == oldName) = some (oldName, newName))
    (hnewRec : recMap.find? (·.1 == newName) = none)
    (hnewEntry : entries.find? (·.aux == newName) = none)
    (hnewCtor : findRestoreCtor entries newName = none) :
    restoreExpr entries recMap ((VExpr.const oldName ls).appN args) =
      (VExpr.const newName ls).appN
        (args.map (restoreExpr entries recMap)) := by
  simpa using restoreExpr_rec_reverse hold hnewRec hnewEntry hnewCtor
    args.reverse

private theorem restoreExpr_ctor_const_of_pos
    {entries : List RestoreEntry} {recMap : List (Name × Name)}
    {entry : RestoreEntry} {ctor suffix : Name} {ls : List VLevel}
    (hrec : recMap.find? (·.1 == ctor) = none)
    (hentry : entries.find? (·.aux == ctor) = none)
    (hctor : findRestoreCtor entries ctor = some (entry, suffix))
    (hnp : 0 < entry.np) :
    restoreExpr entries recMap (.const ctor ls) = .const ctor ls := by
  have hs : restoreExpr.restoreSpine entries recMap
      (.const ctor ls) = none := by
    unfold restoreExpr.restoreSpine
    simp only [VExpr.appHead, VExpr.appArgs]
    rw [hrec, hentry, hctor]
    simp [show ¬ 0 = entry.np by omega]
  simp [restoreExpr, hs]

private theorem restoreExpr_ctor_reverse_prefix
    {entries : List RestoreEntry} {recMap : List (Name × Name)}
    {entry : RestoreEntry} {ctor suffix : Name} {ls : List VLevel}
    (hrec : recMap.find? (·.1 == ctor) = none)
    (hentry : entries.find? (·.aux == ctor) = none)
    (hctor : findRestoreCtor entries ctor = some (entry, suffix)) :
    ∀ revArgs : List VExpr, revArgs.length < entry.np →
      restoreExpr entries recMap
          ((VExpr.const ctor ls).appN revArgs.reverse) =
        (VExpr.const ctor ls).appN
          (revArgs.reverse.map (restoreExpr entries recMap)) := by
  intro revArgs hlt
  induction revArgs with
  | nil =>
      change restoreExpr entries recMap (VExpr.const ctor ls) =
        VExpr.const ctor ls
      exact restoreExpr_ctor_const_of_pos hrec hentry hctor
        (by simpa using hlt)
  | cons arg revArgs ih =>
      have hprefix : revArgs.length < entry.np := by
        simpa using Nat.lt_trans (Nat.lt_succ_self _) hlt
      have hfull : revArgs.length + 1 < entry.np := by simpa using hlt
      rw [List.reverse_cons, VExpr.appN_append]
      change restoreExpr entries recMap
        (((VExpr.const ctor ls).appN revArgs.reverse).app arg) = _
      change (restoreExpr.restoreSpine entries recMap
        ((restoreExpr entries recMap
          ((VExpr.const ctor ls).appN revArgs.reverse)).app
            (restoreExpr entries recMap arg))).getD _ = _
      rw [ih hprefix]
      have hs : restoreExpr.restoreSpine entries recMap
          (((VExpr.const ctor ls).appN
            (revArgs.reverse.map (restoreExpr entries recMap))).app
              (restoreExpr entries recMap arg)) = none := by
        have hhead : ((((VExpr.const ctor ls).appN
            (revArgs.reverse.map (restoreExpr entries recMap))).app
              (restoreExpr entries recMap arg))).appHead =
            VExpr.const ctor ls := by
          simp [VExpr.appHead, VExpr.appHead_appN]
        have hargs : ((((VExpr.const ctor ls).appN
            (revArgs.reverse.map (restoreExpr entries recMap))).app
              (restoreExpr entries recMap arg))).appArgs [] =
            revArgs.reverse.map (restoreExpr entries recMap) ++
              [restoreExpr entries recMap arg] := by
          simp [VExpr.appArgs, VExpr.appArgs_appN]
        unfold restoreExpr.restoreSpine
        rw [hhead, hargs]
        simp only
        rw [hrec, hentry, hctor]
        simp only [List.length_append, List.length_map,
          List.length_reverse, List.length_cons, List.length_nil]
        simp [Nat.ne_of_lt hfull]
      rw [hs]
      simp [List.map_append, List.map_reverse, VExpr.appN_append]
      rfl

private theorem restoreExpr_ctor_prefix
    {entries : List RestoreEntry} {recMap : List (Name × Name)}
    {entry : RestoreEntry} {ctor suffix : Name} {ls : List VLevel}
    {args : List VExpr}
    (hrec : recMap.find? (·.1 == ctor) = none)
    (hentry : entries.find? (·.aux == ctor) = none)
    (hctor : findRestoreCtor entries ctor = some (entry, suffix))
    (hlt : args.length < entry.np) :
    restoreExpr entries recMap ((VExpr.const ctor ls).appN args) =
      (VExpr.const ctor ls).appN
        (args.map (restoreExpr entries recMap)) := by
  simpa using restoreExpr_ctor_reverse_prefix hrec hentry hctor
    args.reverse (by simpa using hlt)

/-- At an exact auxiliary-constructor spine, restoration replaces the
auxiliary prefix in the target-family head and beta-instantiates the target
application's parameter-open arguments. -/
theorem restoreExpr_ctor_appN
    {entries : List RestoreEntry} {recMap : List (Name × Name)}
    {entry : RestoreEntry} {ctor suffix target : Name}
    {ls targetLevels : List VLevel} {valueArgs args : List VExpr}
    (hrec : recMap.find? (·.1 == ctor) = none)
    (hentry : entries.find? (·.aux == ctor) = none)
    (hctor : findRestoreCtor entries ctor = some (entry, suffix))
    (hvalue : entry.value =
      (VExpr.const target targetLevels).appN valueArgs)
    (hlen : args.length = entry.np) :
    restoreExpr entries recMap ((VExpr.const ctor ls).appN args) =
      instRevParams
        ((VExpr.const (target ++ suffix) targetLevels).appN valueArgs)
        (args.map (restoreExpr entries recMap)) := by
  cases hrev : args.reverse with
  | nil =>
      have : args = [] := by
        have := congrArg List.reverse hrev
        simpa using this
      subst args
      have hnp : entry.np = 0 := by simpa using hlen.symm
      change (restoreExpr.restoreSpine entries recMap
        (VExpr.const ctor ls)).getD _ = _
      have hs : restoreExpr.restoreSpine entries recMap
          (VExpr.const ctor ls) =
          some ((VExpr.const (target ++ suffix) targetLevels).appN
            valueArgs) := by
        unfold restoreExpr.restoreSpine
        simp only [VExpr.appHead, VExpr.appArgs]
        rw [hrec, hentry, hctor]
        simp only [hnp, hvalue, instRevParams]
        rw [VExpr.appHead_appN, VExpr.appArgs_appN]
        simp [VExpr.appArgs, VExpr.appHead]
      rw [hs]
      rfl
  | cons arg revArgs =>
      have hargs : args = revArgs.reverse ++ [arg] := by
        have := congrArg List.reverse hrev
        simpa using this
      have hprefix' : revArgs.length < entry.np := by
        rw [hargs] at hlen
        simp only [List.length_append, List.length_reverse,
          List.length_cons, List.length_nil] at hlen
        omega
      have hprefix : revArgs.reverse.length < entry.np := by
        simpa using hprefix'
      rw [hargs, VExpr.appN_append]
      change (restoreExpr.restoreSpine entries recMap
        ((restoreExpr entries recMap
          ((VExpr.const ctor ls).appN revArgs.reverse)).app
            (restoreExpr entries recMap arg))).getD _ = _
      rw [restoreExpr_ctor_prefix hrec hentry hctor hprefix]
      let restoredArgs :=
        revArgs.reverse.map (restoreExpr entries recMap) ++
          [restoreExpr entries recMap arg]
      have hsaturated : restoredArgs.length = entry.np := by
        simpa [restoredArgs, hargs] using hlen
      have hs : restoreExpr.restoreSpine entries recMap
          (((VExpr.const ctor ls).appN
            (revArgs.reverse.map (restoreExpr entries recMap))).app
              (restoreExpr entries recMap arg)) =
          some ((VExpr.const (target ++ suffix) targetLevels).appN
            (valueArgs.map (VExpr.instRev · restoredArgs))) := by
        have hhead : ((((VExpr.const ctor ls).appN
            (revArgs.reverse.map (restoreExpr entries recMap))).app
              (restoreExpr entries recMap arg))).appHead =
            VExpr.const ctor ls := by
          simp [VExpr.appHead, VExpr.appHead_appN]
        have hargs' : ((((VExpr.const ctor ls).appN
            (revArgs.reverse.map (restoreExpr entries recMap))).app
              (restoreExpr entries recMap arg))).appArgs [] =
            restoredArgs := by
          simp [restoredArgs, VExpr.appArgs, VExpr.appArgs_appN]
        unfold restoreExpr.restoreSpine
        rw [hhead, hargs']
        simp only
        rw [hrec, hentry, hctor]
        simp only [hsaturated, beq_self_eq_true, ↓reduceIte]
        rw [hvalue, instRevParams_eq_instRev, VExpr.instRev_appN]
        rw [VExpr.instRev_closedN restoredArgs (by trivial),
          VExpr.appHead_appN, VExpr.appArgs_appN]
        simp [VExpr.appArgs, VExpr.appHead]
      rw [hs]
      simp only [Option.getD_some]
      rw [instRevParams_eq_instRev, VExpr.instRev_appN]
      rw [VExpr.instRev_closedN _ (by trivial)]
      simp [restoredArgs, List.map_append, List.map_reverse]

private theorem restoreExpr_appN_reverse_of_head_inert
    {entries : List RestoreEntry} {recMap : List (Name × Name)}
    {base restored : VExpr} {name : Name} {ls : List VLevel}
    (hbase : restoreExpr entries recMap base = restored)
    (hhead : restored.appHead = VExpr.const name ls)
    (hrec : recMap.find? (·.1 == name) = none)
    (hentry : entries.find? (·.aux == name) = none)
    (hctor : findRestoreCtor entries name = none) :
    ∀ revArgs : List VExpr,
      restoreExpr entries recMap (base.appN revArgs.reverse) =
        restored.appN
          (revArgs.reverse.map (restoreExpr entries recMap)) := by
  intro revArgs
  induction revArgs with
  | nil => exact hbase
  | cons arg revArgs ih =>
      rw [List.reverse_cons, VExpr.appN_append]
      change restoreExpr entries recMap ((base.appN revArgs.reverse).app arg) = _
      change (restoreExpr.restoreSpine entries recMap
        ((restoreExpr entries recMap (base.appN revArgs.reverse)).app
          (restoreExpr entries recMap arg))).getD _ = _
      rw [ih]
      have hs : restoreExpr.restoreSpine entries recMap
          ((restored.appN
            (revArgs.reverse.map (restoreExpr entries recMap))).app
              (restoreExpr entries recMap arg)) = none := by
        have hhead' : ((restored.appN
            (revArgs.reverse.map (restoreExpr entries recMap))).app
              (restoreExpr entries recMap arg)).appHead =
            VExpr.const name ls := by
          simpa [VExpr.appHead, VExpr.appHead_appN] using hhead
        unfold restoreExpr.restoreSpine
        rw [hhead']
        simp only
        rw [hrec, hentry, hctor]
      rw [hs]
      simp [List.map_append, List.map_reverse, VExpr.appN_append]
      rfl

/-- Restoration extends through arbitrary trailing arguments once the
restored head is outside every restoration domain. -/
theorem restoreExpr_appN_of_head_inert
    {entries : List RestoreEntry} {recMap : List (Name × Name)}
    {base restored : VExpr} {name : Name} {ls : List VLevel}
    {args : List VExpr}
    (hbase : restoreExpr entries recMap base = restored)
    (hhead : restored.appHead = VExpr.const name ls)
    (hrec : recMap.find? (·.1 == name) = none)
    (hentry : entries.find? (·.aux == name) = none)
    (hctor : findRestoreCtor entries name = none) :
    restoreExpr entries recMap (base.appN args) =
      restored.appN (args.map (restoreExpr entries recMap)) := by
  simpa using restoreExpr_appN_reverse_of_head_inert
    hbase hhead hrec hentry hctor args.reverse

end VInductDecl

/-- Under the canonical recursor interpretation, σ̂ and nested restoration
agree syntactically on the complete recursor application spine. -/
theorem VExpr.substConst_restoreExpr_rec
    {U : Nat} {interp : Name → Option VExpr}
    {entries : List VInductDecl.RestoreEntry}
    {recMap : List (Name × Name)} {oldName newName : Name}
    {args : List VExpr}
    (hold : recMap.find? (·.1 == oldName) = some (oldName, newName))
    (hnewRec : recMap.find? (·.1 == newName) = none)
    (hnewEntry : entries.find? (·.aux == newName) = none)
    (hnewCtor : VInductDecl.findRestoreCtor entries newName = none)
    (hinterp : interp oldName =
      some (VExpr.const newName (VLevel.params U)))
    (hargs : args.map (VInductDecl.restoreExpr entries recMap) =
      args.map (VExpr.substConst interp)) :
    (((VExpr.const oldName (VLevel.params U)).appN args).substConst interp) =
      VInductDecl.restoreExpr entries recMap
        ((VExpr.const oldName (VLevel.params U)).appN args) := by
  rw [VExpr.substConst_appN, VExpr.substConst, hinterp]
  simp only
  rw [(show (VExpr.const newName (VLevel.params U)).LevelWF U by
    exact VLevel.params_wf).instL_id, ← hargs]
  exact (VInductDecl.restoreExpr_rec_appN hold hnewRec hnewEntry
    hnewCtor).symm

/-- Typed beta-collapse of σ̂ at one canonical auxiliary application. -/
theorem VEnv.IsDefEq.substConst_aux_beta
    {env : VEnv} (henv : env.Ordered) {U : Nat}
    {Γ As args : List VExpr} {body T B : VExpr}
    {interp : Name → Option VExpr} {aux : Name}
    (hinterp : interp aux = some (VExpr.lamN As body))
    (hlevel : (VExpr.lamN As body).LevelWF U)
    (hTel : env.OnTel U Γ As)
    (hbody : env.HasType U (As.reverse ++ Γ) body T)
    (hspine : env.SpineWF U Γ (VExpr.forallN As T)
      (args.map (VExpr.substConst interp)) B)
    (hlen : args.length = As.length) :
    env.IsDefEq U Γ
      (((VExpr.const aux (VLevel.params U)).appN args).substConst interp)
      (VInductDecl.instRevParams body
        (args.map (VExpr.substConst interp))) B := by
  rw [VExpr.substConst_appN, VExpr.substConst, hinterp]
  simp only
  rw [hlevel.instL_id, VInductDecl.instRevParams_eq_instRev]
  exact VEnv.IsDefEq.appN_lamN henv hTel hbody hspine
    (by simpa using hlen)

/-- Typed beta-collapse of σ̂ at an auxiliary application whose occurrence
levels need not be the identity parameters of the ambient universe context.
This is the recursor-world form needed after a declaration-level restoration
closure is instantiated into generated-rule universes. -/
theorem VEnv.IsDefEq.substConst_aux_beta_instL
    {env : VEnv} (henv : env.Ordered) {U : Nat}
    {Γ As args : List VExpr} {body T B : VExpr}
    {interp : Name → Option VExpr} {aux : Name}
    {levels : List VLevel}
    (hinterp : interp aux = some (VExpr.lamN As body))
    (hTel : env.OnTel U Γ (As.map (VExpr.instL levels)))
    (hbody : env.HasType U
      ((As.map (VExpr.instL levels)).reverse ++ Γ)
      (body.instL levels) T)
    (hspine : env.SpineWF U Γ
      (VExpr.forallN (As.map (VExpr.instL levels)) T)
      (args.map (VExpr.substConst interp)) B)
    (hlen : args.length = As.length) :
    env.IsDefEq U Γ
      (((VExpr.const aux levels).appN args).substConst interp)
      (VExpr.instRev (body.instL levels)
        (args.map (VExpr.substConst interp))) B := by
  rw [VExpr.substConst_appN, VExpr.substConst, hinterp]
  simp only
  rw [VExpr.instL_lamN]
  exact VEnv.IsDefEq.appN_lamN henv hTel hbody hspine
    (by simpa using hlen)

/-- Extend an already typed σ̂/restoration alignment across a trailing
application spine.  The restoration equation is kept explicit so this lemma
also applies at noncanonical universe occurrences, where the more specialized
auxiliary-constructor lemmas below do not match `VLevel.params U`. -/
theorem VEnv.IsDefEq.substConst_restoreExpr_appN_of_prefix
    {env : VEnv} {U : Nat} {Γ rest : List VExpr} {B C : VExpr}
    {interp : Name → Option VExpr}
    {entries : List VInductDecl.RestoreEntry}
    {recMap : List (Name × Name)} {base : VExpr}
    (hprefix : env.IsDefEq U Γ
      (base.substConst interp)
      (VInductDecl.restoreExpr entries recMap base) B)
    (hrestSpine : env.SpineWF U Γ B
      (rest.map (VExpr.substConst interp)) C)
    (hrest : rest.map (VInductDecl.restoreExpr entries recMap) =
      rest.map (VExpr.substConst interp))
    (hrestore : VInductDecl.restoreExpr entries recMap
        (base.appN rest) =
      (VInductDecl.restoreExpr entries recMap base).appN
        (rest.map (VInductDecl.restoreExpr entries recMap))) :
    env.IsDefEq U Γ
      ((base.appN rest).substConst interp)
      (VInductDecl.restoreExpr entries recMap (base.appN rest)) C := by
  rw [VExpr.substConst_appN, hrestore, hrest]
  exact VEnv.IsDefEq.appN_congr hprefix hrestSpine

/-- Build a typed σ̂/restoration alignment for one application once the
function heads agree exactly and the argument alignment is typed.  This is
the final composition step for restored recursor redexes: recursor renaming
is syntactic, while an auxiliary constructor major generally agrees only
after beta reduction. -/
theorem VEnv.IsDefEq.substConst_restoreExpr_app_of_head_eq
    {env : VEnv} {U : Nat} {Γ : List VExpr} {A B : VExpr}
    {interp : Name → Option VExpr}
    {entries : List VInductDecl.RestoreEntry}
    {recMap : List (Name × Name)} {fn arg : VExpr}
    (hfn : fn.substConst interp =
      VInductDecl.restoreExpr entries recMap fn)
    (hfnType : env.HasType U Γ (fn.substConst interp) (.forallE A B))
    (harg : env.IsDefEq U Γ (arg.substConst interp)
      (VInductDecl.restoreExpr entries recMap arg) A)
    (hrestore : VInductDecl.restoreExpr entries recMap (fn.app arg) =
      (VInductDecl.restoreExpr entries recMap fn).app
        (VInductDecl.restoreExpr entries recMap arg)) :
    env.IsDefEq U Γ
      ((fn.app arg).substConst interp)
      (VInductDecl.restoreExpr entries recMap (fn.app arg))
      (B.inst (arg.substConst interp)) := by
  have happ := hfnType.appDF harg
  simpa only [VExpr.substConst, hfn, hrestore] using happ

/-- Exact beta bridge from σ̂ to nested restoration at a saturated
auxiliary-family spine, assuming the recursively restored arguments agree
with their σ̂-images. -/
theorem VEnv.IsDefEq.substConst_restoreExpr_aux_beta
    {env : VEnv} (henv : env.Ordered) {U : Nat}
    {Γ As args : List VExpr} {T B : VExpr}
    {interp : Name → Option VExpr}
    {entries : List VInductDecl.RestoreEntry}
    {recMap : List (Name × Name)} {entry : VInductDecl.RestoreEntry}
    (hrec : recMap.find? (·.1 == entry.aux) = none)
    (hentry : entries.find? (·.aux == entry.aux) = some entry)
    (hlen : args.length = entry.np)
    (hargs : args.map (VInductDecl.restoreExpr entries recMap) =
      args.map (VExpr.substConst interp))
    (hinterp : interp entry.aux =
      some (VExpr.lamN As entry.value))
    (hbinders : As.length = entry.np)
    (hlevel : (VExpr.lamN As entry.value).LevelWF U)
    (hTel : env.OnTel U Γ As)
    (hbody : env.HasType U (As.reverse ++ Γ) entry.value T)
    (hspine : env.SpineWF U Γ (VExpr.forallN As T)
      (args.map (VExpr.substConst interp)) B) :
    env.IsDefEq U Γ
      (((VExpr.const entry.aux (VLevel.params U)).appN args).substConst interp)
      (VInductDecl.restoreExpr entries recMap
        ((VExpr.const entry.aux (VLevel.params U)).appN args)) B := by
  rw [VInductDecl.restoreExpr_aux_appN hrec hentry hlen, hargs]
  exact VEnv.IsDefEq.substConst_aux_beta henv hinterp hlevel hTel
    hbody hspine (hlen.trans hbinders.symm)

/-- The auxiliary-family beta bridge extends across arbitrary trailing
arguments when the restored head is outside every restoration domain. -/
theorem VEnv.IsDefEq.substConst_restoreExpr_aux_beta_appN
    {env : VEnv} (henv : env.Ordered) {U : Nat}
    {Γ As params rest : List VExpr} {T B C : VExpr}
    {interp : Name → Option VExpr}
    {entries : List VInductDecl.RestoreEntry}
    {recMap : List (Name × Name)}
    {entry : VInductDecl.RestoreEntry}
    {restoredHead : Name} {restoredLevels : List VLevel}
    (hrec : recMap.find? (·.1 == entry.aux) = none)
    (hentry : entries.find? (·.aux == entry.aux) = some entry)
    (hlen : params.length = entry.np)
    (hparams : params.map (VInductDecl.restoreExpr entries recMap) =
      params.map (VExpr.substConst interp))
    (hinterp : interp entry.aux =
      some (VExpr.lamN As entry.value))
    (hbinders : As.length = entry.np)
    (hlevel : (VExpr.lamN As entry.value).LevelWF U)
    (hTel : env.OnTel U Γ As)
    (hbody : env.HasType U (As.reverse ++ Γ) entry.value T)
    (hparamSpine : env.SpineWF U Γ (VExpr.forallN As T)
      (params.map (VExpr.substConst interp)) B)
    (hrestSpine : env.SpineWF U Γ B
      (rest.map (VExpr.substConst interp)) C)
    (hrest : rest.map (VInductDecl.restoreExpr entries recMap) =
      rest.map (VExpr.substConst interp))
    (hhead : (VInductDecl.instRevParams entry.value
      (params.map (VInductDecl.restoreExpr entries recMap))).appHead =
        VExpr.const restoredHead restoredLevels)
    (hheadRec : recMap.find? (·.1 == restoredHead) = none)
    (hheadEntry : entries.find? (·.aux == restoredHead) = none)
    (hheadCtor : VInductDecl.findRestoreCtor entries restoredHead = none) :
    env.IsDefEq U Γ
      (((VExpr.const entry.aux (VLevel.params U)).appN
        (params ++ rest)).substConst interp)
      (VInductDecl.restoreExpr entries recMap
        ((VExpr.const entry.aux (VLevel.params U)).appN
          (params ++ rest))) C := by
  have hbeta := VEnv.IsDefEq.substConst_restoreExpr_aux_beta
    henv hrec hentry hlen hparams hinterp hbinders hlevel hTel hbody
      hparamSpine
  have happ := VEnv.IsDefEq.appN_congr hbeta hrestSpine
  have hrestore := VInductDecl.restoreExpr_appN_of_head_inert
    (VInductDecl.restoreExpr_aux_appN (ls := VLevel.params U)
      hrec hentry hlen) hhead
    hheadRec hheadEntry hheadCtor (args := rest)
  rw [hrest] at hrestore
  rw [← VExpr.appN_append] at hrestore
  rw [hrestore]
  have hbase := VInductDecl.restoreExpr_aux_appN
    (ls := VLevel.params U) hrec hentry hlen
  rw [hbase] at happ
  simpa [VExpr.appN_append, VExpr.substConst_appN] using happ

/-- Exact beta bridge from σ̂ to nested restoration at a saturated
auxiliary-constructor spine. -/
theorem VEnv.IsDefEq.substConst_restoreExpr_ctor_beta
    {env : VEnv} (henv : env.Ordered) {U : Nat}
    {Γ As args : List VExpr} {T B : VExpr}
    {interp : Name → Option VExpr}
    {entries : List VInductDecl.RestoreEntry}
    {recMap : List (Name × Name)}
    {entry : VInductDecl.RestoreEntry} {ctor suffix target : Name}
    {targetLevels : List VLevel} {valueArgs : List VExpr}
    (hrec : recMap.find? (·.1 == ctor) = none)
    (hentry : entries.find? (·.aux == ctor) = none)
    (hctor : VInductDecl.findRestoreCtor entries ctor =
      some (entry, suffix))
    (hvalue : entry.value =
      (VExpr.const target targetLevels).appN valueArgs)
    (hlen : args.length = entry.np)
    (hargs : args.map (VInductDecl.restoreExpr entries recMap) =
      args.map (VExpr.substConst interp))
    (hinterp : interp ctor = some (VExpr.lamN As
      ((VExpr.const (target ++ suffix) targetLevels).appN valueArgs)))
    (hbinders : As.length = entry.np)
    (hlevel : (VExpr.lamN As
      ((VExpr.const (target ++ suffix) targetLevels).appN valueArgs)).LevelWF U)
    (hTel : env.OnTel U Γ As)
    (hbody : env.HasType U (As.reverse ++ Γ)
      ((VExpr.const (target ++ suffix) targetLevels).appN valueArgs) T)
    (hspine : env.SpineWF U Γ (VExpr.forallN As T)
      (args.map (VExpr.substConst interp)) B) :
    env.IsDefEq U Γ
      (((VExpr.const ctor (VLevel.params U)).appN args).substConst interp)
      (VInductDecl.restoreExpr entries recMap
        ((VExpr.const ctor (VLevel.params U)).appN args)) B := by
  rw [VInductDecl.restoreExpr_ctor_appN hrec hentry hctor hvalue hlen,
    hargs]
  exact VEnv.IsDefEq.substConst_aux_beta henv hinterp hlevel hTel
    hbody hspine (hlen.trans hbinders.symm)

/-- The auxiliary-constructor beta bridge extends across arbitrary trailing
arguments when the restored head is outside every restoration domain. -/
theorem VEnv.IsDefEq.substConst_restoreExpr_ctor_beta_appN
    {env : VEnv} (henv : env.Ordered) {U : Nat}
    {Γ As params rest : List VExpr} {T B C : VExpr}
    {interp : Name → Option VExpr}
    {entries : List VInductDecl.RestoreEntry}
    {recMap : List (Name × Name)}
    {entry : VInductDecl.RestoreEntry} {ctor suffix target : Name}
    {targetLevels : List VLevel} {valueArgs : List VExpr}
    {restoredHead : Name} {restoredLevels : List VLevel}
    (hrec : recMap.find? (·.1 == ctor) = none)
    (hentry : entries.find? (·.aux == ctor) = none)
    (hctor : VInductDecl.findRestoreCtor entries ctor =
      some (entry, suffix))
    (hvalue : entry.value =
      (VExpr.const target targetLevels).appN valueArgs)
    (hlen : params.length = entry.np)
    (hparams : params.map (VInductDecl.restoreExpr entries recMap) =
      params.map (VExpr.substConst interp))
    (hinterp : interp ctor = some (VExpr.lamN As
      ((VExpr.const (target ++ suffix) targetLevels).appN valueArgs)))
    (hbinders : As.length = entry.np)
    (hlevel : (VExpr.lamN As
      ((VExpr.const (target ++ suffix) targetLevels).appN valueArgs)).LevelWF U)
    (hTel : env.OnTel U Γ As)
    (hbody : env.HasType U (As.reverse ++ Γ)
      ((VExpr.const (target ++ suffix) targetLevels).appN valueArgs) T)
    (hparamSpine : env.SpineWF U Γ (VExpr.forallN As T)
      (params.map (VExpr.substConst interp)) B)
    (hrestSpine : env.SpineWF U Γ B
      (rest.map (VExpr.substConst interp)) C)
    (hrest : rest.map (VInductDecl.restoreExpr entries recMap) =
      rest.map (VExpr.substConst interp))
    (hhead : (VInductDecl.instRevParams
      ((VExpr.const (target ++ suffix) targetLevels).appN valueArgs)
      (params.map (VInductDecl.restoreExpr entries recMap))).appHead =
        VExpr.const restoredHead restoredLevels)
    (hheadRec : recMap.find? (·.1 == restoredHead) = none)
    (hheadEntry : entries.find? (·.aux == restoredHead) = none)
    (hheadCtor : VInductDecl.findRestoreCtor entries restoredHead = none) :
    env.IsDefEq U Γ
      (((VExpr.const ctor (VLevel.params U)).appN
        (params ++ rest)).substConst interp)
      (VInductDecl.restoreExpr entries recMap
        ((VExpr.const ctor (VLevel.params U)).appN
          (params ++ rest))) C := by
  have hbeta := VEnv.IsDefEq.substConst_restoreExpr_ctor_beta
    henv hrec hentry hctor hvalue hlen hparams hinterp hbinders hlevel
      hTel hbody hparamSpine
  have happ := VEnv.IsDefEq.appN_congr hbeta hrestSpine
  have hrestore := VInductDecl.restoreExpr_appN_of_head_inert
    (VInductDecl.restoreExpr_ctor_appN (ls := VLevel.params U)
      hrec hentry hctor hvalue hlen) hhead
    hheadRec hheadEntry hheadCtor (args := rest)
  rw [hrest] at hrestore
  rw [← VExpr.appN_append] at hrestore
  rw [hrestore]
  have hbase := VInductDecl.restoreExpr_ctor_appN
    (ls := VLevel.params U) hrec hentry hctor hvalue hlen
  rw [hbase] at happ
  simpa [VExpr.appN_append, VExpr.substConst_appN] using happ

namespace VEnv

/-- Successful constant insertion preserves the registered definitional
equations exactly. -/
theorem addConst_defeqs_iff
    {env env' : VEnv} {name : Name} {ci : VConstant}
    (hadd : env.addConst name ci = some env') (df : VDefEq) :
    env'.defeqs df ↔ env.defeqs df := by
  unfold VEnv.addConst at hadd
  split at hadd
  · cases hadd
  · cases hadd
    rfl

/-- Folding registered definitional equations yields precisely the new
equations together with the original inventory. -/
theorem foldl_addDefEq_defeqs_iff
    (dfs : List VDefEq) (env : VEnv) (df : VDefEq) :
    (dfs.foldl VEnv.addDefEq env).defeqs df ↔
      df ∈ dfs ∨ env.defeqs df := by
  induction dfs generalizing env with
  | nil => simp
  | cons d dfs ih =>
    rw [List.foldl_cons, ih (env.addDefEq d)]
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

/-- Successful constant insertion preserves the structure-eta inventory
exactly. -/
theorem addConst_structEtas_iff
    {env env' : VEnv} {name : Name} {ci : VConstant}
    (hadd : env.addConst name ci = some env') (rule : VStructEta) :
    env'.structEtas rule ↔ env.structEtas rule := by
  unfold VEnv.addConst at hadd
  split at hadd
  · cases hadd
  · cases hadd
    rfl

/-- A fold of registered definitional equations likewise leaves the
structure-eta inventory unchanged. -/
theorem foldl_addDefEq_structEtas_iff
    (dfs : List VDefEq) (env : VEnv) (rule : VStructEta) :
    (dfs.foldl VEnv.addDefEq env).structEtas rule ↔
      env.structEtas rule := by
  induction dfs generalizing env with
  | nil => rfl
  | cons df dfs ih =>
    exact (ih (env.addDefEq df)).trans Iff.rfl

/-- Registering a list of definitional equations leaves constant lookup
unchanged. -/
theorem foldl_addDefEq_constants_eq
    (dfs : List VDefEq) (env : VEnv) (name : Name) :
    (dfs.foldl VEnv.addDefEq env).constants name =
      env.constants name := by
  induction dfs generalizing env with
  | nil => rfl
  | cons df dfs ih => exact ih (env.addDefEq df)

/-- Environment morphism along a constant interpretation: interpreted
constants become closed values typed at their σ̂-image types in the target
environment; surviving constants are σ̂-imaged, and registered source
equations become typed target equations between their σ̂-images.  The latter
is deliberately semantic rather than literal registration: nested restoration
registers the β-collapsed `restoreExpr` image, whereas σ̂ retains the
corresponding lambda redexes.  The staged flattened environments of a nested
block and their restored counterparts form exactly such a morphism, with the
auxiliary families, constructors, and recursors interpreted by their
restoration closures. -/
structure ConstInterp (E E' : VEnv) (interp : Name → Option VExpr) : Prop where
  ordered' : VEnv.Ordered E'
  closed : InterpClosed interp
  value : ∀ {c ci v}, E.constants c = some ci → interp c = some v →
    E'.HasType ci.uvars [] v (ci.type.substConst interp)
  keep : ∀ {c ci}, E.constants c = some ci → interp c = none →
    E'.constants c = some ⟨ci.uvars, ci.type.substConst interp⟩
  defeq : ∀ {df}, E.defeqs df →
    E'.IsDefEq df.uvars [] (df.lhs.substConst interp)
      (df.rhs.substConst interp) (df.type.substConst interp)
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
  | extra h1 h2 _ =>
    have hcore := (hi.defeq h1).instL h2
    simpa [VExpr.substConst_instL] using hcore.weak0 hi.ordered'
  | nil => exact .nil
  | cons _ _ ihType ihRest =>
    exact .cons ihType (by
      simpa only [VExpr.substConst_inst hi.closed] using ihRest)

/-- Specialized typed transport for the simultaneous body instantiation at
the reduction boundary.  The result is normalized to the σ̂-image body and
pointwise σ̂-image captures expected by restored-rule consumers. -/
theorem IsDefEq.substConst_instRev
    {E E' : VEnv} {interp : Name → Option VExpr}
    (hi : ConstInterp E E' interp)
    {U : Nat} {Γ : List VExpr} {body redex B : VExpr}
    {levels : List VLevel} {args : List VExpr}
    (H : E.IsDefEq U Γ (VExpr.instRev (body.instL levels) args) redex B) :
    E'.IsDefEq U (Γ.map (VExpr.substConst interp))
      (VExpr.instRev ((body.substConst interp).instL levels)
        (args.map (VExpr.substConst interp)))
      (redex.substConst interp) (B.substConst interp) := by
  have hout := H.substConst hi
  rw [VExpr.substConst_instRev hi.closed,
    VExpr.substConst_instL] at hout
  exact hout

theorem HasType.substConst {E E' : VEnv} {interp : Name → Option VExpr}
    (hi : ConstInterp E E' interp) (H : E.HasType U Γ e A) :
    E'.HasType U (Γ.map (VExpr.substConst interp))
      (e.substConst interp) (A.substConst interp) :=
  IsDefEq.substConst hi H

/-- Application-spine typing transports pointwise along the same constant
interpretation.  This exposes the mutual spine case of `IsDefEq.substConst`
as a reusable boundary for staged nested reductions. -/
theorem SpineWF.substConst {E E' : VEnv} {interp : Name → Option VExpr}
    (hi : ConstInterp E E' interp) :
    ∀ {U : Nat} {Γ : List VExpr} {A es B},
      E.SpineWF U Γ A es B →
      E'.SpineWF U (Γ.map (VExpr.substConst interp))
        (A.substConst interp) (es.map (VExpr.substConst interp))
        (B.substConst interp)
  | _, _, _, [], _, .nil => .nil
  | _, _, _, _ :: _, _, .cons he hrest =>
    .cons (he.substConst hi) (by
      simpa only [VExpr.substConst_inst hi.closed] using
        SpineWF.substConst hi hrest)

/-- Transport a saturated telescope spine through σ̂ and retarget it to a
definitionally equal restored Pi tower.  The flat spine supplies all
argument typing; the caller supplies only the whole restored-type alignment
and the explicit common arity. -/
theorem SpineWF.substConst_forallN_of_defeq
    {E E' : VEnv} {interp : Name → Option VExpr}
    (hi : ConstInterp E E' interp) (henv : E'.WF)
    {U : Nat} {Γ : List VExpr}
    (hΓ : OnCtx (Γ.map (VExpr.substConst interp)) (E'.IsType U))
    {As : List VExpr} {C : VExpr} {es : List VExpr} {B : VExpr}
    (H : E.SpineWF U Γ (VExpr.forallN As C) es B)
    (hlen : es.length = As.length)
    {As' : List VExpr} {C' : VExpr}
    (hlen' : As'.length = As.length)
    (htype : E'.IsDefEqU U (Γ.map (VExpr.substConst interp))
      (VExpr.forallN As' C')
      ((VExpr.forallN As C).substConst interp)) :
    E'.SpineWF U (Γ.map (VExpr.substConst interp))
      (VExpr.forallN As' C') (es.map (VExpr.substConst interp))
      (VExpr.instRev C' (es.map (VExpr.substConst interp))) := by
  have hσ := H.substConst hi
  have hσ' : E'.SpineWF U (Γ.map (VExpr.substConst interp))
      (VExpr.forallN (As.map (VExpr.substConst interp))
        (C.substConst interp))
      (es.map (VExpr.substConst interp)) (B.substConst interp) := by
    simpa only [VExpr.substConst_forallN] using hσ
  have htype' : E'.IsDefEqU U (Γ.map (VExpr.substConst interp))
      (VExpr.forallN As' C')
      (VExpr.forallN (As.map (VExpr.substConst interp))
        (C.substConst interp)) := by
    simpa only [VExpr.substConst_forallN] using htype
  have htel := VEnv.TelDefEq.of_forallN_defeq_of_length henv hΓ
    (hlen'.trans (by simp)) htype'
  have hlenσ : (es.map (VExpr.substConst interp)).length =
      (As.map (VExpr.substConst interp)).length := by simpa using hlen
  have hσC' := hσ'.retarget hlenσ C'
  apply VEnv.TelDefEq.spine henv.ordered htel hσC'
  simpa [hlen] using hlen'.symm

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

/--
info: 'Lean4Lean.VInductDecl.restoreExpr_aux_appN' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.restoreExpr_aux_appN

/--
info: 'Lean4Lean.VInductDecl.restoreExpr_rec_appN' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.restoreExpr_rec_appN

/--
info: 'Lean4Lean.VInductDecl.restoreExpr_ctor_appN' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.restoreExpr_ctor_appN

/--
info: 'Lean4Lean.VInductDecl.restoreExpr_appN_of_head_inert' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.restoreExpr_appN_of_head_inert

/--
info: 'Lean4Lean.VExpr.substConst_restoreExpr_rec' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VExpr.substConst_restoreExpr_rec

/--
info: 'Lean4Lean.VEnv.IsDefEq.substConst_aux_beta' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VEnv.IsDefEq.substConst_aux_beta

/--
info: 'Lean4Lean.VEnv.IsDefEq.substConst_aux_beta_instL' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VEnv.IsDefEq.substConst_aux_beta_instL

/-- info: 'Lean4Lean.VEnv.IsDefEq.substConst_restoreExpr_appN_of_prefix' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Lean4Lean.VEnv.IsDefEq.substConst_restoreExpr_appN_of_prefix

/-- info: 'Lean4Lean.VEnv.IsDefEq.substConst_restoreExpr_app_of_head_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Lean4Lean.VEnv.IsDefEq.substConst_restoreExpr_app_of_head_eq

/--
info: 'Lean4Lean.VEnv.IsDefEq.substConst_restoreExpr_aux_beta' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VEnv.IsDefEq.substConst_restoreExpr_aux_beta

/--
info: 'Lean4Lean.VEnv.IsDefEq.substConst_restoreExpr_aux_beta_appN' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VEnv.IsDefEq.substConst_restoreExpr_aux_beta_appN

/--
info: 'Lean4Lean.VEnv.IsDefEq.substConst_restoreExpr_ctor_beta' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VEnv.IsDefEq.substConst_restoreExpr_ctor_beta

/--
info: 'Lean4Lean.VEnv.IsDefEq.substConst_restoreExpr_ctor_beta_appN' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VEnv.IsDefEq.substConst_restoreExpr_ctor_beta_appN

/-- info: 'Lean4Lean.VEnv.addConst_structEtas_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VEnv.addConst_structEtas_iff

/-- info: 'Lean4Lean.VEnv.addConst_defeqs_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VEnv.addConst_defeqs_iff

/-- info: 'Lean4Lean.VEnv.foldl_addDefEq_defeqs_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Lean4Lean.VEnv.foldl_addDefEq_defeqs_iff

/-- info: 'Lean4Lean.VEnv.foldl_addDefEq_structEtas_iff' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Lean4Lean.VEnv.foldl_addDefEq_structEtas_iff

/-- info: 'Lean4Lean.VEnv.foldl_addDefEq_constants_eq' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Lean4Lean.VEnv.foldl_addDefEq_constants_eq

/-- info: 'Lean4Lean.VEnv.SpineWF.substConst' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VEnv.SpineWF.substConst

/-- info: 'Lean4Lean.VExpr.substConst_forallN' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Lean4Lean.VExpr.substConst_forallN

/-- info: 'Lean4Lean.VExpr.substConst_instRev' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Lean4Lean.VExpr.substConst_instRev

/-- info: 'Lean4Lean.VEnv.IsDefEq.substConst_instRev' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VEnv.IsDefEq.substConst_instRev

/-- info: 'Lean4Lean.VInductDecl.restoreExpr_forallN' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.restoreExpr_forallN

/-- info: 'Lean4Lean.VInductDecl.restoreExpr_lamN' depends on axioms: [propext] -/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.restoreExpr_lamN

/-- info: 'Lean4Lean.VEnv.SpineWF.substConst_forallN_of_defeq' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VEnv.SpineWF.substConst_forallN_of_defeq
