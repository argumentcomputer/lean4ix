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

/-- Nested restoration distributes through an application spine whose head
is a bound variable.  Such a spine can never trigger any of the
constant-headed restoration cases, although restoration may still act
inside its arguments. -/
theorem VInductDecl.restoreExpr_bvar_appN
    (entries : List VInductDecl.RestoreEntry)
    (recMap : List (Name × Name)) (index : Nat) (arguments : List VExpr) :
    VInductDecl.restoreExpr entries recMap
        ((VExpr.bvar index).appN arguments) =
      (VExpr.bvar index).appN
        (arguments.map (VInductDecl.restoreExpr entries recMap)) := by
  have go : ∀ (base restored : VExpr),
      VInductDecl.restoreExpr entries recMap base = restored →
      restored.appHead = .bvar index →
      ∀ arguments : List VExpr,
        VInductDecl.restoreExpr entries recMap (base.appN arguments) =
          restored.appN
            (arguments.map (VInductDecl.restoreExpr entries recMap)) := by
    intro base restored hbase hhead remaining
    induction remaining generalizing base restored with
    | nil => exact hbase
    | cons argument remaining ih =>
        apply ih (base := base.app argument)
          (restored := restored.app
            (VInductDecl.restoreExpr entries recMap argument))
        · simp only [VInductDecl.restoreExpr, hbase]
          unfold VInductDecl.restoreExpr.restoreSpine
          simp [VExpr.appHead, hhead]
        · simpa [VExpr.appHead] using hhead
  exact go (.bvar index) (.bvar index) rfl rfl arguments

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

/-- Restoration maps an exact Pi prefix pointwise.  The length premise rules
out the total function's non-Pi fallback before all requested binders have
been consumed. -/
theorem VInductDecl.restoreExpr_telN
    (entries : List VInductDecl.RestoreEntry)
    (recMap : List (Name × Name)) (count : Nat) (expression : VExpr)
    (length_eq : (VExpr.telN count expression).length = count) :
    (VExpr.telN count expression).map
        (VInductDecl.restoreExpr entries recMap) =
      VExpr.telN count
        (VInductDecl.restoreExpr entries recMap expression) := by
  induction count generalizing expression with
  | zero => rfl
  | succ count ih =>
      cases expression with
      | forallE domain body =>
          have tailLength : (VExpr.telN count body).length = count := by
            simp only [VExpr.telN, List.length_cons] at length_eq
            omega
          simp only [VExpr.telN, List.map_cons, VInductDecl.restoreExpr]
          rw [ih body tailLength]
      | bvar | sort | const | app | lam =>
          simp only [VExpr.telN, List.length_nil] at length_eq
          omega

/-- Restoration commutes with dropping an exact Pi prefix. -/
theorem VInductDecl.restoreExpr_dropN
    (entries : List VInductDecl.RestoreEntry)
    (recMap : List (Name × Name)) (count : Nat) (expression : VExpr)
    (length_eq : (VExpr.telN count expression).length = count) :
    VInductDecl.restoreExpr entries recMap (VExpr.dropN count expression) =
      VExpr.dropN count
        (VInductDecl.restoreExpr entries recMap expression) := by
  induction count generalizing expression with
  | zero => rfl
  | succ count ih =>
      cases expression with
      | forallE domain body =>
          have tailLength : (VExpr.telN count body).length = count := by
            simp only [VExpr.telN, List.length_cons] at length_eq
            omega
          simp only [VExpr.dropN, VInductDecl.restoreExpr]
          exact ih body tailLength
      | bvar | sort | const | app | lam =>
          simp only [VExpr.telN, List.length_nil] at length_eq
          omega

/-- Asking `telN` for the complete constructor-telescope length returns the
constructor telescope itself. -/
theorem VExpr.telN_ctorFields_length (expression : VExpr) :
    VExpr.telN (VInductDecl.ctorFields expression).length expression =
      VInductDecl.ctorFields expression := by
  induction expression with
  | forallE domain body domainIH bodyIH =>
      simp only [VInductDecl.ctorFields, List.length_cons, VExpr.telN, bodyIH]
  | bvar | sort | const | app | lam => rfl

/-- Equal field counts turn whole-expression restoration into a pointwise
restoration equation for the complete constructor telescope. -/
theorem VInductDecl.restoreExpr_ctorFields
    (entries : List VInductDecl.RestoreEntry)
    (recMap : List (Name × Name)) {expression restored : VExpr}
    (restored_eq : VInductDecl.restoreExpr entries recMap expression =
      restored)
    (length_eq : (VInductDecl.ctorFields expression).length =
      (VInductDecl.ctorFields restored).length) :
    (VInductDecl.ctorFields expression).map
        (VInductDecl.restoreExpr entries recMap) =
      VInductDecl.ctorFields restored := by
  let count := (VInductDecl.ctorFields expression).length
  have sourceTel : VExpr.telN count expression =
      VInductDecl.ctorFields expression := by
    exact VExpr.telN_ctorFields_length expression
  have sourceLength : (VExpr.telN count expression).length = count := by
    rw [sourceTel]
  have restoredTel : VExpr.telN count restored =
      VInductDecl.ctorFields restored := by
    have count_eq : count = (VInductDecl.ctorFields restored).length :=
      length_eq
    rw [count_eq]
    exact VExpr.telN_ctorFields_length restored
  rw [← sourceTel,
    VInductDecl.restoreExpr_telN entries recMap count expression sourceLength,
    restored_eq, restoredTel]

/-- Every interpreted value is closed. -/
def InterpClosed (interp : Name → Option VExpr) : Prop :=
  ∀ c v, interp c = some v → v.ClosedN 0

/-- An expression does not mention any constant on which an interpretation
is defined. -/
def InterpInert (interp : Name → Option VExpr) (expression : VExpr) : Prop :=
  ∀ c v, interp c = some v → expression.hasConst c = false

/-- Constant substitution is literally inert on an expression disjoint from
its interpretation domain. -/
theorem VExpr.substConst_eq_of_interpInert
    {interp : Name → Option VExpr} {expression : VExpr}
    (inert : InterpInert interp expression) :
    expression.substConst interp = expression := by
  induction expression with
  | bvar | sort => rfl
  | const name levels =>
      cases found : interp name with
      | none => simp [VExpr.substConst, found]
      | some value =>
          have impossible := inert name value found
          simp [VExpr.hasConst] at impossible
  | app function argument functionIH argumentIH =>
      simp only [VExpr.substConst]
      congr
      · apply functionIH
        intro name value found
        exact (Bool.or_eq_false_iff.mp (inert name value found)).1
      · apply argumentIH
        intro name value found
        exact (Bool.or_eq_false_iff.mp (inert name value found)).2
  | lam domain body domainIH bodyIH =>
      simp only [VExpr.substConst]
      congr
      · apply domainIH
        intro name value found
        exact (Bool.or_eq_false_iff.mp (inert name value found)).1
      · apply bodyIH
        intro name value found
        exact (Bool.or_eq_false_iff.mp (inert name value found)).2
  | forallE domain body domainIH bodyIH =>
      simp only [VExpr.substConst]
      congr
      · apply domainIH
        intro name value found
        exact (Bool.or_eq_false_iff.mp (inert name value found)).1
      · apply bodyIH
        intro name value found
        exact (Bool.or_eq_false_iff.mp (inert name value found)).2

/-- `lamN` and `forallN` impose the same de Bruijn closedness obligations:
only their binder constructors differ. -/
theorem VExpr.ClosedN.lamN_of_forallN :
    ∀ {binders : List VExpr} {body : VExpr} {depth : Nat},
      (VExpr.forallN binders body).ClosedN depth →
        (VExpr.lamN binders body).ClosedN depth
  | [], _, _, closed => by
      simpa only [VExpr.forallN, VExpr.lamN] using closed
  | _ :: binders, body, depth, closed => by
      refine ⟨closed.1, VExpr.ClosedN.lamN_of_forallN ?_⟩
      simpa only [VExpr.forallN] using closed.2

namespace VInductDecl.NestedBlockChecked

variable {source : VInductDecl}

/-- Family and constructor constants introduced by the exact flattened
transaction, in their transaction order.  Recursors are kept separate
because their universe arity is the generated recursor arity rather than the
source declaration arity. -/
def flatDeclarationConstants (nested : NestedBlockChecked source) :
    List VConstVal :=
  nested.elim.flat.blockTypeConstants ++
    nested.elim.flat.blockConstructorConstants

/-- The closed σ̂-value assigned to one flattened family or constructor.
It abstracts the shared block parameters and restores the corresponding
formal application.  Abstracting only the shared parameters is intentional:
family indices and constructor fields remain in the resulting function
body. -/
def declarationInterpValue (nested : NestedBlockChecked source)
    (constant : VConstVal) : VExpr :=
  let binders := VExpr.telN source.nparams constant.type
  let parameters := VExpr.bvarRevRange 0 source.nparams
  VExpr.lamN binders <|
    restoreExpr nested.declEntries nested.recMap <|
      (VExpr.const constant.name (VLevel.params constant.uvars)).appN
        parameters

/-- Public name selected for one flattened recursor by restoration. -/
def restoredRecursorName (nested : NestedBlockChecked source)
    (recursor : VConstVal) : Name :=
  ((nested.recMap.find? (·.1 == recursor.name)).map (·.2)).getD
    recursor.name

/-- Closed σ̂-value assigned to one flattened recursor. -/
def recursorInterpValue (nested : NestedBlockChecked source)
    (recursor : VConstVal) : VExpr :=
  VExpr.const (nested.restoredRecursorName recursor)
    (VLevel.params recursor.uvars)

/-- Canonical compositional interpretation underlying this checked nested
restoration.  Every family and constructor introduced by the flattened
transaction is interpreted by its closed parameter abstraction.  Every
flattened recursor is interpreted by the exact restored recursor constant;
the producer's recursor map chooses its public name.  Constants inherited
from the input environment are left uninterpreted. -/
def restoreInterp (nested : NestedBlockChecked source) :
    Name → Option VExpr := fun name =>
  match nested.generation.recursors.find? (·.name == name) with
  | some recursor =>
      some (nested.recursorInterpValue recursor)
  | none =>
      match nested.flatDeclarationConstants.find? (·.name == name) with
      | some constant => some (nested.declarationInterpValue constant)
      | none => none

/-- The recursor branch has priority in the canonical interpreter. -/
@[simp] theorem restoreInterp_of_recursor_find?_eq_some
    (nested : NestedBlockChecked source) {name : Name}
    {recursor : VConstVal}
    (found : nested.generation.recursors.find? (·.name == name) =
      some recursor) :
    nested.restoreInterp name = some (nested.recursorInterpValue recursor) := by
  simp [NestedBlockChecked.restoreInterp, found]

/-- Once no recursor owns a name, an exact flattened declaration lookup
selects its parameter-abstraction value. -/
@[simp] theorem restoreInterp_of_declaration_find?_eq_some
    (nested : NestedBlockChecked source) {name : Name}
    (recursorAbsent :
      nested.generation.recursors.find? (·.name == name) = none)
    {constant : VConstVal}
    (found : nested.flatDeclarationConstants.find? (·.name == name) =
      some constant) :
    nested.restoreInterp name =
      some (nested.declarationInterpValue constant) := by
  simp [NestedBlockChecked.restoreInterp, recursorAbsent, found]

/-- A name absent from both exact producer inventories is uninterpreted. -/
@[simp] theorem restoreInterp_eq_none
    (nested : NestedBlockChecked source) {name : Name}
    (recursorAbsent :
      nested.generation.recursors.find? (·.name == name) = none)
    (declarationAbsent :
      nested.flatDeclarationConstants.find? (·.name == name) = none) :
    nested.restoreInterp name = none := by
  simp [NestedBlockChecked.restoreInterp, recursorAbsent, declarationAbsent]

/-- Every recursor in the exact flattened generation inventory is acted on
by the canonical restoration interpretation. -/
theorem restoreInterp_ne_none_of_recursor_mem
    (nested : NestedBlockChecked source) {recursor : VConstVal}
    (member : recursor ∈ nested.generation.recursors) :
    nested.restoreInterp recursor.name ≠ none := by
  intro absent
  unfold NestedBlockChecked.restoreInterp at absent
  split at absent
  next _ _ => contradiction
  next recursorAbsent =>
    have rejected := List.find?_eq_none.mp recursorAbsent recursor member
    simp at rejected

/-- Every family or constructor in the exact flattened declaration
inventory is acted on by the canonical restoration interpretation.  A name
collision with a recursor is harmless here: the higher-priority recursor
branch is still an interpretation value, never `none`. -/
theorem restoreInterp_ne_none_of_declaration_mem
    (nested : NestedBlockChecked source) {constant : VConstVal}
    (member : constant ∈ nested.flatDeclarationConstants) :
    nested.restoreInterp constant.name ≠ none := by
  intro absent
  unfold NestedBlockChecked.restoreInterp at absent
  split at absent
  next _ _ => contradiction
  next _ =>
    split at absent
    next _ _ => contradiction
    next declarationAbsent =>
      have rejected := List.find?_eq_none.mp declarationAbsent constant member
      simp at rejected

end VInductDecl.NestedBlockChecked

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

/-- The exact parameter-variable spine restores a guarded parameter
expression after the nested transformer has lowered it past constructor-local
binders. -/
theorem VInductDecl.instRevParams_lowerN_bvarRevRange
    {expression : VExpr} {locals params : Nat}
    (closed : expression.ClosedN (locals + params))
    (free : expression.hasLooseBelow locals = false) :
    instRevParams (expression.lowerN locals)
        (VExpr.bvarRevRange locals params) = expression := by
  rw [instRevParams_eq_instRev, ← VExpr.instRevAt_zero]
  have loweredClosed : (expression.lowerN locals).ClosedN params := by
    have closed' : expression.ClosedN (0 + locals + params) := by
      simpa using closed
    simpa using VExpr.lowerN_closedN
      (count := locals) (depth := 0) (remaining := params) closed' free
  have loweredClosed' :
      (expression.lowerN locals).ClosedN (0 + params) := by
    simpa using loweredClosed
  rw [VExpr.instRevAt_bvarRevRange_eq_liftN _ locals params 0
    loweredClosed']
  exact VExpr.liftN_lowerN_of_hasLooseBelow_eq_false free

/-- Simultaneously restoring every lowered parameter expression in a target
application recovers the exact application seen by the nested transformer.
The number of target parameters need not equal the current source block's
parameter count: every target argument may depend on all current parameters. -/
theorem VInductDecl.instRevParams_lowerN_const_appN_bvarRevRange
    {target : Name} {levels : List VLevel} {values : List VExpr}
    {locals params : Nat}
    (closed : ∀ expression ∈ values,
      expression.ClosedN (locals + params))
    (free : ∀ expression ∈ values,
      expression.hasLooseBelow locals = false) :
    instRevParams
        ((VExpr.const target levels).appN
          (values.map (fun expression => expression.lowerN locals)))
        (VExpr.bvarRevRange locals params) =
      (VExpr.const target levels).appN values := by
  rw [instRevParams_eq_instRev, VExpr.instRev_appN,
    VExpr.instRev_closedN _ (by trivial), List.map_map]
  congr 1
  have mapped :
      values.map (fun expression =>
          (expression.lowerN locals).instRev
            (VExpr.bvarRevRange locals params)) =
        values.map id := by
    apply List.map_congr_left
    intro expression member
    simpa only [id_eq, instRevParams_eq_instRev] using
      instRevParams_lowerN_bvarRevRange
        (closed expression member) (free expression member)
  change values.map (fun expression =>
      (expression.lowerN locals).instRev
        (VExpr.bvarRevRange locals params)) = values
  simpa only [List.map_id] using mapped

/-- Checked generated-name uniqueness projects to the exact flattened raw
family-name inventory. -/
theorem VInductDecl.NestedBlockChecked.flat_family_names_nodup
    {source : VInductDecl} (nested : NestedBlockChecked source) :
    (nested.elim.flat.types.map fun family => family.name).Nodup := by
  have viewGeneratedNamesNodup :
      (blockGeneratedNames
        nested.generation.block.normalization.view.types).Nodup := by
    rw [← nested.generation.checked.names_eq]
    exact nested.generation.checked.names_nodup
  have viewFamilyNamesNodup :
      (nested.generation.block.normalization.view.types.map
        fun family => family.name).Nodup := by
    unfold blockGeneratedNames at viewGeneratedNamesNodup
    exact (List.nodup_append.mp
      (List.nodup_append.mp viewGeneratedNamesNodup).1).1
  have rawViewFamilyNames :
      nested.elim.flat.types.map (fun family => family.name) =
        nested.generation.block.normalization.view.types.map
          (fun family => family.name) := by
    rw [← nested.generation.families_map_raw,
      ← CheckedFamilies.data_map_value
        nested.generation.block.checked.families,
      ← nested.generation.families_map_view]
    simp only [List.map_map]
    apply List.map_congr_left
    intro family member
    exact (nested.generation.shape.2.2.2.2 family member).1
  rw [rawViewFamilyNames]
  exact viewFamilyNamesNodup

/-- The original source-family names are pairwise distinct.  They are the
exact prefix of the checked flattened family inventory. -/
theorem VInductDecl.NestedBlockChecked.source_family_names_nodup
    {source : VInductDecl} (nested : NestedBlockChecked source) :
    (source.types.map fun family => family.name).Nodup := by
  have flat := nested.flat_family_names_nodup
  rw [nested.elim.specsAligned] at flat
  exact (List.nodup_append.mp flat).1

/-- Checked flattened generated-name uniqueness specializes to the exact
auxiliary specification inventory retained by nested elimination. -/
theorem VInductDecl.NestedBlockChecked.specs_aux_nodup
    {source : VInductDecl} (nested : NestedBlockChecked source) :
    (nested.elim.specs.map fun spec => spec.aux).Nodup := by
  have viewGeneratedNamesNodup :
      (blockGeneratedNames
        nested.generation.block.normalization.view.types).Nodup := by
    rw [← nested.generation.checked.names_eq]
    exact nested.generation.checked.names_nodup
  have viewFamilyNamesNodup :
      (nested.generation.block.normalization.view.types.map
        fun family => family.name).Nodup := by
    unfold blockGeneratedNames at viewGeneratedNamesNodup
    exact (List.nodup_append.mp
      (List.nodup_append.mp viewGeneratedNamesNodup).1).1
  have rawViewFamilyNames :
      nested.elim.flat.types.map (fun family => family.name) =
        nested.generation.block.normalization.view.types.map
          (fun family => family.name) := by
    rw [← nested.generation.families_map_raw,
      ← CheckedFamilies.data_map_value
        nested.generation.block.checked.families,
      ← nested.generation.families_map_view]
    simp only [List.map_map]
    apply List.map_congr_left
    intro family member
    exact (nested.generation.shape.2.2.2.2 family member).1
  have rawFamilyNamesNodup :
      (nested.elim.flat.types.map fun family => family.name).Nodup := by
    rw [rawViewFamilyNames]
    exact viewFamilyNamesNodup
  rw [nested.elim.specsAligned] at rawFamilyNamesNodup
  exact (List.nodup_append.mp rawFamilyNamesNodup).2.1

/-- A retained source-family name cannot be one of the auxiliary family
names appended by nested elimination.  This is an exact consequence of the
checked flattened generated-name inventory and the producer's positional
`specsAligned` trace. -/
theorem VInductDecl.NestedBlockChecked.source_name_ne_aux
    {source : VInductDecl} (nested : NestedBlockChecked source)
    {family : VInductiveType} (familyMember : family ∈ source.types)
    {spec : NestedAuxSpec} (specMember : spec ∈ nested.elim.specs) :
    family.name ≠ spec.aux := by
  have viewGeneratedNamesNodup :
      (blockGeneratedNames
        nested.generation.block.normalization.view.types).Nodup := by
    rw [← nested.generation.checked.names_eq]
    exact nested.generation.checked.names_nodup
  have viewFamilyNamesNodup :
      (nested.generation.block.normalization.view.types.map
        fun candidate => candidate.name).Nodup := by
    unfold blockGeneratedNames at viewGeneratedNamesNodup
    exact (List.nodup_append.mp
      (List.nodup_append.mp viewGeneratedNamesNodup).1).1
  have rawViewFamilyNames :
      nested.elim.flat.types.map (fun candidate => candidate.name) =
        nested.generation.block.normalization.view.types.map
          (fun candidate => candidate.name) := by
    rw [← nested.generation.families_map_raw,
      ← CheckedFamilies.data_map_value
        nested.generation.block.checked.families,
      ← nested.generation.families_map_view]
    simp only [List.map_map]
    apply List.map_congr_left
    intro candidate member
    exact (nested.generation.shape.2.2.2.2 candidate member).1
  have rawFamilyNamesNodup :
      (nested.elim.flat.types.map fun candidate => candidate.name).Nodup := by
    rw [rawViewFamilyNames]
    exact viewFamilyNamesNodup
  rw [nested.elim.specsAligned] at rawFamilyNamesNodup
  exact (List.nodup_append.mp rawFamilyNamesNodup).2.2 family.name
    (List.mem_map_of_mem familyMember) spec.aux
    (List.mem_map_of_mem specMember)

/-- Recursor renaming is restricted to auxiliary-family recursors.  Hence
the canonical recursor of every retained source family keeps its exact name
through restoration. -/
theorem VInductDecl.NestedBlockChecked.recMap_find?_source_recursor_eq_none
    {source : VInductDecl} (nested : NestedBlockChecked source)
    {family : VInductiveType} (familyMember : family ∈ source.types) :
    nested.recMap.find? (·.1 == (.str family.name "rec" : Name)) = none := by
  unfold NestedBlockChecked.recMap
  rw [List.find?_eq_none]
  intro entry entryMember
  obtain ⟨index, upper, entryEq⟩ := List.mem_mapIdx.mp entryMember
  let spec := nested.elim.specs[index]
  have specMember : spec ∈ nested.elim.specs := List.getElem_mem upper
  have different : family.name ≠ spec.aux :=
    nested.source_name_ne_aux familyMember specMember
  rw [← entryEq]
  intro equal
  rw [beq_iff_eq] at equal
  have namesEqual : spec.aux = family.name := by
    injection equal
  exact different namesEqual.symm

/-- No auxiliary family name can be the source of a recursor-renaming entry.
Both sides are exact components of the checked flattened generated-name
inventory: auxiliary names occur in the family segment and the map keys occur
in its recursor segment. -/
theorem VInductDecl.NestedBlockChecked.recMap_find?_aux_eq_none
    {source : VInductDecl} (nested : NestedBlockChecked source)
    {spec : NestedAuxSpec} (member : spec ∈ nested.elim.specs) :
    nested.recMap.find? (·.1 == spec.aux) = none := by
  have generatedNodup :
      (blockGeneratedNames
        nested.generation.block.normalization.view.types).Nodup := by
    rw [← nested.generation.checked.names_eq]
    exact nested.generation.checked.names_nodup
  have rawViewNames :
      nested.elim.flat.types.map (fun family => family.name) =
        nested.generation.block.normalization.view.types.map
          (fun family => family.name) := by
    rw [← nested.generation.families_map_raw,
      ← CheckedFamilies.data_map_value
        nested.generation.block.checked.families,
      ← nested.generation.families_map_view]
    simp only [List.map_map]
    apply List.map_congr_left
    intro family familyMember
    exact (nested.generation.shape.2.2.2.2 family familyMember).1
  have specFamilyRaw : spec.aux ∈
      nested.elim.flat.types.map (fun family => family.name) := by
    rw [nested.elim.specsAligned]
    exact List.mem_append_right _ (List.mem_map_of_mem member)
  have specFamilyView : spec.aux ∈
      nested.generation.block.normalization.view.types.map
        (fun family => family.name) := by
    rw [← rawViewNames]
    exact specFamilyRaw
  unfold NestedBlockChecked.recMap
  rw [List.find?_eq_none]
  intro entry entryMember
  obtain ⟨index, upper, entryEq⟩ := List.mem_mapIdx.mp entryMember
  let candidate := nested.elim.specs[index]
  have candidateMember : candidate ∈ nested.elim.specs :=
    List.getElem_mem upper
  have candidateFamilyRaw : candidate.aux ∈
      nested.elim.flat.types.map (fun family => family.name) := by
    rw [nested.elim.specsAligned]
    exact List.mem_append_right _ (List.mem_map_of_mem candidateMember)
  have candidateFamilyView : candidate.aux ∈
      nested.generation.block.normalization.view.types.map
        (fun family => family.name) := by
    rw [← rawViewNames]
    exact candidateFamilyRaw
  obtain ⟨candidateFamily, candidateFamilyMember,
      candidateName⟩ := List.mem_map.mp candidateFamilyView
  have candidateRecursorView : (.str candidate.aux "rec" : Name) ∈
      nested.generation.block.normalization.view.types.map
        (fun family => (.str family.name "rec" : Name)) := by
    apply List.mem_map.2
    refine ⟨candidateFamily, candidateFamilyMember, ?_⟩
    simp only [candidateName]
  rw [blockGeneratedNames, List.nodup_append] at generatedNodup
  obtain ⟨familyCtorNodup, recursorNodup, familyCtorRecursorDisjoint⟩ :=
    generatedNodup
  have different : (.str candidate.aux "rec" : Name) ≠ spec.aux := by
    exact (familyCtorRecursorDisjoint spec.aux
      (List.mem_append.2 (.inl specFamilyView))
      (.str candidate.aux "rec") candidateRecursorView).symm
  rw [← entryEq]
  intro equal
  rw [beq_iff_eq] at equal
  have equal' : (.str candidate.aux "rec" : Name) = spec.aux := by
    simpa only [candidate] using equal
  exact different equal'

/-- The terminal producer state inherits the checked generated-name
disjointness for every recorded auxiliary specification. -/
theorem VInductDecl.NestedBlockChecked.recMap_find?_state_aux_eq_none
    {source : VInductDecl} (nested : NestedBlockChecked source)
    {spec : NestedAuxSpec} (member : spec ∈ nested.elim.state.specs.toList) :
    nested.recMap.find? (·.1 == spec.aux) = none := by
  apply nested.recMap_find?_aux_eq_none
  rw [nested.elim.specs_eq]
  exact member

/-- A member of an auxiliary specification list is the unique lookup by its
generated name in the corresponding declaration-world restoration entries. -/
private theorem VInductDecl.find_declEntry_of_spec_mem
    {specs : List NestedAuxSpec} {spec : NestedAuxSpec} {np : Nat}
    (nodup : (specs.map fun candidate => candidate.aux).Nodup)
    (member : spec ∈ specs) :
    (specs.map fun candidate : NestedAuxSpec =>
        (⟨candidate.aux, np, candidate.value⟩ : RestoreEntry)).find?
          (·.aux == spec.aux) =
      some ⟨spec.aux, np, spec.value⟩ := by
  induction specs with
  | nil => simp at member
  | cons head tail ih =>
      simp only [List.map_cons, List.nodup_cons] at nodup
      rcases List.mem_cons.mp member with equal | member
      · subst head
        simp
      · have different : head.aux ≠ spec.aux := by
          intro equal
          apply nodup.1
          rw [equal]
          exact List.mem_map_of_mem member
        simp [different, ih nodup.2 member]

/-- Exact lookup of the canonical declaration restoration entry for every
producer-retained auxiliary specification. -/
theorem VInductDecl.NestedBlockChecked.declEntries_find?_of_mem
    {source : VInductDecl} (nested : NestedBlockChecked source)
    {spec : NestedAuxSpec} (member : spec ∈ nested.elim.specs) :
    nested.declEntries.find? (·.aux == spec.aux) =
      some ⟨spec.aux, source.nparams, spec.value⟩ := by
  exact VInductDecl.find_declEntry_of_spec_mem nested.specs_aux_nodup member

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

/-! ## Universe instantiation of nested restoration

Nested restoration stores replacement bodies in the universe world of the
artifact being restored. Runtime projection and reduction programs then
instantiate that whole artifact at concrete levels. The following small
calculus shows that these operations commute when the replacement inventory
is instantiated pointwise. -/

/-- Instantiate the expression payload of one restoration entry without
changing its name or parameter-arity key. -/
def VInductDecl.RestoreEntry.instL (entry : VInductDecl.RestoreEntry)
    (levels : List VLevel) : VInductDecl.RestoreEntry :=
  { entry with value := entry.value.instL levels }

@[simp] theorem VInductDecl.RestoreEntry.instL_aux
    (entry : VInductDecl.RestoreEntry) (levels : List VLevel) :
    (entry.instL levels).aux = entry.aux := rfl

@[simp] theorem VInductDecl.RestoreEntry.instL_np
    (entry : VInductDecl.RestoreEntry) (levels : List VLevel) :
    (entry.instL levels).np = entry.np := rfl

@[simp] theorem VInductDecl.RestoreEntry.instL_value
    (entry : VInductDecl.RestoreEntry) (levels : List VLevel) :
    (entry.instL levels).value = entry.value.instL levels := rfl

/-- Universe instantiation preserves the head of an application spine and
instantiates only its universe payload. -/
theorem VExpr.appHead_instL (expression : VExpr)
    (levels : List VLevel) :
    (expression.instL levels).appHead = expression.appHead.instL levels := by
  induction expression with
  | app function argument functionIH _ =>
      simpa [VExpr.instL, VExpr.appHead] using functionIH
  | bvar | sort | const | lam | forallE => rfl

/-- Universe instantiation maps every argument of an application spine. -/
theorem VExpr.appArgs_instL (expression : VExpr)
    (levels : List VLevel) (accumulator : List VExpr) :
    (expression.instL levels).appArgs
        (accumulator.map (VExpr.instL levels)) =
      (expression.appArgs accumulator).map (VExpr.instL levels) := by
  induction expression generalizing accumulator with
  | app function argument functionIH _ =>
      simpa [VExpr.instL, VExpr.appArgs] using
        functionIH (argument :: accumulator)
  | bvar | sort | const | lam | forallE => rfl

/-- Simultaneous parameter substitution commutes with universe
instantiation. -/
theorem VInductDecl.instRevParams_instL (body : VExpr)
    (arguments : List VExpr) (levels : List VLevel) :
    (VInductDecl.instRevParams body arguments).instL levels =
      VInductDecl.instRevParams (body.instL levels)
        (arguments.map (VExpr.instL levels)) := by
  induction arguments generalizing body with
  | nil => rfl
  | cons argument arguments ih =>
      simp only [VInductDecl.instRevParams, List.map_cons]
      rw [ih, VExpr.instL_instN]
      simp only [List.length_map]

private theorem VInductDecl.findEntry_instL
    (entries : List VInductDecl.RestoreEntry) (levels : List VLevel)
    (name : Name) :
    (entries.map (·.instL levels)).find? (·.aux == name) =
      (entries.find? (·.aux == name)).map (·.instL levels) := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      simp only [List.map_cons, List.find?_cons]
      simp only [VInductDecl.RestoreEntry.instL_aux]
      split <;> simp_all

private theorem VInductDecl.findRestoreCtor_instL
    (entries : List VInductDecl.RestoreEntry) (levels : List VLevel)
    (name : Name) :
    VInductDecl.findRestoreCtor (entries.map (·.instL levels)) name =
      (VInductDecl.findRestoreCtor entries name).map fun result =>
        (result.1.instL levels, result.2) := by
  unfold VInductDecl.findRestoreCtor
  rw [List.findSome?_map, List.map_findSome?]
  apply congrArg (entries.findSome? ·)
  funext entry
  simp [VInductDecl.RestoreEntry.instL]

private theorem VInductDecl.restoreCtorResult_instL
    (value : VExpr) (suffix : Name) (levels : List VLevel) :
    (match value.appHead with
      | VExpr.const target targetLevels =>
          some ((VExpr.const (target ++ suffix) targetLevels).appN
            (value.appArgs []))
      | _ => none).map (VExpr.instL levels) =
      match (value.instL levels).appHead with
      | VExpr.const target targetLevels =>
          some ((VExpr.const (target ++ suffix) targetLevels).appN
            ((value.instL levels).appArgs []))
      | _ => none := by
  rw [VExpr.appHead_instL]
  cases head : value.appHead with
  | bvar | sort | app | lam | forallE => rfl
  | const target targetLevels =>
      simp only [VExpr.instL, Option.map_some, VExpr.instL_appN]
      have argsInst := VExpr.appArgs_instL value levels []
      simp only [List.map_nil] at argsInst
      rw [argsInst]

private theorem VInductDecl.restoreSpine_instL
    (entries : List VInductDecl.RestoreEntry)
    (recMap : List (Name × Name)) (expression : VExpr)
    (levels : List VLevel) :
    (VInductDecl.restoreExpr.restoreSpine entries recMap expression).map
        (VExpr.instL levels) =
      VInductDecl.restoreExpr.restoreSpine
        (entries.map (·.instL levels)) recMap
        (expression.instL levels) := by
  unfold VInductDecl.restoreExpr.restoreSpine
  have headInst := VExpr.appHead_instL expression levels
  have argsInst := VExpr.appArgs_instL expression levels []
  simp only [List.map_nil] at argsInst
  rw [headInst, argsInst]
  cases head : expression.appHead with
  | bvar | sort | app | lam | forallE => rfl
  | const name nameLevels =>
      simp only [VExpr.instL]
      cases recursor : recMap.find? (·.1 == name) with
      | some renamed =>
          by_cases empty : (expression.appArgs []).isEmpty
          · simp [empty, List.isEmpty_map, VExpr.instL]
          · simp [empty, List.isEmpty_map]
      | none =>
          rw [VInductDecl.findEntry_instL]
          cases entryFound : entries.find? (·.aux == name) with
          | some entry =>
              simp only [Option.map_some]
              by_cases arity : (expression.appArgs []).length == entry.np
              · simp [arity, VInductDecl.instRevParams_instL]
              · simp [arity]
          | none =>
              simp only [Option.map_none]
              rw [VInductDecl.findRestoreCtor_instL]
              cases constructorFound :
                  VInductDecl.findRestoreCtor entries name with
              | none => simp
              | some result =>
                  obtain ⟨entry, suffix⟩ := result
                  simp only [Option.map_some]
                  by_cases arity :
                      (expression.appArgs []).length == entry.np
                  · have arityInst :
                        (((expression.appArgs []).map
                            (VExpr.instL levels)).length ==
                          (entry.instL levels).np) = true := by
                      simpa using arity
                    simp only [arity, arityInst, if_true]
                    let value := VInductDecl.instRevParams entry.value
                      (expression.appArgs [])
                    have valueInst :
                        VInductDecl.instRevParams
                            (entry.instL levels).value
                            ((expression.appArgs []).map
                              (VExpr.instL levels)) =
                          value.instL levels := by
                      simpa [value] using
                        (VInductDecl.instRevParams_instL entry.value
                          (expression.appArgs []) levels).symm
                    rw [valueInst]
                    exact VInductDecl.restoreCtorResult_instL value suffix
                      levels
                  · simp [arity]

private theorem VInductDecl.restoreGetD_instL
    (restored : Option VExpr) (fallback : VExpr)
    (levels : List VLevel) :
    (restored.getD fallback).instL levels =
      (restored.map (VExpr.instL levels)).getD
        (fallback.instL levels) := by
  cases restored <;> rfl

/-- Restoring an artifact and then instantiating its universe parameters is
the same as instantiating the artifact and every replacement body first.
This is the universe-polymorphic bridge used by restored recursor programs. -/
theorem VInductDecl.restoreExpr_instL
    (entries : List VInductDecl.RestoreEntry)
    (recMap : List (Name × Name)) (expression : VExpr)
    (levels : List VLevel) :
    (VInductDecl.restoreExpr entries recMap expression).instL levels =
      VInductDecl.restoreExpr (entries.map (·.instL levels)) recMap
        (expression.instL levels) := by
  induction expression with
  | bvar | sort => rfl
  | const name nameLevels =>
      simp only [VInductDecl.restoreExpr]
      rw [VInductDecl.restoreGetD_instL]
      rw [VInductDecl.restoreSpine_instL]
      rfl
  | app function argument functionIH argumentIH =>
      simp only [VInductDecl.restoreExpr]
      rw [VInductDecl.restoreGetD_instL]
      rw [VInductDecl.restoreSpine_instL]
      simp only [VExpr.instL, functionIH, argumentIH]
      rfl
  | lam domain body domainIH bodyIH =>
      simp only [VInductDecl.restoreExpr, VExpr.instL, domainIH, bodyIH]
  | forallE domain body domainIH bodyIH =>
      simp only [VInductDecl.restoreExpr, VExpr.instL, domainIH, bodyIH]

/-- Runtime instance of recursor-world restoration.  `levels` is the full
universe spine supplied to the flattened recursor, so the pre-spliced
replacement entries are instantiated in exactly the same world as the
artifact being restored. -/
def VInductDecl.NestedBlockChecked.restoreRecAt
    {source : VInductDecl} (nested : source.NestedBlockChecked)
    (levels : List VLevel) (expression : VExpr) : VExpr :=
  VInductDecl.restoreExpr
    (nested.recEntries.map (·.instL levels)) nested.recMap expression

/-- Instantiating a restored recursor artifact is definitionally represented
by the runtime restoration inventory. -/
theorem VInductDecl.NestedBlockChecked.restoreRec_instL
    {source : VInductDecl} (nested : source.NestedBlockChecked)
    (expression : VExpr) (levels : List VLevel) :
    (nested.restoreRec expression).instL levels =
      nested.restoreRecAt levels (expression.instL levels) := by
  exact VInductDecl.restoreExpr_instL nested.recEntries nested.recMap
    expression levels

/-- Runtime restoration remains natural under a further universe
instantiation. -/
@[simp] theorem VInductDecl.NestedBlockChecked.restoreRecAt_instL
    {source : VInductDecl} (nested : source.NestedBlockChecked)
    (levels : List VLevel) (expression : VExpr) (extra : List VLevel) :
    (nested.restoreRecAt levels expression).instL extra =
      nested.restoreRecAt (levels.map (VLevel.inst extra))
        (expression.instL extra) := by
  unfold VInductDecl.NestedBlockChecked.restoreRecAt
  rw [VInductDecl.restoreExpr_instL]
  congr 1
  simp [List.map_map, Function.comp_def,
    VInductDecl.RestoreEntry.instL, VExpr.instL_instL]

/-- Every restoration replacement is closed over precisely the parameter
prefix consumed by its entry.  This is the necessary condition for
restoration to commute with ambient binder lifting. -/
def VInductDecl.RestoreEntriesClosed
    (entries : List VInductDecl.RestoreEntry) : Prop :=
  ∀ entry ∈ entries, entry.value.ClosedN entry.np

/-- Every replacement body has a constant application head.  Constructor
restoration inspects that head after consuming the parameter spine, so this
is the exact producer-shape invariant needed for restoration to commute with
ambient term substitution.  It is deliberately separate from closure: the
claim is false for an arbitrary parameter-closed replacement whose head is a
bound variable. -/
def VInductDecl.RestoreEntriesConstHead
    (entries : List VInductDecl.RestoreEntry) : Prop :=
  ∀ entry ∈ entries, ∃ name levels,
    entry.value.appHead = .const name levels

/-- Lifting distributes across an application head. -/
theorem VExpr.appHead_liftN (expression : VExpr) (count cutoff : Nat) :
    (expression.liftN count cutoff).appHead =
      expression.appHead.liftN count cutoff := by
  induction expression with
  | app function argument functionIH _ =>
      simpa [VExpr.liftN, VExpr.appHead] using functionIH
  | bvar | sort | const | lam | forallE => rfl

/-- Lifting maps every argument in an application spine. -/
theorem VExpr.appArgs_liftN (expression : VExpr)
    (arguments : List VExpr) (count cutoff : Nat) :
    (expression.liftN count cutoff).appArgs
        (arguments.map fun argument => argument.liftN count cutoff) =
      (expression.appArgs arguments).map
        fun argument => argument.liftN count cutoff := by
  induction expression generalizing arguments with
  | app function argument functionIH _ =>
      simpa [VExpr.liftN, VExpr.appArgs] using
        functionIH (argument :: arguments)
  | bvar | sort | const | lam | forallE => rfl

/-- General lifting law for simultaneous restoration-parameter
instantiation.  The replacement body is lifted above the entire consumed
parameter segment. -/
theorem VInductDecl.instRevParams_liftN_general
    (body : VExpr) (arguments : List VExpr) (count cutoff : Nat) :
    (VInductDecl.instRevParams body arguments).liftN count cutoff =
      VInductDecl.instRevParams
        (body.liftN count (cutoff + arguments.length))
        (arguments.map fun argument => argument.liftN count cutoff) := by
  induction arguments generalizing body with
  | nil => rfl
  | cons argument arguments ih =>
      simp only [VInductDecl.instRevParams, List.map_cons,
        List.length_cons]
      rw [ih]
      rw [VExpr.liftN_instN_hi]
      rw [show cutoff + (arguments.length + 1) =
        cutoff + arguments.length + 1 by omega]
      simp only [List.length_map]

/-- A parameter-closed replacement body therefore needs no lifting of its
own; only the runtime arguments are lifted. -/
theorem VInductDecl.instRevParams_liftN
    (body : VExpr) (arguments : List VExpr) (count cutoff : Nat)
    (closed : body.ClosedN arguments.length) :
    (VInductDecl.instRevParams body arguments).liftN count cutoff =
      VInductDecl.instRevParams body
        (arguments.map fun argument => argument.liftN count cutoff) := by
  rw [VInductDecl.instRevParams_liftN_general]
  rw [closed.liftN_eq (by omega)]

private theorem VInductDecl.mem_of_findRestoreCtor_eq_some
    {entries : List VInductDecl.RestoreEntry} {name suffix : Name}
    {entry : VInductDecl.RestoreEntry}
    (found : VInductDecl.findRestoreCtor entries name =
      some (entry, suffix)) : entry ∈ entries := by
  unfold VInductDecl.findRestoreCtor at found
  obtain ⟨candidate, member, selected⟩ :=
    List.exists_of_findSome?_eq_some found
  split at selected
  · have pairEq := Option.some.inj selected
    have entryEq : candidate = entry := by
      exact congrArg Prod.fst pairEq
    exact entryEq ▸ member
  · cases selected

private theorem VInductDecl.restoreCtorResult_liftN
    (value : VExpr) (suffix : Name) (count cutoff : Nat) :
    (match value.appHead with
      | VExpr.const target targetLevels =>
          some ((VExpr.const (target ++ suffix) targetLevels).appN
            (value.appArgs []))
      | _ => none).map
        (fun expression : VExpr => expression.liftN count cutoff) =
      match (value.liftN count cutoff).appHead with
      | VExpr.const target targetLevels =>
          some ((VExpr.const (target ++ suffix) targetLevels).appN
            ((value.liftN count cutoff).appArgs []))
      | _ => none := by
  rw [VExpr.appHead_liftN]
  cases head : value.appHead with
  | bvar | sort | app | lam | forallE => rfl
  | const target targetLevels =>
      simp only [VExpr.liftN, Option.map_some]
      rw [VExpr.liftN_appN]
      simp only [VExpr.liftN]
      have argsLift := VExpr.appArgs_liftN value [] count cutoff
      simp only [List.map_nil] at argsLift
      rw [argsLift]

private theorem VInductDecl.restoreSpine_liftN
    (entries : List VInductDecl.RestoreEntry)
    (closed : VInductDecl.RestoreEntriesClosed entries)
    (recMap : List (Name × Name)) (expression : VExpr)
    (count cutoff : Nat) :
    (VInductDecl.restoreExpr.restoreSpine entries recMap expression).map
        (fun result => result.liftN count cutoff) =
      VInductDecl.restoreExpr.restoreSpine entries recMap
        (expression.liftN count cutoff) := by
  unfold VInductDecl.restoreExpr.restoreSpine
  have headLift := VExpr.appHead_liftN expression count cutoff
  have argsLift := VExpr.appArgs_liftN expression [] count cutoff
  simp only [List.map_nil] at argsLift
  rw [headLift, argsLift]
  cases head : expression.appHead with
  | bvar | sort | app | lam | forallE => rfl
  | const name nameLevels =>
      simp only [VExpr.liftN]
      cases recursor : recMap.find? (·.1 == name) with
      | some renamed =>
          by_cases empty : (expression.appArgs []).isEmpty
          · simp [empty, List.isEmpty_map, VExpr.liftN]
          · simp [empty, List.isEmpty_map]
      | none =>
          cases entryFound : entries.find? (·.aux == name) with
          | some entry =>
              have entryClosed : entry.value.ClosedN entry.np :=
                closed entry (List.mem_of_find?_eq_some entryFound)
              by_cases arity :
                  (expression.appArgs []).length == entry.np
              · have lengthEq :
                    (expression.appArgs []).length = entry.np := by
                    simpa using arity
                have closedAt : entry.value.ClosedN
                    (expression.appArgs []).length := by
                  rw [lengthEq]
                  exact entryClosed
                have lifted := VInductDecl.instRevParams_liftN entry.value
                  (expression.appArgs []) count cutoff closedAt
                simpa only [arity, List.length_map, if_true,
                  Option.map_some] using congrArg some lifted
              · simp [arity]
          | none =>
              cases constructorFound :
                  VInductDecl.findRestoreCtor entries name with
              | none => simp
              | some result =>
                  obtain ⟨entry, suffix⟩ := result
                  have entryClosed : entry.value.ClosedN entry.np :=
                    closed entry
                      (VInductDecl.mem_of_findRestoreCtor_eq_some
                        constructorFound)
                  by_cases arity :
                      (expression.appArgs []).length == entry.np
                  · have arityLift :
                        (((expression.appArgs []).map fun argument =>
                            argument.liftN count cutoff).length ==
                          entry.np) = true := by
                      simpa using arity
                    simp only [arity, arityLift, if_true]
                    let value := VInductDecl.instRevParams entry.value
                      (expression.appArgs [])
                    have lengthEq :
                        (expression.appArgs []).length = entry.np := by
                      simpa using arity
                    have closedAt : entry.value.ClosedN
                        (expression.appArgs []).length := by
                      rw [lengthEq]
                      exact entryClosed
                    have valueLift :
                        VInductDecl.instRevParams entry.value
                            ((expression.appArgs []).map fun argument =>
                              argument.liftN count cutoff) =
                          value.liftN count cutoff := by
                      simpa [value] using
                        (VInductDecl.instRevParams_liftN entry.value
                          (expression.appArgs []) count cutoff
                          closedAt).symm
                    rw [valueLift]
                    exact VInductDecl.restoreCtorResult_liftN value suffix
                      count cutoff
                  · simp [arity]

private theorem VInductDecl.restoreGetD_liftN
    (restored : Option VExpr) (fallback : VExpr)
    (count cutoff : Nat) :
    (restored.getD fallback).liftN count cutoff =
      (restored.map fun result => result.liftN count cutoff).getD
        (fallback.liftN count cutoff) := by
  cases restored <;> rfl

/-- Under the exact replacement-closure condition, nested restoration
commutes with arbitrary ambient lifting. -/
theorem VInductDecl.restoreExpr_liftN
    (entries : List VInductDecl.RestoreEntry)
    (closed : VInductDecl.RestoreEntriesClosed entries)
    (recMap : List (Name × Name)) (expression : VExpr)
    (count cutoff : Nat) :
    (VInductDecl.restoreExpr entries recMap expression).liftN count cutoff =
      VInductDecl.restoreExpr entries recMap
        (expression.liftN count cutoff) := by
  induction expression generalizing cutoff with
  | bvar | sort => rfl
  | const name nameLevels =>
      simp only [VInductDecl.restoreExpr]
      rw [VInductDecl.restoreGetD_liftN]
      rw [VInductDecl.restoreSpine_liftN entries closed]
      rfl
  | app function argument functionIH argumentIH =>
      simp only [VInductDecl.restoreExpr]
      rw [VInductDecl.restoreGetD_liftN]
      rw [VInductDecl.restoreSpine_liftN entries closed]
      simp only [VExpr.liftN, functionIH, argumentIH]
      rfl
  | lam domain body domainIH bodyIH =>
      simp only [VInductDecl.restoreExpr, VExpr.liftN, domainIH, bodyIH]
  | forallE domain body domainIH bodyIH =>
      simp only [VInductDecl.restoreExpr, VExpr.liftN, domainIH, bodyIH]

/-- Pointwise restoration commutes with the progressive lifting used to
embed a telescope beneath a shared binder prefix. -/
theorem VInductDecl.restoreExpr_liftTelN
    (entries : List VInductDecl.RestoreEntry)
    (closed : VInductDecl.RestoreEntriesClosed entries)
    (recMap : List (Name × Name)) (count : Nat) :
    ∀ (telescope : List VExpr) (cutoff : Nat),
      (VExpr.liftTelN count telescope cutoff).map
          (VInductDecl.restoreExpr entries recMap) =
        VExpr.liftTelN count
          (telescope.map (VInductDecl.restoreExpr entries recMap)) cutoff := by
  intro telescope
  induction telescope with
  | nil => intro cutoff; rfl
  | cons field fields ih =>
      intro cutoff
      simp only [VExpr.liftTelN, List.map_cons]
      rw [VInductDecl.restoreExpr_liftN entries closed recMap field]
      rw [ih (cutoff + 1)]

/-- A parameter-closed restoration inventory preserves every ambient
closedness boundary.  Lift naturality reduces the claim to the primitive
characterization of closed expressions by an inert one-variable lift. -/
theorem VInductDecl.restoreExpr_closedN
    (entries : List VInductDecl.RestoreEntry)
    (entriesClosed : VInductDecl.RestoreEntriesClosed entries)
    (recMap : List (Name × Name)) {expression : VExpr} {cutoff : Nat}
    (expressionClosed : expression.ClosedN cutoff) :
    (VInductDecl.restoreExpr entries recMap expression).ClosedN cutoff := by
  apply VExpr.closedN_of_liftN_one_eq _ cutoff
  rw [VInductDecl.restoreExpr_liftN entries entriesClosed]
  rw [expressionClosed.liftN_eq (Nat.le_refl cutoff)]

/-- Universe-instantiating a closed replacement inventory preserves its
parameter closure. -/
theorem VInductDecl.RestoreEntriesClosed.instL
    {entries : List VInductDecl.RestoreEntry}
    (closed : VInductDecl.RestoreEntriesClosed entries)
    (levels : List VLevel) :
    VInductDecl.RestoreEntriesClosed
      (entries.map (·.instL levels)) := by
  intro entry member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  simpa [VInductDecl.RestoreEntry.instL] using
    (closed original originalMember).instL (ls := levels)

/-- Universe instantiation changes only the universe payload of a constant
application head, so it preserves the exact head-shape invariant. -/
theorem VInductDecl.RestoreEntriesConstHead.instL
    {entries : List VInductDecl.RestoreEntry}
    (heads : VInductDecl.RestoreEntriesConstHead entries)
    (levels : List VLevel) :
    VInductDecl.RestoreEntriesConstHead
      (entries.map (·.instL levels)) := by
  intro entry member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨name, nameLevels, head⟩ := heads original originalMember
  refine ⟨name, nameLevels.map (VLevel.inst levels), ?_⟩
  rw [VInductDecl.RestoreEntry.instL_value,
    VExpr.appHead_instL, head]
  rfl

/-- Declaration-world entries emitted by nested elimination are
definitionally headed by their retained target family. -/
theorem VInductDecl.NestedBlockChecked.declEntriesConstHead
    {source : VInductDecl} (nested : source.NestedBlockChecked) :
    VInductDecl.RestoreEntriesConstHead nested.declEntries := by
  intro entry member
  unfold VInductDecl.NestedBlockChecked.declEntries at member
  obtain ⟨spec, _specMember, rfl⟩ := List.mem_map.mp member
  refine ⟨spec.target, spec.levels, ?_⟩
  simp [VInductDecl.NestedAuxSpec.value, VExpr.appHead_appN,
    VExpr.appHead]

/-- Recursor-world entries retain the same constant heads after the
producer's universe-offset instantiation. -/
theorem VInductDecl.NestedBlockChecked.recEntriesConstHead
    {source : VInductDecl} (nested : source.NestedBlockChecked) :
    VInductDecl.RestoreEntriesConstHead nested.recEntries := by
  intro entry member
  unfold VInductDecl.NestedBlockChecked.recEntries at member
  obtain ⟨spec, _specMember, rfl⟩ := List.mem_map.mp member
  refine ⟨spec.target,
    spec.levels.map (VLevel.inst (VLevel.params' source.uvars
      (nested.generation.recUvars - source.uvars))), ?_⟩
  rw [VExpr.appHead_instL]
  simp [VInductDecl.NestedAuxSpec.value, VExpr.appHead_appN,
    VExpr.appHead, VExpr.instL]

/-- Runtime recursor restoration commutes with ambient lifting once the
producer's replacement inventory is known parameter-closed. -/
theorem VInductDecl.NestedBlockChecked.restoreRecAt_liftN
    {source : VInductDecl} (nested : source.NestedBlockChecked)
    (closed : VInductDecl.RestoreEntriesClosed nested.recEntries)
    (levels : List VLevel) (expression : VExpr)
    (count cutoff : Nat) :
    (nested.restoreRecAt levels expression).liftN count cutoff =
      nested.restoreRecAt levels (expression.liftN count cutoff) := by
  exact VInductDecl.restoreExpr_liftN _ (closed.instL levels)
    nested.recMap expression count cutoff

/--
info: 'Lean4Lean.VInductDecl.restoreExpr_instL' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms VInductDecl.restoreExpr_instL

/--
info: 'Lean4Lean.VInductDecl.restoreExpr_liftN' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in
#print axioms VInductDecl.restoreExpr_liftN

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

/-- An expression mentions no constant on which nested restoration can
fire.  This is a source-syntax property used internally to prove that the
parts untouched by flattening are also untouched by restoration. -/
def RestoreInert (entries : List RestoreEntry)
    (recMap : List (Name × Name)) (expression : VExpr) : Prop :=
  ∀ name, expression.hasConst name = true →
    recMap.find? (·.1 == name) = none ∧
      entries.find? (·.aux == name) = none ∧
        findRestoreCtor entries name = none

/-- Any occurring constant below an auxiliary-family prefix is detected by
the executable restoration-domain scan. -/
theorem VExpr.hasNestedRestoreConst_of_hasConst
    {specs : List NestedAuxSpec} {expression : VExpr}
    {name : Name} {spec : NestedAuxSpec}
    (member : spec ∈ specs)
    (isPrefixed : spec.aux.isPrefixOf name = true)
    (present : expression.hasConst name = true) :
    expression.hasNestedRestoreConst specs = true := by
  induction expression with
  | bvar | sort => simp [VExpr.hasConst] at present
  | const constant levels =>
      simp only [VExpr.hasConst, beq_iff_eq] at present
      subst constant
      simp only [VExpr.hasNestedRestoreConst, List.any_eq_true]
      exact ⟨spec, member, isPrefixed⟩
  | app function argument functionIH argumentIH =>
      simp only [VExpr.hasConst, Bool.or_eq_true] at present
      simp only [VExpr.hasNestedRestoreConst, Bool.or_eq_true]
      rcases present with functionPresent | argumentPresent
      · exact .inl (functionIH functionPresent)
      · exact .inr (argumentIH argumentPresent)
  | lam domain body domainIH bodyIH =>
      simp only [VExpr.hasConst, Bool.or_eq_true] at present
      simp only [VExpr.hasNestedRestoreConst, Bool.or_eq_true]
      rcases present with domainPresent | bodyPresent
      · exact .inl (domainIH domainPresent)
      · exact .inr (bodyIH bodyPresent)
  | forallE domain body domainIH bodyIH =>
      simp only [VExpr.hasConst, Bool.or_eq_true] at present
      simp only [VExpr.hasNestedRestoreConst, Bool.or_eq_true]
      rcases present with domainPresent | bodyPresent
      · exact .inl (domainIH domainPresent)
      · exact .inr (bodyIH bodyPresent)

private theorem Name.isPrefixOf_self_eq_true (name : Name) :
    name.isPrefixOf name = true := by
  induction name with
  | anonymous => rfl
  | str parent suffix ih =>
      change (((.str parent suffix : Name) ==
        (.str parent suffix : Name)) || _) = true
      simp
  | num parent index ih =>
      change (((.num parent index : Name) ==
        (.num parent index : Name)) || _) = true
      simp

private theorem Name.isPrefixOf_str_eq_true (name : Name) (suffix : String) :
    name.isPrefixOf (.str name suffix) = true := by
  change ((name == .str name suffix) || name.isPrefixOf name) = true
  rw [Name.isPrefixOf_self_eq_true]
  simp

/-- Project the retained block-wide restoration gate to one exact source
family head. -/
theorem NestedBlockChecked.sourceFamilyName_restoreSafe
    {source : VInductDecl} (nested : source.NestedBlockChecked)
    {family : VInductiveType} (familyMember : family ∈ source.types) :
    (VExpr.const family.name []).hasNestedRestoreConst
      nested.elim.specs = false := by
  have safe := nested.source_restore_safe
  simp only [nestedRestoreSafe, List.all_eq_true, Bool.and_eq_true,
    Bool.not_eq_true'] at safe
  exact (safe family familyMember).1

/-- Project the retained block-wide restoration gate to one exact source
constructor head. -/
theorem NestedBlockChecked.sourceConstructorName_restoreSafe
    {source : VInductDecl} (nested : source.NestedBlockChecked)
    {family : VInductiveType} (familyMember : family ∈ source.types)
    {constructor : VConstVal} (constructorMember : constructor ∈ family.ctors) :
    (VExpr.const constructor.name []).hasNestedRestoreConst
      nested.elim.specs = false := by
  have safe := nested.source_restore_safe
  simp only [nestedRestoreSafe, List.all_eq_true, Bool.and_eq_true,
    Bool.not_eq_true'] at safe
  exact ((safe family familyMember).2 constructor constructorMember).1

/-- Project the retained block-wide restoration gate to one exact source
constructor type. -/
theorem NestedBlockChecked.sourceConstructor_restoreSafe
    {source : VInductDecl} (nested : source.NestedBlockChecked)
    {family : VInductiveType} (familyMember : family ∈ source.types)
    {constructor : VConstVal} (constructorMember : constructor ∈ family.ctors) :
    constructor.type.hasNestedRestoreConst nested.elim.specs = false := by
  have safe := nested.source_restore_safe
  simp only [nestedRestoreSafe, List.all_eq_true, Bool.and_eq_true,
    Bool.not_eq_true'] at safe
  exact ((safe family familyMember).2 constructor constructorMember).2

/-- Any successful restoration-domain scan discharges restoration inertness
for the exact producer inventory retained by the nested certificate. -/
theorem NestedBlockChecked.restoreInert_of_restoreSafe
    {source : VInductDecl} (nested : source.NestedBlockChecked)
    {expression : VExpr}
    (safe : expression.hasNestedRestoreConst nested.elim.specs = false) :
    RestoreInert nested.declEntries nested.recMap expression := by
  intro name present
  have prefixFalse : ∀ spec ∈ nested.elim.specs,
      spec.aux.isPrefixOf name = false := by
    intro spec specMember
    cases prefixEq : spec.aux.isPrefixOf name with
    | false => rfl
    | true =>
        have detected := VExpr.hasNestedRestoreConst_of_hasConst
          specMember prefixEq present
        rw [safe] at detected
        contradiction
  refine ⟨?_, ?_, ?_⟩
  · unfold NestedBlockChecked.recMap
    rw [List.find?_eq_none]
    intro entry entryMember
    obtain ⟨index, upper, entryEq⟩ := List.mem_mapIdx.mp entryMember
    let spec := nested.elim.specs[index]
    have specMember : spec ∈ nested.elim.specs := List.getElem_mem upper
    rw [← entryEq]
    intro equal
    rw [beq_iff_eq] at equal
    have prefixed : spec.aux.isPrefixOf name = true := by
      rw [← equal]
      exact Name.isPrefixOf_str_eq_true _ _
    rw [prefixFalse spec specMember] at prefixed
    contradiction
  · unfold NestedBlockChecked.declEntries
    rw [List.find?_eq_none]
    intro entry entryMember
    obtain ⟨spec, specMember, entryEq⟩ := List.mem_map.mp entryMember
    rw [← entryEq]
    intro equal
    rw [beq_iff_eq] at equal
    have prefixed : spec.aux.isPrefixOf name = true := by
      rw [← equal]
      exact Name.isPrefixOf_self_eq_true _
    rw [prefixFalse spec specMember] at prefixed
    contradiction
  · unfold findRestoreCtor
    rw [List.findSome?_eq_none_iff]
    intro entry entryMember
    obtain ⟨spec, specMember, entryEq⟩ := List.mem_map.mp entryMember
    rw [← entryEq]
    simp [prefixFalse spec specMember]

/-- A checked source family constant is inert under restoration at every
universe instantiation. -/
theorem NestedBlockChecked.sourceFamilyName_restoreInert
    {source : VInductDecl} (nested : source.NestedBlockChecked)
    {family : VInductiveType} (familyMember : family ∈ source.types)
    (levels : List VLevel) :
    RestoreInert nested.declEntries nested.recMap
      (.const family.name levels) := by
  apply nested.restoreInert_of_restoreSafe
  simpa [VExpr.hasNestedRestoreConst] using
    nested.sourceFamilyName_restoreSafe familyMember

/-- A checked source constructor constant is inert under restoration at every
universe instantiation. -/
theorem NestedBlockChecked.sourceConstructorName_restoreInert
    {source : VInductDecl} (nested : source.NestedBlockChecked)
    {family : VInductiveType} (familyMember : family ∈ source.types)
    {constructor : VConstVal} (constructorMember : constructor ∈ family.ctors)
    (levels : List VLevel) :
    RestoreInert nested.declEntries nested.recMap
      (.const constructor.name levels) := by
  apply nested.restoreInert_of_restoreSafe
  simpa [VExpr.hasNestedRestoreConst] using
    nested.sourceConstructorName_restoreSafe familyMember constructorMember

/-- The checked restoration-domain gate discharges the exact inertness
premise needed when the producer trace restores an original constructor
body. -/
theorem NestedBlockChecked.sourceConstructor_restoreInert
    {source : VInductDecl} (nested : source.NestedBlockChecked)
    {family : VInductiveType} (familyMember : family ∈ source.types)
    {constructor : VConstVal} (constructorMember : constructor ∈ family.ctors) :
    RestoreInert nested.declEntries nested.recMap constructor.type :=
  nested.restoreInert_of_restoreSafe
    (nested.sourceConstructor_restoreSafe familyMember constructorMember)

/-- Inertness descends to any expression whose constants all occur in the
original expression. -/
theorem RestoreInert.of_hasConst
    {entries : List RestoreEntry} {recMap : List (Name × Name)}
    {expression child : VExpr}
    (inert : RestoreInert entries recMap expression)
    (contained : ∀ name, child.hasConst name = true →
      expression.hasConst name = true) :
    RestoreInert entries recMap child := by
  intro name present
  exact inert name (contained name present)

/-- Restoration inertness is closed under application. -/
theorem RestoreInert.app
    {entries : List RestoreEntry} {recMap : List (Name × Name)}
    {function argument : VExpr}
    (functionInert : RestoreInert entries recMap function)
    (argumentInert : RestoreInert entries recMap argument) :
    RestoreInert entries recMap (.app function argument) := by
  intro name present
  simp only [VExpr.hasConst, Bool.or_eq_true] at present
  exact present.elim (functionInert name) (argumentInert name)

/-- Restoration inertness is closed under an arbitrary application spine. -/
theorem RestoreInert.appN
    {entries : List RestoreEntry} {recMap : List (Name × Name)}
    {function : VExpr} {arguments : List VExpr}
    (functionInert : RestoreInert entries recMap function)
    (argumentsInert : ∀ argument ∈ arguments,
      RestoreInert entries recMap argument) :
    RestoreInert entries recMap (VExpr.appN function arguments) := by
  induction arguments generalizing function with
  | nil => exact functionInert
  | cons argument arguments ih =>
      apply ih (functionInert.app
        (argumentsInert argument (by simp)))
      intro trailing trailingMember
      exact argumentsInert trailing (by simp [trailingMember])

/-- Binder lifting preserves every occurring constant and hence preserves
restoration inertness. -/
theorem RestoreInert.liftN
    {entries : List RestoreEntry} {recMap : List (Name × Name)}
    {expression : VExpr}
    (inert : RestoreInert entries recMap expression)
    (count cutoff : Nat) :
    RestoreInert entries recMap (expression.liftN count cutoff) := by
  intro name present
  apply inert name
  rw [← VExpr.lift'_consN_skipN, VExpr.hasConst_lift'] at present
  exact present

/-- Instantiating restoration-entry payloads leaves the executable
restoration domain unchanged. -/
theorem RestoreInert.instLEntries
    {entries : List RestoreEntry} {recMap : List (Name × Name)}
    {expression : VExpr}
    (inert : RestoreInert entries recMap expression)
    (levels : List VLevel) :
    RestoreInert (entries.map (·.instL levels)) recMap expression := by
  intro name present
  obtain ⟨recursor, entry, constructor⟩ := inert name present
  refine ⟨recursor, ?_, ?_⟩
  · rw [VInductDecl.findEntry_instL, entry]
    rfl
  · rw [VInductDecl.findRestoreCtor_instL, constructor]
    rfl

/-- Declaration-world inertness transports to the exact recursor-world
inventory retained by the checked nested producer. -/
theorem NestedBlockChecked.restoreInert_recEntries
    {source : VInductDecl} (nested : source.NestedBlockChecked)
    {expression : VExpr}
    (inert : RestoreInert nested.declEntries nested.recMap expression) :
    RestoreInert nested.recEntries nested.recMap expression := by
  have instantiated := inert.instLEntries
    (VLevel.params' source.uvars
      (nested.generation.recUvars - source.uvars))
  simpa [NestedBlockChecked.recEntries, NestedBlockChecked.declEntries,
    RestoreEntry.instL, List.map_map, Function.comp_def] using instantiated

/-- A checked source family constant is inert in the producer's recursor
universe world at every universe instantiation. -/
theorem NestedBlockChecked.sourceFamilyName_restoreRecInert
    {source : VInductDecl} (nested : source.NestedBlockChecked)
    {family : VInductiveType} (familyMember : family ∈ source.types)
    (levels : List VLevel) :
    RestoreInert nested.recEntries nested.recMap
      (.const family.name levels) :=
  nested.restoreInert_recEntries
    (nested.sourceFamilyName_restoreInert familyMember levels)

/-- A checked source constructor constant is inert in the producer's
recursor universe world at every universe instantiation. -/
theorem NestedBlockChecked.sourceConstructorName_restoreRecInert
    {source : VInductDecl} (nested : source.NestedBlockChecked)
    {family : VInductiveType} (familyMember : family ∈ source.types)
    {constructor : VConstVal} (constructorMember : constructor ∈ family.ctors)
    (levels : List VLevel) :
    RestoreInert nested.recEntries nested.recMap
      (.const constructor.name levels) :=
  nested.restoreInert_recEntries
    (nested.sourceConstructorName_restoreInert familyMember
      constructorMember levels)

/-- No auxiliary family retained by nested elimination can have the name of
an original source recursor.  The producer's complete generated-name
inventory separates the auxiliary family segment from every recursor name. -/
theorem NestedBlockChecked.sourceRecursorName_ne_aux
    {source : VInductDecl} (nested : source.NestedBlockChecked)
    {family : VInductiveType} (familyMember : family ∈ source.types)
    {spec : NestedAuxSpec} (specMember : spec ∈ nested.elim.specs) :
    (.str family.name "rec" : Name) ≠ spec.aux := by
  have generatedNodup :
      (blockGeneratedNames
        nested.generation.block.normalization.view.types).Nodup := by
    rw [← nested.generation.checked.names_eq]
    exact nested.generation.checked.names_nodup
  let viewFamilies :=
    nested.generation.block.normalization.view.types.map (·.name)
  let viewConstructors :=
    nested.generation.block.normalization.view.types.flatMap
      fun family => family.ctors.map (·.name)
  let viewRecursors :=
    nested.generation.block.normalization.view.types.map
      fun family => (.str family.name "rec" : Name)
  have generatedShape : blockGeneratedNames
      nested.generation.block.normalization.view.types =
      (viewFamilies ++ viewConstructors) ++ viewRecursors := by
    rfl
  rw [generatedShape] at generatedNodup
  have disjoint := (List.nodup_append.mp generatedNodup).2.2
  have rawViewFamilyNames :
      nested.elim.flat.types.map (·.name) = viewFamilies := by
    dsimp [viewFamilies]
    rw [← nested.generation.families_map_raw,
      ← CheckedFamilies.data_map_value
        nested.generation.block.checked.families,
      ← nested.generation.families_map_view]
    simp only [List.map_map]
    apply List.map_congr_left
    intro candidate member
    exact (nested.generation.shape.2.2.2.2 candidate member).1
  have specRaw : spec.aux ∈ nested.elim.flat.types.map (·.name) := by
    rw [nested.elim.specsAligned]
    exact List.mem_append.mpr
      (.inr (List.mem_map_of_mem specMember))
  have familyRaw : family.name ∈ nested.elim.flat.types.map (·.name) := by
    rw [nested.elim.specsAligned]
    exact List.mem_append.mpr
      (.inl (List.mem_map_of_mem familyMember))
  have specView : spec.aux ∈ viewFamilies := by
    rw [← rawViewFamilyNames]
    exact specRaw
  have familyView : family.name ∈ viewFamilies := by
    rw [← rawViewFamilyNames]
    exact familyRaw
  have recView : (.str family.name "rec" : Name) ∈ viewRecursors := by
    dsimp [viewFamilies] at familyView
    dsimp [viewRecursors]
    obtain ⟨viewFamily, viewFamilyMember, nameEq⟩ :=
      List.mem_map.1 familyView
    exact List.mem_map.2
      ⟨viewFamily, viewFamilyMember, by rw [nameEq]⟩
  intro equal
  exact (disjoint spec.aux
    (List.mem_append_left viewConstructors specView)
    (.str family.name "rec") recView) equal.symm

/-- An original source recursor name is outside every auxiliary restoration
prefix.  Appending the conventional `rec` suffix can only introduce the
exact auxiliary name, which generated-name disjointness rules out. -/
theorem NestedBlockChecked.sourceRecursorName_restoreSafe
    {source : VInductDecl} (nested : source.NestedBlockChecked)
    {family : VInductiveType} (familyMember : family ∈ source.types) :
    (VExpr.const (.str family.name "rec") []).hasNestedRestoreConst
      nested.elim.specs = false := by
  have familySafe := nested.sourceFamilyName_restoreSafe familyMember
  simp only [VExpr.hasNestedRestoreConst, List.any_eq_false] at familySafe ⊢
  intro spec specMember
  have base := familySafe spec specMember
  have different := nested.sourceRecursorName_ne_aux
    familyMember specMember
  intro prefixed
  change ((spec.aux == (.str family.name "rec" : Name)) ||
    spec.aux.isPrefixOf family.name) = true at prefixed
  rw [Bool.or_eq_true] at prefixed
  rcases prefixed with equal | basePrefixed
  · rw [beq_iff_eq] at equal
    exact different equal.symm
  · exact base basePrefixed

/-- A checked original source recursor is inert in the producer's recursor
restoration world at every universe instantiation. -/
theorem NestedBlockChecked.sourceRecursorName_restoreRecInert
    {source : VInductDecl} (nested : source.NestedBlockChecked)
    {family : VInductiveType} (familyMember : family ∈ source.types)
    (levels : List VLevel) :
    RestoreInert nested.recEntries nested.recMap
      (.const (.str family.name "rec") levels) := by
  apply nested.restoreInert_recEntries
  apply nested.restoreInert_of_restoreSafe
  simpa [VExpr.hasNestedRestoreConst] using
    nested.sourceRecursorName_restoreSafe familyMember

/-- Inertness descends to every argument extracted from an application
spine. -/
theorem RestoreInert.appArgs
    {entries : List RestoreEntry} {recMap : List (Name × Name)}
    {expression argument : VExpr}
    (inert : RestoreInert entries recMap expression)
    (member : argument ∈ expression.appArgs []) :
    RestoreInert entries recMap argument :=
  inert.of_hasConst fun _ present =>
    VExpr.hasConst_of_mem_appArgs member present

/-- Inertness descends through a stripped Pi prefix. -/
theorem RestoreInert.dropN
    {entries : List RestoreEntry} {recMap : List (Name × Name)} :
    ∀ (count : Nat) {expression : VExpr},
      RestoreInert entries recMap expression →
      RestoreInert entries recMap (VExpr.dropN count expression)
  | 0, _, inert => inert
  | count + 1, .forallE domain body, inert => by
      apply RestoreInert.dropN count
      exact inert.of_hasConst fun _ present => by
        simp only [VExpr.hasConst, Bool.or_eq_true]
        exact .inr present
  | _ + 1, .bvar _, inert => inert
  | _ + 1, .sort _, inert => inert
  | _ + 1, .const _ _, inert => inert
  | _ + 1, .app _ _, inert => inert
  | _ + 1, .lam _ _, inert => inert

/-- Every binder domain extracted from an inert Pi telescope is inert. -/
theorem RestoreInert.telN
    {entries : List RestoreEntry} {recMap : List (Name × Name)} :
    ∀ (count : Nat) {expression : VExpr},
      RestoreInert entries recMap expression →
      ∀ domain ∈ VExpr.telN count expression,
        RestoreInert entries recMap domain
  | 0, _, _, _, member => by simp [VExpr.telN] at member
  | count + 1, .forallE domain body, inert, candidate, member => by
      simp only [VExpr.telN, List.mem_cons] at member
      rcases member with rfl | member
      · exact inert.of_hasConst fun _ present => by
          simp only [VExpr.hasConst, Bool.or_eq_true]
          exact .inl present
      · apply RestoreInert.telN count
          (inert.of_hasConst fun _ present => by
            simp only [VExpr.hasConst, Bool.or_eq_true]
            exact .inr present)
          candidate member
  | _ + 1, .bvar _, _, _, member => by simp [VExpr.telN] at member
  | _ + 1, .sort _, _, _, member => by simp [VExpr.telN] at member
  | _ + 1, .const _ _, _, _, member => by simp [VExpr.telN] at member
  | _ + 1, .app _ _, _, _, member => by simp [VExpr.telN] at member
  | _ + 1, .lam _ _, _, _, member => by simp [VExpr.telN] at member

private theorem restoreSpine_eq_none_of_inert
    {entries : List RestoreEntry} {recMap : List (Name × Name)}
    {expression : VExpr}
    (inert : RestoreInert entries recMap expression) :
    restoreExpr.restoreSpine entries recMap expression = none := by
  unfold restoreExpr.restoreSpine
  cases headEq : expression.appHead with
  | const name levels =>
      simp only
      obtain ⟨hrec, hentry, hctor⟩ := inert name
        (VExpr.hasConst_of_appHead_eq_const headEq)
      rw [hrec, hentry, hctor]
  | bvar index => rfl
  | sort level => rfl
  | app function argument => rfl
  | lam domain body => rfl
  | forallE domain body => rfl

/-- Nested restoration is the identity on an inert expression. -/
theorem RestoreInert.restoreExpr_eq
    {entries : List RestoreEntry} {recMap : List (Name × Name)} :
    ∀ {expression : VExpr}, RestoreInert entries recMap expression →
      restoreExpr entries recMap expression = expression
  | .bvar _, _ => rfl
  | .sort _, _ => rfl
  | .const name levels, inert => by
      change (restoreExpr.restoreSpine entries recMap (.const name levels)).getD
        (.const name levels) = .const name levels
      rw [restoreSpine_eq_none_of_inert inert]
      rfl
  | .app function argument, inert => by
      have functionInert : RestoreInert entries recMap function :=
        inert.of_hasConst fun _ present => by
          simp only [VExpr.hasConst, Bool.or_eq_true]
          exact .inl present
      have argumentInert : RestoreInert entries recMap argument :=
        inert.of_hasConst fun _ present => by
          simp only [VExpr.hasConst, Bool.or_eq_true]
          exact .inr present
      change (restoreExpr.restoreSpine entries recMap
        ((restoreExpr entries recMap function).app
          (restoreExpr entries recMap argument))).getD _ =
            .app function argument
      rw [functionInert.restoreExpr_eq, argumentInert.restoreExpr_eq,
        restoreSpine_eq_none_of_inert inert]
      rfl
  | .lam domain body, inert => by
      have domainInert : RestoreInert entries recMap domain :=
        inert.of_hasConst fun _ present => by
          simp only [VExpr.hasConst, Bool.or_eq_true]
          exact .inl present
      have bodyInert : RestoreInert entries recMap body :=
        inert.of_hasConst fun _ present => by
          simp only [VExpr.hasConst, Bool.or_eq_true]
          exact .inr present
      simp only [restoreExpr, domainInert.restoreExpr_eq,
        bodyInert.restoreExpr_eq]
  | .forallE domain body, inert => by
      have domainInert : RestoreInert entries recMap domain :=
        inert.of_hasConst fun _ present => by
          simp only [VExpr.hasConst, Bool.or_eq_true]
          exact .inl present
      have bodyInert : RestoreInert entries recMap body :=
        inert.of_hasConst fun _ present => by
          simp only [VExpr.hasConst, Bool.or_eq_true]
          exact .inr present
      simp only [restoreExpr, domainInert.restoreExpr_eq,
        bodyInert.restoreExpr_eq]

/-! ## Term instantiation of nested restoration

Unlike universe instantiation and lifting, ambient term instantiation can
replace an application head.  The inertness premise below rules out a new
restoration redex in that case; `RestoreEntriesConstHead` handles the other
head-sensitive operation, auxiliary-constructor restoration. -/

/-- A constant application head is stable under ambient term
instantiation. -/
private theorem VExpr.appHead_instN_of_eq_const
    {expression : VExpr} {name : Name} {levels : List VLevel}
    (head : expression.appHead = .const name levels)
    (argument : VExpr) (cutoff : Nat) :
    (expression.inst argument cutoff).appHead = .const name levels := by
  have reconstructed :
      VExpr.appN expression.appHead (expression.appArgs []) = expression := by
    simpa [VExpr.appN] using VExpr.appN_appHead_appArgs expression []
  rw [head] at reconstructed
  calc
    (expression.inst argument cutoff).appHead =
        ((VExpr.const name levels).appN (expression.appArgs [])
          |>.inst argument cutoff).appHead := by rw [reconstructed]
    _ = .const name levels := by
      rw [VExpr.instN_appN, VExpr.appHead_appN]
      rfl

/-- When the application head is constant, term instantiation maps exactly
the extracted application arguments. -/
private theorem VExpr.appArgs_instN_of_appHead_eq_const
    {expression : VExpr} {name : Name} {levels : List VLevel}
    (head : expression.appHead = .const name levels)
    (argument : VExpr) (cutoff : Nat) :
    (expression.inst argument cutoff).appArgs [] =
      (expression.appArgs []).map (·.inst argument cutoff) := by
  have reconstructed :
      VExpr.appN expression.appHead (expression.appArgs []) = expression := by
    simpa [VExpr.appN] using VExpr.appN_appHead_appArgs expression []
  rw [head] at reconstructed
  calc
    (expression.inst argument cutoff).appArgs [] =
        ((VExpr.const name levels).appN (expression.appArgs [])
          |>.inst argument cutoff).appArgs [] := by rw [reconstructed]
    _ = (expression.appArgs []).map (·.inst argument cutoff) := by
      rw [VExpr.instN_appN, VExpr.appArgs_appN]
      simp [VExpr.inst, VExpr.appArgs]

/-- General interchange law between the producer's simultaneous parameter
instantiation and one ambient term instantiation. -/
theorem instRevParams_instN_general
    (body : VExpr) (arguments : List VExpr)
    (argument : VExpr) (cutoff : Nat) :
    (instRevParams body arguments).inst argument cutoff =
      instRevParams (body.inst argument (cutoff + arguments.length))
        (arguments.map (·.inst argument cutoff)) := by
  induction arguments generalizing body with
  | nil => simp [instRevParams]
  | cons parameter parameters ih =>
      simp only [instRevParams, List.map_cons]
      rw [ih]
      simp only [List.length_cons, List.length_map]
      rw [VExpr.inst_inst_hi]
      congr 3 <;> omega

/-- If the replacement body is closed over precisely the consumed parameter
spine, only the runtime arguments need ambient instantiation. -/
theorem instRevParams_instN
    (body : VExpr) (arguments : List VExpr)
    (argument : VExpr) (cutoff : Nat)
    (closed : body.ClosedN arguments.length) :
    (instRevParams body arguments).inst argument cutoff =
      instRevParams body
        (arguments.map (·.inst argument cutoff)) := by
  rw [instRevParams_instN_general]
  rw [closed.instN_eq (by omega)]

/-- Consuming parameters preserves a retained constant head. -/
private theorem instRevParams_appHead_eq_const
    {body : VExpr} {name : Name} {levels : List VLevel}
    (head : body.appHead = .const name levels) :
    ∀ arguments : List VExpr,
      (instRevParams body arguments).appHead = .const name levels
  | [] => head
  | argument :: arguments => by
      apply instRevParams_appHead_eq_const
        (body := body.inst argument arguments.length)
      exact VExpr.appHead_instN_of_eq_const head argument arguments.length

/-- Constructor-target rebuilding commutes with ambient substitution once
the instantiated auxiliary value has its producer-guaranteed constant
head. -/
private theorem restoreCtorResult_instN
    (value : VExpr) (suffix : Name) (argument : VExpr) (cutoff : Nat)
    {target : Name} {targetLevels : List VLevel}
    (head : value.appHead = .const target targetLevels) :
    (match value.appHead with
      | VExpr.const target targetLevels =>
          some ((VExpr.const (target ++ suffix) targetLevels).appN
            (value.appArgs []))
      | _ => none).map (fun result : VExpr =>
        result.inst argument cutoff) =
      match (value.inst argument cutoff).appHead with
      | VExpr.const target targetLevels =>
          some ((VExpr.const (target ++ suffix) targetLevels).appN
            ((value.inst argument cutoff).appArgs []))
      | _ => none := by
  have headInst := VExpr.appHead_instN_of_eq_const head argument cutoff
  have argsInst := VExpr.appArgs_instN_of_appHead_eq_const head argument cutoff
  rw [head, headInst]
  simp only [Option.map_some, VExpr.instN_appN, VExpr.inst]
  rw [argsInst]

/-- Extending an application spine whose function is inert cannot create a
restoration redex at the outer spine node. -/
private theorem restoreSpine_appN_eq_none_of_function_inert
    {entries : List RestoreEntry} {recMap : List (Name × Name)}
    (function : VExpr) (arguments : List VExpr)
    (inert : RestoreInert entries recMap function) :
    restoreExpr.restoreSpine entries recMap
        (VExpr.appN function arguments) = none := by
  unfold restoreExpr.restoreSpine
  rw [VExpr.appHead_appN, VExpr.appArgs_appN]
  simp only [List.append_nil]
  cases head : function.appHead with
  | const name levels =>
      simp only
      obtain ⟨recursor, entry, constructor⟩ := inert name
        (VExpr.hasConst_of_appHead_eq_const head)
      rw [recursor, entry, constructor]
  | bvar | sort | app | lam | forallE => rfl

/-- Instantiating a bound-variable head by an inert argument still leaves
that head outside the restoration domain. -/
private theorem RestoreInert.instVar
    {entries : List RestoreEntry} {recMap : List (Name × Name)}
    {argument : VExpr}
    (inert : RestoreInert entries recMap argument)
    (index cutoff : Nat) :
    RestoreInert entries recMap (VExpr.instVar index argument cutoff) := by
  unfold VExpr.instVar
  split
  · intro name present
    simp [VExpr.hasConst] at present
  · split
    · exact inert.liftN cutoff 0
    · intro name present
      simp [VExpr.hasConst] at present

/-- Under the exact producer invariants, one ambient term instantiation
commutes with the head-sensitive restoration decision on an application
spine. -/
private theorem restoreSpine_appN_instN
    (entries : List RestoreEntry)
    (closed : RestoreEntriesClosed entries)
    (heads : RestoreEntriesConstHead entries)
    (recMap : List (Name × Name))
    (function : VExpr) (arguments : List VExpr)
    (argument : VExpr) (cutoff : Nat)
    (argumentInert : RestoreInert entries recMap argument) :
    (restoreExpr.restoreSpine entries recMap
        (VExpr.appN function arguments)).map
          (fun result : VExpr => result.inst argument cutoff) =
      restoreExpr.restoreSpine entries recMap
        ((VExpr.appN function arguments).inst argument cutoff) := by
  induction function generalizing arguments cutoff with
  | app function spineArgument functionIH _ =>
      change (restoreExpr.restoreSpine entries recMap
          (VExpr.appN function (spineArgument :: arguments))).map _ =
        restoreExpr.restoreSpine entries recMap
          ((VExpr.appN function (spineArgument :: arguments)).inst
            argument cutoff)
      exact functionIH (spineArgument :: arguments) cutoff
  | bvar index =>
      have before : restoreExpr.restoreSpine entries recMap
          (VExpr.appN (.bvar index) arguments) = none := by
        unfold restoreExpr.restoreSpine
        rw [VExpr.appHead_appN]
        rfl
      rw [before, Option.map_none, VExpr.instN_appN]
      exact (restoreSpine_appN_eq_none_of_function_inert
        (VExpr.instVar index argument cutoff)
        (arguments.map (·.inst argument cutoff))
        (argumentInert.instVar index cutoff)).symm
  | sort level =>
      rw [VExpr.instN_appN]
      unfold restoreExpr.restoreSpine
      simp [VExpr.appHead_appN, VExpr.appArgs_appN,
        VExpr.appHead, VExpr.appArgs, VExpr.inst]
  | lam domain body _ _ =>
      rw [VExpr.instN_appN]
      unfold restoreExpr.restoreSpine
      simp [VExpr.appHead_appN, VExpr.appArgs_appN,
        VExpr.appHead, VExpr.appArgs, VExpr.inst]
  | forallE domain body _ _ =>
      rw [VExpr.instN_appN]
      unfold restoreExpr.restoreSpine
      simp [VExpr.appHead_appN, VExpr.appArgs_appN,
        VExpr.appHead, VExpr.appArgs, VExpr.inst]
  | const name nameLevels =>
      rw [VExpr.instN_appN]
      unfold restoreExpr.restoreSpine
      simp only [VExpr.appHead_appN, VExpr.appArgs_appN,
        List.append_nil, VExpr.inst, VExpr.appHead, VExpr.appArgs]
      cases recursor : recMap.find? (·.1 == name) with
      | some renamed =>
          by_cases empty : arguments.isEmpty
          · simp [recursor, empty, List.isEmpty_map, VExpr.inst]
          · simp [recursor, empty, List.isEmpty_map]
      | none =>
          cases entryFound : entries.find? (·.aux == name) with
          | some entry =>
              have entryClosed : entry.value.ClosedN entry.np :=
                closed entry (List.mem_of_find?_eq_some entryFound)
              by_cases arity : arguments.length == entry.np
              · have lengthEq : arguments.length = entry.np := by
                  simpa using arity
                have closedAt : entry.value.ClosedN arguments.length := by
                  rw [lengthEq]
                  exact entryClosed
                have instantiated := instRevParams_instN entry.value
                  arguments argument cutoff closedAt
                simpa only [recursor, entryFound, arity,
                  List.length_map, if_true, Option.map_some] using
                    congrArg some instantiated
              · simp [recursor, entryFound, arity]
          | none =>
              cases constructorFound : findRestoreCtor entries name with
              | none => simp [recursor, entryFound, constructorFound]
              | some result =>
                  obtain ⟨entry, suffix⟩ := result
                  have entryMember : entry ∈ entries :=
                    VInductDecl.mem_of_findRestoreCtor_eq_some
                      constructorFound
                  have entryClosed : entry.value.ClosedN entry.np :=
                    closed entry entryMember
                  obtain ⟨target, targetLevels, entryHead⟩ :=
                    heads entry entryMember
                  by_cases arity : arguments.length == entry.np
                  · have lengthEq : arguments.length = entry.np := by
                      simpa using arity
                    have closedAt : entry.value.ClosedN arguments.length := by
                      rw [lengthEq]
                      exact entryClosed
                    let value := instRevParams entry.value arguments
                    have valueHead : value.appHead =
                        .const target targetLevels := by
                      exact instRevParams_appHead_eq_const entryHead arguments
                    have valueInst :
                        instRevParams entry.value
                            (arguments.map (·.inst argument cutoff)) =
                          value.inst argument cutoff := by
                      simpa [value] using
                        (instRevParams_instN entry.value arguments argument
                          cutoff closedAt).symm
                    simp only [recursor, entryFound, constructorFound,
                      arity, List.length_map, if_true]
                    rw [valueInst]
                    exact restoreCtorResult_instN value suffix argument
                      cutoff valueHead
                  · simp [recursor, entryFound, constructorFound, arity]

/-- Application-spine form specialized to an arbitrary expression. -/
private theorem restoreSpine_instN
    (entries : List RestoreEntry)
    (closed : RestoreEntriesClosed entries)
    (heads : RestoreEntriesConstHead entries)
    (recMap : List (Name × Name))
    (expression argument : VExpr) (cutoff : Nat)
    (argumentInert : RestoreInert entries recMap argument) :
    (restoreExpr.restoreSpine entries recMap expression).map
        (fun result : VExpr => result.inst argument cutoff) =
      restoreExpr.restoreSpine entries recMap
        (expression.inst argument cutoff) := by
  simpa [VExpr.appN] using restoreSpine_appN_instN entries closed heads
    recMap expression [] argument cutoff argumentInert

private theorem restoreGetD_instN
    (restored : Option VExpr) (fallback argument : VExpr)
    (cutoff : Nat) :
    (restored.getD fallback).inst argument cutoff =
      (restored.map fun result : VExpr =>
        result.inst argument cutoff).getD
          (fallback.inst argument cutoff) := by
  cases restored <;> rfl

/-- Under closure, constant-headed replacement shape, and inertness of the
runtime argument, nested restoration commutes with arbitrary ambient term
instantiation. -/
theorem restoreExpr_instN
    (entries : List RestoreEntry)
    (closed : RestoreEntriesClosed entries)
    (heads : RestoreEntriesConstHead entries)
    (recMap : List (Name × Name)) (expression argument : VExpr)
    (cutoff : Nat)
    (argumentInert : RestoreInert entries recMap argument) :
    (restoreExpr entries recMap expression).inst argument cutoff =
      restoreExpr entries recMap (expression.inst argument cutoff) := by
  induction expression generalizing cutoff with
  | bvar index =>
      change VExpr.instVar index argument cutoff =
        restoreExpr entries recMap (VExpr.instVar index argument cutoff)
      exact (argumentInert.instVar index cutoff).restoreExpr_eq.symm
  | sort => rfl
  | const name nameLevels =>
      simp only [restoreExpr]
      rw [restoreGetD_instN]
      rw [restoreSpine_instN entries closed heads recMap _ argument cutoff
        argumentInert]
      rfl
  | app function spineArgument functionIH argumentIH =>
      simp only [restoreExpr]
      rw [restoreGetD_instN]
      rw [restoreSpine_instN entries closed heads recMap _ argument cutoff
        argumentInert]
      simp only [VExpr.inst, functionIH, argumentIH]
      rfl
  | lam domain body domainIH bodyIH =>
      simp only [restoreExpr, VExpr.inst, domainIH, bodyIH]
  | forallE domain body domainIH bodyIH =>
      simp only [restoreExpr, VExpr.inst, domainIH, bodyIH]

/-! The operational projection motives generated below substitute earlier
projector applications into later field types.  Those arguments are not
restoration-inert: their lambda bodies contain the generated recursor.
Their restored application heads are nevertheless lambdas, so substituting
them cannot complete a new auxiliary-constant spine.  The following variant
records precisely that weaker head condition while restoring the argument on
the left-hand side. -/

/-- Extending a non-constant-headed application spine cannot trigger any
restoration case at its outer node. -/
private theorem restoreSpine_appN_eq_none_of_function_nonConst
    {entries : List RestoreEntry} {recMap : List (Name × Name)}
    (function : VExpr) (arguments : List VExpr)
    (nonConst : ∀ name levels,
      function.appHead ≠ .const name levels) :
    restoreExpr.restoreSpine entries recMap
        (VExpr.appN function arguments) = none := by
  unfold restoreExpr.restoreSpine
  rw [VExpr.appHead_appN, VExpr.appArgs_appN]
  cases head : function.appHead with
  | const name levels => exact (nonConst name levels head).elim
  | bvar | sort | app | lam | forallE => rfl

/-- Ambient substitution preserves the fact that an application head is
non-constant. -/
private theorem VExpr.appHead_instVar_ne_const
    {argument : VExpr}
    (nonConst : ∀ name levels,
      argument.appHead ≠ .const name levels)
    (index cutoff : Nat) :
    ∀ name levels,
      (VExpr.instVar index argument cutoff).appHead ≠
        .const name levels := by
  intro name levels
  unfold VExpr.instVar
  split
  · simp [VExpr.appHead]
  · split
    · rw [VExpr.appHead_liftN]
      cases head : argument.appHead with
      | const source sourceLevels => exact (nonConst source sourceLevels head).elim
      | bvar | sort | app | lam | forallE => simp [VExpr.liftN]
    · simp [VExpr.appHead]

/-- One ambient substitution commutes with the restoration-spine decision
when the substituted expression has a non-constant head. -/
private theorem restoreSpine_appN_instN_nonConst
    (entries : List RestoreEntry)
    (closed : RestoreEntriesClosed entries)
    (heads : RestoreEntriesConstHead entries)
    (recMap : List (Name × Name))
    (function : VExpr) (arguments : List VExpr)
    (argument : VExpr) (cutoff : Nat)
    (argumentNonConst : ∀ name levels,
      argument.appHead ≠ .const name levels) :
    (restoreExpr.restoreSpine entries recMap
        (VExpr.appN function arguments)).map
          (fun result : VExpr => result.inst argument cutoff) =
      restoreExpr.restoreSpine entries recMap
        ((VExpr.appN function arguments).inst argument cutoff) := by
  induction function generalizing arguments cutoff with
  | app function spineArgument functionIH _ =>
      change (restoreExpr.restoreSpine entries recMap
          (VExpr.appN function (spineArgument :: arguments))).map _ =
        restoreExpr.restoreSpine entries recMap
          ((VExpr.appN function (spineArgument :: arguments)).inst
            argument cutoff)
      exact functionIH (spineArgument :: arguments) cutoff
  | bvar index =>
      have before : restoreExpr.restoreSpine entries recMap
          (VExpr.appN (.bvar index) arguments) = none := by
        unfold restoreExpr.restoreSpine
        rw [VExpr.appHead_appN]
        rfl
      rw [before, Option.map_none, VExpr.instN_appN]
      exact (restoreSpine_appN_eq_none_of_function_nonConst
        (VExpr.instVar index argument cutoff)
        (arguments.map (·.inst argument cutoff))
        (VExpr.appHead_instVar_ne_const argumentNonConst index cutoff)).symm
  | sort level =>
      rw [VExpr.instN_appN]
      unfold restoreExpr.restoreSpine
      simp [VExpr.appHead_appN, VExpr.appArgs_appN,
        VExpr.appHead, VExpr.appArgs, VExpr.inst]
  | lam domain body _ _ =>
      rw [VExpr.instN_appN]
      unfold restoreExpr.restoreSpine
      simp [VExpr.appHead_appN, VExpr.appArgs_appN,
        VExpr.appHead, VExpr.appArgs, VExpr.inst]
  | forallE domain body _ _ =>
      rw [VExpr.instN_appN]
      unfold restoreExpr.restoreSpine
      simp [VExpr.appHead_appN, VExpr.appArgs_appN,
        VExpr.appHead, VExpr.appArgs, VExpr.inst]
  | const name nameLevels =>
      rw [VExpr.instN_appN]
      unfold restoreExpr.restoreSpine
      simp only [VExpr.appHead_appN, VExpr.appArgs_appN,
        List.append_nil, VExpr.inst, VExpr.appHead, VExpr.appArgs]
      cases recursor : recMap.find? (·.1 == name) with
      | some renamed =>
          by_cases empty : arguments.isEmpty
          · simp [recursor, empty, List.isEmpty_map, VExpr.inst]
          · simp [recursor, empty, List.isEmpty_map]
      | none =>
          cases entryFound : entries.find? (·.aux == name) with
          | some entry =>
              have entryClosed : entry.value.ClosedN entry.np :=
                closed entry (List.mem_of_find?_eq_some entryFound)
              by_cases arity : arguments.length == entry.np
              · have lengthEq : arguments.length = entry.np := by
                  simpa using arity
                have closedAt : entry.value.ClosedN arguments.length := by
                  rw [lengthEq]
                  exact entryClosed
                have instantiated := instRevParams_instN entry.value
                  arguments argument cutoff closedAt
                simpa only [recursor, entryFound, arity,
                  List.length_map, if_true, Option.map_some] using
                    congrArg some instantiated
              · simp [recursor, entryFound, arity]
          | none =>
              cases constructorFound : findRestoreCtor entries name with
              | none => simp [recursor, entryFound, constructorFound]
              | some result =>
                  obtain ⟨entry, suffix⟩ := result
                  have entryMember : entry ∈ entries :=
                    VInductDecl.mem_of_findRestoreCtor_eq_some
                      constructorFound
                  have entryClosed : entry.value.ClosedN entry.np :=
                    closed entry entryMember
                  obtain ⟨target, targetLevels, entryHead⟩ :=
                    heads entry entryMember
                  by_cases arity : arguments.length == entry.np
                  · have lengthEq : arguments.length = entry.np := by
                      simpa using arity
                    have closedAt : entry.value.ClosedN arguments.length := by
                      rw [lengthEq]
                      exact entryClosed
                    let value := instRevParams entry.value arguments
                    have valueHead : value.appHead =
                        .const target targetLevels := by
                      exact instRevParams_appHead_eq_const entryHead arguments
                    have valueInst :
                        instRevParams entry.value
                            (arguments.map (·.inst argument cutoff)) =
                          value.inst argument cutoff := by
                      simpa [value] using
                        (instRevParams_instN entry.value arguments argument
                          cutoff closedAt).symm
                    simp only [recursor, entryFound, constructorFound,
                      arity, List.length_map, if_true]
                    rw [valueInst]
                    exact restoreCtorResult_instN value suffix argument
                      cutoff valueHead
                  · simp [recursor, entryFound, constructorFound, arity]

/-- Application-spine form of the non-constant-head interchange law. -/
private theorem restoreSpine_instN_nonConst
    (entries : List RestoreEntry)
    (closed : RestoreEntriesClosed entries)
    (heads : RestoreEntriesConstHead entries)
    (recMap : List (Name × Name))
    (expression argument : VExpr) (cutoff : Nat)
    (argumentNonConst : ∀ name levels,
      argument.appHead ≠ .const name levels) :
    (restoreExpr.restoreSpine entries recMap expression).map
        (fun result : VExpr => result.inst argument cutoff) =
      restoreExpr.restoreSpine entries recMap
        (expression.inst argument cutoff) := by
  simpa [VExpr.appN] using restoreSpine_appN_instN_nonConst entries closed
    heads recMap expression [] argument cutoff argumentNonConst

/-- Restoration commutes with substitution while mapping the substituted
expression itself, provided its restored application head is non-constant.
This is the exact case generated by an application of a lambda-headed
operational projector. -/
theorem restoreExpr_instN_map
    (entries : List RestoreEntry)
    (closed : RestoreEntriesClosed entries)
    (heads : RestoreEntriesConstHead entries)
    (recMap : List (Name × Name)) (expression argument : VExpr)
    (cutoff : Nat)
    (argumentNonConst : ∀ name levels,
      (restoreExpr entries recMap argument).appHead ≠
        .const name levels) :
    (restoreExpr entries recMap expression).inst
        (restoreExpr entries recMap argument) cutoff =
      restoreExpr entries recMap (expression.inst argument cutoff) := by
  induction expression generalizing cutoff with
  | bvar index =>
      change VExpr.instVar index (restoreExpr entries recMap argument) cutoff =
        restoreExpr entries recMap (VExpr.instVar index argument cutoff)
      unfold VExpr.instVar
      split
      · rfl
      · split
        · exact restoreExpr_liftN entries closed recMap argument cutoff 0
        · rfl
  | sort => rfl
  | const name nameLevels =>
      simp only [restoreExpr]
      rw [restoreGetD_instN]
      rw [restoreSpine_instN_nonConst entries closed heads recMap _
        (restoreExpr entries recMap argument) cutoff argumentNonConst]
      rfl
  | app function spineArgument functionIH argumentIH =>
      simp only [restoreExpr]
      rw [restoreGetD_instN]
      rw [restoreSpine_instN_nonConst entries closed heads recMap _
        (restoreExpr entries recMap argument) cutoff argumentNonConst]
      simp only [VExpr.inst, functionIH, argumentIH]
      rfl
  | lam domain body domainIH bodyIH =>
      simp only [restoreExpr, VExpr.inst, domainIH, bodyIH]
  | forallE domain body domainIH bodyIH =>
      simp only [restoreExpr, VExpr.inst, domainIH, bodyIH]

/-- Iterated mapped-argument substitution for a list of non-constant-headed
restored expressions. -/
theorem restoreExpr_instRevAt_map
    (entries : List RestoreEntry)
    (closed : RestoreEntriesClosed entries)
    (heads : RestoreEntriesConstHead entries)
    (recMap : List (Name × Name)) (expression : VExpr)
    (arguments : List VExpr) (offset : Nat)
    (argumentsNonConst : ∀ argument ∈ arguments, ∀ name levels,
      (restoreExpr entries recMap argument).appHead ≠
        .const name levels) :
    (restoreExpr entries recMap expression).instRevAt
        (arguments.map (restoreExpr entries recMap)) offset =
      restoreExpr entries recMap
        (expression.instRevAt arguments offset) := by
  induction arguments generalizing expression with
  | nil => rfl
  | cons argument arguments ih =>
      simp only [List.map_cons, VExpr.instRevAt, List.length_map]
      rw [restoreExpr_instN_map entries closed heads recMap expression
        argument (offset + arguments.length)
        (argumentsNonConst argument (by simp))]
      exact ih (expression := expression.inst argument
        (offset + arguments.length)) fun candidate member =>
          argumentsNonConst candidate (List.mem_cons_of_mem argument member)

/-- Iterating the one-argument law yields commutation with an
outermost-first runtime parameter spine. -/
theorem restoreExpr_instRevAt
    (entries : List RestoreEntry)
    (closed : RestoreEntriesClosed entries)
    (heads : RestoreEntriesConstHead entries)
    (recMap : List (Name × Name)) (expression : VExpr)
    (arguments : List VExpr) (offset : Nat)
    (argumentsInert : ∀ argument ∈ arguments,
      RestoreInert entries recMap argument) :
    (restoreExpr entries recMap expression).instRevAt arguments offset =
      restoreExpr entries recMap
        (expression.instRevAt arguments offset) := by
  induction arguments generalizing expression with
  | nil => rfl
  | cons argument arguments ih =>
      simp only [VExpr.instRevAt]
      rw [restoreExpr_instN entries closed heads recMap expression argument
        (offset + arguments.length) (argumentsInert argument (by simp))]
      exact ih (expression := expression.inst argument
        (offset + arguments.length)) fun candidate member =>
          argumentsInert candidate (List.mem_cons_of_mem argument member)

/-- Runtime recursor restoration commutes with one inert ambient argument;
the nested producer discharges the constant-head invariant definitionally. -/
theorem NestedBlockChecked.restoreRecAt_instN
    {source : VInductDecl} (nested : source.NestedBlockChecked)
    (closed : RestoreEntriesClosed nested.recEntries)
    (levels : List VLevel) (expression argument : VExpr) (cutoff : Nat)
    (argumentInert : RestoreInert
      (nested.recEntries.map (·.instL levels)) nested.recMap argument) :
    (nested.restoreRecAt levels expression).inst argument cutoff =
      nested.restoreRecAt levels (expression.inst argument cutoff) := by
  unfold NestedBlockChecked.restoreRecAt
  exact restoreExpr_instN _ (closed.instL levels)
    (nested.recEntriesConstHead.instL levels) nested.recMap expression
      argument cutoff argumentInert

/-- Runtime recursor restoration commutes with a complete inert parameter
spine at any binder offset. -/
theorem NestedBlockChecked.restoreRecAt_instRevAt
    {source : VInductDecl} (nested : source.NestedBlockChecked)
    (closed : RestoreEntriesClosed nested.recEntries)
    (levels : List VLevel) (expression : VExpr)
    (arguments : List VExpr) (offset : Nat)
    (argumentsInert : ∀ argument ∈ arguments,
      RestoreInert (nested.recEntries.map (·.instL levels))
        nested.recMap argument) :
    (nested.restoreRecAt levels expression).instRevAt arguments offset =
      nested.restoreRecAt levels
        (expression.instRevAt arguments offset) := by
  unfold NestedBlockChecked.restoreRecAt
  exact restoreExpr_instRevAt _ (closed.instL levels)
    (nested.recEntriesConstHead.instL levels) nested.recMap expression
      arguments offset argumentsInert

/-- Runtime wrapper for mapped non-constant-head substitution.  This is the
form consumed by restored operational projector motives. -/
theorem NestedBlockChecked.restoreRecAt_instRevAt_map
    {source : VInductDecl} (nested : source.NestedBlockChecked)
    (closed : RestoreEntriesClosed nested.recEntries)
    (levels : List VLevel) (expression : VExpr)
    (arguments : List VExpr) (offset : Nat)
    (argumentsNonConst : ∀ argument ∈ arguments, ∀ name nameLevels,
      (nested.restoreRecAt levels argument).appHead ≠
        .const name nameLevels) :
    (nested.restoreRecAt levels expression).instRevAt
        (arguments.map (nested.restoreRecAt levels)) offset =
      nested.restoreRecAt levels
        (expression.instRevAt arguments offset) := by
  unfold NestedBlockChecked.restoreRecAt
  exact restoreExpr_instRevAt_map _ (closed.instL levels)
    (nested.recEntriesConstHead.instL levels) nested.recMap expression
      arguments offset argumentsNonConst

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

/-- One exact auxiliary application produced by nested elimination restores
to the target occurrence whose parameter expressions were lowered when the
auxiliary specification was recorded. -/
theorem restoreExpr_aux_bvarRevRange_of_lowerN
    {entries : List RestoreEntry} {recMap : List (Name × Name)}
    {entry : RestoreEntry} {target : Name}
    {levels auxLevels : List VLevel} {values : List VExpr}
    {locals params : Nat}
    (hrec : recMap.find? (·.1 == entry.aux) = none)
    (hentry : entries.find? (·.aux == entry.aux) = some entry)
    (hnp : entry.np = params)
    (hvalue : entry.value =
      (VExpr.const target levels).appN
        (values.map (fun expression => expression.lowerN locals)))
    (closed : ∀ expression ∈ values,
      expression.ClosedN (locals + params))
    (free : ∀ expression ∈ values,
      expression.hasLooseBelow locals = false) :
    restoreExpr entries recMap
        ((VExpr.const entry.aux auxLevels).appN
          (VExpr.bvarRevRange locals params)) =
      (VExpr.const target levels).appN values := by
  rw [restoreExpr_aux_appN hrec hentry (by simp [hnp])]
  have restoredParameters :
      (VExpr.bvarRevRange locals params).map
          (restoreExpr entries recMap) =
        VExpr.bvarRevRange locals params := by
    have all : ∀ count,
        (VExpr.bvarRevRange locals count).map
            (restoreExpr entries recMap) =
          VExpr.bvarRevRange locals count := by
      intro count
      induction count with
      | zero => rfl
      | succ count ih =>
          simp only [VExpr.bvarRevRange, List.map_cons, restoreExpr, ih]
    exact all params
  rw [restoredParameters, hvalue]
  exact instRevParams_lowerN_const_appN_bvarRevRange closed free

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

/-- Restoration extends structurally through an application spine whenever
the restored head is not constant-headed.  Such a spine cannot trigger a
restoration entry, constructor replacement, or recursor rename at any later
argument position. -/
theorem restoreExpr_appN_of_nonConst_head
    {entries : List RestoreEntry} {recMap : List (Name × Name)}
    {base restored : VExpr} {arguments : List VExpr}
    (baseEq : restoreExpr entries recMap base = restored)
    (headNonConst : ∀ name levels,
      restored.appHead ≠ .const name levels) :
    restoreExpr entries recMap (base.appN arguments) =
      restored.appN (arguments.map (restoreExpr entries recMap)) := by
  induction arguments generalizing base restored with
  | nil => exact baseEq
  | cons argument arguments ih =>
      simp only [VExpr.appN, List.map_cons]
      apply ih
      · simp only [restoreExpr, baseEq]
        unfold restoreExpr.restoreSpine
        have headEq :
            (restored.app (restoreExpr entries recMap argument)).appHead =
              restored.appHead := by simp [VExpr.appHead]
        rw [headEq]
        cases headFound : restored.appHead with
        | const name levels =>
            exact (headNonConst name levels headFound).elim
        | bvar | sort | app | lam | forallE => rfl
      · intro name levels
        simpa [VExpr.appHead] using headNonConst name levels

/-- Restoration extends the exact recorded replacement through the trailing
arguments retained by `ElimNested.replace`.  The target-head hypotheses are
the explicit disjointness obligations later discharged from the producer's
fresh generated-name inventory. -/
theorem restoreExpr_recordedReplacement
    {entries : List RestoreEntry} {recMap : List (Name × Name)}
    {entry : RestoreEntry} {target : Name}
    {levels auxLevels : List VLevel} {values trailing : List VExpr}
    {locals params : Nat}
    (hrec : recMap.find? (·.1 == entry.aux) = none)
    (hentry : entries.find? (·.aux == entry.aux) = some entry)
    (hnp : entry.np = params)
    (hvalue : entry.value =
      (VExpr.const target levels).appN
        (values.map (fun expression => expression.lowerN locals)))
    (closed : ∀ expression ∈ values,
      expression.ClosedN (locals + params))
    (free : ∀ expression ∈ values,
      expression.hasLooseBelow locals = false)
    (htargetRec : recMap.find? (·.1 == target) = none)
    (htargetEntry : entries.find? (·.aux == target) = none)
    (htargetCtor : findRestoreCtor entries target = none) :
    restoreExpr entries recMap
        ((VExpr.const entry.aux auxLevels).appN
          (VExpr.bvarRevRange locals params ++ trailing)) =
      ((VExpr.const target levels).appN values).appN
        (trailing.map (restoreExpr entries recMap)) := by
  rw [VExpr.appN_append]
  apply restoreExpr_appN_of_head_inert (name := target) (ls := levels)
  · exact restoreExpr_aux_bvarRevRange_of_lowerN hrec hentry hnp
      hvalue closed free
  · simp [VExpr.appHead, VExpr.appHead_appN]
  · exact htargetRec
  · exact htargetEntry
  · exact htargetCtor

/-- The declaration-world restoration entry canonically associated with one
producer-owned atomic replacement. -/
def ElimNested.ReplacementResult.restoreEntry
    {uvars params : Nat} {e e' : VExpr} {k : Nat}
    {state : ElimNested.State}
    (result : ElimNested.ReplacementResult uvars params e e' k state) :
    RestoreEntry :=
  ⟨result.spec.aux, params, result.spec.value⟩

/-- Terminal producer provenance determines the exact declaration-world
entry lookup consumed by restoration. -/
theorem ElimNested.ReplacementResult.declEntries_find?
    {source : VInductDecl} {nested : NestedBlockChecked source}
    {e e' : VExpr} {k : Nat}
    (result : ElimNested.ReplacementResult source.uvars source.nparams
      e e' k nested.elim.state) :
    nested.declEntries.find? (·.aux == result.spec.aux) =
      some result.restoreEntry := by
  apply nested.declEntries_find?_of_mem
  rw [nested.elim.specs_eq]
  exact result.spec_mem

/-- One producer-owned atomic nested replacement is exactly inverted by
restoration.  The remaining hypotheses are global terminal-state facts:
entry lookup, generated-name disjointness, closure of the source parameter
expressions, and inertness of the untouched trailing arguments. -/
theorem ElimNested.ReplacementResult.restoreExpr_eq
    {uvars params : Nat} {e e' : VExpr} {k : Nat}
    {state : ElimNested.State}
    (result : ElimNested.ReplacementResult uvars params e e' k state)
    {entries : List RestoreEntry} {recMap : List (Name × Name)}
    (hauxRec : recMap.find? (·.1 == result.spec.aux) = none)
    (hentry : entries.find? (·.aux == result.spec.aux) =
      some result.restoreEntry)
    (closed : ∀ expression ∈ result.parameters,
      expression.ClosedN (k + params))
    (htargetRec : recMap.find? (·.1 == result.target) = none)
    (htargetEntry : entries.find? (·.aux == result.target) = none)
    (htargetCtor : findRestoreCtor entries result.target = none)
    (htrailing : result.trailing.map (restoreExpr entries recMap) =
      result.trailing) :
    restoreExpr entries recMap e' = e := by
  rw [result.result_eq]
  have restored := restoreExpr_recordedReplacement
    (entry := result.restoreEntry) (target := result.target)
    (levels := result.levels) (auxLevels := VLevel.params uvars)
    (values := result.parameters) (trailing := result.trailing)
    (locals := k) (params := params)
    hauxRec hentry rfl (by
      simpa only [ElimNested.ReplacementResult.restoreEntry] using
        result.spec_value_eq)
    closed result.parameters_free htargetRec htargetEntry htargetCtor
  have restored' :
      restoreExpr entries recMap
          ((VExpr.const result.spec.aux (VLevel.params uvars)).appN
            (VExpr.bvarRevRange k params ++ result.trailing)) =
        ((VExpr.const result.target result.levels).appN
          result.parameters).appN
            (result.trailing.map (restoreExpr entries recMap)) := by
    simpa only [ElimNested.ReplacementResult.restoreEntry] using restored
  rw [restored', htrailing, ← VExpr.appN_append,
    ← result.arguments_eq, ← result.head_eq]
  exact VExpr.appN_appHead_appArgs e []

/-- Source closure and inertness discharge all local obligations of the
atomic replacement inversion.  In particular, closure is inherited by the
recorded parameter prefix and restoration is the identity on every recorded
trailing argument. -/
theorem ElimNested.ReplacementResult.restoreExpr_eq_of_source
    {uvars params : Nat} {e e' : VExpr} {k : Nat}
    {state : ElimNested.State}
    (result : ElimNested.ReplacementResult uvars params e e' k state)
    {entries : List RestoreEntry} {recMap : List (Name × Name)}
    (hauxRec : recMap.find? (·.1 == result.spec.aux) = none)
    (hentry : entries.find? (·.aux == result.spec.aux) =
      some result.restoreEntry)
    (closed : e.ClosedN (k + params))
    (inert : RestoreInert entries recMap e) :
    restoreExpr entries recMap e' = e := by
  have parametersClosed : ∀ expression ∈ result.parameters,
      expression.ClosedN (k + params) := by
    intro expression member
    apply closed.appArgs
    rw [result.arguments_eq]
    exact List.mem_append_left _ member
  obtain ⟨htargetRec, htargetEntry, htargetCtor⟩ :=
    inert result.target
      (VExpr.hasConst_of_appHead_eq_const result.head_eq)
  have trailingRestored :
      result.trailing.map (restoreExpr entries recMap) =
        result.trailing := by
    have mapped :
        result.trailing.map (restoreExpr entries recMap) =
          result.trailing.map id := by
      apply List.map_congr_left
      intro expression member
      exact (inert.appArgs (by
        rw [result.arguments_eq]
        exact List.mem_append_right _ member)).restoreExpr_eq
    simpa only [List.map_id] using mapped
  exact result.restoreExpr_eq hauxRec hentry parametersClosed
    htargetRec htargetEntry htargetCtor trailingRestored

private theorem elimNestedSpecsPrefix_trans
    {first middle final : ElimNested.State}
    (left : first.specs.toList <+: middle.specs.toList)
    (right : middle.specs.toList <+: final.specs.toList) :
    first.specs.toList <+: final.specs.toList := by
  obtain ⟨leftSuffix, leftEq⟩ := left
  obtain ⟨rightSuffix, rightEq⟩ := right
  refine ⟨leftSuffix ++ rightSuffix, ?_⟩
  rw [← List.append_assoc, leftEq, rightEq]

/-- Every auxiliary specification accumulated in a flattening state denotes
an expression closed over exactly the current inductive block parameters. -/
def ElimNested.State.SpecValuesClosed
    (state : ElimNested.State) (params : Nat) : Prop :=
  ∀ spec ∈ state.specs.toList, spec.value.ClosedN params

/-- An environment-backed target-block copy has closed raw metadata. -/
theorem NestedTargetBlock.WF.metadataClosed
    {env : VEnv} (henv : env.Ordered)
    {block : NestedTargetBlock} (wf : block.WF env) :
    block.MetadataClosed := by
  intro family familyMember
  refine ⟨?_, ?_⟩
  · simpa using henv.closedC (wf.families family familyMember)
  · intro constructor constructorMember
    simpa using henv.closedC
      (wf.ctors family familyMember constructor constructorMember)

/-- Environment-backed well-formedness closes every target block consulted
by nested elimination. -/
theorem NestedTargetsWF.metadataClosed
    {env : VEnv} (henv : env.Ordered)
    {targets : List NestedTargetBlock}
    (wf : NestedTargetsWF env targets) : NestedTargetsClosed targets := by
  intro block member
  exact (wf block member).metadataClosed henv

/-- The literal auxiliary application emitted by one recorded replacement is
closed at the same local-plus-parameter boundary as its source application. -/
theorem ElimNested.ReplacementResult.result_closedN
    {uvars params : Nat} {e e' : VExpr} {k : Nat}
    {state : ElimNested.State}
    (result : ElimNested.ReplacementResult uvars params e e' k state)
    (closed : e.ClosedN (k + params)) :
    e'.ClosedN (k + params) := by
  rw [result.result_eq]
  apply VExpr.ClosedN.appN (by trivial)
  intro argument member
  rw [List.mem_append] at member
  rcases member with localArgument | trailing
  · exact VInductDecl.bvarRevRange_closedN params k (k + params)
      (by omega) argument localArgument
  · apply closed.appArgs
    rw [result.arguments_eq]
    exact List.mem_append_right _ trailing

/-- Atomic nested rewriting preserves the source expression's exact
local-plus-parameter closedness boundary. -/
theorem ElimNested.replace_rewrite_closedN
    {targets : List NestedTargetBlock} {uvars params : Nat}
    {doms : List VExpr} {e e' : VExpr} {k : Nat}
    {state finalState : ElimNested.State}
    (run : ElimNested.replace.rewrite? targets uvars params doms e k state =
      some (some (e', finalState)))
    (closed : e.ClosedN (k + params)) :
    e'.ClosedN (k + params) := by
  obtain ⟨result⟩ :=
    ElimNested.replace_rewrite_result targets uvars params run
  exact result.result_closedN closed

/-- Recursive nested replacement preserves expression closedness. -/
theorem ElimNested.replace_closedN
    {targets : List NestedTargetBlock} {uvars params : Nat}
    {doms : List VExpr} {e e' : VExpr} {k : Nat}
    {state finalState : ElimNested.State}
    (run : ElimNested.replace targets uvars params doms e k state =
      some (e', finalState))
    (closed : e.ClosedN (k + params)) :
    e'.ClosedN (k + params) := by
  induction e generalizing k state e' finalState with
  | app function argument functionIH argumentIH =>
      simp only [ElimNested.replace] at run
      cases rewriteRun : ElimNested.replace.rewrite? targets uvars params doms
          (.app function argument) k state with
      | none =>
          rw [rewriteRun] at run
          obtain ⟨functionResult, functionRun, run⟩ :=
            Option.bind_eq_some_iff.mp run
          obtain ⟨function', functionState⟩ := functionResult
          obtain ⟨argumentResult, argumentRun, run⟩ :=
            Option.bind_eq_some_iff.mp run
          obtain ⟨argument', argumentState⟩ := argumentResult
          cases run
          exact ⟨functionIH functionRun closed.1,
            argumentIH argumentRun closed.2⟩
      | some rewriteResult =>
          rw [rewriteRun] at run
          cases rewriteResult with
          | none => contradiction
          | some result =>
              obtain ⟨resultExpr, resultState⟩ := result
              cases run
              exact ElimNested.replace_rewrite_closedN rewriteRun closed
  | const name levels =>
      simp only [ElimNested.replace] at run
      cases rewriteRun : ElimNested.replace.rewrite? targets uvars params doms
          (.const name levels) k state with
      | none =>
          rw [rewriteRun] at run
          cases run
          exact closed
      | some rewriteResult =>
          rw [rewriteRun] at run
          cases rewriteResult with
          | none => contradiction
          | some result =>
              obtain ⟨resultExpr, resultState⟩ := result
              cases run
              exact ElimNested.replace_rewrite_closedN rewriteRun closed
  | lam domain body domainIH bodyIH =>
      simp only [ElimNested.replace] at run
      obtain ⟨domainResult, domainRun, run⟩ :=
        Option.bind_eq_some_iff.mp run
      obtain ⟨domain', domainState⟩ := domainResult
      obtain ⟨bodyResult, bodyRun, run⟩ :=
        Option.bind_eq_some_iff.mp run
      obtain ⟨body', bodyState⟩ := bodyResult
      cases run
      refine ⟨domainIH domainRun closed.1, ?_⟩
      have bodyResultClosed := bodyIH bodyRun (by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using closed.2)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        bodyResultClosed
  | forallE domain body domainIH bodyIH =>
      simp only [ElimNested.replace] at run
      obtain ⟨domainResult, domainRun, run⟩ :=
        Option.bind_eq_some_iff.mp run
      obtain ⟨domain', domainState⟩ := domainResult
      obtain ⟨bodyResult, bodyRun, run⟩ :=
        Option.bind_eq_some_iff.mp run
      obtain ⟨body', bodyState⟩ := bodyResult
      cases run
      refine ⟨domainIH domainRun closed.1, ?_⟩
      have bodyResultClosed := bodyIH bodyRun (by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using closed.2)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        bodyResultClosed
  | _ =>
      simp only [ElimNested.replace] at run
      cases run
      exact closed

/-- One atomic rewrite preserves closure of the complete growing family
queue when the exact consulted target inventory is closed. -/
theorem ElimNested.replace_rewrite_typesClosed
    {targets : List NestedTargetBlock} {uvars params : Nat}
    {doms : List VExpr} {e e' : VExpr} {k : Nat}
    {state finalState : ElimNested.State}
    (run : ElimNested.replace.rewrite? targets uvars params doms e k state =
      some (some (e', finalState)))
    (targetsClosed : NestedTargetsClosed targets)
    (stateClosed : state.TypesClosed)
    (domsClosed : (VExpr.forallN doms (.sort .zero)).ClosedN)
    (domsLength : doms.length = params)
    (closed : e.ClosedN (k + params)) :
    finalState.TypesClosed := by
  unfold ElimNested.replace.rewrite? at run
  cases head_eq : e.appHead with
  | const target levels =>
      simp only [head_eq] at run
      obtain ⟨block, blockEq, run⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨_, _parametersBound, run⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨_, _parametersPositive, run⟩ :=
        Option.bind_eq_some_iff.mp run
      obtain ⟨_, _nestedOccurrence, run⟩ :=
        Option.bind_eq_some_iff.mp run
      split at run
      · simp at run
      · rename_i parametersFree
        have parametersFree' : ∀ expression ∈
            (e.appArgs []).take block.nparams,
            expression.hasLooseBelow k = false := by
          simpa [List.any_eq_false] using parametersFree
        split at run
        · cases run
          exact stateClosed
        · split at run
          · rename_i auxName registeredState registerRun
            cases run
            have blockMember : block ∈ targets := by
              unfold ElimNested.findTarget? at blockEq
              split at blockEq
              · simp at blockEq
              · exact List.mem_of_find?_eq_some blockEq
            have valuesClosed : ∀ value ∈
                ((e.appArgs []).take block.nparams).map
                  (fun expression => expression.lowerN k),
                value.ClosedN doms.length := by
              intro value member
              obtain ⟨expression, expressionMember, rfl⟩ :=
                List.mem_map.mp member
              have expressionClosed :
                  expression.ClosedN (k + params) :=
                closed.appArgs (List.mem_of_mem_take expressionMember)
              have expressionClosed' :
                  expression.ClosedN (0 + k + params) := by
                simpa using expressionClosed
              have lowered := VExpr.lowerN_closedN
                (count := k) (depth := 0) (remaining := params)
                expressionClosed'
                (parametersFree' expression expressionMember)
              rw [domsLength]
              simpa using lowered
            exact ElimNested.registerAux_typesClosed uvars stateClosed
              (targetsClosed block blockMember) domsClosed valuesClosed
              registerRun
          · simp at run
  | _ => simp [head_eq] at run

/-- Recursive nested replacement preserves closure of the complete growing
family queue. -/
theorem ElimNested.replace_typesClosed
    {targets : List NestedTargetBlock} {uvars params : Nat}
    {doms : List VExpr} {e e' : VExpr} {k : Nat}
    {state finalState : ElimNested.State}
    (run : ElimNested.replace targets uvars params doms e k state =
      some (e', finalState))
    (targetsClosed : NestedTargetsClosed targets)
    (stateClosed : state.TypesClosed)
    (domsClosed : (VExpr.forallN doms (.sort .zero)).ClosedN)
    (domsLength : doms.length = params)
    (closed : e.ClosedN (k + params)) :
    finalState.TypesClosed := by
  induction e generalizing k state e' finalState with
  | app function argument functionIH argumentIH =>
      simp only [ElimNested.replace] at run
      cases rewriteRun : ElimNested.replace.rewrite? targets uvars params doms
          (.app function argument) k state with
      | none =>
          rw [rewriteRun] at run
          obtain ⟨functionResult, functionRun, run⟩ :=
            Option.bind_eq_some_iff.mp run
          obtain ⟨function', functionState⟩ := functionResult
          obtain ⟨argumentResult, argumentRun, run⟩ :=
            Option.bind_eq_some_iff.mp run
          obtain ⟨argument', argumentState⟩ := argumentResult
          cases run
          exact argumentIH argumentRun
            (functionIH functionRun stateClosed closed.1) closed.2
      | some rewriteResult =>
          rw [rewriteRun] at run
          cases rewriteResult with
          | none => contradiction
          | some result =>
              obtain ⟨resultExpr, resultState⟩ := result
              cases run
              exact ElimNested.replace_rewrite_typesClosed rewriteRun
                targetsClosed stateClosed domsClosed domsLength closed
  | const name levels =>
      simp only [ElimNested.replace] at run
      cases rewriteRun : ElimNested.replace.rewrite? targets uvars params doms
          (.const name levels) k state with
      | none =>
          rw [rewriteRun] at run
          cases run
          exact stateClosed
      | some rewriteResult =>
          rw [rewriteRun] at run
          cases rewriteResult with
          | none => contradiction
          | some result =>
              obtain ⟨resultExpr, resultState⟩ := result
              cases run
              exact ElimNested.replace_rewrite_typesClosed rewriteRun
                targetsClosed stateClosed domsClosed domsLength closed
  | lam domain body domainIH bodyIH =>
      simp only [ElimNested.replace] at run
      obtain ⟨domainResult, domainRun, run⟩ :=
        Option.bind_eq_some_iff.mp run
      obtain ⟨domain', domainState⟩ := domainResult
      obtain ⟨bodyResult, bodyRun, run⟩ :=
        Option.bind_eq_some_iff.mp run
      obtain ⟨body', bodyState⟩ := bodyResult
      cases run
      have bodyClosed : body.ClosedN ((k + 1) + params) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using closed.2
      exact bodyIH bodyRun
        (domainIH domainRun stateClosed closed.1) bodyClosed
  | forallE domain body domainIH bodyIH =>
      simp only [ElimNested.replace] at run
      obtain ⟨domainResult, domainRun, run⟩ :=
        Option.bind_eq_some_iff.mp run
      obtain ⟨domain', domainState⟩ := domainResult
      obtain ⟨bodyResult, bodyRun, run⟩ :=
        Option.bind_eq_some_iff.mp run
      obtain ⟨body', bodyState⟩ := bodyResult
      cases run
      have bodyClosed : body.ClosedN ((k + 1) + params) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using closed.2
      exact bodyIH bodyRun
        (domainIH domainRun stateClosed closed.1) bodyClosed
  | _ =>
      simp only [ElimNested.replace] at run
      cases run
      exact stateClosed

/-- One successful atomic nested rewrite preserves specification-value
closure.  A reused specification is covered by the input invariant; a fresh
registration appends an entire target block, whose specifications all share
the exact guarded-and-lowered parameter vector exposed by
`registerAux_spec_mem`. -/
theorem ElimNested.replace_rewrite_specValuesClosed
    {targets : List NestedTargetBlock} {uvars params : Nat}
    {doms : List VExpr} {e e' : VExpr} {k : Nat}
    {state finalState : ElimNested.State}
    (run : ElimNested.replace.rewrite? targets uvars params doms e k state =
      some (some (e', finalState)))
    (stateClosed : state.SpecValuesClosed params)
    (closed : e.ClosedN (k + params)) :
    finalState.SpecValuesClosed params := by
  unfold ElimNested.replace.rewrite? at run
  cases head_eq : e.appHead with
  | const target levels =>
      simp only [head_eq] at run
      obtain ⟨block, _block_eq, run⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨_, _parametersBound, run⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨_, _parametersPositive, run⟩ :=
        Option.bind_eq_some_iff.mp run
      obtain ⟨_, _nestedOccurrence, run⟩ :=
        Option.bind_eq_some_iff.mp run
      split at run
      · simp at run
      · rename_i parametersFree
        have parametersFree' : ∀ expression ∈
            (e.appArgs []).take block.nparams,
            expression.hasLooseBelow k = false := by
          simpa [List.any_eq_false] using parametersFree
        split at run
        · cases run
          exact stateClosed
        · split at run
          · rename_i auxName registeredState registerRun
            cases run
            intro spec member
            rcases ElimNested.registerAux_spec_mem uvars registerRun member with
              old | shape
            · exact stateClosed spec old
            · unfold NestedAuxSpec.value
              rw [shape.1, shape.2]
              apply VExpr.ClosedN.appN (by trivial)
              intro lowered loweredMember
              obtain ⟨expression, expressionMember, rfl⟩ :=
                List.mem_map.mp loweredMember
              have expressionClosed :
                  expression.ClosedN (k + params) :=
                closed.appArgs (List.mem_of_mem_take expressionMember)
              have expressionClosed' :
                  expression.ClosedN (0 + k + params) := by
                simpa using expressionClosed
              simpa using VExpr.lowerN_closedN
                (count := k) (depth := 0) (remaining := params)
                expressionClosed' (parametersFree' expression expressionMember)
          · simp at run
  | _ => simp [head_eq] at run

/-- Recursive nested replacement preserves specification-value closure when
its source expression is closed at the current local-binder plus block-
parameter boundary. -/
theorem ElimNested.replace_specValuesClosed
    {targets : List NestedTargetBlock} {uvars params : Nat}
    {doms : List VExpr} {e e' : VExpr} {k : Nat}
    {state finalState : ElimNested.State}
    (run : ElimNested.replace targets uvars params doms e k state =
      some (e', finalState))
    (stateClosed : state.SpecValuesClosed params)
    (closed : e.ClosedN (k + params)) :
    finalState.SpecValuesClosed params := by
  induction e generalizing k state e' finalState with
  | app function argument functionIH argumentIH =>
      simp only [ElimNested.replace] at run
      cases rewriteRun : ElimNested.replace.rewrite? targets uvars params doms
          (.app function argument) k state with
      | none =>
          rw [rewriteRun] at run
          obtain ⟨functionResult, functionRun, run⟩ :=
            Option.bind_eq_some_iff.mp run
          obtain ⟨function', functionState⟩ := functionResult
          obtain ⟨argumentResult, argumentRun, run⟩ :=
            Option.bind_eq_some_iff.mp run
          obtain ⟨argument', argumentState⟩ := argumentResult
          cases run
          exact argumentIH argumentRun
            (functionIH functionRun stateClosed closed.1) closed.2
      | some rewriteResult =>
          rw [rewriteRun] at run
          cases rewriteResult with
          | none => contradiction
          | some result =>
              obtain ⟨resultExpr, resultState⟩ := result
              cases run
              exact ElimNested.replace_rewrite_specValuesClosed rewriteRun
                stateClosed closed
  | const name levels =>
      simp only [ElimNested.replace] at run
      cases rewriteRun : ElimNested.replace.rewrite? targets uvars params doms
          (.const name levels) k state with
      | none =>
          rw [rewriteRun] at run
          cases run
          exact stateClosed
      | some rewriteResult =>
          rw [rewriteRun] at run
          cases rewriteResult with
          | none => contradiction
          | some result =>
              obtain ⟨resultExpr, resultState⟩ := result
              cases run
              exact ElimNested.replace_rewrite_specValuesClosed rewriteRun
                stateClosed closed
  | lam domain body domainIH bodyIH =>
      simp only [ElimNested.replace] at run
      obtain ⟨domainResult, domainRun, run⟩ :=
        Option.bind_eq_some_iff.mp run
      obtain ⟨domain', domainState⟩ := domainResult
      obtain ⟨bodyResult, bodyRun, run⟩ :=
        Option.bind_eq_some_iff.mp run
      obtain ⟨body', bodyState⟩ := bodyResult
      cases run
      have bodyClosed : body.ClosedN ((k + 1) + params) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using closed.2
      exact bodyIH bodyRun (domainIH domainRun stateClosed closed.1) bodyClosed
  | forallE domain body domainIH bodyIH =>
      simp only [ElimNested.replace] at run
      obtain ⟨domainResult, domainRun, run⟩ :=
        Option.bind_eq_some_iff.mp run
      obtain ⟨domain', domainState⟩ := domainResult
      obtain ⟨bodyResult, bodyRun, run⟩ :=
        Option.bind_eq_some_iff.mp run
      obtain ⟨body', bodyState⟩ := bodyResult
      cases run
      have bodyClosed : body.ClosedN ((k + 1) + params) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using closed.2
      exact bodyIH bodyRun (domainIH domainRun stateClosed closed.1) bodyClosed
  | _ =>
      simp only [ElimNested.replace] at run
      cases run
      exact stateClosed

/-- A source-ordered constructor rewrite preserves specification-value
closure when every constructor entering that exact trace has closed stored
metadata. -/
theorem ElimNested.RewriteCtorsTrace.specValuesClosed
    {targets : List NestedTargetBlock} {uvars params : Nat}
    {constructors output : List VConstVal}
    {state finalState : ElimNested.State}
    (trace : ElimNested.RewriteCtorsTrace targets uvars params
      constructors output state finalState)
    (stateClosed : state.SpecValuesClosed params)
    (constructorsClosed : ∀ constructor ∈ constructors,
      constructor.type.ClosedN) :
    finalState.SpecValuesClosed params := by
  induction trace with
  | nil => exact stateClosed
  | @cons constructor constructors output state replacementState finalState
      body parametersLength replacement tail ih =>
      have constructorClosed : constructor.type.ClosedN :=
        constructorsClosed constructor (by simp)
      have bodyClosed :
          (VExpr.dropN params constructor.type).ClosedN (0 + params) := by
        simpa [Nat.add_comm] using constructorClosed.dropN params
      have replacementClosed := ElimNested.replace_specValuesClosed
        replacement stateClosed bodyClosed
      apply ih replacementClosed
      intro candidate member
      exact constructorsClosed candidate (List.mem_cons_of_mem constructor member)

/-- The same exact constructor trace preserves closure of every family still
queued in the growing flattening state. -/
theorem ElimNested.RewriteCtorsTrace.typesClosed
    {targets : List NestedTargetBlock} {uvars params : Nat}
    {constructors output : List VConstVal}
    {state finalState : ElimNested.State}
    (trace : ElimNested.RewriteCtorsTrace targets uvars params
      constructors output state finalState)
    (targetsClosed : NestedTargetsClosed targets)
    (stateClosed : state.TypesClosed)
    (constructorsClosed : ∀ constructor ∈ constructors,
      constructor.type.ClosedN) :
    finalState.TypesClosed := by
  induction trace with
  | nil => exact stateClosed
  | @cons constructor constructors output state replacementState finalState
      body parametersLength replacement tail ih =>
      have constructorClosed : constructor.type.ClosedN :=
        constructorsClosed constructor (by simp)
      have bodyClosed :
          (VExpr.dropN params constructor.type).ClosedN (0 + params) := by
        simpa [Nat.add_comm] using constructorClosed.dropN params
      have domsClosed :
          (VExpr.forallN (VExpr.telN params constructor.type)
            (.sort .zero)).ClosedN := by
        have recomposed :
            (VExpr.forallN (VExpr.telN params constructor.type)
              (VExpr.dropN params constructor.type)).ClosedN := by
          simpa only [VExpr.forallN_telN_dropN] using constructorClosed
        apply recomposed.forallN_retarget
        trivial
      have replacementStateClosed := ElimNested.replace_typesClosed
        replacement targetsClosed stateClosed domsClosed parametersLength
          bodyClosed
      apply ih replacementStateClosed
      intro candidate member
      exact constructorsClosed candidate (List.mem_cons_of_mem constructor member)

/-- Every constructor emitted by the exact constructor trace remains closed.
This is the expression-side invariant used when the enclosing family cursor
installs the rewritten constructor list back into its array position. -/
theorem ElimNested.RewriteCtorsTrace.outputClosed
    {targets : List NestedTargetBlock} {uvars params : Nat}
    {constructors output : List VConstVal}
    {state finalState : ElimNested.State}
    (trace : ElimNested.RewriteCtorsTrace targets uvars params
      constructors output state finalState)
    (constructorsClosed : ∀ constructor ∈ constructors,
      constructor.type.ClosedN) :
    ∀ constructor ∈ output, constructor.type.ClosedN := by
  induction trace with
  | nil => simp
  | @cons constructor constructors output state replacementState finalState
      body parametersLength replacement tail ih =>
      have constructorClosed : constructor.type.ClosedN :=
        constructorsClosed constructor (by simp)
      have sourceBodyClosed :
          (VExpr.dropN params constructor.type).ClosedN (0 + params) := by
        simpa [Nat.add_comm] using constructorClosed.dropN params
      have resultBodyClosed : body.ClosedN (0 + params) :=
        ElimNested.replace_closedN replacement sourceBodyClosed
      have domsClosed :
          (VExpr.forallN (VExpr.telN params constructor.type)
            (.sort .zero)).ClosedN := by
        have recomposed :
            (VExpr.forallN (VExpr.telN params constructor.type)
              (VExpr.dropN params constructor.type)).ClosedN := by
          simpa only [VExpr.forallN_telN_dropN] using constructorClosed
        apply recomposed.forallN_retarget
        trivial
      intro candidate member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · change (VExpr.forallN (VExpr.telN params constructor.type) body).ClosedN
        apply domsClosed.forallN_retarget
        rw [parametersLength]
        simpa using resultBodyClosed
      · apply ih
        · intro tailConstructor tailMember
          exact constructorsClosed tailConstructor
            (List.mem_cons_of_mem constructor tailMember)
        · exact member

/-- Recursive nested replacement is inverted exactly by restoration.  The
terminal lookup premises describe only the producer's eventual specification
inventory; each atomic rewrite is retargeted to that inventory using the
prefix trace retained by `replace`. -/
theorem ElimNested.replace_restoreExpr
    {targets : List NestedTargetBlock} {uvars params : Nat}
    {doms : List VExpr} {e e' : VExpr} {k : Nat}
    {state state' final : ElimNested.State}
    {entries : List RestoreEntry} {recMap : List (Name × Name)}
    (run : ElimNested.replace targets uvars params doms e k state =
      some (e', state'))
    (extension : state'.specs.toList <+: final.specs.toList)
    (closed : e.ClosedN (k + params))
    (inert : RestoreInert entries recMap e)
    (entryLookup : ∀ spec ∈ final.specs.toList,
      entries.find? (·.aux == spec.aux) =
        some (⟨spec.aux, params, spec.value⟩ : RestoreEntry))
    (auxRecFree : ∀ spec ∈ final.specs.toList,
      recMap.find? (·.1 == spec.aux) = none) :
    restoreExpr entries recMap e' = e := by
  induction e generalizing k state e' state' with
  | app function argument functionIH argumentIH =>
      simp only [ElimNested.replace] at run
      cases rewriteRun : ElimNested.replace.rewrite? targets uvars params
          doms (.app function argument) k state with
      | none =>
          rw [rewriteRun] at run
          obtain ⟨functionResult, functionRun, run⟩ :=
            Option.bind_eq_some_iff.mp run
          obtain ⟨function', functionState⟩ := functionResult
          obtain ⟨argumentResult, argumentRun, run⟩ :=
            Option.bind_eq_some_iff.mp run
          obtain ⟨argument', argumentState⟩ := argumentResult
          cases run
          have functionExtension :
              functionState.specs.toList <+: final.specs.toList :=
            elimNestedSpecsPrefix_trans
              (ElimNested.replace_specs_prefix targets uvars params
                argumentRun) extension
          have functionInert : RestoreInert entries recMap function :=
            inert.of_hasConst fun _ present => by
              simp only [VExpr.hasConst, Bool.or_eq_true]
              exact .inl present
          have argumentInert : RestoreInert entries recMap argument :=
            inert.of_hasConst fun _ present => by
              simp only [VExpr.hasConst, Bool.or_eq_true]
              exact .inr present
          have functionRestored :
              restoreExpr entries recMap function' = function :=
            functionIH functionRun functionExtension closed.1 functionInert
          have argumentRestored :
              restoreExpr entries recMap argument' = argument :=
            argumentIH argumentRun extension closed.2 argumentInert
          change (restoreExpr.restoreSpine entries recMap
            ((restoreExpr entries recMap function').app
              (restoreExpr entries recMap argument'))).getD _ =
                .app function argument
          rw [functionRestored, argumentRestored,
            restoreSpine_eq_none_of_inert inert]
          rfl
      | some rewriteResult =>
          rw [rewriteRun] at run
          cases rewriteResult with
          | none => contradiction
          | some result =>
              obtain ⟨resultExpr, resultState⟩ := result
              cases run
              obtain ⟨atomic⟩ :=
                ElimNested.replace_rewrite_result targets uvars params
                  rewriteRun
              let terminal := atomic.mono uvars params extension
              have hentry := entryLookup terminal.spec terminal.spec_mem
              have hauxRec := auxRecFree terminal.spec terminal.spec_mem
              exact terminal.restoreExpr_eq_of_source hauxRec
                (by simpa [ElimNested.ReplacementResult.restoreEntry]
                  using hentry)
                closed inert
  | const name levels =>
      simp only [ElimNested.replace] at run
      cases rewriteRun : ElimNested.replace.rewrite? targets uvars params
          doms (.const name levels) k state with
      | none =>
          rw [rewriteRun] at run
          cases run
          exact inert.restoreExpr_eq
      | some rewriteResult =>
          rw [rewriteRun] at run
          cases rewriteResult with
          | none => contradiction
          | some result =>
              obtain ⟨resultExpr, resultState⟩ := result
              cases run
              obtain ⟨atomic⟩ :=
                ElimNested.replace_rewrite_result targets uvars params
                  rewriteRun
              let terminal := atomic.mono uvars params extension
              have hentry := entryLookup terminal.spec terminal.spec_mem
              have hauxRec := auxRecFree terminal.spec terminal.spec_mem
              exact terminal.restoreExpr_eq_of_source hauxRec
                (by simpa [ElimNested.ReplacementResult.restoreEntry]
                  using hentry)
                closed inert
  | lam domain body domainIH bodyIH =>
      simp only [ElimNested.replace] at run
      obtain ⟨domainResult, domainRun, run⟩ :=
        Option.bind_eq_some_iff.mp run
      obtain ⟨domain', domainState⟩ := domainResult
      obtain ⟨bodyResult, bodyRun, run⟩ :=
        Option.bind_eq_some_iff.mp run
      obtain ⟨body', bodyState⟩ := bodyResult
      cases run
      have domainExtension :
          domainState.specs.toList <+: final.specs.toList :=
        elimNestedSpecsPrefix_trans
          (ElimNested.replace_specs_prefix targets uvars params bodyRun)
          extension
      have domainInert : RestoreInert entries recMap domain :=
        inert.of_hasConst fun _ present => by
          simp only [VExpr.hasConst, Bool.or_eq_true]
          exact .inl present
      have bodyInert : RestoreInert entries recMap body :=
        inert.of_hasConst fun _ present => by
          simp only [VExpr.hasConst, Bool.or_eq_true]
          exact .inr present
      have domainRestored : restoreExpr entries recMap domain' = domain :=
        domainIH domainRun domainExtension closed.1 domainInert
      have bodyClosed : body.ClosedN ((k + 1) + params) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using closed.2
      have bodyRestored : restoreExpr entries recMap body' = body :=
        bodyIH bodyRun extension bodyClosed bodyInert
      simp only [restoreExpr, domainRestored, bodyRestored]
  | forallE domain body domainIH bodyIH =>
      simp only [ElimNested.replace] at run
      obtain ⟨domainResult, domainRun, run⟩ :=
        Option.bind_eq_some_iff.mp run
      obtain ⟨domain', domainState⟩ := domainResult
      obtain ⟨bodyResult, bodyRun, run⟩ :=
        Option.bind_eq_some_iff.mp run
      obtain ⟨body', bodyState⟩ := bodyResult
      cases run
      have domainExtension :
          domainState.specs.toList <+: final.specs.toList :=
        elimNestedSpecsPrefix_trans
          (ElimNested.replace_specs_prefix targets uvars params bodyRun)
          extension
      have domainInert : RestoreInert entries recMap domain :=
        inert.of_hasConst fun _ present => by
          simp only [VExpr.hasConst, Bool.or_eq_true]
          exact .inl present
      have bodyInert : RestoreInert entries recMap body :=
        inert.of_hasConst fun _ present => by
          simp only [VExpr.hasConst, Bool.or_eq_true]
          exact .inr present
      have domainRestored : restoreExpr entries recMap domain' = domain :=
        domainIH domainRun domainExtension closed.1 domainInert
      have bodyClosed : body.ClosedN ((k + 1) + params) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using closed.2
      have bodyRestored : restoreExpr entries recMap body' = body :=
        bodyIH bodyRun extension bodyClosed bodyInert
      simp only [restoreExpr, domainRestored, bodyRestored]
  | bvar index =>
      simp only [ElimNested.replace] at run
      cases run
      rfl
  | sort level =>
      simp only [ElimNested.replace] at run
      cases run
      rfl

/-- The checked nested block supplies both canonical terminal restoration
facts for every specification reached by a recursive replacement: its exact
declaration-world entry and exclusion from the recursor-renaming domain.
Thus a consumer of the producer trace retains only semantic closure and
inertness of the source expression. -/
theorem NestedBlockChecked.replace_restoreExpr
    {source : VInductDecl} (nested : source.NestedBlockChecked)
    {doms : List VExpr} {e e' : VExpr} {k : Nat}
    {state state' : ElimNested.State}
    (run : ElimNested.replace nested.elim.targets source.uvars source.nparams
      doms e k state = some (e', state'))
    (extension : state'.specs.toList <+:
      nested.elim.state.specs.toList)
    (closed : e.ClosedN (k + source.nparams))
    (inert : RestoreInert nested.declEntries nested.recMap e) :
    restoreExpr nested.declEntries nested.recMap e' = e := by
  apply ElimNested.replace_restoreExpr run extension closed inert
  · intro spec member
    have specMember : spec ∈ nested.elim.specs := by
      rw [nested.elim.specs_eq]
      exact member
    exact nested.declEntries_find?_of_mem specMember
  · intro spec member
    exact nested.recMap_find?_state_aux_eq_none member

/-- A constructor-loop trace only extends the auxiliary-specification
inventory. -/
theorem ElimNested.RewriteCtorsTrace.specs_prefix
    {targets : List NestedTargetBlock} {uvars params : Nat}
    {constructors output : List VConstVal}
    {state finalState : ElimNested.State}
    (trace : ElimNested.RewriteCtorsTrace targets uvars params
      constructors output state finalState) :
    state.specs.toList <+: finalState.specs.toList := by
  induction trace with
  | nil => exact ⟨[], by simp⟩
  | cons parametersLength replacement tail ih =>
      exact elimNestedSpecsPrefix_trans
        (ElimNested.replace_specs_prefix targets uvars params replacement) ih

/-- A constructor-loop trace only appends families to its state. -/
theorem ElimNested.RewriteCtorsTrace.types_prefix
    {targets : List NestedTargetBlock} {uvars params : Nat}
    {constructors output : List VConstVal}
    {state finalState : ElimNested.State}
    (trace : ElimNested.RewriteCtorsTrace targets uvars params
      constructors output state finalState) :
    state.types.toList <+: finalState.types.toList := by
  induction trace with
  | nil => exact ⟨[], by simp⟩
  | cons parametersLength replacement tail ih =>
      obtain ⟨leftSuffix, leftEq⟩ :=
        ElimNested.replace_types_prefix targets uvars params replacement
      obtain ⟨rightSuffix, rightEq⟩ := ih
      refine ⟨leftSuffix ++ rightSuffix, ?_⟩
      rw [← List.append_assoc, leftEq, rightEq]

/-- An array prefix preserves every lookup already present in the smaller
array. -/
private theorem ElimNested.array_getElem?_of_toList_prefix
    {α : Type} {before after : Array α} {index : Nat} {value : α}
    (hprefix : before.toList <+: after.toList)
    (found : before[index]? = some value) :
    after[index]? = some value := by
  obtain ⟨suffix, prefixEq⟩ := hprefix
  have beforeList : before.toList[index]? = some value := by
    simpa using found
  have upper : index < before.toList.length :=
    (List.getElem?_eq_some_iff.1 beforeList).1
  have afterList : after.toList[index]? = some value := by
    rw [← prefixEq, List.getElem?_append_left]
    · exact beforeList
    · exact upper
  simpa using afterList

/-- The enclosing family traversal also only extends the specification
inventory. -/
theorem ElimNested.RunTrace.specs_prefix
    {targets : List NestedTargetBlock} {uvars params index : Nat}
    {state finalState : ElimNested.State}
    (trace : ElimNested.RunTrace targets uvars params index state
      finalState) :
    state.specs.toList <+: finalState.specs.toList := by
  induction trace with
  | done => exact ⟨[], by simp⟩
  | step upper constructorsTrace tail ih =>
      exact elimNestedSpecsPrefix_trans constructorsTrace.specs_prefix ih

/-- The complete retained family traversal preserves both queued-metadata
closure and specification-value closure.  Each step consumes the exact
constructor list stored at its cursor and installs the exact rewritten list
proved closed by that constructor trace. -/
theorem ElimNested.RunTrace.finalClosures
    {targets : List NestedTargetBlock} {uvars params index : Nat}
    {state finalState : ElimNested.State}
    (trace : ElimNested.RunTrace targets uvars params index state finalState)
    (targetsClosed : NestedTargetsClosed targets)
    (stateTypesClosed : state.TypesClosed)
    (stateSpecsClosed : state.SpecValuesClosed params) :
    finalState.TypesClosed ∧ finalState.SpecValuesClosed params := by
  induction trace with
  | done => exact ⟨stateTypesClosed, stateSpecsClosed⟩
  | @step index state rewrittenState finalState constructors upper
      constructorsTrace tail ih =>
      have currentClosed : state.types[index].NestedMetadataClosed :=
        stateTypesClosed state.types[index]
          (Array.getElem_mem_toList upper)
      have rewrittenTypesClosed := constructorsTrace.typesClosed
        targetsClosed stateTypesClosed currentClosed.2
      have rewrittenSpecsClosed := constructorsTrace.specValuesClosed
        stateSpecsClosed currentClosed.2
      have constructorsClosed := constructorsTrace.outputClosed
        currentClosed.2
      let updatedFamily : VInductiveType :=
        { state.types[index] with ctors := constructors }
      have updatedFamilyClosed : updatedFamily.NestedMetadataClosed := by
        simpa [updatedFamily, VInductiveType.NestedMetadataClosed] using
          (show state.types[index].type.ClosedN ∧
              (∀ constructor ∈ constructors, constructor.type.ClosedN) from
            ⟨currentClosed.1, constructorsClosed⟩)
      have updatedTypesClosed :
          ({ rewrittenState with
            types := rewrittenState.types.set! index updatedFamily } :
              ElimNested.State).TypesClosed := by
        intro family member
        change family ∈
          (rewrittenState.types.set! index updatedFamily).toList at member
        rw [Array.toList_set!] at member
        rcases List.mem_or_eq_of_mem_set member with old | equal
        · exact rewrittenTypesClosed family old
        · subst family
          exact updatedFamilyClosed
      exact ih updatedTypesClosed rewrittenSpecsClosed

/-- Exact end-to-end producer closure for the exposed auxiliary inventory.
The only inputs are closure of the source declaration metadata and closure of
the exact target-block copies consulted by the retained elimination run. -/
theorem NestedElimination.specValuesClosed
    {source : VInductDecl} (elim : source.NestedElimination)
    (sourceClosed : ∀ family ∈ source.types,
      family.NestedMetadataClosed)
    (targetsClosed : NestedTargetsClosed elim.targets) :
    ∀ spec ∈ elim.specs, spec.value.ClosedN source.nparams := by
  let initial : ElimNested.State :=
    { types := source.types.toArray, specs := #[] }
  have initialTypesClosed : initial.TypesClosed := by
    intro family member
    apply sourceClosed family
    simpa [initial] using member
  have initialSpecsClosed : initial.SpecValuesClosed source.nparams := by
    intro spec member
    simp [initial] at member
  have trace := ElimNested.run_trace elim.targets source.uvars
    source.nparams elim.run_eq
  have terminal := trace.finalClosures targetsClosed initialTypesClosed
    initialSpecsClosed
  intro spec member
  apply terminal.2 spec
  rw [← elim.specs_eq]
  exact member

/-- Exact end-to-end producer closure for every family and constructor in
the exposed flattened block. -/
theorem NestedElimination.flatMetadataClosed
    {source : VInductDecl} (elim : source.NestedElimination)
    (sourceClosed : ∀ family ∈ source.types,
      family.NestedMetadataClosed)
    (targetsClosed : NestedTargetsClosed elim.targets) :
    ∀ family ∈ elim.flat.types, family.NestedMetadataClosed := by
  let initial : ElimNested.State :=
    { types := source.types.toArray, specs := #[] }
  have initialTypesClosed : initial.TypesClosed := by
    intro family member
    apply sourceClosed family
    simpa [initial] using member
  have initialSpecsClosed : initial.SpecValuesClosed source.nparams := by
    intro spec member
    simp [initial] at member
  have trace := ElimNested.run_trace elim.targets source.uvars
    source.nparams elim.run_eq
  have terminal := trace.finalClosures targetsClosed initialTypesClosed
    initialSpecsClosed
  intro family member
  have flatTypesEq : elim.flat.types = elim.state.types.toList := by
    simpa using congrArg VInductDecl.types elim.flat_eq
  rw [flatTypesEq] at member
  apply terminal.1 family
  exact member

/-- Declaration-world restoration entries are closed over the exact shared
parameter boundary whenever their producer inputs are closed. -/
theorem NestedBlockChecked.declEntriesClosed
    {source : VInductDecl} (nested : source.NestedBlockChecked)
    (sourceClosed : ∀ family ∈ source.types,
      family.NestedMetadataClosed)
    (targetsClosed : NestedTargetsClosed nested.elim.targets) :
    RestoreEntriesClosed nested.declEntries := by
  intro entry member
  unfold NestedBlockChecked.declEntries at member
  obtain ⟨spec, specMember, rfl⟩ := List.mem_map.mp member
  simpa using nested.elim.specValuesClosed sourceClosed targetsClosed
    spec specMember

/-- Recursor-world restoration entries inherit the same closure after the
producer's exact universe-offset instantiation. -/
theorem NestedBlockChecked.recEntriesClosed
    {source : VInductDecl} (nested : source.NestedBlockChecked)
    (sourceClosed : ∀ family ∈ source.types,
      family.NestedMetadataClosed)
    (targetsClosed : NestedTargetsClosed nested.elim.targets) :
    RestoreEntriesClosed nested.recEntries := by
  intro entry member
  unfold NestedBlockChecked.recEntries at member
  obtain ⟨spec, specMember, rfl⟩ := List.mem_map.mp member
  simpa using (nested.elim.specValuesClosed sourceClosed targetsClosed
    spec specMember).instL

/-- Every family/constructor constant exposed by the flattened declaration
has a closed raw type. -/
theorem NestedBlockChecked.flatDeclarationConstantsClosed
    {source : VInductDecl} (nested : source.NestedBlockChecked)
    (sourceClosed : ∀ family ∈ source.types,
      family.NestedMetadataClosed)
    (targetsClosed : NestedTargetsClosed nested.elim.targets) :
    ∀ constant ∈ nested.flatDeclarationConstants,
      constant.type.ClosedN := by
  intro constant member
  simp only [NestedBlockChecked.flatDeclarationConstants,
    List.mem_append] at member
  rcases member with familyMember | constructorMember
  · simp only [VInductDecl.blockTypeConstants, List.mem_map] at familyMember
    obtain ⟨family, familyMember, rfl⟩ := familyMember
    exact (nested.elim.flatMetadataClosed sourceClosed targetsClosed
      family familyMember).1
  · simp only [VInductDecl.blockConstructorConstants,
      List.mem_flatMap] at constructorMember
    obtain ⟨family, familyMember, constructorMember⟩ := constructorMember
    exact (nested.elim.flatMetadataClosed sourceClosed targetsClosed
      family familyMember).2 constant constructorMember

/-- The generation-shape gate proves that every flattened family and
constructor constant exposes the complete shared-parameter telescope. -/
theorem NestedBlockChecked.flatDeclarationConstants_params_length
    {source : VInductDecl} (nested : source.NestedBlockChecked) :
    ∀ constant ∈ nested.flatDeclarationConstants,
      (VExpr.telN source.nparams constant.type).length = source.nparams := by
  intro constant member
  simp only [NestedBlockChecked.flatDeclarationConstants,
    List.mem_append] at member
  rcases member with familyMember | constructorMember
  · simp only [VInductDecl.blockTypeConstants, List.mem_map] at familyMember
    obtain ⟨raw, rawMember, rfl⟩ := familyMember
    have mappedMember :
        raw ∈ nested.generation.families.map (·.raw) := by
      rw [nested.generation.families_map_raw]
      exact rawMember
    obtain ⟨family, familyMember, rfl⟩ := List.mem_map.mp mappedMember
    have lengthEq :=
      (nested.generation.shape.2.2.2.2 family familyMember).2.2.1
    rw [nested.elim.nparams_eq] at lengthEq
    exact lengthEq
  · simp only [VInductDecl.blockConstructorConstants,
      List.mem_flatMap] at constructorMember
    obtain ⟨rawFamily, rawFamilyMember, rawConstructorMember⟩ :=
      constructorMember
    have mappedFamily :
        rawFamily ∈ nested.generation.families.map (·.raw) := by
      rw [nested.generation.families_map_raw]
      exact rawFamilyMember
    obtain ⟨family, familyMember, familyRawEq⟩ :=
      List.mem_map.mp mappedFamily
    have rawConstructorMember' : constant ∈ family.raw.ctors := by
      rw [familyRawEq]
      exact rawConstructorMember
    have mappedConstructor : constant ∈ family.ctorPairs.map (·.raw) := by
      rw [family.ctorPairs_map_raw familyMember]
      exact rawConstructorMember'
    obtain ⟨ctor, ctorMember, ctorRawEq⟩ :=
      List.mem_map.mp mappedConstructor
    have lengthEq :=
      ((nested.generation.shape.2.2.2.2 family familyMember).2.2.2.2.2.2
        ctor ctorMember).2.2.1
    rw [nested.elim.nparams_eq] at lengthEq
    rw [ctorRawEq] at lengthEq
    exact lengthEq

/-- The canonical interpretation value of a flattened family or constructor
is closed.  The original raw type supplies the lambda domains, while the
producer-closed restoration inventory closes the restored formal body. -/
theorem NestedBlockChecked.declarationInterpValue_closed
    {source : VInductDecl} (nested : source.NestedBlockChecked)
    {constant : VConstVal} (constantMember :
      constant ∈ nested.flatDeclarationConstants)
    (sourceClosed : ∀ family ∈ source.types,
      family.NestedMetadataClosed)
    (targetsClosed : NestedTargetsClosed nested.elim.targets) :
    (nested.declarationInterpValue constant).ClosedN 0 := by
  let binders := VExpr.telN source.nparams constant.type
  let parameters := VExpr.bvarRevRange 0 source.nparams
  have bindersLength : binders.length = source.nparams := by
    exact nested.flatDeclarationConstants_params_length constant
      constantMember
  have applicationClosed :
      ((VExpr.const constant.name (VLevel.params constant.uvars)).appN
        parameters).ClosedN source.nparams := by
    apply VExpr.ClosedN.appN (by trivial)
    intro parameter parameterMember
    exact VInductDecl.bvarRevRange_closedN source.nparams 0
      source.nparams (by omega) parameter parameterMember
  have restoredClosed := VInductDecl.restoreExpr_closedN
    nested.declEntries
    (nested.declEntriesClosed sourceClosed targetsClosed)
    nested.recMap applicationClosed
  have rawTypeClosed : constant.type.ClosedN :=
    nested.flatDeclarationConstantsClosed sourceClosed targetsClosed
      constant constantMember
  have recomposedClosed :
      (VExpr.forallN binders
        (VExpr.dropN source.nparams constant.type)).ClosedN 0 := by
    simpa [binders, VExpr.forallN_telN_dropN] using rawTypeClosed
  have restoredAtBinders :
      (VInductDecl.restoreExpr nested.declEntries nested.recMap
        ((VExpr.const constant.name (VLevel.params constant.uvars)).appN
          parameters)).ClosedN (0 + binders.length) := by
    simpa [bindersLength] using restoredClosed
  apply VExpr.ClosedN.lamN_of_forallN
  apply recomposedClosed.forallN_retarget restoredAtBinders

/-- The exact checked producer inputs make its canonical restoration
interpretation closed. -/
theorem NestedBlockChecked.restoreInterp_closed
    {source : VInductDecl} (nested : source.NestedBlockChecked)
    (sourceClosed : ∀ family ∈ source.types,
      family.NestedMetadataClosed)
    (targetsClosed : NestedTargetsClosed nested.elim.targets) :
    InterpClosed nested.restoreInterp := by
  intro name value lookup
  unfold NestedBlockChecked.restoreInterp at lookup
  split at lookup
  · injection lookup with valueEq
    subst value
    trivial
  · split at lookup
    · rename_i constant found
      injection lookup with valueEq
      subst value
      apply nested.declarationInterpValue_closed
        (List.mem_of_find?_eq_some found) sourceClosed targetsClosed
    · contradiction

/-- Once the family cursor has passed an array position, later traversal
steps preserve that position literally. -/
theorem ElimNested.RunTrace.getElem?_of_lt
    {targets : List NestedTargetBlock} {uvars params index : Nat}
    {state finalState : ElimNested.State}
    (trace : ElimNested.RunTrace targets uvars params index state
      finalState) {prior : Nat} (passed : prior < index) :
    finalState.types[prior]? = state.types[prior]? := by
  induction trace with
  | done => rfl
  | @step index state rewrittenState finalState constructors upper
      constructorsTrace tail ih =>
      have rewrittenLookup : rewrittenState.types[prior]? =
          state.types[prior]? := by
        cases original : state.types[prior]? with
        | none =>
            have outside : state.types.size ≤ prior := by
              simpa only [Array.getElem?_eq_none_iff] using original
            omega
        | some value =>
            exact ElimNested.array_getElem?_of_toList_prefix
              constructorsTrace.types_prefix original
      have updatedLookup :
          ({ rewrittenState with
            types := rewrittenState.types.set! index
              { state.types[index] with ctors := constructors } } :
              ElimNested.State).types[prior]? =
            rewrittenState.types[prior]? := by
        simp only
        rw [Array.set!_eq_setIfInBounds,
          Array.getElem?_setIfInBounds_ne (by omega)]
      calc
        finalState.types[prior]? =
            ({ rewrittenState with
              types := rewrittenState.types.set! index
                { state.types[index] with ctors := constructors } } :
                  ElimNested.State).types[prior]? :=
          ih (by omega)
        _ = rewrittenState.types[prior]? := updatedLookup
        _ = state.types[prior]? := rewrittenLookup

/-- Select the exact constructor-loop trace that rewrote one family position
between the current traversal cursor and the terminal state. -/
theorem ElimNested.RunTrace.familyRewriteAt
    {targets : List NestedTargetBlock} {uvars params cursor : Nat}
    {state finalState : ElimNested.State}
    (trace : ElimNested.RunTrace targets uvars params cursor state
      finalState)
    {familyIndex : Nat} (notPassed : cursor ≤ familyIndex)
    {sourceFamily flatFamily : VInductiveType}
    (source_at : state.types[familyIndex]? = some sourceFamily)
    (flat_at : finalState.types[familyIndex]? = some flatFamily) :
    ∃ beforeStep afterStep,
      ElimNested.RewriteCtorsTrace targets uvars params
        sourceFamily.ctors flatFamily.ctors beforeStep afterStep ∧
      afterStep.specs.toList <+: finalState.specs.toList := by
  induction trace with
  | @done cursor state finished =>
      obtain ⟨familyUpper, _⟩ :=
        Array.getElem?_eq_some_iff.mp source_at
      exact (finished (Nat.lt_of_le_of_lt notPassed familyUpper)).elim
  | @step cursor state rewrittenState finalState constructors upper
      constructorsTrace tail ih =>
      by_cases selected : cursor = familyIndex
      · subst familyIndex
        have current_at : state.types[cursor]? = some state.types[cursor] := by
          simp only [Array.getElem?_eq_getElem, upper]
        have sourceFamilyEq : state.types[cursor] = sourceFamily :=
          Option.some.inj (current_at.symm.trans source_at)
        subst sourceFamily
        have rewritten_at : rewrittenState.types[cursor]? =
            some state.types[cursor] :=
          ElimNested.array_getElem?_of_toList_prefix
            constructorsTrace.types_prefix current_at
        obtain ⟨rewrittenUpper, _⟩ :=
          Array.getElem?_eq_some_iff.mp rewritten_at
        let updatedFamily : VInductiveType :=
          { state.types[cursor] with ctors := constructors }
        let updatedState : ElimNested.State :=
          { rewrittenState with
            types := rewrittenState.types.set! cursor updatedFamily }
        have updated_at : updatedState.types[cursor]? =
            some updatedFamily := by
          simp only [updatedState]
          rw [Array.set!_eq_setIfInBounds,
            Array.getElem?_setIfInBounds_self_of_lt rewrittenUpper]
        have final_updated := tail.getElem?_of_lt (prior := cursor) (by omega)
        have updatedFamilyEq : updatedFamily = flatFamily :=
          Option.some.inj
            (updated_at.symm.trans (final_updated.symm.trans flat_at))
        have constructorsEq : constructors = flatFamily.ctors := by
          simpa only [updatedFamily] using
            congrArg VInductiveType.ctors updatedFamilyEq
        refine ⟨state, rewrittenState, ?_, tail.specs_prefix⟩
        simpa only [constructorsEq] using constructorsTrace
      · have beforeFamily_at : rewrittenState.types[familyIndex]? =
            some sourceFamily :=
          ElimNested.array_getElem?_of_toList_prefix
            constructorsTrace.types_prefix source_at
        have updatedFamily_at :
            ({ rewrittenState with
              types := rewrittenState.types.set! cursor
                { state.types[cursor] with ctors := constructors } } :
                  ElimNested.State).types[familyIndex]? =
              some sourceFamily := by
          simp only
          rw [Array.set!_eq_setIfInBounds,
            Array.getElem?_setIfInBounds_ne selected]
          exact beforeFamily_at
        exact ih (by omega) updatedFamily_at flat_at

/-- Declaration-world restoration applied to one flattened constructor. -/
def NestedBlockChecked.restoreDeclConstructor
    {source : VInductDecl} (nested : source.NestedBlockChecked)
    (constructor : VConstVal) : VConstVal :=
  { constructor with
      type := restoreExpr nested.declEntries nested.recMap constructor.type }

/-- Exact inversion of the producer's source-ordered constructor loop.  The
terminal checked block fixes every restoration lookup; the only semantic
inputs are closure and restoration-domain inertness of the original source
constructor types. -/
theorem ElimNested.RewriteCtorsTrace.restoreDeclConstructors
    {source : VInductDecl} (nested : source.NestedBlockChecked)
    {constructors output : List VConstVal}
    {state finalState : ElimNested.State}
    (trace : ElimNested.RewriteCtorsTrace nested.elim.targets source.uvars
      source.nparams constructors output state finalState)
    (extension : finalState.specs.toList <+:
      nested.elim.state.specs.toList)
    (closed : ∀ constructor ∈ constructors,
      constructor.type.ClosedN)
    (inert : ∀ constructor ∈ constructors,
      RestoreInert nested.declEntries nested.recMap constructor.type) :
    output.map nested.restoreDeclConstructor = constructors := by
  induction trace with
  | nil => rfl
  | @cons constructor constructors output state replacementState finalState
      body parametersLength replacement tail ih =>
      have constructorClosed : constructor.type.ClosedN :=
        closed constructor (by simp)
      have constructorInert :
          RestoreInert nested.declEntries nested.recMap constructor.type :=
        inert constructor (by simp)
      have bodyClosed :
          (VExpr.dropN source.nparams constructor.type).ClosedN
            source.nparams := by
        simpa only [Nat.zero_add] using
          constructorClosed.dropN source.nparams
      have bodyInert : RestoreInert nested.declEntries nested.recMap
          (VExpr.dropN source.nparams constructor.type) :=
        constructorInert.dropN source.nparams
      have replacementExtension : replacementState.specs.toList <+:
          nested.elim.state.specs.toList :=
        elimNestedSpecsPrefix_trans tail.specs_prefix extension
      have bodyRestored :
          restoreExpr nested.declEntries nested.recMap body =
            VExpr.dropN source.nparams constructor.type :=
        nested.replace_restoreExpr replacement replacementExtension
          (by simpa only [Nat.zero_add] using bodyClosed) bodyInert
      have domainsRestored :
          (VExpr.telN source.nparams constructor.type).map
              (restoreExpr nested.declEntries nested.recMap) =
            VExpr.telN source.nparams constructor.type := by
        have mapped :
            (VExpr.telN source.nparams constructor.type).map
                (restoreExpr nested.declEntries nested.recMap) =
              (VExpr.telN source.nparams constructor.type).map id := by
          apply List.map_congr_left
          intro domain member
          exact (constructorInert.telN source.nparams domain member)
            |>.restoreExpr_eq
        simpa only [List.map_id] using mapped
      have typeRestored :
          restoreExpr nested.declEntries nested.recMap
              (VExpr.forallN (VExpr.telN source.nparams constructor.type)
                body) =
            constructor.type := by
        rw [restoreExpr_forallN, domainsRestored, bodyRestored,
          VExpr.forallN_telN_dropN]
      have headRestored :
          nested.restoreDeclConstructor
              { constructor with type := (VExpr.forallN
                (VExpr.telN source.nparams constructor.type) body) } =
            constructor := by
        cases constructor
        simp only [NestedBlockChecked.restoreDeclConstructor, typeRestored]
      have tailClosed : ∀ candidate ∈ constructors,
          candidate.type.ClosedN := by
        intro candidate member
        exact closed candidate (List.mem_cons_of_mem constructor member)
      have tailInert : ∀ candidate ∈ constructors,
          RestoreInert nested.declEntries nested.recMap candidate.type := by
        intro candidate member
        exact inert candidate (List.mem_cons_of_mem constructor member)
      simp only [List.map_cons, headRestored, List.cons.injEq, true_and]
      exact ih extension tailClosed tailInert

/-- Select the exact constructor-loop trace for a source/flattened family
position from the retained complete elimination execution. -/
theorem NestedElimination.familyRewriteAt
    {source : VInductDecl} (elim : source.NestedElimination)
    {familyIndex : Nat} {sourceFamily flatFamily : VInductiveType}
    (source_at : source.types[familyIndex]? = some sourceFamily)
    (flat_at : elim.flat.types[familyIndex]? = some flatFamily) :
    ∃ beforeStep afterStep,
      ElimNested.RewriteCtorsTrace elim.targets source.uvars source.nparams
        sourceFamily.ctors flatFamily.ctors beforeStep afterStep ∧
      afterStep.specs.toList <+: elim.state.specs.toList := by
  have initial_at :
      source.types.toArray[familyIndex]? = some sourceFamily := by
    simpa using source_at
  have terminal_at : elim.state.types[familyIndex]? = some flatFamily := by
    rw [elim.flat_eq] at flat_at
    simpa using flat_at
  have trace := ElimNested.run_trace elim.targets source.uvars source.nparams
    elim.run_eq
  exact trace.familyRewriteAt (Nat.zero_le familyIndex) initial_at terminal_at

/-- Restoring the exact flattened constructor list at a retained source
family position recovers that source family's constructor list literally. -/
theorem NestedBlockChecked.restoreDeclConstructorsAt
    {source : VInductDecl} (nested : source.NestedBlockChecked)
    {familyIndex : Nat} {sourceFamily flatFamily : VInductiveType}
    (source_at : source.types[familyIndex]? = some sourceFamily)
    (flat_at : nested.elim.flat.types[familyIndex]? = some flatFamily)
    (closed : ∀ constructor ∈ sourceFamily.ctors,
      constructor.type.ClosedN)
    (inert : ∀ constructor ∈ sourceFamily.ctors,
      RestoreInert nested.declEntries nested.recMap constructor.type) :
    flatFamily.ctors.map nested.restoreDeclConstructor =
      sourceFamily.ctors := by
  obtain ⟨beforeStep, afterStep, trace, extension⟩ :=
    nested.elim.familyRewriteAt source_at flat_at
  exact trace.restoreDeclConstructors nested extension closed inert

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

/-- Every lookup after one successful constant insertion is either the exact
inserted payload or an inherited lookup.  This is the local inversion fact
behind exact producer-inventory arguments. -/
theorem addConst_constants_cases
    {env env' : VEnv} {name query : Name} {ci found : VConstant}
    (hadd : env.addConst name ci = some env')
    (lookup : env'.constants query = some found) :
    (query = name ∧ found = ci) ∨ env.constants query = some found := by
  rw [VEnv.addConst_constants_eq hadd] at lookup
  change (if name = query then some ci else env.constants query) =
    some found at lookup
  split at lookup
  next equal =>
    exact .inl ⟨equal.symm, Option.some.inj lookup |>.symm⟩
  next notEqual =>
    exact .inr lookup

/-- Exact lookup inversion for a successful fold of constant insertions.
An output constant is either one payload from the producer-owned input list
or an unchanged constant from the fold's initial environment. -/
theorem foldlM_addConst_constants_cases {α : Type _}
    (name : α → Name) (constant : α → VConstant) :
    ∀ (values : List α) {env env' : VEnv},
      values.foldlM
          (fun env value => env.addConst (name value) (constant value)) env =
        some env' →
      ∀ {query : Name} {found : VConstant},
        env'.constants query = some found →
        (∃ value ∈ values,
          query = name value ∧ found = constant value) ∨
          env.constants query = some found
  | [], _, _, folded, _, _, lookup => by
      cases folded
      exact .inr lookup
  | value :: values, _, _, folded, query, found, lookup => by
      rw [List.foldlM_cons] at folded
      obtain ⟨next, added, tail⟩ := Option.bind_eq_some_iff.1 folded
      rcases foldlM_addConst_constants_cases name constant values tail lookup with
        generated | inherited
      · obtain ⟨candidate, member, candidateName, candidateValue⟩ := generated
        exact .inl ⟨candidate, List.mem_cons_of_mem value member,
          candidateName, candidateValue⟩
      · rcases addConst_constants_cases added inherited with inserted | old
        · exact .inl ⟨value, List.mem_cons_self, inserted.1, inserted.2⟩
        · exact .inr old

/-- A successful fold of constant insertions preserves the registered
definitional-equation inventory exactly. -/
theorem foldlM_addConst_defeqs_iff {α : Type _}
    (name : α → Name) (constant : α → VConstant) :
    ∀ (values : List α) {env env' : VEnv},
      values.foldlM
          (fun env value => env.addConst (name value) (constant value)) env =
        some env' →
      ∀ df : VDefEq, env'.defeqs df ↔ env.defeqs df
  | [], _, _, folded, _ => by
      cases folded
      rfl
  | value :: values, _, _, folded, df => by
      rw [List.foldlM_cons] at folded
      obtain ⟨next, added, tail⟩ := Option.bind_eq_some_iff.1 folded
      exact (foldlM_addConst_defeqs_iff name constant values tail df).trans
        (addConst_defeqs_iff added df)

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

/-- A successful fold of constant insertions preserves the structure-eta
inventory exactly. -/
theorem foldlM_addConst_structEtas_iff {α : Type _}
    (name : α → Name) (constant : α → VConstant) :
    ∀ (values : List α) {env env' : VEnv},
      values.foldlM
          (fun env value => env.addConst (name value) (constant value)) env =
        some env' →
      ∀ rule : VStructEta, env'.structEtas rule ↔ env.structEtas rule
  | [], _, _, folded, _ => by
      cases folded
      rfl
  | value :: values, _, _, folded, rule => by
      rw [List.foldlM_cons] at folded
      obtain ⟨next, added, tail⟩ := Option.bind_eq_some_iff.1 folded
      exact (foldlM_addConst_structEtas_iff name constant values tail rule).trans
        (addConst_structEtas_iff added rule)

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
environment; surviving constants retain an exact target lookup whose stored
type is definitionally equal to its σ̂-image; and registered source equations
become typed target equations between their σ̂-images.  Both latter clauses
are deliberately semantic rather than literal.  Nested restoration registers
the β-collapsed `restoreExpr` image, whereas σ̂ retains the corresponding
lambda redexes.  The staged flattened environments of a nested block and
their restored counterparts form exactly such a morphism, with the auxiliary
families, constructors, and recursors interpreted by their restoration
closures. -/
structure ConstInterp (E E' : VEnv) (interp : Name → Option VExpr) : Prop where
  ordered : VEnv.Ordered E
  ordered' : VEnv.Ordered E'
  closed : InterpClosed interp
  value : ∀ {c ci v}, E.constants c = some ci → interp c = some v →
    E'.HasType ci.uvars [] v (ci.type.substConst interp)
  keep : ∀ {c ci}, E.constants c = some ci → interp c = none →
    ∃ ci' sortLevel, E'.constants c = some ci' ∧
      ci'.uvars = ci.uvars ∧
      E'.IsDefEq ci.uvars [] ci'.type (ci.type.substConst interp)
        (.sort sortLevel)
  defeq : ∀ {df}, E.defeqs df →
    E'.IsDefEq df.uvars [] (df.lhs.substConst interp)
      (df.rhs.substConst interp) (df.type.substConst interp)
  /-- Semantic transport for one *used* primitive structure-eta rule.  Both
  the source premises and their recursively transported target images are
  supplied.  This avoids requiring every registered descriptor in `E` to be
  globally syntactically inert under `interp`: an old descriptor may mention
  a future fresh name in an otherwise unusable position, while any actual
  derivation exposes the typed premises needed to prove local inertness. -/
  structEta : ∀ {rule U Γ levels params resultLevel major},
    E.structEtas rule →
    OnCtx Γ (E.IsType U) →
    (∀ level ∈ levels, level.WF U) →
    levels.length = rule.uvars →
    params.length = rule.nparams →
    E.SpineWF U Γ (rule.familyType.instL levels) params
      (.sort resultLevel) →
    E.HasType U Γ major (rule.structureType levels params) →
    E.HasType U Γ (rule.rebuild levels params major)
      (rule.structureType levels params) →
    E'.SpineWF U (Γ.map (VExpr.substConst interp))
      ((rule.familyType.instL levels).substConst interp)
      (params.map (VExpr.substConst interp)) (.sort resultLevel) →
    E'.HasType U (Γ.map (VExpr.substConst interp))
      (major.substConst interp)
      ((rule.structureType levels params).substConst interp) →
    E'.HasType U (Γ.map (VExpr.substConst interp))
      ((rule.rebuild levels params major).substConst interp)
      ((rule.structureType levels params).substConst interp) →
    E'.IsDefEq U (Γ.map (VExpr.substConst interp))
      ((rule.rebuild levels params major).substConst interp)
      (major.substConst interp)
      ((rule.structureType levels params).substConst interp)

/-- Typed transport along a constant interpretation: every Theory judgment
of the interpreted environment holds of the σ̂-images in the target
environment. -/
theorem IsDefEq.substConst {E E' : VEnv} {interp : Name → Option VExpr}
    (hi : ConstInterp E E' interp)
    (H : E.IsDefEq U Γ e1 e2 A) :
    OnCtx Γ (E.IsType U) →
      E'.IsDefEq U (Γ.map (VExpr.substConst interp))
        (e1.substConst interp) (e2.substConst interp)
        (A.substConst interp) := by
  apply IsDefEq.rec
      (motive_1 := fun Γ e1 e2 A _ =>
        OnCtx Γ (E.IsType U) →
          E'.IsDefEq U (Γ.map (VExpr.substConst interp))
            (e1.substConst interp) (e2.substConst interp)
            (A.substConst interp))
      (motive_2 := fun Γ A es B _ =>
        OnCtx Γ (E.IsType U) →
          E'.SpineWF U (Γ.map (VExpr.substConst interp))
            (A.substConst interp) (es.map (VExpr.substConst interp))
            (B.substConst interp))
      (t := H)
  case bvar =>
    intro _ _ _ h _
    exact .bvar (h.substConst hi.closed)
  case symm =>
    intro _ _ _ _ _ ih hΓ
    exact .symm (ih hΓ)
  case trans =>
    intro _ _ _ _ _ _ _ ih1 ih2 hΓ
    exact .trans (ih1 hΓ) (ih2 hΓ)
  case sortDF =>
    intro _ _ _ h1 h2 h3 _
    exact .sortDF h1 h2 h3
  case constDF =>
    intro c ci ls ls' sourceContext h1 h2 h3 h4 h5 _
    rw [VExpr.substConst_instL (e := ci.type)]
    simp only [VExpr.substConst]
    cases hv : interp c with
    | none =>
      obtain ⟨ci', sortLevel, hlookup, huvars, htype⟩ := hi.keep h1 hv
      have hconst : E'.IsDefEq U
          (sourceContext.map (VExpr.substConst interp))
          (.const c ls) (.const c ls')
          (ci'.type.instL ls) :=
        .constDF hlookup h2 h3 (h4.trans huvars.symm) h5
      have htype' : E'.IsDefEq U
          (sourceContext.map (VExpr.substConst interp))
          (ci'.type.instL ls)
          ((ci.type.substConst interp).instL ls)
          (.sort (sortLevel.inst ls)) := by
        exact (htype.instL h2).weak0 hi.ordered'
      exact .defeqDF htype' hconst
    | some v =>
      have hval := hi.value h1 hv
      have hnil : OnCtx ([] : List VExpr) (E'.IsType ci.uvars) := trivial
      have hcore := hval.instL_r hi.ordered' hnil h2 h3 h5
      exact hcore.weak0 hi.ordered'
  case appDF =>
    intro _ _ _ _ _ _ _ _ _ ih1 ih2 hΓ
    exact (VExpr.substConst_inst hi.closed ..).symm ▸
      .appDF (ih1 hΓ) (ih2 hΓ)
  case lamDF =>
    intro _ _ _ _ _ _ _ h1 _ ih1 ih2 hΓ
    exact .lamDF (ih1 hΓ) (ih2 ⟨hΓ, _, h1.hasType.1⟩)
  case forallEDF =>
    intro _ _ _ _ _ _ _ h1 _ ih1 ih2 hΓ
    exact .forallEDF (ih1 hΓ) (ih2 ⟨hΓ, _, h1.hasType.1⟩)
  case defeqDF =>
    intro _ _ _ _ _ _ _ _ ih1 ih2 hΓ
    exact .defeqDF (ih1 hΓ) (ih2 hΓ)
  case beta =>
    intro _ _ _ _ _ _ h2 ih1 ih2 hΓ
    have hA := h2.isType hi.ordered hΓ
    simpa [VExpr.substConst, VExpr.substConst_inst hi.closed] using
      VEnv.IsDefEq.beta (ih1 ⟨hΓ, hA⟩) (ih2 hΓ)
  case eta =>
    intro _ _ _ _ _ ih hΓ
    simpa [VExpr.substConst, VExpr.substConst_lift hi.closed] using
      VEnv.IsDefEq.eta (ih hΓ)
  case structEta =>
    intro _ _ _ _ _ _ hreg hlevels hlevelsLength hparamsLength
      hSpine hMajor hRebuild ihSpine ihMajor ihRebuild hΓ
    exact hi.structEta hreg hΓ hlevels hlevelsLength hparamsLength
      hSpine hMajor hRebuild (ihSpine hΓ) (ihMajor hΓ) (ihRebuild hΓ)
  case proofIrrel =>
    intro _ _ _ _ _ _ _ ih1 ih2 ih3 hΓ
    exact .proofIrrel (ih1 hΓ) (ih2 hΓ) (ih3 hΓ)
  case extra =>
    intro _ _ _ h1 h2 _ _
    have hcore := (hi.defeq h1).instL h2
    simpa [VExpr.substConst_instL] using hcore.weak0 hi.ordered'
  case nil =>
    intro _ _ _
    exact .nil
  case cons =>
    intro _ _ _ _ _ _ _ _ ihType ihRest hΓ
    exact .cons (ihType hΓ) (by
      simpa only [VExpr.substConst_inst hi.closed] using ihRest hΓ)

/-- Specialized typed transport for the simultaneous body instantiation at
the reduction boundary.  The result is normalized to the σ̂-image body and
pointwise σ̂-image captures expected by restored-rule consumers. -/
theorem IsDefEq.substConst_instRev
    {E E' : VEnv} {interp : Name → Option VExpr}
    (hi : ConstInterp E E' interp)
    {U : Nat} {Γ : List VExpr} {body redex B : VExpr}
    {levels : List VLevel} {args : List VExpr}
    (hΓ : OnCtx Γ (E.IsType U))
    (H : E.IsDefEq U Γ (VExpr.instRev (body.instL levels) args) redex B) :
    E'.IsDefEq U (Γ.map (VExpr.substConst interp))
      (VExpr.instRev ((body.substConst interp).instL levels)
        (args.map (VExpr.substConst interp)))
      (redex.substConst interp) (B.substConst interp) := by
  have hout := H.substConst hi hΓ
  rw [VExpr.substConst_instRev hi.closed,
    VExpr.substConst_instL] at hout
  exact hout

theorem HasType.substConst {E E' : VEnv} {interp : Name → Option VExpr}
    (hi : ConstInterp E E' interp)
    (hΓ : OnCtx Γ (E.IsType U))
    (H : E.HasType U Γ e A) :
    E'.HasType U (Γ.map (VExpr.substConst interp))
      (e.substConst interp) (A.substConst interp) :=
  IsDefEq.substConst hi H hΓ

/-- Application-spine typing transports pointwise along the same constant
interpretation.  This exposes the mutual spine case of `IsDefEq.substConst`
as a reusable boundary for staged nested reductions. -/
theorem SpineWF.substConst {E E' : VEnv} {interp : Name → Option VExpr}
    (hi : ConstInterp E E' interp) :
    ∀ {U : Nat} {Γ : List VExpr} {A es B},
      OnCtx Γ (E.IsType U) →
      E.SpineWF U Γ A es B →
      E'.SpineWF U (Γ.map (VExpr.substConst interp))
        (A.substConst interp) (es.map (VExpr.substConst interp))
        (B.substConst interp)
  | _, _, _, [], _, _, .nil => .nil
  | _, _, _, _ :: _, _, hΓ, .cons he hrest =>
    .cons (he.substConst hi hΓ) (by
      simpa only [VExpr.substConst_inst hi.closed] using
        SpineWF.substConst hi hΓ hrest)

/-- Transport a saturated telescope spine through σ̂ and retarget it to a
definitionally equal restored Pi tower.  The flat spine supplies all
argument typing; the caller supplies only the whole restored-type alignment
and the explicit common arity. -/
theorem SpineWF.substConst_forallN_of_defeq
    {E E' : VEnv} {interp : Name → Option VExpr}
    (hi : ConstInterp E E' interp) (henv : E'.WF)
    {U : Nat} {Γ : List VExpr}
    (hΓSource : OnCtx Γ (E.IsType U))
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
  have hσ := H.substConst hi hΓSource
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
    (hi : ConstInterp E E' interp)
    (hΓ : OnCtx Γ (E.IsType U))
    (H : E.IsType U Γ A) :
    E'.IsType U (Γ.map (VExpr.substConst interp)) (A.substConst interp) :=
  let ⟨_, h⟩ := H; ⟨_, IsDefEq.substConst hi h hΓ⟩

end VEnv

/-- Constant well-formedness transports to the σ̂-image constant. -/
theorem VConstant.WF.substConst {E E' : VEnv} {interp : Name → Option VExpr}
    {ci : VConstant} (hi : VEnv.ConstInterp E E' interp) (H : ci.WF E) :
    VConstant.WF E' ⟨ci.uvars, ci.type.substConst interp⟩ :=
  VEnv.IsType.substConst hi (by trivial) H

/-- Rule well-formedness transports to the σ̂-image rule. -/
theorem VDefEq.WF.substConst {E E' : VEnv} {interp : Name → Option VExpr}
    {df : VDefEq} (hi : VEnv.ConstInterp E E' interp) (H : df.WF E) :
    VDefEq.WF E' ⟨df.uvars, df.lhs.substConst interp,
      df.rhs.substConst interp, df.type.substConst interp⟩ :=
  ⟨VEnv.IsDefEq.substConst hi H.1 (by trivial),
    VEnv.IsDefEq.substConst hi H.2 (by trivial)⟩

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
