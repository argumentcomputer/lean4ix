import Lean4Lean.Theory.Inductive

/-!
# Nested-inductive flattening (L4L-09B)

The Theory mirror of the kernel's `ElimNestedInductive` transformation,
following the committed L4L-09A design
(`Lean4Lean/Verify/Environment/NestedRepresentation.lean`): the stored
payload of a nested declaration is the source `VInductDecl`, and nested
support flows through an additive artifact coupling

1. the flattened mutual block, an ordinary `VInductDecl` handled by the
   existing arbitrary-block analyzer, and
2. one auxiliary specification per auxiliary family — the Theory analog of
   the kernel's `aux2nested` map.

`nestedElimination?` computes both from the source declaration plus the
caller-supplied metadata of the previously declared inductives that are
nested into (`NestedTargetBlock`).  Keeping the target metadata an explicit
input keeps this analyzer environment-free, exactly like `checked?`;
`NestedTargetBlock.WF` separately ties the supplied copy to a Theory
environment.

The transformation mirrors the kernel phase for phase:

- An application `I Ds is` is a nested occurrence when `I` is a family of a
  supplied target block, the spine covers at least `I`'s parameters, and
  the parametric arguments `Ds` mention a family of the growing flattened
  block.  Parametric arguments that also mention a constructor-local binder
  reject the declaration (the kernel's "parameters cannot contain local
  variables"), and matched occurrences are rewritten without descending
  into the emitted replacement, exactly like `Expr.replace`.
- One auxiliary family is created per family of `I`'s block, in `all`
  order, with `I`'s family and constructor types level-instantiated at the
  occurrence's levels and parameter-instantiated at `Ds`; auxiliary
  constructor bodies are queued and flattened by the same loop until the
  block is stable.
- Auxiliary names are canonical: `(`_nested` ++ familyName).appendIndexAfter i`
  with a global counter, matching the kernel's choice whenever the ambient
  environment contains no colliding `_nested.*` constant.  The L4L-09A
  collision probe shows the choice is erased from all final artifacts, and
  in-block collisions are rejected downstream by `blockNamesOK` exactly
  where the kernel's `checkName` rejects its own collisions.

Acceptance (`nestedStage3`) is flattening success plus generation
readiness of the flattened block through the unchanged L4L-08 machinery.
No generated recursor, rule, or environment replay is claimed at this
checkpoint; the restoration substitution over generation artifacts is
L4L-09C's obligation.
-/

namespace Lean4Lean

deriving instance DecidableEq for VDefEq
deriving instance DecidableEq for VInductiveType
deriving instance DecidableEq for VInductDecl

/-- Does `e` mention, through a loose bvar, one of the `k` binders directly
below its root?  `d` counts binders passed inside `e` itself. -/
def VExpr.hasLooseBelow (k : Nat) : VExpr → (d : Nat := 0) → Bool
  | .bvar i, d => d ≤ i && i - d < k
  | .sort _, _ | .const .., _ => false
  | .app e1 e2, d => e1.hasLooseBelow k d || e2.hasLooseBelow k d
  | .lam e1 e2, d | .forallE e1 e2, d =>
      e1.hasLooseBelow k d || e2.hasLooseBelow k (d+1)

/-- Lower every loose bvar of `e` by `n`.  Total; meaningful only when no
loose bvar lies below `n`, which callers establish with `hasLooseBelow`. -/
def VExpr.lowerN (n : Nat) : VExpr → (d : Nat := 0) → VExpr
  | .bvar i, d => if i < d then .bvar i else .bvar (i - n)
  | .sort l, _ => .sort l
  | .const c ls, _ => .const c ls
  | .app e1 e2, d => .app (e1.lowerN n d) (e2.lowerN n d)
  | .lam e1 e2, d => .lam (e1.lowerN n d) (e2.lowerN n (d+1))
  | .forallE e1 e2, d => .forallE (e1.lowerN n d) (e2.lowerN n (d+1))

/-- Lowering the free-variable segment above a local binder prefix and then
lifting it back is exact when the expression does not mention that prefix.
This is the syntactic inverse used by nested restoration for the kernel's
"parameters cannot contain local variables" guard. -/
theorem VExpr.liftN_lowerN_of_hasLooseBelow_eq_false
    {expression : VExpr} {count depth : Nat}
    (free : expression.hasLooseBelow count depth = false) :
    (expression.lowerN count depth).liftN count depth = expression := by
  induction expression generalizing depth with
  | bvar index =>
      simp only [hasLooseBelow, Bool.and_eq_false_iff,
        decide_eq_false_iff_not] at free
      by_cases position : index < depth
      · simp [lowerN, VExpr.liftN, position, liftVar]
      · have depth_le : depth ≤ index := Nat.le_of_not_gt position
        have outside : ¬ index - depth < count := by
          rcases free with below | outside
          · exact (below depth_le).elim
          · exact outside
        have above : depth + count ≤ index := by omega
        simp only [lowerN, if_neg position]
        change VExpr.bvar (liftVar count (index - count) depth) =
          VExpr.bvar index
        rw [liftVar_le (by omega)]
        congr 1
        omega
  | sort | const => rfl
  | app function argument functionIH argumentIH =>
      simp only [hasLooseBelow, Bool.or_eq_false_iff] at free
      simp [lowerN, VExpr.liftN, functionIH free.1, argumentIH free.2]
  | lam domain body domainIH bodyIH =>
      simp only [hasLooseBelow, Bool.or_eq_false_iff] at free
      simp [lowerN, VExpr.liftN, domainIH free.1, bodyIH free.2]
  | forallE domain body domainIH bodyIH =>
      simp only [hasLooseBelow, Bool.or_eq_false_iff] at free
      simp [lowerN, VExpr.liftN, domainIH free.1, bodyIH free.2]

/-- Lowering a guarded variable segment preserves every surrounding free
variable boundary, shifted down by exactly the removed segment length. -/
theorem VExpr.lowerN_closedN {expression : VExpr}
    {count depth remaining : Nat}
    (closed : expression.ClosedN (depth + count + remaining))
    (free : expression.hasLooseBelow count depth = false) :
    (expression.lowerN count depth).ClosedN (depth + remaining) := by
  induction expression generalizing depth with
  | bvar index =>
      simp only [ClosedN] at closed ⊢
      simp only [hasLooseBelow, Bool.and_eq_false_iff,
        decide_eq_false_iff_not] at free
      by_cases position : index < depth
      · simp [lowerN, position, ClosedN]
        omega
      · have depth_le : depth ≤ index := Nat.le_of_not_gt position
        have outside : ¬ index - depth < count := by
          rcases free with below | outside
          · exact (below depth_le).elim
          · exact outside
        simp [lowerN, position, ClosedN]
        omega
  | sort | const => trivial
  | app function argument functionIH argumentIH =>
      simp only [ClosedN] at closed ⊢
      simp only [hasLooseBelow, Bool.or_eq_false_iff] at free
      exact ⟨functionIH closed.1 free.1, argumentIH closed.2 free.2⟩
  | lam domain body domainIH bodyIH =>
      simp only [ClosedN] at closed ⊢
      simp only [hasLooseBelow, Bool.or_eq_false_iff] at free
      exact ⟨domainIH closed.1 free.1, by
        have bodyClosed : body.ClosedN ((depth + 1) + count + remaining) := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using closed.2
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          bodyIH bodyClosed free.2⟩
  | forallE domain body domainIH bodyIH =>
      simp only [ClosedN] at closed ⊢
      simp only [hasLooseBelow, Bool.or_eq_false_iff] at free
      exact ⟨domainIH closed.1 free.1, by
        have bodyClosed : body.ClosedN ((depth + 1) + count + remaining) := by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using closed.2
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          bodyIH bodyClosed free.2⟩

/-- Stripping an outer Pi prefix increases the available local-variable
depth by at most the requested prefix length. -/
theorem VExpr.ClosedN.dropN :
    ∀ (count : Nat) {expression : VExpr} {depth : Nat},
      expression.ClosedN depth →
      (VExpr.dropN count expression).ClosedN (depth + count)
  | 0, _, _, closed => by simpa [VExpr.dropN] using closed
  | count + 1, .forallE domain body, depth, closed => by
      have tail := VExpr.ClosedN.dropN count closed.2
      simpa only [VExpr.dropN, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using tail
  | count + 1, .bvar index, depth, closed => by
      exact closed.mono (by omega)
  | count + 1, .sort level, depth, closed => trivial
  | count + 1, .const name levels, depth, closed => trivial
  | count + 1, .app function argument, depth, closed => by
      exact closed.mono (by omega)
  | count + 1, .lam domain body, depth, closed => by
      exact closed.mono (by omega)

/-- A closed Pi telescope can have its terminal expression replaced by any
other expression closed at the telescope's terminal binder depth. -/
theorem VExpr.ClosedN.forallN_retarget :
    ∀ {domains : List VExpr} {sourceBody targetBody : VExpr} {depth : Nat},
      (VExpr.forallN domains sourceBody).ClosedN depth →
      targetBody.ClosedN (depth + domains.length) →
      (VExpr.forallN domains targetBody).ClosedN depth
  | [], _, _, _, _, targetClosed => by simpa [VExpr.forallN] using targetClosed
  | domain :: domains, sourceBody, targetBody, depth, sourceClosed,
      targetClosed => by
      simp only [VExpr.forallN, ClosedN] at sourceClosed ⊢
      refine ⟨sourceClosed.1, ?_⟩
      apply VExpr.ClosedN.forallN_retarget sourceClosed.2
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using targetClosed

namespace VInductDecl

/-- Simultaneous outermost-first parameter substitution: the first list
element replaces the outermost of the `args.length` innermost loose bvars.
The same shape as `instantiateRev` on the implementation side. -/
def instRevParams : VExpr → List VExpr → VExpr
  | C, [] => C
  | C, e :: es => instRevParams (C.inst e es.length) es

/-- Simultaneous parameter instantiation closes a target body in any ambient
context in which all supplied parameter values are closed. -/
theorem instRevParams_closedN :
    ∀ {body : VExpr} {args : List VExpr} {depth : Nat},
      body.ClosedN (depth + args.length) →
      (∀ argument ∈ args, argument.ClosedN depth) →
      (instRevParams body args).ClosedN depth
  | body, [], depth, bodyClosed, _ => by
      simpa only [instRevParams, List.length_nil, Nat.add_zero] using bodyClosed
  | body, argument :: arguments, depth, bodyClosed, argumentsClosed => by
      simp only [instRevParams]
      have bodyClosed' :
          body.ClosedN (depth + arguments.length + 1) := by
        simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using bodyClosed
      have instantiatedClosed :
          (body.inst argument arguments.length).ClosedN
            (depth + arguments.length) :=
        bodyClosed'.instN (argumentsClosed argument (by simp))
      exact instRevParams_closedN instantiatedClosed
        (fun candidate member =>
          argumentsClosed candidate (List.mem_cons_of_mem argument member))

/-- Substitute the leading `np`-binder telescope of `ty` simultaneously at
`args` (outermost parameter first), mirroring the kernel's
`instantiateForallParams`.  Fails when `ty` exposes fewer than `np`
binders. -/
def instTelescope (np : Nat) (ty : VExpr) (args : List VExpr) :
    Option VExpr := do
  guard (args.length == np)
  guard ((VExpr.telN np ty).length == np)
  return instRevParams (VExpr.dropN np ty) args

/-- Successful parameter-telescope instantiation preserves closure in the
ambient context of the supplied values. -/
theorem instTelescope_closedN
    {np depth : Nat} {type result : VExpr} {args : List VExpr}
    (run : instTelescope np type args = some result)
    (typeClosed : type.ClosedN)
    (argsClosed : ∀ argument ∈ args, argument.ClosedN depth) :
    result.ClosedN depth := by
  unfold instTelescope at run
  by_cases argsLength : args.length = np
  · by_cases telescopeLength : (VExpr.telN np type).length = np
    · simp [guard, argsLength, telescopeLength] at run
      cases run
      apply instRevParams_closedN
      · have dropped : (VExpr.dropN np type).ClosedN np := by
          simpa using typeClosed.dropN np
        rw [argsLength]
        exact dropped.mono (by omega)
      · exact argsClosed
    · simp [guard, argsLength, telescopeLength] at run
  · simp [guard, argsLength] at run

/-- One previously declared mutual block that nested occurrences may point
into.  `families` is the complete block in `all` order, in that block's own
universe parameters; a copy is supplied so the analyzer stays
environment-free, and `NestedTargetBlock.WF` ties the copy to an
environment. -/
structure NestedTargetBlock where
  nparams : Nat
  families : List VInductiveType

/-- Closed raw family and constructor metadata, independent of an ambient
environment. -/
def _root_.Lean4Lean.VInductiveType.NestedMetadataClosed
    (family : VInductiveType) : Prop :=
  family.type.ClosedN ∧
    ∀ constructor ∈ family.ctors, constructor.type.ClosedN

/-- Every family copied into one nested-elimination target block has closed
raw metadata. -/
def NestedTargetBlock.MetadataClosed
    (block : NestedTargetBlock) : Prop :=
  ∀ family ∈ block.families, family.NestedMetadataClosed

/-- Environment-free closedness of every target block consulted by nested
elimination. -/
def NestedTargetsClosed (targets : List NestedTargetBlock) : Prop :=
  ∀ block ∈ targets, block.MetadataClosed

/-- The supplied target copy agrees with the environment's stored
constants. -/
structure NestedTargetBlock.WF (env : VEnv) (block : NestedTargetBlock) :
    Prop where
  families : ∀ f ∈ block.families,
    env.constants f.name = some f.toVConstVal.toVConstant
  ctors : ∀ f ∈ block.families, ∀ c ∈ f.ctors,
    env.constants c.name = some c.toVConstant

def NestedTargetsWF (env : VEnv) (targets : List NestedTargetBlock) : Prop :=
  ∀ t ∈ targets, t.WF env

/-- One auxiliary family created by nested elimination: the Theory analog
of one `aux2nested` binding.  `values` are the parametric arguments `Ds`,
open over the block parameters (innermost bvar = last parameter), in
declaration level-world. -/
structure NestedAuxSpec where
  aux : Name
  target : Name
  levels : List VLevel
  values : List VExpr
  deriving DecidableEq

/-- The nested occurrence this auxiliary family abbreviates: `I Ds`. -/
def NestedAuxSpec.value (spec : NestedAuxSpec) : VExpr :=
  (VExpr.const spec.target spec.levels).appN spec.values

/-- Constructor data that nested elimination is not permitted to change.
Only expressions inside the constructor telescope are rewritten. -/
def VExpr.nestedArity : VExpr → Nat
  | .forallE _ body => VExpr.nestedArity body + 1
  | _ => 0

/-- The restoration-stable arity is the ordinary complete Pi-telescope
length used by inductive generation. -/
theorem VExpr.nestedArity_eq_ctorFields_length (expression : VExpr) :
    VExpr.nestedArity expression = (ctorFields expression).length := by
  induction expression with
  | forallE domain body _ bodyIH =>
      simp [VExpr.nestedArity, ctorFields, bodyIH, Nat.add_comm]
  | bvar | sort | const | app | lam => rfl

@[simp] theorem VExpr.nestedArity_forallN (domains : List VExpr)
    (body : VExpr) :
    VExpr.nestedArity (VExpr.forallN domains body) =
      domains.length + VExpr.nestedArity body := by
  induction domains with
  | nil => simp [VExpr.forallN]
  | cons domain domains ih =>
      simp [VExpr.forallN, VExpr.nestedArity, ih, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm]

/-- Splitting a telescope at an arbitrary parameter boundary preserves its
complete Pi arity, including when the expression ends before the boundary. -/
theorem VExpr.telN_length_add_dropN_nestedArity (count : Nat)
    (expression : VExpr) :
    (VExpr.telN count expression).length +
        VExpr.nestedArity (VExpr.dropN count expression) =
      VExpr.nestedArity expression := by
  induction count generalizing expression with
  | zero => simp [VExpr.telN, VExpr.dropN]
  | succ count ih =>
      cases expression <;>
        simp [VExpr.telN, VExpr.dropN, VExpr.nestedArity, ih,
          Nat.add_assoc, Nat.add_comm]

/-- `telN` consumes exactly the smaller of its requested boundary and the
available Pi arity. -/
theorem VExpr.telN_length_eq_min_nestedArity (count : Nat)
    (expression : VExpr) :
    (VExpr.telN count expression).length =
      min count (VExpr.nestedArity expression) := by
  induction count generalizing expression with
  | zero => simp [VExpr.telN]
  | succ count ih =>
      cases expression <;>
        simp [VExpr.telN, VExpr.nestedArity, ih, Nat.succ_min_succ]

/-- Equal complete Pi arities transport an exact parameter-prefix boundary. -/
theorem VExpr.telN_length_eq_of_nestedArity_eq
    {left right : VExpr} {count : Nat}
    (arity : VExpr.nestedArity left = VExpr.nestedArity right)
    (rightLength : (VExpr.telN count right).length = count) :
    (VExpr.telN count left).length = count := by
  rw [VExpr.telN_length_eq_min_nestedArity] at rightLength ⊢
  rw [arity]
  exact rightLength

/-- Rebuilding a Pi telescope from an explicitly complete prefix recovers
that prefix exactly.  Unlike the projection-layer specialization of this
fact, this version is available at the nested-elimination boundary itself. -/
theorem VExpr.telN_forallN_of_length
    (domains : List VExpr) (body : VExpr) (count : Nat)
    (length_eq : domains.length = count) :
    VExpr.telN count (VExpr.forallN domains body) = domains := by
  induction domains generalizing count with
  | nil =>
      subst count
      rfl
  | cons domain domains ih =>
      cases count with
      | zero => simp at length_eq
      | succ count =>
          simp only [List.length_cons, Nat.succ.injEq] at length_eq
          simp only [VExpr.forallN, VExpr.telN, List.cons.injEq, true_and]
          exact ih count length_eq

@[simp] theorem VExpr.nestedArity_app_appN (function argument : VExpr)
    (arguments : List VExpr) :
    VExpr.nestedArity ((function.app argument).appN arguments) = 0 := by
  induction arguments generalizing function argument with
  | nil => rfl
  | cons next rest ih =>
      simp only [VExpr.appN]
      exact ih (function.app argument) next

@[simp] theorem VExpr.nestedArity_const_appN (name : Name)
    (levels : List VLevel) (arguments : List VExpr) :
    VExpr.nestedArity ((VExpr.const name levels).appN arguments) = 0 := by
  cases arguments with
  | nil => rfl
  | cons argument rest =>
      simp only [VExpr.appN]
      exact VExpr.nestedArity_app_appN _ _ _

structure NestedCtorHeader where
  name : Name
  uvars : Nat
  arity : Nat
  deriving DecidableEq

def VConstVal.nestedHeader (constructor : VConstVal) : NestedCtorHeader :=
  { name := constructor.name
    uvars := constructor.uvars
    arity := VExpr.nestedArity constructor.type }

/-- Family data that nested elimination is not permitted to change.  Source
family types stay literal; constructor names/universe arities stay aligned
while their bodies are rewritten. -/
structure NestedFamilyHeader where
  name : Name
  uvars : Nat
  type : VExpr
  constructors : List NestedCtorHeader
  deriving DecidableEq

def VInductiveType.nestedHeader (family : VInductiveType) :
    NestedFamilyHeader :=
  { name := family.name
    uvars := family.uvars
    type := family.type
    constructors := family.ctors.map VConstVal.nestedHeader }

/-- The constructor prefixes which nested elimination must retain literally.
The transformation rewrites only the body after this shared boundary. -/
def VInductiveType.constructorParameterHeaders
    (np : Nat) (family : VInductiveType) : List (List VExpr) :=
  family.ctors.map fun constructor => VExpr.telN np constructor.type

namespace ElimNested

/-- Growing flattening state.  `types` extends the source families with the
auxiliary families; `specs` aligns with `types.drop ntypes`. -/
structure State where
  types : Array VInductiveType
  specs : Array NestedAuxSpec
  nextIdx : Nat := 1

/-- Every family currently queued by the flattening loop has closed raw
family and constructor metadata. -/
def State.TypesClosed (state : State) : Prop :=
  ∀ family ∈ state.types.toList, family.NestedMetadataClosed

/-- The transformation-stable family skeleton of a growing state. -/
def State.headers (state : State) : List NestedFamilyHeader :=
  state.types.toList.map VInductiveType.nestedHeader

/-- Source-ordered constructor-parameter inventories for every queued
family.  Auxiliary families may extend this list, while existing entries are
preserved exactly. -/
def State.parameterHeaders (np : Nat) (state : State) :
    List (List (List VExpr)) :=
  state.types.toList.map (VInductiveType.constructorParameterHeaders np)

/-- The generated family-name suffix and auxiliary specification inventory
remain positionally aligned throughout flattening. -/
def State.SpecsAligned (baseNames : List Name) (state : State) : Prop :=
  state.types.toList.map (fun family => family.name) =
    baseNames ++ state.specs.toList.map (fun spec => spec.aux)

variable (targets : List NestedTargetBlock) (uvars np : Nat)

/-- The target block owning family `c`, ignoring names that are currently
part of the flattened block itself (the kernel only recognizes previously
*declared* inductives). -/
def findTarget? (st : State) (c : Name) : Option NestedTargetBlock :=
  if st.types.any (·.name == c) then none
  else targets.find? fun t => t.families.any (·.name == c)

/-- Register the auxiliary families for one first-seen nested occurrence
`I Ds` and return the auxiliary family name standing for `I` itself.
`doms` is the discovering constructor's parameter telescope, and `values`
are the parametric arguments in parameter-world. -/
private def registerAuxFamilies (uvars : Nat) (block : NestedTargetBlock)
    (I : Name) (ls : List VLevel) (doms values : List VExpr) :
    List VInductiveType → State → Option Name →
      Option (State × Option Name)
  | [], st, result => some (st, result)
  | J :: families, st, result => do
      if J.uvars != ls.length then failure
      let auxName := (`_nested ++ J.name).appendIndexAfter st.nextIdx
      let auxType ← instTelescope block.nparams (J.type.instL ls) values
      let auxCtors ← J.ctors.mapM fun c => do
        let ctype ← instTelescope block.nparams (c.type.instL ls) values
        return ⟨⟨uvars, VExpr.forallN doms ctype⟩,
          c.name.replacePrefix J.name auxName⟩
      let auxFamily : VInductiveType :=
        { name := auxName, uvars, type := VExpr.forallN doms auxType
          ctors := auxCtors }
      let st :=
        { types := st.types.push auxFamily
          specs := st.specs.push ⟨auxName, J.name, ls, values⟩
          nextIdx := st.nextIdx + 1 }
      let result := if J.name == I then some auxName else result
      registerAuxFamilies uvars block I ls doms values families st result

private theorem registerAuxFamilies_types_prefix
    {uvars : Nat} {block : NestedTargetBlock} {I : Name}
    {ls : List VLevel} {doms values : List VExpr}
    {families : List VInductiveType} {st st' : State}
    {result result' : Option Name}
    (run : registerAuxFamilies uvars block I ls doms values families st result =
      some (st', result')) :
    st.types.toList <+: st'.types.toList := by
  induction families generalizing st result with
  | nil =>
      simp only [registerAuxFamilies, Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      exact ⟨[], by simp⟩
  | cons family families ih =>
      simp only [registerAuxFamilies] at run
      split at run
      · contradiction
      · rename_i level_ok
        obtain ⟨auxType, _auxType_eq, run⟩ :=
          Option.bind_eq_some_iff.mp run
        obtain ⟨auxCtors, _auxCtors_eq, run⟩ :=
          Option.bind_eq_some_iff.mp run
        have tail := ih run
        obtain ⟨suffix, suffix_eq⟩ := tail
        refine ⟨[
          { name := (`_nested ++ family.name).appendIndexAfter st.nextIdx
            uvars := uvars
            type := VExpr.forallN doms auxType
            ctors := auxCtors }] ++ suffix, ?_⟩
        change (st.types.push
          { name := (`_nested ++ family.name).appendIndexAfter st.nextIdx
            uvars := uvars
            type := VExpr.forallN doms auxType
            ctors := auxCtors }).toList ++ suffix = st'.types.toList at suffix_eq
        rw [Array.toList_push, List.append_assoc] at suffix_eq
        simpa using suffix_eq

/-- Auxiliary registration appends specifications in lockstep with the
generated family inventory. -/
private theorem registerAuxFamilies_specs_prefix
    {uvars : Nat} {block : NestedTargetBlock} {I : Name}
    {ls : List VLevel} {doms values : List VExpr}
    {families : List VInductiveType} {st st' : State}
    {result result' : Option Name}
    (run : registerAuxFamilies uvars block I ls doms values families st result =
      some (st', result')) :
    st.specs.toList <+: st'.specs.toList := by
  induction families generalizing st result with
  | nil =>
      simp only [registerAuxFamilies, Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      exact ⟨[], by simp⟩
  | cons family families ih =>
      simp only [registerAuxFamilies] at run
      split at run
      · contradiction
      · obtain ⟨auxType, _auxType_eq, run⟩ :=
          Option.bind_eq_some_iff.mp run
        obtain ⟨auxCtors, _auxCtors_eq, run⟩ :=
          Option.bind_eq_some_iff.mp run
        have tail := ih run
        obtain ⟨suffix, suffix_eq⟩ := tail
        refine ⟨[⟨
          (`_nested ++ family.name).appendIndexAfter st.nextIdx,
          family.name, ls, values⟩] ++ suffix, ?_⟩
        change (st.specs.push ⟨
          (`_nested ++ family.name).appendIndexAfter st.nextIdx,
          family.name, ls, values⟩).toList ++ suffix =
            st'.specs.toList at suffix_eq
        rw [Array.toList_push, List.append_assoc] at suffix_eq
        simpa using suffix_eq

/-- Every specification added by one target-family registration shares the
exact universe spine and lowered parameter vector of the discovered nested
occurrence.  Specifications already present on entry remain distinguishable
as the left disjunct. -/
private theorem registerAuxFamilies_spec_mem
    {uvars : Nat} {block : NestedTargetBlock} {I : Name}
    {ls : List VLevel} {doms values : List VExpr}
    {families : List VInductiveType} {st st' : State}
    {result result' : Option Name} {spec : NestedAuxSpec}
    (run : registerAuxFamilies uvars block I ls doms values families st result =
      some (st', result'))
    (member : spec ∈ st'.specs.toList) :
    spec ∈ st.specs.toList ∨
      spec.levels = ls ∧ spec.values = values := by
  induction families generalizing st result with
  | nil =>
      simp only [registerAuxFamilies, Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      exact .inl member
  | cons family families ih =>
      simp only [registerAuxFamilies] at run
      split at run
      · contradiction
      · obtain ⟨auxType, _auxType_eq, run⟩ :=
          Option.bind_eq_some_iff.mp run
        obtain ⟨auxCtors, _auxCtors_eq, run⟩ :=
          Option.bind_eq_some_iff.mp run
        rcases ih run with prior | shape
        · rw [Array.toList_push, List.mem_append] at prior
          rcases prior with old | added
          · exact .inl old
          · have specEq : spec = ⟨
                (`_nested ++ family.name).appendIndexAfter st.nextIdx,
                family.name, ls, values⟩ := by
              simpa using added
            subst spec
            exact .inr ⟨rfl, rfl⟩
        · exact .inr shape

/-- If auxiliary-family registration returns a selected name, that name was
either already selected on entry or is owned by an exact specification
appended during this run. -/
private theorem registerAuxFamilies_result_spec
    {uvars : Nat} {block : NestedTargetBlock} {I : Name}
    {ls : List VLevel} {doms values : List VExpr}
    {families : List VInductiveType} {st st' : State}
    {result : Option Name} {name : Name}
    (run : registerAuxFamilies uvars block I ls doms values families st result =
      some (st', some name)) :
    result = some name ∨
      ∃ spec ∈ st'.specs.toList,
        spec.aux = name ∧ spec.target = I ∧
          spec.levels = ls ∧ spec.values = values := by
  induction families generalizing st result with
  | nil =>
      simp only [registerAuxFamilies, Option.some.injEq, Prod.mk.injEq] at run
      exact .inl run.2
  | cons family families ih =>
      simp only [registerAuxFamilies] at run
      split at run
      · contradiction
      · obtain ⟨auxType, _auxType_eq, run⟩ :=
          Option.bind_eq_some_iff.mp run
        obtain ⟨auxCtors, _auxCtors_eq, run⟩ :=
          Option.bind_eq_some_iff.mp run
        rcases ih run with prior | witness
        · by_cases selected : family.name == I
          · have targetEq : family.name = I := by
              simpa only [beq_iff_eq] using selected
            have auxEq :
                (`_nested ++ family.name).appendIndexAfter st.nextIdx =
                  name := by
              simpa only [selected, if_true, Option.some.injEq] using prior
            have specPrefix := registerAuxFamilies_specs_prefix run
            obtain ⟨suffix, suffixEq⟩ := specPrefix
            have member :
                (⟨(`_nested ++ family.name).appendIndexAfter st.nextIdx,
                    family.name, ls, values⟩ : NestedAuxSpec) ∈
                  st'.specs.toList := by
              rw [← suffixEq]
              simp
            exact .inr ⟨_, member, auxEq, targetEq, rfl, rfl⟩
          · exact .inl (by simpa [selected] using prior)
        · exact .inr witness

/-- Registering a target-family suffix preserves exact positional alignment
between generated family names and specifications. -/
private theorem registerAuxFamilies_specsAligned
    {baseNames : List Name}
    {uvars : Nat} {block : NestedTargetBlock} {I : Name}
    {ls : List VLevel} {doms values : List VExpr}
    {families : List VInductiveType} {st st' : State}
    {result result' : Option Name}
    (aligned : st.SpecsAligned baseNames)
    (run : registerAuxFamilies uvars block I ls doms values families st result =
      some (st', result')) :
    st'.SpecsAligned baseNames := by
  induction families generalizing st result with
  | nil =>
      simp only [registerAuxFamilies, Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      exact aligned
  | cons family families ih =>
      simp only [registerAuxFamilies] at run
      split at run
      · contradiction
      · obtain ⟨auxType, _auxType_eq, run⟩ :=
          Option.bind_eq_some_iff.mp run
        obtain ⟨auxCtors, _auxCtors_eq, run⟩ :=
          Option.bind_eq_some_iff.mp run
        apply ih (run := run)
        unfold State.SpecsAligned at aligned ⊢
        simp only [Array.toList_push, List.map_append, List.map_singleton]
        rw [aligned]
        simp only [List.append_assoc]

/-- Registering a complete target-family suffix preserves closure of the
growing family queue.  The target metadata is closed in its own declaration
world, while `values` are closed over the discovering block's parameter
telescope. -/
private theorem registerAuxFamilies_typesClosed
    {uvars : Nat} {block : NestedTargetBlock} {I : Name}
    {ls : List VLevel} {doms values : List VExpr}
    {families : List VInductiveType} {st st' : State}
    {result result' : Option Name}
    (stateClosed : st.TypesClosed)
    (familiesClosed : ∀ family ∈ families,
      family.NestedMetadataClosed)
    (domsClosed : (VExpr.forallN doms (.sort .zero)).ClosedN)
    (valuesClosed : ∀ value ∈ values, value.ClosedN doms.length)
    (run : registerAuxFamilies uvars block I ls doms values families st result =
      some (st', result')) :
    st'.TypesClosed := by
  induction families generalizing st result with
  | nil =>
      simp only [registerAuxFamilies, Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      exact stateClosed
  | cons family families ih =>
      simp only [registerAuxFamilies] at run
      split at run
      · contradiction
      · obtain ⟨auxType, auxTypeRun, run⟩ :=
          Option.bind_eq_some_iff.mp run
        obtain ⟨auxCtors, auxCtorsRun, run⟩ :=
          Option.bind_eq_some_iff.mp run
        have familyClosed : family.NestedMetadataClosed :=
          familiesClosed family (by simp)
        have auxTypeClosed : auxType.ClosedN doms.length :=
          instTelescope_closedN auxTypeRun familyClosed.1.instL valuesClosed
        have auxCtorsClosed : ∀ constructor ∈ auxCtors,
            constructor.type.ClosedN := by
          intro constructor member
          have alignment := List.mapM_eq_some.mp auxCtorsRun
          obtain ⟨sourceConstructor, sourceMember, sourceRun⟩ :=
            Lean4Lean.List.Forall₂.forall_exists_r alignment constructor member
          obtain ⟨ctype, ctypeRun, constructorEq⟩ :=
            Option.bind_eq_some_iff.mp sourceRun
          cases constructorEq
          change (VExpr.forallN doms ctype).ClosedN
          apply domsClosed.forallN_retarget
          simpa using instTelescope_closedN ctypeRun
            (familyClosed.2 sourceConstructor sourceMember).instL valuesClosed
        let auxFamily : VInductiveType :=
          { name := (`_nested ++ family.name).appendIndexAfter st.nextIdx
            uvars := uvars
            type := VExpr.forallN doms auxType
            ctors := auxCtors }
        have auxFamilyClosed : auxFamily.NestedMetadataClosed := by
          refine ⟨?_, auxCtorsClosed⟩
          exact domsClosed.forallN_retarget (by simpa using auxTypeClosed)
        have pushedClosed :
            ({ types := st.types.push auxFamily
               specs := st.specs.push ⟨
                 (`_nested ++ family.name).appendIndexAfter st.nextIdx,
                 family.name, ls, values⟩
               nextIdx := st.nextIdx + 1 } : State).TypesClosed := by
          intro candidate candidateMember
          rw [Array.toList_push, List.mem_append] at candidateMember
          rcases candidateMember with old | added
          · exact stateClosed candidate old
          · have candidateEq : candidate = auxFamily := by
              simpa only [List.mem_singleton] using added
            subst candidate
            exact auxFamilyClosed
        exact ih pushedClosed
          (fun candidate member =>
            familiesClosed candidate (List.mem_cons_of_mem family member)) run

def registerAux (st : State) (block : NestedTargetBlock) (I : Name)
    (ls : List VLevel) (doms values : List VExpr) :
    Option (Name × State) := do
  let (st, result) ←
    registerAuxFamilies uvars block I ls doms values block.families st none
  return (← result, st)

/-- Registering an auxiliary block only appends families to the flattening
state; every family already present in the input state remains an exact
prefix of the output inventory. -/
theorem registerAux_types_prefix
    {st st' : State} {block : NestedTargetBlock} {I name : Name}
    {ls : List VLevel} {doms values : List VExpr}
    (run : registerAux uvars st block I ls doms values = some (name, st')) :
    st.types.toList <+: st'.types.toList := by
  unfold registerAux at run
  obtain ⟨pair, familiesRun, run⟩ := Option.bind_eq_some_iff.mp run
  obtain ⟨finalState, result⟩ := pair
  obtain ⟨selected, selectedEq, run⟩ := Option.bind_eq_some_iff.mp run
  cases run
  exact registerAuxFamilies_types_prefix familiesRun

/-- The public one-occurrence auxiliary registration wrapper only appends
specifications. -/
theorem registerAux_specs_prefix
    {st st' : State} {block : NestedTargetBlock} {I name : Name}
    {ls : List VLevel} {doms values : List VExpr}
    (run : registerAux uvars st block I ls doms values = some (name, st')) :
    st.specs.toList <+: st'.specs.toList := by
  unfold registerAux at run
  obtain ⟨pair, familiesRun, run⟩ := Option.bind_eq_some_iff.mp run
  obtain ⟨finalState, result⟩ := pair
  obtain ⟨selected, _selectedEq, run⟩ := Option.bind_eq_some_iff.mp run
  cases run
  exact registerAuxFamilies_specs_prefix familiesRun

/-- Every specification visible after one public auxiliary registration was
either already visible before the call or carries the call's exact universe
spine and lowered parameter vector. -/
theorem registerAux_spec_mem
    {st st' : State} {block : NestedTargetBlock} {I name : Name}
    {ls : List VLevel} {doms values : List VExpr}
    {spec : NestedAuxSpec}
    (run : registerAux uvars st block I ls doms values = some (name, st'))
    (member : spec ∈ st'.specs.toList) :
    spec ∈ st.specs.toList ∨
      spec.levels = ls ∧ spec.values = values := by
  unfold registerAux at run
  obtain ⟨pair, familiesRun, run⟩ := Option.bind_eq_some_iff.mp run
  obtain ⟨finalState, result⟩ := pair
  obtain ⟨selected, _selectedEq, run⟩ := Option.bind_eq_some_iff.mp run
  cases run
  exact registerAuxFamilies_spec_mem familiesRun member

/-- A successful fresh auxiliary registration returns the name of an exact
specification retained in its output state. -/
theorem registerAux_result_spec
    {st st' : State} {block : NestedTargetBlock} {I name : Name}
    {ls : List VLevel} {doms values : List VExpr}
    (run : registerAux uvars st block I ls doms values = some (name, st')) :
    ∃ spec ∈ st'.specs.toList,
      spec.aux = name ∧ spec.target = I ∧
        spec.levels = ls ∧ spec.values = values := by
  unfold registerAux at run
  obtain ⟨pair, familiesRun, run⟩ := Option.bind_eq_some_iff.mp run
  obtain ⟨finalState, result⟩ := pair
  obtain ⟨selected, selectedEq, run⟩ := Option.bind_eq_some_iff.mp run
  cases run
  rw [selectedEq] at familiesRun
  have outcome := registerAuxFamilies_result_spec familiesRun
  exact outcome.resolve_left (by simp)

/-- The public registration wrapper preserves specification alignment. -/
theorem registerAux_specsAligned
    {baseNames : List Name}
    {st st' : State} {block : NestedTargetBlock} {I name : Name}
    {ls : List VLevel} {doms values : List VExpr}
    (aligned : st.SpecsAligned baseNames)
    (run : registerAux uvars st block I ls doms values = some (name, st')) :
    st'.SpecsAligned baseNames := by
  unfold registerAux at run
  obtain ⟨pair, familiesRun, run⟩ := Option.bind_eq_some_iff.mp run
  obtain ⟨finalState, result⟩ := pair
  obtain ⟨selected, _selectedEq, run⟩ := Option.bind_eq_some_iff.mp run
  cases run
  exact registerAuxFamilies_specsAligned aligned familiesRun

/-- The public one-occurrence registration wrapper preserves closure of the
complete growing family queue. -/
theorem registerAux_typesClosed
    {st st' : State} {block : NestedTargetBlock} {I name : Name}
    {ls : List VLevel} {doms values : List VExpr}
    (stateClosed : st.TypesClosed)
    (blockClosed : block.MetadataClosed)
    (domsClosed : (VExpr.forallN doms (.sort .zero)).ClosedN)
    (valuesClosed : ∀ value ∈ values, value.ClosedN doms.length)
    (run : registerAux uvars st block I ls doms values = some (name, st')) :
    st'.TypesClosed := by
  unfold registerAux at run
  obtain ⟨pair, familiesRun, run⟩ := Option.bind_eq_some_iff.mp run
  obtain ⟨finalState, result⟩ := pair
  obtain ⟨selected, _selectedEq, run⟩ := Option.bind_eq_some_iff.mp run
  cases run
  exact registerAuxFamilies_typesClosed stateClosed blockClosed domsClosed
    valuesClosed familiesRun

/-- Rewrite one constructor-body subterm at binder depth `k`, mirroring
`replaceAllNested`: matched occurrences are replaced without descending
into the replacement; unmatched nodes recurse into their children. -/
def replace (doms : List VExpr) :
    VExpr → (k : Nat) → State → Option (VExpr × State)
  | e@(.app f a), k, st => do
      match rewrite? e k st with
      | some result => result
      | none =>
          let (f', st) ← replace doms f k st
          let (a', st) ← replace doms a k st
          return (.app f' a', st)
  | e@(.const ..), k, st => (rewrite? e k st).getD (some (e, st))
  | .lam ty body, k, st => do
      let (ty', st) ← replace doms ty k st
      let (body', st) ← replace doms body (k+1) st
      return (.lam ty' body', st)
  | .forallE ty body, k, st => do
      let (ty', st) ← replace doms ty k st
      let (body', st) ← replace doms body (k+1) st
      return (.forallE ty' body', st)
  | e, _, st => some (e, st)
  where
  /-- `some (some ..)` rewrites the node, `some none` is a hard rejection,
  `none` leaves the node to the structural recursion. -/
  rewrite? (e : VExpr) (k : Nat) (st : State) :
      Option (Option (VExpr × State)) := do
    let .const c ls := VExpr.appHead e | none
    let args := e.appArgs []
    let block ← findTarget? targets st c
    guard (block.nparams ≤ args.length)
    guard (0 < block.nparams)
    let ds := args.take block.nparams
    let names := st.types.toList.map (·.name)
    guard (ds.any (·.hasAnyConst names))
    -- the kernel's "nested inductive datatypes parameters cannot contain
    -- local variables" rejection
    if ds.any (·.hasLooseBelow k) then return none
    let values := ds.map (·.lowerN k)
    let key := (VExpr.const c ls).appN values
    let rest := args.drop block.nparams
    let recover (auxName : Name) (st : State) : VExpr × State :=
      ((VExpr.const auxName (VLevel.params uvars)).appN
        (VExpr.bvarRevRange k np ++ rest), st)
    match st.specs.find? (·.value == key) with
    | some spec => return some (recover spec.aux st)
    | none =>
        match registerAux uvars st block c ls doms values with
        | some (auxName, st) => return some (recover auxName st)
        | none => return none

/-- Exact producer provenance for one atomic nested replacement.  It records
the source application split, the surviving auxiliary specification, the
local-variable guard, and the literal replacement expression. -/
structure ReplacementResult (e e' : VExpr) (k : Nat) (st' : State) where
  target : Name
  levels : List VLevel
  parameters : List VExpr
  trailing : List VExpr
  spec : NestedAuxSpec
  head_eq : e.appHead = .const target levels
  arguments_eq : e.appArgs [] = parameters ++ trailing
  parameters_free : ∀ expression ∈ parameters,
    expression.hasLooseBelow k = false
  spec_mem : spec ∈ st'.specs.toList
  spec_value_eq : spec.value =
    (VExpr.const target levels).appN
      (parameters.map (fun expression => expression.lowerN k))
  result_eq : e' =
    (VExpr.const spec.aux (VLevel.params uvars)).appN
      (VExpr.bvarRevRange k np ++ trailing)

/-- Every successful atomic rewrite exposes its exact restoration inputs;
freshly registered and previously reused specifications share the same
consumer boundary. -/
theorem replace_rewrite_result
    {e e' : VExpr} {k : Nat} {st st' : State}
    (run : replace.rewrite? targets uvars np doms e k st =
      some (some (e', st'))) :
    Nonempty (ReplacementResult uvars np e e' k st') := by
  unfold replace.rewrite? at run
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
        · rename_i spec specFind
          cases run
          exact ⟨{
            target
            levels
            parameters := (e.appArgs []).take block.nparams
            trailing := (e.appArgs []).drop block.nparams
            spec
            head_eq
            arguments_eq := (List.take_append_drop ..).symm
            parameters_free := parametersFree'
            spec_mem := by
              simpa using Array.mem_of_find?_eq_some specFind
            spec_value_eq := by
              simpa only [beq_iff_eq] using Array.find?_some specFind
            result_eq := rfl }⟩
        · split at run
          · rename_i auxName finalState registerRun
            cases run
            obtain ⟨spec, specMem, auxEq, targetEq, levelsEq,
                valuesEq⟩ := registerAux_result_spec uvars registerRun
            exact ⟨{
              target
              levels
              parameters := (e.appArgs []).take block.nparams
              trailing := (e.appArgs []).drop block.nparams
              spec
              head_eq
              arguments_eq := (List.take_append_drop ..).symm
              parameters_free := parametersFree'
              spec_mem := specMem
              spec_value_eq := by
                simp only [NestedAuxSpec.value, targetEq, levelsEq, valuesEq]
              result_eq := by simp only [auxEq] }⟩
          · simp at run
  | _ => simp [head_eq] at run

/-- Atomic replacement provenance retargets to every later state whose
specification inventory extends the producing state. -/
def ReplacementResult.mono
    {e e' : VExpr} {k : Nat} {st' final : State}
    (result : ReplacementResult uvars np e e' k st')
    (extension : st'.specs.toList <+: final.specs.toList) :
    ReplacementResult uvars np e e' k final := {
    target := result.target
    levels := result.levels
    parameters := result.parameters
    trailing := result.trailing
    spec := result.spec
    head_eq := result.head_eq
    arguments_eq := result.arguments_eq
    parameters_free := result.parameters_free
    spec_mem := extension.sublist.subset result.spec_mem
    spec_value_eq := result.spec_value_eq
    result_eq := result.result_eq }

private theorem replace_rewrite_types_prefix
    {e e' : VExpr} {k : Nat} {st st' : State}
    (run : replace.rewrite? targets uvars np doms e k st =
      some (some (e', st'))) :
    st.types.toList <+: st'.types.toList := by
  unfold replace.rewrite? at run
  cases head_eq : e.appHead with
  | const c levels =>
      simp only [head_eq] at run
      obtain ⟨block, _block_eq, run⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨_, _params_bound, run⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨_, _params_pos, run⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨_, _nested_occurrence, run⟩ :=
        Option.bind_eq_some_iff.mp run
      split at run
      · simp at run
      · split at run
        · cases run
          exact ⟨[], by simp⟩
        · split at run
          · rename_i auxName finalState registerRun
            cases run
            exact registerAux_types_prefix uvars registerRun
          · simp at run
  | _ => simp [head_eq] at run

/-- A successful atomic rewrite only appends specifications. -/
private theorem replace_rewrite_specs_prefix
    {e e' : VExpr} {k : Nat} {st st' : State}
    (run : replace.rewrite? targets uvars np doms e k st =
      some (some (e', st'))) :
    st.specs.toList <+: st'.specs.toList := by
  unfold replace.rewrite? at run
  cases head_eq : e.appHead with
  | const c levels =>
      simp only [head_eq] at run
      obtain ⟨block, _block_eq, run⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨_, _params_bound, run⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨_, _params_pos, run⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨_, _nested_occurrence, run⟩ :=
        Option.bind_eq_some_iff.mp run
      split at run
      · simp at run
      · split at run
        · cases run
          exact ⟨[], by simp⟩
        · split at run
          · rename_i auxName finalState registerRun
            cases run
            exact registerAux_specs_prefix uvars registerRun
          · simp at run
  | _ => simp [head_eq] at run

/-- Atomic rewriting preserves the positional family/specification
alignment invariant. -/
private theorem replace_rewrite_specsAligned
    {baseNames : List Name}
    {e e' : VExpr} {k : Nat} {st st' : State}
    (aligned : st.SpecsAligned baseNames)
    (run : replace.rewrite? targets uvars np doms e k st =
      some (some (e', st'))) :
    st'.SpecsAligned baseNames := by
  unfold replace.rewrite? at run
  cases head_eq : e.appHead with
  | const c levels =>
      simp only [head_eq] at run
      obtain ⟨block, _block_eq, run⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨_, _params_bound, run⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨_, _params_pos, run⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨_, _nested_occurrence, run⟩ :=
        Option.bind_eq_some_iff.mp run
      split at run
      · simp at run
      · split at run
        · cases run
          exact aligned
        · split at run
          · rename_i auxName finalState registerRun
            cases run
            exact registerAux_specsAligned uvars aligned registerRun
          · simp at run
  | _ => simp [head_eq] at run

private theorem types_prefix_trans {first middle final : State}
    (left : first.types.toList <+: middle.types.toList)
    (right : middle.types.toList <+: final.types.toList) :
    first.types.toList <+: final.types.toList := by
  obtain ⟨leftSuffix, leftEq⟩ := left
  obtain ⟨rightSuffix, rightEq⟩ := right
  refine ⟨leftSuffix ++ rightSuffix, ?_⟩
  rw [← List.append_assoc, leftEq, rightEq]

private theorem specs_prefix_trans {first middle final : State}
    (left : first.specs.toList <+: middle.specs.toList)
    (right : middle.specs.toList <+: final.specs.toList) :
    first.specs.toList <+: final.specs.toList := by
  obtain ⟨leftSuffix, leftEq⟩ := left
  obtain ⟨rightSuffix, rightEq⟩ := right
  refine ⟨leftSuffix ++ rightSuffix, ?_⟩
  rw [← List.append_assoc, leftEq, rightEq]

/-- Recursive constructor-body rewriting only grows the family inventory;
the original state is an exact prefix of every successful output state. -/
theorem replace_types_prefix
    {doms : List VExpr} {e e' : VExpr} {k : Nat} {st st' : State}
    (run : replace targets uvars np doms e k st = some (e', st')) :
    st.types.toList <+: st'.types.toList := by
  induction e generalizing k st e' st' with
  | app fn arg fnIH argIH =>
      simp only [replace] at run
      cases rewriteRun : replace.rewrite? targets uvars np doms
          (.app fn arg) k st with
      | none =>
          rw [rewriteRun] at run
          obtain ⟨fnResult, fnRun, run⟩ := Option.bind_eq_some_iff.mp run
          obtain ⟨fn', fnState⟩ := fnResult
          obtain ⟨argResult, argRun, run⟩ := Option.bind_eq_some_iff.mp run
          obtain ⟨arg', argState⟩ := argResult
          cases run
          exact types_prefix_trans (fnIH fnRun) (argIH argRun)
      | some rewriteResult =>
          rw [rewriteRun] at run
          cases rewriteResult with
          | none => contradiction
          | some result =>
              obtain ⟨resultExpr, resultState⟩ := result
              cases run
              exact replace_rewrite_types_prefix targets uvars np rewriteRun
  | const name levels =>
      simp only [replace] at run
      cases rewriteRun : replace.rewrite? targets uvars np doms
          (.const name levels) k st with
      | none =>
          rw [rewriteRun] at run
          cases run
          exact ⟨[], by simp⟩
      | some rewriteResult =>
          rw [rewriteRun] at run
          cases rewriteResult with
          | none => contradiction
          | some result =>
              obtain ⟨resultExpr, resultState⟩ := result
              cases run
              exact replace_rewrite_types_prefix targets uvars np rewriteRun
  | lam domain body domainIH bodyIH =>
      simp only [replace] at run
      obtain ⟨domainResult, domainRun, run⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨domain', domainState⟩ := domainResult
      obtain ⟨bodyResult, bodyRun, run⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨body', bodyState⟩ := bodyResult
      cases run
      exact types_prefix_trans (domainIH domainRun) (bodyIH bodyRun)
  | forallE domain body domainIH bodyIH =>
      simp only [replace] at run
      obtain ⟨domainResult, domainRun, run⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨domain', domainState⟩ := domainResult
      obtain ⟨bodyResult, bodyRun, run⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨body', bodyState⟩ := bodyResult
      cases run
      exact types_prefix_trans (domainIH domainRun) (bodyIH bodyRun)
  | _ =>
      simp only [replace] at run
      cases run
      exact ⟨[], by simp⟩

/-- Recursive constructor-body rewriting only appends specifications. -/
theorem replace_specs_prefix
    {doms : List VExpr} {e e' : VExpr} {k : Nat} {st st' : State}
    (run : replace targets uvars np doms e k st = some (e', st')) :
    st.specs.toList <+: st'.specs.toList := by
  induction e generalizing k st e' st' with
  | app fn arg fnIH argIH =>
      simp only [replace] at run
      cases rewriteRun : replace.rewrite? targets uvars np doms
          (.app fn arg) k st with
      | none =>
          rw [rewriteRun] at run
          obtain ⟨fnResult, fnRun, run⟩ := Option.bind_eq_some_iff.mp run
          obtain ⟨fn', fnState⟩ := fnResult
          obtain ⟨argResult, argRun, run⟩ := Option.bind_eq_some_iff.mp run
          obtain ⟨arg', argState⟩ := argResult
          cases run
          exact specs_prefix_trans (fnIH fnRun) (argIH argRun)
      | some rewriteResult =>
          rw [rewriteRun] at run
          cases rewriteResult with
          | none => contradiction
          | some result =>
              obtain ⟨resultExpr, resultState⟩ := result
              cases run
              exact replace_rewrite_specs_prefix targets uvars np rewriteRun
  | const name levels =>
      simp only [replace] at run
      cases rewriteRun : replace.rewrite? targets uvars np doms
          (.const name levels) k st with
      | none =>
          rw [rewriteRun] at run
          cases run
          exact ⟨[], by simp⟩
      | some rewriteResult =>
          rw [rewriteRun] at run
          cases rewriteResult with
          | none => contradiction
          | some result =>
              obtain ⟨resultExpr, resultState⟩ := result
              cases run
              exact replace_rewrite_specs_prefix targets uvars np rewriteRun
  | lam domain body domainIH bodyIH =>
      simp only [replace] at run
      obtain ⟨domainResult, domainRun, run⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨domain', domainState⟩ := domainResult
      obtain ⟨bodyResult, bodyRun, run⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨body', bodyState⟩ := bodyResult
      cases run
      exact specs_prefix_trans (domainIH domainRun) (bodyIH bodyRun)
  | forallE domain body domainIH bodyIH =>
      simp only [replace] at run
      obtain ⟨domainResult, domainRun, run⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨domain', domainState⟩ := domainResult
      obtain ⟨bodyResult, bodyRun, run⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨body', bodyState⟩ := bodyResult
      cases run
      exact specs_prefix_trans (domainIH domainRun) (bodyIH bodyRun)
  | _ =>
      simp only [replace] at run
      cases run
      exact ⟨[], by simp⟩

/-- Recursive replacement preserves exact positional alignment between the
generated family suffix and the specification inventory. -/
theorem replace_specsAligned
    {baseNames : List Name}
    {doms : List VExpr} {e e' : VExpr} {k : Nat} {st st' : State}
    (aligned : st.SpecsAligned baseNames)
    (run : replace targets uvars np doms e k st = some (e', st')) :
    st'.SpecsAligned baseNames := by
  induction e generalizing k st e' st' with
  | app fn arg fnIH argIH =>
      simp only [replace] at run
      cases rewriteRun : replace.rewrite? targets uvars np doms
          (.app fn arg) k st with
      | none =>
          rw [rewriteRun] at run
          obtain ⟨fnResult, fnRun, run⟩ := Option.bind_eq_some_iff.mp run
          obtain ⟨fn', fnState⟩ := fnResult
          obtain ⟨argResult, argRun, run⟩ := Option.bind_eq_some_iff.mp run
          obtain ⟨arg', argState⟩ := argResult
          cases run
          exact argIH (fnIH aligned fnRun) argRun
      | some rewriteResult =>
          rw [rewriteRun] at run
          cases rewriteResult with
          | none => contradiction
          | some result =>
              obtain ⟨resultExpr, resultState⟩ := result
              cases run
              exact replace_rewrite_specsAligned targets uvars np aligned
                rewriteRun
  | const name levels =>
      simp only [replace] at run
      cases rewriteRun : replace.rewrite? targets uvars np doms
          (.const name levels) k st with
      | none =>
          rw [rewriteRun] at run
          cases run
          exact aligned
      | some rewriteResult =>
          rw [rewriteRun] at run
          cases rewriteResult with
          | none => contradiction
          | some result =>
              obtain ⟨resultExpr, resultState⟩ := result
              cases run
              exact replace_rewrite_specsAligned targets uvars np aligned
                rewriteRun
  | lam domain body domainIH bodyIH =>
      simp only [replace] at run
      obtain ⟨domainResult, domainRun, run⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨domain', domainState⟩ := domainResult
      obtain ⟨bodyResult, bodyRun, run⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨body', bodyState⟩ := bodyResult
      cases run
      exact bodyIH (domainIH aligned domainRun) bodyRun
  | forallE domain body domainIH bodyIH =>
      simp only [replace] at run
      obtain ⟨domainResult, domainRun, run⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨domain', domainState⟩ := domainResult
      obtain ⟨bodyResult, bodyRun, run⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨body', bodyState⟩ := bodyResult
      cases run
      exact bodyIH (domainIH aligned domainRun) bodyRun
  | _ =>
      simp only [replace] at run
      cases run
      exact aligned

private theorem replace_rewrite_nestedArity
    {doms : List VExpr} {e e' : VExpr} {k : Nat} {st st' : State}
    (run : replace.rewrite? targets uvars np doms e k st =
      some (some (e', st'))) :
    VExpr.nestedArity e' = 0 := by
  unfold replace.rewrite? at run
  cases head_eq : e.appHead with
  | const c levels =>
      simp only [head_eq] at run
      obtain ⟨block, _block_eq, run⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨_, _params_bound, run⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨_, _params_pos, run⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨_, _nested_occurrence, run⟩ :=
        Option.bind_eq_some_iff.mp run
      split at run
      · simp at run
      · split at run
        · cases run
          simp
        · split at run
          · cases run
            simp
          · simp at run
  | _ => simp [head_eq] at run

/-- Nested replacement changes expressions inside a Pi telescope but never
changes the telescope's binder count. -/
theorem replace_nestedArity
    {doms : List VExpr} {e e' : VExpr} {k : Nat} {st st' : State}
    (run : replace targets uvars np doms e k st = some (e', st')) :
    VExpr.nestedArity e' = VExpr.nestedArity e := by
  induction e generalizing k st e' st' with
  | app function argument functionIH argumentIH =>
      simp only [replace] at run
      cases rewriteRun : replace.rewrite? targets uvars np doms
          (.app function argument) k st with
      | none =>
          rw [rewriteRun] at run
          obtain ⟨functionResult, functionRun, run⟩ :=
            Option.bind_eq_some_iff.mp run
          obtain ⟨function', functionState⟩ := functionResult
          obtain ⟨argumentResult, argumentRun, run⟩ :=
            Option.bind_eq_some_iff.mp run
          obtain ⟨argument', argumentState⟩ := argumentResult
          cases run
          rfl
      | some rewriteResult =>
          rw [rewriteRun] at run
          cases rewriteResult with
          | none => contradiction
          | some result =>
              obtain ⟨resultExpr, resultState⟩ := result
              cases run
              exact replace_rewrite_nestedArity targets uvars np rewriteRun
  | const name levels =>
      simp only [replace] at run
      cases rewriteRun : replace.rewrite? targets uvars np doms
          (.const name levels) k st with
      | none =>
          rw [rewriteRun] at run
          cases run
          rfl
      | some rewriteResult =>
          rw [rewriteRun] at run
          cases rewriteResult with
          | none => contradiction
          | some result =>
              obtain ⟨resultExpr, resultState⟩ := result
              cases run
              exact replace_rewrite_nestedArity targets uvars np rewriteRun
  | forallE domain body domainIH bodyIH =>
      simp only [replace] at run
      obtain ⟨domainResult, domainRun, run⟩ :=
        Option.bind_eq_some_iff.mp run
      obtain ⟨domain', domainState⟩ := domainResult
      obtain ⟨bodyResult, bodyRun, run⟩ :=
        Option.bind_eq_some_iff.mp run
      obtain ⟨body', bodyState⟩ := bodyResult
      cases run
      simp only [VExpr.nestedArity]
      rw [bodyIH bodyRun]
  | lam domain body domainIH bodyIH =>
      simp only [replace] at run
      obtain ⟨domainResult, domainRun, run⟩ :=
        Option.bind_eq_some_iff.mp run
      obtain ⟨domain', domainState⟩ := domainResult
      obtain ⟨bodyResult, bodyRun, run⟩ :=
        Option.bind_eq_some_iff.mp run
      obtain ⟨body', bodyState⟩ := bodyResult
      cases run
      rfl
  | _ =>
      simp only [replace] at run
      cases run
      rfl

/-- Public proof trace for the private source-ordered constructor loop.  Each
output constructor is tied to the exact recursive `replace` execution that
rewrote its source body; no consumer may select a parallel flattened body or
state transition. -/
inductive RewriteCtorsTrace
    (targets : List NestedTargetBlock) (uvars np : Nat) :
    List VConstVal → List VConstVal → State → State → Prop where
  | nil (state : State) :
      RewriteCtorsTrace targets uvars np [] [] state state
  | cons {constructor : VConstVal} {constructors output : List VConstVal}
      {state replacementState finalState : State} {body : VExpr}
      (parameters_length :
        (VExpr.telN np constructor.type).length = np)
      (replacement : replace targets uvars np
        (VExpr.telN np constructor.type)
        (VExpr.dropN np constructor.type) 0 state =
          some (body, replacementState))
      (tail : RewriteCtorsTrace targets uvars np constructors output
        replacementState finalState) :
      RewriteCtorsTrace targets uvars np (constructor :: constructors)
        ({ constructor with type := (VExpr.forallN
          (VExpr.telN np constructor.type) body) } :: output)
        state finalState

private def rewriteCtors (targets : List NestedTargetBlock)
    (uvars np : Nat) : List VConstVal → List VConstVal → State →
      Option (List VConstVal × State)
  | [], rewritten, st => some (rewritten, st)
  | constructor :: constructors, rewritten, st => do
      let doms := VExpr.telN np constructor.type
      guard (doms.length == np)
      let (body, st) ←
        replace targets uvars np doms (VExpr.dropN np constructor.type) 0 st
      rewriteCtors targets uvars np constructors
        (rewritten ++ [{ constructor with type := VExpr.forallN doms body }]) st

/-- The executable constructor loop produces the exact public proof trace,
with its internal output accumulator factored away. -/
private theorem rewriteCtors_trace_acc
    {constructors rewritten output : List VConstVal} {st st' : State}
    (run : rewriteCtors targets uvars np constructors rewritten st =
      some (output, st')) :
    ∃ suffix,
      output = rewritten ++ suffix ∧
      RewriteCtorsTrace targets uvars np constructors suffix st st' := by
  induction constructors generalizing rewritten st output st' with
  | nil =>
      simp only [rewriteCtors, Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      exact ⟨[], by simp, .nil st⟩
  | cons constructor constructors ih =>
      simp only [rewriteCtors] at run
      obtain ⟨_, parametersLength, run⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨replacement, replacementRun, run⟩ :=
        Option.bind_eq_some_iff.mp run
      obtain ⟨body, replacementState⟩ := replacement
      obtain ⟨suffix, outputEq, trace⟩ := ih run
      let rewrittenConstructor : VConstVal :=
        { constructor with type := (VExpr.forallN
          (VExpr.telN np constructor.type) body) }
      refine ⟨rewrittenConstructor :: suffix, ?_, ?_⟩
      · rw [outputEq]
        simp only [rewrittenConstructor, List.append_assoc,
          List.singleton_append]
      · have parametersEq :
            (VExpr.telN np constructor.type).length = np := by
          by_cases equal : (VExpr.telN np constructor.type).length = np
          · exact equal
          · simp [guard, equal] at parametersLength
        exact RewriteCtorsTrace.cons parametersEq replacementRun trace

/-- Accumulator-free constructor executions expose their exact source/output
trace. -/
private theorem rewriteCtors_trace
    {constructors output : List VConstVal} {st st' : State}
    (run : rewriteCtors targets uvars np constructors [] st =
      some (output, st')) :
    RewriteCtorsTrace targets uvars np constructors output st st' := by
  obtain ⟨suffix, outputEq, trace⟩ :=
    rewriteCtors_trace_acc targets uvars np run
  simp only [List.nil_append] at outputEq
  subst output
  exact trace

private theorem rewriteCtors_facts
    {constructors rewritten output : List VConstVal} {st st' : State}
    (run : rewriteCtors targets uvars np constructors rewritten st =
      some (output, st')) :
    st.types.toList <+: st'.types.toList ∧
      output.map VConstVal.nestedHeader =
        rewritten.map VConstVal.nestedHeader ++
          constructors.map VConstVal.nestedHeader := by
  induction constructors generalizing rewritten st output st' with
  | nil =>
      simp only [rewriteCtors, Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      exact ⟨⟨[], by simp⟩, by simp⟩
  | cons constructor constructors ih =>
      simp only [rewriteCtors] at run
      obtain ⟨_, _domsLength, run⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨replacement, replacementRun, run⟩ :=
        Option.bind_eq_some_iff.mp run
      obtain ⟨body, replacementState⟩ := replacement
      have tail := ih run
      have bodyArity := replace_nestedArity targets uvars np replacementRun
      have constructorArity :
          (VExpr.telN np constructor.type).length +
              VExpr.nestedArity body =
            VExpr.nestedArity constructor.type := by
        rw [bodyArity]
        exact VExpr.telN_length_add_dropN_nestedArity np constructor.type
      refine ⟨types_prefix_trans
        (replace_types_prefix targets uvars np replacementRun) tail.1, ?_⟩
      simpa [VConstVal.nestedHeader, List.map_append, List.append_assoc,
        constructorArity]
        using tail.2

/-- Rewriting constructor bodies retains every shared-parameter prefix in
source order.  The output constructor is rebuilt from the literal prefix
selected before `replace` is run on its suffix. -/
private theorem rewriteCtors_parameterHeaders
    {constructors rewritten output : List VConstVal} {st st' : State}
    (run : rewriteCtors targets uvars np constructors rewritten st =
      some (output, st')) :
    output.map (fun constructor => VExpr.telN np constructor.type) =
      rewritten.map (fun constructor => VExpr.telN np constructor.type) ++
        constructors.map (fun constructor =>
          VExpr.telN np constructor.type) := by
  induction constructors generalizing rewritten st output st' with
  | nil =>
      simp only [rewriteCtors, Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      simp
  | cons constructor constructors ih =>
      simp only [rewriteCtors] at run
      obtain ⟨_, parametersLength, run⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨replacement, _replacementRun, run⟩ :=
        Option.bind_eq_some_iff.mp run
      obtain ⟨body, replacementState⟩ := replacement
      have tail := ih run
      have parametersEq :
          (VExpr.telN np constructor.type).length = np := by
        by_cases equal : (VExpr.telN np constructor.type).length = np
        · exact equal
        · simp [guard, equal] at parametersLength
      rw [tail]
      simp only [List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.singleton_append]
      rw [VExpr.telN_forallN_of_length
        (VExpr.telN np constructor.type) body np parametersEq]

/-- Rewriting a source-ordered constructor suffix only appends auxiliary
specifications. -/
private theorem rewriteCtors_specs_prefix
    {constructors rewritten output : List VConstVal} {st st' : State}
    (run : rewriteCtors targets uvars np constructors rewritten st =
      some (output, st')) :
    st.specs.toList <+: st'.specs.toList := by
  induction constructors generalizing rewritten st output st' with
  | nil =>
      simp only [rewriteCtors, Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      exact ⟨[], by simp⟩
  | cons constructor constructors ih =>
      simp only [rewriteCtors] at run
      obtain ⟨_, _domsLength, run⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨replacement, replacementRun, run⟩ :=
        Option.bind_eq_some_iff.mp run
      obtain ⟨body, replacementState⟩ := replacement
      exact specs_prefix_trans
        (replace_specs_prefix targets uvars np replacementRun) (ih run)

/-- Rewriting a constructor suffix preserves family/specification
alignment. -/
private theorem rewriteCtors_specsAligned
    {baseNames : List Name}
    {constructors rewritten output : List VConstVal} {st st' : State}
    (aligned : st.SpecsAligned baseNames)
    (run : rewriteCtors targets uvars np constructors rewritten st =
      some (output, st')) :
    st'.SpecsAligned baseNames := by
  induction constructors generalizing rewritten st output st' with
  | nil =>
      simp only [rewriteCtors, Option.some.injEq, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      exact aligned
  | cons constructor constructors ih =>
      simp only [rewriteCtors] at run
      obtain ⟨_, _domsLength, run⟩ := Option.bind_eq_some_iff.mp run
      obtain ⟨replacement, replacementRun, run⟩ :=
        Option.bind_eq_some_iff.mp run
      obtain ⟨body, replacementState⟩ := replacement
      exact ih (replace_specsAligned targets uvars np aligned replacementRun)
        run

private theorem types_prefix_headers {before after : State}
    (hprefix : before.types.toList <+: after.types.toList) :
    before.headers <+: after.headers := by
  obtain ⟨suffix, suffixEq⟩ := hprefix
  refine ⟨suffix.map VInductiveType.nestedHeader, ?_⟩
  simp only [State.headers, ← List.map_append, suffixEq]

private theorem rewriteCtors_set_headers
    {i : Nat} {st rewrittenState : State} (upper : i < st.types.size)
    {constructors : List VConstVal}
    (hprefix : st.types.toList <+: rewrittenState.types.toList)
    (headers : constructors.map VConstVal.nestedHeader =
      st.types[i].ctors.map VConstVal.nestedHeader) :
    ({ rewrittenState with
      types := rewrittenState.types.set! i { st.types[i] with
        ctors := constructors } }).headers = rewrittenState.headers := by
  let original := st.types[i]
  let replacement : VInductiveType := { original with ctors := constructors }
  obtain ⟨suffix, suffixEq⟩ := hprefix
  have rewrittenUpper : i < rewrittenState.types.toList.length := by
    rw [← suffixEq]
    simp only [List.length_append, Array.length_toList]
    omega
  have originalGet : st.types.toList[i]? = some original := by
    simp [original, upper]
  have rewrittenGet : rewrittenState.types.toList[i]? = some original := by
    rw [← suffixEq, List.getElem?_append_left]
    · exact originalGet
    · simpa only [Array.length_toList] using upper
  have headerGet : rewrittenState.headers[i]? =
      some (VInductiveType.nestedHeader original) := by
    simp only [State.headers, List.getElem?_map, rewrittenGet,
      Option.map_some]
  have headerUpper : i < rewrittenState.headers.length := by
    simpa [State.headers] using rewrittenUpper
  have headerAt : rewrittenState.headers[i] =
      VInductiveType.nestedHeader original := by
    rw [List.getElem?_eq_getElem headerUpper] at headerGet
    exact Option.some.inj headerGet
  have replacementHeader : VInductiveType.nestedHeader replacement =
      VInductiveType.nestedHeader original := by
    simp [replacement, original, VInductiveType.nestedHeader, headers]
  simp only [State.headers, Array.toList_set!, List.map_set]
  rw [replacementHeader, ← headerAt]
  change rewrittenState.headers.set i rewrittenState.headers[i] =
    rewrittenState.headers
  exact List.set_getElem_self headerUpper

/-- Updating the currently processed family with rewritten constructors
leaves its parameter-prefix inventory unchanged.  Any auxiliary families
already appended by body rewriting remain untouched. -/
private theorem rewriteCtors_set_parameterHeaders
    {i : Nat} {st rewrittenState : State} (upper : i < st.types.size)
    {constructors : List VConstVal}
    (hprefix : st.types.toList <+: rewrittenState.types.toList)
    (parameters : constructors.map
        (fun constructor => VExpr.telN np constructor.type) =
      st.types[i].ctors.map
        (fun constructor => VExpr.telN np constructor.type)) :
    ({ rewrittenState with
      types := rewrittenState.types.set! i { st.types[i] with
        ctors := constructors } }).parameterHeaders np =
      rewrittenState.parameterHeaders np := by
  let original := st.types[i]
  let replacement : VInductiveType := { original with ctors := constructors }
  obtain ⟨suffix, suffixEq⟩ := hprefix
  have rewrittenUpper : i < rewrittenState.types.toList.length := by
    rw [← suffixEq]
    simp only [List.length_append, Array.length_toList]
    omega
  have originalGet : st.types.toList[i]? = some original := by
    simp [original, upper]
  have rewrittenGet : rewrittenState.types.toList[i]? = some original := by
    rw [← suffixEq, List.getElem?_append_left]
    · exact originalGet
    · simpa only [Array.length_toList] using upper
  have parameterGet : (rewrittenState.parameterHeaders np)[i]? =
      some (VInductiveType.constructorParameterHeaders np original) := by
    simp only [State.parameterHeaders, List.getElem?_map, rewrittenGet,
      Option.map_some]
  have parameterUpper : i <
      (rewrittenState.parameterHeaders np).length := by
    simpa [State.parameterHeaders] using rewrittenUpper
  have parameterAt : (rewrittenState.parameterHeaders np)[i] =
      VInductiveType.constructorParameterHeaders np original := by
    rw [List.getElem?_eq_getElem parameterUpper] at parameterGet
    exact Option.some.inj parameterGet
  have replacementParameters :
      VInductiveType.constructorParameterHeaders np replacement =
        VInductiveType.constructorParameterHeaders np original := by
    simpa [replacement, original,
      VInductiveType.constructorParameterHeaders] using parameters
  simp only [State.parameterHeaders, Array.toList_set!, List.map_set]
  rw [replacementParameters, ← parameterAt]
  exact List.set_getElem_self parameterUpper

/-- Flatten every constructor of every block family, including the queued
auxiliary families, until the block is stable.  `fuel` mirrors the
kernel's `inductiveFuel` bound on the same loop. -/
def run (fuel : Nat) (i : Nat) (st : State) : Option State :=
  match fuel with
  | 0 => none
  | fuel+1 =>
    if h : i < st.types.size then
      let ty := st.types[i]
      let step := rewriteCtors targets uvars np ty.ctors [] st
      match step with
      | some (ctors, st) =>
          run fuel (i+1) { st with types := st.types.set! i { ty with ctors } }
      | none => none
    else some st

/-- Public proof trace for the private constructor loop nested inside the
family traversal.  It records every exact family update and therefore keeps
the source-to-flattened constructor provenance available after `run` returns
only its terminal state. -/
inductive RunTrace (targets : List NestedTargetBlock) (uvars np : Nat) :
    Nat → State → State → Prop where
  | done {i : Nat} {state : State}
      (finished : ¬ i < state.types.size) :
      RunTrace targets uvars np i state state
  | step {i : Nat} {state rewrittenState finalState : State}
      {constructors : List VConstVal}
      (upper : i < state.types.size)
      (constructorsTrace : RewriteCtorsTrace targets uvars np
        state.types[i].ctors constructors state rewrittenState)
      (tail : RunTrace targets uvars np (i + 1)
        { rewrittenState with
          types := rewrittenState.types.set! i
            { state.types[i] with ctors := constructors } }
        finalState) :
      RunTrace targets uvars np i state finalState

/-- Every successful complete flattening execution retains a public trace of
the exact constructor replacements and family updates it performed. -/
theorem run_trace
    {fuel i : Nat} {st st' : State}
    (run_eq : run targets uvars np fuel i st = some st') :
    RunTrace targets uvars np i st st' := by
  induction fuel generalizing i st st' with
  | zero => simp [run] at run_eq
  | succ fuel ih =>
      simp only [run] at run_eq
      split at run_eq
      · rename_i upper
        cases rewrite_eq : rewriteCtors targets uvars np
            st.types[i].ctors [] st with
        | none => simp [rewrite_eq] at run_eq
        | some result =>
            obtain ⟨constructors, rewrittenState⟩ := result
            rw [rewrite_eq] at run_eq
            exact .step upper
              (rewriteCtors_trace targets uvars np rewrite_eq)
              (ih run_eq)
      · rename_i finished
        cases run_eq
        exact .done finished

private theorem headers_prefix_trans
    {first middle final : List NestedFamilyHeader}
    (left : first <+: middle) (right : middle <+: final) :
    first <+: final := by
  obtain ⟨leftSuffix, leftEq⟩ := left
  obtain ⟨rightSuffix, rightEq⟩ := right
  refine ⟨leftSuffix ++ rightSuffix, ?_⟩
  rw [← List.append_assoc, leftEq, rightEq]

/-- A successful flattening run retains every input family at the same
position and preserves its transformation-stable header.  Any families
created for nested occurrences occur strictly after that prefix. -/
theorem run_headers_prefix
    {fuel i : Nat} {st st' : State}
    (run_eq : run targets uvars np fuel i st = some st') :
    st.headers <+: st'.headers := by
  induction fuel generalizing i st st' with
  | zero => simp [run] at run_eq
  | succ fuel ih =>
      simp only [run] at run_eq
      split at run_eq
      · rename_i upper
        cases rewrite_eq : rewriteCtors targets uvars np
            st.types[i].ctors [] st with
        | none => simp [rewrite_eq] at run_eq
        | some result =>
            obtain ⟨constructors, rewrittenState⟩ := result
            rw [rewrite_eq] at run_eq
            have facts := rewriteCtors_facts targets uvars np rewrite_eq
            have constructorHeaders :
                constructors.map VConstVal.nestedHeader =
                  st.types[i].ctors.map VConstVal.nestedHeader := by
              simpa using facts.2
            have updatedHeaders := rewriteCtors_set_headers upper facts.1
              constructorHeaders
            have tail := ih run_eq
            rw [updatedHeaders] at tail
            exact headers_prefix_trans (types_prefix_headers facts.1) tail
      · cases run_eq
        exact ⟨[], by simp⟩

/-- A complete flattening run preserves the literal constructor-parameter
inventory of every input family.  Only a suffix for newly generated
auxiliary families may be appended. -/
theorem run_parameterHeaders_prefix
    {fuel i : Nat} {st st' : State}
    (run_eq : run targets uvars np fuel i st = some st') :
    st.parameterHeaders np <+: st'.parameterHeaders np := by
  induction fuel generalizing i st st' with
  | zero => simp [run] at run_eq
  | succ fuel ih =>
      simp only [run] at run_eq
      split at run_eq
      · rename_i upper
        cases rewrite_eq : rewriteCtors targets uvars np
            st.types[i].ctors [] st with
        | none => simp [rewrite_eq] at run_eq
        | some result =>
            obtain ⟨constructors, rewrittenState⟩ := result
            rw [rewrite_eq] at run_eq
            have facts := rewriteCtors_facts targets uvars np rewrite_eq
            have parameters := rewriteCtors_parameterHeaders
              targets uvars np rewrite_eq
            have updatedParameters := rewriteCtors_set_parameterHeaders
              (np := np) upper facts.1 (by simpa using parameters)
            have sourcePrefix : st.parameterHeaders np <+:
                rewrittenState.parameterHeaders np := by
              obtain ⟨suffix, typesEq⟩ := facts.1
              refine ⟨suffix.map
                (VInductiveType.constructorParameterHeaders np), ?_⟩
              simp only [State.parameterHeaders]
              rw [← typesEq]
              simp
            have tail := ih run_eq
            rw [updatedParameters] at tail
            obtain ⟨sourceSuffix, sourceEq⟩ := sourcePrefix
            obtain ⟨tailSuffix, tailEq⟩ := tail
            refine ⟨sourceSuffix ++ tailSuffix, ?_⟩
            rw [← List.append_assoc, sourceEq, tailEq]
      · cases run_eq
        exact ⟨[], by simp⟩

/-- Every successful complete flattening run retains the input
specification inventory as an exact prefix of its terminal inventory. -/
theorem run_specs_prefix
    {fuel i : Nat} {st st' : State}
    (run_eq : run targets uvars np fuel i st = some st') :
    st.specs.toList <+: st'.specs.toList := by
  induction fuel generalizing i st st' with
  | zero => simp [run] at run_eq
  | succ fuel ih =>
      simp only [run] at run_eq
      split at run_eq
      · cases rewrite_eq : rewriteCtors targets uvars np
            st.types[i].ctors [] st with
        | none => simp [rewrite_eq] at run_eq
        | some result =>
            obtain ⟨constructors, rewrittenState⟩ := result
            rw [rewrite_eq] at run_eq
            have step := rewriteCtors_specs_prefix targets uvars np rewrite_eq
            have tail := ih run_eq
            exact specs_prefix_trans step tail
      · cases run_eq
        exact ⟨[], by simp⟩

/-- A successful complete flattening run preserves the exact positional
alignment between the original family-name prefix and every accumulated
auxiliary specification. -/
theorem run_specsAligned
    {baseNames : List Name}
    {fuel i : Nat} {st st' : State}
    (aligned : st.SpecsAligned baseNames)
    (run_eq : run targets uvars np fuel i st = some st') :
    st'.SpecsAligned baseNames := by
  induction fuel generalizing i st st' with
  | zero => simp [run] at run_eq
  | succ fuel ih =>
      simp only [run] at run_eq
      split at run_eq
      · rename_i upper
        cases rewrite_eq : rewriteCtors targets uvars np
            st.types[i].ctors [] st with
        | none => simp [rewrite_eq] at run_eq
        | some result =>
            obtain ⟨constructors, rewrittenState⟩ := result
            rw [rewrite_eq] at run_eq
            have rewrittenAligned := rewriteCtors_specsAligned
              targets uvars np aligned rewrite_eq
            have facts := rewriteCtors_facts targets uvars np rewrite_eq
            have constructorHeaders :
                constructors.map VConstVal.nestedHeader =
                  st.types[i].ctors.map VConstVal.nestedHeader := by
              simpa using facts.2
            have updatedHeaders := rewriteCtors_set_headers upper facts.1
              constructorHeaders
            let updatedState : State := {
              rewrittenState with
              types := rewrittenState.types.set! i { st.types[i] with
                ctors := constructors } }
            have updatedNames :
                updatedState.types.toList.map (fun family => family.name) =
                  rewrittenState.types.toList.map
                    (fun family => family.name) := by
              have names := congrArg
                (List.map fun header : NestedFamilyHeader => header.name)
                updatedHeaders
              simpa [updatedState, State.headers, List.map_map,
                Function.comp_def, VInductiveType.nestedHeader] using names
            have updatedAligned : updatedState.SpecsAligned baseNames := by
              unfold State.SpecsAligned at rewrittenAligned ⊢
              rw [updatedNames]
              exact rewrittenAligned
            apply ih updatedAligned
            simpa only [updatedState] using run_eq
      · cases run_eq
        exact aligned

end ElimNested

/-- The flattening result: the flattened mutual block plus one auxiliary
specification per auxiliary family, in flattened family order.  When the
source contains no nested occurrence, `flat` is the source itself and
`specs` is empty.  The successful executable run is retained as producer
provenance for restoration proofs. -/
structure NestedElimination (source : VInductDecl) where
  /-- The exact previously-declared inductive inventory consulted by the
  successful flattening run. -/
  targets : List NestedTargetBlock
  /-- The exact recursion budget consumed by the successful flattening run. -/
  fuel : Nat
  /-- The terminal state returned by the successful flattening run. -/
  state : ElimNested.State
  /-- Producer provenance for `state`. -/
  run_eq : ElimNested.run targets source.uvars source.nparams fuel 0
    { types := source.types.toArray, specs := #[] } = some state
  flat : VInductDecl
  /-- The exposed flattened declaration is exactly the declaration carried by
  the terminal run state. -/
  flat_eq : flat = { source with types := state.types.toList }
  specs : List NestedAuxSpec
  /-- The exposed auxiliary inventory is exactly the terminal run inventory. -/
  specs_eq : specs = state.specs.toList
  /-- Flattening rewrites constructor bodies and may append auxiliary
  families, but it never changes the shared source-parameter boundary. -/
  nparams_eq : flat.nparams = source.nparams

/-- Flatten one source declaration against the supplied target blocks.
Returns the flattened block plus the auxiliary specifications; the
identity result (`flat = source`, no specs) is returned when nothing is
nested. -/
def nestedElimination? (targets : List NestedTargetBlock)
    (source : VInductDecl) (fuel : Nat := 1000) :
    Option (NestedElimination source) :=
  match run_eq : ElimNested.run targets source.uvars source.nparams fuel 0
      { types := source.types.toArray, specs := #[] } with
  | none => none
  | some st => some {
      targets
      fuel
      state := st
      run_eq
      flat := { source with types := st.types.toList }
      flat_eq := rfl
      specs := st.specs.toList
      specs_eq := rfl
      nparams_eq := rfl }

/-- The exposed flattened declaration retains the complete source-family
header inventory as an exact prefix.  In particular, source families stay
at their original offsets while auxiliary families are appended afterward. -/
theorem NestedElimination.source_headers_prefix {source : VInductDecl}
    (elim : NestedElimination source) :
    source.types.map VInductiveType.nestedHeader <+:
      elim.flat.types.map VInductiveType.nestedHeader := by
  have run := ElimNested.run_headers_prefix elim.targets source.uvars
    source.nparams elim.run_eq
  rw [elim.flat_eq]
  simpa [ElimNested.State.headers] using run

/-- The exposed flattened declaration retains every source constructor's
literal shared-parameter prefix at the same family and constructor offsets.
Auxiliary families may only extend the outer inventory. -/
theorem NestedElimination.source_parameterHeaders_prefix
    {source : VInductDecl} (elim : NestedElimination source) :
    source.types.map
        (VInductiveType.constructorParameterHeaders source.nparams) <+:
      elim.flat.types.map
        (VInductiveType.constructorParameterHeaders source.nparams) := by
  have run := ElimNested.run_parameterHeaders_prefix elim.targets source.uvars
    source.nparams elim.run_eq
  rw [elim.flat_eq]
  simpa [ElimNested.State.parameterHeaders] using run

/-- The terminal auxiliary specifications are positionally identical to the
generated family-name suffix after the untouched source-family prefix. -/
theorem NestedElimination.specsAligned {source : VInductDecl}
    (elim : NestedElimination source) :
    elim.flat.types.map (fun family => family.name) =
      source.types.map (fun family => family.name) ++
        elim.specs.map (fun spec => spec.aux) := by
  have initial :
      (ElimNested.State.mk source.types.toArray #[] 1).SpecsAligned
        (source.types.map fun family => family.name) := by
    simp [ElimNested.State.SpecsAligned]
  have terminal := ElimNested.run_specsAligned elim.targets source.uvars
    source.nparams initial elim.run_eq
  rw [elim.flat_eq, elim.specs_eq]
  simpa [ElimNested.State.SpecsAligned] using terminal

/-- Select the flattened family occupying a source-family offset.  Its
name, universe arity, literal family type, and ordered constructor headers
are exactly those of the source family. -/
theorem NestedElimination.flat_family_header_at {source : VInductDecl}
    (elim : NestedElimination source) {i : Nat}
    {sourceFamily : VInductiveType}
    (source_at : source.types[i]? = some sourceFamily) :
    ∃ flatFamily,
      elim.flat.types[i]? = some flatFamily ∧
      VInductiveType.nestedHeader flatFamily =
        VInductiveType.nestedHeader sourceFamily := by
  obtain ⟨suffix, prefixEq⟩ := elim.source_headers_prefix
  have sourceHeaderAt :
      (source.types.map VInductiveType.nestedHeader)[i]? =
        some (VInductiveType.nestedHeader sourceFamily) := by
    simp only [List.getElem?_map, source_at, Option.map_some]
  have flatHeaderAt :
      (elim.flat.types.map VInductiveType.nestedHeader)[i]? =
        some (VInductiveType.nestedHeader sourceFamily) := by
    rw [← prefixEq, List.getElem?_append_left]
    · exact sourceHeaderAt
    · simpa using (List.getElem?_eq_some_iff.1 source_at).1
  have flatUpper : i < elim.flat.types.length := by
    simpa using (List.getElem?_eq_some_iff.1 flatHeaderAt).1
  let flatFamily := elim.flat.types[i]
  have flat_at : elim.flat.types[i]? = some flatFamily :=
    List.getElem?_eq_some_iff.2 ⟨flatUpper, rfl⟩
  refine ⟨flatFamily, flat_at, ?_⟩
  simp only [List.getElem?_map, flat_at, Option.map_some] at flatHeaderAt
  exact Option.some.inj flatHeaderAt

/-- Constructor positions inside retained source families are stable too:
the flattened constructor at the same offset has the same name and universe
arity, although its type body may have been rewritten. -/
theorem NestedElimination.flat_constructor_header_at
    {source : VInductDecl} (elim : NestedElimination source)
    {familyIndex constructorIndex : Nat}
    {sourceFamily : VInductiveType} {sourceConstructor : VConstVal}
    (family_at : source.types[familyIndex]? = some sourceFamily)
    (constructor_at : sourceFamily.ctors[constructorIndex]? =
      some sourceConstructor) :
    ∃ flatFamily flatConstructor,
      elim.flat.types[familyIndex]? = some flatFamily ∧
      flatFamily.ctors[constructorIndex]? = some flatConstructor ∧
      VConstVal.nestedHeader flatConstructor =
        VConstVal.nestedHeader sourceConstructor := by
  obtain ⟨flatFamily, flat_at, familyHeader⟩ :=
    elim.flat_family_header_at family_at
  have constructorHeaders :
      flatFamily.ctors.map VConstVal.nestedHeader =
        sourceFamily.ctors.map VConstVal.nestedHeader :=
    congrArg NestedFamilyHeader.constructors familyHeader
  have sourceHeaderAt :
      (sourceFamily.ctors.map VConstVal.nestedHeader)[constructorIndex]? =
        some (VConstVal.nestedHeader sourceConstructor) := by
    simp only [List.getElem?_map, constructor_at, Option.map_some]
  have flatHeaderAt :
      (flatFamily.ctors.map VConstVal.nestedHeader)[constructorIndex]? =
        some (VConstVal.nestedHeader sourceConstructor) := by
    rw [constructorHeaders]
    exact sourceHeaderAt
  have flatUpper : constructorIndex < flatFamily.ctors.length := by
    simpa using (List.getElem?_eq_some_iff.1 flatHeaderAt).1
  let flatConstructor := flatFamily.ctors[constructorIndex]
  have flatConstructorAt : flatFamily.ctors[constructorIndex]? =
      some flatConstructor := List.getElem?_eq_some_iff.2 ⟨flatUpper, rfl⟩
  refine ⟨flatFamily, flatConstructor, flat_at, flatConstructorAt, ?_⟩
  simp only [List.getElem?_map, flatConstructorAt, Option.map_some] at flatHeaderAt
  exact Option.some.inj flatHeaderAt

/-- At any retained source position, the flattened constructor has exactly
the same first `nparams` domains as the source constructor.  This is stronger
than arity preservation and follows from the producer's literal
`forallN (telN nparams ...)` reconstruction. -/
theorem NestedElimination.flat_constructor_params_eq
    {source : VInductDecl} (elim : NestedElimination source)
    {familyIndex constructorIndex : Nat}
    {sourceFamily flatFamily : VInductiveType}
    {sourceConstructor flatConstructor : VConstVal}
    (sourceFamilyAt : source.types[familyIndex]? = some sourceFamily)
    (flatFamilyAt : elim.flat.types[familyIndex]? = some flatFamily)
    (sourceConstructorAt : sourceFamily.ctors[constructorIndex]? =
      some sourceConstructor)
    (flatConstructorAt : flatFamily.ctors[constructorIndex]? =
      some flatConstructor) :
    VExpr.telN source.nparams flatConstructor.type =
      VExpr.telN source.nparams sourceConstructor.type := by
  obtain ⟨suffix, prefixEq⟩ := elim.source_parameterHeaders_prefix
  have sourceFamilyParametersAt :
      (source.types.map
        (VInductiveType.constructorParameterHeaders source.nparams))[
          familyIndex]? =
        some (VInductiveType.constructorParameterHeaders source.nparams
          sourceFamily) := by
    simp only [List.getElem?_map, sourceFamilyAt, Option.map_some]
  have flatFamilyParametersAt :
      (elim.flat.types.map
        (VInductiveType.constructorParameterHeaders source.nparams))[
          familyIndex]? =
        some (VInductiveType.constructorParameterHeaders source.nparams
          sourceFamily) := by
    rw [← prefixEq, List.getElem?_append_left]
    · exact sourceFamilyParametersAt
    · simpa using (List.getElem?_eq_some_iff.1 sourceFamilyAt).1
  simp only [List.getElem?_map, flatFamilyAt, Option.map_some] at flatFamilyParametersAt
  have familyParametersEq :
      VInductiveType.constructorParameterHeaders source.nparams flatFamily =
        VInductiveType.constructorParameterHeaders source.nparams
          sourceFamily :=
    Option.some.inj flatFamilyParametersAt
  have flatConstructorParametersAt :
      (VInductiveType.constructorParameterHeaders source.nparams flatFamily)[
        constructorIndex]? =
      some (VExpr.telN source.nparams flatConstructor.type) := by
    simp only [VInductiveType.constructorParameterHeaders,
      List.getElem?_map, flatConstructorAt, Option.map_some]
  have sourceConstructorParametersAt :
      (VInductiveType.constructorParameterHeaders source.nparams sourceFamily)[
        constructorIndex]? =
      some (VExpr.telN source.nparams sourceConstructor.type) := by
    simp only [VInductiveType.constructorParameterHeaders,
      List.getElem?_map, sourceConstructorAt, Option.map_some]
  rw [familyParametersEq] at flatConstructorParametersAt
  exact Option.some.inj
    (flatConstructorParametersAt.symm.trans sourceConstructorParametersAt)

/-- The number of auxiliary families, matching the stored
`InductiveVal.numNested` of an accepted nested declaration. -/
def NestedElimination.numNested {source : VInductDecl}
    (elim : NestedElimination source) : Nat :=
  elim.specs.length

/-- Detect a constant name on which the nested restoration substitution can
fire.  Every restoration case is rooted at the name of one exact auxiliary
family retained by the elimination run: the family itself, its recursor, and
its constructors are therefore covered uniformly by prefix membership. -/
def _root_.Lean4Lean.VExpr.hasNestedRestoreConst
    (specs : List NestedAuxSpec) : VExpr → Bool
  | .bvar _ | .sort _ => false
  | .const name _ => specs.any fun spec => spec.aux.isPrefixOf name
  | .app function argument | .lam function argument |
      .forallE function argument =>
    hasNestedRestoreConst specs function ||
      hasNestedRestoreConst specs argument

/-- Executable restoration-domain check for an original source block.  The
restoration pass acts on constant heads as well as on expressions below
binders, so source family and constructor names must themselves remain
outside every auxiliary prefix.  Constructor types retain the corresponding
occurrence-wide condition.  Together these are the exact Theory obligations
needed by restored recursor rules and projector programs. -/
def nestedRestoreSafe (source : VInductDecl)
    (specs : List NestedAuxSpec) : Bool :=
  source.types.all fun family =>
    !(VExpr.const family.name []).hasNestedRestoreConst specs &&
      family.ctors.all fun constructor =>
        !(VExpr.const constructor.name []).hasNestedRestoreConst specs &&
          !constructor.type.hasNestedRestoreConst specs

/-- A flattened declaration accepted by the unchanged arbitrary-block
machinery: the complete L4L-09B validation gate.  Positivity, name, level,
anatomy, and generation-shape checking of the flattened block reuse the
L4L-08 analyzers verbatim. -/
structure NestedBlockChecked (source : VInductDecl) where
  elim : NestedElimination source
  generation : BlockGenerationChecked elim.flat
  /-- The original source syntax and its declaration heads are outside the
  exact domain rewritten by restoration.  Retaining the successful equation
  rules out the historical auxiliary-name escape hatch at the Theory
  artifact boundary. -/
  source_restore_safe : source.nestedRestoreSafe elim.specs = true

def nestedBlockChecked? (targets : List NestedTargetBlock)
    (source : VInductDecl) (fuel : Nat := 1000) :
    Option (NestedBlockChecked source) := do
  let elim ← nestedElimination? targets source fuel
  if hsafe : source.nestedRestoreSafe elim.specs = true then
    let generation ← elim.flat.identityBlockGeneration?
    return ⟨elim, generation, hsafe⟩
  else
    none

/-- Project the exact flattened generation transaction retained by a
successful nested-block check. -/
theorem NestedBlockChecked.generation_eq_of_check
    {targets : List NestedTargetBlock} {source : VInductDecl} {fuel : Nat}
    {nested : NestedBlockChecked source}
    (h : nestedBlockChecked? targets source fuel = some nested) :
    nested.elim.flat.identityBlockGeneration? = some nested.generation := by
  unfold nestedBlockChecked? at h
  obtain ⟨elim, _helim, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · obtain ⟨generation, hgeneration, h⟩ :=
      Option.bind_eq_some_iff.mp h
    cases h
    exact hgeneration
  · contradiction

/-- Structural acceptance for a nested declaration. -/
def nestedStage3 (targets : List NestedTargetBlock)
    (source : VInductDecl) (fuel : Nat := 1000) : Bool :=
  (nestedBlockChecked? targets source fuel).isSome

/-! ## Restoration (L4L-09C)

The restoration substitution σ maps the flattened block's generation
artifacts back to the stored metadata surface: auxiliary family constants
become their nested values, auxiliary constructor constants become the
target block's constructors applied to the instantiated value's own
arguments, and auxiliary recursor constants are renamed onto the main
family's `appendIndexAfter` inventory.  On an application spine headed by
an auxiliary family or constructor, the first `nparams` spine arguments
are consumed by the value instantiation, mirroring
`ElimNestedInductive.Result.restoreNested`; generated artifacts always
apply auxiliary constants to at least the block parameters (the kernel
asserts exactly this), so the identity fallback on an under-applied
auxiliary head is unreachable from real artifacts and merely keeps σ
total. -/

/-- One σ replacement entry.  `value` is already in the level world of the
artifact being restored (`instL`-spliced by the caller for recursor-world
artifacts). -/
structure RestoreEntry where
  aux : Name
  np : Nat
  value : VExpr
  deriving DecidableEq

def findRestoreCtor (entries : List RestoreEntry) (c : Name) :
    Option (RestoreEntry × Name) :=
  entries.findSome? fun entry =>
    if entry.aux.isPrefixOf c && c != entry.aux then
      some (entry, c.replacePrefix entry.aux .anonymous)
    else none

/-- σ on one expression, bottom-up: a replacement fires at the innermost
spine node where an auxiliary head has collected exactly its block-parameter
count, and enclosing applications extend the already-restored value.  On
generated artifacts — where auxiliary constants are always applied to at
least the block parameters and never occur inside another auxiliary spine's
arguments — this coincides with `restoreNested`'s top-down
replace-without-descending pass.  `recMap` renames auxiliary recursor
constants and is consulted before the constructor-prefix case, exactly like
`restoreNested`'s `auxRec` map. -/
def restoreExpr (entries : List RestoreEntry) (recMap : List (Name × Name)) :
    VExpr → VExpr
  | .bvar i => .bvar i
  | .sort l => .sort l
  | .lam ty body => .lam (restoreExpr entries recMap ty) (restoreExpr entries recMap body)
  | .forallE ty body =>
      .forallE (restoreExpr entries recMap ty) (restoreExpr entries recMap body)
  | .app f a =>
      let e := VExpr.app (restoreExpr entries recMap f) (restoreExpr entries recMap a)
      (restoreSpine e).getD e
  | e@(.const ..) => (restoreSpine e).getD e
  where
  /-- Fire one replacement at a completed spine.  The head constant is
  still unrestored exactly when no inner node completed its parameter
  count. -/
  restoreSpine (e : VExpr) : Option VExpr :=
    match VExpr.appHead e with
    | .const c ls =>
      let args := e.appArgs []
      match recMap.find? (·.1 == c) with
      | some (_, newName) =>
          if args.isEmpty then some (VExpr.const newName ls) else none
      | none =>
      match entries.find? (·.aux == c) with
      | some entry =>
          if args.length == entry.np then
            some (instRevParams entry.value args)
          else none
      | none =>
      match findRestoreCtor entries c with
      | some (entry, suffix) =>
          if args.length == entry.np then
            let value := instRevParams entry.value args
            match VExpr.appHead value with
            | .const iname ils =>
                some ((VExpr.const (iname ++ suffix) ils).appN (value.appArgs []))
            | _ => none
          else none
      | none => none
    | _ => none

namespace NestedBlockChecked

variable {source : VInductDecl}

/-- The main family name owning the restored recursor inventory. -/
def mainName (_nested : NestedBlockChecked source) : Name :=
  match source.types with
  | ty :: _ => ty.name
  | [] => .anonymous

/-- Auxiliary recursor renaming: the `i`-th auxiliary family's recursor
becomes `mainName.rec_(i+1)`, matching `mkAuxRecNameMap`. -/
def recMap (nested : NestedBlockChecked source) : List (Name × Name) :=
  nested.elim.specs.mapIdx fun i spec =>
    (.str spec.aux "rec", ((.str nested.mainName "rec" : Name)).appendIndexAfter (i + 1))

/-- σ entries in declaration level-world (constructor-type restorations). -/
def declEntries (nested : NestedBlockChecked source) : List RestoreEntry :=
  nested.elim.specs.map fun spec =>
    ⟨spec.aux, source.nparams, spec.value⟩

/-- σ entries spliced into recursor level-world by the elimination
offset. -/
def recEntries (nested : NestedBlockChecked source) : List RestoreEntry :=
  nested.elim.specs.map fun spec =>
    ⟨spec.aux, source.nparams,
      spec.value.instL (VLevel.params' source.uvars
        (nested.generation.recUvars - source.uvars))⟩

/-- σ on a recursor-world artifact. -/
def restoreRec (nested : NestedBlockChecked source) (e : VExpr) : VExpr :=
  restoreExpr nested.recEntries nested.recMap e

/-- The restored recursor inventory: the flattened block's recursors with
auxiliary names renamed and every type restored.  Source-family recursors
keep their `.str name "rec"` names. -/
def recursors (nested : NestedBlockChecked source) : List VConstVal :=
  nested.generation.recursors.map fun r =>
    ⟨⟨r.uvars, nested.restoreRec r.type⟩,
      ((nested.recMap.find? (·.1 == r.name)).map (·.2)).getD r.name⟩

/-- Restore all three expression payloads of one flattened generated rule. -/
def restoreRule (nested : NestedBlockChecked source) (rule : VDefEq) : VDefEq :=
  { rule with
      lhs := nested.restoreRec rule.lhs
      rhs := nested.restoreRec rule.rhs
      type := nested.restoreRec rule.type }

/-- The exact restored rule at one flattened constructor position. -/
def restoredRule (nested : NestedBlockChecked source) (i : Nat)
    (constructor : NormalizedBlockCtor) : VDefEq :=
  nested.restoreRule (nested.generation.rule i constructor)

/-- The restored rule inventory, in the flattened block's globally ordered
rule order. -/
def generatedRules (nested : NestedBlockChecked source) : List VDefEq :=
  nested.generation.generatedRules.map nested.restoreRule

end NestedBlockChecked

end VInductDecl

/-- The nested transaction: the four-phase shape of
`addInductBlockGeneration` with the *source* families and constructors as
the stored payload and the *restored* recursors and rules as the generated
artifacts.  No auxiliary constant enters the environment. -/
def VEnv.addInductNested {source : VInductDecl} (env : VEnv)
    (nested : source.NestedBlockChecked) : Option VEnv := do
  let env ← source.blockTypeConstants.foldlM
    (fun env type => env.addConst type.name type.toVConstant) env
  let env ← source.blockConstructorConstants.foldlM
    (fun env constructor => env.addConst constructor.name constructor.toVConstant) env
  let env ← nested.recursors.foldlM
    (fun env recursor => env.addConst recursor.name recursor.toVConstant) env
  return nested.generatedRules.foldl VEnv.addDefEq env

namespace VInductDecl

/-- Chained constant well-formedness along an `addConst` fold: each
constant is well formed in the environment already holding every earlier
one. -/
def NestedConstsWF (env : VEnv) : List VConstVal → Prop
  | [] => True
  | c :: cs => c.toVConstant.WF env ∧
      ∀ env', env.addConst c.name c.toVConstant = some env' →
        NestedConstsWF env' cs

/-- Chained rule well-formedness along an `addDefEq` fold. -/
def NestedRulesWF (env : VEnv) : List VDefEq → Prop
  | [] => True
  | df :: dfs => df.WF env ∧ NestedRulesWF (env.addDefEq df) dfs

/-- Semantic input to nested preservation: the four transaction phases are
well formed at their exact insertion environments.  The phase environments
are determined by the deterministic constant folds, so each later field
takes the earlier folds as hypotheses; a fixture discharges them by
computation.  Inhabiting this package from the flattened block's staged
semantic certificate is the σ-transport route recorded by the L4L-09A
design note; fixtures may equally inhabit it from direct checker
executions on the restored artifacts. -/
structure NestedBlockChecked.WF {source : VInductDecl}
    (nested : NestedBlockChecked source) (env : VEnv) : Prop where
  types : NestedConstsWF env source.blockTypeConstants
  ctors : ∀ {typeEnv},
    source.blockTypeConstants.foldlM
      (fun env type => env.addConst type.name type.toVConstant) env =
        some typeEnv →
    NestedConstsWF typeEnv source.blockConstructorConstants
  recs : ∀ {typeEnv ctorEnv},
    source.blockTypeConstants.foldlM
      (fun env type => env.addConst type.name type.toVConstant) env =
        some typeEnv →
    source.blockConstructorConstants.foldlM
      (fun env constructor => env.addConst constructor.name constructor.toVConstant)
      typeEnv = some ctorEnv →
    NestedConstsWF ctorEnv nested.recursors
  rules : ∀ {typeEnv ctorEnv recEnv},
    source.blockTypeConstants.foldlM
      (fun env type => env.addConst type.name type.toVConstant) env =
        some typeEnv →
    source.blockConstructorConstants.foldlM
      (fun env constructor => env.addConst constructor.name constructor.toVConstant)
      typeEnv = some ctorEnv →
    nested.recursors.foldlM
      (fun env recursor => env.addConst recursor.name recursor.toVConstant)
      ctorEnv = some recEnv →
    NestedRulesWF recEnv nested.generatedRules

end VInductDecl

/-- Exact phase boundaries of a successful nested transaction. -/
structure VEnv.AddInductNestedTrace {source : VInductDecl}
    (env env' : VEnv) (nested : source.NestedBlockChecked) where
  typeEnv : VEnv
  ctorEnv : VEnv
  recEnv : VEnv
  addTypes :
    source.blockTypeConstants.foldlM
      (fun env type => env.addConst type.name type.toVConstant) env =
        some typeEnv
  addCtors :
    source.blockConstructorConstants.foldlM
      (fun env constructor => env.addConst constructor.name constructor.toVConstant)
      typeEnv = some ctorEnv
  addRecs :
    nested.recursors.foldlM
      (fun env recursor => env.addConst recursor.name recursor.toVConstant)
      ctorEnv = some recEnv
  addRules :
    nested.generatedRules.foldl VEnv.addDefEq recEnv = env'

end Lean4Lean
