import Lean4Lean.Theory.Typing.EnvLemmas
import Lean4Lean.Theory.Typing.InductivePattern
import Lean4Lean.Theory.Typing.NestedInductiveLemmas

/-!
# Consumer certificates for completed inductive blocks

`BlockGenerationCertificate` is the semantic input to the block transaction.
This module packages that input with one successful transaction and a
well-formed dependency environment, then exports the stable consequences a
consumer needs.  The package contains only Theory values and proofs: no
implementation metadata, checker state, or normalization execution crosses
this boundary.

In particular, `BlockCertificate.ruleClosure` derives the closed payload
required by the generated-pattern API from the registered, well-formed iota
rules in the completed environment.  A consumer therefore does not need a
second closedness assumption in order to use `IotaPat`.

For nested transport, `NestedStagedCertificate` non-invasively pairs the
restored transaction with its otherwise-erased flattened transaction.  Its
ordinary `BlockCertificate` projection supplies the flattened rule typing,
closure, and `IotaPat` facts needed before σ̂-restoration, while its per-rule
bundle identifies the exact registered restored counterpart.
-/

namespace Lean4Lean

namespace VInductDecl

/-- One successful proof-carrying block transaction over an explicit
dependency environment. -/
structure BlockCertificate (source : VInductDecl) (before after : VEnv) where
  semantic : source.BlockGenerationCertificate before
  success : before.addInductBlockCertified semantic = some after
  beforeWF : before.WF

/-- The generated rule at any exact flattened-constructor position belongs
to the generation's source-ordered rule inventory. -/
theorem BlockGenerationChecked.rule_mem_generatedRules
    {source : VInductDecl} (generation : source.BlockGenerationChecked)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (hentry : generation.flatCtors[i]? = some constructor) :
    generation.rule i constructor ∈ generation.generatedRules := by
  apply List.mem_map.2
  refine ⟨(constructor, i), ?_, rfl⟩
  apply List.mem_of_getElem? (i := i)
  rw [List.getElem?_zipIdx, hentry, Option.map_some, Nat.zero_add]

namespace BlockCertificate

variable {source : VInductDecl} {before after : VEnv}

/-- Package the ordinary raw `addInduct` entry point once its accepted block
descriptor and semantic proof are known.  This is the compatibility bridge
for consumers that still execute `addInduct`; no second transaction is run. -/
def ofAddInduct
    (generation : source.BlockGenerationChecked) (blockEnv : VEnv)
    (hidentity : source.identityBlockGeneration? = some generation)
    (hwf : generation.WF before blockEnv) (hbefore : before.WF)
    (hadd : before.addInduct source = some after) :
    BlockCertificate source before after where
  semantic := ⟨generation, blockEnv, hwf⟩
  success := by
    unfold VEnv.addInduct at hadd
    rw [hidentity] at hadd
    exact hadd
  beforeWF := hbefore

/-- The exact generation descriptor retained by a completed block. -/
abbrev generation (certificate : BlockCertificate source before after) :
    source.BlockGenerationChecked :=
  certificate.semantic.generation

/-- Recover the four exact insertion phases of the completed block. -/
theorem trace (certificate : BlockCertificate source before after) :
    Nonempty (VEnv.AddInductBlockGenerationTrace before after
      certificate.generation) :=
  VEnv.addInductBlockCertified_trace certificate.success

/-- The completed transaction is a genuine block declaration step. -/
theorem declWF (certificate : BlockCertificate source before after) :
    VDecl.WF before (.induct source) after := by
  apply VDecl.WF.inductBlock certificate.semantic.wf
  simpa only [VEnv.addInductBlockCertified_eq_addInductBlockGeneration] using
    certificate.success

/-- Extend the dependency-environment history with the certified block. -/
theorem afterWF (certificate : BlockCertificate source before after) :
    after.WF := by
  rcases certificate.beforeWF with ⟨decls, hdecls⟩
  exact ⟨.induct source :: decls, hdecls.decl certificate.declWF⟩

/-- A completed block only grows its dependency environment. -/
theorem envLE (certificate : BlockCertificate source before after) :
    before ≤ after := by
  rcases certificate.trace with ⟨trace⟩
  exact trace.le

/-- Compatibility spelling for consumers of the historical
`addInduct_le` growth theorem. -/
theorem addInduct_le (certificate : BlockCertificate source before after) :
    before ≤ after :=
  certificate.envLE

/-- Compatibility spelling for the preservation result traditionally
exported as `addInduct_WF`. -/
theorem addInduct_WF (certificate : BlockCertificate source before after) :
    after.WF :=
  certificate.afterWF

/-- Recover success through the ordinary raw API when this certificate's
descriptor is the declaration's identity descriptor. -/
theorem addInduct
    (certificate : BlockCertificate source before after)
    (hidentity : source.identityBlockGeneration? =
      some certificate.generation) :
    before.addInduct source = some after := by
  unfold VEnv.addInduct
  rw [hidentity]
  simpa [VEnv.addInductBlockCertified] using certificate.success

/-- Every source family has its exact stored Theory value in the completed
environment. -/
theorem familyLookup (certificate : BlockCertificate source before after)
    {family : VInductiveType} (hfamily : family ∈ source.types) :
    after.constants family.name = some family.toVConstant := by
  rcases certificate.trace with ⟨trace⟩
  exact trace.family_lookup hfamily

/-- Every flattened source constructor has its exact stored Theory value in
the completed environment. -/
theorem constructorLookup
    (certificate : BlockCertificate source before after)
    {constructor : VConstVal}
    (hconstructor : constructor ∈ source.blockConstructorConstants) :
    after.constants constructor.name = some constructor.toVConstant := by
  rcases certificate.trace with ⟨trace⟩
  exact trace.ctor_lookup hconstructor

/-- Every generated family recursor has its exact Theory value in the
completed environment. -/
theorem recursorLookup
    (certificate : BlockCertificate source before after)
    {recursor : VConstVal}
    (hrecursor : recursor ∈ certificate.generation.recursors) :
    after.constants recursor.name = some recursor.toVConstant := by
  rcases certificate.trace with ⟨trace⟩
  exact trace.rec_lookup hrecursor

/-- The completed environment carries the full generation invariant, not
only its individual lookup consequences.  The transaction trace identifies
the semantic certificate's post-family environment with the trace's family
phase, and every later constructor, recursor, and rule phase is monotone. -/
theorem generationEnv
    (certificate : BlockCertificate source before after) :
    BlockGenerationEnv certificate.generation after := by
  rcases certificate.trace with ⟨trace⟩
  have hstage := certificate.semantic.wf.blockWF.1.1
  rw [← blockTypeConstants_foldlM_eq_stageInductiveTypes before source,
    trace.addTypes] at hstage
  have htypeEnv : trace.typeEnv = certificate.semantic.blockEnv :=
    Option.some.inj hstage
  have hleTC :=
    (ctorFold_spec source.blockConstructorConstants trace.addCtors).1
  have hleCR := (ctorFold_spec certificate.generation.recursors
    trace.addRecs).1
  have hleRA : trace.recEnv ≤ after := by
    simpa only [trace.addRules] using
      (rulesFold_spec certificate.generation.generatedRules trace.recEnv).1
  have hleBlock : certificate.semantic.blockEnv ≤ after := by
    rw [← htypeEnv]
    exact hleTC.trans (hleCR.trans hleRA)
  apply certificate.semantic.wf.toBlockGenerationEnv certificate.envLE
    hleBlock certificate.afterWF.ordered
  · intro family hfamily
    apply certificate.familyLookup
    rw [← certificate.generation.families_map_raw]
    exact List.mem_map.2 ⟨family, hfamily, rfl⟩
  · intro constructor hconstructor
    apply certificate.constructorLookup
    rw [← certificate.generation.flatCtors_map_raw]
    exact List.mem_map.2 ⟨constructor, hconstructor, rfl⟩

/-- A source family name was fresh at the dependency boundary. -/
theorem familyFresh (certificate : BlockCertificate source before after)
    {family : VInductiveType} (hfamily : family ∈ source.types) :
    before.constants family.name = none := by
  rcases certificate.trace with ⟨trace⟩
  exact trace.family_fresh hfamily

/-- A flattened source constructor name was fresh at the dependency
boundary. -/
theorem constructorFresh
    (certificate : BlockCertificate source before after)
    {constructor : VConstVal}
    (hconstructor : constructor ∈ source.blockConstructorConstants) :
    before.constants constructor.name = none := by
  rcases certificate.trace with ⟨trace⟩
  exact trace.ctor_fresh hconstructor

/-- A generated recursor name was fresh at the dependency boundary. -/
theorem recursorFresh
    (certificate : BlockCertificate source before after)
    {recursor : VConstVal}
    (hrecursor : recursor ∈ certificate.generation.recursors) :
    before.constants recursor.name = none := by
  rcases certificate.trace with ⟨trace⟩
  exact trace.rec_fresh hrecursor

/-- Every generated rule is registered by the completed transaction. -/
theorem ruleRegistered
    (certificate : BlockCertificate source before after)
    {rule : VDefEq}
    (hrule : rule ∈ certificate.generation.generatedRules) :
    after.defeqs rule := by
  rcases certificate.trace with ⟨trace⟩
  exact trace.rule_mem hrule

/-- Every generated rule is well formed in the completed environment. -/
theorem ruleWF
    (certificate : BlockCertificate source before after)
    {rule : VDefEq}
    (hrule : rule ∈ certificate.generation.generatedRules) :
    rule.WF after :=
  certificate.afterWF.ordered.defEqWF (certificate.ruleRegistered hrule)

/-- An exact family lookup is unique.  This small eliminator is convenient
for consumers that translate their own family representation to a Theory
constant and then compare it with the certificate inventory. -/
theorem familyLookup_unique
    (certificate : BlockCertificate source before after)
    {family : VInductiveType} (hfamily : family ∈ source.types)
    {constant : VConstant}
    (hlookup : after.constants family.name = some constant) :
    constant = family.toVConstant := by
  exact Option.some.inj (hlookup.symm.trans (certificate.familyLookup hfamily))

/-- An exact constructor lookup is unique. -/
theorem constructorLookup_unique
    (certificate : BlockCertificate source before after)
    {constructor : VConstVal}
    (hconstructor : constructor ∈ source.blockConstructorConstants)
    {constant : VConstant}
    (hlookup : after.constants constructor.name = some constant) :
    constant = constructor.toVConstant := by
  exact Option.some.inj
    (hlookup.symm.trans (certificate.constructorLookup hconstructor))

/-- An exact generated-recursor lookup is unique. -/
theorem recursorLookup_unique
    (certificate : BlockCertificate source before after)
    {recursor : VConstVal}
    (hrecursor : recursor ∈ certificate.generation.recursors)
    {constant : VConstant}
    (hlookup : after.constants recursor.name = some constant) :
    constant = recursor.toVConstant := by
  exact Option.some.inj
    (hlookup.symm.trans (certificate.recursorLookup hrecursor))

private theorem closedN_lamN_body :
    ∀ {binders : List VExpr} {body : VExpr} {k : Nat},
      (VExpr.lamN binders body).ClosedN k →
        body.ClosedN (k + binders.length)
  | [], _, _, h => by
      simpa only [VExpr.lamN, List.length_nil, Nat.add_zero] using h
  | _ :: binders, body, k, h => by
      have hbody := closedN_lamN_body (binders := binders)
        (body := body) (k := k + 1) h.2
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbody

private theorem closedN_lamN_replace :
    ∀ {binders : List VExpr} {body body' : VExpr} {k : Nat},
      (VExpr.lamN binders body).ClosedN k →
      body'.ClosedN (k + binders.length) →
        (VExpr.lamN binders body').ClosedN k
  | [], _, _, _, _, hbody' => by
      simpa only [VExpr.lamN, List.length_nil, Nat.add_zero] using hbody'
  | _ :: binders, body, body', k, h, hbody' => by
      refine ⟨h.1, closedN_lamN_replace (binders := binders)
        (body := body) (body' := body') (k := k + 1) h.2 ?_⟩
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hbody'

private theorem closedN_appN_function :
    ∀ {function : VExpr} {arguments : List VExpr} {k : Nat},
      (VExpr.appN function arguments).ClosedN k → function.ClosedN k
  | _, [], _, h => by simpa only [VExpr.appN] using h
  | function, argument :: arguments, k, h =>
      (closedN_appN_function (function := function.app argument)
        (arguments := arguments) (k := k) h).1

private theorem closedN_appN_argument
    {function : VExpr} {arguments : List VExpr} {k : Nat}
    (hclosed : (VExpr.appN function arguments).ClosedN k)
    {argument : VExpr} (hargument : argument ∈ arguments) :
    argument.ClosedN k := by
  induction arguments generalizing function with
  | nil => simp at hargument
  | cons head tail ih =>
    rcases List.mem_cons.1 hargument with heq | htail
    · rw [heq]
      exact (closedN_appN_function
        (function := function.app head) (arguments := tail)
        (k := k) hclosed).2
    · exact ih (function := function.app head) hclosed htail

/-- The successful block transaction supplies the closedness bundle required
by `IotaPat`.  Closedness is derived from the registered rules and the
completed environment's ordinary WF history; it is not an additional
consumer assumption. -/
theorem ruleClosure
    (certificate : BlockCertificate source before after) :
    certificate.generation.RuleClosure := by
  constructor
  · intro i constructor hentry
    have hmem := certificate.generation.rule_mem_generatedRules hentry
    exact (certificate.ruleWF hmem).2.closedN
      certificate.afterWF.ordered trivial
  · intro constructor hconstructor expression hexpression
    obtain ⟨i, hentry⟩ := List.mem_iff_getElem?.1 hconstructor
    have hmem := certificate.generation.rule_mem_generatedRules hentry
    have hlhs := (certificate.ruleWF hmem).1.closedN
      certificate.afterWF.ordered trivial
    rw [certificate.generation.rule_lhs i constructor] at hlhs
    have hbody := closedN_lamN_body hlhs
    have hexpression' : expression ∈
        certificate.generation.ruleIdx constructor ++
          [certificate.generation.ruleCtorApp constructor] :=
      List.mem_append.2 (.inl hexpression)
    have hclosed : expression.ClosedN
        (certificate.generation.ruleBinders constructor).length := by
      apply closedN_appN_argument
        (function := certificate.generation.recBase
          (certificate.generation.ruleFieldCount constructor)
          constructor.owner)
        (arguments := certificate.generation.ruleIdx constructor ++
          [certificate.generation.ruleCtorApp constructor])
      · simpa only [BlockGenerationChecked.ruleLhsBody, List.length_nil,
          Nat.zero_add] using hbody
      · exact hexpression'
    apply closedN_lamN_replace hlhs
    simpa using hclosed

/-- The exact generated pattern and payload associated with one flattened
rule entry. -/
theorem recursorPattern
    (certificate : BlockCertificate source before after)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (hentry : certificate.generation.ruleEntry i constructor) :
    certificate.generation.IotaPat certificate.ruleClosure
      ((certificate.generation.rulePattern constructor).toPattern)
      (certificate.generation.ruleRHS certificate.ruleClosure hentry,
        certificate.generation.ruleCheck certificate.ruleClosure
          (List.mem_of_getElem? hentry)) :=
  .mk hentry

/-- Rule-level consumer bundle: exact global position, generated-list
membership, registration, well-formedness, and the corresponding L4L-10
pattern all come from the same completed block. -/
structure RecursorRuleFacts
    (certificate : BlockCertificate source before after)
    (i : Nat) (constructor : NormalizedBlockCtor) : Prop where
  entry : certificate.generation.ruleEntry i constructor
  member : certificate.generation.rule i constructor ∈
    certificate.generation.generatedRules
  registered : after.defeqs (certificate.generation.rule i constructor)
  wf : (certificate.generation.rule i constructor).WF after
  pattern : certificate.generation.IotaPat certificate.ruleClosure
    ((certificate.generation.rulePattern constructor).toPattern)
    (certificate.generation.ruleRHS certificate.ruleClosure entry,
      certificate.generation.ruleCheck certificate.ruleClosure
        (List.mem_of_getElem? entry))

/-- Assemble all rule facts without a consumer-supplied semantic premise. -/
theorem recursorRuleFacts
    (certificate : BlockCertificate source before after)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (hentry : certificate.generation.ruleEntry i constructor) :
    certificate.RecursorRuleFacts i constructor := by
  have hmember := certificate.generation.rule_mem_generatedRules hentry
  exact {
    entry := hentry
    member := hmember
    registered := certificate.ruleRegistered hmember
    wf := certificate.ruleWF hmember
    pattern := certificate.recursorPattern hentry }

end BlockCertificate

/-! ## Completed nested transactions -/

/-- The complete syntactic Pi telescope of a well-formed type is itself a
well-formed telescope.  This deliberately stops at the first non-`forall`
cursor, matching `ctorFields`. -/
theorem VEnv.IsType.ctorFields_onTel {env : VEnv} {U : Nat}
    {context : List VExpr} {expression : VExpr}
    (henv : env.Ordered) (self : env.IsType U context expression) :
    env.OnTel U context (ctorFields expression) := by
  induction expression generalizing context with
  | forallE domain body _ bodyIH =>
      have parts := self.forallE_inv henv
      exact ⟨parts.1, bodyIH parts.2⟩
  | bvar | sort | const | app | lam => trivial

/-- One successful proof-carrying nested transaction over an explicit
dependency environment.  As with `BlockCertificate`, this package contains
only Theory artifacts. -/
structure NestedBlockCertificate
    (source : VInductDecl) (before after : VEnv) where
  nested : source.NestedBlockChecked
  semantic : nested.WF before
  success : before.addInductNested nested = some after
  beforeWF : before.WF

/-- The exact normalized flattened family/constructor selected by a
one-constructor, unindexed family of the restored nested source.  Besides
positional provenance, the package records the parameter and field boundaries
transported back to the source constructor from restoration-stable total Pi
arity.  No second normalization run or caller-owned flattened descriptor is
accepted. -/
structure NestedStructureSelection {source : VInductDecl}
    (nested : source.NestedBlockChecked) (familyIndex : Nat)
    (sourceFamily : VInductiveType) (sourceConstructor : VConstVal) where
  source_at : source.types[familyIndex]? = some sourceFamily
  source_constructors_eq : sourceFamily.ctors = [sourceConstructor]
  source_raw_indices_eq :
    ctorFields (VExpr.dropN source.nparams sourceFamily.type) = []
  flatFamily : VInductiveType
  flatConstructor : VConstVal
  flat_at : nested.elim.flat.types[familyIndex]? = some flatFamily
  flat_constructors_eq : flatFamily.ctors = [flatConstructor]
  family_header_eq : VInductiveType.nestedHeader flatFamily =
    VInductiveType.nestedHeader sourceFamily
  constructor_header_eq :
    VConstVal.nestedHeader flatConstructor =
      VConstVal.nestedHeader sourceConstructor
  family : NormalizedFamily
  family_at : nested.generation.families[familyIndex]? = some family
  family_raw_eq : family.raw = flatFamily
  constructor : NormalizedCtor
  constructors_eq : family.ctorPairs = [constructor]
  constructor_raw_eq : constructor.raw = flatConstructor
  flat_raw_indices_eq :
    family.rawIndices nested.elim.flat.nparams = []
  checked_indices_eq : family.view.indices = []
  source_constructor_params_length :
    (VExpr.telN source.nparams sourceConstructor.type).length = source.nparams
  source_flat_fields_length_eq :
    (ctorFields (VExpr.dropN source.nparams sourceConstructor.type)).length =
      (constructor.rawFields nested.elim.flat.nparams).length

/-- The source constructor selected through nested restoration has the same
declaration universe arity as the checked flattened block. -/
theorem NestedStructureSelection.source_constructor_uvars_eq
    {source : VInductDecl} {nested : source.NestedBlockChecked}
    {familyIndex : Nat} {sourceFamily : VInductiveType}
    {sourceConstructor : VConstVal}
    (selection : NestedStructureSelection nested familyIndex sourceFamily
      sourceConstructor) :
    sourceConstructor.uvars = source.uvars := by
  have headerUvars := congrArg NestedCtorHeader.uvars
    selection.constructor_header_eq
  have flatUvars : selection.flatConstructor.uvars = nested.elim.flat.uvars := by
    rw [← selection.constructor_raw_eq]
    exact nested.generation.ctor_uvars
      (List.mem_iff_getElem?.2 ⟨familyIndex, selection.family_at⟩)
      (by rw [selection.constructors_eq]; simp)
  have declarationUvars : nested.elim.flat.uvars = source.uvars := by
    simpa using congrArg VInductDecl.uvars nested.elim.flat_eq
  calc
    sourceConstructor.uvars = selection.flatConstructor.uvars := by
      simpa [VConstVal.nestedHeader] using headerUvars.symm
    _ = nested.elim.flat.uvars := flatUvars
    _ = source.uvars := declarationUvars

/-- The selected flattened constructor retains the restored source
constructor's literal shared-parameter prefix.  Nested elimination rewrites
only the suffix after this boundary. -/
theorem NestedStructureSelection.flat_constructor_params_eq
    {source : VInductDecl} {nested : source.NestedBlockChecked}
    {familyIndex : Nat} {sourceFamily : VInductiveType}
    {sourceConstructor : VConstVal}
    (selection : NestedStructureSelection nested familyIndex sourceFamily
      sourceConstructor) :
    VExpr.telN source.nparams selection.flatConstructor.type =
      VExpr.telN source.nparams sourceConstructor.type := by
  apply nested.elim.flat_constructor_params_eq (constructorIndex := 0)
    selection.source_at selection.flat_at
  · rw [selection.source_constructors_eq]
    rfl
  · rw [selection.flat_constructors_eq]
    rfl

/-- Select the normalized flattened producer at an exact restored source
position.  Successful nested elimination preserves family/constructor
headers, and the flattened generation shape supplies every remaining layout
fact. -/
theorem NestedBlockChecked.selectStructure
    {source : VInductDecl} (nested : source.NestedBlockChecked)
    {familyIndex : Nat} {sourceFamily : VInductiveType}
    {sourceConstructor : VConstVal}
    (source_at : source.types[familyIndex]? = some sourceFamily)
    (source_constructors_eq : sourceFamily.ctors = [sourceConstructor])
    (source_raw_indices_eq :
      ctorFields (VExpr.dropN source.nparams sourceFamily.type) = []) :
    Nonempty (NestedStructureSelection nested familyIndex sourceFamily
      sourceConstructor) := by
  have sourceConstructorAt : sourceFamily.ctors[0]? =
      some sourceConstructor := by
    simp [source_constructors_eq]
  obtain ⟨flatFamily, flatAt, familyHeader⟩ :=
    nested.elim.flat_family_header_at source_at
  obtain ⟨flatFamily', flatConstructor, flatAt', flatConstructorAt,
      constructorHeader⟩ :=
    nested.elim.flat_constructor_header_at source_at sourceConstructorAt
  have flatFamilyEq : flatFamily' = flatFamily :=
    Option.some.inj (flatAt'.symm.trans flatAt)
  subst flatFamily'
  have flatConstructorsLength : flatFamily.ctors.length = 1 := by
    have headersEq := congrArg NestedFamilyHeader.constructors familyHeader
    have lengthsEq := congrArg List.length headersEq
    simpa [VInductiveType.nestedHeader, source_constructors_eq] using lengthsEq
  obtain ⟨onlyFlatConstructor, flatConstructorsEq⟩ :=
    List.length_eq_one_iff.mp flatConstructorsLength
  have flatConstructorEq : flatConstructor = onlyFlatConstructor := by
    rw [flatConstructorsEq] at flatConstructorAt
    have selectedEq : onlyFlatConstructor = flatConstructor := by
      simpa only [List.getElem?_cons_zero, Option.some.injEq] using
        flatConstructorAt
    exact selectedEq.symm
  subst onlyFlatConstructor
  obtain ⟨family, familyAt, familyRawEq⟩ :=
    nested.generation.exists_family_getElem?_of_raw flatAt
  have familyMember : family ∈ nested.generation.families :=
    List.mem_iff_getElem?.2 ⟨familyIndex, familyAt⟩
  have familyRawConstructorAt : family.raw.ctors[0]? =
      some flatConstructor := by
    rw [familyRawEq, flatConstructorsEq]
    rfl
  obtain ⟨constructor, constructorAt, constructorRawEq⟩ :=
    family.exists_ctor_getElem?_of_raw familyMember familyRawConstructorAt
  have constructorPairsLength : family.ctorPairs.length = 1 := by
    calc
      family.ctorPairs.length = family.raw.ctors.length :=
        (nested.generation.shape.2.2.2.2 family familyMember).2.2.2.2.1
      _ = flatFamily.ctors.length :=
        congrArg (fun raw => raw.ctors.length) familyRawEq
      _ = 1 := flatConstructorsLength
  obtain ⟨onlyConstructor, constructorsEq⟩ :=
    List.length_eq_one_iff.mp constructorPairsLength
  have constructorEq : constructor = onlyConstructor := by
    rw [constructorsEq] at constructorAt
    have selectedEq : onlyConstructor = constructor := by
      simpa only [List.getElem?_cons_zero, Option.some.injEq] using
        constructorAt
    exact selectedEq.symm
  subst onlyConstructor
  have familyTypeEq : family.raw.type = sourceFamily.type := by
    calc
      family.raw.type = flatFamily.type :=
        congrArg (fun raw : VInductiveType => raw.type) familyRawEq
      _ = sourceFamily.type := by
        simpa [VInductiveType.nestedHeader] using
          congrArg NestedFamilyHeader.type familyHeader
  have flatRawIndicesEq :
      family.rawIndices nested.elim.flat.nparams = [] := by
    unfold NormalizedFamily.rawIndices
    rw [nested.elim.nparams_eq, familyTypeEq]
    exact source_raw_indices_eq
  have checkedIndicesLength : family.view.indices.length = 0 := by
    rw [← (nested.generation.shape.2.2.2.2 family
      familyMember).2.2.2.1]
    simp [flatRawIndicesEq]
  have checkedIndicesEq : family.view.indices = [] :=
    List.length_eq_zero_iff.mp checkedIndicesLength
  have constructorMember : constructor ∈ family.ctorPairs := by
    rw [constructorsEq]
    simp
  have flatParamLength :
      (VExpr.telN source.nparams constructor.raw.type).length =
        source.nparams := by
    have checked :=
      ((nested.generation.shape.2.2.2.2 family familyMember).2.2.2.2.2.2
        constructor constructorMember).2.2.1
    simpa only [nested.elim.nparams_eq] using checked
  have constructorArityEq :
      VExpr.nestedArity constructor.raw.type =
        VExpr.nestedArity sourceConstructor.type := by
    calc
      VExpr.nestedArity constructor.raw.type =
          VExpr.nestedArity flatConstructor.type := by rw [constructorRawEq]
      _ = VExpr.nestedArity sourceConstructor.type := by
        simpa [VConstVal.nestedHeader] using
          congrArg NestedCtorHeader.arity constructorHeader
  have sourceParamLength :
      (VExpr.telN source.nparams sourceConstructor.type).length =
        source.nparams :=
    VExpr.telN_length_eq_of_nestedArity_eq constructorArityEq.symm
      flatParamLength
  have sourceSplit := VExpr.telN_length_add_dropN_nestedArity
    source.nparams sourceConstructor.type
  have flatSplit := VExpr.telN_length_add_dropN_nestedArity
    source.nparams constructor.raw.type
  rw [sourceParamLength] at sourceSplit
  rw [flatParamLength] at flatSplit
  have fieldsLengthEq :
      (ctorFields (VExpr.dropN source.nparams
        sourceConstructor.type)).length =
      (constructor.rawFields nested.elim.flat.nparams).length := by
    unfold NormalizedCtor.rawFields
    rw [nested.elim.nparams_eq]
    rw [← VExpr.nestedArity_eq_ctorFields_length,
      ← VExpr.nestedArity_eq_ctorFields_length]
    omega
  exact ⟨{
    source_at
    source_constructors_eq
    source_raw_indices_eq
    flatFamily
    flatConstructor
    flat_at := flatAt
    flat_constructors_eq := flatConstructorsEq
    family_header_eq := familyHeader
    constructor_header_eq := constructorHeader
    family
    family_at := familyAt
    family_raw_eq := familyRawEq
    constructor
    constructors_eq := constructorsEq
    constructor_raw_eq := constructorRawEq
    flat_raw_indices_eq := flatRawIndicesEq
    checked_indices_eq := checkedIndicesEq
    source_constructor_params_length := sourceParamLength
    source_flat_fields_length_eq := fieldsLengthEq }⟩

/-- The exact restoration of a flattened rule entry belongs to the nested
transaction's restored rule inventory. -/
theorem NestedBlockChecked.restoredRule_mem
    {source : VInductDecl} (nested : source.NestedBlockChecked)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (hentry : nested.generation.ruleEntry i constructor) :
    nested.restoredRule i constructor ∈ nested.generatedRules := by
  apply List.mem_map.2
  exact ⟨nested.generation.rule i constructor,
    nested.generation.rule_mem_generatedRules hentry, rfl⟩

namespace NestedBlockCertificate

variable {source : VInductDecl} {before after : VEnv}

/-- Recover the exact four-phase nested transaction trace. -/
theorem trace (certificate : NestedBlockCertificate source before after) :
    Nonempty (VEnv.AddInductNestedTrace before after certificate.nested) :=
  VEnv.addInductNested_trace certificate.success

/-- The nested completion is a genuine inductive declaration step. -/
theorem declWF (certificate : NestedBlockCertificate source before after) :
    VDecl.WF before (.induct source) after :=
  .inductNested certificate.semantic certificate.success

/-- Extend the dependency-environment history with the nested block. -/
theorem afterWF (certificate : NestedBlockCertificate source before after) :
    after.WF := by
  rcases certificate.beforeWF with ⟨decls, hdecls⟩
  exact ⟨.induct source :: decls, hdecls.decl certificate.declWF⟩

/-- A completed nested transaction only grows its dependency environment. -/
theorem envLE (certificate : NestedBlockCertificate source before after) :
    before ≤ after :=
  VEnv.addInductNested_le certificate.success

/-- Nested analogue of the public block growth result. -/
theorem addInduct_le
    (certificate : NestedBlockCertificate source before after) :
    before ≤ after :=
  certificate.envLE

/-- Nested analogue of the public block preservation result. -/
theorem addInduct_WF
    (certificate : NestedBlockCertificate source before after) :
    after.WF :=
  certificate.afterWF

/-- Every stored source family has its exact final value. -/
theorem familyLookup (certificate : NestedBlockCertificate source before after)
    {family : VInductiveType} (hfamily : family ∈ source.types) :
    after.constants family.name = some family.toVConstant := by
  rcases certificate.trace with ⟨trace⟩
  exact trace.family_lookup hfamily

/-- Every stored source constructor has its exact final value. -/
theorem constructorLookup
    (certificate : NestedBlockCertificate source before after)
    {family : VInductiveType} (hfamily : family ∈ source.types)
    {constructor : VConstVal} (hconstructor : constructor ∈ family.ctors) :
    after.constants constructor.name = some constructor.toVConstant := by
  rcases certificate.trace with ⟨trace⟩
  exact trace.ctor_lookup hfamily hconstructor

/-- Registration in the completed nested environment exposes the complete
dependent Pi telescope of every exact source constructor. -/
theorem constructorTelescope
    (certificate : NestedBlockCertificate source before after)
    {family : VInductiveType} (hfamily : family ∈ source.types)
    {constructor : VConstVal} (hconstructor : constructor ∈ family.ctors) :
    after.OnTel constructor.uvars [] (ctorFields constructor.type) := by
  have htype := certificate.afterWF.ordered.constWF
    (certificate.constructorLookup hfamily hconstructor)
  change after.IsType constructor.uvars [] constructor.type at htype
  exact VEnv.IsType.ctorFields_onTel certificate.afterWF.ordered htype

/-- The selected restored source constructor telescope is checked in the
source declaration's universe context, not merely at its independently
stored constant arity. -/
theorem selectedSourceConstructorTelescope
    (certificate : NestedBlockCertificate source before after)
    {familyIndex : Nat} {sourceFamily : VInductiveType}
    {sourceConstructor : VConstVal}
    (selection : NestedStructureSelection certificate.nested familyIndex
      sourceFamily sourceConstructor) :
    after.OnTel source.uvars [] (ctorFields sourceConstructor.type) := by
  have familyMember : sourceFamily ∈ source.types :=
    List.mem_iff_getElem?.2 ⟨familyIndex, selection.source_at⟩
  have constructorMember : sourceConstructor ∈ sourceFamily.ctors := by
    rw [selection.source_constructors_eq]
    simp
  have telescope := certificate.constructorTelescope familyMember
    constructorMember
  rw [selection.source_constructor_uvars_eq] at telescope
  exact telescope

/-- After the exact source parameter prefix, the restored constructor field
suffix remains a well-formed telescope in the corresponding parameter
context. -/
theorem selectedSourceConstructorFieldsTelescope
    (certificate : NestedBlockCertificate source before after)
    {familyIndex : Nat} {sourceFamily : VInductiveType}
    {sourceConstructor : VConstVal}
    (selection : NestedStructureSelection certificate.nested familyIndex
      sourceFamily sourceConstructor) :
    after.OnTel source.uvars
      (VExpr.telN source.nparams sourceConstructor.type).reverse
      (ctorFields (VExpr.dropN source.nparams sourceConstructor.type)) := by
  have telescope := certificate.selectedSourceConstructorTelescope selection
  rw [VExpr.ctorFields_eq_telN_append source.nparams
    sourceConstructor.type] at telescope
  simpa using (VEnv.OnTel.of_append telescope).2

/-- Every restored recursor has its exact final value. -/
theorem recursorLookup
    (certificate : NestedBlockCertificate source before after)
    {recursor : VConstVal} (hrecursor : recursor ∈ certificate.nested.recursors) :
    after.constants recursor.name = some recursor.toVConstant := by
  rcases certificate.trace with ⟨trace⟩
  exact trace.rec_lookup hrecursor

/-- Every source family name was fresh at the dependency boundary. -/
theorem familyFresh (certificate : NestedBlockCertificate source before after)
    {family : VInductiveType} (hfamily : family ∈ source.types) :
    before.constants family.name = none := by
  rcases certificate.trace with ⟨trace⟩
  exact trace.family_fresh hfamily

/-- Every flattened source constructor name was fresh at the dependency
boundary. -/
theorem constructorFresh
    (certificate : NestedBlockCertificate source before after)
    {constructor : VConstVal}
    (hconstructor : constructor ∈ source.blockConstructorConstants) :
    before.constants constructor.name = none := by
  rcases certificate.trace with ⟨trace⟩
  exact trace.ctor_fresh hconstructor

/-- Every restored recursor name was fresh at the dependency boundary. -/
theorem recursorFresh
    (certificate : NestedBlockCertificate source before after)
    {recursor : VConstVal} (hrecursor : recursor ∈ certificate.nested.recursors) :
    before.constants recursor.name = none := by
  rcases certificate.trace with ⟨trace⟩
  exact trace.rec_fresh hrecursor

/-- Every restored rule is registered in the completed environment. -/
theorem ruleRegistered
    (certificate : NestedBlockCertificate source before after)
    {rule : VDefEq} (hrule : rule ∈ certificate.nested.generatedRules) :
    after.defeqs rule := by
  rcases certificate.trace with ⟨trace⟩
  exact trace.rule_mem hrule

/-- Every registered restored rule is well formed. -/
theorem ruleWF
    (certificate : NestedBlockCertificate source before after)
    {rule : VDefEq} (hrule : rule ∈ certificate.nested.generatedRules) :
    rule.WF after :=
  certificate.afterWF.ordered.defEqWF (certificate.ruleRegistered hrule)

/-- The restored rule at an exact flattened position is registered by the
completed nested transaction. -/
theorem restoredRuleRegistered
    (certificate : NestedBlockCertificate source before after)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (hentry : certificate.nested.generation.ruleEntry i constructor) :
    after.defeqs (certificate.nested.restoredRule i constructor) :=
  certificate.ruleRegistered
    (certificate.nested.restoredRule_mem hentry)

/-- The restored rule at an exact flattened position is well formed in the
completed nested environment. -/
theorem restoredRuleWF
    (certificate : NestedBlockCertificate source before after)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (hentry : certificate.nested.generation.ruleEntry i constructor) :
    (certificate.nested.restoredRule i constructor).WF after :=
  certificate.ruleWF (certificate.nested.restoredRule_mem hentry)

/-- Exact family lookups are unique. -/
theorem familyLookup_unique
    (certificate : NestedBlockCertificate source before after)
    {family : VInductiveType} (hfamily : family ∈ source.types)
    {constant : VConstant}
    (hlookup : after.constants family.name = some constant) :
    constant = family.toVConstant :=
  Option.some.inj (hlookup.symm.trans (certificate.familyLookup hfamily))

/-- Exact constructor lookups are unique. -/
theorem constructorLookup_unique
    (certificate : NestedBlockCertificate source before after)
    {family : VInductiveType} (hfamily : family ∈ source.types)
    {constructor : VConstVal} (hconstructor : constructor ∈ family.ctors)
    {constant : VConstant}
    (hlookup : after.constants constructor.name = some constant) :
    constant = constructor.toVConstant :=
  Option.some.inj
    (hlookup.symm.trans (certificate.constructorLookup hfamily hconstructor))

/-- Exact restored-recursor lookups are unique. -/
theorem recursorLookup_unique
    (certificate : NestedBlockCertificate source before after)
    {recursor : VConstVal} (hrecursor : recursor ∈ certificate.nested.recursors)
    {constant : VConstant}
    (hlookup : after.constants recursor.name = some constant) :
    constant = recursor.toVConstant :=
  Option.some.inj
    (hlookup.symm.trans (certificate.recursorLookup hrecursor))

end NestedBlockCertificate

/-! ## Paired flattened/restored nested staging -/

/-- A completed nested transaction together with the exact flattened
generation transaction from which restoration transport proceeds.  This is
separate from `NestedBlockCertificate`: consumers of an already-restored
transaction retain the smaller package, while transport proofs explicitly
retain the otherwise-erased flattened staging environment. -/
structure NestedStagedCertificate
    (source : VInductDecl) (before flatAfter after : VEnv) where
  restored : source.NestedBlockCertificate before after
  flatBlockEnv : VEnv
  flatWF : restored.nested.generation.WF before flatBlockEnv
  flatSuccess : before.addInductBlockGeneration
    restored.nested.generation = some flatAfter

namespace NestedStagedCertificate

variable {source : VInductDecl} {before flatAfter after : VEnv}

/-- Erase the restored half and expose the ordinary certificate for the
exact flattened generation descriptor. -/
def flatCertificate
    (certificate : NestedStagedCertificate source before flatAfter after) :
    certificate.restored.nested.elim.flat.BlockCertificate before
      flatAfter where
  semantic := {
    generation := certificate.restored.nested.generation
    blockEnv := certificate.flatBlockEnv
    wf := certificate.flatWF }
  success := certificate.flatSuccess
  beforeWF := certificate.restored.beforeWF

/-- The flattened staging transaction preserves environment
well-formedness. -/
theorem flatAfterWF
    (certificate : NestedStagedCertificate source before flatAfter after) :
    flatAfter.WF :=
  certificate.flatCertificate.afterWF

/-- The flattened staging transaction supplies the exact closedness bundle
for its generated iota patterns. -/
theorem flatRuleClosure
    (certificate : NestedStagedCertificate source before flatAfter after) :
    certificate.restored.nested.generation.RuleClosure :=
  certificate.flatCertificate.ruleClosure

/-- Recover the exact generated iota pattern at a flattened constructor
position from the retained staging transaction. -/
theorem flatRecursorPattern
    (certificate : NestedStagedCertificate source before flatAfter after)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (hentry : certificate.restored.nested.generation.ruleEntry i constructor) :
    certificate.restored.nested.generation.IotaPat
      certificate.flatRuleClosure
      ((certificate.restored.nested.generation.rulePattern
        constructor).toPattern)
      (certificate.restored.nested.generation.ruleRHS
          certificate.flatRuleClosure hentry,
        certificate.restored.nested.generation.ruleCheck
          certificate.flatRuleClosure (List.mem_of_getElem? hentry)) :=
  certificate.flatCertificate.recursorPattern hentry

/-- Recover registration, well-formedness, and the generated pattern from
one exact flattened rule position. -/
theorem flatRecursorRuleFacts
    (certificate : NestedStagedCertificate source before flatAfter after)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (hentry : certificate.restored.nested.generation.ruleEntry i constructor) :
    certificate.flatCertificate.RecursorRuleFacts i constructor :=
  certificate.flatCertificate.recursorRuleFacts hentry

/-- Per-rule nested transport bundle: one flattened position determines its
ordinary registered rule and generated pattern as well as the exact restored
rule registered and well formed in the final nested environment. -/
structure RecursorRuleFacts
    (certificate : NestedStagedCertificate source before flatAfter after)
    (i : Nat) (constructor : NormalizedBlockCtor) : Prop where
  flat : certificate.flatCertificate.RecursorRuleFacts i constructor
  restoredMember : certificate.restored.nested.restoredRule i constructor ∈
    certificate.restored.nested.generatedRules
  restoredRegistered : after.defeqs
    (certificate.restored.nested.restoredRule i constructor)
  restoredWF :
    (certificate.restored.nested.restoredRule i constructor).WF after

/-- Assemble both sides of one nested rule from the same exact flattened
constructor position. -/
theorem recursorRuleFacts
    (certificate : NestedStagedCertificate source before flatAfter after)
    {i : Nat} {constructor : NormalizedBlockCtor}
    (hentry : certificate.restored.nested.generation.ruleEntry i constructor) :
    certificate.RecursorRuleFacts i constructor := {
  flat := certificate.flatRecursorRuleFacts hentry
  restoredMember := certificate.restored.nested.restoredRule_mem hentry
  restoredRegistered := certificate.restored.restoredRuleRegistered hentry
  restoredWF := certificate.restored.restoredRuleWF hentry }

end NestedStagedCertificate

end VInductDecl

end Lean4Lean

/-! ## Exact Theory trust guards -/

/-- info: 'Lean4Lean.VInductDecl.BlockCertificate.afterWF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockCertificate.afterWF

/-- info: 'Lean4Lean.VInductDecl.BlockCertificate.generationEnv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockCertificate.generationEnv

/-- info: 'Lean4Lean.VInductDecl.BlockCertificate.ruleClosure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockCertificate.ruleClosure

/-- info: 'Lean4Lean.VInductDecl.BlockCertificate.recursorRuleFacts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.BlockCertificate.recursorRuleFacts

/-- info: 'Lean4Lean.VInductDecl.NestedBlockCertificate.afterWF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.NestedBlockCertificate.afterWF

/-- info: 'Lean4Lean.VInductDecl.NestedBlockCertificate.ruleWF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.NestedBlockCertificate.ruleWF

/-- info: 'Lean4Lean.VInductDecl.NestedBlockChecked.restoredRule_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.NestedBlockChecked.restoredRule_mem

/-- info: 'Lean4Lean.VInductDecl.NestedBlockCertificate.restoredRuleWF' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.NestedBlockCertificate.restoredRuleWF

/-- info: 'Lean4Lean.VInductDecl.NestedStagedCertificate.flatAfterWF' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.NestedStagedCertificate.flatAfterWF

/--
info: 'Lean4Lean.VInductDecl.NestedStagedCertificate.flatRuleClosure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.NestedStagedCertificate.flatRuleClosure

/--
info: 'Lean4Lean.VInductDecl.NestedStagedCertificate.flatRecursorPattern' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.NestedStagedCertificate.flatRecursorPattern

/--
info: 'Lean4Lean.VInductDecl.NestedStagedCertificate.flatRecursorRuleFacts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.NestedStagedCertificate.flatRecursorRuleFacts

/--
info: 'Lean4Lean.VInductDecl.NestedStagedCertificate.recursorRuleFacts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in
#print axioms Lean4Lean.VInductDecl.NestedStagedCertificate.recursorRuleFacts
