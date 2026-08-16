# L4L-15B registered structure-eta design

Date: 2026-08-11

Status: approved fork divergence; implementation target is the reconciled
v4.33 base at merge checkpoint `99a7f8ae7b89`. Upstream review is deferred to
the L4L-20C PR series. This note is the mandatory pre-implementation design
record for ledger entry D019.

## Scope and kernel behavior

Lean gives eta conversion to nonrecursive, single-constructor inductives with
no indices. For a checked structure family `S`, constructor `C`, parameters
`ps`, canonical generated projectors `proj_i`, and a well-typed major `e`, the
new Theory step is the contraction

```text
C ps (proj_0 e) ... (proj_n e)  ≡  e : S ps.
```

The zero-field case is the same rule with an empty projector list. Prop-valued
structures remain convertible by proof irrelevance as well; using one
eligibility artifact for Prop and Type keeps host metadata alignment uniform.

The previous derivability audit is unchanged by the v4.33 reconciliation.
Recursor iota rules reduce a projector only on a constructor-headed major,
function eta applies only at Pi types, and proof irrelevance covers only Prop.
Consequently the neutral reconstruction equation above is not derivable from
the existing `VEnv.IsDefEq` constructors.

## Lower-layer descriptor and registry

`VStructEta` lives below `Typing.Basic`. It contains only Theory syntax and
the syntactic stability laws needed by generic equality transport:

```text
structure VStructEta where
  uvars          : Nat
  nparams        : Nat
  nfields        : Nat
  familyName     : Name
  familyType     : VExpr
  constructorName : Name
  projectors     : List VLevel -> List VExpr -> List VExpr

  projectors_length : levels.length = uvars ->
    params.length = nparams ->
    (projectors levels params).length = nfields
  projectors_liftN : ...
  projectors_instN : ...
  projectors_instL : ...
```

The omitted equations are literal naturality equations: mapping `liftN`, term
substitution, or universe instantiation over a projector list equals asking
the descriptor for the correspondingly transformed levels and parameters.
They are equations about syntax, not semantic equality assumptions.

The descriptor defines, rather than stores as caller-selected callbacks:

```text
structureType levels params = const familyName levels |>.appN params
rebuild levels params major =
  const constructorName levels |>.appN
    (params ++ (projectors levels params).map (.app . major))
```

`VEnv` gains a monotone `structEtas : VStructEta -> Prop` registry and an
`addStructEta` extension operation. `empty` registers none; `addConst` and
`addDefEq` preserve registrations; `VEnv.LE` transports them. `Ordered` gains
one constructor whose premise is `VStructEta.WF env`, and
`Ordered.structEtaWF` recovers that certificate for every registered
descriptor.

`VStructEta.WF env` is the subject-reduction package. Given a well-formed
context, well-formed universe arguments of the exact length, an exact family
parameter `SpineWF`, and `major : structureType levels params`, its
`rebuild_hasType` field produces the same type for `rebuild levels params
major`. This package contains no equality premise.

`VStructureView.toStructEta` is the only checked generation bridge used by
the verifier. It sets `projectors` to the deterministic
`VStructureView.projectionCodes` projector list. Its naturality laws are the
existing `projectionCodes_liftN`, `projectionCodes_instN`, and
`projectionCodes_instL` theorems; its subject-reduction proof is
`ProgramsWF.etaRebuild_hasType_of_constructorPrefix` plus the registered
constructor telescope. A `ProjectionArtifact` records membership of this
exact descriptor, so host readiness cannot substitute arbitrary projector
syntax.

## Equality rule

The new constructor in `VEnv.IsDefEq` has the following exact logical shape
(notation abbreviated):

```text
IsDefEq.structEta
  (registered : env.structEtas rule)
  (levelsWF : every level in levels is WF at U)
  (levelsLength : levels.length = rule.uvars)
  (paramsLength : params.length = rule.nparams)
  (paramsSpine : familyType.instL levels consumes params to a sort)
  (majorTyped : Gamma |- major : rule.structureType levels params)
  (rebuildTyped : Gamma |- rule.rebuild levels params major :
    rule.structureType levels params)
  : Gamma |- rule.rebuild levels params major == major :
      rule.structureType levels params
```

Both endpoint typings are deliberately constructor premises. Thus
`IsDefEq.hasType` and `IsDefEq.isType'` remain structural for arbitrary
environments; `Ordered.structEtaWF` supplies `rebuildTyped` at registered
call sites rather than becoming a hidden equality oracle. The parameter spine
and exact lengths make the primitive unavailable on partial applications.

Weakening and term/universe substitution rebuild the same constructor with
the descriptor naturality equations. Context-defeq transport preserves the
syntax and transports the two typing premises. Environment monotonicity uses
the new `VEnv.LE.structEtas` component.

## Strong typing, inversion, and discrimination

`IsDefEqStrong` gains the same registered step with strong certificates for
the common structure type and both endpoints. The weak-to-strong translation
obtains these from the recursive typing premises; strong-to-weak erases them.
The `HasTypeStrong` inversion family sees the new case only through those
endpoint certificates.

Sort/Pi/constant-head discrimination does not discard the case by syntactic
pattern matching. If the arbitrary major has the queried head, its explicit
typing is compared with the registered `const familyName ... |>.appN params`
type via the existing strong unique-typing/inversion path. The reconstruction
endpoint is constructor-headed. This keeps the existing L4L-16/L4L-17
frontier visible rather than embedding injectivity in the descriptor.

## Confluence and standardization

Structure eta is represented in `NormalEq` by left and right reconstruction
forms, analogously to function eta. The congruence payload relates the major
terms and every parameter/projector occurrence at one registered descriptor.
The descriptor naturality laws provide weakening and substitution directly.

The parallel-reduction compatibility proof must cover these cases explicitly:

1. constructor major versus generated projector iota;
2. nested reconstruction, contracting either layer first;
3. beta/delta/iota reduction inside the major and its repeated projector
   occurrences;
4. dependent later projector types after an earlier projection changes;
5. proof fields and Prop-valued structures; and
6. overlap with a registered `.extra` rule under the generic `[Params]`
   pattern interface.

No new `sorry`, axiom, or final-result field is added to `Params`. The generic
development may gain primitive descriptor coverage/disjointness premises,
but the actual triangle/join statements remain proved theorems. The concrete
checked-view bridge must discharge those premises from constructor-headed
syntax and the deterministic projector programs.

`WHRed` does not contract structure eta: as in Lean's equality procedure it
is a conversion rule, not weak-head computation. Head standardization gains
only the cases needed to transport the enlarged `NormalEq` relation.

## Exhaustive consumer inventory

Before the rule lands, the direct constructor-aligned source inventory is:

| File | Direct aligned sites | Required work |
|---|---:|---|
| `Typing/Basic.lean` | 1 | rule and subject-reduction-facing aliases |
| `Typing/Lemmas.lean` | 9 | closure, levels, mono, weak/inst/context transport |
| `Typing/Strong.lean` | 12 | strong relation, translations, inversion |
| `Typing/NestedTransport.lean` | 1 | nested environment transport |
| `Typing/ChurchRosser.lean` | 26 | `NormalEq`, parallel joins, CR translation |
| `Typing/HeadReduction.lean` | 12 | standardization interaction |

The compiler-driven audit also covers dependent consumers in
`UniqueTyping`, `Injectivity`, `InductiveLemmas`, `Projection`, and Verify.
Every failed exhaustive match after adding the constructor is treated as an
inventory defect, not silenced with a wildcard.

Environment-schema consumers are `VEnv`, `Typing.Lemmas` (`Ordered`),
`Typing.Env`/`EnvLemmas`, Verify's `TrEnv'`/`VEnvAt` construction, and the few
explicit `VEnv.LE` records in Verify environment extension proofs.

## Checker closure and fixtures

`ProjectionArtifact` and `ProjectionReady` retain the exact registered eta
descriptor for any host family/constructor accepted by
`isNonRecStructure`. This supplies both `StructureEtaReady` and descriptor
membership. `VEnv.HasStructureEta` is then a theorem derived from
`IsDefEq.structEta`, not a new assumption. The already proved
`tryEtaStructCore.WF_of_structureEta` and
`isDefEqUnitLike.WF_of_structureEta` become the bodies of the unconditional
roots.

Focused executable/Theory fixtures cover:

- a dependent parameterized structure and neutral major;
- a parameterized zero-field structure;
- a proof field;
- a Prop-valued one-constructor inductive; and
- recursive, multi-constructor, and indexed negative cases.

Exact `#print axioms` guards cover descriptor registration,
`VStructEta.WF.rebuild_hasType`, the primitive equality step, its
Church--Rosser translation, and both checker roots. The L4L-15B checkpoint may
inherit already classified frontier dependencies, but its source diff adds
no `sorry` and the compiled frontier may not grow.

## Removal and upstream path

D019 is revisited at every upstream reconciliation. It is removed when
upstream adopts this registered primitive or an agreed equivalent and the
fork migrates. If upstream ultimately rejects any Theory representation of
structure eta, the recorded fallback is to disable `tryEtaStruct` and
`isDefEqUnitLike`; certifying the current runtime against a weaker relation is
not an option.
