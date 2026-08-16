# L4L-18B extension contract and pattern-interface design

Date: 2026-08-12

Status: implemented fork divergence on the reconciled v4.33 base. This note
records the interface decision owned by ledger entry D020. Construction of a
whole-live-environment semantic instance remains L4L-16 work.

## Problem

The upstream-shaped `Params` interface coupled two facts that do not hold at
the same syntactic point in lean4lean:

1. `extra_pat` required a `Pattern.Matches` witness for
   `df.lhs.instL levels`.
2. `pat_wf` accepted a pattern match, checks, and a bare typing of the redex,
   then had to manufacture equality with the RHS template.

Generated iota equations and `quotDefEq` are registered as closed lambda
towers. A first-order iota pattern cannot match the tower itself. The useful
recursor/constructor application appears only underneath the leading lambdas,
after applying a typed spine and beta-collapsing the tower. The proved
generated-rule soundness theorem consequently needs that typed spine
decomposition; bare `HasType` does not contain it.

Leaving either mismatch as a `Params` field would make a generated instance
an oracle: registration or pattern membership could silently assert an
operational rewrite that was not proved at the actual redex.

## Decision: separate shape, local soundness, and global joining

### Pattern combinatorics

`Params` now contains only the pattern set and its combinatorial laws:
simple-pattern classification and the overlap/nonintersection properties used
by the parallel-reduction proofs. It has neither `pat_wf` nor `extra_pat`.

Pattern membership therefore says only that a pattern and payload participate
in the reduction system. It does not imply that any term matches, that checks
hold, or that a rewrite is definitionally equal.

### Proof-carrying contractions

The `.extra` constructors of `ParRed`, `CParRed`, and `WHRed`, and the
corresponding `NonNeutral` witness, carry the exact local certificate

```lean
IsDefEqU env univs Γ e (r.1.apply m1 m2)
```

in addition to pattern membership, the successful match, and `Check.OK`.
Weakening, substitution, context conversion, standardization, and triangle
proofs transport or reconstruct this certificate explicitly. `ParRed.defeq`
uses the carried equality; it never obtains soundness from pattern
classification.

This makes the operational trust boundary local: the consumer selecting a
contraction must prove equality for that concrete redex and capture map.

### Beta-collapsed tower coverage

`CertifiedExtension.covers` now states only the syntactic fact that the
registered left side matches after its leading lambda tower is exposed:

```lean
∃ m1 m2, pat.toPattern.Matches
  (VExpr.stripLams (df.lhs.instL levels)) m1 m2
```

`VExpr.stripLams_instL` and `Pattern.Matches.instL` make this stable under
universe instantiation. They do not claim that the pattern payload's RHS is
equal to the registered RHS.

Two kernel-checked constructors pin the intended environment classes:

- `BlockGenerationChecked.iotaExtension` derives coverage from the generated
  rule body and `ruleLhsBody_matches` for every certified iota rule.
- `CertifiedExtension.quot` gives the corresponding `Quot.lift`/`Quot.mk`
  pattern, captures, checks, and collapsed coverage for `quotDefEq`.

Both have exact axiom guards containing only the standard logical baseline;
neither uses a project axiom or `sorryAx`.

### Global registered-equation joining

Church--Rosser's raw `IsDefEq.extra` case has a different obligation from a
local pattern contraction. It is isolated in the explicit class

```lean
class Params.Extension [Params] where
  join : OnCtx Γ (env.IsType univs) →
    env.defeqs df → (∀ l ∈ levels, l.WF univs) →
    levels.length = df.uvars →
    CRDefEq Γ (df.lhs.instL levels) (df.rhs.instL levels)
```

`CRDefEq` includes typings for both endpoints and parallel-reduction paths to
endpoints related by `NormalEq`. Thus an instance must prove operational
coverage for every registered equation in every well-formed context; registry
membership alone cannot inhabit it. `Params.Extension.extra_symm` derives the
reverse direction from the join rather than adding a second oracle field.

Only `IsDefEq.church_rosser` and results that transitively invoke it require
`[Params.Extension]`. The remaining generic reduction and standardization
lemmas stay generic in `[Params]` alone.

The live-environment instance covering definitions, quotient rules,
ordinary/mutual/nested inductives, and registered structure eta is deliberately
not manufactured here. L4L-16 constructs it through the semantic environment
bridge.

## Environment transport

The named `VEnv.LE` helpers make the core registered-equation behavior under
environment growth explicit:

- `VEnv.LE.extra` transports registry membership and reconstructs the raw
  typed equality with the original level side conditions.
- `VEnv.LE.extra_appN` additionally transports a typed spine and applies
  congruence to both tower endpoints.
- `VEnv.LE.extra_appN_symm` derives the reverse applied equality by symmetry.

These theorems transport proofs already available in the smaller environment;
they do not certify a new rule or infer a reduction from a pattern.

## Trust matrix

| Evidence | What it establishes | What it does not establish |
|---|---|---|
| `env.defeqs df` | the raw tower equation is registered | a pattern match or reduction step |
| `CertifiedExtension.covers` | the stripped left body has the advertised shape | checks, typing, or equality to the payload RHS |
| `Check.OK` | captured side conditions hold in the current context | redex-to-RHS equality |
| local `IsDefEqU` certificate | this matched redex equals this instantiated payload | global confluence for every registered equation |
| `Params.Extension.join` | a registered raw equation has a typed Church--Rosser join | automatic permission to contract an arbitrary match |

No row implies a later row without a proof supplied by the corresponding
consumer.

## Downstream migration

`ChurchRosser.lean` transports the local equality certificate through
weakening, substitution, context conversion, complete parallel reduction,
match inversion, and the triangle proof. `HeadReduction.lean` mirrors the
same certificate in weak-head steps and reconstructs it in the
standardization triangle. The broad extension-instance requirement was
narrowed to `reduce_sort`, `reduce_forallE`, and `InferType.exists`, the three
head-reduction results that actually invoke Church--Rosser.

Later L4L-18A overlap proofs target the proof-carrying `.extra` constructor.
Later L4L-16 constructs `Params.Extension` from the promoted semantic bridge;
it may use the beta-collapsed certificates and `pat_wf`, but cannot replace
their typing premises with registry membership.

## Rejected alternatives

- Matching the raw lambda tower: structurally false for the supported
  first-order patterns.
- Storing a collapsed RHS equation in `CertifiedExtension`: this conflates a
  syntactic inventory certificate with semantic soundness and would still
  omit the typed-spine premises.
- Retaining `Params.pat_wf` with bare `HasType`: insufficient for the proved
  generated-rule theorem and invites a consumer oracle.
- Treating every registered equality as a reduction: equality registration
  is symmetric conversion data, not an orientation or termination policy.
- Generating a global `Params`/extension instance in the assembler: the
  assembler covers one block plus explicit extensions, not the whole live
  environment required by the semantic proof.

## Validation and upstream path

Focused builds cover Church--Rosser, head reduction, the pattern environment,
and concrete pattern fixtures. Exact guards pin the new universe-match
transport, generated-iota and quotient certificates, and `VEnv.LE` transport
helpers. The full milestone gate is recorded in the landing checkpoint.

D020 is revisited at every upstream reconciliation. It is removed when
upstream adopts the proof-carrying contraction and explicit join split, or an
equivalent interface that can represent beta-collapsed tower rules without a
trusted shape/soundness oracle. Upstream review is consolidated in the
L4L-20C proof-PR series.
